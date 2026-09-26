/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import HaxLean.AST
public meta import HaxLean.SemanticsCF
public import HaxLean.AST
public import HaxLean.SemanticsCF
public import HaxLean.NF

/-!
# ANF normalisation for the `haxToLowCT` subset

`CatCrypt.Crypto.Hax.HaxToLowCT.haxToLowCT : ImpExpr → Option LowCT` accepts a
let-normalised fragment: every `app` occurs as the right-hand side of a
`letBind`, every argument of an `app` is a `var`, every branch condition is a
`var`, and the tail of a body is a `var`, a `unitVal` or a tuple of `var`s. The
extraction pipeline produces neither shape: a body's tail is the value
expression it computes, and arguments carry nested applications and literals.

`anfLowCT` rewrites an extracted body into that fragment. Each non-atomic
subexpression in argument position is bound to a fresh `_anf<n>` slot by a
`letBind` inserted immediately before the statement that used it, and a tail
value expression `e` becomes `letBind _anf<n> e (var _anf<n>)`.

The rewrite is evaluation-order preserving and duplication-free: a hoisted
subterm is bound once, in the position where it was evaluated, and the
occurrence is replaced by a reference to its binder. Hoisted binders are
inserted in the scope that contained the subterm, so no free occurrence is
captured and none escapes its binder.

Three positions are deliberately left alone, because hoisting out of them would
not preserve the program:

* a `whileLoop` / `whileFold` condition, which is re-evaluated per iteration;
* the bounds of a `forFold` / `forFoldRev`, which `haxToLowCT` reads as literals;
* the right-hand side of a `letBind` that is not an `app`, `lit`, `var` or
  `proj` — an `if`-expression or a `match`-expression bound to a name has no
  image in `LowCT`'s statement grammar, and giving it one would mean inventing a
  default value for the slot.

A body containing one of the last kind is returned with its subexpressions
normalised and that binding intact; `haxToLowCT` still returns `none` on it.

## Loop guards

hax desugars a Rust `while c { body }` into `loop { if c { body } else { break } }`,
which reaches this pass as `whileFold (lit true) (G; ifThenElse (var g) T (seq
(cfBreak unitVal) unitVal))`, where `G` is the `letBind` chain the hoisting above
produced for the condition `c` and `g` names its value. `haxToLowCT` lowers only a
`whileFold` whose condition is a variable and has no image for `cfBreak`, so
`normWhileTrue` rewrites that shape into

```
G; whileFold (var g) (T; G')
```

where `G'` re-evaluates the guard chain as `assign`s into the same names. The
rewrite preserves the denotation (`normWhileTrue_denoteValueCF`): the original loop
evaluates `G` at the head of every trip and leaves through the `break` on the
first trip whose guard is false; the rewritten loop evaluates `G` once before the
first trip and again at the end of every completed trip, which is the same
program point as the head of the following trip, and leaves when the variable
holds `false`. The rewrite applies only when `T` contains no `continue` that
reaches this loop, since a `continue` skips `G'` in the rewritten body but not
the head guard in the original; every other `whileFold`, and every `break` in any
other position, is left as it is.

The fresh-name scheme is the one
`CatCrypt.Crypto.SecureCompilation.ImpExprToThir.anfName` uses, so the two
lifters name their temporaries alike.

## Normal form

On the source fragment `anfSrc false`, the output of `anfLowCT` is in the monadic
A-normal form `NF` (`anfLowCT_NF`), and every expression in `NF` is in that fragment
(`anfSrc_of_isNFK`).
-/

@[expose] public section

namespace Hax

/-- Fresh hoisting-temporary name `_anf<n>`. No extracted binder starts with
    `_anf`, so these are disjoint from the source names. -/
def anfName (n : Nat) : String := "_anf" ++ toString n

/-- A limb read `index(v, i)` on a variable and a non-negative integer literal.
    `haxToLowCT` reads this shape directly, so its literal index is not hoisted;
    every other argument list is reduced to variables. -/
def isLimbRead (f : String) (args : List ImpExpr) : Bool :=
  f == "index" &&
    match args with
    | [.var _, .lit (.int i)] => 0 ≤ i
    | _ => false

mutual

/-- Normalise an expression in *value* position, so that it can stand as the
    right-hand side of a `letBind`: the head is kept and each argument is
    reduced to a variable. Returns the next counter, a wrapper prepending the
    hoisted bindings in evaluation order, and the rewritten right-hand side. -/
def anfRhs (n : Nat) (e : ImpExpr) : Nat × (ImpExpr → ImpExpr) × ImpExpr :=
  match e with
  | .app f args =>
      if isLimbRead f args then (n, id, .app f args)
      else
        let (n₁, w, args') := anfArgs n args
        (n₁, w, .app f args')
  | .proj b i =>
      let (n₁, w, b') := anfArg n b
      (n₁, w, .proj b' i)
  | .typeAscription b _ => anfRhs n b
  | _ => (n, id, e)
termination_by (sizeOf e, 0)

/-- Normalise an expression in *argument* position, where `haxToLowCT` requires
    a variable: a variable passes through, anything else is normalised as a
    right-hand side and bound to a fresh `_anf<n>`. -/
def anfArg (n : Nat) (e : ImpExpr) : Nat × (ImpExpr → ImpExpr) × ImpExpr :=
  match e with
  | .var x => (n, id, .var x)
  | e' =>
      let (n₁, w, rhs) := anfRhs n e'
      let t := anfName n₁
      (n₁ + 1, fun body => w (.letBind t rhs body), .var t)
termination_by (sizeOf e, 1)

/-- Normalise an argument list left to right, so the hoisted bindings appear in
    the order the arguments were evaluated. -/
def anfArgs (n : Nat) (es : List ImpExpr) :
    Nat × (ImpExpr → ImpExpr) × List ImpExpr :=
  match es with
  | [] => (n, id, [])
  | a :: rest =>
      let (n₁, w₁, a') := anfArg n a
      let (n₂, w₂, rest') := anfArgs n₁ rest
      (n₂, fun body => w₁ (w₂ body), a' :: rest')
termination_by (sizeOf es, 0)

end

/-- A right-hand side `haxToLowCT` binds directly. -/
def bindableRhs : ImpExpr → Bool
  | .app _ _ => true
  | .lit _ => true
  | .var _ => true
  | .proj (.var _) _ => true
  | _ => false

/-- The guard chain of a desugared `while`: a `letBind` chain with bindable
    right-hand sides ending in `ifThenElse (var g) T (seq (cfBreak unitVal)
    unitVal)`. Returns the chain's bindings in order, the guard variable `g` and
    the then-branch `T`. -/
def splitWhileGuard : ImpExpr → Option (List (String × ImpExpr) × String × ImpExpr)
  | .letBind x v rest =>
      if bindableRhs v then
        (splitWhileGuard rest).map fun (gs, g, t) => ((x, v) :: gs, g, t)
      else none
  | .ifThenElse (.var g) t (.seq (.cfBreak .unitVal) .unitVal) => some ([], g, t)
  | _ => none

/-- The `letBind` chain of `gs` over `k`. -/
def bindChain : List (String × ImpExpr) → ImpExpr → ImpExpr
  | [], k => k
  | (x, v) :: rest, k => .letBind x v (bindChain rest k)

/-- The bindings of `gs` as a `seq` of `assign`s, ending in `unitVal`. -/
def assignSeq : List (String × ImpExpr) → ImpExpr
  | [] => .unitVal
  | (x, v) :: rest => .seq (.assign x v) (assignSeq rest)

/-- `true` when no `continue` in `e` reaches the loop enclosing `e`: every
    `cfContinue`, `cfBreakContinue` and `continue_` in `e` lies inside the body of
    a loop nested in `e`. -/
partial def noLoopContinue : ImpExpr → Bool
  | .cfContinue _ | .cfBreakContinue _ | .continue_ => false
  | .letBind _ v b => noLoopContinue v && noLoopContinue b
  | .lam _ b => noLoopContinue b
  | .app _ args => args.all noLoopContinue
  | .tuple es => es.all noLoopContinue
  | .proj e _ => noLoopContinue e
  | .ifThenElse c t e => noLoopContinue c && noLoopContinue t && noLoopContinue e
  | .match_ s arms => noLoopContinue s && arms.all fun (_, b) => noLoopContinue b
  | .seq a b => noLoopContinue a && noLoopContinue b
  | .borrow e | .deref e => noLoopContinue e
  | .assign _ e => noLoopContinue e
  | .forLoop _ lo hi _ | .forLoopRev _ lo hi _ | .forFold _ lo hi _
  | .forFoldRev _ lo hi _ | .forFoldReturn _ lo hi _ | .forFoldRevReturn _ lo hi _ =>
      noLoopContinue lo && noLoopContinue hi
  | .whileLoop c _ | .whileFold c _ | .whileFoldReturn c _ => noLoopContinue c
  | .break_ (some e) => noLoopContinue e
  | .earlyReturn e | .questionMark e | .cfBreak e => noLoopContinue e
  | .typeAscription e _ => noLoopContinue e
  | .lit _ | .var _ | .unitVal | .break_ none => true

/-- Rewrite `whileFold (lit true) (G; ifThenElse (var g) T (seq (cfBreak unitVal)
    unitVal))` into `G; whileFold (var g) (seq T G')`, with `G'` the guard chain
    as assignments, when `T` has no `continue` reaching the loop. Any other loop
    is returned unchanged. -/
def normWhileTrue (c body : ImpExpr) : ImpExpr :=
  match c, splitWhileGuard body with
  | .lit (.bool true), some (gs, g, t) =>
      if noLoopContinue t then
        bindChain gs (.whileFold (.var g) (.seq t (assignSeq gs)))
      else .whileFold c body
  | _, _ => .whileFold c body

mutual

/-- Normalise an expression in *statement* position. -/
def anfStmt (n : Nat) (e : ImpExpr) : Nat × ImpExpr :=
  match e with
  | .letBind x v body =>
      if bindableRhs v then
        let (n₁, w, v') := anfRhs n v
        let (n₂, body') := anfStmt n₁ body
        (n₂, w (.letBind x v' body'))
      else
        -- An `if`-expression bound to a name has no image in `LowCT`'s
        -- statement grammar, so the binding stands. Its condition is
        -- evaluated once, before the branch, and is hoisted to a variable so
        -- the binding has the shape a widened recogniser would read; the two
        -- branches stay where they are, since hoisting either one out would
        -- evaluate it on both paths.
        match v with
        | .ifThenElse c t f =>
            let (n₁, w, c') := anfArg n c
            let (n₂, body') := anfStmt n₁ body
            (n₂, w (.letBind x (.ifThenElse c' t f) body'))
        | _ =>
            let (n₁, body') := anfStmt n body
            (n₁, .letBind x v body')
  | .seq a b =>
      let (n₁, a') := anfStmt n a
      let (n₂, b') := anfStmt n₁ b
      (n₂, .seq a' b')
  | .ifThenElse c t f =>
      let (n₁, w, c') := anfArg n c
      let (n₂, t') := anfStmt n₁ t
      let (n₃, f') := anfStmt n₂ f
      (n₃, w (.ifThenElse c' t' f'))
  | .assign x rhs =>
      if bindableRhs rhs then
        let (n₁, w, rhs') := anfRhs n rhs
        (n₁, w (.assign x rhs'))
      else (n, .assign x rhs)
  | .tuple es =>
      let (n₁, w, es') := anfArgs n es
      (n₁, w (.tuple es'))
  | .match_ scrut arms =>
      let (n₁, w, scrut') := anfRhs n scrut
      let (n₂, arms') := anfArms n₁ arms
      (n₂, w (.match_ scrut' arms'))
  | .typeAscription b s =>
      let (n₁, b') := anfStmt n b
      (n₁, .typeAscription b' s)
  -- A loop condition is re-evaluated each iteration, so it stays in place.
  | .whileLoop c body =>
      let (n₁, body') := anfStmt n body
      (n₁, .whileLoop c body')
  -- A desugared `while` is turned into a variable-guarded loop once its body,
  -- and so every loop nested in it, is normalised.
  | .whileFold c body =>
      let (n₁, body') := anfStmt n body
      (n₁, normWhileTrue c body')
  | .whileFoldReturn c body =>
      let (n₁, body') := anfStmt n body
      (n₁, .whileFoldReturn c body')
  -- `haxToLowCT` reads the bounds of a fold as literals, so they stay in place.
  | .forFold v lo hi body =>
      let (n₁, body') := anfStmt n body
      (n₁, .forFold v lo hi body')
  | .forFoldRev v lo hi body =>
      let (n₁, body') := anfStmt n body
      (n₁, .forFoldRev v lo hi body')
  | .forFoldReturn v lo hi body =>
      let (n₁, body') := anfStmt n body
      (n₁, .forFoldReturn v lo hi body')
  | .forFoldRevReturn v lo hi body =>
      let (n₁, body') := anfStmt n body
      (n₁, .forFoldRevReturn v lo hi body')
  | .var x => (n, .var x)
  | .unitVal => (n, .unitVal)
  -- A tail value expression: bound to a fresh slot, which the tail then names.
  | .app f args =>
      let (n₁, w, rhs) := anfRhs n (.app f args)
      let t := anfName n₁
      (n₁ + 1, w (.letBind t rhs (.var t)))
  | .lit l =>
      let t := anfName n
      (n + 1, .letBind t (.lit l) (.var t))
  | .proj b i =>
      let (n₁, w, rhs) := anfRhs n (.proj b i)
      let t := anfName n₁
      (n₁ + 1, w (.letBind t rhs (.var t)))
  | _ => (n, e)
termination_by sizeOf e

/-- Normalise the bodies of the arms of a `match_`. -/
def anfArms (n : Nat) (arms : List (ImpPat × ImpExpr)) :
    Nat × List (ImpPat × ImpExpr) :=
  match arms with
  | [] => (n, [])
  | (p, b) :: rest =>
      let (n₁, b') := anfStmt n b
      let (n₂, rest') := anfArms n₁ rest
      (n₂, (p, b') :: rest')
termination_by sizeOf arms

end

/-- ANF-normalise an extracted function body into the fragment
    `haxToLowCT` accepts. -/
def anfLowCT (e : ImpExpr) : ImpExpr := (anfStmt 0 e).2

/-! ### The normal form of `anfLowCT`

`anfSrc il e` is the source fragment on which `anfStmt` produces the normal form
`NF`: the fragment `isNFK il` describes, with every argument position except exit
payloads (a call argument, a branch condition, a tuple component, a tail value)
widened to a value expression, which `anfStmt` hoists into `letBind`s. The `whileFold` on the literal
`true` that `normWhileTrue` rewrites is outside the fragment. -/

mutual

/-- A value expression: a variable, a literal, a call on value expressions, or a
    projection or type ascription of a value expression. -/
def anfValSrc : ImpExpr → Bool
  | .var _ => true
  | .lit _ => true
  | .app _ args => anfValSrcs args
  | .proj b _ => anfValSrc b
  | .typeAscription b _ => anfValSrc b
  | _ => false

/-- Every expression of the list is a value expression. -/
def anfValSrcs : List ImpExpr → Bool
  | [] => true
  | a :: rest => anfValSrc a && anfValSrcs rest

end

/-- The source fragment of `anfStmt` in loop context `il`: the clauses of `isNFK il`
    with value expressions (`anfValSrc`) in argument positions, a bindable value
    expression as the right-hand side of a `letBind` or an `assign`, and a call on
    value expressions as the scrutinee of the two-tuple `match_`. -/
def anfSrc : Bool → ImpExpr → Bool
  | il, .letBind _ v b => bindableRhs v && anfValSrc v && anfSrc il b
  | _, .var _ => true
  | _, .lit _ => true
  | _, .unitVal => true
  | _, .app _ args => anfValSrcs args
  | _, .proj b _ => anfValSrc b
  | il, .seq a b => anfSrc il a && anfSrc il b
  | il, .ifThenElse c t e => anfValSrc c && anfSrc il t && anfSrc il e
  | _, .assign _ r => bindableRhs r && anfValSrc r
  | _, .tuple es => anfValSrcs es
  | il, .match_ (.app _ args) [(.tuplePat [.varPat _, .varPat _], b)] =>
      anfValSrcs args && anfSrc il b
  | _, .whileLoop (.var _) b => anfSrc false b
  | _, .whileFold (.var _) b => anfSrc false b
  | _, .whileFoldReturn (.var _) b => anfSrc true b
  | _, .forFold _ lo hi b => nfLit lo && nfBound hi && anfSrc false b
  | _, .forFoldRev _ lo hi b => nfLit lo && nfLit hi && anfSrc false b
  | _, .forFoldReturn _ lo hi b => nfLit lo && nfLit hi && anfSrc true b
  | _, .forFoldRevReturn _ lo hi b => nfLit lo && nfLit hi && anfSrc true b
  | il, .cfBreak e => il && nfBreakArg e
  | il, .cfContinue e => il && nfBreakArg e
  | il, .cfBreakContinue e => il && nfBreakArg e
  | il, .typeAscription e _ => anfSrc il e
  | _, _ => false

/-- `w` prepends a `letBind` chain whose right-hand sides are in normal form. -/
def IsNFChain (w : ImpExpr → ImpExpr) : Prop :=
  ∃ gs : List (String × ImpExpr), gs.all (fun p => nfRhs p.2) = true ∧ ∀ k, w k = bindChain gs k

theorem bindChain_append (gs hs : List (String × ImpExpr)) (k : ImpExpr) :
    bindChain (gs ++ hs) k = bindChain gs (bindChain hs k) := by
  induction gs with
  | nil => rfl
  | cons p rest ih => obtain ⟨x, v⟩ := p; simp [bindChain, ih]

theorem isNFK_bindChain (il : Bool) (gs : List (String × ImpExpr)) (k : ImpExpr) :
    isNFK il (bindChain gs k) = (gs.all (fun p => nfRhs p.2) && isNFK il k) := by
  induction gs with
  | nil => simp [bindChain]
  | cons p rest ih => obtain ⟨x, v⟩ := p; simp [bindChain, isNFK, ih, Bool.and_assoc]

theorem IsNFChain.id : IsNFChain id := ⟨[], rfl, fun _ => rfl⟩

theorem IsNFChain.comp {w₁ w₂ : ImpExpr → ImpExpr} (h₁ : IsNFChain w₁) (h₂ : IsNFChain w₂) :
    IsNFChain (fun b => w₁ (w₂ b)) := by
  obtain ⟨g₁, hg₁, e₁⟩ := h₁
  obtain ⟨g₂, hg₂, e₂⟩ := h₂
  exact ⟨g₁ ++ g₂, by rw [List.all_append, hg₁, hg₂]; rfl,
    fun k => by simp [e₁, e₂, bindChain_append]⟩

theorem IsNFChain.snoc {w : ImpExpr → ImpExpr} (h : IsNFChain w) (t : String) {rhs : ImpExpr}
    (hr : nfRhs rhs = true) : IsNFChain (fun b => w (.letBind t rhs b)) := by
  obtain ⟨g, hg, e⟩ := h
  exact ⟨g ++ [(t, rhs)], by rw [List.all_append, hg]; simp [hr],
    fun k => by simp [e, bindChain_append, bindChain]⟩

/-- A chain of normal-form bindings over a normal form is a normal form. -/
theorem IsNFChain.isNFK {w : ImpExpr → ImpExpr} (h : IsNFChain w) {il : Bool} {k : ImpExpr}
    (hk : isNFK il k = true) : isNFK il (w k) = true := by
  obtain ⟨g, hg, e⟩ := h
  simp [e, isNFK_bindChain, hg, hk]

/-- On a value expression, `anfRhs` returns a normal-form right-hand side after a
    chain of normal-form bindings, and `anfArg` a variable after such a chain. -/
theorem anfRhs_nf (e : ImpExpr) : ∀ n, anfValSrc e = true →
    (IsNFChain (anfRhs n e).2.1 ∧ nfRhs (anfRhs n e).2.2 = true) ∧
    (IsNFChain (anfArg n e).2.1 ∧ nfVar (anfArg n e).2.2 = true) := by
  induction e using ImpExpr.ind with
  | var x => intro n _; simp [anfRhs, anfArg, nfRhs, nfVar, IsNFChain.id]
  | lit l =>
    intro n _
    refine ⟨by simp [anfRhs, nfRhs, IsNFChain.id], ?_⟩
    simp only [anfArg, anfRhs]
    exact ⟨IsNFChain.snoc IsNFChain.id _ rfl, rfl⟩
  | app f args ih =>
    intro n h
    simp only [anfValSrc] at h
    have hargs : ∀ m, IsNFChain (anfArgs m args).2.1 ∧ (anfArgs m args).2.2.all nfVar = true := by
      induction args with
      | nil => intro m; simp [anfArgs, IsNFChain.id]
      | cons a rest ihl =>
        intro m
        simp only [anfValSrcs, Bool.and_eq_true] at h
        have ha := (ih a (by simp) m h.1).2
        have hrest := ihl (fun x hx => ih x (by simp [hx])) h.2 (anfArg m a).1
        simp only [anfArgs]
        exact ⟨IsNFChain.comp ha.1 hrest.1, by simp [ha.2, hrest.2]⟩
    have hr : IsNFChain (anfRhs n (.app f args)).2.1 ∧ nfRhs (anfRhs n (.app f args)).2.2 = true := by
      simp only [anfRhs]
      split
      · rename_i hl
        refine ⟨IsNFChain.id, ?_⟩
        simp only [isLimbRead, Bool.and_eq_true] at hl
        obtain ⟨_, hl⟩ := hl
        split at hl <;> simp_all [nfRhs]
      · refine ⟨(hargs n).1, ?_⟩
        have hv := (hargs n).2
        simp only [nfRhs, List.all_eq_true] at hv ⊢
        intro x hx
        have := hv x hx
        cases x <;> simp_all [nfVar]
    refine ⟨hr, ?_⟩
    simp only [anfArg]
    exact ⟨IsNFChain.snoc hr.1 _ hr.2, rfl⟩
  | proj b i ih =>
    intro n h
    simp only [anfValSrc] at h
    have hr : IsNFChain (anfRhs n (.proj b i)).2.1 ∧ nfRhs (anfRhs n (.proj b i)).2.2 = true := by
      obtain ⟨_, ⟨hc, hv⟩⟩ := ih n h
      simp only [anfRhs]
      refine ⟨hc, ?_⟩
      generalize (anfArg n b).2.2 = v at hv
      cases v <;> simp_all [nfVar, nfRhs]
    refine ⟨hr, ?_⟩
    simp only [anfArg]
    exact ⟨IsNFChain.snoc hr.1 _ hr.2, rfl⟩
  | typeAscription b s ih =>
    intro n h
    simp only [anfValSrc] at h
    have hr : IsNFChain (anfRhs n (.typeAscription b s)).2.1 ∧
        nfRhs (anfRhs n (.typeAscription b s)).2.2 = true := by
      simp only [anfRhs]; exact (ih n h).1
    refine ⟨hr, ?_⟩
    simp only [anfArg]
    exact ⟨IsNFChain.snoc hr.1 _ hr.2, rfl⟩
  | _ => intro n h; simp [anfValSrc] at h

/-- On a list of value expressions, `anfArgs` returns variables after a chain of
    normal-form bindings. -/
theorem anfArgs_nf (args : List ImpExpr) : ∀ n, anfValSrcs args = true →
    IsNFChain (anfArgs n args).2.1 ∧ (anfArgs n args).2.2.all nfVar = true := by
  induction args with
  | nil => intro m _; simp [anfArgs, IsNFChain.id]
  | cons a rest ihl =>
    intro m h
    simp only [anfValSrcs, Bool.and_eq_true] at h
    have ha := (anfRhs_nf a m h.1).2
    have hrest := ihl (anfArg m a).1 h.2
    simp only [anfArgs]
    exact ⟨IsNFChain.comp ha.1 hrest.1, by simp [ha.2, hrest.2]⟩

/-- `anfRhs` keeps the head of a call. -/
theorem anfRhs_app (n : Nat) (f : String) (args : List ImpExpr) :
    ∃ args', (anfRhs n (.app f args)).2.2 = .app f args' := by
  simp only [anfRhs]
  split
  · exact ⟨args, rfl⟩
  · exact ⟨_, rfl⟩

theorem nfVar_eq {e : ImpExpr} (h : nfVar e = true) : ∃ x, e = .var x := by
  cases e <;> simp_all [nfVar]

/-- On the source fragment `anfSrc il`, `anfStmt` produces a normal form in loop
    context `il`. -/
theorem anfStmt_isNFK (e : ImpExpr) : ∀ n il, anfSrc il e = true →
    isNFK il (anfStmt n e).2 = true := by
  induction e using ImpExpr.ind with
  | lit l => intro n il _; simp [anfStmt, isNFK, nfRhs]
  | var x => intro n il _; simp [anfStmt, isNFK]
  | unitVal => intro n il _; simp [anfStmt, isNFK]
  | letBind x v b ihv ihb =>
    intro n il h
    simp only [anfSrc, Bool.and_eq_true] at h
    obtain ⟨⟨hb, hv⟩, hs⟩ := h
    have hr := (anfRhs_nf v n hv).1
    unfold anfStmt
    simp only [hb, if_true]
    exact hr.1.isNFK (by simp [isNFK, hr.2, ihb _ _ hs])
  | app f args ih =>
    intro n il h
    have hr := (anfRhs_nf (.app f args) n (by simpa [anfValSrc, anfSrc] using h)).1
    simp only [anfStmt]
    exact hr.1.isNFK (by simp [isNFK, hr.2])
  | proj b i ih =>
    intro n il h
    have hr := (anfRhs_nf (.proj b i) n (by simpa [anfValSrc, anfSrc] using h)).1
    simp only [anfStmt]
    exact hr.1.isNFK (by simp [isNFK, hr.2])
  | seq a b iha ihb =>
    intro n il h
    simp only [anfSrc, Bool.and_eq_true] at h
    simp [anfStmt, isNFK, iha _ _ h.1, ihb _ _ h.2]
  | ifThenElse c t f ihc iht ihf =>
    intro n il h
    simp only [anfSrc, Bool.and_eq_true] at h
    obtain ⟨⟨hc, ht⟩, hf⟩ := h
    have hr := (anfRhs_nf c n hc).2
    simp only [anfStmt]
    refine hr.1.isNFK ?_
    obtain ⟨x, hx⟩ := nfVar_eq hr.2
    rw [hx]
    simp [isNFK, iht _ _ ht, ihf _ _ hf]
  | assign x r ih =>
    intro n il h
    simp only [anfSrc, Bool.and_eq_true] at h
    have hr := (anfRhs_nf r n h.2).1
    simp only [anfStmt, h.1, if_true]
    exact hr.1.isNFK (by simp [isNFK, nfAssignRhs, hr.2])
  | tuple es ih =>
    intro n il h
    have hr := anfArgs_nf es n (by simpa [anfSrc] using h)
    simp only [anfStmt]
    exact hr.1.isNFK (by simp [isNFK, hr.2])
  | match_ scrut arms ihs iha =>
    intro n il h
    unfold anfSrc at h
    split at h
    all_goals try (rename_i heq; cases heq; done)
    all_goals try (simp at h; done)
    rename_i f args a b body heq
    cases heq
    simp only [Bool.and_eq_true] at h
    have hr := (anfRhs_nf (.app f args) n (by simpa [anfValSrc] using h.1)).1
    obtain ⟨args', hargs'⟩ := anfRhs_app n f args
    have hb := iha (.tuplePat [.varPat a, .varPat b], body) (by simp)
      (anfRhs n (.app f args)).1 _ h.2
    have hn := hr.2
    rw [hargs'] at hn
    unfold anfStmt
    simp only [anfArms]
    refine hr.1.isNFK ?_
    rw [hargs']
    simp only [nfRhs] at hn
    simp [isNFK, hn, hb]
  | whileLoop c b ihc ihb =>
    intro n il h
    cases c <;> simp [anfSrc] at h
    simp [anfStmt, isNFK, ihb _ _ h]
  | whileFold c b ihc ihb =>
    intro n il h
    cases c <;> simp [anfSrc] at h
    simp [anfStmt, normWhileTrue, isNFK, ihb _ _ h]
  | whileFoldReturn c b ihc ihb =>
    intro n il h
    cases c <;> simp [anfSrc] at h
    simp [anfStmt, isNFK, ihb _ _ h]
  | forFold v lo hi b _ _ ihb =>
    intro n il h
    simp only [anfSrc, Bool.and_eq_true] at h
    simp [anfStmt, isNFK, h.1.1, h.1.2, ihb _ _ h.2]
  | forFoldRev v lo hi b _ _ ihb =>
    intro n il h
    simp only [anfSrc, Bool.and_eq_true] at h
    simp [anfStmt, isNFK, h.1.1, h.1.2, ihb _ _ h.2]
  | forFoldReturn v lo hi b _ _ ihb =>
    intro n il h
    simp only [anfSrc, Bool.and_eq_true] at h
    simp [anfStmt, isNFK, h.1.1, h.1.2, ihb _ _ h.2]
  | forFoldRevReturn v lo hi b _ _ ihb =>
    intro n il h
    simp only [anfSrc, Bool.and_eq_true] at h
    simp [anfStmt, isNFK, h.1.1, h.1.2, ihb _ _ h.2]
  | cfBreak e _ => intro n il h; simpa [anfStmt, anfSrc, isNFK] using h
  | cfContinue e _ => intro n il h; simpa [anfStmt, anfSrc, isNFK] using h
  | cfBreakContinue e _ => intro n il h; simpa [anfStmt, anfSrc, isNFK] using h
  | typeAscription b s ih =>
    intro n il h
    simp only [anfSrc] at h
    simp [anfStmt, isNFK, ih _ _ h]
  | _ => intro n il h; simp [anfSrc] at h

/-- On the source fragment `anfSrc false`, `anfLowCT` produces the normal form
    `NF`. -/
theorem anfLowCT_NF (e : ImpExpr) (h : anfSrc false e = true) : NF (anfLowCT e) :=
  anfStmt_isNFK e 0 false h

theorem anfValSrcs_of_all_nfAtom {args : List ImpExpr} (h : args.all nfAtom = true) :
    anfValSrcs args = true := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases a <;> simp_all [anfValSrcs, anfValSrc, nfAtom]

theorem anfValSrcs_of_all_nfVar {args : List ImpExpr} (h : args.all nfVar = true) :
    anfValSrcs args = true := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases a <;> simp_all [anfValSrcs, anfValSrc, nfVar]

theorem bindable_of_nfRhs {v : ImpExpr} (h : nfRhs v = true) :
    bindableRhs v = true ∧ anfValSrc v = true := by
  cases v with
  | app f args => exact ⟨rfl, by simpa [anfValSrc] using anfValSrcs_of_all_nfAtom h⟩
  | proj b i => cases b <;> simp_all [nfRhs, bindableRhs, anfValSrc]
  | _ => simp_all [nfRhs, bindableRhs, anfValSrc]

/-- A normal form in loop context `il` lies in the source fragment `anfSrc il`, so
    `anfLowCT` maps `NF` into `NF`. -/
theorem anfSrc_of_isNFK (il : Bool) (e : ImpExpr) (h : isNFK il e = true) :
    anfSrc il e = true := by
  fun_induction isNFK il e <;>
    simp_all [-List.all_eq_true, anfSrc, anfValSrc, nfAssignRhs, bindable_of_nfRhs,
      anfValSrcs_of_all_nfAtom, anfValSrcs_of_all_nfVar]

/-! ### Denotation of the guard rewrite -/

/-- The value of `e` under the control-flow semantics `denote'`, when evaluation
    ends in a value. -/
def denoteValueCF (bi : Builtins) (fuel : Nat) (e : ImpExpr) (env : Env) : Option Value :=
  ((denote' bi fuel e).run env).1.toVal

/-- `denote'` at a `whileFold` is `denoteWhile'`. -/
theorem denote'_whileFold (bi : Builtins) (fuel : Nat) (c body : ImpExpr) :
    denote' bi fuel (.whileFold c body) = denoteWhile' bi fuel c body := by
  conv => lhs; unfold denote'

/-- A body `splitWhileGuard` splits is the guard chain over the guarded branch. -/
theorem splitWhileGuard_eq (body : ImpExpr) (gs : List (String × ImpExpr)) (g : String)
    (t : ImpExpr) (h : splitWhileGuard body = some (gs, g, t)) :
    body = bindChain gs (.ifThenElse (.var g) t (.seq (.cfBreak .unitVal) .unitVal)) := by
  induction body using splitWhileGuard.induct generalizing gs with
  | case1 x v rest hb ih =>
    simp only [splitWhileGuard, hb, if_true, Option.map_eq_some_iff] at h
    obtain ⟨⟨gs', g', t'⟩, hrest, heq⟩ := h
    cases heq
    simp only [bindChain]
    rw [← ih gs' hrest]
  | case2 x v rest hb =>
    simp [splitWhileGuard, hb] at h
  | case3 g' t' =>
    simp only [splitWhileGuard, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  | case4 e _ _ =>
    simp [splitWhileGuard] at h

/-- Continue with `k` from the environment of a guard chain whose outcome is
    `unit`; every other outcome passes through. -/
def afterGuard (p : Outcome × Env) (k : Env → Outcome × Env) : Outcome × Env :=
  match p with
  | (.val .unit, env) => k env
  | (o, env) => (o, env)

/-- `denote'` at `unitVal`. -/
theorem denote'_unitVal_run (bi : Builtins) (fuel : Nat) (env : Env) :
    denote' bi fuel .unitVal env = (.val .unit, env) := by
  conv => lhs; unfold denote'
  rfl

/-- One-step unfolding of `denote'` at a `letBind`. -/
theorem denote'_letBind_run (bi : Builtins) (fuel : Nat) (n : String) (v b : ImpExpr)
    (env : Env) :
    denote' bi fuel (.letBind n v b) env =
      match denote' bi fuel v env with
      | (.val (.controlFlow isBreak w), env') => (.val (.controlFlow isBreak w), env')
      | (.val w, env') => denote' bi fuel b (Env.extend env' n w)
      | (other, env') => (other, env') := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, pure, Pure.pure, StateT.pure, Id.run]
  generalize denote' bi fuel v env = p
  obtain ⟨rv, env'⟩ := p
  cases rv <;> try rfl
  rename_i w; cases w <;> rfl

/-- One-step unfolding of `denote'` at a `seq`. -/
theorem denote'_seq_run (bi : Builtins) (fuel : Nat) (a b : ImpExpr) (env : Env) :
    denote' bi fuel (.seq a b) env =
      match denote' bi fuel a env with
      | (.val (.controlFlow isBreak w), env') => (.val (.controlFlow isBreak w), env')
      | (.val _, env') => denote' bi fuel b env'
      | (other, env') => (other, env') := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  generalize denote' bi fuel a env = p
  obtain ⟨rv, env'⟩ := p
  cases rv <;> try rfl
  rename_i w; cases w <;> rfl

/-- One-step unfolding of `denote'` at an `assign`. -/
theorem denote'_assign_run (bi : Builtins) (fuel : Nat) (n : String) (v : ImpExpr)
    (env : Env) :
    denote' bi fuel (.assign n v) env =
      match denote' bi fuel v env with
      | (.val (.controlFlow isBreak w), env') => (.val (.controlFlow isBreak w), env')
      | (.val w, env') => (.val .unit, Env.extend env' n w)
      | (other, env') => (other, env') := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, pure, Pure.pure, StateT.pure, Id.run]
  generalize denote' bi fuel v env = p
  obtain ⟨rv, env'⟩ := p
  cases rv <;> try rfl
  rename_i w; cases w <;> rfl

/-- A `letBind` chain over `k` evaluates the chain and then `k`, from the
    environment the chain leaves, when the chain's outcome is `unit`. -/
theorem denote'_bindChain (bi : Builtins) (fuel : Nat) (gs : List (String × ImpExpr))
    (k : ImpExpr) : ∀ env,
    denote' bi fuel (bindChain gs k) env =
      afterGuard (denote' bi fuel (bindChain gs .unitVal) env) (denote' bi fuel k) := by
  induction gs with
  | nil =>
    intro env
    simp only [bindChain, denote'_unitVal_run, afterGuard]
  | cons xv rest ih =>
    intro env
    obtain ⟨x, v⟩ := xv
    simp only [bindChain, denote'_letBind_run]
    generalize denote' bi fuel v env = p
    obtain ⟨rv, env'⟩ := p
    cases rv <;> try rfl
    rename_i w; cases w <;> first | rfl | exact ih _

/-- `denote'` at a literal. -/
theorem denote'_lit_run (bi : Builtins) (fuel : Nat) (l : ImpLit) (env : Env) :
    denote' bi fuel (.lit l) env = (.val (Value.ofLit l), env) := by
  conv => lhs; unfold denote'
  rfl

/-- `denote'` at a variable. -/
theorem denote'_var_run (bi : Builtins) (fuel : Nat) (x : String) (env : Env) :
    denote' bi fuel (.var x) env =
      match env x with
      | some v => (.val v, env)
      | none => (.err s!"undefined variable: {x}", env) := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, Pure.pure, StateT.pure, Id.run]
  cases env x <;> rfl

/-- `denote'` at a value-less `cfBreak`. -/
theorem denote'_cfBreak_unit_run (bi : Builtins) (fuel : Nat) (env : Env) :
    denote' bi fuel (.cfBreak .unitVal) env = (.val (.controlFlow true .unit), env) := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  rw [denote'_unitVal_run]
  rfl

/-- `denote'` at the `break` statement hax leaves in the else-branch of a
    desugared `while` guard. -/
theorem denote'_breakStmt_run (bi : Builtins) (fuel : Nat) (env : Env) :
    denote' bi fuel (.seq (.cfBreak .unitVal) .unitVal) env =
      (.val (.controlFlow true .unit), env) := by
  rw [denote'_seq_run, denote'_cfBreak_unit_run]

/-- One-step unfolding of `denote'` at an `ifThenElse`. -/
theorem denote'_ifThenElse_run (bi : Builtins) (fuel : Nat) (c t e : ImpExpr) (env : Env) :
    denote' bi fuel (.ifThenElse c t e) env =
      match denote' bi fuel c env with
      | (.val (.controlFlow isBreak w), env') => (.val (.controlFlow isBreak w), env')
      | (.val (.bool true), env') => denote' bi fuel t env'
      | (.val (.bool false), env') => denote' bi fuel e env'
      | (.val _, env') => (.err "if condition not a bool", env')
      | (other, env') => (other, env') := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  generalize denote' bi fuel c env = p
  obtain ⟨rv, env'⟩ := p
  cases rv <;> try rfl
  rename_i w; cases w <;> try rfl
  rename_i b; cases b <;> rfl

/-- The `assign` sequence of a chain denotes as the chain itself. -/
theorem denote'_assignSeq (bi : Builtins) (fuel : Nat) (gs : List (String × ImpExpr)) :
    ∀ env, denote' bi fuel (assignSeq gs) env = denote' bi fuel (bindChain gs .unitVal) env := by
  induction gs with
  | nil => intro env; rfl
  | cons xv rest ih =>
    intro env
    obtain ⟨x, v⟩ := xv
    simp only [assignSeq, bindChain, denote'_seq_run, denote'_assign_run, denote'_letBind_run]
    generalize denote' bi fuel v env = p
    obtain ⟨rv, env'⟩ := p
    cases rv <;> try rfl
    rename_i w; cases w <;> first | rfl | exact ih _

/-- One trip of `denoteWhile'` at positive fuel. -/
theorem denoteWhile'_succ_run (bi : Builtins) (n : Nat) (cond body : ImpExpr) (env : Env) :
    denoteWhile' bi (n + 1) cond body env =
      match denote' bi (n + 1) cond env with
      | (.val (.controlFlow isBreak v), env') => (.val (.controlFlow isBreak v), env')
      | (.val (.bool true), env') =>
          match denote' bi (n + 1) body env' with
          | (.val (.controlFlow true v), env'') => (.val v, env'')
          | (.val (.controlFlow false _), env'') => denoteWhile' bi n cond body env''
          | (.val _, env'') => denoteWhile' bi n cond body env''
          | (other, env'') => (other, env'')
      | (.val (.bool false), env') => (.val .unit, env')
      | (.val _, env') => (.err "while condition not a bool", env')
      | (other, env') => (other, env') := by
  have hfuel : ¬(n + 1 = 0) := by omega
  conv => lhs; unfold denoteWhile'
  rw [if_neg hfuel]
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  simp only [show n + 1 - 1 = n from rfl]
  generalize denote' bi (n + 1) cond env = p
  obtain ⟨rc, env'⟩ := p
  cases rc <;> try rfl
  rename_i w; cases w <;> try rfl
  rename_i b; cases b <;> try rfl
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  generalize denote' bi (n + 1) body env' = q
  obtain ⟨rb, env''⟩ := q
  cases rb <;> try rfl
  rename_i w; cases w <;> try rfl
  rename_i b _; cases b <;> rfl

/-- A guard chain `G` whose outcome is `unit` or an error, is the same at every
    fuel, and leaves a boolean in `g` whenever its outcome is `unit`. The
    hoisted condition of a `while` has this property: its right-hand sides are
    applications of builtins to variables and literals. -/
structure GuardChain (bi : Builtins) (gs : List (String × ImpExpr)) (g : String) : Prop where
  fuel_free : ∀ fuel env,
    denote' bi fuel (bindChain gs .unitVal) env = denote' bi 1 (bindChain gs .unitVal) env
  outcome : ∀ env, (∃ env', denote' bi 1 (bindChain gs .unitVal) env = (.val .unit, env')) ∨
    (∃ msg env', denote' bi 1 (bindChain gs .unitVal) env = (.err msg, env'))
  guard_bool : ∀ env env', denote' bi 1 (bindChain gs .unitVal) env = (.val .unit, env') →
    ∃ b, env' g = some (.bool b)

/-- The loop `whileFold (lit true) (G; ifThenElse (var g) T (break))` and the loop
    `whileFold (var g) (T; G')` entered after `G` compute the same value at every
    fuel, for a guard chain `G` and a body `T` that never continues. -/
theorem denoteWhile'_guard_rewrite (bi : Builtins) (gs : List (String × ImpExpr))
    (g : String) (t : ImpExpr) (hG : GuardChain bi gs g)
    (hT : ∀ fuel env w, (denote' bi fuel t env).1 ≠ .val (.controlFlow false w)) :
    ∀ fuel env,
      (denoteWhile' bi fuel (.lit (.bool true))
        (bindChain gs (.ifThenElse (.var g) t (.seq (.cfBreak .unitVal) .unitVal))) env).1.toVal =
      (afterGuard (denote' bi fuel (bindChain gs .unitVal) env)
        (denoteWhile' bi fuel (.var g) (.seq t (assignSeq gs)))).1.toVal := by
  intro fuel
  induction fuel with
  | zero =>
    intro env
    rw [hG.fuel_free]
    rcases hG.outcome env with ⟨env', h⟩ | ⟨msg, env', h⟩ <;> rw [h] <;> unfold denoteWhile' <;> rfl
  | succ n ih =>
    intro env
    rw [denoteWhile'_succ_run, denote'_lit_run]
    simp only [Value.ofLit]
    rw [denote'_bindChain bi (n + 1) gs (.ifThenElse (.var g) t (.seq (.cfBreak .unitVal) .unitVal)) env,
      hG.fuel_free (n + 1) env]
    rcases hG.outcome env with ⟨env', h⟩ | ⟨msg, env', h⟩ <;> rw [h]
    · obtain ⟨b, hb⟩ := hG.guard_bool env env' h
      simp only [afterGuard]
      rw [denote'_ifThenElse_run, denote'_var_run, hb, denoteWhile'_succ_run, denote'_var_run, hb]
      cases b <;> dsimp only
      · rw [denote'_breakStmt_run]
      · rw [denote'_seq_run]
        have hTp := hT (n + 1) env'
        generalize denote' bi (n + 1) t env' = p at hTp ⊢
        obtain ⟨ot, env''⟩ := p
        cases ot <;> try rfl
        rename_i w; cases w <;> dsimp only
        case controlFlow isBreak w' =>
          cases isBreak
          · exact absurd rfl (hTp w')
          · rfl
        all_goals
          rw [ih env'', denote'_assignSeq, hG.fuel_free (n + 1) env'', hG.fuel_free n env'']
          rcases hG.outcome env'' with ⟨env''', h2⟩ | ⟨msg, env''', h2⟩ <;> rw [h2] <;> rfl
    · rfl

/-- `normWhileTrue` preserves the value of a desugared `while` at every fuel, for
    a guard chain `G` and a then-branch `T` that never continues. -/
theorem normWhileTrue_denoteValueCF (bi : Builtins) (body : ImpExpr)
    (gs : List (String × ImpExpr)) (g : String) (t : ImpExpr)
    (hs : splitWhileGuard body = some (gs, g, t)) (hc : noLoopContinue t = true)
    (hG : GuardChain bi gs g)
    (hT : ∀ fuel env w, (denote' bi fuel t env).1 ≠ .val (.controlFlow false w)) :
    ∀ fuel env,
      denoteValueCF bi fuel (.whileFold (.lit (.bool true)) body) env =
        denoteValueCF bi fuel (normWhileTrue (.lit (.bool true)) body) env := by
  intro fuel env
  simp only [normWhileTrue, hs, hc, if_true]
  rw [splitWhileGuard_eq body gs g t hs]
  simp only [denoteValueCF, StateT.run]
  rw [denote'_whileFold, denote'_bindChain, denote'_whileFold]
  exact denoteWhile'_guard_rewrite bi gs g t hG hT fuel env

/-! Static checks pinning the three shapes the rewrite is responsible for: the
hoisting order of a nested application, the binding of a tail application, and
the limb read left in place. A shape that drifts turns an accepted front into a
rejected one with no other local signal. These run on four-node terms. -/

-- Nested arguments are hoisted left to right, and the tail names its binder.
#guard anfLowCT (.app "Add" [.app "Mul" [.var "a", .var "b"], .var "c"])
  == .letBind "_anf0" (.app "Mul" [.var "a", .var "b"])
       (.letBind "_anf1" (.app "Add" [.var "_anf0", .var "c"]) (.var "_anf1"))

-- A literal argument is hoisted too: `haxToLowCT` reads only variables.
#guard anfLowCT (.letBind "x" (.app "Shl" [.var "a", .lit (.int 51)]) (.var "x"))
  == .letBind "_anf0" (.lit (.int 51))
       (.letBind "x" (.app "Shl" [.var "a", .var "_anf0"]) (.var "x"))

-- A limb read keeps its literal index, which `haxToLowCT` reads directly.
#guard anfLowCT (.letBind "x" (.app "index" [.var "a", .lit (.int 0)]) (.var "x"))
  == .letBind "x" (.app "index" [.var "a", .lit (.int 0)]) (.var "x")

-- A branch condition becomes a variable; the branches stay where they are.
#guard anfLowCT (.ifThenElse (.app "Ne" [.var "a", .var "b"]) (.var "x") (.var "y"))
  == .letBind "_anf0" (.app "Ne" [.var "a", .var "b"])
       (.ifThenElse (.var "_anf0") (.var "x") (.var "y"))

/-! ### Loop guards

Static checks for `normWhileTrue`: the desugaring of a `while` becomes a
variable-guarded loop, a loop whose then-branch continues is left alone, and the
rewritten loop denotes as the original under `denote'`. -/

-- `while k > 0 { k = k - 1 }` as hax desugars it.
#guard anfLowCT (.whileFold (.lit (.bool true))
    (.ifThenElse (.app "Gt" [.var "k", .lit (.int 0)])
      (.letBind "k" (.app "Sub" [.var "k", .lit (.int 1)]) (.var "k"))
      (.seq (.cfBreak .unitVal) .unitVal)))
  == .letBind "_anf0" (.lit (.int 0))
      (.letBind "_anf1" (.app "Gt" [.var "k", .var "_anf0"])
        (.whileFold (.var "_anf1")
          (.seq (.letBind "_anf2" (.lit (.int 1))
                  (.letBind "k" (.app "Sub" [.var "k", .var "_anf2"]) (.var "k")))
            (.seq (.assign "_anf0" (.lit (.int 0)))
              (.seq (.assign "_anf1" (.app "Gt" [.var "k", .var "_anf0"])) .unitVal)))))

-- A `continue` in the then-branch reaches the loop, so the loop is left as it is.
#guard anfLowCT (.whileFold (.lit (.bool true))
    (.ifThenElse (.var "g") (.seq (.cfContinue .unitVal) .unitVal)
      (.seq (.cfBreak .unitVal) .unitVal)))
  == .whileFold (.lit (.bool true))
      (.ifThenElse (.var "g") (.seq (.cfContinue .unitVal) .unitVal)
        (.seq (.cfBreak .unitVal) .unitVal))

/-- `k := 5; acc := 0; while k > 0 { acc := acc + k; k := k - 1 }; acc`, as hax
    desugars it: the fixture of the differential check on a single loop. -/
def whileDesugaredFixture : ImpExpr :=
  .letBind "k" (.lit (.int 5)) (.letBind "acc" (.lit (.int 0))
    (.seq (.whileFold (.lit (.bool true))
      (.ifThenElse (.app "gt" [.var "k", .lit (.int 0)])
        (.seq (.letBind "acc" (.app "add" [.var "acc", .var "k"]) (.var "acc"))
              (.letBind "k" (.app "sub" [.var "k", .lit (.int 1)]) (.var "k")))
        (.seq (.cfBreak .unitVal) .unitVal)))
     (.var "acc")))

/-- `k := 3; acc := 0; while k > 0 { j := 4; while j > 0 { if j == 2 { break };
    j := j - 1; acc := acc + 1 }; k := k - 1 }; acc`, as hax desugars it: the
    fixture of the differential check on nested loops with a `break` that is not
    the else-branch of a guard. -/
def whileNestedFixture : ImpExpr :=
  .letBind "k" (.lit (.int 3)) (.letBind "acc" (.lit (.int 0))
    (.seq (.whileFold (.lit (.bool true))
      (.ifThenElse (.app "gt" [.var "k", .lit (.int 0)])
        (.letBind "j" (.lit (.int 4))
          (.seq (.whileFold (.lit (.bool true))
            (.ifThenElse (.app "gt" [.var "j", .lit (.int 0)])
              (.seq (.ifThenElse (.app "eq" [.var "j", .lit (.int 2)])
                      (.seq (.cfBreak .unitVal) .unitVal) .unitVal)
                (.seq (.letBind "j" (.app "sub" [.var "j", .lit (.int 1)]) (.var "j"))
                      (.letBind "acc" (.app "add" [.var "acc", .lit (.int 1)]) (.var "acc"))))
              (.seq (.cfBreak .unitVal) .unitVal)))
            (.letBind "k" (.app "sub" [.var "k", .lit (.int 1)]) (.var "k"))))
        (.seq (.cfBreak .unitVal) .unitVal)))
     (.var "acc")))

-- The differential check: source and normalised form denote alike, and to the
-- value the Rust source computes.
#guard denoteValueCF fullBuiltins 64 whileDesugaredFixture Env.empty == some (.int 15)
#guard denoteValueCF fullBuiltins 64 (anfLowCT whileDesugaredFixture) Env.empty
  == some (.int 15)
#guard denoteValueCF fullBuiltins 64 whileNestedFixture Env.empty == some (.int 6)
#guard denoteValueCF fullBuiltins 64 (anfLowCT whileNestedFixture) Env.empty
  == some (.int 6)

/-- A variable. -/
def anfIsVar : ImpExpr → Bool
  | .var _ => true
  | _ => false

/-- The statement fragment `haxToLowCT` lowers, restricted to the constructors a
    normalised `while` can contain. Each arm mirrors the arm of the same shape in
    `CatCrypt.Crypto.Hax.HaxToLowCT.AnfShaped`, which cannot be imported here
    because the compiler package depends on this one. -/
partial def whileFragmentShaped : ImpExpr → Bool
  | .letBind _ (.app _ args) body => args.all anfIsVar && whileFragmentShaped body
  | .letBind _ (.lit (.int n)) body => decide (n ≥ 0) && whileFragmentShaped body
  | .letBind _ (.lit (.bool _)) body => whileFragmentShaped body
  | .letBind _ (.var _) body => whileFragmentShaped body
  | .letBind _ (.proj (.var _) _) body => whileFragmentShaped body
  | .var _ | .unitVal => true
  | .seq a b => whileFragmentShaped a && whileFragmentShaped b
  | .ifThenElse (.var _) t e => whileFragmentShaped t && whileFragmentShaped e
  | .assign _ (.lit (.int n)) => decide (n ≥ 0)
  | .assign _ (.lit (.bool _)) => true
  | .assign _ (.app _ args) => args.all anfIsVar
  | .whileFold (.var _) body => whileFragmentShaped body
  | .typeAscription e _ => whileFragmentShaped e
  | _ => false

/-- The `_impExprAnf` literal `PrettyPrintT` prints for the ristretto255
    `Field::pow` body before the guard rewrite: two nested `while` loops, each
    desugared to a `loop` with a guarded `break`. -/
def fieldPowDesugaredFixture : ImpExpr :=
  (.letBind "self" (.var "self") (.letBind "exp" (.var "exp") (.letBind "result" (.var "ONE") (.letBind "k" (.app "len" [(.var "exp")]) (.seq (.whileFold (.lit (ImpLit.bool true)) (.letBind "_anf0" (.lit (ImpLit.int 0)) (.letBind "_anf1" (.app "Gt" [(.var "k"), (.var "_anf0")]) (.ifThenElse (.var "_anf1") (.seq (.seq (.letBind "_anf2" (.lit (ImpLit.int 1)) (.letBind "k" (.app "Sub" [(.var "k"), (.var "_anf2")]) (.var "k"))) .unitVal) (.letBind "limb" (.app "index" [(.var "exp"), (.var "k")]) (.letBind "i" (.lit (ImpLit.int 64)) (.whileFold (.lit (ImpLit.bool true)) (.letBind "_anf3" (.lit (ImpLit.int 0)) (.letBind "_anf4" (.app "Gt" [(.var "i"), (.var "_anf3")]) (.ifThenElse (.var "_anf4") (.seq (.seq (.letBind "_anf5" (.lit (ImpLit.int 1)) (.letBind "i" (.app "Sub" [(.var "i"), (.var "_anf5")]) (.var "i"))) .unitVal) (.seq (.seq (.letBind "result" (.app "Field_square" [(.var "result")]) (.var "result")) .unitVal) (.letBind "_anf6" (.app "Shr#64" [(.var "limb"), (.var "i")]) (.letBind "_anf7" (.lit (ImpLit.int 1)) (.letBind "_anf8" (.app "BitAnd#64" [(.var "_anf6"), (.var "_anf7")]) (.letBind "_anf9" (.lit (ImpLit.int 1)) (.letBind "_anf10" (.app "Eq" [(.var "_anf8"), (.var "_anf9")]) (.ifThenElse (.var "_anf10") (.seq (.seq (.letBind "result" (.app "Field_mul" [(.var "result"), (.var "self")]) (.var "result")) .unitVal) .unitVal) .unitVal)))))))) (.seq (.cfBreak .unitVal) .unitVal)))))))) (.seq (.cfBreak .unitVal) .unitVal))))) (.var "result"))))))

-- The single-loop fixture and the `Field::pow` body normalise into the fragment
-- `haxToLowCT` lowers. The nested fixture does not: its `break` inside the inner
-- then-branch has no image in `LowCT`, and stays where it is.
#guard whileFragmentShaped (anfLowCT whileDesugaredFixture)
#guard whileFragmentShaped (anfLowCT fieldPowDesugaredFixture)
#guard !whileFragmentShaped (anfLowCT whileNestedFixture)

end Hax
