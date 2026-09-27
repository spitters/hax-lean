/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.SemanticsCF
public import HaxLean.Phase.RewriteAppName

/-!
# Monomorphisation of trait-generic functions

The `ImpExpr` literal of a Rust function generic over a trait bound calls the trait's
methods by their bare names: `fn f<F: Field>(x: F, y: F) -> F { x.mul(y).add(x) }`
reads `.app "add" [.app "mul" [x, y], x]`. At an instance type the methods are the
functions of the trait `impl` for that type, which the extraction names separately
(`Field_add`, `Plonky3Crypto_field_add`). A monomorphisation table `MonoTable` lists,
for each pair of a method name and an instance type, the name of the implementing
function. `monomorphise tbl insts e` renames every call of a method of `e` to its
implementation at the first instance of `insts` the table lists for it; every other
call is kept.

The pass is a simultaneous renaming of call heads, `renameCalls σ`. Under `denote'`,
renaming the call heads of `e` by `σ` has the effect of reading `e` with the builtin
table `bi.viaNames σ`, which answers a call of `f` as `bi` answers a call of `σ f`.
For `monomorphise`, that table is `bi` extended by the method table of the instances: a
method answers as its implementation, every other name as in `bi`.

The two runs agree up to the text of an error: a call no builtin answers ends in
`.err` with a message naming the called function, which is `σ f` in one run and `f` in
the other. `ErrEq` is this agreement: the same final environment, and the same outcome
once the text of an error is erased. A run of either side that ends in anything but an
error is a run of the other (`ErrEq.run_eq`).

## Main definitions

* `renameCalls σ`: rename the head `f` of every call to `σ f`.
* `Builtins.viaNames bi σ`: the builtin table answering `f` as `bi` answers `σ f`.
* `ErrEq`: agreement of two runs up to the text of an error.
* `MethodImpl`, `MonoTable`: the implementation of a trait method at an instance type.
* `MonoTable.resolve tbl insts`: the implementing function of a method name at the
  instances `insts`, and the name itself for a name the table does not list.
* `monomorphise tbl insts`: `renameCalls (tbl.resolve insts)`.

## Main results

* `denote'_renameCalls`: `ErrEq (denote' bi fuel (renameCalls σ e))
  (denote' (bi.viaNames σ) fuel e)`, for every fuel and expression.
* `denote'_monomorphise`: the specialised body under `bi` runs as the generic body
  under `bi` extended by the method table of the instances.
* `denote'_monomorphise_run`: every run of the generic body that does not end in an
  error is the run of the specialised body.
* `rewriteAppName_eq_renameCalls`, `denote'_rewriteAppName`: the single-name renaming
  `rewriteAppName` is `renameCalls` at a one-point renaming, and it preserves `denote'`
  up to the text of an error when the two names are the same builtin.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Monomorphise

/-- Rename the head `f` of every call `.app f args` to `σ f`; every other node is kept. -/
def renameCalls (σ : String → String) : ImpExpr → ImpExpr
  | .lit v => .lit v
  | .var n => .var n
  | .unitVal => .unitVal
  | .continue_ => .continue_
  | .break_ none => .break_ none
  | .break_ (some e) => .break_ (some (renameCalls σ e))
  | .lam ps body => .lam ps (renameCalls σ body)
  | .app f args => .app (σ f) (mapExpr σ args)
  | .letBind n v body => .letBind n (renameCalls σ v) (renameCalls σ body)
  | .seq a b => .seq (renameCalls σ a) (renameCalls σ b)
  | .ifThenElse c t e => .ifThenElse (renameCalls σ c) (renameCalls σ t) (renameCalls σ e)
  | .tuple es => .tuple (mapExpr σ es)
  | .proj e i => .proj (renameCalls σ e) i
  | .match_ scrut arms => .match_ (renameCalls σ scrut) (mapArms σ arms)
  | .borrow e => .borrow (renameCalls σ e)
  | .deref e => .deref (renameCalls σ e)
  | .assign n rhs => .assign n (renameCalls σ rhs)
  | .forLoop v lo hi body =>
    .forLoop v (renameCalls σ lo) (renameCalls σ hi) (renameCalls σ body)
  | .forLoopRev v lo hi body =>
    .forLoopRev v (renameCalls σ lo) (renameCalls σ hi) (renameCalls σ body)
  | .whileLoop c body => .whileLoop (renameCalls σ c) (renameCalls σ body)
  | .earlyReturn e => .earlyReturn (renameCalls σ e)
  | .questionMark e => .questionMark (renameCalls σ e)
  | .forFold v lo hi body =>
    .forFold v (renameCalls σ lo) (renameCalls σ hi) (renameCalls σ body)
  | .forFoldRev v lo hi body =>
    .forFoldRev v (renameCalls σ lo) (renameCalls σ hi) (renameCalls σ body)
  | .whileFold c body => .whileFold (renameCalls σ c) (renameCalls σ body)
  | .forFoldReturn v lo hi body =>
    .forFoldReturn v (renameCalls σ lo) (renameCalls σ hi) (renameCalls σ body)
  | .forFoldRevReturn v lo hi body =>
    .forFoldRevReturn v (renameCalls σ lo) (renameCalls σ hi) (renameCalls σ body)
  | .whileFoldReturn c body => .whileFoldReturn (renameCalls σ c) (renameCalls σ body)
  | .cfBreak e => .cfBreak (renameCalls σ e)
  | .cfContinue e => .cfContinue (renameCalls σ e)
  | .cfBreakContinue e => .cfBreakContinue (renameCalls σ e)
  | .typeAscription e ty => .typeAscription (renameCalls σ e) ty
where
  /-- `renameCalls σ` on every expression of a list. -/
  mapExpr (σ : String → String) : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => renameCalls σ e :: mapExpr σ es
  /-- `renameCalls σ` on the body of every match arm. -/
  mapArms (σ : String → String) : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, renameCalls σ e) :: mapArms σ rest

@[simp] theorem renameCalls.mapExpr_eq (σ : String → String) (es : List ImpExpr) :
    renameCalls.mapExpr σ es = es.map (renameCalls σ) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [renameCalls.mapExpr, ih]

@[simp] theorem renameCalls.mapArms_eq (σ : String → String)
    (arms : List (ImpPat × ImpExpr)) :
    renameCalls.mapArms σ arms = arms.map fun (p, e) => (p, renameCalls σ e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [renameCalls.mapArms, ih]

/-- The builtin table answering a call of `f` as `bi` answers a call of `σ f`. -/
def _root_.Hax.Builtins.viaNames (bi : Builtins) (σ : String → String) : Builtins :=
  fun f args => bi (σ f) args

/-! ## Agreement up to the text of an error -/

/-- An outcome with the text of an error erased. -/
def eraseErr : Outcome → Outcome
  | .err _ => .err ""
  | o => o

theorem eraseErr_eq {o₁ o₂ : Outcome} (h : eraseErr o₁ = eraseErr o₂) :
    o₁ = o₂ ∨ ∃ a b, o₁ = .err a ∧ o₂ = .err b := by
  cases o₁ <;> cases o₂ <;> simp_all [eraseErr]

/-- Two runs agree up to the text of an error: from every environment they end in the
    same environment, with the same outcome once the text of an error is erased. -/
def ErrEq (m₁ m₂ : StateM Env Outcome) : Prop :=
  ∀ env, (m₁.run env).2 = (m₂.run env).2 ∧ eraseErr (m₁.run env).1 = eraseErr (m₂.run env).1

theorem run_bind {α β : Type} (x : StateM Env α) (k : α → StateM Env β) (env : Env) :
    (x >>= k).run env = (k (x.run env).1).run (x.run env).2 := rfl

theorem ErrEq.refl (m : StateM Env Outcome) : ErrEq m m := fun _ => ⟨rfl, rfl⟩

theorem ErrEq.pure_err (a b : String) :
    ErrEq (pure (Outcome.err a)) (pure (Outcome.err b)) := fun _ => ⟨rfl, rfl⟩

theorem ErrEq.bind {m₁ m₂ : StateM Env Outcome} {k₁ k₂ : Outcome → StateM Env Outcome}
    (hm : ErrEq m₁ m₂) (hv : ∀ o, ErrEq (k₁ o) (k₂ o))
    (he : ∀ a b, ErrEq (k₁ (.err a)) (k₂ (.err b))) : ErrEq (m₁ >>= k₁) (m₂ >>= k₂) := by
  intro env
  obtain ⟨hs, ho⟩ := hm env
  rw [run_bind, run_bind, hs]
  rcases eraseErr_eq ho with h | ⟨a, b, h₁, h₂⟩
  · rw [h]; exact hv _ _
  · rw [h₁, h₂]; exact he a b _

theorem ErrEq.bindU {α : Type} (x : StateM Env α) {k₁ k₂ : α → StateM Env Outcome}
    (h : ∀ a, ErrEq (k₁ a) (k₂ a)) : ErrEq (x >>= k₁) (x >>= k₂) := by
  intro env
  rw [run_bind, run_bind]
  exact h _ _

/-- A bind whose continuation does not read the text of an error, after two runs that
    agree up to it, is one computation. -/
theorem ErrEq.bind_eq {α : Type} {m₁ m₂ : StateM Env Outcome} {k : Outcome → StateM Env α}
    (hm : ErrEq m₁ m₂) (he : ∀ a b, k (.err a) = k (.err b)) : m₁ >>= k = m₂ >>= k := by
  funext env
  obtain ⟨hs, ho⟩ := hm env
  show (m₁ >>= k).run env = (m₂ >>= k).run env
  rw [run_bind, run_bind, hs]
  rcases eraseErr_eq ho with h | ⟨a, b, h₁, h₂⟩
  · rw [h]
  · rw [h₁, h₂, he a b]

/-- A run of the second computation that does not end in an error is a run of the
    first. -/
theorem ErrEq.run_eq {m₁ m₂ : StateM Env Outcome} (h : ErrEq m₁ m₂) {env env' : Env}
    {o : Outcome} (hr : m₂.run env = (o, env')) (ho : ∀ a, o ≠ .err a) :
    m₁.run env = (o, env') := by
  obtain ⟨hs, he⟩ := h env
  rw [hr] at hs he
  rcases eraseErr_eq he with h1 | ⟨a, b, _, h2⟩
  · exact Prod.ext h1 hs
  · exact absurd h2 (ho b)

/-- One step of an `ErrEq` proof between two runs of the same shape: identical runs,
    a hypothesis, a bind of a shared computation, or a bind of two agreeing runs
    followed by a case split on the outcome. -/
syntax "errEq_step" : tactic

macro_rules
  | `(tactic| errEq_step) => `(tactic| first
      | exact ErrEq.refl _
      | solve_by_elim (maxDepth := 2)
      | (refine ErrEq.bind (by solve_by_elim (maxDepth := 2)) (fun o => ?_) (fun a b => ?_)
         · split <;> (try split) <;> first | errEq_step | (exfalso; simp_all)
         · first
             | exact ErrEq.pure_err a b
             | (split <;> (try split) <;> first | exact ErrEq.pure_err _ _ | (exfalso; simp_all)))
      | (refine ErrEq.bindU _ fun _ => ?_; errEq_step))

/-! ## Loop helpers under two builtin tables -/

section Loops

variable {bi₁ bi₂ : Builtins}

theorem forLoop'_errEq {v : String} {b₁ b₂ : ImpExpr}
    (h : ∀ fuel, ErrEq (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel lo hi,
      ErrEq (denoteForLoop' bi₁ fuel v lo hi b₁) (denoteForLoop' bi₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero => intro lo hi; unfold denoteForLoop'; by_cases hl : lo ≥ hi <;> simp [hl, ErrEq.refl]
  | succ n ih =>
    intro lo hi; unfold denoteForLoop'
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; exact ErrEq.refl _
    · simp only [hl, if_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      errEq_step

theorem forLoopRev'_errEq {v : String} {b₁ b₂ : ImpExpr}
    (h : ∀ fuel, ErrEq (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel lo hi,
      ErrEq (denoteForLoopRev' bi₁ fuel v lo hi b₁) (denoteForLoopRev' bi₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopRev'; by_cases hl : lo ≥ hi <;> simp [hl, ErrEq.refl]
  | succ n ih =>
    intro lo hi; unfold denoteForLoopRev'
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; exact ErrEq.refl _
    · simp only [hl, if_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      errEq_step

theorem forLoopOrig'_errEq {v : String} {b₁ b₂ : ImpExpr}
    (h : ∀ fuel, ErrEq (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel lo hi,
      ErrEq (denoteForLoopOrig' bi₁ fuel v lo hi b₁) (denoteForLoopOrig' bi₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopOrig'; by_cases hl : lo ≥ hi <;> simp [hl, ErrEq.refl]
  | succ n ih =>
    intro lo hi; unfold denoteForLoopOrig'
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; exact ErrEq.refl _
    · simp only [hl, if_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      errEq_step

theorem forLoopRevOrig'_errEq {v : String} {b₁ b₂ : ImpExpr}
    (h : ∀ fuel, ErrEq (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel lo hi,
      ErrEq (denoteForLoopRevOrig' bi₁ fuel v lo hi b₁)
        (denoteForLoopRevOrig' bi₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopRevOrig'; by_cases hl : lo ≥ hi <;> simp [hl, ErrEq.refl]
  | succ n ih =>
    intro lo hi; unfold denoteForLoopRevOrig'
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; exact ErrEq.refl _
    · simp only [hl, if_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      errEq_step

theorem forLoop'Return_errEq {v : String} {b₁ b₂ : ImpExpr}
    (h : ∀ fuel, ErrEq (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel lo hi,
      ErrEq (denoteForLoop'Return bi₁ fuel v lo hi b₁)
        (denoteForLoop'Return bi₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoop'Return; by_cases hl : lo ≥ hi <;> simp [hl, ErrEq.refl]
  | succ n ih =>
    intro lo hi; unfold denoteForLoop'Return
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; exact ErrEq.refl _
    · simp only [hl, if_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      errEq_step

theorem forLoopRev'Return_errEq {v : String} {b₁ b₂ : ImpExpr}
    (h : ∀ fuel, ErrEq (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel lo hi,
      ErrEq (denoteForLoopRev'Return bi₁ fuel v lo hi b₁)
        (denoteForLoopRev'Return bi₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopRev'Return
    by_cases hl : lo ≥ hi <;> simp [hl, ErrEq.refl]
  | succ n ih =>
    intro lo hi; unfold denoteForLoopRev'Return
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; exact ErrEq.refl _
    · simp only [hl, if_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      errEq_step

theorem while'_errEq {c₁ c₂ b₁ b₂ : ImpExpr}
    (hc : ∀ fuel, ErrEq (denote' bi₁ fuel c₁) (denote' bi₂ fuel c₂))
    (h : ∀ fuel, ErrEq (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel, ErrEq (denoteWhile' bi₁ fuel c₁ b₁) (denoteWhile' bi₂ fuel c₂ b₂) := by
  intro fuel
  induction fuel with
  | zero => unfold denoteWhile'; simp only [if_true]; exact ErrEq.refl _
  | succ n ih =>
    unfold denoteWhile'
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    errEq_step

theorem whileOrig'_errEq {c₁ c₂ b₁ b₂ : ImpExpr}
    (hc : ∀ fuel, ErrEq (denote' bi₁ fuel c₁) (denote' bi₂ fuel c₂))
    (h : ∀ fuel, ErrEq (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel, ErrEq (denoteWhileOrig' bi₁ fuel c₁ b₁) (denoteWhileOrig' bi₂ fuel c₂ b₂) := by
  intro fuel
  induction fuel with
  | zero => unfold denoteWhileOrig'; simp only [if_true]; exact ErrEq.refl _
  | succ n ih =>
    unfold denoteWhileOrig'
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    errEq_step

theorem while'Return_errEq {c₁ c₂ b₁ b₂ : ImpExpr}
    (hc : ∀ fuel, ErrEq (denote' bi₁ fuel c₁) (denote' bi₂ fuel c₂))
    (h : ∀ fuel, ErrEq (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel, ErrEq (denoteWhile'Return bi₁ fuel c₁ b₁) (denoteWhile'Return bi₂ fuel c₂ b₂) := by
  intro fuel
  induction fuel with
  | zero => unfold denoteWhile'Return; simp only [if_true]; exact ErrEq.refl _
  | succ n ih =>
    unfold denoteWhile'Return
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    errEq_step

end Loops

/-! ## Renaming the call heads -/

section Rename

variable (bi : Builtins) (σ : String → String)

theorem denoteArgs'_renameCalls (args : List ImpExpr)
    (ih : ∀ a, a ∈ args → ∀ fuel,
      ErrEq (denote' bi fuel (renameCalls σ a)) (denote' (bi.viaNames σ) fuel a))
    (fuel : Nat) :
    denoteArgs' bi fuel (args.map (renameCalls σ)) = denoteArgs' (bi.viaNames σ) fuel args := by
  induction args with
  | nil => simp only [List.map_nil, denoteArgs']
  | cons a as iha =>
    simp only [List.map_cons, denoteArgs',
      iha (fun b hb => ih b (List.mem_cons_of_mem a hb))]
    exact ErrEq.bind_eq (ih a List.mem_cons_self fuel) (fun _ _ => rfl)

theorem denoteMatchArms'_renameCalls (arms : List (ImpPat × ImpExpr))
    (ih : ∀ pa, pa ∈ arms → ∀ fuel,
      ErrEq (denote' bi fuel (renameCalls σ pa.2)) (denote' (bi.viaNames σ) fuel pa.2))
    (fuel : Nat) (v : Value) :
    ErrEq (denoteMatchArms' bi fuel v (arms.map fun (p, e) => (p, renameCalls σ e)))
      (denoteMatchArms' (bi.viaNames σ) fuel v arms) := by
  induction arms with
  | nil => simp only [List.map_nil, denoteMatchArms']; exact ErrEq.refl _
  | cons pa rest iha =>
    obtain ⟨p, e⟩ := pa
    have he := ih (p, e) List.mem_cons_self fuel
    have hr := iha (fun b hb => ih b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons, denoteMatchArms']
    refine ErrEq.bindU _ fun env => ?_
    split
    · exact ErrEq.bindU _ fun _ => he
    · exact hr

/-- **Renaming the call heads.** Renaming every call head of `e` by `σ` and reading the
    result with `bi` agrees, up to the text of an error, with reading `e` with the table
    `bi.viaNames σ`, for every fuel. -/
theorem denote'_renameCalls (e : ImpExpr) : ∀ fuel,
    ErrEq (denote' bi fuel (renameCalls σ e)) (denote' (bi.viaNames σ) fuel e) := by
  induction e using ImpExpr.ind with
  | app f args ih =>
    intro fuel
    simp only [renameCalls, renameCalls.mapExpr_eq, denote']
    unfold denoteApp'
    rw [denoteArgs'_renameCalls bi σ args ih fuel]
    refine ErrEq.bindU _ fun mv => ?_
    simp only [Builtins.viaNames]
    split
    · split <;> first | exact ErrEq.refl _ | exact ErrEq.pure_err _ _
    · exact ErrEq.refl _
  | tuple es ih =>
    intro fuel
    simp only [renameCalls, renameCalls.mapExpr_eq, denote',
      denoteArgs'_renameCalls bi σ es ih fuel]
    exact ErrEq.refl _
  | match_ scrut arms ihs iha =>
    intro fuel
    have ha := denoteMatchArms'_renameCalls bi σ arms iha fuel
    simp only [renameCalls, renameCalls.mapArms_eq, denote']
    errEq_step
  | forLoop v lo hi body ihl ihh ihb =>
    intro fuel
    have := forLoopOrig'_errEq (v := v) ihb fuel
    simp only [renameCalls, denote']
    errEq_step
  | forLoopRev v lo hi body ihl ihh ihb =>
    intro fuel
    have := forLoopRevOrig'_errEq (v := v) ihb fuel
    simp only [renameCalls, denote']
    errEq_step
  | whileLoop c body ihc ihb =>
    intro fuel
    simp only [renameCalls, denote']
    exact whileOrig'_errEq ihc ihb fuel
  | forFold v lo hi body ihl ihh ihb =>
    intro fuel
    have := forLoop'_errEq (v := v) ihb fuel
    simp only [renameCalls, denote']
    errEq_step
  | forFoldRev v lo hi body ihl ihh ihb =>
    intro fuel
    have := forLoopRev'_errEq (v := v) ihb fuel
    simp only [renameCalls, denote']
    errEq_step
  | whileFold c body ihc ihb =>
    intro fuel
    simp only [renameCalls, denote']
    exact while'_errEq ihc ihb fuel
  | forFoldReturn v lo hi body ihl ihh ihb =>
    intro fuel
    have := forLoop'Return_errEq (v := v) ihb fuel
    simp only [renameCalls, denote']
    errEq_step
  | forFoldRevReturn v lo hi body ihl ihh ihb =>
    intro fuel
    have := forLoopRev'Return_errEq (v := v) ihb fuel
    simp only [renameCalls, denote']
    errEq_step
  | whileFoldReturn c body ihc ihb =>
    intro fuel
    simp only [renameCalls, denote']
    exact while'Return_errEq ihc ihb fuel
  | _ => intro fuel; simp only [renameCalls, denote']; errEq_step

end Rename

/-! ## The monomorphisation table -/

/-- The implementation of the trait method `method` at the instance type `inst`: the
    function `impl`, called by name. -/
structure MethodImpl where
  method : String
  inst : String
  impl : String
  deriving Repr, BEq

/-- A monomorphisation table: the implementations of trait methods at instance types. -/
abbrev MonoTable := List MethodImpl

/-- The implementing function of the name `f` at the instances `insts`: the first
    entry of `tbl` for the method `f` at a type in `insts`, and `f` itself when there
    is none. -/
def MonoTable.resolve (tbl : MonoTable) (insts : List String) (f : String) : String :=
  match tbl.find? (fun m => m.method == f && insts.contains m.inst) with
  | some m => m.impl
  | none => f

/-- The builtin table `bi` extended by the method table of the instances `insts`: a
    method of an instance answers as its implementing function in `bi`, and every other
    name as in `bi`. -/
def withInstances (bi : Builtins) (tbl : MonoTable) (insts : List String) : Builtins :=
  bi.viaNames (tbl.resolve insts)

/-- Specialise a generic function body at the instances `insts`: every call of a
    method of an instance becomes a call of its implementing function. -/
def monomorphise (tbl : MonoTable) (insts : List String) : ImpExpr → ImpExpr :=
  renameCalls (tbl.resolve insts)

/-- **Monomorphisation.** The specialised body read with the builtins `bi` agrees, up to
    the text of an error, with the generic body read with `bi` extended by the method
    table of the instances. -/
theorem denote'_monomorphise (bi : Builtins) (tbl : MonoTable) (insts : List String)
    (e : ImpExpr) (fuel : Nat) :
    ErrEq (denote' bi fuel (monomorphise tbl insts e))
      (denote' (withInstances bi tbl insts) fuel e) :=
  denote'_renameCalls bi (tbl.resolve insts) e fuel

/-- Every run of the generic body under the extended table that does not end in an
    error is the run of the specialised body under `bi`. -/
theorem denote'_monomorphise_run (bi : Builtins) (tbl : MonoTable) (insts : List String)
    (e : ImpExpr) (fuel : Nat) {env env' : Env} {o : Outcome}
    (hr : (denote' (withInstances bi tbl insts) fuel e).run env = (o, env'))
    (ho : ∀ a, o ≠ .err a) :
    (denote' bi fuel (monomorphise tbl insts e)).run env = (o, env') :=
  (denote'_monomorphise bi tbl insts e fuel).run_eq hr ho

/-! ## The single-name renaming -/

theorem rewriteAppName_eq_renameCalls (old new : String) (e : ImpExpr) :
    rewriteAppName old new e = renameCalls (fun f => if f == old then new else f) e := by
  induction e using ImpExpr.ind with
  | app f args ih =>
    simp only [rewriteAppName, renameCalls, rewriteAppName.mapExpr_eq,
      renameCalls.mapExpr_eq, ImpExpr.app.injEq, true_and]
    exact List.map_congr_left ih
  | tuple es ih =>
    simp only [rewriteAppName, renameCalls, rewriteAppName.mapExpr_eq,
      renameCalls.mapExpr_eq, ImpExpr.tuple.injEq]
    exact List.map_congr_left ih
  | match_ scrut arms ihs iha =>
    simp only [rewriteAppName, renameCalls, rewriteAppName.mapArms_eq,
      renameCalls.mapArms_eq, ImpExpr.match_.injEq, ihs, true_and]
    exact List.map_congr_left fun pa h => by rw [iha pa h]
  | _ => simp_all [rewriteAppName, renameCalls]

/-- `rewriteAppName old new` preserves `denote'` up to the text of an error when `old`
    and `new` are the same builtin. -/
theorem denote'_rewriteAppName (bi : Builtins) (old new : String) (h : bi new = bi old)
    (e : ImpExpr) (fuel : Nat) :
    ErrEq (denote' bi fuel (rewriteAppName old new e)) (denote' bi fuel e) := by
  have hbi : bi.viaNames (fun f => if f == old then new else f) = bi := by
    funext f args
    simp only [Builtins.viaNames]
    split <;> simp_all
  have := denote'_renameCalls bi (fun f => if f == old then new else f) e fuel
  rwa [← rewriteAppName_eq_renameCalls, hbi] at this

end Hax.Monomorphise
