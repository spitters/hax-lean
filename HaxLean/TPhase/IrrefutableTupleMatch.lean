/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.TExpr
public import HaxLean.AnfLowCT
public import HaxLean.Phase.InlineLocalClosures

/-!
# Irrefutable tuple matches as `let` chains

A match on a tuple literal with one arm whose pattern is a flat tuple of variables and
wildcards,

    match_ (tuple [e₁, …, eₙ]) [(tuplePat [p₁, …, pₙ], b)],

is the chain that evaluates `e₁, …, eₙ` in order and binds each `eᵢ` whose pattern is
`varPat xᵢ` to `xᵢ` (`letBind xᵢ eᵢ`) and runs each `eᵢ` whose pattern is a wildcard for
its effect (`seq eᵢ`), followed by `b` (`letChain`). The match binds its variables after
evaluating every element, the chain binds each one as soon as its element is evaluated;
the two agree when no element reads or binds a variable bound before it in the chain
(`chainFresh`). The phase rewrites a site only under that check and leaves it unchanged
otherwise.

`irrefutableTupleMatch` applies the rewrite bottom-up at every node (`bottomUp`);
`tIrrefutableTupleMatch` is the typed phase, whose chain nodes carry the type of the
match.

## Main results

* `denote'_letChain`: the chain refines the match under `denote'`: every run of the
  match that does not end in an error is the run of the chain, with the same final
  environment.
* `denote'_rewriteSite`: the rewrite of one node refines the node under `denote'`.
* `tIrrefutableTupleMatch_erase`: the typed phase commutes with erasure.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax

namespace IrrefutableTupleMatch

open InlineLocalClosures

/-! ## The rewrite of one node -/

/-- The binders of a flat tuple pattern: `some x` for `varPat x`, `none` for a wildcard;
    `none` for a pattern list with any other subpattern. -/
def flatBinders : List ImpPat → Option (List (Option String))
  | [] => some []
  | .varPat x :: ps => (flatBinders ps).map (some x :: ·)
  | .wildcard :: ps => (flatBinders ps).map (none :: ·)
  | _ :: _ => none

/-- `e` reads no variable of `acc`, binds none of them, and contains no `match_`. -/
def avoids (acc : List String) (e : ImpExpr) : Bool :=
  frameOk (fun y => !acc.contains y) (fun y => !acc.contains y) (fun _ => true) e

/-- Every element avoids the variables the chain binds before it, `acc` being the
    variables bound before the first one. -/
def chainFresh (acc : List String) : List (Option String) → List ImpExpr → Bool
  | some x :: xs, e :: es => avoids acc e && chainFresh (acc ++ [x]) xs es
  | none :: xs, e :: es => avoids acc e && chainFresh acc xs es
  | _, _ => true

/-- The chain binding the elements to the binders in order, followed by `b`. -/
def letChain : List (Option String) → List ImpExpr → ImpExpr → ImpExpr
  | some x :: xs, e :: es, b => .letBind x e (letChain xs es b)
  | none :: xs, e :: es, b => .seq e (letChain xs es b)
  | _, _, b => b

/-- The elements of a tuple literal. -/
def tupleElems? : ImpExpr → Option (List ImpExpr)
  | .tuple es => some es
  | _ => none

/-- A match on a tuple literal with a single arm whose pattern is a tuple pattern: the
    elements, the subpatterns and the arm body. -/
def siteOf? : ImpExpr → Option (List ImpExpr × List ImpPat × ImpExpr)
  | .match_ s [(p, b)] =>
    match tupleElems? s, p with
    | some es, .tuplePat ps => some (es, ps, b)
    | _, _ => none
  | _ => none

/-- The chain for the elements `es`, subpatterns `ps` and body `b` when the subpatterns
    are flat, as many as the elements, and the chain is fresh; `orig` otherwise. -/
def rewriteWith (es : List ImpExpr) (ps : List ImpPat) (b orig : ImpExpr) : ImpExpr :=
  match flatBinders ps with
  | some xs => if xs.length = es.length ∧ chainFresh [] xs es = true then letChain xs es b
      else orig
  | none => orig

/-- The rewrite of one node. -/
def rewriteSite (e : ImpExpr) : ImpExpr :=
  match siteOf? e with
  | some (es, ps, b) => rewriteWith es ps b e
  | none => e

/-! ## Bottom-up application -/

/-- Apply `f` at every node, children first. -/
def bottomUp (f : ImpExpr → ImpExpr) : ImpExpr → ImpExpr
  | .lit v => f (.lit v)
  | .var n => f (.var n)
  | .letBind n v b => f (.letBind n (bottomUp f v) (bottomUp f b))
  | .lam ps b => f (.lam ps (bottomUp f b))
  | .app g args => f (.app g (mapE f args))
  | .tuple es => f (.tuple (mapE f es))
  | .proj e i => f (.proj (bottomUp f e) i)
  | .ifThenElse c t e => f (.ifThenElse (bottomUp f c) (bottomUp f t) (bottomUp f e))
  | .match_ s arms => f (.match_ (bottomUp f s) (mapA f arms))
  | .unitVal => f .unitVal
  | .seq a b => f (.seq (bottomUp f a) (bottomUp f b))
  | .borrow e => f (.borrow (bottomUp f e))
  | .deref e => f (.deref (bottomUp f e))
  | .assign n r => f (.assign n (bottomUp f r))
  | .forLoop v lo hi b => f (.forLoop v (bottomUp f lo) (bottomUp f hi) (bottomUp f b))
  | .forLoopRev v lo hi b => f (.forLoopRev v (bottomUp f lo) (bottomUp f hi) (bottomUp f b))
  | .whileLoop c b => f (.whileLoop (bottomUp f c) (bottomUp f b))
  | .break_ none => f (.break_ none)
  | .break_ (some e) => f (.break_ (some (bottomUp f e)))
  | .continue_ => f .continue_
  | .earlyReturn e => f (.earlyReturn (bottomUp f e))
  | .questionMark e => f (.questionMark (bottomUp f e))
  | .forFold v lo hi b => f (.forFold v (bottomUp f lo) (bottomUp f hi) (bottomUp f b))
  | .forFoldRev v lo hi b => f (.forFoldRev v (bottomUp f lo) (bottomUp f hi) (bottomUp f b))
  | .whileFold c b => f (.whileFold (bottomUp f c) (bottomUp f b))
  | .forFoldReturn v lo hi b =>
    f (.forFoldReturn v (bottomUp f lo) (bottomUp f hi) (bottomUp f b))
  | .forFoldRevReturn v lo hi b =>
    f (.forFoldRevReturn v (bottomUp f lo) (bottomUp f hi) (bottomUp f b))
  | .whileFoldReturn c b => f (.whileFoldReturn (bottomUp f c) (bottomUp f b))
  | .cfBreak e => f (.cfBreak (bottomUp f e))
  | .cfContinue e => f (.cfContinue (bottomUp f e))
  | .cfBreakContinue e => f (.cfBreakContinue (bottomUp f e))
  | .typeAscription e s => f (.typeAscription (bottomUp f e) s)
where
  /-- `bottomUp` on every expression of a list. -/
  mapE (f : ImpExpr → ImpExpr) : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => bottomUp f e :: mapE f es
  /-- `bottomUp` on the body of every match arm. -/
  mapA (f : ImpExpr → ImpExpr) : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, bottomUp f e) :: mapA f rest

@[simp] theorem bottomUp.mapE_eq (f : ImpExpr → ImpExpr) (es : List ImpExpr) :
    bottomUp.mapE f es = es.map (bottomUp f) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [bottomUp.mapE, ih]

@[simp] theorem bottomUp.mapA_eq (f : ImpExpr → ImpExpr) (arms : List (ImpPat × ImpExpr)) :
    bottomUp.mapA f arms = arms.map fun (p, e) => (p, bottomUp f e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [bottomUp.mapA, ih]

end IrrefutableTupleMatch

open IrrefutableTupleMatch in
/-- Rewrite every irrefutable match on a tuple literal into its `let` chain. -/
def irrefutableTupleMatch (e : ImpExpr) : ImpExpr := bottomUp rewriteSite e

namespace IrrefutableTupleMatch

open InlineLocalClosures

/-! ## Environments extended by a list of bindings -/

/-- `env` extended by the bindings of `P` in order. -/
def applyExts (env : Env) (P : List (String × Value)) : Env :=
  P.foldl (fun e nv => e.extend nv.1 nv.2) env

theorem applyExts_append_single (env : Env) (P : List (String × Value)) (x : String)
    (v : Value) : applyExts env (P ++ [(x, v)]) = (applyExts env P).extend x v := by
  simp [applyExts, List.foldl_append]

theorem extend_comm (env : Env) {a b : String} (hab : a ≠ b) (v w : Value) :
    (env.extend a v).extend b w = (env.extend b w).extend a v := by
  funext z
  simp only [Env.extend, beq_iff_eq]
  by_cases hb : z = b
  · subst hb; simp [Ne.symm hab]
  · simp [hb]

theorem applyExts_read (P : List (String × Value)) :
    ∀ (env : Env) (y : String), (P.map Prod.fst).contains y = false →
      applyExts env P y = env y := by
  induction P with
  | nil => intro env y _; rfl
  | cons nv P ih =>
    intro env y hy
    obtain ⟨n, w⟩ := nv
    simp only [List.map_cons, List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
      ne_eq] at hy
    simp only [applyExts, List.foldl_cons] at ih ⊢
    rw [ih _ _ hy.2]
    exact ContinueFlag.extend_ne w hy.1

theorem applyExts_extend (P : List (String × Value)) :
    ∀ (env : Env) (n : String) (w : Value), (P.map Prod.fst).contains n = false →
      applyExts (env.extend n w) P = (applyExts env P).extend n w := by
  induction P with
  | nil => intro env n w _; rfl
  | cons mu P ih =>
    intro env n w hn
    obtain ⟨m, u⟩ := mu
    simp only [List.map_cons, List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
      ne_eq] at hn
    simp only [applyExts, List.foldl_cons] at ih ⊢
    rw [extend_comm env hn.1 w u]
    exact ih _ _ _ hn.2

/-- An expression that avoids the variables of `P` runs from an environment extended by
    `P` as from the environment itself, its final environment extended by `P`. -/
theorem denote'_applyExts (bi : Builtins) (fuel : Nat) (P : List (String × Value))
    (e : ImpExpr) (h : avoids (P.map Prod.fst) e = true) :
    RefE (fun e₁ e₂ => e₁ = applyExts e₂ P) (denote' bi fuel e) (denote' bi fuel e) := by
  have hid : renameReads id e = e :=
    renameReads_id e (frameOk_mono (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) e h)
  have := denote'_frame (R := fun e₁ e₂ => e₁ = applyExts e₂ P) (bi₁ := bi) (bi₂ := bi) id
    (fun y => !(P.map Prod.fst).contains y) (fun y => !(P.map Prod.fst).contains y)
    (fun _ => true)
    (fun e₁ e₂ x hR hx => by
      subst hR
      exact applyExts_read P e₂ x (by simpa using hx))
    (fun e₁ e₂ n w hR hn => by
      subst hR
      exact (applyExts_extend P e₂ n w (by simpa using hn)).symm)
    (fun _ _ => rfl) e h fuel
  rwa [hid] at this

/-! ## One-step runs -/

theorem denote'_tuple_run (bi : Builtins) (fuel : Nat) (es : List ImpExpr) (env : Env) :
    denote' bi fuel (.tuple es) env =
      match denoteArgs' bi fuel es env with
      | (some vals, s) => (.val (.tuple vals), s)
      | (none, s) => (.err "non-value in tuple elements", s) := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  generalize denoteArgs' bi fuel es env = p
  obtain ⟨r, s⟩ := p
  cases r <;> rfl

theorem denote'_match_run (bi : Builtins) (fuel : Nat) (sc : ImpExpr)
    (arms : List (ImpPat × ImpExpr)) (env : Env) :
    denote' bi fuel (.match_ sc arms) env =
      match denote' bi fuel sc env with
      | (.val (.controlFlow isBreak w), s) => (.val (.controlFlow isBreak w), s)
      | (.val w, s) => denoteMatchArms' bi fuel w arms s
      | (other, s) => (other, s) := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  generalize denote' bi fuel sc env = p
  obtain ⟨r, s⟩ := p
  cases r <;> try rfl
  rename_i w; cases w <;> rfl

theorem denoteMatchArms'_single_run (bi : Builtins) (fuel : Nat) (v : Value) (p : ImpPat)
    (b : ImpExpr) (env : Env) :
    denoteMatchArms' bi fuel v [(p, b)] env =
      match matchPat p v env with
      | some env' => denote' bi fuel b env'
      | none => (.err "no matching pattern", env) := by
  conv => lhs; unfold denoteMatchArms'
  dsimp only [bind, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set,
    MonadStateOf.set, StateT.set, pure, Pure.pure, StateT.pure, Id.run]
  cases matchPat p v env with
  | some env' => rfl
  | none => unfold denoteMatchArms'; rfl

theorem denoteArgs'_nil (bi : Builtins) (fuel : Nat) (env : Env) :
    denoteArgs' bi fuel [] env = (some [], env) := by
  unfold denoteArgs'; rfl

/-- A list of arguments evaluating to values: its head evaluates to a value that is not a
    control-flow value, and its tail to the remaining values. -/
theorem denoteArgs'_cons_some (bi : Builtins) (fuel : Nat) (e : ImpExpr) (es : List ImpExpr)
    (env s : Env) (vals : List Value)
    (h : denoteArgs' bi fuel (e :: es) env = (some vals, s)) :
    ∃ v s₀ vs, denote' bi fuel e env = (.val v, s₀) ∧ (∀ b w, v ≠ .controlFlow b w) ∧
      denoteArgs' bi fuel es s₀ = (some vs, s) ∧ vals = v :: vs := by
  unfold denoteArgs' at h
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run] at h
  revert h
  generalize hd : denote' bi fuel e env = p
  obtain ⟨r, s₀⟩ := p
  cases r with
  | val v =>
    cases v with
    | controlFlow b w => intro h; cases h
    | _ =>
      dsimp only [StateT.bind]
      generalize hq : denoteArgs' bi fuel es s₀ = q
      obtain ⟨r', s'⟩ := q
      cases r' with
      | none => intro h; cases h
      | some vs =>
        intro h
        injection h with h1 h2
        injection h1 with h1
        subst h1 h2
        exact ⟨_, s₀, vs, rfl, fun _ _ h' => (by cases h'), hq, rfl⟩
  | _ => intro h; cases h

theorem denoteArgs'_length (bi : Builtins) (fuel : Nat) :
    ∀ (es : List ImpExpr) (env s : Env) (vals : List Value),
      denoteArgs' bi fuel es env = (some vals, s) → vals.length = es.length := by
  intro es
  induction es with
  | nil =>
    intro env s vals h
    rw [denoteArgs'_nil] at h
    cases h; rfl
  | cons e es ih =>
    intro env s vals h
    obtain ⟨v, s₀, vs, -, -, hes, rfl⟩ := denoteArgs'_cons_some bi fuel e es env s vals h
    simp [ih s₀ s vs hes]

/-! ## The chain refines the match -/

/-- The bindings the binders `xs` make for the values `vals`. -/
def binds : List (Option String) → List Value → List (String × Value)
  | some x :: xs, v :: vs => (x, v) :: binds xs vs
  | none :: xs, _ :: vs => binds xs vs
  | _, _ => []

theorem matchPatList_flat :
    ∀ (ps : List ImpPat) (xs : List (Option String)) (vs : List Value) (env : Env),
      flatBinders ps = some xs → xs.length = vs.length →
        matchPat.matchPatList ps vs env = some (applyExts env (binds xs vs)) := by
  intro ps
  induction ps with
  | nil =>
    intro xs vs env hx hl
    simp only [flatBinders, Option.some.injEq] at hx
    subst hx
    cases vs with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons p ps ih =>
    intro xs vs env hx hl
    cases p with
    | varPat x =>
      simp only [flatBinders, Option.map_eq_some_iff] at hx
      obtain ⟨xs', hx', rfl⟩ := hx
      cases vs with
      | nil => simp at hl
      | cons v vs =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
        simp only [matchPat.matchPatList, matchPat, Option.bind_eq_bind, Option.bind_some]
        rw [ih xs' vs _ hx' hl]
        rfl
    | wildcard =>
      simp only [flatBinders, Option.map_eq_some_iff] at hx
      obtain ⟨xs', hx', rfl⟩ := hx
      cases vs with
      | nil => simp at hl
      | cons v vs =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
        simp only [matchPat.matchPatList, matchPat, Option.bind_eq_bind, Option.bind_some]
        rw [ih xs' vs _ hx' hl]
        rfl
    | _ => simp [flatBinders] at hx

theorem flatBinders_length :
    ∀ (ps : List ImpPat) (xs : List (Option String)), flatBinders ps = some xs →
      xs.length = ps.length := by
  intro ps
  induction ps with
  | nil => intro xs hx; simp only [flatBinders, Option.some.injEq] at hx; subst hx; rfl
  | cons p ps ih =>
    intro xs hx
    cases p with
    | varPat x =>
      simp only [flatBinders, Option.map_eq_some_iff] at hx
      obtain ⟨xs', hx', rfl⟩ := hx
      simp [ih xs' hx']
    | wildcard =>
      simp only [flatBinders, Option.map_eq_some_iff] at hx
      obtain ⟨xs', hx', rfl⟩ := hx
      simp [ih xs' hx']
    | _ => simp [flatBinders] at hx

/-- The chain run from an environment extended by pending bindings `P` (whose variables
    are `acc`) is the run of `b` from the environment the elements leave, extended by `P`
    and then by the bindings of the chain. -/
theorem letChain_run (bi : Builtins) (fuel : Nat) (b : ImpExpr) :
    ∀ (xs : List (Option String)) (es : List ImpExpr) (acc : List String)
      (P : List (String × Value)), P.map Prod.fst = acc → xs.length = es.length →
      chainFresh acc xs es = true → ∀ (env s : Env) (vals : List Value),
      denoteArgs' bi fuel es env = (some vals, s) →
      denote' bi fuel (letChain xs es b) (applyExts env P) =
        denote' bi fuel b (applyExts s (P ++ binds xs vals)) := by
  intro xs
  induction xs with
  | nil =>
    intro es acc P _ hl _ env s vals h
    cases es with
    | nil =>
      rw [denoteArgs'_nil] at h
      cases h
      simp [letChain, binds]
    | cons _ _ => simp at hl
  | cons xo xs ih =>
    intro es acc P hP hl hf env s vals h
    cases es with
    | nil => simp at hl
    | cons e es =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      obtain ⟨v, s₀, vs, he, hcf, hes, rfl⟩ := denoteArgs'_cons_some bi fuel e es env s vals h
      cases xo with
      | some x =>
        simp only [chainFresh, Bool.and_eq_true] at hf
        obtain ⟨s₁, hs₁, hR⟩ := denote'_applyExts bi fuel P e (by rw [hP]; exact hf.1)
          (applyExts env P) env rfl (.val v) s₀ he (fun ⟨_, h'⟩ => by cases h')
        subst hR
        simp only [letChain, binds]
        rw [denote'_letBind_run]
        rw [show denote' bi fuel e (applyExts env P) = (.val v, applyExts s₀ P) from hs₁]
        have hstep : denote' bi fuel (letChain xs es b) ((applyExts s₀ P).extend x v) =
            denote' bi fuel b (applyExts s ((P ++ [(x, v)]) ++ binds xs vs)) := by
          rw [← applyExts_append_single]
          exact ih es (acc ++ [x]) (P ++ [(x, v)]) (by simp [hP]) hl hf.2 s₀ s vs hes
        cases v with
        | controlFlow b w => exact absurd rfl (hcf b w)
        | _ => simpa using hstep
      | none =>
        simp only [chainFresh, Bool.and_eq_true] at hf
        obtain ⟨s₁, hs₁, hR⟩ := denote'_applyExts bi fuel P e (by rw [hP]; exact hf.1)
          (applyExts env P) env rfl (.val v) s₀ he (fun ⟨_, h'⟩ => by cases h')
        subst hR
        simp only [letChain, binds]
        rw [denote'_seq_run]
        rw [show denote' bi fuel e (applyExts env P) = (.val v, applyExts s₀ P) from hs₁]
        have hstep := ih es acc P hP hl hf.2 s₀ s vs hes
        cases v with
        | controlFlow b w => exact absurd rfl (hcf b w)
        | _ => exact hstep

/-- **The chain refines the match.** For a flat tuple pattern with as many binders as
    elements and a fresh chain, every run of the match on the tuple literal that does not
    end in an error is the run of the chain, with the same final environment. -/
theorem denote'_letChain (bi : Builtins) (fuel : Nat) (es : List ImpExpr) (ps : List ImpPat)
    (b : ImpExpr) (xs : List (Option String)) (hx : flatBinders ps = some xs)
    (hl : xs.length = es.length) (hf : chainFresh [] xs es = true) :
    RefE (fun e₁ e₂ => e₁ = e₂) (denote' bi fuel (letChain xs es b))
      (denote' bi fuel (.match_ (.tuple es) [(.tuplePat ps, b)])) := by
  intro e₁ e₂ h o s₂ hr hnb
  subst h
  change denote' bi fuel (.match_ (.tuple es) [(.tuplePat ps, b)]) e₁ = (o, s₂) at hr
  rw [denote'_match_run, denote'_tuple_run] at hr
  revert hr
  generalize hd : denoteArgs' bi fuel es e₁ = q
  obtain ⟨r, s⟩ := q
  cases r with
  | none => intro hr; cases hr; exact absurd ⟨_, rfl⟩ hnb
  | some vals =>
    intro hr
    dsimp only at hr
    rw [denoteMatchArms'_single_run] at hr
    have hvl := denoteArgs'_length bi fuel es e₁ s vals hd
    have hpl := flatBinders_length ps xs hx
    have hm : matchPat (.tuplePat ps) (.tuple vals) s = some (applyExts s (binds xs vals)) := by
      simp only [matchPat]
      rw [if_neg (by simp [← hpl, hl, hvl])]
      exact matchPatList_flat ps xs vals s hx (by rw [hl, hvl])
    rw [hm] at hr
    refine ⟨s₂, ?_, rfl⟩
    change denote' bi fuel (letChain xs es b) e₁ = (o, s₂)
    have := letChain_run bi fuel b xs es [] [] rfl hl hf e₁ s vals hd
    simp only [List.nil_append] at this
    exact this.trans hr

theorem siteOf?_eq_some {e : ImpExpr} {es : List ImpExpr} {ps : List ImpPat} {b : ImpExpr}
    (h : siteOf? e = some (es, ps, b)) : e = .match_ (.tuple es) [(.tuplePat ps, b)] := by
  unfold siteOf? at h
  split at h
  · rename_i s p b'
    split at h
    · rename_i es' ps' hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      cases s <;> simp_all [tupleElems?]
    · cases h
  · cases h

/-- The rewrite of one node refines the node under `denote'`. -/
theorem denote'_rewriteSite (bi : Builtins) (fuel : Nat) (e : ImpExpr) :
    RefE (fun e₁ e₂ => e₁ = e₂) (denote' bi fuel (rewriteSite e)) (denote' bi fuel e) := by
  unfold rewriteSite
  split
  · rename_i es ps b h
    have he := siteOf?_eq_some h
    unfold rewriteWith
    split
    · rename_i xs hx
      split
      · rename_i hc
        rw [he]
        exact denote'_letChain bi fuel es ps b xs hx hc.1 hc.2
      · exact RefR.refl _
    · exact RefR.refl _
  · exact RefR.refl _

/-! ## The typed phase -/

/-- The elements of a tuple literal under any number of `ann` markers. -/
def tTupleElems? : TExpr → Option (List TExpr)
  | .mk (.tuple es) _ => some es
  | .mk (.ann e) _ => tTupleElems? e
  | _ => none

theorem tTupleElems?_erase (s : TExpr) :
    (tTupleElems? s).map (List.map TExpr.erase) = tupleElems? s.erase := by
  induction s using TExpr.ind <;> simp_all [tTupleElems?, tupleElems?, TExpr.erase]

/-- Typed `siteOf?`. -/
def tSiteOf? : TExpr → Option (List TExpr × List ImpPat × TExpr)
  | .mk (.match_ s [(p, b)]) _ =>
    match tTupleElems? s, p with
    | some es, .tuplePat ps => some (es, ps, b)
    | _, _ => none
  | _ => none

/-- Typed `letChain`: every node of the chain has type `ty`. -/
def tLetChain (ty : ImpType) : List (Option String) → List TExpr → TExpr → TExpr
  | some x :: xs, e :: es, b => .mk (.letBind x e (tLetChain ty xs es b)) ty
  | none :: xs, e :: es, b => .mk (.seq e (tLetChain ty xs es b)) ty
  | _, _, b => b

theorem tLetChain_erase (ty : ImpType) :
    ∀ (xs : List (Option String)) (es : List TExpr) (b : TExpr),
      (tLetChain ty xs es b).erase = letChain xs (es.map TExpr.erase) b.erase := by
  intro xs
  induction xs with
  | nil => intro es b; cases es <;> rfl
  | cons xo xs ih =>
    intro es b
    cases es with
    | nil => cases xo <;> rfl
    | cons e es => cases xo <;> simp [tLetChain, letChain, TExpr.erase, ih]

/-- Typed `rewriteSite`. -/
def tRewriteSite (t : TExpr) : TExpr :=
  match tSiteOf? t with
  | some (es, ps, b) =>
    match flatBinders ps with
    | some xs =>
      if xs.length = es.length ∧ chainFresh [] xs (es.map TExpr.erase) = true then
        tLetChain t.ty xs es b
      else t
    | none => t
  | none => t

theorem tSiteOf?_erase (k : TExprKind) (ty : ImpType) (hk : ∀ e, k ≠ .ann e) :
    (tSiteOf? (.mk k ty)).map (fun (es, ps, b) => (es.map TExpr.erase, ps, b.erase))
      = siteOf? (TExpr.mk k ty).erase := by
  cases k with
  | match_ s arms =>
    rcases arms with _ | ⟨⟨p, b⟩, _ | ⟨pb, rest⟩⟩
    · simp [tSiteOf?, siteOf?, TExpr.erase]
    · simp only [tSiteOf?, siteOf?, TExpr.erase, TExpr.eraseArms_eq, List.map_cons,
        List.map_nil]
      rw [← tTupleElems?_erase]
      cases tTupleElems? s <;> cases p <;> simp
    · simp [tSiteOf?, siteOf?, TExpr.erase]
  | ann e => exact absurd rfl (hk e)
  | break_ eo => cases eo <;> simp [tSiteOf?, siteOf?, TExpr.erase]
  | _ => simp [tSiteOf?, siteOf?, TExpr.erase]

theorem tRewriteSite_erase (k : TExprKind) (ty : ImpType) (hk : ∀ e, k ≠ .ann e) :
    (tRewriteSite (.mk k ty)).erase = rewriteSite (TExpr.mk k ty).erase := by
  have hs := tSiteOf?_erase k ty hk
  unfold tRewriteSite rewriteSite
  revert hs
  cases tSiteOf? (.mk k ty) with
  | none => intro hs; rw [← hs]; rfl
  | some site =>
    obtain ⟨es, ps, b⟩ := site
    intro hs
    rw [← hs]
    simp only [Option.map_some, rewriteWith]
    cases flatBinders ps with
    | none => rfl
    | some xs =>
      simp only [List.length_map]
      split
      · rw [tLetChain_erase]
      · rfl

/-- Typed `bottomUp`: apply `g` at every node except an `ann` marker, children first. -/
def tBottomUp (g : TExpr → TExpr) : TExpr → TExpr
  | .mk (.lit v) ty => g (.mk (.lit v) ty)
  | .mk (.var n) ty => g (.mk (.var n) ty)
  | .mk (.letBind n v b) ty => g (.mk (.letBind n (tBottomUp g v) (tBottomUp g b)) ty)
  | .mk (.lam ps b) ty => g (.mk (.lam ps (tBottomUp g b)) ty)
  | .mk (.app f args) ty => g (.mk (.app f (mapE g args)) ty)
  | .mk (.tuple es) ty => g (.mk (.tuple (mapE g es)) ty)
  | .mk (.proj e i) ty => g (.mk (.proj (tBottomUp g e) i) ty)
  | .mk (.ifThenElse c t e) ty =>
    g (.mk (.ifThenElse (tBottomUp g c) (tBottomUp g t) (tBottomUp g e)) ty)
  | .mk (.match_ s arms) ty => g (.mk (.match_ (tBottomUp g s) (mapA g arms)) ty)
  | .mk .unitVal ty => g (.mk .unitVal ty)
  | .mk (.seq a b) ty => g (.mk (.seq (tBottomUp g a) (tBottomUp g b)) ty)
  | .mk (.borrow e) ty => g (.mk (.borrow (tBottomUp g e)) ty)
  | .mk (.deref e) ty => g (.mk (.deref (tBottomUp g e)) ty)
  | .mk (.assign n r) ty => g (.mk (.assign n (tBottomUp g r)) ty)
  | .mk (.forLoop v lo hi b) ty =>
    g (.mk (.forLoop v (tBottomUp g lo) (tBottomUp g hi) (tBottomUp g b)) ty)
  | .mk (.forLoopRev v lo hi b) ty =>
    g (.mk (.forLoopRev v (tBottomUp g lo) (tBottomUp g hi) (tBottomUp g b)) ty)
  | .mk (.whileLoop c b) ty => g (.mk (.whileLoop (tBottomUp g c) (tBottomUp g b)) ty)
  | .mk (.break_ none) ty => g (.mk (.break_ none) ty)
  | .mk (.break_ (some e)) ty => g (.mk (.break_ (some (tBottomUp g e))) ty)
  | .mk .continue_ ty => g (.mk .continue_ ty)
  | .mk (.earlyReturn e) ty => g (.mk (.earlyReturn (tBottomUp g e)) ty)
  | .mk (.questionMark e) ty => g (.mk (.questionMark (tBottomUp g e)) ty)
  | .mk (.forFold v lo hi b) ty =>
    g (.mk (.forFold v (tBottomUp g lo) (tBottomUp g hi) (tBottomUp g b)) ty)
  | .mk (.forFoldRev v lo hi b) ty =>
    g (.mk (.forFoldRev v (tBottomUp g lo) (tBottomUp g hi) (tBottomUp g b)) ty)
  | .mk (.whileFold c b) ty => g (.mk (.whileFold (tBottomUp g c) (tBottomUp g b)) ty)
  | .mk (.forFoldReturn v lo hi b) ty =>
    g (.mk (.forFoldReturn v (tBottomUp g lo) (tBottomUp g hi) (tBottomUp g b)) ty)
  | .mk (.forFoldRevReturn v lo hi b) ty =>
    g (.mk (.forFoldRevReturn v (tBottomUp g lo) (tBottomUp g hi) (tBottomUp g b)) ty)
  | .mk (.whileFoldReturn c b) ty =>
    g (.mk (.whileFoldReturn (tBottomUp g c) (tBottomUp g b)) ty)
  | .mk (.cfBreak e) ty => g (.mk (.cfBreak (tBottomUp g e)) ty)
  | .mk (.cfContinue e) ty => g (.mk (.cfContinue (tBottomUp g e)) ty)
  | .mk (.cfBreakContinue e) ty => g (.mk (.cfBreakContinue (tBottomUp g e)) ty)
  | .mk (.ann e) ty => .mk (.ann (tBottomUp g e)) ty
  | .mk (.namedProj n e) ty => g (.mk (.namedProj n (tBottomUp g e)) ty)
where
  /-- `tBottomUp` on every expression of a list. -/
  mapE (g : TExpr → TExpr) : List TExpr → List TExpr
    | [] => []
    | e :: es => tBottomUp g e :: mapE g es
  /-- `tBottomUp` on the body of every match arm. -/
  mapA (g : TExpr → TExpr) : List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest => (p, tBottomUp g e) :: mapA g rest

@[simp] theorem tBottomUp.mapE_eq (g : TExpr → TExpr) (es : List TExpr) :
    tBottomUp.mapE g es = es.map (tBottomUp g) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [tBottomUp.mapE, ih]

@[simp] theorem tBottomUp.mapA_eq (g : TExpr → TExpr) (arms : List (ImpPat × TExpr)) :
    tBottomUp.mapA g arms = arms.map fun (p, e) => (p, tBottomUp g e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [tBottomUp.mapA, ih]

/-- `tBottomUp g` commutes with erasure when `g` does at every node that is not an `ann`
    marker. -/
theorem tBottomUp_erase (g : TExpr → TExpr) (f : ImpExpr → ImpExpr)
    (hg : ∀ k ty, (∀ e, k ≠ .ann e) → (g (.mk k ty)).erase = f (TExpr.mk k ty).erase)
    (t : TExpr) : (tBottomUp g t).erase = bottomUp f t.erase := by
  induction t using TExpr.ind with
  | ann _ _ ih => simp [tBottomUp, TExpr.erase, ih]
  | app _ _ args ih =>
    rw [tBottomUp, hg _ _ (by simp)]
    simp only [TExpr.erase, TExpr.eraseList_eq, tBottomUp.mapE_eq, List.map_map,
      bottomUp, bottomUp.mapE_eq]
    congr 2
    exact List.map_congr_left fun a ha => ih a ha
  | tuple _ elems ih =>
    rw [tBottomUp, hg _ _ (by simp)]
    simp only [TExpr.erase, TExpr.eraseList_eq, tBottomUp.mapE_eq, List.map_map,
      bottomUp, bottomUp.mapE_eq]
    congr 2
    exact List.map_congr_left fun a ha => ih a ha
  | match_ _ _ arms ih1 ih2 =>
    rw [tBottomUp, hg _ _ (by simp)]
    simp only [TExpr.erase, TExpr.eraseArms_eq, tBottomUp.mapA_eq, List.map_map,
      bottomUp, bottomUp.mapA_eq, ih1]
    congr 2
    exact List.map_congr_left fun pa hpa => by simp [ih2 pa hpa]
  | _ => simp_all [tBottomUp, TExpr.erase, bottomUp]

end IrrefutableTupleMatch

open IrrefutableTupleMatch in
/-- Typed `irrefutableTupleMatch`. -/
def tIrrefutableTupleMatch (t : TExpr) : TExpr := tBottomUp tRewriteSite t

open IrrefutableTupleMatch in
/-- The typed phase commutes with erasure. -/
theorem tIrrefutableTupleMatch_erase (t : TExpr) :
    (tIrrefutableTupleMatch t).erase = irrefutableTupleMatch t.erase :=
  tBottomUp_erase tRewriteSite rewriteSite (fun k ty hk => tRewriteSite_erase k ty hk) t

end Hax
