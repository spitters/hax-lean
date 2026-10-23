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
* `denote'_bottomUp`: a rewrite of one node that refines the node, the final
  environments related by a reflexive, transitive relation kept by `extend`, gives a
  `bottomUp` traversal that refines every term whose reads that relation admits
  (`readsOk`).
* `irrefutableTupleMatch_refines`: the whole pass refines its input under `denote'`.
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
      rw [ite_eq_right (by simp [← hpl, hl, hvl])]
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

namespace IrrefutableTupleMatch

open InlineLocalClosures

/-! ## Refinement through `bottomUp` -/

/-- A variable read or the projection of one: an expression that leaves the environment
    unchanged and that `bottomUp` keeps when the rewrite keeps such nodes. -/
def simpleRead : ImpExpr → Bool
  | .var _ => true
  | .proj (.var _) _ => true
  | _ => false

/-- The reads of `e` are admissible in mode `s`. In mode `true` every variable may be
    read, in mode `false` only those with `rd`. The value of a `letBind` and the operand
    of a `proj` are read in the mode of the node; the body of `letBind n v b` is read in
    mode `true` when `up n` holds or when the node is in mode `true` and `v` is a
    `simpleRead`, and in mode `false` otherwise; every other child is read in mode
    `false`. -/
def readsOk (rd up : String → Bool) : Bool → ImpExpr → Bool
  | s, .var x => s || rd x
  | s, .letBind n v b =>
    readsOk rd up s v && readsOk rd up (up n || (s && simpleRead v)) b
  | _, .lam _ b => readsOk rd up false b
  | _, .app _ args => readsList rd up args
  | _, .tuple es => readsList rd up es
  | s, .proj e _ => readsOk rd up s e
  | _, .ifThenElse c t e =>
    readsOk rd up false c && readsOk rd up false t && readsOk rd up false e
  | _, .match_ sc arms => readsOk rd up false sc && readsArms rd up arms
  | _, .seq a b => readsOk rd up false a && readsOk rd up false b
  | _, .borrow e => readsOk rd up false e
  | _, .deref e => readsOk rd up false e
  | _, .assign _ r => readsOk rd up false r
  | _, .forLoop _ lo hi b =>
    readsOk rd up false lo && readsOk rd up false hi && readsOk rd up false b
  | _, .forLoopRev _ lo hi b =>
    readsOk rd up false lo && readsOk rd up false hi && readsOk rd up false b
  | _, .whileLoop c b => readsOk rd up false c && readsOk rd up false b
  | _, .break_ (some e) => readsOk rd up false e
  | _, .earlyReturn e => readsOk rd up false e
  | _, .questionMark e => readsOk rd up false e
  | _, .forFold _ lo hi b =>
    readsOk rd up false lo && readsOk rd up false hi && readsOk rd up false b
  | _, .forFoldRev _ lo hi b =>
    readsOk rd up false lo && readsOk rd up false hi && readsOk rd up false b
  | _, .whileFold c b => readsOk rd up false c && readsOk rd up false b
  | _, .forFoldReturn _ lo hi b =>
    readsOk rd up false lo && readsOk rd up false hi && readsOk rd up false b
  | _, .forFoldRevReturn _ lo hi b =>
    readsOk rd up false lo && readsOk rd up false hi && readsOk rd up false b
  | _, .whileFoldReturn c b => readsOk rd up false c && readsOk rd up false b
  | _, .cfBreak e => readsOk rd up false e
  | _, .cfContinue e => readsOk rd up false e
  | _, .cfBreakContinue e => readsOk rd up false e
  | _, .typeAscription e _ => readsOk rd up false e
  | _, _ => true
where
  /-- `readsOk` in mode `false` of every expression of a list. -/
  readsList (rd up : String → Bool) : List ImpExpr → Bool
    | [] => true
    | e :: es => readsOk rd up false e && readsList rd up es
  /-- `readsOk` in mode `false` of the body of every match arm. -/
  readsArms (rd up : String → Bool) : List (ImpPat × ImpExpr) → Bool
    | [] => true
    | (_, e) :: rest => readsOk rd up false e && readsArms rd up rest

theorem readsOk.readsList_eq (rd up : String → Bool) (es : List ImpExpr) :
    readsOk.readsList rd up es = es.all (readsOk rd up false) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [readsOk.readsList, ih]

theorem readsOk.readsArms_eq (rd up : String → Bool) (arms : List (ImpPat × ImpExpr)) :
    readsOk.readsArms rd up arms = arms.all fun pa => readsOk rd up false pa.2 := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [readsOk.readsArms, ih]

/-- Every read is admissible when every variable may be read in mode `false`. -/
theorem readsOk_of_rd {rd : String → Bool} (up : String → Bool) (hrd : ∀ x, rd x = true)
    (e : ImpExpr) : ∀ s, readsOk rd up s e = true := by
  induction e using ImpExpr.ind with
  | app g args ih =>
    intro s
    simp only [readsOk, readsOk.readsList_eq, List.all_eq_true]
    exact fun a ha => ih a ha false
  | tuple es ih =>
    intro s
    simp only [readsOk, readsOk.readsList_eq, List.all_eq_true]
    exact fun a ha => ih a ha false
  | match_ sc arms ihs iha =>
    intro s
    simp only [readsOk, readsOk.readsArms_eq, List.all_eq_true, Bool.and_eq_true]
    exact ⟨ihs false, fun pa ha => iha pa ha false⟩
  | letBind n v b ihv ihb =>
    intro s
    simp only [readsOk, Bool.and_eq_true]
    exact ⟨ihv s, ihb _⟩
  | proj e i ih => intro s; exact ih s
  | _ => intro s; simp_all [readsOk]

/-- The relation of a mode: equality in mode `true`, `R` in mode `false`. -/
def modeRel (R : Env → Env → Prop) : Bool → Env → Env → Prop
  | true => fun e₁ e₂ => e₁ = e₂
  | false => R

/-- A run related to `m` from equal environments, `m` related to `src` from `P`-related
    ones, the final relation transitive: the run is related to `src`. -/
theorem refR_site {α : Type} {P R : Env → Env → Prop} {bad : α → Prop}
    (hR : ∀ a b c, R a b → R b c → R a c) {t m src : StateM Env α}
    (hf : RefR (fun e₁ e₂ => e₁ = e₂) R bad t m) (hc : RefR P R bad m src) :
    RefR P R bad t src := by
  intro e₁ e₂ hP o s₂ hr hb
  obtain ⟨sm, hm, hR₁⟩ := hc e₁ e₂ hP o s₂ hr hb
  obtain ⟨s₁, h₁, hR₂⟩ := hf e₁ e₁ rfl o sm hm hb
  exact ⟨s₁, h₁, hR _ _ _ hR₂ hR₁⟩

theorem refR_modify_ext {α : Type} {P P' Q : Env → Env → Prop} {bad : α → Prop} {n : String}
    {w : Value} (hn : ∀ e₁ e₂, P e₁ e₂ → P' (e₁.extend n w) (e₂.extend n w))
    {k₁ k₂ : PUnit → StateM Env α} (h : ∀ u, RefR P' Q bad (k₁ u) (k₂ u)) :
    RefR P Q bad (_root_.modify (fun x => x.extend n w) >>= k₁)
      (_root_.modify (fun x => x.extend n w) >>= k₂) := by
  intro e₁ e₂ hP o s hr hb
  exact h _ _ _ (hn e₁ e₂ hP) o s hr hb

/-- Pattern matching extends the environment by bindings that depend on the pattern and
    the value only, so a relation kept by every `extend` relates the results. -/
theorem matchPat_rel {R : Env → Env → Prop}
    (hR : ∀ e₁ e₂ n w, R e₁ e₂ → R (e₁.extend n w) (e₂.extend n w)) (pat : ImpPat) (v : Value)
    (e₁ : Env) : ∀ e₂, R e₁ e₂ → Option.Rel R (matchPat pat v e₁) (matchPat pat v e₂) := by
  induction pat, v, e₁ using matchPat.induct (motive_1 := fun pats vs e₁ =>
      ∀ e₂, R e₁ e₂ →
        Option.Rel R (matchPat.matchPatList pats vs e₁) (matchPat.matchPatList pats vs e₂)) with
  | case6 pats vs env hlen ih1 => intro e₂ hs; simp only [matchPat, hlen]; exact ih1 e₂ hs
  | case8 pats vs env hlen ih1 => intro e₂ hs; simp only [matchPat, hlen]; exact ih1 e₂ hs
  | case9 p v env ih2 => intro e₂ hs; simp only [matchPat]; exact ih2 e₂ hs
  | case11 p v env ih2 => intro e₂ hs; simp only [matchPat]; exact ih2 e₂ hs
  | case12 p v env ih2 => intro e₂ hs; simp only [matchPat]; exact ih2 e₂ hs
  | case15 p ps v vs env ih2 ih1 =>
    rename_i e₂ hs
    have h2 := ih2 e₂ hs
    simp only [matchPat.matchPatList]
    revert ih1
    generalize matchPat p v env = a₁ at h2 ⊢
    generalize matchPat p v e₂ = a₂ at h2 ⊢
    intro ih1
    cases h2 with
    | none => exact Option.Rel.none
    | some h => exact ih1 _ _ h
  | case4 name v' env =>
    intro e₂ hs
    simp only [matchPat]
    exact Option.Rel.some (hR _ _ _ _ hs)
  | case16 t x env h1 h2 =>
    rename_i e₂ hs
    cases t <;> cases x <;> simp_all [matchPat.matchPatList]
  | _ =>
    intros
    simp_all [matchPat, matchPat.matchPatList]

theorem denoteMatchArms'_cons_run (bi : Builtins) (fuel : Nat) (v : Value) (p : ImpPat)
    (b : ImpExpr) (rest : List (ImpPat × ImpExpr)) (env : Env) :
    (denoteMatchArms' bi fuel v ((p, b) :: rest)).run env =
      match matchPat p v env with
      | some env' => (denote' bi fuel b).run env'
      | none => (denoteMatchArms' bi fuel v rest).run env := by
  conv => lhs; unfold denoteMatchArms'
  dsimp only [bind, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set,
    MonadStateOf.set, StateT.set, pure, Pure.pure, StateT.pure, Id.run, StateT.run]
  rcases matchPat p v env with _ | e' <;> rfl

/-- Match arms whose bodies are related are related, from environments related by a
    relation that every `extend` keeps. -/
theorem arms_rel {R : Env → Env → Prop} {bi₁ bi₂ : Builtins}
    (hR : ∀ e₁ e₂ n w, R e₁ e₂ → R (e₁.extend n w) (e₂.extend n w)) (g : ImpExpr → ImpExpr)
    (fuel : Nat) (v : Value) (arms : List (ImpPat × ImpExpr))
    (ih : ∀ pa, pa ∈ arms → RefE R (denote' bi₁ fuel (g pa.2)) (denote' bi₂ fuel pa.2)) :
    RefE R (denoteMatchArms' bi₁ fuel v (arms.map fun (p, e) => (p, g e)))
      (denoteMatchArms' bi₂ fuel v arms) := by
  induction arms with
  | nil =>
    simp only [List.map_nil]
    unfold denoteMatchArms'
    exact RefR.pure _
  | cons pa rest iha =>
    obtain ⟨p, b⟩ := pa
    intro e₁ e₂ hR₁ o s₂ hr hb
    have hm := matchPat_rel hR p v e₁ e₂ hR₁
    simp only [List.map_cons]
    rw [denoteMatchArms'_cons_run] at hr ⊢
    generalize matchPat p v e₁ = a₁ at hm ⊢
    generalize matchPat p v e₂ = a₂ at hm hr
    cases hm with
    | none =>
      exact iha (fun pa h => ih pa (List.mem_cons_of_mem _ h)) e₁ e₂ hR₁ o s₂ hr hb
    | some h =>
      exact ih (p, b) List.mem_cons_self _ _ h o s₂ hr hb

section BottomUp

variable {R : Env → Env → Prop} {rd up : String → Bool} {bi : Builtins}
  {f : ImpExpr → ImpExpr}

/-- **Refinement through `bottomUp`.** Let the rewrite `f` of one node refine the node
    from equal environments, the final environments related by a transitive, reflexive
    relation `R`; let every `extend` keep `R`, an `extend` at a name with `up` turn `R`
    into equality, and `R`-related environments agree on the names with `rd`; let `f` keep
    variable reads and their projections. For `e` whose reads are admissible in mode `s`
    (`readsOk`), `bottomUp f e` refines `e` from environments related in mode `s`. -/
theorem denote'_bottomUp (hRrefl : ∀ a, R a a) (hRtrans : ∀ a b c, R a b → R b c → R a c)
    (hRext : ∀ e₁ e₂ n w, R e₁ e₂ → R (e₁.extend n w) (e₂.extend n w))
    (hup : ∀ e₁ e₂ n w, R e₁ e₂ → up n = true → e₁.extend n w = e₂.extend n w)
    (hrd : ∀ e₁ e₂ x, R e₁ e₂ → rd x = true → e₁ x = e₂ x)
    (hfv : ∀ y, f (.var y) = .var y) (hfp : ∀ y i, f (.proj (.var y) i) = .proj (.var y) i)
    (hf : ∀ fuel e, RefR (fun e₁ e₂ => e₁ = e₂) R IsErr (denote' bi fuel (f e))
      (denote' bi fuel e))
    (e : ImpExpr) : ∀ s, readsOk rd up s e = true → ∀ fuel,
      RefR (modeRel R s) R IsErr (denote' bi fuel (bottomUp f e)) (denote' bi fuel e) := by
  have hlow : ∀ s a b, modeRel R s a b → R a b := by
    intro s a b h
    cases s
    · exact h
    · cases h; exact hRrefl a
  have site : ∀ s fuel (x src : ImpExpr),
      RefR (modeRel R s) R IsErr (denote' bi fuel x) (denote' bi fuel src) →
      RefR (modeRel R s) R IsErr (denote' bi fuel (f x)) (denote' bi fuel src) :=
    fun _ fuel x _ h => refR_site hRtrans (hf fuel x) h
  have low : ∀ s {t src : StateM Env Outcome}, RefE R t src → RefR (modeRel R s) R IsErr t src :=
    fun s _ _ h => h.mono (hlow s) (fun _ _ h => h)
  have ext : ∀ n e₁ e₂ w, R e₁ e₂ → R (e₁.extend n w) (e₂.extend n w) :=
    fun n e₁ e₂ w h => hRext e₁ e₂ n w h
  induction e using ImpExpr.ind with
  | var x =>
    intro s hK fuel
    simp only [bottomUp]
    refine site s fuel _ _ ?_
    intro e₁ e₂ hP o s₂ hr hnb
    rw [ContinueFlag.var_run] at hr ⊢
    have hx : e₁ x = e₂ x := by
      cases s
      · simp only [readsOk, Bool.false_or] at hK
        exact hrd e₁ e₂ x hP hK
      · cases hP; rfl
    rw [hx]
    cases h : e₂ x <;> simp only [h] at hr <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
    · exact absurd ⟨_, rfl⟩ hnb
    · exact ⟨e₁, rfl, hlow s _ _ hP⟩
  | letBind n v b ihv ihb =>
    intro s hK fuel
    simp only [readsOk, Bool.and_eq_true] at hK
    simp only [bottomUp]
    refine site s fuel _ _ ?_
    have hv : RefR (modeRel R s) (modeRel R (s && simpleRead v)) IsErr
        (denote' bi fuel (bottomUp f v)) (denote' bi fuel v) := by
      cases s
      · exact ihv false hK.1 fuel
      · cases hsv : simpleRead v
        · exact ihv true hK.1 fuel
        · have hbv : bottomUp f v = v := by
            unfold simpleRead at hsv
            split at hsv
            · simp only [bottomUp, hfv]
            · simp only [bottomUp, hfv, hfp]
            · cases hsv
          rw [hbv]
          exact RefR.refl _
    have hb := ihb _ hK.2 fuel
    have hx : ∀ w e₁ e₂, modeRel R (s && simpleRead v) e₁ e₂ →
        modeRel R (up n || (s && simpleRead v)) (e₁.extend n w) (e₂.extend n w) := by
      intro w e₁ e₂ h
      cases hu : up n
      · simp only [Bool.false_or]
        generalize (s && simpleRead v) = t at h ⊢
        cases t
        · exact ext n e₁ e₂ w h
        · cases h; rfl
      · exact hup e₁ e₂ n w (hlow _ _ _ h) hu
    simp only [denote']
    refine RefR.bind (badα := IsErr) hv (fun o ho => ?_) (fun a ha s => by
      obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨m, rfl⟩)
    split
    · exact (RefR.pure _).mono (hlow _) (fun _ _ h => h)
    · exact refR_modify_ext (hx _) (fun _ => hb)
    · exact (RefR.pure _).mono (hlow _) (fun _ _ h => h)
  | proj e i ih =>
    intro s hK fuel
    simp only [readsOk] at hK
    simp only [bottomUp]
    refine site s fuel _ _ ?_
    have h := ih s hK
    simp only [denote']
    rel_step
  | app g args ih =>
    intro s hK fuel
    simp only [readsOk, readsOk.readsList_eq, List.all_eq_true] at hK
    simp only [bottomUp, bottomUp.mapE_eq]
    refine site s fuel _ _ (low s ?_)
    simp only [denote']
    unfold denoteApp'
    refine RefR.bind (badα := fun o => o = none)
      (args_rel _ args fuel fun a ha => (ih a ha false (hK a ha) fuel).mono (hlow false)
        (fun _ _ h => h))
      (fun r hr => ?_) (fun r hr s => by subst hr; exact ⟨_, rfl⟩)
    split <;> (try split) <;> first | exact RefR.pure _ | exact absurd rfl hr
  | tuple es ih =>
    intro s hK fuel
    simp only [readsOk, readsOk.readsList_eq, List.all_eq_true] at hK
    simp only [bottomUp, bottomUp.mapE_eq]
    refine site s fuel _ _ (low s ?_)
    simp only [denote']
    refine RefR.bind (badα := fun o => o = none)
      (args_rel _ es fuel fun a ha => (ih a ha false (hK a ha) fuel).mono (hlow false)
        (fun _ _ h => h))
      (fun r hr => ?_) (fun r hr s => by subst hr; exact ⟨_, rfl⟩)
    split <;> first | exact RefR.pure _ | exact absurd rfl hr
  | match_ sc arms ihs iha =>
    intro s hK fuel
    simp only [readsOk, readsOk.readsArms_eq, List.all_eq_true, Bool.and_eq_true] at hK
    simp only [bottomUp, bottomUp.mapA_eq]
    refine site s fuel _ _ (low s ?_)
    have hs : RefE R (denote' bi fuel (bottomUp f sc)) (denote' bi fuel sc) := ihs false hK.1 fuel
    have ha := arms_rel hRext (bottomUp f) fuel (bi₁ := bi) (bi₂ := bi)
    simp only [denote']
    refine RefR.bind (badα := IsErr) hs (fun o ho => ?_) (fun a ha s => by
      obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨m, rfl⟩)
    split
    · exact RefR.pure _
    · exact ha _ arms fun pa hpa => iha pa hpa false (hK.2 pa hpa) fuel
    · exact RefR.pure _
  | lam qs b _ =>
    intro _ _ fuel
    simp only [bottomUp]
    refine site _ fuel _ _ ?_
    exact RefR.of_bad fun _ => by simp only [denote']; exact ⟨_, rfl⟩
  | forLoop v lo hi b ihl ihh ihb =>
    intro s hK fuel
    simp only [readsOk, Bool.and_eq_true] at hK
    simp only [bottomUp]
    refine site s fuel _ _ (low s ?_)
    have hl := ihl false hK.1.1
    have hh := ihh false hK.1.2
    have := forLoopOrig'_rel (bi₁ := bi) (ext v) (ihb false hK.2)
    simp only [denote']
    rel_step
  | forLoopRev v lo hi b ihl ihh ihb =>
    intro s hK fuel
    simp only [readsOk, Bool.and_eq_true] at hK
    simp only [bottomUp]
    refine site s fuel _ _ (low s ?_)
    have hl := ihl false hK.1.1
    have hh := ihh false hK.1.2
    have := forLoopRevOrig'_rel (bi₁ := bi) (ext v) (ihb false hK.2)
    simp only [denote']
    rel_step
  | forFold v lo hi b ihl ihh ihb =>
    intro s hK fuel
    simp only [readsOk, Bool.and_eq_true] at hK
    simp only [bottomUp]
    refine site s fuel _ _ (low s ?_)
    have hl := ihl false hK.1.1
    have hh := ihh false hK.1.2
    have := forLoop'_rel (bi₁ := bi) (ext v) (ihb false hK.2)
    simp only [denote']
    rel_step
  | forFoldRev v lo hi b ihl ihh ihb =>
    intro s hK fuel
    simp only [readsOk, Bool.and_eq_true] at hK
    simp only [bottomUp]
    refine site s fuel _ _ (low s ?_)
    have hl := ihl false hK.1.1
    have hh := ihh false hK.1.2
    have := forLoopRev'_rel (bi₁ := bi) (ext v) (ihb false hK.2)
    simp only [denote']
    rel_step
  | forFoldReturn v lo hi b ihl ihh ihb =>
    intro s hK fuel
    simp only [readsOk, Bool.and_eq_true] at hK
    simp only [bottomUp]
    refine site s fuel _ _ (low s ?_)
    have hl := ihl false hK.1.1
    have hh := ihh false hK.1.2
    have := forLoop'Return_rel (bi₁ := bi) (ext v) (ihb false hK.2)
    simp only [denote']
    rel_step
  | forFoldRevReturn v lo hi b ihl ihh ihb =>
    intro s hK fuel
    simp only [readsOk, Bool.and_eq_true] at hK
    simp only [bottomUp]
    refine site s fuel _ _ (low s ?_)
    have hl := ihl false hK.1.1
    have hh := ihh false hK.1.2
    have := forLoopRev'Return_rel (bi₁ := bi) (ext v) (ihb false hK.2)
    simp only [denote']
    rel_step
  | whileLoop c b ihc ihb =>
    intro s hK fuel
    simp only [readsOk, Bool.and_eq_true] at hK
    simp only [bottomUp]
    refine site s fuel _ _ (low s ?_)
    simp only [denote']
    exact whileOrig'_rel (ihc false hK.1) (ihb false hK.2) fuel
  | whileFold c b ihc ihb =>
    intro s hK fuel
    simp only [readsOk, Bool.and_eq_true] at hK
    simp only [bottomUp]
    refine site s fuel _ _ (low s ?_)
    simp only [denote']
    exact while'_rel (ihc false hK.1) (ihb false hK.2) fuel
  | whileFoldReturn c b ihc ihb =>
    intro s hK fuel
    simp only [readsOk, Bool.and_eq_true] at hK
    simp only [bottomUp]
    refine site s fuel _ _ (low s ?_)
    simp only [denote']
    exact while'Return_rel (ihc false hK.1) (ihb false hK.2) fuel
  | assign n rhs ih =>
    intro s hK fuel
    simp only [readsOk] at hK
    simp only [bottomUp]
    refine site s fuel _ _ (low s ?_)
    have hn := ext n
    have hr := ih false hK
    simp only [denote']
    rel_step
  | seq a b iha ihb =>
    intro s hK fuel
    simp only [readsOk, Bool.and_eq_true] at hK
    simp only [bottomUp]
    refine site s fuel _ _ (low s ?_)
    have ha := iha false hK.1
    have hb := ihb false hK.2
    simp only [denote']
    rel_step
  | ifThenElse c t e ihc iht ihe =>
    intro s hK fuel
    simp only [readsOk, Bool.and_eq_true] at hK
    simp only [bottomUp]
    refine site s fuel _ _ (low s ?_)
    have h1 := ihc false hK.1.1
    have h2 := iht false hK.1.2
    have h3 := ihe false hK.2
    simp only [denote']
    rel_step
  | borrow e ih | deref e ih | break_some e ih | earlyReturn e ih
  | questionMark e ih | cfBreak e ih | cfContinue e ih | cfBreakContinue e ih
  | typeAscription e _ ih =>
    intro s hK fuel
    simp only [readsOk] at hK
    simp only [bottomUp]
    refine site s fuel _ _ (low s ?_)
    have h := ih false hK
    simp only [denote']
    rel_step
  | _ =>
    intro s _ fuel
    simp only [bottomUp]
    refine site s fuel _ _ (low s ?_)
    simp only [denote']
    rel_step

end BottomUp

end IrrefutableTupleMatch

open IrrefutableTupleMatch InlineLocalClosures in
/-- **The whole pass.** `irrefutableTupleMatch e` refines `e` under `denote'`: from equal
    environments, every run of `e` that does not end in an error is the run of the
    rewritten term, with the same final environment. -/
theorem irrefutableTupleMatch_refines (bi : Builtins) (e : ImpExpr) (fuel : Nat) :
    RefE (fun e₁ e₂ => e₁ = e₂) (denote' bi fuel (irrefutableTupleMatch e))
      (denote' bi fuel e) :=
  denote'_bottomUp (rd := fun _ => true) (up := fun _ => true) (fun _ => rfl)
    (fun _ _ _ h₁ h₂ => h₁.trans h₂) (fun _ _ _ _ h => h ▸ rfl) (fun _ _ _ _ h _ => h ▸ rfl)
    (fun _ _ _ h _ => h ▸ rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun fuel e => denote'_rewriteSite bi fuel e) e true
    (readsOk_of_rd _ (fun _ => rfl) e true) fuel

end Hax
