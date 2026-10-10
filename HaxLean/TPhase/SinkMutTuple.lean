/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.TPhase.IrrefutableTupleMatch

/-!
# The mutation tuple of an `if`-join sunk into its branches

`ThreadMutations.tThreadMut` joins the variables `x₁, …, xₙ` that the branches of a
statement-`if` assign by ending each branch in the tuple of those variables and
destructuring the joined value bound to `m` (`_mtup`):

    letBind m (ifThenElse c T F) (destructure xs (var m) rest)

where `destructure [x] (var m)` binds `x` to `var m`, and for `n ≥ 2` the chain binds
each `xᵢ` to the flat projection `proj (var m) i`. Under `denote'` a binding is not
undone at the end of a branch, so each `xᵢ` already holds its joined value after the
`if`, and the destructuring rebinds every `xᵢ` to the value it holds. The rewrite drops
the binding of `m` and the destructuring:

    seq (ifThenElse c T' F') rest

where `T'` and `F'` are the branches with the tail tuple `(xs)` replaced by `unitVal`
(`stripTail`); a single variable tail `var x` stays. The site is rewritten only when

* every branch tail, through `letBind` bodies, `seq` continuations and nested
  `ifThenElse` branches, is the tuple of the variables `xs` (`n ≥ 2`) or the variable
  `x` (`n = 1`);
* the body is the destructuring of `xs` from `var m`, followed by `rest` (`undestr`);
* no `xᵢ` is `m`;
* `rest` does not read `m` and contains no `match_` (`frameOk`).

The final environments of the two sides differ at `m` alone, so the refinement relates
equal initial environments to final environments that agree off `m` (`EqOff [m]`).

`sinkMutTuple` applies the rewrite at `m = "_mtup"` bottom-up at every node.

## Main results

* `stripTail_run`: a branch and its stripped form run alike, the stripped one ending
  in a non-control-flow value where the branch ends in its tail tuple.
* `denote'_rewriteSite`: the rewrite of one node refines the node under `denote'`, the
  final environments agreeing off `m`.
* `sinkMutTuple_refines`: the whole pass refines its input under `denote'` when the input
  reads `_mtup` only right after binding it (`mtupReadsOk`), the final environments
  agreeing off `_mtup`.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax

namespace SinkMutTuple

open InlineLocalClosures IrrefutableTupleMatch

/-! ## The rewrite of one node -/

/-- The names of a list of variable reads; `none` when an element is not a variable. -/
def varsOf : List ImpExpr → Option (List String)
  | [] => some []
  | .var x :: es => (varsOf es).map (x :: ·)
  | _ :: _ => none

/-- The variables of the tail of the first branch: the variable of a tail `var x`, the
    variables of a tail tuple of variables. -/
def tailVars : ImpExpr → Option (List String)
  | .var x => some [x]
  | .tuple es => varsOf es
  | .letBind _ _ b => tailVars b
  | .seq _ b => tailVars b
  | .ifThenElse _ t _ => tailVars t
  | _ => none

/-- The branch with its tail replaced: a tail tuple of the variables `xs` (`n ≥ 2`)
    becomes `unitVal`, a tail `var x` with `xs = [x]` stays. The tail is reached through
    `letBind` bodies, `seq` continuations and both branches of an `ifThenElse`; `none`
    when some tail is not of this form. -/
def stripTail (xs : List String) : ImpExpr → Option ImpExpr
  | .var x => if xs = [x] then some (.var x) else none
  | .tuple es => if varsOf es = some xs ∧ 2 ≤ xs.length then some .unitVal else none
  | .letBind n v b => (stripTail xs b).map (.letBind n v)
  | .seq a b => (stripTail xs b).map (.seq a)
  | .ifThenElse c t f =>
    match stripTail xs t, stripTail xs f with
    | some t', some f' => some (.ifThenElse c t' f')
    | _, _ => none
  | _ => none

/-- The continuation after a chain binding `xs` to the flat projections `i, i+1, …` of
    `var m`; `none` when the expression is not such a chain. -/
def undestrAt (m : String) : Nat → List String → ImpExpr → Option ImpExpr
  | _, [], e => some e
  | i, x :: xs, .letBind y (.proj (.var m') j) b =>
    if y = x ∧ m' = m ∧ j = i then undestrAt m (i + 1) xs b else none
  | _, _ :: _, _ => none

/-- The continuation after the destructuring of `xs` from `var m`: the binding of `x` to
    `var m` for `xs = [x]`, the chain of flat projections otherwise. -/
def undestr (m : String) (xs : List String) (e : ImpExpr) : Option ImpExpr :=
  match xs, e with
  | [x], .letBind y (.var m') b => if y = x ∧ m' = m then some b else none
  | [_], _ => none
  | _, _ => undestrAt m 0 xs e

/-- `rest` reads no `m` and contains no `match_`. -/
def restOk (m : String) (rest : ImpExpr) : Bool :=
  frameOk (fun y => y != m) (fun _ => true) (fun _ => true) rest

/-- The rewrite of one node at the join variable `m`. -/
def rewriteSite (m : String) (e : ImpExpr) : ImpExpr :=
  match e with
  | .letBind m' (.ifThenElse c t f) body =>
    if m' = m then
      match tailVars t with
      | some xs =>
        match stripTail xs (.ifThenElse c t f), undestr m xs body with
        | some s, some rest =>
          if xs.contains m = false ∧ restOk m rest = true then .seq s rest else e
        | _, _ => e
      | none => e
    else e
  | _ => e

end SinkMutTuple

open SinkMutTuple IrrefutableTupleMatch in
/-- Sink every `_mtup` join of an `if` into its branches. -/
def sinkMutTuple (e : ImpExpr) : ImpExpr := bottomUp (rewriteSite "_mtup") e

namespace SinkMutTuple

open InlineLocalClosures IrrefutableTupleMatch

/-! ## Runs of the pieces -/

/-- A value that is not a control-flow value. -/
def NotCf (v : Value) : Prop := ∀ b w, v ≠ .controlFlow b w

/-- The joined value `v` of the variables `xs` in `s`: `s x = some v` for `xs = [x]`,
    and for `n ≥ 2` a tuple of non-control-flow values that `s` holds at `xs`. -/
def Fits (xs : List String) (v : Value) (s : Env) : Prop :=
  match xs with
  | [x] => s x = some v
  | _ => ∃ vals, v = .tuple vals ∧ xs.map s = vals.map some ∧ ∀ w ∈ vals, NotCf w

theorem extend_self {env : Env} {x : String} {w : Value} (h : env x = some w) :
    env.extend x w = env := by
  funext y
  simp only [Env.extend]
  split
  · rename_i hy; simp only [beq_iff_eq] at hy; subst hy; exact h.symm
  · rfl

/-- Arguments that are variables leave the environment unchanged and evaluate to the
    values the environment holds. -/
theorem denoteArgs'_vars (bi : Builtins) (fuel : Nat) :
    ∀ (es : List ImpExpr) (xs : List String), varsOf es = some xs →
      ∀ (env s : Env) (vals : List Value), denoteArgs' bi fuel es env = (some vals, s) →
        s = env ∧ xs.map env = vals.map some ∧ ∀ w ∈ vals, NotCf w := by
  intro es
  induction es with
  | nil =>
    intro xs hx env s vals h
    simp only [varsOf, Option.some.injEq] at hx
    subst hx
    rw [denoteArgs'_nil] at h
    cases h
    simp
  | cons e es ih =>
    intro xs hx env s vals h
    cases e with
    | var x =>
      simp only [varsOf, Option.map_eq_some_iff] at hx
      obtain ⟨ys, hys, rfl⟩ := hx
      obtain ⟨v, s₀, vs, he, hcf, hes, rfl⟩ := denoteArgs'_cons_some bi fuel _ es env s vals h
      rw [denote'_var_run] at he
      cases hx : env x with
      | none => rw [hx] at he; cases he
      | some w =>
        rw [hx] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨rfl, h2, h3⟩ := ih ys hys env s vs hes
        refine ⟨rfl, by simp [hx, h2], ?_⟩
        intro w' hw'
        simp only [List.mem_cons] at hw'
        rcases hw' with rfl | hw'
        · exact hcf
        · exact h3 w' hw'
    | _ => simp [varsOf] at hx

/-- **The stripped branch.** When `stripTail xs T = some T'`, every run of `T` that does
    not end in an error either ends in a non-control-flow value `v` joining `xs`
    (`Fits`), the run of `T'` then ending in a non-control-flow value in the same
    environment, or ends in an outcome other than such a value, which `T'` reproduces. -/
theorem stripTail_run (bi : Builtins) (fuel : Nat) (xs : List String) (T : ImpExpr) :
    ∀ T', stripTail xs T = some T' → ∀ env o s, denote' bi fuel T env = (o, s) →
      ¬ IsErr o →
      (∃ v, o = .val v ∧ NotCf v ∧ Fits xs v s ∧
          ∃ u, NotCf u ∧ denote' bi fuel T' env = (.val u, s)) ∨
        ((∀ v, o = .val v → ¬ NotCf v) ∧ denote' bi fuel T' env = (o, s)) := by
  induction T using ImpExpr.ind with
  | var x =>
    intro T' hT env o s hr hne
    simp only [stripTail] at hT
    split at hT
    · rename_i hx
      cases hT
      subst hx
      rw [denote'_var_run] at hr
      cases hv : env x with
      | none => rw [hv] at hr; cases hr; exact absurd ⟨_, rfl⟩ hne
      | some v =>
        rw [hv] at hr
        cases hr
        by_cases hc : NotCf v
        · exact .inl ⟨v, rfl, hc, hv, v, hc, by rw [denote'_var_run, hv]⟩
        · exact .inr ⟨fun w hw => by cases hw; exact hc, by rw [denote'_var_run, hv]⟩
    · cases hT
  | tuple es _ =>
    intro T' hT env o s hr hne
    simp only [stripTail] at hT
    split at hT
    · rename_i hx
      cases hT
      rw [denote'_tuple_run] at hr
      revert hr
      generalize hd : denoteArgs' bi fuel es env = q
      obtain ⟨r, s₀⟩ := q
      cases r with
      | none => intro hr; cases hr; exact absurd ⟨_, rfl⟩ hne
      | some vals =>
        intro hr
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
        obtain ⟨hs, h2, h3⟩ := denoteArgs'_vars bi fuel es xs hx.1 env s₀ vals hd
        rw [hs]
        refine .inl ⟨.tuple vals, rfl, (fun _ _ h => by cases h), ?_, Value.unit,
          (fun _ _ h => by cases h), denote'_unitVal_run bi fuel env⟩
        match xs, hx.2 with
        | _ :: _ :: _, _ => exact ⟨vals, rfl, h2, h3⟩
    · cases hT
  | letBind n v b _ ih =>
    intro T' hT env o s hr hne
    simp only [stripTail, Option.map_eq_some_iff] at hT
    obtain ⟨b', hb, rfl⟩ := hT
    rw [denote'_letBind_run] at hr
    generalize hq : denote' bi fuel v env = q at hr
    obtain ⟨r, e₁⟩ := q
    rw [denote'_letBind_run, hq]
    rcases r with w | w | w | _ | msg
    · cases w with
      | controlFlow k w' =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
        exact .inr ⟨(fun v hv => by cases hv; exact fun h' => h' k w' rfl), rfl⟩
      | _ => exact ih b' hb _ o s hr hne
    all_goals (obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr; exact .inr ⟨(fun _ h => by cases h), rfl⟩)
  | seq a b _ ih =>
    intro T' hT env o s hr hne
    simp only [stripTail, Option.map_eq_some_iff] at hT
    obtain ⟨b', hb, rfl⟩ := hT
    rw [denote'_seq_run] at hr
    generalize hq : denote' bi fuel a env = q at hr
    obtain ⟨r, e₁⟩ := q
    rw [denote'_seq_run, hq]
    rcases r with w | w | w | _ | msg
    · cases w with
      | controlFlow k w' =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
        exact .inr ⟨(fun v hv => by cases hv; exact fun h' => h' k w' rfl), rfl⟩
      | _ => exact ih b' hb _ o s hr hne
    all_goals (obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr; exact .inr ⟨(fun _ h => by cases h), rfl⟩)
  | ifThenElse c t f _ iht ihf =>
    intro T' hT env o s hr hne
    simp only [stripTail] at hT
    cases ht : stripTail xs t with
    | none => simp [ht] at hT
    | some t' =>
      cases hf : stripTail xs f with
      | none => simp [ht, hf] at hT
      | some f' =>
        simp only [ht, hf, Option.some.injEq] at hT
        subst hT
        rw [denote'_ifThenElse_run] at hr
        generalize hq : denote' bi fuel c env = q at hr
        obtain ⟨r, e₁⟩ := q
        rw [denote'_ifThenElse_run, hq]
        rcases r with w | w | w | _ | msg
        · cases w with
          | controlFlow k w' =>
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
            exact .inr ⟨(fun v hv => by cases hv; exact fun h' => h' k w' rfl), rfl⟩
          | bool b =>
            cases b
            · exact ihf f' hf _ o s hr hne
            · exact iht t' ht _ o s hr hne
          | _ => obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr; exact absurd ⟨_, rfl⟩ hne
        all_goals (obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr; exact .inr ⟨(fun _ h => by cases h), rfl⟩)
  | _ => intro T' hT; simp [stripTail] at hT

/-- The chain of flat projections of `var m` rebinds each variable to the value it holds,
    so it runs as its continuation. -/
theorem undestrAt_run (bi : Builtins) (fuel : Nat) (m : String) (rest : ImpExpr)
    (σ : Env) (vals : List Value) (hm : σ m = some (.tuple vals)) :
    ∀ (xs : List String) (i : Nat) (e : ImpExpr), undestrAt m i xs e = some rest →
      (∀ j x, xs[j]? = some x → x ≠ m ∧ ∃ w, vals[i + j]? = some w ∧ σ x = some w ∧ NotCf w) →
      denote' bi fuel e σ = denote' bi fuel rest σ := by
  intro xs
  induction xs with
  | nil =>
    intro i e h _
    simp only [undestrAt, Option.some.injEq] at h
    subst h; rfl
  | cons x xs ih =>
    intro i e h hx
    obtain ⟨b, rfl, hb⟩ : ∃ b, e = .letBind x (.proj (.var m) i) b ∧
        undestrAt m (i + 1) xs b = some rest := by
      cases e with
      | letBind y v b =>
        cases v with
        | proj e' j =>
          cases e' with
          | var m' =>
            simp only [undestrAt] at h
            split at h
            · rename_i hc
              obtain ⟨rfl, rfl, rfl⟩ := hc
              exact ⟨b, rfl, h⟩
            · cases h
          | _ => simp [undestrAt] at h
        | _ => simp [undestrAt] at h
      | _ => simp [undestrAt] at h
    obtain ⟨-, w, hw, hσ, hcf⟩ := hx 0 x rfl
    have hproj : denote' bi fuel (.proj (.var m) i) σ = (.val w, σ) := by
      change (denote' bi fuel (.proj (.var m) i)).run σ = _
      rw [proj_run]
      change (match denote' bi fuel (.var m) σ with
        | (Outcome.val (.controlFlow k v), e1) => (Outcome.val (.controlFlow k v), e1)
        | (Outcome.val v, e1) =>
          match v.projIdx i with
          | some vi => (Outcome.val vi, e1)
          | none => (Outcome.err s!"projection index {i} out of range", e1)
        | (o, e1) => (o, e1)) = _
      rw [denote'_var_run, hm]
      simp only [Value.projIdx]
      simp only [Nat.add_zero] at hw
      rw [hw]
    rw [denote'_letBind_run, hproj]
    have hb : denote' bi fuel b (σ.extend x w) = denote' bi fuel rest σ := by
      rw [extend_self hσ]
      refine ih (i + 1) b hb fun k z hz => ?_
      obtain ⟨hne, w', hw', hz', hcf'⟩ := hx (k + 1) z (by simpa using hz)
      exact ⟨hne, w', by rw [← hw']; congr 1; omega, hz', hcf'⟩
    cases w with
    | controlFlow k w' => exact absurd rfl (hcf k w')
    | _ => exact hb

/-- The destructuring of `xs` from `var m`, with `m` holding the joined value of `xs`,
    runs as its continuation. -/
theorem undestr_run (bi : Builtins) (fuel : Nat) (m : String) (xs : List String)
    (body rest : ImpExpr) (h : undestr m xs body = some rest) (hxm : xs.contains m = false)
    {v : Value} {s : Env} (hv : NotCf v) (hfit : Fits xs v s) :
    denote' bi fuel body (s.extend m v) = denote' bi fuel rest (s.extend m v) := by
  have hσx : ∀ x, xs.contains x = true → (s.extend m v) x = s x := fun x hx =>
    ContinueFlag.extend_ne v (fun hxe => by subst hxe; simp_all)
  match xs, h, hfit, hσx with
  | [x], h, hfit, hσx =>
    cases body with
    | letBind y w b =>
      cases w with
      | var m' =>
        simp only [undestr] at h
        split at h
        · rename_i hc
          obtain ⟨hy, hm'⟩ := hc
          subst hy hm'
          obtain rfl : b = rest := by simpa using ‹some b = some rest›
          have hx : (s.extend m' v) y = some v := by rw [hσx y (by simp)]; exact hfit
          have hm : (s.extend m' v) m' = some v := by simp [Env.extend]
          rw [denote'_letBind_run, denote'_var_run, hm]
          cases v with
          | controlFlow k w' => exact absurd rfl (hv k w')
          | _ => simp only; rw [extend_self hx]
        · cases h
      | _ => simp [undestr] at h
    | _ => simp [undestr] at h
  | [], h, _, _ => simp [undestr, undestrAt] at h; subst h; rfl
  | a :: b :: c, h, hfit, hσx =>
    obtain ⟨vals, rfl, hmap, hcf⟩ := hfit
    refine undestrAt_run bi fuel m rest (s.extend m (.tuple vals)) vals
      (by simp [Env.extend]) (a :: b :: c) 0 body h fun j x hj => ?_
    have hxin : (a :: b :: c).contains x = true := by
      simpa using List.mem_of_getElem? hj
    refine ⟨fun hxe => by subst hxe; simp_all, ?_⟩
    have h1 : ((a :: b :: c).map s)[j]? = some (s x) := by rw [List.getElem?_map, hj]; rfl
    rw [hmap, List.getElem?_map] at h1
    cases hw : vals[j]? with
    | none => simp [hw] at h1
    | some w =>
      simp only [hw, Option.map_some, Option.some.injEq] at h1
      exact ⟨w, by simpa using hw, by rw [hσx x hxin, ← h1], hcf w (List.mem_of_getElem? hw)⟩

theorem letBind_val {bi : Builtins} {fuel : Nat} {n : String} {v b : ImpExpr} {env e : Env}
    {w : Value} (h : denote' bi fuel v env = (.val w, e)) (hw : NotCf w) :
    denote' bi fuel (.letBind n v b) env = denote' bi fuel b (e.extend n w) := by
  rw [denote'_letBind_run, h]
  cases w with
  | controlFlow k w' => exact absurd rfl (hw k w')
  | _ => rfl

theorem seq_val {bi : Builtins} {fuel : Nat} {a b : ImpExpr} {env e : Env}
    {w : Value} (h : denote' bi fuel a env = (.val w, e)) (hw : NotCf w) :
    denote' bi fuel (.seq a b) env = denote' bi fuel b e := by
  rw [denote'_seq_run, h]
  cases w with
  | controlFlow k w' => exact absurd rfl (hw k w')
  | _ => rfl

theorem letBind_nonplain {bi : Builtins} {fuel : Nat} {n : String} {v b : ImpExpr} {env e : Env}
    {r : Outcome} (h : denote' bi fuel v env = (r, e)) (hr : ∀ w, r = .val w → ¬ NotCf w) :
    denote' bi fuel (.letBind n v b) env = (r, e) := by
  rw [denote'_letBind_run, h]
  rcases r with w | _ | _ | _ | _
  · cases w with
    | controlFlow k w' => rfl
    | _ => exact absurd (fun _ _ h => by cases h) (hr _ rfl)
  all_goals rfl

theorem seq_nonplain {bi : Builtins} {fuel : Nat} {a b : ImpExpr} {env e : Env}
    {r : Outcome} (h : denote' bi fuel a env = (r, e)) (hr : ∀ w, r = .val w → ¬ NotCf w) :
    denote' bi fuel (.seq a b) env = (r, e) := by
  rw [denote'_seq_run, h]
  rcases r with w | _ | _ | _ | _
  · cases w with
    | controlFlow k w' => rfl
    | _ => exact absurd (fun _ _ h => by cases h) (hr _ rfl)
  all_goals rfl

/-- The rewrite of one node refines the node under `denote'`: equal initial environments,
    final environments agreeing off `m`. -/
theorem denote'_rewriteSite (bi : Builtins) (fuel : Nat) (m : String) (e : ImpExpr) :
    RefR (fun e₁ e₂ => e₁ = e₂) (EqOff [m]) IsErr (denote' bi fuel (rewriteSite m e))
      (denote' bi fuel e) := by
  have refl : RefR (fun e₁ e₂ => e₁ = e₂) (EqOff [m]) IsErr (denote' bi fuel e)
      (denote' bi fuel e) :=
    RefR.mono (RefR.refl _) (fun _ _ h => h) (fun a b h => EqOff.of_eq [m] a b h)
  unfold rewriteSite
  split
  · rename_i m' c t f body
    split
    · rename_i hm'
      subst m'
      split
      · rename_i xs _
        split
        · rename_i s rest hs hrest
          split
          · rename_i hc
            obtain ⟨hxm, hok⟩ := hc
            intro e₁ e₁' hpre o s₂ hr hne
            subst hpre
            change denote' bi fuel _ e₁ = (o, s₂) at hr
            change ∃ s₁, denote' bi fuel _ e₁ = (o, s₁) ∧ _
            generalize hite : denote' bi fuel (.ifThenElse c t f) e₁ = q
            obtain ⟨r, e₂⟩ := q
            by_cases herr : IsErr r
            · obtain ⟨msg, rfl⟩ := herr
              rw [letBind_nonplain hite (fun _ h => by cases h)] at hr
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
              exact absurd ⟨_, rfl⟩ hne
            · rcases stripTail_run bi fuel xs _ s hs e₁ r e₂ hite herr with
                ⟨v, rfl, hv, hfit, u, hu, hs'⟩ | ⟨hnp, hs'⟩
              · rw [letBind_val hite hv, undestr_run bi fuel m xs body rest hrest hxm hv hfit] at hr
                rw [seq_val hs' hu]
                have hfr := denote'_frame (R := EqOff [m]) (bi₁ := bi) (bi₂ := bi) id
                  (fun y => y != m) (fun _ => true) (fun _ => true)
                  (fun _ _ x h hx => h x (by simpa using hx))
                  (fun _ _ n w h _ x hx => by
                    simp only [Env.extend]
                    split
                    · rfl
                    · exact h x hx)
                  (fun _ _ => rfl) rest hok fuel
                rw [renameReads_id rest (frameOk_mono (fun _ _ => rfl) (fun _ _ => rfl)
                  (fun _ _ => rfl) rest hok)] at hfr
                exact hfr e₂ (e₂.extend m v)
                  (fun x hx => (ContinueFlag.extend_ne v (by simpa using hx)).symm) o s₂ hr hne
              · rw [letBind_nonplain hite hnp] at hr
                rw [seq_nonplain hs' hnp]
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
                exact ⟨_, rfl, EqOff.of_eq [m] _ _ rfl⟩
          · exact refl
        · exact refl
      · exact refl
    · exact refl
  · exact refl

/-! ## The whole pass -/

/-- The reads of `_mtup` in `e` are admissible for `sinkMutTuple`: `_mtup` is read only
    where every run has just bound it (`readsOk`, the binding of `_mtup` and the chain of
    variable reads and their projections after it in mode `true`). -/
def mtupReadsOk (e : ImpExpr) : Bool :=
  readsOk (fun y => y != "_mtup") (fun n => n == "_mtup") true e

end SinkMutTuple

open SinkMutTuple IrrefutableTupleMatch InlineLocalClosures in
/-- **The whole pass.** For `e` that reads `_mtup` only where it has just been bound
    (`mtupReadsOk`), `sinkMutTuple e` refines `e` under `denote'`: from equal environments,
    every run of `e` that does not end in an error is matched by a run of the rewritten
    term with the same outcome, the final environments agreeing off `_mtup`. -/
theorem sinkMutTuple_refines (bi : Builtins) (e : ImpExpr) (h : mtupReadsOk e = true)
    (fuel : Nat) :
    RefR (fun e₁ e₂ => e₁ = e₂) (EqOff ["_mtup"]) IsErr (denote' bi fuel (sinkMutTuple e))
      (denote' bi fuel e) :=
  denote'_bottomUp (rd := fun y => y != "_mtup") (up := fun n => n == "_mtup")
    (fun _ _ _ => rfl) (fun _ _ _ h₁ h₂ x hx => (h₁ x hx).trans (h₂ x hx))
    (by
      intro e₁ e₂ n w h x hx
      simp only [Env.extend]
      split
      · rfl
      · exact h x hx)
    (by
      intro e₁ e₂ n w h hn
      simp only [beq_iff_eq] at hn
      subst hn
      funext x
      simp only [Env.extend]
      split
      · rfl
      · rename_i hx
        exact h x (by simpa using hx))
    (fun _ _ x h hx => h x (by simpa using hx)) (fun _ => rfl) (fun _ _ => rfl)
    (fun fuel e => denote'_rewriteSite bi fuel "_mtup" e) e true h fuel

end Hax
