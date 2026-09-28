/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Phase.InlineLocalClosures

/-!
# `map` over a closure literal as a counted loop

hax-lean emits `let ys: Vec<_> = xs.iter().map(|p| body).collect()` as
`letBind y (app "collect" [app "map" [app "iter" [var s], lam [p] body]]) k`. The reference
semantics `denote'` does not evaluate closures, so the binding errs and a lowering has
no image for it. For a pure `body` it is the counted loop `mapStmt y s i x n body'`:

```
letBind n (len s);
letBind y (var s) unitVal;
forFold i 0 n (letBind x (index s i) (letBind y (array_update y i body') unitVal))
```

where `body' = subst [p] [var x] body` reads the element through a variable `x`, `i` is
the counter and `n` holds the length, so the bound is a variable. `y` starts as a copy of
`s`, which fixes its length; trip `j` replaces element `j` by the value of the body at
element `j` of `s`.

A source that is not a variable is first bound to `mapS y` (`nameMapSources`).

**Reference reading.** `mapArray bi fuel ρ s p body` is the array of the values of `body`
read in `ρ` with `p` bound to each element of the array `s` holds; it is defined when
`s` holds an array of at most `fuel` elements, none a control-flow value, and every value
of the body is a value that is not a control-flow value. `denoteMapSpine` reads each
rewritten `map` binding on the statement spine as the binding of `y` to that array, and
every other expression by `denote'`.

**Builtins.** The loop reads `len`, `index` and `array_update`; `ArrayOps bi` states that
`bi` answers them as `Hax.widthArrayOps` does on arrays (`arrayOps_widthArrayOps`).

**Agreement.** The loop leaves `i`, `x` and `n` bound. From one environment, every run
of the reference reading that does not end in an error is matched by the run of the
rewritten program, the final environments agreeing off the variables of the loops
(`RefR`, `EqOff`). The continuation of a rewritten binding reads none of them.

## Main results

* `mapStmt_run`: the loop binds `y` to `mapArray`, the environment agreeing with the
  binding off `i`, `x` and `n`
* `denote'_inlineMaps`: `inlineMaps e` read with `bi` refines `denoteMapSpine bi fuel e`,
  the final environments agreeing off `mapW e`
* `denote'_inlineMapClosures`: the same for `inlineMapClosures`, sources named first
-/

@[expose] public section
set_option autoImplicit false

namespace Hax.InlineMap

open InlineLocalClosures
open ContinueFlag (var_run lit_run unitVal_run letBind_run seq_run app_run args_nil_run
  args_cons_run forLoop_ge_run forLoop_succ_run)

/-! ## The builtins the loop reads -/

/-- `bi` answers `len`, `index` at an integer and `array_update` at an integer on an array
    as `widthArrayOps` does. -/
structure ArrayOps (bi : Builtins) : Prop where
  len : ∀ vs : List Value, bi "len" [.array vs] = some (.uint .wsize vs.length)
  index : ∀ (vs : List Value) (j : Nat) (h : j < vs.length), vs[j].isControlFlow = false →
    bi "index" [.array vs, .int j] = some vs[j]
  update : ∀ (vs : List Value) (j : Nat) (v : Value), j < vs.length →
    bi "array_update" [.array vs, .int j, v] = some (.array (vs.set j v))

theorem arrayOps_widthArrayOps : ArrayOps widthArrayOps where
  len vs := rfl
  index vs j h hcf := by
    simp [widthArrayOps, h]; revert hcf; cases vs[j] <;> simp [Value.isControlFlow]
  update vs j v h := by
    simp [widthArrayOps, h]

/-! ## The loop and the reference reading -/

/-- The loop that binds `y` to the array of the values of `bodyX` at the elements of the
    array `s`: the length of `s` bound to `n`, element `j` bound to `x` and the counter `i`
    to `j`. -/
def mapStmt (y s i x n : String) (bodyX : ImpExpr) : ImpExpr :=
  .letBind n (.app "len" [.var s])
    (.seq (.letBind y (.var s) .unitVal)
      (.forFold i (.lit (.int 0)) (.var n)
        (.letBind x (.app "index" [.var s, .var i])
          (.letBind y (.app "array_update" [.var y, .var i, bodyX]) .unitVal))))

/-- The values of `body` read at fuel `fuel` in `ρ` with `p` bound to each element; none
    when a reading does not end in a value or ends in a control-flow value. -/
def mapVals (bi : Builtins) (fuel : Nat) (ρ : Env) (p : String) (body : ImpExpr) :
    List Value → Option (List Value)
  | [] => some []
  | v :: vs =>
    match ((denote' bi fuel body).run (ρ.extend p v)).1 with
    | .val w => if w.isControlFlow then none else (mapVals bi fuel ρ p body vs).map (w :: ·)
    | _ => none

/-- The array `collect (map (iter s) (fun p => body))` in `ρ`: defined when `s` holds an
    array of at most `fuel` elements none of which is a control-flow value. -/
def mapArray (bi : Builtins) (fuel : Nat) (ρ : Env) (s p : String) (body : ImpExpr) :
    Option (List Value) :=
  match ρ s with
  | some (.array vs) =>
    if vs.length ≤ fuel ∧ vs.all (fun v => !v.isControlFlow) = true then
      mapVals bi fuel ρ p body vs
    else none
  | _ => none

/-! ## The reference values -/

theorem mapVals_spec (bi : Builtins) (fuel : Nat) (ρ : Env) (p : String) (body : ImpExpr) :
    ∀ (vs ws : List Value), mapVals bi fuel ρ p body vs = some ws →
      ws.length = vs.length ∧ ∀ (j : Nat) (h : j < vs.length) (h' : j < ws.length),
        ((denote' bi fuel body).run (ρ.extend p vs[j])).1 = .val ws[j] ∧
          ws[j].isControlFlow = false
  | [], ws, h => by
    simp only [mapVals, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun j h => absurd h (Nat.not_lt_zero j)⟩
  | v :: vs, ws, h => by
    simp only [mapVals] at h
    split at h
    · rename_i w hw
      cases hc : w.isControlFlow
      · rw [hc] at h
        simp only [Bool.false_eq_true, if_false] at h
        cases hr : mapVals bi fuel ρ p body vs with
        | none => rw [hr] at h; cases h
        | some rs =>
          rw [hr] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          obtain ⟨hl, hs⟩ := mapVals_spec bi fuel ρ p body vs rs hr
          refine ⟨by simp [hl], fun j hj hj' => ?_⟩
          cases j with
          | zero => exact ⟨hw, hc⟩
          | succ j =>
            exact hs j (by simpa using hj) (by simpa using hj')
      · rw [hc] at h; cases h
    · cases h

/-! ## One trip of the loop -/

section Trip

variable (bi : Builtins)

theorem trip_run (hbi : ArrayOps bi) (y s i x : String) (bodyX : ImpExpr) (f : Nat) (E : Env)
    (vs cur : List Value) (j : Nat) (w : Value)
    (hs : E s = some (.array vs)) (hi : E i = some (.int j)) (hy : E y = some (.array cur))
    (hj : j < vs.length) (hjc : j < cur.length) (hcf : vs[j].isControlFlow = false)
    (hxi : x ≠ i) (hxy : x ≠ y)
    (hw : (denote' bi f bodyX).run (E.extend x vs[j]) = (.val w, E.extend x vs[j]))
    (hwcf : w.isControlFlow = false) :
    (denote' bi f (.letBind x (.app "index" [.var s, .var i])
        (.letBind y (.app "array_update" [.var y, .var i, bodyX]) .unitVal))).run E =
      (.val .unit, (E.extend x vs[j]).extend y (.array (cur.set j w))) := by
  rw [letBind_run, app_run, args_cons_run, var_run, hs]
  simp only
  rw [args_cons_run, var_run, hi]
  simp only [args_nil_run, Option.map_some]
  rw [hbi.index vs j hj hcf]
  have hy' : (E.extend x vs[j]) y = some (.array cur) := by
    simp [Env.extend, Ne.symm hxy, hy]
  have hi' : (E.extend x vs[j]) i = some (.int j) := by
    simp [Env.extend, Ne.symm hxi, hi]
  have hupd := hbi.update cur j w hjc
  generalize hv : vs[j] = v at hcf hw hy' hi' ⊢
  cases v
  case controlFlow => simp [Value.isControlFlow] at hcf
  all_goals
    simp only
    rw [letBind_run, app_run, args_cons_run, var_run, hy']
    simp only
    rw [args_cons_run, var_run, hi']
    simp only
    rw [args_cons_run, hw]
    cases w
    case controlFlow => simp [Value.isControlFlow] at hwcf
    all_goals
      simp only [args_nil_run, Option.map_some]
      rw [hupd]
      simp only [unitVal_run]

theorem take_append_drop_set {α : Type} (ws vs : List α) (j : Nat) (hl : ws.length = vs.length)
    (hj : j < ws.length) :
    (ws.take j ++ vs.drop j).set j ws[j] = ws.take (j + 1) ++ vs.drop (j + 1) := by
  apply List.ext_getElem
  · simp; omega
  · intro k h1 h2
    simp only [List.getElem_set, List.getElem_append, List.getElem_take, List.getElem_drop,
      List.length_take] at *
    by_cases hk : j = k
    · subst hk; simp only [if_true]; rw [dif_pos (by omega)]
    · rw [if_neg hk]
      split <;> split <;> first | rfl | omega | (congr 1; omega)

/-- The loop from trip `j` binds `y` to `ws`, and changes no variable other than `y`, the
    counter `i` and the element variable `x`. The values `ws` are those of `body` in `ρb`,
    which agrees with `ρ` on the variables the body reads other than `p`. -/
theorem loop_run (hbi : ArrayOps bi) (y s i x p : String) (body : ImpExpr)
    (hpure : isPure body = true) (fuel₀ : Nat) (ρ ρb : Env) (vs ws : List Value)
    (hlen : ws.length = vs.length)
    (hvals : ∀ (j : Nat) (h : j < vs.length) (h' : j < ws.length),
      ((denote' bi fuel₀ body).run (ρb.extend p vs[j])).1 = .val ws[j] ∧
        ws[j].isControlFlow = false)
    (hρb : ∀ z, z ∈ pureVars body → z ≠ p → ρ z = ρb z)
    (hcfv : ∀ (j : Nat) (h : j < vs.length), vs[j].isControlFlow = false)
    (hρs : ρ s = some (.array vs)) (hsy : s ≠ y) (hsi : s ≠ i) (hsx : s ≠ x)
    (hxi : x ≠ i) (hxy : x ≠ y) (hiy : i ≠ y)
    (hread : ∀ z, z ∈ pureVars body → z ≠ p → z ≠ y ∧ z ≠ i ∧ z ≠ x) :
    ∀ (m j f : Nat) (E : Env), j + m = vs.length → m ≤ f →
      (∀ z, z ≠ y → z ≠ i → z ≠ x → E z = ρ z) →
      E y = some (.array (ws.take j ++ vs.drop j)) →
      ∃ E', (denoteForLoop' bi f i j vs.length
          (.letBind x (.app "index" [.var s, .var i])
            (.letBind y (.app "array_update" [.var y, .var i, subst [p] [.var x] body])
              .unitVal))).run E = (.val .unit, E') ∧
        (∀ z, z ≠ y → z ≠ i → z ≠ x → E' z = ρ z) ∧ E' y = some (.array ws) := by
  intro m
  induction m with
  | zero =>
    intro j f E hj _ hE hEy
    refine ⟨E, forLoop_ge_run bi f i j vs.length _ E (by omega), hE, ?_⟩
    rw [hEy]
    have : j = ws.length := by omega
    subst this
    simp [← hlen]
  | succ m ih =>
    intro j f E hj hf hE hEy
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hjn : j < vs.length := by omega
    have hjw : j < ws.length := by omega
    rw [forLoop_succ_run bi f' i j vs.length _ E (by omega)]
    have hs1 : (E.extend i (.int j)) s = some (.array vs) := by
      simp only [Env.extend, beq_iff_eq, hsi, if_false]
      exact (hE s hsy hsi hsx).trans hρs
    have hi1 : (E.extend i (.int j)) i = some (.int j) := Env.extend_same _ _ _
    have hy1 : (E.extend i (.int j)) y = some (.array (ws.take j ++ vs.drop j)) := by
      simp only [Env.extend, beq_iff_eq, Ne.symm hiy, if_false]
      exact hEy
    have hvar : ∀ z, z ∈ pureVars body →
        (denote' bi (f' + 1) ((argFor [p] [.var x] z).getD (.var z))).run
            ((E.extend i (.int j)).extend x vs[j]) =
          (((denote' bi fuel₀ (.var z)).run (ρb.extend p vs[j])).1,
            (E.extend i (.int j)).extend x vs[j]) := by
      intro z hz
      by_cases hzp : z = p
      · subst hzp
        simp only [argFor, if_true, Option.getD_some, var_run, Env.extend_same]
      · obtain ⟨h1, h2, h3⟩ := hread z hz hzp
        simp only [argFor, hzp, if_false, Option.getD_none, var_run]
        have : ((E.extend i (.int j)).extend x vs[j]) z = (ρb.extend p vs[j]) z := by
          simp only [Env.extend, beq_iff_eq, h3, h2, hzp, if_false]
          exact (hE z h1 h2 h3).trans (hρb z hz hzp)
        rw [this]
        cases (ρb.extend p vs[j]) z <;> rfl
    have hsub := subst_run bi [p] [.var x] (f' + 1) fuel₀ ((E.extend i (.int j)).extend x vs[j])
      (ρb.extend p vs[j]) body hpure hvar
    simp only [InlineLocalClosures.SubstRun, (hvals j hjn hjw).1] at hsub
    rw [trip_run bi hbi y s i x _ (f' + 1) _ vs (ws.take j ++ vs.drop j) j ws[j] hs1 hi1 hy1 hjn
      (by simp; omega) (hcfv j hjn) hxi hxy hsub (hvals j hjn hjw).2]
    simp only
    have hcast : (j : Int) + 1 = ((j + 1 : Nat) : Int) := by omega
    rw [hcast, take_append_drop_set ws vs j hlen hjw]
    refine ih (j + 1) f' _ (by omega) (by omega) (fun z hz1 hz2 hz3 => ?_) (Env.extend_same _ _ _)
    simp only [Env.extend, beq_iff_eq, hz1, hz2, hz3, if_false]
    exact hE z hz1 hz2 hz3

/-- **The loop.** When the reference array is defined, the loop ends normally, in an
    environment that agrees off `i`, `x` and `n` with `ρ` extended at `y` by the array. -/
theorem mapStmt_run (hbi : ArrayOps bi) (y s i x n p : String) (body : ImpExpr)
    (hpure : isPure body = true) (fuel : Nat) (ρ : Env) (ws : List Value)
    (hmap : mapArray bi fuel ρ s p body = some ws)
    (hsy : s ≠ y) (hsi : s ≠ i) (hsx : s ≠ x) (hxi : x ≠ i) (hxy : x ≠ y) (hiy : i ≠ y)
    (hsn : s ≠ n) (hny : n ≠ y)
    (hread : ∀ z, z ∈ pureVars body → z ≠ p →
      z ≠ y ∧ z ≠ i ∧ z ≠ x ∧ z ≠ n) :
    ∃ E', (denote' bi fuel (mapStmt y s i x n (subst [p] [.var x] body))).run ρ =
        (.val .unit, E') ∧
      ∀ z, z ≠ i → z ≠ x → z ≠ n → E' z = (ρ.extend y (.array ws)) z := by
  simp only [mapArray] at hmap
  split at hmap
  case h_2 => cases hmap
  rename_i vs hρs
  split at hmap
  case isFalse => cases hmap
  rename_i hcond
  obtain ⟨hfuel, hall⟩ := hcond
  obtain ⟨hlen, hvals⟩ := mapVals_spec bi fuel ρ p body vs ws hmap
  have hcfv : ∀ (j : Nat) (h : j < vs.length), vs[j].isControlFlow = false := by
    intro j h
    have := List.all_eq_true.mp hall vs[j] (List.getElem_mem h)
    simpa using this
  simp only [mapStmt]
  rw [letBind_run, app_run, args_cons_run, var_run, hρs]
  simp only [args_nil_run, Option.map_some, hbi.len]
  generalize hρ1 : ρ.extend n (.uint .wsize vs.length) = ρ1
  have hρ1s : ρ1 s = some (.array vs) := by
    rw [← hρ1]; simp only [Env.extend, beq_iff_eq, hsn, if_false]; exact hρs
  have hρ1n : ρ1 n = some (.uint .wsize vs.length) := by
    rw [← hρ1]; exact Env.extend_same _ _ _
  rw [seq_run, letBind_run, var_run, hρ1s]
  simp only [unitVal_run]
  have hn0 : (ρ1.extend y (.array vs)) n = some (.uint .wsize vs.length) := by
    simp only [Env.extend, beq_iff_eq, hny, if_false, hρ1n]
  have hff : ∀ (B : ImpExpr), (denote' bi fuel (.forFold i (.lit (.int 0))
      (.var n) B)).run (ρ1.extend y (.array vs)) =
      (denoteForLoop' bi fuel i 0 vs.length B).run (ρ1.extend y (.array vs)) := by
    intro B
    simp only [denote', StateT.run, bind, StateT.bind, pure, StateT.pure, get, getThe,
      MonadStateOf.get, StateT.get, Value.ofLit, hn0]
  rw [hff]
  obtain ⟨E', hrun, hE', hEy⟩ := loop_run bi hbi y s i x p body hpure fuel ρ1 ρ vs ws hlen
    hvals
    (fun z hz hzp => by
      rw [← hρ1]; simp only [Env.extend, beq_iff_eq, (hread z hz hzp).2.2.2, if_false])
    hcfv hρ1s hsy hsi hsx hxi hxy hiy (fun z hz hzp => by
      obtain ⟨h1, h2, h3, _⟩ := hread z hz hzp; exact ⟨h1, h2, h3⟩)
    vs.length 0 fuel (ρ1.extend y (.array vs)) (by omega)
    hfuel (fun z hz _ _ => by simp only [Env.extend, beq_iff_eq, hz, if_false])
    (by simp)
  refine ⟨E', by simpa using hrun, fun z hzi hzx hzn => ?_⟩
  by_cases hzy : z = y
  · subst hzy; rw [hEy, Env.extend_same]
  · rw [hE' z hzy hzi hzx, ← hρ1]
    simp only [Env.extend, beq_iff_eq, hzy, hzn, if_false]

end Trip

/-! ## The statement spine -/

/-- The array variable, parameter and body of `collect (map (iter (var s)) (lam [p] body))`. -/
def mapSite? : ImpExpr → Option (String × String × ImpExpr)
  | .app "collect" [.app "map" [.app "iter" [.var s], .lam [p] body]] => some (s, p, body)
  | _ => none

/-- The counter of the loop that binds `y`. -/
def mapI (y : String) : String := "_mapi_" ++ y

/-- The element variable of the loop that binds `y`. -/
def mapX (y : String) : String := "_mapx_" ++ y

/-- The length variable of the loop that binds `y`. -/
def mapN (y : String) : String := "_mapn_" ++ y

/-- The binding of `y` to the map of `body` over `s` before the continuation `k` is
    rewritten: `body` is pure, the names `s`, `y`, `mapI y`, `mapX y` and `mapN y` are
    distinct, the body reads none of the last four except as its parameter `p`, and `k`
    reads none of the last three and contains no `match_`. -/
def mapOk (y s p : String) (body k : ImpExpr) : Bool :=
  isPure body && s != y && s != mapI y && s != mapX y && s != mapN y && mapX y != mapI y &&
    mapX y != y && mapI y != y && mapN y != mapI y && mapN y != mapX y && mapN y != y &&
    (pureVars body).all
      (fun z => z == p || (z != y && z != mapI y && z != mapX y && z != mapN y)) &&
    frameOk (fun z => z != mapI y && z != mapX y && z != mapN y) (fun _ => true)
      (fun _ => true) k

/-- Every `map` binding of `mapOk` on the statement spine (`letBind` and `seq`) rewritten
    to its loop, innermost first. -/
def inlineMaps : ImpExpr → ImpExpr
  | .letBind y v k =>
    match mapSite? v with
    | some (s, p, body) =>
      if mapOk y s p body (inlineMaps k) then
        .seq (mapStmt y s (mapI y) (mapX y) (mapN y) (subst [p] [.var (mapX y)] body))
          (inlineMaps k)
      else .letBind y v (inlineMaps k)
    | none => .letBind y v (inlineMaps k)
  | .seq a b => .seq a (inlineMaps b)
  | e => e

/-- The counter, element and length variables of the loops `inlineMaps` introduces. -/
def mapW : ImpExpr → List String
  | .letBind y v k =>
    match mapSite? v with
    | some (s, p, body) =>
      if mapOk y s p body (inlineMaps k) then mapI y :: mapX y :: mapN y :: mapW k
      else mapW k
    | none => mapW k
  | .seq _ b => mapW b
  | _ => []

/-- The reference reading of a function body: along the statement spine a `map` binding
    of `mapOk` binds `y` to `mapArray`, and every other expression is read by `denote'`. -/
def denoteMapSpine (bi : Builtins) (fuel : Nat) : ImpExpr → StateM Env Outcome
  | .letBind y v k =>
    match mapSite? v with
    | some (s, p, body) =>
      if mapOk y s p body (inlineMaps k) then do
        let ρ ← get
        match mapArray bi fuel ρ s p body with
        | some ws => do set (ρ.extend y (.array ws)); denoteMapSpine bi fuel k
        | none => pure (.err "map")
      else do
        let rv ← denote' bi fuel v
        match rv with
        | .val (.controlFlow isBreak w) => pure (.val (.controlFlow isBreak w))
        | .val w => do modify (Env.extend · y w); denoteMapSpine bi fuel k
        | other => pure other
    | none => do
      let rv ← denote' bi fuel v
      match rv with
      | .val (.controlFlow isBreak w) => pure (.val (.controlFlow isBreak w))
      | .val w => do modify (Env.extend · y w); denoteMapSpine bi fuel k
      | other => pure other
  | .seq a b => do
    let r ← denote' bi fuel a
    match r with
    | .val (.controlFlow isBreak w) => pure (.val (.controlFlow isBreak w))
    | .val _ => denoteMapSpine bi fuel b
    | other => pure other
  | e => denote' bi fuel e

/-- The source, parameter and body of `collect (map (iter src) (lam [p] body))`. -/
def mapSrc? : ImpExpr → Option (ImpExpr × String × ImpExpr)
  | .app "collect" [.app "map" [.app "iter" [src], .lam [p] body]] => some (src, p, body)
  | _ => none

/-- The variable that holds the source array of the `map` bound to `y`. -/
def mapS (y : String) : String := "_maps_" ++ y

/-- Every `map` binding on the statement spine whose source is not a variable preceded by
    a binding of the source to `mapS y`, the map reading that variable. -/
def nameMapSources : ImpExpr → ImpExpr
  | .letBind y v k =>
    match mapSrc? v with
    | some (.var _, _, _) => .letBind y v (nameMapSources k)
    | some (src, p, body) =>
      .letBind (mapS y) src
        (.letBind y (.app "collect" [.app "map" [.app "iter" [.var (mapS y)], .lam [p] body]])
          (nameMapSources k))
    | none => .letBind y v (nameMapSources k)
  | .seq a b => .seq a (nameMapSources b)
  | e => e

/-- The rewriting: sources named, then every `map` binding of `mapOk` on the spine
    rewritten to its loop. -/
def inlineMapClosures (e : ImpExpr) : ImpExpr := inlineMaps (nameMapSources e)

/-- **The spine.** From one environment, every run of the reference reading
    `denoteMapSpine bi fuel e` that does not end in an error is matched by the run of
    `inlineMaps e` read with `bi`, the final environments agreeing off `mapW e`. -/
theorem denote'_inlineMaps (bi : Builtins) (fuel : Nat) (hbi : ArrayOps bi) (e : ImpExpr) :
    RefR (fun e₁ e₂ => e₁ = e₂) (EqOff (mapW e)) IsErr (denote' bi fuel (inlineMaps e))
      (denoteMapSpine bi fuel e) := by
  induction e using ImpExpr.ind with
  | letBind y v k _ ihk =>
    cases hv : mapSite? v with
    | some t =>
      obtain ⟨s, p, body⟩ := t
      cases hok : mapOk y s p body (inlineMaps k) with
      | true =>
        simp only [inlineMaps, denoteMapSpine, mapW, hv, hok, if_true]
        intro env _ heq o s₂ hr ho
        subst heq
        simp only [mapOk, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true,
          Bool.or_eq_true, beq_iff_eq] at hok
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpure, hsy⟩, hsi⟩, hsx⟩, hsn⟩, hxi⟩, hxy⟩, hiy⟩, -⟩, -⟩,
          hny⟩, hread⟩, hframe⟩ := hok
        cases hm : mapArray bi fuel env s p body with
        | none =>
          simp only [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
            pure, StateT.pure, hm] at hr
          cases hr
          exact absurd ⟨_, rfl⟩ ho
        | some ws =>
          have hr' : (denoteMapSpine bi fuel k).run (env.extend y (.array ws)) = (o, s₂) := by
            simp only [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
              pure] at hr
            rw [hm] at hr
            exact hr
          obtain ⟨E', hrun, hE'⟩ := mapStmt_run bi hbi y s (mapI y) (mapX y) (mapN y) p body
            hpure fuel env ws hm hsy hsi hsx hxi hxy hiy hsn hny (fun z hz hzp => by
              rcases hread z hz with h | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
              · exact absurd h hzp
              · exact ⟨h1, h2, h3, h4⟩)
          obtain ⟨s₁', h1, hQ⟩ := ihk (env.extend y (.array ws)) _ rfl o s₂ hr' ho
          have hfr := denote'_frame (R := EqOff [mapI y, mapX y, mapN y]) (bi₁ := bi)
            (bi₂ := bi) id (fun z => z != mapI y && z != mapX y && z != mapN y) (fun _ => true)
            (fun _ => true)
            (fun e₁ e₂ z h hz => by
              simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hz
              exact h z (by simp [hz.1.1, hz.1.2, hz.2]))
            (fun e₁ e₂ n w h _ z hz => by
              simp only [Env.extend]
              split
              · rfl
              · exact h z hz)
            (fun _ _ => rfl) (inlineMaps k) hframe fuel
          rw [renameReads_id _ (frameOk_mono (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
            _ hframe)] at hfr
          obtain ⟨s₁, h2, hR⟩ := hfr E' (env.extend y (.array ws))
            (fun z hz => by
              simp only [List.contains_cons, List.contains_nil, Bool.or_false,
                Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hz
              exact hE' z hz.1 hz.2.1 hz.2.2) o s₁' h1 ho
          refine ⟨s₁, ?_, fun z hz => ?_⟩
          · rw [seq_run, hrun]; exact h2
          · simp only [List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
              ne_eq] at hz
            rw [hR z (by simp [hz.1, hz.2.1, hz.2.2.1]), hQ z hz.2.2.2]
      | false =>
        simp only [inlineMaps, denoteMapSpine, mapW, hv, hok, Bool.false_eq_true, if_false,
          denote']
        refine RefR.bind (badα := IsErr) (RefR.refl _) (fun o _ => ?_)
          (fun a ha s => by obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨m, rfl⟩)
        rcases o with w | _ | _ | _ | _
        · cases w <;> dsimp only <;>
            first
              | exact RefR.pure_mono _ (EqOff.of_eq _)
              | exact RefR.modify_mono (fun _ _ h => h ▸ rfl) (fun _ => ihk)
        all_goals (dsimp only; exact RefR.pure_mono _ (EqOff.of_eq _))
    | none =>
      simp only [inlineMaps, denoteMapSpine, mapW, hv, denote']
      refine RefR.bind (badα := IsErr) (RefR.refl _) (fun o _ => ?_)
        (fun a ha s => by obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨m, rfl⟩)
      rcases o with w | _ | _ | _ | _
      · cases w <;> dsimp only <;>
          first
            | exact RefR.pure_mono _ (EqOff.of_eq _)
            | exact RefR.modify_mono (fun _ _ h => h ▸ rfl) (fun _ => ihk)
      all_goals (dsimp only; exact RefR.pure_mono _ (EqOff.of_eq _))
  | seq a b _ ihb =>
    simp only [inlineMaps, denoteMapSpine, mapW, denote']
    refine RefR.bind (badα := IsErr) (RefR.refl _) (fun o _ => ?_)
      (fun a ha s => by obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨m, rfl⟩)
    rcases o with w | _ | _ | _ | _
    · cases w <;> dsimp only <;>
        first | exact RefR.pure_mono _ (EqOff.of_eq _) | exact ihb
    all_goals (dsimp only; exact RefR.pure_mono _ (EqOff.of_eq _))
  | _ =>
    simp only [inlineMaps, denoteMapSpine, mapW]
    exact (RefR.refl _).mono (fun _ _ h => h) (EqOff.of_eq _)

/-- `inlineMapClosures e` read with `bi` refines the reference reading of `e`, which is
    `denoteMapSpine` of `e` with its `map` sources named, the final environments agreeing
    off the counter, element and length variables of the loops. -/
theorem denote'_inlineMapClosures (bi : Builtins) (fuel : Nat) (hbi : ArrayOps bi)
    (e : ImpExpr) :
    RefR (fun e₁ e₂ => e₁ = e₂) (EqOff (mapW (nameMapSources e))) IsErr
      (denote' bi fuel (inlineMapClosures e)) (denoteMapSpine bi fuel (nameMapSources e)) :=
  denote'_inlineMaps bi fuel hbi _

end Hax.InlineMap
