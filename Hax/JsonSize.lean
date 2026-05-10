/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean.Data.Json
import Lean.Data.Json.FromToJson

/-!
# Json structural-size measure (Path A foundation)

Provides `jsonSize : Json → Nat` and the strict-decrease lemmas used as
termination measures when converting `Hax.HaxAdapter.parseHaxExpr` from
`partial def` to `def`.

This file is a *split* of the original Path-A foundations that previously
lived in `Hax/AdapterRefinement.lean`. We extract them here so that
`Hax/HaxAdapter.lean` (the parser) can import the lemmas without creating
a circular import (`AdapterRefinement` already imports `HaxAdapter`).

## Contents

* `jsonSize` — `@[reducible] noncomputable def jsonSize := sizeOf`
* `jsonSize_arr_lt` / `jsonSize_lt_of_mem_arr` — every array element
  strictly decreases the measure.
* `jsonSize_obj_value_lt` — every value extracted via the underlying
  `Std.TreeMap.Raw.get?` strictly decreases the measure.
* `JsonObjGet` / `JsonObjGet_decreases` — `Option`-shape variant of
  `Json.getObjVal?`; convenient for refinement statements.
* `JsonContents` / `JsonContents_decreases` — specialization to the
  hax `"contents"` field.
* `getObjVal?_decreases` — the canonical strict-decrease lemma matching
  the parser's `do`-block use of `← j.getObjVal? k`.
* `getObjValAs?_arr_mem_decreases` — strict decrease of every element of
  an `Array Json` retrieved via `j.getObjValAs? (Array Json) k`.
-/

namespace Hax.JsonSize

open Lean (Json)

/-- AST node count for a JSON value. Used as a termination / induction
    measure on the JSON sub-tree. Defined via `sizeOf`. -/
@[reducible] noncomputable def jsonSize (j : Json) : Nat := sizeOf j

/-- Every element of an `arr` strictly decreases the AST measure. -/
theorem jsonSize_arr_lt (xs : Array Json) (j : Json) (h : j ∈ xs) :
    jsonSize j < jsonSize (Json.arr xs) := by
  unfold jsonSize
  have h1 : sizeOf j < sizeOf xs := Array.sizeOf_lt_of_mem h
  decreasing_trivial

/-- Membership-shaped restatement of `jsonSize_arr_lt`. -/
theorem jsonSize_lt_of_mem_arr {xs : Array Json} {j : Json} (h : j ∈ xs) :
    jsonSize j < jsonSize (.arr xs) :=
  jsonSize_arr_lt xs j h

/-- Auxiliary: the value returned by `Const.get?` is strictly smaller
    (in `sizeOf`) than the tree it was found in. Proved by induction on
    the underlying `Impl` tree. -/
private theorem sizeOf_lt_of_const_get?_eq_some
    {t : Std.DTreeMap.Internal.Impl String (fun _ => Json)}
    {k : String} {w : Json}
    (h : Std.DTreeMap.Internal.Impl.Const.get? t k = some w) :
    sizeOf w < sizeOf t := by
  induction t with
  | leaf =>
    simp [Std.DTreeMap.Internal.Impl.Const.get?] at h
  | inner sz k' v' l r ihl ihr =>
    simp only [Std.DTreeMap.Internal.Impl.Const.get?] at h
    split at h
    · have hl := ihl h
      have hLT : sizeOf l < sizeOf (Std.DTreeMap.Internal.Impl.inner sz k' v' l r) := by
        decreasing_trivial
      omega
    · have hr := ihr h
      have hLT : sizeOf r < sizeOf (Std.DTreeMap.Internal.Impl.inner sz k' v' l r) := by
        decreasing_trivial
      omega
    · have hvw : v' = w := by
        have := h
        simp at this
        exact this
      subst hvw
      have hLT : sizeOf v' < sizeOf (Std.DTreeMap.Internal.Impl.inner sz k' v' l r) := by
        decreasing_trivial
      exact hLT

/-- Strict-decrease for `obj`-value extraction. -/
theorem jsonSize_obj_value_lt {kvs : Std.TreeMap.Raw String Json}
    {k : String} {v : Json} (h : kvs.get? k = some v) :
    jsonSize v < jsonSize (.obj kvs) := by
  unfold jsonSize
  have h' : Std.DTreeMap.Internal.Impl.Const.get? kvs.inner.inner k = some v := h
  have h1 : sizeOf v < sizeOf kvs.inner.inner :=
    sizeOf_lt_of_const_get?_eq_some h'
  have step1 : sizeOf kvs.inner = 1 + sizeOf kvs.inner.inner := by
    cases kvs.inner; rfl
  have step2 : sizeOf kvs = 1 + sizeOf kvs.inner := by
    cases kvs; rfl
  have step3 : sizeOf kvs < sizeOf (Json.obj kvs) := by decreasing_trivial
  omega

/-- `Option`-shape lookup, used by `JsonRefines*` relations. -/
def JsonObjGet (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok v => some v
  | _ => none

/-- The contents-payload of a hax `Decorated<ExprKind>` JSON node. -/
def JsonContents (j : Json) : Option Json := JsonObjGet j "contents"

/-- Strict-decrease for `JsonObjGet`. -/
theorem JsonObjGet_decreases (j : Json) (k : String) (j' : Json)
    (h : JsonObjGet j k = some j') :
    jsonSize j' < jsonSize j := by
  cases j with
  | null   => simp [JsonObjGet, Json.getObjVal?] at h
  | bool _ => simp [JsonObjGet, Json.getObjVal?] at h
  | num _  => simp [JsonObjGet, Json.getObjVal?] at h
  | str _  => simp [JsonObjGet, Json.getObjVal?] at h
  | arr _  => simp [JsonObjGet, Json.getObjVal?] at h
  | obj kvs =>
    simp only [JsonObjGet, Json.getObjVal?] at h
    cases hg : kvs.get? k with
    | none =>
      rw [hg] at h; simp at h
    | some v =>
      rw [hg] at h
      simp [pure, Except.pure] at h
      subst h
      exact jsonSize_obj_value_lt hg

/-- Strict-decrease for `JsonContents` (lookup of the `"contents"` field). -/
theorem JsonContents_decreases (j j' : Json)
    (h : JsonContents j = some j') :
    jsonSize j' < jsonSize j :=
  JsonObjGet_decreases j "contents" j' h

/-- Strict-decrease for the parser's actual `getObjVal?` use.

    When `j.getObjVal? k = .ok j'`, the underlying `kvs.get? k` returned
    `some j'` (only branch that yields `.ok`), and `jsonSize_obj_value_lt`
    applies. -/
theorem getObjVal?_decreases {j : Json} {k : String} {j' : Json}
    (h : j.getObjVal? k = .ok j') :
    jsonSize j' < jsonSize j := by
  cases j with
  | null   => simp [Json.getObjVal?] at h
  | bool _ => simp [Json.getObjVal?] at h
  | num _  => simp [Json.getObjVal?] at h
  | str _  => simp [Json.getObjVal?] at h
  | arr _  => simp [Json.getObjVal?] at h
  | obj kvs =>
    simp only [Json.getObjVal?] at h
    cases hg : kvs.get? k with
    | none =>
      rw [hg] at h; simp at h
    | some v =>
      rw [hg] at h
      simp [pure, Except.pure] at h
      subst h
      exact jsonSize_obj_value_lt hg

/-! ### Chained and `getObjValAs?`-based decreases -/

open Lean (FromJson)

/-- Two-step chain decrease: if `j.getObjVal? k1 = .ok data` and
    `data.getObjVal? k2 = .ok v`, then `jsonSize v < jsonSize j`.

    Used by `parseHaxExpr` when destructuring nested kind/contents pairs:
    `let kind ← j.getObjVal? "kind"; let v ← kind.getObjVal? "Inner"`. -/
theorem getObjVal?_chain_decreases {j data v : Json} {k1 k2 : String}
    (h1 : j.getObjVal? k1 = .ok data)
    (h2 : data.getObjVal? k2 = .ok v) :
    jsonSize v < jsonSize j :=
  Nat.lt_trans (getObjVal?_decreases h2) (getObjVal?_decreases h1)

/-- Auxiliary: `Array.fromJson?` at type `Array Json` is the identity on
    `Json.arr` payloads. The `FromJson` instance for `Json` is `Except.ok`,
    so `a.mapM Except.ok = Except.ok a`. -/
private theorem array_fromJson?_arr_id (a : Array Json) :
    (Array.fromJson? (α := Json) (Json.arr a)) = .ok a := by
  -- `Array.fromJson?` on `.arr a` reduces to `a.mapM fromJson?`.
  -- The `FromJson Json` instance is `⟨Except.ok⟩`, so `fromJson? = Except.ok`.
  -- `mapM (pure ∘ id)` on an array equals `pure (a.map id) = pure a`.
  show a.mapM (m := Except String) (fun x => Except.ok x) = .ok a
  have : a.mapM (m := Except String) (pure <| id ·) = pure (a.map id) :=
    Array.mapM_pure
  simpa using this

/-- Strict decrease for every element of an `Array Json` retrieved via
    `j.getObjValAs? (Array Json) k`.

    Concretely: if `j.getObjValAs? (Array Json) k = .ok arr` and `x ∈ arr`,
    then `jsonSize x < jsonSize j`. The proof unfolds `getObjValAs?` to
    extract a `Json.arr` from the `getObjValD k` lookup and then composes
    `getObjVal?_decreases` with `jsonSize_lt_of_mem_arr`. -/
theorem getObjValAs?_arr_mem_decreases {j : Json} {k : String}
    {arr : Array Json} {x : Json}
    (hk : j.getObjValAs? (Array Json) k = .ok arr)
    (hx : x ∈ arr) :
    jsonSize x < jsonSize j := by
  -- Unfold `getObjValAs?`: it is `fromJson? <| j.getObjValD k`.
  -- `getObjValD` is `(j.getObjVal? k).toOption.getD null`.
  simp only [Lean.Json.getObjValAs?, Lean.Json.getObjValD] at hk
  -- Case-split on whether `getObjVal? k` succeeded.
  cases hg : j.getObjVal? k with
  | error e =>
    -- Then `getObjValD = null`, and `Array.fromJson? Json.null = .error _`,
    -- contradicting `hk`.
    rw [hg] at hk
    -- hk : Lean.fromJson? ((Except.error e).toOption.getD .null) = .ok arr
    -- which simplifies to `Lean.fromJson? .null = .ok arr` for `Array Json`.
    simp only [Except.toOption, Option.getD] at hk
    -- hk : Lean.fromJson? (α := Array Json) .null = .ok arr
    -- The `FromJson (Array Json)` instance is `Array.fromJson?`, which
    -- throws on `.null`.
    exact (by
      have : (Lean.fromJson? (α := Array Json) Json.null) = Array.fromJson? .null := rfl
      rw [this] at hk
      simp [Array.fromJson?] at hk)
  | ok val =>
    rw [hg] at hk
    simp only [Except.toOption, Option.getD] at hk
    -- hk : Lean.fromJson? (α := Array Json) val = .ok arr
    have hk' : Array.fromJson? (α := Json) val = .ok arr := hk
    -- Case on the shape of `val`: only `.arr a` succeeds.
    cases val with
    | arr a =>
      rw [array_fromJson?_arr_id] at hk'
      have ha : a = arr := by injection hk'
      subst ha
      -- Now `j.getObjVal? k = .ok (.arr a)` and `x ∈ a`.
      have h1 : jsonSize (Json.arr a) < jsonSize j := getObjVal?_decreases hg
      have h2 : jsonSize x < jsonSize (Json.arr a) := jsonSize_lt_of_mem_arr hx
      exact Nat.lt_trans h2 h1
    | null => simp [Array.fromJson?] at hk'
    | bool _ => simp [Array.fromJson?] at hk'
    | num _ => simp [Array.fromJson?] at hk'
    | str _ => simp [Array.fromJson?] at hk'
    | obj _ => simp [Array.fromJson?] at hk'

end Hax.JsonSize
