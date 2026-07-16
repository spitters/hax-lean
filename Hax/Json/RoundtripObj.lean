/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

import Hax.Json.Roundtrip
import Std.Data.TreeMap

set_option autoImplicit false

/-!
# JSON Object Roundtrip — task B5, gap 4

The base roundtrip development (`Hax.Json.Roundtrip`) renders `obj` as the
placeholder `{}` (its contents are dropped) and scopes its proof to the
`Simple` fragment (`null` / `bool` / `arr`). This file lifts the object gap:
it defines a serializer that **emits object contents** (key / `:` / value /
`,` tokens) and proves the corresponding parser-inversion roundtrip.

## Why the roundtrip is *modulo canonicalization*

`Lean.Json.obj` stores a `Std.TreeMap.Raw String Json compare`, and the parser
rebuilds objects via `Json.mkObj = Json.obj ∘ (Std.TreeMap.Raw.ofList · compare)`.
A structural roundtrip `parse (serializeObj (.obj t)) = .ok (.obj t)` therefore
requires

  `Std.TreeMap.Raw.ofList (t.toList) compare = t`   (canonicalisation idempotency)

which is **false** for a general `t`: two trees with the same key/value content
but different internal shape have the same `toList` yet are not structurally
equal, and `ofList` always produces the one canonical shape. The Std library
does not even offer a structural `ofList (toList t) = t` lemma — the correct
notion is the *extensional* `Std.TreeMap.Raw.Equiv` (`~m`), characterised by
`equiv_iff_toList_perm : t₁ ~m t₂ ↔ t₁.toList.Perm t₂.toList`. There is no
`toList_ofList` structural lemma; `toList_eq` only recovers list equality from
`Equiv` **plus well-formedness**. See the `Canonicalization findings` section
below.

The honest, provable statement is therefore roundtrip **to the canonical form**:

  `parse (toTokensObj (.obj t)) = .ok (canonObj (.obj t))`

where `canonObj (.obj t) = Json.mkObj t.toList = .obj (ofList t.toList compare)`
is the tree re-canonicalised through `ofList ∘ toList`. This is a genuine
parser-inversion theorem exercising the full `parseObjectBody` recursion (key,
colon, value, comma handling, trailing-comma rejection), not a placeholder.

## Scope of the proof

* We work at the **token / parser** level (`parse (toTokensObj j) = …`), not the
  full string pipeline (`tokenize (serializeObj j)`). The tokenizer half is
  blocked for objects by an *independent* wall documented in `Roundtrip.lean`:
  keys are `strT` tokens, and re-lexing `serialize (strT k)` requires
  `takeString` correctness over an arbitrary (escaped) key body — the same
  unsolved `str` leaf. A concrete full-pipeline object instance is corroborated
  by `native_decide` at the end of the file.
* Object **values** are taken from the `Simple` fragment (`null` / `bool` /
  `arr` of `Simple`); this reuses `Roundtrip.parseValue_toTokens` for the
  per-value inversion. Nested objects as values are out of scope for the proof
  (they would need a mutual recursion whose termination goes through
  `TreeMap.Raw.toList`, for which Std exposes no `sizeOf` member lemma). The
  serializer `toTokensObj` is nevertheless *total* over all of `Lean.Json`.
-/

namespace Hax.Json.RoundtripObj

open Hax.Json.Lexer
open Hax.Json.Parser
open Hax.Json.Roundtrip

/-! ## Object serializer (emits contents) -/

/-- Tokens for one `(key, value)` member: `strT key`, `:`, then the value's
tokens (reusing `Roundtrip.toTokens`). -/
def toTokensKV (kv : String × Lean.Json) : List JsonToken :=
  .strT kv.1 :: .colon :: toTokens kv.2

/-- Tokens for an object given as a key/value list: `{`, comma-separated
members, `}`. -/
def toTokensObjL (kvs : List (String × Lean.Json)) : List JsonToken :=
  .lbrace :: commaSep (kvs.map toTokensKV) ++ [.rbrace]

/-- Token serialization emitting object contents. On `obj` we render the
tree's `toList`; all other constructors defer to `Roundtrip.toTokens`. -/
def toTokensObj : Lean.Json → List JsonToken
  | .obj t => toTokensObjL t.toList
  | j      => toTokens j

/-- Compact serializer that emits object contents. -/
def serializeObj (j : Lean.Json) : String :=
  String.join ((toTokensObj j).map JsonToken.serialize)

/-! ## Canonicalization

`canonObj` re-canonicalises a top-level object through `ofList ∘ toList` (the
exact normal form the parser produces). It is the identity on all other
constructors and on already-canonical objects up to `Equiv`. -/

/-- Top-level object canonicalisation: `.obj t ↦ mkObj t.toList`. -/
def canonObj : Lean.Json → Lean.Json
  | .obj t => Lean.Json.mkObj t.toList
  | j      => j

/-! ## Reduction lemmas for `parseObjectBody` -/

/-- The object-body parser step for a `strT key : value` member. Definitional. -/
theorem pob_step (key : String) (L : List JsonToken)
    (acc : List (String × Lean.Json)) (k : Nat) :
    parseObjectBody (k + 1) (.strT key :: .colon :: L) acc =
      (match parseValue k L with
       | .error e => .error e
       | .ok (v, rest') =>
         match rest' with
         | .rbrace :: rest'' => .ok (Lean.Json.mkObj ((key, v) :: acc).reverse, rest'')
         | .comma :: .rbrace :: _ => .error "trailing comma in object"
         | .comma :: rest'' => parseObjectBody k rest'' ((key, v) :: acc)
         | _ => .error "expected ',' or '}' in object") := rfl

/-- Reduce the continuation match when the tail after a value is `, th2 …` with
`th2 ≠ '}'` (a genuine next member, not a trailing comma). -/
theorem pob_comma {th2 : JsonToken} (hth2 : th2 ≠ .rbrace)
    (key : String) (v : Lean.Json) (M : List JsonToken)
    (acc : List (String × Lean.Json)) (k : Nat) :
    (match (Except.ok (v, JsonToken.comma :: th2 :: M) :
              Except String (Lean.Json × List JsonToken)) with
     | .error e => .error e
     | .ok (v, rest') =>
       match rest' with
       | .rbrace :: rest'' => .ok (Lean.Json.mkObj ((key, v) :: acc).reverse, rest'')
       | .comma :: .rbrace :: _ => .error "trailing comma in object"
       | .comma :: rest'' => parseObjectBody k rest'' ((key, v) :: acc)
       | _ => .error "expected ',' or '}' in object")
      = parseObjectBody k (th2 :: M) ((key, v) :: acc) := by
  cases th2 <;> first | exact absurd rfl hth2 | rfl

/-- `parseValue` on `lbrace :: X` opens an object body. Definitional. -/
theorem pv_lbrace (X : List JsonToken) (n : Nat) :
    parseValue (n + 1) (.lbrace :: X) = parseObjectBody n X [] := rfl

/-- Head of a nonempty comma-separated member body is `strT key :: colon :: …`. -/
theorem commaSepKV_head (kv : String × Lean.Json) (kvs : List (String × Lean.Json)) :
    ∃ r, commaSep ((kv :: kvs).map toTokensKV) = .strT kv.1 :: .colon :: r := by
  cases kvs with
  | nil => exact ⟨toTokens kv.2, rfl⟩
  | cons kv2 kvs' =>
    refine ⟨toTokens kv.2 ++ JsonToken.comma :: commaSep ((kv2 :: kvs').map toTokensKV), ?_⟩
    simp only [List.map_cons]
    rw [commaSep_cons_cons]
    rfl

/-! ## Parser inversion for an object body -/

/-- Parser inversion for a `(key, value)` list with `Simple` values: parsing the
emitted body recovers `mkObj (acc.reverse ++ kvs)`. -/
theorem parseObjectBody_toTokens :
    ∀ (kvs : List (String × Lean.Json)), (∀ kv ∈ kvs, Simple kv.2) →
    ∀ (acc : List (String × Lean.Json)) (rest : List JsonToken) (fuel : Nat),
      2 * (commaSep (kvs.map toTokensKV)).length + 2 ≤ fuel →
      parseObjectBody fuel (commaSep (kvs.map toTokensKV) ++ .rbrace :: rest) acc
        = .ok (Lean.Json.mkObj (acc.reverse ++ kvs), rest) := by
  intro kvs
  induction kvs with
  | nil =>
    intro _ acc rest fuel hf
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 :=
      ⟨fuel - 1, by simp only [List.map_nil, commaSep, List.length_nil] at hf; omega⟩
    simp only [List.map_nil, commaSep, List.nil_append, List.append_nil]
    rfl
  | cons kv kvs' ih =>
    intro hS acc rest fuel hf
    have hSkv : Simple kv.2 := hS kv (List.mem_cons_self ..)
    have hInvE := Roundtrip.parseValue_toTokens hSkv
    cases kvs' with
    | nil =>
      have hcs : commaSep (((kv :: [])).map toTokensKV) = toTokensKV kv := by
        simp only [List.map_cons, List.map_nil, commaSep]
      rw [hcs] at hf ⊢
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [toTokensKV, List.length_cons] at hf; omega⟩
      have hin : toTokensKV kv ++ JsonToken.rbrace :: rest
          = .strT kv.1 :: .colon :: (toTokens kv.2 ++ JsonToken.rbrace :: rest) := by
        simp only [toTokensKV, List.cons_append]
      rw [hin, pob_step, hInvE (JsonToken.rbrace :: rest) k (by
        simp only [toTokensKV, List.length_cons] at hf; omega)]
      simp only [List.reverse_cons]
    | cons kv2 kvs'' =>
      have hSkv2 : ∀ kv' ∈ (kv2 :: kvs''), Simple kv'.2 :=
        fun kv' hkv' => hS kv' (List.mem_cons_of_mem _ hkv')
      obtain ⟨r2, hcb2⟩ := commaSepKV_head kv2 kvs''
      have hCBeq : commaSep ((kv :: kv2 :: kvs'').map toTokensKV)
          = toTokensKV kv ++ JsonToken.comma :: commaSep ((kv2 :: kvs'').map toTokensKV) := by
        rw [List.map_cons]; exact commaSep_cons_ne (by simp)
      rw [hCBeq] at hf ⊢
      have hlen : (toTokensKV kv ++ JsonToken.comma :: commaSep ((kv2 :: kvs'').map toTokensKV)).length
          = (toTokens kv.2).length + 3 + (commaSep ((kv2 :: kvs'').map toTokensKV)).length := by
        simp only [toTokensKV, List.length_append, List.length_cons]; omega
      rw [hlen] at hf
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      have hin : (toTokensKV kv ++ JsonToken.comma :: commaSep ((kv2 :: kvs'').map toTokensKV))
                    ++ JsonToken.rbrace :: rest
          = .strT kv.1 :: .colon :: (toTokens kv.2 ++ (JsonToken.comma
              :: commaSep ((kv2 :: kvs'').map toTokensKV) ++ JsonToken.rbrace :: rest)) := by
        simp only [toTokensKV, List.cons_append, List.append_assoc]
      rw [hin, pob_step,
          hInvE (JsonToken.comma :: commaSep ((kv2 :: kvs'').map toTokensKV)
                  ++ JsonToken.rbrace :: rest) k (by omega)]
      have hr0 : (JsonToken.comma :: commaSep ((kv2 :: kvs'').map toTokensKV)
                    ++ JsonToken.rbrace :: rest)
          = JsonToken.comma :: JsonToken.strT kv2.1
              :: JsonToken.colon :: (r2 ++ JsonToken.rbrace :: rest) := by
        rw [hcb2]; rfl
      have hth2 : JsonToken.strT kv2.1 ≠ JsonToken.rbrace := by simp
      rw [hr0, pob_comma hth2]
      have hback : JsonToken.strT kv2.1 :: JsonToken.colon :: (r2 ++ JsonToken.rbrace :: rest)
          = commaSep ((kv2 :: kvs'').map toTokensKV) ++ JsonToken.rbrace :: rest := by
        rw [hcb2]; rfl
      rw [hback, ih hSkv2 ((kv.1, kv.2) :: acc) rest k (by omega)]
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

/-! ## Top-level object roundtrip (modulo canonicalization) -/

/-- `parseValue` inverts the object serializer, up to canonicalisation. -/
theorem parseValue_toTokensObj (t : Std.TreeMap.Raw String Lean.Json compare)
    (hvals : ∀ kv ∈ t.toList, Simple kv.2) :
    ∀ (rest : List JsonToken) (fuel : Nat),
      2 * (toTokensObj (.obj t)).length + 1 ≤ fuel →
      parseValue fuel (toTokensObj (.obj t) ++ rest)
        = .ok (Lean.Json.mkObj t.toList, rest) := by
  intro rest fuel hf
  have hlen : (toTokensObj (.obj t)).length
      = (commaSep (t.toList.map toTokensKV)).length + 2 := by
    simp only [toTokensObj, toTokensObjL, List.length_cons, List.length_append,
      List.length_nil]
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by rw [hlen] at hf; omega⟩
  have hshape : toTokensObj (.obj t) ++ rest
      = .lbrace :: (commaSep (t.toList.map toTokensKV) ++ JsonToken.rbrace :: rest) := by
    simp only [toTokensObj, toTokensObjL, List.cons_append, List.append_assoc,
      List.nil_append]
  rw [hshape, pv_lbrace,
      parseObjectBody_toTokens t.toList hvals [] rest n (by rw [hlen] at hf; omega)]
  simp only [List.reverse_nil, List.nil_append]

/-- **Object roundtrip modulo canonicalization.** Parsing the emitted object
tokens recovers the canonical form `canonObj (.obj t) = mkObj t.toList`. -/
theorem parse_toTokensObj (t : Std.TreeMap.Raw String Lean.Json compare)
    (hvals : ∀ kv ∈ t.toList, Simple kv.2) :
    parse (toTokensObj (.obj t)) = .ok (canonObj (.obj t)) := by
  have hpv := parseValue_toTokensObj t hvals [] (2 * (toTokensObj (.obj t)).length + 1) (by omega)
  rw [List.append_nil] at hpv
  unfold parse
  rw [hpv]
  rfl

/-! ## Canonicalization findings (task B5, gap 4, goal 3)

The weaker idempotency `ofList (toList (ofList l)) = ofList l` was investigated
and is **not structurally provable**, for the same reason the structural
roundtrip fails: `Std.TreeMap.Raw` has no `toList_ofList` / `ofList_toList`
structural lemma, and structural tree equality is the wrong notion. The Std
API only relates trees extensionally, via `Std.TreeMap.Raw.Equiv` (`~m`):

* `equiv_iff_toList_perm : t₁ ~m t₂ ↔ t₁.toList.Perm t₂.toList`
* `equiv_iff_toList_eq (h₁ : t₁.WF) (h₂ : t₂.WF) : t₁ ~m t₂ ↔ t₁.toList = t₂.toList`
* `Std.TreeMap.Raw.WF.ofList : (Raw.ofList l cmp).WF`

So the honest statement of idempotency is at the level of `~m` (equivalently,
`toList` equality **for well-formed trees**), not structural `=`. The parser
always emits a well-formed canonical tree (`ofList …`), and any object produced
by `Json.mkObj` / by this file's parser is already canonical, so on the image
of the parser `canonObj` acts as the identity up to `~m`. Establishing
`ofList (t.toList) ~m t` in general still requires a `toList`-permutation
argument (sortedness + key-distinctness of a WF tree) that Std does not package
as a reusable lemma; it is left as the residual gap. The two probes below
corroborate both facts concretely by `native_decide`. -/

/-- Full-pipeline corroboration that object **contents** are emitted (not the
`{}` placeholder): a two-member object with `Simple` values round-trips through
`serializeObj → tokenize → parse`, recovering both keys and both values in
canonical (sorted) key order. -/
def rtObjContent : Bool :=
  match tokenize (serializeObj
      (Lean.Json.mkObj [("a", Lean.Json.bool true), ("b", Lean.Json.null)])) >>= parse with
  | .ok (.obj t) =>
    match t.toList with
    | [(k1, .bool true), (k2, .null)] => k1 == "a" && k2 == "b"
    | _ => false
  | _ => false

theorem roundtrip_obj_content : rtObjContent = true := by native_decide

/-- Concrete canonicalization idempotency: feeding `mkObj` an **unsorted** member
list canonicalises it (reorders `b, a` to `a, b`), and re-canonicalising the
result through `ofList ∘ toList` is stable at the key level — the concrete
instance of the `~m`-idempotency discussed above. -/
def canonIdemKeys : Bool :=
  match Lean.Json.mkObj [("b", Lean.Json.null), ("a", Lean.Json.bool true)] with
  | .obj t =>
    (Std.TreeMap.Raw.ofList t.toList compare).toList.map Prod.fst == t.toList.map Prod.fst
      && t.toList.map Prod.fst == ["a", "b"]
  | _ => false

theorem canon_idem_keys_concrete : canonIdemKeys = true := by native_decide

end Hax.Json.RoundtripObj
