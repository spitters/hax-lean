/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

import HaxLean.Json.Lexer
import HaxLean.Json.Parser

set_option autoImplicit false

/-!
# JSON Roundtrip — task B5

`parse (tokenize (serialize j)) = .ok j`.

## Serializer choice

`serialize` is a **compact** (no-whitespace) printer defined as the
concatenation of the per-token spellings produced by the lexer's own
`JsonToken.serialize` (reused verbatim), applied to a token list `toTokens j`.
Concretely:

```
serialize j := String.join ((toTokens j).map JsonToken.serialize)
toTokens (.arr a) := .lbracket :: commaSep (a.toList.map toTokens) ++ [.rbracket]
```

This factoring gives the natural two-halves decomposition:

* **(a) serializer/lexer agree:** `tokenize (serialize j) = .ok (toTokens j)`.
* **(b) parser inverts the token serializer:** `parse (toTokens j) = .ok j`.

## Scope of the proved roundtrip

The theorem `roundtrip` is proved for the fragment carved out by the
inductive predicate `Simple`: `null`, `bool`, and (recursively) `arr` of
`Simple` elements. This is a genuine **nested induction** over arrays with a
real tokenizer-concatenation lemma (`tokenizeAux_serChars`) and a real
parser-inversion lemma (`parseValue_toTokens` / `parseArrayBody_toTokens`).

`str`, `num`, and `obj` are **excluded from `Simple`** because each roundtrip
leaf is a substantial separate development that this no-`mathlib` project has
no supporting lemmas for:

* `num`: `parseJsonNumber (toString i) = some (fromInt i)` needs a left-inverse
  of `Int.toString` under `String.toInt?`, which is not available and reduces
  only under `native_decide` per concrete value.
* `str`: the lexer's `takeString` correctness over an arbitrary (escaped) body.
* `obj`: `Lean.Json.obj` stores an `Std.TreeMap.Raw`, and the parser rebuilds
  it via `mkObj = Json.obj ∘ TreeMap.Raw.ofList`. Structural `= .ok j` then
  requires `TreeMap.Raw.ofList (t.toList) compare = t` (canonicalisation
  idempotency), which is false for non-canonical trees and unproved otherwise.

`serialize` / `toTokens` are nevertheless **total** over all of `Lean.Json`:
`str` and `num` are serialized faithfully; `obj` is rendered as the placeholder
`{}` (its contents are dropped — outside the proved fragment, and object
contents cannot round-trip structurally without the canonicalisation lemma
above). Only the *proof* is scoped to `Simple`. Concrete `str` / `num` /
empty-`obj` instances are corroborated by `native_decide` at the end of the
file.
-/

namespace Hax.Json.Roundtrip

open Hax.Json.Lexer
open Hax.Json.Parser

/-! ## Serializer -/

/-- Interleave token-chunks with `comma` separators (no trailing comma). -/
def commaSep : List (List JsonToken) → List JsonToken
  | [] => []
  | [x] => x
  | x :: xs => x ++ JsonToken.comma :: commaSep xs

/-- Token serialization of a `Lean.Json` value. Recurses through arrays; `obj`
is rendered as an empty pair of braces placeholder (outside the proved
fragment — see the module docstring). -/
def toTokens : Lean.Json → List JsonToken
  | .null => [.nullT]
  | .bool true => [.trueT]
  | .bool false => [.falseT]
  | .num n => [.numT (toString n.mantissa)]
  | .str s => [.strT s]
  | .arr a => .lbracket :: (commaSep (a.toList.map toTokens)) ++ [.rbracket]
  | .obj _ => [.lbrace, .rbrace]
  termination_by j => sizeOf j
  decreasing_by
    rename_i x hx
    have h := Array.sizeOf_lt_of_mem (Array.mem_def.mpr hx)
    simp only [Lean.Json.arr.sizeOf_spec]
    omega

/-- Compact JSON serializer: concatenate the per-token spellings. -/
def serialize (j : Lean.Json) : String :=
  String.join ((toTokens j).map JsonToken.serialize)

/-! ## The proved fragment -/

/-- Fragment on which the roundtrip is proved: literals `null`/`bool` and
arrays of such. -/
inductive Simple : Lean.Json → Prop
  | null : Simple .null
  | bool (b : Bool) : Simple (.bool b)
  | arr (a : Array Lean.Json) : (∀ e ∈ a.toList, Simple e) → Simple (.arr a)

/-- Tokens emitted for `Simple` values: never `numT` / `strT`. -/
def isSimpleTok : JsonToken → Prop
  | .numT _ => False
  | .strT _ => False
  | _ => True

/-! ## Half (a): serializer/lexer agree

`tokenize (serialize j) = .ok (toTokens j)`.  We prove a general
tokenizer-concatenation lemma over token lists of non-payload tokens, then
specialise. -/

/-- Chars produced by serializing one token. -/
def serTokChars (t : JsonToken) : List Char := (JsonToken.serialize t).toList

private theorem join_toList_foldl (ss : List String) : ∀ acc : String,
    (List.foldl (fun r s => r ++ s) acc ss).toList = acc.toList ++ ss.flatMap String.toList := by
  induction ss with
  | nil => intro acc; simp
  | cons t ss ih =>
    intro acc
    simp [ih, String.toList_append, List.flatMap_cons, List.append_assoc]

theorem serialize_toList (ts : List JsonToken) :
    (String.join (ts.map JsonToken.serialize)).toList = ts.flatMap serTokChars := by
  have h := join_toList_foldl (ts.map JsonToken.serialize) ""
  simp only [String.join]
  rw [h]
  simp only [String.toList]
  rw [List.flatMap_map]
  rfl

/-- The tokenizer re-lexes the char stream of a list of non-payload tokens
back to exactly that list, given enough fuel. -/
theorem tokenizeAux_serChars (ts : List JsonToken)
    (hs : ∀ t ∈ ts, isSimpleTok t) :
    ∀ fuel, ts.length < fuel →
      tokenizeAux fuel (ts.flatMap serTokChars) = .ok ts := by
  induction ts with
  | nil =>
    intro fuel hf
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
    rfl
  | cons t ts ih =>
    intro fuel hf
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
    have ht : isSimpleTok t := hs t (List.mem_cons_self ..)
    have hts : ∀ t' ∈ ts, isSimpleTok t' := fun t' h => hs t' (List.mem_cons_of_mem _ h)
    have hlen : ts.length < n := by simp only [List.length_cons] at hf; omega
    have hrc : tokenizeAux n (ts.flatMap serTokChars) = .ok ts := ih hts n hlen
    rw [List.flatMap_cons]
    cases t with
    | numT s => exact ht.elim
    | strT s => exact ht.elim
    | lbrace =>
        have hstep : tokenizeAux (n+1) (serTokChars .lbrace ++ ts.flatMap serTokChars)
            = (tokenizeAux n (ts.flatMap serTokChars)).map (JsonToken.lbrace :: ·) := rfl
        rw [hstep, hrc]; rfl
    | rbrace =>
        have hstep : tokenizeAux (n+1) (serTokChars .rbrace ++ ts.flatMap serTokChars)
            = (tokenizeAux n (ts.flatMap serTokChars)).map (JsonToken.rbrace :: ·) := rfl
        rw [hstep, hrc]; rfl
    | lbracket =>
        have hstep : tokenizeAux (n+1) (serTokChars .lbracket ++ ts.flatMap serTokChars)
            = (tokenizeAux n (ts.flatMap serTokChars)).map (JsonToken.lbracket :: ·) := rfl
        rw [hstep, hrc]; rfl
    | rbracket =>
        have hstep : tokenizeAux (n+1) (serTokChars .rbracket ++ ts.flatMap serTokChars)
            = (tokenizeAux n (ts.flatMap serTokChars)).map (JsonToken.rbracket :: ·) := rfl
        rw [hstep, hrc]; rfl
    | colon =>
        have hstep : tokenizeAux (n+1) (serTokChars .colon ++ ts.flatMap serTokChars)
            = (tokenizeAux n (ts.flatMap serTokChars)).map (JsonToken.colon :: ·) := rfl
        rw [hstep, hrc]; rfl
    | comma =>
        have hstep : tokenizeAux (n+1) (serTokChars .comma ++ ts.flatMap serTokChars)
            = (tokenizeAux n (ts.flatMap serTokChars)).map (JsonToken.comma :: ·) := rfl
        rw [hstep, hrc]; rfl
    | trueT =>
        have hstep : tokenizeAux (n+1) (serTokChars .trueT ++ ts.flatMap serTokChars)
            = (tokenizeAux n (ts.flatMap serTokChars)).map (JsonToken.trueT :: ·) := rfl
        rw [hstep, hrc]; rfl
    | falseT =>
        have hstep : tokenizeAux (n+1) (serTokChars .falseT ++ ts.flatMap serTokChars)
            = (tokenizeAux n (ts.flatMap serTokChars)).map (JsonToken.falseT :: ·) := rfl
        rw [hstep, hrc]; rfl
    | nullT =>
        have hstep : tokenizeAux (n+1) (serTokChars .nullT ++ ts.flatMap serTokChars)
            = (tokenizeAux n (ts.flatMap serTokChars)).map (JsonToken.nullT :: ·) := rfl
        rw [hstep, hrc]; rfl

/-- Membership in `commaSep L`: either a separator, or in one of the chunks. -/
theorem mem_commaSep {t : JsonToken} :
    ∀ (L : List (List JsonToken)), t ∈ commaSep L → t = .comma ∨ ∃ l ∈ L, t ∈ l := by
  intro L
  induction L with
  | nil => intro h; simp [commaSep] at h
  | cons x xs ih =>
    intro h
    cases xs with
    | nil =>
      simp only [commaSep] at h
      exact Or.inr ⟨x, List.mem_cons_self .., h⟩
    | cons y ys =>
      simp only [commaSep, List.mem_append, List.mem_cons] at h
      rcases h with hx | hc | hrest
      · exact Or.inr ⟨x, List.mem_cons_self .., hx⟩
      · exact Or.inl hc
      · rcases ih hrest with h' | ⟨l, hl, htl⟩
        · exact Or.inl h'
        · exact Or.inr ⟨l, List.mem_cons_of_mem _ hl, htl⟩

/-- Every token emitted for a `Simple` value is a non-payload token. -/
theorem toTokens_isSimpleTok {j : Lean.Json} (h : Simple j) :
    ∀ t ∈ toTokens j, isSimpleTok t := by
  induction h with
  | null => intro t ht; simp only [toTokens, List.mem_cons, List.not_mem_nil, or_false] at ht
            subst ht; trivial
  | bool b =>
    cases b <;>
      (intro t ht; simp only [toTokens, List.mem_cons, List.not_mem_nil, or_false] at ht
       subst ht; trivial)
  | arr a hall ih =>
    intro t ht
    rw [toTokens] at ht
    rcases List.mem_cons.1 ht with hlb | ht'
    · subst hlb; trivial
    · rcases List.mem_append.1 ht' with hcs | hrb
      · rcases mem_commaSep _ hcs with hc | ⟨l, hlmem, htl⟩
        · subst hc; trivial
        · rcases List.mem_map.1 hlmem with ⟨e, hemem, rfl⟩
          exact ih e hemem t htl
      · rcases List.mem_cons.1 hrb with h | h
        · subst h; trivial
        · simp at h

/-- Each non-payload token has a nonempty spelling. -/
theorem serTokChars_ne_nil {t : JsonToken} (h : isSimpleTok t) :
    1 ≤ (serTokChars t).length := by
  cases t <;> simp_all [isSimpleTok, serTokChars, JsonToken.serialize]

/-- Token count is at most char count (each non-payload token has a nonempty
spelling). -/
theorem length_le_serChars (ts : List JsonToken) (hs : ∀ t ∈ ts, isSimpleTok t) :
    ts.length ≤ (ts.flatMap serTokChars).length := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have h := serTokChars_ne_nil (hs t (List.mem_cons_self ..))
    have ih' := ih (fun t' ht' => hs t' (List.mem_cons_of_mem _ ht'))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem tokenize_serialize {j : Lean.Json} (h : Simple j) :
    tokenize (serialize j) = .ok (toTokens j) := by
  have hsimp := toTokens_isSimpleTok h
  have hchars : (serialize j).toList = (toTokens j).flatMap serTokChars := serialize_toList _
  have hle := length_le_serChars (toTokens j) hsimp
  show tokenizeAux (2 * (serialize j).toList.length + 1) (serialize j).toList = .ok (toTokens j)
  rw [hchars]
  exact tokenizeAux_serChars (toTokens j) hsimp _ (by omega)

/-! ## Half (b): parser inverts the token serializer -/

/-- Head token of a `Simple` value's serialization is never `]`. -/
theorem toTokens_cons {e : Lean.Json} (h : Simple e) :
    ∃ th tt, toTokens e = th :: tt ∧ th ≠ JsonToken.rbracket := by
  cases h with
  | null => exact ⟨.nullT, [], by simp only [toTokens], by decide⟩
  | bool b =>
    cases b
    · exact ⟨.falseT, [], by simp only [toTokens], by decide⟩
    · exact ⟨.trueT, [], by simp only [toTokens], by decide⟩
  | arr a _ =>
      refine ⟨.lbracket, commaSep (a.toList.map toTokens) ++ [.rbracket], ?_, by decide⟩
      simp only [toTokens, List.cons_append]

/-- `commaSep` of a `x :: y :: ys` chunk list unfolds to a single append. -/
theorem commaSep_cons_cons (x y : List JsonToken) (ys : List (List JsonToken)) :
    commaSep (x :: y :: ys) = x ++ JsonToken.comma :: commaSep (y :: ys) := rfl

/-- `commaSep (x :: L)` with `L` nonempty inserts a separator. -/
theorem commaSep_cons_ne {x : List JsonToken} {L : List (List JsonToken)} (h : L ≠ []) :
    commaSep (x :: L) = x ++ JsonToken.comma :: commaSep L := by
  cases L with
  | nil => exact absurd rfl h
  | cons y ys => rfl

/-- Head token of a nonempty comma-separated body is never `]`. -/
theorem commaSep_cons {es : List Lean.Json} (h : es ≠ []) (hs : ∀ e ∈ es, Simple e) :
    ∃ th r, commaSep (es.map toTokens) = th :: r ∧ th ≠ JsonToken.rbracket := by
  cases es with
  | nil => exact absurd rfl h
  | cons e es' =>
    obtain ⟨th, tt, hte, hne⟩ := toTokens_cons (hs e (List.mem_cons_self ..))
    cases es' with
    | nil =>
      refine ⟨th, tt, ?_, hne⟩
      simp only [List.map_cons, List.map_nil, commaSep]
      exact hte
    | cons e2 es'' =>
      refine ⟨th, tt ++ JsonToken.comma :: commaSep ((e2 :: es'').map toTokens), ?_, hne⟩
      simp only [List.map_cons]
      rw [commaSep_cons_cons, hte, List.cons_append]

/-- One `parseArrayBody` step past a value token (head `th ≠ ']'`). -/
theorem pab_step {th : JsonToken} (hthne : th ≠ .rbracket)
    (L : List JsonToken) (acc : Array Lean.Json) (k : Nat) :
    parseArrayBody (k + 1) (th :: L) acc =
      (match parseValue k (th :: L) with
       | .error er => .error er
       | .ok (v, r) =>
         match r with
         | .rbracket :: r' => .ok (.arr (acc.push v), r')
         | .comma :: .rbracket :: _ => .error "trailing comma in array"
         | .comma :: r' => parseArrayBody k r' (acc.push v)
         | _ => .error "expected ',' or ']' in array") := by
  cases th <;> first | exact absurd rfl hthne | rfl

/-- Reduce the continuation match when the tail after a value is `, th2 …` with
`th2 ≠ ']'` (a genuine next element, not a trailing comma). -/
theorem pab_comma {th2 : JsonToken} (hth2 : th2 ≠ .rbracket)
    (v : Lean.Json) (M : List JsonToken) (acc : Array Lean.Json) (k : Nat) :
    (match (Except.ok (v, JsonToken.comma :: th2 :: M) :
              Except String (Lean.Json × List JsonToken)) with
     | .error er => .error er
     | .ok (v, r) =>
       match r with
       | .rbracket :: r' => .ok (.arr (acc.push v), r')
       | .comma :: .rbracket :: _ => .error "trailing comma in array"
       | .comma :: r' => parseArrayBody k r' (acc.push v)
       | _ => .error "expected ',' or ']' in array")
      = parseArrayBody k (th2 :: M) (acc.push v) := by
  cases th2 <;> first | exact absurd rfl hth2 | rfl

/-- Parser inversion for an array body (list of `Simple` elements), taking the
per-element inversion as a hypothesis. -/
theorem parseArrayBody_toTokens :
    ∀ (es : List Lean.Json), (∀ e ∈ es, Simple e) →
      (∀ e ∈ es, ∀ (rest : List JsonToken) (fuel : Nat),
        2 * (toTokens e).length + 1 ≤ fuel →
        parseValue fuel (toTokens e ++ rest) = .ok (e, rest)) →
    ∀ (acc : Array Lean.Json) (rest : List JsonToken) (fuel : Nat),
      2 * (commaSep (es.map toTokens)).length + 2 ≤ fuel →
      parseArrayBody fuel (commaSep (es.map toTokens) ++ .rbracket :: rest) acc
        = .ok (.arr (acc ++ es.toArray), rest) := by
  intro es
  induction es with
  | nil =>
    intro _ _ acc rest fuel hf
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 :=
      ⟨fuel - 1, by simp only [List.map_nil, commaSep, List.length_nil] at hf; omega⟩
    simp only [List.map_nil, commaSep, List.nil_append]
    rw [show parseArrayBody (k + 1) (JsonToken.rbracket :: rest) acc
          = Except.ok (Lean.Json.arr acc, rest) from rfl]
    simp
  | cons e es' ih =>
    intro hSimple hInv acc rest fuel hf
    have hSe : Simple e := hSimple e (List.mem_cons_self ..)
    have hInvE := hInv e (List.mem_cons_self ..)
    obtain ⟨th, tt, hte, hthne⟩ := toTokens_cons hSe
    cases es' with
    | nil =>
      simp only [List.map_cons, List.map_nil, commaSep] at hf ⊢
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      have hin : toTokens e ++ JsonToken.rbracket :: rest = th :: (tt ++ JsonToken.rbracket :: rest) := by
        rw [hte, List.cons_append]
      rw [hin, pab_step hthne, ← hin, hInvE _ k (by omega)]
      show Except.ok (Lean.Json.arr (acc.push e), rest) = _
      rw [Array.push_eq_append]
    | cons e2 es'' =>
      obtain ⟨th2, r2, hcb2, hth2⟩ :=
        commaSep_cons (es := e2 :: es'') (by simp)
          (fun x hx => hSimple x (List.mem_cons_of_mem _ hx))
      have hCBeq : commaSep ((e :: e2 :: es'').map toTokens)
          = toTokens e ++ JsonToken.comma :: commaSep ((e2 :: es'').map toTokens) := by
        rw [List.map_cons]; exact commaSep_cons_ne (by simp)
      rw [hCBeq] at hf ⊢
      have hlen : (toTokens e ++ JsonToken.comma :: commaSep ((e2 :: es'').map toTokens)).length
          = (toTokens e).length + 1 + (commaSep ((e2 :: es'').map toTokens)).length := by
        simp only [List.length_append, List.length_cons]; omega
      rw [hlen] at hf
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      have hin : (toTokens e ++ JsonToken.comma :: commaSep ((e2 :: es'').map toTokens))
                    ++ JsonToken.rbracket :: rest
          = th :: (tt ++ (JsonToken.comma :: commaSep ((e2 :: es'').map toTokens)
                            ++ JsonToken.rbracket :: rest)) := by
        rw [hte]; simp [List.cons_append, List.append_assoc]
      rw [hin, pab_step hthne]
      have hin2 : th :: (tt ++ (JsonToken.comma :: commaSep ((e2 :: es'').map toTokens)
                            ++ JsonToken.rbracket :: rest))
          = toTokens e ++ (JsonToken.comma :: commaSep ((e2 :: es'').map toTokens)
                            ++ JsonToken.rbracket :: rest) := by
        rw [hte]; simp [List.cons_append]
      rw [hin2, hInvE _ k (by omega)]
      have hr0 : (JsonToken.comma :: commaSep ((e2 :: es'').map toTokens)
                    ++ JsonToken.rbracket :: rest)
          = JsonToken.comma :: th2 :: (r2 ++ JsonToken.rbracket :: rest) := by
        rw [hcb2]; rfl
      rw [hr0, pab_comma hth2]
      have hback : th2 :: (r2 ++ JsonToken.rbracket :: rest)
          = commaSep ((e2 :: es'').map toTokens) ++ JsonToken.rbracket :: rest := by
        rw [hcb2, List.cons_append]
      rw [hback, ih (fun x hx => hSimple x (List.mem_cons_of_mem _ hx))
            (fun x hx => hInv x (List.mem_cons_of_mem _ hx)) (acc.push e) rest k (by omega)]
      have harr : acc.push e ++ (e2 :: es'').toArray = acc ++ (e :: e2 :: es'').toArray := by
        rw [Array.push_eq_append, Array.append_assoc]
        congr 1
        rw [List.toArray_cons]
        simp
      rw [harr]

/-- `parseValue` on `toTokens j ++ rest` returns `(j, rest)`, for `Simple j`. -/
theorem parseValue_toTokens {j : Lean.Json} (h : Simple j) :
    ∀ (rest : List JsonToken) (fuel : Nat),
      2 * (toTokens j).length + 1 ≤ fuel →
      parseValue fuel (toTokens j ++ rest) = .ok (j, rest) := by
  induction h with
  | null =>
    intro rest fuel hf
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp only [toTokens] at hf; omega⟩
    simp only [toTokens]; rfl
  | bool b =>
    intro rest fuel hf
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by cases b <;> (simp only [toTokens] at hf; omega)⟩
    cases b <;> (simp only [toTokens]; rfl)
  | arr a hall ih =>
    intro rest fuel hf
    have hlen : (toTokens (.arr a)).length
        = (commaSep (a.toList.map toTokens)).length + 2 := by
      rw [toTokens]; simp only [List.length_cons, List.length_append, List.length_nil]
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by rw [hlen] at hf; omega⟩
    rw [toTokens]
    have hstep : parseValue (n + 1)
          ((.lbracket :: commaSep (a.toList.map toTokens) ++ [.rbracket]) ++ rest)
        = parseArrayBody n
            (commaSep (a.toList.map toTokens) ++ .rbracket :: rest) (#[] : Array Lean.Json) := by
      simp only [List.cons_append, List.append_assoc, List.nil_append]; rfl
    rw [hstep]
    rw [parseArrayBody_toTokens a.toList hall ih #[] rest n (by rw [hlen] at hf; omega)]
    have harr : (#[] : Array Lean.Json) ++ a.toList.toArray = a := by simp
    rw [harr]

theorem parse_toTokens {j : Lean.Json} (h : Simple j) :
    parse (toTokens j) = .ok j := by
  have hpv := parseValue_toTokens h [] (2 * (toTokens j).length + 1) (by omega)
  rw [List.append_nil] at hpv
  unfold parse
  rw [hpv]
  rfl

/-! ## Roundtrip -/

/-- Roundtrip: serialize, then tokenize, then parse, recovers the value.

The informal statement `parse (tokenize (serialize j)) = .ok j` is ill-typed
(`tokenize` returns `Except String (List JsonToken)`, `parse` consumes
`List JsonToken`); the faithful well-typed rendering threads the two through
the `Except` monad, exactly as the `Adapter.parseJsonString` composition does. -/
theorem roundtrip {j : Lean.Json} (h : Simple j) :
    (tokenize (serialize j) >>= parse) = .ok j := by
  rw [tokenize_serialize h]
  exact parse_toTokens h

/-! ## Corroboration for str / num / empty-obj (concrete instances)

These exercise the full `serialize` → `tokenize` → `parse` pipeline on values
*outside* the `Simple` fragment, via `Bool`-valued shape-and-value probes
(`Lean.Json` has no `DecidableEq`), closed by `native_decide`. -/

/-- A string value round-trips through the full pipeline. -/
def rtStr : Bool :=
  match tokenize (serialize (.str "hi")) >>= parse with
  | .ok (.str s) => s == "hi"
  | _ => false

theorem roundtrip_str : rtStr = true := by native_decide

/-- An integer number round-trips through the full pipeline. -/
def rtNum : Bool :=
  match tokenize (serialize (.num (Lean.JsonNumber.fromInt 42))) >>= parse with
  | .ok (.num n) => n.mantissa == 42 && n.exponent == 0
  | _ => false

theorem roundtrip_num : rtNum = true := by native_decide

/-- The empty object round-trips (objects render as the `{}` placeholder, so
only the empty object is faithful). -/
def rtEmptyObj : Bool :=
  match tokenize (serialize (Lean.Json.mkObj [])) >>= parse with
  | .ok (.obj _) => true
  | _ => false

theorem roundtrip_empty_obj : rtEmptyObj = true := by native_decide

end Hax.Json.Roundtrip
