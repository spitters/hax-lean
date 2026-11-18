/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import HaxLean.Json.Adapter
public import HaxLean.Json.IdTable

set_option autoImplicit false

/-!
# Chunked JSON parse of a large hax export

`Hax.Json.parseJsonString` tokenizes the whole input as a `List Char` and then as a
token list, which needs several GB for an export of 100 MB. `chunkedParse T s` computes
the same `Lean.Json` value from slices of `s`: a byte scanner (aware of strings and
escapes) finds the end of each value; a value whose text exceeds `T` bytes and is an
array or an object is split into its elements, and every other value is parsed by the
unchanged `parseJsonString` on its slice. Arrays are assembled with `Json.arr` and
objects with `Json.mkObj` in the order of the parser, with the keys decoded by
`parseJsonString`. A structural anomaly in a split value hands the value to
`parseJsonString`, which reports the error.

`chunkedParseResolved T s` computes `Hax.resolveIds` of the same value. In the id form
`[table, items]` of `cargo hax json --use-ids` the table is parsed first and each leaf
of `items` is substituted against it right after parsing, so the unresolved `items`
tree is never held.

In the inline form every occurrence of a hax id node `{"id": n, "value": v}` carries its
value. Without an id table the parse interns these nodes (`internIds`): one table per
parse records a node for each id, and a later node of the same id with an equal (`==`)
value is replaced by the recorded node. The parsed value is unchanged; the equal values
of an id are one value in memory.

The value of both entry points equals the value of the whole-file path for every
threshold `T` (error messages of malformed input may differ); no theorem is claimed.
`T = 0` selects the whole-file parse.
-/

@[expose] public section

namespace Hax.Json.Chunked

open Lean (Json)

/-- The threshold in bytes of `--json-chunk` when the option is absent. -/
def defaultChunkThreshold : Nat := 4194304

/-- The threshold of an optional `--json-chunk` argument; `0` selects the whole-file
parse. -/
def chunkThreshold (arg : Option Nat) : Nat := arg.getD defaultChunkThreshold

/-- The byte at index `i` of the UTF-8 encoding of `s`, and `0` past its end. -/
def byteAt (s : String) (i : Nat) : UInt8 :=
  if h : (⟨i⟩ : String.Pos.Raw) < s.rawEndPos then s.getUTF8Byte ⟨i⟩ h else 0

/-- The slice `[b, e)` of the bytes of `s` as a string. -/
def slice (s : String) (b e : Nat) : String :=
  String.Pos.Raw.extract s ⟨b⟩ ⟨e⟩

/-- JSON whitespace. -/
def isWs (c : UInt8) : Bool := c == 0x20 || c == 0x09 || c == 0x0A || c == 0x0D

/-- The first index at or after `i` that is not whitespace. Each step advances `i`;
the measure is `s.utf8ByteSize - i`. -/
partial def skipWs (s : String) (i : Nat) : Nat :=
  if i < s.utf8ByteSize && isWs (byteAt s i) then skipWs s (i + 1) else i

/-- The index after the closing quote of the string whose body starts at `i`, `some`
of the end of the input when unterminated, and `none` once `i` reaches `lim`. Measure:
`s.utf8ByteSize - i`. -/
partial def scanStr (s : String) (i lim : Nat) : Option Nat :=
  if i ≥ s.utf8ByteSize then some s.utf8ByteSize
  else if i ≥ lim then none
  else
    let c := byteAt s i
    if c == 0x22 then some (i + 1)
    else if c == 0x5C then scanStr s (i + 2) lim
    else scanStr s (i + 1) lim

/-- The index after the bracket that closes the array or object scanned from `i` at
nesting depth `depth`, skipping strings; `none` once `i` reaches `lim`. Measure:
`s.utf8ByteSize - i`. -/
partial def scanBr (s : String) (i depth lim : Nat) : Option Nat :=
  if i ≥ s.utf8ByteSize then some s.utf8ByteSize
  else if i ≥ lim then none
  else
    let c := byteAt s i
    if c == 0x22 then
      match scanStr s (i + 1) lim with
      | some j => scanBr s j depth lim
      | none => none
    else if c == 0x5B || c == 0x7B then scanBr s (i + 1) (depth + 1) lim
    else if c == 0x5D || c == 0x7D then
      if depth ≤ 1 then some (i + 1) else scanBr s (i + 1) (depth - 1) lim
    else scanBr s (i + 1) depth lim

/-- The end of a number or literal starting at `i`: the next delimiter, whitespace or
the end of the input. Measure: `s.utf8ByteSize - i`. -/
partial def scanScalar (s : String) (i : Nat) : Nat :=
  if i ≥ s.utf8ByteSize then s.utf8ByteSize
  else
    let c := byteAt s i
    if c == 0x2C || c == 0x5D || c == 0x7D || isWs c then i else scanScalar s (i + 1)

/-- The end of the value starting at `b`, or `none` when scanning reaches `lim` first. -/
def scanEnd (s : String) (b lim : Nat) : Option Nat :=
  let c := byteAt s b
  if c == 0x22 then scanStr s (b + 1) lim
  else if c == 0x5B || c == 0x7B then scanBr s (b + 1) 1 lim
  else some (scanScalar s b)

/-- The value on `[b, e)` by the whole-file parser, paired with `e`. -/
def leaf (s : String) (b e : Nat) : Except String (Json × Nat) :=
  (fun j => (j, e)) <$> Hax.Json.parseJsonString (slice s b e)

/-- The value starting at `b` parsed whole, whatever its size. -/
def whole (s : String) (b : Nat) : Except String (Json × Nat) :=
  leaf s b ((scanEnd s b (s.utf8ByteSize + 1)).getD s.utf8ByteSize)

/-- The key of an object member: the string literal on `[b, e)`. The parser keeps the raw body between the quotes as the key, and the
literal is checked by `parseJsonString`. -/
def keyOf (s : String) (b e : Nat) : Except String String :=
  match Hax.Json.parseJsonString (slice s b e) with
  | .ok (.str _) => .ok (slice s (b + 1) (e - 1))
  | .ok _ => .error "chunked JSON: object key is not a string"
  | .error err => .error err

/-- The id substitution of `Hax.substIds` at an object node assembled from its
members: a node `{"id": n, "value": null}` takes the value of entry `n`. -/
def substNode (tbl : Option (Array Json)) (j : Json) : Json :=
  match tbl, j with
  | some tbl, .obj kvs =>
    match Hax.idRefOf kvs with
    | some n =>
      match tbl[n]? with
      | some v => .obj (kvs.insert "value" v)
      | none => j
    | none => j
  | _, _ => j

/-- The id nodes recorded by the interning of a chunked parse: for each id `n`, the value
`v` and the node `{"id": n, "value": v}` met last with that id. -/
abbrev InternTable := Std.HashMap Nat (Json × Json)

/-- The id and the value of a hax id node `{"id": n, "value": v}`, an object of exactly
these two members with `n` a natural number; `none` for any other object. -/
def idNode? (kvs : Std.TreeMap.Raw String Json compare) : Option (Nat × Json) :=
  if kvs.size == 2 then
    match kvs.get? "id", kvs.get? "value" with
    | some (.num n), some v =>
      if n.exponent == 0 && 0 ≤ n.mantissa then some (n.mantissa.toNat, v) else none
    | _, _ => none
  else none

/-- The members of an object with each value mapped by `f`; the tree of the members keeps
its shape. -/
def mapMembers (f : Json → StateM InternTable Json)
    (kvs : Std.TreeMap.Raw String Json compare) :
    StateM InternTable (Std.TreeMap.Raw String Json compare) := do
  return ⟨⟨← kvs.inner.inner.mapM fun _ v => f v⟩⟩

/-- The interning of one node whose members are already interned: an id node
`{"id": n, "value": v}` with `v == w` for the node recorded for `n` with value `w` is that
recorded node; any other id node is recorded; every other value is unchanged. The result
is `==` to `j`. -/
def internNode (j : Json) : StateM InternTable Json := do
  match j with
  | .obj kvs =>
    match idNode? kvs with
    | some (n, v) =>
      if let some (w, node) := (← get)[n]? then
        if w == v then return node
      modify (·.insert n (v, j))
      return j
    | none => return j
  | _ => return j

/-- The value `j` with its id nodes shared: top down, an id node whose value equals (`==`)
the value recorded for its id is replaced by the recorded node; any other id node has its
members interned and is recorded. The result is `==` to `j`, and the equal values of the
occurrences of an id met under one table are one value in memory. -/
partial def internIds (j : Json) : StateM InternTable Json := do
  match j with
  | .arr xs => return .arr (← xs.mapM internIds)
  | .obj kvs =>
    if let some (n, v) := idNode? kvs then
      if let some (w, node) := (← get)[n]? then
        if w == v then return node
    let out := Json.obj (← mapMembers internIds kvs)
    if let .obj okvs := out then
      if let some (n, v) := idNode? okvs then modify (·.insert n (v, out))
    return out
  | _ => return j

/-- A parsed leaf: substituted against the id table `tbl` when given, and otherwise with
its id nodes interned under `tab` (`internIds`). -/
def finishLeaf (tbl : Option (Array Json)) (tab : InternTable) (j : Json) :
    Json × InternTable :=
  match tbl with
  | some t => (Hax.substIds t j, tab)
  | none => (internIds j).run tab

/-- An object assembled from its members: substituted against `tbl` when given
(`substNode`), and otherwise interned as one node under `tab` (`internNode`). -/
def finishObj (tbl : Option (Array Json)) (tab : InternTable) (j : Json) :
    Json × InternTable :=
  match tbl with
  | some _ => (substNode tbl j, tab)
  | none => (internNode j).run tab

/-- A result of `whole`, paired with the unchanged intern table `tab`. -/
def keepTab (tab : InternTable) (r : Except String (Json × Nat)) :
    Except String (Json × Nat × InternTable) :=
  (fun (j, e) => (j, e, tab)) <$> r

mutual

/-- The value starting at the non-whitespace index `b`, the index after it and the intern
table after it. A value of at most `T` bytes is parsed on its slice and finished by
`finishLeaf` (substituted against `tbl` when given, its id nodes interned under `tab`
otherwise); an array or object of more bytes is split into its elements. Each recursive
call starts strictly after `b`, so the depth of the recursion is bounded by the nesting
of the input. -/
partial def parseAt (s : String) (T : Nat) (tbl : Option (Array Json)) (tab : InternTable)
    (b : Nat) : Except String (Json × Nat × InternTable) :=
  match scanEnd s b (b + T + 1) with
  | some e =>
    match leaf s b e with
    | .ok (j, e') => let (j, tab) := finishLeaf tbl tab j; .ok (j, e', tab)
    | .error err => .error err
  | none =>
    let c := byteAt s b
    if c == 0x5B then parseArr s T tbl tab b
    else if c == 0x7B then parseObj s T tbl tab b
    else
      match whole s b with
      | .ok (j, e') => let (j, tab) := finishLeaf tbl tab j; .ok (j, e', tab)
      | .error err => .error err

/-- The array starting at `b` (a `[`) split into its elements. -/
partial def parseArr (s : String) (T : Nat) (tbl : Option (Array Json)) (tab : InternTable)
    (b : Nat) : Except String (Json × Nat × InternTable) :=
  let i := skipWs s (b + 1)
  if byteAt s i == 0x5D then .ok (.arr #[], i + 1, tab) else arrLoop s T tbl tab b #[] i

/-- The elements of the array from `b`, the next element starting at `i`. -/
partial def arrLoop (s : String) (T : Nat) (tbl : Option (Array Json)) (tab : InternTable)
    (b : Nat) (acc : Array Json) (i : Nat) : Except String (Json × Nat × InternTable) :=
  match parseAt s T tbl tab i with
  | .error err => .error err
  | .ok (v, e, tab) =>
    let acc := acc.push v
    let j := skipWs s e
    let c := byteAt s j
    if c == 0x2C then arrLoop s T tbl tab b acc (skipWs s (j + 1))
    else if c == 0x5D then .ok (.arr acc, j + 1, tab)
    else keepTab tab (whole s b)

/-- The object starting at `b` (a `{`) split into its members. -/
partial def parseObj (s : String) (T : Nat) (tbl : Option (Array Json)) (tab : InternTable)
    (b : Nat) : Except String (Json × Nat × InternTable) :=
  let i := skipWs s (b + 1)
  if byteAt s i == 0x7D then
    let (j, tab) := finishObj tbl tab (Json.mkObj [])
    .ok (j, i + 1, tab)
  else objLoop s T tbl tab b [] i

/-- The members of the object from `b`, the next member starting at `i`. -/
partial def objLoop (s : String) (T : Nat) (tbl : Option (Array Json)) (tab : InternTable)
    (b : Nat) (acc : List (String × Json)) (i : Nat) :
    Except String (Json × Nat × InternTable) :=
  if byteAt s i != 0x22 then keepTab tab (whole s b)
  else
    match scanStr s (i + 1) (s.utf8ByteSize + 1) with
    | none => keepTab tab (whole s b)
    | some ke =>
      match keyOf s i ke with
      | .error err => .error err
      | .ok k =>
        let c := skipWs s ke
        if byteAt s c != 0x3A then keepTab tab (whole s b)
        else
          match parseAt s T tbl tab (skipWs s (c + 1)) with
          | .error err => .error err
          | .ok (v, e, tab) =>
            let acc := (k, v) :: acc
            let j := skipWs s e
            let d := byteAt s j
            if d == 0x2C then objLoop s T tbl tab b acc (skipWs s (j + 1))
            else if d == 0x7D then
              let (o, tab) := finishObj tbl tab (Json.mkObj acc.reverse)
              .ok (o, j + 1, tab)
            else keepTab tab (whole s b)

end

/-- The value of `parseJsonString s`, computed from slices of at most about `T` bytes.
`T = 0` is the whole-file parse. -/
def chunkedParse (T : Nat) (s : String) : Except String Json :=
  if T == 0 || s.utf8ByteSize ≤ T then Hax.Json.parseJsonString s
  else
    let b := skipWs s 0
    match parseAt s T none {} b with
    | .error err => .error err
    | .ok (j, e, _) =>
      if skipWs s e == s.utf8ByteSize then .ok j
      else Hax.Json.parseJsonString s

/-- The id table of an export `[table, items]`: the entries resolved in id order, as
in `Hax.resolveIds`; `none` when the first element is not an id table. -/
def tableOf (j : Json) : Option (Array Json) :=
  match j with
  | .arr table =>
    match table[0]? >>= Hax.tableEntryValue with
    | none => none
    | some _ =>
      some (table.foldl (init := (#[] : Array Json)) fun acc entry =>
        match Hax.tableEntryValue entry with
        | some v => acc.push (Hax.substIds acc v)
        | none => acc.push .null)
  | _ => none

/-- The value of `Hax.resolveIds <$> parseJsonString s`, computed from slices of at most
about `T` bytes. In the id form the items are substituted against the table as their
slices are parsed. `T = 0` is the whole-file parse. -/
def chunkedParseResolved (T : Nat) (s : String) : Except String Json :=
  let direct : Except String Json := Hax.resolveIds <$> Hax.Json.parseJsonString s
  if T == 0 || s.utf8ByteSize ≤ T then direct
  else
    let b := skipWs s 0
    let i := skipWs s (b + 1)
    if byteAt s b != 0x5B || byteAt s i != 0x5B then
      Hax.resolveIds <$> chunkedParse T s
    else
      match parseAt s T none {} i with
      | .error err => .error err
      | .ok (first, e, _) =>
        match tableOf first with
        | none => Hax.resolveIds <$> chunkedParse T s
        | some tbl =>
          let j := skipWs s e
          if byteAt s j != 0x2C then direct
          else
            let k := skipWs s (j + 1)
            let c := byteAt s k
            if c != 0x5B && c != 0x7B then direct
            else
              match parseAt s T (some tbl) {} k with
              | .error err => .error err
              | .ok (items, e', _) =>
                let l := skipWs s e'
                if byteAt s l == 0x5D && skipWs s (l + 1) == s.utf8ByteSize then .ok items
                else direct

end Hax.Json.Chunked
