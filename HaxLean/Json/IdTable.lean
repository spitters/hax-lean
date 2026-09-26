/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean.Data.Json

/-!
# The id-table form of a hax frontend export

`cargo hax json --use-ids` writes a pair `[table, items]`. The table is an
array of entries `[id, {"<Kind>": value}]` with `Kind` one of `DefId`, `Ty`
and `ItemRef`, and every occurrence of such a value in `items` or in the
table is the node `{"id": id, "value": null}`. The default export writes the
items alone, with each node carrying its value inline as
`{"id": id, "value": value}`.

`Hax.resolveIds` turns the first form into the second. The entries of a
table refer only to smaller ids, so one forward pass resolves the table, and
the resolved values are shared between their occurrences and not copied.

## Main definitions

* `Hax.substIds`: replace each `{"id": n, "value": null}` node by the node
  carrying entry `n` of a resolved table.
* `Hax.resolveIds`: the inline form of an export in either form.
-/

@[expose] public section

namespace Hax

open Lean (Json)

/-- The id of a node `{"id": n, "value": null}`, and `none` for any other
    object. -/
def idRefOf (kvs : Std.TreeMap.Raw String Json compare) : Option Nat :=
  if kvs.size == 2 then
    match kvs.get? "id", kvs.get? "value" with
    | some (.num n), some .null =>
      if n.exponent == 0 && 0 ≤ n.mantissa then some n.mantissa.toNat else none
    | _, _ => none
  else none

/-- Replace each node `{"id": n, "value": null}` with `n` inside the table by
    `{"id": n, "value": tbl[n]}`. A node whose id lies outside the table is
    kept. -/
partial def substIds (tbl : Array Json) : Json → Json
  | .obj kvs =>
    match idRefOf kvs with
    | some n =>
      match tbl[n]? with
      | some v => .obj (kvs.insert "value" v)
      | none => .obj kvs
    | none => .obj (kvs.foldl (init := ∅) fun acc k v => acc.insert k (substIds tbl v))
  | .arr a => .arr (a.map (substIds tbl))
  | j => j

/-- The value of a table entry `[id, {"<Kind>": value}]`. -/
def tableEntryValue : Json → Option Json
  | .arr #[.num _, .obj kvs] =>
    if kvs.size == 1 then kvs.minEntry?.map (·.2) else none
  | _ => none

/-- The inline form of a hax frontend export. An export `[table, items]`
    written with `--use-ids` has its table resolved in id order and
    substituted into `items`; any other value is returned unchanged. -/
def resolveIds (j : Json) : Json :=
  match j with
  | .arr #[.arr table, .arr items] =>
    match table[0]? >>= tableEntryValue with
    | none => j
    | some _ =>
      let tbl := table.foldl (init := (#[] : Array Json)) fun acc entry =>
        match tableEntryValue entry with
        | some v => acc.push (substIds acc v)
        | none => acc.push .null
      substIds tbl (.arr items)
  | _ => j

end Hax
