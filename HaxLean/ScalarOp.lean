/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import HaxLean.ImpType

/-!
# Typed scalar operators

The scalar operators that the builtin tables of the hax extractions name by
string, as an inductive type indexed by the integer width `IntWidth`.

* `ScalarOp` — the untagged arithmetic operators `Add`, `Sub`, `Mul`, `Div`,
  `Rem`; the bitwise operators and shifts with an optional width tag
  (`BitXor`, `BitXor#8`); the trait-method shifts `shl#w`, `shr#w`; the
  rotations, wrapping arithmetic, `mulhi#w`, `mulmod#w` and `cast#w` at a
  width; and the `scalar#` calls computed in the scalar heap.
* `ScalarOp.name` — the builtin name of an operator (`bitXor (some .w8)` is
  `"BitXor#8"`, `cast .wsize` is `"cast#size"`).
* `ScalarOp.ofName?` — the operator of a builtin name, with the round trip
  `ofName?_name` and its converse `name_of_ofName?`.
-/

@[expose] public section

namespace Hax

/-- The width tag of an integer width: the bit width in decimal, and `size` for
    the platform word. -/
def IntWidth.tag : IntWidth → String
  | .w8 => "8" | .w16 => "16" | .w32 => "32" | .w64 => "64" | .w128 => "128"
  | .wsize => "size"

/-- The six integer widths. -/
def IntWidth.all : List IntWidth := [.w8, .w16, .w32, .w64, .w128, .wsize]

/-- Every integer width is in `IntWidth.all`. -/
theorem IntWidth.mem_all (w : IntWidth) : w ∈ IntWidth.all := by
  cases w <;> simp [IntWidth.all]

/-- The comparisons of the `scalar#` calls. -/
inductive ScalarCmp where
  | lt | gt | le | ge | eq | ne
  deriving Inhabited, Repr, DecidableEq

/-- The builtin name of a comparison: `Lt`, `Gt`, `Le`, `Ge`, `Eq`, `Ne`. -/
def ScalarCmp.name : ScalarCmp → String
  | .lt => "Lt" | .gt => "Gt" | .le => "Le" | .ge => "Ge" | .eq => "Eq" | .ne => "Ne"

/-- The binary operations of the `scalar#` calls, whose operands and result are
    in the scalar heap. -/
inductive ScalarCallOp where
  | add | sub | mul | bitAnd | bitXor | shr | shl
  | cmp (c : ScalarCmp)
  deriving Inhabited, Repr, DecidableEq

/-- The builtin name of a `scalar#` operation without its prefix. -/
def ScalarCallOp.name : ScalarCallOp → String
  | .add => "Add" | .sub => "Sub" | .mul => "Mul" | .bitAnd => "BitAnd"
  | .bitXor => "BitXor" | .shr => "Shr" | .shl => "Shl"
  | .cmp c => c.name

/-- The scalar operators of the builtin tables. `none` as the width of a
    bitwise operator or a shift is the untagged operator. -/
inductive ScalarOp where
  | add | sub | mul | div | rem
  | bitAnd (w : Option IntWidth)
  | bitOr (w : Option IntWidth)
  | bitXor (w : Option IntWidth)
  | not (w : Option IntWidth)
  | shl (w : Option IntWidth)
  | shr (w : Option IntWidth)
  /-- The trait method `shl` (`shl#w`). -/
  | shlM (w : IntWidth)
  /-- The trait method `shr` (`shr#w`). -/
  | shrM (w : IntWidth)
  | rotl (w : IntWidth)
  | rotr (w : IntWidth)
  | wrappingAdd (w : IntWidth)
  | wrappingSub (w : IntWidth)
  | wrappingMul (w : IntWidth)
  | mulhi (w : IntWidth)
  | mulmod (w : IntWidth)
  | cast (w : IntWidth)
  /-- A call `scalar#<op>` computed in the scalar heap. -/
  | scalar (s : ScalarCallOp)
  deriving Inhabited, Repr, DecidableEq

namespace ScalarOp

/-- `base` with the width tag `#<w>` of `w`, or `base` alone for `none`. -/
def tagged (base : String) : Option IntWidth → String
  | none => base
  | some w => base ++ "#" ++ w.tag

/-- The builtin name of an operator. -/
def name : ScalarOp → String
  | .add => "Add" | .sub => "Sub" | .mul => "Mul" | .div => "Div" | .rem => "Rem"
  | .bitAnd w => tagged "BitAnd" w
  | .bitOr w => tagged "BitOr" w
  | .bitXor w => tagged "BitXor" w
  | .not w => tagged "Not" w
  | .shl w => tagged "Shl" w
  | .shr w => tagged "Shr" w
  | .shlM w => "shl#" ++ w.tag
  | .shrM w => "shr#" ++ w.tag
  | .rotl w => "rotate_left#" ++ w.tag
  | .rotr w => "rotate_right#" ++ w.tag
  | .wrappingAdd w => "wrapping_add#" ++ w.tag
  | .wrappingSub w => "wrapping_sub#" ++ w.tag
  | .wrappingMul w => "wrapping_mul#" ++ w.tag
  | .mulhi w => "mulhi#" ++ w.tag
  | .mulmod w => "mulmod#" ++ w.tag
  | .cast w => "cast#" ++ w.tag
  | .scalar s => "scalar#" ++ s.name

/-- Every operator, each once. -/
def all : List ScalarOp :=
  [.add, .sub, .mul, .div, .rem] ++
  ((none :: IntWidth.all.map some).flatMap fun w =>
    [.bitAnd w, .bitOr w, .bitXor w, .not w, .shl w, .shr w]) ++
  (IntWidth.all.flatMap fun w =>
    [.shlM w, .shrM w, .rotl w, .rotr w, .wrappingAdd w, .wrappingSub w,
     .wrappingMul w, .mulhi w, .mulmod w, .cast w]) ++
  ([.add, .sub, .mul, .bitAnd, .bitXor, .shr, .shl, .cmp .lt, .cmp .gt, .cmp .le,
    .cmp .ge, .cmp .eq, .cmp .ne].map .scalar)

/-- The operator of a builtin name: the first operator of `all` with that name. -/
def ofName? (s : String) : Option ScalarOp :=
  all.find? fun o => o.name == s

/-- An operator parsed from a name has that name. -/
theorem name_of_ofName? {s : String} {o : ScalarOp} (h : ofName? s = some o) :
    o.name = s := by
  unfold ofName? at h
  simpa using List.find?_some h

/-- The name of an operator parses back to the operator. -/
theorem ofName?_name (o : ScalarOp) : ofName? o.name = some o := by
  cases o
  all_goals try (rename_i w; cases w)
  all_goals try (rename_i w; cases w)
  all_goals rfl

end ScalarOp

end Hax
