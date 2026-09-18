/-
Copyright (c) the Aeneas contributors. Licensed under the Apache License,
Version 2.0 (the "License"); you may not use this file except in compliance with
the License. You may obtain a copy of the License at
http://www.apache.org/licenses/LICENSE-2.0. Unless required by applicable law or
agreed to in writing, software distributed under the License is distributed on
an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and
limitations under the License.

Ported to Lean v4.33.1 without Mathlib by the CatCrypt Contributors.
Source: cryspen/aeneas at 6852e6474ec508930acba4df79977b3483a10d10,
  backends/lean/Aeneas/Std/Scalar/Elab.lean
-/

module

public meta import Lean

/-!
# Generic Scalar Definitions and Theorems

`uscalar cmd` elaborates `cmd` once for each unsigned scalar type, `iscalar cmd` once for
each signed one, and `scalar cmd` for all twelve; the `_no_usize`/`_no_isize` variants
omit the pointer-sized type. In `cmd`:

- a name segment `«%S»` is replaced with the scalar name (`U8`, `U16`, …);
- the substring `'S` in a name segment is replaced with the scalar name
  (`Clone'S` becomes `CloneU8`);
- the term `%BitWidth` is replaced with the bit width (`8`, …, `System.Platform.numBits`);
- the term `%Size` is replaced with the size in bytes.
-/

@[expose] public section

set_option autoImplicit false

namespace Aeneas.Std.ScalarElab

open Lean Elab Command Term Meta

/-- `some rest` when `sub` is a prefix of `str` with remainder `rest`. -/
meta def isSubstring (sub str : List Char) : Option (List Char) :=
  match sub, str with
  | [], _ => some str
  | hd :: sub, hd' :: str =>
    if hd == hd' then isSubstring sub str
    else none
  | _, _ => none

/-- `str` with every occurrence of `'S` replaced with `ty`. -/
meta partial def elabString (ty : String) (str : String) : String :=
  let rec replace (str : List Char) : List Char :=
    match isSubstring "'S".toList str with
    | some str => ty.toList ++ replace str
    | none =>
      match str with
      | [] => []
      | c :: str => c :: replace str
  String.ofList (replace str.toList)

/-- `n` with the segment `%S` replaced with `ty` and `'S` replaced inside every segment. -/
meta def elabSpecialName (ty : String) (n : Name) : CommandElabM Name := do
  match n with
  | .anonymous => pure .anonymous
  | .str pre str =>
    let str := if str == "%S" then ty else elabString ty str
    pure (.str (← elabSpecialName ty pre) str)
  | .num pre i => pure (.num (← elabSpecialName ty pre) i)

/-- `stx` with the scalar placeholders replaced. -/
meta partial def elabSpecial (ty : String) (bw size : Syntax) (stx : Syntax) :
    CommandElabM Syntax := do
  match stx with
  | .missing => pure .missing
  | .node _ _ #[.atom _ "%BitWidth"] =>
    pure bw
  | .node _ _ #[.atom _ "%Size"] =>
    pure size
  | .node info kind args =>
    let args ← args.mapM (elabSpecial ty bw size)
    pure (.node info kind args)
  | .atom info val =>
    if val == "%BitWidth" then
      pure bw
    else pure (.atom info val)
  | .ident info rawVal val preresolved =>
    let val ← elabSpecialName ty val
    pure (.ident info rawVal val preresolved)

/-- Elaborate `cmd` once per scalar type in `tysBws`. -/
meta def elabCommand (tysBws : List (String × Syntax × Syntax)) (cmd : TSyntax `command) :
    CommandElabM Unit := do
  let elabOne (tyBw : String × Syntax × Syntax) : CommandElabM Unit := do
    let (ty, bw, size) := tyBw
    let cmd ← elabSpecial ty bw size cmd
    let cmd ← liftMacroM (expandNamespacedDeclaration cmd)
    Command.elabCommand cmd
  for tyBw in tysBws do
    elabOne tyBw

scoped syntax "%BitWidth" : term
scoped syntax "%Size" : term

scoped syntax (name := uscalarCommand) "uscalar" command : command

@[command_elab uscalarCommand]
meta def uscalarCommandImpl : CommandElab := fun stx => do
  match stx with
  | `(uscalarCommand| uscalar $cmd) =>
    elabCommand [("U8", ←`(8), ←`(1)), ("U16", ←`(16), ←`(2)), ("U32", ←`(32), ←`(4)),
                 ("U64", ←`(64), ←`(8)), ("U128", ←`(128), ←`(16)),
                 ("Usize", ←`(System.Platform.numBits), ←`(System.Platform.numBits/8))] cmd
  | _ => throwUnsupportedSyntax

scoped syntax (name := uscalarNoUsizeCommand) "uscalar_no_usize" command : command

@[command_elab uscalarNoUsizeCommand]
meta def uscalarNoUsizeCommandImpl : CommandElab := fun stx => do
  match stx with
  | `(uscalarNoUsizeCommand| uscalar_no_usize $cmd) =>
    elabCommand [("U8", ←`(8), ←`(1)), ("U16", ←`(16), ←`(2)), ("U32", ←`(32), ←`(4)),
                 ("U64", ←`(64), ←`(8)), ("U128", ←`(128), ←`(16))] cmd
  | _ => throwUnsupportedSyntax

scoped syntax (name := iscalarCommand) "iscalar" command : command

@[command_elab iscalarCommand]
meta def iscalarCommandImpl : CommandElab := fun stx => do
  match stx with
  | `(iscalarCommand| iscalar $cmd) =>
    elabCommand [("I8", ←`(8), ←`(1)), ("I16", ←`(16), ←`(2)), ("I32", ←`(32), ←`(4)),
                 ("I64", ←`(64), ←`(8)), ("I128", ←`(128), ←`(16)),
                 ("Isize", ←`(System.Platform.numBits), ←`(System.Platform.numBits/8))] cmd
  | _ => throwUnsupportedSyntax

scoped syntax (name := iscalarNoIsizeCommand) "iscalar_no_isize" command : command

@[command_elab iscalarNoIsizeCommand]
meta def iscalarNoIsizeNoIsizeCommandImpl : CommandElab := fun stx => do
  match stx with
  | `(iscalarNoIsizeCommand| iscalar_no_isize $cmd) =>
    elabCommand [("I8", ←`(8), ←`(1)), ("I16", ←`(16), ←`(2)), ("I32", ←`(32), ←`(4)),
                 ("I64", ←`(64), ←`(8)), ("I128", ←`(128), ←`(16))] cmd
  | _ => throwUnsupportedSyntax

scoped syntax (name := scalarCommand) "scalar" command : command

@[command_elab scalarCommand]
meta def scalarCommandImpl : CommandElab := fun stx => do
  match stx with
  | `(scalarCommand| scalar $cmd) =>
    elabCommand [("U8", ←`(8), ←`(1)), ("U16", ←`(16), ←`(2)), ("U32", ←`(32), ←`(4)),
                 ("U64", ←`(64), ←`(8)), ("U128", ←`(128), ←`(16)),
                 ("Usize", ←`(System.Platform.numBits), ←`(System.Platform.numBits/8)),
                 ("I8", ←`(8), ←`(1)), ("I16", ←`(16), ←`(2)), ("I32", ←`(32), ←`(4)),
                 ("I64", ←`(64), ←`(8)), ("I128", ←`(128), ←`(16)),
                 ("Isize", ←`(System.Platform.numBits), ←`(System.Platform.numBits/8))] cmd
  | _ => throwUnsupportedSyntax

end Aeneas.Std.ScalarElab
