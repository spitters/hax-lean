/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import HaxLean.Py.Json
public import HaxLean.Py.ToTExpr
public import HaxLean.Py.Secrecy
public import HaxLean.CertifiedTExprs

/-!
# The extraction module of a checked Python module

The Lean extraction module of a Python module of the subset, printed by the
printer of `haxpipeT --hax --emit-certified` (`toLeanCertifiedFileTyped`) from
the terms of `pyToTExpr`.

* `fnSecrecyDef` — the `<name>_fnSecrecy` definition listing a table of
  `FnSecrecy` records, as both `haxpipeT` modes print it.
* `PyReadError.render`, `PyRefusal.render` — a refusal of the reader and of the
  checker as one line with its position.
* `pyPrinterInputs` — the definitions the printer reads: the constants and the
  functions that are not linked, before the pipeline and after `postPipeline`
  at the empty write-back, with their signatures.
* `pyExtractionModule` — the text of the extraction module of a module that
  `pyCheck` accepts, with the secrecy records of `pyModuleSecrecy`.

A linked function has no definition in the module: a call of it is a call of a
name the module does not define, which the printer makes a field of the `Deps`
class, typed at the call site.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax

/-- The definition `<name>_fnSecrecy : List Hax.FnSecrecy` listing `recs`, with
its docstring, as the text appended to an extraction module. -/
def fnSecrecyDef (name : String) (recs : List FnSecrecy) : String :=
  let lit := "[" ++ ",\n    ".intercalate (recs.map FnSecrecy.toLean) ++ "]"
  s!"\n/-- The per-function secrecy of the crate: each function with a parameter or a\nresult holding a secret value, with the secrecy of each parameter and of the result.\nA function not listed has no secret parameter and a public result. -/\ndef {name}_fnSecrecy : List Hax.FnSecrecy :=\n  {lit}\n"

namespace Py

/-- A source position as `line:col`. -/
def Pos.render (p : Pos) : String := s!"{p.line}:{p.col}"

/-- An optional source position as ` at line:col`, empty when absent. -/
def renderAt : Option Pos → String
  | some p => s!" at {p.render}"
  | none => ""

/-- A refusal of the reader: the node, the position and the message. -/
def PyReadError.render (e : PyReadError) : String :=
  s!"read: {e.node}{renderAt e.pos}: {e.msg}"

/-- A refusal of the checker: the refusal kind, the position and the names. -/
def PyRefusal.render (r : PyRefusal) : String :=
  let names := if r.names.isEmpty then "" else s!" ({", ".intercalate r.names})"
  s!"check: {reprStr r.kind}{renderAt r.pos}{names}"

/-- The inputs of the printer for an extraction `x`: the definitions before the
pipeline (the constants, then the functions that are not linked), the same
definitions after `postPipeline` at the empty write-back (no struct fields, no
newtypes, no writers), and the signature table, a constant having no parameter
and an unknown result type as a constant item of a hax export has. -/
def pyPrinterInputs (x : PyExtraction) :
    List (String × TExpr) × List (String × TExpr) × List (String × HaxAdapter.FnTypeInfo) :=
  let rawTdefs := x.consts ++ x.fns
  let w : Writeback :=
    { procTdefs := rawTdefs, writeFns := [], writers := [], tupWriters := [],
      writeReturns := [], dropped := [] }
  let fnTypes : List (String × HaxAdapter.FnTypeInfo) :=
    x.consts.map (fun c => (c.1, ⟨[], .unknown⟩)) ++
      (x.sigs.filter (·.linked.isNone)).map fun s => (s.name, s.info)
  (rawTdefs, postPipeline [] [] w, fnTypes)

/-- The module docstring of the printer with its source named as the Python
module `moduleName` and its `py2json` dump. -/
def pyDocstring (moduleName : String) (text : String) : String :=
  (text.replace "The haxpipeT extraction of the crate,\ntaken from its hax frontend export."
      s!"The haxpipeT extraction of the Python module `{moduleName}`,\nread from its `py2json` dump.").replace
    "change the Rust source or the emitter." "change the Python source or the emitter."

/-- The text of the Lean extraction module `moduleName` of the Python module `m`:
`pyCheck`, `pyToTExpr`, the printer `toLeanCertifiedFileTyped` on
`pyPrinterInputs`, and `fnSecrecyDef` of `pyModuleSecrecy`. An error is the
refusal of the checker or of the translation, with its position. -/
def pyExtractionModule (moduleName : String) (m : PyModule) : Except String String := do
  let cm ← (pyCheck m).mapError PyRefusal.render
  let x ← (pyToTExpr cm).mapError fun e => s!"translate: {e}"
  let (rawTdefs, postTdefs, fnTypes) := pyPrinterInputs x
  let text := toLeanCertifiedFileTyped rawTdefs moduleName (fnTypes := fnTypes)
    (procTdefs := postTdefs)
  pure (pyDocstring moduleName text ++ fnSecrecyDef moduleName (pyModuleSecrecy cm))

end Py

end Hax
