/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

-- Each probe evaluates `parseJsonString`, which calls into the lexer and the
-- parser. Evaluating a definition from another module needs its IR, which only a
-- `meta` import supplies; `meta` replaces rather than adds, so each module is
-- imported twice, the `meta` line first. These probes live apart from `Adapter`
-- because a `meta` import there would withhold `parseJsonString` from the
-- module's public surface.
public meta import HaxLean.Json.Lexer
public import HaxLean.Json.Lexer
public meta import HaxLean.Json.Parser
public import HaxLean.Json.Parser
public meta import HaxLean.Json.Adapter
public import HaxLean.Json.Adapter

/-!
# Evaluated probes for `parseJsonString`

The probes `Adapter` closes by `decide` stay there. The ones below reach values
the kernel does not reduce — `Lean.Json.obj`'s string-keyed map, the lexer's
`String.ofList` string body, `String.toInt?` through `String.Slice` — and are
checked by evaluation.
-/

@[expose] public section

namespace Hax.Json

/-- Probe: `parseJsonString "{}"` yields a `Json.obj` (empty object). -/
def isParseStringEmptyObj : Bool :=
  match parseJsonString "{}" with
  | .ok (Lean.Json.obj _) => true
  | _ => false

#guard isParseStringEmptyObj

/-- Probe: a string literal `"hi"` parses to `Json.str "hi"`. -/
def isParseStringHi : Bool :=
  match parseJsonString "\"hi\"" with
  | .ok (Lean.Json.str s) => s == "hi"
  | _ => false

#guard isParseStringHi

/-- Probe: an integer literal parses to a `Json.num`. -/
def isParseStringInt : Bool :=
  match parseJsonString "42" with
  | .ok (Lean.Json.num _) => true
  | _ => false

#guard isParseStringInt

/-- Round-trip probe: `parseJsonString "{}"` produces an empty `Json.obj`. The
    empty object is `Lean.Json.obj t` for an empty `Std.TreeMap.Raw`, whose
    constructors are not exposed for a direct match, so the size is read by
    `foldl`. -/
def roundtripEmptyObj : Bool :=
  match parseJsonString "{}" with
  | .ok (Lean.Json.obj t) => t.foldl (init := 0) (fun n _ _ => n + 1) == 0
  | _ => false

#guard roundtripEmptyObj

/-- Round-trip probe: `parseJsonString "\"hi\""` produces `Json.str "hi"`. -/
def roundtripStrHi : Bool :=
  match parseJsonString "\"hi\"" with
  | .ok (Lean.Json.str s) => s == "hi"
  | _ => false

#guard roundtripStrHi

end Hax.Json
