/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.MonadicEmit

/-!
# Reading theorems for the `--emit-monadic` text

The opt-in `--emit-reading MOD` mode of haxpipeT. With `--emit-monadic`, it prints, in place of
the extraction, a companion module of the extraction module `MOD`: for each function `f` that
`--emit-monadic` prints in `RustM`, a theorem `f_reading` relating the printed `f` to the
state-passing reading `toRustMSB appRt f_impExpr` of its `ImpExpr` literal
(`HaxAscent/RustSemantics/ReadingTac.lean` of catcrypt-compiler), proved by the tactic
`emit_reading`. Each parameter `p` of `f` is bound in the reading's environment to a value
`v_p` whose encoding is the encoding of `p`.

The companion imports `MOD` and `HaxAscent.RustSemantics.ReadingTac`; haxpipeT does not depend
on the compiler, so the theorems are checked when the companion is built. A function whose
body has a construct or a call head outside the fragment of `emit_reading` gets no theorem; the
companion names the construct in a comment (`refusal?`), and haxpipeT reports each such
function on stderr as a line `reading-refused<TAB>f<TAB>construct`, followed by the line
`reading: N emitted, M refused`.

## Main definitions

* `refusal?`: the first construct of a body outside the fragment of `emit_reading`.
* `readingThm`: the text of the theorem `f_reading`.
* `readingFile`: the companion module.
* `readingReport`: the stderr lines for the functions without a theorem, and the counts.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.ReadingEmit

/-- A checked width-tagged arithmetic head at an unsigned width: `Add#32`, `Mul#size`. -/
def checkedHead (f : String) : Bool :=
  match f.splitOn "#" with
  | [op, tag] => ["Add", "Sub", "Mul"].contains op &&
      ["8", "16", "32", "64", "128", "size"].contains tag
  | _ => false

/-- The call heads other than checked arithmetic that `emit_reading` reads. -/
def readHeads : List String := ["index", "len", "Lt", "Le", "Gt", "Ge", "Eq", "Ne"]

/-- The range arguments of `index` that the printer reads as slicing. -/
def isRangeArg : ImpExpr → Bool
  | .app f _ => ["Range", "RangeTo", "RangeFrom", "RangeFull"].contains f
  | .var "RangeFull" => true
  | _ => false

/-- The first construct of `e` outside the fragment of `emit_reading`, as a short phrase;
    `none` when the whole expression is in the fragment. The fragment: integer and Boolean
    literals, variables, `let`, sequencing, the unit value, type ascriptions, conditionals, and
    calls of the heads `checkedHead` and `readHeads`. A call of a function of `crate` and a
    counted loop are outside it. -/
partial def refusal? (crate : List String) : ImpExpr → Option String
  | .lit (.int _) | .lit (.bool _) | .var _ | .unitVal => none
  | .letBind _ v b | .seq v b => (refusal? crate v).orElse fun _ => refusal? crate b
  | .typeAscription e _ => refusal? crate e
  | .ifThenElse c t e =>
    (refusal? crate c).orElse fun _ => (refusal? crate t).orElse fun _ => refusal? crate e
  | .app f args =>
    if crate.contains f then some s!"call of the crate function {f}"
    else if f == "index" && args.any isRangeArg then some "slicing"
    else if checkedHead f || readHeads.contains f then
      args.foldl (fun acc a => acc.orElse fun _ => refusal? crate a) none
    else some s!"head {f}"
  | .forFold .. => some "counted loop (the invariant is not generated)"
  | .forFoldRev .. => some "reverse loop"
  | .forFoldReturn .. | .forFoldRevReturn .. => some "loop with early return"
  | .whileLoop .. | .whileFold .. | .whileFoldReturn .. => some "while loop"
  | .lit _ => some "literal"
  | .tuple _ => some "tuple"
  | .proj _ _ => some "projection"
  | .match_ _ _ => some "match"
  | .cfBreak _ => some "break"
  | .lam .. => some "closure"
  | _ => some "construct"

/-- The theorem `f_reading` of the function `fn` with parameters `params` (name and printed
    Lean type), in the namespace of the extraction. -/
def readingThm (fn : String) (params : List (String × String)) : String :=
  let binders := params.map fun (p, t) => s!"({p} : {t})"
  let vbinders := params.map fun (p, _) => s!"(v_{p} : AVal)"
  let hyps := params.map fun (p, _) =>
    s!"    (h_{p} : v_{p}.toValue = Hax.Ascent.HaxEnc.enc {p})"
  let env := params.foldl (fun acc (p, _) => s!"({acc}.upd \"{p}\" v_{p})") "ρ"
  let args := " ".intercalate (fn :: params.map (·.1))
  let sig := " ".intercalate (s!"theorem {fn}_reading" :: binders ++ vbinders ++ ["(ρ : AEnv)"])
  let hypText := if hyps.isEmpty then "" else "\n" ++ "\n".intercalate hyps
  s!"/-- The printed `{fn}` reads as the `toRustMSB` reading of `{fn}_impExpr`. -/\n" ++
  s!"{sig}{hypText} :\n" ++
  s!"    ReadsAs ({args})\n      (toRustMSB appRt {fn}_impExpr {env}) := by\n" ++
  s!"  emit_reading [{fn}, {fn}_impExpr]\n"

/-- The reason of a function with a parameter without a printed type. -/
def noPrintedType : String := "a parameter without a printed type"

/-- The comment of the companion for a function `f` without a theorem. -/
def refusedComment (f why : String) : String :=
  s!"-- `{f}`: no reading theorem ({why}).\n"

/-- The companion module of the extraction module `extMod` with namespace `ns`: the theorem
    `f_reading` of each function `(f, params, body)` of `fns` whose parameters have printed
    types (`params = some ps`) and whose body is in the fragment, and a comment naming the
    reason for each other. `crate` lists the names of the crate's functions. -/
def readingFile (extMod ns : String) (crate : List String)
    (fns : List (String × Option (List (String × String)) × ImpExpr)) : String :=
  let parts := fns.map fun (f, params?, body) =>
    match params?, refusal? crate body with
    | none, _ => refusedComment f noPrintedType
    | _, some why => refusedComment f why
    | some params, none => readingThm f params
  s!"/-\n  Auto-generated by haxpipeT --emit-reading\n-/\n" ++
  s!"import {extMod}\nimport HaxAscent.RustSemantics.ReadingTac\n\n" ++
  s!"/-!\n# Reading theorems of `{extMod}`\n\nFor each function of `{extMod}` " ++
  "printed in `RustM`, the theorem `f_reading`: every outcome of the `toRustMSB` reading of " ++
  "its literal `f_impExpr` is a value of the printed function with the same encoding.\n-/\n\n" ++
  s!"namespace {ns}\n\nopen Hax HaxAscent.RustSemantics CatCrypt.Hax.RustSemantics\n\n" ++
  "\n".intercalate parts ++ s!"\nend {ns}\n"

/-- The `(function, construct)` pairs named by the `refusedComment` lines of a companion text,
    and the number of theorems the text contains. -/
def readingCounts (text : String) : List (String × String) × Nat :=
  text.splitOn "\n" |>.foldl (fun (acc : List (String × String) × Nat) line =>
    if line.startsWith "theorem " then (acc.1, acc.2 + 1)
    else if line.startsWith "-- `" then
      match (line.drop 4).toString.splitOn "`: no reading theorem (" with
      | [f, rest] => (acc.1 ++ [(f, (rest.dropEnd 2).toString)], acc.2)
      | _ => acc
    else acc) ([], 0)

/-- The stderr report of a companion text: one line `reading-refused<TAB>f<TAB>construct` per
    function without a theorem, then `reading: N emitted, M refused`. -/
def readingReport (text : String) : List String :=
  let (refused, n) := readingCounts text
  refused.map (fun (f, why) => s!"reading-refused\t{f}\t{why}") ++
    [s!"reading: {n} emitted, {refused.length} refused"]

#guard readingReport (refusedComment "f" "a counted loop" ++ "theorem g_reading\n") ==
  ["reading-refused\tf\ta counted loop", "reading: 1 emitted, 1 refused"]

-- The theorem of a function of two parameters, as `ReadingTacTest.mulChecked_reading` states it.
#guard readingThm "mulChecked" [("a", "Int"), ("b", "Int")] ==
  "/-- The printed `mulChecked` reads as the `toRustMSB` reading of `mulChecked_impExpr`. -/\n" ++
  "theorem mulChecked_reading (a : Int) (b : Int) (v_a : AVal) (v_b : AVal) (ρ : AEnv)\n" ++
  "    (h_a : v_a.toValue = Hax.Ascent.HaxEnc.enc a)\n" ++
  "    (h_b : v_b.toValue = Hax.Ascent.HaxEnc.enc b) :\n" ++
  "    ReadsAs (mulChecked a b)\n" ++
  "      (toRustMSB appRt mulChecked_impExpr ((ρ.upd \"a\" v_a).upd \"b\" v_b)) := by\n" ++
  "  emit_reading [mulChecked, mulChecked_impExpr]\n"

end Hax.ReadingEmit
