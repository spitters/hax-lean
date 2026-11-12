/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.PrettyPrint -- deprecated_module: ignore
public import HaxLean.Range.Heads

/-!
# Monadic emission of the effect closure

The opt-in `--emit-monadic` mode of haxpipeT. A function is emitted in
`Aeneas.Std.RustM` when its body reaches an operation that panics in Rust, or calls a
function so emitted; every other function keeps its total surface definition.

A call of a partial operation is printed as the guarded operation of
`HaxLean/RuntimeM.lean` (`guardedHead?`): checked `+ - * / % << >>` at the width of the
head's tag (`Add#32` is `Hax.addM_w 32`, `Div#i64` is `Hax.divM_iw 64`), indexing and
updates within bounds, slicing, `copy_from_slice`, `unwrap`, `expect`, `assert` and the
panicking heads. An untagged arithmetic head is an operation on unbounded integers and
stays total.

The body of a monadic function is printed in A-normal form (`renderM`): each monadic
subterm is bound by `let x ← …` in Rust evaluation order, arguments left to right
(`hoist`), and a monadic subterm under `if`, `match` or a loop body is bound inside that
branch, which is a `do` sequence. A variable that a branch rebinds is returned by the
branch as part of a tuple and rebound after it (`let (v₁, …, vₙ) ← if c then … else …`).
A subterm without monadic content is printed by `toLean`. Counted loops become
`Hax.foldRangeM`, `Hax.forFoldM` and `Hax.forFoldReturnM` (a reverse loop runs the
forward counter and computes the reverse one), `while` loops `Hax.whileFoldM` and
`Hax.whileFoldReturnM`, and `map` with a monadic closure `mapM`. A closure body passed to
any other higher-order function is printed by `toLean`, with total operations.

## Main definitions

* `guardedHead?`: the guarded operation of a call head that panics in Rust.
* `hasEffect`: whether an expression has monadic content.
* `Facts`, `emissionOf`: the emission decision of one function, the one place where a
  proof that a function does not panic keeps it total.
* `effectClosure`: the monadic functions of a crate, the least set closed under
  `emissionOf` and under the groups of definitions that share a type (the `impl`s of a
  trait method).
* `recursiveFns`: the monadic functions on a cycle of the call graph; they are emitted
  with `partial_fixpoint`.
* `renderM`, `renderBody`: the A-normal `do` rendering.
* `RangeInput`, `rangePlan`: the decision of the verified range checker (`Range.checkT`) on the
  functions of a crate, which `Facts.total` and `Facts.specced` carry to `emissionOf`.
* `pureCalls`: the calls of a total function to `specced` functions, through their total
  surface `f_pure`.
* `rangeBlock`: the theorems `f_noPanic` and `f_noPanicOn`, proved by
  `Range.checkT_rust_sound_defs` and evaluation of the checker on `f_texpr`.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.MonadicEmit

/-! ## Partial heads -/

/-- The width argument and signedness of an integer tag: `32` is `("32", false)`, `i64`
    is `("64", true)`, `size` is `("Hax.usizeBits", false)`; `none` for any other tag. -/
def intTag? (tag : String) : Option (String × Bool) :=
  let (signed, t) := if tag.startsWith "i" then (true, (tag.drop 1).toString) else (false, tag)
  if t == "size" then some ("Hax.usizeBits", signed)
  else if ["8", "16", "32", "64", "128"].contains t then some (t, signed)
  else none

/-- The stem of the guarded operation of a checked operator: `Add` is `add`. -/
def checkedStem? : String → Option String
  | "Add" => some "add" | "Sub" => some "sub" | "Mul" => some "mul"
  | "Div" => some "div" | "Rem" => some "rem"
  | "Shl" | "shl" => some "shl" | "Shr" | "shr" => some "shr"
  | _ => none

/-- The call heads that always panic. -/
def panicHeads : List String :=
  ["panic", "panic_fmt", "begin_panic", "panic_explicit", "panic_display",
   "unreachable_display", "panic_nounwind", "panic_nounwind_fmt", "panic_str",
   "panic_bounds_check", "unreachable", "todo", "unimplemented"]

/-- The guarded operation of `HaxLean/RuntimeM.lean` of a call `f args` that panics in
    Rust, with the arguments it takes; `none` for a total call. -/
def guardedHead? (f : String) (args : List ImpExpr) : Option (String × List ImpExpr) :=
  match f, args with
  | "index", [a, .app "RangeTo" [n]] | "index_mut", [a, .app "RangeTo" [n]] =>
    some ("Hax.slice_toM", [a, n])
  | "index", [a, .app "RangeFrom" [n]] | "index_mut", [a, .app "RangeFrom" [n]] =>
    some ("Hax.slice_fromM", [a, n])
  | "index", [a, .app "Range" [lo, hi]] | "index_mut", [a, .app "Range" [lo, hi]] =>
    some ("Hax.slice_rangeM", [a, lo, hi])
  | "index", [_, .var "RangeFull"] | "index", [_, .app "RangeFull" []]
  | "index_mut", [_, .var "RangeFull"] | "index_mut", [_, .app "RangeFull" []] => none
  | "index", [a, i] | "index_mut", [a, i] => some ("Hax.indexM", [a, i])
  | "array_update", [_, _, _] => some ("Hax.array_updateM", args)
  | "vec_remove", [_, _] => some ("Hax.vec_removeM", args)
  | "slice_update", [_, _, _, _] => some ("Hax.slice_updateM", args)
  | "copy_from_slice", [_, _] => some ("Hax.copy_from_sliceM", args)
  | "unwrap", [_] => some ("Hax.unwrapM", args)
  | "expect", [_, _] => some ("Hax.expectM", args)
  | "assert", [_] => some ("Hax.assertM", args)
  | "assert_failed", [_, _, _, _] | "assert_failed'", [_, _, _, _] =>
    some ("Hax.assert_failedM", args)
  | _, _ =>
    if panicHeads.contains f then some ("Hax.panicM", []) else
    match f.splitOn "#", args with
    | [op, tag], [_, _] =>
      match checkedStem? op, intTag? tag with
      | some s, some (w, signed) => some (s!"Hax.{s}M_{if signed then "iw" else "w"} {w}", args)
      | _, _ => none
    | _, _ => none

/-! ## Monadic content and the effect closure -/

/-- The immediate subterms of an expression evaluated where the expression is; the body
    of a closure (`.lam`) is evaluated where the closure is called and is not one. -/
def kids : ImpExpr → List ImpExpr
  | .letBind _ v b => [v, b]
  | .app _ as => as
  | .tuple es => es
  | .proj e _ => [e]
  | .ifThenElse c t e => [c, t, e]
  | .match_ s arms => s :: arms.map (·.2)
  | .seq a b => [a, b]
  | .borrow e | .deref e | .assign _ e | .earlyReturn e | .questionMark e
  | .cfBreak e | .cfContinue e | .cfBreakContinue e | .typeAscription e _ => [e]
  | .forLoop _ lo hi b | .forLoopRev _ lo hi b | .forFold _ lo hi b | .forFoldRev _ lo hi b
  | .forFoldReturn _ lo hi b | .forFoldRevReturn _ lo hi b => [lo, hi, b]
  | .whileLoop c b | .whileFold c b | .whileFoldReturn c b => [c, b]
  | .break_ (some e) => [e]
  | _ => []

/-- Whether `e` has monadic content: a call of a partial operation (`guardedHead?`) or of
    a function of `monadic`, or a reference to a constant of `monadic`, outside a closure
    body other than the closure of a `map`. -/
partial def hasEffect (monadic : List String) (e : ImpExpr) : Bool :=
  match e with
  | .var v => monadic.contains v
  | .app "map" [it, .lam _ b] => hasEffect monadic it || hasEffect monadic b
  | .app f args =>
    (guardedHead? f args).isSome || monadic.contains f || args.any (hasEffect monadic)
  | _ => (kids e).any (hasEffect monadic)

/-- The emission of a function. -/
inductive Emission where
  /-- The total surface definition. -/
  | pure
  /-- A definition in `RustM`. -/
  | monadic
  deriving BEq, Inhabited, Repr

/-- Facts about the functions of a crate established before emission. -/
structure Facts where
  /-- Functions proved not to panic, with every function they call. -/
  noPanic : List String := []
  /-- Functions the verified range checker accepts at the full type ranges of their
      parameters, calling only such functions and functions of `specced` (`rangePlan`). -/
  total : List String := []
  /-- Functions the verified range checker accepts under the precondition of their summary,
      calling only functions of `total` and `specced` (`rangePlan`). -/
  specced : List String := []
  deriving Inhabited

/-- The emission of the function `name` with body `body` when the functions `monadic` are
    monadic: monadic when the body has monadic content, unless `facts` proves that the
    function does not panic or the verified range checker accepts it at the full type ranges
    of its parameters (`Facts.total`). -/
def emissionOf (facts : Facts) (monadic : List String) (name : String) (body : ImpExpr) :
    Emission :=
  if facts.noPanic.contains name || facts.total.contains name then .pure
  else if hasEffect monadic body then .monadic else .pure

/-! ## The decision of the verified range checker

The range checker `Range.checkT` (`HaxLean/Range/Check.lean`) is sound for `denote'` with the
Rust guards (`Range.checkT_rust_sound_defs`). Its candidates (parameter intervals, loop
annotations and the summaries of the crate's functions) come from an untrusted inference
(`HaxLean/RangeProbe.lean`); `rangePlan` runs the checker on each function's `TExpr` literal
and keeps the functions it accepts, so that the theorems `rangeBlock` prints are proved by
evaluating the checker on the same literals. Per function there are three outcomes: accepted
at the full type ranges of its parameters (`RangePlan.total`, printed total with `f_noPanic`),
accepted under the precondition of its summary (`RangePlan.specced`, printed in `RustM` beside
the total surface `f_pure`, with `f_noPanicOn`), or neither (monadic). -/

/-- The candidates of the range checker for the functions of a crate. -/
structure RangeInput where
  /-- The `TExpr` literal of each function (`f_texpr`). -/
  texprs : List (String × TExpr)
  /-- The parameters of each function, in order. -/
  params : List (String × List String)
  /-- The names of all functions and constants of the crate. -/
  crate : List String
  /-- For each function, the abstract values of its parameters at their full type ranges
      and the loop annotation. -/
  full : List (String × Range.AEnv × Range.AEnv) := []
  /-- The summaries `(g, (pre, post))` of `Range.checkSums`, callers first. -/
  sums : List (String × (List Range.AV × Range.AV)) := []
  /-- The loop annotation of each summarised function's body. -/
  sumAnns : List (String × Range.AEnv) := []
  /-- The groups of definitions that share a type (`effectClosure`). -/
  groups : List (List String) := []
  deriving Inhabited

/-- The functions the range checker accepts, each with the abstract environment of its
    parameters and its loop annotation, and the input with its summaries kept only when
    `Range.checkSums` accepts them. -/
structure RangePlan where
  /-- The candidates. -/
  input : RangeInput
  /-- Accepted at the full type ranges of the parameters. -/
  total : List (String × Range.AEnv × Range.AEnv) := []
  /-- Accepted under the precondition of the summary, and not in `total`. -/
  specced : List (String × Range.AEnv × Range.AEnv) := []
  deriving Inhabited

/-- The definitions of `inp` as `Range.checkSums` reads them: name, parameters, erased body. -/
def RangeInput.defs (inp : RangeInput) : List (String × List String × ImpExpr) :=
  inp.texprs.map fun (n, t) => (n, (inp.params.lookup n).getD [], t.erase)

/-- Whether the range checker accepts the literal `t` from `entry` with loop annotation `ann`
    and the summaries `sums`, refining by Boolean guards. -/
def rangeAccepts (sums : List (String × (List Range.AV × Range.AV))) (ann entry : Range.AEnv)
    (t : TExpr) : Bool :=
  (Range.checkT (Range.stdSpec sums ann true) entry t).isSome

/-- The functions and constants of `crate` that `e` calls or names. -/
def crateRefs (crate : List String) (e : ImpExpr) : List String :=
  ((collectAppCalls e).map (·.1) ++ collectFreeVars [] e).eraseDups.filter crate.contains

/-- The largest subset of `cands` whose members refer, among the functions of `crate`, only
    to members: rounds removing a member that refers to a non-member, at most `fuel`. -/
def closedSubset (refs : String → List String) (crate : List String) :
    Nat → List String → List String
  | 0, s => s
  | fuel + 1, s =>
    let s' := s.filter fun f => (refs f).all fun g => g == f || s.contains g || !crate.contains g
    if s'.length == s.length then s else closedSubset refs crate fuel s'

/-- The decision of the range checker on the functions of a crate. A function is a candidate
    of `total` when the checker accepts its literal at its full type ranges, and of `specced`
    when it has a summary and the checker accepts its literal from the parameters at the
    summary's precondition; both checks read calls of summarised functions through the
    summaries, so that their arguments lie in the preconditions. The summaries are dropped
    when `Range.checkSums` refuses them. Members of a group are not candidates. The plan
    keeps the largest set of candidates whose members refer to no other function of the
    crate outside the set. -/
def rangePlan (inp : RangeInput) : RangePlan :=
  let annOf (n : String) : Range.AEnv := (inp.sumAnns.lookup n).getD []
  let sums := if Range.checkSums inp.defs annOf true inp.sums then inp.sums else []
  let inp := { inp with sums, sumAnns := if sums.isEmpty then [] else inp.sumAnns }
  let grouped := inp.groups.flatten
  let tot := inp.texprs.filterMap fun (n, t) =>
    if grouped.contains n then none
    else match inp.full.lookup n with
      | some (entry, ann) => if rangeAccepts sums ann entry t then some (n, entry, ann) else none
      | none => none
  let spc := inp.texprs.filterMap fun (n, t) =>
    if grouped.contains n || (tot.lookup n).isSome then none
    else match sums.lookup n with
      | some (pre, _) =>
        let entry := ((inp.params.lookup n).getD []).zip pre
        if pre.length == ((inp.params.lookup n).getD []).length &&
            rangeAccepts sums (annOf n) entry t then some (n, entry, annOf n)
        else none
      | none => none
  let refsOf : List (String × List String) :=
    inp.texprs.map fun (n, t) => (n, crateRefs inp.crate t.erase)
  let keep := closedSubset (fun f => (refsOf.lookup f).getD []) inp.crate
    (inp.texprs.length + 1) (tot.map (·.1) ++ spc.map (·.1))
  { input := inp, total := tot.filter (keep.contains ·.1),
    specced := spc.filter (keep.contains ·.1) }

/-- The facts of a range plan: its `total` and `specced` functions. -/
def RangePlan.facts (p : RangePlan) (base : Facts := {}) : Facts :=
  { base with total := p.total.map (·.1), specced := p.specced.map (·.1) }

/-- The functions of `facts.specced` that are monadic in `monadic`: a total caller calls their
    total surface `f_pure` (`pureCalls`). -/
def Facts.pureCallees (facts : Facts) (monadic : List String) : List String :=
  facts.specced.filter monadic.contains

/-- `e` with each call of a function of `fs` replaced by a call of its total surface
    `f_pure`. -/
def pureCalls (fs : List String) (e : ImpExpr) : ImpExpr :=
  fs.foldl (fun e g => rewriteAppName g (g ++ "_pure") e) e

/-! ### Printing the range theorems -/

/-- The literal of an abstract value. -/
def avLit : Range.AV → String
  | .top => ".top"
  | .num (a, b) => s!".num ({a}, {b})"
  | .arr (a, b) => s!".arr ({a}, {b})"
  | .idx lo hi rs => s!".idx ({lo}) ({reprStr hi}) {reprStr rs}"
  | .rng (a, b) (c, d) => s!".rng ({a}, {b}) ({c}, {d})"

/-- The literal of a list of abstract values. -/
def avsLit (as : List Range.AV) : String := "[" ++ ", ".intercalate (as.map avLit) ++ "]"

/-- The literal of an abstract environment. -/
def aenvLit (Γ : Range.AEnv) : String :=
  "[" ++ ", ".intercalate (Γ.map fun (x, a) => s!"({x.quote}, {avLit a})") ++ "]"

/-- The name of a range declaration of the function `f`: `f_suffix`. -/
def rangeName (f suffix : String) : String := sanitizeName (f ++ suffix)

/-- The declarations of the crate that the range theorems share: the definitions as
    `Range.checkSums` reads them (`rangeDefs`), the summaries (`rangeSums`), their loop
    annotations (`rangeSumAnns`), and the theorem that `Range.checkSums` accepts them
    (`rangeSums_ok`), proved by evaluation. -/
def rangeHeader (inp : RangeInput) : String :=
  let defLit := ",\n    ".intercalate (inp.texprs.map fun (n, _) =>
    let ps := ", ".intercalate (((inp.params.lookup n).getD []).map String.quote)
    s!"({n.quote}, [{ps}], {rangeName n "_texpr"}.erase)")
  let sumLit := ",\n    ".intercalate (inp.sums.map fun (n, pre, post) =>
    s!"({n.quote}, ({avsLit pre}, {avLit post}))")
  let annLit := ",\n    ".intercalate (inp.sumAnns.map fun (n, a) => s!"({n.quote}, {aenvLit a})")
  "\n".intercalate [
    "/-- The definitions of the crate as the range checker reads them. -/",
    "def rangeDefs : List (String × List String × Hax.ImpExpr) :=",
    s!"  [{defLit}]",
    "",
    "/-- The summaries of the crate's functions, callers first. -/",
    "def rangeSums : List (String × (List Hax.Range.AV × Hax.Range.AV)) :=",
    s!"  [{sumLit}]",
    "",
    "/-- The loop annotations of the summarised bodies. -/",
    "def rangeSumAnns : List (String × Hax.Range.AEnv) :=",
    s!"  [{annLit}]",
    "",
    "/-- The summaries hold against the bodies of `rangeDefs`. -/",
    "theorem rangeSums_ok :",
    "    Hax.Range.checkSums rangeDefs (fun g => (rangeSumAnns.lookup g).getD []) true",
    "      rangeSums = true := by",
    "  native_decide"]

/-- The theorem `f_noPanic` (`onPre = false`) or `f_noPanicOn` (`onPre = true`): from every
    environment in the abstract environment `entry` of its parameters without control-flow
    values, the run of `f_texpr` under `denote'` with the table that fails where a Rust guard
    fails (`Range.guardBi Range.rustGuard`) is its run with the table, under the semantics
    of the heads (`Range.HeadSem`, `Range.LogicSem`) and the reading of the crate's
    definitions by the table (`Range.DefsSem`). Proved by `Range.checkT_rust_sound_defs` and
    evaluation of the checker on `f_texpr`. -/
def noPanicThm (f : String) (entry ann : Range.AEnv) (onPre : Bool) : String :=
  let entryN := rangeName f "_rangeEntry"
  let annN := rangeName f "_rangeAnn"
  let te := rangeName f "_texpr"
  let thm := rangeName f (if onPre then "_noPanicOn" else "_noPanic")
  let at_ := if onPre then "the precondition of its summary" else "the full type ranges"
  "\n".intercalate [
    s!"/-- The parameters of `{f}` at {at_}. -/",
    s!"def {entryN} : Hax.Range.AEnv := {aenvLit entry}",
    "",
    s!"/-- The loop annotation of `{f}`. -/",
    s!"def {annN} : Hax.Range.AEnv := {aenvLit ann}",
    "",
    s!"/-- `{f}` fails no Rust guard of its operations from parameters at {at_}. -/",
    s!"theorem {thm} {"{"}bi : Hax.Builtins} (hH : Hax.Range.HeadSem bi [])",
    "    (hL : Hax.Range.LogicSem bi) (hD : Hax.Range.DefsSem bi rangeDefs) (fuel : Nat)",
    s!"    {"{"}env : Hax.Env} (hΓ : Hax.Range.Sat {entryN} env)" ++
      " (hN : Hax.Env.NoControlFlow env) :",
    s!"    Hax.denote' (Hax.Range.guardBi Hax.Range.rustGuard bi) fuel {te}.erase env =",
    s!"      Hax.denote' bi fuel {te}.erase env := by",
    "  obtain ⟨⟨_, _⟩, h⟩ := Option.isSome_iff_exists.mp (show",
    s!"    (Hax.Range.checkT (Hax.Range.stdSpec rangeSums {annN} true) {entryN}",
    s!"      {te}).isSome = true by native_decide)",
    "  exact (Hax.Range.checkT_rust_sound_defs hH (fun _ => hL) hD rangeSums_ok h fuel hΓ hN).1"]

/-- The range declarations of a plan: `rangeHeader`, then `f_noPanic` for each function of
    `total` and `f_noPanicOn` for each of `specced`; empty when the plan accepts no
    function. -/
def rangeBlock (p : RangePlan) : String :=
  if p.total.isEmpty && p.specced.isEmpty then ""
  else "\n\n".intercalate (rangeHeader p.input ::
    p.total.map (fun (f, e, a) => noPanicThm f e a false) ++
    p.specced.map (fun (f, e, a) => noPanicThm f e a true))

/-- The monadic functions of the crate `defs`: the least set that contains every function
    whose `emissionOf` is monadic and, with one member of a group of `groups`, every
    member. A group is the method name of a trait together with the definitions of its
    `impl`s, which share the method's type. -/
def effectClosure (defs : List (String × ImpExpr)) (groups : List (List String) := [])
    (facts : Facts := {}) : List String :=
  go (defs.length + groups.length + 1) []
where
  /-- One round adds the functions of `emissionOf` and the groups they meet. -/
  step (cl : List String) : List String :=
    let direct := defs.filterMap fun (n, b) =>
      if cl.contains n || emissionOf facts cl n b == .monadic then some n else none
    (groups.foldl (fun acc g => if g.any acc.contains then acc ++ g else acc) direct).eraseDups
  /-- Rounds until the set is stable, at most `fuel`. -/
  go : Nat → List String → List String
    | 0, cl => cl
    | fuel + 1, cl =>
      let cl' := step cl
      if cl'.length == cl.length then cl' else go fuel cl'

/-- The functions of `names` from which a call path of `edges` leads back to the function
    itself. -/
def recursiveFns (edges : List (String × List String)) (names : List String) : List String :=
  names.filter fun f => (reach (edges.length + 1) ((edges.lookup f).getD []) []).contains f
where
  /-- The functions reachable from `todo`, by at most `fuel` rounds. -/
  reach : Nat → List String → List String → List String
    | 0, _, seen => seen
    | fuel + 1, todo, seen =>
      let new := todo.filter (!seen.contains ·)
      if new.isEmpty then seen
      else reach fuel (new.flatMap fun g => (edges.lookup g).getD []) (seen ++ new)

/-! ## A-normal rendering -/

/-- The rendering context: the monadic functions and the Bool-valued functions. -/
structure Ctx where
  /-- The functions emitted in `RustM`. -/
  monadic : List String
  /-- The functions that return `Bool` (`toLean`'s `boolNames`). -/
  boolNames : List String := []

/-- The rendering monad: a counter for fresh names. -/
abbrev M := StateM Nat

/-- A fresh variable name. -/
def fresh : M String := modifyGet fun n => (s!"_m{n}", n + 1)

/-- The right-hand side of a binding: a pure expression or a rendered monadic term. -/
inductive Rhs where
  /-- A pure expression. -/
  | pure (e : ImpExpr)
  /-- A rendered term of type `RustM T`. -/
  | bind (s : String)
  deriving Inhabited

/-- The lines `ls` as one string. -/
def lines (ls : List String) : String := "\n".intercalate (ls.filter (!·.isEmpty))

/-- The name of the hole of `prefixOf`. -/
def holeName : String := "_hax_monadic_hole"

/-- The text that `toLean` prints before the hole `holeName`, when the hole is the last
    line at indentation `lvl` and occurs once. -/
def prefixOf (s : String) (lvl : Nat) : Option String :=
  let suffix := s!"{indent lvl}{holeName}"
  if s.endsWith suffix && (s.splitOn holeName).length == 2 then
    let p := String.ofList (s.toList.take (s.length - suffix.length))
    some (String.ofList (p.toList.reverse.dropWhile (· == '\n')).reverse)
  else none

/-- The condition of an `if` as `toLean` prints it. -/
def condStr (bn : List String) (c : ImpExpr) : String :=
  let s := toLean (.ifThenElse c (.var "_hax_t") (.var "_hax_e")) 0 bn
  let first := ((s.splitOn "\n").headD "").toList.dropWhile (· == ' ')
  String.ofList ((first.drop 3).take (first.length - 8))

/-- The pattern that rebinds the variables `names`: `_`, `x` or `(x, y)`. -/
def rebindPat (names : List String) : String :=
  match names with
  | [] => "_"
  | [a] => sanitizeName a
  | _ => s!"({", ".intercalate (names.map sanitizeName)})"

/-- A pure value after `let x :=`, on the same line when it is a leaf. -/
def valStr (bn : List String) (lvl : Nat) (e : ImpExpr) : String :=
  if isLeafExpr e then toLean e 0 bn else s!"\n{toLean e (lvl + 1) bn}"

/-- An application `g a₁ … aₙ` of a rendered head to arguments. -/
def applyStr (bn : List String) (g : String) (args : List ImpExpr) : String :=
  String.join (g :: args.map fun a => " " ++ parensIf (toLean a 0 bn) (!isAtom a))

/-- A pure expression as the last element of a `do` sequence. -/
def pureTail (bn : List String) (lvl : Nat) (e : ImpExpr) : String :=
  if isLeafExpr e then s!"{indent lvl}pure {parensIf (toLean e 0 bn) (!isAtom e)}"
  else
    let s := toLean e (lvl + 1) bn
    let s := if isLeafExpr e then s!"{indent (lvl + 1)}{s}" else s
    s!"{indent lvl}pure <|\n{s}"

/-- Whether every tail of `e` is a control-flow value. -/
partial def cfTail : ImpExpr → Bool
  | .cfBreak _ | .cfContinue _ | .cfBreakContinue _ => true
  | .letBind _ _ b => cfTail b
  | .seq _ b => cfTail b
  | .ifThenElse _ t e => cfTail t && cfTail e
  | .match_ _ arms => arms.all (fun (_, b) => cfTail b)
  | _ => false

/-- The value of a binding that is a type ascription, without it. -/
def unwrapAsc : ImpExpr → ImpExpr
  | .typeAscription e _ => e
  | e => e

/-- The accumulators of a `while` body: `extractWhileAccumulators` without the variables
    the body binds. -/
def whileAccs (body : ImpExpr) : List String :=
  let localVars := collectLetBindVars body
  (extractWhileAccumulators body).filter fun a => !localVars.contains a

mutual

/-- Bind the monadic subterms of `e`, left to right, by lines at indentation `lvl`; the
    result is those lines and the pure residue of `e`. -/
partial def hoist (cx : Ctx) (lvl : Nat) (e : ImpExpr) : M (List String × ImpExpr) := do
  if !hasEffect cx.monadic e then return ([], e)
  match e with
  | .var v =>
    let x ← fresh
    return ([s!"{indent lvl}let {x} ← {sanitizeName v}"], .var x)
  | .app f args =>
    let (ss, r) ← hoistCall cx lvl f args
    match r with
    | .pure e' => return (ss, e')
    | .bind s =>
      let x ← fresh
      return (ss ++ [s!"{indent lvl}let {x} ← {s}"], .var x)
  | .tuple es => let (ss, es') ← hoistList cx lvl es; return (ss, .tuple es')
  | .proj a i => let (ss, a') ← hoist cx lvl a; return (ss, .proj a' i)
  | .typeAscription a t => let (ss, a') ← hoist cx lvl a; return (ss, .typeAscription a' t)
  | .cfBreak a => let (ss, a') ← hoist cx lvl a; return (ss, .cfBreak a')
  | .cfContinue a => let (ss, a') ← hoist cx lvl a; return (ss, .cfContinue a')
  | .cfBreakContinue a => let (ss, a') ← hoist cx lvl a; return (ss, .cfBreakContinue a')
  | .borrow a => let (ss, a') ← hoist cx lvl a; return (ss, .borrow a')
  | .deref a => let (ss, a') ← hoist cx lvl a; return (ss, .deref a')
  | .ifThenElse c t f =>
    if !hasEffect cx.monadic t && !hasEffect cx.monadic f then
      let (ss, c') ← hoist cx lvl c
      return (ss, .ifThenElse c' t f)
    else bindTerm cx lvl e
  | .match_ s arms =>
    if arms.all (fun (_, b) => !hasEffect cx.monadic b) then
      let (ss, s') ← hoist cx lvl s
      return (ss, .match_ s' arms)
    else bindTerm cx lvl e
  | _ => bindTerm cx lvl e

/-- `hoist` on each expression of a list, left to right. -/
partial def hoistList (cx : Ctx) (lvl : Nat) (es : List ImpExpr) :
    M (List String × List ImpExpr) := do
  let mut ss : List String := []
  let mut out : List ImpExpr := []
  for e in es do
    let (s, e') ← hoist cx lvl e
    ss := ss ++ s
    out := out ++ [e']
  return (ss, out)

/-- Bind a whole expression, rendered as a `do` term, to a fresh variable. -/
partial def bindTerm (cx : Ctx) (lvl : Nat) (e : ImpExpr) : M (List String × ImpExpr) := do
  let t ← renderTerm cx lvl e
  let x ← fresh
  return ([s!"{indent lvl}let {x} ← {t}"], .var x)

/-- An expression as a term of type `RustM T`: `do` followed by its `renderM` lines. -/
partial def renderTerm (cx : Ctx) (lvl : Nat) (e : ImpExpr) : M String := do
  return s!"do\n{← renderM cx (lvl + 1) e}"

/-- The call `f args`: its arguments hoisted, and its value, a monadic term when `f` is a
    partial operation or a monadic function. -/
partial def hoistCall (cx : Ctx) (lvl : Nat) (f : String) (args : List ImpExpr) :
    M (List String × Rhs) := do
  let bn := cx.boolNames
  match f, args with
  | "map", [it, .lam [p] b] =>
    if hasEffect cx.monadic b then
      let (ss, it') ← hoist cx lvl it
      let bs ← renderM cx (lvl + 2) b
      return (ss, .bind
        s!"({toLean it' 0 bn}).mapM (fun {sanitizeName p} => do\n{bs})")
    else
      let (ss, it') ← hoist cx lvl it
      return (ss, .pure (.app f [it', .lam [p] b]))
  | "_HAX_MERGE", [inner] =>
    let (ss, x) ← bindTerm cx lvl inner
    return (ss, .pure (.app "_HAX_MERGE" [x]))
  | _, _ =>
    let (ss, args') ← hoistList cx lvl args
    match guardedHead? f args' with
    | some (g, gargs) => return (ss, .bind (applyStr bn g gargs))
    | none =>
      if cx.monadic.contains f then return (ss, .bind (toLean (.app f args') 0 bn))
      else return (ss, .pure (.app f args'))

/-- The value of a binding: its monadic subterms hoisted, and the value itself, a monadic
    term when it is a monadic call or a compound expression with monadic branches. -/
partial def hoistRhs (cx : Ctx) (lvl : Nat) (e : ImpExpr) : M (List String × Rhs) := do
  if !hasEffect cx.monadic e then return ([], .pure e)
  match e with
  | .var v => return ([], .bind (sanitizeName v))
  | .app f args => hoistCall cx lvl f args
  | .typeAscription (.app f args) t =>
    let (ss, r) ← hoistCall cx lvl f args
    match r with
    | .pure e' => return (ss, .pure (.typeAscription e' t))
    | .bind s => return (ss, .bind s!"({s} : RustM ({t}))")
  | .letBind .. | .seq .. | .forFold .. | .forFoldRev .. | .forFoldReturn ..
  | .forFoldRevReturn .. | .whileFold .. | .whileFoldReturn .. =>
    return ([], .bind (← renderTerm cx lvl e))
  | .ifThenElse _ t f =>
    if hasEffect cx.monadic t || hasEffect cx.monadic f then
      return ([], .bind (← renderTerm cx lvl e))
    else
      let (ss, r) ← hoist cx lvl e
      return (ss, .pure r)
  | .match_ _ arms =>
    if arms.any (fun (_, b) => hasEffect cx.monadic b) then
      return ([], .bind (← renderTerm cx lvl e))
    else
      let (ss, r) ← hoist cx lvl e
      return (ss, .pure r)
  | _ =>
    let (ss, r) ← hoist cx lvl e
    return (ss, .pure r)

/-- The lines of a `do` sequence at indentation `lvl` whose value is the value of `e`. -/
partial def renderM (cx : Ctx) (lvl : Nat) (e : ImpExpr) : M String := do
  let bn := cx.boolNames
  if !hasEffect cx.monadic e then return pureTail bn lvl e
  match e with
  | .letBind n v body => renderLet cx lvl n v body
  | .seq a b => renderSeq cx lvl a b
  | .ifThenElse c t f =>
    let (ss, c') ← hoist cx lvl c
    return lines (ss ++ [← renderIf cx lvl (condStr bn c') t f])
  | .match_ s arms => renderMatch cx lvl s arms
  | .forFold .. | .forFoldRev .. | .forFoldReturn .. | .forFoldRevReturn ..
  | .whileFold .. | .whileFoldReturn .. =>
    let (ss, t) ← foldTerm cx lvl e
    return lines (ss ++ [s!"{indent lvl}{t}"])
  | _ =>
    let (ss, r) ← hoistRhs cx lvl e
    let last := match r with
      | .bind s => s!"{indent lvl}{s}"
      | .pure p => pureTail bn lvl p
    return lines (ss ++ [last])

/-- The value of `e` discarded: its lines, then `pure ()`. -/
partial def discardM (cx : Ctx) (lvl : Nat) (e : ImpExpr) : M String := do
  if !hasEffect cx.monadic e then return s!"{indent lvl}pure ()"
  let (ss, r) ← hoistRhs cx lvl e
  let l := match r with
    | .bind s => if s == "Hax.panicM" then s!"{indent lvl}let _ ← (Hax.panicM : RustM Unit)"
      else s!"{indent lvl}let _ ← {s}"
    | .pure _ => ""
  return lines (ss ++ [l, s!"{indent lvl}pure ()"])

/-- `let n := v; body`. -/
partial def renderLet (cx : Ctx) (lvl : Nat) (n : String) (v body : ImpExpr) :
    M String := do
  let bn := cx.boolNames
  let ind := indent lvl
  match v with
  | .cfBreak _ | .cfBreakContinue _ =>
    if n.startsWith "_" then return ← renderM cx lvl (markProjChain n body)
  | _ => pure ()
  let body := markProjChain n body
  -- A binding whose value is a `match` with an early-return arm: the continuation moves
  -- into the other arms (as `toLean` does).
  match unwrapAsc v with
  | .match_ scrut arms =>
    if arms.any (fun (_, b) => hasCfBreak b) then
      let loop := cfTail body
      let arms' := arms.map fun (p, a) =>
        if hasCfBreak a then (p, if loop then a else (extractCfBreak a).getD a)
        else (p, .letBind n a body)
      return ← renderM cx lvl (.match_ scrut arms')
  | _ => pure ()
  if !hasEffect cx.monadic v && n.startsWith "_assign" then
    if let some p := prefixOf (toLean (.letBind n v (.var holeName)) lvl bn) lvl then
      return lines [p, ← renderM cx lvl body]
  if n.startsWith "_assign" && body == .var n then
    return ← discardM cx lvl v
  match extractTupleDestr n body with
  | some (names, rest) =>
    let (ss, r) ← hoistRhs cx lvl v
    let nonWild := (names.zip (List.range names.length)).filter fun (nm, _) => nm != "_"
    let bindLines : List String ← match nonWild with
      | [(nm, idx)] =>
        let path := projPath idx names.length
        match r with
        | .pure p => pure [s!"{ind}let {sanitizeName nm} := ({toLean p 0 bn}){path}"]
        | .bind s =>
          let x ← fresh
          pure [s!"{ind}let {x} ← {s}", s!"{ind}let {sanitizeName nm} := {x}{path}"]
      | _ =>
        let pat := ", ".intercalate (names.map sanitizeName)
        match r with
        | .pure p => pure [s!"{ind}let ({pat}) := {toLean p 0 bn}"]
        | .bind s => pure [s!"{ind}let ({pat}) ← {s}"]
    return lines (ss ++ bindLines ++ [← renderM cx lvl rest])
  | none =>
    let (ss, r) ← hoistRhs cx lvl v
    let l := match r with
      | .pure p => s!"{ind}let {sanitizeName n} := {valStr bn lvl p}"
      | .bind s => s!"{ind}let {sanitizeName n} ← {s}"
    return lines (ss ++ [l, ← renderM cx lvl body])

/-- `a; b`. -/
partial def renderSeq (cx : Ctx) (lvl : Nat) (a b : ImpExpr) : M String := do
  let bn := cx.boolNames
  let ind := indent lvl
  match a with
  | .seq x y => return ← renderSeq cx lvl x (.seq y b)
  | .unitVal | .var _ | .cfBreak _ | .cfContinue _ | .cfBreakContinue _ =>
    return ← renderM cx lvl b
  | .letBind n v body => return ← renderLet cx lvl n v (.seq body b)
  | _ => pure ()
  if b == .unitVal then return ← renderM cx lvl a
  -- A statement without monadic content: `toLean`'s rendering of it, when the rest of the
  -- block follows it in straight-line form.
  if !hasEffect cx.monadic a then
    if let some p := prefixOf (toLean (.seq a (.var holeName)) lvl bn) lvl then
      return lines [p, ← renderM cx lvl b]
  match a with
  | .forFold _ _ _ fb | .forFoldRev _ _ _ fb => seqFold cx lvl a fb b false
  | .whileFold _ fb => seqFold cx lvl a fb b true
  | .forFoldReturn _ _ _ fb | .forFoldRevReturn _ _ _ fb | .whileFoldReturn _ fb =>
    if hasCfBreak fb then seqFoldReturn cx lvl a fb b
    else seqFold cx lvl a fb b (match a with | .whileFoldReturn .. => true | _ => false)
  | .ifThenElse c t f =>
    if isCfGuardIf t f then return ← renderM cx lvl (inlineRestIntoCfGuard b a)
    match extractCfBreak t, extractCfBreak f with
    | some rv, none =>
      let t' := match rv with | .cfBreak _ => .cfBreak rv | _ => stripCfBreak t
      renderM cx lvl (.ifThenElse c t' b)
    | none, some rv =>
      let f' := match rv with | .cfBreak _ => .cfBreak rv | _ => stripCfBreak f
      renderM cx lvl (.ifThenElse c b f')
    | _, _ =>
      if f == .unitVal && cfTail t then renderM cx lvl (.ifThenElse c t b)
      else if t == .unitVal && cfTail f then renderM cx lvl (.ifThenElse c b f)
      else
        let names := ((extractCondMutations t ++ extractCondMutations f).map (·.1)
          |>.filter (!·.startsWith "_assign")).eraseDups
        let tup := if names.isEmpty then ImpExpr.unitVal else accTuple names
        let (ss, c') ← hoist cx lvl c
        let ifS ← renderIf cx (lvl + 1) (condStr bn c') (replaceTail tup t) (replaceTail tup f)
        return lines (ss ++ [s!"{ind}let {rebindPat names} ← do", ifS, ← renderM cx lvl b])
  | .match_ s arms =>
    let names := matchArmMutations [] (freeVars s) arms
    let tup := if names.isEmpty then ImpExpr.unitVal else accTuple names
    let m ← renderMatch cx (lvl + 1) s (arms.map fun (p, x) => (p, replaceTail tup x))
    return lines [s!"{ind}let {rebindPat names} ← do", m, ← renderM cx lvl b]
  | _ =>
    if hasEffect cx.monadic a then
      return lines [← discardStmt cx lvl a, ← renderM cx lvl b]
    else
      return lines [s!"{ind}let _ := {valStr bn lvl a}", ← renderM cx lvl b]

/-- The lines of a statement whose value is discarded. -/
partial def discardStmt (cx : Ctx) (lvl : Nat) (a : ImpExpr) : M String := do
  let (ss, r) ← hoistRhs cx lvl a
  let l := match r with
    | .bind s => if s == "Hax.panicM" then s!"{indent lvl}let _ ← (Hax.panicM : RustM Unit)"
      else s!"{indent lvl}let _ ← {s}"
    | .pure _ => ""
  return lines (ss ++ [l])

/-- `if c then t else f` with the condition rendered, each branch a `do` sequence. -/
partial def renderIf (cx : Ctx) (lvl : Nat) (cond : String) (t f : ImpExpr) : M String := do
  let ind := indent lvl
  let ind1 := indent (lvl + 1)
  let cont := s!"{ind1}pure (Hax.cfContinue ())"
  let tS ←
    if t == .unitVal && hasControlFlowNodes f then pure cont
    else if f == .unitVal && !hasControlFlowNodes t && t != .unitVal then discardM cx (lvl + 1) t
    else renderM cx (lvl + 1) t
  let fS ← if f == .unitVal && hasControlFlowNodes t then pure cont else renderM cx (lvl + 1) f
  return s!"{ind}if {cond} then\n{tS}\n{ind}else\n{fS}"

/-- `match s with arms`, each arm a `do` sequence; arms that all bind constants are the
    `Hax.beq` chain of `toLean`. -/
partial def renderMatch (cx : Ctx) (lvl : Nat) (s : ImpExpr) (arms : List (ImpPat × ImpExpr)) :
    M String := do
  let bn := cx.boolNames
  let ind := indent lvl
  let (ss, s') ← hoist cx lvl s
  let allVarPats := arms.all fun (p, _) => match p with
    | .varPat _ | .wildcard => true
    | _ => false
  if allVarPats && arms.length > 1 then
    let scrut := parensIf (toLean s' 0 bn) (!isAtom s')
    let rec chain (l : Nat) : List (ImpPat × ImpExpr) → M String
      | [] => pure s!"{indent l}pure ()"
      | [(_, body)] => renderM cx l body
      | (.varPat n, body) :: rest => do
        let thn ← renderM cx (l + 1) body
        let els ← chain (l + 1) rest
        return s!"{indent l}if Hax.beq {scrut} {sanitizeName n} then\n{thn}\n{indent l}else\n{els}"
      | (_, body) :: _ => renderM cx l body
    return lines (ss ++ [← chain lvl arms])
  else
    let mut armStrs : List String := []
    for (p, body) in arms do
      armStrs := armStrs ++ [s!"{ind}| {patToLean p} =>\n{← renderM cx (lvl + 1) body}"]
    return lines (ss ++ [s!"{ind}match {toLean s' 0 bn} with"] ++ armStrs)

/-- A loop: the lines hoisting its bounds, and the monadic loop term, whose body lines are
    at indentation `lvl + 1`. -/
partial def foldTerm (cx : Ctx) (lvl : Nat) (e : ImpExpr) : M (List String × String) := do
  let bn := cx.boolNames
  let ind1 := indent (lvl + 1)
  let counted (v : String) (lo hi : ImpExpr) (rev : Bool) (k : String → String → String →
      String → M String) : M (List String × String) := do
    let (s1, lo') ← hoist cx lvl lo
    let (s2, hi') ← hoist cx lvl hi
    let loS := parensIf (toLean lo' 0 bn) (!isAtom lo')
    let hiS := parensIf (toLean hi' 0 bn) (!isAtom hi')
    let ctr := if rev then "_k" else sanitizeName v
    let revLine := if rev then s!"{ind1}let {sanitizeName v} := {loS} + {hiS} - 1 - _k" else ""
    let t ← k loS hiS ctr revLine
    return (s1 ++ s2, t)
  match e with
  | .forFold v lo hi body | .forFoldRev v lo hi body =>
    let rev := match e with | .forFoldRev .. => true | _ => false
    let accs := extractAccumulators body
    let (initS, paramS) := accStrings accs
    counted v lo hi rev fun loS hiS ctr revLine => do
      let head (f : String) := s!"Hax.{f} {loS} {hiS} {initS} fun {ctr} {paramS} => do\n"
      if !hasSurfaceControlFlow body && !accs.isEmpty then
        let body' := wrapTailFoldForOuterAccs accs
          (wrapTailForFoldWithMerge (simplifyFoldBody (transformFoldBody accs body)))
        return head "foldRangeM" ++ lines [revLine, ← renderM cx (lvl + 1) body']
      else if accs.isEmpty && !hasSurfaceControlFlow body then
        return head "foldRangeM" ++ lines [revLine, ← discardM cx (lvl + 1) body]
      else
        let body' := encodeForFoldBody (accTuple accs) (distributeStmtCF body)
        return head "forFoldM" ++ lines [revLine, ← renderM cx (lvl + 1) body']
  | .forFoldReturn v lo hi body | .forFoldRevReturn v lo hi body =>
    let rev := match e with | .forFoldRevReturn .. => true | _ => false
    let accs := extractAccumulators body
    let (initS, paramS) := accStrings accs
    let body' := encodeReturnFoldBody (accTuple accs) (distributeStmtCF body)
    counted v lo hi rev fun loS hiS ctr revLine => do
      return s!"Hax.forFoldReturnM {loS} {hiS} {initS} fun {ctr} {paramS} => do\n"
        ++ lines [revLine, ← renderM cx (lvl + 1) body']
  | .whileFold c body | .whileFoldReturn c body =>
    let ret := match e with | .whileFoldReturn .. => true | _ => false
    let accs := if ret then
        let l := collectLetBindVars body
        (extractAccumulators body).filter fun a => !l.contains a
      else whileAccs body
    let (initS, paramS) := accStrings accs
    let body' := if ret then encodeReturnFoldBody (accTuple accs) (distributeStmtCF body)
      else encodeForFoldBody (accTuple accs) (distributeStmtCF body)
    let condS ←
      if hasEffect cx.monadic c then
        pure s!"(fun {paramS} => do\n{← renderM cx (lvl + 2) c})"
      else pure s!"(fun {paramS} => pure {parensIf (toLean c 0 bn) (!isAtom c)})"
    let fn := if ret then "Hax.whileFoldReturnM" else "Hax.whileFoldM"
    return ([], s!"{fn} {initS} {condS} fun {paramS} => do\n{← renderM cx (lvl + 1) body'}")
  | _ =>
    let (ss, r) ← hoistRhs cx lvl e
    match r with
    | .bind s => return (ss, s)
    | .pure p => return (ss, s!"pure {parensIf (toLean p 0 bn) (!isAtom p)}")

/-- A loop followed by `tail`: the loop's result rebinds its accumulators (as `toLean`'s
    `seqFold` and `seqWhileFold` do), `_wf.merge` for a loop with control flow. -/
partial def seqFold (cx : Ctx) (lvl : Nat) (loop body tail : ImpExpr) (isWhile : Bool) :
    M String := do
  let bn := cx.boolNames
  let ind := indent lvl
  let accs := if isWhile then whileAccs body else extractAccumulators body
  let isCf := isWhile || hasSurfaceControlFlow body
  let pre := (accInitOverrides accs body (foldVars loop)).map fun (n, x) =>
    s!"{ind}let {sanitizeName n} := {toLean x 0 bn}"
  let (ss, t) ← foldTerm cx lvl loop
  let head := pre ++ ss
  match accs with
  | [] => return lines (head ++ [s!"{ind}let _ ← {t}", ← renderM cx lvl tail])
  | [acc] =>
    if tail == .var acc then
      if isCf then return lines (head ++ [s!"{ind}let _wf ← {t}", s!"{ind}pure _wf.merge"])
      else return lines (head ++ [s!"{ind}{t}"])
    else if isCf then
      return lines (head ++ [s!"{ind}let _wf ← {t}",
        s!"{ind}let {sanitizeName acc} := _wf.merge", ← renderM cx lvl tail])
    else return lines (head ++ [s!"{ind}let {sanitizeName acc} ← {t}", ← renderM cx lvl tail])
  | _ =>
    if isCf then
      return lines (head ++ [s!"{ind}let _wf ← {t}", s!"{ind}let {rebindPat accs} := _wf.merge",
        ← renderM cx lvl tail])
    else return lines (head ++ [s!"{ind}let {rebindPat accs} ← {t}", ← renderM cx lvl tail])

/-- A loop with early return followed by `tail` (as `toLean`'s `seqFoldReturn`): the
    early-return arm returns, or propagates the return to an enclosing loop. -/
partial def seqFoldReturn (cx : Ctx) (lvl : Nat) (loop body tail : ImpExpr) : M String := do
  let bn := cx.boolNames
  let ind := indent lvl
  let ind1 := indent (lvl + 1)
  let accs := extractAccumulators body
  let pre := (accInitOverrides accs body (foldVars loop)).map fun (n, x) =>
    s!"{ind}let {sanitizeName n} := {toLean x 0 bn}"
  let (ss, t) ← foldTerm cx lvl loop
  let enclosed := cfTail tail
  if accs.isEmpty then
    let brk := if enclosed then "pure (Hax.cfBreak (Hax.cfBreak _v))" else "pure _v"
    return lines (pre ++ ss ++ [s!"{ind}let _fr ← {t}",
      s!"{ind}match (show ControlFlow _ (ControlFlow Unit _) from _fr) with",
      s!"{ind}| .Break _v => {brk}", s!"{ind}| .Continue _ =>", ← renderM cx (lvl + 1) tail])
  else
    let brk := if !enclosed then "pure _v"
      else if hasDoubleCfBreak tail then "pure (Hax.cfBreak (Hax.cfBreak _v))"
      else "pure (Hax.cfBreak _v)"
    let scrut := if hasCfBreakContinue body then "_fr"
      else "(show ControlFlow _ (ControlFlow Unit _) from _fr)"
    let tailS ← renderM cx (lvl + 2) tail
    return lines (pre ++ ss ++ [s!"{ind}let _fr ← {t}", s!"{ind}match {scrut} with",
      s!"{ind}| .Break _v => {brk}", s!"{ind}| .Continue _cf =>", s!"{ind1}match _cf with",
      s!"{ind1}| .Continue {rebindPat accs} =>", tailS, s!"{ind1}| .Break _ =>", tailS])

end

/-- The body of a monadic definition: `do` and the `renderM` lines of `body`. -/
def renderBody (cx : Ctx) (body : ImpExpr) : String :=
  s!"{indent 1}do\n{(renderM cx 2 body).run' 0}"

/-! ## Checks of the range decision -/

namespace RangeExamples

/-- `[u8; 16]`. -/
def a16 : ImpType := .array (.uint .w8) 16
/-- A variable node. -/
def v (x : String) (t : ImpType) : TExpr := .mk (.var x) t
/-- A call node. -/
def ap (f : String) (as : List TExpr) (t : ImpType) : TExpr := .mk (.app f as) t
/-- A parameter binding `let x := x` in front of `b`. -/
def prm (x : String) (t : ImpType) (b : TExpr) : TExpr := .mk (.letBind x (v x t) b) b.ty

/-- `h(a, i) = a[i]`. -/
def hF : TExpr := prm "a" a16 (prm "i" (.uint .wsize)
  (ap "index" [v "a" a16, v "i" (.uint .wsize)] (.uint .w8)))
/-- `k(a) = for j in 0..16 { h(a, j) }`. -/
def kF : TExpr := prm "a" a16 (.mk (.forFold "j" (.mk (.lit (.int 0)) (.uint .wsize))
  (.mk (.lit (.int 16)) (.uint .wsize))
  (ap "h" [v "a" a16, v "j" (.uint .wsize)] (.uint .w8))) .unit)
/-- `x + 1` on `x : u8`. -/
def addF : TExpr := prm "x" (.uint .w8)
  (ap "Add#8" [v "x" (.uint .w8), .mk (.lit (.int 1)) (.uint .w8)] (.uint .w8))
/-- `m(a, i) = h(a, i)`, calling `h` outside its precondition. -/
def mF : TExpr := prm "a" a16 (prm "i" (.uint .wsize)
  (ap "h" [v "a" a16, v "i" (.uint .wsize)] (.uint .w8)))

/-- The candidates for `h`, `k`, `add` and `m`: type ranges, and the summary of `h` at the
    interval of its call site in `k`. -/
def input : RangeInput where
  texprs := [("h", hF), ("k", kF), ("add", addF), ("m", mF)]
  params := [("h", ["a", "i"]), ("k", ["a"]), ("add", ["x"]), ("m", ["a", "i"])]
  crate := ["h", "k", "add", "m"]
  full := [("h", [("a", .arr (16, 16)), ("i", .num (0, 2 ^ 64 - 1))], []),
    ("k", [("a", .arr (16, 16))], []), ("add", [("x", .num (0, 255))], []),
    ("m", [("a", .arr (16, 16)), ("i", .num (0, 2 ^ 64 - 1))], [])]
  sums := [("h", ([.arr (16, 16), .num (0, 15)], .top))]

/-- Outcome 1 for `k`, which calls `h` inside its precondition; outcome 2 for `h`; outcome 3
    for `x + 1` on `u8` and for `m`, which calls `h` at the full range of `i`. -/
def chkPlan : Bool :=
  let p := rangePlan input
  p.total.map (·.1) == ["k"] && p.specced.map (·.1) == ["h"]

/-- Under the plan's facts, `k` is printed total although it calls the monadic `h`, and calls
    `h_pure`; `h`, `add` and `m` are monadic. -/
def chkEmission : Bool :=
  let facts := (rangePlan input).facts
  let defs := input.texprs.map fun (n, t) => (n, t.erase)
  let cl := effectClosure defs [] facts
  cl == ["h", "add", "m"] && emissionOf facts cl "k" kF.erase == .pure &&
    facts.pureCallees cl == ["h"] &&
    (collectAppCalls (pureCalls (facts.pureCallees cl) kF.erase)).map (·.1) == ["h_pure"]

/-- A plan whose summaries `Range.checkSums` refuses keeps none of them, and `h` is not
    accepted. -/
def chkBadSums : Bool :=
  let p := rangePlan { input with sums := [("h", ([.arr (16, 16), .num (0, 16)], .top))] }
  p.input.sums.isEmpty && p.specced.isEmpty && p.total.map (·.1) == []

end RangeExamples

end Hax.MonadicEmit
