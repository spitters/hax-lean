/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import HaxLean.AST
public import HaxLean.AST
public meta import HaxLean.Value
public import HaxLean.Value
public meta import HaxLean.Features
public import HaxLean.Features
public meta import HaxLean.Semantics
public import HaxLean.Semantics
public meta import HaxLean.Phase.DropReferences
public import HaxLean.Phase.DropReferences
public meta import HaxLean.Phase.LocalMutation
public import HaxLean.Phase.LocalMutation
public meta import HaxLean.Phase.FunctionalizeLoops
public import HaxLean.Phase.FunctionalizeLoops
public meta import HaxLean.Phase.CfIntoMonads
public import HaxLean.Phase.CfIntoMonads
public meta import HaxLean.Pipeline
public import HaxLean.Pipeline
public meta import HaxLean.ThreadMutations
public import HaxLean.ThreadMutations
public meta import HaxLean.PrettyPrint
public import HaxLean.PrettyPrint
public meta import HaxLean.Json.AdapterProbes
public import HaxLean.Json.AdapterProbes
public meta import HaxLean.PrettyPrintT
public import HaxLean.PrettyPrintT
public meta import HaxLean.EmitterRegressions
public import HaxLean.EmitterRegressions

/-!
# Test Programs

Concrete `ImpExpr` programs inspired by the hax test suite, testing each
compiler phase. Each test verifies:
1. Feature predicates via boolean checkers
2. Phase transformations produce expected output properties
3. Denotational semantics produce expected values

## Test Programs (from hax tests)

| Test | Rust equivalent | Exercises |
|------|----------------|-----------|
| `simpleMut` | `let mut x = 0; x = 5; x` | assign |
| `sumRange` | `for i in 0..n { acc += i; }` | forLoop, assign |
| `earlyRet` | `if x > 0 { return x; } 0` | earlyReturn |
| `borrowDeref` | `let y = &x; *y + 1` | borrow, deref |
| `loopBreak` | `for i in 0..10 { if i > 5 { break; } }` | forLoop, break_ |
| `questionMark` | `let v = x?; Ok(v + 1)` | questionMark |
| `whileLoop` | `while cond { body; }` | whileLoop |
| `combined` | mutation + loop + early return | all features |
-/

@[expose] public section

namespace Hax.Tests

open Hax

/-! ## Test Programs -/

/-- `let mut x = 0; x = 5; x` → should evaluate to 5 -/
def simpleMut : ImpExpr :=
  .letBind "x" (.lit (.int 0))
    (.seq (.assign "x" (.lit (.int 5)))
      (.var "x"))

/-- `let y = &x; *y + 1` where x = 10 → should evaluate to 11 -/
def borrowDeref : ImpExpr :=
  .letBind "y" (.borrow (.var "x"))
    (.app "add" [.deref (.var "y"), .lit (.int 1)])

/-- `if x > 0 { return x; } 0` -/
def earlyRet : ImpExpr :=
  .seq
    (.ifThenElse
      (.app "gt" [.var "x", .lit (.int 0)])
      (.earlyReturn (.var "x"))
      .unitVal)
    (.lit (.int 0))

/-- `for i in 0..n { acc = acc + i; } acc`
    with acc initialized to 0. -/
def sumRange : ImpExpr :=
  .letBind "acc" (.lit (.int 0))
    (.seq
      (.forLoop "i" (.lit (.int 0)) (.var "n")
        (.assign "acc" (.app "add" [.var "acc", .var "i"])))
      (.var "acc"))

/-- `for i in 0..10 { if i > 5 { break; } } 0` -/
def loopBreak : ImpExpr :=
  .seq
    (.forLoop "i" (.lit (.int 0)) (.lit (.int 10))
      (.ifThenElse (.app "gt" [.var "i", .lit (.int 5)])
        (.break_ none)
        .unitVal))
    (.lit (.int 0))

/-- `let v = x?; Ok(v + 1)` -/
def questionMarkTest : ImpExpr :=
  .letBind "v" (.questionMark (.var "x"))
    (.app "Ok" [.app "add" [.var "v", .lit (.int 1)]])

/-- `while x > 0 { x = x - 1; }` -/
def whileTest : ImpExpr :=
  .whileLoop
    (.app "gt" [.var "x", .lit (.int 0)])
    (.assign "x" (.app "sub" [.var "x", .lit (.int 1)]))

/-- Combined: mutation + loop + early return -/
def combined : ImpExpr :=
  .letBind "result" (.lit (.int 0))
    (.seq
      (.forLoop "i" (.lit (.int 0)) (.var "n")
        (.seq
          (.assign "result" (.app "add" [.var "result", .var "i"]))
          (.ifThenElse (.app "gt" [.var "result", .lit (.int 100)])
            (.earlyReturn (.var "result"))
            .unitVal)))
      (.var "result"))

/-! ## Feature Predicate Tests -/

-- simpleMut has assign (mutation) but no references, loops, or early exit
#eval checkNoReferences simpleMut  -- true
#eval checkNoMutation simpleMut    -- false (has assign)
#eval checkNoLoops simpleMut       -- true
#eval checkNoEarlyExit simpleMut   -- true

-- borrowDeref has borrow/deref but nothing else
#eval checkNoReferences borrowDeref -- false
#eval checkNoMutation borrowDeref   -- true
#eval checkNoLoops borrowDeref      -- true
#eval checkNoEarlyExit borrowDeref  -- true

-- earlyRet has earlyReturn
#eval checkNoReferences earlyRet  -- true
#eval checkNoMutation earlyRet    -- true
#eval checkNoLoops earlyRet       -- true
#eval checkNoEarlyExit earlyRet   -- false

-- sumRange has forLoop and assign
#eval checkNoReferences sumRange  -- true
#eval checkNoMutation sumRange    -- false (has assign)
#eval checkNoLoops sumRange       -- false (has forLoop)
#eval checkNoEarlyExit sumRange   -- true

-- loopBreak has forLoop and break
#eval checkNoReferences loopBreak -- true
#eval checkNoMutation loopBreak   -- true
#eval checkNoLoops loopBreak      -- false
#eval checkNoEarlyExit loopBreak  -- true

-- questionMarkTest has questionMark
#eval checkNoEarlyExit questionMarkTest -- false

-- whileTest has whileLoop and assign
#eval checkNoLoops whileTest      -- false
#eval checkNoMutation whileTest   -- false

-- combined has everything
#eval checkFullyFunctional combined  -- false

/-! ## Pipeline Tests -/

-- After pipeline, all programs should be fully functional
#eval checkFullyFunctional (pipeline simpleMut)         -- true
#eval checkFullyFunctional (pipeline borrowDeref)       -- true
#eval checkFullyFunctional (pipeline earlyRet)          -- true
#eval checkFullyFunctional (pipeline sumRange)          -- true
#eval checkFullyFunctional (pipeline loopBreak)         -- true
#eval checkFullyFunctional (pipeline questionMarkTest)  -- true
#eval checkFullyFunctional (pipeline whileTest)         -- true
#eval checkFullyFunctional (pipeline combined)          -- true

/-! ## Semantics Tests -/

/-- Run a program with given environment bindings and return the outcome. -/
def run (fuel : Nat) (bindings : List (String × Value)) (e : ImpExpr) : Outcome :=
  let env := bindings.foldl (fun acc (n, v) => acc.extend n v) Env.empty
  (denote defaultBuiltins fuel e env).1

-- simpleMut: let mut x = 0; x = 5; x → 5
#eval run 10 [] simpleMut  -- Outcome.val (Value.int 5)

-- borrowDeref: let y = &x; *y + 1 with x = 10 → 11
#eval run 10 [("x", .int 10)] borrowDeref  -- Outcome.val (Value.int 11)

-- earlyRet: if x > 0 { return x; } 0
#eval run 10 [("x", .int 42)] earlyRet  -- Outcome.earlyRet (Value.int 42)
#eval run 10 [("x", .int 0)] earlyRet   -- Outcome.val (Value.int 0)
#eval run 10 [("x", .int (-5))] earlyRet -- Outcome.val (Value.int 0)

-- sumRange: sum 0..5 = 0+1+2+3+4 = 10
#eval run 100 [("n", .int 5)] sumRange  -- Outcome.val (Value.int 10)

-- sumRange: sum 0..0 = 0
#eval run 100 [("n", .int 0)] sumRange  -- Outcome.val (Value.int 0)

-- loopBreak: loop 0..10, break when i > 5
#eval run 100 [] loopBreak  -- Outcome.val (Value.int 0)

-- questionMark with Ok value
#eval run 10 [("x", .result true (.int 5))] questionMarkTest
  -- Outcome.val (Value.result true (Value.int 6))

-- questionMark with Err value → early return
#eval run 10 [("x", .result false (.int 99))] questionMarkTest
  -- Outcome.earlyRet (Value.result false (Value.int 99))

-- whileTest: count down from 3
#eval run 100 [("x", .int 3)] whileTest  -- Outcome.val (Value.unit)

/-! ## Phase-by-Phase Transformation Tests -/

-- Phase 1: dropReferences removes borrow/deref
#eval checkNoReferences (dropReferences borrowDeref)  -- true
-- Original semantics preserved
#eval run 10 [("x", .int 10)] (dropReferences borrowDeref)
  -- Outcome.val (Value.int 11) — same as original

-- Phase 2: localMutation removes assign
#eval checkNoMutation (localMutation [] simpleMut)  -- true

-- Phase 3: functionalizeLoops removes loops
#eval checkNoLoops (functionalizeLoops sumRange)  -- true
#eval checkNoLoops (functionalizeLoops loopBreak)  -- true
-- Phase 3 uses nested encoding for loops with earlyReturn
#eval checkNoLoops (functionalizeLoops combined)  -- true
#eval checkFullyFunctional (pipeline combined)    -- true

-- Phase 4: cfIntoMonads removes early exit
#eval checkNoEarlyExit (cfIntoMonads earlyRet)  -- true
#eval checkNoEarlyExit (cfIntoMonads questionMarkTest)  -- true

/-! ## Pipeline Semantics Preservation Tests

For programs without loops or early exits, the pipeline preserves
denotational semantics exactly. -/

-- simpleMut through pipeline: mutation is the only feature,
-- localMutation preserves semantics
#eval run 10 [] (pipeline simpleMut)
  -- Should give val (int 5), same as original

-- borrowDeref through pipeline: dropReferences preserves semantics
#eval run 10 [("x", .int 10)] (pipeline borrowDeref)
  -- Should give val (int 11), same as original

/-! ## Theorem-Level Tests

Verify key properties as theorems (checked by Lean's kernel). -/

example : NoReferences (dropReferences borrowDeref) :=
  dropReferences_noRefs borrowDeref

example : NoMutation (localMutation [] simpleMut) :=
  localMutation_noMut [] simpleMut

example : NoLoops (functionalizeLoops sumRange) :=
  functionalizeLoops_noLoops sumRange

example : NoEarlyExit (cfIntoMonads earlyRet) :=
  cfIntoMonads_noEarlyExit earlyRet

example : FullyFunctional (pipeline simpleMut) :=
  pipeline_fullyFunctional simpleMut

example : FullyFunctional (pipeline combined) :=
  pipeline_fullyFunctional combined

/-- End-to-end: pipeline preserves semantics for loop-free,
    early-exit-free programs. -/
example (fuel : Nat) : denote defaultBuiltins fuel (pipeline simpleMut) =
    denote defaultBuiltins fuel simpleMut := by
  apply pipeline_correct
  · -- NoLoops after phases 1-2
    simp [mutatedVars]
    exact .letBind .lit (.seq (.seq (.letBind .lit .var) .unitVal) .var)
  · -- NoEarlyExit after phases 1-2
    simp [mutatedVars]
    exact .letBind .lit (.seq (.seq (.letBind .lit .var) .unitVal) .var)

/-! ## Mutation threading across an `if`- or `match`-statement join

A branch of a statement-`if` can end in a further statement — a nested `if`, a
`match`, a loop — and the mutation it performs has to survive `tThreadMut`. A
`match` used as a statement joins its arms the way an `if` joins its branches.
Each fixture below assigns inside such a position; the check reads the
assignment (resp. the loop, resp. the `_mtup` join binding) back out of the
threaded result. -/

/-- `if a { if b { acc = 1; } } acc` — the assignment sits at the tail of the
    outer branch, inside a nested `if`. -/
def tailNestedIf : TExpr :=
  .mk (.seq
    (.mk (.ifThenElse (.mk (.var "a") .unknown)
      (.mk (.ifThenElse (.mk (.var "b") .unknown)
        (.mk (.assign "acc" (.mk (.lit (.int 1)) .unknown)) .unit)
        (.mk .unitVal .unit)) .unit)
      (.mk .unitVal .unit)) .unit)
    (.mk (.var "acc") .unknown)) .unknown

/-- `if a { for i in 0..4 { acc = i; } } acc` — the assignment sits at the tail
    of the branch, inside a loop. -/
def tailLoop : TExpr :=
  .mk (.seq
    (.mk (.ifThenElse (.mk (.var "a") .unknown)
      (.mk (.forLoop "i" (.mk (.lit (.int 0)) .unknown) (.mk (.lit (.int 4)) .unknown)
        (.mk (.assign "acc" (.mk (.var "i") .unknown)) .unit)) .unit)
      (.mk .unitVal .unit)) .unit)
    (.mk (.var "acc") .unknown)) .unknown

/-- `if a { match t { A => acc = 1, _ => {} } } acc` — the assignment sits at
    the tail of the branch, inside a `match`. -/
def tailMatch : TExpr :=
  .mk (.seq
    (.mk (.ifThenElse (.mk (.var "a") .unknown)
      (.mk (.match_ (.mk (.var "t") .unknown)
        [(.ctorPat "A" [], .mk (.assign "acc" (.mk (.lit (.int 1)) .unknown)) .unit),
         (.wildcard, .mk .unitVal .unit)]) .unit)
      (.mk .unitVal .unit)) .unit)
    (.mk (.var "acc") .unknown)) .unknown

/-- `match t { A => acc = 1, _ => {} } acc` — the `match` is the statement whose
    arms join, with no enclosing `if`. -/
def matchStmt : TExpr :=
  .mk (.seq
    (.mk (.match_ (.mk (.var "t") .unknown)
      [(.ctorPat "A" [], .mk (.assign "acc" (.mk (.lit (.int 1)) .unknown)) .unit),
       (.wildcard, .mk .unitVal .unit)]) .unit)
    (.mk (.var "acc") .unknown)) .unknown

/-- `match t { A => 1, _ => 2 } acc` — arms that assign nothing, so the join is
    declined and the expression is returned unchanged. -/
def pureMatchStmt : TExpr :=
  .mk (.seq
    (.mk (.match_ (.mk (.var "t") .unknown)
      [(.ctorPat "A" [], .mk (.lit (.int 1)) .unknown),
       (.wildcard, .mk (.lit (.int 2)) .unknown)]) .unknown)
    (.mk (.var "acc") .unknown)) .unknown

#eval tAssignedVars (tThreadMut true tailNestedIf)  -- ["acc"]
#eval tAssignedVars (tThreadMut true tailLoop)      -- ["acc"]
#eval tContainsLoop (tThreadMut true tailLoop)      -- true
#eval tAssignedVars (tThreadMut true tailMatch)     -- ["acc"]
#eval (tVarRefs (tThreadMut true matchStmt)).contains "_mtup"        -- true
#eval (tThreadMut true pureMatchStmt).erase == pureMatchStmt.erase   -- true

/-! ## `&mut` write-back

A Rust `fn f(v: &mut T, …)` yields `()` and writes through `v`. The extraction
returns `v` from `f` and rebinds it at every call, both sides reading the table
`mutWriteFns` resolves from the export's signatures and bodies.

The five signatures below are the four shapes a signature can take (write-back,
a result that carries a value, two `&mut` parameters, and a `&mut` parameter
written only through a field) plus a function whose parameter is written only by
a nested write-back call. The three bodies decide which candidates survive: `f`
assigns its parameter, `m` writes through a field — which the parse arms lower
to a `struct_update` assignment of the parameter itself — and `n` writes only
by calling `f`. -/

def mutStateTy : ImpType := .array .int 8
def mutBlockTy : ImpType := .array .int 64

/-- `fn f(st: &mut [u32; 8], blk: &[u8; 64])`. -/
def writebackSig : FnTypeInfo :=
  ⟨[("st", .ref mutStateTy true), ("blk", .ref mutBlockTy false)], .unit⟩
/-- `fn h(st: &mut [u32; 8]) -> [u8; 32]`. -/
def valueSig : FnTypeInfo := ⟨[("st", .ref mutStateTy true)], .array .int 32⟩
/-- `fn k(st: &mut [u32; 8], o: &mut [u8; 64])`. -/
def twoMutSig : FnTypeInfo :=
  ⟨[("st", .ref mutStateTy true), ("o", .ref mutBlockTy true)], .unit⟩
/-- `fn m(self: &mut S)`. -/
def fieldSig : FnTypeInfo := ⟨[("self", .ref (.adt "S" []) true)], .unit⟩
/-- `fn n(v: &mut [u32; 8], blk: &[u8; 64])`. -/
def nestedSig : FnTypeInfo :=
  ⟨[("v", .ref mutStateTy true), ("blk", .ref mutBlockTy false)], .unit⟩

def writebackFns : List (String × FnTypeInfo) :=
  [("f", writebackSig), ("h", valueSig), ("k", twoMutSig), ("m", fieldSig),
   ("n", nestedSig)]

/-- Field layout of the struct `S` behind `m`'s `&mut self`. -/
def sFields : StructFieldNames := [("S", ["h", "buf"])]

/-- `st = q;` — `f`'s body. -/
def writebackBody : TExpr :=
  .mk (.seq (.mk (.assign "st" (.mk (.var "q") mutStateTy)) .unit) (.mk .unitVal .unit)) .unit
/-- `self.buf = q;` — `m`'s body, as the parse arms lower it under `sFields`:
    an assignment of `self` to a functional field update. -/
def fieldBody : TExpr :=
  .mk (.seq (.mk (.assign "self" (.mk (.app "struct_update#S#1#2"
      [.mk (.var "self") (.adt "S" []), .mk (.var "q") mutStateTy]) (.adt "S" []))) .unit)
    (.mk .unitVal .unit)) .unit
/-- `f(&mut v, blk);` — `n`'s body. -/
def nestedBody : TExpr :=
  .mk (.seq
    (.mk (.app "f" [.mk (.borrow (.mk (.var "v") mutStateTy)) (.ref mutStateTy true),
      .mk (.var "blk") (.ref mutBlockTy false)]) .unit) (.mk .unitVal .unit)) .unit

def writebackDefs : List (String × TExpr) :=
  [("f", writebackBody), ("m", fieldBody), ("n", nestedBody)]

/-- `f(&mut st, blk); digest(st)` — the call in statement position whose result
    carries `st`'s update. -/
def writebackStmt : TExpr :=
  .mk (.seq
    (.mk (.app "f" [.mk (.borrow (.mk (.var "st") mutStateTy)) (.ref mutStateTy true),
      .mk (.var "blk") (.ref mutBlockTy false)]) .unit)
    (.mk (.app "digest" [.mk (.var "st") mutStateTy]) mutBlockTy)) mutBlockTy

/-- `f(&mut a[0])` — the borrowed place is an element, so the result is that
    element rather than `a`. -/
def writebackIndexed : TExpr :=
  .mk (.app "f" [.mk (.borrow (.mk (.app "index"
    [.mk (.var "a") mutStateTy, .mk (.lit (.int 0)) .int]) .int)) (.ref .int true)]) .unit

/-- `h(&mut st)` — a call to a function that is not a write-back function. -/
def valueCall : TExpr :=
  .mk (.app "h" [.mk (.borrow (.mk (.var "st") mutStateTy)) (.ref mutStateTy true)])
    (.array .int 32)

def writebackTable : List (String × Nat) :=
  mutWriteTable (mutWriteFns sFields writebackFns writebackDefs)

#eval mutWriteCandidates writebackFns
  -- [("f", [0], ["st"], false), ("h", [0], ["st"], true), ("k", [0, 1], ["st", "o"], false),
  --  ("m", [0], ["self"], false), ("n", [0], ["v"], false)]
#eval mutWriteStep sFields writebackDefs [] [] (mutWriteCandidates writebackFns)
  -- [("f", [0], ["st"], false), ("m", [0], ["self"], false)]
#eval mutWriteFns sFields writebackFns writebackDefs
  -- [("f", [0], ["st"], false), ("m", [0], ["self"], false), ("n", [0], ["v"], false)]
#eval mutWriteReturns (mutWriteFns sFields writebackFns writebackDefs)
  -- [("f", ["st"], false), ("m", ["self"], false), ("n", ["v"], false)]
#eval mutWriteTupleTable (mutWriteFns sFields writebackFns writebackDefs)  -- []
#eval tAssignedVars (tRebindMutCalls sFields writebackTable [] writebackStmt)      -- ["st"]
#eval tAssignedVars (tRebindMutCalls sFields writebackTable [] writebackIndexed)   -- []
#eval (tRebindMutCalls sFields writebackTable [] valueCall).erase == valueCall.erase  -- true
#eval tAssignedVars
  (tThreadMut true (tRebindMutCalls sFields writebackTable [] writebackStmt))  -- ["st"]
#eval (tReturnMutParams ["st"] false writebackBody).erase
        == ImpExpr.seq (.assign "st" (.var "q")) (.var "st")            -- true
#eval (tReturnMutParams [] false writebackBody).erase == writebackBody.erase  -- true

/-- `k(&mut st, &mut o)` — two `&mut` parameters, outside the write-back fragment. -/
def twoMutCall : TExpr :=
  .mk (.app "k" [.mk (.borrow (.mk (.var "st") mutStateTy)) (.ref mutStateTy true),
    .mk (.borrow (.mk (.var "o") mutBlockTy)) (.ref mutBlockTy true)]) .unit

#eval tDroppedMutCalls writebackFns sFields writebackTable [] writebackStmt    -- []
#eval tDroppedMutCalls writebackFns sFields writebackTable [] twoMutCall       -- [("k", [0, 1])]
#eval tDroppedMutCalls writebackFns sFields writebackTable [] valueCall        -- [("h", [0])]
#eval tDroppedMutCalls writebackFns sFields writebackTable [] writebackIndexed -- [("f", [0])]

/-! ## Struct-field writes

A write through a struct-field place lowers to an assignment of the root
variable to a functional `struct_update`; the renderer expands the resolved
head into the `Hax.struct_update_fst`/`_snd` composition. The fixtures pin the
lowering on the two handled place shapes, the declined shapes, the call-site
field write-back, and the rendered composition. -/

/-- `self.buf` over `self : S`. -/
def fieldWriteLhs : TExpr :=
  .mk (.app ".buf" [.mk (.var "self") (.adt "S" [])]) mutStateTy

/-- `self.buf[i]`. -/
def fieldElemLhs : TExpr :=
  .mk (.app "index" [fieldWriteLhs, .mk (.var "i") .int]) .int

/-- Erased view of a lowered assignment, for comparison. -/
def loweredErase (k : Option TExprKind) : Option ImpExpr :=
  k.map fun k => (TExpr.mk k .unit).erase

#eval loweredErase (HaxAdapter.tFieldPlaceAssign sFields fieldWriteLhs
        (fun _ => .mk (.var "q") mutStateTy))
  == some (ImpExpr.assign "self"
       (.app "struct_update#S#1#2" [.var "self", .var "q"]))  -- true
#eval loweredErase (HaxAdapter.tFieldPlaceAssign sFields fieldElemLhs
        (fun _ => .mk (.var "q") .int))
  == some (ImpExpr.assign "self" (.app "struct_update#S#1#2" [.var "self",
       .app "array_update" [.app ".buf" [.var "self"], .var "i", .var "q"]]))  -- true
-- Declined: no layout, an ambiguous field name, a non-variable root.
#eval (HaxAdapter.tFieldPlaceAssign [] fieldWriteLhs
        (fun _ => .mk (.var "q") mutStateTy)).isNone  -- true
#eval (HaxAdapter.tFieldPlaceAssign [("S", ["buf"]), ("T", ["buf"])] fieldWriteLhs
        (fun _ => .mk (.var "q") mutStateTy)).isNone  -- true
#eval (HaxAdapter.tFieldPlaceAssign sFields
        (.mk (.app ".buf" [.mk (.app ".inner" [.mk (.var "self") .unknown]) .unknown])
          mutStateTy)
        (fun _ => .mk (.var "q") mutStateTy)).isNone  -- true

/-- `f(&mut self.buf, blk)` — the write-back argument is a field place, so the
    call becomes a functional field update of `self` from the call's result. -/
def writebackFieldCall : TExpr :=
  .mk (.app "f" [.mk (.borrow fieldWriteLhs) (.ref mutStateTy true),
    .mk (.var "blk") (.ref mutBlockTy false)]) .unit

#eval (tRebindMutCalls sFields writebackTable [] writebackFieldCall).erase
  == ImpExpr.assign "self" (.app "struct_update#S#1#2" [.var "self",
       .app "f" [.borrow (.app ".buf" [.var "self"]), .var "blk"]])  -- true

-- Rendered composition, one shape per position class.
#eval renderStructUpdate 0 2 "s" "v" == "Hax.struct_update_fst s v"  -- true
#eval renderStructUpdate 1 4 "self" "v"
  == "Hax.struct_update_snd self (Hax.struct_update_fst self.2 v)"  -- true
#eval renderStructUpdate 3 4 "s" "v"
  == "Hax.struct_update_snd s (Hax.struct_update_snd s.2 (Hax.struct_update_snd s.2.2 v))"
  -- true
#eval renderStructUpdate 0 1 "s" "v" == "v"  -- true
#eval toLean (.app "struct_update#S#1#4" [.var "self", .var "v"])
  == "Hax.struct_update_snd self (Hax.struct_update_fst self.2 v)"  -- true

-- Qualified enum-variant construction renders as the Lean constructor.
#eval toLean (.app "LoginOutcome::LoggedIn" [.var "session_key"])
  == "LoginOutcome.LoggedIn session_key"  -- true

/-! ## Slice-range writes

A write through a slice-range place `x[lo..hi]` lowers to an assignment of `x`
to a functional `slice_update` of that range from the call's result. The
fixtures pin the three bounded range spellings, the declined full range, and
the rendered call. -/

/-- `header[16..48].copy_from_slice(sig)`, as the export spells it. -/
def sliceRangeCall : TExpr :=
  .mk (.app "copy_from_slice"
    [.mk (.app "index_mut" [.mk (.var "header") mutBlockTy,
        .mk (.app "Range" [.mk (.lit (.int 16)) .int, .mk (.lit (.int 48)) .int]) .unknown])
      mutBlockTy,
     .mk (.var "sig") mutBlockTy]) .unit

/-- `header[..16].copy_from_slice(nonce)`, whose lower bound is `0`. -/
def sliceToCall : TExpr :=
  .mk (.app "copy_from_slice"
    [.mk (.app "index_mut" [.mk (.var "header") mutBlockTy,
        .mk (.app "RangeTo" [.mk (.lit (.int 16)) .int]) .unknown]) mutBlockTy,
     .mk (.var "nonce") mutBlockTy]) .unit

/-- `header[16..].copy_from_slice(tail)`, whose upper bound is the receiver's
    length. -/
def sliceFromCall : TExpr :=
  .mk (.app "copy_from_slice"
    [.mk (.app "index_mut" [.mk (.var "header") mutBlockTy,
        .mk (.app "RangeFrom" [.mk (.lit (.int 16)) .int]) .unknown]) mutBlockTy,
     .mk (.var "tail") mutBlockTy]) .unit

def sliceWriteTable : List (String × Nat) := writebackTable ++ builtinWriteTable

#eval (tRebindMutCalls sFields sliceWriteTable [] sliceRangeCall).erase
  == ImpExpr.assign "header" (.app "slice_update"
       [.var "header", .lit (.int 16), .lit (.int 48),
        .app "copy_from_slice"
          [.app "index_mut" [.var "header", .app "Range" [.lit (.int 16), .lit (.int 48)]],
           .var "sig"]])  -- true
#eval (tRebindMutCalls sFields sliceWriteTable [] sliceToCall).erase
  == ImpExpr.assign "header" (.app "slice_update"
       [.var "header", .lit (.int 0), .lit (.int 16),
        .app "copy_from_slice"
          [.app "index_mut" [.var "header", .app "RangeTo" [.lit (.int 16)]],
           .var "nonce"]])  -- true
#eval (tRebindMutCalls sFields sliceWriteTable [] sliceFromCall).erase
  == ImpExpr.assign "header" (.app "slice_update"
       [.var "header", .lit (.int 16), .app "len" [.var "header"],
        .app "copy_from_slice"
          [.app "index_mut" [.var "header", .app "RangeFrom" [.lit (.int 16)]],
           .var "tail"]])  -- true
#eval tAssignedVars (tRebindMutCalls sFields sliceWriteTable [] sliceRangeCall)  -- ["header"]
-- Declined: a full range carries no bounds.
#eval (tMutArgSlice (.mk (.app "index_mut" [.mk (.var "header") mutBlockTy,
    .mk (.app "RangeFull" []) .unknown]) mutBlockTy)).isNone  -- true
#eval toLean (.app "slice_update"
    [.var "header", .lit (.int 0), .lit (.int 16), .var "nonce"])
  == "Hax.slice_update header (0 : Int) (16 : Int) nonce"  -- true

/-! ## Tuple-form `&mut` write-back

A callee with a value result, or with several `&mut` parameters, returns the
tuple of its result and its written parameters. A call site binds that tuple to
`_wb` and assigns each component: from a `let`, from an assignment, and from a
statement. A call in any other position keeps its value and is reported by
`tDroppedMutCalls`.

The three signatures are the three shapes: a value result with one written
parameter (`p`, `rej`) and a `()` result with two (`w`). -/

/-- `fn p(dst: &mut [u8; 64], pos: Int) -> Int`. -/
def pushSig : FnTypeInfo := ⟨[("dst", .ref mutBlockTy true), ("pos", .int)], .int⟩
/-- `fn rej(f: &mut [u32; 8], idx: Int) -> Int`. -/
def rejSig : FnTypeInfo := ⟨[("f", .ref mutStateTy true), ("idx", .int)], .int⟩
/-- `fn w(st: &mut [u32; 8], o: &mut [u8; 64])`. -/
def twoWriteSig : FnTypeInfo :=
  ⟨[("st", .ref mutStateTy true), ("o", .ref mutBlockTy true)], .unit⟩

def tupleFns : List (String × FnTypeInfo) :=
  [("p", pushSig), ("rej", rejSig), ("w", twoWriteSig)]

/-- `dst = q; pos + 1` — `p`'s body: it writes its parameter and ends in a
    value. -/
def pushBody : TExpr :=
  .mk (.seq (.mk (.assign "dst" (.mk (.var "q") mutBlockTy)) .unit)
    (.mk (.app "add" [.mk (.var "pos") .int, .mk (.lit (.int 1)) .int]) .int)) .int
/-- `f = q; idx + 1` — `rej`'s body. -/
def rejBody : TExpr :=
  .mk (.seq (.mk (.assign "f" (.mk (.var "q") mutStateTy)) .unit)
    (.mk (.app "add" [.mk (.var "idx") .int, .mk (.lit (.int 1)) .int]) .int)) .int
/-- `st = q; o = r;` — `w`'s body: it writes both of its parameters. -/
def twoWriteBody : TExpr :=
  .mk (.seq (.mk (.assign "st" (.mk (.var "q") mutStateTy)) .unit)
    (.mk (.seq (.mk (.assign "o" (.mk (.var "r") mutBlockTy)) .unit)
      (.mk .unitVal .unit)) .unit)) .unit

def tupleDefs : List (String × TExpr) :=
  [("p", pushBody), ("rej", rejBody), ("w", twoWriteBody)]

def tupleResolved : List (String × List Nat × List String × Bool) :=
  mutWriteFns sFields tupleFns tupleDefs
def tupleWriters : List (String × Nat) := mutWriteTable tupleResolved
def tupleTup : List (String × List Nat × Bool) := mutWriteTupleTable tupleResolved

#eval tupleResolved
  -- [("p", [0], ["dst"], true), ("rej", [0], ["f"], true), ("w", [0, 1], ["st", "o"], false)]
#eval tupleWriters  -- []
#eval tupleTup      -- [("p", [0], true), ("rej", [0], true), ("w", [0, 1], false)]

-- The callee's tail: the value paired with the written parameter, and the pair
-- of the two written parameters.
#eval (tReturnMutParams ["dst"] true pushBody).erase
  == ImpExpr.seq (.assign "dst" (.var "q"))
       (.tuple [.app "add" [.var "pos", .lit (.int 1)], .var "dst"])  -- true
#eval (tReturnMutParams ["st", "o"] false twoWriteBody).erase
  == ImpExpr.seq (.assign "st" (.var "q"))
       (.seq (.assign "o" (.var "r")) (.tuple [.var "st", .var "o"]))  -- true

/-- `let p0 = p(&mut dst, pos); use(p0, dst)` — the call in `let` position with
    its result used. -/
def pushLetCall : TExpr :=
  .mk (.letBind "p0"
    (.mk (.app "p" [.mk (.borrow (.mk (.var "dst") mutBlockTy)) (.ref mutBlockTy true),
      .mk (.var "pos") .int]) .int)
    (.mk (.app "use" [.mk (.var "p0") .int, .mk (.var "dst") mutBlockTy]) .int)) .int

/-- `while c { idx = rej(&mut f, idx) }` — the call in assignment position
    inside a loop body. -/
def rejLoopCall : TExpr :=
  .mk (.whileLoop (.mk (.var "c") .bool)
    (.mk (.assign "idx"
      (.mk (.app "rej" [.mk (.borrow (.mk (.var "f") mutStateTy)) (.ref mutStateTy true),
        .mk (.var "idx") .int]) .int)) .unit)) .unit

/-- `w(&mut st, &mut o); digest(st)` — the two-parameter call in statement
    position. -/
def twoWriteStmt : TExpr :=
  .mk (.seq
    (.mk (.app "w" [.mk (.borrow (.mk (.var "st") mutStateTy)) (.ref mutStateTy true),
      .mk (.borrow (.mk (.var "o") mutBlockTy)) (.ref mutBlockTy true)]) .unit)
    (.mk (.app "digest" [.mk (.var "st") mutStateTy]) mutBlockTy)) mutBlockTy

/-- `outer(p(&mut dst, pos))` — a tuple-form call as the argument of another
    call, which the rewrite does not reach. -/
def tupleArgCall : TExpr :=
  .mk (.app "outer"
    [.mk (.app "p" [.mk (.borrow (.mk (.var "dst") mutBlockTy)) (.ref mutBlockTy true),
      .mk (.var "pos") .int]) .int]) .int

#eval (tRebindMutCalls sFields tupleWriters tupleTup pushLetCall).erase
  == ImpExpr.letBind "_wb" (.app "p" [.borrow (.var "dst"), .var "pos"])
       (.seq (.assign "dst" (.app "::proj::.2" [.var "_wb"]))
         (.letBind "p0" (.proj (.var "_wb") 0)
           (.app "use" [.var "p0", .var "dst"])))  -- true
#eval (tRebindMutCalls sFields tupleWriters tupleTup rejLoopCall).erase
  == ImpExpr.whileLoop (.var "c")
       (.letBind "_wb" (.app "rej" [.borrow (.var "f"), .var "idx"])
         (.seq (.assign "f" (.app "::proj::.2" [.var "_wb"]))
           (.assign "idx" (.proj (.var "_wb") 0))))  -- true
#eval (tRebindMutCalls sFields tupleWriters tupleTup twoWriteStmt).erase
  == ImpExpr.letBind "_wb" (.app "w" [.borrow (.var "st"), .borrow (.var "o")])
       (.seq (.assign "st" (.proj (.var "_wb") 0))
         (.seq (.assign "o" (.app "::proj::.2" [.var "_wb"]))
           (.app "digest" [.var "st"])))  -- true
#eval (tRebindMutCalls sFields tupleWriters tupleTup tupleArgCall).erase
  == tupleArgCall.erase  -- true

-- The written variables reach the mutation analyses, so the loop threads them.
#eval tAssignedVars (tRebindMutCalls sFields tupleWriters tupleTup pushLetCall)  -- ["dst"]
#eval tAssignedVars (tRebindMutCalls sFields tupleWriters tupleTup rejLoopCall)  -- ["f", "idx"]
#eval tAssignedVars
  (tThreadMut true (tRebindMutCalls sFields tupleWriters tupleTup rejLoopCall))  -- ["f", "idx"]
#eval tAssignedVars (tRebindMutCalls sFields tupleWriters tupleTup twoWriteStmt) -- ["st", "o"]

-- Rewritten and reported are complements: the three rewritten sites report
-- nothing, the call in argument position is reported.
#eval tDroppedMutCalls tupleFns sFields tupleWriters tupleTup pushLetCall    -- []
#eval tDroppedMutCalls tupleFns sFields tupleWriters tupleTup rejLoopCall    -- []
#eval tDroppedMutCalls tupleFns sFields tupleWriters tupleTup twoWriteStmt   -- []
#eval tDroppedMutCalls tupleFns sFields tupleWriters tupleTup tupleArgCall   -- [("p", [0])]
-- Without the tuple table the same sites are reported, and nothing is rewritten.
#eval tDroppedMutCalls tupleFns sFields tupleWriters [] pushLetCall          -- [("p", [0])]
#eval (tRebindMutCalls sFields tupleWriters [] pushLetCall).erase == pushLetCall.erase  -- true

/-! ### The rendered signature of a tuple-form callee

The parameters of a definition are the self-bindings the adapter emits ahead of
the body, and the renderer reads the Rust result from the body's type. A
tuple-form callee returns a product, so its annotation is the product of that
Rust result and the written parameters; a single-form callee returns its one
parameter in place of a `()` result, which carries no annotation. -/

/-- `fn p(dst: &mut [u8; 64], pos: Int) -> Int` with its parameter bindings. -/
def pushRawTe : TExpr :=
  .mk (.letBind "dst" (.mk (.var "dst") mutBlockTy)
    (.mk (.letBind "pos" (.mk (.var "pos") .int) pushBody) .int)) .int
/-- `fn w(st: &mut [u32; 8], o: &mut [u8; 64])` with its parameter bindings. -/
def twoWriteRawTe : TExpr :=
  .mk (.letBind "st" (.mk (.var "st") mutStateTy)
    (.mk (.letBind "o" (.mk (.var "o") mutBlockTy) twoWriteBody) .unit)) .unit
/-- `fn f(st: &mut [u32; 8], blk: &[u8; 64])` with its parameter bindings. -/
def writebackRawTe : TExpr :=
  .mk (.letBind "st" (.mk (.var "st") mutStateTy)
    (.mk (.letBind "blk" (.mk (.var "blk") mutBlockTy) writebackBody) .unit)) .unit

/-- The first line of a rendered definition: its signature. -/
def renderedSignature (name : String) (rawTe : TExpr) (body : ImpExpr)
    (rets : List (String × List String × Bool)) : String :=
  ((toLeanDefTyped name rawTe body (mutWriteRets := rets)).splitOn "\n").headD ""

#eval renderedSignature "p" pushRawTe ((tReturnMutParams ["dst"] true pushBody).erase)
    (mutWriteTupleReturns tupleResolved)
  -- "def p (dst : Array (Int)) (pos : Int) : Int × Array (Int) :="
#eval renderedSignature "w" twoWriteRawTe
    ((tReturnMutParams ["st", "o"] false twoWriteBody).erase)
    (mutWriteTupleReturns tupleResolved)
  -- "def w (st : Array (Int)) (o : Array (Int)) : Array (Int) × Array (Int) :="
-- The single form is not in the tuple table, so its `()` result stays
-- unannotated and its definition is rendered as before.
#eval renderedSignature "f" writebackRawTe ((tReturnMutParams ["st"] false writebackBody).erase)
    (mutWriteTupleReturns (mutWriteFns sFields writebackFns writebackDefs))
  -- "def f (st : Array (Int)) (blk : Array (Int)) :="

/-! ## Fold-body tails that carry mutations

The plain-fold encoder distributes into a `match` tail, keeps a mutation or a
nested loop ahead of the continue, and still replaces a pure-value tail. A
statement following a conditional break is distributed into the non-breaking
branches by `distributeStmtCF` before encoding. -/

/-- Fold body ending in a `match` whose arm assigns. -/
def foldMatchTail : ImpExpr :=
  .match_ (.var "t")
    [(.ctorPat "A" [], .assign "acc" (.lit (.int 1))),
     (.wildcard, .var "acc")]

#eval encodeForFoldBody (.var "acc") foldMatchTail ==
  ImpExpr.match_ (.var "t")
    [(.ctorPat "A" [], .seq (.assign "acc" (.lit (.int 1))) (.cfContinue (.var "acc"))),
     (.wildcard, .cfContinue (.var "acc"))]  -- true
-- An all-pure match is a pure-value tail: replaced by the continue.
#eval encodeForFoldBody (.var "acc")
    (.match_ (.var "t") [(.ctorPat "A" [], .lit (.int 1)), (.wildcard, .lit (.int 2))])
  == ImpExpr.cfContinue (.var "acc")  -- true

/-- Fold body ending in a nested fold. -/
def foldLoopTail : ImpExpr :=
  .seq (.assign "x" (.lit (.int 1)))
    (.forFold "i" (.lit (.int 0)) (.lit (.int 4)) (.assign "acc" (.var "i")))

#eval encodeForFoldBody (.var "acc") foldLoopTail ==
  ImpExpr.seq (.assign "x" (.lit (.int 1)))
    (.seq (.forFold "i" (.lit (.int 0)) (.lit (.int 4)) (.assign "acc" (.var "i")))
      (.cfContinue (.var "acc")))  -- true

/-- Typed twin of `foldMatchTail`, for the erase square. -/
def foldMatchTailT : TExpr :=
  .mk (.match_ (.mk (.var "t") .unknown)
    [(.ctorPat "A" [], .mk (.assign "acc" (.mk (.lit (.int 1)) .unknown)) .unit),
     (.wildcard, .mk (.var "acc") .unknown)]) .unknown

#eval (tEncodeForFoldBody (.mk (.var "acc") .unknown) foldMatchTailT).erase
  == encodeForFoldBody (.var "acc") foldMatchTail  -- true

/-- `if c { break }; acc = 1` — a conditional break followed by a write. -/
def breakThenWrite : ImpExpr :=
  .seq (.ifThenElse (.var "c") (.cfBreak .unitVal) .unitVal)
    (.assign "acc" (.lit (.int 1)))

#eval distributeStmtCF breakThenWrite ==
  ImpExpr.ifThenElse (.var "c") (.cfBreak .unitVal)
    (.seq .unitVal (.assign "acc" (.lit (.int 1))))  -- true
#eval encodeForFoldBody (.var "acc") (distributeStmtCF breakThenWrite) ==
  ImpExpr.ifThenElse (.var "c") (.cfBreak (.var "acc"))
    (.seq .unitVal (.seq (.assign "acc" (.lit (.int 1)))
      (.cfContinue (.var "acc"))))  -- true
-- An unconditional break still drops its dead tail.
#eval encodeForFoldBody (.var "acc")
    (.seq (.cfBreak .unitVal) (.assign "acc" (.lit (.int 1))))
  == ImpExpr.cfBreak (.var "acc")  -- true

/-! ## Mutations under a nested `if` inside a loop body

The post-pipeline form of

    let mut in_idx = 0; let mut bits = 0u32; let mut total = 0u32;
    for out_idx in 0..out_len {
        if bits == 0 {
            if in_idx < input.len() { total = input[in_idx] as u32; in_idx += 1; }
            bits = 8;
        }
        bits -= 4;
        result[out_idx] = ((total >> bits) & 15) as u8;
    }

(FIPS 205 `base_w`). `total` and `in_idx` are assigned only under the nested
`if`; both are carried in the `whileFold` state and rebound at the join of the
outer `if`. -/
def nestedIfLoop : ImpExpr :=
  (.letBind "result" (.app "repeat" [(.lit (ImpLit.int 0)), (.lit (ImpLit.int 35))]) (.letBind "in_idx" (.lit (ImpLit.int 0)) (.letBind "bits" (.lit (ImpLit.int 0)) (.letBind "total" (.lit (ImpLit.int 0)) (.letBind "out_idx" (.lit (ImpLit.int 0)) (.seq (.whileFold (.lit (ImpLit.bool true)) (.ifThenElse (.app "Lt" [(.var "out_idx"), (.var "out_len")]) (.seq (.ifThenElse (.app "Eq" [(.var "bits"), (.lit (ImpLit.int 0))]) (.seq (.ifThenElse (.app "Lt" [(.var "in_idx"), (.app "len" [(.var "input")])]) (.seq (.seq (.letBind "total" (.app "cast#32" [(.app "index" [(.var "input"), (.var "in_idx")])]) (.var "total")) .unitVal) (.seq (.seq (.letBind "in_idx" (.app "Add" [(.var "in_idx"), (.lit (ImpLit.int 1))]) (.var "in_idx")) .unitVal) .unitVal)) .unitVal) (.seq (.seq (.letBind "bits" (.lit (ImpLit.int 8)) (.var "bits")) .unitVal) .unitVal)) .unitVal) (.seq (.seq (.letBind "bits" (.app "Sub" [(.var "bits"), (.lit (ImpLit.int 4))]) (.var "bits")) .unitVal) (.seq (.seq (.letBind "result" (.app "array_update" [(.var "result"), (.var "out_idx"), (.app "cast#8" [(.app "BitAnd#32" [(.app "Shr#32" [(.var "total"), (.var "bits")]), (.lit (ImpLit.int 15))])])]) (.var "result")) .unitVal) (.seq (.seq (.letBind "out_idx" (.app "Add" [(.var "out_idx"), (.lit (ImpLit.int 1))]) (.var "out_idx")) .unitVal) .unitVal)))) (.seq (.cfBreak .unitVal) .unitVal))) (.var "result")))))))

/-- The rendering of `e` contains `s` exactly once. -/
def rendersOnce (e : ImpExpr) (s : String) : Bool :=
  ((toLean e).splitOn s).length == 2

#guard rendersOnce nestedIfLoop "Hax.whileFold (total, in_idx, bits, result, out_idx)"
#guard rendersOnce nestedIfLoop "let (total, in_idx, bits) :="
#guard rendersOnce nestedIfLoop
  "let total := if Hax.lt in_idx (Hax.array_len input) then Hax.castVal_w 32 (Hax.index input in_idx) else total"
#guard rendersOnce nestedIfLoop
  "let in_idx := if Hax.lt in_idx (Hax.array_len input) then Hax.add in_idx (1 : Int) else in_idx"
#guard rendersOnce nestedIfLoop "Hax.cfContinue (total, in_idx, bits, result, out_idx)"

/-! ## Typed literals

The `_texpr` literal of a generated definition: `retypeWith` rebuilds the
emitted `ImpExpr` as a `TExpr` carrying the node types of the typed term,
`toLeanTExpr` prints it, and `TExpr.erase` maps it back. -/

/-- `fn f(x: u32) -> u32 { x + 1 }`, in the adapter's parameter encoding. -/
def addOneT : TExpr :=
  .mk (.letBind "x" (.mk (.var "x") (.uint .w32))
    (.mk (.app "add" [.mk (.var "x") (.uint .w32), .mk (.lit (.int 1)) (.uint .w32)])
      (.uint .w32))) (.uint .w32)

/-- The `ImpExpr` literal of `addOneT`. -/
def addOneImp : ImpExpr := addOneT.erase

#eval toLeanImpExpr addOneImp ==
  "(.letBind \"x\" (.var \"x\") (.app \"add\" [(.var \"x\"), (.lit (ImpLit.int 1))]))"  -- true

-- The rebuilt term prints every node with its type.
#eval toLeanTExpr (fun _ => none) (retypeWith addOneImp addOneT) ==
  "(.mk (.letBind \"x\" (.mk (.var \"x\") (.uint .w32)) (.mk (.app \"add\" [(.mk (.var \"x\") (.uint .w32)), (.mk (.lit (ImpLit.int 1)) (.uint .w32))]) (.uint .w32))) (.uint .w32))"  -- true

-- The erase round trip: the rebuilt term erases to the literal it was built
-- from, which is what the emitted `example ... := rfl` states.
#eval toLeanImpExpr (retypeWith addOneImp addOneT).erase == toLeanImpExpr addOneImp  -- true

-- A repeated type is shared by an abbreviation, which the printer uses in
-- place of the rendering.
#eval mkTyAbbrevs "ty_" (collectTyStrs addOneT) == [("(.uint .w32)", "ty_0")]  -- true
#eval toLeanTExpr (fun s => if s == "(.uint .w32)" then some "ty_0" else none)
    (retypeWith addOneImp addOneT) ==
  "(.mk (.letBind \"x\" (.mk (.var \"x\") ty_0) (.mk (.app \"add\" [(.mk (.var \"x\") ty_0), (.mk (.lit (ImpLit.int 1)) ty_0)]) ty_0)) ty_0)"  -- true

-- Types come from the typed term: rebuilt against a term with none, every
-- node is `.unknown`.
#eval toLeanTExpr (fun _ => none) (retypeWith addOneImp unknownTExpr) ==
  "(.mk (.letBind \"x\" (.mk (.var \"x\") .unknown) (.mk (.app \"add\" [(.mk (.var \"x\") .unknown), (.mk (.lit (ImpLit.int 1)) .unknown)]) .unknown)) .unknown)"  -- true

/-! ## Newtype tuple structs and their neighbours

A single-field tuple struct `struct Tag([u8; 32])` is an erased newtype: the
printer emits the transparent alias `abbrev Tag`, the unwrap `«Tag.0»` and the
constructor `«Tag.mk»`, three distinct names, and rewrites the construction
site `Tag(v)` to the constructor name. A tuple struct with two fields and a
named-field struct are not newtypes — `buildNewtypeMap` records only
single-field tuple structs — so their construction sites keep the bare
struct name. -/

/-- `struct Tag([u8; 32])`, in the adapter's newtype encoding. -/
def tagNewtypes : HaxAdapter.NewtypeMap := [("Tag", .array (.uint .w8) 32)]

/-- `fn wrap(v: [u8; 32]) -> Tag { Tag(v) }`. -/
def wrapTagT : TExpr :=
  .mk (.lam ["v"] (.mk (.app "Tag" [.mk (.var "v") .unknown]) .unknown)) .unknown

/-- The emitted file for `wrapTagT`. -/
def wrapTagFile : String :=
  toLeanCertifiedFileTyped [("wrap", wrapTagT)] "T" [] [] [] (newtypes := tagNewtypes)

-- The three declarations carry three distinct names.
#eval ((wrapTagFile.splitOn
  "abbrev Tag := Array (Int)\nnoncomputable def «Tag.0» (x : Tag) : Array (Int) := x\nnoncomputable def «Tag.mk» (x : Array (Int)) : Tag := x\n").length == 2)  -- true

-- No declaration reuses the alias name `Tag`.
#eval ((wrapTagFile.splitOn "def Tag ").length == 1)  -- true

-- The construction site names the constructor, in the surface rendering and
-- in the `ImpExpr` literal.
#eval ((wrapTagFile.splitOn "(fun v => «Tag.mk» v)").length == 2)  -- true
#eval ((wrapTagFile.splitOn "(.app \"Tag.mk\" [(.var \"v\")])").length == 2)  -- true

/-- `struct Pair(u32, u32)`, in the adapter's positional-field encoding. -/
def pairStructMeta : StructMeta := [("Pair", [("0", "int", .int), ("1", "int", .int)])]

/-- `struct Pt { x: u32, y: u32 }`. -/
def ptStructMeta : StructMeta := [("Pt", [("x", "int", .int), ("y", "int", .int)])]

/-- `fn mk(a: u32, b: u32) -> S { S(a, b) }` for a struct named `sname`. -/
def mkStructT (sname : String) : TExpr :=
  .mk (.lam ["a", "b"]
    (.mk (.app sname [.mk (.var "a") .int, .mk (.var "b") .int]) .unknown)) .unknown

-- A two-field tuple struct is not in the newtype map, so its construction
-- site keeps the bare struct name.
#eval (((toLeanCertifiedFileTyped [("mk", mkStructT "Pair")] "T" pairStructMeta [] []).splitOn
  "Pair.mk").length == 1)  -- true
#eval (((toLeanCertifiedFileTyped [("mk", mkStructT "Pair")] "T" pairStructMeta [] []).splitOn
  "(fun a b => Pair a b)").length == 2)  -- true

-- A named-field struct is unaffected for the same reason.
#eval (((toLeanCertifiedFileTyped [("mk", mkStructT "Pt")] "T" ptStructMeta [] []).splitOn
  "Pt.mk").length == 1)  -- true
#eval (((toLeanCertifiedFileTyped [("mk", mkStructT "Pt")] "T" ptStructMeta [] []).splitOn
  "(fun a b => Pt a b)").length == 2)  -- true

end Hax.Tests
