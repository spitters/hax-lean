/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.CertifiedTExprs
public import HaxLean.Range.Heads
public meta import HaxLean.Range.Heads

/-!
# Interval inference over the typed extraction (`lake exe rangeprobe`)

An untrusted abstract interpretation of the `TExpr` literals of `Hax.certifiedTExprs` in
integer intervals, which counts, per function, the operations that panic in Rust
(the guarded operations of `HaxLean/RuntimeM.lean`) and how many of them the intervals prove
safe. Every operation counted safe passes an interval comparison written out in
`checkedArith`, `divOk`, `shiftOk`, `idxOk`, `sliceOk` or `sameLen`.

## Domain

An abstract value (`AV`) is an integer interval, the length interval of an array, a tuple of
abstract values, or no information. The value of each node is met with the range of its
`ImpType` (`clampTy`): a node of type `u8` lies in `[0, 255]`, an array of type `[T; n]` has
length `n`. A parameter of a function starts at the range of its type.

## Transfer

* `Add`, `Sub`, `Mul` with a width tag (`#8` … `#128`, `#size`, `#i32` …) or an integer node
  type: the interval of the exact result; safe when it lies in the range of the width.
* `Div`, `Rem`: safe when the divisor interval excludes `0` and, signed, the pair
  `(MIN, -1)` is excluded. `Shl`, `Shr`: safe when the amount lies in `[0, w)`. `Neg`
  (signed): safe when `MIN` is excluded.
* `index`, `array_update`, `vec_remove`: safe when the index lies in `[0, n)` for every
  length `n` of the array's length interval. `index` on a range (`Range`, `RangeTo`,
  `RangeFrom`, `RangeFull`) is a slice, safe when `0 ≤ lo ≤ hi ≤ n`; `slice_update` also
  needs the source length to equal `hi - lo`, and `copy_from_slice` equal lengths, either
  both one constant or both slices over the same range expression.
* `unwrap`, `expect`, `panic`, `assert`, `assert_failed`: never counted safe.
* Wrapping, bitwise, cast and comparison heads are total; their intervals follow the
  operands where the result provably stays in range, and the type range otherwise.

## Control flow

A guard `a < b`, `a ≤ b`, `a == b`, `a != b` (and `!`, `&&`, `||` of guards) between a
variable and an expression refines the variable on each branch (`refine`). The arms of an
`if` or `match` are joined. A counted loop binds its counter to `[lo, hi - 1]`; the variables
it rebinds are iterated to a fixed point from the loop head, joined with the environments
at `break` and `continue`, widened from the third round on to the integer constants of the
function (`widenEnv`), and set to no information after eight rounds. The operations of a
loop body are counted once, on the fixed point.

## Call-site intervals and classes

Each function is analysed four times (`classify`): (A) with parameters at their type ranges,
which gives the argument intervals at each call site of the crate; the join of these per
function is its call-site precondition `pre`; (B) under `pre`, which gives a result interval
per function; (C) and (D) as (A) and (B) with the result intervals of (B) at calls. A
function is of class 1 when (C) proves all its operations safe, of class 2 when (D) does,
and of class 3 otherwise; a function that calls a function of class 3 is of class 3. The
arguments of every call lie in the callee's `pre`, since every caller's analysis starts at
its type ranges or at its own `pre`.

## The verified checker

The analysis above is untrusted: its intervals (`Itv`, `AV`) are a candidate generator. The
column `checked` of each function reports whether the verified checker
`Hax.Range.checkT` (`HaxLean/Range/Check.lean`, sound by `Hax.Range.checkT_rust_sound`) accepts
the function on the shared interval domain, from the candidates this analysis proposes
(`checkedFn`): its parameters at the call-site precondition of round (B) or at their type
ranges, the functions of the crate through summaries (their call-site precondition and their
result value of round (B)), and the type ranges of the variables a loop writes as loop
annotation (or none).

## Main definitions

* `Itv`, `AV`: the abstract domain.
* `clampTy`: the meet of an abstract value with the range of a type.
* `ev`: the abstract evaluation of a `TExpr`, counting operations.
* `analyzeFn`: the analysis of one function under parameter intervals.
* `classify`: the four rounds and the classes of a crate's functions.
* `toRangeAV`, `typeAV`, `annOfTypes`, `checkedFn`: the candidates for the verified checker
  and its verdict.
* `Hax.RangeProbe.run`: the command line `rangeprobe [--name N] PATH...`.
-/

@[expose] public section

namespace Hax.RangeProbe

/-- The bound standing for an unknown end of an interval. -/
def big : Int := 2 ^ 130

/-! ## Intervals -/

/-- A closed integer interval `[lo, hi]`; empty when `hi < lo`. -/
structure Itv where
  /-- The lower end. -/
  lo : Int
  /-- The upper end. -/
  hi : Int
  deriving BEq, Repr, Inhabited

namespace Itv

/-- The interval of one integer. -/
def exact (c : Int) : Itv := ⟨c, c⟩

/-- The interval with unknown ends. -/
def unknown : Itv := ⟨-big, big⟩

/-- The empty interval. -/
def empty : Itv := ⟨1, 0⟩

/-- Whether the interval holds no integer. -/
def isEmpty (a : Itv) : Bool := decide (a.hi < a.lo)

/-- Whether the interval holds exactly one integer. -/
def single? (a : Itv) : Option Int := if a.lo = a.hi then some a.lo else none

/-- The least interval holding both. -/
def join (a b : Itv) : Itv :=
  if a.isEmpty then b else if b.isEmpty then a else ⟨min a.lo b.lo, max a.hi b.hi⟩

/-- The intersection. -/
def meet (a b : Itv) : Itv := ⟨max a.lo b.lo, min a.hi b.hi⟩

/-- Whether every integer of `a` lies in `b`. -/
def sub? (a b : Itv) : Bool := a.isEmpty || (decide (b.lo ≤ a.lo) && decide (a.hi ≤ b.hi))

/-- Whether `c` lies outside `a`. -/
def excludes (a : Itv) (c : Int) : Bool := a.isEmpty || decide (c < a.lo) || decide (a.hi < c)

/-- A binary interval operation, empty when an argument is empty. -/
def lift2 (f : Itv → Itv → Itv) (a b : Itv) : Itv :=
  if a.isEmpty || b.isEmpty then empty else f a b

/-- The interval of the sums. -/
def add : Itv → Itv → Itv := lift2 fun a b => ⟨a.lo + b.lo, a.hi + b.hi⟩

/-- The interval of the differences. -/
def sub : Itv → Itv → Itv := lift2 fun a b => ⟨a.lo - b.hi, a.hi - b.lo⟩

/-- The interval of the products. -/
def mul : Itv → Itv → Itv := lift2 fun a b =>
  let ps := [a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi]
  ⟨ps.foldl min (a.lo * b.lo), ps.foldl max (a.lo * b.lo)⟩

/-- Whether both ends are nonnegative and the interval is not empty. -/
def nonneg (a : Itv) : Bool := !a.isEmpty && decide (0 ≤ a.lo)

end Itv

/-- The range of a machine integer of `bits` bits. -/
def wRange (bits : Nat) (signed : Bool) : Itv :=
  if signed then ⟨-2 ^ (bits - 1), 2 ^ (bits - 1) - 1⟩ else ⟨0, 2 ^ bits - 1⟩

/-- The width and signedness of an integer type, through references. -/
def intTy : ImpType → Option (Nat × Bool)
  | .uint w => some (w.bits, false)
  | .sint w => some (w.bits, true)
  | .ref t _ => intTy t
  | _ => none

/-- The static length of an array type, through references. -/
def staticLen : ImpType → Option Nat
  | .array _ n => some n
  | .ref t _ => staticLen t
  | _ => none

/-! ## Abstract values -/

/-- An abstract value: an integer interval, the length interval of an array, a tuple, or no
    information. -/
inductive AV where
  | top
  | num (i : Itv)
  | arr (len : Itv)
  | tup (es : List AV)
  deriving BEq, Repr, Inhabited

namespace AV

/-- The least abstract value above both. -/
partial def join : AV → AV → AV
  | .num a, .num b => .num (a.join b)
  | .arr a, .arr b => .arr (a.join b)
  | .tup es, .tup fs => if es.length = fs.length then .tup (es.zipWith join fs) else .top
  | _, _ => .top

/-- The interval of an integer value; unknown for any other value. -/
def itv : AV → Itv
  | .num i => i
  | _ => Itv.unknown

/-- The length interval of an array value; `[0, big]` for any other value. -/
def len : AV → Itv
  | .arr l => l
  | _ => ⟨0, big⟩

end AV

/-- The meet of an abstract value with the range of the type `ty`: the type's integer range,
    its static array length, or componentwise for a tuple type. -/
partial def clampTy (ty : ImpType) (av : AV) : AV :=
  match intTy ty with
  | some (b, s) =>
    let r := wRange b s
    match av with
    | .num i => .num (i.meet r)
    | _ => .num r
  | none =>
    match staticLen ty with
    | some n => .arr (Itv.exact n)
    | none =>
      match ty, av with
      | .tuple ts, .tup es =>
        if ts.length = es.length then .tup (ts.zipWith clampTy es)
        else .tup (ts.map (clampTy · .top))
      | .tuple ts, _ => .tup (ts.map (clampTy · .top))
      | _, _ => av

/-- The interval of a literal. -/
def litAV : ImpLit → AV
  | .int n => .num (Itv.exact n)
  | .uintLit _ n => .num (Itv.exact n)
  | .sintLit _ n => .num (Itv.exact n)
  | _ => .top

/-! ## Environments and widening -/

/-- An abstract environment: the abstract value of each bound variable. -/
abbrev AEnv := List (String × AV)

/-- The environment with `x` bound to `v`. -/
def AEnv.set (env : AEnv) (x : String) (v : AV) : AEnv :=
  (x, v) :: env.filter fun p => p.1 != x

/-- The join of two environments; a variable bound in one only keeps its value there. -/
def joinEnv (e1 e2 : AEnv) : AEnv :=
  let both := e1.map fun (x, a) =>
    match e2.lookup x with
    | some b => (x, a.join b)
    | none => (x, a)
  both ++ e2.filter fun p => (e1.lookup p.1).isNone

/-- Whether two environments bind the same variables to the same values. -/
def envEq (e1 e2 : AEnv) : Bool :=
  e1.length == e2.length && e1.all fun (x, a) => e2.lookup x == some a

/-- The upper end `hi` raised to the least threshold at or above it, or `big`. -/
def thrUp (thr : List Int) (hi : Int) : Int :=
  (thr.filter (hi ≤ ·)).foldl min big

/-- The lower end `lo` lowered to the greatest threshold at or below it, or `-big`. -/
def thrDown (thr : List Int) (lo : Int) : Int :=
  (thr.filter (· ≤ lo)).foldl max (-big)

/-- The widening of the interval `old` by `new` to the thresholds `thr`: an end that grew
    moves to the next threshold. -/
def widenItv (thr : List Int) (old new : Itv) : Itv :=
  if old.isEmpty then new
  else if new.isEmpty then old
  else
    ⟨if new.lo < old.lo then thrDown thr new.lo else old.lo,
     if old.hi < new.hi then thrUp thr new.hi else old.hi⟩

/-- The widening of abstract values, componentwise. -/
partial def widenAV (thr : List Int) : AV → AV → AV
  | .num a, .num b => .num (widenItv thr a b)
  | .arr a, .arr b => .arr (widenItv thr a b)
  | .tup es, .tup fs => if es.length = fs.length then .tup (es.zipWith (widenAV thr) fs) else .top
  | _, _ => .top

/-- The widening of the environment `old` by `new`, variable by variable. -/
def widenEnv (thr : List Int) (old new : AEnv) : AEnv :=
  new.map fun (x, b) =>
    match old.lookup x with
    | some a => (x, widenAV thr a b)
    | none => (x, b)

/-- `new` with every variable whose value differs from `old` set to no information. -/
def topChanged (old new : AEnv) : AEnv :=
  new.map fun (x, b) => if old.lookup x == some b then (x, b) else (x, .top)

/-! ## Checks -/

/-- The width tag of a head `Op#tag`: the width and whether the tag is signed. -/
def tagWidth (tag : String) : Option (Nat × Bool) :=
  let (signed, t) := if tag.startsWith "i" then (true, tag.drop 1 |>.toString) else (false, tag)
  if t == "size" then some (64, signed)
  else t.toNat?.bind fun n =>
    if n == 8 || n == 16 || n == 32 || n == 64 || n == 128 then some (n, signed) else none

/-- The base and the tag of a head `Op#tag`. -/
def splitHead (f : String) : String × Option String :=
  match f.splitOn "#" with
  | [b] => (b, none)
  | b :: t :: _ => (b, some t)
  | [] => (f, none)

/-- The width of a checked operation: from its tag, else from the node type; a tag naming
    no machine width (a field tag) gives no width. -/
def opWidth (tag : Option String) (ty : ImpType) : Option (Nat × Bool) :=
  match tag with
  | some t =>
    let tySigned := match intTy ty with
      | some (_, s') => s'
      | none => false
    (tagWidth t).map fun (b, s) => (b, s || tySigned)
  | none => intTy ty

/-- Checked `+ - *` at width `w`: the exact result lies in the range of `w`. -/
def checkedArith (r : Itv) (bits : Nat) (signed : Bool) : Bool :=
  r.sub? (wRange bits signed)

/-- Division and remainder: the divisor excludes `0`, and, signed, the dividend excludes
    `MIN` or the divisor excludes `-1`. -/
def divOk (a b : Itv) (bits : Nat) (signed : Bool) : Bool :=
  b.excludes 0 && (!signed || a.excludes (-2 ^ (bits - 1)) || b.excludes (-1))

/-- Shifts: the amount lies in `[0, bits)`. -/
def shiftOk (amt : Itv) (bits : Nat) : Bool := amt.sub? ⟨0, (bits : Int) - 1⟩

/-- Element access: the index lies in `[0, n)` for every length `n` of `len`. -/
def idxOk (i len : Itv) : Bool := i.isEmpty || (decide (0 ≤ i.lo) && decide (i.hi < len.lo))

/-- Slicing `lo..hi` of an array of length in `len`: `0 ≤ lo ≤ hi ≤ n`. -/
def sliceOk (lo hi len : Itv) : Bool :=
  lo.isEmpty || hi.isEmpty ||
    (decide (0 ≤ lo.lo) && decide (lo.hi ≤ hi.lo) && decide (hi.hi ≤ len.lo))

/-- Two lengths are one and the same constant. -/
def sameLen (a b : Itv) : Bool :=
  match a.single?, b.single? with
  | some x, some y => x == y
  | _, _ => false

/-- The range argument of a slicing `index`/`index_mut`, erased, when its bounds give the
    slice's length on their own (`Range`, `RangeTo`). -/
def sliceRangeOf : TExpr → Option ImpExpr
  | .mk (.app h [_, r@(.mk (.app rh _) _)]) _ =>
    if (h == "index" || h == "index_mut") && (rh == "Range" || rh == "RangeTo") then some r.erase
    else none
  | _ => none

/-- Whether a call argument is a range (`Range`, `RangeTo`, `RangeFrom`, `RangeFull`,
    `RangeInclusive`). -/
def isRange : TExpr → Bool
  | .mk (.app h _) _ =>
    h == "Range" || h == "RangeTo" || h == "RangeFrom" || h == "RangeFull" ||
      h == "RangeInclusive"
  | _ => false

/-- The children of a node. -/
def kids : TExprKind → List TExpr
  | .letBind _ v b => [v, b]
  | .lam _ b => [b]
  | .app _ as => as
  | .tuple es => es
  | .proj e _ => [e]
  | .ifThenElse c t f => [c, t, f]
  | .match_ s arms => s :: arms.map (·.2)
  | .seq a b => [a, b]
  | .borrow e | .deref e | .assign _ e | .earlyReturn e | .questionMark e | .cfBreak e
  | .cfContinue e | .cfBreakContinue e | .ann e | .namedProj _ e => [e]
  | .forLoop _ lo hi b | .forLoopRev _ lo hi b | .forFold _ lo hi b | .forFoldRev _ lo hi b
  | .forFoldReturn _ lo hi b | .forFoldRevReturn _ lo hi b => [lo, hi, b]
  | .whileLoop c b | .whileFold c b | .whileFoldReturn c b => [c, b]
  | .break_ (some e) => [e]
  | _ => []

/-- The integer literals of a term. -/
partial def litsOf : TExpr → List Int
  | .mk (.lit (.int n)) _ => [n]
  | .mk (.lit (.uintLit _ n)) _ => [n]
  | .mk (.lit (.sintLit _ n)) _ => [n]
  | .mk k _ => (kids k).flatMap litsOf

/-- The widening thresholds of a term: its integer constants, their neighbours and `0`. -/
def thresholds (e : TExpr) : List Int :=
  ((litsOf e).flatMap fun n => [n - 1, n, n + 1]) ++ [0] |>.eraseDups

/-! ## Abstract evaluation -/

/-- The context of an evaluation: whether operations are counted, the crate's functions
    with their result values, and the widening thresholds. -/
structure Cx where
  /-- Whether operations and calls are recorded. -/
  record : Bool := true
  /-- The functions of the crate, with a result value where one is known. -/
  fns : Std.HashMap String (Option AV) := {}
  /-- The widening thresholds. -/
  thr : List Int := [0]
  deriving Inhabited

/-- The state of an evaluation. -/
structure St where
  /-- The current environment. -/
  env : AEnv := []
  /-- The join of the environments at `break` and `continue` of the innermost loop. -/
  jump : Option AEnv := none
  /-- The join of the values returned early. -/
  ret : Option AV := none
  /-- The counted operations: the kind of each and whether it is proved safe. -/
  obls : Array (String × Bool) := #[]
  /-- The calls of crate functions with the abstract values of their arguments. -/
  calls : Array (String × List AV) := #[]
  deriving Inhabited

/-- The evaluation monad. -/
abbrev M := ReaderT Cx (StateM St)

/-- Record an operation of kind `kind`, proved safe when `ok`. -/
def oblig (kind : String) (ok : Bool) : M Unit := do
  if (← read).record then
    modify fun s => { s with obls := s.obls.push (if ok then (kind, true) else (kind, false)) }

/-- Replace the current environment. -/
def setEnv (env : AEnv) : M Unit := modify fun s => { s with env }

/-- Bind `x` to `v` in the current environment. -/
def setVar (x : String) (v : AV) : M Unit := modify fun s => { s with env := s.env.set x v }

/-- Join the current environment into the loop's jump environment. -/
def addJump : M Unit := modify fun s =>
  { s with jump := some (match s.jump with | some j => joinEnv j s.env | none => s.env) }

/-- Join a value into the early-return value. -/
def addRet (v : AV) : M Unit := modify fun s =>
  { s with ret := some (match s.ret with | some r => r.join v | none => v) }

/-- The relation of a comparison head, as `(strict, swapped)` for `<`, `≤`, `>`, `≥`. -/
def cmpOf : String → Option (Bool × Bool)
  | "Lt" | "lt" => some (true, false)
  | "Le" | "le" => some (false, false)
  | "Gt" | "gt" => some (true, true)
  | "Ge" | "ge" => some (false, true)
  | _ => none

/-- The variable a guard operand names, through `deref`, `borrow` and annotations. -/
partial def sideVar : TExpr → Option String
  | .mk (.var x) _ => some x
  | .mk (.deref e) _ | .mk (.borrow e) _ | .mk (.ann e) _ => sideVar e
  | .mk (.app "deref" [e]) _ => sideVar e
  | _ => none

/-- `a` refined by `a < b` (`strict`) or `a ≤ b`. -/
def refineBelow (a b : Itv) (strict : Bool) : Itv :=
  a.meet ⟨-big, if strict then b.hi - 1 else b.hi⟩

/-- `b` refined by `a < b` (`strict`) or `a ≤ b`. -/
def refineAbove (a b : Itv) (strict : Bool) : Itv :=
  b.meet ⟨if strict then a.lo + 1 else a.lo, big⟩

/-- `a` refined by `a ≠ b`: a constant `b` at an end of `a` moves that end. -/
def refineNe (a b : Itv) : Itv :=
  match b.single? with
  | some c =>
    if a.lo = c then ⟨a.lo + 1, a.hi⟩ else if a.hi = c then ⟨a.lo, a.hi - 1⟩ else a
  | none => a

/-- The relation `l R r` refined into the variables among `l` and `r`; `rel` is
    `0` for `<`, `1` for `≤`, `2` for `=`, `3` for `≠`. -/
def refineRel (rel : Nat) (l r : TExpr) (li ri : Itv) (env : AEnv) : AEnv :=
  let nl : Itv := match rel with
    | 0 => refineBelow li ri true
    | 1 => refineBelow li ri false
    | 2 => li.meet ri
    | _ => refineNe li ri
  let nr : Itv := match rel with
    | 0 => refineAbove li ri true
    | 1 => refineAbove li ri false
    | 2 => li.meet ri
    | _ => refineNe ri li
  let env := match sideVar l with
    | some x => env.set x (.num nl)
    | none => env
  match sideVar r with
  | some x => env.set x (.num nr)
  | none => env

mutual

/-- The abstract value of a term; counts its operations when the context records. -/
partial def ev : TExpr → M AV
  | .mk k ty => do
    let v ← evK ty k
    pure (clampTy ty v)

/-- The value of a term evaluated in `env` without recording, leaving the state as it was. -/
partial def evIn (env : AEnv) (e : TExpr) : M AV := do
  let s ← get
  setEnv env
  let v ← withReader (fun c => { c with record := false }) (ev e)
  set s
  pure v

/-- The environment `env` refined by the guard `c` holding (`pos`) or failing. -/
partial def refine (c : TExpr) (pos : Bool) (env : AEnv) : M AEnv := do
  match c with
  | .mk (.app "Not" [c']) _ => refine c' (!pos) env
  | .mk (.ann c') _ => refine c' pos env
  | .mk (.app "&&" [a, b]) _ =>
    if pos then refine b true (← refine a true env) else pure env
  | .mk (.app "||" [a, b]) _ =>
    if pos then pure env else refine b false (← refine a false env)
  | .mk (.app op [a, b]) _ =>
    let ai := (← evIn env a).itv
    let bi := (← evIn env b).itv
    if op == "Eq" || op == "eq" then
      pure (refineRel (if pos then 2 else 3) a b ai bi env)
    else if op == "Ne" || op == "ne" then
      pure (refineRel (if pos then 3 else 2) a b ai bi env)
    else
      match cmpOf op with
      | some (strict, swapped) =>
        -- `l < r` holding, or `r ≤ l` when it fails.
        let (l, r, li, ri) := if swapped then (b, a, bi, ai) else (a, b, ai, bi)
        if pos then pure (refineRel (if strict then 0 else 1) l r li ri env)
        else pure (refineRel (if strict then 1 else 0) r l ri li env)
      | none => pure env
  | _ => pure env

/-- The abstract value of a node of kind `k` and type `ty`. -/
partial def evK (ty : ImpType) : TExprKind → M AV
  | .lit l => pure (litAV l)
  | .var x => do pure (((← get).env.lookup x).getD .top)
  | .letBind x v b => do
    let a ← ev v
    setVar x a
    ev b
  | .lam ps b => do
    let env0 := (← get).env
    for p in ps do setVar p .top
    let _ ← ev b
    setEnv env0
    pure .top
  | .app f args => evApp ty f args
  | .tuple es => do pure (.tup (← es.mapM ev))
  | .proj e i => do
    match ← ev e with
    | .tup es => pure (es.getD i .top)
    | _ => pure .top
  | .ifThenElse c t f => do
    let _ ← ev c
    let env0 := (← get).env
    setEnv (← refine c true env0)
    let a ← ev t
    let e1 := (← get).env
    setEnv (← refine c false env0)
    let b ← ev f
    setEnv (joinEnv e1 (← get).env)
    pure (a.join b)
  | .match_ s arms => do
    let _ ← ev s
    let env0 := (← get).env
    let mut acc : Option (AEnv × AV) := none
    for (p, b) in arms do
      setEnv ((patBinders p).foldl (fun env x => env.set x .top) env0)
      let v ← ev b
      let e := (← get).env
      acc := some (match acc with
        | some (ea, va) => (joinEnv ea e, va.join v)
        | none => (e, v))
    match acc with
    | some (e, v) => do setEnv e; pure v
    | none => pure .top
  | .unitVal => pure .top
  | .seq a b => do
    let _ ← ev a
    ev b
  | .borrow e | .deref e | .ann e => ev e
  | .assign x r => do
    setVar x (← ev r)
    pure .top
  | .forLoop x lo hi b | .forLoopRev x lo hi b | .forFold x lo hi b | .forFoldRev x lo hi b
  | .forFoldReturn x lo hi b | .forFoldRevReturn x lo hi b => evFor x lo hi b
  | .whileLoop c b | .whileFold c b | .whileFoldReturn c b => evWhile c b
  | .break_ (some e) | .cfBreak e | .cfContinue e | .cfBreakContinue e => do
    let a ← ev e
    addJump
    pure a
  | .break_ none | .continue_ => do
    addJump
    pure .top
  | .earlyReturn e => do
    addRet (← ev e)
    pure .top
  | .questionMark e | .namedProj _ e => do
    let _ ← ev e
    pure .top

/-- The fixed point of a loop body from the head environment `head0`: `step` runs one
    iteration from the head; the result is the head environment at the fixed point. -/
partial def loopHead (head0 : AEnv) (step : AEnv → M Unit) : M AEnv := do
  let thr := (← read).thr
  let mut head := head0
  let mut stable := false
  for k in [0:8] do
    modify fun s => { s with jump := none }
    withReader (fun c => { c with record := false }) (step head)
    let s ← get
    let after := match s.jump with
      | some j => joinEnv s.env j
      | none => s.env
    let nxt0 := joinEnv head after
    let nxt := if k ≥ 2 then widenEnv thr head nxt0 else nxt0
    if envEq nxt head then
      stable := true
      break
    head := nxt
  if stable then pure head
  else
    modify fun s => { s with jump := none }
    withReader (fun c => { c with record := false }) (step head)
    let s ← get
    let after := match s.jump with
      | some j => joinEnv s.env j
      | none => s.env
    pure (topChanged head (joinEnv head after))

/-- A counted loop over `[lo, hi)` with counter `x`. -/
partial def evFor (x : String) (lo hi b : TExpr) : M AV := do
  let l := (← ev lo).itv
  let h := (← ev hi).itv
  let ctr : AV := .num ⟨l.lo, h.hi - 1⟩
  let saved := (← get).jump
  let head ← loopHead (← get).env fun env => do
    setEnv (env.set x ctr)
    let _ ← ev b
  modify fun s => { s with jump := none }
  setEnv (head.set x ctr)
  let _ ← ev b
  let s ← get
  let after := match s.jump with
    | some j => joinEnv s.env j
    | none => s.env
  set { s with env := joinEnv head after, jump := saved }
  pure .top

/-- A `while` loop with guard `c`. -/
partial def evWhile (c b : TExpr) : M AV := do
  let saved := (← get).jump
  let head ← loopHead (← get).env fun env => do
    setEnv env
    let _ ← ev c
    setEnv (← refine c true (← get).env)
    let _ ← ev b
  modify fun s => { s with jump := none }
  setEnv head
  let _ ← ev c
  let afterC := (← get).env
  setEnv (← refine c true afterC)
  let _ ← ev b
  let s ← get
  let exits := match s.jump with
    | some j => joinEnv s.env j
    | none => s.env
  set { s with jump := saved }
  setEnv (joinEnv (← refine c false afterC) exits)
  pure .top

/-- The slice `a[r]` for a range `r`: its check and the length of the slice. -/
partial def evSlice (a r : TExpr) : M AV := do
  let la := (← ev a).len
  let (lo, hi, rlen) ← match r with
    | .mk (.app "Range" [x, y]) _ => do
      let li := (← ev x).itv
      let hi := (← ev y).itv
      pure (li, hi, hi.sub li)
    | .mk (.app "RangeInclusive" [x, y]) _ => do
      let li := (← ev x).itv
      let hi := (← ev y).itv.add (Itv.exact 1)
      pure (li, hi, hi.sub li)
    | .mk (.app "RangeTo" [y]) _ => do
      let hi := (← ev y).itv
      pure (Itv.exact 0, hi, hi)
    | .mk (.app "RangeFrom" [x]) _ => do
      let li := (← ev x).itv
      pure (li, la, la.sub li)
    | _ => pure (Itv.exact 0, la, la)
  let ok := sliceOk lo hi la
  oblig (if ok then "slice" else if la.single?.isSome then "slice:range" else "slice:dynlen") ok
  pure (.arr (rlen.meet ⟨0, big⟩))

/-- A call of the head `f` on `args` at a node of type `ty`. -/
partial def evApp (ty : ImpType) (f : String) (args : List TExpr) : M AV := do
  match f, args with
  | "&&", [a, b] => do
    let _ ← ev a
    let env0 := (← get).env
    setEnv (← refine a true env0)
    let _ ← ev b
    setEnv (joinEnv (← refine a false env0) (← get).env)
    pure .top
  | "||", [a, b] => do
    let _ ← ev a
    let env0 := (← get).env
    setEnv (← refine a false env0)
    let _ ← ev b
    setEnv (joinEnv (← refine a true env0) (← get).env)
    pure .top
  | "index", [a, r] | "index_mut", [a, r] =>
    if isRange r then evSlice a r
    else do
      let la := (← ev a).len
      let i := (← ev r).itv
      let ok := idxOk i la
      oblig (if ok then "index" else if la.single?.isSome then "index:range" else "index:dynlen")
        ok
      pure .top
  | _, _ => do
    let avs ← args.mapM ev
    let (base, tag) := splitHead f
    match base, avs with
    | "Add", [a, b] | "Sub", [a, b] | "Mul", [a, b] =>
      let r := if base == "Add" then a.itv.add b.itv
        else if base == "Sub" then a.itv.sub b.itv else a.itv.mul b.itv
      let kind := base.toLower
      match opWidth tag ty with
      | some (bits, signed) =>
        oblig kind (checkedArith r bits signed)
        pure (.num r)
      | none =>
        if tag.isSome then pure .top
        else
          oblig "untagged" (a.itv.single?.isSome && b.itv.single?.isSome)
          pure (.num r)
    | "Div", [a, b] | "Rem", [a, b] =>
      match opWidth tag ty with
      | some (bits, signed) =>
        oblig base.toLower (divOk a.itv b.itv bits signed)
        let ai := a.itv
        let bi := b.itv
        if ai.nonneg && decide (0 < bi.lo) && !bi.isEmpty then
          if base == "Div" then pure (.num ⟨ai.lo / bi.hi, ai.hi / bi.lo⟩)
          else pure (.num ⟨0, min ai.hi (bi.hi - 1)⟩)
        else pure .top
      | none =>
        if tag.isSome then pure .top
        else
          oblig "untagged" (b.itv.excludes 0 && a.itv.single?.isSome && b.itv.single?.isSome)
          pure .top
    | "Shl", [a, b] | "Shr", [a, b] =>
      match opWidth tag ty with
      | some (bits, signed) =>
        let amt := b.itv
        oblig base.toLower (shiftOk amt bits)
        let ai := a.itv
        if signed || !ai.nonneg || !amt.nonneg || amt.isEmpty then pure .top
        else if base == "Shr" then
          pure (.num ⟨ai.lo.toNat >>> amt.hi.toNat, ai.hi.toNat >>> amt.lo.toNat⟩)
        else if decide (ai.hi * 2 ^ amt.hi.toNat < 2 ^ bits) then
          pure (.num ⟨ai.lo * 2 ^ amt.lo.toNat, ai.hi * 2 ^ amt.hi.toNat⟩)
        else pure .top
      | none =>
        if tag.isSome then pure .top
        else
          oblig "untagged" false
          pure .top
    | "Neg", [a] =>
      match opWidth tag ty with
      | some (bits, true) =>
        oblig "neg" (a.itv.excludes (-2 ^ (bits - 1)))
        pure (.num ⟨-a.itv.hi, -a.itv.lo⟩)
      | _ => pure .top
    | "array_update", [a, i, _] =>
      let ok := idxOk i.itv a.len
      oblig (if ok then "index" else if a.len.single?.isSome then "index:range" else "index:dynlen")
        ok
      pure a
    | "vec_remove", [a, i] =>
      let ok := idxOk i.itv a.len
      oblig (if ok then "index" else if a.len.single?.isSome then "index:range" else "index:dynlen")
        ok
      pure .top
    | "slice_update", [d, lo, hi, src] =>
      let n := hi.itv.sub lo.itv
      oblig "slice_update" (sliceOk lo.itv hi.itv d.len && sameLen n src.len)
      pure d
    | "copy_from_slice", [dst, src] =>
      let same := match args with
        | [x, y] => (sliceRangeOf x).isSome && sliceRangeOf x == sliceRangeOf y
        | _ => false
      oblig "copy_from_slice" (sameLen dst.len src.len || same)
      pure dst
    | "unwrap", _ | "expect", _ | "panic", _ | "assert", _ | "assert_failed", _ =>
      oblig base false
      pure .top
    | "len", [a] => pure (.num (a.len.meet ⟨0, 2 ^ 64 - 1⟩))
    | "repeat", [_, n] | "from_elem", [_, n] => pure (.arr (n.itv.meet ⟨0, big⟩))
    | "array_lit", _ => pure (.arr (Itv.exact args.length))
    | "push", [v, _] => pure (.arr (v.len.add (Itv.exact 1)))
    | "extend_from_slice", [v, s] | "append", [v, s] => pure (.arr (v.len.add s.len))
    | "with_capacity", _ => pure (.arr (Itv.exact 0))
    | "to_vec", [a] | "clone", [a] | "deref", [a] | "borrow", [a] => pure a
    | "cast", [a] | "wrapping_add", [a] =>
      -- A cast keeps a value that its target range holds; `clampTy` checks the target.
      match intTy ty with
      | some (b, s) => pure (if a.itv.sub? (wRange b s) then a else .top)
      | none => pure .top
    | "BitAnd", [a, b] =>
      if a.itv.nonneg then pure (.num ⟨0, a.itv.hi⟩)
      else if b.itv.nonneg then pure (.num ⟨0, b.itv.hi⟩)
      else pure .top
    | "BitOr", [a, b] | "BitXor", [a, b] =>
      if a.itv.nonneg && b.itv.nonneg then
        pure (.num ⟨0, ((max a.itv.hi b.itv.hi).toNat + 1).nextPowerOfTwo - 1⟩)
      else pure .top
    | _, _ =>
      let fns := (← read).fns
      match fns.get? f with
      | some r =>
        if (← read).record then
          modify fun s => { s with calls := s.calls.push (f, avs) }
        pure (r.getD .top)
      | none => pure .top

end

/-! ## Functions -/

/-- The parameters of a definition with their types, read off the bindings `let x := x`
    that open its body, and the rest of the body. -/
partial def stripParams : TExpr → List (String × ImpType) × TExpr
  | e@(.mk (.letBind x (.mk (.var y) ty) b) _) =>
    if x == y then
      let (ps, b') := stripParams b
      ((x, ty) :: ps, b')
    else ([], e)
  | e => ([], e)

/-- The result of analysing one function. -/
structure FnResult where
  /-- The counted operations with their kinds. -/
  obls : Array (String × Bool)
  /-- The calls of crate functions with their argument values. -/
  calls : Array (String × List AV)
  /-- The value of the function. -/
  ret : AV
  deriving Inhabited

/-- The analysis of the function with parameters `ps` and body `body`, the parameters bound
    to `pre` (their type ranges when `pre` is absent or of another arity). -/
def analyzeFn (fns : Std.HashMap String (Option AV)) (ps : List (String × ImpType))
    (body : TExpr) (pre : Option (List AV)) : FnResult :=
  let pv : List AV := match pre with
    | some vs => if vs.length = ps.length then vs else ps.map fun _ => .top
    | none => ps.map fun _ => .top
  let env : AEnv := (ps.zip pv).map fun ((x, ty), v) => (x, clampTy ty v)
  let cx : Cx := { record := true, fns, thr := thresholds body }
  let (v, s) := ((ev body).run cx).run { env }
  let ret := match s.ret with
    | some r => r.join v
    | none => v
  { obls := s.obls, calls := s.calls, ret }

/-! ## Candidates for the verified checker -/

/-- An abstract value of this analysis as one of the verified checker: an interval with a
    known end pair, an array-length interval, or no information. -/
def toRangeAV : AV → Range.AV
  | .num i => if i.lo ≤ -big || big ≤ i.hi || i.hi < i.lo then .top else .num (i.lo, i.hi)
  | .arr l => if l.hi < l.lo then .top else .arr (l.lo, l.hi)
  | _ => .top

/-- The abstract value of a type: the range of an integer type, the length of an array type;
    no information otherwise. -/
def typeAV (ty : ImpType) : Range.AV :=
  match intTy ty with
  | some (b, s) => let r := wRange b s; .num (r.lo, r.hi)
  | none =>
    match staticLen ty with
    | some n => .arr (n, n)
    | none => .top

/-- The type ranges of the variables a term binds or assigns, as a loop annotation. -/
partial def annOfTypes : TExpr → Range.AEnv
  | .mk (.letBind x v b) _ => (x, typeAV v.ty) :: annOfTypes v ++ annOfTypes b
  | .mk (.assign x r) _ => (x, typeAV r.ty) :: annOfTypes r
  | .mk k _ => (kids k).flatMap annOfTypes

/-- Whether the verified checker accepts a definition with parameters `ps` at `pre` (their
    type ranges when absent) and the summaries `sums`, with the type ranges as loop
    annotation or with none. -/
def checkedFn (sums : List (String × (List Range.AV × Range.AV))) (ps : List (String × ImpType))
    (pre : Option (List AV)) (e : TExpr) : Bool :=
  let pv : List Range.AV := match pre with
    | some vs => if vs.length = ps.length then
        (ps.zip vs).map fun ((_, t), v) =>
          match toRangeAV v, typeAV t with
          | .num a, .num b => .num (CatCrypt.Crypto.SecureCompilation.RangeDomain.ivMeet a b)
          | a, .top => a
          | _, b => b
      else ps.map fun (_, t) => typeAV t
    | none => ps.map fun (_, t) => typeAV t
  let Γ : Range.AEnv := (ps.zip pv).map fun ((x, _), a) => (x, a)
  (Range.checkT (Range.stdSpec sums (annOfTypes e)) Γ e).isSome ||
    (Range.checkT (Range.stdSpec sums []) Γ e).isSome

/-- The class of each function and its analyses (C) and (D) (see the module docstring). -/
structure FnRow where
  /-- The function. -/
  name : String
  /-- The operations counted at the parameters' type ranges. -/
  full : Array (String × Bool)
  /-- The operations counted under the call-site precondition. -/
  ctx : Array (String × Bool)
  /-- The class: 1, 2 or 3. -/
  cls : Nat
  /-- The number of call sites of class-3 functions. -/
  monadicCalls : Nat
  /-- Whether the function has a counted operation or calls one that has (transitively). -/
  baseline : Bool
  /-- Whether the verified checker accepts the function (`checkedFn`). -/
  checked : Bool := false
  deriving Inhabited

/-- The join of the argument values at the call sites of each function, of the arity of its
    parameters; absent for a function without call sites or called at another arity. -/
def callPre (defs : List (String × List (String × ImpType) × TExpr))
    (calls : List (String × List AV)) : Std.HashMap String (List AV) := Id.run do
  let arity : Std.HashMap String Nat := defs.foldl (fun m (n, ps, _) => m.insert n ps.length) {}
  let mut pre : Std.HashMap String (Option (List AV)) := {}
  for (g, avs) in calls do
    let ok := arity.get? g == some avs.length
    let cur := pre.get? g
    let nxt : Option (List AV) :=
      if !ok then none
      else match cur with
        | some (some vs) => some (vs.zipWith AV.join avs)
        | some none => none
        | none => some avs
    pre := pre.insert g nxt
  pure (pre.fold (fun m g v => match v with | some vs => m.insert g vs | none => m) {})

/-- Whether every counted operation is proved safe. -/
def allSafe (os : Array (String × Bool)) : Bool := os.all (·.2)

/-- The four analyses of a crate's definitions and the class of each function. -/
def classify (defs0 : List (String × TExpr)) : List FnRow := Id.run do
  let defs := defs0.map fun (n, e) => let (ps, b) := stripParams e; (n, ps, b)
  let noSum : Std.HashMap String (Option AV) :=
    defs.foldl (fun m (n, _, _) => m.insert n none) {}
  -- (A) type ranges, no result values.
  let ra := defs.map fun (n, ps, b) => (n, analyzeFn noSum ps b none)
  let pre := callPre defs (ra.flatMap fun (_, r) => r.calls.toList)
  -- (B) call-site preconditions, no result values.
  let rb := defs.map fun (n, ps, b) => (n, analyzeFn noSum ps b (pre.get? n))
  let sum : Std.HashMap String (Option AV) :=
    rb.foldl (fun m (n, r) => m.insert n (some r.ret)) {}
  -- (C) and (D) with the result values of (B).
  let rc := defs.map fun (n, ps, b) => (n, analyzeFn sum ps b none)
  let rd := defs.map fun (n, ps, b) => (n, analyzeFn sum ps b (pre.get? n))
  let own : Std.HashMap String Nat := (rc.zip rd).foldl (fun m ((n, c), (_, d)) =>
    m.insert n (if allSafe c.obls then 1 else if allSafe d.obls then 2 else 3)) {}
  let callees : Std.HashMap String (List String) := (rc.zip rd).foldl (fun m ((n, c), (_, d)) =>
    m.insert n ((c.calls.toList ++ d.calls.toList).map (·.1)).eraseDups) {}
  -- A function calling a class-3 function is of class 3; the baseline closure likewise.
  let mut cls := own
  let mut base : Std.HashMap String Bool :=
    rc.foldl (fun m (n, c) => m.insert n (!c.obls.isEmpty)) {}
  let mut changed := true
  while changed do
    changed := false
    for (n, _, _) in defs do
      let cs := (callees.get? n).getD []
      if cls.get? n != some 3 && cs.any (fun g => cls.get? g == some 3) then
        cls := cls.insert n 3
        changed := true
      if base.get? n != some true && cs.any (fun g => base.get? g == some true) then
        base := base.insert n true
        changed := true
  -- The summaries for the verified checker: call-site precondition and result of (B).
  let sums : List (String × (List Range.AV × Range.AV)) := rb.filterMap fun (n, r) =>
    (pre.get? n).map fun vs => (n, (vs.map toRangeAV, toRangeAV r.ret))
  let chk : Std.HashMap String Bool := defs.foldl (fun m (n, ps, _) =>
    let e := (defs0.lookup n).getD default
    m.insert n (checkedFn sums ps (pre.get? n) e)) {}
  pure <| (rc.zip rd).map fun ((n, c), (_, d)) =>
    { name := n, full := c.obls, ctx := d.obls, cls := (cls.get? n).getD 3,
      monadicCalls := (d.calls.filter fun (g, _) => cls.get? g == some 3).size,
      baseline := (base.get? n).getD false, checked := (chk.get? n).getD false }

/-- The kinds of the unproved operations with their counts, as `kind=count,…`. -/
def residual (os : Array (String × Bool)) : List (String × Nat) :=
  os.foldl (fun acc (k, ok) =>
    if ok then acc
    else match acc.lookup k with
      | some c => (k, c + 1) :: acc.filter (·.1 != k)
      | none => (k, 1) :: acc) []

/-- The TSV line of a function: name, operations, safe under the call-site precondition,
    class, safe at type ranges, calls of class-3 functions, whether the verified checker
    accepts it, unproved kinds. -/
def rowLine (r : FnRow) : String :=
  let res := ",".intercalate ((residual r.ctx).map fun (k, c) => s!"{k}={c}")
  s!"{r.name}\t{r.full.size}\t{(r.ctx.filter (·.2)).size}\t{r.cls}\t" ++
    s!"{(r.full.filter (·.2)).size}\t{r.monadicCalls}\t{if r.checked then 1 else 0}\t{res}"

/-- The summary lines of a crate. -/
def summaryLines (crate : String) (rows : List FnRow) : List String :=
  let count (p : FnRow → Bool) := (rows.filter p).length
  let ops := rows.foldl (fun a r => a + r.full.size) 0
  let safeFull := rows.foldl (fun a r => a + (r.full.filter (·.2)).size) 0
  let safeCtx := rows.foldl (fun a r => a + (r.ctx.filter (·.2)).size) 0
  let res := residual (rows.foldl (fun a r => a ++ r.ctx) #[])
  [s!"# {crate}\tfunctions={rows.length}\tclass1={count (·.cls == 1)}\t" ++
    s!"class2={count (·.cls == 2)}\tclass3={count (·.cls == 3)}\t" ++
    s!"baseline_monadic={count (·.baseline)}\tbaseline_to_pure=" ++
    s!"{count (fun r => r.baseline && r.cls != 3)}\tops={ops}\tsafe_full={safeFull}\t" ++
    s!"safe={safeCtx}\tchecked={count (·.checked)}\t" ++
    s!"checked_with_ops={count (fun r => r.checked && !r.full.isEmpty)}"] ++
  ((res.toArray.qsort (fun a b => a.2 > b.2)).toList.map fun (k, c) =>
    s!"# {crate}\tresidual\t{k}\t{c}")

/-! ## Checks on small terms -/

namespace Examples

/-- `u8`. -/
def u8 : ImpType := .uint .w8
/-- `usize`. -/
def us : ImpType := .uint .wsize
/-- `[u8; 16]`. -/
def a16 : ImpType := .array u8 16
/-- A variable node. -/
def v (x : String) (t : ImpType) : TExpr := .mk (.var x) t
/-- An integer literal node. -/
def n (k : Int) (t : ImpType) : TExpr := .mk (.lit (.int k)) t
/-- A call node. -/
def ap (f : String) (as : List TExpr) (t : ImpType) : TExpr := .mk (.app f as) t
/-- A parameter binding `let x := x` in front of `b`. -/
def prm (x : String) (t : ImpType) (b : TExpr) : TExpr := .mk (.letBind x (v x t) b) b.ty
/-- The classes of a list of definitions. -/
def classes (ds : List (String × TExpr)) : List Nat := (classify ds).map (·.cls)

/-- `for i in 0..hi { a[i] }` with `a : [u8; 16]`. -/
def loopIdx (hi : Int) : TExpr :=
  prm "a" a16 (.mk (.forFold "i" (n 0 us) (n hi us) (ap "index" [v "a" a16, v "i" us] u8)) .unit)
/-- `if i < 16 { a[i] } else { 0 }` with `i : usize`. -/
def guarded : TExpr := prm "a" a16 (prm "i" us (.mk (.ifThenElse
  (ap "Lt" [v "i" us, n 16 us] .bool) (ap "index" [v "a" a16, v "i" us] u8) (n 0 u8)) u8))
/-- `h(a, i) = a[i]`, safe only under its call sites. -/
def hF : TExpr := prm "a" a16 (prm "i" us (ap "index" [v "a" a16, v "i" us] u8))
/-- `k(a) = for j in 0..16 { h(a, j) }`. -/
def kF : TExpr := prm "a" a16
  (.mk (.forFold "j" (n 0 us) (n 16 us) (ap "h" [v "a" a16, v "j" us] u8)) .unit)
/-- `x + 1` on `x : u8`, or `if x < 100 { x + 100 } else { 0 }` when `g`. -/
def addF (g : Bool) : TExpr := prm "x" u8 (if g then
  .mk (.ifThenElse (ap "Lt" [v "x" u8, n 100 u8] .bool) (ap "Add#8" [v "x" u8, n 100 u8] u8)
    (n 0 u8)) u8 else ap "Add#8" [v "x" u8, n 1 u8] u8)
/-- `let i = 0; while i < 16 { a[i]; i = i + 1 }`. -/
def whileF : TExpr := prm "a" a16 (.mk (.letBind "i" (n 0 us) (.mk (.whileLoop
  (ap "Lt" [v "i" us, n 16 us] .bool)
  (.mk (.seq (ap "index" [v "a" a16, v "i" us] u8)
    (.mk (.assign "i" (ap "Add#size" [v "i" us, n 1 us] us)) .unit)) .unit)) .unit)) .unit)

/-- A counter over `0..16` indexes `[u8; 16]` safely; over `0..17` it does not. -/
def chkLoop : Bool := classes [("f", loopIdx 16)] == [1] && classes [("f", loopIdx 17)] == [3]
#guard chkLoop

/-- The guard `i < 16` proves the index safe at the full range of `i`. -/
def chkGuard : Bool := classes [("g", guarded)] == [1]
#guard chkGuard

/-- `h` is safe under the interval `[0, 15]` of its call site in `k`, and `k` stays pure. -/
def chkCallSite : Bool := classes [("h", hF), ("k", kF)] == [2, 1]
#guard chkCallSite

/-- `x + 1` overflows at `x = 255`; under `x < 100`, `x + 100` does not. -/
def chkAdd : Bool := classes [("a", addF false), ("b", addF true)] == [3, 1]
#guard chkAdd

/-- The `while` counter is widened to the threshold `16`; the index and the increment are
    safe. -/
def chkWhile : Bool :=
  (classify [("w", whileF)]).map (fun r => (r.cls, r.full)) ==
    [(1, #[("index", true), ("add", true)])]
#guard chkWhile

/-- The verified checker accepts the guarded index, the counted loop over `0..16`, `x + 100`
    under `x < 100`, and `h` under its call site in `k`; it refuses the loop over `0..17` and
    `x + 1`. -/
def chkVerified : Bool :=
  let ck (ds : List (String × TExpr)) := (classify ds).map (·.checked)
  ck [("g", guarded)] == [true] && ck [("f", loopIdx 16)] == [true] &&
    ck [("f", loopIdx 17)] == [false] && ck [("a", addF false), ("b", addF true)] == [false, true]
    && ck [("h", hF), ("k", kF)] == [true, true]
#guard chkVerified

end Examples

/-! ## Command line -/

/-- The export file a command-line path names: the path itself when it is a file, else
    `PATH/hax_frontend_export.json`. -/
def exportOf (path : System.FilePath) : IO System.FilePath := do
  if ← path.isDir then pure (path / "hax_frontend_export.json") else pure path

/-- The command line `rangeprobe [--name N] PATH...`: for each export, one header line, one
    TSV line per function and the summary lines. -/
def run (args : List String) : IO UInt32 := do
  let (name, paths) := match args with
    | "--name" :: n :: rest => (some n, rest)
    | rest => (none, rest)
  if paths.isEmpty then
    IO.eprintln "usage: rangeprobe [--name N] PATH..."
    return 1
  IO.println "function\tops\tsafe\tclass\tsafe_full\tmonadic_calls\tchecked\tresidual"
  for p in paths do
    let f ← exportOf p
    let crate := name.getD ((f.parent.bind (·.fileName)).getD f.toString)
    let input ← IO.FS.readFile f
    match certifiedTExprs input with
    | .error msg => IO.println s!"# {crate}\terror\t{msg.replace "\n" " "}"
    | .ok defs =>
      let rows := classify defs
      for r in rows do IO.println (rowLine r)
      for l in summaryLines crate rows do IO.println l
  return 0

end Hax.RangeProbe

/-- The entry point of `lake exe rangeprobe`. -/
def main (args : List String) : IO UInt32 :=
  Hax.RangeProbe.run args
