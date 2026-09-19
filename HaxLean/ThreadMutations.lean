/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.TExpr
public import HaxLean.InlineClosures

/-!
# Pre-pipeline normalization: thread mutations across `if`- and `match`-statement joins

A Rust `let mut v = …; if c { v = … } else { v = … }; <use v>` lowers (before this
pass) to `seq (ifThenElse c (assign v …) (assign v …)) rest`. `localMutation` then
rewrites each `assign v x` to a *locally-scoped* `let v := x; …` — so the new `v`
never escapes the branch, and `rest` sees the stale `v`. Worse, the branches end up
with mismatched types (a value-yielding arm vs a `()` arm).

This pass restructures an `if` or a `match` used as a STATEMENT (its value discarded
by an enclosing `seq`) so the mutated, still-live variables are returned by every
branch and rebound after the join:

    seq (if c then T else E) rest
  ↦ letBind _mtup (if c then (T; (v₁,…,vₙ)) else (E; (v₁,…,vₙ)))
       (let v₁ := _mtup.0; …; let vₙ := _mtup.(n-1); rest)

    seq (match s with | pᵢ => Bᵢ) rest
  ↦ letBind _mtup (match s with | pᵢ => (Bᵢ; (v₁,…,vₙ)))
       (let v₁ := _mtup.0; …; let vₙ := _mtup.(n-1); rest)

where `{v₁,…,vₙ}` = variables assigned in some branch that are still used in `rest`.
Because the appended tuple sits in the assigns' continuation, after `localMutation`
+ rendering each `vᵢ` resolves to its mutated value. A loop sitting at a branch
tail gains a continuation, so `functionalizeLoops`/the renderer emit its
`.merge` + projection instead of a bare `whileFold` (a `ControlFlow`).

Run BEFORE the typed pipeline (parse-time normalization, not a verified phase).
-/

@[expose] public section

namespace Hax

/-- Names assigned (`.assign`) anywhere in `e`. Structural recursion (one
    `match` arm per constructor) so the function is non-`partial` and admits the
    `tAssignedVars_erase` commutation lemma in `ThreadMutationsErase`. -/
def tAssignedVars : TExpr → List String
  | .mk (.assign n rhs) _ => n :: tAssignedVars rhs
  | .mk (.letBind _ v b) _ => tAssignedVars v ++ tAssignedVars b
  | .mk (.lam _ b) _ => tAssignedVars b
  | .mk (.app _ args) _ => goE args
  | .mk (.tuple es) _ => goE es
  | .mk (.proj e _) _ => tAssignedVars e
  | .mk (.ifThenElse c t e) _ => tAssignedVars c ++ tAssignedVars t ++ tAssignedVars e
  | .mk (.match_ s arms) _ => tAssignedVars s ++ goA arms
  | .mk (.seq a b) _ => tAssignedVars a ++ tAssignedVars b
  | .mk (.borrow e) _ => tAssignedVars e
  | .mk (.deref e) _ => tAssignedVars e
  | .mk (.forLoop _ lo hi b) _ => tAssignedVars lo ++ tAssignedVars hi ++ tAssignedVars b
  | .mk (.forLoopRev _ lo hi b) _ => tAssignedVars lo ++ tAssignedVars hi ++ tAssignedVars b
  | .mk (.whileLoop c b) _ => tAssignedVars c ++ tAssignedVars b
  | .mk (.earlyReturn e) _ => tAssignedVars e
  | .mk (.questionMark e) _ => tAssignedVars e
  | .mk (.forFold _ lo hi b) _ => tAssignedVars lo ++ tAssignedVars hi ++ tAssignedVars b
  | .mk (.forFoldRev _ lo hi b) _ => tAssignedVars lo ++ tAssignedVars hi ++ tAssignedVars b
  | .mk (.whileFold c b) _ => tAssignedVars c ++ tAssignedVars b
  | .mk (.forFoldReturn _ lo hi b) _ => tAssignedVars lo ++ tAssignedVars hi ++ tAssignedVars b
  | .mk (.forFoldRevReturn _ lo hi b) _ => tAssignedVars lo ++ tAssignedVars hi ++ tAssignedVars b
  | .mk (.whileFoldReturn c b) _ => tAssignedVars c ++ tAssignedVars b
  | .mk (.cfBreak e) _ => tAssignedVars e
  | .mk (.cfContinue e) _ => tAssignedVars e
  | .mk (.cfBreakContinue e) _ => tAssignedVars e
  | .mk (.ann e) _ => tAssignedVars e
  | .mk (.namedProj _ e) _ => tAssignedVars e
  | .mk (.break_ (some e)) _ => tAssignedVars e
  | .mk (.lit _) _ => []
  | .mk (.var _) _ => []
  | .mk .unitVal _ => []
  | .mk (.break_ none) _ => []
  | .mk .continue_ _ => []
where
  goE : List TExpr → List String
    | [] => []
    | e :: es => tAssignedVars e ++ goE es
  goA : List (ImpPat × TExpr) → List String
    | [] => []
    | (_, e) :: rest => tAssignedVars e ++ goA rest

/-- Names referenced (`.var`) anywhere in `e` (over-approximate: ignores binders). -/
def tVarRefs : TExpr → List String
  | .mk (.var n) _ => [n]
  | .mk (.letBind _ v b) _ => tVarRefs v ++ tVarRefs b
  | .mk (.lam _ b) _ => tVarRefs b
  | .mk (.app _ args) _ => goE args
  | .mk (.tuple es) _ => goE es
  | .mk (.proj e _) _ => tVarRefs e
  | .mk (.ifThenElse c t e) _ => tVarRefs c ++ tVarRefs t ++ tVarRefs e
  | .mk (.match_ s arms) _ => tVarRefs s ++ goA arms
  | .mk (.seq a b) _ => tVarRefs a ++ tVarRefs b
  | .mk (.borrow e) _ => tVarRefs e
  | .mk (.deref e) _ => tVarRefs e
  | .mk (.assign _ rhs) _ => tVarRefs rhs
  | .mk (.forLoop _ lo hi b) _ => tVarRefs lo ++ tVarRefs hi ++ tVarRefs b
  | .mk (.forLoopRev _ lo hi b) _ => tVarRefs lo ++ tVarRefs hi ++ tVarRefs b
  | .mk (.whileLoop c b) _ => tVarRefs c ++ tVarRefs b
  | .mk (.earlyReturn e) _ => tVarRefs e
  | .mk (.questionMark e) _ => tVarRefs e
  | .mk (.forFold _ lo hi b) _ => tVarRefs lo ++ tVarRefs hi ++ tVarRefs b
  | .mk (.forFoldRev _ lo hi b) _ => tVarRefs lo ++ tVarRefs hi ++ tVarRefs b
  | .mk (.whileFold c b) _ => tVarRefs c ++ tVarRefs b
  | .mk (.forFoldReturn _ lo hi b) _ => tVarRefs lo ++ tVarRefs hi ++ tVarRefs b
  | .mk (.forFoldRevReturn _ lo hi b) _ => tVarRefs lo ++ tVarRefs hi ++ tVarRefs b
  | .mk (.whileFoldReturn c b) _ => tVarRefs c ++ tVarRefs b
  | .mk (.cfBreak e) _ => tVarRefs e
  | .mk (.cfContinue e) _ => tVarRefs e
  | .mk (.cfBreakContinue e) _ => tVarRefs e
  | .mk (.ann e) _ => tVarRefs e
  | .mk (.namedProj _ e) _ => tVarRefs e
  | .mk (.break_ (some e)) _ => tVarRefs e
  | .mk (.lit _) _ => []
  | .mk .unitVal _ => []
  | .mk (.break_ none) _ => []
  | .mk .continue_ _ => []
where
  goE : List TExpr → List String
    | [] => []
    | e :: es => tVarRefs e ++ goE es
  goA : List (ImpPat × TExpr) → List String
    | [] => []
    | (_, e) :: rest => tVarRefs e ++ goA rest

/-- Whether `e` contains a loop / fold construct. Used to decide whether to thread
    mutations through an `if` that sits *inside* a fold body: when the continuation
    feeds a subsequent loop (so the loop needs the merged post-`if` state) the
    threading is required and safe, whereas an `if` whose mutated variables merely
    become the enclosing fold's accumulator return must be left to the accumulator
    mechanism. -/
def tContainsLoop : TExpr → Bool
  | .mk (.forLoop ..) _ => true
  | .mk (.forLoopRev ..) _ => true
  | .mk (.whileLoop ..) _ => true
  | .mk (.forFold ..) _ => true
  | .mk (.forFoldRev ..) _ => true
  | .mk (.whileFold ..) _ => true
  | .mk (.forFoldReturn ..) _ => true
  | .mk (.forFoldRevReturn ..) _ => true
  | .mk (.whileFoldReturn ..) _ => true
  | .mk (.letBind _ v b) _ => tContainsLoop v || tContainsLoop b
  | .mk (.lam _ b) _ => tContainsLoop b
  | .mk (.app _ args) _ => goE args
  | .mk (.tuple es) _ => goE es
  | .mk (.proj e _) _ => tContainsLoop e
  | .mk (.ifThenElse c t e) _ => tContainsLoop c || tContainsLoop t || tContainsLoop e
  | .mk (.match_ s arms) _ => tContainsLoop s || goA arms
  | .mk (.seq a b) _ => tContainsLoop a || tContainsLoop b
  | .mk (.borrow e) _ => tContainsLoop e
  | .mk (.deref e) _ => tContainsLoop e
  | .mk (.assign _ rhs) _ => tContainsLoop rhs
  | .mk (.earlyReturn e) _ => tContainsLoop e
  | .mk (.questionMark e) _ => tContainsLoop e
  | .mk (.cfBreak e) _ => tContainsLoop e
  | .mk (.cfContinue e) _ => tContainsLoop e
  | .mk (.cfBreakContinue e) _ => tContainsLoop e
  | .mk (.ann e) _ => tContainsLoop e
  | .mk (.namedProj _ e) _ => tContainsLoop e
  | .mk (.break_ (some e)) _ => tContainsLoop e
  | .mk (.lit _) _ => false
  | .mk (.var _) _ => false
  | .mk .unitVal _ => false
  | .mk (.break_ none) _ => false
  | .mk .continue_ _ => false
where
  goE : List TExpr → Bool
    | [] => false
    | e :: es => tContainsLoop e || goE es
  goA : List (ImpPat × TExpr) → Bool
    | [] => false
    | (_, e) :: rest => tContainsLoop e || goA rest

/-- Build `(v₁, …, vₙ)` (or just `vᵢ` when singleton) from variable names. -/
def tVarTuple : List String → TExpr
  | [v] => .mk (.var v) .unknown
  | vs => .mk (.tuple (vs.map (fun v => .mk (.var v) .unknown))) .unknown

/-- Rebind `vars` from the right-nested tuple `tup`, then continue with `cont`.
    A Lean n-tuple `(v₁,…,vₙ)` is `(v₁, (v₂, … vₙ))`, so the head is `tup.1`
    (`proj 0`, which the renderer's untyped `.proj` fallback already prints
    correctly at any arity) and the rest live in `tup.2` — recurse there. The
    tail is built with the `::proj::.2` marker (`Hax.PrettyPrint.projPath`'s
    convention, consumed by the `::proj::` arm of `toLean`) rather than a bare
    `.proj tup 1`, because a bare `.proj _ i` node is read by the untyped
    fallback as a FLAT index into an n-ary tuple and only `i = 0` is safe there;
    the marker instead says directly "the second component of this pair",
    which is what the right-nested encoding always means for index `1`. The
    last variable binds the remaining tail directly (a flat `tup.i` would be
    invalid: `(a,b,c).3` doesn't exist). -/
def tDestructure : List String → TExpr → TExpr → TExpr
  | [], _, cont => cont
  | [v], tup, cont => .mk (.letBind v tup cont) cont.ty
  | v :: vs, tup, cont =>
    .mk (.letBind v (.mk (.proj tup 0) .unknown)
      (tDestructure vs (.mk (.app "::proj::.2" [tup]) .unknown) cont)) cont.ty

/-- Replace the tail value of a `let`/`seq` chain with `newTail`, keeping the
    bindings.

    A branch of a statement-`if` ends in whatever its Rust block ended in, and
    that tail is a statement whenever the block's last item was one: an
    assignment, a nested `if`, a `match`, a loop, a `return`, a jump. Each such
    tail keeps its effect —

    * an `if` distributes `newTail` into both of its branches, so the branch
      that mutates reaches the join with its mutation;
    * a `match` distributes `newTail` into every arm body, for the same reason;
    * an assignment, loop, `return`, `break` or `continue` is kept as a
      statement in front of `newTail`.

    A tail that is a pure value is dropped, since `newTail` supplies the value
    the enclosing rewrite wants. -/
def tReplaceTail : TExpr → TExpr → TExpr
  | .mk (.letBind n v body) ty, newTail => .mk (.letBind n v (tReplaceTail body newTail)) ty
  | .mk (.seq a b) ty, newTail => .mk (.seq a (tReplaceTail b newTail)) ty
  | .mk (.assign n r) ty, newTail => .mk (.seq (.mk (.assign n r) ty) newTail) ty
  | .mk (.ifThenElse c t f) _, newTail =>
      .mk (.ifThenElse c (tReplaceTail t newTail) (tReplaceTail f newTail)) newTail.ty
  | .mk (.match_ s arms) _, newTail =>
      .mk (.match_ s (goA arms newTail)) newTail.ty
  | .mk (.forLoop v lo hi b) ty, newTail =>
      .mk (.seq (.mk (.forLoop v lo hi b) ty) newTail) ty
  | .mk (.forLoopRev v lo hi b) ty, newTail =>
      .mk (.seq (.mk (.forLoopRev v lo hi b) ty) newTail) ty
  | .mk (.whileLoop c b) ty, newTail =>
      .mk (.seq (.mk (.whileLoop c b) ty) newTail) ty
  | .mk (.forFold v lo hi b) ty, newTail =>
      .mk (.seq (.mk (.forFold v lo hi b) ty) newTail) ty
  | .mk (.forFoldRev v lo hi b) ty, newTail =>
      .mk (.seq (.mk (.forFoldRev v lo hi b) ty) newTail) ty
  | .mk (.whileFold c b) ty, newTail =>
      .mk (.seq (.mk (.whileFold c b) ty) newTail) ty
  | .mk (.forFoldReturn v lo hi b) ty, newTail =>
      .mk (.seq (.mk (.forFoldReturn v lo hi b) ty) newTail) ty
  | .mk (.forFoldRevReturn v lo hi b) ty, newTail =>
      .mk (.seq (.mk (.forFoldRevReturn v lo hi b) ty) newTail) ty
  | .mk (.whileFoldReturn c b) ty, newTail =>
      .mk (.seq (.mk (.whileFoldReturn c b) ty) newTail) ty
  | .mk (.earlyReturn e) ty, newTail =>
      .mk (.seq (.mk (.earlyReturn e) ty) newTail) ty
  | .mk (.break_ b) ty, newTail =>
      .mk (.seq (.mk (.break_ b) ty) newTail) ty
  | .mk .continue_ ty, newTail =>
      .mk (.seq (.mk .continue_ ty) newTail) ty
  -- Look through the erase-deleted `.ann` marker so the rewrite commutes with
  -- erasure (no `.ann` exists at this pre-pipeline stage).
  | .mk (.ann e) ty, newTail => .mk (.ann (tReplaceTail e newTail)) ty
  | _, newTail => newTail
where
  goA : List (ImpPat × TExpr) → TExpr → List (ImpPat × TExpr)
    | [], _ => []
    | (p, e) :: rest, newTail => (p, tReplaceTail e newTail) :: goA rest newTail

/-! ## `&mut` write-back

A Rust `fn f(v: &mut T, …)` writes through the reference. The extraction has no
references, so `f` returns `v`'s final value and every caller rebinds its own
variable from that result:

    f(&mut x, y)  ↦  x = f(x, y)

Both halves read one table, `mutWriteFns`, whose entry is
`(function, positions, parameters, hasResult)`: the `&mut` parameter positions
a function writes back through, their names, and whether its Rust result
carries a value. A signature admits a candidate (`mutWriteCandidates`) and the
body decides it per parameter (`mutWriteStep`) — a field write counts, since
the parse arms lower it to a `struct_update` assignment of the parameter
itself, while a parameter written only through an element of itself assigns
nothing and is not written back.

An entry with one parameter and result `()` is the *single* form: the callee's
tail becomes that parameter (`tReturnMutParams` through `tReplaceTail`) and a
call becomes an assignment (`tRebindMutCalls` through `tRebindCall`). A call
whose `&mut` argument is a single-level field place `&mut x.f` becomes a
functional field update of `x` from the call's result, and a slice-range place
`&mut x[lo..hi]` a functional range update of `x`.

Every other entry is the *tuple* form: the callee's tail becomes
`(v₁, …, v_k)`, or `(t, v₁, …, v_k)` when the result carries a value `t`, and a
call site binds that tuple to `_wb` and assigns each component
(`tTupleBind`). The two tables `mutWriteTable` (single) and
`mutWriteTupleTable` (tuple) partition the resolved table, so a function is
read in one form only and the call sites and the definition agree on the
callee's result by construction.

Either form produces ordinary `.assign` nodes, which `tThreadMut`,
`localMutation` and the renderer's accumulator extraction already carry.

`tRebindMutCalls` runs before `tReturnMutParams`: a body whose own tail is a
write-back call has to become an assignment first, or `tReplaceTail` drops it
as a pure value. -/

/-- The write-back shape a signature admits: the positions and names of its
    `&mut` parameters, and whether its Rust result carries a value. `none` for
    a function with no `&mut` parameter. -/
def mutWriteSig (retTy : ImpType) (params : List (String × ImpType)) :
    Option (List Nat × List String × Bool) :=
  let ps := params.zipIdx.filterMap (fun pi =>
    match pi.1.2 with
    | .ref _ true => some (pi.2, pi.1.1)
    | _ => none)
  if ps.isEmpty then none
  else some (ps.map (·.1), ps.map (·.2),
    match retTy with | .unit => false | _ => true)

/-- Each function whose signature admits write-back parameters, as
    `(function, positions, parameters, hasResult)`. -/
def mutWriteCandidates (fns : List (String × FnTypeInfo)) :
    List (String × List Nat × List String × Bool) :=
  fns.filterMap fun ni =>
    (mutWriteSig ni.2.retType ni.2.paramTypes).map (fun s => (ni.1, s.1, s.2.1, s.2.2))

/-- The single-form entries of a resolved table — one write-back parameter and
    result `()` — as `(function, position)`, read at call sites by
    `tRebindCall`. -/
def mutWriteTable (ws : List (String × List Nat × List String × Bool)) :
    List (String × Nat) :=
  ws.filterMap fun c =>
    match c.2.1, c.2.2.2 with
    | [i], false => some (c.1, i)
    | _, _ => none

/-- The tuple-form entries of a resolved table — several write-back parameters,
    or a result that carries a value — as `(function, positions, hasResult)`,
    read at call sites by `tTupleSite`. -/
def mutWriteTupleTable (ws : List (String × List Nat × List String × Bool)) :
    List (String × List Nat × Bool) :=
  ws.filterMap fun c =>
    match c.2.1, c.2.2.2 with
    | [_], false => none
    | ps, hasRes => some (c.1, ps, hasRes)

/-- Write-back parameter names and result flag of a resolved table, read at the
    definition by `tReturnMutParams`. -/
def mutWriteReturns (ws : List (String × List Nat × List String × Bool)) :
    List (String × List String × Bool) :=
  ws.map (fun c => (c.1, c.2.2.1, c.2.2.2))

/-- Standard-library methods that write through their receiver, with the
    receiver's argument position.

    `mutWriteFns` derives its table from the export's own signatures and bodies,
    so it sees only functions the crate defines. These four are `core`/`alloc`
    methods: the export carries neither a signature nor a body for them, so
    `mutWriteCandidates` and `mutWriteStep` both filter them out and their call
    sites are emitted in statement position with the result dropped. The runtime
    models all four value-returningly, so rebinding the receiver is the emission
    that model already expects.

    The table covers a receiver that is a plain place — a variable, borrow,
    deref or ascription, the forms `tMutArgRoot` resolves — and a slice-range
    place `dst[lo..hi]`, which `tMutArgSlice` resolves to its root and bounds
    and `tRebindCall` rebinds through `slice_update`. -/
def builtinWriteTable : List (String × Nat) :=
  [("copy_from_slice", 0), ("extend_from_slice", 0), ("push", 0), ("truncate", 0)]

/-- The variable an argument in write-back position writes to: the root of the
    place passed there. `none` for an index or a field, whose callee result is
    that component rather than the whole variable. -/
def tMutArgRoot : TExpr → Option String
  | .mk (.var n) _ => some n
  | .mk (.borrow e) _ => tMutArgRoot e
  | .mk (.deref e) _ => tMutArgRoot e
  | .mk (.ann e) _ => tMutArgRoot e
  | _ => none

/-- The variable a call to `f` writes back to under the write-back table. The
    newtype-projection head `.0` is excluded: it is a field read the renderer
    introduces, not a Rust function, and it is the head an erased `.namedProj`
    carries. -/
def tCallWriteback (writers : List (String × Nat)) (f : String) (args : List TExpr) :
    Option String :=
  if f == ".0" then none
  else
    match writers.lookup f with
    | some i => (args[i]?).bind tMutArgRoot
    | none => none

/-- The single-level struct-field place a write-back argument passes: the root
    variable and the field name, for an argument of the form `&mut root.f`.
    `none` for a plain variable, an element place, a deeper path, or the
    newtype projection `.0`. -/
def tMutArgField : TExpr → Option (String × String)
  | .mk (.borrow e) _ => tMutArgField e
  | .mk (.deref e) _ => tMutArgField e
  | .mk (.ann e) _ => tMutArgField e
  | .mk (.app pf [sE]) _ =>
    if pf.startsWith "." && pf != ".0" then
      (tMutArgRoot sE).map fun r => (r, (pf.drop 1).toString)
    else none
  | _ => none

/-- The struct-field write-back of a call to `f` under the write-back table:
    the root variable and the field's resolved struct, position and count, when
    the write-back argument is a field place `&mut root.f` whose field name
    resolves through `sf`. The callee's result is the field's new value, so
    such a call becomes `assign root (struct_update#S#i#n root <call>)`. -/
def tCallWritebackField (sf : StructFieldNames) (writers : List (String × Nat))
    (f : String) (args : List TExpr) : Option (String × String × Nat × Nat) :=
  if f == ".0" then none
  else
    match writers.lookup f with
    | some i =>
      (args[i]?).bind fun a =>
        (tMutArgField a).bind fun rf =>
          (resolveStructField sf rf.2).map fun sin => (rf.1, sin)
    | none => none

/-- The lower and upper bound of a range expression over the variable `root`:
    `RangeTo hi` starts at `0`, `Range lo hi` carries both bounds, and
    `RangeFrom lo` ends at `len root`. `none` for `RangeFull` and any other
    expression. -/
def tRangeBounds (root : String) : TExpr → Option (TExpr × TExpr)
  | .mk (.ann e) _ => tRangeBounds root e
  | .mk (.app "RangeTo" [hi]) _ => some (.mk (.lit (.int 0)) .int, hi)
  | .mk (.app "Range" [lo, hi]) _ => some (lo, hi)
  | .mk (.app "RangeFrom" [lo]) _ =>
    some (lo, .mk (.app "len" [.mk (.var root) .unknown]) .int)
  | _ => none

/-- The slice-range place a write-back argument passes: the root variable and
    the range's lower and upper bounds, for an argument of the form
    `&mut root[lo..hi]`, which the export spells `index_mut root r`. `none` for
    a plain variable, a field place, a scalar element, a range whose bounds
    `tRangeBounds` does not carry, or a root that is not itself a variable. -/
def tMutArgSlice : TExpr → Option (String × TExpr × TExpr)
  | .mk (.borrow e) _ => tMutArgSlice e
  | .mk (.deref e) _ => tMutArgSlice e
  | .mk (.ann e) _ => tMutArgSlice e
  | .mk (.app f [aE, rE]) _ =>
    if f == "index_mut" then
      (tMutArgRoot aE).bind fun r =>
        (tRangeBounds r rE).map fun b => (r, b.1, b.2)
    else none
  | _ => none

/-- The slice-range write-back of a call to `f` under the write-back table:
    the root variable and the range bounds, when the write-back argument is a
    slice-range place `&mut root[lo..hi]`. The callee's result is the range's
    new contents, so such a call becomes
    `assign root (slice_update root lo hi <call>)`. -/
def tCallWritebackSlice (writers : List (String × Nat)) (f : String) (args : List TExpr) :
    Option (String × TExpr × TExpr) :=
  if f == ".0" then none
  else
    match writers.lookup f with
    | some i => (args[i]?).bind tMutArgSlice
    | none => none

/-! ### The tuple form

A tuple-form callee returns `(v₁, …, v_k)`, or `(t, v₁, …, v_k)` when its Rust
result carries a value `t`. A call site binds that tuple to `_wb` and assigns
each written variable from its component; the value component stays where the
call's own result was. Every component is projected from the *variable* `_wb`,
never from the call, because a projection of a call does not lower. -/

/-- The binder a tuple-form call site holds its callee's result in. -/
def tWbTmp : String := "_wb"

/-- The `i`-th component of the right-nested `n`-tuple `tup`. A Lean `n`-tuple
    `(c₀, …, c_{n-1})` is `(c₀, (c₁, … c_{n-1}))`, so the head is `.proj _ 0`
    and the rest live in the `::proj::.2`-marked tail (`PrettyPrint.projPath`'s
    convention), which is where the recursion descends; the last component is
    that tail itself. -/
def tTupleComp (tup : TExpr) : Nat → Nat → TExpr
  | _, 0 => tup
  | _, 1 => tup
  | 0, _ => .mk (.proj tup 0) .unknown
  | i + 1, n + 1 => tTupleComp (.mk (.app "::proj::.2" [tup]) .unknown) i n

/-- The variables the arguments at `positions` write to, when every one of them
    is a plain place (`tMutArgRoot`). `none` as soon as one is not. -/
def tMutArgRoots (args : List TExpr) : List Nat → Option (List String)
  | [] => some []
  | i :: is =>
    ((args[i]?).bind tMutArgRoot).bind fun r =>
      (tMutArgRoots args is).map (fun rs => r :: rs)

/-- The tuple-form write-back of a call to `f` under the tuple table: the
    variables to rebind and whether the callee's result carries a value. The
    newtype-projection head `.0` is excluded, as in `tCallWriteback`. -/
def tTupleWriteback (tup : List (String × List Nat × Bool)) (f : String)
    (args : List TExpr) : Option (List String × Bool) :=
  if f == ".0" then none
  else
    match tup.lookup f with
    | some (ps, hasRes) => (tMutArgRoots args ps).map (fun rs => (rs, hasRes))
    | none => none

/-- The tuple-form write-back a node performs: `tTupleWriteback` of a call
    node, `none` for any other node. The erase-deleted `.ann` marker is looked
    through, so the rewrite commutes with erasure. -/
def tTupleSite (tup : List (String × List Nat × Bool)) : TExpr → Option (List String × Bool)
  | .mk (.app f args) _ => tTupleWriteback tup f args
  | .mk (.ann e) _ => tTupleSite tup e
  | _ => none

/-- The assignments `vᵢ := _wb.<offset+i>` of a tuple-form call site, in order,
    in front of `cont`. `n` is the callee's tuple arity. -/
def tTupleAssigns : List String → Nat → Nat → TExpr → TExpr
  | [], _, _, cont => cont
  | v :: vs, offset, n, cont =>
    .mk (.seq (.mk (.assign v (tTupleComp (.mk (.var tWbTmp) .unknown) offset n)) .unit)
      (tTupleAssigns vs (offset + 1) n cont)) cont.ty

/-- A tuple-form call site: the call bound to `_wb`, the write-back assignments
    of `roots` from its components, then `tail`. -/
def tTupleBind (call : TExpr) (roots : List String) (hasRes : Bool) (tail : TExpr) : TExpr :=
  .mk (.letBind tWbTmp call
    (tTupleAssigns roots (if hasRes then 1 else 0)
      (roots.length + (if hasRes then 1 else 0)) tail)) tail.ty

/-- The component of a tuple-form callee's result that carries the call's own
    value: the head of the tuple when the callee has a Rust result, the unit
    value when it has none. -/
def tTupleResult (roots : List String) (hasRes : Bool) : TExpr :=
  if hasRes then tTupleComp (.mk (.var tWbTmp) .unknown) 0 (roots.length + 1)
  else .mk .unitVal .unit

/-- The node a call becomes under the write-back table: an assignment binding
    the write-back variable — or, for a field-place argument, a functional
    field update of its root variable, and for a slice-range argument, a
    functional range update of its root variable — to the call's result, or
    the call itself. -/
def tRebindCall (sf : StructFieldNames) (writers : List (String × Nat)) (f : String)
    (args : List TExpr) (ty : ImpType) : TExpr :=
  match tCallWriteback writers f args with
  | some v => .mk (.assign v (.mk (.app f args) ty)) ty
  | none =>
    match tCallWritebackField sf writers f args with
    | some (root, sname, i, n) =>
      .mk (.assign root (.mk (.app (structUpdateHead sname i n)
        [.mk (.var root) .unknown, .mk (.app f args) ty]) .unknown)) ty
    | none =>
      match tCallWritebackSlice writers f args with
      | some (root, lo, hi) =>
        .mk (.assign root (.mk (.app "slice_update"
          [.mk (.var root) .unknown, lo, hi, .mk (.app f args) ty]) .unknown)) ty
      | none => .mk (.app f args) ty

/-- Bind the write-back variables of every call to a write-back function from
    that call's result: a single-form call becomes an assignment in place, and
    a tuple-form call in `let`, assignment or statement position becomes the
    `_wb` binding, the component assignments and the call's own result. A call
    to any other function, a call whose write-back argument is an index or a
    field rather than a variable, and a tuple-form call in any other position
    keep their own value. -/
def tRebindMutCalls (sf : StructFieldNames) (writers : List (String × Nat))
    (tup : List (String × List Nat × Bool)) : TExpr → TExpr
  | .mk (.app f args) ty => tRebindCall sf writers f (mapE sf writers tup args) ty
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk (.letBind n val body) ty =>
      let val' := tRebindMutCalls sf writers tup val
      let body' := tRebindMutCalls sf writers tup body
      match tTupleSite tup val' with
      | some (roots, hasRes) =>
          tTupleBind val' roots hasRes
            (.mk (.letBind n (tTupleResult roots hasRes) body') ty)
      | none => .mk (.letBind n val' body') ty
  | .mk (.lam ps body) ty => .mk (.lam ps (tRebindMutCalls sf writers tup body)) ty
  | .mk (.tuple elems) ty => .mk (.tuple (mapE sf writers tup elems)) ty
  | .mk (.proj e i) ty => .mk (.proj (tRebindMutCalls sf writers tup e) i) ty
  | .mk (.ifThenElse c t e) ty =>
      .mk (.ifThenElse (tRebindMutCalls sf writers tup c) (tRebindMutCalls sf writers tup t)
        (tRebindMutCalls sf writers tup e)) ty
  | .mk (.match_ scrut arms) ty =>
      .mk (.match_ (tRebindMutCalls sf writers tup scrut) (mapA sf writers tup arms)) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk (.seq a b) ty =>
      let a' := tRebindMutCalls sf writers tup a
      let b' := tRebindMutCalls sf writers tup b
      match tTupleSite tup a' with
      | some (roots, hasRes) => tTupleBind a' roots hasRes b'
      | none => .mk (.seq a' b') ty
  | .mk (.borrow e) ty => .mk (.borrow (tRebindMutCalls sf writers tup e)) ty
  | .mk (.deref e) ty => .mk (.deref (tRebindMutCalls sf writers tup e)) ty
  | .mk (.assign n rhs) ty =>
      let rhs' := tRebindMutCalls sf writers tup rhs
      match tTupleSite tup rhs' with
      | some (roots, hasRes) =>
          tTupleBind rhs' roots hasRes (.mk (.assign n (tTupleResult roots hasRes)) ty)
      | none => .mk (.assign n rhs') ty
  | .mk (.forLoop v lo hi b) ty =>
      .mk (.forLoop v (tRebindMutCalls sf writers tup lo) (tRebindMutCalls sf writers tup hi)
        (tRebindMutCalls sf writers tup b)) ty
  | .mk (.forLoopRev v lo hi b) ty =>
      .mk (.forLoopRev v (tRebindMutCalls sf writers tup lo) (tRebindMutCalls sf writers tup hi)
        (tRebindMutCalls sf writers tup b)) ty
  | .mk (.whileLoop c b) ty =>
      .mk (.whileLoop (tRebindMutCalls sf writers tup c) (tRebindMutCalls sf writers tup b)) ty
  | .mk (.break_ none) ty => .mk (.break_ none) ty
  | .mk (.break_ (some e)) ty => .mk (.break_ (some (tRebindMutCalls sf writers tup e))) ty
  | .mk .continue_ ty => .mk .continue_ ty
  | .mk (.earlyReturn e) ty => .mk (.earlyReturn (tRebindMutCalls sf writers tup e)) ty
  | .mk (.questionMark e) ty => .mk (.questionMark (tRebindMutCalls sf writers tup e)) ty
  | .mk (.forFold v lo hi b) ty =>
      .mk (.forFold v (tRebindMutCalls sf writers tup lo) (tRebindMutCalls sf writers tup hi)
        (tRebindMutCalls sf writers tup b)) ty
  | .mk (.forFoldRev v lo hi b) ty =>
      .mk (.forFoldRev v (tRebindMutCalls sf writers tup lo) (tRebindMutCalls sf writers tup hi)
        (tRebindMutCalls sf writers tup b)) ty
  | .mk (.whileFold c b) ty =>
      .mk (.whileFold (tRebindMutCalls sf writers tup c) (tRebindMutCalls sf writers tup b)) ty
  | .mk (.forFoldReturn v lo hi b) ty =>
      .mk (.forFoldReturn v (tRebindMutCalls sf writers tup lo) (tRebindMutCalls sf writers tup hi)
        (tRebindMutCalls sf writers tup b)) ty
  | .mk (.forFoldRevReturn v lo hi b) ty =>
      .mk (.forFoldRevReturn v (tRebindMutCalls sf writers tup lo)
        (tRebindMutCalls sf writers tup hi) (tRebindMutCalls sf writers tup b)) ty
  | .mk (.whileFoldReturn c b) ty =>
      .mk (.whileFoldReturn (tRebindMutCalls sf writers tup c)
        (tRebindMutCalls sf writers tup b)) ty
  | .mk (.cfBreak e) ty => .mk (.cfBreak (tRebindMutCalls sf writers tup e)) ty
  | .mk (.cfContinue e) ty => .mk (.cfContinue (tRebindMutCalls sf writers tup e)) ty
  | .mk (.cfBreakContinue e) ty => .mk (.cfBreakContinue (tRebindMutCalls sf writers tup e)) ty
  | .mk (.ann e) ty => .mk (.ann (tRebindMutCalls sf writers tup e)) ty
  | .mk (.namedProj n e) ty => .mk (.namedProj n (tRebindMutCalls sf writers tup e)) ty
where
  mapE (sf : StructFieldNames) (writers : List (String × Nat))
      (tup : List (String × List Nat × Bool)) : List TExpr → List TExpr
    | [] => []
    | e :: es => tRebindMutCalls sf writers tup e :: mapE sf writers tup es
  mapA (sf : StructFieldNames) (writers : List (String × Nat))
      (tup : List (String × List Nat × Bool)) :
      List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest => (p, tRebindMutCalls sf writers tup e) :: mapA sf writers tup rest

/-- Wrap the tail value `t` of a body in the tuple `(t, v₁, …, v_k)`, keeping
    every statement of the body ahead of it and distributing into the branches
    of an `if` and the arms of a `match`, as `tReplaceTail` does. `none` for a
    tail that is a statement rather than a value — an assignment, a loop, a
    `return` or a jump — since such a tail carries no value to pair the
    written parameters with. -/
def tTupleTail (vars : List String) : TExpr → Option TExpr
  | .mk (.letBind n v body) ty => (tTupleTail vars body).map fun b => .mk (.letBind n v b) ty
  | .mk (.seq a b) ty => (tTupleTail vars b).map fun b' => .mk (.seq a b') ty
  | .mk (.ifThenElse c t f) ty =>
      (tTupleTail vars t).bind fun t' =>
        (tTupleTail vars f).map fun f' => .mk (.ifThenElse c t' f') ty
  | .mk (.match_ s arms) ty => (goA vars arms).map fun arms' => .mk (.match_ s arms') ty
  | .mk (.ann e) ty => (tTupleTail vars e).map fun e' => .mk (.ann e') ty
  | .mk (.assign _ _) _ => none
  | .mk (.forLoop ..) _ => none
  | .mk (.forLoopRev ..) _ => none
  | .mk (.whileLoop ..) _ => none
  | .mk (.forFold ..) _ => none
  | .mk (.forFoldRev ..) _ => none
  | .mk (.whileFold ..) _ => none
  | .mk (.forFoldReturn ..) _ => none
  | .mk (.forFoldRevReturn ..) _ => none
  | .mk (.whileFoldReturn ..) _ => none
  | .mk (.earlyReturn _) _ => none
  | .mk (.questionMark _) _ => none
  | .mk (.break_ _) _ => none
  | .mk .continue_ _ => none
  | .mk (.cfBreak _) _ => none
  | .mk (.cfContinue _) _ => none
  | .mk (.cfBreakContinue _) _ => none
  | e => some (.mk (.tuple (e :: vars.map (fun v => .mk (.var v) .unknown))) .unknown)
where
  goA (vars : List String) :
      List (ImpPat × TExpr) → Option (List (ImpPat × TExpr))
    | [] => some []
    | (p, e) :: rest =>
      (tTupleTail vars e).bind fun e' => (goA vars rest).map fun rest' => (p, e') :: rest'

/-- Whether `e` contains a `return` or a `?`. A body that does carries its
    value out of tail position, which `tTupleTail` does not reach. -/
def tContainsEarlyReturn : TExpr → Bool
  | .mk (.earlyReturn _) _ => true
  | .mk (.questionMark _) _ => true
  | .mk (.letBind _ v b) _ => tContainsEarlyReturn v || tContainsEarlyReturn b
  | .mk (.lam _ b) _ => tContainsEarlyReturn b
  | .mk (.app _ args) _ => goE args
  | .mk (.tuple es) _ => goE es
  | .mk (.proj e _) _ => tContainsEarlyReturn e
  | .mk (.ifThenElse c t e) _ =>
      tContainsEarlyReturn c || tContainsEarlyReturn t || tContainsEarlyReturn e
  | .mk (.match_ s arms) _ => tContainsEarlyReturn s || goA arms
  | .mk (.seq a b) _ => tContainsEarlyReturn a || tContainsEarlyReturn b
  | .mk (.borrow e) _ => tContainsEarlyReturn e
  | .mk (.deref e) _ => tContainsEarlyReturn e
  | .mk (.assign _ rhs) _ => tContainsEarlyReturn rhs
  | .mk (.forLoop _ lo hi b) _ =>
      tContainsEarlyReturn lo || tContainsEarlyReturn hi || tContainsEarlyReturn b
  | .mk (.forLoopRev _ lo hi b) _ =>
      tContainsEarlyReturn lo || tContainsEarlyReturn hi || tContainsEarlyReturn b
  | .mk (.whileLoop c b) _ => tContainsEarlyReturn c || tContainsEarlyReturn b
  | .mk (.forFold _ lo hi b) _ =>
      tContainsEarlyReturn lo || tContainsEarlyReturn hi || tContainsEarlyReturn b
  | .mk (.forFoldRev _ lo hi b) _ =>
      tContainsEarlyReturn lo || tContainsEarlyReturn hi || tContainsEarlyReturn b
  | .mk (.whileFold c b) _ => tContainsEarlyReturn c || tContainsEarlyReturn b
  | .mk (.forFoldReturn _ lo hi b) _ =>
      tContainsEarlyReturn lo || tContainsEarlyReturn hi || tContainsEarlyReturn b
  | .mk (.forFoldRevReturn _ lo hi b) _ =>
      tContainsEarlyReturn lo || tContainsEarlyReturn hi || tContainsEarlyReturn b
  | .mk (.whileFoldReturn c b) _ => tContainsEarlyReturn c || tContainsEarlyReturn b
  | .mk (.cfBreak e) _ => tContainsEarlyReturn e
  | .mk (.cfContinue e) _ => tContainsEarlyReturn e
  | .mk (.cfBreakContinue e) _ => tContainsEarlyReturn e
  | .mk (.ann e) _ => tContainsEarlyReturn e
  | .mk (.namedProj _ e) _ => tContainsEarlyReturn e
  | .mk (.break_ (some e)) _ => tContainsEarlyReturn e
  | _ => false
where
  goE : List TExpr → Bool
    | [] => false
    | e :: es => tContainsEarlyReturn e || goE es
  goA : List (ImpPat × TExpr) → Bool
    | [] => false
    | (_, e) :: rest => tContainsEarlyReturn e || goA rest

/-- End a write-back function's body with its write-back parameters, keeping
    every statement of the body ahead of them: the single parameter, the tuple
    of several, or the tuple of the body's own value and the parameters when
    the Rust result carries a value. A function with no write-back parameter,
    and a value-returning one whose tail `tTupleTail` does not reach, is
    unchanged. -/
def tReturnMutParams (names : List String) (hasRes : Bool) (body : TExpr) : TExpr :=
  match names with
  | [] => body
  | _ =>
    if hasRes then (tTupleTail names body).getD body
    else tReplaceTail body (tVarTuple names)

/-- Keep the write-back parameters a candidate's body assigns once the calls
    inside it are rebound under `prev`/`prevTup`, and drop a candidate that
    assigns none. A struct-field write is an assignment of its root variable
    (the parse arms lower `self.f = v` to a `struct_update` assignment of
    `self` under `sf`), so a parameter written through its own fields
    qualifies. A parameter written only through an element of itself is
    assigned nothing.

    A candidate whose Rust result carries a value is kept only when the tuple
    its body must end in is reachable: no `return` or `?` anywhere, and a tail
    `tTupleTail` accepts. The calls to a dropped candidate are then reported by
    `tDroppedMutCalls` rather than rewritten. -/
def mutWriteStep (sf : StructFieldNames) (defs : List (String × TExpr))
    (prev : List (String × Nat)) (prevTup : List (String × List Nat × Bool))
    (cands : List (String × List Nat × List String × Bool)) :
    List (String × List Nat × List String × Bool) :=
  cands.filterMap fun c =>
    match defs.lookup c.1 with
    | none => none
    | some body =>
      let rebound := tRebindMutCalls sf prev prevTup body
      let assigned := tAssignedVars rebound
      let kept := (c.2.1.zip c.2.2.1).filter fun pv => assigned.contains pv.2
      let names := kept.map (·.2)
      if kept.isEmpty then none
      else if c.2.2.2 && (tContainsEarlyReturn body || (tTupleTail names rebound).isNone) then none
      else some (c.1, kept.map (·.1), names, c.2.2.2)

/-- Iterate `mutWriteStep` from `cur` until it is stationary or `fuel` runs
    out. -/
def mutWriteIter (sf : StructFieldNames) (defs : List (String × TExpr))
    (cands : List (String × List Nat × List String × Bool)) :
    Nat → List (String × List Nat × List String × Bool) →
    List (String × List Nat × List String × Bool)
  | 0, cur => cur
  | fuel + 1, cur =>
    let next := mutWriteStep sf defs (mutWriteTable cur) (mutWriteTupleTable cur) cands
    if next == cur then cur else mutWriteIter sf defs cands fuel next

/-- The write-back functions of an export: `mutWriteStep` iterated from the
    empty table to a fixpoint. A parameter written only by a nested write-back
    call is reached one round after the callee that writes it, so a chain of
    calls needs as many rounds as it is long; each round that is not the
    fixpoint admits at least one further parameter, so the total number of
    candidate parameters bounds the iteration. The same table drives the call
    sites and the definitions, so the two sides cannot disagree about what a
    callee returns. -/
def mutWriteFns (sf : StructFieldNames) (fns : List (String × FnTypeInfo))
    (defs : List (String × TExpr)) : List (String × List Nat × List String × Bool) :=
  let cands := mutWriteCandidates fns
  let fuel := cands.foldl (fun n c => n + c.2.1.length) 0
  mutWriteIter sf defs cands fuel (mutWriteStep sf defs [] [] cands)

/-! ### Calls through `&mut` outside the write-back fragment

`tRebindCall` rewrites a call into an assignment only when the callee is a
write-back function and the argument in write-back position is a variable, a
single-level field place or a slice-range place. Every other call whose callee
takes a `&mut` parameter keeps its value, and in statement position the
renderer drops that value: the effect the Rust performs through the reference
never reaches the caller. `tDroppedMutCalls` lists those calls, so the driver
can refuse to emit a surface that misdescribes the source. -/

/-- The positions of the `&mut` parameters of `f`: from its signature when the
    export carries one, else from `builtinWriteTable`. -/
def tMutParamPositions (sigs : List (String × FnTypeInfo)) (f : String) : List Nat :=
  match sigs.lookup f with
  | some info =>
    info.paramTypes.zipIdx.filterMap fun pi =>
      match pi.1.2 with
      | .ref _ true => some pi.2
      | _ => none
  | none =>
    match builtinWriteTable.lookup f with
    | some i => [i]
    | none => []

/-- The positions of the arguments of a call that are typed as mutable
    references. A trait method or a stdlib receiver has no signature in the
    export; its `&mut` arguments are visible only here. -/
def tMutArgPositions (args : List TExpr) : List Nat :=
  args.zipIdx.filterMap fun ai =>
    match ai.1 with
    | .mk _ (.ref _ true) => some ai.2
    | _ => none

/-- Heads that denote a place or a functional update rather than a call with an
    effect: the struct/array/slice update forms the parse arms produce for a
    write, the `index_mut` place of a slice-range argument (handled at the
    enclosing call by `tMutArgSlice`), and the projection heads `.f`. -/
def tPlaceHead (f : String) : Bool :=
  f.startsWith "." || f.startsWith "struct_update#" || f == "array_update"
    || f == "slice_update" || f == "index_mut" || f == "index"

/-- Whether `tRebindCall` turns the call `f args` into an assignment. -/
def tCallRebound (sf : StructFieldNames) (writers : List (String × Nat)) (f : String)
    (args : List TExpr) (ty : ImpType) : Bool :=
  match tRebindCall sf writers f args ty with
  | .mk (.assign _ _) _ => true
  | _ => false

/-- The calls in `e` that pass a `&mut` argument — by the callee's signature
    or by the argument's type — and that `tRebindMutCalls` leaves as plain
    calls, as `(callee, &mut positions)`. A place or update head
    (`tPlaceHead`) is not a call.

    `site` says whether the node sits in one of the three positions the
    tuple-form rewrite acts on: the value of a `let`, the right-hand side of an
    assignment, or the head of a `seq`. It is set by exactly those three arms,
    carried through the erase-deleted `.ann` marker as `tTupleSite` carries it,
    and cleared by every other arm, so a tuple-form call is reported exactly
    where `tRebindMutCalls` leaves it alone. -/
def tDroppedMutCallsAt (sigs : List (String × FnTypeInfo)) (sf : StructFieldNames)
    (writers : List (String × Nat)) (tup : List (String × List Nat × Bool))
    (site : Bool) : TExpr → List (String × List Nat)
  | .mk (.app f args) ty =>
      let here :=
        if tPlaceHead f then []
        else
          let ps := (tMutParamPositions sigs f ++ tMutArgPositions args).eraseDups
          if ps.isEmpty || tCallRebound sf writers f args ty
              || (site && (tTupleWriteback tup f args).isSome) then [] else [(f, ps)]
      here ++ goE args
  | .mk (.letBind _ v b) _ =>
      tDroppedMutCallsAt sigs sf writers tup true v
        ++ tDroppedMutCallsAt sigs sf writers tup false b
  | .mk (.lam _ b) _ => tDroppedMutCallsAt sigs sf writers tup false b
  | .mk (.tuple es) _ => goE es
  | .mk (.proj e _) _ => tDroppedMutCallsAt sigs sf writers tup false e
  | .mk (.ifThenElse c t e) _ =>
      tDroppedMutCallsAt sigs sf writers tup false c
        ++ tDroppedMutCallsAt sigs sf writers tup false t
        ++ tDroppedMutCallsAt sigs sf writers tup false e
  | .mk (.match_ s arms) _ => tDroppedMutCallsAt sigs sf writers tup false s ++ goA arms
  | .mk (.seq a b) _ =>
      tDroppedMutCallsAt sigs sf writers tup true a
        ++ tDroppedMutCallsAt sigs sf writers tup false b
  | .mk (.borrow e) _ => tDroppedMutCallsAt sigs sf writers tup false e
  | .mk (.deref e) _ => tDroppedMutCallsAt sigs sf writers tup false e
  | .mk (.assign _ rhs) _ => tDroppedMutCallsAt sigs sf writers tup true rhs
  | .mk (.forLoop _ lo hi b) _ =>
      tDroppedMutCallsAt sigs sf writers tup false lo
        ++ tDroppedMutCallsAt sigs sf writers tup false hi
        ++ tDroppedMutCallsAt sigs sf writers tup false b
  | .mk (.forLoopRev _ lo hi b) _ =>
      tDroppedMutCallsAt sigs sf writers tup false lo
        ++ tDroppedMutCallsAt sigs sf writers tup false hi
        ++ tDroppedMutCallsAt sigs sf writers tup false b
  | .mk (.whileLoop c b) _ =>
      tDroppedMutCallsAt sigs sf writers tup false c
        ++ tDroppedMutCallsAt sigs sf writers tup false b
  | .mk (.earlyReturn e) _ => tDroppedMutCallsAt sigs sf writers tup false e
  | .mk (.questionMark e) _ => tDroppedMutCallsAt sigs sf writers tup false e
  | .mk (.forFold _ lo hi b) _ =>
      tDroppedMutCallsAt sigs sf writers tup false lo
        ++ tDroppedMutCallsAt sigs sf writers tup false hi
        ++ tDroppedMutCallsAt sigs sf writers tup false b
  | .mk (.forFoldRev _ lo hi b) _ =>
      tDroppedMutCallsAt sigs sf writers tup false lo
        ++ tDroppedMutCallsAt sigs sf writers tup false hi
        ++ tDroppedMutCallsAt sigs sf writers tup false b
  | .mk (.whileFold c b) _ =>
      tDroppedMutCallsAt sigs sf writers tup false c
        ++ tDroppedMutCallsAt sigs sf writers tup false b
  | .mk (.forFoldReturn _ lo hi b) _ =>
      tDroppedMutCallsAt sigs sf writers tup false lo
        ++ tDroppedMutCallsAt sigs sf writers tup false hi
        ++ tDroppedMutCallsAt sigs sf writers tup false b
  | .mk (.forFoldRevReturn _ lo hi b) _ =>
      tDroppedMutCallsAt sigs sf writers tup false lo
        ++ tDroppedMutCallsAt sigs sf writers tup false hi
        ++ tDroppedMutCallsAt sigs sf writers tup false b
  | .mk (.whileFoldReturn c b) _ =>
      tDroppedMutCallsAt sigs sf writers tup false c
        ++ tDroppedMutCallsAt sigs sf writers tup false b
  | .mk (.cfBreak e) _ => tDroppedMutCallsAt sigs sf writers tup false e
  | .mk (.cfContinue e) _ => tDroppedMutCallsAt sigs sf writers tup false e
  | .mk (.cfBreakContinue e) _ => tDroppedMutCallsAt sigs sf writers tup false e
  | .mk (.ann e) _ => tDroppedMutCallsAt sigs sf writers tup site e
  | .mk (.namedProj _ e) _ => tDroppedMutCallsAt sigs sf writers tup false e
  | .mk (.break_ (some e)) _ => tDroppedMutCallsAt sigs sf writers tup false e
  | .mk (.lit _) _ => []
  | .mk (.var _) _ => []
  | .mk .unitVal _ => []
  | .mk (.break_ none) _ => []
  | .mk .continue_ _ => []
where
  goE : List TExpr → List (String × List Nat)
    | [] => []
    | e :: es => tDroppedMutCallsAt sigs sf writers tup false e ++ goE es
  goA : List (ImpPat × TExpr) → List (String × List Nat)
    | [] => []
    | (_, e) :: rest => tDroppedMutCallsAt sigs sf writers tup false e ++ goA rest

/-- The calls in a function body that pass a `&mut` argument and that
    `tRebindMutCalls` leaves as plain calls. The body is not itself a `let`
    value, an assignment's right-hand side or the head of a `seq`, so the scan
    starts outside every tuple-form call site. -/
def tDroppedMutCalls (sigs : List (String × FnTypeInfo)) (sf : StructFieldNames)
    (writers : List (String × Nat)) (tup : List (String × List Nat × Bool))
    (e : TExpr) : List (String × List Nat) :=
  tDroppedMutCallsAt sigs sf writers tup false e

/-- Strip the erase-deleted `.ann` type-ascription marker. Used so that the
    `if`-statement detection in `tThreadMut` looks through `.ann` and thus
    commutes with type erasure. No `.ann` nodes exist at this pre-pipeline
    stage, so this is the identity on real inputs. -/
def tStripAnn : TExpr → TExpr
  | .mk (.ann e) _ => tStripAnn e
  | e => e

/-- Thread mutations across `if`- and `match`-statement joins (see module docstring).

    `active` gates the join-threading transformation. It is `true` in
    straight-line / function-tail position and `false` inside a loop or fold
    body — there the loop accumulator mechanism (in the renderer's
    `extractAccumulators` / fold-body transforms) already threads mutated
    variables, and a competing `_mtup` rebind here would mis-detect the
    accumulator (e.g. collapse it to `()`) and emit inconsistent branch types.
    We still recurse into loop bodies (to reach nested straight-line `if`s) but
    with `active := false`.

    Defined by structural recursion. The join is detected by first threading
    the `seq` head `a` and its continuation `rest`, then inspecting the *result*
    `tStripAnn a'` for an `.ifThenElse` or a `.match_` (threading `a` first
    keeps every recursive call on a strict subterm, so the function is
    non-`partial`; looking through `.ann` keeps the detection in agreement with
    type erasure — see `ThreadMutationsErase`). On `.ann`-free inputs (the only
    inputs at this pre-pipeline stage) this agrees with a direct
    `seq (ifThenElse …) rest` / `seq (match_ …) rest` match. -/
def tThreadMut (active : Bool) : TExpr → TExpr
  | .mk (.seq a rest) ty =>
      let a' := tThreadMut active a
      let rest' := tThreadMut active rest
      match tStripAnn a' with
      | .mk (.ifThenElse c t f) _ =>
          let used := tVarRefs rest'
          let m := (tAssignedVars t ++ tAssignedVars f).eraseDups.filter used.contains
          if (!active && !tContainsLoop rest') || m.isEmpty then
            .mk (.seq a' rest') ty
          else
            let tup := tVarTuple m
            let ifE := .mk (.ifThenElse c (tReplaceTail t tup) (tReplaceTail f tup)) .unknown
            .mk (.letBind "_mtup" ifE (tDestructure m (.mk (.var "_mtup") .unknown) rest')) ty
      -- The arm bodies of a statement-`match` join exactly as the two branches
      -- of a statement-`if` do; `tAssignedVars.goA` collects the assignments of
      -- the bodies alone, leaving the scrutinee (the analogue of the condition)
      -- in place.
      | .mk (.match_ s arms) _ =>
          let used := tVarRefs rest'
          let m := (tAssignedVars.goA arms).eraseDups.filter used.contains
          if (!active && !tContainsLoop rest') || m.isEmpty then
            .mk (.seq a' rest') ty
          else
            let tup := tVarTuple m
            let matchE := .mk (.match_ s (tReplaceTail.goA arms tup)) .unknown
            .mk (.letBind "_mtup" matchE (tDestructure m (.mk (.var "_mtup") .unknown) rest')) ty
      | _ => .mk (.seq a' rest') ty
  -- Loop / fold bodies: descend with the transformation disabled.
  | .mk (.forLoop v lo hi b) ty =>
      .mk (.forLoop v (tThreadMut active lo) (tThreadMut active hi) (tThreadMut false b)) ty
  | .mk (.forLoopRev v lo hi b) ty =>
      .mk (.forLoopRev v (tThreadMut active lo) (tThreadMut active hi) (tThreadMut false b)) ty
  | .mk (.forFold v lo hi b) ty =>
      .mk (.forFold v (tThreadMut active lo) (tThreadMut active hi) (tThreadMut false b)) ty
  | .mk (.forFoldRev v lo hi b) ty =>
      .mk (.forFoldRev v (tThreadMut active lo) (tThreadMut active hi) (tThreadMut false b)) ty
  | .mk (.forFoldReturn v lo hi b) ty =>
      .mk (.forFoldReturn v (tThreadMut active lo) (tThreadMut active hi) (tThreadMut false b)) ty
  | .mk (.forFoldRevReturn v lo hi b) ty =>
      .mk (.forFoldRevReturn v (tThreadMut active lo) (tThreadMut active hi) (tThreadMut false b)) ty
  | .mk (.whileLoop c b) ty => .mk (.whileLoop (tThreadMut active c) (tThreadMut false b)) ty
  | .mk (.whileFold c b) ty => .mk (.whileFold (tThreadMut active c) (tThreadMut false b)) ty
  | .mk (.whileFoldReturn c b) ty => .mk (.whileFoldReturn (tThreadMut active c) (tThreadMut false b)) ty
  -- Every other node: traverse children with the same `active` (as `tMapChildren`).
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk (.letBind n val body) ty =>
      .mk (.letBind n (tThreadMut active val) (tThreadMut active body)) ty
  | .mk (.lam ps body) ty => .mk (.lam ps (tThreadMut active body)) ty
  | .mk (.app g args) ty => .mk (.app g (mapE active args)) ty
  | .mk (.tuple elems) ty => .mk (.tuple (mapE active elems)) ty
  | .mk (.proj e i) ty => .mk (.proj (tThreadMut active e) i) ty
  | .mk (.ifThenElse c t e) ty =>
      .mk (.ifThenElse (tThreadMut active c) (tThreadMut active t) (tThreadMut active e)) ty
  | .mk (.match_ scrut arms) ty => .mk (.match_ (tThreadMut active scrut) (mapA active arms)) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk (.borrow e) ty => .mk (.borrow (tThreadMut active e)) ty
  | .mk (.deref e) ty => .mk (.deref (tThreadMut active e)) ty
  | .mk (.assign n rhs) ty => .mk (.assign n (tThreadMut active rhs)) ty
  | .mk (.break_ none) ty => .mk (.break_ none) ty
  | .mk (.break_ (some e)) ty => .mk (.break_ (some (tThreadMut active e))) ty
  | .mk .continue_ ty => .mk .continue_ ty
  | .mk (.earlyReturn e) ty => .mk (.earlyReturn (tThreadMut active e)) ty
  | .mk (.questionMark e) ty => .mk (.questionMark (tThreadMut active e)) ty
  | .mk (.cfBreak e) ty => .mk (.cfBreak (tThreadMut active e)) ty
  | .mk (.cfContinue e) ty => .mk (.cfContinue (tThreadMut active e)) ty
  | .mk (.cfBreakContinue e) ty => .mk (.cfBreakContinue (tThreadMut active e)) ty
  | .mk (.ann e) ty => .mk (.ann (tThreadMut active e)) ty
  | .mk (.namedProj n e) ty => .mk (.namedProj n (tThreadMut active e)) ty
where
  mapE (active : Bool) : List TExpr → List TExpr
    | [] => []
    | e :: es => tThreadMut active e :: mapE active es
  mapA (active : Bool) : List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest => (p, tThreadMut active e) :: mapA active rest

end Hax
