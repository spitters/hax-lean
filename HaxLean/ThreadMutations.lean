/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import HaxLean.TExpr
import HaxLean.InlineClosures

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
    (`proj 0`) and the rest live in `tup.2` (`proj 1`) — recurse there. The last
    variable binds the remaining tail directly. (A flat `tup.i` would be invalid:
    `(a,b,c).3` doesn't exist.) -/
def tDestructure : List String → TExpr → TExpr → TExpr
  | [], _, cont => cont
  | [v], tup, cont => .mk (.letBind v tup cont) cont.ty
  | v :: vs, tup, cont =>
    .mk (.letBind v (.mk (.proj tup 0) .unknown)
      (tDestructure vs (.mk (.proj tup 1) .unknown) cont)) cont.ty

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

A Rust `fn f(v: &mut T, …)` writes through the reference and yields `()`. The
extraction has no references, so `f` returns `v`'s final value and every caller
rebinds its own variable from that result:

    f(&mut x, y)  ↦  x = f(x, y)

Both halves read one table, `mutWriteFns`: the parameter position a function
writes back through. A signature admits a candidate (`mutWriteCandidates`) and
the body decides it (`mutWriteStep`) — a `&mut` parameter written only through
one of its own fields or elements assigns nothing, and such a function keeps its
`()` result. `tReturnMutParam` puts the parameter at the end of the callee's
body and `tRebindMutCalls` turns each call into an assignment, both from that
one table, so the two sides agree on which functions return a value by
construction. The result is an ordinary `.assign`, which `tThreadMut`,
`localMutation` and the renderer's accumulator extraction already carry.

`tRebindMutCalls` runs before `tReturnMutParam`: a body whose own tail is a
write-back call has to become an assignment first, or `tReplaceTail` drops it
as a pure value. -/

/-- The position and name of the parameter a function writes back through: the
    single `&mut` parameter of a function whose Rust result is `()`. Several
    `&mut` parameters, or a result that carries a value, leave the function
    with no write-back parameter. -/
def mutWriteParam (retTy : ImpType) (params : List (String × ImpType)) :
    Option (Nat × String) :=
  match retTy with
  | .unit =>
      match params.zipIdx.filterMap (fun pi =>
          match pi.1.2 with
          | .ref _ true => some (pi.2, pi.1.1)
          | _ => none) with
      | [ip] => some ip
      | _ => none
  | _ => none

/-- Each function whose signature admits a write-back parameter, as
    `(function, position, parameter)`. -/
def mutWriteCandidates (fns : List (String × FnTypeInfo)) : List (String × Nat × String) :=
  fns.filterMap fun ni =>
    (mutWriteParam ni.2.retType ni.2.paramTypes).map (fun ip => (ni.1, ip.1, ip.2))

/-- Write-back positions of a resolved table, read at call sites by
    `tRebindMutCalls`. -/
def mutWriteTable (ws : List (String × Nat × String)) : List (String × Nat) :=
  ws.map (fun c => (c.1, c.2.1))

/-- Write-back parameter names of a resolved table, read at the definition by
    `tReturnMutParam`. -/
def mutWriteParams (ws : List (String × Nat × String)) : List (String × String) :=
  ws.map (fun c => (c.1, c.2.2))

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

/-- The node a call becomes under the write-back table: an assignment binding
    the write-back variable to the call's result, or the call itself. -/
def tRebindCall (writers : List (String × Nat)) (f : String) (args : List TExpr)
    (ty : ImpType) : TExpr :=
  match tCallWriteback writers f args with
  | some v => .mk (.assign v (.mk (.app f args) ty)) ty
  | none => .mk (.app f args) ty

/-- Bind the write-back variable of every call to a write-back function from
    that call's result. A call to any other function, and a call whose
    write-back argument is an index or a field rather than a variable, keeps
    its own value. -/
def tRebindMutCalls (writers : List (String × Nat)) : TExpr → TExpr
  | .mk (.app f args) ty => tRebindCall writers f (mapE writers args) ty
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk (.letBind n val body) ty =>
      .mk (.letBind n (tRebindMutCalls writers val) (tRebindMutCalls writers body)) ty
  | .mk (.lam ps body) ty => .mk (.lam ps (tRebindMutCalls writers body)) ty
  | .mk (.tuple elems) ty => .mk (.tuple (mapE writers elems)) ty
  | .mk (.proj e i) ty => .mk (.proj (tRebindMutCalls writers e) i) ty
  | .mk (.ifThenElse c t e) ty =>
      .mk (.ifThenElse (tRebindMutCalls writers c) (tRebindMutCalls writers t)
        (tRebindMutCalls writers e)) ty
  | .mk (.match_ scrut arms) ty =>
      .mk (.match_ (tRebindMutCalls writers scrut) (mapA writers arms)) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk (.seq a b) ty =>
      .mk (.seq (tRebindMutCalls writers a) (tRebindMutCalls writers b)) ty
  | .mk (.borrow e) ty => .mk (.borrow (tRebindMutCalls writers e)) ty
  | .mk (.deref e) ty => .mk (.deref (tRebindMutCalls writers e)) ty
  | .mk (.assign n rhs) ty => .mk (.assign n (tRebindMutCalls writers rhs)) ty
  | .mk (.forLoop v lo hi b) ty =>
      .mk (.forLoop v (tRebindMutCalls writers lo) (tRebindMutCalls writers hi)
        (tRebindMutCalls writers b)) ty
  | .mk (.forLoopRev v lo hi b) ty =>
      .mk (.forLoopRev v (tRebindMutCalls writers lo) (tRebindMutCalls writers hi)
        (tRebindMutCalls writers b)) ty
  | .mk (.whileLoop c b) ty =>
      .mk (.whileLoop (tRebindMutCalls writers c) (tRebindMutCalls writers b)) ty
  | .mk (.break_ none) ty => .mk (.break_ none) ty
  | .mk (.break_ (some e)) ty => .mk (.break_ (some (tRebindMutCalls writers e))) ty
  | .mk .continue_ ty => .mk .continue_ ty
  | .mk (.earlyReturn e) ty => .mk (.earlyReturn (tRebindMutCalls writers e)) ty
  | .mk (.questionMark e) ty => .mk (.questionMark (tRebindMutCalls writers e)) ty
  | .mk (.forFold v lo hi b) ty =>
      .mk (.forFold v (tRebindMutCalls writers lo) (tRebindMutCalls writers hi)
        (tRebindMutCalls writers b)) ty
  | .mk (.forFoldRev v lo hi b) ty =>
      .mk (.forFoldRev v (tRebindMutCalls writers lo) (tRebindMutCalls writers hi)
        (tRebindMutCalls writers b)) ty
  | .mk (.whileFold c b) ty =>
      .mk (.whileFold (tRebindMutCalls writers c) (tRebindMutCalls writers b)) ty
  | .mk (.forFoldReturn v lo hi b) ty =>
      .mk (.forFoldReturn v (tRebindMutCalls writers lo) (tRebindMutCalls writers hi)
        (tRebindMutCalls writers b)) ty
  | .mk (.forFoldRevReturn v lo hi b) ty =>
      .mk (.forFoldRevReturn v (tRebindMutCalls writers lo) (tRebindMutCalls writers hi)
        (tRebindMutCalls writers b)) ty
  | .mk (.whileFoldReturn c b) ty =>
      .mk (.whileFoldReturn (tRebindMutCalls writers c) (tRebindMutCalls writers b)) ty
  | .mk (.cfBreak e) ty => .mk (.cfBreak (tRebindMutCalls writers e)) ty
  | .mk (.cfContinue e) ty => .mk (.cfContinue (tRebindMutCalls writers e)) ty
  | .mk (.cfBreakContinue e) ty => .mk (.cfBreakContinue (tRebindMutCalls writers e)) ty
  | .mk (.ann e) ty => .mk (.ann (tRebindMutCalls writers e)) ty
  | .mk (.namedProj n e) ty => .mk (.namedProj n (tRebindMutCalls writers e)) ty
where
  mapE (writers : List (String × Nat)) : List TExpr → List TExpr
    | [] => []
    | e :: es => tRebindMutCalls writers e :: mapE writers es
  mapA (writers : List (String × Nat)) : List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest => (p, tRebindMutCalls writers e) :: mapA writers rest

/-- End a write-back function's body with its write-back parameter, keeping
    every statement of the body ahead of it. The body's own tail is the Rust
    `()` result and carries no information, so replacing it loses nothing. A
    function with no write-back parameter is unchanged. -/
def tReturnMutParam (param : Option String) (body : TExpr) : TExpr :=
  match param with
  | some v => tReplaceTail body (.mk (.var v) .unknown)
  | none => body

/-- Keep the candidates whose body assigns their write-back parameter once the
    calls inside it are rebound under `prev`. A parameter written only through a
    field or an element of itself is assigned nothing, and such a function keeps
    its `()` result, so its callers keep discarding it and its emitted form is
    unchanged. -/
def mutWriteStep (defs : List (String × TExpr)) (prev : List (String × Nat))
    (cands : List (String × Nat × String)) : List (String × Nat × String) :=
  cands.filter fun c =>
    match defs.lookup c.1 with
    | some body => (tAssignedVars (tRebindMutCalls prev body)).contains c.2.2
    | none => false

/-- The write-back functions of an export. Two rounds, so a parameter written
    only by a nested write-back call is reached; the same table drives the call
    sites and the definitions, so the two sides cannot disagree about which
    functions return a value. -/
def mutWriteFns (fns : List (String × FnTypeInfo)) (defs : List (String × TExpr)) :
    List (String × Nat × String) :=
  let cands := mutWriteCandidates fns
  let r1 := mutWriteStep defs [] cands
  mutWriteStep defs (mutWriteTable r1) cands

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
