/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import HaxLean.TExpr
import HaxLean.Semantics
import HaxLean.Phase.FlattenLetFoldReturn

/-!
# Typed phase: `tFlattenLetFoldReturn`

Post-pipeline AST normalisation that rewrites `letBind "_" e rest`
patterns so the renderer's `seqFoldReturn` dispatch fires correctly and
function-level early-returns from inside `forFoldReturn` /
`forFoldRevReturn` / `whileFoldReturn` propagate to the enclosing
function-tail.

This is a render-time pass: it runs in `tPipelineFull` *after* the
verified core `tPipeline` and is not subject to the `tPipeline_erase`
commuting diagram. Its four rewrites are mechanised as
denotation-preserving identities on the untyped semantics in
`Hax/Phase/FlattenLetFoldReturn.lean` (B/C unconditional; A/D under the
`noVarRef "_"` freshness side-condition). See the `## Correctness`
section below.

## Motivation

The legacy untyped backend (`cargo hax into lean`) emits, for a discarded
`for` loop with `return v` inside:

```
match (← fold_range_return ...) with
| .Break ret => pure ret      -- function returns ret
| .Continue _ => pure <rest>  -- fold completed; continue
```

The verified pipeline emits the same shape via `seqFoldReturn`, but ONLY
when the AST has `.seq <fold> rest` at the surface. The hax JSON often
produces `.letBind "_" <fold> rest` (or worse, the fold is buried inside
the `then`-branch of an `.ifThenElse`), so `seqFoldReturn` never sees it
and the renderer emits `let _ := <fold>; rest` — silently dropping the
function-return value and producing ill-typed Lean (unresolved
`ControlFlow` type parameters).

This phase normalises four `letBind "_"`-discarding patterns:

| # | Rewrite | Reason |
|---|---|---|
| **A** | `letBind "_" .unitVal rest → rest` | Discarding `()` is a no-op. |
| **B** | `letBind "_" (letBind "_" v₁ b₁) b₂ → letBind "_" v₁ (letBind "_" b₁ b₂)` | Associativity of discarded binds. |
| **C** | `letBind "_" (ifThenElse c t e) rest → ifThenElse c (letBind "_" t rest) (letBind "_" e rest)` (when `t` or `e` contains a fold-with-return) | Push `rest` into branches so the function-return propagates. |
| **D** | `letBind "_" <forFoldReturn> rest → seq <forFoldReturn> rest` | Surface the fold to `seqFoldReturn` so it emits the match-and-destructure form. |

All four are denotation-preserving:

- **A**: `letBind "_" .unitVal e ≡ e` because the bind name `"_"` is
  unreferenced and `.unitVal` is side-effect-free.
- **B**: both forms evaluate `v₁`, then `b₁`, then `b₂` in sequence.
- **C**: both forms branch on `c` and execute exactly one of `t`/`e`,
  then `rest`. The duplicate `rest` in the AST runs once dynamically.
- **D**: `letBind "_" e r ≡ seq e r` whenever `"_"` is not free in `r`.
  By convention `"_"` is the universal discard binding and never a
  free reference, so the equivalence holds for any `e`.

## Termination

The pass is **total**: it takes an explicit `fuel : Nat`, every
recursive call decrements it, and `fuel = 0` returns the input
unchanged. The B/C re-invocations that cross the structural boundary are
bounded by `fuel`. With `fuel` larger than the (finite) recursion depth
the result is the rewrite fixpoint (rules A/D structurally decreasing; B
rotates to the right-leaning canonical fixpoint; C's sub-letBinds are
strictly smaller). `tPipelineFull` supplies a generous quadratic-in-size
fuel, so production output matches the previous `partial`-`def` fixpoint.
-/

namespace Hax

/-- Typed `hasNestedFoldWithReturn`: detect whether the typed expression
    contains a `forFoldReturn` / `forFoldRevReturn` / `whileFoldReturn`
    whose body has a function-level early-return (`.cfBreak _` at the
    body surface). -/
def tHasNestedFoldWithReturn (e : TExpr) : Bool :=
  match e with
  | .mk (.forFoldReturn _ _ _ b) _ | .mk (.forFoldRevReturn _ _ _ b) _
  | .mk (.whileFoldReturn _ b) _ =>
    tBodyHasSurfaceCfBreak b || tHasNestedFoldWithReturn b
  | .mk (.letBind _ v body) _ => tHasNestedFoldWithReturn v || tHasNestedFoldWithReturn body
  | .mk (.seq a b) _ => tHasNestedFoldWithReturn a || tHasNestedFoldWithReturn b
  | .mk (.ifThenElse _ t e') _ => tHasNestedFoldWithReturn t || tHasNestedFoldWithReturn e'
  | .mk (.match_ _ arms) _ => tNestedAnyArms arms
  | .mk (.ann e') _ => tHasNestedFoldWithReturn e'
  | _ => false
where
  tBodyHasSurfaceCfBreak : TExpr → Bool
    | .mk (.cfBreak _) _ => true
    | .mk (.ifThenElse _ t e) _ => tBodyHasSurfaceCfBreak t || tBodyHasSurfaceCfBreak e
    | .mk (.letBind _ _ b) _ => tBodyHasSurfaceCfBreak b
    | .mk (.seq a b) _ => tBodyHasSurfaceCfBreak a || tBodyHasSurfaceCfBreak b
    | .mk (.match_ _ arms) _ => tBodyAnyArms arms
    | .mk (.ann e) _ => tBodyHasSurfaceCfBreak e
    -- Stop at inner loop bodies — their cfBreaks belong to them.
    | .mk (.forFold _ _ _ _) _ | .mk (.forFoldRev _ _ _ _) _
    | .mk (.forFoldReturn _ _ _ _) _ | .mk (.forFoldRevReturn _ _ _ _) _
    | .mk (.whileFold _ _) _ | .mk (.whileFoldReturn _ _) _ => false
    | _ => false
  tBodyAnyArms : List (ImpPat × TExpr) → Bool
    | [] => false
    | (_, b) :: rest => tBodyHasSurfaceCfBreak b || tBodyAnyArms rest
  tNestedAnyArms : List (ImpPat × TExpr) → Bool
    | [] => false
    | (_, b) :: rest => tHasNestedFoldWithReturn b || tNestedAnyArms rest

/-- Typed flattening pass. Bottom-up structural traversal; at each
    `.letBind "_"` apply A/B/C/D as appropriate. Preserves outer types
    on every node. -/
def tFlattenLetFoldReturn : Nat → TExpr → TExpr
  | 0, e => e
  | _ + 1, .mk (.lit v) ty => .mk (.lit v) ty
  | _ + 1, .mk (.var n) ty => .mk (.var n) ty
  | _ + 1, .mk .unitVal ty => .mk .unitVal ty
  | _ + 1, .mk .continue_ ty => .mk .continue_ ty
  | _ + 1, .mk (.break_ none) ty => .mk (.break_ none) ty
  | fuel + 1, .mk (.break_ (some e)) ty =>
    .mk (.break_ (some (tFlattenLetFoldReturn fuel e))) ty
  | fuel + 1, .mk (.lam ps body) ty => .mk (.lam ps (tFlattenLetFoldReturn fuel body)) ty
  | fuel + 1, .mk (.app f args) ty => .mk (.app f (args.map (tFlattenLetFoldReturn fuel))) ty
  | fuel + 1, .mk (.tuple es) ty => .mk (.tuple (es.map (tFlattenLetFoldReturn fuel))) ty
  | fuel + 1, .mk (.proj e i) ty => .mk (.proj (tFlattenLetFoldReturn fuel e) i) ty
  | fuel + 1, .mk (.ifThenElse c t e) ty =>
    .mk (.ifThenElse (tFlattenLetFoldReturn fuel c) (tFlattenLetFoldReturn fuel t)
      (tFlattenLetFoldReturn fuel e)) ty
  | fuel + 1, .mk (.match_ scrut arms) ty =>
    .mk (.match_ (tFlattenLetFoldReturn fuel scrut)
      (arms.map fun pe => (pe.1, tFlattenLetFoldReturn fuel pe.2))) ty
  | fuel + 1, .mk (.seq a b) ty =>
    let a' := tFlattenLetFoldReturn fuel a
    let b' := tFlattenLetFoldReturn fuel b
    -- Rule C' (seq-if-distribute): push `b'` into both `if` branches
    -- when a branch carries a fold-with-return, so the early-return
    -- reaches the function tail. Denotation-preserving like rule C.
    match a' with
    | .mk (.ifThenElse c t e) _ =>
      if tHasNestedFoldWithReturn t || tHasNestedFoldWithReturn e then
        .mk (.ifThenElse c
          (tFlattenLetFoldReturn fuel (.mk (.seq t b') ty))
          (tFlattenLetFoldReturn fuel (.mk (.seq e b') ty))) ty
      else
        .mk (.seq a' b') ty
    | _ => .mk (.seq a' b') ty
  | fuel + 1, .mk (.borrow e) ty => .mk (.borrow (tFlattenLetFoldReturn fuel e)) ty
  | fuel + 1, .mk (.deref e) ty => .mk (.deref (tFlattenLetFoldReturn fuel e)) ty
  | fuel + 1, .mk (.assign n rhs) ty => .mk (.assign n (tFlattenLetFoldReturn fuel rhs)) ty
  | fuel + 1, .mk (.forLoop v lo hi body) ty =>
    .mk (.forLoop v (tFlattenLetFoldReturn fuel lo) (tFlattenLetFoldReturn fuel hi)
      (tFlattenLetFoldReturn fuel body)) ty
  | fuel + 1, .mk (.forLoopRev v lo hi body) ty =>
    .mk (.forLoopRev v (tFlattenLetFoldReturn fuel lo) (tFlattenLetFoldReturn fuel hi)
      (tFlattenLetFoldReturn fuel body)) ty
  | fuel + 1, .mk (.whileLoop c body) ty =>
    .mk (.whileLoop (tFlattenLetFoldReturn fuel c) (tFlattenLetFoldReturn fuel body)) ty
  | fuel + 1, .mk (.earlyReturn e) ty => .mk (.earlyReturn (tFlattenLetFoldReturn fuel e)) ty
  | fuel + 1, .mk (.questionMark e) ty => .mk (.questionMark (tFlattenLetFoldReturn fuel e)) ty
  | fuel + 1, .mk (.forFold v lo hi body) ty =>
    .mk (.forFold v (tFlattenLetFoldReturn fuel lo) (tFlattenLetFoldReturn fuel hi)
      (tFlattenLetFoldReturn fuel body)) ty
  | fuel + 1, .mk (.forFoldRev v lo hi body) ty =>
    .mk (.forFoldRev v (tFlattenLetFoldReturn fuel lo) (tFlattenLetFoldReturn fuel hi)
      (tFlattenLetFoldReturn fuel body)) ty
  | fuel + 1, .mk (.whileFold c body) ty =>
    .mk (.whileFold (tFlattenLetFoldReturn fuel c) (tFlattenLetFoldReturn fuel body)) ty
  | fuel + 1, .mk (.forFoldReturn v lo hi body) ty =>
    .mk (.forFoldReturn v (tFlattenLetFoldReturn fuel lo) (tFlattenLetFoldReturn fuel hi)
      (tFlattenLetFoldReturn fuel body)) ty
  | fuel + 1, .mk (.forFoldRevReturn v lo hi body) ty =>
    .mk (.forFoldRevReturn v (tFlattenLetFoldReturn fuel lo) (tFlattenLetFoldReturn fuel hi)
      (tFlattenLetFoldReturn fuel body)) ty
  | fuel + 1, .mk (.whileFoldReturn c body) ty =>
    .mk (.whileFoldReturn (tFlattenLetFoldReturn fuel c) (tFlattenLetFoldReturn fuel body)) ty
  | fuel + 1, .mk (.cfBreak e) ty => .mk (.cfBreak (tFlattenLetFoldReturn fuel e)) ty
  | fuel + 1, .mk (.cfContinue e) ty => .mk (.cfContinue (tFlattenLetFoldReturn fuel e)) ty
  | fuel + 1, .mk (.cfBreakContinue e) ty => .mk (.cfBreakContinue (tFlattenLetFoldReturn fuel e)) ty
  | fuel + 1, .mk (.ann e) ty => .mk (.ann (tFlattenLetFoldReturn fuel e)) ty
  | fuel + 1, .mk (.namedProj n e) ty => .mk (.namedProj n (tFlattenLetFoldReturn fuel e)) ty
  | fuel + 1, .mk (.letBind n val body) ty =>
    let val' := tFlattenLetFoldReturn fuel val
    let body' := tFlattenLetFoldReturn fuel body
    -- Peel a `.ann` wrapper inserted by `tAnnotateLetBindings`.
    let valStripped := match val' with
      | .mk (.ann inner) _ => inner
      | _ => val'
    if n == "_" then
      match valStripped with
      | .mk .unitVal _ => body'
      | .mk (.forFoldReturn v lo hi b) foldTy =>
        .mk (.seq (.mk (.forFoldReturn v lo hi b) foldTy) body') ty
      | .mk (.forFoldRevReturn v lo hi b) foldTy =>
        .mk (.seq (.mk (.forFoldRevReturn v lo hi b) foldTy) body') ty
      | .mk (.whileFoldReturn c b) foldTy =>
        .mk (.seq (.mk (.whileFoldReturn c b) foldTy) body') ty
      | .mk (.letBind "_" innerVal innerBody) _ =>
        tFlattenLetFoldReturn fuel (.mk (.letBind "_" innerVal
          (.mk (.letBind "_" innerBody body') ty)) ty)
      | .mk (.seq innerA innerB) _ =>
        tFlattenLetFoldReturn fuel (.mk (.letBind "_" innerA
          (.mk (.letBind "_" innerB body') ty)) ty)
      | .mk (.ifThenElse c t e) _ =>
        if tHasNestedFoldWithReturn t || tHasNestedFoldWithReturn e then
          .mk (.ifThenElse c
            (tFlattenLetFoldReturn fuel (.mk (.letBind "_" t body') ty))
            (tFlattenLetFoldReturn fuel (.mk (.letBind "_" e body') ty))) ty
        else
          .mk (.letBind n val' body') ty
      | _ => .mk (.letBind n val' body') ty
    else
      .mk (.letBind n val' body') ty

/-! ## Correctness

The pass is built from four AST-level identities, each a program
equivalence on `ImpExpr`. All four are now **mechanised** on the untyped
`denote` semantics in `Hax/Phase/FlattenLetFoldReturn.lean`:

- **A** `letBind "_" .unitVal e ≡ e` — `flattenA_denote`
- **B / B′** discarded-bind associativity — `flattenB_denote`
- **C / C′** distribute the tail into both `ifThenElse` branches —
  `flattenC_denote`
- **D** `letBind "_" e r ≡ seq e r` — `flattenD_denote`

**B and C are unconditional** clean `denote = denote` equalities (both
sides bind `"_"` to the same value before running the tail, so the two
`StateM Env Outcome` functions coincide).

**A and D depend on the freshness side-condition** `noVarRef "_" r`: they
change the `"_"` slot of the environment (A drops a `()` binding; D
replaces `letBind "_"` by `seq`, which does not bind `"_"`). This is the
universal discard-binding convention: `letBind "_"` introduces a bind
that is never read. Both are proved via the env-insensitivity congruence
`denote_agreeExcept`: under `noVarRef "_" r`, `denote` maps
`Env.AgreeExcept "_"`-related states to equal outcomes and
`AgreeExcept "_"`-related output states. A and D therefore preserve the
outcome and leave the output environments agreeing except at the unread
`"_"` slot.

**Total reformulation.** `tFlattenLetFoldReturn` is now a **total**
`fuel`-bounded function (`Nat → TExpr → TExpr`): every recursive call
decrements `fuel`, and `fuel = 0` returns the input unchanged. The B/C
re-invocations that crossed the structural boundary in the old
`partial def` are now bounded by `fuel`. The untyped twin
`flattenLetFoldReturn : Nat → ImpExpr → ImpExpr`
(`Hax/Phase/FlattenLetFoldReturn.lean`) mirrors it on erased ASTs. At the
call site (`tPipelineFull`) the fuel is a generous quadratic bound in the
AST node count, exceeding the (finite) recursion depth, so the output is
the rewrite fixpoint — identical to the previous `partial` version.

**Composable infrastructure for the whole-pass denotation result.** Now
that equational lemmas exist, the building blocks are mechanised:
`Rel "_"` (equal outcome + `AgreeExcept "_"` output states) is a partial
equivalence (`Rel.symm`, `Rel.trans`) with a bind congruence
(`Rel.bind`); the A/D rewrites have two-environment forms (`flattenA_rel`,
`flattenD_rel`) that compose with it; B/C are clean `denote` equalities.

**Whole-pass denotation preservation (proved).** The end-to-end theorem
`flattenLetFoldReturn_denote`,
`noVarRef "_" e → Rel "_" (denote (flattenLetFoldReturn k e)) (denote e)`,
is mechanised on the total untyped twin (axiom-clean). It is a
heterogeneous structural congruence — the helper relations
`denote{Args,MatchArms,ForLoop,ForLoopRev,While}_rel_het` relate each
`denote`-helper on the flattened subterms to the original, and
`flatten_noVarRef` propagates the freshness invariant — composed with the
four rewrite identities (A/D via `flattenA_rel`/`flattenD_rel`; B/C and
their seq-forms `flattenBseq_eq`/`flattenCseq_eq`) through the `Rel`
partial equivalence.

**Remaining (named, no `sorry`).** A *fixed-fuel* erase lemma
`(tFlattenLetFoldReturn k e).erase = flattenLetFoldReturn k e.erase` does
**not** hold for arbitrary `k`: `ann`/`namedProj` nodes exist in `TExpr`
but are removed by `erase`, so they consume fuel on the typed side but
not the untyped one. The two agree only once both reach the rewrite
fixpoint (sufficient fuel), not at every `k`. The whole-pass theorem
above is stated on the untyped twin precisely to avoid this obstruction:
it compares to the fuel-independent original `denote`, so `ann` passes
straight to the induction hypothesis.
-/

end Hax
