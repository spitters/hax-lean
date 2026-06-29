/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.TExpr

/-!
# Pre-pipeline normalization: lower closure calls to direct applications

A Rust *let-bound* local closure `let f = |a, b| { body }` is represented as a
first-class `.lam` value by the adapter: `letBind f (.lam [a,b] body) cont`. Its
invocations, however, arrive as `Fn::call(f, (x, y))` — i.e. `app "call" [f, (x,y)]`
with the synthetic `call` head — which would render as `call f (tuple)` (applying
a non-function) and pollute the `<X>Deps` class with a `call` field.

This pass lowers every such call **whose receiver is a let-bound `.lam`** to a
direct application `app f [x, y]` (the args tuple is unbundled), which renders as
`f x y` against the in-scope `let f := fun a b => body`. Calls of higher-order
*parameters* (not let-bound lambdas) keep the `Fn::call` form — they are genuine
opaque dependencies. Run BEFORE the typed pipeline (parse-time normalization).
-/

namespace Hax

/-- Apply `f` to every immediate `TExpr` child, rebuilding the node with the
    same kind and type. The single generic traversal the helpers below reuse. -/
def tMapChildren (f : TExpr → TExpr) : TExpr → TExpr
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk (.letBind n val body) ty => .mk (.letBind n (f val) (f body)) ty
  | .mk (.lam ps body) ty => .mk (.lam ps (f body)) ty
  | .mk (.app g args) ty => .mk (.app g (args.map f)) ty
  | .mk (.tuple elems) ty => .mk (.tuple (elems.map f)) ty
  | .mk (.proj e i) ty => .mk (.proj (f e) i) ty
  | .mk (.ifThenElse c t e) ty => .mk (.ifThenElse (f c) (f t) (f e)) ty
  | .mk (.match_ scrut arms) ty => .mk (.match_ (f scrut) (arms.map (fun (p, e) => (p, f e)))) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk (.seq e1 e2) ty => .mk (.seq (f e1) (f e2)) ty
  | .mk (.borrow e) ty => .mk (.borrow (f e)) ty
  | .mk (.deref e) ty => .mk (.deref (f e)) ty
  | .mk (.assign n rhs) ty => .mk (.assign n (f rhs)) ty
  | .mk (.forLoop v lo hi body) ty => .mk (.forLoop v (f lo) (f hi) (f body)) ty
  | .mk (.forLoopRev v lo hi body) ty => .mk (.forLoopRev v (f lo) (f hi) (f body)) ty
  | .mk (.whileLoop c body) ty => .mk (.whileLoop (f c) (f body)) ty
  | .mk (.break_ none) ty => .mk (.break_ none) ty
  | .mk (.break_ (some e)) ty => .mk (.break_ (some (f e))) ty
  | .mk .continue_ ty => .mk .continue_ ty
  | .mk (.earlyReturn e) ty => .mk (.earlyReturn (f e)) ty
  | .mk (.questionMark e) ty => .mk (.questionMark (f e)) ty
  | .mk (.forFold v lo hi body) ty => .mk (.forFold v (f lo) (f hi) (f body)) ty
  | .mk (.forFoldRev v lo hi body) ty => .mk (.forFoldRev v (f lo) (f hi) (f body)) ty
  | .mk (.whileFold c body) ty => .mk (.whileFold (f c) (f body)) ty
  | .mk (.forFoldReturn v lo hi body) ty => .mk (.forFoldReturn v (f lo) (f hi) (f body)) ty
  | .mk (.forFoldRevReturn v lo hi body) ty => .mk (.forFoldRevReturn v (f lo) (f hi) (f body)) ty
  | .mk (.whileFoldReturn c body) ty => .mk (.whileFoldReturn (f c) (f body)) ty
  | .mk (.cfBreak e) ty => .mk (.cfBreak (f e)) ty
  | .mk (.cfContinue e) ty => .mk (.cfContinue (f e)) ty
  | .mk (.cfBreakContinue e) ty => .mk (.cfBreakContinue (f e)) ty
  | .mk (.ann e) ty => .mk (.ann (f e)) ty
  | .mk (.namedProj n e) ty => .mk (.namedProj n (f e)) ty

/-- Strip outer `&`/`*` wrappers to reach the underlying value. -/
def tStripRefs : TExpr → TExpr
  | .mk (.borrow e) _ => tStripRefs e
  | .mk (.deref e) _ => tStripRefs e
  | e => e

/-- The variable name `e` refers to, after stripping `&`/`*` wrappers. -/
def tVarName? (e : TExpr) : Option String :=
  match (tStripRefs e).kind with
  | .var n => some n
  | _ => none

/-- Unbundle a `Fn::call` argument tuple into the positional argument list (a
    literal tuple becomes its elements; anything else is a single argument). -/
def tUnbundleArgs : TExpr → List TExpr
  | .mk (.tuple elems) _ => elems
  | e => [e]

/-- Lower `Fn::call` invocations of a let-bound `.lam` to direct applications.
    `lamNames` is the set of in-scope let-bound lambda names. A call
    `app "call" [recv, argsTup]` whose `recv` is one of them becomes
    `app <name> <unbundled args>`; all other nodes (including `Fn::call` of a
    higher-order *parameter*) are traversed structurally and left in place. -/
partial def tLowerClosureCalls (lamNames : List String) (e : TExpr) : TExpr :=
  match e.kind with
  | .letBind name (.mk (.lam ps lbody) lty) cont =>
    let lbody' := tLowerClosureCalls lamNames lbody
    let cont' := tLowerClosureCalls (name :: lamNames) cont
    .mk (.letBind name (.mk (.lam ps lbody') lty) cont') e.ty
  | .app "call" (recv :: argsTup :: rest) =>
    match tVarName? recv with
    | some name =>
      if rest.isEmpty && lamNames.contains name then
        let args := (tUnbundleArgs argsTup).map (tLowerClosureCalls lamNames)
        .mk (.app name args) e.ty
      else tMapChildren (tLowerClosureCalls lamNames) e
    | none => tMapChildren (tLowerClosureCalls lamNames) e
  | _ => tMapChildren (tLowerClosureCalls lamNames) e

/-- Collect the names of every `let`-bound `.lam` (for excluding them from the
    `<X>Deps` class — they are local functions, not opaque dependencies). -/
partial def tLamBoundNames : TExpr → List String
  | .mk (.letBind name (.mk (.lam _ lbody) _) cont) _ =>
    name :: tLamBoundNames lbody ++ tLamBoundNames cont
  | e => (collectChildren e).foldl (fun acc c => acc ++ tLamBoundNames c) []
where
  /-- Immediate `TExpr` children (for the generic recursion above). -/
  collectChildren : TExpr → List TExpr
    | .mk (.letBind _ v b) _ => [v, b]
    | .mk (.lam _ b) _ => [b]
    | .mk (.app _ args) _ => args
    | .mk (.tuple es) _ => es
    | .mk (.proj e _) _ => [e]
    | .mk (.ifThenElse c t e) _ => [c, t, e]
    | .mk (.match_ s arms) _ => s :: arms.map (·.2)
    | .mk (.seq a b) _ => [a, b]
    | .mk (.borrow e) _ | .mk (.deref e) _ | .mk (.ann e) _
    | .mk (.namedProj _ e) _ | .mk (.earlyReturn e) _ | .mk (.questionMark e) _
    | .mk (.cfBreak e) _ | .mk (.cfContinue e) _ | .mk (.cfBreakContinue e) _
    | .mk (.break_ (some e)) _ | .mk (.assign _ e) _ => [e]
    | .mk (.forLoop _ lo hi b) _ | .mk (.forLoopRev _ lo hi b) _
    | .mk (.forFold _ lo hi b) _ | .mk (.forFoldRev _ lo hi b) _
    | .mk (.forFoldReturn _ lo hi b) _ | .mk (.forFoldRevReturn _ lo hi b) _ => [lo, hi, b]
    | .mk (.whileLoop c b) _ | .mk (.whileFold c b) _ | .mk (.whileFoldReturn c b) _ => [c, b]
    | _ => []

end Hax
