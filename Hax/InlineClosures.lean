/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.TExpr

/-!
# Pre-pipeline normalization: inline let-bound local closures

The IR (`TExprKind`) has no lambda constructor, so a Rust *let-bound* local
closure `let f = |a, b| { body }` cannot be represented as a value. The adapter
marks such a binding with a sentinel `letBind f (app "__clo__:a,b" [body]) cont`
(only for `let`-bound closures — closures passed directly to a higher-order
function or loop keep the existing param-dropping behavior, which is correct
because the HOF/loop binds those params).

This pass eliminates the sentinel by *inlining* the closure at its call sites:
each `app f args` in the continuation becomes `body[a := arg₀, b := arg₁, …]`,
and the `let` is dropped. Without it, the closure's own params (`a`, `b`) leak
as free variables and get misclassified as `<X>Deps` typeclass fields, and the
call sites render as `call f (tuple)` — applying a non-function. Run BEFORE the
typed pipeline (it is parse-time normalization, not a verified phase).
-/

namespace Hax

/-- The sentinel head prefix marking a let-bound closure value. The substring
    after the colon is the comma-separated list of the closure's param names. -/
def closureSentinelPrefix : String := "__clo__:"

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

/-- Substitute free variables per `env` (`name ↦ replacement`). No alpha-capture
    handling is needed: the closure body's only substituted names are its own
    params, which are fresh w.r.t. the call-site arguments. -/
partial def tSubstVars (env : List (String × TExpr)) (e : TExpr) : TExpr :=
  match e.kind with
  | .var n => match env.lookup n with
    | some repl => repl
    | none => e
  | _ => tMapChildren (tSubstVars env) e

/-- Strip outer `&`/`*` wrappers to reach the underlying value. -/
def tStripRefs : TExpr → TExpr
  | .mk (.borrow e) _ => tStripRefs e
  | .mk (.deref e) _ => tStripRefs e
  | e => e

/-- Is `e` (after stripping refs) the variable `name`? -/
def tIsVarNamed (name : String) (e : TExpr) : Bool :=
  match (tStripRefs e).kind with
  | .var n => n == name
  | _ => false

/-- Bind `params` to the components of the `Fn::call` argument tuple. A literal
    tuple of matching arity is destructured directly; otherwise each param maps to
    a projection (or, for a single param, the whole argument). -/
def tMkArgEnv (params : List String) (argsTup : TExpr) : List (String × TExpr) :=
  let byProj := params.zip (List.range params.length)
    |>.map (fun (p, i) => (p, TExpr.mk (.proj argsTup i) .unknown))
  match argsTup.kind with
  | .tuple elems => if elems.length == params.length then params.zip elems else byProj
  | _ => match params with
    | [p] => [(p, argsTup)]
    | _ => byProj

/-- Inline the closure `fname` (params `params`, body `cbody`) at its call sites.
    A Rust closure call `fname(a, b)` is `Fn::call`, i.e. `app "call" [recv, (a,b)]`
    with `recv` a (possibly borrowed) reference to `fname`; rewrite it to
    `cbody[params := (a, b)]`. Other applications are left untouched. -/
partial def tInlineCall (fname : String) (params : List String) (cbody : TExpr)
    (e : TExpr) : TExpr :=
  match e.kind with
  | .app "call" (recv :: argsTup :: rest) =>
    let recv' := tInlineCall fname params cbody recv
    let argsTup' := tInlineCall fname params cbody argsTup
    let rest' := rest.map (tInlineCall fname params cbody)
    if tIsVarNamed fname recv && rest.isEmpty then
      tSubstVars (tMkArgEnv params argsTup') cbody
    else
      .mk (.app "call" (recv' :: argsTup' :: rest')) e.ty
  | _ => tMapChildren (tInlineCall fname params cbody) e

/-- Eliminate let-bound-closure sentinels by inlining at call sites. -/
partial def tInlineClosures (e : TExpr) : TExpr :=
  match e.kind with
  | .letBind name (.mk (.app head [cbodyRaw]) _) cont =>
    if head.startsWith closureSentinelPrefix then
      let suffix : String := (head.toList.drop closureSentinelPrefix.length).asString
      let params := suffix.splitOn "," |>.filter (· != "")
      let cbody := tInlineClosures cbodyRaw
      let cont' := tInlineClosures cont
      -- Inline at every call site and drop the binding. `params` is non-empty by
      -- construction (the adapter only emits the sentinel for ≥1 cleanly-named param).
      tInlineCall name params cbody cont'
    else
      tMapChildren tInlineClosures e
  | _ => tMapChildren tInlineClosures e

end Hax
