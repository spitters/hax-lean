/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.AST
import Hax.ImpType

/-!
# Typed Expressions

`TExpr` wraps every expression with its type, mirroring hax's
`Decorated<ExprKind>` pattern where every subexpression carries
a type annotation from the Rust compiler.

## Design

Uses a mutual inductive: `TExpr` = kind + type wrapper,
`TExprKind` = the actual expression structure. This gives a
clean `TExpr.ty` accessor and mirrors hax's architecture.

The type erasure function `TExpr.erase : TExpr → ImpExpr` maps back
to the untyped AST, enabling a commuting-diagram proof strategy:
all existing untyped proofs are reused via erasure.
-/

namespace Hax

mutual
/-- A typed expression: wraps a kind with its type annotation. -/
inductive TExpr where
  | mk (kind : TExprKind) (ty : ImpType)

/-- Expression kinds — mirrors `ImpExpr` constructors with `TExpr` in recursive positions. -/
inductive TExprKind where
  -- Core (survive all phases)
  | lit (v : ImpLit)
  | var (name : String)
  | letBind (name : String) (val body : TExpr)
  | app (f : String) (args : List TExpr)
  | tuple (elems : List TExpr)
  | proj (e : TExpr) (i : Nat)
  | ifThenElse (cond thn els : TExpr)
  | match_ (scrut : TExpr) (arms : List (ImpPat × TExpr))
  | unitVal
  | seq (e1 e2 : TExpr)
  -- Consumed by dropReferences (Phase 1)
  | borrow (e : TExpr)
  | deref (e : TExpr)
  -- Consumed by localMutation (Phase 2)
  | assign (name : String) (rhs : TExpr)
  -- Consumed by functionalizeLoops (Phase 3)
  | forLoop (var : String) (lo hi body : TExpr)
  | forLoopRev (var : String) (lo hi body : TExpr)
  | whileLoop (cond body : TExpr)
  | break_ (e : Option TExpr)
  | continue_
  -- Consumed by cfIntoMonads (Phase 4)
  | earlyReturn (e : TExpr)
  | questionMark (e : TExpr)
  -- Produced by functionalizeLoops (Phase 3)
  | forFold (var : String) (lo hi body : TExpr)
  | forFoldRev (var : String) (lo hi body : TExpr)
  | whileFold (cond body : TExpr)
  | forFoldReturn (var : String) (lo hi body : TExpr)
  | forFoldRevReturn (var : String) (lo hi body : TExpr)
  | whileFoldReturn (cond body : TExpr)
  | cfBreak (e : TExpr)
  | cfContinue (e : TExpr)
  | cfBreakContinue (e : TExpr)
  -- Type annotation marker (semantically identity; the outer `TExpr.mk _ ty`'s
  -- `ty` field carries the annotation type). Inserted by `tAnnotateLetBindings`
  -- to make Lean's elaborator pick up the JSON-declared type at let-bindings.
  -- Erases to its inner expression — denotationally a no-op. The renderer
  -- separately consumes `.ann` (via `PrettyPrintT.collectLetBindingTypes` and
  -- `injectLetTypeAnnotations`) to emit first-class `ImpExpr.typeAscription`
  -- nodes on the erased ImpExpr.
  | ann (e : TExpr)
  -- Named tuple-struct projection: `commitment.0` where `commitment : T` and
  -- `T` is a newtype. Inserted by `tElideToNamedProj` to mark `.0` calls
  -- whose receiver type is a known newtype. Erases to `.app ".0" [e.erase]`
  -- — the untyped pipeline still sees the same projection structure, so
  -- `pipeline_correct` is unchanged. The renderer emits `«T.0» e` (a
  -- definitional unwrap) instead of the polymorphic runtime `«.0»`.
  | namedProj (typeName : String) (e : TExpr)
end

namespace TExpr

/-- Extract the type annotation. -/
def ty : TExpr → ImpType
  | .mk _ ty => ty

/-- Extract the expression kind. -/
def kind : TExpr → TExprKind
  | .mk kind _ => kind

instance : Inhabited TExpr := ⟨.mk .unitVal .unit⟩

end TExpr

instance : Inhabited TExprKind := ⟨.unitVal⟩

/-! ## Type Erasure -/

/-- Erase type annotations, producing the corresponding `ImpExpr`. -/
def TExpr.erase : TExpr → ImpExpr
  | .mk (.lit v) _ => .lit v
  | .mk (.var n) _ => .var n
  | .mk (.letBind n val body) _ => .letBind n val.erase body.erase
  | .mk (.app f args) _ => .app f (eraseList args)
  | .mk (.tuple elems) _ => .tuple (eraseList elems)
  | .mk (.proj e i) _ => .proj e.erase i
  | .mk (.ifThenElse c t e) _ => .ifThenElse c.erase t.erase e.erase
  | .mk (.match_ scrut arms) _ => .match_ scrut.erase (eraseArms arms)
  | .mk .unitVal _ => .unitVal
  | .mk (.seq e1 e2) _ => .seq e1.erase e2.erase
  | .mk (.borrow e) _ => .borrow e.erase
  | .mk (.deref e) _ => .deref e.erase
  | .mk (.assign n rhs) _ => .assign n rhs.erase
  | .mk (.forLoop v lo hi body) _ => .forLoop v lo.erase hi.erase body.erase
  | .mk (.forLoopRev v lo hi body) _ => .forLoopRev v lo.erase hi.erase body.erase
  | .mk (.whileLoop c body) _ => .whileLoop c.erase body.erase
  | .mk (.break_ (some e)) _ => .break_ (some e.erase)
  | .mk (.break_ none) _ => .break_ none
  | .mk .continue_ _ => .continue_
  | .mk (.earlyReturn e) _ => .earlyReturn e.erase
  | .mk (.questionMark e) _ => .questionMark e.erase
  | .mk (.forFold v lo hi body) _ => .forFold v lo.erase hi.erase body.erase
  | .mk (.forFoldRev v lo hi body) _ => .forFoldRev v lo.erase hi.erase body.erase
  | .mk (.whileFold c body) _ => .whileFold c.erase body.erase
  | .mk (.forFoldReturn v lo hi body) _ => .forFoldReturn v lo.erase hi.erase body.erase
  | .mk (.forFoldRevReturn v lo hi body) _ => .forFoldRevReturn v lo.erase hi.erase body.erase
  | .mk (.whileFoldReturn c body) _ => .whileFoldReturn c.erase body.erase
  | .mk (.cfBreak e) _ => .cfBreak e.erase
  | .mk (.cfContinue e) _ => .cfContinue e.erase
  | .mk (.cfBreakContinue e) _ => .cfBreakContinue e.erase
  -- `.ann` is a denotational no-op marker for Lean elaboration;
  -- type erasure strips it, preserving the pipeline-correctness
  -- theorems unchanged. The PrettyPrintT layer separately reads
  -- `.ann` wrappers and emits `ImpExpr.typeAscription` nodes via
  -- `injectLetTypeAnnotations` on the erased ImpExpr.
  | .mk (.ann e) _ => e.erase
  -- `.namedProj T e` is a renderer-side annotation on `.0` projections
  -- whose receiver is a newtype. At the ImpExpr level we still see a
  -- `.app ".0" [e.erase]` — equivalent to what hax originally emitted —
  -- so `pipeline_correct` (parametric in builtins) is unaffected.
  | .mk (.namedProj _ e) _ => .app ".0" [e.erase]
where
  eraseList : List TExpr → List ImpExpr
    | [] => []
    | e :: es => e.erase :: eraseList es
  eraseArms : List (ImpPat × TExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, e.erase) :: eraseArms rest

@[simp] theorem TExpr.eraseList_eq (es : List TExpr) :
    TExpr.erase.eraseList es = es.map TExpr.erase := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [TExpr.erase.eraseList, ih]

@[simp] theorem TExpr.eraseArms_eq (arms : List (ImpPat × TExpr)) :
    TExpr.erase.eraseArms arms = arms.map fun (p, e) => (p, e.erase) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [TExpr.erase.eraseArms, ih]

/-! ## Custom Induction Principle -/

/-- Custom induction principle for `TExpr` that handles nested lists.
    Mirrors `ImpExpr.ind` but with the type parameter exposed. -/
@[elab_as_elim]
def TExpr.ind {motive : TExpr → Prop}
    (lit : ∀ ty v, motive (.mk (.lit v) ty))
    (var : ∀ ty n, motive (.mk (.var n) ty))
    (letBind : ∀ ty n val body, motive val → motive body →
        motive (.mk (.letBind n val body) ty))
    (app : ∀ ty f args, (∀ a, a ∈ args → motive a) →
        motive (.mk (.app f args) ty))
    (tuple : ∀ ty elems, (∀ a, a ∈ elems → motive a) →
        motive (.mk (.tuple elems) ty))
    (proj : ∀ ty e i, motive e → motive (.mk (.proj e i) ty))
    (ifThenElse : ∀ ty c t e, motive c → motive t → motive e →
        motive (.mk (.ifThenElse c t e) ty))
    (match_ : ∀ ty scrut arms, motive scrut →
        (∀ pa, pa ∈ arms → motive pa.2) →
        motive (.mk (.match_ scrut arms) ty))
    (unitVal : ∀ ty, motive (.mk .unitVal ty))
    (seq : ∀ ty e1 e2, motive e1 → motive e2 →
        motive (.mk (.seq e1 e2) ty))
    (borrow : ∀ ty e, motive e → motive (.mk (.borrow e) ty))
    (deref : ∀ ty e, motive e → motive (.mk (.deref e) ty))
    (assign : ∀ ty n rhs, motive rhs →
        motive (.mk (.assign n rhs) ty))
    (forLoop : ∀ ty v lo hi body, motive lo → motive hi → motive body →
        motive (.mk (.forLoop v lo hi body) ty))
    (forLoopRev : ∀ ty v lo hi body, motive lo → motive hi → motive body →
        motive (.mk (.forLoopRev v lo hi body) ty))
    (whileLoop : ∀ ty c body, motive c → motive body →
        motive (.mk (.whileLoop c body) ty))
    (break_none : ∀ ty, motive (.mk (.break_ none) ty))
    (break_some : ∀ ty e, motive e →
        motive (.mk (.break_ (some e)) ty))
    (continue_ : ∀ ty, motive (.mk .continue_ ty))
    (earlyReturn : ∀ ty e, motive e →
        motive (.mk (.earlyReturn e) ty))
    (questionMark : ∀ ty e, motive e →
        motive (.mk (.questionMark e) ty))
    (forFold : ∀ ty v lo hi body, motive lo → motive hi → motive body →
        motive (.mk (.forFold v lo hi body) ty))
    (forFoldRev : ∀ ty v lo hi body, motive lo → motive hi → motive body →
        motive (.mk (.forFoldRev v lo hi body) ty))
    (whileFold : ∀ ty c body, motive c → motive body →
        motive (.mk (.whileFold c body) ty))
    (forFoldReturn : ∀ ty v lo hi body, motive lo → motive hi → motive body →
        motive (.mk (.forFoldReturn v lo hi body) ty))
    (forFoldRevReturn : ∀ ty v lo hi body, motive lo → motive hi → motive body →
        motive (.mk (.forFoldRevReturn v lo hi body) ty))
    (whileFoldReturn : ∀ ty c body, motive c → motive body →
        motive (.mk (.whileFoldReturn c body) ty))
    (cfBreak : ∀ ty e, motive e → motive (.mk (.cfBreak e) ty))
    (cfContinue : ∀ ty e, motive e → motive (.mk (.cfContinue e) ty))
    (cfBreakContinue : ∀ ty e, motive e → motive (.mk (.cfBreakContinue e) ty))
    (ann : ∀ ty e, motive e → motive (.mk (.ann e) ty))
    (namedProj : ∀ ty n e, motive e → motive (.mk (.namedProj n e) ty))
    (e : TExpr) : motive e :=
  go e
where
  go : (e : TExpr) → motive e
    | .mk (.lit v) ty => lit ty v
    | .mk (.var n) ty => var ty n
    | .mk (.letBind n v b) ty => letBind ty n v b (go v) (go b)
    | .mk (.app f args) ty => app ty f args (goList args)
    | .mk (.tuple elems) ty => tuple ty elems (goList elems)
    | .mk (.proj e i) ty => proj ty e i (go e)
    | .mk (.ifThenElse c t e) ty => ifThenElse ty c t e (go c) (go t) (go e)
    | .mk (.match_ scrut arms) ty => match_ ty scrut arms (go scrut) (goArms arms)
    | .mk .unitVal ty => unitVal ty
    | .mk (.seq e1 e2) ty => seq ty e1 e2 (go e1) (go e2)
    | .mk (.borrow e) ty => borrow ty e (go e)
    | .mk (.deref e) ty => deref ty e (go e)
    | .mk (.assign n rhs) ty => assign ty n rhs (go rhs)
    | .mk (.forLoop v lo hi body) ty =>
        forLoop ty v lo hi body (go lo) (go hi) (go body)
    | .mk (.forLoopRev v lo hi body) ty =>
        forLoopRev ty v lo hi body (go lo) (go hi) (go body)
    | .mk (.whileLoop c body) ty => whileLoop ty c body (go c) (go body)
    | .mk (.break_ none) ty => break_none ty
    | .mk (.break_ (some e)) ty => break_some ty e (go e)
    | .mk .continue_ ty => continue_ ty
    | .mk (.earlyReturn e) ty => earlyReturn ty e (go e)
    | .mk (.questionMark e) ty => questionMark ty e (go e)
    | .mk (.forFold v lo hi body) ty =>
        forFold ty v lo hi body (go lo) (go hi) (go body)
    | .mk (.forFoldRev v lo hi body) ty =>
        forFoldRev ty v lo hi body (go lo) (go hi) (go body)
    | .mk (.whileFold c body) ty => whileFold ty c body (go c) (go body)
    | .mk (.forFoldReturn v lo hi body) ty =>
        forFoldReturn ty v lo hi body (go lo) (go hi) (go body)
    | .mk (.forFoldRevReturn v lo hi body) ty =>
        forFoldRevReturn ty v lo hi body (go lo) (go hi) (go body)
    | .mk (.whileFoldReturn c body) ty =>
        whileFoldReturn ty c body (go c) (go body)
    | .mk (.cfBreak e) ty => cfBreak ty e (go e)
    | .mk (.cfContinue e) ty => cfContinue ty e (go e)
    | .mk (.cfBreakContinue e) ty => cfBreakContinue ty e (go e)
    | .mk (.ann e) ty => ann ty e (go e)
    | .mk (.namedProj n e) ty => namedProj ty n e (go e)
  goList : (es : List TExpr) → ∀ a, a ∈ es → motive a
    | _ :: _, _, .head _ => go _
    | _ :: es, a, .tail _ h => goList es a h
  goArms : (arms : List (ImpPat × TExpr)) → ∀ pa, pa ∈ arms → motive pa.2
    | _ :: _, _, .head _ => go _
    | _ :: rest, pa, .tail _ h => goArms rest pa h

/-! ## Lifting from ImpExpr -/

/-- Lift an untyped `ImpExpr` to a `TExpr` with all types set to `unknown`. -/
def TExpr.ofImpExpr : ImpExpr → TExpr
  | .lit v => .mk (.lit v) .unknown
  | .var n => .mk (.var n) .unknown
  | .letBind n val body => .mk (.letBind n (ofImpExpr val) (ofImpExpr body)) .unknown
  | .app f args => .mk (.app f (liftList args)) .unknown
  | .tuple elems => .mk (.tuple (liftList elems)) .unknown
  | .proj e i => .mk (.proj (ofImpExpr e) i) .unknown
  | .ifThenElse c t e =>
      .mk (.ifThenElse (ofImpExpr c) (ofImpExpr t) (ofImpExpr e)) .unknown
  | .match_ scrut arms =>
      .mk (.match_ (ofImpExpr scrut) (liftArms arms)) .unknown
  | .unitVal => .mk .unitVal .unit
  | .seq e1 e2 => .mk (.seq (ofImpExpr e1) (ofImpExpr e2)) .unknown
  | .borrow e => .mk (.borrow (ofImpExpr e)) .unknown
  | .deref e => .mk (.deref (ofImpExpr e)) .unknown
  | .assign n rhs => .mk (.assign n (ofImpExpr rhs)) .unknown
  | .forLoop v lo hi body =>
      .mk (.forLoop v (ofImpExpr lo) (ofImpExpr hi) (ofImpExpr body)) .unknown
  | .forLoopRev v lo hi body =>
      .mk (.forLoopRev v (ofImpExpr lo) (ofImpExpr hi) (ofImpExpr body)) .unknown
  | .whileLoop c body => .mk (.whileLoop (ofImpExpr c) (ofImpExpr body)) .unknown
  | .break_ (some e) => .mk (.break_ (some (ofImpExpr e))) .unknown
  | .break_ none => .mk (.break_ none) .unknown
  | .continue_ => .mk .continue_ .unknown
  | .earlyReturn e => .mk (.earlyReturn (ofImpExpr e)) .unknown
  | .questionMark e => .mk (.questionMark (ofImpExpr e)) .unknown
  | .forFold v lo hi body =>
      .mk (.forFold v (ofImpExpr lo) (ofImpExpr hi) (ofImpExpr body)) .unknown
  | .forFoldRev v lo hi body =>
      .mk (.forFoldRev v (ofImpExpr lo) (ofImpExpr hi) (ofImpExpr body)) .unknown
  | .whileFold c body => .mk (.whileFold (ofImpExpr c) (ofImpExpr body)) .unknown
  | .forFoldReturn v lo hi body =>
      .mk (.forFoldReturn v (ofImpExpr lo) (ofImpExpr hi) (ofImpExpr body)) .unknown
  | .forFoldRevReturn v lo hi body =>
      .mk (.forFoldRevReturn v (ofImpExpr lo) (ofImpExpr hi) (ofImpExpr body)) .unknown
  | .whileFoldReturn c body =>
      .mk (.whileFoldReturn (ofImpExpr c) (ofImpExpr body)) .unknown
  | .cfBreak e => .mk (.cfBreak (ofImpExpr e)) .unknown
  | .cfContinue e => .mk (.cfContinue (ofImpExpr e)) .unknown
  | .cfBreakContinue e => .mk (.cfBreakContinue (ofImpExpr e)) .unknown
  -- Lift via the existing `.ann` marker so erase round-trips through
  -- the new `ImpExpr.typeAscription` AST node (see `TExpr.erase` for `.ann`).
  | .typeAscription e ty => .mk (.ann (ofImpExpr e)) ty
where
  liftList : List ImpExpr → List TExpr
    | [] => []
    | e :: es => ofImpExpr e :: liftList es
  liftArms : List (ImpPat × ImpExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest => (p, ofImpExpr e) :: liftArms rest

-- The previous `TExpr.erase_ofImpExpr` round-trip theorem
-- (`(TExpr.ofImpExpr e).erase = e`) was retired with the introduction of
-- `ImpExpr.typeAscription` (P1). The new constructor lifts to
-- `.mk (.ann _) _`, which erases back to its inner expression — losing
-- the outer `.typeAscription` wrapper. The theorem was never depended
-- on by production code (only a documentation lemma); the pipeline
-- correctness theorems (`tPipeline_erase` etc.) do not flow through it.

end Hax
