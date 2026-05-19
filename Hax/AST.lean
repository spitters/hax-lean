/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

import Hax.ImpType

/-!
# Imperative Expression AST

This file defines `ImpExpr`, an imperative expression language modelling
the Hax-supported subset of Rust. Each verified compiler phase consumes
certain constructors, progressively lowering the program into a pure
functional form that maps to CatCrypt's `RawCode`.

## Constructors by phase

| Phase             | Consumed constructors                        |
|-------------------|----------------------------------------------|
| dropReferences    | `borrow`, `deref`                            |
| localMutation     | `assign`                                     |
| functionalizeLoops| `forLoop`, `whileLoop`, `break_`, `continue_`|
| cfIntoMonads      | `earlyReturn`, `questionMark`                |

After all four phases, only the *core* constructors survive.
-/

namespace Hax

/-- Literal values in the imperative language. -/
inductive ImpLit where
  | bool (b : Bool)
  | int (n : Int)
  | unit
  | uintLit (w : IntWidth) (n : Nat)   -- unsigned fixed-width literal
  | sintLit (w : IntWidth) (n : Int)   -- signed fixed-width literal
  deriving Inhabited, BEq, Repr

/-- Pattern matching arms.

    `ctorPat name args` is the general constructor pattern — used for
    ADT variants that don't have one of the specialised constructors
    below (e.g. `ControlFlow.Break`, user-defined enums). The
    specialised forms `somePat`/`nonePat`/`okPat`/`errPat` exist for
    `Option`/`Result` because they have first-class semantics in
    `Value.lean`'s `matchPat`. -/
inductive ImpPat where
  | wildcard
  | litPat (l : ImpLit)
  | varPat (name : String)
  | tuplePat (pats : List ImpPat)
  | somePat (p : ImpPat)
  | nonePat
  | okPat (p : ImpPat)
  | errPat (p : ImpPat)
  | ctorPat (name : String) (args : List ImpPat)
  deriving Inhabited, BEq, Repr

/-- Imperative expression AST.

    This is a separate type from `RawCode`, keeping the existing CatCrypt
    evaluation pipeline untouched. It is rich enough to express mutation,
    loops, and control flow — features consumed by the verified phases. -/
inductive ImpExpr where
  -- Core (survive all phases)
  | lit (v : ImpLit)
  | var (name : String)
  | letBind (name : String) (val body : ImpExpr)
  | app (f : String) (args : List ImpExpr)
  | tuple (elems : List ImpExpr)
  | proj (e : ImpExpr) (i : Nat)
  | ifThenElse (cond thn els : ImpExpr)
  | match_ (scrut : ImpExpr) (arms : List (ImpPat × ImpExpr))
  | unitVal
  | seq (e1 e2 : ImpExpr)
  -- Consumed by dropReferences (Phase 1)
  | borrow (e : ImpExpr)
  | deref (e : ImpExpr)
  -- Consumed by localMutation (Phase 2)
  | assign (name : String) (rhs : ImpExpr)
  -- Consumed by functionalizeLoops (Phase 3)
  | forLoop (var : String) (lo hi : ImpExpr) (body : ImpExpr)
  | forLoopRev (var : String) (lo hi : ImpExpr) (body : ImpExpr)
  | whileLoop (cond body : ImpExpr)
  | break_ (e : Option ImpExpr)
  | continue_
  -- Consumed by cfIntoMonads (Phase 4)
  | earlyReturn (e : ImpExpr)
  | questionMark (e : ImpExpr)
  -- Produced by functionalizeLoops (Phase 3)
  | forFold (var : String) (lo hi body : ImpExpr)
  | forFoldRev (var : String) (lo hi body : ImpExpr)
  | whileFold (cond body : ImpExpr)
  | forFoldReturn (var : String) (lo hi body : ImpExpr)
  | forFoldRevReturn (var : String) (lo hi body : ImpExpr)
  | whileFoldReturn (cond body : ImpExpr)
  | cfBreak (e : ImpExpr)
  | cfContinue (e : ImpExpr)
  -- Nested break encoding: break inside loop with earlyReturn
  -- Produces val(CF true (CF false v)) directly, avoiding cfBreak/cfContinue composition
  | cfBreakContinue (e : ImpExpr)
  -- First-class type ascription: `(e : ty)`. Replaces the legacy
  -- `::annot::<TyStr>`-string-prefix `.app` marker. Constructed by the
  -- typed pipeline at injection time so the type information is
  -- carried structurally rather than through a parsed function-name string.
  | typeAscription (e : ImpExpr) (ty : ImpType)
  deriving Inhabited

/-- Custom induction principle for `ImpExpr` that handles nested lists.
    The built-in `induction` tactic cannot handle `ImpExpr` because it is
    a nested inductive type (contains `List ImpExpr` and `List (ImpPat × ImpExpr)`).
    This principle provides proper induction hypotheses for list elements. -/
@[elab_as_elim]
def ImpExpr.ind {motive : ImpExpr → Prop}
    (lit : ∀ v, motive (.lit v))
    (var : ∀ n, motive (.var n))
    (letBind : ∀ n val body, motive val → motive body → motive (.letBind n val body))
    (app : ∀ f args, (∀ a, a ∈ args → motive a) → motive (.app f args))
    (tuple : ∀ elems, (∀ a, a ∈ elems → motive a) → motive (.tuple elems))
    (proj : ∀ e i, motive e → motive (.proj e i))
    (ifThenElse : ∀ c t e, motive c → motive t → motive e → motive (.ifThenElse c t e))
    (match_ : ∀ scrut arms, motive scrut → (∀ pa, pa ∈ arms → motive pa.2) →
        motive (.match_ scrut arms))
    (unitVal : motive .unitVal)
    (seq : ∀ e1 e2, motive e1 → motive e2 → motive (.seq e1 e2))
    (borrow : ∀ e, motive e → motive (.borrow e))
    (deref : ∀ e, motive e → motive (.deref e))
    (assign : ∀ n rhs, motive rhs → motive (.assign n rhs))
    (forLoop : ∀ v lo hi body, motive lo → motive hi → motive body →
        motive (.forLoop v lo hi body))
    (forLoopRev : ∀ v lo hi body, motive lo → motive hi → motive body →
        motive (.forLoopRev v lo hi body))
    (whileLoop : ∀ c body, motive c → motive body → motive (.whileLoop c body))
    (break_none : motive (.break_ none))
    (break_some : ∀ e, motive e → motive (.break_ (some e)))
    (continue_ : motive .continue_)
    (earlyReturn : ∀ e, motive e → motive (.earlyReturn e))
    (questionMark : ∀ e, motive e → motive (.questionMark e))
    (forFold : ∀ v lo hi body, motive lo → motive hi → motive body →
        motive (.forFold v lo hi body))
    (forFoldRev : ∀ v lo hi body, motive lo → motive hi → motive body →
        motive (.forFoldRev v lo hi body))
    (whileFold : ∀ c body, motive c → motive body → motive (.whileFold c body))
    (forFoldReturn : ∀ v lo hi body, motive lo → motive hi → motive body →
        motive (.forFoldReturn v lo hi body))
    (forFoldRevReturn : ∀ v lo hi body, motive lo → motive hi → motive body →
        motive (.forFoldRevReturn v lo hi body))
    (whileFoldReturn : ∀ c body, motive c → motive body → motive (.whileFoldReturn c body))
    (cfBreak : ∀ e, motive e → motive (.cfBreak e))
    (cfContinue : ∀ e, motive e → motive (.cfContinue e))
    (cfBreakContinue : ∀ e, motive e → motive (.cfBreakContinue e))
    (typeAscription : ∀ e ty, motive e → motive (.typeAscription e ty))
    (e : ImpExpr) : motive e :=
  go e
where
  go : (e : ImpExpr) → motive e
    | .lit v => lit v
    | .var n => var n
    | .letBind n v b => letBind n v b (go v) (go b)
    | .app f args => app f args (goList args)
    | .tuple elems => tuple elems (goList elems)
    | .proj e i => proj e i (go e)
    | .ifThenElse c t e => ifThenElse c t e (go c) (go t) (go e)
    | .match_ scrut arms => match_ scrut arms (go scrut) (goArms arms)
    | .unitVal => unitVal
    | .seq e1 e2 => seq e1 e2 (go e1) (go e2)
    | .borrow e => borrow e (go e)
    | .deref e => deref e (go e)
    | .assign n rhs => assign n rhs (go rhs)
    | .forLoop v lo hi body => forLoop v lo hi body (go lo) (go hi) (go body)
    | .forLoopRev v lo hi body => forLoopRev v lo hi body (go lo) (go hi) (go body)
    | .whileLoop c body => whileLoop c body (go c) (go body)
    | .break_ none => break_none
    | .break_ (some e) => break_some e (go e)
    | .continue_ => continue_
    | .earlyReturn e => earlyReturn e (go e)
    | .questionMark e => questionMark e (go e)
    | .forFold v lo hi body => forFold v lo hi body (go lo) (go hi) (go body)
    | .forFoldRev v lo hi body => forFoldRev v lo hi body (go lo) (go hi) (go body)
    | .whileFold c body => whileFold c body (go c) (go body)
    | .forFoldReturn v lo hi body => forFoldReturn v lo hi body (go lo) (go hi) (go body)
    | .forFoldRevReturn v lo hi body => forFoldRevReturn v lo hi body (go lo) (go hi) (go body)
    | .whileFoldReturn c body => whileFoldReturn c body (go c) (go body)
    | .cfBreak e => cfBreak e (go e)
    | .cfContinue e => cfContinue e (go e)
    | .cfBreakContinue e => cfBreakContinue e (go e)
    | .typeAscription e ty => typeAscription e ty (go e)
  goList : (es : List ImpExpr) → ∀ a, a ∈ es → motive a
    | _ :: _, _, .head _ => go _
    | _ :: es, a, .tail _ h => goList es a h
  goArms : (arms : List (ImpPat × ImpExpr)) → ∀ pa, pa ∈ arms → motive pa.2
    | _ :: _, _, .head _ => go _
    | _ :: rest, pa, .tail _ h => goArms rest pa h

/-! ## BEq instance for ImpExpr

Lean 4 cannot derive `BEq` for nested inductives (containing `List ImpExpr`),
so we define it manually. -/

/-- Structural equality for `ImpExpr`. -/
def ImpExpr.beq : ImpExpr → ImpExpr → Bool
  | .lit v₁, .lit v₂ => v₁ == v₂
  | .var n₁, .var n₂ => n₁ == n₂
  | .letBind n₁ v₁ b₁, .letBind n₂ v₂ b₂ =>
    n₁ == n₂ && v₁.beq v₂ && b₁.beq b₂
  | .app f₁ a₁, .app f₂ a₂ => f₁ == f₂ && beqList a₁ a₂
  | .tuple e₁, .tuple e₂ => beqList e₁ e₂
  | .proj e₁ i₁, .proj e₂ i₂ => e₁.beq e₂ && i₁ == i₂
  | .ifThenElse c₁ t₁ e₁, .ifThenElse c₂ t₂ e₂ =>
    c₁.beq c₂ && t₁.beq t₂ && e₁.beq e₂
  | .match_ s₁ a₁, .match_ s₂ a₂ => s₁.beq s₂ && beqArms a₁ a₂
  | .unitVal, .unitVal => true
  | .seq e₁ e₂, .seq f₁ f₂ => e₁.beq f₁ && e₂.beq f₂
  | .borrow e₁, .borrow e₂ => e₁.beq e₂
  | .deref e₁, .deref e₂ => e₁.beq e₂
  | .assign n₁ r₁, .assign n₂ r₂ => n₁ == n₂ && r₁.beq r₂
  | .forLoop v₁ l₁ h₁ b₁, .forLoop v₂ l₂ h₂ b₂ =>
    v₁ == v₂ && l₁.beq l₂ && h₁.beq h₂ && b₁.beq b₂
  | .forLoopRev v₁ l₁ h₁ b₁, .forLoopRev v₂ l₂ h₂ b₂ =>
    v₁ == v₂ && l₁.beq l₂ && h₁.beq h₂ && b₁.beq b₂
  | .whileLoop c₁ b₁, .whileLoop c₂ b₂ => c₁.beq c₂ && b₁.beq b₂
  | .break_ (some e₁), .break_ (some e₂) => e₁.beq e₂
  | .break_ none, .break_ none => true
  | .continue_, .continue_ => true
  | .earlyReturn e₁, .earlyReturn e₂ => e₁.beq e₂
  | .questionMark e₁, .questionMark e₂ => e₁.beq e₂
  | .forFold v₁ l₁ h₁ b₁, .forFold v₂ l₂ h₂ b₂ =>
    v₁ == v₂ && l₁.beq l₂ && h₁.beq h₂ && b₁.beq b₂
  | .forFoldRev v₁ l₁ h₁ b₁, .forFoldRev v₂ l₂ h₂ b₂ =>
    v₁ == v₂ && l₁.beq l₂ && h₁.beq h₂ && b₁.beq b₂
  | .whileFold c₁ b₁, .whileFold c₂ b₂ => c₁.beq c₂ && b₁.beq b₂
  | .forFoldReturn v₁ l₁ h₁ b₁, .forFoldReturn v₂ l₂ h₂ b₂ =>
    v₁ == v₂ && l₁.beq l₂ && h₁.beq h₂ && b₁.beq b₂
  | .forFoldRevReturn v₁ l₁ h₁ b₁, .forFoldRevReturn v₂ l₂ h₂ b₂ =>
    v₁ == v₂ && l₁.beq l₂ && h₁.beq h₂ && b₁.beq b₂
  | .whileFoldReturn c₁ b₁, .whileFoldReturn c₂ b₂ => c₁.beq c₂ && b₁.beq b₂
  | .cfBreak e₁, .cfBreak e₂ => e₁.beq e₂
  | .cfContinue e₁, .cfContinue e₂ => e₁.beq e₂
  | .cfBreakContinue e₁, .cfBreakContinue e₂ => e₁.beq e₂
  | .typeAscription e₁ t₁, .typeAscription e₂ t₂ => e₁.beq e₂ && t₁ == t₂
  | _, _ => false
where
  beqList : List ImpExpr → List ImpExpr → Bool
    | [], [] => true
    | e₁ :: r₁, e₂ :: r₂ => e₁.beq e₂ && beqList r₁ r₂
    | _, _ => false
  beqArms : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr) → Bool
    | [], [] => true
    | (p₁, e₁) :: r₁, (p₂, e₂) :: r₂ => p₁ == p₂ && e₁.beq e₂ && beqArms r₁ r₂
    | _, _ => false

instance : BEq ImpExpr := ⟨ImpExpr.beq⟩

end Hax
