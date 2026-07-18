/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import HaxLean.AST
import HaxLean.Features

/-!
# Phase 5: Explicit Monadic Encoding

Wraps pure return positions in `cfContinue` within fold bodies, making the
ControlFlow encoding explicit. After this phase, every fold body returns
a `ControlFlow` value — either `cfBreak` (stop/break) or `cfContinue` (continue).

## Main definitions

* `wrapReturns` — wraps pure return positions in `cfContinue`
* `explicitMonadic` — the full phase: recurse + wrap fold bodies
* `explicitMonadic_preserves_*` — feature preservation theorems

## Semantic justification

The phase is semantically neutral for fold bodies because `denoteForLoop'`
and `denoteWhile'` treat bare values (`val v`) identically to
`val (controlFlow false v)` — both continue iteration.
-/

namespace Hax

/-! ## wrapReturns: wrap return positions in cfContinue -/

/-- Wrap pure return positions in `cfContinue`. Walks the "return spine"
    (letBind body, if branches, match arms, seq tail) and wraps leaf
    positions that aren't already CF operations. -/
def wrapReturns : ImpExpr → ImpExpr
  -- Already CF: leave unchanged
  | .cfBreak e => .cfBreak e
  | .cfContinue e => .cfContinue e
  | .cfBreakContinue e => .cfBreakContinue e
  -- Return spine: recurse into return positions
  | .letBind n val body => .letBind n val (wrapReturns body)
  | .ifThenElse c t e => .ifThenElse c (wrapReturns t) (wrapReturns e)
  | .seq e1 e2 => .seq e1 (wrapReturns e2)
  | .match_ scrut arms => .match_ scrut (wrapReturnsArms arms)
  -- Type ascriptions are transparent: descend into the inner expression.
  -- Mirrors `tWrapReturns` for `.ann` so erase-preservation holds.
  | .typeAscription e ty => .typeAscription (wrapReturns e) ty
  -- Leaf return position: wrap in cfContinue
  | e => .cfContinue e
where
  wrapReturnsArms : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, wrapReturns e) :: wrapReturnsArms rest

@[simp] theorem wrapReturns.wrapReturnsArms_eq (arms : List (ImpPat × ImpExpr)) :
    wrapReturns.wrapReturnsArms arms =
      arms.map fun (p, e) => (p, wrapReturns e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [wrapReturns.wrapReturnsArms, ih]

/-! ## explicitMonadic: the full phase -/

/-- Phase 5: Make monadic encoding explicit by wrapping fold body return
    positions in `cfContinue`. After this phase, fold bodies always return
    ControlFlow values (either `cfBreak`/`cfBreakContinue` or `cfContinue`). -/
def explicitMonadic : ImpExpr → ImpExpr
  | .lit v => .lit v
  | .var n => .var n
  | .unitVal => .unitVal
  | .letBind n val body =>
      .letBind n (explicitMonadic val) (explicitMonadic body)
  | .lam ps body => .lam ps (explicitMonadic body)
  | .app f args => .app f (mapExpr args)
  | .tuple elems => .tuple (mapExpr elems)
  | .proj e i => .proj (explicitMonadic e) i
  | .ifThenElse c t e =>
      .ifThenElse (explicitMonadic c) (explicitMonadic t) (explicitMonadic e)
  | .match_ scrut arms =>
      .match_ (explicitMonadic scrut) (mapArms arms)
  | .seq e1 e2 => .seq (explicitMonadic e1) (explicitMonadic e2)
  -- Fold bodies: recurse then wrap returns
  | .forFold v lo hi body =>
      .forFold v (explicitMonadic lo) (explicitMonadic hi)
        (wrapReturns (explicitMonadic body))
  | .whileFold c body =>
      .whileFold (explicitMonadic c) (wrapReturns (explicitMonadic body))
  | .forFoldReturn v lo hi body =>
      .forFoldReturn v (explicitMonadic lo) (explicitMonadic hi)
        (wrapReturns (explicitMonadic body))
  | .whileFoldReturn c body =>
      .whileFoldReturn (explicitMonadic c) (wrapReturns (explicitMonadic body))
  | .forFoldRev v lo hi body =>
      .forFoldRev v (explicitMonadic lo) (explicitMonadic hi)
        (wrapReturns (explicitMonadic body))
  | .forFoldRevReturn v lo hi body =>
      .forFoldRevReturn v (explicitMonadic lo) (explicitMonadic hi)
        (wrapReturns (explicitMonadic body))
  -- CF constructors: recurse
  | .cfBreak e => .cfBreak (explicitMonadic e)
  | .cfContinue e => .cfContinue (explicitMonadic e)
  | .cfBreakContinue e => .cfBreakContinue (explicitMonadic e)
  -- Pre-pipeline constructors: pass through
  | .borrow e => .borrow (explicitMonadic e)
  | .deref e => .deref (explicitMonadic e)
  | .assign n rhs => .assign n (explicitMonadic rhs)
  | .forLoop v lo hi body =>
      .forLoop v (explicitMonadic lo) (explicitMonadic hi) (explicitMonadic body)
  | .forLoopRev v lo hi body =>
      .forLoopRev v (explicitMonadic lo) (explicitMonadic hi) (explicitMonadic body)
  | .whileLoop c body => .whileLoop (explicitMonadic c) (explicitMonadic body)
  | .break_ (some e) => .break_ (some (explicitMonadic e))
  | .break_ none => .break_ none
  | .continue_ => .continue_
  | .earlyReturn e => .earlyReturn (explicitMonadic e)
  | .questionMark e => .questionMark (explicitMonadic e)
  | .typeAscription e ty => .typeAscription (explicitMonadic e) ty
where
  mapExpr : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => explicitMonadic e :: mapExpr es
  mapArms : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, explicitMonadic e) :: mapArms rest

@[simp] theorem explicitMonadic.mapExpr_eq (es : List ImpExpr) :
    explicitMonadic.mapExpr es = es.map explicitMonadic := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [explicitMonadic.mapExpr, ih]

@[simp] theorem explicitMonadic.mapArms_eq (arms : List (ImpPat × ImpExpr)) :
    explicitMonadic.mapArms arms =
      arms.map fun (p, e) => (p, explicitMonadic e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [explicitMonadic.mapArms, ih]

/-! ## Feature Preservation: wrapReturns -/

private theorem wrapReturns_preserves (e : ImpExpr)
    {P : ImpExpr → Prop}
    (h : P e)
    -- P is closed under cfContinue
    (hcf : ∀ e, P e → P (.cfContinue e))
    -- P decomposes for return-spine nodes
    (hLetBind : ∀ n val body, P (.letBind n val body) → P val ∧ P body)
    (hIf : ∀ c t e, P (.ifThenElse c t e) → P c ∧ P t ∧ P e)
    (hSeq : ∀ e1 e2, P (.seq e1 e2) → P e1 ∧ P e2)
    (hMatch : ∀ scrut arms, P (.match_ scrut arms) →
        P scrut ∧ ∀ pa, pa ∈ arms → P pa.2)
    -- P rebuilds for return-spine nodes
    (mkLetBind : ∀ n val body, P val → P body → P (.letBind n val body))
    (mkIf : ∀ c t e, P c → P t → P e → P (.ifThenElse c t e))
    (mkSeq : ∀ e1 e2, P e1 → P e2 → P (.seq e1 e2))
    (mkMatch : ∀ scrut arms, P scrut →
        (∀ pa, pa ∈ arms → P pa.2) → P (.match_ scrut arms))
    -- P decomposes / rebuilds through typeAscription (transparent wrapper)
    (hAsc : ∀ e ty, P (.typeAscription e ty) → P e)
    (mkAsc : ∀ e ty, P e → P (.typeAscription e ty))
    : P (wrapReturns e) := by
  induction e using ImpExpr.ind with
  | cfBreak _ _ => exact h
  | cfContinue _ _ => exact h
  | cfBreakContinue _ _ => exact h
  | typeAscription _ _ ih =>
    rename_i e' ty
    exact mkAsc _ _ (ih (hAsc e' ty h))
  | letBind n val body _ ih_body =>
    have ⟨hval, hbody⟩ := hLetBind n val body h
    exact mkLetBind n val _ hval (ih_body hbody)
  | ifThenElse c t e _ ih_t ih_e =>
    have ⟨hc, ht, he⟩ := hIf c t e h
    exact mkIf c _ _ hc (ih_t ht) (ih_e he)
  | seq e1 e2 _ ih2 =>
    have ⟨h1, h2⟩ := hSeq e1 e2 h
    exact mkSeq e1 _ h1 (ih2 h2)
  | match_ scrut arms _ ih_arms =>
    have ⟨hs, harms⟩ := hMatch scrut arms h
    simp only [wrapReturns, wrapReturns.wrapReturnsArms_eq]
    exact mkMatch scrut _ hs (fun pa hpa => by
      obtain ⟨⟨p, e⟩, hpe, rfl⟩ := List.mem_map.mp hpa
      exact ih_arms (p, e) hpe (harms (p, e) hpe))
  | _ => exact hcf _ h

theorem wrapReturns_preserves_noRefs (e : ImpExpr) (h : NoReferences e) :
    NoReferences (wrapReturns e) :=
  wrapReturns_preserves e h (fun _ => .cfContinue)
    (fun _ _ _ h => by cases h with | letBind h1 h2 => exact ⟨h1, h2⟩)
    (fun _ _ _ h => by cases h with | ifThenElse h1 h2 h3 => exact ⟨h1, h2, h3⟩)
    (fun _ _ h => by cases h with | seq h1 h2 => exact ⟨h1, h2⟩)
    (fun _ _ h => by cases h with | match_ hs ha => exact ⟨hs, ha⟩)
    (fun _ _ _ => .letBind) (fun _ _ _ => .ifThenElse)
    (fun _ _ => .seq) (fun _ _ => .match_)
    (fun _ _ h => by cases h with | typeAscription he => exact he)
    (fun _ _ => .typeAscription)

theorem wrapReturns_preserves_noMut (e : ImpExpr) (h : NoMutation e) :
    NoMutation (wrapReturns e) :=
  wrapReturns_preserves e h (fun _ => .cfContinue)
    (fun _ _ _ h => by cases h with | letBind h1 h2 => exact ⟨h1, h2⟩)
    (fun _ _ _ h => by cases h with | ifThenElse h1 h2 h3 => exact ⟨h1, h2, h3⟩)
    (fun _ _ h => by cases h with | seq h1 h2 => exact ⟨h1, h2⟩)
    (fun _ _ h => by cases h with | match_ hs ha => exact ⟨hs, ha⟩)
    (fun _ _ _ => .letBind) (fun _ _ _ => .ifThenElse)
    (fun _ _ => .seq) (fun _ _ => .match_)
    (fun _ _ h => by cases h with | typeAscription he => exact he)
    (fun _ _ => .typeAscription)

theorem wrapReturns_preserves_noLoops (e : ImpExpr) (h : NoLoops e) :
    NoLoops (wrapReturns e) :=
  wrapReturns_preserves e h (fun _ => .cfContinue)
    (fun _ _ _ h => by cases h with | letBind h1 h2 => exact ⟨h1, h2⟩)
    (fun _ _ _ h => by cases h with | ifThenElse h1 h2 h3 => exact ⟨h1, h2, h3⟩)
    (fun _ _ h => by cases h with | seq h1 h2 => exact ⟨h1, h2⟩)
    (fun _ _ h => by cases h with | match_ hs ha => exact ⟨hs, ha⟩)
    (fun _ _ _ => .letBind) (fun _ _ _ => .ifThenElse)
    (fun _ _ => .seq) (fun _ _ => .match_)
    (fun _ _ h => by cases h with | typeAscription he => exact he)
    (fun _ _ => .typeAscription)

theorem wrapReturns_preserves_noEarlyExit (e : ImpExpr) (h : NoEarlyExit e) :
    NoEarlyExit (wrapReturns e) :=
  wrapReturns_preserves e h (fun _ => .cfContinue)
    (fun _ _ _ h => by cases h with | letBind h1 h2 => exact ⟨h1, h2⟩)
    (fun _ _ _ h => by cases h with | ifThenElse h1 h2 h3 => exact ⟨h1, h2, h3⟩)
    (fun _ _ h => by cases h with | seq h1 h2 => exact ⟨h1, h2⟩)
    (fun _ _ h => by cases h with | match_ hs ha => exact ⟨hs, ha⟩)
    (fun _ _ _ => .letBind) (fun _ _ _ => .ifThenElse)
    (fun _ _ => .seq) (fun _ _ => .match_)
    (fun _ _ h => by cases h with | typeAscription he => exact he)
    (fun _ _ => .typeAscription)

/-! ## Feature Preservation: explicitMonadic -/

/-- `explicitMonadic` preserves `NoReferences`. -/
theorem explicitMonadic_preserves_noRefs (e : ImpExpr)
    (h : NoReferences e) : NoReferences (explicitMonadic e) := by
  induction e using ImpExpr.ind with
  | lit => exact .lit
  | var => exact .var
  | unitVal => exact .unitVal
  | letBind _ _ _ ih1 ih2 =>
    cases h with | letBind h1 h2 => exact .letBind (ih1 h1) (ih2 h2)
  | lam _ _ ih =>
    cases h with | lam h1 => exact .lam (ih h1)
  | app _ args ih =>
    cases h with | app hargs =>
    simp only [explicitMonadic, explicitMonadic.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (hargs b hb))
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [explicitMonadic, explicitMonadic.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (helems b hb))
  | proj _ _ ih => cases h with | proj he => exact .proj (ih he)
  | ifThenElse _ _ _ ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 =>
    exact .ifThenElse (ih1 h1) (ih2 h2) (ih3 h3)
  | match_ _ arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    simp only [explicitMonadic, explicitMonadic.mapArms_eq]
    exact .match_ (ih1 hs) (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb (harms (p, b) hpb))
  | seq _ _ ih1 ih2 => cases h with | seq h1 h2 => exact .seq (ih1 h1) (ih2 h2)
  | forFold _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFold h1 h2 h3 =>
    exact .forFold (ih1 h1) (ih2 h2) (wrapReturns_preserves_noRefs _ (ih3 h3))
  | whileFold _ _ ih1 ih2 =>
    cases h with | whileFold h1 h2 =>
    exact .whileFold (ih1 h1) (wrapReturns_preserves_noRefs _ (ih2 h2))
  | forFoldReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldReturn h1 h2 h3 =>
    exact .forFoldReturn (ih1 h1) (ih2 h2) (wrapReturns_preserves_noRefs _ (ih3 h3))
  | whileFoldReturn _ _ ih1 ih2 =>
    cases h with | whileFoldReturn h1 h2 =>
    exact .whileFoldReturn (ih1 h1) (wrapReturns_preserves_noRefs _ (ih2 h2))
  | forFoldRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRev h1 h2 h3 =>
    exact .forFoldRev (ih1 h1) (ih2 h2) (wrapReturns_preserves_noRefs _ (ih3 h3))
  | forFoldRevReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRevReturn h1 h2 h3 =>
    exact .forFoldRevReturn (ih1 h1) (ih2 h2) (wrapReturns_preserves_noRefs _ (ih3 h3))
  | cfBreak _ ih => cases h with | cfBreak he => exact .cfBreak (ih he)
  | cfContinue _ ih => cases h with | cfContinue he => exact .cfContinue (ih he)
  | cfBreakContinue _ ih => cases h with | cfBreakContinue he => exact .cfBreakContinue (ih he)
  | borrow => exact absurd h NoReferences.not_borrow
  | deref => exact absurd h NoReferences.not_deref
  | assign _ _ ih => cases h with | assign hrhs => exact .assign (ih hrhs)
  | forLoop _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoop h1 h2 h3 => exact .forLoop (ih1 h1) (ih2 h2) (ih3 h3)
  | forLoopRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoopRev h1 h2 h3 => exact .forLoopRev (ih1 h1) (ih2 h2) (ih3 h3)
  | whileLoop _ _ ih1 ih2 =>
    cases h with | whileLoop h1 h2 => exact .whileLoop (ih1 h1) (ih2 h2)
  | break_none => exact .break_none
  | break_some _ ih => cases h with | break_some he => exact .break_some (ih he)
  | continue_ => exact .continue_
  | earlyReturn _ ih => cases h with | earlyReturn he => exact .earlyReturn (ih he)
  | questionMark _ ih => cases h with | questionMark he => exact .questionMark (ih he)
  | typeAscription _ _ ih => cases h with | typeAscription he => exact .typeAscription (ih he)

/-- `explicitMonadic` preserves `NoMutation`. -/
theorem explicitMonadic_preserves_noMut (e : ImpExpr)
    (h : NoMutation e) : NoMutation (explicitMonadic e) := by
  induction e using ImpExpr.ind with
  | lit => exact .lit
  | var => exact .var
  | unitVal => exact .unitVal
  | letBind _ _ _ ih1 ih2 =>
    cases h with | letBind h1 h2 => exact .letBind (ih1 h1) (ih2 h2)
  | lam _ _ ih =>
    cases h with | lam h1 => exact .lam (ih h1)
  | app _ args ih =>
    cases h with | app hargs =>
    simp only [explicitMonadic, explicitMonadic.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (hargs b hb))
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [explicitMonadic, explicitMonadic.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (helems b hb))
  | proj _ _ ih => cases h with | proj he => exact .proj (ih he)
  | ifThenElse _ _ _ ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 =>
    exact .ifThenElse (ih1 h1) (ih2 h2) (ih3 h3)
  | match_ _ arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    simp only [explicitMonadic, explicitMonadic.mapArms_eq]
    exact .match_ (ih1 hs) (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb (harms (p, b) hpb))
  | seq _ _ ih1 ih2 => cases h with | seq h1 h2 => exact .seq (ih1 h1) (ih2 h2)
  | forFold _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFold h1 h2 h3 =>
    exact .forFold (ih1 h1) (ih2 h2) (wrapReturns_preserves_noMut _ (ih3 h3))
  | whileFold _ _ ih1 ih2 =>
    cases h with | whileFold h1 h2 =>
    exact .whileFold (ih1 h1) (wrapReturns_preserves_noMut _ (ih2 h2))
  | forFoldReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldReturn h1 h2 h3 =>
    exact .forFoldReturn (ih1 h1) (ih2 h2) (wrapReturns_preserves_noMut _ (ih3 h3))
  | whileFoldReturn _ _ ih1 ih2 =>
    cases h with | whileFoldReturn h1 h2 =>
    exact .whileFoldReturn (ih1 h1) (wrapReturns_preserves_noMut _ (ih2 h2))
  | forFoldRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRev h1 h2 h3 =>
    exact .forFoldRev (ih1 h1) (ih2 h2) (wrapReturns_preserves_noMut _ (ih3 h3))
  | forFoldRevReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRevReturn h1 h2 h3 =>
    exact .forFoldRevReturn (ih1 h1) (ih2 h2) (wrapReturns_preserves_noMut _ (ih3 h3))
  | cfBreak _ ih => cases h with | cfBreak he => exact .cfBreak (ih he)
  | cfContinue _ ih => cases h with | cfContinue he => exact .cfContinue (ih he)
  | cfBreakContinue _ ih => cases h with | cfBreakContinue he => exact .cfBreakContinue (ih he)
  | borrow _ ih => cases h with | borrow he => exact .borrow (ih he)
  | deref _ ih => cases h with | deref he => exact .deref (ih he)
  | assign => exact absurd h NoMutation.not_assign
  | forLoop _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoop h1 h2 h3 => exact .forLoop (ih1 h1) (ih2 h2) (ih3 h3)
  | forLoopRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoopRev h1 h2 h3 => exact .forLoopRev (ih1 h1) (ih2 h2) (ih3 h3)
  | whileLoop _ _ ih1 ih2 =>
    cases h with | whileLoop h1 h2 => exact .whileLoop (ih1 h1) (ih2 h2)
  | break_none => exact .break_none
  | break_some _ ih => cases h with | break_some he => exact .break_some (ih he)
  | continue_ => exact .continue_
  | earlyReturn _ ih => cases h with | earlyReturn he => exact .earlyReturn (ih he)
  | questionMark _ ih => cases h with | questionMark he => exact .questionMark (ih he)
  | typeAscription _ _ ih => cases h with | typeAscription he => exact .typeAscription (ih he)

/-- `explicitMonadic` preserves `NoLoops`. -/
theorem explicitMonadic_preserves_noLoops (e : ImpExpr)
    (h : NoLoops e) : NoLoops (explicitMonadic e) := by
  induction e using ImpExpr.ind with
  | lit => exact .lit
  | var => exact .var
  | unitVal => exact .unitVal
  | letBind _ _ _ ih1 ih2 =>
    cases h with | letBind h1 h2 => exact .letBind (ih1 h1) (ih2 h2)
  | lam _ _ ih =>
    cases h with | lam h1 => exact .lam (ih h1)
  | app _ args ih =>
    cases h with | app hargs =>
    simp only [explicitMonadic, explicitMonadic.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (hargs b hb))
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [explicitMonadic, explicitMonadic.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (helems b hb))
  | proj _ _ ih => cases h with | proj he => exact .proj (ih he)
  | ifThenElse _ _ _ ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 =>
    exact .ifThenElse (ih1 h1) (ih2 h2) (ih3 h3)
  | match_ _ arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    simp only [explicitMonadic, explicitMonadic.mapArms_eq]
    exact .match_ (ih1 hs) (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb (harms (p, b) hpb))
  | seq _ _ ih1 ih2 => cases h with | seq h1 h2 => exact .seq (ih1 h1) (ih2 h2)
  | forFold _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFold h1 h2 h3 =>
    exact .forFold (ih1 h1) (ih2 h2) (wrapReturns_preserves_noLoops _ (ih3 h3))
  | whileFold _ _ ih1 ih2 =>
    cases h with | whileFold h1 h2 =>
    exact .whileFold (ih1 h1) (wrapReturns_preserves_noLoops _ (ih2 h2))
  | forFoldReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldReturn h1 h2 h3 =>
    exact .forFoldReturn (ih1 h1) (ih2 h2) (wrapReturns_preserves_noLoops _ (ih3 h3))
  | whileFoldReturn _ _ ih1 ih2 =>
    cases h with | whileFoldReturn h1 h2 =>
    exact .whileFoldReturn (ih1 h1) (wrapReturns_preserves_noLoops _ (ih2 h2))
  | forFoldRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRev h1 h2 h3 =>
    exact .forFoldRev (ih1 h1) (ih2 h2) (wrapReturns_preserves_noLoops _ (ih3 h3))
  | forFoldRevReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRevReturn h1 h2 h3 =>
    exact .forFoldRevReturn (ih1 h1) (ih2 h2) (wrapReturns_preserves_noLoops _ (ih3 h3))
  | cfBreak _ ih => cases h with | cfBreak he => exact .cfBreak (ih he)
  | cfContinue _ ih => cases h with | cfContinue he => exact .cfContinue (ih he)
  | cfBreakContinue _ ih => cases h with | cfBreakContinue he => exact .cfBreakContinue (ih he)
  | borrow _ ih => cases h with | borrow he => exact .borrow (ih he)
  | deref _ ih => cases h with | deref he => exact .deref (ih he)
  | assign _ _ ih => cases h with | assign hrhs => exact .assign (ih hrhs)
  | forLoop => exact absurd h NoLoops.not_forLoop
  | forLoopRev => exact absurd h NoLoops.not_forLoopRev
  | whileLoop => exact absurd h NoLoops.not_whileLoop
  | break_none => exact absurd h NoLoops.not_break
  | break_some => exact absurd h NoLoops.not_break
  | continue_ => exact absurd h NoLoops.not_continue
  | earlyReturn _ ih => cases h with | earlyReturn he => exact .earlyReturn (ih he)
  | questionMark _ ih => cases h with | questionMark he => exact .questionMark (ih he)
  | typeAscription _ _ ih => cases h with | typeAscription he => exact .typeAscription (ih he)

/-- `explicitMonadic` preserves `NoEarlyExit`. -/
theorem explicitMonadic_preserves_noEarlyExit (e : ImpExpr)
    (h : NoEarlyExit e) : NoEarlyExit (explicitMonadic e) := by
  induction e using ImpExpr.ind with
  | lit => exact .lit
  | var => exact .var
  | unitVal => exact .unitVal
  | letBind _ _ _ ih1 ih2 =>
    cases h with | letBind h1 h2 => exact .letBind (ih1 h1) (ih2 h2)
  | lam _ _ ih =>
    cases h with | lam h1 => exact .lam (ih h1)
  | app _ args ih =>
    cases h with | app hargs =>
    simp only [explicitMonadic, explicitMonadic.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (hargs b hb))
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [explicitMonadic, explicitMonadic.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (helems b hb))
  | proj _ _ ih => cases h with | proj he => exact .proj (ih he)
  | ifThenElse _ _ _ ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 =>
    exact .ifThenElse (ih1 h1) (ih2 h2) (ih3 h3)
  | match_ _ arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    simp only [explicitMonadic, explicitMonadic.mapArms_eq]
    exact .match_ (ih1 hs) (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb (harms (p, b) hpb))
  | seq _ _ ih1 ih2 => cases h with | seq h1 h2 => exact .seq (ih1 h1) (ih2 h2)
  | forFold _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFold h1 h2 h3 =>
    exact .forFold (ih1 h1) (ih2 h2) (wrapReturns_preserves_noEarlyExit _ (ih3 h3))
  | whileFold _ _ ih1 ih2 =>
    cases h with | whileFold h1 h2 =>
    exact .whileFold (ih1 h1) (wrapReturns_preserves_noEarlyExit _ (ih2 h2))
  | forFoldReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldReturn h1 h2 h3 =>
    exact .forFoldReturn (ih1 h1) (ih2 h2) (wrapReturns_preserves_noEarlyExit _ (ih3 h3))
  | whileFoldReturn _ _ ih1 ih2 =>
    cases h with | whileFoldReturn h1 h2 =>
    exact .whileFoldReturn (ih1 h1) (wrapReturns_preserves_noEarlyExit _ (ih2 h2))
  | forFoldRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRev h1 h2 h3 =>
    exact .forFoldRev (ih1 h1) (ih2 h2) (wrapReturns_preserves_noEarlyExit _ (ih3 h3))
  | forFoldRevReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRevReturn h1 h2 h3 =>
    exact .forFoldRevReturn (ih1 h1) (ih2 h2) (wrapReturns_preserves_noEarlyExit _ (ih3 h3))
  | cfBreak _ ih => cases h with | cfBreak he => exact .cfBreak (ih he)
  | cfContinue _ ih => cases h with | cfContinue he => exact .cfContinue (ih he)
  | cfBreakContinue _ ih => cases h with | cfBreakContinue he => exact .cfBreakContinue (ih he)
  | borrow _ ih => cases h with | borrow he => exact .borrow (ih he)
  | deref _ ih => cases h with | deref he => exact .deref (ih he)
  | assign _ _ ih => cases h with | assign hrhs => exact .assign (ih hrhs)
  | forLoop _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoop h1 h2 h3 => exact .forLoop (ih1 h1) (ih2 h2) (ih3 h3)
  | forLoopRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoopRev h1 h2 h3 => exact .forLoopRev (ih1 h1) (ih2 h2) (ih3 h3)
  | whileLoop _ _ ih1 ih2 =>
    cases h with | whileLoop h1 h2 => exact .whileLoop (ih1 h1) (ih2 h2)
  | break_none => exact .break_none
  | break_some _ ih => cases h with | break_some he => exact .break_some (ih he)
  | continue_ => exact .continue_
  | earlyReturn => exact absurd h NoEarlyExit.not_earlyReturn
  | questionMark => exact absurd h NoEarlyExit.not_questionMark
  | typeAscription _ _ ih => cases h with | typeAscription he => exact .typeAscription (ih he)

end Hax
