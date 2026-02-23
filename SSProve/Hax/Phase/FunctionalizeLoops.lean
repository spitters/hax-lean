/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.AST
import SSProve.Hax.Value
import SSProve.Hax.Features
import SSProve.Hax.Semantics

/-!
# Phase 3: Functionalize Loops

Convert loops to fold/unfold patterns.

## Main definitions

* `functionalizeLoops` — the transformation
* `functionalizeLoops_noLoops` — output guarantee: `NoLoops`
* `functionalizeLoops_preserves_noRefs` — preservation: `NoReferences`
* `functionalizeLoops_preserves_noMut` — preservation: `NoMutation`
-/

namespace SSProve.Hax

/-- Convert loops to functional fold patterns. -/
def functionalizeLoops : ImpExpr → ImpExpr
  | .lit v => .lit v
  | .var n => .var n
  | .letBind n val body =>
    .letBind n (functionalizeLoops val) (functionalizeLoops body)
  | .app f args => .app f (mapExpr args)
  | .tuple elems => .tuple (mapExpr elems)
  | .proj e i => .proj (functionalizeLoops e) i
  | .ifThenElse c t e =>
    .ifThenElse (functionalizeLoops c) (functionalizeLoops t) (functionalizeLoops e)
  | .match_ scrut arms =>
    .match_ (functionalizeLoops scrut) (mapArms arms)
  | .unitVal => .unitVal
  | .seq e1 e2 => .seq (functionalizeLoops e1) (functionalizeLoops e2)
  | .borrow e => .borrow (functionalizeLoops e)
  | .deref e => .deref (functionalizeLoops e)
  | .assign n rhs => .assign n (functionalizeLoops rhs)
  | .forLoop v lo hi body =>
    .app "for_fold" [.var v, functionalizeLoops lo, functionalizeLoops hi,
      functionalizeLoops body]
  | .whileLoop cond body =>
    .app "while_fold" [functionalizeLoops cond, functionalizeLoops body]
  | .break_ (some e) =>
    .app "ControlFlow.Break" [functionalizeLoops e]
  | .break_ none =>
    .app "ControlFlow.Break" [.unitVal]
  | .continue_ =>
    .app "ControlFlow.Continue" [.unitVal]
  | .earlyReturn e => .earlyReturn (functionalizeLoops e)
  | .questionMark e => .questionMark (functionalizeLoops e)
where
  mapExpr : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => functionalizeLoops e :: mapExpr es
  mapArms : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, functionalizeLoops e) :: mapArms rest

@[simp] theorem functionalizeLoops.mapExpr_eq (es : List ImpExpr) :
    functionalizeLoops.mapExpr es = es.map functionalizeLoops := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [functionalizeLoops.mapExpr, ih]

@[simp] theorem functionalizeLoops.mapArms_eq (arms : List (ImpPat × ImpExpr)) :
    functionalizeLoops.mapArms arms = arms.map fun (p, e) => (p, functionalizeLoops e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [functionalizeLoops.mapArms, ih]

/-- `functionalizeLoops` produces an expression with no loop nodes. -/
theorem functionalizeLoops_noLoops (e : ImpExpr) :
    NoLoops (functionalizeLoops e) := by
  induction e using ImpExpr.ind with
  | lit => exact .lit
  | var => exact .var
  | letBind _ _ _ ih1 ih2 => exact .letBind ih1 ih2
  | app _ args ih =>
    simp only [functionalizeLoops, functionalizeLoops.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb)
  | tuple elems ih =>
    simp only [functionalizeLoops, functionalizeLoops.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb)
  | proj _ _ ih => exact .proj ih
  | ifThenElse _ _ _ ih1 ih2 ih3 => exact .ifThenElse ih1 ih2 ih3
  | match_ _ arms ih1 ih2 =>
    simp only [functionalizeLoops, functionalizeLoops.mapArms_eq]
    exact .match_ ih1 (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb)
  | unitVal => exact .unitVal
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | borrow _ ih => exact .borrow ih
  | deref _ ih => exact .deref ih
  | assign _ _ ih => exact .assign ih
  | forLoop v lo hi body ih1 ih2 ih3 =>
    exact .app (fun a ha => by
      simp at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact .var
      · exact ih1
      · exact ih2
      · exact ih3)
  | whileLoop c body ih1 ih2 =>
    exact .app (fun a ha => by
      simp at ha
      rcases ha with rfl | rfl
      · exact ih1
      · exact ih2)
  | break_none =>
    exact .app (fun a ha => by simp at ha; subst ha; exact .unitVal)
  | break_some _ ih =>
    exact .app (fun a ha => by simp at ha; subst ha; exact ih)
  | continue_ =>
    exact .app (fun a ha => by simp at ha; subst ha; exact .unitVal)
  | earlyReturn _ ih => exact .earlyReturn ih
  | questionMark _ ih => exact .questionMark ih

/-- `functionalizeLoops` preserves `NoReferences`. -/
theorem functionalizeLoops_preserves_noRefs (e : ImpExpr)
    (h : NoReferences e) : NoReferences (functionalizeLoops e) := by
  induction e using ImpExpr.ind with
  | lit => exact .lit
  | var => exact .var
  | letBind _ _ _ ih1 ih2 => cases h with | letBind h1 h2 => exact .letBind (ih1 h1) (ih2 h2)
  | app _ args ih =>
    cases h with | app hargs =>
    simp only [functionalizeLoops, functionalizeLoops.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (hargs b hb))
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [functionalizeLoops, functionalizeLoops.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (helems b hb))
  | proj _ _ ih => cases h with | proj he => exact .proj (ih he)
  | ifThenElse _ _ _ ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 => exact .ifThenElse (ih1 h1) (ih2 h2) (ih3 h3)
  | match_ _ arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    simp only [functionalizeLoops, functionalizeLoops.mapArms_eq]
    exact .match_ (ih1 hs) (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb (harms (p, b) hpb))
  | unitVal => exact .unitVal
  | seq _ _ ih1 ih2 => cases h with | seq h1 h2 => exact .seq (ih1 h1) (ih2 h2)
  | borrow => exact absurd h NoReferences.not_borrow
  | deref => exact absurd h NoReferences.not_deref
  | assign _ _ ih => cases h with | assign hrhs => exact .assign (ih hrhs)
  | forLoop _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoop h1 h2 h3 =>
    exact .app (fun a ha => by
      simp at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact .var
      · exact ih1 h1
      · exact ih2 h2
      · exact ih3 h3)
  | whileLoop _ _ ih1 ih2 =>
    cases h with | whileLoop h1 h2 =>
    exact .app (fun a ha => by
      simp at ha
      rcases ha with rfl | rfl
      · exact ih1 h1
      · exact ih2 h2)
  | break_none => exact .app (fun a ha => by
      simp at ha; subst ha; exact .unitVal)
  | break_some _ ih =>
    cases h with | break_some he =>
    exact .app (fun a ha => by
      simp at ha; subst ha; exact ih he)
  | continue_ => exact .app (fun a ha => by
      simp at ha; subst ha; exact .unitVal)
  | earlyReturn _ ih => cases h with | earlyReturn he => exact .earlyReturn (ih he)
  | questionMark _ ih => cases h with | questionMark he => exact .questionMark (ih he)

/-- `functionalizeLoops` preserves `NoMutation`. -/
theorem functionalizeLoops_preserves_noMut (e : ImpExpr)
    (h : NoMutation e) : NoMutation (functionalizeLoops e) := by
  induction e using ImpExpr.ind with
  | lit => exact .lit
  | var => exact .var
  | letBind _ _ _ ih1 ih2 => cases h with | letBind h1 h2 => exact .letBind (ih1 h1) (ih2 h2)
  | app _ args ih =>
    cases h with | app hargs =>
    simp only [functionalizeLoops, functionalizeLoops.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (hargs b hb))
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [functionalizeLoops, functionalizeLoops.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (helems b hb))
  | proj _ _ ih => cases h with | proj he => exact .proj (ih he)
  | ifThenElse _ _ _ ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 => exact .ifThenElse (ih1 h1) (ih2 h2) (ih3 h3)
  | match_ _ arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    simp only [functionalizeLoops, functionalizeLoops.mapArms_eq]
    exact .match_ (ih1 hs) (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb (harms (p, b) hpb))
  | unitVal => exact .unitVal
  | seq _ _ ih1 ih2 => cases h with | seq h1 h2 => exact .seq (ih1 h1) (ih2 h2)
  | borrow _ ih => cases h with | borrow he => exact .borrow (ih he)
  | deref _ ih => cases h with | deref he => exact .deref (ih he)
  | assign => exact absurd h NoMutation.not_assign
  | forLoop _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoop h1 h2 h3 =>
    exact .app (fun a ha => by
      simp at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact .var
      · exact ih1 h1
      · exact ih2 h2
      · exact ih3 h3)
  | whileLoop _ _ ih1 ih2 =>
    cases h with | whileLoop h1 h2 =>
    exact .app (fun a ha => by
      simp at ha
      rcases ha with rfl | rfl
      · exact ih1 h1
      · exact ih2 h2)
  | break_none => exact .app (fun a ha => by
      simp at ha; subst ha; exact .unitVal)
  | break_some _ ih =>
    cases h with | break_some he =>
    exact .app (fun a ha => by
      simp at ha; subst ha; exact ih he)
  | continue_ => exact .app (fun a ha => by
      simp at ha; subst ha; exact .unitVal)
  | earlyReturn _ ih => cases h with | earlyReturn he => exact .earlyReturn (ih he)
  | questionMark _ ih => cases h with | questionMark he => exact .questionMark (ih he)

/-- On loop-free inputs, `functionalizeLoops` is the identity.

    For inputs with loops, the transform rewrites them into `app` calls
    (e.g. `for_fold`, `while_fold`), which changes the `denote` semantics
    unless appropriate builtins are provided. -/
theorem functionalizeLoops_correct (e : ImpExpr) (h : NoLoops e) :
    functionalizeLoops e = e := by
  induction e using ImpExpr.ind with
  | lit | var | unitVal => rfl
  | letBind n val body ih1 ih2 =>
    cases h with | letBind h1 h2 =>
    simp only [functionalizeLoops, ih1 h1, ih2 h2]
  | seq e1 e2 ih1 ih2 =>
    cases h with | seq h1 h2 =>
    simp only [functionalizeLoops, ih1 h1, ih2 h2]
  | proj e i ih =>
    cases h with | proj he =>
    simp only [functionalizeLoops, ih he]
  | ifThenElse c t e ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 =>
    simp only [functionalizeLoops, ih1 h1, ih2 h2, ih3 h3]
  | borrow e ih =>
    cases h with | borrow he =>
    simp only [functionalizeLoops, ih he]
  | deref e ih =>
    cases h with | deref he =>
    simp only [functionalizeLoops, ih he]
  | assign n rhs ih =>
    cases h with | assign hrhs =>
    simp only [functionalizeLoops, ih hrhs]
  | earlyReturn e ih =>
    cases h with | earlyReturn he =>
    simp only [functionalizeLoops, ih he]
  | questionMark e ih =>
    cases h with | questionMark he =>
    simp only [functionalizeLoops, ih he]
  | app f args ih =>
    cases h with | app hargs =>
    simp only [functionalizeLoops, functionalizeLoops.mapExpr_eq]
    congr 1
    conv => rhs; rw [← List.map_id args]
    exact List.map_congr_left (fun a ha => ih a ha (hargs a ha))
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [functionalizeLoops, functionalizeLoops.mapExpr_eq]
    congr 1
    conv => rhs; rw [← List.map_id elems]
    exact List.map_congr_left (fun a ha => ih a ha (helems a ha))
  | match_ scrut arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    simp only [functionalizeLoops, functionalizeLoops.mapArms_eq, ih1 hs]
    congr 1
    conv => rhs; rw [← List.map_id arms]
    exact List.map_congr_left (fun pa hpa =>
      Prod.ext rfl (ih2 pa hpa (harms pa hpa)))
  | forLoop => exact absurd h NoLoops.not_forLoop
  | whileLoop => exact absurd h NoLoops.not_whileLoop
  | break_none => exact absurd h NoLoops.not_break
  | break_some => exact absurd h NoLoops.not_break
  | continue_ => exact absurd h NoLoops.not_continue

end SSProve.Hax
