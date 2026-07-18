/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import HaxLean.AST
import HaxLean.Value
import HaxLean.Features
import HaxLean.FreeVars
import HaxLean.Semantics

/-!
# Phase 2: Local Mutation Elimination

Transform mutable assignments into pure let-rebindings.

## Main definitions

* `localMutation` — the transformation
* `localMutation_noMut` — output guarantee: `NoMutation`
* `localMutation_preserves_noRefs` — preservation: `NoReferences`
* `localMutation_correct` — semantics preservation under `denote`

## Design

The key transformation is:

    assign n rhs  ↦  seq (letBind n rhs (var n)) unitVal

This works because the denotational semantics uses an `Env` (variable store)
threaded as `StateM Env`. Under `denote`:

* `assign n rhs`: evaluate `rhs` to value `v`, update env with `n ↦ v`, return `unit`
* `seq (letBind n rhs (var n)) unitVal`: evaluate `rhs` to `v`, extend env with
  `n ↦ v`, look up `n` (getting `v` back), then discard and return `unit`

Both produce the same env update and return `unit`. The `denote_assign_eq`
theorem proves this formally. The full `localMutation_correct` theorem
then lifts this to all expressions by structural induction.

Note: `localMutation` takes a `mvars` parameter (list of mutated variables)
for forward compatibility with more sophisticated state-passing transforms,
but the current implementation does not use it — it transforms all `assign`
nodes unconditionally.
-/

namespace Hax

/-- Transform mutable assignments into let-rebindings. -/
def localMutation (mvars : List String) : ImpExpr → ImpExpr
  | .lit v => .lit v
  | .var n => .var n
  | .letBind n val body =>
    .letBind n (localMutation mvars val) (localMutation mvars body)
  | .lam ps body => .lam ps (localMutation mvars body)
  | .app f args => .app f (mapExpr mvars args)
  | .tuple elems => .tuple (mapExpr mvars elems)
  | .proj e i => .proj (localMutation mvars e) i
  | .ifThenElse c t e =>
    .ifThenElse (localMutation mvars c) (localMutation mvars t) (localMutation mvars e)
  | .match_ scrut arms =>
    .match_ (localMutation mvars scrut) (mapArms mvars arms)
  | .unitVal => .unitVal
  | .seq e1 e2 => .seq (localMutation mvars e1) (localMutation mvars e2)
  | .borrow e => .borrow (localMutation mvars e)
  | .deref e => .deref (localMutation mvars e)
  | .assign n rhs =>
    .seq (.letBind n (localMutation mvars rhs) (.var n)) .unitVal
  | .forLoop v lo hi body =>
    .forLoop v (localMutation mvars lo) (localMutation mvars hi) (localMutation mvars body)
  | .forLoopRev v lo hi body =>
    .forLoopRev v (localMutation mvars lo) (localMutation mvars hi) (localMutation mvars body)
  | .whileLoop c body =>
    .whileLoop (localMutation mvars c) (localMutation mvars body)
  | .break_ (some e) => .break_ (some (localMutation mvars e))
  | .break_ none => .break_ none
  | .continue_ => .continue_
  | .earlyReturn e => .earlyReturn (localMutation mvars e)
  | .questionMark e => .questionMark (localMutation mvars e)
  | .forFold v lo hi body =>
    .forFold v (localMutation mvars lo) (localMutation mvars hi) (localMutation mvars body)
  | .whileFold c body =>
    .whileFold (localMutation mvars c) (localMutation mvars body)
  | .forFoldReturn v lo hi body =>
    .forFoldReturn v (localMutation mvars lo) (localMutation mvars hi) (localMutation mvars body)
  | .whileFoldReturn c body =>
    .whileFoldReturn (localMutation mvars c) (localMutation mvars body)
  | .forFoldRev v lo hi body =>
    .forFoldRev v (localMutation mvars lo) (localMutation mvars hi) (localMutation mvars body)
  | .forFoldRevReturn v lo hi body =>
    .forFoldRevReturn v (localMutation mvars lo) (localMutation mvars hi) (localMutation mvars body)
  | .cfBreak e => .cfBreak (localMutation mvars e)
  | .cfContinue e => .cfContinue (localMutation mvars e)
  | .cfBreakContinue e => .cfBreakContinue (localMutation mvars e)
  | .typeAscription e ty => .typeAscription (localMutation mvars e) ty
where
  mapExpr (mvars : List String) : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => localMutation mvars e :: mapExpr mvars es
  mapArms (mvars : List String) : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, localMutation mvars e) :: mapArms mvars rest

@[simp] theorem localMutation.mapExpr_eq (mvars : List String) (es : List ImpExpr) :
    localMutation.mapExpr mvars es = es.map (localMutation mvars) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [localMutation.mapExpr, ih]

@[simp] theorem localMutation.mapArms_eq (mvars : List String) (arms : List (ImpPat × ImpExpr)) :
    localMutation.mapArms mvars arms = arms.map fun (p, e) => (p, localMutation mvars e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [localMutation.mapArms, ih]

/-- `localMutation` produces an expression with no `assign` nodes. -/
theorem localMutation_noMut (mvars : List String) (e : ImpExpr) :
    NoMutation (localMutation mvars e) := by
  induction e using ImpExpr.ind with
  | lit => exact .lit
  | var => exact .var
  | letBind _ _ _ ih1 ih2 => exact .letBind ih1 ih2
  | lam _ _ ih => exact .lam ih
  | app _ args ih =>
    simp only [localMutation, localMutation.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb)
  | tuple elems ih =>
    simp only [localMutation, localMutation.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb)
  | proj _ _ ih => exact .proj ih
  | ifThenElse _ _ _ ih1 ih2 ih3 => exact .ifThenElse ih1 ih2 ih3
  | match_ _ arms ih1 ih2 =>
    simp only [localMutation, localMutation.mapArms_eq]
    exact .match_ ih1 (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb)
  | unitVal => exact .unitVal
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | borrow _ ih => exact .borrow ih
  | deref _ ih => exact .deref ih
  | assign _ _ ih => exact .seq (.letBind ih .var) .unitVal
  | forLoop _ _ _ _ ih1 ih2 ih3 => exact .forLoop ih1 ih2 ih3
  | forLoopRev _ _ _ _ ih1 ih2 ih3 => exact .forLoopRev ih1 ih2 ih3
  | whileLoop _ _ ih1 ih2 => exact .whileLoop ih1 ih2
  | break_none => exact .break_none
  | break_some _ ih => exact .break_some ih
  | continue_ => exact .continue_
  | earlyReturn _ ih => exact .earlyReturn ih
  | questionMark _ ih => exact .questionMark ih
  | forFold _ _ _ _ ih1 ih2 ih3 => exact .forFold ih1 ih2 ih3
  | whileFold _ _ ih1 ih2 => exact .whileFold ih1 ih2
  | forFoldReturn _ _ _ _ ih1 ih2 ih3 => exact .forFoldReturn ih1 ih2 ih3
  | whileFoldReturn _ _ ih1 ih2 => exact .whileFoldReturn ih1 ih2
  | forFoldRev _ _ _ _ ih1 ih2 ih3 => exact .forFoldRev ih1 ih2 ih3
  | forFoldRevReturn _ _ _ _ ih1 ih2 ih3 => exact .forFoldRevReturn ih1 ih2 ih3
  | cfBreak _ ih => exact .cfBreak ih
  | cfContinue _ ih => exact .cfContinue ih
  | cfBreakContinue _ ih => exact .cfBreakContinue ih
  | typeAscription _ _ ih => exact .typeAscription ih

/-- `localMutation` preserves `NoReferences`. -/
theorem localMutation_preserves_noRefs (mvars : List String) (e : ImpExpr)
    (h : NoReferences e) : NoReferences (localMutation mvars e) := by
  induction e using ImpExpr.ind with
  | lit => exact .lit
  | var => exact .var
  | letBind _ _ _ ih1 ih2 => cases h with | letBind h1 h2 => exact .letBind (ih1 h1) (ih2 h2)
  | lam _ _ ih => cases h with | lam h1 => exact .lam (ih h1)
  | app _ args ih =>
    cases h with | app hargs =>
    simp only [localMutation, localMutation.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (hargs b hb))
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [localMutation, localMutation.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (helems b hb))
  | proj _ _ ih => cases h with | proj he => exact .proj (ih he)
  | ifThenElse _ _ _ ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 => exact .ifThenElse (ih1 h1) (ih2 h2) (ih3 h3)
  | match_ _ arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    simp only [localMutation, localMutation.mapArms_eq]
    exact .match_ (ih1 hs) (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb (harms (p, b) hpb))
  | unitVal => exact .unitVal
  | seq _ _ ih1 ih2 => cases h with | seq h1 h2 => exact .seq (ih1 h1) (ih2 h2)
  | borrow => exact absurd h NoReferences.not_borrow
  | deref => exact absurd h NoReferences.not_deref
  | assign _ _ ih =>
    cases h with | assign hrhs =>
    exact .seq (.letBind (ih hrhs) .var) .unitVal
  | forLoop _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoop h1 h2 h3 => exact .forLoop (ih1 h1) (ih2 h2) (ih3 h3)
  | forLoopRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoopRev h1 h2 h3 => exact .forLoopRev (ih1 h1) (ih2 h2) (ih3 h3)
  | whileLoop _ _ ih1 ih2 => cases h with | whileLoop h1 h2 => exact .whileLoop (ih1 h1) (ih2 h2)
  | break_none => exact .break_none
  | break_some _ ih =>
    cases h with | break_some he => exact .break_some (ih he)
  | continue_ => exact .continue_
  | earlyReturn _ ih => cases h with | earlyReturn he => exact .earlyReturn (ih he)
  | questionMark _ ih => cases h with | questionMark he => exact .questionMark (ih he)
  | forFold _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFold h1 h2 h3 => exact .forFold (ih1 h1) (ih2 h2) (ih3 h3)
  | whileFold _ _ ih1 ih2 =>
    cases h with | whileFold h1 h2 => exact .whileFold (ih1 h1) (ih2 h2)
  | forFoldReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldReturn h1 h2 h3 => exact .forFoldReturn (ih1 h1) (ih2 h2) (ih3 h3)
  | whileFoldReturn _ _ ih1 ih2 =>
    cases h with | whileFoldReturn h1 h2 => exact .whileFoldReturn (ih1 h1) (ih2 h2)
  | forFoldRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRev h1 h2 h3 => exact .forFoldRev (ih1 h1) (ih2 h2) (ih3 h3)
  | forFoldRevReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRevReturn h1 h2 h3 => exact .forFoldRevReturn (ih1 h1) (ih2 h2) (ih3 h3)
  | cfBreak _ ih => cases h with | cfBreak he => exact .cfBreak (ih he)
  | cfContinue _ ih => cases h with | cfContinue he => exact .cfContinue (ih he)
  | cfBreakContinue _ ih => cases h with | cfBreakContinue he => exact .cfBreakContinue (ih he)
  | typeAscription _ _ ih => cases h with | typeAscription he => exact .typeAscription (ih he)

/-- The `assign n rhs` ↦ `seq (letBind n rhs (var n)) unitVal` transformation
    preserves denotational semantics. -/
private theorem denote_assign_eq (bi : Builtins) (fuel : Nat) (n : String) (rhs : ImpExpr) :
    denote bi fuel (.seq (.letBind n rhs (.var n)) .unitVal) =
    denote bi fuel (.assign n rhs) := by
  funext env
  simp only [denote, bind, StateT.bind, modify, modifyGet,
    MonadStateOf.modifyGet, get, getThe, MonadStateOf.get]
  generalize denote bi fuel rhs env = p
  obtain ⟨outcome, env'⟩ := p
  cases outcome with
  | val v =>
    simp only [StateT.bind, Bind.bind, Pure.pure, StateT.pure,
      StateT.modifyGet, StateT.get, Env.extend_same]
  | err msg => rfl
  | earlyRet v => rfl
  | broke v => rfl
  | continued => rfl

/-- Semantics preservation for localMutation. -/
theorem localMutation_correct (bi : Builtins) (fuel : Nat)
    (mvars : List String) (e : ImpExpr) :
    denote bi fuel (localMutation mvars e) = denote bi fuel e := by
  revert fuel
  induction e using ImpExpr.ind with
  | lit | var | unitVal | continue_ | break_none => intro fuel; rfl
  | borrow e ih =>
    intro fuel
    simp only [localMutation]
    unfold denote
    exact ih fuel
  | deref e ih =>
    intro fuel
    simp only [localMutation]
    unfold denote
    exact ih fuel
  | lam _ _ _ => intro fuel; simp only [localMutation, denote]
  | letBind n val body ih1 ih2 =>
    intro fuel
    simp only [localMutation]
    unfold denote
    rw [ih1 fuel]; congr 1; funext rv; split
    · congr 1; funext _; exact ih2 fuel
    · rfl
  | seq e1 e2 ih1 ih2 =>
    intro fuel
    simp only [localMutation]
    unfold denote
    rw [ih1 fuel]; congr 1; funext r1; split
    · exact ih2 fuel
    · rfl
  | proj e i ih =>
    intro fuel
    simp only [localMutation]
    unfold denote
    rw [ih fuel]
  | ifThenElse c t e ih1 ih2 ih3 =>
    intro fuel
    simp only [localMutation]
    unfold denote
    rw [ih1 fuel]; congr 1; funext rc; split
    · exact ih2 fuel
    · exact ih3 fuel
    · rfl
    · rfl
  | assign n rhs ih =>
    intro fuel
    simp only [localMutation]
    rw [denote_assign_eq]
    unfold denote
    rw [ih fuel]
  | earlyReturn e ih =>
    intro fuel
    simp only [localMutation]
    unfold denote
    rw [ih fuel]
  | questionMark e ih =>
    intro fuel
    simp only [localMutation]
    unfold denote
    rw [ih fuel]
  | break_some e ih =>
    intro fuel
    simp only [localMutation]
    unfold denote
    rw [ih fuel]
  | app f args ih =>
    intro fuel
    simp only [localMutation, localMutation.mapExpr_eq]
    unfold denote
    rw [denoteArgs_map_congr bi fuel (localMutation mvars) args (fun e he => ih e he fuel)]
  | tuple elems ih =>
    intro fuel
    simp only [localMutation, localMutation.mapExpr_eq]
    unfold denote
    rw [denoteArgs_map_congr bi fuel (localMutation mvars) elems (fun e he => ih e he fuel)]
  | match_ scrut arms ih1 ih2 =>
    intro fuel
    simp only [localMutation, localMutation.mapArms_eq]
    unfold denote
    rw [ih1 fuel]; congr 1; funext rs; split
    · exact denoteMatchArms_map_congr bi fuel (localMutation mvars) _ arms
        (fun pa hpa => ih2 pa hpa fuel)
    · rfl
  | forLoop v lo hi body ih1 ih2 ih3 =>
    intro fuel
    simp only [localMutation]
    unfold denote
    rw [ih1 fuel, ih2 fuel]; congr 1; funext rlo; congr 1; funext rhi
    split
    · exact denoteForLoop_congr bi fuel v _ _ body (localMutation mvars body) ih3
    · rfl
    · rfl
  | forLoopRev v lo hi body ih1 ih2 ih3 =>
    intro fuel
    simp only [localMutation]
    unfold denote
    rw [ih1 fuel, ih2 fuel]; congr 1; funext rlo; congr 1; funext rhi
    split
    · exact denoteForLoopRev_congr bi fuel v _ _ body (localMutation mvars body) ih3
    · rfl
    · rfl
  | whileLoop c body ih1 ih2 =>
    intro fuel
    simp only [localMutation]
    unfold denote
    exact denoteWhile_congr bi fuel c (localMutation mvars c) body (localMutation mvars body) ih1 ih2
  -- Phase 3/4 output constructors: denote returns error for all
  | forFold _ _ _ _ ih1 ih2 ih3 => intro fuel; simp [localMutation, denote]
  | whileFold _ _ ih1 ih2 => intro fuel; simp [localMutation, denote]
  | forFoldReturn _ _ _ _ ih1 ih2 ih3 => intro fuel; simp [localMutation, denote]
  | whileFoldReturn _ _ ih1 ih2 => intro fuel; simp [localMutation, denote]
  | forFoldRev _ _ _ _ ih1 ih2 ih3 => intro fuel; simp [localMutation, denote]
  | forFoldRevReturn _ _ _ _ ih1 ih2 ih3 => intro fuel; simp [localMutation, denote]
  | cfBreak _ ih => intro fuel; simp [localMutation, denote]
  | cfContinue _ ih => intro fuel; simp [localMutation, denote]
  | cfBreakContinue _ ih => intro fuel; simp [localMutation, denote]
  | typeAscription _ _ ih =>
    intro fuel; simp only [localMutation]; unfold denote; exact ih fuel

end Hax
