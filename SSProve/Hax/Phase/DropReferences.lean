/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.AST
import SSProve.Hax.Features
import SSProve.Hax.Semantics

/-!
# Phase 1: Drop References

Erase `borrow` and `deref` nodes: `&x → x`, `*x → x`.

In Hax's supported Rust subset (safe code, no aliased mutable refs),
borrows are semantically transparent.

## Main definitions

* `dropReferences` — the transformation
* `dropReferences_noRefs` — output guarantee: `NoReferences`
* `dropReferences_correct` — semantics preservation
-/

namespace SSProve.Hax

/-- Erase all `borrow` and `deref` nodes. -/
def dropReferences : ImpExpr → ImpExpr
  | .lit v => .lit v
  | .var n => .var n
  | .letBind n val body => .letBind n (dropReferences val) (dropReferences body)
  | .app f args => .app f (mapExpr args)
  | .tuple elems => .tuple (mapExpr elems)
  | .proj e i => .proj (dropReferences e) i
  | .ifThenElse c t e => .ifThenElse (dropReferences c) (dropReferences t) (dropReferences e)
  | .match_ scrut arms =>
    .match_ (dropReferences scrut) (mapArms arms)
  | .unitVal => .unitVal
  | .seq e1 e2 => .seq (dropReferences e1) (dropReferences e2)
  | .borrow e => dropReferences e
  | .deref e => dropReferences e
  | .assign n rhs => .assign n (dropReferences rhs)
  | .forLoop v lo hi body =>
    .forLoop v (dropReferences lo) (dropReferences hi) (dropReferences body)
  | .whileLoop c body => .whileLoop (dropReferences c) (dropReferences body)
  | .break_ (some e) => .break_ (some (dropReferences e))
  | .break_ none => .break_ none
  | .continue_ => .continue_
  | .earlyReturn e => .earlyReturn (dropReferences e)
  | .questionMark e => .questionMark (dropReferences e)
where
  mapExpr : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => dropReferences e :: mapExpr es
  mapArms : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, dropReferences e) :: mapArms rest

@[simp] theorem dropReferences.mapExpr_eq (es : List ImpExpr) :
    dropReferences.mapExpr es = es.map dropReferences := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [dropReferences.mapExpr, ih]

@[simp] theorem dropReferences.mapArms_eq (arms : List (ImpPat × ImpExpr)) :
    dropReferences.mapArms arms = arms.map fun (p, e) => (p, dropReferences e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [dropReferences.mapArms, ih]

/-- `dropReferences` produces an expression with no references. -/
theorem dropReferences_noRefs (e : ImpExpr) : NoReferences (dropReferences e) := by
  induction e using ImpExpr.ind with
  | lit => exact .lit
  | var => exact .var
  | letBind _ _ _ ih1 ih2 => exact .letBind ih1 ih2
  | app _ args ih =>
    simp only [dropReferences, dropReferences.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb)
  | tuple elems ih =>
    simp only [dropReferences, dropReferences.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb)
  | proj _ _ ih => exact .proj ih
  | ifThenElse _ _ _ ih1 ih2 ih3 => exact .ifThenElse ih1 ih2 ih3
  | match_ _ arms ih1 ih2 =>
    simp only [dropReferences, dropReferences.mapArms_eq]
    exact .match_ ih1 (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb)
  | unitVal => exact .unitVal
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | borrow _ ih => exact ih
  | deref _ ih => exact ih
  | assign _ _ ih => exact .assign ih
  | forLoop _ _ _ _ ih1 ih2 ih3 => exact .forLoop ih1 ih2 ih3
  | whileLoop _ _ ih1 ih2 => exact .whileLoop ih1 ih2
  | break_none => exact .break_none
  | break_some _ ih => exact .break_some ih
  | continue_ => exact .continue_
  | earlyReturn _ ih => exact .earlyReturn ih
  | questionMark _ ih => exact .questionMark ih

/-- Semantics preservation: `denote` commutes with `dropReferences`.

    In the Hax-safe fragment, `borrow` and `deref` are semantically
    transparent (identity operations), so erasing them preserves behavior. -/
theorem dropReferences_correct (bi : Builtins) (fuel : Nat) (e : ImpExpr) :
    denote bi fuel (dropReferences e) = denote bi fuel e := by
  revert fuel
  induction e using ImpExpr.ind with
  | lit | var | unitVal | continue_ | break_none => intro fuel; rfl
  | borrow e ih =>
    intro fuel
    conv => rhs; unfold denote
    exact ih fuel
  | deref e ih =>
    intro fuel
    conv => rhs; unfold denote
    exact ih fuel
  | letBind n val body ih1 ih2 =>
    intro fuel
    simp only [dropReferences]
    unfold denote
    rw [ih1 fuel]; congr 1; funext rv; split
    · congr 1; funext _; exact ih2 fuel
    · rfl
  | seq e1 e2 ih1 ih2 =>
    intro fuel
    simp only [dropReferences]
    unfold denote
    rw [ih1 fuel]; congr 1; funext r1; split
    · exact ih2 fuel
    · rfl
  | proj e i ih =>
    intro fuel
    simp only [dropReferences]
    unfold denote
    rw [ih fuel]
  | ifThenElse c t e ih1 ih2 ih3 =>
    intro fuel
    simp only [dropReferences]
    unfold denote
    rw [ih1 fuel]; congr 1; funext rc; split
    · exact ih2 fuel
    · exact ih3 fuel
    · rfl
    · rfl
  | assign n rhs ih =>
    intro fuel
    simp only [dropReferences]
    unfold denote
    rw [ih fuel]
  | earlyReturn e ih =>
    intro fuel
    simp only [dropReferences]
    unfold denote
    rw [ih fuel]
  | questionMark e ih =>
    intro fuel
    simp only [dropReferences]
    unfold denote
    rw [ih fuel]
  | break_some e ih =>
    intro fuel
    simp only [dropReferences]
    unfold denote
    rw [ih fuel]
  | app f args ih =>
    intro fuel
    simp only [dropReferences, dropReferences.mapExpr_eq]
    unfold denote
    rw [denoteArgs_map_congr bi fuel dropReferences args (fun e he => ih e he fuel)]
  | tuple elems ih =>
    intro fuel
    simp only [dropReferences, dropReferences.mapExpr_eq]
    unfold denote
    rw [denoteArgs_map_congr bi fuel dropReferences elems (fun e he => ih e he fuel)]
  | match_ scrut arms ih1 ih2 =>
    intro fuel
    simp only [dropReferences, dropReferences.mapArms_eq]
    unfold denote
    rw [ih1 fuel]; congr 1; funext rs; split
    · exact denoteMatchArms_map_congr bi fuel dropReferences _ arms
        (fun pa hpa => ih2 pa hpa fuel)
    · rfl
  | forLoop v lo hi body ih1 ih2 ih3 =>
    intro fuel
    simp only [dropReferences]
    unfold denote
    rw [ih1 fuel, ih2 fuel]; congr 1; funext rlo; congr 1; funext rhi
    split
    · exact denoteForLoop_congr bi fuel v _ _ body (dropReferences body) ih3
    · rfl
    · rfl
  | whileLoop c body ih1 ih2 =>
    intro fuel
    simp only [dropReferences]
    unfold denote
    exact denoteWhile_congr bi fuel c (dropReferences c) body (dropReferences body) ih1 ih2

end SSProve.Hax
