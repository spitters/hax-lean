/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Phase.ExplicitMonadicCF

/-!
# Bindings of `if`-expressions and blocks moved into statements

hax-lean emits a Rust `let x = if c { a } else { b }; k`, and the mutation tuple
`let _mtup = if c { …; x } else { x }; let x = _mtup; k` of a branch that assigns `x`,
as `letBind x (ifThenElse c a b) k`. A lowering whose statement grammar has no
`if`-expression refuses the binding. Under `denote'` a `letBind` extends the
environment and does not restore it, so the binding moves into the branches:

```
letBind x (ifThenElse c t f) k   ↦   seq (ifThenElse c (letBind x t unitVal)
                                                      (letBind x f unitVal)) k
```

and past the statements of a block bound to a name:

```
letBind x (seq a b) k         ↦   seq a (letBind x b k)
letBind x (letBind y w b) k   ↦   letBind y w (letBind x b k)
```

`bindInto x v k` applies the three rewrites to `letBind x v k`, recursively in the moved
bindings. `letsInto e` applies `bindInto` to every `letBind` of the statement spine of
`e` (`letBind`, `seq`, the branches of `ifThenElse`) and of the bodies of the counted
and `while` loops. Neither introduces a name, duplicates an expression or reorders an
evaluation, and both preserve `denote'` exactly, at every builtin table and fuel.

## Main results

* `denote'_bindInto`: `bindInto x v k` and `letBind x v k` have the same denotation
* `denote'_letsInto`: `letsInto e` and `e` have the same denotation
-/

@[expose] public section
set_option autoImplicit false

namespace Hax.LetIntoBranches

/-! ## The rewriting -/

/-- `letBind x v k` with the binding of `x` moved into the branches of an
    `if`-expression `v` and past the statements of a block `v`. -/
def bindInto (x : String) : ImpExpr → ImpExpr → ImpExpr
  | .ifThenElse c t f, k =>
      .seq (.ifThenElse c (bindInto x t .unitVal) (bindInto x f .unitVal)) k
  | .seq a b, k => .seq a (bindInto x b k)
  | .letBind y w b, k => bindInto y w (bindInto x b k)
  | v, k => .letBind x v k

/-- `e` with `bindInto` applied to every `letBind` of its statement spine and of the
    bodies of its loops. -/
def letsInto : ImpExpr → ImpExpr
  | .letBind x v k => bindInto x (letsInto v) (letsInto k)
  | .seq a b => .seq (letsInto a) (letsInto b)
  | .ifThenElse c t f => .ifThenElse c (letsInto t) (letsInto f)
  | .forFold i lo hi b => .forFold i lo hi (letsInto b)
  | .forFoldRev i lo hi b => .forFoldRev i lo hi (letsInto b)
  | .forFoldReturn i lo hi b => .forFoldReturn i lo hi (letsInto b)
  | .forFoldRevReturn i lo hi b => .forFoldRevReturn i lo hi (letsInto b)
  | .whileFold c b => .whileFold c (letsInto b)
  | .whileFoldReturn c b => .whileFoldReturn c (letsInto b)
  | e => e

/-! ## Preservation of the denotation -/

theorem denote'_bindInto (bi : Builtins) (fuel : Nat) (x : String) (v k : ImpExpr) :
    denote' bi fuel (bindInto x v k) = denote' bi fuel (.letBind x v k) := by
  fun_induction bindInto x v k with
  | case1 x c t f k iht ihf =>
    funext env
    simp only [denote', iht, ihf, bind, StateT.bind, pure, modify, modifyGet,
      MonadStateOf.modifyGet]
    generalize denote' bi fuel c env = pc
    obtain ⟨rc, e1⟩ := pc
    rcases rc with ⟨v⟩ | v | v | _ | m <;> try rfl
    cases v with
    | bool b =>
      cases b with
      | true =>
        simp only [StateT.bind]
        generalize denote' bi fuel t e1 = pt
        obtain ⟨rt, e2⟩ := pt
        rcases rt with ⟨w⟩ | w | w | _ | m <;> try rfl
        cases w <;> rfl
      | false =>
        simp only [StateT.bind]
        generalize denote' bi fuel f e1 = pt
        obtain ⟨rt, e2⟩ := pt
        rcases rt with ⟨w⟩ | w | w | _ | m <;> try rfl
        cases w <;> rfl
    | _ => rfl
  | case2 x a b k ih =>
    funext env
    simp only [denote', ih, bind, StateT.bind, pure, modify, modifyGet, MonadStateOf.modifyGet]
    generalize denote' bi fuel a env = pa
    obtain ⟨ra, e1⟩ := pa
    rcases ra with ⟨u⟩ | u | u | _ | m <;> try rfl
    cases u <;> rfl
  | case3 x y w b k ihb ihw =>
    funext env
    simp only [denote', ihb, ihw, bind, StateT.bind, pure, modify, modifyGet,
      MonadStateOf.modifyGet]
    generalize denote' bi fuel w env = pw
    obtain ⟨rw, e1⟩ := pw
    rcases rw with ⟨u⟩ | u | u | _ | m <;> try rfl
    cases u <;> rfl
  | case4 => rfl

theorem denote'_letsInto (e : ImpExpr) :
    ∀ (bi : Builtins) (fuel : Nat), denote' bi fuel (letsInto e) = denote' bi fuel e := by
  fun_induction letsInto e with
  | case1 x v k ihv ihk =>
    intro bi fuel
    rw [denote'_bindInto]
    simp only [denote', ihv, ihk]
  | case2 a b iha ihb =>
    intro bi fuel
    simp only [denote', iha, ihb]
  | case3 c t f iht ihf =>
    intro bi fuel
    simp only [denote', iht, ihf]
  | case4 i lo hi b ih =>
    intro bi fuel
    have hl : ∀ l h, denoteForLoop' bi fuel i l h (letsInto b) = denoteForLoop' bi fuel i l h b :=
      fun l h => funext (denoteForLoop'_body_congr bi i _ _ (fun f e => by rw [ih]) fuel l h)
    simp only [denote', hl]
  | case5 i lo hi b ih =>
    intro bi fuel
    have hl : ∀ l h, denoteForLoopRev' bi fuel i l h (letsInto b) =
        denoteForLoopRev' bi fuel i l h b :=
      fun l h => funext (denoteForLoopRev'_body_congr bi i _ _ (fun f e => by rw [ih]) fuel l h)
    simp only [denote', hl]
  | case6 i lo hi b ih =>
    intro bi fuel
    have hl : ∀ l h, denoteForLoop'Return bi fuel i l h (letsInto b) =
        denoteForLoop'Return bi fuel i l h b :=
      fun l h => funext
        (denoteForLoop'Return_body_congr bi i _ _ (fun f e => by rw [ih]) fuel l h)
    simp only [denote', hl]
  | case7 i lo hi b ih =>
    intro bi fuel
    have hl : ∀ l h, denoteForLoopRev'Return bi fuel i l h (letsInto b) =
        denoteForLoopRev'Return bi fuel i l h b :=
      fun l h => funext
        (denoteForLoopRev'Return_body_congr bi i _ _ (fun f e => by rw [ih]) fuel l h)
    simp only [denote', hl]
  | case8 c b ih =>
    intro bi fuel
    simp only [denote']
    exact funext (denoteWhile'_congr bi c c _ _ (fun _ _ => rfl) (fun f e => by rw [ih]) fuel)
  | case9 c b ih =>
    intro bi fuel
    simp only [denote']
    exact funext
      (denoteWhile'Return_congr bi c c _ _ (fun _ _ => rfl) (fun f e => by rw [ih]) fuel)
  | case10 => intro bi fuel; rfl

end Hax.LetIntoBranches
