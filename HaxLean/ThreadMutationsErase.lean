/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import HaxLean.AST
import HaxLean.ThreadMutations

/-!
# Untyped twin of the mutation-threading pre-pass + erase commutation

`tThreadMut` (`Hax/ThreadMutations.lean`) runs before the typed pipeline. This
file gives the untyped twin `threadMut` on `ImpExpr` together with the commuting
square

    (tThreadMut active e).erase = threadMut active e.erase

so the pre-pass is a refinement of an untyped transformation, like the five
verified pipeline phases. The analysis twins (`assignedVars`, `varRefs`,
`containsLoop`) and the rewrite helpers (`replaceTail`, `varTuple`,
`destructure`) get their own `@[simp]` erase lemmas first.
-/

namespace Hax

/-! ## Untyped twins of the analyses -/

/-- Untyped twin of `tAssignedVars`. -/
def assignedVars : ImpExpr → List String
  | .assign n rhs => n :: assignedVars rhs
  | .letBind _ v b => assignedVars v ++ assignedVars b
  | .lam _ b => assignedVars b
  | .app _ args => goE args
  | .tuple es => goE es
  | .proj e _ => assignedVars e
  | .ifThenElse c t e => assignedVars c ++ assignedVars t ++ assignedVars e
  | .match_ s arms => assignedVars s ++ goA arms
  | .seq a b => assignedVars a ++ assignedVars b
  | .borrow e => assignedVars e
  | .deref e => assignedVars e
  | .forLoop _ lo hi b => assignedVars lo ++ assignedVars hi ++ assignedVars b
  | .forLoopRev _ lo hi b => assignedVars lo ++ assignedVars hi ++ assignedVars b
  | .whileLoop c b => assignedVars c ++ assignedVars b
  | .earlyReturn e => assignedVars e
  | .questionMark e => assignedVars e
  | .forFold _ lo hi b => assignedVars lo ++ assignedVars hi ++ assignedVars b
  | .forFoldRev _ lo hi b => assignedVars lo ++ assignedVars hi ++ assignedVars b
  | .whileFold c b => assignedVars c ++ assignedVars b
  | .forFoldReturn _ lo hi b => assignedVars lo ++ assignedVars hi ++ assignedVars b
  | .forFoldRevReturn _ lo hi b => assignedVars lo ++ assignedVars hi ++ assignedVars b
  | .whileFoldReturn c b => assignedVars c ++ assignedVars b
  | .cfBreak e => assignedVars e
  | .cfContinue e => assignedVars e
  | .cfBreakContinue e => assignedVars e
  | .typeAscription e _ => assignedVars e
  | .break_ (some e) => assignedVars e
  | _ => []
where
  goE : List ImpExpr → List String
    | [] => []
    | e :: es => assignedVars e ++ goE es
  goA : List (ImpPat × ImpExpr) → List String
    | [] => []
    | (_, e) :: rest => assignedVars e ++ goA rest

/-- Untyped twin of `tVarRefs`. -/
def varRefs : ImpExpr → List String
  | .var n => [n]
  | .letBind _ v b => varRefs v ++ varRefs b
  | .lam _ b => varRefs b
  | .app _ args => goE args
  | .tuple es => goE es
  | .proj e _ => varRefs e
  | .ifThenElse c t e => varRefs c ++ varRefs t ++ varRefs e
  | .match_ s arms => varRefs s ++ goA arms
  | .seq a b => varRefs a ++ varRefs b
  | .borrow e => varRefs e
  | .deref e => varRefs e
  | .assign _ rhs => varRefs rhs
  | .forLoop _ lo hi b => varRefs lo ++ varRefs hi ++ varRefs b
  | .forLoopRev _ lo hi b => varRefs lo ++ varRefs hi ++ varRefs b
  | .whileLoop c b => varRefs c ++ varRefs b
  | .earlyReturn e => varRefs e
  | .questionMark e => varRefs e
  | .forFold _ lo hi b => varRefs lo ++ varRefs hi ++ varRefs b
  | .forFoldRev _ lo hi b => varRefs lo ++ varRefs hi ++ varRefs b
  | .whileFold c b => varRefs c ++ varRefs b
  | .forFoldReturn _ lo hi b => varRefs lo ++ varRefs hi ++ varRefs b
  | .forFoldRevReturn _ lo hi b => varRefs lo ++ varRefs hi ++ varRefs b
  | .whileFoldReturn c b => varRefs c ++ varRefs b
  | .cfBreak e => varRefs e
  | .cfContinue e => varRefs e
  | .cfBreakContinue e => varRefs e
  | .typeAscription e _ => varRefs e
  | .break_ (some e) => varRefs e
  | _ => []
where
  goE : List ImpExpr → List String
    | [] => []
    | e :: es => varRefs e ++ goE es
  goA : List (ImpPat × ImpExpr) → List String
    | [] => []
    | (_, e) :: rest => varRefs e ++ goA rest

/-- Untyped twin of `tContainsLoop`. -/
def containsLoop : ImpExpr → Bool
  | .forLoop .. => true
  | .forLoopRev .. => true
  | .whileLoop .. => true
  | .forFold .. => true
  | .forFoldRev .. => true
  | .whileFold .. => true
  | .forFoldReturn .. => true
  | .forFoldRevReturn .. => true
  | .whileFoldReturn .. => true
  | .letBind _ v b => containsLoop v || containsLoop b
  | .lam _ b => containsLoop b
  | .app _ args => goE args
  | .tuple es => goE es
  | .proj e _ => containsLoop e
  | .ifThenElse c t e => containsLoop c || containsLoop t || containsLoop e
  | .match_ s arms => containsLoop s || goA arms
  | .seq a b => containsLoop a || containsLoop b
  | .borrow e => containsLoop e
  | .deref e => containsLoop e
  | .assign _ rhs => containsLoop rhs
  | .earlyReturn e => containsLoop e
  | .questionMark e => containsLoop e
  | .cfBreak e => containsLoop e
  | .cfContinue e => containsLoop e
  | .cfBreakContinue e => containsLoop e
  | .typeAscription e _ => containsLoop e
  | .break_ (some e) => containsLoop e
  | _ => false
where
  goE : List ImpExpr → Bool
    | [] => false
    | e :: es => containsLoop e || goE es
  goA : List (ImpPat × ImpExpr) → Bool
    | [] => false
    | (_, e) :: rest => containsLoop e || goA rest

/-! ## Untyped twins of the rewrite helpers -/

/-- Untyped twin of `tReplaceTail`. -/
def replaceTail : ImpExpr → ImpExpr → ImpExpr
  | .letBind n v body, newTail => .letBind n v (replaceTail body newTail)
  | .seq a b, newTail => .seq a (replaceTail b newTail)
  | .assign n r, newTail => .seq (.assign n r) newTail
  | _, newTail => newTail

/-- Untyped twin of `tVarTuple`. -/
def varTuple : List String → ImpExpr
  | [v] => .var v
  | vs => .tuple (vs.map (fun v => .var v))

/-- Untyped twin of `tDestructure`. -/
def destructure : List String → ImpExpr → ImpExpr → ImpExpr
  | [], _, cont => cont
  | [v], tup, cont => .letBind v tup cont
  | v :: vs, tup, cont =>
    .letBind v (.proj tup 0) (destructure vs (.proj tup 1) cont)

/-! ## Erase commutation for the helpers -/

@[simp] theorem tStripAnn_erase (e : TExpr) : (tStripAnn e).erase = e.erase := by
  induction e using TExpr.ind with
  | ann _ _ ih => simpa only [tStripAnn, TExpr.erase] using ih
  | _ => rfl

/-- `tStripAnn` removes every outer `.ann`, so its result is never an `.ann`. -/
theorem tStripAnn_ne_ann (e : TExpr) (x : TExpr) (ty : ImpType) :
    tStripAnn e ≠ .mk (.ann x) ty := by
  induction e using TExpr.ind with
  | ann _ _ ih => simpa only [tStripAnn] using ih
  | _ => intro h; simp only [tStripAnn] at h ⊢ <;> exact absurd h (by simp)

@[simp] theorem tAssignedVars_erase (e : TExpr) :
    tAssignedVars e = assignedVars e.erase := by
  apply tAssignedVars.induct
    (motive_2 := fun e => tAssignedVars e = assignedVars e.erase)
    (motive_1 := fun es => tAssignedVars.goE es = assignedVars.goE (es.map TExpr.erase))
    (motive_3 := fun arms => tAssignedVars.goA arms
                  = assignedVars.goA (arms.map (fun pe => (pe.1, pe.2.erase)))) <;>
  intros <;>
  simp_all [tAssignedVars, assignedVars, TExpr.erase,
    tAssignedVars.goE, tAssignedVars.goA, assignedVars.goE, assignedVars.goA,
    TExpr.eraseList_eq, TExpr.eraseArms_eq]

@[simp] theorem tVarRefs_erase (e : TExpr) :
    tVarRefs e = varRefs e.erase := by
  apply tVarRefs.induct
    (motive_2 := fun e => tVarRefs e = varRefs e.erase)
    (motive_1 := fun es => tVarRefs.goE es = varRefs.goE (es.map TExpr.erase))
    (motive_3 := fun arms => tVarRefs.goA arms
                  = varRefs.goA (arms.map (fun pe => (pe.1, pe.2.erase)))) <;>
  intros <;>
  simp_all [tVarRefs, varRefs, TExpr.erase,
    tVarRefs.goE, tVarRefs.goA, varRefs.goE, varRefs.goA,
    TExpr.eraseList_eq, TExpr.eraseArms_eq]

@[simp] theorem tContainsLoop_erase (e : TExpr) :
    tContainsLoop e = containsLoop e.erase := by
  apply tContainsLoop.induct
    (motive_2 := fun e => tContainsLoop e = containsLoop e.erase)
    (motive_1 := fun es => tContainsLoop.goE es = containsLoop.goE (es.map TExpr.erase))
    (motive_3 := fun arms => tContainsLoop.goA arms
                  = containsLoop.goA (arms.map (fun pe => (pe.1, pe.2.erase)))) <;>
  intros <;>
  simp_all [tContainsLoop, containsLoop, TExpr.erase,
    tContainsLoop.goE, tContainsLoop.goA, containsLoop.goE, containsLoop.goA,
    TExpr.eraseList_eq, TExpr.eraseArms_eq]

@[simp] theorem tReplaceTail_erase (e t : TExpr) :
    (tReplaceTail e t).erase = replaceTail e.erase t.erase := by
  induction e using TExpr.ind with
  | letBind _ _ _ _ _ ih => simp_all [tReplaceTail, replaceTail, TExpr.erase]
  | seq _ _ _ _ ih => simp_all [tReplaceTail, replaceTail, TExpr.erase]
  | assign => simp [tReplaceTail, replaceTail, TExpr.erase]
  | ann _ _ ih => simp_all [tReplaceTail, replaceTail, TExpr.erase]
  | _ => rfl

@[simp] theorem tVarTuple_erase (vs : List String) :
    (tVarTuple vs).erase = varTuple vs := by
  match vs with
  | [] => simp [tVarTuple, varTuple, TExpr.erase, TExpr.eraseList_eq]
  | [v] => rfl
  | v₁ :: v₂ :: vs =>
    simp [tVarTuple, varTuple, TExpr.erase, TExpr.eraseList_eq, List.map_map, Function.comp_def]

@[simp] theorem tDestructure_erase (vs : List String) (tup cont : TExpr) :
    (tDestructure vs tup cont).erase = destructure vs tup.erase cont.erase := by
  induction vs generalizing tup with
  | nil => rfl
  | cons v vs ih =>
    cases vs with
    | nil => simp [tDestructure, destructure, TExpr.erase]
    | cons v₂ vs => simp [tDestructure, destructure, TExpr.erase, ih]

/-! ## Untyped twin of `tThreadMut` -/

/-- Untyped twin of `tThreadMut` (see that function's docstring). -/
def threadMut (active : Bool) : ImpExpr → ImpExpr
  | .seq a rest =>
      let a' := threadMut active a
      let rest' := threadMut active rest
      match a' with
      | .ifThenElse c t f =>
          let used := varRefs rest'
          let m := (assignedVars t ++ assignedVars f).eraseDups.filter used.contains
          if (!active && !containsLoop rest') || m.isEmpty then
            .seq a' rest'
          else
            let tup := varTuple m
            let ifE := .ifThenElse c (replaceTail t tup) (replaceTail f tup)
            .letBind "_mtup" ifE (destructure m (.var "_mtup") rest')
      | _ => .seq a' rest'
  | .forLoop v lo hi b => .forLoop v (threadMut active lo) (threadMut active hi) (threadMut false b)
  | .forLoopRev v lo hi b =>
      .forLoopRev v (threadMut active lo) (threadMut active hi) (threadMut false b)
  | .forFold v lo hi b => .forFold v (threadMut active lo) (threadMut active hi) (threadMut false b)
  | .forFoldRev v lo hi b =>
      .forFoldRev v (threadMut active lo) (threadMut active hi) (threadMut false b)
  | .forFoldReturn v lo hi b =>
      .forFoldReturn v (threadMut active lo) (threadMut active hi) (threadMut false b)
  | .forFoldRevReturn v lo hi b =>
      .forFoldRevReturn v (threadMut active lo) (threadMut active hi) (threadMut false b)
  | .whileLoop c b => .whileLoop (threadMut active c) (threadMut false b)
  | .whileFold c b => .whileFold (threadMut active c) (threadMut false b)
  | .whileFoldReturn c b => .whileFoldReturn (threadMut active c) (threadMut false b)
  | .lit v => .lit v
  | .var n => .var n
  | .letBind n val body => .letBind n (threadMut active val) (threadMut active body)
  | .lam ps body => .lam ps (threadMut active body)
  | .app g args => .app g (mapE active args)
  | .tuple elems => .tuple (mapE active elems)
  | .proj e i => .proj (threadMut active e) i
  | .ifThenElse c t e =>
      .ifThenElse (threadMut active c) (threadMut active t) (threadMut active e)
  | .match_ scrut arms => .match_ (threadMut active scrut) (mapA active arms)
  | .unitVal => .unitVal
  | .borrow e => .borrow (threadMut active e)
  | .deref e => .deref (threadMut active e)
  | .assign n rhs => .assign n (threadMut active rhs)
  | .break_ none => .break_ none
  | .break_ (some e) => .break_ (some (threadMut active e))
  | .continue_ => .continue_
  | .earlyReturn e => .earlyReturn (threadMut active e)
  | .questionMark e => .questionMark (threadMut active e)
  | .cfBreak e => .cfBreak (threadMut active e)
  | .cfContinue e => .cfContinue (threadMut active e)
  | .cfBreakContinue e => .cfBreakContinue (threadMut active e)
  | .typeAscription e ty => .typeAscription (threadMut active e) ty
where
  mapE (active : Bool) : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => threadMut active e :: mapE active es
  mapA (active : Bool) : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, threadMut active e) :: mapA active rest

/-! ## Main erase commutation -/

/-- Commuting diagram: type erasure commutes with `tThreadMut`. -/
theorem tThreadMut_erase (active : Bool) (e : TExpr) :
    (tThreadMut active e).erase = threadMut active e.erase := by
  apply tThreadMut.induct
    (motive_2 := fun active e => (tThreadMut active e).erase = threadMut active e.erase)
    (motive_1 := fun active es => (tThreadMut.mapE active es).map TExpr.erase
                  = threadMut.mapE active (es.map TExpr.erase))
    (motive_3 := fun active arms => (tThreadMut.mapA active arms).map (fun pe => (pe.1, pe.2.erase))
                  = threadMut.mapA active (arms.map (fun pe => (pe.1, pe.2.erase))))
  -- The three `seq` cases (the `if`-statement join is detected / not) need the
  -- untyped match scrutinee bridged to the typed one via the IH; every other
  -- constructor closes by `simp_all`.
  case case1 =>
    intro active a rest sty a' rest' c t f ifty hx used m hcond ih_a ih_rest
    have hx' : tStripAnn (tThreadMut active a) = .mk (.ifThenElse c t f) ifty := hx
    have hau : threadMut active a.erase = (tStripAnn (tThreadMut active a)).erase := by
      rw [tStripAnn_erase]; exact ih_a.symm
    have hbridge : threadMut active a.erase = ImpExpr.ifThenElse c.erase t.erase f.erase := by
      simp only [hau, hx', TExpr.erase]
    simp only [tThreadMut, threadMut, TExpr.erase, hx', hbridge,
      tContainsLoop_erase, tVarRefs_erase, tAssignedVars_erase, ih_rest]
    split <;>
      simp_all [TExpr.erase, tAssignedVars_erase, tVarRefs_erase, tContainsLoop_erase,
        tReplaceTail_erase, tVarTuple_erase, tDestructure_erase, ih_a, ih_rest, hbridge,
        TExpr.eraseList_eq, TExpr.eraseArms_eq]
  case case2 =>
    intro active a rest sty a' rest' c t f ifty hx used m hcond ih_a ih_rest
    have hx' : tStripAnn (tThreadMut active a) = .mk (.ifThenElse c t f) ifty := hx
    have hau : threadMut active a.erase = (tStripAnn (tThreadMut active a)).erase := by
      rw [tStripAnn_erase]; exact ih_a.symm
    have hbridge : threadMut active a.erase = ImpExpr.ifThenElse c.erase t.erase f.erase := by
      simp only [hau, hx', TExpr.erase]
    simp only [tThreadMut, threadMut, TExpr.erase, hx', hbridge,
      tContainsLoop_erase, tVarRefs_erase, tAssignedVars_erase, ih_rest]
    split <;>
      simp_all [TExpr.erase, tAssignedVars_erase, tVarRefs_erase, tContainsLoop_erase,
        tReplaceTail_erase, tVarTuple_erase, tDestructure_erase, ih_a, ih_rest, hbridge,
        TExpr.eraseList_eq, TExpr.eraseArms_eq]
  case case3 =>
    intro active a rest sty a' hneg ih_a ih_rest
    have hau : threadMut active a.erase = (tStripAnn (tThreadMut active a)).erase := by
      rw [tStripAnn_erase]; exact ih_a.symm
    simp only [tThreadMut, threadMut, TExpr.erase, hau]
    cases hk : tStripAnn (tThreadMut active a) with
    | mk k kty =>
      cases k <;>
        first
        | exact absurd hk (hneg _ _ _ _)
        | exact absurd hk (tStripAnn_ne_ann _ _ _)
        | (cases ‹Option TExpr› <;>
            simp_all [TExpr.erase, tStripAnn_ne_ann, ih_a, ih_rest,
              TExpr.eraseList_eq, TExpr.eraseArms_eq])
        | simp_all [TExpr.erase, tStripAnn_ne_ann, ih_a, ih_rest,
            TExpr.eraseList_eq, TExpr.eraseArms_eq]
  all_goals (try intros)
  all_goals
    simp_all [tThreadMut, threadMut, TExpr.erase,
      tThreadMut.mapE, tThreadMut.mapA, threadMut.mapE, threadMut.mapA,
      TExpr.eraseList_eq, TExpr.eraseArms_eq]

end Hax
