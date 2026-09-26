/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.AST
public import HaxLean.ThreadMutations

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

## Main results

* `tThreadMut_erase`: erasure commutes with the mutation-threading pre-pass.
* `tRebindMutCalls_erase`: erasure commutes with the `&mut` call rewrite, in
  its single and tuple forms.
* `tReturnMutParams_erase`, `tTupleTail_erase`: erasure commutes with the
  write-back tail of a callee.
-/

@[expose] public section

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
  | .ifThenElse c t f, newTail => .ifThenElse c (replaceTail t newTail) (replaceTail f newTail)
  | .match_ s arms, newTail => .match_ s (goA arms newTail)
  | .forLoop v lo hi b, newTail => .seq (.forLoop v lo hi b) newTail
  | .forLoopRev v lo hi b, newTail => .seq (.forLoopRev v lo hi b) newTail
  | .whileLoop c b, newTail => .seq (.whileLoop c b) newTail
  | .forFold v lo hi b, newTail => .seq (.forFold v lo hi b) newTail
  | .forFoldRev v lo hi b, newTail => .seq (.forFoldRev v lo hi b) newTail
  | .whileFold c b, newTail => .seq (.whileFold c b) newTail
  | .forFoldReturn v lo hi b, newTail => .seq (.forFoldReturn v lo hi b) newTail
  | .forFoldRevReturn v lo hi b, newTail => .seq (.forFoldRevReturn v lo hi b) newTail
  | .whileFoldReturn c b, newTail => .seq (.whileFoldReturn c b) newTail
  | .earlyReturn e, newTail => .seq (.earlyReturn e) newTail
  | .break_ b, newTail => .seq (.break_ b) newTail
  | .continue_, newTail => .seq .continue_ newTail
  | _, newTail => newTail
where
  goA : List (ImpPat × ImpExpr) → ImpExpr → List (ImpPat × ImpExpr)
    | [], _ => []
    | (p, e) :: rest, newTail => (p, replaceTail e newTail) :: goA rest newTail

/-- Untyped twin of `tVarTuple`. -/
def varTuple : List String → ImpExpr
  | [v] => .var v
  | vs => .tuple (vs.map (fun v => .var v))

/-- Untyped twin of `tDestructure`. -/
def destructure : List String → ImpExpr → ImpExpr → ImpExpr
  | [], _, cont => cont
  | [v], tup, cont => .letBind v tup cont
  | v :: vs, tup, cont =>
    .letBind v (.proj tup 0) (destructure vs (.app "::proj::.2" [tup]) cont)

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

/-- The arms component of `tAssignedVars_erase`, used where a `match` is
    analysed through its arm bodies alone. -/
@[simp] theorem tAssignedVars_goA_erase (arms : List (ImpPat × TExpr)) :
    tAssignedVars.goA arms = assignedVars.goA (arms.map (fun pe => (pe.1, pe.2.erase))) := by
  induction arms with
  | nil => rfl
  | cons pa rest ih =>
    obtain ⟨p, e⟩ := pa
    simp [tAssignedVars.goA, assignedVars.goA, ih]

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
  | ifThenElse _ _ _ _ _ iht ihf =>
    first
      | (simp only [tReplaceTail, replaceTail, TExpr.erase, iht, ihf]; done)
      | simp_all [tReplaceTail, replaceTail, TExpr.erase]
  | match_ _ _ arms _ iharms =>
    simp only [tReplaceTail, replaceTail, TExpr.erase, TExpr.eraseArms_eq]
    congr 1
    induction arms with
    | nil => rfl
    | cons pa rest ih =>
      obtain ⟨p, e⟩ := pa
      simp only [tReplaceTail.goA, replaceTail.goA, List.map_cons,
        iharms (p, e) (List.mem_cons_self ..),
        ih (fun pa hpa => iharms pa (List.mem_cons_of_mem _ hpa))]
  | ann _ _ ih => simp_all [tReplaceTail, TExpr.erase]
  | _ => first | rfl | simp [tReplaceTail, replaceTail, TExpr.erase]

/-- The arms component of `tReplaceTail_erase`, used where a `match` is
    rewritten through its arm bodies alone. -/
@[simp] theorem tReplaceTail_goA_erase (arms : List (ImpPat × TExpr)) (t : TExpr) :
    (tReplaceTail.goA arms t).map (fun pe => (pe.1, pe.2.erase))
      = replaceTail.goA (arms.map (fun pe => (pe.1, pe.2.erase))) t.erase := by
  induction arms with
  | nil => rfl
  | cons pa rest ih =>
    obtain ⟨p, e⟩ := pa
    simp only [tReplaceTail.goA, replaceTail.goA, List.map_cons, tReplaceTail_erase, ih]

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
    | cons v₂ vs =>
      simp [tDestructure, destructure, TExpr.erase, TExpr.eraseList_eq, ih]

/-! ## Untyped twins of the `&mut` write-back rewrites

The write-back table is built from function signatures, which are not part of an
expression, so both sides read the same `List (String × Nat)` and the square
below is over that shared table. -/

/-- Untyped twin of `tMutArgRoot`. -/
def mutArgRoot : ImpExpr → Option String
  | .var n => some n
  | .borrow e => mutArgRoot e
  | .deref e => mutArgRoot e
  | .typeAscription e _ => mutArgRoot e
  | _ => none

/-- Untyped twin of `tCallWriteback`. -/
def callWriteback (writers : List (String × Nat)) (f : String) (args : List ImpExpr) :
    Option String :=
  if f == ".0" then none
  else
    match writers.lookup f with
    | some i => (args[i]?).bind mutArgRoot
    | none => none

/-- Untyped twin of `tMutArgField`. -/
def mutArgField : ImpExpr → Option (String × String)
  | .borrow e => mutArgField e
  | .deref e => mutArgField e
  | .typeAscription e _ => mutArgField e
  | .app pf [sE] =>
    if pf.startsWith "." && pf != ".0" then
      (mutArgRoot sE).map fun r => (r, (pf.drop 1).toString)
    else none
  | _ => none

/-- Untyped twin of `tCallWritebackField`. -/
def callWritebackField (sf : StructFieldNames) (writers : List (String × Nat))
    (f : String) (args : List ImpExpr) : Option (String × String × Nat × Nat) :=
  if f == ".0" then none
  else
    match writers.lookup f with
    | some i =>
      (args[i]?).bind fun a =>
        (mutArgField a).bind fun rf =>
          (resolveStructField sf rf.2).map fun sin => (rf.1, sin)
    | none => none

/-- Untyped twin of `tRangeBounds`. -/
def rangeBounds (root : String) : ImpExpr → Option (ImpExpr × ImpExpr)
  | .typeAscription e _ => rangeBounds root e
  | .app "RangeTo" [hi] => some (.lit (.int 0), hi)
  | .app "Range" [lo, hi] => some (lo, hi)
  | .app "RangeFrom" [lo] => some (lo, .app "len" [.var root])
  | _ => none

/-- Untyped twin of `tMutArgSlice`. -/
def mutArgSlice : ImpExpr → Option (String × ImpExpr × ImpExpr)
  | .borrow e => mutArgSlice e
  | .deref e => mutArgSlice e
  | .typeAscription e _ => mutArgSlice e
  | .app f [aE, rE] =>
    if f == "index_mut" then
      (mutArgRoot aE).bind fun r =>
        (rangeBounds r rE).map fun b => (r, b.1, b.2)
    else none
  | _ => none

/-- Untyped twin of `tCallWritebackSlice`. -/
def callWritebackSlice (writers : List (String × Nat)) (f : String) (args : List ImpExpr) :
    Option (String × ImpExpr × ImpExpr) :=
  if f == ".0" then none
  else
    match writers.lookup f with
    | some i => (args[i]?).bind mutArgSlice
    | none => none

/-- Untyped twin of `tTupleComp`. -/
def tupleComp (tup : ImpExpr) : Nat → Nat → ImpExpr
  | _, 0 => tup
  | _, 1 => tup
  | 0, _ => .proj tup 0
  | i + 1, n + 1 => tupleComp (.app "::proj::.2" [tup]) i n

/-- Untyped twin of `tMutArgRoots`. -/
def mutArgRoots (args : List ImpExpr) : List Nat → Option (List String)
  | [] => some []
  | i :: is =>
    ((args[i]?).bind mutArgRoot).bind fun r =>
      (mutArgRoots args is).map (fun rs => r :: rs)

/-- Untyped twin of `tTupleWriteback`. -/
def tupleWriteback (tup : List (String × List Nat × Bool)) (f : String)
    (args : List ImpExpr) : Option (List String × Bool) :=
  if f == ".0" then none
  else
    match tup.lookup f with
    | some (ps, hasRes) => (mutArgRoots args ps).map (fun rs => (rs, hasRes))
    | none => none

/-- Untyped twin of `tTupleSite`. -/
def tupleSite (tup : List (String × List Nat × Bool)) : ImpExpr → Option (List String × Bool)
  | .app f args => tupleWriteback tup f args
  | _ => none

/-- Untyped twin of `tTupleAssigns`. -/
def tupleAssigns : List String → Nat → Nat → ImpExpr → ImpExpr
  | [], _, _, cont => cont
  | v :: vs, offset, n, cont =>
    .seq (.assign v (tupleComp (.var tWbTmp) offset n)) (tupleAssigns vs (offset + 1) n cont)

/-- Untyped twin of `tTupleBind`. -/
def tupleBind (call : ImpExpr) (roots : List String) (hasRes : Bool) (tail : ImpExpr) : ImpExpr :=
  .letBind tWbTmp call
    (tupleAssigns roots (if hasRes then 1 else 0)
      (roots.length + (if hasRes then 1 else 0)) tail)

/-- Untyped twin of `tTupleResult`. -/
def tupleResult (roots : List String) (hasRes : Bool) : ImpExpr :=
  if hasRes then tupleComp (.var tWbTmp) 0 (roots.length + 1) else .unitVal

/-- Untyped twin of `tRebindCall`. -/
def rebindCall (sf : StructFieldNames) (writers : List (String × Nat)) (f : String)
    (args : List ImpExpr) : ImpExpr :=
  match callWriteback writers f args with
  | some v => .assign v (.app f args)
  | none =>
    match callWritebackField sf writers f args with
    | some (root, sname, i, n) =>
      .assign root (.app (structUpdateHead sname i n) [.var root, .app f args])
    | none =>
      match callWritebackSlice writers f args with
      | some (root, lo, hi) =>
        .assign root (.app "slice_update" [.var root, lo, hi, .app f args])
      | none => .app f args

/-- Untyped twin of `tRebindMutCalls`. -/
def rebindMutCalls (sf : StructFieldNames) (writers : List (String × Nat))
    (tup : List (String × List Nat × Bool)) : ImpExpr → ImpExpr
  | .app f args => rebindCall sf writers f (mapE sf writers tup args)
  | .lit v => .lit v
  | .var n => .var n
  | .letBind n val body =>
      let val' := rebindMutCalls sf writers tup val
      let body' := rebindMutCalls sf writers tup body
      match tupleSite tup val' with
      | some (roots, hasRes) =>
          tupleBind val' roots hasRes (.letBind n (tupleResult roots hasRes) body')
      | none => .letBind n val' body'
  | .lam ps body => .lam ps (rebindMutCalls sf writers tup body)
  | .tuple elems => .tuple (mapE sf writers tup elems)
  | .proj e i => .proj (rebindMutCalls sf writers tup e) i
  | .ifThenElse c t e =>
      .ifThenElse (rebindMutCalls sf writers tup c) (rebindMutCalls sf writers tup t)
        (rebindMutCalls sf writers tup e)
  | .match_ scrut arms => .match_ (rebindMutCalls sf writers tup scrut) (mapA sf writers tup arms)
  | .unitVal => .unitVal
  | .seq a b =>
      let a' := rebindMutCalls sf writers tup a
      let b' := rebindMutCalls sf writers tup b
      match tupleSite tup a' with
      | some (roots, hasRes) => tupleBind a' roots hasRes b'
      | none => .seq a' b'
  | .borrow e => .borrow (rebindMutCalls sf writers tup e)
  | .deref e => .deref (rebindMutCalls sf writers tup e)
  | .assign n rhs =>
      let rhs' := rebindMutCalls sf writers tup rhs
      match tupleSite tup rhs' with
      | some (roots, hasRes) =>
          tupleBind rhs' roots hasRes (.assign n (tupleResult roots hasRes))
      | none => .assign n rhs'
  | .forLoop v lo hi b =>
      .forLoop v (rebindMutCalls sf writers tup lo) (rebindMutCalls sf writers tup hi)
        (rebindMutCalls sf writers tup b)
  | .forLoopRev v lo hi b =>
      .forLoopRev v (rebindMutCalls sf writers tup lo) (rebindMutCalls sf writers tup hi)
        (rebindMutCalls sf writers tup b)
  | .whileLoop c b =>
      .whileLoop (rebindMutCalls sf writers tup c) (rebindMutCalls sf writers tup b)
  | .break_ none => .break_ none
  | .break_ (some e) => .break_ (some (rebindMutCalls sf writers tup e))
  | .continue_ => .continue_
  | .earlyReturn e => .earlyReturn (rebindMutCalls sf writers tup e)
  | .questionMark e => .questionMark (rebindMutCalls sf writers tup e)
  | .forFold v lo hi b =>
      .forFold v (rebindMutCalls sf writers tup lo) (rebindMutCalls sf writers tup hi)
        (rebindMutCalls sf writers tup b)
  | .forFoldRev v lo hi b =>
      .forFoldRev v (rebindMutCalls sf writers tup lo) (rebindMutCalls sf writers tup hi)
        (rebindMutCalls sf writers tup b)
  | .whileFold c b =>
      .whileFold (rebindMutCalls sf writers tup c) (rebindMutCalls sf writers tup b)
  | .forFoldReturn v lo hi b =>
      .forFoldReturn v (rebindMutCalls sf writers tup lo) (rebindMutCalls sf writers tup hi)
        (rebindMutCalls sf writers tup b)
  | .forFoldRevReturn v lo hi b =>
      .forFoldRevReturn v (rebindMutCalls sf writers tup lo) (rebindMutCalls sf writers tup hi)
        (rebindMutCalls sf writers tup b)
  | .whileFoldReturn c b =>
      .whileFoldReturn (rebindMutCalls sf writers tup c) (rebindMutCalls sf writers tup b)
  | .cfBreak e => .cfBreak (rebindMutCalls sf writers tup e)
  | .cfContinue e => .cfContinue (rebindMutCalls sf writers tup e)
  | .cfBreakContinue e => .cfBreakContinue (rebindMutCalls sf writers tup e)
  | .typeAscription e ty => .typeAscription (rebindMutCalls sf writers tup e) ty
where
  mapE (sf : StructFieldNames) (writers : List (String × Nat))
      (tup : List (String × List Nat × Bool)) : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => rebindMutCalls sf writers tup e :: mapE sf writers tup es
  mapA (sf : StructFieldNames) (writers : List (String × Nat))
      (tup : List (String × List Nat × Bool)) :
      List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, rebindMutCalls sf writers tup e) :: mapA sf writers tup rest

/-- Untyped twin of `tTupleTail`. -/
def tupleTail (vars : List String) : ImpExpr → Option ImpExpr
  | .letBind n v body => (tupleTail vars body).map fun b => .letBind n v b
  | .seq a b => (tupleTail vars b).map fun b' => .seq a b'
  | .ifThenElse c t f =>
      (tupleTail vars t).bind fun t' => (tupleTail vars f).map fun f' => .ifThenElse c t' f'
  | .match_ s arms => (goA vars arms).map fun arms' => .match_ s arms'
  | .assign _ _ => none
  | .forLoop .. => none
  | .forLoopRev .. => none
  | .whileLoop .. => none
  | .forFold .. => none
  | .forFoldRev .. => none
  | .whileFold .. => none
  | .forFoldReturn .. => none
  | .forFoldRevReturn .. => none
  | .whileFoldReturn .. => none
  | .earlyReturn _ => none
  | .questionMark _ => none
  | .break_ _ => none
  | .continue_ => none
  | .cfBreak _ => none
  | .cfContinue _ => none
  | .cfBreakContinue _ => none
  | e => some (.tuple (e :: vars.map (fun v => .var v)))
where
  goA (vars : List String) :
      List (ImpPat × ImpExpr) → Option (List (ImpPat × ImpExpr))
    | [] => some []
    | (p, e) :: rest =>
      (tupleTail vars e).bind fun e' => (goA vars rest).map fun rest' => (p, e') :: rest'

/-- Untyped twin of `tReturnMutParams`. -/
def returnMutParams (names : List String) (hasRes : Bool) (body : ImpExpr) : ImpExpr :=
  match names with
  | [] => body
  | _ => if hasRes then (tupleTail names body).getD body else replaceTail body (varTuple names)

@[simp] theorem tMutArgRoot_erase (e : TExpr) : tMutArgRoot e = mutArgRoot e.erase := by
  induction e using TExpr.ind with
  | borrow _ _ ih => simpa only [tMutArgRoot, TExpr.erase, mutArgRoot] using ih
  | deref _ _ ih => simpa only [tMutArgRoot, TExpr.erase, mutArgRoot] using ih
  | ann _ _ ih => simpa only [tMutArgRoot, TExpr.erase] using ih
  | _ => rfl

@[simp] theorem tCallWriteback_erase (writers : List (String × Nat)) (f : String)
    (args : List TExpr) :
    tCallWriteback writers f args = callWriteback writers f (args.map TExpr.erase) := by
  simp only [tCallWriteback, callWriteback]
  split
  · rfl
  · cases writers.lookup f with
    | none => rfl
    | some i =>
      cases h : args[i]? with
      | none => simp [h]
      | some a => simp [h, tMutArgRoot_erase]

@[simp] theorem tMutArgField_erase (e : TExpr) : tMutArgField e = mutArgField e.erase := by
  induction e using TExpr.ind with
  | borrow _ _ ih => simpa only [tMutArgField, TExpr.erase, mutArgField] using ih
  | deref _ _ ih => simpa only [tMutArgField, TExpr.erase, mutArgField] using ih
  | ann _ _ ih => simpa only [tMutArgField, TExpr.erase] using ih
  | app ty f args _ =>
    match args with
    | [] => rfl
    | [sE] => simp [tMutArgField, mutArgField, TExpr.erase, tMutArgRoot_erase]
    | _ :: _ :: _ => rfl
  -- `.namedProj T e` erases to the excluded `.0` projection head.
  | namedProj _ _ _ _ => simp [tMutArgField, TExpr.erase, mutArgField]
  | _ => rfl

@[simp] theorem tCallWritebackField_erase (sf : StructFieldNames)
    (writers : List (String × Nat)) (f : String) (args : List TExpr) :
    tCallWritebackField sf writers f args
      = callWritebackField sf writers f (args.map TExpr.erase) := by
  simp only [tCallWritebackField, callWritebackField]
  split
  · rfl
  · cases writers.lookup f with
    | none => rfl
    | some i =>
      cases h : args[i]? with
      | none => simp [h]
      | some a => simp [h, tMutArgField_erase]

@[simp] theorem tRangeBounds_erase (root : String) (e : TExpr) :
    (tRangeBounds root e).map (fun b => (b.1.erase, b.2.erase)) = rangeBounds root e.erase := by
  induction e using TExpr.ind with
  | ann _ _ ih => simpa only [tRangeBounds, TExpr.erase] using ih
  | app ty f args _ =>
    match args with
    | [] => simp [tRangeBounds, rangeBounds, TExpr.erase]
    | [_] =>
      by_cases h : f = "RangeTo"
      · simp [tRangeBounds, rangeBounds, TExpr.erase, h]
      · by_cases h' : f = "RangeFrom" <;>
          simp [tRangeBounds, rangeBounds, TExpr.erase, h, h']
    | [_, _] => by_cases h : f = "Range" <;> simp [tRangeBounds, rangeBounds, TExpr.erase, h]
    | _ :: _ :: _ :: _ => simp [tRangeBounds, rangeBounds, TExpr.erase]
  | _ => rfl

@[simp] theorem tMutArgSlice_erase (e : TExpr) :
    (tMutArgSlice e).map (fun t => (t.1, t.2.1.erase, t.2.2.erase)) = mutArgSlice e.erase := by
  induction e using TExpr.ind with
  | borrow _ _ ih => simpa only [tMutArgSlice, TExpr.erase, mutArgSlice] using ih
  | deref _ _ ih => simpa only [tMutArgSlice, TExpr.erase, mutArgSlice] using ih
  | ann _ _ ih => simpa only [tMutArgSlice, TExpr.erase] using ih
  | app ty f args _ =>
    match args with
    | [] => rfl
    | [_] => rfl
    | [aE, rE] =>
      by_cases h : f = "index_mut"
      · subst h
        simp only [tMutArgSlice, mutArgSlice, TExpr.erase, TExpr.eraseList_eq,
          List.map_cons, List.map_nil, beq_self_eq_true, if_true,
          ← tMutArgRoot_erase, ← tRangeBounds_erase]
        cases tMutArgRoot aE with
        | none => rfl
        | some r => simp only [Option.bind]; cases tRangeBounds r rE <;> rfl
      · simp [tMutArgSlice, mutArgSlice, TExpr.erase, h]
    | _ :: _ :: _ :: _ => rfl
  | namedProj _ _ _ _ => simp [tMutArgSlice, TExpr.erase, mutArgSlice]
  | _ => rfl

@[simp] theorem tCallWritebackSlice_erase (writers : List (String × Nat)) (f : String)
    (args : List TExpr) :
    (tCallWritebackSlice writers f args).map (fun t => (t.1, t.2.1.erase, t.2.2.erase))
      = callWritebackSlice writers f (args.map TExpr.erase) := by
  simp only [tCallWritebackSlice, callWritebackSlice]
  split
  · rfl
  · cases writers.lookup f with
    | none => rfl
    | some i =>
      cases h : args[i]? with
      | none => simp [h]
      | some a => simp [h, ← tMutArgSlice_erase]

@[simp] theorem tRebindCall_erase (sf : StructFieldNames) (writers : List (String × Nat))
    (f : String) (args : List TExpr) (ty : ImpType) :
    (tRebindCall sf writers f args ty).erase
      = rebindCall sf writers f (args.map TExpr.erase) := by
  simp only [tRebindCall, rebindCall, tCallWriteback_erase, tCallWritebackField_erase,
    ← tCallWritebackSlice_erase]
  cases callWriteback writers f (args.map TExpr.erase)
  · cases callWritebackField sf writers f (args.map TExpr.erase)
    · cases tCallWritebackSlice writers f args <;>
        simp [TExpr.erase, TExpr.eraseList_eq]
    · simp [TExpr.erase, TExpr.eraseList_eq]
  · simp [TExpr.erase, TExpr.eraseList_eq]

@[simp] theorem tTupleComp_erase (tup : TExpr) (i n : Nat) :
    (tTupleComp tup i n).erase = tupleComp tup.erase i n := by
  induction i generalizing tup n <;> rcases n with _ | _ | n <;>
    simp_all [tTupleComp, tupleComp, TExpr.erase, TExpr.eraseList_eq]

@[simp] theorem tMutArgRoots_erase (args : List TExpr) (ps : List Nat) :
    tMutArgRoots args ps = mutArgRoots (args.map TExpr.erase) ps := by
  induction ps with
  | nil => rfl
  | cons i is ih =>
    simp only [tMutArgRoots, mutArgRoots, List.getElem?_map, ih]
    cases args[i]? with
    | none => rfl
    | some a => simp [tMutArgRoot_erase]

@[simp] theorem tTupleWriteback_erase (tup : List (String × List Nat × Bool)) (f : String)
    (args : List TExpr) :
    tTupleWriteback tup f args = tupleWriteback tup f (args.map TExpr.erase) := by
  simp only [tTupleWriteback, tupleWriteback, tMutArgRoots_erase]
  rfl

@[simp] theorem tTupleSite_erase (tup : List (String × List Nat × Bool)) (e : TExpr) :
    tTupleSite tup e = tupleSite tup e.erase := by
  induction e using TExpr.ind with
  | app _ _ _ _ => simp [tTupleSite, tupleSite, TExpr.erase, TExpr.eraseList_eq]
  | ann _ _ ih => simpa only [tTupleSite, TExpr.erase] using ih
  | namedProj _ _ _ _ => simp [tTupleSite, tupleSite, tupleWriteback, TExpr.erase]
  | _ => rfl

@[simp] theorem tTupleAssigns_erase (roots : List String) (offset n : Nat) (cont : TExpr) :
    (tTupleAssigns roots offset n cont).erase = tupleAssigns roots offset n cont.erase := by
  induction roots generalizing offset with
  | nil => rfl
  | cons v vs ih => simp [tTupleAssigns, tupleAssigns, TExpr.erase, ih]

@[simp] theorem tTupleResult_erase (roots : List String) (hasRes : Bool) :
    (tTupleResult roots hasRes).erase = tupleResult roots hasRes := by
  cases hasRes <;> simp [tTupleResult, tupleResult, TExpr.erase]

@[simp] theorem tTupleBind_erase (call : TExpr) (roots : List String) (hasRes : Bool)
    (tail : TExpr) :
    (tTupleBind call roots hasRes tail).erase = tupleBind call.erase roots hasRes tail.erase := by
  simp [tTupleBind, tupleBind, TExpr.erase]

/-- Commuting diagram: type erasure commutes with `tRebindMutCalls`. -/
theorem tRebindMutCalls_erase (sf : StructFieldNames) (writers : List (String × Nat))
    (tup : List (String × List Nat × Bool)) (e : TExpr) :
    (tRebindMutCalls sf writers tup e).erase = rebindMutCalls sf writers tup e.erase := by
  apply tRebindMutCalls.induct (sf := sf) (writers := writers) (tup := tup)
    (motive_2 := fun e => (tRebindMutCalls sf writers tup e).erase
                  = rebindMutCalls sf writers tup e.erase)
    (motive_1 := fun es => (tRebindMutCalls.mapE sf writers tup es).map TExpr.erase
                  = rebindMutCalls.mapE sf writers tup (es.map TExpr.erase))
    (motive_3 := fun arms =>
                  (tRebindMutCalls.mapA sf writers tup arms).map (fun pe => (pe.1, pe.2.erase))
                  = rebindMutCalls.mapA sf writers tup (arms.map (fun pe => (pe.1, pe.2.erase))))
  all_goals (try intros)
  all_goals
    first
      | rfl
      | (simp_all [tRebindMutCalls, rebindMutCalls, rebindCall, callWriteback,
          callWritebackField, callWritebackSlice, TExpr.erase,
          tRebindMutCalls.mapE, tRebindMutCalls.mapA, rebindMutCalls.mapE, rebindMutCalls.mapA,
          tRebindCall_erase, TExpr.eraseList_eq, TExpr.eraseArms_eq]; done)
      | (unfold tRebindMutCalls rebindMutCalls
         simp_all [TExpr.erase, tTupleSite_erase]
         all_goals (split <;> simp_all [TExpr.erase, tTupleBind_erase, tTupleResult_erase]))

/-- The arms component of `tTupleTail_erase`. -/
theorem tTupleTail_goA_erase (vars : List String) (arms : List (ImpPat × TExpr))
    (h : ∀ pa ∈ arms, (tTupleTail vars pa.2).map TExpr.erase = tupleTail vars pa.2.erase) :
    (tTupleTail.goA vars arms).map (fun l => l.map (fun pe => (pe.1, pe.2.erase)))
      = tupleTail.goA vars (arms.map (fun pe => (pe.1, pe.2.erase))) := by
  induction arms with
  | nil => rfl
  | cons pa rest ih =>
    obtain ⟨p, e⟩ := pa
    have he := h (p, e) (List.mem_cons_self ..)
    have hr := ih (fun pa hpa => h pa (List.mem_cons_of_mem _ hpa))
    simp only [tTupleTail.goA, tupleTail.goA, List.map_cons, ← he, ← hr]
    cases tTupleTail vars e <;> cases tTupleTail.goA vars rest <;> rfl

@[simp] theorem tTupleTail_erase (vars : List String) (e : TExpr) :
    (tTupleTail vars e).map TExpr.erase = tupleTail vars e.erase := by
  induction e using TExpr.ind with
  | letBind _ _ _ _ _ ih =>
    simp only [tTupleTail, tupleTail, TExpr.erase, ← ih, Option.map_map]
    cases tTupleTail vars _ <;> rfl
  | seq _ _ _ _ ih =>
    simp only [tTupleTail, tupleTail, TExpr.erase, ← ih, Option.map_map]
    cases tTupleTail vars _ <;> rfl
  | ann _ _ ih =>
    simpa only [tTupleTail, TExpr.erase, Option.map_map, Function.comp_def] using ih
  | ifThenElse _ _ _ _ _ iht ihf =>
    simp only [tTupleTail, tupleTail, TExpr.erase, ← iht, ← ihf]
    cases tTupleTail vars _ <;> cases tTupleTail vars _ <;> rfl
  | match_ _ _ arms _ iharms =>
    simp only [tTupleTail, tupleTail, TExpr.erase, TExpr.eraseArms_eq, Option.map_map,
      ← tTupleTail_goA_erase vars arms iharms]
    cases tTupleTail.goA vars arms <;>
      simp [TExpr.erase, TExpr.eraseArms_eq, Function.comp_def]
  | _ =>
    first
      | rfl
      | simp [tTupleTail, tupleTail, TExpr.erase, TExpr.eraseList_eq, List.map_map,
          Function.comp_def]

@[simp] theorem tReturnMutParams_erase (names : List String) (hasRes : Bool) (body : TExpr) :
    (tReturnMutParams names hasRes body).erase = returnMutParams names hasRes body.erase := by
  cases names <;> cases hasRes <;>
    simp [tReturnMutParams, returnMutParams, ← tTupleTail_erase, Option.getD_map]

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
      | .match_ s arms =>
          let used := varRefs rest'
          let m := (assignedVars.goA arms).eraseDups.filter used.contains
          if (!active && !containsLoop rest') || m.isEmpty then
            .seq a' rest'
          else
            let tup := varTuple m
            let matchE := .match_ s (replaceTail.goA arms tup)
            .letBind "_mtup" matchE (destructure m (.var "_mtup") rest')
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
  -- The five `seq` cases (the `if`- or `match`-statement join is detected and
  -- taken, detected and declined, or absent) need the untyped match scrutinee
  -- bridged to the typed one via the IH; every other constructor closes by
  -- `simp_all`.
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
      simp_all [TExpr.erase, tContainsLoop_erase, tReplaceTail_erase, tVarTuple_erase,
        tDestructure_erase]
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
      simp_all [TExpr.erase, tContainsLoop_erase, tReplaceTail_erase, tVarTuple_erase,
        tDestructure_erase]
  case case3 =>
    intro active a rest sty a' rest' s arms mty hx used m hcond ih_a ih_rest
    have hx' : tStripAnn (tThreadMut active a) = .mk (.match_ s arms) mty := hx
    have hau : threadMut active a.erase = (tStripAnn (tThreadMut active a)).erase := by
      rw [tStripAnn_erase]; exact ih_a.symm
    have hbridge : threadMut active a.erase
        = ImpExpr.match_ s.erase (arms.map (fun pe => (pe.1, pe.2.erase))) := by
      simp only [hau, hx', TExpr.erase, TExpr.eraseArms_eq]
    simp only [tThreadMut, threadMut, TExpr.erase, hx', hbridge,
      tContainsLoop_erase, tVarRefs_erase, tAssignedVars_goA_erase, ih_rest]
    split <;>
      simp_all [TExpr.erase, tContainsLoop_erase, tReplaceTail_goA_erase, tVarTuple_erase,
        tDestructure_erase, TExpr.eraseArms_eq]
  case case4 =>
    intro active a rest sty a' rest' s arms mty hx used m hcond ih_a ih_rest
    have hx' : tStripAnn (tThreadMut active a) = .mk (.match_ s arms) mty := hx
    have hau : threadMut active a.erase = (tStripAnn (tThreadMut active a)).erase := by
      rw [tStripAnn_erase]; exact ih_a.symm
    have hbridge : threadMut active a.erase
        = ImpExpr.match_ s.erase (arms.map (fun pe => (pe.1, pe.2.erase))) := by
      simp only [hau, hx', TExpr.erase, TExpr.eraseArms_eq]
    simp only [tThreadMut, threadMut, TExpr.erase, hx', hbridge,
      tContainsLoop_erase, tVarRefs_erase, tAssignedVars_goA_erase, ih_rest]
    split <;>
      simp_all [TExpr.erase, tContainsLoop_erase, tReplaceTail_goA_erase, tVarTuple_erase,
        tDestructure_erase, TExpr.eraseArms_eq]
  case case5 =>
    intro active a rest sty a' hneg hnegm ih_a ih_rest
    have hau : threadMut active a.erase = (tStripAnn (tThreadMut active a)).erase := by
      rw [tStripAnn_erase]; exact ih_a.symm
    simp only [tThreadMut, threadMut, TExpr.erase, hau]
    cases hk : tStripAnn (tThreadMut active a) with
    | mk k kty =>
      cases k <;>
        first
        | exact absurd hk (hneg _ _ _ _)
        | exact absurd hk (hnegm _ _ _)
        | exact absurd hk (tStripAnn_ne_ann _ _ _)
        | (cases ‹Option TExpr› <;> simp_all [TExpr.erase])
        | simp_all [TExpr.erase, TExpr.eraseList_eq]
  all_goals (try intros)
  all_goals
    simp_all [tThreadMut, threadMut, TExpr.erase,
      tThreadMut.mapE, tThreadMut.mapA, threadMut.mapE, threadMut.mapA,
      TExpr.eraseList_eq, TExpr.eraseArms_eq]

end Hax
