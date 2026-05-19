/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.SemanticsCF
import Hax.Phase.CfIntoMonads
import Hax.Phase.FunctionalizeLoopsCF

/-!
# Phase 4 Correctness: Control Flow into Monads

Proves that `cfIntoMonads` preserves denotational semantics (under `denote'`)
up to `Outcome.encodeCF4` encoding (`earlyRet v` → `val (controlFlow true v)`).

## Main results

* `CF4_combined` — simulation theorem for all expressions

## Preconditions

* `NoLoops e` — no `forLoop`, `whileLoop`, `break_`, or `continue_`
* `NoQuestionMark e` — no `questionMark` subexpressions

## Refactored design

With dedicated AST constructors (`cfBreak`, `cfContinue`, `forFold`, etc.),
the `NoReservedApps` precondition is no longer needed. The `app` case in
`CF4_combined` now only handles regular function calls (non-reserved names).
The reserved-name dispatch is handled by dedicated constructor cases
(`cfBreak`, `cfContinue`, `forFold`, `whileFold`, etc.) which unfold to
their corresponding `denote'` semantics directly.
-/

namespace Hax

/-! ### NoQuestionMark predicate -/

/-- An expression contains no `questionMark` nodes. -/
inductive NoQuestionMark : ImpExpr → Prop where
  | lit {v} : NoQuestionMark (.lit v)
  | var {n} : NoQuestionMark (.var n)
  | letBind {n val body} : NoQuestionMark val → NoQuestionMark body →
      NoQuestionMark (.letBind n val body)
  | app {f args} : (∀ a, a ∈ args → NoQuestionMark a) →
      NoQuestionMark (.app f args)
  | tuple {elems} : (∀ a, a ∈ elems → NoQuestionMark a) →
      NoQuestionMark (.tuple elems)
  | proj {e i} : NoQuestionMark e → NoQuestionMark (.proj e i)
  | ifThenElse {c t e} : NoQuestionMark c → NoQuestionMark t → NoQuestionMark e →
      NoQuestionMark (.ifThenElse c t e)
  | match_ {scrut arms} : NoQuestionMark scrut →
      (∀ pa, pa ∈ arms → NoQuestionMark pa.2) →
      NoQuestionMark (.match_ scrut arms)
  | unitVal : NoQuestionMark .unitVal
  | seq {e1 e2} : NoQuestionMark e1 → NoQuestionMark e2 →
      NoQuestionMark (.seq e1 e2)
  | borrow {e} : NoQuestionMark e → NoQuestionMark (.borrow e)
  | deref {e} : NoQuestionMark e → NoQuestionMark (.deref e)
  | assign {n rhs} : NoQuestionMark rhs → NoQuestionMark (.assign n rhs)
  | forLoop {v lo hi body} : NoQuestionMark lo → NoQuestionMark hi →
      NoQuestionMark body → NoQuestionMark (.forLoop v lo hi body)
  | forLoopRev {v lo hi body} : NoQuestionMark lo → NoQuestionMark hi →
      NoQuestionMark body → NoQuestionMark (.forLoopRev v lo hi body)
  | whileLoop {c body} : NoQuestionMark c → NoQuestionMark body →
      NoQuestionMark (.whileLoop c body)
  | break_some {e} : NoQuestionMark e → NoQuestionMark (.break_ (some e))
  | break_none : NoQuestionMark (.break_ none)
  | continue_ : NoQuestionMark .continue_
  | earlyReturn {e} : NoQuestionMark e → NoQuestionMark (.earlyReturn e)
  | forFold {v lo hi body} : NoQuestionMark lo → NoQuestionMark hi →
      NoQuestionMark body → NoQuestionMark (.forFold v lo hi body)
  | forFoldRev {v lo hi body} : NoQuestionMark lo → NoQuestionMark hi →
      NoQuestionMark body → NoQuestionMark (.forFoldRev v lo hi body)
  | whileFold {c body} : NoQuestionMark c → NoQuestionMark body →
      NoQuestionMark (.whileFold c body)
  | forFoldReturn {v lo hi body} : NoQuestionMark lo → NoQuestionMark hi →
      NoQuestionMark body → NoQuestionMark (.forFoldReturn v lo hi body)
  | forFoldRevReturn {v lo hi body} : NoQuestionMark lo → NoQuestionMark hi →
      NoQuestionMark body → NoQuestionMark (.forFoldRevReturn v lo hi body)
  | whileFoldReturn {c body} : NoQuestionMark c → NoQuestionMark body →
      NoQuestionMark (.whileFoldReturn c body)
  | cfBreak {e} : NoQuestionMark e → NoQuestionMark (.cfBreak e)
  | cfContinue {e} : NoQuestionMark e → NoQuestionMark (.cfContinue e)
  | cfBreakContinue {e} : NoQuestionMark e → NoQuestionMark (.cfBreakContinue e)
  | typeAscription {e tyStr} : NoQuestionMark e → NoQuestionMark (.typeAscription e tyStr)

theorem NoQuestionMark.not_questionMark {e : ImpExpr} :
    ¬NoQuestionMark (.questionMark e) := by intro h; cases h

/-! ### WellFormedFolds predicate -/

/-- All `forFold`/`whileFold` bodies in an expression satisfy `NoEarlyExit`.
    This holds for the output of `functionalizeLoops` (Phase 3), which creates
    `forFold` only when `checkNoEarlyExit body = true`. -/
inductive WellFormedFolds : ImpExpr → Prop where
  | lit {v} : WellFormedFolds (.lit v)
  | var {n} : WellFormedFolds (.var n)
  | letBind {n val body} : WellFormedFolds val → WellFormedFolds body →
      WellFormedFolds (.letBind n val body)
  | app {f args} : (∀ a, a ∈ args → WellFormedFolds a) →
      WellFormedFolds (.app f args)
  | tuple {elems} : (∀ a, a ∈ elems → WellFormedFolds a) →
      WellFormedFolds (.tuple elems)
  | proj {e i} : WellFormedFolds e → WellFormedFolds (.proj e i)
  | ifThenElse {c t e} : WellFormedFolds c → WellFormedFolds t → WellFormedFolds e →
      WellFormedFolds (.ifThenElse c t e)
  | match_ {scrut arms} : WellFormedFolds scrut →
      (∀ pa, pa ∈ arms → WellFormedFolds pa.2) →
      WellFormedFolds (.match_ scrut arms)
  | unitVal : WellFormedFolds .unitVal
  | seq {e1 e2} : WellFormedFolds e1 → WellFormedFolds e2 →
      WellFormedFolds (.seq e1 e2)
  | borrow {e} : WellFormedFolds e → WellFormedFolds (.borrow e)
  | deref {e} : WellFormedFolds e → WellFormedFolds (.deref e)
  | assign {n rhs} : WellFormedFolds rhs → WellFormedFolds (.assign n rhs)
  | forLoop {v lo hi body} : WellFormedFolds lo → WellFormedFolds hi →
      WellFormedFolds body → WellFormedFolds (.forLoop v lo hi body)
  | forLoopRev {v lo hi body} : WellFormedFolds lo → WellFormedFolds hi →
      WellFormedFolds body → WellFormedFolds (.forLoopRev v lo hi body)
  | whileLoop {c body} : WellFormedFolds c → WellFormedFolds body →
      WellFormedFolds (.whileLoop c body)
  | break_some {e} : WellFormedFolds e → WellFormedFolds (.break_ (some e))
  | break_none : WellFormedFolds (.break_ none)
  | continue_ : WellFormedFolds .continue_
  | earlyReturn {e} : WellFormedFolds e → WellFormedFolds (.earlyReturn e)
  | questionMark {e} : WellFormedFolds e → WellFormedFolds (.questionMark e)
  | forFold {v lo hi body} : WellFormedFolds lo → WellFormedFolds hi →
      WellFormedFolds body → NoEarlyExit body →
      WellFormedFolds (.forFold v lo hi body)
  | forFoldRev {v lo hi body} : WellFormedFolds lo → WellFormedFolds hi →
      WellFormedFolds body → NoEarlyExit body →
      WellFormedFolds (.forFoldRev v lo hi body)
  | whileFold {c body} : WellFormedFolds c → WellFormedFolds body →
      NoEarlyExit body → WellFormedFolds (.whileFold c body)
  | forFoldReturn {v lo hi body} : WellFormedFolds lo → WellFormedFolds hi →
      WellFormedFolds body → WellFormedFolds (.forFoldReturn v lo hi body)
  | forFoldRevReturn {v lo hi body} : WellFormedFolds lo → WellFormedFolds hi →
      WellFormedFolds body → WellFormedFolds (.forFoldRevReturn v lo hi body)
  | whileFoldReturn {c body} : WellFormedFolds c → WellFormedFolds body →
      WellFormedFolds (.whileFoldReturn c body)
  | cfBreak {e} : WellFormedFolds e → WellFormedFolds (.cfBreak e)
  | cfContinue {e} : WellFormedFolds e → WellFormedFolds (.cfContinue e)
  | cfBreakContinue {e} : WellFormedFolds e → WellFormedFolds (.cfBreakContinue e)
  | typeAscription {e tyStr} : WellFormedFolds e → WellFormedFolds (.typeAscription e tyStr)

/-! ### Helper: denoteArgs' commutes with cfIntoMonads -/

/-- `denoteArgs'` gives the same result with `cfIntoMonads`-mapped args.
    This is because `encodeCF4` maps `earlyRet` to `val(controlFlow)`,
    and `denoteArgs'` rejects both `earlyRet` (non-val) and
    `val(controlFlow)` (CF val) equally, returning `none`. -/
private theorem denoteArgs'_cfIntoMonads (bi : Builtins) (fuel : Nat)
    (args : List ImpExpr)
    (ih : ∀ a, a ∈ args → ∀ env, denote' bi fuel (cfIntoMonads a) env =
      (Outcome.encodeCF4 (denote' bi fuel a env).1, (denote' bi fuel a env).2)) :
    ∀ env, denoteArgs' bi fuel (args.map cfIntoMonads) env =
      denoteArgs' bi fuel args env := by
  induction args with
  | nil => intro env; rfl
  | cons e es ih_es =>
    intro env
    simp only [List.map_cons]
    unfold denoteArgs'
    simp only [bind, StateT.bind]
    rw [ih e (.head _) env]
    generalize denote' bi fuel e env = pe
    obtain ⟨re, enve⟩ := pe
    cases re with
    | val v =>
      simp only [Outcome.encodeCF4]
      cases v with
      | controlFlow => rfl
      | _ =>
        have h : denoteArgs' bi fuel (es.map cfIntoMonads) = denoteArgs' bi fuel es :=
          funext fun env' => ih_es (fun a ha => ih a (.tail _ ha)) env'
        rw [h]
    | earlyRet => simp [Outcome.encodeCF4]
    | err => rfl
    | broke => rfl
    | continued => rfl

/-! ### Helper: denoteMatchArms' commutes with cfIntoMonads up to encodeCF4 -/

/-- `denoteMatchArms'` with `cfIntoMonads`-mapped arms gives `encodeCF4` of
    the original result. -/
private theorem denoteMatchArms'_cfIntoMonads (bi : Builtins) (fuel : Nat)
    (v : Value) (arms : List (ImpPat × ImpExpr))
    (ih : ∀ pa, pa ∈ arms → ∀ env, denote' bi fuel (cfIntoMonads pa.2) env =
      (Outcome.encodeCF4 (denote' bi fuel pa.2 env).1, (denote' bi fuel pa.2 env).2)) :
    ∀ env, denoteMatchArms' bi fuel v (arms.map fun (p, e) => (p, cfIntoMonads e)) env =
      (Outcome.encodeCF4 (denoteMatchArms' bi fuel v arms env).1,
       (denoteMatchArms' bi fuel v arms env).2) := by
  induction arms with
  | nil =>
    intro env
    unfold denoteMatchArms'
    rfl
  | cons pa arms ih_arms =>
    intro env
    obtain ⟨pat, body⟩ := pa
    simp only [List.map_cons]
    unfold denoteMatchArms'
    simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get]
    cases hm : matchPat pat v env with
    | some env' =>
      simp only [hm, set, StateT.set, bind, StateT.bind]
      exact ih (pat, body) (.head _) env'
    | none =>
      simp only [hm]
      exact ih_arms (fun pa' hpa' => ih pa' (.tail _ hpa')) env

/-! ### Helper: encodeCF4 is identity on non-earlyRet outcomes -/

private theorem Outcome.encodeCF4_id_of_not_earlyRet (o : Outcome)
    (h : ∀ v, o ≠ .earlyRet v) : encodeCF4 o = o := by
  cases o with
  | earlyRet v => exact absurd rfl (h v)
  | _ => rfl

/-! ### Invariant: earlyRet values are never controlFlow -/

/-- `denoteForLoop'` earlyRet invariant: if the body preserves the invariant,
    so does the loop. -/
private theorem denoteForLoop'_earlyRet_not_cf (bi : Builtins) (body : ImpExpr)
    (hbody : ∀ fuel env v, (denote' bi fuel body env).1 = .earlyRet v → v.isControlFlow = false)
    (fuel : Nat) (var : String) (lo hi : Int) :
    ∀ env v, (denoteForLoop' bi fuel var lo hi body env).1 = .earlyRet v →
      v.isControlFlow = false := by
  induction fuel generalizing lo with
  | zero =>
    intro env v; unfold denoteForLoop'; split
    · simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    · simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | succ n ih =>
    intro env v
    unfold denoteForLoop'
    by_cases hge : lo ≥ hi
    · simp only [if_pos hge, pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    · simp only [if_neg hge, show ¬(n + 1 = 0) from by omega, ↓reduceIte]
      dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
      generalize heqb : denote' bi (n + 1) body (Env.extend env var (.int lo)) = pb
      obtain ⟨rb, envb⟩ := pb
      cases rb with
      | val vb =>
        cases vb with
        | controlFlow isBreak w =>
          cases isBreak with
          | true => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
          | false => simp only [show n + 1 - 1 = n from rfl]; exact ih (lo + 1) envb v
        | _ => simp only [show n + 1 - 1 = n from rfl]; exact ih (lo + 1) envb v
      | earlyRet w =>
        intro h; have := Outcome.earlyRet.inj h; subst this
        exact hbody (n + 1) _ _ (by rw [heqb])
      | err => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
      | broke => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
      | continued => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h

/-- `denoteForLoopRev'` earlyRet invariant. -/
private theorem denoteForLoopRev'_earlyRet_not_cf (bi : Builtins) (body : ImpExpr)
    (hbody : ∀ fuel env v, (denote' bi fuel body env).1 = .earlyRet v → v.isControlFlow = false)
    (fuel : Nat) (var : String) (lo hi : Int) :
    ∀ env v, (denoteForLoopRev' bi fuel var lo hi body env).1 = .earlyRet v →
      v.isControlFlow = false := by
  induction fuel generalizing hi with
  | zero =>
    intro env v; unfold denoteForLoopRev'; split
    · simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    · simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | succ n ih =>
    intro env v
    unfold denoteForLoopRev'
    by_cases hge : lo ≥ hi
    · simp only [if_pos hge, pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    · simp only [if_neg hge, show ¬(n + 1 = 0) from by omega, ↓reduceIte]
      dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
      generalize heqb : denote' bi (n + 1) body (Env.extend env var (.int (hi - 1))) = pb
      obtain ⟨rb, envb⟩ := pb
      cases rb with
      | val vb =>
        cases vb with
        | controlFlow isBreak w =>
          cases isBreak with
          | true => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
          | false => simp only [show n + 1 - 1 = n from rfl]; exact ih (hi - 1) envb v
        | _ => simp only [show n + 1 - 1 = n from rfl]; exact ih (hi - 1) envb v
      | earlyRet w =>
        intro h; have := Outcome.earlyRet.inj h; subst this
        exact hbody (n + 1) _ _ (by rw [heqb])
      | err => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
      | broke => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
      | continued => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h

/-- `denoteWhile'` earlyRet invariant. -/
private theorem denoteWhile'_earlyRet_not_cf (bi : Builtins) (cond body : ImpExpr)
    (hcond : ∀ fuel env v, (denote' bi fuel cond env).1 = .earlyRet v → v.isControlFlow = false)
    (hbody : ∀ fuel env v, (denote' bi fuel body env).1 = .earlyRet v → v.isControlFlow = false)
    (fuel : Nat) :
    ∀ env v, (denoteWhile' bi fuel cond body env).1 = .earlyRet v →
      v.isControlFlow = false := by
  induction fuel with
  | zero =>
    intro env v; unfold denoteWhile'
    simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | succ n ih =>
    intro env v
    unfold denoteWhile'
    simp only [show ¬(n + 1 = 0) from by omega, ↓reduceIte, bind, StateT.bind]
    generalize heqc : denote' bi (n + 1) cond env = pc
    obtain ⟨rc, envc⟩ := pc
    cases rc with
    | val vc =>
      cases vc with
      | controlFlow =>
        simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | bool b =>
        cases b with
        | true =>
          simp only [bind, StateT.bind]
          generalize heqb : denote' bi (n + 1) body envc = pb
          obtain ⟨rb, envb⟩ := pb
          cases rb with
          | val vb =>
            cases vb with
            | controlFlow isBreak w =>
              cases isBreak with
              | true =>
                simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
              | false => simp only [show n + 1 - 1 = n from rfl]; exact ih envb v
            | _ => simp only [show n + 1 - 1 = n from rfl]; exact ih envb v
          | earlyRet w =>
            intro h; have := Outcome.earlyRet.inj h; subst this
            exact hbody (n + 1) envc _ (by rw [heqb])
          | err =>
            simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
          | broke =>
            simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
          | continued =>
            simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | false =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | earlyRet w =>
      simp only [pure, Pure.pure, StateT.pure]; intro h
      have := Outcome.earlyRet.inj h; subst this; exact hcond (n + 1) env _ (by rw [heqc])
    | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h

/-- `denoteForLoopOrig'` earlyRet invariant. -/
private theorem denoteForLoopOrig'_earlyRet_not_cf (bi : Builtins) (body : ImpExpr)
    (hbody : ∀ fuel env v, (denote' bi fuel body env).1 = .earlyRet v → v.isControlFlow = false)
    (fuel : Nat) (var : String) (lo hi : Int) :
    ∀ env v, (denoteForLoopOrig' bi fuel var lo hi body env).1 = .earlyRet v →
      v.isControlFlow = false := by
  induction fuel generalizing lo with
  | zero =>
    intro env v; unfold denoteForLoopOrig'; split
    · simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    · simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | succ n ih =>
    intro env v
    unfold denoteForLoopOrig'
    by_cases hge : lo ≥ hi
    · simp only [if_pos hge, pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    · simp only [if_neg hge, show ¬(n + 1 = 0) from by omega, ↓reduceIte]
      dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
      generalize heqb : denote' bi (n + 1) body (Env.extend env var (.int lo)) = pb
      obtain ⟨rb, envb⟩ := pb
      cases rb with
      | val _ => simp only [show n + 1 - 1 = n from rfl]; exact ih (lo + 1) envb v
      | earlyRet w =>
        intro h; have := Outcome.earlyRet.inj h; subst this
        exact hbody (n + 1) _ _ (by rw [heqb])
      | err => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
      | broke => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
      | continued => simp only [show n + 1 - 1 = n from rfl]; exact ih (lo + 1) envb v

/-- `denoteForLoopRevOrig'` earlyRet invariant. -/
private theorem denoteForLoopRevOrig'_earlyRet_not_cf (bi : Builtins) (body : ImpExpr)
    (hbody : ∀ fuel env v, (denote' bi fuel body env).1 = .earlyRet v → v.isControlFlow = false)
    (fuel : Nat) (var : String) (lo hi : Int) :
    ∀ env v, (denoteForLoopRevOrig' bi fuel var lo hi body env).1 = .earlyRet v →
      v.isControlFlow = false := by
  induction fuel generalizing hi with
  | zero =>
    intro env v; unfold denoteForLoopRevOrig'; split
    · simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    · simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | succ n ih =>
    intro env v
    unfold denoteForLoopRevOrig'
    by_cases hge : lo ≥ hi
    · simp only [if_pos hge, pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    · simp only [if_neg hge, show ¬(n + 1 = 0) from by omega, ↓reduceIte]
      dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
      generalize heqb : denote' bi (n + 1) body (Env.extend env var (.int (hi - 1))) = pb
      obtain ⟨rb, envb⟩ := pb
      cases rb with
      | val _ => simp only [show n + 1 - 1 = n from rfl]; exact ih (hi - 1) envb v
      | earlyRet w =>
        intro h; have := Outcome.earlyRet.inj h; subst this
        exact hbody (n + 1) _ _ (by rw [heqb])
      | err => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
      | broke => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
      | continued => simp only [show n + 1 - 1 = n from rfl]; exact ih (hi - 1) envb v

/-- `denoteWhileOrig'` earlyRet invariant. -/
private theorem denoteWhileOrig'_earlyRet_not_cf (bi : Builtins) (cond body : ImpExpr)
    (hcond : ∀ fuel env v, (denote' bi fuel cond env).1 = .earlyRet v → v.isControlFlow = false)
    (hbody : ∀ fuel env v, (denote' bi fuel body env).1 = .earlyRet v → v.isControlFlow = false)
    (fuel : Nat) :
    ∀ env v, (denoteWhileOrig' bi fuel cond body env).1 = .earlyRet v →
      v.isControlFlow = false := by
  induction fuel with
  | zero =>
    intro env v; unfold denoteWhileOrig'
    simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | succ n ih =>
    intro env v
    unfold denoteWhileOrig'
    simp only [show ¬(n + 1 = 0) from by omega, ↓reduceIte, bind, StateT.bind]
    generalize heqc : denote' bi (n + 1) cond env = pc
    obtain ⟨rc, envc⟩ := pc
    cases rc with
    | val vc =>
      cases vc with
      | bool b =>
        cases b with
        | true =>
          simp only [bind, StateT.bind]
          generalize heqb : denote' bi (n + 1) body envc = pb
          obtain ⟨rb, envb⟩ := pb
          cases rb with
          | val _ => simp only [show n + 1 - 1 = n from rfl]; exact ih envb v
          | earlyRet w =>
            intro h; have := Outcome.earlyRet.inj h; subst this
            exact hbody (n + 1) envc _ (by rw [heqb])
          | err =>
            simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
          | broke =>
            simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
          | continued => simp only [show n + 1 - 1 = n from rfl]; exact ih envb v
        | false =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | earlyRet w =>
      simp only [pure, Pure.pure, StateT.pure]; intro h
      have := Outcome.earlyRet.inj h; subst this; exact hcond (n + 1) env _ (by rw [heqc])
    | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h

/-- `denoteForLoop'Return` earlyRet invariant. -/
private theorem denoteForLoop'Return_earlyRet_not_cf (bi : Builtins) (body : ImpExpr)
    (hbody : ∀ fuel env v, (denote' bi fuel body env).1 = .earlyRet v → v.isControlFlow = false)
    (fuel : Nat) (var : String) (lo hi : Int) :
    ∀ env v, (denoteForLoop'Return bi fuel var lo hi body env).1 = .earlyRet v →
      v.isControlFlow = false := by
  induction fuel generalizing lo with
  | zero =>
    intro env v; unfold denoteForLoop'Return; split
    · simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    · simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | succ n ih =>
    intro env v
    unfold denoteForLoop'Return
    by_cases hge : lo ≥ hi
    · simp only [if_pos hge, pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    · simp only [if_neg hge, show ¬(n + 1 = 0) from by omega, ↓reduceIte]
      dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
      generalize heqb : denote' bi (n + 1) body (Env.extend env var (.int lo)) = pb
      obtain ⟨rb, envb⟩ := pb
      cases rb with
      | val vb =>
        cases vb with
        | controlFlow isBreak w =>
          cases isBreak with
          | true =>
            cases w with
            | controlFlow isBreak2 w2 =>
              cases isBreak2 with
              | true =>
                simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
              | false =>
                simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
            | _ =>
              simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
          | false => simp only [show n + 1 - 1 = n from rfl]; exact ih (lo + 1) envb v
        | _ => simp only [show n + 1 - 1 = n from rfl]; exact ih (lo + 1) envb v
      | earlyRet w =>
        intro h; have := Outcome.earlyRet.inj h; subst this
        exact hbody (n + 1) _ _ (by rw [heqb])
      | err => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
      | broke => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
      | continued => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h

/-- `denoteWhile'Return` earlyRet invariant. -/
private theorem denoteWhile'Return_earlyRet_not_cf (bi : Builtins) (cond body : ImpExpr)
    (hcond : ∀ fuel env v, (denote' bi fuel cond env).1 = .earlyRet v → v.isControlFlow = false)
    (hbody : ∀ fuel env v, (denote' bi fuel body env).1 = .earlyRet v → v.isControlFlow = false)
    (fuel : Nat) :
    ∀ env v, (denoteWhile'Return bi fuel cond body env).1 = .earlyRet v →
      v.isControlFlow = false := by
  induction fuel with
  | zero =>
    intro env v; unfold denoteWhile'Return
    simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | succ n ih =>
    intro env v
    unfold denoteWhile'Return
    simp only [show ¬(n + 1 = 0) from by omega, ↓reduceIte, bind, StateT.bind]
    generalize heqc : denote' bi (n + 1) cond env = pc
    obtain ⟨rc, envc⟩ := pc
    cases rc with
    | val vc =>
      cases vc with
      | controlFlow =>
        simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | bool b =>
        cases b with
        | true =>
          simp only [bind, StateT.bind]
          generalize heqb : denote' bi (n + 1) body envc = pb
          obtain ⟨rb, envb⟩ := pb
          cases rb with
          | val vb =>
            cases vb with
            | controlFlow isBreak w =>
              cases isBreak with
              | true =>
                cases w with
                | controlFlow isBreak2 w2 =>
                  cases isBreak2 with
                  | true =>
                    simp only [pure, Pure.pure, StateT.pure]
                    intro h; exact Outcome.noConfusion h
                  | false =>
                    simp only [pure, Pure.pure, StateT.pure]
                    intro h; exact Outcome.noConfusion h
                | _ =>
                  simp only [pure, Pure.pure, StateT.pure]
                  intro h; exact Outcome.noConfusion h
              | false => simp only [show n + 1 - 1 = n from rfl]; exact ih envb v
            | _ => simp only [show n + 1 - 1 = n from rfl]; exact ih envb v
          | earlyRet w =>
            intro h; have := Outcome.earlyRet.inj h; subst this
            exact hbody (n + 1) envc _ (by rw [heqb])
          | err =>
            simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
          | broke =>
            simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
          | continued =>
            simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | false =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | earlyRet w =>
      simp only [pure, Pure.pure, StateT.pure]; intro h
      have := Outcome.earlyRet.inj h; subst this; exact hcond (n + 1) env _ (by rw [heqc])
    | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h

/-- `denoteForLoopRev'Return` earlyRet invariant. -/
private theorem denoteForLoopRev'Return_earlyRet_not_cf (bi : Builtins) (body : ImpExpr)
    (hbody : ∀ fuel env v, (denote' bi fuel body env).1 = .earlyRet v → v.isControlFlow = false)
    (fuel : Nat) (var : String) (lo hi : Int) :
    ∀ env v, (denoteForLoopRev'Return bi fuel var lo hi body env).1 = .earlyRet v →
      v.isControlFlow = false := by
  induction fuel generalizing hi with
  | zero =>
    intro env v; unfold denoteForLoopRev'Return; split
    · simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    · simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | succ n ih =>
    intro env v
    unfold denoteForLoopRev'Return
    by_cases hge : lo ≥ hi
    · simp only [if_pos hge, pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    · simp only [if_neg hge, show ¬(n + 1 = 0) from by omega, ↓reduceIte]
      dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
      generalize heqb : denote' bi (n + 1) body (Env.extend env var (.int (hi - 1))) = pb
      obtain ⟨rb, envb⟩ := pb
      cases rb with
      | val vb =>
        cases vb with
        | controlFlow isBreak w =>
          cases isBreak with
          | true =>
            cases w with
            | controlFlow isBreak2 w2 =>
              cases isBreak2 with
              | true =>
                simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
              | false =>
                simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
            | _ =>
              simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
          | false => simp only [show n + 1 - 1 = n from rfl]; exact ih (hi - 1) envb v
        | _ => simp only [show n + 1 - 1 = n from rfl]; exact ih (hi - 1) envb v
      | earlyRet w =>
        intro h; have := Outcome.earlyRet.inj h; subst this
        exact hbody (n + 1) _ _ (by rw [heqb])
      | err => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
      | broke => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
      | continued => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h

/-- `denoteMatchArms'` earlyRet invariant. -/
private theorem denoteMatchArms'_earlyRet_not_cf (bi : Builtins) (fuel : Nat)
    (v : Value) (arms : List (ImpPat × ImpExpr))
    (ih : ∀ pa, pa ∈ arms → ∀ env w,
      (denote' bi fuel pa.2 env).1 = .earlyRet w → w.isControlFlow = false) :
    ∀ env w, (denoteMatchArms' bi fuel v arms env).1 = .earlyRet w →
      w.isControlFlow = false := by
  induction arms with
  | nil =>
    intro env w; unfold denoteMatchArms'
    simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | cons pa rest ih_rest =>
    intro env w
    obtain ⟨pat, body⟩ := pa
    unfold denoteMatchArms'
    simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get]
    cases hm : matchPat pat v env with
    | some env' =>
      simp only [hm, set, StateT.set, bind, StateT.bind]
      exact ih (pat, body) (.head _) env' w
    | none =>
      simp only [hm]
      exact ih_rest (fun pa' hpa' => ih pa' (.tail _ hpa')) env w

/-- Main invariant: if `denote'` produces `earlyRet v`, then `v.isControlFlow = false`.
    This is because `earlyReturn e` only wraps non-CF values as earlyRet,
    and `questionMark e` wraps `result false v` which is non-CF. -/
theorem denote'_earlyRet_not_cf (bi : Builtins) (e : ImpExpr) :
    ∀ fuel env v, (denote' bi fuel e env).1 = .earlyRet v → v.isControlFlow = false := by
  induction e using ImpExpr.ind with
  | lit v =>
    intro fuel env w; unfold denote'
    simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | var n =>
    intro fuel env w; unfold denote'
    simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get]
    cases env n <;> (simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h)
  | unitVal =>
    intro fuel env w; unfold denote'
    simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | letBind n val body ih_val ih_body =>
    intro fuel env w; unfold denote'
    simp only [bind, StateT.bind]
    generalize heqv : denote' bi fuel val env = pv
    obtain ⟨rv, envv⟩ := pv
    cases rv with
    | val v =>
      cases v with
      | controlFlow =>
        simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ =>
        simp only [modify, modifyGet, MonadStateOf.modifyGet]
        exact ih_body fuel _ w
    | earlyRet w' =>
      simp only [pure, Pure.pure, StateT.pure]; intro h
      have := Outcome.earlyRet.inj h; subst this; exact ih_val fuel env _ (by rw [heqv])
    | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | seq e1 e2 ih1 ih2 =>
    intro fuel env w; unfold denote'
    simp only [bind, StateT.bind]
    generalize heq1 : denote' bi fuel e1 env = p1
    obtain ⟨r1, env1⟩ := p1
    cases r1 with
    | val v =>
      cases v with
      | controlFlow =>
        simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ => exact ih2 fuel _ w
    | earlyRet w' =>
      simp only [pure, Pure.pure, StateT.pure]; intro h
      have := Outcome.earlyRet.inj h; subst this; exact ih1 fuel env _ (by rw [heq1])
    | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | proj e i ih =>
    intro fuel env w; unfold denote'
    simp only [bind, StateT.bind]
    generalize heqe : denote' bi fuel e env = pe
    obtain ⟨re, enve⟩ := pe
    cases re with
    | val v =>
      cases v with
      | controlFlow =>
        simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ =>
        dsimp only []; cases Value.projIdx _ i <;>
          (simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h)
    | earlyRet w' =>
      simp only [pure, Pure.pure, StateT.pure]; intro h
      have := Outcome.earlyRet.inj h; subst this; exact ih fuel env _ (by rw [heqe])
    | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | ifThenElse c t el ih_c ih_t ih_e =>
    intro fuel env w; unfold denote'
    simp only [bind, StateT.bind]
    generalize heqc : denote' bi fuel c env = pc
    obtain ⟨rc, envc⟩ := pc
    cases rc with
    | val v =>
      cases v with
      | controlFlow =>
        simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | bool b =>
        cases b with
        | true => exact ih_t fuel _ w
        | false => exact ih_e fuel _ w
      | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | earlyRet w' =>
      simp only [pure, Pure.pure, StateT.pure]; intro h
      have := Outcome.earlyRet.inj h; subst this; exact ih_c fuel env _ (by rw [heqc])
    | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | match_ scrut arms ih_scrut ih_arms =>
    intro fuel env w; unfold denote'
    simp only [bind, StateT.bind]
    generalize heqs : denote' bi fuel scrut env = ps
    obtain ⟨rs, envs⟩ := ps
    cases rs with
    | val v =>
      cases v with
      | controlFlow =>
        simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ =>
        exact denoteMatchArms'_earlyRet_not_cf bi fuel _ arms
          (fun pa hpa => ih_arms pa hpa fuel) envs w
    | earlyRet w' =>
      simp only [pure, Pure.pure, StateT.pure]; intro h
      have := Outcome.earlyRet.inj h; subst this; exact ih_scrut fuel env _ (by rw [heqs])
    | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | assign n rhs ih =>
    intro fuel env w; unfold denote'
    simp only [bind, StateT.bind]
    generalize heqr : denote' bi fuel rhs env = pr
    obtain ⟨rr, envr⟩ := pr
    cases rr with
    | val v =>
      cases v with
      | controlFlow =>
        simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ =>
        simp only [modify, modifyGet, MonadStateOf.modifyGet]
        simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | earlyRet w' =>
      simp only [pure, Pure.pure, StateT.pure]; intro h
      have := Outcome.earlyRet.inj h; subst this; exact ih fuel env _ (by rw [heqr])
    | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | borrow e ih =>
    intro fuel env w; unfold denote'; exact ih fuel env w
  | deref e ih =>
    intro fuel env w; unfold denote'; exact ih fuel env w
  | app f args ih =>
    intro fuel env w; unfold denote'; unfold denoteApp'
    simp only [bind, StateT.bind]
    generalize denoteArgs' bi fuel args env = pa
    obtain ⟨ma, enva⟩ := pa
    cases ma with
    | some vals =>
      dsimp only []; cases bi f vals <;>
        (simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h)
    | none =>
      simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | tuple elems ih =>
    intro fuel env w; unfold denote'
    simp only [bind, StateT.bind]
    generalize denoteArgs' bi fuel elems env = pa
    obtain ⟨ma, enva⟩ := pa
    cases ma <;>
      (simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h)
  | earlyReturn e ih =>
    intro fuel env w; unfold denote'
    simp only [bind, StateT.bind]
    generalize heqe : denote' bi fuel e env = pe
    obtain ⟨re, enve⟩ := pe
    cases re with
    | val v =>
      simp only [pure, Pure.pure, StateT.pure]
      cases v with
      | controlFlow => intro h; exact Outcome.noConfusion h
      | bool => intro h; have := Outcome.earlyRet.inj h; subst this; rfl
      | int => intro h; have := Outcome.earlyRet.inj h; subst this; rfl
      | uint => intro h; have := Outcome.earlyRet.inj h; subst this; rfl
      | sint => intro h; have := Outcome.earlyRet.inj h; subst this; rfl
      | unit => intro h; have := Outcome.earlyRet.inj h; subst this; rfl
      | tuple => intro h; have := Outcome.earlyRet.inj h; subst this; rfl
      | array => intro h; have := Outcome.earlyRet.inj h; subst this; rfl
      | option => intro h; have := Outcome.earlyRet.inj h; subst this; rfl
      | result => intro h; have := Outcome.earlyRet.inj h; subst this; rfl
    | earlyRet w' =>
      simp only [pure, Pure.pure, StateT.pure]; intro h
      have := Outcome.earlyRet.inj h; subst this; exact ih fuel env _ (by rw [heqe])
    | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | questionMark e ih =>
    intro fuel env w; unfold denote'
    simp only [bind, StateT.bind]
    generalize heqe : denote' bi fuel e env = pe
    obtain ⟨re, enve⟩ := pe
    cases re with
    | val v =>
      simp only [pure, Pure.pure, StateT.pure]
      cases v with
      | controlFlow => intro h; exact Outcome.noConfusion h
      | result ok v =>
        cases ok with
        | true => intro h; exact Outcome.noConfusion h
        | false => intro h; have := Outcome.earlyRet.inj h; subst this; rfl
      | _ => intro h; exact Outcome.noConfusion h
    | earlyRet w' =>
      simp only [pure, Pure.pure, StateT.pure]; intro h
      have := Outcome.earlyRet.inj h; subst this; exact ih fuel env _ (by rw [heqe])
    | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | forLoop var lo hi body ih_lo ih_hi ih_body =>
    intro fuel env w; unfold denote'
    simp only [bind, StateT.bind]
    generalize heqlo : denote' bi fuel lo env = plo
    obtain ⟨rlo, envlo⟩ := plo
    dsimp only []
    generalize heqhi : denote' bi fuel hi envlo = phi
    obtain ⟨rhi, envhi⟩ := phi
    dsimp only []
    cases rlo with
    | val vlo =>
      cases rhi with
      | val vhi =>
        cases vlo with
        | int lo_val =>
          cases vhi with
          | int hi_val =>
            exact denoteForLoopOrig'_earlyRet_not_cf bi body ih_body fuel var lo_val hi_val envhi w
          | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | _ =>
          cases vhi <;>
            (simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h)
      | earlyRet w' =>
        simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | earlyRet w' =>
      simp only [pure, Pure.pure, StateT.pure]; intro h
      have := Outcome.earlyRet.inj h; subst this; exact ih_lo fuel env _ (by rw [heqlo])
    | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | forLoopRev var lo hi body ih_lo ih_hi ih_body =>
    intro fuel env w; unfold denote'
    simp only [bind, StateT.bind]
    generalize heqlo : denote' bi fuel lo env = plo
    obtain ⟨rlo, envlo⟩ := plo
    dsimp only []
    generalize heqhi : denote' bi fuel hi envlo = phi
    obtain ⟨rhi, envhi⟩ := phi
    dsimp only []
    cases rlo with
    | val vlo =>
      cases rhi with
      | val vhi =>
        cases vlo with
        | int lo_val =>
          cases vhi with
          | int hi_val =>
            exact denoteForLoopRevOrig'_earlyRet_not_cf bi body ih_body fuel var lo_val hi_val envhi w
          | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | _ =>
          cases vhi <;>
            (simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h)
      | earlyRet w' =>
        simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | earlyRet w' =>
      simp only [pure, Pure.pure, StateT.pure]; intro h
      have := Outcome.earlyRet.inj h; subst this; exact ih_lo fuel env _ (by rw [heqlo])
    | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | whileLoop c body ih_c ih_body =>
    intro fuel env w; unfold denote'
    exact denoteWhileOrig'_earlyRet_not_cf bi c body ih_c ih_body fuel env w
  | break_some e ih =>
    intro fuel env w; unfold denote'
    simp only [bind, StateT.bind]
    generalize heqe : denote' bi fuel e env = pe
    obtain ⟨re, enve⟩ := pe
    cases re with
    | val v =>
      cases v with
      | controlFlow =>
        simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | earlyRet w' =>
      simp only [pure, Pure.pure, StateT.pure]; intro h
      have := Outcome.earlyRet.inj h; subst this; exact ih fuel env _ (by rw [heqe])
    | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | break_none =>
    intro fuel env w; unfold denote'
    simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | continue_ =>
    intro fuel env w; unfold denote'
    simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | forFold var lo hi body ih_lo ih_hi ih_body =>
    intro fuel env w; unfold denote'
    simp only [bind, StateT.bind]
    generalize heqlo : denote' bi fuel lo env = plo
    obtain ⟨rlo, envlo⟩ := plo
    dsimp only []
    generalize heqhi : denote' bi fuel hi envlo = phi
    obtain ⟨rhi, envhi⟩ := phi
    dsimp only []
    cases rlo with
    | val vlo =>
      cases vlo with
      | controlFlow =>
        simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | int lo_val =>
        cases rhi with
        | val vhi =>
          cases vhi with
          | controlFlow =>
            simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
          | int hi_val =>
            exact denoteForLoop'_earlyRet_not_cf bi body ih_body fuel var lo_val hi_val envhi w
          | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | earlyRet w' =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ =>
        cases rhi with
        | val vhi =>
          cases vhi with
          | controlFlow =>
            simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
          | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | earlyRet w' =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | earlyRet w' =>
      cases rhi with
      | val vhi =>
        cases vhi with
        | controlFlow =>
          simp only [pure, Pure.pure, StateT.pure]; intro h
          have := Outcome.earlyRet.inj h; subst this; exact ih_lo fuel env _ (by rw [heqlo])
        | _ =>
          simp only [pure, Pure.pure, StateT.pure]; intro h
          have := Outcome.earlyRet.inj h; subst this; exact ih_lo fuel env _ (by rw [heqlo])
      | _ =>
        simp only [pure, Pure.pure, StateT.pure]; intro h
        have := Outcome.earlyRet.inj h; subst this; exact ih_lo fuel env _ (by rw [heqlo])
    | err =>
      cases rhi with
      | val vhi =>
        cases vhi with
        | controlFlow =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | broke =>
      cases rhi with
      | val vhi =>
        cases vhi with
        | controlFlow =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | continued =>
      cases rhi with
      | val vhi =>
        cases vhi with
        | controlFlow =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | forFoldRev var lo hi body ih_lo ih_hi ih_body =>
    intro fuel env w; unfold denote'
    simp only [bind, StateT.bind]
    generalize heqlo : denote' bi fuel lo env = plo
    obtain ⟨rlo, envlo⟩ := plo
    dsimp only []
    generalize heqhi : denote' bi fuel hi envlo = phi
    obtain ⟨rhi, envhi⟩ := phi
    dsimp only []
    cases rlo with
    | val vlo =>
      cases vlo with
      | controlFlow =>
        simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | int lo_val =>
        cases rhi with
        | val vhi =>
          cases vhi with
          | controlFlow =>
            simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
          | int hi_val =>
            exact denoteForLoopRev'_earlyRet_not_cf bi body ih_body fuel var lo_val hi_val envhi w
          | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | earlyRet w' =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ =>
        cases rhi with
        | val vhi =>
          cases vhi with
          | controlFlow =>
            simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
          | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | earlyRet w' =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | earlyRet w' =>
      cases rhi with
      | val vhi =>
        cases vhi with
        | controlFlow =>
          simp only [pure, Pure.pure, StateT.pure]; intro h
          have := Outcome.earlyRet.inj h; subst this; exact ih_lo fuel env _ (by rw [heqlo])
        | _ =>
          simp only [pure, Pure.pure, StateT.pure]; intro h
          have := Outcome.earlyRet.inj h; subst this; exact ih_lo fuel env _ (by rw [heqlo])
      | _ =>
        simp only [pure, Pure.pure, StateT.pure]; intro h
        have := Outcome.earlyRet.inj h; subst this; exact ih_lo fuel env _ (by rw [heqlo])
    | err =>
      cases rhi with
      | val vhi =>
        cases vhi with
        | controlFlow =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | broke =>
      cases rhi with
      | val vhi =>
        cases vhi with
        | controlFlow =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | continued =>
      cases rhi with
      | val vhi =>
        cases vhi with
        | controlFlow =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | whileFold c body ih_c ih_body =>
    intro fuel env w; unfold denote'
    exact denoteWhile'_earlyRet_not_cf bi c body ih_c ih_body fuel env w
  | forFoldReturn var lo hi body ih_lo ih_hi ih_body =>
    intro fuel env w; unfold denote'
    simp only [bind, StateT.bind]
    generalize heqlo : denote' bi fuel lo env = plo
    obtain ⟨rlo, envlo⟩ := plo
    dsimp only []
    generalize heqhi : denote' bi fuel hi envlo = phi
    obtain ⟨rhi, envhi⟩ := phi
    dsimp only []
    cases rlo with
    | val vlo =>
      cases vlo with
      | controlFlow =>
        simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | int lo_val =>
        cases rhi with
        | val vhi =>
          cases vhi with
          | controlFlow =>
            simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
          | int hi_val =>
            exact denoteForLoop'Return_earlyRet_not_cf bi body ih_body fuel var lo_val hi_val envhi w
          | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | earlyRet w' =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ =>
        cases rhi with
        | val vhi =>
          cases vhi with
          | controlFlow =>
            simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
          | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | earlyRet w' =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | earlyRet w' =>
      cases rhi with
      | val vhi =>
        cases vhi with
        | controlFlow =>
          simp only [pure, Pure.pure, StateT.pure]; intro h
          have := Outcome.earlyRet.inj h; subst this; exact ih_lo fuel env _ (by rw [heqlo])
        | _ =>
          simp only [pure, Pure.pure, StateT.pure]; intro h
          have := Outcome.earlyRet.inj h; subst this; exact ih_lo fuel env _ (by rw [heqlo])
      | _ =>
        simp only [pure, Pure.pure, StateT.pure]; intro h
        have := Outcome.earlyRet.inj h; subst this; exact ih_lo fuel env _ (by rw [heqlo])
    | err =>
      cases rhi with
      | val vhi =>
        cases vhi with
        | controlFlow =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | broke =>
      cases rhi with
      | val vhi =>
        cases vhi with
        | controlFlow =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | continued =>
      cases rhi with
      | val vhi =>
        cases vhi with
        | controlFlow =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | forFoldRevReturn var lo hi body ih_lo ih_hi ih_body =>
    intro fuel env w; unfold denote'
    simp only [bind, StateT.bind]
    generalize heqlo : denote' bi fuel lo env = plo
    obtain ⟨rlo, envlo⟩ := plo
    dsimp only []
    generalize heqhi : denote' bi fuel hi envlo = phi
    obtain ⟨rhi, envhi⟩ := phi
    dsimp only []
    cases rlo with
    | val vlo =>
      cases vlo with
      | controlFlow =>
        simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | int lo_val =>
        cases rhi with
        | val vhi =>
          cases vhi with
          | controlFlow =>
            simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
          | int hi_val =>
            exact denoteForLoopRev'Return_earlyRet_not_cf bi body ih_body fuel var lo_val hi_val envhi w
          | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | earlyRet w' =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ =>
        cases rhi with
        | val vhi =>
          cases vhi with
          | controlFlow =>
            simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
          | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | earlyRet w' =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | earlyRet w' =>
      cases rhi with
      | val vhi =>
        cases vhi with
        | controlFlow =>
          simp only [pure, Pure.pure, StateT.pure]; intro h
          have := Outcome.earlyRet.inj h; subst this; exact ih_lo fuel env _ (by rw [heqlo])
        | _ =>
          simp only [pure, Pure.pure, StateT.pure]; intro h
          have := Outcome.earlyRet.inj h; subst this; exact ih_lo fuel env _ (by rw [heqlo])
      | _ =>
        simp only [pure, Pure.pure, StateT.pure]; intro h
        have := Outcome.earlyRet.inj h; subst this; exact ih_lo fuel env _ (by rw [heqlo])
    | err =>
      cases rhi with
      | val vhi =>
        cases vhi with
        | controlFlow =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | broke =>
      cases rhi with
      | val vhi =>
        cases vhi with
        | controlFlow =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | continued =>
      cases rhi with
      | val vhi =>
        cases vhi with
        | controlFlow =>
          simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
        | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | whileFoldReturn c body ih_c ih_body =>
    intro fuel env w; unfold denote'
    exact denoteWhile'Return_earlyRet_not_cf bi c body ih_c ih_body fuel env w
  | cfBreak e ih =>
    intro fuel env w; unfold denote'
    simp only [bind, StateT.bind]
    generalize heqe : denote' bi fuel e env = pe
    obtain ⟨re, enve⟩ := pe
    cases re with
    | val v =>
      cases v with
      | controlFlow =>
        simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | earlyRet w' =>
      simp only [pure, Pure.pure, StateT.pure]; intro h
      have := Outcome.earlyRet.inj h; subst this; exact ih fuel env _ (by rw [heqe])
    | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | cfContinue e ih =>
    intro fuel env w; unfold denote'
    simp only [bind, StateT.bind]
    generalize heqe : denote' bi fuel e env = pe
    obtain ⟨re, enve⟩ := pe
    cases re with
    | val v =>
      cases v with
      | controlFlow =>
        simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | earlyRet w' =>
      simp only [pure, Pure.pure, StateT.pure]; intro h
      have := Outcome.earlyRet.inj h; subst this; exact ih fuel env _ (by rw [heqe])
    | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | cfBreakContinue e ih =>
    intro fuel env w; unfold denote'
    simp only [bind, StateT.bind]
    generalize heqe : denote' bi fuel e env = pe
    obtain ⟨re, enve⟩ := pe
    cases re with
    | val v =>
      cases v with
      | controlFlow =>
        simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
      | _ => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | earlyRet w' =>
      simp only [pure, Pure.pure, StateT.pure]; intro h
      have := Outcome.earlyRet.inj h; subst this; exact ih fuel env _ (by rw [heqe])
    | err => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | broke => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    | continued => simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | typeAscription _ _ ih =>
    intro fuel env w; unfold denote'; exact ih fuel env w

/-! ### Helper: denoteForLoop' never produces earlyRet -/

/-- `denoteForLoop'` never produces `earlyRet` when the body never does. -/
private theorem denoteForLoop'_no_earlyRet (bi : Builtins) (body : ImpExpr)
    (hbody : ∀ fuel env v, (denote' bi fuel body env).1 ≠ .earlyRet v)
    (fuel : Nat) (var : String) (lo hi : Int) :
    ∀ env v, (denoteForLoop' bi fuel var lo hi body env).1 ≠ .earlyRet v := by
  induction fuel generalizing lo with
  | zero =>
    intro env v
    unfold denoteForLoop'
    split
    · simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    · simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | succ n ih =>
    intro env v
    unfold denoteForLoop'
    by_cases hge : lo ≥ hi
    · simp only [if_pos hge, pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    · simp only [if_neg hge, show ¬(n + 1 = 0) from by omega, ↓reduceIte]
      dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
      generalize heqb : denote' bi (n + 1) body (Env.extend env var (.int lo)) = pb
      obtain ⟨rb, envb⟩ := pb
      cases rb with
      | val vb =>
        cases vb with
        | controlFlow isBreak w =>
          cases isBreak with
          | true => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
          | false => simp only [show n + 1 - 1 = n from rfl]; exact ih (lo + 1) envb v
        | _ => simp only [show n + 1 - 1 = n from rfl]; exact ih (lo + 1) envb v
      | earlyRet w =>
        exact absurd (show (denote' bi (n + 1) body _).1 = .earlyRet w from
          by rw [heqb]) (hbody (n + 1) _ w)
      | err => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
      | broke => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
      | continued => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h

/-! ### Helper: denoteForLoopRev' never produces earlyRet -/

/-- `denoteForLoopRev'` never produces `earlyRet` when the body never does. -/
private theorem denoteForLoopRev'_no_earlyRet (bi : Builtins) (body : ImpExpr)
    (hbody : ∀ fuel env v, (denote' bi fuel body env).1 ≠ .earlyRet v)
    (fuel : Nat) (var : String) (lo hi : Int) :
    ∀ env v, (denoteForLoopRev' bi fuel var lo hi body env).1 ≠ .earlyRet v := by
  induction fuel generalizing hi with
  | zero =>
    intro env v
    unfold denoteForLoopRev'
    split
    · simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    · simp only [pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
  | succ n ih =>
    intro env v
    unfold denoteForLoopRev'
    by_cases hge : lo ≥ hi
    · simp only [if_pos hge, pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    · simp only [if_neg hge, show ¬(n + 1 = 0) from by omega, ↓reduceIte]
      dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
      generalize heqb : denote' bi (n + 1) body (Env.extend env var (.int (hi - 1))) = pb
      obtain ⟨rb, envb⟩ := pb
      cases rb with
      | val vb =>
        cases vb with
        | controlFlow isBreak w =>
          cases isBreak with
          | true => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
          | false => simp only [show n + 1 - 1 = n from rfl]; exact ih (hi - 1) envb v
        | _ => simp only [show n + 1 - 1 = n from rfl]; exact ih (hi - 1) envb v
      | earlyRet w =>
        exact absurd (show (denote' bi (n + 1) body _).1 = .earlyRet w from
          by rw [heqb]) (hbody (n + 1) _ w)
      | err => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
      | broke => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
      | continued => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h

/-! ### Helper: denoteForLoopRev'Return simulation for forFoldRevReturn -/

/-- `denoteForLoopRev'Return` with `cfIntoMonads body` gives `encodeCF4` of original,
    using the earlyRet-not-CF invariant for the body. -/
private theorem denoteForLoopRev'Return_sim (bi : Builtins) (var : String) (body : ImpExpr)
    (ih_body : ∀ fuel env, denote' bi fuel (cfIntoMonads body) env =
      (Outcome.encodeCF4 (denote' bi fuel body env).1, (denote' bi fuel body env).2))
    (hbody_er_not_cf : ∀ fuel env v, (denote' bi fuel body env).1 = .earlyRet v →
      v.isControlFlow = false) :
    ∀ fuel (lo hi : Int) env,
      denoteForLoopRev'Return bi fuel var lo hi (cfIntoMonads body) env =
        (Outcome.encodeCF4 (denoteForLoopRev'Return bi fuel var lo hi body env).1,
         (denoteForLoopRev'Return bi fuel var lo hi body env).2) := by
  intro fuel; induction fuel with
  | zero =>
    intro lo hi env
    unfold denoteForLoopRev'Return
    split
    · simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
    · simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
  | succ n ih =>
    intro lo hi env
    unfold denoteForLoopRev'Return
    by_cases hge : lo ≥ hi
    · simp only [if_pos hge, pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
    · simp only [if_neg hge, show ¬(n + 1 = 0) from by omega, ↓reduceIte]
      dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
      rw [ih_body (n + 1) (Env.extend env var (.int (hi - 1)))]
      generalize heqb : denote' bi (n + 1) body (Env.extend env var (.int (hi - 1))) = pb
      obtain ⟨rb, envb⟩ := pb
      cases rb with
      | val vb =>
        simp only [Outcome.encodeCF4]
        cases vb with
        | controlFlow isBreak w =>
          cases isBreak with
          | true =>
            cases w with
            | controlFlow isBreak2 w2 =>
              cases isBreak2 with
              | false => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
              | true => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
            | _ => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
          | false => simp only [show n + 1 - 1 = n from rfl]; exact ih lo (hi - 1) envb
        | _ => simp only [show n + 1 - 1 = n from rfl]; exact ih lo (hi - 1) envb
      | earlyRet w =>
        have hncf := hbody_er_not_cf (n + 1) (Env.extend env var (.int (hi - 1))) w
          (by rw [heqb])
        simp only [Outcome.encodeCF4]
        cases w with
        | controlFlow => simp [Value.isControlFlow] at hncf
        | _ => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
      | err => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
      | broke => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
      | continued => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]

/-! ### Helper: denoteWhile' simulation for whileFold -/

/-- `denoteWhile'` with `cfIntoMonads` condition gives `encodeCF4` of original. -/
private theorem denoteWhile'_sim (bi : Builtins) (c body : ImpExpr)
    (ih_c : ∀ fuel env, denote' bi fuel (cfIntoMonads c) env =
      (Outcome.encodeCF4 (denote' bi fuel c env).1, (denote' bi fuel c env).2))
    (hbody_no_er : ∀ fuel env v, (denote' bi fuel body env).1 ≠ .earlyRet v) :
    ∀ fuel env, denoteWhile' bi fuel (cfIntoMonads c) body env =
      (Outcome.encodeCF4 (denoteWhile' bi fuel c body env).1,
       (denoteWhile' bi fuel c body env).2) := by
  intro fuel; induction fuel with
  | zero =>
    intro env
    unfold denoteWhile'
    simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
  | succ n ih =>
    intro env
    unfold denoteWhile'
    have hfuel : ¬(n + 1 = 0) := by omega
    simp only [if_neg hfuel, bind, StateT.bind]
    rw [ih_c (n + 1) env]
    generalize denote' bi (n + 1) c env = pc
    obtain ⟨rc, envc⟩ := pc
    cases rc with
    | val vc =>
      simp only [Outcome.encodeCF4]
      cases vc with
      | controlFlow => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
      | bool b =>
        cases b with
        | true =>
          simp only [bind, StateT.bind]
          generalize heqb : denote' bi (n + 1) body envc = pb
          obtain ⟨rb, envb⟩ := pb
          cases rb with
          | val vb =>
            cases vb with
            | controlFlow isBreak w =>
              cases isBreak with
              | true => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
              | false => simp only [show n + 1 - 1 = n from rfl]; exact ih envb
            | _ => simp only [show n + 1 - 1 = n from rfl]; exact ih envb
          | earlyRet w =>
            exact absurd (show (denote' bi (n + 1) body envc).1 = .earlyRet w from
              by rw [heqb]) (hbody_no_er (n + 1) envc w)
          | err => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
          | broke => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
          | continued => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
        | false => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
      | _ => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
    | earlyRet => simp [Outcome.encodeCF4, pure, Pure.pure, StateT.pure]
    | err => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
    | broke => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
    | continued => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]

/-! ### Helper: denoteForLoop'Return simulation for forFoldReturn -/

/-- `denoteForLoop'Return` with `cfIntoMonads body` gives `encodeCF4` of original,
    using the earlyRet-not-CF invariant for the body. -/
private theorem denoteForLoop'Return_sim (bi : Builtins) (var : String) (body : ImpExpr)
    (ih_body : ∀ fuel env, denote' bi fuel (cfIntoMonads body) env =
      (Outcome.encodeCF4 (denote' bi fuel body env).1, (denote' bi fuel body env).2))
    (hbody_er_not_cf : ∀ fuel env v, (denote' bi fuel body env).1 = .earlyRet v →
      v.isControlFlow = false) :
    ∀ fuel (lo hi : Int) env,
      denoteForLoop'Return bi fuel var lo hi (cfIntoMonads body) env =
        (Outcome.encodeCF4 (denoteForLoop'Return bi fuel var lo hi body env).1,
         (denoteForLoop'Return bi fuel var lo hi body env).2) := by
  intro fuel; induction fuel with
  | zero =>
    intro lo hi env
    unfold denoteForLoop'Return
    split
    · simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
    · simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
  | succ n ih =>
    intro lo hi env
    unfold denoteForLoop'Return
    by_cases hge : lo ≥ hi
    · simp only [if_pos hge, pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
    · simp only [if_neg hge, show ¬(n + 1 = 0) from by omega, ↓reduceIte]
      dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
      rw [ih_body (n + 1) (Env.extend env var (.int lo))]
      generalize heqb : denote' bi (n + 1) body (Env.extend env var (.int lo)) = pb
      obtain ⟨rb, envb⟩ := pb
      cases rb with
      | val vb =>
        simp only [Outcome.encodeCF4]
        cases vb with
        | controlFlow isBreak w =>
          cases isBreak with
          | true =>
            cases w with
            | controlFlow isBreak2 w2 =>
              cases isBreak2 with
              | false => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
              | true => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
            | _ => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
          | false => simp only [show n + 1 - 1 = n from rfl]; exact ih (lo + 1) hi envb
        | _ => simp only [show n + 1 - 1 = n from rfl]; exact ih (lo + 1) hi envb
      | earlyRet w =>
        have hncf := hbody_er_not_cf (n + 1) (Env.extend env var (.int lo)) w
          (by rw [heqb])
        simp only [Outcome.encodeCF4]
        cases w with
        | controlFlow => simp [Value.isControlFlow] at hncf
        | _ => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
      | err => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
      | broke => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
      | continued => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]

/-! ### Helper: denoteWhile'Return simulation for whileFoldReturn -/

/-- `denoteWhile'Return` with `cfIntoMonads` cond and body gives `encodeCF4` of original. -/
private theorem denoteWhile'Return_sim (bi : Builtins) (c body : ImpExpr)
    (ih_c : ∀ fuel env, denote' bi fuel (cfIntoMonads c) env =
      (Outcome.encodeCF4 (denote' bi fuel c env).1, (denote' bi fuel c env).2))
    (ih_body : ∀ fuel env, denote' bi fuel (cfIntoMonads body) env =
      (Outcome.encodeCF4 (denote' bi fuel body env).1, (denote' bi fuel body env).2))
    (hbody_er_not_cf : ∀ fuel env v, (denote' bi fuel body env).1 = .earlyRet v →
      v.isControlFlow = false) :
    ∀ fuel env, denoteWhile'Return bi fuel (cfIntoMonads c) (cfIntoMonads body) env =
      (Outcome.encodeCF4 (denoteWhile'Return bi fuel c body env).1,
       (denoteWhile'Return bi fuel c body env).2) := by
  intro fuel; induction fuel with
  | zero =>
    intro env
    unfold denoteWhile'Return
    simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
  | succ n ih =>
    intro env
    unfold denoteWhile'Return
    have hfuel : ¬(n + 1 = 0) := by omega
    simp only [if_neg hfuel, bind, StateT.bind]
    rw [ih_c (n + 1) env]
    generalize denote' bi (n + 1) c env = pc
    obtain ⟨rc, envc⟩ := pc
    cases rc with
    | val vc =>
      simp only [Outcome.encodeCF4]
      cases vc with
      | controlFlow => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
      | bool b =>
        cases b with
        | true =>
          simp only [bind, StateT.bind]
          rw [ih_body (n + 1) envc]
          generalize heqb : denote' bi (n + 1) body envc = pb
          obtain ⟨rb, envb⟩ := pb
          cases rb with
          | val vb =>
            simp only [Outcome.encodeCF4]
            cases vb with
            | controlFlow isBreak w =>
              cases isBreak with
              | true =>
                cases w with
                | controlFlow isBreak2 w2 =>
                  cases isBreak2 with
                  | false => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
                  | true => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
                | _ => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
              | false => simp only [show n + 1 - 1 = n from rfl]; exact ih envb
            | _ => simp only [show n + 1 - 1 = n from rfl]; exact ih envb
          | earlyRet w =>
            have hncf := hbody_er_not_cf (n + 1) envc w (by rw [heqb])
            simp only [Outcome.encodeCF4]
            cases w with
            | controlFlow => simp [Value.isControlFlow] at hncf
            | _ => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
          | err => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
          | broke => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
          | continued => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
        | false => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
      | _ => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
    | earlyRet => simp [Outcome.encodeCF4, pure, Pure.pure, StateT.pure]
    | err => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
    | broke => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]
    | continued => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4]

/-! ### Main theorem -/

/-- Phase 4 simulation: `cfIntoMonads` preserves `denote'` semantics
    up to `Outcome.encodeCF4` on the result, with identical env.

    Note: `NoReservedApps` precondition eliminated thanks to dedicated constructors.
    Note: `fuel` is universally quantified inside to give the IH fuel-universality. -/
theorem CF4_combined (bi : Builtins) (e : ImpExpr)
    (hnl : NoLoops e) (hnq : NoQuestionMark e) (hwf : WellFormedFolds e) :
    ∀ fuel env, denote' bi fuel (cfIntoMonads e) env =
      (Outcome.encodeCF4 (denote' bi fuel e env).1, (denote' bi fuel e env).2) := by
  induction e using ImpExpr.ind with
  -- Trivial cases: cfIntoMonads is identity, denote' returns val or err
  | lit v =>
    intro fuel env; simp only [cfIntoMonads]; unfold denote'; rfl
  | var n =>
    intro fuel env
    simp only [cfIntoMonads]; unfold denote'
    simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get]
    cases env n <;> rfl
  | unitVal =>
    intro fuel env; simp only [cfIntoMonads]; unfold denote'; rfl
  -- Structural: letBind
  | letBind n val body ih_val ih_body =>
    cases hnl with | letBind hl1 hl2 =>
    cases hnq with | letBind hq1 hq2 =>
    cases hwf with | letBind hw1 hw2 =>
    intro fuel env
    simp only [cfIntoMonads]; unfold denote'
    simp only [bind, StateT.bind]
    rw [ih_val hl1 hq1 hw1 fuel env]
    generalize denote' bi fuel val env = pv
    obtain ⟨rv, envv⟩ := pv
    cases rv with
    | val v =>
      simp only [Outcome.encodeCF4]
      cases v with
      | controlFlow => rfl
      | _ =>
        simp only [modify, modifyGet, MonadStateOf.modifyGet]
        exact ih_body hl2 hq2 hw2 fuel _
    | earlyRet => rfl
    | err => rfl
    | broke => rfl
    | continued => rfl
  -- Structural: seq
  | seq e1 e2 ih1 ih2 =>
    cases hnl with | seq hl1 hl2 =>
    cases hnq with | seq hq1 hq2 =>
    cases hwf with | seq hw1 hw2 =>
    intro fuel env
    simp only [cfIntoMonads]; unfold denote'
    simp only [bind, StateT.bind]
    rw [ih1 hl1 hq1 hw1 fuel env]
    generalize denote' bi fuel e1 env = p1
    obtain ⟨r1, env1⟩ := p1
    cases r1 with
    | val v =>
      simp only [Outcome.encodeCF4]
      cases v with
      | controlFlow => rfl
      | _ => exact ih2 hl2 hq2 hw2 fuel _
    | earlyRet => rfl
    | err => rfl
    | broke => rfl
    | continued => rfl
  -- Structural: proj
  | proj e i ih =>
    cases hnl with | proj he =>
    cases hnq with | proj hqe =>
    cases hwf with | proj hwe =>
    intro fuel env
    simp only [cfIntoMonads]; unfold denote'
    simp only [bind, StateT.bind]
    rw [ih he hqe hwe fuel env]
    generalize denote' bi fuel e env = pe
    obtain ⟨re, enve⟩ := pe
    cases re with
    | val v =>
      simp only [Outcome.encodeCF4]
      cases v with
      | controlFlow => rfl
      | _ => dsimp only []; cases Value.projIdx _ i <;> rfl
    | earlyRet => rfl
    | err => rfl
    | broke => rfl
    | continued => rfl
  -- Structural: ifThenElse
  | ifThenElse c t el ih_c ih_t ih_e =>
    cases hnl with | ifThenElse hlc hlt hle =>
    cases hnq with | ifThenElse hqc hqt hqe =>
    cases hwf with | ifThenElse hwc hwt hwe =>
    intro fuel env
    simp only [cfIntoMonads]; unfold denote'
    simp only [bind, StateT.bind]
    rw [ih_c hlc hqc hwc fuel env]
    generalize denote' bi fuel c env = pc
    obtain ⟨rc, envc⟩ := pc
    cases rc with
    | val v =>
      simp only [Outcome.encodeCF4]
      cases v with
      | controlFlow => rfl
      | bool b =>
        cases b with
        | true => exact ih_t hlt hqt hwt fuel _
        | false => exact ih_e hle hqe hwe fuel _
      | _ => rfl
    | earlyRet => rfl
    | err => rfl
    | broke => rfl
    | continued => rfl
  -- Structural: assign
  | assign n rhs ih =>
    cases hnl with | assign hrhs =>
    cases hnq with | assign hqrhs =>
    cases hwf with | assign hwrhs =>
    intro fuel env
    simp only [cfIntoMonads]; unfold denote'
    simp only [bind, StateT.bind]
    rw [ih hrhs hqrhs hwrhs fuel env]
    generalize denote' bi fuel rhs env = pr
    obtain ⟨rr, envr⟩ := pr
    cases rr with
    | val v =>
      simp only [Outcome.encodeCF4]
      cases v with
      | controlFlow => rfl
      | _ =>
        simp only [modify, modifyGet, MonadStateOf.modifyGet]
        rfl
    | earlyRet => rfl
    | err => rfl
    | broke => rfl
    | continued => rfl
  -- Pass-through: borrow, deref
  | borrow e ih =>
    cases hnl with | borrow he =>
    cases hnq with | borrow hqe =>
    cases hwf with | borrow hwe =>
    intro fuel env
    simp only [cfIntoMonads]; unfold denote'
    exact ih he hqe hwe fuel env
  | deref e ih =>
    cases hnl with | deref he =>
    cases hnq with | deref hqe =>
    cases hwf with | deref hwe =>
    intro fuel env
    simp only [cfIntoMonads]; unfold denote'
    exact ih he hqe hwe fuel env
  -- App: uses denoteArgs' helper
  | app f args ih =>
    cases hnl with | app hlargs =>
    cases hnq with | app hqargs =>
    cases hwf with | app hwargs =>
    intro fuel env
    simp only [cfIntoMonads, cfIntoMonads.mapExpr_eq]; unfold denote'; unfold denoteApp'
    simp only [bind, StateT.bind]
    rw [denoteArgs'_cfIntoMonads bi fuel args
      (fun a ha => ih a ha (hlargs a ha) (hqargs a ha) (hwargs a ha) fuel) env]
    generalize denoteArgs' bi fuel args env = pa
    obtain ⟨ma, enva⟩ := pa
    dsimp only []
    cases ma with
    | some vals => dsimp only []; cases bi f vals <;> rfl
    | none => dsimp only []; rfl
  -- Tuple: uses denoteArgs' helper
  | tuple elems ih =>
    cases hnl with | tuple hlelems =>
    cases hnq with | tuple hqelems =>
    cases hwf with | tuple hwelems =>
    intro fuel env
    simp only [cfIntoMonads, cfIntoMonads.mapExpr_eq]; unfold denote'
    simp only [bind, StateT.bind]
    rw [denoteArgs'_cfIntoMonads bi fuel elems
      (fun a ha => ih a ha (hlelems a ha) (hqelems a ha) (hwelems a ha) fuel) env]
    generalize denoteArgs' bi fuel elems env = pa
    obtain ⟨ma, enva⟩ := pa
    dsimp only []
    cases ma <;> rfl
  -- Match: uses denoteMatchArms' helper
  | match_ scrut arms ih_scrut ih_arms =>
    cases hnl with | match_ hls hlarms =>
    cases hnq with | match_ hqs hqarms =>
    cases hwf with | match_ hws hwarms =>
    intro fuel env
    simp only [cfIntoMonads, cfIntoMonads.mapArms_eq]; unfold denote'
    simp only [bind, StateT.bind]
    rw [ih_scrut hls hqs hws fuel env]
    generalize denote' bi fuel scrut env = ps
    obtain ⟨rs, envs⟩ := ps
    cases rs with
    | val v =>
      simp only [Outcome.encodeCF4]
      cases v with
      | controlFlow => rfl
      | _ =>
        exact denoteMatchArms'_cfIntoMonads bi fuel _ arms
          (fun pa hpa => ih_arms pa hpa (hlarms pa hpa) (hqarms pa hpa) (hwarms pa hpa) fuel) envs
    | earlyRet => rfl
    | err => rfl
    | broke => rfl
    | continued => rfl
  -- Main transform: earlyReturn → cfBreak
  | earlyReturn e ih =>
    cases hnl with | earlyReturn he =>
    cases hnq with | earlyReturn hqe =>
    cases hwf with | earlyReturn hwe =>
    intro fuel env
    simp only [cfIntoMonads]; unfold denote'
    simp only [bind, StateT.bind]
    rw [ih he hqe hwe fuel env]
    generalize denote' bi fuel e env = pe
    obtain ⟨re, enve⟩ := pe
    cases re with
    | val v =>
      simp only [Outcome.encodeCF4]
      cases v with
      | controlFlow => rfl
      | _ => rfl
    | earlyRet => rfl
    | err => rfl
    | broke => rfl
    | continued => rfl
  -- Impossible cases
  | questionMark => exact absurd hnq NoQuestionMark.not_questionMark
  | forLoop => exact absurd hnl NoLoops.not_forLoop
  | forLoopRev => exact absurd hnl NoLoops.not_forLoopRev
  | whileLoop => exact absurd hnl NoLoops.not_whileLoop
  | break_none => exact absurd hnl NoLoops.not_break
  | break_some => exact absurd hnl NoLoops.not_break
  | continue_ => exact absurd hnl NoLoops.not_continue
  -- forFold/whileFold: body has NoEarlyExit, so cfIntoMonads body = body
  | forFold v lo hi body ih_lo ih_hi ih_body =>
    cases hnl with | forFold hllo hlhi hlbody =>
    cases hnq with | forFold hqlo hqhi hqbody =>
    cases hwf with | forFold hwlo hwhi hwbody hee_body =>
    intro fuel env
    have hid : cfIntoMonads body = body := cfIntoMonads_identity body hee_body
    simp only [cfIntoMonads, hid]; unfold denote'
    simp only [bind, StateT.bind]
    -- Rewrite BOTH lo and hi before case-splitting
    rw [ih_lo hllo hqlo hwlo fuel env]
    generalize denote' bi fuel lo env = plo
    obtain ⟨rlo, envlo⟩ := plo
    dsimp only []
    rw [ih_hi hlhi hqhi hwhi fuel envlo]
    generalize denote' bi fuel hi envlo = phi
    obtain ⟨rhi, envhi⟩ := phi
    dsimp only []
    -- Body never produces earlyRet (from IH + cfIntoMonads identity)
    have hbody_no_er : ∀ fuel env v, (denote' bi fuel body env).1 ≠ .earlyRet v := by
      intro f e v heq
      have h := ih_body hlbody hqbody hwbody f e
      rw [hid] at h
      have h1 := congrArg Prod.fst h
      rw [heq] at h1; simp [Outcome.encodeCF4] at h1
    -- Case split on (encodeCF4 rlo, encodeCF4 rhi) vs (rlo, rhi)
    -- Use dsimp to reduce match expressions and encodeCF4
    cases rlo with
    | val vlo =>
      cases rhi with
      | val vhi =>
        simp only [Outcome.encodeCF4]
        cases vlo with
        | int lo_val =>
          cases vhi with
          | int hi_val =>
            -- Reduce match on LHS (both sides now use denoteForLoop' directly)
            dsimp only []
            -- Since denoteForLoop' never produces earlyRet, encodeCF4 is identity
            have hfl := denoteForLoop'_no_earlyRet bi body hbody_no_er fuel v lo_val hi_val envhi
            generalize heqfl : denoteForLoop' bi fuel v lo_val hi_val body envhi = pfl
            obtain ⟨rfl_out, envfl⟩ := pfl
            cases rfl_out with
            | earlyRet w => exact absurd (congrArg Prod.fst heqfl) (hfl w)
            | _ => rfl
          | controlFlow => rfl
          | _ => rfl
        | controlFlow => rfl
        | _ =>
          cases vhi with
          | controlFlow => rfl
          | _ => rfl
      | earlyRet w =>
        dsimp only [Outcome.encodeCF4]
        cases vlo with
        | controlFlow => dsimp only []; rfl
        | _ => dsimp only []; rfl
      | err =>
        dsimp only [Outcome.encodeCF4]
        cases vlo <;> dsimp only [] <;> rfl
      | broke =>
        dsimp only [Outcome.encodeCF4]
        cases vlo <;> dsimp only [] <;> rfl
      | continued =>
        dsimp only [Outcome.encodeCF4]
        cases vlo <;> dsimp only [] <;> rfl
    | earlyRet w =>
      dsimp only [Outcome.encodeCF4]
      cases rhi with
      | val vhi =>
        cases vhi <;> dsimp only [] <;> rfl
      | _ => dsimp only [] ; rfl
    | err =>
      dsimp only [Outcome.encodeCF4]
      cases rhi with
      | val vhi => cases vhi <;> dsimp only [] <;> rfl
      | _ => dsimp only []; rfl
    | broke =>
      dsimp only [Outcome.encodeCF4]
      cases rhi with
      | val vhi => cases vhi <;> dsimp only [] <;> rfl
      | _ => dsimp only []; rfl
    | continued =>
      dsimp only [Outcome.encodeCF4]
      cases rhi with
      | val vhi => cases vhi <;> dsimp only [] <;> rfl
      | _ => dsimp only []; rfl
  | forFoldRev v lo hi body ih_lo ih_hi ih_body =>
    cases hnl with | forFoldRev hllo hlhi hlbody =>
    cases hnq with | forFoldRev hqlo hqhi hqbody =>
    cases hwf with | forFoldRev hwlo hwhi hwbody hee_body =>
    intro fuel env
    have hid : cfIntoMonads body = body := cfIntoMonads_identity body hee_body
    simp only [cfIntoMonads, hid]; unfold denote'
    simp only [bind, StateT.bind]
    -- Rewrite BOTH lo and hi before case-splitting
    rw [ih_lo hllo hqlo hwlo fuel env]
    generalize denote' bi fuel lo env = plo
    obtain ⟨rlo, envlo⟩ := plo
    dsimp only []
    rw [ih_hi hlhi hqhi hwhi fuel envlo]
    generalize denote' bi fuel hi envlo = phi
    obtain ⟨rhi, envhi⟩ := phi
    dsimp only []
    -- Body never produces earlyRet (from IH + cfIntoMonads identity)
    have hbody_no_er : ∀ fuel env v, (denote' bi fuel body env).1 ≠ .earlyRet v := by
      intro f e v heq
      have h := ih_body hlbody hqbody hwbody f e
      rw [hid] at h
      have h1 := congrArg Prod.fst h
      rw [heq] at h1; simp [Outcome.encodeCF4] at h1
    cases rlo with
    | val vlo =>
      cases rhi with
      | val vhi =>
        simp only [Outcome.encodeCF4]
        cases vlo with
        | int lo_val =>
          cases vhi with
          | int hi_val =>
            dsimp only []
            -- Since denoteForLoopRev' never produces earlyRet, encodeCF4 is identity
            have hfl := denoteForLoopRev'_no_earlyRet bi body hbody_no_er fuel v lo_val hi_val envhi
            generalize heqfl : denoteForLoopRev' bi fuel v lo_val hi_val body envhi = pfl
            obtain ⟨rfl_out, envfl⟩ := pfl
            cases rfl_out with
            | earlyRet w => exact absurd (congrArg Prod.fst heqfl) (hfl w)
            | _ => rfl
          | controlFlow => rfl
          | _ => rfl
        | controlFlow => rfl
        | _ =>
          cases vhi with
          | controlFlow => rfl
          | _ => rfl
      | earlyRet w =>
        dsimp only [Outcome.encodeCF4]
        cases vlo with
        | controlFlow => dsimp only []; rfl
        | _ => dsimp only []; rfl
      | err =>
        dsimp only [Outcome.encodeCF4]
        cases vlo <;> dsimp only [] <;> rfl
      | broke =>
        dsimp only [Outcome.encodeCF4]
        cases vlo <;> dsimp only [] <;> rfl
      | continued =>
        dsimp only [Outcome.encodeCF4]
        cases vlo <;> dsimp only [] <;> rfl
    | earlyRet w =>
      dsimp only [Outcome.encodeCF4]
      cases rhi with
      | val vhi =>
        cases vhi <;> dsimp only [] <;> rfl
      | _ => dsimp only [] ; rfl
    | err =>
      dsimp only [Outcome.encodeCF4]
      cases rhi with
      | val vhi => cases vhi <;> dsimp only [] <;> rfl
      | _ => dsimp only []; rfl
    | broke =>
      dsimp only [Outcome.encodeCF4]
      cases rhi with
      | val vhi => cases vhi <;> dsimp only [] <;> rfl
      | _ => dsimp only []; rfl
    | continued =>
      dsimp only [Outcome.encodeCF4]
      cases rhi with
      | val vhi => cases vhi <;> dsimp only [] <;> rfl
      | _ => dsimp only []; rfl
  | whileFold c body ih_c ih_body =>
    cases hnl with | whileFold hlc hlbody =>
    cases hnq with | whileFold hqc hqbody =>
    cases hwf with | whileFold hwc hwbody hee_body =>
    intro fuel env
    have hid : cfIntoMonads body = body := cfIntoMonads_identity body hee_body
    simp only [cfIntoMonads, hid]; unfold denote'
    -- Derive: body never produces earlyRet (from IH + identity)
    have hbody_no_er : ∀ fuel env v, (denote' bi fuel body env).1 ≠ .earlyRet v := by
      intro f e v heq
      have := congrArg Prod.fst (ih_body hlbody hqbody hwbody f e)
      rw [hid] at this; simp only at this; rw [heq] at this
      simp [Outcome.encodeCF4] at this
    exact denoteWhile'_sim bi c body (ih_c hlc hqc hwc) hbody_no_er fuel env
  | forFoldReturn v lo hi body ih_lo ih_hi ih_body =>
    cases hnl with | forFoldReturn hllo hlhi hlbody =>
    cases hnq with | forFoldReturn hqlo hqhi hqbody =>
    cases hwf with | forFoldReturn hwlo hwhi hwbody =>
    intro fuel env
    simp only [cfIntoMonads]; unfold denote'
    simp only [bind, StateT.bind]
    -- Rewrite lo and hi via their IHs
    rw [ih_lo hllo hqlo hwlo fuel env]
    generalize denote' bi fuel lo env = plo
    obtain ⟨rlo, envlo⟩ := plo
    dsimp only []
    rw [ih_hi hlhi hqhi hwhi fuel envlo]
    generalize denote' bi fuel hi envlo = phi
    obtain ⟨rhi, envhi⟩ := phi
    dsimp only []
    -- Derive earlyRet-not-CF for body
    have hbody_er_not_cf : ∀ fuel env w, (denote' bi fuel body env).1 = .earlyRet w →
        w.isControlFlow = false :=
      denote'_earlyRet_not_cf bi body
    -- Case split on rlo
    cases rlo with
    | val vlo =>
      cases rhi with
      | val vhi =>
        simp only [Outcome.encodeCF4]
        cases vlo with
        | int lo_val =>
          cases vhi with
          | int hi_val =>
            dsimp only []
            exact denoteForLoop'Return_sim bi v body
              (ih_body hlbody hqbody hwbody) hbody_er_not_cf fuel lo_val hi_val envhi
          | controlFlow => rfl
          | _ => rfl
        | controlFlow => rfl
        | _ =>
          cases vhi with
          | controlFlow => rfl
          | _ => rfl
      | earlyRet w =>
        dsimp only [Outcome.encodeCF4]
        cases vlo with
        | controlFlow => dsimp only []; rfl
        | _ => dsimp only []; rfl
      | err =>
        dsimp only [Outcome.encodeCF4]
        cases vlo <;> dsimp only [] <;> rfl
      | broke =>
        dsimp only [Outcome.encodeCF4]
        cases vlo <;> dsimp only [] <;> rfl
      | continued =>
        dsimp only [Outcome.encodeCF4]
        cases vlo <;> dsimp only [] <;> rfl
    | earlyRet w =>
      dsimp only [Outcome.encodeCF4]
      cases rhi with
      | val vhi =>
        cases vhi <;> dsimp only [] <;> rfl
      | _ => dsimp only []; rfl
    | err =>
      dsimp only [Outcome.encodeCF4]
      cases rhi with
      | val vhi => cases vhi <;> dsimp only [] <;> rfl
      | _ => dsimp only []; rfl
    | broke =>
      dsimp only [Outcome.encodeCF4]
      cases rhi with
      | val vhi => cases vhi <;> dsimp only [] <;> rfl
      | _ => dsimp only []; rfl
    | continued =>
      dsimp only [Outcome.encodeCF4]
      cases rhi with
      | val vhi => cases vhi <;> dsimp only [] <;> rfl
      | _ => dsimp only []; rfl
  | forFoldRevReturn v lo hi body ih_lo ih_hi ih_body =>
    cases hnl with | forFoldRevReturn hllo hlhi hlbody =>
    cases hnq with | forFoldRevReturn hqlo hqhi hqbody =>
    cases hwf with | forFoldRevReturn hwlo hwhi hwbody =>
    intro fuel env
    simp only [cfIntoMonads]; unfold denote'
    simp only [bind, StateT.bind]
    -- Rewrite lo and hi via their IHs
    rw [ih_lo hllo hqlo hwlo fuel env]
    generalize denote' bi fuel lo env = plo
    obtain ⟨rlo, envlo⟩ := plo
    dsimp only []
    rw [ih_hi hlhi hqhi hwhi fuel envlo]
    generalize denote' bi fuel hi envlo = phi
    obtain ⟨rhi, envhi⟩ := phi
    dsimp only []
    -- Derive earlyRet-not-CF for body
    have hbody_er_not_cf : ∀ fuel env w, (denote' bi fuel body env).1 = .earlyRet w →
        w.isControlFlow = false :=
      denote'_earlyRet_not_cf bi body
    -- Case split on rlo
    cases rlo with
    | val vlo =>
      cases rhi with
      | val vhi =>
        simp only [Outcome.encodeCF4]
        cases vlo with
        | int lo_val =>
          cases vhi with
          | int hi_val =>
            dsimp only []
            exact denoteForLoopRev'Return_sim bi v body
              (ih_body hlbody hqbody hwbody) hbody_er_not_cf fuel lo_val hi_val envhi
          | controlFlow => rfl
          | _ => rfl
        | controlFlow => rfl
        | _ =>
          cases vhi with
          | controlFlow => rfl
          | _ => rfl
      | earlyRet w =>
        dsimp only [Outcome.encodeCF4]
        cases vlo with
        | controlFlow => dsimp only []; rfl
        | _ => dsimp only []; rfl
      | err =>
        dsimp only [Outcome.encodeCF4]
        cases vlo <;> dsimp only [] <;> rfl
      | broke =>
        dsimp only [Outcome.encodeCF4]
        cases vlo <;> dsimp only [] <;> rfl
      | continued =>
        dsimp only [Outcome.encodeCF4]
        cases vlo <;> dsimp only [] <;> rfl
    | earlyRet w =>
      dsimp only [Outcome.encodeCF4]
      cases rhi with
      | val vhi =>
        cases vhi <;> dsimp only [] <;> rfl
      | _ => dsimp only []; rfl
    | err =>
      dsimp only [Outcome.encodeCF4]
      cases rhi with
      | val vhi => cases vhi <;> dsimp only [] <;> rfl
      | _ => dsimp only []; rfl
    | broke =>
      dsimp only [Outcome.encodeCF4]
      cases rhi with
      | val vhi => cases vhi <;> dsimp only [] <;> rfl
      | _ => dsimp only []; rfl
    | continued =>
      dsimp only [Outcome.encodeCF4]
      cases rhi with
      | val vhi => cases vhi <;> dsimp only [] <;> rfl
      | _ => dsimp only []; rfl
  | whileFoldReturn c body ih_c ih_body =>
    cases hnl with | whileFoldReturn hlc hlbody =>
    cases hnq with | whileFoldReturn hqc hqbody =>
    cases hwf with | whileFoldReturn hwc hwbody =>
    intro fuel env
    simp only [cfIntoMonads]; unfold denote'
    -- Derive earlyRet-not-CF for body
    have hbody_er_not_cf : ∀ fuel env w, (denote' bi fuel body env).1 = .earlyRet w →
        w.isControlFlow = false :=
      denote'_earlyRet_not_cf bi body
    exact denoteWhile'Return_sim bi c body (ih_c hlc hqc hwc)
      (ih_body hlbody hqbody hwbody) hbody_er_not_cf fuel env
  -- CF constructors: pass-through
  | cfBreak e ih =>
    cases hnl with | cfBreak he =>
    cases hnq with | cfBreak hqe =>
    cases hwf with | cfBreak hwe =>
    intro fuel env
    simp only [cfIntoMonads]; unfold denote'
    simp only [bind, StateT.bind]
    rw [ih he hqe hwe fuel env]
    generalize denote' bi fuel e env = pe
    obtain ⟨re, enve⟩ := pe
    cases re with
    | val v =>
      simp only [Outcome.encodeCF4]
      cases v with
      | controlFlow => rfl
      | _ => rfl
    | earlyRet => rfl
    | err => rfl
    | broke => rfl
    | continued => rfl
  | cfContinue e ih =>
    cases hnl with | cfContinue he =>
    cases hnq with | cfContinue hqe =>
    cases hwf with | cfContinue hwe =>
    intro fuel env
    simp only [cfIntoMonads]; unfold denote'
    simp only [bind, StateT.bind]
    rw [ih he hqe hwe fuel env]
    generalize denote' bi fuel e env = pe
    obtain ⟨re, enve⟩ := pe
    cases re with
    | val v =>
      simp only [Outcome.encodeCF4]
      cases v with
      | controlFlow => rfl
      | _ => rfl
    | earlyRet => rfl
    | err => rfl
    | broke => rfl
    | continued => rfl
  | cfBreakContinue e ih =>
    cases hnl with | cfBreakContinue he =>
    cases hnq with | cfBreakContinue hqe =>
    cases hwf with | cfBreakContinue hwe =>
    intro fuel env
    simp only [cfIntoMonads]; unfold denote'
    simp only [bind, StateT.bind]
    rw [ih he hqe hwe fuel env]
    generalize denote' bi fuel e env = pe
    obtain ⟨re, enve⟩ := pe
    cases re with
    | val v =>
      simp only [Outcome.encodeCF4]
      cases v with
      | controlFlow => rfl
      | _ => rfl
    | earlyRet => rfl
    | err => rfl
    | broke => rfl
    | continued => rfl
  | typeAscription _ _ ih =>
    cases hnl with | typeAscription he =>
    cases hnq with | typeAscription hqe =>
    cases hwf with | typeAscription hwe =>
    intro fuel env
    simp only [cfIntoMonads]; unfold denote'
    exact ih he hqe hwe fuel env

end Hax
