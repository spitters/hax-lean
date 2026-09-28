/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Phase.ContinueFlag

/-!
# Inlining of let-bound local closures

The adapter represents a Rust closure bound by `let` as a first-class value,
`.letBind f (.lam ps body) cont`, and `tLowerClosureCalls` (`InlineClosures`) turns its
invocations into direct calls `.app f args`. `denote'` reads `.lam` as an error, and no
front accepts it. This phase removes such a binding: every call `.app f args` of `cont`
becomes `body` with each parameter replaced by the matching argument
(`inlineCalls f ps body`).

**Fragment.** The phase inlines a binding when `closureOk f ps body cont` holds:

* the body is pure (`isPure`): literals, variables, `unitVal`, calls, tuples and
  projections, so running it changes no variable;
* every call of `f` in `cont` passes pure arguments (`callsOk`);
* no variable the body captures, a variable of the body that is not a parameter
  (`captures`), is bound in `cont` by a `letBind`, an `assign`, a loop counter or a
  pattern (`noBind`).

**Reference reading.** A closure reads its captured variables in the environment of its
definition. `closureTable bi fuel₀ f ps body ρ` is the builtin table that answers a call
of `f` on values `vs` with the value of `body` read with `bi` in `ρ` extended by the
parameters bound to `vs`, and every other name as `bi` does. The binding
`.letBind f (.lam ps body) cont` is read as `cont` with that table, `ρ` the environment
at the binding (`denoteLetClosure`); `denoteSpine` reads that way every binding on the
statement spine of a function body (`letBind` and `seq`) whose continuation, with the
bindings it contains inlined, is in the fragment.

**Agreement.** The rewritten program refines the reference reading: from an environment
agreeing with `ρ` on the captured variables, every run of the reference reading that
does not end in an error is the run of the rewritten program (`RefO`). The converse
fails: a call whose argument goes unused by the body errs in the reference reading and
may not err after inlining.

## Main definitions

* `inlineCalls f ps body`: replace every call of `f` by the body instantiated at the
  arguments.
* `closureOk f ps body cont`: the fragment.
* `inlineSpine`: inline every binding of the fragment on the statement spine.
* `closureTable`, `denoteLetClosure`, `denoteSpine`: the reference reading.
* `Ref`, `RefO`: refinement of runs from environments satisfying an invariant.

## Main results

* `denote'_inlineCalls`: `inlineCalls f ps body cont` read with `bi` refines `cont` read
  with `closureTable bi fuel₀ f ps body ρ`, from an environment agreeing with `ρ` on the
  captures.
* `denote'_inlineLet`: the rewritten binding refines `denoteLetClosure`.
* `denote'_inlineSpine`: `inlineSpine e` read with `bi` refines `denoteSpine bi fuel e`.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.InlineLocalClosures

/-! ## The pure fragment -/

/-- A pure expression: a literal, a variable, `unitVal`, a call, a tuple or a projection
    whose subexpressions are pure. Reading it changes no variable. -/
def isPure : ImpExpr → Bool
  | .lit _ => true
  | .var _ => true
  | .unitVal => true
  | .app _ args => allPure args
  | .tuple es => allPure es
  | .proj e _ => isPure e
  | _ => false
where
  /-- `isPure` of every expression of a list. -/
  allPure : List ImpExpr → Bool
    | [] => true
    | e :: es => isPure e && allPure es

/-- The variables a pure expression reads. -/
def pureVars : ImpExpr → List String
  | .var x => [x]
  | .app _ args => varsList args
  | .tuple es => varsList es
  | .proj e _ => pureVars e
  | _ => []
where
  /-- `pureVars` of every expression of a list, concatenated. -/
  varsList : List ImpExpr → List String
    | [] => []
    | e :: es => pureVars e ++ varsList es

/-- The variables a closure body captures: those it reads that are not parameters. -/
def captures (ps : List String) (body : ImpExpr) : List String :=
  (pureVars body).filter fun x => !ps.contains x

/-! ## Instantiation of the body -/

/-- The argument passed for the variable `x`: the argument at the first position of `x`
    in the parameters. -/
def argFor : List String → List ImpExpr → String → Option ImpExpr
  | p :: ps, a :: as, x => if x = p then some a else argFor ps as x
  | _, _, _ => none

/-- Replace every parameter of a pure expression by its argument. -/
def subst (ps : List String) (args : List ImpExpr) : ImpExpr → ImpExpr
  | .var x => (argFor ps args x).getD (.var x)
  | .app g es => .app g (substList ps args es)
  | .tuple es => .tuple (substList ps args es)
  | .proj e i => .proj (subst ps args e) i
  | e => e
where
  /-- `subst` on every expression of a list. -/
  substList (ps : List String) (args : List ImpExpr) : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => subst ps args e :: substList ps args es

/-- The environment `ρ` with the parameters bound to the values; a parameter repeated in
    the list takes the value of its first position. -/
def bindAll (ρ : Env) : List String → List Value → Env
  | p :: ps, v :: vs => (bindAll ρ ps vs).extend p v
  | _, _ => ρ

/-! ## The rewriting -/

/-- Replace every call `.app f args` with as many arguments as parameters by `body`
    instantiated at the rewritten arguments; every other node is kept. -/
def inlineCalls (f : String) (ps : List String) (body : ImpExpr) : ImpExpr → ImpExpr
  | .lit v => .lit v
  | .var n => .var n
  | .unitVal => .unitVal
  | .continue_ => .continue_
  | .break_ none => .break_ none
  | .break_ (some e) => .break_ (some (inlineCalls f ps body e))
  | .lam qs b => .lam qs (inlineCalls f ps body b)
  | .app g args =>
    if g = f ∧ args.length = ps.length then subst ps (mapExpr f ps body args) body
    else .app g (mapExpr f ps body args)
  | .letBind n v b => .letBind n (inlineCalls f ps body v) (inlineCalls f ps body b)
  | .seq a b => .seq (inlineCalls f ps body a) (inlineCalls f ps body b)
  | .ifThenElse c t e =>
    .ifThenElse (inlineCalls f ps body c) (inlineCalls f ps body t) (inlineCalls f ps body e)
  | .tuple es => .tuple (mapExpr f ps body es)
  | .proj e i => .proj (inlineCalls f ps body e) i
  | .match_ scrut arms => .match_ (inlineCalls f ps body scrut) (mapArms f ps body arms)
  | .borrow e => .borrow (inlineCalls f ps body e)
  | .deref e => .deref (inlineCalls f ps body e)
  | .assign n rhs => .assign n (inlineCalls f ps body rhs)
  | .forLoop v lo hi b =>
    .forLoop v (inlineCalls f ps body lo) (inlineCalls f ps body hi) (inlineCalls f ps body b)
  | .forLoopRev v lo hi b =>
    .forLoopRev v (inlineCalls f ps body lo) (inlineCalls f ps body hi)
      (inlineCalls f ps body b)
  | .whileLoop c b => .whileLoop (inlineCalls f ps body c) (inlineCalls f ps body b)
  | .earlyReturn e => .earlyReturn (inlineCalls f ps body e)
  | .questionMark e => .questionMark (inlineCalls f ps body e)
  | .forFold v lo hi b =>
    .forFold v (inlineCalls f ps body lo) (inlineCalls f ps body hi) (inlineCalls f ps body b)
  | .forFoldRev v lo hi b =>
    .forFoldRev v (inlineCalls f ps body lo) (inlineCalls f ps body hi)
      (inlineCalls f ps body b)
  | .whileFold c b => .whileFold (inlineCalls f ps body c) (inlineCalls f ps body b)
  | .forFoldReturn v lo hi b =>
    .forFoldReturn v (inlineCalls f ps body lo) (inlineCalls f ps body hi)
      (inlineCalls f ps body b)
  | .forFoldRevReturn v lo hi b =>
    .forFoldRevReturn v (inlineCalls f ps body lo) (inlineCalls f ps body hi)
      (inlineCalls f ps body b)
  | .whileFoldReturn c b =>
    .whileFoldReturn (inlineCalls f ps body c) (inlineCalls f ps body b)
  | .cfBreak e => .cfBreak (inlineCalls f ps body e)
  | .cfContinue e => .cfContinue (inlineCalls f ps body e)
  | .cfBreakContinue e => .cfBreakContinue (inlineCalls f ps body e)
  | .typeAscription e ty => .typeAscription (inlineCalls f ps body e) ty
where
  /-- `inlineCalls` on every expression of a list. -/
  mapExpr (f : String) (ps : List String) (body : ImpExpr) : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => inlineCalls f ps body e :: mapExpr f ps body es
  /-- `inlineCalls` on the body of every match arm. -/
  mapArms (f : String) (ps : List String) (body : ImpExpr) :
      List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, inlineCalls f ps body e) :: mapArms f ps body rest

/-! ## The fragment -/

/-- The variables a pattern binds. -/
def patVars : ImpPat → List String
  | .varPat n => [n]
  | .tuplePat pats => patVarsList pats
  | .somePat p => patVars p
  | .okPat p => patVars p
  | .errPat p => patVars p
  | .ctorPat _ pats => patVarsList pats
  | _ => []
where
  /-- `patVars` of every pattern of a list, concatenated. -/
  patVarsList : List ImpPat → List String
    | [] => []
    | p :: ps => patVars p ++ patVarsList ps

/-- No `letBind`, `assign`, loop counter or pattern of `e` binds a variable of `K`. -/
def noBind (K : List String) : ImpExpr → Bool
  | .letBind n v b => !K.contains n && noBind K v && noBind K b
  | .assign n rhs => !K.contains n && noBind K rhs
  | .lam _ b => noBind K b
  | .app _ args => noBindList K args
  | .tuple es => noBindList K es
  | .proj e _ => noBind K e
  | .ifThenElse c t e => noBind K c && noBind K t && noBind K e
  | .match_ scrut arms => noBind K scrut && noBindArms K arms
  | .seq a b => noBind K a && noBind K b
  | .borrow e => noBind K e
  | .deref e => noBind K e
  | .forLoop v lo hi b => !K.contains v && noBind K lo && noBind K hi && noBind K b
  | .forLoopRev v lo hi b => !K.contains v && noBind K lo && noBind K hi && noBind K b
  | .whileLoop c b => noBind K c && noBind K b
  | .break_ (some e) => noBind K e
  | .earlyReturn e => noBind K e
  | .questionMark e => noBind K e
  | .forFold v lo hi b => !K.contains v && noBind K lo && noBind K hi && noBind K b
  | .forFoldRev v lo hi b => !K.contains v && noBind K lo && noBind K hi && noBind K b
  | .whileFold c b => noBind K c && noBind K b
  | .forFoldReturn v lo hi b => !K.contains v && noBind K lo && noBind K hi && noBind K b
  | .forFoldRevReturn v lo hi b =>
    !K.contains v && noBind K lo && noBind K hi && noBind K b
  | .whileFoldReturn c b => noBind K c && noBind K b
  | .cfBreak e => noBind K e
  | .cfContinue e => noBind K e
  | .cfBreakContinue e => noBind K e
  | .typeAscription e _ => noBind K e
  | _ => true
where
  /-- `noBind` of every expression of a list. -/
  noBindList (K : List String) : List ImpExpr → Bool
    | [] => true
    | e :: es => noBind K e && noBindList K es
  /-- No pattern of an arm binds a variable of `K`, nor does any arm body. -/
  noBindArms (K : List String) : List (ImpPat × ImpExpr) → Bool
    | [] => true
    | (p, e) :: rest => (patVars p).all (fun x => !K.contains x) && noBind K e &&
        noBindArms K rest

/-- Every call of `f` in `e` passes pure arguments. -/
def callsOk (f : String) : ImpExpr → Bool
  | .app g args => (g != f || isPure.allPure args) && callsOkList f args
  | .letBind _ v b => callsOk f v && callsOk f b
  | .assign _ rhs => callsOk f rhs
  | .lam _ b => callsOk f b
  | .tuple es => callsOkList f es
  | .proj e _ => callsOk f e
  | .ifThenElse c t e => callsOk f c && callsOk f t && callsOk f e
  | .match_ scrut arms => callsOk f scrut && callsOkArms f arms
  | .seq a b => callsOk f a && callsOk f b
  | .borrow e => callsOk f e
  | .deref e => callsOk f e
  | .forLoop _ lo hi b => callsOk f lo && callsOk f hi && callsOk f b
  | .forLoopRev _ lo hi b => callsOk f lo && callsOk f hi && callsOk f b
  | .whileLoop c b => callsOk f c && callsOk f b
  | .break_ (some e) => callsOk f e
  | .earlyReturn e => callsOk f e
  | .questionMark e => callsOk f e
  | .forFold _ lo hi b => callsOk f lo && callsOk f hi && callsOk f b
  | .forFoldRev _ lo hi b => callsOk f lo && callsOk f hi && callsOk f b
  | .whileFold c b => callsOk f c && callsOk f b
  | .forFoldReturn _ lo hi b => callsOk f lo && callsOk f hi && callsOk f b
  | .forFoldRevReturn _ lo hi b => callsOk f lo && callsOk f hi && callsOk f b
  | .whileFoldReturn c b => callsOk f c && callsOk f b
  | .cfBreak e => callsOk f e
  | .cfContinue e => callsOk f e
  | .cfBreakContinue e => callsOk f e
  | .typeAscription e _ => callsOk f e
  | _ => true
where
  /-- `callsOk` of every expression of a list. -/
  callsOkList (f : String) : List ImpExpr → Bool
    | [] => true
    | e :: es => callsOk f e && callsOkList f es
  /-- `callsOk` of every arm body. -/
  callsOkArms (f : String) : List (ImpPat × ImpExpr) → Bool
    | [] => true
    | (_, e) :: rest => callsOk f e && callsOkArms f rest

/-- The binding `.letBind f (.lam ps body) cont` is in the fragment: a pure body, pure
    arguments at every call of `f`, and no binding of a captured variable in `cont`. -/
def closureOk (f : String) (ps : List String) (body cont : ImpExpr) : Bool :=
  isPure body && callsOk f cont && noBind (captures ps body) cont

/-- Inline every binding of the fragment on the statement spine (`letBind` and `seq`)
    of a function body, innermost first. -/
def inlineSpine : ImpExpr → ImpExpr
  | .letBind f (.lam ps body) cont =>
    if closureOk f ps body (inlineSpine cont) then inlineCalls f ps body (inlineSpine cont)
    else .letBind f (.lam ps body) (inlineSpine cont)
  | .letBind x v cont => .letBind x v (inlineSpine cont)
  | .seq a b => .seq a (inlineSpine b)
  | e => e

/-! ## The reference reading -/

/-- The builtin table of a closure: a call of `f` on as many values as parameters is
    answered by the value of `body` read with `bi` at fuel `fuel₀` in `ρ` with the
    parameters bound to the values; every other name is answered by `bi`. -/
def closureTable (bi : Builtins) (fuel₀ : Nat) (f : String) (ps : List String)
    (body : ImpExpr) (ρ : Env) : Builtins := fun g vals =>
  if g = f then
    if vals.length = ps.length then
      match ((denote' bi fuel₀ body).run (bindAll ρ ps vals)).1 with
      | .val v => some v
      | _ => none
    else none
  else bi g vals

/-- The reading of `.letBind f (.lam ps body) cont`: `cont` read with the builtin table
    of the closure, `ρ` the environment at the binding. -/
def denoteLetClosure (bi : Builtins) (fuel : Nat) (f : String) (ps : List String)
    (body cont : ImpExpr) : StateM Env Outcome := do
  let ρ ← get
  denote' (closureTable bi fuel f ps body ρ) fuel cont

/-- The reference reading of a function body: along the statement spine a binding whose
    continuation, with the bindings it contains inlined, is in the fragment is read as in
    `denoteLetClosure`, and every other expression by `denote'`. -/
def denoteSpine (bi : Builtins) (fuel : Nat) : ImpExpr → StateM Env Outcome
  | .letBind f (.lam ps body) cont =>
    if closureOk f ps body (inlineSpine cont) then do
      let ρ ← get
      denoteSpine (closureTable bi fuel f ps body ρ) fuel cont
    else denote' bi fuel (.letBind f (.lam ps body) cont)
  | .letBind x v cont => do
    let rv ← denote' bi fuel v
    match rv with
    | .val (.controlFlow isBreak w) => pure (.val (.controlFlow isBreak w))
    | .val w => do modify (Env.extend · x w); denoteSpine bi fuel cont
    | other => pure other
  | .seq a b => do
    let r ← denote' bi fuel a
    match r with
    | .val (.controlFlow isBreak w) => pure (.val (.controlFlow isBreak w))
    | .val _ => denoteSpine bi fuel b
    | other => pure other
  | e => denote' bi fuel e

/-! ## Refinement under an invariant -/

/-- `tgt` refines `src` from environments satisfying `A`: every run of `src` from such
    an environment whose result is not `bad` is the run of `tgt`, and ends in an
    environment satisfying `A`. -/
def Ref {α : Type} (A : Env → Prop) (bad : α → Prop) (tgt src : StateM Env α) : Prop :=
  ∀ env, A env → ∀ o s, src.run env = (o, s) → ¬ bad o → tgt.run env = (o, s) ∧ A s

/-- An outcome that is an error. -/
def IsErr (o : Outcome) : Prop := ∃ m, o = .err m

/-- `Ref` on outcomes, an error being the result excluded. -/
abbrev RefO (A : Env → Prop) (tgt src : StateM Env Outcome) : Prop := Ref A IsErr tgt src

/-- `Ref` on the argument lists of `denoteArgs'`, `none` being the result excluded. -/
abbrev RefA (A : Env → Prop) (tgt src : StateM Env (Option (List Value))) : Prop :=
  Ref A (fun o => o = none) tgt src

theorem run_bind {α β : Type} (x : StateM Env α) (k : α → StateM Env β) (env : Env) :
    (x >>= k).run env = (k (x.run env).1).run (x.run env).2 := rfl

section Ref

variable {A : Env → Prop}

theorem Ref.pure {α : Type} {bad : α → Prop} (a : α) : Ref A bad (pure a) (pure a) := by
  intro env hA o s h _
  exact ⟨h, by cases h; exact hA⟩

theorem Ref.of_bad {α : Type} {bad : α → Prop} {tgt src : StateM Env α}
    (h : ∀ env, bad (src.run env).1) : Ref A bad tgt src := by
  intro env _ o s hr hb
  have := h env
  rw [hr] at this
  exact absurd this hb

theorem Ref.bind {α β : Type} {badα : α → Prop} {badβ : β → Prop}
    {m₁ m₂ : StateM Env α} {k₁ k₂ : α → StateM Env β}
    (hm : Ref A badα m₁ m₂) (hk : ∀ a, ¬ badα a → Ref A badβ (k₁ a) (k₂ a))
    (hb : ∀ a, badα a → ∀ s, badβ ((k₂ a).run s).1) :
    Ref A badβ (m₁ >>= k₁) (m₂ >>= k₂) := by
  intro env hA o s h hnb
  rw [run_bind] at h
  by_cases ha : badα (m₂.run env).1
  · exact absurd (by have := hb _ ha (m₂.run env).2; rw [h] at this; exact this) hnb
  · obtain ⟨h₁, hA₁⟩ := hm env hA _ _ rfl ha
    rw [run_bind, h₁]
    exact hk _ ha _ hA₁ o s h hnb

theorem Ref.get {α : Type} {bad : α → Prop} {k₁ k₂ : Env → StateM Env α}
    (h : ∀ e, A e → Ref A bad (k₁ e) (k₂ e)) :
    Ref A bad (MonadState.get >>= k₁) (MonadState.get >>= k₂) := by
  intro env hA o s hr hb
  exact h env hA env hA o s hr hb

theorem Ref.modify {α : Type} {bad : α → Prop} (g : Env → Env) (hg : ∀ e, A e → A (g e))
    {k₁ k₂ : PUnit → StateM Env α} (h : ∀ u, Ref A bad (k₁ u) (k₂ u)) :
    Ref A bad (modify g >>= k₁) (modify g >>= k₂) := by
  intro env hA o s hr hb
  exact h _ _ (hg env hA) o s hr hb

end Ref

/-! ## Pure expressions -/

section Pure

variable (bi : Builtins)

theorem tuple_run (fuel : Nat) (es : List ImpExpr) (env : Env) :
    (denote' bi fuel (.tuple es)).run env =
      match (denoteArgs' bi fuel es).run env with
      | (some vals, e1) => (.val (.tuple vals), e1)
      | (none, e1) => (.err "non-value in tuple elements", e1) := by
  simp only [denote', StateT.run, bind, StateT.bind, pure]
  rcases (denoteArgs' bi fuel es) env with ⟨o, e1⟩
  rcases o with _ | vals <;> rfl

theorem proj_run (fuel : Nat) (e : ImpExpr) (i : Nat) (env : Env) :
    (denote' bi fuel (.proj e i)).run env =
      match (denote' bi fuel e).run env with
      | (.val (.controlFlow k v), e1) => (.val (.controlFlow k v), e1)
      | (.val v, e1) =>
        match v.projIdx i with
        | some vi => (.val vi, e1)
        | none => (.err s!"projection index {i} out of range", e1)
      | (o, e1) => (o, e1) := by
  simp only [denote', StateT.run, bind, StateT.bind, pure]
  rcases (denote' bi fuel e) env with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _ <;> try rfl
  cases v <;> try rfl
  all_goals (simp only; split <;> simp_all <;> rfl)

theorem allPure_eq (es : List ImpExpr) : isPure.allPure es = es.all isPure := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [isPure.allPure, ih]

/-- A pure expression changes no variable, and its outcome does not depend on the
    fuel. -/
def PureRun (e : ImpExpr) : Prop :=
  ∀ fuel fuel' env, (denote' bi fuel e).run env = (((denote' bi fuel' e).run env).1, env)

theorem pureArgs_run (es : List ImpExpr) (ih : ∀ a, a ∈ es → PureRun bi a) :
    ∀ fuel fuel' env, (denoteArgs' bi fuel es).run env =
      (((denoteArgs' bi fuel' es).run env).1, env) := by
  induction es with
  | nil => intro fuel fuel' env; simp only [ContinueFlag.args_nil_run]
  | cons e es ihes =>
    intro fuel fuel' env
    have he := ih e List.mem_cons_self
    have hes := ihes (fun a ha => ih a (List.mem_cons_of_mem e ha))
    obtain ⟨o, ho⟩ : ∃ o, (denote' bi fuel' e).run env = (o, env) := ⟨_, he fuel' fuel' env⟩
    have ho' : (denote' bi fuel e).run env = (o, env) := by rw [he fuel fuel' env, ho]
    rw [ContinueFlag.args_cons_run, ContinueFlag.args_cons_run, ho, ho']
    rcases o with v | _ | _ | _ | _ <;> try rfl
    cases v <;> simp only [hes fuel fuel' env]

theorem pure_run (e : ImpExpr) (he : isPure e = true) : PureRun bi e := by
  induction e using ImpExpr.ind with
  | lit l => intro fuel fuel' env; simp only [ContinueFlag.lit_run]
  | var x =>
    intro fuel fuel' env; simp only [ContinueFlag.var_run]; cases env x <;> rfl
  | unitVal => intro fuel fuel' env; simp only [ContinueFlag.unitVal_run]
  | app f args ih =>
    simp only [isPure, allPure_eq, List.all_eq_true] at he
    intro fuel fuel' env
    have hp := pureArgs_run bi args (fun a ha => ih a ha (he a ha))
    obtain ⟨o, ho⟩ : ∃ o, (denoteArgs' bi fuel' args).run env = (o, env) :=
      ⟨_, hp fuel' fuel' env⟩
    have ho' : (denoteArgs' bi fuel args).run env = (o, env) := by rw [hp fuel fuel' env, ho]
    rw [ContinueFlag.app_run, ContinueFlag.app_run, ho, ho']
    rcases o with _ | vals
    · rfl
    · simp only; split <;> rfl
  | tuple es ih =>
    simp only [isPure, allPure_eq, List.all_eq_true] at he
    intro fuel fuel' env
    have hp := pureArgs_run bi es (fun a ha => ih a ha (he a ha))
    obtain ⟨o, ho⟩ : ∃ o, (denoteArgs' bi fuel' es).run env = (o, env) :=
      ⟨_, hp fuel' fuel' env⟩
    have ho' : (denoteArgs' bi fuel es).run env = (o, env) := by rw [hp fuel fuel' env, ho]
    rw [tuple_run, tuple_run, ho, ho']
    rcases o with _ | vals <;> rfl
  | proj e i ih =>
    simp only [isPure] at he
    intro fuel fuel' env
    have hp := ih he
    obtain ⟨o, ho⟩ : ∃ o, (denote' bi fuel' e).run env = (o, env) := ⟨_, hp fuel' fuel' env⟩
    have ho' : (denote' bi fuel e).run env = (o, env) := by rw [hp fuel fuel' env, ho]
    rw [proj_run, proj_run, ho, ho']
    rcases o with v | _ | _ | _ | _ <;> try rfl
    cases v <;> try rfl
    all_goals (simp only; split <;> simp_all <;> rfl)
  | _ => simp [isPure] at he

theorem subst.substList_eq (ps : List String) (args es : List ImpExpr) :
    subst.substList ps args es = es.map (subst ps args) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [subst.substList, ih]

theorem pureVars.varsList_eq (es : List ImpExpr) :
    pureVars.varsList es = es.flatMap pureVars := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [pureVars.varsList, ih]

/-- The run of a pure expression from `σ` with its variables read through the
    arguments. -/
def SubstRun (ps : List String) (args : List ImpExpr) (fuel fuel₀ : Nat) (σ ρ' : Env)
    (b : ImpExpr) : Prop :=
  (denote' bi fuel (subst ps args b)).run σ = (((denote' bi fuel₀ b).run ρ').1, σ)

theorem substArgs_run (ps : List String) (args : List ImpExpr) (fuel fuel₀ : Nat)
    (σ ρ' : Env) (es : List ImpExpr) (hp : ∀ a, a ∈ es → isPure a = true)
    (ih : ∀ a, a ∈ es → SubstRun bi ps args fuel fuel₀ σ ρ' a) :
    (denoteArgs' bi fuel (es.map (subst ps args))).run σ =
      (((denoteArgs' bi fuel₀ es).run ρ').1, σ) := by
  induction es with
  | nil => simp only [List.map_nil, ContinueFlag.args_nil_run]
  | cons e es ihes =>
    have he := ih e List.mem_cons_self
    have hes := ihes (fun a ha => hp a (List.mem_cons_of_mem e ha))
      (fun a ha => ih a (List.mem_cons_of_mem e ha))
    have hsrc := pure_run bi e (hp e List.mem_cons_self) fuel₀ fuel₀ ρ'
    have hsrcs := pureArgs_run bi es
      (fun a ha => pure_run bi a (hp a (List.mem_cons_of_mem e ha))) fuel₀ fuel₀
    simp only [SubstRun] at he
    rw [List.map_cons, ContinueFlag.args_cons_run, ContinueFlag.args_cons_run, he, hsrc]
    rcases ((denote' bi fuel₀ e).run ρ').1 with v | _ | _ | _ | _ <;> try rfl
    cases v <;> dsimp only <;> first | rfl | rw [hes, hsrcs ρ']

theorem subst_run (ps : List String) (args : List ImpExpr) (fuel fuel₀ : Nat) (σ ρ' : Env)
    (b : ImpExpr) (hb : isPure b = true)
    (hvar : ∀ x, x ∈ pureVars b →
      (denote' bi fuel ((argFor ps args x).getD (.var x))).run σ =
        (((denote' bi fuel₀ (.var x)).run ρ').1, σ)) :
    SubstRun bi ps args fuel fuel₀ σ ρ' b := by
  induction b using ImpExpr.ind with
  | var x => exact hvar x (by simp [pureVars])
  | lit l => simp only [SubstRun, subst, ContinueFlag.lit_run]
  | unitVal => simp only [SubstRun, subst, ContinueFlag.unitVal_run]
  | app f es ih =>
    simp only [isPure, allPure_eq, List.all_eq_true] at hb
    simp only [pureVars, pureVars.varsList_eq, List.mem_flatMap] at hvar
    have hargs := substArgs_run bi ps args fuel fuel₀ σ ρ' es hb
      (fun a ha => ih a ha (hb a ha) (fun x hx => hvar x ⟨a, ha, hx⟩))
    have hsrc := pureArgs_run bi es (fun a ha => pure_run bi a (hb a ha)) fuel₀ fuel₀ ρ'
    simp only [SubstRun, subst, subst.substList_eq]
    rw [ContinueFlag.app_run, ContinueFlag.app_run, hargs, hsrc]
    rcases ((denoteArgs' bi fuel₀ es).run ρ').1 with _ | vals
    · rfl
    · simp only; split <;> rfl
  | tuple es ih =>
    simp only [isPure, allPure_eq, List.all_eq_true] at hb
    simp only [pureVars, pureVars.varsList_eq, List.mem_flatMap] at hvar
    have hargs := substArgs_run bi ps args fuel fuel₀ σ ρ' es hb
      (fun a ha => ih a ha (hb a ha) (fun x hx => hvar x ⟨a, ha, hx⟩))
    have hsrc := pureArgs_run bi es (fun a ha => pure_run bi a (hb a ha)) fuel₀ fuel₀ ρ'
    simp only [SubstRun, subst, subst.substList_eq]
    rw [tuple_run, tuple_run, hargs, hsrc]
    rcases ((denoteArgs' bi fuel₀ es).run ρ').1 with _ | vals <;> rfl
  | proj e i ih =>
    simp only [isPure] at hb
    simp only [pureVars] at hvar
    have he := ih hb hvar
    have hsrc := pure_run bi e hb fuel₀ fuel₀ ρ'
    simp only [SubstRun, subst] at he ⊢
    rw [proj_run, proj_run, he, hsrc]
    clear he hsrc hvar ih
    rcases ((denote' bi fuel₀ e).run ρ').1 with v | _ | _ | _ | _ <;> try rfl
    cases v <;> try rfl
    all_goals (simp only; split <;> simp_all <;> rfl)
  | _ => simp [isPure] at hb

/-- A variable read through the arguments: a parameter reads the value of its argument,
    and any other variable reads the same value in `σ` as in `ρ`. -/
theorem argFor_run (fuel fuel₀ : Nat) (σ ρ : Env) (x : String) :
    ∀ (ps : List String) (targs : List ImpExpr) (vals : List Value),
      (∀ av, av ∈ targs.zip vals → (denote' bi fuel av.1).run σ = (.val av.2, σ)) →
      targs.length = ps.length → vals.length = ps.length → (x ∉ ps → σ x = ρ x) →
      (denote' bi fuel ((argFor ps targs x).getD (.var x))).run σ =
        (((denote' bi fuel₀ (.var x)).run (bindAll ρ ps vals)).1, σ)
  | [], targs, vals, _, _, _, hx => by
    have hσ := hx List.not_mem_nil
    have hv : (denote' bi fuel (.var x)).run σ = (((denote' bi fuel₀ (.var x)).run ρ).1, σ) := by
      simp only [ContinueFlag.var_run, hσ]; cases ρ x <;> rfl
    cases targs <;> cases vals <;> exact hv
  | _ :: _, [], _, _, hl, _, _ => by simp at hl
  | _ :: _, _ :: _, [], _, _, hl, _ => by simp at hl
  | p :: ps, a :: as, v :: vs, h2, hl, hl', hx => by
    simp only [argFor, bindAll]
    by_cases hxp : x = p
    · subst hxp
      have ha := h2 (a, v) (by simp)
      simp only [if_true, Option.getD_some, ha, ContinueFlag.var_run, Env.extend_same]
    · simp only [hxp, if_false]
      rw [argFor_run fuel fuel₀ σ ρ x ps as vs (fun av h => h2 av (by simp [h]))
        (by simpa using hl) (by simpa using hl') (fun h => hx (by simp [hxp, h]))]
      simp only [ContinueFlag.var_run, Env.extend_other _ _ _ _ hxp]
      cases bindAll ρ ps vs x <;> rfl

/-- The arguments of a pure call that evaluate to values: one value per argument, each
    the value of its argument, with the environment unchanged. -/
theorem pureArgs_vals (fuel : Nat) (σ : Env) :
    ∀ (args : List ImpExpr) (vals : List Value) (s : Env),
      (∀ a, a ∈ args → isPure a = true) →
      (denoteArgs' bi fuel args).run σ = (some vals, s) →
      s = σ ∧ vals.length = args.length ∧
        ∀ av, av ∈ args.zip vals → (denote' bi fuel av.1).run σ = (.val av.2, σ)
  | [], vals, s, _, h => by
    rw [ContinueFlag.args_nil_run] at h
    cases h; exact ⟨rfl, rfl, by simp⟩
  | a :: as, vals, s, hp, h => by
    have ha := pure_run bi a (hp a List.mem_cons_self) fuel fuel σ
    rw [ContinueFlag.args_cons_run, ha] at h
    have hpa : ∀ b, b ∈ as → isPure b = true := fun b hb => hp b (List.mem_cons_of_mem a hb)
    generalize ho : ((denote' bi fuel a).run σ).1 = o at h ha
    rcases o with v | _ | _ | _ | _
    case val =>
      cases v
      case controlFlow => exact absurd (congrArg Prod.fst h) (by simp)
      all_goals
        try simp only at h
        obtain ⟨hv, hs⟩ := Prod.mk.inj h
        cases hrest : ((denoteArgs' bi fuel as).run σ).1 with
        | none => rw [hrest] at hv; simp at hv
        | some vs =>
          rw [hrest] at hv
          simp only [Option.map_some, Option.some.injEq] at hv
          have hr : (denoteArgs' bi fuel as).run σ = (some vs, σ) := by
            rw [pureArgs_run bi as (fun b hb => pure_run bi b (hpa b hb)) fuel fuel σ, hrest]
          obtain ⟨-, hlen, hz⟩ := pureArgs_vals fuel σ as vs σ hpa hr
          rw [hr] at hs
          subst hv hs
          refine ⟨rfl, by simp [hlen], ?_⟩
          intro av hav
          simp only [List.zip_cons_cons, List.mem_cons] at hav
          rcases hav with rfl | hav
          · exact ha
          · exact hz av hav
    all_goals exact absurd (congrArg Prod.fst h) (by simp)

end Pure

/-! ## A call of the closure -/

@[simp] theorem inlineCalls.mapExpr_eq (f : String) (ps : List String) (body : ImpExpr)
    (es : List ImpExpr) : inlineCalls.mapExpr f ps body es = es.map (inlineCalls f ps body) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [inlineCalls.mapExpr, ih]

@[simp] theorem inlineCalls.mapArms_eq (f : String) (ps : List String) (body : ImpExpr)
    (arms : List (ImpPat × ImpExpr)) :
    inlineCalls.mapArms f ps body arms = arms.map fun (p, e) => (p, inlineCalls f ps body e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [inlineCalls.mapArms, ih]

/-- A match binds only the variables of its pattern. -/
theorem matchPat_frame (x : String) (pat : ImpPat) (v : Value) (env : Env) :
    ∀ env', matchPat pat v env = some env' → x ∉ patVars pat → env' x = env x := by
  induction pat, v, env using matchPat.induct (motive_1 := fun pats vs env =>
      ∀ env', matchPat.matchPatList pats vs env = some env' →
        x ∉ patVars.patVarsList pats → env' x = env x) with
  | case15 p ps v vs env ih2 ih1 =>
    rename_i env' h hx
    simp only [matchPat.matchPatList, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨mid, h1, h2⟩ := h
    simp only [patVars.patVarsList, List.mem_append, not_or] at hx
    rw [ih1 mid env' h2 hx.2, ih2 mid h1 hx.1]
  | case4 name v' env =>
    intro env' h hx
    simp only [matchPat, Option.some.injEq] at h
    subst h
    simp only [patVars, List.mem_singleton] at hx
    exact Env.extend_other _ _ _ _ hx
  | _ =>
    intros
    simp_all [matchPat, matchPat.matchPatList, patVars, patVars.patVarsList]

/-- The environment `env` agrees with `ρ` on the variables `K`. -/
def Agree (K : List String) (ρ env : Env) : Prop := ∀ x, x ∈ K → env x = ρ x

theorem Agree.extend {K : List String} {ρ e : Env} (h : Agree K ρ e) {n : String}
    (hn : n ∉ K) (w : Value) : Agree K ρ (e.extend n w) := by
  intro x hx
  have : x ≠ n := by rintro rfl; exact hn hx
  rw [Env.extend_other _ _ _ _ this]; exact h x hx

theorem Ref.set {α : Type} {A : Env → Prop} {bad : α → Prop} {e' : Env} (hA : A e')
    {k₁ k₂ : PUnit → StateM Env α} (h : ∀ u, Ref A bad (k₁ u) (k₂ u)) :
    Ref A bad (MonadStateOf.set e' >>= k₁) (MonadStateOf.set e' >>= k₂) := by
  intro env _ o s hr hb
  exact h _ _ hA o s hr hb

theorem Ref.modify_extend {α : Type} {bad : α → Prop} {K : List String} {ρ : Env}
    {n : String} (hn : n ∉ K) (w : Value) {k₁ k₂ : PUnit → StateM Env α}
    (h : ∀ u, Ref (Agree K ρ) bad (k₁ u) (k₂ u)) :
    Ref (Agree K ρ) bad (_root_.modify (fun x => x.extend n w) >>= k₁)
      (_root_.modify (fun x => x.extend n w) >>= k₂) :=
  Ref.modify _ (fun _ he => Agree.extend he hn w) h

/-- One step of a `Ref` proof between two runs of the same shape: identical pure steps, a
    hypothesis, an environment update that keeps the invariant, or a bind of two related
    runs followed by a case split on the outcome. -/
scoped syntax "ref_step" : tactic

macro_rules
  | `(tactic| ref_step) => `(tactic| first
      | exact Ref.pure _
      | (apply Ref.of_bad; intro _; exact ⟨_, rfl⟩)
      | solve_by_elim (maxDepth := 2)
      | (refine Ref.modify_extend (by first | assumption | simp_all) _ (fun _ => ?_); ref_step)
      | (refine Ref.get (fun _ _ => ?_); split <;> ref_step)
      | (refine Ref.bind (badα := IsErr) (by solve_by_elim (maxDepth := 2)) (fun o ho => ?_)
            (fun a ha s => by
              obtain ⟨m, hm⟩ := ha; subst hm
              first
                | exact ⟨m, rfl⟩
                | (split <;> first | exact ⟨_, rfl⟩ | (exfalso; simp_all) | simp_all [IsErr]))
         split <;> first | ref_step | (exfalso; simp_all [IsErr])))

section Loops

variable {K : List String} {ρ : Env} {bi₁ bi₂ : Builtins}

theorem forLoop'_ref {v : String} {b₁ b₂ : ImpExpr} (hv : v ∉ K)
    (h : ∀ fuel, RefO (Agree K ρ) (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel lo hi, RefO (Agree K ρ) (denoteForLoop' bi₁ fuel v lo hi b₁)
      (denoteForLoop' bi₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero => intro lo hi; unfold denoteForLoop'; by_cases hl : lo ≥ hi <;> simp [hl] <;> ref_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoop'
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; ref_step
    · simp only [hl, if_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      refine Ref.modify_extend hv _ (fun _ => ?_)
      refine Ref.bind (h _) (fun o ho => ?_) (fun a ha s => ?_)
      · split <;> first | exact Ref.pure _ | exact ih _ _ | (exfalso; simp_all [IsErr])
      · obtain ⟨m, rfl⟩ := ha; exact ⟨m, rfl⟩

theorem forLoopRev'_ref {v : String} {b₁ b₂ : ImpExpr} (hv : v ∉ K)
    (h : ∀ fuel, RefO (Agree K ρ) (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel lo hi, RefO (Agree K ρ) (denoteForLoopRev' bi₁ fuel v lo hi b₁)
      (denoteForLoopRev' bi₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopRev'; by_cases hl : lo ≥ hi <;> simp [hl] <;> ref_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoopRev'
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; ref_step
    · simp only [hl, if_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      ref_step

theorem forLoopOrig'_ref {v : String} {b₁ b₂ : ImpExpr} (hv : v ∉ K)
    (h : ∀ fuel, RefO (Agree K ρ) (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel lo hi, RefO (Agree K ρ) (denoteForLoopOrig' bi₁ fuel v lo hi b₁)
      (denoteForLoopOrig' bi₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopOrig'; by_cases hl : lo ≥ hi <;> simp [hl] <;> ref_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoopOrig'
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; ref_step
    · simp only [hl, if_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      ref_step

theorem forLoopRevOrig'_ref {v : String} {b₁ b₂ : ImpExpr} (hv : v ∉ K)
    (h : ∀ fuel, RefO (Agree K ρ) (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel lo hi, RefO (Agree K ρ) (denoteForLoopRevOrig' bi₁ fuel v lo hi b₁)
      (denoteForLoopRevOrig' bi₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopRevOrig'
    by_cases hl : lo ≥ hi <;> simp [hl] <;> ref_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoopRevOrig'
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; ref_step
    · simp only [hl, if_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      ref_step

theorem forLoop'Return_ref {v : String} {b₁ b₂ : ImpExpr} (hv : v ∉ K)
    (h : ∀ fuel, RefO (Agree K ρ) (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel lo hi, RefO (Agree K ρ) (denoteForLoop'Return bi₁ fuel v lo hi b₁)
      (denoteForLoop'Return bi₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoop'Return
    by_cases hl : lo ≥ hi <;> simp [hl] <;> ref_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoop'Return
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; ref_step
    · simp only [hl, if_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      ref_step

theorem forLoopRev'Return_ref {v : String} {b₁ b₂ : ImpExpr} (hv : v ∉ K)
    (h : ∀ fuel, RefO (Agree K ρ) (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel lo hi, RefO (Agree K ρ) (denoteForLoopRev'Return bi₁ fuel v lo hi b₁)
      (denoteForLoopRev'Return bi₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopRev'Return
    by_cases hl : lo ≥ hi <;> simp [hl] <;> ref_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoopRev'Return
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; ref_step
    · simp only [hl, if_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      ref_step

theorem while'_ref {c₁ c₂ b₁ b₂ : ImpExpr}
    (hc : ∀ fuel, RefO (Agree K ρ) (denote' bi₁ fuel c₁) (denote' bi₂ fuel c₂))
    (h : ∀ fuel, RefO (Agree K ρ) (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel, RefO (Agree K ρ) (denoteWhile' bi₁ fuel c₁ b₁) (denoteWhile' bi₂ fuel c₂ b₂) := by
  intro fuel
  induction fuel with
  | zero => unfold denoteWhile'; simp only [if_true]; ref_step
  | succ n ih =>
    unfold denoteWhile'
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    ref_step

theorem whileOrig'_ref {c₁ c₂ b₁ b₂ : ImpExpr}
    (hc : ∀ fuel, RefO (Agree K ρ) (denote' bi₁ fuel c₁) (denote' bi₂ fuel c₂))
    (h : ∀ fuel, RefO (Agree K ρ) (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel, RefO (Agree K ρ) (denoteWhileOrig' bi₁ fuel c₁ b₁)
      (denoteWhileOrig' bi₂ fuel c₂ b₂) := by
  intro fuel
  induction fuel with
  | zero => unfold denoteWhileOrig'; simp only [if_true]; ref_step
  | succ n ih =>
    unfold denoteWhileOrig'
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    ref_step

theorem while'Return_ref {c₁ c₂ b₁ b₂ : ImpExpr}
    (hc : ∀ fuel, RefO (Agree K ρ) (denote' bi₁ fuel c₁) (denote' bi₂ fuel c₂))
    (h : ∀ fuel, RefO (Agree K ρ) (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel, RefO (Agree K ρ) (denoteWhile'Return bi₁ fuel c₁ b₁)
      (denoteWhile'Return bi₂ fuel c₂ b₂) := by
  intro fuel
  induction fuel with
  | zero => unfold denoteWhile'Return; simp only [if_true]; ref_step
  | succ n ih =>
    unfold denoteWhile'Return
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    ref_step

theorem args_ref (g : ImpExpr → ImpExpr) (args : List ImpExpr)
    (ih : ∀ a, a ∈ args → ∀ fuel,
      RefO (Agree K ρ) (denote' bi₁ fuel (g a)) (denote' bi₂ fuel a)) (fuel : Nat) :
    RefA (Agree K ρ) (denoteArgs' bi₁ fuel (args.map g)) (denoteArgs' bi₂ fuel args) := by
  induction args with
  | nil => simp only [List.map_nil, denoteArgs']; exact Ref.pure _
  | cons a as iha =>
    simp only [List.map_cons, denoteArgs']
    refine Ref.bind (badα := IsErr) (ih a List.mem_cons_self fuel) (fun o ho => ?_)
      (fun o ho s => by obtain ⟨m, hm⟩ := ho; subst hm; rfl)
    split
    · exact Ref.pure _
    · exact Ref.bind (badα := fun o => o = none)
        (iha fun b hb => ih b (List.mem_cons_of_mem a hb))
        (fun _ _ => Ref.pure _) (fun r hr s => by subst hr; rfl)
    · exact Ref.pure _

theorem arms_ref (g : ImpExpr → ImpExpr) (arms : List (ImpPat × ImpExpr))
    (hK : ∀ pa, pa ∈ arms → ∀ x, x ∈ patVars pa.1 → K.contains x = false)
    (ih : ∀ pa, pa ∈ arms → ∀ fuel,
      RefO (Agree K ρ) (denote' bi₁ fuel (g pa.2)) (denote' bi₂ fuel pa.2))
    (fuel : Nat) (v : Value) :
    RefO (Agree K ρ) (denoteMatchArms' bi₁ fuel v (arms.map fun (p, e) => (p, g e)))
      (denoteMatchArms' bi₂ fuel v arms) := by
  induction arms with
  | nil => simp only [List.map_nil, denoteMatchArms']; exact Ref.pure _
  | cons pa rest iha =>
    obtain ⟨p, e⟩ := pa
    simp only [List.map_cons, denoteMatchArms']
    refine Ref.get fun env he => ?_
    split
    · rename_i env' hm
      refine Ref.set (fun x hx => ?_) (fun _ => ih (p, e) List.mem_cons_self fuel)
      rw [matchPat_frame x p v env env' hm (fun hxp => by
        have := hK (p, e) List.mem_cons_self x hxp
        simp [hx] at this)]
      exact he x hx
    · exact iha (fun pa hpa => hK pa (List.mem_cons_of_mem _ hpa))
        (fun pa hpa => ih pa (List.mem_cons_of_mem _ hpa))

end Loops

section Main

variable (bi : Builtins) (fuel₀ : Nat) (f : String) (ps : List String) (body : ImpExpr)
  (ρ : Env)

/-- **A call of the closure.** From an environment agreeing with `ρ` on the captures,
    every run of a call of `f` with pure arguments under the closure table that does not
    end in an error is the run of the body instantiated at the rewritten arguments. -/
theorem call_ref (hbody : isPure body = true) (args : List ImpExpr)
    (hpure : ∀ a, a ∈ args → isPure a = true) (hlen : args.length = ps.length)
    (ih : ∀ a, a ∈ args → ∀ fuel, RefO (Agree (captures ps body) ρ)
      (denote' bi fuel (inlineCalls f ps body a))
      (denote' (closureTable bi fuel₀ f ps body ρ) fuel a))
    (fuel : Nat) :
    RefO (Agree (captures ps body) ρ)
      (denote' bi fuel (subst ps (args.map (inlineCalls f ps body)) body))
      (denote' (closureTable bi fuel₀ f ps body ρ) fuel (.app f args)) := by
  intro σ hA o s hsrc hnb
  rw [ContinueFlag.app_run] at hsrc
  have hpa := pureArgs_run (closureTable bi fuel₀ f ps body ρ) args
    (fun a ha => pure_run _ a (hpure a ha)) fuel fuel σ
  generalize hr : ((denoteArgs' (closureTable bi fuel₀ f ps body ρ) fuel args).run σ).1 = r
    at hpa
  rw [hpa] at hsrc
  rcases r with _ | vals
  · exact absurd ⟨_, (congrArg Prod.fst hsrc).symm⟩ hnb
  · obtain ⟨-, hvlen, hz⟩ := pureArgs_vals _ fuel σ args vals σ hpure hpa
    have hvl : vals.length = ps.length := hvlen.trans hlen
    dsimp only at hsrc
    simp only [closureTable, if_true, hvl] at hsrc
    have htgt := subst_run bi ps (args.map (inlineCalls f ps body)) fuel fuel₀ σ
      (bindAll ρ ps vals) body hbody (fun x _ => by
        refine argFor_run bi fuel fuel₀ σ ρ x ps _ vals ?_ (by simp [hlen]) hvl ?_
        · intro av hav
          rw [List.zip_map_left, List.mem_map] at hav
          obtain ⟨⟨a, v⟩, hmem, rfl⟩ := hav
          have hsa := hz (a, v) hmem
          exact (ih a (List.of_mem_zip hmem).1 fuel σ hA _ _ hsa
            (by rintro ⟨m, hm⟩; cases hm)).1
        · intro hxp
          apply hA
          simp only [captures, List.mem_filter]
          exact ⟨by assumption, by simpa using hxp⟩)
    simp only [SubstRun] at htgt
    generalize hb : ((denote' bi fuel₀ body).run (bindAll ρ ps vals)).1 = ob at hsrc htgt
    rcases ob with w | _ | _ | _ | _
    · simp only at hsrc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hsrc
      exact ⟨htgt, hA⟩
    all_goals exact absurd ⟨_, (congrArg Prod.fst hsrc).symm⟩ hnb

theorem noBind.noBindList_eq (K : List String) (es : List ImpExpr) :
    noBind.noBindList K es = es.all (noBind K) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [noBind.noBindList, ih]

theorem noBind.noBindArms_eq (K : List String) (arms : List (ImpPat × ImpExpr)) :
    noBind.noBindArms K arms =
      arms.all fun pa => (patVars pa.1).all (fun x => !K.contains x) && noBind K pa.2 := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [noBind.noBindArms, ih]

theorem callsOk.callsOkList_eq (g : String) (es : List ImpExpr) :
    callsOk.callsOkList g es = es.all (callsOk g) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [callsOk.callsOkList, ih]

theorem callsOk.callsOkArms_eq (g : String) (arms : List (ImpPat × ImpExpr)) :
    callsOk.callsOkArms g arms = arms.all fun pa => callsOk g pa.2 := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [callsOk.callsOkArms, ih]

/-- A call of `f` whose argument count differs from the parameter count errs under the
    closure table. -/
theorem call_arity_err (args : List ImpExpr) (hpure : ∀ a, a ∈ args → isPure a = true)
    (hlen : args.length ≠ ps.length) (fuel : Nat) (env : Env) :
    IsErr ((denote' (closureTable bi fuel₀ f ps body ρ) fuel (.app f args)).run env).1 := by
  rw [ContinueFlag.app_run]
  have hpa := pureArgs_run (closureTable bi fuel₀ f ps body ρ) args
    (fun a ha => pure_run _ a (hpure a ha)) fuel fuel env
  generalize hr : ((denoteArgs' (closureTable bi fuel₀ f ps body ρ) fuel args).run env).1 = r
    at hpa
  rw [hpa]
  rcases r with _ | vals
  · exact ⟨_, rfl⟩
  · obtain ⟨-, hvlen, -⟩ := pureArgs_vals _ fuel env args vals env hpure hpa
    have : vals.length ≠ ps.length := hvlen ▸ hlen
    simp only [closureTable, if_true, this, if_false]
    exact ⟨_, rfl⟩

/-- **Inlining the calls of a closure.** For a pure body, a continuation `e` whose calls
    of `f` pass pure arguments and which binds no captured variable, `inlineCalls f ps
    body e` read with `bi` refines `e` read with the closure table of `f` defined in `ρ`,
    from every environment agreeing with `ρ` on the captures. -/
theorem denote'_inlineCalls (hbody : isPure body = true) (e : ImpExpr) :
    noBind (captures ps body) e = true → callsOk f e = true → ∀ fuel,
      RefO (Agree (captures ps body) ρ) (denote' bi fuel (inlineCalls f ps body e))
        (denote' (closureTable bi fuel₀ f ps body ρ) fuel e) := by
  induction e using ImpExpr.ind with
  | app g args ih =>
    intro hK hc fuel
    simp only [noBind, noBind.noBindList_eq, List.all_eq_true] at hK
    simp only [callsOk, callsOk.callsOkList_eq, Bool.and_eq_true, Bool.or_eq_true,
      bne_iff_ne, ne_eq, allPure_eq, List.all_eq_true] at hc
    have ih' := fun a ha => ih a ha (hK a ha) (hc.2 a ha)
    by_cases hgf : g = f
    · subst hgf
      have hp : ∀ a, a ∈ args → isPure a = true := hc.1.resolve_left (by simp)
      by_cases hl : args.length = ps.length
      · simp only [inlineCalls, hl, and_self, if_true, inlineCalls.mapExpr_eq]
        exact call_ref bi fuel₀ g ps body ρ hbody args hp hl ih' fuel
      · exact Ref.of_bad (call_arity_err bi fuel₀ g ps body ρ args hp hl fuel)
    · simp only [inlineCalls, hgf, false_and, if_false, inlineCalls.mapExpr_eq, denote']
      unfold denoteApp'
      refine Ref.bind (badα := fun o => o = none) (args_ref _ args ih' fuel)
        (fun r hr => ?_) (fun r hr s => by subst hr; exact ⟨_, rfl⟩)
      simp only [closureTable, hgf, if_false]
      split <;> (try split) <;> first | exact Ref.pure _ | exact absurd rfl hr
  | tuple es ih =>
    intro hK hc fuel
    simp only [noBind, noBind.noBindList_eq, List.all_eq_true] at hK
    simp only [callsOk, callsOk.callsOkList_eq, List.all_eq_true] at hc
    have ih' := fun a ha => ih a ha (hK a ha) (hc a ha)
    simp only [inlineCalls, inlineCalls.mapExpr_eq, denote']
    refine Ref.bind (badα := fun o => o = none) (args_ref _ es ih' fuel)
      (fun r hr => ?_) (fun r hr s => by subst hr; exact ⟨_, rfl⟩)
    split <;> first | exact Ref.pure _ | exact absurd rfl hr
  | match_ scrut arms ihs iha =>
    intro hK hc fuel
    simp only [noBind, noBind.noBindArms_eq, Bool.and_eq_true, List.all_eq_true,
      Bool.not_eq_true'] at hK
    simp only [callsOk, callsOk.callsOkArms_eq, Bool.and_eq_true, List.all_eq_true] at hc
    have hs := ihs hK.1 hc.1
    have ha := arms_ref (bi₁ := bi) (bi₂ := closureTable bi fuel₀ f ps body ρ)
      (inlineCalls f ps body) arms
      (fun pa hpa x hx => by
        have := (hK.2 pa hpa).1 x hx
        simpa using this)
      (fun pa hpa => iha pa hpa (hK.2 pa hpa).2 (hc.2 pa hpa))
    simp only [inlineCalls, inlineCalls.mapArms_eq, denote']
    ref_step
  | lam qs b ihb =>
    intro _ _ fuel
    exact Ref.of_bad fun _ => by simp only [denote']; exact ⟨_, rfl⟩
  | forLoop v lo hi b ihl ihh ihb =>
    intro hK hc fuel
    simp only [noBind, callsOk, Bool.and_eq_true, Bool.not_eq_true'] at hK hc
    have hl := ihl hK.1.1.2 hc.1.1
    have hh := ihh hK.1.2 hc.1.2
    have := forLoopOrig'_ref (bi₁ := bi) (by simpa using hK.1.1.1) (ihb hK.2 hc.2)
    simp only [inlineCalls, denote']
    ref_step
  | forLoopRev v lo hi b ihl ihh ihb =>
    intro hK hc fuel
    simp only [noBind, callsOk, Bool.and_eq_true, Bool.not_eq_true'] at hK hc
    have hl := ihl hK.1.1.2 hc.1.1
    have hh := ihh hK.1.2 hc.1.2
    have := forLoopRevOrig'_ref (bi₁ := bi) (by simpa using hK.1.1.1) (ihb hK.2 hc.2)
    simp only [inlineCalls, denote']
    ref_step
  | forFold v lo hi b ihl ihh ihb =>
    intro hK hc fuel
    simp only [noBind, callsOk, Bool.and_eq_true, Bool.not_eq_true'] at hK hc
    have hl := ihl hK.1.1.2 hc.1.1
    have hh := ihh hK.1.2 hc.1.2
    have := forLoop'_ref (bi₁ := bi) (by simpa using hK.1.1.1) (ihb hK.2 hc.2)
    simp only [inlineCalls, denote']
    ref_step
  | forFoldRev v lo hi b ihl ihh ihb =>
    intro hK hc fuel
    simp only [noBind, callsOk, Bool.and_eq_true, Bool.not_eq_true'] at hK hc
    have hl := ihl hK.1.1.2 hc.1.1
    have hh := ihh hK.1.2 hc.1.2
    have := forLoopRev'_ref (bi₁ := bi) (by simpa using hK.1.1.1) (ihb hK.2 hc.2)
    simp only [inlineCalls, denote']
    ref_step
  | forFoldReturn v lo hi b ihl ihh ihb =>
    intro hK hc fuel
    simp only [noBind, callsOk, Bool.and_eq_true, Bool.not_eq_true'] at hK hc
    have hl := ihl hK.1.1.2 hc.1.1
    have hh := ihh hK.1.2 hc.1.2
    have := forLoop'Return_ref (bi₁ := bi) (by simpa using hK.1.1.1) (ihb hK.2 hc.2)
    simp only [inlineCalls, denote']
    ref_step
  | forFoldRevReturn v lo hi b ihl ihh ihb =>
    intro hK hc fuel
    simp only [noBind, callsOk, Bool.and_eq_true, Bool.not_eq_true'] at hK hc
    have hl := ihl hK.1.1.2 hc.1.1
    have hh := ihh hK.1.2 hc.1.2
    have := forLoopRev'Return_ref (bi₁ := bi) (by simpa using hK.1.1.1) (ihb hK.2 hc.2)
    simp only [inlineCalls, denote']
    ref_step
  | whileLoop c b ihc ihb =>
    intro hK hc fuel
    simp only [noBind, callsOk, Bool.and_eq_true] at hK hc
    simp only [inlineCalls, denote']
    exact whileOrig'_ref (ihc hK.1 hc.1) (ihb hK.2 hc.2) fuel
  | whileFold c b ihc ihb =>
    intro hK hc fuel
    simp only [noBind, callsOk, Bool.and_eq_true] at hK hc
    simp only [inlineCalls, denote']
    exact while'_ref (ihc hK.1 hc.1) (ihb hK.2 hc.2) fuel
  | whileFoldReturn c b ihc ihb =>
    intro hK hc fuel
    simp only [noBind, callsOk, Bool.and_eq_true] at hK hc
    simp only [inlineCalls, denote']
    exact while'Return_ref (ihc hK.1 hc.1) (ihb hK.2 hc.2) fuel
  | letBind n v b ihv ihb =>
    intro hK hc fuel
    simp only [noBind, callsOk, Bool.and_eq_true, Bool.not_eq_true'] at hK hc
    have hn : n ∉ captures ps body := by simpa using hK.1.1
    have hv := ihv hK.1.2 hc.1
    have hb := ihb hK.2 hc.2
    simp only [inlineCalls, denote']
    ref_step
  | assign n rhs ih =>
    intro hK hc fuel
    simp only [noBind, callsOk, Bool.and_eq_true, Bool.not_eq_true'] at hK hc
    have hn : n ∉ captures ps body := by simpa using hK.1
    have hr := ih hK.2 hc
    simp only [inlineCalls, denote']
    ref_step
  | seq a b iha ihb =>
    intro hK hc fuel
    simp only [noBind, callsOk, Bool.and_eq_true] at hK hc
    have ha := iha hK.1 hc.1
    have hb := ihb hK.2 hc.2
    simp only [inlineCalls, denote']
    ref_step
  | ifThenElse c t e ihc iht ihe =>
    intro hK hc fuel
    simp only [noBind, callsOk, Bool.and_eq_true] at hK hc
    have h1 := ihc hK.1.1 hc.1.1
    have h2 := iht hK.1.2 hc.1.2
    have h3 := ihe hK.2 hc.2
    simp only [inlineCalls, denote']
    ref_step
  | proj e _ ih | borrow e ih | deref e ih | break_some e ih | earlyReturn e ih
  | questionMark e ih | cfBreak e ih | cfContinue e ih | cfBreakContinue e ih
  | typeAscription e _ ih =>
    intro hK hc fuel
    simp only [noBind, callsOk] at hK hc
    have h := ih hK hc
    simp only [inlineCalls, denote']
    ref_step
  | _ =>
    intro _ _ fuel
    simp only [inlineCalls, denote']
    ref_step

/-- **The rewritten binding.** For a binding of the fragment, every run of
    `denoteLetClosure` that does not end in an error is the run of the rewritten
    continuation. -/
theorem denote'_inlineLet (cont : ImpExpr) (h : closureOk f ps body cont = true) (fuel : Nat)
    (env : Env) (o : Outcome) (s : Env) (hr : (denoteLetClosure bi fuel f ps body cont).run env = (o, s))
    (ho : ¬ IsErr o) : (denote' bi fuel (inlineCalls f ps body cont)).run env = (o, s) := by
  simp only [closureOk, Bool.and_eq_true] at h
  exact (denote'_inlineCalls bi fuel f ps body env h.1.1 cont h.2 h.1.2 fuel env
    (fun _ _ => rfl) o s hr ho).1

end Main

/-! ## The statement spine -/

theorem Ref.refl_true {α : Type} {bad : α → Prop} (m : StateM Env α) :
    Ref (fun _ => True) bad m m := fun _ _ _ _ h _ => ⟨h, trivial⟩

theorem denote'_letBind_lam_err (bi : Builtins) (fuel : Nat) (f : String) (ps : List String)
    (body cont : ImpExpr) (env : Env) :
    IsErr ((denote' bi fuel (.letBind f (.lam ps body) cont)).run env).1 := by
  rw [ContinueFlag.letBind_run]
  simp only [denote']
  exact ⟨_, rfl⟩

/-- **The spine.** `inlineSpine e` read with `bi` refines the reference reading
    `denoteSpine bi fuel e`: every run of the reference reading that does not end in an
    error is the run of the rewritten body. -/
theorem denote'_inlineSpine (e : ImpExpr) : ∀ (bi : Builtins) (fuel : Nat),
    RefO (fun _ => True) (denote' bi fuel (inlineSpine e)) (denoteSpine bi fuel e) := by
  induction e using ImpExpr.ind with
  | letBind x v cont ihv ihc =>
    intro bi fuel
    clear ihv
    cases v
    case lam ps body =>
      simp only [inlineSpine, denoteSpine]
      split
      · rename_i hok
        intro env _ o s hr ho
        have hr' : (denoteSpine (closureTable bi fuel x ps body env) fuel cont).run env =
            (o, s) := hr
        obtain ⟨h1, -⟩ := ihc (closureTable bi fuel x ps body env) fuel env trivial o s hr' ho
        simp only [closureOk, Bool.and_eq_true] at hok
        exact ⟨(denote'_inlineCalls bi fuel x ps body env hok.1.1 (inlineSpine cont) hok.2
          hok.1.2 fuel env (fun _ _ => rfl) o s h1 ho).1, trivial⟩
      · exact Ref.of_bad (denote'_letBind_lam_err bi fuel x ps body cont)
    all_goals
      simp only [inlineSpine, denoteSpine, denote']
      refine Ref.bind (badα := IsErr) (Ref.refl_true _) (fun o _ => ?_)
        (fun a ha s => by obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨m, rfl⟩)
      rcases o with w | _ | _ | _ | _
      · cases w <;> dsimp only <;>
          first | exact Ref.pure _ | exact Ref.modify _ (fun _ _ => trivial) (fun _ => ihc bi fuel)
      all_goals (dsimp only; exact Ref.pure _)
  | seq a b _ ihb =>
    intro bi fuel
    simp only [inlineSpine, denoteSpine, denote']
    refine Ref.bind (badα := IsErr) (Ref.refl_true _) (fun o _ => ?_)
      (fun a ha s => by obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨m, rfl⟩)
    rcases o with w | _ | _ | _ | _
    · cases w <;> dsimp only <;> first | exact Ref.pure _ | exact ihb bi fuel
    all_goals (dsimp only; exact Ref.pure _)
  | _ =>
    intro bi fuel
    simp only [inlineSpine, denoteSpine]
    exact Ref.refl_true _

end Hax.InlineLocalClosures
