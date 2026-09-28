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

**Statement closures.** A body that binds variables or runs a loop is inlined when
`blockOk f ps body cont` holds: the parameters are distinct; the body is a chain of
`letBind`s over an expression, reading only parameters, captured variables (`blockK`) and
names the chain bound earlier, and binding no parameter (`bodyOk`); every call of `f` in
`cont` has atomic arguments reading no variable the call binds (`blockW`), is not under a
loop or a `match_`, and `cont` binds no captured variable (`contOk`). A call becomes its
call block (`callBlock`): literal arguments bound to their parameters over the body in
which a parameter whose argument is a variable reads that variable. The block leaves the
variables of `blockW` bound, so the refinement relates environments that agree off
`blockW` (`ContRel`, `RefR`).

## Main definitions

* `inlineCalls f ps body`: replace every call of `f` by the body instantiated at the
  arguments.
* `closureOk f ps body cont`: the pure fragment.
* `inlineBlocks f ps body`, `callBlock`: replace every call of `f` by its call block.
* `blockOk f ps body cont`: the statement fragment.
* `inlineSpine`: inline every binding of either fragment on the statement spine.
* `closureTable`, `denoteLetClosure`, `denoteSpine`: the reference reading.
* `Ref`, `RefO`: refinement of runs from environments satisfying an invariant.
* `RefR`: refinement of runs from related environments to related environments.

## Main results

* `denote'_inlineCalls`: `inlineCalls f ps body cont` read with `bi` refines `cont` read
  with `closureTable bi fuel₀ f ps body ρ`, from an environment agreeing with `ρ` on the
  captures.
* `denote'_inlineLet`: the rewritten binding refines `denoteLetClosure`.
* `denote'_frame`: an expression read through a renaming of its reads refines itself
  from environments related so that each read agrees.
* `denote'_inlineBlocks`: `inlineBlocks f ps body cont` read with `bi` refines `cont` read
  with the closure table, from environments related by `ContRel`.
* `denote'_inlineSpine`: from one environment, `inlineSpine e` read with `bi` refines
  `denoteSpine bi fuel e`, the final environments agreeing off `spineW e`.
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

theorem denote'_letBind_lam_err (bi : Builtins) (fuel : Nat) (f : String) (ps : List String)
    (body cont : ImpExpr) (env : Env) :
    IsErr ((denote' bi fuel (.letBind f (.lam ps body) cont)).run env).1 := by
  rw [ContinueFlag.letBind_run]
  simp only [denote']
  exact ⟨_, rfl⟩

/-! ## Relational refinement -/

/-- `tgt` refines `src` from environments related by `Pre`: every run of `src` from the
    right environment whose result is not `bad` is matched by a run of `tgt` from the
    left one with the same result, the final environments related by `Post`. -/
def RefR {α : Type} (Pre Post : Env → Env → Prop) (bad : α → Prop) (tgt src : StateM Env α) :
    Prop :=
  ∀ e₁ e₂, Pre e₁ e₂ → ∀ o s₂, src.run e₂ = (o, s₂) → ¬ bad o →
    ∃ s₁, tgt.run e₁ = (o, s₁) ∧ Post s₁ s₂

/-- `RefR` on outcomes with one relation before and after, an error being the result
    excluded. -/
abbrev RefE (R : Env → Env → Prop) (tgt src : StateM Env Outcome) : Prop :=
  RefR R R IsErr tgt src

section RefR

variable {R : Env → Env → Prop}

theorem RefR.pure {α : Type} {bad : α → Prop} (a : α) : RefR R R bad (pure a) (pure a) := by
  intro e₁ e₂ h o s₂ hr _
  cases hr; exact ⟨e₁, rfl, h⟩

theorem RefR.of_bad {α : Type} {P Q : Env → Env → Prop} {bad : α → Prop}
    {tgt src : StateM Env α} (h : ∀ env, bad (src.run env).1) : RefR P Q bad tgt src := by
  intro _ e₂ _ o s₂ hr hb
  have := h e₂
  rw [hr] at this
  exact absurd this hb

theorem RefR.bind {α β : Type} {P Q S : Env → Env → Prop} {badα : α → Prop}
    {badβ : β → Prop} {m₁ m₂ : StateM Env α} {k₁ k₂ : α → StateM Env β}
    (hm : RefR P Q badα m₁ m₂) (hk : ∀ a, ¬ badα a → RefR Q S badβ (k₁ a) (k₂ a))
    (hb : ∀ a, badα a → ∀ s, badβ ((k₂ a).run s).1) :
    RefR P S badβ (m₁ >>= k₁) (m₂ >>= k₂) := by
  intro e₁ e₂ hP o s₂ h hnb
  rw [run_bind] at h
  by_cases ha : badα (m₂.run e₂).1
  · exact absurd (by have := hb _ ha (m₂.run e₂).2; rw [h] at this; exact this) hnb
  · obtain ⟨s₁, h₁, hQ⟩ := hm e₁ e₂ hP _ _ rfl ha
    obtain ⟨s₁', h₂, hS⟩ := hk _ ha _ _ hQ o s₂ h hnb
    exact ⟨s₁', by rw [run_bind, h₁]; exact h₂, hS⟩

theorem RefR.modify_ext {α : Type} {bad : α → Prop} {n : String} {w : Value}
    (hn : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend n w) (e₂.extend n w))
    {k₁ k₂ : PUnit → StateM Env α} (h : ∀ u, RefR R R bad (k₁ u) (k₂ u)) :
    RefR R R bad (_root_.modify (fun x => x.extend n w) >>= k₁)
      (_root_.modify (fun x => x.extend n w) >>= k₂) := by
  intro e₁ e₂ hR o s hr hb
  exact h _ _ _ (hn e₁ e₂ w hR) o s hr hb

theorem RefR.mono {α : Type} {P P' Q Q' : Env → Env → Prop} {bad : α → Prop}
    {tgt src : StateM Env α} (h : RefR P Q bad tgt src) (hP : ∀ a b, P' a b → P a b)
    (hQ : ∀ a b, Q a b → Q' a b) : RefR P' Q' bad tgt src := by
  intro e₁ e₂ hp o s₂ hr hb
  obtain ⟨s₁, h1, hq⟩ := h e₁ e₂ (hP _ _ hp) o s₂ hr hb
  exact ⟨s₁, h1, hQ _ _ hq⟩

end RefR

/-- One step of a `RefR` proof between two runs of the same shape: identical pure steps,
    a hypothesis, an environment update that keeps the relation, or a bind of two related
    runs followed by a case split on the outcome. -/
scoped syntax "rel_step" : tactic

macro_rules
  | `(tactic| rel_step) => `(tactic| first
      | exact RefR.pure _
      | (apply RefR.of_bad; intro _; exact ⟨_, rfl⟩)
      | solve_by_elim (maxDepth := 2)
      | (refine RefR.modify_ext (by assumption) (fun _ => ?_); rel_step)
      | (refine RefR.bind (badα := IsErr) (by solve_by_elim (maxDepth := 2)) (fun o ho => ?_)
            (fun a ha s => by
              obtain ⟨m, hm⟩ := ha; subst hm
              first
                | exact ⟨m, rfl⟩
                | (split <;> first | exact ⟨_, rfl⟩ | (exfalso; simp_all) | simp_all [IsErr]))
         split <;> first | rel_step | (exfalso; simp_all [IsErr]))
      | (split <;> rel_step))

section RelLoops

variable {R : Env → Env → Prop} {bi₁ bi₂ : Builtins}

theorem forLoop'_rel {v : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v w) (e₂.extend v w))
    (h : ∀ fuel, RefE R (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel lo hi, RefE R (denoteForLoop' bi₁ fuel v lo hi b₁)
      (denoteForLoop' bi₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero => intro lo hi; unfold denoteForLoop'; by_cases hl : lo ≥ hi <;> simp [hl] <;> rel_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoop'
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; rel_step
    · simp only [hl, if_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      rel_step

theorem forLoopRev'_rel {v : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v w) (e₂.extend v w))
    (h : ∀ fuel, RefE R (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel lo hi, RefE R (denoteForLoopRev' bi₁ fuel v lo hi b₁)
      (denoteForLoopRev' bi₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopRev'; by_cases hl : lo ≥ hi <;> simp [hl] <;> rel_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoopRev'
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; rel_step
    · simp only [hl, if_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      rel_step

theorem forLoopOrig'_rel {v : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v w) (e₂.extend v w))
    (h : ∀ fuel, RefE R (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel lo hi, RefE R (denoteForLoopOrig' bi₁ fuel v lo hi b₁)
      (denoteForLoopOrig' bi₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopOrig'; by_cases hl : lo ≥ hi <;> simp [hl] <;> rel_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoopOrig'
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; rel_step
    · simp only [hl, if_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      rel_step

theorem forLoopRevOrig'_rel {v : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v w) (e₂.extend v w))
    (h : ∀ fuel, RefE R (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel lo hi, RefE R (denoteForLoopRevOrig' bi₁ fuel v lo hi b₁)
      (denoteForLoopRevOrig' bi₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopRevOrig'
    by_cases hl : lo ≥ hi <;> simp [hl] <;> rel_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoopRevOrig'
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; rel_step
    · simp only [hl, if_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      rel_step

theorem forLoop'Return_rel {v : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v w) (e₂.extend v w))
    (h : ∀ fuel, RefE R (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel lo hi, RefE R (denoteForLoop'Return bi₁ fuel v lo hi b₁)
      (denoteForLoop'Return bi₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoop'Return
    by_cases hl : lo ≥ hi <;> simp [hl] <;> rel_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoop'Return
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; rel_step
    · simp only [hl, if_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      rel_step

theorem forLoopRev'Return_rel {v : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v w) (e₂.extend v w))
    (h : ∀ fuel, RefE R (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel lo hi, RefE R (denoteForLoopRev'Return bi₁ fuel v lo hi b₁)
      (denoteForLoopRev'Return bi₂ fuel v lo hi b₂) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi; unfold denoteForLoopRev'Return
    by_cases hl : lo ≥ hi <;> simp [hl] <;> rel_step
  | succ n ih =>
    intro lo hi; unfold denoteForLoopRev'Return
    by_cases hl : lo ≥ hi
    · simp only [hl, if_true]; rel_step
    · simp only [hl, if_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      rel_step

theorem while'_rel {c₁ c₂ b₁ b₂ : ImpExpr}
    (hc : ∀ fuel, RefE R (denote' bi₁ fuel c₁) (denote' bi₂ fuel c₂))
    (h : ∀ fuel, RefE R (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel, RefE R (denoteWhile' bi₁ fuel c₁ b₁) (denoteWhile' bi₂ fuel c₂ b₂) := by
  intro fuel
  induction fuel with
  | zero => unfold denoteWhile'; simp only [if_true]; rel_step
  | succ n ih =>
    unfold denoteWhile'
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rel_step

theorem whileOrig'_rel {c₁ c₂ b₁ b₂ : ImpExpr}
    (hc : ∀ fuel, RefE R (denote' bi₁ fuel c₁) (denote' bi₂ fuel c₂))
    (h : ∀ fuel, RefE R (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel, RefE R (denoteWhileOrig' bi₁ fuel c₁ b₁) (denoteWhileOrig' bi₂ fuel c₂ b₂) := by
  intro fuel
  induction fuel with
  | zero => unfold denoteWhileOrig'; simp only [if_true]; rel_step
  | succ n ih =>
    unfold denoteWhileOrig'
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rel_step

theorem while'Return_rel {c₁ c₂ b₁ b₂ : ImpExpr}
    (hc : ∀ fuel, RefE R (denote' bi₁ fuel c₁) (denote' bi₂ fuel c₂))
    (h : ∀ fuel, RefE R (denote' bi₁ fuel b₁) (denote' bi₂ fuel b₂)) :
    ∀ fuel, RefE R (denoteWhile'Return bi₁ fuel c₁ b₁) (denoteWhile'Return bi₂ fuel c₂ b₂) := by
  intro fuel
  induction fuel with
  | zero => unfold denoteWhile'Return; simp only [if_true]; rel_step
  | succ n ih =>
    unfold denoteWhile'Return
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rel_step

theorem args_rel (g : ImpExpr → ImpExpr) (args : List ImpExpr) (fuel : Nat)
    (ih : ∀ a, a ∈ args → RefE R (denote' bi₁ fuel (g a)) (denote' bi₂ fuel a)) :
    RefR R R (fun o => o = none) (denoteArgs' bi₁ fuel (args.map g))
      (denoteArgs' bi₂ fuel args) := by
  induction args with
  | nil => simp only [List.map_nil, denoteArgs']; exact RefR.pure _
  | cons a as iha =>
    simp only [List.map_cons, denoteArgs']
    refine RefR.bind (badα := IsErr) (ih a List.mem_cons_self) (fun o ho => ?_)
      (fun o ho s => by obtain ⟨m, hm⟩ := ho; subst hm; rfl)
    split
    · exact RefR.pure _
    · exact RefR.bind (badα := fun o => o = none)
        (iha fun b hb => ih b (List.mem_cons_of_mem a hb))
        (fun _ _ => RefR.pure _) (fun r hr s => by subst hr; rfl)
    · exact RefR.pure _

end RelLoops

/-! ## The frame of an expression -/

/-- Replace every variable read `var x` by `var (σ x)`; binders are kept. -/
def renameReads (σ : String → String) : ImpExpr → ImpExpr
  | .lit v => .lit v
  | .var n => .var (σ n)
  | .unitVal => .unitVal
  | .continue_ => .continue_
  | .break_ none => .break_ none
  | .break_ (some e) => .break_ (some (renameReads σ e))
  | .lam qs b => .lam qs (renameReads σ b)
  | .app g args => .app g (mapE σ args)
  | .letBind n v b => .letBind n (renameReads σ v) (renameReads σ b)
  | .seq a b => .seq (renameReads σ a) (renameReads σ b)
  | .ifThenElse c t e =>
    .ifThenElse (renameReads σ c) (renameReads σ t) (renameReads σ e)
  | .tuple es => .tuple (mapE σ es)
  | .proj e i => .proj (renameReads σ e) i
  | .match_ scrut arms => .match_ (renameReads σ scrut) (mapA σ arms)
  | .borrow e => .borrow (renameReads σ e)
  | .deref e => .deref (renameReads σ e)
  | .assign n rhs => .assign n (renameReads σ rhs)
  | .forLoop v lo hi b =>
    .forLoop v (renameReads σ lo) (renameReads σ hi) (renameReads σ b)
  | .forLoopRev v lo hi b =>
    .forLoopRev v (renameReads σ lo) (renameReads σ hi) (renameReads σ b)
  | .whileLoop c b => .whileLoop (renameReads σ c) (renameReads σ b)
  | .earlyReturn e => .earlyReturn (renameReads σ e)
  | .questionMark e => .questionMark (renameReads σ e)
  | .forFold v lo hi b =>
    .forFold v (renameReads σ lo) (renameReads σ hi) (renameReads σ b)
  | .forFoldRev v lo hi b =>
    .forFoldRev v (renameReads σ lo) (renameReads σ hi) (renameReads σ b)
  | .whileFold c b => .whileFold (renameReads σ c) (renameReads σ b)
  | .forFoldReturn v lo hi b =>
    .forFoldReturn v (renameReads σ lo) (renameReads σ hi) (renameReads σ b)
  | .forFoldRevReturn v lo hi b =>
    .forFoldRevReturn v (renameReads σ lo) (renameReads σ hi) (renameReads σ b)
  | .whileFoldReturn c b => .whileFoldReturn (renameReads σ c) (renameReads σ b)
  | .cfBreak e => .cfBreak (renameReads σ e)
  | .cfContinue e => .cfContinue (renameReads σ e)
  | .cfBreakContinue e => .cfBreakContinue (renameReads σ e)
  | .typeAscription e ty => .typeAscription (renameReads σ e) ty
where
  /-- `renameReads` on every expression of a list. -/
  mapE (σ : String → String) : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => renameReads σ e :: mapE σ es
  /-- `renameReads` on the body of every match arm. -/
  mapA (σ : String → String) : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, renameReads σ e) :: mapA σ rest

@[simp] theorem renameReads.mapE_eq (σ : String → String) (es : List ImpExpr) :
    renameReads.mapE σ es = es.map (renameReads σ) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [renameReads.mapE, ih]

/-- Every variable `e` reads satisfies `rd`, every name it binds (`letBind`, `assign`,
    loop counter) satisfies `bd`, every name it calls satisfies `ok`, and `e` contains
    no `match_`. -/
def frameOk (rd bd ok : String → Bool) : ImpExpr → Bool
  | .var x => rd x
  | .letBind n v b => bd n && frameOk rd bd ok v && frameOk rd bd ok b
  | .assign n rhs => bd n && frameOk rd bd ok rhs
  | .lam _ b => frameOk rd bd ok b
  | .app g args => ok g && okList rd bd ok args
  | .tuple es => okList rd bd ok es
  | .proj e _ => frameOk rd bd ok e
  | .ifThenElse c t e => frameOk rd bd ok c && frameOk rd bd ok t && frameOk rd bd ok e
  | .match_ _ _ => false
  | .seq a b => frameOk rd bd ok a && frameOk rd bd ok b
  | .borrow e => frameOk rd bd ok e
  | .deref e => frameOk rd bd ok e
  | .forLoop v lo hi b =>
    bd v && frameOk rd bd ok lo && frameOk rd bd ok hi && frameOk rd bd ok b
  | .forLoopRev v lo hi b =>
    bd v && frameOk rd bd ok lo && frameOk rd bd ok hi && frameOk rd bd ok b
  | .whileLoop c b => frameOk rd bd ok c && frameOk rd bd ok b
  | .break_ (some e) => frameOk rd bd ok e
  | .earlyReturn e => frameOk rd bd ok e
  | .questionMark e => frameOk rd bd ok e
  | .forFold v lo hi b =>
    bd v && frameOk rd bd ok lo && frameOk rd bd ok hi && frameOk rd bd ok b
  | .forFoldRev v lo hi b =>
    bd v && frameOk rd bd ok lo && frameOk rd bd ok hi && frameOk rd bd ok b
  | .whileFold c b => frameOk rd bd ok c && frameOk rd bd ok b
  | .forFoldReturn v lo hi b =>
    bd v && frameOk rd bd ok lo && frameOk rd bd ok hi && frameOk rd bd ok b
  | .forFoldRevReturn v lo hi b =>
    bd v && frameOk rd bd ok lo && frameOk rd bd ok hi && frameOk rd bd ok b
  | .whileFoldReturn c b => frameOk rd bd ok c && frameOk rd bd ok b
  | .cfBreak e => frameOk rd bd ok e
  | .cfContinue e => frameOk rd bd ok e
  | .cfBreakContinue e => frameOk rd bd ok e
  | .typeAscription e _ => frameOk rd bd ok e
  | _ => true
where
  /-- `frameOk` of every expression of a list. -/
  okList (rd bd ok : String → Bool) : List ImpExpr → Bool
    | [] => true
    | e :: es => frameOk rd bd ok e && okList rd bd ok es

theorem frameOk.okList_eq (rd bd ok : String → Bool) (es : List ImpExpr) :
    frameOk.okList rd bd ok es = es.all (frameOk rd bd ok) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [frameOk.okList, ih]

section Frame

variable {R : Env → Env → Prop} {bi₁ bi₂ : Builtins} (σ : String → String)
  (rd bd ok : String → Bool)

/-- **The frame of an expression.** Let `R` relate environments so that a variable `x`
    with `rd x` reads in the right environment what `σ x` reads in the left one, and so
    that extending both at a name with `bd` by one value keeps `R`; let `bi₁` and `bi₂`
    agree on the names with `ok`. For `e` in `frameOk rd bd ok`, `renameReads σ e` read
    with `bi₁` refines `e` read with `bi₂` from `R`-related environments. -/
theorem denote'_frame
    (hrd : ∀ e₁ e₂ x, R e₁ e₂ → rd x = true → e₁ (σ x) = e₂ x)
    (hbd : ∀ e₁ e₂ n w, R e₁ e₂ → bd n = true → R (e₁.extend n w) (e₂.extend n w))
    (hok : ∀ g, ok g = true → bi₁ g = bi₂ g) (e : ImpExpr) :
    frameOk rd bd ok e = true → ∀ fuel,
      RefE R (denote' bi₁ fuel (renameReads σ e)) (denote' bi₂ fuel e) := by
  have ext : ∀ n, bd n = true → ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend n w) (e₂.extend n w) :=
    fun n hn e₁ e₂ w h => hbd e₁ e₂ n w h hn
  induction e using ImpExpr.ind with
  | var x =>
    intro hK fuel e₁ e₂ hR o s₂ hr hnb
    simp only [frameOk] at hK
    simp only [renameReads]
    rw [ContinueFlag.var_run] at hr ⊢
    rw [hrd e₁ e₂ x hR hK]
    cases h : e₂ x <;> simp only [h] at hr <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
    · exact absurd ⟨_, rfl⟩ hnb
    · exact ⟨e₁, rfl, hR⟩
  | app g args ih =>
    intro hK fuel
    simp only [frameOk, frameOk.okList_eq, Bool.and_eq_true, List.all_eq_true] at hK
    have ih' := fun a ha => ih a ha (hK.2 a ha)
    simp only [renameReads, renameReads.mapE_eq, denote']
    unfold denoteApp'
    refine RefR.bind (badα := fun o => o = none) (args_rel _ args fuel fun a ha => ih' a ha fuel)
      (fun r hr => ?_) (fun r hr s => by subst hr; exact ⟨_, rfl⟩)
    rw [hok g hK.1]
    split <;> (try split) <;> first | exact RefR.pure _ | exact absurd rfl hr
  | tuple es ih =>
    intro hK fuel
    simp only [frameOk, frameOk.okList_eq, List.all_eq_true] at hK
    have ih' := fun a ha => ih a ha (hK a ha)
    simp only [renameReads, renameReads.mapE_eq, denote']
    refine RefR.bind (badα := fun o => o = none) (args_rel _ es fuel fun a ha => ih' a ha fuel)
      (fun r hr => ?_) (fun r hr s => by subst hr; exact ⟨_, rfl⟩)
    split <;> first | exact RefR.pure _ | exact absurd rfl hr
  | match_ scrut arms _ _ => intro hK; simp [frameOk] at hK
  | lam qs b _ =>
    intro _ fuel
    exact RefR.of_bad fun _ => by simp only [denote']; exact ⟨_, rfl⟩
  | forLoop v lo hi b ihl ihh ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hl := ihl hK.1.1.2
    have hh := ihh hK.1.2
    have := forLoopOrig'_rel (bi₁ := bi₁) (ext v hK.1.1.1) (ihb hK.2)
    simp only [renameReads, denote']
    rel_step
  | forLoopRev v lo hi b ihl ihh ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hl := ihl hK.1.1.2
    have hh := ihh hK.1.2
    have := forLoopRevOrig'_rel (bi₁ := bi₁) (ext v hK.1.1.1) (ihb hK.2)
    simp only [renameReads, denote']
    rel_step
  | forFold v lo hi b ihl ihh ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hl := ihl hK.1.1.2
    have hh := ihh hK.1.2
    have := forLoop'_rel (bi₁ := bi₁) (ext v hK.1.1.1) (ihb hK.2)
    simp only [renameReads, denote']
    rel_step
  | forFoldRev v lo hi b ihl ihh ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hl := ihl hK.1.1.2
    have hh := ihh hK.1.2
    have := forLoopRev'_rel (bi₁ := bi₁) (ext v hK.1.1.1) (ihb hK.2)
    simp only [renameReads, denote']
    rel_step
  | forFoldReturn v lo hi b ihl ihh ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hl := ihl hK.1.1.2
    have hh := ihh hK.1.2
    have := forLoop'Return_rel (bi₁ := bi₁) (ext v hK.1.1.1) (ihb hK.2)
    simp only [renameReads, denote']
    rel_step
  | forFoldRevReturn v lo hi b ihl ihh ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hl := ihl hK.1.1.2
    have hh := ihh hK.1.2
    have := forLoopRev'Return_rel (bi₁ := bi₁) (ext v hK.1.1.1) (ihb hK.2)
    simp only [renameReads, denote']
    rel_step
  | whileLoop c b ihc ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    simp only [renameReads, denote']
    exact whileOrig'_rel (ihc hK.1) (ihb hK.2) fuel
  | whileFold c b ihc ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    simp only [renameReads, denote']
    exact while'_rel (ihc hK.1) (ihb hK.2) fuel
  | whileFoldReturn c b ihc ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    simp only [renameReads, denote']
    exact while'Return_rel (ihc hK.1) (ihb hK.2) fuel
  | letBind n v b ihv ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hn := ext n hK.1.1
    have hv := ihv hK.1.2
    have hb := ihb hK.2
    simp only [renameReads, denote']
    rel_step
  | assign n rhs ih =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hn := ext n hK.1
    have hr := ih hK.2
    simp only [renameReads, denote']
    rel_step
  | seq a b iha ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have ha := iha hK.1
    have hb := ihb hK.2
    simp only [renameReads, denote']
    rel_step
  | ifThenElse c t e ihc iht ihe =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have h1 := ihc hK.1.1
    have h2 := iht hK.1.2
    have h3 := ihe hK.2
    simp only [renameReads, denote']
    rel_step
  | proj e _ ih | borrow e ih | deref e ih | break_some e ih | earlyReturn e ih
  | questionMark e ih | cfBreak e ih | cfContinue e ih | cfBreakContinue e ih
  | typeAscription e _ ih =>
    intro hK fuel
    simp only [frameOk] at hK
    have h := ih hK
    simp only [renameReads, denote']
    rel_step
  | _ =>
    intro _ fuel
    simp only [renameReads, denote']
    rel_step

end Frame

theorem renameReads_id (e : ImpExpr) (h : frameOk (fun _ => true) (fun _ => true) (fun _ => true) e = true) :
    renameReads id e = e := by
  induction e using ImpExpr.ind with
  | app g args ih =>
    simp only [frameOk, frameOk.okList_eq, List.all_eq_true, Bool.true_and] at h
    simp only [renameReads, renameReads.mapE_eq, ImpExpr.app.injEq, true_and]
    exact (List.map_congr_left fun a ha => ih a ha (h a ha)).trans (by simp)
  | tuple es ih =>
    simp only [frameOk, frameOk.okList_eq, List.all_eq_true] at h
    simp only [renameReads, renameReads.mapE_eq, ImpExpr.tuple.injEq]
    exact (List.map_congr_left fun a ha => ih a ha (h a ha)).trans (by simp)
  | match_ => simp [frameOk] at h
  | _ => simp_all [frameOk, renameReads]

theorem frameOk_mono {rd bd ok rd' bd' ok' : String → Bool} (hrd : ∀ x, rd x = true → rd' x = true)
    (hbd : ∀ x, bd x = true → bd' x = true) (hok : ∀ x, ok x = true → ok' x = true)
    (e : ImpExpr) : frameOk rd bd ok e = true → frameOk rd' bd' ok' e = true := by
  induction e using ImpExpr.ind with
  | app g args ih =>
    simp only [frameOk, frameOk.okList_eq, List.all_eq_true, Bool.and_eq_true]
    exact fun h => ⟨hok _ h.1, fun a ha => ih a ha (h.2 a ha)⟩
  | tuple es ih =>
    simp only [frameOk, frameOk.okList_eq, List.all_eq_true]
    exact fun h a ha => ih a ha (h a ha)
  | match_ => simp [frameOk]
  | _ => simp_all [frameOk]

/-! ## Closures with statement bodies

A closure body that binds variables or runs a loop is inlined at a call as a block: the
parameters whose argument is a literal are bound by `letBind`, and every read of a
parameter whose argument is a variable reads that variable (`callBlock`). The block
binds the parameters and the variables the body binds, the set `blockW ps body`; the
calls are in argument position, where `denote'` threads the environment, so these
bindings survive the call. The refinement therefore relates environments that agree off
that set (`ContRel`). -/

/-- The variables an expression binds: `letBind` and `assign` names and loop counters. -/
def bindVars : ImpExpr → List String
  | .letBind n v b => n :: (bindVars v ++ bindVars b)
  | .assign n rhs => n :: bindVars rhs
  | .lam _ b => bindVars b
  | .app _ args => listVars args
  | .tuple es => listVars es
  | .proj e _ => bindVars e
  | .ifThenElse c t e => bindVars c ++ bindVars t ++ bindVars e
  | .seq a b => bindVars a ++ bindVars b
  | .borrow e => bindVars e
  | .deref e => bindVars e
  | .forLoop v lo hi b => v :: (bindVars lo ++ bindVars hi ++ bindVars b)
  | .forLoopRev v lo hi b => v :: (bindVars lo ++ bindVars hi ++ bindVars b)
  | .whileLoop c b => bindVars c ++ bindVars b
  | .break_ (some e) => bindVars e
  | .earlyReturn e => bindVars e
  | .questionMark e => bindVars e
  | .forFold v lo hi b => v :: (bindVars lo ++ bindVars hi ++ bindVars b)
  | .forFoldRev v lo hi b => v :: (bindVars lo ++ bindVars hi ++ bindVars b)
  | .whileFold c b => bindVars c ++ bindVars b
  | .forFoldReturn v lo hi b => v :: (bindVars lo ++ bindVars hi ++ bindVars b)
  | .forFoldRevReturn v lo hi b => v :: (bindVars lo ++ bindVars hi ++ bindVars b)
  | .whileFoldReturn c b => bindVars c ++ bindVars b
  | .cfBreak e => bindVars e
  | .cfContinue e => bindVars e
  | .cfBreakContinue e => bindVars e
  | .typeAscription e _ => bindVars e
  | _ => []
where
  /-- `bindVars` of every expression of a list, concatenated. -/
  listVars : List ImpExpr → List String
    | [] => []
    | e :: es => bindVars e ++ listVars es

/-- The variables an expression reads: every `var` occurrence. -/
def readVars : ImpExpr → List String
  | .var x => [x]
  | .letBind _ v b => readVars v ++ readVars b
  | .assign _ rhs => readVars rhs
  | .lam _ b => readVars b
  | .app _ args => listVars args
  | .tuple es => listVars es
  | .proj e _ => readVars e
  | .ifThenElse c t e => readVars c ++ readVars t ++ readVars e
  | .seq a b => readVars a ++ readVars b
  | .borrow e => readVars e
  | .deref e => readVars e
  | .forLoop _ lo hi b => readVars lo ++ readVars hi ++ readVars b
  | .forLoopRev _ lo hi b => readVars lo ++ readVars hi ++ readVars b
  | .whileLoop c b => readVars c ++ readVars b
  | .break_ (some e) => readVars e
  | .earlyReturn e => readVars e
  | .questionMark e => readVars e
  | .forFold _ lo hi b => readVars lo ++ readVars hi ++ readVars b
  | .forFoldRev _ lo hi b => readVars lo ++ readVars hi ++ readVars b
  | .whileFold c b => readVars c ++ readVars b
  | .forFoldReturn _ lo hi b => readVars lo ++ readVars hi ++ readVars b
  | .forFoldRevReturn _ lo hi b => readVars lo ++ readVars hi ++ readVars b
  | .whileFoldReturn c b => readVars c ++ readVars b
  | .cfBreak e => readVars e
  | .cfContinue e => readVars e
  | .cfBreakContinue e => readVars e
  | .typeAscription e _ => readVars e
  | _ => []
where
  /-- `readVars` of every expression of a list, concatenated. -/
  listVars : List ImpExpr → List String
    | [] => []
    | e :: es => readVars e ++ listVars es

/-- The variables a call of the closure binds: the parameters and the variables the body
    binds. -/
def blockW (ps : List String) (body : ImpExpr) : List String := ps ++ bindVars body

/-- The variables a statement body captures: those it reads outside `blockW`. -/
def blockK (ps : List String) (body : ImpExpr) : List String :=
  (readVars body).filter fun x => !(blockW ps body).contains x

/-- A name the body may bind: one of `W` that is not a parameter. -/
def bodyBd (W ps : List String) (n : String) : Bool := W.contains n && !ps.contains n

/-- The body of a statement closure: a chain of `letBind`s whose right-hand sides, and
    the expression ending the chain, read only the variables of `D` extended by the names
    bound earlier in the chain, bind only names of `bodyBd W ps`, and contain no
    `match_`. -/
def bodyOk (W ps : List String) : List String → ImpExpr → Bool
  | D, .letBind n v b =>
    frameOk D.contains (bodyBd W ps) (fun _ => true) v && bodyBd W ps n &&
      bodyOk W ps (n :: D) b
  | D, e => frameOk D.contains (bodyBd W ps) (fun _ => true) e

/-- The relation along a run of the body: a variable of `D` reads in the right
    environment what its renaming reads in the left one, and the left one agrees with
    `E` off `W`. -/
def BodyRel (σ : String → String) (W D : List String) (E : Env) (e₁ e₂ : Env) : Prop :=
  (∀ x, D.contains x = true → e₁ (σ x) = e₂ x) ∧ (∀ x, W.contains x = false → e₁ x = E x)

section Body

variable {σ : String → String} {W ps : List String} {E : Env}

theorem BodyRel.extend_cons (hσ : ∀ x, σ x = x ∨ W.contains (σ x) = false)
    (hσps : ∀ x, ps.contains x = false → σ x = x) {D : List String} {e₁ e₂ : Env}
    (h : BodyRel σ W D E e₁ e₂) {n : String} (hn : bodyBd W ps n = true) (w : Value) :
    BodyRel σ W (n :: D) E (e₁.extend n w) (e₂.extend n w) := by
  simp only [bodyBd, Bool.and_eq_true, Bool.not_eq_true'] at hn
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · by_cases hxn : x = n
    · subst hxn
      rw [hσps x hn.2, Env.extend_same, Env.extend_same]
    · have hD : D.contains x = true := by simpa [hxn] using hx
      have hσn : σ x ≠ n := by
        rcases hσ x with h' | h'
        · rw [h']; exact hxn
        · intro he; rw [he, hn.1] at h'; cases h'
      rw [Env.extend_other _ _ _ _ hσn, Env.extend_other _ _ _ _ hxn]
      exact h.1 x hD
  · have hxn : x ≠ n := by rintro rfl; rw [hn.1] at hx; cases hx
    rw [Env.extend_other _ _ _ _ hxn]
    exact h.2 x hx

theorem BodyRel.of_cons {D : List String} {n : String} {e₁ e₂ : Env}
    (h : BodyRel σ W (n :: D) E e₁ e₂) : BodyRel σ W D E e₁ e₂ :=
  ⟨fun x hx => h.1 x (by simp only [List.contains_cons, hx, Bool.or_true]), h.2⟩

theorem RefR.pure_mono {α : Type} {P Q : Env → Env → Prop} {bad : α → Prop} (a : α)
    (h : ∀ e₁ e₂, P e₁ e₂ → Q e₁ e₂) : RefR P Q bad (Pure.pure a) (Pure.pure a) := by
  intro e₁ e₂ hp o s₂ hr _
  cases hr; exact ⟨e₁, rfl, h _ _ hp⟩

theorem RefR.modify_mono {α : Type} {P Q S : Env → Env → Prop} {bad : α → Prop}
    {g₁ g₂ : Env → Env} (hg : ∀ e₁ e₂, P e₁ e₂ → Q (g₁ e₁) (g₂ e₂))
    {k₁ k₂ : PUnit → StateM Env α} (h : ∀ u, RefR Q S bad (k₁ u) (k₂ u)) :
    RefR P S bad (_root_.modify g₁ >>= k₁) (_root_.modify g₂ >>= k₂) := by
  intro e₁ e₂ hp o s hr hb
  exact h _ _ _ (hg e₁ e₂ hp) o s hr hb

/-- **A run of the body.** For a body in `bodyOk W ps D`, the renamed body read with
    `bi` refines the body read with `bi` from environments related by `BodyRel`, and the
    left run ends in an environment agreeing with `E` off `W`. -/
theorem denote'_body (bi : Builtins) (hσ : ∀ x, σ x = x ∨ W.contains (σ x) = false)
    (hσps : ∀ x, ps.contains x = false → σ x = x) (body : ImpExpr) :
    ∀ D, bodyOk W ps D body = true → ∀ fuel,
      RefR (BodyRel σ W D E) (fun s₁ _ => ∀ x, W.contains x = false → s₁ x = E x) IsErr
        (denote' bi fuel (renameReads σ body)) (denote' bi fuel body) := by
  have frame : ∀ D e, frameOk D.contains (bodyBd W ps) (fun _ => true) e = true → ∀ fuel,
      RefR (BodyRel σ W D E) (fun s₁ _ => ∀ x, W.contains x = false → s₁ x = E x) IsErr
        (denote' bi fuel (renameReads σ e)) (denote' bi fuel e) := fun D e h fuel =>
    (denote'_frame (bi₁ := bi) (bi₂ := bi) σ D.contains (bodyBd W ps) (fun _ => true)
      (fun _ _ x hR hx => hR.1 x hx)
      (fun _ _ n w hR hn => (hR.extend_cons hσ hσps hn w).of_cons)
      (fun _ _ => rfl) e h fuel).mono (fun _ _ h => h) (fun _ _ h => h.2)
  intro D h fuel
  induction body using ImpExpr.ind generalizing D with
  | letBind n v b _ ihb =>
    simp only [bodyOk, Bool.and_eq_true] at h
    have hv : RefE (BodyRel σ W D E) (denote' bi fuel (renameReads σ v)) (denote' bi fuel v) :=
      denote'_frame σ D.contains (bodyBd W ps) (fun _ => true)
        (fun _ _ x hR hx => hR.1 x hx)
        (fun _ _ n w hR hn => (hR.extend_cons hσ hσps hn w).of_cons)
        (fun _ _ => rfl) v h.1.1 fuel
    simp only [renameReads, denote']
    refine RefR.bind (badα := IsErr) hv (fun o ho => ?_)
      (fun a ha s => by obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨m, rfl⟩)
    split
    · exact RefR.pure_mono _ fun _ _ (hR : BodyRel σ W D E _ _) => hR.2
    · exact RefR.modify_mono (fun _ _ hR => hR.extend_cons hσ hσps h.1.2 _)
        (fun _ => ihb (n :: D) h.2)
    · exact RefR.pure_mono _ fun _ _ (hR : BodyRel σ W D E _ _) => hR.2
  | _ => exact frame D _ (by simpa only [bodyOk] using h) fuel

end Body

/-! ### The call block -/

/-- A variable or a literal. -/
def isAtom : ImpExpr → Bool
  | .var _ => true
  | .lit _ => true
  | _ => false

/-- The renaming of a call: a parameter whose argument is the variable `y` reads `y`;
    every other name is kept. -/
def argRen (ps : List String) (args : List ImpExpr) (x : String) : String :=
  match argFor ps args x with
  | some (.var y) => y
  | _ => x

/-- Bind every parameter whose argument is a literal to it, in parameter order, over
    `b`. -/
def bindArgs : List String → List ImpExpr → ImpExpr → ImpExpr
  | p :: ps, a :: as, b =>
    match a with
    | .lit l => .letBind p (.lit l) (bindArgs ps as b)
    | _ => bindArgs ps as b
  | _, _, b => b

/-- The environment `e` extended as `bindArgs` extends it. -/
def bindLits : List String → List ImpExpr → Env → Env
  | p :: ps, a :: as, e =>
    match a with
    | .lit l => bindLits ps as (e.extend p (Value.ofLit l))
    | _ => bindLits ps as e
  | _, _, e => e

/-- The block that replaces a call of a statement closure on atomic arguments: the
    literal arguments bound to their parameters, over the body with every parameter
    whose argument is a variable read as that variable. -/
def callBlock (ps : List String) (args : List ImpExpr) (body : ImpExpr) : ImpExpr :=
  bindArgs ps args (renameReads (argRen ps args) body)

/-- The value an atom reads in `e`. -/
def atomVal (e : Env) : ImpExpr → Option Value
  | .var y => e y
  | .lit l => some (Value.ofLit l)
  | _ => none

theorem bindLits_other (x : String) :
    ∀ (ps : List String) (args : List ImpExpr) (e : Env), x ∉ ps → bindLits ps args e x = e x
  | [], _, _, _ => by simp only [bindLits]
  | _ :: _, [], _, _ => by simp only [bindLits]
  | p :: ps, a :: as, e, hx => by
    have hxp : x ≠ p := fun h => hx (h ▸ List.mem_cons_self)
    have hx' : x ∉ ps := fun h => hx (List.mem_cons_of_mem p h)
    cases a
    case lit l =>
      simp only [bindLits]
      rw [bindLits_other x ps as _ hx', Env.extend_other _ _ _ _ hxp]
    all_goals (simp only [bindLits]; exact bindLits_other x ps as e hx')

theorem bindArgs_run (bi : Builtins) (fuel : Nat) (b : ImpExpr) :
    ∀ (ps : List String) (args : List ImpExpr) (e : Env),
      (denote' bi fuel (bindArgs ps args b)).run e = (denote' bi fuel b).run (bindLits ps args e)
  | [], _, _ => by simp only [bindArgs, bindLits]
  | _ :: _, [], _ => by simp only [bindArgs, bindLits]
  | p :: ps, a :: as, e => by
    cases a
    case lit l =>
      simp only [bindArgs, bindLits]
      rw [ContinueFlag.letBind_run, ContinueFlag.lit_run]
      cases l <;> exact bindArgs_run bi fuel b ps as _
    all_goals (simp only [bindArgs, bindLits]; exact bindArgs_run bi fuel b ps as e)

theorem argFor_none (x : String) :
    ∀ (ps : List String) (args : List ImpExpr), x ∉ ps → argFor ps args x = none
  | [], _, _ => by simp only [argFor]
  | _ :: _, [], _ => by simp only [argFor]
  | p :: ps, a :: as, hx => by
    have hxp : x ≠ p := fun h => hx (h ▸ List.mem_cons_self)
    simp only [argFor, hxp, if_false]
    exact argFor_none x ps as (fun h => hx (List.mem_cons_of_mem p h))

theorem argFor_mem (x : String) :
    ∀ (ps : List String) (args : List ImpExpr) (a : ImpExpr), argFor ps args x = some a →
      a ∈ args
  | [], _, _, h => by simp [argFor] at h
  | _ :: _, [], _, h => by simp [argFor] at h
  | p :: ps, b :: bs, a, h => by
    simp only [argFor] at h
    split at h
    · cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem b (argFor_mem x ps bs a h)

theorem atomVal_extend {a : ImpExpr} (ha : isAtom a = true) {p : String}
    (hp : ∀ y, a = .var y → y ≠ p) (e : Env) (w : Value) :
    atomVal (e.extend p w) a = atomVal e a := by
  cases a <;> simp_all [isAtom, atomVal, Env.extend_other]

/-- At a parameter, the environment `bindLits ps args e` read through the renaming of the
    call holds the value `bindAll` binds, when every argument is an atom that reads its
    value in `e` and no variable argument is a parameter. -/
theorem bindLits_param (ρ : Env) :
    ∀ (ps : List String) (args : List ImpExpr) (vals : List Value) (e : Env),
      ps.Nodup → args.length = ps.length → vals.length = ps.length →
      (∀ a, a ∈ args → isAtom a = true) → (∀ y, ImpExpr.var y ∈ args → y ∉ ps) →
      (∀ av, av ∈ args.zip vals → atomVal e av.1 = some av.2) →
      ∀ x, x ∈ ps → bindLits ps args e (argRen ps args x) = bindAll ρ ps vals x
  | [], _, _, _, _, _, _, _, _, _, x, hx => by simp at hx
  | _ :: _, [], _, _, _, hl, _, _, _, _, _, _ => by simp at hl
  | _ :: _, _ :: _, [], _, _, _, hl, _, _, _, _, _ => by simp at hl
  | p :: ps, a :: as, v :: vs, e, hnd, hl, hl', hat, hy, hz, x, hx => by
    obtain ⟨hpn, hnd'⟩ := List.nodup_cons.mp hnd
    have hza : atomVal e a = some v := hz (a, v) (by simp)
    have hat' : ∀ b, b ∈ as → isAtom b = true := fun b hb => hat b (List.mem_cons_of_mem a hb)
    have hy' : ∀ y, ImpExpr.var y ∈ as → y ∉ ps := fun y hy'' h =>
      hy y (List.mem_cons_of_mem a hy'') (List.mem_cons_of_mem p h)
    have hyp : ∀ y, ImpExpr.var y ∈ as → y ≠ p := fun y hy'' h =>
      hy y (List.mem_cons_of_mem a hy'') (h ▸ List.mem_cons_self)
    have hzs : ∀ w, ∀ av, av ∈ as.zip vs → atomVal (e.extend p w) av.1 = some av.2 := by
      intro w av hav
      have hmem := (List.of_mem_zip hav).1
      rw [atomVal_extend (hat' _ hmem) (fun y hy'' => hyp y (hy'' ▸ hmem)) e w]
      exact hz av (by simp [hav])
    have hzs' : ∀ av, av ∈ as.zip vs → atomVal e av.1 = some av.2 := fun av hav =>
      hz av (by simp [hav])
    by_cases hxp : x = p
    · subst hxp
      simp only [bindAll, Env.extend_same]
      have ha := hat a List.mem_cons_self
      cases a with
      | var y =>
        simp only [argRen, argFor, if_true, bindLits]
        have hyps : y ∉ ps := fun h => hy y List.mem_cons_self (List.mem_cons_of_mem x h)
        rw [bindLits_other y ps as e hyps]
        exact hza
      | lit l =>
        simp only [argRen, argFor, if_true, bindLits]
        rw [bindLits_other x ps as _ hpn, Env.extend_same]
        simpa [atomVal] using hza
      | _ => simp [isAtom] at ha
    · have hx' : x ∈ ps := by simpa [hxp] using hx
      simp only [bindAll, Env.extend_other _ _ _ _ hxp]
      have hren : argRen (p :: ps) (a :: as) x = argRen ps as x := by
        simp only [argRen, argFor, hxp, if_false]
      rw [hren]
      cases a
      case lit l =>
        simp only [bindLits]
        exact bindLits_param ρ ps as vs _ hnd' (by simpa using hl) (by simpa using hl') hat' hy'
          (hzs _) x hx'
      all_goals
        simp only [bindLits]
        exact bindLits_param ρ ps as vs e hnd' (by simpa using hl) (by simpa using hl') hat' hy'
          hzs' x hx'

/-! ### The rewriting and the fragment -/

/-- Replace every call `.app f args` with as many arguments as parameters by
    `callBlock ps args body`; every other node is kept. -/
def inlineBlocks (f : String) (ps : List String) (body : ImpExpr) : ImpExpr → ImpExpr
  | .lit v => .lit v
  | .var n => .var n
  | .unitVal => .unitVal
  | .continue_ => .continue_
  | .break_ none => .break_ none
  | .break_ (some e) => .break_ (some (inlineBlocks f ps body e))
  | .lam qs b => .lam qs (inlineBlocks f ps body b)
  | .app g args =>
    if g = f ∧ args.length = ps.length then callBlock ps args body
    else .app g (mapExpr f ps body args)
  | .letBind n v b => .letBind n (inlineBlocks f ps body v) (inlineBlocks f ps body b)
  | .seq a b => .seq (inlineBlocks f ps body a) (inlineBlocks f ps body b)
  | .ifThenElse c t e =>
    .ifThenElse (inlineBlocks f ps body c) (inlineBlocks f ps body t) (inlineBlocks f ps body e)
  | .tuple es => .tuple (mapExpr f ps body es)
  | .proj e i => .proj (inlineBlocks f ps body e) i
  | .match_ scrut arms => .match_ (inlineBlocks f ps body scrut) (mapArms f ps body arms)
  | .borrow e => .borrow (inlineBlocks f ps body e)
  | .deref e => .deref (inlineBlocks f ps body e)
  | .assign n rhs => .assign n (inlineBlocks f ps body rhs)
  | .forLoop v lo hi b =>
    .forLoop v (inlineBlocks f ps body lo) (inlineBlocks f ps body hi) (inlineBlocks f ps body b)
  | .forLoopRev v lo hi b =>
    .forLoopRev v (inlineBlocks f ps body lo) (inlineBlocks f ps body hi)
      (inlineBlocks f ps body b)
  | .whileLoop c b => .whileLoop (inlineBlocks f ps body c) (inlineBlocks f ps body b)
  | .earlyReturn e => .earlyReturn (inlineBlocks f ps body e)
  | .questionMark e => .questionMark (inlineBlocks f ps body e)
  | .forFold v lo hi b =>
    .forFold v (inlineBlocks f ps body lo) (inlineBlocks f ps body hi) (inlineBlocks f ps body b)
  | .forFoldRev v lo hi b =>
    .forFoldRev v (inlineBlocks f ps body lo) (inlineBlocks f ps body hi)
      (inlineBlocks f ps body b)
  | .whileFold c b => .whileFold (inlineBlocks f ps body c) (inlineBlocks f ps body b)
  | .forFoldReturn v lo hi b =>
    .forFoldReturn v (inlineBlocks f ps body lo) (inlineBlocks f ps body hi)
      (inlineBlocks f ps body b)
  | .forFoldRevReturn v lo hi b =>
    .forFoldRevReturn v (inlineBlocks f ps body lo) (inlineBlocks f ps body hi)
      (inlineBlocks f ps body b)
  | .whileFoldReturn c b =>
    .whileFoldReturn (inlineBlocks f ps body c) (inlineBlocks f ps body b)
  | .cfBreak e => .cfBreak (inlineBlocks f ps body e)
  | .cfContinue e => .cfContinue (inlineBlocks f ps body e)
  | .cfBreakContinue e => .cfBreakContinue (inlineBlocks f ps body e)
  | .typeAscription e ty => .typeAscription (inlineBlocks f ps body e) ty
where
  /-- `inlineBlocks` on every expression of a list. -/
  mapExpr (f : String) (ps : List String) (body : ImpExpr) : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => inlineBlocks f ps body e :: mapExpr f ps body es
  /-- `inlineBlocks` on the body of every match arm. -/
  mapArms (f : String) (ps : List String) (body : ImpExpr) :
      List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, inlineBlocks f ps body e) :: mapArms f ps body rest

@[simp] theorem inlineBlocks.mapExpr_eq (f : String) (ps : List String) (body : ImpExpr)
    (es : List ImpExpr) :
    inlineBlocks.mapExpr f ps body es = es.map (inlineBlocks f ps body) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [inlineBlocks.mapExpr, ih]

/-- No call of `f` in `e`, and no `match_`. -/
def callFree (f : String) (e : ImpExpr) : Bool :=
  frameOk (fun _ => true) (fun _ => true) (fun g => g != f) e

theorem inlineBlocks_free (f : String) (ps : List String) (body e : ImpExpr)
    (h : callFree f e = true) : inlineBlocks f ps body e = e := by
  simp only [callFree] at h
  induction e using ImpExpr.ind with
  | app g args ih =>
    simp only [frameOk, frameOk.okList_eq, List.all_eq_true, Bool.and_eq_true, bne_iff_ne,
      ne_eq] at h
    simp only [inlineBlocks, h.1, false_and, if_false, inlineBlocks.mapExpr_eq,
      ImpExpr.app.injEq, true_and]
    exact (List.map_congr_left fun a ha => ih a ha (h.2 a ha)).trans (by simp)
  | tuple es ih =>
    simp only [frameOk, frameOk.okList_eq, List.all_eq_true] at h
    simp only [inlineBlocks, inlineBlocks.mapExpr_eq, ImpExpr.tuple.injEq]
    exact (List.map_congr_left fun a ha => ih a ha (h a ha)).trans (by simp)
  | match_ => simp [frameOk] at h
  | _ => simp_all [frameOk, inlineBlocks]

/-- The continuation of a statement closure `f`: every subexpression is either in
    `frameOk rd bd` with no call of `f`, or is a call of `f` on atoms that read only `rd`
    variables, or is a `letBind`, `assign`, `seq`, `ifThenElse`, call, tuple,
    projection or single-operand node binding only `bd` names whose operands are in the
    fragment. A call of `f` under a loop or a `match_` is outside the fragment. -/
def contOk (f : String) (rd bd : String → Bool) : ImpExpr → Bool
  | .app g args => frameOk rd bd (fun g => g != f) (.app g args) ||
    (if g = f then args.all fun a => isAtom a && frameOk rd bd (fun _ => true) a
     else contOkList f rd bd args)
  | .letBind n v b => frameOk rd bd (fun g => g != f) (.letBind n v b) ||
    (bd n && contOk f rd bd v && contOk f rd bd b)
  | .assign n rhs => frameOk rd bd (fun g => g != f) (.assign n rhs) ||
    (bd n && contOk f rd bd rhs)
  | .seq a b => frameOk rd bd (fun g => g != f) (.seq a b) ||
    (contOk f rd bd a && contOk f rd bd b)
  | .ifThenElse c t e => frameOk rd bd (fun g => g != f) (.ifThenElse c t e) ||
    (contOk f rd bd c && contOk f rd bd t && contOk f rd bd e)
  | .tuple es => frameOk rd bd (fun g => g != f) (.tuple es) || contOkList f rd bd es
  | .proj e i => frameOk rd bd (fun g => g != f) (.proj e i) || contOk f rd bd e
  | .borrow e => frameOk rd bd (fun g => g != f) (.borrow e) || contOk f rd bd e
  | .deref e => frameOk rd bd (fun g => g != f) (.deref e) || contOk f rd bd e
  | .break_ (some e) => frameOk rd bd (fun g => g != f) (.break_ (some e)) || contOk f rd bd e
  | .earlyReturn e => frameOk rd bd (fun g => g != f) (.earlyReturn e) || contOk f rd bd e
  | .questionMark e => frameOk rd bd (fun g => g != f) (.questionMark e) || contOk f rd bd e
  | .cfBreak e => frameOk rd bd (fun g => g != f) (.cfBreak e) || contOk f rd bd e
  | .cfContinue e => frameOk rd bd (fun g => g != f) (.cfContinue e) || contOk f rd bd e
  | .cfBreakContinue e =>
    frameOk rd bd (fun g => g != f) (.cfBreakContinue e) || contOk f rd bd e
  | .typeAscription e ty =>
    frameOk rd bd (fun g => g != f) (.typeAscription e ty) || contOk f rd bd e
  | e => frameOk rd bd (fun g => g != f) e
where
  /-- `contOk` of every expression of a list. -/
  contOkList (f : String) (rd bd : String → Bool) : List ImpExpr → Bool
    | [] => true
    | e :: es => contOk f rd bd e && contOkList f rd bd es

theorem contOk.contOkList_eq (f : String) (rd bd : String → Bool) (es : List ImpExpr) :
    contOk.contOkList f rd bd es = es.all (contOk f rd bd) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [contOk.contOkList, ih]

/-- The relation along the continuation: the left environment agrees with the right one
    off `W`, and the right one agrees with `ρ` on `K`. -/
def ContRel (W K : List String) (ρ : Env) (e₁ e₂ : Env) : Prop :=
  (∀ x, W.contains x = false → e₁ x = e₂ x) ∧ Agree K ρ e₂

theorem bindAll_other (ρ : Env) (x : String) :
    ∀ (ps : List String) (vals : List Value), x ∉ ps → bindAll ρ ps vals x = ρ x
  | [], _, _ => by simp only [bindAll]
  | _ :: _, [], _ => by simp only [bindAll]
  | p :: ps, v :: vs, hx => by
    have hxp : x ≠ p := fun h => hx (h ▸ List.mem_cons_self)
    simp only [bindAll, Env.extend_other _ _ _ _ hxp]
    exact bindAll_other ρ x ps vs (fun h => hx (List.mem_cons_of_mem p h))

section Blocks

variable (bi : Builtins) (fuel₀ : Nat) (f : String) (ps : List String) (body : ImpExpr)
  (ρ : Env) {W K : List String}

/-- **A call of a statement closure.** From environments related by `ContRel`, every run
    of a call of `f` on atoms reading no variable of `W` under the closure table that does
    not end in an error is matched by the run of the call block, the final environments
    related by `ContRel`. -/
theorem callBlock_rel (hW : ∀ p, p ∈ ps → W.contains p = true)
    (hKW : ∀ x, x ∈ K → W.contains x = false) (hnd : ps.Nodup)
    (hbody : bodyOk W ps (ps ++ K) body = true) (args : List ImpExpr)
    (hat : ∀ a, a ∈ args → isAtom a = true ∧
      frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun _ => true) a = true) :
    RefE (ContRel W K ρ) (denote' bi fuel₀ (inlineBlocks f ps body (.app f args)))
      (denote' (closureTable bi fuel₀ f ps body ρ) fuel₀ (.app f args)) := by
  have hpure : ∀ a, a ∈ args → isPure a = true := fun a ha => by
    have := (hat a ha).1
    cases a <;> simp_all [isAtom, isPure]
  by_cases hl : args.length = ps.length
  case neg =>
    simp only [inlineBlocks, hl, and_false, if_false]
    exact RefR.of_bad (call_arity_err bi fuel₀ f ps body ρ args hpure hl fuel₀)
  simp only [inlineBlocks, hl, and_self, if_true, callBlock]
  intro e₁ e₂ hR o s₂ hsrc hnb
  rw [ContinueFlag.app_run] at hsrc
  have hpa := pureArgs_run (closureTable bi fuel₀ f ps body ρ) args
    (fun a ha => pure_run _ a (hpure a ha)) fuel₀ fuel₀ e₂
  generalize hr : ((denoteArgs' (closureTable bi fuel₀ f ps body ρ) fuel₀ args).run e₂).1 = r
    at hpa
  rw [hpa] at hsrc
  rcases r with _ | vals
  · exact absurd ⟨_, (congrArg Prod.fst hsrc).symm⟩ hnb
  obtain ⟨-, hvlen, hz⟩ := pureArgs_vals _ fuel₀ e₂ args vals e₂ hpure hpa
  have hvl : vals.length = ps.length := hvlen.trans hl
  dsimp only at hsrc
  simp only [closureTable, if_true, hvl] at hsrc
  have hy : ∀ y, ImpExpr.var y ∈ args → W.contains y = false := fun y hy' => by
    simpa [frameOk] using (hat _ hy').2
  have hzv : ∀ av, av ∈ args.zip vals → atomVal e₁ av.1 = some av.2 := by
    intro av hav
    have hmem := (List.of_mem_zip hav).1
    have hrun := hz av hav
    have ha := (hat _ hmem).1
    obtain ⟨a, v⟩ := av
    cases a with
    | var y =>
      rw [ContinueFlag.var_run] at hrun
      simp only [atomVal]
      rw [hR.1 y (hy y hmem)]
      cases h : e₂ y with
      | none => simp only [h] at hrun; cases (Prod.mk.inj hrun).1
      | some u =>
        simp only [h] at hrun
        cases (Prod.mk.inj hrun).1
        rfl
    | lit l =>
      rw [ContinueFlag.lit_run] at hrun
      cases (Prod.mk.inj hrun).1
      rfl
    | _ => simp [isAtom] at ha
  have hσps : ∀ x, ps.contains x = false → argRen ps args x = x := fun x hx => by
    simp only [argRen, argFor_none x ps args (by simpa using hx)]
  have hσ : ∀ x, argRen ps args x = x ∨ W.contains (argRen ps args x) = false := by
    intro x
    simp only [argRen]
    split
    · rename_i y hy'
      exact Or.inr (hy y (argFor_mem x ps args _ hy'))
    · exact Or.inl rfl
  have hpre : BodyRel (argRen ps args) W (ps ++ K) e₁ (bindLits ps args e₁) (bindAll ρ ps vals) := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp only [List.contains_append, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · exact bindLits_param ρ ps args vals e₁ hnd hl hvl (fun a ha => (hat a ha).1)
          (fun y hy' hyp => by have := hW y hyp; rw [hy y hy'] at this; cases this) hzv x
          (by simpa using hx)
      · have hxK : x ∈ K := by simpa using hx
        have hxW := hKW x hxK
        have hxps : x ∉ ps := fun h => by rw [hW x h] at hxW; cases hxW
        rw [hσps x (by simpa using hxps), bindLits_other x ps args e₁ hxps, hR.1 x hxW,
          hR.2 x hxK, bindAll_other ρ x ps vals hxps]
    · have hxps : x ∉ ps := fun h => by rw [hW x h] at hx; cases hx
      exact bindLits_other x ps args e₁ hxps
  generalize hb : (denote' bi fuel₀ body).run (bindAll ρ ps vals) = rb at hsrc
  obtain ⟨ob, sb⟩ := rb
  rcases ob with w | _ | _ | _ | _
  · simp only at hsrc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hsrc
    obtain ⟨s₁, h1, h2⟩ := denote'_body (E := e₁) bi hσ hσps body (ps ++ K) hbody fuel₀ _ _ hpre
      (.val w) sb hb (by rintro ⟨m, hm⟩; cases hm)
    refine ⟨s₁, ?_, fun x hx => (h2 x hx).trans (hR.1 x hx), hR.2⟩
    rw [bindArgs_run]
    exact h1
  all_goals (simp only at hsrc; exact absurd ⟨_, (congrArg Prod.fst hsrc).symm⟩ hnb)

/-- **Inlining a statement closure.** Let `W` contain the parameters, `K` be disjoint from
    `W`, the parameters be distinct and the body be in `bodyOk W ps (ps ++ K)`. For a
    continuation in `contOk`, reading no variable of `W` and binding none of `K`,
    `inlineBlocks f ps body e` read with `bi` refines `e` read with the closure table of
    `f` defined in `ρ`, at the fuel of the table, from environments related by
    `ContRel W K ρ`. -/
theorem denote'_inlineBlocks (hW : ∀ p, p ∈ ps → W.contains p = true)
    (hKW : ∀ x, x ∈ K → W.contains x = false) (hnd : ps.Nodup)
    (hbody : bodyOk W ps (ps ++ K) body = true) (e : ImpExpr) :
    contOk f (fun x => !W.contains x) (fun n => !K.contains n) e = true →
      RefE (ContRel W K ρ) (denote' bi fuel₀ (inlineBlocks f ps body e))
        (denote' (closureTable bi fuel₀ f ps body ρ) fuel₀ e) := by
  have hrd : ∀ e₁ e₂ x, ContRel W K ρ e₁ e₂ → (!W.contains x) = true → e₁ (id x) = e₂ x :=
    fun _ _ x h hx => h.1 x (by simpa using hx)
  have hbd : ∀ e₁ e₂ n w, ContRel W K ρ e₁ e₂ → (!K.contains n) = true →
      ContRel W K ρ (e₁.extend n w) (e₂.extend n w) := by
    intro e₁ e₂ n w h hn
    refine ⟨fun x hx => ?_, Agree.extend h.2 (by simpa using hn) w⟩
    by_cases hxn : x = n
    · subst hxn; simp
    · rw [Env.extend_other _ _ _ _ hxn, Env.extend_other _ _ _ _ hxn]; exact h.1 x hx
  have hok : ∀ g, (g != f) = true → bi g = closureTable bi fuel₀ f ps body ρ g := fun g hg => by
    have hgf : g ≠ f := by simpa using hg
    funext vals; simp [closureTable, hgf]
  have free : ∀ e, frameOk (fun x => !W.contains x) (fun n => !K.contains n)
      (fun g => g != f) e = true →
      RefE (ContRel W K ρ) (denote' bi fuel₀ (inlineBlocks f ps body e))
        (denote' (closureTable bi fuel₀ f ps body ρ) fuel₀ e) := by
    intro e h
    rw [inlineBlocks_free f ps body e
      (frameOk_mono (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h) e h)]
    have := denote'_frame (bi₁ := bi) (bi₂ := closureTable bi fuel₀ f ps body ρ) id _ _ _
      hrd hbd hok e h fuel₀
    rwa [renameReads_id e (frameOk_mono (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) e h)]
      at this
  have ext : ∀ n, (!K.contains n) = true → ∀ e₁ e₂ w, ContRel W K ρ e₁ e₂ →
      ContRel W K ρ (e₁.extend n w) (e₂.extend n w) := fun n hn e₁ e₂ w h => hbd e₁ e₂ n w h hn
  induction e using ImpExpr.ind with
  | app g args ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.app g args)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    by_cases hgf : g = f
    · subst hgf
      simp only [if_true, List.all_eq_true, Bool.and_eq_true] at h
      exact callBlock_rel bi fuel₀ g ps body ρ hW hKW hnd hbody args h
    · simp only [hgf, if_false, contOk.contOkList_eq, List.all_eq_true] at h
      have ih' := fun a ha => ih a ha (h a ha)
      simp only [inlineBlocks, hgf, false_and, if_false, inlineBlocks.mapExpr_eq, denote']
      unfold denoteApp'
      refine RefR.bind (badα := fun o => o = none) (args_rel _ args fuel₀ ih')
        (fun r hr => ?_) (fun r hr s => by subst hr; exact ⟨_, rfl⟩)
      rw [← hok g (by simpa using hgf)]
      split <;> (try split) <;> first | exact RefR.pure _ | exact absurd rfl hr
  | tuple es ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.tuple es)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or, contOk.contOkList_eq, List.all_eq_true] at h
    have ih' := fun a ha => ih a ha (h a ha)
    simp only [inlineBlocks, inlineBlocks.mapExpr_eq, denote']
    refine RefR.bind (badα := fun o => o = none) (args_rel _ es fuel₀ ih')
      (fun r hr => ?_) (fun r hr s => by subst hr; exact ⟨_, rfl⟩)
    split <;> first | exact RefR.pure _ | exact absurd rfl hr
  | letBind n v b ihv ihb =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.letBind n v b)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or, Bool.and_eq_true] at h
    have hn := ext n h.1.1
    have hv := ihv h.1.2
    have hb := ihb h.2
    simp only [inlineBlocks, denote']
    rel_step
  | assign n rhs ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.assign n rhs)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or, Bool.and_eq_true] at h
    have hn := ext n h.1
    have hr := ih h.2
    simp only [inlineBlocks, denote']
    rel_step
  | seq a b iha ihb =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.seq a b)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or, Bool.and_eq_true] at h
    have ha := iha h.1
    have hb := ihb h.2
    simp only [inlineBlocks, denote']
    rel_step
  | ifThenElse c t e ihc iht ihe =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.ifThenElse c t e)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or, Bool.and_eq_true] at h
    have h1 := ihc h.1.1
    have h2 := iht h.1.2
    have h3 := ihe h.2
    simp only [inlineBlocks, denote']
    rel_step
  | proj e i ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.proj e i)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    have h' := ih h
    simp only [inlineBlocks, denote']
    rel_step
  | borrow e ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.borrow e)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    have h' := ih h
    simp only [inlineBlocks, denote']
    rel_step
  | deref e ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.deref e)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    have h' := ih h
    simp only [inlineBlocks, denote']
    rel_step
  | break_some e ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.break_ (some e))
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    have h' := ih h
    simp only [inlineBlocks, denote']
    rel_step
  | earlyReturn e ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.earlyReturn e)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    have h' := ih h
    simp only [inlineBlocks, denote']
    rel_step
  | questionMark e ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.questionMark e)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    have h' := ih h
    simp only [inlineBlocks, denote']
    rel_step
  | cfBreak e ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.cfBreak e)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    have h' := ih h
    simp only [inlineBlocks, denote']
    rel_step
  | cfContinue e ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.cfContinue e)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    have h' := ih h
    simp only [inlineBlocks, denote']
    rel_step
  | cfBreakContinue e ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.cfBreakContinue e)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    have h' := ih h
    simp only [inlineBlocks, denote']
    rel_step
  | typeAscription e ty ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.typeAscription e ty)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    have h' := ih h
    simp only [inlineBlocks, denote']
    rel_step
  | _ => intro h; exact free _ (by simpa only [contOk] using h)

end Blocks

/-- The binding `.letBind f (.lam ps body) cont` is in the statement fragment: distinct
    parameters, a body in `bodyOk` over the parameters and its captures, and a
    continuation in `contOk` reading no variable a call binds and binding no captured
    variable. -/
def blockOk (f : String) (ps : List String) (body cont : ImpExpr) : Bool :=
  decide ps.Nodup && bodyOk (blockW ps body) ps (ps ++ blockK ps body) body &&
    contOk f (fun x => !(blockW ps body).contains x) (fun n => !(blockK ps body).contains n)
      cont

/-! ## The statement spine -/

/-- Inline every binding of either fragment on the statement spine (`letBind` and `seq`)
    of a function body, innermost first: a pure body by `inlineCalls`, a statement body
    by `inlineBlocks`. -/
def inlineSpine : ImpExpr → ImpExpr
  | .letBind f (.lam ps body) cont =>
    if closureOk f ps body (inlineSpine cont) then inlineCalls f ps body (inlineSpine cont)
    else if blockOk f ps body (inlineSpine cont) then
      inlineBlocks f ps body (inlineSpine cont)
    else .letBind f (.lam ps body) (inlineSpine cont)
  | .letBind x v cont => .letBind x v (inlineSpine cont)
  | .seq a b => .seq a (inlineSpine b)
  | e => e

/-- The variables the calls of the statement closures `inlineSpine` inlines bind. -/
def spineW : ImpExpr → List String
  | .letBind f (.lam ps body) cont =>
    if closureOk f ps body (inlineSpine cont) then spineW cont
    else if blockOk f ps body (inlineSpine cont) then blockW ps body ++ spineW cont
    else spineW cont
  | .letBind _ _ cont => spineW cont
  | .seq _ b => spineW b
  | _ => []

/-- The reference reading of a function body: along the statement spine a binding whose
    continuation, with the bindings it contains inlined, is in either fragment is read as
    in `denoteLetClosure`, and every other expression by `denote'`. -/
def denoteSpine (bi : Builtins) (fuel : Nat) : ImpExpr → StateM Env Outcome
  | .letBind f (.lam ps body) cont =>
    if closureOk f ps body (inlineSpine cont) || blockOk f ps body (inlineSpine cont) then do
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

/-- Two environments agree off the variables `U`. -/
def EqOff (U : List String) (e₁ e₂ : Env) : Prop := ∀ x, U.contains x = false → e₁ x = e₂ x

theorem RefR.refl {α : Type} {bad : α → Prop} (m : StateM Env α) :
    RefR (fun e₁ e₂ => e₁ = e₂) (fun e₁ e₂ => e₁ = e₂) bad m m := by
  intro e₁ e₂ h o s hr _
  subst h
  exact ⟨s, hr, rfl⟩

theorem EqOff.of_eq (U : List String) (e₁ e₂ : Env) (h : e₁ = e₂) : EqOff U e₁ e₂ :=
  fun _ _ => h ▸ rfl

/-- **The spine.** From one environment, every run of the reference reading
    `denoteSpine bi fuel e` that does not end in an error is matched by the run of
    `inlineSpine e` read with `bi`, the final environments agreeing off `spineW e`, the
    variables the inlined calls of statement closures bind. -/
theorem denote'_inlineSpine (e : ImpExpr) : ∀ (bi : Builtins) (fuel : Nat),
    RefR (fun e₁ e₂ => e₁ = e₂) (EqOff (spineW e)) IsErr (denote' bi fuel (inlineSpine e))
      (denoteSpine bi fuel e) := by
  induction e using ImpExpr.ind with
  | letBind x v cont ihv ihc =>
    intro bi fuel
    clear ihv
    cases v
    case lam ps body =>
      simp only [inlineSpine, denoteSpine, spineW]
      cases hp : closureOk x ps body (inlineSpine cont)
      case true =>
        simp only [if_true, Bool.true_or]
        intro env _ heq o s hr ho
        subst heq
        have hr' : (denoteSpine (closureTable bi fuel x ps body env) fuel cont).run env =
            (o, s) := hr
        obtain ⟨sm, h1, hQ⟩ := ihc (closureTable bi fuel x ps body env) fuel env env rfl o s hr' ho
        simp only [closureOk, Bool.and_eq_true] at hp
        exact ⟨sm, (denote'_inlineCalls bi fuel x ps body env hp.1.1 (inlineSpine cont) hp.2
          hp.1.2 fuel env (fun _ _ => rfl) o sm h1 ho).1, hQ⟩
      cases hb : blockOk x ps body (inlineSpine cont)
      case false =>
        simp only [Bool.false_or, Bool.false_eq_true, if_false]
        exact RefR.of_bad (denote'_letBind_lam_err bi fuel x ps body cont)
      simp only [Bool.false_or, Bool.false_eq_true, if_false, if_true]
      intro env _ heq o s hr ho
      subst heq
      have hr' : (denoteSpine (closureTable bi fuel x ps body env) fuel cont).run env =
          (o, s) := hr
      obtain ⟨sm, h1, hQ⟩ := ihc (closureTable bi fuel x ps body env) fuel env env rfl o s hr' ho
      simp only [blockOk, Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨s₁, h2, hR⟩ := denote'_inlineBlocks bi fuel x ps body env
        (fun p hp' => by simp [blockW, hp'])
        (fun y hy => by simp only [blockK, List.mem_filter] at hy; simpa using hy.2)
        hb.1.1 hb.1.2 (inlineSpine cont) hb.2 env env ⟨fun _ _ => rfl, fun _ _ => rfl⟩ o sm h1 ho
      refine ⟨s₁, h2, fun y hy => ?_⟩
      simp only [List.contains_append, Bool.or_eq_false_iff] at hy
      exact (hR.1 y hy.1).trans (hQ y hy.2)
    all_goals
      simp only [inlineSpine, denoteSpine, spineW, denote']
      refine RefR.bind (badα := IsErr) (RefR.refl _) (fun o _ => ?_)
        (fun a ha s => by obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨m, rfl⟩)
      rcases o with w | _ | _ | _ | _
      · cases w <;> dsimp only <;>
          first
            | exact RefR.pure_mono _ (EqOff.of_eq _)
            | exact RefR.modify_mono (fun _ _ h => h ▸ rfl) (fun _ => ihc bi fuel)
      all_goals (dsimp only; exact RefR.pure_mono _ (EqOff.of_eq _))
  | seq a b _ ihb =>
    intro bi fuel
    simp only [inlineSpine, denoteSpine, spineW, denote']
    refine RefR.bind (badα := IsErr) (RefR.refl _) (fun o _ => ?_)
      (fun a ha s => by obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨m, rfl⟩)
    rcases o with w | _ | _ | _ | _
    · cases w <;> dsimp only <;>
        first | exact RefR.pure_mono _ (EqOff.of_eq _) | exact ihb bi fuel
    all_goals (dsimp only; exact RefR.pure_mono _ (EqOff.of_eq _))
  | _ =>
    intro bi fuel
    simp only [inlineSpine, denoteSpine, spineW]
    exact (RefR.refl _).mono (fun _ _ h => h) (EqOff.of_eq _)

end Hax.InlineLocalClosures
