/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import HaxLean.Py.Check
public import HaxLean.Secrecy

/-!
# Secrecy of a checked Python function

The secrecy records of the Rust route (`Hax.FnSecrecy`, `Hax.secrecyOfBindings`)
built from the checked types of a Python function.

* `PyTy.isSecretTy` — a secret type: `secret τ`, `secretBool`, an array of a
  secret type, or a tuple with a secret component.
* `pyTySecrecy` — `secret` for a secret type and `pub` otherwise; the `fields`
  form is not produced, since a `Secret[...]` never appears inside a struct.
* `pyFnSecrecy` — the `FnSecrecy` of a function: its parameters, in order, and
  its result. `pyModuleSecrecy` lists the functions of a checked module with a
  secret parameter or result, as `crateSecrecy` does for a crate.
* `walkStmt`, `walkStmts` — the statement walk of `checkStmt`, `checkStmts`,
  which also returns the bindings of loop bodies; `walkStmts_fst` states that
  its context is the checker's.
* `pyBindings` — the parameters and the bindings of the body with their
  checked types; `pySecretBindings` — the names among them of a secret type,
  without repetition.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Py

/-- A secret type: a secret word, a secret Boolean, an array of a secret type,
or a tuple with a component of a secret type. -/
def PyTy.isSecretTy : PyTy → Bool
  | .secret _ => true
  | .secretBool => true
  | .array t _ => t.isSecretTy
  | .tuple ts => isSecretTys ts
  | _ => false
where
  /-- Some type of the list is secret. -/
  isSecretTys : List PyTy → Bool
    | [] => false
    | t :: ts => t.isSecretTy || isSecretTys ts

/-- The secrecy of a binding of type `τ`: `secret` for a secret type, `pub`
otherwise. -/
def pyTySecrecy (τ : PyTy) : BindingSecrecy :=
  if τ.isSecretTy then .secret else .pub

theorem pyTySecrecy_eq_secret_iff (τ : PyTy) : pyTySecrecy τ = .secret ↔ τ.isSecretTy = true := by
  unfold pyTySecrecy; split <;> simp_all

theorem pyTySecrecy_eq_pub_iff (τ : PyTy) : pyTySecrecy τ = .pub ↔ τ.isSecretTy = false := by
  unfold pyTySecrecy; split <;> simp_all

/-- The secrecy record of a checked function: its name, each parameter in order
with the secrecy of its type, and the secrecy of its result type. -/
def pyFnSecrecy (f : CheckedFn) : FnSecrecy where
  fn := f.name
  params := f.sig.params.map fun p => (p.1, pyTySecrecy p.2)
  ret := pyTySecrecy f.sig.result

/-- The records of the functions of a checked module with a parameter or a
result that is not public, in order of definition. -/
def pyModuleSecrecy (cm : CheckedModule) : List FnSecrecy :=
  (cm.fns.map pyFnSecrecy).filter FnSecrecy.hasSecret

/-- Each parameter of `pyFnSecrecy f` is the parameter of `f` with the secrecy of
its type, `secret` exactly when the type is secret and `pub` otherwise; likewise
the result. -/
theorem pyFnSecrecy_param (f : CheckedFn) :
    (pyFnSecrecy f).fn = f.name ∧
    (pyFnSecrecy f).params.map Prod.fst = f.sig.params.map Prod.fst ∧
    (∀ x s, (x, s) ∈ (pyFnSecrecy f).params ↔
      ∃ τ, (x, τ) ∈ f.sig.params ∧
        ((τ.isSecretTy = true ∧ s = .secret) ∨ (τ.isSecretTy = false ∧ s = .pub))) ∧
    ((pyFnSecrecy f).ret = .secret ↔ f.sig.result.isSecretTy = true) ∧
    ((pyFnSecrecy f).ret = .pub ↔ f.sig.result.isSecretTy = false) := by
  refine ⟨rfl, by simp [pyFnSecrecy], ?_, pyTySecrecy_eq_secret_iff _,
    pyTySecrecy_eq_pub_iff _⟩
  intro x s
  simp only [pyFnSecrecy, List.mem_map, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨y, τ, h, rfl, rfl⟩
    refine ⟨τ, h, ?_⟩
    unfold pyTySecrecy; cases τ.isSecretTy <;> simp
  · rintro ⟨τ, h, hs⟩
    refine ⟨x, τ, h, rfl, ?_⟩
    unfold pyTySecrecy
    rcases hs with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> simp [h1]

/-! ## Bindings of a function body -/

mutual

/-- The statement walk of `checkStmt`, returning with the context it leaves the
bindings made in loop bodies, which that context does not keep. -/
def walkStmt (env : ModEnv) (top : Bool) (Γ : Ctx) :
    PyStmt → Except PyRefusal (Ctx × List (String × PyTy))
  | .forStmt p target iter body orelse => do
      let Γ₀ ← liftK p (targetNames [target]) (loopEntry env Γ target iter orelse)
      let r ← walkStmts env true Γ₀ body
      pure (Γ, r.1.vars ++ r.2)
  | .ifStmt p c body orelse => do
      let τ ← inferExpr env Γ c
      liftK p [] (condOk τ)
      let r₁ ← walkStmts env false Γ body
      let r₂ ← walkStmts env false r₁.1 orelse
      pure (r₂.1, r₁.2 ++ r₂.2)
  | s => do
      let Γ' ← checkStmt env top Γ s
      pure (Γ', [])

/-- The statement walk of `checkStmts`, with the bindings made in loop bodies. -/
def walkStmts (env : ModEnv) (top : Bool) (Γ : Ctx) :
    List PyStmt → Except PyRefusal (Ctx × List (String × PyTy))
  | [] => pure (Γ, [])
  | s :: ss => do
      let r₁ ← walkStmt env top Γ s
      let r₂ ← walkStmts env top r₁.1 ss
      pure (r₂.1, r₁.2 ++ r₂.2)

end

mutual

/-- The context of `walkStmt` is the context of `checkStmt`. -/
theorem walkStmt_fst (env : ModEnv) (top : Bool) (Γ : Ctx) (s : PyStmt) :
    (walkStmt env top Γ s).map Prod.fst = checkStmt env top Γ s := by
  cases s with
  | forStmt p target iter body orelse =>
    rw [walkStmt, checkStmt]
    cases liftK p (targetNames [target]) (loopEntry env Γ target iter orelse) with
    | error e => rfl
    | ok Γ₀ =>
      simp only [Except.map, bind, Except.bind, pure, Except.pure]
      rw [← walkStmts_fst env true Γ₀ body]
      cases walkStmts env true Γ₀ body <;> rfl
  | ifStmt p c body orelse =>
    rw [walkStmt, checkStmt]
    cases inferExpr env Γ c with
    | error e => rfl
    | ok τ =>
      simp only [Except.map, bind, Except.bind, pure, Except.pure]
      cases liftK (α := Unit) p [] (condOk τ) with
      | error e => rfl
      | ok u =>
        simp only
        rw [← walkStmts_fst env false Γ body]
        cases walkStmts env false Γ body with
        | error e => rfl
        | ok r =>
          simp only [Except.map]
          rw [← walkStmts_fst env false r.1 orelse]
          cases walkStmts env false r.1 orelse <;> rfl
  | _ =>
    rw [walkStmt]
    · cases checkStmt _ _ _ _ <;> rfl
    all_goals simp

/-- The context of `walkStmts` is the context of `checkStmts`. -/
theorem walkStmts_fst (env : ModEnv) (top : Bool) (Γ : Ctx) (ss : List PyStmt) :
    (walkStmts env top Γ ss).map Prod.fst = checkStmts env top Γ ss := by
  cases ss with
  | nil => rfl
  | cons s ss =>
    rw [walkStmts, checkStmts, ← walkStmt_fst env top Γ s]
    cases walkStmt env top Γ s with
    | error e => rfl
    | ok r =>
      simp only [Except.map, bind, Except.bind, pure, Except.pure]
      rw [← walkStmts_fst env top r.1 ss]
      cases walkStmts env top r.1 ss <;> rfl

end

/-- The bindings of the body of `f` with their checked types: the context the
statements before the final `return` leave, and the bindings of their loop
bodies; none for a linked function, whose body is not checked. -/
def pyBodyBindings (f : CheckedFn) : List (String × PyTy) :=
  if f.sig.linked.isNone then
    match walkStmts f.env true (Ctx.ofParams f.sig.params) f.body.dropLast with
    | .ok r => r.1.vars ++ r.2
    | .error _ => []
  else []

/-- The parameters and the bindings of the body of `f`, with their checked
types. -/
def pyBindings (f : CheckedFn) : List (String × PyTy) :=
  f.sig.params ++ pyBodyBindings f

/-- The names of the parameters and bindings of `f` of a secret type, without
repetition, in order of first occurrence in `pyBindings f`. -/
def pySecretBindings (f : CheckedFn) : List String :=
  ((pyBindings f).filterMap fun p => if p.2.isSecretTy then some p.1 else none).eraseDups

/-- A name is in `pySecretBindings f` exactly when it is a parameter or a binding
of the body of `f` whose checked type is secret. -/
theorem mem_pySecretBindings_iff (f : CheckedFn) (x : String) :
    x ∈ pySecretBindings f ↔
      (∃ τ, (x, τ) ∈ f.sig.params ∧ τ.isSecretTy = true) ∨
        (∃ τ, (x, τ) ∈ pyBodyBindings f ∧ τ.isSecretTy = true) := by
  simp only [pySecretBindings, List.mem_eraseDups, List.mem_filterMap, pyBindings,
    List.mem_append, Option.ite_none_right_eq_some, Option.some.injEq, Prod.exists]
  constructor
  · rintro ⟨y, τ, h | h, hs, rfl⟩
    · exact .inl ⟨τ, h, hs⟩
    · exact .inr ⟨τ, h, hs⟩
  · rintro (⟨τ, h, hs⟩ | ⟨τ, h, hs⟩)
    · exact ⟨x, τ, .inl h, hs, rfl⟩
    · exact ⟨x, τ, .inr h, hs, rfl⟩

end Hax.Py
