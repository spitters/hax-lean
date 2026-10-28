/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.SemanticsCF

/-!
# One-step unfolding lemmas for `denote'`

Equations that unfold the control-flow semantics `denote'` of `HaxLean.SemanticsCF`
by one constructor, stated on the state-passing form `denote' bi fuel e env`, and the
one-trip unfolding of `denoteWhile'` at positive fuel.

## Main results

* `denote'_whileFold` — `denote'` at a `whileFold` is `denoteWhile'`
* `denote'_letBind_run`, `denote'_seq_run`, `denote'_assign_run`,
  `denote'_ifThenElse_run` — one-step unfoldings at the binding and branching
  constructors, with control-flow values and errors passed through
* `denote'_unitVal_run`, `denote'_lit_run`, `denote'_var_run`,
  `denote'_cfBreak_unit_run`, `denote'_breakStmt_run` — the leaves
* `denoteWhile'_succ_run` — one trip of `denoteWhile'` at positive fuel
-/

@[expose] public section

namespace Hax

/-- `denote'` at a `whileFold` is `denoteWhile'`. -/
theorem denote'_whileFold (bi : Builtins) (fuel : Nat) (c body : ImpExpr) :
    denote' bi fuel (.whileFold c body) = denoteWhile' bi fuel c body := by
  conv => lhs; unfold denote'

/-- `denote'` at `unitVal`. -/
theorem denote'_unitVal_run (bi : Builtins) (fuel : Nat) (env : Env) :
    denote' bi fuel .unitVal env = (.val .unit, env) := by
  unfold denote'; rfl

/-- One-step unfolding of `denote'` at a `letBind`. -/
theorem denote'_letBind_run (bi : Builtins) (fuel : Nat) (n : String) (v b : ImpExpr)
    (env : Env) :
    denote' bi fuel (.letBind n v b) env =
      match denote' bi fuel v env with
      | (.val (.controlFlow isBreak w), env') => (.val (.controlFlow isBreak w), env')
      | (.val w, env') => denote' bi fuel b (Env.extend env' n w)
      | (other, env') => (other, env') := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, pure, Pure.pure, StateT.pure, Id.run]
  generalize denote' bi fuel v env = p
  obtain ⟨rv, env'⟩ := p
  cases rv <;> try rfl
  rename_i w; cases w <;> rfl

/-- One-step unfolding of `denote'` at a `seq`. -/
theorem denote'_seq_run (bi : Builtins) (fuel : Nat) (a b : ImpExpr) (env : Env) :
    denote' bi fuel (.seq a b) env =
      match denote' bi fuel a env with
      | (.val (.controlFlow isBreak w), env') => (.val (.controlFlow isBreak w), env')
      | (.val _, env') => denote' bi fuel b env'
      | (other, env') => (other, env') := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  generalize denote' bi fuel a env = p
  obtain ⟨rv, env'⟩ := p
  cases rv <;> try rfl
  rename_i w; cases w <;> rfl

/-- One-step unfolding of `denote'` at an `assign`. -/
theorem denote'_assign_run (bi : Builtins) (fuel : Nat) (n : String) (v : ImpExpr)
    (env : Env) :
    denote' bi fuel (.assign n v) env =
      match denote' bi fuel v env with
      | (.val (.controlFlow isBreak w), env') => (.val (.controlFlow isBreak w), env')
      | (.val w, env') => (.val .unit, Env.extend env' n w)
      | (other, env') => (other, env') := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, pure, Pure.pure, StateT.pure, Id.run]
  generalize denote' bi fuel v env = p
  obtain ⟨rv, env'⟩ := p
  cases rv <;> try rfl
  rename_i w; cases w <;> rfl

/-- `denote'` at a literal. -/
theorem denote'_lit_run (bi : Builtins) (fuel : Nat) (l : ImpLit) (env : Env) :
    denote' bi fuel (.lit l) env = (.val (Value.ofLit l), env) := by
  unfold denote'; rfl

/-- `denote'` at a variable. -/
theorem denote'_var_run (bi : Builtins) (fuel : Nat) (x : String) (env : Env) :
    denote' bi fuel (.var x) env =
      match env x with
      | some v => (.val v, env)
      | none => (.err s!"undefined variable: {x}", env) := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, Pure.pure, StateT.pure, Id.run]
  cases env x <;> rfl

/-- `denote'` at a value-less `cfBreak`. -/
theorem denote'_cfBreak_unit_run (bi : Builtins) (fuel : Nat) (env : Env) :
    denote' bi fuel (.cfBreak .unitVal) env = (.val (.controlFlow true .unit), env) := by
  simp [denote']; rfl

/-- `denote'` at the `break` statement hax leaves in the else-branch of a
    desugared `while` guard. -/
theorem denote'_breakStmt_run (bi : Builtins) (fuel : Nat) (env : Env) :
    denote' bi fuel (.seq (.cfBreak .unitVal) .unitVal) env =
      (.val (.controlFlow true .unit), env) := by
  rw [denote'_seq_run, denote'_cfBreak_unit_run]

/-- One-step unfolding of `denote'` at an `ifThenElse`. -/
theorem denote'_ifThenElse_run (bi : Builtins) (fuel : Nat) (c t e : ImpExpr) (env : Env) :
    denote' bi fuel (.ifThenElse c t e) env =
      match denote' bi fuel c env with
      | (.val (.controlFlow isBreak w), env') => (.val (.controlFlow isBreak w), env')
      | (.val (.bool true), env') => denote' bi fuel t env'
      | (.val (.bool false), env') => denote' bi fuel e env'
      | (.val _, env') => (.err "if condition not a bool", env')
      | (other, env') => (other, env') := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  generalize denote' bi fuel c env = p
  obtain ⟨rv, env'⟩ := p
  cases rv <;> try rfl
  rename_i w; cases w <;> try rfl
  rename_i b; cases b <;> rfl

/-- One trip of `denoteWhile'` at positive fuel. -/
theorem denoteWhile'_succ_run (bi : Builtins) (n : Nat) (cond body : ImpExpr) (env : Env) :
    denoteWhile' bi (n + 1) cond body env =
      match denote' bi (n + 1) cond env with
      | (.val (.controlFlow isBreak v), env') => (.val (.controlFlow isBreak v), env')
      | (.val (.bool true), env') =>
          match denote' bi (n + 1) body env' with
          | (.val (.controlFlow true v), env'') => (.val v, env'')
          | (.val (.controlFlow false _), env'') => denoteWhile' bi n cond body env''
          | (.val _, env'') => denoteWhile' bi n cond body env''
          | (other, env'') => (other, env'')
      | (.val (.bool false), env') => (.val .unit, env')
      | (.val _, env') => (.err "while condition not a bool", env')
      | (other, env') => (other, env') := by
  have hfuel : ¬(n + 1 = 0) := by omega
  conv => lhs; unfold denoteWhile'
  rw [ite_eq_right hfuel]
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  simp only [show n + 1 - 1 = n from rfl]
  generalize denote' bi (n + 1) cond env = p
  obtain ⟨rc, env'⟩ := p
  cases rc <;> try rfl
  rename_i w; cases w <;> try rfl
  rename_i b; cases b <;> try rfl
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  generalize denote' bi (n + 1) body env' = q
  obtain ⟨rb, env''⟩ := q
  cases rb <;> try rfl
  rename_i w; cases w <;> try rfl
  rename_i b _; cases b <;> rfl

end Hax

end
