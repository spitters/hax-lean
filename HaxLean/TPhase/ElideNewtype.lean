/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.TPhase.IrrefutableTupleMatch

/-!
# Identity heads elided from a term

A newtype `struct S(Inner)` reaches the erased term in two forms: its construction
`S(x)` is the call `app "S" [x]`, and its projection `x.0` is the call `app ".0" [x]`.
Both are the identity on their one argument. For a list `heads` of call heads, the
rewrite of one node replaces `app f [x]` with `f ∈ heads` by `x` (`rewriteSite`), and
`elideNewtype heads` applies it bottom-up at every node.

Under `denote'`, the rewrite refines the call when the builtin interpretation is the
identity at every head of `heads` wherever it is defined (`IdentityOn`): a run of
`app f [x]` that does not end in an error evaluates `x` to a value `v`, and `bi f [v]`
returns `v`.

## Main results

* `denote'_app_single_run`: the run of a call with one argument.
* `denote'_rewriteSite`: the rewrite of one node refines the node under `denote'`.
* `elideNewtype_refines`: the whole pass refines its input under `denote'`, from equal
  environments to equal final environments.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax

namespace ElideNewtype

open IrrefutableTupleMatch InlineLocalClosures

/-- The rewrite of one node: a call `app f [x]` whose head is in `heads` is `x`; every
    other node is unchanged. -/
def rewriteSite (heads : List String) (e : ImpExpr) : ImpExpr :=
  match e with
  | .app f [x] => if heads.contains f then x else e
  | _ => e

/-- The builtin interpretation `bi` is the identity on one argument at every head of
    `heads`, wherever it is defined. -/
def IdentityOn (bi : Builtins) (heads : List String) : Prop :=
  ∀ f, f ∈ heads → ∀ v w, bi f [v] = some w → w = v

/-- The run of a call with one argument: the argument's run, then the builtin at its
    value when that value is not a control-flow value. -/
theorem denote'_app_single_run (bi : Builtins) (fuel : Nat) (f : String) (x : ImpExpr)
    (env : Env) :
    denote' bi fuel (.app f [x]) env =
      match denote' bi fuel x env with
      | (.val (.controlFlow _ _), s) => (.err "non-value in function arguments", s)
      | (.val v, s) =>
        match bi f [v] with
        | some w => (.val w, s)
        | none => (.err s!"unknown function or bad args: {f}", s)
      | (_, s) => (.err "non-value in function arguments", s) := by
  conv => lhs; unfold denote'
  unfold denoteApp' denoteArgs'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  generalize denote' bi fuel x env = p
  obtain ⟨r, s⟩ := p
  cases r with
  | val v =>
    cases v with
    | controlFlow b w => rfl
    | _ =>
      dsimp only [StateT.bind]
      rw [denoteArgs'_nil]
      dsimp only [Option.map, StateT.pure]
      simp only [bind, pure]
      split <;> (rename_i h; rw [h]; rfl)
  | _ => rfl

/-- The rewrite of one node refines the node under `denote'` when `bi` is the identity
    at `heads`. -/
theorem denote'_rewriteSite (bi : Builtins) (heads : List String) (hbi : IdentityOn bi heads)
    (fuel : Nat) (e : ImpExpr) :
    RefE (fun e₁ e₂ => e₁ = e₂) (denote' bi fuel (rewriteSite heads e))
      (denote' bi fuel e) := by
  unfold rewriteSite
  split
  · rename_i f x
    split
    · rename_i hf
      intro e₁ e₂ h o s₂ hr hb
      subst h
      change denote' bi fuel (.app f [x]) e₁ = (o, s₂) at hr
      show ∃ s₁, denote' bi fuel x e₁ = (o, s₁) ∧ s₁ = s₂
      rw [denote'_app_single_run] at hr
      revert hr
      generalize hd : denote' bi fuel x e₁ = p
      obtain ⟨r, s⟩ := p
      have hmem : f ∈ heads := by simpa using hf
      cases r with
      | val v =>
        cases v with
        | controlFlow b w => intro hr; cases hr; exact absurd ⟨_, rfl⟩ hb
        | _ =>
          intro hr
          dsimp only at hr
          split at hr
          · rename_i w hw
            cases hr
            rw [hbi f hmem _ _ hw]
            exact ⟨_, rfl, rfl⟩
          · cases hr; exact absurd ⟨_, rfl⟩ hb
      | _ => intro hr; cases hr; exact absurd ⟨_, rfl⟩ hb
    · exact RefR.refl _
  · exact RefR.refl _

end ElideNewtype

open ElideNewtype IrrefutableTupleMatch in
/-- The elision of the call heads `heads`: `ElideNewtype.rewriteSite heads` applied
    bottom-up at every node. -/
def elideNewtype (heads : List String) (e : ImpExpr) : ImpExpr :=
  bottomUp (rewriteSite heads) e

open ElideNewtype IrrefutableTupleMatch InlineLocalClosures in
/-- **The whole pass.** When `bi` is the identity at `heads`, `elideNewtype heads e`
    refines `e` under `denote'`: from equal environments, every run of `e` that does not
    end in an error is the run of the rewritten term, with the same final environment. -/
theorem elideNewtype_refines (bi : Builtins) (heads : List String)
    (hbi : IdentityOn bi heads) (e : ImpExpr) (fuel : Nat) :
    RefE (fun e₁ e₂ => e₁ = e₂) (denote' bi fuel (elideNewtype heads e))
      (denote' bi fuel e) :=
  denote'_bottomUp (rd := fun _ => true) (up := fun _ => true) (fun _ => rfl)
    (fun _ _ _ h₁ h₂ => h₁.trans h₂) (fun _ _ _ _ h => h ▸ rfl) (fun _ _ _ _ h _ => h ▸ rfl)
    (fun _ _ _ h _ => h ▸ rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun fuel e => denote'_rewriteSite bi heads hbi fuel e) e true
    (readsOk_of_rd _ (fun _ => rfl) e true) fuel

end Hax
