/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.AST

/-!
# Monadic A-normal form of `ImpExpr`

`NF` is an A-normal form of `ImpExpr` in which every intermediate value is named by
a `letBind`. A call takes atoms (variables or literals) as arguments; the one
exception is the upper bound of a `forFold`, which may be an `Add`, `Sub`, `Mul` or
`min` of bounds. A branch or loop guard is a variable. By convention an array is a
value, read by an `index` call and written by an `array_update` call that rebinds or
assigns the array's name; the predicate does not check this.

Loops occur both as folds (`forFold`, `forFoldRev`, `whileFold` and their `Return`
forms, with early exits in a control-flow monad) and as `whileLoop` on a variable,
and a variable may be updated by `assign`. The constructors `lam`, `borrow`, `deref`,
`forLoop`, `forLoopRev`, `break_`, `continue_`, `earlyReturn` and `questionMark` do
not occur.

The predicate is syntactic and states no scoping or typing condition. A loop body
is checked with the loop context `il`: `true` inside the body of a
`whileFoldReturn`, `forFoldReturn` or `forFoldRevReturn`, where a `cfBreak`,
`cfContinue` or `cfBreakContinue` of an atom or `unitVal` is an exit; `false`
elsewhere, and the body of any other loop resets it to `false`.

## Main definitions

* `nfAtom` — a variable or a literal
* `nfBound` — a counted-loop bound: an atom, or `Add`/`Sub`/`Mul`/`min` of two bounds
* `nfRhs` — the right-hand side of a `letBind`: a call on atoms, a literal, a
  variable, or a projection of a variable
* `isNFK il e` — `e` is in normal form in loop context `il`
* `isNF`, `NF` — the normal form outside every exit loop, as a `Bool` and a `Prop`

## Main results

* `isNFK_mono` — a normal form in loop context `il₀` is one in `il₀ || il`
* `isNFK_of_isNF` — a normal form outside every exit loop is one in every loop
  context
-/

@[expose] public section

namespace Hax

/-- A variable or a literal. -/
def nfAtom : ImpExpr → Bool
  | .var _ => true
  | .lit _ => true
  | _ => false

/-- A variable. -/
def nfVar : ImpExpr → Bool
  | .var _ => true
  | _ => false

/-- A literal. -/
def nfLit : ImpExpr → Bool
  | .lit _ => true
  | _ => false

/-- The payload of an exit (`cfBreak`, `cfContinue`, `cfBreakContinue`): an atom or
    `unitVal`. -/
def nfBreakArg : ImpExpr → Bool
  | .var _ => true
  | .lit _ => true
  | .unitVal => true
  | _ => false

/-- The arithmetic operations of a counted-loop bound. -/
def nfBoundOp (f : String) : Bool :=
  f == "Add" || f == "Sub" || f == "Mul" || f == "min"

/-- A counted-loop bound: an atom, or a binary `Add`, `Sub`, `Mul` or `min` of two
    bounds. -/
def nfBound : ImpExpr → Bool
  | .var _ => true
  | .lit _ => true
  | .app f [a, b] => nfBoundOp f && nfBound a && nfBound b
  | _ => false

/-- The right-hand side of a `letBind` in normal form: a call on atoms, a literal, a
    variable, or a projection of a variable. -/
def nfRhs : ImpExpr → Bool
  | .app _ args => args.all nfAtom
  | .lit _ => true
  | .var _ => true
  | .proj (.var _) _ => true
  | _ => false

/-- The right-hand side of an `assign` in normal form: a right-hand side of a
    `letBind` in normal form. The two positions share one predicate; the separate
    name marks the `assign` clause of `isNFK`, so a consumer unfolds the assign
    position by name without unfolding `nfRhs` at every `letBind`. -/
def nfAssignRhs (e : ImpExpr) : Bool := nfRhs e

/-- `e` is in monadic A-normal form in loop context `il` (`true` inside the body of
    an exit loop):
    * `letBind _ v b` with `nfRhs v` and `b` in normal form;
    * an atom or `unitVal`;
    * `seq a b`, `ifThenElse (var _) t e` and `typeAscription e _` with components in
      normal form in the same context;
    * `match_ (app _ args) [(tuplePat [varPat _, varPat _], b)]` with atom arguments
      and `b` in normal form in the same context;
    * `whileLoop (var _) b`, `whileFold (var _) b`, `forFold _ lo hi b` with `lo` a
      literal and `hi` a bound, and `forFoldRev _ lo hi b` with literal bounds, the
      body `b` in normal form outside every exit loop;
    * `whileFoldReturn (var _) b`, `forFoldReturn _ lo hi b` and
      `forFoldRevReturn _ lo hi b` with literal bounds, the body inside an exit loop;
    * inside an exit loop, `cfBreak`, `cfContinue` and `cfBreakContinue` of an atom
      or `unitVal`;
    * `assign _ r` with `nfAssignRhs r`;
    * `tuple es` of variables. -/
def isNFK : Bool → ImpExpr → Bool
  | il, .letBind _ v b => nfRhs v && isNFK il b
  | _, .var _ => true
  | _, .lit _ => true
  | _, .unitVal => true
  | il, .seq a b => isNFK il a && isNFK il b
  | il, .ifThenElse (.var _) t e => isNFK il t && isNFK il e
  | _, .whileLoop (.var _) b => isNFK false b
  | _, .assign _ r => nfAssignRhs r
  | il, .match_ (.app _ args) [(.tuplePat [.varPat _, .varPat _], b)] =>
      args.all nfAtom && isNFK il b
  | _, .tuple es => es.all nfVar
  | _, .forFold _ lo hi b => nfLit lo && nfBound hi && isNFK false b
  | _, .forFoldRev _ lo hi b => nfLit lo && nfLit hi && isNFK false b
  | _, .whileFold (.var _) b => isNFK false b
  | _, .whileFoldReturn (.var _) b => isNFK true b
  | _, .forFoldReturn _ lo hi b => nfLit lo && nfLit hi && isNFK true b
  | _, .forFoldRevReturn _ lo hi b => nfLit lo && nfLit hi && isNFK true b
  | il, .cfBreak e => il && nfBreakArg e
  | il, .cfContinue e => il && nfBreakArg e
  | il, .cfBreakContinue e => il && nfBreakArg e
  | il, .typeAscription e _ => isNFK il e
  | _, _ => false

/-- `e` is in monadic A-normal form outside every exit loop. -/
def isNF (e : ImpExpr) : Bool := isNFK false e

/-- `e` is in monadic A-normal form outside every exit loop. -/
def NF (e : ImpExpr) : Prop := isNF e = true

instance : DecidablePred NF := fun e => inferInstanceAs (Decidable (isNF e = true))

/-- A variable is an atom. -/
@[simp] theorem nfAtom_var (n : String) : nfAtom (.var n) = true := rfl

/-- A literal is an atom. -/
@[simp] theorem nfAtom_lit (l : ImpLit) : nfAtom (.lit l) = true := rfl

/-- A normal form in loop context `il₀` is a normal form in loop context
    `il₀ || il`. -/
theorem isNFK_mono (il₀ il : Bool) (e : ImpExpr) (h : isNFK il₀ e = true) :
    isNFK (il₀ || il) e = true := by
  fun_induction isNFK il₀ e <;> simp_all [isNFK]

/-- A normal form outside every exit loop is a normal form in every loop context. -/
theorem isNFK_of_isNF (e : ImpExpr) (il : Bool) (h : NF e) : isNFK il e = true :=
  isNFK_mono false il e h

end Hax
