/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import HaxLean.Py.Types

/-!
# Index bounds of the Python subset

A source-level analysis of the array indices of a checked module in the fact language of
the compiler's index check `idxInvCheckB` (`X86Backend/IdxInvCheck.lean` of the compiler
package). Every index `a[i]` and `x.set(i, v)` of a function reached from an entry needs an
upper bound at most the length of the array; `idxCheck` returns the position of the first
index without one, with the name and the length of the array.

The abstract value of an expression (`Bnd`) is an inclusive lower bound, an optional
exclusive upper bound, a list of excluded values and the shape of its term (`Shape`), which
says where the compiler's entailment can use the upper bound. The rules of `exprBnd` are
those of the check's entailment: a constant (`linOf` of an immediate); an addition or a
subtraction of a constant (`linOf`, a subtraction only of a constant at most the lower
bound); a product with a constant (`mulLe`); a conjunction with a constant mask (the mask
rule of `hiLe`); a word constructor or `.cast` whose argument fits the width. An equality
guard `x == c` or `x != c` with `c` a literal or a module constant gives `x` the value `c` on
one arm and excludes `c` on the other (`cmpFacts`), and an excluded value at a bound moves
the bound by one (`hiNe`, `lbNe`).

A conditional whose arms read no index, update no array, call no linked function and contain
no loop and no `return` (`keepsE`, `keepsS`) is compiled to a select (`lowerSelects`), and the
index check reads no bound off a select: its value, and every name such an `if` rebinds, has
no upper bound. The bounds after any other `if` are the join of the arms that fall through,
each under the facts of its guard.

A loop `for i in range(lo, hi)` bounds `i` by `hi` when `hi` has a known value. A name
rebound in a loop body has at the loop head the least bound `Bnd.widen` stable under the body:
upper bounds among the successors of the constants of the function, lower bounds `0` or `1`,
no excluded values, the candidates of the compiler's annotation `idxAnnot`. A call of a
module function analyses the callee's body under the bounds of the arguments.

## Main definitions

* `Bnd`, `Bnd.Mem`, `Bnd.join`, `Bnd.widen`, `Bnd.exclude`: abstract values.
* `keepsE`, `keepsS`: the conditionals the compiler keeps as branches.
* `exprBnd`: the abstract value of an expression.
* `walkE`, `walkS`, `walkSs`: the index obligations of expressions and statements.
* `analyze`, `idxCheck`: the analysis of the functions reached from the entries.
* `EvalN`: the natural-number meaning of the expression forms `exprBnd` bounds.

## Main results

* `Bnd.mem_join_left`, `Bnd.mem_join_right`, `Bnd.mem_widen`, `Bnd.mem_exclude`: the join,
  the widening and the exclusion keep every value of their arguments.
* `exprBnd_sound`: the value of an expression lies in its abstract value when every name
  lies in its bound.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Py

namespace IdxBound

/-! ## Abstract values -/

/-- The shape of the term of an expression as the index check reads it: `lin`, an atom plus a
constant, whose upper bound holds wherever the term occurs; `prod`, a product with a constant
plus a constant, whose upper bound holds for an index, under additions of constants and under
masks; `mask`, a conjunction with a constant mask, whose upper bound holds for an index
only. -/
inductive Shape where
  | lin
  | prod
  | mask
  deriving Repr, DecidableEq, Inhabited

/-- The least shape at or above both. -/
def Shape.join : Shape → Shape → Shape
  | .lin, .lin => .lin
  | .mask, _ => .mask
  | _, .mask => .mask
  | _, _ => .prod

/-- An abstract natural number: an inclusive lower bound `lb`, an optional exclusive upper
bound `ub`, excluded values `ex` and the shape `sh` of the term. -/
structure Bnd where
  lb : Nat
  ub : Option Nat
  ex : List Nat
  sh : Shape
  deriving Repr, DecidableEq, Inhabited

/-- Whether `v` is below the optional exclusive bound `u`. -/
def below : Option Nat → Nat → Bool
  | some u, v => decide (v < u)
  | none, _ => true

namespace Bnd

/-- No bound. -/
def top : Bnd := ⟨0, none, [], .lin⟩

/-- The value `c`. -/
def exact (c : Nat) : Bnd := ⟨c, some (c + 1), [], .lin⟩

/-- The values of an abstract value: `v` lies in `[lb, ub)` and is not excluded. -/
def Mem (b : Bnd) (v : Nat) : Prop := b.lb ≤ v ∧ below b.ub v = true ∧ v ∉ b.ex

instance (b : Bnd) (v : Nat) : Decidable (b.Mem v) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The value of an abstract value of shape `lin` with one value. -/
def exact? (b : Bnd) : Option Nat :=
  if b.sh = .lin ∧ b.ub = some (b.lb + 1) then some b.lb else none

/-- An excluded lower bound raises the lower bound by one (`lbNe`); an excluded largest value
below the upper bound lowers the upper bound by one (`hiNe`). -/
def norm (b : Bnd) : Bnd :=
  { b with
    lb := if b.lb ∈ b.ex then b.lb + 1 else b.lb
    ub := b.ub.map fun u => if u - 1 ∈ b.ex then u - 1 else u }

/-- The abstract value with the value `c` excluded. -/
def exclude (c : Nat) (b : Bnd) : Bnd := norm { b with ex := c :: b.ex }

/-- The join: the least lower bound, the greatest upper bound, and the values excluded by
one argument and not in the other. -/
def join (a b : Bnd) : Bnd where
  lb := min a.lb b.lb
  ub := match a.ub, b.ub with
    | some u, some u' => some (max u u')
    | _, _ => none
  ex := a.ex.filter (fun c => !decide (b.Mem c)) ++ b.ex.filter (fun c => !decide (a.Mem c))
  sh := a.sh.join b.sh

/-- The least threshold of `thr` at or above `u`. -/
def thrUp (thr : List Nat) (u : Nat) : Option Nat := (thr.filter (u ≤ ·)).min?

/-- The widening to the thresholds `thr`: the upper bound raised to the least threshold at or
above it (or dropped), the lower bound lowered to `0` or `1`, no excluded values, shape
`lin`. -/
def widen (thr : List Nat) (b : Bnd) : Bnd where
  lb := if 1 ≤ b.lb then 1 else 0
  ub := b.ub.bind (thrUp thr)
  ex := []
  sh := .lin

/-- The sum with the constant `c`. -/
def addC (b : Bnd) (c : Nat) : Bnd :=
  if b.sh = .mask then top else ⟨b.lb + c, b.ub.map (· + c), [], b.sh⟩

/-- The difference with the constant `c`, bounded when `c` is at most the lower bound. -/
def subC (b : Bnd) (c : Nat) : Bnd :=
  if b.sh ≠ .mask ∧ c ≤ b.lb then ⟨b.lb - c, b.ub.map (· - c), [], b.sh⟩ else top

/-- The product with the constant `c`, of shape `prod`. -/
def mulC (b : Bnd) (c : Nat) : Bnd :=
  if b.sh = .lin then ⟨0, b.ub.map (fun u => (u - 1) * c + 1), [], .prod⟩ else top

/-- The conjunction with the constant mask `m`: the bound of the argument when it is within
the mask, and otherwise the mask, of shape `mask`. -/
def andC (b : Bnd) (m : Nat) : Bnd :=
  match b.ub with
  | some u => if u ≤ m + 1 then ⟨0, some u, [], b.sh⟩ else ⟨0, some (m + 1), [], .mask⟩
  | none => ⟨0, some (m + 1), [], .mask⟩

/-- The conversion to a word of `w` bits: the argument's value when its upper bound is at most
`2 ^ w`. -/
def fit (b : Bnd) (w : Nat) : Bnd :=
  match b.ub with
  | some u => if u ≤ 2 ^ w then b else top
  | none => top

end Bnd

open Bnd

/-! ## Expressions -/

/-- The bounds of local names. -/
abbrev Bnds := List (String × Bnd)

/-- The bounds with `x` bound to `b`. -/
def setB (x : String) (b : Bnd) (σ : Bnds) : Bnds := (x, b) :: σ.filter fun p => !decide (p.1 = x)

/-- The bound of a name: a local, or a module constant. -/
def nameBnd (env : ModEnv) (σ : Bnds) (x : String) : Bnd :=
  match σ.lookup x with
  | some b => b
  | none =>
    match env.consts.lookup x with
    | some n => exact n
    | none => top

/-- The value of an `int` literal at least `0` or of a module constant. -/
def litNat (env : ModEnv) (e : PyExpr) : Option Nat :=
  match litVal env e with
  | some n => if 0 ≤ n then some n.toNat else none
  | none => none

/-- The polarity of an equality comparison. -/
def eqPol : PyCmpOp → Option Bool
  | .eq => some true
  | .notEq => some false
  | _ => none

/-- An equality guard `x == c` or `x != c` (either operand order) with `c` a literal or a
module constant: the name, the value and the polarity. -/
def guardOf (env : ModEnv) : PyExpr → Option (String × Nat × Bool)
  | .compare _ l [op] [r] =>
    match eqPol op with
    | none => none
    | some pol =>
      match l, litNat env r with
      | .name _ x, some c => some (x, c, pol)
      | _, _ =>
        match r, litNat env l with
        | .name _ x, some c => some (x, c, pol)
        | _, _ => none
  | _ => none

/-- The bounds on the arm of the condition `c` where it has the value `b`. -/
def refine (env : ModEnv) (σ : Bnds) (c : PyExpr) (b : Bool) : Bnds :=
  match guardOf env c with
  | some (x, k, pol) =>
    if b = pol then setB x (exact k) σ else setB x ((nameBnd env σ x).exclude k) σ
  | none => σ

mutual

/-- The expression keeps a branch in the compiled code: it reads an index, updates an array
or calls a linked function. A conditional whose arms keep no branch has arms of register
arithmetic and register constants only, which the compiler lowers to a select
(`NFProg.Lowerable`); the index check reads no bound off a select. -/
def keepsE (env : ModEnv) : PyExpr → Bool
  | .name .. | .const .. => false
  | .binOp _ l _ r => keepsE env l || keepsE env r
  | .unaryOp _ _ e => keepsE env e
  | .boolOp _ _ vs => keepsEs env vs
  | .compare _ l _ cs => keepsE env l || keepsEs env cs
  | .ifExp _ c t e => keepsE env c || keepsE env t || keepsE env e
  | .call _ (.attribute _ _ "set") _ _ => true
  | .call _ (.name _ f) args _ =>
    (match env.fns.lookup f with
     | some sig => sig.linked.isSome
     | none => false) || keepsEs env args
  | .call _ f args _ => keepsE env f || keepsEs env args
  | .attribute _ e _ => keepsE env e
  | .subscript .. => true
  | .tuple _ es => keepsEs env es

/-- A list of expressions keeps a branch. -/
def keepsEs (env : ModEnv) : List PyExpr → Bool
  | [] => false
  | e :: es => keepsE env e || keepsEs env es

end

mutual

/-- The statement keeps a branch in the compiled code: an expression of it does
(`keepsE`), or it is a loop or a `return`. -/
def keepsS (env : ModEnv) : PyStmt → Bool
  | .assign _ _ v => keepsE env v
  | .annAssign _ _ _ v _ =>
    match v with
    | some v => keepsE env v
    | none => false
  | .forStmt .. => true
  | .ifStmt _ c body orelse => keepsE env c || keepsSs env body || keepsSs env orelse
  | .ret .. => true
  | .expr _ v => keepsE env v
  | _ => false

/-- A statement list keeps a branch. -/
def keepsSs (env : ModEnv) : List PyStmt → Bool
  | [] => false
  | s :: ss => keepsS env s || keepsSs env ss

end

/-- The abstract value of a binary operation. -/
def binBnd (op : PyBinOp) (l r : Bnd) : Bnd :=
  match op with
  | .add =>
    match l.exact?, r.exact? with
    | some a, some b => exact (a + b)
    | _, some c => l.addC c
    | some c, _ => r.addC c
    | none, none => top
  | .sub =>
    match r.exact? with
    | some c => l.subC c
    | none => top
  | .mult =>
    match l.exact?, r.exact? with
    | some a, some b => exact (a * b)
    | _, some c => l.mulC c
    | some c, _ => r.mulC c
    | none, none => top
  | .bitAnd =>
    match l.exact?, r.exact? with
    | some a, some b => exact (a &&& b)
    | _, some c => l.andC c
    | some c, _ => r.andC c
    | none, none => top
  | _ => top

/-- The abstract value of an expression under the bounds `σ`. -/
def exprBnd (env : ModEnv) (σ : Bnds) : PyExpr → Bnd
  | .const _ (.int n) => if 0 ≤ n then exact n.toNat else top
  | .name _ x => nameBnd env σ x
  | .binOp _ l op r => binBnd op (exprBnd env σ l) (exprBnd env σ r)
  | .call _ (.name _ f) [a] [] =>
    match wordName? f with
    | some w => (exprBnd env σ a).fit w.bits
    | none => top
  | .call _ (.attribute _ recv "cast") [.name _ x] [] =>
    match wordName? x with
    | some w => (exprBnd env σ recv).fit w.bits
    | none => top
  | .ifExp _ c t e =>
    if keepsE env t || keepsE env e then
      (exprBnd env (refine env σ c true) t).join (exprBnd env (refine env σ c false) e)
    else top
  | _ => top

/-! ## Natural-number meaning and soundness -/

/-- The condition `c` has the value `b` at the name values `ρ`: an equality guard compares
the value of its name with its constant; any other condition has either value. -/
def CondN (env : ModEnv) (ρ : String → Option Nat) (c : PyExpr) (b : Bool) : Prop :=
  match guardOf env c with
  | some (x, k, pol) => ∃ v, ρ x = some v ∧ (decide (v = k) == pol) = b
  | none => True

/-- `EvalN env ρ e v`: the expression `e` has the natural-number value `v` at the name values
`ρ`, for the forms `exprBnd` bounds; a subtraction has a value when it does not underflow, and
a word constructor or `.cast` reduces modulo the width. -/
inductive EvalN (env : ModEnv) (ρ : String → Option Nat) : PyExpr → Nat → Prop where
  | lit {p : Pos} {n : Int} : 0 ≤ n → EvalN env ρ (.const p (.int n)) n.toNat
  | name {p : Pos} {x : String} {v : Nat} : ρ x = some v → EvalN env ρ (.name p x) v
  | add {p : Pos} {l r : PyExpr} {a b : Nat} :
      EvalN env ρ l a → EvalN env ρ r b → EvalN env ρ (.binOp p l .add r) (a + b)
  | sub {p : Pos} {l r : PyExpr} {a b : Nat} :
      EvalN env ρ l a → EvalN env ρ r b → b ≤ a → EvalN env ρ (.binOp p l .sub r) (a - b)
  | mul {p : Pos} {l r : PyExpr} {a b : Nat} :
      EvalN env ρ l a → EvalN env ρ r b → EvalN env ρ (.binOp p l .mult r) (a * b)
  | band {p : Pos} {l r : PyExpr} {a b : Nat} :
      EvalN env ρ l a → EvalN env ρ r b → EvalN env ρ (.binOp p l .bitAnd r) (a &&& b)
  | ctor {p q : Pos} {f : String} {a : PyExpr} {w : IntWidth} {v : Nat} :
      wordName? f = some w → EvalN env ρ a v →
      EvalN env ρ (.call p (.name q f) [a] []) (v % 2 ^ w.bits)
  | cast {p q r : Pos} {recv : PyExpr} {x : String} {w : IntWidth} {v : Nat} :
      wordName? x = some w → EvalN env ρ recv v →
      EvalN env ρ (.call p (.attribute q recv "cast") [.name r x] []) (v % 2 ^ w.bits)
  | ifT {p : Pos} {c t e : PyExpr} {v : Nat} :
      CondN env ρ c true → EvalN env ρ t v → EvalN env ρ (.ifExp p c t e) v
  | ifF {p : Pos} {c t e : PyExpr} {v : Nat} :
      CondN env ρ c false → EvalN env ρ e v → EvalN env ρ (.ifExp p c t e) v

/-- Every name with a value lies in its bound. -/
def Holds (env : ModEnv) (σ : Bnds) (ρ : String → Option Nat) : Prop :=
  ∀ x v, ρ x = some v → (nameBnd env σ x).Mem v

namespace Bnd

theorem mem_top (v : Nat) : top.Mem v := ⟨Nat.zero_le _, rfl, List.not_mem_nil⟩

theorem mem_exact (c : Nat) : (exact c).Mem c := by
  simp [Mem, exact, below]

theorem eq_of_exact? {b : Bnd} {c v : Nat} (h : b.exact? = some c) (hv : b.Mem v) : v = c := by
  unfold exact? at h
  split at h
  · rename_i hc
    cases h
    obtain ⟨h1, h2, -⟩ := hv
    rw [hc.2] at h2
    simp only [below, decide_eq_true_eq] at h2
    omega
  · cases h

theorem mem_norm {b : Bnd} {v : Nat} (hv : b.Mem v) : b.norm.Mem v := by
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨?_, ?_, h3⟩
  · simp only [norm]
    split
    · rename_i hm
      have : v ≠ b.lb := fun e => h3 (e ▸ hm)
      omega
    · exact h1
  · simp only [norm]
    cases hu : b.ub with
    | none => rfl
    | some u =>
      rw [hu] at h2
      simp only [below, decide_eq_true_eq] at h2
      simp only [Option.map_some, below, decide_eq_true_eq]
      split
      · rename_i hm
        have : v ≠ u - 1 := fun e => h3 (e ▸ hm)
        omega
      · exact h2

/-- **Exclusion is sound.** -/
theorem mem_exclude {b : Bnd} {v c : Nat} (hv : b.Mem v) (hc : v ≠ c) :
    (b.exclude c).Mem v := by
  obtain ⟨h1, h2, h3⟩ := hv
  exact mem_norm ⟨h1, h2, by simp [hc, h3]⟩

/-- **The join keeps the values of its left argument.** -/
theorem mem_join_left {a : Bnd} (b : Bnd) {v : Nat} (hv : a.Mem v) : (a.join b).Mem v := by
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨Nat.le_trans (Nat.min_le_left _ _) h1, ?_, ?_⟩
  · simp only [join]
    split
    · rename_i u u' hu _
      rw [hu] at h2
      simp only [below, decide_eq_true_eq] at h2 ⊢
      omega
    · rfl
  · simp only [join, List.mem_append, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not,
      not_or, not_and, Decidable.not_not]
    exact ⟨fun h => absurd h h3, fun _ => ⟨h1, h2, h3⟩⟩

/-- **The join keeps the values of its right argument.** -/
theorem mem_join_right (a : Bnd) {b : Bnd} {v : Nat} (hv : b.Mem v) : (a.join b).Mem v := by
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨Nat.le_trans (Nat.min_le_right _ _) h1, ?_, ?_⟩
  · simp only [join]
    split
    · rename_i u u' _ hu
      rw [hu] at h2
      simp only [below, decide_eq_true_eq] at h2 ⊢
      omega
    · rfl
  · simp only [join, List.mem_append, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not,
      not_or, not_and, Decidable.not_not]
    exact ⟨fun _ => ⟨h1, h2, h3⟩, fun h => absurd h h3⟩

theorem le_of_thrUp {thr : List Nat} {u t : Nat} (h : thrUp thr u = some t) : u ≤ t := by
  have := List.min?_mem h
  simp only [List.mem_filter, decide_eq_true_eq] at this
  exact this.2

/-- **The widening keeps the values of its argument.** -/
theorem mem_widen (thr : List Nat) {b : Bnd} {v : Nat} (hv : b.Mem v) : (b.widen thr).Mem v := by
  obtain ⟨h1, h2, -⟩ := hv
  refine ⟨?_, ?_, List.not_mem_nil⟩
  · simp only [widen]
    split <;> omega
  · simp only [widen]
    cases hu : b.ub with
    | none => rfl
    | some u =>
      rw [hu] at h2
      simp only [below, decide_eq_true_eq] at h2
      simp only [Option.bind_some]
      cases ht : thrUp thr u with
      | none => rfl
      | some t =>
        have := le_of_thrUp ht
        simp only [below, decide_eq_true_eq]
        omega

theorem mem_addC {b : Bnd} {v : Nat} (c : Nat) (hv : b.Mem v) : (b.addC c).Mem (v + c) := by
  unfold addC
  split
  · exact mem_top _
  · obtain ⟨h1, h2, -⟩ := hv
    refine ⟨by simp only; omega, ?_, List.not_mem_nil⟩
    cases hu : b.ub with
    | none => rfl
    | some u =>
      rw [hu] at h2
      simp only [below, decide_eq_true_eq] at h2
      simp only [Option.map_some, below, decide_eq_true_eq]
      omega

theorem mem_subC {b : Bnd} {v c : Nat} (hv : b.Mem v) (hc : c ≤ v) : (b.subC c).Mem (v - c) := by
  unfold subC
  split
  · rename_i hlb
    obtain ⟨h1, h2, -⟩ := hv
    refine ⟨by simp only; omega, ?_, List.not_mem_nil⟩
    cases hu : b.ub with
    | none => rfl
    | some u =>
      rw [hu] at h2
      simp only [below, decide_eq_true_eq] at h2
      simp only [Option.map_some, below, decide_eq_true_eq]
      omega
  · exact mem_top _

theorem mem_mulC {b : Bnd} {v : Nat} (c : Nat) (hv : b.Mem v) : (b.mulC c).Mem (v * c) := by
  unfold mulC
  split
  · obtain ⟨-, h2, -⟩ := hv
    refine ⟨Nat.zero_le _, ?_, List.not_mem_nil⟩
    cases hu : b.ub with
    | none => rfl
    | some u =>
      rw [hu] at h2
      simp only [below, decide_eq_true_eq] at h2
      simp only [Option.map_some, below, decide_eq_true_eq]
      exact Nat.lt_succ_of_le (Nat.mul_le_mul_right c (by omega))
  · exact mem_top _

theorem mem_andC {b : Bnd} {v : Nat} (m : Nat) (hv : b.Mem v) : (b.andC m).Mem (v &&& m) := by
  obtain ⟨-, h2, -⟩ := hv
  have hl : v &&& m ≤ v := Nat.and_le_left
  have hr : v &&& m ≤ m := Nat.and_le_right
  unfold andC
  split
  · rename_i u hu
    rw [hu] at h2
    simp only [below, decide_eq_true_eq] at h2
    split
    · exact ⟨Nat.zero_le _, by simp only [below, decide_eq_true_eq]; omega, List.not_mem_nil⟩
    · exact ⟨Nat.zero_le _, by simp only [below, decide_eq_true_eq]; omega, List.not_mem_nil⟩
  · exact ⟨Nat.zero_le _, by simp only [below, decide_eq_true_eq]; omega, List.not_mem_nil⟩

theorem mem_fit {b : Bnd} {v : Nat} (w : Nat) (hv : b.Mem v) : (b.fit w).Mem (v % 2 ^ w) := by
  unfold fit
  split
  · rename_i u hu
    split
    · rename_i hw
      have h2 := hv.2.1
      rw [hu] at h2
      simp only [below, decide_eq_true_eq] at h2
      rw [Nat.mod_eq_of_lt (by omega)]
      exact hv
    · exact mem_top _
  · exact mem_top _

end Bnd

theorem lookup_filter_ne {x y : String} (h : y ≠ x) :
    ∀ σ : Bnds, (σ.filter fun p => !decide (p.1 = x)).lookup y = σ.lookup y
  | [] => rfl
  | (z, b) :: σ => by
    have ih := lookup_filter_ne h σ
    by_cases hz : z = x
    · subst hz
      have : (y == z) = false := by simpa using h
      simp [List.lookup, this, ih]
    · simp only [List.filter_cons, hz, decide_false, Bool.not_false, ite_true, List.lookup]
      split <;> simp_all

theorem nameBnd_setB (env : ModEnv) (σ : Bnds) (x y : String) (b : Bnd) :
    nameBnd env (setB x b σ) y = if y = x then b else nameBnd env σ y := by
  by_cases h : y = x
  · subst h
    simp [nameBnd, setB]
  · have : (y == x) = false := by simpa using h
    simp only [nameBnd, setB, List.lookup, this, lookup_filter_ne h σ, h, ite_false]

theorem holds_setB {env : ModEnv} {σ : Bnds} {ρ : String → Option Nat} (h : Holds env σ ρ)
    {x : String} {b : Bnd} (hb : ∀ v, ρ x = some v → b.Mem v) : Holds env (setB x b σ) ρ := by
  intro y v hy
  rw [nameBnd_setB]
  split
  · subst_vars
    exact hb v hy
  · exact h y v hy

/-- **Guards are sound.** The bounds on the arm of a condition hold where the condition has
the arm's value. -/
theorem holds_refine {env : ModEnv} {σ : Bnds} {ρ : String → Option Nat} (h : Holds env σ ρ)
    {c : PyExpr} {b : Bool} (hc : CondN env ρ c b) : Holds env (refine env σ c b) ρ := by
  unfold CondN at hc
  unfold refine
  split
  · rename_i x k pol hg
    rw [hg] at hc
    obtain ⟨v, hv, hb⟩ := hc
    split
    · rename_i hp
      subst hp
      apply holds_setB h
      intro v' hv'
      rw [hv] at hv'
      cases hv'
      have : v = k := by cases b <;> simpa using hb
      subst this
      exact mem_exact v
    · rename_i hp
      apply holds_setB h
      intro v' hv'
      rw [hv] at hv'
      cases hv'
      have : v ≠ k := by
        intro e
        subst e
        cases pol <;> cases b <;> simp_all
      exact mem_exclude (h x v hv) this
  · exact h

theorem binBnd_add {l r : Bnd} {a b : Nat} (hl : l.Mem a) (hr : r.Mem b) :
    (binBnd .add l r).Mem (a + b) := by
  cases ha : l.exact? <;> cases hb : r.exact? <;> simp only [binBnd, ha, hb]
  · exact mem_top _
  · rw [eq_of_exact? hb hr]
    exact mem_addC _ hl
  · rw [eq_of_exact? ha hl, Nat.add_comm]
    exact mem_addC _ hr
  · rw [eq_of_exact? ha hl, eq_of_exact? hb hr]
    exact mem_exact _

theorem binBnd_sub {l r : Bnd} {a b : Nat} (hl : l.Mem a) (hr : r.Mem b) (hab : b ≤ a) :
    (binBnd .sub l r).Mem (a - b) := by
  simp only [binBnd]
  split
  · rename_i c hc
    have := eq_of_exact? hc hr
    subst this
    exact mem_subC hl hab
  · exact mem_top _

theorem binBnd_mul {l r : Bnd} {a b : Nat} (hl : l.Mem a) (hr : r.Mem b) :
    (binBnd .mult l r).Mem (a * b) := by
  cases ha : l.exact? <;> cases hb : r.exact? <;> simp only [binBnd, ha, hb]
  · exact mem_top _
  · rw [eq_of_exact? hb hr]
    exact mem_mulC _ hl
  · rw [eq_of_exact? ha hl, Nat.mul_comm]
    exact mem_mulC _ hr
  · rw [eq_of_exact? ha hl, eq_of_exact? hb hr]
    exact mem_exact _

theorem binBnd_and {l r : Bnd} {a b : Nat} (hl : l.Mem a) (hr : r.Mem b) :
    (binBnd .bitAnd l r).Mem (a &&& b) := by
  cases ha : l.exact? <;> cases hb : r.exact? <;> simp only [binBnd, ha, hb]
  · exact mem_top _
  · rw [eq_of_exact? hb hr]
    exact mem_andC _ hl
  · rw [eq_of_exact? ha hl, Nat.and_comm]
    exact mem_andC _ hr
  · rw [eq_of_exact? ha hl, eq_of_exact? hb hr]
    exact mem_exact _

/-- **Soundness of the expression bounds.** When every name with a value lies in its bound,
the value of an expression lies in its abstract value. -/
theorem exprBnd_sound {env : ModEnv} {ρ : String → Option Nat} {e : PyExpr} {v : Nat}
    (he : EvalN env ρ e v) : ∀ {σ : Bnds}, Holds env σ ρ → (exprBnd env σ e).Mem v := by
  induction he with
  | lit hn =>
    intro σ _
    simp only [exprBnd, hn, ite_true]
    exact mem_exact _
  | name hx =>
    intro σ h
    exact h _ _ hx
  | add _ _ ihl ihr =>
    intro σ h
    exact binBnd_add (ihl h) (ihr h)
  | sub _ _ hab ihl ihr =>
    intro σ h
    exact binBnd_sub (ihl h) (ihr h) hab
  | mul _ _ ihl ihr =>
    intro σ h
    exact binBnd_mul (ihl h) (ihr h)
  | band _ _ ihl ihr =>
    intro σ h
    exact binBnd_and (ihl h) (ihr h)
  | ctor hw _ ih =>
    intro σ h
    simp only [exprBnd, hw]
    exact mem_fit _ (ih h)
  | cast hw _ ih =>
    intro σ h
    simp only [exprBnd, hw]
    exact mem_fit _ (ih h)
  | ifT hc _ ih =>
    intro σ h
    simp only [exprBnd]
    split
    · exact mem_join_left _ (ih (holds_refine h hc))
    · exact mem_top _
  | ifF hc _ ih =>
    intro σ h
    simp only [exprBnd]
    split
    · exact mem_join_right _ (ih (holds_refine h hc))
    · exact mem_top _

/-! ## Index obligations -/

/-- The analysis state: the bounds of the local names and the lengths of the local
arrays. -/
structure St where
  bs : Bnds
  arrs : List (String × Nat)

/-- A refusal: the position of the index and the names concerned. -/
abbrev IdxM := Except (Pos × List String)

/-- The analysis context: the module environment of the function, the widening thresholds,
and the analysis of a call of a name with the bounds of its arguments. -/
structure Cx where
  env : ModEnv
  thr : List Nat
  call : String → List Bnd → IdxM Unit

/-- The length of an array expression: a local array, `x.set(i, v)`, a call of a module
function with an array result, or a conditional. -/
def arrLen (env : ModEnv) (arrs : List (String × Nat)) : PyExpr → Option Nat
  | .name _ x => arrs.lookup x
  | .call _ (.attribute _ recv "set") _ _ => arrLen env arrs recv
  | .call _ (.name _ f) _ _ =>
    match env.fns.lookup f with
    | some sig =>
      match sig.result with
      | .array _ n => some n
      | _ => none
    | none => none
  | .ifExp _ _ t _ => arrLen env arrs t
  | _ => none

/-- The name of an array expression, for refusals. -/
def arrName : PyExpr → String
  | .name _ x => x
  | .call _ (.attribute _ recv _) _ _ => arrName recv
  | .call _ (.name _ f) _ _ => f ++ "(..)"
  | _ => "_"

/-- The obligation of the index `i` of the array `a`: an upper bound at most its length. -/
def oblig (cx : Cx) (st : St) (a i : PyExpr) : IdxM Unit :=
  match arrLen cx.env st.arrs a with
  | some n =>
    match (exprBnd cx.env st.bs i).ub with
    | some u => if u ≤ n then pure () else .error (i.pos, [arrName a, toString n])
    | none => .error (i.pos, [arrName a, toString n])
  | none => .error (i.pos, [arrName a])

mutual

/-- The index obligations of an expression and the analyses of its calls. -/
def walkE (cx : Cx) (st : St) : PyExpr → IdxM Unit
  | .name .. | .const .. => pure ()
  | .binOp _ l _ r => do walkE cx st l; walkE cx st r
  | .unaryOp _ _ e => walkE cx st e
  | .boolOp _ _ vs => walkEs cx st vs
  | .compare _ l _ cs => do walkE cx st l; walkEs cx st cs
  | .ifExp _ c t e => do
    walkE cx st c
    walkE cx { st with bs := refine cx.env st.bs c true } t
    walkE cx { st with bs := refine cx.env st.bs c false } e
  | .call _ func args _ => do
    walkEs cx st args
    match func with
    | .attribute _ recv m => do
      walkE cx st recv
      match m, args with
      | "set", i :: _ => oblig cx st recv i
      | _, _ => pure ()
    | .name _ f => cx.call f (args.map (exprBnd cx.env st.bs))
    | _ => pure ()
  | .attribute _ e _ => walkE cx st e
  | .subscript _ a i => do walkE cx st a; walkE cx st i; oblig cx st a i
  | .tuple _ es => walkEs cx st es

/-- The index obligations of a list of expressions. -/
def walkEs (cx : Cx) (st : St) : List PyExpr → IdxM Unit
  | [] => pure ()
  | e :: es => do walkE cx st e; walkEs cx st es

end

/-! ## Statements -/

mutual

/-- The names a statement assigns. -/
def assignedS : PyStmt → List String
  | .assign _ ts _ => ts.filterMap fun | .name _ x => some x | _ => none
  | .annAssign _ (.name _ x) _ _ _ => [x]
  | .forStmt _ _ _ body orelse => assignedSs body ++ assignedSs orelse
  | .ifStmt _ _ body orelse => assignedSs body ++ assignedSs orelse
  | _ => []

/-- The names a statement list assigns. -/
def assignedSs : List PyStmt → List String
  | [] => []
  | s :: ss => assignedS s ++ assignedSs ss

end

/-- `range(hi)` or `range(lo, hi)`: the optional lower bound and the upper bound. -/
def rangeOf : PyExpr → Option (Option PyExpr × PyExpr)
  | .call _ (.name _ "range") [hi] [] => some (none, hi)
  | .call _ (.name _ "range") [lo, hi] [] => some (some lo, hi)
  | _ => none

/-- The range of a loop iterator, `range(...)` or `reversed(range(...))`. -/
def loopRange : PyExpr → Option (Option PyExpr × PyExpr)
  | .call _ (.name _ "reversed") [r] [] => rangeOf r
  | e => rangeOf e

/-- The bound of a loop variable: below the upper bound of the range when it has a known
value, at least `1` when the lower bound is. -/
def loopVarBnd (env : ModEnv) (σ : Bnds) (iter : PyExpr) : Bnd :=
  match loopRange iter with
  | some (lo, hi) =>
    let lb := match lo with
      | some l => (exprBnd env σ l).lb
      | none => 0
    ⟨if 1 ≤ lb then 1 else 0, (exprBnd env σ hi).exact?, [], .lin⟩
  | none => top

/-- The bounds with each name of `xs` bound to `f x`. -/
def setMany (xs : List String) (f : String → Bnd) (σ : Bnds) : Bnds :=
  xs.foldl (fun σ x => setB x (f x) σ) σ

/-- The loop head of the names `xs` rebound by a loop body `body`, from the head `h`: the
widened join of the head and the bounds after the body, until it is stable; within `fuel`
rounds, and with no bound on `xs` when they are spent. -/
def loopFix (env : ModEnv) (thr : List Nat) (xs : List String) (body : Bnds → Bnds) :
    Nat → Bnds → Bnds
  | 0, h => setMany xs (fun _ => top) h
  | n + 1, h =>
    let out := body h
    let h' := setMany xs (fun x => ((nameBnd env h x).join (nameBnd env out x)).widen thr) h
    if xs.all (fun x => nameBnd env h' x == nameBnd env h x) then h
    else loopFix env thr xs body n h'

/-- The join of the bounds `a` and `b` of two arms on the names of `σ`. -/
def joinBs (env : ModEnv) (σ a b : Bnds) : Bnds :=
  σ.map fun p => (p.1, (nameBnd env a p.1).join (nameBnd env b p.1))

/-- The state after `x = v`. -/
def bindSt (env : ModEnv) (st : St) (x : String) (v : PyExpr) (len : Option Nat) : St where
  bs := setB x (exprBnd env st.bs v) st.bs
  arrs := match len with
    | some n => (x, n) :: st.arrs
    | none => st.arrs

/-- The array length of an annotation. -/
def annLen (env : ModEnv) (ann : PyExpr) : Option Nat :=
  match parseAnn env ann with
  | .ok (.array _ n) => some n
  | _ => none

mutual

/-- The state after a statement, `none` after a `return`; with `chk`, the index obligations
of the statement are checked and its calls analysed. A loop's bounds are its head
(`loopFix`), whose iterations do not check; the body is checked once from the head. -/
def walkS (cx : Cx) (chk : Bool) (st : St) : PyStmt → IdxM (Option St)
  | .assign _ [.name _ x] v => do
    if chk then walkE cx st v
    pure (some (bindSt cx.env st x v (arrLen cx.env st.arrs v)))
  | .annAssign _ (.name _ x) ann (some v) _ => do
    if chk then walkE cx st v
    pure (some (bindSt cx.env st x v (annLen cx.env ann)))
  | .forStmt _ (.name _ i) iter body _ => do
    if chk then walkE cx st iter
    let xs := (assignedSs body).filter fun x => (st.bs.lookup x).isSome
    let bi := loopVarBnd cx.env st.bs iter
    let run : Bnds → Bnds := fun h =>
      match walkSs cx false { st with bs := setB i bi h } body with
      | .ok (some st') => st'.bs
      | _ => h
    let h₀ := setMany xs (fun x => (nameBnd cx.env st.bs x).widen cx.thr) st.bs
    let h := loopFix cx.env cx.thr xs run ((cx.thr.length + 3) * (xs.length + 1)) h₀
    if chk then
      let _ ← walkSs cx true { st with bs := setB i bi h } body
    pure (some { st with bs := h })
  | .ifStmt _ c body orelse => do
    if chk then walkE cx st c
    let a ← walkSs cx chk { st with bs := refine cx.env st.bs c true } body
    let b ← walkSs cx chk { st with bs := refine cx.env st.bs c false } orelse
    let xs := (assignedSs body ++ assignedSs orelse).filter fun x => (st.bs.lookup x).isSome
    pure <| match a, b with
      | some a, some b =>
        if keepsSs cx.env body || keepsSs cx.env orelse then
          some { st with bs := joinBs cx.env st.bs a.bs b.bs }
        else some { st with bs := setMany xs (fun _ => top) st.bs }
      | some a, none => some a
      | none, some b => some b
      | none, none => none
  | .ret _ v => do
    if chk then
      match v with
      | some e => walkE cx st e
      | none => pure ()
    pure none
  | .expr _ v => do
    if chk then walkE cx st v
    pure (some st)
  | _ => pure (some st)

/-- The state after a statement list, `none` after a `return`. -/
def walkSs (cx : Cx) (chk : Bool) (st : St) : List PyStmt → IdxM (Option St)
  | [] => pure (some st)
  | s :: ss => do
    match ← walkS cx chk st s with
    | some st' => walkSs cx chk st' ss
    | none => pure none

end

/-! ## Functions and modules -/

mutual

/-- The constants of an expression: its `int` literals and module constants. -/
def constsE (env : ModEnv) : PyExpr → List Nat
  | .name p x => (litNat env (.name p x)).toList
  | .const p c => (litNat env (.const p c)).toList
  | .binOp _ l _ r => constsE env l ++ constsE env r
  | .unaryOp _ _ e => constsE env e
  | .boolOp _ _ vs => constsEs env vs
  | .compare _ l _ cs => constsE env l ++ constsEs env cs
  | .ifExp _ c t e => constsE env c ++ constsE env t ++ constsE env e
  | .call _ f args _ => constsE env f ++ constsEs env args
  | .attribute _ e _ => constsE env e
  | .subscript _ a i => constsE env a ++ constsE env i
  | .tuple _ es => constsEs env es

/-- The constants of a list of expressions. -/
def constsEs (env : ModEnv) : List PyExpr → List Nat
  | [] => []
  | e :: es => constsE env e ++ constsEs env es

end

mutual

/-- The constants of a statement. -/
def constsS (env : ModEnv) : PyStmt → List Nat
  | .assign _ ts v => constsEs env ts ++ constsE env v
  | .annAssign _ t a v _ =>
    constsE env t ++ constsE env a ++ (match v with | some v => constsE env v | none => [])
  | .forStmt _ t i body orelse =>
    constsE env t ++ constsE env i ++ constsSs env body ++ constsSs env orelse
  | .ifStmt _ c body orelse => constsE env c ++ constsSs env body ++ constsSs env orelse
  | .ret _ v => match v with | some v => constsE env v | none => []
  | .expr _ v => constsE env v
  | _ => []

/-- The constants of a statement list. -/
def constsSs (env : ModEnv) : List PyStmt → List Nat
  | [] => []
  | s :: ss => constsS env s ++ constsSs env ss

end

/-- The widening thresholds of a function: the successors of the constants of its body and of
the lengths of its array parameters. An exclusive bound `c + 1` is the inclusive bound `c` of
a candidate of `idxAnnot`, whose bounds are constants and array lengths. -/
def thrOf (f : CheckedFn) : List Nat :=
  let cs := constsSs f.env f.body ++ f.sig.params.filterMap fun p =>
    match p.2 with
    | .array _ n => some n
    | _ => none
  (cs.map (· + 1)).eraseDups

/-- The state at the entry of a function: its parameters bound to the bounds of the
arguments, and its array parameters with their lengths. -/
def initSt (sig : FnSig) (args : List Bnd) : St where
  bs := (sig.params.zip args).map fun pb => (pb.1.1, pb.2)
  arrs := sig.params.filterMap fun p =>
    match p.2 with
    | .array _ n => some (p.1, n)
    | _ => none

/-- The analysis of the body of `f` under the bounds `args` of its parameters, with calls of
the functions `fns` analysed at each call, within `fuel` nested calls. A linked function is
not analysed. -/
def analyze (fns : List CheckedFn) : Nat → CheckedFn → List Bnd → IdxM Unit
  | 0, f, _ => .error (f.pos, [f.name])
  | n + 1, f, args =>
    if f.sig.linked.isSome then pure ()
    else do
      let cx : Cx :=
        { env := f.env, thr := thrOf f,
          call := fun g bs =>
            match fns.find? (·.name == g) with
            | some h => analyze fns n h bs
            | none => pure () }
      let _ ← walkSs cx true (initSt f.sig args) f.body
      pure ()

/-- The index analysis of the checked functions `fns`: every entry, with no bound on its
parameters, and the functions it calls, within `maxCallDepth` nested calls. -/
def idxCheck (fns : List CheckedFn) : IdxM Unit :=
  fns.forM fun f =>
    if f.sig.entry then analyze fns (maxCallDepth + 1) f (f.sig.params.map fun _ => top)
    else pure ()

end IdxBound

end Hax.Py
