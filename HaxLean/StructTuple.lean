/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.TExpr
public import HaxLean.Semantics
public import HaxLean.Phase.FlattenLetFoldReturn

/-!
# Structs as tuples of their fields

A Rust struct reaches the typed AST in three forms: a construction `.app "S" fs`, a field
read `.app ".f" [s]` or `.app "S.f" [s]`, and a field update
`.app "struct_update#S#i#n" [s, v]`. `Value` has no struct constructor, so the semantics of
these heads is the table `structBi`, which reads a struct as the tuple of its fields.
The rewrite `tStructToTuple` replaces each head by tuple syntax: a construction becomes a
`.tuple`, a field read a `.proj`, and an update a `let` of the pair `(s, v)` followed by the
tuple of the fields of `s` with the `i`-th replaced by `v`. Struct types `.adt S _` become
tuple types of the field types.

## Main definitions

* `StructFieldTys` — struct name to its fields with their types, in declaration order
* `structHead?` — the classification of an application head as a struct head
* `structBi` — the struct heads over a builtin table, structs read as tuples
* `tStructToTuple` — the rewrite of struct heads and struct types into tuples
* `StructOk` — the side condition: the reserved name is not read, struct heads have their arity

## Main results

* `denote_tStructToTuple` — the rewrite refines `denote`: when the struct term's outcome is
  not an error, the rewritten term has the same outcome, from and to environments that agree
  except at the reserved name bound by the update's `let`.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax

/-! ## Struct layout and head classification -/

/-- Field layout of the structs of an export: struct name to its fields with their types, in
    declaration order. -/
abbrev StructFieldTys := List (String × List (String × ImpType))

/-- The field names of a struct layout. -/
def StructFieldTys.names (sf : StructFieldTys) : StructFieldNames :=
  sf.map fun p => (p.1, p.2.map Prod.fst)

/-- The role of an application head on structs. -/
inductive StructHead where
  /-- Construction of a struct with `n` fields. -/
  | ctor (n : Nat)
  /-- Read of field `i` of a struct with `n` fields. -/
  | field (i n : Nat)
  /-- Update of field `i` of a struct with `n` fields. -/
  | update (i n : Nat)
  deriving Inhabited, DecidableEq, Repr

/-- The struct role of the application head `f`: a struct name of `sf` constructs that
    struct; `struct_update#S#i#n` updates field `i` when `S` has `n` fields and `i < n`;
    `.g` reads field `g` of the unique struct declaring it, and `S.g` reads field `g` of `S`
    (`resolveStructField`). Every other head has no struct role. -/
def structHead? (sf : StructFieldTys) (f : String) : Option StructHead :=
  match sf.lookup f with
  | some fs => some (.ctor fs.length)
  | none =>
    match parseStructUpdateHead f with
    | some (s, i, n) =>
      match sf.lookup s with
      | some fs => if fs.length = n ∧ i < n then some (.update i n) else none
      | none => none
    | none =>
      match f.splitOn "." with
      | ["", g] => (resolveStructField sf.names g).map fun r => .field r.2.1 r.2.2
      | [_, _] => (resolveStructField sf.names f).map fun r => .field r.2.1 r.2.2
      | _ => none

/-- The struct heads over the builtin table `bi`, a struct read as the tuple of its fields:
    a construction of `n` fields builds the tuple of its `n` arguments; a field read projects
    a tuple of `n` values; an update replaces the `i`-th value of a tuple of `n` values. Every
    head without a struct role is answered by `bi`. -/
def structBi (sf : StructFieldTys) (bi : Builtins) : Builtins := fun f args =>
  match structHead? sf f with
  | some (.ctor n) => if args.length = n then some (.tuple args) else none
  | some (.field i n) =>
    match args with
    | [.tuple vs] => if vs.length = n then vs[i]? else none
    | _ => none
  | some (.update i n) =>
    match args with
    | [.tuple vs, v] => if vs.length = n then some (.tuple (vs.set i v)) else none
    | _ => none
  | none => bi f args

/-! ## Types -/

/-- The fields of the struct a type name denotes, by its last `::` segment. -/
def StructFieldTys.fieldsOfName (sf : StructFieldTys) (n : String) :
    Option (List (String × ImpType)) :=
  sf.lookup (((n.splitOn "::").getLast?).getD n)

/-- One expansion pass over a type: a struct type `.adt S _` of `sf` becomes the tuple of its
    field types, each passed to `exp`. -/
def tyStructStep (sf : StructFieldTys) (exp : ImpType → ImpType) : ImpType → ImpType
  | .adt n args =>
    match sf.fieldsOfName n with
    | some fs => .tuple (fs.map fun p => exp p.2)
    | none => .adt n (goList args)
  | .tuple es => .tuple (goList es)
  | .option a => .option (tyStructStep sf exp a)
  | .result a b => .result (tyStructStep sf exp a) (tyStructStep sf exp b)
  | .controlFlow a b => .controlFlow (tyStructStep sf exp a) (tyStructStep sf exp b)
  | .fn ps r => .fn (goList ps) (tyStructStep sf exp r)
  | .ref a m => .ref (tyStructStep sf exp a) m
  | .slice a => .slice (tyStructStep sf exp a)
  | .array a k => .array (tyStructStep sf exp a) k
  | ty => ty
where
  goList : List ImpType → List ImpType
    | [] => []
    | a :: as => tyStructStep sf exp a :: goList as

/-- Struct types as tuple types, nested structs expanded to depth `k`. -/
def tyStructToTuple (sf : StructFieldTys) : Nat → ImpType → ImpType
  | 0, ty => ty
  | k + 1, ty => tyStructStep sf (tyStructToTuple sf k) ty

/-! ## The rewrite -/

/-- The type of component `j` of a tuple type, `unknown` otherwise. -/
def tupleCompTy (ty : ImpType) (j : Nat) : ImpType :=
  match ty with
  | .tuple tys => tys.getD j .unknown
  | _ => .unknown

/-- The fields of an updated struct, read from the variable `t` bound to the pair `(s, v)`:
    component `i` is `t.1`, every other component `j < n` is `t.0.j`. -/
def updFields (t : String) (i n : Nat) (sty vty : ImpType) : List TExpr :=
  let tv : TExpr := .mk (.var t) (.tuple [sty, vty])
  (List.range n).map fun j =>
    if j = i then .mk (.proj tv 1) vty
    else .mk (.proj (.mk (.proj tv 0) sty) j) (tupleCompTy sty j)

/-- The tuple form of an application of the head `f` to the rewritten arguments `args`, when
    `f` has a struct role and `args` its arity: a construction is the tuple of its arguments;
    a field read `S.g s` is the projection `s.i`; an update of `s` by `v` is
    `let t := (s, v); (t.0.0, …, t.1, …, t.0.(n-1))`. -/
def structApp (sf : StructFieldTys) (t : String) (f : String) (args : List TExpr) :
    Option TExprKind :=
  match structHead? sf f, args with
  | some (.ctor _), _ => some (.tuple args)
  | some (.field i _), [s] => some (.proj s i)
  | some (.update i n), [s, v] =>
    some (.letBind t (.mk (.tuple [s, v]) (.tuple [s.ty, v.ty]))
      (.mk (.tuple (updFields t i n s.ty v.ty)) s.ty))
  | _, _ => none

/-- Structs as tuples: every application with a struct role becomes tuple syntax
    (`structApp`), `t` names the pair an update binds, and every type annotation has its
    struct types expanded to depth `sf.length` (`tyStructToTuple`). -/
def tStructToTuple (sf : StructFieldTys) (t : String) : TExpr → TExpr
  | .mk k ty => .mk (goKind k) (tyStructToTuple sf sf.length ty)
where
  goKind : TExprKind → TExprKind
    | .lit v => .lit v
    | .var n => .var n
    | .letBind n v b => .letBind n (tStructToTuple sf t v) (tStructToTuple sf t b)
    | .lam ps b => .lam ps (tStructToTuple sf t b)
    | .app f args => (structApp sf t f (goList args)).getD (.app f (goList args))
    | .tuple es => .tuple (goList es)
    | .proj e i => .proj (tStructToTuple sf t e) i
    | .ifThenElse c a b =>
      .ifThenElse (tStructToTuple sf t c) (tStructToTuple sf t a) (tStructToTuple sf t b)
    | .match_ s arms => .match_ (tStructToTuple sf t s) (goArms arms)
    | .unitVal => .unitVal
    | .seq a b => .seq (tStructToTuple sf t a) (tStructToTuple sf t b)
    | .borrow e => .borrow (tStructToTuple sf t e)
    | .deref e => .deref (tStructToTuple sf t e)
    | .assign n e => .assign n (tStructToTuple sf t e)
    | .forLoop v lo hi b =>
      .forLoop v (tStructToTuple sf t lo) (tStructToTuple sf t hi) (tStructToTuple sf t b)
    | .forLoopRev v lo hi b =>
      .forLoopRev v (tStructToTuple sf t lo) (tStructToTuple sf t hi) (tStructToTuple sf t b)
    | .whileLoop c b => .whileLoop (tStructToTuple sf t c) (tStructToTuple sf t b)
    | .break_ none => .break_ none
    | .break_ (some e) => .break_ (some (tStructToTuple sf t e))
    | .continue_ => .continue_
    | .earlyReturn e => .earlyReturn (tStructToTuple sf t e)
    | .questionMark e => .questionMark (tStructToTuple sf t e)
    | .forFold v lo hi b =>
      .forFold v (tStructToTuple sf t lo) (tStructToTuple sf t hi) (tStructToTuple sf t b)
    | .forFoldRev v lo hi b =>
      .forFoldRev v (tStructToTuple sf t lo) (tStructToTuple sf t hi) (tStructToTuple sf t b)
    | .whileFold c b => .whileFold (tStructToTuple sf t c) (tStructToTuple sf t b)
    | .forFoldReturn v lo hi b =>
      .forFoldReturn v (tStructToTuple sf t lo) (tStructToTuple sf t hi)
        (tStructToTuple sf t b)
    | .forFoldRevReturn v lo hi b =>
      .forFoldRevReturn v (tStructToTuple sf t lo) (tStructToTuple sf t hi)
        (tStructToTuple sf t b)
    | .whileFoldReturn c b => .whileFoldReturn (tStructToTuple sf t c) (tStructToTuple sf t b)
    | .cfBreak e => .cfBreak (tStructToTuple sf t e)
    | .cfContinue e => .cfContinue (tStructToTuple sf t e)
    | .cfBreakContinue e => .cfBreakContinue (tStructToTuple sf t e)
    | .ann e => .ann (tStructToTuple sf t e)
    | .namedProj n e =>
      (structApp sf t ".0" [tStructToTuple sf t e]).getD (.namedProj n (tStructToTuple sf t e))
  goList : List TExpr → List TExpr
    | [] => []
    | e :: es => tStructToTuple sf t e :: goList es
  goArms : List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest => (p, tStructToTuple sf t e) :: goArms rest

/-! ## The side condition -/

/-- Every application with a struct role in `e` has that role's arity: one argument for a
    field read, two for an update. -/
def structArityOk (sf : StructFieldTys) : ImpExpr → Bool
  | .app f args =>
    (match structHead? sf f with
      | some (.field _ _) => args.length == 1
      | some (.update _ _) => args.length == 2
      | _ => true) && allExpr args
  | .letBind _ v b => structArityOk sf v && structArityOk sf b
  | .lam _ b => structArityOk sf b
  | .tuple es => allExpr es
  | .proj e _ => structArityOk sf e
  | .ifThenElse c a b => structArityOk sf c && structArityOk sf a && structArityOk sf b
  | .match_ s arms => structArityOk sf s && allArms arms
  | .seq a b => structArityOk sf a && structArityOk sf b
  | .borrow e => structArityOk sf e
  | .deref e => structArityOk sf e
  | .assign _ e => structArityOk sf e
  | .forLoop _ lo hi b => structArityOk sf lo && structArityOk sf hi && structArityOk sf b
  | .forLoopRev _ lo hi b => structArityOk sf lo && structArityOk sf hi && structArityOk sf b
  | .whileLoop c b => structArityOk sf c && structArityOk sf b
  | .break_ (some e) => structArityOk sf e
  | .earlyReturn e => structArityOk sf e
  | .questionMark e => structArityOk sf e
  | .forFold _ lo hi b => structArityOk sf lo && structArityOk sf hi && structArityOk sf b
  | .forFoldRev _ lo hi b => structArityOk sf lo && structArityOk sf hi && structArityOk sf b
  | .whileFold c b => structArityOk sf c && structArityOk sf b
  | .forFoldReturn _ lo hi b =>
    structArityOk sf lo && structArityOk sf hi && structArityOk sf b
  | .forFoldRevReturn _ lo hi b =>
    structArityOk sf lo && structArityOk sf hi && structArityOk sf b
  | .whileFoldReturn c b => structArityOk sf c && structArityOk sf b
  | .cfBreak e => structArityOk sf e
  | .cfContinue e => structArityOk sf e
  | .cfBreakContinue e => structArityOk sf e
  | .typeAscription e _ => structArityOk sf e
  | _ => true
where
  allExpr : List ImpExpr → Bool
    | [] => true
    | e :: es => structArityOk sf e && allExpr es
  allArms : List (ImpPat × ImpExpr) → Bool
    | [] => true
    | (_, e) :: rest => structArityOk sf e && allArms rest

/-- The side condition of `tStructToTuple sf t e`: the reserved name `t` is never read in `e`
    (`noVarRef`), and every application with a struct role has that role's arity
    (`structArityOk`). -/
def StructOk (sf : StructFieldTys) (t : String) (e : TExpr) : Prop :=
  noVarRef t e.erase = true ∧ structArityOk sf e.erase = true

/-! ## Refinement up to one slot -/

namespace StructTuple

/-- `o` is an error outcome. -/
def isErr : Outcome → Bool
  | .err _ => true
  | _ => false

/-- `m₂` refines `m₁` up to the slot `t`, `bad` marking failed results: from environments that
    agree except at `t`, whenever `m₁`'s result is not `bad`, `m₂` has the same result and the
    final environments agree except at `t`. -/
def Refines {α : Type} (bad : α → Bool) (t : String) (m₁ m₂ : StateM Env α) : Prop :=
  ∀ s₁ s₂, Env.AgreeExcept t s₁ s₂ → bad (m₁ s₁).1 = false →
    (m₂ s₂).1 = (m₁ s₁).1 ∧ Env.AgreeExcept t (m₁ s₁).2 (m₂ s₂).2

theorem Refines.pure {α : Type} {bad : α → Bool} {t : String} (a : α) :
    Refines bad t (Pure.pure a) (Pure.pure a) :=
  fun _ _ hs _ => ⟨rfl, hs⟩

theorem Refines.of_bad {α : Type} {bad : α → Bool} {t : String} {m₁ m₂ : StateM Env α}
    (h : ∀ s, bad (m₁ s).1 = true) : Refines bad t m₁ m₂ := by
  grind only [Refines]

theorem Refines.bind {α β : Type} {bad₁ : α → Bool} {bad₂ : β → Bool} {t : String}
    {m₁ m₂ : StateM Env α} {f₁ f₂ : α → StateM Env β}
    (hm : Refines bad₁ t m₁ m₂)
    (hstrict : ∀ a s, bad₁ a = true → bad₂ (f₁ a s).1 = true)
    (hf : ∀ a, bad₁ a = false → Refines bad₂ t (f₁ a) (f₂ a)) :
    Refines bad₂ t (m₁ >>= f₁) (m₂ >>= f₂) := by
  intro s₁ s₂ hs hb
  rw [stateM_bind_apply] at hb ⊢
  rw [stateM_bind_apply]
  have ha : bad₁ (m₁ s₁).1 = false := by
    cases h : bad₁ (m₁ s₁).1
    · rfl
    · rw [hstrict _ _ h] at hb; exact absurd hb (by simp)
  obtain ⟨ho, hst⟩ := hm s₁ s₂ hs ha
  rw [ho]
  exact hf _ ha _ _ hst hb

theorem Refines.modify_extend {t : String} (k : String) (w : Value) :
    Refines (fun _ => false) t (modify (Env.extend · k w)) (modify (Env.extend · k w)) :=
  fun _ _ hs _ => ⟨rfl, hs.extend k w⟩

theorem Refines.var (bi₁ bi₂ : Builtins) (fuel : Nat) {t m : String} (h : m ≠ t) :
    Refines isErr t (denote bi₁ fuel (.var m)) (denote bi₂ fuel (.var m)) := by
  intro s₁ s₂ hs _
  simp only [denote, stateM_bind_apply, stateM_get_apply]
  rw [hs m h]
  cases s₂ m <;> exact ⟨rfl, hs⟩

theorem denoteArgs_length (bi : Builtins) (fuel : Nat) :
    ∀ (es : List ImpExpr) (s : Env) (vals : List Value),
      (denoteArgs bi fuel es s).1 = some vals → vals.length = es.length := by
  intro es
  induction es with
  | nil =>
    intro s vals h
    simp only [denoteArgs, stateM_pure_apply, Option.some.injEq] at h
    simp [← h]
  | cons e es ih =>
    intro s vals h
    simp only [denoteArgs, stateM_bind_apply] at h
    rcases hr : denote bi fuel e s with ⟨o, s'⟩
    rw [hr] at h
    rcases o with v | v | v | _ | m
    · simp only [stateM_bind_apply, stateM_pure_apply, Option.map_eq_some_iff] at h
      obtain ⟨rest, hrest, rfl⟩ := h
      simp [ih s' rest hrest]
    all_goals simp [stateM_pure_apply] at h

theorem denoteArgs_refines (bi₁ bi₂ : Builtins) (t : String) (fuel : Nat) {β : Type}
    (F G : β → ImpExpr) :
    ∀ (xs : List β),
      (∀ x ∈ xs, Refines isErr t (denote bi₁ fuel (F x)) (denote bi₂ fuel (G x))) →
      Refines Option.isNone t (denoteArgs bi₁ fuel (xs.map F))
        (denoteArgs bi₂ fuel (xs.map G)) := by
  intro xs
  induction xs with
  | nil => intro _; simp only [List.map_nil, denoteArgs]; exact Refines.pure _
  | cons x xs ih =>
    intro hall
    simp only [List.map_cons, denoteArgs]
    refine Refines.bind (hall x (List.mem_cons_self ..)) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr; cases r <;> (try exact Refines.pure _)
      refine Refines.bind (ih fun y hy => hall y (List.mem_cons_of_mem _ hy)) ?_ ?_
      · intro r s hr; cases r <;> simp_all [stateM_pure_apply]
      · intro r hr; exact Refines.pure _

theorem denoteMatchArms_refines (bi₁ bi₂ : Builtins) (t : String) (fuel : Nat) (v : Value)
    {β : Type} (F G : β → ImpExpr) :
    ∀ (arms : List (ImpPat × β)),
      (∀ pa ∈ arms, Refines isErr t (denote bi₁ fuel (F pa.2)) (denote bi₂ fuel (G pa.2))) →
      Refines isErr t (denoteMatchArms bi₁ fuel v (arms.map fun pa => (pa.1, F pa.2)))
        (denoteMatchArms bi₂ fuel v (arms.map fun pa => (pa.1, G pa.2))) := by
  intro arms
  induction arms with
  | nil => intro _; simp only [List.map_nil, denoteMatchArms]; exact Refines.pure _
  | cons pa rest ih =>
    obtain ⟨pat, b⟩ := pa
    intro hall s₁ s₂ hs hb
    simp only [List.map_cons, denoteMatchArms, stateM_bind_apply, stateM_get_apply] at hb ⊢
    have hmp := matchPat_agree t pat v s₁ s₂ hs
    cases hp1 : matchPat pat v s₁ <;> cases hp2 : matchPat pat v s₂ <;>
      simp only [hp1, hp2, OptAgree] at hmp hb ⊢
    · exact ih (fun pa' h' => hall pa' (List.mem_cons_of_mem _ h')) s₁ s₂ hs hb
    · simp only [stateM_bind_apply, stateM_set_apply] at hb ⊢
      exact hall (pat, b) (List.mem_cons_self ..) _ _ hmp hb

theorem denoteForLoop_refines (bi₁ bi₂ : Builtins) (t var : String) (body body' : ImpExpr)
    (hb : ∀ fuel, Refines isErr t (denote bi₁ fuel body) (denote bi₂ fuel body')) :
    ∀ fuel lo hi, Refines isErr t (denoteForLoop bi₁ fuel var lo hi body)
      (denoteForLoop bi₂ fuel var lo hi body') := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi
    unfold denoteForLoop
    split
    · exact Refines.pure _
    · split
      · exact Refines.pure _
      · exact absurd rfl ‹_›
  | succ k ih =>
    intro lo hi
    unfold denoteForLoop
    split
    · exact Refines.pure _
    · split
      · exact Refines.pure _
      · refine Refines.bind (Refines.modify_extend var (.int lo)) (by simp) (fun _ _ => ?_)
        refine Refines.bind (hb (k + 1)) ?_ ?_
        · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
        · intro rb _
          cases rb <;> first
            | (simp only [Nat.add_sub_cancel]; exact ih (lo + 1) hi)
            | exact Refines.pure _

theorem denoteForLoopRev_refines (bi₁ bi₂ : Builtins) (t var : String) (body body' : ImpExpr)
    (hb : ∀ fuel, Refines isErr t (denote bi₁ fuel body) (denote bi₂ fuel body')) :
    ∀ fuel lo hi, Refines isErr t (denoteForLoopRev bi₁ fuel var lo hi body)
      (denoteForLoopRev bi₂ fuel var lo hi body') := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi
    unfold denoteForLoopRev
    split
    · exact Refines.pure _
    · split
      · exact Refines.pure _
      · exact absurd rfl ‹_›
  | succ k ih =>
    intro lo hi
    unfold denoteForLoopRev
    split
    · exact Refines.pure _
    · split
      · exact Refines.pure _
      · refine Refines.bind (Refines.modify_extend var (.int (hi - 1))) (by simp) (fun _ _ => ?_)
        refine Refines.bind (hb (k + 1)) ?_ ?_
        · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
        · intro rb _
          cases rb <;> first
            | (simp only [Nat.add_sub_cancel]; exact ih lo (hi - 1))
            | exact Refines.pure _

theorem denoteWhile_refines (bi₁ bi₂ : Builtins) (t : String) (cond cond' body body' : ImpExpr)
    (hc : ∀ fuel, Refines isErr t (denote bi₁ fuel cond) (denote bi₂ fuel cond'))
    (hb : ∀ fuel, Refines isErr t (denote bi₁ fuel body) (denote bi₂ fuel body')) :
    ∀ fuel, Refines isErr t (denoteWhile bi₁ fuel cond body)
      (denoteWhile bi₂ fuel cond' body') := by
  intro fuel
  induction fuel with
  | zero =>
    unfold denoteWhile
    split
    · exact Refines.pure _
    · exact absurd rfl ‹_›
  | succ k ih =>
    unfold denoteWhile
    split
    · exact Refines.pure _
    · refine Refines.bind (hc (k + 1)) ?_ ?_
      · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
      · intro rc hrc
        rcases rc with v | v | v | _ | m
        · cases v <;> (try exact Refines.pure _)
          rename_i bv
          cases bv
          · exact Refines.pure _
          · refine Refines.bind (hb (k + 1)) ?_ ?_
            · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
            · intro rb _
              cases rb <;> first
                | (simp only [Nat.add_sub_cancel]; exact ih)
                | exact Refines.pure _
        all_goals exact Refines.pure _

/-- A list of expressions each evaluating to a value without changing the environment
    evaluates to the list of those values. -/
theorem denoteArgs_map_val (bi : Builtins) (fuel : Nat) (s : Env) {β : Type}
    (g : β → ImpExpr) (hv : β → Value) :
    ∀ (l : List β), (∀ j ∈ l, denote bi fuel (g j) s = (.val (hv j), s)) →
      denoteArgs bi fuel (l.map g) s = (some (l.map hv), s) := by
  intro l
  induction l with
  | nil => intro _; simp only [List.map_nil, denoteArgs, stateM_pure_apply]
  | cons j l ih =>
    intro h
    simp only [List.map_cons, denoteArgs, stateM_bind_apply, h j (List.mem_cons_self ..),
      ih (fun j' hj' => h j' (List.mem_cons_of_mem _ hj')), stateM_pure_apply, Option.map_some]

/-- The fields of an update evaluate, without changing the environment, to the fields of the
    struct with the `i`-th replaced. -/
theorem denoteArgs_updFields (bi : Builtins) (fuel : Nat) (t : String) (i n : Nat)
    (sty vty : ImpType) (vs : List Value) (w : Value) (s : Env)
    (hs : s t = some (.tuple [.tuple vs, w])) (hn : vs.length = n) :
    denoteArgs bi fuel ((updFields t i n sty vty).map TExpr.erase) s =
      (some (vs.set i w), s) := by
  unfold updFields
  rw [List.map_map,
    denoteArgs_map_val bi fuel s _ (fun j => if j = i then w else vs.getD j .unit)]
  · refine Prod.ext (congrArg some ?_) rfl
    apply List.ext_getElem
    · simp [hn]
    · intro k h1 h2
      simp only [List.getElem_map, List.getElem_range, List.getElem_set]
      grind only [= List.length_set, = List.getD_eq_getElem?_getD, = getElem?_pos,
        = Option.getD_some]
  · intro j hj
    rw [List.mem_range] at hj
    show denote bi fuel (TExpr.erase (if j = i then _ else _)) s = _
    have hjv : j < vs.length := hn ▸ hj
    by_cases hji : j = i
    · simp only [hji, ↓reduceIte, TExpr.erase, denote, stateM_bind_apply, stateM_get_apply, hs,
        Value.projIdx, stateM_pure_apply]
      rfl
    · simp only [hji, ↓reduceIte, TExpr.erase, denote, stateM_bind_apply, stateM_get_apply, hs,
        Value.projIdx, stateM_pure_apply]
      simp [List.getElem?_eq_getElem hjv, stateM_pure_apply, List.getD_eq_getElem?_getD]

end StructTuple

open StructTuple

@[simp] theorem tStructToTuple_goList (sf : StructFieldTys) (t : String) (es : List TExpr) :
    tStructToTuple.goList sf t es = es.map (tStructToTuple sf t) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [tStructToTuple.goList, ih, List.map_cons]

@[simp] theorem tStructToTuple_goArms (sf : StructFieldTys) (t : String)
    (arms : List (ImpPat × TExpr)) :
    tStructToTuple.goArms sf t arms = arms.map fun pa => (pa.1, tStructToTuple sf t pa.2) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp only [tStructToTuple.goArms, ih, List.map_cons]

/-- An application left in place refines itself when `structBi` answers its head as `bi` does,
    or not at all, on every argument list of its arity. -/
theorem denote_app_fallback (sf : StructFieldTys) (bi : Builtins) (t f : String)
    (args : List TExpr)
    (ih : ∀ a ∈ args, ∀ fuel, Refines isErr t (denote (structBi sf bi) fuel a.erase)
      (denote bi fuel (tStructToTuple sf t a).erase))
    (hfb : ∀ vals : List Value, vals.length = args.length →
      structBi sf bi f vals = bi f vals ∨ structBi sf bi f vals = none) (fuel : Nat) :
    Refines isErr t (denote (structBi sf bi) fuel (.app f (args.map TExpr.erase)))
      (denote bi fuel (.app f ((args.map (tStructToTuple sf t)).map TExpr.erase))) := by
  intro s₁ s₂ hs hb
  simp only [denote, List.map_map, stateM_bind_apply] at hb ⊢
  have hA := denoteArgs_refines (structBi sf bi) bi t fuel TExpr.erase
    (TExpr.erase ∘ tStructToTuple sf t) args (fun x hx => ih x hx fuel) s₁ s₂ hs
  cases hr : (denoteArgs (structBi sf bi) fuel (args.map TExpr.erase) s₁).1 with
  | none => rw [hr] at hb; exact absurd hb (by simp [isErr, stateM_pure_apply])
  | some vals =>
    obtain ⟨ho, hst⟩ := hA (by simp [hr])
    rw [hr] at ho hb
    rw [ho]
    have hlen := denoteArgs_length _ fuel _ s₁ vals hr
    rw [List.length_map] at hlen
    rcases hfb vals hlen with he | he
    · simp only [he] at hb ⊢
      cases bi f vals <;> exact ⟨rfl, hst⟩
    · simp only [he] at hb
      exact absurd hb (by simp [isErr, stateM_pure_apply])

/-- An application node refines its rewrite, given that its arguments do. -/
theorem denote_structApp (sf : StructFieldTys) (bi : Builtins) (t f : String)
    (args : List TExpr) (ty : ImpType)
    (ih : ∀ a ∈ args, ∀ fuel, Refines isErr t (denote (structBi sf bi) fuel a.erase)
      (denote bi fuel (tStructToTuple sf t a).erase)) (fuel : Nat) :
    Refines isErr t (denote (structBi sf bi) fuel (.app f (args.map TExpr.erase)))
      (denote bi fuel (TExpr.mk ((structApp sf t f (args.map (tStructToTuple sf t))).getD
        (.app f (args.map (tStructToTuple sf t)))) ty).erase) := by
  have ih' : ∀ x ∈ args, Refines isErr t (denote (structBi sf bi) fuel x.erase)
      (denote bi fuel ((TExpr.erase ∘ tStructToTuple sf t) x)) := fun x hx => ih x hx fuel
  cases hh : structHead? sf f with
  | none =>
    have hs : structApp sf t f (args.map (tStructToTuple sf t)) = none := by
      simp [structApp, hh]
    rw [hs]
    simp only [Option.getD_none, TExpr.erase, TExpr.eraseList_eq]
    exact denote_app_fallback sf bi t f args ih
      (fun vals _ => Or.inl (by simp [structBi, hh])) fuel
  | some hd =>
    cases hd with
    | ctor n =>
      have hs : structApp sf t f (args.map (tStructToTuple sf t)) =
          some (.tuple (args.map (tStructToTuple sf t))) := by
        simp [structApp, hh]
      rw [hs]
      simp only [Option.getD_some, TExpr.erase, TExpr.eraseList_eq, List.map_map, denote]
      refine Refines.bind (denoteArgs_refines _ _ t fuel _ _ args ih') ?_ ?_
      · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
      · intro r hr
        cases r with
        | none => exact Refines.of_bad (fun _ => rfl)
        | some vals =>
          simp only [structBi, hh]
          by_cases hl : vals.length = n
          · simp only [hl, ↓reduceIte]; exact Refines.pure _
          · simp only [hl, ↓reduceIte]; exact Refines.of_bad (fun _ => rfl)
    | field i n =>
      rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · rw [show structApp sf t f (List.map (tStructToTuple sf t) []) = none by
          simp [structApp, hh]]
        simp only [Option.getD_none, TExpr.erase, TExpr.eraseList_eq]
        exact denote_app_fallback sf bi t f [] ih (fun vals hl => Or.inr (by
          rcases vals with _ | ⟨x, _ | ⟨y, _⟩⟩ <;> simp_all [structBi])) fuel
      · rw [show structApp sf t f (List.map (tStructToTuple sf t) [a]) =
            some (.proj (tStructToTuple sf t a) i) by simp [structApp, hh]]
        simp only [Option.getD_some, TExpr.erase, List.map_cons, List.map_nil, denote,
          denoteArgs]
        rw [bind_assoc]
        refine Refines.bind (ih a (List.mem_singleton_self a) fuel) ?_ ?_
        · intro r s hr
          cases r <;> simp_all [isErr, stateM_pure_apply, stateM_bind_apply]
        · intro r hr
          rcases r with v | v | v | _ | m
          · intro s₁ s₂ hs hb
            simp only [stateM_bind_apply, stateM_pure_apply, Option.map_some, structBi, hh]
              at hb ⊢
            cases v with
            | tuple vs =>
              simp only [Value.projIdx]
              by_cases hl : vs.length = n
              · simp only [hl, ↓reduceIte] at hb ⊢
                cases hvi : vs[i]? <;> simp only [hvi] at hb ⊢
                · exact absurd hb (by simp [isErr, stateM_pure_apply])
                · exact ⟨rfl, hs⟩
              · simp only [hl, ↓reduceIte] at hb
                exact absurd hb (by simp [isErr, stateM_pure_apply])
            | _ => exact absurd hb (by simp [isErr, stateM_pure_apply])
          all_goals exact Refines.of_bad (fun _ => rfl)
      · rw [show structApp sf t f (List.map (tStructToTuple sf t) (a :: b :: rest)) = none by
          simp [structApp, hh]]
        simp only [Option.getD_none, TExpr.erase, TExpr.eraseList_eq]
        exact denote_app_fallback sf bi t f _ ih (fun vals hl => Or.inr (by
          rcases vals with _ | ⟨x, _ | ⟨y, _⟩⟩ <;> simp_all [structBi])) fuel
    | update i n =>
      rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
      · rw [show structApp sf t f (List.map (tStructToTuple sf t) []) = none by
          simp [structApp, hh]]
        simp only [Option.getD_none, TExpr.erase, TExpr.eraseList_eq]
        exact denote_app_fallback sf bi t f [] ih (fun vals hl => Or.inr (by
          rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, _⟩⟩⟩ <;> simp_all [structBi])) fuel
      · rw [show structApp sf t f (List.map (tStructToTuple sf t) [a]) = none by
          simp [structApp, hh]]
        simp only [Option.getD_none, TExpr.erase, TExpr.eraseList_eq]
        exact denote_app_fallback sf bi t f [a] ih (fun vals hl => Or.inr (by
          rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, _⟩⟩⟩ <;> simp_all [structBi])) fuel
      · rw [show structApp sf t f (List.map (tStructToTuple sf t) [a, b]) =
            some (.letBind t
              (.mk (.tuple [tStructToTuple sf t a, tStructToTuple sf t b])
                (.tuple [(tStructToTuple sf t a).ty, (tStructToTuple sf t b).ty]))
              (.mk (.tuple (updFields t i n (tStructToTuple sf t a).ty
                (tStructToTuple sf t b).ty)) (tStructToTuple sf t a).ty)) by
          simp [structApp, hh]]
        simp only [Option.getD_some, TExpr.erase, TExpr.eraseList_eq, List.map_cons,
          List.map_nil]
        intro s₁ s₂ hs hb
        have hA := denoteArgs_refines (structBi sf bi) bi t fuel TExpr.erase
          (TExpr.erase ∘ tStructToTuple sf t) [a, b] ih' s₁ s₂ hs
        simp only [denote, stateM_bind_apply, List.map_cons, List.map_nil,
          Function.comp_apply] at hb hA ⊢
        generalize hD₁ : denoteArgs (structBi sf bi) fuel [a.erase, b.erase] s₁ = D₁ at hb hA ⊢
        generalize hD₂ : denoteArgs bi fuel
          [(tStructToTuple sf t a).erase, (tStructToTuple sf t b).erase] s₂ = D₂ at hA ⊢
        obtain ⟨o₁, s₁'⟩ := D₁
        obtain ⟨o₂, s₂'⟩ := D₂
        cases o₁ with
        | none => exact absurd hb (by simp [isErr, stateM_pure_apply])
        | some vals =>
          obtain ⟨ho, hst⟩ := hA rfl
          simp only at ho hst
          subst ho
          have hlen : vals.length = 2 := by
            have := denoteArgs_length _ fuel _ s₁ vals (by rw [hD₁])
            simpa using this
          rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, _⟩⟩⟩ <;> simp at hlen
          cases x with
          | tuple vs =>
            by_cases hl : vs.length = n
            · simp only [structBi, hh, hl, ↓reduceIte, stateM_pure_apply, stateM_bind_apply,
                stateM_modify_apply] at hb ⊢
              rw [denoteArgs_updFields bi fuel t i n _ _ vs y _ (by simp) hl]
              exact ⟨rfl, (hst.symm.extend_left _).symm⟩
            · simp [structBi, hh, hl, stateM_pure_apply, isErr] at hb
          | _ => simp [structBi, hh, stateM_pure_apply, isErr] at hb
      · rw [show structApp sf t f (List.map (tStructToTuple sf t) (a :: b :: c :: rest)) = none
          by simp [structApp, hh]]
        simp only [Option.getD_none, TExpr.erase, TExpr.eraseList_eq]
        exact denote_app_fallback sf bi t f _ ih (fun vals hl => Or.inr (by
          rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, _⟩⟩⟩ <;> simp_all [structBi])) fuel

/-- The rewrite refines `denote`: when the struct term `e`, whose erasure never reads the
    reserved name `t`, has an outcome that is not an error under `structBi sf bi`, the
    rewritten term has the same outcome under `bi`, from and to environments that agree
    except at `t`. Values correspond by the identity, a struct being read as the tuple of its
    fields. -/
theorem denote_tStructToTuple (sf : StructFieldTys) (bi : Builtins) (t : String) (e : TExpr)
    (h : noVarRef t e.erase = true) (fuel : Nat) :
    Refines isErr t (denote (structBi sf bi) fuel e.erase)
      (denote bi fuel (tStructToTuple sf t e).erase) := by
  induction e using TExpr.ind generalizing fuel with
  | letBind ty n v b ihv ihb =>
    simp only [TExpr.erase, noVarRef, Bool.and_eq_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote]
    refine Refines.bind (ihv h.1 fuel) ?_ ?_
    · intro a s ha; cases a <;> simp_all [isErr, stateM_pure_apply]
    · intro a ha; cases a <;> (try exact Refines.pure _)
      exact Refines.bind (Refines.modify_extend n _) (by simp) (fun _ _ => ihb h.2 fuel)
  | lit ty v =>
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote]
    exact Refines.pure _
  | var ty m =>
    simp only [TExpr.erase, noVarRef, bne_iff_ne, ne_eq] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase]
    exact Refines.var _ _ fuel h
  | lam ty ps b ihb =>
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote]
    exact Refines.pure _
  | app ty f args ih =>
    simp only [TExpr.erase, TExpr.eraseList_eq, noVarRef] at h
    simp only [tStructToTuple, tStructToTuple.goKind, tStructToTuple_goList, TExpr.erase,
      TExpr.eraseList_eq]
    exact denote_structApp sf bi t f args _
      (fun a ha => ih a ha (noVarRef_allExpr_mem h _ (List.mem_map_of_mem ha))) fuel
  | tuple ty es ih =>
    simp only [TExpr.erase, TExpr.eraseList_eq, noVarRef] at h
    simp only [tStructToTuple, tStructToTuple.goKind, tStructToTuple_goList, TExpr.erase,
      TExpr.eraseList_eq, List.map_map, denote]
    refine Refines.bind (denoteArgs_refines _ _ t fuel TExpr.erase
      (TExpr.erase ∘ tStructToTuple sf t) es
      (fun a ha => ih a ha (noVarRef_allExpr_mem h _ (List.mem_map_of_mem ha)) fuel)) ?_ ?_
    · intro a s ha; cases a <;> simp_all [isErr, stateM_pure_apply]
    · intro a ha; cases a <;> exact Refines.pure _
  | proj ty e i ih =>
    simp only [TExpr.erase, noVarRef] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote]
    refine Refines.bind (ih h fuel) ?_ ?_
    · intro a s ha; cases a <;> simp_all [isErr, stateM_pure_apply]
    · intro a ha; cases a <;> (try exact Refines.pure _)
      dsimp only
      generalize Value.projIdx _ i = o
      cases o <;> exact Refines.pure _
  | ifThenElse ty c a b ihc iha ihb =>
    simp only [TExpr.erase, noVarRef, Bool.and_eq_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote]
    refine Refines.bind (ihc h.1.1 fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr
      rcases r with v | v | v | _ | m
      · cases v <;> (try exact Refines.pure _)
        rename_i bv
        cases bv
        · exact ihb h.2 fuel
        · exact iha h.1.2 fuel
      all_goals exact Refines.pure _
  | match_ ty s arms ihs iharms =>
    simp only [TExpr.erase, TExpr.eraseArms_eq, noVarRef, Bool.and_eq_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind, tStructToTuple_goArms, TExpr.erase,
      TExpr.eraseArms_eq, List.map_map, denote]
    refine Refines.bind (ihs h.1 fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr
      cases r <;> (try exact Refines.pure _)
      exact denoteMatchArms_refines _ _ t fuel _ TExpr.erase
        (fun x => (tStructToTuple sf t x).erase) arms
        (fun pa hpa => iharms pa hpa (noVarRef_allArms_mem h.2 _
          (List.mem_map_of_mem hpa)) fuel)
  | unitVal ty =>
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote]
    exact Refines.pure _
  | seq ty a b iha ihb =>
    simp only [TExpr.erase, noVarRef, Bool.and_eq_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote]
    refine Refines.bind (iha h.1 fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr; cases r <;> (try exact Refines.pure _)
      exact ihb h.2 fuel
  | borrow ty e ih =>
    simp only [TExpr.erase, noVarRef] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote]
    exact ih h fuel
  | deref ty e ih =>
    simp only [TExpr.erase, noVarRef] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote]
    exact ih h fuel
  | ann ty e ih =>
    simp only [TExpr.erase] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase]
    exact ih h fuel
  | assign ty n e ih =>
    simp only [TExpr.erase, noVarRef] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote]
    refine Refines.bind (ih h fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr; cases r <;> (try exact Refines.pure _)
      exact Refines.bind (Refines.modify_extend n _) (by simp) (fun _ _ => Refines.pure _)
  | forLoop ty v lo hi b ihlo ihhi ihb =>
    simp only [TExpr.erase, noVarRef, Bool.and_eq_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote]
    refine Refines.bind (ihlo h.1.1 fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr; cases r <;> (try exact Refines.pure _)
      refine Refines.bind (ihhi h.1.2 fuel) ?_ ?_
      · intro r s hr; rename_i vlo; cases r <;> cases vlo <;> simp_all [isErr, stateM_pure_apply]
      · intro r hr
        split <;> first
          | exact Refines.pure _
          | exact denoteForLoop_refines _ _ t v _ _ (ihb h.2) _ _ _
  | forLoopRev ty v lo hi b ihlo ihhi ihb =>
    simp only [TExpr.erase, noVarRef, Bool.and_eq_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote]
    refine Refines.bind (ihlo h.1.1 fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr; cases r <;> (try exact Refines.pure _)
      refine Refines.bind (ihhi h.1.2 fuel) ?_ ?_
      · intro r s hr; rename_i vlo; cases r <;> cases vlo <;> simp_all [isErr, stateM_pure_apply]
      · intro r hr
        split <;> first
          | exact Refines.pure _
          | exact denoteForLoopRev_refines _ _ t v _ _ (ihb h.2) _ _ _
  | whileLoop ty c b ihc ihb =>
    simp only [TExpr.erase, noVarRef, Bool.and_eq_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote]
    exact denoteWhile_refines _ _ t _ _ _ _ (ihc h.1) (ihb h.2) fuel
  | break_none ty =>
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote]
    exact Refines.pure _
  | continue_ ty =>
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote]
    exact Refines.pure _
  | break_some ty e ih =>
    simp only [TExpr.erase, noVarRef] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote]
    refine Refines.bind (ih h fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr; cases r <;> exact Refines.pure _
  | earlyReturn ty e ih =>
    simp only [TExpr.erase, noVarRef] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote]
    refine Refines.bind (ih h fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr; cases r <;> exact Refines.pure _
  | questionMark ty e ih =>
    simp only [TExpr.erase, noVarRef] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote]
    refine Refines.bind (ih h fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr; cases r <;> (try exact Refines.pure _)
      split <;> exact Refines.pure _
  | namedProj ty n e ih =>
    simp only [TExpr.erase, noVarRef, noVarRef.allExpr, Bool.and_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind]
    have hk : ∀ (k : Option TExprKind) (e' : TExpr) (ty' : ImpType),
        (TExpr.mk (k.getD (.namedProj n e')) ty').erase =
          (TExpr.mk (k.getD (.app ".0" [e'])) ty').erase := by
      intro k e' ty'; cases k <;> rfl
    rw [hk]
    have := denote_structApp sf bi t ".0" [e] (tyStructToTuple sf sf.length ty)
      (fun a ha => by rw [List.mem_singleton] at ha; subst ha; exact ih h) fuel
    simpa only [List.map_cons, List.map_nil, TExpr.erase] using this
  | _ =>
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote]
    exact Refines.pure _

/-- `denote_tStructToTuple` under the side condition `StructOk`. -/
theorem denote_tStructToTuple_of_structOk (sf : StructFieldTys) (bi : Builtins) (t : String)
    (e : TExpr) (h : StructOk sf t e) (fuel : Nat) :
    Refines isErr t (denote (structBi sf bi) fuel e.erase)
      (denote bi fuel (tStructToTuple sf t e).erase) :=
  denote_tStructToTuple sf bi t e h.1 fuel

end Hax
