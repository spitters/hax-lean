/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.TExpr
public import HaxLean.Semantics
public import HaxLean.Phase.FlattenLetFoldReturn
public import HaxLean.Phase.InlineLocalClosures
public import HaxLean.DenoteTotal

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
* `structHead?` — the classification of an application head as a struct head, by equality
  with the names the layout generates, so that a non-canonical spelling is not a struct head
* `structBi` — the struct heads over a builtin table, structs read as tuples
* `tStructToTuple` — the rewrite of struct heads and struct types into tuples
* `StructOk` — the side condition: the reserved name is not read, struct heads have their arity

## Main results

* `denote_tStructToTuple` — the rewrite refines `denote`: when the struct term's outcome is
  not an error, the rewritten term has the same outcome, from and to environments that agree
  except at the reserved name bound by the update's `let`.
* `denote'_tStructToTuple`, `denoteApp'_tStructToTuple` — the same refinement for the
  control-flow semantics `denote'` and its call dispatch `denoteApp'`.
* `denoteSpine_tStructToTuple` — the same refinement for the spine reading `denoteSpine`,
  under `spineStructOk`: every closure the source spine inlines is inlined after the rewrite
  and binds a name without a struct role.
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

/-- The update role of `f`: field `i` of a struct `S` of `sf` with `n` fields when `f` is the
    generated head `structUpdateHead S i n` with `i < n`. -/
def structUpdateRole? (sf : StructFieldTys) (f : String) : Option StructHead :=
  sf.findSome? fun p =>
    ((List.range p.2.length).find? fun i => structUpdateHead p.1 i p.2.length == f).map
      fun i => .update i p.2.length

/-- The field-read role of `f`: field `g` of the unique struct of `sf` declaring `g` when `f`
    is `"." ++ g`, and otherwise field `g` of a struct `S` of `sf` when `f` is
    `S ++ "." ++ g`. -/
def structFieldRole? (sf : StructFieldTys) (f : String) : Option StructHead :=
  match sf.filter (fun p => p.2.any fun q => "." ++ q.1 == f) with
  | [(_, fs)] => (fs.findIdx? fun q => "." ++ q.1 == f).map fun i => .field i fs.length
  | _ =>
    sf.findSome? fun p =>
      (p.2.findIdx? fun q => p.1 ++ "." ++ q.1 == f).map fun i => .field i p.2.length

/-- The struct role of the application head `f`, by equality with the names the layout `sf`
    generates: a struct name `S` of `sf` constructs that struct; `structUpdateHead S i n`
    updates field `i` when `S` has `n` fields and `i < n`; `"." ++ g` reads field `g` of the
    unique struct declaring it, and `S ++ "." ++ g` reads field `g` of `S`. Every other head,
    a non-canonical spelling of one of these names among them, has no struct role. -/
def structHead? (sf : StructFieldTys) (f : String) : Option StructHead :=
  match sf.lookup f with
  | some fs => some (.ctor fs.length)
  | none =>
    match structUpdateRole? sf f with
    | some h => some h
    | none => structFieldRole? sf f

/-- The struct heads over the builtin table `bi`, a struct read as the tuple of its fields:
    a construction of `n` fields builds the tuple of its `n` arguments; a field read projects
    a tuple of `n` values; an update replaces the `i`-th value of a tuple of `n` values none of
    which is a control-flow value. Every
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
    | [.tuple vs, v] =>
      if vs.length = n ∧ (vs.all fun x => !x.isControlFlow) = true then
        some (.tuple (vs.set i v))
      else none
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
            by_cases hl : vs.length = n ∧ (vs.all fun x => !x.isControlFlow) = true
            · simp only [structBi, hh, hl, and_self, ↓reduceIte, stateM_pure_apply,
                stateM_bind_apply, stateM_modify_apply] at hb ⊢
              rw [denoteArgs_updFields bi fuel t i n _ _ vs y _ (by simp) hl.1]
              exact ⟨rfl, (hst.symm.extend_left _).symm⟩
            · simp only [structBi, hh, hl, ↓reduceIte, stateM_pure_apply, isErr] at hb
              exact absurd hb (by simp)
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

/-! ## Refinement of `denote'` -/

/-- Case split of an outcome down to the constructor of its value, the Boolean of a `bool`,
    `result` or control-flow value included. -/
local macro "cf_cases " x:ident : tactic =>
  `(tactic| rcases $x:ident with
    (⟨_ | _⟩ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _, _⟩ | ⟨_ | _, _⟩) | _ | _ | _ | _)

/-- `cf_cases` that also splits the payload of a control-flow value. -/
local macro "cf_cases2 " x:ident : tactic =>
  `(tactic| rcases $x:ident with
    (⟨_ | _⟩ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _, _⟩ |
      ⟨_ | _, (⟨_ | _⟩ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _, _⟩ | ⟨_ | _, _⟩)⟩) | _ | _ | _ | _)

namespace StructTuple

/-- The builtin table `S` answers every call a run can make as the struct heads over `T` do:
    whenever `S` answers `f` at argument values `vals` none of which is a control-flow value,
    `structBi sf T` gives the same answer. `denoteArgs'` reads no control-flow value as an
    argument (`denoteArgs'_all_not_isControlFlow`). -/
def StructTab (sf : StructFieldTys) (S T : Builtins) : Prop :=
  ∀ f vals v, (vals.all fun x => !x.isControlFlow) = true → S f vals = some v →
    structBi sf T f vals = some v

theorem StructTab.of_structBi (sf : StructFieldTys) (bi : Builtins) :
    StructTab sf (structBi sf bi) bi :=
  fun _ _ _ _ h => h

/-- A run of `denoteArgs'` on a nonempty list to a list of values reads the head to a value
    that is no control-flow value and the tail to the rest. -/
theorem denoteArgs'_cons_inv (bi : Builtins) (fuel : Nat) (x : ImpExpr) (xs : List ImpExpr)
    (s s' : Env) (vals : List Value) (h : denoteArgs' bi fuel (x :: xs) s = (some vals, s')) :
    ∃ v rest s₁, vals = v :: rest ∧ v.isControlFlow = false ∧
      denote' bi fuel x s = (.val v, s₁) ∧ denoteArgs' bi fuel xs s₁ = (some rest, s') := by
  simp only [denoteArgs', stateM_bind_apply] at h
  rcases hr : denote' bi fuel x s with ⟨o, s₁⟩
  rw [hr] at h
  dsimp only at h
  split at h
  · exact absurd (Prod.mk.inj h).1 (by simp)
  · rename_i v hv
    rcases hrest : denoteArgs' bi fuel xs s₁ with ⟨r, s₂⟩
    rw [stateM_bind_apply, hrest] at h
    cases r with
    | none => exact absurd (Prod.mk.inj h).1 (by simp)
    | some rest =>
      obtain ⟨h1, rfl⟩ := Prod.mk.inj h
      simp only [Option.map_some, Option.some.injEq] at h1
      exact ⟨v, rest, s₁, h1.symm, by cases v <;> simp_all, rfl, hrest⟩
  · exact absurd (Prod.mk.inj h).1 (by simp)

theorem denoteArgs'_length_of_eq (bi : Builtins) (fuel : Nat) :
    ∀ (es : List ImpExpr) (s s' : Env) (vals : List Value),
      denoteArgs' bi fuel es s = (some vals, s') → vals.length = es.length
  | [], s, s', vals, h => by
    rw [Total.denoteArgs'_nil_run] at h
    obtain ⟨h1, -⟩ := Prod.mk.inj h
    cases h1; rfl
  | x :: xs, s, s', vals, h => by
    obtain ⟨v, rest, s₁, rfl, -, -, hr⟩ := denoteArgs'_cons_inv bi fuel x xs s s' vals h
    simp [denoteArgs'_length_of_eq bi fuel xs s₁ s' rest hr]

/-- A run of `denoteArgs'` to a list of values reads no control-flow value. -/
theorem denoteArgs'_all_not_isControlFlow (bi : Builtins) (fuel : Nat) :
    ∀ (es : List ImpExpr) (s s' : Env) (vals : List Value),
      denoteArgs' bi fuel es s = (some vals, s') → (vals.all fun x => !x.isControlFlow) = true
  | [], s, s', vals, h => by
    rw [Total.denoteArgs'_nil_run] at h
    obtain ⟨h1, -⟩ := Prod.mk.inj h
    cases h1; rfl
  | x :: xs, s, s', vals, h => by
    obtain ⟨v, rest, s₁, rfl, hv, -, hr⟩ := denoteArgs'_cons_inv bi fuel x xs s s' vals h
    simp only [List.all_cons, hv, Bool.not_false, Bool.true_and]
    exact denoteArgs'_all_not_isControlFlow bi fuel xs s₁ s' rest hr

/-- A call read by `denote'` without error reads its arguments to values that the builtin
    table answers. -/
theorem denote'_app_inv (bi : Builtins) (fuel : Nat) (f : String) (xs : List ImpExpr)
    (s s' : Env) (o : Outcome) (h : denote' bi fuel (.app f xs) s = (o, s'))
    (ho : isErr o = false) :
    ∃ vals v, o = .val v ∧ bi f vals = some v ∧ denoteArgs' bi fuel xs s = (some vals, s') := by
  simp only [denote', denoteApp', stateM_bind_apply] at h
  rcases hA : denoteArgs' bi fuel xs s with ⟨r, s₁⟩
  rw [hA] at h
  cases r with
  | none =>
    obtain ⟨rfl, -⟩ := Prod.mk.inj h
    simp [isErr] at ho
  | some vals =>
    cases hb : bi f vals with
    | none =>
      simp only [hb, stateM_pure_apply] at h
      obtain ⟨rfl, -⟩ := Prod.mk.inj h
      simp [isErr] at ho
    | some v =>
      simp only [hb, stateM_pure_apply] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨vals, v, rfl, hb, rfl⟩

theorem denote'_var_refines (S T : Builtins) (fuel : Nat) {t m : String} (h : m ≠ t) :
    Refines isErr t (denote' S fuel (.var m)) (denote' T fuel (.var m)) := by
  intro s₁ s₂ hs _
  simp only [denote', stateM_bind_apply, stateM_get_apply]
  rw [hs m h]
  cases s₂ m <;> exact ⟨rfl, hs⟩

theorem denoteArgs'_refines (S T : Builtins) (t : String) (fuel : Nat) {β : Type}
    (F G : β → ImpExpr) :
    ∀ (xs : List β),
      (∀ x ∈ xs, Refines isErr t (denote' S fuel (F x)) (denote' T fuel (G x))) →
      Refines Option.isNone t (denoteArgs' S fuel (xs.map F))
        (denoteArgs' T fuel (xs.map G)) := by
  intro xs
  induction xs with
  | nil => intro _; simp only [List.map_nil, denoteArgs']; exact Refines.pure _
  | cons x xs ih =>
    intro hall
    simp only [List.map_cons, denoteArgs']
    refine Refines.bind (hall x (List.mem_cons_self ..)) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr
      cf_cases r <;> first
        | exact Refines.pure _
        | (refine Refines.bind (ih fun y hy => hall y (List.mem_cons_of_mem _ hy)) ?_ ?_
           · intro r s hr; cases r <;> simp_all [stateM_pure_apply]
           · intro r hr; exact Refines.pure _)

theorem denoteMatchArms'_refines (S T : Builtins) (t : String) (fuel : Nat) (v : Value)
    {β : Type} (F G : β → ImpExpr) :
    ∀ (arms : List (ImpPat × β)),
      (∀ pa ∈ arms, Refines isErr t (denote' S fuel (F pa.2)) (denote' T fuel (G pa.2))) →
      Refines isErr t (denoteMatchArms' S fuel v (arms.map fun pa => (pa.1, F pa.2)))
        (denoteMatchArms' T fuel v (arms.map fun pa => (pa.1, G pa.2))) := by
  intro arms
  induction arms with
  | nil => intro _; simp only [List.map_nil, denoteMatchArms']; exact Refines.pure _
  | cons pa rest ih =>
    obtain ⟨pat, b⟩ := pa
    intro hall s₁ s₂ hs hb
    simp only [List.map_cons, denoteMatchArms', stateM_bind_apply, stateM_get_apply] at hb ⊢
    have hmp := matchPat_agree t pat v s₁ s₂ hs
    cases hp1 : matchPat pat v s₁ <;> cases hp2 : matchPat pat v s₂ <;>
      simp only [hp1, hp2, OptAgree] at hmp hb ⊢
    · exact ih (fun pa' h' => hall pa' (List.mem_cons_of_mem _ h')) s₁ s₂ hs hb
    · simp only [stateM_bind_apply, stateM_set_apply] at hb ⊢
      exact hall (pat, b) (List.mem_cons_self ..) _ _ hmp hb

theorem denoteForLoopOrig'_refines (S T : Builtins) (t var : String) (body body' : ImpExpr)
    (hb : ∀ fuel, Refines isErr t (denote' S fuel body) (denote' T fuel body')) :
    ∀ fuel lo hi, Refines isErr t (denoteForLoopOrig' S fuel var lo hi body)
      (denoteForLoopOrig' T fuel var lo hi body') := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi
    unfold denoteForLoopOrig'
    split
    · exact Refines.pure _
    · split
      · exact Refines.pure _
      · exact absurd rfl ‹_›
  | succ k ih =>
    intro lo hi
    unfold denoteForLoopOrig'
    split
    · exact Refines.pure _
    · split
      · exact Refines.pure _
      · refine Refines.bind (Refines.modify_extend var (.int lo)) (by simp) (fun _ _ => ?_)
        refine Refines.bind (hb (k + 1)) ?_ ?_
        · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
        · intro rb _
          cases rb <;> first | exact ih _ _ | exact Refines.pure _

theorem denoteForLoopRevOrig'_refines (S T : Builtins) (t var : String) (body body' : ImpExpr)
    (hb : ∀ fuel, Refines isErr t (denote' S fuel body) (denote' T fuel body')) :
    ∀ fuel lo hi, Refines isErr t (denoteForLoopRevOrig' S fuel var lo hi body)
      (denoteForLoopRevOrig' T fuel var lo hi body') := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi
    unfold denoteForLoopRevOrig'
    split
    · exact Refines.pure _
    · split
      · exact Refines.pure _
      · exact absurd rfl ‹_›
  | succ k ih =>
    intro lo hi
    unfold denoteForLoopRevOrig'
    split
    · exact Refines.pure _
    · split
      · exact Refines.pure _
      · refine Refines.bind (Refines.modify_extend var (.int (hi - 1))) (by simp)
          (fun _ _ => ?_)
        refine Refines.bind (hb (k + 1)) ?_ ?_
        · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
        · intro rb _
          cases rb <;> first | exact ih _ _ | exact Refines.pure _

theorem denoteForLoop'_refines (S T : Builtins) (t var : String) (body body' : ImpExpr)
    (hb : ∀ fuel, Refines isErr t (denote' S fuel body) (denote' T fuel body')) :
    ∀ fuel lo hi, Refines isErr t (denoteForLoop' S fuel var lo hi body)
      (denoteForLoop' T fuel var lo hi body') := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi
    unfold denoteForLoop'
    split
    · exact Refines.pure _
    · split
      · exact Refines.pure _
      · exact absurd rfl ‹_›
  | succ k ih =>
    intro lo hi
    unfold denoteForLoop'
    split
    · exact Refines.pure _
    · split
      · exact Refines.pure _
      · refine Refines.bind (Refines.modify_extend var (.int lo)) (by simp) (fun _ _ => ?_)
        refine Refines.bind (hb (k + 1)) ?_ ?_
        · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
        · intro rb _
          cf_cases rb <;> first | exact Refines.pure _ | exact ih _ _

theorem denoteForLoopRev'_refines (S T : Builtins) (t var : String) (body body' : ImpExpr)
    (hb : ∀ fuel, Refines isErr t (denote' S fuel body) (denote' T fuel body')) :
    ∀ fuel lo hi, Refines isErr t (denoteForLoopRev' S fuel var lo hi body)
      (denoteForLoopRev' T fuel var lo hi body') := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi
    unfold denoteForLoopRev'
    split
    · exact Refines.pure _
    · split
      · exact Refines.pure _
      · exact absurd rfl ‹_›
  | succ k ih =>
    intro lo hi
    unfold denoteForLoopRev'
    split
    · exact Refines.pure _
    · split
      · exact Refines.pure _
      · refine Refines.bind (Refines.modify_extend var (.int (hi - 1))) (by simp)
          (fun _ _ => ?_)
        refine Refines.bind (hb (k + 1)) ?_ ?_
        · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
        · intro rb _
          cf_cases rb <;> first | exact Refines.pure _ | exact ih _ _

theorem denoteForLoop'Return_refines (S T : Builtins) (t var : String) (body body' : ImpExpr)
    (hb : ∀ fuel, Refines isErr t (denote' S fuel body) (denote' T fuel body')) :
    ∀ fuel lo hi, Refines isErr t (denoteForLoop'Return S fuel var lo hi body)
      (denoteForLoop'Return T fuel var lo hi body') := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi
    unfold denoteForLoop'Return
    split
    · exact Refines.pure _
    · split
      · exact Refines.pure _
      · exact absurd rfl ‹_›
  | succ k ih =>
    intro lo hi
    unfold denoteForLoop'Return
    split
    · exact Refines.pure _
    · split
      · exact Refines.pure _
      · refine Refines.bind (Refines.modify_extend var (.int lo)) (by simp) (fun _ _ => ?_)
        refine Refines.bind (hb (k + 1)) ?_ ?_
        · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
        · intro rb _
          cf_cases2 rb <;> first | exact Refines.pure _ | exact ih _ _

theorem denoteForLoopRev'Return_refines (S T : Builtins) (t var : String)
    (body body' : ImpExpr)
    (hb : ∀ fuel, Refines isErr t (denote' S fuel body) (denote' T fuel body')) :
    ∀ fuel lo hi, Refines isErr t (denoteForLoopRev'Return S fuel var lo hi body)
      (denoteForLoopRev'Return T fuel var lo hi body') := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi
    unfold denoteForLoopRev'Return
    split
    · exact Refines.pure _
    · split
      · exact Refines.pure _
      · exact absurd rfl ‹_›
  | succ k ih =>
    intro lo hi
    unfold denoteForLoopRev'Return
    split
    · exact Refines.pure _
    · split
      · exact Refines.pure _
      · refine Refines.bind (Refines.modify_extend var (.int (hi - 1))) (by simp)
          (fun _ _ => ?_)
        refine Refines.bind (hb (k + 1)) ?_ ?_
        · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
        · intro rb _
          cf_cases2 rb <;> first | exact Refines.pure _ | exact ih _ _

theorem denoteWhileOrig'_refines (S T : Builtins) (t : String) (cond cond' body body' : ImpExpr)
    (hc : ∀ fuel, Refines isErr t (denote' S fuel cond) (denote' T fuel cond'))
    (hb : ∀ fuel, Refines isErr t (denote' S fuel body) (denote' T fuel body')) :
    ∀ fuel, Refines isErr t (denoteWhileOrig' S fuel cond body)
      (denoteWhileOrig' T fuel cond' body') := by
  intro fuel
  induction fuel with
  | zero =>
    unfold denoteWhileOrig'
    split
    · exact Refines.pure _
    · exact absurd rfl ‹_›
  | succ k ih =>
    unfold denoteWhileOrig'
    split
    · exact Refines.pure _
    · refine Refines.bind (hc (k + 1)) ?_ ?_
      · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
      · intro rc _
        cf_cases rc <;> first
          | exact Refines.pure _
          | (refine Refines.bind (hb (k + 1)) ?_ ?_
             · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
             · intro rb _
               cases rb <;> first | exact ih | exact Refines.pure _)

theorem denoteWhile'_refines (S T : Builtins) (t : String) (cond cond' body body' : ImpExpr)
    (hc : ∀ fuel, Refines isErr t (denote' S fuel cond) (denote' T fuel cond'))
    (hb : ∀ fuel, Refines isErr t (denote' S fuel body) (denote' T fuel body')) :
    ∀ fuel, Refines isErr t (denoteWhile' S fuel cond body)
      (denoteWhile' T fuel cond' body') := by
  intro fuel
  induction fuel with
  | zero =>
    unfold denoteWhile'
    split
    · exact Refines.pure _
    · exact absurd rfl ‹_›
  | succ k ih =>
    unfold denoteWhile'
    split
    · exact Refines.pure _
    · refine Refines.bind (hc (k + 1)) ?_ ?_
      · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
      · intro rc _
        cf_cases rc <;> first
          | exact Refines.pure _
          | (refine Refines.bind (hb (k + 1)) ?_ ?_
             · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
             · intro rb _
               cf_cases rb <;> first | exact Refines.pure _ | exact ih)

theorem denoteWhile'Return_refines (S T : Builtins) (t : String)
    (cond cond' body body' : ImpExpr)
    (hc : ∀ fuel, Refines isErr t (denote' S fuel cond) (denote' T fuel cond'))
    (hb : ∀ fuel, Refines isErr t (denote' S fuel body) (denote' T fuel body')) :
    ∀ fuel, Refines isErr t (denoteWhile'Return S fuel cond body)
      (denoteWhile'Return T fuel cond' body') := by
  intro fuel
  induction fuel with
  | zero =>
    unfold denoteWhile'Return
    split
    · exact Refines.pure _
    · exact absurd rfl ‹_›
  | succ k ih =>
    unfold denoteWhile'Return
    split
    · exact Refines.pure _
    · refine Refines.bind (hc (k + 1)) ?_ ?_
      · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
      · intro rc _
        cf_cases rc <;> first
          | exact Refines.pure _
          | (refine Refines.bind (hb (k + 1)) ?_ ?_
             · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
             · intro rb _
               cf_cases2 rb <;> first | exact Refines.pure _ | exact ih)

/-- A list of expressions each read by `denote'` to a value that is no control-flow value,
    without changing the environment, reads to the list of those values. -/
theorem denoteArgs'_map_val (bi : Builtins) (fuel : Nat) (s : Env) {β : Type}
    (g : β → ImpExpr) (hv : β → Value) :
    ∀ (l : List β), (∀ j ∈ l, denote' bi fuel (g j) s = (.val (hv j), s) ∧
        (hv j).isControlFlow = false) →
      denoteArgs' bi fuel (l.map g) s = (some (l.map hv), s) := by
  intro l
  induction l with
  | nil => intro _; exact Total.denoteArgs'_nil_run bi fuel s
  | cons j l ih =>
    intro h
    exact Total.denoteArgs'_cons_of_val (h j (List.mem_cons_self ..)).1
      (h j (List.mem_cons_self ..)).2 (ih fun j' hj' => h j' (List.mem_cons_of_mem _ hj'))

/-- The fields of an update read by `denote'`, without changing the environment, to the
    fields of the struct with the `i`-th replaced, when no field and not the new value is a
    control-flow value. -/
theorem denoteArgs'_updFields (bi : Builtins) (fuel : Nat) (t : String) (i n : Nat)
    (sty vty : ImpType) (vs : List Value) (w : Value) (s : Env)
    (hs : s t = some (.tuple [.tuple vs, w])) (hn : vs.length = n)
    (hw : w.isControlFlow = false) (hc : (vs.all fun x => !x.isControlFlow) = true) :
    denoteArgs' bi fuel ((updFields t i n sty vty).map TExpr.erase) s =
      (some (vs.set i w), s) := by
  unfold updFields
  rw [List.map_map,
    denoteArgs'_map_val bi fuel s _ (fun j => if j = i then w else vs.getD j .unit)]
  · refine Prod.ext (congrArg some ?_) rfl
    apply List.ext_getElem
    · simp [hn]
    · intro k h1 h2
      simp only [List.getElem_map, List.getElem_range, List.getElem_set]
      grind only [= List.length_set, = List.getD_eq_getElem?_getD, = getElem?_pos,
        = Option.getD_some]
  · intro j hj
    rw [List.mem_range] at hj
    show denote' bi fuel (TExpr.erase (if j = i then _ else _)) s = _ ∧ _
    have hjv : j < vs.length := hn ▸ hj
    by_cases hji : j = i
    · simp only [hji, ↓reduceIte, TExpr.erase, denote', stateM_bind_apply, stateM_get_apply, hs,
        Value.projIdx, stateM_pure_apply]
      exact ⟨rfl, hw⟩
    · have hcj : vs[j].isControlFlow = false := by
        have := List.all_eq_true.1 hc vs[j] (List.getElem_mem hjv)
        simpa using this
      simp only [hji, ↓reduceIte, TExpr.erase, denote', stateM_bind_apply, stateM_get_apply, hs,
        Value.projIdx, stateM_pure_apply]
      simp [List.getElem?_eq_getElem hjv, stateM_pure_apply, List.getD_eq_getElem?_getD, hcj]

/-- A call left in place refines itself when `T` answers its head as `S` does on every
    argument list of its arity on which `S` answers. -/
theorem denote'_app_fallback (sf : StructFieldTys) (S T : Builtins) (t f : String)
    (args : List TExpr)
    (ih : ∀ a ∈ args, ∀ fuel, Refines isErr t (denote' S fuel a.erase)
      (denote' T fuel (tStructToTuple sf t a).erase))
    (hfb : ∀ vals : List Value, vals.length = args.length →
      (vals.all fun x => !x.isControlFlow) = true → ∀ v,
      S f vals = some v → T f vals = some v) (fuel : Nat) :
    Refines isErr t (denote' S fuel (.app f (args.map TExpr.erase)))
      (denote' T fuel (.app f ((args.map (tStructToTuple sf t)).map TExpr.erase))) := by
  intro s₁ s₂ hs hb
  rcases h₁ : denote' S fuel (.app f (args.map TExpr.erase)) s₁ with ⟨o, s₁'⟩
  rw [h₁] at hb
  obtain ⟨vals, v, rfl, hS, hA⟩ := denote'_app_inv S fuel f _ s₁ s₁' o h₁ hb
  have hA' := denoteArgs'_refines S T t fuel TExpr.erase (TExpr.erase ∘ tStructToTuple sf t)
    args (fun x hx => ih x hx fuel) s₁ s₂ hs (by simp [hA])
  rw [hA] at hA'
  rcases hB : denoteArgs' T fuel (List.map (TExpr.erase ∘ tStructToTuple sf t) args) s₂ with
    ⟨o₂, s₂'⟩
  rw [hB] at hA'
  obtain ⟨ho, hst⟩ := hA'
  simp only at ho hst
  subst ho
  have hlen := denoteArgs'_length_of_eq S fuel _ s₁ s₁' vals hA
  rw [List.length_map] at hlen
  rw [List.map_map, Total.denote'_app_of_args hB
    (hfb vals hlen (denoteArgs'_all_not_isControlFlow S fuel _ s₁ s₁' vals hA) v hS)]
  exact ⟨rfl, hst⟩

/-- A call node refines its rewrite under `denote'`, given that its arguments do. -/
theorem denote'_structApp (sf : StructFieldTys) (S T : Builtins) (hST : StructTab sf S T)
    (t f : String) (args : List TExpr) (ty : ImpType)
    (ih : ∀ a ∈ args, ∀ fuel, Refines isErr t (denote' S fuel a.erase)
      (denote' T fuel (tStructToTuple sf t a).erase)) (fuel : Nat) :
    Refines isErr t (denote' S fuel (.app f (args.map TExpr.erase)))
      (denote' T fuel (TExpr.mk ((structApp sf t f (args.map (tStructToTuple sf t))).getD
        (.app f (args.map (tStructToTuple sf t)))) ty).erase) := by
  have hT : ∀ vals v, (vals.all fun x => !x.isControlFlow) = true → S f vals = some v →
      structBi sf T f vals = some v := hST f
  have ih' : ∀ x ∈ args, Refines isErr t (denote' S fuel x.erase)
      (denote' T fuel ((TExpr.erase ∘ tStructToTuple sf t) x)) := fun x hx => ih x hx fuel
  cases hh : structHead? sf f with
  | none =>
    have hs : structApp sf t f (args.map (tStructToTuple sf t)) = none := by
      simp [structApp, hh]
    rw [hs]
    simp only [Option.getD_none, TExpr.erase, TExpr.eraseList_eq]
    exact denote'_app_fallback sf S T t f args ih
      (fun vals _ hc v h => by simpa [structBi, hh] using hT vals v hc h) fuel
  | some hd =>
    cases hd with
    | ctor n =>
      have hs : structApp sf t f (args.map (tStructToTuple sf t)) =
          some (.tuple (args.map (tStructToTuple sf t))) := by
        simp [structApp, hh]
      rw [hs]
      simp only [Option.getD_some, TExpr.erase, TExpr.eraseList_eq, List.map_map]
      intro s₁ s₂ hs₁ hb
      rcases h₁ : denote' S fuel (.app f (args.map TExpr.erase)) s₁ with ⟨o, s₁'⟩
      rw [h₁] at hb
      obtain ⟨vals, v, rfl, hS, hA⟩ := denote'_app_inv S fuel f _ s₁ s₁' o h₁ hb
      have hv := hT vals v (denoteArgs'_all_not_isControlFlow S fuel _ s₁ s₁' vals hA) hS
      simp only [structBi, hh] at hv
      split at hv
      · cases hv
        have hA' := denoteArgs'_refines S T t fuel TExpr.erase
          (TExpr.erase ∘ tStructToTuple sf t) args ih' s₁ s₂ hs₁ (by simp [hA])
        rw [hA] at hA'
        rcases hB : denoteArgs' T fuel (List.map (TExpr.erase ∘ tStructToTuple sf t) args) s₂
          with ⟨o₂, s₂'⟩
        rw [hB] at hA'
        obtain ⟨ho, hst⟩ := hA'
        simp only at ho hst
        subst ho
        simp only [denote', stateM_bind_apply, hB, stateM_pure_apply]
        exact ⟨by trivial, hst⟩
      · cases hv
    | field i n =>
      rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · rw [show structApp sf t f (List.map (tStructToTuple sf t) []) = none by
          simp [structApp, hh]]
        simp only [Option.getD_none, TExpr.erase, TExpr.eraseList_eq]
        exact denote'_app_fallback sf S T t f [] ih (fun vals hl hc v h => by
          have := hT vals v hc h
          rcases vals with _ | ⟨x, _ | ⟨y, _⟩⟩ <;> simp_all [structBi]) fuel
      · rw [show structApp sf t f (List.map (tStructToTuple sf t) [a]) =
            some (.proj (tStructToTuple sf t a) i) by simp [structApp, hh]]
        simp only [Option.getD_some, TExpr.erase, List.map_cons, List.map_nil]
        intro s₁ s₂ hs₁ hb
        rcases h₁ : denote' S fuel (.app f [a.erase]) s₁ with ⟨o, s₁'⟩
        rw [h₁] at hb
        obtain ⟨vals, v, rfl, hS, hA⟩ := denote'_app_inv S fuel f _ s₁ s₁' o h₁ hb
        have hc := denoteArgs'_all_not_isControlFlow S fuel _ s₁ s₁' vals hA
        obtain ⟨w, rest, s₃, rfl, hw, hd, hrest⟩ :=
          denoteArgs'_cons_inv S fuel _ _ s₁ s₁' vals hA
        rw [Total.denoteArgs'_nil_run] at hrest
        obtain ⟨hr1, rfl⟩ := Prod.mk.inj hrest
        cases hr1
        have hv := hT [w] v hc hS
        obtain ⟨ho, hst⟩ := ih a (List.mem_singleton_self a) fuel s₁ s₂ hs₁ (by simp [hd, isErr])
        rw [hd] at ho hst
        rcases h₂ : denote' T fuel (tStructToTuple sf t a).erase s₂ with ⟨o₂, s₂'⟩
        rw [h₂] at ho hst
        simp only at ho hst
        subst ho
        cases w with
        | tuple vs =>
          simp only [structBi, hh] at hv
          split at hv
          · simp only [denote', stateM_bind_apply, h₂, Value.projIdx, hv, stateM_pure_apply]
            exact ⟨by trivial, hst⟩
          · cases hv
        | _ => simp [structBi, hh] at hv
      · rw [show structApp sf t f (List.map (tStructToTuple sf t) (a :: b :: rest)) = none by
          simp [structApp, hh]]
        simp only [Option.getD_none, TExpr.erase, TExpr.eraseList_eq]
        exact denote'_app_fallback sf S T t f _ ih (fun vals hl hc v h => by
          have := hT vals v hc h
          rcases vals with _ | ⟨x, _ | ⟨y, _⟩⟩ <;> simp_all [structBi]) fuel
    | update i n =>
      rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
      · rw [show structApp sf t f (List.map (tStructToTuple sf t) []) = none by
          simp [structApp, hh]]
        simp only [Option.getD_none, TExpr.erase, TExpr.eraseList_eq]
        exact denote'_app_fallback sf S T t f [] ih (fun vals hl hc v h => by
          have := hT vals v hc h
          rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, _⟩⟩⟩ <;> simp_all [structBi]) fuel
      · rw [show structApp sf t f (List.map (tStructToTuple sf t) [a]) = none by
          simp [structApp, hh]]
        simp only [Option.getD_none, TExpr.erase, TExpr.eraseList_eq]
        exact denote'_app_fallback sf S T t f [a] ih (fun vals hl hc v h => by
          have := hT vals v hc h
          rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, _⟩⟩⟩ <;> simp_all [structBi]) fuel
      · rw [show structApp sf t f (List.map (tStructToTuple sf t) [a, b]) =
            some (.letBind t
              (.mk (.tuple [tStructToTuple sf t a, tStructToTuple sf t b])
                (.tuple [(tStructToTuple sf t a).ty, (tStructToTuple sf t b).ty]))
              (.mk (.tuple (updFields t i n (tStructToTuple sf t a).ty
                (tStructToTuple sf t b).ty)) (tStructToTuple sf t a).ty)) by
          simp [structApp, hh]]
        simp only [Option.getD_some, TExpr.erase, TExpr.eraseList_eq, List.map_cons,
          List.map_nil]
        intro s₁ s₂ hs₁ hb
        rcases h₁ : denote' S fuel (.app f [a.erase, b.erase]) s₁ with ⟨o, s₁'⟩
        rw [h₁] at hb
        obtain ⟨vals, v, rfl, hS, hA⟩ := denote'_app_inv S fuel f _ s₁ s₁' o h₁ hb
        have hc := denoteArgs'_all_not_isControlFlow S fuel _ s₁ s₁' vals hA
        have hA' := denoteArgs'_refines S T t fuel TExpr.erase
          (TExpr.erase ∘ tStructToTuple sf t) [a, b] ih' s₁ s₂ hs₁ (by simp [hA])
        simp only [List.map_cons, List.map_nil, Function.comp_apply] at hA'
        rw [hA] at hA'
        rcases hB : denoteArgs' T fuel
          [(tStructToTuple sf t a).erase, (tStructToTuple sf t b).erase] s₂ with ⟨o₂, s₂'⟩
        rw [hB] at hA'
        obtain ⟨ho, hst⟩ := hA'
        simp only at ho hst
        subst ho
        obtain ⟨x, rest, s₃, rfl, -, -, hrest⟩ := denoteArgs'_cons_inv S fuel _ _ s₁ s₁' vals hA
        obtain ⟨y, rest', s₄, rfl, hy, -, hnil⟩ :=
          denoteArgs'_cons_inv S fuel _ _ s₃ s₁' rest hrest
        rw [Total.denoteArgs'_nil_run] at hnil
        obtain ⟨hr1, rfl⟩ := Prod.mk.inj hnil
        cases hr1
        have hv := hT [x, y] v hc hS
        cases x with
        | tuple vs =>
          simp only [structBi, hh] at hv
          split at hv
          · rename_i hl
            cases hv
            simp only [denote', stateM_bind_apply, hB, stateM_pure_apply, stateM_modify_apply]
            rw [denoteArgs'_updFields T fuel t i n _ _ vs y _ (by simp) hl.1 hy hl.2]
            exact ⟨rfl, (hst.symm.extend_left _).symm⟩
          · cases hv
        | _ => simp [structBi, hh] at hv
      · rw [show structApp sf t f (List.map (tStructToTuple sf t) (a :: b :: c :: rest)) = none
          by simp [structApp, hh]]
        simp only [Option.getD_none, TExpr.erase, TExpr.eraseList_eq]
        exact denote'_app_fallback sf S T t f _ ih (fun vals hl hc v h => by
          have := hT vals v hc h
          rcases vals with _ | ⟨x, _ | ⟨y, _ | ⟨z, _⟩⟩⟩ <;> simp_all [structBi]) fuel

end StructTuple

/-- The rewrite refines `denote'` over builtin tables `S` and `T` with `StructTab sf S T`:
    when the struct term `e`, whose erasure never reads the reserved name `t`, has an outcome
    that is not an error under `S`, the rewritten term has the same outcome under `T`, from
    and to environments that agree except at `t`. -/
theorem denote'_tStructToTuple_of_structTab (sf : StructFieldTys) (S T : Builtins)
    (hST : StructTab sf S T) (t : String) (e : TExpr) (h : noVarRef t e.erase = true)
    (fuel : Nat) :
    Refines isErr t (denote' S fuel e.erase) (denote' T fuel (tStructToTuple sf t e).erase) := by
  induction e using TExpr.ind generalizing fuel with
  | letBind ty n v b ihv ihb =>
    simp only [TExpr.erase, noVarRef, Bool.and_eq_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    refine Refines.bind (ihv h.1 fuel) ?_ ?_
    · intro a s ha; cases a <;> simp_all [isErr, stateM_pure_apply]
    · intro a ha
      cf_cases a <;> first
        | exact Refines.pure _
        | exact Refines.bind (Refines.modify_extend n _) (by simp) (fun _ _ => ihb h.2 fuel)
  | var ty m =>
    simp only [TExpr.erase, noVarRef, bne_iff_ne, ne_eq] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase]
    exact denote'_var_refines _ _ fuel h
  | app ty f args ih =>
    simp only [TExpr.erase, TExpr.eraseList_eq, noVarRef] at h
    simp only [tStructToTuple, tStructToTuple.goKind, tStructToTuple_goList, TExpr.erase,
      TExpr.eraseList_eq]
    exact denote'_structApp sf S T hST t f args _
      (fun a ha => ih a ha (noVarRef_allExpr_mem h _ (List.mem_map_of_mem ha))) fuel
  | tuple ty es ih =>
    simp only [TExpr.erase, TExpr.eraseList_eq, noVarRef] at h
    simp only [tStructToTuple, tStructToTuple.goKind, tStructToTuple_goList, TExpr.erase,
      TExpr.eraseList_eq, List.map_map, denote']
    refine Refines.bind (denoteArgs'_refines _ _ t fuel TExpr.erase
      (TExpr.erase ∘ tStructToTuple sf t) es
      (fun a ha => ih a ha (noVarRef_allExpr_mem h _ (List.mem_map_of_mem ha)) fuel)) ?_ ?_
    · intro a s ha; cases a <;> simp_all [isErr, stateM_pure_apply]
    · intro a ha; cases a <;> exact Refines.pure _
  | proj ty e i ih =>
    simp only [TExpr.erase, noVarRef] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    refine Refines.bind (ih h fuel) ?_ ?_
    · intro a s ha; cases a <;> simp_all [isErr, stateM_pure_apply]
    · intro a ha
      cf_cases a <;> first
        | exact Refines.pure _
        | (dsimp only
           generalize Value.projIdx _ i = o
           cases o <;> exact Refines.pure _)
  | ifThenElse ty c a b ihc iha ihb =>
    simp only [TExpr.erase, noVarRef, Bool.and_eq_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    refine Refines.bind (ihc h.1.1 fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr
      cf_cases r <;> first
        | exact Refines.pure _
        | exact iha h.1.2 fuel
        | exact ihb h.2 fuel
  | match_ ty s arms ihs iharms =>
    simp only [TExpr.erase, TExpr.eraseArms_eq, noVarRef, Bool.and_eq_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind, tStructToTuple_goArms, TExpr.erase,
      TExpr.eraseArms_eq, List.map_map, denote']
    refine Refines.bind (ihs h.1 fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr
      cf_cases r <;> first
        | exact Refines.pure _
        | exact denoteMatchArms'_refines _ _ t fuel _ TExpr.erase
            (fun x => (tStructToTuple sf t x).erase) arms
            (fun pa hpa => iharms pa hpa (noVarRef_allArms_mem h.2 _
              (List.mem_map_of_mem hpa)) fuel)
  | seq ty a b iha ihb =>
    simp only [TExpr.erase, noVarRef, Bool.and_eq_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    refine Refines.bind (iha h.1 fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr
      cf_cases r <;> first | exact Refines.pure _ | exact ihb h.2 fuel
  | borrow ty e ih =>
    simp only [TExpr.erase, noVarRef] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    exact ih h fuel
  | deref ty e ih =>
    simp only [TExpr.erase, noVarRef] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    exact ih h fuel
  | ann ty e ih =>
    simp only [TExpr.erase] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase]
    exact ih h fuel
  | assign ty n e ih =>
    simp only [TExpr.erase, noVarRef] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    refine Refines.bind (ih h fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr
      cf_cases r <;> first
        | exact Refines.pure _
        | exact Refines.bind (Refines.modify_extend n _) (by simp) (fun _ _ => Refines.pure _)
  | forLoop ty v lo hi b ihlo ihhi ihb =>
    simp only [TExpr.erase, noVarRef, Bool.and_eq_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    refine Refines.bind (ihlo h.1.1 fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr
      cf_cases r <;> first
        | exact Refines.pure _
        | (refine Refines.bind (ihhi h.1.2 fuel) ?_ ?_
           · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
           · intro r' _
             cf_cases r' <;> first
               | exact Refines.pure _
               | exact denoteForLoopOrig'_refines _ _ t v _ _ (ihb h.2) _ _ _)
  | forLoopRev ty v lo hi b ihlo ihhi ihb =>
    simp only [TExpr.erase, noVarRef, Bool.and_eq_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    refine Refines.bind (ihlo h.1.1 fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr
      cf_cases r <;> first
        | exact Refines.pure _
        | (refine Refines.bind (ihhi h.1.2 fuel) ?_ ?_
           · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
           · intro r' _
             cf_cases r' <;> first
               | exact Refines.pure _
               | exact denoteForLoopRevOrig'_refines _ _ t v _ _ (ihb h.2) _ _ _)
  | whileLoop ty c b ihc ihb =>
    simp only [TExpr.erase, noVarRef, Bool.and_eq_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    exact denoteWhileOrig'_refines _ _ t _ _ _ _ (ihc h.1) (ihb h.2) fuel
  | forFold ty v lo hi b ihlo ihhi ihb =>
    simp only [TExpr.erase, noVarRef, Bool.and_eq_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    refine Refines.bind (ihlo h.1.1 fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr
      cf_cases r <;> first
        | exact Refines.pure _
        | (refine Refines.bind (ihhi h.1.2 fuel) ?_ ?_
           · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
           · intro r' _
             cf_cases r' <;> first
               | exact Refines.pure _
               | exact denoteForLoop'_refines _ _ t v _ _ (ihb h.2) _ _ _)
  | forFoldRev ty v lo hi b ihlo ihhi ihb =>
    simp only [TExpr.erase, noVarRef, Bool.and_eq_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    refine Refines.bind (ihlo h.1.1 fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr
      cf_cases r <;> first
        | exact Refines.pure _
        | (refine Refines.bind (ihhi h.1.2 fuel) ?_ ?_
           · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
           · intro r' _
             cf_cases r' <;> first
               | exact Refines.pure _
               | exact denoteForLoopRev'_refines _ _ t v _ _ (ihb h.2) _ _ _)
  | whileFold ty c b ihc ihb =>
    simp only [TExpr.erase, noVarRef, Bool.and_eq_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    exact denoteWhile'_refines _ _ t _ _ _ _ (ihc h.1) (ihb h.2) fuel
  | forFoldReturn ty v lo hi b ihlo ihhi ihb =>
    simp only [TExpr.erase, noVarRef, Bool.and_eq_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    refine Refines.bind (ihlo h.1.1 fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr
      cf_cases r <;> first
        | exact Refines.pure _
        | (refine Refines.bind (ihhi h.1.2 fuel) ?_ ?_
           · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
           · intro r' _
             cf_cases r' <;> first
               | exact Refines.pure _
               | exact denoteForLoop'Return_refines _ _ t v _ _ (ihb h.2) _ _ _)
  | forFoldRevReturn ty v lo hi b ihlo ihhi ihb =>
    simp only [TExpr.erase, noVarRef, Bool.and_eq_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    refine Refines.bind (ihlo h.1.1 fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr
      cf_cases r <;> first
        | exact Refines.pure _
        | (refine Refines.bind (ihhi h.1.2 fuel) ?_ ?_
           · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
           · intro r' _
             cf_cases r' <;> first
               | exact Refines.pure _
               | exact denoteForLoopRev'Return_refines _ _ t v _ _ (ihb h.2) _ _ _)
  | whileFoldReturn ty c b ihc ihb =>
    simp only [TExpr.erase, noVarRef, Bool.and_eq_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    exact denoteWhile'Return_refines _ _ t _ _ _ _ (ihc h.1) (ihb h.2) fuel
  | break_some ty e ih =>
    simp only [TExpr.erase, noVarRef] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    refine Refines.bind (ih h fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr; cf_cases r <;> exact Refines.pure _
  | earlyReturn ty e ih =>
    simp only [TExpr.erase, noVarRef] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    refine Refines.bind (ih h fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr; cf_cases r <;> exact Refines.pure _
  | questionMark ty e ih =>
    simp only [TExpr.erase, noVarRef] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    refine Refines.bind (ih h fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr; cf_cases r <;> exact Refines.pure _
  | cfBreak ty e ih =>
    simp only [TExpr.erase, noVarRef] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    refine Refines.bind (ih h fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr; cf_cases r <;> exact Refines.pure _
  | cfContinue ty e ih =>
    simp only [TExpr.erase, noVarRef] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    refine Refines.bind (ih h fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr; cf_cases r <;> exact Refines.pure _
  | cfBreakContinue ty e ih =>
    simp only [TExpr.erase, noVarRef] at h
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    refine Refines.bind (ih h fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr; cf_cases r <;> exact Refines.pure _
  | namedProj ty n e ih =>
    simp only [TExpr.erase, noVarRef, noVarRef.allExpr, Bool.and_true] at h
    simp only [tStructToTuple, tStructToTuple.goKind]
    have hk : ∀ (k : Option TExprKind) (e' : TExpr) (ty' : ImpType),
        (TExpr.mk (k.getD (.namedProj n e')) ty').erase =
          (TExpr.mk (k.getD (.app ".0" [e'])) ty').erase := by
      intro k e' ty'; cases k <;> rfl
    rw [hk]
    have := denote'_structApp sf S T hST t ".0" [e] (tyStructToTuple sf sf.length ty)
      (fun a ha => by rw [List.mem_singleton] at ha; subst ha; exact ih h) fuel
    simpa only [List.map_cons, List.map_nil, TExpr.erase] using this
  | _ =>
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denote']
    exact Refines.pure _

/-- The rewrite refines `denote'`: when the struct term `e`, whose erasure never reads the
    reserved name `t`, has an outcome that is not an error under `structBi sf bi`, the
    rewritten term has the same outcome under `bi`, from and to environments that agree
    except at `t`. -/
theorem denote'_tStructToTuple (sf : StructFieldTys) (bi : Builtins) (t : String) (e : TExpr)
    (h : noVarRef t e.erase = true) (fuel : Nat) :
    Refines isErr t (denote' (structBi sf bi) fuel e.erase)
      (denote' bi fuel (tStructToTuple sf t e).erase) :=
  denote'_tStructToTuple_of_structTab sf _ bi (StructTab.of_structBi sf bi) t e h fuel

/-- A call of a head without a struct role refines its rewrite under `denoteApp'`, given that
    its arguments do. -/
theorem denoteApp'_tStructToTuple (sf : StructFieldTys) (bi : Builtins) (t f : String)
    (args : List TExpr) (hf : structHead? sf f = none)
    (h : ∀ a ∈ args, noVarRef t a.erase = true) (fuel : Nat) :
    Refines isErr t (denoteApp' (structBi sf bi) fuel f (args.map TExpr.erase))
      (denoteApp' bi fuel f ((args.map (tStructToTuple sf t)).map TExpr.erase)) := by
  have := denote'_app_fallback sf (structBi sf bi) bi t f args
    (fun a ha fuel => denote'_tStructToTuple sf bi t a (h a ha) fuel)
    (fun vals _ _ v hv => by simpa [structBi, hf] using hv) fuel
  simpa only [denote'] using this

/-! ## Refinement of the spine reading `denoteSpine` -/

open InlineLocalClosures (denoteSpine inlineSpine closureOk blockOk closureTable bindAll)

/-- The side condition of `denoteSpine` on the rewrite: every closure binding on the statement
    spine of `e` that `denoteSpine` reads as a closure (`closureOk` or `blockOk` of the binding
    with its continuation inlined) is read as a closure after the rewrite too, and binds a name
    without a struct role. -/
def spineStructOk (sf : StructFieldTys) (t : String) : TExpr → Bool
  | .mk (.letBind f v cont) _ =>
    (match v.erase, (tStructToTuple sf t v).erase with
      | .lam ps body, .lam ps' body' =>
        !(closureOk f ps body (inlineSpine cont.erase) ||
            blockOk f ps body (inlineSpine cont.erase)) ||
          ((closureOk f ps' body' (inlineSpine (tStructToTuple sf t cont).erase) ||
              blockOk f ps' body' (inlineSpine (tStructToTuple sf t cont).erase)) &&
            (structHead? sf f).isNone)
      | _, _ => true) && spineStructOk sf t cont
  | .mk (.seq _ b) _ => spineStructOk sf t b
  | .mk (.ann e) _ => spineStructOk sf t e
  | _ => true

namespace StructTuple

theorem bindAll_agreeExcept {t : String} {ρ₁ ρ₂ : Env} (h : Env.AgreeExcept t ρ₁ ρ₂) :
    ∀ (ps : List String) (vals : List Value),
      Env.AgreeExcept t (bindAll ρ₁ ps vals) (bindAll ρ₂ ps vals)
  | [], _ => h
  | _ :: _, [] => h
  | p :: ps, v :: vs => by
    simp only [bindAll]
    exact (bindAll_agreeExcept h ps vs).extend p v

/-- The builtin table of a closure whose name has no struct role keeps `StructTab`, when the
    body refines its rewrite and the environments of the binding agree except at `t`. -/
theorem structTab_closureTable {sf : StructFieldTys} {S T : Builtins} (hST : StructTab sf S T)
    {t f : String} (hf : structHead? sf f = none) (fuel : Nat) (ps : List String)
    {body body' : ImpExpr} (hb : Refines isErr t (denote' S fuel body) (denote' T fuel body'))
    {ρ₁ ρ₂ : Env} (hρ : Env.AgreeExcept t ρ₁ ρ₂) :
    StructTab sf (closureTable S fuel f ps body ρ₁) (closureTable T fuel f ps body' ρ₂) := by
  intro g vals v hc h
  by_cases hg : g = f
  · subst hg
    simp only [structBi, hf]
    simp only [InlineLocalClosures.closureTable, ite_true] at h ⊢
    by_cases hl : vals.length = ps.length
    · simp only [hl, ite_true] at h ⊢
      rcases hd : (denote' S fuel body).run (bindAll ρ₁ ps vals) with ⟨o, s⟩
      rw [hd] at h
      cases o with
      | val w =>
        obtain ⟨ho, -⟩ := hb _ _ (bindAll_agreeExcept hρ ps vals)
          (by simp only [StateT.run] at hd; simp [hd, isErr])
        simp only [StateT.run] at hd ho ⊢
        rw [ho, hd]
        exact h
      | _ => simp at h
    · simp [hl] at h
  · have h' := hST g vals v hc (by simpa [InlineLocalClosures.closureTable, hg] using h)
    simp only [structBi] at h' ⊢
    cases hh : structHead? sf g with
    | none =>
      simp only [hh] at h' ⊢
      simpa [InlineLocalClosures.closureTable, hg] using h'
    | some r => simp only [hh] at h' ⊢; cases r <;> exact h'

/-- The spine reading of a binding whose value is no closure. -/
theorem denoteSpine_letBind_of_not_lam (bi : Builtins) (fuel : Nat) (x : String)
    (v cont : ImpExpr) (hv : ∀ ps b, v ≠ .lam ps b) :
    denoteSpine bi fuel (.letBind x v cont) = (do
      let rv ← denote' bi fuel v
      match rv with
      | .val (.controlFlow isBreak w) => pure (.val (.controlFlow isBreak w))
      | .val w => do modify (Env.extend · x w); denoteSpine bi fuel cont
      | other => pure other) := by
  cases v <;> first | exact absurd rfl (hv _ _) | rfl

/-- The spine reading of an expression that is neither a binding nor a sequence is
    `denote'`. -/
theorem denoteSpine_of_not_spine (bi : Builtins) (fuel : Nat) (e : ImpExpr)
    (h1 : ∀ x v c, e ≠ .letBind x v c) (h2 : ∀ a b, e ≠ .seq a b) :
    denoteSpine bi fuel e = denote' bi fuel e := by
  cases e <;> first | exact absurd rfl (h1 _ _ _) | exact absurd rfl (h2 _ _) | rfl

/-- The spine reading of a binding of a tuple followed by a tuple is `denote'`. -/
theorem denoteSpine_letBind_tuple (bi : Builtins) (fuel : Nat) (x : String)
    (xs ys : List ImpExpr) :
    denoteSpine bi fuel (.letBind x (.tuple xs) (.tuple ys)) =
      denote' bi fuel (.letBind x (.tuple xs) (.tuple ys)) := by
  rw [denoteSpine_letBind_of_not_lam bi fuel x _ _ (fun _ _ h => by cases h),
    denoteSpine_of_not_spine bi fuel _ (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)]
  simp only [denote']; rfl

/-- The erasure of a term is a closure exactly when the erasure of its rewrite is, with the
    rewritten body. -/
theorem erase_tStructToTuple_lam (sf : StructFieldTys) (t : String) :
    ∀ (v : TExpr) (ps : List String) (body : ImpExpr), v.erase = .lam ps body →
      ∃ b : TExpr, body = b.erase ∧
        (tStructToTuple sf t v).erase = .lam ps (tStructToTuple sf t b).erase := by
  intro v
  induction v using TExpr.ind with
  | lam ty ps' b ih =>
    intro ps body h
    simp only [TExpr.erase, ImpExpr.lam.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨b, rfl, by simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase]⟩
  | ann ty e ih =>
    intro ps body h
    simp only [TExpr.erase] at h
    obtain ⟨b, hb, he⟩ := ih ps body h
    exact ⟨b, hb, by simpa only [tStructToTuple, tStructToTuple.goKind, TExpr.erase] using he⟩
  | _ => intro ps body h; simp [TExpr.erase] at h

theorem erase_tStructToTuple_not_lam (sf : StructFieldTys) (t : String) :
    ∀ (v : TExpr), (∀ ps b, v.erase ≠ .lam ps b) →
      ∀ ps b, (tStructToTuple sf t v).erase ≠ .lam ps b := by
  intro v
  induction v using TExpr.ind with
  | lam ty ps' b ih => intro h; exact absurd rfl (h ps' b.erase)
  | ann ty e ih =>
    intro h
    simpa only [tStructToTuple, tStructToTuple.goKind, TExpr.erase] using
      ih (by simpa only [TExpr.erase] using h)
  | app ty f args ih =>
    intro _ ps b
    simp only [tStructToTuple, tStructToTuple.goKind, structApp]
    split <;> simp [TExpr.erase]
  | namedProj ty n e ih =>
    intro _ ps b
    simp only [tStructToTuple, tStructToTuple.goKind, structApp]
    split <;> simp [TExpr.erase]
  | _ => intro _ ps b; simp [tStructToTuple, tStructToTuple.goKind, TExpr.erase]

/-- On a term that is neither a binding, a sequence nor an annotation, the spine readings of
    the term and of its rewrite are `denote'`. -/
theorem denoteSpine_tStructToTuple_nonspine (sf : StructFieldTys) (t : String) (S T : Builtins)
    (fuel : Nat) (k : TExprKind) (ty : ImpType)
    (h1 : ∀ n v b, k ≠ .letBind n v b) (h2 : ∀ a b, k ≠ .seq a b) (h3 : ∀ e, k ≠ .ann e) :
    denoteSpine S fuel (TExpr.mk k ty).erase = denote' S fuel (TExpr.mk k ty).erase ∧
      denoteSpine T fuel (tStructToTuple sf t (.mk k ty)).erase =
        denote' T fuel (tStructToTuple sf t (.mk k ty)).erase := by
  cases k
  case letBind n v b => exact absurd rfl (h1 n v b)
  case seq a b => exact absurd rfl (h2 a b)
  case ann e => exact absurd rfl (h3 e)
  case app f args =>
    refine ⟨denoteSpine_of_not_spine _ _ _ (by simp [TExpr.erase]) (by simp [TExpr.erase]), ?_⟩
    simp only [tStructToTuple, tStructToTuple.goKind, structApp]
    split <;> simp only [Option.getD_some, Option.getD_none, TExpr.erase, TExpr.eraseList_eq] <;>
      first
        | exact denoteSpine_letBind_tuple _ _ _ _ _
        | exact denoteSpine_of_not_spine _ _ _ (by simp) (by simp)
  case namedProj n e =>
    refine ⟨denoteSpine_of_not_spine _ _ _ (by simp [TExpr.erase]) (by simp [TExpr.erase]), ?_⟩
    simp only [tStructToTuple, tStructToTuple.goKind, structApp]
    split <;> simp only [Option.getD_some, Option.getD_none, TExpr.erase, TExpr.eraseList_eq] <;>
      first
        | exact denoteSpine_letBind_tuple _ _ _ _ _
        | exact denoteSpine_of_not_spine _ _ _ (by simp) (by simp)
  case break_ o =>
    cases o <;>
    exact ⟨denoteSpine_of_not_spine _ _ _ (by simp [TExpr.erase]) (by simp [TExpr.erase]),
      denoteSpine_of_not_spine _ _ _ (by simp [tStructToTuple, tStructToTuple.goKind, TExpr.erase])
        (by simp [tStructToTuple, tStructToTuple.goKind, TExpr.erase])⟩
  all_goals
    exact ⟨denoteSpine_of_not_spine _ _ _ (by simp [TExpr.erase]) (by simp [TExpr.erase]),
      denoteSpine_of_not_spine _ _ _ (by simp [tStructToTuple, tStructToTuple.goKind, TExpr.erase])
        (by simp [tStructToTuple, tStructToTuple.goKind, TExpr.erase])⟩

/-- On a term that is neither a binding, a sequence nor an annotation, refinement of the spine
    readings follows from refinement under `denote'`. -/
theorem refines_denoteSpine_of_nonspine (sf : StructFieldTys) (t : String) (S T : Builtins)
    (fuel : Nat) (k : TExprKind) (ty : ImpType)
    (h1 : ∀ n v b, k ≠ .letBind n v b) (h2 : ∀ a b, k ≠ .seq a b) (h3 : ∀ e, k ≠ .ann e)
    (hr : Refines isErr t (denote' S fuel (TExpr.mk k ty).erase)
      (denote' T fuel (tStructToTuple sf t (.mk k ty)).erase)) :
    Refines isErr t (denoteSpine S fuel (TExpr.mk k ty).erase)
      (denoteSpine T fuel (tStructToTuple sf t (.mk k ty)).erase) := by
  obtain ⟨hS, hT⟩ := denoteSpine_tStructToTuple_nonspine sf t S T fuel k ty h1 h2 h3
  rw [hS, hT]
  exact hr

end StructTuple

/-- The rewrite refines the spine reading `denoteSpine` over builtin tables `S` and `T` with
    `StructTab sf S T`: when the struct term `e`, whose erasure never reads the reserved name
    `t` and whose spine satisfies `spineStructOk`, has an outcome that is not an error under
    `S`, the rewritten term has the same outcome under `T`, from and to environments that agree
    except at `t`. -/
theorem denoteSpine_tStructToTuple_of_structTab (sf : StructFieldTys) (t : String)
    (fuel : Nat) (e : TExpr) :
    ∀ (S T : Builtins), StructTab sf S T → noVarRef t e.erase = true →
      spineStructOk sf t e = true →
      Refines isErr t (denoteSpine S fuel e.erase)
        (denoteSpine T fuel (tStructToTuple sf t e).erase) := by
  induction e using TExpr.ind with
  | letBind ty n v b ihv ihb =>
    intro S T hST h hok
    simp only [TExpr.erase, noVarRef, Bool.and_eq_true] at h
    by_cases hl : ∃ ps body, v.erase = .lam ps body
    · obtain ⟨ps, body, hv⟩ := hl
      obtain ⟨bT, rfl, hv'⟩ := erase_tStructToTuple_lam sf t v ps body hv
      have hnb : noVarRef t bT.erase = true := by simpa [hv, noVarRef] using h.1
      simp only [spineStructOk, hv, hv', Bool.and_eq_true] at hok
      obtain ⟨hg, hokb⟩ := hok
      simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, hv, hv', denoteSpine]
      cases hg₁ : (closureOk n ps bT.erase (inlineSpine b.erase) ||
          blockOk n ps bT.erase (inlineSpine b.erase))
      · simp only [Bool.false_eq_true, ite_false]
        refine Refines.of_bad (fun s => ?_)
        obtain ⟨m, hm⟩ := InlineLocalClosures.denote'_letBind_lam_err S fuel n ps bT.erase
          b.erase s
        simp only [StateT.run] at hm
        rw [hm]; rfl
      · simp only [hg₁, Bool.not_true, Bool.false_or, Bool.and_eq_true,
          Option.isNone_iff_eq_none] at hg
        obtain ⟨hg₂, hn⟩ := hg
        simp only [hg₂, ite_true]
        intro s₁ s₂ hs hb
        simp only [stateM_bind_apply, stateM_get_apply] at hb ⊢
        exact ihb _ _ (structTab_closureTable hST hn fuel ps
          (denote'_tStructToTuple_of_structTab sf S T hST t bT hnb fuel) hs) h.2 hokb s₁ s₂ hs hb
    · have hnl : ∀ ps body, v.erase ≠ .lam ps body := fun ps body he => hl ⟨ps, body, he⟩
      have hnl' := erase_tStructToTuple_not_lam sf t v hnl
      have hokb : spineStructOk sf t b = true := by
        simp only [spineStructOk, Bool.and_eq_true] at hok
        exact hok.2
      simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase]
      rw [denoteSpine_letBind_of_not_lam _ _ _ _ _ hnl,
        denoteSpine_letBind_of_not_lam _ _ _ _ _ hnl']
      refine Refines.bind (denote'_tStructToTuple_of_structTab sf S T hST t v h.1 fuel) ?_ ?_
      · intro a s ha; cases a <;> simp_all [isErr, stateM_pure_apply]
      · intro a ha
        cf_cases a <;> first
          | exact Refines.pure _
          | exact Refines.bind (Refines.modify_extend n _) (by simp)
              (fun _ _ => ihb S T hST h.2 hokb)
  | seq ty a b iha ihb =>
    intro S T hST h hok
    simp only [TExpr.erase, noVarRef, Bool.and_eq_true] at h
    simp only [spineStructOk] at hok
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase, denoteSpine]
    refine Refines.bind (denote'_tStructToTuple_of_structTab sf S T hST t a h.1 fuel) ?_ ?_
    · intro r s hr; cases r <;> simp_all [isErr, stateM_pure_apply]
    · intro r hr
      cf_cases r <;> first | exact Refines.pure _ | exact ihb S T hST h.2 hok
  | ann ty e ih =>
    intro S T hST h hok
    simp only [TExpr.erase] at h
    simp only [spineStructOk] at hok
    simp only [tStructToTuple, tStructToTuple.goKind, TExpr.erase]
    exact ih S T hST h hok
  | _ =>
    intro S T hST h _
    refine refines_denoteSpine_of_nonspine sf t S T fuel _ _ ?_ ?_ ?_
      (denote'_tStructToTuple_of_structTab sf S T hST t _ h fuel) <;> simp

/-- The rewrite refines the spine reading `denoteSpine`, the reading of a function body by
    `compileA`'s run semantics: when the struct term `e`, whose erasure never reads the reserved
    name `t` and whose spine satisfies `spineStructOk`, has an outcome that is not an error
    under `structBi sf bi`, the rewritten term has the same outcome under `bi`, from and to
    environments that agree except at `t`. -/
theorem denoteSpine_tStructToTuple (sf : StructFieldTys) (bi : Builtins) (t : String)
    (e : TExpr) (h : noVarRef t e.erase = true) (hok : spineStructOk sf t e = true)
    (fuel : Nat) :
    Refines isErr t (denoteSpine (structBi sf bi) fuel e.erase)
      (denoteSpine bi fuel (tStructToTuple sf t e).erase) :=
  denoteSpine_tStructToTuple_of_structTab sf t fuel e _ bi (StructTab.of_structBi sf bi) h hok

end Hax
