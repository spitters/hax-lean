/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.HaxAdapter
public import HaxLean.PrettyPrint

/-!
# Trait-to-class emission

The opt-in `--emit-classes <trait-export.json>` mode of haxpipeT. It reads the
Rust trait definitions of a hax frontend export (the export of the crate that
defines the traits, together with the traits the extracted crate defines
itself) and renders:

* one Lean `class` per trait, over the trait's `Self` type: a field per
  associated type (with its trait bounds as instance fields), per associated
  constant and per method; supertraits of a non-builtin crate become `extends`
  clauses;
* an `export` of each trait method or constant the extracted crate calls
  through a trait bound of a generic function (an `in_trait.impl` atom of kind
  `LocalBound`), so the call's bare name resolves to the class field, and those
  names leave the generated `Deps` class;
* each generic function with its type parameters and trait bounds as binders,
  `def f {F : Type} [CtField F] …`;
* each generic struct as a type-parametric tuple abbreviation with a
  parametric constructor and projections;
* each trait `impl` of the extracted crate as an `instance`, whose fields name
  the definitions the adapter emits for the `impl`'s methods and associated
  constants (`buildTraitImplMethodMap`, `buildTraitImplConstMap`).

A type parameter reaches the renderer as `ImpType.typeVar`: `keepTypeParams`
rewrites every `Param` type of the export to a `TypeVar` node before the
adapter parses it. A generic struct is looked up through a template over its
type arguments (`ImpType.fillTypeArgs`), so `RPoint<F>` renders as
`RPoint_T F` and `RPoint<Fe51>` as `RPoint_T Fe51_T`.

The definitions are emitted in dependency order outside a `mutual` block when
their call graph has no cycle besides self-recursion, so that each instance can
stand after the definitions it names and before the definitions that use it
(`orderBody`).

The `ImpExpr` and `TExpr` literals are emitted as in the default mode.
-/

@[expose] public section

namespace Hax.ClassEmit

open Lean (Json)
open Hax.HaxAdapter (parseHaxType defIdLeafName defIdKrate defIdPathNames
  builtinKrates extractFnName buildTraitImplMethodMap buildTraitImplConstMap)

/-! ## Export rewriting -/

/-- The associated-type name of a projection `Self::Name`, from the `Alias`
    node of the type: a projection whose trait reference has the type parameter
    `Self` as its self argument. Inside a trait definition hax resolves such a
    projection through `SelfImpl` or through the `Self: Trait` bound
    (`LocalBound`); either way the self argument is `Self`. -/
def selfAssocName (alias : Json) : Option String := do
  let kind ← (alias.getObjVal? "kind").toOption
  let proj ← (kind.getObjVal? "Projection").toOption
  let ie ← (proj.getObjVal? "impl_expr").toOption
  let tr ← (ie.getObjVal? "trait").toOption
  let tv ← (tr.getObjVal? "value").toOption
  let tvv ← (tv.getObjVal? "value").toOption
  let args ← (tvv.getObjValAs? (Array Json) "generic_args").toOption
  let a0 ← args[0]?
  let ty ← (a0.getObjVal? "Type").toOption
  let tyv ← (ty.getObjVal? "value").toOption
  let p ← (tyv.getObjVal? "Param").toOption
  guard ((p.getObjValAs? String "name").toOption == some "Self")
  let item ← (proj.getObjVal? "assoc_item").toOption
  let defId ← (item.getObjVal? "def_id").toOption
  defIdLeafName defId

/-- Rewrite every type-parameter node `{"Param": {"index": i, "name": n}}` of
    a hax export to `{"TypeVar": n}`, and every projection `Self::A` through the
    enclosing trait to `{"TypeVar": A}`. `HaxAdapter.parseHaxType` reads the
    rewritten node as `ImpType.typeVar n`; it reads a `Param` as `.slice .int`. -/
partial def keepTypeParams (j : Json) : Json :=
  match j with
  | .arr xs => .arr (xs.map keepTypeParams)
  | .obj t =>
    match t.toList with
    | [("Param", p)] =>
      match p.getObjValAs? String "name" with
      | .ok n => Json.mkObj [("TypeVar", .str n)]
      | _ => Json.mkObj [("Param", keepTypeParams p)]
    | [("Alias", a)] =>
      match selfAssocName a with
      | some n => Json.mkObj [("TypeVar", .str n)]
      | none => Json.mkObj [("Alias", keepTypeParams a)]
    | kvs => Json.mkObj (kvs.map fun (k, v) => (k, keepTypeParams v))
  | _ => j

/-- Every item of an export, with the sub-items of each `Mod` item after it. -/
partial def allItems (j : Json) : List Json :=
  match j with
  | .arr xs => xs.toList.flatMap fun it =>
    let sub : List Json := match it.getObjVal? "kind" with
      | .ok k =>
        match k.getObjVal? "Mod" with
        | .ok (.arr md) => (md[1]?.map allItems).getD []
        | .ok md =>
          match md.getObjValAs? (Array Json) "items" with
          | .ok s => allItems (.arr s)
          | _ => []
        | _ => []
      | _ => []
    it :: sub
  | _ => []

/-! ## Trait definitions -/

/-- A Rust trait definition, as the class it is emitted as. Types are read
    from an export rewritten by `keepTypeParams`, so `Self` is
    `.typeVar "Self"` and an associated type `A` is `.typeVar "A"`. -/
structure TraitDef where
  /-- The trait's short name. -/
  name : String
  /-- The crate defining the trait. -/
  krate : String
  /-- The supertraits outside `core`, `alloc` and `std`, by short name. -/
  supers : List String := []
  /-- Associated types, each with the short names of its trait bounds. -/
  assocTypes : List (String × List String) := []
  /-- Associated constants with their types. -/
  consts : List (String × ImpType) := []
  /-- Methods with their named parameters and result type. -/
  methods : List (String × List (String × ImpType) × ImpType) := []
  deriving Inhabited

/-- The short names of the traits outside `core`, `alloc` and `std` among a
    list of hax clauses (`{kind: {value: {Trait: {trait_ref}}}}`). -/
def localTraitsOfClauses (clauses : Json) : List String :=
  match clauses with
  | .arr cs => cs.toList.filterMap fun c => do
    let k ← (c.getObjVal? "kind").toOption
    let v ← (k.getObjVal? "value").toOption
    let tr ← (v.getObjVal? "Trait").toOption
    let tref ← (tr.getObjVal? "trait_ref").toOption
    let tv ← (tref.getObjVal? "value").toOption
    let defId ← (tv.getObjVal? "def_id").toOption
    guard (!builtinKrates.contains (defIdKrate defId))
    defIdLeafName defId
  | _ => []

/-- The parameter names and types and the result type of a trait method,
    from the `[signature, parameter idents]` payload of a `RequiredFn` or
    `ProvidedFn` item. A parameter without an ident is named `a<i>`. -/
def traitFnSig (f : Array Json) : List (String × ImpType) × ImpType :=
  let decl := (f[0]? >>= fun s => (s.getObjVal? "decl").toOption).getD .null
  let inputs := match decl.getObjValAs? (Array Json) "inputs" with
    | .ok xs => xs.toList
    | _ => []
  let names : List String := match f[1]? with
    | some (Json.arr ids) => ids.toList.map extractFnName
    | _ => []
  let params := ((List.range inputs.length).zip inputs).map fun (i, ty) =>
    let n := match names[i]? with
      | some n => if n == "unknown_fn" || n == "_" then s!"a{i}" else n
      | none => s!"a{i}"
    (n, parseHaxType ty)
  let ret := match decl.getObjVal? "output" with
    | .ok o => match o.getObjVal? "Return" with
      | .ok ty => parseHaxType ty
      | _ => .unit
    | _ => .unit
  (params, ret)

/-- Add one item of a trait definition (associated constant, method or type). -/
def addTraitItem (td : TraitDef) (it : Json) : TraitDef :=
  let name := match it.getObjVal? "ident" with
    | .ok i => extractFnName i
    | _ => "unknown_fn"
  match it.getObjVal? "kind" with
  | .ok k =>
    if let .ok (.arr c) := k.getObjVal? "Const" then
      match c[0]? with
      | some ty => { td with consts := td.consts ++ [(name, parseHaxType ty)] }
      | none => td
    else if let .ok (.arr f) := k.getObjVal? "RequiredFn" then
      { td with methods := td.methods ++ [(name, traitFnSig f)] }
    else if let .ok (.arr f) := k.getObjVal? "ProvidedFn" then
      { td with methods := td.methods ++ [(name, traitFnSig f)] }
    else if let .ok (.arr ty) := k.getObjVal? "Type" then
      let bounds := (ty[0]?.map localTraitsOfClauses).getD []
      { td with assocTypes := td.assocTypes ++ [(name, bounds)] }
    else td
  | _ => td

/-- The trait definitions of an export rewritten by `keepTypeParams`, one per
    trait name, in export order. A trait item is `Trait: [constness, auto,
    safety, ident, generics, supertrait clauses, items]`. -/
def parseTraitDefs (j : Json) : List TraitDef :=
  let defs := (allItems j).filterMap fun it => do
    let k ← (it.getObjVal? "kind").toOption
    let tr ← (k.getObjValAs? (Array Json) "Trait").toOption
    let name := extractFnName (tr[3]?.getD .null)
    let krate := match it.getObjVal? "owner_id" with
      | .ok oid => defIdKrate oid
      | _ => ""
    let supers := (tr[5]?.map localTraitsOfClauses).getD []
    let items := match tr[6]? with
      | some (.arr xs) => xs.toList
      | _ => []
    some (items.foldl addTraitItem { name, krate, supers })
  defs.foldl (fun acc d => if acc.any (·.name == d.name) then acc else acc ++ [d]) []

/-- Order trait definitions so that each follows its supertraits. -/
def orderTraits (tds : List TraitDef) : List TraitDef :=
  let rec go (fuel : Nat) (done : List TraitDef) (rest : List TraitDef) : List TraitDef :=
    match fuel with
    | 0 => done ++ rest
    | fuel + 1 =>
      let (ready, blocked) := rest.partition fun td =>
        td.supers.all fun s => done.any (·.name == s) || !tds.any (·.name == s)
      if ready.isEmpty then done ++ rest else go fuel (done ++ ready) blocked
  go tds.length [] tds

/-! ## What the extracted crate uses -/

/-- A generic function of the extracted crate: its type parameters and its
    trait bounds `(trait, type parameter)` over the known traits. -/
structure GenericFn where
  name : String
  typeParams : List String
  bounds : List (String × String)
  deriving Inhabited

/-- The type-parameter names of a hax `generics` node. -/
def typeParamNames (generics : Json) : List String :=
  match generics.getObjValAs? (Array Json) "params" with
  | .ok ps => ps.toList.filterMap fun p => do
    let k ← (p.getObjVal? "kind").toOption
    let _ ← (k.getObjVal? "Type").toOption
    let n ← (p.getObjVal? "name").toOption
    let plain ← (n.getObjVal? "Plain").toOption
    (plain.getObjValAs? String "name").toOption
  | _ => []

/-- The bounds `(trait, type parameter)` of a hax `generics` node whose trait
    is among `traits` and whose self argument is a type parameter. -/
def typeParamBounds (traits : List String) (generics : Json) : List (String × String) :=
  match generics.getObjValAs? (Array Json) "bounds" with
  | .ok bs => bs.toList.filterMap fun b => do
    let k ← (b.getObjVal? "kind").toOption
    let v ← (k.getObjVal? "value").toOption
    let tr ← (v.getObjVal? "Trait").toOption
    let tref ← (tr.getObjVal? "trait_ref").toOption
    let tv ← (tref.getObjVal? "value").toOption
    let defId ← (tv.getObjVal? "def_id").toOption
    let tn ← defIdLeafName defId
    guard (traits.contains tn)
    let args ← (tv.getObjValAs? (Array Json) "generic_args").toOption
    let a0 ← args[0]?
    let ty ← (a0.getObjVal? "Type").toOption
    let tyv ← (ty.getObjVal? "value").toOption
    let p ← (tyv.getObjValAs? String "TypeVar").toOption
    some (tn, p)
  | _ => []

/-- The generic top-level functions of an export rewritten by
    `keepTypeParams`, one per name. -/
def genericFns (traits : List String) (j : Json) : List GenericFn :=
  let fs := (allItems j).filterMap fun it => do
    let k ← (it.getObjVal? "kind").toOption
    let f ← (k.getObjVal? "Fn").toOption
    let ident ← (f.getObjVal? "ident").toOption
    let g ← (f.getObjVal? "generics").toOption
    let ps := typeParamNames g
    guard (!ps.isEmpty)
    some { name := extractFnName ident, typeParams := ps, bounds := typeParamBounds traits g }
  fs.foldl (fun acc f => if acc.any (·.name == f.name) then acc else acc ++ [f]) []

/-- The generic structs of an export, with their type-parameter names. A
    struct item is `Struct: [ident, generics, …]`. -/
def genericStructs (j : Json) : List (String × List String) :=
  let ss := (allItems j).filterMap fun it => do
    let k ← (it.getObjVal? "kind").toOption
    let s ← (k.getObjValAs? (Array Json) "Struct").toOption
    let name := extractFnName (s[0]?.getD .null)
    let ps := typeParamNames (s[1]?.getD .null)
    guard (!ps.isEmpty)
    some (ImpType.sanitizeAdtShortName name, ps)
  ss.foldl (fun acc s => if acc.any (·.1 == s.1) then acc else acc ++ [s]) []

/-- The trait items the crate reads through a trait bound, as
    `(item, defining trait)`: every node carrying an `in_trait` whose `impl`
    atom is `LocalBound`, named by the leaf of its `def_id`, whose parent is the
    trait that defines the item. Items of a trait of `core`, `alloc` or `std`
    are left out. -/
partial def localBoundItems (j : Json) (acc : Array (String × String) := #[]) :
    Array (String × String) :=
  match j with
  | .arr xs => xs.foldl (fun a x => localBoundItems x a) acc
  | .obj t =>
    let here : Option (String × String) := do
      let it ← (j.getObjVal? "in_trait").toOption
      let impl ← (it.getObjVal? "impl").toOption
      let _ ← (impl.getObjVal? "LocalBound").toOption
      let defId ← (j.getObjVal? "def_id").toOption
      guard (!builtinKrates.contains (defIdKrate defId))
      match (defIdPathNames defId).reverse with
      | item :: trait :: _ => some (item, trait)
      | _ => none
    let acc := match here with
      | some p => if acc.contains p then acc else acc.push p
      | none => acc
    t.toList.foldl (fun a (_, v) => localBoundItems v a) acc
  | _ => acc

/-- A trait `impl` of the extracted crate, as the instance it is emitted as:
    the trait, the self type and, per trait item, the emitted definition. -/
structure ImplInstance where
  trait : String
  selfTy : ImpType
  fields : List (String × String)
  deriving Inhabited

/-- The trait `impl`s of the extracted crate whose trait is among `traits`,
    one per `impl` block. The fields are the entries of
    `buildTraitImplMethodMap` and `buildTraitImplConstMap` for the block. -/
def implInstances (traits : List String) (j : Json) : List ImplInstance :=
  let items := buildTraitImplMethodMap j ++ buildTraitImplConstMap j
  let found := (allItems j).filterMap fun it => do
    let k ← (it.getObjVal? "kind").toOption
    let impl ← (k.getObjVal? "Impl").toOption
    let tr ← (impl.getObjVal? "of_trait").toOption
    let tv ← (tr.getObjVal? "value").toOption
    let defId ← (tv.getObjVal? "def_id").toOption
    let tn ← defIdLeafName defId
    guard (traits.contains tn)
    let oid ← (it.getObjVal? "owner_id").toOption
    let c ← (oid.getObjVal? "contents").toOption
    let implId ← (c.getObjValAs? Nat "id").toOption
    let v ← (c.getObjVal? "value").toOption
    guard ((v.getObjValAs? Bool "is_local").toOption == some true)
    let selfTy := match impl.getObjVal? "self_ty" with
      | .ok st => parseHaxType st
      | _ => .unknown
    let fields := ((items.filter (·.1 == implId)).map fun (_, item, emitted) =>
      (item, emitted)).eraseDups
    some (implId, { trait := tn, selfTy, fields : ImplInstance })
  (found.foldl (fun acc p => if acc.any (·.1 == p.1) then acc else acc ++ [p]) []).map (·.2)

/-! ## The plan handed to the renderer -/

/-- Everything the class mode adds to the typed renderer
    (`toLeanCertifiedFileTyped`). The default value is the default mode: the
    renderer consults each field only when it is non-empty. -/
structure ClassHooks where
  /-- The traits emitted as classes, supertraits first. -/
  traits : List TraitDef := []
  /-- Per trait, the item names exported to the module namespace. -/
  exports : List (String × List String) := []
  /-- Generic functions, with their binders. -/
  genericFns : List GenericFn := []
  /-- Generic structs, with their type parameters. -/
  genericStructs : List (String × List String) := []
  /-- The trait `impl`s emitted as instances. -/
  instances : List ImplInstance := []
  deriving Inhabited

/-- Whether the class mode is on. -/
def ClassHooks.enabled (h : ClassHooks) : Bool := !h.traits.isEmpty

/-- The item names exported from the classes; they are not `Deps` fields. -/
def ClassHooks.classItemNames (h : ClassHooks) : List String := h.exports.flatMap (·.2)

/-- The plan for an extracted crate (`crate`) and the definitions of the traits
    it uses (`traitExport`), both rewritten by `keepTypeParams`. The traits are
    those of `traitExport` and of `crate`. -/
def plan (traitExport crate : Json) : ClassHooks :=
  let traits := orderTraits (parseTraitDefs traitExport ++ parseTraitDefs crate)
  let names := traits.map (·.name)
  let used := (localBoundItems crate).toList.filter fun (_, t) => names.contains t
  let exports := names.filterMap fun t =>
    let items := (used.filter (·.2 == t)).map (·.1)
    if items.isEmpty then none else some (t, items)
  { traits, exports
    genericFns := genericFns names crate
    genericStructs := genericStructs crate
    instances := implInstances names crate }

/-! ## Rendering -/

/-- A struct lookup that resolves each generic struct to its template
    `S_T ⟪0⟫ … ⟪n-1⟫` (`ImpType.fillTypeArgs`) and every other name through `sl`. -/
def ClassHooks.wrapLookup (h : ClassHooks) (sl : String → Option String) :
    String → Option String :=
  if h.genericStructs.isEmpty then sl else fun n =>
    let short := ImpType.sanitizeAdtShortName n
    match h.genericStructs.find? (·.1 == short) with
    | some (s, ps) =>
      some (" ".intercalate
        (s!"{sanitizeName s}_T" :: (List.range ps.length).map ImpType.typeArgSlot))
    | none => sl n

/-- The opaque type names the class signatures and instance heads mention. -/
def ClassHooks.opaqueNames (h : ClassHooks) (sl : String → Option String) : List String :=
  let tys := h.traits.flatMap (fun td =>
      td.consts.map (·.2) ++ td.methods.flatMap fun (_, ps, r) => r :: ps.map (·.2))
    ++ h.instances.map (·.selfTy)
  (tys.flatMap (·.collectOpaqueAdtNames sl)).eraseDups

/-- A type rendered for a binder or a field, parenthesized when it has a
    space. -/
def argTypeStr (sl : String → Option String) (ty : ImpType) : String :=
  let s := ty.toLeanTypeStrSurface sl
  if s.any (· == ' ') then s!"({s})" else s

/-- The class declarations and the `export` lines. -/
def ClassHooks.renderClasses (h : ClassHooks) (sl : String → Option String) : String :=
  let known := h.traits.map (·.name)
  let classes := h.traits.map fun td =>
    let supers := td.supers.filter known.contains
    let ext := if supers.isEmpty then ""
      else " extends " ++ ", ".intercalate (supers.map fun s => s!"{s} Self")
    let assoc := td.assocTypes.flatMap fun (a, bs) =>
      s!"  {sanitizeName a} : Type" ::
        (bs.filter known.contains).map fun b => s!"  [inst{b}_{a} : {b} {sanitizeName a}]"
    let consts := td.consts.map fun (c, ty) =>
      s!"  {sanitizeName c} : {ty.toLeanTypeStrSurface sl}"
    let methods := td.methods.map fun (m, ps, r) =>
      let binders := ps.map fun (p, ty) => s!" ({sanitizeName p} : {ty.toLeanTypeStrSurface sl})"
      s!"  {sanitizeName m}{String.join binders} : {r.toLeanTypeStrSurface sl}"
    let attrs := td.assocTypes.flatMap fun (a, bs) =>
      (bs.filter known.contains).map fun b =>
        s!"\nattribute [instance_reducible, instance] {td.name}.inst{b}_{a}"
    s!"/-- The Rust trait `{td.name}` of the crate `{td.krate}`, as a class over its `Self` type. -/\nclass {td.name} (Self : Type){ext} where\n"
      ++ "\n".intercalate (assoc ++ consts ++ methods) ++ String.join attrs
  let exports := h.exports.map fun (t, items) =>
    s!"export {t} ({" ".intercalate (items.map sanitizeName)})"
  "\n\n".intercalate classes ++ "\n\n" ++ "\n".intercalate exports ++ "\n\n"

/-- The generic structs: a type-parametric tuple abbreviation, constructor and
    projections for each, rendered from its fields in `structMeta`. -/
def ClassHooks.renderGenericStructs (h : ClassHooks) (structMeta : StructMeta)
    (sl : String → Option String) : String :=
  let blocks := h.genericStructs.filterMap fun (s, ps) => do
    let (_, fields) ← structMeta.find? (·.1 == s)
    guard (!fields.isEmpty)
    let sn := sanitizeName s
    let params := " ".intercalate ps
    let binders := " ".intercalate (ps.map fun p => s!"\{{p} : Type}")
    let fieldTys := fields.map fun (_, _, ty) => ty.toLeanTypeStrSurface sl
    let tuple := " × ".intercalate (fieldTys.map fun t =>
      if (t.splitOn " × ").length > 1 then s!"({t})" else t)
    let abbrevBinders := " ".intercalate (ps.map fun p => s!"({p} : Type)")
    let ctorParams := " ".intercalate ((fields.zip fieldTys).map fun ((f, _, _), t) =>
      s!"({sanitizeName f} : {t})")
    let ctorBody := if fields.length == 1 then sanitizeName fields.head!.1
      else "(" ++ ", ".intercalate (fields.map fun (f, _, _) => sanitizeName f) ++ ")"
    let projs := (fields.zip (List.range fields.length)).map fun ((f, _, _), i) =>
      s!"def «.{f}» {binders} (x : {sn}_T {params}) := x{projPath i fields.length}"
    some (s!"/-- Tuple-encoded type for the generic Rust struct `{s}`. -/\nabbrev {sn}_T {abbrevBinders} := {tuple}\n\n"
      ++ s!"/-- Constructor and projections of the generic Rust struct `{s}`. -/\ndef {sn} {binders} {ctorParams} : {sn}_T {params} := {ctorBody}\n\n"
      ++ "\n\n".intercalate projs)
  if blocks.isEmpty then "" else "\n\n".intercalate blocks ++ "\n\n"

/-- The binders of a generic function: `{F : Type} [Inhabited F] [CtField F]`.
    The `Inhabited` binder is what the runtime's total indexing and default
    values (`Hax.index`, `Hax.repeat_`) ask of an element type. -/
def GenericFn.binders (g : GenericFn) : String :=
  " ".intercalate (g.typeParams.map (fun p => s!"\{{p} : Type} [Inhabited {p}]")
    ++ g.bounds.map fun (t, p) => s!"[{t} {p}]")

/-- A rendered definition with the binders of its generic function inserted
    after `def <name>`. Other definitions are returned unchanged. -/
def ClassHooks.addBinders (h : ClassHooks) (name text : String) : String :=
  match h.genericFns.find? (·.name == name) with
  | none => text
  | some g =>
    let pfx := s!"def {sanitizeName name}"
    if text.startsWith pfx then
      pfx ++ " " ++ g.binders ++ (text.drop pfx.length).toString
    else text

/-- The instance declaration of a trait `impl`. A supertrait's field is filled
    by instance resolution, from the instance of the supertrait at the same
    self type. -/
def ClassHooks.renderInstance (h : ClassHooks) (sl : String → Option String)
    (inst : ImplInstance) : String :=
  let supers := match h.traits.find? (·.name == inst.trait) with
    | some td => td.supers.filter fun s => h.traits.any (·.name == s)
    | none => []
  let superFields := supers.map fun s => s!"  to{s} := inferInstance"
  let fields := inst.fields.map fun (item, d) => s!"  {sanitizeName item} := {d}"
  s!"instance : {inst.trait} {argTypeStr sl inst.selfTy} where\n"
    ++ "\n".intercalate (superFields ++ fields) ++ "\n"

/-- The rendered definitions and instances in dependency order, or `none` when
    the call graph of the definitions has a cycle other than self-recursion.

    `defs` pairs each definition's name and rendered text with the names its
    body refers to. An instance follows the definitions it names and the
    instances of its supertraits at the same self type; a non-generic
    definition that calls a generic one follows every instance, since the call
    is resolved at a concrete type by instance search. Ties keep the input
    order. -/
def ClassHooks.orderBody (h : ClassHooks) (sl : String → Option String)
    (defs : List (String × String × List String)) : Option (List String) :=
  let defNames := defs.map (·.1)
  let genericNames := h.genericFns.map (·.name)
  let instIds := (List.range h.instances.length).map fun i => s!"instance#{i}"
  let instDeps : List (String × List String) :=
    (h.instances.zip instIds).map fun (inst, id) =>
      let supers := match h.traits.find? (·.name == inst.trait) with
        | some td => td.supers
        | none => []
      let superInsts := (h.instances.zip instIds).filterMap fun (o, oid) =>
        if supers.contains o.trait &&
            argTypeStr sl o.selfTy == argTypeStr sl inst.selfTy then some oid else none
      (id, (inst.fields.map (·.2)).filter defNames.contains ++ superInsts)
  let defDeps : List (String × List String) := defs.map fun (n, _, refs) =>
    let callees := (refs.filter fun r => r != n && defNames.contains r).eraseDups
    let needsInst := !genericNames.contains n && callees.any genericNames.contains
    (n, if needsInst then callees ++ instIds else callees)
  let nodes := defDeps ++ instDeps
  let text (id : String) : String :=
    match defs.find? (·.1 == id) with
    | some (_, t, _) => t
    | none =>
      match (h.instances.zip instIds).find? (·.2 == id) with
      | some (inst, _) => h.renderInstance sl inst
      | none => ""
  let rec go (fuel : Nat) (done : List String) (rest : List (String × List String)) :
      Option (List String) :=
    if rest.isEmpty then some done else
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match rest.find? (fun (_, ds) => ds.all done.contains) with
      | none => none
      | some (id, _) => go fuel (done ++ [id]) (rest.filter (·.1 != id))
  (go nodes.length [] nodes).map (·.map text)

end Hax.ClassEmit
