/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.HaxAdapter
public import HaxLean.PrettyPrint -- deprecated_module: ignore

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

The `ImpExpr` and `TExpr` literals are emitted as in the default mode, except
that a read of an associated constant through a trait bound of a type parameter
is a nullary call of the class constant, `.app "ZERO" []`
(`HaxAdapter.constReadKind`). A parameter whose type is a type parameter or a
projection on one carries its type in the surface signature,
`(a_hat : (PolyRing.NttForm R))`.
-/

@[expose] public section

namespace Hax.ClassEmit

open Lean (Json)
open Hax.HaxAdapter (parseHaxType defIdLeafName defIdKrate defIdPathNames
  builtinKrates extractFnName buildTraitImplMethodMap buildTraitImplConstMap
  extractAdtShortName)

/-! ## Export rewriting -/

/-- The Lean name of a hax type parameter. hax names the synthetic type
    parameter of an argument-position `impl Trait` by its Rust spelling
    (`impl Into<String>`), which is not a Lean identifier; such a name is the
    alphanumeric runs of the spelling joined by `_` (`impl_Into_String`). Every
    other name is returned unchanged. -/
def typeParamLeanName (n : String) : String :=
  if !n.startsWith "impl " then n else
  let (runs, cur) := n.toList.foldl (fun (acc : List String × String) c =>
      if c.isAlphanum then (acc.1, acc.2.push c)
      else if acc.2.isEmpty then acc else (acc.1 ++ [acc.2], "")) ([], "")
  "_".intercalate (if cur.isEmpty then runs else runs ++ [cur])

/-- The type parameter, trait and associated item of a projection `P::A` on a
    type parameter `P`, by short names, from the `Alias` node of the type: the
    self argument of the projection's trait reference is the `Param` `P`. -/
def paramAssocProj (alias : Json) : Option (String × String × String) := do
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
  let param ← (p.getObjValAs? String "name").toOption
  let traitName ← (tvv.getObjVal? "def_id").toOption >>= defIdLeafName
  let item ← (proj.getObjVal? "assoc_item").toOption
  let defId ← (item.getObjVal? "def_id").toOption
  let itemName ← defIdLeafName defId
  pure (typeParamLeanName param, traitName, itemName)

/-- The associated-type name of a projection `Self::Name`, from the `Alias`
    node of the type: a projection whose trait reference has the type parameter
    `Self` as its self argument. Inside a trait definition hax resolves such a
    projection through `SelfImpl` or through the `Self: Trait` bound
    (`LocalBound`); either way the self argument is `Self`. -/
def selfAssocName (alias : Json) : Option String := do
  let (param, _, item) ← paramAssocProj alias
  guard (param == "Self")
  pure item

/-- The Lean type of a projection `P::A` of the trait `T` on a type parameter
    `P` other than `Self`: the class field applied to the parameter,
    `(T.A P)`. -/
def paramAssocType (alias : Json) : Option String := do
  let (param, traitName, item) ← paramAssocProj alias
  guard (param != "Self")
  pure s!"({traitName}.{item} {param})"

/-- Rewrite every type-parameter node `{"Param": {"index": i, "name": n}}` of
    a hax export to `{"TypeVar": n}`, and every projection `Self::A` through the
    enclosing trait to `{"TypeVar": A}`, and every projection `P::A` of a trait
    `T` on another type parameter `P` to `{"TypeVar": "(T.A P)"}`.
    `HaxAdapter.parseHaxType` reads the rewritten node as `ImpType.typeVar n`;
    it reads a `Param` as `.slice .int`. A parameter is named by
    `typeParamLeanName`. -/
partial def keepTypeParams (j : Json) : Json :=
  match j with
  | .arr xs => .arr (xs.map keepTypeParams)
  | .obj t =>
    match t.toList with
    | [("Param", p)] =>
      match p.getObjValAs? String "name" with
      | .ok n => Json.mkObj [("TypeVar", .str (typeParamLeanName n))]
      | _ => Json.mkObj [("Param", keepTypeParams p)]
    | [("Alias", a)] =>
      match selfAssocName a, paramAssocType a with
      | some n, _ => Json.mkObj [("TypeVar", .str n)]
      | none, some n => Json.mkObj [("TypeVar", .str n)]
      | none, none => Json.mkObj [("Alias", keepTypeParams a)]
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
  /-- Whether `core::cmp::PartialEq` (or `Eq`) is a supertrait. The class then
      carries a `BEq Self` instance field, through which `==` on a type
      parameter bounded by the trait resolves. -/
  beq : Bool := false
  /-- The associated types with a `core::cmp::PartialEq` (or `Eq`) bound. The
      class carries a `BEq` instance field for each. -/
  beqAssoc : List String := []
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

/-- Whether a list of hax clauses holds a trait bound `PartialEq` or `Eq` of
    `core`. -/
def hasPartialEqClause (clauses : Json) : Bool :=
  match clauses with
  | .arr cs => cs.toList.any fun c => (do
      let k ← (c.getObjVal? "kind").toOption
      let v ← (k.getObjVal? "value").toOption
      let tr ← (v.getObjVal? "Trait").toOption
      let tref ← (tr.getObjVal? "trait_ref").toOption
      let tv ← (tref.getObjVal? "value").toOption
      let defId ← (tv.getObjVal? "def_id").toOption
      guard (builtinKrates.contains (defIdKrate defId))
      let n ← defIdLeafName defId
      guard (n == "PartialEq" || n == "Eq")
      pure ()).isSome
  | _ => false

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
      let beq := (ty[0]?.map hasPartialEqClause).getD false
      { td with assocTypes := td.assocTypes ++ [(name, bounds)],
                beqAssoc := if beq then td.beqAssoc ++ [name] else td.beqAssoc }
    else td
  | _ => td

/-- The first definition of each trait name, in list order. -/
def dedupTraits (tds : List TraitDef) : List TraitDef :=
  tds.foldl (fun acc d => if acc.any (·.name == d.name) then acc else acc ++ [d]) []

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
    let beq := (tr[5]?.map hasPartialEqClause).getD false
    let items := match tr[6]? with
      | some (.arr xs) => xs.toList
      | _ => []
    some (items.foldl addTraitItem { name, krate, supers, beq })
  dedupTraits defs

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
  /-- The type parameters with a `PartialEq` or `Eq` bound of their own, which
      are bound with a `BEq` instance. -/
  beqParams : List String := []
  /-- The trait items the function reads through a trait bound, as
      `(trait, item, self type)` (`localBoundSelfItems`). -/
  boundItems : List (String × String × Option String) := []
  /-- The references the function makes with type arguments, as `(callee, type
      arguments)` (`typeArgCallsOf`). -/
  typeCalls : List (String × List ImpType) := []
  deriving Inhabited

/-- The type-parameter names of a hax `generics` node, by
    `typeParamLeanName`: the synthetic parameter of an argument-position
    `impl Trait` is among them. -/
def typeParamNames (generics : Json) : List String :=
  match generics.getObjValAs? (Array Json) "params" with
  | .ok ps => ps.toList.filterMap fun p => do
    let k ← (p.getObjVal? "kind").toOption
    let _ ← (k.getObjVal? "Type").toOption
    let n ← (p.getObjVal? "name").toOption
    let plain ← (n.getObjVal? "Plain").toOption
    (plain.getObjValAs? String "name").toOption.map typeParamLeanName
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

/-- The trait items a node of an export rewritten by `keepTypeParams` reads
    through a trait bound, as `(trait, item, self type)`: every node carrying an
    `in_trait` whose `impl` atom is `LocalBound`, outside the traits of `core`,
    `alloc` and `std`. The self type is the first generic argument of the
    `in_trait` trait reference when it is a type variable
    (`HaxAdapter.localBoundTraitSelf`), and `none` otherwise. -/
partial def localBoundSelfItems (j : Json)
    (acc : Array (String × String × Option String) := #[]) :
    Array (String × String × Option String) :=
  match j with
  | .arr xs => xs.foldl (fun a x => localBoundSelfItems x a) acc
  | .obj t =>
    let here : Option (String × String × Option String) := do
      let it ← (j.getObjVal? "in_trait").toOption
      let impl ← (it.getObjVal? "impl").toOption
      let _ ← (impl.getObjVal? "LocalBound").toOption
      let defId ← (j.getObjVal? "def_id").toOption
      guard (!builtinKrates.contains (defIdKrate defId))
      let item :: trait :: _ := (defIdPathNames defId).reverse | none
      let selfTy := HaxAdapter.localBoundTraitSelf
        (Json.mkObj [("item", Json.mkObj [("value", j)])])
      pure (trait, item, selfTy.map (·.2))
    let acc := match here with
      | some p => if acc.contains p then acc else acc.push p
      | none => acc
    t.toList.foldl (fun a (_, v) => localBoundSelfItems v a) acc
  | _ => acc

/-- The parse context of `typeArgCallsOf` for the export `j`: the inherent `impl`
    blocks with their self types, type-argument heads and method collisions, and
    the methods of the trait `impl` blocks, as `parseHaxFileWithTExprReport` builds
    them, so that a reference to a method of an `impl` of the crate is named by the
    definition the adapter emits for it. -/
def typeArgImplMap (j : Json) : HaxAdapter.ImplSelfTypeMap :=
  { impls := HaxAdapter.buildImplSelfTypeMap j
    implArgHeads := HaxAdapter.inherentImplArgHeads j
    inherentCollisions := HaxAdapter.inherentMethodCollisions j
    traitImplMethods := buildTraitImplMethodMap j }

/-- The `Type` entries of a hax `generic_args` list, in order
    (`HaxAdapter.parseHaxType`). -/
def typeArgsOfGenericArgs (args : Array Json) : List ImpType :=
  args.toList.filterMap fun a => (a.getObjVal? "Type").toOption.map parseHaxType

/-- The references with type arguments in a node of an export rewritten by
    `keepTypeParams`, as `(callee, type arguments)`: every node with a `def_id`
    and a `generic_args` list, whose type arguments are not empty, of one of two
    kinds.

    * A node with a `null` `in_trait`, with the `Type` entries of its
      `generic_args`, which for a method of an inherent `impl` are the `impl`'s
      followed by the method's own. It is named by
      `HaxAdapter.disambiguateMethodCallWithImplMap` under `implMap`: the leaf of
      its `def_id` for a function, `<SelfType>_<method>` for a method of an
      inherent `impl` of the crate.
    * A node whose `in_trait` resolves to a trait `impl` of the crate that defines
      the method (`HaxAdapter.resolveTraitImplCall`), named by the definition of
      that method, with the `Type` entries of the `impl`'s `Concrete` reference
      followed by those of the node's `generic_args`, which for a trait item are
      the method's own.

    A call `g::<D>(…)` of a generic function of the crate, `S::m::<D>(…)` of a
    generic method of an inherent `impl` and `<S as T>::m::<D>(…)` of a generic
    method of a trait `impl` are such references. -/
partial def typeArgCallsOf (j : Json) (acc : Array (String × List ImpType) := #[])
    (implMap : HaxAdapter.ImplSelfTypeMap := {}) : Array (String × List ImpType) :=
  match j with
  | .arr xs => xs.foldl (fun a x => typeArgCallsOf x a implMap) acc
  | .obj t =>
    let here : Option (String × List ImpType) := do
      let defId ← (j.getObjVal? "def_id").toOption
      let args ← (j.getObjValAs? (Array Json) "generic_args").toOption
      let inTrait ← (j.getObjVal? "in_trait").toOption
      let funJ := Json.mkObj [("contents", Json.mkObj [("GlobalName",
        Json.mkObj [("item", Json.mkObj [("value", j)])])])]
      let (f, tys) ← if inTrait == Json.null then do
          let leaf ← defIdLeafName defId
          pure (HaxAdapter.disambiguateMethodCallWithImplMap funJ leaf implMap,
            typeArgsOfGenericArgs args)
        else do
          let f ← HaxAdapter.resolveTraitImplCall funJ implMap
          let implJ ← (inTrait.getObjVal? "impl").toOption
          let concrete ← (implJ.getObjVal? "Concrete").toOption
          let cVal ← (concrete.getObjVal? "value").toOption
          let implArgs ← (cVal.getObjValAs? (Array Json) "generic_args").toOption
          pure (f, typeArgsOfGenericArgs implArgs ++ typeArgsOfGenericArgs args)
      guard (!tys.isEmpty)
      pure (f, tys)
    let acc := match here with
      | some p => if acc.any (fun q => q.1 == p.1 && q.2 == p.2) then acc else acc.push p
      | none => acc
    t.toList.foldl (fun a (_, v) => typeArgCallsOf v a implMap) acc
  | _ => acc

/-- The generic top-level functions of an export rewritten by
    `keepTypeParams`, one per name. -/
def genericFns (traits : List String) (j : Json) : List GenericFn :=
  let implMap := typeArgImplMap j
  let fs := (allItems j).filterMap fun it => do
    let k ← (it.getObjVal? "kind").toOption
    let f ← (k.getObjVal? "Fn").toOption
    let ident ← (f.getObjVal? "ident").toOption
    let g ← (f.getObjVal? "generics").toOption
    let ps := typeParamNames g
    guard (!ps.isEmpty)
    let beqParams := ((typeParamBounds ["PartialEq", "Eq"] g).map (·.2)).eraseDups
    some { name := extractFnName ident, typeParams := ps, bounds := typeParamBounds traits g,
           beqParams, boundItems := (localBoundSelfItems f).toList,
           typeCalls := (typeArgCallsOf f #[] implMap).toList }
  fs.foldl (fun acc f => if acc.any (·.name == f.name) then acc else acc ++ [f]) []

/-- The generic methods of the `impl` blocks of an export rewritten by
    `keepTypeParams`: each method whose `impl` block or whose own generics have
    a type parameter, with the type parameters and bounds of both, the block's
    first. A method of an inherent `impl` is named `<SelfType>_<method>`, and a
    method of a trait `impl` by `buildTraitImplMethodMap`; these are the names of
    the definitions the adapter emits (`HaxAdapter.parseHaxFileWithTExpr`). -/
def genericImplMethods (traits : List String) (j : Json) : List GenericFn :=
  let traitNames := buildTraitImplMethodMap j
  let implMap := typeArgImplMap j
  (allItems j).flatMap fun it => ((do
    let k ← (it.getObjVal? "kind").toOption
    let impl ← (k.getObjVal? "Impl").toOption
    let ig := (impl.getObjVal? "generics").toOption.getD .null
    let isTrait := match impl.getObjVal? "of_trait" with
      | .ok Json.null => false
      | .ok _ => true
      | _ => false
    let implId : Option Nat := do
      let oid ← (it.getObjVal? "owner_id").toOption
      let c ← (oid.getObjVal? "contents").toOption
      (c.getObjValAs? Nat "id").toOption
    let selfName : Option String := do
      let st ← (impl.getObjVal? "self_ty").toOption
      let v ← (st.getObjVal? "value").toOption
      let adt ← (v.getObjVal? "Adt").toOption
      extractAdtShortName adt
    let implItems ← (impl.getObjValAs? (Array Json) "items").toOption
    pure (implItems.toList.filterMap fun ii => do
      let ik ← (ii.getObjVal? "kind").toOption
      let _ ← (ik.getObjVal? "Fn").toOption
      let m := extractFnName ((ii.getObjVal? "ident").toOption.getD .null)
      let name ← if isTrait then do
          let iid ← implId
          let e ← traitNames.find? fun p => p.1 == iid && p.2.1 == m
          pure e.2.2
        else selfName.map (s!"{·}_{m}")
      let mg := (ii.getObjVal? "generics").toOption.getD .null
      let ps := (typeParamNames ig ++ typeParamNames mg).eraseDups
      guard (!ps.isEmpty)
      let eqB := typeParamBounds ["PartialEq", "Eq"] ig ++ typeParamBounds ["PartialEq", "Eq"] mg
      some { name, typeParams := ps,
             bounds := (typeParamBounds traits ig ++ typeParamBounds traits mg).eraseDups,
             beqParams := (eqB.map (·.2)).eraseDups,
             boundItems := (localBoundSelfItems ii).toList,
             typeCalls := (typeArgCallsOf ii #[] implMap).toList : GenericFn })) : Option _).getD []

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
  /-- The interning id of the `impl` block's `owner_id`. -/
  implId : Nat := 0
  /-- The pre- and postcondition fields of the instance under
      `--emit-contracts`, as (field name, rendered value). -/
  contractFields : List (String × String) := []
  /-- The type parameters of the `impl` block and its bounds `(trait, type
      parameter)` over the known traits, bound by the instance. -/
  typeParams : List String := []
  bounds : List (String × String) := []
  deriving Inhabited

/-- The trait `impl`s of the extracted crate whose trait is among `traits`,
    one per `impl` block. The fields are the entries of
    `buildTraitImplMethodMap` and `buildTraitImplConstMap` for the block; the
    type parameters and bounds are those of the block's generics. -/
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
    let ig := (impl.getObjVal? "generics").toOption.getD .null
    some (implId, { trait := tn, selfTy, fields, implId, typeParams := typeParamNames ig,
                    bounds := typeParamBounds traits ig : ImplInstance })
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
  /-- Per trait, the methods that carry a pre- and a postcondition field
      (`--emit-contracts`). -/
  contractMethods : List (String × List String) := []
  /-- The trait-level contract definitions and the `Contract` classes, rendered
      under a struct lookup; they follow the classes. -/
  contractText : (String → Option String) → String := fun _ => ""
  /-- The methods, by trait and name, emitted with result type `RustM` (the effect
      closure of `--emit-monadic`). -/
  monadicMethods : List (String × String) := []
  /-- Per function of the crate, its references with type arguments to the
      generic top-level functions and the generic methods of the `impl` blocks of
      the crate (`genericFns`, `genericImplMethods`, `typeArgCallsOf`). -/
  typeArgCalls : List (String × List (String × List ImpType)) := []
  deriving Inhabited

/-- Whether the class mode is on. -/
def ClassHooks.enabled (h : ClassHooks) : Bool := !h.traits.isEmpty

/-- The item names exported from the classes; they are not `Deps` fields. -/
def ClassHooks.classItemNames (h : ClassHooks) : List String := h.exports.flatMap (·.2)

/-- The plan for an extracted crate (`crate`) and the definitions of the traits
    it uses (`traitExport`), both rewritten by `keepTypeParams`. The traits are
    those of `traitExport` and of `crate`, one per trait name, so a trait both
    exports define (as when `traitExport` is the crate's own export) is emitted
    once. -/
def plan (traitExport crate : Json) : ClassHooks :=
  let traits := orderTraits (dedupTraits (parseTraitDefs traitExport ++ parseTraitDefs crate))
  let names := traits.map (·.name)
  let used := (localBoundItems crate).toList.filter fun (_, t) => names.contains t
  let exports := names.filterMap fun t =>
    let items := (used.filter (·.2 == t)).map (·.1)
    if items.isEmpty then none else some (t, items)
  let topFns := genericFns names crate
  let gfns := (topFns ++ genericImplMethods names crate).foldl
    (fun acc f => if acc.any (·.name == f.name) then acc else acc ++ [f]) []
  -- The generic top-level functions and the generic methods of the `impl` blocks.
  let callees := gfns.map (·.name)
  let implMap := typeArgImplMap crate
  -- Every top-level function, generic or not, and every generic method.
  let fnCalls := (allItems crate).filterMap fun it => do
    let k ← (it.getObjVal? "kind").toOption
    let f ← (k.getObjVal? "Fn").toOption
    let ident ← (f.getObjVal? "ident").toOption
    pure (extractFnName ident, (typeArgCallsOf f #[] implMap).toList)
  let callers := (fnCalls ++ gfns.map fun g => (g.name, g.typeCalls)).foldl
    (fun acc c => if acc.any (·.1 == c.1) then acc else acc ++ [c]) []
  { traits, exports
    genericFns := gfns
    genericStructs := genericStructs crate
    instances := implInstances names crate
    typeArgCalls := callers.filterMap fun (n, cs) =>
      let cs := cs.filter (callees.contains ·.1)
      if cs.isEmpty then none else some (n, cs) }

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

/-- Whether the class of a trait carries a `BEq Self` instance, its own or a
    supertrait's (`TraitDef.beq`). -/
partial def ClassHooks.traitHasBeq (h : ClassHooks) (t : String) : Bool :=
  match h.traits.find? (·.name == t) with
  | some td => td.beq || td.supers.any (h.traitHasBeq ·)
  | none => false

/-- The type variables of a type read from an export rewritten by
    `keepTypeParams`. -/
partial def typeVarNames : ImpType → List String
  | .typeVar n => [n]
  | .tuple es | .adt _ es => es.flatMap typeVarNames
  | .option a | .ref a _ | .slice a | .array a _ => typeVarNames a
  | .result a b | .controlFlow a b => typeVarNames a ++ typeVarNames b
  | .fn ps r => ps.flatMap typeVarNames ++ typeVarNames r
  | .bool | .int | .uint _ | .sint _ | .unit | .str | .unknown => []

/-- The type variables through which a field of the class of the trait `t`
    mentions its `Self` type: `Self` and the associated types of the trait and
    of its supertraits, which `keepTypeParams` renders as type variables. -/
partial def ClassHooks.selfTypeNames (h : ClassHooks) (t : String) : List String :=
  "Self" :: (h.traits.filter (·.name == t)).flatMap fun td =>
    td.assocTypes.map (·.1) ++ td.supers.flatMap (h.selfTypeNames ·)

/-- Whether the method `m` of the trait `t` is a class field whose type does not
    mention `Self` (`selfTypeNames`), as a Rust associated function without a
    `self` receiver whose signature names neither `Self` nor an associated type.
    The projection of such a field takes `Self` as an explicit argument. -/
def ClassHooks.isStaticMethod (h : ClassHooks) (t m : String) : Bool :=
  let selfNames := h.selfTypeNames t
  (h.traits.filter (·.name == t)).any fun td =>
    td.methods.any fun (n, ps, r) =>
      n == m && !((r :: ps.map (·.2)).flatMap typeVarNames).any selfNames.contains

/-- The call heads of the static trait methods (`isStaticMethod`) that the
    generic function `fn` calls through a trait bound, as `(method, head)`. The
    head `HaxAdapter.classItemHead t m S` names the class `t` and the self type
    `S` of the calls (`GenericFn.boundItems`), and the renderer prints it as
    `(t.m (Self := S))`. An error names a static method that `fn` calls at a self
    type other than a type variable, at two self types, or through two traits. -/
def ClassHooks.staticCallHeads (h : ClassHooks) (fn : String) :
    Except String (List (String × String)) :=
  let calls := ((h.genericFns.filter (·.name == fn)).flatMap (·.boundItems)).filter
    fun (t, m, _) => h.isStaticMethod t m
  (calls.map (·.2.1)).eraseDups.mapM fun m =>
    let sites := ((calls.filter (·.2.1 == m)).map fun (t, _, s) => (t, s)).eraseDups
    if let [(t, some s)] := sites then .ok (m, HaxAdapter.classItemHead t m s)
    else .error (s!"`{fn}` calls the trait method `{m}`, whose class field does not " ++
      s!"mention `Self`, at the (trait, self type) pairs {sites}; the call names its " ++
      "instance only at one trait and one type-variable self type")

/-- The refusals of `staticCallHeads` over the generic functions, as
    `(function, reason)`. -/
def ClassHooks.staticCallRefusals (h : ClassHooks) : List (String × String) :=
  h.genericFns.filterMap fun g =>
    match h.staticCallHeads g.name with
    | .error msg => some (g.name, msg)
    | .ok _ => none

/-- The call heads of the generic functions and `impl` methods of the crate that
    the function `fn` calls with type arguments (`typeArgCalls`), as
    `(callee, head)`. A callee `g`
    gets the head `typeArgsHead g [(P, X), …]`, printed `(g (P := X) …)`, naming
    each type parameter `P` of `g` that `sigVars g` (the type variables of `g`'s
    parameter and result types) leaves out, at the type argument `X` of the call;
    a callee whose type parameters all occur in its signature keeps its name. An
    error names a callee that `fn` calls at two lists of type arguments, or at a
    list whose length differs from the callee's type parameters or that holds a
    type the adapter does not read. -/
def ClassHooks.typeArgCallHeads (h : ClassHooks) (sl : String → Option String)
    (sigVars : String → List String) (fn : String) :
    Except String (List (String × String)) := do
  let calls := (h.typeArgCalls.filter (·.1 == fn)).flatMap (·.2)
  let heads ← (calls.map (·.1)).eraseDups.mapM fun g => do
    let tps := (h.genericFns.filter (·.name == g)).flatMap (·.typeParams)
    let free := tps.filter fun p => !(sigVars g).contains p
    if free.isEmpty then return none
    let sites := ((calls.filter (·.1 == g)).map (·.2)).eraseDups
    let [args] := sites
      | throw (s!"`{fn}` calls `{g}` at {sites.length} lists of type arguments; the " ++
          s!"type parameters {free} of `{g}` occur only in its bounds and are named " ++
          "at one list")
    if args.length != tps.length || args.any (·.isUnknown) then
      throw (s!"`{fn}` calls `{g}` at type arguments the adapter does not read for " ++
        s!"the type parameters {tps}")
    return some (g, typeArgsHead g (((tps.zip args).filter (free.contains ·.1)).map
      fun (p, a) => (p, argTypeStr sl a)))
  return heads.filterMap id

/-- The refusals of `typeArgCallHeads` over the callers of `typeArgCalls`, as
    `(function, reason)`. -/
def ClassHooks.typeArgCallRefusals (h : ClassHooks) (sigVars : String → List String) :
    List (String × String) :=
  (h.typeArgCalls.map (·.1)).eraseDups.filterMap fun fn =>
    match h.typeArgCallHeads (fun _ => none) sigVars fn with
    | .error msg => some (fn, msg)
    | .ok _ => none

/-- The result type of the class field of a trait method with the parameters
    `ps` and the Rust result `r`, under the write-back convention of `&mut`
    parameters that the definitions of the crate follow (`mutWriteRets` of
    `toLeanDefTyped`): `r` without a `&mut` parameter; the parameter's type for one
    `&mut` parameter and the result `()`; otherwise the product of `r`, unless it
    is `()`, and the types of the `&mut` parameters in order. -/
def writeBackResult (ps : List (String × ImpType)) (r : ImpType) : ImpType :=
  let muts := ps.flatMap fun (_, t) =>
    match t with
    | .ref inner true => [inner]
    | .ref _ false | .bool | .int | .uint _ | .sint _ | .unit | .str | .tuple _
    | .option _ | .result _ _ | .controlFlow _ _ | .adt _ _ | .fn _ _ | .slice _
    | .array _ _ | .typeVar _ | .unknown => []
  if muts.isEmpty then r else
  match (if r == .unit then [] else [r]) ++ muts with
  | [t] => t
  | ts => .tuple ts

/-- The name of the class field of a trait with contract methods that holds the
    invariant of the Rust self type of an instance: `T_inv`. -/
def selfInvField (t : String) : String := s!"{t}_inv"

/-- The binder name of a method's result in its postcondition: `result`, or
    `result` followed by primes when a parameter already has that name. -/
def resultBinderName (params : List String) : String :=
  go params.length "result"
where
  /-- Add primes until the name is free, at most `fuel` times. -/
  go : Nat → String → String
    | 0, n => n
    | fuel + 1, n => if params.contains n then go fuel (n ++ "'") else n

/-- The class declarations and the `export` lines, followed by the contract
    text of `--emit-contracts` (`ClassHooks.contractText`). A method listed in
    `ClassHooks.contractMethods` also carries a precondition field `m_pre` over
    its parameters and a postcondition field `m_post` over its parameters and
    result, and the class of a trait with such methods the invariant field
    `T_inv : Self → Prop` (`selfInvField`). A method of
    `ClassHooks.monadicMethods` has result type `RustM` of its Rust result type. -/
def ClassHooks.renderClasses (h : ClassHooks) (sl : String → Option String) : String :=
  let known := h.traits.map (·.name)
  let classes := h.traits.map fun td =>
    let supers := td.supers.filter known.contains
    let ext := if supers.isEmpty then ""
      else " extends " ++ ", ".intercalate (supers.map fun s => s!"{s} Self")
    -- A `PartialEq` supertrait is a `BEq Self` instance field, unless an
    -- emitted supertrait already carries one.
    let ownBeq := td.beq && !supers.any (h.traitHasBeq ·)
    let beqField := if ownBeq then ["  [instBEq : BEq Self]"] else []
    -- An associated type with a `PartialEq` bound carries a `BEq` instance
    -- field, unless one of its emitted trait bounds already supplies one.
    let assocBeq (a : String) (bs : List String) : Bool :=
      td.beqAssoc.contains a && !(bs.filter known.contains).any (h.traitHasBeq ·)
    let assoc := td.assocTypes.flatMap fun (a, bs) =>
      s!"  {sanitizeName a} : Type" ::
        ((bs.filter known.contains).map fun b => s!"  [inst{b}_{a} : {b} {sanitizeName a}]")
        ++ (if assocBeq a bs then [s!"  [instBEq_{a} : BEq {sanitizeName a}]"] else [])
    let consts := td.consts.map fun (c, ty) =>
      s!"  {sanitizeName c} : {ty.toLeanTypeStrSurface sl}"
    let methods := td.methods.map fun (m, ps, r0) =>
      let binders := ps.map fun (p, ty) => s!" ({sanitizeName p} : {ty.toLeanTypeStrSurface sl})"
      -- A method with `&mut` parameters returns what it writes back.
      let r := writeBackResult ps r0
      let res := if h.monadicMethods.contains (td.name, m) then
          s!"RustM ({r.toLeanTypeStrSurface sl})"
        else r.toLeanTypeStrSurface sl
      s!"  {sanitizeName m}{String.join binders} : {res}"
    let contractMs := ((h.contractMethods.find? (·.1 == td.name)).map (·.2)).getD []
    -- A trait with contract methods carries the invariant of the Rust self
    -- type of its instance (`selfInvField`), under which its `Contract`
    -- obligations quantify.
    let invField := if contractMs.isEmpty then []
      else [s!"  {selfInvField td.name} (x : Self) : Prop"]
    let prePost := invField ++ td.methods.flatMap fun (m, ps, r) =>
      if !contractMs.contains m then [] else
      let binders := String.join (ps.map fun (p, ty) =>
        s!" ({sanitizeName p} : {ty.toLeanTypeStrSurface sl})")
      let res := resultBinderName (ps.map (·.1))
      [s!"  {sanitizeName m}_pre{binders} : Prop",
       s!"  {sanitizeName m}_post{binders} ({res} : {r.toLeanTypeStrSurface sl}) : Prop"]
    let attrs := td.assocTypes.flatMap fun (a, bs) =>
      ((bs.filter known.contains).map fun b =>
        s!"\nattribute [instance_reducible, instance] {td.name}.inst{b}_{a}")
      ++ (if assocBeq a bs then
            [s!"\nattribute [instance_reducible, instance] {td.name}.instBEq_{a}"] else [])
    let beqAttr := if ownBeq then
        s!"\nattribute [instance_reducible, instance] {td.name}.instBEq" else ""
    s!"/-- The Rust trait `{td.name}` of the crate `{td.krate}`, as a class over its `Self` type. -/\nclass {td.name} (Self : Type){ext} where\n"
      ++ "\n".intercalate (beqField ++ assoc ++ consts ++ methods ++ prePost)
      ++ beqAttr ++ String.join attrs
  let exports := h.exports.map fun (t, items) =>
    s!"export {t} ({" ".intercalate (items.map sanitizeName)})"
  "\n\n".intercalate classes ++ "\n\n" ++ "\n".intercalate exports ++ "\n\n"
    ++ h.contractText sl

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
    ++ g.beqParams.map (fun p => s!"[BEq {p}]")
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
  let contractFields := inst.contractFields.map fun (f, v) => s!"  {f} := {v}"
  let binders := if inst.typeParams.isEmpty then ""
    else " " ++ ({ name := "", typeParams := inst.typeParams, bounds := inst.bounds :
      GenericFn }).binders
  s!"instance{binders} : {inst.trait} {argTypeStr sl inst.selfTy} where\n"
    ++ "\n".intercalate (superFields ++ fields ++ contractFields) ++ "\n"

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
