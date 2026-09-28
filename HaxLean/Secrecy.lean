module

public import HaxLean.ImpType

/-!
# Source secret-value recognition (IF/CT transfer, phase 2)

The source secret-integer discipline (Bertie's `tls13utils.rs` pattern: a `U8`
newtype whose only escape is `.declassify()`) reaches the extraction as an
`ImpType.adt "U8" []` — a *nominal* newtype. `parseTyKind`'s `NewtypeMap`
currently unwraps it transparently to `Int`, erasing the secret/public
distinction. This module is the recognizer that recovers it.

Two families of secret nominal newtype are recognized:
- secret *integers* (`secretNewtypeNames`: `U8`/…/`I128`) — a fixed-width word
  whose only escape is `.declassify()`;
- secret *values* (`secretValueNewtypeNames`: `Scalar`) — the secret-array
  pattern (sole field `[u8; N]`, ingress `from_bytes_secret`, egress
  `declassify`), e.g. an EdDSA scalar.
- the generic wrapper of libcrux-secrets (`secretWrapperNames`: `Secret`). With
  the crate feature `check-secret-independence` its aliases are
  `pub type U8 = Secret<u8>` and so on; the export expands the alias, so a
  binding declared `x : U8` reaches the extraction as `.adt "Secret" [.uint .w8]`.
  Without the feature the aliases are the plain integers and carry no secrecy, so
  a crate is extracted with the feature for its secret bindings to be recovered.

`secrecyOfBindings` gives the secret names of a list of typed bindings.

## Per-function secrecy

`FnSecrecy` is the secrecy of one function: each parameter with its
`BindingSecrecy`, and the secrecy of the result. `bindingSecrecy` reads it off the
Rust type (`FnTypeInfo.paramTypes`, before newtype unwrapping) and the field types
of the crate's structs (`FieldTypes`):

* a type that `isSecretValue` recognizes is `secret`;
* a struct, or a reference to one, that is not a secret newtype and has a field
  holding a secret value (`holdsSecret`: the field's type is secret, or is an
  array, reference, option or tuple of a type holding a secret, or a struct with
  such a field) is `fields fs`, `fs` the fields holding a secret; this is the
  level of `self` in a method of a struct with a secret field;
* any other type holding a secret (an array of such structs, a tuple) is `secret`;
* every other type is `pub`.

`crateSecrecy` lists the functions of a crate with a non-public parameter or
result; `FnSecrecy.lookup` gives a listed function's record and, for any other
name, the record with no secret binding. `MainT` emits the list as
`<name>_fnSecrecy`, and the compiler maps a record to a level table over the slots
of the lowered body.
-/

@[expose] public section

namespace Hax

/-- The source secret-integer newtype names — the wrappers whose only escape is
    `.declassify()` (Bertie's `U8`, and the natural signed/wider analogues). A
    binding whose type is one of these is `Secret`; everything else defaults to
    `Public`. -/
def secretNewtypeNames : List String :=
  ["U8", "U16", "U32", "U64", "U128", "I8", "I16", "I32", "I64", "I128"]

/-- The source secret-*value* newtype names — the secret-array wrappers (sole
    field `[u8; N]`, ingress `from_bytes_secret`, egress `declassify`), e.g. an
    EdDSA `Scalar`. Keyed nominally at the same `.adt` site as the secret
    integers. -/
def secretValueNewtypeNames : List String :=
  ["Scalar"]

/-- The generic secret wrapper names — the `Secret<T>` of libcrux-secrets, whose field is
    private to that crate and whose only escapes are `declassify` and its `_ref`
    and `_mut_slice` variants. A `Secret<T>` is secret whatever `T` is. -/
def secretWrapperNames : List String :=
  ["Secret"]

/-- The phase-2 recognizer: a type is a source secret value iff it is a secret
    newtype (`adt`) — a secret integer, a secret-array value newtype or the
    libcrux-secrets wrapper `Secret` — or an
    `array`/`slice`/`ref` whose element is one (a buffer of secret bytes is
    secret — its values, though not its public length, must not leak). A plain
    `uint`/`sint` (declassified, or never classified) is not secret. -/
def ImpType.isSecretValue : ImpType → Bool
  | .adt name _    =>
      secretNewtypeNames.contains name || secretValueNewtypeNames.contains name
        || secretWrapperNames.contains name
  | .array inner _ => inner.isSecretValue
  | .slice inner   => inner.isSecretValue
  | .ref inner _   => inner.isSecretValue
  | _              => false

/-- Backward-compatible alias for `isSecretValue`. The recognizer was first
    named for the secret-*integer* case; it now also keys the secret-array value
    newtypes, so the general name is `isSecretValue`. -/
def ImpType.isSecretInteger (t : ImpType) : Bool := t.isSecretValue

/-- The phase-2 producer: from the per-binding types of an extracted function,
    the names whose source type is a secret value. The result has the type of
    `SourceSecrecy.secret`, the input of the CatCrypt `cmdCT` gate; no emitted
    list is passed to that gate yet. -/
def secrecyOfBindings (bindings : List (String × ImpType)) : List String :=
  bindings.filterMap fun (name, ty) => if ty.isSecretValue then some name else none

/-! ## Per-function secrecy -/

/-- The field types of the structs of a crate: struct name to its fields, each with
    its type, in declaration order. -/
abbrev FieldTypes := List (String × List (String × ImpType))

/-- A type holds a secret value: it is one (`isSecretValue`), or it is an array,
    slice, reference, option, result or tuple of a type holding one, or a struct of
    `st` with a field holding one. `fuel` bounds the struct unfoldings and the type
    depth; at fuel `0` only `isSecretValue` is read. -/
def ImpType.holdsSecret (st : FieldTypes) : Nat → ImpType → Bool
  | 0, t => t.isSecretValue
  | n + 1, t =>
      t.isSecretValue ||
        match t with
        | .adt s _ => ((st.lookup s).getD []).any fun p => ImpType.holdsSecret st n p.2
        | .array i _ => ImpType.holdsSecret st n i
        | .slice i => ImpType.holdsSecret st n i
        | .ref i _ => ImpType.holdsSecret st n i
        | .option i => ImpType.holdsSecret st n i
        | .result a b => ImpType.holdsSecret st n a || ImpType.holdsSecret st n b
        | .tuple ts => ts.any (ImpType.holdsSecret st n)
        | _ => false

/-- The fuel `bindingSecrecy` gives `holdsSecret`: one unfolding per struct of `st`
    and sixteen further type constructors. -/
def secrecyFuel (st : FieldTypes) : Nat := st.length + 16

/-- The secrecy of a binding. -/
inductive BindingSecrecy where
  /-- Every value the binding holds is public. -/
  | pub
  /-- The binding is secret as a whole. -/
  | secret
  /-- A struct binding whose listed fields are secret and whose other fields are
      public. -/
  | fields (fs : List String)
  deriving DecidableEq, Repr, Inhabited

/-- The secrecy of a binding of type `t` (see the module docstring): `secret` for a
    secret value; for a struct, or a reference to one, that is not a secret newtype
    and holds a secret, `fields` of its fields holding a secret (`secret` when that
    list is empty); `secret` for any other type holding a secret; `pub` otherwise. -/
def bindingSecrecy (st : FieldTypes) (t : ImpType) : BindingSecrecy :=
  let fuel := secrecyFuel st
  if t.isSecretValue then .secret
  else if !t.holdsSecret st fuel then .pub
  else
    match t.pointee with
    | .adt s _ =>
        match st.lookup s with
        | some fs =>
            match fs.filterMap fun p => if p.2.holdsSecret st fuel then some p.1 else none with
            | [] => .secret
            | f :: fs' => .fields (f :: fs')
        | none => .secret
    | _ => .secret

/-- The secrecy of one function: each parameter, in order, with its secrecy, and
    the secrecy of the result. -/
structure FnSecrecy where
  /-- The function's name, as in the `<fn>_impExpr` literal of its body. -/
  fn : String
  /-- The parameters in order, each with its secrecy. -/
  params : List (String × BindingSecrecy)
  /-- The secrecy of the result. -/
  ret : BindingSecrecy
  deriving DecidableEq, Repr, Inhabited

/-- The secrecy of the function `fn` with type information `ti`. -/
def fnSecrecyOf (st : FieldTypes) (fn : String) (ti : FnTypeInfo) : FnSecrecy where
  fn := fn
  params := ti.paramTypes.map fun p => (p.1, bindingSecrecy st p.2)
  ret := bindingSecrecy st ti.retType

/-- A function has a parameter or a result that is not public. -/
def FnSecrecy.hasSecret (s : FnSecrecy) : Bool :=
  s.ret != .pub || s.params.any fun p => p.2 != .pub

/-- The records of the functions of a crate with a parameter or a result that is not
    public, in the order of `fns`. -/
def crateSecrecy (st : FieldTypes) (fns : List (String × FnTypeInfo)) : List FnSecrecy :=
  (fns.map fun p => fnSecrecyOf st p.1 p.2).filter FnSecrecy.hasSecret

/-- The record of `fn` in `tbl`; for a name `tbl` does not list, the record with no
    parameter and a public result. -/
def FnSecrecy.lookup (tbl : List FnSecrecy) (fn : String) : FnSecrecy :=
  (tbl.find? (·.fn == fn)).getD { fn := fn, params := [], ret := .pub }

/-- A `BindingSecrecy` as a Lean term. -/
def BindingSecrecy.toLean : BindingSecrecy → String
  | .pub => "Hax.BindingSecrecy.pub"
  | .secret => "Hax.BindingSecrecy.secret"
  | .fields fs => "Hax.BindingSecrecy.fields [" ++ ", ".intercalate (fs.map String.quote) ++ "]"

/-- A `FnSecrecy` as a Lean term. -/
def FnSecrecy.toLean (s : FnSecrecy) : String :=
  let ps := s.params.map fun p => "(" ++ p.1.quote ++ ", " ++ p.2.toLean ++ ")"
  "{ fn := " ++ s.fn.quote ++ ", params := [" ++ ", ".intercalate ps ++ "], ret := " ++
    s.ret.toLean ++ " }"

/-! ## Verification of the recognizer -/

/-- A secret newtype byte is recognized. -/
example : ImpType.isSecretValue (.adt "U8" []) = true := by decide

/-- A secret-array value newtype (`Scalar`) is recognized. -/
example : ImpType.isSecretValue (.adt "Scalar" []) = true := by decide

/-- A libcrux-secrets byte, `U8 = Secret<u8>` under `check-secret-independence`, is
    recognized. -/
example : ImpType.isSecretValue (.adt "Secret" [.uint .w8]) = true := by decide

/-- A buffer of libcrux-secrets words (`[U64; 4]`) is secret. -/
example : ImpType.isSecretValue (.array (.adt "Secret" [.uint .w64]) 4) = true := by decide

/-- A slice of libcrux-secrets bytes (`&[U8]`) is secret. -/
example :
    ImpType.isSecretValue (.ref (.slice (.adt "Secret" [.uint .w8])) false) = true := by
  decide

/-- A plain fixed-width integer is not secret (it is `Public` — e.g. a
    declassified value or one never classified). -/
example : ImpType.isSecretValue (.uint .w8) = false := by decide

/-- An arbitrary-precision `int` (the type a transparently-unwrapped newtype
    collapses to today) is not secret — which is exactly the erasure this
    recognizer prevents by keying on the newtype name before the unwrap. -/
example : ImpType.isSecretValue .int = false := by decide

/-- A non-secret ADT (an ordinary struct) is not secret. -/
example : ImpType.isSecretValue (.adt "Point" []) = false := by decide

/-- A buffer of secret bytes (`[U8; 16]`) is secret. -/
example : ImpType.isSecretValue (.array (.adt "U8" []) 16) = true := by decide

/-- A reference to a secret buffer (`&[U8]`) is secret. -/
example : ImpType.isSecretValue (.ref (.slice (.adt "U8" [])) false) = true := by decide

/-- A buffer of public bytes (`[u8; 16]`) is not secret. -/
example : ImpType.isSecretValue (.array (.uint .w8) 16) = false := by decide

/-- The producer keeps exactly the secret-typed binding names, in order. -/
example :
    secrecyOfBindings
      [("g", .adt "U8" []), ("len", .uint .w32), ("k", .adt "U64" []), ("i", .int)]
      = ["g", "k"] := by decide

/-- The EdDSA scalar-mul pattern: a public group element `self : Edwards25519`, a
    secret `k : Scalar`, and a public `k_bytes : [u8; 32]` — only `k` is secret. -/
example :
    secrecyOfBindings
      [("self", .adt "Edwards25519" []), ("k", .adt "Scalar" []),
       ("k_bytes", .array (.uint .w8) 32)]
      = ["k"] := by decide

/-- A libcrux-secrets signature: a secret key `sk : &[U8]`, a public message
    `msg : &[u8]` and a secret nonce `r : U64` — `sk` and `r` are secret. -/
example :
    secrecyOfBindings
      [("sk", .ref (.slice (.adt "Secret" [.uint .w8])) false),
       ("msg", .ref (.slice (.uint .w8)) false), ("r", .adt "Secret" [.uint .w64])]
      = ["sk", "r"] := by decide

/-- The structs of a method-carrying crate: a point of public coordinates and a key
    pair with a public `pk` and a secret `sk`. -/
private def keyStructs : FieldTypes :=
  [("Point", [("x", .array (.uint .w64) 4), ("y", .array (.uint .w64) 4)]),
   ("KeyPair", [("pk", .adt "Point" []), ("sk", .adt "Scalar" [])])]

/-- `self : &Scalar` in a method of the secret newtype is secret as a whole. -/
example : bindingSecrecy keyStructs (.ref (.adt "Scalar" []) false) = .secret := by decide

/-- `self : Point` of public coordinates is public. -/
example : bindingSecrecy keyStructs (.adt "Point" []) = .pub := by decide

/-- `self : &KeyPair` has its field `sk` secret and its field `pk` public. -/
example : bindingSecrecy keyStructs (.ref (.adt "KeyPair" []) false) = .fields ["sk"] := by
  decide

/-- An array of key pairs is secret as a whole. -/
example : bindingSecrecy keyStructs (.array (.adt "KeyPair" []) 2) = .secret := by decide

/-- A point method taking a secret scalar: the per-function record marks `k` and not
    `self`. -/
example :
    fnSecrecyOf keyStructs "scalar_mul"
        { paramTypes := [("self", .adt "Point" []), ("k", .adt "Scalar" [])],
          retType := .adt "Point" [] } =
      { fn := "scalar_mul", params := [("self", .pub), ("k", .secret)], ret := .pub } := by
  decide

end Hax
