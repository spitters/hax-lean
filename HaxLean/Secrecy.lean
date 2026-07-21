import HaxLean.ImpType

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

`secrecyOfBindings` produces exactly the `List String` of secret binding names
that the compiler-side consumer wraps — `SourceSecrecy.secret` in
`CatCrypt/Crypto/SecureCompilation/SourceSecrecyTransfer.lean` (SSProve) — so the
producer↔consumer contract across the two repos is a plain list of names.

Wiring point (`MainT.lean`): the per-function parameter types
(`FnTypeInfo.paramTypes`, pre-newtype-unwrap) carry a secret `U8` (or a
`[U8; n]`/`&[U8]` buffer, or a `Scalar`) as an `.adt`; `secrecyOfBindings` keeps
those names and `MainT` emits them as an additive `<name>_secrecy` def.
-/

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

/-- The phase-2 recognizer: a type is a source secret value iff it is a secret
    newtype (`adt`) — a secret integer or a secret-array value newtype — or an
    `array`/`slice`/`ref` whose element is one (a buffer of secret bytes is
    secret — its values, though not its public length, must not leak). A plain
    `uint`/`sint` (declassified, or never classified) is not secret. -/
def ImpType.isSecretValue : ImpType → Bool
  | .adt name _    => secretNewtypeNames.contains name || secretValueNewtypeNames.contains name
  | .array inner _ => inner.isSecretValue
  | .slice inner   => inner.isSecretValue
  | .ref inner _   => inner.isSecretValue
  | _              => false

/-- Backward-compatible alias for `isSecretValue`. The recognizer was first
    named for the secret-*integer* case; it now also keys the secret-array value
    newtypes, so the general name is `isSecretValue`. -/
def ImpType.isSecretInteger (t : ImpType) : Bool := t.isSecretValue

/-- The phase-2 producer: from the per-binding types of an extracted function,
    the names whose source type is a secret value. This is precisely the
    `SourceSecrecy.secret` list the SSProve-side `cmdCT` gate consumes. -/
def secrecyOfBindings (bindings : List (String × ImpType)) : List String :=
  bindings.filterMap fun (name, ty) => if ty.isSecretValue then some name else none

/-! ## Verification of the recognizer -/

/-- A secret newtype byte is recognized. -/
example : ImpType.isSecretValue (.adt "U8" []) = true := by decide

/-- A secret-array value newtype (`Scalar`) is recognized. -/
example : ImpType.isSecretValue (.adt "Scalar" []) = true := by decide

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

end Hax
