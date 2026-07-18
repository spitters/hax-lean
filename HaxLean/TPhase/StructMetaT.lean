/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import HaxLean.ImpType

/-!
# Shared struct-metadata abbreviation for typed phases

`StructMetaT` is the shape that the type-dependent TPhase rewriters
(`tQualifyProjections`, `tRewriteNewToStructCtor`, `tRewriteStructFromElem`)
consume. It is structurally identical to the untyped renderer's
`StructMeta'` in `Hax/PrettyPrint.lean`, just relocated here so the
typed phases can share a single definition without re-declaring it
(and thereby colliding when imported together).
-/

namespace Hax

/-- Struct metadata: name → list of (field_name, type_tag, impType). -/
abbrev StructMetaT := List (String × List (String × String × ImpType))

end Hax
