/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Phase.InlineLocalClosures

/-!
# Fragment checks of the inlining of local closures

A closure called with an argument that contains a call is outside the pure fragment
(`closureOk`), whether its body drops the parameter (`|x| y`) or reads it twice
(`|x| x + x`). It is in the statement fragment (`blockOk`), whose call block binds the
argument to the parameter once. A pure closure applied to `a + b` is inlined the same way.
A call of a closure with an argument that contains a call is in neither fragment under a
loop or a `match_`. A call with an argument without calls stays in the pure fragment.
-/

set_option autoImplicit false

namespace Hax.InlineLocalClosures

example : closureOk "f" ["x"] (.var "y") (.app "f" [.app "g" []]) = false := by decide
example : closureOk "f" ["x"] (.app "add" [.var "x", .var "x"])
    (.app "f" [.app "g" [.var "z"]]) = false := by decide
example : blockOk "f" ["x"] (.var "y") (.app "f" [.app "g" []]) = true := by decide
example : blockOk "f" ["x"] (.app "add" [.var "x", .var "x"])
    (.app "f" [.app "g" [.var "z"]]) = true := by decide
example : inlineSpine (.letBind "f" (.lam ["x"] (.app "add" [.var "x", .var "x"]))
    (.app "f" [.app "g" [.var "z"]])) =
      .letBind "x" (.app "g" [.var "z"]) (.app "add" [.var "x", .var "x"]) := by rfl
example : inlineSpine (.letBind "f" (.lam ["x"] (.var "y")) (.app "f" [.app "g" []])) =
      .letBind "x" (.app "g" []) (.var "y") := by rfl
example : closureOk "f" ["x"] (.app "mul" [.var "x", .var "c"])
    (.app "f" [.app "add" [.var "a", .var "b"]]) = false := by decide
example : blockOk "f" ["x"] (.app "mul" [.var "x", .var "c"])
    (.app "f" [.app "add" [.var "a", .var "b"]]) = true := by decide
example : closureOk "f" ["x"] (.app "add" [.var "x", .var "x"])
    (.forFold "i" (.var "lo") (.var "hi") (.app "f" [.app "g" []])) = false := by decide
example : blockOk "f" ["x"] (.app "add" [.var "x", .var "x"])
    (.forFold "i" (.var "lo") (.var "hi") (.app "f" [.app "g" []])) = false := by decide
example : closureOk "f" ["x"] (.app "add" [.var "x", .var "x"])
    (.match_ (.var "s") [(.varPat "q", .app "f" [.app "g" []])]) = false := by decide
example : blockOk "f" ["x"] (.app "add" [.var "x", .var "x"])
    (.match_ (.var "s") [(.varPat "q", .app "f" [.app "g" []])]) = false := by decide
example : closureOk "f" ["x"] (.app "add" [.var "x", .var "x"]) (.app "f" [.var "z"]) =
    true := by decide

end Hax.InlineLocalClosures
