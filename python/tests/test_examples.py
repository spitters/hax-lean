# Copyright (c) 2026 CatCrypt Contributors. MIT license.
"""The examples against the meaning of their Rust counterparts, and the decorators."""

import importlib.util
import os
import unittest
from types import ModuleType

import py2json
from catcrypt_py import U64, Array, entry, linked

EXAMPLES = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "examples")
M64 = (1 << 64) - 1


def load(name: str) -> ModuleType:
    path = os.path.join(EXAMPLES, f"{name}.py")
    spec = importlib.util.spec_from_file_location(f"examples.{name}", path)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def bind_loop_rust(a: list[int], k: int) -> list[int]:
    """``bind_loop`` of ``constructs-hax/src/lib.rs`` on ``u64`` values."""
    s = ((k ^ 0x5555_5555_5555_5555) + k) & M64
    return [x ^ s for x in a]


class BindLoopTest(unittest.TestCase):
    def setUp(self) -> None:
        self.mod = load("bind_loop")

    def run_py(self, a: list[int], k: int) -> list[int]:
        arr = Array[U64, 4]([U64(x) for x in a])
        return [int(x) for x in self.mod.bind_loop(arr, U64(k))]

    def test_rust_test_case(self) -> None:
        # The Rust test `bind_loop_value`.
        s = ((7 ^ 0x5555_5555_5555_5555) + 7) & M64
        self.assertEqual(self.run_py([1, 2, 3, 4], 7), [1 ^ s, 2 ^ s, 3 ^ s, 4 ^ s])

    def test_against_rust_meaning(self) -> None:
        for a, k in (([0, 0, 0, 0], 0), ([M64] * 4, M64), ([1, 2, 3, 4], 0xAAAA_AAAA_AAAA_AAAA),
                     ([5, M64, 0, 1 << 63], 1 << 63)):
            self.assertEqual(self.run_py(a, k), bind_loop_rust(a, k))

    def test_entry_marked(self) -> None:
        self.assertIs(self.mod.bind_loop.__catcrypt_entry__, True)
        self.assertEqual(self.mod.N, 4)

    def test_dumps(self) -> None:
        with open(os.path.join(EXAMPLES, "bind_loop.py"), "rb") as f:
            obj = py2json.dump_source(f.read(), "bind_loop.py")
        fn = [n for n in obj["module"]["body"] if n["_type"] == "FunctionDef"][0]
        self.assertEqual(fn["name"], "bind_loop")
        self.assertEqual(fn["decorator_list"][0]["id"], "entry")
        ann = fn["args"]["args"][0]["annotation"]
        self.assertEqual(ann["_type"], "Subscript")
        self.assertEqual(ann["value"]["id"], "Array")
        self.assertEqual([e["id"] for e in ann["slice"]["elts"]], ["U64", "N"])


class DecoratorTest(unittest.TestCase):
    def test_entry(self) -> None:
        def f(x: int) -> int:
            return x

        self.assertIs(entry(f), f)
        self.assertIs(f.__catcrypt_entry__, True)  # type: ignore[attr-defined]

    def test_linked(self) -> None:
        @linked
        def k1(x: int) -> int:
            return x

        @linked(name="fiat_p256_mul")
        def k2(x: int) -> int:
            return x

        self.assertEqual(k1.__catcrypt_linked__, "k1")  # type: ignore[attr-defined]
        self.assertEqual(k2.__catcrypt_linked__, "fiat_p256_mul")  # type: ignore[attr-defined]
        self.assertEqual(k2(3), 3)
        with self.assertRaises(TypeError):
            linked(name="")(k1)


if __name__ == "__main__":
    unittest.main()
