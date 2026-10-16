# Copyright (c) 2026 CatCrypt Contributors. MIT license.
"""Arrays: construction, bounds, negative indices, immutability, ``set``."""

import unittest

from catcrypt_py import U8, U32, U64, Array, Secret, field


def a4(*vs: int) -> Array:
    return Array[U64, 4]([U64(v) for v in vs])


class ArrayClassTest(unittest.TestCase):
    def test_cached(self) -> None:
        self.assertIs(Array[U64, 4], Array[U64, 4])
        self.assertIsNot(Array[U64, 4], Array[U64, 5])
        self.assertIsNot(Array[U64, 4], Array[U32, 4])
        self.assertEqual(Array[U64, 4].LENGTH, 4)
        self.assertIs(Array[U64, 4].ELEMENT, U64)
        self.assertEqual(Array[U64, 4].__name__, "Array[U64, 4]")

    def test_parameters(self) -> None:
        with self.assertRaises(TypeError):
            Array[int, 4]  # type: ignore[misc]
        with self.assertRaises(TypeError):
            Array[U64, True]  # type: ignore[misc]
        with self.assertRaises(TypeError):
            Array[U64, 4.0]  # type: ignore[misc]
        with self.assertRaises(TypeError):
            Array[U64]  # type: ignore[misc]
        with self.assertRaises(ValueError):
            Array[U64, -1]  # type: ignore[misc]
        with self.assertRaises(TypeError):
            Array([U64(1)])
        with self.assertRaises(TypeError):
            Array[U64, 4][U64, 4]  # type: ignore[misc]

    def test_element_classes(self) -> None:
        Array[Secret[U64], 2]([Secret[U64](1), Secret[U64](2)])  # type: ignore[misc]
        F = field(17)
        self.assertEqual(Array[F, 2]([F(1), F(2)])[1], F(2))  # type: ignore[misc, valid-type]


class ConstructionTest(unittest.TestCase):
    def test_length(self) -> None:
        self.assertEqual(len(a4(1, 2, 3, 4)), 4)
        with self.assertRaises(ValueError):
            Array[U64, 4]([U64(1)] * 3)
        with self.assertRaises(ValueError):
            Array[U64, 4]([U64(1)] * 5)
        self.assertEqual(len(Array[U64, 0]([])), 0)

    def test_element_type(self) -> None:
        with self.assertRaises(TypeError):
            Array[U64, 2]([U64(1), 2])
        with self.assertRaises(TypeError):
            Array[U64, 2]([U64(1), U32(2)])
        with self.assertRaises(TypeError):
            Array[U64, 1]([Secret[U64](1)])  # type: ignore[misc]

    def test_filled(self) -> None:
        self.assertEqual(Array[U8, 3].filled(U8(7)), Array[U8, 3]([U8(7)] * 3))
        with self.assertRaises(TypeError):
            Array[U8, 3].filled(7)


class IndexTest(unittest.TestCase):
    def test_bounds(self) -> None:
        a = a4(10, 20, 30, 40)
        self.assertEqual(a[0], U64(10))
        self.assertEqual(a[3], U64(40))
        self.assertEqual(a[U8(2)], U64(30))
        self.assertEqual(a[U64(1)], U64(20))
        for bad in (4, 5, U64(4), 1 << 64):
            with self.assertRaises(IndexError):
                a[bad]
        for neg in (-1, -4, -5):
            with self.assertRaises(IndexError):
                a[neg]

    def test_index_types(self) -> None:
        a = a4(1, 2, 3, 4)
        with self.assertRaises(TypeError):
            a[True]
        with self.assertRaises(TypeError):
            a[1.0]  # type: ignore[index]
        with self.assertRaises(TypeError):
            a[0:2]  # type: ignore[index]
        with self.assertRaises(TypeError):
            a[Secret[U64](1)]  # type: ignore[index]

    def test_set(self) -> None:
        a = a4(1, 2, 3, 4)
        b = a.set(0, U64(9))
        self.assertEqual(b, a4(9, 2, 3, 4))
        self.assertEqual(a, a4(1, 2, 3, 4))
        self.assertEqual(a.set(U8(3), U64(0)), a4(1, 2, 3, 0))
        with self.assertRaises(IndexError):
            a.set(4, U64(0))
        with self.assertRaises(IndexError):
            a.set(-1, U64(0))
        with self.assertRaises(TypeError):
            a.set(0, 0)
        with self.assertRaises(TypeError):
            a.set(0, U32(0))
        with self.assertRaises(TypeError):
            a.set(Secret[U64](0), U64(0))  # type: ignore[arg-type]


class ImmutabilityTest(unittest.TestCase):
    def test_no_item_assignment(self) -> None:
        a = a4(1, 2, 3, 4)
        with self.assertRaises(TypeError):
            a[0] = U64(5)
        with self.assertRaises(TypeError):
            del a[0]
        with self.assertRaises(AttributeError):
            a._items = ()  # type: ignore[misc]
        self.assertEqual(a, a4(1, 2, 3, 4))

    def test_aliasing_not_observable(self) -> None:
        a = a4(1, 2, 3, 4)
        r = a
        r = r.set(0, U64(7))
        self.assertEqual(a[0], U64(1))
        self.assertEqual(r[0], U64(7))


class EqualityTest(unittest.TestCase):
    def test_equality(self) -> None:
        self.assertIs(a4(1, 2, 3, 4) == a4(1, 2, 3, 4), True)
        self.assertIs(a4(1, 2, 3, 4) == a4(1, 2, 3, 5), False)
        self.assertIs(a4(1, 2, 3, 4) != a4(1, 2, 3, 5), True)
        self.assertEqual(hash(a4(1, 2, 3, 4)), hash(a4(1, 2, 3, 4)))
        with self.assertRaises(TypeError):
            a4(1, 2, 3, 4) == Array[U64, 3]([U64(1)] * 3)
        self.assertIs(a4(1, 2, 3, 4) == (1, 2, 3, 4), False)

    def test_iteration_and_truthiness(self) -> None:
        self.assertEqual([int(x) for x in a4(1, 2, 3, 4)], [1, 2, 3, 4])
        with self.assertRaises(TypeError):
            bool(a4(1, 2, 3, 4))
        self.assertEqual(repr(Array[U8, 2]([U8(1), U8(2)])), "Array[U8, 2]([U8(1), U8(2)])")


if __name__ == "__main__":
    unittest.main()
