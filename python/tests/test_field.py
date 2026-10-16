# Copyright (c) 2026 CatCrypt Contributors. MIT license.
"""Residues at the BabyBear modulus ``p = 2013265921``."""

import unittest

from catcrypt_py import U64, field

P = 2013265921
F = field(P)


class FieldClassTest(unittest.TestCase):
    def test_class(self) -> None:
        self.assertIs(field(P), F)
        self.assertEqual(F.p, P)
        self.assertEqual(F.head("mul"), "mul#p2013265921")
        self.assertEqual(repr(F(5)), "field(2013265921)(5)")

    def test_modulus_range(self) -> None:
        for bad in (0, 1, -5, 1 << 64, True):
            with self.assertRaises(ValueError):
                field(bad)
        self.assertEqual(field((1 << 64) - 1).p, (1 << 64) - 1)
        self.assertEqual(field(2).p, 2)

    def test_constructor(self) -> None:
        self.assertEqual(int(F(0)), 0)
        self.assertEqual(int(F(P - 1)), P - 1)
        for bad in (P, -1, True, 1.0):
            with self.assertRaises(ValueError):
                F(bad)


class FieldOpsTest(unittest.TestCase):
    def test_add_sub(self) -> None:
        self.assertEqual(F(P - 1) + F(1), F(0))
        self.assertEqual(F(P - 1) + F(P - 1), F(P - 2))
        self.assertEqual(F(0) - F(1), F(P - 1))
        self.assertEqual(F(5) - F(5), F(0))
        self.assertEqual(1 + F(P - 1), F(0))
        self.assertEqual(0 - F(1), F(P - 1))
        self.assertEqual(F(3) - 4, F(P - 1))

    def test_mul_neg_square_double(self) -> None:
        self.assertEqual(F(P - 1) * F(P - 1), F(1))
        self.assertEqual(F(1 << 30) * F(4), F((1 << 32) % P))
        self.assertEqual(2 * F(P - 1), F(P - 2))
        self.assertEqual(-F(0), F(0))
        self.assertEqual(-F(1), F(P - 1))
        self.assertEqual(F(P - 1).square(), F(1))
        self.assertEqual(F(12345).square(), F(12345 * 12345 % P))
        self.assertEqual(F(P - 1).double(), F(P - 2))
        self.assertEqual(F(0).double(), F(0))

    def test_against_definition(self) -> None:
        for a in (0, 1, 2, P // 2, P - 2, P - 1):
            for b in (0, 1, P // 3, P - 1):
                self.assertEqual(int(F(a) + F(b)), (a + b) % P)
                self.assertEqual(int(F(a) - F(b)), (a + P - b) % P)
                self.assertEqual(int(F(a) * F(b)), (a * b) % P)
            self.assertEqual(int(-F(a)), (P - a) % P)

    def test_equality_and_mixing(self) -> None:
        self.assertIs(F(3) == F(3), True)
        self.assertIs(F(3) == 3, True)
        self.assertIs(F(3) != F(4), True)
        self.assertEqual(hash(F(3)), hash(3))
        G = field(17)
        with self.assertRaises(TypeError):
            F(1) + G(1)  # type: ignore[operator]
        with self.assertRaises(TypeError):
            F(1) == G(1)
        with self.assertRaises(TypeError):
            F(1) + U64(1)  # type: ignore[operator]
        with self.assertRaises(ValueError):
            F(1) + P

    def test_immutable_and_no_truthiness(self) -> None:
        x = F(3)
        with self.assertRaises(AttributeError):
            x._r = 4  # type: ignore[misc]
        with self.assertRaises(TypeError):
            bool(x)
        with self.assertRaises(TypeError):
            F(1) < F(2)  # type: ignore[operator]


if __name__ == "__main__":
    unittest.main()
