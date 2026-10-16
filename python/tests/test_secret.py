# Copyright (c) 2026 CatCrypt Contributors. MIT license.
"""Secrets: closed operations, public amounts, no truthiness, no secret index, ``select``."""

import unittest

from catcrypt_py import U8, U32, U64, Array, Secret, SecretBool, select

S64 = Secret[U64]
S32 = Secret[U32]
TOP = (1 << 64) - 1


class SecretClassTest(unittest.TestCase):
    def test_class(self) -> None:
        self.assertIs(Secret[U64], S64)
        self.assertIs(S64.WORD, U64)
        self.assertEqual(S64.__name__, "Secret[U64]")
        with self.assertRaises(TypeError):
            Secret[int]  # type: ignore[misc]
        with self.assertRaises(TypeError):
            Secret(U64(1))
        with self.assertRaises(TypeError):
            S64(U32(1))
        with self.assertRaises(TypeError):
            S64(S64(1))
        with self.assertRaises(ValueError):
            S64(-1)

    def test_declassify(self) -> None:
        self.assertEqual(S64(5).declassify(), U64(5))
        self.assertIs(type(S64(5).declassify()), U64)
        self.assertIs((S64(5) == 5).declassify(), True)
        self.assertIs((S64(5) < S64(4)).declassify(), False)


class SecretOpsTest(unittest.TestCase):
    def test_closed(self) -> None:
        s, t = S64(6), S64(3)
        for r, v in ((s + t, 9), (s - t, 3), (s * t, 18), (s & t, 2), (s | t, 7), (s ^ t, 5),
                     (s + 1, 7), (1 + s, 7), (U64(1) + s, 7), (10 - s, 4), (U64(2) * s, 12),
                     (s.wrapping_sub(7), TOP), (s.wrapping_add(U64(TOP)), 5),
                     (s.wrapping_mul(t), 18), (U64(1).wrapping_sub(s), TOP - 4),
                     (s << 1, 12), (s >> U8(1), 3), (~S64(0), TOP),
                     (S64(1).rotate_right(1), 1 << 63), (S64(1 << 63).rotate_left(1), 1),
                     (S64(1).wrapping_neg(), TOP), (S64(TOP).mulhi(TOP), TOP - 1),
                     (U64(TOP).mulhi(S64(2)), 1)):
            self.assertIsInstance(r, S64)
            self.assertEqual(int(r.declassify()), v)
        c = S64(0x1_0000_0002).cast(U32)
        self.assertIs(type(c), S32)
        self.assertEqual(c.declassify(), U32(2))

    def test_checked_failures(self) -> None:
        with self.assertRaises(OverflowError):
            S64(TOP) + 1
        with self.assertRaises(OverflowError):
            S64(0) - S64(1)
        with self.assertRaises(OverflowError):
            S64(1 << 32) * (1 << 32)
        with self.assertRaises(OverflowError):
            S64(1) << 64

    def test_mixing(self) -> None:
        with self.assertRaises(TypeError):
            S64(1) + S32(1)  # type: ignore[operator]
        with self.assertRaises(TypeError):
            S64(1) + U32(1)  # type: ignore[operator]
        with self.assertRaises(TypeError):
            U32(1) + S64(1)  # type: ignore[operator]
        with self.assertRaises(TypeError):
            S32(1).wrapping_add(U64(1))

    def test_public_amounts(self) -> None:
        for f in (lambda: S64(1) << S64(1), lambda: S64(1) >> S64(1),
                  lambda: U64(1) << S64(1), lambda: U64(1) >> S64(1),
                  lambda: S64(1).rotate_left(S64(1)), lambda: U64(1).rotate_right(S64(1)),
                  lambda: S64(1).rotate_left(SecretBool(True))):
            with self.assertRaises(TypeError):
                f()

    def test_comparisons_secret(self) -> None:
        s = S64(5)
        for c, v in ((s == 5, True), (s != 5, False), (s < 6, True), (s <= 4, False),
                     (s > U64(4), True), (s >= S64(6), False), (5 == s, True), (U64(6) > s, True)):
            self.assertIsInstance(c, SecretBool)
            self.assertIs(c.declassify(), v)


class NoEscapeTest(unittest.TestCase):
    def test_if_raises(self) -> None:
        s = S64(1)
        with self.assertRaises(TypeError):
            if s:
                pass
        with self.assertRaises(TypeError):
            if s == 1:
                pass
        with self.assertRaises(TypeError):
            _ = (s < 2) and True
        with self.assertRaises(TypeError):
            _ = not (s < 2)

    def test_index_raises(self) -> None:
        a = Array[U64, 4]([U64(i) for i in range(4)])
        s = S64(1)
        with self.assertRaises(TypeError):
            a[s]  # type: ignore[index]
        with self.assertRaises(TypeError):
            [1, 2][s]  # type: ignore[index]
        with self.assertRaises(TypeError):
            range(s)  # type: ignore[call-overload]
        with self.assertRaises(TypeError):
            int(s)  # type: ignore[call-overload]
        with self.assertRaises(TypeError):
            hash(s)

    def test_secret_bool(self) -> None:
        b = SecretBool(True)
        with self.assertRaises(TypeError):
            bool(b)
        with self.assertRaises(TypeError):
            b == SecretBool(True)
        with self.assertRaises(TypeError):
            SecretBool(1)  # type: ignore[arg-type]
        self.assertIs(b.declassify(), True)

    def test_immutable(self) -> None:
        s = S64(1)
        with self.assertRaises(AttributeError):
            s._w = U64(2)  # type: ignore[misc]
        self.assertEqual(repr(s), "Secret[U64](...)")


class SelectTest(unittest.TestCase):
    def test_public_condition(self) -> None:
        self.assertEqual(select(True, U64(1), U64(2)), U64(1))
        self.assertEqual(select(False, U64(1), U64(2)), U64(2))
        a, b = Array[U8, 1]([U8(1)]), Array[U8, 1]([U8(2)])
        self.assertIs(select(False, a, b), b)
        with self.assertRaises(TypeError):
            select(True, U64(1), U32(2))
        with self.assertRaises(TypeError):
            select(1, U64(1), U64(2))  # type: ignore[arg-type]
        with self.assertRaises(TypeError):
            select(U64(1), U64(1), U64(2))  # type: ignore[arg-type]

    def test_secret_condition(self) -> None:
        c = S64(3) < S64(4)
        r = select(c, U64(1), U64(2))
        self.assertIsInstance(r, S64)
        self.assertEqual(r.declassify(), U64(1))
        r = select(S64(3) > 4, S64(1), S64(2))
        self.assertEqual(r.declassify(), U64(2))
        with self.assertRaises(TypeError):
            select(c, S64(1), U64(2))
        with self.assertRaises(TypeError):
            select(c, Array[U8, 1]([U8(1)]), Array[U8, 1]([U8(2)]))


if __name__ == "__main__":
    unittest.main()
