# Copyright (c) 2026 CatCrypt Contributors. MIT license.
"""The word heads at boundary values for the four widths."""

import unittest

from catcrypt_py import U8, U16, U32, U64, Word

WIDTHS: list[type[Word]] = [U8, U16, U32, U64]


class ConstructorTest(unittest.TestCase):
    def test_range(self) -> None:
        for W in WIDTHS:
            top = (1 << W.BITS) - 1
            self.assertEqual(int(W(0)), 0)
            self.assertEqual(int(W(1)), 1)
            self.assertEqual(int(W(top)), top)
            with self.assertRaises(ValueError):
                W(top + 1)
            with self.assertRaises(ValueError):
                W(-1)

    def test_bool_and_other_types_rejected(self) -> None:
        for W in WIDTHS:
            for bad in (True, False, 1.0, "1", None):
                with self.assertRaises(ValueError):
                    W(bad)  # type: ignore[arg-type]
        with self.assertRaises(TypeError):
            Word(1)

    def test_widening_from_word(self) -> None:
        for W in WIDTHS:
            for V in WIDTHS:
                top = (1 << V.BITS) - 1
                if V.BITS <= W.BITS:
                    for v in (0, 1, top):
                        x = W(V(v))
                        self.assertIs(type(x), W)
                        self.assertEqual(int(x), v)
                        self.assertEqual(x, V(v).cast(W))
                else:
                    with self.assertRaises(ValueError):
                        W(V(1))

    def test_immutable(self) -> None:
        x = U64(5)
        with self.assertRaises(AttributeError):
            x._v = 6  # type: ignore[misc]
        with self.assertRaises(AttributeError):
            x.y = 1  # type: ignore[attr-defined]
        with self.assertRaises(AttributeError):
            del x._v
        self.assertEqual(int(x), 5)

    def test_no_truthiness(self) -> None:
        for W in WIDTHS:
            with self.assertRaises(TypeError):
                bool(W(1))
            with self.assertRaises(TypeError):
                if W(0):
                    pass
            with self.assertRaises(TypeError):
                _ = not W(0)

    def test_index_int_repr(self) -> None:
        self.assertEqual(list(range(U8(3))), [0, 1, 2])
        self.assertEqual(int(U32(7)), 7)
        self.assertEqual(repr(U64(5)), "U64(5)")
        self.assertEqual(repr(U8(255)), "U8(255)")


class CheckedTest(unittest.TestCase):
    def test_add(self) -> None:
        for W in WIDTHS:
            top = (1 << W.BITS) - 1
            self.assertEqual(W(0) + W(0), W(0))
            self.assertEqual(W(top - 1) + W(1), W(top))
            self.assertEqual(W(top) + 0, W(top))
            self.assertEqual(1 + W(top - 1), W(top))
            with self.assertRaises(OverflowError):
                W(top) + W(1)
            with self.assertRaises(OverflowError):
                1 + W(top)
            with self.assertRaises(OverflowError):
                W(top) + W(top)

    def test_sub(self) -> None:
        for W in WIDTHS:
            top = (1 << W.BITS) - 1
            self.assertEqual(W(top) - W(top), W(0))
            self.assertEqual(W(1) - 1, W(0))
            self.assertEqual(top - W(1), W(top - 1))
            with self.assertRaises(OverflowError):
                W(0) - W(1)
            with self.assertRaises(OverflowError):
                W(top - 1) - top
            with self.assertRaises(OverflowError):
                0 - W(1)

    def test_mul(self) -> None:
        for W in WIDTHS:
            top = (1 << W.BITS) - 1
            half = 1 << (W.BITS // 2)
            self.assertEqual(W(top) * W(1), W(top))
            self.assertEqual(W(top) * 0, W(0))
            self.assertEqual(W(half - 1) * W(half + 1), W(top))
            self.assertEqual(2 * W(top >> 1), W(top - 1))
            with self.assertRaises(OverflowError):
                W(half) * W(half)
            with self.assertRaises(OverflowError):
                W(top) * 2

    def test_int_operand_read_as_word(self) -> None:
        for W in WIDTHS:
            top = (1 << W.BITS) - 1
            with self.assertRaises(ValueError):
                W(0) + (top + 1)
            with self.assertRaises(ValueError):
                W(1) - (-1)
            with self.assertRaises(ValueError):
                W(1) + True
            with self.assertRaises(ValueError):
                W(1) == True  # noqa: E712

    def test_width_mixing(self) -> None:
        for W in WIDTHS:
            for V in WIDTHS:
                if V is W:
                    continue
                for op in (lambda a, b: a + b, lambda a, b: a - b, lambda a, b: a * b,
                           lambda a, b: a & b, lambda a, b: a | b, lambda a, b: a ^ b,
                           lambda a, b: a == b, lambda a, b: a != b, lambda a, b: a < b,
                           lambda a, b: a <= b, lambda a, b: a > b, lambda a, b: a >= b,
                           lambda a, b: a.wrapping_add(b), lambda a, b: a.wrapping_sub(b),
                           lambda a, b: a.wrapping_mul(b)):
                    with self.assertRaises(TypeError):
                        op(W(1), V(1))

    def test_other_operand_types(self) -> None:
        with self.assertRaises(TypeError):
            U64(1) + 1.0  # type: ignore[operator]
        with self.assertRaises(TypeError):
            U64(1).wrapping_add("1")  # type: ignore[arg-type]
        with self.assertRaises(TypeError):
            U64(4) // U64(2)  # type: ignore[operator]
        with self.assertRaises(TypeError):
            U64(4) % U64(2)  # type: ignore[operator]
        with self.assertRaises(TypeError):
            -U64(1)  # type: ignore[operator]
        self.assertFalse(U64(1) == "1")


class WrappingTest(unittest.TestCase):
    def test_wrapping(self) -> None:
        for W in WIDTHS:
            top = (1 << W.BITS) - 1
            self.assertEqual(W(top).wrapping_add(W(1)), W(0))
            self.assertEqual(W(top).wrapping_add(top), W(top - 1))
            self.assertEqual(W(0).wrapping_add(0), W(0))
            self.assertEqual(W(0).wrapping_sub(W(1)), W(top))
            self.assertEqual(W(1).wrapping_sub(1), W(0))
            self.assertEqual(W(0).wrapping_sub(top), W(1))
            self.assertEqual(W(top).wrapping_mul(W(top)), W(1))
            self.assertEqual(W(top).wrapping_mul(0), W(0))
            self.assertEqual(W(1 << (W.BITS - 1)).wrapping_mul(2), W(0))

    def test_wrapping_neg(self) -> None:
        self.assertEqual(U64(0).wrapping_neg(), U64(0))
        self.assertEqual(U64(1).wrapping_neg(), U64((1 << 64) - 1))
        self.assertEqual(U64((1 << 64) - 1).wrapping_neg(), U64(1))
        self.assertEqual(U64(1 << 63).wrapping_neg(), U64(1 << 63))
        for W in (U8, U16, U32):
            self.assertFalse(hasattr(W(1), "wrapping_neg"))

    def test_mulhi(self) -> None:
        top = (1 << 64) - 1
        self.assertEqual(U64(0).mulhi(U64(top)), U64(0))
        self.assertEqual(U64(1).mulhi(top), U64(0))
        self.assertEqual(U64(top).mulhi(U64(top)), U64(top - 1))
        self.assertEqual(U64(1 << 63).mulhi(2), U64(1))
        for W in (U8, U16, U32):
            self.assertFalse(hasattr(W(1), "mulhi"))


class BitwiseTest(unittest.TestCase):
    def test_bitwise(self) -> None:
        for W in WIDTHS:
            top = (1 << W.BITS) - 1
            a, b = 0b1100 & top, 0b1010 & top
            self.assertEqual(W(a) & W(b), W(a & b))
            self.assertEqual(W(a) | W(b), W(a | b))
            self.assertEqual(W(a) ^ W(b), W(a ^ b))
            self.assertEqual(W(top) & 1, W(1))
            self.assertEqual(1 | W(0), W(1))
            self.assertEqual(top ^ W(top), W(0))
            self.assertEqual(~W(0), W(top))
            self.assertEqual(~W(top), W(0))
            self.assertEqual(~W(1), W(top - 1))


class ShiftRotateTest(unittest.TestCase):
    def test_shifts(self) -> None:
        for W in WIDTHS:
            w = W.BITS
            top = (1 << w) - 1
            self.assertEqual(W(1) << 0, W(1))
            self.assertEqual(W(1) << (w - 1), W(1 << (w - 1)))
            self.assertEqual(W(top) << 1, W(top - 1))
            self.assertEqual(W(top) >> (w - 1), W(1))
            self.assertEqual(W(top) >> 0, W(top))
            self.assertEqual(W(1) << U8(1), W(2))
            self.assertEqual(W(4) >> U64(2), W(1))
            for amount in (w, w + 1, U64(w), 1 << 70):
                with self.assertRaises(OverflowError):
                    W(1) << amount
                with self.assertRaises(OverflowError):
                    W(1) >> amount
            with self.assertRaises(ValueError):
                W(1) << -1
            with self.assertRaises(ValueError):
                W(1) << True
            with self.assertRaises(TypeError):
                W(1) << 1.0  # type: ignore[operator]

    def test_int_shifted_by_word_refused(self) -> None:
        with self.assertRaises(TypeError):
            1 << U64(1)  # type: ignore[operator]

    def test_rotations(self) -> None:
        for W in WIDTHS:
            w = W.BITS
            top = (1 << w) - 1
            hi = 1 << (w - 1)
            self.assertEqual(W(1).rotate_left(0), W(1))
            self.assertEqual(W(1).rotate_left(1), W(2))
            self.assertEqual(W(hi).rotate_left(1), W(1))
            self.assertEqual(W(1).rotate_right(1), W(hi))
            self.assertEqual(W(top).rotate_left(3), W(top))
            self.assertEqual(W(0).rotate_right(5), W(0))
            # Amounts modulo the width.
            self.assertEqual(W(1).rotate_left(w), W(1))
            self.assertEqual(W(1).rotate_left(w + 1), W(2))
            self.assertEqual(W(1).rotate_right(w + 1), W(hi))
            self.assertEqual(W(3).rotate_left(U8(w)), W(3))
            self.assertEqual(W(3).rotate_right(U64((1 << 64) - 1)),
                             W(3).rotate_right(((1 << 64) - 1) % w))
            with self.assertRaises(OverflowError):
                W(1).rotate_left(1 << 64)
            with self.assertRaises(ValueError):
                W(1).rotate_left(-1)

    def test_rotations_against_definition(self) -> None:
        for W in WIDTHS:
            w = W.BITS
            m = (1 << w) - 1
            x = 0x0123_4567_89AB_CDEF & m
            for n in (0, 1, 7, w - 1, w, 3 * w + 5):
                s = n % w
                left = ((x << s) | (x >> (w - s))) & m
                right = ((x >> s) | (x << (w - s))) & m
                self.assertEqual(int(W(x).rotate_left(n)), left)
                self.assertEqual(int(W(x).rotate_right(n)), right)


class CastTest(unittest.TestCase):
    def test_casts(self) -> None:
        for W in WIDTHS:
            top = (1 << W.BITS) - 1
            for V in WIDTHS:
                r = W(top).cast(V)
                self.assertIs(type(r), V)
                self.assertEqual(int(r), top % (1 << V.BITS))
                self.assertEqual(W(0).cast(V), V(0))
        self.assertEqual(U64(0x1_0000_0001).cast(U32), U32(1))
        self.assertEqual(U16(0x1234).cast(U8), U8(0x34))
        with self.assertRaises(TypeError):
            U64(1).cast(int)  # type: ignore[type-var]
        with self.assertRaises(TypeError):
            U64(1).cast(Word)


class ComparisonTest(unittest.TestCase):
    def test_comparisons(self) -> None:
        for W in WIDTHS:
            top = (1 << W.BITS) - 1
            a, b = W(0), W(top)
            self.assertIs(a == W(0), True)
            self.assertIs(a == b, False)
            self.assertIs(a != b, True)
            self.assertIs(a < b, True)
            self.assertIs(a <= a, True)
            self.assertIs(b > a, True)
            self.assertIs(b >= b, True)
            self.assertIs(a > b, False)
            self.assertIs(b == top, True)
            self.assertIs(top == b, True)
            self.assertIs(0 < b, True)
            self.assertIs(top >= a, True)

    def test_hash(self) -> None:
        self.assertEqual(hash(U64(5)), hash(U64(5)))
        self.assertEqual(hash(U32(5)), hash(5))
        self.assertEqual(len({U64(1), U64(1), U64(2)}), 2)


if __name__ == "__main__":
    unittest.main()
