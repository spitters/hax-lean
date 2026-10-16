# Copyright (c) 2026 CatCrypt Contributors. MIT license.
"""Unsigned words of 8, 16, 32 and 64 bits.

A word of the class ``Uw`` (``w`` is the class attribute ``BITS``) holds an ``int`` value ``v``
with ``0 <= v < 2**w``. Each operator and method computes one call head of the table
``hax64WordOps`` in ``HaxLean/Semantics.lean`` (with the arms of ``hax64NarrowOps`` and
``hax64CmpOps`` it falls through to). Its docstring names the head with ``w`` for the width, so
that ``Add#w`` of ``U32`` is ``Add#32``. Where the head has no value, the operation raises
``OverflowError``.

Operands. The second operand of an arithmetic, bitwise or comparison operation is a word of the
same class or an ``int``. An ``int`` is read as ``Uw(n)``, so it raises ``ValueError`` outside
``[0, 2**w)`` and for a ``bool``. A word of another width raises ``TypeError``. A shift or
rotation amount is a non-negative ``int`` or a public word of any width. A secret operand
(module ``secret``) makes the result secret; a secret shift or rotation amount raises
``TypeError``.

A word has no truth value: ``bool(x)`` raises ``TypeError``, so ``if x:`` on a word fails in
CPython as the checker refuses it.
"""

from __future__ import annotations

from typing import ClassVar, NoReturn, Self

__all__ = ["U8", "U16", "U32", "U64", "Word"]

_TWO64 = 1 << 64


class _SecretBase:
    """The base class of the secret values of module ``secret``.

    A word method with a secret operand is computed by the secret class (``_lift``); any other
    use of a secret where a public value is required raises ``TypeError``.
    """

    __slots__ = ()

    def _lift(self, public: Word) -> _SecretBase:
        """The secret of the class of ``self`` holding the public word ``public``."""
        raise TypeError(f"{type(self).__name__} is not a secret word")


def _amount(k: object) -> int:
    """The value of a public shift or rotation amount: a word of any width or an ``int``.

    ``TypeError`` for a secret or any other type, ``ValueError`` for a ``bool`` or a negative
    ``int``.
    """
    if isinstance(k, _SecretBase):
        raise TypeError("a shift or rotation amount is public; declassify it first")
    if isinstance(k, Word):
        return k._v
    if isinstance(k, bool):
        raise ValueError("a shift or rotation amount is an int or a word, not a bool")
    if isinstance(k, int):
        if k < 0:
            raise ValueError("a shift or rotation amount is non-negative")
        return int(k)
    raise TypeError(f"a shift or rotation amount is an int or a word, not {type(k).__name__}")


def rotl(w: int, x: int, n: int) -> int:
    """``rotlNat w x n``: ``x mod 2**w`` rotated left by ``n mod w`` bits."""
    m = (1 << w) - 1
    x &= m
    s = n % w
    return ((x << s) | (x >> (w - s))) & m


def rotr(w: int, x: int, n: int) -> int:
    """``rotrNat w x n``: ``x mod 2**w`` rotated right by ``n mod w`` bits."""
    m = (1 << w) - 1
    x &= m
    s = n % w
    return ((x >> s) | (x << (w - s))) & m


class Word:
    """An unsigned word. The subclasses ``U8``, ``U16``, ``U32``, ``U64`` fix the width ``BITS``.

    Instances are immutable: attribute assignment and deletion raise ``AttributeError``.
    """

    __slots__ = ("_v",)
    BITS: ClassVar[int] = 0
    _v: int

    def __new__(cls, n: int) -> Self:
        """The word of value ``n``: an ``int`` (not a ``bool``) with ``0 <= n < 2**BITS``.

        ``ValueError`` for any other argument. No call head: a literal of type ``Uw``.
        """
        if cls.BITS == 0:
            raise TypeError("Word is abstract; use U8, U16, U32 or U64")
        if isinstance(n, bool) or not isinstance(n, int):
            raise ValueError(f"{cls.__name__} takes an int, not {type(n).__name__}")
        if not 0 <= n < (1 << cls.BITS):
            raise ValueError(f"{cls.__name__} takes an int in [0, 2**{cls.BITS})")
        return cls._of(int(n))

    @classmethod
    def _of(cls, v: int) -> Self:
        """The word of value ``v``, with ``0 <= v < 2**BITS`` known to the caller."""
        x = object.__new__(cls)
        object.__setattr__(x, "_v", v)
        return x

    def __setattr__(self, name: str, value: object) -> NoReturn:
        """Words are immutable: ``AttributeError``."""
        raise AttributeError(f"{type(self).__name__} is immutable")

    def __delattr__(self, name: str) -> NoReturn:
        """Words are immutable: ``AttributeError``."""
        raise AttributeError(f"{type(self).__name__} is immutable")

    # Operands

    def _operand(self, other: object) -> int | None:
        """The value of a second operand: a word of this class, or an ``int`` read as one.

        ``TypeError`` for a word of another width; ``None`` for any other type, on which a
        binary operator returns ``NotImplemented``.
        """
        cls = type(self)
        if isinstance(other, Word):
            if type(other) is not cls:
                raise TypeError(
                    f"operands of widths {cls.BITS} and {other.BITS}: "
                    f"{cls.__name__} and {type(other).__name__}"
                )
            return other._v
        if isinstance(other, int):
            return cls(other)._v
        return None

    def _method_operand(self, other: object, name: str) -> int:
        """The value of the argument of the method ``name``; ``TypeError`` for a wrong type."""
        b = self._operand(other)
        if b is None:
            cls = type(self).__name__
            raise TypeError(f"{cls}.{name} takes a {cls} or an int, not {type(other).__name__}")
        return b

    # Checked arithmetic

    def __add__(self, other: Self | int) -> Self:
        """Head ``Add#w``: the sum ``a + b``; ``OverflowError`` when ``a + b >= 2**w``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of(_checked_add(self.BITS, self._v, b))

    def __radd__(self, other: int) -> Self:
        """Head ``Add#w`` with the ``int`` on the left: ``n + a``, checked as ``__add__``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of(_checked_add(self.BITS, b, self._v))

    def __sub__(self, other: Self | int) -> Self:
        """Head ``Sub#w``: the difference ``a - b``; ``OverflowError`` when ``b > a``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of(_checked_sub(self.BITS, self._v, b))

    def __rsub__(self, other: int) -> Self:
        """Head ``Sub#w`` with the ``int`` on the left: ``n - a``; ``OverflowError`` when
        ``a > n``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of(_checked_sub(self.BITS, b, self._v))

    def __mul__(self, other: Self | int) -> Self:
        """Head ``Mul#w``: the product ``a * b``; ``OverflowError`` when ``a * b >= 2**w``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of(_checked_mul(self.BITS, self._v, b))

    def __rmul__(self, other: int) -> Self:
        """Head ``Mul#w`` with the ``int`` on the left: ``n * a``, checked as ``__mul__``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of(_checked_mul(self.BITS, b, self._v))

    # Wrapping arithmetic

    def wrapping_add(self, other: Self | int) -> Self:
        """Head ``wrapping_add#w``: ``(a + b) mod 2**w``."""
        if isinstance(other, _SecretBase):
            return other._lift(self).wrapping_add(other)
        b = self._method_operand(other, "wrapping_add")
        return self._of((self._v + b) & ((1 << self.BITS) - 1))

    def wrapping_sub(self, other: Self | int) -> Self:
        """Head ``wrapping_sub#w``: ``(a + 2**w - b) mod 2**w``."""
        if isinstance(other, _SecretBase):
            return other._lift(self).wrapping_sub(other)
        b = self._method_operand(other, "wrapping_sub")
        return self._of((self._v - b) & ((1 << self.BITS) - 1))

    def wrapping_mul(self, other: Self | int) -> Self:
        """Head ``wrapping_mul#w``: ``(a * b) mod 2**w``."""
        if isinstance(other, _SecretBase):
            return other._lift(self).wrapping_mul(other)
        b = self._method_operand(other, "wrapping_mul")
        return self._of((self._v * b) & ((1 << self.BITS) - 1))

    # Bitwise operations

    def __and__(self, other: Self | int) -> Self:
        """Head ``BitAnd#w``: the bitwise conjunction ``a & b``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of(self._v & b)

    def __rand__(self, other: int) -> Self:
        """Head ``BitAnd#w`` with the ``int`` on the left: ``n & a``."""
        return self.__and__(other)

    def __or__(self, other: Self | int) -> Self:
        """Head ``BitOr#w``: the bitwise disjunction ``a | b``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of(self._v | b)

    def __ror__(self, other: int) -> Self:
        """Head ``BitOr#w`` with the ``int`` on the left: ``n | a``."""
        return self.__or__(other)

    def __xor__(self, other: Self | int) -> Self:
        """Head ``BitXor#w``: the bitwise exclusive disjunction ``a ^ b``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of(self._v ^ b)

    def __rxor__(self, other: int) -> Self:
        """Head ``BitXor#w`` with the ``int`` on the left: ``n ^ a``."""
        return self.__xor__(other)

    def __invert__(self) -> Self:
        """Head ``Not#w``: the complement ``2**w - 1 - a``."""
        return self._of((1 << self.BITS) - 1 - self._v)

    # Shifts and rotations

    def __lshift__(self, k: Word | int) -> Self:
        """Head ``Shl#w``: ``(a << k) mod 2**w``; ``OverflowError`` when ``k >= w``.

        ``k`` is a non-negative ``int`` or a public word of any width.
        """
        n = _amount(k)
        if n >= self.BITS:
            raise OverflowError(f"Shl#{self.BITS}: shift amount >= {self.BITS}")
        return self._of((self._v << n) & ((1 << self.BITS) - 1))

    def __rshift__(self, k: Word | int) -> Self:
        """Head ``Shr#w``: ``a >> k``; ``OverflowError`` when ``k >= w``.

        ``k`` is a non-negative ``int`` or a public word of any width.
        """
        n = _amount(k)
        if n >= self.BITS:
            raise OverflowError(f"Shr#{self.BITS}: shift amount >= {self.BITS}")
        return self._of(self._v >> n)

    def rotate_left(self, k: Word | int) -> Self:
        """Head ``rotate_left#w``: ``a`` rotated left by ``k mod w`` bits (``rotlNat``).

        ``k`` is a public word of any width or an ``int`` in ``[0, 2**64)``; the table has no
        value at a larger ``int`` (``OverflowError``).
        """
        n = _amount(k)
        if n >= _TWO64:
            raise OverflowError(f"rotate_left#{self.BITS}: amount >= 2**64")
        return self._of(rotl(self.BITS, self._v, n))

    def rotate_right(self, k: Word | int) -> Self:
        """Head ``rotate_right#w``: ``a`` rotated right by ``k mod w`` bits (``rotrNat``).

        ``k`` is a public word of any width or an ``int`` in ``[0, 2**64)``; the table has no
        value at a larger ``int`` (``OverflowError``).
        """
        n = _amount(k)
        if n >= _TWO64:
            raise OverflowError(f"rotate_right#{self.BITS}: amount >= 2**64")
        return self._of(rotr(self.BITS, self._v, n))

    # Conversion

    def cast[W: Word](self, target: type[W]) -> W:
        """Head ``cast#w2`` for ``target = Uw2``: the word ``a mod 2**w2`` of class ``target``."""
        if not (isinstance(target, type) and issubclass(target, Word) and target.BITS):
            raise TypeError(f"cast takes U8, U16, U32 or U64, not {target!r}")
        return target._of(self._v & ((1 << target.BITS) - 1))

    # Comparisons

    def __eq__(self, other: object) -> bool:
        """Head ``Eq``: ``a == b``, a ``bool``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._v == b

    def __ne__(self, other: object) -> bool:
        """Head ``Ne``: ``a != b``, a ``bool``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._v != b

    def __lt__(self, other: Self | int) -> bool:
        """Head ``Lt``: ``a < b``, a ``bool``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._v < b

    def __le__(self, other: Self | int) -> bool:
        """Head ``Le``: ``a <= b``, a ``bool``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._v <= b

    def __gt__(self, other: Self | int) -> bool:
        """Head ``Gt``: ``a > b``, a ``bool``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._v > b

    def __ge__(self, other: Self | int) -> bool:
        """Head ``Ge``: ``a >= b``, a ``bool``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._v >= b

    def __hash__(self) -> int:
        """No call head: the hash of the value, so that ``Uw(n) == n`` implies equal hashes."""
        return hash(self._v)

    # Python protocols

    def __bool__(self) -> NoReturn:
        """No call head: a word has no truth value; ``TypeError``."""
        raise TypeError(f"{type(self).__name__} has no truth value; compare it with a value")

    def __index__(self) -> int:
        """No call head: the value ``v``, read by ``range`` and by sequence indexing."""
        return self._v

    def __int__(self) -> int:
        """No call head: the value ``v``."""
        return self._v

    def __repr__(self) -> str:
        """No call head: the constructor call, for example ``U64(5)``."""
        return f"{type(self).__name__}({self._v})"


def _checked_add(w: int, a: int, b: int) -> int:
    """``uintAddOp w a b``: ``a + b``; ``OverflowError`` when it is ``2**w`` or more."""
    r = a + b
    if r >> w:
        raise OverflowError(f"Add#{w}: {a} + {b} >= 2**{w}")
    return r


def _checked_sub(w: int, a: int, b: int) -> int:
    """``uintSubOp w a b``: ``a - b``; ``OverflowError`` when ``b > a``."""
    if b > a:
        raise OverflowError(f"Sub#{w}: {b} > {a}")
    return a - b


def _checked_mul(w: int, a: int, b: int) -> int:
    """``uintMulOp w a b``: ``a * b``; ``OverflowError`` when it is ``2**w`` or more."""
    r = a * b
    if r >> w:
        raise OverflowError(f"Mul#{w}: {a} * {b} >= 2**{w}")
    return r


class U8(Word):
    """Unsigned 8-bit words, Rust ``u8``; heads tagged ``#8``."""

    __slots__ = ()
    BITS = 8


class U16(Word):
    """Unsigned 16-bit words, Rust ``u16``; heads tagged ``#16``."""

    __slots__ = ()
    BITS = 16


class U32(Word):
    """Unsigned 32-bit words, Rust ``u32``; heads tagged ``#32``."""

    __slots__ = ()
    BITS = 32


class U64(Word):
    """Unsigned 64-bit words, Rust ``u64``; heads tagged ``#64``.

    Beside the methods of every width: ``wrapping_neg`` and ``mulhi``.
    """

    __slots__ = ()
    BITS = 64

    def wrapping_neg(self) -> U64:
        """Head ``wrapping_neg#64``: ``(2**64 - a) mod 2**64``."""
        return U64._of((_TWO64 - self._v) % _TWO64)

    def mulhi(self, other: U64 | int) -> U64:
        """Head ``mulhi#64``: ``(a * b) >> 64``, the high word of the 128-bit product."""
        if isinstance(other, _SecretBase):
            return other._lift(self).mulhi(other)  # type: ignore[attr-defined, no-any-return]
        b = self._method_operand(other, "mulhi")
        return U64._of((self._v * b) >> 64)
