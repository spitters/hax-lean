# Copyright (c) 2026 CatCrypt Contributors. MIT license.
"""Secret words, secret Booleans and the selection ``select``.

``Secret[W]`` for a word class ``W`` is the class of secret words of ``W``. Its operations are
those of ``W`` (module ``words``), with the same call heads and meanings; an operand is a secret
of the same class, a public word of ``W`` or an ``int`` read as ``W(n)``, and the result is a
secret. A shift or rotation amount is public. A comparison gives a ``SecretBool``.

A secret has no truth value, no ``__index__`` and no ``__int__``: ``if s:``, ``range(s)``,
``a[s]`` and ``int(s)`` raise ``TypeError`` in CPython, as the checker refuses a branch, a loop
bound or an index on a secret. ``declassify()`` is the only way from a secret to a public value.
The checker lists the bindings of a ``Secret`` type in the record ``_fnSecrecy``; the call heads
are those of ``W``.
"""

from __future__ import annotations

from typing import Any, ClassVar, NoReturn, Self, TypeVar, overload

from .words import U64, Word, _amount, _SecretBase

__all__ = ["Secret", "SecretBool", "select"]

_T = TypeVar("_T")


class Secret(_SecretBase):
    """A secret word; ``Secret[W]`` is the class of secret words of the word class ``W``.

    ``Secret[W](x)`` takes a word of class ``W`` or an ``int`` read as ``W(x)``. Instances are
    immutable and unhashable.
    """

    __slots__ = ("_w",)
    WORD: ClassVar[type[Word]]
    _w: Word
    _classes: ClassVar[dict[type[Word], type[Secret]]] = {}

    def __class_getitem__(cls, word: type[Word]) -> type[Secret]:
        """The class ``Secret[W]`` of the word class ``W``, created once and cached."""
        if cls is not Secret:
            raise TypeError(f"{cls.__name__} is already specialised")
        return _secret_class(word)

    def __new__(cls, value: Word | int) -> Self:
        """The secret holding ``value``: a word of class ``WORD`` or an ``int`` read as one.

        No call head: the secrecy of a binding is a record of the checker, not a call.
        """
        if not hasattr(cls, "WORD"):
            raise TypeError("use Secret[W] for a word class W")
        if isinstance(value, _SecretBase):
            raise TypeError("the value is already secret")
        if isinstance(value, Word):
            if type(value) is not cls.WORD:
                raise TypeError(f"{cls.__name__} holds a {cls.WORD.__name__}, "
                                f"not a {type(value).__name__}")
            return cls._of(value)
        return cls._of(cls.WORD(value))

    @classmethod
    def _of(cls, w: Word) -> Self:
        """The secret holding the word ``w`` of class ``WORD``."""
        x = object.__new__(cls)
        object.__setattr__(x, "_w", w)
        return x

    def _lift(self, public: Word) -> Self:
        """The secret of the class of ``self`` holding the public word ``public``."""
        if type(public) is not self.WORD:
            raise TypeError(f"operands {type(public).__name__} and {type(self).__name__}")
        return type(self)._of(public)

    def __setattr__(self, name: str, value: object) -> NoReturn:
        """Secrets are immutable: ``AttributeError``."""
        raise AttributeError(f"{type(self).__name__} is immutable")

    def __delattr__(self, name: str) -> NoReturn:
        """Secrets are immutable: ``AttributeError``."""
        raise AttributeError(f"{type(self).__name__} is immutable")

    def declassify(self) -> Word:
        """No call head: the public word the secret holds."""
        return self._w

    def _operand(self, other: object) -> Word | None:
        """The word of a second operand: a secret of this class, a public word of ``WORD``, or
        an ``int`` read as one; ``TypeError`` for another width, ``None`` for another type."""
        if isinstance(other, Secret):
            if type(other) is not type(self):
                raise TypeError(f"operands {type(self).__name__} and {type(other).__name__}")
            return other._w
        if isinstance(other, Word):
            if type(other) is not self.WORD:
                raise TypeError(f"operands {type(self).__name__} and {type(other).__name__}")
            return other
        if isinstance(other, int):
            return self.WORD(other)
        return None

    def _method_operand(self, other: object, name: str) -> Word:
        """The word of the argument of the method ``name``; ``TypeError`` for a wrong type."""
        b = self._operand(other)
        if b is None:
            raise TypeError(f"{type(self).__name__}.{name} takes a secret, a word or an int, "
                            f"not {type(other).__name__}")
        return b

    @staticmethod
    def _public_amount(k: object) -> Word | int:
        """A shift or rotation amount, which is public: ``TypeError`` for a secret."""
        _amount(k)
        assert isinstance(k, (Word, int))
        return k

    # Checked arithmetic, heads Add#w, Sub#w, Mul#w

    def __add__(self, other: Secret | Word | int) -> Self:
        """Head ``Add#w``: the sum ``a + b``; ``OverflowError`` when ``a + b >= 2**w``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of(self._w + b)

    def __radd__(self, other: Word | int) -> Self:
        """Head ``Add#w`` with the public operand on the left: ``b + a``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of(b + self._w)

    def __sub__(self, other: Secret | Word | int) -> Self:
        """Head ``Sub#w``: the difference ``a - b``; ``OverflowError`` when ``b > a``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of(self._w - b)

    def __rsub__(self, other: Word | int) -> Self:
        """Head ``Sub#w`` with the public operand on the left: ``b - a``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of(b - self._w)

    def __mul__(self, other: Secret | Word | int) -> Self:
        """Head ``Mul#w``: the product ``a * b``; ``OverflowError`` when ``a * b >= 2**w``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of(self._w * b)

    def __rmul__(self, other: Word | int) -> Self:
        """Head ``Mul#w`` with the public operand on the left: ``b * a``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of(b * self._w)

    # Wrapping arithmetic

    def wrapping_add(self, other: Secret | Word | int) -> Self:
        """Head ``wrapping_add#w``: ``(a + b) mod 2**w``."""
        return self._of(self._w.wrapping_add(self._method_operand(other, "wrapping_add")))

    def wrapping_sub(self, other: Secret | Word | int) -> Self:
        """Head ``wrapping_sub#w``: ``(a + 2**w - b) mod 2**w``."""
        return self._of(self._w.wrapping_sub(self._method_operand(other, "wrapping_sub")))

    def wrapping_mul(self, other: Secret | Word | int) -> Self:
        """Head ``wrapping_mul#w``: ``(a * b) mod 2**w``."""
        return self._of(self._w.wrapping_mul(self._method_operand(other, "wrapping_mul")))

    # Bitwise operations

    def __and__(self, other: Secret | Word | int) -> Self:
        """Head ``BitAnd#w``: ``a & b``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of(self._w & b)

    def __rand__(self, other: Word | int) -> Self:
        """Head ``BitAnd#w`` with the public operand on the left: ``b & a``."""
        return self.__and__(other)

    def __or__(self, other: Secret | Word | int) -> Self:
        """Head ``BitOr#w``: ``a | b``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of(self._w | b)

    def __ror__(self, other: Word | int) -> Self:
        """Head ``BitOr#w`` with the public operand on the left: ``b | a``."""
        return self.__or__(other)

    def __xor__(self, other: Secret | Word | int) -> Self:
        """Head ``BitXor#w``: ``a ^ b``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of(self._w ^ b)

    def __rxor__(self, other: Word | int) -> Self:
        """Head ``BitXor#w`` with the public operand on the left: ``b ^ a``."""
        return self.__xor__(other)

    def __invert__(self) -> Self:
        """Head ``Not#w``: ``2**w - 1 - a``."""
        return self._of(~self._w)

    # Shifts and rotations, by public amounts

    def __lshift__(self, k: Word | int) -> Self:
        """Head ``Shl#w``: ``(a << k) mod 2**w``; ``OverflowError`` when ``k >= w``; ``TypeError``
        for a secret ``k``."""
        return self._of(self._w << self._public_amount(k))

    def __rshift__(self, k: Word | int) -> Self:
        """Head ``Shr#w``: ``a >> k``; ``OverflowError`` when ``k >= w``; ``TypeError`` for a
        secret ``k``."""
        return self._of(self._w >> self._public_amount(k))

    def rotate_left(self, k: Word | int) -> Self:
        """Head ``rotate_left#w``: ``a`` rotated left by ``k mod w`` bits; ``TypeError`` for a
        secret ``k``."""
        return self._of(self._w.rotate_left(self._public_amount(k)))

    def rotate_right(self, k: Word | int) -> Self:
        """Head ``rotate_right#w``: ``a`` rotated right by ``k mod w`` bits; ``TypeError`` for a
        secret ``k``."""
        return self._of(self._w.rotate_right(self._public_amount(k)))

    def cast(self, target: type[Word]) -> Secret:
        """Head ``cast#w2`` for ``target = Uw2``: the secret word ``a mod 2**w2``."""
        return _secret_class(target)._of(self._w.cast(target))

    # Comparisons, with a SecretBool result

    def __eq__(self, other: object) -> SecretBool:  # type: ignore[override]
        """Head ``Eq``: ``a == b``, a ``SecretBool``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return SecretBool(self._w == b)

    def __ne__(self, other: object) -> SecretBool:  # type: ignore[override]
        """Head ``Ne``: ``a != b``, a ``SecretBool``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return SecretBool(self._w != b)

    def __lt__(self, other: Secret | Word | int) -> SecretBool:
        """Head ``Lt``: ``a < b``, a ``SecretBool``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return SecretBool(self._w < b)

    def __le__(self, other: Secret | Word | int) -> SecretBool:
        """Head ``Le``: ``a <= b``, a ``SecretBool``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return SecretBool(self._w <= b)

    def __gt__(self, other: Secret | Word | int) -> SecretBool:
        """Head ``Gt``: ``a > b``, a ``SecretBool``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return SecretBool(self._w > b)

    def __ge__(self, other: Secret | Word | int) -> SecretBool:
        """Head ``Ge``: ``a >= b``, a ``SecretBool``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return SecretBool(self._w >= b)

    __hash__ = None  # type: ignore[assignment]

    def __bool__(self) -> NoReturn:
        """No call head: a secret has no truth value; ``TypeError``."""
        raise TypeError("a secret has no truth value; use select or declassify")

    def __repr__(self) -> str:
        """No call head: the class name, without the value."""
        return f"{type(self).__name__}(...)"


def _secret_class(word: type[Word]) -> type[Secret]:
    """The class ``Secret[word]``, created once per word class and cached; ``TypeError`` unless
    ``word`` is ``U8``, ``U16``, ``U32`` or ``U64``."""
    if not (isinstance(word, type) and issubclass(word, Word) and word.BITS):
        raise TypeError(f"Secret takes U8, U16, U32 or U64, not {word!r}")
    spec = Secret._classes.get(word)
    if spec is None:
        name = f"Secret[{word.__name__}]"
        base: type[Secret] = _Secret64 if word is U64 else Secret
        spec = type(name, (base,), {"__slots__": (), "WORD": word, "__qualname__": name})
        spec.__module__ = __name__
        Secret._classes[word] = spec
    return spec


class _Secret64(Secret):
    """The base class of ``Secret[U64]``: the methods of ``U64`` beside those of every width."""

    __slots__ = ()

    def wrapping_neg(self) -> Self:
        """Head ``wrapping_neg#64``: ``(2**64 - a) mod 2**64``."""
        w = self._w
        assert isinstance(w, U64)
        return self._of(w.wrapping_neg())

    def mulhi(self, other: Secret | U64 | int) -> Self:
        """Head ``mulhi#64``: ``(a * b) >> 64``."""
        w = self._w
        assert isinstance(w, U64)
        b = self._method_operand(other, "mulhi")
        assert isinstance(b, U64)
        return self._of(w.mulhi(b))


class SecretBool(_SecretBase):
    """A secret Boolean, the result of a comparison of secrets.

    It has no truth value and no equality; ``declassify()`` gives the ``bool``, and ``select``
    takes it as a condition.
    """

    __slots__ = ("_b",)
    _b: bool

    def __new__(cls, b: bool) -> Self:
        """The secret Boolean of ``b``, a ``bool``. No call head."""
        if not isinstance(b, bool):
            raise TypeError(f"SecretBool takes a bool, not {type(b).__name__}")
        x = object.__new__(cls)
        object.__setattr__(x, "_b", b)
        return x

    def __setattr__(self, name: str, value: object) -> NoReturn:
        """Secret Booleans are immutable: ``AttributeError``."""
        raise AttributeError("SecretBool is immutable")

    def __delattr__(self, name: str) -> NoReturn:
        """Secret Booleans are immutable: ``AttributeError``."""
        raise AttributeError("SecretBool is immutable")

    def declassify(self) -> bool:
        """No call head: the public ``bool``."""
        return self._b

    def __bool__(self) -> NoReturn:
        """No call head: a secret Boolean has no truth value; ``TypeError``."""
        raise TypeError("a SecretBool has no truth value; use select or declassify")

    def __eq__(self, other: object) -> NoReturn:
        """No call head: secret Booleans are not compared; ``TypeError``."""
        raise TypeError("a SecretBool is not compared; declassify it first")

    def __ne__(self, other: object) -> NoReturn:
        """No call head: secret Booleans are not compared; ``TypeError``."""
        raise TypeError("a SecretBool is not compared; declassify it first")

    __hash__ = None  # type: ignore[assignment]

    def __repr__(self) -> str:
        """No call head: the class name, without the value."""
        return "SecretBool(...)"


@overload
def select(c: bool, a: _T, b: _T) -> _T: ...


@overload
def select(c: SecretBool, a: Secret | Word, b: Secret | Word) -> Secret: ...


def select(c: bool | SecretBool, a: Any, b: Any) -> Any:
    """Head ``select`` (``selectOp`` of ``withSelect`` in the compiler's ``ImpToNF``): ``a``
    when ``c`` holds, else ``b``.

    ``c`` is a ``bool`` or a ``SecretBool``; ``a`` and ``b`` are of one type (``TypeError``
    otherwise). With a ``SecretBool`` condition, ``a`` and ``b`` are two secrets of one class or
    two public words of one class, and the result is a secret: a public word is returned as
    ``Secret[W]``.
    """
    if type(a) is not type(b):
        raise TypeError(f"select takes two values of one type, not {type(a).__name__} "
                        f"and {type(b).__name__}")
    if isinstance(c, SecretBool):
        chosen = a if c._b else b
        if isinstance(chosen, Secret):
            return chosen
        if isinstance(chosen, Word):
            return _secret_class(type(chosen))._of(chosen)
        raise TypeError("a secret condition selects between secrets or public words")
    if isinstance(c, bool):
        return a if c else b
    raise TypeError(f"the condition of select is a bool or a SecretBool, not {type(c).__name__}")
