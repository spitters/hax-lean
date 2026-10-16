# Copyright (c) 2026 CatCrypt Contributors. MIT license.
"""Residues modulo a number ``p`` with ``1 < p < 2**64``.

``field(p)`` is the class of the residues ``r`` with ``0 <= r < p``. Its operations are the
tagged methods of the prime-field interface (``FieldTag.fieldCall`` in ``HaxLean/Semantics.lean``):
the head of the method ``m`` is ``m#p<p>`` with the modulus in decimal, for example
``mul#p2013265921``, and its meaning is ``FieldTag.fieldVal``. At a modulus below ``2**64`` an
element is one word, the integer of its residue. The library does not test ``p`` for primality;
``fieldVal`` is defined at every positive modulus.

A second operand is an element of the same class or an ``int`` read as ``F(n)``, which raises
``ValueError`` outside ``[0, p)``. An element of another modulus raises ``TypeError``.
"""

from __future__ import annotations

from typing import ClassVar, NoReturn, Self

__all__ = ["FieldElement", "field"]


class FieldElement:
    """A residue modulo the class constant ``p``; ``field(p)`` is the class of modulus ``p``.

    Instances are immutable: attribute assignment and deletion raise ``AttributeError``.
    """

    __slots__ = ("_r",)
    p: ClassVar[int] = 0
    _r: int

    def __new__(cls, n: int) -> Self:
        """The residue ``n``: an ``int`` (not a ``bool``) with ``0 <= n < p``; ``ValueError``
        otherwise. No call head: a literal of the field."""
        if cls.p == 0:
            raise TypeError("FieldElement is abstract; use field(p)")
        if isinstance(n, bool) or not isinstance(n, int):
            raise ValueError(f"{cls.__name__} takes an int, not {type(n).__name__}")
        if not 0 <= n < cls.p:
            raise ValueError(f"{cls.__name__} takes an int in [0, {cls.p})")
        return cls._of(int(n))

    @classmethod
    def _of(cls, r: int) -> Self:
        """The element of residue ``r``, with ``0 <= r < p`` known to the caller."""
        x = object.__new__(cls)
        object.__setattr__(x, "_r", r)
        return x

    @classmethod
    def head(cls, method: str) -> str:
        """The call head ``<method>#p<p>`` of a method of this field, for example ``add#p17``."""
        return f"{method}#p{cls.p}"

    def __setattr__(self, name: str, value: object) -> NoReturn:
        """Field elements are immutable: ``AttributeError``."""
        raise AttributeError(f"{type(self).__name__} is immutable")

    def __delattr__(self, name: str) -> NoReturn:
        """Field elements are immutable: ``AttributeError``."""
        raise AttributeError(f"{type(self).__name__} is immutable")

    def _operand(self, other: object) -> int | None:
        """The residue of a second operand: an element of this class, or an ``int`` read as
        one; ``TypeError`` for another modulus, ``None`` for any other type."""
        cls = type(self)
        if isinstance(other, FieldElement):
            if type(other) is not cls:
                raise TypeError(f"operands of moduli {cls.p} and {other.p}")
            return other._r
        if isinstance(other, int):
            return cls(other)._r
        return None

    def __add__(self, other: Self | int) -> Self:
        """Head ``add#p<p>``: ``(a + b) mod p``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of((self._r + b) % self.p)

    def __radd__(self, other: int) -> Self:
        """Head ``add#p<p>`` with the ``int`` on the left: ``(n + a) mod p``."""
        return self.__add__(other)

    def __sub__(self, other: Self | int) -> Self:
        """Head ``sub#p<p>``: ``(a + p - b) mod p``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of((self._r + self.p - b) % self.p)

    def __rsub__(self, other: int) -> Self:
        """Head ``sub#p<p>`` with the ``int`` on the left: ``(n + p - a) mod p``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of((b + self.p - self._r) % self.p)

    def __mul__(self, other: Self | int) -> Self:
        """Head ``mul#p<p>``: ``(a * b) mod p``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._of((self._r * b) % self.p)

    def __rmul__(self, other: int) -> Self:
        """Head ``mul#p<p>`` with the ``int`` on the left: ``(n * a) mod p``."""
        return self.__mul__(other)

    def __neg__(self) -> Self:
        """Head ``neg#p<p>``: ``(p - a) mod p``."""
        return self._of((self.p - self._r) % self.p)

    def square(self) -> Self:
        """Head ``square#p<p>``: ``(a * a) mod p``."""
        return self._of((self._r * self._r) % self.p)

    def double(self) -> Self:
        """Head ``double#p<p>``: ``(2 * a) mod p``."""
        return self._of((2 * self._r) % self.p)

    def __eq__(self, other: object) -> bool:
        """Head ``Eq``: equality of the residues, a ``bool``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._r == b

    def __ne__(self, other: object) -> bool:
        """Head ``Ne``: disequality of the residues, a ``bool``."""
        b = self._operand(other)
        if b is None:
            return NotImplemented
        return self._r != b

    def __hash__(self) -> int:
        """No call head: the hash of the residue, so that ``F(n) == n`` implies equal hashes."""
        return hash(self._r)

    def __bool__(self) -> NoReturn:
        """No call head: a field element has no truth value; ``TypeError``."""
        raise TypeError(f"{type(self).__name__} has no truth value; compare it with a value")

    def __int__(self) -> int:
        """No call head: the residue ``r``."""
        return self._r

    def __repr__(self) -> str:
        """No call head: the constructor call, for example ``field(17)(5)``."""
        return f"{type(self).__name__}({self._r})"


_fields: dict[int, type[FieldElement]] = {}


def field(p: int) -> type[FieldElement]:
    """The class of residues modulo ``p``, an ``int`` with ``1 < p < 2**64``; ``ValueError``
    otherwise. The class is created once per modulus and cached, so ``field(p) is field(p)``.
    No call head: the modulus is the tag of the heads ``<method>#p<p>``."""
    if isinstance(p, bool) or not isinstance(p, int):
        raise ValueError(f"field takes an int modulus, not {type(p).__name__}")
    if not 1 < p < (1 << 64):
        raise ValueError("field takes a modulus p with 1 < p < 2**64")
    cls = _fields.get(p)
    if cls is None:
        name = f"field({p})"
        cls = type(name, (FieldElement,), {"__slots__": (), "p": int(p), "__qualname__": name})
        cls.__module__ = __name__
        _fields[p] = cls
    return cls
