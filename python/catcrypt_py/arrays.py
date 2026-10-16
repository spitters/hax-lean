# Copyright (c) 2026 CatCrypt Contributors. MIT license.
"""Arrays of fixed length, Rust ``[W; N]``.

``Array[W, N]`` is the class of arrays of ``N`` elements of the class ``W``: a word class
(``U8`` ... ``U64``), a secret word class ``Secret[W]`` or a field class ``field(p)``. ``N`` is an
``int``; in a program it is a literal or a module constant ``N: Final = 4``. An array is backed
by a tuple and is immutable: ``set`` returns a new array, and ``a[i] = v`` raises ``TypeError``.

An index is an ``int`` or a public word; an index outside ``[0, N)``, negative indices included,
raises ``IndexError`` (the heads ``index`` and ``array_update`` of ``widthArrayOps`` in
``HaxLean/Semantics.lean`` have no value there). A secret index raises ``TypeError``.

``len(a)`` and iteration are defined for tests and drivers; the checker refuses both in a
compiled program.
"""

from __future__ import annotations

from collections.abc import Iterable, Iterator
from typing import Any, ClassVar, NoReturn, Self

from .field import FieldElement
from .secret import Secret
from .words import Word, _SecretBase

__all__ = ["Array"]


def _element_class(w: object) -> bool:
    """Whether ``w`` is an element class of an array: a word, secret word or field class."""
    if not isinstance(w, type):
        return False
    if issubclass(w, Word):
        return w.BITS != 0
    if issubclass(w, Secret):
        return hasattr(w, "WORD")
    if issubclass(w, FieldElement):
        return w.p != 0
    return False


def _index(i: object, n: int) -> int:
    """The position of a public index ``i`` in an array of length ``n``.

    ``TypeError`` for a secret, a ``bool`` or a non-integer; ``IndexError`` outside ``[0, n)``.
    """
    if isinstance(i, _SecretBase):
        raise TypeError("an array index is public; declassify it first")
    if isinstance(i, Word):
        k = int(i)
    elif isinstance(i, bool) or not isinstance(i, int):
        raise TypeError(f"an array index is an int or a word, not {type(i).__name__}")
    else:
        k = int(i)
    if not 0 <= k < n:
        raise IndexError(f"index out of range [0, {n})")
    return k


class Array:
    """An array of fixed length; ``Array[W, N]`` is the class of length ``N`` over ``W``."""

    __slots__ = ("_items",)
    ELEMENT: ClassVar[type]
    LENGTH: ClassVar[int]
    _items: tuple[Any, ...]
    _classes: ClassVar[dict[tuple[type, int], type[Array]]] = {}

    def __class_getitem__(cls, params: tuple[type, int]) -> type[Array]:
        """The class ``Array[W, N]``, created once per pair ``(W, N)`` and cached.

        ``TypeError`` unless ``W`` is an element class and ``N`` an ``int`` (not a ``bool``);
        ``ValueError`` for a negative ``N``.
        """
        if cls is not Array:
            raise TypeError(f"{cls.__name__} is already specialised")
        if not (isinstance(params, tuple) and len(params) == 2):
            raise TypeError("Array takes two parameters: Array[W, N]")
        w, n = params
        if not _element_class(w):
            raise TypeError(f"the element class of Array is a word, secret word or field "
                            f"class, not {w!r}")
        if isinstance(n, bool) or not isinstance(n, int):
            raise TypeError(f"the length of Array is an int, not {type(n).__name__}")
        if n < 0:
            raise ValueError("the length of Array is non-negative")
        key = (w, int(n))
        spec = Array._classes.get(key)
        if spec is None:
            name = f"Array[{w.__name__}, {n}]"
            spec = type(name, (Array,), {"__slots__": (), "ELEMENT": w, "LENGTH": int(n),
                                         "__qualname__": name})
            spec.__module__ = __name__
            Array._classes[key] = spec
        return spec

    def __new__(cls, values: Iterable[Any]) -> Self:
        """The array of the elements of ``values``: exactly ``N`` elements (``ValueError``
        otherwise), each of class ``W`` (``TypeError`` otherwise). No call head: an array
        literal, head ``array_lit``."""
        if not hasattr(cls, "ELEMENT"):
            raise TypeError("use Array[W, N] for an element class W and a length N")
        items = tuple(values)
        if len(items) != cls.LENGTH:
            raise ValueError(f"{cls.__name__} takes {cls.LENGTH} elements, not {len(items)}")
        for x in items:
            if type(x) is not cls.ELEMENT:
                raise TypeError(f"{cls.__name__} takes elements of class "
                                f"{cls.ELEMENT.__name__}, not {type(x).__name__}")
        return cls._of(items)

    @classmethod
    def _of(cls, items: tuple[Any, ...]) -> Self:
        """The array of the tuple ``items``, checked by the caller."""
        x = object.__new__(cls)
        object.__setattr__(x, "_items", items)
        return x

    @classmethod
    def filled(cls, v: Any) -> Self:
        """The array of ``N`` copies of ``v``, of class ``W``; for tests. Head ``repeat``."""
        return cls((v,) * cls.LENGTH)

    def __getitem__(self, i: Word | int) -> Any:
        """Head ``index``: the element at position ``i``; ``IndexError`` unless
        ``0 <= i < N``, ``TypeError`` for a secret index."""
        return self._items[_index(i, self.LENGTH)]

    def set(self, i: Word | int, v: Any) -> Self:
        """Head ``array_update``: the array with the element at position ``i`` replaced by
        ``v``; ``IndexError`` unless ``0 <= i < N``, ``TypeError`` for a secret index or for
        ``v`` not of class ``W``. The array itself is unchanged."""
        k = _index(i, self.LENGTH)
        if type(v) is not self.ELEMENT:
            raise TypeError(f"{type(self).__name__}.set takes an element of class "
                            f"{self.ELEMENT.__name__}, not {type(v).__name__}")
        return self._of(self._items[:k] + (v,) + self._items[k + 1:])

    def __setitem__(self, i: object, v: object) -> NoReturn:
        """Arrays are immutable: ``TypeError``; write ``a = a.set(i, v)``."""
        raise TypeError("Array is immutable; write a = a.set(i, v)")

    def __delitem__(self, i: object) -> NoReturn:
        """Arrays are immutable: ``TypeError``."""
        raise TypeError("Array is immutable")

    def __setattr__(self, name: str, value: object) -> NoReturn:
        """Arrays are immutable: ``AttributeError``."""
        raise AttributeError(f"{type(self).__name__} is immutable")

    def __delattr__(self, name: str) -> NoReturn:
        """Arrays are immutable: ``AttributeError``."""
        raise AttributeError(f"{type(self).__name__} is immutable")

    def __eq__(self, other: object) -> bool:
        """Head ``Eq``: element-wise equality, a ``bool``; ``TypeError`` for an array of
        another class. Arrays of secrets are not compared (``TypeError``)."""
        if not isinstance(other, Array):
            return NotImplemented
        if type(other) is not type(self):
            raise TypeError(f"operands {type(self).__name__} and {type(other).__name__}")
        return self._items == other._items

    def __ne__(self, other: object) -> bool:
        """Head ``Ne``: the negation of ``==``, a ``bool``."""
        eq = self.__eq__(other)
        if eq is NotImplemented:
            return NotImplemented
        return not eq

    def __hash__(self) -> int:
        """No call head: the hash of the class and the elements."""
        return hash((type(self), self._items))

    def __len__(self) -> int:
        """No call head: ``N``. Refused by the checker in a compiled program."""
        return len(self._items)

    def __iter__(self) -> Iterator[Any]:
        """No call head: the elements in order. Refused by the checker in a compiled
        program, where a loop is ``for i in range(N)``."""
        return iter(self._items)

    def __bool__(self) -> NoReturn:
        """No call head: an array has no truth value; ``TypeError``."""
        raise TypeError(f"{type(self).__name__} has no truth value")

    def __repr__(self) -> str:
        """No call head: the constructor call, for example ``Array[U64, 2]([U64(1), U64(2)])``."""
        return f"{type(self).__name__}({list(self._items)!r})"
