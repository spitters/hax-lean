# Copyright (c) 2026 CatCrypt Contributors. MIT license.
"""The runtime library of the CatCrypt Python front.

A program of the typed Python subset imports its types and operations from this package. Each
operator and method computes the value of one call head of the compiler's table
(``hax64WordOps`` and the tables it falls through to, in ``HaxLean/Semantics.lean``), and its
docstring names that head. Where the head has no value, the operation raises an exception
(``OverflowError``, ``IndexError``, ``ValueError`` or ``TypeError``); the front reads every
exception as the one error outcome. Every value is immutable, so aliasing is not observable.

* ``U8``, ``U16``, ``U32``, ``U64``: unsigned words (module ``words``).
* ``Array[W, N]``: arrays of fixed length (module ``arrays``).
* ``field(p)``: residues modulo ``p < 2**64`` (module ``field``).
* ``Secret[W]``, ``SecretBool``, ``select``: secret words (module ``secret``).
* ``entry``, ``linked``: decorators (module ``decorators``).

Module constants are written with ``typing.Final``::

    from typing import Final

    N: Final = 4

The checker reads such a constant as its literal, so that ``Array[U64, N]`` is the type
``[u64; 4]`` and ``range(N)`` a loop with a constant count.
"""

from .arrays import Array
from .decorators import entry, linked
from .field import FieldElement, field
from .secret import Secret, SecretBool, select
from .words import U8, U16, U32, U64, Word

__all__ = [
    "Array",
    "FieldElement",
    "Secret",
    "SecretBool",
    "U8",
    "U16",
    "U32",
    "U64",
    "Word",
    "entry",
    "field",
    "linked",
    "select",
]
