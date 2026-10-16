# Copyright (c) 2026 CatCrypt Contributors. MIT license.
"""The decorators ``entry`` and ``linked``.

``@entry`` marks a function the front compiles as an entry; a module may have several, each
compiled with the module's other functions as callees. ``@linked`` marks a
kernel that the compiled code calls as linked code (a ``LinkedFn``); its Python body is a
reference only, run by CPython and not translated.
"""

from __future__ import annotations

from collections.abc import Callable
from typing import Any, TypeVar, overload

__all__ = ["entry", "linked"]

_F = TypeVar("_F", bound=Callable[..., Any])


def entry(fn: _F) -> _F:
    """Mark ``fn`` as the compiled entry: set ``fn.__catcrypt_entry__ = True`` and return
    ``fn`` unchanged. No call head."""
    fn.__catcrypt_entry__ = True  # type: ignore[attr-defined]
    return fn


@overload
def linked(fn: _F, /) -> _F: ...


@overload
def linked(*, name: str | None = None) -> Callable[[_F], _F]: ...


def linked(fn: _F | None = None, /, *, name: str | None = None) -> _F | Callable[[_F], _F]:
    """Mark a function as a linked kernel, written ``@linked`` or ``@linked(name="...")``.

    Sets ``fn.__catcrypt_linked__`` to ``name``, or to ``fn.__name__`` when no name is given, and
    returns ``fn`` unchanged. The compiled code calls the kernel of that name; the Python body
    is a reference. No call head: each call is a call of a ``LinkedFn``.
    """

    def mark(f: _F) -> _F:
        if name is not None and (not isinstance(name, str) or not name):
            raise TypeError("the name of a linked kernel is a non-empty str")
        f.__catcrypt_linked__ = name if name is not None else f.__name__  # type: ignore[attr-defined]
        return f

    if fn is not None:
        return mark(fn)
    return mark
