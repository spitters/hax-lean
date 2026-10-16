# Copyright (c) 2026 CatCrypt Contributors. MIT license.
"""The Python counterpart of ``bind_loop`` in ``constructs-hax/src/lib.rs``: bindings, then a
loop with a constant count over a carried array."""

from typing import Final

from catcrypt_py import U64, Array, entry

N: Final = 4


@entry
def bind_loop(a: Array[U64, N], k: U64) -> Array[U64, N]:
    m = k ^ 0x5555_5555_5555_5555
    s = m.wrapping_add(k)
    r = a
    for i in range(N):
        r = r.set(i, r[i] ^ s)
    return r
