# Python front

A module written in a typed subset of Python 3.12 is translated to
[`TExpr`](../HaxLean/TExpr.lean), the typed imperative AST that hax extractions produce, and
from there through the same typed pipeline and printer as a hax export. CPython runs the same
module with the library [`catcrypt_py`](catcrypt_py/), whose operations mean what the call
table of the CatCrypt compiler means.

The stages:

1. [`py2json.py`](py2json.py) writes CPython's parse tree as JSON, node by node with source
   positions.
2. [`PyModule.fromJson?`](../HaxLean/Py/Json.lean) reads the nodes of the fragment into a
   [`PyModule`](../HaxLean/Py/AST.lean).
3. [`pyCheck`](../HaxLean/Py/Check.lean) type-checks the module and refuses any construct
   outside the fragment, with its kind and source position.
4. [`pyToTExpr`](../HaxLean/Py/ToTExpr.lean) translates each function to an imperative
   [`TExpr`](../HaxLean/TExpr.lean).
5. [`postPipeline`](../HaxLean/CertifiedTExprs.lean), the passes of `haxpipeT --hax`, and
   [`pyExtractionModule`](../HaxLean/Py/Emit.lean) print the extraction module.

```
python3 -I python/py2json.py prog.py -o prog.json
lake exe haxpipeT --python prog.json --name Prog -o Prog.lean
```

## Syntax

```python
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
```

Every value is immutable, so two names that share an object in CPython cannot observe each
other's updates; an array is updated by `x = x.set(i, v)`, which is the term hax produces for
Rust `x[i] = v`.

## The fragment

Types: `bool`; `int` for literals, loop indices and index arithmetic; the words `U8`, `U16`,
`U32`, `U64`; `Array[T, N]` with `N` a constant or a literal; a prime field `F = field(p)`
with `1 < p < 2^64`; `Secret[W]` over a word.

Module level: a module begins with a docstring, followed by `from typing import Final`,
imports from `catcrypt_py`, constants `N: Final = <int>`, field classes `F = field(<int>)`,
and function definitions, each parameter and result annotated. `@entry` marks a function the
compiler takes as an entry: at most six parameters, each a word, a field element, a secret
word or an array of these; the result a word, a field element or an array, and an entry with
six parameters returns an array only if one of its array parameters has the same length (the
layout writes an array result into an array parameter of its length or, with fewer than six
parameters, into an extra output parameter). `@linked` marks a
kernel called as linked code, whose Python body is a reference only.

Statements: a first binding `x = e` or `x: T = e` at the top level of a function body or of a
loop body; a rebinding at the same type; `x = x.set(i, v)`; `for i in range(lo, hi)` and
`for i in reversed(range(lo, hi))`; `if c:`/`else:` with `c` a `bool`, whose arms rebind
names bound before; `pass`; one `return e` as the last statement.

Expressions and the call heads they become:

| Python | Head |
|---|---|
| `a + b`, `a - b`, `a * b` on `Uw` (an overflow raises) | `Add#w`, `Sub#w`, `Mul#w` |
| `a.wrapping_add(b)`, `wrapping_sub`, `wrapping_mul`; `U64`: `wrapping_neg()`, `mulhi(b)` | `wrapping_add#w`, ..., `wrapping_neg#64`, `mulhi#64` |
| `a & b`, `a \| b`, `a ^ b`, `~a` | `BitAnd#w`, `BitOr#w`, `BitXor#w`, `Not#w` |
| `a << k`, `a >> k` (an amount of at least `w` raises) | `Shl#w`, `Shr#w` |
| `a.rotate_left(k)`, `a.rotate_right(k)`, `a.cast(U32)` | `rotate_left#w`, `rotate_right#w`, `cast#32` |
| `==`, `!=`, `<`, `<=`, `>`, `>=` | `Eq`, `Ne`, `Lt`, `Le`, `Gt`, `Ge` |
| `not c`; `c and d`, `c or d` | `Not`; `&&`, `\|\|`, or a conditional when `d` can fail |
| `a if c else b`, `select(c, a, b)` | `ifThenElse` |
| `a[i]`, `x.set(i, v)` | `index`, `array_update` |
| field `+`, `-`, `*`, unary `-`, `.square()`, `.double()` | `add#p<p>`, `sub#p<p>`, `mul#p<p>`, `neg#p<p>`, `square#p<p>`, `double#p<p>` |
| `i + 1`, `2 * i` on `int` (index arithmetic) | `Add#size`, `Mul#size` |
| `g(args)` for a function defined earlier, or a linked function | a call of `g` |

An `int` expression other than a literal occurs only as an index, a loop bound, the argument
of a word constructor or an operand of a comparison. The call table computes its arithmetic
as checked 64-bit arithmetic (`Add#size`, `Mul#size`), which agrees with CPython's exact
arithmetic on values in `[0, 2^64)`. A secret is never a condition, an index, a loop bound
or a shift amount; its comparisons give a secret bit, which only `select` consumes, and
`declassify()` is its only escape. The checker also refuses tuples, `int` literals of at
least `2^64`, callee arrays of words narrower than 64 bits, call chains deeper than four, and
functions named after a call head or an array operation.

## What is proved

| Statement | Lean |
|---|---|
| Reading the JSON written for a module gives back the module. | [`PyModule.fromJson_toJson`](../HaxLean/Py/Json.lean) |
| Every module the checker accepts satisfies the declarative typing rules of the fragment. | [`pyCheck_wellTyped`](../HaxLean/Py/CheckSound.lean); rules [`HasTy`](../HaxLean/Py/Types.lean), [`StmtsOk`](../HaxLean/Py/Types.lean) |
| Every translated function is built from literals, names, `let`, assignment, sequence, calls, counted loops and conditionals only: no match, closure, reference, early exit, `while` loop or fold. | [`pyToTExpr_pyImage`](../HaxLean/Py/ToTExpr.lean); predicate [`PyImage`](../HaxLean/Py/ToTExpr.lean) |
| Every translated function satisfies the hypotheses on the term of the pipeline's semantic preservation theorem [`pipeline_full_correct`](../HaxLean/PipelineCF.lean): its loops scope their breaks, it has no `?` and no control-flow constructor. | [`pyToTExpr_loopScoped`](../HaxLean/Py/ToTExprProps.lean), [`pyToTExpr_noQuestionMark`](../HaxLean/Py/ToTExprProps.lean), [`pyToTExpr_noCFConstructors`](../HaxLean/Py/ToTExprProps.lean) |
| The secrecy record of a function marks a parameter or the result secret exactly when its checked type holds a secret. | [`pyFnSecrecy_param`](../HaxLean/Py/Secrecy.lean) |
| The secret bindings of a function are exactly its parameters and bindings of a secret type, loop bodies included, and the walk that collects them leaves the context the checker leaves. | [`mem_pySecretBindings_iff`](../HaxLean/Py/Secrecy.lean), [`walkStmts_fst`](../HaxLean/Py/Secrecy.lean) |

## Files

- [`catcrypt_py/`](catcrypt_py/): the runtime library (`words.py`, `arrays.py`, `field.py`,
  `secret.py`, `decorators.py`); each operation's docstring names its call head.
- [`py2json.py`](py2json.py): the dump of CPython's parse tree.
- [`examples/`](examples/), [`tests/`](tests/): `python3 -I -m unittest discover -s tests -t .`
  from this directory.
- [`../HaxLean/Py/`](../HaxLean/Py/): the reader ([`AST.lean`](../HaxLean/Py/AST.lean),
  [`Json.lean`](../HaxLean/Py/Json.lean)), the checker
  ([`Types.lean`](../HaxLean/Py/Types.lean), [`Check.lean`](../HaxLean/Py/Check.lean),
  [`CheckSound.lean`](../HaxLean/Py/CheckSound.lean)), the translation
  ([`ToTExpr.lean`](../HaxLean/Py/ToTExpr.lean),
  [`ToTExprProps.lean`](../HaxLean/Py/ToTExprProps.lean)), the secrecy records
  ([`Secrecy.lean`](../HaxLean/Py/Secrecy.lean)) and the printer of the extraction module
  ([`Emit.lean`](../HaxLean/Py/Emit.lean)).
