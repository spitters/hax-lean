# Copyright (c) 2026 CatCrypt Contributors. MIT license.
"""Write the CPython parse tree of a Python source file as JSON.

Usage: ``python3 -I py2json.py SRC.py [-o OUT.json]``.

The dumper runs only under Python 3.12 (exit status 2 otherwise), since the node classes of
``ast`` change between versions. It parses ``SRC`` with ``ast.parse(source, filename=SRC)`` and
writes, compact and with keys in a fixed order, the object

    {"python": [major, minor, micro], "file": SRC, "module": NODE}

A node (any ``ast.AST``) is an object whose first key is ``"_type"``, the class name; then each
name of ``type(node)._fields``, in order, with its value; then each of ``lineno``,
``col_offset``, ``end_lineno``, ``end_col_offset`` that the node has. Operators and expression
contexts are nodes with no fields, for example ``{"_type": "Add"}``. A value is a node; a list
is an array; ``None`` is ``null``; a ``bool`` is ``true`` or ``false``; an ``int`` is a JSON
integer with all its digits; a ``str`` is a string; any other constant (``float``, ``complex``,
``bytes``, ``Ellipsis``) is ``{"_const": "<type name>", "repr": "<repr>"}``.

The output is UTF-8 without escapes of non-ASCII characters and without a final newline. Exit
status 1 for a file that cannot be read or parsed.
"""

from __future__ import annotations

import argparse
import ast
import json
import sys
from typing import Any

__all__ = ["POSITIONS", "dump_source", "main", "node_json", "value_json"]

POSITIONS = ("lineno", "col_offset", "end_lineno", "end_col_offset")
"""The position attributes, in the order the dumper writes them."""


def value_json(v: object) -> Any:
    """The JSON value of a field value: a node, a list, ``None``, a ``bool``, an ``int``, a
    ``str``, or any other constant as ``{"_const": type name, "repr": repr}``."""
    if isinstance(v, ast.AST):
        return node_json(v)
    if isinstance(v, list):
        return [value_json(x) for x in v]
    if v is None:
        return None
    if isinstance(v, bool):
        return v
    if isinstance(v, int):
        return int(v)
    if isinstance(v, str):
        return v
    return {"_const": type(v).__name__, "repr": repr(v)}


def node_json(node: ast.AST) -> dict[str, Any]:
    """The JSON object of a node: ``"_type"``, the fields in order, then the positions."""
    out: dict[str, Any] = {"_type": type(node).__name__}
    for name in node._fields:
        out[name] = value_json(getattr(node, name))
    attributes = type(node)._attributes
    for name in POSITIONS:
        if name in attributes and hasattr(node, name):
            out[name] = value_json(getattr(node, name))
    return out


def dump_source(source: str | bytes, filename: str) -> dict[str, Any]:
    """The output object of the source text ``source`` read from the file ``filename``."""
    tree = ast.parse(source, filename=filename)
    major, minor, micro = sys.version_info[:3]
    return {"python": [major, minor, micro], "file": filename, "module": node_json(tree)}


def main(argv: list[str] | None = None) -> int:
    """Run the dumper on the command line ``argv``; the exit status."""
    if tuple(sys.version_info[:2]) != (3, 12):
        v = ".".join(str(x) for x in sys.version_info[:3])
        print(f"py2json: Python 3.12 is required, this is Python {v}", file=sys.stderr)
        return 2
    parser = argparse.ArgumentParser(prog="py2json", description="Write the CPython parse tree "
                                     "of a Python source file as JSON.")
    parser.add_argument("src", metavar="SRC.py", help="the Python source file")
    parser.add_argument("-o", dest="out", metavar="OUT.json", help="the output file "
                        "(standard output when absent)")
    args = parser.parse_args(argv)
    # Integer literals and their decimal text have no length bound.
    sys.set_int_max_str_digits(0)
    try:
        with open(args.src, "rb") as f:
            source = f.read()
    except OSError as e:
        print(f"py2json: {args.src}: {e.strerror}", file=sys.stderr)
        return 1
    try:
        obj = dump_source(source, args.src)
    except (SyntaxError, ValueError) as e:
        print(f"py2json: {args.src}: {type(e).__name__}: {e}", file=sys.stderr)
        return 1
    text = json.dumps(obj, ensure_ascii=False, separators=(",", ":"), allow_nan=False)
    try:
        data = text.encode("utf-8")
    except UnicodeEncodeError:
        print(f"py2json: {args.src}: a string contains a lone surrogate", file=sys.stderr)
        return 1
    if args.out is None:
        sys.stdout.buffer.write(data)
        sys.stdout.buffer.flush()
    else:
        with open(args.out, "wb") as f:
            f.write(data)
    return 0


if __name__ == "__main__":
    sys.exit(main())
