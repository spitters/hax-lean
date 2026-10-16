# Copyright (c) 2026 CatCrypt Contributors. MIT license.
"""The dumper ``py2json``: schema keys, positions, integer exactness, version refusal."""

import ast
import contextlib
import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
from typing import Any
from unittest import mock

import py2json

HERE = os.path.dirname(os.path.abspath(__file__))
DUMPER = os.path.join(os.path.dirname(HERE), "py2json.py")

BIG = 2**200 + 12345
SOURCE = f"""\
from typing import Final

N: Final = 4
BIG = {BIG}
HEX = 0x{(1 << 300) - 1:x}


def f(a: int, k: int = 1) -> int:
    x = a + k * 2
    if not x < 3 and True:
        x = -x
    return x if x else None


z = (1.5, 2j, b"ab", ..., "é")
"""


def run_cli(args: list[str]) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run([sys.executable, "-I", DUMPER, *args], capture_output=True,
                          check=False)


class SchemaTest(unittest.TestCase):
    def setUp(self) -> None:
        self.obj = py2json.dump_source(SOURCE, "prog.py")

    def test_top_level(self) -> None:
        self.assertEqual(list(self.obj), ["python", "file", "module"])
        self.assertEqual(self.obj["python"], list(sys.version_info[:3]))
        self.assertEqual(self.obj["file"], "prog.py")
        mod = self.obj["module"]
        self.assertEqual(list(mod), ["_type", "body", "type_ignores"])
        self.assertEqual(mod["_type"], "Module")

    def test_fields_in_order_then_positions(self) -> None:
        def check(d: Any) -> None:
            if isinstance(d, list):
                for x in d:
                    check(x)
            elif isinstance(d, dict) and "_type" in d:
                cls = getattr(ast, d["_type"])
                keys = list(d)
                self.assertEqual(keys[0], "_type")
                fields = list(cls._fields)
                self.assertEqual(keys[1:1 + len(fields)], fields)
                positions = [a for a in py2json.POSITIONS if a in cls._attributes]
                self.assertEqual(keys[1 + len(fields):], positions)
                for k in fields:
                    check(d[k])
        check(self.obj["module"])

    def test_operators_and_contexts(self) -> None:
        text = json.dumps(self.obj)
        self.assertIn('{"_type": "Add"}', text)
        self.assertIn('{"_type": "Mult"}', text)
        self.assertIn('{"_type": "Load"}', text)
        self.assertIn('{"_type": "Store"}', text)
        self.assertIn('{"_type": "USub"}', text)
        self.assertIn('{"_type": "Not"}', text)
        self.assertIn('{"_type": "And"}', text)
        self.assertIn('{"_type": "Lt"}', text)

    def test_positions(self) -> None:
        body = self.obj["module"]["body"]
        ann = body[1]
        self.assertEqual(ann["_type"], "AnnAssign")
        self.assertEqual((ann["lineno"], ann["col_offset"], ann["end_lineno"],
                          ann["end_col_offset"]), (3, 0, 3, 12))
        target = ann["target"]
        self.assertEqual(target, {"_type": "Name", "id": "N", "ctx": {"_type": "Store"},
                                  "lineno": 3, "col_offset": 0, "end_lineno": 3,
                                  "end_col_offset": 1})
        fn = body[4]
        self.assertEqual(fn["_type"], "FunctionDef")
        self.assertEqual(fn["lineno"], 8)
        arg = fn["args"]["args"][0]
        self.assertEqual((arg["_type"], arg["arg"], arg["lineno"], arg["col_offset"]),
                         ("arg", "a", 8, 6))
        self.assertNotIn("lineno", fn["args"])
        self.assertEqual(fn["args"]["_type"], "arguments")

    def test_constants(self) -> None:
        body = self.obj["module"]["body"]
        big = body[2]["value"]
        self.assertEqual(big["_type"], "Constant")
        self.assertIs(type(big["value"]), int)
        self.assertEqual(big["value"], BIG)
        self.assertIsNone(big["kind"])
        hexv = body[3]["value"]["value"]
        self.assertEqual(hexv, (1 << 300) - 1)
        elts = body[5]["value"]["elts"]
        self.assertEqual([e["value"] for e in elts], [
            {"_const": "float", "repr": "1.5"},
            {"_const": "complex", "repr": "2j"},
            {"_const": "bytes", "repr": "b'ab'"},
            {"_const": "ellipsis", "repr": "Ellipsis"},
            "é",
        ])
        consts = []

        def walk(d: Any) -> None:
            if isinstance(d, list):
                for x in d:
                    walk(x)
            elif isinstance(d, dict):
                if d.get("_type") == "Constant":
                    consts.append(d["value"])
                for v in d.values():
                    walk(v)
        walk(self.obj["module"])
        self.assertIn(True, consts)
        self.assertIn(None, consts)
        self.assertTrue(any(c is True for c in consts))

    def test_bool_before_int(self) -> None:
        self.assertIs(py2json.value_json(True), True)
        self.assertIs(py2json.value_json(False), False)
        self.assertEqual(py2json.value_json(1), 1)
        self.assertIs(type(py2json.value_json(1)), int)


class CliTest(unittest.TestCase):
    def test_output_file_and_stdout(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            src = os.path.join(d, "prog.py")
            out = os.path.join(d, "prog.json")
            with open(src, "w", encoding="utf-8") as f:
                f.write(SOURCE)
            r = run_cli([src, "-o", out])
            self.assertEqual(r.returncode, 0, r.stderr)
            with open(out, "rb") as f:
                data = f.read()
            r2 = run_cli([src])
            self.assertEqual(r2.returncode, 0, r2.stderr)
            self.assertEqual(r2.stdout, data)
            # Compact, deterministic, UTF-8, exact integers.
            text = data.decode("utf-8")
            self.assertNotIn(", ", text.replace('", "', ""))
            self.assertNotIn("\n", text)
            self.assertIn(str(BIG), text)
            self.assertIn(str((1 << 300) - 1), text)
            self.assertIn("é", text)
            self.assertEqual(run_cli([src]).stdout, data)
            obj = json.loads(text)
            self.assertEqual(obj["file"], src)
            self.assertEqual(obj, py2json.dump_source(SOURCE, src))
            self.assertEqual(text, json.dumps(obj, ensure_ascii=False, separators=(",", ":")))

    def test_long_decimal_literal(self) -> None:
        digits = "7" * 5000
        with tempfile.TemporaryDirectory() as d:
            src = os.path.join(d, "big.py")
            with open(src, "w", encoding="utf-8") as f:
                f.write(f"X = {digits}\n")
            r = run_cli([src])
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertIn(digits.encode(), r.stdout)

    def test_errors(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            src = os.path.join(d, "bad.py")
            with open(src, "w", encoding="utf-8") as f:
                f.write("def f(:\n")
            r = run_cli([src])
            self.assertEqual(r.returncode, 1)
            self.assertIn(b"SyntaxError", r.stderr)
            r = run_cli([os.path.join(d, "missing.py")])
            self.assertEqual(r.returncode, 1)

    def test_version_refusal(self) -> None:
        err = io.StringIO()
        with mock.patch.object(sys, "version_info", (3, 11, 9, "final", 0)), \
                contextlib.redirect_stderr(err):
            status = py2json.main(["unused.py"])
        self.assertEqual(status, 2)
        self.assertIn("3.12", err.getvalue())

    def test_version_refusal_subprocess(self) -> None:
        code = ("import sys, runpy; sys.version_info = (3, 13, 0, 'final', 0); "
                f"sys.argv = [{DUMPER!r}, 'unused.py']; runpy.run_path({DUMPER!r}, "
                "run_name='__main__')")
        r = subprocess.run([sys.executable, "-I", "-c", code], capture_output=True, check=False)
        self.assertEqual(r.returncode, 2)
        self.assertIn(b"Python 3.12 is required", r.stderr)


if __name__ == "__main__":
    unittest.main()
