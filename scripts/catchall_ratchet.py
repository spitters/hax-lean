#!/usr/bin/env python3
"""Catch-all ratchet of the typed hax adapter.

Lists every arm of HaxLean/HaxAdapter.lean, HaxLean/CertifiedTExprs.lean,
HaxLean/ClassEmit.lean and HaxLean/ContractEmit.lean that falls back on a value
after a `getObjVal?` miss or an unmatched kind, and every default-taking call
(`.getD x`), as rows (file, function, reason) with a count, and compares them with
the shrink-only baseline scripts/catchall-baseline.tsv.

A fallback arm is a match arm `| _ =>`, `| .error _ =>` or `| none =>`, or an
`else`, whose right-hand side is a value: `.wildcard`, `.unknown`, `.unitVal`,
`.unit`, `.lit (.int 0)`, `0`, a name literal, `[]`, `#[]`, `none`, `.null`, `false`,
`""`, or `pure ()` (the node is skipped), possibly under `pure`/`return`. A right-hand
side that throws or returns a refusal message is not a fallback.

Usage:
  catchall-ratchet.sh            check: exit 1 when a row's count exceeds the baseline
  catchall-ratchet.sh --list     print the current rows
  catchall-ratchet.sh --update   rewrite the baseline; refused when a count grows

The script reads files only.
"""
import collections
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FILES = ["HaxLean/HaxAdapter.lean", "HaxLean/CertifiedTExprs.lean",
         "HaxLean/ClassEmit.lean", "HaxLean/ContractEmit.lean"]
BASELINE = os.path.join(ROOT, "scripts", "catchall-baseline.tsv")

TOP_DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|partial|noncomputable|unsafe|meta|public)\s+)*"
    r"(?:def|theorem|lemma|abbrev|instance|structure|inductive)\s+([^\s(:{\[]+)")
WHERE_FN = re.compile(r"^  ([A-Za-z_][\w'?!]*)\s*(?:\(|\{|\[|:)")
MISS_ARM = re.compile(r"\|\s*(?:_|\.error\s+_\w*|none)\s*=>\s*(.*)$")
ELSE_VAL = re.compile(r"^\s*else\s+(.*)$")
GETD = re.compile(r"\.getD\s+(\(\s*[^()]*(?:\([^()]*\)[^()]*)*\)|\S+)")
TOLIST_DEFAULT = re.compile(r"\.toOption\)?\.toList\b")

VALUE = re.compile(
    r"^(?:(?:pure|return)\s+)?\(?\s*(?:"
    r"(?:TExpr\.mk\s+)?\.(?:wildcard|unknown|unitVal|unit)(?:\s+\.\w+)?"
    r"|\.lit\s+\(\.int\s+0\)|\.int\s+0|0|\[\]|#\[\]|none|\.null|false|\(\)"
    r"|\"[^\"]*\""
    r")\s*\)?\s*$")


def strip_comments(lines):
    """The lines with comments and docstrings blanked, line numbers kept."""
    out = []
    depth = 0
    for line in lines:
        res = []
        i = 0
        in_str = False
        while i < len(line):
            if depth > 0:
                if line.startswith("/-", i):
                    depth += 1
                    i += 2
                elif line.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
                continue
            c = line[i]
            if in_str:
                res.append(c)
                if c == "\\" and i + 1 < len(line):
                    res.append(line[i + 1])
                    i += 2
                    continue
                if c == '"':
                    in_str = False
                i += 1
                continue
            if c == '"':
                in_str = True
                res.append(c)
                i += 1
            elif line.startswith("/-", i):
                depth += 1
                i += 2
            elif line.startswith("--", i):
                break
            else:
                res.append(c)
                i += 1
        out.append("".join(res).rstrip())
    return out


def reason_of(rhs):
    rhs = rhs.strip()
    if not rhs or "unsupported" in rhs or rhs.startswith(("throw", ".error", "some")):
        return None
    if VALUE.match(rhs):
        return "fallback " + re.sub(r"\s+", " ", rhs)
    return None


def rows():
    counts = collections.Counter()
    for rel in FILES:
        path = os.path.join(ROOT, rel)
        with open(path, encoding="utf-8") as fh:
            lines = strip_comments(fh.read().split("\n"))
        fn = "<top>"
        top = "<top>"
        in_where = False
        for idx, line in enumerate(lines):
            m = TOP_DECL.match(line)
            if m:
                top = fn = m.group(1)
                in_where = False
            elif line.startswith("where"):
                in_where = True
            elif in_where:
                w = WHERE_FN.match(line)
                if w and w.group(1) not in ("let", "if", "match", "else", "do", "return"):
                    fn = top + "." + w.group(1)
            m = MISS_ARM.search(line)
            rhs = None
            if m:
                rhs = m.group(1)
            else:
                e = ELSE_VAL.match(line)
                if e and not e.group(1).startswith(("if", "match", "do")):
                    rhs = e.group(1)
            if rhs is not None:
                if rhs.strip() == "":
                    rhs = next((l for l in lines[idx + 1:idx + 4] if l.strip()), "")
                r = reason_of(rhs)
                if r:
                    counts[(rel, fn, r)] += 1
            for g in GETD.finditer(line):
                counts[(rel, fn, "getD " + re.sub(r"\s+", " ", g.group(1)))] += 1
            # A failed read turned into an empty list is a default as well.
            for _ in TOLIST_DEFAULT.finditer(line):
                counts[(rel, fn, "getD [] (toOption.toList)")] += 1
    return counts


def read_baseline():
    base = collections.Counter()
    if not os.path.exists(BASELINE):
        return base
    with open(BASELINE, encoding="utf-8") as fh:
        for line in fh:
            if line.startswith("#") or not line.strip():
                continue
            f, fn, r, n = line.rstrip("\n").split("\t")
            base[(f, fn, r)] = int(n)
    return base


def write_baseline(cur):
    with open(BASELINE, "w", encoding="utf-8") as fh:
        fh.write("# file\tfunction\treason\tcount (scripts/catchall-ratchet.sh; shrink only)\n")
        for (f, fn, r), n in sorted(cur.items()):
            fh.write(f"{f}\t{fn}\t{r}\t{n}\n")


def main(argv):
    cur = rows()
    if "--list" in argv:
        for (f, fn, r), n in sorted(cur.items()):
            print(f"{f}\t{fn}\t{r}\t{n}")
        arms = sum(n for (f, fn, r), n in cur.items() if r.startswith("fallback"))
        getd = sum(n for (f, fn, r), n in cur.items() if r.startswith("getD"))
        print(f"# fallback arms {arms}, defaults {getd}")
        return 0
    base = read_baseline()
    grown = [(k, n, base.get(k, 0)) for k, n in cur.items() if n > base.get(k, 0)]
    if "--update" in argv:
        if grown and base:
            for (f, fn, r), n, b in sorted(grown):
                print(f"catchall-ratchet: refused, {f} {fn}: {r} grows {b} -> {n}")
            return 1
        write_baseline(cur)
        print(f"catchall-ratchet: baseline written ({sum(cur.values())} rows counted)")
        return 0
    for (f, fn, r), n, b in sorted(grown):
        print(f"catchall-ratchet: new fallback in {f} {fn}: {r} ({b} -> {n}); "
              "refuse the node instead, or read the field")
    shrunk = [k for k, b in base.items() if cur.get(k, 0) < b]
    if shrunk and not grown:
        print(f"catchall-ratchet: {len(shrunk)} rows shrank; run with --update")
    return 1 if grown else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
