#!/usr/bin/env python3
"""Port every Lean file of the repository to Lean's module system.

Each file becomes, as in Mathlib,

    <copyright comment>
    module

    public import A
    public import B

    @[expose] public section

    <module docstring and the rest of the file, unchanged>

`public import` re-exports the imports, and `@[expose] public section` makes
every declaration public with its definition body visible to other files, so
the library behaves as before. Files that already start with `module` are left
alone, so the script can be run again safely.

Usage, from the repository root:  python3 scripts/palomar_port.py
"""
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
IMPORT = re.compile(r"^import\s+(.+?)\s*$")
PORTED = re.compile(r"^(module|public import\s+.+|@\[expose\] public section)\s*$")


def header_end(lines):
    """Index just past the leading comments, blank lines and imports."""
    i, in_comment = 0, False
    while i < len(lines):
        s = lines[i].strip()
        if in_comment:
            if "-/" in s:
                in_comment = False
            i += 1
        elif s.startswith("/-") and not s.startswith("/-!"):   # copyright comment
            in_comment = "-/" not in s[2:]
            i += 1
        elif s == "" or s.startswith("--") or IMPORT.match(lines[i]) or PORTED.match(s):
            i += 1
        else:
            break
    return i


def port(text):
    lines = text.split("\n")
    end = header_end(lines)
    if any(l.strip() == "module" for l in lines[:end]):
        return None                                   # already ported
    imports = [i for i in range(end) if IMPORT.match(lines[i])]
    out = list(lines)
    if imports:
        for i in imports:                             # import A B -> public import A B
            out[i] = "public import " + IMPORT.match(lines[i]).group(1)
        last = imports[-1]
        out[last + 1:last + 1] = ["", "@[expose] public section"]
        out[imports[0]:imports[0]] = ["module", ""]
    else:                                             # no imports: header at the top
        first = end if end < len(lines) else 0
        out[first:first] = ["module", "", "@[expose] public section", ""]
    return "\n".join(out)


def main():
    files = subprocess.run(["git", "ls-files", "*.lean"], cwd=ROOT, capture_output=True,
                           text=True, check=True).stdout.split()
    changed = skipped = 0
    for f in files:
        p = ROOT / f
        new = port(p.read_text(encoding="utf-8"))
        if new is None:
            skipped += 1
            continue
        p.write_text(new, encoding="utf-8")
        changed += 1
    long = [f for f in files if len((ROOT / f).read_text(encoding="utf-8").split("\n")) > 10000]
    print(f"Ported {changed} files; {skipped} already used the module system.")
    print("Files over 10,000 lines:", ", ".join(long) if long else "none")
    return 0


if __name__ == "__main__":
    sys.exit(main())
