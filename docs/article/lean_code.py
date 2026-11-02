#!/usr/bin/env python3
"""Extract the Lean code of every declaration cited in the article.

Reads docs/article/plaplacian-article.tex, collects the Lean names cited with
\\leanref{...}, determines where each is cited (Main Theorem, Theorem 6.1, ...),
and copies the exact source of each declaration from Plaplacian/*.lean, followed
by the definitions those statements are built on. The result is written to
docs/article/lean-code.txt.

Usage, from the repository root:  python3 docs/article/lean_code.py
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
ARTICLE = ROOT / "docs" / "article" / "plaplacian-article.tex"
OUT = ROOT / "docs" / "article" / "lean-code.txt"

sys.path.insert(0, str(ROOT / "docs" / "blueprint" / "site"))
import build  # noqa: E402  (reuses the blueprint's Lean indexer)

AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# the definitions the cited statements are built on
SUPPORT = ["BddMeas", "tugOfWarOp", "dppOp", "bdryStrip", "IsPHarmonious",
           "IsViscositySubsolution", "IsViscositySupersolution", "ubar", "lbar"]
ENVS = ("theorem", "proposition", "lemma", "definition", "remark")


def cited_names(tex):
    """Each cited Lean name with the place it is cited, in order of appearance.

    Numbering follows amsart with \\newtheorem{theorem}{Theorem}[section] and the
    other environments sharing its counter, as in the article."""
    # only the document body, without comments
    tex = tex[tex.index("\\begin{document}"):]
    tex = "\n".join(re.sub(r"(?<!\\)%.*", "", line) for line in tex.splitlines())
    pattern = re.compile(
        r"\\section\*?\{|\\begin\{(" + "|".join(ENVS) + r"|maintheorem)\}"
        r"|\\end\{(" + "|".join(ENVS) + r"|maintheorem)\}"
        r"|\\leanref\{([^}]*)\}")
    section, counter, current = 0, 0, "the introduction"
    seen = {}
    for m in pattern.finditer(tex):
        tok = m.group(0)
        if tok.startswith("\\section"):
            if not tok.startswith("\\section*"):
                section += 1
                counter = 0
            current = f"Section {section}" if not tok.startswith("\\section*") else current
        elif m.group(1) == "maintheorem":
            current = "the Main Theorem"
        elif m.group(1):
            counter += 1
            current = f"{m.group(1).capitalize()} {section}.{counter}"
        elif m.group(2):
            current = f"the text of Section {section}" if section else "the introduction"
        elif m.group(3):
            name = m.group(3).replace("\\_", "_")
            seen.setdefault(name, current)
    return seen


def block(title, name, decl):
    rule = "=" * 78
    if decl is None:
        return f"{rule}\n{title}: {name}\n(not found in Plaplacian/)\n{rule}\n"
    return (f"{rule}\n{title}: {name}\n{decl['file']}, lines {decl['start']}-{decl['end']}\n"
            f"{rule}\n\n{decl['code'].rstrip()}\n\n")


def main():
    tex = ARTICLE.read_text(encoding="utf-8")
    cited = cited_names(tex)
    decls, nfiles = build.index_lean()
    sha = build.commit_sha()
    out = [
        "Lean code of the declarations cited in the article\n"
        "\"A formally verified convergence theorem for the tug-of-war scheme of the\n"
        "normalized p-Laplacian\" by J. J. Manfredi and B. Moosavi.\n\n"
        f"Extracted from the repository at commit {sha[:12]}\n"
        "(https://github.com/BehroozMoosavi/tugofwar_formalization)\n"
        "by docs/article/lean_code.py. Lean 4.34.0-rc2 (toolchain\n"
        "leanprover/lean4:v4.34.0-rc2); Mathlib commit\n"
        "85e3a25e006c35636f0e53b0e9296caca2685bc0.\n\n"
        "Each entry gives the place in the article where the declaration is cited,\n"
        "its file and lines, and its exact source: docstring, statement and proof.\n"
    ]
    found, missing, axioms = 0, [], []
    out.append("\nCONTENTS\n")
    for name, where in cited.items():
        out.append(f"  {where:<22} {name}{'  (Lean axiom)' if name in AXIOMS else ''}\n")
    out.append("\n\nPART I. DECLARATIONS CITED IN THE ARTICLE\n\n")
    for name, where in cited.items():
        if name in AXIOMS:
            axioms.append(name)
            continue
        d = build.find_decl(name if "." in name else "PLaplacian." + name, decls)
        found += d is not None
        if d is None:
            missing.append(name)
        out.append(block(where[0].upper() + where[1:], name, d))
    out.append("\nPART II. DEFINITIONS USED IN THESE STATEMENTS\n\n")
    for name in SUPPORT:
        d = build.find_decl("PLaplacian." + name, decls)
        if d is not None:
            out.append(block("Definition", name, d))
    out.append("=" * 78 + "\nAXIOMS\n" + "=" * 78 + "\n\n"
               "The main theorems depend only on the axioms "
               + ", ".join(sorted(axioms or AXIOMS)) + ",\n"
               "which belong to Lean's core library and are not part of this "
               "development.\nTo check: #print axioms PLaplacian.pharmonious_exists_converge\n")
    OUT.write_text("".join(out), encoding="utf-8")
    print(f"Cited in the article: {len(cited)} names "
          f"({len(axioms)} Lean axioms, {found} declarations found).")
    if missing:
        print("Not found in Plaplacian/:", ", ".join(missing))
    print(f"Written to {OUT.relative_to(ROOT)} ({len(''.join(out).splitlines())} lines).")


if __name__ == "__main__":
    main()
