#!/usr/bin/env python3
"""Build the blueprint website.

Reads the blueprint (docs/blueprint/content.tex and macros/common.tex), finds
every Lean declaration named in a \\lean{...} annotation in the sources under
Plaplacian/, and writes a static website to _site/:

  index.html   every definition and theorem, with its statement, its
               dependencies, a proof sketch, and the exact Lean source of the
               declarations that prove it
  graph.html   the dependency graph; clicking a node opens its statement

The Lean source shown on the site is read from the repository at build time,
so it is always the code of the commit being built. Names that cannot be found
are reported on the site and in the build log.

Usage:  python3 docs/blueprint/site/build.py [--strict]
        (--strict: exit with an error if any Lean name is not found)
"""
import html
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import unicodedata

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import lean2tex  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[3]
BP = ROOT / "docs" / "blueprint"
SITE_SRC = BP / "site"
OUT = ROOT / "_site"
LEAN_DIR = ROOT / "Plaplacian"
REPO_URL = "https://github.com/BehroozMoosavi/tugofwar_formalization"
TITLE = ("A formally verified convergence theorem for the tug-of-war scheme "
         "of the normalized p-Laplacian")
TITLE_HTML = ("A formally verified convergence theorem for the tug-of-war "
              "scheme of the normalized \\(p\\)-Laplacian")
AUTHORS = "Juan J. Manfredi and Behrooz Moosavi"

warnings = []


def warn(msg):
    warnings.append(msg)
    print("warning:", msg, file=sys.stderr)


# --------------------------------------------------------------------------
# Brace-aware helpers
# --------------------------------------------------------------------------

def match_brace(s, i):
    """Given s[i] == '{', return the index of the matching '}'."""
    depth = 0
    for j in range(i, len(s)):
        c = s[j]
        if c == "\\":
            continue
        if c == "{" and (j == 0 or s[j - 1] != "\\"):
            depth += 1
        elif c == "}" and (j == 0 or s[j - 1] != "\\"):
            depth -= 1
            if depth == 0:
                return j
    raise ValueError("unbalanced braces near: " + s[i:i + 60])


def replace_command(s, cmd, fn):
    """Replace every \\cmd{arg} in s by fn(arg), arguments may nest braces."""
    pat = "\\" + cmd + "{"
    out, i = [], 0
    while True:
        k = s.find(pat, i)
        if k < 0:
            out.append(s[i:])
            return "".join(out)
        # require a non-letter after the command name (avoid \emphx)
        out.append(s[i:k])
        start = k + len(pat) - 1
        end = match_brace(s, start)
        out.append(fn(s[start + 1:end]))
        i = end + 1


# --------------------------------------------------------------------------
# Macros for MathJax
# --------------------------------------------------------------------------

def read_macros():
    text = (BP / "macros" / "common.tex").read_text(encoding="utf-8")
    macros = {}
    i = 0
    while True:
        k = text.find("\\newcommand{", i)
        if k < 0:
            break
        a = k + len("\\newcommand")
        name_end = match_brace(text, a)
        name = text[a + 1:name_end].lstrip("\\")
        j = name_end + 1
        nargs = 0
        m = re.match(r"\[(\d)\]", text[j:])
        if m:
            nargs = int(m.group(1))
            j += m.end()
        while text[j] != "{":
            j += 1
        body_end = match_brace(text, j)
        body = text[j + 1:body_end]
        macros[name] = [body, nargs] if nargs else body
        i = body_end + 1
    # The print macro for the averaged integral uses \mathrlap and \rule,
    # which MathJax may not provide; draw the same symbol with basic commands.
    if "fint" in macros:
        macros["fint"] = r"\mathop{\int\mkern-17.5mu{-}\mkern1mu}\nolimits"
    return macros


# --------------------------------------------------------------------------
# The blueprint
# --------------------------------------------------------------------------

KIND_NAMES = {"definition": "Definition", "theorem": "Theorem",
              "lemma": "Lemma", "proposition": "Proposition",
              "corollary": "Corollary"}
ABBREV = {"definition": "Def.", "theorem": "Thm.", "lemma": "Lem.",
          "proposition": "Prop.", "corollary": "Cor."}


def parse_blueprint():
    text = (BP / "content.tex").read_text(encoding="utf-8")
    chapters = []
    parts = re.split(r"\\chapter\{([^}]*)\}", text)
    # parts = [preamble, title1, body1, title2, body2, ...]
    for ci in range(1, len(parts), 2):
        ctitle, cbody = parts[ci], parts[ci + 1]
        nodes = []
        env = re.compile(
            r"\\begin\{(definition|theorem|lemma|proposition|corollary)\}"
            r"(?:\[(.*?)\])?\s*\\label\{([^}]*)\}(.*?)\\end\{\1\}"
            r"(\s*\\begin\{proof\}(.*?)\\end\{proof\})?", re.S)
        for m in env.finditer(cbody):
            kind, title, label, body = m.group(1), m.group(2) or "", m.group(3), m.group(4)
            proof = m.group(6) or ""

            def take(cmd, src):
                vals = []
                for mm in re.finditer(r"\\" + cmd + r"\{([^}]*)\}", src):
                    vals += [x.strip() for x in mm.group(1).split(",") if x.strip()]
                return vals

            node = {
                "kind": kind, "title": title.strip(), "label": label,
                "lean": take("lean", body),
                "leanok": "\\leanok" in body,
                "uses": take("uses", body),
                "proof_uses": take("uses", proof),
                "proof_leanok": "\\leanok" in proof,
                "body": re.sub(r"\\(lean|uses)\{[^}]*\}|\\leanok", "", body).strip(),
                "proof": re.sub(r"\\(lean|uses)\{[^}]*\}|\\leanok", "", proof).strip(),
                "chapter": len(chapters) + 1,
            }
            nodes.append(node)
        chapters.append({"title": ctitle, "nodes": nodes})
    # numbering: one counter per chapter, shared by all kinds (as in the PDF)
    index = {}
    for c, ch in enumerate(chapters, 1):
        for k, n in enumerate(ch["nodes"], 1):
            n["number"] = f"{c}.{k}"
            index[n["label"]] = n
    for n in index.values():
        for dep in n["uses"] + n["proof_uses"]:
            if dep not in index:
                warn(f"{n['label']} uses unknown label {dep}")
    return chapters, index


# --------------------------------------------------------------------------
# LaTeX to HTML (for statements and proof sketches; MathJax renders the math)
# --------------------------------------------------------------------------

MATH_RE = re.compile(
    r"(\\\[.*?\\\]|\$\$.*?\$\$|\$(?:\\\$|[^$])+?\$|\\\(.*?\\\)"
    r"|\\begin\{(?:equation|align|gather|multline)\*?\}.*?"
    r"\\end\{(?:equation|align|gather|multline)\*?\})", re.S)

ACCENTS = {"'": "\u0301", "`": "\u0300", '"': "\u0308", "^": "\u0302", "~": "\u0303"}


def latex_to_html(src, index):
    # Replace each math segment by a placeholder, convert the text as a whole
    # (so that a command such as \emph{...} may contain math), then restore
    # the math for MathJax.
    maths = []

    def stash(m):
        math = re.sub(r"\\label\{[^}]*\}", "", m.group(0))
        math = re.sub(r"\\begin\{(equation|gather|multline)\}", r"\\begin{\1*}", math)
        math = re.sub(r"\\end\{(equation|gather|multline)\}", r"\\end{\1*}", math)
        maths.append(html.escape(math, quote=False))
        return f"\ue000{len(maths) - 1}\ue001"

    s = text_to_html(MATH_RE.sub(stash, src), index).strip()
    paras = [p.strip() for p in re.split(r"\n\s*\n", s) if p.strip()]
    s = "".join(p if p.startswith(("<ul", "<ol")) else f"<p>{p}</p>" for p in paras)
    return re.sub("\ue000(\\d+)\ue001", lambda m: maths[int(m.group(1))], s)


def ref_html(label, index):
    n = index.get(label)
    if not n:
        warn(f"reference to unknown label {label}")
        return "??"
    return (f'<a class="ref" href="#{html.escape(label)}">'
            f'{KIND_NAMES[n["kind"]]}&nbsp;{n["number"]}</a>')


def text_to_html(t, index):
    t = html.escape(t, quote=False)
    # lists
    t = re.sub(r"\\begin\{itemize\}(\[[^\]]*\])?", "\n\n<ul>", t)
    t = t.replace("\\end{itemize}", "</ul>\n\n")
    t = re.sub(r"\\begin\{enumerate\}(\[[^\]]*\])?", "\n\n<ol>", t)
    t = t.replace("\\end{enumerate}", "</ol>\n\n")
    t = re.sub(r"\\item\[([^\]]*)\]\s*", r'<li class="lbl"><span class="itemlabel">\1</span> ', t)
    t = re.sub(r"\\item\s*", "<li>", t)
    # commands with an argument
    t = replace_command(t, "texttt", lambda a: "<code>" + a.replace("\\_", "_") + "</code>")
    for cmd, tag in (("emph", "em"), ("textit", "em"), ("textbf", "strong"),
                     ("textsc", "span"), ("mbox", "span"), ("text", "span")):
        t = replace_command(t, cmd, lambda a, tag=tag: f"<{tag}>{a}</{tag}>")
    t = replace_command(t, "ref", lambda a: ref_html(a.strip(), index))
    t = replace_command(t, "eqref", lambda a: "")
    t = replace_command(t, "footnote", lambda a: f" ({a})")
    # accents
    def accent(m):
        return unicodedata.normalize("NFC", m.group(2) + ACCENTS[m.group(1)])
    t = re.sub(r"\\(['`\"^~])\{?([A-Za-z])\}?", accent, t)
    # simple replacements
    for a, b in (("---", "\u2014"), ("--", "\u2013"), ("``", "\u201c"),
                 ("''", "\u201d"), ("~", "\u00a0"), ("\\S", "\u00a7"),
                 ("\\ldots", "\u2026"), ("\\dots", "\u2026"), ("\\,", "\u2009"),
                 ("\\&amp;", "&amp;"), ("\\%", "%"), ("\\_", "_"),
                 ("\\\\", "<br>"), ("\\ ", " ")):
        t = t.replace(a, b)
    t = re.sub(r"\\(par|noindent|medskip|smallskip|bigskip|allowbreak|quad|qquad)\b\s*", " ", t)
    for m in re.finditer(r"\\([A-Za-z]+)", t):
        warn(f"unconverted LaTeX command \\{m.group(1)} in text")
    t = re.sub(r"\\([A-Za-z]+)", r"\1", t)
    t = t.replace("{", "").replace("}", "")
    return t


# --------------------------------------------------------------------------
# Lean sources
# --------------------------------------------------------------------------

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)\s+"
    r"([^\s:({\[⦃]+)")


def index_lean():
    """Map each fully qualified declaration name to its location."""
    decls = {}
    files = sorted(LEAN_DIR.rglob("*.lean"))
    for f in files:
        lines = f.read_text(encoding="utf-8").split("\n")
        stack = []  # (kind, name) for namespaces and sections
        for i, line in enumerate(lines):
            m = re.match(r"^namespace\s+(\S+)", line)
            if m:
                for part in m.group(1).split("."):
                    stack.append(("ns", part))
                continue
            m = re.match(r"^(?:noncomputable\s+)?section(?:\s+(\S+))?", line)
            if m:
                stack.append(("sec", m.group(1) or ""))
                continue
            m = re.match(r"^end(?:\s+(\S+))?\s*$", line)
            if m:
                name = m.group(1)
                if name is None:
                    if stack:
                        stack.pop()
                else:
                    k = len(name.split("."))
                    for _ in range(k):
                        if stack:
                            stack.pop()
                continue
            m = DECL_RE.match(line)
            if not m:
                continue
            short = m.group(2)
            if short.startswith("_root_."):
                full = short[len("_root_."):]
            else:
                ns = [n for kind, n in stack if kind == "ns"]
                full = ".".join(ns + [short])
            start = i
            # include the docstring, attributes and `open ... in` just above
            j = i - 1
            while j >= 0:
                prev = lines[j]
                if prev.startswith("@[") or re.match(r"^open\s.*\sin\s*$", prev):
                    start = j
                    j -= 1
                    continue
                if prev.rstrip().endswith("-/"):
                    k = j
                    while k >= 0 and not lines[k].lstrip().startswith("/--"):
                        k -= 1
                    if k >= 0:
                        start = k
                        j = k - 1
                        continue
                break
            # the declaration ends before the next line starting in column 0
            end = i
            for k in range(i + 1, len(lines)):
                if lines[k].strip() == "":
                    continue
                if not lines[k][0].isspace():
                    break
                end = k
            rel = f.relative_to(ROOT).as_posix()
            decls.setdefault(full, {"file": rel, "start": start + 1, "end": end + 1,
                                    "code": "\n".join(lines[start:end + 1])})
    return decls, len(files)


def find_decl(name, decls):
    """Find a declaration by its full name. If the name is not found as written,
    accept a declaration whose name differs only in its namespace prefix, but
    only when exactly one such declaration exists, so the match is never
    ambiguous."""
    if name in decls:
        return decls[name]
    short = name[len("PLaplacian."):] if name.startswith("PLaplacian.") else name
    cands = [k for k in decls
             if k == short or k.endswith("." + short) or name.endswith("." + k)]
    if len(cands) == 1:
        return decls[cands[0]]
    if len(cands) > 1:
        warn(f"{name} matches several declarations: {', '.join(sorted(cands))}")
    return None


LEAN_KEYWORDS = ("theorem lemma def abbrev structure class instance inductive "
                 "where extends noncomputable private protected open namespace "
                 "section end variable universe import set_option attribute "
                 "fun λ let in if then else match with do return at by "
                 "have show from calc suffices obtain").split()
LEAN_TACTICS = ("exact refine intro intros apply rw rwa simp simpa dsimp "
                "linarith nlinarith positivity ring field_simp norm_num omega "
                "constructor rcases rintro obtain use exists unfold induction "
                "cases by_cases by_contra contradiction exfalso push_neg "
                "specialize gcongr filter_upwards convert congr ext funext "
                "aesop tauto trivial rfl assumption split_ifs choose set "
                "calc show beta_reduce").split()
TOKEN_RE = re.compile(
    r"(?P<comment>/-[\s\S]*?-/|--[^\n]*)"
    r"|(?P<string>\"(?:\\.|[^\"\\])*\")"
    r"|(?P<attr>@\[[^\]]*\])"
    r"|(?P<word>[^\W\d][\w'!?.]*)"
    r"|(?P<num>\b\d+(?:\.\d+)?\b)")


def highlight_lean(code):
    out, pos = [], 0
    for m in TOKEN_RE.finditer(code):
        out.append(html.escape(code[pos:m.start()], quote=False))
        tok = html.escape(m.group(0), quote=False)
        kind = m.lastgroup
        if kind == "comment":
            out.append(f'<span class="tk-c">{tok}</span>')
        elif kind == "string":
            out.append(f'<span class="tk-s">{tok}</span>')
        elif kind == "attr":
            out.append(f'<span class="tk-a">{tok}</span>')
        elif kind == "num":
            out.append(f'<span class="tk-n">{tok}</span>')
        elif m.group(0) in LEAN_KEYWORDS:
            out.append(f'<span class="tk-k">{tok}</span>')
        elif m.group(0) in LEAN_TACTICS:
            out.append(f'<span class="tk-t">{tok}</span>')
        else:
            out.append(tok)
        pos = m.end()
    out.append(html.escape(code[pos:], quote=False))
    return "".join(out)


# --------------------------------------------------------------------------
# Pages
# --------------------------------------------------------------------------

def commit_sha():
    sha = os.environ.get("GITHUB_SHA")
    if sha:
        return sha
    try:
        return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT,
                                       text=True).strip()
    except Exception:
        return "main"


def page(title, body, macros, extra_head=""):
    mj = {"tex": {"macros": macros,
                  "inlineMath": [["$", "$"], ["\\(", "\\)"]],
                  "displayMath": [["\\[", "\\]"], ["$$", "$$"]],
                  "processEnvironments": True},
          "options": {"ignoreHtmlClass": "mj-lazy", "processHtmlClass": "mj-now",
                      "skipHtmlTags": ["script", "noscript", "style",
                                       "textarea", "pre", "code"]},
          "chtml": {"displayAlign": "center"}}
    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)}</title>
<link rel="stylesheet" href="assets/style.css">
<script>window.MathJax = {json.dumps(mj)};</script>
<script defer src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js"></script>
{extra_head}
</head>
<body>
{body}
<script src="assets/site.js"></script>
</body>
</html>
"""


def nav(active):
    items = [("index.html", "Blueprint"), ("graph.html", "Dependency graph"),
             ("graph3d.html", "3D map"), ("library.html", "All declarations"),
             (REPO_URL, "Repository"),
             (f"{REPO_URL}/blob/main/docs/blueprint/blueprint.pdf", "PDF")]
    links = "".join(
        f'<a href="{u}"{" class=active" if t == active else ""}>{t}</a>' for u, t in items)
    return f'<nav class="top"><span class="brand">Blueprint</span>{links}</nav>'


STATEMENTS = SITE_SRC / "statements.json"
NAMES_FILE = SITE_SRC / "lean_names.txt"


def load_statements():
    if not STATEMENTS.exists():
        return {}
    data = json.loads(STATEMENTS.read_text(encoding="utf-8"))
    return {st["name"]: st for st in data if not st.get("missing")}


def formal_block(n, statements):
    """The statements of the node's Lean declarations, typeset from Lean's output."""
    blocks = []
    for name in n["lean"]:
        st = statements.get(name)
        if st is None:
            continue
        try:
            body, ok = lean2tex.render_statement(st)
        except Exception as e:                     # never let one statement stop the build
            warn(f"could not typeset {name} ({type(e).__name__}); shown as Lean code")
            body, ok = "<p><code>" + html.escape(st.get("conclusion", "")) + "</code></p>", False
        note = "" if ok else '<span class="fs-note">parts shown as Lean code</span>'
        blocks.append(f'<div class="fs-decl"><div class="fs-name"><code>'
                      f'{html.escape(name.replace("PLaplacian.", ""))}</code>{note}</div>'
                      f'{body}</div>')
    if not blocks:
        return ""
    return ('<div class="formal"><div class="fs-head">Formal statement'
            '<span>generated from the Lean declaration</span></div>'
            + "".join(blocks) + "</div>")


FORMAL_TEX = BP / "content-formal.tex"


def write_formal_blueprint(statements):
    """The blueprint with, after each statement, its formal statement typeset
    from Lean's export. Used by print.tex for the PDF."""
    text = (BP / "content.tex").read_text(encoding="utf-8")
    env = re.compile(r"\\begin\{(definition|theorem|lemma|proposition|corollary)\}"
                     r"(?:\[.*?\])?\s*\\label\{[^}]*\}(.*?)\\end\{\1\}", re.S)
    pieces, pos, inserted, partial = [], 0, 0, 0
    for m in env.finditer(text):
        names = []
        for mm in re.finditer(r"\\lean\{([^}]*)\}", m.group(2)):
            names += [x.strip() for x in mm.group(1).split(",") if x.strip()]
        blocks = []
        for name in names:
            st = statements.get(name)
            if st is None:
                continue
            try:
                body, ok = lean2tex.render_statement_tex(st)
            except Exception as e:                 # never let one statement stop the build
                warn(f"could not typeset {name} for the PDF ({type(e).__name__})")
                body = "\\texttt{" + lean2tex.tex_escape(st.get("conclusion", "")) + "}\n"
                ok = False
            partial += not ok
            blocks.append("\\begin{formalstatement}{%s}\n%s\\end{formalstatement}\n"
                          % (lean2tex.tex_escape(name.replace("PLaplacian.", "")), body))
        pieces.append(text[pos:m.end()])
        if blocks:
            pieces.append("\n" + "".join(blocks))
            inserted += len(blocks)
        pos = m.end()
    pieces.append(text[pos:])
    header = ("% Generated by docs/blueprint/site/build.py from content.tex and\n"
              "% statements.json (exported from Lean by ExportStatements.lean.txt).\n"
              "% Do not edit: edit content.tex, or the Lean code, and rebuild.\n")
    FORMAL_TEX.write_text(header + "".join(pieces), encoding="utf-8")
    return inserted, partial


def build_index(chapters, index, decls, sha, macros, statements):
    used_by = {lab: [] for lab in index}
    for n in index.values():
        for dep in dict.fromkeys(n["uses"] + n["proof_uses"]):
            if dep in used_by:
                used_by[dep].append(n["label"])
    n_nodes = len(index)
    n_names = len({x for n in index.values() for x in n["lean"]})
    missing = sorted({x for n in index.values() for x in n["lean"] if not find_decl(x, decls)})

    def chips(labels):
        return "".join(
            f'<a class="chip" href="#{l}" title="{html.escape(index[l]["title"])}">'
            f'{ABBREV[index[l]["kind"]]}&nbsp;{index[l]["number"]}</a>'
            for l in labels if l in index)

    toc = "".join(f'<li><a href="#ch{c}">{c}. {html.escape(ch["title"])}</a></li>'
                  for c, ch in enumerate(chapters, 1))
    parts = [nav("Blueprint"), '<main>',
             f'<header class="intro"><h1>{TITLE_HTML}</h1>',
             f'<p class="authors">{AUTHORS}</p>',
             f'<p>Every definition and theorem on the route to the main result, '
             f'with the results it uses and the Lean code that proves it. '
             f'Click <em>Lean</em> under a statement to see its source, read '
             f'from the repository at commit <a href="{REPO_URL}/tree/{sha}">'
             f'<code>{sha[:7]}</code></a>.</p>',
             f'<p class="stats"><span>{n_nodes} statements</span>'
             f'<span>{n_names} Lean declarations</span>'
             f'<span class="{"ok" if not missing else "bad"}">'
             f'{"all formalized" if not missing else str(len(missing)) + " names not found"}'
             f'</span></p>',
             '<input id="filter" type="search" placeholder="Filter by title, number or Lean name…" '
             'aria-label="Filter statements">',
             f'<ul class="toc">{toc}</ul></header>']
    for c, ch in enumerate(chapters, 1):
        parts.append(f'<section class="chapter" id="ch{c}"><h2>{c}. {html.escape(ch["title"])}</h2>')
        for n in ch["nodes"]:
            kind = KIND_NAMES[n["kind"]]
            lean_blocks, found_all = [], True
            for name in n["lean"]:
                d = find_decl(name, decls)
                if d is None:
                    found_all = False
                    lean_blocks.append(
                        f'<div class="decl missing"><div class="declhead">'
                        f'<code>{html.escape(name)}</code><span class="where">'
                        f'not found in the sources</span></div></div>')
                    continue
                url = f'{REPO_URL}/blob/{sha}/{d["file"]}#L{d["start"]}-L{d["end"]}'
                lean_blocks.append(
                    f'<div class="decl"><div class="declhead"><code>{html.escape(name)}</code>'
                    f'<a class="where" href="{url}">{html.escape(d["file"])}, '
                    f'lines {d["start"]}–{d["end"]}</a></div>'
                    f'<pre class="lean"><code>{highlight_lean(d["code"])}</code></pre></div>')
            status = ('<span class="badge ok" title="Formalized: every Lean name was found">'
                      '✓ formalized</span>' if (n["leanok"] and found_all and n["lean"])
                      else '<span class="badge bad">check Lean names</span>')
            search = " ".join([n["number"], n["title"], n["label"]] + n["lean"]).lower()
            uses = list(dict.fromkeys(n["uses"] + n["proof_uses"]))
            parts.append(
                f'<article class="node {n["kind"]}" id="{n["label"]}" data-search="{html.escape(search)}">'
                f'<div class="nodehead"><span class="kind">{kind} {n["number"]}</span>'
                f'<span class="title">{html.escape(n["title"])}</span>{status}</div>'
                + formal_block(n, statements)
                + (f'<div class="informal"><div class="fs-head">Informal statement'
                   f'<span>from the blueprint</span></div>' if statements else '')
                + f'<div class="statement">{latex_to_html(n["body"], index)}</div>'
                + ('</div>' if statements else '')
                + (f'<div class="deps"><span class="deplabel">Uses</span>{chips(uses)}</div>' if uses else '')
                + (f'<div class="deps"><span class="deplabel">Used by</span>{chips(used_by[n["label"]])}</div>'
                   if used_by[n["label"]] else '')
                + (f'<details class="lean-panel"><summary>Lean <span class="count">'
                   f'{len(n["lean"])}</span></summary>{"".join(lean_blocks)}</details>'
                   if n["lean"] else '')
                + (f'<details class="proof-panel"><summary>Proof sketch</summary>'
                   f'<div class="proof">{latex_to_html(n["proof"], index)}</div></details>'
                   if n["proof"] else '')
                + '</article>')
        parts.append('</section>')
    parts.append('<footer>Generated from <code>docs/blueprint/content.tex</code> and the '
                 'Lean sources by <code>docs/blueprint/site/build.py</code>.</footer></main>')
    return page("Blueprint — " + TITLE, "\n".join(parts), macros), missing


def build_graph(chapters, index, decls, macros):
    colors = ["#fff8e1", "#e3f2fd", "#f3e5f5", "#e0f7fa", "#fce4ec", "#ede7f6", "#f1f8e9"]
    main = {"thm:existsconv", "thm:main", "thm:viscomp", "thm:main4"}
    L = ['digraph G {', '  rankdir=LR; nodesep=0.12; ranksep=0.45; newrank=true; bgcolor="transparent";',
         '  node [shape=box, style="rounded,filled", fontname="Helvetica", fontsize=11, '
         'fillcolor="#e8f5e9", color="#2e7d32", margin="0.08,0.03", target="_top"];',
         '  edge [color="#666666", arrowsize=0.6];']
    for c, ch in enumerate(chapters, 1):
        L.append(f'  subgraph cluster_{c} {{ label="{c}. {ch["title"]}"; fontname="Helvetica-Bold"; '
                 f'fontsize=12; style="rounded,filled"; fillcolor="{colors[(c - 1) % len(colors)]}"; color="#999999";')
        for n in ch["nodes"]:
            ok = n["lean"] and all(find_decl(x, decls) for x in n["lean"])
            shape = "ellipse" if n["kind"] == "definition" else "box"
            extra = ', penwidth=2.5, fillcolor="#a5d6a7"' if n["label"] in main else ""
            if not ok:
                extra += ', color="#c62828", fillcolor="#ffebee"'
            tip = f'{KIND_NAMES[n["kind"]]} {n["number"]}: {n["title"]}'
            L.append(f'    "{n["label"]}" [label="{n["number"]}  {n["title"]}", shape={shape}, '
                     f'URL="index.html#{n["label"]}", tooltip="{tip}"{extra}];')
        L.append('  }')
    for n in index.values():
        for dep in dict.fromkeys(n["uses"] + n["proof_uses"]):
            if dep in index:
                L.append(f'  "{dep}" -> "{n["label"]}";')
    L.append('}')
    dot = "\n".join(L)
    try:
        svg = subprocess.run(["dot", "-Tsvg"], input=dot, text=True,
                             capture_output=True, check=True).stdout
        svg = svg[svg.index("<svg"):]
    except (FileNotFoundError, subprocess.CalledProcessError) as e:
        warn(f"Graphviz unavailable ({e}); the graph page will be empty")
        svg = "<p>The graph could not be generated: Graphviz is not installed.</p>"
    body = (nav("Dependency graph") +
            '<main class="wide"><header class="intro"><h1>Dependency graph</h1>'
            '<p>Arrows point from a result to the results that use it; the main '
            'theorem is at the far right. Click a node to open its statement and '
            'Lean code. Definitions are ellipses, theorems are boxes.</p>'
            '<div class="zoom"><button data-z="-1" aria-label="Zoom out">−</button>'
            '<button data-z="0" aria-label="Fit to width">Fit</button>'
            '<button data-z="1" aria-label="Zoom in">+</button></div></header>'
            f'<div id="graph" class="graph">{svg}</div></main>')
    return page("Dependency graph — " + TITLE, body, macros), dot


CHAPTER_COLORS = ["#e6a700", "#1f77b4", "#9467bd", "#17a2b8", "#d62728",
                  "#7f5bd5", "#2ca02c", "#8c564b", "#e377c2"]
MAIN_RESULTS = {"thm:existsconv", "thm:main", "thm:viscomp", "thm:main4",
                "thm:viscunique", "thm:discunique"}


def plain_title(t):
    """A title as plain text, for labels in the 3D map."""
    t = t.replace("$\\eps$", "\u03b5").replace("$\\varepsilon$", "\u03b5")
    t = re.sub(r"\$([^$]*)\$", r"\1", t)
    return re.sub(r"\\([A-Za-z]+)", r"\1", t).replace("{", "").replace("}", "")


def build_graph3d(chapters, index, decls, macros):
    nodes, links = [], []
    for c, ch in enumerate(chapters, 1):
        for n in ch["nodes"]:
            nodes.append({
                "id": n["label"], "number": n["number"],
                "title": plain_title(n["title"]),
                "kind": n["kind"], "kindName": KIND_NAMES[n["kind"]],
                "chapter": c, "chapterTitle": plain_title(ch["title"]),
                "lean": n["lean"], "main": n["label"] in MAIN_RESULTS,
                "color": CHAPTER_COLORS[(c - 1) % len(CHAPTER_COLORS)],
                "ok": bool(n["lean"]) and all(find_decl(x, decls) for x in n["lean"]),
            })
            for dep in dict.fromkeys(n["uses"] + n["proof_uses"]):
                if dep in index:
                    links.append({"source": dep, "target": n["label"]})
    data = {"nodes": nodes, "links": links,
            "chapters": [{"number": c, "title": plain_title(ch["title"]),
                          "color": CHAPTER_COLORS[(c - 1) % len(CHAPTER_COLORS)]}
                         for c, ch in enumerate(chapters, 1)]}
    blob = json.dumps(data, ensure_ascii=False).replace("</", "<\\/")
    body = (nav("3D map") + f"""
<div class="g3-wrap">
  <aside class="g3-side">
    <h1>3D dependency map</h1>
    <p class="g3-help">Drag to rotate &middot; scroll to zoom &middot; right-drag to pan
      &middot; click a node to select it</p>
    <div class="g3-search">
      <input id="g3-q" type="search" autocomplete="off" spellcheck="false"
             placeholder="Search a title, number (7.10) or Lean name"
             aria-label="Search the dependency map">
      <ul id="g3-results" role="listbox"></ul>
    </div>
    <div class="g3-controls">
      <label>Highlight
        <select id="g3-mode">
          <option value="direct">direct neighbours</option>
          <option value="up">everything it depends on</option>
          <option value="down">everything that uses it</option>
        </select>
      </label>
      <label>Layout
        <select id="g3-layout">
          <option value="">free (force-directed)</option>
          <option value="lr">layered, left to right</option>
          <option value="radialout">radial</option>
        </select>
      </label>
      <div class="g3-buttons">
        <button id="g3-clear" type="button">Clear selection</button>
        <button id="g3-fit" type="button">Fit all</button>
      </div>
    </div>
    <div id="g3-info" class="g3-info">
      <p class="g3-empty">Select a result, by searching or by clicking a node, to
        see what it depends on and what uses it.</p>
    </div>
    <div class="g3-legend-head">Chapters <span>(click to show or hide)</span></div>
    <div id="g3-legend" class="g3-legend"></div>
  </aside>
  <div id="g3-canvas" class="g3-canvas"></div>
</div>
<script id="g3-data" type="application/json">{blob}</script>
<script src="https://cdn.jsdelivr.net/npm/3d-force-graph@1/dist/3d-force-graph.min.js"></script>
<script src="assets/graph3d.js"></script>
""")
    return page("3D dependency map \u2014 " + TITLE, body, macros), len(nodes), len(links)


def decl_kind(code):
    for line in code.split("\n"):
        m = DECL_RE.match(line)
        if m:
            return m.group(1)
    return "declaration"


def build_library(index, decls, statements, sha, macros):
    """Every declaration of the library, grouped by file, with its formal
    statement generated from Lean and its source code."""
    cited = {}
    for n in index.values():
        for name in n["lean"]:
            d = find_decl(name, decls)
            if d is not None:
                cited.setdefault((d["file"], d["start"]), n)
    by_file = {}
    for name, d in decls.items():
        by_file.setdefault(d["file"], []).append((d["start"], name, d))
    n_stmt = sum(1 for name in decls if name in statements)
    parts = [nav("All declarations"), '<main>',
             '<header class="intro"><h1>All declarations</h1>',
             f'<p>Every declaration of the development, {len(decls)} in {len(by_file)} files, '
             f'with its formal statement generated from Lean and its source code at commit '
             f'<a href="{REPO_URL}/tree/{sha}"><code>{sha[:7]}</code></a>. Declarations used '
             f'in the blueprint link to their statement there. Open a declaration to see it.</p>',
             '<input id="lib-filter" type="search" placeholder="Filter by name or file…" '
             'aria-label="Filter declarations">',
             f'<p id="lib-count">{len(decls)} declarations; {n_stmt} with an exported statement.</p>',
             '</header>']
    for f in sorted(by_file):
        items = sorted(by_file[f])
        parts.append(f'<section class="lib-file" data-file="{html.escape(f.lower())}">'
                     f'<h2>{html.escape(f)}<span>{len(items)} declarations</span></h2>')
        for start, name, d in items:
            kind = decl_kind(d["code"])
            short = name.replace("PLaplacian.", "")
            node = cited.get((d["file"], d["start"]))
            bp = (f'<a class="lib-bp" href="index.html#{html.escape(node["label"])}">'
                  f'{KIND_NAMES[node["kind"]]} {node["number"]} in the blueprint</a>') if node else ''
            st = statements.get(name)
            if st is not None:
                try:
                    body, _ = lean2tex.render_statement(st)
                except Exception:
                    body = "<p><code>" + html.escape(st.get("conclusion", "")) + "</code></p>"
                formal = ('<div class="formal"><div class="fs-head">Formal statement'
                          '<span>generated from the Lean declaration</span></div>' + body + '</div>')
            else:
                formal = '<p class="lib-none">No exported statement.</p>'
            url = f'{REPO_URL}/blob/{sha}/{d["file"]}#L{d["start"]}-L{d["end"]}'
            parts.append(
                f'<details class="lib-decl" data-search="{html.escape((short + " " + f).lower())}">'
                f'<summary><span class="lib-kind {html.escape(kind)}">{html.escape(kind)}</span>'
                f'<span class="lib-name">{html.escape(short)}</span>{bp}</summary>'
                f'<div class="lib-body mj-lazy">{formal}'
                f'<div class="decl"><div class="declhead"><code>{html.escape(name)}</code>'
                f'<a class="where" href="{url}">{html.escape(d["file"])}, lines '
                f'{d["start"]}–{d["end"]}</a></div>'
                f'<pre class="lean"><code>{highlight_lean(d["code"])}</code></pre></div>'
                f'</div></details>')
        parts.append('</section>')
    parts.append('</main>')
    return page("All declarations — " + TITLE, "\n".join(parts), macros), len(decls), n_stmt


def main():
    strict = "--strict" in sys.argv
    macros = read_macros()
    chapters, index = parse_blueprint()
    decls, nfiles = index_lean()
    sha = commit_sha()
    if OUT.exists():
        shutil.rmtree(OUT)
    (OUT / "assets").mkdir(parents=True)
    for asset in ("style.css", "site.js", "graph3d.js"):
        shutil.copy(SITE_SRC / "assets" / asset, OUT / "assets" / asset)
    # the names for ExportStatements.lean, and the statements it produced
    names = sorted({x for n in index.values() for x in n["lean"]} | set(decls))
    NAMES_FILE.write_text("\n".join(names) + "\n", encoding="utf-8")
    statements = load_statements()
    idx, missing = build_index(chapters, index, decls, sha, macros, statements)
    (OUT / "index.html").write_text(idx, encoding="utf-8")
    gph, dot = build_graph(chapters, index, decls, macros)
    (OUT / "graph.html").write_text(gph, encoding="utf-8")
    (OUT / "graph.dot").write_text(dot, encoding="utf-8")
    g3, n3, l3 = build_graph3d(chapters, index, decls, macros)
    (OUT / "graph3d.html").write_text(g3, encoding="utf-8")
    lib, n_lib, n_lib_st = build_library(index, decls, statements, sha, macros)
    (OUT / "library.html").write_text(lib, encoding="utf-8")
    print(f"Library page: {n_lib} declarations, {n_lib_st} with a formal statement from Lean.")
    (OUT / ".nojekyll").write_text("")
    print(f"Read {len(index)} statements from the blueprint and "
          f"{len(decls)} declarations from {nfiles} Lean files.")
    if missing:
        print(f"{len(missing)} Lean names were not found:", file=sys.stderr)
        for m in missing:
            print("   ", m, file=sys.stderr)
    else:
        print("Every Lean name in the blueprint was found.")
    if statements:
        n_tex, n_partial = write_formal_blueprint(statements)
        print(f"Blueprint LaTeX: {n_tex} formal statements generated from Lean "
              f"into docs/blueprint/content-formal.tex.")
        def _typeset(st):
            try:
                return lean2tex.render_statement(st)[1]
            except Exception:
                return False
        partial = [name for name, st in statements.items() if not _typeset(st)]
        print(f"Formal statements: {len(statements)} declarations read from statements.json; "
              f"{len(statements) - len(partial)} fully typeset.")
        for name in partial:
            print(f"    shown partly as Lean code: {name}")
    else:
        print("No statements.json yet: run `sh docs/blueprint/site/export.sh`"
              " to add the formal statements, then build again.")
    print(f"{len(warnings)} warnings. Site written to {OUT}.")
    if strict and missing:
        sys.exit(1)


if __name__ == "__main__":
    main()
