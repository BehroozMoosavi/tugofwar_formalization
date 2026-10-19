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
    if name in decls:
        return decls[name]
    # tolerate a missing or extra namespace prefix
    tails = [k for k in decls if k.endswith("." + name) or name.endswith("." + k)]
    if len(tails) == 1:
        return decls[tails[0]]
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
    r"|(?P<word>[A-Za-z_][A-Za-z0-9_'!?.]*)"
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
          "options": {"skipHtmlTags": ["script", "noscript", "style",
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
             (REPO_URL, "Repository"),
             (f"{REPO_URL}/blob/main/docs/blueprint/blueprint.pdf", "PDF")]
    links = "".join(
        f'<a href="{u}"{" class=active" if t == active else ""}>{t}</a>' for u, t in items)
    return f'<nav class="top"><span class="brand">Blueprint</span>{links}</nav>'


def build_index(chapters, index, decls, sha, macros):
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
                f'<div class="statement">{latex_to_html(n["body"], index)}</div>'
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


def main():
    strict = "--strict" in sys.argv
    macros = read_macros()
    chapters, index = parse_blueprint()
    decls, nfiles = index_lean()
    sha = commit_sha()
    if OUT.exists():
        shutil.rmtree(OUT)
    (OUT / "assets").mkdir(parents=True)
    for asset in ("style.css", "site.js"):
        shutil.copy(SITE_SRC / "assets" / asset, OUT / "assets" / asset)
    idx, missing = build_index(chapters, index, decls, sha, macros)
    (OUT / "index.html").write_text(idx, encoding="utf-8")
    gph, dot = build_graph(chapters, index, decls, macros)
    (OUT / "graph.html").write_text(gph, encoding="utf-8")
    (OUT / "graph.dot").write_text(dot, encoding="utf-8")
    (OUT / ".nojekyll").write_text("")
    print(f"Read {len(index)} statements from the blueprint and "
          f"{len(decls)} declarations from {nfiles} Lean files.")
    if missing:
        print(f"{len(missing)} Lean names were not found:", file=sys.stderr)
        for m in missing:
            print("   ", m, file=sys.stderr)
    else:
        print("Every Lean name in the blueprint was found.")
    print(f"{len(warnings)} warnings. Site written to {OUT}.")
    if strict and missing:
        sys.exit(1)


if __name__ == "__main__":
    main()
