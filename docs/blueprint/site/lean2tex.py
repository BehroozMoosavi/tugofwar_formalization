"""Typeset statements exported from Lean (statements.json) as LaTeX.

The input is the output of Lean's pretty-printer, for each declaration: its
parameters and hypotheses (binders) and its conclusion. This module parses that
notation and renders it for MathJax. It never invents content: anything it
cannot parse is shown verbatim as Lean code instead.
"""
import html
import re

# ---------------------------------------------------------------------------
# Tokens
# ---------------------------------------------------------------------------

SYMBOLS = ["∀ᶠ", "∃ᶠ", "=>", "⁻¹", "\\", "≤", "≥", "≠", "→", "↔", "∧", "∨", "¬", "∈", "∉", "⊆",
           "⊂", "∩", "∪", "∀", "∃", "⨍", "∫", "⨆", "⨅", "∑", "∏", "‖", "|",
           "↑", "•", "∘", "×", "(", ")", "[", "]", "{", "}", "⟨", "⟩", "⟪",
           "⟫", ",", ":", "+", "-", "*", "/", "^", "=", "<", ">", "∞", "''"]
TOKEN_RE = re.compile(
    r"\s+|(?P<num>\d+(?:\.\d+)?)"
    r"|(?P<sym>" + "|".join(re.escape(s) for s in sorted(SYMBOLS, key=len, reverse=True)) + r")"
    r"|(?P<id>[^\W\d][\w'₀-₉!?.]*)"
    r"|(?P<other>\S)")


class Unsupported(Exception):
    """Raised for notation the renderer does not handle."""


# Lean keywords: never variables. Meeting one means the notation is not
# understood, so the renderer stops instead of typesetting it as a name.
RESERVED = {"in", "if", "then", "else", "match", "with", "let", "have", "show",
            "from", "by", "do", "at", "fun", "λ", "where"}


def tokenize(s):
    out = []
    for m in TOKEN_RE.finditer(s):
        if m.lastgroup is None:
            continue
        if m.lastgroup == "other":
            raise Unsupported(m.group(0))
        out.append(m.group(0))
    return out


# ---------------------------------------------------------------------------
# Identifiers
# ---------------------------------------------------------------------------

GREEK = {"ι": r"\iota", "υ": r"\upsilon", "ϵ": r"\epsilon", "ϑ": r"\vartheta",
         "ϕ": r"\phi", "ς": r"\varsigma", "Υ": r"\Upsilon",
         "α": r"\alpha", "β": r"\beta", "γ": r"\gamma", "δ": r"\delta",
         "ε": r"\varepsilon", "ζ": r"\zeta", "η": r"\eta", "θ": r"\theta",
         "κ": r"\kappa", "λ": r"\lambda", "μ": r"\mu", "ν": r"\nu", "ξ": r"\xi",
         "π": r"\pi", "ρ": r"\rho", "σ": r"\sigma", "τ": r"\tau", "φ": r"\varphi",
         "χ": r"\chi", "ψ": r"\psi", "ω": r"\omega", "Γ": r"\Gamma", "Δ": r"\Delta",
         "Θ": r"\Theta", "Λ": r"\Lambda", "Ξ": r"\Xi", "Π": r"\Pi", "Σ": r"\Sigma",
         "Φ": r"\Phi", "Ψ": r"\Psi", "Ω": r"\Omega"}
CONSTANTS = {"ℝ": r"\mathbb{R}", "ℕ": r"\mathbb{N}", "ℤ": r"\mathbb{Z}",
             "ℚ": r"\mathbb{Q}", "ℂ": r"\mathbb{C}", "True": r"\mathrm{True}",
             "False": r"\mathrm{False}", "volume": r"\lambda"}
SUBSCRIPTS = str.maketrans("₀₁₂₃₄₅₆₇₈₉", "0123456789")
NAMESPACES = ("PLaplacian.", "Set.", "Metric.", "Bornology.", "MeasureTheory.",
              "Filter.", "Real.")


def strip_ns(name):
    for ns in NAMESPACES:
        if name.startswith(ns):
            return name[len(ns):]
    return name


def ident_tex(name):
    name = strip_ns(name)
    if len(name) > 1 and name.endswith("ᶜ"):         # the complement Ωᶜ
        return ident_tex(name[:-1]) + "^{c}"
    if name in CONSTANTS:
        return CONSTANTS[name]
    m = re.fullmatch(r"([^\W\d_]+?)([₀-₉]+|'+)?", name)
    if m:
        base, suffix = m.group(1), m.group(2) or ""
        if base in GREEK:
            base = GREEK[base]
        elif len(base) > 1:
            base = r"\mathrm{" + base + "}"
        if suffix.startswith("'"):
            return base + suffix
        if suffix:
            return base + "_{" + suffix.translate(SUBSCRIPTS) + "}"
        return base
    return r"\mathrm{" + name.replace("_", r"\_") + "}"


# ---------------------------------------------------------------------------
# Special functions and predicates
# ---------------------------------------------------------------------------

def T(s):
    """Prose inside math: "$U$ is open" -> U\\text{ is open}.

    The $...$ pieces stay math and the rest becomes \\text{...}, so no MathJax
    extension is needed."""
    out = []
    for k, seg in enumerate(s.split("$")):
        if k % 2:
            out.append(seg)
        elif seg:
            out.append(r"\text{" + seg + "}")
    return "".join(out)


def _range_of(a):
    m = re.fullmatch(r"\\operatorname\{range\}\((.*)\)", a)
    return m.group(1) if m else a


def _rhs_zero(f):
    return f in ("x \\mapsto 0", "0")


SPECIAL = {
    "tugOfWarOp": lambda a: (r"T_{%s} %s" % (a[1], a[2]) + (r"(%s)" % a[3] if len(a) > 3 else ""))
                  if len(a) >= 3 else None,
    "dppOp": lambda a: (r"\widetilde{T}_{%s} %s" % (a[1], a[3]) + (r"(%s)" % a[4] if len(a) > 4 else ""))
             if len(a) >= 4 else None,
    "frontier": lambda a: r"\partial %s" % a[0] if len(a) == 1 else None,
    "closure": lambda a: r"\overline{%s}" % a[0] if len(a) == 1 else None,
    "interior": lambda a: r"\operatorname{int} %s" % a[0] if len(a) == 1 else None,
    "ball": lambda a: r"B(%s, %s)" % (a[0], a[1]) if len(a) == 2 else None,
    "closedBall": lambda a: r"\overline{B}(%s, %s)" % (a[0], a[1]) if len(a) == 2 else None,
    "closureEps": lambda a: r"%s_{%s}" % (a[0], a[1]) if len(a) == 2 else None,
    "dist": lambda a: r"\operatorname{dist}(%s, %s)" % (a[0], a[1]) if len(a) == 2 else None,
    "ubar": lambda a: r"\overline{%s}" % a[0] + (r"(%s)" % a[1] if len(a) > 1 else ""),
    "lbar": lambda a: r"\underline{%s}" % a[0] + (r"(%s)" % a[1] if len(a) > 1 else ""),
    "EuclSpace": lambda a: r"\mathbb{R}^{%s}" % a[0] if len(a) == 1 else None,
    "EuclSpaceM": lambda a: r"\mathbb{R}^{%s}" % a[0] if len(a) == 1 else None,
    "sSup": lambda a: r"\sup %s" % a[0] if len(a) == 1 else None,
    "sInf": lambda a: r"\inf %s" % a[0] if len(a) == 1 else None,
    "IsOpen": lambda a: T(r"$%s$ is open" % a[0]) if len(a) == 1 else None,
    "IsClosed": lambda a: T(r"$%s$ is closed" % a[0]) if len(a) == 1 else None,
    "IsBounded": lambda a: T(r"$%s$ is bounded" % a[0]) if len(a) == 1 else None,
    "MeasurableSet": lambda a: T(r"$%s$ is measurable" % a[0]) if len(a) == 1 else None,
    "Measurable": lambda a: T(r"$%s$ is Borel measurable" % a[0]) if len(a) == 1 else None,
    "Continuous": lambda a: T(r"$%s$ is continuous" % a[0]) if len(a) == 1 else None,
    "UpperSemicontinuous": lambda a: T(r"$%s$ is upper semicontinuous" % a[0]) if len(a) == 1 else None,
    "LowerSemicontinuous": lambda a: T(r"$%s$ is lower semicontinuous" % a[0]) if len(a) == 1 else None,
    "BddMeas": lambda a: T(r"$%s$ is admissible (bounded and Borel measurable)" % a[0]) if len(a) == 1 else None,
    "BddAbove": lambda a: T(r"$%s$ is bounded above" % _range_of(a[0])) if len(a) == 1 else None,
    "BddBelow": lambda a: T(r"$%s$ is bounded below" % _range_of(a[0])) if len(a) == 1 else None,
    "Nontrivial": lambda a: T(r"$%s$ is nontrivial" % a[0]) if len(a) == 1 else None,
    "IsPHarmonious": lambda a: T(r"$%s$ is $%s$-harmonious in $%s$ with step $%s$ and data $%s$"
                                 % (a[4], a[0], a[2], a[1], a[3])) if len(a) == 5 else None,
    "IsViscositySubsolution": lambda a: T(
        r"$%s$ is a viscosity subsolution of $-\Delta_{%s}^{\mathrm N} u = %s$ in $%s$"
        % (a[3], a[0], "0" if _rhs_zero(a[2]) else a[2], a[1])) if len(a) == 4 else None,
    "IsViscositySupersolution": lambda a: T(
        r"$%s$ is a viscosity supersolution of $-\Delta_{%s}^{\mathrm N} u = %s$ in $%s$"
        % (a[3], a[0], "0" if _rhs_zero(a[2]) else a[2], a[1])) if len(a) == 4 else None,
}
def _tendsto(a):
    if len(a) != 3:
        return None
    m = re.fullmatch(r"(\S+) \\mapsto (.*)", a[0])
    lim = re.fullmatch(r"𝓝\((.*)\)", a[2])
    if m and lim and a[1] == r"\mathrm{atTop}":
        return r"%s \to %s \ \text{as } %s \to \infty" % (m.group(2), lim.group(1), m.group(1))
    return None


SPECIAL["Tendsto"] = _tendsto
SUFFIX_PREDICATES = {"Nonempty": "is nonempty"}

INFIX = {"≤": r"\le", "≥": r"\ge", "<": "<", ">": ">", "=": "=", "≠": r"\ne",
         "→": r"\to", "↔": r"\iff", "∧": r"\wedge", "∨": r"\vee", "∈": r"\in",
         "∉": r"\notin", "⊆": r"\subseteq", "⊂": r"\subset", "∩": r"\cap",
         "∪": r"\cup", "\\": r"\setminus", "+": "+", "-": "-", "*": r"\cdot", "/": "/",
         "•": r"\cdot", "∘": r"\circ", "×": r"\times"}
BINDERS = ("∀", "∃", "fun", "⨍", "∫", "⨆", "⨅")


# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------

class Parser:
    def __init__(self, tokens):
        self.t = tokens
        self.i = 0

    def peek(self, k=0):
        j = self.i + k
        return self.t[j] if j < len(self.t) else None

    def take(self, expected=None):
        tok = self.peek()
        if tok is None or (expected is not None and tok != expected):
            raise Unsupported(f"expected {expected!r}, found {tok!r}")
        self.i += 1
        return tok

    # an expression: binders, or applications joined by infix operators
    def expr(self, stops):
        tok = self.peek()
        if tok in BINDERS:
            return self.binder(stops)
        parts = []
        while True:
            tok = self.peek()
            if tok is None or tok in stops:
                break
            if tok == "^":
                self.take()
                parts.append("^{" + self.atom()[1] + "}")
                continue
            if tok in INFIX:
                self.take()
                parts.append(INFIX[tok])
                if self.peek() in BINDERS:
                    parts.append(self.binder(stops))
                    break
                continue
            if tok == "¬":
                self.take()
                parts.append(r"\neg")
                continue
            parts.append(self.app(stops))
        if not parts:
            raise Unsupported("empty expression")
        return " ".join(parts)

    def app(self, stops):
        items = []
        while True:
            tok = self.peek()
            if (tok is None or tok in stops or tok in INFIX or tok in BINDERS
                    or tok in ("^", "¬", "=>")):
                break
            items.append(self.atom())
        if not items:
            raise Unsupported(f"unexpected {self.peek()!r}")
        return render_app(items[0], items[1:])

    def atom(self):
        tok = self.take()
        if tok == "(":
            inner = self.expr({")", ":"})
            if self.peek() == ":":            # a type ascription (x : T): keep x
                depth = 0
                while True:
                    t = self.take()
                    if t == "(":
                        depth += 1
                    elif t == ")":
                        if depth == 0:
                            break
                        depth -= 1
                return ("group", inner)
            self.take(")")
            return ("group", inner)
        if tok in ("|", "‖"):
            inner = self.expr({tok})
            self.take(tok)
            return ("raw", (r"\lvert %s\rvert" if tok == "|" else r"\lVert %s\rVert") % inner)
        if tok == "⟪":
            a = self.expr({","})
            self.take(",")
            b = self.expr({"⟫"})
            self.take("⟫")
            if self.peek() is not None and self.peek().startswith("_"):
                self.take()                    # the subscript _ℝ of older notation
            return ("raw", r"\langle %s, %s\rangle" % (a, b))
        if tok == "↑":
            return self.atom()
        if tok == "∞":
            return ("raw", r"\infty")
        if re.fullmatch(r"\d+(\.\d+)?", tok):
            return ("num", tok)
        if tok == "⁻¹":
            return ("raw", "^{-1}")
        if tok in RESERVED:
            raise Unsupported(tok)
        if re.fullmatch(r"[^\W\d][\w'₀-₉!?.]*", tok):
            return ("ident", tok)
        raise Unsupported(tok)

    # ∀ … , body   ∃ … , body   fun … => body   ⨍ x in S, f   ⨆ x, f
    def binder(self, stops):
        kind = self.take()
        head = []
        depth = 0
        end = "=>" if kind == "fun" else ","
        while True:
            tok = self.peek()
            if tok is None:
                raise Unsupported("unterminated binder")
            if tok in ("(", "⟨", "{", "["):
                depth += 1
            elif tok in (")", "⟩", "}", "]"):
                depth -= 1
            elif tok == end and depth == 0:
                break
            head.append(self.take())
        self.take(end)
        body = self.expr(stops)
        if kind in ("⨍", "∫"):
            if "in" in head:
                k = head.index("in")
                var, dom = binder_vars(head[:k]), Parser(head[k + 1:]).expr(set())
                sym = r"\fint" if kind == "⨍" else r"\int"
                return r"%s_{%s} %s \, d%s" % (sym, dom, paren(body), var)
            sym = r"\fint" if kind == "⨍" else r"\int"
            return r"%s %s \, d%s" % (sym, paren(body), binder_vars(head))
        if kind in ("⨆", "⨅"):
            op = r"\sup" if kind == "⨆" else r"\inf"
            return r"%s_{%s} %s" % (op, binder_vars(head), body)
        if kind == "fun":
            return r"%s \mapsto %s" % (binder_vars(head), body)
        quant = r"\forall" if kind == "∀" else r"\exists"
        return r"%s %s,\ %s" % (quant, binder_head(head), body)


def binder_vars(tokens):
    """The variables bound by a binder, ignoring their type ascriptions."""
    names, depth, after_colon = [], 0, False
    for tok in tokens:
        if tok == "(":
            depth += 1
            after_colon = False
        elif tok == ")":
            depth -= 1
            after_colon = False
        elif tok == ":":
            after_colon = True
        elif tok in RESERVED:
            raise Unsupported(tok)
        elif not after_colon and re.fullmatch(r"[^\W\d][\w'₀-₉!?.]*|_", tok):
            names.append("x" if tok == "_" else ident_tex(tok))
    if not names:
        raise Unsupported("binder without variables")
    return ", ".join(names)


def binder_head(tokens):
    """The head of ∀/∃: plain variables, or a bounded form such as x ∈ S, ε > 0."""
    if any(t in ("∈", "∉", ">", "<", "≥", "≤", "⊆") for t in tokens):
        return Parser(tokens).expr(set())
    return binder_vars(tokens)


def render_app(head, args):
    kind, val = head
    argtex = [a[1] if a[0] != "ident" else ident_tex(a[1]) for a in args]
    if kind == "ident":
        name = strip_ns(val)
        base, _, suffix = name.rpartition(".")
        if base and suffix in SUFFIX_PREDICATES and not args:
            return T(r"$%s$ %s" % (ident_tex(base), SUFFIX_PREDICATES[suffix]))
        if name in SPECIAL:
            out = SPECIAL[name](argtex)
            if out is not None:
                return out
        htex = ident_tex(val)
        if not args:
            return htex
        if len(val) == 1 and argtex[0] == r"\varepsilon":      # u ε x  ->  u_ε(x)
            rest = argtex[1:]
            return htex + r"_{\varepsilon}" + ("(" + ", ".join(rest) + ")" if rest else "")
        if len(strip_ns(val)) > 1 and htex.startswith(r"\mathrm{"):
            htex = r"\operatorname{" + htex[len(r"\mathrm{"):]
        return htex + "(" + ", ".join(argtex) + ")"
    if kind == "group":
        if not args:
            return "(" + val + ")" if needs_parens(val) else val
        return "(" + val + ")(" + ", ".join(argtex) + ")"
    if args:
        return val + "(" + ", ".join(argtex) + ")"
    return val


def paren(tex):
    return "(" + tex + ")" if needs_parens(tex) else tex


def needs_parens(tex):
    return any(op in tex for op in (" + ", " - ", r"\to", r"\wedge", r"\vee",
                                    r"\le", r"\ge", " < ", " > ", " = ", r"\mapsto"))


def to_tex(lean):
    """LaTeX for one Lean expression, or raise Unsupported."""
    p = Parser(tokenize(lean))
    out = p.expr(set())
    if p.peek() is not None:
        raise Unsupported(f"trailing {p.peek()!r}")
    return out


def split_conjunction(lean):
    """Split a Lean proposition at its top-level conjunctions.

    Notation the tokenizer does not know is left to the renderer, which shows
    it as Lean code, so the proposition is returned whole."""
    try:
        tokens = tokenize(lean)
    except Unsupported:
        return [lean]
    parts, depth, cur = [], 0, []
    for tok in tokens:
        if tok in ("(", "⟨", "{", "[", "⟪"):
            depth += 1
        elif tok in (")", "⟩", "}", "]", "⟫"):
            depth -= 1
        if tok == "∧" and depth == 0:
            parts.append(cur)
            cur = []
            continue
        if tok in BINDERS and depth == 0 and cur:
            cur.append(tok)                      # a binder swallows the rest
            depth = 10 ** 6
            continue
        cur.append(tok)
    parts.append(cur)
    return [" ".join(strip_outer(p)) for p in parts]


def strip_outer(tokens):
    """Remove parentheses that enclose a whole token list."""
    while len(tokens) >= 2 and tokens[0] == "(" and tokens[-1] == ")":
        depth = 0
        for i, tok in enumerate(tokens):
            depth += tok == "("
            depth -= tok == ")"
            if depth == 0 and i < len(tokens) - 1:
                return tokens
        tokens = tokens[1:-1]
    return tokens


# ---------------------------------------------------------------------------
# A whole statement
# ---------------------------------------------------------------------------

def math_or_code(lean):
    try:
        return "$" + to_tex(lean) + "$", True
    except (Unsupported, IndexError, RecursionError):
        return "<code>" + html.escape(lean) + "</code>", False


def is_universe(lean_type):
    """Types of types: Type, Type u, Type*, Sort u."""
    return re.fullmatch(r"(Type|Sort)(\s+\S+|\*)?", lean_type.strip()) is not None


def type_clause(names, lean_type):
    """`p ε : ℝ` -> $p, ε \\in ℝ$;  `Ω : Set E` -> $Ω \\subseteq E$;  `u : E → ℝ` -> $u \\colon E \\to ℝ$."""
    vs = ", ".join(ident_tex(n) for n in names)
    if is_universe(lean_type):
        return ("$%s$ be types" if len(names) > 1 else "$%s$ be a type") % vs, True
    try:
        if lean_type.startswith("Set "):
            return "$%s \\subseteq %s$" % (vs, to_tex(lean_type[4:])), True
        tt = to_tex(lean_type)
        if "→" in lean_type:
            return "$%s \\colon %s$" % (vs, tt), True
        return "$%s \\in %s$" % (vs, tt), True
    except (Unsupported, IndexError, RecursionError):
        return "<code>" + html.escape(", ".join(names) + " : " + lean_type) + "</code>", False


def render_statement(st):
    """HTML for one exported declaration. Returns (html, fully_typeset)."""
    ok = True
    params, hyps = [], []
    group, group_type = [], None
    for b in st["binders"]:
        if b["prop"] or b["kind"] == "instance":
            if group:
                params.append(type_clause(group, group_type))
                group = []
            h, good = math_or_code(b["type"])
            ok &= good
            label = "" if b["kind"] == "instance" or b["name"].startswith("inst") \
                else ' <span class="fs-h">' + html.escape(b["name"]) + "</span>"
            hyps.append(h + label)
        else:
            if group and b["type"] != group_type:
                params.append(type_clause(group, group_type))
                group = []
            group.append(b["name"])
            group_type = b["type"]
    if group:
        params.append(type_clause(group, group_type))
    for _, good in params:
        ok &= good
    out = []
    if params:
        out.append("<p>Let " + ", ".join(p for p, _ in params) + ".</p>")
    if hyps:
        out.append("<p>Assume</p><ul>" + "".join("<li>" + h + "</li>" for h in hyps) + "</ul>")
    concl = st["conclusion"]
    if st.get("conclusionProp", True):
        lead = "Then" if hyps else ("Then" if params else "")
        m = re.match(r"∃\s+([^,]+),\s*(.*)$", concl, re.S)
        parts = split_conjunction(m.group(2) if m else concl)
        if m:
            try:
                head = binder_head(tokenize(m.group(1)))
                intro = "there exists $" + head + "$ such that"
            except (Unsupported, IndexError):
                intro, parts, m = None, split_conjunction(concl), None
        if len(parts) > 1 or m:
            items = []
            for part in parts:
                h, good = math_or_code(part)
                ok &= good
                items.append("<li>" + h + "</li>")
            out.append("<p>" + (lead + " " if lead else "") + (intro if m else "")
                       + ("" if m else ("all of the following hold" if lead else "All of the following hold"))
                       + ":</p><ul>" + "".join(items) + "</ul>")
        else:
            h, good = math_or_code(concl)
            ok &= good
            out.append("<p>" + (lead + " " if lead else "") + h + ".</p>")
    elif st.get("declKind") == "structure" and concl.strip() == "Prop":
        out.append("<p>This defines a property of these parameters.</p>")
    else:
        h, good = math_or_code(concl)
        ok &= good
        out.append("<p>Its value lies in " + h + ".</p>")
    return "".join(out), ok


# ---------------------------------------------------------------------------
# LaTeX output, for the blueprint PDF
# ---------------------------------------------------------------------------

UNICODE_TEX = {
    "ℝ": r"\ensuremath{\mathbb{R}}", "ℕ": r"\ensuremath{\mathbb{N}}",
    "→": r"\ensuremath{\to}", "↔": r"\ensuremath{\leftrightarrow}",
    "∀": r"\ensuremath{\forall}", "∃": r"\ensuremath{\exists}",
    "∈": r"\ensuremath{\in}", "∉": r"\ensuremath{\notin}",
    "≤": r"\ensuremath{\le}", "≥": r"\ensuremath{\ge}", "≠": r"\ensuremath{\ne}",
    "∧": r"\ensuremath{\wedge}", "∨": r"\ensuremath{\vee}", "¬": r"\ensuremath{\neg}",
    "‖": r"\ensuremath{\Vert}", "⨍": r"\ensuremath{\fint}", "∫": r"\ensuremath{\int}",
    "↑": r"\ensuremath{\uparrow}", "⟪": r"\ensuremath{\langle\!\langle}",
    "⟫": r"\ensuremath{\rangle\!\rangle}", "⟨": r"\ensuremath{\langle}",
    "⟩": r"\ensuremath{\rangle}", "•": r"\ensuremath{\bullet}", "∘": r"\ensuremath{\circ}",
    "×": r"\ensuremath{\times}", "⊆": r"\ensuremath{\subseteq}", "∩": r"\ensuremath{\cap}",
    "∪": r"\ensuremath{\cup}", "∞": r"\ensuremath{\infty}", "ᶠ": r"\textsuperscript{f}",
    "𝓝": r"\ensuremath{\mathcal{N}}", "⁻": r"\ensuremath{^{-}}", "¹": r"\ensuremath{^{1}}",
    "✝": r"\ensuremath{\dagger}", "∂": r"\ensuremath{\partial}", "⦃": r"\{", "⦄": r"\}",
}
UNICODE_TEX.update({k: r"\ensuremath{" + v + "}" for k, v in GREEK.items()})
UNICODE_TEX.update({chr(0x2080 + i): r"\textsubscript{%d}" % i for i in range(10)})
TEX_SPECIAL = {"\\": r"\textbackslash{}", "{": r"\{", "}": r"\}", "_": r"\_",
               "^": r"\^{}", "%": r"\%", "&": r"\&", "#": r"\#", "$": r"\$",
               "~": r"\~{}"}


def tex_escape(s):
    """Lean source as LaTeX text, for \\texttt."""
    out = []
    for ch in s:
        if ch in TEX_SPECIAL:
            out.append(TEX_SPECIAL[ch])
        elif ord(ch) < 128:
            out.append(ch)
        else:
            out.append(UNICODE_TEX.get(ch, "?"))
    return "".join(out)


def ascii_only(tex):
    return all(ord(c) < 128 for c in tex)


def math_or_code_tex(lean):
    try:
        tex = to_tex(lean)
        if not ascii_only(tex):            # e.g. a symbol missing from the tables
            raise Unsupported("non-ASCII character in formula")
        return "$" + tex + "$", True
    except (Unsupported, IndexError, RecursionError):
        return r"\texttt{" + tex_escape(lean) + "}", False


def type_clause_tex(names, lean_type):
    vs = ", ".join(ident_tex(n) for n in names)
    if is_universe(lean_type):
        return ("$%s$ be types" if len(names) > 1 else "$%s$ be a type") % vs, ascii_only(vs)
    try:
        if not ascii_only(vs):
            raise Unsupported("non-ASCII variable")
        if lean_type.startswith("Set "):
            return "$%s \\subseteq %s$" % (vs, to_tex(lean_type[4:])), True
        tt = to_tex(lean_type)
        if not ascii_only(tt):
            raise Unsupported("non-ASCII character in formula")
        if "→" in lean_type:
            return "$%s \\colon %s$" % (vs, tt), True
        return "$%s \\in %s$" % (vs, tt), True
    except (Unsupported, IndexError, RecursionError):
        return r"\texttt{" + tex_escape(", ".join(names) + " : " + lean_type) + "}", False


def render_statement_tex(st):
    """LaTeX for one exported declaration. Returns (latex, fully_typeset)."""
    ok = True
    params, hyps = [], []
    group, group_type = [], None
    for b in st["binders"]:
        if b["prop"] or b["kind"] == "instance":
            if group:
                params.append(type_clause_tex(group, group_type))
                group = []
            h, good = math_or_code_tex(b["type"])
            ok &= good
            if not (b["kind"] == "instance" or b["name"].startswith("inst")):
                h += r" \quad{\footnotesize\texttt{" + tex_escape(b["name"]) + "}}"
            hyps.append(h)
        else:
            if group and b["type"] != group_type:
                params.append(type_clause_tex(group, group_type))
                group = []
            group.append(b["name"])
            group_type = b["type"]
    if group:
        params.append(type_clause_tex(group, group_type))
    for _, good in params:
        ok &= good
    out = []
    if params:
        out.append("Let " + ", ".join(p for p, _ in params) + ".\n")
    if hyps:
        out.append("Assume\n\\begin{itemize}\n" + "".join("  \\item " + h + "\n" for h in hyps)
                   + "\\end{itemize}\n")
    concl = st["conclusion"]
    lead = "Then " if (hyps or params) else ""
    if st.get("conclusionProp", True):
        m = re.match(r"∃\s+([^,]+),\s*(.*)$", concl, re.S)
        intro = None
        if m:
            try:
                intro = "there exists $" + binder_head(tokenize(m.group(1))) + "$ such that"
                parts = split_conjunction(m.group(2))
            except (Unsupported, IndexError):
                m, parts = None, split_conjunction(concl)
        else:
            parts = split_conjunction(concl)
        if len(parts) > 1 or m:
            items = []
            for part in parts:
                h, good = math_or_code_tex(part)
                ok &= good
                items.append("  \\item " + h + "\n")
            head = intro if m else "all of the following hold"
            out.append((lead + head if lead else head[0].upper() + head[1:]) + ":\n"
                       + "\\begin{itemize}\n" + "".join(items) + "\\end{itemize}\n")
        else:
            h, good = math_or_code_tex(concl)
            ok &= good
            out.append(lead + h + ".\n")
    elif st.get("declKind") == "structure" and concl.strip() == "Prop":
        out.append("This defines a property of these parameters.\n")
    else:
        h, good = math_or_code_tex(concl)
        ok &= good
        out.append("Its value lies in " + h + ".\n")
    return "".join(out), ok
