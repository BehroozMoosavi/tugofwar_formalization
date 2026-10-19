# Documentation

| Document | PDF | LaTeX source |
|---|---|---|
| **Article**: *A formally verified convergence theorem for the tug-of-war scheme of the normalized p-Laplacian* (10 pages) | [`article/plaplacian-article.pdf`](article/plaplacian-article.pdf) | [`article/plaplacian-article.tex`](article/plaplacian-article.tex) |
| **Technical companion**: the development layer by layer, with fifty-one findings (42 pages) | [`technical-companion.pdf`](technical-companion.pdf) | [`companion/plaplacian-paper.tex`](companion/plaplacian-paper.tex) |
| **Blueprint**: every definition and theorem with its Lean declarations and dependencies (23 pages) | [`blueprint/blueprint.pdf`](blueprint/blueprint.pdf) | [`blueprint/`](blueprint/) |

The dependency graph of the blueprint is also available on its own as
[`blueprint/graph.pdf`](blueprint/graph.pdf).

## Building the PDFs

Each document compiles with `pdflatex` (run it twice so that cross-references
resolve), or with `latexmk -pdf`:

```bash
cd docs/article   && latexmk -pdf plaplacian-article.tex
cd docs/companion && latexmk -pdf plaplacian-paper.tex
cd docs/blueprint && latexmk -pdf print.tex
```

The blueprint sources follow the layout of
[leanblueprint](https://github.com/PatrickMassot/leanblueprint):
`content.tex` holds the statements, with `\lean`, `\leanok` and `\uses`
annotations, and `macros/common.tex` the shared macros. `print.tex` builds the
PDF without the tool; `graph.dot` is the Graphviz source of the graph.
