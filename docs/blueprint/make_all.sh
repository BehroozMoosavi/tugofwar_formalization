#!/bin/sh
# Rebuild the blueprint website and the blueprint PDF, with every formal
# statement generated from the Lean code. Run from the repository root:
#     sh docs/blueprint/make_all.sh
set -e
echo "1/4  Listing the Lean declarations cited in the blueprint"
python3 docs/blueprint/site/build.py > /dev/null
echo "2/4  Exporting their statements from Lean (about a minute)"
sh docs/blueprint/site/export.sh
echo "3/4  Building the website and the blueprint LaTeX"
python3 docs/blueprint/site/build.py
echo "4/4  Compiling the blueprint PDF"
if command -v latexmk > /dev/null 2>&1; then
  (cd docs/blueprint && latexmk -pdf -interaction=nonstopmode -halt-on-error print.tex > /dev/null \
     && cp print.pdf blueprint.pdf && latexmk -c print.tex > /dev/null && rm -f print.pdf)
  echo "     docs/blueprint/blueprint.pdf updated"
else
  echo "     latexmk not found: install MacTeX, or compile docs/blueprint/print.tex"
  echo "     on Overleaf with content-formal.tex, macros/ and graph.pdf beside it."
fi
echo "Done. Website: _site/index.html   Blueprint: docs/blueprint/blueprint.pdf"
