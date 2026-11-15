#!/bin/sh
# Export the statements of the declarations listed in lean_names.txt.
# The export script is kept as ExportStatements.lean.txt, so that every .lean
# file in the repository belongs to the library (as Palomar requires); it is
# copied under .lake/, which Palomar ignores, and run from the repository root.
set -e
mkdir -p .lake
cp docs/blueprint/site/ExportStatements.lean.txt .lake/ExportStatements.lean
lake env lean .lake/ExportStatements.lean
