import Plaplacian

/-!
# Export the statements of the blueprint's declarations

For every declaration listed in `docs/blueprint/site/lean_names.txt` (written by
`build.py`), this program reads the declaration's type from the Lean
environment, splits it into its parameters, its hypotheses and its conclusion,
and pretty-prints each part with Lean's own pretty-printer. The result is
written to `docs/blueprint/site/statements.json`, from which `build.py`
typesets the formal statements on the website.

Run from the repository root, after `lake build`:

    python3 docs/blueprint/site/build.py        # writes lean_names.txt
    lake env lean docs/blueprint/site/ExportStatements.lean
    python3 docs/blueprint/site/build.py        # uses statements.json
-/

open Lean Meta

/-- How a binder is written: `(x : α)`, `{x : α}` or `[C α]`. -/
private def binderKind : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "implicit"
  | .instImplicit => "instance"

/-- What kind of declaration a constant is. -/
private def declKind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .inductInfo _ => "structure"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "definition"
  | _ => "other"

/-- Pretty-print an expression on a single line. -/
private def pp (e : Expr) : MetaM String := do
  return (← ppExpr e).pretty 100000

private def exportDecl (n : Name) : MetaM Json := do
  match (← getEnv).find? n with
  | none =>
      return Json.mkObj [("name", Json.str n.toString), ("missing", Json.bool true)]
  | some ci =>
      forallTelescope ci.type fun xs body => do
        let mut binders : Array Json := #[]
        for x in xs do
          let decl ← x.fvarId!.getDecl
          binders := binders.push <| Json.mkObj
            [("name", Json.str decl.userName.toString),
             ("kind", Json.str (binderKind decl.binderInfo)),
             ("type", Json.str (← pp decl.type)),
             ("prop", Json.bool (← isProp decl.type))]
        return Json.mkObj
          [("name", Json.str n.toString),
           ("declKind", Json.str (declKind ci)),
           ("binders", Json.arr binders),
           ("conclusion", Json.str (← pp body)),
           ("conclusionProp", Json.bool (← isProp body))]

#eval show MetaM Unit from do
  let file := "docs/blueprint/site/lean_names.txt"
  let names := ((← IO.FS.readFile file).splitOn "\n").filter (fun s => !s.trim.isEmpty)
  let mut out : Array Json := #[]
  for s in names do
    out := out.push (← exportDecl s.trim.toName)
  IO.FS.writeFile "docs/blueprint/site/statements.json" (Json.arr out).pretty
  IO.println s!"Exported {out.size} statements to docs/blueprint/site/statements.json"
