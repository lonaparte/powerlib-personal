import powerlib

set_option pp.all true
set_option pp.maxSteps 1000000

-- Export public declarations, not generated theorem bodies or proof hints.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut entries : Array Json := #[]
  for name in powerlib.Registry.theoremNames env do
    let some entry := powerlib.Search.describe env name |
      throwError "Registered declaration is not a theorem: {name}"
    let some kind := entry.kind | throwError "Registered theorem lost its classification: {name}"
    unless entry.axioms.all powerlib.Search.allowedAxiom do
      throwError "Registered theorem has an unapproved axiom: {name}"
    let type ← liftTermElabM <| PrettyPrinter.ppExpr entry.type
    entries := entries.push (Json.mkObj [
      ("name", Json.str entry.name.toString),
      ("kind", Json.str kind.label),
      ("module", Json.str entry.moduleName.toString),
      ("universes", toJson (entry.levelParams.map toString)),
      ("type", Json.str type.pretty),
      ("axioms", toJson (entry.axioms.map toString))])
  if entries.isEmpty then throwError "The public theorem registry is empty"
  IO.println "POWERLIB_REGISTRY_BEGIN"
  IO.println (Json.mkObj [
    ("schema", Json.str "powerlib.theorem-registry/v1"),
    ("theorems", Json.arr entries)]).compress
  IO.println "POWERLIB_REGISTRY_END"
