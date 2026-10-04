import powerlib

-- Export types only. A separate Lean process re-proves and audits each one.
-- No theorem body, proof, or suggested theorem name is supplied to the tactic.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  IO.println "POWERLIB_EXPORT_BEGIN"
  IO.println "import powerlib\nopen scoped Topology\n"
  for (name, info) in env.constants do
    if name.getRoot == `powerlib && info.isTheorem then
      let type ← liftTermElabM <| PrettyPrinter.ppExpr info.type
      IO.println s!"-- Source: {name}\ntheorem AutomationCheck.reuse_{count} : {type.pretty} := by powerlib_auto\n"
      count := count + 1
  IO.println s!"-- POWERLIB_THEOREM_COUNT {count}"
  IO.println "POWERLIB_EXPORT_END"
