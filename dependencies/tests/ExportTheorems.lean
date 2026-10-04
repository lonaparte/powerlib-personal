import powerlib

set_option pp.all true
set_option pp.maxSteps 1000000

-- Export types only. A separate Lean process re-proves and audits each one.
-- No theorem body, proof, or suggested theorem name is supplied to the tactic.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  let mut pairs : Array String := #[]
  IO.println "POWERLIB_EXPORT_BEGIN"
  IO.println "import powerlib\nset_option autoImplicit false\nopen scoped Topology\n"
  for (name, info) in env.constants do
    if name.getRoot == `powerlib && info.isTheorem then
      let type ← liftTermElabM <| PrettyPrinter.ppExpr info.type
      IO.println s!"-- Source: {name}\ntheorem AutomationCheck.reuse_{count} : {type.pretty} := by powerlib_auto\n"
      pairs := pairs.push s!"(`{name}, `AutomationCheck.reuse_{count})"
      count := count + 1
  IO.println "open Lean Elab Command in\nrun_cmd do"
  IO.println s!"  for (source, consumer) in [{String.intercalate ", " pairs.toList}] do"
  IO.println "    let original ← getConstInfo source\n    let tested ← getConstInfo consumer"
  IO.println "    unless (← liftTermElabM <| Meta.isDefEq original.type tested.type) do"
  IO.println "      throwError \"Automatic consumer changed theorem type: {source}\""
  IO.println s!"-- POWERLIB_THEOREM_COUNT {count}"
  IO.println "POWERLIB_EXPORT_END"
