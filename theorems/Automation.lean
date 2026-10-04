import theorems.RLStability
import theorems.AutomationRules

/-! Register every public theorem in the PowerLib namespace, including imported
model-conversion theorems.  New theorem modules must be imported above this point.
`powerlib_auto` is proof search, not an oracle: failure never admits a goal. -/
-- Iff theorems are intentionally available as whole propositions too.
set_option aesop.warn.applyIff false

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants do
    if name.getRoot == `powerlib && info.isTheorem then
      elabCommand (← `(attribute [aesop unsafe 50% apply (rule_sets := [PowerLib])]
        $(mkIdent name)))

macro "powerlib_auto" : tactic => `(tactic| aesop (rule_sets := [PowerLib]))
