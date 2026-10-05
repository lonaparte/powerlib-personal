import theorems.RLStability
import theorems.LCLSynthesis
import theorems.Dynamics.Models
import theorems.Dynamics.Nonlinear
import theorems.AutomationRules
import theorems.LibrarySearch

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
      modifyEnv (powerlibTheoremNames.addEntry · name)
      elabCommand (← `(attribute [aesop unsafe 50% apply (rule_sets := [PowerLib])]
        $(mkIdent name)))

-- Try a theorem application and its immediate premises before indexed search.
-- A shallow first pass preserves whole iff goals and prevents an expanding
-- theorem inventory from spending the heartbeat budget on blind deep search.
open Lean Elab Tactic in
elab "powerlib_auto" : tactic => do
  let env ← getEnv
  let mut rules : Array (TSyntax `term) := #[]
  for name in powerlibTheoremNames.getState env do
    rules := rules.push (← `(term| $(mkIdent name)))
  let saved ← saveState
  try
    liftMetaTactic fun goal => do
      let remaining ← SolveByElim.processSyntax { maxDepth := 2, exfalso := false }
        false false rules.toList [] #[] [goal]
      unless remaining.isEmpty do
        throwError "Short PowerLib proof search left unsolved goals"
      pure []
  catch _ =>
    saved.restore
    try
      evalTactic (← `(tactic| aesop (rule_sets := [PowerLib])))
      unless (← getGoals).isEmpty do
        throwError "Indexed PowerLib proof search left unsolved goals"
    catch _ =>
      saved.restore
      evalTactic (← `(tactic| powerlib_search))
