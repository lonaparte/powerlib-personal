import powerlib

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut state : Lean.CollectAxioms.State := {}
  for (root, _) in env.constants do
    if root.getRoot == `powerlib then
      let (_, next) := ((Lean.CollectAxioms.collect root).run env).run state
      state := next
  for ax in state.axioms do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "Unexpected axiom {ax}"
  logInfo "POWERLIB_KERNEL_OK"
