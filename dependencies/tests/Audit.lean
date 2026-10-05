import powerlib

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut state : Lean.CollectAxioms.State := {}
  for (root, info) in env.constants do
    if root.getRoot == `powerlib && !info.isUnsafe then
      let (_, next) := ((Lean.CollectAxioms.collect root).run env).run state
      state := next

  let roots := ([] : List Name) ++ (powerlib.Registry.theoremNames env).toList
  for root in roots do
    unless (env.find? root).isSome do
      throwError "Missing audit root {root}"
    let (_, next) := ((Lean.CollectAxioms.collect root).run env).run state
    state := next
  for ax in state.axioms do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "Unexpected axiom {ax}"
  logInfo "POWERLIB_KERNEL_OK"
