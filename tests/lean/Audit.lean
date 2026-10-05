import powerlib

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut roots := powerlib.Registry.theoremNames env
  -- Public definitions support model semantics even without theorem attributes.
  for (root, info) in env.constants do
    if root.getRoot == `powerlib && !info.isUnsafe then
      roots := roots.push root
  -- Registered declarations outside the namespace remain admission roots.
  for root in (roots.qsort Name.quickLt).toList.eraseDups do
    for axiomName in powerlib.Search.declarationAxioms env root do
      unless powerlib.Search.allowedAxiom axiomName do
        throwError "Unexpected axiom {axiomName} in {root}"
  logInfo "POWERLIB_KERNEL_OK"
