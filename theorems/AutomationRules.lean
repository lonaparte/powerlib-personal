import Mathlib.Tactic

-- Aesop rule sets become available to modules importing this declaration.
declare_aesop_rule_sets [PowerLib]

-- Cache theorem names when the library is imported. Enumerating all constants
-- from inside an in-progress theorem can wait on that theorem's own async task.
initialize powerlibTheoremNames : Lean.SimplePersistentEnvExtension Lean.Name (Array Lean.Name) ←
  Lean.registerSimplePersistentEnvExtension {
    addEntryFn := fun names name => names.push name
    addImportedFn := fun arrays => arrays.foldl (fun names more => names ++ more) #[]
  }
