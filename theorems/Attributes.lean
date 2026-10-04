import Lean

namespace powerlib.Registry
open Lean

inductive TheoremKind where
  | foundation
  | domain
  deriving BEq, Inhabited, Repr

def TheoremKind.label : TheoremKind → String
  | .foundation => "foundation"
  | .domain => "domain"

initialize theoremKinds : EnumAttributes TheoremKind ← do
  -- Use Lean's native metadata persistence and asynchronous declaration lookup.
  -- The validator closes over the registry only after it has been initialized.
  let registry ← IO.mkRef (none : Option (EnumAttributes TheoremKind))
  let attributes ← registerEnumAttributes
    [(`powerlib_foundation, "PowerLib foundation theorem", .foundation),
     (`powerlib_domain, "PowerLib domain theorem", .domain)]
    (fun name kind => do
      match (← getConstInfo name) with
      | .thmInfo _ => pure ()
      | _ => throwError "PowerLib theorem attributes require a theorem: {name}"
      if let some attributes ← registry.get then
        if let some previous := attributes.getValue (← getEnv) name then
          unless previous == kind do
            throwError "PowerLib theorem {name} is already classified as {previous.label}")
  registry.set (some attributes)
  pure attributes

-- Whole-registry queries belong at command boundaries, outside a pending proof.
def kindOf? (env : Environment) (name : Name) : Option TheoremKind :=
  -- Join current-file attribute updates as well as reading imported metadata.
  ((theoremKinds.ext.getState env (asyncMode := .sync)).find? name).orElse
    (fun _ => theoremKinds.getValue env name)

def theoremNames (env : Environment) (kind : Option TheoremKind := none) : Array Name := Id.run do
  let mut entries := theoremKinds.ext.getState env (asyncMode := .sync)
  for modIdx in [:env.header.moduleNames.size] do
    for (name, actual) in theoremKinds.ext.getModuleEntries env modIdx do
      entries := entries.insert name actual
  let mut names : Array Name := #[]
  for (name, actual) in entries.toList do
    if kind.isNone || kind == some actual then
      names := names.push name
  return names.qsort Name.quickLt

end powerlib.Registry
