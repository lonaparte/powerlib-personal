import Lean

namespace powerlib.Registry
open Lean

inductive TheoremKind where
  | foundation
  | domain
  deriving BEq, Inhabited, Repr

initialize theoremKinds : EnumAttributes TheoremKind ←
  registerEnumAttributes
    [(`powerlib_foundation, "PowerLib foundation theorem", .foundation),
     (`powerlib_domain, "PowerLib domain theorem", .domain)]
    (fun name _ => do
      match (← getConstInfo name) with
      | .thmInfo _ => pure ()
      | _ => throwError "PowerLib theorem attributes require a theorem: {name}")

def kindOf? (env : Environment) (name : Name) : Option TheoremKind :=
  -- Join current-file attribute updates as well as reading imported metadata.
  ((theoremKinds.ext.getState env (asyncMode := .sync)).find? name).orElse
    (fun _ => theoremKinds.getValue env name)

def theoremNames (env : Environment) (kind : Option TheoremKind := none) : Array Name := Id.run do
  let add := fun (names : Array Name) (name : Name) (actual : TheoremKind) =>
    if kind.isNone || kind == some actual then names.push name else names
  let mut names : Array Name := #[]
  for (name, actual) in (theoremKinds.ext.getState env (asyncMode := .sync)).toList do
    names := add names name actual
  for modIdx in [:env.header.moduleNames.size] do
    for (name, actual) in theoremKinds.ext.getModuleEntries env modIdx do
      names := add names name actual
  return names.qsort Name.quickLt

end powerlib.Registry
