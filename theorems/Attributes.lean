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
  theoremKinds.getValue env name

def theoremNames (env : Environment) (kind : Option TheoremKind := none) : Array Name :=
  let names := env.constants.fold (fun names name _ =>
    match kindOf? env name with
    | none => names
    | some actual =>
      if kind.isNone || kind == some actual then names.push name else names) #[]
  names.qsort Name.quickLt

end powerlib.Registry
