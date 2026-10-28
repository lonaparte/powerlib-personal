import Lean

/-! # Five-category theorem attributes

Scope.
* Lean-only source attributes and admission checks. The five kinds are theory, model,
  theory–model, model–implementation and implementation–observation. This module does not
  infer a kind from declaration names, source paths or theorem syntax.
* `@[tmio T]`, `@[tmio M]`, `@[tmio TM]`, `@[tmio MI]` and `@[tmio IO]` attach one reviewed
  kind to a theorem. A second assignment, even of the same kind, is rejected. Ordinary
  mathematical theorems may carry attributes too; this audit covers typed connections only.
* Environment admission checks authored public theorems from imported `theorem.*` modules
  whose declared conclusion carries `powerlib.TMIO.Statement`. Private proofs, compiler
  auxiliaries and ordinary mathematical theorems are outside this connection coverage check.

Source: the five-category contract in `Layers.md`; the authored-declaration provenance and
typed-statement checks in `theorem/Architecture.lean`; Lean's `ParametricAttribute` interface.

Results.
* `Kind`, `Kind.label` and `theoremKinds`: the closed five-category schema and persistent
  `tmio` attribute; `kindOf?` reads local asynchronous updates and imported attributes.
* `Entry` and `entriesInEnvironment`: classified public typed connections actually imported,
  with declaration ownership read from Lean; missing attributes are errors.
* `auditEnvironment`: coverage admission for this imported environment. No separate catalog
  supplies names, kinds or a presumed total.
-/

namespace powerlib.Knowledge

open Lean Meta Elab Command

/-- The only five primary knowledge categories. -/
inductive Kind where
  | T
  | M
  | TM
  | MI
  | IO
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Labels used in theorem queries. -/
def Kind.label : Kind → String
  | .T => "T"
  | .M => "M"
  | .TM => "T-M"
  | .MI => "M-I"
  | .IO => "I-O"

/-- One queried primary classification and the module that authors the theorem. -/
structure Entry where
  name : Name
  module : Name
  kind : Kind
  deriving Repr, Inhabited

/-- One explicit primary classification on a theorem declaration. -/
syntax (name := tmio) "tmio" ident : attr

private def lookupKind? (attributes : ParametricAttribute Kind)
    (env : Environment) (name : Name) : Option Kind :=
  -- After-typechecking updates may be newer than a declaration's async snapshot.
  ((attributes.ext.getState env (asyncMode := .local)).2.find? name).orElse
    (fun _ => attributes.getParam? env name)

/-- The persistent attribute. All rejection checks run before the value is stored. -/
initialize theoremKinds : ParametricAttribute Kind ← do
  let registry ← IO.mkRef (none : Option (ParametricAttribute Kind))
  let attributes ← registerParametricAttribute {
    name := `tmio
    descr := "one reviewed knowledge category: T, M, TM, MI or IO"
    getParam := fun name stx => do
      let `(attr| tmio $kind:ident) := stx |
        throwError "Expected @[tmio T], @[tmio M], @[tmio TM], @[tmio MI] or @[tmio IO]"
      let value ← match kind.getId with
        | `T => pure Kind.T
        | `M => pure Kind.M
        | `TM => pure Kind.TM
        | `MI => pure Kind.MI
        | `IO => pure Kind.IO
        | _ => throwError "Unknown tmio kind {kind}; expected T, M, TM, MI or IO"
      match ← getConstInfo name with
      | .thmInfo _ => pure ()
      | _ => throwError "The tmio attribute requires a theorem: {name}"
      if let some attributes ← registry.get then
        if let some previous := lookupKind? attributes (← getEnv) name then
          throwError "Theorem {name} already has tmio {previous.label}; a second assignment is not allowed"
      return value
  }
  registry.set (some attributes)
  pure attributes

/-- Read one theorem's explicit kind, including current asynchronous and imported entries. -/
def kindOf? (env : Environment) (name : Name) : Option Kind :=
  lookupKind? theoremKinds env name

/-- Only source-authored public theorem declarations are connection admission subjects. -/
private def authoredPublic (env : Environment) (info : ConstantInfo) : Bool :=
  match info with
  | .thmInfo _ => !isPrivateName info.name && (declRangeExt.find? env info.name).isSome
  | _ => false

/-- Inspect the declared conclusion before unfolding the `Statement` marker itself.
Telescope parameters, lets and transparent aliases may precede that marker. The marker is a
literal name so attribute queries do not have to import its mathematical definition. -/
private partial def hasTypedStatement (type : Expr) (fuel : Nat := 64) : MetaM Bool := do
  if fuel == 0 then
    throwError "TMIO connection audit exhausted its alias-unfolding limit at conclusion {type}; classification coverage cannot be determined"
  if type.getAppFn.isConstOf `powerlib.TMIO.Statement then return true
  match type with
  | .forallE name domain body binderInfo =>
    withLocalDecl name binderInfo domain fun value =>
      hasTypedStatement (body.instantiate1 value) fuel
  | .letE _ _ value body _ => hasTypedStatement (body.instantiate1 value) fuel
  | .mdata _ body => hasTypedStatement body fuel
  | _ =>
    if let some unfolded ← unfoldDefinition? type then
      if unfolded != type then return ← hasTypedStatement unfolded (fuel - 1)
    return false

/-- Enumerate the actual imported authored public typed connection theorems.
The declaration owner comes from the imported module table, never from a namespace heuristic.
Missing classifications are errors; unrelated ordinary theorem attributes are not counted. -/
def entriesInEnvironment : CommandElabM (Array Entry) := do
  let env ← getEnv
  let mut entries : Array Entry := #[]
  for index in [:env.header.moduleNames.size] do
    let owner := env.header.moduleNames[index]!
    unless owner.getRoot == `theorem do continue
    for name in env.header.moduleData[index]!.constNames do
      let some info := env.find? name | continue
      unless authoredPublic env info do continue
      unless ← liftTermElabM (hasTypedStatement info.type) do continue
      let some kind := kindOf? env name |
        throwError "Imported public typed connection theorem lacks a tmio attribute: {name} in {owner}"
      entries := entries.push ⟨name, owner, kind⟩
  return entries.qsort (fun left right => Name.quickLt left.name right.name)

/-- Check coverage of all imported first-party public typed connection theorems.
The build calls this after importing its complete module inventory; standalone queries and
checks report only their current imported environment, without claiming whole-library coverage. -/
def auditEnvironment : CommandElabM Unit := do
  let entries ← entriesInEnvironment
  logInfo m!"POWERLIB_KNOWLEDGE_CHECK_OK: {entries.size} imported public typed connection theorems, each with one tmio attribute"

end powerlib.Knowledge
