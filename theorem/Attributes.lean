import Lean

/-! # Theorem classification registry (foundation)

The two PowerLib theorem classifications, `foundation` and `domain`, and the audit that a
source-authored theorem of a first-party module carries exactly one of them. Classification is
optional search metadata, never an admission exemption.

Scope.
* Lean meta-programming, no mathematics: the attributes `powerlib_foundation` and
  `powerlib_domain`, persisted by Lean's enum attributes; a theorem is classified once (a second,
  different classification is an error), and only theorems can be classified.
* A theorem whose statement is a typed `TMIO.Statement` (a connection statement) is a `domain`
  theorem without either attribute.
* Source ownership: first-party modules are those rooted at `theorem`, `dependencies`, `example`
  and `powerlib`, plus sources of an isolated integration profile under
  `dependencies/integrations`; imported upstream declarations and downstream modules are not
  relabeled.

Source: Lean's `EnumAttributes` and `ModuleLinter` interfaces; the library rules (`Rules.md` §3,
foundation and domain results). The admission audit (`theorem/Architecture.lean`) reads the
registry through `kindOf?`, `isFirstPartyModule`, `isIntegrationSource` and `authoredTheorems`.

Results.
* `TheoremKind` (`foundation`, `domain`), `TheoremKind.label`, the attribute registry
  `theoremKinds`.
* Queries: `kindOf?` (the classification of a declaration), `theoremNames` (every classified
  theorem, optionally of one kind, including the unannotated connection statements).
* Source ownership: `isFirstPartyModule`, `isIntegrationSource`.
* Authored theorems: `authoredTheorems` (the theorems of the current module authored in a list of
  commands, matched by name and selection range, without generated auxiliaries),
  `auditAuthoredTheorems` (each needs exactly one classification), and the module linter
  `classificationLinter` running that audit on first-party sources.
-/

namespace powerlib.Registry
open Lean

inductive TheoremKind where
  | foundation
  | domain
  deriving BEq, Inhabited, Repr

def TheoremKind.label : TheoremKind → String
  | .foundation => "foundation"
  | .domain => "domain"

private def lookupKind? (attributes : EnumAttributes TheoremKind)
    (env : Environment) (name : Name) : Option TheoremKind :=
  -- After-typechecking updates may be newer than a declaration's async snapshot.
  -- A local map lookup sees those updates without joining unfinished proofs.
  ((attributes.ext.getState env (asyncMode := .local)).find? name).orElse
    (fun _ => attributes.getValue env name)

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
        if let some previous := lookupKind? attributes (← getEnv) name then
          unless previous == kind do
            throwError "PowerLib theorem {name} is already classified as {previous.label}")
  registry.set (some attributes)
  pure attributes

private partial def statementType (type : Expr) : Bool :=
  if type.getAppFn.isConstOf `powerlib.TMIO.Statement then true
  else match type with
    | .forallE _ _ body _ => statementType body
    | _ => false

def kindOf? (env : Environment) (name : Name) : Option TheoremKind :=
  if (env.find? name).any (fun info => statementType info.type) then some .domain
  else lookupKind? theoremKinds env name

-- Whole-registry queries belong at command boundaries, outside a pending proof.
def theoremNames (env : Environment) (kind : Option TheoremKind := none) : Array Name := Id.run do
  let mut entries := theoremKinds.ext.getState env (asyncMode := .sync)
  for modIdx in [:env.header.moduleNames.size] do
    for (name, actual) in theoremKinds.ext.getModuleEntries env modIdx do
      entries := entries.insert name actual
  let mut names : Array Name := #[]
  for (name, _) in entries.toList do
    if kind.isNone || kind == kindOf? env name then
      names := names.push name
  -- Typed public claims are discoverable without either metadata annotation.
  for (name, info) in env.constants do
    if let .thmInfo _ := info then
      if statementType info.type && (kind.isNone || kind == some .domain) &&
          !names.contains name then
        names := names.push name
  return names.qsort Name.quickLt

end powerlib.Registry


namespace powerlib.Registry
open Lean Elab Command

-- Source ownership follows the canonical first-party module directories.
-- Imported upstream declarations and downstream modules are not relabeled.
def isFirstPartyModule (moduleName : Name) : Bool :=
  #[`theorem, `dependencies, `example, `powerlib].contains moduleName.getRoot

-- An isolated integration profile may compile its entry point under a short
-- module name. Its actual source directory still establishes first-party scope.
def isIntegrationSource (path : System.FilePath) : Bool :=
  (path.components.zip path.components.tail).any fun (left, right) =>
    left == "dependencies" && right == "integrations"

private def isFirstPartySource : CommandElabM Bool := do
  if isFirstPartyModule (← getEnv).mainModule then
    return true
  try
    return isIntegrationSource (← IO.FS.realPath (← getFileName))
  catch _ =>
    return false

private partial def authoredDeclarationRefs (stx : Syntax) : Array Syntax := Id.run do
  if stx.isOfKind ``Parser.Command.declaration || stx.isOfKind `lemma then
    if stx[1].isOfKind ``Parser.Command.«example» then
      return #[]
    -- Stop at the declaration boundary, before proof bodies or syntax quotations.
    return #[Elab.getDeclarationSelectionRef stx[1]]
  let mut refs := #[]
  for child in stx.getArgs do
    refs := refs ++ authoredDeclarationRefs child
  return refs

-- Match original parsed name tokens to actual current-module theorem constants.
-- Generated ext/inj/eq declarations do not share both the authored name and its
-- exact selection range. Private declarations retain their user name for this
-- match. No declaration-name list or generated-suffix blacklist is involved.
def authoredTheorems (commands : Array Syntax) : CommandElabM (Array Name) := do
  let env ← getEnv
  let mut refs : Array (Name × DeclarationRange) := #[]
  for command in commands do
    for ref in authoredDeclarationRefs command do
      if ref.isIdent then
        if let some range ← Elab.getDeclarationRange? ref then
          refs := refs.push
            (ref.getId.eraseMacroScopes.replacePrefix rootNamespace .anonymous, range)
  let mut names := #[]
  -- Main-branch source ranges and immediate async constant kinds avoid joining
  -- env.checked while a command or its linter is still completing.
  let ranges := declRangeExt.getState env (asyncMode := .local)
  for (name, declarationRanges) in ranges.toList do
    if (env.findAsync? name (skipRealize := true)).any (·.kind == .thm) then
      if refs.any (fun (sourceName, range) =>
          sourceName.isSuffixOf (privateToUserName name).eraseMacroScopes &&
            decide (range = declarationRanges.selectionRange)) then
        names := names.push name
  return names.qsort Name.quickLt

-- This check runs at a module boundary, after later `attribute [...]` commands.
-- The enum registry enforces exactly one classification; simp/ext/Aesop remain
-- independent attributes and are neither required nor altered by this check.
def auditAuthoredTheorems (commands : Array Syntax) : CommandElabM Unit := do
  let env ← getEnv
  for name in ← authoredTheorems commands do
    unless (kindOf? env name).isSome do
      throwError m!"Source-authored theorem {privateToUserName name} requires exactly one " ++
        m!"PowerLib classification"

def classificationLinter : ModuleLinter where
  run commands := do
    if ← isFirstPartySource then
      auditAuthoredTheorems commands

-- Classification is optional search metadata, never an admission exemption.

end powerlib.Registry
