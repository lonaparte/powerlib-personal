import theorem.TMIO.KnowledgeKind

/-! # Queries over attributed theorems and connections

Scope.
* Lean-only queries for the five knowledge classes `T`, `M`, `T-M`, `M-I`, and `I-O`, read from
  explicit `@[tmio ...]` attributes. No class is inferred
  from declaration names, namespaces, proposition keywords, or endpoint type roles.
* Queries cover only the theorem modules imported in the current environment. `#tmio_edges`
  requires every authored public typed connection theorem to be classified. `#tmio_theorems`
  lists all explicitly classified authored theorems, including ordinary and private proofs;
  unclassified ordinary theorems are outside that query.
* `#tmio_check` delegates classification and connection-coverage checks to `auditEnvironment`;
  it does not substitute for importing and checking the whole library.

Source: the five-class `tmio` attribute and environment audit in
`theorem/TMIO/KnowledgeKind.lean`; the per-declaration knowledge classes in `Layers.md`.

Results.
* `indexSummary`, `indexListing`: counts and module-grouped listings of public connections.
* `theoremSummary`, `theoremListing`: counts and listings of all explicitly classified authored
  theorems. Private names are shown in their source form and marked `[private]`.
* `#tmio_edges`: counts for all five classes; `#tmio_edges T`, `M`, `TM`, `MI`, or `IO` lists one
  class. The output identifies the current imported environment as the scope of the query.
* `#tmio_theorems` with the same optional class argument: all explicitly classified authored
  theorems, including ordinary and private declarations.
* `#tmio_check`: classification audit and public typed connection coverage check.
-/

namespace powerlib.Knowledge

open Lean Elab Command

private def listingKinds : Array Kind := #[.T, .M, .TM, .MI, .IO]

private def parseKind? (name : Name) : Option Kind :=
  if name == `T then some .T
  else if name == `M then some .M
  else if name == `TM then some .TM
  else if name == `MI then some .MI
  else if name == `IO then some .IO
  else none

private def moduleCount (entries : Array Entry) : Nat :=
  (entries.foldl (fun (modules : Array Name) entry =>
    if modules.contains entry.module then modules else modules.push entry.module) #[]).size

private def environmentNotice : String :=
  "Scope: authored public typed connection theorems in the currently imported theorem modules. " ++
  "Unimported modules are not included."

/-- Attribute counts for the currently imported connection theorems. -/
def indexSummary (entries : Array Entry) : String := Id.run do
  let mut lines := #[s!"Imported connection index: {entries.size} entries in {moduleCount entries} modules."]
  for kind in listingKinds do
    let count := (entries.filter (·.kind == kind)).size
    lines := lines.push s!"  {kind.label}: {count}"
  lines := lines.push "List a class with #tmio_edges T, M, TM, MI, or IO."
  lines := lines.push environmentNotice
  return "\n".intercalate lines.toList

/-- One attributed class, sorted by source module and declaration name. -/
def indexListing (entries : Array Entry) (kind : Kind) : String := Id.run do
  let selected := (entries.filter (·.kind == kind)).qsort fun a b =>
    a.module.toString < b.module.toString ||
      (a.module == b.module && a.name.toString < b.name.toString)
  let mut lines := #[s!"Imported connection index [{kind.label}]: {selected.size} entries in " ++
    s!"{moduleCount selected} modules."]
  let mut currentModule : Name := .anonymous
  for entry in selected do
    if entry.module != currentModule then
      currentModule := entry.module
      lines := lines.push s!"{entry.module}:"
    lines := lines.push s!"  {entry.name}"
  lines := lines.push environmentNotice
  return "\n".intercalate lines.toList

private def classifiedNotice : String :=
  "Scope: explicitly tmio-classified authored theorems, public and private, in the currently " ++
  "imported theorem modules. Unclassified ordinary theorems and unimported modules are not included."

private def displayTheoremName (entry : Entry) : String :=
  if isPrivateName entry.name then s!"{privateToUserName entry.name} [private]"
  else entry.name.toString

/-- Counts of all explicitly classified imported authored theorems, including private proofs. -/
def theoremSummary (entries : Array Entry) : String := Id.run do
  let privateCount := (entries.filter (isPrivateName ·.name)).size
  let mut lines := #[s!"Imported classified theorem index: {entries.size} entries " ++
    s!"({entries.size - privateCount} public, {privateCount} private) in {moduleCount entries} modules."]
  for kind in listingKinds do
    let count := (entries.filter (·.kind == kind)).size
    lines := lines.push s!"  {kind.label}: {count}"
  lines := lines.push "List a class with #tmio_theorems T, M, TM, MI, or IO."
  lines := lines.push classifiedNotice
  return "\n".intercalate lines.toList

/-- All explicitly classified theorems of one class, showing source names for private proofs. -/
def theoremListing (entries : Array Entry) (kind : Kind) : String := Id.run do
  let selected := (entries.filter (·.kind == kind)).qsort fun a b =>
    a.module.toString < b.module.toString ||
      (a.module == b.module && displayTheoremName a < displayTheoremName b)
  let mut lines := #[s!"Imported classified theorem index [{kind.label}]: " ++
    s!"{selected.size} entries in {moduleCount selected} modules."]
  let mut currentModule : Name := .anonymous
  for entry in selected do
    if entry.module != currentModule then
      currentModule := entry.module
      lines := lines.push s!"{entry.module}:"
    lines := lines.push s!"  {displayTheoremName entry}"
  lines := lines.push classifiedNotice
  return "\n".intercalate lines.toList

syntax (name := tmioEdges) "#tmio_edges" (ppSpace ident)? : command

elab_rules : command
  | `(#tmio_edges $[$kind:ident]?) => do
    let entries ← entriesInEnvironment
    match kind with
    | none => logInfo (indexSummary entries)
    | some stx =>
      let some selected := parseKind? stx.getId |
        throwErrorAt stx "Unknown knowledge class '{stx.getId}'; expected T, M, TM, MI, or IO"
      logInfo (indexListing entries selected)

syntax (name := tmioTheorems) "#tmio_theorems" (ppSpace ident)? : command

elab_rules : command
  | `(#tmio_theorems $[$kind:ident]?) => do
    let entries ← classifiedEntriesInEnvironment
    match kind with
    | none => logInfo (theoremSummary entries)
    | some stx =>
      let some selected := parseKind? stx.getId |
        throwErrorAt stx "Unknown knowledge class '{stx.getId}'; expected T, M, TM, MI, or IO"
      logInfo (theoremListing entries selected)

syntax (name := tmioCheck) "#tmio_check" : command

elab_rules : command
  | `(#tmio_check) => do
    auditEnvironment

end powerlib.Knowledge
