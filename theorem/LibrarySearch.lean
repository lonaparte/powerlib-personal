import theorem.Attributes
import Lean.Meta.Tactic.LibrarySearch
import Lean.Util.CollectAxioms

/-! # Library search with an axiom audit (foundation)

Goal-directed reuse of imported declarations. The index is Lean's library
search index; upstream libraries need no PowerLib attributes or namespace.
Model equivalences remain explicit theorem premises, checked by Lean.

Scope.
* Lean meta-programming, no mathematics. A candidate is a theorem of the library search index
  whose axioms are only `propext`, `Classical.choice` and `Quot.sound`; a proof assembled by the
  search (the candidate applied, its remaining goals closed by `solveByElim`) is audited
  against the same allowlist before it is accepted.
* The axiom audit is shared with whole-package admission (`theorem/Architecture.lean`), which runs
  `axiomViolation?` on the declarations of every built module.

Source: Lean's library search (`Lean.Meta.Tactic.LibrarySearch`) and axiom collector
(`Lean.Util.CollectAxioms`); the classification registry of `theorem/Attributes.lean`.

Results.
* Entries: `TheoremEntry`, `describe` (module, universe parameters, statement, classification and
  axioms of a theorem), `allowedAxiom`, `declarationAxioms`, `eligible`.
* `axiomViolation?`: a root of a batch whose transitive type and value dependencies reach an axiom
  outside the allowlist, with that axiom.
* Search: `candidates` (the library search candidates restricted to eligible theorems),
  `checkProof`, `solve`, and the tactic `powerlib_search`.
-/
namespace powerlib.Search
open Lean Meta

structure TheoremEntry where
  name : Name
  moduleName : Name
  levelParams : List Name
  type : Expr
  kind : Option Registry.TheoremKind
  axioms : Array Name

def allowedAxiom (name : Name) : Bool :=
  name == `propext || name == `Classical.choice || name == `Quot.sound

def declarationAxioms (env : Environment) (name : Name) : Array Name :=
  -- Use Lean's public collector; its internal state differs between pinned versions.
  let _ : MonadEnv (StateM Environment) :=
    { getEnv := get, modifyEnv := modify }
  ((collectAxioms (m := StateM Environment) name).run env).1

-- For admission only the allowlist decision is needed, not a separate axiom
-- array for every root. Walk the union of their kernel dependencies once.
-- Keep provenance queries above on Lean's public CollectAxioms API.
private partial def axiomViolation (env : Environment) (checked : Kernel.Environment)
    (name : Name) :
    StateM (Std.HashSet Name) (Option Name) := do
  if (← get).contains name then return none
  modify (·.insert name)
  -- Imported declarations already have axiom metadata in pinned Lean. Preserve
  -- that constant-time boundary rather than rescanning their proof bodies.
  -- This also handles proved declarations exported as axioms by the module system.
  if (env.getModuleIdxFor? name).isSome then
    return (declarationAxioms env name).find? fun ax => !allowedAxiom ax
  let visitExpr (e : Expr) : StateM (Std.HashSet Name) (Option Name) := do
    for dependency in e.getUsedConstants do
      if let some ax ← axiomViolation env checked dependency then return some ax
    return none
  match checked.find? name with
  | some (.axiomInfo v) =>
    if !allowedAxiom name then return some name
    visitExpr v.type
  | some (.defnInfo v) =>
    if let some ax ← visitExpr v.type then return some ax
    visitExpr v.value
  | some (.thmInfo v) =>
    if let some ax ← visitExpr v.type then return some ax
    visitExpr v.value
  | some (.opaqueInfo v) =>
    if let some ax ← visitExpr v.type then return some ax
    visitExpr v.value
  | some (.ctorInfo v) => visitExpr v.type
  | some (.recInfo v) => visitExpr v.type
  | some (.inductInfo v) =>
    if let some ax ← visitExpr v.type then return some ax
    for ctor in v.ctors do
      if let some ax ← axiomViolation env checked ctor then return some ax
    return none
  | some (.quotInfo _) | none => return none

/-- Audit every root's transitive type and value dependencies against the same
allowlist as `declarationAxioms`. The visited set belongs to this fixed kernel
environment and this batch only; it is never reused after environment changes.
On failure, retain both the offending axiom and the root that reached it. -/
def axiomViolation? (env : Environment) (roots : Array Name) : Option (Name × Name) :=
  let checked := env.checked.get
  let audit : StateM (Std.HashSet Name) (Option (Name × Name)) := do
    for root in roots do
      if let some ax ← axiomViolation env checked root then return some (root, ax)
    return none
  audit.run' {}

def describe (env : Environment) (name : Name) : Option TheoremEntry := do
  let info ← env.find? name
  if !info.isTheorem || info.isUnsafe then none else
    let moduleName := match env.getModuleIdxFor? name with
      | some index => env.header.moduleNames[index]!
      | none => env.mainModule
    -- Read only this declaration's metadata while another proof is in progress.
    some ⟨name, moduleName, info.levelParams, info.type, Registry.kindOf? env name,
      declarationAxioms env name⟩

def eligible (env : Environment) (name : Name) : Bool :=
  match describe env name with
  | some entry => entry.axioms.all allowedAxiom
  | none => false

def candidates : LibrarySearch.CandidateFinder := fun goal => do
  let env ← getEnv
  return (← LibrarySearch.libSearchFindDecls goal).filter (fun (name, _) => eligible env name)

def checkProof (proof : Expr) : MetaM Unit := do
  let proof ← instantiateMVars proof
  if proof.hasMVar then throwError "Library search left unresolved proof metavariables"
  -- Retain used local let values and dependent binder types in the audit.
  -- Looking only at constants in an open term would miss their dependencies.
  let proof ← mkLambdaFVars (← getLCtx).getFVars proof (usedOnly := true)
  let env ← getEnv
  if let some (_, axiomName) := axiomViolation? env proof.getUsedConstants then
    throwError "Library search used an unapproved axiom: {axiomName}"

def solve (goal : MVarId) : MetaM Unit := do
  let found ← LibrarySearch.librarySearchSymm candidates goal
  let result ← LibrarySearch.tryOnEach (fun ((target, context), (name, direction)) => do
    setMCtx context
    let termProof ← LibrarySearch.mkLibrarySearchLemma name direction
    let pending ← target.apply termProof { allowSynthFailures := true }
    let remaining ← LibrarySearch.solveByElim [] false pending 6
    if remaining.isEmpty then checkProof (mkMVar goal)
    return remaining) found
  unless result.isNone do
    throwError "No kernel-admissible library theorem closed the goal"

end powerlib.Search

open Lean Elab Tactic in
elab "powerlib_search" : tactic =>
  liftMetaTactic fun goal => do
    powerlib.Search.solve goal
    return []
