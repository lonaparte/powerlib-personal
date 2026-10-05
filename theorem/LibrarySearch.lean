import theorem.Attributes
import Lean.Meta.Tactic.LibrarySearch
import Lean.Util.CollectAxioms

/-! Goal-directed reuse of imported declarations. The index is Lean's library
search index; upstream libraries need no PowerLib attributes or namespace.
Model equivalences remain explicit theorem premises, checked by Lean. -/
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
  for name in proof.getUsedConstants do
    for axiomName in declarationAxioms env name do
      unless allowedAxiom axiomName do
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
