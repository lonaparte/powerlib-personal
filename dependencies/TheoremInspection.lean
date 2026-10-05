import theorems.Attributes
import Lean.Meta.Tactic.LibrarySearch
import Lean.Util.CollectAxioms

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
  let (_, state) := ((CollectAxioms.collect name).run env).run {}
  state.axioms

def describe (env : Environment) (name : Name) : Option TheoremEntry := do
  let info ← env.find? name
  if !info.isTheorem || info.isUnsafe then none else
    let moduleName := match env.getModuleIdxFor? name with
      | some index => env.header.moduleNames[index]!
      | none => env.mainModule
    some ⟨name, moduleName, info.levelParams, info.type,
      Registry.theoremKinds.getValue env name, declarationAxioms env name⟩

def eligible (env : Environment) (name : Name) : Bool :=
  match describe env name with
  | some entry => entry.axioms.all allowedAxiom
  | none => false

def candidates : LibrarySearch.CandidateFinder := fun goal => do
  let env ← getEnv
  return (← LibrarySearch.libSearchFindDecls goal).filter
    (fun (name, _) => eligible env name)

end powerlib.Search
