import theorem.Attributes

/-! # Source knowledge attribute checks

Scope.
* Lean-only checks for the five `tmio` values, immediate asynchronous queries, private helpers
  and delayed assignment. These ordinary test theorems are not typed connection coverage subjects.
* Rejection cases preserve the original classification: repeated assignment of either the
  same or another kind, standalone I/O values and non-theorem declarations are rejected.
* A single attribute block combines `tmio` and `powerlib_foundation` in either order.

Source: `theorem/TMIO/KnowledgeKind.lean`, `theorem/Attributes.lean` and the five-category
contract in `Layers.md`.

Results.
* All five source attributes and an attributed private helper are observable through `kindOf?`
  in the current module; ordinary unclassified theorems do not acquire a kind.
* Expected diagnostics check the attribute's type, value and uniqueness boundaries.
* Combined attribute blocks update both independent registries in either order.
* The final query checks that rejected assignments neither replace nor add classifications.
-/

namespace KnowledgeAttributeCases

open Lean Elab Command powerlib.Knowledge

@[tmio T] theorem theory : True := True.intro
@[tmio M] theorem model : True := True.intro
@[tmio TM] theorem theoryModel : True := True.intro
@[tmio MI] theorem modelImplementation : True := True.intro
@[tmio IO] theorem implementationObservation : True := True.intro
@[tmio T] private theorem privateTheory : True := True.intro
@[tmio T, powerlib_foundation] theorem combinedTheory : True := True.intro
@[powerlib_foundation, tmio M] theorem combinedModel : True := True.intro

run_cmd do
  let env ← getEnv
  for (name, expected) in #[
      (`KnowledgeAttributeCases.theory, Kind.T),
      (`KnowledgeAttributeCases.model, Kind.M),
      (`KnowledgeAttributeCases.theoryModel, Kind.TM),
      (`KnowledgeAttributeCases.modelImplementation, Kind.MI),
      (`KnowledgeAttributeCases.implementationObservation, Kind.IO),
      (`KnowledgeAttributeCases.combinedTheory, Kind.T),
      (`KnowledgeAttributeCases.combinedModel, Kind.M)] do
    unless kindOf? env name == some expected do
      throwError "Immediate tmio lookup failed for {name}"
  let privateRef ← `(privateTheory)
  let privateName ← liftCoreM <| Lean.realizeGlobalConstNoOverload privateRef
  unless isPrivateName privateName && kindOf? env privateName == some .T do
    throwError "An explicitly classified private theorem was lost"
  for name in #[`KnowledgeAttributeCases.combinedTheory, `KnowledgeAttributeCases.combinedModel] do
    unless powerlib.Registry.kindOf? env name == some .foundation do
      throwError "Combined attribute block failed to update the foundation registry for {name}"

theorem delayed : True := True.intro
attribute [tmio M] delayed

/-- error: Theorem KnowledgeAttributeCases.theoryModel already has tmio T-M; a second assignment is not allowed -/
#guard_msgs in
attribute [tmio TM] theoryModel

/-- error: Theorem KnowledgeAttributeCases.theoryModel already has tmio T-M; a second assignment is not allowed -/
#guard_msgs in
attribute [tmio IO] theoryModel

theorem unclassified : True := True.intro

/-- error: Unknown tmio kind I; expected T, M, TM, MI or IO -/
#guard_msgs in
attribute [tmio I] unclassified

/-- error: Unknown tmio kind O; expected T, M, TM, MI or IO -/
#guard_msgs in
attribute [tmio O] unclassified

def ordinaryDefinition : Nat := 0

/-- error: The tmio attribute requires a theorem: KnowledgeAttributeCases.ordinaryDefinition -/
#guard_msgs in
attribute [tmio M] ordinaryDefinition

run_cmd do
  let env ← getEnv
  unless kindOf? env `KnowledgeAttributeCases.delayed == some .M do
    throwError "Delayed tmio assignment was lost"
  unless kindOf? env `KnowledgeAttributeCases.theoryModel == some .TM do
    throwError "Rejected reassignment changed the original tmio kind"
  unless (kindOf? env `KnowledgeAttributeCases.unclassified).isNone do
    throwError "An invalid tmio value was stored"
  unless (kindOf? env `KnowledgeAttributeCases.ordinaryDefinition).isNone do
    throwError "A non-theorem received a tmio attribute"

end KnowledgeAttributeCases
