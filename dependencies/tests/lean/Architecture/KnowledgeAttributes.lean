import theorem.TMIO.KnowledgeKind

/-! # Source knowledge attribute checks

Scope.
* Lean-only checks for the five `tmio` values, immediate asynchronous queries and delayed
  assignment. These ordinary test theorems are not typed connection coverage subjects.
* Rejection cases preserve the original classification: repeated assignment of either the
  same or another kind, standalone I/O values and non-theorem declarations are rejected.

Source: `theorem/TMIO/KnowledgeKind.lean` and the five-category contract in `Layers.md`.

Results.
* All five source attributes are observable through `kindOf?` in the current module.
* Expected diagnostics check the attribute's type, value and uniqueness boundaries.
* The final query checks that rejected assignments neither replace nor add classifications.
-/

namespace KnowledgeAttributeCases

open Lean Elab Command powerlib.Knowledge

@[tmio T] theorem theory : True := True.intro
@[tmio M] theorem model : True := True.intro
@[tmio TM] theorem theoryModel : True := True.intro
@[tmio MI] theorem modelImplementation : True := True.intro
@[tmio IO] theorem implementationObservation : True := True.intro

run_cmd do
  let env ← getEnv
  for (name, expected) in #[
      (`KnowledgeAttributeCases.theory, Kind.T),
      (`KnowledgeAttributeCases.model, Kind.M),
      (`KnowledgeAttributeCases.theoryModel, Kind.TM),
      (`KnowledgeAttributeCases.modelImplementation, Kind.MI),
      (`KnowledgeAttributeCases.implementationObservation, Kind.IO)] do
    unless kindOf? env name == some expected do
      throwError "Immediate tmio lookup failed for {name}"

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
