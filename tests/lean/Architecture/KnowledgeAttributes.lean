import theorem.Attributes

/-! # Source knowledge attribute checks

Scope.
* Lean-only checks for the five `tmio` values, immediate asynchronous queries, private helpers
  and delayed assignment. These ordinary test theorems are not typed connection coverage subjects.
* Rejection cases preserve the original classification: repeated assignment of either the
  same or another kind, standalone I/O values and non-theorem declarations are rejected.
* A single attribute block combines `tmio` and `powerlib_foundation` in either order.

Source: `theorem/TMIO/KnowledgeKind.lean`, `theorem/Attributes.lean` and the five-category
contract in `Architecture.md`.

Results.
* All five source attributes and an attributed private helper are observable through `kindOf?`
  in the current module; ordinary unclassified theorems do not acquire a kind.
* Expected diagnostics check the attribute's type, value and uniqueness boundaries.
* Combined attribute blocks update both registries in either order. Compatibility permits
  foundation T/M/TM and domain M/TM/MI/IO, without requiring both tags to be present.
* Rejected pairs are tested in temporary environments, including delayed and private cases.
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
@[tmio TM, powerlib_foundation] theorem foundationTheoryModel : True := True.intro
@[powerlib_domain, tmio M] theorem domainModel : True := True.intro
@[tmio TM, powerlib_domain] theorem domainTheoryModel : True := True.intro
@[powerlib_domain, tmio MI] theorem domainImplementation : True := True.intro
@[tmio IO, powerlib_domain] private theorem domainObservation : True := True.intro

-- Test actual attribute persistence and the same checker used by the module linter and
-- whole-package build. Negative fixtures never escape their temporary environments.
set_option hygiene false in
run_cmd do
  let cases : Array (Syntax × String) := #[
    ((← `(@[tmio MI, powerlib_foundation] theorem bad : True := True.intro)).raw,
      "powerlib_foundation with tmio M-I"),
    ((← `(@[powerlib_foundation, tmio MI] theorem bad : True := True.intro)).raw,
      "powerlib_foundation with tmio M-I"),
    ((← `(@[tmio IO, powerlib_foundation] private theorem bad : True := True.intro)).raw,
      "powerlib_foundation with tmio I-O"),
    ((← `(@[powerlib_foundation, tmio IO] theorem bad : True := True.intro)).raw,
      "powerlib_foundation with tmio I-O"),
    ((← `(@[tmio T, powerlib_domain] theorem bad : True := True.intro)).raw,
      "powerlib_domain with tmio T"),
    ((← `(@[powerlib_domain, tmio T] private theorem bad : True := True.intro)).raw,
      "powerlib_domain with tmio T"),
    ((← `(attribute [powerlib_foundation] modelImplementation)).raw,
      "powerlib_foundation with tmio M-I"),
    ((← `(attribute [powerlib_foundation] implementationObservation)).raw,
      "powerlib_foundation with tmio I-O"),
    ((← `(attribute [powerlib_domain] theory)).raw,
      "powerlib_domain with tmio T")]
  for (command, expected) in cases do
    withoutModifyingEnv do
      elabCommand command
      let mut rejected := false
      try
        powerlib.Registry.auditCompatibilityInEnvironment
      catch ex =>
        unless (← ex.toMessageData.toString).contains expected do throw ex
        rejected := true
      unless rejected do throwError "An incompatible pair was accepted: {expected}"
  powerlib.Registry.auditCompatibilityInEnvironment

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
attribute [powerlib_foundation] delayed

@[powerlib_domain] theorem metadataFirst : True := True.intro
attribute [tmio TM] metadataFirst

@[powerlib_foundation] theorem untaggedFoundation : True := True.intro
@[powerlib_domain] theorem untaggedDomain : True := True.intro

set_option hygiene false in
run_cmd do
  for command in #[
      (← `(attribute [tmio MI] untaggedFoundation)),
      (← `(attribute [tmio IO] untaggedFoundation)),
      (← `(attribute [tmio T] untaggedDomain))] do
    withoutModifyingEnv do
      elabCommand command
      let mut rejected := false
      try
        powerlib.Registry.auditCompatibilityInEnvironment
      catch ex =>
        unless (← ex.toMessageData.toString).contains "Incompatible PowerLib classifications" do
          throw ex
        rejected := true
      unless rejected do throwError "An incompatible delayed tmio attribute was accepted"

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
