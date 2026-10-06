import powerlib
import dependencies.tests.lean.RegistryFixture

namespace RegistryCurrent

def StableContract (m : powerlib.Impedance) : Prop := m.Stable ∧ m.Stable

@[powerlib_domain] theorem stable (m : powerlib.Impedance) (c : powerlib.Accepted m) :
    StableContract m := ⟨c.stable, c.stable⟩

def unclassifiable : Nat := 0

/-- error: PowerLib theorem attributes require a theorem: RegistryCurrent.unclassifiable -/
#guard_msgs in
attribute [powerlib_domain] unclassifiable

/-- error: PowerLib theorem RegistryCurrent.stable is already classified as domain -/
#guard_msgs in
attribute [powerlib_foundation] stable

-- These consumers import only declarations and metadata. They supply no names
-- or per-goal rule lists to native or audited proof search.
universe u

@[powerlib_foundation] theorem imported_application {α : Sort u} (P : α → Prop) (x : α) (h : P x) :
    RegistryFixture.Envelope (P x) := by powerlib_search

@[powerlib_foundation] theorem imported_iff (P : Prop) : RegistryFixture.Envelope P ↔ P := by
  powerlib_search

@[powerlib_domain] theorem current_application (m : powerlib.Impedance) (c : powerlib.Accepted m) :
    StableContract m := by powerlib_search

end RegistryCurrent

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  -- Read current-file metadata before any whole-registry synchronization.
  let some current := powerlib.Search.describe env `RegistryCurrent.stable |
    throwError "A current-file tagged theorem lost its metadata"
  unless current.kind == some .domain do
    throwError "The current-file theorem classification changed"
  let names := powerlib.Registry.theoremNames env
  let domains := powerlib.Registry.theoremNames env (some .domain)
  let foundations := powerlib.Registry.theoremNames env (some .foundation)
  unless names.size == domains.size + foundations.size do
    throwError "The classified theorem partition is incomplete"
  unless names == names.qsort Name.quickLt && names.toList.eraseDups.length == names.size do
    throwError "The classified theorem registry is not unique and deterministic"
  unless domains.contains `RegistryCurrent.stable do
    throwError "A newly tagged theorem outside the PowerLib namespace was omitted"
  unless foundations.contains `RegistryFixture.envelope &&
      foundations.contains `RegistryFixture.envelope_iff do
    throwError "Imported attribute metadata was omitted"
  unless (powerlib.Registry.kindOf? env `RegistryCurrent.stable) == some .domain &&
      (powerlib.Registry.kindOf? env `RegistryFixture.envelope) == some .foundation do
    throwError "Current or imported theorem classification was lost"
  let some imported := powerlib.Search.describe env `RegistryFixture.envelope |
    throwError "An imported tagged theorem lost its metadata"
  unless imported.moduleName == `dependencies.tests.lean.RegistryFixture &&
      imported.kind == some .foundation && imported.levelParams.length == 1 do
    throwError "Imported theorem origin, classification, or universe metadata changed"
  for (consumer, sources) in #[
      (`RegistryCurrent.imported_application,
        #[`RegistryFixture.envelope, `RegistryFixture.envelope_iff]),
      (`RegistryCurrent.current_application, #[`RegistryCurrent.stable])] do
    let info ← getConstInfo consumer
    let some proof := info.value? (allowOpaque := true) | throwError "Missing automatic proof: {consumer}"
    unless sources.any proof.getUsedConstants.contains do
      throwError "Automatic search failed to reuse the discovered declaration: {consumer}"
  -- The same dynamically collected registry drives admission, so no handwritten
  -- admission list can omit the newly tagged current-file theorem above.
  for name in names ++ #[`RegistryCurrent.imported_application,
      `RegistryCurrent.imported_iff, `RegistryCurrent.current_application] do
    unless powerlib.Search.eligible env name do
      throwError "A registered theorem or its automatic consumer failed admission: {name}"
  logInfo "POWERLIB_REGISTRY_OK"
