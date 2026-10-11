import theorem.Circuits.RL
import theorem.Architecture
import dependencies.tests.lean.ConnectionFamilyFixture

open powerlib powerlib.TMIO

namespace ConnectionAdmission

-- No classification annotation is needed for a real public connection theorem.
theorem passive (m : Circuits.RL.Impedance) (h : 0 ≤ m.resistance) :
    connection% (m ∈ Circuits.RL.family.den .passive) := by
  unfold Statement
  exact Circuits.RL.family_isLinear.mem_den_passive (Circuits.RL.kyp m h)

-- The annotation cannot change the theorem's structurally inferred role.
@[powerlib_foundation] theorem misleading_label (m : Circuits.RL.Impedance)
    (h : 0 ≤ m.resistance) : connection% (m ∈ Circuits.RL.family.den .passive) := passive m h

-- Private fixtures are implementation evidence, never public results.
@[powerlib_foundation] private theorem raw (m : Circuits.RL.Impedance)
    (h : 0 ≤ m.resistance) : m.plant.system.Passive :=
  ⟨_, (Circuits.RL.kyp m h).passiveWith⟩

def fakeEndpoint (m : Circuits.RL.Impedance) : Prop := m.plant.system.Passive

private theorem aliased (m : Circuits.RL.Impedance) (h : 0 ≤ m.resistance) :
    fakeEndpoint m := raw m h

abbrev ModelAlias := Circuits.RL.Impedance

private theorem aliasedModel (m : ModelAlias) (h : 0 ≤ m.resistance) :
    fakeEndpoint m := raw m h

private def proofDefinition (m : Circuits.RL.Impedance) (h : 0 ≤ m.resistance) :
    fakeEndpoint m := raw m h

private theorem hiddenRelation (m : Circuits.RL.Impedance) (h : 0 ≤ m.resistance) :
    connection% (m ∈ Circuits.RL.family.den .passive ↔ fakeEndpoint m) := by
  unfold Statement
  exact ⟨fun _ => raw m h, fun _ => passive m h⟩

private theorem rawHypothesis (m : Circuits.RL.Impedance) (h : m.plant.system.Passive) :
    connection% (m ∈ Circuits.RL.family.den .passive) := by
  unfold Statement
  exact Circuits.RL.family.mem_den.mpr h

-- A real connection does not make a raw behavioural input an admitted interface.
private theorem hiddenInput (m : Circuits.RL.Impedance) (h : 0 ≤ m.resistance) :
    connection% (m ∈ (sInfHom.id (Set Circuits.RL.Impedance))
      {m : Circuits.RL.Impedance | fakeEndpoint m}) := by
  unfold Statement
  exact raw m h

private theorem freshRaw (m : ConnectionFamilyFixture.Model) :
    (Port.System.autonomous m.field).Passive := Port.System.autonomous_passive m.field

def AllPassive : Prop := ∀ m : Circuits.RL.Impedance, 0 ≤ m.resistance → m.plant.system.Passive

private theorem packed : AllPassive := fun m h => raw m h

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  liftTermElabM do
    let ctx ← Architecture.context
    let models ← Architecture.modelTypes
    for name in #[``raw, ``aliased, ``aliasedModel, ``proofDefinition, ``hiddenRelation,
        ``rawHypothesis, ``hiddenInput, ``freshRaw, ``packed] do
      if (← Architecture.publicTypeRejection ctx models (← getConstInfo name).type).isNone then
        throwError "Public admission accepted its rejection fixture: {name}"
    for name in #[``passive, ``misleading_label] do
      if let some reason ← Architecture.declarationRejection ctx models name then
        throwError "Public admission rejected its positive fixture: {name}: {reason}"
  for name in #[``passive, ``misleading_label] do
    unless Registry.kindOf? env name == some .domain &&
        (Registry.theoremNames env (some .domain)).contains name &&
        !(Registry.theoremNames env (some .foundation)).contains name do
      throwError "Connection discovery trusted metadata instead of the proposition type"
  logInfo "POWERLIB_TYPED_ADMISSION_OK: unlabeled and mislabeled positive claims; 9 rejection controls"

end ConnectionAdmission
