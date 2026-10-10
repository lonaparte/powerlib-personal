import powerlib

open powerlib powerlib.TMIO OrderDual

-- A new consumer supplies its three relations and nothing else; the generated chain, its
-- explicit formula and its soundness are reused without new order-theoretic proofs.
namespace TMIOConsumers

inductive Sentence
  | safe

inductive Requirement
  | atMost (k : ℕ)

def translation : SetRel Sentence Requirement := {p | p.2 = .atMost 10}

def Meets (n : ℕ) : Requirement → Prop
  | .atMost k => n ≤ k

-- A position sensor reports the position or one above it.
def sensor : SetRel ℕ ℕ := {p | p.2 = p.1 ∨ p.2 = p.1 + 1}

def seed : Seed (Set Sentence) (Set Requirement) (Set ℕ)ᵒᵈ (Set ℕ)ᵒᵈ :=
  relationalSeed translation Meets sensor

@[powerlib_foundation] theorem certified (Φ : Set Sentence) :
    ofDual (generate seed.uTO Φ) = certify sensor (realize Meets (translation.image Φ)) :=
  relationalSeed_whole translation Meets sensor Φ

@[powerlib_foundation] theorem certified_sound {r n : ℕ}
    (hr : r ∈ ofDual (generate seed.uTO {Sentence.safe})) (hn : (n, r) ∈ sensor) : n ≤ 10 :=
  relationalSeed_sound translation Meets sensor (den := fun _ => {n | n ≤ 10})
    (fun φ x hx => by
      rw [mem_realize] at hx
      exact hx (.atMost 10) ⟨φ, rfl, rfl⟩) hr hn .safe rfl

-- A separately written forward map is the generated one once it is a lower adjoint.
@[powerlib_foundation] theorem forward_unique {l : Set ℕ → Set ℕ}
    (h : GaloisConnection l (preimage (· + 1 : ℕ → ℕ))) : l = Set.image (· + 1) := by
  rw [generate_unique _ h, generate_preimage]

-- A forward map that differs from the generated one is rejected.
@[powerlib_foundation] theorem wrong_forward_rejected :
    ¬ GaloisConnection (fun _ : Set ℕ => (Set.univ : Set ℕ)) (preimage (· + 1 : ℕ → ℕ)) := by
  intro h
  have := (congrFun (generate_unique _ h) ∅).trans (congrFun (generate_preimage _) ∅)
  simp at this

end TMIOConsumers

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  -- The generator and its standard constructors directly apply Mathlib's Galois-connection API.
  for (consumer, source) in #[
      (`powerlib.TMIO.generate_unique, `GaloisConnection.l_unique),
      (`powerlib.TMIO.generate_comp, `GaloisConnection.compose),
      (`powerlib.TMIO.generate_isLeast, `GaloisConnection.isLeast_l),
      (`powerlib.TMIO.generate_sSup, `GaloisConnection.l_sSup_eq_sSup_image),
      (`powerlib.TMIO.generate_satisfaction, `SetRel.gc_leftDual_rightDual),
      (`powerlib.TMIO.generate_preimage, `Set.image_preimage),
      (`powerlib.TMIO.generate_kern, `Set.preimage_kernImage),
      (`powerlib.TMIO.gc_certify, `GaloisConnection.dual),
      (`powerlib.TMIO.gc_predict, `GaloisConnection.compl)] do
    let info ← getConstInfo consumer
    let some proof := info.value? (allowOpaque := true) |
      throwError "Missing TMIO proof: {consumer}"
    unless proof.getUsedConstants.contains source do
      throwError "TMIO proof did not directly reuse {source}: {consumer}"
    let some entry := powerlib.Search.describe env source |
      throwError "Upstream theorem absent from discovery: {source}"
    unless entry.moduleName.getRoot == `Mathlib && entry.kind.isNone &&
        powerlib.Search.eligible env source do
      throwError "Upstream theorem failed provenance or axiom checks: {source}"
  -- Instances and consumers reach their conclusions through the generated structure, and the
  -- families reach exactness through the single linear semantics.
  for (consumer, source) in #[
      (`powerlib.Circuits.RL.reading_certifies, `powerlib.TMIO.relationalSeed_sound),
      (`powerlib.Circuits.RL.certified_readings, `powerlib.TMIO.relationalSeed_whole),
      (`powerlib.Circuits.RL.certified_records, `powerlib.TMIO.generate_comp),
      (`powerlib.Circuits.RL.predicted_readings, `powerlib.TMIO.predict_eq_image),
      (`powerlib.Circuits.RL.reading_refutes, `powerlib.TMIO.predict_eq_image),
      (`powerlib.Circuits.RL.stateSpace_whole, `powerlib.TMIO.Seed.transport_whole),
      (`powerlib.Circuits.RL.stateSpace_space, `powerlib.TMIO.generate_transport),
      (`powerlib.Circuits.RL.realize_translate, `powerlib.Linear.realize_eq_den),
      (`powerlib.Circuits.LCL.realize_translate_attractive, `powerlib.Linear.realize_eq_den),
      (`powerlib.Circuits.Interconnection.exactUnder_impedanceStable,
        `powerlib.Linear.exactUnder_den),
      (`powerlib.Circuits.Interconnection.portData_not_certified, `powerlib.TMIO.mem_certify),
      (`powerlib.Data.Analysis.generate_distributedEdge,
        `powerlib.Data.Analysis.distributedEdge_eq_centralEdge),
      (`TMIOConsumers.certified, `powerlib.TMIO.relationalSeed_whole),
      (`TMIOConsumers.certified_sound, `powerlib.TMIO.relationalSeed_sound),
      (`TMIOConsumers.forward_unique, `powerlib.TMIO.generate_unique)] do
    let info ← getConstInfo consumer
    let some proof := info.value? (allowOpaque := true) |
      throwError "Missing TMIO consumer proof: {consumer}"
    unless proof.getUsedConstants.contains source do
      throwError "TMIO consumer did not directly reuse {source}: {consumer}"
  -- The core makes no engineering claim: every TMIO theorem is a foundation theorem and passes
  -- the transitive axiom audit. Domain conclusions live with the families.
  let mut foundations : Nat := 0
  for name in powerlib.Registry.theoremNames env do
    unless (`powerlib.TMIO).isPrefixOf name || (`TMIOConsumers).isPrefixOf name do
      continue
    unless powerlib.Registry.kindOf? env name == some .foundation do
      throwError "The TMIO core makes a domain claim: {name}"
    foundations := foundations + 1
    for axiomName in powerlib.Search.declarationAxioms env name do
      unless powerlib.Search.allowedAxiom axiomName do
        throwError "TMIO theorem used an unapproved axiom: {name}: {axiomName}"
  for name in #[`powerlib.Circuits.RL.realize_translate, `powerlib.Circuits.RL.reading_certifies,
      `powerlib.Circuits.RL.dcTest_certifies, `powerlib.Circuits.RL.stateSpace_space,
      `powerlib.Circuits.LCL.realize_translate_attractive,
      `powerlib.Circuits.LCL.exactUnder_damped,
      `powerlib.Circuits.Interconnection.exactUnder_impedanceStable,
      `powerlib.Circuits.Interconnection.portData_not_certified] do
    unless powerlib.Registry.kindOf? env name == some .domain do
      throwError "A family conclusion is not a classified domain theorem: {name}"
  for name in #[`powerlib.TMIO.generate, `powerlib.TMIO.realize, `powerlib.TMIO.Seed,
      `powerlib.TMIO.relationalSeed, `powerlib.TMIO.transport, `powerlib.TMIO.ExactUnder] do
    unless (powerlib.Registry.kindOf? env name).isNone do
      throwError "A TMIO definition was classified as a theorem: {name}"
  logInfo m!"POWERLIB_TMIO_OK: {foundations} foundation theorems in the core"
