import theorem.TMIO.ClaimElab
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
    (fun φ _ x hx => by
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
  -- Instances and consumers reach their conclusions through the generated structure: exactness and
  -- soundness are comparisons of the chain with the semantics connection, and every family reaches
  -- them through the generic comparison theorems.
  for (consumer, source) in #[
      (`powerlib.TMIO.generate_inj, `powerlib.TMIO.generate_le_generate_iff),
      (`powerlib.Family.chain_eq_semantics_iff, `powerlib.TMIO.chain_eq_satisfaction_iff),
      (`powerlib.Family.chain_le_semantics_iff, `powerlib.TMIO.chain_le_satisfaction_iff),
      (`powerlib.Family.exact_iff_generate, `powerlib.Family.generate_chain_singleton),
      (`powerlib.Family.certifies, `powerlib.TMIO.relationalSeed_sound),
      (`powerlib.Family.certified, `powerlib.TMIO.relationalSeed_whole),
      (`powerlib.Family.refutes, `powerlib.TMIO.predict_eq_image),
      (`powerlib.Family.Exact.comap, `powerlib.Family.realize_comap),
      (`powerlib.Family.Exact.extend, `powerlib.Family.realize_extend_inl),
      (`powerlib.Circuits.RL.chain_eq_semantics, `powerlib.Family.chain_eq_semantics_iff),
      (`powerlib.Circuits.RL.certified_readings, `powerlib.Family.certified),
      (`powerlib.Circuits.RL.certified_records, `powerlib.TMIO.generate_comp),
      (`powerlib.Circuits.RL.predict_reading, `powerlib.TMIO.predict_eq_image),
      (`powerlib.Circuits.RL.stateSpace_whole, `powerlib.TMIO.Seed.transport_whole),
      (`powerlib.Circuits.LCL.chain_le_semantics, `powerlib.Family.chain_le_semantics_iff),
      (`powerlib.Circuits.LCL.exact_hurwitz, `powerlib.Family.IsLinear.den_hurwitz),
      (`powerlib.Circuits.Interconnection.exactUnder_hurwitz,
        `powerlib.Family.IsLinear.den_hurwitz),
      (`powerlib.Circuits.Interconnection.portData_not_certified, `powerlib.TMIO.mem_certify),
      (`powerlib.Nonlinear.Cubic.chain_eq_semantics, `powerlib.Family.chain_eq_semantics_iff),
      (`powerlib.Nonlinear.Polynomial2.chain_le_semantics,
        `powerlib.Family.chain_le_semantics_iff),
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
  for name in #[`powerlib.Circuits.RL.chain_eq_semantics, `powerlib.Circuits.RL.certified_readings,
      `powerlib.Circuits.RL.certified_records, `powerlib.Circuits.RL.closure_resistance,
      `powerlib.Circuits.LCL.chain_le_semantics, `powerlib.Circuits.LCL.exact_hurwitz,
      `powerlib.Circuits.LCL.exactUnder_conservative, `powerlib.Circuits.LCL.realize_passive_damped,
      `powerlib.Circuits.LCL.exact_passive,
      `powerlib.Circuits.LCL.not_exact_lyapunovStable, `powerlib.Circuits.LCL.not_exact_conservative,
      `powerlib.Circuits.Interconnection.exactUnder_hurwitz,
      `powerlib.Circuits.Interconnection.portData_not_certified,
      `powerlib.Circuits.Interconnection.portData_certified,
      `powerlib.Circuits.Interconnection.soundUnder, `powerlib.Nonlinear.Cubic.chain_eq_semantics,
      `powerlib.Nonlinear.Polynomial2.not_exact_asymptotic] do
    unless powerlib.Registry.kindOf? env name == some .domain do
      throwError "A family conclusion is not a classified domain theorem: {name}"
  for name in #[`powerlib.TMIO.generate, `powerlib.TMIO.realize, `powerlib.TMIO.Seed,
      `powerlib.TMIO.relationalSeed, `powerlib.TMIO.transport, `powerlib.TMIO.ExactUnder,
      `powerlib.Family.chain, `powerlib.Family.semantics, `powerlib.Family.Exact] do
    unless (powerlib.Registry.kindOf? env name).isNone do
      throwError "A TMIO definition was classified as a theorem: {name}"
  logInfo m!"POWERLIB_TMIO_OK: {foundations} foundation theorems in the core"

-- Every conclusion is checked independently of its theorem name and module root.
-- These foundation controls test admission; their matrix-only claims are deliberately rejected.
namespace PlacementFixture

open powerlib LinearSystems

@[powerlib_foundation] theorem offConnection : IsHurwitz !![(-1 : ℝ)] :=
  (Linear.isHurwitz_one_iff (-1)).mpr (by norm_num)

@[powerlib_foundation] theorem phantomFamily (_F : Family Unit Unit 1 0) :
    IsHurwitz !![(-1 : ℝ)] := offConnection

@[powerlib_foundation] theorem irrelevantHypothesis (m : Circuits.RL.Impedance)
    (_h : m ∈ Circuits.RL.family.den (.flow .lyapunovStable)) :
    IsHurwitz !![(-1 : ℝ)] := offConnection

-- Holds is a semantic alias, not a generated endpoint, even though it belongs to Family.
@[powerlib_foundation] private theorem directHolds (m : Circuits.RL.Impedance)
    (h : Circuits.RL.family.Holds m (.flow .lyapunovStable)) :
    Circuits.RL.family.Holds m (.flow .lyapunovStable) := h

def hiddenHolds (m : Circuits.RL.Impedance) : Prop :=
  Circuits.RL.family.Holds m (.flow .lyapunovStable)

@[powerlib_foundation] private theorem transitiveHolds (m : Circuits.RL.Impedance)
    (h : hiddenHolds m) : hiddenHolds m := h

@[powerlib_foundation] theorem unrelatedConjunct :
    Circuits.RL.family.chain = Circuits.RL.family.semantics ∧ IsHurwitz !![(-1 : ℝ)] :=
  ⟨Circuits.RL.chain_eq_semantics, offConnection⟩

@[powerlib_foundation] theorem conditionPadding :
    IsHurwitz (@ite (Matrix (Fin 1) (Fin 1) ℝ)
      (Circuits.RL.family.chain = Circuits.RL.family.semantics)
      (Classical.propDecidable _) !![(-1 : ℝ)] !![(-1 : ℝ)]) := by
  simp only [ite_self]
  exact offConnection

-- The side conditions of the grammar are comparisons of numbers, on the characterizing side of an
-- iff only: a static fact on that side, or a numeric conjunct, is not a connection conclusion.
@[powerlib_foundation] theorem staticIff :
    Circuits.RL.family.chain = Circuits.RL.family.semantics ↔ IsHurwitz !![(-1 : ℝ)] :=
  iff_of_true Circuits.RL.chain_eq_semantics offConnection

@[powerlib_foundation] theorem numericConjunct :
    Circuits.RL.family.chain = Circuits.RL.family.semantics ∧ (1 : ℕ) ≤ 2 :=
  ⟨Circuits.RL.chain_eq_semantics, by norm_num⟩

@[powerlib_domain] theorem onConnection :
    connection% (Circuits.RL.family.chain = Circuits.RL.family.semantics) :=
  Circuits.RL.chain_eq_semantics

end PlacementFixture

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  liftTermElabM do
    let ctx ← powerlib.Architecture.context
    let mut placed : Nat := 0
    for name in powerlib.Registry.theoremNames env (some .domain) do
      let some i := env.getModuleIdxFor? name | continue
      unless powerlib.Registry.isFirstPartyModule env.header.moduleNames[i.toNat]! do continue
      if let some reason ← powerlib.Architecture.rejection ctx (← getConstInfo name).type then
        throwError "Domain theorem failed connection admission: {name}: {reason}"
      placed := placed + 1
    if placed == 0 then throwError "The placement audit found no domain theorem"
    for name in #[`PlacementFixture.offConnection, `PlacementFixture.phantomFamily,
        `PlacementFixture.irrelevantHypothesis, ``PlacementFixture.directHolds,
        ``PlacementFixture.transitiveHolds, `PlacementFixture.unrelatedConjunct,
        `PlacementFixture.conditionPadding, `PlacementFixture.staticIff,
        `PlacementFixture.numericConjunct] do
      if (← powerlib.Architecture.rejection ctx (← getConstInfo name).type).isNone then
        throwError "The architecture audit accepted its negative control: {name}"
    if let some reason ← powerlib.Architecture.rejection ctx
        (← getConstInfo `PlacementFixture.onConnection).type then
      throwError "The architecture audit rejected its positive control: {reason}"
    logInfo m!"POWERLIB_PLACEMENT_OK: {placed} first-party domain theorems; 9 negative controls"
