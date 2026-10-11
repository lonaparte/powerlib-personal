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
      `powerlib.Circuits.RL.dcTest_certified, `powerlib.Circuits.RL.closure_resistance,
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

-- Theorem placement: every domain theorem of the library is stated on a connection.
/-! A domain theorem is the value of a connection at a point, the agreement or order of two
connections, or a witness where they part; its statement therefore mentions a definition of the
TMIO core or of the family layer. The audit reads only the module structure and the registry. The
negative control is a domain theorem about a matrix alone. -/
namespace PlacementFixture

open powerlib LinearSystems

@[powerlib_domain] theorem offConnection : IsHurwitz !![(-1 : ℝ)] :=
  (Linear.isHurwitz_one_iff (-1)).mpr (by norm_num)

@[powerlib_domain] theorem onConnection :
    Circuits.RL.family.chain = Circuits.RL.family.semantics :=
  Circuits.RL.chain_eq_semantics

end PlacementFixture

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let connectionModule (m : Name) : Bool :=
    (`theorem.TMIO).isPrefixOf m || (`theorem.Family).isPrefixOf m
  let onConnection (name : Name) : CommandElabM Bool := do
    let info ← getConstInfo name
    return info.type.getUsedConstants.any fun c =>
      match env.getModuleIdxFor? c with
      | some i => connectionModule env.header.moduleNames[i.toNat]!
      | none => false
  let mut placed : Nat := 0
  let mut violations : Array Name := #[]
  for name in powerlib.Registry.theoremNames env (some .domain) do
    let some i := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[i.toNat]!.getRoot == `theorem do continue
    if (← onConnection name) then placed := placed + 1 else violations := violations.push name
  unless violations.isEmpty do
    throwError "Domain theorems not stated on a connection: {violations}"
  if placed == 0 then throwError "The placement audit found no domain theorem"
  if (← onConnection `PlacementFixture.offConnection) then
    throwError "The placement audit accepted a domain theorem off every connection"
  unless (← onConnection `PlacementFixture.onConnection) do
    throwError "The placement audit rejected a domain theorem on a connection"
  logInfo m!"POWERLIB_PLACEMENT_OK: {placed} library domain theorems on connections"

