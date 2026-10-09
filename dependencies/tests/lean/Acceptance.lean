import powerlib

-- Public interface acceptance.
open powerlib

-- Public interfaces for simplification, extensionality, and supplied certificates.
example (m : Impedance) : toImpedance (toStateSpace m) = m := by simp
example (m : LCL.Circuit) : LCL.toCircuit (LCL.toStateSpace m) = m := by simp

example (p q : LCL.SymmetricMatrix) (h11 : p.p11 = q.p11) (h12 : p.p12 = q.p12)
    (h13 : p.p13 = q.p13) (h22 : p.p22 = q.p22) (h23 : p.p23 = q.p23)
    (h33 : p.p33 = q.p33) : p = q := by ext <;> assumption

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f : E → E} {V : E → ℝ} {equilibrium : E}
    (certificate : Dynamics.QuadraticDecayCertificate f V equilibrium)
    (hf : ContDiff ℝ 1 f) :
    Dynamics.ForwardComplete f ∧ Dynamics.GloballyExponentiallyStable f equilibrium := by aesop

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in #[`powerlib.generated.convert_spec, `powerlib.generated.convertLCL_spec,
      `powerlib.Dynamics.globallyAsymptoticallyStable_of_strictLyapunov,
      `powerlib.Dynamics.QuadraticDecayCertificate.globallyExponentiallyStable] do
    unless (powerlib.Registry.kindOf? env name).isSome do
      throwError "Public theorem missing from its classification: {name}"
  unless (powerlib.Registry.kindOf? env `powerlib.response).isNone do
    throwError "A definition was classified as a theorem"
  logInfo "POWERLIB_API_OK"

-- Native automation acceptance.
open powerlib Filter
open scoped Topology

example (m : StateSpace) : toStateSpace (toImpedance m) = m := by simp
example (m : Impedance) : toImpedance (toStateSpace m) = m := by simp
example (x : Positive) : reciprocal (reciprocal x) = x := by simp
example (m : Impedance) (h : 0 < m.resistance) : (toStateSpace m).Stable := by
  simpa using h
example (m : Impedance) (initial : ℝ) : response m initial 0 = initial := by simp

example (m : Impedance) (c : Accepted m) : m.Stable := by aesop
example (m : Impedance) (c : Accepted m) (i : ℝ) :
    2 * c.p * i * (toStateSpace m).field i 0 = -i ^ 2 := by aesop
example (m : Impedance) (initial t : ℝ) :
    HasDerivAt (response m initial) ((toStateSpace m).field (response m initial t) 0) t := by
  aesop

-- Constructed solutions satisfy both the ODE and the submitted initial state.
example (m : Impedance) (initial : ℝ) :
    IsTrajectory m 0 (response m initial) ∧ response m initial 0 = initial := by aesop

example (m : Impedance) (v e initial : ℝ) (he : IsEquilibrium m v e) :
    IsTrajectory m v (equilibriumResponse m e initial) ∧
      equilibriumResponse m e initial 0 = initial := by aesop
example (m : Impedance) (c : Accepted m) (initial t : ℝ) :
    (response m initial t) ^ 2 = initial ^ 2 * Real.exp (-c.rate * t) := by aesop

example (m : LCL.Circuit) : LCL.toCircuit (LCL.toStateSpace m) = m := by simp
example (m : LCL.StateSpace) : LCL.toStateSpace (LCL.toCircuit m) = m := by simp
example (m : LCL.Circuit) (hp : m.Passive)
    (hd : m.first.resistance ≠ 0 ∨ m.second.resistance ≠ 0) :
    (LCL.toStateSpace m).Stable := by simpa [hp] using hd
example (m : LCL.Circuit) :
    (LCL.toStateSpace m).Stable ↔ m.Stable := by simp

example (m : LCL.Circuit) (c : LCL.Accepted m) : (LCL.toStateSpace m).Stable := by aesop
example (m : LCL.Circuit) (c : LCL.Accepted m) (x y z : ℝ)
    (hn : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) : 0 < LCL.energy c.p x y z := by aesop
example (m : LCL.Circuit) (c : LCL.Accepted m) (x y z : ℝ) :
    let f := (LCL.toStateSpace m).field x y z 0 0
    LCL.energyDerivative c.p x y z f.1 f.2.1 f.2.2 = -(x^2+y^2+z^2) := by aesop
example (m : LCL.Circuit) (h2 : 0 < m.a2) (h1 : 0 < m.a1) (h0 : 0 < m.a0)
    (hg : 0 < m.a2*m.a1-m.a3*m.a0) : m.Stable := by aesop

example (m : LCL.Circuit) (initial : LCL.State) :
    LCL.IsTrajectory m 0 0 (LCL.response m initial) ∧
      LCL.response m initial 0 = initial := by aesop

example (m : LCL.Circuit) (initial : LCL.State) (t : ℝ) :
    HasDerivAt (LCL.response m initial)
      ((LCL.toStateSpace m).operator (LCL.response m initial t)) t ∧
      LCL.response m initial 0 = initial := by aesop

example (m : LCL.Circuit) (u vg : ℝ) (e initial : LCL.State)
    (he : LCL.IsEquilibrium m u vg e) :
    LCL.IsTrajectory m u vg (LCL.equilibriumResponse m e initial) ∧
      LCL.equilibriumResponse m e initial 0 = initial := by aesop

-- A supplied equilibrium is itself a forward solution of the submitted model.
example (m : LCL.Circuit) (u vg : ℝ) (e : LCL.State)
    (he : LCL.IsEquilibrium m u vg e) :
    LCL.IsTrajectory m u vg (fun _ => e) := by aesop

example (m : LCL.Circuit) : LCL.IsTrajectory m 0 0 (fun _ => 0) := by aesop

-- Physical stored energy uses the plant's own positive inductances/capacitance.
example (m : LCL.Circuit) (x : LCL.State) (hx : x ≠ 0) :
    0 < LCL.quadraticEnergy (LCL.physicalWeights m) x := by aesop

-- Passivity alone gives Lyapunov stability; no damping or certificate is supplied.
example (m : LCL.Circuit) (hp : m.Passive) (u vg : ℝ) (e : LCL.State)
    (he : LCL.IsEquilibrium m u vg e) : LCL.LyapunovStable m u vg e := by aesop

example (p q : LCL.SymmetricMatrix) (h11 : p.p11 = q.p11) (h12 : p.p12 = q.p12)
    (h13 : p.p13 = q.p13) (h22 : p.p22 = q.p22) (h23 : p.p23 = q.p23)
    (h33 : p.p33 = q.p33) : p = q := by ext <;> assumption

-- Native library search receives goals and local hypotheses, without theorem-name hints.
example (m : Impedance) : toImpedance (toStateSpace m) = m := by aesop

example (m : Impedance) : m.Stable ↔ 0 < m.resistance := by aesop

example (m : Impedance) :
    (toStateSpace m).Stable ↔ m.Stable := by aesop

example (m : Impedance) : IsEquilibrium m 0 0 := by simp

example (m : Impedance) (c : Accepted m) : m.Stable := by aesop

example (m : Impedance) (c : Accepted m) :
    AsymptoticallyStable m 0 0 := by aesop

example (m : Impedance) (c : Accepted m) :
    GloballyExponentiallyStable m 0 0 ∧ AsymptoticallyStable m 0 0 := by aesop

example (m : Impedance) (c : Accepted m) (v e : ℝ) (he : IsEquilibrium m v e) :
    LyapunovStable m v e := by aesop

example (m : Impedance) (c : Accepted m) (v e : ℝ) (he : IsEquilibrium m v e) :
    GloballyAsymptoticallyStable m v e := by aesop

example (m : Impedance) (c : Accepted m) (v e : ℝ) (he : IsEquilibrium m v e) :
    GloballyExponentiallyStable m v e := by aesop

example (m : Impedance) (v e : ℝ) (he : IsEquilibrium m v e) :
    AsymptoticallyStable m v e ↔ 0 < m.resistance := by aesop

example (m : Impedance) (v e initial : ℝ) (he : IsEquilibrium m v e) :
    ∃ i, IsTrajectory m v i ∧ i 0 = initial := by aesop

example (m : Impedance) (hm : m.Stable) (v e : ℝ) (i : ℝ → ℝ)
    (he : IsEquilibrium m v e) (hi : IsTrajectory m v i) :
    Tendsto i atTop (𝓝 e) := by aesop

example (m : Impedance) (c : Accepted m) (v e : ℝ) (i : ℝ → ℝ)
    (he : IsEquilibrium m v e) (hi : IsTrajectory m v i) (t : ℝ) (ht : 0 ≤ t) :
    (i t - e) ^ 2 = (i 0 - e) ^ 2 * Real.exp (-(c.rate * t)) := by aesop

example (m : Impedance) (c : Accepted m) (v e : ℝ) (i : ℝ → ℝ)
    (he : IsEquilibrium m v e) (hi : IsTrajectory m v i) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => energy c.p (i s - e)) (-(i t - e) ^ 2) (Set.Ici 0) t := by
  aesop

-- Admission uses a named certificate definition, introduced as a local fact.
namespace RLAdmissionFixture

def submittedModel : Impedance := ⟨2, ⟨1, by norm_num⟩⟩

noncomputable def accepted : Accepted submittedModel :=
  synthesize submittedModel (by norm_num [submittedModel])

example (voltage : ℝ)
    (he : IsEquilibrium submittedModel voltage (voltage / submittedModel.resistance)) :
    GloballyAsymptoticallyStable submittedModel voltage
      (voltage / submittedModel.resistance) := by
  have certificate := accepted
  aesop

example (voltage equilibrium : ℝ) (i : ℝ → ℝ)
    (he : IsEquilibrium submittedModel voltage equilibrium)
    (hi : IsTrajectory submittedModel voltage i) (t : ℝ) (ht : 0 ≤ t) :
    (i t - equilibrium) ^ 2 =
      (i 0 - equilibrium) ^ 2 * Real.exp (-(accepted.rate * t)) := by
  let certificate := accepted
  aesop

end RLAdmissionFixture


example (m : LCL.Circuit) : LCL.toCircuit (LCL.toStateSpace m) = m := by aesop
example (m : LCL.Circuit) (c : LCL.Accepted m) :
    (LCL.toStateSpace m).Stable := by aesop
example (m : LCL.Circuit) (c : LCL.Accepted m) (x y z : ℝ)
    (hn : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) : 0 < LCL.energy c.p x y z := by aesop
example (m : LCL.Circuit) (c : LCL.Accepted m) (x y z : ℝ) :
    let f := (LCL.toStateSpace m).field x y z 0 0
    LCL.energyDerivative c.p x y z f.1 f.2.1 f.2.2 = -(x^2+y^2+z^2) := by aesop

example (m : LCL.Circuit) (c : LCL.Accepted m) (u vg : ℝ) (e : LCL.State)
    (he : LCL.IsEquilibrium m u vg e) :
    LCL.GloballyExponentiallyStable m u vg e := by aesop

example (m : LCL.Circuit) (c : LCL.Accepted m) (u vg : ℝ) (e : LCL.State)
    (he : LCL.IsEquilibrium m u vg e) :
    LCL.GloballyAsymptoticallyStable m u vg e := by aesop

example (m : LCL.Circuit) : LCL.IsEquilibrium m 0 0 0 := by simp

example (m : LCL.Circuit) (c : LCL.Accepted m) :
    LCL.AsymptoticallyStable m 0 0 0 := by aesop

example (m : LCL.Circuit) (c : LCL.Accepted m) :
    LCL.GloballyExponentiallyStable m 0 0 0 ∧ LCL.AsymptoticallyStable m 0 0 0 := by aesop

example (m : LCL.Circuit) (c : LCL.Accepted m) (u vg : ℝ) (initial : LCL.State) :
    ∃ x, LCL.IsTrajectory m u vg x ∧ x 0 = initial := by aesop

example (m : LCL.Circuit) (c : LCL.Accepted m) (u vg : ℝ) (e : LCL.State)
    (x : ℝ → LCL.State) (he : LCL.IsEquilibrium m u vg e) (hx : LCL.IsTrajectory m u vg x) :
    Tendsto x atTop (𝓝 e) := by aesop

example (m : LCL.Circuit) (c : LCL.Accepted m) (u vg : ℝ) (e : LCL.State)
    (x : ℝ → LCL.State) (he : LCL.IsEquilibrium m u vg e) (hx : LCL.IsTrajectory m u vg x)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => LCL.quadraticEnergy c.p (x s - e))
      (-LCL.squaredSize (x t - e)) (Set.Ici 0) t := by aesop

example (m : LCL.Circuit) (hp : m.Passive) (u vg : ℝ) (e : LCL.State)
    (he : LCL.IsEquilibrium m u vg e) : LCL.LyapunovStable m u vg e := by aesop

example (m : LCL.Circuit) (h1 : m.first.resistance = 0) (h2 : m.second.resistance = 0)
    (u vg : ℝ) (e : LCL.State) (he : LCL.IsEquilibrium m u vg e) :
    ¬ LCL.AsymptoticallyStable m u vg e := by aesop

example (m : LCL.Circuit) (hp : m.Passive) (hd : m.Damped) :
    LCL.AsymptoticallyStable m 0 0 0 := by aesop

example (m : LCL.Circuit) (hp : m.Passive) (hd : m.Damped) (u vg : ℝ) (e : LCL.State)
    (he : LCL.IsEquilibrium m u vg e) :
    LCL.GloballyExponentiallyStable m u vg e := by aesop

namespace LCLAdmissionFixture

def submittedModel : LCL.Circuit :=
  ⟨⟨1, ⟨1, by norm_num⟩⟩, ⟨1, ⟨1, by norm_num⟩⟩, ⟨1, by norm_num⟩⟩

noncomputable def accepted : LCL.Accepted submittedModel :=
  LCL.synthesize submittedModel
    (by norm_num [submittedModel, LCL.Circuit.Passive])
    (by norm_num [submittedModel, LCL.Circuit.Damped])

example : LCL.GloballyAsymptoticallyStable submittedModel 0 0 0 := by
  have certificate := accepted
  aesop

example (initial : LCL.State) :
    ∃ x, LCL.IsTrajectory submittedModel 0 0 x ∧ x 0 = initial := by
  let certificate := accepted
  aesop

example (x : ℝ → LCL.State) (hx : LCL.IsTrajectory submittedModel 0 0 x)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => LCL.quadraticEnergy accepted.p (x s))
      (-LCL.squaredSize (x t)) (Set.Ici 0) t := by
  let certificate := accepted
  have he : LCL.IsEquilibrium submittedModel 0 0 0 := by simp
  simpa using certificate.energy_derivative he hx ht

end LCLAdmissionFixture

example (m : LCL.Circuit) (hp : m.Passive) (u vg : ℝ) (e : LCL.State)
    (he : LCL.IsEquilibrium m u vg e) :
    LCL.AsymptoticallyStable m u vg e ↔ m.first.resistance ≠ 0 ∨ m.second.resistance ≠ 0 := by
  aesop

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let domains := Registry.theoremNames env (some .domain)
  let foundations := Registry.theoremNames env (some .foundation)
  for name in #[`powerlib.lcl_stable_iff, `powerlib.impedance_stable_iff,
      `powerlib.Accepted.stable, `powerlib.LCL.Accepted.stable,
      `powerlib.asymptoticallyStable_iff_resistance_pos,
      `powerlib.Accepted.globallyExponentiallyStable,
      `powerlib.Accepted.energy_derivative, `powerlib.LCL.Accepted.globallyExponentiallyStable,
      `powerlib.LCL.Accepted.globallyAsymptoticallyStable,
      `powerlib.LCL.Accepted.energy_derivative, `powerlib.LCL.trajectory_exists,
      `powerlib.LCL.trajectory_unique, `powerlib.LCL.passive_lyapunovStable,
      `powerlib.LCL.lossless_not_asymptoticallyStable,
      `powerlib.LCL.lossless_energy_conserved,
      `powerlib.Upstream.lcl_upstream_contractive_block] do
    unless domains.contains name do
      throwError "Public domain theorem missing from discovery: {name}"
  for name in #[`powerlib.lcl_asymptotically_stable_iff,
      `powerlib.lcl_globally_exponentially_stable_iff,
      `powerlib.LCL.passive_asymptoticallyStable, `powerlib.LCL.passive_globallyExponentiallyStable] do
    unless domains.contains name do
      throwError "Public semantic theorem missing from discovery: {name}"
  for name in #[`powerlib.state_roundtrip, `powerlib.LCL.circuit_roundtrip,
      `powerlib.generated.convert_spec, `powerlib.generated.convertLCL_spec,
      `powerlib.trajectory_iff_circuit] do
    unless foundations.contains name do
      throwError "Imported foundation theorem missing from discovery: {name}"
  unless (Registry.kindOf? env `powerlib.response).isNone do
    throwError "A definition was classified as a theorem"
  for name in Registry.theoremNames env do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Discovery returned a non-theorem: {name}"
  -- Audit the actual native tactic consumers, including anonymous examples.
  for (name, info) in env.constants do
    if info.isTheorem && (env.getModuleIdxFor? name).isNone then
      for axiomName in Search.declarationAxioms env name do
        unless Search.allowedAxiom axiomName do
          throwError "Native automatic consumer used an unapproved axiom: {name}: {axiomName}"
  logInfo "POWERLIB_AUTOMATION_OK"

-- Audited rule reuse.
open powerlib

-- These are library-rule reuse checks with supplied premises, not certificate synthesis.
namespace RuleReuseChecks

inductive DerivedClaim (value : ℕ) : Prop where
  | intro : 0 < value → DerivedClaim value

-- A type-directed rule whose numerical premise must be discharged at the application.
@[powerlib_foundation] theorem from_model_relation (value witness : ℕ) (h : value = 2 * witness + 1) :
    DerivedClaim value := .intro (by omega)

@[powerlib_foundation] theorem concrete_relation : DerivedClaim 23 := by
  have hmodel : (23 : ℕ) = 2 * 11 + 1 := by decide
  powerlib_search

@[powerlib_domain] theorem existence_and_decay {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f : E → E} {V : E → ℝ} {equilibrium : E}
    (certificate : Dynamics.QuadraticDecayCertificate f V equilibrium)
    (hf : ContDiff ℝ 1 f) :
    Dynamics.ForwardComplete f ∧ Dynamics.GloballyExponentiallyStable f equilibrium := by
  constructor <;> powerlib_search

@[powerlib_domain] theorem strict_energy_existence {n : ℕ}
    {f : Dynamics.State n → Dynamics.State n} {V : Dynamics.State n → ℝ}
    {equilibrium : Dynamics.State n} (hn : 0 < n) (hf : ContDiff ℝ 1 f)
    (hV : Dynamics.IsStrictLyapunovFunction f V equilibrium) :
    Dynamics.ForwardComplete f := by
  have hstable : Dynamics.GloballyAsymptoticallyStable f equilibrium := by powerlib_search
  exact hstable.2.1

end RuleReuseChecks

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let info ← getConstInfo `RuleReuseChecks.concrete_relation
  let some proof := info.value? (allowOpaque := true) | throwError "Missing rule-reuse proof"
  unless proof.getUsedConstants.contains `RuleReuseChecks.from_model_relation do
    throwError "The numerical target did not apply the type-directed rule"
  for name in #[`RuleReuseChecks.concrete_relation, `RuleReuseChecks.existence_and_decay,
      `RuleReuseChecks.strict_energy_existence] do
    for axiomName in powerlib.Search.declarationAxioms env name do
      unless powerlib.Search.allowedAxiom axiomName do
        throwError "Rule reuse used an unapproved axiom: {axiomName}"
  logInfo "POWERLIB_RULE_REUSE_OK"

-- Upstream theorem reuse.
open scoped Matrix.Norms.Frobenius

namespace UpstreamConsumers

-- No upstream names or PowerLib classification attributes are supplied to search.
@[powerlib_foundation] theorem exp_positive (x : ℝ) : 0 < Real.exp x := by powerlib_search
@[powerlib_foundation] theorem exp_add (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y := by powerlib_search
@[powerlib_foundation] theorem exp_injective {x y : ℝ} (h : Real.exp x = Real.exp y) : x = y := by powerlib_search

@[powerlib_domain]
theorem lcl_contractive_reuse {m : powerlib.LCL.Circuit} (c : powerlib.LCL.Accepted m) :
    ∃ k : ℕ, 0 < k ∧
      ‖NormedSpace.exp ((k : ℝ) • (powerlib.LCL.toStateSpace m).matrix)‖ < 1 :=
  powerlib.Upstream.lcl_upstream_contractive_block c

end UpstreamConsumers

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some entry := powerlib.Search.describe env `Real.exp_pos |
    throwError "Imported theorem absent from discovery"
  unless entry.name == `Real.exp_pos && entry.moduleName.getRoot == `Mathlib do
    throwError "Imported theorem lost its source module"
  unless entry.kind.isNone && entry.axioms.all powerlib.Search.allowedAxiom do
    throwError "Upstream theorem was misclassified or failed the axiom policy"
  unless powerlib.Search.eligible env `Real.exp_pos do
    throwError "Admissible upstream theorem was excluded"
  unless (powerlib.Search.describe env `Real.exp).isNone do
    throwError "A definition was indexed as a theorem"
  for name in #[`UpstreamConsumers.exp_positive, `UpstreamConsumers.exp_add,
      `UpstreamConsumers.exp_injective] do
    let info ← getConstInfo name
    let some proof := info.value? (allowOpaque := true) | throwError "Missing consumer proof: {name}"
    unless proof.getUsedConstants.any (fun dependency =>
        match env.getModuleIdxFor? dependency with
        | some index => env.header.moduleNames[index]!.getRoot == `Mathlib
        | none => false) do
      throwError "Consumer did not directly reuse an imported theorem: {name}"
    for ax in powerlib.Search.declarationAxioms env name do
      unless powerlib.Search.allowedAxiom ax do
        throwError "Unexpected upstream consumer axiom: {ax}"
  for (consumer, source) in #[
      (`powerlib.Passivity.DissipativeStorage.integral_dissipation,
        `intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le),
      (`powerlib.Passivity.DissipativeStorage.zeroInput_energy_antitone,
        `antitoneOn_of_hasDerivWithinAt_nonpos),
      (`powerlib.StateSpacePassivity.trajectory_unique, `ODE_solution_unique),
      (`powerlib.LTI.Model.response_solves, `hasDerivAt_exp_smul_const')] do
    let info ← getConstInfo consumer
    let some proof := info.value? (allowOpaque := true) | throwError "Missing passivity proof: {consumer}"
    unless proof.getUsedConstants.contains source do
      throwError "Passivity proof did not directly reuse {source}"
    let some entry := powerlib.Search.describe env source |
      throwError "Passivity upstream theorem absent from discovery: {source}"
    unless entry.moduleName.getRoot == `Mathlib &&
        entry.axioms.all powerlib.Search.allowedAxiom &&
        powerlib.Search.eligible env source do
      throwError "Passivity upstream theorem failed provenance or axiom checks: {source}"
  let some bridgeInfo := env.find? `powerlib.Upstream.contractive_block |
    throwError "The LeanForControl contractivity bridge is missing"
  let some bridgeProof := bridgeInfo.value? (allowOpaque := true) |
    throwError "The LeanForControl contractivity bridge has no proof"
  unless bridgeProof.getUsedConstants.contains
      `LinearSystems.IsHurwitz.exists_norm_exp_nat_smul_lt_one do
    throwError "The bridge did not directly reuse LeanForControl's contractivity theorem"
  unless powerlib.Registry.kindOf? env `UpstreamConsumers.lcl_contractive_reuse == some .domain do
    throwError "The LCL upstream domain consumer lost its classification"
  logInfo "POWERLIB_UPSTREAM_REUSE_OK"
