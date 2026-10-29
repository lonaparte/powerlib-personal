import theorem.TMIO.ClaimElab
import powerlib
import dependencies.tests.lean.Architecture.RegistryFixture

-- Registered theorem discovery.
namespace RegistryCurrent

open powerlib LinearSystems

def StableContract (m : Circuits.RL.Impedance) : Prop :=
  m ∈ Circuits.RL.family.den (.flow .globallyExponentiallyStable) ∧
    m ∈ Circuits.RL.family.den (.flow .globallyExponentiallyStable)

@[powerlib_domain] theorem stable (m : Circuits.RL.Impedance) (c : Linear.Certificate m.plant.A) :
    connection% (StableContract m) := by
  unfold powerlib.TMIO.Statement
  unfold StableContract
  rw [Circuits.RL.family_isLinear.den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)]
  exact ⟨c.isHurwitz, c.isHurwitz⟩

def unclassifiable : Nat := 0

/-- error: PowerLib theorem attributes require a theorem: RegistryCurrent.unclassifiable -/
#guard_msgs in
attribute [powerlib_domain] unclassifiable

/-- error: PowerLib theorem RegistryCurrent.stable is already classified as domain -/
#guard_msgs in
attribute [powerlib_foundation] stable

universe u

-- These consumers supply no theorem names to the audited search.
@[powerlib_foundation] theorem imported_application {α : Sort u} (P : α → Prop) (x : α) (h : P x) :
    RegistryFixture.Envelope (P x) := by powerlib_search

@[powerlib_foundation] theorem imported_iff (P : Prop) : RegistryFixture.Envelope P ↔ P := by
  powerlib_search

@[powerlib_domain] theorem current_application (m : Circuits.RL.Impedance)
    (c : Linear.Certificate m.plant.A) :
    connection% (StableContract m) := by
  unfold powerlib.TMIO.Statement
  powerlib_search

end RegistryCurrent

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some current := powerlib.Search.describe env `RegistryCurrent.stable |
    throwError "A current-file tagged theorem lost its metadata"
  unless current.kind == some .domain do
    throwError "The current-file theorem classification changed"
  let names := powerlib.Registry.theoremNames env
  let domains := powerlib.Registry.theoremNames env (some .domain)
  let foundations := powerlib.Registry.theoremNames env (some .foundation)
  unless names.size == domains.size + foundations.size do
    throwError "The classified theorem partition is incomplete: all {names.size}, domain {domains.size}, foundation {foundations.size}; missing {names.filter (fun n => !domains.contains n && !foundations.contains n)}; overlap {domains.filter foundations.contains}"
  unless names == names.qsort Name.quickLt && names.toList.eraseDups.length == names.size do
    throwError "The classified theorem registry is not unique and deterministic"
  unless domains.contains `RegistryCurrent.stable do
    throwError "A newly tagged theorem outside the PowerLib namespace was omitted"
  unless foundations.contains `RegistryFixture.envelope &&
      foundations.contains `RegistryFixture.envelope_iff do
    throwError "Imported attribute metadata was omitted"
  let some imported := powerlib.Search.describe env `RegistryFixture.envelope |
    throwError "An imported tagged theorem lost its metadata"
  unless imported.moduleName == `dependencies.tests.lean.Architecture.RegistryFixture &&
      imported.kind == some .foundation && imported.levelParams.length == 1 do
    throwError "Imported theorem origin, classification, or universe metadata changed"
  for (consumer, sources) in #[
      (`RegistryCurrent.imported_application,
        #[`RegistryFixture.envelope, `RegistryFixture.envelope_iff]),
      (`RegistryCurrent.current_application, #[`RegistryCurrent.stable])] do
    let info ← getConstInfo consumer
    let some proof := info.value? (allowOpaque := true) |
      throwError "Missing automatic proof: {consumer}"
    unless sources.any proof.getUsedConstants.contains do
      throwError "Automatic search failed to reuse the discovered declaration: {consumer}"
  for name in names do
    unless powerlib.Search.eligible env name do
      throwError "A registered theorem failed admission: {name}"
  logInfo "POWERLIB_REGISTRY_OK"

-- Goal-directed reuse of the library through the audited search: no theorem names are supplied.
namespace AutomaticReuse

open powerlib LinearSystems

@[powerlib_foundation] theorem certificate_holds {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (c : Linear.Certificate A) {P : Flow.Property} (hP : P.Attractive)
    (e : EuclideanSpace ℝ (Fin n)) :
    P.holds (affineLinearVectorField A e) e := by powerlib_search

@[powerlib_foundation] theorem hurwitz_global {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : IsHurwitz A) (e : EuclideanSpace ℝ (Fin n)) :
    Flow.GloballyExponentiallyStable (affineLinearVectorField A e) e := by powerlib_search

@[powerlib_domain] theorem rl_faithful :
    connection% (Circuits.RL.family.chain = Circuits.RL.family.semantics) := by
  unfold powerlib.TMIO.Statement
  powerlib_search

@[powerlib_foundation] theorem rl_sign (m : Circuits.RL.Impedance) :
    IsHurwitz m.plant.A ↔ 0 < m.resistance := by powerlib_search

@[powerlib_foundation] theorem lcl_poles (m : Circuits.LCL.Circuit) :
    IsHurwitz m.plant.A ↔ m.Stable := by powerlib_search

@[powerlib_foundation] theorem decay_global {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {V : EuclideanSpace ℝ (Fin n) → ℝ}
    {e : EuclideanSpace ℝ (Fin n)} (c : Flow.QuadraticDecay f V e) (hf : ContDiff ℝ 1 f) :
    Flow.GloballyExponentiallyStable f e := by powerlib_search

@[powerlib_foundation] theorem decay_complete {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {V : EuclideanSpace ℝ (Fin n) → ℝ}
    {e : EuclideanSpace ℝ (Fin n)} (c : Flow.QuadraticDecay f V e) (hf : ContDiff ℝ 1 f) :
    Flow.ForwardComplete f := by
  powerlib_search

theorem polynomial_global {model : Nonlinear.Polynomial2.Model}
    (c : Nonlinear.Polynomial2.Certificate model) :
    connection% (model ∈ Nonlinear.Polynomial2.family.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  powerlib_search

-- Upstream declarations need no PowerLib attributes or names.
@[powerlib_foundation] theorem exp_positive (x : ℝ) : 0 < Real.exp x := by powerlib_search
@[powerlib_foundation] theorem exp_add (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y := by
  powerlib_search

-- A type-directed rule whose numerical premise is discharged at the application.
inductive DerivedClaim (value : ℕ) : Prop where
  | intro : 0 < value → DerivedClaim value

@[powerlib_foundation] theorem from_model_relation (value witness : ℕ)
    (h : value = 2 * witness + 1) :
    DerivedClaim value := .intro (by omega)

@[powerlib_foundation] theorem concrete_relation : DerivedClaim 23 := by
  have hmodel : (23 : ℕ) = 2 * 11 + 1 := by decide
  powerlib_search

end AutomaticReuse

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (consumer, source) in #[
      (`AutomaticReuse.certificate_holds, `powerlib.Linear.Certificate.holds),
      (`AutomaticReuse.hurwitz_global, `powerlib.Linear.globallyExponentiallyStable_of_isHurwitz),
      (`AutomaticReuse.rl_faithful, `powerlib.Circuits.RL.chain_eq_semantics),
      (`AutomaticReuse.rl_sign, `powerlib.Circuits.RL.isHurwitz_iff),
      (`AutomaticReuse.lcl_poles, `powerlib.Circuits.LCL.isHurwitz_iff_stable),
      (`AutomaticReuse.decay_global, `powerlib.Flow.QuadraticDecay.globallyExponentiallyStable),
      (`AutomaticReuse.decay_complete, `powerlib.Flow.QuadraticDecay.forwardComplete),
      (`AutomaticReuse.polynomial_global,
        `powerlib.Nonlinear.Polynomial2.Certificate.mem_den),
      (`AutomaticReuse.exp_positive, `Real.exp_pos),
      (`AutomaticReuse.concrete_relation, `AutomaticReuse.from_model_relation)] do
    let names := powerlib.Registry.theoremNames env
    let consumer := (names.find? (fun name => privateToUserName name == consumer)).getD consumer
    let source := (names.find? (fun name => privateToUserName name == source)).getD source
    let info ← getConstInfo consumer
    let some proof := info.value? (allowOpaque := true) |
      throwError "Missing automatic proof: {consumer}"
    unless proof.getUsedConstants.contains source do
      throwError "Automatic search did not apply {source}: {consumer}"
    for ax in powerlib.Search.declarationAxioms env consumer do
      unless powerlib.Search.allowedAxiom ax do
        throwError "Automatic reuse used an unapproved axiom: {consumer}: {ax}"
  logInfo "POWERLIB_AUTOMATIC_REUSE_OK"

-- Multi-step goals closed by Aesop from the library's reviewed rules; no theorem names given.
namespace AutomaticChaining

open powerlib LinearSystems

@[powerlib_foundation] theorem certificate_lyapunov {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (c : Linear.Certificate A) : LyapunovStable (affineLinearVectorField A 0) 0 := by aesop

@[powerlib_foundation] theorem certificate_local {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (c : Linear.Certificate A) : LocalAsymptoticStable (affineLinearVectorField A 0) 0 := by
  aesop

@[powerlib_domain] theorem rl_resistance (m : Circuits.RL.Impedance) (h : 0 < m.resistance) :
    connection% (m ∈ Circuits.RL.family.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Circuits.RL.family_isLinear.mem_den_flow)]
  change Flow.GloballyExponentiallyStable (affineLinearVectorField m.plant.A 0) 0
  aesop

@[powerlib_domain] theorem lcl_passive_damped (m : Circuits.LCL.Circuit) (hp : m.Passive)
    (hd : m.Damped) :
    connection% (m ∈ Circuits.LCL.family.den (.flow .globallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Circuits.LCL.family_isLinear.mem_den_flow)]
  change Flow.GloballyAsymptoticallyStable (affineLinearVectorField m.plant.A 0) 0
  aesop

@[powerlib_domain] theorem interconnection_criterion {n₁ n₂ p : ℕ}
    (ic : Circuits.Interconnection n₁ n₂ p) (h₁ : IsHurwitz ic.source.A)
    (h₂ : IsHurwitz ic.load.A) (h : ic.ImpedanceStable) :
    connection% (ic ∈ Circuits.Interconnection.family.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Circuits.Interconnection.family_isLinear.mem_den_flow)]
  change Flow.GloballyExponentiallyStable (affineLinearVectorField ic.closedLoopA 0) 0
  aesop

@[powerlib_domain] theorem polynomial_certificate {model : Nonlinear.Polynomial2.Model}
    (c : Nonlinear.Polynomial2.Certificate model) :
    connection% (model ∈ Nonlinear.Polynomial2.family.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  aesop

end AutomaticChaining

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (consumer, sources) in #[
      (`AutomaticChaining.certificate_lyapunov,
        #[`powerlib.Linear.Certificate.isHurwitz, `powerlib.Linear.lyapunovStable_of_isHurwitz]),
      (`AutomaticChaining.certificate_local,
        #[`powerlib.Linear.Certificate.isHurwitz,
          `powerlib.Linear.localAsymptoticStable_of_isHurwitz]),
      (`AutomaticChaining.rl_resistance,
        #[`powerlib.Circuits.RL.isHurwitz_iff,
          `powerlib.Linear.globallyExponentiallyStable_of_isHurwitz]),
      (`AutomaticChaining.lcl_passive_damped,
        #[`powerlib.Circuits.LCL.routhHurwitz_of_passive,
          `powerlib.Circuits.LCL.stable_of_routhHurwitz, `powerlib.Circuits.LCL.isHurwitz_iff_stable]),
      (`AutomaticChaining.interconnection_criterion,
        #[`powerlib.Circuits.Interconnection.isHurwitz_closedLoop_of_impedanceStable,
          `powerlib.Linear.globallyExponentiallyStable_of_isHurwitz]),
      (`AutomaticChaining.polynomial_certificate,
        #[`powerlib.Nonlinear.Polynomial2.Certificate.mem_den])] do
    let names := powerlib.Registry.theoremNames env
    let sources := sources.map fun source =>
      (names.find? (fun name => privateToUserName name == source)).getD source
    let info ← getConstInfo consumer
    let some proof := info.value? (allowOpaque := true) | throwError "Missing proof: {consumer}"
    -- Follow the auxiliary declarations simp creates for rewrite rules (`_simp_1`, ...).
    let mut used := proof.getUsedConstants
    let mut todo := used.filter Name.isInternal
    for _ in [0:64] do
      let some aux := todo.back? | break
      todo := todo.pop
      if let some auxValue := (env.find? aux).bind (·.value? (allowOpaque := true)) then
        for c in auxValue.getUsedConstants do
          unless used.contains c do
            used := used.push c
            if c.isInternal then todo := todo.push c
    for source in sources do
      unless used.contains source do
        throwError "Aesop did not chain through {source}: {consumer}"
    for ax in powerlib.Search.declarationAxioms env consumer do
      unless powerlib.Search.allowedAxiom ax do
        throwError "Automatic chaining used an unapproved axiom: {consumer}: {ax}"
  logInfo "POWERLIB_AUTOMATIC_CHAINING_OK"

-- Direct reuse of Mathlib and LeanForControl: the library applies the upstream theorem and does
-- not restate its proof.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (consumer, source, root) in #[
      (`powerlib.Linear.locallyExponentiallyStable_of_isHurwitz,
        `hurwitz_linearization_locally_exponentially_stable, `LeanForControl),
      (`powerlib.Linear.nonempty_certificate_iff,
        `LinearSystems.IsHurwitz.exists_posDef_unique_solution_continuous_lyapunov,
        `LeanForControl),
      (`powerlib.Linear.unstable_of_eigenvalue, `unstable_affineLinear_of_eigenvalue_re_pos,
        `LeanForControl),
      (`powerlib.Flow.globallyAsymptoticallyStable_of_strictLyapunov,
        `lyapunov_asymptotic_stable, `LeanForControl),
      (`powerlib.Flow.forwardComplete_of_lipschitzWith, `exists_isIntegralCurveOn_Ici,
        `LeanForControl),
      (`powerlib.Flow.forwardComplete_of_compact_sublevel, `antitoneOn_V_comp_traj,
        `LeanForControl),
      (`powerlib.Linear.isObservable_iff_isControllable_transpose,
        `LinearSystems.isControllable_iff_controllabilityMatrix_rank_eq, `LeanForControl),
      (`powerlib.Linear.contractive_block,
        `LinearSystems.IsHurwitz.exists_norm_exp_nat_smul_lt_one, `LeanForControl),
      (`powerlib.Linear.op_exp, `NormedSpace.map_exp, `Mathlib),
      (`powerlib.Port.System.passiveWith_of_rate,
        `intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le, `Mathlib),
      (`powerlib.Linear.solution_hasDerivAt, `hasDerivAt_exp_smul_const', `Mathlib)] do
    let info ← getConstInfo consumer
    let some proof := info.value? (allowOpaque := true) | throwError "Missing proof: {consumer}"
    unless proof.getUsedConstants.contains source do
      throwError "{consumer} did not directly reuse {source}"
    let some entry := powerlib.Search.describe env source |
      throwError "Upstream theorem absent from discovery: {source}"
    unless entry.moduleName.getRoot == root && entry.kind.isNone &&
        powerlib.Search.eligible env source do
      throwError "Upstream theorem failed provenance, classification or axiom checks: {source}"
  logInfo "POWERLIB_UPSTREAM_REUSE_OK"
