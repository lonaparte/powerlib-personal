import powerlib
import LeanForControl.axioms

-- Dynamics semantic regression cases.
/-! Regression checks on the public API: global existence, estimates for every
finite solution segment, attraction of every complete trajectory, and rejection
of a locally stable field whose energy increases far from the equilibrium. -/

noncomputable section
namespace powerlib.Tests.Dynamics

open powerlib.Dynamics Set Filter Topology

-- There is a full forward trajectory through every initial state, including n = 0.
@[powerlib_domain] theorem nonlinear_every_initial_state_has_global_solution (n : ℕ) (a : ℝ) (x₀ : State n) :
    ∃ φ : ℝ → State n, φ a = x₀ ∧
      powerlib.Dynamics.IsIntegralCurveOn φ (fun _ x => Nonlinear.field x) (Ici a) :=
  (Nonlinear.globallyExponentiallyStable n).2.1 a x₀

-- This estimate applies to an arbitrary solution, time anchor, and amplitude.
@[powerlib_domain] theorem nonlinear_every_finite_segment_decays {n : ℕ} {φ : ℝ → State n}
    {a b t : ℝ} (hφ : powerlib.Dynamics.IsTrajectoryOn φ (@Nonlinear.field n) a b) (ht : t ∈ Icc a b) :
    ‖φ t‖ ≤ Real.exp (-(t - a)) * ‖φ a‖ :=
  Nonlinear.norm_bound hφ ht

-- The public GAS theorem supplies universal attraction, not a selected response.
@[powerlib_domain] theorem nonlinear_every_global_trajectory_converges {n : ℕ} (hn : 0 < n)
    (a : ℝ) (φ : ℝ → State n)
    (hφ : powerlib.Dynamics.IsIntegralCurveOn φ (fun _ x => Nonlinear.field x) (Ici a)) :
    Tendsto φ atTop (𝓝 (0 : State n)) :=
  (Nonlinear.globallyAsymptoticallyStable hn).2.2.2 a φ hφ

-- Accepted LCL witnesses remain indexed by the exact original zero-input plant.
@[powerlib_domain] theorem lcl_every_initial_state_has_global_solution {m : powerlib.LCL.Circuit}
    (c : powerlib.LCL.Accepted m) (a : ℝ) (x₀ : powerlib.LCL.State3) :
    ∃ φ : ℝ → powerlib.LCL.State3, φ a = x₀ ∧
      powerlib.Dynamics.IsIntegralCurveOn φ (fun _ x => m.autonomousField x) (Ici a) :=
  c.autonomousGloballyExponentiallyStable.2.1 a x₀

@[powerlib_domain] theorem lcl_uniform_decay_of_every_finite_segment {m : powerlib.LCL.Circuit}
    (c : powerlib.LCL.Accepted m) :
    ∃ C rate : ℝ, 1 ≤ C ∧ 0 < rate ∧
      ∀ (a b : ℝ) (φ : ℝ → powerlib.LCL.State3),
        powerlib.Dynamics.IsTrajectoryOn φ m.autonomousField a b →
        ∀ t ∈ Icc a b,
          ‖φ t‖ ≤ C * Real.exp (-(rate * (t - a))) * ‖φ a‖ := by
  simpa only [sub_zero] using c.autonomousGloballyExponentiallyStable.2.2

@[powerlib_domain] theorem lcl_every_global_trajectory_converges {m : powerlib.LCL.Circuit}
    (c : powerlib.LCL.Accepted m) (a : ℝ) (φ : ℝ → powerlib.LCL.State3)
    (hφ : powerlib.Dynamics.IsIntegralCurveOn φ (fun _ x => m.autonomousField x) (Ici a)) :
    Tendsto φ atTop (𝓝 (0 : powerlib.LCL.State3)) :=
  c.autonomousGloballyAsymptoticallyStable.2.2.2 a φ hφ

-- A negative Jacobian at zero must not be mistaken for global stability.
def locallyStableField (x : ℝ) : ℝ := -x + x ^ 3

def squareEnergy (x : ℝ) : ℝ := x ^ 2

@[powerlib_foundation] theorem locallyStableField_has_negative_linearization :
    HasDerivAt locallyStableField (-1) 0 := by
  simpa [locallyStableField, Pi.neg_apply, Pi.add_apply, Pi.pow_apply] using!
    (hasDerivAt_id (0 : ℝ)).neg.add ((hasDerivAt_id (0 : ℝ)).pow 3)

@[powerlib_foundation] theorem squareEnergy_lie_derivative (x : ℝ) :
    fderiv ℝ squareEnergy x (locallyStableField x) =
      2 * x * locallyStableField x := by
  have hd := ((hasDerivAt_id x).pow 2).hasFDerivAt
  change fderiv ℝ (fun y : ℝ => id y ^ 2) x (locallyStableField x) = _
  erw [hd.fderiv]
  simp
  ring

-- At x = 2 the Lie derivative is 24; no positive global decay rate can fit.
@[powerlib_domain] theorem locallyStableField_rejects_global_decay_certificate :
    ¬ Nonempty (QuadraticDecayCertificate locallyStableField squareEnergy 0) := by
  rintro ⟨c⟩
  have hdecay := c.dissipation 2
  rw [squareEnergy_lie_derivative] at hdecay
  norm_num [locallyStableField, squareEnergy] at hdecay
  nlinarith [c.rate_pos]

-- The complete field has a nonzero constant trajectory. Thus global exponential
-- stability itself is false, independently of the choice of energy certificate.
@[powerlib_domain] theorem locallyStableField_not_globallyExponentiallyStable :
    ¬ powerlib.Dynamics.GloballyExponentiallyStable locallyStableField (0 : ℝ) := by
  intro hstable
  obtain ⟨C, rate, hC, hrate, hdecay⟩ := hstable.2.2
  have hCpos : 0 < C + 1 := by linarith
  let t := Real.log (C + 1) / rate
  have ht : 0 ≤ t := by
    apply le_of_lt
    exact div_pos (Real.log_pos (by linarith : 1 < C + 1)) hrate
  have hφ : powerlib.Dynamics.IsTrajectoryOn (fun _ : ℝ => (1 : ℝ)) locallyStableField 0 t := by
    intro s hs
    simpa [locallyStableField] using (hasDerivAt_const s (1 : ℝ)).hasDerivWithinAt
  have hbound := hdecay 0 t (fun _ => 1) hφ t ⟨ht, le_refl t⟩
  simp only [sub_zero, norm_one, mul_one] at hbound
  have hrt : rate * t = Real.log (C + 1) := by
    dsimp [t]
    field_simp
  rw [hrt, Real.exp_neg, Real.exp_log hCpos] at hbound
  have hlt : C * (C + 1)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hCpos]
    linarith
  exact (not_lt_of_ge hbound) hlt

end powerlib.Tests.Dynamics

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let namespacePrefix := `powerlib.Tests.Dynamics
  let roots := (powerlib.Registry.theoremNames env).filter namespacePrefix.isPrefixOf
  if roots.isEmpty then
    throwError "Dynamics regression discovery found no registered theorems"
  let mut auditedAxioms : Array Name := #[]
  for root in roots do
    match env.find? root with
    | some (.thmInfo _) => pure ()
    | some _ => throwError "Dynamics regression audit root {root} is not a theorem"
    | none => throwError "Dynamics regression audit root {root} was not found"
    auditedAxioms := auditedAxioms ++ powerlib.Search.declarationAxioms env root
  for ax in auditedAxioms do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "Unexpected Dynamics regression axiom {ax}"
  logInfo "POWERLIB_DYNAMICS_OK"

-- RL large-signal cases.
noncomputable section
namespace powerlib.Tests.RLLargeSignal
open powerlib

@[powerlib_domain] theorem component_only (m : Impedance) (hR : 0 < m.resistance) (voltage : ℝ) :
    GloballyExponentiallyStable m voltage (voltage / m.resistance) := by aesop

def submittedModel : Impedance := ⟨2, ⟨1, by norm_num⟩⟩

@[powerlib_domain] theorem concrete_component_only (voltage : ℝ) :
    GloballyExponentiallyStable submittedModel voltage
      (voltage / submittedModel.resistance) := by
  have hR : 0 < submittedModel.resistance := by norm_num [submittedModel]
  aesop

@[powerlib_domain] theorem all_trajectories_decay (m : Impedance) (hR : 0 < m.resistance)
    (voltage : ℝ) (i : ℝ → ℝ) (hi : IsTrajectory m voltage i)
    (t : ℝ) (ht : 0 ≤ t) :
    (i t - voltage / m.resistance) ^ 2 =
      (i 0 - voltage / m.resistance) ^ 2 * Real.exp (-(2 * (toStateSpace m).decay * t)) := by
  let certificate := synthesize m hR
  have he : IsEquilibrium m voltage (voltage / m.resistance) :=
    equilibrium_of_resistance_ne_zero (ne_of_gt hR) voltage
  change _ = _ * Real.exp (-(certificate.rate * t))
  aesop

end powerlib.Tests.RLLargeSignal

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless powerlib.Registry.kindOf? env `powerlib.rl_globally_exponentially_stable == some .domain do
    throwError "Component-only RL theorem missing from public discovery"
  for name in #[`powerlib.Tests.RLLargeSignal.component_only,
      `powerlib.Tests.RLLargeSignal.concrete_component_only,
      `powerlib.Tests.RLLargeSignal.all_trajectories_decay] do
    for axiomName in powerlib.Search.declarationAxioms env name do
      unless powerlib.Search.allowedAxiom axiomName do
        throwError "Unapproved RL large-signal consumer axiom: {name}: {axiomName}"
  logInfo "POWERLIB_RL_LARGE_SIGNAL_OK"

-- LTI automatic reuse cases.
open powerlib

example {n : ℕ} (m : LTI.AutonomousModel n) (c : LTI.Accepted m) : LTI.ExponentiallyStable m := by aesop
example {n : ℕ} (m : LTI.AutonomousModel n) (initial : LTI.State n) :
    LTI.IsTrajectory m (LTI.response m initial) := by aesop
example {n : ℕ} (m : LTI.AutonomousModel n) (initial : LTI.State n) :
    LTI.response m initial 0 = initial := by simp
example {n : ℕ} (m : LTI.AutonomousModel n) (c : LTI.Accepted m)
    (initial : LTI.State n) (t : ℝ) (ht : 0 ≤ t) :
    LTI.sqNorm (LTI.response m initial t) ≤
      (c.upper / c.lower) * Real.exp (-(t / c.upper)) * LTI.sqNorm initial := by aesop

-- Every named LTI theorem has a standard automation use case. None of these
-- proofs supplies a theorem name to aesop/simp; mere registry membership is
-- tested separately below and is not a substitute for actual proof search.
section LTIReuse
variable {n : ℕ} (m : LTI.AutonomousModel n) (c : LTI.Accepted m)
  (x y : ℝ → LTI.State n) (hx : LTI.IsTrajectory m x) (hy : LTI.IsTrajectory m y)
  (t : ℝ) (ht : 0 ≤ t) (u v : LTI.State n)

example : m.field 0 = 0 := by simp
example : m.field (u + v) - m.field u = m.field v := by aesop
example : m.operator u = m.field u := by simp
example : LTI.sqNorm u = ‖LTI.euclidean u‖ ^ 2 := by aesop
example : ∃ z, LTI.IsTrajectory m z ∧ z 0 = u := by aesop
example : 0 ≤ LTI.sqNorm u := by aesop
example : LTI.sqNorm (0 : LTI.State n) = 0 := by simp
example : LTI.sqNorm u = 0 ↔ u = 0 := by simp

include hx in
example (P : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun s => LTI.energy P (x s))
      (dotProduct (m.field (x t)) (P.mulVec (x t)) +
       dotProduct (x t) (P.mulVec (m.field (x t)))) t := by aesop
example : dotProduct (m.field u) (c.P.mulVec u) +
    dotProduct u (c.P.mulVec (m.field u)) = -LTI.sqNorm u := by aesop
include hx in
example : HasDerivAt (fun s => LTI.energy c.P (x s)) (-LTI.sqNorm (x t)) t := by aesop
include hx ht in
example : LTI.energy c.P (x t) ≤ Real.exp (-(t / c.upper)) * LTI.energy c.P (x 0) := by aesop
include hx ht in
example : LTI.sqNorm (x t) ≤
    (c.upper / c.lower) * Real.exp (-(t / c.upper)) * LTI.sqNorm (x 0) := by aesop
include hx ht in
example : ‖LTI.euclidean (x t)‖ ≤ Real.sqrt (c.upper / c.lower) *
    Real.exp (-(t / c.upper) / 2) * ‖LTI.euclidean (x 0)‖ := by aesop
include c hx hy ht in
example (h0 : x 0 = y 0) : x t = y t := by aesop
include c hx ht in
example : x t = LTI.response m (x 0) t := by aesop
include c hx in
example : Filter.Tendsto (fun t => LTI.sqNorm (x t)) Filter.atTop (nhds 0) := by aesop
example : generated.linearField m.A u = m.A.mulVec u := by simp
end LTIReuse

-- State-space passivity cases.
open powerlib Matrix
open scoped Topology

noncomputable section

namespace StateSpacePassivityCases

@[powerlib_domain] theorem arbitrary_dimensions_passive {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (m : LTI.Model ι κ) (c : StateSpacePassivity.Certificate m) :
    Passivity.PassiveWithStorage (StateSpacePassivity.system m)
      (StateSpacePassivity.energy c.P) := by aesop

@[powerlib_domain] theorem arbitrary_dimensions_stable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty ι] (m : LTI.Model ι κ)
    (c : StateSpacePassivity.Certificate m) :
    Passivity.LyapunovStable (StateSpacePassivity.system m) := by aesop

@[powerlib_domain] theorem arbitrary_dimensions_equilibrium_stable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty ι] (m : LTI.Model ι κ)
    (c : StateSpacePassivity.Certificate m) (u : κ → ℝ) (e : ι → ℝ)
    (he : m.IsEquilibrium u e) :
    StateSpacePassivity.LyapunovStableAt m u e := by aesop

@[powerlib_domain] theorem arbitrary_dimensions_matrix_certificate_passive {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] (m : LTI.Model ι κ)
    (c : StateSpacePassivity.MatrixCertificate m) :
    Passivity.PassiveWithStorage (StateSpacePassivity.system m)
      (StateSpacePassivity.energy c.P) := by
  let gc := c.toCertificate
  have hp : Passivity.PassiveWithStorage (StateSpacePassivity.system m)
      (StateSpacePassivity.energy gc.P) := by aesop
  exact hp

@[powerlib_domain] theorem arbitrary_dimensions_matrix_certificate_stable {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [Nonempty ι] (m : LTI.Model ι κ)
    (c : StateSpacePassivity.MatrixCertificate m) :
    Passivity.LyapunovStable (StateSpacePassivity.system m) := by
  let gc := c.toCertificate
  aesop

@[powerlib_domain] theorem arbitrary_dimensions_integral {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (m : LTI.Model ι κ) (c : StateSpacePassivity.Certificate m)
    {u : ℝ → (κ → ℝ)} {x : ℝ → (ι → ℝ)}
    (hx : Passivity.IsTrajectory (StateSpacePassivity.system m) u x)
    {t : ℝ} (ht : 0 ≤ t)
    (hpower : IntervalIntegrable
      (fun τ => Passivity.supply (StateSpacePassivity.system m) (x τ) (u τ))
      MeasureTheory.volume 0 t) :
    StateSpacePassivity.energy c.P (x t) - StateSpacePassivity.energy c.P (x 0) ≤
      ∫ τ in (0 : ℝ)..t, Passivity.supply (StateSpacePassivity.system m) (x τ) (u τ) := by
  aesop

@[powerlib_domain] theorem arbitrary_dimensions_forward_solution {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (m : LTI.Model ι κ) (initial : ι → ℝ) :
    ∃ x, Passivity.IsTrajectory (StateSpacePassivity.system m) (fun _ => 0) x ∧
      x 0 = initial := by aesop

@[powerlib_domain] theorem arbitrary_input_uniqueness {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (m : LTI.Model ι κ) {u : ℝ → (κ → ℝ)}
    {x y : ℝ → (ι → ℝ)}
    (hx : Passivity.IsTrajectory (StateSpacePassivity.system m) u x)
    (hy : Passivity.IsTrajectory (StateSpacePassivity.system m) u y)
    (h0 : x 0 = y 0) : Set.EqOn x y (Set.Ici 0) := by aesop


@[powerlib_domain] theorem constructed_response_contract {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (m : LTI.Model ι κ) (initial : ι → ℝ) (t : ℝ) :
    HasDerivAt (m.response initial) (m.operator (m.response initial t)) t ∧
      Passivity.IsTrajectory (StateSpacePassivity.system m) (fun _ => 0)
        (m.response initial) ∧
      m.response initial 0 = initial := by aesop

@[powerlib_domain] theorem constructed_equilibrium_response_contract {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] (m : LTI.Model ι κ)
    (u : κ → ℝ) (e initial : ι → ℝ) (he : m.IsEquilibrium u e) :
    Passivity.IsTrajectory (StateSpacePassivity.system m) (fun _ => u) (m.equilibriumResponse e initial) ∧
      m.equilibriumResponse e initial 0 = initial := by aesop

@[powerlib_domain] theorem supplied_equilibrium_forward_solution {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] (m : LTI.Model ι κ)
    (u : κ → ℝ) (e initial : ι → ℝ) (he : m.IsEquilibrium u e) :
    ∃ x, Passivity.IsTrajectory (StateSpacePassivity.system m) (fun _ => u) x ∧
      x 0 = initial := by aesop

@[powerlib_domain] theorem constructed_unique_forward_solution {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] (m : LTI.Model ι κ) (initial : ι → ℝ) :
    ∃ x, Passivity.IsTrajectory (StateSpacePassivity.system m) (fun _ => 0) x ∧
      x 0 = initial ∧ ∀ y,
        Passivity.IsTrajectory (StateSpacePassivity.system m) (fun _ => 0) y →
        y 0 = initial → Set.EqOn y x (Set.Ici 0) := by aesop

@[powerlib_domain] theorem supplied_quadratic_storage_passive {E κ : Type*} [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Passivity.System E κ)
    (V : Passivity.QuadraticStorage s) : Passivity.PassiveWithStorage s V.energy := by aesop

@[powerlib_domain] theorem supplied_quadratic_storage_stable {E κ : Type*} [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    (s : Passivity.System E κ) (V : Passivity.QuadraticStorage s)
    (he : Passivity.IsEquilibrium s 0) : Passivity.LyapunovStable s := by aesop

@[powerlib_foundation] theorem supplied_positive_storage {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (hP : P.PosDef) (x : ι → ℝ) (hx : x ≠ 0) :
    0 < StateSpacePassivity.energy P x := by aesop

def fullStorage : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 2]

def feedthroughModel : LTI.Model (Fin 2) (Fin 1) where
  A := !![-1, 0; 0, -1]
  B := !![1; 0]
  C := !![0, 0]
  D := !![1]

@[powerlib_foundation] theorem fullStorage_quadratic_positive (x : Fin 2 → ℝ) (hx : x ≠ 0) :
    0 < dotProduct x (fullStorage.mulVec x) := by
  simp only [dotProduct, mulVec, fullStorage, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hn : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    ext i
    fin_cases i <;> simp_all
  rcases hn with h0 | h1
  · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg (x 0 + x 1)]
  · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg (x 0 + x 1)]

@[powerlib_foundation] theorem fullStorage_posDef : fullStorage.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.IsHermitian, Matrix.conjTranspose,
      fullStorage]
  · intro x hx
    simpa only [star_trivial] using fullStorage_quadratic_positive x hx

@[powerlib_foundation] theorem feedthrough_full_kyp (x : Fin 2 → ℝ) (u : Fin 1 → ℝ) :
    dotProduct (fullStorage.mulVec x) (LTI.Model.field feedthroughModel x u) ≤
      Passivity.supply (StateSpacePassivity.system feedthroughModel) x u := by
  simp [LTI.Model.field, StateSpacePassivity.system, LTI.Model.output,
    Passivity.supply, dotProduct, mulVec, fullStorage, feedthroughModel,
    Fin.sum_univ_two]
  nlinarith [sq_nonneg (u 0 - x 0 - x 1 / 2),
    sq_nonneg (x 0 + x 1 / 2), sq_nonneg (x 1)]

def feedthroughCertificate : StateSpacePassivity.Certificate feedthroughModel where
  P := fullStorage
  positive := fullStorage_posDef
  kyp := feedthrough_full_kyp

@[powerlib_foundation] theorem storage_has_off_diagonal_entry : fullStorage 0 1 ≠ 0 := by
  norm_num [fullStorage]

@[powerlib_foundation] theorem model_has_feedthrough : feedthroughModel.D ≠ 0 := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℝ => M 0 0) h
  norm_num [feedthroughModel] at he

@[powerlib_foundation] theorem model_is_not_collocated : fullStorage * feedthroughModel.B ≠
    feedthroughModel.C.transpose := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 1) ℝ => M 0 0) h
  norm_num [fullStorage, feedthroughModel, Matrix.mul_apply, Fin.sum_univ_two] at he

@[powerlib_domain] theorem full_kyp_passive :
    Passivity.PassiveWithStorage (StateSpacePassivity.system feedthroughModel)
      (StateSpacePassivity.energy feedthroughCertificate.P) := by
  let c := feedthroughCertificate
  aesop

@[powerlib_domain] theorem full_kyp_stable :
    Passivity.LyapunovStable (StateSpacePassivity.system feedthroughModel) := by
  let c := feedthroughCertificate
  aesop

@[powerlib_domain] theorem full_kyp_forward_solution (initial : Fin 2 → ℝ) :
    ∃ x, Passivity.IsTrajectory (StateSpacePassivity.system feedthroughModel)
      (fun _ => 0) x ∧ x 0 = initial := by
  let submittedModel := feedthroughModel
  aesop


-- The same dimensions do not identify the submitted model.
def mismatchedModel : LTI.Model (Fin 2) (Fin 1) :=
  { feedthroughModel with D := !![-1] }

@[powerlib_foundation] theorem mismatched_model_certificate_is_rejected : True := by
  fail_if_success
    have forged : StateSpacePassivity.Certificate mismatchedModel := feedthroughCertificate
  trivial

@[powerlib_domain] theorem negative_feedthrough_has_no_certificate :
    ¬ Nonempty (StateSpacePassivity.Certificate mismatchedModel) := by
  rintro ⟨c⟩
  have hkyp := c.kyp 0 ![1]
  norm_num [LTI.Model.field, StateSpacePassivity.system,
    LTI.Model.output, Passivity.supply, mismatchedModel, feedthroughModel,
    dotProduct, mulVec, Fin.sum_univ_one, Fin.sum_univ_two] at hkyp

def reversedPortModel : LTI.Model (Fin 1) (Fin 1) where
  A := !![0]
  B := !![1]
  C := !![-1]
  D := !![0]

@[powerlib_domain] theorem reversed_port_has_no_positive_kyp_certificate :
    ¬ Nonempty (StateSpacePassivity.Certificate reversedPortModel) := by
  rintro ⟨c⟩
  have hnonzero : (![1] : Fin 1 → ℝ) ≠ 0 := by
    intro h
    have he := congrArg (fun x : Fin 1 → ℝ => x 0) h
    norm_num at he
  have hpositive := c.positive.dotProduct_mulVec_pos hnonzero
  have hkyp := c.kyp ![1] ![1]
  simp [star_trivial, dotProduct, mulVec] at hpositive
  simp [LTI.Model.field, StateSpacePassivity.system, LTI.Model.output,
    Passivity.supply, reversedPortModel, dotProduct, mulVec] at hkyp
  linarith

def indefiniteStorage : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

@[powerlib_foundation] theorem indefinite_storage_is_rejected : ¬ indefiniteStorage.PosDef := by
  intro hp
  have hnonzero : (![0, 1] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have he := congrArg (fun x : Fin 2 → ℝ => x 1) h
    norm_num at he
  have hpositive := hp.dotProduct_mulVec_pos hnonzero
  norm_num [star_trivial, indefiniteStorage, dotProduct, mulVec, Fin.sum_univ_two] at hpositive

@[powerlib_foundation] theorem autonomous_trajectory_forward {n : ℕ} {κ : Type*} [Fintype κ]
    (m : LTI.Model (Fin n) κ) {x : ℝ → (Fin n → ℝ)} (hx : LTI.IsTrajectory m.autonomous x) :
    Passivity.IsTrajectory (StateSpacePassivity.system m) (fun _ => 0) x := by aesop

end StateSpacePassivityCases

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants do
    if name.getRoot == `StateSpacePassivityCases && info.isTheorem then
      for axiomName in powerlib.Search.declarationAxioms env name do
        unless powerlib.Search.allowedAxiom axiomName do
          throwError "Unexpected generic state-space consumer axiom: {name}: {axiomName}"
  for (consumer, source) in #[
      (`StateSpacePassivityCases.arbitrary_dimensions_passive,
        `powerlib.StateSpacePassivity.Certificate.passiveWithStorage),
      (`StateSpacePassivityCases.arbitrary_dimensions_stable,
        `powerlib.StateSpacePassivity.Certificate.lyapunovStable),
      (`StateSpacePassivityCases.arbitrary_dimensions_integral,
        `powerlib.StateSpacePassivity.Certificate.integral_passivity),
      (`StateSpacePassivityCases.arbitrary_input_uniqueness,
        `powerlib.StateSpacePassivity.trajectory_unique),
      (`StateSpacePassivityCases.full_kyp_passive,
        `powerlib.StateSpacePassivity.Certificate.passiveWithStorage),
      (`StateSpacePassivityCases.full_kyp_stable,
        `powerlib.StateSpacePassivity.Certificate.lyapunovStable),
      (`powerlib.StateSpacePassivity.MatrixCertificate.passiveWithStorage,
        `powerlib.StateSpacePassivity.Certificate.passiveWithStorage),
      (`powerlib.StateSpacePassivity.MatrixCertificate.lyapunovStable,
        `powerlib.StateSpacePassivity.Certificate.lyapunovStable)] do
    let info ← getConstInfo consumer
    let some proof := info.value? (allowOpaque := true) | throwError "Missing generic consumer proof: {consumer}"
    unless proof.getUsedConstants.contains source do
      throwError "Native consumer did not use the general state-space theorem {source}"
  for (consumer, sources) in #[
      (`StateSpacePassivityCases.autonomous_trajectory_forward,
        #[`powerlib.StateSpacePassivity.trajectory_of_autonomous]),
      (`StateSpacePassivityCases.arbitrary_dimensions_forward_solution,
        #[`powerlib.StateSpacePassivity.trajectory_exists,
          `powerlib.StateSpacePassivity.trajectory_exists_unique]),
      (`StateSpacePassivityCases.arbitrary_dimensions_equilibrium_stable,
        #[`powerlib.StateSpacePassivity.Certificate.lyapunovStableAt,
          `powerlib.StateSpacePassivity.Certificate.lyapunovStable]),
      (`StateSpacePassivityCases.arbitrary_dimensions_matrix_certificate_passive,
        #[`powerlib.StateSpacePassivity.Certificate.passiveWithStorage,
          `powerlib.StateSpacePassivity.MatrixCertificate.passiveWithStorage]),
      (`StateSpacePassivityCases.arbitrary_dimensions_matrix_certificate_stable,
        #[`powerlib.StateSpacePassivity.Certificate.lyapunovStable,
          `powerlib.StateSpacePassivity.MatrixCertificate.lyapunovStable])] do
    let info ← getConstInfo consumer
    let some proof := info.value? (allowOpaque := true) | throwError "Missing generic matrix consumer proof: {consumer}"
    unless sources.any proof.getUsedConstants.contains do
      throwError "Matrix consumer did not use a general state-space semantic theorem: {consumer}"
  logInfo "POWERLIB_STATE_SPACE_PASSIVITY_CASES_OK"

-- LeanForControl dynamics reuse audit.
open Lean Meta Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for name in powerlib.Registry.theoremNames env do
    let some entry := powerlib.Search.describe env name |
      throwError "Registered theorem absent from discovery: {name}"
    if entry.moduleName == `theorem.Dynamics.Autonomous ||
        entry.moduleName == `theorem.Dynamics.GlobalLipschitz ||
        name == `powerlib.Dynamics.isCompact_sublevel_set then
      let info ← getConstInfo name
      let some proof := info.value? (allowOpaque := true) |
        throwError "Upstream adapter proof is unavailable: {name}"
      unless proof.getUsedConstants.any (fun dependency =>
          match powerlib.Search.describe env dependency with
          | some source => source.moduleName.getRoot == `LeanForControl
          | none => false) do
        throwError "Adapter did not directly apply a real upstream theorem: {name}"
      count := count + 1
  unless count == 23 do
    throwError "Expected 23 direct upstream adapters, found {count}"
  let badName := `exists_strictMono_upper_bound
  let some bad := powerlib.Search.describe env badName |
    throwError "Missing real upstream negative control"
  unless bad.moduleName == `LeanForControl.axioms &&
      bad.axioms.contains `exists_strictMono_upper_bound_global do
    throwError "Negative control lost its upstream custom-axiom dependency"
  if powerlib.Search.eligible env badName then
    throwError "An upstream custom-axiom consequence entered search"
  liftTermElabM do
    let info ← getConstInfo badName
    forallTelescope info.type fun _ goal => do
      let raw ← LibrarySearch.libSearchFindDecls goal
      unless raw.any (fun candidate => candidate.1 == badName) do
        throwError "Negative control was absent from the standard search index"
      let admissible ← powerlib.Search.candidates goal
      if admissible.any (fun candidate => candidate.1 == badName) then
        throwError "Search did not filter a real upstream custom-axiom consequence"
    let badProof ← mkConstWithFreshMVarLevels badName
    unless (← observing? (powerlib.Search.checkProof badProof)).isNone do
      throwError "Completed-proof audit accepted a custom axiom"
    withLetDecl `borrowed info.type badProof fun borrowed => do
      unless (← observing? (powerlib.Search.checkProof borrowed)).isNone do
        throwError "A local let hid an upstream custom axiom"
  logInfo "POWERLIB_DYNAMICS_UPSTREAM_OK: 23 direct adapters; custom-axiom rejection"
