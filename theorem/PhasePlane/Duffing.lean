import theorem.PhasePlane.Conservative
import theorem.Criteria.Hurwitz2
import theorem.Flow.Certificate

/-! # The bistable Duffing oscillator `ẍ + δẋ − x + x³ = 0`

Equilibria, the saddle at the origin, the stable wells, forward completeness and the absence of
attractors in the conservative case, for the canonical bistable textbook oscillator.

Model boundary.
* State `(x, y) = (y 0, y 1) ∈ State 2`, `y = ẋ`, constant damping `δ`, continuous time, no
  input or noise. The field is `Conservative.field 1 δ (x³ − x)`, i.e. `ẋ = y`,
  `ẏ = x − x³ − δy`, with the double-well potential `V(x) = x⁴/4 − x²/2` (`V' = x³ − x`) and
  energy `E = y²/2 + V(x)`.
* A canonical textbook system, not a power-system model: no model family; foundation results.

Source: work-sync theory/T-nonlinear-phase-plane.md §1.4, §1.6–1.7;
theory/T-attractors-basins.md (codes example (b): bistable Duffing, saddle eigenvalues
`(−δ ± √(δ² + 4))/2`); theory/T-dynamical-systems.md.

Results.
* Equilibria: exactly `(0, 0)` and `(±1, 0)` (`field_eq_zero_iff`).
* Jacobian at `(x, 0)`: `!![0, 1; 1 − 3x², −δ]` (`hasFDerivAt_field`).
* Saddle at the origin: characteristic roots `(−δ ± √(δ² + 4))/2` (`saddle_eigenvalues`), and
  the origin is unstable for every `δ` (`origin_unstable`, `det = −1 < 0`).
* Wells `(±1, 0)`: locally exponentially stable for `δ > 0` (`tr = −δ`, `det = 2`;
  `well_locallyExponentiallyStable`); Lyapunov stable for every `δ ≥ 0` (strict minima of `V`,
  energy as Lyapunov function; `well_lyapunovStable`).
* Forward completeness for `δ ≥ 0` (`forwardComplete`): the energy has compact sublevel sets and
  is nonincreasing (powerlib `forwardComplete_of_compact_sublevel`).
* Conservative case `δ = 0`: energy is conserved (`energy_conserved`), and a forward solution
  whose energy differs from `E(±1, 0) = −1/4` can never converge to `(±1, 0)`
  (`not_tendsto_of_energy_ne`); points with this property exist arbitrarily close to the wells
  (`energy_off_well`). Hence the wells are not locally asymptotically stable
  (`not_localAsymptoticStable_conservative`): there is no attractor.

Potential shapes: `V(x) = x⁴/4 − x²/2` is the double well of `theorem/Potential/Wells.lean` with
`a = b = 1` (wells `±1`, barrier `a²/4b = 1/4`); the same quartic shape is the supercritical
pitchfork potential of `theorem/NormalForm/Pitchfork.lean` at `μ = 1`.

Corrections. (T-nonlinear-phase-plane.md §1.4): the note says the figure-eight separatrix of the
(undamped) double well "划分吸引域" (separates basins of attraction). For the conservative system
there are no attractors at all (`not_tendsto_of_energy_ne`); basins only appear with damping
`δ > 0`, where the wells become locally exponentially stable (`well_locallyExponentiallyStable`).
-/

noncomputable section
namespace powerlib.PhasePlane.Duffing
open Set Filter Topology
open powerlib.Dynamics (State)
open powerlib.PhasePlane

/-- Restoring force `V'(x) = x³ − x`. -/
def force (x : ℝ) : ℝ := x ^ 3 - x

/-- Double-well potential `V(x) = x⁴/4 − x²/2`. -/
def potential (x : ℝ) : ℝ := x ^ 4 / 4 - x ^ 2 / 2

/-- The Duffing field `ẋ = y`, `ẏ = x − x³ − δy`. -/
def field (δ : ℝ) : State 2 → State 2 := Conservative.field 1 δ force

/-- Energy `y²/2 + x⁴/4 − x²/2`. -/
def energy : State 2 → ℝ := Conservative.energy 1 potential

@[powerlib_foundation] theorem hasDerivAt_potential (x : ℝ) :
    HasDerivAt potential (force x) x := by
  have h := ((hasDerivAt_pow 4 x).div_const 4).sub ((hasDerivAt_pow 2 x).div_const 2)
  unfold potential force
  convert h using 1
  push_cast; ring

@[powerlib_foundation] theorem force_contDiff {k : WithTop ℕ∞} : ContDiff ℝ k force := by
  unfold force; fun_prop

@[powerlib_foundation] theorem field_contDiff (δ : ℝ) {k : WithTop ℕ∞} : ContDiff ℝ k (field δ) :=
  Conservative.field_contDiff force_contDiff

@[powerlib_foundation] theorem field_eq_zero_iff (δ : ℝ) (y : State 2) :
    field δ y = 0 ↔ y 1 = 0 ∧ (y 0 = 0 ∨ y 0 = 1 ∨ y 0 = -1) := by
  rw [field, Conservative.field_eq_zero_iff one_ne_zero]
  have : force (y 0) = 0 ↔ (y 0 = 0 ∨ y 0 = 1 ∨ y 0 = -1) := by
    unfold force
    constructor
    · intro h
      have h' : y 0 * (y 0 - 1) * (y 0 + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.mp h' with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (Or.inl (by linarith))
      · exact Or.inr (Or.inr (by linarith))
    · rintro (h | h | h) <;> rw [h] <;> norm_num
  rw [this]

/-- Jacobian of the Duffing field at `(x, y)`. -/
@[powerlib_foundation] theorem hasFDerivAt_field (δ : ℝ) (y : State 2) :
    HasFDerivAt (field δ)
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) !![0, 1; 1 - 3 * y 0 ^ 2, -δ]) y := by
  refine Dynamics.hasFDerivAt_toEuclideanCLM_of_components _ ![Dynamics.coord 1, (1 - 3 * y 0 ^ 2) • Dynamics.coord 0 + (-δ) • Dynamics.coord 1]
    ?_ ?_
  · intro i; fin_cases i
    · exact Dynamics.hasFDerivAt_coord 1 y
    · show HasFDerivAt (fun z => field δ z 1) _ y
      have h0 := Dynamics.hasFDerivAt_coord 0 y
      have h1 := Dynamics.hasFDerivAt_coord 1 y
      have h := ((h1.const_smul (-δ)).sub ((h0.pow 3).sub h0))
      have hf : (fun z => field δ z 1) = fun z : State 2 => (-δ) • z 1 - (z 0 ^ 3 - z 0) := by
        funext z; simp [field, force, smul_eq_mul]
      rw [hf]
      convert h using 1
      ext v; simp; ring
  · intro i v; rw [Fin.sum_univ_two]; fin_cases i <;> simp

/-- The characteristic roots at the saddle are `(−δ ± √(δ² + 4))/2`. -/
@[powerlib_foundation] theorem saddle_eigenvalues (δ : ℝ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    (Linear.characteristicMatrix (!![0, 1; 1, -δ] : Matrix (Fin 2) (Fin 2) ℝ)
      (((-δ + σ * √(δ ^ 2 + 4)) / 2 : ℝ) : ℂ)).det = 0 := by
  rw [Criteria.det_characteristicMatrix_fin_two]
  have hs : √(δ ^ 2 + 4) ^ 2 = δ ^ 2 + 4 := Real.sq_sqrt (by positivity)
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  simp only [Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  have : ((-δ + σ * √(δ ^ 2 + 4)) / 2) ^ 2 - (0 + -δ) * ((-δ + σ * √(δ ^ 2 + 4)) / 2) +
      (0 * -δ - 1 * 1) = 0 := by
    linear_combination (σ ^ 2 / 4) * hs + ((δ ^ 2 + 4) / 4) * hσ2
  exact_mod_cast this

/-- The origin is a saddle (`det = −1 < 0`), hence unstable, for every damping. -/
@[powerlib_foundation] theorem origin_unstable (δ : ℝ) : Unstable (field δ) (mk 0 0) := by
  refine Criteria.unstable_of_jacobian_det_neg_fin_two _ (field_contDiff δ) ?_
    (hasFDerivAt_field δ (mk 0 0)).fderiv ?_
  · rw [field_eq_zero_iff]; simp
  · simp [Matrix.det_fin_two]

/-- With damping `δ > 0` the wells `(±1, 0)` are locally exponentially stable. -/
@[powerlib_foundation] theorem well_locallyExponentiallyStable {δ : ℝ} (hδ : 0 < δ) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) : LocallyExponentiallyStable (field δ) (mk σ 0) := by
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine Criteria.locallyExponentiallyStable_of_jacobian_fin_two _ (field_contDiff δ) ?_
    (hasFDerivAt_field δ (mk σ 0)).fderiv ?_ ?_
  · rw [field_eq_zero_iff]; simp only [mk_apply_zero, mk_apply_one, true_and]
    rcases hσ with rfl | rfl <;> norm_num
  · simp [Matrix.trace_fin_two]; linarith
  · simp [Matrix.det_fin_two, hσ2]

/-- For every `δ ≥ 0` the wells `(±1, 0)` are Lyapunov stable (strict minima of `V`). -/
@[powerlib_foundation] theorem well_lyapunovStable {δ : ℝ} (hδ : 0 ≤ δ) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) : LyapunovStable (field δ) (mk σ 0) := by
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine Conservative.center_lyapunovStable one_pos hδ hasDerivAt_potential one_pos ?_
  intro x hx hne
  have hdiff : potential x - potential σ = (x - σ) ^ 2 * (x + σ) ^ 2 / 4 := by
    unfold potential
    have h4 : σ ^ 4 = 1 := by rw [show σ ^ 4 = (σ ^ 2) ^ 2 by ring, hσ2]; norm_num
    rw [h4, hσ2]
    have : (x - σ) ^ 2 * (x + σ) ^ 2 = (x ^ 2 - σ ^ 2) ^ 2 := by ring
    rw [this, hσ2]; ring
  have h1 : 0 < (x - σ) ^ 2 := by
    have : x - σ ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have h2 : 0 < (x + σ) ^ 2 := by
    have : x + σ ≠ 0 := by
      intro h
      have : |x - σ| = 2 * |σ| := by
        rw [show x - σ = -(2 * σ) by linarith, abs_neg, abs_mul, abs_two]
      have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
      rw [hσabs] at this
      linarith
    positivity
  have : 0 < potential x - potential σ := by rw [hdiff]; positivity
  linarith

/-- Energy is conserved in the undamped case. -/
@[powerlib_foundation] theorem energy_conserved {φ : ℝ → State 2} {a b : ℝ}
    (hφ : IsTrajectoryOn φ (field 0) a b) :
    ∀ t ∈ Icc a b, energy (φ t) = energy (φ a) :=
  Conservative.energy_conserved one_ne_zero hasDerivAt_potential hφ

@[powerlib_foundation] theorem energy_well (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    energy (mk σ 0) = -(1 / 4) := by
  rcases hσ with rfl | rfl <;> simp [energy, Conservative.energy, potential] <;> norm_num

@[powerlib_foundation] theorem energy_continuous : Continuous energy :=
  (Conservative.energy_differentiable (m := 1) hasDerivAt_potential).continuous

/-- Conservative case: a forward solution whose energy differs from that of the well never
converges to the well. -/
@[powerlib_foundation] theorem not_tendsto_of_energy_ne {φ : ℝ → State 2} {t₀ : ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ y => field 0 y) (Ici t₀)) {x : State 2}
    (hE : energy (φ t₀) ≠ energy x) : ¬ Tendsto φ atTop (𝓝 x) := by
  intro hlim
  have hconst : ∀ t, t₀ ≤ t → energy (φ t) = energy (φ t₀) := by
    intro t ht
    exact energy_conserved (hφ.mono (Icc_subset_Ici_self)) t ⟨ht, le_rfl⟩
  have h1 : Tendsto (fun t => energy (φ t)) atTop (𝓝 (energy x)) :=
    (energy_continuous.tendsto x).comp hlim
  have h2 : Tendsto (fun t => energy (φ t)) atTop (𝓝 (energy (φ t₀))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop t₀] with t ht
    exact (hconst t ht).symm
  exact hE (tendsto_nhds_unique h2 h1)

/-- Arbitrarily close to a well there are states with a different energy:
`E(σ, s) = s²/2 − 1/4 ≠ −1/4` for `s ≠ 0`. -/
@[powerlib_foundation] theorem energy_off_well (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) {s : ℝ}
    (hs : s ≠ 0) : energy (mk σ s) ≠ energy (mk σ 0) ∧ ‖mk σ s - mk σ 0‖ = |s| := by
  constructor
  · rw [energy_well σ hσ]
    have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
    have hσ4 : σ ^ 4 = 1 := by rw [show σ ^ 4 = (σ ^ 2) ^ 2 by ring, hσ2]; norm_num
    simp only [energy, Conservative.energy, potential, mk_apply_zero, mk_apply_one, hσ2, hσ4]
    have : 0 < s ^ 2 := by positivity
    intro h; linarith
  · rw [mk_sub, norm_mk]; simp [Real.sqrt_sq_eq_abs]

/-- `dE/dt = −δ y² ≤ 0` for `δ ≥ 0`. -/
@[powerlib_foundation] theorem energy_lie_nonpos {δ : ℝ} (hδ : 0 ≤ δ) (y : State 2) :
    fderiv ℝ energy y (field δ y) ≤ 0 := by
  rw [energy, field, Conservative.energy_lie one_ne_zero hasDerivAt_potential]
  nlinarith [sq_nonneg (y 1)]

/-- Energy sublevel sets are compact (`‖y‖² ≤ 2c + 9/2` on `{E ≤ c}`). -/
@[powerlib_foundation] theorem energy_sublevel_compact (c : ℝ) :
    IsCompact {y : State 2 | energy y ≤ c} := by
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_le energy_continuous continuous_const)
  rw [Metric.isBounded_iff_subset_closedBall (0 : State 2)]
  refine ⟨√(max (2 * c + 9 / 2) 0), fun y hy => ?_⟩
  simp only [Set.mem_ofPred_eq, energy, Conservative.energy, potential] at hy
  rw [Metric.mem_closedBall, dist_zero_right]
  have hsq : ‖y‖ ^ 2 ≤ max (2 * c + 9 / 2) 0 := by
    rw [norm_sq_eq]
    have := sq_nonneg (y 0 ^ 2 - 3)
    exact le_max_of_le_left (by nlinarith [sq_nonneg (y 1)])
  calc ‖y‖ = √(‖y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg y)).symm
    _ ≤ √(max (2 * c + 9 / 2) 0) := Real.sqrt_le_sqrt hsq

/-- Every initial state has a forward solution for `δ ≥ 0`. -/
@[powerlib_foundation] theorem forwardComplete {δ : ℝ} (hδ : 0 ≤ δ) :
    Flow.ForwardComplete (field δ) :=
  Flow.forwardComplete_of_compact_sublevel (field_contDiff δ)
    (Conservative.energy_differentiable hasDerivAt_potential) (energy_lie_nonpos hδ)
    energy_sublevel_compact

/-- Correction: without damping the wells are not asymptotically stable — there is no attractor
whose basin a separatrix could bound. -/
@[powerlib_foundation] theorem not_localAsymptoticStable_conservative (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) : ¬ LocalAsymptoticStable (field 0) (mk σ 0) := by
  rintro ⟨-, c, hc, hconv⟩
  obtain ⟨hne, hdist⟩ := energy_off_well σ hσ (s := c / 2) (by positivity)
  obtain ⟨φ, hφ0, hφ⟩ := forwardComplete le_rfl 0 (mk σ (c / 2))
  have hlim := hconv 0 φ hφ (by rw [hφ0, hdist, abs_of_pos (by positivity)]; linarith)
  exact not_tendsto_of_energy_ne hφ (by rw [hφ0]; exact hne) hlim

end powerlib.PhasePlane.Duffing
