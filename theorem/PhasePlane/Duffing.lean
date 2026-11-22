import theorem.PhasePlane.Conservative
import theorem.Criteria.Hurwitz2
import theorem.Flow.Certificate
import theorem.Potential.DoubleWell

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
* Linearization through `Conservative.jacobian 1 δ (3x² − 1)` (`V'' = 3x² − 1`,
  `hasDerivAt_force`).
* Saddle at the origin: characteristic roots `(−δ ± √(δ² + 4))/2` (`saddle_eigenvalues`), and
  the origin is unstable for every `δ` (`origin_unstable`, `V''(0) = −1 < 0`,
  `Conservative.unstable_of_slope_neg`).
* Wells `(±1, 0)`: locally exponentially stable for `δ > 0` (`V''(±1) = 2 > 0`;
  `well_locallyExponentiallyStable` from `Conservative.locallyExponentiallyStable_of_slope_pos`);
  Lyapunov stable for every `δ ≥ 0` (strict minima of `V`, `Potential.doubleWell_eq_min_iff`;
  energy as Lyapunov function; `well_lyapunovStable`).
* Forward completeness for `δ ≥ 0` (`forwardComplete`): the energy has compact sublevel sets and
  is nonincreasing (`Conservative.energy_lie_nonpos`; powerlib
  `forwardComplete_of_compact_sublevel`). The field is smooth by `Conservative.field_contDiff`
  (`force_contDiff`).
* Conservative case `δ = 0`: energy is conserved (`Conservative.energy_conserved` with `m = 1`,
  `V = x⁴/4 − x²/2`, `hasDerivAt_potential`), and a forward solution
  whose energy differs from `E(±1, 0) = −1/4` can never converge to `(±1, 0)`
  (`not_tendsto_of_energy_ne`); points with this property exist arbitrarily close to the wells
  (`energy_off_well`, at distance `|s|` by `norm_mk_sub_mk_zero`). Hence the wells are not
  locally asymptotically stable (`not_localAsymptoticStable_conservative`): there is no
  attractor.

Potential shapes: `V(x) = x⁴/4 − x²/2` is the double well `Potential.doubleWell 1 1` of
`theorem/Potential/DoubleWell.lean` (wells `±1`, minimum `−1/4`, barrier `a²/4b = 1/4`); the same
quartic is the supercritical pitchfork potential of `theorem/NormalForm/Pitchfork.lean` at `μ = 1`.

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

/-- Double-well potential `V(x) = x⁴/4 − x²/2`: the double well `Potential.doubleWell 1 1`. -/
abbrev potential : ℝ → ℝ := Potential.doubleWell 1 1

/-- The Duffing field `ẋ = y`, `ẏ = x − x³ − δy`. -/
def field (δ : ℝ) : State 2 → State 2 := Conservative.field 1 δ force

/-- Energy `y²/2 + x⁴/4 − x²/2`. -/
def energy : State 2 → ℝ := Conservative.energy 1 potential

@[tmio T, powerlib_foundation] theorem hasDerivAt_potential (x : ℝ) :
    HasDerivAt potential (force x) x :=
  (Potential.hasDerivAt_doubleWell 1 1 x).congr_deriv (by unfold force; ring)

@[tmio T, powerlib_foundation] theorem force_contDiff {k : WithTop ℕ∞} : ContDiff ℝ k force := by
  unfold force; fun_prop

@[tmio M, powerlib_foundation] theorem field_eq_zero_iff (δ : ℝ) (y : State 2) :
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

/-- `V''(x) = 3x² − 1`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_force (x : ℝ) :
    HasDerivAt force (3 * x ^ 2 - 1) x := by
  show HasDerivAt (fun y => y ^ 3 - y) _ x
  convert (hasDerivAt_pow 3 x).fun_sub (hasDerivAt_id' x)

/-- The characteristic roots at the saddle are `(−δ ± √(δ² + 4))/2`. -/
@[tmio T, powerlib_foundation] theorem saddle_eigenvalues (δ : ℝ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
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

/-- The origin is a saddle (`V''(0) = −1 < 0`), hence unstable, for every damping
(`Conservative.unstable_of_slope_neg`). -/
@[tmio TM, powerlib_foundation] theorem origin_unstable (δ : ℝ) : Unstable (field δ) (mk 0 0) :=
  Conservative.unstable_of_slope_neg one_pos force_contDiff (by simp [force])
    (hasDerivAt_force 0) (by norm_num)

/-- With damping `δ > 0` the wells `(±1, 0)` (`V''(±1) = 2 > 0`) are locally exponentially
stable (`Conservative.locallyExponentiallyStable_of_slope_pos`). -/
@[tmio TM, powerlib_foundation] theorem well_locallyExponentiallyStable {δ : ℝ} (hδ : 0 < δ) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) : LocallyExponentiallyStable (field δ) (mk σ 0) := by
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine Conservative.locallyExponentiallyStable_of_slope_pos one_pos hδ force_contDiff ?_
    (hasDerivAt_force σ) (by rw [hσ2]; norm_num)
  rcases hσ with rfl | rfl <;> norm_num [force]

/-- For every `δ ≥ 0` the wells `(±1, 0)` are Lyapunov stable (strict minima of `V`). -/
@[tmio TM, powerlib_foundation] theorem well_lyapunovStable {δ : ℝ} (hδ : 0 ≤ δ) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) : LyapunovStable (field δ) (mk σ 0) := by
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine Conservative.center_lyapunovStable one_pos hδ hasDerivAt_potential one_pos ?_
  intro x hx hne
  have h1 : √((1 : ℝ) / 1) = 1 := by simp
  have hσm := (Potential.doubleWell_eq_min_iff one_pos one_pos σ).mpr (by rw [h1]; exact hσ)
  show Potential.doubleWell 1 1 σ < Potential.doubleWell 1 1 x
  rw [hσm]
  refine lt_of_le_of_ne (Potential.doubleWell_min one_pos x) fun h => ?_
  have hx' := (Potential.doubleWell_eq_min_iff one_pos one_pos x).mp h.symm
  rw [h1] at hx'
  rcases hσ with rfl | rfl <;> rcases hx' with rfl | rfl <;>
    first | exact absurd rfl hne | norm_num at hx

@[tmio M, powerlib_foundation] theorem energy_well (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    energy (mk σ 0) = -(1 / 4) := by
  rcases hσ with rfl | rfl <;> simp [energy, Conservative.energy, Potential.doubleWell] <;>
    norm_num

@[tmio T, powerlib_foundation] theorem energy_continuous : Continuous energy :=
  (Conservative.energy_differentiable (m := 1) hasDerivAt_potential).continuous

/-- Conservative case: a forward solution whose energy differs from that of the well never
converges to the well. -/
@[tmio TM, powerlib_foundation] theorem not_tendsto_of_energy_ne {φ : ℝ → State 2} {t₀ : ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ y => field 0 y) (Ici t₀)) {x : State 2}
    (hE : energy (φ t₀) ≠ energy x) : ¬ Tendsto φ atTop (𝓝 x) := by
  intro hlim
  have hconst : ∀ t, t₀ ≤ t → energy (φ t) = energy (φ t₀) := by
    intro t ht
    exact Conservative.energy_conserved one_ne_zero hasDerivAt_potential
      (hφ.mono (Icc_subset_Ici_self)) t ⟨ht, le_rfl⟩
  have h1 : Tendsto (fun t => energy (φ t)) atTop (𝓝 (energy x)) :=
    (energy_continuous.tendsto x).comp hlim
  have h2 : Tendsto (fun t => energy (φ t)) atTop (𝓝 (energy (φ t₀))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop t₀] with t ht
    exact (hconst t ht).symm
  exact hE (tendsto_nhds_unique h2 h1)

/-- Off a well there are states with a different energy:
`E(σ, s) = s²/2 − 1/4 ≠ −1/4` for `s ≠ 0` (at distance `|s|`, `norm_mk_sub_mk_zero`). -/
@[tmio M, powerlib_foundation] theorem energy_off_well (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) {s : ℝ}
    (hs : s ≠ 0) : energy (mk σ s) ≠ energy (mk σ 0) := by
  rw [energy_well σ hσ]
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ4 : σ ^ 4 = 1 := by rw [show σ ^ 4 = (σ ^ 2) ^ 2 by ring, hσ2]; norm_num
  simp only [energy, Conservative.energy, Potential.doubleWell, mk_apply_zero, mk_apply_one, hσ2,
    hσ4]
  have : 0 < s ^ 2 := by positivity
  intro h; linarith

/-- The state `(σ, s)` lies at distance `|s|` from `(σ, 0)`. -/
@[tmio T, powerlib_foundation] theorem norm_mk_sub_mk_zero (σ s : ℝ) :
    ‖mk σ s - mk σ 0‖ = |s| := by
  rw [mk_sub, norm_mk]; simp [Real.sqrt_sq_eq_abs]

/-- Energy sublevel sets are compact (`‖y‖² ≤ 2c + 9/2` on `{E ≤ c}`). -/
@[tmio T, powerlib_foundation] theorem energy_sublevel_compact (c : ℝ) :
    IsCompact {y : State 2 | energy y ≤ c} := by
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_le energy_continuous continuous_const)
  rw [Metric.isBounded_iff_subset_closedBall (0 : State 2)]
  refine ⟨√(max (2 * c + 9 / 2) 0), fun y hy => ?_⟩
  simp only [Set.mem_ofPred_eq, energy, Conservative.energy, Potential.doubleWell] at hy
  rw [Metric.mem_closedBall, dist_zero_right]
  have hsq : ‖y‖ ^ 2 ≤ max (2 * c + 9 / 2) 0 := by
    rw [norm_sq_eq]
    have := sq_nonneg (y 0 ^ 2 - 3)
    exact le_max_of_le_left (by nlinarith [sq_nonneg (y 1)])
  calc ‖y‖ = √(‖y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg y)).symm
    _ ≤ √(max (2 * c + 9 / 2) 0) := Real.sqrt_le_sqrt hsq

/-- Every initial state has a forward solution for `δ ≥ 0`. -/
@[tmio TM, powerlib_foundation] theorem forwardComplete {δ : ℝ} (hδ : 0 ≤ δ) :
    Flow.ForwardComplete (field δ) :=
  Flow.forwardComplete_of_compact_sublevel (Conservative.field_contDiff force_contDiff)
    (Conservative.energy_differentiable hasDerivAt_potential)
    (Conservative.energy_lie_nonpos one_ne_zero hδ hasDerivAt_potential) energy_sublevel_compact

/-- Correction: without damping the wells are not asymptotically stable — there is no attractor
whose basin a separatrix could bound. -/
@[tmio TM, powerlib_foundation] theorem not_localAsymptoticStable_conservative (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) : ¬ LocalAsymptoticStable (field 0) (mk σ 0) := by
  rintro ⟨-, c, hc, hconv⟩
  have hne := energy_off_well σ hσ (s := c / 2) (by positivity)
  have hdist := norm_mk_sub_mk_zero σ (c / 2)
  obtain ⟨φ, hφ0, hφ⟩ := forwardComplete le_rfl 0 (mk σ (c / 2))
  have hlim := hconv 0 φ hφ (by rw [hφ0, hdist, abs_of_pos (by positivity)]; linarith)
  exact not_tendsto_of_energy_ne hφ (by rw [hφ0]; exact hne) hlim

end powerlib.PhasePlane.Duffing
