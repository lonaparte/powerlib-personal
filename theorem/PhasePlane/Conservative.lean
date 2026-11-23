import theorem.PhasePlane.Planar
import theorem.PH.Nonlinear

/-! # Second-order mechanical systems `m ẍ + γ ẋ + V'(x) = 0`

The common phase-plane model behind the pendulum, Duffing and washboard examples: energy balance,
equilibria and Lyapunov stability at strict minima of the potential.

Model boundary.
* State `y = (x, v) = (y 0, y 1) ∈ State 2` with `v = ẋ`; constant mass `m > 0`, constant linear
  damping `γ` (`γ = 0` conservative), potential `V : ℝ → ℝ` with everywhere derivative
  `dV = V'`. The vector field is exactly `ẋ = v`, `v̇ = (−γ v − V'(x)) / m` (`field`; continuous
  time, no input, noise or saturation). Energy `E = V(x) + m v²/2` (`energy`), the case
  `k = m`, `b = 0` of the separable energy `U(x) + (k/2)(v − b)²` (`separableEnergy`).
* A canonical textbook system with a caller-supplied potential: no model family; foundation
  results.

Source: work-sync theory/T-nonlinear-phase-plane.md §1.1, §1.2, §1.7,
theory/T-dynamical-systems.md §1.2.

Results.
* Separable energy `E = U(x) + (k/2)(v − b)²` (`separableEnergy`; the mechanical energy, the PI-PLL
  energy and the classical-machine Hamiltonian read it): derivative and gradient
  `(U'(x), k (v − b))` (`hasFDerivAt_separableEnergy`, `hasGradientAt_separableEnergy`),
  smoothness (`contDiff_separableEnergy`, `differentiable_separableEnergy`), and a strict local
  minimum at `(x*, b)` when `x*` is one of `U` and `k > 0` (`eventually_separableEnergy_lt`).
* Phase-trajectory slope (`phase_slope`): where a trajectory is locally a graph `v = Φ(x)` with
  `v ≠ 0`, `Φ'(x) = v̇ / v = f(x, v) / v`.
* Port-Hamiltonian form (`toPH`, `γ ≥ 0`): `J = [[0, 1/m], [−1/m, 0]]`, `R = diag(0, γ/m²)`,
  `H = energy`, `∇H = (V'(x), m v)`, no ports; its zero-input field is `field`
  (`toPH_zeroInputField`, `m ≠ 0`). Static identity between two mathematical models (no family,
  no connection statement).
* Energy balance `dE/dt = −γ v²` along every solution (`energy_lie`,
  `energy_hasDerivWithinAt`); conservation for `γ = 0` (`energy_conserved`), monotone decay for
  `γ ≥ 0` (`energy_lie_nonpos`; `energy_antitone`, on every convex time set), read from the pH
  laws of `toPH`.
* Equilibria are `(x*, 0)` with `V'(x*) = 0` (`field_eq_zero_iff`).
* Linearization: the Jacobian at a point with `V'' = k` is `!![0, 1; −k/m, −γ/m]`
  (`jacobian`, `hasFDerivAt_field`; `tr = −γ/m`, `det = k/m`: `trace_jacobian`, `det_jacobian`);
  `m det(sI − J) = m s² + γ s + k` (`characteristic_polynomial_jacobian`), Hurwitz iff `γ, k > 0`
  (`isHurwitz_jacobian_iff`), damping ratio `γ / (2 √(m k))` (`dampingRatio_jacobian`), real
  eigenvalues iff `4 m k ≤ γ²` (`eigenvalues_real_iff_jacobian`); the swing-equation and damping
  class Jacobians are instances.
  At an equilibrium `(x*, 0)` with `m > 0`: `γ > 0` and `V''(x*) > 0` give local exponential
  stability (`locallyExponentiallyStable_of_slope_pos`); `V''(x*) < 0` a saddle
  (`unstable_of_slope_neg`, every `γ`); `γ < 0` instability (`unstable_of_damping_neg`, every
  `V''`).
* A strict local minimum `x*` of `V` gives a Lyapunov-stable equilibrium `(x*, 0)` for `γ ≥ 0`
  (a strict local minimum of the Hamiltonian of `toPH`, `eventually_separableEnergy_lt`,
  `PH.NonlinearModel.IsStrictLocalMin.lyapunovStable`; `center_lyapunovStable`).
-/

noncomputable section
namespace powerlib.PhasePlane.Conservative
open Set Filter Topology
open powerlib.Dynamics (State)

/-- `ẋ = v`, `v̇ = (−γ v − V'(x)) / m`. -/
def field (m γ : ℝ) (dV : ℝ → ℝ) (y : State 2) : State 2 :=
  mk (y 1) ((-γ * y 1 - dV (y 0)) / m)

/-- Separable energy `U(y₀) + (k/2)(y₁ − b)²`: a potential of the first coordinate plus a
quadratic in the second centred at `b`. The mechanical energy (`energy`: `k = m`, `b = 0`), the
PI-PLL energy (integrator set point `b`) and the classical-machine Hamiltonian (`k = 1/M`) are
readings of it. -/
def separableEnergy (U : ℝ → ℝ) (k b : ℝ) (y : State 2) : ℝ := U (y 0) + k / 2 * (y 1 - b) ^ 2

/-- Mechanical energy `V(x) + m v²/2`: the separable energy with `k = m`, `b = 0`. -/
abbrev energy (m : ℝ) (V : ℝ → ℝ) : State 2 → ℝ := separableEnergy V m 0

@[tmio T, simp, powerlib_foundation] theorem field_apply_zero (m γ : ℝ) (dV : ℝ → ℝ) (y : State 2) :
    field m γ dV y 0 = y 1 := rfl

@[tmio T, simp, powerlib_foundation] theorem field_apply_one (m γ : ℝ) (dV : ℝ → ℝ) (y : State 2) :
    field m γ dV y 1 = (-γ * y 1 - dV (y 0)) / m := rfl

@[tmio T, powerlib_foundation] theorem field_contDiff {m γ : ℝ} {dV : ℝ → ℝ} {k : WithTop ℕ∞}
    (hdV : ContDiff ℝ k dV) : ContDiff ℝ k (field m γ dV) := by
  refine contDiff_euclidean.2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · exact Dynamics.contDiff_coord 1
  · have h0 : ContDiff ℝ k (fun y : State 2 => y 0) := Dynamics.contDiff_coord 0
    have h1 : ContDiff ℝ k (fun y : State 2 => y 1) := Dynamics.contDiff_coord 1
    exact (((h1.const_smul (-γ)).sub (hdV.comp h0)).div_const m)

@[tmio T, powerlib_foundation] theorem field_eq_zero_iff {m γ : ℝ} {dV : ℝ → ℝ} (hm : m ≠ 0) (y : State 2) :
    field m γ dV y = 0 ↔ y 1 = 0 ∧ dV (y 0) = 0 := by
  rw [field, mk_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩
    rw [h1] at h2
    refine ⟨h1, ?_⟩
    have := (div_eq_zero_iff.mp h2).resolve_right hm
    linarith
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h1, h2]; simp⟩

/-! ## Linearization at an equilibrium -/

/-- Jacobian of `field m γ dV` at a point where `V'' = k`: `!![0, 1; −k/m, −γ/m]`. -/
def jacobian (m γ k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -k / m, -γ / m]

@[tmio T, powerlib_foundation] theorem trace_jacobian (m γ k : ℝ) :
    (jacobian m γ k).trace = -γ / m := by
  simp [jacobian, Matrix.trace_fin_two]

@[tmio T, powerlib_foundation] theorem det_jacobian (m γ k : ℝ) :
    (jacobian m γ k).det = k / m := by
  simp [jacobian, Matrix.det_fin_two]
  ring

/-- Characteristic polynomial of the mechanical Jacobian: `m det(sI − J) = m s² + γ s + k`. -/
@[tmio T, powerlib_foundation] theorem characteristic_polynomial_jacobian {m : ℝ} (hm : m ≠ 0)
    (γ k : ℝ) (s : ℂ) :
    (m : ℂ) * (Linear.characteristicMatrix (jacobian m γ k) s).det =
      (m : ℂ) * s ^ 2 + (γ : ℂ) * s + (k : ℂ) := by
  rw [Criteria.det_characteristicMatrix_fin_two, trace_jacobian, det_jacobian]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  push_cast
  field_simp
  ring

/-- The mechanical Jacobian is Hurwitz iff the damping and the stiffness are positive (`m > 0`;
`Criteria.isHurwitz_iff_of_coeffs_quadratic` for `m s² + γ s + k`). -/
@[tmio T, powerlib_foundation] theorem isHurwitz_jacobian_iff {m : ℝ} (hm : 0 < m) (γ k : ℝ) :
    LinearSystems.IsHurwitz (jacobian m γ k) ↔ 0 < γ ∧ 0 < k :=
  Criteria.isHurwitz_iff_of_coeffs_quadratic _ hm (trace_jacobian m γ k) (det_jacobian m γ k)

/-- Damping ratio of the mechanical Jacobian (`Criteria.dampingRatio`):
`ζ = γ / (2 √(m k))` (`m, k > 0`). -/
@[tmio T, powerlib_foundation] theorem dampingRatio_jacobian {m k : ℝ} (hm : 0 < m) (hk : 0 < k)
    (γ : ℝ) : Criteria.dampingRatio (jacobian m γ k) = γ / (2 * Real.sqrt (m * k)) := by
  have hs : Real.sqrt (k / m) = Real.sqrt (m * k) / m := by
    rw [show k / m = m * k / m ^ 2 by field_simp, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq hm.le]
  have hpos : 0 < Real.sqrt (m * k) := Real.sqrt_pos.mpr (mul_pos hm hk)
  rw [Criteria.dampingRatio, trace_jacobian, det_jacobian, hs]
  field_simp

open Matrix in
/-- All eigenvalues of the mechanical Jacobian are real iff `4 m k ≤ γ²` (`m > 0`; the
discriminant of `m s² + γ s + k`). -/
@[tmio T, powerlib_foundation] theorem eigenvalues_real_iff_jacobian {m : ℝ} (hm : 0 < m)
    (γ k : ℝ) :
    (∀ (μ : ℂ) (v : Fin 2 → ℂ), v ≠ 0 →
        (jacobian m γ k).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → μ.im = 0) ↔
      4 * m * k ≤ γ ^ 2 := by
  rw [Criteria.eigenvalues_real_iff_discriminant_nonneg, trace_jacobian, det_jacobian]
  have hm2 : 0 < m ^ 2 := by positivity
  have he : (-γ / m) ^ 2 - 4 * (k / m) = (γ ^ 2 - 4 * m * k) / m ^ 2 := by
    field_simp
  rw [he, div_nonneg_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · linarith
    · linarith
  · intro h; left; exact ⟨by linarith, hm2.le⟩

/-- The Jacobian of the field at `y` is `jacobian m γ k` for `k = V''(y 0)`. -/
@[tmio T, powerlib_foundation] theorem hasFDerivAt_field {m γ k : ℝ} {dV : ℝ → ℝ} {y : State 2}
    (hdV : HasDerivAt dV k (y 0)) :
    HasFDerivAt (field m γ dV)
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (jacobian m γ k)) y := by
  refine Dynamics.hasFDerivAt_toEuclideanCLM_of_components _
    ![Dynamics.coord 1, (-k / m) • Dynamics.coord 0 + (-γ / m) • Dynamics.coord 1] ?_ ?_
  · intro i; fin_cases i
    · exact Dynamics.hasFDerivAt_coord 1 y
    · show HasFDerivAt (fun z => field m γ dV z 1) _ y
      have h0 := Dynamics.hasFDerivAt_coord 0 y
      have h1 := Dynamics.hasFDerivAt_coord 1 y
      have h := ((h1.const_smul (-γ)).sub (hdV.comp_hasFDerivAt y h0)).const_smul m⁻¹
      refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
      · ext v; simp; ring
      · simp [field, div_eq_inv_mul]
  · intro i v; rw [Fin.sum_univ_two]; fin_cases i <;> simp [jacobian]

/-- Linearization at an equilibrium `(x*, 0)`: positive mass, positive damping and a potential
with `V''(x*) > 0` give local exponential stability (`tr = −γ/m < 0`, `det = V''/m > 0`). -/
@[tmio T, powerlib_foundation] theorem locallyExponentiallyStable_of_slope_pos {m γ k x₀ : ℝ}
    {dV : ℝ → ℝ} (hm : 0 < m) (hγ : 0 < γ) (hdV : ContDiff ℝ 1 dV) (h0 : dV x₀ = 0)
    (hk : HasDerivAt dV k x₀) (hpos : 0 < k) :
    LocallyExponentiallyStable (field m γ dV) (mk x₀ 0) :=
  Criteria.locallyExponentiallyStable_of_jacobian_fin_two _ (field_contDiff hdV)
    ((field_eq_zero_iff hm.ne' _).2 ⟨rfl, h0⟩) (hasFDerivAt_field hk).fderiv
    (by rw [trace_jacobian, neg_div]; exact neg_neg_of_pos (div_pos hγ hm))
    (by rw [det_jacobian]; exact div_pos hpos hm)

/-- Linearization at an equilibrium `(x*, 0)` with `V''(x*) < 0` (a potential maximum): a saddle
(`det = V''/m < 0`), unstable for every damping. -/
@[tmio T, powerlib_foundation] theorem unstable_of_slope_neg {m γ k x₀ : ℝ} {dV : ℝ → ℝ}
    (hm : 0 < m) (hdV : ContDiff ℝ 1 dV) (h0 : dV x₀ = 0) (hk : HasDerivAt dV k x₀)
    (hneg : k < 0) : Unstable (field m γ dV) (mk x₀ 0) :=
  Criteria.unstable_of_jacobian_det _ (field_contDiff hdV)
    ((field_eq_zero_iff hm.ne' _).2 ⟨rfl, h0⟩) (hasFDerivAt_field hk).fderiv
    (by rw [neg_one_sq, one_mul, det_jacobian]; exact div_neg_of_neg_of_pos hneg hm)

/-- Linearization at an equilibrium `(x*, 0)` with negative damping `γ < 0`: unstable
(`tr = −γ/m > 0`) for every potential curvature. -/
@[tmio T, powerlib_foundation] theorem unstable_of_damping_neg {m γ k x₀ : ℝ} {dV : ℝ → ℝ}
    (hm : 0 < m) (hγ : γ < 0) (hdV : ContDiff ℝ 1 dV) (h0 : dV x₀ = 0)
    (hk : HasDerivAt dV k x₀) : Unstable (field m γ dV) (mk x₀ 0) :=
  Criteria.unstable_of_jacobian_trace_pos _ (field_contDiff hdV)
    ((field_eq_zero_iff hm.ne' _).2 ⟨rfl, h0⟩) (hasFDerivAt_field hk).fderiv
    (by rw [trace_jacobian, neg_div]; exact neg_pos.mpr (div_neg_of_neg_of_pos hγ hm))

/-! ## The separable energy -/

/-- Where `U' = u` at `y₀`, the separable energy has the derivative `u dy₀ + k (y₁ − b) dy₁`. -/
@[tmio T, powerlib_foundation] theorem hasFDerivAt_separableEnergy {U : ℝ → ℝ} {u k b : ℝ}
    {y : State 2} (hU : HasDerivAt U u (y 0)) :
    HasFDerivAt (separableEnergy U k b)
      (u • Dynamics.coord 0 + (k * (y 1 - b)) • Dynamics.coord 1) y := by
  have h0 := Dynamics.hasFDerivAt_coord 0 y
  have h1 := Dynamics.hasFDerivAt_coord 1 y
  refine ((hU.comp_hasFDerivAt y h0).add
    (((h1.sub_const b).pow 2).const_mul (k / 2))).congr_fderiv ?_
  ext v
  simp
  ring

/-- The gradient of the separable energy: `∇E = (U'(y₀), k (y₁ − b))`. -/
@[tmio T, powerlib_foundation] theorem hasGradientAt_separableEnergy {U : ℝ → ℝ} {u k b : ℝ}
    {y : State 2} (hU : HasDerivAt U u (y 0)) :
    HasGradientAt (separableEnergy U k b) (mk u (k * (y 1 - b))) y :=
  PH.hasGradientAt_of_hasFDerivAt (hasFDerivAt_separableEnergy hU) fun v => by
    simp [mk, dotProduct, Fin.sum_univ_two]

@[tmio T, powerlib_foundation] theorem contDiff_separableEnergy {U : ℝ → ℝ} {n : WithTop ℕ∞}
    (hU : ContDiff ℝ n U) (k b : ℝ) : ContDiff ℝ n (separableEnergy U k b) :=
  (hU.comp (Dynamics.contDiff_coord 0)).add
    (contDiff_const.mul (((Dynamics.contDiff_coord 1).sub contDiff_const).pow 2))

@[tmio T, powerlib_foundation] theorem differentiable_separableEnergy {U : ℝ → ℝ}
    (hU : Differentiable ℝ U) (k b : ℝ) : Differentiable ℝ (separableEnergy U k b) :=
  fun y => (hasFDerivAt_separableEnergy (hU (y 0)).hasDerivAt).differentiableAt

/-- A strict local minimum `x₀` of `U` and `k > 0` make `(x₀, b)` a strict local minimum of the
separable energy: off `(x₀, b)` either `U` or the quadratic term increases. -/
@[tmio T, powerlib_foundation] theorem eventually_separableEnergy_lt {U : ℝ → ℝ} {k x₀ b : ℝ}
    (hk : 0 < k) (hU : ∀ᶠ x in 𝓝[≠] x₀, U x₀ < U x) :
    ∀ᶠ y in 𝓝[≠] mk x₀ b, separableEnergy U k b (mk x₀ b) < separableEnergy U k b y := by
  have h0 : Tendsto (fun y : State 2 => y 0) (𝓝 (mk x₀ b)) (𝓝 x₀) :=
    (Dynamics.contDiff_coord (k := 0) 0).continuous.tendsto' _ _ rfl
  rw [eventually_nhdsWithin_iff] at hU ⊢
  filter_upwards [h0.eventually hU] with y hy hne
  simp only [separableEnergy, mk_apply_zero, mk_apply_one, sub_self]
  have hq : 0 ≤ k / 2 * (y 1 - b) ^ 2 := by positivity
  by_cases hx : y 0 = x₀
  · have h1 : y 1 - b ≠ 0 := fun h1 =>
      hne (ext_iff'.2 ⟨by rw [hx, mk_apply_zero], by rw [mk_apply_one]; linarith⟩)
    have : 0 < k / 2 * (y 1 - b) ^ 2 := by positivity
    rw [hx]; linarith
  · have := hy hx
    linarith

/-! ## Port-Hamiltonian form -/

/-- The mechanical system as a nonlinear port-Hamiltonian system without ports, in
position–velocity coordinates: `J = [[0, 1/m], [−1/m, 0]]`, `R = diag(0, γ/m²)`, `H = energy`,
`∇H = (V'(x), m v)`. Its zero-input field is `field` (`toPH_zeroInputField`). -/
def toPH (m γ : ℝ) (V dV : ℝ → ℝ) (hγ : 0 ≤ γ) (hV : ∀ x, HasDerivAt V (dV x) x) :
    PH.NonlinearModel 2 0 where
  J _ := !![0, 1 / m; -(1 / m), 0]
  R _ := Matrix.diagonal ![0, γ / m ^ 2]
  g _ := 0
  H := energy m V
  dH y := mk (dV (y 0)) (m * y 1)
  skew _ := by ext i j; fin_cases i <;> fin_cases j <;> simp
  dissipation_posSemidef _ := Matrix.PosSemidef.diagonal fun i => by
    fin_cases i
    · simp
    · simpa using div_nonneg hγ (sq_nonneg m)
  hasGradient y := by simpa using hasGradientAt_separableEnergy (k := m) (b := 0) (hV (y 0))

/-- The zero-input field of the port-Hamiltonian form is `field` (`m ≠ 0`). -/
@[tmio T, powerlib_foundation] theorem toPH_zeroInputField {m γ : ℝ} {V dV : ℝ → ℝ} (hm : m ≠ 0)
    (hγ : 0 ≤ γ) (hV : ∀ x, HasDerivAt V (dV x) x) :
    (toPH m γ V dV hγ hV).zeroInputField = field m γ dV := by
  funext y
  ext i
  fin_cases i
  · simp [PH.NonlinearModel.zeroInputField_apply, toPH, field, mk, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, hm]
  · simp [PH.NonlinearModel.zeroInputField_apply, toPH, field, mk, Matrix.diagonal_vec2]
    field_simp
    ring

/-- Energy balance: the Lie derivative of `E` is `−γ v²`. -/
@[tmio T, powerlib_foundation] theorem energy_lie {m γ : ℝ} {V dV : ℝ → ℝ} (hm : m ≠ 0)
    (hV : ∀ x, HasDerivAt V (dV x) x) (y : State 2) :
    fderiv ℝ (energy m V) y (field m γ dV y) = -γ * y 1 ^ 2 := by
  rw [(hasFDerivAt_separableEnergy (k := m) (b := 0) (hV (y 0))).fderiv]
  simp only [sub_zero, _root_.add_apply, _root_.smul_apply, Dynamics.coord_apply,
    field_apply_zero, field_apply_one, smul_eq_mul]
  field_simp
  ring

/-- Along every solution, `dE/dt = −γ v²`. -/
@[tmio T, powerlib_foundation] theorem energy_hasDerivWithinAt {m γ : ℝ} {V dV : ℝ → ℝ} (hm : m ≠ 0)
    (hV : ∀ x, HasDerivAt V (dV x) x) {φ : ℝ → State 2} {s : Set ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ y => field m γ dV y) s) {t : ℝ} (ht : t ∈ s) :
    HasDerivWithinAt (fun τ => energy m V (φ τ)) (-γ * φ t 1 ^ 2) s t := by
  have hE := hasFDerivAt_separableEnergy (k := m) (b := 0) (hV (φ t 0))
  rw [← energy_lie (γ := γ) hm hV, hE.fderiv]
  exact hE.comp_hasDerivWithinAt t (hφ t ht)

/-- Conservative case: the energy is constant along every solution segment. -/
@[tmio T, powerlib_foundation] theorem energy_conserved {m : ℝ} {V dV : ℝ → ℝ} (hm : m ≠ 0)
    (hV : ∀ x, HasDerivAt V (dV x) x) {φ : ℝ → State 2} {a b : ℝ}
    (hφ : IsTrajectoryOn φ (field m 0 dV) a b) :
    ∀ t ∈ Icc a b, energy m V (φ t) = energy m V (φ a) := by
  have hc : ∀ t ∈ Icc a b, HasDerivWithinAt (fun τ => energy m V (φ τ)) 0 (Icc a b) t := by
    intro t ht
    simpa using energy_hasDerivWithinAt hm hV hφ ht
  intro t ht
  exact constant_of_has_deriv_right_zero
    (fun τ hτ => (hc τ hτ).continuousWithinAt)
    (fun τ hτ => ((hc τ (Ico_subset_Icc_self hτ)).mono (Icc_subset_Icc_left hτ.1))
      |>.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hτ.2)) t ht

/-- Damped case `γ ≥ 0`: the energy does not increase along the field, `Ė = −γ v² ≤ 0`
(`PH.NonlinearModel.zeroInput_lie_nonpos` of `toPH`). -/
@[tmio T, powerlib_foundation] theorem energy_lie_nonpos {m γ : ℝ} {V dV : ℝ → ℝ} (hm : m ≠ 0)
    (hγ : 0 ≤ γ) (hV : ∀ x, HasDerivAt V (dV x) x) (y : State 2) :
    fderiv ℝ (energy m V) y (field m γ dV y) ≤ 0 := by
  have h := (toPH m γ V dV hγ hV).zeroInput_lie_nonpos y
  rwa [toPH_zeroInputField hm] at h

/-- Damped case `γ ≥ 0`: the energy is nonincreasing along every solution on a convex time set
(a solution segment `Icc a b`, a forward ray `Ici a`, …;
`PH.NonlinearModel.energy_antitoneOn_of_isIntegralCurveOn` of `toPH`). -/
@[tmio T, powerlib_foundation] theorem energy_antitone {m γ : ℝ} {V dV : ℝ → ℝ} (hm : m ≠ 0)
    (hγ : 0 ≤ γ) (hV : ∀ x, HasDerivAt V (dV x) x) {φ : ℝ → State 2} {s : Set ℝ}
    (hs : Convex ℝ s) (hφ : IsIntegralCurveOn φ (fun _ y => field m γ dV y) s) :
    AntitoneOn (fun t => energy m V (φ t)) s :=
  (toPH m γ V dV hγ hV).energy_antitoneOn_of_isIntegralCurveOn hs
    (by rwa [toPH_zeroInputField hm])

/-- Slope of a phase trajectory: if `v = Φ(x)` near `t` and `v(t) ≠ 0`, then
`Φ'(x(t)) = v̇(t) / v(t)`. -/
@[tmio T, powerlib_foundation] theorem phase_slope {x v Φ : ℝ → ℝ} {t a Φ' : ℝ}
    (hx : HasDerivAt x (v t) t) (hv : HasDerivAt v a t)
    (hgraph : v =ᶠ[𝓝 t] fun τ => Φ (x τ)) (hΦ : HasDerivAt Φ Φ' (x t)) (hv0 : v t ≠ 0) :
    Φ' = a / v t := by
  have h1 : HasDerivAt (fun τ => Φ (x τ)) (Φ' * v t) t := hΦ.comp t hx
  have h2 : HasDerivAt (fun τ => Φ (x τ)) a t := hv.congr_of_eventuallyEq hgraph.symm
  rw [h1.unique h2 |>.symm]
  field_simp

/-- A strict local minimum `x*` of `V` gives a Lyapunov-stable equilibrium `(x*, 0)` for any
damping `γ ≥ 0`: `(x*, 0)` is a strict local minimum of the Hamiltonian of `toPH`
(`eventually_separableEnergy_lt`, `PH.NonlinearModel.IsStrictLocalMin.lyapunovStable`). -/
@[tmio T, powerlib_foundation] theorem center_lyapunovStable {m γ : ℝ} {V dV : ℝ → ℝ} (hm : 0 < m)
    (hγ : 0 ≤ γ) (hV : ∀ x, HasDerivAt V (dV x) x) {x₀ r : ℝ} (hr : 0 < r)
    (hmin : ∀ x, |x - x₀| < r → x ≠ x₀ → V x₀ < V x) :
    LyapunovStable (field m γ dV) (mk x₀ 0) := by
  rw [← toPH_zeroInputField hm.ne' hγ hV]
  refine PH.NonlinearModel.IsStrictLocalMin.lyapunovStable _ (eventually_separableEnergy_lt hm ?_)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds x₀ hr] with x hx hne
  exact hmin x (by rwa [Metric.mem_ball, Real.dist_eq] at hx) hne

end powerlib.PhasePlane.Conservative
