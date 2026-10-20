import theorem.PhasePlane.Planar

/-! # Second-order mechanical systems `m ẍ + γ ẋ + V'(x) = 0`

The common phase-plane model behind the pendulum, Duffing and washboard examples: energy balance,
equilibria and Lyapunov stability at strict minima of the potential.

Model boundary.
* State `y = (x, v) = (y 0, y 1) ∈ State 2` with `v = ẋ`; constant mass `m > 0`, constant linear
  damping `γ` (`γ = 0` conservative), potential `V : ℝ → ℝ` with everywhere derivative
  `dV = V'`. The vector field is exactly `ẋ = v`, `v̇ = (−γ v − V'(x)) / m` (`field`; continuous
  time, no input, noise or saturation). Energy `E = m v²/2 + V(x)` (`energy`).
* A canonical textbook system with a caller-supplied potential: no model family; foundation
  results.

Source: work-sync theory/T-nonlinear-phase-plane.md §1.1, §1.2, §1.7,
theory/T-dynamical-systems.md §1.2.

Results.
* Phase-trajectory slope (`phase_slope`): where a trajectory is locally a graph `v = Φ(x)` with
  `v ≠ 0`, `Φ'(x) = v̇ / v = f(x, v) / v`.
* Energy balance `dE/dt = −γ v²` along every solution (`energy_lie`,
  `energy_hasDerivWithinAt`); conservation for `γ = 0` (`energy_conserved`), monotone decay for
  `γ ≥ 0` (`energy_antitone`).
* Equilibria are `(x*, 0)` with `V'(x*) = 0` (`field_eq_zero_iff`).
* A strict local minimum `x*` of `V` gives a Lyapunov-stable equilibrium `(x*, 0)` for `γ ≥ 0`
  (energy as local Lyapunov function; LeanForControl `lyapunov_stable`;
  `center_lyapunovStable`).
-/

noncomputable section
namespace powerlib.PhasePlane.Conservative
open Set Filter Topology
open powerlib.Dynamics (State)

/-- `ẋ = v`, `v̇ = (−γ v − V'(x)) / m`. -/
def field (m γ : ℝ) (dV : ℝ → ℝ) (y : State 2) : State 2 :=
  mk (y 1) ((-γ * y 1 - dV (y 0)) / m)

/-- Mechanical energy `m v²/2 + V(x)`. -/
def energy (m : ℝ) (V : ℝ → ℝ) (y : State 2) : ℝ := m * y 1 ^ 2 / 2 + V (y 0)

@[simp, powerlib_foundation] theorem field_apply_zero (m γ : ℝ) (dV : ℝ → ℝ) (y : State 2) :
    field m γ dV y 0 = y 1 := rfl

@[simp, powerlib_foundation] theorem field_apply_one (m γ : ℝ) (dV : ℝ → ℝ) (y : State 2) :
    field m γ dV y 1 = (-γ * y 1 - dV (y 0)) / m := rfl

@[powerlib_foundation] theorem field_contDiff {m γ : ℝ} {dV : ℝ → ℝ} {k : WithTop ℕ∞}
    (hdV : ContDiff ℝ k dV) : ContDiff ℝ k (field m γ dV) := by
  refine Dynamics.contDiff_of_components (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · exact Dynamics.contDiff_coord 1
  · have h0 : ContDiff ℝ k (fun y : State 2 => y 0) := Dynamics.contDiff_coord 0
    have h1 : ContDiff ℝ k (fun y : State 2 => y 1) := Dynamics.contDiff_coord 1
    exact (((h1.const_smul (-γ)).sub (hdV.comp h0)).div_const m)

@[powerlib_foundation] theorem field_eq_zero_iff {m γ : ℝ} {dV : ℝ → ℝ} (hm : m ≠ 0) (y : State 2) :
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

@[powerlib_foundation] theorem hasFDerivAt_energy {m : ℝ} {V dV : ℝ → ℝ}
    (hV : ∀ x, HasDerivAt V (dV x) x) (y : State 2) :
    HasFDerivAt (energy m V) (dV (y 0) • Dynamics.coord 0 + (m * y 1) • Dynamics.coord 1) y := by
  have h0 := Dynamics.hasFDerivAt_coord 0 y
  have h1 := Dynamics.hasFDerivAt_coord 1 y
  have h : HasFDerivAt (fun z : State 2 => m / 2 * z 1 ^ 2 + V (z 0)) _ y :=
    ((h1.pow 2).const_mul (m / 2)).add ((hV (y 0)).comp_hasFDerivAt y h0)
  have hf : energy m V = fun z : State 2 => m / 2 * z 1 ^ 2 + V (z 0) := by
    funext z; simp only [energy]; ring
  rw [hf]
  convert h using 1
  ext v
  simp
  ring

@[powerlib_foundation] theorem energy_differentiable {m : ℝ} {V dV : ℝ → ℝ}
    (hV : ∀ x, HasDerivAt V (dV x) x) : Differentiable ℝ (energy m V) :=
  fun y => (hasFDerivAt_energy hV y).differentiableAt

/-- Energy balance: the Lie derivative of `E` is `−γ v²`. -/
@[powerlib_foundation] theorem energy_lie {m γ : ℝ} {V dV : ℝ → ℝ} (hm : m ≠ 0)
    (hV : ∀ x, HasDerivAt V (dV x) x) (y : State 2) :
    fderiv ℝ (energy m V) y (field m γ dV y) = -γ * y 1 ^ 2 := by
  rw [(hasFDerivAt_energy hV y).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, Dynamics.coord_apply,
    field_apply_zero, field_apply_one, smul_eq_mul]
  field_simp
  ring

/-- Along every solution, `dE/dt = −γ v²`. -/
@[powerlib_foundation] theorem energy_hasDerivWithinAt {m γ : ℝ} {V dV : ℝ → ℝ} (hm : m ≠ 0)
    (hV : ∀ x, HasDerivAt V (dV x) x) {φ : ℝ → State 2} {s : Set ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ y => field m γ dV y) s) {t : ℝ} (ht : t ∈ s) :
    HasDerivWithinAt (fun τ => energy m V (φ τ)) (-γ * φ t 1 ^ 2) s t := by
  have h := (hasFDerivAt_energy (m := m) hV (φ t)).comp_hasDerivWithinAt t (hφ t ht)
  rw [← energy_lie (γ := γ) hm hV, (hasFDerivAt_energy hV (φ t)).fderiv]
  exact h

/-- Conservative case: the energy is constant along every solution segment. -/
@[powerlib_foundation] theorem energy_conserved {m : ℝ} {V dV : ℝ → ℝ} (hm : m ≠ 0)
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

/-- Damped case `γ ≥ 0`: the energy is nonincreasing along every solution segment. -/
@[powerlib_foundation] theorem energy_antitone {m γ : ℝ} {V dV : ℝ → ℝ} (hm : m ≠ 0) (hγ : 0 ≤ γ)
    (hV : ∀ x, HasDerivAt V (dV x) x) {φ : ℝ → State 2} {a b : ℝ}
    (hφ : IsTrajectoryOn φ (field m γ dV) a b) :
    AntitoneOn (fun t => energy m V (φ t)) (Icc a b) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    (f' := fun t => -γ * φ t 1 ^ 2)
  · exact fun t ht => (energy_hasDerivWithinAt hm hV hφ ht).continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact ((energy_hasDerivWithinAt hm hV hφ (Ioo_subset_Icc_self ht)).mono
      Ioo_subset_Icc_self).mono_of_mem_nhdsWithin (by rw [interior_Icc]; exact self_mem_nhdsWithin)
  · intro t _
    have := sq_nonneg (φ t 1)
    nlinarith

/-- Slope of a phase trajectory: if `v = Φ(x)` near `t` and `v(t) ≠ 0`, then
`Φ'(x(t)) = v̇(t) / v(t)`. -/
@[powerlib_foundation] theorem phase_slope {x v Φ : ℝ → ℝ} {t a Φ' : ℝ}
    (hx : HasDerivAt x (v t) t) (hv : HasDerivAt v a t)
    (hgraph : v =ᶠ[𝓝 t] fun τ => Φ (x τ)) (hΦ : HasDerivAt Φ Φ' (x t)) (hv0 : v t ≠ 0) :
    Φ' = a / v t := by
  have h1 : HasDerivAt (fun τ => Φ (x τ)) (Φ' * v t) t := hΦ.comp t hx
  have h2 : HasDerivAt (fun τ => Φ (x τ)) a t := hv.congr_of_eventuallyEq hgraph.symm
  rw [h1.unique h2 |>.symm]
  field_simp

/-- A strict local minimum `x*` of `V` (with `V'(x*) = 0`) gives a Lyapunov-stable equilibrium
`(x*, 0)` for any damping `γ ≥ 0`. -/
@[powerlib_foundation] theorem center_lyapunovStable {m γ : ℝ} {V dV : ℝ → ℝ} (hm : 0 < m)
    (hγ : 0 ≤ γ) (hV : ∀ x, HasDerivAt V (dV x) x) {x₀ r : ℝ} (hr : 0 < r)
    (hmin : ∀ x, |x - x₀| < r → x ≠ x₀ → V x₀ < V x) :
    LyapunovStable (field m γ dV) (mk x₀ 0) := by
  refine _root_.lyapunov_stable (D := {y : State 2 | |y 0 - x₀| < r})
    (V := fun y => energy m V y - V x₀) (by norm_num) ?_
  have hE := energy_differentiable (m := m) hV
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : Continuous fun y : State 2 => |y 0 - x₀| :=
      ((Dynamics.coord 0).continuous.sub continuous_const).abs
    exact isOpen_lt hc continuous_const
  · simp [hr]
  · exact hE.continuous.sub continuous_const
  · exact hE.sub_const _
  · simp [energy]
  · intro y hy hne
    simp only [energy]
    have hv2 : 0 ≤ m * y 1 ^ 2 / 2 := by positivity
    by_cases hx : y 0 = x₀
    · have hv : y 1 ≠ 0 := by
        intro h1; apply hne; rw [← mk_coords y, hx, h1]
      have : 0 < m * y 1 ^ 2 / 2 := by positivity
      rw [hx]; linarith
    · have := hmin (y 0) hy hx
      linarith
  · intro y _
    have h : fderiv ℝ (fun y => energy m V y - V x₀) y = fderiv ℝ (energy m V) y :=
      fderiv_sub_const _
    rw [h, energy_lie hm.ne' hV]
    have := sq_nonneg (y 1)
    nlinarith

end powerlib.PhasePlane.Conservative
