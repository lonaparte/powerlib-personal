import theorem.Dynamics.Stability
import theorem.Dynamics.LyapunovDefs

/-! Linearization is inconclusive at `σ = 0` (foundation, negative result).

Source: work-sync `theory/T-small-signal-stability.md` §1.6: "`σ_i = 0` 是临界情形——线性分析
不结论". Formalised as a pair of systems with the same equilibrium and the same (zero)
Jacobian whose nonlinear stability differs.

`cubicField c x = (c ‖x‖²) x` on `ℝⁿ` (`n ≥ 1`); for `n = 1` this is `ẋ = c x³`.
* Both fields are `C¹`, vanish at `0`, and have Jacobian `0` at `0` (every eigenvalue has real
  part `0`).
* `c = −1`: the origin is globally asymptotically stable (`cubic_neg_globallyAsymptoticallyStable`,
  strict Lyapunov function `‖x‖²`).
* `c = +1`: the origin is unstable (`cubic_pos_unstable`): from `x₀ = r e`, the explicit
  solution `x(t) = (1 − 2r²t)^{−1/2} x₀` reaches norm `1` at `t = (1 − r²)/(2r²)`.
* `linearization_inconclusive` packages both: no criterion that depends only on the Jacobian
  at the equilibrium can decide stability when the spectrum lies on the imaginary axis.
-/

noncomputable section
namespace powerlib.Modal
open powerlib.Dynamics

variable {n : ℕ}

/-- `ẋ = c ‖x‖² x`. -/
def cubicField (c : ℝ) (x : State n) : State n := (c * ‖x‖ ^ 2) • x

@[powerlib_foundation] theorem cubicField_zero (c : ℝ) : cubicField c (0 : State n) = 0 := by
  simp [cubicField]

@[powerlib_foundation] theorem cubicField_contDiff (c : ℝ) : ContDiff ℝ 1 (cubicField (n := n) c) :=
  (contDiff_const.mul (contDiff_norm_sq ℝ)).smul contDiff_id

/-- The Jacobian at the origin is the zero matrix. -/
@[powerlib_foundation] theorem cubicField_jacobian (c : ℝ) :
    fderiv ℝ (cubicField (n := n) c) 0 = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) 0 := by
  have hg : HasFDerivAt (fun x : State n => c * ‖x‖ ^ 2)
      (fderiv ℝ (fun x : State n => c * ‖x‖ ^ 2) 0) 0 :=
    ((contDiff_const.mul (contDiff_norm_sq ℝ) : ContDiff ℝ 1 (fun x : State n => c * ‖x‖ ^ 2)).differentiable one_ne_zero 0).hasFDerivAt
  have h := hg.smul (hasFDerivAt_id (0 : State n))
  rw [map_zero]
  have h0 : HasFDerivAt (cubicField (n := n) c) (0 : State n →L[ℝ] State n) 0 := by
    have hfun : cubicField (n := n) c = fun y => (c * ‖y‖ ^ 2) • id y := rfl
    rw [hfun]
    refine h.congr_fderiv ?_
    ext v
    simp
  exact h0.fderiv

@[powerlib_foundation] private lemma lie_norm_sq (x v : State n) :
    fderiv ℝ (fun y : State n => ‖y‖ ^ 2) x v = 2 * inner ℝ x v := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  rw [h.fderiv]
  simp

/-- `‖x‖²` is a strict global Lyapunov function for `ẋ = −‖x‖² x`. -/
@[powerlib_foundation] theorem cubic_neg_strictLyapunov :
    Dynamics.IsStrictLyapunovFunction (cubicField (n := n) (-1)) (fun x => ‖x‖ ^ 2) 0 where
  hcont := continuous_norm.pow 2
  hV_c1 := contDiff_norm_sq ℝ
  hzero := by simp
  hpos := fun x hx => by positivity
  hequil := cubicField_zero _
  hLie_neg := by
    intro x hx
    rw [lie_norm_sq, cubicField, inner_smul_right, real_inner_self_eq_norm_sq]
    have : 0 < ‖x‖ := norm_pos_iff.mpr hx
    nlinarith [pow_pos this 4]
  hbounded_sublevel := by
    intro c
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_le (continuous_norm.pow 2) continuous_const
    · rw [isBounded_iff_forall_norm_le]
      refine ⟨max 1 c, fun x hx => ?_⟩
      simp only [Set.mem_setOf_eq] at hx
      by_cases h1 : ‖x‖ ≤ 1
      · exact h1.trans (le_max_left _ _)
      · push Not at h1
        exact (le_of_lt (by nlinarith)).trans ((hx.trans' le_rfl).trans (le_max_right _ _))

/-- `ẋ = −‖x‖² x` (for `n = 1`, `ẋ = −x³`): the origin is globally asymptotically stable. -/
@[powerlib_foundation] theorem cubic_neg_globallyAsymptoticallyStable (hn : 0 < n) :
    GloballyAsymptoticallyStable (cubicField (n := n) (-1)) 0 :=
  globallyAsymptoticallyStable_of_strictLyapunov hn (cubicField_contDiff _)
    cubic_neg_strictLyapunov

/-- `ẋ = ‖x‖² x` (for `n = 1`, `ẋ = x³`): the origin is unstable. -/
@[powerlib_foundation] theorem cubic_pos_unstable (hn : 0 < n) :
    Dynamics.Unstable (cubicField (n := n) 1) 0 := by
  intro hstab
  obtain ⟨δ, hδ, hball⟩ := hstab 1 one_pos
  let e : State n := EuclideanSpace.single ⟨0, hn⟩ 1
  have he : ‖e‖ = 1 := by simp [e]
  set r : ℝ := min (δ / 2) (1 / 2) with hr
  have hr0 : 0 < r := lt_min (half_pos hδ) (by norm_num)
  have hrδ : r < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hr1 : r < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let x₀ : State n := r • e
  have hx₀ : ‖x₀‖ = r := by simp [x₀, he, norm_smul, abs_of_pos hr0]
  clear_value x₀
  let t₁ : ℝ := (1 - r ^ 2) / (2 * r ^ 2)
  have ht₁ : 0 ≤ t₁ := div_nonneg (by nlinarith) (by positivity)
  let u : ℝ → ℝ := fun t => 1 - 2 * r ^ 2 * t
  have hu : ∀ t ∈ Set.Icc 0 t₁, r ^ 2 ≤ u t := by
    intro t ht
    have h2 : 2 * r ^ 2 * t ≤ 2 * r ^ 2 * t₁ := by
      have := ht.2; nlinarith [sq_nonneg r]
    have h3 : 2 * r ^ 2 * t₁ = 1 - r ^ 2 := by
      simp only [t₁]; field_simp
    simp only [u]; linarith
  let g : ℝ → ℝ := fun t => (Real.sqrt (u t))⁻¹
  let φ : ℝ → State n := fun t => g t • x₀
  have hφ : Dynamics.IsTrajectoryOn φ (cubicField 1) 0 t₁ := by
    intro t ht
    have hut : 0 < u t := lt_of_lt_of_le (by positivity) (hu t ht)
    have hsq : 0 < Real.sqrt (u t) := Real.sqrt_pos.mpr hut
    have hdu : HasDerivAt u (-(2 * r ^ 2)) t := by
      simpa [u] using ((hasDerivAt_id t).const_mul (2 * r ^ 2)).const_sub 1
    have hdg : HasDerivAt g (-(-(2 * r ^ 2) / (2 * Real.sqrt (u t))) / Real.sqrt (u t) ^ 2) t :=
      (hdu.sqrt hut.ne').inv hsq.ne'
    refine (hdg.smul_const x₀).hasDerivWithinAt.congr_deriv ?_
    simp only [cubicField, φ, g]
    rw [norm_smul, hx₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsq), smul_smul]
    refine congrArg (fun c : ℝ => c • x₀) ?_
    field_simp
  have h0 : ‖φ 0 - 0‖ < δ := by
    simp only [φ, g, u, sub_zero, mul_zero, Real.sqrt_one, inv_one, one_smul]
    rw [hx₀]; exact hrδ
  have hend := hball 0 t₁ φ hφ h0 t₁ ⟨ht₁, le_rfl⟩
  have hut₁ : u t₁ = r ^ 2 := by
    simp only [u, t₁]; field_simp; ring
  have : ‖φ t₁ - 0‖ = 1 := by
    simp only [φ, g, sub_zero, hut₁]
    rw [Real.sqrt_sq hr0.le, norm_smul, hx₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr0),
      inv_mul_cancel₀ hr0.ne']
  linarith

/-- Two `C¹` systems with the same equilibrium and the same Jacobian (the zero matrix, all
eigenvalues with zero real part), one globally asymptotically stable and one unstable. -/
@[powerlib_foundation] theorem linearization_inconclusive (hn : 0 < n) :
    ∃ f g : State n → State n, ContDiff ℝ 1 f ∧ ContDiff ℝ 1 g ∧ f 0 = 0 ∧ g 0 = 0 ∧
      fderiv ℝ f 0 = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) 0 ∧
      fderiv ℝ g 0 = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) 0 ∧
      GloballyAsymptoticallyStable f 0 ∧ Dynamics.Unstable g 0 :=
  ⟨cubicField (-1), cubicField 1, cubicField_contDiff _, cubicField_contDiff _,
    cubicField_zero _, cubicField_zero _, cubicField_jacobian _, cubicField_jacobian _,
    cubic_neg_globallyAsymptoticallyStable hn, cubic_pos_unstable hn⟩

end powerlib.Modal
