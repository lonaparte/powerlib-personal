import theorem.NormalForm.Fold
import theorem.Flow.Certificate
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Transcritical and pitchfork normal forms

Foundation layer: truncated one-dimensional normal forms, not engineering models.

Model boundary. One state `x` (coordinate `x 0` of `State 1`), constant parameter `μ ∈ ℝ`,
continuous time, no input, noise, delay or saturation. The vector fields are exactly
* transcritical `ẋ = μ x − x²`,
* supercritical pitchfork `ẋ = μ x − x³`,
* subcritical pitchfork `ẋ = μ x + x³`,
with no higher-order remainder. Conclusions are equilibrium sets and trajectory-level
stability of those equilibria for the lifted `State 1` systems.

Results.
* Transcritical: equilibria `0, μ`; exchange of stability (`f_x(0) = μ`, `f_x(μ) = −μ`).
* Supercritical pitchfork: equilibria `0` and `±√μ` (`μ > 0`); `f_x(0) = μ`,
  `f_x(±√μ) = −2μ`; `0` is locally exponentially stable for `μ < 0` and unstable for
  `μ > 0`, where `±√μ` are locally exponentially stable.
* At `μ = 0`: the origin of `ẋ = −x³` is globally asymptotically stable (`V = x²`,
  `V̇ = −2x⁴`) but **not** locally exponentially stable (the solution
  `x₀ / √(1 + 2 x₀² t)` decays only algebraically).
* Subcritical pitchfork: equilibria `0` and `±√(−μ)` (`μ < 0`), the side branches are unstable
  (`f_x = −2μ > 0`); the origin is locally exponentially stable for `μ < 0` and unstable for
  `μ > 0`.
* `ℤ₂` symmetry: an odd field `f(−x) = −f(x)` has `f(0) = 0` and all even-order derivatives
  vanish at `0`; both pitchfork fields are odd.
* Basin of the supercritical branch: for `μ > 0` every forward-complete solution with
  `x(t₀) > 0` converges to `√μ` (explicit Bernoulli solution of `w = 1/x²`).
* Potential barrier of the supercritical pitchfork, `V(x) = −μx²/2 + x⁴/4`:
  `V(0) − V(±√μ) = μ²/4`.

Correction (T-fold-critical-scaling §2.3 contrasts the fold barrier exponent `3/2` with
"`1` (pitchfork)"): for the pitchfork normal form the barrier is `μ²/4`, so the exponent is `2`,
not `1` (`barrier`).

Source: work-sync theory/T-pitchfork-bifurcation.md §1.1–1.3, theory/T-bifurcation.md §1.4,
theory/T-attractors-basins.md (codes example (a): 1D pitchfork bistable, basin boundary 0),
theory/T-fold-critical-scaling.md §2.3.

Architecture: truncated normal forms, no model family; all results remain public foundation
support. Global asymptotic stability is `powerlib.Flow.GloballyAsymptoticallyStable`
(equilibrium, forward completeness and LeanForControl's `GlobalAsymptoticStable`).
-/

noncomputable section
namespace powerlib.NormalForm.Pitchfork
open Set Filter Topology
open powerlib.Dynamics (State)

/-! ## Transcritical normal form -/

/-- The transcritical normal form `x ↦ μ x − x²`. -/
def transField (μ : ℝ) (x : ℝ) : ℝ := μ * x - x ^ 2

@[powerlib_foundation] theorem transField_contDiff (μ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (transField μ) := by
  unfold transField; fun_prop

@[powerlib_foundation] theorem hasDerivAt_transField (μ x : ℝ) :
    HasDerivAt (transField μ) (μ - 2 * x) x := by
  have h := ((hasDerivAt_id' x).const_mul μ).sub (hasDerivAt_pow 2 x)
  unfold transField
  convert h using 1
  push_cast; ring

@[powerlib_foundation] theorem deriv_transField (μ x : ℝ) : deriv (transField μ) x = μ - 2 * x :=
  (hasDerivAt_transField μ x).deriv

@[powerlib_foundation] theorem transField_eq_zero_iff (μ x : ℝ) :
    transField μ x = 0 ↔ x = 0 ∨ x = μ := by
  unfold transField
  constructor
  · intro h
    have : x * (μ - x) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> ring

/-- Exchange of stability, `μ < 0`: the origin is stable and `x = μ` is unstable. -/
@[powerlib_foundation] theorem trans_stability_neg {μ : ℝ} (hμ : μ < 0) :
    LocallyExponentiallyStable (lift (transField μ)) (embed 0) ∧
      Unstable (lift (transField μ)) (embed μ) :=
  ⟨lift_locallyExponentiallyStable (transField_contDiff μ) (by simp [transField])
      (by rw [deriv_transField]; linarith),
    lift_unstable (transField_contDiff μ) (by simp [transField]; ring)
      (by rw [deriv_transField]; linarith)⟩

/-- Exchange of stability, `μ > 0`: the origin is unstable and `x = μ` is stable. -/
@[powerlib_foundation] theorem trans_stability_pos {μ : ℝ} (hμ : 0 < μ) :
    Unstable (lift (transField μ)) (embed 0) ∧
      LocallyExponentiallyStable (lift (transField μ)) (embed μ) :=
  ⟨lift_unstable (transField_contDiff μ) (by simp [transField])
      (by rw [deriv_transField]; linarith),
    lift_locallyExponentiallyStable (transField_contDiff μ) (by simp [transField]; ring)
      (by rw [deriv_transField]; linarith)⟩

/-! ## Supercritical pitchfork `ẋ = μ x − x³` -/

/-- The supercritical pitchfork normal form `x ↦ μ x − x³`. -/
def superField (μ : ℝ) (x : ℝ) : ℝ := μ * x - x ^ 3

/-- The supercritical pitchfork as a vector field on `State 1`. -/
def superSystem (μ : ℝ) : State 1 → State 1 := lift (superField μ)

@[powerlib_foundation] theorem superField_contDiff (μ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (superField μ) := by
  unfold superField; fun_prop

@[powerlib_foundation] theorem hasDerivAt_superField (μ x : ℝ) :
    HasDerivAt (superField μ) (μ - 3 * x ^ 2) x := by
  have h := ((hasDerivAt_id' x).const_mul μ).sub (hasDerivAt_pow 3 x)
  unfold superField
  convert h using 1
  push_cast; ring

@[powerlib_foundation] theorem deriv_superField (μ x : ℝ) :
    deriv (superField μ) x = μ - 3 * x ^ 2 :=
  (hasDerivAt_superField μ x).deriv

@[powerlib_foundation] theorem superField_eq_zero_iff (μ x : ℝ) :
    superField μ x = 0 ↔ x = 0 ∨ (0 ≤ μ ∧ (x = √μ ∨ x = -√μ)) := by
  have hfac : superField μ x = x * Fold.field μ x := by simp [superField, Fold.field]; ring
  rw [hfac, mul_eq_zero, Fold.field_eq_zero_iff]

/-- Linearization slopes: `f_x(0) = μ`, `f_x(±√μ) = −2μ` (`μ ≥ 0`). -/
@[powerlib_foundation] theorem super_slopes {μ : ℝ} (hμ : 0 ≤ μ) :
    deriv (superField μ) 0 = μ ∧ deriv (superField μ) √μ = -2 * μ ∧
      deriv (superField μ) (-√μ) = -2 * μ := by
  simp only [deriv_superField, neg_sq, Real.sq_sqrt hμ]
  refine ⟨by ring, by ring, by ring⟩

@[powerlib_foundation] theorem super_origin_stable {μ : ℝ} (hμ : μ < 0) :
    LocallyExponentiallyStable (superSystem μ) (embed 0) :=
  lift_locallyExponentiallyStable (superField_contDiff μ) (by simp [superField])
    (by rw [deriv_superField]; linarith)

@[powerlib_foundation] theorem super_origin_unstable {μ : ℝ} (hμ : 0 < μ) :
    Unstable (superSystem μ) (embed 0) :=
  lift_unstable (superField_contDiff μ) (by simp [superField])
    (by rw [deriv_superField]; linarith)

@[powerlib_foundation] theorem super_branch_stable {μ : ℝ} (hμ : 0 < μ) :
    LocallyExponentiallyStable (superSystem μ) (embed √μ) ∧
      LocallyExponentiallyStable (superSystem μ) (embed (-√μ)) := by
  obtain ⟨-, h1, h2⟩ := super_slopes hμ.le
  refine ⟨lift_locallyExponentiallyStable (superField_contDiff μ)
      ((superField_eq_zero_iff μ _).mpr (Or.inr ⟨hμ.le, Or.inl rfl⟩)) (by rw [h1]; linarith),
    lift_locallyExponentiallyStable (superField_contDiff μ)
      ((superField_eq_zero_iff μ _).mpr (Or.inr ⟨hμ.le, Or.inr rfl⟩)) (by rw [h2]; linarith)⟩

/-! ### The degenerate point `μ = 0`: asymptotic but not exponential stability -/

@[powerlib_foundation] theorem inner_superSystem (x : State 1) :
    inner ℝ x (superSystem 0 x) = -(x 0) ^ 4 := by
  simp [superSystem, PiLp.inner_apply, superField]
  ring

/-- `V(x) = ‖x‖² = x²` is a radially unbounded strict Lyapunov function with `V̇ = −2x⁴`. -/
@[powerlib_foundation] theorem super_zero_lie (x : State 1) :
    fderiv ℝ (fun y : State 1 => ‖y‖ ^ 2) x (superSystem 0 x) = -2 * (x 0) ^ 4 := by
  rw [(hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv]
  simp only [smul_apply, innerSL_apply_apply, inner_superSystem]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

@[powerlib_foundation] theorem super_zero_lyapunov :
    _root_.IsAsymptoticLyapunovFunction (superSystem 0) (fun y : State 1 => ‖y‖ ^ 2) 0 where
  hcont := (continuous_norm.pow 2)
  hV_c1 := contDiff_norm_sq ℝ
  hzero := by simp only [norm_zero]; norm_num
  hpos := by
    intro x hx
    have : 0 < ‖x‖ := norm_pos_iff.mpr hx
    positivity
  hequil := by
    have := (lift_eq_zero_iff (superField 0) 0).mpr (by norm_num [superField])
    rwa [embed_zero] at this
  hLie_neg := by
    intro x hx
    rw [super_zero_lie]
    have h0 : x 0 ≠ 0 := by
      intro h; apply hx; rw [← embed_coord x, h, embed_zero]
    have : 0 < (x 0) ^ 4 := by positivity
    linarith
  hradial := by
    have : Tendsto (fun r : ℝ => r ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
    exact this.comp tendsto_comap

/-- At `μ = 0` the origin of `ẋ = −x³` is globally asymptotically stable. -/
@[powerlib_foundation] theorem super_zero_globallyAsymptoticallyStable :
    Flow.GloballyAsymptoticallyStable (superSystem 0) 0 :=
  Flow.globallyAsymptoticallyStable_of_strictLyapunov (by norm_num)
    (lift_contDiff (superField_contDiff 0)) (asymptotic_implies_strict super_zero_lyapunov)

@[powerlib_foundation] theorem super_zero_solution_hasDerivAt (x₀ t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => x₀ / √(1 + 2 * x₀ ^ 2 * s))
      (superField 0 (x₀ / √(1 + 2 * x₀ ^ 2 * t))) t := by
  have hu : 0 < 1 + 2 * x₀ ^ 2 * t := by positivity
  have hd : HasDerivAt (fun s => 1 + 2 * x₀ ^ 2 * s) (2 * x₀ ^ 2) t := by
    simpa using ((hasDerivAt_id t).const_mul (2 * x₀ ^ 2)).const_add 1
  have hs := hd.sqrt hu.ne'
  have hsq : √(1 + 2 * x₀ ^ 2 * t) ≠ 0 := (Real.sqrt_pos.mpr hu).ne'
  have h := (hasDerivAt_const t x₀).div hs hsq
  convert h using 1
  have hsq2 : √(1 + 2 * x₀ ^ 2 * t) ^ 2 = 1 + 2 * x₀ ^ 2 * t := Real.sq_sqrt hu.le
  set u := 1 + 2 * x₀ ^ 2 * t with hu_def
  set q := √u with hq_def
  have hq3 : q ^ 3 = q * u := by rw [pow_succ, hsq2, mul_comm]
  simp only [superField, zero_mul, zero_sub, div_pow, hq3]
  field_simp
  rw [hsq2]

/-- At `μ = 0` the origin is not locally exponentially stable. -/
@[powerlib_foundation] theorem super_zero_not_locallyExponentiallyStable :
    ¬ LocallyExponentiallyStable (superSystem 0) (embed 0) := by
  rintro ⟨r, C, a, hr, hC, ha, h⟩
  set x₀ := r / 2 with hx₀
  have hx₀pos : 0 < x₀ := by positivity
  -- `C e^{-at} (1 + 2 x₀² t)` tends to zero
  have hlim : Tendsto (fun t => C * Real.exp (-a * t) * (1 + 2 * x₀ ^ 2 * t)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t => Real.exp (-a * t)) atTop (𝓝 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop ha)
      exact this.congr (fun t => by simp [neg_mul])
    have h2 : Tendsto (fun t => t * Real.exp (-a * t)) atTop (𝓝 0) := by
      have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
        (tendsto_id.const_mul_atTop ha)).const_mul (1 / a)
      refine (this.congr (fun t => ?_)).trans (by simp)
      simp only [Function.comp, id, pow_one]
      field_simp
    have := (h1.const_mul C).add ((h2.const_mul (2 * x₀ ^ 2)).const_mul C)
    simp only [mul_zero, add_zero] at this
    exact this.congr (fun t => by ring)
  obtain ⟨t, ht0, ht⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (hlim.eventually (gt_mem_nhds zero_lt_one))).exists
  have htraj : IsTrajectoryOn (fun s => embed (x₀ / √(1 + 2 * x₀ ^ 2 * s)))
      (superSystem 0) 0 t := by
    apply isTrajectoryOn_embed
    intro s hs
    exact (super_zero_solution_hasDerivAt x₀ s hs.1).hasDerivWithinAt
  have h0 : ‖embed (x₀ / √(1 + 2 * x₀ ^ 2 * 0)) - embed 0‖ < r := by
    rw [embed_sub, norm_embed]
    simp only [mul_zero, add_zero, Real.sqrt_one, div_one, sub_zero]
    rw [abs_of_pos hx₀pos]; linarith
  have hb := h 0 t _ htraj h0 t ⟨ht0, le_rfl⟩
  simp only [embed_sub, norm_embed, sub_zero, mul_zero, add_zero, Real.sqrt_one, div_one,
    abs_of_pos hx₀pos] at hb
  have hu : 0 < 1 + 2 * x₀ ^ 2 * t := by positivity
  have hsqrt_pos : 0 < √(1 + 2 * x₀ ^ 2 * t) := Real.sqrt_pos.mpr hu
  rw [abs_of_pos (div_pos hx₀pos hsqrt_pos), div_le_iff₀ hsqrt_pos] at hb
  have hu1 : 1 ≤ 1 + 2 * x₀ ^ 2 * t := by nlinarith [sq_nonneg x₀]
  have hsq_le : √(1 + 2 * x₀ ^ 2 * t) ≤ 1 + 2 * x₀ ^ 2 * t := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have : x₀ ≤ C * Real.exp (-a * t) * (1 + 2 * x₀ ^ 2 * t) * x₀ := by
    calc x₀ ≤ C * Real.exp (-a * t) * x₀ * √(1 + 2 * x₀ ^ 2 * t) := hb
      _ ≤ C * Real.exp (-a * t) * x₀ * (1 + 2 * x₀ ^ 2 * t) := by
        apply mul_le_mul_of_nonneg_left hsq_le; positivity
      _ = C * Real.exp (-a * t) * (1 + 2 * x₀ ^ 2 * t) * x₀ := by ring
  nlinarith

/-! ### Basin of the positive branch -/

/-- For `μ > 0`, every solution with `x(a) > 0` satisfies `1/x² − 1/μ = (1/x(a)² − 1/μ) e^{−2μ(t−a)}`. -/
@[powerlib_foundation] theorem super_bernoulli {μ : ℝ} (hμ : 0 < μ) {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : IsIntegralCurveOn ψ (fun _ r => superField μ r) (Icc a b)) (ha : 0 < ψ a) :
    ∀ t ∈ Icc a b, 1 / ψ t ^ 2 - 1 / μ = (1 / ψ a ^ 2 - 1 / μ) * Real.exp (-2 * μ * (t - a)) := by
  have hpos := pos_of_pos (superField_contDiff μ) (by simp [superField]) hψ ha
  have hconst := eq_of_hasDerivWithinAt_zero
    (F := fun t => ((ψ t ^ 2)⁻¹ - 1 / μ) * Real.exp (2 * μ * (t - a))) (a := a) (b := b)
    (by
      intro t ht
      have hne : ψ t ≠ 0 := (hpos t ht).ne'
      have hd : HasDerivWithinAt ψ (μ * ψ t - ψ t ^ 3) (Icc a b) t := by
        simpa [superField] using hψ t ht
      have h2 : HasDerivWithinAt (fun s => ψ s ^ 2) (2 * ψ t * (μ * ψ t - ψ t ^ 3)) (Icc a b) t := by
        convert hd.pow 2 using 1; push_cast; ring
      have h3 : HasDerivWithinAt (fun s => (ψ s ^ 2)⁻¹)
          (-(2 * ψ t * (μ * ψ t - ψ t ^ 3)) / (ψ t ^ 2) ^ 2) (Icc a b) t :=
        h2.inv (pow_ne_zero 2 hne)
      have hw : HasDerivWithinAt (fun s => (ψ s ^ 2)⁻¹ - 1 / μ)
          (-(2 * ψ t * (μ * ψ t - ψ t ^ 3)) / (ψ t ^ 2) ^ 2) (Icc a b) t :=
        h3.sub_const (1 / μ)
      have he : HasDerivWithinAt (fun s => Real.exp (2 * μ * (s - a)))
          (Real.exp (2 * μ * (t - a)) * (2 * μ)) (Icc a b) t := by
        have : HasDerivAt (fun s => 2 * μ * (s - a)) (2 * μ) t := by
          simpa using ((hasDerivAt_id t).sub_const a).const_mul (2 * μ)
        exact this.exp.hasDerivWithinAt
      convert hw.mul he using 1
      field_simp
      ring)
  intro t ht
  have h := hconst t ht
  simp only [sub_self, mul_zero, Real.exp_zero, mul_one, ← one_div] at h
  have hexp : Real.exp (2 * μ * (t - a)) * Real.exp (-2 * μ * (t - a)) = 1 := by
    rw [← Real.exp_add]; simp
  calc 1 / ψ t ^ 2 - 1 / μ
      = (1 / ψ t ^ 2 - 1 / μ) * Real.exp (2 * μ * (t - a)) * Real.exp (-2 * μ * (t - a)) := by
        rw [mul_assoc, hexp, mul_one]
    _ = _ := by rw [h]

/-- For `μ > 0` the positive half-line lies in the basin of `√μ`: every forward-complete
solution with `x(a) > 0` converges to `√μ`. -/
@[powerlib_foundation] theorem super_tendsto_sqrt {μ : ℝ} (hμ : 0 < μ) {ψ : ℝ → ℝ} {a : ℝ}
    (hψ : IsIntegralCurveOn ψ (fun _ r => superField μ r) (Ici a)) (ha : 0 < ψ a) :
    Tendsto ψ atTop (𝓝 √μ) := by
  have hpos : ∀ t, a ≤ t → 0 < ψ t := fun t ht =>
    pos_of_pos (superField_contDiff μ) (by simp [superField]) (hψ.mono Icc_subset_Ici_self) ha
      t ⟨ht, le_rfl⟩
  have hw : ∀ t, a ≤ t → 1 / ψ t ^ 2 = 1 / μ + (1 / ψ a ^ 2 - 1 / μ) * Real.exp (-2 * μ * (t - a)) :=
    fun t ht => by
      have := super_bernoulli hμ (hψ.mono Icc_subset_Ici_self) ha t ⟨ht, le_rfl⟩
      linarith
  have hexp : Tendsto (fun t => Real.exp (-2 * μ * (t - a))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => 2 * μ * (t - a)) atTop atTop :=
      Tendsto.const_mul_atTop (show (0 : ℝ) < 2 * μ by positivity)
        (tendsto_atTop_add_const_right _ (-a) tendsto_id) |>.congr
        (fun t => by simp only [id]; ring)
    exact (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).congr (fun t => by simp [neg_mul])
  have hlimw : Tendsto (fun t => 1 / μ + (1 / ψ a ^ 2 - 1 / μ) * Real.exp (-2 * μ * (t - a)))
      atTop (𝓝 (1 / μ)) := by
    have := (hexp.const_mul (1 / ψ a ^ 2 - 1 / μ)).const_add (1 / μ)
    rwa [mul_zero, add_zero] at this
  -- `ψ = (1/ψ²)^{-1/2}` on the forward ray
  have hψeq : ∀ t, a ≤ t → ψ t = 1 / √(1 / ψ t ^ 2) := by
    intro t ht
    rw [Real.sqrt_div' 1 (sq_nonneg _), Real.sqrt_sq (hpos t ht).le]; simp
  have hcont : ContinuousAt (fun w : ℝ => 1 / √w) (1 / μ) := by
    have : √(1 / μ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    exact continuousAt_const.div Real.continuous_sqrt.continuousAt this
  have hval : 1 / √(1 / μ) = √μ := by
    rw [Real.sqrt_div' 1 hμ.le, Real.sqrt_one, one_div_one_div]
  have := (hcont.tendsto.comp hlimw)
  rw [hval] at this
  refine this.congr' (eventually_atTop.mpr ⟨a, fun t ht => ?_⟩)
  simp only [Function.comp]
  rw [← hw t ht, ← hψeq t ht]

/-! ## Subcritical pitchfork `ẋ = μ x + x³` -/

/-- The subcritical pitchfork normal form `x ↦ μ x + x³`. -/
def subField (μ : ℝ) (x : ℝ) : ℝ := μ * x + x ^ 3

/-- The subcritical pitchfork as a vector field on `State 1`. -/
def subSystem (μ : ℝ) : State 1 → State 1 := lift (subField μ)

@[powerlib_foundation] theorem subField_contDiff (μ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (subField μ) := by
  unfold subField; fun_prop

@[powerlib_foundation] theorem hasDerivAt_subField (μ x : ℝ) :
    HasDerivAt (subField μ) (μ + 3 * x ^ 2) x := by
  have h := ((hasDerivAt_id' x).const_mul μ).add (hasDerivAt_pow 3 x)
  unfold subField
  convert h using 1
  push_cast; ring

@[powerlib_foundation] theorem deriv_subField (μ x : ℝ) :
    deriv (subField μ) x = μ + 3 * x ^ 2 :=
  (hasDerivAt_subField μ x).deriv

@[powerlib_foundation] theorem subField_eq_zero_iff (μ x : ℝ) :
    subField μ x = 0 ↔ x = 0 ∨ (μ ≤ 0 ∧ (x = √(-μ) ∨ x = -√(-μ))) := by
  have hfac : subField μ x = -(x * Fold.field (-μ) x) := by simp [subField, Fold.field]; ring
  rw [hfac, neg_eq_zero, mul_eq_zero, Fold.field_eq_zero_iff, neg_nonneg]

/-- Subcritical side branches `±√(−μ)` (`μ < 0`) have slope `−2μ > 0` and are unstable. -/
@[powerlib_foundation] theorem sub_branch_unstable {μ : ℝ} (hμ : μ < 0) :
    Unstable (subSystem μ) (embed √(-μ)) ∧
      Unstable (subSystem μ) (embed (-√(-μ))) := by
  have hs : √(-μ) ^ 2 = -μ := Real.sq_sqrt (by linarith)
  refine ⟨lift_unstable (subField_contDiff μ)
      ((subField_eq_zero_iff μ _).mpr (Or.inr ⟨hμ.le, Or.inl rfl⟩))
      (by rw [deriv_subField, hs]; linarith),
    lift_unstable (subField_contDiff μ)
      ((subField_eq_zero_iff μ _).mpr (Or.inr ⟨hμ.le, Or.inr rfl⟩))
      (by rw [deriv_subField, neg_sq, hs]; linarith)⟩

@[powerlib_foundation] theorem sub_origin_stable {μ : ℝ} (hμ : μ < 0) :
    LocallyExponentiallyStable (subSystem μ) (embed 0) :=
  lift_locallyExponentiallyStable (subField_contDiff μ) (by simp [subField])
    (by rw [deriv_subField]; linarith)

@[powerlib_foundation] theorem sub_origin_unstable {μ : ℝ} (hμ : 0 < μ) :
    Unstable (subSystem μ) (embed 0) :=
  lift_unstable (subField_contDiff μ) (by simp [subField])
    (by rw [deriv_subField]; linarith)

/-! ## `ℤ₂` symmetry -/

/-- An odd scalar field has the origin as an equilibrium. -/
@[powerlib_foundation] theorem odd_apply_zero {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) :
    f 0 = 0 := by
  have := hodd 0
  rw [neg_zero] at this
  linarith

/-- An odd scalar field has vanishing even-order derivatives at the origin. -/
@[powerlib_foundation] theorem odd_iteratedDeriv_even_zero {f : ℝ → ℝ}
    (hodd : ∀ x, f (-x) = -f x) (k : ℕ) : iteratedDeriv (2 * k) f 0 = 0 := by
  have hfun : (fun x => f (-x)) = fun x => -f x := funext hodd
  have h := iteratedDeriv_comp_neg (2 * k) f 0
  rw [hfun, iteratedDeriv_fun_neg, neg_zero, pow_mul, neg_one_sq, one_pow, one_smul] at h
  linarith

@[powerlib_foundation] theorem superField_odd (μ x : ℝ) : superField μ (-x) = -superField μ x := by
  simp [superField]; ring

@[powerlib_foundation] theorem subField_odd (μ x : ℝ) : subField μ (-x) = -subField μ x := by
  simp [subField]; ring

/-! ## Potential barrier -/

/-- The supercritical pitchfork potential `V(x) = −μx²/2 + x⁴/4`, `V' = −(μx − x³)`. -/
def potential (μ : ℝ) (x : ℝ) : ℝ := -μ * x ^ 2 / 2 + x ^ 4 / 4

@[powerlib_foundation] theorem hasDerivAt_potential (μ x : ℝ) :
    HasDerivAt (potential μ) (-superField μ x) x := by
  have h := (((hasDerivAt_pow 2 x).const_mul (-μ)).div_const 2).add
    ((hasDerivAt_pow 4 x).div_const 4)
  convert h using 1
  · funext y; simp [potential]
  · simp [superField]; ring

/-- Correction: the pitchfork barrier is `μ²/4` (exponent `2`). -/
@[powerlib_foundation] theorem barrier {μ : ℝ} (hμ : 0 ≤ μ) :
    potential μ 0 - potential μ √μ = μ ^ 2 / 4 ∧
      potential μ 0 - potential μ (-√μ) = μ ^ 2 / 4 := by
  have h2 : √μ ^ 2 = μ := Real.sq_sqrt hμ
  have h4 : √μ ^ 4 = μ ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, h2]
  have h2' : (-√μ) ^ 2 = μ := by rw [neg_sq, h2]
  have h4' : (-√μ) ^ 4 = μ ^ 2 := by rw [show (-√μ) ^ 4 = √μ ^ 4 by ring, h4]
  unfold potential
  rw [h2, h4, h2', h4']
  constructor <;> ring

end powerlib.NormalForm.Pitchfork
