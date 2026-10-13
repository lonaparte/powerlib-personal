import theorem.Asymptotics.GuardPotential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Guard versus committed escape: `T_committed / T_guard → 2`

Foundation layer: one-variable real analysis of an explicit double integral. Nothing here is a
stochastic statement; the integral is *taken* as the definition of the mean first-passage time
(MFPT), exactly as the source note does, and no Fokker–Planck / backward-Kolmogorov derivation of
it is formalized.

Model boundary.
* Potential: the truncated subcritical-Hopf potential `U(r) = α r²/2 − l₁ r⁴/4` of
  `Asymptotics/GuardPotential.lean` (`guardPotential`), `α, l₁ > 0`, well at `r = 0`, barrier top
  at `r_c = √(α/l₁)` (`guardRadius`), barrier height `ΔU = α²/(4 l₁)`.
* MFPT (source §1.2, two-dimensional amplitude measure, natural reflection at `r = 0`):
  `T(r_b) = D̃⁻¹ ∫₀^{r_b} (dy/y) e^{U(y)/D̃} ∫₀^y z e^{−U(z)/D̃} dz` (`guardMFPT α l₁ D̃ r_b`).
  `T_guard = T(r_c)` is the first arrival at the barrier top; `T_committed = T(r_b)` with any
  downstream boundary `r_b > r_c` is committed escape.
* Asymptotic regime: noise intensity `D̃ → 0⁺` at fixed `α, l₁, r_b`, equivalently
  `X = ΔU/D̃ → ∞`.

Results.
* `tendsto_guardMFPT_ratio`: `T(r_b)/T(r_c) → 2` as `D̃ → 0⁺`, for every `r_b > r_c`
  (the source's `U(r_b) ≪ U(r_c)` placement is not needed for the limit);
  `tendsto_guardMFPT_ratio_atTop`: the same along `X = ΔU/D̃ → ∞`;
  `tendsto_guardMFPT_ratio_inv`: `T_guard/T_committed → 1/2`.
* Proof route (no Laplace expansion is needed for the ratio): cut at `a < r_c` and at its mirror
  `ψ(a) = √(2r_c² − a²)`, for which `U(ψ(a)) = U(a)` (`guardPotential_reflect`). The substitution
  `y ↦ ψ(y)` (`integral_guardIntegrand_reflect`) maps the part of the outer integral beyond the
  top onto the part inside it with Jacobian factor `y/ψ(y)` and inner integral `K(ψ(y))`;
  `guard_ratio_bounds` gives explicit deterministic bounds
  `a²/(2r_c² − a²) · A ≤ (1 + ε) B` and `B ≤ (1 + κ + ε) A`
  (`A = ∫₀^{r_c}`, `B = ∫_{r_c}^{r_b}`), with explicit `ε = guardEps`, `κ = guardKappa` that tend
  to `0` as `D̃ → 0⁺` (`tendsto_guardEps`, `tendsto_guardKappa`); letting `a → r_c` closes the
  squeeze `B/A → 1`.
* Supporting facts: `U(z) = ΔU − (l₁/4)(z² − r_c²)²` (`guardPotential_eq_barrier_sub`),
  monotonicity / integrability / two-sided bounds of the inner integral `K` (`guardInner_*`) and
  of the outer integrand (`guardIntegrand_*`).

Not formalized: the rate `T_committed/T_guard = 2(1 + O(X^{−1/2}))` claimed in source §1.2 and
the individual asymptotics `T_guard ~ P e^X` of §1.3 (the endpoint/interior Laplace rates
themselves are in `Asymptotics/LaplaceMethod.lean`, `laplace_endpoint_rate`,
`laplace_interior_rate`).

Source: work-sync theory/T-endpoint-laplace-asymptotics.md §1.2 ("逃逸时间的两种边界，比值恰为 2",
`T_committed / T_guard → 2`), §1.3 (the potential `U = αr²/2 − l₁r⁴/4`).
-/

noncomputable section
namespace powerlib.Asymptotics

open Real Set Filter Topology MeasureTheory intervalIntegral

/-! ## The mean first-passage time and its two boundary choices -/

/-- Inner integral of the MFPT formula, `K(y) = ∫₀^y z e^{−U(z)/D̃} dz`. -/
def guardInner (α l₁ D y : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..y, z * Real.exp (-(guardPotential α l₁ z / D))

/-- Outer integrand of the MFPT formula, `y⁻¹ e^{U(y)/D̃} K(y)`. -/
def guardIntegrand (α l₁ D y : ℝ) : ℝ :=
  y⁻¹ * Real.exp (guardPotential α l₁ y / D) * guardInner α l₁ D y

/-- Mean first-passage time to the outer boundary `r_b`:
`T(r_b) = D̃⁻¹ ∫₀^{r_b} (dy/y) e^{U(y)/D̃} ∫₀^y z e^{−U(z)/D̃} dz` (two-dimensional amplitude
measure, natural reflection at `r = 0`). `r_b = r_c` is the first arrival at the barrier top
(`T_guard`); `r_b > r_c` is committed escape (`T_committed`). -/
def guardMFPT (α l₁ D rb : ℝ) : ℝ :=
  D⁻¹ * ∫ y in (0 : ℝ)..rb, guardIntegrand α l₁ D y

variable {α l₁ : ℝ}

/-- `U(z) = ΔU − (l₁/4)(z² − r_c²)²`. -/
@[powerlib_foundation] theorem guardPotential_eq_barrier_sub (hl : 0 < l₁) (z : ℝ) :
    guardPotential α l₁ z = barrierHeight α l₁ - l₁ / 4 * (z ^ 2 - α / l₁) ^ 2 := by
  simp only [guardPotential, barrierHeight]; field_simp; ring

/-- `U` is a decreasing function of `(z² − r_c²)²`. -/
@[powerlib_foundation] theorem guardPotential_le_of_sq_le (hl : 0 < l₁) {z w : ℝ}
    (h : (z ^ 2 - α / l₁) ^ 2 ≤ (w ^ 2 - α / l₁) ^ 2) :
    guardPotential α l₁ w ≤ guardPotential α l₁ z := by
  rw [guardPotential_eq_barrier_sub hl, guardPotential_eq_barrier_sub hl]
  have : 0 < l₁ / 4 := by positivity
  nlinarith

@[powerlib_foundation] theorem guardPotential_le_quad (hl : 0 ≤ l₁) (z : ℝ) :
    guardPotential α l₁ z ≤ α * z ^ 2 / 2 := by
  simp only [guardPotential]; nlinarith [pow_nonneg (sq_nonneg z) 2, sq_nonneg (z ^ 2)]

@[powerlib_foundation] theorem guardPotential_le_barrier (hl : 0 < l₁) (z : ℝ) :
    guardPotential α l₁ z ≤ barrierHeight α l₁ := by
  rw [guardPotential_eq_barrier_sub hl]
  have : 0 ≤ l₁ / 4 * (z ^ 2 - α / l₁) ^ 2 := by positivity
  linarith

@[powerlib_foundation] theorem guardPotential_pos (hl : 0 < l₁) {z : ℝ}
    (hz : 0 < z) (hz2 : z ^ 2 < 2 * (α / l₁)) : 0 < guardPotential α l₁ z := by
  have : guardPotential α l₁ z = z ^ 2 / 4 * (l₁ * (2 * (α / l₁) - z ^ 2)) := by
    simp only [guardPotential]; field_simp; ring
  rw [this]
  have : 0 < 2 * (α / l₁) - z ^ 2 := by linarith
  positivity

section Inner

variable {D : ℝ}

@[powerlib_foundation] theorem continuous_guardInner_integrand (α l₁ D : ℝ) :
    Continuous fun z => z * Real.exp (-(guardPotential α l₁ z / D)) := by
  unfold guardPotential; fun_prop

@[powerlib_foundation] theorem hasDerivAt_guardInner (α l₁ D y : ℝ) :
    HasDerivAt (guardInner α l₁ D) (y * Real.exp (-(guardPotential α l₁ y / D))) y :=
  ((continuous_guardInner_integrand α l₁ D).integral_hasStrictDerivAt 0 y).hasDerivAt

@[powerlib_foundation] theorem continuous_guardInner (α l₁ D : ℝ) :
    Continuous (guardInner α l₁ D) :=
  continuous_iff_continuousAt.2 fun y => (hasDerivAt_guardInner α l₁ D y).continuousAt

/-- `K(y₂) − K(y₁) = ∫_{y₁}^{y₂} z e^{−U/D̃}`. -/
@[powerlib_foundation] theorem guardInner_sub (α l₁ D y₁ y₂ : ℝ) :
    guardInner α l₁ D y₂ - guardInner α l₁ D y₁ =
      ∫ z in y₁..y₂, z * Real.exp (-(guardPotential α l₁ z / D)) := by
  simp only [guardInner]
  rw [integral_interval_sub_left]
  · exact (continuous_guardInner_integrand α l₁ D).intervalIntegrable _ _
  · exact (continuous_guardInner_integrand α l₁ D).intervalIntegrable _ _

@[powerlib_foundation] theorem guardInner_mono {y₁ y₂ : ℝ} (h0 : 0 ≤ y₁) (h : y₁ ≤ y₂) :
    guardInner α l₁ D y₁ ≤ guardInner α l₁ D y₂ := by
  have := guardInner_sub α l₁ D y₁ y₂
  have hnn : 0 ≤ ∫ z in y₁..y₂, z * Real.exp (-(guardPotential α l₁ z / D)) :=
    integral_nonneg h fun z hz => mul_nonneg (h0.trans hz.1) (Real.exp_pos _).le
  linarith

@[powerlib_foundation] theorem guardInner_nonneg {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ guardInner α l₁ D y := by
  have := guardInner_mono (α := α) (l₁ := l₁) (D := D) le_rfl hy
  simpa [guardInner] using this

/-- `K(y) ≤ (y²/2)(1 + e^{−U(y)/D̃})`: on `[0, y]` the potential is at least `min(0, U(y))`. -/
@[powerlib_foundation] theorem guardInner_le (hl : 0 < l₁) (hD : 0 < D) {y : ℝ} (hy : 0 ≤ y) :
    guardInner α l₁ D y ≤ y ^ 2 / 2 * (1 + Real.exp (-(guardPotential α l₁ y / D))) := by
  have hb : ∀ z ∈ Icc (0 : ℝ) y, z * Real.exp (-(guardPotential α l₁ z / D)) ≤
      z * (1 + Real.exp (-(guardPotential α l₁ y / D))) := by
    intro z hz
    apply mul_le_mul_of_nonneg_left _ hz.1
    -- `(z² − ρ)² ≤ max(ρ², (y² − ρ)²)`
    have hz2 : z ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hz.1 hz.2 2
    have hz0 : 0 ≤ z ^ 2 := sq_nonneg z
    rcases le_or_gt (z ^ 2) (2 * (α / l₁)) with h | h
    · -- `(z² − ρ)² ≤ ρ² = (0² − ρ)²`, so `U(z) ≥ U(0) = 0`
      have h0 : (z ^ 2 - α / l₁) ^ 2 ≤ ((0 : ℝ) ^ 2 - α / l₁) ^ 2 := by nlinarith
      have := guardPotential_le_of_sq_le (α := α) hl h0
      have hU0 : guardPotential α l₁ 0 = 0 := by simp [guardPotential]
      rw [hU0] at this
      have : Real.exp (-(guardPotential α l₁ z / D)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by have := div_nonneg this hD.le; linarith)
      linarith [Real.exp_pos (-(guardPotential α l₁ y / D))]
    · -- `z² > 2ρ`: then `(z² − ρ)² ≤ (y² − ρ)²`, so `U(z) ≥ U(y)`
      have h1 : (z ^ 2 - α / l₁) ^ 2 ≤ (y ^ 2 - α / l₁) ^ 2 := by nlinarith
      have := guardPotential_le_of_sq_le (α := α) hl h1
      have : Real.exp (-(guardPotential α l₁ z / D)) ≤ Real.exp (-(guardPotential α l₁ y / D)) :=
        Real.exp_le_exp.mpr (by rw [neg_le_neg_iff]; exact div_le_div_of_nonneg_right this hD.le)
      linarith [Real.exp_pos (-(guardPotential α l₁ y / D))]
  calc guardInner α l₁ D y ≤ ∫ z in (0 : ℝ)..y, z * (1 + Real.exp (-(guardPotential α l₁ y / D))) :=
        integral_mono_on hy ((continuous_guardInner_integrand α l₁ D).intervalIntegrable _ _)
          ((by fun_prop : Continuous fun z : ℝ =>
            z * (1 + Real.exp (-(guardPotential α l₁ y / D)))).intervalIntegrable _ _) hb
    _ = y ^ 2 / 2 * (1 + Real.exp (-(guardPotential α l₁ y / D))) := by
        rw [intervalIntegral.integral_mul_const, integral_id]; ring

/-- `K(a) ≥ (D̃/2) e^{−α/2}` once `D̃ ≤ a²`. -/
@[powerlib_foundation] theorem guardInner_ge (hα : 0 ≤ α) (hl : 0 ≤ l₁) (hD : 0 < D) {a : ℝ}
    (ha : 0 ≤ a)
    (hDa : D ≤ a ^ 2) : D / 2 * Real.exp (-(α / 2)) ≤ guardInner α l₁ D a := by
  have hs : √D ≤ a := by
    rw [show a = √(a ^ 2) from (Real.sqrt_sq ha).symm]; exact Real.sqrt_le_sqrt hDa
  have hs0 : 0 ≤ √D := Real.sqrt_nonneg D
  calc D / 2 * Real.exp (-(α / 2)) = ∫ z in (0 : ℝ)..√D, z * Real.exp (-(α / 2)) := by
        rw [intervalIntegral.integral_mul_const, integral_id, Real.sq_sqrt hD.le]; ring
    _ ≤ ∫ z in (0 : ℝ)..√D, z * Real.exp (-(guardPotential α l₁ z / D)) := by
        apply integral_mono_on hs0 ((by fun_prop : Continuous fun z : ℝ =>
            z * Real.exp (-(α / 2))).intervalIntegrable _ _)
          ((continuous_guardInner_integrand α l₁ D).intervalIntegrable _ _)
        intro z hz
        apply mul_le_mul_of_nonneg_left _ hz.1
        apply Real.exp_le_exp.mpr
        rw [neg_le_neg_iff, div_le_iff₀ hD]
        have h1 := guardPotential_le_quad (α := α) hl z
        have h2 : z ^ 2 ≤ D := by
          have := pow_le_pow_left₀ hz.1 hz.2 2; rwa [Real.sq_sqrt hD.le] at this
        nlinarith
    _ ≤ guardInner α l₁ D a := guardInner_mono hs0 hs

@[powerlib_foundation] theorem guardInner_sub_le (hD : 0 < D) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hU : ∀ z ∈ Icc a b, guardPotential α l₁ a ≤ guardPotential α l₁ z) :
    guardInner α l₁ D b - guardInner α l₁ D a ≤
      (b - a) * (b * Real.exp (-(guardPotential α l₁ a / D))) := by
  rw [guardInner_sub]
  calc ∫ z in a..b, z * Real.exp (-(guardPotential α l₁ z / D))
      ≤ ∫ z in a..b, b * Real.exp (-(guardPotential α l₁ a / D)) := by
        apply integral_mono_on hab ((continuous_guardInner_integrand α l₁ D).intervalIntegrable _ _)
          intervalIntegrable_const
        intro z hz
        apply mul_le_mul hz.2 _ (Real.exp_pos _).le (ha.trans hab)
        apply Real.exp_le_exp.mpr
        rw [neg_le_neg_iff]; exact div_le_div_of_nonneg_right (hU z hz) hD.le
    _ = (b - a) * (b * Real.exp (-(guardPotential α l₁ a / D))) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]

end Inner

section Outer

variable {D : ℝ}

@[powerlib_foundation] theorem guardIntegrand_nonneg {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ guardIntegrand α l₁ D y :=
  mul_nonneg (mul_nonneg (inv_nonneg.2 hy) (Real.exp_pos _).le) (guardInner_nonneg hy)

/-- `y⁻¹ e^{U/D̃} K(y) ≤ (y/2)(e^{U(y)/D̃} + 1)`. -/
@[powerlib_foundation] theorem guardIntegrand_le (hl : 0 < l₁) (hD : 0 < D) {y : ℝ} (hy : 0 < y) :
    guardIntegrand α l₁ D y ≤ y / 2 * (Real.exp (guardPotential α l₁ y / D) + 1) := by
  unfold guardIntegrand
  have hK := guardInner_le (α := α) hl hD hy.le
  have e : Real.exp (guardPotential α l₁ y / D) * Real.exp (-(guardPotential α l₁ y / D)) = 1 := by
    rw [← Real.exp_add]; simp
  calc y⁻¹ * Real.exp (guardPotential α l₁ y / D) * guardInner α l₁ D y
      ≤ y⁻¹ * Real.exp (guardPotential α l₁ y / D) *
          (y ^ 2 / 2 * (1 + Real.exp (-(guardPotential α l₁ y / D)))) :=
        mul_le_mul_of_nonneg_left hK (by positivity)
    _ = y / 2 * (Real.exp (guardPotential α l₁ y / D) +
          Real.exp (guardPotential α l₁ y / D) * Real.exp (-(guardPotential α l₁ y / D))) := by
        field_simp
    _ = y / 2 * (Real.exp (guardPotential α l₁ y / D) + 1) := by rw [e]

@[powerlib_foundation] theorem continuous_exp_guardPotential (α l₁ D : ℝ) :
    Continuous fun y => Real.exp (guardPotential α l₁ y / D) := by
  unfold guardPotential; fun_prop

@[powerlib_foundation] theorem continuousOn_guardIntegrand (α l₁ D : ℝ) :
    ContinuousOn (guardIntegrand α l₁ D) (Ioi 0) := by
  have h1 : ContinuousOn (fun y : ℝ => y⁻¹) (Ioi 0) :=
    continuousOn_inv₀.mono fun y hy => (ne_of_gt hy : y ≠ 0)
  exact (h1.mul (continuous_exp_guardPotential α l₁ D).continuousOn).mul
    (continuous_guardInner α l₁ D).continuousOn

@[powerlib_foundation] theorem intervalIntegrable_guardIntegrand (hl : 0 < l₁) (hD : 0 < D)
    {R : ℝ} (hR : 0 ≤ R) : IntervalIntegrable (guardIntegrand α l₁ D) volume 0 R := by
  refine IntervalIntegrable.mono_fun'
    (g := fun _ => R / 2 * (Real.exp (barrierHeight α l₁ / D) + 1)) intervalIntegrable_const ?_ ?_
  · exact ((measurable_inv.mul (continuous_exp_guardPotential α l₁ D).measurable).mul
      (continuous_guardInner α l₁ D).measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
    rw [uIoc_of_le hR] at hy
    rw [Real.norm_eq_abs, abs_of_nonneg (guardIntegrand_nonneg hy.1.le)]
    refine (guardIntegrand_le hl hD hy.1).trans ?_
    apply mul_le_mul (by linarith [hy.2]) _ (by positivity) (by linarith [hy.2, hy.1])
    have := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      (guardPotential_le_barrier (α := α) hl y) hD.le)
    linarith

@[powerlib_foundation] theorem intervalIntegrable_guardIntegrand_of_pos {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) : IntervalIntegrable (guardIntegrand α l₁ D) volume a b :=
  ((continuousOn_guardIntegrand α l₁ D).mono fun y hy => by
    simp only [mem_Ioi]
    rcases le_total a b with h | h
    · rw [uIcc_of_le h] at hy; linarith [hy.1]
    · rw [uIcc_of_ge h] at hy; linarith [hy.1]).intervalIntegrable

/-- The reflection `ψ(y) = √(2r_c² − y²)` about the barrier top preserves the potential. -/
@[powerlib_foundation] theorem guardPotential_reflect (hl : 0 < l₁) {y : ℝ}
    (hy : y ^ 2 ≤ 2 * (α / l₁)) :
    guardPotential α l₁ √(2 * (α / l₁) - y ^ 2) = guardPotential α l₁ y := by
  apply le_antisymm <;> apply guardPotential_le_of_sq_le hl <;>
    rw [Real.sq_sqrt (by linarith)] <;> nlinarith

/-- Change of variables through the reflection: the part of the outer integral just beyond the
barrier top, `∫_{r_c}^{ψ(a)} h`, equals `∫_a^{r_c} h(ψ(y)) y/ψ(y) dy`. -/
@[powerlib_foundation] theorem integral_guardIntegrand_reflect {a : ℝ} (ha : 0 < a)
    (har : a ≤ √(α / l₁)) (hρ : 0 < α / l₁) :
    ∫ y in √(α / l₁)..√(2 * (α / l₁) - a ^ 2), guardIntegrand α l₁ D y =
      ∫ y in a..√(α / l₁), guardIntegrand α l₁ D √(2 * (α / l₁) - y ^ 2) *
        (y / √(2 * (α / l₁) - y ^ 2)) := by
  set ρ := α / l₁ with hρdef
  set rc := √ρ with hrcdef
  have hrc2 : rc ^ 2 = ρ := Real.sq_sqrt hρ.le
  have hI : ∀ x ∈ uIcc a rc, 0 < 2 * ρ - x ^ 2 := by
    intro x hx
    rw [uIcc_of_le har] at hx
    have : x ^ 2 ≤ rc ^ 2 := pow_le_pow_left₀ (ha.le.trans hx.1) hx.2 2
    linarith
  have hder : ∀ x ∈ uIcc a rc, HasDerivAt (fun x => √(2 * ρ - x ^ 2))
      (-x / √(2 * ρ - x ^ 2)) x := by
    intro x hx
    have h := ((hasDerivAt_pow 2 x).const_sub (2 * ρ)).sqrt (hI x hx).ne'
    convert h using 1
    field_simp
    push_cast; ring
  have hcont' : ContinuousOn (fun x => -x / √(2 * ρ - x ^ 2)) (uIcc a rc) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx; exact (Real.sqrt_pos.mpr (hI x hx)).ne'
  have hg : ContinuousOn (guardIntegrand α l₁ D) ((fun x => √(2 * ρ - x ^ 2)) '' uIcc a rc) := by
    apply (continuousOn_guardIntegrand α l₁ D).mono
    rintro _ ⟨x, hx, rfl⟩
    exact Real.sqrt_pos.mpr (hI x hx)
  have h := integral_comp_mul_deriv' hder hcont' hg
  have hend : √(2 * ρ - rc ^ 2) = rc := by rw [hrc2, show 2 * ρ - ρ = ρ by ring]
  simp only [Function.comp_def, hend] at h
  rw [integral_symm, ← h, ← intervalIntegral.integral_neg]
  congr 1
  funext y
  ring

end Outer

/-! ## The ratio `T_committed / T_guard → 2` -/

/-- Relative size of the tails, an explicit upper bound for `(A_tail + B_tail)/(K(a) I)`. -/
def guardEps (α l₁ a rb D : ℝ) : ℝ :=
  (a ^ 2 / 2 + (rb - √(2 * (α / l₁) - a ^ 2)) * (rb / 2)) *
      (Real.exp (guardPotential α l₁ a / D) + 1) /
    (D / 2 * Real.exp (-(α / 2)) * ((√(α / l₁) - (a + √(α / l₁)) / 2) / √(α / l₁) *
      Real.exp (guardPotential α l₁ ((a + √(α / l₁)) / 2) / D)))

/-- Relative growth of the inner integral across the barrier, an explicit upper bound for
`K(ψ(a))/K(a) − 1`. -/
def guardKappa (α l₁ a D : ℝ) : ℝ :=
  (√(2 * (α / l₁) - a ^ 2) - a) * (√(2 * (α / l₁) - a ^ 2) *
    Real.exp (-(guardPotential α l₁ a / D))) / (D / 2 * Real.exp (-(α / 2)))

section Ratio

variable {D : ℝ}

@[powerlib_foundation] private theorem frac_le_inv {y ρ : ℝ} (hy0 : 0 < y) (hy2 : y ^ 2 ≤ ρ) :
    y / (2 * ρ - y ^ 2) ≤ y⁻¹ := by
  have hpos : 0 < 2 * ρ - y ^ 2 := by nlinarith
  rw [div_le_iff₀ hpos, inv_mul_eq_div, le_div_iff₀ hy0]
  nlinarith

@[powerlib_foundation] private theorem frac_ge {a y ρ : ℝ} (ha : 0 < a) (hay : a ≤ y)
    (hy2 : y ^ 2 ≤ ρ) : a ^ 2 / (2 * ρ - a ^ 2) * y⁻¹ ≤ y / (2 * ρ - y ^ 2) := by
  have hy0 : 0 < y := ha.trans_le hay
  have hya : a ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ ha.le hay 2
  have hpos : 0 < 2 * ρ - y ^ 2 := by nlinarith
  have hposa : 0 < 2 * ρ - a ^ 2 := by nlinarith
  have h1 : a ^ 2 / (2 * ρ - a ^ 2) ≤ y ^ 2 / (2 * ρ - y ^ 2) := by
    rw [div_le_div_iff₀ hposa hpos]; nlinarith
  calc a ^ 2 / (2 * ρ - a ^ 2) * y⁻¹ ≤ y ^ 2 / (2 * ρ - y ^ 2) * y⁻¹ :=
        mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hy0.le)
    _ = y / (2 * ρ - y ^ 2) := by field_simp

/-- The reflected integrand `h(ψ(y)) y/ψ(y) = y/(2r_c² − y²) · e^{U(y)/D̃} · K(ψ(y))`. -/
@[powerlib_foundation] private theorem guardIntegrand_reflect_eq (hl : 0 < l₁) {y : ℝ}
    (hy2 : y ^ 2 < 2 * (α / l₁)) :
    guardIntegrand α l₁ D √(2 * (α / l₁) - y ^ 2) * (y / √(2 * (α / l₁) - y ^ 2)) =
      y / (2 * (α / l₁) - y ^ 2) * Real.exp (guardPotential α l₁ y / D) *
        guardInner α l₁ D √(2 * (α / l₁) - y ^ 2) := by
  have hpos : 0 < 2 * (α / l₁) - y ^ 2 := by linarith
  have hs : √(2 * (α / l₁) - y ^ 2) ^ 2 = 2 * (α / l₁) - y ^ 2 := Real.sq_sqrt hpos.le
  have hs0 : 0 < √(2 * (α / l₁) - y ^ 2) := Real.sqrt_pos.mpr hpos
  have hU := guardPotential_reflect (α := α) hl (y := y) hy2.le
  simp only [guardIntegrand]
  rw [hU]
  have e : (√(2 * (α / l₁) - y ^ 2))⁻¹ * (y / √(2 * (α / l₁) - y ^ 2)) =
      y / (2 * (α / l₁) - y ^ 2) := by
    generalize √(2 * (α / l₁) - y ^ 2) = S at hs hs0 ⊢
    rw [← hs]; field_simp
  calc (√(2 * (α / l₁) - y ^ 2))⁻¹ * Real.exp (guardPotential α l₁ y / D) *
        guardInner α l₁ D √(2 * (α / l₁) - y ^ 2) * (y / √(2 * (α / l₁) - y ^ 2))
      = ((√(2 * (α / l₁) - y ^ 2))⁻¹ * (y / √(2 * (α / l₁) - y ^ 2))) *
          Real.exp (guardPotential α l₁ y / D) * guardInner α l₁ D √(2 * (α / l₁) - y ^ 2) := by
        ring
    _ = y / (2 * (α / l₁) - y ^ 2) * Real.exp (guardPotential α l₁ y / D) *
          guardInner α l₁ D √(2 * (α / l₁) - y ^ 2) := by rw [e]

@[powerlib_foundation] private theorem intervalIntegrable_guardIntegrand_reflect {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb2 : b ^ 2 < 2 * (α / l₁)) :
    IntervalIntegrable (fun y => guardIntegrand α l₁ D √(2 * (α / l₁) - y ^ 2) *
      (y / √(2 * (α / l₁) - y ^ 2))) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  intro y hy
  have hy2 : y ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (ha.le.trans hy.1) hy.2 2
  have hpos : 0 < 2 * (α / l₁) - y ^ 2 := by linarith
  have hc1 : ContinuousWithinAt (fun y => √(2 * (α / l₁) - y ^ 2)) (Icc a b) y := by fun_prop
  have hct : ContinuousAt (guardIntegrand α l₁ D) ((fun y => √(2 * (α / l₁) - y ^ 2)) y) :=
    (continuousOn_guardIntegrand α l₁ D).continuousAt (Ioi_mem_nhds (Real.sqrt_pos.mpr hpos))
  have hc2 : ContinuousWithinAt (fun y : ℝ => y) (Icc a b) y := continuousWithinAt_id
  exact (ContinuousAt.comp_continuousWithinAt (f := fun y => √(2 * (α / l₁) - y ^ 2)) (x := y)
    hct hc1).mul (hc2.div hc1 (Real.sqrt_pos.mpr hpos).ne')

/-- The weight `w(y) = y⁻¹ e^{U(y)/D̃}` is interval integrable on `[a, b]`, `0 < a ≤ b`. -/
@[powerlib_foundation] private theorem intervalIntegrable_guardWeight {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    IntervalIntegrable (fun y => y⁻¹ * Real.exp (guardPotential α l₁ y / D)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply ContinuousOn.mul _ (continuous_exp_guardPotential α l₁ D).continuousOn
  exact continuousOn_inv₀.mono fun y hy => (ne_of_gt (ha.trans_le hy.1) : y ≠ 0)

/-- The part of the outer integral just inside the barrier top:
`K(a) I ≤ ∫_a^{r_c} h ≤ K(r_c) I`, `I = ∫_a^{r_c} y⁻¹ e^{U/D̃}`. -/
@[powerlib_foundation] private theorem guard_inside_bounds {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    guardInner α l₁ D a * ∫ y in a..b, y⁻¹ * Real.exp (guardPotential α l₁ y / D) ≤
        ∫ y in a..b, guardIntegrand α l₁ D y ∧
      ∫ y in a..b, guardIntegrand α l₁ D y ≤
        guardInner α l₁ D b * ∫ y in a..b, y⁻¹ * Real.exp (guardPotential α l₁ y / D) := by
  have hw := intervalIntegrable_guardWeight (α := α) (l₁ := l₁) (D := D) ha hab
  have hh : IntervalIntegrable (guardIntegrand α l₁ D) volume a b :=
    intervalIntegrable_guardIntegrand_of_pos ha (ha.trans_le hab)
  constructor
  · rw [← intervalIntegral.integral_const_mul]
    apply integral_mono_on hab (hw.const_mul _) hh
    intro y hy
    have hy0 : 0 < y := ha.trans_le hy.1
    simp only [guardIntegrand]
    rw [mul_comm (guardInner α l₁ D a)]
    exact mul_le_mul_of_nonneg_left (guardInner_mono ha.le hy.1)
      (mul_nonneg (inv_nonneg.2 hy0.le) (Real.exp_pos _).le)
  · rw [← intervalIntegral.integral_const_mul]
    apply integral_mono_on hab hh (hw.const_mul _)
    intro y hy
    have hy0 : 0 < y := ha.trans_le hy.1
    simp only [guardIntegrand]
    rw [mul_comm (guardInner α l₁ D b)]
    exact mul_le_mul_of_nonneg_left (guardInner_mono hy0.le hy.2)
      (mul_nonneg (inv_nonneg.2 hy0.le) (Real.exp_pos _).le)

/-- The part just beyond the barrier top, through the reflection:
`a²/(2r_c² − a²) K(r_c) I ≤ ∫_{r_c}^{ψ(a)} h ≤ K(ψ(a)) I`. -/
@[powerlib_foundation] private theorem guard_beyond_bounds (hl : 0 < l₁) {a : ℝ} (ha : 0 < a)
    (har : a ≤ √(α / l₁)) (hρ : 0 < α / l₁) :
    a ^ 2 / (2 * (α / l₁) - a ^ 2) *
        (guardInner α l₁ D √(α / l₁) *
          ∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D)) ≤
        ∫ y in √(α / l₁)..√(2 * (α / l₁) - a ^ 2), guardIntegrand α l₁ D y ∧
      ∫ y in √(α / l₁)..√(2 * (α / l₁) - a ^ 2), guardIntegrand α l₁ D y ≤
        guardInner α l₁ D √(2 * (α / l₁) - a ^ 2) *
          ∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D) := by
  have hrc2 : √(α / l₁) ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  have hrc : 0 < √(α / l₁) := Real.sqrt_pos.mpr hρ
  have hw := intervalIntegrable_guardWeight (α := α) (l₁ := l₁) (D := D) ha har
  have hri := intervalIntegrable_guardIntegrand_reflect (α := α) (l₁ := l₁) (D := D) ha har
    (by rw [hrc2]; linarith)
  have hy2 : ∀ y ∈ Icc a √(α / l₁), y ^ 2 ≤ α / l₁ := fun y hy => by
    have := pow_le_pow_left₀ (ha.le.trans hy.1) hy.2 2; rwa [hrc2] at this
  rw [integral_guardIntegrand_reflect ha har hρ]
  constructor
  · rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply integral_mono_on har ((hw.const_mul _).const_mul _) hri
    intro y hy
    have hy0 : 0 < y := ha.trans_le hy.1
    rw [guardIntegrand_reflect_eq hl (by linarith [hy2 y hy, hρ])]
    have hK1 : guardInner α l₁ D √(α / l₁) ≤ guardInner α l₁ D √(2 * (α / l₁) - y ^ 2) :=
      guardInner_mono hrc.le (Real.sqrt_le_sqrt (by linarith [hy2 y hy]))
    have hfac := frac_ge ha hy.1 (hy2 y hy)
    calc a ^ 2 / (2 * (α / l₁) - a ^ 2) *
          (guardInner α l₁ D √(α / l₁) * (y⁻¹ * Real.exp (guardPotential α l₁ y / D)))
        = (a ^ 2 / (2 * (α / l₁) - a ^ 2) * y⁻¹) * Real.exp (guardPotential α l₁ y / D) *
            guardInner α l₁ D √(α / l₁) := by ring
      _ ≤ y / (2 * (α / l₁) - y ^ 2) * Real.exp (guardPotential α l₁ y / D) *
            guardInner α l₁ D √(2 * (α / l₁) - y ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hfac (Real.exp_pos _).le) hK1
            (guardInner_nonneg hrc.le) (mul_nonneg (div_nonneg hy0.le
              (by linarith [hy2 y hy])) (Real.exp_pos _).le)
  · rw [← intervalIntegral.integral_const_mul]
    apply integral_mono_on har hri (hw.const_mul _)
    intro y hy
    have hy0 : 0 < y := ha.trans_le hy.1
    rw [guardIntegrand_reflect_eq hl (by linarith [hy2 y hy, hρ])]
    have hK1 : guardInner α l₁ D √(2 * (α / l₁) - y ^ 2) ≤
        guardInner α l₁ D √(2 * (α / l₁) - a ^ 2) := by
      apply guardInner_mono (Real.sqrt_nonneg _)
      apply Real.sqrt_le_sqrt
      have := pow_le_pow_left₀ ha.le hy.1 2; linarith
    have hfac := frac_le_inv hy0 (hy2 y hy)
    calc y / (2 * (α / l₁) - y ^ 2) * Real.exp (guardPotential α l₁ y / D) *
          guardInner α l₁ D √(2 * (α / l₁) - y ^ 2)
        ≤ y⁻¹ * Real.exp (guardPotential α l₁ y / D) *
            guardInner α l₁ D √(2 * (α / l₁) - a ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hfac (Real.exp_pos _).le) hK1
            (guardInner_nonneg (Real.sqrt_nonneg _))
            (mul_nonneg (inv_nonneg.2 hy0.le) (Real.exp_pos _).le)
      _ = guardInner α l₁ D √(2 * (α / l₁) - a ^ 2) *
            (y⁻¹ * Real.exp (guardPotential α l₁ y / D)) := by ring

/-- Lower bound for the main weight integral: `I ≥ ((r_c − m)/r_c) e^{U(m)/D̃}` for `a ≤ m ≤ r_c`
with `U ≥ U(m)` on `[m, r_c]`. -/
@[powerlib_foundation] private theorem guard_weight_ge (hD : 0 < D) {a m rc : ℝ} (ha : 0 < a)
    (ham : a ≤ m) (hmr : m ≤ rc)
    (hU : ∀ y ∈ Icc m rc, guardPotential α l₁ m ≤ guardPotential α l₁ y) :
    (rc - m) / rc * Real.exp (guardPotential α l₁ m / D) ≤
      ∫ y in a..rc, y⁻¹ * Real.exp (guardPotential α l₁ y / D) := by
  have hm0 : 0 < m := ha.trans_le ham
  have hrc0 : 0 < rc := hm0.trans_le hmr
  calc (rc - m) / rc * Real.exp (guardPotential α l₁ m / D) =
        ∫ y in m..rc, rc⁻¹ * Real.exp (guardPotential α l₁ m / D) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    _ ≤ ∫ y in m..rc, y⁻¹ * Real.exp (guardPotential α l₁ y / D) := by
        apply integral_mono_on hmr intervalIntegrable_const
          (intervalIntegrable_guardWeight hm0 hmr)
        intro y hy
        have hy0 : 0 < y := hm0.trans_le hy.1
        apply mul_le_mul (inv_anti₀ hy0 hy.2) _ (Real.exp_pos _).le (inv_nonneg.2 hy0.le)
        exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hU y hy) hD.le)
    _ ≤ ∫ y in a..rc, y⁻¹ * Real.exp (guardPotential α l₁ y / D) := by
        apply integral_mono_interval ham hmr le_rfl
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
          exact mul_nonneg (inv_nonneg.2 (ha.trans hy.1).le) (Real.exp_pos _).le
        · exact intervalIntegrable_guardWeight ha (ham.trans hmr)

/-- Tail bound: `∫_c^d h ≤ (d − c)(d/2)(e^{U*/D̃} + 1)` when `U ≤ U*` on `[c, d]`, `0 ≤ c ≤ d`. -/
@[powerlib_foundation] private theorem guard_tail_le (hl : 0 < l₁) (hD : 0 < D) {c d Us : ℝ}
    (hc : 0 ≤ c) (hcd : c ≤ d) (hU : ∀ y ∈ Icc c d, guardPotential α l₁ y ≤ Us)
    (hint : IntervalIntegrable (guardIntegrand α l₁ D) volume c d) :
    ∫ y in c..d, guardIntegrand α l₁ D y ≤ (d - c) * (d / 2 * (Real.exp (Us / D) + 1)) := by
  calc ∫ y in c..d, guardIntegrand α l₁ D y ≤ ∫ y in c..d, d / 2 * (Real.exp (Us / D) + 1) := by
        apply integral_mono_on hcd hint intervalIntegrable_const
        intro y hy
        rcases eq_or_lt_of_le (hc.trans hy.1) with h0 | h0
        · rw [← h0]; simp only [guardIntegrand, inv_zero, zero_mul]
          have : 0 ≤ d := hc.trans hcd
          positivity
        · refine (guardIntegrand_le hl hD h0).trans ?_
          apply mul_le_mul (by linarith [hy.2]) _ (by positivity) (by linarith [hc, hcd])
          have := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hU y hy) hD.le)
          linarith
    _ = (d - c) * (d / 2 * (Real.exp (Us / D) + 1)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]

/-- Deterministic bounds at a fixed cut `a ∈ (0, r_c)` with reflected cut `ψ(a) ≤ r_b` and
`D̃ ≤ a²`: with `A = ∫₀^{r_c} h` and `B = ∫_{r_c}^{r_b} h`,
`0 < A`, `B ≤ (1 + κ + ε) A` and `a²/(2r_c² − a²) · A ≤ (1 + ε) B`. -/
@[powerlib_foundation] theorem guard_ratio_bounds (hα : 0 < α) (hl : 0 < l₁) {a rb : ℝ}
    (ha : 0 < a) (har : a < √(α / l₁)) (hψ : √(2 * (α / l₁) - a ^ 2) ≤ rb) (hD : 0 < D)
    (hDa : D ≤ a ^ 2) :
    0 < ∫ y in (0 : ℝ)..√(α / l₁), guardIntegrand α l₁ D y ∧
      ∫ y in √(α / l₁)..rb, guardIntegrand α l₁ D y ≤
        (1 + guardKappa α l₁ a D + guardEps α l₁ a rb D) *
          ∫ y in (0 : ℝ)..√(α / l₁), guardIntegrand α l₁ D y ∧
      a ^ 2 / (2 * (α / l₁) - a ^ 2) * ∫ y in (0 : ℝ)..√(α / l₁), guardIntegrand α l₁ D y ≤
        (1 + guardEps α l₁ a rb D) * ∫ y in √(α / l₁)..rb, guardIntegrand α l₁ D y := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hrc : 0 < √(α / l₁) := Real.sqrt_pos.mpr hρ
  have hrc2 : √(α / l₁) ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  have ha2 : a ^ 2 < α / l₁ := by
    have := pow_lt_pow_left₀ har ha.le (two_ne_zero); rwa [hrc2] at this
  have hψa2 : √(2 * (α / l₁) - a ^ 2) ^ 2 = 2 * (α / l₁) - a ^ 2 := Real.sq_sqrt (by linarith)
  have hrcψ : √(α / l₁) ≤ √(2 * (α / l₁) - a ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have hψ0 : 0 < √(2 * (α / l₁) - a ^ 2) := hrc.trans_le hrcψ
  have hrb0 : 0 < rb := hψ0.trans_le hψ
  have ham : a < (a + √(α / l₁)) / 2 := by linarith
  have hmr : (a + √(α / l₁)) / 2 < √(α / l₁) := by linarith
  -- potential comparisons
  have hUa_le : ∀ y ∈ Icc 0 a, guardPotential α l₁ y ≤ guardPotential α l₁ a := by
    intro y hy
    apply guardPotential_le_of_sq_le hl
    have : y ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hy.1 hy.2 2
    nlinarith [sq_nonneg y]
  have hUψ_le : ∀ y ∈ Icc √(2 * (α / l₁) - a ^ 2) rb,
      guardPotential α l₁ y ≤ guardPotential α l₁ a := by
    intro y hy
    apply guardPotential_le_of_sq_le hl
    have : √(2 * (α / l₁) - a ^ 2) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hψ0.le hy.1 2
    nlinarith
  have hUa_ge : ∀ z ∈ Icc a √(2 * (α / l₁) - a ^ 2),
      guardPotential α l₁ a ≤ guardPotential α l₁ z := by
    intro z hz
    apply guardPotential_le_of_sq_le hl
    have h1 : a ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ ha.le hz.1 2
    have h2 : z ^ 2 ≤ √(2 * (α / l₁) - a ^ 2) ^ 2 := pow_le_pow_left₀ (ha.le.trans hz.1) hz.2 2
    nlinarith
  have hUm_ge : ∀ y ∈ Icc ((a + √(α / l₁)) / 2) √(α / l₁),
      guardPotential α l₁ ((a + √(α / l₁)) / 2) ≤ guardPotential α l₁ y := by
    intro y hy
    apply guardPotential_le_of_sq_le hl
    have hm0 : 0 < (a + √(α / l₁)) / 2 := by linarith
    have h1 : ((a + √(α / l₁)) / 2) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hm0.le hy.1 2
    have h2 : y ^ 2 ≤ √(α / l₁) ^ 2 := pow_le_pow_left₀ (hm0.le.trans hy.1) hy.2 2
    nlinarith
  -- the pieces
  have hKa := guardInner_ge (l₁ := l₁) hα.le hl.le hD ha.le hDa
  have hKa0 : 0 < guardInner α l₁ D a := lt_of_lt_of_le (by positivity) hKa
  have hKar : guardInner α l₁ D a ≤ guardInner α l₁ D √(α / l₁) := guardInner_mono ha.le har.le
  have hKψ := guardInner_sub_le (l₁ := l₁) hD ha.le (har.le.trans hrcψ) hUa_ge
  obtain ⟨hAm_lo, hAm_hi⟩ := guard_inside_bounds (α := α) (l₁ := l₁) (D := D) ha har.le
  obtain ⟨hBm_lo, hBm_hi⟩ := guard_beyond_bounds (D := D) hl ha har.le hρ
  have hI := guard_weight_ge (l₁ := l₁) hD ha ham.le hmr.le hUm_ge
  have hint0a : IntervalIntegrable (guardIntegrand α l₁ D) volume 0 a :=
    intervalIntegrable_guardIntegrand hl hD ha.le
  have hintar : IntervalIntegrable (guardIntegrand α l₁ D) volume a √(α / l₁) :=
    intervalIntegrable_guardIntegrand_of_pos ha hrc
  have hintrψ : IntervalIntegrable (guardIntegrand α l₁ D) volume √(α / l₁)
      √(2 * (α / l₁) - a ^ 2) := intervalIntegrable_guardIntegrand_of_pos hrc hψ0
  have hintψb : IntervalIntegrable (guardIntegrand α l₁ D) volume √(2 * (α / l₁) - a ^ 2) rb :=
    intervalIntegrable_guardIntegrand_of_pos hψ0 (hψ0.trans_le hψ)
  have hAt := guard_tail_le (l₁ := l₁) hl hD le_rfl ha.le hUa_le hint0a
  have hBt := guard_tail_le (l₁ := l₁) hl hD hψ0.le hψ hUψ_le hintψb
  have hAt0 : 0 ≤ ∫ y in (0 : ℝ)..a, guardIntegrand α l₁ D y :=
    integral_nonneg ha.le fun y hy => guardIntegrand_nonneg hy.1
  have hBt0 : 0 ≤ ∫ y in √(2 * (α / l₁) - a ^ 2)..rb, guardIntegrand α l₁ D y :=
    integral_nonneg hψ fun y hy => guardIntegrand_nonneg (hψ0.le.trans hy.1)
  rw [← integral_add_adjacent_intervals hint0a hintar,
    ← integral_add_adjacent_intervals hintrψ hintψb]
  -- abbreviations
  generalize hIdef : (∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D)) = I
    at hAm_lo hAm_hi hBm_lo hBm_hi hI
  generalize hAt' : (∫ y in (0 : ℝ)..a, guardIntegrand α l₁ D y) = At at hAt hAt0 ⊢
  generalize hAm' : (∫ y in a..√(α / l₁), guardIntegrand α l₁ D y) = Am at hAm_lo hAm_hi ⊢
  generalize hBm' : (∫ y in √(α / l₁)..√(2 * (α / l₁) - a ^ 2), guardIntegrand α l₁ D y) = Bm
    at hBm_lo hBm_hi ⊢
  generalize hBt' : (∫ y in √(2 * (α / l₁) - a ^ 2)..rb, guardIntegrand α l₁ D y) = Bt
    at hBt hBt0 ⊢
  have hrm : 0 < √(α / l₁) - (a + √(α / l₁)) / 2 := by linarith
  have hI0 : 0 < I := lt_of_lt_of_le (by positivity) hI
  have hKaI : 0 < guardInner α l₁ D a * I := mul_pos hKa0 hI0
  -- `At + Bt ≤ ε K(a) I`
  have hQ : D / 2 * Real.exp (-(α / 2)) * ((√(α / l₁) - (a + √(α / l₁)) / 2) / √(α / l₁) *
      Real.exp (guardPotential α l₁ ((a + √(α / l₁)) / 2) / D)) ≤ guardInner α l₁ D a * I :=
    mul_le_mul hKa hI (by positivity) hKa0.le
  have heps : At + Bt ≤ guardEps α l₁ a rb D * (guardInner α l₁ D a * I) := by
    have hP0 : 0 ≤ (a ^ 2 / 2 + (rb - √(2 * (α / l₁) - a ^ 2)) * (rb / 2)) *
        (Real.exp (guardPotential α l₁ a / D) + 1) := by
      have : 0 ≤ rb - √(2 * (α / l₁) - a ^ 2) := by linarith
      positivity
    have hP : At + Bt ≤ (a ^ 2 / 2 + (rb - √(2 * (α / l₁) - a ^ 2)) * (rb / 2)) *
        (Real.exp (guardPotential α l₁ a / D) + 1) := by
      have h1 : (a - 0) * (a / 2 * (Real.exp (guardPotential α l₁ a / D) + 1)) =
          a ^ 2 / 2 * (Real.exp (guardPotential α l₁ a / D) + 1) := by ring
      have h2 : (rb - √(2 * (α / l₁) - a ^ 2)) * (rb / 2 *
          (Real.exp (guardPotential α l₁ a / D) + 1)) = (rb - √(2 * (α / l₁) - a ^ 2)) *
          (rb / 2) * (Real.exp (guardPotential α l₁ a / D) + 1) := by ring
      rw [h1] at hAt; rw [h2] at hBt
      linarith
    refine hP.trans ?_
    unfold guardEps
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left hQ hP0
  have heps0 : 0 ≤ guardEps α l₁ a rb D := by
    by_contra hneg; push Not at hneg
    have : guardEps α l₁ a rb D * (guardInner α l₁ D a * I) < 0 := mul_neg_of_neg_of_pos hneg hKaI
    linarith
  -- `K(ψ(a)) ≤ (1 + κ) K(a)`
  have hkap : guardInner α l₁ D √(2 * (α / l₁) - a ^ 2) ≤
      (1 + guardKappa α l₁ a D) * guardInner α l₁ D a := by
    have hk : (√(2 * (α / l₁) - a ^ 2) - a) * (√(2 * (α / l₁) - a ^ 2) *
        Real.exp (-(guardPotential α l₁ a / D))) ≤ guardKappa α l₁ a D * guardInner α l₁ D a := by
      unfold guardKappa
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : 0 ≤ (√(2 * (α / l₁) - a ^ 2) - a) * (√(2 * (α / l₁) - a ^ 2) *
          Real.exp (-(guardPotential α l₁ a / D))) := by
        have : 0 ≤ √(2 * (α / l₁) - a ^ 2) - a := by linarith
        positivity
      exact mul_le_mul_of_nonneg_left hKa this
    linarith
  have hkap0 : 0 ≤ guardKappa α l₁ a D := by
    unfold guardKappa
    have : 0 ≤ √(2 * (α / l₁) - a ^ 2) - a := by linarith
    positivity
  have hAt_le : At ≤ guardEps α l₁ a rb D * Am := by
    have := mul_le_mul_of_nonneg_left hAm_lo heps0
    linarith
  have hBt_le : Bt ≤ guardEps α l₁ a rb D * Am := by
    have := mul_le_mul_of_nonneg_left hAm_lo heps0
    linarith
  have hAm0 : 0 < Am := lt_of_lt_of_le hKaI hAm_lo
  have hL0 : 0 ≤ a ^ 2 / (2 * (α / l₁) - a ^ 2) := div_nonneg (sq_nonneg a) (by linarith)
  refine ⟨by linarith, ?_, ?_⟩
  · have h1 : guardInner α l₁ D √(2 * (α / l₁) - a ^ 2) * I ≤
        (1 + guardKappa α l₁ a D) * (guardInner α l₁ D a * I) := by
      have := mul_le_mul_of_nonneg_right hkap hI0.le; linarith
    have h2 : (1 + guardKappa α l₁ a D) * (guardInner α l₁ D a * I) ≤
        (1 + guardKappa α l₁ a D) * Am := mul_le_mul_of_nonneg_left hAm_lo (by linarith)
    have h3 : (1 + guardKappa α l₁ a D + guardEps α l₁ a rb D) * Am ≤
        (1 + guardKappa α l₁ a D + guardEps α l₁ a rb D) * (At + Am) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    calc Bm + Bt ≤ (1 + guardKappa α l₁ a D) * Am + guardEps α l₁ a rb D * Am := by linarith
      _ = (1 + guardKappa α l₁ a D + guardEps α l₁ a rb D) * Am := by ring
      _ ≤ _ := h3
  · have h1 : a ^ 2 / (2 * (α / l₁) - a ^ 2) * (At + Am) ≤
        a ^ 2 / (2 * (α / l₁) - a ^ 2) * ((1 + guardEps α l₁ a rb D) * Am) := by
      apply mul_le_mul_of_nonneg_left _ hL0; linarith
    have h2 : a ^ 2 / (2 * (α / l₁) - a ^ 2) * Am ≤
        a ^ 2 / (2 * (α / l₁) - a ^ 2) * (guardInner α l₁ D √(α / l₁) * I) :=
      mul_le_mul_of_nonneg_left hAm_hi hL0
    have h3 : a ^ 2 / (2 * (α / l₁) - a ^ 2) * ((1 + guardEps α l₁ a rb D) * Am) ≤
        (1 + guardEps α l₁ a rb D) * Bm := by
      calc a ^ 2 / (2 * (α / l₁) - a ^ 2) * ((1 + guardEps α l₁ a rb D) * Am)
          = (1 + guardEps α l₁ a rb D) * (a ^ 2 / (2 * (α / l₁) - a ^ 2) * Am) := by ring
        _ ≤ (1 + guardEps α l₁ a rb D) * Bm :=
          mul_le_mul_of_nonneg_left (h2.trans hBm_lo) (by linarith)
    have h4 : (1 + guardEps α l₁ a rb D) * Bm ≤ (1 + guardEps α l₁ a rb D) * (Bm + Bt) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith

/-- `e^{−c/D̃}/D̃ → 0` as `D̃ → 0⁺` (`c > 0`). -/
@[powerlib_foundation] theorem tendsto_exp_neg_div_div {c : ℝ} (hc : 0 < c) :
    Tendsto (fun D : ℝ => Real.exp (-(c / D)) / D) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => t * Real.exp (-(c * t))) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.const_mul_atTop hc)).const_mul c⁻¹
    rw [mul_zero] at h
    refine h.congr fun t => ?_
    simp only [Function.comp_apply, id, pow_one]
    field_simp
  refine (h1.comp tendsto_inv_nhdsGT_zero).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with D hD
  simp only [Function.comp_apply]
  rw [div_eq_mul_inv, mul_comm, div_eq_mul_inv c]

@[powerlib_foundation] theorem tendsto_guardKappa (hl : 0 < l₁) {a : ℝ} (ha : 0 < a)
    (ha2 : a ^ 2 < 2 * (α / l₁)) : Tendsto (guardKappa α l₁ a) (𝓝[>] 0) (𝓝 0) := by
  have hU := guardPotential_pos (α := α) hl ha ha2
  have h := (tendsto_exp_neg_div_div hU).const_mul
    ((√(2 * (α / l₁) - a ^ 2) - a) * √(2 * (α / l₁) - a ^ 2) / (Real.exp (-(α / 2)) / 2))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with D hD
  have hD0 : (D : ℝ) ≠ 0 := ne_of_gt hD
  simp only [guardKappa]
  field_simp

@[powerlib_foundation] theorem tendsto_guardEps (hl : 0 < l₁) {a rb : ℝ} (ha : 0 < a)
    (har : a < √(α / l₁)) (hρ : 0 < α / l₁) : Tendsto (guardEps α l₁ a rb) (𝓝[>] 0) (𝓝 0) := by
  set m := (a + √(α / l₁)) / 2 with hmdef
  have hrc2 : √(α / l₁) ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  have hrc : 0 < √(α / l₁) := Real.sqrt_pos.mpr hρ
  have ham : a < m := by simp only [hmdef]; linarith
  have hmr : m < √(α / l₁) := by simp only [hmdef]; linarith
  have hm0 : 0 < m := ha.trans ham
  have hm2 : m ^ 2 < α / l₁ := by
    have := pow_lt_pow_left₀ hmr hm0.le two_ne_zero; rwa [hrc2] at this
  have ha2 : a ^ 2 < m ^ 2 := pow_lt_pow_left₀ ham ha.le two_ne_zero
  have hUm : 0 < guardPotential α l₁ m := guardPotential_pos hl hm0 (by linarith)
  have hUma : 0 < guardPotential α l₁ m - guardPotential α l₁ a := by
    rw [guardPotential_eq_barrier_sub hl, guardPotential_eq_barrier_sub hl]
    have : (m ^ 2 - α / l₁) ^ 2 < (a ^ 2 - α / l₁) ^ 2 := by nlinarith
    have : 0 < l₁ / 4 := by positivity
    nlinarith
  have hq : 0 < (√(α / l₁) - m) / √(α / l₁) := div_pos (by linarith) hrc
  set C := (a ^ 2 / 2 + (rb - √(2 * (α / l₁) - a ^ 2)) * (rb / 2)) /
    (Real.exp (-(α / 2)) / 2 * ((√(α / l₁) - m) / √(α / l₁))) with hCdef
  have h := ((tendsto_exp_neg_div_div hUma).add (tendsto_exp_neg_div_div hUm)).const_mul C
  rw [add_zero, mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with D hD
  have hD0 : (D : ℝ) ≠ 0 := ne_of_gt hD
  have e1 : Real.exp (-((guardPotential α l₁ m - guardPotential α l₁ a) / D)) =
      Real.exp (guardPotential α l₁ a / D) / Real.exp (guardPotential α l₁ m / D) := by
    rw [← Real.exp_sub]; congr 1; field_simp; ring
  have e2 : Real.exp (-(guardPotential α l₁ m / D)) = 1 / Real.exp (guardPotential α l₁ m / D) := by
    rw [Real.exp_neg, one_div]
  simp only [guardEps, ← hmdef, hCdef]
  rw [e1, e2]
  have hE := Real.exp_pos (guardPotential α l₁ m / D)
  have hE2 := Real.exp_pos (-(α / 2))
  have hq' : (√(α / l₁) - m) / √(α / l₁) ≠ 0 := hq.ne'
  field_simp

/-- **`T_committed / T_guard → 2`** (source §1.2): for the truncated subcritical-Hopf potential
`U(r) = αr²/2 − l₁r⁴/4` (`α, l₁ > 0`) and any committed-escape boundary `r_b > r_c = √(α/l₁)`,
the ratio of the mean first-passage times `T(r_b)/T(r_c)` (`guardMFPT`) tends to `2` as the noise
intensity `D̃ → 0⁺` (equivalently `X = ΔU/D̃ → ∞`): stopping at the barrier top integrates only
half of the Gaussian barrier peak. -/
@[powerlib_foundation] theorem tendsto_guardMFPT_ratio (hα : 0 < α) (hl : 0 < l₁) {rb : ℝ}
    (hrb : guardRadius α l₁ < rb) :
    Tendsto (fun D => guardMFPT α l₁ D rb / guardMFPT α l₁ D (guardRadius α l₁))
      (𝓝[>] 0) (𝓝 2) := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  set rc := guardRadius α l₁ with hrcdef
  have hrcs : rc = √(α / l₁) := rfl
  have hrc : 0 < rc := Real.sqrt_pos.mpr hρ
  have hrc2 : rc ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  -- the ratio as `1 + B/A`
  have hratio : ∀ D, 0 < D → guardMFPT α l₁ D rb / guardMFPT α l₁ D rc =
      ((∫ y in (0 : ℝ)..rc, guardIntegrand α l₁ D y) +
        ∫ y in rc..rb, guardIntegrand α l₁ D y) / ∫ y in (0 : ℝ)..rc, guardIntegrand α l₁ D y := by
    intro D hD
    simp only [guardMFPT]
    rw [← integral_add_adjacent_intervals (intervalIntegrable_guardIntegrand hl hD hrc.le)
      (intervalIntegrable_guardIntegrand_of_pos hrc (hrc.trans hrb))]
    exact mul_div_mul_left _ _ (inv_ne_zero (ne_of_gt hD))
  -- choosing the cut `a`
  have hcut : ∀ t < 1, ∃ a, 0 < a ∧ a < rc ∧ √(2 * (α / l₁) - a ^ 2) ≤ rb ∧
      t < a ^ 2 / (2 * (α / l₁) - a ^ 2) := by
    intro t ht
    have hψc : ContinuousAt (fun a : ℝ => √(2 * (α / l₁) - a ^ 2)) rc := by fun_prop
    have hLc : ContinuousAt (fun a : ℝ => a ^ 2 / (2 * (α / l₁) - a ^ 2)) rc := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      rw [hrc2]; linarith
    have hψrc : √(2 * (α / l₁) - rc ^ 2) = rc := by rw [hrc2, hrcs]; ring_nf
    have hLrc : rc ^ 2 / (2 * (α / l₁) - rc ^ 2) = 1 := by
      rw [hrc2, div_eq_one_iff_eq (by linarith)]; ring
    have h1 : ∀ᶠ a in 𝓝 rc, √(2 * (α / l₁) - a ^ 2) < rb :=
      hψc.eventually (gt_mem_nhds (by show √(2 * (α / l₁) - rc ^ 2) < rb; rw [hψrc]; exact hrb))
    have h2 : ∀ᶠ a in 𝓝 rc, t < a ^ 2 / (2 * (α / l₁) - a ^ 2) :=
      hLc.eventually (lt_mem_nhds (by
        show t < rc ^ 2 / (2 * (α / l₁) - rc ^ 2); rw [hLrc]; exact ht))
    have h3 : ∀ᶠ a in 𝓝 rc, 0 < a := eventually_gt_nhds hrc
    have hev : ∀ᶠ a in 𝓝[<] rc, 0 < a ∧ a < rc ∧ √(2 * (α / l₁) - a ^ 2) < rb ∧
        t < a ^ 2 / (2 * (α / l₁) - a ^ 2) := by
      filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, nhdsWithin_le_nhds h3,
        self_mem_nhdsWithin] with a h1a h2a h3a h4a
      exact ⟨h3a, h4a, h1a, h2a⟩
    obtain ⟨a, h3a, h4a, h1a, h2a⟩ := hev.exists
    exact ⟨a, h3a, h4a, h1a.le, h2a⟩
  rw [tendsto_order]
  constructor
  · -- lower bound
    intro l hl2
    obtain ⟨a, ha, har, hψ, hLa⟩ := hcut (l - 1) (by linarith)
    have hε := tendsto_guardEps (rb := rb) hl ha har hρ
    have hlim : Tendsto (fun D => 1 + a ^ 2 / (2 * (α / l₁) - a ^ 2) /
        (1 + guardEps α l₁ a rb D)) (𝓝[>] 0)
        (𝓝 (1 + a ^ 2 / (2 * (α / l₁) - a ^ 2) / (1 + 0))) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div (tendsto_const_nhds.add hε) (by norm_num))
    rw [add_zero, div_one] at hlim
    have hev := hlim.eventually
      (lt_mem_nhds (by linarith : l < 1 + a ^ 2 / (2 * (α / l₁) - a ^ 2)))
    filter_upwards [hev, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_lt_nhds (by positivity : (0 : ℝ) < a ^ 2)),
      hε.eventually (lt_mem_nhds (by norm_num : (-1 : ℝ) < 0))] with D h1 hD hDa hε1
    obtain ⟨hA, -, hlow⟩ := guard_ratio_bounds hα hl ha har hψ hD hDa.le
    rw [hratio D hD, ← hrcs] at *
    have hA' : 0 < ∫ y in (0 : ℝ)..rc, guardIntegrand α l₁ D y := hA
    rw [add_div, div_self hA'.ne']
    have h1ε : 0 < 1 + guardEps α l₁ a rb D := by linarith
    have : a ^ 2 / (2 * (α / l₁) - a ^ 2) / (1 + guardEps α l₁ a rb D) ≤
        (∫ y in rc..rb, guardIntegrand α l₁ D y) / ∫ y in (0 : ℝ)..rc, guardIntegrand α l₁ D y := by
      rw [div_le_div_iff₀ h1ε hA']
      linarith
    linarith
  · -- upper bound
    intro u hu
    obtain ⟨a, ha, har, hψ, -⟩ := hcut 0 one_pos
    have hκ := tendsto_guardKappa (α := α) hl ha (by
      have := pow_lt_pow_left₀ har ha.le two_ne_zero; rw [hrc2] at this; linarith)
    have hε := tendsto_guardEps (rb := rb) hl ha har hρ
    have hlim : Tendsto (fun D => 2 + guardKappa α l₁ a D + guardEps α l₁ a rb D) (𝓝[>] 0)
        (𝓝 (2 + 0 + 0)) := (tendsto_const_nhds.add hκ).add hε
    rw [add_zero, add_zero] at hlim
    have hev := hlim.eventually (gt_mem_nhds hu)
    filter_upwards [hev, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_lt_nhds (by positivity : (0 : ℝ) < a ^ 2))]
      with D h1 hD hDa
    obtain ⟨hA, hup, -⟩ := guard_ratio_bounds hα hl ha har hψ hD hDa.le
    rw [hratio D hD]
    have hA' : 0 < ∫ y in (0 : ℝ)..rc, guardIntegrand α l₁ D y := hA
    have hup' : ∫ y in rc..rb, guardIntegrand α l₁ D y ≤
        (1 + guardKappa α l₁ a D + guardEps α l₁ a rb D) *
          ∫ y in (0 : ℝ)..rc, guardIntegrand α l₁ D y := hup
    rw [div_lt_iff₀ hA']
    nlinarith [mul_lt_mul_of_pos_right h1 hA']

/-- The limit of `T_guard / T_committed` is `1/2`: the guard (first-arrival) time underestimates the
committed escape time by a factor of two. -/
@[powerlib_foundation] theorem tendsto_guardMFPT_ratio_inv (hα : 0 < α) (hl : 0 < l₁) {rb : ℝ}
    (hrb : guardRadius α l₁ < rb) :
    Tendsto (fun D => guardMFPT α l₁ D (guardRadius α l₁) / guardMFPT α l₁ D rb)
      (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have h := (tendsto_guardMFPT_ratio hα hl hrb).inv₀ (by norm_num)
  rw [one_div]
  refine h.congr fun D => ?_
  simp only [inv_div]

/-- **`T_committed / T_guard → 2` along `X = ΔU/D̃ → ∞`**: the same limit with the noise intensity
written as `D̃ = ΔU/X`, `ΔU = α²/(4 l₁)` (`barrierHeight`). -/
@[powerlib_foundation] theorem tendsto_guardMFPT_ratio_atTop (hα : 0 < α) (hl : 0 < l₁) {rb : ℝ}
    (hrb : guardRadius α l₁ < rb) :
    Tendsto (fun X => guardMFPT α l₁ (barrierHeight α l₁ / X) rb /
        guardMFPT α l₁ (barrierHeight α l₁ / X) (guardRadius α l₁)) atTop (𝓝 2) := by
  have hΔ : 0 < barrierHeight α l₁ := by unfold barrierHeight; positivity
  have hD : Tendsto (fun X : ℝ => barrierHeight α l₁ / X) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.div_atTop tendsto_id, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with X hX
    exact div_pos hΔ hX
  exact (tendsto_guardMFPT_ratio hα hl hrb).comp hD

end Ratio

end powerlib.Asymptotics
