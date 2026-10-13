import theorem.Asymptotics.GuardPotential
import theorem.Asymptotics.LaplaceMethod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Guard versus committed escape: `T_committed / T_guard → 2`, rate and `T_guard ~ P e^X`

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
* Rate of the ratio (source §1.2, "趋近 2 的方式本身是 `1 + O(X^{−1/2})`"):
  `guardMFPT_ratio_sub_two_isBigO`: `T(r_b)/T(r_c) − 2 = O(√D̃)` as `D̃ → 0⁺`;
  `guardMFPT_ratio_isBigO_atTop`: `T(r_b)/T(r_c) = 2(1 + O(X^{−1/2}))` along `X = ΔU/D̃ → ∞`.
  Deterministic form: `guard_ratio_rate_bounds` (`(1 − δ) A ≤ (1 + ε) B`) and
  `guardMFPT_ratio_sub_two_le` (`|T(r_b)/T(r_c) − 2| ≤ δ + κ + ε`), with the explicit half-order
  term `δ = (8e/a)(1 + κ)√(D̃/α)` (`guardDelta`) and `κ, ε = o(D̃)` (`tendsto_guardKappa_div`,
  `tendsto_guardEps_div`). Route: no Laplace expansion of either half is needed. On the
  reflected part the Jacobian `y/ψ(y)²` differs from `y⁻¹` by at most `4(r_c − y)/(a r_c)`
  (`guard_beyond_lower`), and the first moment `∫_a^{r_c} (r_c − y) e^{U/D̃}` is at most
  `2e r_c √(D̃/α)` times the weight integral `∫_a^{r_c} y⁻¹ e^{U/D̃}`
  (`guard_firstMoment_le_weight`, from the two-sided quadratic bounds
  `ΔU − α(r_c − y)² ≤ U(y) ≤ ΔU − (α/4)(r_c − y)²`, `barrier_sub_sq_le_guardPotential`,
  `guardPotential_le_barrier_sub_sq`). The inner integral `K` enters only through
  `K(a) ≤ K(y) ≤ K(ψ(a)) ≤ (1 + κ) K(a)`, so no separate expansion of `K` is needed. The rate is
  an upper bound; that the `X^{−1/2}` term is generically present is the endpoint-table statement
  `endpointCorrection_ne_zero_iff` (`Asymptotics/EndpointLaplace.lean`), not a statement proved
  here for this integral.
* Single-term asymptotics (source §1.3, and the `× 2` of §1.5), with
  `P = guardPrefactor α l₁ D̃ = (√π/2) √(D̃ l₁)/α²` and `X = ΔU/D̃`:
  `guardMFPT_guard_isBigO`: `T_guard/(P e^X) − 1 = O(√D̃)` as `D̃ → 0⁺`;
  `guardMFPT_guard_isBigO_atTop`: `T_guard = P e^X (1 + O(X^{−1/2}))`;
  `tendsto_guardMFPT_guard`: `T_guard/(P e^X) → 1`;
  `guardMFPT_committed_isBigO`, `guardMFPT_committed_isBigO_atTop`:
  `T_committed = 2 P e^X (1 + O(X^{−1/2}))` for every `r_b > r_c`.
  Explicit two-sided bounds at a cut `0 < a < r_c` (`guardMFPT_guard_ge`, `guardMFPT_guard_le`):
  `(1 − e^{−αa²/(2D̃)})(1 − √(D̃/α)/(√π(r_c − a))) P e^X ≤ T_guard ≤
  (1 + ε)(1 + 16 l₁D̃/α²)(1 + 17√(D̃/α)/(√π a)) P e^X` (`D̃ ≤ a²` for the upper bound).
  Route, following the source's assembly "阱 · 垒 · 1/D̃": the inner integral is a Gaussian mass,
  `(D̃/α)(1 − e^{−αa²/(2D̃)}) ≤ K(a) ≤ K(r_c) ≤ (D̃/α)(1 + 16 l₁D̃/α²)` (`guardInner_ge_gauss`,
  `guardInner_le_gauss`; relative error `O(1/X)`), and the weight integral is an endpoint Gaussian,
  `r_c⁻¹ e^X √(πD̃/α)/2 · (1 + O(√D̃))` (`guard_weight_ge_gauss`, `guard_weight_le_gauss`; relative
  error `O(X^{−1/2})`, the endpoint half order), from
  `ΔU − α(r_c − y)² ≤ U(y)` and `e^{−s} ≤ e^{−cξ²} + (l₁ r_c ξ³/D̃) e^{−cξ²/4}` in `ξ = r_c − y`;
  the generic Laplace theorems `laplace_endpoint_rate` are not used because the integral is over a
  finite interval with a non-global quadratic phase. Generic Gaussian facts: `gaussMoment1`,
  `gaussMoment3`, `gaussMoment5` (`∫_0^∞ ξⁿ e^{−cξ²}`, `n = 1, 3, 5`), `integral_exp_neg_mul_sq_ge`
  (`∫_0^L e^{−cξ²} ≥ √(π/c)/2 − 1/(2cL)`), `intervalIntegral_le_integral_Ioi`.
  The rates are upper bounds; that the `X^{−1/2}` term is present for this barrier is the
  truncated-table statement `endpointCorrection_ne_zero_iff`, not proved here for the integral.
* Supporting facts: `U(z) = ΔU − (l₁/4)(z² − r_c²)²` (`guardPotential_eq_barrier_sub`),
  monotonicity / integrability / two-sided bounds of the inner integral `K` (`guardInner_*`) and
  of the outer integrand (`guardIntegrand_*`).

Source: work-sync theory/T-endpoint-laplace-asymptotics.md §1.2 ("逃逸时间的两种边界，比值恰为 2",
`T_committed / T_guard → 2` and "趋近 2 的方式本身是 `1 + O(X^{−1/2})`"), §1.3 (the potential
`U = αr²/2 − l₁r⁴/4` and `T_guard ∼ (√π/2) √(D̃ l₁)/α² e^X (1 + O(X^{−1/2}))`), §1.5 (`× 2` for
committed escape).
-/

noncomputable section
namespace powerlib.Asymptotics

open Real Set Filter Topology MeasureTheory intervalIntegral

/-! ## Half-line Gaussian moments and a finite-interval Gaussian bound

Generic one-variable facts in the form `∫_0^∞ ξⁿ e^{−cξ²}` used for `T_guard ~ P e^X`. -/

/-- `∫_0^∞ ξ e^{−cξ²} dξ = 1/(2c)` (`halfMoment1` with `b = 2c`). -/
@[powerlib_foundation] theorem gaussMoment1 {c : ℝ} (hc : 0 < c) :
    ∫ ξ in Ioi (0 : ℝ), ξ * Real.exp (-c * ξ ^ 2) = 1 / (2 * c) := by
  have h := halfMoment1 (b := 2 * c) (by positivity)
  rw [show 2 * c / 2 = c by ring] at h
  rw [← h]

/-- `∫_0^∞ ξ³ e^{−cξ²} dξ = 1/(2c²)` (`halfMoment3` with `b = 2c`). -/
@[powerlib_foundation] theorem gaussMoment3 {c : ℝ} (hc : 0 < c) :
    ∫ ξ in Ioi (0 : ℝ), ξ ^ 3 * Real.exp (-c * ξ ^ 2) = 1 / (2 * c ^ 2) := by
  have h := halfMoment3 (b := 2 * c) (by positivity)
  rw [show 2 * c / 2 = c by ring] at h
  have e : (2 : ℝ) / (2 * c) ^ 2 = 1 / (2 * c ^ 2) := by field_simp
  rw [← e, ← h]

/-- `∫_0^∞ ξ⁵ e^{−cξ²} dξ = 1/c³` (wraps `integral_rpow_mul_exp_neg_mul_rpow`, `Γ(3) = 2`). -/
@[powerlib_foundation] theorem gaussMoment5 {c : ℝ} (hc : 0 < c) :
    ∫ ξ in Ioi (0 : ℝ), ξ ^ 5 * Real.exp (-c * ξ ^ 2) = 1 / c ^ 3 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 5) (b := c)
    two_pos (by norm_num) hc
  have h5 : ∀ ξ : ℝ, ξ ^ (5 : ℝ) = ξ ^ (5 : ℕ) := fun ξ => by
    exact_mod_cast Real.rpow_natCast ξ 5
  simp only [h5, Real.rpow_two] at h
  rw [h]
  have hG : Real.Gamma ((5 + 1) / 2) = 2 := by
    rw [show ((5 : ℝ) + 1) / 2 = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num
  rw [hG, show -((5 : ℝ) + 1) / 2 = -(3 : ℕ) by norm_num, Real.rpow_neg hc.le,
    Real.rpow_natCast]
  field_simp

/-- A finite integral of a function that is nonnegative and integrable on `(0, ∞)` is at most the
half-line integral. -/
@[powerlib_foundation] theorem intervalIntegral_le_integral_Ioi {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : IntegrableOn f (Ioi 0)) (h0 : ∀ x, 0 < x → 0 ≤ f x) :
    ∫ x in (0 : ℝ)..L, f x ≤ ∫ x in Ioi (0 : ℝ), f x := by
  rw [intervalIntegral.integral_of_le hL]
  apply setIntegral_mono_set hf
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using h0 x hx
  · exact Ioc_subset_Ioi_self.eventuallyLE

/-- Gaussian lower bound on a finite interval:
`∫_0^L e^{−cξ²} dξ ≥ √(π/c)/2 − 1/(2cL)` (the tail beyond `L` is at most `(1/L) ∫ ξ e^{−cξ²}`). -/
@[powerlib_foundation] theorem integral_exp_neg_mul_sq_ge {c L : ℝ} (hc : 0 < c) (hL : 0 < L) :
    √(π / c) / 2 - 1 / (2 * c * L) ≤ ∫ ξ in (0 : ℝ)..L, Real.exp (-c * ξ ^ 2) := by
  have hg : Integrable fun ξ : ℝ => Real.exp (-c * ξ ^ 2) := integrable_exp_neg_mul_sq hc
  have hg1 : Integrable fun ξ : ℝ => ξ * Real.exp (-c * ξ ^ 2) := integrable_mul_exp_neg_mul_sq hc
  have hsplit : ∫ ξ in Ioi (0 : ℝ), Real.exp (-c * ξ ^ 2) =
      (∫ ξ in Ioc (0 : ℝ) L, Real.exp (-c * ξ ^ 2)) + ∫ ξ in Ioi L, Real.exp (-c * ξ ^ 2) := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hg.integrableOn
      hg.integrableOn, Ioc_union_Ioi_eq_Ioi hL.le]
  have htail : ∫ ξ in Ioi L, Real.exp (-c * ξ ^ 2) ≤ 1 / (2 * c * L) := by
    calc ∫ ξ in Ioi L, Real.exp (-c * ξ ^ 2)
        ≤ ∫ ξ in Ioi L, L⁻¹ * (ξ * Real.exp (-c * ξ ^ 2)) := by
          apply setIntegral_mono_on hg.integrableOn (hg1.const_mul _).integrableOn
            measurableSet_Ioi
          intro ξ hξ
          have hξ' : L < ξ := hξ
          rw [← mul_assoc]
          apply le_mul_of_one_le_left (Real.exp_pos _).le
          rw [inv_mul_eq_div, one_le_div hL]; exact hξ'.le
      _ ≤ ∫ ξ in Ioi (0 : ℝ), L⁻¹ * (ξ * Real.exp (-c * ξ ^ 2)) := by
          apply setIntegral_mono_set (hg1.const_mul _).integrableOn
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
            have : (0 : ℝ) < ξ := hξ
            positivity
          · exact (Ioi_subset_Ioi hL.le).eventuallyLE
      _ = 1 / (2 * c * L) := by
          rw [MeasureTheory.integral_const_mul, gaussMoment1 hc]; field_simp
  have hmain := integral_gaussian_Ioi c
  rw [intervalIntegral.integral_of_le hL.le]
  linarith


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

/-- Near the top from above: `U(y) ≤ ΔU − (α/4)(r_c − y)²` for every `y ≥ 0`. -/
@[powerlib_foundation] theorem guardPotential_le_barrier_sub_sq (hα : 0 < α) (hl : 0 < l₁)
    {y : ℝ} (hy : 0 ≤ y) :
    guardPotential α l₁ y ≤ barrierHeight α l₁ - α / 4 * (√(α / l₁) - y) ^ 2 := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  rw [guardPotential_eq_barrier_sub hl]
  obtain ⟨r, hr, hr2⟩ : ∃ r, r = √(α / l₁) ∧ r ^ 2 = α / l₁ := ⟨_, rfl, Real.sq_sqrt hρ.le⟩
  rw [← hr, ← hr2]
  have hαe : α = l₁ * r ^ 2 := by rw [hr2]; field_simp
  have hr0 : 0 ≤ r := hr ▸ Real.sqrt_nonneg _
  have key : (y ^ 2 - r ^ 2) ^ 2 - r ^ 2 * (r - y) ^ 2 = (r - y) ^ 2 * (y * (2 * r + y)) := by
    ring
  have : 0 ≤ (r - y) ^ 2 * (y * (2 * r + y)) := by positivity
  have h4 : 0 ≤ l₁ / 4 := by positivity
  have : α / 4 * (r - y) ^ 2 ≤ l₁ / 4 * (y ^ 2 - r ^ 2) ^ 2 := by
    rw [hαe]; nlinarith [mul_nonneg h4 this]
  linarith

/-- Near the top from below: `U(y) ≥ ΔU − α(r_c − y)²` for `0 ≤ y ≤ r_c`. -/
@[powerlib_foundation] theorem barrier_sub_sq_le_guardPotential (hα : 0 < α) (hl : 0 < l₁)
    {y : ℝ} (hy : 0 ≤ y) (hyr : y ≤ √(α / l₁)) :
    barrierHeight α l₁ - α * (√(α / l₁) - y) ^ 2 ≤ guardPotential α l₁ y := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  rw [guardPotential_eq_barrier_sub hl]
  obtain ⟨r, hr, hr2⟩ : ∃ r, r = √(α / l₁) ∧ r ^ 2 = α / l₁ := ⟨_, rfl, Real.sq_sqrt hρ.le⟩
  rw [← hr] at hyr ⊢
  rw [← hr2]
  have hαe : α = l₁ * r ^ 2 := by rw [hr2]; field_simp
  have key : 4 * r ^ 2 * (r - y) ^ 2 - (y ^ 2 - r ^ 2) ^ 2 =
      (r - y) ^ 2 * ((r - y) * (3 * r + y)) := by ring
  have hr0 : 0 ≤ r := hr ▸ Real.sqrt_nonneg _
  have : 0 ≤ (r - y) ^ 2 * ((r - y) * (3 * r + y)) := by
    have : 0 ≤ r - y := by linarith
    exact mul_nonneg (sq_nonneg _) (mul_nonneg this (by linarith))
  have h4 : 0 ≤ l₁ / 4 := by positivity
  have : l₁ / 4 * (y ^ 2 - r ^ 2) ^ 2 ≤ α * (r - y) ^ 2 := by
    rw [hαe]; nlinarith [mul_nonneg h4 this]
  linarith

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

/-! ### The barrier weight near the top -/

/-- First moment of the barrier weight about the top:
`∫_a^{r_c} (r_c − y) e^{U(y)/D̃} dy ≤ (2D̃/α) e^{ΔU/D̃}`. -/
@[powerlib_foundation] theorem guard_firstMoment_le (hα : 0 < α) (hl : 0 < l₁) {a : ℝ}
    (hD : 0 < D) (ha : 0 ≤ a)
    (har : a ≤ √(α / l₁)) :
    ∫ y in a..√(α / l₁), (√(α / l₁) - y) * Real.exp (guardPotential α l₁ y / D) ≤
      2 * D / α * Real.exp (barrierHeight α l₁ / D) := by
  set rc := √(α / l₁) with hrc
  set g : ℝ → ℝ := fun y => Real.exp (-(α * (rc - y) ^ 2 / (4 * D))) with hg
  have hderiv : ∀ y ∈ uIcc a rc, HasDerivAt (fun y => 2 * D / α * g y)
      ((rc - y) * g y) y := by
    intro y _
    have h1 : HasDerivAt (fun y => -(α * (rc - y) ^ 2 / (4 * D)))
        (α * (rc - y) / (2 * D)) y := by
      have h0 : HasDerivAt (fun y => rc - y) (-1) y := by
        simpa using (hasDerivAt_id y).const_sub rc
      have := (((h0.pow 2).const_mul α).div_const (4 * D)).neg
      convert this using 1
      · simp; field_simp; ring
    have := (h1.exp).const_mul (2 * D / α)
    convert this using 1
    simp only [hg]; field_simp
  have hcont : Continuous fun y => (rc - y) * g y := by simp only [hg]; fun_prop
  have hFTC := integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)
  have hga : 0 ≤ g a := (Real.exp_pos _).le
  have hgr : g rc = 1 := by simp [hg]
  calc ∫ y in a..rc, (rc - y) * Real.exp (guardPotential α l₁ y / D)
      ≤ ∫ y in a..rc, Real.exp (barrierHeight α l₁ / D) * ((rc - y) * g y) := by
        apply integral_mono_on har
        · exact (by unfold guardPotential; fun_prop : Continuous fun y =>
            (rc - y) * Real.exp (guardPotential α l₁ y / D)).intervalIntegrable _ _
        · exact (hcont.const_mul _).intervalIntegrable _ _
        intro y hy
        have hy0 : 0 ≤ rc - y := by linarith [hy.2]
        rw [mul_left_comm]
        apply mul_le_mul_of_nonneg_left _ hy0
        simp only [hg]
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have := guardPotential_le_barrier_sub_sq hα hl (ha.trans hy.1)
        rw [div_le_iff₀ hD]
        have e : (barrierHeight α l₁ / D + -(α * (rc - y) ^ 2 / (4 * D))) * D =
            barrierHeight α l₁ - α / 4 * (rc - y) ^ 2 := by field_simp; ring
        rw [e]; exact this
    _ = Real.exp (barrierHeight α l₁ / D) * (2 * D / α * g rc - 2 * D / α * g a) := by
        rw [intervalIntegral.integral_const_mul, hFTC]
    _ ≤ 2 * D / α * Real.exp (barrierHeight α l₁ / D) := by
        rw [hgr]
        have : 0 ≤ 2 * D / α * g a := by positivity
        have he := Real.exp_pos (barrierHeight α l₁ / D)
        nlinarith

/-- Window lower bound for the weight integral: if `s = √(D̃/α) ≤ r_c − a` then
`∫_a^{r_c} y⁻¹ e^{U(y)/D̃} dy ≥ (s/r_c) e^{ΔU/D̃ − 1}`. -/
@[powerlib_foundation] theorem guard_weight_ge_window (hα : 0 < α) (hl : 0 < l₁) {a : ℝ}
    (hD : 0 < D) (ha : 0 < a)
    (hwin : √(D / α) ≤ √(α / l₁) - a) :
    √(D / α) / √(α / l₁) * Real.exp (barrierHeight α l₁ / D - 1) ≤
      ∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D) := by
  set rc := √(α / l₁) with hrc
  set s := √(D / α) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = D / α := Real.sq_sqrt (div_pos hD hα).le
  have hm : a ≤ rc - s := by linarith
  have hm0 : 0 < rc - s := ha.trans_le hm
  have hrc0 : 0 < rc := by linarith
  have hw : ∀ {p q : ℝ}, 0 < p → p ≤ q →
      IntervalIntegrable (fun y => y⁻¹ * Real.exp (guardPotential α l₁ y / D)) volume p q := by
    intro p q hp hpq
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hpq]
    apply ContinuousOn.mul _ (continuous_exp_guardPotential α l₁ D).continuousOn
    exact continuousOn_inv₀.mono fun y hy => (ne_of_gt (hp.trans_le hy.1) : y ≠ 0)
  calc s / rc * Real.exp (barrierHeight α l₁ / D - 1) =
        ∫ y in (rc - s)..rc, rc⁻¹ * Real.exp (barrierHeight α l₁ / D - 1) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; field_simp; ring
    _ ≤ ∫ y in (rc - s)..rc, y⁻¹ * Real.exp (guardPotential α l₁ y / D) := by
        apply integral_mono_on (by linarith) intervalIntegrable_const (hw hm0 (by linarith))
        intro y hy
        have hy0 : 0 < y := hm0.trans_le hy.1
        apply mul_le_mul (inv_anti₀ hy0 hy.2) _ (Real.exp_pos _).le (inv_nonneg.2 hy0.le)
        apply Real.exp_le_exp.mpr
        have hU := barrier_sub_sq_le_guardPotential hα hl hy0.le hy.2
        have hsq : α * (rc - y) ^ 2 ≤ D := by
          have h1 : (rc - y) ^ 2 ≤ s ^ 2 := by
            apply pow_le_pow_left₀ (by linarith [hy.2]) (by linarith [hy.1])
          rw [hs2] at h1
          have := mul_le_mul_of_nonneg_left h1 hα.le
          rwa [mul_div_cancel₀ _ hα.ne'] at this
        rw [← hrc] at hU
        have h2 : barrierHeight α l₁ - D ≤ guardPotential α l₁ y := by linarith
        rw [show barrierHeight α l₁ / D - 1 = (barrierHeight α l₁ - D) / D by field_simp]
        exact div_le_div_of_nonneg_right h2 hD.le
    _ ≤ ∫ y in a..rc, y⁻¹ * Real.exp (guardPotential α l₁ y / D) := by
        apply integral_mono_interval hm (by linarith) le_rfl
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
          exact mul_nonneg (inv_nonneg.2 (ha.trans hy.1).le) (Real.exp_pos _).le
        · exact hw ha (by linarith)

/-- `J ≤ 2e r_c √(D̃/α) · I`: the first moment about the top is `O(√D̃)` relative to the
weight integral. -/
@[powerlib_foundation] theorem guard_firstMoment_le_weight (hα : 0 < α) (hl : 0 < l₁) {a : ℝ}
    (hD : 0 < D)
    (ha : 0 < a) (hwin : √(D / α) ≤ √(α / l₁) - a) :
    ∫ y in a..√(α / l₁), (√(α / l₁) - y) * Real.exp (guardPotential α l₁ y / D) ≤
      2 * Real.exp 1 * √(α / l₁) * √(D / α) *
        ∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D) := by
  have hrc0 : 0 < √(α / l₁) := Real.sqrt_pos.mpr (div_pos hα hl)
  have hs2 : √(D / α) ^ 2 = D / α := Real.sq_sqrt (div_pos hD hα).le
  have hJ := guard_firstMoment_le hα hl hD ha.le (by linarith [Real.sqrt_nonneg (D / α)])
  have hI := guard_weight_ge_window hα hl hD ha hwin
  refine hJ.trans ?_
  have hc : 0 ≤ 2 * Real.exp 1 * √(α / l₁) * √(D / α) := by positivity
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hI hc)
  rw [Real.exp_sub]
  have he := Real.exp_pos 1
  have e : 2 * Real.exp 1 * √(α / l₁) * √(D / α) *
      (√(D / α) / √(α / l₁) * (Real.exp (barrierHeight α l₁ / D) / Real.exp 1)) =
      2 * √(D / α) ^ 2 * Real.exp (barrierHeight α l₁ / D) := by
    field_simp
  rw [e, hs2]
  apply le_of_eq; ring

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

/-- Relative half-order term of the ratio rate, `δ = (8e/a)(1 + κ) √(D̃/α)`
(`guard_ratio_rate_bounds`). -/
def guardDelta (α l₁ a D : ℝ) : ℝ :=
  8 * Real.exp 1 / a * (1 + guardKappa α l₁ a D) * √(D / α)

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

/-- `y⁻¹ − 4(r − y)/(a r) ≤ y/(2r² − y²)` for `0 < a ≤ y ≤ r`: the reflection Jacobian
`y/ψ(y)²` differs from `y⁻¹` by `O(r − y)`. -/
@[powerlib_foundation] private theorem reflect_weight_ge {a y r : ℝ} (ha : 0 < a) (hay : a ≤ y)
    (hyr : y ≤ r) :
    y⁻¹ - 4 * (r - y) / (a * r) ≤ y / (2 * r ^ 2 - y ^ 2) := by
  have hy : 0 < y := ha.trans_le hay
  have hr : 0 < r := hy.trans_le hyr
  have hy2 : y ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hy.le hyr 2
  have hpos : 0 < 2 * r ^ 2 - y ^ 2 := by nlinarith
  have e : y / (2 * r ^ 2 - y ^ 2) - (y⁻¹ - 4 * (r - y) / (a * r)) =
      (r - y) * (4 * y * (2 * r ^ 2 - y ^ 2) - 2 * a * r * (r + y)) /
        (y * (2 * r ^ 2 - y ^ 2) * (a * r)) := by
    field_simp; ring
  have hnum : 0 ≤ 4 * y * (2 * r ^ 2 - y ^ 2) - 2 * a * r * (r + y) := by
    have h1 : a * r * (r + y) ≤ y * r * (r + y) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hay hr.le) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hyr hy.le, mul_le_mul_of_nonneg_left hyr hr.le]
  have : 0 ≤ (r - y) * (4 * y * (2 * r ^ 2 - y ^ 2) - 2 * a * r * (r + y)) /
      (y * (2 * r ^ 2 - y ^ 2) * (a * r)) :=
    div_nonneg (mul_nonneg (by linarith) hnum) (by positivity)
  linarith

/-- The new lower estimate for the part just beyond the top:
`∫_a^{r_c} h − (4/(a r_c)) K(r_c) J ≤ ∫_{r_c}^{ψ(a)} h`, `J = ∫_a^{r_c} (r_c − y) e^{U/D̃}`. -/
@[powerlib_foundation] private theorem guard_beyond_lower (hl : 0 < l₁) {a : ℝ} (ha : 0 < a)
    (har : a ≤ √(α / l₁)) (hρ : 0 < α / l₁) :
    (∫ y in a..√(α / l₁), guardIntegrand α l₁ D y) -
        4 / (a * √(α / l₁)) * guardInner α l₁ D √(α / l₁) *
          ∫ y in a..√(α / l₁), (√(α / l₁) - y) * Real.exp (guardPotential α l₁ y / D) ≤
      ∫ y in √(α / l₁)..√(2 * (α / l₁) - a ^ 2), guardIntegrand α l₁ D y := by
  have hrc2 : √(α / l₁) ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  have hrc : 0 < √(α / l₁) := Real.sqrt_pos.mpr hρ
  have hri := intervalIntegrable_guardIntegrand_reflect (α := α) (l₁ := l₁) (D := D) ha har
    (by rw [hrc2]; linarith)
  have hh : IntervalIntegrable (guardIntegrand α l₁ D) volume a √(α / l₁) :=
    intervalIntegrable_guardIntegrand_of_pos ha hrc
  have hJ : IntervalIntegrable (fun y => (√(α / l₁) - y) *
      Real.exp (guardPotential α l₁ y / D)) volume a √(α / l₁) :=
    (by unfold guardPotential; fun_prop : Continuous fun y =>
      (√(α / l₁) - y) * Real.exp (guardPotential α l₁ y / D)).intervalIntegrable _ _
  rw [integral_guardIntegrand_reflect ha har hρ, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub hh (hJ.const_mul _)]
  apply integral_mono_on har (hh.sub (hJ.const_mul _)) hri
  intro y hy
  have hy0 : 0 < y := ha.trans_le hy.1
  have hy2 : y ^ 2 ≤ α / l₁ := by
    have := pow_le_pow_left₀ hy0.le hy.2 2; rwa [hrc2] at this
  rw [guardIntegrand_reflect_eq hl (by linarith)]
  have hK0 : 0 ≤ guardInner α l₁ D y := guardInner_nonneg hy0.le
  have hKr : guardInner α l₁ D y ≤ guardInner α l₁ D √(α / l₁) := guardInner_mono hy0.le hy.2
  have hKψ : guardInner α l₁ D y ≤ guardInner α l₁ D √(2 * (α / l₁) - y ^ 2) := by
    apply guardInner_mono hy0.le
    rw [show y = √(y ^ 2) from (Real.sqrt_sq hy0.le).symm, Real.sqrt_sq hy0.le]
    exact Real.le_sqrt_of_sq_le (by linarith)
  have hw := reflect_weight_ge ha hy.1 hy.2
  rw [hrc2] at hw
  have hE := Real.exp_pos (guardPotential α l₁ y / D)
  have hq0 : 0 ≤ y / (2 * (α / l₁) - y ^ 2) := div_nonneg hy0.le (by linarith)
  have hc0 : 0 ≤ 4 * (√(α / l₁) - y) / (a * √(α / l₁)) :=
    div_nonneg (by linarith [hy.2]) (by positivity)
  simp only [guardIntegrand]
  calc y⁻¹ * Real.exp (guardPotential α l₁ y / D) * guardInner α l₁ D y -
        4 / (a * √(α / l₁)) * guardInner α l₁ D √(α / l₁) *
          ((√(α / l₁) - y) * Real.exp (guardPotential α l₁ y / D))
      = Real.exp (guardPotential α l₁ y / D) * (y⁻¹ * guardInner α l₁ D y -
          4 * (√(α / l₁) - y) / (a * √(α / l₁)) * guardInner α l₁ D √(α / l₁)) := by ring
    _ ≤ Real.exp (guardPotential α l₁ y / D) * ((y⁻¹ -
          4 * (√(α / l₁) - y) / (a * √(α / l₁))) * guardInner α l₁ D y) := by
        apply mul_le_mul_of_nonneg_left _ hE.le
        nlinarith [mul_le_mul_of_nonneg_left hKr hc0]
    _ ≤ Real.exp (guardPotential α l₁ y / D) * (y / (2 * (α / l₁) - y ^ 2) *
          guardInner α l₁ D √(2 * (α / l₁) - y ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hE.le
        calc (y⁻¹ - 4 * (√(α / l₁) - y) / (a * √(α / l₁))) * guardInner α l₁ D y
            ≤ y / (2 * (α / l₁) - y ^ 2) * guardInner α l₁ D y :=
              mul_le_mul_of_nonneg_right hw hK0
          _ ≤ y / (2 * (α / l₁) - y ^ 2) * guardInner α l₁ D √(2 * (α / l₁) - y ^ 2) :=
              mul_le_mul_of_nonneg_left hKψ hq0
    _ = y / (2 * (α / l₁) - y ^ 2) * Real.exp (guardPotential α l₁ y / D) *
          guardInner α l₁ D √(2 * (α / l₁) - y ^ 2) := by ring

/-- The two tails are exponentially small against the main part: with
`I = ∫_a^{r_c} y⁻¹ e^{U/D̃}`, `∫₀^a h + ∫_{ψ(a)}^{r_b} h ≤ ε K(a) I`. -/
@[powerlib_foundation] private theorem guard_tails_le (hα : 0 < α) (hl : 0 < l₁) {a rb : ℝ}
    (ha : 0 < a) (har : a < √(α / l₁)) (hψ : √(2 * (α / l₁) - a ^ 2) ≤ rb) (hD : 0 < D)
    (hDa : D ≤ a ^ 2) :
    (∫ y in (0 : ℝ)..a, guardIntegrand α l₁ D y) +
        ∫ y in √(2 * (α / l₁) - a ^ 2)..rb, guardIntegrand α l₁ D y ≤
      guardEps α l₁ a rb D * (guardInner α l₁ D a *
        ∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D)) := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hrc : 0 < √(α / l₁) := Real.sqrt_pos.mpr hρ
  have hrc2 : √(α / l₁) ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  have ha2 : a ^ 2 < α / l₁ := by
    have := pow_lt_pow_left₀ har ha.le (two_ne_zero); rwa [hrc2] at this
  have hrcψ : √(α / l₁) ≤ √(2 * (α / l₁) - a ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have hψ0 : 0 < √(2 * (α / l₁) - a ^ 2) := hrc.trans_le hrcψ
  have ham : a < (a + √(α / l₁)) / 2 := by linarith
  have hmr : (a + √(α / l₁)) / 2 < √(α / l₁) := by linarith
  have hUa_le : ∀ y ∈ Icc 0 a, guardPotential α l₁ y ≤ guardPotential α l₁ a := by
    intro y hy
    apply guardPotential_le_of_sq_le hl
    have : y ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hy.1 hy.2 2
    nlinarith [sq_nonneg y]
  have hUψ_le : ∀ y ∈ Icc √(2 * (α / l₁) - a ^ 2) rb,
      guardPotential α l₁ y ≤ guardPotential α l₁ a := by
    intro y hy
    apply guardPotential_le_of_sq_le hl
    have hψa2 : √(2 * (α / l₁) - a ^ 2) ^ 2 = 2 * (α / l₁) - a ^ 2 := Real.sq_sqrt (by linarith)
    have : √(2 * (α / l₁) - a ^ 2) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hψ0.le hy.1 2
    nlinarith
  have hUm_ge : ∀ y ∈ Icc ((a + √(α / l₁)) / 2) √(α / l₁),
      guardPotential α l₁ ((a + √(α / l₁)) / 2) ≤ guardPotential α l₁ y := by
    intro y hy
    apply guardPotential_le_of_sq_le hl
    have hm0 : 0 < (a + √(α / l₁)) / 2 := by linarith
    have h1 : ((a + √(α / l₁)) / 2) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hm0.le hy.1 2
    have h2 : y ^ 2 ≤ √(α / l₁) ^ 2 := pow_le_pow_left₀ (hm0.le.trans hy.1) hy.2 2
    nlinarith
  have hKa := guardInner_ge (l₁ := l₁) hα.le hl.le hD ha.le hDa
  have hKa0 : 0 < guardInner α l₁ D a := lt_of_lt_of_le (by positivity) hKa
  have hI := guard_weight_ge (l₁ := l₁) hD ha ham.le hmr.le hUm_ge
  have hint0a : IntervalIntegrable (guardIntegrand α l₁ D) volume 0 a :=
    intervalIntegrable_guardIntegrand hl hD ha.le
  have hintψb : IntervalIntegrable (guardIntegrand α l₁ D) volume √(2 * (α / l₁) - a ^ 2) rb :=
    intervalIntegrable_guardIntegrand_of_pos hψ0 (hψ0.trans_le hψ)
  have hAt := guard_tail_le (l₁ := l₁) hl hD le_rfl ha.le hUa_le hint0a
  have hBt := guard_tail_le (l₁ := l₁) hl hD hψ0.le hψ hUψ_le hintψb
  generalize (∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D)) = I at hI ⊢
  generalize (∫ y in (0 : ℝ)..a, guardIntegrand α l₁ D y) = At at hAt ⊢
  generalize (∫ y in √(2 * (α / l₁) - a ^ 2)..rb, guardIntegrand α l₁ D y) = Bt at hBt ⊢
  have hrm : 0 < √(α / l₁) - (a + √(α / l₁)) / 2 := by linarith
  have hQ : D / 2 * Real.exp (-(α / 2)) * ((√(α / l₁) - (a + √(α / l₁)) / 2) / √(α / l₁) *
      Real.exp (guardPotential α l₁ ((a + √(α / l₁)) / 2) / D)) ≤ guardInner α l₁ D a * I :=
    mul_le_mul hKa hI (by positivity) hKa0.le
  have hP0 : 0 ≤ (a ^ 2 / 2 + (rb - √(2 * (α / l₁) - a ^ 2)) * (rb / 2)) *
      (Real.exp (guardPotential α l₁ a / D) + 1) := by
    have : 0 ≤ rb - √(2 * (α / l₁) - a ^ 2) := by linarith
    have : 0 ≤ rb := by linarith
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

/-- `K(ψ(a)) ≤ (1 + κ) K(a)`: across the barrier the inner integral grows by an exponentially
small relative amount. -/
@[powerlib_foundation] private theorem guardInner_reflect_le (hα : 0 < α) (hl : 0 < l₁) {a : ℝ}
    (ha : 0 < a) (har : a < √(α / l₁)) (hD : 0 < D) (hDa : D ≤ a ^ 2) :
    guardInner α l₁ D √(2 * (α / l₁) - a ^ 2) ≤
      (1 + guardKappa α l₁ a D) * guardInner α l₁ D a := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hrc : 0 < √(α / l₁) := Real.sqrt_pos.mpr hρ
  have hrc2 : √(α / l₁) ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  have ha2 : a ^ 2 < α / l₁ := by
    have := pow_lt_pow_left₀ har ha.le (two_ne_zero); rwa [hrc2] at this
  have hψa2 : √(2 * (α / l₁) - a ^ 2) ^ 2 = 2 * (α / l₁) - a ^ 2 := Real.sq_sqrt (by linarith)
  have hrcψ : √(α / l₁) ≤ √(2 * (α / l₁) - a ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have hUa_ge : ∀ z ∈ Icc a √(2 * (α / l₁) - a ^ 2),
      guardPotential α l₁ a ≤ guardPotential α l₁ z := by
    intro z hz
    apply guardPotential_le_of_sq_le hl
    have h1 : a ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ ha.le hz.1 2
    have h2 : z ^ 2 ≤ √(2 * (α / l₁) - a ^ 2) ^ 2 := pow_le_pow_left₀ (ha.le.trans hz.1) hz.2 2
    nlinarith
  have hKa := guardInner_ge (l₁ := l₁) hα.le hl.le hD ha.le hDa
  have hKψ := guardInner_sub_le (l₁ := l₁) hD ha.le (har.le.trans hrcψ) hUa_ge
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

@[powerlib_foundation] private theorem guardKappa_nonneg (hα : 0 < α) (hl : 0 < l₁) {a : ℝ}
    (ha : 0 < a) (har : a < √(α / l₁)) (hD : 0 < D) : 0 ≤ guardKappa α l₁ a D := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hrc2 : √(α / l₁) ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  have ha2 : a ^ 2 < α / l₁ := by
    have := pow_lt_pow_left₀ har ha.le (two_ne_zero); rwa [hrc2] at this
  have hrcψ : √(α / l₁) ≤ √(2 * (α / l₁) - a ^ 2) := Real.sqrt_le_sqrt (by linarith)
  unfold guardKappa
  have : 0 ≤ √(2 * (α / l₁) - a ^ 2) - a := by linarith
  positivity

@[powerlib_foundation] private theorem guardEps_nonneg (hα : 0 < α) (hl : 0 < l₁) {a rb : ℝ}
    (ha : 0 < a) (har : a < √(α / l₁)) (hψ : √(2 * (α / l₁) - a ^ 2) ≤ rb) (hD : 0 < D) :
    0 ≤ guardEps α l₁ a rb D := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hrc : 0 < √(α / l₁) := Real.sqrt_pos.mpr hρ
  have hrm : 0 < √(α / l₁) - (a + √(α / l₁)) / 2 := by linarith
  have hb : 0 ≤ rb - √(2 * (α / l₁) - a ^ 2) := by linarith
  have hrb : 0 ≤ rb := (Real.sqrt_nonneg _).trans hψ
  unfold guardEps
  apply div_nonneg
  · exact mul_nonneg (add_nonneg (by positivity) (mul_nonneg hb (by positivity))) (by positivity)
  · exact mul_nonneg (by positivity) (mul_nonneg (div_nonneg hrm.le hrc.le) (by positivity))

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
  have hrcψ : √(α / l₁) ≤ √(2 * (α / l₁) - a ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have hψ0 : 0 < √(2 * (α / l₁) - a ^ 2) := hrc.trans_le hrcψ
  have ham : a < (a + √(α / l₁)) / 2 := by linarith
  have hmr : (a + √(α / l₁)) / 2 < √(α / l₁) := by linarith
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
  obtain ⟨hAm_lo, hAm_hi⟩ := guard_inside_bounds (α := α) (l₁ := l₁) (D := D) ha har.le
  obtain ⟨hBm_lo, hBm_hi⟩ := guard_beyond_bounds (D := D) hl ha har.le hρ
  have hI := guard_weight_ge (l₁ := l₁) hD ha ham.le hmr.le hUm_ge
  have htails := guard_tails_le hα hl ha har hψ hD hDa
  have hkap := guardInner_reflect_le hα hl ha har hD hDa
  have heps0 := guardEps_nonneg hα hl ha har hψ hD
  have hkap0 := guardKappa_nonneg hα hl ha har hD
  have hint0a : IntervalIntegrable (guardIntegrand α l₁ D) volume 0 a :=
    intervalIntegrable_guardIntegrand hl hD ha.le
  have hintar : IntervalIntegrable (guardIntegrand α l₁ D) volume a √(α / l₁) :=
    intervalIntegrable_guardIntegrand_of_pos ha hrc
  have hintrψ : IntervalIntegrable (guardIntegrand α l₁ D) volume √(α / l₁)
      √(2 * (α / l₁) - a ^ 2) := intervalIntegrable_guardIntegrand_of_pos hrc hψ0
  have hintψb : IntervalIntegrable (guardIntegrand α l₁ D) volume √(2 * (α / l₁) - a ^ 2) rb :=
    intervalIntegrable_guardIntegrand_of_pos hψ0 (hψ0.trans_le hψ)
  have hAt0 : 0 ≤ ∫ y in (0 : ℝ)..a, guardIntegrand α l₁ D y :=
    integral_nonneg ha.le fun y hy => guardIntegrand_nonneg hy.1
  have hBt0 : 0 ≤ ∫ y in √(2 * (α / l₁) - a ^ 2)..rb, guardIntegrand α l₁ D y :=
    integral_nonneg hψ fun y hy => guardIntegrand_nonneg (hψ0.le.trans hy.1)
  rw [← integral_add_adjacent_intervals hint0a hintar,
    ← integral_add_adjacent_intervals hintrψ hintψb]
  -- abbreviations
  generalize (∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D)) = I
    at hAm_lo hAm_hi hBm_lo hBm_hi hI htails
  generalize (∫ y in (0 : ℝ)..a, guardIntegrand α l₁ D y) = At at htails hAt0 ⊢
  generalize (∫ y in a..√(α / l₁), guardIntegrand α l₁ D y) = Am at hAm_lo hAm_hi ⊢
  generalize (∫ y in √(α / l₁)..√(2 * (α / l₁) - a ^ 2), guardIntegrand α l₁ D y) = Bm
    at hBm_lo hBm_hi ⊢
  generalize (∫ y in √(2 * (α / l₁) - a ^ 2)..rb, guardIntegrand α l₁ D y) = Bt
    at htails hBt0 ⊢
  have hrm : 0 < √(α / l₁) - (a + √(α / l₁)) / 2 := by linarith
  have hI0 : 0 < I := lt_of_lt_of_le (by positivity) hI
  have hKaI : 0 < guardInner α l₁ D a * I := mul_pos hKa0 hI0
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

/-- **Rate lower bound at a fixed cut.** Under the hypotheses of `guard_ratio_bounds` and the
window condition `√(D̃/α) ≤ r_c − a`: `(1 − δ) A ≤ (1 + ε) B` with `δ = guardDelta α l₁ a D̃`
(`A = ∫₀^{r_c} h`, `B = ∫_{r_c}^{r_b} h`). Together with `B ≤ (1 + κ + ε) A`
(`guard_ratio_bounds`) this pins `B/A` to `1 + O(√D̃)`. The proof compares the reflected
integrand with the inside one pointwise (`|y/ψ(y)² − y⁻¹| ≤ 4(r_c − y)/(a r_c)`) and bounds the
first moment `∫ (r_c − y) e^{U/D̃}` by `2e r_c √(D̃/α)` times the weight integral. -/
@[powerlib_foundation] theorem guard_ratio_rate_bounds (hα : 0 < α) (hl : 0 < l₁) {a rb : ℝ}
    (ha : 0 < a) (har : a < √(α / l₁)) (hψ : √(2 * (α / l₁) - a ^ 2) ≤ rb) (hD : 0 < D)
    (hDa : D ≤ a ^ 2) (hwin : √(D / α) ≤ √(α / l₁) - a) :
    (1 - guardDelta α l₁ a D) * ∫ y in (0 : ℝ)..√(α / l₁), guardIntegrand α l₁ D y ≤
      (1 + guardEps α l₁ a rb D) * ∫ y in √(α / l₁)..rb, guardIntegrand α l₁ D y := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hrc : 0 < √(α / l₁) := Real.sqrt_pos.mpr hρ
  have hrc2 : √(α / l₁) ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  have ha2 : a ^ 2 < α / l₁ := by
    have := pow_lt_pow_left₀ har ha.le (two_ne_zero); rwa [hrc2] at this
  have hrcψ : √(α / l₁) ≤ √(2 * (α / l₁) - a ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have hψ0 : 0 < √(2 * (α / l₁) - a ^ 2) := hrc.trans_le hrcψ
  have hKa := guardInner_ge (l₁ := l₁) hα.le hl.le hD ha.le hDa
  have hKa0 : 0 < guardInner α l₁ D a := lt_of_lt_of_le (by positivity) hKa
  obtain ⟨hAm_lo, -⟩ := guard_inside_bounds (α := α) (l₁ := l₁) (D := D) ha har.le
  have hbl := guard_beyond_lower (D := D) hl ha har.le hρ
  have hJ := guard_firstMoment_le_weight hα hl hD ha hwin
  have htails := guard_tails_le hα hl ha har hψ hD hDa
  have hkap := guardInner_reflect_le hα hl ha har hD hDa
  have hKrψ : guardInner α l₁ D √(α / l₁) ≤ guardInner α l₁ D √(2 * (α / l₁) - a ^ 2) :=
    guardInner_mono hrc.le hrcψ
  have heps0 := guardEps_nonneg hα hl ha har hψ hD
  have hkap0 := guardKappa_nonneg hα hl ha har hD
  have hint0a : IntervalIntegrable (guardIntegrand α l₁ D) volume 0 a :=
    intervalIntegrable_guardIntegrand hl hD ha.le
  have hintar : IntervalIntegrable (guardIntegrand α l₁ D) volume a √(α / l₁) :=
    intervalIntegrable_guardIntegrand_of_pos ha hrc
  have hintrψ : IntervalIntegrable (guardIntegrand α l₁ D) volume √(α / l₁)
      √(2 * (α / l₁) - a ^ 2) := intervalIntegrable_guardIntegrand_of_pos hrc hψ0
  have hintψb : IntervalIntegrable (guardIntegrand α l₁ D) volume √(2 * (α / l₁) - a ^ 2) rb :=
    intervalIntegrable_guardIntegrand_of_pos hψ0 (hψ0.trans_le hψ)
  have hAt0 : 0 ≤ ∫ y in (0 : ℝ)..a, guardIntegrand α l₁ D y :=
    integral_nonneg ha.le fun y hy => guardIntegrand_nonneg hy.1
  have hAm0 : 0 ≤ ∫ y in a..√(α / l₁), guardIntegrand α l₁ D y :=
    integral_nonneg har.le fun y hy => guardIntegrand_nonneg (ha.le.trans hy.1)
  have hBm0 : 0 ≤ ∫ y in √(α / l₁)..√(2 * (α / l₁) - a ^ 2), guardIntegrand α l₁ D y :=
    integral_nonneg hrcψ fun y hy => guardIntegrand_nonneg (hrc.le.trans hy.1)
  have hBt0 : 0 ≤ ∫ y in √(2 * (α / l₁) - a ^ 2)..rb, guardIntegrand α l₁ D y :=
    integral_nonneg hψ fun y hy => guardIntegrand_nonneg (hψ0.le.trans hy.1)
  have hJ0 : 0 ≤ ∫ y in a..√(α / l₁), (√(α / l₁) - y) * Real.exp (guardPotential α l₁ y / D) :=
    integral_nonneg har.le fun y hy => mul_nonneg (by linarith [hy.2]) (Real.exp_pos _).le
  have hI0 : 0 ≤ ∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D) :=
    integral_nonneg har.le fun y hy =>
      mul_nonneg (inv_nonneg.2 (ha.le.trans hy.1)) (Real.exp_pos _).le
  rw [← integral_add_adjacent_intervals hint0a hintar,
    ← integral_add_adjacent_intervals hintrψ hintψb]
  generalize (∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D)) = I
    at hAm_lo hJ htails hI0
  generalize (∫ y in a..√(α / l₁), (√(α / l₁) - y) * Real.exp (guardPotential α l₁ y / D)) = J
    at hbl hJ hJ0
  generalize (∫ y in (0 : ℝ)..a, guardIntegrand α l₁ D y) = At at htails hAt0 ⊢
  generalize (∫ y in a..√(α / l₁), guardIntegrand α l₁ D y) = Am at hAm_lo hbl hAm0 ⊢
  generalize (∫ y in √(α / l₁)..√(2 * (α / l₁) - a ^ 2), guardIntegrand α l₁ D y) = Bm
    at hbl hBm0 ⊢
  generalize (∫ y in √(2 * (α / l₁) - a ^ 2)..rb, guardIntegrand α l₁ D y) = Bt
    at htails hBt0 ⊢
  -- `(4/(a r_c)) K(r_c) J ≤ δ K(a) I ≤ δ A_m`
  have hc0 : 0 ≤ 4 / (a * √(α / l₁)) := by positivity
  have hKr : guardInner α l₁ D √(α / l₁) ≤ (1 + guardKappa α l₁ a D) * guardInner α l₁ D a :=
    hKrψ.trans hkap
  have hδ0 : 0 ≤ guardDelta α l₁ a D := by
    unfold guardDelta
    have : 0 ≤ 1 + guardKappa α l₁ a D := by linarith
    positivity
  have hδ : 4 / (a * √(α / l₁)) * guardInner α l₁ D √(α / l₁) * J ≤
      guardDelta α l₁ a D * Am := by
    calc 4 / (a * √(α / l₁)) * guardInner α l₁ D √(α / l₁) * J
        ≤ 4 / (a * √(α / l₁)) * ((1 + guardKappa α l₁ a D) * guardInner α l₁ D a) * J :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKr hc0) hJ0
      _ ≤ 4 / (a * √(α / l₁)) * ((1 + guardKappa α l₁ a D) * guardInner α l₁ D a) *
            (2 * Real.exp 1 * √(α / l₁) * √(D / α) * I) := by
          apply mul_le_mul_of_nonneg_left hJ
          have : 0 ≤ 1 + guardKappa α l₁ a D := by linarith
          positivity
      _ = guardDelta α l₁ a D * (guardInner α l₁ D a * I) := by
          unfold guardDelta
          field_simp
          ring
      _ ≤ guardDelta α l₁ a D * Am := mul_le_mul_of_nonneg_left hAm_lo hδ0
  have hBm : (1 - guardDelta α l₁ a D) * Am ≤ Bm := by linarith
  have hAt : At ≤ guardEps α l₁ a rb D * Am := by
    have := mul_le_mul_of_nonneg_left hAm_lo heps0
    linarith
  rcases le_or_gt 0 (1 - guardDelta α l₁ a D) with h | h
  · calc (1 - guardDelta α l₁ a D) * (At + Am)
        ≤ (1 - guardDelta α l₁ a D) * ((1 + guardEps α l₁ a rb D) * Am) :=
          mul_le_mul_of_nonneg_left (by linarith) h
      _ = (1 + guardEps α l₁ a rb D) * ((1 - guardDelta α l₁ a D) * Am) := by ring
      _ ≤ (1 + guardEps α l₁ a rb D) * (Bm + Bt) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  · have h1 : (1 - guardDelta α l₁ a D) * (At + Am) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h.le (by linarith)
    have h2 : 0 ≤ (1 + guardEps α l₁ a rb D) * (Bm + Bt) :=
      mul_nonneg (by linarith) (by linarith)
    linarith

/-- **Explicit rate for `T_committed / T_guard`.** Under the hypotheses of
`guard_ratio_rate_bounds`: `|T(r_b)/T(r_c) − 2| ≤ δ + κ + ε`, where `δ = guardDelta α l₁ a D̃`
is `O(√D̃)` and `κ`, `ε` are exponentially small (`tendsto_guardKappa_div`,
`tendsto_guardEps_div`). -/
@[powerlib_foundation] theorem guardMFPT_ratio_sub_two_le (hα : 0 < α) (hl : 0 < l₁) {a rb : ℝ}
    (ha : 0 < a) (har : a < √(α / l₁)) (hψ : √(2 * (α / l₁) - a ^ 2) ≤ rb) (hD : 0 < D)
    (hDa : D ≤ a ^ 2) (hwin : √(D / α) ≤ √(α / l₁) - a) :
    |guardMFPT α l₁ D rb / guardMFPT α l₁ D (guardRadius α l₁) - 2| ≤
      guardDelta α l₁ a D + guardKappa α l₁ a D + guardEps α l₁ a rb D := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hrc : 0 < √(α / l₁) := Real.sqrt_pos.mpr hρ
  have hrc2 : √(α / l₁) ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  have ha2 : a ^ 2 < α / l₁ := by
    have := pow_lt_pow_left₀ har ha.le (two_ne_zero); rwa [hrc2] at this
  have hrcψ : √(α / l₁) < √(2 * (α / l₁) - a ^ 2) := Real.sqrt_lt_sqrt hρ.le (by linarith)
  have hrb : √(α / l₁) < rb := hrcψ.trans_le hψ
  obtain ⟨hA, hup, -⟩ := guard_ratio_bounds hα hl ha har hψ hD hDa
  have hlow := guard_ratio_rate_bounds hα hl ha har hψ hD hDa hwin
  have heps0 := guardEps_nonneg hα hl ha har hψ hD
  have hkap0 := guardKappa_nonneg hα hl ha har hD
  have hδ0 : 0 ≤ guardDelta α l₁ a D := by
    unfold guardDelta
    have : 0 ≤ 1 + guardKappa α l₁ a D := by linarith
    positivity
  have hratio : guardMFPT α l₁ D rb / guardMFPT α l₁ D (guardRadius α l₁) =
      ((∫ y in (0 : ℝ)..√(α / l₁), guardIntegrand α l₁ D y) +
        ∫ y in √(α / l₁)..rb, guardIntegrand α l₁ D y) /
          ∫ y in (0 : ℝ)..√(α / l₁), guardIntegrand α l₁ D y := by
    simp only [guardMFPT, guardRadius]
    rw [← integral_add_adjacent_intervals (intervalIntegrable_guardIntegrand hl hD hrc.le)
      (intervalIntegrable_guardIntegrand_of_pos hrc (hrc.trans hrb))]
    exact mul_div_mul_left _ _ (inv_ne_zero (ne_of_gt hD))
  rw [hratio]
  generalize (∫ y in (0 : ℝ)..√(α / l₁), guardIntegrand α l₁ D y) = A at hA hup hlow ⊢
  generalize (∫ y in √(α / l₁)..rb, guardIntegrand α l₁ D y) = B at hup hlow ⊢
  have hB_lo : (1 - guardDelta α l₁ a D - guardEps α l₁ a rb D) * A ≤ B := by
    have h1 : (1 + guardEps α l₁ a rb D) *
        ((1 - guardDelta α l₁ a D - guardEps α l₁ a rb D) * A) ≤
          (1 + guardEps α l₁ a rb D) * B := by
      nlinarith [mul_nonneg (mul_nonneg hδ0 heps0) hA.le,
        mul_nonneg (mul_nonneg heps0 heps0) hA.le]
    exact le_of_mul_le_mul_left h1 (by linarith)
  have e : (A + B) / A - 2 = B / A - 1 := by field_simp; ring
  rw [e, abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ hA]
    nlinarith [mul_nonneg hkap0 hA.le]
  · rw [sub_le_iff_le_add, div_le_iff₀ hA]
    nlinarith [mul_nonneg hδ0 hA.le]

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

/-- `e^{−c/D̃}/D̃² → 0` as `D̃ → 0⁺` (`c > 0`). -/
@[powerlib_foundation] theorem tendsto_exp_neg_div_div_div {c : ℝ} (hc : 0 < c) :
    Tendsto (fun D : ℝ => Real.exp (-(c / D)) / D / D) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => t ^ 2 * Real.exp (-(c * t))) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
      (tendsto_id.const_mul_atTop hc)).const_mul (c⁻¹ ^ 2)
    rw [mul_zero] at h
    refine h.congr fun t => ?_
    simp only [Function.comp_apply, id]
    field_simp
  refine (h1.comp tendsto_inv_nhdsGT_zero).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with D hD
  simp only [Function.comp_apply]
  rw [div_eq_mul_inv c]
  field_simp

/-- `κ = o(D̃)`: the inner-integral growth across the barrier is exponentially small. -/
@[powerlib_foundation] theorem tendsto_guardKappa_div (hl : 0 < l₁) {a : ℝ} (ha : 0 < a)
    (ha2 : a ^ 2 < 2 * (α / l₁)) :
    Tendsto (fun D => guardKappa α l₁ a D / D) (𝓝[>] 0) (𝓝 0) := by
  have hU := guardPotential_pos (α := α) hl ha ha2
  have h := (tendsto_exp_neg_div_div_div hU).const_mul
    ((√(2 * (α / l₁) - a ^ 2) - a) * √(2 * (α / l₁) - a ^ 2) / (Real.exp (-(α / 2)) / 2))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with D hD
  have hD0 : (D : ℝ) ≠ 0 := ne_of_gt hD
  simp only [guardKappa]
  field_simp

/-- `ε = o(D̃)`: the tails are exponentially small. -/
@[powerlib_foundation] theorem tendsto_guardEps_div (hl : 0 < l₁) {a rb : ℝ} (ha : 0 < a)
    (har : a < √(α / l₁)) (hρ : 0 < α / l₁) :
    Tendsto (fun D => guardEps α l₁ a rb D / D) (𝓝[>] 0) (𝓝 0) := by
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
  have h := ((tendsto_exp_neg_div_div_div hUma).add
    (tendsto_exp_neg_div_div_div hUm)).const_mul C
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

/-- Choice of the cut: for every `t < 1` there is `a ∈ (0, r_c)` with `ψ(a) ≤ r_b` and
`t < a²/(2r_c² − a²)`. -/
@[powerlib_foundation] private theorem guard_exists_cut (hα : 0 < α) (hl : 0 < l₁) {rb : ℝ}
    (hrb : guardRadius α l₁ < rb) {t : ℝ} (ht : t < 1) :
    ∃ a, 0 < a ∧ a < √(α / l₁) ∧ √(2 * (α / l₁) - a ^ 2) ≤ rb ∧
      t < a ^ 2 / (2 * (α / l₁) - a ^ 2) := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  set rc := guardRadius α l₁ with hrcdef
  have hrcs : rc = √(α / l₁) := rfl
  have hrc : 0 < rc := Real.sqrt_pos.mpr hρ
  have hrc2 : rc ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
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
      t < a ^ 2 / (2 * (α / l₁) - a ^ 2) := fun t ht => guard_exists_cut hα hl hrb ht
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

/-- **`T_committed / T_guard = 2 + O(√D̃)`** as `D̃ → 0⁺` (source §1.2: the approach to `2` is
itself an endpoint effect of relative order `X^{−1/2}`, `X = ΔU/D̃`), for every committed-escape
boundary `r_b > r_c`. Explicitly, at a fixed cut `a`, `|T(r_b)/T(r_c) − 2| ≤ δ + κ + ε`
(`guardMFPT_ratio_sub_two_le`) with `δ ≤ (16e/a) √(D̃/α)` and `κ, ε ≤ D̃` eventually. -/
@[powerlib_foundation] theorem guardMFPT_ratio_sub_two_isBigO (hα : 0 < α) (hl : 0 < l₁)
    {rb : ℝ} (hrb : guardRadius α l₁ < rb) :
    (fun D => guardMFPT α l₁ D rb / guardMFPT α l₁ D (guardRadius α l₁) - 2) =O[𝓝[>] 0]
      fun D => √D := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hrc2 : √(α / l₁) ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  obtain ⟨a, ha, har, hψ, -⟩ := guard_exists_cut hα hl hrb (t := 0) one_pos
  have ha2 : a ^ 2 < 2 * (α / l₁) := by
    have := pow_lt_pow_left₀ har ha.le two_ne_zero; rw [hrc2] at this; linarith
  have hκ := tendsto_guardKappa_div (α := α) hl ha ha2
  have hε := tendsto_guardEps_div (rb := rb) hl ha har hρ
  have hs : Tendsto (fun D : ℝ => √(D / α)) (𝓝[>] 0) (𝓝 0) := by
    have h := ((continuous_id.div_const α).sqrt).tendsto (0 : ℝ)
    simp only [id, zero_div, Real.sqrt_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hsα : 0 < √α := Real.sqrt_pos.mpr hα
  apply Asymptotics.IsBigO.of_bound (16 * Real.exp 1 / a / √α + 2)
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds (by positivity : (0 : ℝ) < a ^ 2)),
    nhdsWithin_le_nhds (eventually_lt_nhds (one_pos : (0 : ℝ) < 1)),
    hs.eventually (gt_mem_nhds (sub_pos.2 har)),
    hκ.eventually (gt_mem_nhds one_pos), hε.eventually (gt_mem_nhds one_pos)]
    with D hD hDa hD1 hwin hκD hεD
  have hD0 : (0 : ℝ) < D := hD
  have hκle : guardKappa α l₁ a D ≤ D := by
    have := (div_lt_one hD0).1 hκD; linarith
  have hεle : guardEps α l₁ a rb D ≤ D := by
    have := (div_lt_one hD0).1 hεD; linarith
  have hkap0 := guardKappa_nonneg hα hl ha har hD0
  have hbound := guardMFPT_ratio_sub_two_le hα hl ha har hψ hD0 hDa.le hwin.le
  have hsD : √(D / α) = √D / √α := Real.sqrt_div' D hα.le
  have hDs : D ≤ √D := by
    have h1 : √D ^ 2 = D := Real.sq_sqrt hD0.le
    have h2 : √D ≤ 1 := by
      rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hD1.le
    nlinarith [Real.sqrt_nonneg D]
  have hδ : guardDelta α l₁ a D ≤ 16 * Real.exp 1 / a / √α * √D := by
    unfold guardDelta
    rw [hsD]
    have h1 : 1 + guardKappa α l₁ a D ≤ 2 := by linarith
    have h2 : 0 ≤ 8 * Real.exp 1 / a * (√D / √α) := by positivity
    calc 8 * Real.exp 1 / a * (1 + guardKappa α l₁ a D) * (√D / √α)
        = (1 + guardKappa α l₁ a D) * (8 * Real.exp 1 / a * (√D / √α)) := by ring
      _ ≤ 2 * (8 * Real.exp 1 / a * (√D / √α)) := mul_le_mul_of_nonneg_right h1 h2
      _ = 16 * Real.exp 1 / a / √α * √D := by ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg D)]
  refine hbound.trans ?_
  have : 0 ≤ 16 * Real.exp 1 / a / √α * √D := by positivity
  nlinarith

/-- **`T_committed / T_guard = 2(1 + O(X^{−1/2}))`** along `X = ΔU/D̃ → ∞`, `ΔU = α²/(4 l₁)`
(source §1.2, "趋近 2 的方式本身是 `1 + O(X^{−1/2})`"). The half-order term is genuinely present
in general (`endpointCorrection_ne_zero_iff`); this theorem is the upper bound. -/
@[powerlib_foundation] theorem guardMFPT_ratio_isBigO_atTop (hα : 0 < α) (hl : 0 < l₁) {rb : ℝ}
    (hrb : guardRadius α l₁ < rb) :
    (fun X => guardMFPT α l₁ (barrierHeight α l₁ / X) rb /
        guardMFPT α l₁ (barrierHeight α l₁ / X) (guardRadius α l₁) / 2 - 1) =O[atTop]
      fun X => (√X)⁻¹ := by
  have hΔ : 0 < barrierHeight α l₁ := by unfold barrierHeight; positivity
  have hD : Tendsto (fun X : ℝ => barrierHeight α l₁ / X) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.div_atTop tendsto_id, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with X hX
    exact div_pos hΔ hX
  have h1 := (guardMFPT_ratio_sub_two_isBigO hα hl hrb).comp_tendsto hD
  have h2 : (fun X => √(barrierHeight α l₁ / X)) =O[atTop] fun X => (√X)⁻¹ := by
    apply Asymptotics.IsBigO.of_bound (√(barrierHeight α l₁))
    filter_upwards [eventually_gt_atTop 0] with X hX
    have hsX : 0 < √X := Real.sqrt_pos.mpr hX
    rw [Real.sqrt_div' _ hX.le, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), div_eq_mul_inv]
  have h3 := (h1.trans h2).const_mul_left (1 / 2)
  refine h3.congr_left fun X => ?_
  simp only [Function.comp_apply]
  ring

end Ratio

/-! ## The single-term asymptotics `T_guard ~ P e^X` -/

section Guard

/-- `∫_0^y z e^{−αz²/(2D̃)} dz = (D̃/α)(1 − e^{−αy²/(2D̃)})`. -/
@[powerlib_foundation] theorem integral_mul_exp_neg_sq_div (hα : 0 < α) {D : ℝ} (hD : 0 < D)
    (y : ℝ) :
    ∫ z in (0 : ℝ)..y, z * Real.exp (-(α / (2 * D)) * z ^ 2) =
      D / α * (1 - Real.exp (-(α / (2 * D)) * y ^ 2)) := by
  have hderiv : ∀ z ∈ uIcc 0 y, HasDerivAt (fun z => -(D / α) * Real.exp (-(α / (2 * D)) * z ^ 2))
      (z * Real.exp (-(α / (2 * D)) * z ^ 2)) z := by
    intro z _
    have h1 : HasDerivAt (fun z => -(α / (2 * D)) * z ^ 2) (-(α / (2 * D)) * (2 * z)) z := by
      simpa using (hasDerivAt_pow 2 z).const_mul (-(α / (2 * D)))
    have := (h1.exp).const_mul (-(D / α))
    convert this using 1
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun z : ℝ =>
      z * Real.exp (-(α / (2 * D)) * z ^ 2)).intervalIntegrable _ _)]
  simp
  ring

/-- Lower Gaussian bound for the inner integral: `K(y) ≥ (D̃/α)(1 − e^{−αy²/(2D̃)})`, `y ≥ 0`
(from `U(z) ≤ αz²/2`). -/
@[powerlib_foundation] theorem guardInner_ge_gauss (hα : 0 < α) (hl : 0 ≤ l₁) {D y : ℝ}
    (hD : 0 < D) (hy : 0 ≤ y) :
    D / α * (1 - Real.exp (-(α / (2 * D)) * y ^ 2)) ≤ guardInner α l₁ D y := by
  rw [← integral_mul_exp_neg_sq_div hα hD]
  apply integral_mono_on hy
    ((by fun_prop : Continuous fun z : ℝ =>
      z * Real.exp (-(α / (2 * D)) * z ^ 2)).intervalIntegrable _ _)
    ((continuous_guardInner_integrand α l₁ D).intervalIntegrable _ _)
  intro z hz
  apply mul_le_mul_of_nonneg_left _ hz.1
  apply Real.exp_le_exp.mpr
  have h := guardPotential_le_quad (α := α) hl z
  have : guardPotential α l₁ z / D ≤ α / (2 * D) * z ^ 2 := by
    rw [div_le_iff₀ hD]
    have e : α / (2 * D) * z ^ 2 * D = α * z ^ 2 / 2 := by field_simp
    rw [e]; exact h
  linarith

/-- Upper Gaussian bound for the inner integral up to the barrier top:
`K(r_c) ≤ (D̃/α)(1 + 16 l₁ D̃/α²)` (from `e^{−U/D̃} ≤ e^{−αz²/(2D̃)} + (l₁z⁴/(4D̃)) e^{−αz²/(4D̃)}`
on `[0, r_c]` and the fifth half-line moment). -/
@[powerlib_foundation] theorem guardInner_le_gauss (hα : 0 < α) (hl : 0 < l₁) {D : ℝ}
    (hD : 0 < D) :
    guardInner α l₁ D √(α / l₁) ≤ D / α * (1 + 16 * l₁ * D / α ^ 2) := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hrc : 0 ≤ √(α / l₁) := Real.sqrt_nonneg _
  have hrc2 : √(α / l₁) ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  have hc : 0 < α / (4 * D) := by positivity
  have hg5 : Continuous fun z : ℝ =>
      l₁ / (4 * D) * (z ^ 5 * Real.exp (-(α / (4 * D)) * z ^ 2)) := by fun_prop
  have hg1 : Continuous fun z : ℝ => z * Real.exp (-(α / (2 * D)) * z ^ 2) := by fun_prop
  have hpt : ∀ z ∈ Icc (0 : ℝ) √(α / l₁), z * Real.exp (-(guardPotential α l₁ z / D)) ≤
      z * Real.exp (-(α / (2 * D)) * z ^ 2) +
        l₁ / (4 * D) * (z ^ 5 * Real.exp (-(α / (4 * D)) * z ^ 2)) := by
    intro z hz
    have hz2 : z ^ 2 ≤ α / l₁ := by
      have := pow_le_pow_left₀ hz.1 hz.2 2; rwa [hrc2] at this
    have hlz : l₁ * z ^ 2 ≤ α := by rwa [le_div_iff₀ hl, mul_comm] at hz2
    set s := guardPotential α l₁ z / D with hs
    set t := α / (2 * D) * z ^ 2 with ht
    have hts : t - s = l₁ / (4 * D) * z ^ 4 := by
      simp only [hs, ht, guardPotential]; field_simp; ring
    have hs4 : α / (4 * D) * z ^ 2 ≤ s := by
      simp only [hs, guardPotential]
      rw [le_div_iff₀ hD]
      have e : α / (4 * D) * z ^ 2 * D = α * z ^ 2 / 4 := by field_simp
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left hlz (sq_nonneg z)]
    have hts0 : 0 ≤ t - s := by rw [hts]; positivity
    -- `e^{−s} ≤ e^{−t} + (t − s) e^{−s}`
    have hexp : Real.exp (-s) ≤ Real.exp (-t) + (t - s) * Real.exp (-s) := by
      have h1 := Real.add_one_le_exp (-(t - s))
      have h2 : Real.exp (-t) = Real.exp (-s) * Real.exp (-(t - s)) := by
        rw [← Real.exp_add]; congr 1; ring
      have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-s)).le
      nlinarith
    have hexp2 : Real.exp (-s) ≤ Real.exp (-(α / (4 * D)) * z ^ 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have : Real.exp (-s) ≤ Real.exp (-t) +
        l₁ / (4 * D) * z ^ 4 * Real.exp (-(α / (4 * D)) * z ^ 2) := by
      rw [← hts]; nlinarith [mul_le_mul_of_nonneg_left hexp2 hts0]
    have e1 : Real.exp (-t) = Real.exp (-(α / (2 * D)) * z ^ 2) := by
      simp only [ht]; ring_nf
    rw [e1] at this
    calc z * Real.exp (-s) ≤ z * (Real.exp (-(α / (2 * D)) * z ^ 2) +
          l₁ / (4 * D) * z ^ 4 * Real.exp (-(α / (4 * D)) * z ^ 2)) :=
          mul_le_mul_of_nonneg_left this hz.1
      _ = _ := by ring
  have hint5 : IntegrableOn (fun z : ℝ => l₁ / (4 * D) *
      (z ^ 5 * Real.exp (-(α / (4 * D)) * z ^ 2))) (Ioi 0) :=
    ((integrable_pow_mul_exp_neg_mul_sq hc 5).const_mul _).integrableOn
  calc guardInner α l₁ D √(α / l₁)
      ≤ ∫ z in (0 : ℝ)..√(α / l₁), (z * Real.exp (-(α / (2 * D)) * z ^ 2) +
          l₁ / (4 * D) * (z ^ 5 * Real.exp (-(α / (4 * D)) * z ^ 2))) :=
        integral_mono_on hrc ((continuous_guardInner_integrand α l₁ D).intervalIntegrable _ _)
          ((hg1.add hg5).intervalIntegrable _ _) hpt
    _ = (∫ z in (0 : ℝ)..√(α / l₁), z * Real.exp (-(α / (2 * D)) * z ^ 2)) +
          ∫ z in (0 : ℝ)..√(α / l₁), l₁ / (4 * D) *
            (z ^ 5 * Real.exp (-(α / (4 * D)) * z ^ 2)) :=
        intervalIntegral.integral_add (hg1.intervalIntegrable _ _) (hg5.intervalIntegrable _ _)
    _ ≤ D / α + l₁ / (4 * D) * (1 / (α / (4 * D)) ^ 3) := by
        apply add_le_add
        · rw [integral_mul_exp_neg_sq_div hα hD]
          have := Real.exp_pos (-(α / (2 * D)) * √(α / l₁) ^ 2)
          have : 0 < D / α := by positivity
          nlinarith
        · refine (intervalIntegral_le_integral_Ioi hrc hint5 fun z hz => by positivity).trans ?_
          rw [MeasureTheory.integral_const_mul, gaussMoment5 hc]
    _ = D / α * (1 + 16 * l₁ * D / α ^ 2) := by field_simp; ring


/-- Lower Gaussian bound for the barrier weight, `c = α/D̃`:
`∫_a^{r_c} y⁻¹ e^{U/D̃} ≥ r_c⁻¹ e^{ΔU/D̃} (√(π/c)/2 − 1/(2c(r_c − a)))`
(from `U(y) ≥ ΔU − α(r_c − y)²` and `integral_exp_neg_mul_sq_ge`). -/
@[powerlib_foundation] theorem guard_weight_ge_gauss (hα : 0 < α) (hl : 0 < l₁) {D a : ℝ}
    (hD : 0 < D) (ha : 0 < a) (har : a < √(α / l₁)) :
    (√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) *
        (√(π / (α / D)) / 2 - 1 / (2 * (α / D) * (√(α / l₁) - a))) ≤
      ∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D) := by
  have hc : 0 < α / D := div_pos hα hD
  have hG := integral_exp_neg_mul_sq_ge hc (sub_pos.2 har)
  have hsub : ∫ y in a..√(α / l₁), Real.exp (-(α / D) * (√(α / l₁) - y) ^ 2) =
      ∫ ξ in (0 : ℝ)..(√(α / l₁) - a), Real.exp (-(α / D) * ξ ^ 2) := by
    have := intervalIntegral.integral_comp_sub_left
      (fun ξ => Real.exp (-(α / D) * ξ ^ 2)) (√(α / l₁)) (a := a) (b := √(α / l₁))
    simp only [sub_self] at this
    exact this
  calc (√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) *
        (√(π / (α / D)) / 2 - 1 / (2 * (α / D) * (√(α / l₁) - a)))
      ≤ (√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) *
          ∫ y in a..√(α / l₁), Real.exp (-(α / D) * (√(α / l₁) - y) ^ 2) := by
        rw [hsub]; exact mul_le_mul_of_nonneg_left hG (by positivity)
    _ = ∫ y in a..√(α / l₁), (√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) *
          Real.exp (-(α / D) * (√(α / l₁) - y) ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D) := by
        apply integral_mono_on har.le
        · exact (by fun_prop : Continuous fun y : ℝ => (√(α / l₁))⁻¹ *
            Real.exp (barrierHeight α l₁ / D) *
              Real.exp (-(α / D) * (√(α / l₁) - y) ^ 2)).intervalIntegrable _ _
        · apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le har.le]
          apply ContinuousOn.mul _ (continuous_exp_guardPotential α l₁ D).continuousOn
          exact continuousOn_inv₀.mono fun y hy => (ne_of_gt (ha.trans_le hy.1) : y ≠ 0)
        intro y hy
        have hy0 : 0 < y := ha.trans_le hy.1
        rw [mul_assoc, ← Real.exp_add]
        apply mul_le_mul (inv_anti₀ hy0 hy.2) _ (Real.exp_pos _).le (inv_nonneg.2 hy0.le)
        apply Real.exp_le_exp.mpr
        have hU := barrier_sub_sq_le_guardPotential hα hl hy0.le hy.2
        have e : barrierHeight α l₁ / D + -(α / D) * (√(α / l₁) - y) ^ 2 =
            (barrierHeight α l₁ - α * (√(α / l₁) - y) ^ 2) / D := by field_simp; ring
        rw [e]
        exact div_le_div_of_nonneg_right hU hD.le

/-- Upper Gaussian bound for the barrier weight, `c = α/D̃`, `c' = α/(4D̃)`:
`∫_a^{r_c} y⁻¹ e^{U/D̃} ≤ e^{ΔU/D̃} (r_c⁻¹ √(π/c)/2 + (a r_c)⁻¹/(2c) + (l₁ r_c/(a D̃))/(2c'²))`.
In `ξ = r_c − y`: `U = ΔU − D̃ s`, `s ≥ c'ξ²`, `0 ≤ cξ² − s ≤ l₁ r_c ξ³/D̃`, so
`e^{−s} ≤ e^{−cξ²} + (l₁ r_c ξ³/D̃) e^{−c'ξ²}`; and `(r_c − ξ)⁻¹ ≤ r_c⁻¹ + ξ/(a r_c)`. -/
@[powerlib_foundation] theorem guard_weight_le_gauss (hα : 0 < α) (hl : 0 < l₁) {D a : ℝ}
    (hD : 0 < D) (ha : 0 < a) (har : a < √(α / l₁)) :
    ∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D) ≤
      Real.exp (barrierHeight α l₁ / D) * ((√(α / l₁))⁻¹ * (√(π / (α / D)) / 2) +
        (a * √(α / l₁))⁻¹ * (1 / (2 * (α / D))) +
          l₁ * √(α / l₁) / (a * D) * (1 / (2 * (α / (4 * D)) ^ 2))) := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hc : 0 < α / D := div_pos hα hD
  have hc' : 0 < α / (4 * D) := by positivity
  obtain ⟨rc, hrcdef, hrc2⟩ : ∃ r, r = √(α / l₁) ∧ r ^ 2 = α / l₁ :=
    ⟨_, rfl, Real.sq_sqrt hρ.le⟩
  rw [← hrcdef] at har ⊢
  have hrc : 0 < rc := ha.trans har
  have hαe : α = l₁ * rc ^ 2 := by rw [hrc2]; field_simp
  have hL0 : 0 < rc - a := sub_pos.2 har
  -- substitution `y = r_c − ξ`
  have hsub : ∫ y in a..rc, y⁻¹ * Real.exp (guardPotential α l₁ y / D) =
      ∫ ξ in (0 : ℝ)..(rc - a), (rc - ξ)⁻¹ * Real.exp (guardPotential α l₁ (rc - ξ) / D) := by
    have := intervalIntegral.integral_comp_sub_left
      (fun ξ => (rc - ξ)⁻¹ * Real.exp (guardPotential α l₁ (rc - ξ) / D)) rc (a := a) (b := rc)
    simp only [sub_sub_cancel, sub_self] at this
    exact this
  set E := Real.exp (barrierHeight α l₁ / D) with hE
  set F : ℝ → ℝ := fun ξ => E * (rc⁻¹ * Real.exp (-(α / D) * ξ ^ 2) +
      (a * rc)⁻¹ * (ξ * Real.exp (-(α / D) * ξ ^ 2)) +
        l₁ * rc / (a * D) * (ξ ^ 3 * Real.exp (-(α / (4 * D)) * ξ ^ 2))) with hF
  have hFc : Continuous F := by simp only [hF]; fun_prop
  have hFi : IntegrableOn F (Ioi 0) := by
    have := (((integrable_exp_neg_mul_sq hc).const_mul rc⁻¹).add
      ((integrable_mul_exp_neg_mul_sq hc).const_mul (a * rc)⁻¹)).add
      ((integrable_pow_mul_exp_neg_mul_sq hc' 3).const_mul (l₁ * rc / (a * D)))
    exact (this.const_mul E).integrableOn
  have hF0 : ∀ ξ : ℝ, 0 < ξ → 0 ≤ F ξ := fun ξ hξ => by simp only [hF]; positivity
  have hpt : ∀ ξ ∈ Icc (0 : ℝ) (rc - a),
      (rc - ξ)⁻¹ * Real.exp (guardPotential α l₁ (rc - ξ) / D) ≤ F ξ := by
    intro ξ hξ
    have hξ0 := hξ.1
    have hra : a ≤ rc - ξ := by linarith [hξ.2]
    have hr0 : 0 < rc - ξ := ha.trans_le hra
    have hξr : ξ ≤ rc := by linarith
    set s := l₁ / 4 * (ξ ^ 2 * (2 * rc - ξ) ^ 2) / D with hs
    have hU : guardPotential α l₁ (rc - ξ) / D = barrierHeight α l₁ / D - s := by
      rw [guardPotential_eq_barrier_sub hl, ← hrc2]; simp only [hs]; field_simp; ring
    set t := α / D * ξ ^ 2 with ht
    have hts : t - s = l₁ / (4 * D) * (ξ ^ 2 * (4 * rc * ξ - ξ ^ 2)) := by
      simp only [hs, ht]; rw [hαe]; field_simp; ring
    have hts0 : 0 ≤ t - s := by
      rw [hts]
      have : 0 ≤ 4 * rc * ξ - ξ ^ 2 := by nlinarith
      positivity
    have hts1 : t - s ≤ l₁ * rc / D * ξ ^ 3 := by
      rw [hts]
      have e : l₁ / (4 * D) * (ξ ^ 2 * (4 * rc * ξ - ξ ^ 2)) =
          l₁ * rc / D * ξ ^ 3 - l₁ / (4 * D) * ξ ^ 4 := by field_simp
      rw [e]
      have : 0 ≤ l₁ / (4 * D) * ξ ^ 4 := by positivity
      linarith
    have hs4 : α / (4 * D) * ξ ^ 2 ≤ s := by
      simp only [hs]
      rw [le_div_iff₀ hD, hαe]
      have e : l₁ * rc ^ 2 / (4 * D) * ξ ^ 2 * D = l₁ / 4 * (ξ ^ 2 * rc ^ 2) := by field_simp
      rw [e]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg ξ)
      nlinarith
    have hexp : Real.exp (-s) ≤ Real.exp (-t) + (t - s) * Real.exp (-s) := by
      have h1 := Real.add_one_le_exp (-(t - s))
      have h2 : Real.exp (-t) = Real.exp (-s) * Real.exp (-(t - s)) := by
        rw [← Real.exp_add]; congr 1; ring
      have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-s)).le
      nlinarith
    have hexp2 : Real.exp (-s) ≤ Real.exp (-(α / (4 * D)) * ξ ^ 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have hexp3 : Real.exp (-s) ≤ Real.exp (-(α / D) * ξ ^ 2) +
        l₁ * rc / D * ξ ^ 3 * Real.exp (-(α / (4 * D)) * ξ ^ 2) := by
      have e : Real.exp (-t) = Real.exp (-(α / D) * ξ ^ 2) := by simp only [ht]; ring_nf
      have : (t - s) * Real.exp (-s) ≤ l₁ * rc / D * ξ ^ 3 *
          Real.exp (-(α / (4 * D)) * ξ ^ 2) :=
        mul_le_mul hts1 hexp2 (Real.exp_pos _).le (by positivity)
      rw [← e]; linarith
    have hinv1 : (rc - ξ)⁻¹ ≤ rc⁻¹ + (a * rc)⁻¹ * ξ := by
      have e : (rc - ξ)⁻¹ = rc⁻¹ + ξ / (rc * (rc - ξ)) := by field_simp; ring
      have h : ξ / (rc * (rc - ξ)) ≤ ξ / (rc * a) :=
        div_le_div_of_nonneg_left hξ0 (by positivity) (mul_le_mul_of_nonneg_left hra hrc.le)
      rw [e]
      have e2 : ξ / (rc * a) = (a * rc)⁻¹ * ξ := by field_simp
      linarith
    have hinv2 : (rc - ξ)⁻¹ ≤ a⁻¹ := inv_anti₀ ha hra
    have hE0 : 0 < E := Real.exp_pos _
    have hes : Real.exp (barrierHeight α l₁ / D - s) = E * Real.exp (-s) := by
      rw [hE, ← Real.exp_add]; ring_nf
    rw [hU, hes]
    have hK : 0 ≤ l₁ * rc / D * ξ ^ 3 * Real.exp (-(α / (4 * D)) * ξ ^ 2) := by positivity
    have hq0 : 0 ≤ (rc - ξ)⁻¹ := (inv_pos.2 hr0).le
    calc (rc - ξ)⁻¹ * (E * Real.exp (-s)) = E * ((rc - ξ)⁻¹ * Real.exp (-s)) := by ring
      _ ≤ E * ((rc - ξ)⁻¹ * Real.exp (-(α / D) * ξ ^ 2) +
            (rc - ξ)⁻¹ * (l₁ * rc / D * ξ ^ 3 * Real.exp (-(α / (4 * D)) * ξ ^ 2))) := by
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp3 hq0) hE0.le
      _ ≤ E * ((rc⁻¹ + (a * rc)⁻¹ * ξ) * Real.exp (-(α / D) * ξ ^ 2) +
            a⁻¹ * (l₁ * rc / D * ξ ^ 3 * Real.exp (-(α / (4 * D)) * ξ ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ hE0.le
          exact add_le_add (mul_le_mul_of_nonneg_right hinv1 (Real.exp_pos _).le)
            (mul_le_mul_of_nonneg_right hinv2 hK)
      _ = F ξ := by simp only [hF]; field_simp
  have hlhs : IntervalIntegrable (fun ξ => (rc - ξ)⁻¹ *
      Real.exp (guardPotential α l₁ (rc - ξ) / D)) volume 0 (rc - a) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hL0.le]
    apply ContinuousOn.mul
    · apply ContinuousOn.inv₀ (by fun_prop)
      intro ξ hξ; have := hξ.2; linarith
    · exact ((continuous_exp_guardPotential α l₁ D).comp
        (continuous_const.sub continuous_id)).continuousOn
  rw [hsub]
  calc ∫ ξ in (0 : ℝ)..(rc - a), (rc - ξ)⁻¹ * Real.exp (guardPotential α l₁ (rc - ξ) / D)
      ≤ ∫ ξ in (0 : ℝ)..(rc - a), F ξ :=
        integral_mono_on hL0.le hlhs (hFc.intervalIntegrable _ _) hpt
    _ ≤ ∫ ξ in Ioi (0 : ℝ), F ξ := intervalIntegral_le_integral_Ioi hL0.le hFi hF0
    _ = _ := by
        have i0 := (integrable_exp_neg_mul_sq hc).integrableOn (s := Ioi (0 : ℝ))
        have i1 := (integrable_mul_exp_neg_mul_sq hc).integrableOn (s := Ioi (0 : ℝ))
        have i3 := (integrable_pow_mul_exp_neg_mul_sq hc' 3).integrableOn (s := Ioi (0 : ℝ))
        simp only [hF]
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add,
          MeasureTheory.integral_add, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          integral_gaussian_Ioi, gaussMoment1 hc, gaussMoment3 hc']
        all_goals first
          | exact i0.const_mul _
          | exact i1.const_mul _
          | exact i3.const_mul _
          | exact (i0.const_mul _).add (i1.const_mul _)


/-- `D̃ P = (D̃/α) · r_c⁻¹ · √(π/(α/D̃))/2`: the prefactor is the product of the inner Gaussian
mass `D̃/α`, the weight `1/r_c` at the top and the half Gaussian `√(πD̃/α)/2`. -/
@[powerlib_foundation] theorem mul_guardPrefactor_eq (hα : 0 < α) (hl : 0 < l₁) {D : ℝ}
    (hD : 0 < D) :
    D * guardPrefactor α l₁ D = D / α * ((√(α / l₁))⁻¹ * (√(π / (α / D)) / 2)) := by
  have e1 : π / (α / D) = π * D / α := by field_simp
  rw [guardPrefactor, e1, Real.sqrt_div' _ hα.le, Real.sqrt_div' _ hl.le,
    Real.sqrt_mul Real.pi_pos.le, Real.sqrt_mul hD.le]
  have hsl : 0 < √l₁ := Real.sqrt_pos.mpr hl
  obtain ⟨u, hu, hu2⟩ : ∃ u, u = √α ∧ u ^ 2 = α := ⟨_, rfl, Real.sq_sqrt hα.le⟩
  have hu0 : 0 < u := hu ▸ Real.sqrt_pos.mpr hα
  rw [← hu, ← hu2]
  field_simp

/-- Algebra of the upper weight bound in `σ = √(D̃/α)`. -/
@[powerlib_foundation] private theorem weight_upper_identity {α l₁ D a rc σ p : ℝ}
    (hα : 0 < α) (hl : 0 < l₁) (hD : 0 < D) (ha : 0 < a) (hrc : 0 < rc)
    (hrc2 : rc ^ 2 = α / l₁) (hσ : 0 < σ) (hσ2 : σ ^ 2 = D / α) (hp : 0 < p) :
    rc⁻¹ * (p * σ / 2) + (a * rc)⁻¹ * (1 / (2 * (α / D))) +
        l₁ * rc / (a * D) * (1 / (2 * (α / (4 * D)) ^ 2)) =
      rc⁻¹ * (p * σ / 2) * (1 + 17 * σ / (p * a)) := by
  have hl' : l₁ = α / rc ^ 2 := by
    rw [hrc2]; field_simp
  have hD' : D = α * σ ^ 2 := by rw [hσ2]; field_simp
  subst hl' hD'
  field_simp
  ring

/-- **Explicit lower bound for `T_guard`** (source §1.3): for `0 < a < r_c` and `D̃ > 0`,
`(1 − e^{−αa²/(2D̃)}) (1 − √(D̃/α)/(√π (r_c − a))) · P e^X ≤ T_guard`, `P = guardPrefactor`,
`X = ΔU/D̃`. -/
@[powerlib_foundation] theorem guardMFPT_guard_ge (hα : 0 < α) (hl : 0 < l₁) {D a : ℝ}
    (ha : 0 < a) (har : a < √(α / l₁)) (hD : 0 < D) :
    (1 - Real.exp (-(α / (2 * D)) * a ^ 2)) * (1 - √(D / α) / (√π * (√(α / l₁) - a))) *
        (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D)) ≤
      guardMFPT α l₁ D (guardRadius α l₁) := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hrc : 0 < √(α / l₁) := Real.sqrt_pos.mpr hρ
  have hc : 0 < α / D := div_pos hα hD
  have hL : 0 < √(α / l₁) - a := sub_pos.2 har
  have hsπ : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hσ : 0 < √(D / α) := Real.sqrt_pos.mpr (div_pos hD hα)
  have hσ2 : √(D / α) ^ 2 = D / α := Real.sq_sqrt (div_pos hD hα).le
  have hsq : √(π / (α / D)) = √π * √(D / α) := by
    rw [show π / (α / D) = π * (D / α) by field_simp, Real.sqrt_mul Real.pi_pos.le]
  -- `T_guard ≥ D̃⁻¹ K(a) I`
  have hKa := guardInner_ge_gauss (l₁ := l₁) hα hl.le hD ha.le
  have hI := guard_weight_ge_gauss hα hl hD ha har
  obtain ⟨hAm, -⟩ := guard_inside_bounds (α := α) (l₁ := l₁) (D := D) ha har.le
  have hAt0 : 0 ≤ ∫ y in (0 : ℝ)..a, guardIntegrand α l₁ D y :=
    integral_nonneg ha.le fun y hy => guardIntegrand_nonneg hy.1
  have hsplit : ∫ y in (0 : ℝ)..√(α / l₁), guardIntegrand α l₁ D y =
      (∫ y in (0 : ℝ)..a, guardIntegrand α l₁ D y) + ∫ y in a..√(α / l₁), guardIntegrand α l₁ D y :=
    (integral_add_adjacent_intervals (intervalIntegrable_guardIntegrand hl hD ha.le)
      (intervalIntegrable_guardIntegrand_of_pos ha hrc)).symm
  have hE1 : Real.exp (-(α / (2 * D)) * a ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have : 0 ≤ α / (2 * D) * a ^ 2 := by positivity
                                linarith)
  have hk0 : 0 ≤ D / α * (1 - Real.exp (-(α / (2 * D)) * a ^ 2)) :=
    mul_nonneg (by positivity) (by linarith)
  -- the main term
  have hmain : D * (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D)) =
      D / α * ((√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2)) := by
    rw [← mul_assoc, mul_guardPrefactor_eq hα hl hD]; ring
  have hi : (√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) *
      (√(π / (α / D)) / 2 - 1 / (2 * (α / D) * (√(α / l₁) - a))) =
      (√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2) *
        (1 - √(D / α) / (√π * (√(α / l₁) - a))) := by
    rw [hsq]
    obtain ⟨σ, hσdef, hσ2'⟩ : ∃ σ, σ = √(D / α) ∧ σ ^ 2 = D / α := ⟨_, rfl, hσ2⟩
    have hσ0 : 0 < σ := hσdef ▸ hσ
    rw [← hσdef]
    have hD' : D = α * σ ^ 2 := by rw [hσ2']; field_simp
    rw [hD']
    field_simp
  rw [hi] at hI
  generalize hIdef : (∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D)) = I
    at hI hAm
  have hKI : D / α * (1 - Real.exp (-(α / (2 * D)) * a ^ 2)) *
      ((√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2) *
        (1 - √(D / α) / (√π * (√(α / l₁) - a)))) ≤ guardInner α l₁ D a * I := by
    rcases le_or_gt 0 ((√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2) *
        (1 - √(D / α) / (√π * (√(α / l₁) - a)))) with h | h
    · exact mul_le_mul hKa hI h (hk0.trans hKa)
    · have : D / α * (1 - Real.exp (-(α / (2 * D)) * a ^ 2)) *
          ((√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2) *
            (1 - √(D / α) / (√π * (√(α / l₁) - a)))) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk0 h.le
      have : 0 ≤ guardInner α l₁ D a * I := by
        have hI0 : 0 ≤ I := by
          rw [← hIdef]
          exact integral_nonneg har.le fun y hy =>
            mul_nonneg (inv_nonneg.2 (ha.le.trans hy.1)) (Real.exp_pos _).le
        exact mul_nonneg (guardInner_nonneg ha.le) hI0
      linarith
  unfold guardMFPT guardRadius
  rw [hsplit, le_inv_mul_iff₀ hD]
  calc D * ((1 - Real.exp (-(α / (2 * D)) * a ^ 2)) * (1 - √(D / α) / (√π * (√(α / l₁) - a))) *
        (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D)))
      = D / α * (1 - Real.exp (-(α / (2 * D)) * a ^ 2)) *
          ((√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2) *
            (1 - √(D / α) / (√π * (√(α / l₁) - a)))) := by
        rw [show D * ((1 - Real.exp (-(α / (2 * D)) * a ^ 2)) *
          (1 - √(D / α) / (√π * (√(α / l₁) - a))) *
            (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D))) =
          (1 - Real.exp (-(α / (2 * D)) * a ^ 2)) * (1 - √(D / α) / (√π * (√(α / l₁) - a))) *
            (D * (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D))) by ring, hmain]
        ring
    _ ≤ guardInner α l₁ D a * I := hKI
    _ ≤ _ := by linarith

/-- **Explicit upper bound for `T_guard`** (source §1.3): for `0 < a < r_c` and `0 < D̃ ≤ a²`,
`T_guard ≤ (1 + ε)(1 + 16 l₁D̃/α²)(1 + 17√(D̃/α)/(√π a)) · P e^X` with the exponentially small
`ε = guardEps α l₁ a ψ(a) D̃`. -/
@[powerlib_foundation] theorem guardMFPT_guard_le (hα : 0 < α) (hl : 0 < l₁) {D a : ℝ}
    (ha : 0 < a) (har : a < √(α / l₁)) (hD : 0 < D) (hDa : D ≤ a ^ 2) :
    guardMFPT α l₁ D (guardRadius α l₁) ≤
      (1 + guardEps α l₁ a √(2 * (α / l₁) - a ^ 2) D) * (1 + 16 * l₁ * D / α ^ 2) *
        (1 + 17 * √(D / α) / (√π * a)) *
          (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D)) := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hrc : 0 < √(α / l₁) := Real.sqrt_pos.mpr hρ
  have hrc2 : √(α / l₁) ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  have hsπ : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hσ : 0 < √(D / α) := Real.sqrt_pos.mpr (div_pos hD hα)
  have hσ2 : √(D / α) ^ 2 = D / α := Real.sq_sqrt (div_pos hD hα).le
  have hsq : √(π / (α / D)) = √π * √(D / α) := by
    rw [show π / (α / D) = π * (D / α) by field_simp, Real.sqrt_mul Real.pi_pos.le]
  have htails := guard_tails_le (D := D) hα hl ha har le_rfl hD hDa
  rw [intervalIntegral.integral_same, add_zero] at htails
  have heps0 := guardEps_nonneg (D := D) hα hl ha har le_rfl hD
  obtain ⟨-, hAm⟩ := guard_inside_bounds (α := α) (l₁ := l₁) (D := D) ha har.le
  have hKr := guardInner_le_gauss hα hl hD
  have hI := guard_weight_le_gauss hα hl hD ha har
  have hKar : guardInner α l₁ D a ≤ guardInner α l₁ D √(α / l₁) := guardInner_mono ha.le har.le
  have hK0 : 0 ≤ guardInner α l₁ D a := guardInner_nonneg ha.le
  have hI0 : 0 ≤ ∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D) :=
    integral_nonneg har.le fun y hy =>
      mul_nonneg (inv_nonneg.2 (ha.le.trans hy.1)) (Real.exp_pos _).le
  have hiden : Real.exp (barrierHeight α l₁ / D) * ((√(α / l₁))⁻¹ * (√(π / (α / D)) / 2) +
      (a * √(α / l₁))⁻¹ * (1 / (2 * (α / D))) +
        l₁ * √(α / l₁) / (a * D) * (1 / (2 * (α / (4 * D)) ^ 2))) =
      (√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2) *
        (1 + 17 * √(D / α) / (√π * a)) := by
    rw [hsq, weight_upper_identity hα hl hD ha hrc hrc2 hσ hσ2 hsπ]
    ring
  rw [hiden] at hI
  have hsplit : ∫ y in (0 : ℝ)..√(α / l₁), guardIntegrand α l₁ D y =
      (∫ y in (0 : ℝ)..a, guardIntegrand α l₁ D y) + ∫ y in a..√(α / l₁), guardIntegrand α l₁ D y :=
    (integral_add_adjacent_intervals (intervalIntegrable_guardIntegrand hl hD ha.le)
      (intervalIntegrable_guardIntegrand_of_pos ha hrc)).symm
  have hmain : D * (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D)) =
      D / α * ((√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2)) := by
    rw [← mul_assoc, mul_guardPrefactor_eq hα hl hD]; ring
  generalize (∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D)) = I
    at htails hAm hI hI0
  have hk1 : 0 ≤ D / α * (1 + 16 * l₁ * D / α ^ 2) := by positivity
  have hA : (∫ y in (0 : ℝ)..a, guardIntegrand α l₁ D y) +
      ∫ y in a..√(α / l₁), guardIntegrand α l₁ D y ≤
        (1 + guardEps α l₁ a √(2 * (α / l₁) - a ^ 2) D) * (guardInner α l₁ D √(α / l₁) * I) := by
    have h1 : guardEps α l₁ a √(2 * (α / l₁) - a ^ 2) D * (guardInner α l₁ D a * I) ≤
        guardEps α l₁ a √(2 * (α / l₁) - a ^ 2) D * (guardInner α l₁ D √(α / l₁) * I) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKar hI0) heps0
    nlinarith
  have hKI : guardInner α l₁ D √(α / l₁) * I ≤ D / α * (1 + 16 * l₁ * D / α ^ 2) *
      ((√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2) *
        (1 + 17 * √(D / α) / (√π * a))) := mul_le_mul hKr hI hI0 hk1
  unfold guardMFPT guardRadius
  rw [hsplit, inv_mul_le_iff₀ hD]
  calc (∫ y in (0 : ℝ)..a, guardIntegrand α l₁ D y) +
        ∫ y in a..√(α / l₁), guardIntegrand α l₁ D y
      ≤ (1 + guardEps α l₁ a √(2 * (α / l₁) - a ^ 2) D) * (guardInner α l₁ D √(α / l₁) * I) := hA
    _ ≤ (1 + guardEps α l₁ a √(2 * (α / l₁) - a ^ 2) D) * (D / α * (1 + 16 * l₁ * D / α ^ 2) *
          ((√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2) *
            (1 + 17 * √(D / α) / (√π * a)))) :=
        mul_le_mul_of_nonneg_left hKI (by linarith)
    _ = D * ((1 + guardEps α l₁ a √(2 * (α / l₁) - a ^ 2) D) * (1 + 16 * l₁ * D / α ^ 2) *
          (1 + 17 * √(D / α) / (√π * a)) *
            (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D))) := by
        rw [show D * ((1 + guardEps α l₁ a √(2 * (α / l₁) - a ^ 2) D) *
          (1 + 16 * l₁ * D / α ^ 2) * (1 + 17 * √(D / α) / (√π * a)) *
            (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D))) =
          (1 + guardEps α l₁ a √(2 * (α / l₁) - a ^ 2) D) * (1 + 16 * l₁ * D / α ^ 2) *
            (1 + 17 * √(D / α) / (√π * a)) *
              (D * (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D))) by ring, hmain]
        ring

/-- **`T_guard = P e^X (1 + O(√D̃))`** as `D̃ → 0⁺` (source §1.3,
`T_guard ∼ (√π/2) √(D̃ l₁)/α² e^X (1 + O(X^{−1/2}))`), `P = guardPrefactor`, `X = ΔU/D̃`. -/
@[powerlib_foundation] theorem guardMFPT_guard_isBigO (hα : 0 < α) (hl : 0 < l₁) :
    (fun D => guardMFPT α l₁ D (guardRadius α l₁) /
        (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D)) - 1) =O[𝓝[>] 0]
      fun D => √D := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hrc : 0 < √(α / l₁) := Real.sqrt_pos.mpr hρ
  have hrc2 : √(α / l₁) ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  set a := √(α / l₁) / 2 with hadef
  have ha : 0 < a := by positivity
  have har : a < √(α / l₁) := by linarith
  have hL : 0 < √(α / l₁) - a := by linarith
  have hsα : 0 < √α := Real.sqrt_pos.mpr hα
  have hsπ : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hca : 0 < α * a ^ 2 / 2 := by positivity
  have he1 := tendsto_exp_neg_div_div hca
  have hε := tendsto_guardEps_div (rb := √(2 * (α / l₁) - a ^ 2)) hl ha har hρ
  set k₁ := 1 / (√α * √π * (√(α / l₁) - a)) with hk₁
  set k₃ := 17 / (√α * √π * a) with hk₃
  set c₂ := 16 * l₁ / α ^ 2 with hc₂
  have hk₁0 : 0 ≤ k₁ := by positivity
  have hk₃0 : 0 ≤ k₃ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  apply Asymptotics.IsBigO.of_bound ((1 + k₁) + (1 + 2 * c₂ + 2 * k₃ + 2 * c₂ * k₃))
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds (by positivity : (0 : ℝ) < a ^ 2)),
    nhdsWithin_le_nhds (eventually_lt_nhds (one_pos : (0 : ℝ) < 1)),
    he1.eventually (gt_mem_nhds one_pos), hε.eventually (gt_mem_nhds one_pos)]
    with D hD hDa hD1 he1D hεD
  have hD0 : (0 : ℝ) < D := hD
  have hQ : 0 < guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D) := by
    unfold guardPrefactor; positivity
  have hs0 : 0 ≤ √D := Real.sqrt_nonneg D
  have hs2 : √D ^ 2 = D := Real.sq_sqrt hD0.le
  have hs1 : √D ≤ 1 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hD1.le
  have hDs : D ≤ √D := by
    have := pow_le_of_le_one hs0 hs1 two_ne_zero; rwa [hs2] at this
  have hσ : √(D / α) = √D / √α := Real.sqrt_div' D hα.le
  have he1le : Real.exp (-(α / (2 * D)) * a ^ 2) ≤ D := by
    have e : Real.exp (-(α / (2 * D)) * a ^ 2) = Real.exp (-(α * a ^ 2 / 2 / D)) := by
      congr 1; field_simp
    rw [e]
    have := (div_lt_one hD0).1 he1D; linarith
  have hεle : guardEps α l₁ a √(2 * (α / l₁) - a ^ 2) D ≤ D := by
    have := (div_lt_one hD0).1 hεD; linarith
  have hε0 := guardEps_nonneg (D := D) hα hl ha har le_rfl hD0
  have he0 := Real.exp_pos (-(α / (2 * D)) * a ^ 2)
  have hlo := guardMFPT_guard_ge hα hl ha har hD0
  have hhi := guardMFPT_guard_le hα hl ha har hD0 hDa.le
  rw [hσ] at hlo hhi
  have e₁ : √D / √α / (√π * (√(α / l₁) - a)) = k₁ * √D := by
    simp only [hk₁]; field_simp
  have e₃ : 17 * (√D / √α) / (√π * a) = k₃ * √D := by
    simp only [hk₃]; field_simp
  have e₂ : 16 * l₁ * D / α ^ 2 = c₂ * D := by simp only [hc₂]; ring
  rw [e₁] at hlo
  rw [e₃, e₂] at hhi
  generalize guardMFPT α l₁ D (guardRadius α l₁) = T at hlo hhi ⊢
  generalize guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D) = Q at hQ hlo hhi ⊢
  generalize Real.exp (-(α / (2 * D)) * a ^ 2) = e at he1le he0 hlo
  generalize guardEps α l₁ a √(2 * (α / l₁) - a ^ 2) D = ε at hεle hε0 hhi
  generalize √D = s at hs0 hs1 hDs hlo hhi ⊢
  clear_value k₁ k₃ c₂
  have hlo' : (1 - e) * (1 - k₁ * s) ≤ T / Q := by rw [le_div_iff₀ hQ]; exact hlo
  have hhi' : T / Q ≤ (1 + ε) * (1 + c₂ * D) * (1 + k₃ * s) := by rw [div_le_iff₀ hQ]; exact hhi
  have hlo2 : -((1 + k₁) * s) ≤ T / Q - 1 := by
    have h1 : 0 ≤ e * (k₁ * s) := by positivity
    have h2 : (1 - e) * (1 - k₁ * s) = 1 - e - k₁ * s + e * (k₁ * s) := by ring
    have h3 : (1 + k₁) * s = s + k₁ * s := by ring
    linarith
  have hhi2 : T / Q - 1 ≤ (1 + 2 * c₂ + 2 * k₃ + 2 * c₂ * k₃) * s := by
    have h1 : 0 ≤ 1 + c₂ * D := by have := mul_nonneg hc₂0 hD0.le; linarith
    have m1 : (1 + ε) * (1 + c₂ * D) ≤ (1 + s) * (1 + c₂ * s) :=
      mul_le_mul (by linarith) (by linarith [mul_le_mul_of_nonneg_left hDs hc₂0]) h1
        (by linarith)
    have m2 : (1 + ε) * (1 + c₂ * D) * (1 + k₃ * s) ≤ (1 + s) * (1 + c₂ * s) * (1 + k₃ * s) :=
      mul_le_mul_of_nonneg_right m1 (by have := mul_nonneg hk₃0 hs0; linarith)
    have hs2' : s ^ 2 ≤ s := pow_le_of_le_one hs0 hs1 two_ne_zero
    have hs3' : s ^ 3 ≤ s := pow_le_of_le_one hs0 hs1 (by norm_num)
    have expand : (1 + s) * (1 + c₂ * s) * (1 + k₃ * s) = 1 + (1 + c₂ + k₃) * s +
        (c₂ + k₃ + c₂ * k₃) * s ^ 2 + c₂ * k₃ * s ^ 3 := by ring
    have t2 : (c₂ + k₃ + c₂ * k₃) * s ^ 2 ≤ (c₂ + k₃ + c₂ * k₃) * s :=
      mul_le_mul_of_nonneg_left hs2' (by positivity)
    have t3 : c₂ * k₃ * s ^ 3 ≤ c₂ * k₃ * s := mul_le_mul_of_nonneg_left hs3' (by positivity)
    have eR : (1 + 2 * c₂ + 2 * k₃ + 2 * c₂ * k₃) * s =
        (1 + c₂ + k₃) * s + (c₂ + k₃ + c₂ * k₃) * s + c₂ * k₃ * s := by ring
    linarith
  have hB : 0 ≤ (1 + 2 * c₂ + 2 * k₃ + 2 * c₂ * k₃) * s := by positivity
  have hA1 : 0 ≤ (1 + k₁) * s := by positivity
  have eC : ((1 + k₁) + (1 + 2 * c₂ + 2 * k₃ + 2 * c₂ * k₃)) * s =
      (1 + k₁) * s + (1 + 2 * c₂ + 2 * k₃ + 2 * c₂ * k₃) * s := by ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hs0, abs_le, eC]
  constructor <;> linarith

/-- `T_guard / (P e^X) → 1` as `D̃ → 0⁺`. -/
@[powerlib_foundation] theorem tendsto_guardMFPT_guard (hα : 0 < α) (hl : 0 < l₁) :
    Tendsto (fun D => guardMFPT α l₁ D (guardRadius α l₁) /
        (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D))) (𝓝[>] 0) (𝓝 1) := by
  have hs : Tendsto (fun D : ℝ => √D) (𝓝[>] 0) (𝓝 0) := by
    have h := Real.continuous_sqrt.tendsto (0 : ℝ)
    rw [Real.sqrt_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h := ((guardMFPT_guard_isBigO hα hl).trans_tendsto hs).add_const 1
  rw [zero_add] at h
  exact h.congr fun D => by ring

/-- **`T_guard = P e^X (1 + O(X^{−1/2}))`** along `X = ΔU/D̃ → ∞` (source §1.3), with
`P = (√π/2) √(D̃ l₁)/α² = √π/(4α√X)` (`guardPrefactor_eq`). -/
@[powerlib_foundation] theorem guardMFPT_guard_isBigO_atTop (hα : 0 < α) (hl : 0 < l₁) :
    (fun X => guardMFPT α l₁ (barrierHeight α l₁ / X) (guardRadius α l₁) /
        (guardPrefactor α l₁ (barrierHeight α l₁ / X) * Real.exp X) - 1) =O[atTop]
      fun X => (√X)⁻¹ := by
  have hΔ : 0 < barrierHeight α l₁ := by unfold barrierHeight; positivity
  have hD : Tendsto (fun X : ℝ => barrierHeight α l₁ / X) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.div_atTop tendsto_id, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with X hX
    exact div_pos hΔ hX
  have h1 := (guardMFPT_guard_isBigO hα hl).comp_tendsto hD
  have h2 : (fun X => √(barrierHeight α l₁ / X)) =O[atTop] fun X => (√X)⁻¹ := by
    apply Asymptotics.IsBigO.of_bound (√(barrierHeight α l₁))
    filter_upwards [eventually_gt_atTop 0] with X hX
    have hsX : 0 < √X := Real.sqrt_pos.mpr hX
    rw [Real.sqrt_div' _ hX.le, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), div_eq_mul_inv]
  refine (h1.trans h2).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with X hX
  simp only [Function.comp_apply]
  rw [div_div_cancel₀ hΔ.ne']

/-- **`T_committed = 2 P e^X (1 + O(√D̃))`** as `D̃ → 0⁺`, for every committed-escape boundary
`r_b > r_c` (source §1.5, "`× 2` 承诺逃逸"): the product of `guardMFPT_ratio_sub_two_isBigO` and
`guardMFPT_guard_isBigO`. -/
@[powerlib_foundation] theorem guardMFPT_committed_isBigO (hα : 0 < α) (hl : 0 < l₁) {rb : ℝ}
    (hrb : guardRadius α l₁ < rb) :
    (fun D => guardMFPT α l₁ D rb /
        (2 * (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D))) - 1) =O[𝓝[>] 0]
      fun D => √D := by
  have hs : Tendsto (fun D : ℝ => √D) (𝓝[>] 0) (𝓝 0) := by
    have h := Real.continuous_sqrt.tendsto (0 : ℝ)
    rw [Real.sqrt_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hf := guardMFPT_ratio_sub_two_isBigO hα hl hrb
  have hg := guardMFPT_guard_isBigO hα hl
  have hg1 := hg.trans_tendsto_nhds (F := ℝ) hs
  have hfg := (hf.mul hg1).congr_right (fun D => mul_one (√D))
  have hsum := (hg.add (hf.const_mul_left (1 / 2))).add (hfg.const_mul_left (1 / 2))
  refine hsum.congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin,
    (tendsto_guardMFPT_guard hα hl).eventually (lt_mem_nhds (one_pos : (0 : ℝ) < 1))]
    with D hD hTD
  have hD0 : (0 : ℝ) < D := hD
  have hQ : 0 < guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D) := by
    unfold guardPrefactor; positivity
  have hT : guardMFPT α l₁ D (guardRadius α l₁) ≠ 0 := by
    intro h; rw [h, zero_div] at hTD; exact lt_irrefl _ hTD
  generalize guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D) = Q at hQ ⊢
  have hQ0 : Q ≠ 0 := hQ.ne'
  field_simp
  ring

/-- Composition with `D̃ = c/X` (`c > 0`): an `O(√D̃)` bound as `D̃ → 0⁺` is an `O(X^{−1/2})` bound
as `X → ∞`. -/
@[powerlib_foundation] theorem isBigO_comp_div_atTop {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : f =O[𝓝[>] 0] fun D => √D) : (fun X => f (c / X)) =O[atTop] fun X => (√X)⁻¹ := by
  have hD : Tendsto (fun X : ℝ => c / X) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.div_atTop tendsto_id, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with X hX
    exact div_pos hc hX
  have h2 : (fun X => √(c / X)) =O[atTop] fun X => (√X)⁻¹ := by
    apply Asymptotics.IsBigO.of_bound (√c)
    filter_upwards [eventually_gt_atTop 0] with X hX
    have hsX : 0 < √X := Real.sqrt_pos.mpr hX
    rw [Real.sqrt_div' _ hX.le, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), div_eq_mul_inv]
  exact (hf.comp_tendsto hD).trans h2

/-- **`T_committed = 2 P e^X (1 + O(X^{−1/2}))`** along `X = ΔU/D̃ → ∞`. -/
@[powerlib_foundation] theorem guardMFPT_committed_isBigO_atTop (hα : 0 < α) (hl : 0 < l₁)
    {rb : ℝ} (hrb : guardRadius α l₁ < rb) :
    (fun X => guardMFPT α l₁ (barrierHeight α l₁ / X) rb /
        (2 * (guardPrefactor α l₁ (barrierHeight α l₁ / X) * Real.exp X)) - 1) =O[atTop]
      fun X => (√X)⁻¹ := by
  have hΔ : 0 < barrierHeight α l₁ := by unfold barrierHeight; positivity
  refine (isBigO_comp_div_atTop hΔ (guardMFPT_committed_isBigO hα hl hrb)).congr' ?_
    EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with X hX
  rw [div_div_cancel₀ hΔ.ne']

end Guard

end powerlib.Asymptotics
