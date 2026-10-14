import theorem.Asymptotics.Guard.MFPT
import theorem.Asymptotics.LaplaceTwoTerm
import theorem.Asymptotics.EndpointLaplace

/-! # Guard MFPT: the half-order term is present, with coefficient `1/√(πX)`

Foundation layer: one-variable real analysis of the explicit MFPT double integral; nothing here is a
stochastic statement (the integral is taken as the definition of the MFPT, as in the source note).

Model boundary: exactly that of `Asymptotics/Guard/MFPT.lean` — truncated subcritical-Hopf potential
`U(r) = αr²/2 − l₁r⁴/4` (`α, l₁ > 0`), barrier top `r_c = √(α/l₁)`, `ΔU = α²/(4l₁)`,
`T(r_b) = D̃⁻¹ ∫₀^{r_b} (dy/y) e^{U(y)/D̃} ∫₀^y z e^{−U(z)/D̃} dz` (`guardMFPT`),
`T_guard = T(r_c)`,
`T_committed = T(r_b)` with any `r_b > r_c`, `P = guardPrefactor α l₁ D̃ = (√π/2)√(D̃l₁)/α²`,
`X = ΔU/D̃`; asymptotic regime `D̃ → 0⁺` at fixed `α, l₁, r_b` (equivalently `X → ∞`).

Results (`c = 2√l₁/(√π α)`, so that `c √D̃ = 1/√(πX)`):
* `guardMFPT_guard_two_term`: `T_guard/(P e^X) = 1 + c√D̃ + O(D̃)`;
  `tendsto_guardMFPT_guard_sub_one_div_sqrt`: `(T_guard/(P e^X) − 1)/√D̃ → c`;
  `tendsto_guardMFPT_guard_mul_sqrt_atTop`: `√X (T_guard/(P e^X) − 1) → 1/√π`, i.e.
  `T_guard = P e^X (1 + 1/√(πX) + o(X^{−1/2}))`.
* `guardMFPT_beyond_two_term`: `(T(r_b) − T_guard)/(P e^X) = 1 − c√D̃ + O(D̃)`.
* `guardMFPT_ratio_two_term`: `T(r_b)/T(r_c) = 2 − 2c√D̃ + O(D̃)`;
  `tendsto_guardMFPT_ratio_sub_two_div_sqrt`: `(T(r_b)/T(r_c) − 2)/√D̃ → −2c = −4√l₁/(√π α)`;
  `tendsto_guardMFPT_ratio_mul_sqrt_atTop`: `√X (T_committed/T_guard − 2) → −2/√π`, i.e.
  `T_committed/T_guard = 2 (1 − 1/√(πX) + o(X^{−1/2}))`.
* The coefficient is nonzero (`guardHalfOrder_pos`), so the rates `O(√D̃)` of
  `guardMFPT_guard_isBigO` and `guardMFPT_ratio_sub_two_isBigO` are sharp:
  `guardMFPT_guard_sub_one_isTheta`, `guardMFPT_ratio_sub_two_isTheta` (`=Θ(√D̃)`),
  `not_guardMFPT_guard_sub_one_isLittleO`, `not_guardMFPT_ratio_sub_two_isLittleO` (`≠ o(√D̃)`).
  This settles for the integral itself what `Asymptotics/Guard/MFPT.lean` only had from the
  truncated table `endpointCorrection_ne_zero_iff`.
* `guardMFPT_committed_two_term`, `guardMFPT_committed_two_term_atTop`:
  `T_committed = 2 P e^X (1 + O(1/X))` — the half-order terms of the two halves of the barrier peak
  cancel (committed escape integrates the full Gaussian, an interior Laplace integral), so the whole
  half-order term of the ratio comes from `T_guard`. This sharpens the `O(X^{−1/2})` upper bound
  `guardMFPT_committed_isBigO_atTop`; it is consistent with the source (§1.2: "极值成为内点 ⇒ 完整高斯").

Route. Morse substitution `u = y² − r_c²` makes the barrier phase exactly Gaussian, because
`U(y) = ΔU − (l₁/4)(y² − r_c²)²`:
`∫_a^b y⁻¹ e^{U/D̃} dy = (e^X/2) ∫ (r_c² + u)⁻¹ e^{−l₁u²/(4D̃)} du`
(`guard_weight_morse`; inside the top `guard_weight_inside_morse`, amplitude `(r_c² − u)⁻¹`; beyond
it up to the reflected cut `ψ(a) = √(2r_c² − a²)`, `guard_weight_beyond_morse`, amplitude
`(r_c² + u)⁻¹`). The generic two-term endpoint expansion `laplace_two_term_isBigO`
(`Asymptotics/LaplaceTwoTerm.lean`) with `h₀ = r_c⁻²`, `h₁ = ±r_c⁻⁴` (Taylor remainders
`inv_sub_taylor_le`, `inv_add_taylor_le`) and `β = l₁/(4D̃)` gives the two halves of the weight
to `1 ± c√D̃ + O(D̃)` (`guard_weight_inside_two_term`, `guard_weight_beyond_two_term`). The inner
integral and the tails enter only at relative order `O(D̃)`: deterministic sandwiches
`guardMFPT_guard_weight_bounds`, `guardMFPT_beyond_weight_bounds` (from the bounds of
`Asymptotics/Guard/MFPT.lean`: `guardInner_ge_gauss`, `guardInner_le_gauss`, `guard_inside_bounds`,
`guard_tails_le`, `guardInner_reflect_le`). Cross-check with the truncated table
(`guard_endpointCorrection_eq`): in `ξ = r_c − y`, `g₀ = 1/r_c`, `g₁ = 1/r_c²`, `φ₂ = 2α`,
`φ₃ = −6l₁r_c` give `endpointCorrection = 2√l₁/(√π α) = c` (with `X` there `= 1/D̃`).
Generic helpers: `tendsto_guardBeta`, `guardBeta_inv_isBigO`, `guard_weight_lead_eq`,
`guard_weight_coeff_eq`, `mul_guardPrefactor_exp_eq`, `tendsto_div_sqrt_of_isBigO`,
`tendsto_sqrt_mul_comp_div_atTop`, `isBigO_comp_div_atTop_inv`, `sqrt_barrierHeight_mul_halfOrder`.

Source: work-sync theory/T-endpoint-laplace-asymptotics.md §1.2 ("趋近 2 的方式本身是
`1 + O(X^{−1/2})`"), §1.3 (`T_guard ∼ (√π/2)√(D̃l₁)/α² e^X (1 + O(X^{−1/2}))`, "修正确为半阶"),
§1.5 (`× 2` for committed escape).
-/

noncomputable section
namespace powerlib.Asymptotics.Guard

open Real Set Filter Topology MeasureTheory intervalIntegral

variable {α l₁ : ℝ}

/-! ## Morse substitution for the barrier weight -/

/-- Morse substitution `u = y² − r_c²` (`r_c² = α/l₁`): for `0 < a ≤ b`,
`∫_a^b y⁻¹ e^{U(y)/D̃} dy = (e^{ΔU/D̃}/2) ∫_{a²−r_c²}^{b²−r_c²} (r_c² + u)⁻¹ e^{−l₁u²/(4D̃)} du`,
since `U(y) = ΔU − (l₁/4)(y² − r_c²)²` exactly. -/
@[powerlib_foundation] theorem guard_weight_morse (hl : 0 < l₁) {D a b : ℝ} (hD : 0 < D)
    (ha : 0 < a) (hab : a ≤ b) :
    ∫ y in a..b, y⁻¹ * Real.exp (guardPotential α l₁ y / D) =
      Real.exp (barrierHeight α l₁ / D) / 2 *
        ∫ u in (a ^ 2 - α / l₁)..(b ^ 2 - α / l₁),
          (α / l₁ + u)⁻¹ * Real.exp (-(l₁ / (4 * D)) * u ^ 2) := by
  set R := α / l₁ with hR
  set g : ℝ → ℝ := fun u => (R + u)⁻¹ * Real.exp (-(l₁ / (4 * D)) * u ^ 2) with hg
  have hder : ∀ x ∈ uIcc a b, HasDerivAt (fun x => x ^ 2 - R) (2 * x) x := fun x _ => by
    simpa using (hasDerivAt_pow 2 x).sub_const R
  have hcont' : ContinuousOn (fun x : ℝ => 2 * x) (uIcc a b) := by fun_prop
  have hgc : ContinuousOn g ((fun x => x ^ 2 - R) '' uIcc a b) := by
    simp only [hg]
    apply ContinuousOn.mul _ (by fun_prop)
    apply ContinuousOn.inv₀ (by fun_prop)
    rintro _ ⟨x, hx, rfl⟩
    rw [uIcc_of_le hab] at hx
    have : 0 < x := ha.trans_le hx.1
    have e : R + (x ^ 2 - R) = x ^ 2 := by ring
    rw [e]; positivity
  have h := integral_comp_mul_deriv' hder hcont' hgc
  rw [← h, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hab] at hx
  have hx0 : 0 < x := ha.trans_le hx.1
  simp only [Function.comp_apply, hg]
  rw [guardPotential_eq_barrier_sub hl]
  have e : R + (x ^ 2 - R) = x ^ 2 := by ring
  rw [e, show (barrierHeight α l₁ - l₁ / 4 * (x ^ 2 - R) ^ 2) / D =
    barrierHeight α l₁ / D + -(l₁ / (4 * D)) * (x ^ 2 - R) ^ 2 by field_simp; ring, Real.exp_add]
  field_simp

/-- The barrier weight inside the top in Morse form:
`∫_a^{r_c} y⁻¹ e^{U/D̃} = (e^{ΔU/D̃}/2) ∫_0^{r_c² − a²} (r_c² − u)⁻¹ e^{−l₁u²/(4D̃)} du`. -/
@[powerlib_foundation] theorem guard_weight_inside_morse (hα : 0 < α) (hl : 0 < l₁) {D a : ℝ}
    (hD : 0 < D) (ha : 0 < a) (har : a ≤ √(α / l₁)) :
    ∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D) =
      Real.exp (barrierHeight α l₁ / D) / 2 *
        ∫ u in (0 : ℝ)..(α / l₁ - a ^ 2),
          (α / l₁ - u)⁻¹ * Real.exp (-(l₁ / (4 * D)) * u ^ 2) := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  rw [guard_weight_morse hl hD ha har, Real.sq_sqrt hρ.le, sub_self]
  congr 1
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := α / l₁ - a ^ 2)
    (fun u => (α / l₁ + u)⁻¹ * Real.exp (-(l₁ / (4 * D)) * u ^ 2))
  simp only [neg_sq, neg_zero, neg_sub] at h
  rw [← h]
  rfl

/-- The barrier weight just beyond the top in Morse form, up to the reflected cut
`ψ(a) = √(2r_c² − a²)`:
`∫_{r_c}^{ψ(a)} y⁻¹ e^{U/D̃} = (e^{ΔU/D̃}/2) ∫_0^{r_c² − a²} (r_c² + u)⁻¹ e^{−l₁u²/(4D̃)} du`. -/
@[powerlib_foundation] theorem guard_weight_beyond_morse (hα : 0 < α) (hl : 0 < l₁) {D a : ℝ}
    (hD : 0 < D) (har : a ^ 2 ≤ α / l₁) :
    ∫ y in √(α / l₁)..√(2 * (α / l₁) - a ^ 2), y⁻¹ * Real.exp (guardPotential α l₁ y / D) =
      Real.exp (barrierHeight α l₁ / D) / 2 *
        ∫ u in (0 : ℝ)..(α / l₁ - a ^ 2),
          (α / l₁ + u)⁻¹ * Real.exp (-(l₁ / (4 * D)) * u ^ 2) := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  rw [guard_weight_morse hl hD (Real.sqrt_pos.mpr hρ)
    (Real.sqrt_le_sqrt (by linarith)), Real.sq_sqrt hρ.le, Real.sq_sqrt (by linarith), sub_self]
  congr 2
  ring

/-! ## Two-term expansion of the two halves of the barrier weight -/

/-- Taylor remainder of `(R − u)⁻¹` at `u = 0`: `|(R − u)⁻¹ − R⁻¹ − R⁻²u| ≤ R⁻²a⁻²u²` for
`0 ≤ u ≤ R − a²`, `a > 0`. -/
@[powerlib_foundation] theorem inv_sub_taylor_le {R a u : ℝ} (ha : 0 < a)
    (hu : u ∈ Icc 0 (R - a ^ 2)) :
    |(R - u)⁻¹ - R⁻¹ - (R ^ 2)⁻¹ * u| ≤ (R ^ 2)⁻¹ * (a ^ 2)⁻¹ * u ^ 2 := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hRu : a ^ 2 ≤ R - u := by linarith [hu.2]
  have hR : 0 < R := by linarith [hu.1]
  have hRu0 : 0 < R - u := ha2.trans_le hRu
  have e : (R - u)⁻¹ - R⁻¹ - (R ^ 2)⁻¹ * u = u ^ 2 / (R ^ 2 * (R - u)) := by
    field_simp; ring
  rw [e, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  have h1 : 1 ≤ (a ^ 2)⁻¹ * (R - u) := by
    rw [inv_mul_eq_div, le_div_iff₀ ha2]; linarith
  calc u ^ 2 = u ^ 2 * 1 := by ring
    _ ≤ u ^ 2 * ((a ^ 2)⁻¹ * (R - u)) := mul_le_mul_of_nonneg_left h1 (sq_nonneg u)
    _ = (R ^ 2)⁻¹ * (a ^ 2)⁻¹ * u ^ 2 * (R ^ 2 * (R - u)) := by field_simp

/-- Taylor remainder of `(R + u)⁻¹` at `u = 0`: `|(R + u)⁻¹ − R⁻¹ + R⁻²u| ≤ R⁻³u²` for `u ≥ 0`. -/
@[powerlib_foundation] theorem inv_add_taylor_le {R u : ℝ} (hR : 0 < R) (hu : 0 ≤ u) :
    |(R + u)⁻¹ - R⁻¹ - -(R ^ 2)⁻¹ * u| ≤ (R ^ 3)⁻¹ * u ^ 2 := by
  have hRu0 : 0 < R + u := by linarith
  have e : (R + u)⁻¹ - R⁻¹ - -(R ^ 2)⁻¹ * u = u ^ 2 / (R ^ 2 * (R + u)) := by
    field_simp; ring
  rw [e, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  have h1 : 1 ≤ (R ^ 3)⁻¹ * (R ^ 2 * (R + u)) := by
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg R]
  calc u ^ 2 = u ^ 2 * 1 := by ring
    _ ≤ u ^ 2 * ((R ^ 3)⁻¹ * (R ^ 2 * (R + u))) := mul_le_mul_of_nonneg_left h1 (sq_nonneg u)
    _ = (R ^ 3)⁻¹ * u ^ 2 * (R ^ 2 * (R + u)) := by ring

/-- `D̃ ↦ β = l₁/(4D̃)` tends to `+∞` as `D̃ → 0⁺`. -/
@[powerlib_foundation] theorem tendsto_guardBeta (hl : 0 < l₁) :
    Tendsto (fun D : ℝ => l₁ / (4 * D)) (𝓝[>] 0) atTop := by
  refine (tendsto_inv_nhdsGT_zero.const_mul_atTop (by positivity : 0 < l₁ / 4)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with D hD
  have hD0 : (D : ℝ) ≠ 0 := ne_of_gt hD
  field_simp

/-- `(l₁/(4D̃))⁻¹ = O(D̃)`. -/
@[powerlib_foundation] theorem guardBeta_inv_isBigO (hl : 0 < l₁) :
    (fun D : ℝ => (l₁ / (4 * D))⁻¹) =O[𝓝[>] 0] fun D => D := by
  apply Asymptotics.IsBigO.of_bound (4 / l₁)
  filter_upwards [self_mem_nhdsWithin] with D hD
  have hD0 : (0 : ℝ) < D := hD
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_pos hD0]
  apply le_of_eq
  field_simp

/-- The leading weight is the Gaussian main term of the Morse form:
`r_c⁻¹ e^{ΔU/D̃} √(π/(α/D̃))/2 = (e^{ΔU/D̃}/2) · r_c⁻² √(π/β)/2`, `β = l₁/(4D̃)`. -/
@[powerlib_foundation] theorem guard_weight_lead_eq (hα : 0 < α) (hl : 0 < l₁) {D : ℝ}
    (hD : 0 < D) :
    (√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2) =
      Real.exp (barrierHeight α l₁ / D) / 2 * ((α / l₁)⁻¹ * (√(π / (l₁ / (4 * D))) / 2)) := by
  rw [Real.sqrt_div' _ hl.le, Real.sqrt_div' _ (div_pos hα hD).le, Real.sqrt_div' _ hD.le,
    Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ l₁ / (4 * D)), Real.sqrt_div' _ (by positivity),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show √(4 : ℝ) = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  obtain ⟨p, hp, hp2⟩ : ∃ p, p = √α ∧ p ^ 2 = α := ⟨_, rfl, Real.sq_sqrt hα.le⟩
  obtain ⟨q, hq, hq2⟩ : ∃ q, q = √l₁ ∧ q ^ 2 = l₁ := ⟨_, rfl, Real.sq_sqrt hl.le⟩
  have hp0 : 0 < p := hp ▸ Real.sqrt_pos.mpr hα
  have hq0 : 0 < q := hq ▸ Real.sqrt_pos.mpr hl
  have hd0 : 0 < √D := Real.sqrt_pos.mpr hD
  have hsπ : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  rw [← hp, ← hq]
  subst hp2 hq2
  field_simp

/-- The half-order coefficient of the Morse form: `(r_c⁻⁴/r_c⁻²)/√(πβ) = 2√l₁/(√π α) · √D̃`,
`β = l₁/(4D̃)`. -/
@[powerlib_foundation] theorem guard_weight_coeff_eq (hα : 0 < α) (hl : 0 < l₁) {D : ℝ}
    (hD : 0 < D) :
    ((α / l₁) ^ 2)⁻¹ / (α / l₁)⁻¹ / √(π * (l₁ / (4 * D))) = 2 * √l₁ / (√π * α) * √D := by
  rw [Real.sqrt_mul Real.pi_pos.le, Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ 4 * D),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show √(4 : ℝ) = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  obtain ⟨q, hq, hq2⟩ : ∃ q, q = √l₁ ∧ q ^ 2 = l₁ := ⟨_, rfl, Real.sq_sqrt hl.le⟩
  have hq0 : 0 < q := hq ▸ Real.sqrt_pos.mpr hl
  have hd0 : 0 < √D := Real.sqrt_pos.mpr hD
  have hsπ : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  rw [← hq]
  subst hq2
  field_simp

/-- **Two-term expansion of the inside weight** (`D̃ → 0⁺`): for a cut `0 < a < r_c`,
`∫_a^{r_c} y⁻¹ e^{U/D̃} = W(D̃) (1 + c √D̃ + O(D̃))` with the leading weight
`W(D̃) = r_c⁻¹ e^{ΔU/D̃} √(πD̃/α)/2` and `c = 2√l₁/(√π α)`. -/
@[powerlib_foundation] theorem guard_weight_inside_two_term (hα : 0 < α) (hl : 0 < l₁) {a : ℝ}
    (ha : 0 < a) (har : a < √(α / l₁)) :
    (fun D => (∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D)) /
        ((√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2)) - 1 -
        2 * √l₁ / (√π * α) * √D) =O[𝓝[>] 0] fun D => D := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have ha2 : a ^ 2 < α / l₁ := by
    have := pow_lt_pow_left₀ har ha.le two_ne_zero; rwa [Real.sq_sqrt hρ.le] at this
  have hL : 0 < α / l₁ - a ^ 2 := by linarith
  have hcont : ContinuousOn (fun u : ℝ => (α / l₁ - u)⁻¹) (Icc 0 (α / l₁ - a ^ 2)) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro u hu; have := hu.2; have : 0 < a ^ 2 := by positivity
    exact (by linarith : (0 : ℝ) < α / l₁ - u).ne'
  have hO := laplace_two_term_isBigO (h := fun u : ℝ => (α / l₁ - u)⁻¹) (h₀ := (α / l₁)⁻¹)
    (h₁ := ((α / l₁) ^ 2)⁻¹) (M := ((α / l₁) ^ 2)⁻¹ * (a ^ 2)⁻¹) hL (inv_ne_zero hρ.ne') hcont
    (fun u hu => inv_sub_taylor_le ha hu)
  refine ((hO.comp_tendsto (tendsto_guardBeta hl)).trans (guardBeta_inv_isBigO hl)).congr' ?_
    EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with D hD
  have hD0 : (0 : ℝ) < D := hD
  simp only [Function.comp_apply]
  rw [guard_weight_inside_morse hα hl hD0 ha har.le, guard_weight_lead_eq hα hl hD0,
    guard_weight_coeff_eq hα hl hD0, mul_div_mul_left _ _ (by positivity)]

/-- **Two-term expansion of the weight beyond the top** (`D̃ → 0⁺`): for a cut `0 < a < r_c`,
`∫_{r_c}^{ψ(a)} y⁻¹ e^{U/D̃} = W(D̃) (1 − c √D̃ + O(D̃))`, `ψ(a) = √(2r_c² − a²)`; the
half-order term has the opposite sign of the inside one (`guard_weight_inside_two_term`). -/
@[powerlib_foundation] theorem guard_weight_beyond_two_term (hα : 0 < α) (hl : 0 < l₁) {a : ℝ}
    (ha : 0 < a) (har : a < √(α / l₁)) :
    (fun D => (∫ y in √(α / l₁)..√(2 * (α / l₁) - a ^ 2),
          y⁻¹ * Real.exp (guardPotential α l₁ y / D)) /
        ((√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2)) - 1 +
        2 * √l₁ / (√π * α) * √D) =O[𝓝[>] 0] fun D => D := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have ha2 : a ^ 2 < α / l₁ := by
    have := pow_lt_pow_left₀ har ha.le two_ne_zero; rwa [Real.sq_sqrt hρ.le] at this
  have hL : 0 < α / l₁ - a ^ 2 := by linarith
  have hcont : ContinuousOn (fun u : ℝ => (α / l₁ + u)⁻¹) (Icc 0 (α / l₁ - a ^ 2)) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro u hu; have := hu.1
    exact (by linarith : (0 : ℝ) < α / l₁ + u).ne'
  have hO := laplace_two_term_isBigO (h := fun u : ℝ => (α / l₁ + u)⁻¹) (h₀ := (α / l₁)⁻¹)
    (h₁ := -((α / l₁) ^ 2)⁻¹) (M := ((α / l₁) ^ 3)⁻¹) hL (inv_ne_zero hρ.ne') hcont
    (fun u hu => inv_add_taylor_le hρ hu.1)
  refine ((hO.comp_tendsto (tendsto_guardBeta hl)).trans (guardBeta_inv_isBigO hl)).congr' ?_
    EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with D hD
  have hD0 : (0 : ℝ) < D := hD
  simp only [Function.comp_apply]
  rw [guard_weight_beyond_morse hα hl hD0 ha2.le, guard_weight_lead_eq hα hl hD0,
    neg_div, neg_div, guard_weight_coeff_eq hα hl hD0, mul_div_mul_left _ _ (by positivity)]
  ring

/-! ## Deterministic sandwiches by the normalized weights -/

/-- `D̃ · P e^{ΔU/D̃} = (D̃/α) W(D̃)`, `W(D̃) = r_c⁻¹ e^{ΔU/D̃} √(π/(α/D̃))/2`
(`mul_guardPrefactor_eq`). -/
@[powerlib_foundation] theorem mul_guardPrefactor_exp_eq (hα : 0 < α) (hl : 0 < l₁) {D : ℝ}
    (hD : 0 < D) :
    D * (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D)) =
      D / α * ((√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2)) := by
  rw [← mul_assoc, mul_guardPrefactor_eq hα hl hD]; ring

/-- **Sandwich of `T_guard`** by the normalized inside weight
`w = ∫_a^{r_c} y⁻¹ e^{U/D̃} / W(D̃)`: for `0 < a < r_c` and `0 < D̃ ≤ a²`,
`(1 − e^{−αa²/(2D̃)}) w ≤ T_guard/(P e^X) ≤ (1 + ε)(1 + 16 l₁D̃/α²) w`,
`ε = guardEps α l₁ a ψ(a) D̃`. -/
@[powerlib_foundation] theorem guardMFPT_guard_weight_bounds (hα : 0 < α) (hl : 0 < l₁) {D a : ℝ}
    (ha : 0 < a) (har : a < √(α / l₁)) (hD : 0 < D) (hDa : D ≤ a ^ 2) :
    (1 - Real.exp (-(α / (2 * D)) * a ^ 2)) *
        ((∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D)) /
          ((√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2))) ≤
        guardMFPT α l₁ D (guardRadius α l₁) /
          (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D)) ∧
      guardMFPT α l₁ D (guardRadius α l₁) /
          (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D)) ≤
        (1 + guardEps α l₁ a √(2 * (α / l₁) - a ^ 2) D) * (1 + 16 * l₁ * D / α ^ 2) *
          ((∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D)) /
            ((√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2))) := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hrc : 0 < √(α / l₁) := Real.sqrt_pos.mpr hρ
  have hW : 0 < (√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2) := by
    have : 0 < √(π / (α / D)) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have hQ : 0 < guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D) := by
    unfold guardPrefactor; positivity
  have hDQ := mul_guardPrefactor_exp_eq hα hl hD
  have htails := guard_tails_le (D := D) hα hl ha har le_rfl hD hDa
  rw [intervalIntegral.integral_same, add_zero] at htails
  have heps0 := guardEps_nonneg (D := D) hα hl ha har le_rfl hD
  obtain ⟨hAm_lo, hAm_hi⟩ := guard_inside_bounds (α := α) (l₁ := l₁) (D := D) ha har.le
  have hKa := guardInner_ge_gauss (l₁ := l₁) hα hl.le hD ha.le
  have hKr := guardInner_le_gauss hα hl hD
  have hKar : guardInner α l₁ D a ≤ guardInner α l₁ D √(α / l₁) := guardInner_mono ha.le har.le
  have hI0 : 0 ≤ ∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D) :=
    integral_nonneg har.le fun y hy =>
      mul_nonneg (inv_nonneg.2 (ha.le.trans hy.1)) (Real.exp_pos _).le
  have hAt0 : 0 ≤ ∫ y in (0 : ℝ)..a, guardIntegrand α l₁ D y :=
    integral_nonneg ha.le fun y hy => guardIntegrand_nonneg hy.1
  have hsplit : ∫ y in (0 : ℝ)..√(α / l₁), guardIntegrand α l₁ D y =
      (∫ y in (0 : ℝ)..a, guardIntegrand α l₁ D y) + ∫ y in a..√(α / l₁), guardIntegrand α l₁ D y :=
    (integral_add_adjacent_intervals (intervalIntegrable_guardIntegrand hl hD ha.le)
      (intervalIntegrable_guardIntegrand_of_pos ha hrc)).symm
  have hT : guardMFPT α l₁ D (guardRadius α l₁) /
      (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D)) =
      ((∫ y in (0 : ℝ)..a, guardIntegrand α l₁ D y) +
        ∫ y in a..√(α / l₁), guardIntegrand α l₁ D y) /
        (D / α * ((√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2))) := by
    rw [← hDQ, guardMFPT, guardRadius, hsplit]
    field_simp
  rw [hT]
  generalize (√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2) = W
    at hW ⊢
  generalize (∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D)) = I
    at htails hAm_lo hAm_hi hI0 ⊢
  generalize (∫ y in (0 : ℝ)..a, guardIntegrand α l₁ D y) = At at htails hAt0 ⊢
  generalize (∫ y in a..√(α / l₁), guardIntegrand α l₁ D y) = Am at hAm_lo hAm_hi ⊢
  generalize guardEps α l₁ a √(2 * (α / l₁) - a ^ 2) D = ε at htails heps0 ⊢
  generalize guardInner α l₁ D a = Ka at hAm_lo hKa hKar htails
  generalize guardInner α l₁ D √(α / l₁) = Kr at hAm_hi hKr hKar
  have hDα : 0 < D / α := by positivity
  have hDW : 0 < D / α * W := by positivity
  have he1 : Real.exp (-(α / (2 * D)) * a ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have : 0 ≤ α / (2 * D) * a ^ 2 := by positivity
                                linarith)
  constructor
  · rw [le_div_iff₀ hDW]
    have h1 : D / α * (1 - Real.exp (-(α / (2 * D)) * a ^ 2)) * I ≤ Ka * I :=
      mul_le_mul_of_nonneg_right hKa hI0
    have e : (1 - Real.exp (-(α / (2 * D)) * a ^ 2)) * (I / W) * (D / α * W) =
        D / α * (1 - Real.exp (-(α / (2 * D)) * a ^ 2)) * I := by
      field_simp
    rw [e]; linarith
  · rw [div_le_iff₀ hDW]
    have h1 : ε * (Ka * I) ≤ ε * (Kr * I) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKar hI0) heps0
    have h2 : (1 + ε) * (Kr * I) ≤ (1 + ε) * (D / α * (1 + 16 * l₁ * D / α ^ 2) * I) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKr hI0) (by linarith)
    have e : (1 + ε) * (1 + 16 * l₁ * D / α ^ 2) * (I / W) * (D / α * W) =
        (1 + ε) * (D / α * (1 + 16 * l₁ * D / α ^ 2) * I) := by
      field_simp
    rw [e]; nlinarith

/-- **Sandwich of the beyond-top part** `T(r_b) − T_guard` by the normalized weights
`w = ∫_a^{r_c} y⁻¹ e^{U/D̃} / W(D̃)` and `w' = ∫_{r_c}^{ψ(a)} y⁻¹ e^{U/D̃} / W(D̃)`: for
`0 < a < r_c`, `ψ(a) ≤ r_b` and `0 < D̃ ≤ a²`,
`(1 − e^{−αa²/(2D̃)}) w' ≤ (T(r_b) − T_guard)/(P e^X) ≤
(1 + κ)(1 + 16l₁D̃/α²) w' + ε (1 + 16l₁D̃/α²) w`,
`κ = guardKappa α l₁ a D̃`, `ε = guardEps α l₁ a r_b D̃`. -/
@[powerlib_foundation] theorem guardMFPT_beyond_weight_bounds (hα : 0 < α) (hl : 0 < l₁)
    {D a rb : ℝ} (ha : 0 < a) (har : a < √(α / l₁)) (hψ : √(2 * (α / l₁) - a ^ 2) ≤ rb)
    (hD : 0 < D) (hDa : D ≤ a ^ 2) :
    (1 - Real.exp (-(α / (2 * D)) * a ^ 2)) *
        ((∫ y in √(α / l₁)..√(2 * (α / l₁) - a ^ 2),
            y⁻¹ * Real.exp (guardPotential α l₁ y / D)) /
          ((√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2))) ≤
        (guardMFPT α l₁ D rb - guardMFPT α l₁ D (guardRadius α l₁)) /
          (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D)) ∧
      (guardMFPT α l₁ D rb - guardMFPT α l₁ D (guardRadius α l₁)) /
          (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D)) ≤
        (1 + guardKappa α l₁ a D) * (1 + 16 * l₁ * D / α ^ 2) *
          ((∫ y in √(α / l₁)..√(2 * (α / l₁) - a ^ 2),
              y⁻¹ * Real.exp (guardPotential α l₁ y / D)) /
            ((√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2))) +
        guardEps α l₁ a rb D * (1 + 16 * l₁ * D / α ^ 2) *
          ((∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D)) /
            ((√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2))) := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hrc : 0 < √(α / l₁) := Real.sqrt_pos.mpr hρ
  have hrc2 : √(α / l₁) ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  have ha2 : a ^ 2 < α / l₁ := by
    have := pow_lt_pow_left₀ har ha.le two_ne_zero; rwa [hrc2] at this
  have hrcψ : √(α / l₁) ≤ √(2 * (α / l₁) - a ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have hψ0 : 0 < √(2 * (α / l₁) - a ^ 2) := hrc.trans_le hrcψ
  have hW : 0 < (√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2) := by
    have : 0 < √(π / (α / D)) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have hDQ := mul_guardPrefactor_exp_eq hα hl hD
  have htails := guard_tails_le (D := D) hα hl ha har hψ hD hDa
  have heps0 := guardEps_nonneg (D := D) hα hl ha har hψ hD
  have hkap0 := guardKappa_nonneg (D := D) hα hl ha har hD
  have hkap := guardInner_reflect_le (D := D) hα hl ha har hD hDa
  obtain ⟨hBm_lo, hBm_hi⟩ := guard_inside_bounds (α := α) (l₁ := l₁) (D := D) hrc hrcψ
  have hKa := guardInner_ge_gauss (l₁ := l₁) hα hl.le hD ha.le
  have hKr := guardInner_le_gauss hα hl hD
  have hKar : guardInner α l₁ D a ≤ guardInner α l₁ D √(α / l₁) := guardInner_mono ha.le har.le
  have hI0 : 0 ≤ ∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D) :=
    integral_nonneg har.le fun y hy =>
      mul_nonneg (inv_nonneg.2 (ha.le.trans hy.1)) (Real.exp_pos _).le
  have hI'0 : 0 ≤ ∫ y in √(α / l₁)..√(2 * (α / l₁) - a ^ 2),
      y⁻¹ * Real.exp (guardPotential α l₁ y / D) :=
    integral_nonneg hrcψ fun y hy =>
      mul_nonneg (inv_nonneg.2 (hrc.le.trans hy.1)) (Real.exp_pos _).le
  have hAt0 : 0 ≤ ∫ y in (0 : ℝ)..a, guardIntegrand α l₁ D y :=
    integral_nonneg ha.le fun y hy => guardIntegrand_nonneg hy.1
  have hBt0 : 0 ≤ ∫ y in √(2 * (α / l₁) - a ^ 2)..rb, guardIntegrand α l₁ D y :=
    integral_nonneg hψ fun y hy => guardIntegrand_nonneg (hψ0.le.trans hy.1)
  have hT : (guardMFPT α l₁ D rb - guardMFPT α l₁ D (guardRadius α l₁)) /
      (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D)) =
      ((∫ y in √(α / l₁)..√(2 * (α / l₁) - a ^ 2), guardIntegrand α l₁ D y) +
        ∫ y in √(2 * (α / l₁) - a ^ 2)..rb, guardIntegrand α l₁ D y) /
        (D / α * ((√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2))) := by
    rw [← hDQ, guardMFPT, guardMFPT, guardRadius,
      ← integral_add_adjacent_intervals (intervalIntegrable_guardIntegrand hl hD hrc.le)
        (intervalIntegrable_guardIntegrand_of_pos hrc (hrc.trans_le (hrcψ.trans hψ))),
      ← integral_add_adjacent_intervals (intervalIntegrable_guardIntegrand_of_pos hrc hψ0)
        (intervalIntegrable_guardIntegrand_of_pos hψ0 (hψ0.trans_le hψ))]
    field_simp
    ring
  rw [hT]
  generalize (√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2) = W
    at hW ⊢
  generalize (∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D)) = I
    at htails hI0 ⊢
  generalize (∫ y in √(α / l₁)..√(2 * (α / l₁) - a ^ 2),
    y⁻¹ * Real.exp (guardPotential α l₁ y / D)) = I' at hBm_lo hBm_hi hI'0 ⊢
  generalize (∫ y in (0 : ℝ)..a, guardIntegrand α l₁ D y) = At at htails hAt0
  generalize (∫ y in √(α / l₁)..√(2 * (α / l₁) - a ^ 2), guardIntegrand α l₁ D y) = Bm
    at hBm_lo hBm_hi ⊢
  generalize (∫ y in √(2 * (α / l₁) - a ^ 2)..rb, guardIntegrand α l₁ D y) = Bt
    at htails hBt0 ⊢
  generalize guardEps α l₁ a rb D = ε at htails heps0 ⊢
  generalize guardKappa α l₁ a D = κ at hkap hkap0 ⊢
  generalize guardInner α l₁ D a = Ka at hKa hKar htails hkap
  generalize guardInner α l₁ D √(α / l₁) = Kr at hBm_lo hKr hKar
  generalize guardInner α l₁ D √(2 * (α / l₁) - a ^ 2) = Kψ at hBm_hi hkap
  have hDα : 0 < D / α := by positivity
  have hDW : 0 < D / α * W := by positivity
  have hc2 : 0 ≤ 16 * l₁ * D / α ^ 2 := by positivity
  constructor
  · rw [le_div_iff₀ hDW]
    have h1 : D / α * (1 - Real.exp (-(α / (2 * D)) * a ^ 2)) * I' ≤ Kr * I' :=
      mul_le_mul_of_nonneg_right (hKa.trans hKar) hI'0
    have e : (1 - Real.exp (-(α / (2 * D)) * a ^ 2)) * (I' / W) * (D / α * W) =
        D / α * (1 - Real.exp (-(α / (2 * D)) * a ^ 2)) * I' := by
      field_simp
    rw [e]; linarith
  · rw [div_le_iff₀ hDW]
    have hKψ : Kψ ≤ (1 + κ) * (D / α * (1 + 16 * l₁ * D / α ^ 2)) :=
      hkap.trans (mul_le_mul_of_nonneg_left (hKar.trans hKr) (by linarith))
    have h1 : Kψ * I' ≤ (1 + κ) * (D / α * (1 + 16 * l₁ * D / α ^ 2)) * I' :=
      mul_le_mul_of_nonneg_right hKψ hI'0
    have h2 : Bt ≤ ε * (D / α * (1 + 16 * l₁ * D / α ^ 2) * I) := by
      have : ε * (Ka * I) ≤ ε * (D / α * (1 + 16 * l₁ * D / α ^ 2) * I) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hKar.trans hKr) hI0) heps0
      linarith
    have e : ((1 + κ) * (1 + 16 * l₁ * D / α ^ 2) * (I' / W) +
        ε * (1 + 16 * l₁ * D / α ^ 2) * (I / W)) * (D / α * W) =
        (1 + κ) * (D / α * (1 + 16 * l₁ * D / α ^ 2)) * I' +
          ε * (D / α * (1 + 16 * l₁ * D / α ^ 2) * I) := by
      field_simp
    rw [e]; linarith

/-! ## Two-term expansions of `T_guard`, of the part beyond the top and of `T_committed` -/

/-- Real-inequality core of `guardMFPT_guard_two_term`. -/
@[powerlib_foundation] private theorem guard_two_term_core {G w e ε c s C c₂ D : ℝ} (hD0 : 0 < D)
    (hD1 : D ≤ 1) (hs1 : s ≤ 1) (hc0 : 0 ≤ c) (hc₂0 : 0 ≤ c₂) (he : e ≤ D) (hε0 : 0 ≤ ε)
    (hε : ε ≤ D) (hw0 : 0 ≤ w) (hw : |w - 1 - c * s| ≤ C * D)
    (hlo : (1 - e) * w ≤ G) (hhi : G ≤ (1 + ε) * (1 + c₂ * D) * w) :
    |G - 1 - c * s| ≤ (|C| + (1 + 2 * c₂) * (1 + c + |C|)) * D := by
  have hCD : C * D ≤ |C| * D := mul_le_mul_of_nonneg_right (le_abs_self C) hD0.le
  have hCD1 : |C| * D ≤ |C| := by
    have := mul_le_mul_of_nonneg_left hD1 (abs_nonneg C); linarith
  have hcs : c * s ≤ c := by have := mul_le_mul_of_nonneg_left hs1 hc0; linarith
  rw [abs_le] at hw
  have hwb : w ≤ 1 + c + |C| := by linarith [hw.2]
  have h1 : e * w ≤ D * (1 + c + |C|) := mul_le_mul he hwb hw0 hD0.le
  have hk : ε + c₂ * D + ε * (c₂ * D) ≤ (1 + 2 * c₂) * D := by
    have : ε * (c₂ * D) ≤ 1 * (c₂ * D) :=
      mul_le_mul_of_nonneg_right (hε.trans hD1) (by positivity)
    nlinarith
  have hk0 : 0 ≤ ε + c₂ * D + ε * (c₂ * D) := by positivity
  have h2 : (ε + c₂ * D + ε * (c₂ * D)) * w ≤ (1 + 2 * c₂) * D * (1 + c + |C|) :=
    mul_le_mul hk hwb hw0 (by positivity)
  have eh : (1 + ε) * (1 + c₂ * D) * w = w + (ε + c₂ * D + ε * (c₂ * D)) * w := by ring
  have hB : 0 ≤ (1 + 2 * c₂) * D * (1 + c + |C|) := by positivity
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- Real-inequality core of `guardMFPT_beyond_two_term`. -/
@[powerlib_foundation] private theorem beyond_two_term_core {B w w' e κ ε c s C C' c₂ D : ℝ}
    (hD0 : 0 < D) (hD1 : D ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hc0 : 0 ≤ c) (hc₂0 : 0 ≤ c₂)
    (he : e ≤ D) (hκ0 : 0 ≤ κ) (hκ : κ ≤ D) (hε : ε ≤ D)
    (hw0 : 0 ≤ w) (hw'0 : 0 ≤ w') (hw : |w - 1 - c * s| ≤ C * D)
    (hw' : |w' - 1 + c * s| ≤ C' * D) (hlo : (1 - e) * w' ≤ B)
    (hhi : B ≤ (1 + κ) * (1 + c₂ * D) * w' + ε * (1 + c₂ * D) * w) :
    |B - 1 + c * s| ≤
      (|C'| + (1 + 2 * c₂) * (1 + c + |C'|) + (1 + c₂) * (1 + c + |C|)) * D := by
  have hCD' : C' * D ≤ |C'| * D := mul_le_mul_of_nonneg_right (le_abs_self C') hD0.le
  have hCD1 : |C| * D ≤ |C| := by
    have := mul_le_mul_of_nonneg_left hD1 (abs_nonneg C); linarith
  have hCD1' : |C'| * D ≤ |C'| := by
    have := mul_le_mul_of_nonneg_left hD1 (abs_nonneg C'); linarith
  have hCD : C * D ≤ |C| * D := mul_le_mul_of_nonneg_right (le_abs_self C) hD0.le
  have hcs : c * s ≤ c := by have := mul_le_mul_of_nonneg_left hs1 hc0; linarith
  have hcs0 : 0 ≤ c * s := mul_nonneg hc0 hs0
  rw [abs_le] at hw hw'
  have hwb : w ≤ 1 + c + |C| := by linarith [hw.2]
  have hwb' : w' ≤ 1 + c + |C'| := by linarith [hw'.2]
  have h1 : e * w' ≤ D * (1 + c + |C'|) := mul_le_mul he hwb' hw'0 hD0.le
  have hk : κ + c₂ * D + κ * (c₂ * D) ≤ (1 + 2 * c₂) * D := by
    have : κ * (c₂ * D) ≤ 1 * (c₂ * D) :=
      mul_le_mul_of_nonneg_right (hκ.trans hD1) (by positivity)
    nlinarith
  have hk0 : 0 ≤ κ + c₂ * D + κ * (c₂ * D) := by positivity
  have h2 : (κ + c₂ * D + κ * (c₂ * D)) * w' ≤ (1 + 2 * c₂) * D * (1 + c + |C'|) :=
    mul_le_mul hk hwb' hw'0 (by positivity)
  have hk2 : ε * (1 + c₂ * D) ≤ D * (1 + c₂) := by
    have : c₂ * D ≤ c₂ := by have := mul_le_mul_of_nonneg_left hD1 hc₂0; linarith
    have : 0 ≤ 1 + c₂ * D := by positivity
    calc ε * (1 + c₂ * D) ≤ D * (1 + c₂ * D) := mul_le_mul_of_nonneg_right hε this
      _ ≤ D * (1 + c₂) := mul_le_mul_of_nonneg_left (by linarith) hD0.le
  have h3 : ε * (1 + c₂ * D) * w ≤ D * (1 + c₂) * (1 + c + |C|) :=
    mul_le_mul hk2 hwb hw0 (by positivity)
  have eh : (1 + κ) * (1 + c₂ * D) * w' = w' + (κ + c₂ * D + κ * (c₂ * D)) * w' := by ring
  have hB1 : 0 ≤ (1 + 2 * c₂) * D * (1 + c + |C'|) := by positivity
  have hB2 : 0 ≤ D * (1 + c₂) * (1 + c + |C|) := by positivity
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- **Two-term expansion of `T_guard`** (source §1.3): as `D̃ → 0⁺`,
`T_guard/(P e^X) = 1 + c √D̃ + O(D̃)` with `c = 2√l₁/(√π α)`, `P = guardPrefactor`, `X = ΔU/D̃`;
equivalently `T_guard = P e^X (1 + 1/√(πX) + O(1/X))` (`tendsto_guardMFPT_guard_mul_sqrt_atTop`).
The half-order term is the endpoint effect of stopping the outer integral at the barrier top: in
the Morse variable `u = r_c² − y²` the weight is `(e^X/2) ∫ (r_c² − u)⁻¹ e^{−l₁u²/(4D̃)} du`
(`guard_weight_inside_morse`), whose amplitude has slope `r_c⁻⁴ ≠ 0`; the inner integral and the
tails contribute only `O(D̃)` (`guardMFPT_guard_weight_bounds`). -/
@[powerlib_foundation] theorem guardMFPT_guard_two_term (hα : 0 < α) (hl : 0 < l₁) :
    (fun D => guardMFPT α l₁ D (guardRadius α l₁) /
        (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D)) - 1 -
        2 * √l₁ / (√π * α) * √D) =O[𝓝[>] 0] fun D => D := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hrc : 0 < √(α / l₁) := Real.sqrt_pos.mpr hρ
  set a := √(α / l₁) / 2 with hadef
  have ha : 0 < a := by positivity
  have har : a < √(α / l₁) := by linarith
  have hca : 0 < α * a ^ 2 / 2 := by positivity
  have he1 := tendsto_exp_neg_div_div hca
  have hε := tendsto_guardEps_div (rb := √(2 * (α / l₁) - a ^ 2)) hl ha har hρ
  obtain ⟨C, hC⟩ := (guard_weight_inside_two_term hα hl ha har).bound
  have hc0 : 0 ≤ 2 * √l₁ / (√π * α) := by positivity
  have hc₂0 : 0 ≤ 16 * l₁ / α ^ 2 := by positivity
  apply Asymptotics.IsBigO.of_bound (|C| + (1 + 2 * (16 * l₁ / α ^ 2)) *
    (1 + 2 * √l₁ / (√π * α) + |C|))
  filter_upwards [hC, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds (by positivity : (0 : ℝ) < a ^ 2)),
    nhdsWithin_le_nhds (eventually_lt_nhds (one_pos : (0 : ℝ) < 1)),
    he1.eventually (gt_mem_nhds one_pos), hε.eventually (gt_mem_nhds one_pos)]
    with D hCD hD hDa hD1 he1D hεD
  have hD0 : (0 : ℝ) < D := hD
  obtain ⟨hlo, hhi⟩ := guardMFPT_guard_weight_bounds hα hl ha har hD0 hDa.le
  have he1le : Real.exp (-(α / (2 * D)) * a ^ 2) ≤ D := by
    have e : Real.exp (-(α / (2 * D)) * a ^ 2) = Real.exp (-(α * a ^ 2 / 2 / D)) := by
      congr 1; field_simp
    rw [e]
    have := (div_lt_one hD0).1 he1D; linarith
  have hεle : guardEps α l₁ a √(2 * (α / l₁) - a ^ 2) D ≤ D := by
    have := (div_lt_one hD0).1 hεD; linarith
  have hε0 := guardEps_nonneg (D := D) hα hl ha har le_rfl hD0
  have hs0 : 0 ≤ √D := Real.sqrt_nonneg D
  have hs1 : √D ≤ 1 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hD1.le
  have hW : 0 < (√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2) := by
    have : 0 < √(π / (α / D)) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have hw0 : 0 ≤ (∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D)) /
      ((√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2)) :=
    div_nonneg (integral_nonneg har.le fun y hy =>
      mul_nonneg (inv_nonneg.2 (ha.le.trans hy.1)) (Real.exp_pos _).le) hW.le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hD0] at hCD ⊢
  rw [show 16 * l₁ * D / α ^ 2 = 16 * l₁ / α ^ 2 * D by ring] at hhi
  exact guard_two_term_core hD0 hD1.le hs1 hc0 hc₂0 he1le hε0 hεle hw0
    (by simpa only [sub_sub] using hCD) hlo hhi

/-- **Two-term expansion of the part beyond the top** (`D̃ → 0⁺`), for every committed-escape
boundary `r_b > r_c`: `(T(r_b) − T_guard)/(P e^X) = 1 − c √D̃ + O(D̃)`, `c = 2√l₁/(√π α)`. The
half-order term has the sign opposite to that of `T_guard` (`guardMFPT_guard_two_term`): beyond the
top the Morse amplitude is `(r_c² + u)⁻¹`, with slope `−r_c⁻⁴` (`guard_weight_beyond_two_term`). -/
@[powerlib_foundation] theorem guardMFPT_beyond_two_term (hα : 0 < α) (hl : 0 < l₁) {rb : ℝ}
    (hrb : guardRadius α l₁ < rb) :
    (fun D => (guardMFPT α l₁ D rb - guardMFPT α l₁ D (guardRadius α l₁)) /
        (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D)) - 1 +
        2 * √l₁ / (√π * α) * √D) =O[𝓝[>] 0] fun D => D := by
  have hρ : 0 < α / l₁ := div_pos hα hl
  have hrc2 : √(α / l₁) ^ 2 = α / l₁ := Real.sq_sqrt hρ.le
  obtain ⟨a, ha, har, hψ, -⟩ := guard_exists_cut hα hl hrb (t := 0) one_pos
  have ha2 : a ^ 2 < α / l₁ := by
    have := pow_lt_pow_left₀ har ha.le two_ne_zero; rwa [hrc2] at this
  have hca : 0 < α * a ^ 2 / 2 := by positivity
  have he1 := tendsto_exp_neg_div_div hca
  have hε := tendsto_guardEps_div (rb := rb) hl ha har hρ
  have hκ := tendsto_guardKappa_div (α := α) hl ha (by linarith)
  obtain ⟨C, hC⟩ := (guard_weight_inside_two_term hα hl ha har).bound
  obtain ⟨C', hC'⟩ := (guard_weight_beyond_two_term hα hl ha har).bound
  have hc0 : 0 ≤ 2 * √l₁ / (√π * α) := by positivity
  have hc₂0 : 0 ≤ 16 * l₁ / α ^ 2 := by positivity
  apply Asymptotics.IsBigO.of_bound (|C'| + (1 + 2 * (16 * l₁ / α ^ 2)) *
    (1 + 2 * √l₁ / (√π * α) + |C'|) + (1 + 16 * l₁ / α ^ 2) * (1 + 2 * √l₁ / (√π * α) + |C|))
  filter_upwards [hC, hC', self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds (by positivity : (0 : ℝ) < a ^ 2)),
    nhdsWithin_le_nhds (eventually_lt_nhds (one_pos : (0 : ℝ) < 1)),
    he1.eventually (gt_mem_nhds one_pos), hε.eventually (gt_mem_nhds one_pos),
    hκ.eventually (gt_mem_nhds one_pos)]
    with D hCD hCD' hD hDa hD1 he1D hεD hκD
  have hD0 : (0 : ℝ) < D := hD
  obtain ⟨hlo, hhi⟩ := guardMFPT_beyond_weight_bounds hα hl ha har hψ hD0 hDa.le
  have he1le : Real.exp (-(α / (2 * D)) * a ^ 2) ≤ D := by
    have e : Real.exp (-(α / (2 * D)) * a ^ 2) = Real.exp (-(α * a ^ 2 / 2 / D)) := by
      congr 1; field_simp
    rw [e]
    have := (div_lt_one hD0).1 he1D; linarith
  have hεle : guardEps α l₁ a rb D ≤ D := by
    have := (div_lt_one hD0).1 hεD; linarith
  have hκle : guardKappa α l₁ a D ≤ D := by
    have := (div_lt_one hD0).1 hκD; linarith
  have hκ0 := guardKappa_nonneg (D := D) hα hl ha har hD0
  have hs0 : 0 ≤ √D := Real.sqrt_nonneg D
  have hs1 : √D ≤ 1 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hD1.le
  have hρ' : 0 < α / l₁ := hρ
  have hrc : 0 < √(α / l₁) := Real.sqrt_pos.mpr hρ'
  have hrcψ : √(α / l₁) ≤ √(2 * (α / l₁) - a ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have hW : 0 < (√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2) := by
    have : 0 < √(π / (α / D)) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have hw0 : 0 ≤ (∫ y in a..√(α / l₁), y⁻¹ * Real.exp (guardPotential α l₁ y / D)) /
      ((√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2)) :=
    div_nonneg (integral_nonneg har.le fun y hy =>
      mul_nonneg (inv_nonneg.2 (ha.le.trans hy.1)) (Real.exp_pos _).le) hW.le
  have hw'0 : 0 ≤ (∫ y in √(α / l₁)..√(2 * (α / l₁) - a ^ 2),
      y⁻¹ * Real.exp (guardPotential α l₁ y / D)) /
      ((√(α / l₁))⁻¹ * Real.exp (barrierHeight α l₁ / D) * (√(π / (α / D)) / 2)) :=
    div_nonneg (integral_nonneg hrcψ fun y hy =>
      mul_nonneg (inv_nonneg.2 (hrc.le.trans hy.1)) (Real.exp_pos _).le) hW.le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hD0] at hCD hCD' ⊢
  rw [show 16 * l₁ * D / α ^ 2 = 16 * l₁ / α ^ 2 * D by ring] at hhi
  exact beyond_two_term_core hD0 hD1.le hs0 hs1 hc0 hc₂0 he1le hκ0 hκle hεle hw0 hw'0
    (by simpa only [sub_sub] using hCD) hCD' hlo hhi

/-- **`T_committed` has no half-order term**: for every committed-escape boundary `r_b > r_c`,
`T_committed/(2 P e^X) = 1 + O(D̃)` as `D̃ → 0⁺`, i.e. `T_committed = 2 P e^X (1 + O(1/X))`. The
half-order terms `± c √D̃` of the two halves of the barrier peak cancel: committed escape integrates
the full Gaussian, an interior Laplace integral. This sharpens `guardMFPT_committed_isBigO`. -/
@[powerlib_foundation] theorem guardMFPT_committed_two_term (hα : 0 < α) (hl : 0 < l₁) {rb : ℝ}
    (hrb : guardRadius α l₁ < rb) :
    (fun D => guardMFPT α l₁ D rb /
        (2 * (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D))) - 1) =O[𝓝[>] 0]
      fun D => D := by
  have h := ((guardMFPT_guard_two_term hα hl).add
    (guardMFPT_beyond_two_term hα hl hrb)).const_mul_left (1 / 2)
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with D hD
  have hD0 : (0 : ℝ) < D := hD
  have hQ : 0 < guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D) := by
    unfold guardPrefactor; positivity
  generalize guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D) = Q at hQ ⊢
  field_simp
  ring

/-- **Two-term expansion of the ratio** (source §1.2): for every `r_b > r_c`,
`T(r_b)/T(r_c) = 2 − 2c √D̃ + O(D̃)` as `D̃ → 0⁺`, `c = 2√l₁/(√π α)`; equivalently
`T_committed/T_guard = 2 (1 − 1/√(πX) + O(1/X))`. -/
@[powerlib_foundation] theorem guardMFPT_ratio_two_term (hα : 0 < α) (hl : 0 < l₁) {rb : ℝ}
    (hrb : guardRadius α l₁ < rb) :
    (fun D => guardMFPT α l₁ D rb / guardMFPT α l₁ D (guardRadius α l₁) - 2 +
        2 * (2 * √l₁ / (√π * α)) * √D) =O[𝓝[>] 0] fun D => D := by
  have hG := guardMFPT_guard_two_term hα hl
  have hB := guardMFPT_beyond_two_term hα hl hrb
  have hG1 := guardMFPT_guard_isBigO hα hl
  have hsG : (fun D => √D * (guardMFPT α l₁ D (guardRadius α l₁) /
      (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D)) - 1)) =O[𝓝[>] 0]
      fun D => D := by
    refine ((Asymptotics.isBigO_refl (fun D : ℝ => √D) _).mul hG1).congr' EventuallyEq.rfl ?_
    filter_upwards [self_mem_nhdsWithin] with D hD
    exact Real.mul_self_sqrt (le_of_lt hD)
  have hN := (hB.sub hG).add (hsG.const_mul_left (2 * (2 * √l₁ / (√π * α))))
  have hGinv : (fun D => (guardMFPT α l₁ D (guardRadius α l₁) /
      (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D)))⁻¹) =O[𝓝[>] 0]
      fun _ => (1 : ℝ) := by
    have := (tendsto_guardMFPT_guard hα hl).inv₀ one_ne_zero
    rw [inv_one] at this
    exact this.isBigO_one ℝ
  refine ((hN.mul hGinv).congr' ?_ ?_)
  · filter_upwards [self_mem_nhdsWithin,
      (tendsto_guardMFPT_guard hα hl).eventually (lt_mem_nhds (one_pos : (0 : ℝ) < 1))]
      with D hD hTD
    have hD0 : (0 : ℝ) < D := hD
    have hQ : 0 < guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D) := by
      unfold guardPrefactor; positivity
    have hT : guardMFPT α l₁ D (guardRadius α l₁) ≠ 0 := by
      intro h; rw [h, zero_div] at hTD; exact lt_irrefl _ hTD
    generalize guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D) = Q at hQ ⊢
    generalize guardMFPT α l₁ D (guardRadius α l₁) = T at hT ⊢
    field_simp
    ring
  · exact Filter.Eventually.of_forall fun D => mul_one D

/-! ## The half-order coefficient: limits and sharpness -/

/-- An expansion `f(D̃) = c √D̃ + O(D̃)` gives `f(D̃)/√D̃ → c` as `D̃ → 0⁺`. -/
@[powerlib_foundation] theorem tendsto_div_sqrt_of_isBigO {f : ℝ → ℝ} {c : ℝ}
    (h : (fun D => f D - c * √D) =O[𝓝[>] 0] fun D => D) :
    Tendsto (fun D => f D / √D) (𝓝[>] 0) (𝓝 c) := by
  have hm := h.mul (Asymptotics.isBigO_refl (fun D : ℝ => (√D)⁻¹) (𝓝[>] 0))
  have hs : Tendsto (fun D : ℝ => D * (√D)⁻¹) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun D : ℝ => √D) (𝓝[>] 0) (𝓝 0) := by
      have := Real.continuous_sqrt.tendsto (0 : ℝ)
      rw [Real.sqrt_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine h0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with D hD
    have hs : 0 < √D := Real.sqrt_pos.mpr hD
    rw [show D = √D * √D from (Real.mul_self_sqrt (le_of_lt hD)).symm, Real.sqrt_mul_self hs.le]
    field_simp
  have ht := (hm.trans_tendsto hs).add_const c
  rw [zero_add] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with D hD
  have hs : 0 < √D := Real.sqrt_pos.mpr hD
  field_simp
  ring

/-- **The half-order coefficient of `T_guard`**: `(T_guard/(P e^X) − 1)/√D̃ → 2√l₁/(√π α)` as
`D̃ → 0⁺`. -/
@[powerlib_foundation] theorem tendsto_guardMFPT_guard_sub_one_div_sqrt (hα : 0 < α)
    (hl : 0 < l₁) :
    Tendsto (fun D => (guardMFPT α l₁ D (guardRadius α l₁) /
        (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D)) - 1) / √D) (𝓝[>] 0)
      (𝓝 (2 * √l₁ / (√π * α))) :=
  tendsto_div_sqrt_of_isBigO ((guardMFPT_guard_two_term hα hl).congr_left fun D => by ring)

/-- **The half-order coefficient of the ratio**: `(T(r_b)/T(r_c) − 2)/√D̃ → −4√l₁/(√π α)` as
`D̃ → 0⁺`, for every `r_b > r_c`. -/
@[powerlib_foundation] theorem tendsto_guardMFPT_ratio_sub_two_div_sqrt (hα : 0 < α) (hl : 0 < l₁)
    {rb : ℝ} (hrb : guardRadius α l₁ < rb) :
    Tendsto (fun D => (guardMFPT α l₁ D rb / guardMFPT α l₁ D (guardRadius α l₁) - 2) / √D)
      (𝓝[>] 0) (𝓝 (-(4 * √l₁ / (√π * α)))) :=
  tendsto_div_sqrt_of_isBigO ((guardMFPT_ratio_two_term hα hl hrb).congr_left fun D => by ring)

/-- The half-order coefficient `2√l₁/(√π α)` is positive: the `X^{−1/2}` term of `T_guard` (and
of the ratio) is present for every `α, l₁ > 0`. -/
@[powerlib_foundation] theorem guardHalfOrder_pos (hα : 0 < α) (hl : 0 < l₁) :
    0 < 2 * √l₁ / (√π * α) := by
  have := Real.sqrt_pos.mpr hl
  have := Real.sqrt_pos.mpr Real.pi_pos
  positivity

/-- **The rate of `T_guard ~ P e^X` is sharp**: `T_guard/(P e^X) − 1 =Θ(√D̃)` as `D̃ → 0⁺` (an upper
bound is `guardMFPT_guard_isBigO`; the matching lower bound comes from the nonzero coefficient). -/
@[powerlib_foundation] theorem guardMFPT_guard_sub_one_isTheta (hα : 0 < α) (hl : 0 < l₁) :
    (fun D => guardMFPT α l₁ D (guardRadius α l₁) /
        (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D)) - 1) =Θ[𝓝[>] 0]
      fun D => √D :=
  (Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero
    (tendsto_guardMFPT_guard_sub_one_div_sqrt hα hl) (guardHalfOrder_pos hα hl).ne').symm

/-- **The rate of `T_committed/T_guard → 2` is sharp**: `T(r_b)/T(r_c) − 2 =Θ(√D̃)` as `D̃ → 0⁺`
for every `r_b > r_c` (upper bound `guardMFPT_ratio_sub_two_isBigO`). -/
@[powerlib_foundation] theorem guardMFPT_ratio_sub_two_isTheta (hα : 0 < α) (hl : 0 < l₁)
    {rb : ℝ} (hrb : guardRadius α l₁ < rb) :
    (fun D => guardMFPT α l₁ D rb / guardMFPT α l₁ D (guardRadius α l₁) - 2) =Θ[𝓝[>] 0]
      fun D => √D := by
  have h4 : 0 < 4 * √l₁ / (√π * α) := by
    have := guardHalfOrder_pos hα hl
    have e : 4 * √l₁ / (√π * α) = 2 * (2 * √l₁ / (√π * α)) := by ring
    rw [e]; positivity
  exact (Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero
    (tendsto_guardMFPT_ratio_sub_two_div_sqrt hα hl hrb) (neg_ne_zero.mpr h4.ne')).symm

/-- The half-order term of the ratio is not removable: `T(r_b)/T(r_c) − 2 ≠ o(√D̃)`. -/
@[powerlib_foundation] theorem not_guardMFPT_ratio_sub_two_isLittleO (hα : 0 < α) (hl : 0 < l₁)
    {rb : ℝ} (hrb : guardRadius α l₁ < rb) :
    ¬ (fun D => guardMFPT α l₁ D rb / guardMFPT α l₁ D (guardRadius α l₁) - 2) =o[𝓝[>] 0]
      fun D => √D := by
  intro ho
  have h1 := ho.tendsto_div_nhds_zero
  have h2 := tendsto_guardMFPT_ratio_sub_two_div_sqrt hα hl hrb
  have h4 : 0 < 4 * √l₁ / (√π * α) := by
    have := guardHalfOrder_pos hα hl
    have e : 4 * √l₁ / (√π * α) = 2 * (2 * √l₁ / (√π * α)) := by ring
    rw [e]; positivity
  have := tendsto_nhds_unique h1 h2
  linarith

/-- The half-order term of `T_guard` is not removable: `T_guard/(P e^X) − 1 ≠ o(√D̃)`. -/
@[powerlib_foundation] theorem not_guardMFPT_guard_sub_one_isLittleO (hα : 0 < α) (hl : 0 < l₁) :
    ¬ (fun D => guardMFPT α l₁ D (guardRadius α l₁) /
        (guardPrefactor α l₁ D * Real.exp (barrierHeight α l₁ / D)) - 1) =o[𝓝[>] 0]
      fun D => √D := by
  intro ho
  have := tendsto_nhds_unique ho.tendsto_div_nhds_zero
    (tendsto_guardMFPT_guard_sub_one_div_sqrt hα hl)
  linarith [guardHalfOrder_pos hα hl]

/-- Consistency with the truncated moment table (`Asymptotics/EndpointLaplace.lean`): in
`ξ = r_c − y` the weight has amplitude `g = (r_c − ξ)⁻¹` (`g₀ = r_c⁻¹`, `g₁ = r_c⁻²`) and phase
`ΔU − U(r_c − ξ)` (`φ₂ = 2α`, `φ₃ = −6l₁r_c`), whose table coefficient is the half-order coefficient
`2√l₁/(√π α)` of `guardMFPT_guard_two_term` (large parameter `1/D̃`). -/
@[powerlib_foundation] theorem guard_endpointCorrection_eq (hα : 0 < α) (hl : 0 < l₁) :
    endpointCorrection (√(α / l₁))⁻¹ ((√(α / l₁)) ^ 2)⁻¹ (2 * α) (-(6 * l₁ * √(α / l₁))) =
      2 * √l₁ / (√π * α) := by
  unfold endpointCorrection
  rw [Real.sqrt_div' _ hl.le, Real.sqrt_div' _ Real.pi_pos.le,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  obtain ⟨p, hp, hp2⟩ : ∃ p, p = √α ∧ p ^ 2 = α := ⟨_, rfl, Real.sq_sqrt hα.le⟩
  obtain ⟨q, hq, hq2⟩ : ∃ q, q = √l₁ ∧ q ^ 2 = l₁ := ⟨_, rfl, Real.sq_sqrt hl.le⟩
  have hp0 : 0 < p := hp ▸ Real.sqrt_pos.mpr hα
  have hq0 : 0 < q := hq ▸ Real.sqrt_pos.mpr hl
  have hs2 : 0 < √(2 : ℝ) := Real.sqrt_pos.mpr two_pos
  have hsπ : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  rw [← hp, ← hq]
  subst hp2 hq2
  field_simp
  ring


/-! ## The same statements along `X = ΔU/D̃ → ∞` -/

/-- Composition with `D̃ = Δ/X` (`Δ > 0`): `f(D̃)/√D̃ → c` as `D̃ → 0⁺` gives
`√X f(Δ/X) → √Δ c` as `X → ∞`. -/
@[powerlib_foundation] theorem tendsto_sqrt_mul_comp_div_atTop {f : ℝ → ℝ} {c Δ : ℝ} (hΔ : 0 < Δ)
    (hf : Tendsto (fun D => f D / √D) (𝓝[>] 0) (𝓝 c)) :
    Tendsto (fun X => √X * f (Δ / X)) atTop (𝓝 (√Δ * c)) := by
  have hD : Tendsto (fun X : ℝ => Δ / X) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.div_atTop tendsto_id, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with X hX
    exact div_pos hΔ hX
  refine ((hf.comp hD).const_mul √Δ).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with X hX
  have hsX : 0 < √X := Real.sqrt_pos.mpr hX
  have hsΔ : 0 < √Δ := Real.sqrt_pos.mpr hΔ
  simp only [Function.comp_apply]
  rw [Real.sqrt_div' _ hX.le]
  field_simp

/-- Composition with `D̃ = Δ/X` (`Δ > 0`): `f = O(D̃)` as `D̃ → 0⁺` gives `f(Δ/X) = O(1/X)` as
`X → ∞`. -/
@[powerlib_foundation] theorem isBigO_comp_div_atTop_inv {f : ℝ → ℝ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hf : f =O[𝓝[>] 0] fun D => D) : (fun X => f (Δ / X)) =O[atTop] fun X => X⁻¹ := by
  have hD : Tendsto (fun X : ℝ => Δ / X) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.div_atTop tendsto_id, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with X hX
    exact div_pos hΔ hX
  refine (hf.comp_tendsto hD).trans ?_
  apply Asymptotics.IsBigO.of_bound Δ
  filter_upwards [eventually_gt_atTop 0] with X hX
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (div_pos hΔ hX), abs_of_pos (inv_pos.2 hX),
    div_eq_mul_inv]

/-- `√ΔU · 2√l₁/(√π α) = 1/√π`, `ΔU = α²/(4l₁)`. -/
@[powerlib_foundation] theorem sqrt_barrierHeight_mul_halfOrder (hα : 0 < α) (hl : 0 < l₁) :
    √(barrierHeight α l₁) * (2 * √l₁ / (√π * α)) = 1 / √π := by
  rw [barrierHeight, Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ 4 * l₁), Real.sqrt_sq hα.le,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show √(4 : ℝ) = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have := Real.sqrt_pos.mpr hl
  have := Real.sqrt_pos.mpr Real.pi_pos
  field_simp

/-- **`T_guard = P e^X (1 + 1/√(πX) + o(X^{−1/2}))`** along `X = ΔU/D̃ → ∞` (source §1.3):
`√X (T_guard/(P e^X) − 1) → 1/√π`. -/
@[powerlib_foundation] theorem tendsto_guardMFPT_guard_mul_sqrt_atTop (hα : 0 < α) (hl : 0 < l₁) :
    Tendsto (fun X => √X * (guardMFPT α l₁ (barrierHeight α l₁ / X) (guardRadius α l₁) /
        (guardPrefactor α l₁ (barrierHeight α l₁ / X) * Real.exp X) - 1)) atTop
      (𝓝 (1 / √π)) := by
  have hΔ : 0 < barrierHeight α l₁ := by unfold barrierHeight; positivity
  have h := tendsto_sqrt_mul_comp_div_atTop hΔ (tendsto_guardMFPT_guard_sub_one_div_sqrt hα hl)
  rw [sqrt_barrierHeight_mul_halfOrder hα hl] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with X hX
  rw [div_div_cancel₀ hΔ.ne']

/-- **`T_committed/T_guard = 2 (1 − 1/√(πX) + o(X^{−1/2}))`** along `X = ΔU/D̃ → ∞`
(source §1.2, "趋近 2 的方式本身是 `1 + O(X^{−1/2})`", with the coefficient):
`√X (T(r_b)/T(r_c) − 2) → −2/√π`, for every `r_b > r_c`. -/
@[powerlib_foundation] theorem tendsto_guardMFPT_ratio_mul_sqrt_atTop (hα : 0 < α) (hl : 0 < l₁)
    {rb : ℝ} (hrb : guardRadius α l₁ < rb) :
    Tendsto (fun X => √X * (guardMFPT α l₁ (barrierHeight α l₁ / X) rb /
        guardMFPT α l₁ (barrierHeight α l₁ / X) (guardRadius α l₁) - 2)) atTop
      (𝓝 (-(2 / √π))) := by
  have hΔ : 0 < barrierHeight α l₁ := by unfold barrierHeight; positivity
  have h := tendsto_sqrt_mul_comp_div_atTop hΔ
    (tendsto_guardMFPT_ratio_sub_two_div_sqrt hα hl hrb)
  have e : √(barrierHeight α l₁) * -(4 * √l₁ / (√π * α)) = -(2 / √π) := by
    have := sqrt_barrierHeight_mul_halfOrder hα hl
    have e2 : √(barrierHeight α l₁) * -(4 * √l₁ / (√π * α)) =
        -(2 * (√(barrierHeight α l₁) * (2 * √l₁ / (√π * α)))) := by ring
    rw [e2, this]; ring
  rwa [e] at h

/-- **`T_committed = 2 P e^X (1 + O(1/X))`** along `X = ΔU/D̃ → ∞`, for every `r_b > r_c`: no
half-order term (`guardMFPT_committed_two_term`). -/
@[powerlib_foundation] theorem guardMFPT_committed_two_term_atTop (hα : 0 < α) (hl : 0 < l₁)
    {rb : ℝ} (hrb : guardRadius α l₁ < rb) :
    (fun X => guardMFPT α l₁ (barrierHeight α l₁ / X) rb /
        (2 * (guardPrefactor α l₁ (barrierHeight α l₁ / X) * Real.exp X)) - 1) =O[atTop]
      fun X => X⁻¹ := by
  have hΔ : 0 < barrierHeight α l₁ := by unfold barrierHeight; positivity
  refine (isBigO_comp_div_atTop_inv hΔ (guardMFPT_committed_two_term hα hl hrb)).congr' ?_
    EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with X hX
  rw [div_div_cancel₀ hΔ.ne']

end powerlib.Asymptotics.Guard
