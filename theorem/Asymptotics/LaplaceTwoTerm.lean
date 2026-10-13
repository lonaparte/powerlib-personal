import theorem.Asymptotics.LaplaceMethod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Two-term endpoint Laplace expansion for an exact Gaussian phase

Foundation layer: one-variable real analysis, no model.

Setting. `J(β) = ∫_0^L h(u) e^{−βu²} du` with `L > 0`, `h` continuous on `[0, L]` and a first-order
Taylor bound `|h(u) − h₀ − h₁ u| ≤ M u²` on `[0, L]`. The phase `βu²` is exactly quadratic with its
minimum at the endpoint `u = 0`; a nondegenerate endpoint minimum of a general phase takes this form
after the Morse change of variables `u² = φ(y) − φ(y*)`, the Jacobian being absorbed into `h`
(this is how `Asymptotics/GuardMFPTExpansion.lean` uses it). Large parameter `β → ∞`.

Results.
* `gaussMoment2_Ioi`: `∫_0^∞ u² e^{−βu²} du = √(π/β)/(4β)`.
* `integral_mul_exp_neg_mul_sq_interval`: `∫_0^L u e^{−βu²} du = (1 − e^{−βL²})/(2β)`.
* `integral_exp_neg_mul_sq_interval_bounds`:
  `√(π/β)/2 − e^{−βL²}/(2βL) ≤ ∫_0^L e^{−βu²} du ≤ √(π/β)/2`.
* `exp_neg_le_inv`: `e^{−x} ≤ 1/x` for `x > 0`.
* `laplace_two_term_bound` (explicit, every `β > 0`):
  `|J(β) − h₀ √(π/β)/2 − h₁/(2β)| ≤ M √(π/β)/(4β) + (|h₀|/L + |h₁|)/(2β²L²)`.
* `laplace_two_term_isBigO` (`h₀ ≠ 0`, `β → ∞`):
  `J(β)/(h₀ √(π/β)/2) − 1 − (h₁/h₀)/√(πβ) = O(1/β)`, i.e.
  `J(β) = h₀ (√(π/β)/2) (1 + (h₁/h₀)(πβ)^{−1/2} + O(β^{−1}))`.
* `laplace_two_term_tendsto`: `√β (J(β)/(h₀ √(π/β)/2) − 1) → (h₁/h₀)/√π`; the half-order term is
  present exactly when `h₁ ≠ 0` (`laplace_two_term_coeff_ne_zero_iff`).

Relation to the truncated table `Asymptotics/EndpointLaplace.lean`: there the half-order coefficient
`√(2/π)(g₁/g₀ − φ₃/(3φ₂))/√φ₂` is read off the first three Taylor terms without a remainder
estimate; here the phase has been normalized, the remainder is controlled and the coefficient is
`(h₁/h₀)/√π`.

Source: work-sync theory/T-endpoint-laplace-asymptotics.md §1.1 (endpoint Laplace, relative
correction of order `X^{−1/2}`).
-/

noncomputable section
namespace powerlib.Asymptotics

open Real Set Filter Topology MeasureTheory intervalIntegral

/-- Half-line second Gaussian moment: `∫_0^∞ u² e^{−βu²} du = √(π/β)/(4β)`
(wraps `integral_rpow_mul_exp_neg_mul_rpow` with `p = q = 2`, `Γ(3/2) = √π/2`). -/
@[powerlib_foundation] theorem gaussMoment2_Ioi {β : ℝ} (hβ : 0 < β) :
    ∫ u in Ioi (0 : ℝ), u ^ 2 * Real.exp (-β * u ^ 2) = √(π / β) / (4 * β) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) (b := β) two_pos
    (by norm_num) hβ
  simp only [Real.rpow_two] at h
  rw [h]
  have hG : Real.Gamma ((2 + 1) / 2) = √π / 2 := by
    rw [show ((2 : ℝ) + 1) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  have hb : β ^ (-((2 : ℝ) + 1) / 2) = (β * √β)⁻¹ := by
    rw [show -((2 : ℝ) + 1) / 2 = -(1 + 1 / 2) by norm_num, Real.rpow_neg hβ.le,
      Real.rpow_add hβ, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hG, hb, Real.sqrt_div' π hβ.le]
  have hs : 0 < √β := Real.sqrt_pos.mpr hβ
  field_simp
  ring

/-- `∫_0^L u e^{−βu²} du = (1 − e^{−βL²})/(2β)` (fundamental theorem of calculus). -/
@[powerlib_foundation] theorem integral_mul_exp_neg_mul_sq_interval {β : ℝ} (hβ : 0 < β) (L : ℝ) :
    ∫ u in (0 : ℝ)..L, u * Real.exp (-β * u ^ 2) = (1 - Real.exp (-β * L ^ 2)) / (2 * β) := by
  have hderiv : ∀ u ∈ uIcc 0 L, HasDerivAt (fun u => -(1 / (2 * β)) * Real.exp (-β * u ^ 2))
      (u * Real.exp (-β * u ^ 2)) u := by
    intro u _
    have h1 : HasDerivAt (fun u => -β * u ^ 2) (-β * (2 * u)) u := by
      simpa using (hasDerivAt_pow 2 u).const_mul (-β)
    have := (h1.exp).const_mul (-(1 / (2 * β)))
    convert this using 1
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun u : ℝ => u * Real.exp (-β * u ^ 2)).intervalIntegrable _ _)]
  simp
  field_simp
  ring

/-- `e^{−x} ≤ 1/x` for `x > 0`. -/
@[powerlib_foundation] theorem exp_neg_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 1 / x := by
  have h := Real.add_one_le_exp x
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ hx (by linarith)

/-- Gaussian mass on a finite interval:
`√(π/β)/2 − e^{−βL²}/(2βL) ≤ ∫_0^L e^{−βu²} du ≤ √(π/β)/2`. -/
@[powerlib_foundation] theorem integral_exp_neg_mul_sq_interval_bounds {β L : ℝ} (hβ : 0 < β)
    (hL : 0 < L) :
    √(π / β) / 2 - Real.exp (-β * L ^ 2) / (2 * β * L) ≤
        ∫ u in (0 : ℝ)..L, Real.exp (-β * u ^ 2) ∧
      ∫ u in (0 : ℝ)..L, Real.exp (-β * u ^ 2) ≤ √(π / β) / 2 := by
  have hg : Integrable fun u : ℝ => Real.exp (-β * u ^ 2) := integrable_exp_neg_mul_sq hβ
  have hg1 : Integrable fun u : ℝ => u * Real.exp (-β * u ^ 2) := integrable_mul_exp_neg_mul_sq hβ
  have hsplit : ∀ f : ℝ → ℝ, Integrable f → ∫ u in Ioi (0 : ℝ), f u =
      (∫ u in Ioc (0 : ℝ) L, f u) + ∫ u in Ioi L, f u := fun f hf => by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hf.integrableOn
      hf.integrableOn, Ioc_union_Ioi_eq_Ioi hL.le]
  have hmain := integral_gaussian_Ioi β
  have h0 := hsplit _ hg
  have h1 := hsplit _ hg1
  have hm1 : ∫ u in Ioi (0 : ℝ), u * Real.exp (-β * u ^ 2) = 1 / (2 * β) := by
    have h := halfMoment1 (b := 2 * β) (by positivity)
    rw [show 2 * β / 2 = β by ring] at h
    simpa only [neg_mul] using h
  have hI1 : ∫ u in Ioc (0 : ℝ) L, u * Real.exp (-β * u ^ 2) =
      (1 - Real.exp (-β * L ^ 2)) / (2 * β) := by
    rw [← intervalIntegral.integral_of_le hL.le, integral_mul_exp_neg_mul_sq_interval hβ]
  have htail1 : ∫ u in Ioi L, u * Real.exp (-β * u ^ 2) = Real.exp (-β * L ^ 2) / (2 * β) := by
    have : (∫ u in Ioi L, u * Real.exp (-β * u ^ 2)) =
        1 / (2 * β) - (1 - Real.exp (-β * L ^ 2)) / (2 * β) := by linarith
    rw [this]; field_simp; ring
  have htail : ∫ u in Ioi L, Real.exp (-β * u ^ 2) ≤ Real.exp (-β * L ^ 2) / (2 * β * L) := by
    calc ∫ u in Ioi L, Real.exp (-β * u ^ 2)
        ≤ ∫ u in Ioi L, L⁻¹ * (u * Real.exp (-β * u ^ 2)) := by
          apply setIntegral_mono_on hg.integrableOn (hg1.const_mul _).integrableOn
            measurableSet_Ioi
          intro u hu
          have hu' : L < u := hu
          rw [← mul_assoc]
          apply le_mul_of_one_le_left (Real.exp_pos _).le
          rw [inv_mul_eq_div, one_le_div hL]; exact hu'.le
      _ = Real.exp (-β * L ^ 2) / (2 * β * L) := by
          rw [MeasureTheory.integral_const_mul, htail1]; field_simp
  have htail0 : 0 ≤ ∫ u in Ioi L, Real.exp (-β * u ^ 2) :=
    setIntegral_nonneg measurableSet_Ioi fun u _ => (Real.exp_pos _).le
  rw [intervalIntegral.integral_of_le hL.le]
  constructor <;> linarith

/-- **Two-term endpoint Laplace bound** for an exact Gaussian phase: if `h` is continuous on
`[0, L]` (`L > 0`) and `|h(u) − h₀ − h₁u| ≤ M u²` there, then for every `β > 0`
`|∫_0^L h e^{−βu²} − h₀ √(π/β)/2 − h₁/(2β)| ≤ M √(π/β)/(4β) + (|h₀|/L + |h₁|)/(2β²L²)`. -/
@[powerlib_foundation] theorem laplace_two_term_bound {h : ℝ → ℝ} {β L h₀ h₁ M : ℝ} (hβ : 0 < β)
    (hL : 0 < L) (hcont : ContinuousOn h (Icc 0 L))
    (hrem : ∀ u ∈ Icc (0 : ℝ) L, |h u - h₀ - h₁ * u| ≤ M * u ^ 2) :
    |(∫ u in (0 : ℝ)..L, h u * Real.exp (-β * u ^ 2)) -
        (h₀ * (√(π / β) / 2) + h₁ * (1 / (2 * β)))| ≤
      M * (√(π / β) / (4 * β)) + (|h₀| / L + |h₁|) * (1 / (2 * β ^ 2 * L ^ 2)) := by
  have hM : 0 ≤ M := by
    have h1 := hrem L ⟨hL.le, le_rfl⟩
    have h2 := abs_nonneg (h L - h₀ - h₁ * L)
    have hL2 : 0 < L ^ 2 := by positivity
    by_contra hneg
    push Not at hneg
    nlinarith
  set e : ℝ → ℝ := fun u => Real.exp (-β * u ^ 2) with he
  have hec : Continuous e := by simp only [he]; fun_prop
  have hcont' : ContinuousOn h (uIcc 0 L) := by rwa [uIcc_of_le hL.le]
  have ihe : IntervalIntegrable (fun u => h u * e u) volume 0 L :=
    (hcont'.mul hec.continuousOn).intervalIntegrable
  have ie : IntervalIntegrable e volume 0 L := hec.intervalIntegrable _ _
  have iue : IntervalIntegrable (fun u => u * e u) volume 0 L :=
    (continuous_id.mul hec).intervalIntegrable _ _
  -- decomposition `∫ h e = h₀ G₀ + h₁ G₁ + ∫ r e`
  have hdec : (∫ u in (0 : ℝ)..L, (h u - h₀ - h₁ * u) * e u) =
      (∫ u in (0 : ℝ)..L, h u * e u) - h₀ * (∫ u in (0 : ℝ)..L, e u) -
        h₁ * ∫ u in (0 : ℝ)..L, u * e u := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub ihe (ie.const_mul _),
      ← intervalIntegral.integral_sub (ihe.sub (ie.const_mul _)) (iue.const_mul _)]
    congr 1; funext u; ring
  -- the remainder
  have hR : |∫ u in (0 : ℝ)..L, (h u - h₀ - h₁ * u) * e u| ≤ M * (√(π / β) / (4 * β)) := by
    have i2 : Integrable fun u : ℝ => M * (u ^ 2 * e u) :=
      (integrable_pow_mul_exp_neg_mul_sq hβ 2).const_mul M
    calc |∫ u in (0 : ℝ)..L, (h u - h₀ - h₁ * u) * e u|
        ≤ ∫ u in (0 : ℝ)..L, |(h u - h₀ - h₁ * u) * e u| :=
          intervalIntegral.abs_integral_le_integral_abs hL.le
      _ ≤ ∫ u in (0 : ℝ)..L, M * (u ^ 2 * e u) := by
          apply intervalIntegral.integral_mono_on hL.le
          · exact ((hcont'.sub continuousOn_const).sub (continuousOn_const.mul
              continuousOn_id) |>.mul hec.continuousOn).abs.intervalIntegrable
          · exact i2.intervalIntegrable
          intro u hu
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          have := mul_le_mul_of_nonneg_right (hrem u hu) (Real.exp_pos (-β * u ^ 2)).le
          simp only [he]
          linarith
      _ ≤ ∫ u in Ioi (0 : ℝ), M * (u ^ 2 * e u) := by
          rw [intervalIntegral.integral_of_le hL.le]
          apply setIntegral_mono_set i2.integrableOn
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
            simp only [he]; positivity
          · exact Ioc_subset_Ioi_self.eventuallyLE
      _ = M * (√(π / β) / (4 * β)) := by
          rw [MeasureTheory.integral_const_mul]
          simp only [he]
          rw [gaussMoment2_Ioi hβ]
  -- the two Gaussian moments on `[0, L]`
  obtain ⟨hG0lo, hG0hi⟩ := integral_exp_neg_mul_sq_interval_bounds hβ hL
  have hG1 := integral_mul_exp_neg_mul_sq_interval hβ L
  have hE : Real.exp (-β * L ^ 2) ≤ 1 / (β * L ^ 2) := by
    have := exp_neg_le_inv (x := β * L ^ 2) (by positivity)
    rwa [show -(β * L ^ 2) = -β * L ^ 2 by ring] at this
  have hE0 := Real.exp_pos (-β * L ^ 2)
  have hT0 : Real.exp (-β * L ^ 2) / (2 * β * L) ≤ 1 / L * (1 / (2 * β ^ 2 * L ^ 2)) := by
    rw [div_le_iff₀ (by positivity)]
    calc Real.exp (-β * L ^ 2) ≤ 1 / (β * L ^ 2) := hE
      _ = 1 / L * (1 / (2 * β ^ 2 * L ^ 2)) * (2 * β * L) := by field_simp
  have hT1 : Real.exp (-β * L ^ 2) / (2 * β) ≤ 1 / (2 * β ^ 2 * L ^ 2) := by
    rw [div_le_iff₀ (by positivity)]
    calc Real.exp (-β * L ^ 2) ≤ 1 / (β * L ^ 2) := hE
      _ = 1 / (2 * β ^ 2 * L ^ 2) * (2 * β) := by field_simp
  -- assemble
  simp only [he] at hdec hR
  generalize (∫ u in (0 : ℝ)..L, h u * Real.exp (-β * u ^ 2)) = J at hdec ⊢
  generalize (∫ u in (0 : ℝ)..L, (h u - h₀ - h₁ * u) * Real.exp (-β * u ^ 2)) = R at hdec hR
  generalize (∫ u in (0 : ℝ)..L, Real.exp (-β * u ^ 2)) = G₀ at hdec hG0lo hG0hi
  generalize (∫ u in (0 : ℝ)..L, u * Real.exp (-β * u ^ 2)) = G₁ at hdec hG1
  have hJ : J - (h₀ * (√(π / β) / 2) + h₁ * (1 / (2 * β))) =
      R + h₀ * (G₀ - √(π / β) / 2) + h₁ * (G₁ - 1 / (2 * β)) := by linarith
  rw [hJ]
  have hA0 : |G₀ - √(π / β) / 2| ≤ 1 / L * (1 / (2 * β ^ 2 * L ^ 2)) := by
    rw [abs_le]; constructor <;> linarith
  have hA1 : |G₁ - 1 / (2 * β)| ≤ 1 / (2 * β ^ 2 * L ^ 2) := by
    have e1 : G₁ - 1 / (2 * β) = -(Real.exp (-β * L ^ 2) / (2 * β)) := by
      rw [hG1]; field_simp; ring
    rw [e1, abs_neg, abs_of_pos (by positivity)]
    exact hT1
  calc |R + h₀ * (G₀ - √(π / β) / 2) + h₁ * (G₁ - 1 / (2 * β))|
      ≤ |R| + |h₀| * |G₀ - √(π / β) / 2| + |h₁| * |G₁ - 1 / (2 * β)| := by
        rw [← abs_mul, ← abs_mul]
        exact (abs_add_le _ _).trans (by linarith [abs_add_le R (h₀ * (G₀ - √(π / β) / 2))])
    _ ≤ M * (√(π / β) / (4 * β)) + |h₀| * (1 / L * (1 / (2 * β ^ 2 * L ^ 2))) +
          |h₁| * (1 / (2 * β ^ 2 * L ^ 2)) := by
        gcongr
    _ = M * (√(π / β) / (4 * β)) + (|h₀| / L + |h₁|) * (1 / (2 * β ^ 2 * L ^ 2)) := by ring

/-- **Two-term endpoint Laplace expansion** (`β → ∞`): for `h₀ ≠ 0`,
`J(β)/(h₀ √(π/β)/2) − 1 − (h₁/h₀)/√(πβ) = O(1/β)`, `J(β) = ∫_0^L h e^{−βu²}`. Explicitly the bound
`M/(2|h₀|β) + (|h₀|/L + |h₁|)/(|h₀| L² √π β)` holds for `β ≥ 1` (`laplace_two_term_bound`). -/
@[powerlib_foundation] theorem laplace_two_term_isBigO {h : ℝ → ℝ} {L h₀ h₁ M : ℝ} (hL : 0 < L)
    (hh₀ : h₀ ≠ 0) (hcont : ContinuousOn h (Icc 0 L))
    (hrem : ∀ u ∈ Icc (0 : ℝ) L, |h u - h₀ - h₁ * u| ≤ M * u ^ 2) :
    (fun β => (∫ u in (0 : ℝ)..L, h u * Real.exp (-β * u ^ 2)) / (h₀ * (√(π / β) / 2)) - 1 -
      h₁ / h₀ / √(π * β)) =O[atTop] fun β => β⁻¹ := by
  apply Asymptotics.IsBigO.of_bound
    (M / (2 * |h₀|) + (|h₀| / L + |h₁|) / (|h₀| * L ^ 2 * √π))
  filter_upwards [eventually_ge_atTop 1] with β hβ1
  have hβ : 0 < β := by linarith
  have hb := laplace_two_term_bound hβ hL hcont hrem
  generalize (∫ u in (0 : ℝ)..L, h u * Real.exp (-β * u ^ 2)) = J at hb ⊢
  obtain ⟨r, hr, hr2⟩ : ∃ r, r = √β ∧ r ^ 2 = β := ⟨_, rfl, Real.sq_sqrt hβ.le⟩
  have hr0 : 0 < r := hr ▸ Real.sqrt_pos.mpr hβ
  have hr1 : 1 ≤ r := by
    rw [hr, show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hβ1
  have hsπ : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hh : 0 < |h₀| := abs_pos.mpr hh₀
  have e1 : √(π / β) = √π / r := by rw [Real.sqrt_div' _ hβ.le, ← hr]
  have e2 : √(π * β) = √π * r := by rw [Real.sqrt_mul Real.pi_pos.le, ← hr]
  rw [e1, e2]
  rw [e1] at hb
  rw [← hr2] at hb ⊢
  have key : J / (h₀ * (√π / r / 2)) - 1 - h₁ / h₀ / (√π * r) =
      (J - (h₀ * (√π / r / 2) + h₁ * (1 / (2 * r ^ 2)))) / (h₀ * (√π / r / 2)) := by
    field_simp
    ring
  have hden : |h₀ * (√π / r / 2)| = |h₀| * (√π / r / 2) := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < √π / r / 2)]
  rw [key, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_inv,
    abs_of_pos (by positivity : 0 < r ^ 2), hden, div_le_iff₀ (by positivity)]
  refine hb.trans (le_of_le_of_eq ?_ (show M * (√π / r / (4 * r ^ 2)) +
      (|h₀| / L + |h₁|) * (1 / (2 * L ^ 2 * r ^ 3)) =
      (M / (2 * |h₀|) + (|h₀| / L + |h₁|) / (|h₀| * L ^ 2 * √π)) * (r ^ 2)⁻¹ *
        (|h₀| * (√π / r / 2)) by field_simp; ring))
  have hK : 0 ≤ |h₀| / L + |h₁| := by positivity
  have hr34 : r ^ 3 ≤ (r ^ 2) ^ 2 := by
    rw [← pow_mul]; exact pow_le_pow_right₀ hr1 (by norm_num)
  have : 1 / (2 * (r ^ 2) ^ 2 * L ^ 2) ≤ 1 / (2 * L ^ 2 * r ^ 3) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [sq_nonneg L, mul_le_mul_of_nonneg_left hr34 (by positivity : (0 : ℝ) ≤ 2 * L ^ 2)]
  have := mul_le_mul_of_nonneg_left this hK
  linarith

/-- The half-order coefficient of the two-term expansion:
`√β (J(β)/(h₀ √(π/β)/2) − 1) → (h₁/h₀)/√π` as `β → ∞` (`h₀ ≠ 0`). -/
@[powerlib_foundation] theorem laplace_two_term_tendsto {h : ℝ → ℝ} {L h₀ h₁ M : ℝ} (hL : 0 < L)
    (hh₀ : h₀ ≠ 0) (hcont : ContinuousOn h (Icc 0 L))
    (hrem : ∀ u ∈ Icc (0 : ℝ) L, |h u - h₀ - h₁ * u| ≤ M * u ^ 2) :
    Tendsto (fun β => √β * ((∫ u in (0 : ℝ)..L, h u * Real.exp (-β * u ^ 2)) /
      (h₀ * (√(π / β) / 2)) - 1)) atTop (𝓝 (h₁ / h₀ / √π)) := by
  have hO := laplace_two_term_isBigO hL hh₀ hcont hrem
  have h1 := (Asymptotics.isBigO_refl (fun β : ℝ => √β) atTop).mul hO
  have h2 : Tendsto (fun β : ℝ => √β * β⁻¹) atTop (𝓝 0) := by
    refine (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with β hβ
    have hs : 0 < √β := Real.sqrt_pos.mpr hβ
    simp only [Function.comp_apply]
    rw [show β = √β ^ 2 from (Real.sq_sqrt hβ.le).symm]
    rw [Real.sqrt_sq hs.le]
    field_simp
  have h3 := (h1.trans_tendsto h2).add_const (h₁ / h₀ / √π)
  rw [zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with β hβ
  have hs : 0 < √β := Real.sqrt_pos.mpr hβ
  have hsπ : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  rw [Real.sqrt_mul Real.pi_pos.le]
  field_simp
  ring

/-- The half-order term of the two-term expansion is present exactly when `h₁ ≠ 0`. -/
@[powerlib_foundation] theorem laplace_two_term_coeff_ne_zero_iff {h₀ h₁ : ℝ} (hh₀ : h₀ ≠ 0) :
    h₁ / h₀ / √π ≠ 0 ↔ h₁ ≠ 0 := by
  have hsπ : √π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  simp [hh₀, hsπ]

end powerlib.Asymptotics
