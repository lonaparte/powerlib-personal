import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.LDPContraction
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-! # The large-deviation principle of a small Gaussian vector

The finite-dimensional ingredient of Schilder's theorem: `√ε Z`, `Z` a standard Gaussian vector
of `ℝᵈ`, satisfies the large-deviation principle as `ε → 0⁺` with the good rate `|x|²/2`.

Scope.
* Probability theory, not an engineering result. `ℝᵈ` is `Fin d → ℝ` with its product
  (sup-norm) topology and Borel sets; the law of `√ε Z` is `gaussLaw d ε`, the product of `d`
  copies of `N(0, ε)` (Mathlib's `gaussianReal`).
* This is the finite-dimensional Gaussian LDP; Schilder's theorem on `C([0, T])` is
  `theorem/Stochastic/Schilder.lean`.

Source: A. Dembo, O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed. (1998),
Ex. 2.2.29 / Thm 2.2.30 (Gaussian vectors, rate `|x|²/2` at speed `ε`) and the proof of Thm 5.2.3
(Schilder) through finite-dimensional projections; work-sync theory/T-large-deviations.md.

Results.
* `gaussLaw`, `gaussRate`; `integral_exp_mul_sq_gaussianReal`
  (`E exp((1 − δ) Y²/(2ε)) = δ^{−1/2}` for `Y ~ N(0, ε)`);
  `gaussLaw_sq_ge_le` (chi-square Chernoff bound
  `P(|√ε Z|² ≥ 2a) ≤ e^{−(1−δ)a/ε} δ^{−d/2}`); `gaussianReal_ball_ge` (a ball of radius `ρ`
  around `a` has mass `≥ 2ρ (2πε)^{−1/2} e^{−(|a|+ρ)²/(2ε)}`).
* `isGoodRate_gaussRate` (compact sublevel sets), `isLDP_gaussLaw`: **the Gaussian LDP**,
  `IsLDP (𝓝[>] 0) id (gaussLaw d) (gaussRate d)`.
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped ENNReal NNReal

/-- Law of `√ε Z` on `ℝᵈ`, `Z` standard Gaussian: independent `N(0, ε)` coordinates. -/
def gaussLaw (d : ℕ) (ε : ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 (Real.toNNReal ε)

/-- Gaussian rate `|x|²/2`. -/
def gaussRate (d : ℕ) (x : Fin d → ℝ) : ℝ≥0∞ := ENNReal.ofReal (∑ i, x i ^ 2 / 2)

instance (d : ℕ) (ε : ℝ) : IsProbabilityMeasure (gaussLaw d ε) := by
  unfold gaussLaw; infer_instance

/-! ## One-dimensional Gaussian estimates -/

/-- `E exp((1 − δ) Y²/(2ε)) = δ^{−1/2}` for `Y ~ N(0, ε)`, `ε, δ > 0`. -/
@[tmio T, powerlib_foundation] theorem integral_exp_mul_sq_gaussianReal {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) :
    ∫ y, Real.exp ((1 - δ) / (2 * ε) * y ^ 2) ∂(gaussianReal 0 (Real.toNNReal ε)) = (√δ)⁻¹ := by
  have hv : Real.toNNReal ε ≠ 0 := by simpa using hε
  have hv' : ((Real.toNNReal ε : ℝ≥0) : ℝ) = ε := Real.coe_toNNReal _ hε.le
  rw [integral_gaussianReal_eq_integral_smul hv]
  have e : ∀ y : ℝ, gaussianPDFReal 0 (Real.toNNReal ε) y •
      Real.exp ((1 - δ) / (2 * ε) * y ^ 2) =
      (√(2 * π * ε))⁻¹ * Real.exp (-(δ / (2 * ε)) * y ^ 2) := by
    intro y
    rw [gaussianPDFReal, hv', smul_eq_mul, mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [e]
  rw [integral_const_mul, integral_gaussian]
  have h1 : π / (δ / (2 * ε)) = 2 * π * ε / δ := by field_simp
  have h2 : 0 < √(2 * π * ε) := Real.sqrt_pos.mpr (by positivity)
  have h3 : 0 < √δ := Real.sqrt_pos.mpr hδ
  rw [h1, Real.sqrt_div (by positivity)]
  field_simp

/-- **Chi-square Chernoff bound**: `P(|√ε Z|² ≥ 2a) ≤ e^{−(1−δ)a/ε} δ^{−d/2}` for
`0 < δ ≤ 1`. -/
@[tmio T, powerlib_foundation] theorem gaussLaw_sq_ge_le (d : ℕ) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (a : ℝ) :
    gaussLaw d ε {x | 2 * a ≤ ∑ i, x i ^ 2} ≤
      ENNReal.ofReal (Real.exp (-(1 - δ) * a / ε) * (√δ)⁻¹ ^ d) := by
  set κ := (1 - δ) / (2 * ε) with hκ
  have hκ0 : 0 ≤ κ := div_nonneg (by linarith) (by positivity)
  set f : (Fin d → ℝ) → ℝ := fun x => ∏ i, Real.exp (κ * x i ^ 2) with hf
  have hI1 := integral_exp_mul_sq_gaussianReal hε hδ
  have hint1 : Integrable (fun y : ℝ => Real.exp (κ * y ^ 2))
      (gaussianReal 0 (Real.toNNReal ε)) :=
    Integrable.of_integral_ne_zero (by rw [hI1]; exact inv_ne_zero (Real.sqrt_pos.mpr hδ).ne')
  have hint : Integrable f (gaussLaw d ε) := Integrable.fintype_prod fun _ => hint1
  have hf0 : 0 ≤ᵐ[gaussLaw d ε] f :=
    ae_of_all _ fun x => Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
  have hI : ∫ x, f x ∂(gaussLaw d ε) = (√δ)⁻¹ ^ d := by
    rw [gaussLaw, integral_fintype_prod_eq_pow (fun y => Real.exp (κ * y ^ 2)), hI1,
      Fintype.card_fin]
  have hsub : {x : Fin d → ℝ | 2 * a ≤ ∑ i, x i ^ 2} ⊆
      {x | Real.exp (κ * (2 * a)) ≤ f x} := by
    intro x hx
    simp only [mem_ofPred_eq, hf, ← Real.exp_sum] at hx ⊢
    rw [← Finset.mul_sum]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx hκ0)
  have hmk := mul_meas_ge_le_integral_of_nonneg hf0 hint (Real.exp (κ * (2 * a)))
  rw [hI] at hmk
  have hreal : (gaussLaw d ε).real {x | 2 * a ≤ ∑ i, x i ^ 2} ≤
      Real.exp (-(1 - δ) * a / ε) * (√δ)⁻¹ ^ d := by
    have h1 := measureReal_mono (μ := gaussLaw d ε) hsub
    have hpos := Real.exp_pos (κ * (2 * a))
    have e : Real.exp (-(1 - δ) * a / ε) = (Real.exp (κ * (2 * a)))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      rw [hκ]
      field_simp
    rw [e]
    rw [inv_mul_eq_div, le_div_iff₀ hpos]
    nlinarith
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **Mass of a ball**: `N(0, ε)(B(a, ρ)) ≥ 2ρ (2πε)^{−1/2} e^{−(|a|+ρ)²/(2ε)}`. -/
@[tmio T, powerlib_foundation] theorem gaussianReal_ball_ge {ε : ℝ} (hε : 0 < ε) (ρ a : ℝ) :
    ENNReal.ofReal (2 * ρ * ((√(2 * π * ε))⁻¹ * Real.exp (-(|a| + ρ) ^ 2 / (2 * ε)))) ≤
      gaussianReal 0 (Real.toNNReal ε) (Metric.ball a ρ) := by
  have hv : Real.toNNReal ε ≠ 0 := by simpa using hε
  have hv' : ((Real.toNNReal ε : ℝ≥0) : ℝ) = ε := Real.coe_toNNReal _ hε.le
  rw [gaussianReal_apply _ hv]
  set c := (√(2 * π * ε))⁻¹ * Real.exp (-(|a| + ρ) ^ 2 / (2 * ε)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ x ∈ Metric.ball a ρ, ENNReal.ofReal c ≤ gaussianPDF 0 (Real.toNNReal ε) x := by
    intro x hx
    rw [gaussianPDF, gaussianPDFReal, hv']
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine Real.exp_le_exp.mpr (div_le_div_of_nonneg_right ?_ (by positivity))
    rw [Metric.mem_ball, Real.dist_eq] at hx
    have h1 : |x| ≤ |a| + ρ := by
      have := abs_sub_abs_le_abs_sub x a
      linarith
    have h2 : x ^ 2 ≤ (|a| + ρ) ^ 2 := by
      rw [← sq_abs x]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    simp only [sub_zero]
    linarith
  calc ENNReal.ofReal (2 * ρ * c) = ∫⁻ _ in Metric.ball a ρ, ENNReal.ofReal c := by
        rw [setLIntegral_const, Real.volume_ball, ← ENNReal.ofReal_mul hc0]
        ring_nf
    _ ≤ _ := setLIntegral_mono (measurable_gaussianPDF _ _) hpt

/-! ## The rate -/

@[tmio T, powerlib_foundation] theorem continuous_gaussRate (d : ℕ) :
    Continuous (gaussRate d) :=
  ENNReal.continuous_ofReal.comp (continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).pow 2).div_const 2)

@[tmio T, powerlib_foundation] theorem coe_gaussRate (d : ℕ) (x : Fin d → ℝ) :
    ((gaussRate d x : ℝ≥0∞) : EReal) = ((∑ i, x i ^ 2 / 2 : ℝ) : EReal) := by
  rw [gaussRate, EReal.coe_ennreal_ofReal,
    max_eq_left (Finset.sum_nonneg fun i _ => by positivity)]

/-- The Gaussian rate is good: `{|x|²/2 ≤ a}` is closed and bounded. -/
@[tmio T, powerlib_foundation] theorem isGoodRate_gaussRate (d : ℕ) :
    IsGoodRate (gaussRate d) := by
  intro a ha
  refine Metric.isCompact_of_isClosed_isBounded
    ((continuous_gaussRate d).lowerSemicontinuous.isClosed_preimage a) ?_
  refine (isBounded_iff_forall_norm_le).mpr ⟨√(2 * a.toReal), fun x hx => ?_⟩
  simp only [mem_preimage, mem_Iic, gaussRate] at hx
  have hs : ∑ i, x i ^ 2 / 2 ≤ a.toReal := by
    rw [← ENNReal.ofReal_toReal ha] at hx
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hx
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  have := Finset.single_le_sum (f := fun j => x j ^ 2 / 2) (fun j _ => by positivity)
    (Finset.mem_univ i)
  linarith

/-! ## The large-deviation principle -/

/-- `ε log P(A) ≤ 0` for a probability measure and `ε > 0`. -/
@[tmio T, powerlib_foundation] private theorem mul_log_nonpos {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ] (A : Set (Fin d → ℝ)) :
    (ε : EReal) * ENNReal.log (μ A) ≤ 0 := by
  have h : ENNReal.log (μ A) ≤ 0 := by
    rw [← ENNReal.log_one]; exact ENNReal.log_le_log prob_le_one
  simpa using mul_le_mul_of_nonneg_left h (by exact_mod_cast hε.le : (0 : EReal) ≤ ε)

/-- Upper bound: `limsup ε log P_ε(A) ≤ −inf_{cl A} |x|²/2`. -/
@[tmio T, powerlib_foundation] private theorem gaussLaw_upper (d : ℕ) (A : Set (Fin d → ℝ)) :
    limsup (fun ε : ℝ => ((id ε : ℝ) : EReal) * ENNReal.log (gaussLaw d ε A)) (𝓝[>] 0) ≤
      -(⨅ x ∈ closure A, ((gaussRate d x : ℝ≥0∞) : EReal)) := by
  set c := ⨅ x ∈ closure A, ((gaussRate d x : ℝ≥0∞) : EReal) with hc
  refine le_of_forall_gt_imp_ge_of_dense fun b hb => ?_
  induction b using EReal.rec with
  | bot => exact absurd hb not_lt_bot
  | top => exact le_top
  | coe r =>
    refine limsup_le_of_le (by isBoundedDefault) ?_
    by_cases hr : 0 ≤ r
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (mul_log_nonpos hε A).trans (EReal.coe_nonneg.mpr hr)
    push Not at hr
    have hrc : ((-r : ℝ) : EReal) < c := by
      rw [EReal.coe_neg]; exact EReal.neg_lt_comm.mp hb
    obtain ⟨e, he1, he2⟩ := exists_between hrc
    have he_top : e ≠ ⊤ := ne_top_of_lt he2
    have he_bot : e ≠ ⊥ := ne_bot_of_gt he1
    set a := e.toReal with ha
    have hae : (a : EReal) = e := EReal.coe_toReal he_top he_bot
    have har : -r < a := by rw [← hae] at he1; exact_mod_cast he1
    have ha0 : 0 < a := by linarith
    have hsubA : A ⊆ {x | 2 * a ≤ ∑ i, x i ^ 2} := by
      intro x hx
      have h1 : c ≤ ((gaussRate d x : ℝ≥0∞) : EReal) := iInf₂_le x (subset_closure hx)
      rw [coe_gaussRate] at h1
      have h2 : (a : EReal) < ((∑ i, x i ^ 2 / 2 : ℝ) : EReal) := hae ▸ he2.trans_le h1
      have h3 : a < ∑ i, x i ^ 2 / 2 := by exact_mod_cast h2
      simp only [mem_ofPred_eq]
      rw [← Finset.sum_div] at h3
      linarith
    set δ := (1 + r / a) / 2 with hδ
    have hra : -1 < r / a := by rw [lt_div_iff₀ ha0]; linarith
    have hra' : r / a < 0 := div_neg_of_neg_of_pos hr ha0
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    have hδ1 : δ ≤ 1 := by rw [hδ]; linarith
    have hη : 0 < r + (1 - δ) * a := by
      have : (1 - δ) * a = (a - r) / 2 := by rw [hδ]; field_simp; ring
      rw [this]; linarith
    set C := (d : ℝ) * Real.log (√δ)⁻¹ with hC
    have htend : Tendsto (fun ε : ℝ => ε * C) (𝓝[>] 0) (𝓝 0) := by
      have hcont : Continuous fun ε : ℝ => ε * C := continuous_id.mul continuous_const
      have := hcont.tendsto 0
      simp only [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, htend.eventually (gt_mem_nhds hη)] with ε hε hsmall
    have hbound := (measure_mono hsubA).trans (gaussLaw_sq_ge_le d hε hδ0 hδ1 a)
    have hexp : Real.exp (-(1 - δ) * a / ε) * (√δ)⁻¹ ^ d =
        Real.exp ((-(1 - δ) * a + ε * C) / ε) := by
      rw [add_div, Real.exp_add, hC, mul_div_cancel_left₀ _ hε.ne', Real.exp_nat_mul,
        Real.exp_log (inv_pos.mpr (Real.sqrt_pos.mpr hδ0))]
    rw [hexp] at hbound
    refine (mul_log_le_of_le_exp hε hbound).trans ?_
    exact_mod_cast (by linarith : -(1 - δ) * a + ε * C ≤ r)

/-- Lower bound at a point: `−|z|²/2 ≤ liminf ε log P_ε(G)` for `z` interior to `G`. -/
@[tmio T, powerlib_foundation] private theorem gaussLaw_lower_point (d : ℕ)
    (G : Set (Fin d → ℝ)) {z : Fin d → ℝ} (hz : z ∈ interior G) :
    ((-(∑ i, z i ^ 2 / 2) : ℝ) : EReal) ≤
      liminf (fun ε : ℝ => ((id ε : ℝ) : EReal) * ENNReal.log (gaussLaw d ε G)) (𝓝[>] 0) := by
  refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
  induction b using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd hb not_top_lt
  | coe r =>
    have hr : r < -(∑ i, z i ^ 2 / 2) := by exact_mod_cast hb
    refine le_liminf_of_le (by isBoundedDefault) ?_
    obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
    -- a radius with `−Σ (|zᵢ| + ρ)²/2 > r`
    set g : ℝ → ℝ := fun ρ => -(∑ i, (|z i| + ρ) ^ 2 / 2) with hg
    have hgc : Continuous g := by
      refine (continuous_finsetSum _ fun i _ => ?_).neg
      exact ((continuous_const.add continuous_id).pow 2).div_const 2
    have hg0 : g 0 = -(∑ i, z i ^ 2 / 2) := by simp [hg, sq_abs]
    have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), r < g ρ ∧ ρ < ρ₀ ∧ 0 < ρ := by
      have h1 : ∀ᶠ ρ in 𝓝 (0 : ℝ), r < g ρ :=
        (hgc.tendsto 0).eventually (lt_mem_nhds (by rw [hg0]; exact hr))
      have h2 : ∀ᶠ ρ in 𝓝 (0 : ℝ), ρ < ρ₀ := gt_mem_nhds hρ₀
      filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, self_mem_nhdsWithin]
        with ρ h1 h2 h3 using ⟨h1, h2, h3⟩
    obtain ⟨ρ, hgρ, hρρ₀, hρ⟩ := hev.exists
    -- the error term `d ε log(2ρ/√(2πε)) → 0`
    set h : ℝ → ℝ := fun ε => (d : ℝ) * (ε * (Real.log (2 * ρ) - Real.log (2 * π) / 2)) -
      (d : ℝ) / 2 * (ε * Real.log ε) with hh
    have hhc : Continuous h := by
      refine ((continuous_const.mul (continuous_id.mul continuous_const))).sub
        (continuous_const.mul Real.continuous_mul_log)
    have hh0 : h 0 = 0 := by simp [hh]
    have hη : 0 < g ρ - r := by linarith
    have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), -(g ρ - r) < h ε :=
      nhdsWithin_le_nhds ((hhc.tendsto 0).eventually (lt_mem_nhds (by rw [hh0]; linarith)))
    filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hsm
    have hε' : (0 : ℝ) < ε := hε
    -- the mass of the ball around `z`
    set c : ℝ := 2 * ρ * (√(2 * π * ε))⁻¹ with hcdef
    have hc0 : 0 < c := by positivity
    have hprod : ENNReal.ofReal (∏ i, (c * Real.exp (-(|z i| + ρ) ^ 2 / (2 * ε)))) ≤
        gaussLaw d ε G := by
      rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
      refine le_trans ?_ (measure_mono ((Metric.ball_subset_ball hρρ₀.le).trans hball))
      rw [gaussLaw, ball_pi _ hρ, Measure.pi_pi]
      refine Finset.prod_le_prod fun i _ => ?_
      have := gaussianReal_ball_ge hε' ρ (z i)
      rwa [← mul_assoc] at this
    have hexp : ∏ i, (c * Real.exp (-(|z i| + ρ) ^ 2 / (2 * ε))) =
        Real.exp ((h ε + g ρ) / ε) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.exp_sum, ← Real.exp_log hc0, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      have hl : Real.log c = Real.log (2 * ρ) - (Real.log (2 * π) + Real.log ε) / 2 := by
        rw [hcdef, Real.log_mul (by positivity) (by positivity), Real.log_inv,
          Real.log_sqrt (by positivity), Real.log_mul (by positivity) hε'.ne']
        ring
      have hsum : (∑ i, -(|z i| + ρ) ^ 2 / (2 * ε)) * ε = -(∑ i, (|z i| + ρ) ^ 2 / 2) := by
        rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        field_simp
      rw [eq_div_iff hε'.ne', add_mul, hsum, hl]
      simp only [hh, hg]
      ring
    rw [hexp] at hprod
    refine le_trans ?_ (le_mul_log_of_exp_le hε' hprod)
    exact_mod_cast (by linarith : r ≤ h ε + g ρ)

/-- **Gaussian large deviations**: `√ε Z` (`Z` standard Gaussian in `ℝᵈ`) satisfies the
large-deviation principle as `ε → 0⁺` with the good rate `|x|²/2`. -/
@[tmio T, powerlib_foundation] theorem isLDP_gaussLaw (d : ℕ) :
    IsLDP (𝓝[>] (0 : ℝ)) id (gaussLaw d) (gaussRate d) := by
  refine ⟨(continuous_gaussRate d).lowerSemicontinuous, fun A _ => gaussLaw_upper d A,
    fun G _ => ?_⟩
  rw [EReal.neg_le]
  refine le_iInf₂ fun z hz => ?_
  rw [EReal.neg_le, coe_gaussRate, ← EReal.coe_neg]
  exact gaussLaw_lower_point d G hz

end powerlib.Stochastic.LDP
