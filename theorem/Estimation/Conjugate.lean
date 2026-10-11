import theorem.Estimation.Bayes
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Conjugate Bayesian updates

Source: work-sync `theory/T-bayesian-inference.md` §1.4.1 (Beta–Binomial), §1.4.2
(Gamma–Poisson), §1.4.3 (Normal–Normal, known variance), §1.4.5 (exponential family).

Foundation (general probability), not an engineering result.

Parameter space `ℝ` with Mathlib's `betaMeasure`, `gammaMeasure` (shape `a`, rate `r`),
`gaussianReal` (mean, variance in `ℝ≥0`). Models:
* `binomialKernel N θ = Bin(N, clamp θ)` on `ℕ`, `clamp = projIcc 0 1` (the Beta prior lives on
  `(0,1)`, where `clamp θ = θ`);
* `poissonIIDKernel N θ = ⊗ᵢ Po(max θ 0)` on `Fin N → ℕ` (i.i.d. counts);
* `gaussianKernel v θ = N(θ, v)` on `ℝ`, `v ≠ 0` known.

Results are stated both for the density-level `bayesPosterior` and, through
`posterior_ae_eq_bayesPosterior`, for Mathlib's posterior kernel `κ†μ` (a.e. in the data).
-/

noncomputable section
namespace powerlib.Estimation
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal unitInterval

variable {Θ : Type*} {mΘ : MeasurableSpace Θ}

/-- **Conjugacy lemma.** If prior density × likelihood is (a.e.) a constant multiple of a
normalised density `g`, the posterior is `ν.withDensity g`. -/
@[powerlib_foundation] theorem bayesPosterior_withDensity_eq {ν : Measure Θ} {f L g : Θ → ℝ≥0∞}
    (hf : Measurable f) (hL : Measurable L) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (hfac : ∀ᵐ θ ∂ν, f θ * L θ = c * g θ) (hg1 : ∫⁻ θ, g θ ∂ν = 1) :
    bayesPosterior (ν.withDensity f) L = ν.withDensity g := by
  rw [bayesPosterior_withDensity ν hf hL]
  have h1 : bayesPosterior ν (fun θ => f θ * L θ) = bayesPosterior ν (fun θ => c * g θ) := by
    unfold bayesPosterior evidence
    rw [lintegral_congr_ae hfac, withDensity_congr_ae hfac]
  rw [h1, bayesPosterior_const_mul ν g hc0 hct, bayesPosterior, evidence, hg1, inv_one, one_smul]

/-- A measure-valued map into a countable discrete space is measurable as soon as the masses of
singletons are measurable. -/
@[powerlib_foundation] theorem measurable_measure_of_singleton {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β] {f : α → Measure β}
    (h : ∀ b, Measurable fun a => f a {b}) : Measurable f := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have : ∀ a, f a s = ∑' b, s.indicator (fun b => f a {b}) b :=
    fun a => (Measure.tsum_indicator_apply_singleton (f a) s hs).symm
  simp_rw [this]
  refine Measurable.ennreal_tsum fun b => ?_
  by_cases hb : b ∈ s
  · simpa [Set.indicator_of_mem hb] using h b
  · simp [Set.indicator_of_notMem hb]

/-! ### Beta–Binomial -/

section BetaBinomial

/-- Binomial observation kernel `θ ↦ Bin(N, clamp θ)`. -/
def binomialKernel (N : ℕ) : Kernel ℝ ℕ where
  toFun θ := binomial N (Set.projIcc 0 1 zero_le_one θ)
  measurable' := by
    refine measurable_measure_of_singleton fun k => ?_
    simp_rw [binomial_singleton]
    refine ENNReal.measurable_ofReal.comp ?_
    have : Measurable fun θ : ℝ => ((Set.projIcc (0 : ℝ) 1 zero_le_one θ : I) : ℝ) :=
      (continuous_subtype_val.comp continuous_projIcc).measurable
    exact (measurable_const.mul (this.pow_const k)).mul ((measurable_const.sub this).pow_const _)

instance (N : ℕ) : IsMarkovKernel (binomialKernel N) :=
  ⟨fun θ => by simp only [binomialKernel, Kernel.coe_mk]; infer_instance⟩

@[powerlib_foundation] theorem binomialKernel_singleton (N k : ℕ) {θ : ℝ} (h0 : 0 < θ)
    (h1 : θ < 1) :
    binomialKernel N θ {k} = ENNReal.ofReal (N.choose k * θ ^ k * (1 - θ) ^ (N - k)) := by
  simp only [binomialKernel, Kernel.coe_mk, binomial_singleton]
  rw [Set.projIcc_of_mem _ ⟨h0.le, h1.le⟩]

@[powerlib_foundation] private theorem measurable_betaPDF (α β : ℝ) : Measurable (betaPDF α β) :=
  ENNReal.measurable_ofReal.comp (measurable_betaPDFReal α β)

/-- Prior density × binomial likelihood is a multiple of the updated Beta density. -/
@[powerlib_foundation] theorem betaPDF_mul_binomial {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (N k : ℕ) (θ : ℝ) :
    betaPDF α β θ * binomialKernel N θ {k} =
      ENNReal.ofReal (N.choose k * ProbabilityTheory.beta (α + k) (β + (N - k : ℕ)) /
        ProbabilityTheory.beta α β) * betaPDF (α + k) (β + (N - k : ℕ)) θ := by
  by_cases hθ : 0 < θ ∧ θ < 1
  · obtain ⟨h0, h1⟩ := hθ
    have hB := ProbabilityTheory.beta_pos hα hβ
    have hB' := ProbabilityTheory.beta_pos (by positivity : 0 < α + k)
      (by positivity : 0 < β + ((N - k : ℕ) : ℝ))
    rw [binomialKernel_singleton N k h0 h1, betaPDF_of_pos_lt_one h0 h1,
      betaPDF_of_pos_lt_one h0 h1, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have e1 : θ ^ (α + k - 1) = θ ^ (α - 1) * θ ^ k := by
      rw [show α + k - 1 = (α - 1) + (k : ℝ) by ring, Real.rpow_add h0, Real.rpow_natCast]
    have e2 : (1 - θ) ^ (β + ((N - k : ℕ) : ℝ) - 1) = (1 - θ) ^ (β - 1) * (1 - θ) ^ (N - k) := by
      rw [show β + ((N - k : ℕ) : ℝ) - 1 = (β - 1) + ((N - k : ℕ) : ℝ) by ring,
        Real.rpow_add (by linarith), Real.rpow_natCast]
    rw [e1, e2]
    field_simp
  · have hz : ∀ a b : ℝ, betaPDF a b θ = 0 := by
      intro a b
      rcases not_and_or.mp hθ with h | h
      · exact betaPDF_eq_zero_of_nonpos (not_lt.mp h)
      · exact betaPDF_eq_zero_of_one_le (not_lt.mp h)
    rw [hz, hz, zero_mul, mul_zero]

/-- **Beta–Binomial conjugacy** (density level): after `k` successes in `N` trials,
`Beta(α, β) ↦ Beta(α + k, β + N - k)`. -/
@[powerlib_foundation] theorem bayesPosterior_beta_binomial {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    {N k : ℕ} (hk : k ≤ N) :
    bayesPosterior (betaMeasure α β) (fun θ => binomialKernel N θ {k}) =
      betaMeasure (α + k) (β + (N - k : ℕ)) := by
  have hB := ProbabilityTheory.beta_pos hα hβ
  have hB' := ProbabilityTheory.beta_pos (by positivity : 0 < α + k)
    (by positivity : 0 < β + ((N - k : ℕ) : ℝ))
  have hchoose : (0 : ℝ) < N.choose k := by exact_mod_cast Nat.choose_pos hk
  refine bayesPosterior_withDensity_eq (measurable_betaPDF α β)
    (Kernel.measurable_coe _ (measurableSet_singleton k)) ?_ ENNReal.ofReal_ne_top
    (Filter.Eventually.of_forall (betaPDF_mul_binomial hα hβ N k))
    (lintegral_betaPDF_eq_one (by positivity) (by positivity))
  exact ENNReal.ofReal_pos.mpr (by positivity) |>.ne'

/-- **Beta–Binomial conjugacy, Mathlib posterior kernel**:
`(binomialKernel N)†Beta(α, β) =ᵐ k ↦ Beta(α + k, β + N - k)`. -/
@[powerlib_foundation] theorem posterior_binomialKernel_betaMeasure {α β : ℝ} (hα : 0 < α)
    (hβ : 0 < β) (N : ℕ) :
    have := isProbabilityMeasureBeta hα hβ
    (binomialKernel N)†(betaMeasure α β) =ᵐ[binomialKernel N ∘ₘ betaMeasure α β]
      fun k => betaMeasure (α + k) (β + N - k) := by
  have := isProbabilityMeasureBeta hα hβ
  have hle : ∀ᵐ k ∂(binomialKernel N ∘ₘ betaMeasure α β), k ≤ N := by
    refine Measure.ae_comp_of_ae_ae (measurableSet_le measurable_id measurable_const)
      (Filter.Eventually.of_forall fun θ => ?_)
    simpa [binomialKernel] using ae_le_of_hasLaw_binomial (HasLaw.id (μ := binomial N _))
  filter_upwards [posterior_ae_eq_bayesPosterior_of_countable (μ := betaMeasure α β)
    (κ := binomialKernel N), hle] with k hk hkN
  rw [hk, bayesPosterior_beta_binomial hα hβ hkN, Nat.cast_sub hkN]
  ring_nf

end BetaBinomial

end powerlib.Estimation
