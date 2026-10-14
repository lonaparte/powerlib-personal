import theorem.Attributes
import Mathlib.Probability.Kernel.Posterior
import Mathlib.Probability.ConditionalProbability

/-! # Bayes' theorem, sufficiency, sequential updating and the posterior kernel

Bayes' theorem at the density level and for Mathlib's posterior kernel, with the likelihood
principle, sufficiency, sequential updating, the posterior predictive and the Bayes factor.

Scope.
* General probability, not an engineering result.
* `bayesPosterior μ L = (∫ L dμ)⁻¹ • μ.withDensity L`: the normalised posterior for a prior
  measure `μ` on the parameter space and a likelihood `L : Θ → ℝ≥0∞` evaluated at the observed
  data. `evidence μ L = ∫ L dμ` is the marginal likelihood `p(D)`.
* Mathlib's posterior kernel `κ†μ` (`ProbabilityTheory.posterior`), defined by disintegration of
  the joint law; it is unique only `κ ∘ₘ μ`-almost everywhere.

Source: work-sync theory/T-bayesian-inference.md §1.2 (Bayes' theorem), §1.3 (likelihood
principle, Fisher–Neyman factorisation), §1.5 (posterior predictive), §1.6 (Bayes factor),
§1.7 (sequential updating).

Results.
* Thin Mathlib wrappers: `bayes_cond` (`ProbabilityTheory.cond_eq_inv_mul_cond_mul`),
  `posterior_ae_eq_withDensity` (`ProbabilityTheory.posterior_eq_withDensity`),
  `posterior_comp_ae_eq` (`ProbabilityTheory.posterior_comp`: posterior through a composite
  channel `θ → x → y`).
* `posterior_ae_eq_bayesPosterior` — for a dominated model `κ θ = ν.withDensity (p θ)` with
  jointly measurable density, Mathlib's posterior is a.e. the density-level `bayesPosterior`
  (Bayes' theorem in density form). `posterior_ae_eq_bayesPosterior_of_countable` specialises to
  countable data with `p θ x = κ θ {x}`.
* `bayesPosterior_const_mul`, `bayesPosterior_smul`, `bayesPosterior_eq_of_statistic_eq`,
  `posterior_ae_eq_of_factorizesThrough` — likelihood principle; prior scaling; sufficiency and
  its kernel form.
* `bayesPosterior_bayesPosterior`, `posterior_prod_ae_eq_sequential` — sequential updating.
* `compProd_posteriorPredictive` — posterior predictive.
* `posterior_odds`, `posterior_odds_toReal` — Bayes factor.

Corrections.
* §1.7: the note writes the simplification condition as `d_n ⊥ θ D_{1:n-1}`. The correct
  condition is conditional independence of the new datum from the past data *given* `θ`,
  `d_n ⊥ D_{1:n-1} | θ`. Formally this is the product kernel `κ₁ ×ₖ κ₂` (the joint likelihood
  factorises as `p₁(d₁|θ) p₂(d₂|θ)`), which is the hypothesis of
  `posterior_prod_ae_eq_sequential`.

Not formalized.
* Cox's theorem (§1.1) and Bernstein–von Mises (§1.10); the note also omits their regularity
  hypotheses.
-/

noncomputable section
namespace powerlib.Estimation
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {Θ : Type*} {mΘ : MeasurableSpace Θ}

/-! ### Thin wrappers of Mathlib's Bayes theorems -/

/-- **Bayes' theorem for events.** Wrapper of Mathlib
`ProbabilityTheory.cond_eq_inv_mul_cond_mul`. -/
@[powerlib_foundation] theorem bayes_cond {s t : Set Θ} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (μ : Measure Θ) [IsFiniteMeasure μ] :
    μ[t | s] = (μ s)⁻¹ * μ[s | t] * μ t :=
  cond_eq_inv_mul_cond_mul hs ht μ

section MathlibPosterior

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  [StandardBorelSpace Θ] [Nonempty Θ]

/-- **Bayes' theorem (Radon–Nikodym form).** Wrapper of Mathlib
`ProbabilityTheory.posterior_eq_withDensity`. -/
@[powerlib_foundation] theorem posterior_ae_eq_withDensity {κ : Kernel Θ 𝓧} [IsFiniteKernel κ]
    {μ : Measure Θ} [IsFiniteMeasure μ] [MeasurableSpace.CountableOrCountablyGenerated Θ 𝓧]
    (h_ac : ∀ᵐ θ ∂μ, κ θ ≪ κ ∘ₘ μ) :
    ∀ᵐ x ∂(κ ∘ₘ μ),
      (κ†μ) x = μ.withDensity (fun θ => κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) θ x) :=
  posterior_eq_withDensity h_ac

/-- **Posterior through a composite channel** `θ → x → y`. Wrapper of Mathlib
`ProbabilityTheory.posterior_comp`. -/
@[powerlib_foundation] theorem posterior_comp_ae_eq [StandardBorelSpace 𝓧] [Nonempty 𝓧]
    {κ : Kernel Θ 𝓧} [IsFiniteKernel κ] {μ : Measure Θ} [IsFiniteMeasure μ]
    {η : Kernel 𝓧 𝓨} [IsFiniteKernel η] :
    (η ∘ₖ κ)†μ =ᵐ[η ∘ₘ κ ∘ₘ μ] κ†μ ∘ₖ η†(κ ∘ₘ μ) :=
  posterior_comp

end MathlibPosterior

/-! ### Density-level posterior -/

/-- Evidence (marginal likelihood) `p(D) = ∫ L dμ`. -/
def evidence (μ : Measure Θ) (L : Θ → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ θ, L θ ∂μ

/-- Normalised Bayes posterior `L · μ / ∫ L dμ`. -/
def bayesPosterior (μ : Measure Θ) (L : Θ → ℝ≥0∞) : Measure Θ :=
  (evidence μ L)⁻¹ • μ.withDensity L

@[powerlib_foundation] private theorem inv_mul_self_mul {c a : ℝ≥0∞} (hc0 : c ≠ 0)
    (hct : c ≠ ∞) : (c * a)⁻¹ * c = a⁻¹ := by
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct), mul_comm, ← mul_assoc,
    ENNReal.mul_inv_cancel hc0 hct, one_mul]

@[powerlib_foundation] theorem bayesPosterior_apply (μ : Measure Θ) (L : Θ → ℝ≥0∞) {s : Set Θ}
    (hs : MeasurableSet s) :
    bayesPosterior μ L s = (evidence μ L)⁻¹ * ∫⁻ θ in s, L θ ∂μ := by
  rw [bayesPosterior, Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul]

@[powerlib_foundation] theorem bayesPosterior_univ_le_one (μ : Measure Θ) (L : Θ → ℝ≥0∞) :
    bayesPosterior μ L univ ≤ 1 := by
  rw [bayesPosterior_apply μ L MeasurableSet.univ, Measure.restrict_univ]
  exact ENNReal.inv_mul_le_one _

@[powerlib_foundation] theorem isProbabilityMeasure_bayesPosterior {μ : Measure Θ}
    {L : Θ → ℝ≥0∞} (h0 : evidence μ L ≠ 0) (htop : evidence μ L ≠ ∞) :
    IsProbabilityMeasure (bayesPosterior μ L) := by
  constructor
  rw [bayesPosterior_apply μ L MeasurableSet.univ, Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel h0 htop

/-- **Likelihood principle.** Proportional likelihoods give the same posterior. -/
@[powerlib_foundation] theorem bayesPosterior_const_mul (μ : Measure Θ) (L : Θ → ℝ≥0∞)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) :
    bayesPosterior μ (fun θ => c * L θ) = bayesPosterior μ L := by
  have hW : μ.withDensity (fun θ => c * L θ) = c • μ.withDensity L :=
    withDensity_smul' c L hct
  have hZ : evidence μ (fun θ => c * L θ) = c * evidence μ L :=
    lintegral_const_mul' c L hct
  rw [bayesPosterior, bayesPosterior, hW, hZ, smul_smul, inv_mul_self_mul hc0 hct]

/-- Rescaling the prior does not change the posterior. -/
@[powerlib_foundation] theorem bayesPosterior_smul (μ : Measure Θ) (L : Θ → ℝ≥0∞) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hct : c ≠ ∞) :
    bayesPosterior (c • μ) L = bayesPosterior μ L := by
  have hZ : evidence (c • μ) L = c * evidence μ L := lintegral_smul_measure c L
  rw [bayesPosterior, bayesPosterior, withDensity_smul_measure, hZ, smul_smul,
    inv_mul_self_mul hc0 hct]

/-- A prior with density `f` and likelihood `L` give the posterior of the base measure with
likelihood `f L`. -/
@[powerlib_foundation] theorem bayesPosterior_withDensity (μ : Measure Θ) {f L : Θ → ℝ≥0∞}
    (hf : Measurable f) (hL : Measurable L) :
    bayesPosterior (μ.withDensity f) L = bayesPosterior μ (fun θ => f θ * L θ) := by
  have hW : (μ.withDensity f).withDensity L = μ.withDensity (fun θ => f θ * L θ) :=
    (withDensity_mul μ hf hL).symm
  have hZ : evidence (μ.withDensity f) L = evidence μ (fun θ => f θ * L θ) :=
    lintegral_withDensity_eq_lintegral_mul μ hf hL
  rw [bayesPosterior, bayesPosterior, hW, hZ]

/-- **Sequential updating.** Yesterday's posterior is today's prior: updating with `L₁` and then
with `L₂` equals one update with the joint likelihood `L₁ L₂`. -/
@[powerlib_foundation] theorem bayesPosterior_bayesPosterior (μ : Measure Θ) {L₁ L₂ : Θ → ℝ≥0∞}
    (hL₁ : Measurable L₁) (hL₂ : Measurable L₂) (h0 : evidence μ L₁ ≠ 0)
    (htop : evidence μ L₁ ≠ ∞) :
    bayesPosterior (bayesPosterior μ L₁) L₂ = bayesPosterior μ (fun θ => L₁ θ * L₂ θ) := by
  rw [show bayesPosterior μ L₁ = (evidence μ L₁)⁻¹ • μ.withDensity L₁ from rfl,
    bayesPosterior_smul _ _ (ENNReal.inv_ne_zero.mpr htop) (ENNReal.inv_ne_top.mpr h0),
    bayesPosterior_withDensity μ hL₁ hL₂]

/-! ### Sufficiency (Fisher–Neyman) -/

section Sufficiency

variable {𝓧 𝓣 : Type*}

/-- A likelihood family `L x θ = p(x|θ)` factorises through the statistic `T`:
`L x θ = h x · g (T x) θ` with `0 < h x < ∞`. -/
def FactorizesThrough (L : 𝓧 → Θ → ℝ≥0∞) (T : 𝓧 → 𝓣) : Prop :=
  ∃ (g : 𝓣 → Θ → ℝ≥0∞) (h : 𝓧 → ℝ≥0∞),
    (∀ x, h x ≠ 0) ∧ (∀ x, h x ≠ ∞) ∧ ∀ x θ, L x θ = h x * g (T x) θ

/-- Under Fisher–Neyman factorisation the posterior is a function of `T(x)` only. -/
@[powerlib_foundation] theorem bayesPosterior_factorizesThrough (μ : Measure Θ)
    {L : 𝓧 → Θ → ℝ≥0∞} {T : 𝓧 → 𝓣} (hL : FactorizesThrough L T) :
    ∃ g : 𝓣 → Θ → ℝ≥0∞, ∀ x, bayesPosterior μ (L x) = bayesPosterior μ (g (T x)) := by
  obtain ⟨g, h, h0, htop, hfac⟩ := hL
  refine ⟨g, fun x => ?_⟩
  have : L x = fun θ => h x * g (T x) θ := funext (hfac x)
  rw [this, bayesPosterior_const_mul μ _ (h0 x) (htop x)]

/-- **Sufficiency.** Data with the same value of a sufficient statistic give the same
posterior: `p(θ | D) = p(θ | T(D))`. -/
@[powerlib_foundation] theorem bayesPosterior_eq_of_statistic_eq (μ : Measure Θ)
    {L : 𝓧 → Θ → ℝ≥0∞} {T : 𝓧 → 𝓣} (hL : FactorizesThrough L T) {x y : 𝓧}
    (hxy : T x = T y) : bayesPosterior μ (L x) = bayesPosterior μ (L y) := by
  obtain ⟨g, hg⟩ := bayesPosterior_factorizesThrough μ hL
  rw [hg x, hg y, hxy]

end Sufficiency

/-! ### Mathlib's posterior kernel is the density-level posterior -/

section Bridge

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

@[powerlib_foundation] private theorem measurable_evidence_restrict (μ : Measure Θ) [SFinite μ]
    {p : Θ → 𝓧 → ℝ≥0∞} (hp : Measurable (Function.uncurry p)) (s : Set Θ) :
    Measurable fun x => ∫⁻ θ in s, p θ x ∂μ :=
  hp.lintegral_prod_left' (μ := μ.restrict s)

/-- The posterior kernel `x ↦ bayesPosterior μ (p · x)` of a jointly measurable likelihood. -/
def bayesKernel (μ : Measure Θ) [SFinite μ] (p : Θ → 𝓧 → ℝ≥0∞)
    (hp : Measurable (Function.uncurry p)) : Kernel 𝓧 Θ where
  toFun x := bayesPosterior μ fun θ => p θ x
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [bayesPosterior_apply μ _ hs]
    have h1 : Measurable fun x => evidence μ fun θ => p θ x := by
      simpa [evidence] using measurable_evidence_restrict μ hp univ
    exact h1.inv.mul (measurable_evidence_restrict μ hp s)

instance (μ : Measure Θ) [SFinite μ] (p : Θ → 𝓧 → ℝ≥0∞) (hp : Measurable (Function.uncurry p)) :
    IsFiniteKernel (bayesKernel μ p hp) :=
  ⟨⟨1, ENNReal.one_lt_top, fun _ => bayesPosterior_univ_le_one _ _⟩⟩

@[powerlib_foundation] theorem bayesKernel_apply (μ : Measure Θ) [SFinite μ]
    (p : Θ → 𝓧 → ℝ≥0∞) (hp : Measurable (Function.uncurry p)) (x : 𝓧) :
    bayesKernel μ p hp x = bayesPosterior μ fun θ => p θ x := rfl

/-- The data marginal of a dominated model has density `x ↦ ∫ p(x|θ) dμ(θ)`. -/
@[powerlib_foundation] theorem comp_eq_withDensity_evidence {μ : Measure Θ} [SFinite μ]
    {κ : Kernel Θ 𝓧} {ν : Measure 𝓧} [SFinite ν] {p : Θ → 𝓧 → ℝ≥0∞}
    (hp : Measurable (Function.uncurry p)) (hκ : ∀ θ, κ θ = ν.withDensity (p θ)) :
    κ ∘ₘ μ = ν.withDensity fun x => evidence μ fun θ => p θ x := by
  ext t ht
  rw [Measure.bind_apply ht κ.measurable.aemeasurable, withDensity_apply _ ht]
  simp_rw [hκ, withDensity_apply _ ht]
  exact lintegral_lintegral_swap hp.aemeasurable

/-- **Bayes' theorem for dominated models.** If `κ θ = ν.withDensity (p θ)` with `p` jointly
measurable, then Mathlib's posterior kernel equals, `κ ∘ₘ μ`-a.e., the normalised density-level
posterior `bayesPosterior μ (p · x)`. -/
@[powerlib_foundation] theorem posterior_ae_eq_bayesPosterior [StandardBorelSpace Θ] [Nonempty Θ]
    {μ : Measure Θ} [IsFiniteMeasure μ] {κ : Kernel Θ 𝓧} [IsFiniteKernel κ]
    {ν : Measure 𝓧} [SFinite ν] {p : Θ → 𝓧 → ℝ≥0∞}
    (hp : Measurable (Function.uncurry p)) (hκ : ∀ θ, κ θ = ν.withDensity (p θ)) :
    ∀ᵐ x ∂(κ ∘ₘ μ), (κ†μ) x = bayesPosterior μ fun θ => p θ x := by
  set Z : 𝓧 → ℝ≥0∞ := fun x => evidence μ fun θ => p θ x with hZdef
  have hZ : Measurable Z := by
    simpa [hZdef, evidence] using measurable_evidence_restrict μ hp univ
  have hcomp := comp_eq_withDensity_evidence (μ := μ) hp hκ
  have hZfin : ∀ᵐ x ∂ν, Z x < ∞ := by
    refine ae_lt_top hZ ?_
    have : ∫⁻ x, Z x ∂ν = (κ ∘ₘ μ) univ := by
      rw [hcomp, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [this]
    exact measure_ne_top _ _
  have key : (κ ∘ₘ μ) ⊗ₘ bayesKernel μ p hp = (μ ⊗ₘ κ).map Prod.swap := by
    refine Measure.ext_prod fun {s} {t} hs ht => ?_
    rw [Measure.compProd_apply_prod hs ht, Measure.map_apply measurable_swap (hs.prod ht),
      Set.preimage_swap_prod, Measure.compProd_apply_prod ht hs]
    have hmeas : Measurable fun x => bayesKernel μ p hp x t :=
      Kernel.measurable_coe _ ht
    rw [hcomp, setLIntegral_withDensity_eq_setLIntegral_mul ν hZ hmeas hs]
    simp_rw [hκ, withDensity_apply _ hs]
    rw [lintegral_lintegral_swap (hp.aemeasurable)]
    refine setLIntegral_congr_fun_ae hs ?_
    filter_upwards [hZfin] with x hx _
    rw [Pi.mul_apply, bayesKernel_apply, bayesPosterior_apply μ _ ht]
    rcases eq_or_ne (Z x) 0 with h0 | h0
    · have hle : ∫⁻ θ in t, p θ x ∂μ ≤ Z x := setLIntegral_le_lintegral t _
      rw [h0] at hle
      rw [h0, zero_mul, le_antisymm hle (zero_le)]
    · rw [← mul_assoc, ENNReal.mul_inv_cancel h0 hx.ne, one_mul]
  have h := ae_eq_posterior_of_compProd_eq key
  filter_upwards [h] with x hx
  rw [← hx, bayesKernel_apply]

/-- Countable data: the likelihood is the probability of the observed point. -/
@[powerlib_foundation] theorem posterior_ae_eq_bayesPosterior_of_countable
    [StandardBorelSpace Θ] [Nonempty Θ] [Countable 𝓧] [MeasurableSingletonClass 𝓧]
    {μ : Measure Θ} [IsFiniteMeasure μ] {κ : Kernel Θ 𝓧} [IsFiniteKernel κ] :
    ∀ᵐ x ∂(κ ∘ₘ μ), (κ†μ) x = bayesPosterior μ fun θ => κ θ {x} := by
  have hp : Measurable (Function.uncurry fun θ (x : 𝓧) => κ θ {x}) :=
    measurable_from_prod_countable_left fun x => Kernel.measurable_coe κ (measurableSet_singleton x)
  refine posterior_ae_eq_bayesPosterior (ν := Measure.count) hp fun θ => ?_
  rw [count_withDensity]
  exact (Measure.sum_smul_dirac (κ θ)).symm

/-- **Sufficiency, kernel form.** For countable data, if the likelihood `θ ↦ κ θ {x}` factorises
through `T`, Mathlib's posterior is a.e. a function of `T x`. -/
@[powerlib_foundation] theorem posterior_ae_eq_of_factorizesThrough {𝓣 : Type*}
    [StandardBorelSpace Θ] [Nonempty Θ] [Countable 𝓧] [MeasurableSingletonClass 𝓧]
    {μ : Measure Θ} [IsFiniteMeasure μ] {κ : Kernel Θ 𝓧} [IsFiniteKernel κ] {T : 𝓧 → 𝓣}
    (hT : FactorizesThrough (fun x θ => κ θ {x}) T) :
    ∃ g : 𝓣 → Θ → ℝ≥0∞, ∀ᵐ x ∂(κ ∘ₘ μ), (κ†μ) x = bayesPosterior μ (g (T x)) := by
  obtain ⟨g, hg⟩ := bayesPosterior_factorizesThrough μ hT
  refine ⟨g, ?_⟩
  filter_upwards [posterior_ae_eq_bayesPosterior_of_countable (μ := μ) (κ := κ)] with x hx
  rw [hx, ← hg x]

section Product

variable {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨}

/-- Conditionally independent data `(x₁, x₂)` given `θ` (product kernel): the posterior uses the
product likelihood `p₁(x₁|θ) p₂(x₂|θ)`. -/
@[powerlib_foundation] theorem posterior_prod_ae_eq [StandardBorelSpace Θ] [Nonempty Θ]
    {μ : Measure Θ} [IsFiniteMeasure μ] {κ₁ : Kernel Θ 𝓧} {κ₂ : Kernel Θ 𝓨}
    [IsFiniteKernel κ₁] [IsFiniteKernel κ₂] {ν₁ : Measure 𝓧} {ν₂ : Measure 𝓨} [SFinite ν₁]
    [SFinite ν₂] {p₁ : Θ → 𝓧 → ℝ≥0∞} {p₂ : Θ → 𝓨 → ℝ≥0∞}
    (hp₁ : Measurable (Function.uncurry p₁)) (hp₂ : Measurable (Function.uncurry p₂))
    (hκ₁ : ∀ θ, κ₁ θ = ν₁.withDensity (p₁ θ)) (hκ₂ : ∀ θ, κ₂ θ = ν₂.withDensity (p₂ θ)) :
    ∀ᵐ z ∂((κ₁ ×ₖ κ₂) ∘ₘ μ),
      ((κ₁ ×ₖ κ₂)†μ) z = bayesPosterior μ fun θ => p₁ θ z.1 * p₂ θ z.2 := by
  have hp : Measurable (Function.uncurry fun θ (z : 𝓧 × 𝓨) => p₁ θ z.1 * p₂ θ z.2) := by
    have h1 : Measurable fun w : Θ × (𝓧 × 𝓨) => p₁ w.1 w.2.1 :=
      hp₁.comp (measurable_fst.prodMk measurable_snd.fst)
    have h2 : Measurable fun w : Θ × (𝓧 × 𝓨) => p₂ w.1 w.2.2 :=
      hp₂.comp (measurable_fst.prodMk measurable_snd.snd)
    exact h1.mul h2
  refine posterior_ae_eq_bayesPosterior (ν := ν₁.prod ν₂) hp fun θ => ?_
  rw [Kernel.prod_apply, hκ₁, hκ₂]
  exact prod_withDensity (hp₁.comp measurable_prodMk_left) (hp₂.comp measurable_prodMk_left)

/-- **Sequential Bayes for conditionally independent data** (`x₂ ⊥ x₁ | θ`): a.e., the
posterior given `(x₁, x₂)` is the update of the posterior given `x₁` by the likelihood of `x₂`. -/
@[powerlib_foundation] theorem posterior_prod_ae_eq_sequential [StandardBorelSpace Θ] [Nonempty Θ]
    {μ : Measure Θ} [IsFiniteMeasure μ] {κ₁ : Kernel Θ 𝓧} {κ₂ : Kernel Θ 𝓨}
    [IsFiniteKernel κ₁] [IsMarkovKernel κ₂] {ν₁ : Measure 𝓧} {ν₂ : Measure 𝓨} [SFinite ν₁]
    [SFinite ν₂] {p₁ : Θ → 𝓧 → ℝ≥0∞} {p₂ : Θ → 𝓨 → ℝ≥0∞}
    (hp₁ : Measurable (Function.uncurry p₁)) (hp₂ : Measurable (Function.uncurry p₂))
    (hκ₁ : ∀ θ, κ₁ θ = ν₁.withDensity (p₁ θ)) (hκ₂ : ∀ θ, κ₂ θ = ν₂.withDensity (p₂ θ)) :
    ∀ᵐ z ∂((κ₁ ×ₖ κ₂) ∘ₘ μ),
      ((κ₁ ×ₖ κ₂)†μ) z = bayesPosterior (bayesPosterior μ fun θ => p₁ θ z.1) fun θ => p₂ θ z.2 := by
  set Z : 𝓧 → ℝ≥0∞ := fun x => evidence μ fun θ => p₁ θ x with hZdef
  have hZ : Measurable Z := by
    simpa [hZdef, evidence] using measurable_evidence_restrict μ hp₁ univ
  have hcomp := comp_eq_withDensity_evidence (μ := μ) hp₁ hκ₁
  have hZfin : ∀ᵐ x ∂ν₁, Z x < ∞ := by
    refine ae_lt_top hZ ?_
    have : ∫⁻ x, Z x ∂ν₁ = (κ₁ ∘ₘ μ) univ := by
      rw [hcomp, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [this]
    exact measure_ne_top _ _
  set A : Set 𝓧 := {x | Z x = 0 ∨ Z x = ∞} with hAdef
  have hA : MeasurableSet A :=
    (measurableSet_eq_fun hZ measurable_const).union (measurableSet_eq_fun hZ measurable_const)
  have hA0 : (κ₁ ∘ₘ μ) A = 0 := by
    rw [hcomp, withDensity_apply _ hA]
    refine (setLIntegral_congr_fun_ae hA ?_).trans (lintegral_zero)
    filter_upwards [hZfin] with x hx hxA
    rcases hxA with h | h
    · exact h
    · exact absurd h hx.ne
  have hjoint : ((κ₁ ×ₖ κ₂) ∘ₘ μ) (A ×ˢ univ) = 0 := by
    rw [Measure.bind_apply (hA.prod MeasurableSet.univ) (Kernel.measurable _).aemeasurable]
    simp_rw [Kernel.prod_apply, Measure.prod_prod, measure_univ, mul_one]
    rw [← Measure.bind_apply hA (Kernel.measurable _).aemeasurable]
    exact hA0
  have hgood : ∀ᵐ z ∂((κ₁ ×ₖ κ₂) ∘ₘ μ), z.1 ∉ A := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) hjoint
    simp only [not_not, Set.mem_ofPred_eq] at hz
    exact ⟨hz, Set.mem_univ _⟩
  filter_upwards [posterior_prod_ae_eq hp₁ hp₂ hκ₁ hκ₂, hgood] with z hz hzA
  simp only [hAdef, Set.mem_ofPred_eq, not_or] at hzA
  have m1 : Measurable fun θ => p₁ θ z.1 := hp₁.comp measurable_prodMk_right
  have m2 : Measurable fun θ => p₂ θ z.2 := hp₂.comp measurable_prodMk_right
  rw [hz, bayesPosterior_bayesPosterior μ m1 m2 hzA.1 hzA.2]

end Product

end Bridge

/-! ### Posterior predictive -/

section Predictive

variable {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  [StandardBorelSpace Θ] [Nonempty Θ]

/-- Posterior predictive kernel `p(ỹ | x) = ∫ p(ỹ | θ) p(θ | x) dθ`. -/
def posteriorPredictive (κ : Kernel Θ 𝓧) (κ' : Kernel Θ 𝓨) (μ : Measure Θ) [IsFiniteMeasure μ]
    [IsFiniteKernel κ] : Kernel 𝓧 𝓨 :=
  κ' ∘ₖ κ†μ

instance (κ : Kernel Θ 𝓧) (κ' : Kernel Θ 𝓨) (μ : Measure Θ) [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel κ'] : IsFiniteKernel (posteriorPredictive κ κ' μ) := by
  unfold posteriorPredictive; infer_instance

/-- The posterior predictive disintegrates the joint law of `(x, ỹ)` when `ỹ ⊥ x | θ`
(product kernel `κ ×ₖ κ'`). -/
@[powerlib_foundation] theorem compProd_posteriorPredictive {κ : Kernel Θ 𝓧} [IsFiniteKernel κ]
    {κ' : Kernel Θ 𝓨} [IsFiniteKernel κ'] {μ : Measure Θ} [IsFiniteMeasure μ] :
    (κ ∘ₘ μ) ⊗ₘ posteriorPredictive κ κ' μ = (κ ×ₖ κ') ∘ₘ μ := by
  rw [posteriorPredictive, Measure.compProd_eq_parallelComp_comp_copy_comp,
    ← Kernel.parallelComp_id_left_comp_parallelComp, ← Measure.comp_assoc,
    parallelProd_posterior_comp_copy_comp, Measure.comp_assoc,
    Kernel.parallelComp_comp_parallelComp, Kernel.id_comp, Kernel.comp_id, Measure.comp_assoc,
    Kernel.parallelComp_comp_copy]

/-- Uniqueness: every conditional law of `ỹ` given `x` is a.e. the posterior predictive. -/
@[powerlib_foundation] theorem ae_eq_posteriorPredictive
    [MeasurableSpace.CountableOrCountablyGenerated 𝓧 𝓨]
    {κ : Kernel Θ 𝓧} [IsFiniteKernel κ] {κ' : Kernel Θ 𝓨} [IsFiniteKernel κ']
    {μ : Measure Θ} [IsFiniteMeasure μ] {ρ : Kernel 𝓧 𝓨} [IsFiniteKernel ρ]
    (h : (κ ∘ₘ μ) ⊗ₘ ρ = (κ ×ₖ κ') ∘ₘ μ) :
    ρ =ᵐ[κ ∘ₘ μ] posteriorPredictive κ κ' μ :=
  Kernel.ae_eq_of_compProd_eq (h.trans compProd_posteriorPredictive.symm)

end Predictive

/-! ### Bayes factor -/

section BayesFactor

variable {μ : Measure Θ} [IsFiniteMeasure μ] {D H₁ H₂ : Set Θ}

/-- **Posterior odds = Bayes factor × prior odds** (cross-multiplied form). -/
@[powerlib_foundation] theorem posterior_odds (hD : MeasurableSet D) (h₁ : MeasurableSet H₁)
    (h₂ : MeasurableSet H₂) :
    μ[H₁ | D] * (μ[D | H₂] * μ H₂) = μ[H₂ | D] * (μ[D | H₁] * μ H₁) := by
  rw [bayes_cond hD h₁, bayes_cond hD h₂]
  ring

/-- **Posterior odds = Bayes factor × prior odds** (real ratio form, `μ D ≠ 0`). -/
@[powerlib_foundation] theorem posterior_odds_toReal (hD : MeasurableSet D)
    (h₁ : MeasurableSet H₁) (h₂ : MeasurableSet H₂) (hD0 : μ D ≠ 0) :
    (μ[H₁ | D]).toReal / (μ[H₂ | D]).toReal =
      ((μ[D | H₁]).toReal / (μ[D | H₂]).toReal) * ((μ H₁).toReal / (μ H₂).toReal) := by
  rw [bayes_cond hD h₁, bayes_cond hD h₂]
  simp only [ENNReal.toReal_mul]
  have hk : ((μ D)⁻¹).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨ENNReal.inv_ne_zero.mpr (measure_ne_top μ D),
      ENNReal.inv_ne_top.mpr hD0⟩
  rw [mul_assoc, mul_assoc, mul_div_mul_left _ _ hk, mul_div_mul_comm]

end BayesFactor

end powerlib.Estimation
