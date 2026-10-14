import theorem.Estimation.Conjugate

/-! # Normal–Normal conjugacy (known observation variance)

A Gaussian prior on a mean with Gaussian observations of known variance gives a Gaussian
posterior with the boxed precision and mean formulas of the note.

Scope.
* General probability, not an engineering result.
* Mean `θ ∈ ℝ` with prior `N(μ₀, τ)` (`τ ≠ 0` is the prior *variance*, the note's `τ₀²`);
  observations `dᵢ ~ N(θ, v)` i.i.d. with known variance `v ≠ 0` (the note's `σ²`).

Source: work-sync theory/T-bayesian-inference.md §1.4.3.

Results.
* `bayesPosterior_normal_normal` — density level, any `N`: the posterior is `N(μ_N, τ_N)` with
  precision `1/τ_N = 1/τ + N/v` and `μ_N = τ_N (μ₀/τ + ∑ dᵢ / v)` (`∑ dᵢ = N d̄`), exactly the
  boxed formula of the note.
* `posterior_gaussianKernel_gaussianReal` — Mathlib posterior kernel: one observation, a.e. in
  the data.
-/

noncomputable section
namespace powerlib.Estimation
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

/-- Posterior variance `τ_N = (1/τ + N/v)⁻¹`. -/
def nnPostVar (τ v : ℝ≥0) (N : ℕ) : ℝ≥0 := (τ⁻¹ + N * v⁻¹)⁻¹

/-- Posterior mean `μ_N = τ_N (μ₀/τ + ∑ dᵢ / v)`. -/
def nnPostMean (μ₀ : ℝ) (τ v : ℝ≥0) {N : ℕ} (d : Fin N → ℝ) : ℝ :=
  nnPostVar τ v N * (μ₀ / τ + (∑ i, d i) / v)

@[powerlib_foundation] theorem coe_nnPostVar (τ v : ℝ≥0) (N : ℕ) :
    (nnPostVar τ v N : ℝ) = ((τ : ℝ)⁻¹ + N * (v : ℝ)⁻¹)⁻¹ := by
  simp [nnPostVar]

@[powerlib_foundation] theorem nnPostVar_ne_zero {τ : ℝ≥0} (hτ : τ ≠ 0) (v : ℝ≥0) (N : ℕ) :
    nnPostVar τ v N ≠ 0 := by
  have : 0 < τ⁻¹ + N * v⁻¹ := add_pos_of_pos_of_nonneg (inv_pos.mpr (pos_iff_ne_zero.mpr hτ))
    (zero_le)
  simpa [nnPostVar] using this.ne'

@[powerlib_foundation] private theorem sum_sq_sub (N : ℕ) (d : Fin N → ℝ) (θ : ℝ) :
    ∑ i, (d i - θ) ^ 2 = ∑ i, d i ^ 2 - 2 * θ * ∑ i, d i + N * θ ^ 2 := by
  have : ∀ i, (d i - θ) ^ 2 = d i ^ 2 - 2 * θ * d i + θ ^ 2 := fun i => by ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Completing the square: prior × likelihood is a θ-independent multiple of `N(μ_N, τ_N)`. -/
@[powerlib_foundation] theorem gaussianPDF_mul_prod_gaussianPDF {μ₀ : ℝ} {τ v : ℝ≥0} (hτ : τ ≠ 0)
    (hv : v ≠ 0) {N : ℕ} (d : Fin N → ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ, gaussianPDF μ₀ τ θ * ∏ i, gaussianPDF θ v (d i) =
      ENNReal.ofReal c * gaussianPDF (nnPostMean μ₀ τ v d) (nnPostVar τ v N) θ := by
  have hτ' : (0 : ℝ) < τ := lt_of_le_of_ne τ.2 (by simpa [eq_comm] using hτ)
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.2 (by simpa [eq_comm] using hv)
  set P : ℝ := (τ : ℝ)⁻¹ + N * (v : ℝ)⁻¹ with hP
  have hPpos : 0 < P := by positivity
  set M : ℝ := μ₀ / τ + (∑ i, d i) / v with hM
  have hVar : (nnPostVar τ v N : ℝ) = P⁻¹ := coe_nnPostVar τ v N
  have hMean : nnPostMean μ₀ τ v d = P⁻¹ * M := by rw [nnPostMean, hVar]
  set K : ℝ := -(μ₀ ^ 2 / (2 * τ)) - (∑ i, d i ^ 2) / (2 * v) + M ^ 2 / (2 * P) with hK
  refine ⟨(√(2 * π * τ))⁻¹ * (√(2 * π * v))⁻¹ ^ N * √(2 * π * P⁻¹) * exp K, by positivity,
    fun θ => ?_⟩
  simp only [gaussianPDF, gaussianPDFReal_def]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum, hVar, hMean]
  have hexp : -(θ - μ₀) ^ 2 / (2 * τ) + ∑ i, -(d i - θ) ^ 2 / (2 * v) =
      -(θ - P⁻¹ * M) ^ 2 / (2 * P⁻¹) + K := by
    rw [show ∑ i, -(d i - θ) ^ 2 / (2 * (v : ℝ)) = -(∑ i, (d i - θ) ^ 2) / (2 * v) by
      simp only [neg_div, Finset.sum_neg_distrib, ← Finset.sum_div], sum_sq_sub, hK, hM, hP]
    field_simp
    ring
  have hsq : 0 < √(2 * π * P⁻¹) := by positivity
  calc (√(2 * π * τ))⁻¹ * rexp (-(θ - μ₀) ^ 2 / (2 * τ)) *
        ((√(2 * π * v))⁻¹ ^ N * rexp (∑ i, -(d i - θ) ^ 2 / (2 * v)))
      = (√(2 * π * τ))⁻¹ * (√(2 * π * v))⁻¹ ^ N *
          rexp (-(θ - μ₀) ^ 2 / (2 * τ) + ∑ i, -(d i - θ) ^ 2 / (2 * v)) := by
        rw [Real.exp_add]; ring
    _ = _ := by
        rw [hexp, Real.exp_add]
        field_simp

/-- **Normal–Normal conjugacy** (density level, `N` observations). -/
@[powerlib_foundation] theorem bayesPosterior_normal_normal {μ₀ : ℝ} {τ v : ℝ≥0} (hτ : τ ≠ 0)
    (hv : v ≠ 0) {N : ℕ} (d : Fin N → ℝ) :
    bayesPosterior (gaussianReal μ₀ τ) (fun θ => ∏ i, gaussianPDF θ v (d i)) =
      gaussianReal (nnPostMean μ₀ τ v d) (nnPostVar τ v N) := by
  obtain ⟨c, hc, hfac⟩ := gaussianPDF_mul_prod_gaussianPDF (μ₀ := μ₀) hτ hv d
  have hL : Measurable fun θ => ∏ i, gaussianPDF θ v (d i) :=
    Finset.measurable_prod _ fun i _ => by simp only [gaussianPDF, gaussianPDFReal]; fun_prop
  rw [gaussianReal_of_var_ne_zero _ hτ, gaussianReal_of_var_ne_zero _ (nnPostVar_ne_zero hτ v N)]
  exact bayesPosterior_withDensity_eq (measurable_gaussianPDF μ₀ τ) hL
    (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top (Filter.Eventually.of_forall hfac)
    (lintegral_gaussianPDF_eq_one _ (nnPostVar_ne_zero hτ v N))

/-- Gaussian observation kernel `θ ↦ N(θ, v)`. -/
def gaussianKernel (v : ℝ≥0) : Kernel ℝ ℝ where
  toFun θ := gaussianReal θ v
  measurable' := measurable_gaussianReal.comp (measurable_id.prodMk measurable_const)

instance (v : ℝ≥0) : IsMarkovKernel (gaussianKernel v) :=
  ⟨fun θ => by change IsProbabilityMeasure (gaussianReal θ v); infer_instance⟩

/-- **Normal–Normal conjugacy, Mathlib posterior kernel** (one observation `x`):
`(gaussianKernel v)†N(μ₀, τ) =ᵐ x ↦ N(μ₁, τ₁)`, `1/τ₁ = 1/τ + 1/v`, `μ₁ = τ₁(μ₀/τ + x/v)`. -/
@[powerlib_foundation] theorem posterior_gaussianKernel_gaussianReal {μ₀ : ℝ} {τ v : ℝ≥0}
    (hτ : τ ≠ 0) (hv : v ≠ 0) :
    (gaussianKernel v)†(gaussianReal μ₀ τ) =ᵐ[gaussianKernel v ∘ₘ gaussianReal μ₀ τ]
      fun x => gaussianReal (nnPostMean μ₀ τ v (fun _ : Fin 1 => x)) (nnPostVar τ v 1) := by
  have hp : Measurable (Function.uncurry fun θ x : ℝ => gaussianPDF θ v x) := by
    unfold Function.uncurry; simp only [gaussianPDF, gaussianPDFReal]; fun_prop
  filter_upwards [posterior_ae_eq_bayesPosterior (μ := gaussianReal μ₀ τ)
    (κ := gaussianKernel v) (ν := volume) hp
    (fun θ => gaussianReal_of_var_ne_zero θ hv)] with x hx
  rw [hx, ← bayesPosterior_normal_normal hτ hv (fun _ : Fin 1 => x)]
  simp

end powerlib.Estimation
