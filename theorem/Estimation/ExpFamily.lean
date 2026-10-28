import theorem.Estimation.Bayes
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Matrix.Mul

/-! # Exponential families and their conjugate priors

Exponential-family likelihoods factorise through the sufficient statistic `∑ T(dᵢ)`, and the
conjugate prior is updated by `(χ, n) ↦ (χ + ∑ T(dᵢ), n + N)`.

Scope.
* General probability, not an engineering result.
* Parameter space `Θ` with a base measure `ν`; natural parameter `η : Θ → ℝᵏ`, log-partition
  `A : Θ → ℝ`; data space `𝓧` with base density `h > 0` and sufficient statistic
  `T : 𝓧 → ℝᵏ`. One observation has likelihood `h(d) exp(η(θ)·T(d) - A(θ))`; `N` observations
  `d : Fin N → 𝓧` are conditionally i.i.d. (product likelihood `expFamLik`). The conjugate prior
  is `conjPrior ν η A χ n ∝ exp(η(θ)·χ - n A(θ)) ν(dθ)`. The normalising constant of the prior
  is assumed positive and finite.

Source: work-sync theory/T-bayesian-inference.md §1.4.5 (general exponential family →
conjugate family, update `χ_N = χ₀ + ∑ T(dᵢ)`, `ν_N = ν₀ + N`), §1.3 (exponential families have
the finite-dimensional sufficient statistic `∑ T(dᵢ)`).

Results.
* `expFamLik_eq`, `expFamLik_factorizesThrough` — exponential-family likelihoods factorise
  through the sufficient statistic `∑ T(dᵢ)` (Fisher–Neyman).
* `bayesPosterior_conjPrior` — conjugate update of an exponential family:
  `(χ, n) ↦ (χ + ∑ T(dᵢ), n + N)`.
-/

noncomputable section
namespace powerlib.Estimation
open MeasureTheory Real
open scoped ENNReal

variable {Θ 𝓧 : Type*} {mΘ : MeasurableSpace Θ} {k : ℕ}

/-- Unnormalised conjugate-prior density `exp(η(θ)·χ - n A(θ))`. -/
def conjDensity (η : Θ → Fin k → ℝ) (A : Θ → ℝ) (χ : Fin k → ℝ) (n : ℝ) (θ : Θ) : ℝ≥0∞ :=
  ENNReal.ofReal (exp (η θ ⬝ᵥ χ - n * A θ))

/-- Conjugate prior (normalised). -/
def conjPrior (ν : Measure Θ) (η : Θ → Fin k → ℝ) (A : Θ → ℝ) (χ : Fin k → ℝ) (n : ℝ) :
    Measure Θ :=
  bayesPosterior ν (conjDensity η A χ n)

/-- Likelihood of `N` conditionally i.i.d. exponential-family observations. -/
def expFamLik (h : 𝓧 → ℝ) (T : 𝓧 → Fin k → ℝ) (η : Θ → Fin k → ℝ) (A : Θ → ℝ) {N : ℕ}
    (d : Fin N → 𝓧) (θ : Θ) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (h (d i) * exp (η θ ⬝ᵥ T (d i) - A θ))

@[tmio T, powerlib_foundation] theorem measurable_conjDensity {η : Θ → Fin k → ℝ} {A : Θ → ℝ}
    (hη : Measurable η) (hA : Measurable A) (χ : Fin k → ℝ) (n : ℝ) :
    Measurable (conjDensity η A χ n) := by
  unfold conjDensity dotProduct
  fun_prop

/-- Exponential-family likelihoods factorise through the sufficient statistic `∑ T(dᵢ)`. -/
@[tmio T, powerlib_foundation] theorem expFamLik_eq (h : 𝓧 → ℝ) (hh : ∀ x, 0 < h x)
    (T : 𝓧 → Fin k → ℝ) (η : Θ → Fin k → ℝ) (A : Θ → ℝ) {N : ℕ} (d : Fin N → 𝓧) (θ : Θ) :
    expFamLik h T η A d θ =
      ENNReal.ofReal (∏ i, h (d i)) * conjDensity η A (∑ i, T (d i)) N θ := by
  unfold expFamLik conjDensity
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (mul_pos (hh _) (exp_pos _)).le),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => (hh _).le)]
  congr 1
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_sub_distrib, dotProduct_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The likelihood family `d ↦ expFamLik … d` factorises through `d ↦ ∑ T(dᵢ)` (Fisher–Neyman). -/
@[tmio T, powerlib_foundation] theorem expFamLik_factorizesThrough (h : 𝓧 → ℝ) (hh : ∀ x, 0 < h x)
    (T : 𝓧 → Fin k → ℝ) (η : Θ → Fin k → ℝ) (A : Θ → ℝ) (N : ℕ) :
    FactorizesThrough (fun d : Fin N → 𝓧 => expFamLik h T η A d) (fun d => ∑ i, T (d i)) :=
  ⟨fun t => conjDensity η A t N, fun d => ENNReal.ofReal (∏ i, h (d i)),
    fun _ => (ENNReal.ofReal_pos.mpr (Finset.prod_pos fun _ _ => hh _)).ne',
    fun _ => ENNReal.ofReal_ne_top, fun d θ => expFamLik_eq h hh T η A d θ⟩

/-- **Conjugate update of an exponential family**: `(χ, n) ↦ (χ + ∑ T(dᵢ), n + N)`. -/
@[tmio T, powerlib_foundation] theorem bayesPosterior_conjPrior {ν : Measure Θ} {η : Θ → Fin k → ℝ}
    {A : Θ → ℝ} (hη : Measurable η) (hA : Measurable A) (h : 𝓧 → ℝ) (hh : ∀ x, 0 < h x)
    (T : 𝓧 → Fin k → ℝ) {χ : Fin k → ℝ} {n : ℝ}
    (hZ0 : evidence ν (conjDensity η A χ n) ≠ 0) (hZt : evidence ν (conjDensity η A χ n) ≠ ∞)
    {N : ℕ} (d : Fin N → 𝓧) :
    bayesPosterior (conjPrior ν η A χ n) (expFamLik h T η A d) =
      conjPrior ν η A (χ + ∑ i, T (d i)) (n + N) := by
  have hf := measurable_conjDensity hη hA χ n
  have hL : Measurable (expFamLik h T η A d) := by
    have : expFamLik h T η A d =
        fun θ => ENNReal.ofReal (∏ i, h (d i)) * conjDensity η A (∑ i, T (d i)) N θ :=
      funext (expFamLik_eq h hh T η A d)
    rw [this]
    exact (measurable_conjDensity hη hA _ _).const_mul _
  have hc0 : ENNReal.ofReal (∏ i, h (d i)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Finset.prod_pos fun i _ => hh _)).ne'
  have hpt : ∀ θ, conjDensity η A χ n θ * expFamLik h T η A d θ =
      ENNReal.ofReal (∏ i, h (d i)) * conjDensity η A (χ + ∑ i, T (d i)) (n + N) θ := by
    intro θ
    rw [expFamLik_eq h hh, mul_left_comm]
    congr 1
    unfold conjDensity
    rw [← ENNReal.ofReal_mul (exp_pos _).le, ← Real.exp_add, dotProduct_add]
    congr 2
    ring
  rw [conjPrior, show bayesPosterior ν (conjDensity η A χ n) =
      (evidence ν (conjDensity η A χ n))⁻¹ • ν.withDensity (conjDensity η A χ n) from rfl,
    bayesPosterior_smul _ _ (ENNReal.inv_ne_zero.mpr hZt) (ENNReal.inv_ne_top.mpr hZ0),
    bayesPosterior_withDensity ν hf hL]
  simp_rw [hpt]
  rw [bayesPosterior_const_mul ν _ hc0 ENNReal.ofReal_ne_top, conjPrior]

end powerlib.Estimation
