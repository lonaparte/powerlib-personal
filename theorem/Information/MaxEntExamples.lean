import theorem.Information.MaxEnt
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Closed-form MaxEnt examples: geometric, exponential, Gaussian

The geometric, exponential and Gaussian laws as closed-form maximum-entropy solutions.

Scope.
* General probability, not an engineering result.

Source: work-sync theory/T-maximum-entropy.md §1.2 (Gauss), §1.4 (exponential), §1.5
(geometric).

Results.
* `geometric_partition`, `geometric_gibbs_mass`, `geometric_mean`, `geometric_q_of_mean` —
  geometric (§1.5): on `k ∈ {1, 2, …}` with counting reference, `q = e^{-λ} ∈ (0,1)`:
  `Z = ∑_{k≥1} q^k = q/(1-q)`, Gibbs masses `q^k / Z = (1-q) q^{k-1}`, mean
  `∑ k (1-q) q^{k-1} = 1/(1-q)`, hence `q = 1 - 1/k̄`. Indices are shifted: `k = n + 1`, `n : ℕ`.
* `exponential_partition`, `exponential_first_moment`, `exponential_gibbs_mean`,
  `exponential_gibbs_density` — exponential (§1.4): reference Lebesgue on `(0, ∞)`, `λ > 0`:
  `Z = ∫ e^{-λx} = 1/λ`, `∫ x e^{-λx} = 1/λ²`, so the Gibbs mean is `1/λ` and the density is
  `λ e^{-λx}`.
* `tilted_gaussTilt`, `gaussianReal_maxEnt`, `relEntropy_gaussianReal` — Gaussian (§1.2):
  reference Lebesgue on `ℝ`; the Gibbs measure of the tilt `-(x-μ)²/(2v)` is `gaussianReal μ v`,
  and it maximises the differential entropy among all probability laws `p ≪ Lebesgue` with
  `E_p x = μ`, `E_p x² = μ² + v` (uniquely). Its relative entropy against Lebesgue is
  `-(1/2) - log √(2πv)`.
-/

noncomputable section
namespace powerlib.Information
open MeasureTheory Real ProbabilityTheory Set
open scoped ENNReal NNReal

section Geometric

variable {q : ℝ}

@[powerlib_foundation] theorem geometric_partition (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => q ^ (n + 1)) (q / (1 - q)) := by
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left q
  simpa [pow_succ', div_eq_mul_inv] using h

@[powerlib_foundation] theorem geometric_gibbs_mass (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    q ^ (n + 1) / (q / (1 - q)) = (1 - q) * q ^ n := by
  have : 1 - q ≠ 0 := by linarith
  field_simp
  ring

@[powerlib_foundation] theorem geometric_mean (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * ((1 - q) * q ^ n)) (1 / (1 - q)) := by
  have hn : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq0]
  have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one hn).mul_left (1 - q)
  have h2 := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (1 - q)
  have h := h1.add h2
  have hne : 1 - q ≠ 0 := by linarith
  convert h using 1
  · ext n; ring
  · field_simp; ring

/-- Inverting the mean constraint `k̄ = 1/(1-q)`. -/
@[powerlib_foundation] theorem geometric_q_of_mean {kbar : ℝ} (hq1 : q < 1)
    (h : kbar = 1 / (1 - q)) : q = 1 - 1 / kbar := by
  have hne : 1 - q ≠ 0 := by linarith
  rw [h]; field_simp; ring

end Geometric

section Exponential

variable {lam : ℝ}

@[powerlib_foundation] theorem exponential_partition (hlam : 0 < lam) :
    ∫ x in Ioi (0 : ℝ), exp (-lam * x) = 1 / lam := by
  rw [integral_exp_mul_Ioi (by linarith) 0]
  field_simp
  simp

@[powerlib_foundation] theorem exponential_first_moment (hlam : 0 < lam) :
    ∫ x in Ioi (0 : ℝ), x * exp (-lam * x) = 1 / lam ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := lam) two_pos hlam
  have hc : ∀ x ∈ Ioi (0 : ℝ), x ^ ((2 : ℝ) - 1) * exp (-(lam * x)) = x * exp (-lam * x) := by
    intro x _
    norm_num
  rw [setIntegral_congr_fun measurableSet_Ioi hc] at h
  have hG : Real.Gamma 2 = 1 := by
    have := Real.Gamma_nat_eq_factorial 1
    rw [show ((1 : ℕ) : ℝ) + 1 = 2 by norm_num] at this
    simpa using this
  rw [h, Real.rpow_two, hG]
  field_simp

/-- The Gibbs mean of the exponential example is `1/λ` (so `λ = 1/μ`). -/
@[powerlib_foundation] theorem exponential_gibbs_mean (hlam : 0 < lam) :
    (∫ x in Ioi (0 : ℝ), x * exp (-lam * x)) / (∫ x in Ioi (0 : ℝ), exp (-lam * x)) = 1 / lam := by
  rw [exponential_first_moment hlam, exponential_partition hlam]
  field_simp

/-- The Gibbs density `e^{-λx}/Z` is `(1/μ) e^{-x/μ}` with `μ = 1/λ`. -/
@[powerlib_foundation] theorem exponential_gibbs_density (hlam : 0 < lam) (x : ℝ) :
    exp (-lam * x) / (∫ y in Ioi (0 : ℝ), exp (-lam * y)) =
      (1 / (1 / lam)) * exp (-x / (1 / lam)) := by
  rw [exponential_partition hlam]
  field_simp

end Exponential

section Gaussian

variable {μ : ℝ} {v : ℝ≥0}

/-- The quadratic log-tilt `-(x-μ)²/(2v)`. -/
def gaussTilt (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ := -(x - μ) ^ 2 / (2 * v)

@[powerlib_foundation] theorem integral_exp_gaussTilt (hv : v ≠ 0) :
    ∫ x, exp (gaussTilt μ v x) = √(2 * π * v) := by
  have h := integral_gaussianPDFReal_eq_one μ hv
  rw [gaussianPDFReal_def, integral_const_mul] at h
  have hpos : 0 < √(2 * π * v) := by
    have : (0 : ℝ) < v := lt_of_le_of_ne v.2 (by simpa [eq_comm] using hv)
    positivity
  unfold gaussTilt
  field_simp at h
  simpa [neg_div] using h

@[powerlib_foundation] theorem integrable_exp_gaussTilt (hv : v ≠ 0) :
    Integrable (fun x => exp (gaussTilt μ v x)) := by
  have h := (integrable_gaussianPDFReal μ v).const_mul (√(2 * π * v))
  have hpos : 0 < √(2 * π * v) := by
    have : (0 : ℝ) < v := lt_of_le_of_ne v.2 (by simpa [eq_comm] using hv)
    positivity
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [gaussianPDFReal_def, gaussTilt]
  field_simp

/-- **The Gaussian is the Gibbs measure of the quadratic tilt** (Lebesgue reference). -/
@[powerlib_foundation] theorem tilted_gaussTilt (hv : v ≠ 0) :
    (volume : Measure ℝ).tilted (gaussTilt μ v) = gaussianReal μ v := by
  rw [gaussianReal_of_var_ne_zero μ hv, Measure.tilted, integral_exp_gaussTilt hv]
  congr 1
  ext x
  rw [gaussianPDF_def]
  congr 1
  simp only [gaussianPDFReal_def, gaussTilt]
  ring

@[powerlib_foundation] private theorem integral_gaussTilt {p : Measure ℝ} [IsProbabilityMeasure p]
    (h1 : Integrable (fun x => x) p) (h2 : Integrable (fun x => x ^ 2) p) :
    ∫ x, gaussTilt μ v x ∂p = -(∫ x, x ^ 2 ∂p - 2 * μ * ∫ x, x ∂p + μ ^ 2) / (2 * v) := by
  have : (fun x => gaussTilt μ v x) =
      fun x => (-(1 / (2 * (v : ℝ)))) * (x ^ 2 - 2 * μ * x + μ ^ 2) := by
    ext x; simp only [gaussTilt]; ring
  have hA : Integrable (fun a : ℝ => a ^ 2 - 2 * μ * a) p := h2.sub (h1.const_mul (2 * μ))
  rw [this, integral_const_mul, integral_add hA (integrable_const _),
    integral_sub h2 (h1.const_mul _), integral_const_mul]
  simp
  ring

@[powerlib_foundation] private theorem integrable_gaussTilt {p : Measure ℝ} [IsProbabilityMeasure p]
    (h1 : Integrable (fun x => x) p) (h2 : Integrable (fun x => x ^ 2) p) :
    Integrable (gaussTilt μ v) p := by
  have : gaussTilt μ v =
      fun x => (-(1 / (2 * (v : ℝ)))) * (x ^ 2 - 2 * μ * x + μ ^ 2) := by
    ext x; simp only [gaussTilt]; ring
  rw [this]
  exact ((h2.sub (h1.const_mul _)).add (integrable_const _)).const_mul _

@[powerlib_foundation] private theorem gaussian_moments :
    Integrable (fun x => x) (gaussianReal μ v) ∧ Integrable (fun x => x ^ 2) (gaussianReal μ v) ∧
      ∫ x, x ∂gaussianReal μ v = μ ∧ ∫ x, x ^ 2 ∂gaussianReal μ v = μ ^ 2 + v := by
  have hL2 : MemLp (fun x : ℝ => x) 2 (gaussianReal μ v) := memLp_id_gaussianReal 2
  refine ⟨(memLp_id_gaussianReal 1).integrable le_rfl, hL2.integrable_sq,
    integral_id_gaussianReal, ?_⟩
  have h := variance_eq_sub hL2
  rw [variance_fun_id_gaussianReal, integral_id_gaussianReal] at h
  simp only [Pi.pow_apply] at h
  linarith

/-- Relative entropy of `N(μ, v)` against Lebesgue: `-(1/2) - log √(2πv)`; the differential
entropy is `(1/2) + log √(2πv) = (1/2) log (2πe v)`. -/
@[powerlib_foundation] theorem relEntropy_gaussianReal (hv : v ≠ 0) :
    relEntropy (gaussianReal μ v) volume = -(1 / 2) - log √(2 * π * v) := by
  obtain ⟨h1, h2, hm, hs⟩ := gaussian_moments (μ := μ) (v := v)
  have hvpos : (0 : ℝ) < v := lt_of_le_of_ne v.2 (by simpa [eq_comm] using hv)
  have hq := integrable_gaussTilt (μ := μ) (v := v) h1 h2
  rw [← tilted_gaussTilt hv] at hq ⊢
  rw [relEntropy_tilted_self (integrable_exp_gaussTilt hv) hq, tilted_gaussTilt hv,
    integral_gaussTilt h1 h2, hm, hs, integral_exp_gaussTilt hv]
  field_simp
  ring

/-- **Gaussian maximum entropy** (§1.2): among probability laws `p ≪ Lebesgue` with mean `μ` and
second moment `μ² + v` (and integrable log-density), `N(μ, v)` has the largest differential
entropy, and it is the unique maximiser. -/
@[powerlib_foundation] theorem gaussianReal_maxEnt (hv : v ≠ 0) {p : Measure ℝ}
    [IsProbabilityMeasure p] (hpm : p ≪ volume) (hint : Integrable (llr p volume) p)
    (h1 : Integrable (fun x => x) p) (h2 : Integrable (fun x => x ^ 2) p)
    (hmean : ∫ x, x ∂p = μ) (hsec : ∫ x, x ^ 2 ∂p = μ ^ 2 + v) :
    relEntropy (gaussianReal μ v) volume ≤ relEntropy p volume ∧
      (relEntropy p volume = relEntropy (gaussianReal μ v) volume ↔ p = gaussianReal μ v) := by
  obtain ⟨g1, g2, gm, gs⟩ := gaussian_moments (μ := μ) (v := v)
  have hgq : Integrable (gaussTilt μ v) ((volume : Measure ℝ).tilted (gaussTilt μ v)) := by
    rw [tilted_gaussTilt hv]; exact integrable_gaussTilt g1 g2
  have hmom : ∫ x, gaussTilt μ v x ∂p =
      ∫ x, gaussTilt μ v x ∂((volume : Measure ℝ).tilted (gaussTilt μ v)) := by
    rw [tilted_gaussTilt hv, integral_gaussTilt h1 h2, integral_gaussTilt g1 g2, hmean, hsec,
      gm, gs]
  have hZ := integrable_exp_gaussTilt (μ := μ) hv
  have hle := relEntropy_tilted_le hZ hpm hint (integrable_gaussTilt h1 h2) hgq hmom
  have hiff := relEntropy_eq_relEntropy_tilted_iff hZ hpm hint (integrable_gaussTilt h1 h2) hgq hmom
  rw [tilted_gaussTilt hv] at hle hiff
  exact ⟨hle, hiff⟩

end Gaussian

end powerlib.Information
