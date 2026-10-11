import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.Variance

/-! # Cramér–Rao bound for Gaussian models: Fisher information by definition and a proved bound

Source: work-sync `theory/T-cramer-rao-bound.md` §1.1 (real scalar samples
`y_k = g_s ρ_k(θ) + n_k`, `n_k ~ N(0, σ_n²)` independent, log-likelihood
`ℓ = −Σ (y_k − g_s ρ_k)²/(2σ_n²)`, Fisher matrix `𝓘_ij = (g_s²/σ_n²) Σ_k ∂_iρ_k ∂_jρ_k`,
`Cov(θ̂) ⪰ 𝓘⁻¹`, prefactor `1` for real samples); `projects/basin-guard/notes/concepts/
detection-tolerance.md` §2 (same derivation, "the prefactor is derived, not copied").

Foundation (probability), not an engineering result.

What is proved.
* `score_hasDerivAt`, `fisherDiscrete_eq`: for the sampled model the score is
  `∂_iℓ = (g/σ²) Σ_k n_k ∂_iρ_k` (derivative of the log-likelihood along parameter direction `i`),
  and its second moment under independent `N(0, σ²)` noise (`Measure.pi`) is exactly
  `(g²/σ²) Σ_k ∂_iρ_k ∂_jρ_k`: the Fisher matrix computed from its definition.
* `gaussian_location_fisher`: for the scalar Gaussian location family `N(θ, v)` the Fisher
  information is `1/v`.
* `gaussian_location_crb`: **Cramér–Rao bound for the scalar Gaussian location family** — every
  estimator `T` that is unbiased for all `θ` and square integrable satisfies
  `E_θ[(T − θ)²] ≥ v = 1/𝓘(θ)`.  The proof is the Hammersley–Chapman–Robbins argument (finite
  shifts `θ ↦ θ + h` and Cauchy–Schwarz, `h² ≤ Var(T)(e^{h²/v} − 1)`, then `h → 0`), so no
  differentiation under the integral sign is needed.

Not proved (UNPROVED in the report): the general CRB `Cov(θ̂) ⪰ 𝓘⁻¹` for arbitrary regular
families and the multi-parameter Gaussian version; Mathlib has no Fisher-information theory.
-/

noncomputable section
namespace powerlib.Estimation

open MeasureTheory ProbabilityTheory Real Finset
open scoped NNReal

/-! ## Scalar Gaussian location family -/

section Location

variable {v : ℝ≥0}

/-- Integrability against a nondegenerate Gaussian law is integrability of `pdf · f`. -/
@[powerlib_foundation] theorem integrable_gaussianReal_iff (hv : v ≠ 0) {μ : ℝ} {f : ℝ → ℝ} :
    Integrable f (gaussianReal μ v) ↔ Integrable (fun x => gaussianPDFReal μ v x * f x) := by
  rw [gaussianReal_of_var_ne_zero _ hv, integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp [smul_eq_mul]

/-- Likelihood ratio `p_{θ+h}(y)/p_θ(y) = exp((h(y − θ) − h²/2)/v)`. -/
def lr (θ h : ℝ) (v : ℝ≥0) (y : ℝ) : ℝ := exp ((h * (y - θ) - h ^ 2 / 2) / v)

@[powerlib_foundation] theorem pdf_mul_lr (hv : v ≠ 0) (θ h y : ℝ) :
    gaussianPDFReal θ v y * lr θ h v y = gaussianPDFReal (θ + h) v y := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  unfold gaussianPDFReal lr
  rw [mul_assoc, ← exp_add]
  congr 2
  field_simp
  ring

@[powerlib_foundation] theorem pdf_mul_lr_sq (hv : v ≠ 0) (θ h y : ℝ) :
    gaussianPDFReal θ v y * lr θ h v y ^ 2 = exp (h ^ 2 / v) * gaussianPDFReal (θ + 2 * h) v y := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  unfold gaussianPDFReal lr
  rw [← Real.exp_nat_mul, mul_assoc, ← exp_add, mul_left_comm, ← exp_add]
  congr 2
  push_cast
  field_simp
  ring

@[powerlib_foundation] theorem measurable_lr (θ h : ℝ) (v : ℝ≥0) : Measurable (lr θ h v) := by
  unfold lr; fun_prop

@[powerlib_foundation] theorem integral_lr (hv : v ≠ 0) (θ h : ℝ) :
    ∫ y, lr θ h v y ∂(gaussianReal θ v) = 1 := by
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp_rw [smul_eq_mul, pdf_mul_lr hv]
  exact integral_gaussianPDFReal_eq_one _ hv

@[powerlib_foundation] theorem integral_lr_sq (hv : v ≠ 0) (θ h : ℝ) :
    ∫ y, lr θ h v y ^ 2 ∂(gaussianReal θ v) = exp (h ^ 2 / v) := by
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp_rw [smul_eq_mul, pdf_mul_lr_sq hv]
  rw [integral_const_mul, integral_gaussianPDFReal_eq_one _ hv, mul_one]

@[powerlib_foundation] theorem integrable_lr (hv : v ≠ 0) (θ h : ℝ) :
    Integrable (lr θ h v) (gaussianReal θ v) := by
  rw [integrable_gaussianReal_iff hv]
  simp_rw [pdf_mul_lr hv]
  exact integrable_gaussianPDFReal _ _

@[powerlib_foundation] theorem integrable_lr_sq (hv : v ≠ 0) (θ h : ℝ) :
    Integrable (fun y => lr θ h v y ^ 2) (gaussianReal θ v) := by
  rw [integrable_gaussianReal_iff hv]
  simp_rw [pdf_mul_lr_sq hv]
  exact (integrable_gaussianPDFReal _ _).const_mul _

/-- Change of measure: `E_θ[T · p_{θ+h}/p_θ] = E_{θ+h}[T]`. -/
@[powerlib_foundation] theorem integral_mul_lr (hv : v ≠ 0) (θ h : ℝ) (T : ℝ → ℝ) :
    ∫ y, T y * lr θ h v y ∂(gaussianReal θ v) = ∫ y, T y ∂(gaussianReal (θ + h) v) := by
  rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv]
  congr 1; funext y
  rw [smul_eq_mul, smul_eq_mul, ← pdf_mul_lr hv]; ring

@[powerlib_foundation] theorem integrable_mul_lr (hv : v ≠ 0) (θ h : ℝ) {T : ℝ → ℝ}
    (hT : Integrable T (gaussianReal (θ + h) v)) :
    Integrable (fun y => T y * lr θ h v y) (gaussianReal θ v) := by
  rw [integrable_gaussianReal_iff hv]
  rw [integrable_gaussianReal_iff hv] at hT
  refine hT.congr (ae_of_all _ fun y => ?_)
  simp only
  rw [← pdf_mul_lr hv]; ring

/-- Hammersley–Chapman–Robbins step: `h² ≤ E_θ[(T − θ)²] (e^{h²/v} − 1)`. -/
@[powerlib_foundation] theorem hcr_step (hv : v ≠ 0) {T : ℝ → ℝ} {θ : ℝ}
    (hT2 : MemLp T 2 (gaussianReal θ v))
    (hunb : ∀ θ', Integrable T (gaussianReal θ' v) ∧ ∫ y, T y ∂(gaussianReal θ' v) = θ')
    (h : ℝ) (hh : h ≠ 0) :
    h ^ 2 ≤ (∫ y, (T y - θ) ^ 2 ∂(gaussianReal θ v)) * (exp (h ^ 2 / v) - 1) := by
  set P := gaussianReal θ v
  set L := lr θ h v
  have hvpos : (0 : ℝ) < v := by positivity
  have hc : 0 < exp (h ^ 2 / v) - 1 := by
    have : 0 < h ^ 2 / v := div_pos (by positivity) hvpos
    linarith [add_one_lt_exp this.ne']
  -- integrability
  have iT : Integrable T P := (hunb θ).1
  have iT2 : Integrable (fun y => T y ^ 2) P := hT2.integrable_sq
  have iL : Integrable L P := integrable_lr hv θ h
  have iL2 : Integrable (fun y => L y ^ 2) P := integrable_lr_sq hv θ h
  have iTL : Integrable (fun y => T y * L y) P := integrable_mul_lr hv θ h (hunb (θ + h)).1
  -- the three moments
  have eT : ∫ y, T y ∂P = θ := (hunb θ).2
  have eL : ∫ y, L y ∂P = 1 := integral_lr hv θ h
  have eL2 : ∫ y, L y ^ 2 ∂P = exp (h ^ 2 / v) := integral_lr_sq hv θ h
  have eTL : ∫ y, T y * L y ∂P = θ + h := by
    rw [integral_mul_lr hv θ h T]; exact (hunb (θ + h)).2
  -- `a = E[(T − θ)²]`, and for every `t`, `0 ≤ E[(T − θ − t(L − 1))²]`
  set a := ∫ y, (T y - θ) ^ 2 ∂P
  have iXX : Integrable (fun y => (T y - θ) ^ 2) P := (hT2.sub (memLp_const θ)).integrable_sq
  have eXY : (fun y => (T y - θ) * (L y - 1)) =
      fun y => (T y * L y - T y) - (θ * L y - θ) := by funext y; ring
  have iXY : Integrable (fun y => (T y - θ) * (L y - 1)) P := by
    rw [eXY]; exact (iTL.sub iT).sub ((iL.const_mul θ).sub (integrable_const θ))
  have eYY : (fun y => (L y - 1) ^ 2) = fun y => (L y ^ 2 - 2 * L y) + 1 := by funext y; ring
  have iYY : Integrable (fun y => (L y - 1) ^ 2) P := by
    rw [eYY]; exact (iL2.sub (iL.const_mul 2)).add (integrable_const 1)
  have hXY : ∫ y, (T y - θ) * (L y - 1) ∂P = h := by
    have i1 : Integrable (fun y => T y * L y - T y) P := iTL.sub iT
    have i2 : Integrable (fun y => θ * L y - θ) P := (iL.const_mul θ).sub (integrable_const θ)
    rw [eXY, integral_sub i1 i2,
      integral_sub iTL iT, integral_sub (iL.const_mul θ) (integrable_const θ),
      integral_const_mul, eTL, eT, eL]
    simp
  have hYY : ∫ y, (L y - 1) ^ 2 ∂P = exp (h ^ 2 / v) - 1 := by
    have i3 : Integrable (fun y => L y ^ 2 - 2 * L y) P := iL2.sub (iL.const_mul 2)
    rw [eYY, integral_add i3 (integrable_const 1),
      integral_sub iL2 (iL.const_mul 2), integral_const_mul, eL2, eL]
    simp; ring
  have key : ∀ t : ℝ, 0 ≤ a - 2 * t * h + t ^ 2 * (exp (h ^ 2 / v) - 1) := by
    intro t
    have hnn : 0 ≤ ∫ y, (T y - θ - t * (L y - 1)) ^ 2 ∂P :=
      integral_nonneg fun y => sq_nonneg _
    have e : (fun y => (T y - θ - t * (L y - 1)) ^ 2) = fun y =>
        ((T y - θ) ^ 2 - (2 * t) * ((T y - θ) * (L y - 1))) + t ^ 2 * (L y - 1) ^ 2 := by
      funext y; ring
    have i4 : Integrable (fun y => (T y - θ) ^ 2 - 2 * t * ((T y - θ) * (L y - 1))) P :=
      iXX.sub (iXY.const_mul _)
    have i5 : Integrable (fun y => t ^ 2 * (L y - 1) ^ 2) P := iYY.const_mul _
    rw [e, integral_add i4 i5, integral_sub iXX (iXY.const_mul _), integral_const_mul,
      integral_const_mul, hXY, hYY] at hnn
    linarith
  have := key (h / (exp (h ^ 2 / v) - 1))
  have e : a - 2 * (h / (exp (h ^ 2 / v) - 1)) * h +
      (h / (exp (h ^ 2 / v) - 1)) ^ 2 * (exp (h ^ 2 / v) - 1) =
      a - h ^ 2 / (exp (h ^ 2 / v) - 1) := by
    field_simp; ring
  rw [e, sub_nonneg, div_le_iff₀ hc] at this
  exact this

/-- **Cramér–Rao bound, scalar Gaussian location family**: an estimator that is unbiased for every
`θ` and square integrable at `θ` has `E_θ[(T − θ)²] ≥ v`. -/
@[powerlib_foundation] theorem gaussian_location_crb (hv : v ≠ 0) {T : ℝ → ℝ} {θ : ℝ}
    (hT2 : MemLp T 2 (gaussianReal θ v))
    (hunb : ∀ θ', Integrable T (gaussianReal θ' v) ∧ ∫ y, T y ∂(gaussianReal θ' v) = θ') :
    (v : ℝ) ≤ ∫ y, (T y - θ) ^ 2 ∂(gaussianReal θ v) := by
  set a := ∫ y, (T y - θ) ^ 2 ∂(gaussianReal θ v)
  have hvpos : (0 : ℝ) < v := by positivity
  by_contra hlt
  push Not at hlt
  have ha0 : 0 ≤ a := integral_nonneg fun y => sq_nonneg _
  -- choose `x = h²/v = (v − a)/(2v) ∈ (0, 1/2]`
  set x := ((v : ℝ) - a) / (2 * v)
  have hx0 : 0 < x := div_pos (by linarith) (by positivity)
  have hx1 : x < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  set h := Real.sqrt (x * v)
  have hh2 : h ^ 2 = x * v := Real.sq_sqrt (by positivity)
  have hh : h ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have step := hcr_step hv hT2 hunb h hh
  rw [hh2, show x * (v : ℝ) / v = x by field_simp] at step
  -- `e^x − 1 ≤ x/(1 − x)` for `0 ≤ x < 1`
  have hexp : exp x * (1 - x) ≤ 1 := by
    have := add_one_le_exp (-x)
    have h2 : exp x * exp (-x) = 1 := by rw [← exp_add]; simp
    nlinarith [exp_pos x]
  have hexp' : exp x - 1 ≤ x / (1 - x) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  have : x * v ≤ a * (x / (1 - x)) :=
    le_trans step (mul_le_mul_of_nonneg_left hexp' ha0)
  -- hence `v (1 − x) ≤ a`, contradicting the choice of `x`
  have h3 : (v : ℝ) * (1 - x) ≤ a := by
    have h1x : 0 < 1 - x := by linarith
    rw [mul_div_assoc', le_div_iff₀ h1x] at this
    nlinarith
  have : (v : ℝ) * (1 - x) = ((v : ℝ) + a) / 2 := by
    simp only [x]; field_simp; ring
  linarith

/-- Score of the location family, `∂_θ log p_θ(y) = (y − θ)/v`. -/
@[powerlib_foundation] theorem gaussian_location_score (hv : v ≠ 0) (θ y : ℝ) :
    HasDerivAt (fun θ => log (gaussianPDFReal θ v y)) ((y - θ) / v) θ := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have e : (fun θ => log (gaussianPDFReal θ v y)) =
      fun θ => log ((√(2 * π * v))⁻¹) + -(y - θ) ^ 2 / (2 * v) := by
    funext θ
    unfold gaussianPDFReal
    rw [log_mul (inv_ne_zero (Real.sqrt_pos.mpr (by positivity)).ne') (exp_pos _).ne', log_exp]
  rw [e]
  have := (((hasDerivAt_id' θ).const_sub y).pow 2).neg.div_const (2 * (v : ℝ))
  convert! (this.const_add (log ((√(2 * π * v))⁻¹))) using 1
  field_simp
  ring

/-- **Fisher information of the location family**: `E_θ[((y − θ)/v)²] = 1/v`, so the bound of
`gaussian_location_crb` is `1/𝓘(θ)`. -/
@[powerlib_foundation] theorem gaussian_location_fisher (hv : v ≠ 0) (θ : ℝ) :
    ∫ y, ((y - θ) / v) ^ 2 ∂(gaussianReal θ v) = 1 / v := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hvar : ∫ y, (y - θ) ^ 2 ∂(gaussianReal θ v) = v := by
    have := variance_fun_id_gaussianReal (μ := θ) (v := v)
    rw [variance_eq_integral measurable_id'.aemeasurable] at this
    simpa [integral_id_gaussianReal] using this
  have e : (fun y => ((y - θ) / v) ^ 2) = fun y => (1 / (v : ℝ) ^ 2) * (y - θ) ^ 2 := by
    funext y; field_simp
  rw [e, integral_const_mul, hvar]
  field_simp

end Location

/-! ## Discrete Fisher matrix of the sampled model (§1.1) -/

section Discrete

variable {N p : ℕ} {v : ℝ≥0}

/-- Noise law: `N` independent `N(0, v)` samples. -/
abbrev noiseLaw (N : ℕ) (v : ℝ≥0) : Measure (Fin N → ℝ) := Measure.pi fun _ => gaussianReal 0 v

/-- Score of the sampled model at the true parameter, `∂_iℓ = (g/v) Σ_k n_k ∂_iρ_k`. -/
def score (g : ℝ) (v : ℝ≥0) (D : Matrix (Fin p) (Fin N) ℝ) (i : Fin p) (n : Fin N → ℝ) : ℝ :=
  g / v * ∑ k, n k * D i k

/-- The score is the derivative of the log-likelihood
`ℓ(θ) = −Σ (y_k − g ρ_k(θ))²/(2v)` along a parameter direction, evaluated at data
`y = g ρ(θ₀) + n` (here `d k` is the directional derivative of `ρ_k`). -/
@[powerlib_foundation] theorem score_hasDerivAt {ρ : Fin N → ℝ → ℝ} {d : Fin N → ℝ}
    (hρ : ∀ k, HasDerivAt (ρ k) (d k) 0) (g : ℝ) (n : Fin N → ℝ) :
    HasDerivAt (fun t => -∑ k, (g * ρ k 0 + n k - g * ρ k t) ^ 2 / (2 * (v : ℝ)))
      (g / v * ∑ k, n k * d k) 0 := by
  have h : ∀ k, HasDerivAt (fun t => (g * ρ k 0 + n k - g * ρ k t) ^ 2 / (2 * (v : ℝ)))
      (2 * (g * ρ k 0 + n k - g * ρ k 0) * (-(g * d k)) / (2 * (v : ℝ))) 0 := by
    intro k
    have := ((((hρ k).const_mul g).const_sub (g * ρ k 0 + n k)).pow 2).div_const (2 * (v : ℝ))
    convert! this using 1
    push_cast; ring
  have hs := (HasDerivAt.sum (u := Finset.univ) fun k _ => h k).neg
  convert! hs using 1
  · funext t; simp [Finset.sum_apply]
  · by_cases hv : (v : ℝ) = 0
    · simp [hv]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    congr 1; funext k
    field_simp
    ring

@[powerlib_foundation] theorem memLp_noise_coord (k : Fin N) :
    MemLp (fun n : Fin N → ℝ => n k) 2 (noiseLaw N v) := by
  have := (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := v) 2).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 v) k)
  simpa using this

/-- Second moments of the noise: `E[n_k n_l] = v δ_kl`. -/
@[powerlib_foundation] theorem noise_second_moment (k l : Fin N) :
    ∫ n, n k * n l ∂(noiseLaw N v) = if k = l then (v : ℝ) else 0 := by
  by_cases hkl : k = l
  · subst hkl
    simp only [↓reduceIte]
    have e : ∫ n, n k * n k ∂(noiseLaw N v) = ∫ x, x * x ∂(gaussianReal 0 v) := by
      have := integral_comp_eval (μ := fun _ : Fin N => gaussianReal 0 v) (i := k)
        (f := fun x : ℝ => x * x) (by fun_prop)
      simpa using this
    rw [e]
    have hvar := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := v)
    rw [variance_eq_integral measurable_id'.aemeasurable] at hvar
    simpa [integral_id_gaussianReal, sq] using hvar
  · simp only [hkl, ↓reduceIte]
    let f : Fin N → ℝ → ℝ := fun i x => if i = k ∨ i = l then x else 1
    have hprod : ∀ n : Fin N → ℝ, ∏ i, f i (n i) = n k * n l := by
      intro n
      rw [Fintype.prod_eq_mul k l hkl]
      · simp [f, hkl]
      · intro i hi; simp [f, hi.1, hi.2]
    have : ∫ n, n k * n l ∂(noiseLaw N v) = ∏ i, ∫ x, f i x ∂(gaussianReal 0 v) := by
      rw [← integral_fintype_prod_eq_prod]
      congr 1; funext n; exact (hprod n).symm
    rw [this, Finset.prod_eq_zero (Finset.mem_univ k)]
    simp [f, integral_id_gaussianReal]

/-- **Discrete Fisher matrix from its definition (§1.1)**: under `N` independent `N(0, v)` noise
samples, `E[s_i s_j] = (g²/v) Σ_k ∂_iρ_k ∂_jρ_k` (real samples: prefactor `1`, no factor `2`). -/
@[powerlib_foundation] theorem fisherDiscrete_eq (g : ℝ) (D : Matrix (Fin p) (Fin N) ℝ)
    (i j : Fin p) :
    ∫ n, score g v D i n * score g v D j n ∂(noiseLaw N v) = g ^ 2 / v * ∑ k, D i k * D j k := by
  have hint : ∀ k l, Integrable (fun n : Fin N → ℝ => n k * n l) (noiseLaw N v) :=
    fun k l => (memLp_noise_coord k).integrable_mul (memLp_noise_coord l)
  have e : (fun n => score g v D i n * score g v D j n) =
      fun n => ∑ k, ∑ l, (g / v) ^ 2 * (D i k * D j l) * (n k * n l) := by
    funext n
    simp only [score, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [e, integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    (hint k l).const_mul _]
  simp_rw [integral_finsetSum _ fun l _ => (hint _ l).const_mul _, integral_const_mul,
    noise_second_moment]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  by_cases hv : (v : ℝ) = 0
  · simp [hv]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp

end Discrete

end powerlib.Estimation
