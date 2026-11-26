import theorem.ParametricResonance.Wirtinger

/-! # The real one-sided form of the Fourier series of a periodic signal (TR-110 (2-13))

For a real signal the complex Fourier coefficients over a period are conjugate symmetric,
`A_{−m} = conj A_m`, the mean `A₀` is real and vanishes exactly for a zero-mean signal, and the
two-sided series `Σ_m A_m e^{jmω₀t}` equals the one-sided real series
`A₀ + Σ_{m≥1} 2|A_m| cos(mω₀t + ∠A_m)`: term by term (each pair `±m`), for every symmetric
partial sum, and for the full series whenever `Σ |A_m| < ∞`.

Scope.
* A real signal `f : ℝ → ℝ`, a period `T > 0`, `ω₀ = 2π/T`, and the coefficients
  `A_m = (1/T) ∫₀ᵀ e^{−jmω₀t} f(t) dt` (`SpecialFunctions.PeriodicWaves.coeff`, Mathlib's
  `fourierCoeffOn`). The identities hold for every real `f` (periodicity and continuity are not
  used); the conjugate symmetry is `ParametricResonance.Wirtinger.coeff_neg`. The phase `∠A_m` is
  `Complex.arg` (`∠0 = 0`). No model family.
* Convergence of the series to `f(t)` itself (for continuous periodic `f` with summable
  coefficients) is Mathlib's `has_pointwise_sum_fourier_series_of_summable` on `AddCircle T` and
  is not restated here.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §2.1.2, eq. (2-13)
(`f(t) = Σ_m A_m e^{jmω₀t} = Σ_{m≥1} 2|A_m| cos(mω₀t + ∠A_m)`, "where `A_{−m} = A_m*` and
`A₀ = 0`").

Corrections and sharpenings.
* The conjugate symmetry `A_{−m} = A_m*` is a consequence of `f` being real, not an assumption
  (`ParametricResonance.Wirtinger.coeff_neg`); `A₀ = 0` is the assumption of a zero-mean forcing
  (`coeff_zero_eq_zero_iff`). Without it the one-sided form carries the constant `A₀`
  (`sum_Icc_term`, `hasSum_term`).
* The equality of the two forms holds for the symmetric partial sums of every real signal and,
  for the full series, whenever `Σ_m |A_m| < ∞`; that the series represents `f(t)` itself needs
  more than the report states (e.g. continuity and summable coefficients, Mathlib's
  `has_pointwise_sum_fourier_series_of_summable`).

Results.
* `term`, `harmonic` — the two-sided term `A_m e^{jmω₀t}` and the one-sided harmonic
  `2|A_m| cos(mω₀t + ∠A_m)`.
* `add_conj_mul_exp` — `A e^{jθ} + conj A e^{−jθ} = 2|A| cos(θ + ∠A)` for every complex `A`.
* `coeff_zero_eq`, `coeff_zero_im`, `coeff_zero_eq_zero_iff`, `harmonic_zero` — `A₀ = (1/T)∫₀ᵀ f`
  is real, `A₀ = 0 ↔ ∫₀ᵀ f = 0`, and `2|A₀| cos ∠A₀ = 2A₀`.
* `term_add_term_neg` — termwise: `A_m e^{jmω₀t} + A_{−m} e^{−jmω₀t} = 2|A_m| cos(mω₀t + ∠A_m)`.
* `sum_Icc_term`, `sum_Icc_term_of_mean_zero` — symmetric partial sums:
  `Σ_{|m|≤M} A_m e^{jmω₀t} = A₀ + Σ_{m=1}^{M} 2|A_m| cos(mω₀t + ∠A_m)`, without `A₀` for a
  zero-mean signal.
* `summable_harmonic`, `hasSum_term` — if `Σ_m |A_m| < ∞`, the one-sided series converges
  absolutely and the two-sided series sums to `A₀ + Σ_{m≥1} 2|A_m| cos(mω₀t + ∠A_m)`.
-/

noncomputable section
namespace powerlib.LTI.FourierRealForm
open Complex Set Function ComplexConjugate
open powerlib.SpecialFunctions.PeriodicWaves

variable {T : ℝ}

/-- The two-sided term `A_m e^{jmω₀t}`, `ω₀ = 2π/T`. -/
def term (hT : 0 < T) (f : ℝ → ℝ) (m : ℤ) (t : ℝ) : ℂ :=
  coeff hT f m * Complex.exp (((m * (2 * Real.pi / T) * t : ℝ) : ℂ) * I)

/-- The one-sided harmonic `2|A_m| cos(mω₀t + ∠A_m)`. -/
def harmonic (hT : 0 < T) (f : ℝ → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  2 * ‖coeff hT f m‖ * Real.cos (m * (2 * Real.pi / T) * t + Complex.arg (coeff hT f m))

/-- `A e^{jθ} + conj A e^{−jθ} = 2|A| cos(θ + ∠A)`. -/
@[tmio T, powerlib_foundation] theorem add_conj_mul_exp (A : ℂ) (θ : ℝ) :
    A * Complex.exp ((θ : ℂ) * I) + conj A * Complex.exp (((-θ : ℝ) : ℂ) * I) =
      ((2 * ‖A‖ * Real.cos (θ + Complex.arg A) : ℝ) : ℂ) := by
  have hconj : conj A * Complex.exp (((-θ : ℝ) : ℂ) * I) =
      conj (A * Complex.exp ((θ : ℂ) * I)) := by
    rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 2
    push_cast
    ring
  rw [hconj, Complex.add_conj]
  congr 1
  have hc := Complex.norm_mul_cos_arg A
  have hs := Complex.norm_mul_sin_arg A
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [Real.cos_add]
  linear_combination (-(2 * Real.cos θ)) * hc + (2 * Real.sin θ) * hs

/-- The mean coefficient is the real mean value: `A₀ = (1/T) ∫₀ᵀ f`. -/
@[tmio T, powerlib_foundation] theorem coeff_zero_eq (hT : 0 < T) (f : ℝ → ℝ) :
    coeff hT f 0 = ((T⁻¹ * ∫ t in (0 : ℝ)..T, f t : ℝ) : ℂ) := by
  rw [coeff_eq_integral]
  simp only [kernelExp, Int.cast_zero, mul_zero, zero_div, neg_zero, zero_mul,
    Complex.exp_zero, one_mul]
  rw [intervalIntegral.integral_ofReal]
  push_cast
  ring

/-- `A₀` is real. -/
@[tmio T, powerlib_foundation] theorem coeff_zero_im (hT : 0 < T) (f : ℝ → ℝ) :
    (coeff hT f 0).im = 0 := by
  rw [coeff_zero_eq, Complex.ofReal_im]

/-- `A₀ = 0` exactly for a zero-mean signal. -/
@[tmio T, powerlib_foundation] theorem coeff_zero_eq_zero_iff (hT : 0 < T) (f : ℝ → ℝ) :
    coeff hT f 0 = 0 ↔ ∫ t in (0 : ℝ)..T, f t = 0 := by
  rw [coeff_zero_eq, Complex.ofReal_eq_zero, mul_eq_zero, or_iff_right (inv_ne_zero hT.ne')]

/-- The harmonic of order `0` is `2A₀`. -/
@[tmio T, powerlib_foundation] theorem harmonic_zero (hT : 0 < T) (f : ℝ → ℝ) (t : ℝ) :
    harmonic hT f 0 t = 2 * (coeff hT f 0).re := by
  simp only [harmonic, Nat.cast_zero, zero_mul, zero_add]
  rw [mul_assoc, Complex.norm_mul_cos_arg]

/-- Termwise: `A_m e^{jmω₀t} + A_{−m} e^{−jmω₀t} = 2|A_m| cos(mω₀t + ∠A_m)` for a real signal. -/
@[tmio T, powerlib_foundation] theorem term_add_term_neg (hT : 0 < T) (f : ℝ → ℝ) (m : ℕ)
    (t : ℝ) : term hT f m t + term hT f (-(m : ℤ)) t = (harmonic hT f m t : ℂ) := by
  rw [term, term, ParametricResonance.Wirtinger.coeff_neg, harmonic,
    ← add_conj_mul_exp (coeff hT f m) (m * (2 * Real.pi / T) * t)]
  congr 3
  push_cast
  ring

/-- Symmetric partial sums:
`Σ_{|m| ≤ M} A_m e^{jmω₀t} = A₀ + Σ_{m=1}^{M} 2|A_m| cos(mω₀t + ∠A_m)`. -/
@[tmio T, powerlib_foundation] theorem sum_Icc_term (hT : 0 < T) (f : ℝ → ℝ) (M : ℕ) (t : ℝ) :
    ∑ m ∈ Finset.Icc (-(M : ℤ)) M, term hT f m t =
      ((T⁻¹ * ∫ s in (0 : ℝ)..T, f s) + ∑ m ∈ Finset.Icc 1 M, harmonic hT f m t : ℝ) := by
  induction M with
  | zero =>
    simp only [Nat.cast_zero, neg_zero, Finset.Icc_self, Finset.sum_singleton, term,
      Int.cast_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one, coeff_zero_eq]
    simp
  | succ M ih =>
    have hset : Finset.Icc (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ) =
        insert ((M + 1 : ℕ) : ℤ) (insert (-((M + 1 : ℕ) : ℤ)) (Finset.Icc (-(M : ℤ)) M)) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    have h1 : ((M + 1 : ℕ) : ℤ) ∉ insert (-((M + 1 : ℕ) : ℤ)) (Finset.Icc (-(M : ℤ)) M) := by
      simp only [Finset.mem_insert, Finset.mem_Icc, not_or]
      push_cast
      omega
    have h2 : -((M + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(M : ℤ)) M := by
      simp only [Finset.mem_Icc]
      push_cast
      omega
    rw [hset, Finset.sum_insert h1, Finset.sum_insert h2, ih, ← add_assoc,
      term_add_term_neg, Finset.sum_Icc_succ_top (by omega)]
    push_cast
    ring

/-- For a zero-mean signal the symmetric partial sums are the one-sided real sums
`Σ_{m=1}^{M} 2|A_m| cos(mω₀t + ∠A_m)`. -/
@[tmio T, powerlib_foundation] theorem sum_Icc_term_of_mean_zero (hT : 0 < T) {f : ℝ → ℝ}
    (hf : ∫ t in (0 : ℝ)..T, f t = 0) (M : ℕ) (t : ℝ) :
    ∑ m ∈ Finset.Icc (-(M : ℤ)) M, term hT f m t =
      (∑ m ∈ Finset.Icc 1 M, harmonic hT f m t : ℝ) := by
  rw [sum_Icc_term, hf, mul_zero, zero_add]

@[tmio T, powerlib_foundation] private theorem norm_term (hT : 0 < T) (f : ℝ → ℝ) (m : ℤ)
    (t : ℝ) : ‖term hT f m t‖ = ‖coeff hT f m‖ := by
  rw [term, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- With absolutely summable coefficients the one-sided series converges absolutely. -/
@[tmio T, powerlib_foundation] theorem summable_harmonic (hT : 0 < T) {f : ℝ → ℝ}
    (hs : Summable fun m : ℤ => ‖coeff hT f m‖) (t : ℝ) :
    Summable fun n : ℕ => harmonic hT f (n + 1) t := by
  have hinj : Function.Injective (fun n : ℕ => ((n + 1 : ℕ) : ℤ)) := fun a b h => by
    simpa using h
  refine Summable.of_norm_bounded ((hs.comp_injective hinj).mul_left 2) fun n => ?_
  rw [harmonic, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_norm]
  have := Real.abs_cos_le_one (((n + 1 : ℕ) : ℝ) * (2 * Real.pi / T) * t +
    Complex.arg (coeff hT f ((n + 1 : ℕ) : ℤ)))
  simp only [Function.comp_apply]
  have h0 : 0 ≤ 2 * ‖coeff hT f ((n + 1 : ℕ) : ℤ)‖ := by positivity
  have h1 := mul_le_mul_of_nonneg_left this h0
  push_cast at h1 ⊢
  linarith

/-- The full series: if `Σ_m |A_m| < ∞`, the two-sided series sums to
`A₀ + Σ_{m≥1} 2|A_m| cos(mω₀t + ∠A_m)`. -/
@[tmio T, powerlib_foundation] theorem hasSum_term (hT : 0 < T) {f : ℝ → ℝ}
    (hs : Summable fun m : ℤ => ‖coeff hT f m‖) (t : ℝ) :
    HasSum (fun m : ℤ => term hT f m t)
      (((T⁻¹ * ∫ s in (0 : ℝ)..T, f s) + ∑' n : ℕ, harmonic hT f (n + 1) t : ℝ) : ℂ) := by
  have hsum : Summable fun m : ℤ => term hT f m t :=
    Summable.of_norm (by simpa only [norm_term] using hs)
  have hH := hsum.hasSum.nat_add_neg
  have hpair : (fun n : ℕ => term hT f n t + term hT f (-(n : ℤ)) t) =
      fun n : ℕ => (harmonic hT f n t : ℂ) := funext fun n => term_add_term_neg hT f n t
  rw [hpair] at hH
  have h1 := (hasSum_nat_add_iff' 1).mpr hH
  simp only [Finset.sum_range_one, harmonic_zero] at h1
  have h2 := Complex.hasSum_ofReal.mpr (summable_harmonic hT hs t).hasSum
  have hA0 : term hT f 0 t = coeff hT f 0 := by simp [term]
  have heq := h1.unique h2
  have hre : coeff hT f 0 = ((coeff hT f 0).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [coeff_zero_im]
  rw [hA0, hre] at heq
  have hmean : (coeff hT f 0).re = T⁻¹ * ∫ s in (0 : ℝ)..T, f s := by
    rw [coeff_zero_eq, Complex.ofReal_re]
  have hS : ∑' m : ℤ, term hT f m t =
      (((coeff hT f 0).re + ∑' n : ℕ, harmonic hT f (n + 1) t : ℝ) : ℂ) := by
    push_cast at heq ⊢
    linear_combination heq
  rw [← hmean, ← hS]
  exact hsum.hasSum

end powerlib.LTI.FourierRealForm
