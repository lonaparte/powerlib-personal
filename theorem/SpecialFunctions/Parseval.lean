import theorem.SpecialFunctions.Harmonics
import Mathlib.Analysis.Fourier.AddCircle

/-! # Parseval's identity for the harmonic coefficients (foundation)

For a period `T > 0` and `ω = 2π/T`, the harmonic coefficients `aₙ = harmonicCos v T n`,
`bₙ = harmonicSin v T n` of a real signal `v` on `[0, T]`
(`theorem/SpecialFunctions/Harmonics.lean`) are the real form of Mathlib's complex Fourier
coefficients on `[0, T]`, `cₘ = fourierCoeffOn _ v m = (1/T) ∫₀ᵀ e^{−jmωt} v(t) dt`
(`Mathlib/Analysis/Fourier/AddCircle.lean`): `cₙ = (aₙ − j bₙ)/2` and `c₋ₙ = (aₙ + j bₙ)/2` for
`n ≥ 0`. Mathlib's Parseval identity `Σ_{m ∈ ℤ} |cₘ|² = (1/T) ∫₀ᵀ |v|²` then reads

  `(1/T) ∫₀ᵀ v² = a₀²/4 + ½ Σ_{n ≥ 1} (aₙ² + bₙ²)`:

the mean square of the signal is the square of its mean `a₀/2` plus half the sum of the squared
harmonic amplitudes. With the peak phasor `Vₙ = aₙ − j bₙ` of the `n`-th harmonic
(`aₙ cos(nωt) + bₙ sin(nωt) = Re(Vₙ e^{jnωt})`), `aₙ² + bₙ² = |Vₙ|²`, so the mean square is
`(a₀/2)² + Σ_{n ≥ 1} |Vₙ|²/2`, the sum of the squared RMS values of the harmonics.

Scope.
* Generic real analysis; no model family and no engineering object. The signal `v : ℝ → ℝ` is
  arbitrary, square integrable on `(0, T]` for Parseval (`MemLp v 2` for the restriction of the
  Lebesgue measure to `Ioc 0 T`) and interval integrable on `[0, T]` for the coefficient
  identities; its values outside `[0, T]` play no role. The identity is the `L²` statement: the
  pointwise or uniform convergence of the Fourier series is not part of this module.

Source: Parseval's identity for the Fourier series on an interval, Mathlib's
`hasSum_sq_fourierCoeffOn` (`Mathlib/Analysis/Fourier/AddCircle.lean`), with
`e^{jθ} = cos θ + j sin θ` (`Complex.exp_mul_I`) and the folding of the sum over `ℤ` into a sum
over `ℕ` (`HasSum.nat_add_neg`).

Results.
* `fourierCoeffOn_natCast`: for `v` interval integrable on `[0, T]`, `T > 0`, `n : ℕ`,
  `fourierCoeffOn _ v n = (aₙ − j bₙ)/2`; `fourierCoeffOn_neg_natCast`:
  `fourierCoeffOn _ v (−n) = (aₙ + j bₙ)/2`.
* `hasSum_harmonic_sq` (Parseval): for `v` square integrable on `(0, T]`, `T > 0`, the series
  `Σ_{n ≥ 1} (aₙ² + bₙ²)/2` converges to `(1/T) ∫₀ᵀ v² − a₀²/4`; `mean_sq_eq_tsum`: the same as
  `(1/T) ∫₀ᵀ v² = a₀²/4 + Σ_{n ≥ 1} (aₙ² + bₙ²)/2`.
-/

noncomputable section
namespace powerlib.SpecialFunctions
open Real Set MeasureTheory

/-- `exp(2πj m x/T) = cos(mωx) + j sin(mωx)` with `ω = 2π/T`. -/
@[tmio T, powerlib_foundation] private lemma cexp_eq_cos_add_sin (T x : ℝ) (m : ℤ) :
    Complex.exp (2 * ↑π * Complex.I * ↑m * ↑x / ↑T) =
      ↑(cos (m * (2 * π / T) * x)) + ↑(sin (m * (2 * π / T) * x)) * Complex.I := by
  rw [show (2 * ↑π * Complex.I * ↑m * ↑x / ↑T : ℂ) = ((m * (2 * π / T) * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- The complex Fourier coefficient on `[0, T]` of a real signal, at the integer index `m`, in
terms of its cosine and sine integrals at the index `−m`. -/
@[tmio T, powerlib_foundation] private lemma fourierCoeffOn_ofReal {v : ℝ → ℝ} {T : ℝ}
    (hT : 0 < T) (hv : IntervalIntegrable v volume 0 T) (m : ℤ) :
    fourierCoeffOn hT (fun t => (v t : ℂ)) m =
      ((1 / T * ∫ t in (0 : ℝ)..T, v t * cos ((-m : ℤ) * (2 * π / T) * t) : ℝ) : ℂ) +
        ((1 / T * ∫ t in (0 : ℝ)..T, v t * sin ((-m : ℤ) * (2 * π / T) * t) : ℝ) : ℂ) *
          Complex.I := by
  have hc : IntervalIntegrable (fun t => v t * cos ((-m : ℤ) * (2 * π / T) * t)) volume 0 T :=
    hv.mul_continuousOn (by fun_prop)
  have hs : IntervalIntegrable (fun t => v t * sin ((-m : ℤ) * (2 * π / T) * t)) volume 0 T :=
    hv.mul_continuousOn (by fun_prop)
  have hc' : IntervalIntegrable (fun t => ((v t * cos ((-m : ℤ) * (2 * π / T) * t) : ℝ) : ℂ))
      volume 0 T := ⟨hc.1.ofReal, hc.2.ofReal⟩
  have hs₀ : IntervalIntegrable (fun t => ((v t * sin ((-m : ℤ) * (2 * π / T) * t) : ℝ) : ℂ))
      volume 0 T := ⟨hs.1.ofReal, hs.2.ofReal⟩
  rw [fourierCoeffOn_eq_integral _ _ hT]
  simp only [fourier_coe_apply, sub_zero, smul_eq_mul, cexp_eq_cos_add_sin, Complex.real_smul]
  rw [intervalIntegral.integral_congr
      (g := fun t => ((v t * cos ((-m : ℤ) * (2 * π / T) * t) : ℝ) : ℂ) +
        ((v t * sin ((-m : ℤ) * (2 * π / T) * t) : ℝ) : ℂ) * Complex.I)
      (fun t _ => by push_cast; ring),
    intervalIntegral.integral_add hc' (hs₀.mul_const Complex.I),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]
  push_cast
  ring

/-- The complex Fourier coefficient on `[0, T]` of a real signal at the index `n ≥ 0`:
`cₙ = (aₙ − j bₙ)/2`. -/
@[tmio T, powerlib_foundation] theorem fourierCoeffOn_natCast {v : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hv : IntervalIntegrable v volume 0 T) (n : ℕ) :
    fourierCoeffOn hT (fun t => (v t : ℂ)) n =
      ((harmonicCos v T n : ℂ) - harmonicSin v T n * Complex.I) / 2 := by
  rw [fourierCoeffOn_ofReal hT hv, harmonicCos, harmonicSin]
  simp only [Int.cast_neg, Int.cast_natCast, neg_mul, cos_neg, sin_neg, mul_neg,
    intervalIntegral.integral_neg]
  push_cast
  ring

/-- The complex Fourier coefficient on `[0, T]` of a real signal at the index `−n ≤ 0`:
`c₋ₙ = (aₙ + j bₙ)/2`, the conjugate of `cₙ`. -/
@[tmio T, powerlib_foundation] theorem fourierCoeffOn_neg_natCast {v : ℝ → ℝ} {T : ℝ}
    (hT : 0 < T) (hv : IntervalIntegrable v volume 0 T) (n : ℕ) :
    fourierCoeffOn hT (fun t => (v t : ℂ)) (-n) =
      ((harmonicCos v T n : ℂ) + harmonicSin v T n * Complex.I) / 2 := by
  rw [fourierCoeffOn_ofReal hT hv, harmonicCos, harmonicSin]
  simp only [neg_neg, Int.cast_natCast]
  push_cast
  ring

/-- Parseval's identity for the harmonic coefficients: for `v` square integrable on `(0, T]`,
`Σ_{n ≥ 1} (aₙ² + bₙ²)/2 = (1/T) ∫₀ᵀ v² − a₀²/4`. -/
@[tmio T, powerlib_foundation] theorem hasSum_harmonic_sq {v : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hv : MemLp v 2 (volume.restrict (Ioc 0 T))) :
    HasSum (fun n : ℕ => (harmonicCos v T (n + 1) ^ 2 + harmonicSin v T (n + 1) ^ 2) / 2)
      (1 / T * (∫ t in (0 : ℝ)..T, v t ^ 2) - harmonicCos v T 0 ^ 2 / 4) := by
  have hint : IntervalIntegrable v volume 0 T := by
    have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) T)) :=
      isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr (hv.integrable one_le_two)
  have hL2 : MemLp (fun t => (v t : ℂ)) 2 (volume.restrict (Ioc 0 T)) := hv.ofReal
  have hN := (hasSum_sq_fourierCoeffOn hT hL2).nat_add_neg
  have hterm : ∀ n : ℕ,
      ‖fourierCoeffOn hT (fun t => (v t : ℂ)) n‖ ^ 2 +
          ‖fourierCoeffOn hT (fun t => (v t : ℂ)) (-n)‖ ^ 2 =
        (harmonicCos v T n ^ 2 + harmonicSin v T n ^ 2) / 2 := fun n => by
    rw [fourierCoeffOn_natCast hT hint, fourierCoeffOn_neg_natCast hT hint, Complex.sq_norm,
      Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp
    ring
  have hb0 : harmonicSin v T 0 = 0 := by simp [harmonicSin]
  have h0 : ‖fourierCoeffOn hT (fun t => (v t : ℂ)) 0‖ ^ 2 = harmonicCos v T 0 ^ 2 / 4 := by
    have h := fourierCoeffOn_natCast hT hint 0
    rw [Nat.cast_zero] at h
    rw [h, hb0, Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hS : (T - 0)⁻¹ • ∫ x in (0 : ℝ)..T, ‖((v x : ℝ) : ℂ)‖ ^ 2 =
      1 / T * ∫ t in (0 : ℝ)..T, v t ^ 2 := by
    simp only [sub_zero, smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, one_div]
  simp only [hterm, h0, hS] at hN
  have h1 := (hasSum_nat_add_iff' 1).mpr hN
  convert h1 using 1
  simp [hb0]
  ring

/-- Parseval's identity, the mean square as a sum: for `v` square integrable on `(0, T]`,
`(1/T) ∫₀ᵀ v² = a₀²/4 + Σ_{n ≥ 1} (aₙ² + bₙ²)/2`. -/
@[tmio T, powerlib_foundation] theorem mean_sq_eq_tsum {v : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hv : MemLp v 2 (volume.restrict (Ioc 0 T))) :
    1 / T * (∫ t in (0 : ℝ)..T, v t ^ 2) = harmonicCos v T 0 ^ 2 / 4 +
      ∑' n : ℕ, (harmonicCos v T (n + 1) ^ 2 + harmonicSin v T (n + 1) ^ 2) / 2 := by
  rw [(hasSum_harmonic_sq hT hv).tsum_eq]
  ring

end powerlib.SpecialFunctions
