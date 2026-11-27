import theorem.Periodic.CombinationResonance
import theorem.ParametricResonance.SubharmonicContent

/-! # Where the combination-resonance modes sit in frequency

`theorem/Periodic/CombinationResonance.lean` rotates two copies of a two-state system against
each other at the rate `ω`: the four-state system `ẋ = (A(t) ⊗ I + ω I ⊗ J) x` has the
transition matrix `Φ(t, s) ⊗ R(ω(t − s))` and the multipliers `μ e^{±iωT}`. This module locates
the growing mode in frequency. Start from a real base mode `M w = μ w` with `μ < 0` (the
half-frequency resonance of the base system) and lift it to `w ⊗ e₁`: the four-state mode is
`y(t) = x(t) ⊗ (cos ωt, sin ωt)`, `x(t) = Φ(t, 0) w`. With `ρ = ln |μ| / T` the normalized mode
`p(t) = e^{−ρt} y(t)` has the components `q(t) cos ωt`, `q(t) sin ωt`, where
`q(t) = e^{−ρt} x(t)` is `T`-antiperiodic (`q(t + T) = −q(t)`); equivalently
`y_{i,0} + i y_{i,1} = e^{(ρ + iω)t} q_i(t)`: growth `e^{ρt}`, a rotation at `ω`, and a
half-frequency factor. Multiplying by `cos ωt`, `sin ωt` shifts the spectrum of `q`, which lies at
`(k + ½)Ω` (`Ω = 2π/T`), to `(k + ½)Ω ± ω`.

* Rational rotation `ωT = 2πp/N`: over the window `[0, 2NT]` (Fourier index `m` at the frequency
  `mΩ/(2N)`) every component of `p` has coefficients only at `m ≡ N ± 2p (mod 2N)`, i.e. at
  `(k + ½)Ω ± ω`; when `sin ωT ≠ 0` (`N ∤ 2p`) none of them is on the locked lattice `(k/2)Ω`
  (`N ∣ m`); and some component has a nonzero coefficient at `(k + ½)Ω + ω`. The complex
  combination of the two rotated components carries exactly the half-integer coefficients of the
  base mode: `c_m(p_{i,0}) + i c_m(p_{i,1}) = c_{m−2p}(q_i)`.
* Any rotation rate (in particular irrational `ωT/2π`, where no finite window is adapted): the
  long-window mean content `(1/(nT)) ∫₀^{nT} e^{−iνt} p_{i,k}(t) dt` tends to `0` at every
  frequency `ν` off the set `(k + ½)Ω ± ω`, hence at every locked frequency `(k/2)Ω` when
  `sin ωT ≠ 0`, while at `ν = (k + ½)Ω + ω` the mean of `p_{i,0} + i p_{i,1}` equals the
  half-integer coefficient `c_{2k+1}(q_i)` over `[0, 2T]` for every `n ≥ 1`, and is nonzero for
  some `i, k`.
So the frequency signature of a combination resonance is unlocked from the pump: its lines are
displaced from the half-integer lattice by the rotation rate `ω`, the frozen frequency offset of
the two rotated copies.

Scope.
* The base system `ẋ = A(t) x` on `ℝ^X` (finite `X`), continuous real `T`-periodic `A`, `T > 0`,
  a real multiplier `μ < 0` with real eigenvector `w ≠ 0` of `M = Φ(T, 0)`; the rotated system
  `ẋ = realify (A(t)) (ω I) x` of `theorem/Periodic/CombinationResonance.lean` on
  `ℝ^{X × Fin 2}`, started at `liftRe w = w ⊗ (1, 0)`; times `t ≥ 0`.
* Fourier coefficients over windows `[0, L]` are `SpecialFunctions.PeriodicWaves.coeff`
  (index `m` at the frequency `2πm/L`); `windowMean T f ν n` is the mean
  `(1/(nT)) ∫₀^{nT} e^{−iνt} f(t) dt`.
* Generic mathematics; no model family, no measured record.

Source: combination resonance of multi-degree-of-freedom parametric systems (Nayfeh–Mook,
*Nonlinear Oscillations*, 1979, Ch. 5; Yakubovich–Starzhinskii, *Linear Differential Equations
with Periodic Coefficients*): the response frequencies `(k + ½)Ω ± ω` are combinations of the pump
and the natural frequencies; the rotated system and its multipliers
`Periodic.Combination.mem_spectrum_monodromy_realify_iff`; the window statements of
`theorem/ParametricResonance/Signature.lean` (`integral_floquet`,
`integral_window_eq_zero_of_root`) and the converse `Subharmonic.antiperiodic_mode_coeff_odd` of
`theorem/ParametricResonance/SubharmonicContent.lean`.

Results.
* `windowMean`, `tendsto_windowMean_zero` — a Floquet signal `f(t + T) = u f(t)`, `|u| = 1`, has
  vanishing long-window mean content at every `ν` with `u e^{−iνT} ≠ 1`;
  `windowMean_eq_of_eq_one` — at `u e^{−iνT} = 1` the mean is the one-period mean for every `n ≥ 1`.
* `coeff_mul_cos`, `coeff_mul_sin` — modulation on a window: multiplying by `cos(2πst/L)`,
  `sin(2πst/L)` shifts the coefficients by `±s`; `windowMean_mul_cos`, `windowMean_mul_sin` — the
  same for long-window means and any real `ω`.
* `coeff_window_nat_mul` — a `L`-periodic signal has `c_{Nm}` over `[0, NL]` equal to `c_m` over
  `[0, L]`; `coeff_window_antiperiodic` — a `T`-antiperiodic signal has, over `[0, 2NT]`,
  coefficients only at `m ≡ N (mod 2N)`.
* `liftRe`, `rotatedMode`, `rotated_mode_apply` — `y(t) = x(t) ⊗ (cos ωt, sin ωt)`;
  `normalized_mode` — `q(t) = e^{−ρt} x(t)` is the mode of `A − ρI`, `T`-antiperiodic;
  `rotated_mode_factor` — `y_{i,0} + i y_{i,1} = e^{(ρ + iω)t} q_i(t)` and
  `p_{i,0} = q_i cos ωt`, `p_{i,1} = q_i sin ωt`.
* `combination_window` — rational `ωT = 2πp/N`: content only at `m ≡ N ± 2p (mod 2N)`, none on
  the locked lattice when `N ∤ 2p`, nonzero content at some `m = 2Nk + N + 2p`.
* `combination_mean` — every `ω`: vanishing mean content off `(k + ½)Ω ± ω`, in particular on the
  locked lattice when `sin ωT ≠ 0`, and a nonzero mean at some `(k + ½)Ω + ω`.
-/

noncomputable section
namespace powerlib.Periodic.Combination

open Set Matrix Function Filter Topology Complex
open scoped Matrix.Norms.Operator Kronecker
open powerlib.Periodic
open powerlib.SpecialFunctions.PeriodicWaves (coeff kernelExp coeff_eq_integral)
open powerlib.ParametricResonance.NormalForm (quarter rot)

/-! ## Long-window means of Floquet signals -/

section Mean

variable {T : ℝ}

/-- The mean content `(1/(nT)) ∫₀^{nT} e^{−iνt} f(t) dt` of a complex signal at the frequency `ν`
over `n` periods. -/
def windowMean (T : ℝ) (f : ℝ → ℂ) (ν : ℝ) (n : ℕ) : ℂ :=
  (1 / (n * T) : ℂ) * ∫ x in (0 : ℝ)..n * T, cexp (-(ν * I) * x) * f x

/-- **Mean content off the Floquet frequencies vanishes.** A continuous signal with
`f(t + T) = u f(t)` (`t ≥ 0`, `|u| = 1`) has `windowMean T f ν n → 0` at every frequency with
`u e^{−iνT} ≠ 1`: the window integral is `(Σ_{j<n} rʲ) ∫₀ᵀ e^{−iνt} f` with `r = u e^{−iνT}`,
`|r| = 1`, `r ≠ 1`, and `|Σ_{j<n} rʲ| = |rⁿ − 1| / |r − 1| ≤ 2 / |r − 1|`
(`ParametricResonance.Signature.integral_floquet`). -/
@[tmio T, powerlib_foundation] theorem tendsto_windowMean_zero (hT : 0 < T) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ici 0)) {u : ℂ} (hu : ‖u‖ = 1)
    (hfu : ∀ t, 0 ≤ t → f (t + T) = u * f t) {ν : ℝ} (hne : u * cexp (-(ν * I) * T) ≠ 1) :
    Tendsto (windowMean T f ν) atTop (𝓝 0) := by
  set r := u * cexp (-(ν * I) * T) with hr
  have hr1 : ‖r‖ = 1 := by
    rw [hr, norm_mul, hu, one_mul, Complex.norm_exp]
    simp
  have hrne : r - 1 ≠ 0 := sub_ne_zero.mpr hne
  set I₁ := ∫ x in (0 : ℝ)..T, cexp (-(ν * I) * x) * f x
  set C := 2 / ‖r - 1‖ * ‖I₁‖ / T with hC
  have hbound : ∀ n : ℕ, ‖windowMean T f ν n‖ ≤ C / n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [windowMean]
    have hnT : (0 : ℝ) < n * T := mul_pos (Nat.cast_pos.mpr hn) hT
    rw [windowMean, ParametricResonance.Signature.integral_floquet hT.le hf hfu _ n, ← hr,
      geom_sum_eq hne]
    have hgeom : ‖(r ^ n - 1) / (r - 1)‖ ≤ 2 / ‖r - 1‖ := by
      rw [norm_div]
      gcongr
      calc ‖r ^ n - 1‖ ≤ ‖r ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hr1, one_pow, norm_one]; norm_num
    rw [norm_mul, norm_mul]
    have h1 : ‖(1 / (n * T) : ℂ)‖ = 1 / (n * T) := by
      rw [norm_div, norm_one]
      congr 1
      rw [show ((n : ℂ) * T) = ((n * T : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hnT]
    rw [h1, hC]
    calc 1 / (n * T) * (‖(r ^ n - 1) / (r - 1)‖ * ‖I₁‖) ≤ 1 / (n * T) * (2 / ‖r - 1‖ * ‖I₁‖) := by
          gcongr
      _ = 2 / ‖r - 1‖ * ‖I₁‖ / T / n := by field_simp
  refine squeeze_zero_norm hbound ?_
  exact tendsto_const_div_atTop_nhds_zero_nat C

/-- **Mean content at a Floquet frequency.** If `u e^{−iνT} = 1` the window integral over `n`
periods is `n` times the one-period integral, so `windowMean T f ν n = windowMean T f ν 1` for
every `n ≥ 1`. -/
@[tmio T, powerlib_foundation] theorem windowMean_eq_of_eq_one (hT : 0 < T) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ici 0)) {u : ℂ} (hfu : ∀ t, 0 ≤ t → f (t + T) = u * f t) {ν : ℝ}
    (heq : u * cexp (-(ν * I) * T) = 1) {n : ℕ} (hn : 0 < n) :
    windowMean T f ν n = windowMean T f ν 1 := by
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [windowMean, windowMean, ParametricResonance.Signature.integral_floquet hT.le hf hfu _ n, heq]
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_one,
    one_mul]
  field_simp

end Mean

/-! ## Fourier coefficients on a window: modulation and period multiples -/

section Window

variable {L : ℝ}

@[tmio T, powerlib_foundation] private theorem cexp_kernel_add (L : ℝ) (m s : ℤ) (x : ℝ) :
    cexp (kernelExp L m * x) * cexp (((2 * Real.pi * s * x / L : ℝ) : ℂ) * I) =
      cexp (kernelExp L (m - s) * x) := by
  rw [← Complex.exp_add]
  congr 1
  simp only [kernelExp]
  push_cast
  ring

@[tmio T, powerlib_foundation] private theorem cexp_kernel_sub (L : ℝ) (m s : ℤ) (x : ℝ) :
    cexp (kernelExp L m * x) * cexp (-(((2 * Real.pi * s * x / L : ℝ) : ℂ) * I)) =
      cexp (kernelExp L (m + s) * x) := by
  rw [← Complex.exp_add]
  congr 1
  simp only [kernelExp]
  push_cast
  ring

/-- **Modulation by a cosine on a window.** For `g` continuous on `[0, L]` and an integer `s`,
`c_m(g(t) cos(2πst/L)) = (c_{m−s}(g) + c_{m+s}(g)) / 2` over `[0, L]`. -/
@[tmio T, powerlib_foundation] theorem coeff_mul_cos (hL : 0 < L) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 L)) (s m : ℤ) :
    coeff hL (fun t => g t * Real.cos (2 * Real.pi * s * t / L)) m =
      (coeff hL g (m - s) + coeff hL g (m + s)) / 2 := by
  have hgi : ∀ k : ℤ, IntervalIntegrable (fun x : ℝ => cexp (kernelExp L k * x) * (g x : ℂ))
      MeasureTheory.volume 0 L := fun k =>
    ((Continuous.continuousOn (by fun_prop)).mul
      (Complex.continuous_ofReal.comp_continuousOn hg)).intervalIntegrable_of_Icc hL.le
  rw [coeff_eq_integral, coeff_eq_integral, coeff_eq_integral,
    ← mul_add, ← intervalIntegral.integral_add (hgi _) (hgi _)]
  rw [mul_div_assoc, ← intervalIntegral.integral_div]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [← cexp_kernel_add L m s x, ← cexp_kernel_sub L m s x]
  push_cast
  rw [Complex.cos]
  ring_nf

/-- **Modulation by a sine on a window.** For `g` continuous on `[0, L]` and an integer `s`,
`c_m(g(t) sin(2πst/L)) = (c_{m−s}(g) − c_{m+s}(g)) / (2i)` over `[0, L]`. -/
@[tmio T, powerlib_foundation] theorem coeff_mul_sin (hL : 0 < L) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 L)) (s m : ℤ) :
    coeff hL (fun t => g t * Real.sin (2 * Real.pi * s * t / L)) m =
      (coeff hL g (m - s) - coeff hL g (m + s)) / (2 * I) := by
  have hgi : ∀ k : ℤ, IntervalIntegrable (fun x : ℝ => cexp (kernelExp L k * x) * (g x : ℂ))
      MeasureTheory.volume 0 L := fun k =>
    ((Continuous.continuousOn (by fun_prop)).mul
      (Complex.continuous_ofReal.comp_continuousOn hg)).intervalIntegrable_of_Icc hL.le
  rw [coeff_eq_integral, coeff_eq_integral, coeff_eq_integral,
    ← mul_sub, ← intervalIntegral.integral_sub (hgi _) (hgi _)]
  rw [mul_div_assoc, ← intervalIntegral.integral_div]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [← cexp_kernel_add L m s x, ← cexp_kernel_sub L m s x]
  push_cast
  rw [Complex.sin]
  have hI : (2 * I) ≠ 0 := by simp
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- The coefficients over a window depend only on the window length. -/
@[tmio T, powerlib_foundation] private theorem coeff_length_congr {L₁ L₂ : ℝ} (h : L₁ = L₂)
    (h₁ : 0 < L₁) (h₂ : 0 < L₂) (g : ℝ → ℝ) (m : ℤ) : coeff h₁ g m = coeff h₂ g m := by
  subst h; rfl

/-- The coefficients over `[0, L]` depend only on the values on `[0, L]`. -/
@[tmio T, powerlib_foundation] private theorem coeff_congr_Icc (hL : 0 < L) {g h : ℝ → ℝ}
    (hgh : ∀ t ∈ Icc 0 L, g t = h t) (m : ℤ) : coeff hL g m = coeff hL h m := by
  rw [coeff_eq_integral, coeff_eq_integral]
  congr 1
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le hL.le] at hx
  simp only [hgh x hx]

/-- **Period multiples.** A continuous signal with `g(t + L) = g(t)` (`t ≥ 0`) has, over the
window `[0, NL]`, the coefficient `c_{Nm}` equal to the coefficient `c_m` over `[0, L]`
(`ParametricResonance.Signature.integral_floquet` with the ratio `e^{−2πim} = 1`). -/
@[tmio T, powerlib_foundation] theorem coeff_window_nat_mul (hL : 0 < L) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici 0)) (hp : ∀ t, 0 ≤ t → g (t + L) = g t) {N : ℕ} (hN : 0 < N)
    (m : ℤ) : coeff (mul_pos (Nat.cast_pos.mpr hN) hL) g (N * m) = coeff hL g m := by
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hk : kernelExp (N * L) (N * m) = kernelExp L m := by
    simp only [kernelExp]; push_cast; field_simp
  have hone : (1 : ℂ) * cexp (kernelExp L m * L) = 1 := by
    rw [one_mul, show kernelExp L m * L = (-m : ℤ) * (2 * Real.pi * I) by
      simp only [kernelExp]; push_cast; field_simp]
    exact Complex.exp_int_mul_two_pi_mul_I _
  have hgc : ContinuousOn (fun t => (g t : ℂ)) (Ici 0) :=
    Complex.continuous_ofReal.comp_continuousOn hg
  rw [coeff_eq_integral, coeff_eq_integral, hk,
    ParametricResonance.Signature.integral_floquet (f := fun t => (g t : ℂ)) hL.le hgc (μ := 1)
      (fun t ht => by simp only [hp t ht, one_mul]) _ N, hone]
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  push_cast
  field_simp

/-- **Antiperiodic signals on long windows.** A continuous `T`-antiperiodic signal
(`g(t + T) = −g(t)`, `t ≥ 0`) has, over `[0, 2NT]`, nonzero coefficients only at the indices
`m ≡ N (mod 2N)` — the frequencies `(k + ½)Ω`
(`ParametricResonance.Signature.integral_window_eq_zero_of_root` with `e^{2πiN/(2N)} = −1`). -/
@[tmio T, powerlib_foundation] theorem coeff_window_antiperiodic {T : ℝ} (hT : 0 < T) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici 0)) (ha : ∀ t, 0 ≤ t → g (t + T) = -g t) {N : ℕ} (hN : 0 < N)
    {m : ℤ} (hm : ¬ (2 * N : ℤ) ∣ m - N) :
    coeff (mul_pos (mul_pos two_pos (Nat.cast_pos.mpr hN)) hT) g m = 0 := by
  have h2N : 0 < 2 * N := by omega
  have hroot : ∀ t, 0 ≤ t → ((g (t + T) : ℝ) : ℂ) =
      cexp (2 * Real.pi * I * ((N : ℤ) : ℂ) / ((2 * N : ℕ) : ℂ)) * (g t : ℂ) := by
    intro t ht
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [show 2 * Real.pi * I * ((N : ℤ) : ℂ) / ((2 * N : ℕ) : ℂ) = Real.pi * I by
      push_cast; field_simp, Complex.exp_pi_mul_I, ha t ht]
    push_cast; ring
  have hgc : ContinuousOn (fun t => (g t : ℂ)) (Ici 0) :=
    Complex.continuous_ofReal.comp_continuousOn hg
  have h := ParametricResonance.Signature.integral_window_eq_zero_of_root (f := fun t => (g t : ℂ))
    hT hgc h2N hroot (m := m) (by push_cast; exact hm)
  rw [coeff_eq_integral]
  have e : ((2 * N : ℕ) : ℝ) * T = 2 * N * T := by push_cast; ring
  rw [e] at h
  rw [show kernelExp (2 * N * T) m = -(2 * Real.pi * I * m / ((2 * N : ℕ) * T)) by
    simp only [kernelExp]; push_cast; ring, h, mul_zero]

end Window

/-! ## Means under modulation -/

section MeanModulation

variable {T : ℝ}

/-- Modulating a real signal by `cos ωt` splits its mean content between `ν ∓ ω`. -/
@[tmio T, powerlib_foundation] theorem windowMean_mul_cos {g : ℝ → ℝ} (hg : ContinuousOn g (Ici 0))
    (hT : 0 ≤ T) (ω ν : ℝ) (n : ℕ) :
    windowMean T (fun t => ((g t * Real.cos (ω * t) : ℝ) : ℂ)) ν n =
      (windowMean T (fun t => (g t : ℂ)) (ν - ω) n + windowMean T (fun t => (g t : ℂ)) (ν + ω) n) / 2 := by
  have hnT : (0 : ℝ) ≤ n * T := mul_nonneg (Nat.cast_nonneg n) hT
  have hgi : ∀ lam : ℝ, IntervalIntegrable (fun x : ℝ => cexp (-(lam * I) * x) * (g x : ℂ))
      MeasureTheory.volume 0 (n * T) := fun lam =>
    ((Continuous.continuousOn (by fun_prop)).mul ((Complex.continuous_ofReal.comp_continuousOn hg).mono
      Icc_subset_Ici_self)).intervalIntegrable_of_Icc hnT
  simp only [windowMean]
  rw [← mul_add, ← intervalIntegral.integral_add (hgi _) (hgi _), mul_div_assoc,
    ← intervalIntegral.integral_div]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  push_cast
  rw [Complex.cos, show -((↑ν - ↑ω) * I) * (x : ℂ) = -(↑ν * I) * ↑x + ↑ω * ↑x * I by ring,
    show -((↑ν + ↑ω) * I) * (x : ℂ) = -(↑ν * I) * ↑x + -(↑ω * ↑x) * I by ring,
    Complex.exp_add, Complex.exp_add]
  ring

/-- Modulating a real signal by `sin ωt` splits its mean content between `ν ∓ ω`. -/
@[tmio T, powerlib_foundation] theorem windowMean_mul_sin {g : ℝ → ℝ} (hg : ContinuousOn g (Ici 0))
    (hT : 0 ≤ T) (ω ν : ℝ) (n : ℕ) :
    windowMean T (fun t => ((g t * Real.sin (ω * t) : ℝ) : ℂ)) ν n =
      (windowMean T (fun t => (g t : ℂ)) (ν - ω) n -
        windowMean T (fun t => (g t : ℂ)) (ν + ω) n) / (2 * I) := by
  have hnT : (0 : ℝ) ≤ n * T := mul_nonneg (Nat.cast_nonneg n) hT
  have hgi : ∀ lam : ℝ, IntervalIntegrable (fun x : ℝ => cexp (-(lam * I) * x) * (g x : ℂ))
      MeasureTheory.volume 0 (n * T) := fun lam =>
    ((Continuous.continuousOn (by fun_prop)).mul ((Complex.continuous_ofReal.comp_continuousOn hg).mono
      Icc_subset_Ici_self)).intervalIntegrable_of_Icc hnT
  simp only [windowMean]
  rw [← mul_sub, ← intervalIntegral.integral_sub (hgi _) (hgi _), mul_div_assoc,
    ← intervalIntegral.integral_div]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  push_cast
  rw [Complex.sin, show -((↑ν - ↑ω) * I) * (x : ℂ) = -(↑ν * I) * ↑x + ↑ω * ↑x * I by ring,
    show -((↑ν + ↑ω) * I) * (x : ℂ) = -(↑ν * I) * ↑x + -(↑ω * ↑x) * I by ring,
    Complex.exp_add, Complex.exp_add]
  have hI : (2 * I) ≠ 0 := by simp
  field_simp
  ring_nf
  rw [I_sq]
  ring

end MeanModulation

/-! ## The rotated mode -/

section Mode

variable {X : Type*} [Fintype X] [DecidableEq X] {A : ℝ → Matrix X X ℝ} {T : ℝ}

/-- The lift `w ⊗ (1, 0)` of a base vector to the rotated system. -/
def liftRe (w : X → ℝ) : X × Fin 2 → ℝ := fun p => w p.1 * ![1, 0] p.2

/-- The mode of the rotated system started at `liftRe w`. -/
def rotatedMode (A : ℝ → Matrix X X ℝ) (ω : ℝ) (w : X → ℝ) (t : ℝ) : X × Fin 2 → ℝ :=
  transition (fun r => realify (A r) (ω • 1)) t 0 *ᵥ liftRe w

/-- **The rotated mode is the base mode times a rotation.** For `t ≥ 0`,
`y(t) = x(t) ⊗ (cos ωt, sin ωt)` with `x(t) = Φ(t, 0) w` (`transition_realify`). -/
@[tmio T, powerlib_foundation] theorem rotated_mode_apply (hA : Continuous A) (hP : Periodic A T)
    (hT : 0 < T) (ω : ℝ) (w : X → ℝ) {t : ℝ} (ht : 0 ≤ t) (i : X) :
    rotatedMode A ω w t (i, 0) = (transition A t 0 *ᵥ w) i * Real.cos (ω * t) ∧
      rotatedMode A ω w t (i, 1) = (transition A t 0 *ᵥ w) i * Real.sin (ω * t) := by
  simp only [rotatedMode]
  rw [transition_realify hA hP hT ω ht, sub_zero]
  constructor <;>
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, liftRe, rot, quarter, Fin.sum_univ_two,
      mul_comm, mul_left_comm, mul_assoc]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- **The normalized base mode.** With `ρ = ln(−μ)/T` for a real multiplier `μ < 0`,
`M w = μ w`: the shifted system `A − ρI` has `Φ_{A−ρI}(t, 0) = e^{−ρt} Φ(t, 0)` (`t ≥ 0`,
`transition_sub_smul_one`), its monodromy maps `w` to `−w`, and its mode
`q(t) = e^{−ρt} x(t)` is `T`-antiperiodic. -/
@[tmio T, powerlib_foundation] theorem normalized_mode (hA : Continuous A) (hP : Periodic A T)
    (hT : 0 < T) {μ : ℝ} (hμ : μ < 0) {w : X → ℝ} (hw : monodromy A T 0 *ᵥ w = μ • w) :
    monodromy (fun r => A r - (Real.log (-μ) / T) • 1) T 0 *ᵥ w = -w ∧
      (∀ t, 0 ≤ t → transition (fun r => A r - (Real.log (-μ) / T) • 1) t 0 *ᵥ w =
        Real.exp (-(Real.log (-μ) / T * t)) • (transition A t 0 *ᵥ w)) ∧
      ∀ t, 0 ≤ t → transition (fun r => A r - (Real.log (-μ) / T) • 1) (t + T) 0 *ᵥ w =
        -(transition (fun r => A r - (Real.log (-μ) / T) • 1) t 0 *ᵥ w) := by
  obtain ⟨M, hM⟩ := exists_bound_of_periodic hA hP hT
  set ρ := Real.log (-μ) / T with hρ
  have hshift : ∀ t, 0 ≤ t → transition (fun r => A r - ρ • 1) t 0 *ᵥ w =
      Real.exp (-(ρ * t)) • (transition A t 0 *ᵥ w) := by
    intro t ht
    rw [transition_sub_smul_one hA hM ρ ht, sub_zero, Matrix.smul_mulVec]
  have hmono : monodromy (fun r => A r - ρ • 1) T 0 *ᵥ w = -w := by
    have h := hshift T hT.le
    have e : transition (fun r => A r - ρ • 1) T 0 = monodromy (fun r => A r - ρ • 1) T 0 := by
      rw [monodromy, zero_add]
    have e' : transition A T 0 = monodromy A T 0 := by rw [monodromy, zero_add]
    rw [e, e', hw, smul_smul] at h
    rw [h]
    have hexp : Real.exp (-(ρ * T)) * μ = -1 := by
      have hμ0 : μ ≠ 0 := hμ.ne
      rw [hρ, div_mul_cancel₀ _ hT.ne', Real.exp_neg, Real.exp_log (by linarith)]
      field_simp
    rw [hexp, neg_one_smul]
  refine ⟨hmono, hshift, fun t ht => ?_⟩
  have hA' : Continuous fun r => A r - ρ • (1 : Matrix X X ℝ) := hA.sub continuous_const
  have hP' : Periodic (fun r => A r - ρ • (1 : Matrix X X ℝ)) T := fun r => by
    simp only [hP r]
  have h := transition_mulVec_add_period hA' hP' hT (μ := -1) (w := w)
    (by rw [hmono, neg_one_smul]) ht
  rw [h, neg_one_smul]

/-- **Factorization of the rotated mode.** For `t ≥ 0`, with `ρ = ln(−μ)/T` and the
antiperiodic normalized base mode `q(t) = Φ_{A−ρI}(t, 0) w` of `normalized_mode`:
`e^{−ρt} y_{i,0}(t) = q_i(t) cos ωt`, `e^{−ρt} y_{i,1}(t) = q_i(t) sin ωt`, and
`y_{i,0}(t) + i y_{i,1}(t) = e^{(ρ + iω)t} q_i(t)` — growth at the rate `ρ`, rotation at `ω`, and
a `T`-antiperiodic factor. -/
@[tmio T, powerlib_foundation] theorem rotated_mode_factor (hA : Continuous A)
    (hP : Periodic A T) (hT : 0 < T) {μ : ℝ} (hμ : μ < 0) {w : X → ℝ}
    (hw : monodromy A T 0 *ᵥ w = μ • w) (ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (i : X) :
    Real.exp (-(Real.log (-μ) / T * t)) * rotatedMode A ω w t (i, 0) =
        (transition (fun r => A r - (Real.log (-μ) / T) • 1) t 0 *ᵥ w) i * Real.cos (ω * t) ∧
      Real.exp (-(Real.log (-μ) / T * t)) * rotatedMode A ω w t (i, 1) =
        (transition (fun r => A r - (Real.log (-μ) / T) • 1) t 0 *ᵥ w) i * Real.sin (ω * t) ∧
      (rotatedMode A ω w t (i, 0) : ℂ) + I * rotatedMode A ω w t (i, 1) =
        cexp ((((Real.log (-μ) / T : ℝ) : ℂ) + ω * I) * t) *
          (transition (fun r => A r - (Real.log (-μ) / T) • 1) t 0 *ᵥ w) i := by
  obtain ⟨-, hq, -⟩ := normalized_mode hA hP hT hμ hw
  obtain ⟨h0, h1⟩ := rotated_mode_apply hA hP hT ω w ht i
  set ρ := Real.log (-μ) / T
  have hqi : (transition (fun r => A r - ρ • 1) t 0 *ᵥ w) i =
      Real.exp (-(ρ * t)) * (transition A t 0 *ᵥ w) i := by
    rw [hq t ht, Pi.smul_apply, smul_eq_mul]
  refine ⟨by rw [h0, hqi]; ring, by rw [h1, hqi]; ring, ?_⟩
  rw [h0, h1, hqi]
  rw [show ((ρ : ℂ) + ω * I) * t = ((ρ * t : ℝ) : ℂ) + (ω * t : ℝ) * I by push_cast; ring,
    Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp]
  push_cast
  have hE : cexp (↑ρ * ↑t) * cexp (-(↑ρ * ↑t)) = 1 := by rw [← Complex.exp_add]; simp
  linear_combination (-((((transition A t 0 *ᵥ w) i : ℝ)) : ℂ) *
    (Complex.cos (ω * t) + Complex.sin (ω * t) * I)) * hE

end Mode

/-! ## The frequency position of the combination mode -/

section Position

variable {X : Type*} [Fintype X] [DecidableEq X] {A : ℝ → Matrix X X ℝ} {T : ℝ}

@[tmio T, powerlib_foundation] private theorem continuous_transition_mulVec_apply
    {B : ℝ → Matrix X X ℝ} (hB : Continuous B) (v : X → ℝ) (i : X) :
    Continuous fun t => (transition B t 0 *ᵥ v) i := by
  have hΦ : Continuous fun t => transition B t 0 :=
    continuous_iff_continuousAt.2 fun t => (Dynamics.stm_hasDerivAt hB t 0).continuousAt
  exact (continuous_apply i).comp (hΦ.matrix_mulVec continuous_const)

/-- **Combination modes on a rational rotation.** Let `M w = μ w` with `μ < 0`, `w ≠ 0`, and let
the rotation be rational, `ωT = 2πp/N` (`N > 0`). Over the window `[0, 2NT]` — index `m` at the
frequency `mΩ/(2N)`, `Ω = 2π/T` — every component of the normalized rotated mode
`p(t) = e^{−ρt} y(t)` (`ρ = ln(−μ)/T`):
* has nonzero coefficients only at `m ≡ N + 2p` or `m ≡ N − 2p (mod 2N)`, the frequencies
  `(k + ½)Ω ± ω`;
* if `N ∤ 2p` (that is `sin ωT ≠ 0`), has no coefficient on the locked lattice `(k/2)Ω`
  (`N ∣ m`);
* and some component has a nonzero coefficient at an index `2Nk + N + 2p`, the frequency
  `(k + ½)Ω + ω`.
The proof: `p_{i,0} = q_i cos ωt`, `p_{i,1} = q_i sin ωt` with `q` `T`-antiperiodic
(`rotated_mode_factor`), modulation shifts the coefficients by `±2p` (`coeff_mul_cos`,
`coeff_mul_sin`), `q` has coefficients only at `m ≡ N (mod 2N)` (`coeff_window_antiperiodic`), and
`c_{2Nk+N}(q_i)` over `[0, 2NT]` is the half-integer coefficient `c_{2k+1}(q_i)` over `[0, 2T]`
(`coeff_window_nat_mul`), nonzero for some `i, k`
(`ParametricResonance.Subharmonic.antiperiodic_mode_coeff_odd` for `A − ρI`). -/
@[tmio T, powerlib_foundation] theorem combination_window (hA : Continuous A) (hP : Periodic A T)
    (hT : 0 < T) {μ : ℝ} (hμ : μ < 0) {w : X → ℝ} (hw0 : w ≠ 0)
    (hw : monodromy A T 0 *ᵥ w = μ • w) {ω : ℝ} {N : ℕ} (hN : 0 < N) {p : ℤ}
    (hωT : ω * T = 2 * Real.pi * p / N) :
    (∀ (k : X × Fin 2) (m : ℤ), ¬ (2 * N : ℤ) ∣ m - (N + 2 * p) →
      ¬ (2 * N : ℤ) ∣ m - (N - 2 * p) →
      coeff (mul_pos (mul_pos two_pos (Nat.cast_pos.mpr hN)) hT)
        (fun t => Real.exp (-(Real.log (-μ) / T * t)) * rotatedMode A ω w t k) m = 0) ∧
    (¬ (N : ℤ) ∣ 2 * p → ∀ (k : X × Fin 2) (m : ℤ), (N : ℤ) ∣ m →
      coeff (mul_pos (mul_pos two_pos (Nat.cast_pos.mpr hN)) hT)
        (fun t => Real.exp (-(Real.log (-μ) / T * t)) * rotatedMode A ω w t k) m = 0) ∧
    ∃ (k : X × Fin 2) (j : ℤ),
      coeff (mul_pos (mul_pos two_pos (Nat.cast_pos.mpr hN)) hT)
        (fun t => Real.exp (-(Real.log (-μ) / T * t)) * rotatedMode A ω w t k)
        (2 * N * j + N + 2 * p) ≠ 0 := by
  obtain ⟨hmono, -, hanti⟩ := normalized_mode hA hP hT hμ hw
  set ρ := Real.log (-μ) / T with hρ
  set B : ℝ → Matrix X X ℝ := fun r => A r - ρ • 1 with hBdef
  have hB : Continuous B := hA.sub continuous_const
  set q : X → ℝ → ℝ := fun i t => (transition B t 0 *ᵥ w) i with hqdef
  have hqc : ∀ i, Continuous (q i) := fun i => continuous_transition_mulVec_apply hB w i
  have hqa : ∀ i t, 0 ≤ t → q i (t + T) = -q i t := fun i t ht => by
    simp only [hqdef, hanti t ht, Pi.neg_apply]
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hL : 0 < 2 * (N : ℝ) * T := mul_pos (mul_pos two_pos hNpos) hT
  -- `ω t = 2π (2p) t / (2NT)`
  have hωt : ∀ t, ω * t = 2 * Real.pi * ((2 * p : ℤ) : ℝ) * t / (2 * N * T) := by
    intro t
    have hω : ω = 2 * Real.pi * p / (N * T) := by
      rw [eq_div_iff (by positivity)]
      field_simp at hωT
      linear_combination hωT
    rw [hω]; push_cast; field_simp
  -- the components on the window
  have hcos : ∀ i m, coeff hL (fun t => Real.exp (-(ρ * t)) * rotatedMode A ω w t (i, 0)) m =
      (coeff hL (q i) (m - 2 * p) + coeff hL (q i) (m + 2 * p)) / 2 := by
    intro i m
    rw [coeff_congr_Icc hL (h := fun t => q i t * Real.cos (2 * Real.pi * ((2 * p : ℤ) : ℝ) * t /
      (2 * N * T))) (fun t ht => by
        rw [(rotated_mode_factor hA hP hT hμ hw ω ht.1 i).1, hωt])]
    exact coeff_mul_cos hL (hqc i).continuousOn _ m
  have hsin : ∀ i m, coeff hL (fun t => Real.exp (-(ρ * t)) * rotatedMode A ω w t (i, 1)) m =
      (coeff hL (q i) (m - 2 * p) - coeff hL (q i) (m + 2 * p)) / (2 * I) := by
    intro i m
    rw [coeff_congr_Icc hL (h := fun t => q i t * Real.sin (2 * Real.pi * ((2 * p : ℤ) : ℝ) * t /
      (2 * N * T))) (fun t ht => by
        rw [(rotated_mode_factor hA hP hT hμ hw ω ht.1 i).2.1, hωt])]
    exact coeff_mul_sin hL (hqc i).continuousOn _ m
  have hq0 : ∀ i m, ¬ (2 * N : ℤ) ∣ m - N → coeff hL (q i) m = 0 := fun i m hm =>
    coeff_window_antiperiodic hT (hqc i).continuousOn (hqa i) hN hm
  -- (a) content only at `N ± 2p`
  have ha : ∀ (k : X × Fin 2) (m : ℤ), ¬ (2 * N : ℤ) ∣ m - (N + 2 * p) →
      ¬ (2 * N : ℤ) ∣ m - (N - 2 * p) →
      coeff hL (fun t => Real.exp (-(ρ * t)) * rotatedMode A ω w t k) m = 0 := by
    rintro ⟨i, k⟩ m h₁ h₂
    have e₁ : coeff hL (q i) (m - 2 * p) = 0 := hq0 i _ (by
      rwa [show m - 2 * p - N = m - (N + 2 * p) by ring])
    have e₂ : coeff hL (q i) (m + 2 * p) = 0 := hq0 i _ (by
      rwa [show m + 2 * p - N = m - (N - 2 * p) by ring])
    fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [hcos, e₁, e₂]; simp
    · simp only [Fin.mk_one, Fin.isValue]
      rw [hsin, e₁, e₂]; simp
  refine ⟨ha, fun hNp k m hm => ha k m ?_ ?_, ?_⟩
  · intro h
    apply hNp
    have h' : (N : ℤ) ∣ m - (N + 2 * p) := dvd_trans ⟨2, by ring⟩ h
    have := dvd_sub (dvd_sub hm (dvd_refl (N : ℤ))) h'
    rwa [show m - N - (m - (N + 2 * p)) = 2 * p by ring] at this
  · intro h
    apply hNp
    have h' : (N : ℤ) ∣ m - (N - 2 * p) := dvd_trans ⟨2, by ring⟩ h
    have := dvd_sub h' (dvd_sub hm (dvd_refl (N : ℤ)))
    rwa [show m - (N - 2 * p) - (m - N) = 2 * p by ring] at this
  -- (c) nonzero content at `2Nk + N + 2p`
  have hB' : Periodic B T := fun r => by simp only [hBdef, hP r]
  obtain ⟨i, j, hij⟩ := ParametricResonance.Subharmonic.antiperiodic_mode_coeff_odd hB hB' hT hw0
    hmono (s := 0) le_rfl
  simp only [zero_add] at hij
  have hper : ∀ t, 0 ≤ t → q i (t + 2 * T) = q i t := fun t ht => by
    rw [show t + 2 * T = (t + T) + T by ring, hqa i _ (by linarith), hqa i t ht, neg_neg]
  have hmul := coeff_window_nat_mul (mul_pos two_pos hT) (hqc i).continuousOn hper hN (2 * j + 1)
  rw [coeff_length_congr (show (N : ℝ) * (2 * T) = 2 * N * T by ring) _ hL] at hmul
  by_cases h0 : coeff hL (fun t => Real.exp (-(ρ * t)) * rotatedMode A ω w t (i, 0))
      (2 * N * j + N + 2 * p) = 0
  · refine ⟨(i, 1), j, fun h1 => hij ?_⟩
    have hsum := congrArg₂ (fun a b => a + I * b) h0 h1
    simp only [hcos, hsin, mul_zero, add_zero] at hsum
    have hI : I ≠ 0 := I_ne_zero
    have e : coeff hL (q i) (2 * N * j + N + 2 * p - 2 * p) = coeff (mul_pos two_pos hT) (q i)
        (2 * j + 1) := by
      rw [show 2 * N * j + N + 2 * p - 2 * p = (N : ℤ) * (2 * j + 1) by ring, hmul]
    rw [← e]
    field_simp at hsum
    linear_combination hsum / 2
  · exact ⟨(i, 0), j, h0⟩

@[tmio T, powerlib_foundation] private theorem windowMean_congr {T : ℝ} (hT : 0 ≤ T)
    {f g : ℝ → ℂ} {ν ν' : ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → cexp (-(ν * I) * t) * f t = cexp (-(ν' * I) * t) * g t) (n : ℕ) :
    windowMean T f ν n = windowMean T g ν' n := by
  unfold windowMean
  congr 1
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le (mul_nonneg (Nat.cast_nonneg n) hT)] at hx
  exact h x hx.1

@[tmio T, powerlib_foundation] private theorem sin_eq_zero_of_cexp_eq_neg_one {θ : ℝ}
    (h : cexp (θ * I) = -1) : Real.sin θ = 0 := by
  have := Complex.exp_ofReal_mul_I_im θ
  rw [h] at this
  simpa using this.symm

/-- **Combination modes at any rotation rate.** In the setting of `combination_window`, but for
every `ω` (rational or irrational `ωT/2π`), the long-window mean content
`windowMean T p_{i,k} ν n = (1/(nT)) ∫₀^{nT} e^{−iνt} p_{i,k}(t) dt` of the normalized rotated mode
* tends to `0` as `n → ∞` at every frequency `ν` with `e^{i(ω − ν)T} ≠ −1` and
  `e^{−i(ω + ν)T} ≠ −1`, i.e. off the set `(k + ½)Ω ± ω`;
* tends to `0` at every locked frequency `ν = jπ/T = (j/2)Ω` when `sin ωT ≠ 0`;
* at `ν = (2j + 1)π/T + ω = (j + ½)Ω + ω` equals, for the combination `p_{i,0} + i p_{i,1}` and every
  `n ≥ 1`, the half-integer coefficient `c_{2j+1}` over `[0, 2T]` of the normalized base mode
  `e^{−ρt} x_i(t)`, which is nonzero for some `i, j`.
The means reduce to those of the antiperiodic factor `q` at `ν ∓ ω` (`windowMean_mul_cos`,
`windowMean_mul_sin`), which vanish off the Floquet frequencies (`tendsto_windowMean_zero`) and are
constant on them (`windowMean_eq_of_eq_one`). -/
@[tmio T, powerlib_foundation] theorem combination_mean (hA : Continuous A) (hP : Periodic A T)
    (hT : 0 < T) {μ : ℝ} (hμ : μ < 0) {w : X → ℝ} (hw0 : w ≠ 0)
    (hw : monodromy A T 0 *ᵥ w = μ • w) (ω : ℝ) :
    (∀ (k : X × Fin 2) (ν : ℝ), cexp (((ω - ν) * T : ℝ) * I) ≠ -1 →
      cexp ((-(ω + ν) * T : ℝ) * I) ≠ -1 →
      Tendsto (windowMean T (fun t =>
        ((Real.exp (-(Real.log (-μ) / T * t)) * rotatedMode A ω w t k : ℝ) : ℂ)) ν)
        atTop (𝓝 0)) ∧
    (Real.sin (ω * T) ≠ 0 → ∀ (k : X × Fin 2) (j : ℤ),
      Tendsto (windowMean T (fun t =>
        ((Real.exp (-(Real.log (-μ) / T * t)) * rotatedMode A ω w t k : ℝ) : ℂ)) (j * Real.pi / T))
        atTop (𝓝 0)) ∧
    (∀ (i : X) (j : ℤ) (n : ℕ), 0 < n →
      windowMean T (fun t =>
          ((Real.exp (-(Real.log (-μ) / T * t)) * rotatedMode A ω w t (i, 0) : ℝ) : ℂ) +
            I * ((Real.exp (-(Real.log (-μ) / T * t)) * rotatedMode A ω w t (i, 1) : ℝ) : ℂ))
        ((2 * j + 1) * Real.pi / T + ω) n =
      coeff (mul_pos two_pos hT)
        (fun t => Real.exp (-(Real.log (-μ) / T * t)) * (transition A t 0 *ᵥ w) i) (2 * j + 1)) ∧
    ∃ (i : X) (j : ℤ), coeff (mul_pos two_pos hT)
      (fun t => Real.exp (-(Real.log (-μ) / T * t)) * (transition A t 0 *ᵥ w) i) (2 * j + 1) ≠ 0 := by
  obtain ⟨hmono, hshift, hanti⟩ := normalized_mode hA hP hT hμ hw
  set ρ := Real.log (-μ) / T with hρ
  set B : ℝ → Matrix X X ℝ := fun r => A r - ρ • 1 with hBdef
  have hB : Continuous B := hA.sub continuous_const
  set q : X → ℝ → ℝ := fun i t => (transition B t 0 *ᵥ w) i with hqdef
  have hqc : ∀ i, Continuous (q i) := fun i => continuous_transition_mulVec_apply hB w i
  have hqa : ∀ i t, 0 ≤ t → ((q i (t + T) : ℝ) : ℂ) = -1 * (q i t : ℂ) := fun i t ht => by
    simp only [hqdef, hanti t ht, Pi.neg_apply]; push_cast; ring
  have hqcC : ∀ i, ContinuousOn (fun t => ((q i t : ℝ) : ℂ)) (Ici 0) := fun i =>
    (Complex.continuous_ofReal.comp (hqc i)).continuousOn
  have hnorm : ‖(-1 : ℂ)‖ = 1 := by simp
  -- the mean of `q` off the Floquet frequencies
  have hq0 : ∀ i (lam : ℝ), cexp ((-(lam * T) : ℝ) * I) ≠ -1 →
      Tendsto (windowMean T (fun t => ((q i t : ℝ) : ℂ)) lam) atTop (𝓝 0) := by
    intro i lam hlam
    refine tendsto_windowMean_zero hT (hqcC i) hnorm (hqa i) fun h => hlam ?_
    have e : cexp (-(↑lam * I) * ↑T) = cexp ((-(lam * T) : ℝ) * I) := by
      congr 1; push_cast; ring
    rw [e] at h
    linear_combination -h
  have hfac : ∀ i t, 0 ≤ t →
      Real.exp (-(ρ * t)) * rotatedMode A ω w t (i, 0) = q i t * Real.cos (ω * t) ∧
        Real.exp (-(ρ * t)) * rotatedMode A ω w t (i, 1) = q i t * Real.sin (ω * t) :=
    fun i t ht => ⟨(rotated_mode_factor hA hP hT hμ hw ω ht i).1,
      (rotated_mode_factor hA hP hT hμ hw ω ht i).2.1⟩
  -- (i)
  have hi : ∀ (k : X × Fin 2) (ν : ℝ), cexp (((ω - ν) * T : ℝ) * I) ≠ -1 →
      cexp ((-(ω + ν) * T : ℝ) * I) ≠ -1 →
      Tendsto (windowMean T (fun t =>
        ((Real.exp (-(ρ * t)) * rotatedMode A ω w t k : ℝ) : ℂ)) ν) atTop (𝓝 0) := by
    rintro ⟨i, k⟩ ν h₁ h₂
    have t₁ := hq0 i (ν - ω) (by
      rwa [show (-((ν - ω) * T) : ℝ) = (ω - ν) * T by ring])
    have t₂ := hq0 i (ν + ω) (by
      rwa [show (-((ν + ω) * T) : ℝ) = -(ω + ν) * T by ring])
    fin_cases k
    · have e : windowMean T (fun t => ((Real.exp (-(ρ * t)) * rotatedMode A ω w t (i, 0) : ℝ) : ℂ))
          ν = windowMean T (fun t => ((q i t * Real.cos (ω * t) : ℝ) : ℂ)) ν := by
        funext n
        exact windowMean_congr hT.le (fun t ht => by rw [(hfac i t ht).1]) n
      simp only [Fin.zero_eta, Fin.isValue]
      rw [e]
      have := (t₁.add t₂).div_const 2
      simp only [add_zero, zero_div] at this
      refine this.congr fun n => ?_
      exact (windowMean_mul_cos (hqc i).continuousOn hT.le ω ν n).symm
    · have e : windowMean T (fun t => ((Real.exp (-(ρ * t)) * rotatedMode A ω w t (i, 1) : ℝ) : ℂ))
          ν = windowMean T (fun t => ((q i t * Real.sin (ω * t) : ℝ) : ℂ)) ν := by
        funext n
        exact windowMean_congr hT.le (fun t ht => by rw [(hfac i t ht).2]) n
      simp only [Fin.mk_one, Fin.isValue]
      rw [e]
      have := (t₁.sub t₂).div_const (2 * I)
      simp only [sub_zero, zero_div] at this
      refine this.congr fun n => ?_
      exact (windowMean_mul_sin (hqc i).continuousOn hT.le ω ν n).symm
  -- the normalized base mode in the statement's form
  have hqform : ∀ i t, 0 ≤ t → Real.exp (-(ρ * t)) * (transition A t 0 *ᵥ w) i = q i t :=
    fun i t ht => by simp only [hqdef, hshift t ht, Pi.smul_apply, smul_eq_mul]
  refine ⟨hi, fun hs k j => hi k _ ?_ ?_, ?_, ?_⟩
  · intro h
    have h0 := sin_eq_zero_of_cexp_eq_neg_one h
    rw [show (ω - j * Real.pi / T) * T = ω * T - j * Real.pi by field_simp, Real.sin_sub,
      Real.sin_int_mul_pi, mul_zero, sub_zero] at h0
    have hc : Real.cos (j * Real.pi) ≠ 0 := by
      intro hc
      have := Real.sin_sq_add_cos_sq (j * Real.pi)
      rw [Real.sin_int_mul_pi, hc] at this
      norm_num at this
    exact hs ((mul_eq_zero.mp h0).resolve_right hc)
  · intro h
    have h0 := sin_eq_zero_of_cexp_eq_neg_one h
    rw [show -(ω + j * Real.pi / T) * T = -(ω * T + j * Real.pi) by field_simp, Real.sin_neg,
      Real.sin_add, Real.sin_int_mul_pi, mul_zero, add_zero, neg_eq_zero] at h0
    have hc : Real.cos (j * Real.pi) ≠ 0 := by
      intro hc
      have := Real.sin_sq_add_cos_sq (j * Real.pi)
      rw [Real.sin_int_mul_pi, hc] at this
      norm_num at this
    exact hs ((mul_eq_zero.mp h0).resolve_right hc)
  · intro i j n hn
    set lam : ℝ := (2 * j + 1) * Real.pi / T with hlam
    have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have hcomb : windowMean T (fun t =>
          ((Real.exp (-(ρ * t)) * rotatedMode A ω w t (i, 0) : ℝ) : ℂ) +
            I * ((Real.exp (-(ρ * t)) * rotatedMode A ω w t (i, 1) : ℝ) : ℂ)) (lam + ω) n =
        windowMean T (fun t => ((q i t : ℝ) : ℂ)) lam n := by
      refine windowMean_congr hT.le (fun t ht => ?_) n
      rw [(hfac i t ht).1, (hfac i t ht).2]
      push_cast
      rw [show -((↑lam + ↑ω) * I) * (t : ℂ) = -(↑lam * I) * ↑t + -(↑ω * ↑t * I) by ring,
        Complex.exp_add, show -(↑ω * ↑t * I) = (-(↑ω * ↑t) : ℂ) * I by ring, Complex.exp_mul_I,
        Complex.cos_neg, Complex.sin_neg]
      have h1 := Complex.cos_sq_add_sin_sq (↑ω * ↑t)
      linear_combination (cexp (-(↑lam * I) * ↑t) * ↑(q i t)) * h1 -
        (cexp (-(↑lam * I) * ↑t) * Complex.sin (↑ω * ↑t) ^ 2 * ↑(q i t)) * Complex.I_sq
    have hone : (-1 : ℂ) * cexp (-(↑lam * I) * ↑T) = 1 := by
      rw [show -(↑lam * I) * (T : ℂ) = ((-j - 1 : ℤ) : ℂ) * (2 * Real.pi * I) + Real.pi * I by
        rw [hlam]; push_cast; field_simp; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
        Complex.exp_pi_mul_I]
      ring
    rw [hcomb, windowMean_eq_of_eq_one hT (hqcC i) (hqa i) hone hn,
      ← windowMean_eq_of_eq_one hT (hqcC i) (hqa i) hone two_pos,
      coeff_congr_Icc (mul_pos two_pos hT) (h := q i) (fun t ht => hqform i t ht.1),
      coeff_eq_integral, windowMean]
    congr 1
    · push_cast; ring
    · refine intervalIntegral.integral_congr fun x _ => ?_
      congr 2
      simp only [kernelExp, hlam]
      push_cast
      field_simp
  · have hB' : Periodic B T := fun r => by simp only [hBdef, hP r]
    obtain ⟨i, j, hij⟩ := ParametricResonance.Subharmonic.antiperiodic_mode_coeff_odd hB hB' hT hw0
      hmono (s := 0) le_rfl
    simp only [zero_add] at hij
    refine ⟨i, j, ?_⟩
    rwa [coeff_congr_Icc (mul_pos two_pos hT) (h := q i) (fun t ht => hqform i t ht.1)]

end Position

end powerlib.Periodic.Combination
