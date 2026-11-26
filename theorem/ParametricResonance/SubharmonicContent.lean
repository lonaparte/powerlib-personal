import theorem.ParametricResonance.Signature
import theorem.Periodic.Liouville

/-! # Half-integer spectral content: the converse of the subharmonic signature

Over a window of two pump periods, `[0, 2T]` with `Ω = 2π/T`, the Fourier coefficient of index
`m` sits at the frequency `mΩ/2`: even `m` are the integer multiples `kΩ`, odd `m` the
half-integer frequencies `(k + ½)Ω`. Folding the window onto one pump period and applying
Parseval on `[0, T]` gives the exact energy split
`Σ_k |c_{2k+1}|² = (1/(4T)) ∫₀ᵀ (f(t) − f(t + T))²` and
`Σ_k |c_{2k}|² = (1/(4T)) ∫₀ᵀ (f(t) + f(t + T))²`: the half-integer content of `f` is the
energy of its antiperiodic part, the integer content that of its periodic part. Hence, for `f`
continuous on the window,
* no half-integer content iff `f(t + T) = f(t)` on `[0, T]` (`T`-periodic on the window), and no
  integer content iff `f(t + T) = −f(t)` (`T`-antiperiodic);
* an antiperiodic `f` is nonzero iff it has a nonzero coefficient at some `(k + ½)Ω`.
The direct statements (antiperiodic ⇒ no `kΩ` content, periodic ⇒ no `(k + ½)Ω` content) are
`Signature.coeff_eq_zero_of_antiperiodic` and `Signature.coeff_eq_zero_of_periodic`; this module
proves the converses. Consequently a real Floquet mode with multiplier `−1` (the boundary of a
principal tongue) genuinely shows a subharmonic line in some state component over every window,
and on the Meissner boundary the position signal itself has one. For the half-frequency rule P½
of the swing-model classification (a nonzero `T`-antiperiodic oscillation is parametric) the
premise therefore has a spectral reading: an antiperiodic oscillation is nonzero iff it has
nonzero content at some `(k + ½)Ω`, and then it has none at `Ωℤ`.

Scope.
* Real signals `f : ℝ → ℝ` continuous on the closed window `[0, 2T]`, `T > 0`; hypotheses only
  on the window (`f(t + T) = ±f(t)` for `t ∈ [0, T]`), so signals given on `[0, ∞)` and later
  windows `[s, s + 2T]` (through `t ↦ f(s + t)`) are covered. Coefficients are
  `SpecialFunctions.PeriodicWaves.coeff` over `[0, 2T]` as in
  `theorem/ParametricResonance/Signature.lean`; Parseval is Mathlib's
  `hasSum_sq_fourierCoeffOn` for the complex signals `e^{−iπt/T}(f(t) − f(t + T))` and
  `f(t) + f(t + T)` on `[0, T]`.
* Floquet modes of a continuous `T`-periodic `ẋ = A(t)x` (`Periodic.transition`,
  `Periodic.monodromy`, `theorem/Periodic/ForcedRegime.lean`) and the boundary mode of the Meissner
  oscillator (`theorem/ParametricResonance/Meissner.lean`, right-differentiable solutions).
* Generic mathematics; no model family, no measured record. The swing-model rule itself
  (`theorem/PowerSystem/ForcedOscillation/Classification.lean`, an engineering module) is not
  imported.

Source: Parseval's identity on `AddCircle` (Mathlib `hasSum_sq_fourierCoeffOn`); the frequency
relation of parametric oscillations (a `μ = −1` Floquet mode is `T`-antiperiodic, its spectrum
lies at `(k + ½)Ω`) of `theorem/ParametricResonance/Signature.lean` and the half-frequency rule of
IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.1, §3.4 as sharpened in the
wave-2 classification; the boundary mode `Meissner.antiperiodic_of_boundary`.

Results.
* `coeff_fold` — `c_m = (1/(2T)) ∫₀ᵀ e^{κ_m t} (f(t) + (−1)^m f(t + T)) dt`.
* `coeff_odd_eq`, `coeff_even_eq` — the odd (even) coefficients over `[0, 2T]` are half the
  one-period coefficients of `e^{−iπt/T}(f(t) − f(t + T))` (of `f(t) + f(t + T)`).
* `hasSum_sq_coeff_odd`, `hasSum_sq_coeff_even` — half-integer energy
  `(1/(4T)) ∫₀ᵀ (f(t) − f(t + T))²`, integer energy `(1/(4T)) ∫₀ᵀ (f(t) + f(t + T))²`.
* `coeff_odd_eq_zero_iff`, `coeff_even_eq_zero_iff` — no half-integer (integer) content iff
  `T`-periodic (`T`-antiperiodic) on the window.
* `antiperiodic_ne_zero_iff` — a `T`-antiperiodic signal is nonzero on the window iff it has a
  nonzero half-integer coefficient.
* `antiperiodic_mode_coeff_odd` — a real Floquet mode `M w = −w`, `w ≠ 0`: over every window
  `[s, s + 2T]` some component has a nonzero half-integer coefficient.
* `meissner_boundary_subharmonic` — on the Meissner boundary `τ = −2 cosh(cT)` a nonzero
  antiperiodic solution whose position has no `kΩ` content and nonzero `(k + ½)Ω` content.
-/

noncomputable section
namespace powerlib.ParametricResonance.Subharmonic

open Complex Set MeasureTheory Function Filter Topology Matrix
open scoped Matrix.Norms.Operator
open powerlib.SpecialFunctions.PeriodicWaves (coeff kernelExp coeff_eq_integral)

variable {T : ℝ}

/-! ## Splitting the window `[0, 2T]` into two pump periods -/

/-- The coefficient at index `m` over `[0, 2T]` folds onto one pump period:
`c_m = (1/(2T)) ∫₀ᵀ e^{κ_m t} (f(t) + (−1)^m f(t + T)) dt`, `κ_m = −πim/T`. -/
@[tmio T, powerlib_foundation] theorem coeff_fold (hT : 0 < T) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 (2 * T))) (m : ℤ) :
    coeff (mul_pos two_pos hT) f m = (1 / (2 * T) : ℂ) *
      ∫ t in (0 : ℝ)..T, cexp (kernelExp (2 * T) m * t) *
        ((f t : ℂ) + (-1) ^ m * (f (t + T) : ℂ)) := by
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  set g : ℝ → ℂ := fun x => cexp (kernelExp (2 * T) m * x) * (f x : ℂ) with hg
  have hgc : ContinuousOn g (Icc 0 (2 * T)) := by
    refine (Continuous.continuousOn (by fun_prop)).mul ?_
    exact Complex.continuous_ofReal.comp_continuousOn hf
  have i1 : IntervalIntegrable g volume 0 T :=
    (hgc.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc hT.le
  have i2 : IntervalIntegrable g volume T (2 * T) :=
    (hgc.mono (Icc_subset_Icc hT.le le_rfl)).intervalIntegrable_of_Icc (by linarith)
  have hshift : ∫ x in T..2 * T, g x = ∫ x in (0 : ℝ)..T, g (x + T) := by
    rw [intervalIntegral.integral_comp_add_right g T, zero_add, show T + T = 2 * T by ring]
  have hk : ∀ x : ℝ, g (x + T) = cexp (kernelExp (2 * T) m * x) * ((-1) ^ m * (f (x + T) : ℂ)) := by
    intro x
    have he : cexp (kernelExp (2 * T) m * ((x + T : ℝ) : ℂ)) =
        cexp (kernelExp (2 * T) m * x) * (-1) ^ m := by
      have e1 : kernelExp (2 * T) m * ((x + T : ℝ) : ℂ) =
          kernelExp (2 * T) m * x + m * (-(Real.pi * I)) := by
        simp only [kernelExp]; push_cast; field_simp; ring
      rw [e1, Complex.exp_add, Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
      congr 1
      rw [inv_neg, inv_one]
    simp only [hg, he]
    ring
  have hfT : ContinuousOn (fun x => f (x + T)) (Icc 0 T) :=
    hf.comp (by fun_prop) (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have i3 : IntervalIntegrable
      (fun x : ℝ => cexp (kernelExp (2 * T) m * x) * ((-1) ^ m * (f (x + T) : ℂ))) volume 0 T :=
    ((Continuous.continuousOn (by fun_prop)).mul (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn hfT))).intervalIntegrable_of_Icc hT.le
  rw [coeff_eq_integral, ← intervalIntegral.integral_add_adjacent_intervals i1 i2, hshift,
    intervalIntegral.integral_congr (fun x _ => hk x), ← intervalIntegral.integral_add i1 i3]
  congr 1
  · push_cast; ring
  · refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hg]; ring

/-- The half-integer coefficients (odd index over `[0, 2T]`) are half the one-period Fourier
coefficients of `e^{−iπt/T} (f(t) − f(t + T))`. -/
@[tmio T, powerlib_foundation] theorem coeff_odd_eq (hT : 0 < T) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 (2 * T))) (k : ℤ) :
    coeff (mul_pos two_pos hT) f (2 * k + 1) = (1 / 2 : ℂ) * fourierCoeffOn hT
      (fun t => cexp (-(Real.pi * I * t / T)) * ((f t - f (t + T) : ℝ) : ℂ)) k := by
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [coeff_fold hT hf, fourierCoeffOn_eq_integral _ _ hT, Odd.neg_one_zpow ⟨k, rfl⟩]
  rw [Complex.real_smul, ← mul_assoc, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [fourier_coe_apply, smul_eq_mul, ← mul_assoc (cexp _), ← Complex.exp_add]
  have e : kernelExp (2 * T) ((2 * k + 1 : ℤ)) * x =
      2 * Real.pi * I * ((-k : ℤ) : ℂ) * x / ((T - 0 : ℝ) : ℂ) + -(Real.pi * I * x / T) := by
    simp only [kernelExp]; push_cast; field_simp; ring
  rw [e]
  push_cast
  ring

/-- The integer-frequency coefficients (even index over `[0, 2T]`) are half the one-period
Fourier coefficients of `f(t) + f(t + T)`. -/
@[tmio T, powerlib_foundation] theorem coeff_even_eq (hT : 0 < T) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 (2 * T))) (k : ℤ) :
    coeff (mul_pos two_pos hT) f (2 * k) = (1 / 2 : ℂ) * fourierCoeffOn hT
      (fun t => ((f t + f (t + T) : ℝ) : ℂ)) k := by
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [coeff_fold hT hf, fourierCoeffOn_eq_integral _ _ hT, Even.neg_one_zpow ⟨k, by ring⟩]
  rw [Complex.real_smul, ← mul_assoc, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [fourier_coe_apply, smul_eq_mul]
  have e : kernelExp (2 * T) ((2 * k : ℤ)) * x =
      2 * Real.pi * I * ((-k : ℤ) : ℂ) * x / ((T - 0 : ℝ) : ℂ) := by
    simp only [kernelExp]; push_cast; field_simp; ring
  rw [e]
  push_cast
  ring

@[tmio T, powerlib_foundation] private theorem memLp_of_continuousOn {T : ℝ} {H : ℝ → ℂ}
    (hH : ContinuousOn H (Icc 0 T)) : MemLp H 2 (volume.restrict (Ioc 0 T)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hH
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) T)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  exact MemLp.of_bound ((hH.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) C
    (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hC x (Ioc_subset_Icc_self hx))

/-- **Half-integer energy = energy of the antiperiodic part.** For `f` continuous on `[0, 2T]`:
`Σ_k |c_{2k+1}|² = (1/(4T)) ∫₀ᵀ (f(t) − f(t + T))²` (coefficients over `[0, 2T]`, the
frequencies `(k + ½)Ω`, `Ω = 2π/T`). -/
@[tmio T, powerlib_foundation] theorem hasSum_sq_coeff_odd (hT : 0 < T) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 (2 * T))) :
    HasSum (fun k : ℤ => ‖coeff (mul_pos two_pos hT) f (2 * k + 1)‖ ^ 2)
      ((4 * T)⁻¹ * ∫ t in (0 : ℝ)..T, (f t - f (t + T)) ^ 2) := by
  have hfT : ContinuousOn (fun x => f (x + T)) (Icc 0 T) :=
    hf.comp (by fun_prop) (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hf0 : ContinuousOn f (Icc 0 T) := hf.mono (Icc_subset_Icc le_rfl (by linarith))
  have hH : ContinuousOn (fun t : ℝ => cexp (-(Real.pi * I * t / T)) *
      ((f t - f (t + T) : ℝ) : ℂ)) (Icc 0 T) :=
    (Continuous.continuousOn (by fun_prop)).mul
      (Complex.continuous_ofReal.comp_continuousOn (hf0.sub hfT))
  have h := (hasSum_sq_fourierCoeffOn hT (memLp_of_continuousOn hH)).mul_left (1 / 4)
  have hn : ∀ x : ℝ, ‖cexp (-(Real.pi * I * x / T)) * ((f x - f (x + T) : ℝ) : ℂ)‖ ^ 2 =
      (f x - f (x + T)) ^ 2 := by
    intro x
    rw [norm_mul, show -(Real.pi * I * x / T) = ((-(Real.pi * x / T) : ℝ) : ℂ) * I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  simp only [hn, sub_zero, smul_eq_mul] at h
  convert h using 1
  · funext k
    rw [coeff_odd_eq hT hf, norm_mul, mul_pow]
    norm_num
  · ring

/-- **Integer-frequency energy = energy of the periodic part.**
`Σ_k |c_{2k}|² = (1/(4T)) ∫₀ᵀ (f(t) + f(t + T))²`. -/
@[tmio T, powerlib_foundation] theorem hasSum_sq_coeff_even (hT : 0 < T) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 (2 * T))) :
    HasSum (fun k : ℤ => ‖coeff (mul_pos two_pos hT) f (2 * k)‖ ^ 2)
      ((4 * T)⁻¹ * ∫ t in (0 : ℝ)..T, (f t + f (t + T)) ^ 2) := by
  have hfT : ContinuousOn (fun x => f (x + T)) (Icc 0 T) :=
    hf.comp (by fun_prop) (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hf0 : ContinuousOn f (Icc 0 T) := hf.mono (Icc_subset_Icc le_rfl (by linarith))
  have hH : ContinuousOn (fun t : ℝ => ((f t + f (t + T) : ℝ) : ℂ)) (Icc 0 T) :=
    Complex.continuous_ofReal.comp_continuousOn (hf0.add hfT)
  have h := (hasSum_sq_fourierCoeffOn hT (memLp_of_continuousOn hH)).mul_left (1 / 4)
  have hn : ∀ x : ℝ, ‖((f x + f (x + T) : ℝ) : ℂ)‖ ^ 2 = (f x + f (x + T)) ^ 2 := fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [hn, sub_zero, smul_eq_mul] at h
  convert h using 1
  · funext k
    rw [coeff_even_eq hT hf, norm_mul, mul_pow]
    norm_num
  · ring

@[tmio T, powerlib_foundation] private theorem eq_zero_of_integral_sq {T : ℝ} (hT : 0 < T)
    {h : ℝ → ℝ} (hc : ContinuousOn h (Icc 0 T)) (h0 : ∫ t in (0 : ℝ)..T, h t ^ 2 = 0) :
    ∀ t ∈ Icc 0 T, h t = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨t₀, ht₀, hne⟩ := hne
  have := intervalIntegral.integral_pos (f := fun t => h t ^ 2) hT (hc.pow 2)
    (fun x _ => sq_nonneg (h x)) ⟨t₀, ht₀, lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hne).symm⟩
  linarith

/-- **No half-integer content iff `T`-periodic on the window.** For `f` continuous on `[0, 2T]`,
every coefficient at the half-integer frequencies `(k + ½)Ω` over `[0, 2T]` vanishes iff
`f(t + T) = f(t)` for `t ∈ [0, T]`. -/
@[tmio T, powerlib_foundation] theorem coeff_odd_eq_zero_iff (hT : 0 < T) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 (2 * T))) :
    (∀ k : ℤ, coeff (mul_pos two_pos hT) f (2 * k + 1) = 0) ↔
      ∀ t ∈ Icc 0 T, f (t + T) = f t := by
  have hfT : ContinuousOn (fun x => f (x + T)) (Icc 0 T) :=
    hf.comp (by fun_prop) (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hf0 : ContinuousOn f (Icc 0 T) := hf.mono (Icc_subset_Icc le_rfl (by linarith))
  constructor
  · intro h0
    have hs := hasSum_sq_coeff_odd hT hf
    simp only [h0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hs
    have hz := hs.unique hasSum_zero
    have hI : ∫ t in (0 : ℝ)..T, (f t - f (t + T)) ^ 2 = 0 := by
      have : (4 * T)⁻¹ ≠ 0 := by positivity
      exact (mul_eq_zero.mp hz).resolve_left this
    intro t ht
    have := eq_zero_of_integral_sq (h := fun t => f t - f (t + T)) hT (hf0.sub hfT) hI t ht
    linarith
  · intro hp k
    rw [coeff_fold hT hf, Odd.neg_one_zpow ⟨k, rfl⟩]
    have : ∫ t in (0 : ℝ)..T, cexp (kernelExp (2 * T) ((2 * k + 1 : ℤ)) * t) *
        ((f t : ℂ) + (-1) * (f (t + T) : ℂ)) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) (fun t ht => by
        rw [uIcc_of_le hT.le] at ht
        simp only [hp t ht]; ring)]
      simp
    rw [this, mul_zero]

/-- **No integer-frequency content iff `T`-antiperiodic on the window.** For `f` continuous on
`[0, 2T]`, every coefficient at the integer multiples `kΩ` over `[0, 2T]` vanishes iff
`f(t + T) = −f(t)` for `t ∈ [0, T]`. -/
@[tmio T, powerlib_foundation] theorem coeff_even_eq_zero_iff (hT : 0 < T) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 (2 * T))) :
    (∀ k : ℤ, coeff (mul_pos two_pos hT) f (2 * k) = 0) ↔
      ∀ t ∈ Icc 0 T, f (t + T) = -f t := by
  have hfT : ContinuousOn (fun x => f (x + T)) (Icc 0 T) :=
    hf.comp (by fun_prop) (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hf0 : ContinuousOn f (Icc 0 T) := hf.mono (Icc_subset_Icc le_rfl (by linarith))
  constructor
  · intro h0
    have hs := hasSum_sq_coeff_even hT hf
    simp only [h0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hs
    have hz := hs.unique hasSum_zero
    have hI : ∫ t in (0 : ℝ)..T, (f t + f (t + T)) ^ 2 = 0 := by
      have : (4 * T)⁻¹ ≠ 0 := by positivity
      exact (mul_eq_zero.mp hz).resolve_left this
    intro t ht
    have := eq_zero_of_integral_sq (h := fun t => f t + f (t + T)) hT (hf0.add hfT) hI t ht
    linarith
  · intro hp k
    rw [coeff_fold hT hf, Even.neg_one_zpow ⟨k, by ring⟩]
    have : ∫ t in (0 : ℝ)..T, cexp (kernelExp (2 * T) ((2 * k : ℤ)) * t) *
        ((f t : ℂ) + 1 * (f (t + T) : ℂ)) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) (fun t ht => by
        rw [uIcc_of_le hT.le] at ht
        simp only [hp t ht]; push_cast; ring)]
      simp
    rw [this, mul_zero]

/-- **The spectral converse of the half-frequency signature.** A `T`-antiperiodic function
(`f(t + T) = −f(t)` on `[0, T]`), continuous on `[0, 2T]`, is nonzero on the window iff it has a
nonzero coefficient at some half-integer frequency `(k + ½)Ω`: a sustained `μ = −1` oscillation
always shows a subharmonic line, and an antiperiodic signal without one is zero. -/
@[tmio T, powerlib_foundation] theorem antiperiodic_ne_zero_iff (hT : 0 < T) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 (2 * T))) (ha : ∀ t ∈ Icc 0 T, f (t + T) = -f t) :
    (∃ t ∈ Icc 0 (2 * T), f t ≠ 0) ↔ ∃ k : ℤ, coeff (mul_pos two_pos hT) f (2 * k + 1) ≠ 0 := by
  constructor
  · rintro ⟨t₀, ht₀, hne⟩
    by_contra h
    push Not at h
    have hp := (coeff_odd_eq_zero_iff hT hf).mp h
    have hz : ∀ t ∈ Icc 0 T, f t = 0 := fun t ht => by
      have h1 := hp t ht; have h2 := ha t ht; linarith
    apply hne
    by_cases hle : t₀ ≤ T
    · exact hz t₀ ⟨ht₀.1, hle⟩
    · push Not at hle
      have hmem : t₀ - T ∈ Icc 0 T := ⟨by linarith, by linarith [ht₀.2]⟩
      rw [show t₀ = (t₀ - T) + T by ring, ha _ hmem, hz _ hmem, neg_zero]
  · rintro ⟨k, hk⟩
    by_contra h
    push Not at h
    apply hk
    rw [coeff_eq_integral, intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) (fun t ht => by
      rw [uIcc_of_le (by linarith)] at ht
      simp only [h t ht, Complex.ofReal_zero, mul_zero])]
    simp

/-! ## Floquet modes with multiplier `−1` -/

section Modes

variable {X : Type*} [Fintype X] [DecidableEq X] {A : ℝ → Matrix X X ℝ}

/-- **A `μ = −1` Floquet mode genuinely shows a subharmonic line.** For a continuous
`T`-periodic `A` and a real eigenvector `M w = −w`, `w ≠ 0`, of the monodromy matrix, over every
window `[s, s + 2T]`, `s ≥ 0`, some state component of the mode `x(t) = Φ(t, 0) w` has a nonzero
coefficient at a half-integer frequency `(k + ½)Ω` (its integer-frequency coefficients vanish,
`Signature.antiperiodic_mode_coeff_even`). -/
@[tmio T, powerlib_foundation] theorem antiperiodic_mode_coeff_odd (hA : Continuous A)
    (hP : Periodic A T) (hT : 0 < T) {w : X → ℝ} (hw0 : w ≠ 0)
    (hw : Periodic.monodromy A T 0 *ᵥ w = -w) {s : ℝ} (hs : 0 ≤ s) :
    ∃ i : X, ∃ k : ℤ,
      coeff (mul_pos two_pos hT) (fun t => (Periodic.transition A (s + t) 0 *ᵥ w) i)
        (2 * k + 1) ≠ 0 := by
  have hw' : Periodic.monodromy A T 0 *ᵥ w = (-1 : ℝ) • w := by rw [hw, neg_one_smul]
  have hΦ : Continuous fun t => Periodic.transition A t 0 :=
    continuous_iff_continuousAt.2 fun t => (Dynamics.stm_hasDerivAt hA t 0).continuousAt
  have hx0 : Periodic.transition A s 0 *ᵥ w ≠ 0 := by
    intro h0
    have hdet : (Periodic.transition A s 0).det ≠ 0 := by
      rw [Periodic.det_transition hA]; exact (Real.exp_pos _).ne'
    exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw0, h0⟩)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
  refine ⟨i, (antiperiodic_ne_zero_iff hT ?_ ?_).mp ⟨0, ⟨le_rfl, by positivity⟩, by simpa using hi⟩⟩
  · exact ((continuous_apply i).comp
      ((hΦ.comp (continuous_const.add continuous_id)).matrix_mulVec continuous_const)).continuousOn
  · intro t ht
    show (Periodic.transition A (s + (t + T)) 0 *ᵥ w) i = -(Periodic.transition A (s + t) 0 *ᵥ w) i
    rw [show s + (t + T) = (s + t) + T by ring,
      Periodic.transition_mulVec_add_period hA hP hT hw' (by linarith [ht.1]), Pi.smul_apply,
      smul_eq_mul, neg_one_mul]

end Modes

/-- **The subharmonic line of the Meissner boundary mode.** On the boundary
`τ = −2 cosh(cT)` of the square-wave oscillator there is a nonzero solution with
`y(t + T) = −y(t)` whose position `x = y₀` has, over `[0, 2T]`, no coefficient at the integer
multiples `kΩ` and a nonzero coefficient at some half-integer frequency `(k + ½)Ω`: the sustained
parametric oscillation is visible as a line at `Ω/2 + kΩ` in the position signal itself. -/
@[tmio T, powerlib_foundation] theorem meissner_boundary_subharmonic {c ω₀ ε ν₁ ν₂ : ℝ}
    (hν₁ : ν₁ ^ 2 = ω₀ ^ 2 * (1 + ε) - c ^ 2) (hν₂ : ν₂ ^ 2 = ω₀ ^ 2 * (1 - ε) - c ^ 2)
    (h₁ : ν₁ ≠ 0) (h₂ : ν₂ ≠ 0) (hT : 0 < T)
    (hb : Meissner.reducedTrace ν₁ ν₂ T = -(2 * Real.cosh (c * T))) :
    ∃ y : ℝ → Fin 2 → ℝ, ContinuousOn y (Ici 0) ∧
      (∀ t, 0 ≤ t → HasDerivWithinAt y
        (Periodic.oscMatrix c (Meissner.stiffness ω₀ ε T t) *ᵥ y t) (Ici t) t) ∧
      y 0 ≠ 0 ∧ (∀ t, 0 ≤ t → y (t + T) = -y t) ∧
      (∀ k : ℤ, coeff (mul_pos two_pos hT) (fun t => y t 0) (2 * k) = 0) ∧
      ∃ k : ℤ, coeff (mul_pos two_pos hT) (fun t => y t 0) (2 * k + 1) ≠ 0 := by
  obtain ⟨w, hw0, -, ⟨y, hyc, hyd, hy0⟩, hall⟩ :=
    Meissner.antiperiodic_of_boundary hν₁ hν₂ h₁ h₂ hT hb
  have hanti := hall y hyc hyd hy0
  have hxc : ContinuousOn (fun t => y t 0) (Icc 0 (2 * T)) :=
    ((continuous_apply 0).comp_continuousOn hyc).mono Icc_subset_Ici_self
  have hxa : ∀ t ∈ Icc 0 T, y (t + T) 0 = -y t 0 := fun t ht => by
    rw [hanti t ht.1, Pi.neg_apply]
  refine ⟨y, hyc, hyd, by rw [hy0]; exact hw0, hanti, (coeff_even_eq_zero_iff hT hxc).mpr hxa,
    (antiperiodic_ne_zero_iff hT hxc hxa).mp ?_⟩
  by_contra hz
  push Not at hz
  apply hw0
  have hd := hasDerivWithinAt_pi.1 (hyd 0 le_rfl) 0
  have hev : (fun t => y t 0) =ᶠ[𝓝[Ici 0] 0] fun _ => (0 : ℝ) := by
    filter_upwards [Icc_mem_nhdsGE (by positivity : (0 : ℝ) < 2 * T)] with t ht
    exact hz t ht
  have hd' := hd.congr_of_eventuallyEq hev.symm (hz 0 ⟨le_rfl, by positivity⟩).symm
  have h1 := (uniqueDiffWithinAt_Ici 0).eq_deriv _ hd' (hasDerivWithinAt_const _ _ (0 : ℝ))
  simp only [Periodic.oscMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1
  rw [← hy0]
  funext j
  fin_cases j
  · exact hz 0 ⟨le_rfl, by positivity⟩
  · simpa using h1

end powerlib.ParametricResonance.Subharmonic
