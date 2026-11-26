import theorem.Periodic.ForcedRegime
import theorem.ParametricResonance.Meissner
import theorem.LTI.StartUp
import theorem.LTI.StartUpForced
import theorem.LTI.HarmonicTransfer
import theorem.LTI.Sampling

/-! # Signatures of parametric oscillations: frequency relation, growth and frozen damping

What separates a parametric oscillation from a forced and from a natural one, derived from the
Floquet mechanism. Every free solution of a `T`-periodic linear system is built from Floquet
modes `z(t + T) = μ z(t)`; over a window of `N` pump periods the Fourier coefficients of such a
mode are those of one period multiplied by the geometric sum `Σ_j (μ e^{−2πim/N})^j`. Hence:

* forced regime (`ρ(M) < 1`, periodic input): the steady state is `T`-periodic, so over windows of
  `2T` its coefficients at the half-integer frequencies `(k + ½)Ω` vanish, and those of every
  solution tend to `0` — only `Ωℤ` remains;
* principal parametric resonance (real multiplier `μ = −1`, the tongue boundary of
  `theorem/Periodic/TwoStateBoundary.lean`): the mode is `T`-antiperiodic, all its coefficients at
  the integer multiples `kΩ` vanish — a pure subharmonic `(k + ½)Ω`; a multiplier
  `μ = e^{2πip/N}` confines the mode to `(k + p/N)Ω` (combination resonance for `N ≥ 3`); a
  general multiplier `μ = e^{λT}` gives `z(t) = e^{λt} p(t)` with `p` `T`-periodic, so the
  frequencies are `Im λ + Ωℤ`;
* growth: the peak-to-peak value of a real Floquet mode over successive pump periods is
  multiplied by exactly `|μ|`, so the TR-110 start-up slope is `ln |μ| > 0` and the start-up
  classifier answers "natural" — it cannot separate parametric from natural oscillations;
* frozen damping: the Meissner system (`theorem/ParametricResonance/Meissner.lean`) has an
  explicit family of parameters with positive damping, Hurwitz frozen and averaged matrices and a
  Floquet multiplier outside the unit circle; positive intrinsic damping with a sustained or
  growing oscillation is therefore not specific to forced oscillations. What separates them is
  the frequency relation to the pump.

Scope.
* Signals are real `f : ℝ → ℝ` (or complex `ℂ`-valued) on `[0, ∞)`, continuous there, with
  `f(t + T) = μ f(t)` for `t ≥ 0`; Fourier coefficients over `[0, NT]` are
  `SpecialFunctions.PeriodicWaves.coeff` (Mathlib's `fourierCoeffOn`, index `m` at the frequency
  `mΩ/N`, `Ω = 2π/T`); windows starting at `s` use the shifted signal `t ↦ f(s + t)`.
* The periodic system `ẋ = A(t) x + f(t)` and its Floquet modes are those of
  `theorem/Periodic/ForcedRegime.lean` (continuous `T`-periodic `A`, `f`). The start-up
  quantities are those of `theorem/LTI/StartUp.lean` (`peakToPeak`, `envelope`, `olsSlope`,
  `classify`).
* Generic mathematics; no model family, no measured record.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.1 (forced versus
natural oscillations; "positive intrinsic damping" read as forced), §3.2 (start-up method,
eqs. (3-1)–(3-5), slope test), §3.4–§3.5 (harmonic content of the steady state); the Floquet
mechanism of `theorem/Periodic/ForcedRegime.lean` and the exact Meissner boundary of
`theorem/ParametricResonance/Meissner.lean`.

Corrections and sharpenings.
* TR-110 §3.2 separates natural (`S > 0`) from forced (`S < 0`) start-ups. A parametric
  start-up has `S = ln |μ| > 0` exactly (`slope_floquet`) and is classified natural
  (`classify_floquet`), with the same verdict as a natural start-up of the same growth rate
  (`classify_floquet_eq_natural`): the method needs a third class.
* "Positive intrinsic damping + sustained oscillation ⇒ forced" (§3.1) fails for parametric
  oscillations: `frozen_damping_boundary` (a sustained subharmonic oscillation with Hurwitz
  frozen matrices and no input) and `frozen_damping_paradox` (growth under the same
  conditions).

Results.
* `integral_floquet` — `∫₀^{nT} e^{κx} f = (Σ_{j<n} (μ e^{κT})ʲ) ∫₀ᵀ e^{κx} f` for a Floquet
  signal.
* `integral_window_eq_zero_of_root` — for `μ = e^{2πip/N}` the window integral at index `m`
  vanishes unless `N ∣ m − p`; `coeff_window_eq_zero_of_periodic` (`μ = 1`: only `N ∣ m`),
  `coeff_eq_zero_of_antiperiodic` (`μ = −1`, `N = 2`: only odd `m`), `coeff_eq_zero_of_periodic`
  (`N = 2`: only even `m`).
* `norm_coeff_le` — `|c_m| ≤ sup |f|` over the window.
* `periodicResponse_coeff_odd`, `tendsto_coeff_odd` — in the forced regime the half-integer
  coefficients of the steady state vanish and those of every solution tend to `0`;
  `spectralRadius_monodromy_const_lt_one`, `lti_tendsto_coeff_odd` — the LTI case: a Hurwitz
  `A` is in the forced regime for every `T`, and a periodic input yields only `Ωℤ`.
* `antiperiodic_mode_coeff_even`, `root_mode_coeff` — a real mode with `μ = −1` has no
  coefficient at `kΩ` over any window `[s, s + 2T]`, `s ≥ 0`; a complex mode with
  `μ = e^{2πip/N}` has its window integrals confined to `m ≡ p (mod N)`.
* `floquet_factor` — `μ ≠ 0`, `λ = log μ/T`: `p(t) = e^{−λt} z(t)` is `T`-periodic on `[0, ∞)`,
  `Re λ = ln |μ|/T`, `Im λ = arg μ/T`.
* `peakToPeak_floquet`, `peakToPeak_floquet_period`, `peakToPeak_floquet_pos`,
  `peakToPeak_floquet_eq_envelope` — `X_{i+1} = |μ| X_i`, `X_i = |μ|ⁱ X₀`, `X₀ > 0`, and the
  natural envelope (3-3) with `σ = ln |μ|/T`.
* `slope_floquet` (via `LTI.StartUp.olsSlope_congr`), `classify_floquet`,
  `classify_floquet_eq_natural` — the TR-110 slope of a parametric start-up is `ln |μ|`; the verdict is never "forced", is "natural"
  iff `ε < ln |μ|`, and equals that of every natural start-up with `σT = ln |μ|`.
* `frozen_hurwitz` — positive damping and stiffness `ω₀²(1 ± ε)`, `|ε| < 1`: every frozen state
  matrix is Hurwitz.
* `frozen_damping_paradox` — for `c > 0`, `ν > 0`, `4πc ≤ ν`, the Meissner system with
  `ω₀² = (5ν² + 2c²)/2`, `ε = 3ν²/(5ν² + 2c²)`, `Ω = 3ν` has Hurwitz frozen matrices at every
  instant and a Hurwitz averaged matrix, yet a Floquet multiplier outside the unit circle
  (`τ = −19/8`).
* `frozen_damping_boundary` — between `0` and that depth there is `ε_b` on the exact boundary
  `τ = −2 cosh(cT)` (intermediate values): frozen matrices Hurwitz, and a nonzero solution that
  is `T`-antiperiodic (sustained, period `2T`) with no Fourier content at `kΩ` over any window
  `[s, s + 2T]`.
-/

noncomputable section
namespace powerlib.ParametricResonance.Signature

open Set Matrix Function Filter Topology Complex
open powerlib.SpecialFunctions.PeriodicWaves (coeff kernelExp coeff_eq_integral)
open powerlib.LTI.StartUp (peakToPeak envelope olsSlope classify Verdict)

/-! ## Fourier coefficients of Floquet signals over several periods -/

section Window

open scoped Interval

variable {T : ℝ}

/-- Over `n` periods a Floquet signal `f(t + T) = μ f(t)` contributes the geometric factor
`Σ_{j<n} (μ e^{κT})ʲ` to `∫ e^{κx} f`. -/
@[tmio T, powerlib_foundation] theorem integral_floquet {f : ℝ → ℂ} {μ : ℂ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Ici 0)) (hμ : ∀ t, 0 ≤ t → f (t + T) = μ * f t) (κ : ℂ) (n : ℕ) :
    ∫ x in (0 : ℝ)..n * T, cexp (κ * x) * f x =
      (∑ j ∈ Finset.range n, (μ * cexp (κ * T)) ^ j) * ∫ x in (0 : ℝ)..T, cexp (κ * x) * f x := by
  have hpow : ∀ (j : ℕ) (t : ℝ), 0 ≤ t → f (t + j * T) = μ ^ j * f t := by
    intro j
    induction j with
    | zero => intro t _; simp
    | succ j ih =>
      intro t ht
      have hjT : 0 ≤ t + j * T := by positivity
      rw [show t + ((j + 1 : ℕ) : ℝ) * T = (t + j * T) + T by push_cast; ring, hμ _ hjT,
        ih t ht, pow_succ]
      ring
  have hint : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      IntervalIntegrable (fun x : ℝ => cexp (κ * x) * f x) MeasureTheory.volume a b := by
    intro a b ha hb
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.mul (Continuous.continuousOn (by fun_prop)) (hf.mono ?_)
    intro x hx
    rw [mem_uIcc] at hx
    rcases hx with hx | hx
    · exact mem_Ici.mpr (ha.trans hx.1)
    · exact mem_Ici.mpr (hb.trans hx.1)
  induction n with
  | zero => simp
  | succ n ih =>
    have hnT : (0 : ℝ) ≤ n * T := by positivity
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := n * T)
      (hint _ _ le_rfl hnT) (hint _ _ hnT (by positivity)), ih, Finset.sum_range_succ, add_mul]
    congr 1
    have hshift := intervalIntegral.integral_comp_add_right
      (fun x : ℝ => cexp (κ * x) * f x) (n * T) (a := 0) (b := T)
    rw [zero_add, show T + n * T = ((n + 1 : ℕ) : ℝ) * T by push_cast; ring] at hshift
    rw [← hshift, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : 0 ≤ x := by
      rw [uIcc_of_le hT] at hx
      exact hx.1
    simp only
    rw [show x + n * T = x + (n : ℕ) * T from rfl, hpow n x hx0, mul_pow, ← Complex.exp_nat_mul]
    push_cast
    rw [show κ * (x + n * T) = κ * x + n * (κ * T) by ring, Complex.exp_add]
    ring

/-- **Frequency confinement.** If `μ = e^{2πip/N}` (`N ≥ 1`), the integral of a Floquet signal
against the window kernel `e^{−2πimx/(NT)}` over `[0, NT]` vanishes unless `N ∣ m − p`: the
signal has content only at the frequencies `(p/N + k)Ω`. -/
@[tmio T, powerlib_foundation] theorem integral_window_eq_zero_of_root {f : ℝ → ℂ} (hT : 0 < T)
    (hf : ContinuousOn f (Ici 0)) {N : ℕ} (hN : 0 < N) {p m : ℤ}
    (hμ : ∀ t, 0 ≤ t → f (t + T) = cexp (2 * Real.pi * I * p / N) * f t)
    (hpm : ¬ (N : ℤ) ∣ m - p) :
    ∫ x in (0 : ℝ)..N * T, cexp (-(2 * Real.pi * I * m / (N * T)) * x) * f x = 0 := by
  rw [integral_floquet hT.le hf hμ]
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  set r := cexp (2 * Real.pi * I * p / N) * cexp (-(2 * Real.pi * I * m / (N * T)) * T) with hr
  have hr' : r = cexp ((p - m : ℤ) * (2 * Real.pi * I) / N) := by
    rw [hr, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  have hrN : r ^ N = 1 := by
    rw [hr', ← Complex.exp_nat_mul, show (N : ℂ) * ((p - m : ℤ) * (2 * Real.pi * I) / N) =
      (p - m : ℤ) * (2 * Real.pi * I) by field_simp, Complex.exp_int_mul_two_pi_mul_I]
  have hr1 : r ≠ 1 := by
    rw [hr']
    intro h
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
    apply hpm
    have h2 : ((p - m : ℤ) : ℂ) = (N : ℂ) * k := by
      have := hk
      field_simp at this
      exact this
    have h3 : p - m = (N : ℤ) * k := by exact_mod_cast h2
    exact ⟨-k, by rw [mul_neg, ← h3]; ring⟩
  rw [geom_sum_eq hr1, hrN, sub_self, zero_div, zero_mul]

/-- The window coefficient of a real signal as the window integral. -/
@[tmio T, powerlib_foundation] private theorem coeff_window_eq {N : ℕ} (hNT : 0 < (N : ℝ) * T)
    (f : ℝ → ℝ) (m : ℤ) :
    coeff hNT f m = (1 / ((N : ℝ) * T) : ℂ) *
      ∫ x in (0 : ℝ)..N * T, cexp (-(2 * Real.pi * I * m / (N * T)) * x) * (f x : ℂ) := by
  rw [coeff_eq_integral, kernelExp]
  push_cast
  rfl

/-- A `T`-periodic signal has, over `[0, NT]`, coefficients only at the indices `m` divisible
by `N` (the frequencies `kΩ`). -/
@[tmio T, powerlib_foundation] theorem coeff_window_eq_zero_of_periodic {f : ℝ → ℝ} (hT : 0 < T)
    (hf : ContinuousOn f (Ici 0)) (hp : ∀ t, 0 ≤ t → f (t + T) = f t) {N : ℕ} (hN : 0 < N)
    {m : ℤ} (hm : ¬ (N : ℤ) ∣ m) :
    coeff (mul_pos (Nat.cast_pos.mpr hN) hT) f m = 0 := by
  rw [coeff_window_eq]
  have h := integral_window_eq_zero_of_root (f := fun t => (f t : ℂ)) hT
    (Complex.continuous_ofReal.comp_continuousOn hf) hN (p := 0) (m := m)
    (fun t ht => by simp [hp t ht]) (by simpa using hm)
  rw [h, mul_zero]

/-- A `T`-antiperiodic signal (`f(t + T) = −f(t)`, the mode of the multiplier `−1`) has, over
`[0, 2T]`, no coefficient at even indices: no content at the integer multiples `kΩ`. -/
@[tmio T, powerlib_foundation] theorem coeff_eq_zero_of_antiperiodic {f : ℝ → ℝ} (hT : 0 < T)
    (hf : ContinuousOn f (Ici 0)) (ha : ∀ t, 0 ≤ t → f (t + T) = -f t) {m : ℤ} (hm : Even m) :
    coeff (mul_pos two_pos hT) f m = 0 := by
  have h := integral_window_eq_zero_of_root (f := fun t => (f t : ℂ)) hT
    (Complex.continuous_ofReal.comp_continuousOn hf) (N := 2) two_pos (p := 1) (m := m)
    (fun t ht => by
      rw [show (2 * Real.pi * I * ((1 : ℤ) : ℂ) / ((2 : ℕ) : ℂ)) = Real.pi * I by push_cast; ring,
        Complex.exp_pi_mul_I, ha t ht]
      push_cast
      ring)
    (by
      obtain ⟨k, hk⟩ := hm
      rintro ⟨j, hj⟩
      omega)
  have e := coeff_window_eq (N := 2) (T := T) (by positivity) f m
  have e' : coeff (mul_pos two_pos hT) f m = coeff (show (0 : ℝ) < ((2 : ℕ) : ℝ) * T by
      positivity) f m := by
    congr 1
  rw [e', e, h, mul_zero]

/-- A `T`-periodic signal has, over `[0, 2T]`, no coefficient at odd indices: no content at the
half-integer frequencies `(k + ½)Ω`. -/
@[tmio T, powerlib_foundation] theorem coeff_eq_zero_of_periodic {f : ℝ → ℝ} (hT : 0 < T)
    (hf : ContinuousOn f (Ici 0)) (hp : ∀ t, 0 ≤ t → f (t + T) = f t) {m : ℤ} (hm : Odd m) :
    coeff (mul_pos two_pos hT) f m = 0 := by
  have h := coeff_window_eq_zero_of_periodic hT hf hp (N := 2) two_pos (m := m) (by
    obtain ⟨k, hk⟩ := hm
    rintro ⟨j, hj⟩
    omega)
  have e' : coeff (mul_pos two_pos hT) f m = coeff (show (0 : ℝ) < ((2 : ℕ) : ℝ) * T by
      positivity) f m := by
    congr 1
  rw [e', h]

/-- `|c_m| ≤ C` when `|f| ≤ C` on the window. -/
@[tmio T, powerlib_foundation] theorem norm_coeff_le (hT : 0 < T) {f : ℝ → ℝ} {C : ℝ}
    (hC : ∀ t ∈ Icc 0 T, |f t| ≤ C) (m : ℤ) : ‖coeff hT f m‖ ≤ C := by
  rw [coeff_eq_integral, norm_mul]
  have hb : ∀ x ∈ Ι (0 : ℝ) T, ‖cexp (kernelExp T m * x) * (f x : ℂ)‖ ≤ C := by
    intro x hx
    rw [uIoc_of_le hT.le] at hx
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    have hre : (kernelExp T m * x).re = 0 := by simp [kernelExp]
    rw [hre, Real.exp_zero, one_mul]
    exact hC x ⟨hx.1.le, hx.2⟩
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_pos hT] at hi
  have h1 : ‖(1 / T : ℂ)‖ = 1 / T := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg hT.le]
  rw [h1]
  calc 1 / T * ‖∫ x in (0 : ℝ)..T, cexp (kernelExp T m * x) * (f x : ℂ)‖ ≤ 1 / T * (C * T) := by
        gcongr
    _ = C := by field_simp

end Window

/-! ## The forced regime: only integer harmonics -/

section Forced

open Periodic

variable {X : Type*} [Fintype X] [DecidableEq X] {A : ℝ → Matrix X X ℝ} {f : ℝ → X → ℝ}
  {T : ℝ}

/-- In the forced regime every component of the Floquet–Green steady state has, over every
window `[s, s + 2T]`, no coefficient at the half-integer frequencies `(k + ½)Ω` (odd `m`). -/
@[tmio T, powerlib_foundation] theorem periodicResponse_coeff_odd (hA : Continuous A)
    (hP : Periodic A T) (hT : 0 < T) (hf : Continuous f) (hfP : Periodic f T)
    (hρ : spectralRadius ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ)) < 1) (s : ℝ) (i : X)
    {m : ℤ} (hm : Odd m) :
    coeff (mul_pos two_pos hT) (fun t => periodicResponse A f T (s + t) i) m = 0 := by
  obtain ⟨hd, hper, -⟩ := forced_regime hA hP hT hf hfP hρ
  have hc : Continuous (periodicResponse A f T) :=
    continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
  have hc' : Continuous fun t => periodicResponse A f T (s + t) i :=
    (continuous_apply i).comp (hc.comp (continuous_const.add continuous_id))
  refine coeff_eq_zero_of_periodic (f := fun t => periodicResponse A f T (s + t) i) hT
    hc'.continuousOn (fun t _ => ?_) hm
  show periodicResponse A f T (s + (t + T)) i = periodicResponse A f T (s + t) i
  rw [show s + (t + T) = (s + t) + T by ring, hper (s + t)]

/-- **Forced confinement.** In the forced regime the half-integer coefficients of every global
solution over the windows `[s, s + 2T]` tend to `0` as `s → ∞`. -/
@[tmio T, powerlib_foundation] theorem tendsto_coeff_odd (hA : Continuous A) (hP : Periodic A T)
    (hT : 0 < T) (hf : Continuous f) (hfP : Periodic f T)
    (hρ : spectralRadius ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ)) < 1) {x : ℝ → X → ℝ}
    (hx : ∀ t, HasDerivAt x (A t *ᵥ x t + f t) t) (i : X) {m : ℤ} (hm : Odd m) :
    Tendsto (fun s => coeff (mul_pos two_pos hT) (fun t => x (s + t) i) m) atTop (𝓝 0) := by
  obtain ⟨hd, -, -, -, K, β, hβ, hK⟩ := forced_regime hA hP hT hf hfP hρ
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
  have hpc : Continuous (periodicResponse A f T) :=
    continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
  have hcurve : IsIntegralCurveOn x (fun t v => A t *ᵥ v + f t) (Ici 0) :=
    fun t _ => (hx t).hasDerivWithinAt
  set e0 := ‖x 0 - periodicResponse A f T 0‖
  have hbound : ∀ s, 0 ≤ s → ‖coeff (mul_pos two_pos hT) (fun t => x (s + t) i) m‖ ≤
      |K| * Real.exp (-(β * s)) * e0 := by
    intro s hs
    have hsplit : (fun t => x (s + t) i) = fun t => periodicResponse A f T (s + t) i +
        (x (s + t) i - periodicResponse A f T (s + t) i) := by
      funext t; ring
    have hc1 : Continuous fun t => periodicResponse A f T (s + t) i :=
      (continuous_apply i).comp (hpc.comp (continuous_const.add continuous_id))
    have hc2 : Continuous fun t => x (s + t) i - periodicResponse A f T (s + t) i :=
      ((continuous_apply i).comp (hxc.comp (continuous_const.add continuous_id))).sub hc1
    rw [hsplit, LTI.HarmonicTransfer.coeff_add _ hc1 hc2,
      periodicResponse_coeff_odd hA hP hT hf hfP hρ s i hm, zero_add]
    refine norm_coeff_le _ (fun t ht => ?_) m
    have h1 := hK 0 x hcurve (s + t) (by linarith [ht.1])
    have h2 : |x (s + t) i - periodicResponse A f T (s + t) i| ≤
        ‖x (s + t) - periodicResponse A f T (s + t)‖ := by
      have := norm_le_pi_norm (x (s + t) - periodicResponse A f T (s + t)) i
      simpa [Real.norm_eq_abs] using this
    have h3 : K * Real.exp (-(β * (s + t - 0))) * e0 ≤ |K| * Real.exp (-(β * s)) * e0 := by
      have he : Real.exp (-(β * (s + t - 0))) ≤ Real.exp (-(β * s)) :=
        Real.exp_le_exp.mpr (by nlinarith [ht.1])
      have hK' : K ≤ |K| := le_abs_self K
      have : 0 ≤ e0 := norm_nonneg _
      calc K * Real.exp (-(β * (s + t - 0))) * e0 ≤ |K| * Real.exp (-(β * (s + t - 0))) * e0 := by
            gcongr
        _ ≤ |K| * Real.exp (-(β * s)) * e0 := by gcongr
    linarith
  have hlim : Tendsto (fun s => |K| * Real.exp (-(β * s)) * e0) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop hβ)).inv_tendsto_atTop
    have h' : Tendsto (fun s => Real.exp (-(β * s))) atTop (𝓝 0) := by
      refine h.congr fun s => ?_
      simp [Real.exp_neg]
    simpa using (h'.const_mul |K|).mul_const e0
  exact squeeze_zero_norm' (eventually_atTop.2 ⟨0, hbound⟩) hlim

/-- **The LTI case.** A Hurwitz constant state matrix is in the forced regime for every period:
`ρ(e^{TA}) < 1` (`LTI.isHurwitz_iff_schurStable_exp`). -/
@[tmio T, powerlib_foundation] theorem spectralRadius_monodromy_const_lt_one {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : LinearSystems.IsHurwitz A) {T : ℝ} (hT : 0 < T) :
    spectralRadius ℂ ((monodromy (fun _ => A) T 0).map (algebraMap ℝ ℂ)) < 1 := by
  rw [monodromy_const A hT.le, ← LTI.schurStable_iff_spectralRadius_lt_one]
  exact (LTI.isHurwitz_iff_schurStable_exp A hT).mp hA

/-- A stable LTI system `ẋ = A x + f(t)` with a `T`-periodic input produces only the integer
harmonics `kΩ`: the half-integer coefficients of every global solution over the windows
`[s, s + 2T]` tend to `0`. -/
@[tmio T, powerlib_foundation] theorem lti_tendsto_coeff_odd {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : LinearSystems.IsHurwitz A) {g : ℝ → Fin n → ℝ}
    (hT : 0 < T) (hg : Continuous g) (hgP : Periodic g T) {x : ℝ → Fin n → ℝ}
    (hx : ∀ t, HasDerivAt x (A *ᵥ x t + g t) t) (i : Fin n) {m : ℤ} (hm : Odd m) :
    Tendsto (fun s => coeff (mul_pos two_pos hT) (fun t => x (s + t) i) m) atTop (𝓝 0) :=
  tendsto_coeff_odd (A := fun _ => A) continuous_const (fun _ => rfl) hT hg hgP
    (spectralRadius_monodromy_const_lt_one hA hT) hx i hm

end Forced

/-! ## Parametric modes: the frequency relation -/

section Modes

open Periodic
open scoped Matrix.Norms.Operator

variable {X : Type*} [Fintype X] [DecidableEq X] {A : ℝ → Matrix X X ℝ} {T : ℝ}

/-- **Principal parametric signature.** A real Floquet mode with multiplier `−1`
(`x(t) = Φ(t, 0) w`, `M w = −w`) has, over every window `[s, s + 2T]` with `s ≥ 0`, no
coefficient at the integer multiples `kΩ` (even `m`): a pure subharmonic. -/
@[tmio T, powerlib_foundation] theorem antiperiodic_mode_coeff_even (hA : Continuous A)
    (hP : Periodic A T) (hT : 0 < T) {w : X → ℝ} (hw : monodromy A T 0 *ᵥ w = -w) {s : ℝ}
    (hs : 0 ≤ s) (i : X) {m : ℤ} (hm : Even m) :
    coeff (mul_pos two_pos hT) (fun t => (transition A (s + t) 0 *ᵥ w) i) m = 0 := by
  have hw' : monodromy A T 0 *ᵥ w = (-1 : ℝ) • w := by rw [hw, neg_one_smul]
  have hmode := fun t ht => transition_mulVec_add_period hA hP hT hw' (t := t) ht
  have hΦ : Continuous fun t => transition A t 0 := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    exact (Dynamics.stm_hasDerivAt hA t 0).continuousAt
  have hc : Continuous fun t => (transition A (s + t) 0 *ᵥ w) i :=
    (continuous_apply i).comp
      ((hΦ.comp (continuous_const.add continuous_id)).matrix_mulVec continuous_const)
  refine coeff_eq_zero_of_antiperiodic (f := fun t => (transition A (s + t) 0 *ᵥ w) i) hT
    hc.continuousOn (fun t ht => ?_) hm
  show (transition A (s + (t + T)) 0 *ᵥ w) i = -(transition A (s + t) 0 *ᵥ w) i
  rw [show s + (t + T) = (s + t) + T by ring, hmode (s + t) (by linarith), Pi.smul_apply,
    smul_eq_mul, neg_one_mul]

/-- A complex Floquet mode with a root-of-unity multiplier `μ = e^{2πip/N}` (combination or
fractional resonance) has its window integrals over `[0, NT]` confined to `m ≡ p (mod N)`:
frequencies `(k + p/N)Ω` only. -/
@[tmio T, powerlib_foundation] theorem root_mode_coeff (hA : Continuous A) (hP : Periodic A T)
    (hT : 0 < T) {N : ℕ} (hN : 0 < N) {p m : ℤ} {v : X → ℂ}
    (hv : (monodromy A T 0).map (algebraMap ℝ ℂ) *ᵥ v = cexp (2 * Real.pi * I * p / N) • v)
    (i : X) (hpm : ¬ (N : ℤ) ∣ m - p) :
    ∫ x in (0 : ℝ)..N * T, cexp (-(2 * Real.pi * I * m / (N * T)) * x) *
      ((transition A x 0).map (algebraMap ℝ ℂ) *ᵥ v) i = 0 := by
  have hmode := (floquet_mode hA hP hT hv).1
  have hΦ0 : Continuous fun t => transition A t 0 := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    exact (Dynamics.stm_hasDerivAt hA t 0).continuousAt
  have hΦ : Continuous fun t => (transition A t 0).map (algebraMap ℝ ℂ) :=
    hΦ0.matrix_map (continuous_algebraMap ℝ ℂ)
  have hc : Continuous fun t => ((transition A t 0).map (algebraMap ℝ ℂ) *ᵥ v) i :=
    (continuous_apply i).comp (hΦ.matrix_mulVec continuous_const)
  exact integral_window_eq_zero_of_root hT hc.continuousOn hN
    (fun t ht => by rw [hmode t ht, Pi.smul_apply, smul_eq_mul]) hpm

end Modes

/-- **Floquet factorization of a mode.** For `μ ≠ 0` and `λ = log μ / T`, a signal with
`z(t + T) = μ z(t)` on `[0, ∞)` is `z(t) = e^{λt} p(t)` with `p(t) = e^{−λt} z(t)`
`T`-periodic on `[0, ∞)`; `Re λ = ln |μ|/T` is the growth rate and `Im λ = arg μ/T` the frequency
offset, so the content of `z` lies at `Im λ + Ωℤ`. -/
@[tmio T, powerlib_foundation] theorem floquet_factor {z : ℝ → ℂ} {μ : ℂ} {T : ℝ} (hμ : μ ≠ 0)
    (hT : 0 < T) (hz : ∀ t, 0 ≤ t → z (t + T) = μ * z t) :
    (∀ t, 0 ≤ t → cexp (-(Complex.log μ / T * (t + T : ℝ))) * z (t + T) =
        cexp (-(Complex.log μ / T * t)) * z t) ∧
      (∀ t, z t = cexp (Complex.log μ / T * t) * (cexp (-(Complex.log μ / T * t)) * z t)) ∧
      (Complex.log μ / T).re = Real.log ‖μ‖ / T ∧ (Complex.log μ / T).im = Complex.arg μ / T := by
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  refine ⟨fun t ht => ?_, fun t => ?_, ?_, ?_⟩
  · have e : ((t + T : ℝ) : ℂ) = (t : ℂ) + T := by push_cast; ring
    rw [hz t ht, e, mul_add, neg_add, Complex.exp_add, div_mul_cancel₀ _ hT0,
      Complex.exp_neg (Complex.log μ), Complex.exp_log hμ]
    field_simp
  · rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  · rw [Complex.div_ofReal_re, Complex.log_re]
  · rw [Complex.div_ofReal_im, Complex.log_im]

/-! ## Growth: the TR-110 start-up slope of a parametric oscillation -/

section Growth

variable {x : ℝ → ℝ} {T q : ℝ}

/-- A real Floquet signal `x(t + T) = q x(t)` (`t ≥ 0`) has peak-to-peak values multiplied by
`|q|` from one window to the window shifted by `T` (`LTI.StartUp.peakToPeak_shift` for `q ≥ 0`
on the whole line; here `q` of either sign, on `[0, ∞)`). -/
@[tmio T, powerlib_foundation] theorem peakToPeak_floquet
    (hx : ∀ t, 0 ≤ t → x (t + T) = q * x t) {a b : ℝ} (ha : 0 ≤ a) :
    peakToPeak x (a + T) (b + T) = |q| * peakToPeak x a b := by
  open scoped Pointwise in
  have himg : x '' Icc (a + T) (b + T) = q • (x '' Icc a b) := by
    ext y
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨x (t - T), ⟨t - T, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩, ?_⟩
      have := hx (t - T) (by linarith [ht.1])
      rw [sub_add_cancel] at this
      rw [this, smul_eq_mul]
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t + T, ⟨by linarith [ht.1], by linarith [ht.2]⟩, by
        rw [hx t (ha.trans ht.1), smul_eq_mul]⟩
  rw [peakToPeak, peakToPeak, himg]
  rcases le_or_gt 0 q with hq | hq
  · rw [Real.sSup_smul_of_nonneg hq, Real.sInf_smul_of_nonneg hq, smul_eq_mul, smul_eq_mul,
      abs_of_nonneg hq, mul_sub]
  · rw [Real.sSup_smul_of_nonpos hq.le, Real.sInf_smul_of_nonpos hq.le, smul_eq_mul, smul_eq_mul,
      abs_of_neg hq]
    ring

/-- Over the `i`-th pump period the peak-to-peak value is `|q|ⁱ X₀`. -/
@[tmio T, powerlib_foundation] theorem peakToPeak_floquet_period (hT : 0 ≤ T)
    (hx : ∀ t, 0 ≤ t → x (t + T) = q * x t) (i : ℕ) :
    peakToPeak x (i * T) ((i + 1) * T) = |q| ^ i * peakToPeak x 0 T := by
  induction i with
  | zero => simp
  | succ n ih =>
    have h := peakToPeak_floquet hx (a := n * T) (b := (n + 1) * T) (by positivity)
    rw [show (n : ℝ) * T + T = ((n + 1 : ℕ) : ℝ) * T by push_cast; ring,
      show ((n : ℝ) + 1) * T + T = (((n + 1 : ℕ) : ℝ) + 1) * T by push_cast; ring] at h
    rw [h, ih, pow_succ]
    ring

/-- A continuous Floquet signal with `q ≠ 1` that is not identically zero on `[0, T]` has a
positive peak-to-peak value over the first period. -/
@[tmio T, powerlib_foundation] theorem peakToPeak_floquet_pos (hT : 0 ≤ T)
    (hc : ContinuousOn x (Icc 0 T)) (hx : ∀ t, 0 ≤ t → x (t + T) = q * x t) (hq : q ≠ 1)
    (hne : ∃ t ∈ Icc 0 T, x t ≠ 0) : 0 < peakToPeak x 0 T := by
  have hK := isCompact_Icc (a := (0 : ℝ)) (b := T)
  have hA := hK.bddAbove_image hc
  have hB := hK.bddBelow_image hc
  have hmem : ∀ t ∈ Icc 0 T, sInf (x '' Icc 0 T) ≤ x t ∧ x t ≤ sSup (x '' Icc 0 T) :=
    fun t ht => ⟨csInf_le hB ⟨t, ht, rfl⟩, le_csSup hA ⟨t, ht, rfl⟩⟩
  rw [peakToPeak, sub_pos]
  by_contra hle
  push Not at hle
  -- the signal is constant on `[0, T]`
  have hconst : ∀ t ∈ Icc 0 T, x t = x 0 := by
    intro t ht
    have h1 := hmem t ht
    have h0 := hmem 0 ⟨le_rfl, hT⟩
    linarith [h1.1, h1.2, h0.1, h0.2]
  have hT' := hx 0 le_rfl
  rw [zero_add, hconst T ⟨hT, le_rfl⟩] at hT'
  have h00 : x 0 = 0 := by
    have : (1 - q) * x 0 = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hq))
  obtain ⟨t, ht, hxt⟩ := hne
  exact hxt (by rw [hconst t ht, h00])

/-- The peak-to-peak values of a Floquet signal follow the natural envelope (3-3)
`X_i = E(iT)` with `A = X₀`, `B = 0`, `σ = ln |q|/T`. -/
@[tmio T, powerlib_foundation] theorem peakToPeak_floquet_eq_envelope (hT : 0 < T) (hq : q ≠ 0)
    (hx : ∀ t, 0 ≤ t → x (t + T) = q * x t) (i : ℕ) :
    peakToPeak x (i * T) ((i + 1) * T) =
      envelope (peakToPeak x 0 T) 0 (Real.log |q| / T) (i * T) := by
  rw [peakToPeak_floquet_period hT.le hx, envelope, add_zero,
    show Real.log |q| / T * (i * T) = i * Real.log |q| by field_simp, Real.exp_nat_mul,
    Real.exp_log (abs_pos.mpr hq)]
  ring

/-- **The TR-110 slope of a parametric start-up.** For a continuous Floquet signal with
`|q| > 1`, not identically zero on the first period, the least-squares slope of the log
increments of the peak-to-peak values over `i = 1, …, N` (`N ≥ 2`) is `ln |q|`. -/
@[tmio T, powerlib_foundation] theorem slope_floquet (hT : 0 < T) (hq : 1 < |q|)
    (hc : ContinuousOn x (Icc 0 T)) (hx : ∀ t, 0 ≤ t → x (t + T) = q * x t)
    (hne : ∃ t ∈ Icc 0 T, x t ≠ 0) {N : ℕ} (hN : 2 ≤ N) :
    olsSlope (Finset.Icc 1 N) (fun i : ℕ => (i : ℝ)) (fun i : ℕ =>
      Real.log (peakToPeak x (i * T) ((i + 1) * T) - peakToPeak x ((i - 1) * T) (i * T))) =
      Real.log |q| := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    norm_num at hq
  have hq1 : q ≠ 1 := by
    rintro rfl
    norm_num at hq
  have hX₀ := peakToPeak_floquet_pos hT.le hc hx hq1 hne
  have hσ : 0 < Real.log |q| / T := div_pos (Real.log_pos hq) hT
  have hcongr : ∀ i ∈ Finset.Icc 1 N,
      Real.log (peakToPeak x (i * T) ((i + 1) * T) - peakToPeak x ((i - 1) * T) (i * T)) =
        Real.log (envelope (peakToPeak x 0 T) 0 (Real.log |q| / T) (i * T) -
          envelope (peakToPeak x 0 T) 0 (Real.log |q| / T) ((i - 1) * T)) := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hprev := peakToPeak_floquet_eq_envelope hT hq0 hx (i - 1)
    rw [Nat.cast_sub hi1, Nat.cast_one, sub_add_cancel] at hprev
    rw [peakToPeak_floquet_eq_envelope hT hq0 hx i, hprev]
  rw [LTI.StartUp.olsSlope_congr hcongr, LTI.StartUp.slope_envelope hT (Or.inl ⟨hX₀, hσ⟩) hN]
  field_simp

/-- **The start-up classifier on a parametric oscillation.** The verdict is never "forced", and
it is "natural" exactly when `ε < ln |q|`. -/
@[tmio T, powerlib_foundation] theorem classify_floquet (hT : 0 < T) (hq : 1 < |q|)
    (hc : ContinuousOn x (Icc 0 T)) (hx : ∀ t, 0 ≤ t → x (t + T) = q * x t)
    (hne : ∃ t ∈ Icc 0 T, x t ≠ 0) {ε : ℝ} (hε : 0 ≤ ε) {N : ℕ} (hN : 2 ≤ N) :
    let S := olsSlope (Finset.Icc 1 N) (fun i : ℕ => (i : ℝ)) (fun i : ℕ =>
      Real.log (peakToPeak x (i * T) ((i + 1) * T) - peakToPeak x ((i - 1) * T) (i * T)))
    classify ε S ≠ .forced ∧ (classify ε S = .natural ↔ ε < Real.log |q|) := by
  intro S
  have hS : S = Real.log |q| := slope_floquet hT hq hc hx hne hN
  rw [hS]
  exact ⟨LTI.StartUp.classify_ne_forced hε (Real.log_pos hq),
    LTI.StartUp.classify_eq_natural_iff ε _⟩

/-- **The start-up method cannot separate parametric from natural oscillations.** A parametric
start-up and a natural start-up `m ẍ + c ẋ + k x = 0` (`σ > 0`) with the same growth per
period `σ · 2π/ω_d = ln |q|` receive the same verdict. -/
@[tmio T, powerlib_foundation] theorem classify_floquet_eq_natural (hT : 0 < T) (hq : 1 < |q|)
    (hc : ContinuousOn x (Icc 0 T)) (hx : ∀ t, 0 ≤ t → x (t + T) = q * x t)
    (hne : ∃ t ∈ Icc 0 T, x t ≠ 0) {m c k σ ωd ε : ℝ} (hm : m ≠ 0) (hσ : σ = -(c / (2 * m)))
    (hωd : ωd ^ 2 = k / m - σ ^ 2) (hωd0 : 0 < ωd) (hσ0 : 0 < σ)
    {y v a : ℝ → ℝ} (hy : ∀ t, HasDerivAt y (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * y t = 0) (hy0 : y 0 ≠ 0 ∨ v 0 ≠ 0)
    (hrate : σ * (2 * Real.pi / ωd) = Real.log |q|) {N : ℕ} (hN : 2 ≤ N) :
    classify ε (olsSlope (Finset.Icc 1 N) (fun i : ℕ => (i : ℝ)) (fun i : ℕ =>
        Real.log (peakToPeak x (i * T) ((i + 1) * T) - peakToPeak x ((i - 1) * T) (i * T)))) =
      classify ε (olsSlope (Finset.Icc 1 N) (fun i : ℕ => (i : ℝ)) (fun i : ℕ =>
        Real.log (peakToPeak y (i * (2 * Real.pi / ωd)) ((i + 1) * (2 * Real.pi / ωd)) -
          peakToPeak y ((i - 1) * (2 * Real.pi / ωd)) (i * (2 * Real.pi / ωd))))) := by
  rw [slope_floquet hT hq hc hx hne hN,
    LTI.StartUp.slope_natural hm hσ hωd hωd0 hσ0 hy hv heq hy0 hN, hrate]

end Growth

/-! ## The frozen-damping paradox -/

section Paradox

open Meissner

@[tmio T, powerlib_foundation] private theorem sinh_le_div_one_sub {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x < 1) : Real.sinh x ≤ x / (1 - x) := by
  rcases hx0.eq_or_lt with rfl | hpos
  · simp
  have h1 : Real.exp x < 1 / (1 - x) := Real.exp_bound_div_one_sub_of_interval' hpos hx1
  have h2 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have h3 : 1 / (1 - x) - (1 - x) ≤ 2 * (x / (1 - x)) := by
    have hd : 0 < 1 - x := by linarith
    rw [div_sub' hd.ne', mul_div_assoc', div_le_div_iff_of_pos_right hd]
    nlinarith
  rw [Real.sinh_eq]
  linarith

/-- Positive damping and positive stiffness `ω₀²(1 ± ε)` (`|ε| < 1`): every frozen state matrix
of the Meissner equation is Hurwitz. -/
@[tmio T, powerlib_foundation] theorem frozen_hurwitz {c ω₀ ε : ℝ} (hc : 0 < c) (hω : 0 < ω₀ ^ 2)
    (hε : |ε| < 1) (T t : ℝ) :
    LinearSystems.IsHurwitz (Periodic.oscMatrix c (stiffness ω₀ ε T t)) := by
  rw [Criteria.isHurwitz_fin_two_iff, Periodic.trace_oscMatrix, Periodic.det_oscMatrix]
  refine ⟨by linarith, ?_⟩
  have h := abs_lt.mp hε
  simp only [stiffness, SpecialFunctions.PeriodicWaves.squareWave]
  split_ifs
  · nlinarith
  · nlinarith

/-- The instance: `ν₁ = 2ν`, `ν₂ = ν`, `T = 2π/(3ν)` sits at the tongue centre with
`τ = −19/8`, and `4πc ≤ ν` gives `cosh(cT) < 19/16`. -/
@[tmio T, powerlib_foundation] private theorem instance_bounds {c ν : ℝ} (hc : 0 < c)
    (hν : 0 < ν) (hcν : 4 * Real.pi * c ≤ ν) :
    reducedTrace (2 * ν) ν (2 * Real.pi / (3 * ν)) = -(19 / 8) ∧
      Real.sinh (c * (2 * Real.pi / (3 * ν)) / 2) ≤ 1 / 11 ∧
      2 * Real.cosh (c * (2 * Real.pi / (3 * ν))) < 19 / 8 := by
  set T := 2 * Real.pi / (3 * ν) with hT
  have hTc : T = 2 * Real.pi / (2 * ν + ν) := by rw [hT]; ring_nf
  have hθ : 2 * ν * T / 2 = 2 * Real.pi / 3 := by rw [hT]; field_simp
  have hsin : Real.sin (2 * ν * T / 2) ^ 2 = 3 / 4 := by
    rw [hθ, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub,
      Real.sin_pi_div_three, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hx : c * T / 2 = Real.pi * c / (3 * ν) := by rw [hT]; field_simp
  have hx0 : 0 ≤ Real.pi * c / (3 * ν) := by positivity
  have hx1 : Real.pi * c / (3 * ν) ≤ 1 / 12 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
  have hsh := sinh_le_div_one_sub hx0 (by linarith)
  have hbound : Real.sinh (c * T / 2) ≤ 1 / 11 := by
    rw [hx]
    refine hsh.trans ?_
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hsh0 : 0 ≤ Real.sinh (c * T / 2) := Real.sinh_nonneg_iff.mpr (by rw [hx]; exact hx0)
  refine ⟨?_, hbound, ?_⟩
  · rw [reducedTrace_centre (by positivity) hν hTc, hsin]
    field_simp
    ring
  · have hcosh : Real.cosh (c * T) = 1 + 2 * Real.sinh (c * T / 2) ^ 2 := by
      rw [show c * T = 2 * (c * T / 2) by ring, Real.cosh_two_mul, Real.cosh_sq]
      ring_nf
    rw [hcosh]
    nlinarith [pow_le_pow_left₀ hsh0 hbound 2]

/-- **The frozen-damping paradox.** For `c > 0`, `ν > 0` with `4πc ≤ ν`, the Meissner system
with `ω₀² = (5ν² + 2c²)/2`, `ε = 3ν²/(5ν² + 2c²)` and pump period `T = 2π/(3ν)` (`Ω = 3ν`,
the half periods carry `ν₁ = 2ν`, `ν₂ = ν`) has positive damping, every frozen state matrix
`[[0, 1], [−k(t), −2c]]` and the averaged matrix `[[0, 1], [−ω₀², −2c]]` are Hurwitz, and yet a
Floquet multiplier lies outside the unit circle (`τ = −19/8`). -/
@[tmio T, powerlib_foundation] theorem frozen_damping_paradox {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hcν : 4 * Real.pi * c ≤ ν) :
    (∀ t, LinearSystems.IsHurwitz (Periodic.oscMatrix c
        (stiffness (√((5 * ν ^ 2 + 2 * c ^ 2) / 2)) (3 * ν ^ 2 / (5 * ν ^ 2 + 2 * c ^ 2))
          (2 * Real.pi / (3 * ν)) t))) ∧
      LinearSystems.IsHurwitz (Periodic.oscMatrix c (√((5 * ν ^ 2 + 2 * c ^ 2) / 2) ^ 2)) ∧
      ∃ μ ∈ spectrum ℂ ((meissnerMonodromy c (√((5 * ν ^ 2 + 2 * c ^ 2) / 2))
          (3 * ν ^ 2 / (5 * ν ^ 2 + 2 * c ^ 2)) (2 * Real.pi / (3 * ν))).map (algebraMap ℝ ℂ)),
        1 < ‖μ‖ := by
  set ω₀ := √((5 * ν ^ 2 + 2 * c ^ 2) / 2) with hω₀
  set ε := 3 * ν ^ 2 / (5 * ν ^ 2 + 2 * c ^ 2) with hε
  set T := 2 * Real.pi / (3 * ν) with hT
  have hD : 0 < 5 * ν ^ 2 + 2 * c ^ 2 := by positivity
  have hω₀sq : ω₀ ^ 2 = (5 * ν ^ 2 + 2 * c ^ 2) / 2 := Real.sq_sqrt (by positivity)
  have hp : ω₀ ^ 2 * (1 + ε) = 4 * ν ^ 2 + c ^ 2 := by
    rw [hω₀sq, hε]; field_simp; ring
  have hm : ω₀ ^ 2 * (1 - ε) = ν ^ 2 + c ^ 2 := by
    rw [hω₀sq, hε]; field_simp; ring
  have hε1 : |ε| < 1 := by
    rw [abs_of_nonneg (by positivity), hε, div_lt_one hD]; nlinarith
  have hω : 0 < ω₀ ^ 2 := by rw [hω₀sq]; positivity
  refine ⟨frozen_hurwitz hc hω hε1 T, ?_, ?_⟩
  · rw [Criteria.isHurwitz_fin_two_iff, Periodic.trace_oscMatrix, Periodic.det_oscMatrix]
    exact ⟨by linarith, hω⟩
  · have hν₁ : (2 * ν) ^ 2 = ω₀ ^ 2 * (1 + ε) - c ^ 2 := by rw [hp]; ring
    have hν₂ : ν ^ 2 = ω₀ ^ 2 * (1 - ε) - c ^ 2 := by rw [hm]; ring
    obtain ⟨hτ, -, hcosh⟩ := instance_bounds hc hν hcν
    rw [floquetUnstable_iff hν₁ hν₂ (by positivity) hν.ne' hc.le (by positivity), hτ]
    rw [abs_neg, abs_of_pos (by norm_num)]
    exact hcosh

/-- **A sustained subharmonic oscillation under positive damping.** In the setting of
`frozen_damping_paradox` there is a modulation depth `ε_b ∈ (0, ε)` at the exact boundary
`τ = −2 cosh(cT)` (intermediate values between the stable `ε = 0` and the unstable `ε`). There
every frozen state matrix is Hurwitz, yet a nonzero solution exists that is `T`-antiperiodic —
sustained, not decaying, of period `2T` — and has, over every window `[s, s + 2T]`, no Fourier
content at the integer multiples `kΩ` of the pump frequency: positive intrinsic damping with a
sustained oscillation, which TR-110 §3.1 reads as forced, here comes with no input at all and
only at the half-integer frequencies `(k + ½)Ω`. -/
@[tmio T, powerlib_foundation] theorem frozen_damping_boundary {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hcν : 4 * Real.pi * c ≤ ν) :
    ∃ εb ∈ Ioo 0 (3 * ν ^ 2 / (5 * ν ^ 2 + 2 * c ^ 2)),
      (∀ t, LinearSystems.IsHurwitz (Periodic.oscMatrix c
        (stiffness (√((5 * ν ^ 2 + 2 * c ^ 2) / 2)) εb (2 * Real.pi / (3 * ν)) t))) ∧
      ∃ y : ℝ → Fin 2 → ℝ, ContinuousOn y (Ici 0) ∧
        (∀ t, 0 ≤ t → HasDerivWithinAt y (Periodic.oscMatrix c
          (stiffness (√((5 * ν ^ 2 + 2 * c ^ 2) / 2)) εb (2 * Real.pi / (3 * ν)) t) *ᵥ y t)
            (Ici t) t) ∧
        y 0 ≠ 0 ∧ (∀ t, 0 ≤ t → y (t + 2 * Real.pi / (3 * ν)) = -y t) ∧
        ∀ s, 0 ≤ s → ∀ (i : Fin 2) (m : ℤ), Even m →
          coeff (mul_pos two_pos (div_pos (mul_pos two_pos Real.pi_pos) (mul_pos three_pos hν)))
            (fun t => y (s + t) i) m = 0 := by
  set ω₀ := √((5 * ν ^ 2 + 2 * c ^ 2) / 2) with hω₀
  set εs := 3 * ν ^ 2 / (5 * ν ^ 2 + 2 * c ^ 2) with hεs
  set T := 2 * Real.pi / (3 * ν) with hT
  have hT0 : 0 < T := by positivity
  have hD : 0 < 5 * ν ^ 2 + 2 * c ^ 2 := by positivity
  have hω₀sq : ω₀ ^ 2 = (5 * ν ^ 2 + 2 * c ^ 2) / 2 := Real.sq_sqrt (by positivity)
  have hω : 0 < ω₀ ^ 2 := by rw [hω₀sq]; positivity
  have hεs0 : 0 < εs := by positivity
  have hεs1 : εs < 1 := by rw [hεs, div_lt_one hD]; nlinarith
  have hp : ω₀ ^ 2 * (1 + εs) = 4 * ν ^ 2 + c ^ 2 := by
    rw [hω₀sq, hεs]; field_simp; ring
  have hm : ω₀ ^ 2 * (1 - εs) = ν ^ 2 + c ^ 2 := by
    rw [hω₀sq, hεs]; field_simp; ring
  -- the two half-period frequencies as functions of the depth
  set ν₁f : ℝ → ℝ := fun e => √(ω₀ ^ 2 * (1 + e) - c ^ 2) with hν₁f
  set ν₂f : ℝ → ℝ := fun e => √(ω₀ ^ 2 * (1 - e) - c ^ 2) with hν₂f
  have hpos₁ : ∀ e ∈ Icc 0 εs, 0 < ω₀ ^ 2 * (1 + e) - c ^ 2 := by
    intro e he
    have : ω₀ ^ 2 * (1 + e) - c ^ 2 ≥ ω₀ ^ 2 - c ^ 2 := by nlinarith [he.1]
    have : ω₀ ^ 2 - c ^ 2 = 5 * ν ^ 2 / 2 := by rw [hω₀sq]; ring
    nlinarith
  have hpos₂ : ∀ e ∈ Icc 0 εs, 0 < ω₀ ^ 2 * (1 - e) - c ^ 2 := by
    intro e he
    have : ω₀ ^ 2 * (1 - e) - c ^ 2 = ν ^ 2 + ω₀ ^ 2 * (εs - e) := by linarith
    have : 0 ≤ ω₀ ^ 2 * (εs - e) := mul_nonneg hω.le (by linarith [he.2])
    nlinarith
  have hν₁pos : ∀ e ∈ Icc 0 εs, 0 < ν₁f e := fun e he => Real.sqrt_pos.mpr (hpos₁ e he)
  have hν₂pos : ∀ e ∈ Icc 0 εs, 0 < ν₂f e := fun e he => Real.sqrt_pos.mpr (hpos₂ e he)
  have hν₁sq : ∀ e ∈ Icc 0 εs, ν₁f e ^ 2 = ω₀ ^ 2 * (1 + e) - c ^ 2 :=
    fun e he => Real.sq_sqrt (hpos₁ e he).le
  have hν₂sq : ∀ e ∈ Icc 0 εs, ν₂f e ^ 2 = ω₀ ^ 2 * (1 - e) - c ^ 2 :=
    fun e he => Real.sq_sqrt (hpos₂ e he).le
  set F : ℝ → ℝ := fun e => reducedTrace (ν₁f e) (ν₂f e) T + 2 * Real.cosh (c * T) with hF
  have hc₁ : Continuous ν₁f := by fun_prop
  have hc₂ : Continuous ν₂f := by fun_prop
  have hFc : ContinuousOn F (Icc 0 εs) := by
    have hd₁ : ContinuousOn (fun e => ν₁f e / ν₂f e) (Icc 0 εs) :=
      hc₁.continuousOn.div hc₂.continuousOn fun e he => (hν₂pos e he).ne'
    have hd₂ : ContinuousOn (fun e => ν₂f e / ν₁f e) (Icc 0 εs) :=
      hc₂.continuousOn.div hc₁.continuousOn fun e he => (hν₁pos e he).ne'
    have hcos₁ : Continuous fun e => Real.cos (ν₁f e * T / 2) := by fun_prop
    have hcos₂ : Continuous fun e => Real.cos (ν₂f e * T / 2) := by fun_prop
    have hsin₁ : Continuous fun e => Real.sin (ν₁f e * T / 2) := by fun_prop
    have hsin₂ : Continuous fun e => Real.sin (ν₂f e * T / 2) := by fun_prop
    simp only [hF, reducedTrace]
    exact ((((continuous_const.mul hcos₁).mul hcos₂).continuousOn.sub
      (((hd₁.add hd₂).mul hsin₁.continuousOn).mul hsin₂.continuousOn)).add continuousOn_const)
  -- the end points
  have hF0 : 0 < F 0 := by
    have h12 : ν₂f 0 = ν₁f 0 := by simp [hν₁f, hν₂f]
    have hne : ν₁f 0 ≠ 0 := (hν₁pos 0 ⟨le_rfl, hεs0.le⟩).ne'
    simp only [hF]
    rw [h12, reducedTrace_self hne]
    have h1 : -1 ≤ Real.cos (ν₁f 0 * T) := Real.neg_one_le_cos _
    have h2 : 1 < Real.cosh (c * T) := Real.one_lt_cosh.mpr (by positivity)
    linarith
  have hFs : F εs < 0 := by
    have e1 : ν₁f εs = 2 * ν := by
      simp only [hν₁f]
      rw [hp, show 4 * ν ^ 2 + c ^ 2 - c ^ 2 = (2 * ν) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    have e2 : ν₂f εs = ν := by
      simp only [hν₂f]
      rw [hm, show ν ^ 2 + c ^ 2 - c ^ 2 = ν ^ 2 by ring, Real.sqrt_sq hν.le]
    obtain ⟨hτ, -, hcosh⟩ := instance_bounds hc hν hcν
    simp only [hF]
    rw [e1, e2, hτ]
    linarith
  obtain ⟨εb, hεb, hFb⟩ := intermediate_value_Icc' hεs0.le hFc ⟨hFs.le, hF0.le⟩
  have hεb0 : εb ≠ 0 := by rintro rfl; linarith
  have hεbs : εb ≠ εs := by rintro rfl; linarith
  have hεbI : εb ∈ Ioo 0 εs :=
    ⟨lt_of_le_of_ne hεb.1 (Ne.symm hεb0), lt_of_le_of_ne hεb.2 hεbs⟩
  have hb : reducedTrace (ν₁f εb) (ν₂f εb) T = -(2 * Real.cosh (c * T)) := by
    simp only [hF] at hFb; linarith
  obtain ⟨w, hw, -, ⟨y, hyc, hyd, hy0⟩, hanti⟩ := antiperiodic_of_boundary (ω₀ := ω₀) (ε := εb)
    (hν₁sq εb hεb) (hν₂sq εb hεb) (hν₁pos εb hεb).ne' (hν₂pos εb hεb).ne' hT0 hb
  have hεb1 : |εb| < 1 := by rw [abs_of_pos hεbI.1]; linarith [hεbI.2]
  refine ⟨εb, hεbI, frozen_hurwitz hc hω hεb1 T, y, hyc, hyd, by rw [hy0]; exact hw,
    hanti y hyc hyd hy0, fun s hs i m hm => ?_⟩
  have hcs : ContinuousOn (fun t => y (s + t) i) (Ici 0) := by
    refine (continuous_apply i).comp_continuousOn (hyc.comp
      (continuous_const.add continuous_id).continuousOn fun t ht => ?_)
    show 0 ≤ s + t
    linarith [mem_Ici.mp ht]
  refine coeff_eq_zero_of_antiperiodic (f := fun t => y (s + t) i) hT0 hcs (fun t ht => ?_) hm
  show y (s + (t + T)) i = -y (s + t) i
  rw [show s + (t + T) = (s + t) + T by ring, hanti y hyc hyd hy0 (s + t) (by linarith)]
  rfl

end Paradox

end powerlib.ParametricResonance.Signature
