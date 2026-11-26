import theorem.LTI.HarmonicTransfer
import theorem.ParametricResonance.EnergyBalance

/-! # The Wirtinger inequality and the necessary pump amplitude of a parametric oscillation

A sustained half-frequency (subharmonic) oscillation of `m δ̈ + D δ̇ + K(t) δ = 0` with a
`T`-periodic stiffness is a `T`-antiperiodic solution, `δ(t + T) = −δ(t)`. Its Fourier series over
`[0, 2T]` has no mean, so the Wirtinger inequality `∫ δ̇² ≥ (π/T)² ∫ δ²` holds; with the period
energy balance `D ∫ δ̇² = ½ ∫ K̇ δ²` it gives the rigorous necessary condition
`2 D (π/T)² ≤ sup |K̇|` for every modulation amplitude (no averaging, no smallness), in particular
`|ε| ≥ D Ω / (2 K_s)` for `K = K_s (1 + ε cos Ωt)`.

Scope.
* Real signals on `[0, L]`, `L > 0`, and their complex Fourier coefficients `c_n` over `[0, L]`
  (`SpecialFunctions.PeriodicWaves.coeff`, Mathlib's `fourierCoeffOn`). Parseval is Mathlib's
  `hasSum_sq_fourierCoeffOn`, applied to continuous signals; the derivative rule is
  `LTI.HarmonicTransfer.coeff_deriv`.
* Wirtinger: `δ` differentiable with continuous derivative, `δ(L) = δ(0)` and zero mean over
  `[0, L]`; for antiperiodic `δ` this holds with `L = 2T`.
* Pump bound: the oscillator of `theorem/ParametricResonance/EnergyBalance.lean` without input,
  `m δ̈ + D δ̇ + K(t) δ = 0`, constant `m, D` (any signs), `K` differentiable with continuous
  derivative and `T`-periodic, `κ` any bound of `|K̇|`. Pure analysis: no model family.

Source: the energy mechanism of parametric oscillations (pump work `½ ∮ K̇ δ²` balancing the
dissipation `D ∮ δ̇²`, Landau–Lifshitz, Mechanics §27) and the classical Wirtinger inequality
(Hardy, Littlewood and Pólya, Inequalities, Ch. VII), applied to the swing equation of IEEE PES TR-110
"Forced Oscillations in Power Systems" (2023) §3.3 with a periodically varying synchronizing
coefficient.

Results.
* `hasSum_sq_coeff` — Parseval over a period for a continuous real signal:
  `Σ |c_n|² = (1/L) ∫₀ᴸ f²`.
* `coeff_neg` — `c_{−n} = conj c_n` for a real signal.
* `hasSum_re_coeff_mul_conj` — the polarized form: `Σ_n Re(c_n(f) conj c_n(g)) = (1/L) ∫₀ᴸ f g`.
* `abs_re_coeff_one_le` — if `∫₀ᴸ f g = 0`, the fundamental cross term is bounded by the mean
  and the harmonic tail: `|Re(c₁(f) conj c₁(g))| ≤ |c₀(f)||c₀(g)|/2 + Σ_{n≥2} |c_n(f)||c_n(g)|`.
* `wirtinger` — `δ(L) = δ(0)` and `∫₀ᴸ δ = 0` give `(2π/L)² ∫₀ᴸ δ² ≤ ∫₀ᴸ δ̇²`.
* `antiperiodic_of_hasDerivAt`, `integral_antiperiodic_eq_zero` — for a `T`-antiperiodic
  function (Mathlib's `Function.Antiperiodic`, `2T`-periodic by `Antiperiodic.periodic_two_mul`)
  the derivative is `T`-antiperiodic and the mean over `[0, 2T]` vanishes.
* `wirtinger_antiperiodic` — `δ(t + T) = −δ(t)` gives `(π/T)² ∫₀^{2T} δ² ≤ ∫₀^{2T} δ̇²`.
* `integral_sq_pos_of_ne_zero` — a nonzero continuous periodic function has `∫ δ² > 0` over a
  period.
* `pump_bound` — a nonzero `T`-antiperiodic solution of `m δ̈ + D δ̇ + K(t) δ = 0` with
  `T`-periodic `K` and `|K̇| ≤ κ` forces `2 D (π/T)² ≤ κ`.
* `pump_amplitude_cos` — for `K = K_s (1 + ε cos Ωt)`, `K_s > 0`, `Ω > 0`, a nonzero
  `(2π/Ω)`-antiperiodic solution (a sustained oscillation at `Ω/2`) forces
  `D Ω / (2 K_s) ≤ |ε|`.
-/

noncomputable section
namespace powerlib.ParametricResonance.Wirtinger

open Complex Set Function MeasureTheory ComplexConjugate
open powerlib.SpecialFunctions.PeriodicWaves

variable {L T : ℝ}

/-! ## Parseval over one period -/

/-- Parseval over `[0, L]` for a continuous real signal: `Σ_n |c_n|² = (1/L) ∫₀ᴸ f²`. -/
@[tmio T, powerlib_foundation] theorem hasSum_sq_coeff (hL : 0 < L) {f : ℝ → ℝ}
    (hf : Continuous f) :
    HasSum (fun n => ‖coeff hL f n‖ ^ 2) (L⁻¹ * ∫ t in (0 : ℝ)..L, f t ^ 2) := by
  have hg : Continuous fun t => (f t : ℂ) := by fun_prop
  have h := hasSum_sq_fourierCoeffOn hL
    ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2 (hg.norm.pow 2).integrableOn_Ioc)
  simp only [sub_zero, smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  exact h

/-- The coefficients of a real signal are conjugate symmetric: `c_{−n} = conj c_n`. -/
@[tmio T, powerlib_foundation] theorem coeff_neg (hL : 0 < L) (f : ℝ → ℝ) (n : ℤ) :
    coeff hL f (-n) = conj (coeff hL f n) := by
  rw [coeff_eq_integral, coeff_eq_integral, map_mul, ← intervalIntegral.intervalIntegral_conj]
  congr 1
  · simp
  · apply intervalIntegral.integral_congr
    intro x _
    simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, kernelExp]
    congr 2
    simp only [map_neg, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast,
      Int.cast_neg, map_ofNat]
    ring

/-- The polarized Parseval identity for real signals:
`Σ_n Re(c_n(f) conj c_n(g)) = (1/L) ∫₀ᴸ f g`. -/
@[tmio T, powerlib_foundation] theorem hasSum_re_coeff_mul_conj (hL : 0 < L) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    HasSum (fun n => (coeff hL f n * conj (coeff hL g n)).re)
      (L⁻¹ * ∫ t in (0 : ℝ)..L, f t * g t) := by
  have hng : Continuous fun t => (-1 : ℝ) * g t := continuous_const.mul hg
  have hp := hasSum_sq_coeff hL (f := fun t => f t + g t) (hf.add hg)
  have hm := hasSum_sq_coeff hL (f := fun t => f t + (-1 : ℝ) * g t) (hf.add hng)
  have hcp : ∀ n, coeff hL (fun t => f t + g t) n = coeff hL f n + coeff hL g n := fun n =>
    LTI.HarmonicTransfer.coeff_add hL hf hg n
  have hcm : ∀ n, coeff hL (fun t => f t + (-1 : ℝ) * g t) n = coeff hL f n - coeff hL g n :=
    fun n => by
      rw [LTI.HarmonicTransfer.coeff_add hL hf hng n, coeff_const_mul]
      push_cast; ring
  have h := (hp.sub hm).div_const 4
  convert h using 1
  · funext n
    rw [hcp, hcm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add, Complex.normSq_sub]
    ring
  · have i1 : IntervalIntegrable (fun t => (f t + g t) ^ 2) volume 0 L :=
      (by fun_prop : Continuous _).intervalIntegrable 0 L
    have i2 : IntervalIntegrable (fun t => (f t + (-1 : ℝ) * g t) ^ 2) volume 0 L :=
      (by fun_prop : Continuous _).intervalIntegrable 0 L
    rw [← mul_sub, ← intervalIntegral.integral_sub i1 i2]
    have e : (fun t => (f t + g t) ^ 2 - (f t + (-1 : ℝ) * g t) ^ 2) =
        fun t => 4 * (f t * g t) := by funext t; ring
    rw [e, intervalIntegral.integral_const_mul]
    ring

/-- Orthogonal real signals (`∫₀ᴸ f g = 0`): the cross term of the fundamental harmonic is
bounded by the mean and the harmonic tail,
`|Re(c₁(f) conj c₁(g))| ≤ |c₀(f)| |c₀(g)| / 2 + Σ_{n ≥ 2} |c_n(f)| |c_n(g)|`. -/
@[tmio T, powerlib_foundation] theorem abs_re_coeff_one_le (hL : 0 < L) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (h0 : ∫ t in (0 : ℝ)..L, f t * g t = 0) :
    |(coeff hL f 1 * conj (coeff hL g 1)).re| ≤
      ‖coeff hL f 0‖ * ‖coeff hL g 0‖ / 2 +
        ∑' n : ℕ, ‖coeff hL f ((n : ℤ) + 2)‖ * ‖coeff hL g ((n : ℤ) + 2)‖ := by
  set r : ℤ → ℝ := fun k => (coeff hL f k * conj (coeff hL g k)).re with hr
  have hH : HasSum r 0 := by
    have := hasSum_re_coeff_mul_conj hL hf hg
    rwa [h0, mul_zero] at this
  have hsym : ∀ k, r (-k) = r k := fun k => by
    simp only [hr, coeff_neg, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have h2 : HasSum (fun n : ℕ => 2 * r n) (r 0) := by
    have := hH.nat_add_neg
    simp only [hsym, zero_add] at this
    convert this using 1
    funext n; ring
  have h3 := (hasSum_nat_add_iff' 2).mpr h2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero,
    Nat.cast_one] at h3
  have h4 : HasSum (fun n : ℕ => r ((n : ℤ) + 2)) ((r 0 - (2 * r 0 + 2 * r 1)) / 2) := by
    convert h3.div_const 2 using 1
    funext n
    push_cast
    ring
  have hb : ∀ k, |r k| ≤ ‖coeff hL f k‖ * ‖coeff hL g k‖ := fun k => by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  have hsf := (hasSum_sq_coeff hL hf).summable
  have hsg := (hasSum_sq_coeff hL hg).summable
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ) + 2) := fun a b h => by
    simpa using h
  have hS : Summable (fun n : ℕ => ‖coeff hL f ((n : ℤ) + 2)‖ * ‖coeff hL g ((n : ℤ) + 2)‖) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (((hsf.add hsg).comp_injective hinj).div_const 2)
    simp only [Function.comp_apply]
    nlinarith [sq_nonneg (‖coeff hL f ((n : ℤ) + 2)‖ - ‖coeff hL g ((n : ℤ) + 2)‖)]
  have hup : (r 0 - (2 * r 0 + 2 * r 1)) / 2 ≤
      ∑' n : ℕ, ‖coeff hL f ((n : ℤ) + 2)‖ * ‖coeff hL g ((n : ℤ) + 2)‖ :=
    hasSum_le (fun n : ℕ => (le_abs_self _).trans (hb ((n : ℤ) + 2))) h4 hS.hasSum
  have hlo : -∑' n : ℕ, ‖coeff hL f ((n : ℤ) + 2)‖ * ‖coeff hL g ((n : ℤ) + 2)‖ ≤
      (r 0 - (2 * r 0 + 2 * r 1)) / 2 :=
    hasSum_le (fun n : ℕ => by
      have h1 := hb ((n : ℤ) + 2)
      have h2 := neg_abs_le (r ((n : ℤ) + 2))
      show -(‖coeff hL f ((n : ℤ) + 2)‖ * ‖coeff hL g ((n : ℤ) + 2)‖) ≤ r ((n : ℤ) + 2)
      linarith) hS.hasSum.neg h4
  have h0b := hb 0
  have ha := le_abs_self (r 0)
  have hna := neg_abs_le (r 0)
  rw [show (coeff hL f 1 * conj (coeff hL g 1)).re = r 1 from rfl, abs_le]
  constructor <;> linarith

/-! ## The Wirtinger inequality -/

/-- The Wirtinger inequality over one period: a `C¹` signal with `δ(L) = δ(0)` and zero mean over
`[0, L]` satisfies `(2π/L)² ∫₀ᴸ δ² ≤ ∫₀ᴸ δ̇²`. -/
@[tmio T, powerlib_foundation] theorem wirtinger (hL : 0 < L) {δ δ' : ℝ → ℝ}
    (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hδ'c : Continuous δ') (hper : δ L = δ 0)
    (hmean : ∫ t in (0 : ℝ)..L, δ t = 0) :
    (2 * Real.pi / L) ^ 2 * ∫ t in (0 : ℝ)..L, δ t ^ 2 ≤ ∫ t in (0 : ℝ)..L, δ' t ^ 2 := by
  have hδc : Continuous δ := continuous_iff_continuousAt.2 fun t => (hδ t).continuousAt
  have hA := (hasSum_sq_coeff hL hδc).mul_left ((2 * Real.pi / L) ^ 2)
  have hB := hasSum_sq_coeff hL hδ'c
  have hle := hasSum_le (fun n => ?_) hA hB
  · have hLi : 0 < L⁻¹ := inv_pos.mpr hL
    have : L⁻¹ * ((2 * Real.pi / L) ^ 2 * ∫ t in (0 : ℝ)..L, δ t ^ 2) ≤
        L⁻¹ * ∫ t in (0 : ℝ)..L, δ' t ^ 2 := by linarith
    exact le_of_mul_le_mul_left this hLi
  · rw [LTI.HarmonicTransfer.coeff_deriv hL hδ hδ'c hper n]
    rcases eq_or_ne n 0 with rfl | hn
    · have h0 : coeff hL δ 0 = 0 := by
        rw [coeff_eq_integral]
        simp only [kernelExp, Int.cast_zero, mul_zero, zero_div, neg_zero, zero_mul,
          Complex.exp_zero, one_mul]
        rw [intervalIntegral.integral_ofReal, hmean, Complex.ofReal_zero, mul_zero]
      rw [h0]; simp
    · have hk : ‖-kernelExp L n‖ = 2 * Real.pi / L * |(n : ℝ)| := by
        rw [kernelExp, neg_neg, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_I,
          Complex.norm_ofNat, Complex.norm_real, Complex.norm_intCast, Complex.norm_real,
          Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg hL.le]
        ring
      rw [norm_mul, mul_pow, hk, mul_pow, sq_abs]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        have : (1 : ℤ) ≤ n ^ 2 := by nlinarith [Int.one_le_abs hn, sq_abs n]
        exact_mod_cast this
      have h2 : 0 ≤ (2 * Real.pi / L) ^ 2 * ‖coeff hL δ n‖ ^ 2 := by positivity
      nlinarith

/-- The derivative of a `T`-antiperiodic differentiable function is `T`-antiperiodic. -/
@[tmio T, powerlib_foundation] theorem antiperiodic_of_hasDerivAt {δ δ' : ℝ → ℝ}
    (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hanti : Antiperiodic δ T) : Antiperiodic δ' T := by
  intro t
  have h := HasDerivAt.comp_add_const t T (hδ (t + T))
  rw [show (fun s => δ (s + T)) = fun s => -δ s from funext hanti] at h
  exact h.unique (hδ t).neg

/-- A continuous `T`-antiperiodic function has zero mean over `[0, 2T]`. -/
@[tmio T, powerlib_foundation] theorem integral_antiperiodic_eq_zero {δ : ℝ → ℝ}
    (hδc : Continuous δ) (hanti : Antiperiodic δ T) :
    ∫ t in (0 : ℝ)..2 * T, δ t = 0 := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hδc.intervalIntegrable 0 T) (hδc.intervalIntegrable T (2 * T))
  have h2 : ∫ t in T..2 * T, δ t = ∫ t in (0 : ℝ)..T, δ (t + T) := by
    rw [intervalIntegral.integral_comp_add_right]
    congr 1 <;> ring
  rw [← h1, h2, show (fun t => δ (t + T)) = fun t => -δ t from funext hanti,
    intervalIntegral.integral_neg, add_neg_cancel]

/-- The Wirtinger inequality for antiperiodic functions: `δ(t + T) = −δ(t)` with `δ ∈ C¹` gives
`(π/T)² ∫₀^{2T} δ² ≤ ∫₀^{2T} δ̇²` (the mean over `[0, 2T]` vanishes, so every harmonic present
has frequency at least `π/T`). -/
@[tmio T, powerlib_foundation] theorem wirtinger_antiperiodic (hT : 0 < T) {δ δ' : ℝ → ℝ}
    (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hδ'c : Continuous δ')
    (hanti : Antiperiodic δ T) :
    (Real.pi / T) ^ 2 * ∫ t in (0 : ℝ)..2 * T, δ t ^ 2 ≤ ∫ t in (0 : ℝ)..2 * T, δ' t ^ 2 := by
  have hδc : Continuous δ := continuous_iff_continuousAt.2 fun t => (hδ t).continuousAt
  have hper : δ (2 * T) = δ 0 := by
    have := hanti.periodic_two_mul 0
    rwa [zero_add] at this
  have h := wirtinger (by positivity) hδ hδ'c hper (integral_antiperiodic_eq_zero hδc hanti)
  rwa [show 2 * Real.pi / (2 * T) = Real.pi / T by field_simp] at h

/-- A nonzero continuous `L`-periodic function has `∫₀ᴸ δ² > 0`. -/
@[tmio T, powerlib_foundation] theorem integral_sq_pos_of_ne_zero (hL : 0 < L) {δ : ℝ → ℝ}
    (hδc : Continuous δ) (hper : Periodic δ L) (hne : ∃ t, δ t ≠ 0) :
    0 < ∫ t in (0 : ℝ)..L, δ t ^ 2 := by
  obtain ⟨t, ht⟩ := hne
  obtain ⟨y, hy, hty⟩ := hper.exists_mem_Ico₀ hL t
  refine intervalIntegral.integral_pos hL (by fun_prop) (fun x _ => sq_nonneg _)
    ⟨y, Ico_subset_Icc_self hy, ?_⟩
  rw [← hty]
  positivity

/-! ## The necessary pump amplitude -/

/-- A sustained half-frequency oscillation needs pumping: a nonzero `T`-antiperiodic solution of
`m δ̈ + D δ̇ + K(t) δ = 0` with `T`-periodic `C¹` stiffness and `|K̇| ≤ κ` forces
`2 D (π/T)² ≤ κ`, for every amplitude of the modulation. -/
@[tmio T, powerlib_foundation] theorem pump_bound {m D κ : ℝ} {K K' δ δ' δ'' : ℝ → ℝ}
    (hT : 0 < T) (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (hK : ∀ t, HasDerivAt K (K' t) t) (hK' : Continuous K') (hKT : Periodic K T)
    (heq : ∀ t, m * δ'' t + D * δ' t + K t * δ t = 0) (hanti : Antiperiodic δ T)
    (hne : ∃ t, δ t ≠ 0) (hκ : ∀ t, |K' t| ≤ κ) :
    2 * D * (Real.pi / T) ^ 2 ≤ κ := by
  have hδc : Continuous δ := continuous_iff_continuousAt.2 fun t => (hδ t).continuousAt
  have hδ'c : Continuous δ' := continuous_iff_continuousAt.2 fun t => (hδ' t).continuousAt
  have hδL := hanti.periodic_two_mul
  have hKL : Periodic K (2 * T) := by rw [two_mul]; exact hKT.add_period hKT
  have hbal := EnergyBalance.parametric_balance hδ hδ' hK hK' heq hδL hKL
  have hw := wirtinger_antiperiodic hT hδ hδ'c hanti
  have hpos := integral_sq_pos_of_ne_zero (by positivity) hδc hδL hne
  have hle : ∫ t in (0 : ℝ)..2 * T, K' t * δ t ^ 2 ≤ κ * ∫ t in (0 : ℝ)..2 * T, δ t ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by positivity)
      ((by fun_prop : Continuous _).intervalIntegrable _ _)
      ((by fun_prop : Continuous _).intervalIntegrable _ _) fun t _ => ?_
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hκ t)) (sq_nonneg _)
  rcases lt_or_ge D 0 with hD | hD
  · have : 0 ≤ κ := (abs_nonneg _).trans (hκ 0)
    have : 2 * D * (Real.pi / T) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
    linarith
  · have h1 : D * ((Real.pi / T) ^ 2 * ∫ t in (0 : ℝ)..2 * T, δ t ^ 2) ≤
        D * ∫ t in (0 : ℝ)..2 * T, δ' t ^ 2 := mul_le_mul_of_nonneg_left hw hD
    have h2 : 2 * D * (Real.pi / T) ^ 2 * ∫ t in (0 : ℝ)..2 * T, δ t ^ 2 ≤
        κ * ∫ t in (0 : ℝ)..2 * T, δ t ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right h2 hpos

/-- The necessary pump amplitude of a sinusoidal modulation `K = K_s (1 + ε cos Ωt)`: a sustained
oscillation at half the pump frequency (a nonzero `(2π/Ω)`-antiperiodic solution) of
`m δ̈ + D δ̇ + K(t) δ = 0` needs `|ε| ≥ D Ω / (2 K_s)`. -/
@[tmio T, powerlib_foundation] theorem pump_amplitude_cos {m D Ks ε Ω : ℝ} {δ δ' δ'' : ℝ → ℝ}
    (hΩ : 0 < Ω) (hKs : 0 < Ks) (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, m * δ'' t + D * δ' t + Ks * (1 + ε * Real.cos (Ω * t)) * δ t = 0)
    (hanti : Antiperiodic δ (2 * Real.pi / Ω)) (hne : ∃ t, δ t ≠ 0) :
    D * Ω / (2 * Ks) ≤ |ε| := by
  have hK : ∀ t, HasDerivAt (fun s => Ks * (1 + ε * Real.cos (Ω * s)))
      (-(Ks * ε * Ω) * Real.sin (Ω * t)) t := by
    intro t
    have h := ((((hasDerivAt_id t).const_mul Ω).cos.const_mul ε).const_add 1).const_mul Ks
    simp only [id, mul_one] at h
    convert h using 1
    ring
  have hKT : Periodic (fun s => Ks * (1 + ε * Real.cos (Ω * s))) (2 * Real.pi / Ω) := by
    intro t
    simp only
    rw [show Ω * (t + 2 * Real.pi / Ω) = Ω * t + 2 * Real.pi by field_simp, Real.cos_add_two_pi]
  have hκ : ∀ t, |-(Ks * ε * Ω) * Real.sin (Ω * t)| ≤ Ks * |ε| * Ω := by
    intro t
    rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_of_pos hKs, abs_of_pos hΩ]
    have := Real.abs_sin_le_one (Ω * t)
    have : 0 ≤ Ks * |ε| * Ω := by positivity
    nlinarith
  have h := pump_bound (by positivity) hδ hδ' hK (by fun_prop) hKT heq hanti hne hκ
  rw [show Real.pi / (2 * Real.pi / Ω) = Ω / 2 by field_simp] at h
  rw [div_le_iff₀ (by positivity)]
  nlinarith

end powerlib.ParametricResonance.Wirtinger
