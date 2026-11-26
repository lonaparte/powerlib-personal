import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Random-phase aggregation of sinusoidal oscillations

Sums of equal-frequency sinusoids with random phases: a uniform phase has vanishing circular
moments, the mean-square amplitude of a sum with pairwise independent centred phasors is the sum
of the squared amplitudes, and the root-mean-square aggregate of `N` equal contributions is
`√N` times one contribution while the coherent (worst-case) sum is `N` times one contribution.

Scope.
* Phases are real random variables `θ k : Ω → ℝ` on a probability space. A phase is *uniform* when
  `pdf.IsUniform θ (Ico 0 (2π)) P` (Mathlib's continuous uniform law on `[0, 2π)`). The
  aggregation law needs only that the phasors `e^{iθ_k}` are centred and that the phases are
  *pairwise* independent; uniform phases are one instance. Amplitudes `a k` are deterministic
  complex numbers (a real amplitude with a phase offset is a complex amplitude).
* A sinusoid `a cos(Ωt + θ)` is identified with its phasor `a e^{iθ}` at a common angular frequency
  `Ω` (`sum_cos_eq_amplitude_cos`). Contributions at different frequencies, amplitude
  fluctuations and the dynamics producing the oscillations are outside the scope.
* Generic probability, not an engineering model: no wind-turbine, wind-farm or grid model is
  formalized. The statements are the probabilistic law behind the report's aggregation argument.

Source: ENTSO-E/WindEurope Technical Group on Forced Oscillations Report (2 July 2026) §1.2
("the oscillatory power injection by one turbine can be partially offset by power oscillations
from other wind turbines due to the phase-shift stemming from the stochastic nature of the
disturbances … more pronounced with an increasing number of turbines, leading to lower oscillation
amplitudes relative to the active power output"), §4.1 "Aggregation of sites" (Site12 = Site02 +
Site08: "damping powers are not correlated across wind turbine generators").

Results.
* `integral_Ico_cexp_int_mul`, `integral_cexp_uniform`, `integral_cos_add_uniform` —
  `∫₀^{2π} e^{ikx} dx = 0` (`k ≠ 0`), so a uniform phase `U` has
  `E e^{ikU} = 0` for every integer `k ≠ 0`; if `Y` is independent of `U` then
  `E cos(Y + kU) = 0`.
* `sum_cos_eq_amplitude_cos` — `Σ a_k cos(Ωt + θ_k) = |S| cos(Ωt + arg S)` with
  `S = Σ a_k e^{iθ_k}` (real `a_k`): the aggregate is a sinusoid of amplitude `|S|`.
* `norm_sum_phasor_le`, `norm_sum_phasor_coherent` — deterministic bound `|S| ≤ Σ |a_k|`, attained
  when all phases are equal and all `a_k ≥ 0` (coherent worst case).
* `integral_normSq_sum_phasor` — pairwise independent phases with centred phasors:
  `E|Σ a_k e^{iθ_k}|² = Σ |a_k|²` (cross terms vanish); `integral_normSq_sum_uniform`: the same
  for pairwise independent uniform phases.
* `rms_sum_equal`, `rms_div_coherent` — equal amplitudes `a`: the RMS aggregate is `√N |a|` and its
  ratio to the coherent sum `N |a|` is `1/√N`; `tendsto_rms_div_coherent`: the ratio tends to `0`
  as `N → ∞`.
* `rms_le_of_le_rating` — if each contribution satisfies `|a_k| ≤ c R_k` (a limit `c` relative to
  the rating `R_k`), the RMS aggregate is at most `c √(Σ R_k²) ≤ c Σ R_k`, a limit relative to
  the aggregate rating; `sqrt_sq_add_sq_lt` (two sites): `√(R₁² + R₂²) < R₁ + R₂` for positive
  ratings, so the margin of the aggregated site is strictly larger.
-/

noncomputable section
namespace powerlib.Stochastic.RandomPhase

open MeasureTheory ProbabilityTheory Set Filter
open scoped ComplexConjugate Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ## Uniform phases -/

/-- `∫₀^{2π} e^{ikx} dx = 0` for every integer `k ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem integral_Ico_cexp_int_mul {k : ℤ} (hk : k ≠ 0) :
    ∫ x in Ico 0 (2 * Real.pi), Complex.exp (k * x * Complex.I) = 0 := by
  have hc : (k : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hk) Complex.I_ne_zero
  rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by positivity)]
  have e : ∀ x : ℝ, Complex.exp (k * x * Complex.I) = Complex.exp ((k * Complex.I) * x) := by
    intro x; ring_nf
  simp_rw [e]
  rw [integral_exp_mul_complex hc]
  have h2 : Complex.exp ((k : ℂ) * Complex.I * (2 * (Real.pi : ℂ))) = 1 := by
    rw [← Complex.exp_int_mul_two_pi_mul_I k]; congr 1; ring
  simp [h2]

/-- A uniform phase on `[0, 2π)` has vanishing circular moments: `E e^{ikU} = 0` for `k ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem integral_cexp_uniform {U : Ω → ℝ}
    (hU : pdf.IsUniform U (Ico 0 (2 * Real.pi)) P) {k : ℤ} (hk : k ≠ 0) :
    ∫ ω, Complex.exp (k * U ω * Complex.I) ∂P = 0 := by
  have hcont : Continuous fun x : ℝ => Complex.exp (k * x * Complex.I) := by fun_prop
  rw [← integral_map (f := fun x : ℝ => Complex.exp (k * x * Complex.I)) hU.aemeasurable
    hcont.aestronglyMeasurable, hU.map_eq, ProbabilityTheory.cond, integral_smul_measure,
    integral_Ico_cexp_int_mul hk, smul_zero]

/-- If `Y` is independent of a uniform phase `U`, then `E cos(Y + kU) = 0` for every integer
`k ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem integral_cos_add_uniform {U Y : Ω → ℝ}
    (hU : pdf.IsUniform U (Ico 0 (2 * Real.pi)) P) (hY : AEMeasurable Y P)
    (hind : IndepFun Y U P) {k : ℤ} (hk : k ≠ 0) :
    ∫ ω, Real.cos (Y ω + k * U ω) ∂P = 0 := by
  have : IsProbabilityMeasure P := hU.isProbabilityMeasure
    (by rw [Real.volume_Ico]; simp [Real.pi_pos]) (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
  have hprod : ∫ ω, Complex.exp (Y ω * Complex.I) * Complex.exp (k * U ω * Complex.I) ∂P = 0 := by
    have := hind.integral_fun_comp_mul_comp (f := fun y : ℝ => Complex.exp (y * Complex.I))
      (g := fun u : ℝ => Complex.exp (k * u * Complex.I)) hY hU.aemeasurable
      (by fun_prop) (by fun_prop)
    rw [this, integral_cexp_uniform hU hk, mul_zero]
  have hint : Integrable (fun ω => Complex.exp (Y ω * Complex.I) *
      Complex.exp (k * U ω * Complex.I)) P := by
    refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact (by fun_prop : Continuous fun p : ℝ × ℝ => Complex.exp (p.1 * Complex.I) *
        Complex.exp (k * p.2 * Complex.I)).comp_aestronglyMeasurable
        (hY.prodMk hU.aemeasurable).aestronglyMeasurable
    · rw [norm_mul, Complex.norm_exp_ofReal_mul_I]
      have : Complex.exp (k * U ω * Complex.I) = Complex.exp (((k * U ω : ℝ)) * Complex.I) := by
        push_cast; ring_nf
      rw [this, Complex.norm_exp_ofReal_mul_I, one_mul]
  have e : ∀ ω, Real.cos (Y ω + k * U ω) =
      (Complex.exp (Y ω * Complex.I) * Complex.exp (k * U ω * Complex.I)).re := by
    intro ω
    rw [← Complex.exp_add, ← Complex.exp_ofReal_mul_I_re (Y ω + k * U ω)]
    congr 2; push_cast; ring
  simp_rw [e]
  have h := integral_re hint
  simp only [RCLike.re_to_complex] at h
  rw [h, hprod, Complex.zero_re]

/-! ## Phasor sums -/

/-- **The aggregate of equal-frequency sinusoids is a sinusoid** whose amplitude is the modulus of
the phasor sum: `Σ a_k cos(Ωt + θ_k) = |S| cos(Ωt + arg S)`, `S = Σ a_k e^{iθ_k}`. -/
@[tmio T, powerlib_foundation] theorem sum_cos_eq_amplitude_cos {ι : Type*} (s : Finset ι)
    (a θ : ι → ℝ) (Ω t : ℝ) :
    ∑ k ∈ s, a k * Real.cos (Ω * t + θ k) =
      ‖∑ k ∈ s, (a k : ℂ) * Complex.exp (θ k * Complex.I)‖ *
        Real.cos (Ω * t + Complex.arg (∑ k ∈ s, (a k : ℂ) * Complex.exp (θ k * Complex.I))) := by
  set S := ∑ k ∈ s, (a k : ℂ) * Complex.exp (θ k * Complex.I)
  have hS : (Complex.exp ((Ω * t : ℝ) * Complex.I) * S).re =
      ‖S‖ * Real.cos (Ω * t + Complex.arg S) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I S]
    rw [show Complex.exp ((Ω * t : ℝ) * Complex.I) * (‖S‖ * Complex.exp (Complex.arg S *
        Complex.I)) = ((‖S‖ : ℝ) : ℂ) * Complex.exp (((Ω * t + Complex.arg S : ℝ)) * Complex.I) by
      rw [mul_left_comm, ← Complex.exp_add]; push_cast; ring_nf]
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  rw [← hS, Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, ← Complex.exp_add, Complex.re_ofReal_mul,
    show (↑(Ω * t) * Complex.I + ↑(θ k) * Complex.I) = ((Ω * t + θ k : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_ofReal_mul_I_re]

/-- Deterministic triangle bound: `|Σ a_k e^{iθ_k}| ≤ Σ |a_k|` for every choice of phases. -/
@[tmio T, powerlib_foundation] theorem norm_sum_phasor_le {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (θ : ι → ℝ) :
    ‖∑ k ∈ s, a k * Complex.exp (θ k * Complex.I)‖ ≤ ∑ k ∈ s, ‖a k‖ := by
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The bound is attained by the coherent sum: equal phases and nonnegative real amplitudes. -/
@[tmio T, powerlib_foundation] theorem norm_sum_phasor_coherent {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (ha : ∀ k ∈ s, 0 ≤ a k) (θ₀ : ℝ) :
    ‖∑ k ∈ s, (a k : ℂ) * Complex.exp (θ₀ * Complex.I)‖ = ∑ k ∈ s, |a k| := by
  rw [← Finset.sum_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, ← Complex.ofReal_sum,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg ha)]
  exact Finset.sum_congr rfl fun k hk => (abs_of_nonneg (ha k hk)).symm

/-! ## Mean-square aggregate -/

/-- **Random-phase aggregation law.** If the phases are pairwise independent and every phasor is
centred (`E e^{iθ_k} = 0`), then `E|Σ a_k e^{iθ_k}|² = Σ |a_k|²`: the cross terms
`a_j ā_k E[e^{iθ_j} e^{−iθ_k}]` vanish. -/
@[tmio T, powerlib_foundation] theorem integral_normSq_sum_phasor [IsProbabilityMeasure P]
    {ι : Type*} [Fintype ι] {θ : ι → Ω → ℝ} (hm : ∀ k, AEMeasurable (θ k) P)
    (hind : Pairwise fun j k => IndepFun (θ j) (θ k) P)
    (hc : ∀ k, ∫ ω, Complex.exp (θ k ω * Complex.I) ∂P = 0) (a : ι → ℂ) :
    ∫ ω, ‖∑ k, a k * Complex.exp (θ k ω * Complex.I)‖ ^ 2 ∂P = ∑ k, ‖a k‖ ^ 2 := by
  classical
  set e : ι → Ω → ℂ := fun k ω => Complex.exp (θ k ω * Complex.I)
  have hconj : ∀ k ω, conj (e k ω) = Complex.exp (-(θ k ω * Complex.I)) := by
    intro k ω; rw [← Complex.exp_conj]; simp
  have hnorm : ∀ k ω, ‖e k ω‖ = 1 := fun k ω => Complex.norm_exp_ofReal_mul_I _
  have hmeas : ∀ k, AEStronglyMeasurable (e k) P := fun k =>
    (by fun_prop : Continuous fun x : ℝ => Complex.exp (x * Complex.I)).comp_aestronglyMeasurable
      (hm k).aestronglyMeasurable
  have hint : ∀ j k, Integrable (fun ω => a j * conj (a k) * (e j ω * conj (e k ω))) P := by
    intro j k
    refine Integrable.of_bound (C := ‖a j * conj (a k)‖)
      (((hmeas j).mul ((hmeas k).star)).const_mul _) (Filter.Eventually.of_forall fun ω => ?_)
    simp only [norm_mul, RCLike.norm_conj, hnorm, mul_one, le_refl]
  have hjk : ∀ j k, ∫ ω, e j ω * conj (e k ω) ∂P = if j = k then 1 else 0 := by
    intro j k
    split_ifs with h
    · subst h
      have : ∀ ω, e j ω * conj (e j ω) = 1 := by
        intro ω; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; simp
      simp [this]
    · have := (hind h).integral_fun_comp_mul_comp
        (f := fun y : ℝ => Complex.exp (y * Complex.I))
        (g := fun u : ℝ => conj (Complex.exp (u * Complex.I))) (hm j) (hm k)
        (by fun_prop) (by fun_prop)
      rw [this, integral_conj, hc j, zero_mul]
  have hexp : ∀ ω, ((‖∑ k, a k * e k ω‖ ^ 2 : ℝ) : ℂ) =
      ∑ j, ∑ k, a j * conj (a k) * (e j ω * conj (e k ω)) := by
    intro ω
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]; ring
  show ∫ ω, ‖∑ k, a k * e k ω‖ ^ 2 ∂P = _
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [hexp]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
  simp_rw [integral_finsetSum _ fun k _ => hint _ k, integral_const_mul, hjk]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
  simp [Complex.mul_conj']

/-- The aggregation law for pairwise independent uniform phases on `[0, 2π)`. -/
@[tmio T, powerlib_foundation] theorem integral_normSq_sum_uniform [IsProbabilityMeasure P]
    {ι : Type*} [Fintype ι] {θ : ι → Ω → ℝ}
    (hU : ∀ k, pdf.IsUniform (θ k) (Ico 0 (2 * Real.pi)) P)
    (hind : Pairwise fun j k => IndepFun (θ j) (θ k) P) (a : ι → ℂ) :
    ∫ ω, ‖∑ k, a k * Complex.exp (θ k ω * Complex.I)‖ ^ 2 ∂P = ∑ k, ‖a k‖ ^ 2 :=
  integral_normSq_sum_phasor (fun k => (hU k).aemeasurable) hind
    (fun k => by simpa using integral_cexp_uniform (hU k) (k := 1) one_ne_zero) a

/-- Equal amplitudes: the RMS aggregate of `N` random-phase contributions of amplitude `a` is
`√N |a|`. -/
@[tmio T, powerlib_foundation] theorem rms_sum_equal [IsProbabilityMeasure P] {ι : Type*}
    [Fintype ι] {θ : ι → Ω → ℝ} (hm : ∀ k, AEMeasurable (θ k) P)
    (hind : Pairwise fun j k => IndepFun (θ j) (θ k) P)
    (hc : ∀ k, ∫ ω, Complex.exp (θ k ω * Complex.I) ∂P = 0) (a : ℂ) :
    √(∫ ω, ‖∑ k, a * Complex.exp (θ k ω * Complex.I)‖ ^ 2 ∂P) =
      √(Fintype.card ι) * ‖a‖ := by
  rw [integral_normSq_sum_phasor hm hind hc (fun _ => a), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg a)]

/-- **`1/√N` law.** The RMS aggregate of `N ≥ 1` equal random-phase contributions divided by the
coherent sum `N |a|` is `1/√N`. -/
@[tmio T, powerlib_foundation] theorem rms_div_coherent [IsProbabilityMeasure P] {ι : Type*}
    [Fintype ι] [Nonempty ι] {θ : ι → Ω → ℝ} (hm : ∀ k, AEMeasurable (θ k) P)
    (hind : Pairwise fun j k => IndepFun (θ j) (θ k) P)
    (hc : ∀ k, ∫ ω, Complex.exp (θ k ω * Complex.I) ∂P = 0) {a : ℂ} (ha : a ≠ 0) :
    √(∫ ω, ‖∑ k, a * Complex.exp (θ k ω * Complex.I)‖ ^ 2 ∂P) / (Fintype.card ι * ‖a‖) =
      1 / √(Fintype.card ι) := by
  rw [rms_sum_equal hm hind hc a]
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hs : 0 < √(Fintype.card ι : ℝ) := Real.sqrt_pos.mpr hN
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hsq : √(Fintype.card ι : ℝ) * √(Fintype.card ι : ℝ) = Fintype.card ι :=
    Real.mul_self_sqrt hN.le
  rw [div_eq_div_iff (by positivity) hs.ne']
  calc √(Fintype.card ι : ℝ) * ‖a‖ * √(Fintype.card ι : ℝ)
      = (√(Fintype.card ι : ℝ) * √(Fintype.card ι : ℝ)) * ‖a‖ := by ring
    _ = 1 * (Fintype.card ι * ‖a‖) := by rw [hsq]; ring

/-- The ratio `1/√N` of the RMS aggregate to the coherent sum tends to `0` as `N → ∞`. -/
@[tmio T, powerlib_foundation] theorem tendsto_rms_div_coherent :
    Tendsto (fun N : ℕ => 1 / √(N : ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => √(N : ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop).comp tendsto_natCast_atTop_atTop
  exact h.inv_tendsto_atTop.congr fun N => by simp [one_div]

/-- **Limits relative to ratings aggregate with margin.** If every contribution satisfies
`|a_k| ≤ c R_k` (`R_k ≥ 0`), the RMS aggregate is at most `c √(Σ R_k²)`, which is at most the
same limit `c Σ R_k` relative to the aggregate rating. -/
@[tmio T, powerlib_foundation] theorem rms_le_of_le_rating [IsProbabilityMeasure P] {ι : Type*}
    [Fintype ι] {θ : ι → Ω → ℝ} (hm : ∀ k, AEMeasurable (θ k) P)
    (hind : Pairwise fun j k => IndepFun (θ j) (θ k) P)
    (hc : ∀ k, ∫ ω, Complex.exp (θ k ω * Complex.I) ∂P = 0) {a : ι → ℂ} {R : ι → ℝ} {c : ℝ}
    (hc0 : 0 ≤ c) (hR : ∀ k, 0 ≤ R k) (ha : ∀ k, ‖a k‖ ≤ c * R k) :
    √(∫ ω, ‖∑ k, a k * Complex.exp (θ k ω * Complex.I)‖ ^ 2 ∂P) ≤ c * √(∑ k, R k ^ 2) ∧
      c * √(∑ k, R k ^ 2) ≤ c * ∑ k, R k := by
  refine ⟨?_, mul_le_mul_of_nonneg_left ?_ hc0⟩
  · rw [integral_normSq_sum_phasor hm hind hc a, ← Real.sqrt_sq hc0, ← Real.sqrt_mul (sq_nonneg c),
      Finset.mul_sum]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ => ?_)
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (ha k) 2
  · rw [Real.sqrt_le_left (Finset.sum_nonneg fun k _ => hR k)]
    exact Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => hR k

/-- Two sites (Site12 = Site02 + Site08): `√(R₁² + R₂²) < R₁ + R₂` for positive ratings, so the
RMS bound of the aggregated site is strictly below the limit relative to its rating. -/
@[tmio T, powerlib_foundation] theorem sqrt_sq_add_sq_lt {R₁ R₂ : ℝ} (h₁ : 0 < R₁) (h₂ : 0 < R₂) :
    √(R₁ ^ 2 + R₂ ^ 2) < R₁ + R₂ := by
  rw [Real.sqrt_lt' (by positivity)]
  nlinarith [mul_pos h₁ h₂]

end powerlib.Stochastic.RandomPhase
