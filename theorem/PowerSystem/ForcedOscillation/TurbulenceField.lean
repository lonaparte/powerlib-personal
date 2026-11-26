import dependencies.Mathlib
import theorem.Attributes
import theorem.PowerSystem.ForcedOscillation.Turbulence
import Mathlib.Probability.Moments.Covariance

/-! # The turbulence field of a wind farm: IEC turbulence classes, coherence, aggregation

The stochastic wind field behind the virtual wind farms of the ENTSO-E/WindEurope report: the
IEC 61400-1 normal turbulence model with its categories A, B, C, the exponential coherence model
between turbines, and the aggregation of `N` turbines: the band variance of the farm sum lies
between `N` (incoherent) and `N²` (fully coherent) times that of one turbine, strictly below the
coherent value as soon as two turbines are apart, and it decreases as the turbines move apart, so
the relative fluctuation of the farm output decreases with decreasing coherence.

Model boundary.
* Longitudinal wind-speed fluctuation at hub height. Normal turbulence model (IEC 61400-1 ed. 3,
  NTM): standard deviation `σ₁ = I_ref(0.75 V_hub + b)` (`ntmSigma`) with symbolic `I_ref`, `b`
  (`b = 5.6 m/s` in the standard) and `V_hub` (m/s); the categories A, B, C are the exact
  instances `I_ref = 0.16, 0.14, 0.12` (`TurbulenceClass.Iref`).
* Coherence (`coherence`): `Coh(r, f) = exp(−a√((fr/V)² + (br/L_c)²))` between two points a
  distance `r` (m) apart, at frequency `f` (Hz), with symbolic `a ≥ 0`, `b`, coherence scale
  `L_c` and mean wind speed `V` (IEC: `a = 12`, `b = 0.12`, `L_c = 8.1 Λ₁`). It is used as the
  normalized real cross-spectrum (co-coherence, zero phase) of the turbulence at two turbines, as
  in the synthesis of the report's simulated wind fields.
* Farm: `N` turbines with pairwise distances `r_ij` (`r_ii = 0`), identical single-turbine
  one-sided spectrum `S` (the Kaimal spectrum `Turbulence.kaimal`, or `|G|² kaimal` for a turbine
  represented by a gain `G(f)` from wind speed to output in the band); the band variance of the
  farm sum is `∫ S Σ_ij Coh(r_ij, f)` (`farmBandVar`). At the random-variable level the same
  law is `Var(Σ X_i) = σ² Σ_ij Coh` for outputs with covariances `σ² Coh(r_ij, f)`
  (`variance_sum_coherence`). That a stable linear turbine maps the input spectrum to `|G|² S` is
  the filtering law `SpectralMeasure.charFun_acMeasure_filteredCov` /
  `Periodogram.spectralDensity_filteredCov` (two-sided angular convention); here `G` is an input.
* Excluded: the turbine aerodynamics, drivetrain and controller (optimal-λ region, speed control),
  the slow-varying wind component, wind shear, rotational sampling, tower shadow and tower
  oscillations, the conversion to electrical power beyond the gain `G`, the evaluation of the
  RfG clauses, and the report's MATLAB simulation with its 52-week statistics (Table 12:
  simulated data, Rules §2a). The `8.5 m/s` of the simulation enters only as an exact instance of
  the symbolic NTM formula.

Source: ENTSO-E/WindEurope Technical Group on Forced Oscillations Report (2 July 2026)
Appendix C ("Turbulence based on the Kaimal spectral and exponential coherence model (one time
series for each turbine in the wind farm)"; "three different turbulence levels (IEC turbulence A,
B, C) and an average wind speed of 8.5 m/s"; "The active grid power of the entire wind farm was
obtained by summing all individual outputs") and §1.2 (power oscillations of individual turbines
partially offset each other in the aggregate); IEC 61400-1 ed. 3, §6.3.1.3 (normal turbulence
model) and the informative annex on the Kaimal spectrum and exponential coherence model.

Results.
* `ntmSigma`, `TurbulenceClass`, `TurbulenceClass.Iref`, `ntmSigma_pos`, `ntmSigma_lt_ntmSigma`,
  `ntmSigma_strictMono`, `ntmSigma_div`, `ntmIntensity_antitone`, `ntmSigma_class_order`
  (`σ₁(C) < σ₁(B) < σ₁(A)`), `ntmSigma_classes_8p5` (exact instance `1.916, 1.6765, 1.437 m/s`).
* `coherence`, `decayRate`, `coherence_eq` (`Coh = e^{−a|r|κ(f)}`), `coherence_pos`,
  `coherence_le_one`, `coherence_zero`, `coherence_lt_one`, `coherence_anti_dist`,
  `coherence_anti_freq`, `continuous_coherence` — `0 < Coh ≤ 1`, `Coh = 1` at `r = 0`, `< 1`
  between distinct points, decreasing in distance and in frequency.
* `variance_sum_coherence`, `coherence_sum_bounds` — `Var(Σ X_i) = σ² Σ_ij Coh(r_ij, f)` with
  `N ≤ Σ_ij Coh ≤ N²` (incoherent `Nσ²`, fully coherent `N²σ²`).
* `farmBandVar`, `farmBandVar_bounds`, `farmBandVar_lt`, `farmBandVar_anti`,
  `farmBandVar_coherent`, `tendsto_farmBandVar_spread`, `relativeFluctuation_bounds` — the farm
  band variance between `N∫S` and `N²∫S`, equal to `N²∫S` for full coherence, strictly below it
  for distinct turbines, nonincreasing in the distances and tending to the incoherent value `N∫S`
  as the farm is spread out; the relative RMS in `[1/√N, 1]`.
* `farmBandVar_kaimal` — with the Kaimal spectrum: `N bandVar ≤ farmBandVar < N² bandVar`;
  `farmBandVar_filtered_le` — a turbine gain `|G| ≤ g` gives `∫|G|² S ≤ g² bandVar` and a farm
  band variance `≤ N² g² bandVar`.
-/

noncomputable section
namespace powerlib.ForcedOscillation.TurbulenceField

open MeasureTheory ProbabilityTheory Set Filter
open Turbulence (kaimal bandVar)

/-! ## IEC 61400-1 normal turbulence model -/

/-- IEC 61400-1 normal turbulence model: standard deviation of the longitudinal wind speed at hub
height, `σ₁ = I_ref (0.75 V_hub + b)` (`b = 5.6 m/s` in the standard). -/
def ntmSigma (Iref b V : ℝ) : ℝ := Iref * (3 / 4 * V + b)

/-- The IEC 61400-1 (ed. 3) turbulence categories A, B, C. -/
inductive TurbulenceClass
  | A
  | B
  | C

/-- The reference turbulence intensities `I_ref = 0.16, 0.14, 0.12` of the categories A, B, C. -/
def TurbulenceClass.Iref : TurbulenceClass → ℝ
  | .A => 16 / 100
  | .B => 14 / 100
  | .C => 12 / 100

@[tmio M, powerlib_domain] theorem ntmSigma_pos {Iref b V : ℝ} (hI : 0 < Iref) (hb : 0 ≤ b)
    (hV : 0 < V) : 0 < ntmSigma Iref b V := by
  unfold ntmSigma; positivity

/-- `σ₁` increases strictly with the reference intensity. -/
@[tmio M, powerlib_domain] theorem ntmSigma_lt_ntmSigma {I₁ I₂ b V : ℝ} (hI : I₁ < I₂)
    (hpos : 0 < 3 / 4 * V + b) : ntmSigma I₁ b V < ntmSigma I₂ b V := by
  unfold ntmSigma; nlinarith

/-- `σ₁` increases strictly with the hub-height wind speed. -/
@[tmio M, powerlib_domain] theorem ntmSigma_strictMono {Iref : ℝ} (hI : 0 < Iref) (b : ℝ) :
    StrictMono (ntmSigma Iref b) := by
  intro V₁ V₂ h; unfold ntmSigma; nlinarith

/-- The turbulence intensity `σ₁/V = I_ref (3/4 + b/V)` decreases with the wind speed (`b > 0`). -/
@[tmio M, powerlib_domain] theorem ntmSigma_div {Iref b V : ℝ} (hV : V ≠ 0) :
    ntmSigma Iref b V / V = Iref * (3 / 4 + b / V) := by
  unfold ntmSigma; field_simp

@[tmio M, powerlib_domain] theorem ntmIntensity_antitone {Iref b : ℝ} (hI : 0 ≤ Iref) (hb : 0 ≤ b) :
    AntitoneOn (fun V => ntmSigma Iref b V / V) (Ioi 0) := by
  intro V₁ hV₁ V₂ hV₂ h
  simp only [mem_Ioi] at hV₁ hV₂
  simp only
  rw [ntmSigma_div hV₁.ne', ntmSigma_div hV₂.ne']
  have : b / V₂ ≤ b / V₁ := div_le_div_of_nonneg_left hb hV₁ h
  nlinarith

/-- **Class ordering**: `σ₁(C) < σ₁(B) < σ₁(A)` at every operating point with `0.75 V + b > 0`. -/
@[tmio M, powerlib_domain] theorem ntmSigma_class_order {b V : ℝ} (hpos : 0 < 3 / 4 * V + b) :
    ntmSigma TurbulenceClass.C.Iref b V < ntmSigma TurbulenceClass.B.Iref b V ∧
      ntmSigma TurbulenceClass.B.Iref b V < ntmSigma TurbulenceClass.A.Iref b V :=
  ⟨ntmSigma_lt_ntmSigma (by norm_num [TurbulenceClass.Iref]) hpos,
    ntmSigma_lt_ntmSigma (by norm_num [TurbulenceClass.Iref]) hpos⟩

/-- Exact instance at the report's mean wind speed `8.5 m/s` with `b = 5.6 m/s`:
`σ₁ = 1.916, 1.6765, 1.437 m/s` for the categories A, B, C. -/
@[tmio M, powerlib_domain] theorem ntmSigma_classes_8p5 :
    ntmSigma TurbulenceClass.A.Iref (28 / 5) (17 / 2) = 479 / 250 ∧
      ntmSigma TurbulenceClass.B.Iref (28 / 5) (17 / 2) = 3353 / 2000 ∧
      ntmSigma TurbulenceClass.C.Iref (28 / 5) (17 / 2) = 1437 / 1000 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [ntmSigma, TurbulenceClass.Iref]

/-! ## The exponential coherence model -/

/-- Exponential coherence of the longitudinal wind speed at two points a distance `r` apart, at
frequency `f` (Hz): `Coh(r, f) = exp(−a √((f r/V)² + (b r/L_c)²))` (IEC 61400-1: `a = 12`,
`b = 0.12`, `L_c = 8.1 Λ₁`). -/
def coherence (a b Lc V r f : ℝ) : ℝ :=
  Real.exp (-(a * Real.sqrt ((f * r / V) ^ 2 + (b * r / Lc) ^ 2)))

/-- The decay rate per unit distance: `κ(f) = √((f/V)² + (b/L_c)²)`. -/
def decayRate (b Lc V f : ℝ) : ℝ := Real.sqrt ((f / V) ^ 2 + (b / Lc) ^ 2)

/-- `Coh(r, f) = exp(−a |r| κ(f))`. -/
@[tmio M, powerlib_domain] theorem coherence_eq (a b Lc V r f : ℝ) :
    coherence a b Lc V r f = Real.exp (-(a * |r| * decayRate b Lc V f)) := by
  unfold coherence decayRate
  rw [show (f * r / V) ^ 2 + (b * r / Lc) ^ 2 = r ^ 2 * ((f / V) ^ 2 + (b / Lc) ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs, mul_assoc]

@[tmio M, powerlib_domain] theorem coherence_pos (a b Lc V r f : ℝ) : 0 < coherence a b Lc V r f :=
  Real.exp_pos _

/-- `Coh ≤ 1` for `a ≥ 0`. -/
@[tmio M, powerlib_domain] theorem coherence_le_one {a : ℝ} (ha : 0 ≤ a) (b Lc V r f : ℝ) :
    coherence a b Lc V r f ≤ 1 := by
  rw [coherence_eq, Real.exp_le_one_iff, neg_nonpos]
  exact mul_nonneg (mul_nonneg ha (abs_nonneg r)) (Real.sqrt_nonneg _)

/-- A point is fully coherent with itself: `Coh(0, f) = 1`. -/
@[tmio M, powerlib_domain] theorem coherence_zero (a b Lc V f : ℝ) : coherence a b Lc V 0 f = 1 := by
  simp [coherence]

/-- `Coh < 1` for two distinct points (`r ≠ 0`, `a > 0`) at a frequency `f ≠ 0` or with `b ≠ 0`
(`V, L_c ≠ 0`). -/
@[tmio M, powerlib_domain] theorem coherence_lt_one {a b Lc V r f : ℝ} (ha : 0 < a) (hr : r ≠ 0)
    (hV : V ≠ 0) (hL : Lc ≠ 0) (hfb : f ≠ 0 ∨ b ≠ 0) : coherence a b Lc V r f < 1 := by
  rw [coherence_eq, Real.exp_lt_one_iff, neg_lt_zero]
  have hk : 0 < decayRate b Lc V f := by
    unfold decayRate
    apply Real.sqrt_pos.mpr
    rcases hfb with h | h
    · have : 0 < (f / V) ^ 2 := by positivity
      positivity
    · have : 0 < (b / Lc) ^ 2 := by positivity
      positivity
  have := abs_pos.mpr hr
  positivity

/-- **Coherence decreases with distance** (`a ≥ 0`): `|r₁| ≤ |r₂| ⇒ Coh(r₂, f) ≤ Coh(r₁, f)`. -/
@[tmio M, powerlib_domain] theorem coherence_anti_dist {a : ℝ} (ha : 0 ≤ a) (b Lc V f : ℝ)
    {r₁ r₂ : ℝ} (h : |r₁| ≤ |r₂|) : coherence a b Lc V r₂ f ≤ coherence a b Lc V r₁ f := by
  rw [coherence_eq, coherence_eq, Real.exp_le_exp, neg_le_neg_iff]
  have hk : 0 ≤ decayRate b Lc V f := Real.sqrt_nonneg _
  gcongr

/-- **Coherence decreases with frequency** (`a ≥ 0`): `|f₁| ≤ |f₂| ⇒ Coh(r, f₂) ≤ Coh(r, f₁)`. -/
@[tmio M, powerlib_domain] theorem coherence_anti_freq {a : ℝ} (ha : 0 ≤ a) (b Lc V r : ℝ)
    {f₁ f₂ : ℝ} (h : |f₁| ≤ |f₂|) : coherence a b Lc V r f₂ ≤ coherence a b Lc V r f₁ := by
  rw [coherence_eq, coherence_eq, Real.exp_le_exp, neg_le_neg_iff]
  have hk : decayRate b Lc V f₁ ≤ decayRate b Lc V f₂ := by
    unfold decayRate
    apply Real.sqrt_le_sqrt
    have : (f₁ / V) ^ 2 ≤ (f₂ / V) ^ 2 := by
      rw [div_pow, div_pow]
      exact div_le_div_of_nonneg_right (sq_le_sq.mpr h) (sq_nonneg V)
    linarith
  have := mul_nonneg ha (abs_nonneg r)
  gcongr

@[tmio M, powerlib_domain] theorem continuous_coherence (a b Lc V r : ℝ) :
    Continuous (coherence a b Lc V r) := by
  unfold coherence; fun_prop

/-! ## Aggregation over the turbines of a farm -/

/-- **Variance of the farm sum.** `N` turbine outputs (or wind speeds at `N` hubs) `X_i`,
square-integrable, whose covariances in a narrow frequency band at `f` are `σ² Coh(r_ij, f)`
(`r_ij` the distance between turbines `i` and `j`): `Var(Σ X_i) = σ² Σ_{ij} Coh(r_ij, f)`
(`ProbabilityTheory.variance_sum`). -/
@[tmio M, powerlib_domain] theorem variance_sum_coherence {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {N : ℕ} {X : Fin N → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 P)
    {σ a b Lc V f : ℝ} {r : Fin N → Fin N → ℝ}
    (hcov : ∀ i j, cov[X i, X j; P] = σ ^ 2 * coherence a b Lc V (r i j) f) :
    Var[∑ i, X i; P] = σ ^ 2 * ∑ i, ∑ j, coherence a b Lc V (r i j) f := by
  rw [variance_sum hX, Finset.mul_sum]
  simp_rw [Finset.mul_sum, hcov]

/-- **The coherence sum lies between `N` and `N²`.** With `r_ii = 0` and `a ≥ 0`:
`N ≤ Σ_{ij} Coh(r_ij, f) ≤ N²` (incoherent and fully coherent extremes). -/
@[tmio M, powerlib_domain] theorem coherence_sum_bounds {N : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (b Lc V f : ℝ) {r : Fin N → Fin N → ℝ} (hr : ∀ i, r i i = 0) :
    (N : ℝ) ≤ ∑ i, ∑ j, coherence a b Lc V (r i j) f ∧
      ∑ i, ∑ j, coherence a b Lc V (r i j) f ≤ (N : ℝ) ^ 2 := by
  constructor
  · have h : ∀ i, (1 : ℝ) ≤ ∑ j, coherence a b Lc V (r i j) f := by
      intro i
      calc (1 : ℝ) = coherence a b Lc V (r i i) f := by rw [hr, coherence_zero]
        _ ≤ ∑ j, coherence a b Lc V (r i j) f :=
          Finset.single_le_sum (f := fun j => coherence a b Lc V (r i j) f)
            (fun j _ => (coherence_pos _ _ _ _ _ _).le) (Finset.mem_univ i)
    calc (N : ℝ) = ∑ _i : Fin N, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => h i
  · calc ∑ i, ∑ j, coherence a b Lc V (r i j) f ≤ ∑ _i : Fin N, ∑ _j : Fin N, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => coherence_le_one ha _ _ _ _ _
      _ = (N : ℝ) ^ 2 := by simp; ring

/-- **The farm band variance.** For a single-turbine one-sided spectrum `S` (Hz) and the
coherence model, the band `[f₁, f₂]` variance of the sum of `N` turbines is
`∫_{f₁}^{f₂} S(f) Σ_{ij} Coh(r_ij, f) df`. -/
def farmBandVar (S : ℝ → ℝ) (a b Lc V : ℝ) {N : ℕ} (r : Fin N → Fin N → ℝ) (f₁ f₂ : ℝ) : ℝ :=
  ∫ f in f₁..f₂, S f * ∑ i, ∑ j, coherence a b Lc V (r i j) f

/-- **Farm band variance between `N` and `N²` times the single-turbine band variance**: for
`S ≥ 0` continuous on `[f₁, f₂]`, `r_ii = 0`, `a ≥ 0`:
`N ∫S ≤ farmBandVar ≤ N² ∫S`. -/
@[tmio M, powerlib_domain] theorem farmBandVar_bounds {S : ℝ → ℝ} {f₁ f₂ : ℝ} (h12 : f₁ ≤ f₂)
    (hS : ContinuousOn S (Icc f₁ f₂)) (hS0 : ∀ f ∈ Icc f₁ f₂, 0 ≤ S f) {N : ℕ} {a : ℝ}
    (ha : 0 ≤ a) (b Lc V : ℝ) {r : Fin N → Fin N → ℝ} (hr : ∀ i, r i i = 0) :
    (N : ℝ) * ∫ f in f₁..f₂, S f ≤ farmBandVar S a b Lc V r f₁ f₂ ∧
      farmBandVar S a b Lc V r f₁ f₂ ≤ (N : ℝ) ^ 2 * ∫ f in f₁..f₂, S f := by
  have hcs : ContinuousOn (fun f => S f * ∑ i, ∑ j, coherence a b Lc V (r i j) f) (Icc f₁ f₂) :=
    hS.mul (Continuous.continuousOn (by
      exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        continuous_coherence a b Lc V (r i j)))
  have hi : IntervalIntegrable (fun f => S f * ∑ i, ∑ j, coherence a b Lc V (r i j) f) volume f₁ f₂ :=
    hcs.intervalIntegrable_of_Icc h12
  have hiS : IntervalIntegrable S volume f₁ f₂ := hS.intervalIntegrable_of_Icc h12
  unfold farmBandVar
  constructor
  · rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on h12 (hiS.const_mul _) hi fun f hf => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (coherence_sum_bounds ha b Lc V f hr).1 (hS0 f hf)
  · rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on h12 hi (hiS.const_mul _) fun f hf => ?_
    rw [mul_comm ((N : ℝ) ^ 2)]
    exact mul_le_mul_of_nonneg_left (coherence_sum_bounds ha b Lc V f hr).2 (hS0 f hf)

/-- **Partial coherence strictly reduces the farm variance**: if two turbines are a nonzero
distance apart, `a > 0`, `V, L_c ≠ 0`, and `S > 0` on `(f₁, f₂)` with `0 ≤ f₁ < f₂`, then
`farmBandVar < N² ∫S` (the coherent bound is not attained). -/
@[tmio M, powerlib_domain] theorem farmBandVar_lt {S : ℝ → ℝ} {f₁ f₂ : ℝ} (hf₁ : 0 ≤ f₁)
    (h12 : f₁ < f₂) (hS : ContinuousOn S (Icc f₁ f₂)) (hSpos : ∀ f ∈ Ioo f₁ f₂, 0 < S f) {N : ℕ}
    {a b Lc V : ℝ} (ha : 0 < a) (hV : V ≠ 0) (hL : Lc ≠ 0) {r : Fin N → Fin N → ℝ}
    {i₀ j₀ : Fin N} (hij : r i₀ j₀ ≠ 0) :
    farmBandVar S a b Lc V r f₁ f₂ < (N : ℝ) ^ 2 * ∫ f in f₁..f₂, S f := by
  have hcont : Continuous fun f => ∑ i, ∑ j, coherence a b Lc V (r i j) f :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_coherence a b Lc V (r i j)
  have hiS : IntervalIntegrable S volume f₁ f₂ := hS.intervalIntegrable_of_Icc h12.le
  have hi : IntervalIntegrable (fun f => S f * ∑ i, ∑ j, coherence a b Lc V (r i j) f) volume f₁ f₂ :=
    (hS.mul hcont.continuousOn).intervalIntegrable_of_Icc h12.le
  unfold farmBandVar
  rw [← intervalIntegral.integral_const_mul, ← sub_pos, ← intervalIntegral.integral_sub
    (hiS.const_mul _) hi]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ((hiS.const_mul _).sub hi) (fun f hf => ?_) h12
  have hf0 : f ≠ 0 := (lt_of_le_of_lt hf₁ hf.1).ne'
  -- the coherence sum misses `N²` by at least `1 − Coh(r_{i₀j₀}, f) > 0`
  have hlt : ∑ i, ∑ j, coherence a b Lc V (r i j) f < (N : ℝ) ^ 2 := by
    have h1 : ∀ i j, coherence a b Lc V (r i j) f ≤ 1 := fun i j => coherence_le_one ha.le _ _ _ _ _
    have h2 : coherence a b Lc V (r i₀ j₀) f < 1 := coherence_lt_one ha hij hV hL (Or.inl hf0)
    calc ∑ i, ∑ j, coherence a b Lc V (r i j) f < ∑ _i : Fin N, ∑ _j : Fin N, (1 : ℝ) :=
          Finset.sum_lt_sum (fun i _ => Finset.sum_le_sum fun j _ => h1 i j)
            ⟨i₀, Finset.mem_univ _, Finset.sum_lt_sum (fun j _ => h1 i₀ j)
              ⟨j₀, Finset.mem_univ _, h2⟩⟩
      _ = (N : ℝ) ^ 2 := by simp; ring
  have := hSpos f hf
  nlinarith

/-- **The farm variance decreases as the coherence decreases**: moving the turbines apart
(`|r_ij| ≤ |r'_ij|` for all pairs) does not increase the farm band variance (`a ≥ 0`, `S ≥ 0`). -/
@[tmio M, powerlib_domain] theorem farmBandVar_anti {S : ℝ → ℝ} {f₁ f₂ : ℝ} (h12 : f₁ ≤ f₂)
    (hS : ContinuousOn S (Icc f₁ f₂)) (hS0 : ∀ f ∈ Icc f₁ f₂, 0 ≤ S f) {N : ℕ} {a : ℝ}
    (ha : 0 ≤ a) (b Lc V : ℝ) {r r' : Fin N → Fin N → ℝ} (hrr : ∀ i j, |r i j| ≤ |r' i j|) :
    farmBandVar S a b Lc V r' f₁ f₂ ≤ farmBandVar S a b Lc V r f₁ f₂ := by
  have hc : ∀ r : Fin N → Fin N → ℝ, Continuous fun f => ∑ i, ∑ j, coherence a b Lc V (r i j) f :=
    fun r => continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_coherence a b Lc V (r i j)
  unfold farmBandVar
  refine intervalIntegral.integral_mono_on h12 ((hS.mul (hc r').continuousOn).intervalIntegrable_of_Icc h12)
    ((hS.mul (hc r).continuousOn).intervalIntegrable_of_Icc h12) fun f hf => ?_
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    coherence_anti_dist ha b Lc V f (hrr i j)) (hS0 f hf)

/-- **Fully coherent extreme** (`a = 0`, `Coh ≡ 1`): the farm band variance is `N² ∫S`. -/
@[tmio M, powerlib_domain] theorem farmBandVar_coherent (S : ℝ → ℝ) (b Lc V : ℝ) {N : ℕ}
    (r : Fin N → Fin N → ℝ) (f₁ f₂ : ℝ) :
    farmBandVar S 0 b Lc V r f₁ f₂ = (N : ℝ) ^ 2 * ∫ f in f₁..f₂, S f := by
  simp only [farmBandVar, coherence, zero_mul, neg_zero, Real.exp_zero, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [← intervalIntegral.integral_const_mul]
  congr 1; ext f; ring

/-- **Incoherent limit.** Spreading the farm out (`r_ij ↦ κ r_ij`, `κ → ∞`) with distinct
turbines apart (`r_ij ≠ 0` for `i ≠ j`), `a > 0` and `b ≠ 0` (coherence decays even at `f = 0`):
the farm band variance tends to `N ∫S`, the incoherent value. -/
@[tmio M, powerlib_domain] theorem tendsto_farmBandVar_spread {S : ℝ → ℝ} {f₁ f₂ : ℝ}
    (h12 : f₁ ≤ f₂) (hS : ContinuousOn S (Icc f₁ f₂)) {N : ℕ} {a b Lc V : ℝ} (ha : 0 < a)
    (hb : b ≠ 0) (hLc : Lc ≠ 0) {r : Fin N → Fin N → ℝ} (hr : ∀ i, r i i = 0)
    (hr' : ∀ i j, i ≠ j → r i j ≠ 0) :
    Tendsto (fun κ => farmBandVar S a b Lc V (fun i j => κ * r i j) f₁ f₂) atTop
      (nhds ((N : ℝ) * ∫ f in f₁..f₂, S f)) := by
  have hcont : ∀ κ : ℝ, Continuous fun f => ∑ i, ∑ j, coherence a b Lc V (κ * r i j) f :=
    fun κ => continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_coherence a b Lc V _
  have hlim : ∀ f, Tendsto (fun κ : ℝ => ∑ i, ∑ j, coherence a b Lc V (κ * r i j) f) atTop
      (nhds (N : ℝ)) := by
    intro f
    have hd : 0 < decayRate b Lc V f := by
      unfold decayRate
      apply Real.sqrt_pos.mpr
      have : 0 < (b / Lc) ^ 2 := by positivity
      positivity
    have hterm : ∀ i j, Tendsto (fun κ : ℝ => coherence a b Lc V (κ * r i j) f) atTop
        (nhds (if i = j then 1 else 0)) := by
      intro i j
      split_ifs with h
      · subst h
        simp only [hr, mul_zero, coherence_zero]
        exact tendsto_const_nhds
      · have hrij : 0 < |r i j| := abs_pos.mpr (hr' i j h)
        have hlin : Tendsto (fun κ : ℝ => a * |κ * r i j| * decayRate b Lc V f) atTop atTop := by
          have : Tendsto (fun κ : ℝ => κ * (a * |r i j| * decayRate b Lc V f)) atTop atTop :=
            tendsto_id.atTop_mul_const (by positivity)
          refine this.congr' ?_
          filter_upwards [eventually_ge_atTop 0] with κ hκ
          rw [abs_mul, abs_of_nonneg hκ]; ring
        simp only [coherence_eq]
        exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin N)) fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin N)) fun j _ => hterm i j
    simpa [Finset.sum_ite_eq] using h
  have hbound : ∀ κ f, ‖S f * ∑ i, ∑ j, coherence a b Lc V (κ * r i j) f‖ ≤ ‖S f‖ * (N : ℝ) ^ 2 := by
    intro κ f
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hb' := coherence_sum_bounds ha.le b Lc V f (r := fun i j => κ * r i j)
      (fun i => by simp [hr])
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hb'.1, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)])]
    exact hb'.2
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := f₁) (b := f₂) (l := atTop)
    (F := fun κ f => S f * ∑ i, ∑ j, coherence a b Lc V (κ * r i j) f) (f := fun f => S f * N)
    (fun f => ‖S f‖ * (N : ℝ) ^ 2)
    (Eventually.of_forall fun κ => ((hS.mul (hcont κ).continuousOn).mono
      (by rw [uIoc_of_le h12]; exact Ioc_subset_Icc_self)).aestronglyMeasurable measurableSet_uIoc)
    (Eventually.of_forall fun κ => ae_of_all _ fun f _ => hbound κ f)
    ((hS.norm.mul continuousOn_const).intervalIntegrable_of_Icc h12)
    (ae_of_all _ fun f _ => (hlim f).const_mul (S f))
  unfold farmBandVar
  rw [show (N : ℝ) * ∫ f in f₁..f₂, S f = ∫ f in f₁..f₂, S f * N by
    rw [← intervalIntegral.integral_const_mul]; congr 1; ext f; ring]
  exact h

/-- **Relative fluctuation of the farm output.** The band RMS of the farm sum relative to `N`
times the single-turbine band RMS lies in `[1/√N, 1]`: it equals `1` for full coherence and
decreases towards `1/√N` as the coherence decreases (`farmBandVar_anti`). -/
@[tmio M, powerlib_domain] theorem relativeFluctuation_bounds {S : ℝ → ℝ} {f₁ f₂ : ℝ}
    (h12 : f₁ ≤ f₂) (hS : ContinuousOn S (Icc f₁ f₂)) (hS0 : ∀ f ∈ Icc f₁ f₂, 0 ≤ S f) {N : ℕ}
    (hN : 0 < N) {a : ℝ} (ha : 0 ≤ a) (b Lc V : ℝ) {r : Fin N → Fin N → ℝ} (hr : ∀ i, r i i = 0)
    (hpos : 0 < ∫ f in f₁..f₂, S f) :
    1 / Real.sqrt N ≤ Real.sqrt (farmBandVar S a b Lc V r f₁ f₂) / (N * Real.sqrt (∫ f in f₁..f₂, S f)) ∧
      Real.sqrt (farmBandVar S a b Lc V r f₁ f₂) / (N * Real.sqrt (∫ f in f₁..f₂, S f)) ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := farmBandVar_bounds h12 hS hS0 ha b Lc V hr
  set I := ∫ f in f₁..f₂, S f
  set W := farmBandVar S a b Lc V r f₁ f₂
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsI : 0 < Real.sqrt I := Real.sqrt_pos.mpr hpos
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hden : 0 < (N : ℝ) * Real.sqrt I := by positivity
  constructor
  · rw [div_le_div_iff₀ hsN hden, one_mul]
    -- `N √I = √N · √(N I) ≤ √N · √W`
    have h1 : Real.sqrt (N * I) ≤ Real.sqrt W := Real.sqrt_le_sqrt hlo
    have h2 : (N : ℝ) * Real.sqrt I = Real.sqrt N * Real.sqrt (N * I) := by
      rw [Real.sqrt_mul hNr.le, ← mul_assoc, Real.mul_self_sqrt hNr.le]
    rw [h2, mul_comm (Real.sqrt W)]
    exact mul_le_mul_of_nonneg_left h1 hsN.le
  · rw [div_le_one hden]
    calc Real.sqrt W ≤ Real.sqrt ((N : ℝ) ^ 2 * I) := Real.sqrt_le_sqrt hhi
      _ = N * Real.sqrt I := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hNr.le]

/-- **Kaimal instance.** With the Kaimal spectrum the farm band variance lies between `N` and
`N²` times the closed-form band variance `bandVar` (`Turbulence.integral_kaimal_band`), strictly
below `N² bandVar` as soon as two turbines are apart (`a > 0`, `0 ≤ f₁ < f₂`). -/
@[tmio M, powerlib_domain] theorem farmBandVar_kaimal {σ L U f₁ f₂ : ℝ} (hσ : σ ≠ 0) (hL : 0 < L)
    (hU : 0 < U) (hf₁ : 0 ≤ f₁) (h12 : f₁ < f₂) {N : ℕ} {a b Lc V : ℝ} (ha : 0 < a) (hV : V ≠ 0)
    (hLc : Lc ≠ 0) {r : Fin N → Fin N → ℝ} (hr : ∀ i, r i i = 0) {i₀ j₀ : Fin N}
    (hij : r i₀ j₀ ≠ 0) :
    (N : ℝ) * bandVar σ L U f₁ f₂ ≤ farmBandVar (kaimal σ L U) a b Lc V r f₁ f₂ ∧
      farmBandVar (kaimal σ L U) a b Lc V r f₁ f₂ < (N : ℝ) ^ 2 * bandVar σ L U f₁ f₂ := by
  have hS : ContinuousOn (kaimal σ L U) (Icc f₁ f₂) :=
    (Turbulence.continuousOn_kaimal σ hL hU).mono fun f hf => hf₁.trans hf.1
  have hS0 : ∀ f ∈ Icc f₁ f₂, 0 ≤ kaimal σ L U f := fun f hf =>
    (Turbulence.kaimal_pos hσ hL hU (hf₁.trans hf.1)).le
  have hint := Turbulence.integral_kaimal_band σ hL hU hf₁ h12.le
  refine ⟨?_, ?_⟩
  · rw [← hint]; exact (farmBandVar_bounds h12.le hS hS0 ha.le b Lc V hr).1
  · rw [← hint]
    exact farmBandVar_lt hf₁ h12 hS (fun f hf => Turbulence.kaimal_pos hσ hL hU (hf₁.trans hf.1.le))
      ha hV hLc hij

/-! ## A turbine as a linear filter -/

/-- **Filtered band variance.** A turbine represented by a gain `G(f)` from wind-speed fluctuation
to output in the band (`|G(f)| ≤ g` on `[f₁, f₂]`) turns the Kaimal band variance into
`∫_{f₁}^{f₂} |G(f)|² S(f) df ≤ g² bandVar`; for the farm, the band variance of the sum of the
`N` outputs is at most `N² g² bandVar`. -/
@[tmio M, powerlib_domain] theorem farmBandVar_filtered_le {σ L U f₁ f₂ : ℝ} (hσ : σ ≠ 0)
    (hL : 0 < L) (hU : 0 < U) (hf₁ : 0 ≤ f₁) (h12 : f₁ ≤ f₂) {G : ℝ → ℂ}
    (hG : ContinuousOn G (Icc f₁ f₂)) {g : ℝ} (hg : ∀ f ∈ Icc f₁ f₂, ‖G f‖ ≤ g) {N : ℕ}
    {a : ℝ} (ha : 0 ≤ a) (b Lc V : ℝ) {r : Fin N → Fin N → ℝ} (hr : ∀ i, r i i = 0) :
    (∫ f in f₁..f₂, ‖G f‖ ^ 2 * kaimal σ L U f) ≤ g ^ 2 * bandVar σ L U f₁ f₂ ∧
      farmBandVar (fun f => ‖G f‖ ^ 2 * kaimal σ L U f) a b Lc V r f₁ f₂ ≤
        (N : ℝ) ^ 2 * (g ^ 2 * bandVar σ L U f₁ f₂) := by
  have hK : ContinuousOn (kaimal σ L U) (Icc f₁ f₂) :=
    (Turbulence.continuousOn_kaimal σ hL hU).mono fun f hf => hf₁.trans hf.1
  have hK0 : ∀ f ∈ Icc f₁ f₂, 0 ≤ kaimal σ L U f := fun f hf =>
    (Turbulence.kaimal_pos hσ hL hU (hf₁.trans hf.1)).le
  have hS : ContinuousOn (fun f => ‖G f‖ ^ 2 * kaimal σ L U f) (Icc f₁ f₂) :=
    (hG.norm.pow 2).mul hK
  have hS0 : ∀ f ∈ Icc f₁ f₂, 0 ≤ ‖G f‖ ^ 2 * kaimal σ L U f := fun f hf =>
    mul_nonneg (sq_nonneg _) (hK0 f hf)
  have hint := Turbulence.integral_kaimal_band σ hL hU hf₁ h12
  have h1 : (∫ f in f₁..f₂, ‖G f‖ ^ 2 * kaimal σ L U f) ≤ g ^ 2 * bandVar σ L U f₁ f₂ := by
    rw [← hint, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on h12 (hS.intervalIntegrable_of_Icc h12)
      ((hK.intervalIntegrable_of_Icc h12).const_mul _) fun f hf => ?_
    have hgf := hg f hf
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hgf 2) (hK0 f hf)
  refine ⟨h1, ?_⟩
  exact (farmBandVar_bounds h12 hS hS0 ha b Lc V hr).2.trans
    (mul_le_mul_of_nonneg_left h1 (by positivity))

end powerlib.ForcedOscillation.TurbulenceField
