import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.SpectralDensity
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Topology.Semicontinuity.Basic

/-! # Periodogram fitting: existence of best fits, identifiability and the decision

The fitting step (3-41)/(3-42) of the periodogram method: the squared-error loss of the model
spectral density (3-37)/(3-38) to an estimated spectral density on `[0, ω_c]`, lower
semicontinuity of the loss in the parameters and existence of best fits on compact parameter
boxes, identifiability of the two exact classes of Table 3-1 (an exact limit-cycle spectrum is
never an exact forced spectrum, and conversely), and the correctness of the report's decision
"choose the smaller loss, then `V_PS > 1/2`" on exact spectra.

Scope.
* Parameters `(β, λ, α, σ₁, σ₂)` of Table 3-1 as `Periodogram.Params`, or as tuples in `ℝ⁵`
  (`ofTuple`) for topology; the model spectral density is `modelPSD p ω =
  psdX β σ₂ (psdQ λ α σ₁ ω) ω` (the formulas of `theorem/Stochastic/SpectralDensity.lean`, exact
  for the stationary model; for `σ₁ = 0` it is the absolutely continuous part of the spectrum,
  `theorem/Stochastic/SpectralMeasure.lean`).
* The estimate `P̂` is an arbitrary measurable (for the decision theorems: exact model) function;
  how it is estimated from data (periodogram, windowing, bias and variance) is not formalized, and
  no numerical optimizer is: best fits are minimizers given as hypotheses or obtained from
  `exists_isMinOn_modelFit`. The loss is `ℝ≥0∞`-valued (`fitLoss`); it equals the report's real
  integral when that is finite (`fitLoss_eq_ofReal_integral`).
* Parameter boxes are arbitrary nonempty compact subsets of `ℝ⁵` on which `λ ≠ 0`, `β ≠ 0`. The
  decision theorems use the exact classes of Table 3-1 (`σ₂ = 0` for the limit cycle, `σ₁ = 0`
  for the forced oscillation); the report's open constraints `σ₂ < ε`, `β > M`, `σ₁ < ε` and the
  DC constraint are treated separately (`classify_of_fitLoss_eq_zero_limitCycle`,
  `classify_of_fitLoss_eq_zero_dc`). Table 3-1's `β = ∞` for the limit cycle is not a parameter
  value; limit-cycle boxes take finite `β ≠ 0` (the report's own constraint is `β > M`). Generic
  mathematics; no power-system model is selected.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.6.3, eqs. (3-37)–(3-42),
Table 3-1 and the decision rule ("we choose the set of parameters which has less objective
function value … We classify the oscillation to be a forced oscillation if `V_PS > 0.5`").

Corrections and sharpenings.
* The model is not continuous in the parameters at `σ₁ = 0`: at the peak `ω = α` it blows up as
  `σ₁ → 0` while its value at `σ₁ = 0` is `0` (`tendsto_psdQ_atPeak`; the spectral line of the
  forced model). Best fits nevertheless exist on every compact box because the loss is lower
  semicontinuous (Fatou's lemma, `lowerSemicontinuousOn_fitLoss`): the model is continuous in
  the parameters except at the two frequencies `ω = ±α` (`continuousAt_modelPSD`).
* Identifiability needs no condition on the peak: the model spectral densities are real-analytic,
  so agreement on any band `(0, ω_c)` extends to `ℝ` (`modelPSD_eq_of_eqOn`), and the tail
  `ω² PS[x](ω) → σ₂²` (`tendsto_sq_mul_modelPSD`) separates `σ₂ = 0` from `σ₂ ≠ 0`.
* On exact spectra the rule is correct, and the losses are strictly ordered (`0` for the true
  class, positive for the other), so the decision is not a tie-break (`diagnose_exact_limitCycle`,
  `diagnose_exact_forced`). With the relaxed constraint `σ₂ < ε` an exact fit of limit-cycle data
  still has `σ₂ = 0`; with the DC constraint of (3-42) (read as `σ₂²/β² = P̂(0)`,
  `Periodogram.psdX_zero_forced`) an exact fit has `V_PS = 1`.

Results.
* `fitLoss`, `fitLoss_eq_ofReal_integral`, `fitLoss_self`, `fitLoss_lt_top`,
  `eqOn_of_fitLoss_eq_zero`, `fitLoss_pos_of_exists_ne` — the loss, finite for continuous
  functions, zero exactly for an exact fit on the band.
* `lowerSemicontinuousOn_fitLoss`, `exists_isMinOn_fitLoss` — lower semicontinuity and existence
  of minimizers for any model continuous in the parameters for almost every frequency.
* `modelPSD`, `ofTuple`, `measurable_modelPSD`, `modelPSD_forced`, `vps_eq_div_modelPSD`,
  `continuousAt_modelPSD`, `exists_isMinOn_modelFit` — best fits of the report's model exist on
  every compact box with `λ, β ≠ 0`; `tendsto_psdQ_atPeak` — the discontinuity at `σ₁ = 0`.
* `analyticAt_modelPSD`, `continuous_modelPSD`, `tendsto_psdQ_atTop`, `tendsto_sq_mul_modelPSD`,
  `modelPSD_eq_of_eqOn`, `exists_ne_modelPSD_limitCycle_forced`,
  `exists_ne_modelPSD_forced_limitCycle` — identifiability of the two exact classes.
* `diagnose_exact_limitCycle`, `diagnose_exact_forced` — the decision on exact spectra.
* `classify_of_fitLoss_eq_zero_limitCycle`, `classify_of_fitLoss_eq_zero_dc` — the relaxed
  constraints of (3-41)/(3-42).
-/

noncomputable section
namespace powerlib.Stochastic.PeriodogramFit

open MeasureTheory Set Filter
open scoped Topology ENNReal

open Periodogram (psdQ psdX F Params diagnose classify)

/-! ## The fitting loss -/

/-- The squared-error fitting loss of (3-41)/(3-42), `∫_0^{ω_c} (P̂(ω) − M(ω))² dω`, of a model
spectral density `M` to an estimated spectral density `P̂`, as an extended nonnegative number
(`+∞` when the integral diverges). -/
def fitLoss (Phat M : ℝ → ℝ) (ωc : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω in Icc 0 ωc, ENNReal.ofReal ((Phat ω - M ω) ^ 2)

/-- When the squared error is integrable the loss is the report's real integral. -/
@[tmio T, powerlib_foundation] theorem fitLoss_eq_ofReal_integral {Phat M : ℝ → ℝ} {ωc : ℝ}
    (h : IntegrableOn (fun ω => (Phat ω - M ω) ^ 2) (Icc 0 ωc)) :
    fitLoss Phat M ωc = ENNReal.ofReal (∫ ω in Icc 0 ωc, (Phat ω - M ω) ^ 2) :=
  (ofReal_integral_eq_lintegral_ofReal h (ae_of_all _ fun _ => sq_nonneg _)).symm

@[tmio T, powerlib_foundation] theorem fitLoss_self (M : ℝ → ℝ) (ωc : ℝ) : fitLoss M M ωc = 0 := by
  simp [fitLoss]

/-- A loss of two functions continuous on `[0, ω_c]` is finite. -/
@[tmio T, powerlib_foundation] theorem fitLoss_lt_top {Phat M : ℝ → ℝ} {ωc : ℝ}
    (hP : ContinuousOn Phat (Icc 0 ωc)) (hM : ContinuousOn M (Icc 0 ωc)) : fitLoss Phat M ωc < ∞ :=
  (((hP.sub hM).pow 2).integrableOn_compact isCompact_Icc).lintegral_lt_top

/-- **Zero loss means an exact fit.** If `P̂` and `M` are continuous on `(0, ω_c)` and the loss
vanishes, they agree on `(0, ω_c)`. -/
@[tmio T, powerlib_foundation] theorem eqOn_of_fitLoss_eq_zero {Phat M : ℝ → ℝ} {ωc : ℝ}
    (hPm : AEMeasurable Phat (volume.restrict (Icc 0 ωc)))
    (hMm : AEMeasurable M (volume.restrict (Icc 0 ωc)))
    (hP : ContinuousOn Phat (Ioo 0 ωc)) (hM : ContinuousOn M (Ioo 0 ωc))
    (h : fitLoss Phat M ωc = 0) : EqOn Phat M (Ioo 0 ωc) := by
  rw [fitLoss, lintegral_eq_zero_iff' (by fun_prop)] at h
  have h' : Phat =ᵐ[volume.restrict (Ioo 0 ωc)] M := by
    have := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self h
    filter_upwards [this] with ω hω
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hω
    nlinarith [sq_nonneg (Phat ω - M ω)]
  exact Measure.eqOn_open_of_ae_eq h' isOpen_Ioo hP hM

/-! ## Lower semicontinuity and existence of minimizers -/

/-- **The loss is lower semicontinuous in the parameters** (Fatou's lemma) as soon as the model
value `M θ ω` is continuous in `θ` within `K` at every point of `K`, for almost every frequency
of the band. Continuity of the loss is not needed and fails for the report's model at `σ₁ = 0`
(`tendsto_psdQ_atPeak`). -/
@[tmio T, powerlib_foundation] theorem lowerSemicontinuousOn_fitLoss {Θ : Type*} [TopologicalSpace Θ]
    [FirstCountableTopology Θ] {K : Set Θ} {Phat : ℝ → ℝ} {M : Θ → ℝ → ℝ} {ωc : ℝ}
    (hP : AEMeasurable Phat (volume.restrict (Icc 0 ωc)))
    (hmeas : ∀ θ, AEMeasurable (M θ) (volume.restrict (Icc 0 ωc)))
    (hcont : ∀ θ ∈ K, ∀ᵐ ω ∂(volume.restrict (Icc 0 ωc)),
      ContinuousWithinAt (fun θ' => M θ' ω) K θ) :
    LowerSemicontinuousOn (fun θ => fitLoss Phat (M θ) ωc) K := by
  intro θ₀ hθ₀
  change LowerSemicontinuousWithinAt _ K θ₀
  rw [lowerSemicontinuousWithinAt_iff_le_liminf]
  have : (𝓝[K] θ₀).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (subset_closure hθ₀)
  have hlim : ∀ᵐ ω ∂(volume.restrict (Icc 0 ωc)), ENNReal.ofReal ((Phat ω - M θ₀ ω) ^ 2) =
      liminf (fun θ => ENNReal.ofReal ((Phat ω - M θ ω) ^ 2)) (𝓝[K] θ₀) := by
    filter_upwards [hcont θ₀ hθ₀] with ω hω
    have ht : Tendsto (fun θ => ENNReal.ofReal ((Phat ω - M θ ω) ^ 2)) (𝓝[K] θ₀)
        (𝓝 (ENNReal.ofReal ((Phat ω - M θ₀ ω) ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp
        (((continuous_const.sub continuous_id).pow 2).continuousAt.tendsto.comp hω.tendsto)
    exact ht.liminf_eq.symm
  calc fitLoss Phat (M θ₀) ωc
      = ∫⁻ ω in Icc 0 ωc, liminf (fun θ => ENNReal.ofReal ((Phat ω - M θ ω) ^ 2)) (𝓝[K] θ₀) :=
        lintegral_congr_ae hlim
    _ ≤ liminf (fun θ => fitLoss Phat (M θ) ωc) (𝓝[K] θ₀) :=
        lintegral_liminf_le' fun θ => by
          have := hmeas θ
          fun_prop

/-- **Existence of a best fit.** On a nonempty compact parameter set on which the model is
continuous in the parameters for almost every frequency, the loss attains its minimum. -/
@[tmio T, powerlib_foundation] theorem exists_isMinOn_fitLoss {Θ : Type*} [TopologicalSpace Θ]
    [FirstCountableTopology Θ] {K : Set Θ} (hK : IsCompact K) (hne : K.Nonempty)
    {Phat : ℝ → ℝ} {M : Θ → ℝ → ℝ} {ωc : ℝ}
    (hP : AEMeasurable Phat (volume.restrict (Icc 0 ωc)))
    (hmeas : ∀ θ, AEMeasurable (M θ) (volume.restrict (Icc 0 ωc)))
    (hcont : ∀ θ ∈ K, ∀ᵐ ω ∂(volume.restrict (Icc 0 ωc)),
      ContinuousWithinAt (fun θ' => M θ' ω) K θ) :
    ∃ θ ∈ K, IsMinOn (fun θ => fitLoss Phat (M θ) ωc) K θ :=
  (lowerSemicontinuousOn_fitLoss hP hmeas hcont).exists_isMinOn hne hK

/-! ## The model of TR-110 (3-37)/(3-38) -/

/-- The model spectral density of a parameter set `(β, λ, α, σ₁, σ₂)`:
`PS[x](ω) = psdX β σ₂ (psdQ λ α σ₁ ω) ω` ((3-37) with (3-38) inserted). -/
def modelPSD (p : Params) (ω : ℝ) : ℝ := psdX p.β p.σ₂ (psdQ p.l p.α p.σ₁ ω) ω

/-- The parameter tuple `(β, λ, α, σ₁, σ₂) ∈ ℝ⁵` as a parameter set. -/
def ofTuple (θ : ℝ × ℝ × ℝ × ℝ × ℝ) : Params := ⟨θ.1, θ.2.1, θ.2.2.1, θ.2.2.2.1, θ.2.2.2.2⟩

@[tmio T, powerlib_foundation] theorem measurable_modelPSD (p : Params) : Measurable (modelPSD p) := by
  unfold modelPSD psdX psdQ F
  fun_prop

/-- Forced class (`σ₁ = 0`): `PS[x](ω) = σ₂²/(β² + ω²)`. -/
@[tmio T, powerlib_foundation] theorem modelPSD_forced {p : Params} (h : p.σ₁ = 0) (ω : ℝ) :
    modelPSD p ω = p.σ₂ ^ 2 / (p.β ^ 2 + ω ^ 2) := by
  simp [modelPSD, psdX, h, Periodogram.psdQ_forced]

/-- `V_PS` of a parameter set is the white-noise DC power over the model DC density. -/
@[tmio T, powerlib_foundation] theorem vps_eq_div_modelPSD (p : Params) :
    p.vps = (p.σ₂ ^ 2 / p.β ^ 2) / modelPSD p 0 := rfl

/-- `F(s, α, ω)` is continuous in `(s, α)` wherever its denominator does not vanish. -/
@[tmio T, powerlib_foundation] private theorem continuousAt_F {s₀ α₀ ω : ℝ}
    (h : (4 * (α₀ - ω) ^ 2 + s₀ ^ 2) * (4 * (α₀ + ω) ^ 2 + s₀ ^ 2) ≠ 0) :
    ContinuousAt (fun q : ℝ × ℝ => F q.1 q.2 ω) (s₀, α₀) := by
  unfold F
  exact ContinuousAt.div (by fun_prop) (by fun_prop) h

/-- **The model is continuous in the parameters off two frequencies.** At a parameter tuple
with `λ ≠ 0`, `β ≠ 0`, the model value at `ω` is continuous in the parameters unless `σ₁ = 0`
and `ω = ±α` (where the line of the forced model appears in the limit). -/
@[tmio T, powerlib_foundation] theorem continuousAt_modelPSD {θ₀ : ℝ × ℝ × ℝ × ℝ × ℝ} {ω : ℝ}
    (hl : θ₀.2.1 ≠ 0) (hβ : θ₀.1 ≠ 0)
    (hω : θ₀.2.2.2.1 ≠ 0 ∨ (ω ≠ θ₀.2.2.1 ∧ ω ≠ -θ₀.2.2.1)) :
    ContinuousAt (fun θ => modelPSD (ofTuple θ) ω) θ₀ := by
  have hl2 : θ₀.2.1 ^ 2 ≠ 0 := pow_ne_zero 2 hl
  have hs : ContinuousAt (fun θ : ℝ × ℝ × ℝ × ℝ × ℝ => θ.2.2.2.1 ^ 2 / θ.2.1 ^ 2) θ₀ :=
    ContinuousAt.div (by fun_prop) (by fun_prop) hl2
  have hF1 : ContinuousAt (fun θ : ℝ × ℝ × ℝ × ℝ × ℝ =>
      F (θ.2.2.2.1 ^ 2 / θ.2.1 ^ 2) θ.2.2.1 ω) θ₀ := by
    refine (continuousAt_F ?_).comp (f := fun θ : ℝ × ℝ × ℝ × ℝ × ℝ =>
      (θ.2.2.2.1 ^ 2 / θ.2.1 ^ 2, θ.2.2.1)) (hs.prodMk (by fun_prop))
    rcases hω with h | ⟨h1, h2⟩
    · have : 0 < θ₀.2.2.2.1 ^ 2 / θ₀.2.1 ^ 2 := by positivity
      positivity
    · have : (θ₀.2.2.1 - ω) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
      have : (θ₀.2.2.1 + ω) ≠ 0 := by intro h; apply h2; linarith
      positivity
  have hF2 : ContinuousAt (fun θ : ℝ × ℝ × ℝ × ℝ × ℝ =>
      F (θ.2.2.2.1 ^ 2 / θ.2.1 ^ 2 + 4 * θ.2.1 ^ 2) θ.2.2.1 ω) θ₀ := by
    refine (continuousAt_F ?_).comp (f := fun θ : ℝ × ℝ × ℝ × ℝ × ℝ =>
      (θ.2.2.2.1 ^ 2 / θ.2.1 ^ 2 + 4 * θ.2.1 ^ 2, θ.2.2.1)) ((hs.add (by fun_prop)).prodMk (by fun_prop))
    have : 0 < θ₀.2.2.2.1 ^ 2 / θ₀.2.1 ^ 2 + 4 * θ₀.2.1 ^ 2 := by positivity
    positivity
  have hQ : ContinuousAt (fun θ : ℝ × ℝ × ℝ × ℝ × ℝ => psdQ θ.2.1 θ.2.2.1 θ.2.2.2.1 ω) θ₀ := by
    unfold psdQ
    exact ((continuous_fst.comp continuous_snd).pow 2).continuousAt.mul hF1 |>.add
      ((ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)).mul hF2)
  have hb : θ₀.1 ^ 2 + ω ^ 2 ≠ 0 := by positivity
  have e : (fun θ => modelPSD (ofTuple θ) ω) = fun θ : ℝ × ℝ × ℝ × ℝ × ℝ =>
      θ.1 ^ 2 / (θ.1 ^ 2 + ω ^ 2) * psdQ θ.2.1 θ.2.2.1 θ.2.2.2.1 ω +
        θ.2.2.2.2 ^ 2 / (θ.1 ^ 2 + ω ^ 2) := rfl
  rw [e]
  have hd : ContinuousAt (fun θ : ℝ × ℝ × ℝ × ℝ × ℝ => θ.1 ^ 2 + ω ^ 2) θ₀ := by fun_prop
  exact ((ContinuousAt.div (by fun_prop) hd hb).mul hQ).add (ContinuousAt.div (by fun_prop) hd hb)

/-- **Best fits of the report's model exist** on every nonempty compact parameter set of
`(β, λ, α, σ₁, σ₂)` with `λ ≠ 0`, `β ≠ 0`, for every measurable estimate `P̂` and band
`[0, ω_c]`: the boxes of (3-41) and (3-42) (closed, bounded, `β` bounded away from `0`), with or
without the DC constraint, and boxes containing `σ₁ = 0`, where the loss is only lower
semicontinuous. -/
@[tmio T, powerlib_foundation] theorem exists_isMinOn_modelFit {K : Set (ℝ × ℝ × ℝ × ℝ × ℝ)}
    (hK : IsCompact K) (hne : K.Nonempty) (hKp : ∀ θ ∈ K, θ.2.1 ≠ 0 ∧ θ.1 ≠ 0)
    {Phat : ℝ → ℝ} (hP : Measurable Phat) (ωc : ℝ) :
    ∃ θ ∈ K, IsMinOn (fun θ => fitLoss Phat (modelPSD (ofTuple θ)) ωc) K θ := by
  refine exists_isMinOn_fitLoss hK hne hP.aemeasurable
    (fun θ => (measurable_modelPSD _).aemeasurable) fun θ hθ => ?_
  refine ae_restrict_of_ae ?_
  filter_upwards [Measure.ae_ne volume θ.2.2.1, Measure.ae_ne volume (-θ.2.2.1)] with ω h1 h2
  exact (continuousAt_modelPSD (hKp θ hθ).1 (hKp θ hθ).2 (Or.inr ⟨h1, h2⟩)).continuousWithinAt

/-- **At `σ₁ = 0` the model is discontinuous in the parameters.** For `λ ≠ 0` the model `S_Q`
at the peak frequency `ω = α` blows up as `σ₁ → 0` (`S_Q(α) ≥ λ⁴/σ₁²`), while its value at
`σ₁ = 0` is `0` (`Periodogram.psdQ_forced`): the Lorentzian concentrates into the line of the
forced model. -/
@[tmio T, powerlib_foundation] theorem tendsto_psdQ_atPeak {l : ℝ} (hl : l ≠ 0) (α : ℝ) :
    Tendsto (fun σ₁ => psdQ l α σ₁ α) (𝓝[≠] 0) atTop := by
  have hbound : ∀ σ₁ : ℝ, σ₁ ≠ 0 → l ^ 4 / σ₁ ^ 2 ≤ psdQ l α σ₁ α := by
    intro σ₁ hσ
    set s := σ₁ ^ 2 / l ^ 2 with hsdef
    have hs : 0 < s := by positivity
    have hF : 1 / s ≤ F s α α := by
      unfold F
      rw [div_le_div_iff₀ hs (by positivity)]
      nlinarith [sq_nonneg s, sq_nonneg α, sq_nonneg (α - α), mul_pos hs hs]
    have h2 : 0 ≤ σ₁ ^ 2 / (4 * l ^ 2) * F (σ₁ ^ 2 / l ^ 2 + 4 * l ^ 2) α α :=
      mul_nonneg (by positivity) (Periodogram.F_nonneg (by positivity) α α)
    have h1 : l ^ 4 / σ₁ ^ 2 = l ^ 2 * (1 / s) := by
      rw [hsdef]; field_simp
    unfold psdQ
    rw [h1]
    nlinarith [mul_le_mul_of_nonneg_left hF (sq_nonneg l)]
  have hinf : Tendsto (fun σ₁ : ℝ => l ^ 4 / σ₁ ^ 2) (𝓝[≠] 0) atTop := by
    have h0 : Tendsto (fun σ₁ : ℝ => σ₁ ^ 2) (𝓝[≠] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Tendsto (fun σ₁ : ℝ => σ₁ ^ 2) (𝓝 0) (𝓝 0) := by
          simpa using (continuous_pow 2).tendsto (0 : ℝ)
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with σ₁ hσ
        have : σ₁ ≠ 0 := hσ
        show 0 < σ₁ ^ 2
        positivity
    have := (tendsto_inv_nhdsGT_zero.comp h0).const_mul_atTop (by positivity : 0 < l ^ 4)
    simpa [div_eq_mul_inv] using this
  refine tendsto_atTop_mono' _ ?_ hinf
  filter_upwards [self_mem_nhdsWithin] with σ₁ hσ
  exact hbound σ₁ hσ

/-! ## Identifiability of the two exact classes -/

/-- `S_Q ≡ 0` in the degenerate cases `λ = 0` or `σ₁ = 0`. -/
@[tmio T, powerlib_foundation] private theorem psdQ_degenerate {l α σ₁ : ℝ} (h : l = 0 ∨ σ₁ = 0)
    (ω : ℝ) : psdQ l α σ₁ ω = 0 := by
  rcases h with h | h <;> simp [psdQ, h, Periodogram.F_zero_left]

/-- **The model spectral density is real-analytic in `ω`** for `β ≠ 0` (a rational function
without real poles). -/
@[tmio T, powerlib_foundation] theorem analyticAt_modelPSD {p : Params} (hβ : p.β ≠ 0) (x : ℝ) :
    AnalyticAt ℝ (modelPSD p) x := by
  by_cases hd : p.l = 0 ∨ p.σ₁ = 0
  · have e : modelPSD p = fun ω => p.σ₂ ^ 2 / (p.β ^ 2 + ω ^ 2) := by
      funext ω; simp [modelPSD, psdX, psdQ_degenerate hd]
    rw [e]
    fun_prop (disch := positivity)
  · rw [not_or] at hd
    obtain ⟨hl, hσ⟩ := hd
    have hs : 0 < p.σ₁ ^ 2 / p.l ^ 2 := by positivity
    unfold modelPSD psdX psdQ F
    fun_prop (disch := positivity)

@[tmio T, powerlib_foundation] theorem continuous_modelPSD {p : Params} (hβ : p.β ≠ 0) :
    Continuous (modelPSD p) :=
  continuous_iff_continuousAt.mpr fun x => (analyticAt_modelPSD hβ x).continuousAt

/-- `F(s, α, ω) → 0` as `ω → ∞` for `s > 0`. -/
@[tmio T, powerlib_foundation] private theorem tendsto_F_atTop {s : ℝ} (hs : 0 < s) (α : ℝ) :
    Tendsto (fun ω => F s α ω) atTop (𝓝 0) := by
  have hL : ∀ a : ℝ, Tendsto (fun ω : ℝ => (s / 2) / ((s / 2) ^ 2 + (ω - a) ^ 2)) atTop (𝓝 0) := by
    intro a
    refine tendsto_const_nhds.div_atTop ?_
    exact tendsto_atTop_add_const_left _ _
      ((tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_right _ (-a) tendsto_id))
  have h := ((hL α).add (hL (-α))).div_const 2
  simp only [add_zero, zero_div] at h
  refine h.congr fun ω => ?_
  rw [Periodogram.F_eq_lorentzPair hs, sub_neg_eq_add]

/-- `S_Q(ω) → 0` as `ω → ∞`. -/
@[tmio T, powerlib_foundation] theorem tendsto_psdQ_atTop (l α σ₁ : ℝ) :
    Tendsto (fun ω => psdQ l α σ₁ ω) atTop (𝓝 0) := by
  by_cases hd : l = 0 ∨ σ₁ = 0
  · simp only [psdQ_degenerate hd]; exact tendsto_const_nhds
  · rw [not_or] at hd
    obtain ⟨hl, hσ⟩ := hd
    have h := ((tendsto_F_atTop (by positivity : 0 < σ₁ ^ 2 / l ^ 2) α).const_mul (l ^ 2)).add
      ((tendsto_F_atTop (by positivity : 0 < σ₁ ^ 2 / l ^ 2 + 4 * l ^ 2) α).const_mul
        (σ₁ ^ 2 / (4 * l ^ 2)))
    simpa [psdQ] using h

/-- **The white-noise intensity is read off the tail**: `ω² PS[x](ω) → σ₂²` as `ω → ∞` (`β ≠ 0`);
the coherent part decays like `ω⁻⁴`. -/
@[tmio T, powerlib_foundation] theorem tendsto_sq_mul_modelPSD {p : Params} (hβ : p.β ≠ 0) :
    Tendsto (fun ω => ω ^ 2 * modelPSD p ω) atTop (𝓝 (p.σ₂ ^ 2)) := by
  have hr : Tendsto (fun ω : ℝ => p.β ^ 2 / (p.β ^ 2 + ω ^ 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero))
  have h1 : Tendsto (fun ω : ℝ => ω ^ 2 / (p.β ^ 2 + ω ^ 2)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub hr
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards with ω
    have : p.β ^ 2 + ω ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  have h := ((h1.const_mul (p.β ^ 2)).mul (tendsto_psdQ_atTop p.l p.α p.σ₁)).add
    (h1.const_mul (p.σ₂ ^ 2))
  simp only [mul_one, mul_zero, zero_add] at h
  refine h.congr fun ω => ?_
  have : p.β ^ 2 + ω ^ 2 ≠ 0 := by positivity
  simp only [modelPSD, psdX]
  field_simp

/-- **Agreement on a band forces agreement everywhere** (identity theorem for real-analytic
functions): two model spectral densities (`β ≠ 0`) that agree on `(0, ω_c)`, `ω_c > 0`, agree on
all of `ℝ`, and then have the same white-noise intensity `σ₂²`. -/
@[tmio T, powerlib_foundation] theorem modelPSD_eq_of_eqOn {p q : Params} (hp : p.β ≠ 0)
    (hq : q.β ≠ 0) {ωc : ℝ} (hωc : 0 < ωc) (h : EqOn (modelPSD p) (modelPSD q) (Ioo 0 ωc)) :
    modelPSD p = modelPSD q ∧ p.σ₂ ^ 2 = q.σ₂ ^ 2 := by
  have hz : ωc / 2 ∈ Ioo 0 ωc := ⟨by linarith, by linarith⟩
  have hfreq : ∃ᶠ z in 𝓝[≠] (ωc / 2), modelPSD p z = modelPSD q z :=
    (eventually_nhdsWithin_of_eventually_nhds
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hz) fun z hz' => h hz')).frequently
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (f := modelPSD p)
    (fun x _ => analyticAt_modelPSD hp x) (fun x _ => analyticAt_modelPSD hq x)
    isPreconnected_univ (mem_univ _) hfreq
  have hfun : modelPSD p = modelPSD q := funext fun x => heq (mem_univ x)
  refine ⟨hfun, tendsto_nhds_unique (tendsto_sq_mul_modelPSD hp) ?_⟩
  rw [hfun]; exact tendsto_sq_mul_modelPSD hq

/-- **An exact limit-cycle spectrum is not a forced spectrum.** A limit-cycle parameter set
(`σ₂ = 0`, `λ ≠ 0`, `σ₁ ≠ 0`, `β ≠ 0`) and any forced parameter set (`σ₁ = 0`, `β ≠ 0`) have
model spectral densities that differ somewhere in every band `(0, ω_c)`: equality would extend to
`ℝ` (`modelPSD_eq_of_eqOn`), force `σ₂ = 0` in the forced set by the tail, and then contradict
`S_Q(0) > 0`. No condition on the peak frequency or width is needed. -/
@[tmio T, powerlib_foundation] theorem exists_ne_modelPSD_limitCycle_forced {p q : Params}
    (hp2 : p.σ₂ = 0) (hpl : p.l ≠ 0) (hp1 : p.σ₁ ≠ 0) (hpβ : p.β ≠ 0) (hq1 : q.σ₁ = 0)
    (hqβ : q.β ≠ 0) {ωc : ℝ} (hωc : 0 < ωc) : ∃ ω ∈ Ioo 0 ωc, modelPSD p ω ≠ modelPSD q ω := by
  by_contra! h
  obtain ⟨hfun, hσ⟩ := modelPSD_eq_of_eqOn hpβ hqβ hωc h
  rw [hp2] at hσ
  have hq2 : q.σ₂ = 0 := by
    have : q.σ₂ ^ 2 = 0 := by rw [← hσ]; ring
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  have h0 := congrFun hfun 0
  rw [modelPSD_forced hq1, hq2] at h0
  have hpos : 0 < modelPSD p 0 := by
    rw [modelPSD, Periodogram.psdX_zero hpβ, hp2]
    have := Periodogram.psdQ_zero_pos hpl hp1 p.α
    simpa using this
  simp at h0
  linarith

/-- **An exact forced spectrum is not a limit-cycle spectrum.** A parameter set with white noise
(`σ₂ ≠ 0`, `β ≠ 0`; in particular every nondegenerate forced set) and any limit-cycle-class
parameter set (`σ₂ = 0`, `β ≠ 0`) have model spectral densities that differ somewhere in every
band `(0, ω_c)` (the tails `ω²PS → σ₂²` differ). -/
@[tmio T, powerlib_foundation] theorem exists_ne_modelPSD_forced_limitCycle {p q : Params}
    (hq2 : q.σ₂ ≠ 0) (hqβ : q.β ≠ 0) (hp2 : p.σ₂ = 0) (hpβ : p.β ≠ 0) {ωc : ℝ}
    (hωc : 0 < ωc) : ∃ ω ∈ Ioo 0 ωc, modelPSD q ω ≠ modelPSD p ω := by
  by_contra! h
  obtain ⟨-, hσ⟩ := modelPSD_eq_of_eqOn hqβ hpβ hωc h
  rw [hp2] at hσ
  exact hq2 (pow_eq_zero_iff two_ne_zero |>.mp (by rw [hσ]; ring))

/-- A positive loss: if `P̂` and `M` are continuous and differ somewhere in `(0, ω_c)`, the loss is
positive. -/
@[tmio T, powerlib_foundation] theorem fitLoss_pos_of_exists_ne {Phat M : ℝ → ℝ} {ωc : ℝ}
    (hP : Continuous Phat) (hM : Continuous M) (h : ∃ ω ∈ Ioo 0 ωc, Phat ω ≠ M ω) :
    0 < fitLoss Phat M ωc := by
  rcases h with ⟨ω, hω, hne⟩
  refine pos_iff_ne_zero.mpr fun h0 => hne ?_
  exact eqOn_of_fitLoss_eq_zero hP.aemeasurable hM.aemeasurable hP.continuousOn hM.continuousOn h0 hω

/-! ## Correctness of the decision on exact spectra -/

/-- **Exact limit-cycle data are classified as a limit cycle.** Let the estimated spectrum be the
exact model spectrum of a limit-cycle parameter tuple `θ₀` (`σ₂ = 0`, `λ, σ₁, β ≠ 0`) lying in the
limit-cycle box `K_LC ⊆ {σ₂ = 0}`, let the forced box satisfy `K_FO ⊆ {σ₁ = 0, β ≠ 0}`, and let
`θ_LC`, `θ_FO` be best fits on the two boxes (they exist by `exists_isMinOn_modelFit`). Then the
limit-cycle loss is `0`, the forced loss is positive, and the report's rule answers
`limitCycle`. -/
@[tmio T, powerlib_foundation] theorem diagnose_exact_limitCycle {KLC KFO : Set (ℝ × ℝ × ℝ × ℝ × ℝ)}
    (hLC : ∀ θ ∈ KLC, θ.2.2.2.2 = 0) (hFO : ∀ θ ∈ KFO, θ.2.2.2.1 = 0 ∧ θ.1 ≠ 0)
    {θ₀ θLC θFO : ℝ × ℝ × ℝ × ℝ × ℝ} (h₀ : θ₀ ∈ KLC) (hl : θ₀.2.1 ≠ 0) (hσ : θ₀.2.2.2.1 ≠ 0)
    (hβ : θ₀.1 ≠ 0) (hθLC : θLC ∈ KLC) {ωc : ℝ} (hωc : 0 < ωc)
    (hminLC : IsMinOn (fun θ => fitLoss (modelPSD (ofTuple θ₀)) (modelPSD (ofTuple θ)) ωc) KLC θLC)
    (hθFO : θFO ∈ KFO) :
    fitLoss (modelPSD (ofTuple θ₀)) (modelPSD (ofTuple θLC)) ωc = 0 ∧
      0 < fitLoss (modelPSD (ofTuple θ₀)) (modelPSD (ofTuple θFO)) ωc ∧
      diagnose (fitLoss (modelPSD (ofTuple θ₀)) (modelPSD (ofTuple θLC)) ωc).toReal
        (fitLoss (modelPSD (ofTuple θ₀)) (modelPSD (ofTuple θFO)) ωc).toReal
        (ofTuple θLC) (ofTuple θFO) = .limitCycle := by
  have h0 : fitLoss (modelPSD (ofTuple θ₀)) (modelPSD (ofTuple θLC)) ωc = 0 :=
    le_antisymm ((hminLC h₀).trans_eq (fitLoss_self _ _)) (by positivity)
  refine ⟨h0, ?_, ?_⟩
  · exact fitLoss_pos_of_exists_ne (continuous_modelPSD hβ) (continuous_modelPSD (hFO θFO hθFO).2)
      (exists_ne_modelPSD_limitCycle_forced (hLC θ₀ h₀) hl hσ hβ (hFO θFO hθFO).1
        (hFO θFO hθFO).2 hωc)
  · rw [h0, ENNReal.toReal_zero]
    exact Periodogram.diagnose_limitCycle ENNReal.toReal_nonneg (hLC θLC hθLC)

/-- **Exact forced data are classified as forced.** Let the estimated spectrum be the exact model
spectrum of a forced parameter tuple `θ₀` (`σ₁ = 0`, `σ₂ ≠ 0`, `β ≠ 0`) lying in the forced box
`K_FO ⊆ {σ₁ = 0, β ≠ 0}`, let `K_LC ⊆ {σ₂ = 0, β ≠ 0}`, and let `θ_LC`, `θ_FO` be best fits. Then
the forced loss is `0`, the limit-cycle loss is positive and finite, and the rule answers
`forced`. -/
@[tmio T, powerlib_foundation] theorem diagnose_exact_forced {KLC KFO : Set (ℝ × ℝ × ℝ × ℝ × ℝ)}
    (hLC : ∀ θ ∈ KLC, θ.2.2.2.2 = 0 ∧ θ.1 ≠ 0) (hFO : ∀ θ ∈ KFO, θ.2.2.2.1 = 0 ∧ θ.1 ≠ 0)
    {θ₀ θLC θFO : ℝ × ℝ × ℝ × ℝ × ℝ} (h₀ : θ₀ ∈ KFO) (hσ₂ : θ₀.2.2.2.2 ≠ 0) (hθLC : θLC ∈ KLC)
    (hθFO : θFO ∈ KFO) {ωc : ℝ} (hωc : 0 < ωc)
    (hminFO : IsMinOn (fun θ => fitLoss (modelPSD (ofTuple θ₀)) (modelPSD (ofTuple θ)) ωc) KFO θFO) :
    fitLoss (modelPSD (ofTuple θ₀)) (modelPSD (ofTuple θFO)) ωc = 0 ∧
      0 < fitLoss (modelPSD (ofTuple θ₀)) (modelPSD (ofTuple θLC)) ωc ∧
      diagnose (fitLoss (modelPSD (ofTuple θ₀)) (modelPSD (ofTuple θLC)) ωc).toReal
        (fitLoss (modelPSD (ofTuple θ₀)) (modelPSD (ofTuple θFO)) ωc).toReal
        (ofTuple θLC) (ofTuple θFO) = .forced := by
  have hβ₀ := (hFO θ₀ h₀).2
  have hβF := (hFO θFO hθFO).2
  have hβL := (hLC θLC hθLC).2
  have h0 : fitLoss (modelPSD (ofTuple θ₀)) (modelPSD (ofTuple θFO)) ωc = 0 :=
    le_antisymm ((hminFO h₀).trans_eq (fitLoss_self _ _)) (by positivity)
  have hpos : 0 < fitLoss (modelPSD (ofTuple θ₀)) (modelPSD (ofTuple θLC)) ωc :=
    fitLoss_pos_of_exists_ne (continuous_modelPSD hβ₀) (continuous_modelPSD hβL)
      (exists_ne_modelPSD_forced_limitCycle hσ₂ hβ₀ (hLC θLC hθLC).1 hβL hωc)
  have hfin : fitLoss (modelPSD (ofTuple θ₀)) (modelPSD (ofTuple θLC)) ωc < ∞ :=
    fitLoss_lt_top (continuous_modelPSD hβ₀).continuousOn (continuous_modelPSD hβL).continuousOn
  refine ⟨h0, hpos, ?_⟩
  have hlt : (fitLoss (modelPSD (ofTuple θ₀)) (modelPSD (ofTuple θFO)) ωc).toReal <
      (fitLoss (modelPSD (ofTuple θ₀)) (modelPSD (ofTuple θLC)) ωc).toReal := by
    rw [h0, ENNReal.toReal_zero]
    exact ENNReal.toReal_pos hpos.ne' hfin.ne
  -- the best forced fit is exact, so it carries the same white-noise intensity
  have heq := eqOn_of_fitLoss_eq_zero (measurable_modelPSD _).aemeasurable
    (measurable_modelPSD _).aemeasurable (continuous_modelPSD hβ₀).continuousOn
    (continuous_modelPSD hβF).continuousOn h0
  have hσF : θFO.2.2.2.2 ≠ 0 := by
    obtain ⟨-, hs⟩ := modelPSD_eq_of_eqOn hβ₀ hβF hωc heq
    intro h
    apply hσ₂
    have : θ₀.2.2.2.2 ^ 2 = 0 := by
      have := hs; simp only [ofTuple] at this; rw [this, h]; ring
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  exact Periodogram.diagnose_forced hlt (hFO θFO hθFO).1 hσF hβF

/-! ## The relaxed constraints of (3-41)/(3-42) -/

/-- **(3-41) with `σ₂ < ε`: an exact fit of limit-cycle data has `σ₂ = 0`.** If a parameter set
(`β ≠ 0`) fits the exact spectrum of a limit-cycle-class set (`σ₂ = 0`, `β ≠ 0`) with zero loss on
`[0, ω_c]`, then its own `σ₂` is `0` (the tails agree), so `V_PS = 0` and the rule answers
`limitCycle`, whatever the bound `ε`. -/
@[tmio T, powerlib_foundation] theorem classify_of_fitLoss_eq_zero_limitCycle {p₀ p : Params}
    (h₀ : p₀.σ₂ = 0) (hβ₀ : p₀.β ≠ 0) (hβ : p.β ≠ 0) {ωc : ℝ} (hωc : 0 < ωc)
    (h : fitLoss (modelPSD p₀) (modelPSD p) ωc = 0) :
    p.σ₂ = 0 ∧ classify p.vps = .limitCycle := by
  have heq := eqOn_of_fitLoss_eq_zero (measurable_modelPSD _).aemeasurable
    (measurable_modelPSD _).aemeasurable (continuous_modelPSD hβ₀).continuousOn
    (continuous_modelPSD hβ).continuousOn h
  obtain ⟨-, hs⟩ := modelPSD_eq_of_eqOn hβ₀ hβ hωc heq
  rw [h₀] at hs
  have h2 : p.σ₂ = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by rw [← hs]; ring)
  exact ⟨h2, Periodogram.classify_limitCycle h2⟩

/-- **(3-42) with the DC constraint: an exact fit has `V_PS = 1`.** If a parameter set (`β ≠ 0`)
satisfies the DC constraint `σ₂²/β² = P̂(0)` and fits a continuous estimate `P̂` with
`P̂(0) ≠ 0` with zero loss on `[0, ω_c]`, then `V_PS = 1` and the rule answers `forced`, whatever
the bound on `σ₁`: the fit forces `S_Q(0) = 0`. -/
@[tmio T, powerlib_foundation] theorem classify_of_fitLoss_eq_zero_dc {Phat : ℝ → ℝ}
    (hP : Continuous Phat) (hP0 : Phat 0 ≠ 0) {p : Params} (hβ : p.β ≠ 0)
    (hdc : p.σ₂ ^ 2 / p.β ^ 2 = Phat 0) {ωc : ℝ} (hωc : 0 < ωc)
    (h : fitLoss Phat (modelPSD p) ωc = 0) : p.vps = 1 ∧ classify p.vps = .forced := by
  have heq := eqOn_of_fitLoss_eq_zero hP.aemeasurable (measurable_modelPSD _).aemeasurable
    hP.continuousOn (continuous_modelPSD hβ).continuousOn h
  have hIcc := heq.of_subset_closure hP.continuousOn (continuous_modelPSD hβ).continuousOn
    Ioo_subset_Icc_self (by rw [closure_Ioo hωc.ne]) (x := 0) ⟨le_rfl, hωc.le⟩
  have hv : p.vps = 1 := by
    rw [vps_eq_div_modelPSD, ← hIcc, hdc, div_self hP0]
  refine ⟨hv, ?_⟩
  rw [hv, Periodogram.classify]
  norm_num

end powerlib.Stochastic.PeriodogramFit
