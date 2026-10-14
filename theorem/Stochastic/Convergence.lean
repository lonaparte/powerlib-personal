import dependencies.Mathlib
import theorem.Attributes
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.PSeries

/-! # Modes of stochastic convergence: implications (Mathlib) and separating counterexamples

The implication chain between almost-sure, `L^p`, in-probability and in-distribution
convergence, and counterexamples separating the modes.

Scope.
* Probability theory, not an engineering result; each counterexample is on a concrete
  probability space.
* The distribution-function characterization of convergence in distribution (both directions)
  is `ConvergenceCDF.lean`.

Source: work-sync theory/T-convergence-stochastic.md §1.1–§1.4 (a.s., `L^p`, in probability, in
distribution), §1.5 (implication chain, Markov's inequality), §1.6 (three counterexamples),
§1.7 (in probability + uniform integrability ⇒ `L^p`; subsequence criterion).

Results.
* Mathlib wrappers (Mathlib declaration in brackets): `ae_imp_inProbability`
  [`tendstoInMeasure_of_tendsto_ae`], `Lp_imp_inProbability`
  [`tendstoInMeasure_of_tendsto_eLpNorm`], `inProbability_imp_inDistribution`
  [`TendstoInMeasure.tendstoInDistribution`], `inProbability_subseq_ae`
  [`TendstoInMeasure.exists_seq_tendsto_ae`], `inProbability_UI_imp_Lp`
  [`tendsto_Lp_finite_of_tendstoInMeasure`], `markov_inequality` [`mul_meas_ge_le_lintegral₀`].
* `ae_not_L1` — on `[0,1]`, `X_n = (n+1) 1_{[0, 1/(n+1))}` tends to `0` a.e. but `E|X_n| = 1`.
* `inProbability_not_ae` — on `[0,1]^ℕ` (product of uniform laws), the indicators of the
  independent events `A_n = {ω_n ≤ 1/(n+1)}` tend to `0` in probability but not a.s. (second
  Borel–Cantelli, Mathlib `measure_limsup_eq_one`).
* `inDistribution_not_inProbability` — for `X ~ N(0,1)`, the constant sequence `X` converges in
  distribution to `−X` but not in probability.

Corrections.
* §1.2: "`L^p` convergence automatically gives `X_n, X ∈ L^p`" is false: the distance
  `E|X_n − X|^p` can vanish while `X ∉ L^p` (the note's suggestion: `X_n = X` Cauchy).
  `Lp_conv_not_memLp`: on `[0,1]`, `X_n = X = 1/u` has `‖X_n − X‖_p = 0` but `X ∉ L¹`.
-/

noncomputable section
namespace powerlib.Stochastic.Conv

open MeasureTheory ProbabilityTheory Filter Set unitInterval
open scoped ENNReal NNReal Topology

/-! ## Mathlib wrappers: implications -/

section Implications

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}

/-- a.s. ⇒ in probability (finite measure). -/
@[powerlib_foundation] theorem ae_imp_inProbability [IsFiniteMeasure P]
    (hX : ∀ n, AEStronglyMeasurable (X n) P)
    (h : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) : TendstoInMeasure P X atTop Y :=
  tendstoInMeasure_of_tendsto_ae hX h

/-- `L^p` ⇒ in probability (via Markov's inequality). -/
@[powerlib_foundation] theorem Lp_imp_inProbability {p : ℝ≥0∞} (hp : p ≠ 0)
    (h : Tendsto (fun n => eLpNorm (X n - Y) p P) atTop (𝓝 0)) : TendstoInMeasure P X atTop Y :=
  tendstoInMeasure_of_tendsto_eLpNorm hp h

/-- In probability ⇒ in distribution. -/
@[powerlib_foundation] theorem inProbability_imp_inDistribution [IsProbabilityMeasure P]
    (h : TendstoInMeasure P X atTop Y) (hX : ∀ n, AEMeasurable (X n) P) :
    TendstoInDistribution X atTop Y (fun _ => P) P :=
  h.tendstoInDistribution hX

/-- Subsequence criterion: convergence in probability gives an a.s. convergent subsequence. -/
@[powerlib_foundation] theorem inProbability_subseq_ae (h : TendstoInMeasure P X atTop Y) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂P, Tendsto (fun i => X (ns i) ω) atTop (𝓝 (Y ω)) :=
  h.exists_seq_tendsto_ae

/-- In probability + uniform integrability ⇒ `L^p` (Vitali). -/
@[powerlib_foundation] theorem inProbability_UI_imp_Lp [IsFiniteMeasure P] {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (hX : ∀ n, AEStronglyMeasurable (X n) P) (hY : MemLp Y p P)
    (hui : UnifIntegrable X p P) (h : TendstoInMeasure P X atTop Y) :
    Tendsto (fun n => eLpNorm (X n - Y) p P) atTop (𝓝 0) :=
  tendsto_Lp_finite_of_tendstoInMeasure hp hp' hX hY hui h

/-- Markov's inequality `ε P(f ≥ ε) ≤ E f` for nonnegative `f`. -/
@[powerlib_foundation] theorem markov_inequality {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P)
    (ε : ℝ≥0∞) : ε * P {ω | ε ≤ f ω} ≤ ∫⁻ ω, f ω ∂P :=
  mul_meas_ge_le_lintegral₀ hf ε

end Implications

/-! ## Counterexample 1: a.s. but not `L¹` -/

/-- The spike `X_n = (n+1) 1_{[0, 1/(n+1))}` on `[0,1]`. -/
def spike (n : ℕ) (u : I) : ℝ := if (u : ℝ) < 1 / ((n : ℝ) + 1) then (n : ℝ) + 1 else 0

@[powerlib_foundation] theorem spike_tendsto_zero {u : I} (hu : (u : ℝ) ≠ 0) :
    Tendsto (fun n => spike n u) atTop (𝓝 0) := by
  have hpos : 0 < (u : ℝ) := lt_of_le_of_ne u.2.1 (Ne.symm hu)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hpos
  refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
  have : 1 / ((n : ℝ) + 1) ≤ u := by
    refine le_trans ?_ hN.le
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
  simp only [spike, not_lt.mpr this, ↓reduceIte]

@[powerlib_foundation] theorem integral_spike (n : ℕ) : ∫ u, spike n u ∂(volume : Measure I) = 1 := by
  have hx : (1 / ((n : ℝ) + 1)) ∈ I := ⟨by positivity, by
    rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]⟩
  set x : I := ⟨1 / ((n : ℝ) + 1), hx⟩
  have e : (fun u : I => spike n u) = (Iio x).indicator (fun _ => (n : ℝ) + 1) := by
    funext u
    rw [Set.indicator_apply]
    simp only [spike, mem_Iio]
    by_cases h : (u : ℝ) < 1 / ((n : ℝ) + 1)
    · simp only [h, show u < x from h, ↓reduceIte]
    · simp only [h, show ¬ u < x from h, ↓reduceIte]
  rw [e, integral_indicator measurableSet_Iio, setIntegral_const, measureReal_def, volume_Iio]
  simp only [x, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  field_simp

/-- **a.s. convergence does not imply `L¹` convergence**. -/
@[powerlib_foundation] theorem ae_not_L1 :
    (∀ᵐ u ∂(volume : Measure I), Tendsto (fun n => spike n u) atTop (𝓝 0)) ∧
      ¬ Tendsto (fun n => ∫ u, |spike n u - 0| ∂(volume : Measure I)) atTop (𝓝 0) := by
  constructor
  · have h0 : (volume : Measure I) {u | (u : ℝ) = 0} = 0 := by
      have : {u : I | (u : ℝ) = 0} = {0} := by
        ext u
        simp only [mem_ofPred_eq, mem_singleton_iff]
        exact ⟨fun h => Subtype.ext h, fun h => by subst h; rfl⟩
      rw [this]; exact measure_singleton _
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with u hu
    exact spike_tendsto_zero hu
  · have e : ∀ n, ∫ u, |spike n u - 0| ∂(volume : Measure I) = 1 := by
      intro n
      have : (fun u : I => |spike n u - 0|) = fun u => spike n u := by
        funext u; simp only [sub_zero]; unfold spike; split_ifs <;> simp; positivity
      rw [this, integral_spike]
    simp_rw [e]
    intro h
    have := tendsto_nhds_unique h tendsto_const_nhds
    norm_num at this

/-! ## Counterexample 2: in probability but not a.s. -/

/-- Product of independent uniform laws on `[0,1]^ℕ`. -/
abbrev unifSeq : Measure (ℕ → I) := Measure.infinitePi fun _ => volume

/-- Events `A_n = {ω_n ≤ 1/(n+1)}`. -/
def eventA (n : ℕ) : Set (ℕ → I) := {ω | ((ω n : I) : ℝ) ≤ 1 / ((n : ℝ) + 1)}

@[powerlib_foundation] theorem measurableSet_eventA (n : ℕ) : MeasurableSet (eventA n) :=
  measurableSet_le (by fun_prop) measurable_const

@[powerlib_foundation] theorem unifSeq_eventA (n : ℕ) : unifSeq (eventA n) = ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
  have hx : (1 / ((n : ℝ) + 1)) ∈ I := ⟨by positivity, by
    rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]⟩
  set x : I := ⟨1 / ((n : ℝ) + 1), hx⟩
  have e : eventA n = (fun ω : ℕ → I => ω n) ⁻¹' Iic x := by
    ext ω; simp [eventA, x, ← Subtype.coe_le_coe]
  rw [e, ← Measure.map_apply (by fun_prop) measurableSet_Iic, Measure.infinitePi_map_eval,
    volume_Iic]

@[powerlib_foundation] theorem iIndepSet_eventA : iIndepSet eventA unifSeq := by
  rw [iIndepSet_iff_meas_biInter measurableSet_eventA]
  intro s
  have hind := iIndepFun_infinitePi (P := fun _ : ℕ => (volume : Measure I))
    (X := fun _ (u : I) => (u : ℝ)) (fun _ => by fun_prop)
  have := hind.measure_inter_preimage_eq_mul s (sets := fun n => Iic (1 / ((n : ℝ) + 1)))
    (fun _ _ => measurableSet_Iic)
  exact this

@[powerlib_foundation] theorem tsum_unifSeq_eventA : ∑' n, unifSeq (eventA n) = ∞ := by
  simp_rw [unifSeq_eventA]
  by_contra h
  have hs : Summable (fun n : ℕ => (1 / ((n : ℝ) + 1)).toNNReal) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable]; exact h
  have hs' : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    have := NNReal.summable_coe.mpr hs
    refine this.congr fun n => ?_
    rw [Real.coe_toNNReal _ (by positivity)]
  have : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
    rw [← summable_nat_add_iff 1]
    simpa using hs'
  exact Real.not_summable_one_div_natCast this

/-- **Convergence in probability does not imply a.s. convergence**. -/
@[powerlib_foundation] theorem inProbability_not_ae :
    TendstoInMeasure unifSeq (fun n => (eventA n).indicator (fun _ => (1 : ℝ))) atTop 0 ∧
      ¬ (∀ᵐ ω ∂unifSeq, Tendsto (fun n => (eventA n).indicator (fun _ => (1 : ℝ)) ω) atTop
        (𝓝 0)) := by
  constructor
  · intro ε hε
    have hle : ∀ n, unifSeq {ω | ε ≤ edist ((eventA n).indicator (fun _ => (1 : ℝ)) ω) 0} ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
      intro n
      rw [← unifSeq_eventA]
      apply measure_mono
      intro ω hω
      by_contra hA
      simp [indicator_of_notMem hA] at hω
      exact absurd hω hε.ne'
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => zero_le) hle
  · intro h
    have h1 := measure_limsup_eq_one measurableSet_eventA iIndepSet_eventA tsum_unifSeq_eventA
    have h2 : ∀ᵐ ω ∂unifSeq, ω ∉ limsup eventA atTop := by
      filter_upwards [h] with ω hω hmem
      rw [mem_limsup_iff_frequently_mem] at hmem
      have := hω.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
      obtain ⟨n, hn1, hn2⟩ := (hmem.and_eventually this).exists
      simp [indicator_of_mem hn1] at hn2
    rw [← measure_eq_zero_iff_ae_notMem] at h2
    rw [h2] at h1
    exact zero_ne_one h1

/-! ## Counterexample 3: in distribution but not in probability -/

/-- **Convergence in distribution does not imply convergence in probability**: `X ~ N(0,1)`,
`X_n = X`, limit `−X` (same law). -/
@[powerlib_foundation] theorem inDistribution_not_inProbability :
    TendstoInDistribution (fun _ : ℕ => (id : ℝ → ℝ)) atTop (fun x => -x)
        (fun _ => gaussianReal 0 1) (gaussianReal 0 1) ∧
      ¬ TendstoInMeasure (gaussianReal 0 1) (fun _ : ℕ => (id : ℝ → ℝ)) atTop (fun x => -x) := by
  constructor
  · refine ⟨fun _ => measurable_id.aemeasurable, by fun_prop, ?_⟩
    have e : (gaussianReal 0 1).map (fun x : ℝ => -x) = (gaussianReal 0 1).map id := by
      rw [gaussianReal_map_neg, Measure.map_id, neg_zero]
    simp only [e]
    exact tendsto_const_nhds
  · intro h
    have h1 := h 2 (by norm_num)
    simp only [id] at h1
    have hpos : 0 < gaussianReal 0 1 {x : ℝ | (2 : ℝ≥0∞) ≤ edist x (-x)} := by
      have hsub : Ici (1 : ℝ) ⊆ {x : ℝ | (2 : ℝ≥0∞) ≤ edist x (-x)} := by
        intro x hx
        simp only [mem_Ici] at hx
        simp only [mem_ofPred_eq, edist_dist, Real.dist_eq, sub_neg_eq_add]
        rw [show x + x = 2 * x by ring, abs_of_nonneg (by linarith)]
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      have hvol : volume (Ici (1 : ℝ)) ≠ 0 := by simp
      have hac := gaussianReal_absolutelyContinuous' (0 : ℝ) (one_ne_zero)
      refine lt_of_lt_of_le ?_ (measure_mono hsub)
      rw [pos_iff_ne_zero]
      intro h0
      exact hvol (hac h0)
    have := tendsto_nhds_unique h1 tendsto_const_nhds
    exact hpos.ne' this.symm

/-! ## Correction: `L^p` distance does not certify membership in `L^p` -/

/-- `u ↦ 1/u` is not integrable on `[0,1]`. -/
@[powerlib_foundation] theorem not_integrable_inv_unitInterval :
    ¬ Integrable (fun u : I => 1 / (u : ℝ)) (volume : Measure I) := by
  intro h
  have h' : IntegrableOn (fun x : ℝ => 1 / x) I volume :=
    (measurePreserving_coe.integrable_comp_emb measurableEmbedding_coe
      (g := fun x : ℝ => 1 / x)).mp h
  have hii : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (h'.mono_set Ioc_subset_Icc_self).congr_fun (fun x _ => one_div x) measurableSet_Ioc
  rw [intervalIntegrable_inv_iff] at hii
  simp at hii

/-- **Correction (§1.2)**: `X_n = X = 1/u` on `[0,1]` has `‖X_n − X‖_p = 0` for all `n` (so
`X_n → X` "in `L^p`" as a distance), yet `X ∉ L¹`. -/
@[powerlib_foundation] theorem Lp_conv_not_memLp (p : ℝ≥0∞) :
    (∀ n : ℕ, eLpNorm ((fun _ : ℕ => fun u : I => 1 / (u : ℝ)) n - fun u : I => 1 / (u : ℝ)) p
      volume = 0) ∧ ¬ MemLp (fun u : I => 1 / (u : ℝ)) 1 volume := by
  refine ⟨fun n => by simp, fun h => not_integrable_inv_unitInterval ?_⟩
  exact memLp_one_iff_integrable.mp h

end powerlib.Stochastic.Conv
