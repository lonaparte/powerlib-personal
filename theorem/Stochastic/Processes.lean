import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! # Filtrations, stopping times, hitting times and optional stopping

Stopping times, hitting and exit times, stopped martingales and optional stopping in discrete and
continuous time; a Markov process need not be a martingale.

Scope.
* Probability theory, not an engineering result.
* Related modules: `OptionalStoppingUI.lean` (optional stopping for uniformly integrable stopped
  martingales), `MartingaleNotMarkov.lean` (a martingale that is not Markov),
  `ProcessFoundations.lean` (adapted / progressive / predictable, finite-dimensional laws).

Source: work-sync theory/T-process-foundations-stochastic.md §1.1 (filtered space, usual
conditions), §1.2 (adapted processes); theory/T-martingales-stopping-times.md §1.1
(martingales, discrete increment form), §1.3 (stopping times, hitting times
`τ_a = inf{t ≥ 0 : X_t ≥ a}` are stopping times), §1.4 (stopped processes), §1.5 (optional
stopping), §1.6.1 (Brownian hitting time); theory/T-first-passage-time.md
(`τ_exit = inf{t ≥ 0 : X_t ∉ 𝒟}`); theory/T-process-foundations-stochastic.md §1.4
("Markov need not be a martingale").

Results.
* Mathlib wrappers (Mathlib declaration in brackets): `discrete_hitting_isStoppingTime`
  [`MeasureTheory.Adapted.isStoppingTime_hittingAfter`], `optional_stopping_bounded`
  [`Submartingale.expected_stoppedValue_mono`], `optional_stopping_iff`
  [`submartingale_iff_expected_stoppedValue_mono`], `martingale_stoppedValue_condExp`
  [`Martingale.stoppedValue_ae_eq_condExp_of_le_const`], `submartingale_stopped`
  [`Submartingale.stoppedProcess`].
* `martingale_stoppedProcess` — a stopped (discrete-time, real) martingale is a martingale
  (from the sub/supermartingale cases).
* `hittingAfter_le_iff_of_continuous`, `continuous_hitting_isStoppingTime` — in **continuous
  time** `ℝ≥0`, the hitting time of a **closed** set by an adapted process with continuous paths
  is a stopping time (no usual conditions needed); `continuous_exit_isStoppingTime`: the exit
  time of an **open** domain `𝒟` is a stopping time.
* `UsualConditions`, `UsualConditions.null_mem` — usual conditions (complete + right-continuous
  filtration); every null set is measurable at every time.
* `deterministic_markov_not_martingale` — the deterministic process `X_n = n` is Markov (in the
  conditional-expectation sense, written out in the statement: for bounded measurable `g`,
  `E[g(X_{n+1}) | 𝓕_n] = E[g(X_{n+1}) | σ(X_n)]` a.s.) but is not a martingale.

Corrections.
* T-martingales §1.6.1: "`W_{t∧τ_a}` is bounded" is false for a one-sided level: a stopped path
  is only bounded on the side of the level (`oneSided_stopped_unbounded`: the path `w(t) = −t`
  never reaches `a > 0`, so `w(t ∧ τ_a) = −t` is unbounded). The bounded-stopping argument needs
  the **two-sided** exit time from `(a, b)`: then `w(t ∧ τ) ∈ [a, b]` for every continuous path
  started in `[a, b]` (`twoSided_stopped_mem`).
-/

noncomputable section
namespace powerlib.Stochastic.Proc

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-! ## Mathlib wrappers (discrete time) -/

section Discrete

variable {μ : Measure Ω} {𝒢 : Filtration ℕ m} {f : ℕ → Ω → ℝ} {τ π : Ω → WithTop ℕ}

/-- Discrete hitting (and exit) times of adapted processes are stopping times. -/
@[tmio T, powerlib_foundation] theorem discrete_hitting_isStoppingTime {β : Type*} [MeasurableSpace β]
    {u : ℕ → Ω → β} {s : Set β} (hu : Adapted 𝒢 u) (hs : MeasurableSet s) (n : ℕ) :
    IsStoppingTime 𝒢 (hittingAfter u s n) :=
  hu.isStoppingTime_hittingAfter hs

/-- **Optional stopping, bounded stopping times**. -/
@[powerlib_foundation] theorem optional_stopping_bounded [SigmaFiniteFiltration μ 𝒢]
    (hf : Submartingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ) (hπ : IsStoppingTime 𝒢 π)
    (hle : τ ≤ π) {N : ℕ} (hbdd : ∀ ω, π ω ≤ N) :
    ∫ ω, stoppedValue f τ ω ∂μ ≤ ∫ ω, stoppedValue f π ω ∂μ :=
  hf.expected_stoppedValue_mono hτ hπ hle hbdd

/-- **Optional stopping theorem** (characterization of submartingales). -/
@[powerlib_foundation] theorem optional_stopping_iff [SigmaFiniteFiltration μ 𝒢]
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ) :
    Submartingale f 𝒢 μ ↔ ∀ τ π : Ω → WithTop ℕ, IsStoppingTime 𝒢 τ → IsStoppingTime 𝒢 π →
      τ ≤ π → (∃ N : ℕ, ∀ x, π x ≤ N) →
        ∫ ω, stoppedValue f τ ω ∂μ ≤ ∫ ω, stoppedValue f π ω ∂μ :=
  submartingale_iff_expected_stoppedValue_mono hadp hint

/-- Optional sampling: `f_τ = E[f_n | 𝓕_τ]` for `τ ≤ n`. -/
@[powerlib_foundation] theorem martingale_stoppedValue_condExp [SigmaFiniteFiltration μ 𝒢]
    (h : Martingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ) {n : ℕ} (hτ_le : ∀ x, τ x ≤ n) :
    stoppedValue f τ =ᵐ[μ] μ[f n | hτ.measurableSpace] :=
  h.stoppedValue_ae_eq_condExp_of_le_const hτ hτ_le

/-- Stopped submartingales are submartingales. -/
@[powerlib_foundation] theorem submartingale_stopped [SigmaFiniteFiltration μ 𝒢]
    (h : Submartingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ) :
    Submartingale (stoppedProcess f τ) 𝒢 μ := h.stoppedProcess hτ

/-- **Stopped martingales are martingales** (T-martingales §1.4). -/
@[powerlib_foundation] theorem martingale_stoppedProcess [SigmaFiniteFiltration μ 𝒢]
    (h : Martingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ) :
    Martingale (stoppedProcess f τ) 𝒢 μ := by
  rw [martingale_iff] at h ⊢
  obtain ⟨hsup, hsub⟩ := h
  refine ⟨?_, hsub.stoppedProcess hτ⟩
  have h1 := hsup.neg.stoppedProcess hτ
  have e : stoppedProcess (-f) τ = -stoppedProcess f τ := rfl
  rw [e] at h1
  simpa using h1.neg

end Discrete

/-! ## Continuous-time hitting and exit times -/

section Continuous

variable {E : Type*} [MetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
  {𝓕 : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → E}

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
/-- For continuous paths and a closed set, the hitting time after `0` is at most `i` iff the
path visits the set during `[0, i]` (the infimum is attained). -/
@[powerlib_foundation] theorem hittingAfter_le_iff_of_continuous {F : Set E} (hF : IsClosed F)
    {ω : Ω} (hc : Continuous fun t => X t ω) (i : ℝ≥0) :
    hittingAfter X F 0 ω ≤ i ↔ ∃ j, j ≤ i ∧ X j ω ∈ F := by
  constructor
  · intro h
    classical
    by_cases hex : ∃ j, 0 ≤ j ∧ X j ω ∈ F
    · have hS : IsClosed {j : ℝ≥0 | 0 ≤ j ∧ X j ω ∈ F} := by
        simp only [zero_le, true_and]
        exact hF.preimage hc
      have hne : ({j : ℝ≥0 | 0 ≤ j ∧ X j ω ∈ F}).Nonempty := hex
      have hmem := hS.csInf_mem hne (OrderBot.bddBelow _)
      simp only [hittingAfter, hex, ↓reduceIte] at h
      exact ⟨_, by exact_mod_cast h, hmem.2⟩
    · simp only [hittingAfter, hex, ↓reduceIte] at h
      exact absurd h (not_le.mpr (WithTop.coe_lt_top i))
  · rintro ⟨j, hj, hjF⟩
    exact le_trans (hittingAfter_le_of_mem zero_le hjF) (by exact_mod_cast hj)

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
/-- Visiting a closed nonempty set during `[0, i]` is a countable condition on rational times. -/
@[powerlib_foundation] theorem exists_mem_iff_countable {F : Set E} (hF : IsClosed F)
    (hFne : F.Nonempty) {ω : Ω} (hc : Continuous fun t => X t ω) (i : ℝ≥0) :
    (∃ j, j ≤ i ∧ X j ω ∈ F) ↔ ∀ k : ℕ, infDist (X i ω) F < 1 / ((k : ℝ) + 1) ∨
      ∃ q : ℚ, 0 ≤ q ∧ (q : ℝ) ≤ i ∧ infDist (X (q : ℝ).toNNReal ω) F < 1 / ((k : ℝ) + 1) := by
  set g : ℝ≥0 → ℝ := fun t => infDist (X t ω) F with hg
  have hgc : Continuous g := (continuous_infDist_pt F).comp hc
  constructor
  · rintro ⟨j, hj, hjF⟩ k
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hgj : g j = 0 := infDist_zero_of_mem hjF
    rcases eq_or_lt_of_le hj with hji | hji
    · left; rw [← hji]; simp only [hg] at hgj; rw [hgj]; exact hk
    · right
      obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hgc j _ hk
      have hlt : (j : ℝ) < min ((j : ℝ) + δ) i := lt_min (by linarith) (by exact_mod_cast hji)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
      have hq0 : (0 : ℝ) ≤ q := le_trans j.2 hq1.le
      refine ⟨q, by exact_mod_cast hq0, le_trans hq2.le (min_le_right _ _), ?_⟩
      have hd : dist (q : ℝ).toNNReal j < δ := by
        rw [NNReal.dist_eq, Real.coe_toNNReal _ hq0, abs_of_pos (by linarith)]
        linarith [min_le_left ((j : ℝ) + δ) i]
      have := hball _ hd
      rw [hgj, Real.dist_eq, sub_zero, abs_of_nonneg infDist_nonneg] at this
      exact this
  · intro h
    -- choose times `t k ∈ [0, i]` with `g (t k) < 1/(k+1)`
    have hch : ∀ k : ℕ, ∃ t : ℝ≥0, t ≤ i ∧ g t < 1 / ((k : ℝ) + 1) := by
      intro k
      rcases h k with h1 | ⟨q, hq0, hqi, hq⟩
      · exact ⟨i, le_rfl, h1⟩
      · refine ⟨(q : ℝ).toNNReal, ?_, hq⟩
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by exact_mod_cast hq0)]; exact hqi
    choose t ht hgt using hch
    have hcomp : IsCompact (Icc (0 : ℝ≥0) i) := isCompact_Icc
    obtain ⟨j, hjmem, φ, hφ, hlim⟩ := hcomp.tendsto_subseq (x := t) fun k => ⟨zero_le, ht k⟩
    have hgφ : Tendsto (fun k => g (t (φ k))) atTop (𝓝 (g j)) := (hgc.tendsto j).comp hlim
    have hup : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have hle : g j ≤ 0 :=
      le_of_tendsto_of_tendsto hgφ hup (Eventually.of_forall fun k => (hgt (φ k)).le)
    have hg0 : g j = 0 := le_antisymm hle infDist_nonneg
    refine ⟨j, hjmem.2, ?_⟩
    rw [← hF.closure_eq, mem_closure_iff_infDist_zero hFne]
    exact hg0

/-- **Continuous-time hitting times of closed sets are stopping times** (T-martingales §1.3):
for an adapted process with continuous paths and a closed set `F`, `τ_F = inf{t ≥ 0 : X_t ∈ F}`
is a stopping time of the (raw) filtration. -/
@[powerlib_foundation] theorem continuous_hitting_isStoppingTime (hX : Adapted 𝓕 X)
    (hc : ∀ ω, Continuous fun t => X t ω) {F : Set E} (hF : IsClosed F) :
    IsStoppingTime 𝓕 (hittingAfter X F 0) := by
  intro i
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · have : {ω | hittingAfter X F 0 ω ≤ i} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rw [hittingAfter_le_iff_of_continuous hF (hc ω)]
      simp [hFe]
    rw [this]; exact @MeasurableSet.empty _ (𝓕 i)
  have key : {ω | hittingAfter X F 0 ω ≤ i} = ⋂ k : ℕ,
      ({ω | infDist (X i ω) F < 1 / ((k : ℝ) + 1)} ∪
        ⋃ q : ℚ, {ω | 0 ≤ q ∧ (q : ℝ) ≤ i ∧
          infDist (X (q : ℝ).toNNReal ω) F < 1 / ((k : ℝ) + 1)}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_iUnion]
    rw [hittingAfter_le_iff_of_continuous hF (hc ω), exists_mem_iff_countable hF hFne (hc ω)]
  rw [key]
  refine MeasurableSet.iInter fun k => MeasurableSet.union ?_ (MeasurableSet.iUnion fun q => ?_)
  · exact (((continuous_infDist_pt F).measurable).comp (hX i)) measurableSet_Iio
  · by_cases hq : 0 ≤ q ∧ (q : ℝ) ≤ i
    · have hle : (q : ℝ).toNNReal ≤ i := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by exact_mod_cast hq.1)]; exact hq.2
      have hm : MeasurableSet[𝓕 i]
          {ω | infDist (X (q : ℝ).toNNReal ω) F < 1 / ((k : ℝ) + 1)} :=
        𝓕.mono hle _ ((((continuous_infDist_pt F).measurable).comp (hX _)) measurableSet_Iio)
      convert hm using 1
      ext ω; simp [hq]
    · convert @MeasurableSet.empty _ (𝓕 i) using 1
      ext ω; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => hq ⟨h.1, h.2.1⟩

/-- **Exit times of open domains are stopping times** (T-first-passage-time): for an open
`𝒟`, `τ_exit = inf{t ≥ 0 : X_t ∉ 𝒟}` is the hitting time of the closed set `𝒟ᶜ`. -/
@[powerlib_foundation] theorem continuous_exit_isStoppingTime (hX : Adapted 𝓕 X)
    (hc : ∀ ω, Continuous fun t => X t ω) {D : Set E} (hD : IsOpen D) :
    IsStoppingTime 𝓕 (hittingAfter X Dᶜ 0) :=
  continuous_hitting_isStoppingTime hX hc hD.isClosed_compl

end Continuous

/-! ## Usual conditions -/

/-- **Usual conditions** (T-process-foundations §1.1): `𝓕₀` contains all `P`-null sets and the
filtration is right continuous. -/
def UsualConditions (P : Measure Ω) (𝓕 : Filtration ℝ≥0 m) : Prop :=
  (∀ s, P s = 0 → MeasurableSet[𝓕 0] s) ∧ 𝓕.IsRightContinuous

/-- Under the usual conditions every `P`-null set is `𝓕_t`-measurable for every `t`. -/
@[powerlib_foundation] theorem UsualConditions.null_mem {P : Measure Ω} {𝓕 : Filtration ℝ≥0 m}
    (h : UsualConditions P 𝓕) {s : Set Ω} (hs : P s = 0) (t : ℝ≥0) : MeasurableSet[𝓕 t] s :=
  𝓕.mono zero_le _ (h.1 s hs)

/-! ## Markov does not imply martingale -/

/-- **Markov but not a martingale** (T-process-foundations §1.4): on any probability space the
deterministic process `X_n = n` is Markov (for any filtration) and is not a martingale.

The first conjunct is the Markov property of a real discrete-time process `X` w.r.t. a filtration
`𝓕`, in conditional expectation form, written out for `X_n = n`: for bounded measurable test
functions `g`, `E[g(X_{n+1}) | 𝓕_n] = E[g(X_{n+1}) | σ(X_n)]` a.s. -/
@[powerlib_foundation] theorem deterministic_markov_not_martingale {P : Measure Ω}
    [IsProbabilityMeasure P] (𝓕 : Filtration ℕ m) :
    (∀ (n : ℕ) (g : ℝ → ℝ), Measurable g → (∃ C, ∀ x, |g x| ≤ C) →
      P[fun _ => g ((n + 1 : ℕ) : ℝ) | 𝓕 n] =ᵐ[P]
        P[fun _ => g ((n + 1 : ℕ) : ℝ) |
          MeasurableSpace.comap (fun _ : Ω => (n : ℝ)) inferInstance]) ∧
      ¬ Martingale (fun (n : ℕ) (_ : Ω) => (n : ℝ)) 𝓕 P := by
  constructor
  · intro n g _ _
    have hc : MeasurableSpace.comap (fun _ : Ω => (n : ℝ)) inferInstance ≤ m := by
      intro s ⟨t, _, hts⟩
      rw [← hts]; exact MeasurableSet.const _
    rw [condExp_const (𝓕.le n), condExp_const hc]
  · intro h
    have h01 := h.2 0 1 zero_le_one
    rw [condExp_const (𝓕.le 0)] at h01
    have : ∀ᵐ ω ∂P, ((1 : ℕ) : ℝ) = ((0 : ℕ) : ℝ) := h01
    obtain ⟨_, hω⟩ := this.exists
    norm_num at hω

/-! ## Correction: one-sided vs two-sided stopping (T-martingales §1.6.1) -/

/-- First time a path leaves `(a, b)` (or `⊤`-like large value never attained: we use `sInf`). -/
def exitTime (w : ℝ → ℝ) (a b : ℝ) : ℝ := sInf {t : ℝ | 0 ≤ t ∧ w t ∉ Ioo a b}

/-- **Two-sided stopping keeps the path bounded**: a continuous path started in `[a, b]`,
stopped at its first exit time from `(a, b)`, stays in `[a, b]` at all times `t ≥ 0`. -/
@[powerlib_foundation] theorem twoSided_stopped_mem {w : ℝ → ℝ} (hw : Continuous w) {a b : ℝ}
    (h0 : w 0 ∈ Icc a b) {t : ℝ} (ht : 0 ≤ t) : w (min t (exitTime w a b)) ∈ Icc a b := by
  set S := {t : ℝ | 0 ≤ t ∧ w t ∉ Ioo a b}
  have hbdd : BddBelow S := ⟨0, fun s hs => hs.1⟩
  -- before the exit time the path is inside `(a, b)`
  have hbefore : ∀ s, 0 ≤ s → s < exitTime w a b → w s ∈ Ioo a b := by
    intro s hs hlt
    by_contra hns
    exact absurd (csInf_le hbdd ⟨hs, hns⟩) (not_le.mpr hlt)
  -- a point approached from inside `(a, b)` lies in `[a, b]`
  have hlim : ∀ τ, 0 < τ → τ ≤ exitTime w a b → w τ ∈ Icc a b := by
    intro τ hτ hτe
    have hs : Tendsto (fun k : ℕ => τ - τ * (1 / ((k : ℝ) + 1))) atTop (𝓝 τ) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul τ).const_sub τ
      simpa using this
    refine isClosed_Icc.mem_of_tendsto ((hw.tendsto τ).comp hs) (Eventually.of_forall fun k => ?_)
    have h1 : 0 < 1 / ((k : ℝ) + 1) := by positivity
    have h2 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    exact Ioo_subset_Icc_self (hbefore _ (by nlinarith) (by nlinarith))
  by_cases hS : S.Nonempty
  · have hτ0 : 0 ≤ exitTime w a b := le_csInf hS fun s hs => hs.1
    rcases le_or_gt t (exitTime w a b) with htτ | htτ
    · rw [min_eq_left htτ]
      rcases eq_or_lt_of_le ht with h00 | hpos
      · rw [← h00]; exact h0
      · exact hlim t hpos htτ
    · rw [min_eq_right htτ.le]
      rcases eq_or_lt_of_le hτ0 with h00 | hpos
      · rw [← h00]; exact h0
      · exact hlim _ hpos le_rfl
  · -- never exits: `sInf ∅ = 0`, so the stopped value is `w 0`
    have : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    have hτ : exitTime w a b = 0 := by
      show sInf S = 0; rw [this, Real.sInf_empty]
    rw [hτ, min_eq_right ht]; exact h0

/-- **Correction**: with a one-sided level the stopped path need not be bounded: `w(t) = −t`
never reaches `a > 0`, so the stopped path `w(t ∧ τ_a) = −t` is unbounded below. -/
@[powerlib_foundation] theorem oneSided_stopped_unbounded {a : ℝ} (ha : 0 < a) :
    (∀ t, 0 ≤ t → (fun s : ℝ => -s) t < a) ∧ ¬ BddBelow (range fun t : ℝ≥0 => -((t : ℝ))) := by
  refine ⟨fun t ht => by linarith, ?_⟩
  rintro ⟨M, hM⟩
  have := hM ⟨(|M| + 1).toNNReal, rfl⟩
  simp only at this
  rw [Real.coe_toNNReal _ (by positivity)] at this
  linarith [le_abs_self M, neg_abs_le M]

end powerlib.Stochastic.Proc
