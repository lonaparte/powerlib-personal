import theorem.Attributes
import dependencies.Mathlib
import Mathlib.Data.Nat.Nth
import Mathlib.Order.UpperLower.Basic
import theorem.LTI.Decay

/-! # Envelope detection on sampled records: violation envelopes, events and quantiles

The local-maximum detector of the ENTSO-E/WindEurope prototype tool as generic mathematics on
records: local maxima of a rectified record, exceedance patterns on the peaks, violation
envelopes (maximal runs of consecutive exceeding peaks), events selected by a minimum duration,
their counts and total time, and nearest-rank quantiles of hourly counts.

Scope.
* A record is a sequence `y : ℕ → ℝ` on the samples `0, …, N − 1`; its peaks are the local maxima
  of `|y|` (`IsLocalMaxAbs`: interior sample above its predecessor, not below its successor; the
  first sample of a plateau), in time order (`peakIndex`, `Nat.nth`). The detector compares the
  rectified record with a limit, so positive and negative half-waves both give peaks.
* Everything after the extraction is stated for an arbitrary exceedance pattern `x : ℕ → Prop` on
  `m` peaks with peak times `t : ℕ → ℝ` (nondecreasing on the record, `TimesMono`) and arbitrary
  amplitudes: a threshold comparison `ℓ_k < a_k`, possibly intersected with a time window or an
  exclusion mask, is one such pattern. An envelope `(i, j)` is a maximal run `i ≤ k ≤ j` of
  exceeding peaks; its duration is `t_j − t_i` (a single exceeding peak has duration `0`); the
  events of a duration class `S` (`Ici d`: at least `d`, `Ioi d`: more than `d`) are the
  envelopes with duration in `S`.
* Windows (days, hours) are patterns intersected with a time interval: exceedances are cut at the
  window boundaries. Hourly counts are natural numbers indexed by a finite type; the quantile is
  the nearest-rank one, `Q = min {v | #{h | n_h ≤ v} ≥ ⌈q H⌉}`.
* No model family; no stochastic or spectral content; frequencies enter only through the peak
  spacing and, for the resonance comparison, through the gain of a standard second-order mode.

Source: ENTSO-E/WindEurope Technical Group on Forced Oscillations Report (2 July 2026) §3.3
(local maxima, envelopes "initiated as soon as the local maxima exceeds the dynamic threshold"),
§3.4, §3.7 (frequency blindness, the 0.2 Hz / 1 Hz example), §4.1 (95th percentile,
"168 · 0.05 ≈ 8"), §4.2 (exclusions), §5.6 and Table 9 (minimum durations), §5.1 Fig. 11
(set-point steps through the band-pass filter).

Results.
* Envelopes: `IsEnvelope`, `envelopes`, `mem_envelopes`; every exceeding peak lies in an envelope
  (`exists_envelope`), envelopes are disjoint (`IsEnvelope.eq_of_mem`), a smaller pattern has
  finer envelopes (`IsEnvelope.exists_superset`), no exceedance means no envelope
  (`envelopes_eq_empty`, `envelopes_peakExceeds_eq_empty`: a record within its limit at every
  sample has no envelope).
* Peaks of a record: `IsLocalMaxAbs`, `numPeaks`, `peakIndex`, `peakExceeds`,
  `finite_isLocalMaxAbs`, `peakIndex_spec`, `peakIndex_lt`, `timesMono_peaks` (per-unit
  normalization of a record is in `theorem/Signal/Interpolation.lean`).
* Events: `duration`, `events`, `eventCount`, `eventTime`, `mem_events`; `duration_eq_sum` and
  `eventTime_eq_sum_links` (total time is a sum over links of consecutive peaks);
  `exists_event_superset`, `eventTime_mono` (total exceedance time is monotone in the pattern),
  `events_eq_empty_of_le`, `duration_le_of_le` (duration bounds), `late_peaks_of_le` (bounds on
  peaks late in an envelope), `eventCount_mono_class`, `eventTime_mono_class` (a longer minimum
  duration counts fewer events and less time: Table 9's monotone trend).
* Event counts are not monotone in the pattern (`eventCount_split`: removing the middle
  exceedance of five splits one event into two). Exact counts of a block of exceedances
  (`eventCount_block`) and of a block with every third peak removed (`eventCount_comb`).
* Exponential decay: `duration_lt_of_window`, `lt_mul_exp_neg_iff` (`a < A e^{−σt} ↔
  t < log (A/a)/σ`), `lt_of_abs_le_mul_exp`, `duration_lt_of_exp_bound`; Hurwitz filters:
  `exists_output_bound`, `exists_exceedance_time_bound` (a set-point step seen through a stable
  zero-DC-gain filter exceeds a level only for a bounded time).
* Frequency blindness (§3.7): `envelopes_eq_singleton` (all peaks exceeding: one envelope from the
  first to the last peak, whatever their spacing), `tone_crests_envelope` (tones of different
  frequency over the same window give the same output), `modeGainSq`, `modeGainSq_eq_normSq`,
  `modeGainSq_lt_resonance` (the same amplitude at the mode frequency is amplified `1/(2ζ)`,
  strictly more than above it).
* Aggregation: `abs_sum_le_mul_sum` (capacity-proportional limits survive aggregation),
  `exists_sum_div_le` (mediant inequality).
* Quantiles: `quantileRank`, `countLe`, `nearestRank`, `nearestRank_le_iff_rank`,
  `nearestRank_le_iff` (`Q ≤ c ↔ #{h | n_h > c} ≤ H − ⌈q H⌉`), `nearestRank_spec` (it is the
  `⌈q H⌉`-th smallest count), `nearestRank_mono`, `nearestRank_zero`, `sub_quantileRank`
  (`H − ⌈q H⌉ = ⌊(1 − q) H⌋`), `nearestRank_week_le_iff` (`H = 168`, `q = 0.95`: at most `8`
  hours).

Correction (§3.3–§3.4, Tables 3–9). Monotonicity of the verdicts in the limits holds for
durations, total time, late peaks and the presence of events, but not for event counts: a
stricter limit can merge exceedances (`eventCount_split`). Clause c(ii), which counts events per
hour, is therefore not monotone in the continuous limit
(`ForcedOscillation.clauseC2_not_monotone`).

Family and connection conclusions.
* None: this module defines no family; every result is a property of arbitrary records,
  patterns and counts.
-/

noncomputable section
namespace powerlib.Signal
open Finset

/-! ## Envelopes of an exceedance pattern -/

/-- `(i, j)` is a violation envelope of the exceedance pattern `x` on the peaks `0, …, m − 1`:
the peaks `i, …, j` all exceed, and the run cannot be extended (the peak before `i`, if any, and
the peak after `j`, if it belongs to the record, do not exceed). -/
def IsEnvelope (m : ℕ) (x : ℕ → Prop) (i j : ℕ) : Prop :=
  i ≤ j ∧ j < m ∧ (∀ k, i ≤ k → k ≤ j → x k) ∧ (∀ k, k + 1 = i → ¬ x k) ∧
    (j + 1 < m → ¬ x (j + 1))

open Classical in
/-- The violation envelopes `(start, end)` (peak indices) of the pattern `x`. -/
def envelopes (m : ℕ) (x : ℕ → Prop) : Finset (ℕ × ℕ) :=
  (range m ×ˢ range m).filter fun e => IsEnvelope m x e.1 e.2

@[tmio T, powerlib_foundation] theorem mem_envelopes {m : ℕ} {x : ℕ → Prop} {e : ℕ × ℕ} :
    e ∈ envelopes m x ↔ IsEnvelope m x e.1 e.2 := by
  classical
  simp only [envelopes, mem_filter, mem_product, mem_range]
  exact ⟨fun h => h.2, fun h => ⟨⟨h.1.trans_lt h.2.1, h.2.1⟩, h⟩⟩

/-- Every exceeding peak lies in an envelope. -/
@[tmio T, powerlib_foundation] theorem exists_envelope {m : ℕ} {x : ℕ → Prop} {k : ℕ}
    (hk : k < m) (hx : x k) : ∃ i j, IsEnvelope m x i j ∧ i ≤ k ∧ k ≤ j := by
  classical
  let P : ℕ → Prop := fun i => i ≤ k ∧ ∀ l, i ≤ l → l ≤ k → x l
  have hP : ∃ i, P i := ⟨k, le_rfl, fun l h1 h2 => le_antisymm h2 h1 ▸ hx⟩
  let Q : ℕ → Prop := fun j => k ≤ j ∧ j < m ∧ ∀ l, k ≤ l → l ≤ j → x l
  have hQk : Q k := ⟨le_rfl, hk, fun l h1 h2 => le_antisymm h2 h1 ▸ hx⟩
  have hQ := Nat.findGreatest_spec (P := Q) hk.le hQk
  have hle := Nat.le_findGreatest (P := Q) hk.le hQk
  obtain ⟨hik, hirun⟩ := Nat.find_spec hP
  refine ⟨Nat.find hP, Nat.findGreatest Q m, ⟨hik.trans hQ.1, hQ.2.1, ?_, ?_, ?_⟩, hik, hQ.1⟩
  · intro l h1 h2
    rcases le_total l k with hl | hl
    · exact hirun l h1 hl
    · exact hQ.2.2 l hl h2
  · intro l hl hxl
    have : P l := ⟨by omega, fun l' h1 h2 => by
      rcases Nat.lt_or_ge l' (l + 1) with h | h
      · exact (show l' = l by omega) ▸ hxl
      · exact hirun l' (by omega) h2⟩
    have := Nat.find_min' hP this
    omega
  · intro hj hxj
    have : Q (Nat.findGreatest Q m + 1) := ⟨by omega, hj, fun l h1 h2 => by
      rcases Nat.lt_or_ge l (Nat.findGreatest Q m + 1) with h | h
      · exact hQ.2.2 l h1 (by omega)
      · exact (show l = Nat.findGreatest Q m + 1 by omega) ▸ hxj⟩
    have := Nat.le_findGreatest (P := Q) (show Nat.findGreatest Q m + 1 ≤ m by omega) this
    omega

/-- Two envelopes that share a peak are equal: the envelopes of a pattern are disjoint. -/
@[tmio T, powerlib_foundation] theorem IsEnvelope.eq_of_mem {m : ℕ} {x : ℕ → Prop}
    {i j i' j' k : ℕ} (h : IsEnvelope m x i j) (h' : IsEnvelope m x i' j') (hk : i ≤ k ∧ k ≤ j)
    (hk' : i' ≤ k ∧ k ≤ j') : i = i' ∧ j = j' := by
  obtain ⟨-, hjm, hrun, hstart, hend⟩ := h
  obtain ⟨-, hjm', hrun', hstart', hend'⟩ := h'
  have hi : i = i' := by
    rcases lt_trichotomy i i' with hlt | heq | hgt
    · exact absurd (hrun (i' - 1) (by omega) (by omega)) (hstart' (i' - 1) (by omega))
    · exact heq
    · exact absurd (hrun' (i - 1) (by omega) (by omega)) (hstart (i - 1) (by omega))
  refine ⟨hi, ?_⟩
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · exact absurd (hrun' (j + 1) (by omega) (by omega)) (hend (by omega))
  · exact heq
  · exact absurd (hrun (j' + 1) (by omega) (by omega)) (hend' (by omega))

/-- A smaller pattern has finer envelopes: if every `x'`-exceedance is an `x`-exceedance, every
`x'`-envelope lies inside an `x`-envelope. -/
@[tmio T, powerlib_foundation] theorem IsEnvelope.exists_superset {m : ℕ} {x x' : ℕ → Prop}
    (hx : ∀ k, x' k → x k) {i' j' : ℕ} (h : IsEnvelope m x' i' j') :
    ∃ i j, IsEnvelope m x i j ∧ i ≤ i' ∧ j' ≤ j := by
  obtain ⟨hij', hjm', hrun', -, -⟩ := h
  obtain ⟨i, j, hij, hi, hj⟩ := exists_envelope (hij'.trans_lt hjm') (hx i' (hrun' i' le_rfl hij'))
  refine ⟨i, j, hij, hi, ?_⟩
  by_contra hlt
  exact hij.2.2.2.2 (by omega) (hx _ (hrun' (j + 1) (by omega) (by omega)))

/-- A pattern with no exceedance has no envelope. -/
@[tmio T, powerlib_foundation] theorem envelopes_eq_empty {m : ℕ} {x : ℕ → Prop}
    (h : ∀ k < m, ¬ x k) : envelopes m x = ∅ := by
  refine eq_empty_of_forall_notMem fun e he => ?_
  obtain ⟨hij, hjm, hrun, -, -⟩ := mem_envelopes.mp he
  exact h e.1 (hij.trans_lt hjm) (hrun e.1 le_rfl hij)

/-! ## Local maxima of a sampled record -/

/-- Peak times that do not decrease along the record. -/
def TimesMono (m : ℕ) (t : ℕ → ℝ) : Prop := ∀ i j, i ≤ j → j < m → t i ≤ t j

section Peaks

variable {y L : ℕ → ℝ} {N : ℕ}

/-- Sample `k` of the record `y` (samples `0, …, N − 1`) is a local maximum of the rectified
record `|y|`: an interior sample above its predecessor and not below its successor (the first
sample of a plateau). -/
def IsLocalMaxAbs (y : ℕ → ℝ) (N k : ℕ) : Prop :=
  0 < k ∧ k + 1 < N ∧ |y (k - 1)| < |y k| ∧ |y (k + 1)| ≤ |y k|

open Classical in
/-- Number of local maxima of `|y|` among the samples `0, …, N − 1`. -/
def numPeaks (y : ℕ → ℝ) (N : ℕ) : ℕ := Nat.count (IsLocalMaxAbs y N) N

/-- Sample index of the `i`-th local maximum, in time order. -/
def peakIndex (y : ℕ → ℝ) (N i : ℕ) : ℕ := Nat.nth (IsLocalMaxAbs y N) i

/-- The `i`-th local maximum exceeds the per-sample limit `L`: the exceedance pattern of the
record on its peaks. -/
def peakExceeds (y L : ℕ → ℝ) (N i : ℕ) : Prop := L (peakIndex y N i) < |y (peakIndex y N i)|

@[tmio T, powerlib_foundation] theorem finite_isLocalMaxAbs (y : ℕ → ℝ) (N : ℕ) :
    (Set.ofPred (IsLocalMaxAbs y N)).Finite :=
  (Set.finite_lt_nat N).subset fun _ hk => by have := hk.2.1; show _ < N; omega

/-- The `i`-th peak (`i` below the number of peaks) is a local maximum inside the record. -/
@[tmio T, powerlib_foundation] theorem peakIndex_spec {i : ℕ} (hi : i < numPeaks y N) :
    IsLocalMaxAbs y N (peakIndex y N i) ∧ peakIndex y N i < N := by
  classical
  exact ⟨Nat.nth_mem i fun hf => hi.trans_le (Nat.count_le_card hf N),
    Nat.nth_lt_of_lt_count hi⟩

/-- The peaks are in strictly increasing time order. -/
@[tmio T, powerlib_foundation] theorem peakIndex_lt {i j : ℕ} (hij : i < j)
    (hj : j < numPeaks y N) : peakIndex y N i < peakIndex y N j := by
  classical
  exact Nat.nth_lt_nth_of_lt_card (finite_isLocalMaxAbs y N) hij
    (hj.trans_le (Nat.count_le_card _ N))

/-- With sampling period `h ≥ 0` the peak times `h · k_i` are nondecreasing. -/
@[tmio T, powerlib_foundation] theorem timesMono_peaks {h : ℝ} (hh : 0 ≤ h) :
    TimesMono (numPeaks y N) (fun i => h * peakIndex y N i) := by
  intro i j hij hj
  rcases hij.lt_or_eq with hlt | rfl
  · exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (peakIndex_lt hlt hj).le) hh
  · exact le_rfl

/-- A record within its limit at every sample has no violation envelope. -/
@[tmio T, powerlib_foundation] theorem envelopes_peakExceeds_eq_empty (h : ∀ k, |y k| ≤ L k) :
    envelopes (numPeaks y N) (peakExceeds y L N) = ∅ :=
  envelopes_eq_empty fun _ _ hi => (h _).not_gt hi

end Peaks

/-! ## Events: durations, counts and exceedance time -/

/-- Duration `t_end − t_start` of an envelope `e = (start, end)` whose peaks occur at the times
`t`. -/
def duration (t : ℕ → ℝ) (e : ℕ × ℕ) : ℝ := t e.2 - t e.1

open Classical in
/-- The events of the pattern `x`: its envelopes whose duration lies in the class `S`. A
minimum-duration filter is `S = Ici d` (exceedances shorter than `d` are disregarded) or
`S = Ioi d` (only exceedances longer than `d` count); `S = univ` keeps every envelope. -/
def events (m : ℕ) (x : ℕ → Prop) (t : ℕ → ℝ) (S : Set ℝ) : Finset (ℕ × ℕ) :=
  (envelopes m x).filter fun e => duration t e ∈ S

/-- Number of events. -/
def eventCount (m : ℕ) (x : ℕ → Prop) (t : ℕ → ℝ) (S : Set ℝ) : ℕ := (events m x t S).card

/-- Total exceedance time: the summed duration of the events. -/
def eventTime (m : ℕ) (x : ℕ → Prop) (t : ℕ → ℝ) (S : Set ℝ) : ℝ :=
  ∑ e ∈ events m x t S, duration t e

@[tmio T, powerlib_foundation] theorem mem_events {m : ℕ} {x : ℕ → Prop} {t : ℕ → ℝ}
    {S : Set ℝ} {e : ℕ × ℕ} :
    e ∈ events m x t S ↔ IsEnvelope m x e.1 e.2 ∧ duration t e ∈ S := by
  classical
  simp only [events, mem_filter, mem_envelopes]

/-- The duration of a run is the sum of the gaps between its consecutive peaks. -/
@[tmio T, powerlib_foundation] theorem duration_eq_sum {t : ℕ → ℝ} {i j : ℕ} (h : i ≤ j) :
    duration t (i, j) = ∑ k ∈ Ico i j, (t (k + 1) - t k) :=
  (sum_Ico_sub t h).symm

/-- The total exceedance time is the summed gap over the links (pairs of consecutive peaks) that
lie inside an event. -/
@[tmio T, powerlib_foundation] theorem eventTime_eq_sum_links (m : ℕ) (x : ℕ → Prop)
    (t : ℕ → ℝ) (S : Set ℝ) :
    eventTime m x t S =
      ∑ k ∈ (events m x t S).biUnion (fun e => Ico e.1 e.2), (t (k + 1) - t k) := by
  rw [sum_biUnion, eventTime]
  · refine sum_congr rfl fun e he => ?_
    exact duration_eq_sum (mem_events.mp he).1.1
  · intro e he e' he' hne
    refine Finset.disjoint_left.mpr fun k hk hk' => hne ?_
    rw [mem_Ico] at hk hk'
    obtain ⟨h1, h2⟩ := (mem_events.mp he).1.eq_of_mem (mem_events.mp he').1
      ⟨hk.1, hk.2.le⟩ ⟨hk'.1, hk'.2.le⟩
    exact Prod.ext h1 h2

/-- With nondecreasing peak times, every envelope has nonnegative duration. -/
@[tmio T, powerlib_foundation] theorem IsEnvelope.duration_nonneg {m : ℕ} {x : ℕ → Prop}
    {t : ℕ → ℝ} (ht : TimesMono m t) {i j : ℕ} (h : IsEnvelope m x i j) :
    0 ≤ duration t (i, j) :=
  sub_nonneg.mpr (ht i j h.1 h.2.1)

/-- A smaller pattern has finer events: if every `x'`-exceedance is an `x`-exceedance, the
duration class `S` is upward closed and the peak times are nondecreasing, every `x'`-event lies
inside an `x`-event. -/
@[tmio T, powerlib_foundation] theorem exists_event_superset {m : ℕ} {x x' : ℕ → Prop}
    {t : ℕ → ℝ} {S : Set ℝ} (hx : ∀ k, x' k → x k) (hS : IsUpperSet S) (ht : TimesMono m t)
    {e' : ℕ × ℕ} (he' : e' ∈ events m x' t S) :
    ∃ e ∈ events m x t S, e.1 ≤ e'.1 ∧ e'.2 ≤ e.2 := by
  obtain ⟨henv', hS'⟩ := mem_events.mp he'
  obtain ⟨i, j, henv, hi, hj⟩ := henv'.exists_superset hx
  refine ⟨(i, j), mem_events.mpr ⟨henv, hS ?_ hS'⟩, hi, hj⟩
  simp only [duration]
  linarith [ht _ _ hj henv.2.1, ht _ _ hi (henv'.1.trans_lt henv'.2.1)]

/-- The total exceedance time is monotone in the pattern: removing exceedances (raising the
threshold, excluding periods) never increases it. -/
@[tmio T, powerlib_foundation] theorem eventTime_mono {m : ℕ} {x x' : ℕ → Prop} {t : ℕ → ℝ}
    {S : Set ℝ} (hx : ∀ k, x' k → x k) (hS : IsUpperSet S) (ht : TimesMono m t) :
    eventTime m x' t S ≤ eventTime m x t S := by
  rw [eventTime_eq_sum_links, eventTime_eq_sum_links]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun k hk _ => ?_
  · intro k hk
    obtain ⟨e', he', hk'⟩ := mem_biUnion.mp hk
    obtain ⟨e, he, h1, h2⟩ := exists_event_superset hx hS ht he'
    rw [mem_Ico] at hk'
    exact mem_biUnion.mpr ⟨e, he, mem_Ico.mpr ⟨h1.trans hk'.1, hk'.2.trans_le h2⟩⟩
  · obtain ⟨e, he, hk'⟩ := mem_biUnion.mp hk
    rw [mem_Ico] at hk'
    exact sub_nonneg.mpr (ht _ _ (Nat.le_succ k) (by have := (mem_events.mp he).1.2.1; omega))

/-- A pattern whose `x`-events are all absent has no `x'`-event for any smaller pattern. -/
@[tmio T, powerlib_foundation] theorem events_eq_empty_of_le {m : ℕ} {x x' : ℕ → Prop}
    {t : ℕ → ℝ} {S : Set ℝ} (hx : ∀ k, x' k → x k) (hS : IsUpperSet S) (ht : TimesMono m t)
    (h : events m x t S = ∅) : events m x' t S = ∅ := by
  refine eq_empty_of_forall_notMem fun e' he' => ?_
  obtain ⟨e, he, -⟩ := exists_event_superset hx hS ht he'
  simp [h] at he

/-- Every envelope duration bound passes to a smaller pattern. -/
@[tmio T, powerlib_foundation] theorem duration_le_of_le {m : ℕ} {x x' : ℕ → Prop}
    {t : ℕ → ℝ} (hx : ∀ k, x' k → x k) (ht : TimesMono m t) {b : ℝ}
    (h : ∀ e ∈ envelopes m x, duration t e ≤ b) : ∀ e ∈ envelopes m x', duration t e ≤ b := by
  intro e' he'
  have he'' : e' ∈ events m x' t Set.univ := mem_events.mpr ⟨mem_envelopes.mp he', trivial⟩
  obtain ⟨e, he, h1, h2⟩ := exists_event_superset hx isUpperSet_univ ht he''
  have henv' := mem_envelopes.mp he'
  have := h e (mem_envelopes.mpr (mem_events.mp he).1)
  simp only [duration] at this ⊢
  linarith [ht _ _ h2 (mem_events.mp he).1.2.1, ht _ _ h1 (henv'.1.trans_lt henv'.2.1)]

/-- Late-peak bounds pass to a smaller pattern: if, in every `x`-envelope, the peaks at least
`τ` after its start are bounded by `c`, the same holds in every `x'`-envelope (whose start is
not earlier). -/
@[tmio T, powerlib_foundation] theorem late_peaks_of_le {m : ℕ} {x x' : ℕ → Prop}
    {t a : ℕ → ℝ} (hx : ∀ k, x' k → x k) (ht : TimesMono m t) {τ c : ℝ}
    (h : ∀ e ∈ envelopes m x, ∀ k, e.1 ≤ k → k ≤ e.2 → t e.1 + τ ≤ t k → a k ≤ c) :
    ∀ e ∈ envelopes m x', ∀ k, e.1 ≤ k → k ≤ e.2 → t e.1 + τ ≤ t k → a k ≤ c := by
  intro e' he' k hk1 hk2 hk
  obtain ⟨i, j, henv, hi, hj⟩ := (mem_envelopes.mp he').exists_superset hx
  have henv' := mem_envelopes.mp he'
  refine h (i, j) (mem_envelopes.mpr henv) k (hi.trans hk1) (hk2.trans hj) ?_
  have := ht i e'.1 hi (henv'.1.trans_lt henv'.2.1)
  simp only
  linarith

/-- Event counts and times are monotone in the duration class: a longer minimum duration
(`S' ⊆ S`) counts fewer events and less time. -/
@[tmio T, powerlib_foundation] theorem eventCount_mono_class {m : ℕ} {x : ℕ → Prop}
    {t : ℕ → ℝ} {S S' : Set ℝ} (hS : S' ⊆ S) : eventCount m x t S' ≤ eventCount m x t S := by
  refine card_le_card fun e he => ?_
  obtain ⟨h1, h2⟩ := mem_events.mp he
  exact mem_events.mpr ⟨h1, hS h2⟩

@[tmio T, powerlib_foundation] theorem eventTime_mono_class {m : ℕ} {x : ℕ → Prop}
    {t : ℕ → ℝ} {S S' : Set ℝ} (hS : S' ⊆ S) (ht : TimesMono m t) :
    eventTime m x t S' ≤ eventTime m x t S := by
  refine sum_le_sum_of_subset_of_nonneg (fun e he => ?_) fun e he _ => ?_
  · obtain ⟨h1, h2⟩ := mem_events.mp he
    exact mem_events.mpr ⟨h1, hS h2⟩
  · exact (mem_events.mp he).1.duration_nonneg ht

/-- Event counts are not monotone in the pattern: removing an exceedance in the middle of an
envelope splits it. Five peaks at the times `k D` (`D > 0`), events longer than `d < D`: with all
five peaks exceeding there is one event, `(0, 4)`; without the middle peak there are two,
`(0, 1)` and `(3, 4)`. -/
@[tmio T, powerlib_foundation] theorem eventCount_split {D d : ℝ} (hD : 0 < D) (hd : d < D) :
    eventCount 5 (fun _ => True) (fun k => k * D) (Set.Ioi d) = 1 ∧
      eventCount 5 (fun k => k ≠ 2) (fun k => k * D) (Set.Ioi d) = 2 := by
  have h1 : events 5 (fun _ => True) (fun k => k * D) (Set.Ioi d) = {(0, 4)} := by
    ext ⟨i, j⟩
    simp only [mem_events, mem_singleton, Prod.mk.injEq, IsEnvelope, duration, Set.mem_Ioi]
    constructor
    · rintro ⟨⟨hij, hj, -, hi, hj'⟩, -⟩
      exact ⟨by by_contra h; exact hi (i - 1) (by omega) trivial, by
        by_contra h; exact hj' (by omega) trivial⟩
    · rintro ⟨rfl, rfl⟩
      refine ⟨⟨by omega, by omega, fun _ _ _ => trivial, fun k hk => by omega,
        fun h => by omega⟩, ?_⟩
      push_cast; nlinarith
  have h2 : events 5 (fun k => k ≠ 2) (fun k => k * D) (Set.Ioi d) = {(0, 1), (3, 4)} := by
    ext ⟨i, j⟩
    simp only [mem_events, mem_insert, mem_singleton, Prod.mk.injEq, IsEnvelope, duration,
      Set.mem_Ioi, not_not]
    constructor
    · rintro ⟨⟨hij, hj, hrun, hi, hj'⟩, -⟩
      have h2 : ¬ (i ≤ 2 ∧ 2 ≤ j) := fun h => hrun 2 h.1 h.2 rfl
      have hi' : i = 0 ∨ i = 3 := by
        rcases Nat.eq_zero_or_pos i with h | h
        · exact Or.inl h
        · exact Or.inr (by have := hi (i - 1) (by omega); omega)
      omega
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · refine ⟨⟨by omega, by omega, fun k h1 h2 => by omega, fun k hk => by omega,
          fun _ => by omega⟩, ?_⟩
        push_cast; linarith
      · refine ⟨⟨by omega, by omega, fun k h1 h2 => by omega, fun k hk => by omega,
          fun h => by omega⟩, ?_⟩
        push_cast; linarith
  refine ⟨by rw [eventCount, h1, card_singleton], ?_⟩
  rw [eventCount, h2]
  rfl

/-- A block of `L ≥ 1` consecutive exceeding peaks `s, …, s + L − 1` (and no other exceedance)
is one event when its duration lies in `S`. -/
@[tmio T, powerlib_foundation] theorem eventCount_block {m s L : ℕ} {x : ℕ → Prop} {t : ℕ → ℝ}
    {S : Set ℝ} (hL : 1 ≤ L) (hm : s + L ≤ m) (hx : ∀ k < m, x k ↔ s ≤ k ∧ k < s + L)
    (hS : duration t (s, s + L - 1) ∈ S) : eventCount m x t S = 1 := by
  rw [eventCount, card_eq_one]
  refine ⟨(s, s + L - 1), eq_singleton_iff_unique_mem.mpr ⟨mem_events.mpr ⟨⟨by omega, by omega,
    fun k h1 h2 => (hx k (by omega)).mpr ⟨by omega, by omega⟩, fun k hk hxk => ?_,
    fun h hxk => ?_⟩, hS⟩, fun e he => ?_⟩⟩
  · have := ((hx k (by omega)).mp hxk).1; omega
  · have := ((hx _ h).mp hxk).2; omega
  · obtain ⟨⟨hij, hjm, hrun, hi, hj⟩, -⟩ := mem_events.mp he
    have h1 := (hx e.1 (by omega)).mp (hrun e.1 le_rfl hij)
    have h2 := (hx e.2 hjm).mp (hrun e.2 hij le_rfl)
    have hs : e.1 = s := by
      by_contra hne
      exact hi (e.1 - 1) (by omega) ((hx _ (by omega)).mpr ⟨by omega, by omega⟩)
    have he2 : e.2 = s + L - 1 := by
      by_contra hne
      exact hj (by omega) ((hx _ (by omega)).mpr ⟨by omega, by omega⟩)
    exact Prod.ext hs he2

/-- A block of `3c + 2` peaks `s, …` in which every third peak (`k − s ≡ 2 mod 3`) does not exceed
splits into the `c + 1` events `(s + 3i, s + 3i + 1)`, `i ≤ c`, when each pair's duration lies
in `S`. -/
@[tmio T, powerlib_foundation] theorem eventCount_comb {m s c : ℕ} {x : ℕ → Prop} {t : ℕ → ℝ}
    {S : Set ℝ} (hm : s + 3 * c + 2 ≤ m)
    (hx : ∀ k < m, x k ↔ s ≤ k ∧ k < s + 3 * c + 2 ∧ (k - s) % 3 ≠ 2)
    (hS : ∀ i ≤ c, duration t (s + 3 * i, s + 3 * i + 1) ∈ S) : eventCount m x t S = c + 1 := by
  have hev : events m x t S = (range (c + 1)).image fun i => (s + 3 * i, s + 3 * i + 1) := by
    ext ⟨i, j⟩
    rw [mem_events, mem_image]
    constructor
    · rintro ⟨⟨hij, hjm, hrun, hi, hj⟩, -⟩
      have h1 := (hx i (by omega)).mp (hrun i le_rfl hij)
      have h0 : (i - s) % 3 = 0 := by
        by_contra hne
        exact hi (i - 1) (by omega) ((hx _ (by omega)).mpr ⟨by omega, by omega, by omega⟩)
      have hj1 : j = i + 1 := by
        rcases lt_trichotomy j (i + 1) with hlt | heq | hgt
        · exact absurd ((hx (j + 1) (by omega)).mpr ⟨by omega, by omega, by omega⟩)
            (hj (by omega))
        · exact heq
        · exact absurd ((hx (i + 2) (by omega)).mp (hrun (i + 2) (by omega) (by omega))).2.2
            (by omega)
      refine ⟨(i - s) / 3, mem_range.mpr (by omega), ?_⟩
      simp only [Prod.mk.injEq]
      omega
    · rintro ⟨i', hi', he⟩
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [mem_range] at hi'
      refine ⟨⟨by omega, by omega, fun k h1 h2 => (hx k (by omega)).mpr ⟨by omega, by omega,
        by omega⟩, fun k hk hxk => ?_, fun h hxk => ?_⟩, hS i' (by omega)⟩
      · have := (hx k (by omega)).mp hxk; omega
      · have := (hx _ h).mp hxk; omega
  rw [eventCount, hev, card_image_of_injective _ fun a b hab => by
    simp only [Prod.mk.injEq] at hab; omega, card_range]

/-- Exceedances confined to a time window of length `T` give envelopes shorter than `T`. -/
@[tmio T, powerlib_foundation] theorem duration_lt_of_window {m : ℕ} {x : ℕ → Prop}
    {t : ℕ → ℝ} {u T : ℝ} (h : ∀ k < m, x k → u ≤ t k ∧ t k < u + T) :
    ∀ e ∈ envelopes m x, duration t e < T := by
  intro e he
  obtain ⟨hij, hjm, hrun, -, -⟩ := mem_envelopes.mp he
  have h1 := h e.1 (hij.trans_lt hjm) (hrun e.1 le_rfl hij)
  have h2 := h e.2 hjm (hrun e.2 hij le_rfl)
  simp only [duration]
  linarith

/-! ## Exceedance time of exponentially bounded oscillations -/

/-- An exponential envelope `A e^{−σ t}` (`A, σ > 0`) exceeds the level `a > 0` exactly before
`log (A / a) / σ`. -/
@[tmio T, powerlib_foundation] theorem lt_mul_exp_neg_iff {a A σ t : ℝ} (ha : 0 < a) (hA : 0 < A)
    (hσ : 0 < σ) : a < A * Real.exp (-(σ * t)) ↔ t < Real.log (A / a) / σ := by
  rw [← Real.log_lt_log_iff ha (by positivity), Real.log_mul hA.ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_div hA.ne' ha.ne', lt_div_iff₀ hσ]
  constructor <;> intro h <;> linarith

/-- A signal bounded by `M e^{−r t}` (`r > 0`) exceeds `a > 0` only before `log (M / a) / r`. -/
@[tmio T, powerlib_foundation] theorem lt_of_abs_le_mul_exp {y M a r t : ℝ} (ha : 0 < a)
    (hr : 0 < r) (hy : |y| ≤ M * Real.exp (-(r * t))) (hex : a < |y|) :
    t < Real.log (M / a) / r := by
  have hM : 0 < M := by
    by_contra h
    have : M * Real.exp (-(r * t)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h)
      (Real.exp_pos _).le
    linarith
  exact (lt_mul_exp_neg_iff ha hM hr).mp (hex.trans_le hy)

/-- Envelopes of exponentially decaying exceedances are short: if the exceeding peaks occur after
`t₀`, exceed a level `ℓ > 0` and are bounded by `M e^{−r (t − t₀)}` (`r > 0`), every envelope lasts
less than `log (M / ℓ) / r`. -/
@[tmio T, powerlib_foundation] theorem duration_lt_of_exp_bound {m : ℕ} {x : ℕ → Prop}
    {t a : ℕ → ℝ} {t₀ ℓ M r : ℝ} (hℓ : 0 < ℓ) (hr : 0 < r)
    (hx : ∀ k < m, x k → t₀ ≤ t k ∧ ℓ < a k)
    (hM : ∀ k < m, x k → a k ≤ M * Real.exp (-(r * (t k - t₀)))) :
    ∀ e ∈ envelopes m x, duration t e < Real.log (M / ℓ) / r := by
  refine duration_lt_of_window (u := t₀) fun k hk hxk => ⟨(hx k hk hxk).1, ?_⟩
  have h1 := (hx k hk hxk).2
  have h2 := lt_of_abs_le_mul_exp (y := a k) hℓ hr
    (by rw [abs_of_pos (hℓ.trans h1)]; exact hM k hk hxk) (by rw [abs_of_pos (hℓ.trans h1)]; exact h1)
  linarith

/-- The exceedance of the envelope `A₀ e^{−σ t}` above `a` (`0 < a < A₀`, `σ > 0`) lasts at most
`b > 0` exactly when `σ ≥ log (A₀ / a) / b`. -/
@[tmio T, powerlib_foundation] theorem forall_exceed_le_iff {A₀ a σ b : ℝ} (ha : 0 < a)
    (hA : a < A₀) (hσ : 0 < σ) (hb : 0 < b) :
    (∀ t, 0 ≤ t → a < A₀ * Real.exp (-(σ * t)) → t ≤ b) ↔ Real.log (A₀ / a) / b ≤ σ := by
  have hA0 : 0 < A₀ := ha.trans hA
  have hlog : 0 < Real.log (A₀ / a) := Real.log_pos ((one_lt_div ha).mpr hA)
  rw [div_le_iff₀ hb]
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hT : b < Real.log (A₀ / a) / σ := by rw [lt_div_iff₀ hσ]; linarith
    have h1 := h ((b + Real.log (A₀ / a) / σ) / 2) (by positivity)
      ((lt_mul_exp_neg_iff ha hA0 hσ).mpr (by linarith))
    linarith
  · intro h t _ ht
    have := (lt_mul_exp_neg_iff ha hA0 hσ).mp ht
    rw [lt_div_iff₀ hσ] at this
    nlinarith

/-- The envelope `A₀ e^{−σ τ}` is at most `c > 0` at the time `τ > 0` exactly when
`σ ≥ log (A₀ / c) / τ`. -/
@[tmio T, powerlib_foundation] theorem mul_exp_le_iff {A₀ c σ τ : ℝ} (hc : 0 < c) (hA : 0 < A₀)
    (hσ : 0 < σ) (hτ : 0 < τ) :
    A₀ * Real.exp (-(σ * τ)) ≤ c ↔ Real.log (A₀ / c) / τ ≤ σ := by
  rw [← not_lt, lt_mul_exp_neg_iff hc hA hσ, not_lt, div_le_iff₀ hσ, div_le_iff₀ hτ, mul_comm]

/-- Two decay conditions compared: if `b = 2 τ` and `A₀ a ≤ c²`, the rate needed for an exceedance
of `a` to last at most `b` also brings the envelope below `c` by the time `τ`. -/
@[tmio T, powerlib_foundation] theorem mul_exp_le_of_rate {A₀ a c σ b τ : ℝ} (ha : 0 < a)
    (hA : a < A₀) (hσ : 0 < σ) (hc : 0 < c) (hτ : 0 < τ) (hb : b = 2 * τ)
    (hprod : A₀ * a ≤ c ^ 2) (h : Real.log (A₀ / a) / b ≤ σ) :
    A₀ * Real.exp (-(σ * τ)) ≤ c := by
  have hA0 : 0 < A₀ := ha.trans hA
  rw [mul_exp_le_iff hc hA0 hσ hτ]
  refine le_trans ?_ h
  rw [hb, div_le_div_iff₀ hτ (by positivity)]
  have hsq : 2 * Real.log (A₀ / c) ≤ Real.log (A₀ / a) := by
    rw [← Real.log_rpow (by positivity), Real.rpow_two]
    refine Real.log_le_log (by positivity) ?_
    rw [div_pow, div_le_div_iff₀ (by positivity) ha]
    nlinarith
  nlinarith

section Filter

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- Output bound of a Hurwitz filter: there are `K, r > 0` such that for every solution of
`ė = A e` and every output vector `c`, `|⟪c, e(t)⟫| ≤ K ‖c‖ ‖e 0‖ e^{−r t}` for `t ≥ 0`
(`LTI.exists_global_bound_of_isHurwitz` and Cauchy–Schwarz). -/
@[tmio T, powerlib_foundation] theorem exists_output_bound {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : LinearSystems.IsHurwitz A) :
    ∃ K > 0, ∃ r > 0, ∀ e : ℝ → ℝⁿ, (∀ t, HasDerivAt e (Linear.op A (e t)) t) →
      ∀ (c : ℝⁿ) (t : ℝ), 0 ≤ t →
        |inner ℝ c (e t)| ≤ K * ‖c‖ * ‖e 0‖ * Real.exp (-(r * t)) := by
  obtain ⟨K, hK, r, hr, hb⟩ := LTI.exists_global_bound_of_isHurwitz hA
  refine ⟨K, hK, r, hr, fun e he c t ht => ?_⟩
  calc |inner ℝ c (e t)| ≤ ‖c‖ * ‖e t‖ := abs_real_inner_le_norm c (e t)
    _ ≤ ‖c‖ * (K * Real.exp (-(r * t)) * ‖e 0‖) :=
        mul_le_mul_of_nonneg_left (hb e he t ht) (norm_nonneg c)
    _ = K * ‖c‖ * ‖e 0‖ * Real.exp (-(r * t)) := by ring

/-- A Hurwitz filter forgets a step: the output `⟪c, e(t)⟫` of the deviation `e` of any solution
of `ė = A e` from its new equilibrium exceeds a level `a > 0` only before
`log (K ‖c‖ ‖e 0‖ / a) / r`. For a filter with zero DC gain (a band-pass) the equilibrium output
after a set-point step is `0`, so this bounds the duration of the transient exceedance caused by
the step. -/
@[tmio T, powerlib_foundation] theorem exists_exceedance_time_bound {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : LinearSystems.IsHurwitz A) :
    ∃ K > 0, ∃ r > 0, ∀ e : ℝ → ℝⁿ, (∀ t, HasDerivAt e (Linear.op A (e t)) t) →
      ∀ (c : ℝⁿ) (a t : ℝ), 0 < a → 0 ≤ t → a < |inner ℝ c (e t)| →
        t < Real.log (K * ‖c‖ * ‖e 0‖ / a) / r := by
  obtain ⟨K, hK, r, hr, hb⟩ := exists_output_bound hA
  exact ⟨K, hK, r, hr, fun e he c a t ha ht hex =>
    lt_of_abs_le_mul_exp ha hr (hb e he c t ht) hex⟩

end Filter

/-! ## Frequency blindness of the envelope detector (§3.7) -/

/-- If every peak of a record exceeds, its only envelope runs from the first to the last peak,
whatever the spacing (hence the frequency) of the peaks. -/
@[tmio T, powerlib_foundation] theorem envelopes_eq_singleton {m : ℕ} {x : ℕ → Prop} (hm : 0 < m)
    (h : ∀ k < m, x k) : envelopes m x = {(0, m - 1)} := by
  ext ⟨i, j⟩
  rw [mem_envelopes, mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨hij, hjm, -, hi, hj⟩
    exact ⟨by by_contra hne; exact hi (i - 1) (by omega) (h _ (by omega)), by
      by_contra hne; exact hj (by omega) (h _ (by omega))⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨Nat.zero_le _, by omega, fun k _ hk => h k (by omega), fun k hk => by omega,
      fun hj => by omega⟩

/-- Crest record of the tone `A cos(ω t)` (`ω > 0`) over `K` half-periods: the `K + 1` crests of
`|A cos(ω t)|` at the times `k π / ω`, all of height `|A|`. For every level `ℓ < |A|` the detector
reports the single envelope from `0` to `K π / ω` with peak `|A|`: two tones whose windows
`K π / ω` agree (e.g. `0.2 Hz` and `1 Hz` over `100 s`, `K = 40` and `K = 200`) give identical
detector output. -/
@[tmio T, powerlib_foundation] theorem tone_crests_envelope {A ω ℓ : ℝ} (hω : 0 < ω) (K : ℕ)
    (hℓ : ℓ < |A|) :
    (∀ k : ℕ, |A * Real.cos (ω * (k * Real.pi / ω))| = |A|) ∧
      envelopes (K + 1) (fun k => ℓ < |A * Real.cos (ω * (k * Real.pi / ω))|) = {(0, K)} ∧
      duration (fun k : ℕ => k * Real.pi / ω) (0, K) = K * Real.pi / ω := by
  have hc : ∀ k : ℕ, |A * Real.cos (ω * (k * Real.pi / ω))| = |A| := fun k => by
    rw [show ω * (k * Real.pi / ω) = k * Real.pi by field_simp, Real.cos_nat_mul_pi, abs_mul,
      abs_pow, abs_neg, abs_one, one_pow, mul_one]
  refine ⟨hc, ?_, by simp [duration]⟩
  rw [envelopes_eq_singleton (Nat.succ_pos K) fun k _ => (hc k).symm ▸ hℓ]
  rfl

/-- Squared gain `|H(jω)|²` of the lightly damped mode `H(s) = ω_n² / (s² + 2ζω_n s + ω_n²)`. -/
def modeGainSq (ζ ωn ω : ℝ) : ℝ := ωn ^ 4 / ((ωn ^ 2 - ω ^ 2) ^ 2 + (2 * ζ * ωn * ω) ^ 2)

@[tmio T, powerlib_foundation] theorem modeGainSq_eq_normSq (ζ ωn ω : ℝ) :
    modeGainSq ζ ωn ω =
      ‖(ωn ^ 2 : ℂ) / ((ω * Complex.I) ^ 2 + 2 * ζ * ωn * (ω * Complex.I) + ωn ^ 2)‖ ^ 2 := by
  have hden : (ω * Complex.I) ^ 2 + 2 * ζ * ωn * (ω * Complex.I) + ωn ^ 2 =
      ⟨ωn ^ 2 - ω ^ 2, 2 * ζ * ωn * ω⟩ := by
    apply Complex.ext
    · simp [pow_two]; ring
    · simp [pow_two]
  rw [norm_div, hden, div_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_mk, modeGainSq]
  norm_cast
  rw [Complex.normSq_mk]
  ring

/-- A tone at the mode frequency is amplified by `1/(2ζ)`, strictly more than a tone of the same
amplitude above it: equal detector output, different system risk. -/
@[tmio T, powerlib_foundation] theorem modeGainSq_lt_resonance {ζ ωn ω : ℝ} (hζ : 0 < ζ)
    (hωn : 0 < ωn) (hω : ωn < ω) :
    modeGainSq ζ ωn ωn = 1 / (4 * ζ ^ 2) ∧ modeGainSq ζ ωn ω < modeGainSq ζ ωn ωn := by
  have h4 : modeGainSq ζ ωn ωn = 1 / (4 * ζ ^ 2) := by
    rw [modeGainSq]
    field_simp
    ring
  refine ⟨h4, ?_⟩
  rw [modeGainSq, modeGainSq, sub_self]
  have hω2 : ωn ^ 2 < ω ^ 2 := by nlinarith
  apply div_lt_div_of_pos_left (by positivity) (by positivity)
  nlinarith [sq_nonneg (ωn ^ 2 - ω ^ 2), mul_pos (mul_pos hζ hζ) (mul_pos hωn hωn)]

/-! ## Aggregated records (§4.1, aggregation of sites) -/

/-- A limit proportional to a capacity is preserved by aggregation: if every component satisfies
`|y_i| ≤ α P_i`, the aggregate satisfies `|Σ y_i| ≤ α Σ P_i`. -/
@[tmio T, powerlib_foundation] theorem abs_sum_le_mul_sum {ι : Type*} (s : Finset ι)
    {y P : ι → ℝ} {α : ℝ} (h : ∀ i ∈ s, |y i| ≤ α * P i) :
    |∑ i ∈ s, y i| ≤ α * ∑ i ∈ s, P i := by
  rw [mul_sum]
  exact (abs_sum_le_sum_abs y s).trans (sum_le_sum h)

/-- Mediant inequality: the aggregate relative amplitude `Σ |y_i| / Σ P_i` is at most the largest
component ratio `|y_i| / P_i` (`P_i > 0`). -/
@[tmio T, powerlib_foundation] theorem exists_sum_div_le {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {y P : ι → ℝ} (hP : ∀ i ∈ s, 0 < P i) :
    ∃ i ∈ s, (∑ j ∈ s, |y j|) / (∑ j ∈ s, P j) ≤ |y i| / P i := by
  by_contra hno
  simp only [not_exists, not_and, not_le] at hno
  have hpos : 0 < ∑ j ∈ s, P j := sum_pos hP hs
  have hlt : ∑ j ∈ s, |y j| < ∑ j ∈ s, ((∑ j ∈ s, |y j|) / (∑ j ∈ s, P j)) * P j :=
    sum_lt_sum_of_nonempty hs fun i hi => by
      have := hno i hi
      rwa [div_lt_iff₀ (hP i hi)] at this
  rw [← mul_sum, div_mul_cancel₀ _ hpos.ne'] at hlt
  exact lt_irrefl _ hlt

/-! ## Nearest-rank quantiles of hourly counts (§4.1, clause c(ii)) -/

section Quantile

variable {ι : Type*} [Fintype ι]

/-- Rank `⌈q H⌉` of the nearest-rank `q`-quantile of `H` values. -/
def quantileRank (q : ℝ) (H : ℕ) : ℕ := ⌈q * H⌉₊

open Classical in
/-- Number of the counts `n h` that are `≤ v`. -/
def countLe (n : ι → ℕ) (v : ℕ) : ℕ := (univ.filter fun h => n h ≤ v).card

/-- Nearest-rank `q`-quantile of the counts `n : ι → ℕ` (`H = card ι` values): the least `v`
such that at least `⌈q H⌉` of the counts are `≤ v`; for `0 < q ≤ 1` it is the `⌈q H⌉`-th
smallest count (`nearestRank_spec`). -/
def nearestRank (q : ℝ) (n : ι → ℕ) : ℕ :=
  sInf {v | quantileRank q (Fintype.card ι) ≤ countLe n v}

@[tmio T, powerlib_foundation] theorem countLe_mono (n : ι → ℕ) {v w : ℕ} (h : v ≤ w) :
    countLe n v ≤ countLe n w := by
  classical
  exact card_le_card fun x hx => by
    simp only [mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.trans h⟩

@[tmio T, powerlib_foundation] theorem quantileRank_le {q : ℝ} (hq : q ≤ 1) (H : ℕ) :
    quantileRank q H ≤ H :=
  Nat.ceil_le.mpr (mul_le_of_le_one_left (Nat.cast_nonneg H) hq)

open Classical in
@[tmio T, powerlib_foundation] theorem countLe_add_card_gt (n : ι → ℕ) (v : ℕ) :
    countLe n v + (univ.filter fun h => v < n h).card = Fintype.card ι := by
  rw [countLe, ← card_univ]
  simpa only [not_le] using card_filter_add_card_filter_not (s := univ) (fun h => n h ≤ v)

/-- For `q ≤ 1` the nearest-rank `q`-quantile is `≤ c` exactly when at least `⌈q H⌉` counts are
`≤ c`. -/
@[tmio T, powerlib_foundation] theorem nearestRank_le_iff_rank {q : ℝ} (hq : q ≤ 1)
    (n : ι → ℕ) (c : ℕ) :
    nearestRank q n ≤ c ↔ quantileRank q (Fintype.card ι) ≤ countLe n c := by
  classical
  have hne : {v | quantileRank q (Fintype.card ι) ≤ countLe n v}.Nonempty := by
    refine ⟨univ.sup n, ?_⟩
    show _ ≤ countLe n _
    have h := countLe_add_card_gt n (univ.sup n)
    have h0 : (univ.filter fun h => univ.sup n < n h).card = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      exact fun h _ => not_lt.mpr (le_sup (mem_univ h))
    have hr := quantileRank_le hq (Fintype.card ι)
    omega
  exact ⟨fun h => (Nat.sInf_mem hne).trans (countLe_mono n h), fun h => Nat.sInf_le h⟩

open Classical in
/-- Counting form of a quantile bound: for `q ≤ 1` the nearest-rank `q`-quantile of `H` counts
is `≤ c` exactly when at most `H − ⌈q H⌉` counts exceed `c`. -/
@[tmio T, powerlib_foundation] theorem nearestRank_le_iff {q : ℝ} (hq : q ≤ 1) (n : ι → ℕ)
    (c : ℕ) :
    nearestRank q n ≤ c ↔
      (univ.filter fun h => c < n h).card ≤ Fintype.card ι - quantileRank q (Fintype.card ι) := by
  have hr := quantileRank_le hq (Fintype.card ι)
  have h2 := countLe_add_card_gt n c
  rw [nearestRank_le_iff_rank hq]
  omega

open Classical in
/-- The nearest-rank quantile is the `⌈q H⌉`-th smallest count: for `0 < q ≤ 1` and `H > 0` it is
one of the counts, fewer than `⌈q H⌉` counts lie below it and at least `⌈q H⌉` are `≤` it. -/
@[tmio T, powerlib_foundation] theorem nearestRank_spec {q : ℝ} (hq0 : 0 < q) (hq : q ≤ 1)
    (n : ι → ℕ) (hH : 0 < Fintype.card ι) :
    (∃ h, n h = nearestRank q n) ∧
      (univ.filter fun h => n h < nearestRank q n).card < quantileRank q (Fintype.card ι) ∧
      quantileRank q (Fintype.card ι) ≤ countLe n (nearestRank q n) := by
  have hr1 : 1 ≤ quantileRank q (Fintype.card ι) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  have hle : nearestRank q n ≤ univ.sup n := by
    rw [nearestRank_le_iff hq]
    have : (univ.filter fun h => univ.sup n < n h).card = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      exact fun h _ => not_lt.mpr (le_sup (mem_univ h))
    omega
  have hmem : quantileRank q (Fintype.card ι) ≤ countLe n (nearestRank q n) :=
    (nearestRank_le_iff_rank hq n _).mp le_rfl
  have hbelow : (univ.filter fun h => n h < nearestRank q n).card <
      quantileRank q (Fintype.card ι) := by
    rcases Nat.eq_zero_or_pos (nearestRank q n) with h0 | hpos
    · rw [h0]; simp; omega
    · have hnot : ¬ quantileRank q (Fintype.card ι) ≤ countLe n (nearestRank q n - 1) :=
        fun h => by
          have h' : nearestRank q n ≤ nearestRank q n - 1 := Nat.sInf_le h
          omega
      have heq : (univ.filter fun h => n h < nearestRank q n) =
          univ.filter fun h => n h ≤ nearestRank q n - 1 :=
        filter_congr fun h _ => by omega
      rw [heq]
      exact not_le.mp hnot
  refine ⟨?_, hbelow, hmem⟩
  by_contra hno
  simp only [not_exists] at hno
  have heq : (univ.filter fun h => n h ≤ nearestRank q n) =
      univ.filter fun h => n h < nearestRank q n :=
    filter_congr fun h _ => ⟨fun h' => lt_of_le_of_ne h' (hno h), le_of_lt⟩
  rw [countLe, heq] at hmem
  omega

/-- Hours without counts have quantile `0`. -/
@[tmio T, powerlib_foundation] theorem nearestRank_zero (q : ℝ) : nearestRank q (fun _ : ι => 0) = 0 := by
  classical
  refine Nat.sInf_eq_zero.mpr ?_
  by_cases h : quantileRank q (Fintype.card ι) ≤ countLe (fun _ : ι => 0) 0
  · exact Or.inl h
  · refine Or.inr (Set.eq_empty_of_forall_notMem fun v hv => h ?_)
    have : countLe (fun _ : ι => 0) v = countLe (fun _ : ι => 0) 0 := by
      simp [countLe]
    exact this ▸ hv

/-- The quantile is monotone: smaller counts and a lower level `q' ≤ q` give a smaller
quantile. -/
@[tmio T, powerlib_foundation] theorem nearestRank_mono {q q' : ℝ} (hq : q ≤ 1) (hq' : q' ≤ q)
    {n n' : ι → ℕ} (hn : ∀ h, n' h ≤ n h) : nearestRank q' n' ≤ nearestRank q n := by
  have hmem : quantileRank q (Fintype.card ι) ≤ countLe n (nearestRank q n) :=
    (nearestRank_le_iff_rank hq n _).mp le_rfl
  refine Nat.sInf_le (le_trans ?_ (hmem.trans ?_))
  · exact Nat.ceil_mono (mul_le_mul_of_nonneg_right hq' (Nat.cast_nonneg _))
  · classical
    exact card_le_card fun x hx => by
      simp only [mem_filter] at hx ⊢
      exact ⟨hx.1, (hn x).trans hx.2⟩

/-- `H − ⌈q H⌉ = ⌊(1 − q) H⌋` for `0 ≤ q ≤ 1`: the number of hours allowed above the count
limit. -/
@[tmio T, powerlib_foundation] theorem sub_quantileRank {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1)
    (H : ℕ) : H - quantileRank q H = ⌊(1 - q) * H⌋₊ := by
  have hF : ⌊(1 - q) * H⌋₊ ≤ H :=
    Nat.floor_le_of_le (mul_le_of_le_one_left (Nat.cast_nonneg H) (by linarith))
  have h1 : quantileRank q H ≤ H - ⌊(1 - q) * H⌋₊ := by
    refine Nat.ceil_le.mpr ?_
    rw [Nat.cast_sub hF]
    have := Nat.floor_le (show 0 ≤ (1 - q) * H by
      exact mul_nonneg (by linarith) (Nat.cast_nonneg H))
    linarith
  have h2 : H - ⌊(1 - q) * H⌋₊ ≤ quantileRank q H := by
    by_contra hlt
    have hle : quantileRank q H + 1 ≤ H - ⌊(1 - q) * H⌋₊ := by omega
    have hc := Nat.le_ceil (q * H)
    have : ⌊(1 - q) * H⌋₊ + 1 ≤ ⌊(1 - q) * H⌋₊ := by
      refine Nat.le_floor ?_
      have h3 : ((quantileRank q H + 1 : ℕ) : ℝ) ≤ ((H - ⌊(1 - q) * H⌋₊ : ℕ) : ℝ) :=
        Nat.cast_le.mpr hle
      rw [Nat.cast_sub hF] at h3
      push_cast at h3 ⊢
      unfold quantileRank at h3
      linarith
    omega
  omega

open Classical in
/-- Clause c(ii) over one week: the 95th percentile (nearest rank) of 168 hourly counts is `≤ c`
exactly when at most `⌊0.05 · 168⌋ = 8` hours have more than `c` exceedances (the report's
"168 · 0.05 ≈ 8" is exact as a floor). -/
@[tmio T, powerlib_foundation] theorem nearestRank_week_le_iff (n : Fin 168 → ℕ) (c : ℕ) :
    nearestRank (95 / 100) n ≤ c ↔ (univ.filter fun h => c < n h).card ≤ 8 := by
  rw [nearestRank_le_iff (by norm_num), Fintype.card_fin,
    sub_quantileRank (by norm_num) (by norm_num)]
  have : ⌊(1 - 95 / 100 : ℝ) * (168 : ℕ)⌋₊ = 8 := by
    rw [Nat.floor_eq_iff (by norm_num)]
    norm_num
  rw [this]

end Quantile

end powerlib.Signal
