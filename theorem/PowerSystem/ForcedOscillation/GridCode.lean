import theorem.Signal.Detection

/-! # Draft NC RfG 2.0 forced-oscillation clauses on measured records

The forced-oscillation requirements of draft NC RfG 2.0, Art. 21(3) (onshore) and Art. 26(2)
(offshore), as clauses on the record the ENTSO-E/WindEurope methodology extracts from a
measurement: the continuous limit (a), temporary exceedances (b(i)–b(iii)) and exceedance
frequency (c(i), c(ii)), their logical relations, their monotonicity in the limits and the
exclusions, and their behaviour under decay, set-point steps and aggregation of sites.

Model boundary.
* A power park module of type C or D with maximum capacity `P_max ≥ 0`, measured at the agreed
  measurement point over an assessment period of `days` days starting at time `0`. The record
  (`Record`) is the output of the report's data processing and band-pass filtering: the `m` local
  maxima, in time order, of the rectified filtered active power (`Signal.IsLocalMaxAbs`), with
  times `t_k` [s] (nondecreasing), amplitudes `amp_k`, the actual production `P_actual ≥ 0` at
  the peak, and an exclusion mask (Table 2: system-support requests, operation under disturbed
  network conditions); an excluded peak is treated as compliant. `Record.ofSamples` builds the
  record from samples with period `h`.
* Clause parameters are symbolic (`Clauses`); shares are fractions of the stated power, times are
  seconds. The continuous limit at a peak is `max(max(α P_actual, β P_max), A)`
  (`ContinuousLimit.value`), covering the offshore 0.1–2 Hz form `max(a₁ P_actual, a₂ P_max)`
  and the onshore (and offshore 2–20 Hz) form `max(a₁ P_max, A)` with the absolute value `A`
  symbolic.
* Clause readings. a: no assessed peak above the continuous limit. b(i): no exceedance of
  `b₁ P_max` lasting at least `dB` during an exceedance of the continuous limit (the legal "in
  case this limit is temporarily exceeded"; `dB` is the tool's minimum duration, `0` counts all).
  b(ii): every exceedance of the continuous limit lasts at most `b₂`. b(iii): within each
  exceedance, the peaks from `t₃` after its start on are at most `b₃ P_max`. c(i): each day spends
  at most `c₁ · 86400 s` in exceedances longer than `dC`. c(ii): the nearest-rank `q`-percentile of
  the hourly numbers of exceedances longer than `dC` is at most `c₂`. Exceedances are the
  envelopes of `Signal.envelopes`; day and hour windows cut them at their boundaries.
* Excluded: the filter, the PMU and the sampling (the record is already in the clause's frequency
  band; see `theorem/Signal/Butterworth.lean`, `theorem/Signal/Sampling.lean`), measurement noise,
  the voltage and frequency range conditions other than through the mask, the frequency
  dependence of risk (§3.7, `Signal.tone_crests_envelope`), and any model of the turbine, the
  farm or the grid. The decay-rate and set-point statements assume the stated exponential bounds
  on the peaks (a damped mode, or a Hurwitz filter through `Signal.exists_output_bound`).

Source: ENTSO-E/WindEurope Technical Group on Forced Oscillations Report (2 July 2026) §2.3,
§3.3–§3.5 (Table 1), §4.1 (aggregation of sites, Site12; the 95th percentile, "168 · 0.05 ≈ 8"),
§4.2 (Table 2), §5.1 (Fig. 11), §5.4–§5.6 (Tables 3–9), §5.8, Appendix A (Table 11) and
Appendix B (Fig. 21); draft NC RfG 2.0 Art. 21(3), 26(2) as quoted there.

Results.
* Continuous limit: `ContinuousLimit`, `value`, `offshore`, `onshore`, `offshore_value`,
  `onshore_value`, `value_mono`, `value_add_le` (the limit of an aggregate is at most the sum of
  the site limits).
* Clauses and records: `Clauses`, `Clauses.Relaxes`, `Record`, `aExceeds`, `bExceeds`, `InWindow`,
  `ClauseA`, `ClauseB1`, `ClauseB2`, `ClauseB3`, `dayTime`, `ClauseC1`, `hourCount`, `ClauseC2`,
  `Compliant`; `offshoreDefault`, `offshoreLeastStrict`, `onshoreDefault` (Appendix A columns).
* §3.5: `compliant_of_clauseA` (clause a implies all the other clauses), `clauseA_ofSamples` (a
  sampled record within its limit at every assessed sample respects clause a).
* Per unit (§3.1, §5.2): `Record.perUnit`, `Clauses.perUnit`, `ContinuousLimit.value_perUnit`,
  `compliant_perUnit` (the verdict does not depend on the base when the absolute floor is
  expressed in it).
* Monotonicity (Tables 3–9, §4.2): `aExceeds_relax`, `bExceeds_relax`, `clauseB1_relax`,
  `clauseB2_relax`, `clauseB3_relax`, `clauseC1_relax` (relaxing any limit or excluding further
  periods never fails a passing record), `clauseC2_relax`, `compliant_relax` (all limits but the
  continuous one); `splitRecord`, `clauseC2_not_monotone`, `clauseC2_not_monotone_exclude`
  (c(ii) can fail when the continuous limit is relaxed or when a period is excluded).
* Clause c: `clauseC2_iff` (at most `⌊(1 − q) 24 days⌋` hours above `c₂`), `clauseC2_week_iff`
  (one week at 95 %: at most `8` hours), `offshoreDefault_c1` (`1 %` of a day is
  `864 s = 00:14:24`).
* Decay rates: `clauseB2_decay_iff` (b(ii) as the minimum damping ratio
  `ζ ≥ log (A₀/a)/(ω_n b₂)`), `clauseB3_decay_iff` (`ζ ≥ log (A₀/(b₃ P_max))/(ω_n t₃)`),
  `clauseB3_of_clauseB2_decay` (with `b₂ = 2 t₃`, b(ii) implies b(iii) for exponential decay
  when `A₀ a ≤ (b₃ P_max)²`), `offshore_b_product` (default offshore column: `b₂ = 2 t₃` and
  `b₁ · a(i) = b₃²`, so the bound holds for every oscillation within b(i) at a production
  `≤ P_max`; least strict column: `b₁ · a(i) > b₃²`), `clauseB2_of_decay`, `clauseB3_of_decay`
  (record forms).
* Set-point steps (§5.1, §5.6): `clauseB1_of_step` (a step through a stable band-pass filter gives
  b(i) exceedances shorter than `log (M/(b₁ P_max))/r`; a minimum duration of that length removes
  them).
* Small onshore modules: `bExceeds_iff_aExceeds`, `clauseB1_iff_clauseA`, `onshore_floor_iff`,
  `onshoreDefault_floor_iff` (`P_max ≤ 40 A`, `20 MW` for `A = 500 kW`).
* Aggregation (§4.1): `aggregate_capacity` (no violation of a capacity-relative limit is created),
  `aggregate_offshore_violation`, `aggregate_onshore_violation` (it can be created for the
  max-form limits), `aggregate_cancel` (sites in violation, compliant aggregate).

Correction (§3.5). The claim "if these clauses [a] are respected, the wind farms are also
compliant with the other clauses" holds exactly (`compliant_of_clauseA`, for `c₁ ≥ 0`) when b(i)
is assessed during exceedances of the continuous limit. Under that reading, for an onshore module
with `b₁ P_max ≤ A` (`P_max ≤ 20 MW` at the default `500 kW`, `2.5 %`; `40 MW` at the most strict
`200 kW`, `0.5 %`) every exceedance of the continuous limit is a b(i) violation, so the
temporary-exceedance allowance of b(ii) is void (`clauseB1_iff_clauseA`).

Correction (Tables 3–9, §4.2). The trend "relaxing a limit never fails a passing week" holds for
b(i), b(ii), b(iii), c(i) under every limit and every exclusion and for c(ii) under `c₂`, `q`,
`dC` (`compliant_relax`), but not for c(ii) under the continuous limit: relaxing a(i)/a(ii) can
split one long exceedance into several, each longer than `dC` (`clauseC2_not_monotone`), and so
can excluding periods inside an exceedance (`clauseC2_not_monotone_exclude`): "exclusion can
only remove violations" holds for b(i), b(ii), b(iii), c(i) but not for c(ii).

Correction (§4.1). "Aggregation shows no compliance issues" is not a property of the clauses:
aggregation preserves only purely capacity-relative limits (`aggregate_capacity`); for the
offshore form `max(a₁ P_actual, a₂ P_max)` with `0 < a₂ < a₁` and for the onshore absolute floor,
compliant sites in phase can give a non-compliant aggregate (`aggregate_offshore_violation`,
`aggregate_onshore_violation`). The observed improvement comes from uncorrelated damping powers
(cancellation, `aggregate_cancel`).

Sharpening (§4.1). "168 · 0.05 ≈ 8" is exact as `168 − ⌈0.95 · 168⌉ = ⌊0.05 · 168⌋ = 8`
(`clauseC2_week_iff`).

Family and connection conclusions.
* None: this module defines no family. Every result is a static identity of the clause
  parameters (`M`) or a statement quantified over arbitrary measured records (`IO`).
-/

noncomputable section
namespace powerlib.ForcedOscillation
open Finset Signal

/-! ## Clause parameters -/

/-- Continuous limit of clauses a(i), a(ii): the largest of a share of the actual production, a
share of the maximum capacity and an absolute floor (a power, in the unit of the record). -/
structure ContinuousLimit where
  /-- Share of the actual production (offshore 0.1–2 Hz clause a(i)). -/
  actual : ℝ
  /-- Share of the maximum capacity. -/
  capacity : ℝ
  /-- Absolute floor (onshore clause a(ii), 500 kW by default). -/
  absolute : ℝ

namespace ContinuousLimit

/-- The continuous limit at a timestamp with maximum capacity `Pmax` and actual production
`Pact`. -/
def value (c : ContinuousLimit) (Pmax Pact : ℝ) : ℝ :=
  max (max (c.actual * Pact) (c.capacity * Pmax)) c.absolute

/-- Offshore form, Art. 26(2)(a), 0.1–2 Hz: a(i) `a₁ P_actual`, a(ii) `a₂ P_max`. -/
def offshore (a₁ a₂ : ℝ) : ContinuousLimit := ⟨a₁, a₂, 0⟩

/-- Onshore form, Art. 21(3)(a) (and offshore 2–20 Hz): a(i) `a₁ P_max`, a(ii) the absolute value
`A`. -/
def onshore (a₁ A : ℝ) : ContinuousLimit := ⟨0, a₁, A⟩

@[tmio M, powerlib_domain] theorem offshore_value {a₁ a₂ Pmax : ℝ} (h : 0 ≤ a₂ * Pmax)
    (Pact : ℝ) : (offshore a₁ a₂).value Pmax Pact = max (a₁ * Pact) (a₂ * Pmax) :=
  max_eq_left (h.trans (le_max_right _ _))

@[tmio M, powerlib_domain] theorem onshore_value {a₁ A Pmax Pact : ℝ} (h : 0 ≤ a₁ * Pmax) : (onshore a₁ A).value Pmax Pact = max (a₁ * Pmax) A := by
  simp only [value, onshore, zero_mul, max_eq_right h]

/-- `c'` is at least as permissive as `c`, coefficient by coefficient. -/
def Le (c c' : ContinuousLimit) : Prop :=
  c.actual ≤ c'.actual ∧ c.capacity ≤ c'.capacity ∧ c.absolute ≤ c'.absolute

@[tmio M, powerlib_domain] theorem value_mono {c c' : ContinuousLimit} (h : c.Le c') {Pmax Pact : ℝ}
    (hP : 0 ≤ Pmax) (hA : 0 ≤ Pact) : c.value Pmax Pact ≤ c'.value Pmax Pact :=
  max_le_max (max_le_max (mul_le_mul_of_nonneg_right h.1 hA)
    (mul_le_mul_of_nonneg_right h.2.1 hP)) h.2.2

/-- The limit of an aggregate never exceeds the sum of the site limits (subadditivity of the
maximum); for the purely proportional form it is additive. -/
@[tmio M, powerlib_domain] theorem value_add_le (c : ContinuousLimit) (hA : 0 ≤ c.absolute)
    (P₁ P₂ Q₁ Q₂ : ℝ) :
    c.value (P₁ + P₂) (Q₁ + Q₂) ≤ c.value P₁ Q₁ + c.value P₂ Q₂ := by
  simp only [value]
  have h1 := le_max_left (max (c.actual * Q₁) (c.capacity * P₁)) c.absolute
  have h2 := le_max_left (max (c.actual * Q₂) (c.capacity * P₂)) c.absolute
  have h3 := le_max_right (max (c.actual * Q₁) (c.capacity * P₁)) c.absolute
  have h4 := le_max_right (max (c.actual * Q₂) (c.capacity * P₂)) c.absolute
  refine max_le (max_le ?_ ?_) (by linarith)
  · have := le_max_left (c.actual * Q₁) (c.capacity * P₁)
    have := le_max_left (c.actual * Q₂) (c.capacity * P₂)
    linarith
  · have := le_max_right (c.actual * Q₁) (c.capacity * P₁)
    have := le_max_right (c.actual * Q₂) (c.capacity * P₂)
    linarith

end ContinuousLimit

/-- The forced-oscillation clauses of draft NC RfG 2.0, Art. 21(3) / 26(2), as symbolic
parameters. Shares are fractions of the stated power (`1 / 100` for 1 %), times in seconds. -/
structure Clauses where
  /-- Continuous limit, clauses a(i), a(ii). -/
  a : ContinuousLimit
  /-- b(i): temporary exceedance limit, share of `P_max`. -/
  b₁ : ℝ
  /-- b(ii): maximum duration of an exceedance of the continuous limit [s]. -/
  b₂ : ℝ
  /-- b(iii): level, share of `P_max`, the oscillation must be below ... -/
  b₃ : ℝ
  /-- ... within `t₃` seconds of exceeding the continuous limit. -/
  t₃ : ℝ
  /-- c(i): maximum share of each day spent in exceedance. -/
  c₁ : ℝ
  /-- c(ii): maximum number of exceedances per hour ... -/
  c₂ : ℕ
  /-- ... at the percentile level `q` of the hourly counts. -/
  q : ℝ
  /-- c(i), c(ii) count only exceedances lasting more than `dC` (10 s). -/
  dC : ℝ
  /-- b(i) disregards exceedances lasting less than `dB` (the tool's 1 s; `0` counts all). -/
  dB : ℝ

/-- `C'` is at least as permissive as `C` in every clause. -/
def Clauses.Relaxes (C C' : Clauses) : Prop :=
  C.a.Le C'.a ∧ C.b₁ ≤ C'.b₁ ∧ C.b₂ ≤ C'.b₂ ∧ C.b₃ ≤ C'.b₃ ∧ C.t₃ ≤ C'.t₃ ∧ C.c₁ ≤ C'.c₁ ∧
    C.c₂ ≤ C'.c₂ ∧ C'.q ≤ C.q ∧ C.dC ≤ C'.dC ∧ C.dB ≤ C'.dB

/-- Default values of Art. 26(2) for offshore modules, 0.1–2 Hz (Appendix A, §5.8): a(i) `1 %` of
the actual production, a(ii) `0.5 %` of `P_max`, b(i) `4 %`, b(ii) `180 s`, b(iii) `2 %` within
`90 s`, c(i) `1 %` of the day, c(ii) `3` per hour at the 95th percentile, exceedances longer
than `10 s` counted by c, and the tool's b(i) minimum duration `1 s`. -/
def offshoreDefault : Clauses where
  a := ContinuousLimit.offshore (1 / 100) (5 / 1000)
  b₁ := 4 / 100
  b₂ := 180
  b₃ := 2 / 100
  t₃ := 90
  c₁ := 1 / 100
  c₂ := 3
  q := 95 / 100
  dC := 10
  dB := 1

/-- Least strict values of Art. 26(2), 0.1–2 Hz: a(i) `2 %`, a(ii) `1 %`, b(i) `5 %`, b(ii)
`180 s`, b(iii) `2.5 %` within `90 s`, c(i) `2 %`, c(ii) `4` per hour at the 85th percentile. -/
def offshoreLeastStrict : Clauses where
  a := ContinuousLimit.offshore (2 / 100) (1 / 100)
  b₁ := 5 / 100
  b₂ := 180
  b₃ := 25 / 1000
  t₃ := 90
  c₁ := 2 / 100
  c₂ := 4
  q := 85 / 100
  dC := 10
  dB := 1

/-- Default values of Art. 21(3) for onshore modules, 0.1–20 Hz: a(i) `0.5 %` of `P_max`, a(ii) the
absolute value `A` (`500 kW` in the unit of the record), b(i) `2.5 %`, b(ii) `180 s`, b(iii)
`1.25 %` within `90 s`, c(i) `1 %`, c(ii) `3` per hour at the 95th percentile. -/
def onshoreDefault (A : ℝ) : Clauses where
  a := ContinuousLimit.onshore (5 / 1000) A
  b₁ := 25 / 1000
  b₂ := 180
  b₃ := 125 / 10000
  t₃ := 90
  c₁ := 1 / 100
  c₂ := 3
  q := 95 / 100
  dC := 10
  dB := 1

/-! ## Measured records and the clauses -/

/-- The record of one assessment period (`days` days from time `0`) of a power park module with
maximum capacity `Pmax`: the `m` local maxima, in time order, of the rectified band-pass filtered
active power (`Signal.IsLocalMaxAbs`), with their times `t k` [s], amplitudes `amp k`, the actual
production `pAct k` at the peak and whether the peak lies outside the excluded periods
(`assessed k`). -/
structure Record where
  Pmax : ℝ
  days : ℕ
  m : ℕ
  t : ℕ → ℝ
  amp : ℕ → ℝ
  pAct : ℕ → ℝ
  assessed : ℕ → Prop
  Pmax_nonneg : 0 ≤ Pmax
  pAct_nonneg : ∀ k, 0 ≤ pAct k
  times_mono : TimesMono m t

variable (C : Clauses) (R : Record)

/-- Peak `k` exceeds the continuous limit (and is assessed). -/
def aExceeds (k : ℕ) : Prop := R.assessed k ∧ C.a.value R.Pmax (R.pAct k) < R.amp k

/-- Peak `k` exceeds the temporary limit `b₁ P_max` during an exceedance of the continuous limit
("in case this limit is temporarily exceeded", §2.3). -/
def bExceeds (k : ℕ) : Prop := aExceeds C R k ∧ C.b₁ * R.Pmax < R.amp k

/-- Peak `k` lies in the window `w` of length `len` (the day `w` for `len = 86400`, the hour `w`
for `len = 3600`); exceedances are cut at window boundaries. -/
def InWindow (len : ℝ) (w k : ℕ) : Prop := len * w ≤ R.t k ∧ R.t k < len * (w + 1)

/-- Clause a: no assessed peak exceeds the continuous limit. -/
def ClauseA : Prop := ∀ k < R.m, ¬ aExceeds C R k

/-- Clause b(i): no exceedance of `b₁ P_max` lasting at least `dB`. -/
def ClauseB1 : Prop := events R.m (bExceeds C R) R.t (Set.Ici C.dB) = ∅

/-- Clause b(ii): every exceedance of the continuous limit lasts at most `b₂`. -/
def ClauseB2 : Prop := ∀ e ∈ envelopes R.m (aExceeds C R), duration R.t e ≤ C.b₂

/-- Clause b(iii): in every exceedance of the continuous limit, the peaks from `t₃` after its start
on are at most `b₃ P_max`. -/
def ClauseB3 : Prop :=
  ∀ e ∈ envelopes R.m (aExceeds C R), ∀ k, e.1 ≤ k → k ≤ e.2 → R.t e.1 + C.t₃ ≤ R.t k →
    R.amp k ≤ C.b₃ * R.Pmax

/-- Time of day `d` spent in exceedances lasting more than `dC`. -/
def dayTime (d : ℕ) : ℝ := eventTime R.m (fun k => aExceeds C R k ∧ InWindow R 86400 d k) R.t
  (Set.Ioi C.dC)

/-- Clause c(i): every day spends at most the share `c₁` of its `86400 s` in exceedance. -/
def ClauseC1 : Prop := ∀ d < R.days, dayTime C R d ≤ C.c₁ * 86400

/-- Number of exceedances lasting more than `dC` in hour `h`. -/
def hourCount (h : Fin (24 * R.days)) : ℕ :=
  eventCount R.m (fun k => aExceeds C R k ∧ InWindow R 3600 h k) R.t (Set.Ioi C.dC)

/-- Clause c(ii): the `q`-percentile (nearest rank) of the hourly counts is at most `c₂`. -/
def ClauseC2 : Prop := nearestRank C.q (hourCount C R) ≤ C.c₂

/-- Compliance over the assessment period: b(i), b(ii), b(iii), c(i) and c(ii) (the "overall"
column of Tables 3–10). -/
def Compliant : Prop :=
  ClauseB1 C R ∧ ClauseB2 C R ∧ ClauseB3 C R ∧ ClauseC1 C R ∧ ClauseC2 C R

/-! ## Clause a implies the other clauses (§3.5) -/

variable {C R}

/-- §3.5: a record that respects clause a passes b(i), b(ii), b(iii), c(i) and c(ii) (for a
nonnegative c(i) share). -/
@[tmio IO, powerlib_domain] theorem compliant_of_clauseA (hc₁ : 0 ≤ C.c₁) (h : ClauseA C R) :
    Compliant C R := by
  have hA : envelopes R.m (aExceeds C R) = ∅ := envelopes_eq_empty h
  have hev : ∀ (x : ℕ → Prop) (S : Set ℝ), (∀ k, x k → aExceeds C R k) →
      events R.m x R.t S = ∅ := fun x S hx => by
    rw [events, envelopes_eq_empty fun k hk hxk => h k hk (hx k hxk), filter_empty]
  refine ⟨hev _ _ fun k hk => hk.1, by simp [ClauseB2, hA], by simp [ClauseB3, hA], ?_, ?_⟩
  · intro d _
    rw [dayTime, eventTime, hev _ _ fun k hk => hk.1, sum_empty]
    positivity
  · have : hourCount C R = fun _ => 0 := funext fun h' => by
      rw [hourCount, eventCount, hev _ _ fun k hk => hk.1, card_empty]
    rw [ClauseC2, this, nearestRank_zero]
    exact Nat.zero_le _

/-! ## Monotonicity in the limits and in the exclusions (§4.2, Tables 2–9) -/

/-- The record with the further excluded periods `¬ M` (Table 2: system-support requests,
disturbed network conditions): an excluded peak is treated as compliant. -/
def Record.exclude (R : Record) (M : ℕ → Prop) : Record :=
  { R with assessed := fun k => R.assessed k ∧ M k }

variable {C' : Clauses}

@[tmio IO, powerlib_domain] theorem aExceeds_relax (h : C.Relaxes C') (M : ℕ → Prop) {k : ℕ}
    (hk : aExceeds C' (R.exclude M) k) : aExceeds C R k :=
  ⟨hk.1.1, (ContinuousLimit.value_mono h.1 R.Pmax_nonneg (R.pAct_nonneg k)).trans_lt hk.2⟩

@[tmio IO, powerlib_domain] theorem bExceeds_relax (h : C.Relaxes C') (M : ℕ → Prop) {k : ℕ}
    (hk : bExceeds C' (R.exclude M) k) : bExceeds C R k :=
  ⟨aExceeds_relax h M hk.1,
    (mul_le_mul_of_nonneg_right h.2.1 R.Pmax_nonneg).trans_lt hk.2⟩

/-- b(i) is monotone: relaxing any limit or excluding further periods never fails a passing
record. -/
@[tmio IO, powerlib_domain] theorem clauseB1_relax (h : C.Relaxes C') (M : ℕ → Prop)
    (hb : ClauseB1 C R) : ClauseB1 C' (R.exclude M) := by
  have h0 : events R.m (bExceeds C' (R.exclude M)) R.t (Set.Ici C.dB) = ∅ :=
    events_eq_empty_of_le (fun _ hk => bExceeds_relax h M hk) (isUpperSet_Ici _) R.times_mono hb
  refine eq_empty_of_forall_notMem fun e he => ?_
  obtain ⟨h1, h2⟩ := mem_events.mp he
  have : e ∈ events R.m (bExceeds C' (R.exclude M)) R.t (Set.Ici C.dB) :=
    mem_events.mpr ⟨h1, (Set.Ici_subset_Ici.mpr h.2.2.2.2.2.2.2.2.2) h2⟩
  simp [h0] at this

/-- b(ii) is monotone in the limits and the exclusions. -/
@[tmio IO, powerlib_domain] theorem clauseB2_relax (h : C.Relaxes C') (M : ℕ → Prop)
    (hb : ClauseB2 C R) : ClauseB2 C' (R.exclude M) := fun e he =>
  (duration_le_of_le (fun _ hk => aExceeds_relax h M hk) R.times_mono hb e he).trans h.2.2.1

/-- b(iii) is monotone in the limits (a later deadline `t₃`, a higher level `b₃`) and the
exclusions. -/
@[tmio IO, powerlib_domain] theorem clauseB3_relax (h : C.Relaxes C') (M : ℕ → Prop)
    (hb : ClauseB3 C R) : ClauseB3 C' (R.exclude M) := by
  intro e he k hk1 hk2 hk
  have hk' : R.t e.1 + C'.t₃ ≤ R.t k := hk
  have := late_peaks_of_le (fun _ hk => aExceeds_relax h M hk) R.times_mono hb e he k hk1 hk2
    (by linarith [h.2.2.2.2.1])
  exact this.trans (mul_le_mul_of_nonneg_right h.2.2.2.1 R.Pmax_nonneg)

/-- c(i) is monotone: the daily exceedance time only decreases when a limit is relaxed or a
period is excluded (`Signal.eventTime_mono`, `Signal.eventTime_mono_class`). -/
@[tmio IO, powerlib_domain] theorem clauseC1_relax (h : C.Relaxes C') (M : ℕ → Prop)
    (hc : ClauseC1 C R) : ClauseC1 C' (R.exclude M) := by
  intro d hd
  calc dayTime C' (R.exclude M) d
      ≤ eventTime R.m (fun k => aExceeds C' (R.exclude M) k ∧ InWindow R 86400 d k) R.t
          (Set.Ioi C.dC) :=
        eventTime_mono_class (Set.Ioi_subset_Ioi h.2.2.2.2.2.2.2.2.1) R.times_mono
    _ ≤ dayTime C R d :=
        eventTime_mono (fun _ hk => ⟨aExceeds_relax h M hk.1, hk.2⟩) (isUpperSet_Ioi _) R.times_mono
    _ ≤ C.c₁ * 86400 := hc d hd
    _ ≤ C'.c₁ * 86400 := by linarith [h.2.2.2.2.2.1]

/-- c(ii) is monotone in its own parameters (`c₂`, `q`, `dC`) when the continuous limit is kept. -/
@[tmio IO, powerlib_domain] theorem clauseC2_relax (h : C.Relaxes C') (ha : C'.a = C.a)
    (hq : C.q ≤ 1) (hc : ClauseC2 C R) : ClauseC2 C' R := by
  have hpat : aExceeds C' R = aExceeds C R := by
    funext k; simp only [aExceeds, ha]
  have hcount : ∀ w, hourCount C' R w ≤ hourCount C R w := fun w => by
    rw [hourCount, hourCount, hpat]
    exact eventCount_mono_class (Set.Ioi_subset_Ioi h.2.2.2.2.2.2.2.2.1)
  exact (nearestRank_mono hq h.2.2.2.2.2.2.2.1 hcount).trans (hc.trans h.2.2.2.2.2.2.1)

/-- Relaxing every limit except the continuous limit never fails a passing record. -/
@[tmio IO, powerlib_domain] theorem compliant_relax (h : C.Relaxes C') (ha : C'.a = C.a)
    (hq : C.q ≤ 1) (hc : Compliant C R) : Compliant C' R := by
  have hR : R.exclude (fun _ => True) = R := by
    cases R; simp [Record.exclude]
  obtain ⟨h1, h2, h3, h4, h5⟩ := hc
  refine ⟨?_, ?_, ?_, ?_, clauseC2_relax h ha hq h5⟩
  · simpa [hR] using clauseB1_relax h (fun _ => True) h1
  · simpa [hR] using clauseB2_relax h (fun _ => True) h2
  · simpa [hR] using clauseB3_relax h (fun _ => True) h3
  · simpa [hR] using clauseC1_relax h (fun _ => True) h4

/-- The split record of `clauseC2_not_monotone`: `B` hours, each with `3c + 2` peaks at the uniform
spacing `3600 / (3c + 2)` s (times `3600 k / (3c + 2)`), every third peak of an hour at the
amplitude `A'` and the others at `A' + 1`; no actual production, nothing excluded. -/
def splitRecord (P A' : ℝ) (hP : 0 ≤ P) (days c B : ℕ) : Record where
  Pmax := P
  days := days
  m := B * (3 * c + 2)
  t := fun k => 3600 * k / (3 * c + 2)
  amp := fun k => if (k % (3 * c + 2)) % 3 = 2 then A' else A' + 1
  pAct := fun _ => 0
  assessed := fun _ => True
  Pmax_nonneg := hP
  pAct_nonneg := fun _ => le_rfl
  times_mono := fun i j hij _ => div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hij) (by norm_num)) (by positivity)

open Classical in
/-- c(ii) is not monotone in the continuous limit: for every clause set with `0 < q ≤ 1`, `c₂ ≥ 1` and `dC (3 c₂ + 2) < 3600 s`, every assessment
period of `days ≥ 1` days and every relaxed continuous limit `a'` (larger at the record's
operating point), there is a record that passes c(ii) under the strict limit and fails it under
the relaxed one. In each of `24 days − ⌈q · 24 days⌉ + 1` hours, one long exceedance (one count)
splits into `c₂ + 1` exceedances longer than `dC` when the peaks between them fall below the
relaxed limit. -/
@[tmio IO, powerlib_domain] theorem clauseC2_not_monotone (hq0 : 0 < C.q) (hq : C.q ≤ 1)
    (hc : 1 ≤ C.c₂) (hdC : C.dC * (3 * C.c₂ + 2) < 3600) {days : ℕ} (hdays : 1 ≤ days) {P : ℝ}
    (hP : 0 ≤ P) {a' : ContinuousLimit} (ha : C.a.Le a') (hlt : C.a.value P 0 < a'.value P 0) :
    ∃ R : Record, R.days = days ∧ C.Relaxes { C with a := a' } ∧ ClauseC2 C R ∧
      ¬ ClauseC2 { C with a := a' } R := by
  set c := C.c₂
  set ℓ := 3 * c + 2 with hℓ
  set H := 24 * days
  set B := H - quantileRank C.q H + 1
  have hr1 : 1 ≤ quantileRank C.q H :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (mul_pos hq0 (by positivity))).ne'
  have hrH := quantileRank_le hq H
  set R := splitRecord P (a'.value P 0) hP days c B
  have hℓpos : (0 : ℝ) < ℓ := by positivity
  have hcast : ((ℓ : ℕ) : ℝ) = 3 * c + 2 := by push_cast [hℓ]; ring
  -- the hour windows are the index blocks `[w ℓ, w ℓ + ℓ)`
  have hwin : ∀ w k : ℕ, InWindow R 3600 w k ↔ w * ℓ ≤ k ∧ k < w * ℓ + ℓ := by
    intro w k
    show 3600 * (w : ℝ) ≤ 3600 * k / (3 * c + 2) ∧ 3600 * (k : ℝ) / (3 * c + 2) < 3600 * (w + 1) ↔ _
    rw [← hcast, le_div_iff₀ hℓpos, div_lt_iff₀ hℓpos]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by exact_mod_cast (show ((w * ℓ : ℕ) : ℝ) ≤ k by push_cast; nlinarith),
        by exact_mod_cast (show (k : ℝ) < ((w * ℓ + ℓ : ℕ) : ℝ) by push_cast; nlinarith)⟩
    · rintro ⟨h1, h2⟩
      have h1' : ((w * ℓ : ℕ) : ℝ) ≤ k := by exact_mod_cast h1
      have h2' : (k : ℝ) < ((w * ℓ + ℓ : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at h1' h2'
      constructor <;> nlinarith
  have hmod : ∀ w k : ℕ, w * ℓ ≤ k → k < w * ℓ + ℓ → k % ℓ = k - w * ℓ := fun w k h1 h2 => by
    have hk : k = (k - w * ℓ) + w * ℓ := by omega
    rw [hk, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    omega
  -- under the strict limit every peak exceeds, under the relaxed one every third peak does not
  have hA : ∀ k, aExceeds C R k := fun k => by
    refine ⟨trivial, ?_⟩
    show C.a.value P 0 < if (k % ℓ) % 3 = 2 then a'.value P 0 else a'.value P 0 + 1
    split_ifs <;> linarith
  have hA' : ∀ k, aExceeds { C with a := a' } R k ↔ (k % ℓ) % 3 ≠ 2 := fun k => by
    show (True ∧ a'.value P 0 < if (k % ℓ) % 3 = 2 then a'.value P 0 else a'.value P 0 + 1) ↔ _
    split_ifs with h <;> simp [h]
  have hdur : C.dC < 3600 / (ℓ : ℝ) := by rw [lt_div_iff₀ hℓpos, hcast]; linarith
  -- hourly counts
  have hcount : ∀ w : Fin H, hourCount C R w = if (w : ℕ) < B then 1 else 0 := by
    intro w
    split_ifs with hw
    · have hBw : w * ℓ + ℓ ≤ B * ℓ := by
        simpa [add_mul] using Nat.mul_le_mul_right ℓ (show (w : ℕ) + 1 ≤ B by omega)
      refine eventCount_block (s := w * ℓ) (L := ℓ) (by omega) hBw (fun k _ => ?_) ?_
      · exact (and_iff_right (hA k)).trans (hwin w k)
      · show C.dC < 3600 * ((w * ℓ + ℓ - 1 : ℕ) : ℝ) / (3 * c + 2) -
          3600 * ((w * ℓ : ℕ) : ℝ) / (3 * c + 2)
        rw [Nat.cast_sub (by omega), ← hcast, ← sub_div]
        push_cast
        calc C.dC < 3600 / (ℓ : ℝ) := hdur
          _ ≤ (3600 * ((w : ℝ) * ℓ + ℓ - 1) - 3600 * ((w : ℝ) * ℓ)) / ℓ := by
            apply div_le_div_of_nonneg_right _ hℓpos.le
            have h0 : (0 : ℝ) ≤ c := by positivity
            have : (1 : ℝ) ≤ ℓ - 1 := by rw [hcast]; linarith
            nlinarith
    · show eventCount R.m _ R.t _ = 0
      rw [eventCount, events, envelopes_eq_empty, filter_empty, card_empty]
      intro k hk hx
      have := ((hwin w k).mp hx.2).1
      have : B * ℓ ≤ w * ℓ := Nat.mul_le_mul_right ℓ (by omega)
      have hk' : k < B * ℓ := hk
      omega
  have hcount' : ∀ w : Fin H, hourCount { C with a := a' } R w =
      if (w : ℕ) < B then c + 1 else 0 := by
    intro w
    split_ifs with hw
    · have hBw : w * ℓ + ℓ ≤ B * ℓ := by
        simpa [add_mul] using Nat.mul_le_mul_right ℓ (show (w : ℕ) + 1 ≤ B by omega)
      refine eventCount_comb (s := w * ℓ) (c := c) (by show w * ℓ + 3 * c + 2 ≤ B * ℓ; omega)
        (fun k _ => ?_) (fun i _ => ?_)
      · rw [show aExceeds { C with a := a' } R k ∧ InWindow R 3600 w k ↔
          (k % ℓ) % 3 ≠ 2 ∧ (w * ℓ ≤ k ∧ k < w * ℓ + ℓ) from and_congr (hA' k) (hwin w k)]
        constructor
        · rintro ⟨h1, h2, h3⟩
          rw [hmod w k h2 h3] at h1
          exact ⟨h2, by omega, h1⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨by rw [hmod w k h1 (by omega)]; exact h3, h1, by omega⟩
      · show C.dC < 3600 * ((w * ℓ + 3 * i + 1 : ℕ) : ℝ) / (3 * c + 2) -
          3600 * ((w * ℓ + 3 * i : ℕ) : ℝ) / (3 * c + 2)
        rw [← hcast, ← sub_div]
        push_cast
        convert hdur using 2
        ring
    · show eventCount R.m _ R.t _ = 0
      rw [eventCount, events, envelopes_eq_empty, filter_empty, card_empty]
      intro k hk hx
      have := ((hwin w k).mp hx.2).1
      have : B * ℓ ≤ w * ℓ := Nat.mul_le_mul_right ℓ (by omega)
      have hk' : k < B * ℓ := hk
      omega
  refine ⟨R, rfl, ⟨ha, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩,
    ?_, ?_⟩
  · rw [ClauseC2, nearestRank_le_iff hq]
    have : (univ.filter fun w : Fin (24 * R.days) => C.c₂ < hourCount C R w) = ∅ :=
      filter_eq_empty_iff.mpr fun w _ => by rw [hcount w]; split_ifs <;> omega
    rw [this, card_empty]
    exact Nat.zero_le _
  · rw [ClauseC2, nearestRank_le_iff hq, not_le]
    have : (univ.filter fun w : Fin (24 * R.days) =>
        ({ C with a := a' } : Clauses).c₂ < hourCount { C with a := a' } R w) =
        univ.filter fun w : Fin H => (w : ℕ) < B :=
      filter_congr fun w _ => by
        rw [hcount' w]
        split_ifs with hw
        · exact ⟨fun _ => hw, fun _ => by show c < c + 1; omega⟩
        · exact ⟨fun h => absurd h (by show ¬ c < 0; omega), fun h => absurd h hw⟩
    rw [this, Fintype.card_fin]
    show H - quantileRank C.q H < (univ.filter fun w : Fin H => (w : ℕ) < B).card
    rw [Fin.card_filter_val_lt]
    omega

open Classical in
/-- c(ii) is not monotone in the exclusions either: for every clause set with `0 < q ≤ 1`,
`c₂ ≥ 1` and `dC (3 c₂ + 2) < 3600 s` and every assessment period of `days ≥ 1` days, there are
a record that passes c(ii) and an exclusion mask after which it fails: excluding every third
peak of a long exceedance (e.g. short system-support requests during it, Table 2) splits it into
`c₂ + 1` exceedances longer than `dC`. -/
@[tmio IO, powerlib_domain] theorem clauseC2_not_monotone_exclude (hq0 : 0 < C.q) (hq : C.q ≤ 1)
    (hc : 1 ≤ C.c₂) (hdC : C.dC * (3 * C.c₂ + 2) < 3600) {days : ℕ} (hdays : 1 ≤ days) {P : ℝ}
    (hP : 0 ≤ P) :
    ∃ (R : Record) (M : ℕ → Prop), R.days = days ∧ ClauseC2 C R ∧ ¬ ClauseC2 C (R.exclude M) := by
  set c := C.c₂
  set ℓ := 3 * c + 2 with hℓ
  set H := 24 * days
  set B := H - quantileRank C.q H + 1
  have hr1 : 1 ≤ quantileRank C.q H :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (mul_pos hq0 (by positivity))).ne'
  have hrH := quantileRank_le hq H
  set R := splitRecord P (C.a.value P 0 + 1) hP days c B
  set M : ℕ → Prop := fun k => (k % ℓ) % 3 ≠ 2
  have hℓpos : (0 : ℝ) < ℓ := by positivity
  have hcast : ((ℓ : ℕ) : ℝ) = 3 * c + 2 := by push_cast [hℓ]; ring
  -- the hour windows are the index blocks `[w ℓ, w ℓ + ℓ)`
  have hwin : ∀ w k : ℕ, InWindow R 3600 w k ↔ w * ℓ ≤ k ∧ k < w * ℓ + ℓ := by
    intro w k
    show 3600 * (w : ℝ) ≤ 3600 * k / (3 * c + 2) ∧ 3600 * (k : ℝ) / (3 * c + 2) < 3600 * (w + 1) ↔ _
    rw [← hcast, le_div_iff₀ hℓpos, div_lt_iff₀ hℓpos]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by exact_mod_cast (show ((w * ℓ : ℕ) : ℝ) ≤ k by push_cast; nlinarith),
        by exact_mod_cast (show (k : ℝ) < ((w * ℓ + ℓ : ℕ) : ℝ) by push_cast; nlinarith)⟩
    · rintro ⟨h1, h2⟩
      have h1' : ((w * ℓ : ℕ) : ℝ) ≤ k := by exact_mod_cast h1
      have h2' : (k : ℝ) < ((w * ℓ + ℓ : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at h1' h2'
      constructor <;> nlinarith
  have hmod : ∀ w k : ℕ, w * ℓ ≤ k → k < w * ℓ + ℓ → k % ℓ = k - w * ℓ := fun w k h1 h2 => by
    have hk : k = (k - w * ℓ) + w * ℓ := by omega
    rw [hk, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    omega
  -- under the strict limit every peak exceeds, under the relaxed one every third peak does not
  have hA : ∀ k, aExceeds C R k := fun k => by
    refine ⟨trivial, ?_⟩
    show C.a.value P 0 < if (k % ℓ) % 3 = 2 then C.a.value P 0 + 1 else C.a.value P 0 + 1 + 1
    split_ifs <;> linarith
  have hA' : ∀ k, aExceeds C (R.exclude M) k ↔ (k % ℓ) % 3 ≠ 2 := fun k => by
    show ((True ∧ M k) ∧ C.a.value P 0 <
      if (k % ℓ) % 3 = 2 then C.a.value P 0 + 1 else C.a.value P 0 + 1 + 1) ↔ _
    simp only [M, true_and]
    split_ifs with h
    · simp [h]
    · exact ⟨fun h' => h'.1, fun h' => ⟨h', by linarith⟩⟩
  have hdur : C.dC < 3600 / (ℓ : ℝ) := by rw [lt_div_iff₀ hℓpos, hcast]; linarith
  -- hourly counts
  have hcount : ∀ w : Fin H, hourCount C R w = if (w : ℕ) < B then 1 else 0 := by
    intro w
    split_ifs with hw
    · have hBw : w * ℓ + ℓ ≤ B * ℓ := by
        simpa [add_mul] using Nat.mul_le_mul_right ℓ (show (w : ℕ) + 1 ≤ B by omega)
      refine eventCount_block (s := w * ℓ) (L := ℓ) (by omega) hBw (fun k _ => ?_) ?_
      · exact (and_iff_right (hA k)).trans (hwin w k)
      · show C.dC < 3600 * ((w * ℓ + ℓ - 1 : ℕ) : ℝ) / (3 * c + 2) -
          3600 * ((w * ℓ : ℕ) : ℝ) / (3 * c + 2)
        rw [Nat.cast_sub (by omega), ← hcast, ← sub_div]
        push_cast
        calc C.dC < 3600 / (ℓ : ℝ) := hdur
          _ ≤ (3600 * ((w : ℝ) * ℓ + ℓ - 1) - 3600 * ((w : ℝ) * ℓ)) / ℓ := by
            apply div_le_div_of_nonneg_right _ hℓpos.le
            have h0 : (0 : ℝ) ≤ c := by positivity
            have : (1 : ℝ) ≤ ℓ - 1 := by rw [hcast]; linarith
            nlinarith
    · show eventCount R.m _ R.t _ = 0
      rw [eventCount, events, envelopes_eq_empty, filter_empty, card_empty]
      intro k hk hx
      have := ((hwin w k).mp hx.2).1
      have : B * ℓ ≤ w * ℓ := Nat.mul_le_mul_right ℓ (by omega)
      have hk' : k < B * ℓ := hk
      omega
  have hcount' : ∀ w : Fin H, hourCount C (R.exclude M) w =
      if (w : ℕ) < B then c + 1 else 0 := by
    intro w
    split_ifs with hw
    · have hBw : w * ℓ + ℓ ≤ B * ℓ := by
        simpa [add_mul] using Nat.mul_le_mul_right ℓ (show (w : ℕ) + 1 ≤ B by omega)
      refine eventCount_comb (s := w * ℓ) (c := c) (by show w * ℓ + 3 * c + 2 ≤ B * ℓ; omega)
        (fun k _ => ?_) (fun i _ => ?_)
      · rw [show aExceeds C (R.exclude M) k ∧ InWindow (R.exclude M) 3600 w k ↔
          (k % ℓ) % 3 ≠ 2 ∧ (w * ℓ ≤ k ∧ k < w * ℓ + ℓ) from and_congr (hA' k) (hwin w k)]
        constructor
        · rintro ⟨h1, h2, h3⟩
          rw [hmod w k h2 h3] at h1
          exact ⟨h2, by omega, h1⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨by rw [hmod w k h1 (by omega)]; exact h3, h1, by omega⟩
      · show C.dC < 3600 * ((w * ℓ + 3 * i + 1 : ℕ) : ℝ) / (3 * c + 2) -
          3600 * ((w * ℓ + 3 * i : ℕ) : ℝ) / (3 * c + 2)
        rw [← hcast, ← sub_div]
        push_cast
        convert hdur using 2
        ring
    · show eventCount R.m _ R.t _ = 0
      rw [eventCount, events, envelopes_eq_empty, filter_empty, card_empty]
      intro k hk hx
      have := ((hwin w k).mp hx.2).1
      have : B * ℓ ≤ w * ℓ := Nat.mul_le_mul_right ℓ (by omega)
      have hk' : k < B * ℓ := hk
      omega
  refine ⟨R, M, rfl, ?_, ?_⟩
  · rw [ClauseC2, nearestRank_le_iff hq]
    have : (univ.filter fun w : Fin (24 * R.days) => C.c₂ < hourCount C R w) = ∅ :=
      filter_eq_empty_iff.mpr fun w _ => by rw [hcount w]; split_ifs <;> omega
    rw [this, card_empty]
    exact Nat.zero_le _
  · rw [ClauseC2, nearestRank_le_iff hq, not_le]
    have : (univ.filter fun w : Fin (24 * (R.exclude M).days) =>
        C.c₂ < hourCount C (R.exclude M) w) =
        univ.filter fun w : Fin H => (w : ℕ) < B :=
      filter_congr fun w _ => by
        rw [hcount' w]
        split_ifs with hw
        · exact ⟨fun _ => hw, fun _ => by show c < c + 1; omega⟩
        · exact ⟨fun h => absurd h (by show ¬ c < 0; omega), fun h => absurd h hw⟩
    rw [this, Fintype.card_fin]
    show H - quantileRank C.q H < (univ.filter fun w : Fin H => (w : ℕ) < B).card
    rw [Fin.card_filter_val_lt]
    omega

/-! ## Clause c: units and the percentile -/

open Classical in
/-- c(ii) in counting form: for `0 ≤ q ≤ 1` the percentile bound holds exactly when at most
`⌊(1 − q) · 24 · days⌋` hours have more than `c₂` exceedances. -/
@[tmio IO, powerlib_domain] theorem clauseC2_iff (hq0 : 0 ≤ C.q) (hq : C.q ≤ 1) :
    ClauseC2 C R ↔ (univ.filter fun h => C.c₂ < hourCount C R h).card ≤
      ⌊(1 - C.q) * (24 * R.days : ℕ)⌋₊ := by
  rw [ClauseC2, nearestRank_le_iff hq, Fintype.card_fin, sub_quantileRank hq0 hq]

open Classical in
/-- c(ii) over one week at the 95th percentile: at most `8` hours with more than `c₂`
exceedances. -/
@[tmio IO, powerlib_domain] theorem clauseC2_week_iff (hd : R.days = 7) (hq : C.q = 95 / 100) :
    ClauseC2 C R ↔ (univ.filter fun h => C.c₂ < hourCount C R h).card ≤ 8 := by
  rw [clauseC2_iff (by rw [hq]; norm_num) (by rw [hq]; norm_num), hq,
    show ((24 * R.days : ℕ) : ℝ) = 168 by rw [hd]; norm_num]
  have : ⌊(1 - 95 / 100 : ℝ) * 168⌋₊ = 8 := by
    rw [Nat.floor_eq_iff (by norm_num)]
    norm_num
  rw [this]

/-! ## Per-unit records (§3.1) -/

/-- The record in per unit of the base `P > 0` (e.g. the maximum capacity or the exchange
agreement of §5.2): every power divided by `P`. -/
def Record.perUnit (R : Record) {P : ℝ} (hP : 0 < P) : Record where
  Pmax := R.Pmax / P
  days := R.days
  m := R.m
  t := R.t
  amp := fun k => R.amp k / P
  pAct := fun k => R.pAct k / P
  assessed := R.assessed
  Pmax_nonneg := div_nonneg R.Pmax_nonneg hP.le
  pAct_nonneg := fun k => div_nonneg (R.pAct_nonneg k) hP.le
  times_mono := R.times_mono

/-- The clauses with the absolute floor expressed in the same base (the shares are unchanged). -/
def Clauses.perUnit (C : Clauses) (P : ℝ) : Clauses :=
  { C with a := { C.a with absolute := C.a.absolute / P } }

@[tmio M, powerlib_domain] theorem ContinuousLimit.value_perUnit (c : ContinuousLimit) {P : ℝ}
    (hP : 0 < P) (Pmax Pact : ℝ) :
    ({ c with absolute := c.absolute / P } : ContinuousLimit).value (Pmax / P) (Pact / P) =
      c.value Pmax Pact / P := by
  simp only [ContinuousLimit.value, mul_div_assoc', max_div_div_right hP.le]

/-- Compliance does not depend on the base: the per-unit record under the per-unit clauses has
the same exceedance patterns, hence the same verdict on every clause. -/
@[tmio IO, powerlib_domain] theorem compliant_perUnit {P : ℝ} (hP : 0 < P) :
    Compliant (C.perUnit P) (R.perUnit hP) ↔ Compliant C R := by
  have hA : aExceeds (C.perUnit P) (R.perUnit hP) = aExceeds C R := by
    funext k
    show (R.assessed k ∧ ({ C.a with absolute := C.a.absolute / P } : ContinuousLimit).value
      (R.Pmax / P) (R.pAct k / P) < R.amp k / P) = _
    rw [ContinuousLimit.value_perUnit C.a hP, div_lt_div_iff_of_pos_right hP]
    rfl
  have hB : bExceeds (C.perUnit P) (R.perUnit hP) = bExceeds C R := by
    funext k
    show (aExceeds (C.perUnit P) (R.perUnit hP) k ∧ C.b₁ * (R.Pmax / P) < R.amp k / P) = _
    rw [hA, ← mul_div_assoc, div_lt_div_iff_of_pos_right hP]
    rfl
  have hB3 : ∀ k, (R.amp k / P ≤ C.b₃ * (R.Pmax / P)) ↔ R.amp k ≤ C.b₃ * R.Pmax := fun k => by
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hP]
  show (events R.m (bExceeds (C.perUnit P) (R.perUnit hP)) R.t (Set.Ici C.dB) = ∅ ∧
      (∀ e ∈ envelopes R.m (aExceeds (C.perUnit P) (R.perUnit hP)), duration R.t e ≤ C.b₂) ∧
      (∀ e ∈ envelopes R.m (aExceeds (C.perUnit P) (R.perUnit hP)), ∀ k, e.1 ≤ k → k ≤ e.2 →
        R.t e.1 + C.t₃ ≤ R.t k → R.amp k / P ≤ C.b₃ * (R.Pmax / P)) ∧
      (∀ d < R.days, eventTime R.m (fun k => aExceeds (C.perUnit P) (R.perUnit hP) k ∧
        InWindow R 86400 d k) R.t (Set.Ioi C.dC) ≤ C.c₁ * 86400) ∧
      nearestRank C.q (fun h : Fin (24 * R.days) => eventCount R.m (fun k =>
        aExceeds (C.perUnit P) (R.perUnit hP) k ∧ InWindow R 3600 h k) R.t (Set.Ioi C.dC)) ≤
        C.c₂) ↔ _
  simp only [hA, hB, hB3]
  rfl

/-! ## Records built from samples -/

/-- The record of `N` samples `y` (period `h`) of the band-pass filtered active power, with actual
production `P` and assessed samples `M`: its peaks are the local maxima of `|y|`
(`Signal.peakIndex`). -/
def Record.ofSamples (Pmax : ℝ) (days N : ℕ) (h : ℝ) (y P : ℕ → ℝ) (M : ℕ → Prop)
    (hPmax : 0 ≤ Pmax) (hP : ∀ k, 0 ≤ P k) (hh : 0 ≤ h) : Record where
  Pmax := Pmax
  days := days
  m := numPeaks y N
  t := fun i => h * peakIndex y N i
  amp := fun i => |y (peakIndex y N i)|
  pAct := fun i => P (peakIndex y N i)
  assessed := fun i => M (peakIndex y N i)
  Pmax_nonneg := hPmax
  pAct_nonneg := fun _ => hP _
  times_mono := timesMono_peaks hh

/-- A sampled record within the continuous limit at every assessed sample respects clause a, hence
(`compliant_of_clauseA`) every clause. -/
@[tmio IO, powerlib_domain] theorem clauseA_ofSamples {Pmax : ℝ} {days N : ℕ} {h : ℝ}
    {y P : ℕ → ℝ} {M : ℕ → Prop} (hPmax : 0 ≤ Pmax) (hP : ∀ k, 0 ≤ P k) (hh : 0 ≤ h)
    (hy : ∀ k, M k → |y k| ≤ C.a.value Pmax (P k)) :
    ClauseA C (Record.ofSamples Pmax days N h y P M hPmax hP hh) :=
  fun _ _ hk => (hy _ hk.1).not_gt hk.2

/-! ## Decay-rate form of b(ii) and b(iii) -/

/-- b(ii) for a decaying mode: the envelope `A₀ e^{−ζ ω_n t}` (`0 < a < A₀`, `ω_n > 0`, `ζ > 0`)
stays above the continuous limit `a` for `log (A₀ / a) / (ζ ω_n)`
(`Signal.lt_mul_exp_neg_iff`), so b(ii) holds exactly when the damping ratio is at least
`log (A₀ / a) / (ω_n b₂)`. -/
@[tmio M, powerlib_domain] theorem clauseB2_decay_iff {A₀ a ζ ωn : ℝ} (ha : 0 < a) (hA : a < A₀)
    (hζ : 0 < ζ) (hωn : 0 < ωn) (hb : 0 < C.b₂) :
    (∀ t, 0 ≤ t → a < A₀ * Real.exp (-(ζ * ωn * t)) → t ≤ C.b₂) ↔
      Real.log (A₀ / a) / (ωn * C.b₂) ≤ ζ := by
  rw [forall_exceed_le_iff ha hA (mul_pos hζ hωn) hb, div_le_iff₀ hb,
    div_le_iff₀ (mul_pos hωn hb)]
  constructor <;> intro h <;> linarith

/-- b(iii) for a decaying mode: `A₀ e^{−ζ ω_n t₃} ≤ b₃ P_max` exactly when
`ζ ≥ log (A₀ / (b₃ P_max)) / (ω_n t₃)`. -/
@[tmio M, powerlib_domain] theorem clauseB3_decay_iff {A₀ ζ ωn P : ℝ} (hb : 0 < C.b₃ * P)
    (hA : 0 < A₀) (hζ : 0 < ζ) (hωn : 0 < ωn) (ht : 0 < C.t₃) :
    A₀ * Real.exp (-(ζ * ωn * C.t₃)) ≤ C.b₃ * P ↔
      Real.log (A₀ / (C.b₃ * P)) / (ωn * C.t₃) ≤ ζ := by
  rw [mul_exp_le_iff hb hA (mul_pos hζ hωn) ht, div_le_iff₀ ht, div_le_iff₀ (mul_pos hωn ht)]
  constructor <;> intro h <;> linarith

/-- With `b₂ = 2 t₃` (every column of Appendix A), b(ii) implies b(iii) for an exponentially
decaying oscillation of initial amplitude `A₀` under the continuous limit `a` whenever
`A₀ a ≤ (b₃ P_max)²` (`Signal.mul_exp_le_of_rate`). -/
@[tmio M, powerlib_domain] theorem clauseB3_of_clauseB2_decay {A₀ a σ P : ℝ} (ha : 0 < a)
    (hA : a < A₀) (hσ : 0 < σ) (hb : 0 < C.b₃ * P) (ht : 0 < C.t₃) (h₂₃ : C.b₂ = 2 * C.t₃)
    (hprod : A₀ * a ≤ (C.b₃ * P) ^ 2)
    (h2 : ∀ t, 0 ≤ t → a < A₀ * Real.exp (-(σ * t)) → t ≤ C.b₂) :
    A₀ * Real.exp (-(σ * C.t₃)) ≤ C.b₃ * P :=
  mul_exp_le_of_rate ha hA hσ hb ht h₂₃ hprod
    ((forall_exceed_le_iff ha hA hσ (by rw [h₂₃]; positivity)).mp h2)

/-- Record form of b(ii): if the exceedances of the continuous limit occur after the onset `t₀` of
an oscillation whose peaks are bounded by `A₀ e^{−σ (t − t₀)}`, and the limit is at least `ℓ > 0`,
every exceedance lasts less than `log (A₀ / ℓ) / σ`; b(ii) holds when this is at most `b₂`. -/
@[tmio IO, powerlib_domain] theorem clauseB2_of_decay {t₀ ℓ A₀ σ : ℝ} (hℓ : 0 < ℓ) (hσ : 0 < σ)
    (hlim : ∀ k < R.m, ℓ ≤ C.a.value R.Pmax (R.pAct k))
    (honset : ∀ k < R.m, aExceeds C R k → t₀ ≤ R.t k)
    (hdecay : ∀ k < R.m, aExceeds C R k → R.amp k ≤ A₀ * Real.exp (-(σ * (R.t k - t₀))))
    (hb : Real.log (A₀ / ℓ) / σ ≤ C.b₂) : ClauseB2 C R := fun e he =>
  (duration_lt_of_exp_bound hℓ hσ (fun k hk hx => ⟨honset k hk hx, (hlim k hk).trans_lt hx.2⟩)
    hdecay e he).le.trans hb

/-- Record form of b(iii): if the exceedances start after the onset `t₀` and all later peaks are
bounded by `A₀ e^{−σ (t − t₀)}` with `A₀ e^{−σ t₃} ≤ b₃ P_max`, b(iii) holds. -/
@[tmio IO, powerlib_domain] theorem clauseB3_of_decay {t₀ A₀ σ : ℝ} (hA₀ : 0 ≤ A₀) (hσ : 0 ≤ σ)
    (honset : ∀ k < R.m, aExceeds C R k → t₀ ≤ R.t k)
    (hdecay : ∀ k < R.m, t₀ ≤ R.t k → R.amp k ≤ A₀ * Real.exp (-(σ * (R.t k - t₀))))
    (hb : A₀ * Real.exp (-(σ * C.t₃)) ≤ C.b₃ * R.Pmax) : ClauseB3 C R := by
  intro e he k hk1 hk2 hk
  obtain ⟨hij, hjm, hrun, -, -⟩ := mem_envelopes.mp he
  have h0 := honset e.1 (hij.trans_lt hjm) (hrun e.1 le_rfl hij)
  have hmono := R.times_mono e.1 k hk1 (hk2.trans_lt hjm)
  refine (hdecay k (hk2.trans_lt hjm) (h0.trans hmono)).trans (le_trans ?_ hb)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA₀
  have : C.t₃ ≤ R.t k - t₀ := by linarith
  nlinarith

/-! ## Set-point steps through the band-pass filter (§5.1 Fig. 11, §5.6) -/

/-- A set-point step seen through a stable band-pass filter decays like `M e^{−r (t − t_s)}`
(`Signal.exists_output_bound`). If the b(i) exceedances it causes occur after the step time `t_s`,
each lasts less than `log (M / (b₁ P_max)) / r`; a b(i) minimum duration `dB` of at least that
length removes them. -/
@[tmio IO, powerlib_domain] theorem clauseB1_of_step {ts M r : ℝ} (hr : 0 < r)
    (hb₁ : 0 < C.b₁ * R.Pmax) (honset : ∀ k < R.m, bExceeds C R k → ts ≤ R.t k)
    (hstep : ∀ k < R.m, bExceeds C R k → R.amp k ≤ M * Real.exp (-(r * (R.t k - ts))))
    (hdB : Real.log (M / (C.b₁ * R.Pmax)) / r ≤ C.dB) : ClauseB1 C R := by
  refine eq_empty_of_forall_notMem fun e he => ?_
  obtain ⟨henv, hS⟩ := mem_events.mp he
  have := duration_lt_of_exp_bound hb₁ hr (fun k hk hx => ⟨honset k hk hx, hx.2⟩) hstep e
    (mem_envelopes.mpr henv)
  exact absurd (hS : C.dB ≤ duration R.t e) (not_le.mpr (this.trans_le hdB))

/-! ## Small onshore modules: the absolute floor above the b(i) limit -/

/-- If the b(i) limit `b₁ P_max` is not above the absolute floor of the continuous limit, every
exceedance of the continuous limit is a b(i) exceedance. -/
@[tmio IO, powerlib_domain] theorem bExceeds_iff_aExceeds (h : C.b₁ * R.Pmax ≤ C.a.absolute)
    (k : ℕ) : bExceeds C R k ↔ aExceeds C R k :=
  ⟨fun hk => hk.1, fun hk => ⟨hk, h.trans_lt ((le_max_right _ _).trans_lt hk.2)⟩⟩

/-- For such a module, with `dB ≤ 0` (every b(i) exceedance counted), b(i) is clause a itself:
the temporary-exceedance allowance of b(ii) is void. -/
@[tmio IO, powerlib_domain] theorem clauseB1_iff_clauseA (h : C.b₁ * R.Pmax ≤ C.a.absolute)
    (hdB : C.dB ≤ 0) : ClauseB1 C R ↔ ClauseA C R := by
  constructor
  · intro hb k hk hx
    obtain ⟨i, j, henv, -, -⟩ := exists_envelope hk ((bExceeds_iff_aExceeds h k).mpr hx)
    have hmem : (i, j) ∈ events R.m (bExceeds C R) R.t (Set.Ici C.dB) :=
      mem_events.mpr ⟨henv, hdB.trans (henv.duration_nonneg R.times_mono)⟩
    rw [ClauseB1] at hb
    simp [hb] at hmem
  · intro ha
    rw [ClauseB1, events, envelopes_eq_empty fun k hk hx => ha k hk hx.1, filter_empty]

/-- For the onshore form the b(i) limit `b₁ P_max` is not above the absolute floor `A` exactly when
`P_max ≤ A / b₁` (`b₁ > 0`). -/
@[tmio M, powerlib_domain] theorem onshore_floor_iff {a₁ A P : ℝ} (hb : 0 < C.b₁)
    (ha : C.a = ContinuousLimit.onshore a₁ A) : C.b₁ * P ≤ C.a.absolute ↔ P ≤ A / C.b₁ := by
  rw [ha, le_div_iff₀ hb, mul_comm]
  rfl

/-! ## The Appendix A values -/

/-- The default and least strict offshore columns have `b₂ = 2 t₃`; for the default column
`b₁ · a(i) = b₃²` exactly (`4 % · 1 % = (2 %)²`), for the least strict column `b₁ · a(i) > b₃²`
(`5 % · 2 % > (2.5 %)²`). -/
@[tmio M, powerlib_domain] theorem offshore_b_product :
    offshoreDefault.b₂ = 2 * offshoreDefault.t₃ ∧
      offshoreDefault.b₁ * offshoreDefault.a.actual = offshoreDefault.b₃ ^ 2 ∧
      offshoreLeastStrict.b₂ = 2 * offshoreLeastStrict.t₃ ∧
      offshoreLeastStrict.b₃ ^ 2 < offshoreLeastStrict.b₁ * offshoreLeastStrict.a.actual := by
  simp only [offshoreDefault, offshoreLeastStrict, ContinuousLimit.offshore]
  norm_num

/-- c(i) default: `1 %` of a day is `864 s = 00:14:24`. -/
@[tmio M, powerlib_domain] theorem offshoreDefault_c1 :
    offshoreDefault.c₁ * 86400 = 864 ∧ (864 : ℝ) = 14 * 60 + 24 := by
  simp only [offshoreDefault]
  norm_num

/-- Onshore default: the b(i) limit `2.5 % P_max` is not above the floor `A` exactly for
`P_max ≤ 40 A` (`20 MW` for `A = 500 kW`). -/
@[tmio M, powerlib_domain] theorem onshoreDefault_floor_iff (A P : ℝ) :
    (onshoreDefault A).b₁ * P ≤ (onshoreDefault A).a.absolute ↔ P ≤ 40 * A := by
  rw [onshore_floor_iff (by simp only [onshoreDefault]; norm_num) rfl]
  simp only [onshoreDefault]
  constructor <;> intro h <;> linarith

/-! ## Aggregation of sites (§4.1, Site12) -/

/-- A purely capacity-relative continuous limit (`α P_max`) is never violated by an aggregate of
compliant sites (`Signal.abs_sum_le_mul_sum`). -/
@[tmio IO, powerlib_domain] theorem aggregate_capacity {ι : Type*} (s : Finset ι)
    {y Pmax Pact : ι → ℝ} {α : ℝ}
    (h : ∀ i ∈ s, |y i| ≤ (ContinuousLimit.mk 0 α 0).value (Pmax i) (Pact i))
    (hα : ∀ i ∈ s, 0 ≤ α * Pmax i) :
    |∑ i ∈ s, y i| ≤ (ContinuousLimit.mk 0 α 0).value (∑ i ∈ s, Pmax i) (∑ i ∈ s, Pact i) := by
  have hv : ∀ P Q : ℝ, 0 ≤ α * P → (ContinuousLimit.mk 0 α 0).value P Q = α * P := fun P Q hP => by
    simp [ContinuousLimit.value, hP]
  have hsum : 0 ≤ α * ∑ i ∈ s, Pmax i := by rw [mul_sum]; exact sum_nonneg hα
  rw [hv _ _ hsum]
  exact abs_sum_le_mul_sum s fun i hi => (h i hi).trans_eq (hv _ _ (hα i hi))

/-- The offshore form `max(a₁ P_actual, a₂ P_max)` is not preserved by aggregation: two sites of
capacity `P`, one at full production and one idle, each oscillating in phase exactly at its own
limit (`a₁ P` and `a₂ P`), aggregate to `(a₁ + a₂) P`, above the aggregate limit
`max(a₁ P, 2 a₂ P)` whenever `0 < a₂ < a₁` (default: `1 %`, `0.5 %`). -/
@[tmio IO, powerlib_domain] theorem aggregate_offshore_violation {a₁ a₂ P : ℝ} (ha₂ : 0 < a₂)
    (h : a₂ < a₁) (hP : 0 < P) :
    (ContinuousLimit.offshore a₁ a₂).value P P = a₁ * P ∧
      (ContinuousLimit.offshore a₁ a₂).value P 0 = a₂ * P ∧
      (ContinuousLimit.offshore a₁ a₂).value (P + P) (P + 0) < a₁ * P + a₂ * P := by
  have hx : a₂ * P < a₁ * P := mul_lt_mul_of_pos_right h hP
  have hy : 0 < a₂ * P := mul_pos ha₂ hP
  refine ⟨?_, ?_, ?_⟩
  · rw [ContinuousLimit.offshore_value hy.le, max_eq_left hx.le]
  · rw [ContinuousLimit.offshore_value hy.le, mul_zero, max_eq_right hy.le]
  · rw [ContinuousLimit.offshore_value (by positivity), add_zero, max_lt_iff]
    constructor <;> nlinarith

/-- The onshore absolute floor is not preserved by aggregation either: two sites of capacity `P`
with `a₁ P < A`, each oscillating at the floor `A`, aggregate to `2A`, above the aggregate limit
`max(2 a₁ P, A)`. -/
@[tmio IO, powerlib_domain] theorem aggregate_onshore_violation {a₁ A P : ℝ} (ha : 0 ≤ a₁ * P)
    (h : a₁ * P < A) :
    (ContinuousLimit.onshore a₁ A).value P 0 = A ∧
      (ContinuousLimit.onshore a₁ A).value (P + P) (0 + 0) < A + A := by
  refine ⟨by rw [ContinuousLimit.onshore_value ha, max_eq_right h.le], ?_⟩
  rw [ContinuousLimit.onshore_value (by linarith), max_lt_iff]
  constructor <;> linarith

/-- Cancellation (Site12): two sites of capacity `P` oscillating in antiphase, each above the
capacity-relative limit `α P`, aggregate to `0`, within the aggregate limit. -/
@[tmio IO, powerlib_domain] theorem aggregate_cancel {v α P Q : ℝ}
    (hv : (ContinuousLimit.mk 0 α 0).value P Q < |v|) :
    (ContinuousLimit.mk 0 α 0).value P Q < |-v| ∧
      |v + -v| ≤ (ContinuousLimit.mk 0 α 0).value (P + P) (Q + Q) := by
  refine ⟨by rwa [abs_neg], ?_⟩
  rw [add_neg_cancel, abs_zero]
  exact (le_max_right _ _)

end powerlib.ForcedOscillation
