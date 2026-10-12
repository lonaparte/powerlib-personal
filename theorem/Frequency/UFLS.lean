import theorem.Frequency.SwingNadir

/-! # Under-frequency load shedding (UFLS): conditions, estimates, corrected trip logic

Source: work-sync `theory/T-ufls.md` §1.1 (single-stage threshold shedding), §1.2 (staged
shedding with confirmation delay), §1.4 ("切赢了" condition), §1.5 (load estimate from RoCoF).

Model boundary for the domain statements: the two-state swing + governor model
`Frequency.SwingGovernor.model` (state `(Δω, ΔP_m)`, continuous time, linear, Kundur per-unit,
`M = 2H`, `Δω` per-unit, `f = f₀(1 + Δω)`), load step applied at `t = 0` to the system at rest.
Shedding a fraction `p` of the pre-disturbance load `P⁰` turns the step `ΔP_L` into
`ΔP_L − p P⁰`; the statements below about the post-shedding system take that reduced step as
the model input (shedding at `t = 0`, the most favourable timing). No turbine, AGC, PLL, delay,
dead-band, voltage dynamics or frequency-dependent load beyond `D`.

Results.
* `postShed_steadyState_above_iff` (foundation) and `postShed_necessary` (private): the
  post-shedding frequency can stay above the threshold `−Δf_th` only if
  `ΔP_L − p P⁰ ≤ (K_R + D) Δf_th / f₀` (strictly: the steady state is above the threshold iff
  `ΔP_L − p P⁰ < (K_R + D) Δf_th / f₀`).
  Correction: §1.4 states the condition as `ΔP_L − p ΔP_L⁰ < D_eff Δf_th`; the primary
  response `K_R` is missing and `Δf_th` [Hz] must be converted to per-unit (`/ f₀`).
* `postShed_not_sufficient` (private): the condition is not sufficient: in the underdamped case
  there are thresholds for which the steady state is above `−Δf_th` while the frequency nadir
  (`SwingGovernor.nadir`) still crosses it (overshoot).
* `load_eq_of_rocof` (private, §1.5): the initial RoCoF determines the step exactly,
  `ΔP_L = M |ḟ(0⁺)| / f₀`. Correction (`noteLoadEstimate_ne`): the note's
  `ΔP_L ≈ M_eff |ḟ| · 2π` is wrong by the factor `2π f₀` (it would only be right for
  `f₀ = 1/(2π)`).
* Trip logic (foundation, §1.1–§1.2). The note's single-stage indicator `1[Δf(t) ≤ −Δf_th]`
  is not latched: it re-connects the load as soon as the frequency recovers
  (`instantTrip_not_latched`). The corrected latched indicator is
  `1[min_{0 ≤ τ ≤ t} Δf(τ) ≤ −Δf_th]`, i.e. `∃ τ ∈ [0, t], Δf(τ) ≤ −Δf_th`
  (`latchedTrip_iff_sInf`, `latchedTrip_mono`). The note's confirmation-delay rule
  `1[inf_{τ∈[t−τ_d,t]} Δf(τ) ≤ −Δf_i]` trips on a single touch of the threshold
  (`windowInfTrip_single_touch`), i.e. it provides no confirmation; the corrected rule requires
  the whole window below the threshold, `1[sup_{τ∈[t−τ_d,t]} Δf(τ) ≤ −Δf_i]`, i.e.
  `∀ τ ∈ [t − τ_d, t], Δf(τ) ≤ −Δf_i` (`confirmedTrip_iff_sSup`). These window conditions on
  the record are written out in the statements (behavioural notions are defined only in the
  semantic layer).

Family and connection conclusions. This module adds no family; the plant is the swing + governor
plant of `Frequency.SwingGovernor`, whose family publishes the stability conclusions. The
shedding statements quantify over forward solutions under a load step (eventual bounds,
excursions, initial slope), which the sentence language does not express: `postShed_necessary`,
`postShed_not_sufficient` and `load_eq_of_rocof` (formerly `@[powerlib_domain]`) are private
implementation evidence (Rules §3a). They are derived from the generic
`Frequency.tendsto_apply_of_isHurwitz`, `Frequency.trajectory_eq_osc2`,
`Frequency.hasDerivWithinAt_apply_zero` and static facts of the plant. The steady-state
inequality, the corrected load estimate and the trip logic are foundation.
-/

noncomputable section
namespace powerlib.Frequency.UFLS
open Set Filter Matrix
open scoped Topology

open SwingGovernor (plant)

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

variable {M D K Tg ΔPL f₀ th : ℝ}

/-! ## Post-shedding steady state: necessary, not sufficient -/

/-- The post-shedding steady state `−ΔP'/(K_R + D)` lies strictly above the threshold
`−Δf_th/f₀` iff `ΔP' < (K_R + D) Δf_th / f₀`. -/
@[powerlib_foundation] theorem postShed_steadyState_above_iff {ΔP' : ℝ} (hKD : 0 < K + D)
    (hf : 0 < f₀) : -(th / f₀) < -ΔP' / (K + D) ↔ ΔP' < (K + D) * th / f₀ := by
  rw [neg_div, neg_lt_neg_iff, div_lt_div_iff₀ hKD hf, lt_div_iff₀ hf]
  constructor <;> intro h <;> linarith

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
Necessary condition: if after shedding (`ΔP' = ΔP_L − p P⁰`) the frequency eventually stays at or
above `−Δf_th/f₀`, then `ΔP' ≤ (K_R + D) Δf_th / f₀`. -/
private theorem postShed_necessary {ΔP' : ℝ} (hM : 0 < M) (hTg : 0 < Tg)
    (hD : 0 ≤ D) (hKD : 0 < K + D) (hf : 0 < f₀) {x : ℝ → ℝ²}
    (hx : IsIntegralCurveOn x (fun _ y => (plant M D K Tg).inputField (load ΔP') y) (Ici 0))
    (hev : ∀ᶠ t in atTop, -(th / f₀) ≤ x t 0) : ΔP' ≤ (K + D) * th / f₀ := by
  have hlim := tendsto_apply_of_isHurwitz (plant M D K Tg)
    (SwingGovernor.steadyState_isEquilibrium hM.ne' hTg.ne' hKD.ne')
    ((SwingGovernor.isHurwitz_iff_of_nonneg hM hTg hD).2 hKD) hx 0
  rw [SwingGovernor.steadyState_zero] at hlim
  have h := ge_of_tendsto hlim hev
  rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ hKD hf] at h
  rw [le_div_iff₀ hf]
  linarith

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
The steady-state condition is not sufficient: with an underdamped response there is a threshold
`Δf_th > 0` with `ΔP' < (K_R + D) Δf_th / f₀` (steady state above the threshold) while the
frequency of the forward solution from rest still goes below `−Δf_th/f₀` (at the nadir). -/
private theorem postShed_not_sufficient {ΔP' : ℝ} (hM : 0 < M) (hTg : 0 < Tg)
    (hD : 0 ≤ D) (hKD : 0 < K + D) (hP : 0 < ΔP') (hf : 0 < f₀)
    (hζ : SwingGovernor.dampingRatio M D K Tg < 1) {x : ℝ → ℝ²}
    (hx : IsIntegralCurveOn x (fun _ y => (plant M D K Tg).inputField (load ΔP') y) (Ici 0))
    (h0 : x 0 = 0) :
    ∃ th > 0, ΔP' < (K + D) * th / f₀ ∧ ∃ t ≥ 0, x t 0 < -(th / f₀) := by
  have hωd := SwingGovernor.dampedFreq_pos hM hTg hD hKD hζ
  have hT0 : 0 < SwingGovernor.nadirTime M D K Tg := SwingGovernor.tCrit_pos hωd
  have hval : x (SwingGovernor.nadirTime M D K Tg) 0 = SwingGovernor.nadirValue M D K Tg ΔP' := by
    rw [trajectory_eq_osc2 (plant M D K Tg)
      (SwingGovernor.steadyState_isEquilibrium hM.ne' hTg.ne' hKD.ne')
      (SwingGovernor.trace_A hM hTg hKD) (SwingGovernor.det_A hM hTg hD hKD hζ) hωd.ne' hx
      hT0.le, h0, SwingGovernor.osc2_freq hM hTg hD hKD hζ,
      SwingGovernor.respC_nadirTime hM hTg hD hKD hζ]
  have hlt := SwingGovernor.nadirValue_lt hM hTg hD hKD hP hζ
  set n := SwingGovernor.nadirValue M D K Tg ΔP'
  set c := ΔP' / (K + D) with hc
  have hc0 : 0 < c := div_pos hP hKD
  have hnc : n < -c := by rw [hc, ← neg_div]; exact hlt
  refine ⟨f₀ * ((c - n) / 2), by nlinarith, ?_, SwingGovernor.nadirTime M D K Tg, hT0.le, ?_⟩
  · rw [mul_div_assoc, mul_div_cancel_left₀ _ hf.ne']
    have : ΔP' = (K + D) * c := by rw [hc]; field_simp
    rw [this]
    nlinarith
  · have : f₀ * ((c - n) / 2) / f₀ = (c - n) / 2 := by field_simp
    rw [hval, this]
    linarith

/-! ## Load estimate from the initial RoCoF (§1.5) -/

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
§1.5 corrected: `ΔP_L = M |ḟ(0⁺)| / f₀` for a load increase `ΔP_L ≥ 0`. -/
private theorem load_eq_of_rocof (hM : 0 < M) (hf : 0 < f₀) (hP : 0 ≤ ΔPL)
    {x : ℝ → ℝ²}
    (hx : IsIntegralCurveOn x (fun _ y => (plant M D K Tg).inputField (load ΔPL) y) (Ici 0))
    (h0 : x 0 = 0) {ρ : ℝ} (hρ : HasDerivWithinAt (fun t => f₀ * (1 + x t 0)) ρ (Ici 0) 0) :
    ΔPL = M * |ρ| / f₀ := by
  have hr : HasDerivWithinAt (fun t => x t 0) (-ΔPL / M) (Ici 0) 0 := by
    have h := hasDerivWithinAt_apply_zero hx 0
    rw [SwingGovernor.field_apply, h0] at h
    convert h using 1
    simp only [Fin.isValue, Matrix.cons_val_zero, PiLp.zero_apply]
    ring
  have h := (hr.const_add 1).const_mul f₀
  have hρ' : ρ = f₀ * (-ΔPL / M) := (uniqueDiffWithinAt_Ici 0).eq_deriv _ hρ h
  rw [hρ', abs_mul, abs_of_pos hf, abs_div, abs_neg, abs_of_nonneg hP, abs_of_pos hM]
  field_simp

/-- Correction: the note's estimate `M |ḟ| · 2π` differs from `ΔP_L > 0` unless `2π f₀ = 1`. -/
@[powerlib_foundation] theorem noteLoadEstimate_ne {ρ : ℝ} (hM : 0 < M) (hf : 0 < f₀)
    (hP : 0 < ΔPL) (hρ : ΔPL = M * |ρ| / f₀) (h2π : 2 * Real.pi * f₀ ≠ 1) :
    M * |ρ| * (2 * Real.pi) ≠ ΔPL := by
  intro h
  have h1 : M * |ρ| = ΔPL * f₀ := by rw [hρ]; field_simp
  rw [h1] at h
  apply h2π
  have : ΔPL * (f₀ * (2 * Real.pi)) = ΔPL * 1 := by linarith
  have := mul_left_cancel₀ hP.ne' this
  linarith

/-! ## Trip logic (§1.1–§1.2)

Trip rules on a frequency record `Δf` at time `t`, written out in the statements:
* corrected latched indicator `min_{0 ≤ τ ≤ t} Δf(τ) ≤ −Δf_th`: `∃ τ ∈ [0, t], Δf τ ≤ −th`;
* the note's §1.2 confirmation rule `inf_{τ ∈ [t−τ_d, t]} Δf(τ) ≤ −Δf_i`:
  `∃ τ ∈ [t − τ_d, t], Δf τ ≤ −th`;
* corrected confirmation rule `sup_{τ ∈ [t−τ_d, t]} Δf(τ) ≤ −Δf_i`:
  `∀ τ ∈ [t − τ_d, t], Δf τ ≤ −th`. -/

/-- The note's §1.1 indicator `1[Δf(t) ≤ −Δf_th]` (not latched). -/
def instantTrip (Δf : ℝ → ℝ) (th t : ℝ) : Prop := Δf t ≤ -th

/-- A latched trip stays tripped: `min_{0 ≤ τ ≤ t} Δf(τ) ≤ −Δf_th` persists for `t' ≥ t`. -/
@[powerlib_foundation] theorem latchedTrip_mono {Δf : ℝ → ℝ} {t t' : ℝ} (htt : t ≤ t')
    (h : ∃ τ ∈ Icc 0 t, Δf τ ≤ -th) : ∃ τ ∈ Icc 0 t', Δf τ ≤ -th := by
  obtain ⟨τ, hτ, hle⟩ := h
  exact ⟨τ, ⟨hτ.1, hτ.2.trans htt⟩, hle⟩

/-- For a continuous frequency record the latched trip (`Δf` at or below `−Δf_th` somewhere on
`[0, t]`) is the `min` rule. -/
@[powerlib_foundation] theorem latchedTrip_iff_sInf {Δf : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hc : ContinuousOn Δf (Icc 0 t)) :
    (∃ τ ∈ Icc 0 t, Δf τ ≤ -th) ↔ sInf (Δf '' Icc 0 t) ≤ -th := by
  have hK : IsCompact (Δf '' Icc 0 t) := isCompact_Icc.image_of_continuousOn hc
  have hne : (Δf '' Icc 0 t).Nonempty := (nonempty_Icc.2 ht).image Δf
  constructor
  · rintro ⟨τ, hτ, hle⟩
    exact (csInf_le hK.bddBelow (mem_image_of_mem Δf hτ)).trans hle
  · intro h
    obtain ⟨τ, hτ, heq⟩ := hK.sInf_mem hne
    exact ⟨τ, hτ, heq ▸ h⟩

/-- For a continuous frequency record the corrected confirmation rule (`Δf` at or below
`−Δf_i` on the whole window `[t − τ_d, t]`) is the `sup` rule. -/
@[powerlib_foundation] theorem confirmedTrip_iff_sSup {Δf : ℝ → ℝ} {τd t : ℝ} (hτ : 0 ≤ τd)
    (hc : ContinuousOn Δf (Icc (t - τd) t)) :
    (∀ τ ∈ Icc (t - τd) t, Δf τ ≤ -th) ↔ sSup (Δf '' Icc (t - τd) t) ≤ -th := by
  have hK : IsCompact (Δf '' Icc (t - τd) t) := isCompact_Icc.image_of_continuousOn hc
  have hne : (Δf '' Icc (t - τd) t).Nonempty :=
    (nonempty_Icc.2 (by linarith)).image Δf
  rw [csSup_le_iff hK.bddAbove hne]
  constructor
  · rintro h _ ⟨τ, hτ, rfl⟩
    exact h τ hτ
  · intro h τ hτ
    exact h _ (mem_image_of_mem Δf hτ)

/-- The corrected rule (whole window below the threshold) implies the note's rule (some
instant of the window below it) and, after `τ_d`, the latched trip. -/
@[powerlib_foundation] theorem confirmedTrip_imp {Δf : ℝ → ℝ} {τd t : ℝ} (hτ : 0 ≤ τd)
    (h : ∀ τ ∈ Icc (t - τd) t, Δf τ ≤ -th) :
    (∃ τ ∈ Icc (t - τd) t, Δf τ ≤ -th) ∧ (τd ≤ t → ∃ τ ∈ Icc 0 t, Δf τ ≤ -th) := by
  refine ⟨⟨t, ⟨by linarith, le_rfl⟩, h t ⟨by linarith, le_rfl⟩⟩, fun hle => ?_⟩
  exact ⟨t, ⟨hτ.trans hle, le_rfl⟩, h t ⟨by linarith, le_rfl⟩⟩

/-- The note's §1.1 indicator is not latched: a record that dips below the threshold and
recovers (`Δf(t) = −2 Δf_th + 3 Δf_th t`) trips at `t = 0` and un-trips at `t = 1`, while the
latched indicator stays tripped. -/
@[powerlib_foundation] theorem instantTrip_not_latched (hth : 0 < th) :
    instantTrip (fun t => -2 * th + 3 * th * t) th 0 ∧
      ¬ instantTrip (fun t => -2 * th + 3 * th * t) th 1 ∧
      ∃ τ ∈ Icc (0 : ℝ) 1, -2 * th + 3 * th * τ ≤ -th := by
  refine ⟨?_, ?_, ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩⟩ <;> (try simp only [instantTrip]) <;> linarith

/-- The note's `inf` confirmation rule trips on a single touch of the threshold: the record
`Δf(τ) = −Δf_th + Δf_th |τ − 1|` is at or below `−Δf_th` only at `τ = 1`, yet the `inf` rule
(some instant of `[t − τ_d, t]` below the threshold) trips at `t = 1 + τ_d`; the corrected `sup`
rule (the whole window below it) does not. -/
@[powerlib_foundation] theorem windowInfTrip_single_touch {τd : ℝ} (hth : 0 < th)
    (hτ : 0 < τd) :
    (∀ τ, -th + th * |τ - 1| ≤ -th → τ = 1) ∧
      (∃ τ ∈ Icc (1 + τd - τd) (1 + τd), -th + th * |τ - 1| ≤ -th) ∧
      ¬ ∀ τ ∈ Icc (1 + τd - τd) (1 + τd), -th + th * |τ - 1| ≤ -th := by
  refine ⟨fun τ hτ' => ?_, ⟨1, ⟨by linarith, by linarith⟩, by simp⟩, fun h => ?_⟩
  · have h1 : th * |τ - 1| ≤ 0 := by linarith
    have h2 : |τ - 1| ≤ 0 := by
      by_contra hc; push Not at hc; nlinarith
    have := abs_nonpos_iff.1 h2
    linarith
  · have := h (1 + τd) ⟨by linarith, le_rfl⟩
    simp only [add_sub_cancel_left, abs_of_pos hτ] at this
    nlinarith

end powerlib.Frequency.UFLS
