import theorem.Dynamics.Calculus
import dependencies.Mathlib

/-! # Charging of the secondary DC link under the DC-current limit

The secondary bridge of the lossless resonant link feeds its DC link, a capacitor `C > 0` in
parallel with a resistive load `R_L > 0`. On the time scale of the DC voltage `v(t)` the bridge is
a source of the average DC current `i(t)`, and the capacitor obeys
`C v'(t) = i(t) − v(t)/R_L`. Seen from the DC port, the link is current-limited:
`i(t) ≤ Ī` with `Ī = 8 V_dc1/(π²|ωM|)`, the exact largest secondary DC current of
`DCSide.isGreatest_dcCurrent` (`theorem/WPT/DCSide.lean`), which does not depend on the DC voltage.
Here `Ī` is kept as an abstract bound, so the results hold for any DC-current limit.

The full-current trajectory `v_Ī(t) = Ī R_L + (v₀ − Ī R_L) e^{−t/(R_L C)}` (`fullCurrent`), the
response to `i ≡ Ī`, bounds every admissible trajectory from above: whatever the bridge does within
its limit, `v(t) ≤ v_Ī(t)` for `t ≥ 0`. Physical reading: the DC link charges fastest with the
bridge at its current limit throughout, and from `v₀` to `v_f` (`v₀ ≤ v_f < Ī R_L`) this takes
exactly `t* = R_L C ln((Ī R_L − v₀)/(Ī R_L − v_f))` (`chargeTime`): the full-current trajectory
reaches `v_f` at `t*` and no admissible trajectory reaches `v_f` earlier. The largest DC voltage the
link can hold in steady state is `Ī R_L`, the load line of the current source; every admissible
trajectory ends up below `Ī R_L + ε` for every `ε > 0`, and from `v(0) < Ī R_L` the voltage stays
strictly below `Ī R_L` at every finite time.

Model boundary.
* Averaged (quasi-static) DC link in continuous time `t : ℝ`: one state, the DC-link voltage
  `v : ℝ → ℝ`; one input, the average DC current `i : ℝ → ℝ` that the secondary bridge delivers to
  the link over an AC period; parameters `C > 0` (DC-link capacitance) and `R_L > 0` (resistive
  load). The trajectory hypotheses are `v' = (i − v/R_L)/C` (one-sided derivatives within `[0, t]`)
  and `i(s) ≤ Ī` on `[0, t]`; nothing is assumed about `i` beyond the bound (no controller, no
  continuity of `i`).
* The AC side is in fundamental-harmonic steady state on the time scale of the DC dynamics: the
  resonant-tank envelope and the switching ripple are not modelled, and the bridge is lossless.
  Reading `Ī` as `8 V_dc1/(π²|ωM|)` uses `DCSide.isGreatest_dcCurrent`, which holds at each fixed
  `V_dc2 > 0` for the lossless resonant link of `theorem/WPT/CurrentLimits.lean`; here the bound
  is a hypothesis at every instant, including instants with `v(t) ≤ 0`, where that theorem says
  nothing. The bound is one-sided: a lower limit on `i` (a diode rectifier has `i ≥ 0`) does not
  enter the statements.
* Statements are plain real analysis about the functions `v`, `i`: no dynamical-system family is
  defined, and no stability property of a closed loop is claimed.

Source: the RC charging law of a capacitor fed by a current source; the DC current limit
`DCSide.isGreatest_dcCurrent` (`theorem/WPT/DCSide.lean`); the linear Grönwall inequality
`Dynamics.le_exp_mul_of_hasDerivWithinAt` (`theorem/Dynamics/Calculus.lean`).

Results.
* `fullCurrent` (`v_Ī(t) = Ī R_L + (v₀ − Ī R_L) e^{−t/(R_L C)}`), `chargeTime`
  (`t* = R_L C ln((Ī R_L − v₀)/(Ī R_L − v_f))`).
* `fullCurrent_solves` (`v_Ī(0) = v₀` and `C v_Ī' = Ī − v_Ī/R_L`: the trajectory of `i ≡ Ī`),
  `tendsto_fullCurrent` (`v_Ī(t) → Ī R_L` as `t → ∞`).
* `le_fullCurrent` (comparison: every trajectory with `i ≤ Ī` on `[0, t]`, `t ≥ 0`, has
  `v(t) ≤ v_Ī(t)` from the same initial voltage), `lt_of_initial_lt` (`v(0) < Ī R_L` gives
  `v(t) < Ī R_L` for `t ≥ 0`).
* `fullCurrent_chargeTime` (`v_Ī(t*) = v_f`), `chargeTime_le` (an admissible trajectory with
  `v(t) ≥ v_f` has `t ≥ t*`), `isLeast_chargeTime` (for `v₀ ≤ v_f < Ī R_L`, `t*` is the least time
  at which an admissible trajectory from `v₀` is at `v_f`).
* `isGreatest_steadyState` (the greatest constant voltage the link holds with `i ≤ Ī` is
  `Ī R_L`), `eventually_le` (every trajectory admissible on `[0, ∞)` is eventually below
  `Ī R_L + ε`).
-/

noncomputable section

namespace powerlib.WPT.DCLink

open Set Filter Topology

/-- The full-current trajectory `Ī R_L + (v₀ − Ī R_L) e^{−t/(R_L C)}`: the DC voltage when the
bridge delivers the DC-current limit `Ī` at every instant, from `v(0) = v₀`. -/
def fullCurrent (R C Ibar v₀ t : ℝ) : ℝ := Ibar * R + (v₀ - Ibar * R) * Real.exp (-t / (R * C))

/-- The minimum charging time `R_L C ln((Ī R_L − v₀)/(Ī R_L − v_f))` from `v₀` to `v_f`. -/
def chargeTime (R C Ibar v₀ vf : ℝ) : ℝ := R * C * Real.log ((Ibar * R - v₀) / (Ibar * R - vf))

variable {R C Ibar : ℝ}

/-- The full-current trajectory starts at `v₀` and solves `C v' = Ī − v/R_L`. -/
@[tmio M, powerlib_domain] theorem fullCurrent_solves (hR : R ≠ 0) (hC : C ≠ 0) (v₀ : ℝ) :
    fullCurrent R C Ibar v₀ 0 = v₀ ∧
      ∀ t, HasDerivAt (fullCurrent R C Ibar v₀) ((Ibar - fullCurrent R C Ibar v₀ t / R) / C) t := by
  refine ⟨by simp [fullCurrent], fun t => ?_⟩
  have h := ((((hasDerivAt_id t).neg.div_const (R * C)).exp).const_mul
    (v₀ - Ibar * R)).const_add (Ibar * R)
  convert h using 1
  · funext x
    simp only [fullCurrent, Pi.neg_apply, id]
  · simp only [fullCurrent, Pi.neg_apply, id]
    field_simp
    ring

/-- With the bridge at its limit the DC voltage tends to `Ī R_L`. -/
@[tmio M, powerlib_domain] theorem tendsto_fullCurrent (hR : 0 < R) (hC : 0 < C) (v₀ : ℝ) :
    Tendsto (fullCurrent R C Ibar v₀) atTop (𝓝 (Ibar * R)) := by
  have h : Tendsto (fun t : ℝ => Real.exp (-t / (R * C))) atTop (𝓝 0) := by
    have hk : Tendsto (fun t : ℝ => -t / (R * C)) atTop atBot :=
      (tendsto_neg_atTop_atBot).atBot_div_const (by positivity)
    exact Real.tendsto_exp_atBot.comp hk
  have := (h.const_mul (v₀ - Ibar * R)).const_add (Ibar * R)
  rw [mul_zero, add_zero] at this
  exact this

/-- Comparison: every trajectory with `C v' = i − v/R_L` and `i ≤ Ī` on `[0, t]` stays below the
full-current trajectory from the same initial voltage. -/
@[tmio M, powerlib_domain] theorem le_fullCurrent {t : ℝ} {v i : ℝ → ℝ} (hR : 0 < R) (hC : 0 < C)
    (hv : ∀ s ∈ Icc 0 t, HasDerivWithinAt v ((i s - v s / R) / C) (Icc 0 t) s)
    (hi : ∀ s ∈ Icc 0 t, i s ≤ Ibar) (ht : 0 ≤ t) :
    v t ≤ fullCurrent R C Ibar (v 0) t := by
  have h := Dynamics.le_exp_mul_of_hasDerivWithinAt (g := fun s => v s - Ibar * R)
    (g' := fun s => (i s - v s / R) / C) (ρ := 1 / (R * C)) (t₀ := 0) (t₁ := t)
    (fun s hs => (hv s hs).sub_const _) (fun s hs => by
      have e : -(1 / (R * C)) * (v s - Ibar * R) = (Ibar - v s / R) / C := by
        field_simp
        ring
      rw [e]
      exact div_le_div_of_nonneg_right (by linarith [hi s hs]) hC.le) t ⟨ht, le_rfl⟩
  have e : -(1 / (R * C)) * (t - 0) = -t / (R * C) := by ring
  simp only [e] at h
  unfold fullCurrent
  linarith

/-- Below the load line the voltage stays below it: from `v(0) < Ī R_L`, an admissible trajectory
has `v(t) < Ī R_L` at every `t ≥ 0`. -/
@[tmio M, powerlib_domain] theorem lt_of_initial_lt {t : ℝ} {v i : ℝ → ℝ} (hR : 0 < R)
    (hC : 0 < C) (hv : ∀ s ∈ Icc 0 t, HasDerivWithinAt v ((i s - v s / R) / C) (Icc 0 t) s)
    (hi : ∀ s ∈ Icc 0 t, i s ≤ Ibar) (ht : 0 ≤ t) (h0 : v 0 < Ibar * R) : v t < Ibar * R := by
  have h := le_fullCurrent hR hC hv hi ht
  have hneg : (v 0 - Ibar * R) * Real.exp (-t / (R * C)) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos _)
  unfold fullCurrent at h
  linarith

/-- The full-current trajectory from `v₀` reaches `v_f` at the charging time `t*`. -/
@[tmio M, powerlib_domain] theorem fullCurrent_chargeTime {v₀ vf : ℝ} (hR : 0 < R) (hC : 0 < C)
    (h₀ : v₀ < Ibar * R) (hf : vf < Ibar * R) :
    fullCurrent R C Ibar v₀ (chargeTime R C Ibar v₀ vf) = vf := by
  have ha : 0 < Ibar * R - v₀ := by linarith
  have hb : 0 < Ibar * R - vf := by linarith
  have e : -chargeTime R C Ibar v₀ vf / (R * C) = Real.log ((Ibar * R - vf) / (Ibar * R - v₀)) := by
    rw [chargeTime, neg_div, mul_div_cancel_left₀ _ (mul_pos hR hC).ne', ← Real.log_inv, inv_div]
  rw [fullCurrent, e, Real.exp_log (div_pos hb ha)]
  field_simp
  ring

/-- No admissible trajectory from `v₀` is at or above `v_f < Ī R_L` before the charging time. -/
@[tmio M, powerlib_domain] theorem chargeTime_le {v₀ vf t : ℝ} {v i : ℝ → ℝ} (hR : 0 < R)
    (hC : 0 < C) (h₀ : v₀ < Ibar * R) (hf : vf < Ibar * R) (hv0 : v 0 = v₀)
    (hv : ∀ s ∈ Icc 0 t, HasDerivWithinAt v ((i s - v s / R) / C) (Icc 0 t) s)
    (hi : ∀ s ∈ Icc 0 t, i s ≤ Ibar) (ht : 0 ≤ t) (hreach : vf ≤ v t) :
    chargeTime R C Ibar v₀ vf ≤ t := by
  have ha : 0 < Ibar * R - v₀ := by linarith
  have hb : 0 < Ibar * R - vf := by linarith
  have hcmp := le_fullCurrent hR hC hv hi ht
  rw [hv0, fullCurrent] at hcmp
  have hRC : 0 < R * C := mul_pos hR hC
  have hE : Real.exp (-t / (R * C)) * Real.exp (t / (R * C)) = 1 := by
    rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero]
  have key : Ibar * R - v₀ ≤ (Ibar * R - vf) * Real.exp (t / (R * C)) := by
    have h1 : (Ibar * R - v₀) * Real.exp (-t / (R * C)) ≤ Ibar * R - vf := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (t / (R * C))).le
    rw [mul_assoc, hE, mul_one] at h2
    exact h2
  rw [chargeTime, ← le_div_iff₀' hRC, Real.log_le_iff_le_exp (div_pos ha hb),
    div_le_iff₀ hb]
  exact key.trans_eq (mul_comm _ _)

/-- The minimum charging time is exact: for `v₀ ≤ v_f < Ī R_L`, `t*` is the least time at which a
trajectory from `v₀` with `i ≤ Ī` is at `v_f`. -/
@[tmio M, powerlib_domain] theorem isLeast_chargeTime {v₀ vf : ℝ} (hR : 0 < R) (hC : 0 < C)
    (h₀ : v₀ ≤ vf) (hf : vf < Ibar * R) :
    IsLeast {t : ℝ | 0 ≤ t ∧ ∃ v i : ℝ → ℝ, v 0 = v₀ ∧
        (∀ s ∈ Icc 0 t, HasDerivWithinAt v ((i s - v s / R) / C) (Icc 0 t) s) ∧
        (∀ s ∈ Icc 0 t, i s ≤ Ibar) ∧ v t = vf} (chargeTime R C Ibar v₀ vf) := by
  have h₀' : v₀ < Ibar * R := lt_of_le_of_lt h₀ hf
  have ha : 0 < Ibar * R - v₀ := by linarith
  have hb : 0 < Ibar * R - vf := by linarith
  constructor
  · refine ⟨mul_nonneg (mul_pos hR hC).le (Real.log_nonneg ?_), fullCurrent R C Ibar v₀,
      fun _ => Ibar, (fullCurrent_solves hR.ne' hC.ne' v₀).1,
      fun s _ => ((fullCurrent_solves hR.ne' hC.ne' v₀).2 s).hasDerivWithinAt,
      fun _ _ => le_rfl, fullCurrent_chargeTime hR hC h₀' hf⟩
    rw [le_div_iff₀ hb]
    linarith
  · rintro t ⟨ht, v, i, hv0, hv, hi, hvt⟩
    exact chargeTime_le hR hC h₀' hf hv0 hv hi ht hvt.ge

/-- The greatest DC voltage the link holds in steady state (a constant trajectory) with the bridge
current `i ≤ Ī` is `Ī R_L`. -/
@[tmio M, powerlib_domain] theorem isGreatest_steadyState (hR : 0 < R) (hC : C ≠ 0) :
    IsGreatest {V : ℝ | ∃ i : ℝ → ℝ, (∀ t, i t ≤ Ibar) ∧
      ∀ t, HasDerivAt (fun _ : ℝ => V) ((i t - V / R) / C) t} (Ibar * R) := by
  constructor
  · refine ⟨fun _ => Ibar, fun _ => le_rfl, fun t => ?_⟩
    have e : (Ibar - Ibar * R / R) / C = 0 := by
      rw [mul_div_assoc, div_self hR.ne', mul_one, sub_self, zero_div]
    rw [e]
    exact hasDerivAt_const t _
  · rintro V ⟨i, hi, hV⟩
    have h0 : (i 0 - V / R) / C = 0 := (hV 0).unique (hasDerivAt_const 0 V)
    rw [div_eq_zero_iff, sub_eq_zero] at h0
    rcases h0 with h0 | h0
    · have := hi 0
      rw [h0, div_le_iff₀ hR] at this
      exact this
    · exact absurd h0 hC

/-- Every trajectory admissible on `[0, ∞)` is eventually below `Ī R_L + ε`, for every `ε > 0`. -/
@[tmio M, powerlib_domain] theorem eventually_le {v i : ℝ → ℝ} (hR : 0 < R) (hC : 0 < C)
    (hv : ∀ s, 0 ≤ s → HasDerivAt v ((i s - v s / R) / C) s) (hi : ∀ s, 0 ≤ s → i s ≤ Ibar)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ t in atTop, v t ≤ Ibar * R + ε := by
  have hlim := tendsto_fullCurrent (Ibar := Ibar) hR hC (v 0)
  filter_upwards [hlim.eventually (gt_mem_nhds (lt_add_of_pos_right (Ibar * R) hε)),
    eventually_ge_atTop 0] with t hlt ht
  exact (le_fullCurrent hR hC (fun s hs => (hv s hs.1).hasDerivWithinAt)
    (fun s hs => hi s hs.1) ht).trans hlt.le

end powerlib.WPT.DCLink
