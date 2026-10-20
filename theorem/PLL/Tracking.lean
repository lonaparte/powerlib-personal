import theorem.PLL.Linear
import theorem.LTI.Plant

/-! # Linearized SRF-PLL: steady-state tracking in the time domain

Model boundary.
* System: the linearized SRF-PLL of `theorem/PLL/Linear.lean` (ideal balanced grid of constant
  amplitude `V`, PI loop filter, VCO; no pre-filter, delay, PWM, current loop or saturation),
  continuous time, linearized at the locked point.
* `frequencyModel V K_p K_i`: state `x = (θ̃, η)` (phase error `θ̂ − θ_g`, raw PI integrator),
  input `w(t) = ω_g(t) − ω_s` (grid frequency deviation, any real function of time),
  `θ̃̇ = −V K_p θ̃ + K_i η − w`, `η̇ = −V θ̃`; output `Δω̂ = −V K_p θ̃ + K_i η`.
  `phaseModel V K_p K_i`: state `(Δθ̂, η)`, input grid-angle deviation, output `Δθ̂`.
* Trajectories are forward solutions (`t ≥ 0`: one-sided derivatives on `[0, ∞)` of
  `ẋ = A x + B u`, in plain coordinates) with an arbitrary initial state, written out in each
  statement as `∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x (M.A *ᵥ x t + M.B *ᵥ u t) (Ici 0) t` for the
  plant `M` and input signal `u`; for the error dynamics `M = frequencyModel V K_p K_i` and
  `u t = ![w t]` with the grid-frequency deviation `w(t) = ω_g(t) − ω_s`. Conclusions are limits as
  `t → ∞` of every such solution. They are derived in the time domain by subtracting an explicit
  particular solution and using global exponential stability of the error dynamics (`V K_p > 0`,
  `V K_i > 0`, the linear hub `Linear.globallyExponentiallyStable_of_isHurwitz`); the Laplace
  final-value theorem is not used.

Source: work-sync `theory/T-pll-dynamics.md` §1.3, §1.4.

Results.
* Phase step: `Δθ̂ → Δφ` (zero phase error).
* Frequency step `w ≡ c`: `θ̃ → 0`, `η → c/K_i`, frequency error `Δω̂ − w → 0`.
* Frequency ramp `w = ρ t` (ROCOF): `θ̃ → −ρ/(V K_i)`, frequency error `→ 0`.
* Second-order frequency ramp `w = α t²`, `α ≠ 0`: `|θ̃| → ∞`.

Family and connection conclusions.
The stability of the linearized PLL is the family
`LinearPLL.family` of `theorem/PLL/Linear.lean`. The tracking limits here are statements about
solutions under time-varying inputs (limits of tracking errors, unbounded phase error), which the
sentence language (flow sentences about the origin of the zero-input field, passivity) cannot
express: the five tracking results (`phaseStep_tracking`, `frequencyStep_tracking`,
`frequencyRamp_tracking`, `frequencyRamp_limit_ne_note`, `frequencyQuadratic_unbounded`) are kept
as private implementation evidence. The generic convergence lemma `LTI.tendsto_sub_of_isHurwitz`
(any plant with Hurwitz state matrix, `theorem/LTI/Plant.lean`) and the explicit particular
solutions remain foundation.

Correction (§1.4 table, ramp row): the steady-state phase error for a frequency ramp
`Δω_g = ρ t` is `θ̃(∞) = −ρ/(V K_i)` (the PLL lags a rising grid frequency, `θ̂ < θ_g`), not
`+ρ/(V K_i)`; `frequencyRamp_limit_ne_note` refutes the table value for `ρ ≠ 0`.
-/

noncomputable section
namespace powerlib.PLL
open Matrix Filter Set
open scoped Topology
open powerlib.LTI (plantOutput)

/-! ## Trajectories of the linearized PLL

A forward trajectory of the linearized error dynamics for the grid-frequency deviation
`w(t) = ω_g(t) − ω_s` is a forward trajectory of `frequencyModel V K_p K_i` under the input
`t ↦ ![w t]`. -/

@[powerlib_foundation] theorem frequencyModel_field (V Kp Ki : ℝ) (x : Fin 2 → ℝ)
    (u : Fin 1 → ℝ) :
    (frequencyModel V Kp Ki).A *ᵥ x + (frequencyModel V Kp Ki).B *ᵥ u =
      ![-(V * Kp) * x 0 + Ki * x 1 - u 0, -V * x 0] := by
  ext i; fin_cases i
  · simp [frequencyModel, linA, dotProduct, Fin.sum_univ_two]
    ring
  · simp [frequencyModel, linA, dotProduct, Fin.sum_univ_two]

@[powerlib_foundation] theorem frequencyModel_output (V Kp Ki : ℝ) (x : Fin 2 → ℝ)
    (u : Fin 1 → ℝ) :
    plantOutput (frequencyModel V Kp Ki) x u 0 = -(V * Kp) * x 0 + Ki * x 1 := by
  simp [plantOutput, frequencyModel, dotProduct, Fin.sum_univ_two]

/-- A function with componentwise derivatives `d₀, d₁` solves the error dynamics (forward
trajectory of `frequencyModel V K_p K_i` under the input `t ↦ ![w t]`). -/
@[powerlib_foundation] private lemma isErrorTrajectory_of {V Kp Ki : ℝ} {w : ℝ → ℝ}
    {x : ℝ → Fin 2 → ℝ}
    (h0 : ∀ t, HasDerivAt (fun τ => x τ 0) (-(V * Kp) * x t 0 + Ki * x t 1 - w t) t)
    (h1 : ∀ t, HasDerivAt (fun τ => x τ 1) (-V * x t 0) t) :
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x
      ((frequencyModel V Kp Ki).A *ᵥ x t + (frequencyModel V Kp Ki).B *ᵥ ![w t]) (Ici 0) t := by
  intro t _
  apply HasDerivAt.hasDerivWithinAt
  rw [frequencyModel_field]
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · simpa using h0 t
  · simpa using h1 t

/-! ## Phase step -/

/-- Phase step (constant grid-angle deviation `Δφ` from `t = 0`): every forward trajectory of
the phase model has `Δθ̂ → Δφ` (zero steady-state phase error).
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem phaseStep_tracking {V Kp Ki : ℝ} (hVKp : 0 < V * Kp)
    (hVKi : 0 < V * Ki) (Δφ : ℝ) {x : ℝ → Fin 2 → ℝ}
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x
      ((phaseModel V Kp Ki).A *ᵥ x t + (phaseModel V Kp Ki).B *ᵥ ![Δφ]) (Ici 0) t) :
    Tendsto (fun t => x t 0) atTop (𝓝 Δφ) := by
  have hA : LinearSystems.IsHurwitz (phaseModel V Kp Ki).A :=
    (isHurwitz_linA_iff V Kp Ki).mpr ⟨hVKp, hVKi⟩
  have hp : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun _ : ℝ => (![Δφ, 0] : Fin 2 → ℝ))
      ((phaseModel V Kp Ki).A *ᵥ ![Δφ, 0] + (phaseModel V Kp Ki).B *ᵥ ![Δφ]) (Ici 0) t := by
    intro t _
    apply HasDerivAt.hasDerivWithinAt
    convert hasDerivAt_const t (![Δφ, 0] : Fin 2 → ℝ) using 1
    ext i; fin_cases i <;>
      simp [phaseModel, linA]
  have h := LTI.tendsto_sub_of_isHurwitz hA hx hp 0
  simpa using h.add_const Δφ

/-! ## Frequency step -/

/-- Frequency step `w ≡ c`: `θ̃ → 0`, `η → c / K_i`, and the frequency-estimate error
`Δω̂ − w → 0`, for every forward trajectory. 
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem frequencyStep_tracking {V Kp Ki : ℝ} (hVKp : 0 < V * Kp)
    (hVKi : 0 < V * Ki) (c : ℝ) {x : ℝ → Fin 2 → ℝ}
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x
      ((frequencyModel V Kp Ki).A *ᵥ x t + (frequencyModel V Kp Ki).B *ᵥ ![c]) (Ici 0) t) :
    Tendsto (fun t => x t 0) atTop (𝓝 0) ∧ Tendsto (fun t => x t 1) atTop (𝓝 (c / Ki)) ∧
      Tendsto (fun t => plantOutput (frequencyModel V Kp Ki) (x t) ![c] 0 - c) atTop (𝓝 0) := by
  have hKi : Ki ≠ 0 := by rintro rfl; simp at hVKi
  have hA : LinearSystems.IsHurwitz (frequencyModel V Kp Ki).A :=
    (isHurwitz_linA_iff V Kp Ki).mpr ⟨hVKp, hVKi⟩
  have hp : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun _ : ℝ => (![0, c / Ki] : Fin 2 → ℝ))
      ((frequencyModel V Kp Ki).A *ᵥ ![0, c / Ki] + (frequencyModel V Kp Ki).B *ᵥ ![c])
        (Ici 0) t :=
    isErrorTrajectory_of
      (fun t => (hasDerivAt_const t (0 : ℝ)).congr_deriv (by simp; field_simp; ring))
      (fun t => (hasDerivAt_const t (c / Ki)).congr_deriv (by simp))
  have h0 := LTI.tendsto_sub_of_isHurwitz hA hx hp 0
  have h1 := LTI.tendsto_sub_of_isHurwitz hA hx hp 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero] at h0 h1
  refine ⟨h0, by simpa using h1.add_const (c / Ki), ?_⟩
  have := (h0.const_mul (-(V * Kp))).add (h1.const_mul Ki)
  simp only [mul_zero, add_zero] at this
  refine this.congr fun t => ?_
  rw [frequencyModel_output]
  field_simp
  ring

/-! ## Frequency ramp -/

/-- Particular solution for `w = ρ t`: `θ̃ ≡ −ρ/(V K_i)`, `η = (ρ t + V K_p θ̃)/K_i`. -/
def rampParticular (V Kp Ki ρ : ℝ) (t : ℝ) : Fin 2 → ℝ :=
  ![-ρ / (V * Ki), (ρ * t + V * Kp * (-ρ / (V * Ki))) / Ki]

/-- The particular solution `rampParticular` is a forward trajectory of the error dynamics
for `w = ρ t`. -/
@[powerlib_foundation] theorem rampParticular_isTrajectory {V Kp Ki : ℝ} (hV : V ≠ 0)
    (hKi : Ki ≠ 0) (ρ : ℝ) :
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (rampParticular V Kp Ki ρ)
      ((frequencyModel V Kp Ki).A *ᵥ rampParticular V Kp Ki ρ t +
        (frequencyModel V Kp Ki).B *ᵥ ![ρ * t]) (Ici 0) t := by
  refine isErrorTrajectory_of (fun t => ?_) (fun t => ?_)
  · show HasDerivAt (fun _ => -ρ / (V * Ki)) _ t
    exact (hasDerivAt_const t (-ρ / (V * Ki))).congr_deriv (by
      simp only [rampParticular, Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp; ring)
  · show HasDerivAt (fun τ => (ρ * τ + V * Kp * (-ρ / (V * Ki))) / Ki) _ t
    exact ((((hasDerivAt_id' t).const_mul ρ).add_const (V * Kp * (-ρ / (V * Ki)))).div_const
      Ki).congr_deriv (by
        simp only [rampParticular, Matrix.cons_val_zero]
        field_simp)

/-- Frequency ramp `w = ρ t` (constant ROCOF): `θ̃ → −ρ/(V K_i)` and the frequency estimate
tracks the ramp (`Δω̂ − w → 0`), for every forward trajectory. 
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem frequencyRamp_tracking {V Kp Ki : ℝ} (hVKp : 0 < V * Kp)
    (hVKi : 0 < V * Ki) (ρ : ℝ) {x : ℝ → Fin 2 → ℝ}
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x
      ((frequencyModel V Kp Ki).A *ᵥ x t + (frequencyModel V Kp Ki).B *ᵥ ![ρ * t]) (Ici 0) t) :
    Tendsto (fun t => x t 0) atTop (𝓝 (-ρ / (V * Ki))) ∧
      Tendsto (fun t => plantOutput (frequencyModel V Kp Ki) (x t) ![ρ * t] 0 - ρ * t) atTop
        (𝓝 0) := by
  have hKi : Ki ≠ 0 := by rintro rfl; simp at hVKi
  have hV : V ≠ 0 := by rintro rfl; simp at hVKi
  have hA : LinearSystems.IsHurwitz (frequencyModel V Kp Ki).A :=
    (isHurwitz_linA_iff V Kp Ki).mpr ⟨hVKp, hVKi⟩
  have hp := rampParticular_isTrajectory (Kp := Kp) hV hKi ρ
  have h0 := LTI.tendsto_sub_of_isHurwitz hA hx hp 0
  have h1 := LTI.tendsto_sub_of_isHurwitz hA hx hp 1
  refine ⟨by simpa [rampParticular] using h0.add_const (-ρ / (V * Ki)), ?_⟩
  have := (h0.const_mul (-(V * Kp))).add (h1.const_mul Ki)
  simp only [mul_zero, add_zero] at this
  refine this.congr fun t => ?_
  rw [frequencyModel_output]
  simp only [rampParticular, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-- The table value `+ρ/(V K_i)` of T-pll-dynamics §1.4 is not the steady-state phase error:
the particular trajectory has the constant phase error `−ρ/(V K_i) ≠ ρ/(V K_i)` (`ρ ≠ 0`). 
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem frequencyRamp_limit_ne_note {V Kp Ki ρ : ℝ} (hVKp : 0 < V * Kp)
    (hVKi : 0 < V * Ki) (hρ : ρ ≠ 0) :
    ∃ x : ℝ → Fin 2 → ℝ, (∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x
        ((frequencyModel V Kp Ki).A *ᵥ x t + (frequencyModel V Kp Ki).B *ᵥ ![ρ * t]) (Ici 0) t) ∧
      ¬ Tendsto (fun t => x t 0) atTop (𝓝 (ρ / (V * Ki))) := by
  have hKi : Ki ≠ 0 := by rintro rfl; simp at hVKi
  have hV : V ≠ 0 := by rintro rfl; simp at hVKi
  refine ⟨rampParticular V Kp Ki ρ, rampParticular_isTrajectory hV hKi ρ, fun h => ?_⟩
  have h' := (frequencyRamp_tracking hVKp hVKi ρ (rampParticular_isTrajectory hV hKi ρ)).1
  have := tendsto_nhds_unique h h'
  have hne : ρ / (V * Ki) ≠ -ρ / (V * Ki) := by
    rw [neg_div]
    intro heq
    have : ρ / (V * Ki) = 0 := by linarith
    exact hρ ((div_eq_zero_iff.mp this).resolve_right hVKi.ne')
  exact hne this

/-! ## Second-order frequency ramp -/

/-- Particular solution for `w = α t²`: `θ̃ = p t + q`, `p = −2α/(V K_i)`, `q = −K_p p / K_i`. -/
def quadParticular (V Kp Ki α : ℝ) (t : ℝ) : Fin 2 → ℝ :=
  let p := -2 * α / (V * Ki)
  let q := -Kp * p / Ki
  ![p * t + q, (p + V * Kp * q + V * Kp * p * t + α * t ^ 2) / Ki]

/-- The particular solution `quadParticular` is a forward trajectory of the error dynamics
for `w = α t²`. -/
@[powerlib_foundation] theorem quadParticular_isTrajectory {V Kp Ki : ℝ} (hV : V ≠ 0)
    (hKi : Ki ≠ 0) (α : ℝ) :
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (quadParticular V Kp Ki α)
      ((frequencyModel V Kp Ki).A *ᵥ quadParticular V Kp Ki α t +
        (frequencyModel V Kp Ki).B *ᵥ ![α * t ^ 2]) (Ici 0) t := by
  set p := -2 * α / (V * Ki) with hp
  set q := -Kp * p / Ki with hq
  refine isErrorTrajectory_of (fun t => ?_) (fun t => ?_)
  · show HasDerivAt (fun τ => p * τ + q) _ t
    exact (((hasDerivAt_id' t).const_mul p).add_const q).congr_deriv (by
      simp only [quadParticular, Matrix.cons_val_zero, Matrix.cons_val_one, hp]
      field_simp; ring)
  · show HasDerivAt (fun τ => (p + V * Kp * q + V * Kp * p * τ + α * τ ^ 2) / Ki) _ t
    exact (((((hasDerivAt_id' t).const_mul (V * Kp * p)).const_add (p + V * Kp * q)).add
      (((hasDerivAt_id' t).pow 2).const_mul α)).div_const Ki).congr_deriv (by
        simp only [quadParticular, Matrix.cons_val_zero, hp]
        norm_num
        field_simp; ring)

/-- Second-order frequency ramp `w = α t²` (`α ≠ 0`): the phase error is unbounded,
`|θ̃(t)| → ∞`, for every forward trajectory (the type-2 loop cannot track it). 
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem frequencyQuadratic_unbounded {V Kp Ki : ℝ} (hVKp : 0 < V * Kp)
    (hVKi : 0 < V * Ki) {α : ℝ} (hα : α ≠ 0) {x : ℝ → Fin 2 → ℝ}
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x
      ((frequencyModel V Kp Ki).A *ᵥ x t + (frequencyModel V Kp Ki).B *ᵥ ![α * t ^ 2]) (Ici 0) t) :
    Tendsto (fun t => |x t 0|) atTop atTop := by
  have hKi : Ki ≠ 0 := by rintro rfl; simp at hVKi
  have hV : V ≠ 0 := by rintro rfl; simp at hVKi
  have hA : LinearSystems.IsHurwitz (frequencyModel V Kp Ki).A :=
    (isHurwitz_linA_iff V Kp Ki).mpr ⟨hVKp, hVKi⟩
  have hp := quadParticular_isTrajectory (Kp := Kp) hV hKi α
  have h0 := LTI.tendsto_sub_of_isHurwitz hA hx hp 0
  set p := -2 * α / (V * Ki) with hpdef
  have hp0 : p ≠ 0 := by
    rw [hpdef]
    exact div_ne_zero (mul_ne_zero (by norm_num) hα) hVKi.ne'
  have hlin : Tendsto (fun t => |p * t + (-Kp * p / Ki)|) atTop atTop := by
    have : Tendsto (fun t => |p| * t - |Kp * p / Ki|) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop (abs_pos.mpr hp0))
    refine tendsto_atTop_mono' _ ?_ this
    filter_upwards [eventually_ge_atTop 0] with t ht
    have h1 : |p * t| = |p| * t := by rw [abs_mul, abs_of_nonneg ht]
    have h2 := abs_sub_abs_le_abs_sub (p * t) (-(-Kp * p / Ki))
    rw [sub_neg_eq_add, abs_neg, h1] at h2
    have h3 : |-Kp * p / Ki| = |Kp * p / Ki| := by rw [neg_mul, neg_div, abs_neg]
    linarith
  have hsum : Tendsto (fun t => |(x t 0 - quadParticular V Kp Ki α t 0) +
      quadParticular V Kp Ki α t 0|) atTop atTop := by
    have hb : ∀ᶠ t in atTop, |x t 0 - quadParticular V Kp Ki α t 0| ≤ 1 := by
      have := (tendsto_order.1 h0.abs).2 1 (by norm_num)
      filter_upwards [this] with t ht
      simpa using ht.le
    have hq : Tendsto (fun t => |quadParticular V Kp Ki α t 0| - 1) atTop atTop := by
      refine (tendsto_atTop_add_const_right _ (-1) hlin).congr fun t => ?_
      simp only [quadParticular, hpdef, Matrix.cons_val_zero]
      ring_nf
    refine tendsto_atTop_mono' _ ?_ hq
    filter_upwards [hb] with t ht
    have := abs_sub_abs_le_abs_sub (quadParticular V Kp Ki α t 0)
      (-(x t 0 - quadParticular V Kp Ki α t 0))
    rw [sub_neg_eq_add, abs_neg, add_comm] at this
    linarith
  simpa using hsum

end powerlib.PLL
