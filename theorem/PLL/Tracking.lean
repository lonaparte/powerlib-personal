import theorem.PLL.Linear
import theorem.StateSpaceTrajectories

/-! # Linearized SRF-PLL: steady-state tracking in the time domain

Model boundary (domain module).
* System: the linearized SRF-PLL of `theorem/PLL/Linear.lean` (ideal balanced grid of constant
  amplitude `V`, PI loop filter, VCO; no pre-filter, delay, PWM, current loop or saturation),
  continuous time, linearized at the locked point.
* `frequencyModel V K_p K_i`: state `x = (θ̃, η)` (phase error `θ̂ − θ_g`, raw PI integrator),
  input `w(t) = ω_g(t) − ω_s` (grid frequency deviation, any real function of time),
  `θ̃̇ = −V K_p θ̃ + K_i η − w`, `η̇ = −V θ̃`; output `Δω̂ = −V K_p θ̃ + K_i η`.
  `phaseModel V K_p K_i`: state `(Δθ̂, η)`, input grid-angle deviation, output `Δθ̂`.
* Trajectories are forward solutions (`t ≥ 0`, `Passivity.IsTrajectory` of
  `StateSpacePassivity.system`) with an arbitrary initial state; conclusions are limits as
  `t → ∞` of every such solution. They are derived in the time domain by subtracting an
  explicit particular solution and using exponential stability of the error dynamics
  (`V K_p > 0`, `V K_i > 0`); the Laplace final-value theorem is not used.

Results (T-pll-dynamics §1.4 table).
* Phase step: `Δθ̂ → Δφ` (zero phase error).
* Frequency step `w ≡ c`: `θ̃ → 0`, `η → c/K_i`, frequency error `Δω̂ − w → 0`.
* Frequency ramp `w = ρ t` (ROCOF): `θ̃ → −ρ/(V K_i)`, frequency error `→ 0`.
* Second-order frequency ramp `w = α t²`, `α ≠ 0`: `|θ̃| → ∞`.

Source: work-sync `theory/T-pll-dynamics.md` §1.3, §1.4.

Correction (§1.4 table, ramp row): the steady-state phase error for a frequency ramp
`Δω_g = ρ t` is `θ̃(∞) = −ρ/(V K_i)` (the PLL lags a rising grid frequency, `θ̂ < θ_g`), not
`+ρ/(V K_i)`; `frequencyRamp_limit_ne_note` refutes the table value for `ρ ≠ 0`.
-/

noncomputable section
namespace powerlib.PLL
open Matrix Filter Set
open scoped Topology

/-! ## A general convergence lemma -/

@[powerlib_foundation] private lemma sq_le_sqNorm {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    x i ^ 2 ≤ LTI.sqNorm x := by
  unfold LTI.sqNorm
  exact Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j))
    (Finset.mem_univ i)

/-- Two forward trajectories of the same input-driven LTI model with Hurwitz state matrix
converge to each other, componentwise, for any common input signal. -/
@[powerlib_foundation] theorem tendsto_sub_of_isHurwitz {n : ℕ} {κ : Type*} [Fintype κ]
    {m : LTI.Model (Fin n) κ} (hA : LinearSystems.IsHurwitz m.A) {u : ℝ → κ → ℝ}
    {x y : ℝ → Fin n → ℝ} (hx : Passivity.IsTrajectory (StateSpacePassivity.system m) u x)
    (hy : Passivity.IsTrajectory (StateSpacePassivity.system m) u y) (i : Fin n) :
    Tendsto (fun t => x t i - y t i) atTop (𝓝 0) := by
  have he : Passivity.IsTrajectory (StateSpacePassivity.system m) (fun _ => 0)
      (fun t => x t - y t) := by
    intro t ht
    have h := (hx t ht).sub (hy t ht)
    convert h using 1
    simp only [StateSpacePassivity.system, LTI.Model.field, Matrix.mulVec_sub,
      Matrix.mulVec_zero, add_zero]
    abel
  obtain ⟨c⟩ := LTI.accepted_nonempty_of_isHurwitz (m := m.autonomous) hA
  have hr := c.sqNorm_tendsto_zero (LTI.response_solves m.autonomous (x 0 - y 0))
  have heq : ∀ t, 0 ≤ t → x t - y t = LTI.response m.autonomous (x 0 - y 0) t := by
    intro t ht
    rw [LTI.Model.response_autonomous]
    exact StateSpacePassivity.trajectory_eq_response m he ht
  have hsq : Tendsto (fun t => (x t i - y t i) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun t => sq_nonneg _) ?_ hr
    filter_upwards [eventually_ge_atTop 0] with t ht
    have h1 := sq_le_sqNorm (x t - y t) i
    have h2 : LTI.sqNorm (x t - y t) = LTI.sqNorm (LTI.response m.autonomous (x 0 - y 0) t) := by
      rw [heq t ht]
    simpa [h2] using h1
  have habs : Tendsto (fun t => |x t i - y t i|) atTop (𝓝 0) := by
    have h := hsq.sqrt
    simpa [Real.sqrt_sq_eq_abs] using h
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs

/-! ## Trajectories of the linearized PLL -/

/-- Forward trajectory of the linearized error dynamics for the grid-frequency deviation
`w(t) = ω_g(t) − ω_s`. -/
abbrev IsErrorTrajectory (V Kp Ki : ℝ) (w : ℝ → ℝ) (x : ℝ → Fin 2 → ℝ) : Prop :=
  Passivity.IsTrajectory (StateSpacePassivity.system (frequencyModel V Kp Ki))
    (fun t => ![w t]) x

@[powerlib_foundation] theorem frequencyModel_field (V Kp Ki : ℝ) (x : Fin 2 → ℝ) (u : Fin 1 → ℝ) :
    (StateSpacePassivity.system (frequencyModel V Kp Ki)).field x u =
      ![-(V * Kp) * x 0 + Ki * x 1 - u 0, -V * x 0] := by
  ext i; fin_cases i
  · simp [StateSpacePassivity.system, LTI.Model.field, frequencyModel, linA, dotProduct,
      Fin.sum_univ_two]
    ring
  · simp [StateSpacePassivity.system, LTI.Model.field, frequencyModel, linA, dotProduct,
      Fin.sum_univ_two]

@[powerlib_foundation] theorem frequencyModel_output (V Kp Ki : ℝ) (x : Fin 2 → ℝ) (u : Fin 1 → ℝ) :
    (frequencyModel V Kp Ki).output x u 0 = -(V * Kp) * x 0 + Ki * x 1 := by
  simp [LTI.Model.output, frequencyModel, dotProduct, Fin.sum_univ_two]

/-- A function with componentwise derivatives `d₀, d₁` solves the error dynamics. -/
@[powerlib_foundation] private lemma isErrorTrajectory_of {V Kp Ki : ℝ} {w : ℝ → ℝ}
    {x : ℝ → Fin 2 → ℝ}
    (h0 : ∀ t, HasDerivAt (fun τ => x τ 0) (-(V * Kp) * x t 0 + Ki * x t 1 - w t) t)
    (h1 : ∀ t, HasDerivAt (fun τ => x τ 1) (-V * x t 0) t) :
    IsErrorTrajectory V Kp Ki w x := by
  intro t _
  apply HasDerivAt.hasDerivWithinAt
  rw [frequencyModel_field]
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · simpa using h0 t
  · simpa using h1 t

/-! ## Phase step -/

/-- Phase step (constant grid-angle deviation `Δφ` from `t = 0`): every forward trajectory of
the phase model has `Δθ̂ → Δφ` (zero steady-state phase error). -/
@[powerlib_domain] theorem phaseStep_tracking {V Kp Ki : ℝ} (hVKp : 0 < V * Kp)
    (hVKi : 0 < V * Ki) (Δφ : ℝ) {x : ℝ → Fin 2 → ℝ}
    (hx : Passivity.IsTrajectory (StateSpacePassivity.system (phaseModel V Kp Ki))
      (fun _ => ![Δφ]) x) :
    Tendsto (fun t => x t 0) atTop (𝓝 Δφ) := by
  have hA : LinearSystems.IsHurwitz (phaseModel V Kp Ki).A :=
    (isHurwitz_linA_iff V Kp Ki).mpr ⟨hVKp, hVKi⟩
  have hp : Passivity.IsTrajectory (StateSpacePassivity.system (phaseModel V Kp Ki))
      (fun _ => ![Δφ]) (fun _ => ![Δφ, 0]) := by
    intro t _
    apply HasDerivAt.hasDerivWithinAt
    convert hasDerivAt_const t (![Δφ, 0] : Fin 2 → ℝ) using 1
    ext i; fin_cases i <;>
      simp [StateSpacePassivity.system, LTI.Model.field, phaseModel, linA]
  have h := tendsto_sub_of_isHurwitz hA hx hp 0
  simpa using h.add_const Δφ

/-! ## Frequency step -/

/-- Frequency step `w ≡ c`: `θ̃ → 0`, `η → c / K_i`, and the frequency-estimate error
`Δω̂ − w → 0`, for every forward trajectory. -/
@[powerlib_domain] theorem frequencyStep_tracking {V Kp Ki : ℝ} (hVKp : 0 < V * Kp)
    (hVKi : 0 < V * Ki) (c : ℝ) {x : ℝ → Fin 2 → ℝ} (hx : IsErrorTrajectory V Kp Ki (fun _ => c) x) :
    Tendsto (fun t => x t 0) atTop (𝓝 0) ∧ Tendsto (fun t => x t 1) atTop (𝓝 (c / Ki)) ∧
      Tendsto (fun t => (frequencyModel V Kp Ki).output (x t) ![c] 0 - c) atTop (𝓝 0) := by
  have hKi : Ki ≠ 0 := by rintro rfl; simp at hVKi
  have hA : LinearSystems.IsHurwitz (frequencyModel V Kp Ki).A :=
    (isHurwitz_linA_iff V Kp Ki).mpr ⟨hVKp, hVKi⟩
  have hp : IsErrorTrajectory V Kp Ki (fun _ => c) (fun _ => ![0, c / Ki]) :=
    isErrorTrajectory_of
      (fun t => (hasDerivAt_const t (0 : ℝ)).congr_deriv (by simp; field_simp; ring))
      (fun t => (hasDerivAt_const t (c / Ki)).congr_deriv (by simp))
  have h0 := tendsto_sub_of_isHurwitz hA hx hp 0
  have h1 := tendsto_sub_of_isHurwitz hA hx hp 1
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

@[powerlib_foundation] theorem rampParticular_isTrajectory {V Kp Ki : ℝ} (hV : V ≠ 0)
    (hKi : Ki ≠ 0) (ρ : ℝ) :
    IsErrorTrajectory V Kp Ki (fun t => ρ * t) (rampParticular V Kp Ki ρ) := by
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
tracks the ramp (`Δω̂ − w → 0`), for every forward trajectory. -/
@[powerlib_domain] theorem frequencyRamp_tracking {V Kp Ki : ℝ} (hVKp : 0 < V * Kp)
    (hVKi : 0 < V * Ki) (ρ : ℝ) {x : ℝ → Fin 2 → ℝ}
    (hx : IsErrorTrajectory V Kp Ki (fun t => ρ * t) x) :
    Tendsto (fun t => x t 0) atTop (𝓝 (-ρ / (V * Ki))) ∧
      Tendsto (fun t => (frequencyModel V Kp Ki).output (x t) ![ρ * t] 0 - ρ * t) atTop (𝓝 0) := by
  have hKi : Ki ≠ 0 := by rintro rfl; simp at hVKi
  have hV : V ≠ 0 := by rintro rfl; simp at hVKi
  have hA : LinearSystems.IsHurwitz (frequencyModel V Kp Ki).A :=
    (isHurwitz_linA_iff V Kp Ki).mpr ⟨hVKp, hVKi⟩
  have hp := rampParticular_isTrajectory (Kp := Kp) hV hKi ρ
  have h0 := tendsto_sub_of_isHurwitz hA hx hp 0
  have h1 := tendsto_sub_of_isHurwitz hA hx hp 1
  refine ⟨by simpa [rampParticular] using h0.add_const (-ρ / (V * Ki)), ?_⟩
  have := (h0.const_mul (-(V * Kp))).add (h1.const_mul Ki)
  simp only [mul_zero, add_zero] at this
  refine this.congr fun t => ?_
  rw [frequencyModel_output]
  simp only [rampParticular, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-- The table value `+ρ/(V K_i)` of T-pll-dynamics §1.4 is not the steady-state phase error:
the particular trajectory has the constant phase error `−ρ/(V K_i) ≠ ρ/(V K_i)` (`ρ ≠ 0`). -/
@[powerlib_domain] theorem frequencyRamp_limit_ne_note {V Kp Ki ρ : ℝ} (hVKp : 0 < V * Kp)
    (hVKi : 0 < V * Ki) (hρ : ρ ≠ 0) :
    ∃ x : ℝ → Fin 2 → ℝ, IsErrorTrajectory V Kp Ki (fun t => ρ * t) x ∧
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

@[powerlib_foundation] theorem quadParticular_isTrajectory {V Kp Ki : ℝ} (hV : V ≠ 0)
    (hKi : Ki ≠ 0) (α : ℝ) :
    IsErrorTrajectory V Kp Ki (fun t => α * t ^ 2) (quadParticular V Kp Ki α) := by
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
`|θ̃(t)| → ∞`, for every forward trajectory (the type-2 loop cannot track it). -/
@[powerlib_domain] theorem frequencyQuadratic_unbounded {V Kp Ki : ℝ} (hVKp : 0 < V * Kp)
    (hVKi : 0 < V * Ki) {α : ℝ} (hα : α ≠ 0) {x : ℝ → Fin 2 → ℝ}
    (hx : IsErrorTrajectory V Kp Ki (fun t => α * t ^ 2) x) :
    Tendsto (fun t => |x t 0|) atTop atTop := by
  have hKi : Ki ≠ 0 := by rintro rfl; simp at hVKi
  have hV : V ≠ 0 := by rintro rfl; simp at hVKi
  have hA : LinearSystems.IsHurwitz (frequencyModel V Kp Ki).A :=
    (isHurwitz_linA_iff V Kp Ki).mpr ⟨hVKp, hVKi⟩
  have hp := quadParticular_isTrajectory (Kp := Kp) hV hKi α
  have h0 := tendsto_sub_of_isHurwitz hA hx hp 0
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
