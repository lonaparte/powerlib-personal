import theorem.GridTiedConverter.GFM.Tracking.Linear

/-! # Grid-forming synchronization following a moving grid: tracking and loss of synchronism

The GFM counterparts of the PLL tracking results (`theorem/GridTiedConverter/PLL/Tracking.lean`)
and of the PLL frequency-ramp boundary `Σ_FD` (`PIPLL.frequencyRampBoundary`,
`theorem/GridTiedConverter/PLL/PIPLLFamily.lean`).

Model boundary.
* The reduced GFM of `theorem/GridTiedConverter/GFM/Tracking/Linear.lean`: two-state loop
  `θ̇ = Δω`, `M Δω̇ = P_ref − P_e(θ − θ_g) − D Δω`, `P_e(δ) = c₀ + A sin(δ − α)` (`SwingParams`
  with `k₁ = c₀`, `k₂ = A`, `k₃ = α`, `P_m = P_ref`); three-state loop with power filter on the
  lossless line (`VSMLPF.fieldU`, `P_e = K₀ sin`). The damping acts on the frequency deviation
  from the nominal frequency `ω₀` (droop: `D = K_R`), not on the deviation from the grid
  frequency (that would need a PLL). Per unit, export-positive power, continuous time; line
  dynamics, inner loops, Q–V droop, limits, delay and PWM excluded.
* Grid angle `θ_g(t) = θ₀ + c t` (constant frequency offset `c`) or `θ₀ + c t + ρ t²/2`
  (frequency ramp, constant ROCOF `ρ`).
* Linear tracking: the plants `frequencyPlant`, `anglePlant`, `filterFrequencyPlant` (the
  linearizations at the power angle `δ`, `K = P_e'(δ)`), with forward trajectories on `[0, ∞)`
  written out as in `theorem/GridTiedConverter/PLL/Tracking.lean`; limits as `t → ∞` of every such
  trajectory, by subtracting an explicit particular solution (`LTI.tendsto_sub_of_isHurwitz`).
* Nonlinear frame change: under a constant offset `c` the loop read in the frame of the grid,
  state `(θ − θ_g, Δω − c)`, is autonomous: the VSM model `gridFrame p c δ` of
  `DroopVSM.vsmFamily` with the nominal frequency `ω_s = −c` in that frame
  (`theorem/GridTiedConverter/GFM/DroopVSM.lean`), whose field is the swing field with the power
  reference `P_ref − D c` (`gridFrame_vector`); for three states the VSM + filter model
  `offsetFilter g c` (`P₀ − D c`) of `VSMLPF.family`. Scaffold of this frame change:
  `theorem/GridTiedConverter/GFM/Tracking/GridFrame.agda`.

Source: GFM counterpart study note t8 (tracking): derivation with the SymPy/SciPy check
`s3_tracking.py` (outside the repository; particular solutions, 12 linear and 10 nonlinear
simulations, the existence condition on both sides on 20 parameter sets); Kundur, *Power System
Stability and Control* (1994) §5.1, §11.1 (frequency response of synchronous machines, droop).

Results.
* Linear tracking (implementation evidence, private, as in the PLL module): a grid-angle step is
  followed exactly (`phaseStep_tracking`); a grid-frequency step `c` is followed in frequency
  (`Δω → c`) with the steady angle offset `Δδ → −D c/K` and, with the filter, `ΔP_f → −D c`
  (`frequencyStep_tracking`, `filterFrequencyStep_tracking`); under a frequency ramp `ρ` the
  converter frequency lags the grid by the constant `D ρ/K` and the power angle drifts without
  bound, `|Δδ| → ∞` (`frequencyRamp_tracking`, `filterFrequencyRamp_tracking`): the droop-damped
  loop is of type one in frequency, where the PI-PLL is of type two (`θ̃ → −ρ/(V K_i)`).
  Public particular solutions: `stepParticular_isTrajectory`, `rampParticular_isTrajectory`,
  `filterStepParticular_isTrajectory`, `filterRampParticular_isTrajectory`.
* Nonlinear ramp (implementation evidence): for `M, D > 0` every solution of the two-state and of
  the three-state loop keeps a bounded converter frequency, so under any ramp `ρ ≠ 0` the frequency
  error is unbounded, `|Δω − (c + ρ t)| → ∞` (`ramp_frequencyError_unbounded`,
  `filterRamp_frequencyError_unbounded`): the GFM loses synchronism under every frequency ramp
  that lasts long enough, whereas the PI-PLL has locked phases under every ramp with
  `ρ/K_i` in the range of its detector (`PIPLL.ramp_phaseLocked_iff`).
* Frame change (static): `gridFrame_hasDerivAt_iff`, `filterGridFrame_hasDerivAt_iff`,
  `gridFrame_vector`; the shifted equilibrium exists iff `|P_ref − D c − c₀| ≤ A`
  (`gridFrame_exists_equilibrium_iff`).

Family and connection conclusions.
No new family: the moving-frame models are members of `DroopVSM.vsmFamily` (two states) and
`VSMLPF.family` (three states), whose laws are read.
* Loss of synchronism (the GFM `Σ_FD`): when the demanded power leaves the band,
  `|P_ref − D c − c₀| > A`, every selected angle of the moving-frame model is unstable
  (`gridFrame_mem_den_unstable`); three states: `|P₀ − D c| > |K₀|`
  (`filterGridFrame_mem_den_unstable`). Unlike the PI-PLL, whose integrator absorbs a constant
  offset (`PIPLL.srf_mem_den_locallyExponentiallyStable_inPhase`), the GFM loses synchronism
  under a large enough constant frequency offset.
* Synchronism: the shifted angle `δ_s(c) = α + arcsin((P_ref − D c − c₀)/A)` is locally
  exponentially stable (`gridFrame_mem_den_locallyExponentiallyStable`), and some selected angle
  is locally exponentially stable iff `|P_ref − D c − c₀| < A` (`gridFrame_synchronism_iff`,
  `M, D, A > 0`, through the exactness `Synchronous.Swing.exactUnder_locallyExponentiallyStable`
  and `DroopVSM.vsm_mem_den_iff_swing_of_sinusoid`); three states: iff `|P₀ − D c| < K₀` and the
  filter is fast at the shifted angle, `√(K₀² − (P₀ − D c)²) < D ω_c + D²/M`
  (`filterGridFrame_synchronism_iff`, through `VSMLPF.exactUnder_locallyExponentiallyStable`).
-/

noncomputable section
namespace powerlib.GFM.Tracking
open Matrix Filter Set
open scoped Topology
open powerlib.Dynamics (State mk3 mk3_zero state3_ext)
open powerlib.Synchronous (SwingParams)

/-! ## Generic helpers (implementation evidence) -/

/-- `|a t + b| → ∞` for `a ≠ 0`. -/
@[tmio T, powerlib_foundation] private lemma tendsto_abs_affine {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    Tendsto (fun t : ℝ => |a * t + b|) atTop atTop := by
  have : Tendsto (fun t => |a| * t - |b|) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop (abs_pos.mpr ha))
  refine tendsto_atTop_mono' _ ?_ this
  filter_upwards [eventually_ge_atTop 0] with t ht
  have h1 : |a * t| = |a| * t := by rw [abs_mul, abs_of_nonneg ht]
  have h2 := abs_sub_abs_le_abs_sub (a * t) (-b)
  rw [sub_neg_eq_add, abs_neg, h1] at h2
  linarith

/-- If `f − g → 0` and `|g| → ∞` then `|f| → ∞`. -/
@[tmio T, powerlib_foundation] private lemma tendsto_abs_of_sub {f g : ℝ → ℝ}
    (hfg : Tendsto (fun t => f t - g t) atTop (𝓝 0))
    (hg : Tendsto (fun t => |g t|) atTop atTop) : Tendsto (fun t => |f t|) atTop atTop := by
  have hb : ∀ᶠ t in atTop, |f t - g t| ≤ 1 := by
    have := (tendsto_order.1 hfg.abs).2 1 (by norm_num)
    filter_upwards [this] with t ht
    simpa using ht.le
  refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-1) hg)
  filter_upwards [hb] with t ht
  have := abs_sub_abs_le_abs_sub (g t) (g t - f t)
  rw [sub_sub_cancel, abs_sub_comm] at this
  linarith

/-- A first-order lag `a ẏ = F(t) − b y` with `a, b > 0` and bounded forcing `|F| ≤ B` stays below
`max (y 0) (B/b + 1)` on `[0, ∞)` (Mathlib's fencing theorem
`image_le_of_deriv_right_lt_deriv_boundary`). -/
@[tmio T, powerlib_foundation] private lemma lag_le {a b B : ℝ} (ha : 0 < a) (hb : 0 < b)
    {F y y' : ℝ → ℝ} (hF : ∀ t, 0 ≤ t → |F t| ≤ B)
    (hy : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt y (y' t) (Ici 0) t)
    (hy' : ∀ t, 0 ≤ t → a * y' t = F t - b * y t) :
    ∀ t, 0 ≤ t → y t ≤ max (y 0) (B / b + 1) := by
  intro T hT
  set C := max (y 0) (B / b + 1)
  have hcont : ContinuousOn y (Icc 0 T) := fun t ht =>
    ((hy t ht.1).continuousWithinAt).mono Icc_subset_Ici_self
  refine image_le_of_deriv_right_lt_deriv_boundary (B := fun _ => C) (B' := fun _ => 0) hcont
    (fun t ht => (hy t ht.1).mono (Ici_subset_Ici.mpr ht.1)) (le_max_left _ _)
    (fun t => hasDerivAt_const t C) (fun t ht hyt => ?_) ⟨hT, le_rfl⟩
  have h1 := hy' t ht.1
  have h2 := hF t ht.1
  have hC : B / b + 1 ≤ C := le_max_right _ _
  have hbC : B < b * C := by
    have : b * (B / b + 1) = B + b := by field_simp
    nlinarith
  have hFt : F t ≤ B := (le_abs_self _).trans h2
  have : a * y' t < 0 := by rw [h1, hyt]; linarith
  exact neg_of_mul_neg_right this ha.le

/-- The same lag is bounded on `[0, ∞)`. -/
@[tmio T, powerlib_foundation] private lemma lag_bounded {a b B : ℝ} (ha : 0 < a) (hb : 0 < b)
    {F y y' : ℝ → ℝ} (hF : ∀ t, 0 ≤ t → |F t| ≤ B)
    (hy : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt y (y' t) (Ici 0) t)
    (hy' : ∀ t, 0 ≤ t → a * y' t = F t - b * y t) :
    ∃ C, ∀ t, 0 ≤ t → |y t| ≤ C := by
  have hup := lag_le ha hb hF hy hy'
  have hlo := lag_le (F := fun t => -F t) (y := fun t => -y t) (y' := fun t => -y' t) ha hb
    (fun t ht => by rw [abs_neg]; exact hF t ht) (fun t ht => (hy t ht).neg)
    (fun t ht => by rw [mul_neg, hy' t ht]; ring)
  refine ⟨max (max (y 0) (B / b + 1)) (max (-y 0) (B / b + 1)), fun t ht => abs_le.mpr ⟨?_, ?_⟩⟩
  · have := hlo t ht
    have := le_max_right (max (y 0) (B / b + 1)) (max (-y 0) (B / b + 1))
    linarith
  · exact (hup t ht).trans (le_max_left _ _)

/-- A bounded frequency against a ramping grid frequency: `|ω − (c + ρ t)| → ∞` (`ρ ≠ 0`). -/
@[tmio T, powerlib_foundation] private lemma tendsto_error_of_bounded {ω : ℝ → ℝ} {C : ℝ}
    (hC : ∀ t, 0 ≤ t → |ω t| ≤ C) (c : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    Tendsto (fun t => |ω t - (c + ρ * t)|) atTop atTop := by
  refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-C)
    (tendsto_abs_affine hρ c))
  filter_upwards [eventually_ge_atTop 0] with t ht
  have h1 := abs_sub_abs_le_abs_sub (ρ * t + c) (-(ω t - (c + ρ * t)))
  rw [abs_neg, show ρ * t + c - -(ω t - (c + ρ * t)) = ω t by ring] at h1
  have := hC t ht
  linarith

/-! ## Linear tracking: the two-state loop -/

@[tmio M, powerlib_domain] theorem frequencyPlant_field (p : SwingParams) (δ : ℝ) (x : Fin 2 → ℝ)
    (u : Fin 1 → ℝ) :
    (frequencyPlant p δ).A *ᵥ x + (frequencyPlant p δ).B *ᵥ u =
      ![x 1 - u 0, -(p.syncCoeff δ / p.M) * x 0 - p.D / p.M * x 1] := by
  ext i; fin_cases i <;>
    simp [frequencyPlant, SwingParams.jacobian, dotProduct, Fin.sum_univ_two] <;> ring

/-- A function with componentwise derivatives solves the frequency channel under `t ↦ ![w t]`. -/
@[tmio M, powerlib_domain] private lemma isFrequencyTrajectory_of (p : SwingParams) (δ : ℝ)
    {w : ℝ → ℝ} {x : ℝ → Fin 2 → ℝ}
    (h0 : ∀ t, HasDerivAt (fun τ => x τ 0) (x t 1 - w t) t)
    (h1 : ∀ t, HasDerivAt (fun τ => x τ 1)
      (-(p.syncCoeff δ / p.M) * x t 0 - p.D / p.M * x t 1) t) :
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x
      ((frequencyPlant p δ).A *ᵥ x t + (frequencyPlant p δ).B *ᵥ ![w t]) (Ici 0) t := by
  intro t _
  apply HasDerivAt.hasDerivWithinAt
  rw [frequencyPlant_field]
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · simpa using h0 t
  · simpa using h1 t

/-- Particular solution for a grid-frequency step `w ≡ c`: `(Δδ, Δω) = (−D c/K, c)`. -/
def stepParticular (p : SwingParams) (δ c : ℝ) : Fin 2 → ℝ := ![-(p.D * c) / p.syncCoeff δ, c]

@[tmio TM, powerlib_domain] theorem stepParticular_isTrajectory (p : SwingParams) {δ : ℝ}
    (hK : p.syncCoeff δ ≠ 0) (c : ℝ) :
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun _ : ℝ => stepParticular p δ c)
      ((frequencyPlant p δ).A *ᵥ stepParticular p δ c + (frequencyPlant p δ).B *ᵥ ![c])
        (Ici 0) t :=
  isFrequencyTrajectory_of p δ
    (fun t => (hasDerivAt_const t _).congr_deriv (by simp [stepParticular]))
    (fun t => (hasDerivAt_const t _).congr_deriv (by
      simp only [stepParticular, Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp; ring))

/-- Particular solution for a ramp `w = ρ t`: `Δδ = p t + q`, `Δω = p + ρ t`, `p = −D ρ/K`,
`q = ρ (D² − K M)/K²`. -/
def rampParticular (p : SwingParams) (δ ρ t : ℝ) : Fin 2 → ℝ :=
  ![-(p.D * ρ) / p.syncCoeff δ * t + ρ * (p.D ^ 2 - p.syncCoeff δ * p.M) / p.syncCoeff δ ^ 2,
    -(p.D * ρ) / p.syncCoeff δ + ρ * t]

@[tmio TM, powerlib_domain] theorem rampParticular_isTrajectory (p : SwingParams) {δ : ℝ}
    (hM : p.M ≠ 0) (hK : p.syncCoeff δ ≠ 0) (ρ : ℝ) :
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (rampParticular p δ ρ)
      ((frequencyPlant p δ).A *ᵥ rampParticular p δ ρ t +
        (frequencyPlant p δ).B *ᵥ ![ρ * t]) (Ici 0) t := by
  refine isFrequencyTrajectory_of p δ (fun t => ?_) (fun t => ?_)
  · show HasDerivAt (fun τ => -(p.D * ρ) / p.syncCoeff δ * τ +
      ρ * (p.D ^ 2 - p.syncCoeff δ * p.M) / p.syncCoeff δ ^ 2) _ t
    exact (((hasDerivAt_id' t).const_mul _).add_const _).congr_deriv (by
      simp only [rampParticular, Matrix.cons_val_one, Matrix.cons_val_zero]; ring)
  · show HasDerivAt (fun τ => -(p.D * ρ) / p.syncCoeff δ + ρ * τ) _ t
    exact (((hasDerivAt_id' t).const_mul ρ).const_add _).congr_deriv (by
      simp only [rampParticular, Matrix.cons_val_one, Matrix.cons_val_zero]
      field_simp; ring)

@[tmio M, powerlib_domain] private lemma isHurwitz_frequencyPlant (p : SwingParams) {δ : ℝ}
    (hM : 0 < p.M) (hD : 0 < p.D) (hK : 0 < p.syncCoeff δ) :
    LinearSystems.IsHurwitz (frequencyPlant p δ).A :=
  (p.isHurwitz_jacobian_iff hM δ).mpr ⟨hD, hK⟩

/-- Frequency step `w ≡ c`: the converter frequency follows, `Δω → c`, with the steady angle
offset `Δδ → −D c/K`, for every forward trajectory.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem frequencyStep_tracking (p : SwingParams) {δ : ℝ}
    (hM : 0 < p.M) (hD : 0 < p.D) (hK : 0 < p.syncCoeff δ) (c : ℝ) {x : ℝ → Fin 2 → ℝ}
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x
      ((frequencyPlant p δ).A *ᵥ x t + (frequencyPlant p δ).B *ᵥ ![c]) (Ici 0) t) :
    Tendsto (fun t => x t 0) atTop (𝓝 (-(p.D * c) / p.syncCoeff δ)) ∧
      Tendsto (fun t => x t 1) atTop (𝓝 c) := by
  have hA := isHurwitz_frequencyPlant p hM hD hK
  have hp := stepParticular_isTrajectory p hK.ne' c
  have h0 := LTI.tendsto_sub_of_isHurwitz hA hx hp 0
  have h1 := LTI.tendsto_sub_of_isHurwitz hA hx hp 1
  refine ⟨?_, ?_⟩
  · simpa [stepParticular] using h0.add_const (-(p.D * c) / p.syncCoeff δ)
  · simpa [stepParticular] using h1.add_const c

/-- Frequency ramp `w = ρ t` (constant ROCOF): the converter frequency lags the grid by the
constant `D ρ/K` (`Δω − ρ t → −D ρ/K`), and for `ρ ≠ 0` the power angle drifts without bound
(`|Δδ| → ∞`), for every forward trajectory.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem frequencyRamp_tracking (p : SwingParams) {δ : ℝ}
    (hM : 0 < p.M) (hD : 0 < p.D) (hK : 0 < p.syncCoeff δ) {ρ : ℝ} {x : ℝ → Fin 2 → ℝ}
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x
      ((frequencyPlant p δ).A *ᵥ x t + (frequencyPlant p δ).B *ᵥ ![ρ * t]) (Ici 0) t) :
    Tendsto (fun t => x t 1 - ρ * t) atTop (𝓝 (-(p.D * ρ) / p.syncCoeff δ)) ∧
      (ρ ≠ 0 → Tendsto (fun t => |x t 0|) atTop atTop) := by
  have hA := isHurwitz_frequencyPlant p hM hD hK
  have hp := rampParticular_isTrajectory p hM.ne' hK.ne' ρ
  have h0 := LTI.tendsto_sub_of_isHurwitz hA hx hp 0
  have h1 := LTI.tendsto_sub_of_isHurwitz hA hx hp 1
  refine ⟨?_, fun hρ => tendsto_abs_of_sub h0 ?_⟩
  · refine (h1.add_const (-(p.D * ρ) / p.syncCoeff δ)).congr' ?_ |>.mono_right (by simp)
    exact Eventually.of_forall fun t => by simp [rampParticular]; ring
  · have ha : -(p.D * ρ) / p.syncCoeff δ ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hD.ne' hρ)) hK.ne'
    simpa [rampParticular] using tendsto_abs_affine ha
      (ρ * (p.D ^ 2 - p.syncCoeff δ * p.M) / p.syncCoeff δ ^ 2)

/-- Grid-angle step `Δφ`: the converter angle follows exactly, `Δθ → Δφ`, for every forward
trajectory of the angle channel.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem phaseStep_tracking (p : SwingParams) {δ : ℝ}
    (hM : 0 < p.M) (hD : 0 < p.D) (hK : 0 < p.syncCoeff δ) (Δφ : ℝ) {x : ℝ → Fin 2 → ℝ}
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x
      ((anglePlant p δ).A *ᵥ x t + (anglePlant p δ).B *ᵥ ![Δφ]) (Ici 0) t) :
    Tendsto (fun t => x t 0) atTop (𝓝 Δφ) := by
  have hA : LinearSystems.IsHurwitz (anglePlant p δ).A := (p.isHurwitz_jacobian_iff hM δ).mpr
    ⟨hD, hK⟩
  have hp : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun _ : ℝ => (![Δφ, 0] : Fin 2 → ℝ))
      ((anglePlant p δ).A *ᵥ ![Δφ, 0] + (anglePlant p δ).B *ᵥ ![Δφ]) (Ici 0) t := by
    intro t _
    apply HasDerivAt.hasDerivWithinAt
    convert hasDerivAt_const t (![Δφ, 0] : Fin 2 → ℝ) using 1
    ext i; fin_cases i
    · simp [anglePlant, SwingParams.jacobian]
    · simp [anglePlant, SwingParams.jacobian]; ring
  have h := LTI.tendsto_sub_of_isHurwitz hA hx hp 0
  simpa using h.add_const Δφ

/-! ## Linear tracking: the three-state loop -/

@[tmio M, powerlib_domain] theorem filterFrequencyPlant_field (g : VSMLPF) (δ : ℝ)
    (x : Fin 3 → ℝ) (u : Fin 1 → ℝ) :
    (filterFrequencyPlant g δ).A *ᵥ x + (filterFrequencyPlant g δ).B *ᵥ u =
      ![x 1 - u 0, -(g.D / g.M) * x 1 - 1 / g.M * x 2,
        g.ωc * (g.K0 * Real.cos δ) * x 0 - g.ωc * x 2] := by
  ext i; fin_cases i <;>
    simp [filterFrequencyPlant, VSMLPF.jacobian, dotProduct, Fin.sum_univ_three] <;> ring

@[tmio M, powerlib_domain] private lemma isFilterTrajectory_of (g : VSMLPF) (δ : ℝ)
    {w : ℝ → ℝ} {x : ℝ → Fin 3 → ℝ}
    (h0 : ∀ t, HasDerivAt (fun τ => x τ 0) (x t 1 - w t) t)
    (h1 : ∀ t, HasDerivAt (fun τ => x τ 1) (-(g.D / g.M) * x t 1 - 1 / g.M * x t 2) t)
    (h2 : ∀ t, HasDerivAt (fun τ => x τ 2)
      (g.ωc * (g.K0 * Real.cos δ) * x t 0 - g.ωc * x t 2) t) :
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x
      ((filterFrequencyPlant g δ).A *ᵥ x t + (filterFrequencyPlant g δ).B *ᵥ ![w t])
        (Ici 0) t := by
  intro t _
  apply HasDerivAt.hasDerivWithinAt
  rw [filterFrequencyPlant_field]
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · simpa using h0 t
  · simpa using h1 t
  · simpa using h2 t

/-- Particular solution for a grid-frequency step `w ≡ c`: `(−D c/K, c, −D c)`,
`K = K₀ cos δ`. -/
def filterStepParticular (g : VSMLPF) (δ c : ℝ) : Fin 3 → ℝ :=
  ![-(g.D * c) / (g.K0 * Real.cos δ), c, -(g.D * c)]

@[tmio TM, powerlib_domain] theorem filterStepParticular_isTrajectory (g : VSMLPF) {δ : ℝ}
    (hK : g.K0 * Real.cos δ ≠ 0) (c : ℝ) :
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun _ : ℝ => filterStepParticular g δ c)
      ((filterFrequencyPlant g δ).A *ᵥ filterStepParticular g δ c +
        (filterFrequencyPlant g δ).B *ᵥ ![c]) (Ici 0) t :=
  isFilterTrajectory_of g δ
    (fun t => (hasDerivAt_const t _).congr_deriv (by simp [filterStepParticular]))
    (fun t => (hasDerivAt_const t _).congr_deriv (by
      simp only [filterStepParticular, Matrix.cons_val_one, Matrix.cons_val_zero,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      ring))
    (fun t => (hasDerivAt_const t _).congr_deriv (by
      have hK0 : g.K0 ≠ 0 := left_ne_zero_of_mul hK
      have hc : Real.cos δ ≠ 0 := right_ne_zero_of_mul hK
      simp only [filterStepParticular, Matrix.cons_val_zero,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      field_simp; ring))

/-- Particular solution for a ramp `w = ρ t`: `Δδ = p t + q`, `Δω = p + ρ t`,
`ΔP_f = −M ρ − D (p + ρ t)`, `p = −D ρ/K`, `q = ρ (D² ω_c − D K − K M ω_c)/(K² ω_c)`. -/
def filterRampParticular (g : VSMLPF) (δ ρ t : ℝ) : Fin 3 → ℝ :=
  ![-(g.D * ρ) / (g.K0 * Real.cos δ) * t +
      ρ * (g.D ^ 2 * g.ωc - g.D * (g.K0 * Real.cos δ) - (g.K0 * Real.cos δ) * g.M * g.ωc) /
        ((g.K0 * Real.cos δ) ^ 2 * g.ωc),
    -(g.D * ρ) / (g.K0 * Real.cos δ) + ρ * t,
    -(g.M * ρ) - g.D * (-(g.D * ρ) / (g.K0 * Real.cos δ) + ρ * t)]

@[tmio TM, powerlib_domain] theorem filterRampParticular_isTrajectory (g : VSMLPF) {δ : ℝ}
    (hM : g.M ≠ 0) (hω : g.ωc ≠ 0) (hK : g.K0 * Real.cos δ ≠ 0) (ρ : ℝ) :
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (filterRampParticular g δ ρ)
      ((filterFrequencyPlant g δ).A *ᵥ filterRampParticular g δ ρ t +
        (filterFrequencyPlant g δ).B *ᵥ ![ρ * t]) (Ici 0) t := by
  have hK0 : g.K0 ≠ 0 := left_ne_zero_of_mul hK
  have hc : Real.cos δ ≠ 0 := right_ne_zero_of_mul hK
  set K := g.K0 * Real.cos δ with hKdef
  refine isFilterTrajectory_of g δ (fun t => ?_) (fun t => ?_) (fun t => ?_)
  · show HasDerivAt (fun τ => -(g.D * ρ) / K * τ +
      ρ * (g.D ^ 2 * g.ωc - g.D * K - K * g.M * g.ωc) / (K ^ 2 * g.ωc)) _ t
    exact (((hasDerivAt_id' t).const_mul _).add_const _).congr_deriv (by
      simp only [filterRampParticular, Matrix.cons_val_one, Matrix.cons_val_zero]; ring)
  · show HasDerivAt (fun τ => -(g.D * ρ) / K + ρ * τ) _ t
    exact (((hasDerivAt_id' t).const_mul ρ).const_add _).congr_deriv (by
      simp only [filterRampParticular, Matrix.cons_val_one, Matrix.cons_val_zero,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      field_simp; ring)
  · show HasDerivAt (fun τ => -(g.M * ρ) - g.D * (-(g.D * ρ) / K + ρ * τ)) _ t
    exact ((((hasDerivAt_id' t).const_mul ρ).const_add _).const_mul g.D |>.const_sub _)
      |>.congr_deriv (by
        simp only [filterRampParticular, Matrix.cons_val_zero,
          Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        field_simp; ring)

/-- The three-state Jacobian is Hurwitz for `M, D, ω_c, K > 0` and `K < D ω_c + D²/M`
(`Criteria.isHurwitz_iff_of_coeffs_cubic` on `M s³ + (D + M ω_c) s² + D ω_c s + ω_c K`). -/
@[tmio M, powerlib_domain] private lemma isHurwitz_filterFrequencyPlant (g : VSMLPF) {δ : ℝ}
    (hM : 0 < g.M) (hD : 0 < g.D) (hω : 0 < g.ωc) (hK : 0 < g.K0 * Real.cos δ)
    (hf : g.K0 * Real.cos δ < g.D * g.ωc + g.D ^ 2 / g.M) :
    LinearSystems.IsHurwitz (filterFrequencyPlant g δ).A := by
  rw [show (filterFrequencyPlant g δ).A = g.jacobian δ from rfl,
    Criteria.isHurwitz_iff_of_coeffs_cubic _ hM (a2 := g.D + g.M * g.ωc)
    (a1 := g.D * g.ωc) (a0 := g.ωc * (g.K0 * Real.cos δ))
    (by rw [VSMLPF.trace_jacobian]; field_simp; ring) (VSMLPF.principalMinorSum_jacobian _ _)
    (by rw [VSMLPF.det_jacobian])]
  refine ⟨by positivity, by positivity, ?_⟩
  have : g.M * (g.ωc * (g.K0 * Real.cos δ)) < g.M * (g.ωc * (g.D * g.ωc + g.D ^ 2 / g.M)) :=
    mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hf hω) hM
  have e : g.M * (g.ωc * (g.D * g.ωc + g.D ^ 2 / g.M)) = (g.D + g.M * g.ωc) * (g.D * g.ωc) := by
    field_simp; ring
  linarith

/-- Three states, frequency step `w ≡ c`: `Δω → c`, `Δδ → −D c/K`, `ΔP_f → −D c`, for every
forward trajectory (`M, D, ω_c, K > 0`, `K < D ω_c + D²/M`).
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem filterFrequencyStep_tracking (g : VSMLPF) {δ : ℝ}
    (hM : 0 < g.M) (hD : 0 < g.D) (hω : 0 < g.ωc) (hK : 0 < g.K0 * Real.cos δ)
    (hf : g.K0 * Real.cos δ < g.D * g.ωc + g.D ^ 2 / g.M) (c : ℝ) {x : ℝ → Fin 3 → ℝ}
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x
      ((filterFrequencyPlant g δ).A *ᵥ x t + (filterFrequencyPlant g δ).B *ᵥ ![c]) (Ici 0) t) :
    Tendsto (fun t => x t 0) atTop (𝓝 (-(g.D * c) / (g.K0 * Real.cos δ))) ∧
      Tendsto (fun t => x t 1) atTop (𝓝 c) ∧ Tendsto (fun t => x t 2) atTop (𝓝 (-(g.D * c))) := by
  have hA := isHurwitz_filterFrequencyPlant g hM hD hω hK hf
  have hp := filterStepParticular_isTrajectory g hK.ne' c
  have h0 := LTI.tendsto_sub_of_isHurwitz hA hx hp 0
  have h1 := LTI.tendsto_sub_of_isHurwitz hA hx hp 1
  have h2 := LTI.tendsto_sub_of_isHurwitz hA hx hp 2
  refine ⟨?_, ?_, ?_⟩
  · simpa [filterStepParticular] using h0.add_const (-(g.D * c) / (g.K0 * Real.cos δ))
  · simpa [filterStepParticular] using h1.add_const c
  · simpa [filterStepParticular] using h2.add_const (-(g.D * c))

/-- Three states, frequency ramp `w = ρ t`: `Δω − ρ t → −D ρ/K`, and `|Δδ| → ∞` for `ρ ≠ 0`, for
every forward trajectory.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem filterFrequencyRamp_tracking (g : VSMLPF) {δ : ℝ}
    (hM : 0 < g.M) (hD : 0 < g.D) (hω : 0 < g.ωc) (hK : 0 < g.K0 * Real.cos δ)
    (hf : g.K0 * Real.cos δ < g.D * g.ωc + g.D ^ 2 / g.M) {ρ : ℝ} {x : ℝ → Fin 3 → ℝ}
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x
      ((filterFrequencyPlant g δ).A *ᵥ x t + (filterFrequencyPlant g δ).B *ᵥ ![ρ * t])
        (Ici 0) t) :
    Tendsto (fun t => x t 1 - ρ * t) atTop (𝓝 (-(g.D * ρ) / (g.K0 * Real.cos δ))) ∧
      (ρ ≠ 0 → Tendsto (fun t => |x t 0|) atTop atTop) := by
  have hA := isHurwitz_filterFrequencyPlant g hM hD hω hK hf
  have hp := filterRampParticular_isTrajectory g hM.ne' hω.ne' hK.ne' ρ
  have h0 := LTI.tendsto_sub_of_isHurwitz hA hx hp 0
  have h1 := LTI.tendsto_sub_of_isHurwitz hA hx hp 1
  refine ⟨?_, fun hρ => tendsto_abs_of_sub h0 ?_⟩
  · refine (h1.add_const (-(g.D * ρ) / (g.K0 * Real.cos δ))).congr' ?_ |>.mono_right (by simp)
    exact Eventually.of_forall fun t => by simp [filterRampParticular]; ring
  · have ha : -(g.D * ρ) / (g.K0 * Real.cos δ) ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hD.ne' hρ)) hK.ne'
    simpa [filterRampParticular] using tendsto_abs_affine ha _

/-! ## Nonlinear ramp: the frequency error is unbounded -/

/-- Two states, nonlinear, any grid frequency ramp `θ_g = θ₀ + c t + ρ t²/2`, `ρ ≠ 0`
(`M, D > 0`): along every forward solution of `M Δω̇ = P_ref − P_e(θ − θ_g) − D Δω` the
converter frequency stays bounded (the power curve is bounded), so the frequency error
`Δω − (c + ρ t)` is unbounded: synchronism is lost.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem ramp_frequencyError_unbounded (p : SwingParams)
    (hM : 0 < p.M) (hD : 0 < p.D) {θ₀ c ρ : ℝ} (hρ : ρ ≠ 0) {θ ω : ℝ → ℝ}
    (hω : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt ω
      (angleField p (θ₀ + c * t + ρ * t ^ 2 / 2) (PhasePlane.mk (θ t) (ω t)) 1) (Ici 0) t) :
    Tendsto (fun t => |ω t - (c + ρ * t)|) atTop atTop := by
  obtain ⟨C, hC⟩ := lag_bounded (a := p.M) (b := p.D) (B := |p.Pm - p.k₁| + |p.k₂|) hM hD
    (F := fun t => p.Pm - p.Pe (θ t - (θ₀ + c * t + ρ * t ^ 2 / 2)))
    (fun t _ => by
      show |p.Pm - (p.k₁ + p.k₂ * Real.sin _)| ≤ _
      set x := Real.sin (θ t - (θ₀ + c * t + ρ * t ^ 2 / 2) - p.k₃)
      have hks : |p.k₂ * x| ≤ |p.k₂| := by
        rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
      exact abs_le.mpr ⟨by linarith [neg_abs_le (p.Pm - p.k₁), le_abs_self (p.k₂ * x)],
        by linarith [le_abs_self (p.Pm - p.k₁), neg_abs_le (p.k₂ * x)]⟩)
    hω
    (fun t _ => by
      simp only [angleField_apply_one, PhasePlane.mk_apply_zero, PhasePlane.mk_apply_one,
        SwingParams.accel]
      field_simp)
  exact tendsto_error_of_bounded hC c hρ

/-- Three states (lossless line, power filter), nonlinear, any grid frequency ramp, `ρ ≠ 0`
(`M, D, ω_c > 0`): the filtered power stays bounded, hence the converter frequency, so the
frequency error `Δω − (c + ρ t)` is unbounded along every forward solution of `VSMLPF.fieldU`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
@[tmio TM, powerlib_domain] private theorem filterRamp_frequencyError_unbounded (g : VSMLPF)
    (hM : 0 < g.M) (hD : 0 < g.D) (hω : 0 < g.ωc) {θ₀ c ρ : ℝ} (hρ : ρ ≠ 0)
    {θ ω Pf : ℝ → ℝ}
    (hω' : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt ω
      (g.fieldU (θ₀ + c * t + ρ * t ^ 2 / 2) (mk3 (θ t) (ω t) (Pf t)) 1) (Ici 0) t)
    (hP : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt Pf
      (g.fieldU (θ₀ + c * t + ρ * t ^ 2 / 2) (mk3 (θ t) (ω t) (Pf t)) 2) (Ici 0) t) :
    Tendsto (fun t => |ω t - (c + ρ * t)|) atTop atTop := by
  obtain ⟨CP, hCP⟩ := lag_bounded (a := 1) (b := g.ωc) (B := g.ωc * |g.K0|) one_pos hω
    (F := fun t => g.ωc * (g.K0 * Real.sin (θ t - (θ₀ + c * t + ρ * t ^ 2 / 2))))
    (fun t _ => by
      rw [abs_mul, abs_of_pos hω, abs_mul]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)) hω.le)
    hP (fun t _ => by rw [VSMLPF.fieldU_apply_two]; simp; ring)
  obtain ⟨C, hC⟩ := lag_bounded (a := g.M) (b := g.D) (B := |g.P0| + CP) hM hD
    (F := fun t => g.P0 - Pf t)
    (fun t ht => by
      have h1 := hCP t ht
      exact abs_le.mpr ⟨by linarith [neg_abs_le g.P0, le_abs_self (Pf t)],
        by linarith [le_abs_self g.P0, neg_abs_le (Pf t)]⟩)
    hω' (fun t _ => by simp [VSMLPF.fieldU]; field_simp)
  exact tendsto_error_of_bounded hC c hρ

/-! ## The frame of a grid at a constant frequency offset (two states) -/

/-- The swing machine of the moving frame: power reference `P_ref − D c`. -/
def offsetParams (p : SwingParams) (c : ℝ) : SwingParams :=
  ⟨p.M, p.D, p.Pm - p.D * c, p.k₁, p.k₂, p.k₃⟩

/-- The two-state GFM on a grid at the constant frequency offset `c`, read in the grid frame
about the selected power angle `δ`: the VSM model with the nominal frequency `ω_s = −c` in that
frame. -/
def gridFrame (p : SwingParams) (c δ : ℝ) : DroopVSM.VSMModel :=
  ⟨p.M, p.D, p.Pm, -c, p.Pe, PhasePlane.mk δ 0⟩

/-- The grid-frame field is the swing field with the power reference `P_ref − D c`. -/
@[tmio M, powerlib_domain] theorem gridFrame_vector (p : SwingParams) (c δ : ℝ) (x : State 2) :
    (gridFrame p c δ).vector x = (offsetParams p c).field x := by
  refine PhasePlane.ext_iff'.2 ⟨by simp [DroopVSM.VSMModel.vector], ?_⟩
  simp only [DroopVSM.VSMModel.vector, gridFrame, offsetParams, SwingParams.field,
    SwingParams.accel, SwingParams.Pe, PhasePlane.mk_apply_one]
  ring

/-- Frame change: `(θ, Δω)` solves the nominal-frame loop with grid angle `θ₀ + c t` at `t` iff
`(θ − θ_g, Δω − c)` solves the grid-frame field at `t`, componentwise. -/
@[tmio M, powerlib_domain] theorem gridFrame_hasDerivAt_iff (p : SwingParams) (c θ₀ δ : ℝ)
    (θ ω : ℝ → ℝ) (t : ℝ) :
    (HasDerivAt θ (angleField p (θ₀ + c * t) (PhasePlane.mk (θ t) (ω t)) 0) t ∧
        HasDerivAt ω (angleField p (θ₀ + c * t) (PhasePlane.mk (θ t) (ω t)) 1) t) ↔
      (HasDerivAt (fun s => θ s - (θ₀ + c * s))
          ((gridFrame p c δ).vector (PhasePlane.mk (θ t - (θ₀ + c * t)) (ω t - c)) 0) t ∧
        HasDerivAt (fun s => ω s - c)
          ((gridFrame p c δ).vector (PhasePlane.mk (θ t - (θ₀ + c * t)) (ω t - c)) 1) t) := by
  have hg : HasDerivAt (fun s => θ₀ + c * s) c t := by
    simpa using ((hasDerivAt_id t).const_mul c).const_add θ₀
  have e0 : (gridFrame p c δ).vector (PhasePlane.mk (θ t - (θ₀ + c * t)) (ω t - c)) 0 =
      ω t - c := by simp [DroopVSM.VSMModel.vector]
  have e1 : (gridFrame p c δ).vector (PhasePlane.mk (θ t - (θ₀ + c * t)) (ω t - c)) 1 =
      angleField p (θ₀ + c * t) (PhasePlane.mk (θ t) (ω t)) 1 := by
    simp only [DroopVSM.VSMModel.vector, gridFrame, angleField_apply_one,
      PhasePlane.mk_apply_zero, PhasePlane.mk_apply_one, SwingParams.accel]
    ring_nf
  rw [e0, e1, hasDerivAt_sub_const_iff, angleField_apply_zero, PhasePlane.mk_apply_one]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨h0.sub hg, h1⟩
  · rintro ⟨h0, h1⟩
    refine ⟨?_, h1⟩
    have h := h0.add hg
    rw [sub_add_cancel] at h
    convert h using 1
    funext s
    simp only [Pi.add_apply]
    ring

/-- The shifted equilibrium exists iff the demanded power `P_ref − D c` lies in the range of the
power curve, `|P_ref − D c − c₀| ≤ A` (`M ≠ 0`, `A > 0`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem gridFrame_exists_equilibrium_iff (p : SwingParams)
    (hM : p.M ≠ 0) (hk : 0 < p.k₂) (c δ : ℝ) :
    (∃ x, (gridFrame p c δ).vector x = 0) ↔ |p.Pm - p.D * c - p.k₁| ≤ p.k₂ := by
  simp_rw [gridFrame_vector]
  exact (offsetParams p c).exists_equilibrium_iff hM hk

@[tmio M, powerlib_domain] private lemma contDiff_gridFrame_vector (p : SwingParams) (c δ : ℝ) :
    ContDiff ℝ 1 (gridFrame p c δ).vector := by
  rw [show (gridFrame p c δ).vector = (offsetParams p c).field from
    funext (gridFrame_vector p c δ)]
  exact (offsetParams p c).contDiff_field

/-- Loss of synchronism under a constant grid-frequency offset `c` (the GFM `Σ_FD`): when the
demanded power `P_ref − D c` leaves the band `[c₀ − A, c₀ + A]` no angle balances the power and
every selected angle of the moving-frame model is unstable (`M ≠ 0`, `A > 0`). -/
@[tmio TM, powerlib_domain] theorem gridFrame_mem_den_unstable (p : SwingParams) (hM : p.M ≠ 0)
    {c : ℝ} (h : |p.k₂| < |p.Pm - p.D * c - p.k₁|) :
    connection% (∀ δ, gridFrame p c δ ∈ DroopVSM.vsmFamily.den (.flow .unstable)) := by
  unfold TMIO.Statement
  intro δ
  refine Spectral.mem_den_unstable_of_ne_zero
    (fun m P => Spectral.mem_den_flow_iff_shift (f := DroopVSM.VSMModel.vector)
      (pt := DroopVSM.VSMModel.point) DroopVSM.vsmFamily_isAutonomous)
    (contDiff_gridFrame_vector p c δ) fun h0 => ?_
  rw [DroopVSM.VSMModel.vector_eq_zero_iff _ hM] at h0
  have hb : p.Pe δ = p.Pm - p.D * c := by
    have := h0.2
    simp only [gridFrame, PhasePlane.mk_apply_zero] at this
    linarith
  have hs : |p.k₂ * Real.sin (δ - p.k₃)| ≤ |p.k₂| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  rw [SwingParams.Pe] at hb
  rw [show p.Pm - p.D * c - p.k₁ = p.k₂ * Real.sin (δ - p.k₃) by linarith] at h
  linarith

/-- The shifted angle `δ_s(c) = α + arcsin((P_ref − D c − c₀)/A)` of the moving-frame model is
locally exponentially stable (`M, D, A > 0`, `|P_ref − D c − c₀| < A`): the converter locks to the
offset grid, its frequency follows the grid's (`Δω = c` at the equilibrium). -/
@[tmio TM, powerlib_domain] theorem gridFrame_mem_den_locallyExponentiallyStable
    (p : SwingParams) (hM : 0 < p.M) (hD : 0 < p.D) (hk : 0 < p.k₂) {c : ℝ}
    (h : |p.Pm - p.D * c - p.k₁| < p.k₂) :
    connection% (gridFrame p c (offsetParams p c).deltaS ∈
      DroopVSM.vsmFamily.den (.flow .locallyExponentiallyStable)) := by
  have hb : (offsetParams p c).Pe (offsetParams p c).deltaS = (offsetParams p c).Pm := by
    simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq,
      Synchronous.Swing.Meets] using (offsetParams p c).Pe_deltaS hk h.le
  have hK : 0 < (offsetParams p c).syncCoeff (offsetParams p c).deltaS := by
    simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq,
      Synchronous.Swing.Meets] using (offsetParams p c).syncCoeff_deltaS_pos hk h
  refine DroopVSM.vsm_mem_den_locallyExponentiallyStable _
    (by show ContDiff ℝ 1 p.Pe; unfold SwingParams.Pe; fun_prop) (by simp [gridFrame])
    ?_ hM hD ?_
  · show p.Pe ((PhasePlane.mk (offsetParams p c).deltaS 0) 0) = p.Pm + p.D * -c
    rw [PhasePlane.mk_apply_zero]
    have : (offsetParams p c).Pe (offsetParams p c).deltaS = p.Pe (offsetParams p c).deltaS := rfl
    rw [← this, hb]
    simp [offsetParams]; ring
  · show 0 < deriv p.Pe ((PhasePlane.mk (offsetParams p c).deltaS 0) 0)
    rw [PhasePlane.mk_apply_zero, (p.hasDerivAt_Pe _).deriv]
    exact hK

/-- Synchronism with an offset grid: some selected angle of the moving-frame model is locally
exponentially stable iff the demanded power stays strictly inside the band,
`|P_ref − D c − c₀| < A` (`M, D, A > 0`). The forward direction is the exactness of the swing hub
(`Synchronous.Swing.exactUnder_locallyExponentiallyStable`) read through
`DroopVSM.vsm_mem_den_iff_swing_of_sinusoid`. -/
@[tmio TM, powerlib_domain] theorem gridFrame_synchronism_iff (p : SwingParams) (hM : 0 < p.M)
    (hD : 0 < p.D) (hk : 0 < p.k₂) (c : ℝ) :
    connection% ((∃ δ, gridFrame p c δ ∈
        DroopVSM.vsmFamily.den (.flow .locallyExponentiallyStable)) ↔
      |p.Pm - p.D * c - p.k₁| < p.k₂) := by
  have hex := Synchronous.Swing.exactUnder_locallyExponentiallyStable
  unfold TMIO.Statement at hex ⊢
  constructor
  · rintro ⟨δ, hδ⟩
    have hr := DroopVSM.vsm_mem_den_iff_swing_of_sinusoid (gridFrame p c δ) p.k₁ p.k₂ p.k₃
      (by funext θ; rfl) (by simp [gridFrame]) (.flow .locallyExponentiallyStable)
    unfold TMIO.Statement at hr
    set m : Synchronous.Swing.Model :=
      ⟨⟨p.M, p.D, p.Pm + p.D * -c, p.k₁, p.k₂, p.k₃⟩, (PhasePlane.mk δ 0) 0⟩
    have hm : m ∈ Synchronous.Swing.family.den (.flow .locallyExponentiallyStable) := hr.mp hδ
    have hI : m ∈ TMIO.realize Synchronous.Swing.family.meets {.inertia} :=
      (TMIO.mem_realize _ _ _).mpr fun q hq => by
        rw [Set.mem_singleton_iff.mp hq]; exact hM
    have hR := (Spectral.exactUnder_iff_forall.mp hex m hI).mpr hm
    have hb : m.p.Pe m.δ = m.p.Pm := (TMIO.mem_realize _ _ _).mp hR .balanced
      (by simp [Synchronous.Swing.family, Synchronous.Swing.translate])
    have hs : 0 < m.p.syncCoeff m.δ := (TMIO.mem_realize _ _ _).mp hR .synchronizing
      (by simp [Synchronous.Swing.family, Synchronous.Swing.translate])
    simp only [m, SwingParams.Pe, SwingParams.syncCoeff, PhasePlane.mk_apply_zero] at hb hs
    have hcos : 0 < Real.cos (δ - p.k₃) := pos_of_mul_pos_right hs hk.le
    have hsin : |Real.sin (δ - p.k₃)| < 1 := by
      have h1 := Real.sin_sq_add_cos_sq (δ - p.k₃)
      have h2 : Real.sin (δ - p.k₃) ^ 2 < 1 := by nlinarith
      exact (sq_lt_one_iff_abs_lt_one _).mp h2
    rw [show p.Pm - p.D * c - p.k₁ = p.k₂ * Real.sin (δ - p.k₃) by linarith, abs_mul,
      abs_of_pos hk]
    nlinarith [abs_nonneg (Real.sin (δ - p.k₃))]
  · intro h
    exact ⟨_, gridFrame_mem_den_locallyExponentiallyStable p hM hD hk h⟩

/-! ## The frame of a grid at a constant frequency offset (three states) -/

/-- The VSM + filter model of the moving frame: power reference `P₀ − D c`. -/
def offsetFilter (g : VSMLPF) (c : ℝ) : VSMLPF := ⟨g.M, g.D, g.ωc, g.P0 - g.D * c, g.K0⟩

/-- Frame change, three states: `(θ, Δω, P_f)` solves `VSMLPF.fieldU` with grid angle
`θ₀ + c t` at `t` iff `(θ − θ_g, Δω − c, P_f)` solves the field of `offsetFilter g c` at `t`,
componentwise. -/
@[tmio M, powerlib_domain] theorem filterGridFrame_hasDerivAt_iff (g : VSMLPF) (c θ₀ : ℝ)
    (θ ω Pf : ℝ → ℝ) (t : ℝ) :
    (HasDerivAt θ (g.fieldU (θ₀ + c * t) (mk3 (θ t) (ω t) (Pf t)) 0) t ∧
        HasDerivAt ω (g.fieldU (θ₀ + c * t) (mk3 (θ t) (ω t) (Pf t)) 1) t ∧
        HasDerivAt Pf (g.fieldU (θ₀ + c * t) (mk3 (θ t) (ω t) (Pf t)) 2) t) ↔
      (HasDerivAt (fun s => θ s - (θ₀ + c * s))
          ((offsetFilter g c).field (mk3 (θ t - (θ₀ + c * t)) (ω t - c) (Pf t)) 0) t ∧
        HasDerivAt (fun s => ω s - c)
          ((offsetFilter g c).field (mk3 (θ t - (θ₀ + c * t)) (ω t - c) (Pf t)) 1) t ∧
        HasDerivAt Pf
          ((offsetFilter g c).field (mk3 (θ t - (θ₀ + c * t)) (ω t - c) (Pf t)) 2) t) := by
  have hg : HasDerivAt (fun s => θ₀ + c * s) c t := by
    simpa using ((hasDerivAt_id t).const_mul c).const_add θ₀
  have e0 : g.fieldU (θ₀ + c * t) (mk3 (θ t) (ω t) (Pf t)) 0 = ω t := by
    simp [VSMLPF.fieldU]
  have e1 : g.fieldU (θ₀ + c * t) (mk3 (θ t) (ω t) (Pf t)) 1 =
      (offsetFilter g c).field (mk3 (θ t - (θ₀ + c * t)) (ω t - c) (Pf t)) 1 := by
    simp [VSMLPF.fieldU, offsetFilter]; ring_nf
  have e2 : g.fieldU (θ₀ + c * t) (mk3 (θ t) (ω t) (Pf t)) 2 =
      (offsetFilter g c).field (mk3 (θ t - (θ₀ + c * t)) (ω t - c) (Pf t)) 2 := by
    simp [VSMLPF.fieldU, offsetFilter]
  have e3 : (offsetFilter g c).field (mk3 (θ t - (θ₀ + c * t)) (ω t - c) (Pf t)) 0 =
      ω t - c := by simp
  rw [e0, e1, e2, e3, hasDerivAt_sub_const_iff]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0.sub hg, h1, h2⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, h1, h2⟩
    have h := h0.add hg
    rw [sub_add_cancel] at h
    convert h using 1
    funext s
    simp only [Pi.add_apply]
    ring

/-- Loss of synchronism, three states: when `|P₀ − D c| > |K₀|` no angle balances the power and
every selected angle of the moving-frame VSM + filter model is unstable (`M, ω_c ≠ 0`). -/
@[tmio TM, powerlib_domain] theorem filterGridFrame_mem_den_unstable (g : VSMLPF) (hM : g.M ≠ 0)
    (hω : g.ωc ≠ 0) {c : ℝ} (h : |g.K0| < |g.P0 - g.D * c|) :
    connection% (∀ δ, (⟨offsetFilter g c, δ⟩ : VSMLPF.Model) ∈
      VSMLPF.family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  intro δ
  refine Spectral.mem_den_unstable_of_ne_zero
    (fun m P => Spectral.mem_den_flow_iff_shift (f := fun m : VSMLPF.Model => m.g.field)
      (pt := VSMLPF.Model.point) VSMLPF.family_isAutonomous)
    (offsetFilter g c).contDiff_field fun h0 => ?_
  rw [VSMLPF.Model.field_point_eq_zero_iff _ hM hω] at h0
  have hs : |g.K0 * Real.sin δ| ≤ |g.K0| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  have : (offsetFilter g c).K0 * Real.sin δ = (offsetFilter g c).P0 := h0
  simp only [offsetFilter] at this
  rw [this] at hs
  linarith

/-- Synchronism with an offset grid, three states (`M, D, ω_c, K₀ > 0`): some selected angle is
locally exponentially stable iff `|P₀ − D c| < K₀` and the filter is fast at the shifted loading
angle, `√(K₀² − (P₀ − D c)²) < D ω_c + D²/M` (through the exactness
`VSMLPF.exactUnder_locallyExponentiallyStable`; the converse at the shifted loading angle is
`VSMLPF.locallyExponentiallyStable`). -/
@[tmio TM, powerlib_domain] theorem filterGridFrame_synchronism_iff (g : VSMLPF) (hp : g.Pos)
    (c : ℝ) :
    connection% ((∃ δ, (⟨offsetFilter g c, δ⟩ : VSMLPF.Model) ∈
        VSMLPF.family.den (.flow .locallyExponentiallyStable)) ↔
      |g.P0 - g.D * c| < g.K0 ∧
        Real.sqrt (g.K0 ^ 2 - (g.P0 - g.D * c) ^ 2) < g.D * g.ωc + g.D ^ 2 / g.M) := by
  have hex := VSMLPF.exactUnder_locallyExponentiallyStable
  unfold TMIO.Statement at hex ⊢
  have hM := hp.M; have hD := hp.D; have hω := hp.ωc; have hK0 := hp.K0
  constructor
  · rintro ⟨δ, hδ⟩
    set m : VSMLPF.Model := ⟨offsetFilter g c, δ⟩
    have hI : m ∈ TMIO.realize VSMLPF.family.meets {.physical} :=
      (TMIO.mem_realize _ _ _).mpr fun q hq => by
        rw [Set.mem_singleton_iff.mp hq]; exact ⟨hM, hD, hω⟩
    have hR := (Spectral.exactUnder_iff_forall.mp hex m hI).mpr hδ
    have hb : g.K0 * Real.sin δ = g.P0 - g.D * c := (TMIO.mem_realize _ _ _).mp hR .balanced
      (by simp [VSMLPF.family, VSMLPF.translate])
    have hs : 0 < g.K0 * Real.cos δ := (TMIO.mem_realize _ _ _).mp hR .synchronizing
      (by simp [VSMLPF.family, VSMLPF.translate])
    have hf : g.K0 * Real.cos δ < g.D * g.ωc + g.D ^ 2 / g.M :=
      (TMIO.mem_realize _ _ _).mp hR .fastFilter (by simp [VSMLPF.family, VSMLPF.translate])
    have hsq : (g.K0 * Real.cos δ) ^ 2 = g.K0 ^ 2 - (g.P0 - g.D * c) ^ 2 := by
      rw [← hb]; nlinarith [Real.sin_sq_add_cos_sq δ]
    refine ⟨?_, ?_⟩
    · have : (g.P0 - g.D * c) ^ 2 < g.K0 ^ 2 := by nlinarith
      exact abs_lt_of_sq_lt_sq this hK0.le
    · rw [← hsq, Real.sqrt_sq hs.le]; exact hf
  · rintro ⟨h1, h2⟩
    have hp' : (offsetFilter g c).Pos := ⟨hM, hD, hω, hK0⟩
    refine ⟨(offsetFilter g c).δ0, VSMLPF.locallyExponentiallyStable hp' h1 ?_⟩
    have hK : (offsetFilter g c).K = Real.sqrt (g.K0 ^ 2 - (g.P0 - g.D * c) ^ 2) := by
      simp only [VSMLPF.K, VSMLPF.δ0, offsetFilter, Real.cos_arcsin]
      rw [show g.K0 ^ 2 - (g.P0 - g.D * c) ^ 2 =
          g.K0 ^ 2 * (1 - ((g.P0 - g.D * c) / g.K0) ^ 2) by field_simp,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK0.le]
    rw [hK]
    show Real.sqrt (g.K0 ^ 2 - (g.P0 - g.D * c) ^ 2) / g.D - g.D / g.M < g.ωc
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hD]
    have : (g.ωc + g.D / g.M) * g.D = g.D * g.ωc + g.D ^ 2 / g.M := by ring
    linarith

end powerlib.GFM.Tracking
