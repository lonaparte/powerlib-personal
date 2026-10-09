import theorem.RL

/-! Trajectory semantics for the canonical RL family.  Time starts at zero;
the ODE is required only on `[0, ∞)`, including the right derivative at zero.
The stability predicates below quantify over ALL such trajectories.
State order is `[i]`, the physical scalar branch current in a stationary frame
(not dq coordinates). Voltage follows `L*i' = v - R*i`: the source acts positively
and the resistive drop negatively. `L > 0`; `R` is real, with `R > 0` derived
for strict stability. There is no controller, feedback interconnection, PWM,
PLL, delay, switching, discretization or other state. The input is held constant;
perturbations are about an equilibrium `R*e = v`, not a time-varying trajectory. -/
noncomputable section
namespace powerlib
open Set Filter
open scoped Topology

def IsTrajectory (m : Impedance) (voltage : ℝ) (i : ℝ → ℝ) : Prop :=
  ∀ t ∈ Ici (0 : ℝ),
    HasDerivWithinAt i ((toStateSpace m).field (i t) voltage) (Ici 0) t

def IsEquilibrium (m : Impedance) (voltage equilibrium : ℝ) : Prop :=
  m.resistance * equilibrium = voltage

@[powerlib_foundation] theorem trajectory_iff_circuit (m : Impedance) (v : ℝ) (i : ℝ → ℝ) :
    IsTrajectory m v i ↔ ∀ t ∈ Ici (0 : ℝ),
      HasDerivWithinAt i ((v - m.resistance * i t) / m.inductance.val) (Ici 0) t := by
  simp only [IsTrajectory, same_dynamics]

@[powerlib_foundation] theorem equilibrium_field {m : Impedance} {v e : ℝ} (he : IsEquilibrium m v e) :
    (toStateSpace m).field e v = 0 := by
  rw [same_dynamics, ← he]
  simp

@[powerlib_foundation] theorem field_shift {m : Impedance} {v e : ℝ} (he : IsEquilibrium m v e) (x : ℝ) :
    (toStateSpace m).field x v = (toStateSpace m).field (x - e) 0 := by
  have h := equilibrium_field he
  dsimp [StateSpace.field] at h ⊢
  nlinarith

@[powerlib_foundation] theorem trajectory_shift {m : Impedance} {v e : ℝ} {i : ℝ → ℝ}
    (he : IsEquilibrium m v e) (hi : IsTrajectory m v i) :
    IsTrajectory m 0 (fun t => i t - e) := by
  intro t ht
  simpa only [field_shift he] using (hi t ht).sub_const e

@[simp, powerlib_foundation] theorem zero_equilibrium (m : Impedance) : IsEquilibrium m 0 0 := by
  simp [IsEquilibrium]

@[powerlib_foundation] theorem equilibrium_of_resistance_ne_zero {m : Impedance} (hR : m.resistance ≠ 0) (v : ℝ) :
    IsEquilibrium m v (v / m.resistance) := by
  dsimp [IsEquilibrium]
  field_simp

@[powerlib_domain, aesop safe apply] theorem response_trajectory (m : Impedance) (initial : ℝ) :
    IsTrajectory m 0 (response m initial) := by
  intro t _
  exact (response_solves m initial t).hasDerivWithinAt

@[powerlib_domain] theorem trajectory_eq_response {m : Impedance} {i : ℝ → ℝ}
    (hi : IsTrajectory m 0 i) {t : ℝ} (ht : 0 ≤ t) :
    i t = response m (i 0) t := by
  let a := (toStateSpace m).decay
  have hd : ∀ x ∈ Ici (0 : ℝ),
      HasDerivWithinAt (fun s => i s * Real.exp (a * s)) 0 (Ici 0) x := by
    intro x hx
    convert! (hi x hx).mul
      (((hasDerivAt_id x).const_mul a).exp.hasDerivWithinAt) using 1
    simp [StateSpace.field, a]
    ring
  have hb := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := 0) hd (fun x _ => by simp) (show (0 : ℝ) ∈ Ici 0 by simp) ht
  have hc : i t * Real.exp (a * t) = i 0 := by
    simpa using (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa using hb) (norm_nonneg _))))
  have hh := congrArg (fun z : ℝ => z * Real.exp (-(a * t))) hc
  simpa [response, a, mul_assoc, ← Real.exp_add] using hh

@[powerlib_domain] theorem trajectory_unique {m : Impedance} {i j : ℝ → ℝ}
    (hi : IsTrajectory m 0 i) (hj : IsTrajectory m 0 j) (h0 : i 0 = j 0) :
    EqOn i j (Ici 0) := by
  intro t ht
  rw [trajectory_eq_response hi ht, trajectory_eq_response hj ht, h0]

def equilibriumResponse (m : Impedance) (e initial t : ℝ) : ℝ :=
  e + response m (initial - e) t

@[simp, powerlib_foundation] theorem equilibriumResponse_initial (m : Impedance) (e initial : ℝ) :
    equilibriumResponse m e initial 0 = initial := by
  simp [equilibriumResponse, response_initial]

@[powerlib_domain, aesop safe apply] theorem equilibriumResponse_trajectory {m : Impedance} {v e : ℝ}
    (he : IsEquilibrium m v e) (initial : ℝ) :
    IsTrajectory m v (equilibriumResponse m e initial) := by
  intro t ht
  have h := (response_solves m (initial - e) t).const_add e
  convert! h.hasDerivWithinAt using 1
  rw [field_shift he]
  simp [equilibriumResponse]

@[powerlib_domain] theorem trajectory_exists {m : Impedance} {v e : ℝ}
    (he : IsEquilibrium m v e) (initial : ℝ) :
    ∃ i, IsTrajectory m v i ∧ i 0 = initial :=
  ⟨equilibriumResponse m e initial, equilibriumResponse_trajectory he initial,
    equilibriumResponse_initial m e initial⟩

@[powerlib_domain] theorem trajectory_eq_equilibriumResponse {m : Impedance} {v e : ℝ} {i : ℝ → ℝ}
    (he : IsEquilibrium m v e) (hi : IsTrajectory m v i) {t : ℝ} (ht : 0 ≤ t) :
    i t = equilibriumResponse m e (i 0) t := by
  have h := trajectory_eq_response (trajectory_shift he hi) ht
  dsimp [equilibriumResponse]
  linarith

@[powerlib_domain] theorem trajectory_unique_at_equilibrium {m : Impedance} {v e : ℝ} {i j : ℝ → ℝ}
    (he : IsEquilibrium m v e) (hi : IsTrajectory m v i) (hj : IsTrajectory m v j)
    (h0 : i 0 = j 0) : EqOn i j (Ici 0) := by
  intro t ht
  rw [trajectory_eq_equilibriumResponse he hi ht,
    trajectory_eq_equilibriumResponse he hj ht, h0]

/-- The usual epsilon-delta definition, applied to every forward solution. -/
def LyapunovStable (m : Impedance) (v e : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ i, IsTrajectory m v i → |i 0 - e| < δ →
    ∀ t ≥ 0, |i t - e| < ε

/-- Local attraction, not a definition in terms of the sign of a coefficient. -/
def AsymptoticallyStable (m : Impedance) (v e : ℝ) : Prop :=
  LyapunovStable m v e ∧ ∃ δ > 0, ∀ i, IsTrajectory m v i → |i 0 - e| < δ →
    Tendsto i atTop (𝓝 e)

def GloballyAsymptoticallyStable (m : Impedance) (v e : ℝ) : Prop :=
  LyapunovStable m v e ∧ ∀ i, IsTrajectory m v i → Tendsto i atTop (𝓝 e)

def GloballyExponentiallyStable (m : Impedance) (v e : ℝ) : Prop :=
  ∃ C ≥ (1 : ℝ), ∃ rate > 0, ∀ i, IsTrajectory m v i → ∀ t ≥ 0,
    |i t - e| ≤ C * |i 0 - e| * Real.exp (-rate * t)

@[powerlib_domain] theorem trajectory_error_exact {m : Impedance} {v e : ℝ} {i : ℝ → ℝ}
    (he : IsEquilibrium m v e) (hi : IsTrajectory m v i) {t : ℝ} (ht : 0 ≤ t) :
    |i t - e| = |i 0 - e| * Real.exp (-(toStateSpace m).decay * t) := by
  have h := trajectory_eq_response (trajectory_shift he hi) ht
  rw [h, response, abs_mul, abs_of_pos (Real.exp_pos _)]

@[powerlib_domain, aesop safe forward (immediate := [he, hi])]
theorem trajectory_tendsto {m : Impedance} {v e : ℝ} {i : ℝ → ℝ}
    (hm : m.Stable) (he : IsEquilibrium m v e) (hi : IsTrajectory m v i) :
    Tendsto i atTop (𝓝 e) := by
  have ha : 0 < (toStateSpace m).decay := (stability_agrees m).mpr hm
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(toStateSpace m).decay * t)) atTop (𝓝 0) := by
    simpa only [neg_mul] using! Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop ha)
  have h := (hexp.const_mul (i 0 - e)).const_add e
  have heq : (fun t => e + (i 0 - e) * Real.exp (-(toStateSpace m).decay * t)) =ᶠ[atTop] i := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (trajectory_eq_equilibriumResponse he hi ht).symm
  simpa using h.congr' heq

@[powerlib_domain] theorem lyapunovStable_of_stable {m : Impedance} {v e : ℝ}
    (hm : m.Stable) (he : IsEquilibrium m v e) : LyapunovStable m v e := by
  have ha : 0 < (toStateSpace m).decay := (stability_agrees m).mpr hm
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro i hi h0 t ht
  rw [trajectory_error_exact he hi ht]
  have hx : Real.exp (-(toStateSpace m).decay * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) ht)
  exact (mul_le_of_le_one_right (abs_nonneg _) hx).trans_lt h0

@[powerlib_domain, aesop unsafe 90% apply]
theorem globallyAsymptoticallyStable_of_stable {m : Impedance} {v e : ℝ}
    (hm : m.Stable) (he : IsEquilibrium m v e) : GloballyAsymptoticallyStable m v e :=
  ⟨lyapunovStable_of_stable hm he, fun _ hi => trajectory_tendsto hm he hi⟩

@[powerlib_domain] theorem asymptoticallyStable_of_global {m : Impedance} {v e : ℝ}
    (h : GloballyAsymptoticallyStable m v e) : AsymptoticallyStable m v e :=
  ⟨h.1, 1, zero_lt_one, fun i hi _ => h.2 i hi⟩

@[powerlib_domain] theorem globallyExponentiallyStable_of_stable {m : Impedance} {v e : ℝ}
    (hm : m.Stable) (he : IsEquilibrium m v e) : GloballyExponentiallyStable m v e := by
  refine ⟨1, le_rfl, (toStateSpace m).decay, (stability_agrees m).mpr hm, ?_⟩
  intro i hi t ht
  simp only [one_mul]
  exact (trajectory_error_exact he hi ht).le

/-- A nonpositive decay coefficient prevents even local attraction. -/
@[powerlib_domain] theorem stable_of_asymptoticallyStable {m : Impedance} {v e : ℝ}
    (he : IsEquilibrium m v e) (h : AsymptoticallyStable m v e) : m.Stable := by
  apply (stability_agrees m).mp
  change 0 < (toStateSpace m).decay
  by_contra hn
  have ha : (toStateSpace m).decay ≤ 0 := le_of_not_gt hn
  obtain ⟨δ, hδ, hlocal⟩ := h.2
  have h0 : |equilibriumResponse m e (e + δ / 2) 0 - e| < δ := by
    rw [equilibriumResponse_initial]
    have hp : 0 < δ / 2 := by linarith
    simpa [abs_of_pos hp] using (show δ / 2 < δ by linarith)
  have hlim := hlocal (equilibriumResponse m e (e + δ / 2))
    (equilibriumResponse_trajectory he _) h0
  have hev : ∀ᶠ t : ℝ in atTop,
      equilibriumResponse m e (e + δ / 2) t < e + δ / 4 :=
    hlim.eventually (gt_mem_nhds (by linarith))
  obtain ⟨t, ht, hb⟩ := ((eventually_ge_atTop (0 : ℝ)).and hev).exists
  have hex : 1 ≤ Real.exp (-(toStateSpace m).decay * t) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (neg_nonneg.mpr ha) ht)
  dsimp [equilibriumResponse, response] at hb
  have hp : 0 < δ / 2 := by linarith
  have hm := mul_le_mul_of_nonneg_left hex hp.le
  nlinarith

@[powerlib_domain] theorem asymptoticallyStable_iff_stable {m : Impedance} {v e : ℝ}
    (he : IsEquilibrium m v e) : AsymptoticallyStable m v e ↔ m.Stable :=
  ⟨stable_of_asymptoticallyStable he, fun hm =>
    asymptoticallyStable_of_global (globallyAsymptoticallyStable_of_stable hm he)⟩

@[powerlib_domain, aesop norm simp] theorem asymptoticallyStable_iff_resistance_pos {m : Impedance} {v e : ℝ}
    (he : IsEquilibrium m v e) : AsymptoticallyStable m v e ↔ 0 < m.resistance := by
  rw [asymptoticallyStable_iff_stable he, impedance_stable_iff]

@[powerlib_domain] theorem globallyAsymptoticallyStable_iff_stable {m : Impedance} {v e : ℝ}
    (he : IsEquilibrium m v e) : GloballyAsymptoticallyStable m v e ↔ m.Stable :=
  ⟨fun h => stable_of_asymptoticallyStable he (asymptoticallyStable_of_global h),
    fun hm => globallyAsymptoticallyStable_of_stable hm he⟩

/-- A symbolic certificate constructor: synthesis does not require a supplied witness. -/
def synthesize (m : Impedance) (hR : 0 < m.resistance) : Accepted m where
  p := m.inductance.val / (2 * m.resistance)
  rate := 2 * (toStateSpace m).decay
  p_pos := div_pos m.inductance.property (mul_pos (by norm_num) hR)
  rate_pos := mul_pos (by norm_num)
    ((stability_agrees m).mpr ((impedance_stable_iff m).mpr hR))
  lyapunov_identity := by
    dsimp [toStateSpace, generated.convert, reciprocal]
    field_simp [ne_of_gt hR, ne_of_gt m.inductance.property]
  rate_exact := rfl

@[powerlib_domain] theorem accepted_exists_iff_stable (m : Impedance) : Nonempty (Accepted m) ↔ m.Stable :=
  ⟨fun ⟨c⟩ => c.stable, fun hm => ⟨synthesize m ((impedance_stable_iff m).mp hm)⟩⟩

@[powerlib_domain, aesop norm forward (immediate := [c])]
theorem Accepted.lyapunovStable {m : Impedance} (c : Accepted m) {v e : ℝ}
    (he : IsEquilibrium m v e) : LyapunovStable m v e :=
  lyapunovStable_of_stable c.stable he

@[powerlib_domain] theorem Accepted.globallyAsymptoticallyStable {m : Impedance} (c : Accepted m) {v e : ℝ}
    (he : IsEquilibrium m v e) : GloballyAsymptoticallyStable m v e :=
  globallyAsymptoticallyStable_of_stable c.stable he

@[powerlib_domain, aesop norm forward (immediate := [c])]
theorem Accepted.asymptoticallyStable {m : Impedance} (c : Accepted m) {v e : ℝ}
    (he : IsEquilibrium m v e) : AsymptoticallyStable m v e :=
  asymptoticallyStable_of_global (c.globallyAsymptoticallyStable he)

@[powerlib_domain, aesop norm forward (immediate := [c])]
theorem Accepted.globallyExponentiallyStable {m : Impedance} (c : Accepted m) {v e : ℝ}
    (he : IsEquilibrium m v e) : GloballyExponentiallyStable m v e :=
  globallyExponentiallyStable_of_stable c.stable he

@[powerlib_domain, aesop norm forward (immediate := [c])]
theorem Accepted.trajectory_decay {m : Impedance} (c : Accepted m) {v e : ℝ} {i : ℝ → ℝ}
    (he : IsEquilibrium m v e) (hi : IsTrajectory m v i) {t : ℝ} (ht : 0 ≤ t) :
    (i t - e) ^ 2 = (i 0 - e) ^ 2 * Real.exp (-(c.rate * t)) := by
  rw [trajectory_eq_response (trajectory_shift he hi) ht]
  exact c.decay_bound _ _

@[powerlib_domain, aesop safe apply] theorem Accepted.energy_derivative {m : Impedance} (c : Accepted m) {v e : ℝ} {i : ℝ → ℝ}
    (he : IsEquilibrium m v e) (hi : IsTrajectory m v i) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => energy c.p (i s - e)) (-(i t - e) ^ 2) (Ici 0) t := by
  have h := (((trajectory_shift he hi) t ht).pow 2).const_mul c.p
  convert! h using 1
  · rw [← c.dissipation (i t - e)]
    ring

@[powerlib_domain, aesop unsafe 90% apply]
theorem rl_globally_exponentially_stable (m : Impedance)
    (hR : 0 < m.resistance) (voltage : ℝ) :
    GloballyExponentiallyStable m voltage (voltage / m.resistance) := by
  let certificate := synthesize m hR
  have he : IsEquilibrium m voltage (voltage / m.resistance) :=
    equilibrium_of_resistance_ne_zero (ne_of_gt hR) voltage
  aesop

end powerlib
