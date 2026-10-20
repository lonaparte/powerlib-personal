import theorem.Synchronous.EqualArea

/-! # Equal-area criterion and the three-stage fault sequence of the SMIB swing model

Trajectory-level equal-area criterion and critical clearing time for the switched
(pre-fault / during-fault / post-fault) single-machine infinite-bus swing model.

Model boundary.
* Three instances of the canonical swing model `SwingParams` (`theorem/Synchronous/Swing.lean`):
  the pre-fault, during-fault and post-fault configurations of the same machine.  State
  `(δ, ω) : Dynamics.State 2` (rotor angle relative to the infinite bus, frequency deviation in
  rad/s), `M δ̈ + D δ̇ = P_m − (k₁ + k₂ sin(δ − k₃))`, constant `P_m`, generator OUT-positive
  (Kundur) convention, continuous time; no AVR / governor / PLL / limiter / protection delay.
* Switched dynamics: the fault occurs at `t_f` and is cleared at `t_c ≥ t_f`.  A three-stage
  trajectory is one function `φ : ℝ → State 2` — so the state is continuous at the switching
  instants (trajectory gluing) — that solves the pre-fault field on `(−∞, t_f]`, the
  during-fault field on `[t_f, t_c]` and the post-fault field on `[t_c, ∞)`, with one-sided
  derivatives at the switching instants.  It is written out in each statement as the
  conjunction `tf ≤ tc ∧ IsIntegralCurveOn φ (fun _ x => pre.field x) (Iic tf) ∧
  IsIntegralCurveOn φ (fun _ x => fault.field x) (Icc tf tc) ∧
  IsIntegralCurveOn φ (fun _ x => post.field x) (Ici tc)` (behaviour is defined only in the
  semantic layer, so there is no trajectory structure).
* Single-stage statements: a post-fault statement starts from the clearing state `(δ_c, ω_c)` at
  the clearing time `t_c`, a during-fault statement from the pre-fault equilibrium `(δ₀, 0)` at
  the fault time `t_f`.  Every statement quantifies over every solution of the relevant stage on
  the stated time set.

Source: work-sync `theory/T-transient-stability.md` §1.1, §1.3–§1.6.

Results.
All are private implementation evidence (trajectory-level results outside the sentence language
of `Synchronous.Swing.family`, Rules §3a); the static areas are in
`theorem/Synchronous/EqualArea.lean`.
* Single stage (kept next to the switched-model proofs that use them): energy conservation for
  `D = 0` (`energy_conserved`) and the **exact first-swing equal-area criterion**
  (`firstSwing_iff`, with `firstSwing_le_deltaU`, `exists_gt_deltaU`): a post-fault trajectory
  starting at `(δ_c, ω_c)`, `ω_c > 0`, `δ_u − 2π < δ_c ≤ δ_u`, never exceeds the unstable
  equilibrium angle `δ_u` iff `½ M ω_c² ≤ ∫_{δ_c}^{δ_u} (P_e − P_m)`; bolted three-phase fault
  (`P_e^f ≡ 0`, `D = 0`): explicit during-fault trajectory (`boltedFault_trajectory`) and the
  exact critical clearing time `t_cc = √(2M(δ_cc − δ₀)/P_m)` (`boltedFault_clearingTime`);
  general during-fault curve: time spent in `[δ₀, δ_cc]` is at most
  `√(2M(δ_cc − δ₀)/(P_m − max P_e^f))` (`time_in_window_le`).
* `exists_faultTrajectory`, `faultTrajectory_unique`: from a pre-fault equilibrium the switched
  model has a three-stage trajectory resting at the equilibrium before the fault, and every
  such trajectory agrees with it after the fault (global Lipschitz bound of each stage, generic
  `Flow.forwardComplete_of_lipschitzWith` and LeanForControl's uniqueness).
* `clearing_energy` (`D = 0` during the fault): `½ M ω(t_c)² = A_acc(δ(t_c))
  = ∫_{δ₀}^{δ(t_c)} (P_m − P_e^f)`.
* `firstSwing_iff_areas`: **equal-area criterion** for the switched model (`D = 0`): the
  post-fault trajectory never exceeds the post-fault unstable angle `δ_u` iff
  `A_acc(δ_c) ≤ A_dec(δ_c)`.
* `boltedFault_firstSwing_iff`: **critical clearing time** of a bolted fault (`P_e^f ≡ 0`,
  `D = 0`, `P_m > 0`): with `δ_cc` the zero of `g = A_acc − A_dec` in `[δ₀, δ_u]` (where the
  post-fault curve is positive), the first swing stays below `δ_u` iff
  `t_c − t_f ≤ √(2M(δ_cc − δ₀)/P_m)`; `boltedFault_firstSwing_iff_classical` discharges the
  positivity side condition for the classical lossless curve `P_e^post = P_max sin δ`.

Family and connection conclusions.
* None: no sentence of the library (a flow property of one autonomous field at an equilibrium, or
  passivity) expresses a first-swing bound, a clearing time or a switched trajectory.  The local
  stability of the post-fault equilibria themselves is a connection conclusion of
  `Synchronous.Swing.family` (`Swing.deltaS_mem_den_*`, `Swing.deltaU_mem_den_unstable`).

Corrections (beyond `theorem/Synchronous/EqualArea.lean`).
* T-transient-stability §1.5–§1.6 present `t_cc` and the equal-area criterion for the switched
  system without stating the gluing of the three stages; here the trajectory notion is made
  explicit (the conjunction above) and the criterion is proved for every glued trajectory.  The
  boundary case `A_acc = A_dec` belongs to the stable ("does not cross `δ_u`") side.
-/

noncomputable section
namespace powerlib.Synchronous
open Set Filter Topology intervalIntegral
open powerlib.Dynamics (State)

namespace SwingParams

variable (p : SwingParams)

/-! ## Single stage: energy conservation and the exact first-swing criterion (`D = 0`) -/

/-- Energy is conserved along every solution of the undamped (`D = 0`) swing equation.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem energy_conserved (hM : p.M ≠ 0) (hD : p.D = 0) (δ₀ : ℝ)
    {φ : ℝ → State 2} {a : ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ x => p.field x) (Ici a)) :
    ∀ t ∈ Ici a, p.energy δ₀ (φ t) = p.energy δ₀ (φ a) := by
  have hdiff : Differentiable ℝ (p.energy δ₀) :=
    (p.contDiff_energy (k := 1) δ₀).differentiable (by norm_num)
  have h1 := antitoneOn_V_comp_traj hdiff hdiff.continuous (convex_Ici a) hφ
    (fun t _ => by rw [p.energy_lie hM, hD]; simp)
  have hneg : ∀ x, fderiv ℝ (fun y => -p.energy δ₀ y) x (p.field x) ≤ 0 := by
    intro x
    rw [fderiv_fun_neg, _root_.neg_apply, p.energy_lie hM, hD]
    simp
  have h2 := antitoneOn_V_comp_traj (V := fun x => -p.energy δ₀ x) hdiff.neg
    hdiff.neg.continuous (convex_Ici a) hφ (fun t _ => hneg (φ t))
  intro t ht
  have ha : a ∈ Ici a := mem_Ici.mpr le_rfl
  have e1 := h1 ha ht ht
  have e2 := h2 ha ht ht
  simp only [Function.comp_apply] at e1 e2
  linarith

/-- Sufficiency: if the clearing kinetic energy does not exceed the decelerating area up to the
unstable angle, the post-fault trajectory never goes beyond `δ_u`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem firstSwing_le_deltaU (hM : 0 < p.M) (hD : p.D = 0) (hk : 0 < p.k₂)
    (h : |p.Pm - p.k₁| < p.k₂) {φ : ℝ → State 2} {tc δc ωc : ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ x => p.field x) (Ici tc))
    (h0 : φ tc = PhasePlane.mk δc ωc) (hδc : δc ≤ p.deltaU)
    (hE : p.M / 2 * ωc ^ 2 ≤ ∫ s in δc..p.deltaU, (p.Pe s - p.Pm)) :
    ∀ t ∈ Ici tc, φ t 0 ≤ p.deltaU := by
  intro t ht
  by_contra hlt
  push Not at hlt
  have hcont : ContinuousOn (fun τ => φ τ 0) (Icc tc t) :=
    (p.coord_continuousOn hφ 0).mono Icc_subset_Ici_self
  obtain ⟨ts, hts, hδs⟩ := intermediate_value_Icc ht hcont
    ⟨by simpa [h0] using hδc, hlt.le⟩
  simp only at hδs
  have hcons := p.energy_conserved hM.ne' hD δc hφ ts hts.1
  rw [h0] at hcons
  simp only [energy, PhasePlane.mk_apply_zero, PhasePlane.mk_apply_one, potential_self, add_zero,
    hδs] at hcons
  rw [← potential_eq_integral] at hE
  have hω : φ ts 1 = 0 := by
    have : p.M / 2 * φ ts 1 ^ 2 ≤ 0 := by linarith
    have h2 : 0 < p.M / 2 := by positivity
    have := nonpos_of_mul_nonpos_right this h2 |>.antisymm (sq_nonneg _)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have hsteq : φ ts = PhasePlane.mk p.deltaU 0 :=
    PhasePlane.ext_iff'.2 ⟨by simpa using hδs, by simpa using hω⟩
  have heqf := p.field_mkState_deltaU hM.ne' hk h.le
  have huniq := eqOn_of_isIntegralCurveOn_Icc (f := fun _ x => p.field x)
    (fun _ => p.lipschitzWith_field) (hφ.mono (Icc_subset_Ici_iff hts.2 |>.mpr hts.1))
    (p.isIntegralCurveOn_const heqf (Icc ts t)) (by simpa using hsteq)
  have := huniq ⟨hts.2, le_rfl⟩
  simp only at this
  rw [this] at hlt
  simp at hlt

/-- Necessity: a forward swing (`ω_c > 0`) from the potential well whose kinetic energy exceeds
the decelerating area goes beyond `δ_u` in finite time.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem exists_gt_deltaU (hM : 0 < p.M) (hD : p.D = 0) (hk : 0 < p.k₂)
    (h : |p.Pm - p.k₁| < p.k₂) {φ : ℝ → State 2} {tc δc ωc : ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ x => p.field x) (Ici tc))
    (h0 : φ tc = PhasePlane.mk δc ωc) (hwell : p.deltaU - 2 * Real.pi < δc) (hδc : δc ≤ p.deltaU)
    (hω : 0 < ωc) (hE : ∫ s in δc..p.deltaU, (p.Pe s - p.Pm) < p.M / 2 * ωc ^ 2) :
    ∃ t ∈ Ici tc, p.deltaU < φ t 0 := by
  by_contra hno
  push Not at hno
  rw [← potential_eq_integral] at hE
  set W0 := p.M / 2 * ωc ^ 2
  set c := min W0 (W0 - p.potential δc p.deltaU) with hcdef
  have hW0 : 0 < W0 := by positivity
  have hc : 0 < c := lt_min hW0 (by linarith)
  have hcons : ∀ t ∈ Ici tc, p.M / 2 * φ t 1 ^ 2 + p.potential δc (φ t 0) = W0 := by
    intro t ht
    have := p.energy_conserved hM.ne' hD δc hφ t ht
    rw [h0] at this
    simpa [energy] using this
  -- inside the window `[δ_c, δ_u]` the kinetic energy is at least `c`
  have hkin : ∀ t ∈ Ici tc, φ t 0 ∈ Icc δc p.deltaU → c ≤ p.M / 2 * φ t 1 ^ 2 := by
    intro t ht hwin
    have hU := p.potential_le_max hk h (δ₀ := δc) hwell hwin
    have := hcons t ht
    rw [potential_self] at hU
    rcases le_total (p.potential δc p.deltaU) 0 with hl | hl
    · rw [max_eq_left hl] at hU
      exact (min_le_left _ _).trans (by linarith)
    · rw [max_eq_right hl] at hU
      exact (min_le_right _ _).trans (by linarith)
  have hδ0 : φ tc 0 = δc := by simp [h0]
  have hω0 : φ tc 1 = ωc := by simp [h0]
  have hderiv : ∀ x ∈ Ioi tc, HasDerivAt (fun τ => φ τ 0) (φ x 1) x := by
    intro x hx
    have := p.coord_hasDerivAt hφ (mem_Ici.mpr (le_of_lt hx)) (Ici_mem_nhds hx) 0
    simpa using this
  -- the frequency deviation stays positive
  have hpos : ∀ T ∈ Ici tc, ∀ t ∈ Icc tc T, 0 < φ t 1 := by
    intro T hT
    apply Dynamics.pos_on_Icc_of_propagate ((p.coord_continuousOn hφ 1).mono Icc_subset_Ici_self)
      (by rw [hω0]; exact hω)
    intro t ht hbefore
    have hmono : MonotoneOn (fun τ => φ τ 0) (Icc tc t) :=
      Dynamics.monotoneOn_Icc_of_hasDerivAt ((p.coord_continuousOn hφ 0).mono Icc_subset_Ici_self)
        (fun x hx => hderiv x hx.1) (fun x hx => (hbefore x ⟨hx.1.le, hx.2⟩).le)
    have hwin : φ t 0 ∈ Icc δc p.deltaU :=
      ⟨by simpa [hδ0] using hmono ⟨le_rfl, ht.1.le⟩ ⟨ht.1.le, le_rfl⟩ ht.1.le,
        hno t ht.1.le⟩
    have hk2 := hkin t ht.1.le hwin
    have hne : φ t 1 ≠ 0 := by
      intro h0'; rw [h0'] at hk2; simp at hk2; linarith
    rcases lt_or_gt_of_ne hne with hneg | hp
    · exfalso
      obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht.1.le
        ((p.coord_continuousOn hφ 1).mono Icc_subset_Ici_self)
        ⟨hneg.le, by rw [hω0]; exact hω.le⟩
      simp only at hs0
      have hst : s ≠ t := by rintro rfl; linarith
      have := hbefore s ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
      linarith
    · exact hp
  -- hence the angle grows at least linearly
  set w := Real.sqrt (2 * c / p.M) with hwdef
  have hw : 0 < w := Real.sqrt_pos.mpr (by positivity)
  have hωw : ∀ t ∈ Ici tc, w ≤ φ t 1 := by
    intro t ht
    have hmono : MonotoneOn (fun τ => φ τ 0) (Icc tc t) :=
      Dynamics.monotoneOn_Icc_of_hasDerivAt ((p.coord_continuousOn hφ 0).mono Icc_subset_Ici_self)
        (fun x hx => hderiv x hx.1) (fun x hx => (hpos t ht x ⟨hx.1.le, hx.2.le⟩).le)
    have hwin : φ t 0 ∈ Icc δc p.deltaU :=
      ⟨by simpa [hδ0] using hmono ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht, hno t ht⟩
    have hk2 := hkin t ht hwin
    have hp := hpos t ht t ⟨ht, le_rfl⟩
    rw [hwdef, ← Real.sqrt_sq hp.le]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ hM]
    linarith
  set T := tc + (p.deltaU - δc) / w + 1
  have hT : T ∈ Ici tc := by
    show tc ≤ T
    have : 0 ≤ (p.deltaU - δc) / w := div_nonneg (by linarith) hw.le
    linarith
  have hlin : MonotoneOn (fun τ => φ τ 0 - w * τ) (Icc tc T) :=
    Dynamics.monotoneOn_Icc_of_hasDerivAt
      (((p.coord_continuousOn hφ 0).mono Icc_subset_Ici_self).sub (by fun_prop))
      (fun x hx => (hderiv x hx.1).sub ((hasDerivAt_id x).const_mul w))
      (fun x hx => by simp only [mul_one]; linarith [hωw x hx.1.le])
  have := hlin ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
  simp only [hδ0] at this
  have hTval : w * (T - tc) = (p.deltaU - δc) + w := by
    simp only [T]; field_simp; ring
  have := hno T hT
  nlinarith

/-- **Exact first-swing equal-area criterion** (`D = 0`, `ω_c > 0`, clearing angle in the
potential well `δ_u − 2π < δ_c ≤ δ_u`): the post-fault trajectory never exceeds the unstable
equilibrium angle iff `½ M ω_c² ≤ ∫_{δ_c}^{δ_u} (P_e − P_m) dδ`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem firstSwing_iff (hM : 0 < p.M) (hD : p.D = 0) (hk : 0 < p.k₂)
    (h : |p.Pm - p.k₁| < p.k₂) {φ : ℝ → State 2} {tc δc ωc : ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ x => p.field x) (Ici tc))
    (h0 : φ tc = PhasePlane.mk δc ωc) (hwell : p.deltaU - 2 * Real.pi < δc) (hδc : δc ≤ p.deltaU)
    (hω : 0 < ωc) :
    (∀ t ∈ Ici tc, φ t 0 ≤ p.deltaU) ↔
      p.M / 2 * ωc ^ 2 ≤ ∫ s in δc..p.deltaU, (p.Pe s - p.Pm) := by
  constructor
  · intro hle
    by_contra hgt
    push Not at hgt
    obtain ⟨t, ht, hlt⟩ := p.exists_gt_deltaU hM hD hk h hφ h0 hwell hδc hω hgt
    exact absurd (hle t ht) (not_le.mpr hlt)
  · exact p.firstSwing_le_deltaU hM hD hk h hφ h0 hδc

/-! ## Critical clearing time -/

/-- Bolted fault at the receiving bus (`P_e^f ≡ 0`, `D = 0`): the during-fault trajectory from
the pre-fault equilibrium `(δ₀, 0)` is `ω = (P_m/M)(t − t_f)`,
`δ = δ₀ + (P_m/(2M))(t − t_f)²`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem boltedFault_trajectory (hM : 0 < p.M) (hD : p.D = 0)
    (hk₁ : p.k₁ = 0) (hk₂ : p.k₂ = 0) {φ : ℝ → State 2} {tf T δ₀ : ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ x => p.field x) (Icc tf T))
    (h0 : φ tf = PhasePlane.mk δ₀ 0) :
    ∀ t ∈ Icc tf T, φ t 1 = p.Pm / p.M * (t - tf) ∧
      φ t 0 = δ₀ + p.Pm / (2 * p.M) * (t - tf) ^ 2 := by
  have hacc : ∀ x : State 2, p.field x 1 = p.Pm / p.M := by
    intro x; simp [accel, Pe, hD, hk₁, hk₂]
  have hd := hasDerivWithinAt_Ici_of_isIntegralCurveOn hφ
  have hcont := hφ.continuousOn
  have hproj (j : Fin 2) := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) j : State 2 →L[ℝ] ℝ)
  have h1 : ∀ t ∈ Icc tf T, φ t 1 - p.Pm / p.M * (t - tf) = φ tf 1 - p.Pm / p.M * (tf - tf) := by
    apply constant_of_has_deriv_right_zero
    · exact (((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : State 2 →L[ℝ] ℝ).continuous).comp_continuousOn
        hcont).sub (by fun_prop)
    · intro x hx
      have := ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 :
        State 2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt x (hd x hx)).sub
          (((hasDerivAt_id x).sub_const tf).const_mul (p.Pm / p.M)).hasDerivWithinAt
      convert this using 1
      · funext y; simp [Function.comp_def]
      · simp [hacc]
  have hω : ∀ t ∈ Icc tf T, φ t 1 = p.Pm / p.M * (t - tf) := by
    intro t ht; have := h1 t ht; simp [h0] at this; linarith
  have h2 : ∀ t ∈ Icc tf T, φ t 0 - p.Pm / (2 * p.M) * (t - tf) ^ 2 =
      φ tf 0 - p.Pm / (2 * p.M) * (tf - tf) ^ 2 := by
    apply constant_of_has_deriv_right_zero
    · exact (((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : State 2 →L[ℝ] ℝ).continuous).comp_continuousOn
        hcont).sub (by fun_prop)
    · intro x hx
      have := ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 :
        State 2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt x (hd x hx)).sub
          ((((hasDerivAt_id x).sub_const tf).pow 2).const_mul (p.Pm / (2 * p.M))).hasDerivWithinAt
      convert this using 1
      · funext y; simp [Function.comp_def]
      · simp only [PiLp.proj_apply, field_apply_zero, id_eq]
        rw [hω x ⟨hx.1, hx.2.le⟩]
        field_simp
        ring
  intro t ht
  refine ⟨hω t ht, ?_⟩
  have := h2 t ht
  simp [h0] at this
  linarith

/-- Exact critical clearing time for a bolted fault (`P_e^f ≡ 0`, `D = 0`, `P_m > 0`): the
during-fault angle reaches `δ_cc ≥ δ₀` exactly at `t = t_f + √(2M(δ_cc − δ₀)/P_m)`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem boltedFault_clearingTime (hM : 0 < p.M) (hD : p.D = 0)
    (hk₁ : p.k₁ = 0) (hk₂ : p.k₂ = 0) (hPm : 0 < p.Pm) {φ : ℝ → State 2} {tf T δ₀ δcc : ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ x => p.field x) (Icc tf T))
    (h0 : φ tf = PhasePlane.mk δ₀ 0) (hcc : δ₀ ≤ δcc) {t : ℝ} (ht : t ∈ Icc tf T) :
    φ t 0 = δcc ↔ t = tf + Real.sqrt (2 * p.M * (δcc - δ₀) / p.Pm) := by
  rw [(p.boltedFault_trajectory hM hD hk₁ hk₂ hφ h0 t ht).2]
  have hτ : 0 ≤ t - tf := by linarith [ht.1]
  constructor
  · intro he
    have hsq : (t - tf) ^ 2 = 2 * p.M * (δcc - δ₀) / p.Pm := by
      field_simp; field_simp at he; linarith
    have := Real.sqrt_sq hτ
    rw [hsq] at this
    linarith
  · intro he
    have hs : (t - tf) = Real.sqrt (2 * p.M * (δcc - δ₀) / p.Pm) := by linarith
    have hsq := Real.sq_sqrt (show 0 ≤ 2 * p.M * (δcc - δ₀) / p.Pm by
      apply div_nonneg _ hPm.le; nlinarith)
    rw [hs, hsq]
    field_simp
    ring

/-- Clearing-time bound for a general during-fault curve (`D = 0`): if `P_e^f ≤ p_max < P_m`
on `[δ₀, δ_cc]`, a trajectory starting from `(δ₀, 0)` cannot stay inside the angle window
`[δ₀, δ_cc]` for longer than `√(2M(δ_cc − δ₀)/(P_m − p_max))`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem time_in_window_le (hM : 0 < p.M) (hD : p.D = 0) {pmax δ₀ δcc : ℝ}
    (hgap : pmax < p.Pm) (hbound : ∀ δ ∈ Icc δ₀ δcc, p.Pe δ ≤ pmax) {φ : ℝ → State 2}
    {tf T : ℝ} (hφ : IsIntegralCurveOn φ (fun _ x => p.field x) (Icc tf T))
    (h0 : φ tf = PhasePlane.mk δ₀ 0) {t : ℝ} (ht : t ∈ Icc tf T)
    (hwin : ∀ s ∈ Icc tf t, φ s 0 ∈ Icc δ₀ δcc) :
    t - tf ≤ Real.sqrt (2 * p.M * (δcc - δ₀) / (p.Pm - pmax)) := by
  set a := (p.Pm - pmax) / p.M with hadef
  have ha : 0 < a := div_pos (by linarith) hM
  have hsub : Icc tf t ⊆ Icc tf T := Icc_subset_Icc_right ht.2
  have hφ' := hφ.mono hsub
  have hder : ∀ x ∈ Ioo tf t, ∀ j, HasDerivAt (fun τ => φ τ j) (p.field (φ x) j) x :=
    fun x hx j => p.coord_hasDerivAt hφ' ⟨hx.1.le, hx.2.le⟩ (Icc_mem_nhds hx.1 hx.2) j
  have hc (j : Fin 2) : ContinuousOn (fun τ => φ τ j) (Icc tf t) := p.coord_continuousOn hφ' j
  have hω : MonotoneOn (fun τ => φ τ 1 - a * (τ - tf)) (Icc tf t) := by
    apply Dynamics.monotoneOn_Icc_of_hasDerivAt ((hc 1).sub (by fun_prop))
      (fun x hx => (hder x hx 1).sub (((hasDerivAt_id x).sub_const tf).const_mul a))
    intro x hx
    have hb := hbound _ (hwin x ⟨hx.1.le, hx.2.le⟩)
    simp only [field_apply_one, accel, hD, zero_mul, sub_zero, mul_one]
    rw [hadef, ← sub_div]
    exact div_nonneg (by linarith) hM.le
  have hωlow : ∀ x ∈ Icc tf t, a * (x - tf) ≤ φ x 1 := by
    intro x hx
    have := hω ⟨le_rfl, ht.1⟩ hx hx.1
    simp [h0] at this
    linarith
  have hδ : MonotoneOn (fun τ => φ τ 0 - a / 2 * (τ - tf) ^ 2) (Icc tf t) := by
    apply Dynamics.monotoneOn_Icc_of_hasDerivAt ((hc 0).sub (by fun_prop))
      (fun x hx => (hder x hx 0).sub ((((hasDerivAt_id x).sub_const tf).pow 2).const_mul (a / 2)))
    intro x hx
    have := hωlow x ⟨hx.1.le, hx.2.le⟩
    simp only [field_apply_zero, id_eq]
    norm_num
    linarith
  have hfin := hδ ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩ ht.1
  simp [h0] at hfin
  have hupper := (hwin t ⟨ht.1, le_rfl⟩).2
  have hτ : 0 ≤ t - tf := by linarith [ht.1]
  rw [← Real.sqrt_sq hτ]
  apply Real.sqrt_le_sqrt
  rw [le_div_iff₀ (by linarith)]
  have : (t - tf) ^ 2 * (p.Pm - pmax) = 2 * p.M * (a / 2 * (t - tf) ^ 2) := by
    rw [hadef]; field_simp
  rw [this]
  nlinarith

end SwingParams

/-! ## The switched model -/

/-- Existence for the switched model: from a pre-fault equilibrium `x₀` there is a three-stage
(pre-fault / during-fault / post-fault) trajectory with switching instants `t_f ≤ t_c` — one
function `φ`, so the stages are glued by continuity of the state, solving the pre-fault field on
`(−∞, t_f]`, the during-fault field on `[t_f, t_c]` and the post-fault field on `[t_c, ∞)` —
that rests at `x₀` up to the fault instant.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem exists_faultTrajectory (pre fault post : SwingParams) {x₀ : State 2}
    (hx₀ : pre.field x₀ = 0) {tf tc : ℝ} (htc : tf ≤ tc) :
    ∃ φ : ℝ → State 2, (tf ≤ tc ∧ IsIntegralCurveOn φ (fun _ x => pre.field x) (Iic tf) ∧
        IsIntegralCurveOn φ (fun _ x => fault.field x) (Icc tf tc) ∧
        IsIntegralCurveOn φ (fun _ x => post.field x) (Ici tc)) ∧
      ∀ t ∈ Iic tf, φ t = x₀ := by
  obtain ⟨φ1, h1₀, h1⟩ := Flow.forwardComplete_of_lipschitzWith fault.lipschitzWith_field tf x₀
  obtain ⟨φ2, h2₀, h2⟩ := Flow.forwardComplete_of_lipschitzWith post.lipschitzWith_field tc
    (φ1 tc)
  let φ : ℝ → State 2 := fun t => if t ≤ tf then x₀ else if t ≤ tc then φ1 t else φ2 t
  have e0 : EqOn φ (fun _ => x₀) (Iic tf) := fun t ht => by
    simp [φ, show t ≤ tf from ht]
  have e1 : EqOn φ φ1 (Icc tf tc) := by
    intro t ht
    by_cases h : t ≤ tf
    · have : t = tf := le_antisymm h ht.1
      simp [φ, this, h1₀]
    · simp [φ, h, ht.2]
  have e2 : EqOn φ φ2 (Ici tc) := by
    intro t ht
    have ht' : tc ≤ t := ht
    by_cases h : t ≤ tf
    · have hEq : t = tf := le_antisymm h (htc.trans ht')
      have hEq' : tc = tf := le_antisymm (ht'.trans h) htc
      simp only [φ, h, ite_true]
      rw [hEq, ← hEq', h2₀, hEq', h1₀]
    · by_cases h' : t ≤ tc
      · have hEq : t = tc := le_antisymm h' ht'
        simp only [φ, h, h', ite_true, ite_false]
        rw [hEq, h2₀]
      · simp only [φ, h, h', ite_false]
  refine ⟨φ, ⟨htc, ?_, ?_, ?_⟩, fun t ht => e0 ht⟩
  · intro t ht
    show HasDerivWithinAt φ (pre.field (φ t)) (Iic tf) t
    rw [e0 ht, hx₀]
    exact (hasDerivWithinAt_const t (Iic tf) x₀).congr e0 (e0 ht)
  · intro t ht
    show HasDerivWithinAt φ (fault.field (φ t)) (Icc tf tc) t
    rw [e1 ht]
    exact ((h1 t ht.1).mono Icc_subset_Ici_self).congr e1 (e1 ht)
  · intro t ht
    show HasDerivWithinAt φ (post.field (φ t)) (Ici tc) t
    rw [e2 ht]
    exact (h2 t ht).congr e2 (e2 ht)

/-- Uniqueness for the switched model: two three-stage trajectories (`tf ≤ tc`, pre-fault field
on `Iic tf`, during-fault field on `Icc tf tc`, post-fault field on `Ici tc`) with the same state
at the fault instant agree at every later time.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem faultTrajectory_unique {pre fault post : SwingParams} {tf tc : ℝ}
    {φ ψ : ℝ → State 2}
    (hφ : tf ≤ tc ∧ IsIntegralCurveOn φ (fun _ x => pre.field x) (Iic tf) ∧
        IsIntegralCurveOn φ (fun _ x => fault.field x) (Icc tf tc) ∧
        IsIntegralCurveOn φ (fun _ x => post.field x) (Ici tc))
    (hψ : tf ≤ tc ∧ IsIntegralCurveOn ψ (fun _ x => pre.field x) (Iic tf) ∧
        IsIntegralCurveOn ψ (fun _ x => fault.field x) (Icc tf tc) ∧
        IsIntegralCurveOn ψ (fun _ x => post.field x) (Ici tc))
    (h0 : φ tf = ψ tf) :
    ∀ t ∈ Ici tf, φ t = ψ t := by
  have hfault : EqOn φ ψ (Icc tf tc) :=
    eqOn_of_isIntegralCurveOn_Icc (fun _ => fault.lipschitzWith_field) hφ.2.2.1
      hψ.2.2.1 h0
  have hc : φ tc = ψ tc := hfault ⟨hφ.1, le_rfl⟩
  intro t ht
  rcases le_total t tc with h | h
  · exact hfault ⟨ht, h⟩
  · exact eqOn_of_isIntegralCurveOn_Icc (fun _ => post.lipschitzWith_field)
      (hφ.2.2.2.mono Icc_subset_Ici_self) (hψ.2.2.2.mono Icc_subset_Ici_self) hc ⟨h, le_rfl⟩

namespace SwingParams

variable (p : SwingParams)

/-- Energy conservation (`D = 0`) along a solution on a compact time interval.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem energy_conserved_Icc (hM : p.M ≠ 0) (hD : p.D = 0) (δ₀ : ℝ)
    {φ : ℝ → State 2} {a b : ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ x => p.field x) (Icc a b)) :
    ∀ t ∈ Icc a b, p.energy δ₀ (φ t) = p.energy δ₀ (φ a) := by
  have hdiff : Differentiable ℝ (p.energy δ₀) :=
    (p.contDiff_energy (k := 1) δ₀).differentiable (by norm_num)
  apply constant_of_has_deriv_right_zero (f := fun t => p.energy δ₀ (φ t))
    (hdiff.continuous.comp_continuousOn hφ.continuousOn)
  intro x hx
  have hd := hasDerivWithinAt_Ici_of_isIntegralCurveOn hφ x hx
  have h := (hdiff (φ x)).hasFDerivAt.comp_hasDerivWithinAt x hd
  rw [p.energy_lie hM, hD, neg_zero, zero_mul] at h
  exact h

end SwingParams

/-- Clearing energy: with an undamped during-fault stage started at `(δ₀, 0)`, the kinetic
energy at clearing equals the accelerating area, `½ M ω(t_c)² = A_acc(δ₀, δ(t_c))`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem clearing_energy {fault : SwingParams} (hM : fault.M ≠ 0)
    (hD : fault.D = 0) {φ : ℝ → State 2} {tf tc δ₀ : ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ x => fault.field x) (Icc tf tc)) (htc : tf ≤ tc)
    (h0 : φ tf = PhasePlane.mk δ₀ 0) :
    fault.M / 2 * φ tc 1 ^ 2 = fault.Aacc δ₀ (φ tc 0) := by
  have h := fault.energy_conserved_Icc hM hD δ₀ hφ tc ⟨htc, le_rfl⟩
  rw [h0] at h
  simp only [SwingParams.energy, PhasePlane.mk_apply_zero, PhasePlane.mk_apply_one,
    SwingParams.potential_self, add_zero] at h
  rw [SwingParams.Aacc_eq_neg_potential]
  norm_num at h
  linarith

/-- **Equal-area criterion for the switched model** (`D = 0` in the fault and post-fault stages,
same inertia): if the clearing state lies in the post-fault potential well
(`δ_u − 2π < δ_c ≤ δ_u`) and moves forward (`ω_c > 0`), the post-fault trajectory never exceeds
`δ_u` iff `A_acc(δ₀, δ_c) ≤ A_dec(δ_c, δ_u)`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem firstSwing_iff_areas {pre fault post : SwingParams}
    (hM : 0 < post.M) (hMeq : fault.M = post.M) (hDf : fault.D = 0) (hDp : post.D = 0)
    (hk : 0 < post.k₂) (h : |post.Pm - post.k₁| < post.k₂) {φ : ℝ → State 2} {tf tc δ₀ : ℝ}
    (hφ : tf ≤ tc ∧ IsIntegralCurveOn φ (fun _ x => pre.field x) (Iic tf) ∧
        IsIntegralCurveOn φ (fun _ x => fault.field x) (Icc tf tc) ∧
        IsIntegralCurveOn φ (fun _ x => post.field x) (Ici tc))
    (h0 : φ tf = PhasePlane.mk δ₀ 0)
    (hwell : post.deltaU - 2 * Real.pi < φ tc 0) (hδc : φ tc 0 ≤ post.deltaU)
    (hω : 0 < φ tc 1) :
    (∀ t ∈ Ici tc, φ t 0 ≤ post.deltaU) ↔
      fault.Aacc δ₀ (φ tc 0) ≤ post.Adec (φ tc 0) post.deltaU := by
  have hE := clearing_energy (hMeq ▸ hM.ne') hDf hφ.2.2.1 hφ.1 h0
  rw [hMeq] at hE
  rw [← hE, SwingParams.Adec]
  exact post.firstSwing_iff hM hDp hk h hφ.2.2.2 (PhasePlane.mk_coords (φ tc)).symm hwell hδc hω

/-- **Critical clearing time of a bolted fault** (`P_e^f ≡ 0`, `D = 0`, `P_m > 0`, same `M` and
`P_m` in both stages).  Let `δ_cc ∈ [δ₀, δ_u]` be a zero of `g = A_acc − A_dec`, and let the
post-fault curve be positive on `(δ₀, δ_u)`.  Then the first swing stays below `δ_u` iff the
fault is cleared within `t_c − t_f ≤ √(2M(δ_cc − δ₀)/P_m)`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem boltedFault_firstSwing_iff {pre fault post : SwingParams}
    (hM : 0 < post.M) (hMeq : fault.M = post.M) (hPm : fault.Pm = post.Pm) (hPm0 : 0 < post.Pm)
    (hDf : fault.D = 0) (hDp : post.D = 0) (hk₁ : fault.k₁ = 0) (hk₂ : fault.k₂ = 0)
    (hk : 0 < post.k₂) (h : |post.Pm - post.k₁| < post.k₂) {φ : ℝ → State 2} {tf tc δ₀ δcc : ℝ}
    (hφ : tf ≤ tc ∧ IsIntegralCurveOn φ (fun _ x => pre.field x) (Iic tf) ∧
        IsIntegralCurveOn φ (fun _ x => fault.field x) (Icc tf tc) ∧
        IsIntegralCurveOn φ (fun _ x => post.field x) (Ici tc))
    (h0 : φ tf = PhasePlane.mk δ₀ 0) (htc : tf < tc)
    (hwell : post.deltaU - 2 * Real.pi < δ₀) (hpos : ∀ x ∈ Ioo δ₀ post.deltaU, 0 < post.Pe x)
    (hcc : δcc ∈ Icc δ₀ post.deltaU) (hg : eacG fault post δ₀ post.deltaU δcc = 0) :
    (∀ t ∈ Ici tc, φ t 0 ≤ post.deltaU) ↔
      tc - tf ≤ Real.sqrt (2 * post.M * (δcc - δ₀) / post.Pm) := by
  have hMf : 0 < fault.M := hMeq ▸ hM
  obtain ⟨hωc, hδc⟩ := fault.boltedFault_trajectory hMf hDf hk₁ hk₂ hφ.2.2.1 h0 tc
    ⟨hφ.1, le_rfl⟩
  rw [hMeq, hPm] at hωc hδc
  set τ := tc - tf with hτ
  have hτ0 : 0 < τ := by rw [hτ]; linarith
  -- the clearing angle versus the critical angle, in terms of the clearing time
  have hkey : φ tc 0 ≤ δcc ↔ τ ≤ Real.sqrt (2 * post.M * (δcc - δ₀) / post.Pm) := by
    rw [Real.le_sqrt' hτ0, hδc, le_div_iff₀ hPm0]
    constructor
    · intro h1
      have : post.Pm / (2 * post.M) * τ ^ 2 ≤ δcc - δ₀ := by linarith
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at this
      linarith
    · intro h1
      have : post.Pm / (2 * post.M) * τ ^ 2 ≤ δcc - δ₀ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; linarith
      linarith
  have hδc0 : δ₀ < φ tc 0 := by
    have : 0 < post.Pm / (2 * post.M) * τ ^ 2 := by positivity
    rw [hδc]; linarith
  -- strict monotonicity of `g` on `[δ₀, δ_u]`
  have hfPe : ∀ x, fault.Pe x = 0 := fun x => by simp [SwingParams.Pe, hk₁, hk₂]
  have hPmeq : fault.Pm = post.Pm := hPm
  have hmono : StrictMonoOn (eacG fault post δ₀ post.deltaU) (Icc δ₀ post.deltaU) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact fun z _ =>
        (hasDerivAt_eacG fault post hPmeq δ₀ post.deltaU z).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      rw [(hasDerivAt_eacG fault post hPmeq δ₀ post.deltaU z).deriv, hfPe, sub_zero]
      exact hpos z hz
  by_cases hle : φ tc 0 ≤ post.deltaU
  · rw [firstSwing_iff_areas hM hMeq hDf hDp hk h hφ h0 (by linarith) hle
      (by rw [hωc]; positivity), ← hkey]
    have hmem : φ tc 0 ∈ Icc δ₀ post.deltaU := ⟨hδc0.le, hle⟩
    rw [← sub_nonpos, ← hg]
    exact hmono.le_iff_le hmem hcc
  · push Not at hle
    constructor
    · intro hst
      exact absurd (hst tc (mem_Ici.mpr le_rfl)) (not_le.mpr hle)
    · intro hτle
      have := hkey.mpr hτle
      linarith [hcc.2]

/-- Classical lossless post-fault curve `P_e^post = P_max sin δ` (`k₁ = k₃ = 0`): the positivity
side condition holds for `δ₀ ≥ 0`, so the bolted-fault critical clearing time is exact.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem boltedFault_firstSwing_iff_classical {pre fault post : SwingParams}
    (hM : 0 < post.M) (hMeq : fault.M = post.M) (hPm : fault.Pm = post.Pm) (hPm0 : 0 < post.Pm)
    (hDf : fault.D = 0) (hDp : post.D = 0) (hk₁ : fault.k₁ = 0) (hk₂ : fault.k₂ = 0)
    (hpk₁ : post.k₁ = 0) (hpk₃ : post.k₃ = 0) (hk : 0 < post.k₂) (h : post.Pm < post.k₂)
    {φ : ℝ → State 2} {tf tc δ₀ δcc : ℝ}
    (hφ : tf ≤ tc ∧ IsIntegralCurveOn φ (fun _ x => pre.field x) (Iic tf) ∧
        IsIntegralCurveOn φ (fun _ x => fault.field x) (Icc tf tc) ∧
        IsIntegralCurveOn φ (fun _ x => post.field x) (Ici tc))
    (h0 : φ tf = PhasePlane.mk δ₀ 0) (htc : tf < tc)
    (hδ₀ : 0 ≤ δ₀) (hcc : δcc ∈ Icc δ₀ post.deltaU)
    (hg : eacG fault post δ₀ post.deltaU δcc = 0) :
    (∀ t ∈ Ici tc, φ t 0 ≤ post.deltaU) ↔
      tc - tf ≤ Real.sqrt (2 * post.M * (δcc - δ₀) / post.Pm) := by
  have habs : |post.Pm - post.k₁| < post.k₂ := by
    rw [hpk₁, sub_zero, abs_of_pos hPm0]; exact h
  have hu : post.deltaU < Real.pi := by
    have ha : 0 < Real.arcsin post.loadRatio := by
      rw [Real.arcsin_pos, SwingParams.loadRatio, hpk₁, sub_zero]; exact div_pos hPm0 hk
    simp only [SwingParams.deltaU, hpk₃, add_zero]
    linarith
  refine boltedFault_firstSwing_iff hM hMeq hPm hPm0 hDf hDp hk₁ hk₂ hk habs hφ h0 htc ?_ ?_
    hcc hg
  · have := Real.pi_pos
    linarith
  · intro x hx
    simp only [SwingParams.Pe, hpk₁, hpk₃, sub_zero, zero_add]
    exact mul_pos hk (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2]))

end powerlib.Synchronous
