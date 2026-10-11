import theorem.Synchronous.EqualArea

/-! # The three-stage fault sequence of the SMIB swing model

Model boundary.
* Three instances of the canonical swing model `SwingParams` (`theorem/Synchronous/Swing.lean`):
  the pre-fault, during-fault and post-fault configurations of the same machine.  State
  `(δ, ω) : Dynamics.State 2` (rotor angle relative to the infinite bus, frequency deviation in
  rad/s), `M δ̈ + D δ̇ = P_m − (k₁ + k₂ sin(δ − k₃))`, constant `P_m`, generator OUT-positive
  (Kundur) convention, continuous time; no AVR / governor / PLL / limiter / protection delay.
* Switched dynamics: the fault occurs at `t_f` and is cleared at `t_c ≥ t_f`.  A three-stage
  trajectory (`IsFaultTrajectory`) is one function `φ : ℝ → State 2` — so the state is
  continuous at the switching instants (trajectory gluing) — that solves the pre-fault field on
  `(−∞, t_f]`, the during-fault field on `[t_f, t_c]` and the post-fault field on `[t_c, ∞)`,
  with one-sided derivatives at the switching instants.
* Conclusions are at trajectory level and quantify over every three-stage trajectory.

Results.
* `exists_faultTrajectory`, `faultTrajectory_unique`: from a pre-fault equilibrium the switched
  model has a three-stage trajectory resting at the equilibrium before the fault, and every
  such trajectory agrees with it after the fault (global Lipschitz bound of each stage).
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

Corrections (beyond `theorem/Synchronous/EqualArea.lean`).
* T-transient-stability §1.5–§1.6 present `t_cc` and the equal-area criterion for the switched
  system without stating the gluing of the three stages; here the trajectory notion is defined
  and the criterion is proved for every glued trajectory.  The boundary case
  `A_acc = A_dec` belongs to the stable ("does not cross `δ_u`") side.

Source: work-sync theory/T-transient-stability.md §1.1, §1.4–§1.6.
-/

noncomputable section
namespace powerlib.Synchronous
open Set Filter Topology intervalIntegral
open powerlib.Dynamics (State)

/-- Three-stage (pre-fault / during-fault / post-fault) trajectory with switching instants
`t_f ≤ t_c`; the stages are glued by continuity of the state (one function `φ`). -/
structure IsFaultTrajectory (pre fault post : SwingParams) (tf tc : ℝ) (φ : ℝ → State 2) :
    Prop where
  le : tf ≤ tc
  onPre : Dynamics.IsIntegralCurveOn φ (fun _ x => pre.field x) (Iic tf)
  onFault : Dynamics.IsIntegralCurveOn φ (fun _ x => fault.field x) (Icc tf tc)
  onPost : Dynamics.IsIntegralCurveOn φ (fun _ x => post.field x) (Ici tc)

/-- Existence for the switched model: from a pre-fault equilibrium `x₀` there is a three-stage
trajectory that rests at `x₀` up to the fault instant. -/
@[powerlib_domain] theorem exists_faultTrajectory (pre fault post : SwingParams) {x₀ : State 2}
    (hx₀ : pre.field x₀ = 0) {tf tc : ℝ} (htc : tf ≤ tc) :
    ∃ φ, IsFaultTrajectory pre fault post tf tc φ ∧ ∀ t ∈ Iic tf, φ t = x₀ := by
  obtain ⟨φ1, h1₀, h1⟩ := fault.forwardComplete tf x₀
  obtain ⟨φ2, h2₀, h2⟩ := post.forwardComplete tc (φ1 tc)
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

/-- Uniqueness for the switched model: two three-stage trajectories with the same state at the
fault instant agree at every later time. -/
@[powerlib_domain] theorem faultTrajectory_unique {pre fault post : SwingParams} {tf tc : ℝ}
    {φ ψ : ℝ → State 2} (hφ : IsFaultTrajectory pre fault post tf tc φ)
    (hψ : IsFaultTrajectory pre fault post tf tc ψ) (h0 : φ tf = ψ tf) :
    ∀ t ∈ Ici tf, φ t = ψ t := by
  have hfault : EqOn φ ψ (Icc tf tc) :=
    Dynamics.eqOn_of_isIntegralCurveOn_Icc (fun _ => fault.lipschitzWith_field) hφ.onFault
      hψ.onFault h0
  have hc : φ tc = ψ tc := hfault ⟨hφ.le, le_rfl⟩
  intro t ht
  rcases le_total t tc with h | h
  · exact hfault ⟨ht, h⟩
  · exact Dynamics.eqOn_of_isIntegralCurveOn_Icc (fun _ => post.lipschitzWith_field)
      (hφ.onPost.mono Icc_subset_Ici_self) (hψ.onPost.mono Icc_subset_Ici_self) hc ⟨h, le_rfl⟩

namespace SwingParams

variable (p : SwingParams)

/-- Energy conservation (`D = 0`) along a solution on a compact time interval. -/
@[powerlib_domain] theorem energy_conserved_Icc (hM : p.M ≠ 0) (hD : p.D = 0) (δ₀ : ℝ)
    {φ : ℝ → State 2} {a b : ℝ}
    (hφ : Dynamics.IsIntegralCurveOn φ (fun _ x => p.field x) (Icc a b)) :
    ∀ t ∈ Icc a b, p.energy δ₀ (φ t) = p.energy δ₀ (φ a) := by
  have hdiff : Differentiable ℝ (p.energy δ₀) :=
    (p.contDiff_energy (k := 1) δ₀).differentiable (by norm_num)
  apply constant_of_has_deriv_right_zero (f := fun t => p.energy δ₀ (φ t))
    (hdiff.continuous.comp_continuousOn hφ.continuousOn)
  intro x hx
  have hd := Dynamics.hasDerivWithinAt_Ici_of_isIntegralCurveOn hφ x hx
  have h := (hdiff (φ x)).hasFDerivAt.comp_hasDerivWithinAt x hd
  rw [p.energy_lie hM, hD, neg_zero, zero_mul] at h
  exact h

/-- The accelerating area is minus the potential: `A_acc(δ₀, x) = −U_{δ₀}(x)`. -/
@[powerlib_foundation] theorem Aacc_eq_neg_potential (δ₀ x : ℝ) :
    p.Aacc δ₀ x = -p.potential δ₀ x := by
  rw [Aacc_eq, potential]
  ring

/-- `A_dec(x, δ_max) = U_{δ₀}(δ_max) − U_{δ₀}(x)` for any reference angle `δ₀`. -/
@[powerlib_foundation] theorem Adec_eq_potential_sub (δ₀ x δmax : ℝ) :
    p.Adec x δmax = p.potential δ₀ δmax - p.potential δ₀ x := by
  rw [Adec_eq, potential, potential]
  ring

end SwingParams

/-- Clearing energy: with an undamped during-fault stage started at `(δ₀, 0)`, the kinetic
energy at clearing equals the accelerating area, `½ M ω(t_c)² = A_acc(δ₀, δ(t_c))`. -/
@[powerlib_domain] theorem clearing_energy {fault : SwingParams} (hM : fault.M ≠ 0)
    (hD : fault.D = 0) {φ : ℝ → State 2} {tf tc δ₀ : ℝ}
    (hφ : Dynamics.IsIntegralCurveOn φ (fun _ x => fault.field x) (Icc tf tc)) (htc : tf ≤ tc)
    (h0 : φ tf = mkState δ₀ 0) :
    fault.M / 2 * φ tc 1 ^ 2 = fault.Aacc δ₀ (φ tc 0) := by
  have h := fault.energy_conserved_Icc hM hD δ₀ hφ tc ⟨htc, le_rfl⟩
  rw [h0] at h
  simp only [SwingParams.energy, mkState_zero, mkState_one, SwingParams.potential_self,
    add_zero] at h
  rw [SwingParams.Aacc_eq_neg_potential]
  norm_num at h
  linarith

/-- **Equal-area criterion for the switched model** (`D = 0` in the fault and post-fault stages,
same inertia): if the clearing state lies in the post-fault potential well
(`δ_u − 2π < δ_c ≤ δ_u`) and moves forward (`ω_c > 0`), the post-fault trajectory never exceeds
`δ_u` iff `A_acc(δ₀, δ_c) ≤ A_dec(δ_c, δ_u)`. -/
@[powerlib_domain] theorem firstSwing_iff_areas {pre fault post : SwingParams}
    (hM : 0 < post.M) (hMeq : fault.M = post.M) (hDf : fault.D = 0) (hDp : post.D = 0)
    (hk : 0 < post.k₂) (h : |post.Pm - post.k₁| < post.k₂) {φ : ℝ → State 2} {tf tc δ₀ : ℝ}
    (hφ : IsFaultTrajectory pre fault post tf tc φ) (h0 : φ tf = mkState δ₀ 0)
    (hwell : post.deltaU - 2 * Real.pi < φ tc 0) (hδc : φ tc 0 ≤ post.deltaU)
    (hω : 0 < φ tc 1) :
    (∀ t ∈ Ici tc, φ t 0 ≤ post.deltaU) ↔
      fault.Aacc δ₀ (φ tc 0) ≤ post.Adec (φ tc 0) post.deltaU := by
  have hE := clearing_energy (hMeq ▸ hM.ne') hDf hφ.onFault hφ.le h0
  rw [hMeq] at hE
  rw [← hE, SwingParams.Adec]
  exact post.firstSwing_iff hM hDp hk h hφ.onPost (eq_mkState (φ tc)) hwell hδc hω

/-- **Critical clearing time of a bolted fault** (`P_e^f ≡ 0`, `D = 0`, `P_m > 0`, same `M` and
`P_m` in both stages).  Let `δ_cc ∈ [δ₀, δ_u]` be a zero of `g = A_acc − A_dec`, and let the
post-fault curve be positive on `(δ₀, δ_u)`.  Then the first swing stays below `δ_u` iff the
fault is cleared within `t_c − t_f ≤ √(2M(δ_cc − δ₀)/P_m)`. -/
@[powerlib_domain] theorem boltedFault_firstSwing_iff {pre fault post : SwingParams}
    (hM : 0 < post.M) (hMeq : fault.M = post.M) (hPm : fault.Pm = post.Pm) (hPm0 : 0 < post.Pm)
    (hDf : fault.D = 0) (hDp : post.D = 0) (hk₁ : fault.k₁ = 0) (hk₂ : fault.k₂ = 0)
    (hk : 0 < post.k₂) (h : |post.Pm - post.k₁| < post.k₂) {φ : ℝ → State 2} {tf tc δ₀ δcc : ℝ}
    (hφ : IsFaultTrajectory pre fault post tf tc φ) (h0 : φ tf = mkState δ₀ 0) (htc : tf < tc)
    (hwell : post.deltaU - 2 * Real.pi < δ₀) (hpos : ∀ x ∈ Ioo δ₀ post.deltaU, 0 < post.Pe x)
    (hcc : δcc ∈ Icc δ₀ post.deltaU) (hg : eacG fault post δ₀ post.deltaU δcc = 0) :
    (∀ t ∈ Ici tc, φ t 0 ≤ post.deltaU) ↔
      tc - tf ≤ Real.sqrt (2 * post.M * (δcc - δ₀) / post.Pm) := by
  have hMf : 0 < fault.M := hMeq ▸ hM
  obtain ⟨hωc, hδc⟩ := fault.boltedFault_trajectory hMf hDf hk₁ hk₂ hφ.onFault h0 tc
    ⟨hφ.le, le_rfl⟩
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
side condition holds for `δ₀ ≥ 0`, so the bolted-fault critical clearing time is exact. -/
@[powerlib_domain] theorem boltedFault_firstSwing_iff_classical {pre fault post : SwingParams}
    (hM : 0 < post.M) (hMeq : fault.M = post.M) (hPm : fault.Pm = post.Pm) (hPm0 : 0 < post.Pm)
    (hDf : fault.D = 0) (hDp : post.D = 0) (hk₁ : fault.k₁ = 0) (hk₂ : fault.k₂ = 0)
    (hpk₁ : post.k₁ = 0) (hpk₃ : post.k₃ = 0) (hk : 0 < post.k₂) (h : post.Pm < post.k₂)
    {φ : ℝ → State 2} {tf tc δ₀ δcc : ℝ}
    (hφ : IsFaultTrajectory pre fault post tf tc φ) (h0 : φ tf = mkState δ₀ 0) (htc : tf < tc)
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
