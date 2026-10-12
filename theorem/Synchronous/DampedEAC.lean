import theorem.Synchronous.FaultSequence
import theorem.Dynamics.Basin

/-! # Equal-area criterion with damping: conservative sufficiency and the LaSalle basin of the
potential well

Model boundary.  The canonical swing model `SwingParams` (`theorem/Synchronous/Swing.lean`),
state `(δ, ω) : Dynamics.State 2`, `M δ̈ + D δ̇ = P_m − (k₁ + k₂ sin(δ − k₃))`, constant `P_m`,
generator OUT-positive convention, continuous time, no AVR / governor / PLL / limiter; for the
switched model the three-stage trajectories of `theorem/Synchronous/FaultSequence.lean`.
Damping is now allowed: `D ≥ 0` (sufficiency) or `D > 0` (convergence).  Statements are at
trajectory level and quantify over every solution.

Results.
* `energy_antitoneOn` (`D ≥ 0`): the energy `W = ½ M ω² + U(δ)` is non-increasing along every
  solution on any interval.
* `firstSwing_le_deltaU_of_damping` (`D ≥ 0`): the undamped equal-area condition
  `½ M ω_c² ≤ ∫_{δ_c}^{δ_u} (P_e − P_m)` still guarantees `δ(t) ≤ δ_u` for all `t ≥ t_c`;
  `faultTrajectory_firstSwing_of_areas`: for the switched model with damping in the fault and
  post-fault stages, `A_acc(δ₀, δ_c) ≤ A_dec(δ_c, δ_u)` (undamped areas) is sufficient — the
  undamped EAC is conservative.
* `regionOfAttraction_well` (`D > 0`, LaSalle on the potential well): every energy sublevel
  set `{δ_u − 2π < δ < δ_u, W ≤ c}` with `c` below both saddle levels `U(δ_u)`, `U(δ_u − 2π)`
  lies in the region of attraction of `(δ_s, 0)`.
* `tendsto_of_firstSwing_margin`, `faultTrajectory_tendsto_of_areas` (`D > 0`, `P_m ≥ k₁`):
  a strict equal-area margin at clearing implies convergence of the post-fault trajectory to
  `(δ_s, 0)`.

Correction.
* T-transient-stability §1.8 writes `A_dec^{D>0} = A_dec^{D=0} − ∫ D Δω² dt > A_dec^{D=0}`,
  which is self-contradictory (subtracting a positive quantity cannot increase the area).  The
  formal content of "the undamped EAC is conservative" is energy dissipation
  (`Ẇ = −D ω² ≤ 0`): the undamped area condition stays sufficient for every `D ≥ 0`, and with
  `D > 0` a strict margin gives convergence to `δ_s`.  The claim that the true critical clearing
  time is *strictly* larger than the EAC value is not formalized.

Family and connection conclusions.  None: energy dissipation along solutions, first-swing bounds,
region-of-attraction estimates (LaSalle on the well) and convergence of switched trajectories are
outside the sentence language of `Synchronous.Swing.family` (Rules §3a).  The seven former domain
theorems (`energy_antitoneOn`, `firstSwing_le_deltaU_of_damping`, `regionOfAttraction_well`,
`tendsto_of_firstSwing_margin`, `clearing_energy_le`, `faultTrajectory_firstSwing_of_areas`,
`faultTrajectory_tendsto_of_areas`) are private implementation evidence; the local stability of
`(δ_s, 0)` with `D > 0` is the connection conclusion `Swing.deltaS_mem_den_locallyExponentiallyStable`.
The well geometry (`wellWindow`, compact sublevels, the only equilibrium in the window) stays
public foundation.  LaSalle is the generic `Dynamics.regionOfAttraction_of_lasalle_sublevel`
(`theorem/Dynamics/Basin.lean`).

Source: work-sync theory/T-transient-stability.md §1.3, §1.5, §1.8, §2.2.
-/

noncomputable section
namespace powerlib.Synchronous
open Set Filter Topology intervalIntegral
open powerlib.Dynamics (State)

namespace SwingParams

variable (p : SwingParams)

/-- With `D ≥ 0` the energy is non-increasing along every solution on a convex time set.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem energy_antitoneOn (hM : p.M ≠ 0) (hD : 0 ≤ p.D) (δ₀ : ℝ)
    {φ : ℝ → State 2} {s : Set ℝ} (hs : Convex ℝ s)
    (hφ : IsIntegralCurveOn φ (fun _ x => p.field x) s) :
    AntitoneOn (fun t => p.energy δ₀ (φ t)) s := by
  have hV : Differentiable ℝ (p.energy δ₀) :=
    (p.contDiff_energy (k := 1) δ₀).differentiable (by norm_num)
  apply antitoneOn_of_hasDerivWithinAt_nonpos hs (hV.continuous.comp_continuousOn hφ.continuousOn)
    (f' := fun t => fderiv ℝ (p.energy δ₀) (φ t) (p.field (φ t)))
  · intro t ht
    exact (hV (φ t)).hasFDerivAt.comp_hasDerivWithinAt t
      ((hφ t (interior_subset ht)).mono interior_subset)
  · intro t _
    rw [p.energy_lie hM]
    nlinarith [sq_nonneg (φ t 1)]

/-- `U(δ − 2π) = U(δ) + 2π (P_m − k₁)`. -/
@[powerlib_foundation] theorem potential_sub_two_pi (δ₀ δ : ℝ) :
    p.potential δ₀ (δ - 2 * Real.pi) = p.potential δ₀ δ + 2 * Real.pi * (p.Pm - p.k₁) := by
  have : Real.cos (δ - 2 * Real.pi - p.k₃) = Real.cos (δ - p.k₃) := by
    rw [show δ - 2 * Real.pi - p.k₃ = (δ - p.k₃) - 2 * Real.pi by ring, Real.cos_sub_two_pi]
  simp only [potential, this]
  ring

/-- **The undamped equal-area condition is sufficient for every `D ≥ 0`.**  If the clearing
kinetic energy does not exceed `∫_{δ_c}^{δ_u} (P_e − P_m)`, the post-fault trajectory never goes
beyond `δ_u`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem firstSwing_le_deltaU_of_damping (hM : 0 < p.M) (hD : 0 ≤ p.D)
    (hk : 0 < p.k₂) (h : |p.Pm - p.k₁| < p.k₂) {φ : ℝ → State 2} {tc δc ωc : ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ x => p.field x) (Ici tc))
    (h0 : φ tc = mkState δc ωc) (hδc : δc ≤ p.deltaU)
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
  have hdec := p.energy_antitoneOn hM.ne' hD δc (convex_Ici tc) hφ (mem_Ici.mpr le_rfl) hts.1
    hts.1
  simp only [h0, energy, mkState_zero, mkState_one, potential_self, add_zero, hδs] at hdec
  rw [← potential_eq_integral] at hE
  have hω : φ ts 1 = 0 := by
    have : p.M / 2 * φ ts 1 ^ 2 ≤ 0 := by linarith
    have h2 : 0 < p.M / 2 := by positivity
    have := nonpos_of_mul_nonpos_right this h2 |>.antisymm (sq_nonneg _)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have hsteq : φ ts = mkState p.deltaU 0 := state_ext (by simpa using hδs) (by simpa using hω)
  have heqf := p.field_mkState_deltaU hM.ne' hk h.le
  have huniq := eqOn_of_isIntegralCurveOn_Icc (f := fun _ x => p.field x)
    (fun _ => p.lipschitzWith_field) (hφ.mono (Icc_subset_Ici_iff hts.2 |>.mpr hts.1))
    (p.isIntegralCurveOn_const heqf (Icc ts t)) (by simpa using hsteq)
  have := huniq ⟨hts.2, le_rfl⟩
  simp only at this
  rw [this] at hlt
  simp at hlt

/-! ## LaSalle on the potential well (`D > 0`) -/

/-- Open angular window of the potential well around `δ_s`: `δ_u − 2π < δ < δ_u`. -/
def wellWindow : Set (State 2) := {x | p.deltaU - 2 * Real.pi < x 0 ∧ x 0 < p.deltaU}

@[powerlib_foundation] theorem isOpen_wellWindow : IsOpen p.wellWindow :=
  (isOpen_lt continuous_const (coord_contDiff (k := 0) 0).continuous).inter
    (isOpen_lt (coord_contDiff (k := 0) 0).continuous continuous_const)

/-- The energy dominates the potential (`M > 0`). -/
@[powerlib_foundation] theorem potential_le_energy (hM : 0 < p.M) (δ₀ : ℝ) (x : State 2) :
    p.potential δ₀ (x 0) ≤ p.energy δ₀ x := by
  have : 0 ≤ p.M / 2 * x 1 ^ 2 := by positivity
  simp only [energy]; linarith

/-- Energy sublevel sets of the well below both saddle levels are compact. -/
@[powerlib_foundation] theorem isCompact_wellSublevel (hM : 0 < p.M) {c : ℝ}
    (hc1 : c < p.potential p.deltaS p.deltaU)
    (hc2 : c < p.potential p.deltaS (p.deltaU - 2 * Real.pi)) :
    IsCompact {x ∈ p.wellWindow | p.energy p.deltaS x ≤ c} := by
  set a := p.deltaU - 2 * Real.pi
  set b := p.deltaU
  have hab : a ≤ b := by have := Real.pi_pos; simp only [a, b]; linarith
  have hcU : Continuous (p.potential p.deltaS) := by unfold potential; fun_prop
  have hcV : Continuous (p.energy p.deltaS) := (p.contDiff_energy (k := 0) _).continuous
  have hc0 : Continuous fun x : State 2 => x 0 := (coord_contDiff (k := 0) 0).continuous
  have hEq : {x ∈ p.wellWindow | p.energy p.deltaS x ≤ c} =
      {x : State 2 | a ≤ x 0} ∩ {x | x 0 ≤ b} ∩ {x | p.energy p.deltaS x ≤ c} := by
    ext x
    simp only [wellWindow, mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1.le, h2.le⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hU := p.potential_le_energy hM p.deltaS x
      refine ⟨⟨lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_⟩, h3⟩
      · intro he; rw [← he] at hU; linarith
      · intro he; rw [he] at hU; linarith
  rw [hEq]
  apply Metric.isCompact_of_isClosed_isBounded
  · exact ((isClosed_le continuous_const hc0).inter (isClosed_le hc0 continuous_const)).inter
      (isClosed_le hcV continuous_const)
  · obtain ⟨δm, -, hδm⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hcU.continuousOn
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨|a| + |b| + 1 + 2 * (c - p.potential p.deltaS δm) / p.M, ?_⟩
    rintro x ⟨⟨h1, h2⟩, h3⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hU := hδm (show x 0 ∈ Icc a b from ⟨h1, h2⟩)
    simp only [mem_ofPred_eq] at hU h3 h1 h2
    have hkin : p.M / 2 * x 1 ^ 2 ≤ c - p.potential p.deltaS δm := by
      simp only [energy] at h3; linarith
    have hx1 : x 1 ^ 2 ≤ 2 * (c - p.potential p.deltaS δm) / p.M := by
      rw [le_div_iff₀ hM]; nlinarith
    have hx0 : |x 0| ≤ |a| + |b| := by
      rw [abs_le]; constructor <;>
        cases abs_cases a <;> cases abs_cases b <;> linarith [abs_nonneg a, abs_nonneg b]
    have hx1' : |x 1| ≤ 1 + x 1 ^ 2 := by
      rcases abs_cases (x 1) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nlinarith [sq_nonneg (x 1 - 1),
        sq_nonneg (x 1 + 1)]
    linarith [norm_state_le x]

/-- Inside the well window the only equilibrium is `(δ_s, 0)`. -/
@[powerlib_foundation] theorem eq_deltaS_of_field_eq_zero (hM : p.M ≠ 0) (hk : 0 < p.k₂)
    (h : |p.Pm - p.k₁| < p.k₂) {x : State 2} (hx : x ∈ p.wellWindow) (hf : p.field x = 0) :
    x = mkState p.deltaS 0 := by
  obtain ⟨h1, n, hn⟩ := (p.field_eq_zero_iff_branches hM hk h.le x).mp hf
  obtain ⟨hxa, hxb⟩ := hx
  have hs1 := p.deltaS_lt_deltaU hk h
  have hs2 := p.deltaU_sub_two_pi_lt_deltaS hk h
  have hπ := Real.pi_pos
  rcases hn with hn | hn
  · have hlo : -1 < (n : ℝ) := by
      by_contra hc; push Not at hc
      have : 2 * n * Real.pi ≤ -(2 * Real.pi) := by nlinarith
      linarith
    have hhi : (n : ℝ) < 1 := by
      by_contra hc; push Not at hc
      have : 2 * Real.pi ≤ 2 * n * Real.pi := by nlinarith
      linarith
    have hn0 : n = 0 := by
      have h1' : -1 < n := by exact_mod_cast hlo
      have h2' : n < 1 := by exact_mod_cast hhi
      omega
    rw [hn0] at hn
    simp only [Int.cast_zero, mul_zero, zero_mul, add_zero] at hn
    exact state_ext (by simpa using hn) (by simpa using h1)
  · exfalso
    have hlo : -1 < (n : ℝ) := by
      by_contra hc; push Not at hc
      have : 2 * n * Real.pi ≤ -(2 * Real.pi) := by nlinarith
      linarith
    have hhi : (n : ℝ) < 0 := by
      by_contra hc; push Not at hc
      have : 0 ≤ 2 * n * Real.pi := by positivity
      linarith
    have h1' : -1 < n := by exact_mod_cast hlo
    have h2' : n < 0 := by exact_mod_cast hhi
    omega

/-- **LaSalle on the potential well** (`M, D, k₂ > 0`, `|P_m − k₁| < k₂`): every energy
sublevel set of the well window below both saddle levels lies in the region of attraction of
`(δ_s, 0)`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem regionOfAttraction_well (hM : 0 < p.M) (hD : 0 < p.D)
    (hk : 0 < p.k₂) (h : |p.Pm - p.k₁| < p.k₂) {c : ℝ}
    (hc1 : c < p.potential p.deltaS p.deltaU)
    (hc2 : c < p.potential p.deltaS (p.deltaU - 2 * Real.pi)) :
    Dynamics.RegionOfAttraction p.field (mkState p.deltaS 0)
      {x ∈ p.wellWindow | p.energy p.deltaS x ≤ c} := by
  have hω : ∀ x : State 2, fderiv ℝ (p.energy p.deltaS) x (p.field x) = 0 → x 1 = 0 := by
    intro x hx
    rw [p.energy_lie hM.ne'] at hx
    have : p.D * x 1 ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hD.ne'
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
  refine Dynamics.regionOfAttraction_of_lasalle_sublevel p.isOpen_wellWindow p.contDiff_field
    (p.contDiff_energy _) (fun x _ => ?_) (p.isCompact_wellSublevel hM hc1 hc2) ?_
  · rw [p.energy_lie hM.ne']
    nlinarith [sq_nonneg (x 1)]
  · refine Dynamics.lasalle_condition_of_lieDeriv p.contDiff_field (h := fun x : State 2 => x 1)
      (coord_contDiff 1) ?_ ?_
    · intro x hx
      exact hω x hx.2
    · intro x hx hder
      have hx1 := hω x hx.2
      have hfd : fderiv ℝ (fun y : State 2 => y 1) x =
          (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : State 2 →L[ℝ] ℝ) :=
        (PiLp.proj 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) : State 2 →L[ℝ] ℝ).fderiv
      rw [hfd, PiLp.proj_apply, field_apply_one] at hder
      have hbal : p.Pe (x 0) = p.Pm := by
        simp only [accel, hx1, mul_zero, sub_zero, div_eq_zero_iff, hM.ne', or_false] at hder
        linarith
      exact p.eq_deltaS_of_field_eq_zero hM.ne' hk h hx.1.1
        ((p.field_eq_zero_iff hM.ne' x).mpr ⟨hx1, hbal⟩)

/-- **Strict equal-area margin ⇒ convergence** (`M, D, k₂ > 0`, `|P_m − k₁| < k₂`,
`P_m ≥ k₁`): a post-fault trajectory whose clearing state lies in the well window with
`½ M ω_c² < ∫_{δ_c}^{δ_u} (P_e − P_m)` converges to `(δ_s, 0)`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem tendsto_of_firstSwing_margin (hM : 0 < p.M) (hD : 0 < p.D)
    (hk : 0 < p.k₂) (h : |p.Pm - p.k₁| < p.k₂) (hPk : p.k₁ ≤ p.Pm) {φ : ℝ → State 2}
    {tc δc ωc : ℝ} (hφ : IsIntegralCurveOn φ (fun _ x => p.field x) (Ici tc))
    (h0 : φ tc = mkState δc ωc) (hwell : p.deltaU - 2 * Real.pi < δc) (hδc : δc < p.deltaU)
    (hE : p.M / 2 * ωc ^ 2 < ∫ s in δc..p.deltaU, (p.Pe s - p.Pm)) :
    Tendsto φ atTop (𝓝 (mkState p.deltaS 0)) := by
  set c := p.energy p.deltaS (mkState δc ωc)
  have hA : ∫ s in δc..p.deltaU, (p.Pe s - p.Pm) =
      p.potential p.deltaS p.deltaU - p.potential p.deltaS δc := by
    rw [← p.Adec_eq_potential_sub p.deltaS δc p.deltaU, Adec]
  have hc1 : c < p.potential p.deltaS p.deltaU := by
    simp only [c, energy, mkState_zero, mkState_one]; linarith
  have hc2 : c < p.potential p.deltaS (p.deltaU - 2 * Real.pi) := by
    rw [p.potential_sub_two_pi]
    have : 0 ≤ 2 * Real.pi * (p.Pm - p.k₁) := mul_nonneg (by positivity) (by linarith)
    linarith
  refine (p.regionOfAttraction_well hM hD hk h hc1 hc2).tendsto hφ ?_
  rw [h0]
  exact ⟨⟨by simpa using hwell, by simpa using hδc⟩, le_rfl⟩

end SwingParams

/-! ## The switched model with damping -/

/-- With damping `D ≥ 0` in the fault stage the clearing kinetic energy is at most the
(undamped) accelerating area: `½ M ω(t_c)² ≤ A_acc(δ₀, δ(t_c))`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem clearing_energy_le {fault : SwingParams} (hM : 0 < fault.M)
    (hD : 0 ≤ fault.D) {φ : ℝ → State 2} {tf tc δ₀ : ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ x => fault.field x) (Icc tf tc)) (htc : tf ≤ tc)
    (h0 : φ tf = mkState δ₀ 0) :
    fault.M / 2 * φ tc 1 ^ 2 ≤ fault.Aacc δ₀ (φ tc 0) := by
  have h := fault.energy_antitoneOn hM.ne' hD δ₀ (convex_Icc tf tc) hφ ⟨le_rfl, htc⟩
    ⟨htc, le_rfl⟩ htc
  simp only [h0, SwingParams.energy, mkState_zero, mkState_one,
    SwingParams.potential_self, add_zero] at h
  rw [SwingParams.Aacc_eq_neg_potential]
  norm_num at h
  linarith

/-- **The undamped EAC is conservative for the switched model**: with `D ≥ 0` in the fault and
post-fault stages (same inertia), `A_acc(δ₀, δ_c) ≤ A_dec(δ_c, δ_u)` (undamped areas) and
`δ_c ≤ δ_u` imply that the post-fault trajectory never exceeds `δ_u`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem faultTrajectory_firstSwing_of_areas {pre fault post : SwingParams}
    (hM : 0 < post.M) (hMeq : fault.M = post.M) (hDf : 0 ≤ fault.D) (hDp : 0 ≤ post.D)
    (hk : 0 < post.k₂) (h : |post.Pm - post.k₁| < post.k₂) {φ : ℝ → State 2} {tf tc δ₀ : ℝ}
    (hφ : IsFaultTrajectory pre fault post tf tc φ) (h0 : φ tf = mkState δ₀ 0)
    (hδc : φ tc 0 ≤ post.deltaU)
    (hA : fault.Aacc δ₀ (φ tc 0) ≤ post.Adec (φ tc 0) post.deltaU) :
    ∀ t ∈ Ici tc, φ t 0 ≤ post.deltaU := by
  have hE := clearing_energy_le (hMeq ▸ hM) hDf hφ.onFault hφ.le h0
  rw [hMeq] at hE
  exact post.firstSwing_le_deltaU_of_damping hM hDp hk h hφ.onPost (eq_mkState (φ tc)) hδc
    (by rw [← SwingParams.Adec]; linarith)

/-- **Strict area margin ⇒ asymptotic recovery** for the switched model: with `D ≥ 0` in the
fault stage, `D > 0` post-fault, `P_m ≥ k₁`, a clearing angle inside the well window and
`A_acc(δ₀, δ_c) < A_dec(δ_c, δ_u)`, the trajectory converges to the post-fault stable
equilibrium `(δ_s, 0)`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem faultTrajectory_tendsto_of_areas {pre fault post : SwingParams}
    (hM : 0 < post.M) (hMeq : fault.M = post.M) (hDf : 0 ≤ fault.D) (hDp : 0 < post.D)
    (hk : 0 < post.k₂) (h : |post.Pm - post.k₁| < post.k₂) (hPk : post.k₁ ≤ post.Pm)
    {φ : ℝ → State 2} {tf tc δ₀ : ℝ}
    (hφ : IsFaultTrajectory pre fault post tf tc φ) (h0 : φ tf = mkState δ₀ 0)
    (hwell : post.deltaU - 2 * Real.pi < φ tc 0) (hδc : φ tc 0 < post.deltaU)
    (hA : fault.Aacc δ₀ (φ tc 0) < post.Adec (φ tc 0) post.deltaU) :
    Tendsto φ atTop (𝓝 (mkState post.deltaS 0)) := by
  have hE := clearing_energy_le (hMeq ▸ hM) hDf hφ.onFault hφ.le h0
  rw [hMeq] at hE
  exact post.tendsto_of_firstSwing_margin hM hDp hk h hPk hφ.onPost (eq_mkState (φ tc)) hwell
    hδc (by rw [← SwingParams.Adec]; linarith)

end powerlib.Synchronous
