import theorem.Synchronous.FaultSequence
import theorem.Dynamics.LaSalle.Basin
import theorem.SpecialFunctions.Elementary

/-! # Equal-area criterion with damping: conservative sufficiency and the potential-well basin

Trajectory-level equal-area results for the damped single-machine infinite-bus swing model: the
undamped area condition stays sufficient for every `D ≥ 0`, a strict margin gives convergence for
`D > 0`, and damping strictly delays the critical clearing time of a bolted fault.

Model boundary.
* The canonical swing model `SwingParams` (`theorem/Synchronous/Swing.lean`), state
  `(δ, ω) : Dynamics.State 2`, `M δ̈ + D δ̇ = P_m − (k₁ + k₂ sin(δ − k₃))`, constant `P_m`,
  generator OUT-positive convention, continuous time, no AVR / governor / PLL / limiter; for the
  switched model the three-stage trajectories of `theorem/Synchronous/FaultSequence.lean`.
* Damping is allowed: `D ≥ 0` (sufficiency) or `D > 0` (convergence).  Statements are at
  trajectory level and quantify over every solution.  A three-stage trajectory is written out as
  in `FaultSequence.lean`: `tf ≤ tc ∧ IsIntegralCurveOn φ (fun _ x => pre.field x) (Iic tf) ∧
  IsIntegralCurveOn φ (fun _ x => fault.field x) (Icc tf tc) ∧
  IsIntegralCurveOn φ (fun _ x => post.field x) (Ici tc)`.
* "`S` lies in the region of attraction of `x_eq`" is written out as in
  `theorem/Dynamics/LaSalle/Basin.lean`: from every initial state in `S` a forward solution on
  `[0, ∞)` exists and every forward solution from it converges to `x_eq`.

Source: work-sync `theory/T-transient-stability.md` §1.3, §1.5, §1.6, §1.8, §2.2.

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
* **Damping strictly delays the critical clearing time** (bolted fault `P_e^f ≡ 0`, same `M`,
  `P_m` in both stages, `D > 0` during the fault).  `dampedBolted_trajectory`: explicit damped
  during-fault trajectory `ω = (P_m/D)(1 − e^{−Dτ/M})`,
  `δ = δ₀ + (P_m/D)(τ − (M/D)(1 − e^{−Dτ/M}))`, `τ = t − t_f`, which stays strictly below the
  undamped `δ₀ + P_m τ²/(2M)` for `τ > 0` (`SpecialFunctions.exp_neg_lt_quadratic`:
  `e^{−u} < 1 − u + u²/2`).
  `boltedFault_damped_clearingAngle`: with `δ_cc ∈ (δ₀, δ_u]` the undamped critical clearing
  angle (zero of `g = A_acc − A_dec`, post-fault curve positive on `(δ₀, δ_u)`) there is `ε > 0`
  such that every clearing time `t_c − t_f ≤ t_cc^EAC + ε`, `t_cc^EAC = √(2M(δ_cc − δ₀)/P_m)`,
  gives a clearing angle in `[δ₀, δ_cc)` and a strict undamped area margin;
  `boltedFault_damped_firstSwing` (`D_post ≥ 0`): all those clearing times keep the first swing
  below `δ_u`; `boltedFault_damped_tendsto` (`D_post > 0`, `P_m ≥ k₁`, `δ_u − 2π < δ₀`): all of
  them give convergence to `(δ_s, 0)`.  Since without damping the first swing stays below `δ_u`
  exactly for `t_c − t_f ≤ t_cc^EAC` (`boltedFault_firstSwing_iff`, `FaultSequence.lean`), the
  true (damped) critical clearing time is at least `t_cc^EAC + ε`, strictly larger than the EAC
  value.
* Public foundation: the well geometry (`wellWindow`, `isOpen_wellWindow`,
  `isCompact_wellSublevel`, `potential_le_energy`, `eq_deltaS_of_field_eq_zero`: the only
  equilibrium in the window).

Family and connection conclusions.
* None: energy dissipation along solutions, first-swing bounds, region-of-attraction estimates
  (LaSalle on the well) and convergence of switched trajectories are outside the sentence
  language of `Synchronous.Swing.family` (Rules §3a).  The trajectory theorems
  (`energy_antitoneOn`, `firstSwing_le_deltaU_of_damping`, `regionOfAttraction_well`,
  `tendsto_of_firstSwing_margin`, `clearing_energy_le`, `faultTrajectory_firstSwing_of_areas`,
  `faultTrajectory_tendsto_of_areas`) and the bolted-fault clearing-time results
  (`dampedBolted_trajectory`, `boltedFault_damped_clearingAngle`, `boltedFault_damped_firstSwing`,
  `boltedFault_damped_tendsto`) are private implementation evidence.
* The local stability of `(δ_s, 0)` with `D > 0` is the connection conclusion
  `Swing.deltaS_mem_den_locallyExponentiallyStable`.
* The elementary bounds `SpecialFunctions.exp_neg_lt_quadratic`,
  `SpecialFunctions.exp_neg_le_quadratic` are in `theorem/SpecialFunctions/Elementary.lean`;
  LaSalle is the generic `Dynamics.LaSalle.regionOfAttraction_of_lasalle_sublevel`
  (`theorem/Dynamics/LaSalle/Basin.lean`).

Correction.
* T-transient-stability §1.8 writes `A_dec^{D>0} = A_dec^{D=0} − ∫ D Δω² dt > A_dec^{D=0}`,
  which is self-contradictory (subtracting a positive quantity cannot increase the area).  The
  formal content of "the undamped EAC is conservative" is energy dissipation
  (`Ẇ = −D ω² ≤ 0`): the undamped area condition stays sufficient for every `D ≥ 0`, and with
  `D > 0` a strict margin gives convergence to `δ_s`.  The claim `t_cc^真 > t_cc^EAC` is proved
  for the bolted fault (`boltedFault_damped_firstSwing`, `boltedFault_damped_tendsto`, with a
  uniform `ε > 0`); for a general during-fault curve (no closed-form undamped trajectory) it is
  not formalized.
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
  have hdec := p.energy_antitoneOn hM.ne' hD δc (convex_Ici tc) hφ (mem_Ici.mpr le_rfl) hts.1
    hts.1
  simp only [h0, energy, PhasePlane.mk_apply_zero, PhasePlane.mk_apply_one, potential_self,
    add_zero, hδs] at hdec
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

/-! ## LaSalle on the potential well (`D > 0`) -/

/-- Open angular window of the potential well around `δ_s`: `δ_u − 2π < δ < δ_u`. -/
def wellWindow : Set (State 2) := {x | p.deltaU - 2 * Real.pi < x 0 ∧ x 0 < p.deltaU}

@[powerlib_foundation] theorem isOpen_wellWindow : IsOpen p.wellWindow :=
  (isOpen_lt continuous_const (Dynamics.contDiff_coord (k := 0) 0).continuous).inter
    (isOpen_lt (Dynamics.contDiff_coord (k := 0) 0).continuous continuous_const)

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
  have hc0 : Continuous fun x : State 2 => x 0 := (Dynamics.contDiff_coord (k := 0) 0).continuous
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
    linarith [Dynamics.norm_le_abs_add_abs_two x]

/-- Inside the well window the only equilibrium is `(δ_s, 0)`. -/
@[powerlib_foundation] theorem eq_deltaS_of_field_eq_zero (hM : p.M ≠ 0) (hk : 0 < p.k₂)
    (h : |p.Pm - p.k₁| < p.k₂) {x : State 2} (hx : x ∈ p.wellWindow) (hf : p.field x = 0) :
    x = PhasePlane.mk p.deltaS 0 := by
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
    exact PhasePlane.ext_iff'.2 ⟨by simpa using hn, by simpa using h1⟩
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
    ∀ x₀ ∈ {x ∈ p.wellWindow | p.energy p.deltaS x ≤ c},
      (∃ φ : ℝ → State 2, φ 0 = x₀ ∧ IsIntegralCurveOn φ (fun _ x => p.field x) (Ici 0)) ∧
      ∀ φ : ℝ → State 2, φ 0 = x₀ → IsIntegralCurveOn φ (fun _ x => p.field x) (Ici 0) →
        Tendsto φ atTop (𝓝 (PhasePlane.mk p.deltaS 0)) := by
  have hω : ∀ x : State 2, fderiv ℝ (p.energy p.deltaS) x (p.field x) = 0 → x 1 = 0 := by
    intro x hx
    rw [p.energy_lie hM.ne'] at hx
    have : p.D * x 1 ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hD.ne'
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
  refine Dynamics.LaSalle.regionOfAttraction_of_lasalle_sublevel p.isOpen_wellWindow
    p.contDiff_field (p.contDiff_energy _) (fun x _ => ?_) (p.isCompact_wellSublevel hM hc1 hc2) ?_
  · rw [p.energy_lie hM.ne']
    nlinarith [sq_nonneg (x 1)]
  · refine Dynamics.LaSalle.lasalle_condition_of_lieDeriv p.contDiff_field
      (h := fun x : State 2 => x 1) (Dynamics.contDiff_coord 1) ?_ ?_
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
    (h0 : φ tc = PhasePlane.mk δc ωc) (hwell : p.deltaU - 2 * Real.pi < δc) (hδc : δc < p.deltaU)
    (hE : p.M / 2 * ωc ^ 2 < ∫ s in δc..p.deltaU, (p.Pe s - p.Pm)) :
    Tendsto φ atTop (𝓝 (PhasePlane.mk p.deltaS 0)) := by
  set c := p.energy p.deltaS (PhasePlane.mk δc ωc)
  have hA : ∫ s in δc..p.deltaU, (p.Pe s - p.Pm) =
      p.potential p.deltaS p.deltaU - p.potential p.deltaS δc := by
    rw [← p.Adec_eq_potential_sub p.deltaS δc p.deltaU, Adec]
  have hc1 : c < p.potential p.deltaS p.deltaU := by
    simp only [c, energy, PhasePlane.mk_apply_zero, PhasePlane.mk_apply_one]; linarith
  have hc2 : c < p.potential p.deltaS (p.deltaU - 2 * Real.pi) := by
    rw [p.potential_sub_two_pi]
    have : 0 ≤ 2 * Real.pi * (p.Pm - p.k₁) := mul_nonneg (by positivity) (by linarith)
    linarith
  refine Dynamics.LaSalle.RegionOfAttraction.tendsto (p.regionOfAttraction_well hM hD hk h hc1 hc2)
    hφ ?_
  rw [h0]
  exact ⟨⟨by simpa using hwell, by simpa using hδc⟩, le_rfl⟩

/-- Damped bolted fault (`P_e^f ≡ 0`, `D > 0`): from `(δ₀, 0)` at `t_f`,
`ω = (P_m/D)(1 − e^{−D(t−t_f)/M})`, `δ = δ₀ + (P_m/D)((t − t_f) − (M/D)(1 − e^{−D(t−t_f)/M}))`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem dampedBolted_trajectory (hM : 0 < p.M) (hD : 0 < p.D)
    (hk₁ : p.k₁ = 0) (hk₂ : p.k₂ = 0) {φ : ℝ → State 2} {tf T δ₀ : ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ x => p.field x) (Icc tf T))
    (h0 : φ tf = PhasePlane.mk δ₀ 0) :
    ∀ t ∈ Icc tf T, φ t 1 = p.Pm / p.D * (1 - Real.exp (-(p.D / p.M) * (t - tf))) ∧
      φ t 0 = δ₀ + p.Pm / p.D *
        ((t - tf) - p.M / p.D * (1 - Real.exp (-(p.D / p.M) * (t - tf)))) := by
  have hacc : ∀ x : State 2, p.field x 1 = (p.Pm - p.D * x 1) / p.M := by
    intro x; simp [accel, Pe, hk₁, hk₂]
  have hd := hasDerivWithinAt_Ici_of_isIntegralCurveOn hφ
  have hcont := hφ.continuousOn
  have hEd : ∀ x, HasDerivAt (fun t => Real.exp (p.D / p.M * (t - tf)))
      (p.D / p.M * Real.exp (p.D / p.M * (x - tf))) x :=
    fun x => ((((hasDerivAt_id' x).sub_const tf).const_mul (p.D / p.M)).exp).congr_deriv
      (by ring)
  -- `(ω − W) e^{a(t−t_f)}` is constant
  have h1 : ∀ t ∈ Icc tf T, φ t 1 * Real.exp (p.D / p.M * (t - tf)) -
      p.Pm / p.D * (Real.exp (p.D / p.M * (t - tf)) - 1) =
      φ tf 1 * Real.exp (p.D / p.M * (tf - tf)) -
        p.Pm / p.D * (Real.exp (p.D / p.M * (tf - tf)) - 1) := by
    apply constant_of_has_deriv_right_zero
    · exact ((((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : State 2 →L[ℝ] ℝ).continuous).comp_continuousOn
        hcont).mul (by fun_prop)).sub (by fun_prop)
    · intro x hx
      have hω := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 :
        State 2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt x (hd x hx)
      have := (hω.mul (hEd x).hasDerivWithinAt).sub
        (((hEd x).sub_const 1).const_mul (p.Pm / p.D)).hasDerivWithinAt
      convert this using 1
      · funext y; simp [Function.comp_def]
      · simp only [Function.comp_apply, PiLp.proj_apply, hacc]
        field_simp
        ring
  have hω : ∀ t ∈ Icc tf T, φ t 1 = p.Pm / p.D * (1 - Real.exp (-(p.D / p.M) * (t - tf))) := by
    intro t ht
    have h := h1 t ht
    simp only [sub_self, mul_zero, Real.exp_zero, h0, PhasePlane.mk_apply_one, zero_mul] at h
    have hE : Real.exp (p.D / p.M * (t - tf)) ≠ 0 := (Real.exp_pos _).ne'
    have hinv : Real.exp (-(p.D / p.M) * (t - tf)) = (Real.exp (p.D / p.M * (t - tf)))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    have key : φ t 1 * Real.exp (p.D / p.M * (t - tf)) =
        p.Pm / p.D * (Real.exp (p.D / p.M * (t - tf)) - 1) := by
      linear_combination h
    rw [hinv]
    calc φ t 1 = φ t 1 * Real.exp (p.D / p.M * (t - tf)) / Real.exp (p.D / p.M * (t - tf)) := by
          field_simp
      _ = p.Pm / p.D * (Real.exp (p.D / p.M * (t - tf)) - 1) / Real.exp (p.D / p.M * (t - tf)) := by
          rw [key]
      _ = p.Pm / p.D * (1 - (Real.exp (p.D / p.M * (t - tf)))⁻¹) := by field_simp
  have h2 : ∀ t ∈ Icc tf T, φ t 0 - (δ₀ + p.Pm / p.D * ((t - tf) - p.M / p.D *
      (1 - Real.exp (-(p.D / p.M) * (t - tf))))) = φ tf 0 - (δ₀ + p.Pm / p.D * ((tf - tf) -
        p.M / p.D * (1 - Real.exp (-(p.D / p.M) * (tf - tf))))) := by
    apply constant_of_has_deriv_right_zero
    · exact (((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : State 2 →L[ℝ] ℝ).continuous).comp_continuousOn
        hcont).sub (by fun_prop)
    · intro x hx
      have hδ := (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 :
        State 2 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt x (hd x hx)
      have hE2 : HasDerivAt (fun t => Real.exp (-(p.D / p.M) * (t - tf)))
          (-(p.D / p.M) * Real.exp (-(p.D / p.M) * (x - tf))) x :=
        ((((hasDerivAt_id' x).sub_const tf).const_mul (-(p.D / p.M))).exp).congr_deriv
          (by ring)
      have hW : HasDerivAt (fun t => δ₀ + p.Pm / p.D * ((t - tf) - p.M / p.D *
          (1 - Real.exp (-(p.D / p.M) * (t - tf)))))
          (p.Pm / p.D * (1 - p.M / p.D *
            (-(-(p.D / p.M) * Real.exp (-(p.D / p.M) * (x - tf)))))) x :=
        ((((hasDerivAt_id' x).sub_const tf).sub ((hE2.const_sub 1).const_mul (p.M / p.D))).const_mul
          (p.Pm / p.D)).const_add δ₀
      have := hδ.sub hW.hasDerivWithinAt
      convert this using 1
      · funext y; simp [Function.comp_def]
      · simp only [PiLp.proj_apply, field_apply_zero]
        rw [hω x ⟨hx.1, hx.2.le⟩]
        field_simp
        ring
  intro t ht
  refine ⟨hω t ht, ?_⟩
  have := h2 t ht
  simp only [sub_self, mul_zero, Real.exp_zero, h0, PhasePlane.mk_apply_zero] at this
  linarith

end SwingParams

/-! ## The switched model with damping -/

/-- With damping `D ≥ 0` in the fault stage the clearing kinetic energy is at most the
(undamped) accelerating area: `½ M ω(t_c)² ≤ A_acc(δ₀, δ(t_c))`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem clearing_energy_le {fault : SwingParams} (hM : 0 < fault.M)
    (hD : 0 ≤ fault.D) {φ : ℝ → State 2} {tf tc δ₀ : ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ x => fault.field x) (Icc tf tc)) (htc : tf ≤ tc)
    (h0 : φ tf = PhasePlane.mk δ₀ 0) :
    fault.M / 2 * φ tc 1 ^ 2 ≤ fault.Aacc δ₀ (φ tc 0) := by
  have h := fault.energy_antitoneOn hM.ne' hD δ₀ (convex_Icc tf tc) hφ ⟨le_rfl, htc⟩
    ⟨htc, le_rfl⟩ htc
  simp only [h0, SwingParams.energy, PhasePlane.mk_apply_zero, PhasePlane.mk_apply_one,
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
    (hφ : tf ≤ tc ∧ IsIntegralCurveOn φ (fun _ x => pre.field x) (Iic tf) ∧
      IsIntegralCurveOn φ (fun _ x => fault.field x) (Icc tf tc) ∧
      IsIntegralCurveOn φ (fun _ x => post.field x) (Ici tc))
    (h0 : φ tf = PhasePlane.mk δ₀ 0)
    (hδc : φ tc 0 ≤ post.deltaU)
    (hA : fault.Aacc δ₀ (φ tc 0) ≤ post.Adec (φ tc 0) post.deltaU) :
    ∀ t ∈ Ici tc, φ t 0 ≤ post.deltaU := by
  have hE := clearing_energy_le (hMeq ▸ hM) hDf hφ.2.2.1 hφ.1 h0
  rw [hMeq] at hE
  exact post.firstSwing_le_deltaU_of_damping hM hDp hk h hφ.2.2.2
    (PhasePlane.mk_coords (φ tc)).symm hδc (by rw [← SwingParams.Adec]; linarith)

/-- **Strict area margin ⇒ asymptotic recovery** for the switched model: with `D ≥ 0` in the
fault stage, `D > 0` post-fault, `P_m ≥ k₁`, a clearing angle inside the well window and
`A_acc(δ₀, δ_c) < A_dec(δ_c, δ_u)`, the trajectory converges to the post-fault stable
equilibrium `(δ_s, 0)`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem faultTrajectory_tendsto_of_areas {pre fault post : SwingParams}
    (hM : 0 < post.M) (hMeq : fault.M = post.M) (hDf : 0 ≤ fault.D) (hDp : 0 < post.D)
    (hk : 0 < post.k₂) (h : |post.Pm - post.k₁| < post.k₂) (hPk : post.k₁ ≤ post.Pm)
    {φ : ℝ → State 2} {tf tc δ₀ : ℝ}
    (hφ : tf ≤ tc ∧ IsIntegralCurveOn φ (fun _ x => pre.field x) (Iic tf) ∧
      IsIntegralCurveOn φ (fun _ x => fault.field x) (Icc tf tc) ∧
      IsIntegralCurveOn φ (fun _ x => post.field x) (Ici tc))
    (h0 : φ tf = PhasePlane.mk δ₀ 0)
    (hwell : post.deltaU - 2 * Real.pi < φ tc 0) (hδc : φ tc 0 < post.deltaU)
    (hA : fault.Aacc δ₀ (φ tc 0) < post.Adec (φ tc 0) post.deltaU) :
    Tendsto φ atTop (𝓝 (PhasePlane.mk post.deltaS 0)) := by
  have hE := clearing_energy_le (hMeq ▸ hM) hDf hφ.2.2.1 hφ.1 h0
  rw [hMeq] at hE
  exact post.tendsto_of_firstSwing_margin hM hDp hk h hPk hφ.2.2.2
    (PhasePlane.mk_coords (φ tc)).symm hwell hδc (by rw [← SwingParams.Adec]; linarith)

/-- Clearing-angle margin of a damped bolted fault.  With `D > 0` during a bolted fault
(`P_e^f ≡ 0`) and `δ_cc ∈ (δ₀, δ_u]` the zero of the undamped equal-area function
`g = A_acc − A_dec` (post-fault curve positive on `(δ₀, δ_u)`), there is `ε > 0` such that for
every clearing time `t_c − t_f ≤ √(2M(δ_cc − δ₀)/P_m) + ε` the clearing angle satisfies
`δ₀ ≤ δ(t_c) < δ_cc` and the undamped areas have a strict margin `A_acc < A_dec`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem boltedFault_damped_clearingAngle {fault post : SwingParams}
    (hM : 0 < post.M) (hMeq : fault.M = post.M) (hPm : fault.Pm = post.Pm) (hPm0 : 0 < post.Pm)
    (hDf : 0 < fault.D) (hk₁ : fault.k₁ = 0) (hk₂ : fault.k₂ = 0) {δ₀ δcc : ℝ}
    (hpos : ∀ x ∈ Ioo δ₀ post.deltaU, 0 < post.Pe x)
    (hcc : δcc ∈ Ioc δ₀ post.deltaU) (hg : eacG fault post δ₀ post.deltaU δcc = 0) :
    ∃ ε > 0, ∀ {φ : ℝ → State 2} {tf tc : ℝ}, tf ≤ tc →
      IsIntegralCurveOn φ (fun _ x => fault.field x) (Icc tf tc) → φ tf = PhasePlane.mk δ₀ 0 →
      tc - tf ≤ Real.sqrt (2 * post.M * (δcc - δ₀) / post.Pm) + ε →
      δ₀ ≤ φ tc 0 ∧ φ tc 0 < δcc ∧ fault.Aacc δ₀ (φ tc 0) < post.Adec (φ tc 0) post.deltaU := by
  have hMf : 0 < fault.M := hMeq ▸ hM
  have hPf : 0 < fault.Pm := hPm ▸ hPm0
  rw [← hMeq, ← hPm]
  set M := fault.M with hMdef
  set D := fault.D with hDdef
  set P := fault.Pm with hPdef
  set T := Real.sqrt (2 * M * (δcc - δ₀) / P) with hTdef
  -- the damped during-fault angle as a function of the elapsed time `τ = t − t_f`
  let F : ℝ → ℝ := fun τ => δ₀ + P / D * (τ - M / D * (1 - Real.exp (-(D / M) * τ)))
  have hFc : Continuous F := by fun_prop
  have haM : M / D * (D / M) = 1 := by field_simp
  -- `δ₀ ≤ F τ` for `τ ≥ 0`
  have hFlo : ∀ τ, 0 ≤ τ → δ₀ ≤ F τ := by
    intro τ hτ
    have h1 := Real.add_one_le_exp (-(D / M) * τ)
    have h2 : M / D * (1 - Real.exp (-(D / M) * τ)) ≤ τ := by
      have : 1 - Real.exp (-(D / M) * τ) ≤ D / M * τ := by linarith
      calc M / D * (1 - Real.exp (-(D / M) * τ)) ≤ M / D * (D / M * τ) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = τ := by rw [← mul_assoc, haM, one_mul]
    have : 0 ≤ P / D * (τ - M / D * (1 - Real.exp (-(D / M) * τ))) :=
      mul_nonneg (by positivity) (by linarith)
    simp only [F]; linarith
  -- `F τ ≤ δ₀ + P τ²/(2M)` for `τ ≥ 0` (the undamped angle), strictly for `τ > 0`
  have hFq : ∀ τ, 0 ≤ τ → F τ ≤ δ₀ + P / (2 * M) * τ ^ 2 := by
    intro τ hτ
    have h1 := SpecialFunctions.exp_neg_le_quadratic (u := D / M * τ) (by positivity)
    have h2 : τ - D / M * τ ^ 2 / 2 ≤ M / D * (1 - Real.exp (-(D / M) * τ)) := by
      have e : -(D / M) * τ = -(D / M * τ) := by ring
      rw [e]
      have : D / M * τ - (D / M * τ) ^ 2 / 2 ≤ 1 - Real.exp (-(D / M * τ)) := by linarith
      calc τ - D / M * τ ^ 2 / 2 = M / D * (D / M * τ - (D / M * τ) ^ 2 / 2) := by
            field_simp
        _ ≤ M / D * (1 - Real.exp (-(D / M * τ))) :=
            mul_le_mul_of_nonneg_left this (by positivity)
    have h3 : P / D * (τ - M / D * (1 - Real.exp (-(D / M) * τ))) ≤ P / D * (D / M * τ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h4 : P / D * (D / M * τ ^ 2 / 2) = P / (2 * M) * τ ^ 2 := by field_simp
    simp only [F]; linarith
  have hFq' : ∀ τ, 0 < τ → F τ < δ₀ + P / (2 * M) * τ ^ 2 := by
    intro τ hτ
    have h1 := SpecialFunctions.exp_neg_lt_quadratic (u := D / M * τ) (by positivity)
    have h2 : τ - D / M * τ ^ 2 / 2 < M / D * (1 - Real.exp (-(D / M) * τ)) := by
      have e : -(D / M) * τ = -(D / M * τ) := by ring
      rw [e]
      have : D / M * τ - (D / M * τ) ^ 2 / 2 < 1 - Real.exp (-(D / M * τ)) := by linarith
      calc τ - D / M * τ ^ 2 / 2 = M / D * (D / M * τ - (D / M * τ) ^ 2 / 2) := by
            field_simp
        _ < M / D * (1 - Real.exp (-(D / M * τ))) :=
            mul_lt_mul_of_pos_left this (by positivity)
    have h3 : P / D * (τ - M / D * (1 - Real.exp (-(D / M) * τ))) < P / D * (D / M * τ ^ 2 / 2) :=
      mul_lt_mul_of_pos_left (by linarith) (by positivity)
    have h4 : P / D * (D / M * τ ^ 2 / 2) = P / (2 * M) * τ ^ 2 := by field_simp
    simp only [F]; linarith
  -- the undamped angle reaches `δ_cc` exactly at `T`
  have hcc0 : 0 < δcc - δ₀ := sub_pos.mpr hcc.1
  have hTpos : 0 < T := Real.sqrt_pos.mpr (by positivity)
  have hT2 : δ₀ + P / (2 * M) * T ^ 2 = δcc := by
    rw [hTdef, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  have hFT : F T < δcc := hT2 ▸ hFq' T hTpos
  obtain ⟨ε, hε, hεF⟩ := Metric.eventually_nhds_iff.mp
    (hFc.continuousAt.eventually (gt_mem_nhds hFT))
  -- strict monotonicity of `g` on `[δ₀, δ_u]`
  have hfPe : ∀ x, fault.Pe x = 0 := fun x => by simp [SwingParams.Pe, hk₁, hk₂]
  have hmono : StrictMonoOn (eacG fault post δ₀ post.deltaU) (Icc δ₀ post.deltaU) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact fun z _ =>
        (hasDerivAt_eacG fault post hPm δ₀ post.deltaU z).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      rw [(hasDerivAt_eacG fault post hPm δ₀ post.deltaU z).deriv, hfPe, sub_zero]
      exact hpos z hz
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro φ tf tc htc hφ h0 hle
  have hδc := (fault.dampedBolted_trajectory hMf hDf hk₁ hk₂ hφ h0 tc ⟨htc, le_rfl⟩).2
  have hδF : φ tc 0 = F (tc - tf) := hδc
  have hτ0 : 0 ≤ tc - tf := by linarith
  have hlt : φ tc 0 < δcc := by
    rw [hδF]
    rcases lt_or_ge (tc - tf) T with h | h
    · calc F (tc - tf) ≤ δ₀ + P / (2 * M) * (tc - tf) ^ 2 := hFq _ hτ0
        _ < δ₀ + P / (2 * M) * T ^ 2 := by
            have : (tc - tf) ^ 2 < T ^ 2 := by nlinarith
            have : 0 < P / (2 * M) := by positivity
            nlinarith
        _ = δcc := hT2
    · apply hεF
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
  have hge : δ₀ ≤ φ tc 0 := hδF ▸ hFlo _ hτ0
  refine ⟨hge, hlt, ?_⟩
  have hg' := hmono ⟨hge, hlt.le.trans hcc.2⟩ ⟨hcc.1.le, hcc.2⟩ hlt
  rw [hg] at hg'
  simp only [eacG] at hg'
  linarith

/-- **Damping strictly delays the critical clearing time of a bolted fault.**  Same inertia and
mechanical power in both stages, `D > 0` during the bolted fault (`P_e^f ≡ 0`), `D ≥ 0`
post-fault, `δ_cc ∈ (δ₀, δ_u]` the critical clearing angle (zero of the undamped equal-area
function, post-fault curve positive on `(δ₀, δ_u)`).  Without damping the first swing stays
below `δ_u` exactly for `t_c − t_f ≤ t_cc^EAC = √(2M(δ_cc − δ₀)/P_m)`
(`FaultSequence.boltedFault_firstSwing_iff`); with damping there is `ε > 0` such that every
clearing time `t_c − t_f ≤ t_cc^EAC + ε` keeps the first swing below `δ_u`, so the true critical
clearing time is at least `t_cc^EAC + ε > t_cc^EAC`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem boltedFault_damped_firstSwing {pre fault post : SwingParams}
    (hM : 0 < post.M) (hMeq : fault.M = post.M) (hPm : fault.Pm = post.Pm) (hPm0 : 0 < post.Pm)
    (hDf : 0 < fault.D) (hDp : 0 ≤ post.D) (hk₁ : fault.k₁ = 0) (hk₂ : fault.k₂ = 0)
    (hk : 0 < post.k₂) (h : |post.Pm - post.k₁| < post.k₂) {δ₀ δcc : ℝ}
    (hpos : ∀ x ∈ Ioo δ₀ post.deltaU, 0 < post.Pe x)
    (hcc : δcc ∈ Ioc δ₀ post.deltaU) (hg : eacG fault post δ₀ post.deltaU δcc = 0) :
    ∃ ε > 0, ∀ {φ : ℝ → State 2} {tf tc : ℝ},
      (tf ≤ tc ∧ IsIntegralCurveOn φ (fun _ x => pre.field x) (Iic tf) ∧
        IsIntegralCurveOn φ (fun _ x => fault.field x) (Icc tf tc) ∧
        IsIntegralCurveOn φ (fun _ x => post.field x) (Ici tc)) →
      φ tf = PhasePlane.mk δ₀ 0 →
      tc - tf ≤ Real.sqrt (2 * post.M * (δcc - δ₀) / post.Pm) + ε →
      ∀ t ∈ Ici tc, φ t 0 ≤ post.deltaU := by
  obtain ⟨ε, hε, hmargin⟩ :=
    boltedFault_damped_clearingAngle hM hMeq hPm hPm0 hDf hk₁ hk₂ hpos hcc hg
  refine ⟨ε, hε, fun {φ tf tc} hφ h0 hle => ?_⟩
  obtain ⟨-, hlt, hA⟩ := hmargin hφ.1 hφ.2.2.1 h0 hle
  exact faultTrajectory_firstSwing_of_areas hM hMeq hDf.le hDp hk h hφ h0
    (hlt.le.trans hcc.2) hA.le

/-- **Damping strictly delays the critical clearing time (asymptotic recovery)**: under the
hypotheses of `boltedFault_damped_firstSwing` with `D > 0` post-fault, `P_m ≥ k₁` and
`δ_u − 2π < δ₀`, there is `ε > 0` such that every clearing time
`t_c − t_f ≤ √(2M(δ_cc − δ₀)/P_m) + ε` gives convergence to the post-fault stable equilibrium
`(δ_s, 0)`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem boltedFault_damped_tendsto {pre fault post : SwingParams}
    (hM : 0 < post.M) (hMeq : fault.M = post.M) (hPm : fault.Pm = post.Pm) (hPm0 : 0 < post.Pm)
    (hDf : 0 < fault.D) (hDp : 0 < post.D) (hk₁ : fault.k₁ = 0) (hk₂ : fault.k₂ = 0)
    (hk : 0 < post.k₂) (h : |post.Pm - post.k₁| < post.k₂) (hPk : post.k₁ ≤ post.Pm)
    {δ₀ δcc : ℝ} (hwell : post.deltaU - 2 * Real.pi < δ₀)
    (hpos : ∀ x ∈ Ioo δ₀ post.deltaU, 0 < post.Pe x)
    (hcc : δcc ∈ Ioc δ₀ post.deltaU) (hg : eacG fault post δ₀ post.deltaU δcc = 0) :
    ∃ ε > 0, ∀ {φ : ℝ → State 2} {tf tc : ℝ},
      (tf ≤ tc ∧ IsIntegralCurveOn φ (fun _ x => pre.field x) (Iic tf) ∧
        IsIntegralCurveOn φ (fun _ x => fault.field x) (Icc tf tc) ∧
        IsIntegralCurveOn φ (fun _ x => post.field x) (Ici tc)) →
      φ tf = PhasePlane.mk δ₀ 0 →
      tc - tf ≤ Real.sqrt (2 * post.M * (δcc - δ₀) / post.Pm) + ε →
      Tendsto φ atTop (𝓝 (PhasePlane.mk post.deltaS 0)) := by
  obtain ⟨ε, hε, hmargin⟩ :=
    boltedFault_damped_clearingAngle hM hMeq hPm hPm0 hDf hk₁ hk₂ hpos hcc hg
  refine ⟨ε, hε, fun {φ tf tc} hφ h0 hle => ?_⟩
  obtain ⟨hge, hlt, hA⟩ := hmargin hφ.1 hφ.2.2.1 h0 hle
  exact faultTrajectory_tendsto_of_areas hM hMeq hDf.le hDp hk h hPk hφ h0
    (by linarith) (hlt.trans_le hcc.2) hA

end powerlib.Synchronous
