import theorem.PowerSystem.Synchronous.GeneralSwing
import theorem.Dynamics.PiecewiseAffine
import theorem.Dynamics.FilippovSliding

/-! # Grid-forming converter with a circular current limiter: mode switching

Model boundary.
* Swing-type outer loop (VSM / droop with inertia), state `(δ, ω)`: `δ` the angle of the internal
  voltage `E e^{jδ}` relative to the stiff grid voltage `V`, `ω` its frequency deviation;
  `δ' = ω`, `M ω' = P_ref − P_e(δ) − D ω`. Continuous time, export-positive power as in
  `theorem/GridTiedConverter/GFM/Limiting/Saturation.lean`.
* Lossless line of reactance `X`; the current the voltage source would draw is
  `I = (E e^{jδ} − V)/(jX)`, `|I|² = (E² + V² − 2EV cos δ)/X²`. A circular limiter (work-sync
  T-current-limiting §1.1) with magnitude `I_max` switches by the state: the converter is
  unsaturated where `E² + V² − 2EV cos δ ≤ X² I_max²` (`demand δ ≤ capacity`) and exports
  `P_max sin δ`, `P_max = EV/X`; it is saturated elsewhere and injects `I_max` at the angle `φ`
  relative to its reference, exporting `P_sat cos(δ − φ)`, `P_sat = V I_max` (§1.3). The mode is
  a function of `δ` (state-dependent switching without hysteresis); the switched law
  `switchedPe` is in general discontinuous on the switching angles `demand δ = capacity`.
* On the switching surface the switched field is extended by Filippov's convex hull: a solution
  lying on a switching line `δ = δ_s` has velocities in the segment `[f_sat(x), f_unsat(x)]` of
  the two mode fields (`satField`, `unsatField`, absolute coordinates `(δ, ω)`).
* Excluded: inner loops, PWM, delays, hysteresis or timed switching, virtual impedance, grid
  dynamics, resistive lines; uniqueness of Filippov solutions and the stability, in the plane, of
  the pseudo-equilibria on the switching surface.
* The switched converter is a swing model with the arbitrary law `switchedPe`
  (`Synchronous.GeneralSwing`, `toGeneral`), read about a selected point `(δ*, 0)`.

Source: work-sync `theory/T-current-limiting.md` §1.1, §1.3, §1.6 (exit angle), §1.9 (switched
system stability framework, Filippov solutions); `theory/T-gfm-control.md` §1.10; A. F. Filippov,
*Differential Equations with Discontinuous Righthand Sides* (Kluwer, 1988), §2.4.

Results.
* `demand_lt_capacity_iff` (static): the strictly unsaturated angles are `cos δ > c_exit`,
  `c_exit = (E² + V² − X² I_max²)/(2EV)` (the exit angle of §1.6 with `R_t = 0`).
* Local readings at points off the switching surface: near a strictly unsaturated (saturated)
  angle the switched field is the unsaturated (saturated) swing field, so the local sentences are
  those of that mode (`Dynamics.holds_congr_nhds`).
* The switching surface carries no sliding motion (Filippov,
  `theorem/Dynamics/FilippovSliding.lean`): both modes have the normal component `ω` on a
  switching line (`inner_satField_eq`), so Filippov's segment has a velocity tangent to the line
  exactly at `ω = 0` (`exists_tangent_mem_segment_iff`); the equivalent control is undefined and
  the surface is crossed everywhere else. The zero velocity is a Filippov velocity at `(δ_s, 0)`
  exactly when `P_ref` lies between the saturated and the unsaturated powers at `δ_s`
  (`zero_mem_segment_iff`, `M ≠ 0`): these pseudo-equilibria are the only motions on the surface.
  Trajectory level (private implementation evidence, Rules §3a): every Filippov solution lying on
  a switching line on an open time set is such a rest point (`surface_solution_eq`), and each
  pseudo-equilibrium is a constant Filippov solution (`surface_solution_const`); stability on the
  surface is therefore vacuous. `latchUp` has the pseudo-equilibria `(±π/3, 0)` on its switching
  angles (`latchUp_pseudoEquilibrium`), between its stable operating point and its latched
  state.

Family and connection conclusions.
* No family of its own: a switched converter is read as the swing model with an arbitrary law
  `toGeneral` (`Synchronous.GeneralSwing.family`); the conclusions are member characterizations
  of that family with static right-hand sides.
* `mem_den_locallyExponentiallyStable_iff_of_unsaturated`: with `M > 0` at a strictly
  unsaturated angle, local exponential stability holds exactly when `P_max sin δ* = P_ref`,
  `D > 0` and `P_max cos δ* > 0`; `mem_den_locallyExponentiallyStable_iff_of_saturated`: at a
  strictly saturated angle exactly when `P_sat cos(δ* − φ) = P_ref`, `D > 0` and
  `P_sat sin(δ* − φ) < 0` (the swing hub on the active sinusoid,
  `Synchronous.GeneralSwing.mem_den_locallyExponentiallyStable_iff_of_sinusoid`).
* Latch-up (switched-system counterexample to the return to the normal mode):
  `mem_den_locallyExponentiallyStable_of_latchUp` — for `|P_ref| < P_sat`, `M, D > 0`, if the
  saturated stable angle `δ_s = φ − arccos(P_ref/P_sat)` lies strictly in the saturated region,
  the converter has a locally exponentially stable equilibrium in saturation. The explicit model
  `latchUp` (`E = V = X = I_max = M = D = 1`, `P_ref = 0`, `φ = −π/2`) has two locally
  exponentially stable equilibria in one period, the operating point `δ = 0` in the normal mode
  (`latchUp_mem_den_locallyExponentiallyStable`) and `δ = π` locked in saturation
  (`latchUp_saturated_mem_den_locallyExponentiallyStable`): solutions near `δ = π` never return to
  the normal mode, so no switched stability argument can give convergence to the operating point
  from every state (T-current-limiting §1.3: "the system can be locked on the saturated curve").
-/

noncomputable section
namespace powerlib.Limiting.Switching
open Filter Topology
open powerlib.Dynamics (State)

/-- A grid-forming swing converter on a stiff grid through a lossless line, with a circular
current limiter, read about a selected angle `δ*` (speed `0`). -/
structure Model where
  /-- Inertia `M`. -/
  M : ℝ
  /-- Damping `D`. -/
  D : ℝ
  /-- Power reference `P_ref`. -/
  Pref : ℝ
  /-- Internal voltage magnitude `E`. -/
  E : ℝ
  /-- Grid voltage magnitude `V`. -/
  V : ℝ
  /-- Line reactance `X`. -/
  X : ℝ
  /-- Current limit `I_max`. -/
  Imax : ℝ
  /-- Angle `φ` of the saturated current relative to the converter reference. -/
  φ : ℝ
  /-- The selected angle `δ*`. -/
  δ : ℝ

namespace Model

variable (m : Model)

/-- Peak power of the unsaturated converter, `P_max = EV/X`. -/
def Pmax : ℝ := m.E * m.V / m.X

/-- Peak power of the saturated converter, `P_sat = V I_max`. -/
def Psat : ℝ := m.V * m.Imax

/-- `X² |I(δ)|² = E² + V² − 2EV cos δ`: the current the voltage source would draw, scaled. -/
def demand (δ : ℝ) : ℝ := m.E ^ 2 + m.V ^ 2 - 2 * m.E * m.V * Real.cos δ

/-- `X² I_max²`. -/
def capacity : ℝ := m.X ^ 2 * m.Imax ^ 2

/-- The switched power law: `P_max sin δ` where the converter is unsaturated
(`demand δ ≤ capacity`), `P_sat cos(δ − φ)` where it is saturated. -/
def switchedPe (δ : ℝ) : ℝ :=
  if m.demand δ ≤ m.capacity then m.Pmax * Real.sin δ else m.Psat * Real.cos (δ - m.φ)

/-- The switched converter as a swing model with the arbitrary law `switchedPe`, about `(δ*, 0)`. -/
def toGeneral : Synchronous.GeneralSwing.Model :=
  ⟨m.M, m.D, m.Pref, fun δ _ => m.switchedPe δ, m.δ, 0⟩

/-- The unsaturated converter about `(δ*, 0)`. -/
def toUnsaturated : Synchronous.GeneralSwing.Model :=
  ⟨m.M, m.D, m.Pref, fun δ _ => m.Pmax * Real.sin δ, m.δ, 0⟩

/-- The saturated converter about `(δ*, 0)`. -/
def toSaturated : Synchronous.GeneralSwing.Model :=
  ⟨m.M, m.D, m.Pref, fun δ _ => m.Psat * Real.cos (δ - m.φ), m.δ, 0⟩

/-- The strictly unsaturated angles are `cos δ > c_exit = (E² + V² − X² I_max²)/(2EV)` (for
`EV > 0`): the exit-angle criterion with a lossless line. Static evidence on the model, not a
connection conclusion. -/
@[tmio M, powerlib_domain] theorem demand_lt_capacity_iff (hEV : 0 < m.E * m.V) (δ : ℝ) :
    m.demand δ < m.capacity ↔
      (m.E ^ 2 + m.V ^ 2 - m.X ^ 2 * m.Imax ^ 2) / (2 * (m.E * m.V)) < Real.cos δ := by
  rw [div_lt_iff₀ (by positivity), demand, capacity]
  constructor <;> intro h <;> nlinarith

@[tmio M, powerlib_domain] private theorem continuous_demand : Continuous m.demand := by
  unfold demand
  fun_prop

/-- Two swing models with the same data and selected point whose laws agree near the selected
angle satisfy the same local sentences. -/
@[tmio TM, powerlib_domain] private theorem mem_den_iff_of_eventuallyEq
    {x y : Synchronous.GeneralSwing.Model} (hM : x.M = y.M) (hD : x.D = y.D) (hτ : x.τ = y.τ)
    (hθ : x.θ = y.θ) (hω : x.ω = y.ω) (hPe : ∀ᶠ δ in 𝓝 x.θ, ∀ w, x.Pe δ w = y.Pe δ w)
    {P : Flow.Property}
    (hP : P = .lyapunovStable ∨ P = .locallyAsymptoticallyStable ∨
      P = .locallyExponentiallyStable ∨ P = .unstable) :
    x ∈ Synchronous.GeneralSwing.family.den (.flow P) ↔
      y ∈ Synchronous.GeneralSwing.family.den (.flow P) := by
  rw [(connection_proof% Synchronous.GeneralSwing.family_isAutonomous.mem_den_flow),
    (connection_proof% Synchronous.GeneralSwing.family_isAutonomous.mem_den_flow)]
  refine Dynamics.holds_congr_nhds ?_ hP
  have hc : Continuous fun z : State 2 => (z + x.point) 0 :=
    (PiLp.continuous_apply 2 _ 0).comp (continuous_id.add continuous_const)
  have h0 : (fun z : State 2 => (z + x.point) 0) 0 = x.θ := by
    simp [Synchronous.GeneralSwing.Model.point]
  have hev := hc.continuousAt.preimage_mem_nhds (h0 ▸ hPe)
  filter_upwards [hev] with z hz
  have hpt : x.point = y.point := by
    simp [Synchronous.GeneralSwing.Model.point, hθ, hω]
  simp only [Synchronous.GeneralSwing.Model.field, Synchronous.GeneralSwing.field, ← hpt, hM,
    hD, hτ]
  rw [Set.mem_preimage] at hz
  rw [hz]

/-- **Strictly unsaturated angles.** With `M > 0`, at an angle where the converter is strictly
unsaturated the switched converter is locally exponentially stable exactly when the angle is
balanced in the normal mode, `P_max sin δ* = P_ref`, with `D > 0` and `P_max cos δ* > 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff_of_unsaturated
    (hM : 0 < m.M) (hδ : m.demand m.δ < m.capacity) :
    connection% (m.toGeneral ∈
        Synchronous.GeneralSwing.family.den (.flow .locallyExponentiallyStable) ↔
      m ∈ {m : Model | m.Pmax * Real.sin m.δ = m.Pref ∧ 0 < m.D ∧
        0 < m.Pmax * Real.cos m.δ}) := by
  unfold powerlib.TMIO.Statement
  have hev : ∀ᶠ δ in 𝓝 m.δ, ∀ w, m.toGeneral.Pe δ w = m.toUnsaturated.Pe δ w := by
    filter_upwards [(m.continuous_demand.isOpen_preimage _ isOpen_Iio).mem_nhds hδ] with δ hδ'
    intro w
    have h' : m.demand δ ≤ m.capacity := le_of_lt hδ'
    simp [toGeneral, toUnsaturated, switchedPe, h']
  rw [mem_den_iff_of_eventuallyEq (x := m.toGeneral) (y := m.toUnsaturated) rfl rfl rfl rfl rfl hev
    (Or.inr (Or.inr (Or.inl rfl)))]
  have h := Synchronous.GeneralSwing.mem_den_locallyExponentiallyStable_iff_of_sinusoid
    m.toUnsaturated 0 m.Pmax 0 (by funext δ w; simp [toUnsaturated]) rfl hM
  unfold powerlib.TMIO.Statement at h
  rw [h]
  simp [toUnsaturated]

/-- **Strictly saturated angles.** With `M > 0`, at an angle where the converter is strictly
saturated the switched converter is locally exponentially stable exactly when the angle is
balanced in saturation, `P_sat cos(δ* − φ) = P_ref`, with `D > 0` and `P_sat sin(δ* − φ) < 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff_of_saturated
    (hM : 0 < m.M) (hδ : m.capacity < m.demand m.δ) :
    connection% (m.toGeneral ∈
        Synchronous.GeneralSwing.family.den (.flow .locallyExponentiallyStable) ↔
      m ∈ {m : Model | m.Psat * Real.cos (m.δ - m.φ) = m.Pref ∧ 0 < m.D ∧
        m.Psat * Real.sin (m.δ - m.φ) < 0}) := by
  unfold powerlib.TMIO.Statement
  have hev : ∀ᶠ δ in 𝓝 m.δ, ∀ w, m.toGeneral.Pe δ w = m.toSaturated.Pe δ w := by
    filter_upwards [(m.continuous_demand.isOpen_preimage _ isOpen_Ioi).mem_nhds hδ] with δ hδ'
    intro w
    have h' : ¬ m.demand δ ≤ m.capacity := not_le.mpr hδ'
    simp [toGeneral, toSaturated, switchedPe, h']
  rw [mem_den_iff_of_eventuallyEq (x := m.toGeneral) (y := m.toSaturated) rfl rfl rfl rfl rfl hev
    (Or.inr (Or.inr (Or.inl rfl)))]
  have hsin : ∀ δ, Real.sin (δ - (m.φ - Real.pi / 2)) = Real.cos (δ - m.φ) := fun δ => by
    rw [show δ - (m.φ - Real.pi / 2) = (δ - m.φ) + Real.pi / 2 by ring, Real.sin_add_pi_div_two]
  have hcos : ∀ δ, Real.cos (δ - (m.φ - Real.pi / 2)) = -Real.sin (δ - m.φ) := fun δ => by
    rw [show δ - (m.φ - Real.pi / 2) = (δ - m.φ) + Real.pi / 2 by ring, Real.cos_add_pi_div_two]
  have h := Synchronous.GeneralSwing.mem_den_locallyExponentiallyStable_iff_of_sinusoid
    m.toSaturated 0 m.Psat (m.φ - Real.pi / 2) (by funext δ w; simp [toSaturated, hsin]) rfl hM
  unfold powerlib.TMIO.Statement at h
  rw [h]
  simp only [toSaturated, Set.mem_ofPred_eq, zero_add, hsin, hcos]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1, h2, by linarith⟩

/-- **Latch-up.** With `M, D > 0` and `|P_ref| < P_sat`, if the saturated stable angle
`δ* = φ − arccos(P_ref/P_sat)` lies strictly in the saturated region, the switched converter has a
locally exponentially stable equilibrium in saturation there: solutions starting near it stay
saturated and never return to the normal mode. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_of_latchUp (hM : 0 < m.M)
    (hD : 0 < m.D) (hsat : |m.Pref| < m.Psat)
    (hδ : m.δ = m.φ - Real.arccos (m.Pref / m.Psat)) (hreg : m.capacity < m.demand m.δ) :
    connection% (m.toGeneral ∈
      Synchronous.GeneralSwing.family.den (.flow .locallyExponentiallyStable)) := by
  have h := m.mem_den_locallyExponentiallyStable_iff_of_saturated hM hreg
  unfold powerlib.TMIO.Statement at h ⊢
  have hPs : 0 < m.Psat := (abs_nonneg _).trans_lt hsat
  have hy : |m.Pref / m.Psat| < 1 := by
    rw [abs_div, abs_of_pos hPs, div_lt_one hPs]
    exact hsat
  obtain ⟨hy1, hy2⟩ := abs_lt.mp hy
  refine h.mpr ⟨?_, hD, ?_⟩
  · rw [hδ, show m.φ - Real.arccos (m.Pref / m.Psat) - m.φ = -Real.arccos (m.Pref / m.Psat) by
      ring, Real.cos_neg, Real.cos_arccos hy1.le hy2.le]
    field_simp
  · rw [hδ, show m.φ - Real.arccos (m.Pref / m.Psat) - m.φ = -Real.arccos (m.Pref / m.Psat) by
      ring, Real.sin_neg, Real.sin_arccos]
    have : 0 < Real.sqrt (1 - (m.Pref / m.Psat) ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
    nlinarith

/-! ## The switching surface: Filippov solutions, no sliding motion -/

/-- The unsaturated converter field `(δ, ω) ↦ (ω, (P_ref − P_max sin δ − D ω)/M)`. -/
def unsatField : State 2 → State 2 :=
  Synchronous.GeneralSwing.field m.M m.D m.Pref fun δ _ => m.Pmax * Real.sin δ

/-- The saturated converter field `(δ, ω) ↦ (ω, (P_ref − P_sat cos(δ − φ) − D ω)/M)`. -/
def satField : State 2 → State 2 :=
  Synchronous.GeneralSwing.field m.M m.D m.Pref fun δ _ => m.Psat * Real.cos (δ - m.φ)

/-- **The switching surface is degenerate.** The switching set `demand δ = capacity` is a union of
lines `δ = δ_s` with normal `e_δ`; both modes have the same normal component `ω` there.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem inner_satField_eq (x : State 2) :
    inner ℝ (PhasePlane.mk 1 0) (m.satField x) = x 1 ∧
      inner ℝ (PhasePlane.mk 1 0) (m.unsatField x) = x 1 := by
  constructor <;>
    simp [satField, unsatField, Synchronous.GeneralSwing.field, PhasePlane.mk, PiLp.inner_apply,
      Fin.sum_univ_two]

/-- **The sliding region is the rest line.** On a line `δ = δ_s`, Filippov's segment
`[f_sat(x), f_unsat(x)]` contains a velocity tangent to the line exactly when `ω = 0`: the
switching surface is crossed transversally everywhere else. Static evidence on the model, not a
connection conclusion. -/
@[tmio M, powerlib_domain] theorem exists_tangent_mem_segment_iff (x : State 2) :
    (∃ v ∈ segment ℝ (m.satField x) (m.unsatField x), inner ℝ (PhasePlane.mk 1 0) v = 0) ↔
      x 1 = 0 := by
  obtain ⟨hs, hu⟩ := m.inner_satField_eq x
  constructor
  · rintro ⟨v, hv, hv0⟩
    have h := Dynamics.Sliding.mul_inner_nonpos_of_mem_segment hv hv0
    rw [hs, hu] at h
    nlinarith [sq_nonneg (x 1)]
  · intro h0
    refine ⟨m.satField x, left_mem_segment ℝ _ _, ?_⟩
    rw [hs, h0]

/-- **Pseudo-equilibria.** With `M ≠ 0`, Filippov's segment at the rest point `(δ, 0)` contains
the zero velocity exactly when `P_ref` lies between the saturated and the unsaturated powers at
`δ`. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem zero_mem_segment_iff (hM : m.M ≠ 0) (δ : ℝ) :
    (0 : State 2) ∈ segment ℝ (m.satField (PhasePlane.mk δ 0)) (m.unsatField (PhasePlane.mk δ 0)) ↔
      m.Pref ∈ segment ℝ (m.Psat * Real.cos (δ - m.φ)) (m.Pmax * Real.sin δ) := by
  have hf : ∀ a b : ℝ, a • m.satField (PhasePlane.mk δ 0) + b • m.unsatField (PhasePlane.mk δ 0) =
      PhasePlane.mk 0 ((a * (m.Pref - m.Psat * Real.cos (δ - m.φ)) +
        b * (m.Pref - m.Pmax * Real.sin δ)) / m.M) := by
    intro a b
    ext i
    fin_cases i
    · simp [satField, unsatField, Synchronous.GeneralSwing.field, PhasePlane.mk]
    · simp [satField, unsatField, Synchronous.GeneralSwing.field, PhasePlane.mk]
      ring
  constructor
  · rintro ⟨a, b, ha, hb, hab, h⟩
    rw [hf, PhasePlane.mk_eq_zero_iff, div_eq_zero_iff] at h
    have h1 := h.2.resolve_right hM
    exact ⟨a, b, ha, hb, hab, by
      simp only [smul_eq_mul]
      have : m.Pref = (a + b) * m.Pref := by rw [hab, one_mul]
      linarith⟩
  · rintro ⟨a, b, ha, hb, hab, h⟩
    refine ⟨a, b, ha, hb, hab, ?_⟩
    rw [hf, PhasePlane.mk_eq_zero_iff, div_eq_zero_iff]
    simp only [smul_eq_mul] at h
    refine ⟨rfl, Or.inl ?_⟩
    have : m.Pref = (a + b) * m.Pref := by rw [hab, one_mul]
    linarith

/-- **No sliding motion on the switching surface** (implementation evidence: trajectory level,
Rules §3a). A Filippov solution lying on a line `δ = δ_s` on an open time set `I`, with velocities
in the segment `[f_sat, f_unsat]` (the convex hull of the two modes at the switching angle), stays
at the rest point `(δ_s, 0)`, and `P_ref` lies between the two mode powers there (`M ≠ 0`): the
surface carries no sliding motion, only pseudo-equilibria
(`Dynamics.Sliding.inner_eq_zero_of_mem_surface` on the degenerate surface `inner_satField_eq`). -/
@[tmio TM, powerlib_domain] private theorem surface_solution_eq (hM : m.M ≠ 0) {δs : ℝ}
    {c v : ℝ → State 2} {I : Set ℝ} (hI : IsOpen I) (hon : ∀ s ∈ I, c s 0 = δs)
    (hc : ∀ s ∈ I, HasDerivAt c (v s) s ∧ v s ∈ segment ℝ (m.satField (c s)) (m.unsatField (c s)))
    {t : ℝ} (ht : t ∈ I) :
    c t = PhasePlane.mk δs 0 ∧
      m.Pref ∈ segment ℝ (m.Psat * Real.cos (δs - m.φ)) (m.Pmax * Real.sin δs) := by
  have hon' : ∀ s ∈ I, inner ℝ (PhasePlane.mk 1 0) (c s) = δs := fun s hs => by
    simp [PhasePlane.mk, PiLp.inner_apply, Fin.sum_univ_two, hon s hs]
  have hrest : ∀ s ∈ I, c s 1 = 0 := fun s hs =>
    (m.exists_tangent_mem_segment_iff (c s)).mp ⟨v s, (hc s hs).2,
      Dynamics.Sliding.inner_eq_zero_of_mem_surface hI hon' hs (hc s hs).1⟩
  have hpt : ∀ s ∈ I, c s = PhasePlane.mk δs 0 := fun s hs => by
    rw [← PhasePlane.mk_coords (c s), hon s hs, hrest s hs]
  refine ⟨hpt t ht, ?_⟩
  have hv0 : v t = 0 := by
    have hconst : HasDerivAt c 0 t :=
      (hasDerivAt_const t (PhasePlane.mk δs 0)).congr_of_eventuallyEq
        (Filter.eventually_of_mem (hI.mem_nhds ht) hpt)
    exact (hc t ht).1.unique hconst
  have h := (hc t ht).2
  rw [hv0, hpt t ht] at h
  exact (m.zero_mem_segment_iff hM δs).mp h

/-- **The pseudo-equilibria are Filippov solutions** (implementation evidence: trajectory level).
If `P_ref` lies between the two mode powers at `δ_s`, the rest point `(δ_s, 0)` is a constant
solution of the Filippov inclusion `ẋ ∈ [f_sat(x), f_unsat(x)]`. -/
@[tmio TM, powerlib_domain] private theorem surface_solution_const (hM : m.M ≠ 0) {δs : ℝ}
    (hP : m.Pref ∈ segment ℝ (m.Psat * Real.cos (δs - m.φ)) (m.Pmax * Real.sin δs)) (t : ℝ) :
    HasDerivAt (fun _ : ℝ => PhasePlane.mk δs 0) 0 t ∧
      (0 : State 2) ∈ segment ℝ (m.satField (PhasePlane.mk δs 0))
        (m.unsatField (PhasePlane.mk δs 0)) :=
  ⟨hasDerivAt_const t _, (m.zero_mem_segment_iff hM δs).mpr hP⟩

end Model

/-- The latch-up example: `E = V = X = I_max = 1` (`P_max = P_sat = 1`, unsaturated exactly for
`cos δ ≥ 1/2`), `M = D = 1`, `P_ref = 0`, saturated current angle `φ = −π/2` (saturated power
`cos(δ + π/2) = −sin δ`), about the angle `δ*`. -/
def latchUp (δ : ℝ) : Model := ⟨1, 1, 0, 1, 1, 1, 1, -(Real.pi / 2), δ⟩

/-- The operating point `δ = 0` of `latchUp` (normal mode) is locally exponentially stable. -/
@[tmio TM, powerlib_domain] theorem latchUp_mem_den_locallyExponentiallyStable :
    connection% ((latchUp 0).toGeneral ∈
      Synchronous.GeneralSwing.family.den (.flow .locallyExponentiallyStable)) := by
  have h := (latchUp 0).mem_den_locallyExponentiallyStable_iff_of_unsaturated one_pos
    (by norm_num [latchUp, Model.demand, Model.capacity])
  unfold powerlib.TMIO.Statement at h ⊢
  exact h.mpr (by norm_num [latchUp, Model.Pmax])

/-- The angle `δ = π` of `latchUp` is locally exponentially stable, locked in saturation: a second
stable equilibrium in the same period as the operating point. -/
@[tmio TM, powerlib_domain] theorem latchUp_saturated_mem_den_locallyExponentiallyStable :
    connection% ((latchUp Real.pi).toGeneral ∈
      Synchronous.GeneralSwing.family.den (.flow .locallyExponentiallyStable)) := by
  have h := (latchUp Real.pi).mem_den_locallyExponentiallyStable_iff_of_saturated one_pos
    (by norm_num [latchUp, Model.demand, Model.capacity])
  unfold powerlib.TMIO.Statement at h ⊢
  refine h.mpr ?_
  have h1 : Real.pi - -(Real.pi / 2) = Real.pi / 2 + Real.pi := by ring
  simp only [latchUp, Model.Psat, Set.mem_ofPred_eq, h1, Real.cos_add_pi, Real.sin_add_pi,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  norm_num

/-- The switching angles `±π/3` of `latchUp` (`demand = capacity`) are pseudo-equilibria: Filippov's
segment at `(±π/3, 0)` contains the zero velocity (`P_ref = 0` lies between `−√3/2` and `√3/2`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem latchUp_pseudoEquilibrium (δ : ℝ) {θ : ℝ}
    (hθ : θ = Real.pi / 3 ∨ θ = -(Real.pi / 3)) :
    (latchUp δ).demand θ = (latchUp δ).capacity ∧
      (0 : State 2) ∈ segment ℝ ((latchUp δ).satField (PhasePlane.mk θ 0))
        ((latchUp δ).unsatField (PhasePlane.mk θ 0)) := by
  have hcos : Real.cos θ = 1 / 2 := by
    rcases hθ with rfl | rfl
    · exact Real.cos_pi_div_three
    · rw [Real.cos_neg, Real.cos_pi_div_three]
  refine ⟨by norm_num [latchUp, Model.demand, Model.capacity, hcos], ?_⟩
  rw [(latchUp δ).zero_mem_segment_iff one_ne_zero, segment_eq_uIcc]
  have h1 : Real.cos (θ - -(Real.pi / 2)) = -Real.sin θ := by
    rw [sub_neg_eq_add, Real.cos_add_pi_div_two]
  have hs : Real.sin θ ^ 2 = 3 / 4 := by nlinarith [Real.sin_sq_add_cos_sq θ]
  simp only [latchUp, Model.Psat, Model.Pmax, h1, one_mul, div_one, mul_one]
  rcases le_total 0 (Real.sin θ) with h | h
  · rw [Set.uIcc_of_le (by linarith)]; constructor <;> linarith
  · rw [Set.uIcc_of_ge (by linarith)]; constructor <;> linarith

end powerlib.Limiting.Switching
