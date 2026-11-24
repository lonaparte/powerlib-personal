import theorem.Numerics.EulerPorts

/-! # Grid-forming swing synchronization with the grid-frequency port, and its explicit Euler
discretization

The reduced two-state grid-forming (GFM) converter — a voltage source behind a quasi-static line,
synchronized by a virtual-synchronous-machine swing law — read through its dual port: the input is
the deviation of the grid frequency, which enters the angle equation, and the conjugate output is
the power mismatch `P_ref − P(δ)` (the port of the port-Hamiltonian form with the energy
`U(δ) + M Δω²/2`, `U' = P − P_ref`, and the input matrix `(−1, 0)ᵀ`). The output does not depend
on the input, so an explicit Euler step with a large input against a nonzero output draws
unbounded energy: an Euler discretization with any step `h > 0` is passive exactly when the output
vanishes at every state, that is when the line carries no synchronizing power, `A = E V/|Z| = 0`,
and the set-point equals the line's constant power, `c₀ = P_ref`
(`Numerics.eulerPortFamily_mem_den_passive_iff`). Scaffold: `theorem/Numerics/EulerPorts.agda`.

Model boundary.
* State `x = (δ, Δω) : Dynamics.State 2`, in this order: angle of the internal voltage relative to
  the grid voltage (rad) and angular-frequency deviation of the converter from the nominal
  frequency (rad/s); per unit, dq frame rotating at the nominal frequency, stiff grid `V∠0`.
* Continuous time: `δ̇ = Δω − u`, `M Δω̇ = P_ref − P(δ) − D Δω`, output `y = P_ref − P(δ)`, with the
  export-positive active power of the quasi-static line `P(δ) = c₀ + A sin(δ − α)`
  (`c₀ = E² R/|Z|²`, `A = E V/|Z|`, `α = atan2(R, X)`, as in
  `theorem/GridTiedConverter/GFM/Discrete/SwingPort.lean`). Parameters: virtual inertia `M > 0`,
  damping `D ≥ 0`, `A ≥ 0` (the open line `A = 0` included), any `c₀, α`, set-point `P_ref`. The
  port `u` is the grid-frequency deviation, `u (P_ref − P(δ))` the supplied power.
* A model (`DualPort.Model`) is a parameter set with a selected angle `δ*`, read in the
  coordinates `z = x − (δ*, 0)`.
* Excluded: power filter, reactive-power/voltage loop (constant `E`), inner loops, line dynamics,
  current limiting, PLL, delays, PWM; the momentum (set-point) port is
  `theorem/GridTiedConverter/GFM/Discrete/SwingPort.lean`.
* Discretization (I): `DualPort.Euler`, a model and a step `h > 0`; the explicit Euler step
  `x⁺ = x + h f(x, u)` with the input held over the step, the same output, step length `h`, exact
  arithmetic, fixed step.

Source: work-sync GFM study note t9 (scratchpad `gfm/t9-discrete/REPORT-coord.md`, (a): with the
grid-frequency port, output `P_ref − P(δ)`, the Euler discretization is passive iff
`E V/|Z| = 0` and `c₀ = P_ref`; script `s1_swing_euler_energy.py` (4)); base model
`gfm/base-model.md`, Layer 1; `theorem/Numerics/EulerPorts.lean`
(`Numerics.passive_eulerSystem_iff`, `Numerics.eulerPortFamily_mem_den_passive_iff`); van der
Schaft, *L2-Gain and Passivity Techniques in Nonlinear Control*, §4 (port-Hamiltonian systems).

Results.
* `DualPort.Params.power` (the power characteristic), `DualPort.Params.field` (the port field),
  `DualPort.Params.output` (the power mismatch), `DualPort.Model.system` (the centred port
  system); `DualPort.output_eq_zero_iff` (the output vanishes at every state exactly when
  `A = 0` and `c₀ = P_ref`).

Family and connection conclusions.
* `DualPort.family : Family Model Requirement 2 1`: every model read as its centred port system;
  requirements `flat` (`A = 0` and `c₀ = P_ref`: the output vanishes) and `coupled` (`A > 0`);
  passivity translates into `flat`, the flow sentences have no translation (the whole,
  inconsistent, language), the envelope sentences into nothing. `DualPort.chain_le_semantics`:
  every translation is sound (a flat model supplies nothing).
* `DualPort.eulerFamily` (every discretization read as the Euler discretization of its model's
  port system). `DualPort.euler_mem_den_passive_iff`: a discretization with any step `h > 0` is
  passive exactly when `A = 0` and `c₀ = P_ref`; `DualPort.euler_exact_passive`: the passivity
  translation of the Euler family is exact.
-/

noncomputable section

namespace powerlib.GFM.DualPort

open powerlib.Dynamics (State)

/-- Parameters of the two-state GFM swing synchronization with the grid-frequency port: inertia
`M > 0`, damping `D ≥ 0`, the power characteristic `P(δ) = c₀ + A sin(δ − α)` with `A ≥ 0`, and
the active-power set-point `P_ref`. -/
structure Params where
  M : ℝ
  D : ℝ
  c0 : ℝ
  A : ℝ
  α : ℝ
  Pref : ℝ
  M_pos : 0 < M
  D_nonneg : 0 ≤ D
  A_nonneg : 0 ≤ A

attribute [powerlib_domain] Params.M_pos Params.D_nonneg Params.A_nonneg

namespace Params

variable (g : Params)

/-- The export-positive active power of the quasi-static line, `P(δ) = c₀ + A sin(δ − α)`. -/
def power (δ : ℝ) : ℝ := g.c0 + g.A * Real.sin (δ - g.α)

/-- The swing law with the grid-frequency port: `δ̇ = Δω − u`, `M Δω̇ = P_ref − P(δ) − D Δω`. -/
def field (x : State 2) (u : Fin 1 → ℝ) : State 2 :=
  WithLp.toLp 2 ![x 1 - u 0, (g.Pref - g.power (x 0) - g.D * x 1) / g.M]

/-- The conjugate output, the power mismatch `P_ref − P(δ)`. -/
def output (x : State 2) : Fin 1 → ℝ := ![g.Pref - g.power (x 0)]

end Params

/-- A model: a parameter set with a selected angle `δ*`. -/
structure Model where
  /-- The parameters. -/
  p : Params
  /-- The selected angle `δ*`. -/
  δs : ℝ

/-- The selected point `(δ*, 0)`. -/
def Model.point (m : Model) : State 2 := WithLp.toLp 2 ![m.δs, 0]

/-- The port system in the coordinates `z = x − (δ*, 0)`: the field and the output translated to
the selected point. -/
def Model.system (m : Model) : Port.System 2 1 :=
  ⟨fun z u => m.p.field (z + m.point) u, fun z _ => m.p.output (z + m.point)⟩

/-- **The power mismatch vanishes everywhere exactly on a flat characteristic.** The output
`P_ref − c₀ − A sin(δ − α)` is zero at every state exactly when `A = 0` and `c₀ = P_ref`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem output_eq_zero_iff (m : Model) :
    (∀ z, m.system.output z 0 = 0) ↔ m.p.A = 0 ∧ m.p.c0 = m.p.Pref := by
  have hz : ∀ z : State 2, m.system.output z 0 0 =
      m.p.Pref - m.p.c0 - m.p.A * Real.sin (z 0 + m.δs - m.p.α) := by
    intro z
    simp [Model.system, Params.output, Params.power, Model.point]
    ring
  constructor
  · intro h
    have h0 := hz (WithLp.toLp 2 ![m.p.α - m.δs, 0])
    have h1 := hz (WithLp.toLp 2 ![m.p.α - m.δs + Real.pi / 2, 0])
    rw [h] at h0 h1
    have e : m.p.α - m.δs + Real.pi / 2 + m.δs - m.p.α = Real.pi / 2 := by ring
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at h0 h1
    rw [e, Real.sin_pi_div_two] at h1
    rw [show m.p.α - m.δs + m.δs - m.p.α = 0 by ring, Real.sin_zero] at h0
    constructor <;> linarith
  · rintro ⟨hA, hc⟩ z
    funext i
    fin_cases i
    simpa [hA, hc] using hz z

@[tmio M, powerlib_domain] private theorem output_indep (m : Model) (z : State 2)
    (u : Fin 1 → ℝ) : m.system.output z u = m.system.output z 0 := rfl

/-- Requirements of the grid-frequency port. -/
inductive Requirement
  /-- A flat power characteristic: no synchronizing power `A = 0` and the matched set-point
  `c₀ = P_ref`. -/
  | flat
  /-- A coupled line, `A > 0`. -/
  | coupled

/-- Satisfaction of a requirement. -/
def Meets (m : Model) : Requirement → Prop
  | .flat => m.p.A = 0 ∧ m.p.c0 = m.p.Pref
  | .coupled => 0 < m.p.A

/-- Passivity translates into `flat`; the flow sentences have no translation (the whole,
inconsistent, language); the envelope sentences translate into nothing. -/
def translate : Sentence → Set Requirement
  | .passive => {.flat}
  | .flow _ => Set.univ
  | .envelope _ => ∅

/-- The grid-frequency port family: every model read as its centred port system. -/
def family : Family Model Requirement 2 1 :=
  ⟨fun m => m.system, Meets, translate⟩

@[tmio M, powerlib_domain] theorem family_isPort : family.IsPort Model.system := fun _ => rfl

/-- A flat model supplies nothing: it is passive with the zero storage. -/
@[tmio M, powerlib_domain] private theorem passive_of_flat (m : Model) (hm : Meets m .flat) :
    m.system.Passive := by
  have h0 := (output_eq_zero_iff m).mpr hm
  refine ⟨_, Port.System.passiveWith_of_rate _ (fun _ => 0) (fun _ => le_rfl) (fun _ _ => 0)
    (fun u x t₀ t₁ t _ _ => hasDerivWithinAt_const _ _ _) fun z u => ?_⟩
  simp [Port.System.supply, output_indep m z u, h0 z]

/-- Every translation of the grid-frequency port family is sound. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine (connection_proof% Family.chain_le_semantics_iff).mpr fun s => ?_
  intro m hm
  rw [(connection_proof% TMIO.mem_realize)] at hm
  rcases s with P | _ | E
  · have h1 : Meets m .flat := hm .flat (Set.mem_univ _)
    have h2 : Meets m .coupled := hm .coupled (Set.mem_univ _)
    exact absurd h1.1 h2.ne'
  · rw [(connection_proof% family_isPort.mem_den_passive_iff)]
    exact passive_of_flat m (hm .flat rfl)
  · rw [(connection_proof% family_isPort.den_envelope)]
    trivial

/-! ## The explicit Euler discretization -/

/-- The explicit Euler discretization of a grid-frequency port model with step `h > 0`. -/
abbrev Euler := Numerics.EulerStep Model

/-- The Euler discretization family: every discretization read as the Euler discretization of its
model's port system, with step length its step. -/
def eulerFamily : Family Euler Requirement 2 1 :=
  Numerics.eulerPortFamily family Model.system Numerics.EulerStep.design Numerics.EulerStep.h

/-- **An Euler discretization of the grid-frequency port is passive exactly when the line carries
no synchronizing power and the set-point is matched**, `A = E V/|Z| = 0` and `c₀ = P_ref`,
whatever its step `h > 0`: the output `P_ref − P(δ)` does not see the input, so the Euler
discretization is passive exactly when it vanishes at every state
(`Numerics.eulerPortFamily_mem_den_passive_iff`, `output_eq_zero_iff`). -/
@[tmio TM, powerlib_domain] theorem euler_mem_den_passive_iff (m : Model) (h : ℝ) (hh : 0 < h) :
    connection% ((⟨m, h, hh⟩ : Euler) ∈ eulerFamily.den .passive ↔
      m.p.A = 0 ∧ m.p.c0 = m.p.Pref) := by
  unfold powerlib.TMIO.Statement
  exact (connection_proof% Numerics.eulerPortFamily_mem_den_passive_iff (F := family)
    (sys := Model.system) (design := Numerics.EulerStep.design) (step := Numerics.EulerStep.h)
    (y := (⟨m, h, hh⟩ : Euler)) hh (output_indep m)).trans (output_eq_zero_iff m)

/-- **The passivity translation of the Euler family is exact**: a discretization is passive
exactly when its model is flat (`euler_mem_den_passive_iff`). -/
@[tmio TM, powerlib_domain] theorem euler_exact_passive :
    connection% (eulerFamily.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  ext ⟨m, h, hh⟩
  have hi := euler_mem_den_passive_iff m h hh
  unfold powerlib.TMIO.Statement at hi
  rw [hi, (connection_proof% TMIO.mem_realize)]
  change (∀ q ∈ ({.flat} : Set Requirement), Meets m q) ↔ _
  simp only [Set.mem_singleton_iff, forall_eq]
  rfl

end powerlib.GFM.DualPort
