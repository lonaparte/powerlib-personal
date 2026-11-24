import theorem.PowerSystem.Synchronous.PortEuler
import theorem.Family.Reading

/-! # Grid-forming swing synchronization with a power port: the classical machine, and its
explicit Euler discretization

The reduced two-state grid-forming (GFM) converter — a voltage source behind a quasi-static line,
synchronized by a virtual-synchronous-machine (VSM) swing law — with the deviation of its
active-power set-point as input port and its frequency deviation as output. In the momentum
coordinate `p = M Δω` it is the classical machine on an infinite bus with mechanical power
`P_ref − c₀`, bus coefficient `A` and rotor angle `δ − α` (`Synchronous.ClassicalSM`), so every
sentence, passivity included, is read through that family: the continuous model is passive
exactly when the set-point equals the line's constant power `c₀`, and no explicit Euler
discretization is passive, whatever its step — the classical machine's law
`Synchronous.ClassicalSM.euler_not_mem_den_passive` read through the same change of coordinates,
which commutes with the Euler step. Scaffold:
`theorem/GridTiedConverter/GFM/Discrete/SwingPortMachine.agda`.

Model boundary.
* State `x = (δ, Δω) : Dynamics.State 2`, in this order: angle of the internal voltage relative
  to the grid voltage (rad) and angular-frequency deviation from the nominal frequency (rad/s);
  per unit, dq frame rotating at the nominal frequency, stiff grid `V∠0`.
* Continuous time, `δ̇ = Δω`, `M Δω̇ = P_ref + u − P(δ) − D Δω`, output `y = Δω`, with the
  export-positive active power of the quasi-static line `P(δ) = c₀ + A sin(δ − α)`
  (`c₀ = E² R/|Z|²`, `A = E V/|Z|`, `α = atan2(R, X)`; lossless line `c₀ = α = 0`, `A = E V/X`,
  the infinite-bus power of `theorem/GridTiedConverter/GFM/VSMLPF.lean`). Parameters: virtual
  inertia `M > 0`, damping `D ≥ 0`, `A > 0`, any `c₀, α`, set-point `P_ref`. The port `u` is the
  deviation of the set-point (export-positive power into the swing law), `u Δω` the supplied
  power.
* A model (`SwingPort.Model`) is a parameter set with a selected angle `δ*`, read in the
  coordinates `z = x − (δ*, 0)` (the library reads sentences at the origin).
* Excluded: power filter (the three-state model is `theorem/GridTiedConverter/GFM/VSMLPF.lean`),
  reactive-power/voltage loop (constant `E`), inner voltage and current loops, line dynamics,
  current limiting, PLL, delays, PWM.
* Discretization (I): `SwingPort.Euler`, a model and a step `h > 0`; the explicit Euler step
  `x⁺ = x + h f(x, u)` with the input held over the step, the same output `Δω`, step length `h`,
  exact arithmetic, fixed step.

Source: work-sync GFM study note t9 (scratchpad `gfm/t9-discrete/REPORT-coord.md`, (a): the swing
port read as the classical machine, explicit Euler never passive; base model `gfm/base-model.md`,
Layer 1); `theorem/PowerSystem/Synchronous/PH.lean` (`Synchronous.ClassicalSM.family`,
`Synchronous.ClassicalSM.exact_passive`, `Synchronous.ClassicalSM.chain_le_semantics`),
`theorem/PowerSystem/Synchronous/PortEuler.lean`
(`Synchronous.ClassicalSM.euler_not_mem_den_passive`), `theorem/Numerics/EulerPorts.lean`
(`Numerics.eulerSystem_conjugate`, `Map.System.passive_conjugate_iff`,
`Port.System.passive_conjugate_iff`), `theorem/Family/Reading.lean`
(`Spectral.mem_den_flow_iff_of_transport`, `Spectral.realize_subset_den_of_hub`,
`Spectral.exact_of_hub`); van der Schaft, *L2-Gain and Passivity Techniques in Nonlinear
Control*, §4 (passivity of port-Hamiltonian systems).

Results.
* `SwingPort.Params.power` (the power characteristic), `SwingPort.Params.field` (the port field),
  `SwingPort.Model.system` (the centred port system), `SwingPort.Model.toClassicalSM` (the
  machine `⟨M, D, A, P_ref − c₀⟩` at the angle `δ* − α`).
* `SwingPort.system_eq_conjugate`: the port system is the classical machine's centred pH port
  system in the coordinates `(δ, Δω) = (δ, p / M)` (`Dynamics.scaleCoord`), input and output
  unchanged.

Family and connection conclusions.
* `SwingPort.family : Family Model ClassicalSM.Requirement 2 1`: every model read as its centred
  port system, with the classical machine's requirement language read through
  `Model.toClassicalSM`: `locked` is the power balance `A sin(δ* − α) = P_ref − c₀`,
  `stableBranch` a positive synchronizing coefficient `K = A cos(δ* − α) > 0`, `damped` adds
  `D > 0`, `unstableBranch` is `K < 0`, `noPower` the matched set-point `P_ref = c₀`; the
  translation is the machine's.
* The reading (M–M): `SwingPort.mem_den_iff_classicalSM` — a model satisfies a sentence exactly
  when its machine does, for every sentence: the flow sentences by the conjugacy of the zero-input
  fields (`Spectral.mem_den_flow_iff_of_transport`), passivity by the invariance of passivity
  under the coordinate change (`Port.System.passive_conjugate_iff`), the envelope sentences
  trivially. Hence `SwingPort.chain_le_semantics` (every translation is sound, from
  `Synchronous.ClassicalSM.chain_le_semantics`), `SwingPort.exact_passive` (the passivity
  translation is exact, from `Synchronous.ClassicalSM.exact_passive`) and the member law
  `SwingPort.mem_den_passive_iff` (passive exactly when `P_ref = c₀`: with `P_ref ≠ c₀` the
  energy `p²/(2M) − (P_ref − c₀) δ − A cos(δ − α)` is unbounded below and a slow spin draws
  unbounded energy).
* `SwingPort.eulerFamily` (every discretization read as the Euler discretization of its model's
  port system) and `SwingPort.euler` (`Implementation.ofDesign`). The Euler reading (I–I):
  `SwingPort.euler_mem_den_passive_iff_classicalSM` — a discretization is passive exactly when
  the discretization of its machine with the same step is (`Numerics.eulerSystem_conjugate`,
  `Map.System.passive_conjugate_iff`). Through it the machine's law
  `Synchronous.ClassicalSM.euler_not_mem_den_passive` gives `SwingPort.euler_not_mem_den_passive`:
  no discretization is passive, whatever its step (the output `Δω` does not see the input of the
  step).
* M–I: `SwingPort.not_euler_realizationSoundUnder_passive` — the passivity realization of explicit
  Euler is not sound: a matched model (`P_ref = c₀`) is passive and none of its discretizations
  is.
-/

noncomputable section

namespace powerlib.GFM.SwingPort

open powerlib.Dynamics (State)
open powerlib.Synchronous
open powerlib.PH (NonlinearModel)

/-- Parameters of the two-state GFM swing synchronization with a power port: inertia `M > 0`,
damping `D ≥ 0`, the power characteristic `P(δ) = c₀ + A sin(δ − α)` with `A > 0`, and the
active-power set-point `P_ref`. -/
structure Params where
  M : ℝ
  D : ℝ
  c0 : ℝ
  A : ℝ
  α : ℝ
  Pref : ℝ
  M_pos : 0 < M
  D_nonneg : 0 ≤ D
  A_pos : 0 < A

attribute [powerlib_domain] Params.M_pos Params.D_nonneg Params.A_pos

namespace Params

variable (g : Params)

/-- The export-positive active power of the quasi-static line, `P(δ) = c₀ + A sin(δ − α)`. -/
def power (δ : ℝ) : ℝ := g.c0 + g.A * Real.sin (δ - g.α)

/-- The swing law with the set-point port: `δ̇ = Δω`, `M Δω̇ = P_ref + u − P(δ) − D Δω`. -/
def field (x : State 2) (u : Fin 1 → ℝ) : State 2 :=
  WithLp.toLp 2 ![x 1, (g.Pref + u 0 - g.power (x 0) - g.D * x 1) / g.M]

end Params

/-- A model: a parameter set with a selected angle `δ*`. -/
structure Model where
  /-- The parameters. -/
  p : Params
  /-- The selected angle `δ*`. -/
  δs : ℝ

/-- The selected point `(δ*, 0)`. -/
def Model.point (m : Model) : State 2 := WithLp.toLp 2 ![m.δs, 0]

/-- The port system in the coordinates `z = x − (δ*, 0)`: the field translated to the selected
point, output the frequency deviation `Δω = z₁`. -/
def Model.system (m : Model) : Port.System 2 1 :=
  ⟨fun z u => m.p.field (z + m.point) u, fun z _ => ![z 1]⟩

/-- The classical machine of a model: mechanical power `P_ref − c₀`, bus coefficient `A`, rotor
angle `δ − α`, selected angle `δ* − α`. -/
def Model.toClassicalSM (m : Model) : ClassicalSM.Model :=
  ⟨⟨m.p.M, m.p.D, m.p.A, m.p.Pref - m.p.c0, m.p.M_pos, m.p.D_nonneg, m.p.A_pos⟩, m.δs - m.p.α⟩

/-- The momentum coordinates `(δ, Δω) ↦ (δ, M Δω)`. -/
abbrev Model.momentum (m : Model) : State 2 ≃L[ℝ] State 2 := Dynamics.scaleCoord m.p.M_pos.ne'

@[tmio M, powerlib_domain] private theorem Model.momentum_symm (m : Model) (x : State 2) :
    (m.momentum : State 2 →L[ℝ] State 2) ((m.momentum.symm : State 2 →L[ℝ] State 2) x) = x := by
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

@[tmio M, powerlib_domain] private theorem Model.symm_momentum (m : Model) (x : State 2) :
    (m.momentum.symm : State 2 →L[ℝ] State 2) ((m.momentum : State 2 →L[ℝ] State 2) x) = x := by
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

/-- **The GFM swing port is the classical machine in other coordinates.** The centred port system
is the classical machine's centred pH port system conjugated by the momentum coordinates
`p = M Δω`: the field is `T⁻¹ f(T z, u)`, the output `ω = p / M` read at `T z` is `Δω`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem system_eq_conjugate (m : Model) :
    m.system = m.toClassicalSM.toPH.system.conjugate
      (m.momentum.symm : State 2 →L[ℝ] State 2) (m.momentum : State 2 →L[ℝ] State 2) := by
  have hM := m.p.M_pos.ne'
  simp only [Model.system, Port.System.conjugate]
  congr 1
  · funext z u
    apply WithLp.ofLp_injective 2
    rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe,
      Dynamics.scaleCoord_symm_apply]
    simp only [NonlinearModel.system_field, ClassicalSM.Model.toPH, NonlinearModel.shift_field]
    have hf := classicalSM_field m.toClassicalSM.p (m.momentum z + m.toClassicalSM.point) u
    ext i
    fin_cases i
    · have h0 := congrFun hf 0
      simp [Model.toClassicalSM, ClassicalSM.Model.point, classicalSM_equilibrium, Model.point,
        Params.field] at h0 ⊢
      rw [h0]
      field_simp
    · have h1 := congrFun hf 1
      simp [Model.toClassicalSM, ClassicalSM.Model.point, classicalSM_equilibrium, Model.point,
        Params.field, Params.power] at h1 ⊢
      rw [h1]
      field_simp
      ring_nf
  · funext z u
    rw [ContinuousLinearEquiv.coe_coe, NonlinearModel.system_output, ClassicalSM.Model.toPH,
      NonlinearModel.shift_output]
    funext i
    fin_cases i
    simp [NonlinearModel.output, classicalSM, classicalSM_dH, Matrix.mulVec, dotProduct,
      Model.toClassicalSM, ClassicalSM.Model.point, classicalSM_equilibrium]
    field_simp

/-- Static requirements: the classical machine's, read through `Model.toClassicalSM`. -/
def family : Family Model ClassicalSM.Requirement 2 1 :=
  ⟨fun m => m.system, fun m => ClassicalSM.Meets m.toClassicalSM, ClassicalSM.translate⟩

@[tmio M, powerlib_domain] theorem family_isPort : family.IsPort Model.system := fun _ => rfl

@[tmio M, powerlib_domain] private theorem classicalSM_isPort :
    ClassicalSM.family.IsPort fun c => c.toPH.system := fun _ => rfl

/-- **Reading through the classical machine.** A GFM swing model satisfies a sentence exactly when
its classical machine does: the flow sentences by the conjugacy of the zero-input fields in the
momentum coordinates, passivity by its invariance under that change of coordinates (input and
supplied power unchanged), the envelope sentences trivially. -/
@[tmio TM, powerlib_domain] theorem mem_den_iff_classicalSM (m : Model) (s : Sentence) :
    connection% (m ∈ family.den s ↔ m.toClassicalSM ∈ ClassicalSM.family.den s) := by
  unfold powerlib.TMIO.Statement
  have hsys := system_eq_conjugate m
  rcases s with P | _ | E
  · refine Spectral.mem_den_flow_iff_of_transport (F := family) (G := ClassicalSM.family)
      (f := fun m => m.system.zeroInput) (pt := fun _ => 0)
      (φ := fun c => c.toPH.system.zeroInput) (ψ := fun _ => 0)
      (fun x P => (connection_proof% family_isPort.mem_den_flow))
      (fun y P => (connection_proof% classicalSM_isPort.mem_den_flow))
      (g := Model.toClassicalSM) m.momentum.symm 0 ?_ ?_ P
    · funext z
      change m.system.field z 0 = _
      rw [hsys]
      simp [Port.System.conjugate, Port.System.zeroInput, Dynamics.transportField]
    · simp only [Dynamics.affineCoord, map_zero, add_zero]
  · rw [(connection_proof% family_isPort.mem_den_passive_iff),
      (connection_proof% classicalSM_isPort.mem_den_passive_iff), hsys]
    exact Port.System.passive_conjugate_iff _
      m.momentum_symm
      m.symm_momentum
  · rw [(connection_proof% family_isPort.den_envelope),
      (connection_proof% classicalSM_isPort.den_envelope)]
    exact iff_of_true trivial trivial

@[tmio M, powerlib_domain] private theorem mem_realize_iff {m : Model}
    {Γ : Set ClassicalSM.Requirement} :
    m ∈ TMIO.realize family.meets Γ ↔
      m.toClassicalSM ∈ TMIO.realize ClassicalSM.family.meets Γ := by
  rw [show family.meets = fun m q => ClassicalSM.family.meets m.toClassicalSM q from rfl,
    (connection_proof% TMIO.realize_comap)]
  rfl

/-- Every translation of the GFM swing family is sound: the machine's translations are sound
(`Synchronous.ClassicalSM.chain_le_semantics`) and the two families agree on every sentence and
requirement (`mem_den_iff_classicalSM`). -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  have hs := ClassicalSM.chain_le_semantics
  unfold powerlib.TMIO.Statement at hs ⊢
  refine (connection_proof% Family.chain_le_semantics_iff).mpr fun s => ?_
  have hs' : ClassicalSM.family.Sound s := (connection_proof% Family.chain_le_semantics_iff).mp hs s
  exact (connection_proof% Spectral.realize_subset_den_of_hub Model.toClassicalSM
    (fun x hx => mem_realize_iff.mp hx)
    (fun x _ hx => (connection_proof% (mem_den_iff_classicalSM x s)).mpr hx) hs')

/-- **The passivity translation is exact**: a GFM swing model is passive exactly when its
set-point is matched, `P_ref = c₀` (from `Synchronous.ClassicalSM.exact_passive`). -/
@[tmio TM, powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  have he := ClassicalSM.exact_passive
  unfold powerlib.TMIO.Statement at he ⊢
  exact (connection_proof% Spectral.exact_of_hub (ΔG := ∅) Model.toClassicalSM
    (fun x => by rw [(connection_proof% TMIO.realize_empty)]; trivial)
    (fun x => (connection_proof% (mem_den_iff_classicalSM x .passive)))
    (fun x => mem_realize_iff)
    ((connection_proof% Family.exactUnder_empty_iff).mpr he))

/-- **Passivity of the GFM swing port.** A model is passive exactly when its set-point equals the
line's constant power, `P_ref = c₀` (`exact_passive`): with `P_ref ≠ c₀` a slow spin held by the
port draws unbounded energy. -/
@[tmio TM, powerlib_domain] theorem mem_den_passive_iff (m : Model) :
    connection% (m ∈ family.den .passive ↔ m.p.Pref = m.p.c0) := by
  have he := exact_passive
  unfold powerlib.TMIO.Statement at he ⊢
  rw [← he, (connection_proof% TMIO.mem_realize)]
  change (∀ q ∈ ({.noPower} : Set ClassicalSM.Requirement), ClassicalSM.Meets _ q) ↔ _
  simp [ClassicalSM.Meets, Model.toClassicalSM, sub_eq_zero]

/-! ## The explicit Euler discretization -/

/-- The explicit Euler discretization of a GFM swing model with step `h > 0`. -/
abbrev Euler := Numerics.EulerStep Model

/-- The Euler discretization family: every discretization read as the Euler discretization of its
model's port system, with step length its step. -/
def eulerFamily : Family Euler ClassicalSM.Requirement 2 1 :=
  Numerics.eulerPortFamily family Model.system Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every discretization realizes its model. -/
def euler : Implementation Model ClassicalSM.Requirement Euler ClassicalSM.Requirement 2 1 2 1 :=
  Numerics.eulerPorts family Model.system Numerics.EulerStep.design Numerics.EulerStep.h

/-- **The Euler discretizations read through the classical machine.** A discretization is passive
exactly when the discretization of its machine with the same step is: the Euler step commutes
with the momentum coordinates (`Numerics.eulerSystem_conjugate`) and passivity of a discrete-time
system is invariant under them (`Map.System.passive_conjugate_iff`). -/
@[tmio TM, powerlib_domain] theorem euler_mem_den_passive_iff_classicalSM (m : Model) (h : ℝ)
    (hh : 0 < h) :
    connection% ((⟨m, h, hh⟩ : Euler) ∈ eulerFamily.den .passive ↔
      (⟨m.toClassicalSM, h, hh⟩ : ClassicalSM.Euler) ∈ ClassicalSM.eulerFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% Family.mem_den), (connection_proof% Family.mem_den)]
  change (Numerics.eulerSystem m.system h).Passive ↔
    (Numerics.eulerSystem m.toClassicalSM.toPH.system h).Passive
  rw [system_eq_conjugate m, Numerics.eulerSystem_conjugate _ _ _
    m.symm_momentum h]
  exact Map.System.passive_conjugate_iff _
    m.momentum_symm
    m.symm_momentum

/-- **No Euler discretization of a GFM swing model is passive, whatever its step**: the classical
machine's law `Synchronous.ClassicalSM.euler_not_mem_den_passive` read through
`euler_mem_den_passive_iff_classicalSM`. -/
@[tmio TM, powerlib_domain] theorem euler_not_mem_den_passive :
    connection% (∀ (m : Model) (h : ℝ) (hh : 0 < h),
      (⟨m, h, hh⟩ : Euler) ∉ eulerFamily.den .passive) := by
  have hc := ClassicalSM.euler_not_mem_den_passive
  unfold powerlib.TMIO.Statement at hc ⊢
  intro m h hh hp
  exact hc m.toClassicalSM h hh
    ((connection_proof% (euler_mem_den_passive_iff_classicalSM m h hh)).mp hp)

/-- The matched model `M = D = A = 1`, `c₀ = α = P_ref = 0`, `δ* = 0`. -/
private def matchedModel : Model := ⟨⟨1, 1, 0, 1, 0, 0, one_pos, zero_le_one, one_pos⟩, 0⟩

/-- **The passivity realization of explicit Euler is not sound for the GFM swing.** The matched
model is passive (`mem_den_passive_iff`) and none of its discretizations is
(`euler_not_mem_den_passive`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder_passive :
    connection% (¬ euler.RealizationSoundUnder ∅ .passive) := by
  have hm := (mem_den_passive_iff matchedModel)
  have hn := euler_not_mem_den_passive
  unfold powerlib.TMIO.Statement at hm hn ⊢
  exact (connection_proof% Implementation.not_realizationSoundUnder_of_design (I := euler)
    (y := (⟨matchedModel, 1, one_pos⟩ : Euler)) rfl (hm.mpr rfl)
    (by rw [(connection_proof% TMIO.realize_empty)]; trivial) (hn matchedModel 1 one_pos))

end powerlib.GFM.SwingPort
