import theorem.Synchronous.PH
import theorem.Synchronous.SMIB11PH
import theorem.Numerics.EulerPorts

/-! # The explicit Euler discretization of the port-Hamiltonian machine families

The port-Hamiltonian families of synchronous machines with their ports — the classical machine on
an infinite bus (`ClassicalSM.family`), the seven-state dq machine (`SyncMachine7.family`) and the
11-state single-machine infinite-bus system in the note's and the corrected form
(`SMIB11.family`, `SMIB11Rel.family`) — discretized by the explicit Euler method with a fixed step
`h > 0`, with their ports: each discretization realizes the model it is designed from; the
generic template is `theorem/Numerics/EulerPorts.lean`. For the classical machine the
flow-sentence laws apply (its zero-input field is smooth): local exponential stability is
realized below a step threshold and not without a step constraint. The seven-state and 11-state
families have no locally exponentially stable member, so their realization of local exponential
stability is sound, vacuously, without a step constraint. For every family the
passivity realization is not sound: the collocated outputs `gᵀ ∇H(x)` (speed, currents) do not
depend on the input, so one Euler step with a large input draws energy without bound, while the
continuous models are passive. Scaffold: `theorem/EulerPorts.agda`.

Model boundary.
* Model layer (M), each family with the model boundary of its module
  (`theorem/Synchronous/PH.lean`, `theorem/Synchronous/SMIB11PH.lean`): `ClassicalSM.family`
  (state `(δ, p)` centred at `(δ*, 0)`, mechanical-power port, output `ω`);
  `SyncMachine7.family` (seven states, ports `(v_d, v_q, v_f, T_m)`, outputs
  `(i_d, i_q, i_f, ω_r)`, at the origin); `SMIB11.family` and `SMIB11Rel.family` (eleven states,
  ports `(v_f, T_m, V_D^∞, V_Q^∞)`, outputs `(i_f, ω_r, −I_D, −I_Q)`, at the origin); continuous
  time.
* Implementation layer (I): for each family a structure `Euler` (in its namespace) of a model and
  a step `h > 0`; the system is the explicit Euler discretization `x⁺ = x + h f(x, u)` of the
  model's port system with the same output (the input held over the step), step length `h`,
  discrete time, exact arithmetic, fixed step. Excluded: step-size control, implicit, symplectic
  or discrete-gradient schemes, the integration error against the continuous trajectory.
* Level: local exponential stability of the zero-input dynamics about the origin; passivity of
  the discretized port system.
* The seven-state and 11-state families have no locally exponentially stable member, whatever
  the parameters (`SyncMachine7.not_mem_den_locallyExponentiallyStable`,
  `SMIB11.not_mem_den_locallyExponentiallyStable`,
  `SMIB11Rel.not_mem_den_locallyExponentiallyStable`, in the family modules): the Jacobian at
  the origin kills the rotor-angle direction `e_δ` (`∂H/∂δ = 0` and `∇H(0) = 0`; the frame
  drift of the corrected model is constant), while a locally exponentially stable point has an
  injective Jacobian (converse linearization). For the corrected model with `ω_s ≠ 0` the
  origin is not even an equilibrium (`SMIB11Rel.mem_den_unstable`). So the small-step law holds
  vacuously and is not stated.

Source: `theorem/Numerics/EulerPorts.lean` (`eulerPorts_sound_small_step_local`,
`not_eulerPorts_realizationSoundUnder_of_large_step_local`,
`eulerPortFamily_not_mem_den_passive`, `not_eulerPorts_realizationSoundUnder_passive`,
`Family.IsNonlinearPH.isPort`), `theorem/Numerics/EulerRealization.lean` (`contDiff_shift`),
`theorem/PH/Linearization.lean` (`NonlinearModel.contDiff_zeroInputField`),
`theorem/Stack/Implementation.lean` (`Implementation.certify_realizes_of_design`) and the family
modules (members, passivity, no locally exponentially stable member); work-sync
`theory/T-numerical-integration.md` §1.2, §2.7, `theory/T-ph.md` §2.5.

Results.
* `ClassicalSM.contDiffAt_zeroInput`: the centred zero-input field of the classical machine is
  `C¹` near the origin, the smoothness hypothesis of the generic laws.

Family and connection conclusions.
* For `N` = `ClassicalSM`, `SyncMachine7`, `SMIB11`, `SMIB11Rel`: `N.eulerFamily` (every
  discretization read as the Euler discretization of its model's port system, with the
  requirements and translation of its model read through the design) and `N.euler` (every
  discretization realizing its model, `Implementation.ofDesign`).
* M–I, classical machine. The small-step law is the generic connection law applied to the
  family, with its port structure `ClassicalSM.family_isNonlinearPH.isPort` and the public
  smoothness lemma `ClassicalSM.contDiffAt_zeroInput`: `Numerics.eulerPorts_sound_small_step_local`
  (scaffold `sound-small-step`: a locally exponentially stable model has a step `h₀ > 0` below
  which its discretizations are locally exponentially stable).
  `ClassicalSM.not_euler_realizationSoundUnder` (scaffold
  `not-sound-large-step`): without a step constraint the realization is not sound
  (`M = D = b = 1`, `P_m = 0`, `δ* = 0`).
* M–I, seven-state and 11-state families, for `N` = `SyncMachine7`, `SMIB11`, `SMIB11Rel`:
  `N.euler_realizationSoundUnder`: without a step constraint the realization of local
  exponential stability is sound, vacuously — no model is locally exponentially stable
  (`N.not_mem_den_locallyExponentiallyStable`), so no discretization is certified for it.
* M–I, passivity, for each `N`: `N.euler_not_mem_den_passive`: no discretization is passive,
  whatever its step; `N.not_euler_realizationSoundUnder_passive`: the passivity realization is not
  sound (classical machine: `M = D = b = 1`, `P_m = 0`, passive; the other families: every member
  is passive, `Γ = I`, `M = C = L_l = 1`, zero resistances).
-/

noncomputable section

open powerlib.Dynamics (State)
open powerlib.PH

namespace powerlib.Synchronous.ClassicalSM

/-- The explicit Euler discretization of a classical-machine model with step `h > 0`. -/
structure Euler where
  /-- The discretized model. -/
  design : Model
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler discretization family: every discretization read as the Euler discretization of its
model's centred pH port system, with step length its step. -/
def eulerFamily : Family Euler Requirement 2 1 :=
  Numerics.eulerPortFamily family (fun m => m.toPH.system) Euler.design Euler.h

/-- The Euler realization: every discretization realizes its model. -/
def euler : Implementation Model Requirement Euler Requirement 2 1 2 1 :=
  Numerics.eulerPorts family (fun m => m.toPH.system) Euler.design Euler.h

private theorem family_isPort : family.IsPort fun m => m.toPH.system :=
  family_isNonlinearPH.isPort

/-- The centred zero-input field of a classical machine is `C¹` near the origin: the smoothness
hypothesis of the generic Euler laws for port systems
(`Numerics.eulerPorts_sound_small_step_local`). -/
@[powerlib_foundation] theorem contDiffAt_zeroInput (m : Model) :
    ContDiffAt ℝ 1 m.toPH.system.zeroInput 0 :=
  Numerics.contDiffAt_shift (g := (classicalSM m.p).zeroInputField) (x₀ := m.point)
    ((classicalSM m.p).contDiff_zeroInputField (fun _ _ => contDiff_const)
      (fun _ _ => contDiff_const) (classicalSM_contDiff_dH m.p)).contDiffAt

/-- The model `M = D = b = 1`, `P_m = 0`, `δ* = 0`. -/
private def unitModel : Model := ⟨⟨1, 1, 1, 0, one_pos, zero_le_one, one_pos⟩, 0⟩

/-- The speed output at the centred state `(0, 1)` is `1/M`. -/
private theorem output_unit (m : Model) :
    m.toPH.output (WithLp.toLp 2 ![0, 1]) = ![1 / m.p.M] := by
  rw [Model.toPH, NonlinearModel.shift_output]
  funext i
  fin_cases i
  simp [Model.point, classicalSM_equilibrium, NonlinearModel.output, classicalSM, classicalSM_dH,
    Matrix.mulVec, dotProduct]

private theorem output_unit_ne_zero (m : Model) : ![1 / m.p.M] ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [m.p.M_pos.ne'] at this

/-- **Without a step constraint the Euler realization of the classical machine is not sound.**
The damped machine `M = D = b = 1`, `P_m = 0` at `δ* = 0` is locally exponentially stable, and its
discretizations with a large step are not: every Euler multiplier `1 + hλ` leaves the unit
disk. -/
@[powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := mem_den_locallyExponentiallyStable unitModel (by norm_num [unitModel])
    (by simp [unitModel]) (by simp [unitModel])
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerPorts_realizationSoundUnder_of_large_step_local family_isPort
    (by norm_num) (contDiffAt_zeroInput _) hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

/-- **No Euler discretization of a classical machine is passive, whatever its step.** The speed
output does not depend on the mechanical-power input, so one step from a unit momentum deviation
with a large braking input draws energy without bound. -/
@[powerlib_domain] theorem euler_not_mem_den_passive :
    connection% (∀ (m : Model) (h : ℝ) (hh : 0 < h),
      (⟨m, h, hh⟩ : Euler) ∉ eulerFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  intro m h hh
  exact Numerics.eulerPortFamily_not_mem_den_passive (design := Euler.design) (step := Euler.h)
    (y := ⟨m, h, hh⟩) hh (fun _ => output_unit m) (output_unit_ne_zero m)

/-- **The passivity realization of explicit Euler is not sound for the classical machine.** The
machine without mechanical power (`M = D = b = 1`) is passive, and its discretizations are
not. -/
@[powerlib_domain] theorem not_euler_realizationSoundUnder_passive :
    connection% (¬ euler.RealizationSoundUnder ∅ .passive) := by
  unfold powerlib.TMIO.Statement
  have hm := mem_den_passive_of_Pm_zero unitModel rfl
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerPorts_realizationSoundUnder_passive (y := ⟨unitModel, 1, one_pos⟩) hm
    (by rw [TMIO.realize_empty]; trivial) one_pos (fun _ => output_unit _)
    (output_unit_ne_zero _)

end powerlib.Synchronous.ClassicalSM

namespace powerlib.Synchronous

/-- Vacuous soundness: when no model of a family of port systems is locally exponentially stable,
no Euler implementation is certified for it, so the realization is sound without a step
constraint. -/
private theorem eulerPorts_realizationSoundUnder_of_not_mem {X Y Q : Type} {n p : ℕ}
    {F : Family X Q n p} {sys : X → Port.System n p} {design : Y → X} {step : Y → ℝ}
    (h : ∀ x, x ∉ F.den (.flow .locallyExponentiallyStable)) :
    (Numerics.eulerPorts F sys design step).RealizationSoundUnder ∅
      (.flow .locallyExponentiallyStable) := by
  rintro y ⟨hy, -⟩
  rw [Implementation.certify_realizes_of_design (I := Numerics.eulerPorts F sys design step) rfl]
    at hy
  exact absurd hy (h _)

end powerlib.Synchronous

namespace powerlib.Synchronous.SyncMachine7

/-- The explicit Euler discretization of a seven-state machine with step `h > 0`. -/
structure Euler where
  /-- The discretized machine. -/
  design : SyncMachine7Params
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler discretization family: every discretization read as the Euler discretization of its
machine's pH port system, with step length its step. -/
def eulerFamily : Family Euler Requirement 7 4 :=
  Numerics.eulerPortFamily family (fun p => (syncMachine7 p).system) Euler.design Euler.h

/-- The Euler realization: every discretization realizes its machine. -/
def euler : Implementation SyncMachine7Params Requirement Euler Requirement 7 4 7 4 :=
  Numerics.eulerPorts family (fun p => (syncMachine7 p).system) Euler.design Euler.h

/-- **The Euler realization of the seven-state machine is sound without a step constraint,
vacuously.** No machine is locally exponentially stable at the origin
(`not_mem_den_locallyExponentiallyStable`: the rotor angle is a direction killed by the
Jacobian), so no discretization is certified for local exponential stability, whatever its step;
the family has no step threshold to state. -/
@[powerlib_domain] theorem euler_realizationSoundUnder :
    connection% (euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine eulerPorts_realizationSoundUnder_of_not_mem fun p => ?_
  have hn := not_mem_den_locallyExponentiallyStable p
  unfold powerlib.TMIO.Statement at hn
  exact hn

/-- The output at the unit momentum has the speed component `1/M`. -/
private theorem output_ne_zero (p : SyncMachine7Params) :
    (syncMachine7 p).output (WithLp.toLp 2 ![0, 0, 0, 0, 0, 1, 0]) ≠ 0 := by
  intro h
  have h3 := congrFun h 3
  simp only [NonlinearModel.output] at h3
  rw [syncMachine7_dH] at h3
  simp [syncMachine7, syncMachine7_g, syncMachine7_speed, syncMachine7_current, syncMachine7_flux,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, p.M_pos.ne'] at h3

/-- **No Euler discretization of a seven-state machine is passive, whatever its step.** The
outputs `(i_d, i_q, i_f, ω_r)` do not depend on the inputs, so one step from a unit momentum with
a large braking torque draws energy without bound. -/
@[powerlib_domain] theorem euler_not_mem_den_passive :
    connection% (∀ (p : SyncMachine7Params) (h : ℝ) (hh : 0 < h),
      (⟨p, h, hh⟩ : Euler) ∉ eulerFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  intro p h hh
  exact Numerics.eulerPortFamily_not_mem_den_passive (design := Euler.design) (step := Euler.h)
    (y := ⟨p, h, hh⟩) hh (fun _ => rfl) (output_ne_zero p)

/-- **The passivity realization of explicit Euler is not sound for the seven-state machine.**
Every machine is passive (storage `H ≥ 0`), and no discretization is. -/
@[powerlib_domain] theorem not_euler_realizationSoundUnder_passive :
    connection% (¬ euler.RealizationSoundUnder ∅ .passive) := by
  unfold powerlib.TMIO.Statement
  let p : SyncMachine7Params :=
    ⟨1, 1, 0, 0, 0, 0, 0, Matrix.PosDef.one, one_pos, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  have hm := mem_den_passive p
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerPorts_realizationSoundUnder_passive (y := ⟨p, 1, one_pos⟩) hm
    (by rw [TMIO.realize_empty]; trivial) one_pos (fun _ => rfl) (output_ne_zero p)

end powerlib.Synchronous.SyncMachine7

namespace powerlib.Synchronous

/-- The output of the 11-state system at the unit momentum has the speed component `1/M`. -/
private theorem smib11_output_ne_zero (p : SMIB11Params) :
    (smib11 p).output (WithLp.toLp 2 ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  simp only [NonlinearModel.output] at h1
  rw [smib11_dH] at h1
  simp [smib11, smib11_g, smib11_speed, smib11_current, smib11_flux, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, p.M_pos.ne'] at h1

/-- The 11-state system with `Γ = I`, `M = C = L_l = 1` and zero resistances, damping and
frame speed. -/
private def smib11Unit : SMIB11Params :=
  ⟨1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, Matrix.PosDef.one, one_pos, le_rfl, le_rfl, le_rfl, le_rfl,
    le_rfl, one_pos, one_pos, le_rfl⟩

namespace SMIB11

/-- The explicit Euler discretization of the note's 11-state system with step `h > 0`. -/
structure Euler where
  /-- The discretized system. -/
  design : SMIB11Params
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler discretization family: every discretization read as the Euler discretization of its
pH port system, with step length its step. -/
def eulerFamily : Family Euler Requirement 11 4 :=
  Numerics.eulerPortFamily family (fun p => (smib11 p).system) Euler.design Euler.h

/-- The Euler realization: every discretization realizes its system. -/
def euler : Implementation SMIB11Params Requirement Euler Requirement 11 4 11 4 :=
  Numerics.eulerPorts family (fun p => (smib11 p).system) Euler.design Euler.h

/-- **The Euler realization of the note's 11-state system is sound without a step constraint,
vacuously.** No system is locally exponentially stable at the origin
(`not_mem_den_locallyExponentiallyStable`: the rotor-angle axis is killed by the Jacobian), so
no discretization is certified for local exponential stability, whatever its step. -/
@[powerlib_domain] theorem euler_realizationSoundUnder :
    connection% (euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine eulerPorts_realizationSoundUnder_of_not_mem fun p => ?_
  have hn := not_mem_den_locallyExponentiallyStable p
  unfold powerlib.TMIO.Statement at hn
  exact hn

/-- **No Euler discretization of the note's 11-state system is passive, whatever its step.** The
outputs `(i_f, ω_r, −I_D, −I_Q)` do not depend on the inputs. -/
@[powerlib_domain] theorem euler_not_mem_den_passive :
    connection% (∀ (p : SMIB11Params) (h : ℝ) (hh : 0 < h),
      (⟨p, h, hh⟩ : Euler) ∉ eulerFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  intro p h hh
  exact Numerics.eulerPortFamily_not_mem_den_passive (design := Euler.design) (step := Euler.h)
    (y := ⟨p, h, hh⟩) hh (fun _ => rfl) (smib11_output_ne_zero p)

/-- **The passivity realization of explicit Euler is not sound for the note's 11-state system.**
Every system is passive (storage `H^tot ≥ 0`), and no discretization is. -/
@[powerlib_domain] theorem not_euler_realizationSoundUnder_passive :
    connection% (¬ euler.RealizationSoundUnder ∅ .passive) := by
  unfold powerlib.TMIO.Statement
  have hm := mem_den_passive smib11Unit
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerPorts_realizationSoundUnder_passive (y := ⟨smib11Unit, 1, one_pos⟩) hm
    (by rw [TMIO.realize_empty]; trivial) one_pos (fun _ => rfl) (smib11_output_ne_zero _)

end SMIB11

namespace SMIB11Rel

/-- The explicit Euler discretization of the corrected 11-state system with step `h > 0`. -/
structure Euler where
  /-- The discretized system. -/
  design : SMIB11Params
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler discretization family: every discretization read as the Euler discretization of its
corrected port system, with step length its step. -/
def eulerFamily : Family Euler SMIB11.Requirement 11 4 :=
  Numerics.eulerPortFamily family smib11Rel_system Euler.design Euler.h

/-- The Euler realization: every discretization realizes its system. -/
def euler : Implementation SMIB11Params SMIB11.Requirement Euler SMIB11.Requirement 11 4 11 4 :=
  Numerics.eulerPorts family smib11Rel_system Euler.design Euler.h

/-- **The Euler realization of the corrected 11-state system is sound without a step
constraint, vacuously.** No system is locally exponentially stable at the origin, whatever `ω_s`
(`not_mem_den_locallyExponentiallyStable`: the constant frame drift leaves the note's Jacobian,
which kills the rotor-angle axis), so no discretization is certified for local exponential
stability, whatever its step. -/
@[powerlib_domain] theorem euler_realizationSoundUnder :
    connection% (euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  refine eulerPorts_realizationSoundUnder_of_not_mem fun p => ?_
  have hn := not_mem_den_locallyExponentiallyStable p
  unfold powerlib.TMIO.Statement at hn
  exact hn

/-- **No Euler discretization of the corrected 11-state system is passive, whatever its step.**
The outputs `(i_f, ω_r, −I_D, −I_Q)` do not depend on the inputs. -/
@[powerlib_domain] theorem euler_not_mem_den_passive :
    connection% (∀ (p : SMIB11Params) (h : ℝ) (hh : 0 < h),
      (⟨p, h, hh⟩ : Euler) ∉ eulerFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  intro p h hh
  exact Numerics.eulerPortFamily_not_mem_den_passive (design := Euler.design) (step := Euler.h)
    (y := ⟨p, h, hh⟩) hh (fun _ => rfl) (smib11_output_ne_zero p)

/-- **The passivity realization of explicit Euler is not sound for the corrected 11-state
system.** Every system is passive (storage `H^tot ≥ 0`; the frame drift does no work), and no
discretization is. -/
@[powerlib_domain] theorem not_euler_realizationSoundUnder_passive :
    connection% (¬ euler.RealizationSoundUnder ∅ .passive) := by
  unfold powerlib.TMIO.Statement
  have hm := mem_den_passive smib11Unit
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerPorts_realizationSoundUnder_passive (y := ⟨smib11Unit, 1, one_pos⟩) hm
    (by rw [TMIO.realize_empty]; trivial) one_pos (fun _ => rfl) (smib11_output_ne_zero _)

end SMIB11Rel

end powerlib.Synchronous
