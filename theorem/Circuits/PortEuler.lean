import theorem.Circuits.LCL
import theorem.Numerics.EulerPorts

/-! # The explicit Euler discretization of the RL branch and the LCL filter: realizations

The circuit families `Circuits.RL.family` and `Circuits.LCL.family` discretized by the explicit
Euler method with a fixed step `h > 0`, with their ports: each discretization realizes the circuit
it is designed from. Both families are linear (`family_isLinear`), so the linear laws of the
generic template `theorem/Numerics/EulerPorts.lean` apply: the Euler zero-input map is `I + hA`,
the attractive sentences and sampled contraction are realized completely at every step and
exactly below a step threshold, and not soundly without a step constraint. Passivity is not
realized at any step: both circuits read their port currents, which do not depend on the port
voltages (`D = 0`), so one Euler step with a large voltage draws energy without bound.
Scaffold: `theorem/EulerPorts.agda`.

Model boundary.
* Model layer (M): `Circuits.RL.family` (one series RL branch `L i' = v − R i`, port voltage `v`,
  port current `i`, `theorem/Circuits/RL.lean`) and `Circuits.LCL.family` (converter branch,
  shunt capacitor, grid branch; ports: converter voltage with current `i₁`, grid voltage with
  current `−i₂`, `theorem/Circuits/LCL.lean`), continuous time, read about the origin, with their
  requirement languages and translations.
* Implementation layer (I): for each family a structure `Euler` (in `Circuits.RL` and
  `Circuits.LCL`) of a circuit and a step `h > 0`; the system is the explicit Euler discretization
  `x⁺ = x + h (A x + B u)`, output `y = C x` (the input held over the step), step length `h`,
  discrete time, exact arithmetic, fixed step. Excluded: step-size control, implicit or
  higher-order schemes, the integration error against the continuous trajectory.
* Level: the attractive sentences and sampled contraction of the zero-input dynamics about the
  origin; passivity of the discretized port system.

Source: `theorem/Numerics/EulerPorts.lean` (`eulerPorts_exact_small_step_linear`,
`eulerPorts_realizationCompleteUnder_linear`,
`not_eulerPorts_realizationSoundUnder_of_large_step_linear`,
`eulerPortFamily_not_mem_den_passive`, `not_eulerPorts_realizationSoundUnder_passive`) and the
circuit modules (linearity, Hurwitz criteria, KYP certificates); work-sync
`theory/T-numerical-integration.md` §1.2, §2.7.

Results.
* No static result beyond the family definitions.

Family and connection conclusions.
* For `N` = `Circuits.RL` and `Circuits.LCL`: `N.eulerFamily` (every discretization read as the
  Euler discretization of its circuit's port system, with the requirements and translation of its
  circuit read through the design) and `N.euler` (every discretization realizing its circuit,
  `Implementation.ofDesign`).
* M–I (realization), for each family and every attractive sentence or sampled contraction `P`.
  The small-step and completeness laws are the generic connection laws for linear families
  applied to the family's linearity `N.family_isLinear`:
  `Numerics.eulerPorts_exact_small_step_linear` (scaffold `sound-small-step`, with completeness:
  every circuit has a step `h₀ > 0` below which its discretizations satisfy `P` exactly when the
  circuit does) and `Numerics.eulerPorts_realizationCompleteUnder_linear` (with `Euler.pos`: at
  every step a discretization satisfying `P` realizes only circuits satisfying it, within every
  requirement context). `N.not_euler_realizationSoundUnder`
  (scaffold `not-sound-large-step`): without a step constraint the realization is not sound (RL:
  `R = L = 1`; LCL: all parameters `1`, passive and damped, hence pole stable).
* Passivity: `N.euler_not_mem_den_passive`: no discretization is passive, whatever its step (the
  port current at a unit state is `1` whatever the input);
  `N.not_euler_realizationSoundUnder_passive`: the passivity realization is not sound (the passive
  circuit with all parameters `1`).
-/

noncomputable section

open LinearSystems

namespace powerlib.Circuits.RL

/-- The explicit Euler discretization of an RL branch with step `h > 0`. -/
structure Euler where
  /-- The discretized branch. -/
  design : Impedance
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler discretization family: every discretization read as the Euler discretization of
its branch's port system, with step length its step. -/
def eulerFamily : Family Euler Requirement 1 1 :=
  Numerics.eulerPortFamily family (fun m => m.plant.system) Euler.design Euler.h

/-- The Euler realization: every discretization realizes its branch. -/
def euler : Implementation Impedance Requirement Euler Requirement 1 1 1 1 :=
  Numerics.eulerPorts family (fun m => m.plant.system) Euler.design Euler.h

/-- The branch with `R = L = 1`. -/
private def unitBranch : Impedance := ⟨1, ⟨1, one_pos⟩⟩

/-- **Without a step constraint the Euler realization of the RL branch is not sound.** The branch
`R = L = 1` (`ẋ = −x`) satisfies every attractive sentence, and its discretizations with a large
step do not (the multiplier `1 − h` leaves the unit disk). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact Numerics.not_eulerPorts_realizationSoundUnder_of_large_step_linear family_isLinear
    one_pos hP (x := unitBranch)
    ((family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)).mp
      ((isHurwitz_iff _).mpr one_pos))
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

/-- The port current at the unit state is `1`, whatever the port voltage. -/
@[tmio M] private theorem output_unit (m : Impedance) (u : Fin 1 → ℝ) :
    m.plant.system.output (WithLp.toLp 2 ![1]) u = ![1] := by
  funext i
  fin_cases i
  simp [Impedance.plant, StateSpace.plant, Linear.Plant.system]

/-- **No Euler discretization of an RL branch is passive, whatever its step.** The port current
does not depend on the port voltage, so one step from the unit current with a large reverse
voltage draws energy without bound; no nonnegative storage pays for it. -/
@[tmio TM, powerlib_domain] theorem euler_not_mem_den_passive :
    connection% (∀ (m : Impedance) (h : ℝ) (hh : 0 < h),
      (⟨m, h, hh⟩ : Euler) ∉ eulerFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  intro m h hh
  exact Numerics.eulerPortFamily_not_mem_den_passive (design := Euler.design) (step := Euler.h)
    (y := ⟨m, h, hh⟩) hh (output_unit m) (by simp)

/-- **The passivity realization of explicit Euler is not sound for the RL branch.** The branch
`R = L = 1` is passive (storage `L i²/2`), and its discretizations are not. -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder_passive :
    connection% (¬ euler.RealizationSoundUnder ∅ .passive) := by
  unfold powerlib.TMIO.Statement
  exact Numerics.not_eulerPorts_realizationSoundUnder_passive (y := ⟨unitBranch, 1, one_pos⟩)
    (family_isLinear.mem_den_passive (kyp _ zero_le_one)) (by rw [TMIO.realize_empty]; trivial)
    one_pos (output_unit _) (by simp)

end powerlib.Circuits.RL

namespace powerlib.Circuits.LCL

/-- The explicit Euler discretization of an LCL filter with step `h > 0`. -/
structure Euler where
  /-- The discretized circuit. -/
  design : Circuit
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler discretization family: every discretization read as the Euler discretization of
its circuit's port system, with step length its step. -/
def eulerFamily : Family Euler Requirement 3 2 :=
  Numerics.eulerPortFamily family (fun m => m.plant.system) Euler.design Euler.h

/-- The Euler realization: every discretization realizes its circuit. -/
def euler : Implementation Circuit Requirement Euler Requirement 3 2 3 2 :=
  Numerics.eulerPorts family (fun m => m.plant.system) Euler.design Euler.h

/-- The circuit with all parameters `1`: passive and damped. -/
private def unitCircuit : Circuit := ⟨⟨1, ⟨1, one_pos⟩⟩, ⟨1, ⟨1, one_pos⟩⟩, ⟨1, one_pos⟩⟩

@[tmio M] private theorem unitCircuit_passive : unitCircuit.Passive := ⟨zero_le_one, zero_le_one⟩

/-- **Without a step constraint the Euler realization of the LCL filter is not sound.** The
circuit with all parameters `1` is passive and damped, hence pole stable, and its discretizations
with a large step are not stable. -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow P)) := by
  unfold powerlib.TMIO.Statement
  have hA : IsHurwitz unitCircuit.plant.A := by
    apply (family_isLinear.mem_den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)).mp
    apply (isHurwitz_iff_stable _).mpr
    apply (passive_stable_iff _ unitCircuit_passive).mpr
    simpa only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, Meets] using
      (show unitCircuit.Damped from Or.inl one_ne_zero)
  exact Numerics.not_eulerPorts_realizationSoundUnder_of_large_step_linear family_isLinear
    (by norm_num) hP (x := unitCircuit) hA
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

/-- The port currents at the unit converter current are `(1, 0)`, whatever the port voltages. -/
@[tmio M] private theorem output_unit (m : Circuit) (u : Fin 2 → ℝ) :
    m.plant.system.output (WithLp.toLp 2 ![1, 0, 0]) u = ![1, 0] := by
  funext i
  fin_cases i <;>
    simp [Circuit.plant, StateSpace.plant, Linear.Plant.system, dotProduct,
      Fin.sum_univ_three]

/-- **No Euler discretization of an LCL filter is passive, whatever its step.** The port currents
do not depend on the port voltages, so one step from a unit converter current with a large
reverse converter voltage draws energy without bound. -/
@[tmio TM, powerlib_domain] theorem euler_not_mem_den_passive :
    connection% (∀ (m : Circuit) (h : ℝ) (hh : 0 < h),
      (⟨m, h, hh⟩ : Euler) ∉ eulerFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  intro m h hh
  exact Numerics.eulerPortFamily_not_mem_den_passive (design := Euler.design) (step := Euler.h)
    (y := ⟨m, h, hh⟩) hh (output_unit m) (by simp)

/-- **The passivity realization of explicit Euler is not sound for the LCL filter.** The circuit
with all parameters `1` is passive (its physical energy), and its discretizations are not. -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder_passive :
    connection% (¬ euler.RealizationSoundUnder ∅ .passive) := by
  unfold powerlib.TMIO.Statement
  exact Numerics.not_eulerPorts_realizationSoundUnder_passive (y := ⟨unitCircuit, 1, one_pos⟩)
    (family_isLinear.mem_den_passive (kyp _ unitCircuit_passive))
    (by rw [TMIO.realize_empty]; trivial) one_pos (output_unit _) (by simp)

end powerlib.Circuits.LCL
