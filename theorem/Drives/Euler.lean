import theorem.Drives.InductionMachine
import theorem.Numerics.EulerRealization

/-! # The explicit Euler integration of the IFOC rotor-flux dynamics: a realization

The induction-machine drive family (`InductionMachine.family`,
`theorem/Drives/InductionMachine.lean`) integrated by the explicit Euler method with a fixed step
`h > 0` is an implementation layer over it: each integration realizes the drive it integrates. A
locally exponentially stable drive has a step `h₀ > 0` below which its Euler integration is
locally exponentially stable, and without a step constraint the realization is not sound; an
instance of the generic template `theorem/Numerics/EulerRealization.lean`, in the pattern of
`theorem/Synchronous/SwingEuler.lean`. Scaffold: `theorem/EulerDiscretization.agda`.

Model boundary.
* Model layer (M): `InductionMachine.family`, the rotor-flux dynamics of an indirect field-oriented
  drive with impressed stator currents and slip, state `ψ_r`, read about its flux equilibrium, with
  the model boundary of `theorem/Drives/InductionMachine.lean`.
* Implementation layer (I). `InductionMachine.Euler`: a drive and a step `h > 0`; the system is the
  explicit Euler map `z ↦ z + h f(z)` of the translated rotor-flux field, with step length `h`,
  discrete time, exact arithmetic (no round-off), fixed step. Excluded: step-size control,
  implicit or higher-order schemes, the integration error against the continuous trajectory (the
  sampled predictive-control model of `theorem/Drives/PredictiveControl.lean` is a separate
  discretization).
* Level: local exponential stability of the flux equilibrium.

Source: `theorem/Numerics/EulerRealization.lean` (`euler_sound_small_step`,
`euler_certified_small_step`, `not_euler_realizationSoundUnder_of_large_step`),
`theorem/Drives/InductionMachine.lean` (`family_isAutonomous`, `field_contDiff`,
`mem_den_attractive_iff`); work-sync
`theory/T-numerical-integration.md` §1.2, §2.7.

Results.
* No static result beyond the family definitions.

Family and connection conclusions.
* `InductionMachine.eulerFamily : Family InductionMachine.Euler InductionMachine.Requirement 2 0`:
  every integration read as its Euler map; requirements and translation are those of its drive,
  read through the design. `InductionMachine.euler`: the implementation layer, every integration
  realizing its drive (`Implementation.ofDesign Euler.design`).
* M–I (realization). The small-step laws are the generic connection laws applied to the family,
  with its autonomy `InductionMachine.family_isAutonomous` and the public smoothness lemma
  `InductionMachine.field_contDiff`: `Numerics.euler_sound_small_step` (scaffold
  `sound-small-step`: a locally exponentially stable drive has a step `h₀ > 0` such that every
  Euler integration with a step `h ≤ h₀` is locally exponentially stable) and
  `Numerics.euler_certified_small_step` (scaffold `certified-small-step`).
  `not_euler_realizationSoundUnder` (scaffold `not-sound-large-step`):
  without a step constraint the realization is not sound — the unit-rotor drive (`r_r = L_r = 1`,
  locally exponentially stable by `mem_den_attractive_iff`) has Euler integrations with every
  multiplier outside the unit disk.
-/

noncomputable section

namespace powerlib.Drives.InductionMachine

/-- The explicit Euler integration of a drive about its rotor-flux equilibrium with step `h > 0`. -/
structure Euler where
  /-- The integrated drive. -/
  design : Drive
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler Requirement 2 0 :=
  Numerics.eulerFamily family Drive.field Euler.design Euler.h

/-- The Euler realization: every integration realizes its drive. -/
def euler : Implementation Drive Requirement Euler Requirement 2 0 2 0 :=
  Numerics.euler family Drive.field Euler.design Euler.h

/-- **Without a step constraint the Euler realization of the drives is not sound.** A locally
exponentially stable drive (`unitRotor`, `r_r = L_r = 1`) integrated with a large enough step is not
locally exponentially stable: every Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_euler_realizationSoundUnder_of_large_step`). -/
@[tmio MI]
@[powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := (mem_den_attractive_iff unitRotor (P := .locallyExponentiallyStable) trivial).mpr
    (by norm_num [unitRotor])
  exact Numerics.not_euler_realizationSoundUnder_of_large_step family_isAutonomous
    field_contDiff (by norm_num) hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.Drives.InductionMachine
