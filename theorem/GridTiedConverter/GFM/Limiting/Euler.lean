import theorem.GridTiedConverter.GFM.Limiting.Saturation
import theorem.Numerics.EulerRealization

/-! # The explicit Euler integration of the saturated grid-forming converter: a realization

The saturated-GFM family (`Limiting.family`,
`theorem/GridTiedConverter/GFM/Limiting/Saturation.lean`) integrated by the explicit Euler method
with a fixed step `h > 0` is an implementation layer over it: each integration realizes the model it
integrates. A locally exponentially stable model has a step `h₀ > 0` below which its Euler
integration is locally exponentially stable, and without a step constraint the realization is not
sound; an instance of the generic template `theorem/Numerics/EulerRealization.lean`, in the pattern
of `theorem/PowerSystem/Synchronous/SwingEuler.lean`. Scaffold:
`theorem/Numerics/EulerDiscretization.agda`.

Model boundary.
* Model layer (M): `Limiting.family`, the swing-type outer loop of a GFM converter in current
  saturation (`P_e = P_sat cos(δ − φ)`), state `(δ, ω)`, read about its selected point `(δ*, 0)`
  (a local spectral family), with the model boundary of
  `theorem/GridTiedConverter/GFM/Limiting/Saturation.lean`.
* Implementation layer (I). `Limiting.Euler`: a model and a step `h > 0`; the system is the
  explicit Euler map `z ↦ z + h f(z)` of the translated saturated field, with step length `h`,
  discrete time, exact arithmetic (no round-off), fixed step. Excluded: step-size control,
  implicit or higher-order schemes, the integration error against the continuous trajectory.
* Level: local exponential stability of the selected point.

Source: `theorem/Numerics/EulerRealization.lean` (`euler_sound_small_step_local`,
`not_eulerStep_realizationSoundUnder`, `contDiff_shift`),
`theorem/GridTiedConverter/GFM/Limiting/Saturation.lean` (`satField_contDiff`,
`saturated_stable_equilibrium`); work-sync `theory/T-numerical-integration.md` §1.2, §2.7.

Results.
* The smoothness hypothesis of the generic laws: the translated field is `C¹`
  (`Numerics.contDiff_shift` at `satField_contDiff`); the module states only the connection
  conclusions below.

Family and connection conclusions.
* `Limiting.eulerFamily : Family Limiting.Euler Spectral.Requirement 2 0`: every integration read
  as its Euler map; requirements and translation are those of its model, read through the design.
  `Limiting.euler`: the implementation layer, every integration realizing its model
  (`Implementation.ofDesign Numerics.EulerStep.design`).
* M–I (realization). The small-step laws are the generic connection laws applied to the family,
  with its autonomy (`Spectral.localFamily_isAutonomous`, the family is a local family) and the
  smoothness above: `Numerics.euler_sound_small_step_local`
  (scaffold `sound-small-step`: a locally exponentially stable model has a step `h₀ > 0` such
  that every Euler integration with a step `h ≤ h₀` is locally exponentially stable) and
  `Numerics.euler_sound_small_step_local` (scaffold `certified-small-step`, read through
  certification). `not_euler_realizationSoundUnder` (scaffold `not-sound-large-step`):
  without a step constraint the realization is not sound — the stable saturated equilibrium with
  `M = D = P_sat = 1`, `P_ref = φ = 0` has Euler integrations with every multiplier outside the
  unit disk.
-/

noncomputable section

namespace powerlib.Limiting

/-- The explicit Euler integration of a saturated GFM model about its selected angle with step
`h > 0`. -/
abbrev Euler := Numerics.EulerStep SatModel

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler Spectral.Requirement 2 0 :=
  Numerics.eulerFamily family SatModel.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its saturated GFM model. -/
def euler : Implementation SatModel Spectral.Requirement Euler Spectral.Requirement 2 0 2 0 :=
  Numerics.euler family SatModel.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- **Without a step constraint the Euler realization of the saturated GFM models is not sound.**
The stable saturated equilibrium with `M = D = P_sat = 1`, `P_ref = φ = 0` integrated with a large
enough step is not locally exponentially stable: every Euler multiplier `1 + hλ` leaves the unit
disk (`Numerics.not_eulerStep_realizationSoundUnder`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := saturated_stable_equilibrium (M := 1) (D := 1) (Pref := 0) (Psat := 1) (φ := 0) one_pos
    one_pos one_pos (by norm_num)
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerStep_realizationSoundUnder
    (Spectral.localFamily_isAutonomous _ _ _)
    (fun _ => Numerics.contDiff_shift (satField_contDiff _ _ _ _ _)) (by norm_num) hm

end powerlib.Limiting
