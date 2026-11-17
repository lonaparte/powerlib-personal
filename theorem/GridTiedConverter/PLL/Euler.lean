import theorem.GridTiedConverter.PLL.PIPLLFamily
import theorem.GridTiedConverter.PLL.Multiscale
import theorem.Numerics.EulerRealization

/-! # The explicit Euler integration of the PLL families: realizations

The PI-PLL family (`PLL.PIPLL.family`, `theorem/GridTiedConverter/PLL/PIPLLFamily.lean`) and the
reduced slow SRF-PLL family (`PLL.ReducedSlow.family`,
`theorem/GridTiedConverter/PLL/Multiscale.lean`) integrated by the explicit Euler method with a
fixed step `h > 0` are implementation layers over them: each integration realizes the model it
integrates, and a locally exponentially stable model has a step `h₀ > 0` below which its Euler
integration is locally exponentially stable; instances of the generic template
`theorem/Numerics/EulerRealization.lean`, in the pattern of
`theorem/PowerSystem/Synchronous/SwingEuler.lean`. Scaffold:
`theorem/Numerics/EulerDiscretization.agda`.

Model boundary.
* Model layer (M): `PLL.PIPLL.family`, the PI-PLL with a `C¹` phase-detector characteristic, state
  `(θ, η)`, read about its selected point (`theorem/GridTiedConverter/PLL/PIPLLFamily.lean`);
  `PLL.ReducedSlow.family`, the one-state linear reduced slow model `ẏ = −(b/a) y` about the origin
  (`theorem/GridTiedConverter/PLL/Multiscale.lean`); each with the model boundary of its module.
* Implementation layer (I). `PIPLL.Euler`, `ReducedSlow.Euler`: a model and a step `h > 0`; the
  system is the explicit Euler map `z ↦ z + h f(z)` of the model's (translated) field, with step
  length `h`, discrete time, exact arithmetic (no round-off), fixed step. Excluded: step-size
  control, implicit or higher-order schemes, the integration error against the continuous
  trajectory.
* Level: local exponential stability of the selected point.

Source: `theorem/Numerics/EulerRealization.lean` (`euler_sound_small_step_local`,
`not_eulerStep_realizationSoundUnder`, `contDiff_shift`),
`theorem/GridTiedConverter/PLL/PIPLL.lean` (`contDiff_piPLLField`),
`theorem/GridTiedConverter/PLL/PIPLLFamily.lean` (`srf_mem_den_locallyExponentiallyStable_inPhase`
at `k = 0`),
`theorem/GridTiedConverter/PLL/Multiscale.lean` (`chain_le_semantics`),
`theorem/Linear/Stability.lean` (`Linear.affine_contDiff`); work-sync
`theory/T-numerical-integration.md` §1.2, §2.7.

Results.
* The smoothness hypotheses of the generic laws: the translated PI-PLL field is `C¹`
  (`Numerics.contDiff_shift` at `contDiff_piPLLField`), the reduced slow field is affine
  (`Linear.affine_contDiff`); the module states only the connection conclusions below.

Family and connection conclusions.
* `PIPLL.eulerFamily : Family PIPLL.Euler PIPLL.Requirement 2 0` and
  `ReducedSlow.eulerFamily : Family ReducedSlow.Euler ReducedSlow.Requirement 1 0`: every
  integration read as its Euler map; requirements and translation are those of its model, read
  through the design. `PIPLL.euler`, `ReducedSlow.euler`: the implementation layers, every
  integration realizing its model (`Implementation.ofDesign Numerics.EulerStep.design`).
* M–I (realization), for both families. The small-step laws are the generic connection laws
  applied to each family, with its autonomy (`PIPLL.family_isAutonomous`,
  `ReducedSlow.family_isAutonomous`) and its smoothness above:
  `Numerics.euler_sound_small_step_local` (scaffold `sound-small-step`: a locally exponentially
  stable model has a step `h₀ > 0` such that every Euler integration with a step `h ≤ h₀` is
  locally exponentially stable) and
  `Numerics.euler_sound_small_step_local` (scaffold `certified-small-step`, read through
  certification). `not_euler_realizationSoundUnder` (scaffold `not-sound-large-step`):
  without a step constraint the realization is not sound — for the PI-PLL the SRF detector with
  `V = K_p = K_i = 1` at `θ* = 0`, for the reduced slow model `a = b = 1` (`ẏ = −y`), each locally
  exponentially stable with Euler integrations having every multiplier outside the unit disk.
-/

noncomputable section

namespace powerlib.PLL.PIPLL

/-- The explicit Euler integration of a PI-PLL model about its selected point with step `h > 0`. -/
abbrev Euler := Numerics.EulerStep Model

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler Requirement 2 0 :=
  Numerics.eulerFamily family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its PI-PLL model. -/
def euler : Implementation Model Requirement Euler Requirement 2 0 2 0 :=
  Numerics.euler family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- **Without a step constraint the Euler realization of the PI-PLL models is not sound.** A locally
exponentially stable PI-PLL (the SRF detector `h = −V sin` with `V = K_p = K_i = 1`, `δω = 0`, at
`θ* = 0`) integrated with a large enough step is not locally exponentially stable: every Euler
multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_eulerStep_realizationSoundUnder`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := srf_mem_den_locallyExponentiallyStable_inPhase (V := 1) (Kp := 1) (Ki := 1)
    (by norm_num) (by norm_num) 0 0
  unfold powerlib.TMIO.Statement at hm
  rw [Int.cast_zero, mul_zero, zero_mul] at hm
  exact Numerics.not_eulerStep_realizationSoundUnder family_isAutonomous
    (fun m => Numerics.contDiff_shift (contDiff_piPLLField m.smooth)) (by norm_num) hm

end powerlib.PLL.PIPLL

namespace powerlib.PLL.ReducedSlow

/-- The explicit Euler integration of a reduced slow PLL model about the origin with step
`h > 0`. -/
abbrev Euler := Numerics.EulerStep Model

/-- The Euler integration family: every integration read as the Euler map of its model's field, with
step length its step. -/
def eulerFamily : Family Euler Requirement 1 0 :=
  Numerics.eulerFamily family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its reduced slow PLL model. -/
def euler : Implementation Model Requirement Euler Requirement 1 0 1 0 :=
  Numerics.euler family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- **Without a step constraint the Euler realization of the reduced slow PLL models is not
sound.** The locally exponentially stable model `a = b = 1` (`ẏ = −y`) integrated with a large
enough step is not locally exponentially stable: its Euler multiplier `1 − h` leaves the unit disk
(`Numerics.not_eulerStep_realizationSoundUnder`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hc := chain_le_semantics
  unfold powerlib.TMIO.Statement at hc
  have hm : (⟨1, 1⟩ : Model) ∈ family.den (.flow .locallyExponentiallyStable) :=
    Family.chain_le_semantics_iff.mp hc _ ((TMIO.mem_realize _ _ _).mpr fun q hq => by
      rw [Set.mem_singleton_iff.mp hq]
      show (0 : ℝ) < 1 / 1
      norm_num)
  exact Numerics.not_eulerStep_realizationSoundUnder family_isAutonomous
    (fun _ => Linear.affine_contDiff _ _) one_pos hm

end powerlib.PLL.ReducedSlow
