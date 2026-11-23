import theorem.GridTiedConverter.GFL.DCLink.PLLDC.Stability
import theorem.GridTiedConverter.GFL.DCLink.Cascade
import theorem.GridTiedConverter.GFL.DCLink.VoltageControl
import theorem.Numerics.EulerRealization

/-! # The explicit Euler integration of the DC-link families: realizations

The DC-link families of `theorem/GridTiedConverter/GFL/DCLink/` integrated by the explicit Euler
method with a fixed step `h > 0`: each integration realizes the model it integrates. Their fields
divide by the DC-link voltage, so they are `C¹` only where `V_dc ≠ 0`; near a selected point with
`V_dc ≠ 0` they are, and the local laws of the generic template
`theorem/Numerics/EulerRealization.lean` (smoothness of the model at hand, near its point) apply. A
locally exponentially stable model whose point has a nonzero (for some families: positive) DC
voltage has a step `h₀ > 0` below which its Euler integration is locally exponentially stable, and
without a step constraint the realization is not sound; in the pattern of
`theorem/PowerSystem/Synchronous/SwingEuler.lean`. Scaffold:
`theorem/Numerics/EulerDiscretization.agda`.

Model boundary.
* Model layer (M), each family with the model boundary of its module, read about its selected
  point (continuous time, autonomous, no input): `PLLDC.family` (the four-state DC-link model,
  `theorem/GridTiedConverter/GFL/DCLink/PLLDC/Stability.lean`; the four-state GFL model of
  `theorem/GridTiedConverter/GFL/DCLink/FourState.lean` and the `basin-guard` carrier of
  `theorem/GridTiedConverter/GFL/DCLink/BasinGuard.lean` are parameterizations of it and are
  integrated as their PLL–DC images, `FourState.Model.toPLLDC`, `BasinGuard.Model.toPLLDC`);
  `DCLink.family` (current loop
  feeding the DC link, `theorem/GridTiedConverter/GFL/DCLink/Cascade.lean`); `openFamily` and
  `closedFamily` (DC node in open loop and with the PI outer loop,
  `theorem/GridTiedConverter/GFL/DCLink/VoltageControl.lean`).
* Implementation layer (I). For each family the integrations `Euler := Numerics.EulerStep` of its
  model type (in the namespace of the model type: `PLLDC`, `CascadeParams`, `OpenLoop`,
  `DCParams`): a model and a step `h > 0`; the system is the explicit
  Euler map `z ↦ z + h f(z)` of the model's translated field (with its `1/V_dc` term, read with
  Lean's `x / 0 = 0`), with step length `h`, discrete time, exact arithmetic (no round-off), fixed
  step. Excluded: step-size control, implicit or higher-order schemes, the integration error against
  the continuous trajectory.
* Smoothness at the selected point, as a hypothesis on the model where the family admits points
  off it: `V_dc* ≠ 0` for `PLLDC` (`PLLDC.Params.field_contDiffOn`; every four-state operating
  point has `V = 1`);
  `V0 > 0` for the cascade (`CascadeParams.field_contDiffOn`) and the open loop
  (`openField_contDiffOn`); `V_dc,ref > 0` for the closed loop
  (`DCParams.closedField_contDiffOn`). Without it the laws are
  not stated: the PLL–DC model has selected points on the plane `V_dc = 0` that satisfy the local
  exponential estimate without being equilibria (`PLLDC.collapsePoint`), where no Jacobian exists.
* Level: local exponential stability of the selected point.

Source: `theorem/Numerics/EulerRealization.lean` (`euler_sound_small_step_local`,
`not_eulerStep_realizationSoundUnder_local`,
`contDiffAt_shift`) and the family modules (autonomy, smoothness on `V_dc ≠ 0`, members of local
exponential stability); work-sync `theory/T-numerical-integration.md` §1.2, §2.7.

Results.
* The smoothness hypotheses of the local generic laws, one per family:
  `PLLDC.contDiffAt_modelField` (`V_dc* ≠ 0`), `CascadeParams.contDiffAt_shiftedField`
  (`V0 > 0`), `OpenLoop.contDiffAt_field` (`V0 > 0`), `DCParams.contDiffAt_shiftedField`
  (`V_dc,ref > 0`): the translated field is `C¹` near the origin.

Family and connection conclusions.
* For each family `F` above: `N.eulerFamily` (`N` the namespace of its model type), every
  integration read as its Euler map, with the requirements and translation of its model read
  through the design; `N.euler`, every integration realizing its model (`Implementation.ofDesign`).
* M–I (realization), for each family. The small-step laws are the local generic connection laws
  applied to the family, with its autonomy (`family_isAutonomous`; for the cascade and the DC
  node `Spectral.localFamily_isAutonomous`, they are local families) and its public smoothness
  lemma above: `Numerics.euler_sound_small_step_local` (scaffold `sound-small-step`: a locally
  exponentially stable model, with the smoothness hypothesis above, has a step `h₀ > 0` such that
  every Euler integration with a step `h ≤ h₀` is locally exponentially stable) and
  `Numerics.euler_sound_small_step_local` (scaffold `certified-small-step`, read through
  certification). `N.not_euler_realizationSoundUnder`
  (scaffold `not-sound-large-step`): without a step constraint the realization is not sound — a
  locally exponentially stable member (`PLLDC.negativeReference`; `CascadeParams`:
  `negativeInductance`; `OpenLoop`: `C = P = V0 = 1`; `DCParams`: `C = V_d = V_dc* = Kp = Ki = 1`,
  `i_ff = I_d0 = 0`) has Euler integrations with every multiplier outside the unit disk.
-/

noncomputable section

open powerlib.Dynamics (State)

namespace powerlib.GFL.DCLink.PLLDC

/-- The explicit Euler integration of a PLL–DC system about its selected state with step
`h > 0`. -/
abbrev Euler := Numerics.EulerStep Model

/-- The Euler integration family: every integration read as the Euler map of its model's
translated field, with step length its step. -/
def eulerFamily : Family Euler Requirement 4 0 :=
  Numerics.eulerFamily family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its PLL–DC system. -/
def euler : Implementation Model Requirement Euler Requirement 4 0 4 0 :=
  Numerics.euler family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The translated field is `C¹` near the origin when the selected state has `V_dc ≠ 0`: the
smoothness hypothesis of the local generic Euler laws (`Numerics.euler_sound_small_step_local`). -/
@[tmio M, powerlib_domain] theorem contDiffAt_modelField {m : Model} (hV : m.x 2 ≠ 0) :
    ContDiffAt ℝ 1 m.field 0 :=
  Numerics.contDiffAt_shift (g := m.p.field) (x₀ := m.x)
    (m.p.field_contDiffOn.contDiffAt (PLLDC.Params.isOpen_nonzeroVdc.mem_nhds hV))

/-- **Without a step constraint the Euler realization of the PLL–DC model is not sound.** The
negative-reference converter (`V_dc* = −1`, `negativeReference`) is locally exponentially stable;
integrated with a large enough step it is not: every Euler multiplier `1 + hλ` leaves the unit
disk (`Numerics.not_eulerStep_realizationSoundUnder_local`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := negativeReference_mem_den_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerStep_realizationSoundUnder_local family_isAutonomous
    (by norm_num) (contDiffAt_modelField (by simp [negativeReference])) hm

end powerlib.GFL.DCLink.PLLDC

namespace powerlib.GFL.DCLink.CascadeParams

/-- The explicit Euler integration of a current-loop/DC-link cascade about its operating point
with step `h > 0`. -/
abbrev Euler := Numerics.EulerStep CascadeParams

/-- The Euler integration family: every integration read as the Euler map of its cascade's
translated field, with step length its step. -/
def eulerFamily : Family Euler Spectral.Requirement 3 0 :=
  Numerics.eulerFamily family shiftedField Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its cascade. -/
def euler : Implementation CascadeParams Spectral.Requirement Euler Spectral.Requirement 3 0 3 0 :=
  Numerics.euler family shiftedField Numerics.EulerStep.design Numerics.EulerStep.h

/-- The translated field is `C¹` near the origin when the operating voltage is positive: the
smoothness hypothesis of the local generic Euler laws (`Numerics.euler_sound_small_step_local`). -/
@[tmio M, powerlib_domain] theorem contDiffAt_shiftedField {p : CascadeParams} (hV : 0 < p.V0) :
    ContDiffAt ℝ 1 p.shiftedField 0 :=
  Numerics.contDiffAt_shift (g := p.field p.Id0) (x₀ := p.eqState)
    ((p.field_contDiffOn _).contDiffAt
      ((isOpen_posDC 2).mem_nhds (by simpa [posDC, eqState] using hV)))

/-- **Without a step constraint the Euler realization of the cascades is not sound.** The
negative-inductance cascade (`negativeInductance`, `V0 = 1`) is locally exponentially stable;
integrated with a large enough step it is not: every Euler multiplier `1 + hλ` leaves the unit
disk (`Numerics.not_eulerStep_realizationSoundUnder_local`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := negativeInductance_mem_den_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerStep_realizationSoundUnder_local
    (Spectral.localFamily_isAutonomous _ _ _ : family.IsAutonomous shiftedField)
    (by norm_num) (contDiffAt_shiftedField (by norm_num [negativeInductance])) hm

end powerlib.GFL.DCLink.CascadeParams

namespace powerlib.GFL.DCLink.OpenLoop

/-- The explicit Euler integration of an open-loop DC node about its operating voltage with step
`h > 0`. -/
abbrev Euler := Numerics.EulerStep OpenLoop

/-- The Euler integration family: every integration read as the Euler map of its node's
translated field, with step length its step. -/
def eulerFamily : Family Euler Spectral.Requirement 1 0 :=
  Numerics.eulerFamily openFamily field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its DC node. -/
def euler : Implementation OpenLoop Spectral.Requirement Euler Spectral.Requirement 1 0 1 0 :=
  Numerics.euler openFamily field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The translated field is `C¹` near the origin when the operating voltage is positive: the
smoothness hypothesis of the local generic Euler laws (`Numerics.euler_sound_small_step_local`). -/
@[tmio M, powerlib_domain] theorem contDiffAt_field {m : OpenLoop} (hV : 0 < m.V0) :
    ContDiffAt ℝ 1 m.field 0 :=
  Numerics.contDiffAt_shift (g := openField m.C (-(m.P / m.V0)) m.P) (x₀ := dcState m.V0)
    ((openField_contDiffOn _ _ _).contDiffAt
      ((isOpen_posDC 0).mem_nhds (by simpa [posDC, dcState] using hV)))

/-- **Without a step constraint the Euler realization of the open-loop DC node is not sound.** A
rectifying node (`C = P = V0 = 1`) is locally exponentially stable; integrated with a large enough
step it is not: its Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_eulerStep_realizationSoundUnder_local`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := (connection_proof% openLoop_mem_den_locallyExponentiallyStable_iff
    ⟨⟨0, 1, 0⟩, 1, 1, rfl, rfl⟩ one_pos one_pos).mpr (by norm_num)
  exact Numerics.not_eulerStep_realizationSoundUnder_local
    (Spectral.localFamily_isAutonomous _ _ _ : openFamily.IsAutonomous field)
    (by norm_num) (contDiffAt_field one_pos) hm

end powerlib.GFL.DCLink.OpenLoop

namespace powerlib.GFL.DCLink.DCParams

/-- The explicit Euler integration of a DC-voltage outer loop about `(V_dc*, ζ0)` with step
`h > 0`. -/
abbrev Euler := Numerics.EulerStep DCParams

/-- The Euler integration family: every integration read as the Euler map of its loop's
translated field, with step length its step. -/
def eulerFamily : Family Euler Spectral.Requirement 2 0 :=
  Numerics.eulerFamily closedFamily shiftedField Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its outer loop. -/
def euler : Implementation DCParams Spectral.Requirement Euler Spectral.Requirement 2 0 2 0 :=
  Numerics.euler closedFamily shiftedField Numerics.EulerStep.design Numerics.EulerStep.h

/-- The translated field is `C¹` near the origin when the voltage reference is positive: the
smoothness hypothesis of the local generic Euler laws (`Numerics.euler_sound_small_step_local`). -/
@[tmio M, powerlib_domain] theorem contDiffAt_shiftedField {p : DCParams} (hV : 0 < p.Vref) :
    ContDiffAt ℝ 1 p.shiftedField 0 :=
  Numerics.contDiffAt_shift (g := p.closedField) (x₀ := p.eqState)
    (p.closedField_contDiffOn.contDiffAt
      ((isOpen_posDC 0).mem_nhds (by simpa [posDC, eqState] using hV)))

/-- **Without a step constraint the Euler realization of the DC-voltage outer loop is not
sound.** The loop `C = V_d = V_dc* = Kp = Ki = 1`, `i_ff = I_d0 = 0` is locally exponentially
stable; integrated with a large enough step it is not: every Euler multiplier `1 + hλ` leaves the
unit disk (`Numerics.not_eulerStep_realizationSoundUnder_local`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := (connection_proof% closedLoop_mem_den_locallyExponentiallyStable_iff
    ⟨⟨0, 1, 0⟩, 1, 1, 1, 1, 0, 0, rfl, rfl⟩ one_pos one_pos one_pos).mpr
    ⟨by norm_num [Idc0], one_pos⟩
  exact Numerics.not_eulerStep_realizationSoundUnder_local
    (Spectral.localFamily_isAutonomous _ _ _ : closedFamily.IsAutonomous shiftedField)
    (by norm_num) (contDiffAt_shiftedField one_pos) hm

end powerlib.GFL.DCLink.DCParams
