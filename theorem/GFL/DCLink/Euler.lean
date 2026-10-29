import theorem.GFL.DCLink.FourState
import theorem.GFL.DCLink.BasinGuard
import theorem.GFL.DCLink.ModelBStability
import theorem.GFL.DCLink.Cascade
import theorem.GFL.DCLink.VoltageControl
import theorem.Numerics.EulerRealization

/-! # The explicit Euler integration of the DC-link families: realizations

The DC-link families of `theorem/GFL/DCLink/` integrated by the explicit Euler method with a fixed
step `h > 0`: each integration realizes the model it integrates. Their fields divide by the
DC-link voltage, so they are `C¹` only where `V_dc ≠ 0`; near a selected point with `V_dc ≠ 0`
they are, and the local laws of the generic template `theorem/Numerics/EulerRealization.lean`
(smoothness of the model at hand, near its point) apply. A locally exponentially stable model whose
point has a nonzero (for some families: positive) DC voltage has a step `h₀ > 0` below which its
Euler integration is locally exponentially stable, and without a step constraint the realization
is not sound; in the pattern of `theorem/Synchronous/SwingEuler.lean`. Scaffold:
`theorem/EulerDiscretization.agda`.

Model boundary.
* Model layer (M), each family with the model boundary of its module, read about its selected
  point (continuous time, autonomous, no input): `FourState.family` (four-state GFL with PLL and
  DC-voltage loop, `theorem/GFL/DCLink/FourState.lean`; every operating point has `V = 1`);
  `BasinGuard.family` (the `basin-guard` carrier, `theorem/GFL/DCLink/BasinGuard.lean`);
  `ModelB.family` (reduced-order model B, `theorem/GFL/DCLink/ModelBStability.lean`);
  `DCLink.family` (current loop feeding the DC link, `theorem/GFL/DCLink/Cascade.lean`);
  `openFamily` and `closedFamily` (DC node in open loop and with the PI outer loop,
  `theorem/GFL/DCLink/VoltageControl.lean`).
* Implementation layer (I). For each family a structure `Euler` (in the namespace of its model
  type: `FourState`, `BasinGuard`, `ModelB`, `CascadeParams`, `OpenLoop`, `DCParams`) of a model
  and a step `h > 0`; the system is the explicit Euler map `z ↦ z + h f(z)` of the model's
  translated field (with its `1/V_dc` term, read with Lean's `x / 0 = 0`), with step length `h`,
  discrete time, exact arithmetic (no round-off), fixed step. Excluded: step-size control, implicit
  or higher-order schemes, the integration error against the continuous trajectory.
* Smoothness at the selected point, as a hypothesis on the model where the family admits points
  off it: none for `FourState` (its fields agree with the smooth `regField` near every operating
  point); `V_dc* ≠ 0` for `BasinGuard` (the carrier is `C¹` on `V_dc ≠ 0`,
  `CarrierParams.carrierField_contDiffOn`) and `ModelB` (`ModelBParams.field_contDiffOn`);
  `V0 > 0` for the cascade (`CascadeParams.field_contDiffOn`) and the open loop
  (`openField_contDiffOn`); `V_dc,ref > 0` for the closed loop
  (`DCParams.closedField_contDiffOn`). Without it the laws are
  not stated: model B has selected points on the plane `V_dc = 0` that satisfy the local
  exponential estimate without being equilibria (`ModelB.collapsePoint`), where no Jacobian exists.
* Level: local exponential stability of the selected point.

Source: `theorem/Numerics/EulerRealization.lean` (`euler_sound_small_step_local`,
`euler_certified_small_step_local`, `not_euler_realizationSoundUnder_of_large_step_local`,
`contDiffAt_shift`) and the family modules (autonomy, smoothness on `V_dc ≠ 0`, members of local
exponential stability; for the carrier its four-state reading `BasinGuard.mem_den_iff_fourState`);
work-sync `theory/T-numerical-integration.md` §1.2, §2.7.

Results.
* The smoothness hypotheses of the local generic laws, one per family:
  `FourState.contDiffAt_modelField`, `BasinGuard.contDiffAt_modelField` (`V_dc* ≠ 0`),
  `ModelB.contDiffAt_modelField` (`V_dc* ≠ 0`), `CascadeParams.contDiffAt_shiftedField`
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
  `Numerics.euler_certified_small_step_local` (scaffold `certified-small-step`).
  `N.not_euler_realizationSoundUnder`
  (scaffold `not-sound-large-step`): without a step constraint the realization is not sound — a
  locally exponentially stable member (`FourState`: `V₀ = k_p = k_i = k_pv = k_iv = C = 1`,
  `X_g = i_d0 = I_dc0 = 0` at `θ₀ = 0`, `FourState.mem_den_locallyExponentiallyStable_of_routh`;
  `BasinGuard`: `s = 1`, `I_dc = I_q* = X_g = 0`, `V = K_p^pll = K_i^pll = K_p^dvc = K_i^dvc =
  C = 1` at `(0, 0, 1, 0)`, whose four-state reading is the `FourState` witness,
  `BasinGuard.mem_den_iff_fourState`; `ModelB.negativeReference`; `CascadeParams`:
  `negativeInductance`; `OpenLoop`: `C = P = V0 = 1`; `DCParams`: `C = V_d = V_dc* = Kp = Ki = 1`,
  `i_ff = I_d0 = 0`) has Euler integrations with every multiplier outside the unit disk.
-/

noncomputable section

open powerlib.Dynamics (State)

namespace powerlib.GFL.DCLink.FourState

/-- The explicit Euler integration of a four-state GFL model about its operating point with step
`h > 0`. -/
structure Euler where
  /-- The integrated four-state GFL model. -/
  design : Model
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its model's
translated field, with step length its step. -/
def eulerFamily : Family Euler Requirement 4 0 :=
  Numerics.eulerFamily family Model.field Euler.design Euler.h

/-- The Euler realization: every integration realizes its four-state GFL model. -/
def euler : Implementation Model Requirement Euler Requirement 4 0 4 0 :=
  Numerics.euler family Model.field Euler.design Euler.h

/-- The translated field is `C¹` near the origin: near the operating point (`V = 1`) the physical
field is the smooth `regField`. The smoothness hypothesis of the local generic Euler laws
(`Numerics.euler_sound_small_step_local`). -/
@[powerlib_foundation] theorem contDiffAt_modelField (m : Model) : ContDiffAt ℝ 1 m.field 0 := by
  refine Numerics.contDiffAt_shift (g := FourState.field m.params) (x₀ := opPoint m.θ)
    ((contDiff_regField m.params).contDiffAt.congr_of_eventuallyEq ?_)
  filter_upwards [Metric.ball_mem_nhds (opPoint m.θ) (by norm_num : (0 : ℝ) < 1 / 2)] with y hy
  exact field_eq_regField_of_near m.params (by simpa [dist_eq_norm] using hy)

/-- The unit model `V₀ = k_p = k_i = k_pv = k_iv = C = 1`, `X_g = i_d0 = I_dc0 = 0` at `θ₀ = 0`
is locally exponentially stable: quartic `λ⁴ + (5/2) λ³ + 4 λ² + 3 λ + 3/2`, Routh conditions met
(`mem_den_locallyExponentiallyStable_of_routh`). -/
@[tmio TM] private theorem unitModel_mem_den :
    connection% ((⟨⟨1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0⟩ : Model) ∈
      family.den (.flow .locallyExponentiallyStable)) := by
  change (⟨⟨1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0⟩ : Model) ∈
        family.den (.flow .locallyExponentiallyStable)
  have hm := mem_den_locallyExponentiallyStable_of_routh ⟨1, 0, 0, 1, 1, 1, 1, 1, 0⟩ one_ne_zero
    (θ0 := 0) ⟨by simp, by simp⟩
    (by norm_num [a3, vd0, twoAlphaCl, Params.γ])
    (by norm_num [a1, vd0, twoAlphaCl, omegaClSq, Γc, Params.γ])
    (by norm_num [a0, vd0, omegaClSq, Γc, Params.γ])
    (by norm_num [a1, a2, a3, a0, vd0, twoAlphaCl, omegaClSq, Γc, Params.γ])
  unfold powerlib.TMIO.Statement at hm
  exact hm

/-- **Without a step constraint the Euler realization of the four-state GFL models is not
sound.** A locally exponentially stable model (`V₀ = k_p = k_i = k_pv = k_iv = C = 1`,
`X_g = i_d0 = I_dc0 = 0` at `θ₀ = 0`: quartic `λ⁴ + (5/2) λ³ + 4 λ² + 3 λ + 3/2`, Routh
conditions met) integrated with a large enough step is not locally exponentially stable: every
Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_euler_realizationSoundUnder_of_large_step_local`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact Numerics.not_euler_realizationSoundUnder_of_large_step_local family_isAutonomous
    (by norm_num) (contDiffAt_modelField _) unitModel_mem_den
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.GFL.DCLink.FourState

namespace powerlib.GFL.DCLink.BasinGuard

/-- The explicit Euler integration of a `basin-guard` carrier model about its selected operating
point with step `h > 0`. -/
structure Euler where
  /-- The integrated carrier model. -/
  design : Model
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its model's
translated carrier field, with step length its step. -/
def eulerFamily : Family Euler Requirement 4 0 :=
  Numerics.eulerFamily family Model.field Euler.design Euler.h

/-- The Euler realization: every integration realizes its carrier model. -/
def euler : Implementation Model Requirement Euler Requirement 4 0 4 0 :=
  Numerics.euler family Model.field Euler.design Euler.h

/-- The translated carrier field is `C¹` near the origin when the selected point has
`V_dc ≠ 0`: the smoothness hypothesis of the local generic Euler laws
(`Numerics.euler_sound_small_step_local`). -/
@[powerlib_foundation] theorem contDiffAt_modelField {m : Model} (hV : m.point 2 ≠ 0) :
    ContDiffAt ℝ 1 m.field 0 :=
  Numerics.contDiffAt_shift (g := m.params.carrierField m.s) (x₀ := m.point)
    ((m.params.carrierField_contDiffOn m.s).contDiffAt
      ((isOpen_ne_fun (Dynamics.contDiff_coord (n := 4) (k := 0) 2).continuous
        continuous_const).mem_nhds hV))

/-- **Without a step constraint the Euler realization of the carrier models is not sound.** The
IN-positive carrier (`s = 1`) with `I_dc = I_q* = X_g = 0`,
`V = K_p^pll = K_i^pll = K_p^dvc = K_i^dvc = C = 1` at `(θ_e, x_p, V_dc, ξ) = (0, 0, 1, 0)` is
locally exponentially stable: its four-state reading (`mem_den_iff_fourState`) is the unit
four-state model above. Integrated with a large enough step it is not: every Euler multiplier
`1 + hλ` leaves the unit disk (`Numerics.not_euler_realizationSoundUnder_of_large_step_local`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  set m : Model := ⟨⟨0, 0, 1, 0, 1, 1, 1, 1, 1⟩, 1, WithLp.toLp 2 ![0, 0, 1, 0]⟩
  have h := mem_den_iff_fourState m rfl (by simp [m]) (by simp [m])
    (.flow .locallyExponentiallyStable)
  unfold powerlib.TMIO.Statement at h
  have hto : m.toFourState = ⟨⟨1, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0⟩ := by
    simp [m, Model.toFourState, CarrierParams.fourStateParams]
  rw [hto] at h
  exact Numerics.not_euler_realizationSoundUnder_of_large_step_local family_isAutonomous
    (by norm_num) (contDiffAt_modelField (by simp [m])) (h.mpr FourState.unitModel_mem_den)
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.GFL.DCLink.BasinGuard

namespace powerlib.GFL.DCLink.ModelB

/-- The explicit Euler integration of a model-B system about its selected state with step
`h > 0`. -/
structure Euler where
  /-- The integrated model-B system. -/
  design : Model
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its model's
translated field, with step length its step. -/
def eulerFamily : Family Euler Requirement 4 0 :=
  Numerics.eulerFamily family Model.field Euler.design Euler.h

/-- The Euler realization: every integration realizes its model-B system. -/
def euler : Implementation Model Requirement Euler Requirement 4 0 4 0 :=
  Numerics.euler family Model.field Euler.design Euler.h

/-- The translated field is `C¹` near the origin when the selected state has `V_dc ≠ 0`: the
smoothness hypothesis of the local generic Euler laws (`Numerics.euler_sound_small_step_local`). -/
@[powerlib_foundation] theorem contDiffAt_modelField {m : Model} (hV : m.x 2 ≠ 0) :
    ContDiffAt ℝ 1 m.field 0 :=
  Numerics.contDiffAt_shift (g := m.p.field) (x₀ := m.x)
    (m.p.field_contDiffOn.contDiffAt (ModelBParams.isOpen_nonzeroVdc.mem_nhds hV))

/-- **Without a step constraint the Euler realization of model B is not sound.** The
negative-reference converter (`V_dc* = −1`, `negativeReference`) is locally exponentially stable;
integrated with a large enough step it is not: every Euler multiplier `1 + hλ` leaves the unit
disk (`Numerics.not_euler_realizationSoundUnder_of_large_step_local`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := negativeReference_mem_den_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_euler_realizationSoundUnder_of_large_step_local family_isAutonomous
    (by norm_num) (contDiffAt_modelField (by simp [negativeReference])) hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.GFL.DCLink.ModelB

namespace powerlib.GFL.DCLink.CascadeParams

/-- The explicit Euler integration of a current-loop/DC-link cascade about its operating point
with step `h > 0`. -/
structure Euler where
  /-- The integrated cascade. -/
  design : CascadeParams
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its cascade's
translated field, with step length its step. -/
def eulerFamily : Family Euler Spectral.Requirement 3 0 :=
  Numerics.eulerFamily family shiftedField Euler.design Euler.h

/-- The Euler realization: every integration realizes its cascade. -/
def euler : Implementation CascadeParams Spectral.Requirement Euler Spectral.Requirement 3 0 3 0 :=
  Numerics.euler family shiftedField Euler.design Euler.h

/-- The translated field is `C¹` near the origin when the operating voltage is positive: the
smoothness hypothesis of the local generic Euler laws (`Numerics.euler_sound_small_step_local`). -/
@[powerlib_foundation] theorem contDiffAt_shiftedField {p : CascadeParams} (hV : 0 < p.V0) :
    ContDiffAt ℝ 1 p.shiftedField 0 :=
  Numerics.contDiffAt_shift (g := p.field p.Id0) (x₀ := p.eqState)
    ((p.field_contDiffOn _).contDiffAt
      (isOpen_posV.mem_nhds (by simpa [posV, eqState] using hV)))

/-- **Without a step constraint the Euler realization of the cascades is not sound.** The
negative-inductance cascade (`negativeInductance`, `V0 = 1`) is locally exponentially stable;
integrated with a large enough step it is not: every Euler multiplier `1 + hλ` leaves the unit
disk (`Numerics.not_euler_realizationSoundUnder_of_large_step_local`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := negativeInductance_mem_den_locallyExponentiallyStable
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_euler_realizationSoundUnder_of_large_step_local
    (Spectral.localFamily_isAutonomous _ _ _ : family.IsAutonomous shiftedField)
    (by norm_num) (contDiffAt_shiftedField (by norm_num [negativeInductance])) hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.GFL.DCLink.CascadeParams

namespace powerlib.GFL.DCLink.OpenLoop

/-- The explicit Euler integration of an open-loop DC node about its operating voltage with step
`h > 0`. -/
structure Euler where
  /-- The integrated DC node. -/
  design : OpenLoop
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its node's
translated field, with step length its step. -/
def eulerFamily : Family Euler Spectral.Requirement 1 0 :=
  Numerics.eulerFamily openFamily field Euler.design Euler.h

/-- The Euler realization: every integration realizes its DC node. -/
def euler : Implementation OpenLoop Spectral.Requirement Euler Spectral.Requirement 1 0 1 0 :=
  Numerics.euler openFamily field Euler.design Euler.h

/-- The translated field is `C¹` near the origin when the operating voltage is positive: the
smoothness hypothesis of the local generic Euler laws (`Numerics.euler_sound_small_step_local`). -/
@[powerlib_foundation] theorem contDiffAt_field {m : OpenLoop} (hV : 0 < m.V0) :
    ContDiffAt ℝ 1 m.field 0 :=
  Numerics.contDiffAt_shift (g := openField m.C (-(m.P / m.V0)) m.P) (x₀ := dcState m.V0)
    ((openField_contDiffOn _ _ _).contDiffAt
      ((isOpen_posDC 1).mem_nhds (by simpa [posDC, dcState] using hV)))

/-- **Without a step constraint the Euler realization of the open-loop DC node is not sound.** A
rectifying node (`C = P = V0 = 1`) is locally exponentially stable; integrated with a large enough
step it is not: its Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_euler_realizationSoundUnder_of_large_step_local`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := openLoop_mem_den_locallyExponentiallyStable ⟨1, 1, 1⟩ one_pos one_pos (by norm_num)
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_euler_realizationSoundUnder_of_large_step_local
    (Spectral.localFamily_isAutonomous _ _ _ : openFamily.IsAutonomous field)
    (by norm_num) (contDiffAt_field one_pos) hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.GFL.DCLink.OpenLoop

namespace powerlib.GFL.DCLink.DCParams

/-- The explicit Euler integration of a DC-voltage outer loop about `(V_dc*, ζ0)` with step
`h > 0`. -/
structure Euler where
  /-- The integrated outer loop. -/
  design : DCParams
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its loop's
translated field, with step length its step. -/
def eulerFamily : Family Euler Spectral.Requirement 2 0 :=
  Numerics.eulerFamily closedFamily shiftedField Euler.design Euler.h

/-- The Euler realization: every integration realizes its outer loop. -/
def euler : Implementation DCParams Spectral.Requirement Euler Spectral.Requirement 2 0 2 0 :=
  Numerics.euler closedFamily shiftedField Euler.design Euler.h

/-- The translated field is `C¹` near the origin when the voltage reference is positive: the
smoothness hypothesis of the local generic Euler laws (`Numerics.euler_sound_small_step_local`). -/
@[powerlib_foundation] theorem contDiffAt_shiftedField {p : DCParams} (hV : 0 < p.Vref) :
    ContDiffAt ℝ 1 p.shiftedField 0 :=
  Numerics.contDiffAt_shift (g := p.closedField) (x₀ := p.eqState)
    (p.closedField_contDiffOn.contDiffAt
      ((isOpen_posDC 2).mem_nhds (by simpa [posDC, eqState] using hV)))

/-- **Without a step constraint the Euler realization of the DC-voltage outer loop is not
sound.** The loop `C = V_d = V_dc* = Kp = Ki = 1`, `i_ff = I_d0 = 0` is locally exponentially
stable; integrated with a large enough step it is not: every Euler multiplier `1 + hλ` leaves the
unit disk (`Numerics.not_euler_realizationSoundUnder_of_large_step_local`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := closedLoop_mem_den_locallyExponentiallyStable ⟨1, 1, 1, 1, 1, 0, 0⟩ one_pos one_pos
    one_pos (by norm_num [Idc0]) one_pos
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_euler_realizationSoundUnder_of_large_step_local
    (Spectral.localFamily_isAutonomous _ _ _ : closedFamily.IsAutonomous shiftedField)
    (by norm_num) (contDiffAt_shiftedField one_pos) hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.GFL.DCLink.DCParams
