import theorem.PowerSystem.Synchronous.GeneralSwing
import theorem.Numerics.EulerRealization

/-! # The explicit Euler integration of the swing equation: a realization

The swing family (`Swing.family`, `theorem/PowerSystem/Synchronous/Swing.lean`) and the swing
family with an arbitrary power law (`GeneralSwing.family`,
`theorem/PowerSystem/Synchronous/GeneralSwing.lean`) integrated by the explicit Euler method with a
fixed step `h > 0` are implementation layers over them: each integration realizes the swing model
it integrates. A locally exponentially stable swing model whose field is `C¹` near its point has a
step `h₀ > 0` below which its Euler integration is locally exponentially stable, and without a
step constraint the realization is not sound; the instances of the generic template
`theorem/Numerics/EulerRealization.lean`. Scaffold: `theorem/Numerics/EulerDiscretization.agda`.

Model boundary.
* Model layer (M): `Swing.family`, the swing model `M δ̈ + D δ̇ = P_m − (k₁ + k₂ sin(δ − k₃))` read
  about its selected point `(δ*, 0)` (state `z = (δ − δ*, ω)`, continuous time, autonomous, no
  input), with the model boundary of `theorem/PowerSystem/Synchronous/Swing.lean`;
  `GeneralSwing.family`, the swing model `M θ̈ + D θ̇ = τ − P_e(θ, θ̇)` with an arbitrary law read
  about its selected point `(θ*, ω*)`, with the model boundary of
  `theorem/PowerSystem/Synchronous/GeneralSwing.lean`.
* Implementation layer (I). `Swing.Euler`, `GeneralSwing.Euler`: a swing model and a step `h > 0`;
  the system is the explicit Euler map `z ↦ z + h f(z)` of the translated swing field (the Euler
  integration of the swing equation, read about the selected point), with step length `h`,
  discrete time, exact arithmetic (no round-off), fixed step. Excluded: step-size control,
  implicit or higher-order schemes, the integration error against the continuous trajectory.
* Smoothness: the sinusoidal swing field is `C¹` everywhere (the global laws of the template); the
  law of `GeneralSwing.family` is arbitrary, so its laws carry the hypothesis that it is `C¹` near
  the selected point (`ContDiffAt ℝ 1 (Function.uncurry P_e) (θ*, ω*)`, the local laws).
* Level: local exponential stability of the selected point.

Source: `theorem/Numerics/EulerRealization.lean` (`euler_sound_small_step_local`,
`not_eulerStep_realizationSoundUnder` and their `_local` forms, `contDiffAt_shift`),
`theorem/PowerSystem/Synchronous/Swing.lean` (`family_isAutonomous`, `SwingParams.contDiff_field`,
`mem_den_locallyExponentiallyStable`), `theorem/PowerSystem/Synchronous/GeneralSwing.lean`
(`family_isAutonomous`, `mem_den_locallyExponentiallyStable_iff_of_sinusoid`); work-sync
`theory/T-numerical-integration.md` §1.2, §2.7.

Results.
* The translated swing field is `C¹` (`Numerics.contDiff_shift` of
  `SwingParams.contDiff_field`), the smoothness hypothesis of the generic laws;
  `GeneralSwing.contDiffAt_field`: the translated field with an arbitrary law is `C¹` near the
  origin when the law is `C¹` near the selected point.

Family and connection conclusions.
* `Swing.eulerFamily : Family Swing.Euler Requirement 2 0`: every integration read as its Euler
  map; requirements and translation are those of its swing model, read through the design
  (`meets y = Swing.Meets y.design`). `Swing.euler`: the implementation layer, every integration
  realizing its swing model (`Implementation.ofDesign Numerics.EulerStep.design`).
* M–I (realization). The small-step laws are the generic connection laws applied to the family,
  with its autonomy `Swing.family_isAutonomous` and the smoothness of the translated field
  (`Numerics.contDiff_shift`, `SwingParams.contDiff_field`):
  `Numerics.euler_sound_small_step_local` (scaffold
  `sound-small-step`: a locally exponentially stable swing model — for instance a balanced angle
  with positive inertia, damping and synchronizing coefficient,
  `Swing.mem_den_locallyExponentiallyStable` — has a step `h₀ > 0` such that every Euler
  integration with a step `h ≤ h₀` is locally exponentially stable) and
  `Numerics.euler_sound_small_step_local` (scaffold `certified-small-step`: the same for the design
  of an integration certified for local exponential stability). `not_euler_realizationSoundUnder`
  (scaffold `not-sound-large-step`): without a step constraint the realization is not sound — the
  locally exponentially stable model `M = 1`, `D = 4`, `K = 4` at a balanced angle has Euler
  integrations with every Euler multiplier outside the unit disk (`h = 3`: both at `−5`; the
  generic law `Numerics.not_eulerStep_realizationSoundUnder`).
* The same laws for `GeneralSwing.family` (`GeneralSwing.eulerFamily`, `GeneralSwing.euler`; the
  local generic laws `Numerics.euler_sound_small_step_local` with `GeneralSwing.family_isAutonomous`
  and `GeneralSwing.contDiffAt_field`, for a law `C¹` near `(θ*, ω*)`;
  `GeneralSwing.not_euler_realizationSoundUnder`, witness `M = D = 1`, `τ = 0`, `P_e = sin θ` at
  the origin, locally exponentially stable through the hub,
  `GeneralSwing.mem_den_locallyExponentiallyStable_iff_of_sinusoid`).
-/

noncomputable section

namespace powerlib.Synchronous.Swing

/-- The explicit Euler integration of a swing model about its selected point with step `h > 0`. -/
abbrev Euler := Numerics.EulerStep Model

/-- The Euler integration family: every integration read as the Euler map of its model's
translated field, with step length its step. -/
def eulerFamily : Family Euler Requirement 2 0 :=
  Numerics.eulerFamily family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization: every integration realizes its swing model. -/
def euler : Implementation Model Requirement Euler Requirement 2 0 2 0 :=
  Numerics.euler family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- **Without a step constraint the Euler realization of the swing family is not sound.** A
locally exponentially stable swing model (`M = 1`, `D = 4`, `K = 4` at a balanced angle) integrated
with a large enough step is not locally exponentially stable: every Euler multiplier `1 + hλ` leaves
the unit disk (`Numerics.not_eulerStep_realizationSoundUnder`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := mem_den_locallyExponentiallyStable ⟨⟨1, 4, 0, 0, 4, 0⟩, 0⟩ one_pos (by norm_num)
    (by simp [SwingParams.Pe]) (by norm_num [SwingParams.syncCoeff])
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerStep_realizationSoundUnder family_isAutonomous
    (fun m => Numerics.contDiff_shift (m.p.contDiff_field (k := 1))) two_pos hm

end powerlib.Synchronous.Swing

namespace powerlib.Synchronous.GeneralSwing

open powerlib.Dynamics (State)

/-- The explicit Euler integration of a swing model with an arbitrary power law about its selected
point with step `h > 0`. -/
abbrev Euler := Numerics.EulerStep Model

/-- The Euler integration family of the swing models with an arbitrary law: every integration read
as the Euler map of its model's translated field, with step length its step. -/
def eulerFamily : Family Euler Spectral.Requirement 2 0 :=
  Numerics.eulerFamily family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The Euler realization of the swing models with an arbitrary law: every integration realizes its
model. -/
def euler : Implementation Model Spectral.Requirement Euler Spectral.Requirement 2 0 2 0 :=
  Numerics.euler family Model.field Numerics.EulerStep.design Numerics.EulerStep.h

/-- The translated swing field is `C¹` near the origin when the power law is `C¹` near the
selected point: the smoothness hypothesis of the local generic Euler laws
(`Numerics.euler_sound_small_step_local`). -/
@[tmio M, powerlib_domain] theorem contDiffAt_field {m : Model}
    (hs : ContDiffAt ℝ 1 (Function.uncurry m.Pe) (m.θ, m.ω)) : ContDiffAt ℝ 1 m.field 0 := by
  refine Numerics.contDiffAt_shift (g := field m.M m.D m.τ m.Pe) (x₀ := m.point) ?_
  have hpt : (m.point 0, m.point 1) = (m.θ, m.ω) := by simp [Model.point]
  have hx : ContDiffAt ℝ 1 (fun x : State 2 => m.Pe (x 0) (x 1)) m.point :=
    ContDiffAt.comp (g := Function.uncurry m.Pe) (f := fun x : State 2 => (x 0, x 1)) m.point
      (by beta_reduce; rw [hpt]; exact hs)
      ((Dynamics.contDiff_coord 0).prodMk (Dynamics.contDiff_coord 1)).contDiffAt
  rw [contDiffAt_euclidean]
  intro i
  fin_cases i
  · simpa [field] using (Dynamics.contDiff_coord (k := 1) 1).contDiffAt (x := m.point)
  · simp only [field, Fin.mk_one, Fin.isValue, PhasePlane.mk_apply_one]
    exact ((contDiffAt_const.sub hx).sub
      (contDiffAt_const.mul (Dynamics.contDiff_coord 1).contDiffAt)).div_const _

/-- **Without a step constraint the Euler realization of the swing models with an arbitrary law is
not sound.** The model `M = D = 1`, `τ = 0`, `P_e(θ, ω) = sin θ` at the origin is locally
exponentially stable (`mem_den_locallyExponentiallyStable_iff_of_sinusoid`); integrated with a
large enough step it is not: every Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_eulerStep_realizationSoundUnder_local`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  set m : Model := ⟨1, 1, 0, fun θ _ => 0 + 1 * Real.sin (θ - 0), 0, 0⟩
  have hs := mem_den_locallyExponentiallyStable_iff_of_sinusoid m 0 1 0 rfl rfl one_pos
  unfold powerlib.TMIO.Statement at hs
  exact Numerics.not_eulerStep_realizationSoundUnder_local family_isAutonomous
    (by norm_num) (contDiffAt_field (m := m)
      (show ContDiffAt ℝ 1 (fun p : ℝ × ℝ => 0 + 1 * Real.sin (p.1 - 0)) (0, 0) by fun_prop))
    (hs.mpr (by norm_num [m]))

end powerlib.Synchronous.GeneralSwing
