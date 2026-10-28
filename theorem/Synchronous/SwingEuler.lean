import theorem.Synchronous.Swing
import theorem.Numerics.EulerRealization

/-! # The explicit Euler integration of the swing equation: a realization

The swing family (`Swing.family`, `theorem/Synchronous/Swing.lean`) integrated by the explicit
Euler method with a fixed step `h > 0` is an implementation layer over it: each integration
realizes the swing model it integrates. A locally exponentially stable swing model has a step
`h₀ > 0` below which its Euler integration is locally exponentially stable, and without a step
constraint the realization is not sound; the instance of the generic template
`theorem/Numerics/EulerRealization.lean`. Scaffold: `theorem/EulerDiscretization.agda`.

Model boundary.
* Model layer (M): `Swing.family`, the swing model `M δ̈ + D δ̇ = P_m − (k₁ + k₂ sin(δ − k₃))` read
  about its selected point `(δ*, 0)` (state `z = (δ − δ*, ω)`, continuous time, autonomous, no
  input), with the model boundary of `theorem/Synchronous/Swing.lean`.
* Implementation layer (I). `Swing.Euler`: a swing model and a step `h > 0`; the system is the
  explicit Euler map `z ↦ z + h f(z)` of the translated swing field (the Euler integration of the
  swing equation from `(δ, ω)`, read about `(δ*, 0)`), with step length `h`, discrete time, exact
  arithmetic (no round-off), fixed step. Excluded: step-size control, implicit or higher-order
  schemes, the integration error against the continuous trajectory.
* Level: local exponential stability of the selected point.

Source: `theorem/Numerics/EulerRealization.lean` (`euler_sound_small_step`,
`euler_certified_small_step`, `not_euler_realizationSoundUnder_of_large_step`),
`theorem/Synchronous/Swing.lean` (`family_isAutonomous`, `SwingParams.contDiff_field`,
`mem_den_locallyExponentiallyStable`); work-sync `theory/T-numerical-integration.md` §1.2, §2.7.

Results.
* `Swing.contDiff_modelField`: the translated swing field is `C¹` (from
  `SwingParams.contDiff_field`), the smoothness hypothesis of the generic laws.

Family and connection conclusions.
* `Swing.eulerFamily : Family Swing.Euler Requirement 2 0`: every integration read as its Euler
  map; requirements and translation are those of its swing model, read through the design
  (`meets y = Swing.Meets y.design`). `Swing.euler`: the implementation layer, every integration
  realizing its swing model (`Implementation.ofDesign Euler.design`).
* M–I (realization). The small-step laws are the generic connection laws applied to the family,
  with its autonomy `Swing.family_isAutonomous` and the public smoothness lemma
  `Swing.contDiff_modelField`: `Numerics.euler_sound_small_step` (scaffold `sound-small-step`: a
  locally exponentially stable swing model — for instance a balanced angle with positive inertia,
  damping and synchronizing coefficient, `Swing.mem_den_locallyExponentiallyStable` — has a step
  `h₀ > 0` such that every Euler integration with a step `h ≤ h₀` is locally exponentially
  stable) and `Numerics.euler_certified_small_step` (scaffold `certified-small-step`: the same for
  the design of an integration certified for local exponential stability).
  `not_euler_realizationSoundUnder`
  (scaffold `not-sound-large-step`): without a step constraint the realization is not sound — the
  locally exponentially stable model `M = 1`, `D = 4`, `K = 4` at a balanced angle has Euler
  integrations with every Euler multiplier outside the unit disk (`h = 3`: both at `−5`; the
  generic law `Numerics.not_euler_realizationSoundUnder_of_large_step`).
-/

noncomputable section

namespace powerlib.Synchronous.Swing

/-- The explicit Euler integration of a swing model about its selected point with step `h > 0`. -/
structure Euler where
  /-- The integrated swing model. -/
  design : Model
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its model's
translated field, with step length its step. -/
def eulerFamily : Family Euler Requirement 2 0 :=
  Numerics.eulerFamily family Model.field Euler.design Euler.h

/-- The Euler realization: every integration realizes its swing model. -/
def euler : Implementation Model Requirement Euler Requirement 2 0 2 0 :=
  Numerics.euler family Model.field Euler.design Euler.h

/-- The translated swing field is `C¹`: the smoothness hypothesis of the generic Euler laws
(`Numerics.euler_sound_small_step`). -/
@[powerlib_foundation] theorem contDiff_modelField (m : Model) : ContDiff ℝ 1 m.field :=
  (m.p.contDiff_field (k := 1)).comp (contDiff_id.add contDiff_const)

/-- **Without a step constraint the Euler realization of the swing family is not sound.** A
locally exponentially stable swing model (`M = 1`, `D = 4`, `K = 4` at a balanced angle) integrated
with a large enough step is not locally exponentially stable: every Euler multiplier `1 + hλ` leaves
the unit disk (`Numerics.not_euler_realizationSoundUnder_of_large_step`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := mem_den_locallyExponentiallyStable ⟨⟨1, 4, 0, 0, 4, 0⟩, 0⟩ one_pos (by norm_num)
    (by simp [SwingParams.Pe]) (by norm_num [SwingParams.syncCoeff])
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_euler_realizationSoundUnder_of_large_step family_isAutonomous
    contDiff_modelField two_pos hm fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.Synchronous.Swing
