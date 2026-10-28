import theorem.GFL.PowerLoop.QuasiStaticFold
import theorem.Numerics.EulerRealization

/-! # The explicit Euler integration of the quasi-static GFL power loop: a realization

The quasi-static three-state GFL family (`QuasiStatic.family`,
`theorem/GFL/PowerLoop/QuasiStatic.lean`) integrated by the explicit Euler method with a fixed step
`h > 0` is an implementation layer over it: each integration realizes the model it integrates. A
locally exponentially stable model has a step `h₀ > 0` below which its Euler integration is
locally exponentially stable, and without a step constraint the realization is not sound; an
instance of the generic template `theorem/Numerics/EulerRealization.lean`, in the pattern of
`theorem/Synchronous/SwingEuler.lean`. Scaffold: `theorem/EulerDiscretization.agda`.

Model boundary.
* Model layer (M): `QuasiStatic.family`, PLL and dispatch loop with a quasi-static network, state
  `(θ, x, i_d)`, read about its selected point `(θ*, 0, i_d*)`, with the model boundary of
  `theorem/GFL/PowerLoop/QuasiStatic.lean`.
* Implementation layer (I). `QuasiStatic.Euler`: a model and a step `h > 0`; the system is the
  explicit Euler map `z ↦ z + h f(z)` of the translated field, with step length `h`, discrete time,
  exact arithmetic (no round-off), fixed step. Excluded: step-size control, implicit or
  higher-order schemes, the integration error against the continuous trajectory.
* Level: local exponential stability of the selected point.

Source: `theorem/Numerics/EulerRealization.lean` (`euler_sound_small_step`,
`euler_certified_small_step`, `not_euler_realizationSoundUnder_of_large_step`),
`theorem/GFL/PowerLoop/QuasiStatic.lean` (`mem_den_locallyExponentiallyStable_of_abs_lt`),
`theorem/GFL/PowerLoop/QuasiStaticFold.lean` (`contDiff_model_field`); work-sync
`theory/T-numerical-integration.md` §1.2, §2.7.

Results.
* No static result beyond the family definitions.

Family and connection conclusions.
* `QuasiStatic.eulerFamily : Family QuasiStatic.Euler QuasiStatic.Requirement 3 0`: every
  integration read as its Euler map; requirements and translation are those of its model, read
  through the design. `QuasiStatic.euler`: the implementation layer, every integration realizing
  its model (`Implementation.ofDesign Euler.design`).
* M–I (realization). The small-step laws are the generic connection laws applied to the family,
  with its autonomy `QuasiStatic.family_isAutonomous` and the public smoothness lemma
  `QuasiStatic.contDiff_model_field`: `Numerics.euler_sound_small_step` (scaffold
  `sound-small-step`: a locally exponentially stable model has a step `h₀ > 0` such that every
  Euler integration with a step `h ≤ h₀` is locally exponentially stable) and
  `Numerics.euler_certified_small_step` (scaffold `certified-small-step`).
  `not_euler_realizationSoundUnder` (scaffold `not-sound-large-step`):
  without a step constraint the realization is not sound — the locally exponentially stable model
  `V = k_p = k_i = k_P = 1`, `X_g = P_ref = 0` at `θ* = i_d* = 0` has Euler integrations with every
  multiplier outside the unit disk.
-/

noncomputable section

namespace powerlib.GFL.PowerLoop.QuasiStatic

/-- The explicit Euler integration of a quasi-static GFL model about its selected point with step
`h > 0`. -/
structure Euler where
  /-- The integrated quasi-static GFL model. -/
  design : Model
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler Requirement 3 0 :=
  Numerics.eulerFamily family Model.field Euler.design Euler.h

/-- The Euler realization: every integration realizes its quasi-static GFL model. -/
def euler : Implementation Model Requirement Euler Requirement 3 0 3 0 :=
  Numerics.euler family Model.field Euler.design Euler.h

/-- **Without a step constraint the Euler realization of the quasi-static GFL models is not sound.**
A locally exponentially stable model (`V = k_p = k_i = k_P = 1`, `X_g = P_ref = 0` at
`θ* = i_d* = 0`) integrated with a large enough step is not locally exponentially stable: every
Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_euler_realizationSoundUnder_of_large_step`). -/
@[tmio MI, powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := mem_den_locallyExponentiallyStable_of_abs_lt ⟨1, 0, 1, 1, 1, 0⟩ one_pos one_pos one_pos
    one_pos (θ := 0) (Id := 0) ⟨by simp, by simp [power]⟩ (by simp [Real.pi_pos])
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_euler_realizationSoundUnder_of_large_step family_isAutonomous
    contDiff_model_field (by norm_num) hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.GFL.PowerLoop.QuasiStatic
