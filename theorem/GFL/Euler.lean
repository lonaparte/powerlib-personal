import theorem.GFL.RatePLL
import theorem.Numerics.EulerRealization

/-! # The explicit Euler integration of the rate-coupled GFL PLL: a realization

The rate-coupled PLL family (`RatePLL.family`, `theorem/GFL/RatePLL.lean`) integrated by the
explicit Euler method with a fixed step `h > 0` is an implementation layer over it: each
integration realizes the model it integrates. A locally exponentially stable model has a step
`h₀ > 0` below which its Euler integration is locally exponentially stable, and without a step
constraint the realization is not sound; an instance of the generic template
`theorem/Numerics/EulerRealization.lean`, in the pattern of `theorem/Synchronous/SwingEuler.lean`.
Scaffold: `theorem/EulerDiscretization.agda`.

Model boundary.
* Model layer (M): `RatePLL.family`, the rate-coupled PLL with a frozen current, state `(θ, x)`,
  read about its selected point `(θ*, 0)`, with the model boundary of `theorem/GFL/RatePLL.lean`.
* Implementation layer (I). `RatePLL.Euler`: a model and a step `h > 0`; the system is the explicit
  Euler map `z ↦ z + h f(z)` of the translated field, with step length `h`, discrete time, exact
  arithmetic (no round-off), fixed step. Excluded: step-size control, implicit or higher-order
  schemes, the integration error against the continuous trajectory.
* The other grid-following families are instantiated in their directories
  (`theorem/GFL/PowerLoop/Euler.lean`, `theorem/GFL/LCLine/Euler.lean`,
  `theorem/GFL/DCLink/Euler.lean`; the DC-link fields divide by the DC voltage, so they are `C¹`
  only near points with `V_dc ≠ 0`, and use the local laws of the template).
* Level: local exponential stability of the selected point.

Source: `theorem/Numerics/EulerRealization.lean` (`euler_sound_small_step`,
`euler_certified_small_step`, `not_euler_realizationSoundUnder_of_large_step`),
`theorem/GFL/RatePLL.lean` (`contDiff_field`, `mem_den_locallyExponentiallyStable_of_tan_lt`);
work-sync `theory/T-numerical-integration.md` §1.2, §2.7.

Results.
* No static result beyond the family definitions.

Family and connection conclusions.
* `RatePLL.eulerFamily : Family RatePLL.Euler RatePLL.Requirement 2 0`: every integration read as
  its Euler map; requirements and translation are those of its model, read through the design.
  `RatePLL.euler`: the implementation layer, every integration realizing its model
  (`Implementation.ofDesign Euler.design`).
* M–I (realization). `euler_sound_small_step` (scaffold `sound-small-step`): a locally
  exponentially stable model has a step `h₀ > 0` such that every Euler integration with a step
  `h ≤ h₀` is locally exponentially stable. `euler_certified_small_step` (scaffold
  `certified-small-step`): the same for the design of an integration certified for local
  exponential stability. `not_euler_realizationSoundUnder` (scaffold `not-sound-large-step`):
  without a step constraint the realization is not sound — the locally exponentially stable model
  `V = ω_s = k_p = k_i = 1`, `X_g = i_d = 0` at `θ* = 0` has Euler integrations with every
  multiplier outside the unit disk.
-/

noncomputable section

namespace powerlib.GFL.RatePLL

/-- The explicit Euler integration of a rate-coupled PLL model about its selected point with step
`h > 0`. -/
structure Euler where
  /-- The integrated rate-coupled PLL model. -/
  design : Model
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler Requirement 2 0 :=
  Numerics.eulerFamily family Model.field Euler.design Euler.h

/-- The Euler realization: every integration realizes its rate-coupled PLL model. -/
def euler : Implementation Model Requirement Euler Requirement 2 0 2 0 :=
  Numerics.euler family Model.field Euler.design Euler.h

/-- **Small steps realize local exponential stability of the rate-coupled PLL models.** A locally
exponentially stable rate-coupled PLL model has a step `h₀ > 0` such that its explicit Euler
integration with every step `h ∈ (0, h₀]` is locally exponentially stable. -/
@[powerlib_domain] theorem euler_sound_small_step :
    connection% (∀ m : Model, m ∈ family.den (.flow .locallyExponentiallyStable) →
      ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
        (⟨m, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro m hm
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_sound_small_step (design := Euler.design)
    (step := Euler.h) family_isAutonomous Model.field_contDiff hm
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨m, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Certified integrations with a small step.** For an Euler integration certified for local
exponential stability (its rate-coupled PLL model is locally exponentially stable), every Euler
integration of its rate-coupled PLL model with a step below a threshold is locally exponentially
stable. -/
@[powerlib_domain] theorem euler_certified_small_step :
    connection% (∀ y : Euler,
      y ∈ TMIO.certify euler.realizes (euler.model.den (.flow .locallyExponentiallyStable)) →
        ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
          (⟨y.design, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro y hy
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_certified_small_step family_isAutonomous
    Model.field_contDiff hy
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨y.design, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Without a step constraint the Euler realization of the rate-coupled PLL models is not sound.**
A locally exponentially stable model (`V = ω_s = k_p = k_i = 1`, `X_g = i_d = 0` at `θ* = 0`)
integrated with a large enough step is not locally exponentially stable: every Euler multiplier
`1 + hλ` leaves the unit disk (`Numerics.not_euler_realizationSoundUnder_of_large_step`). -/
@[powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := mem_den_locallyExponentiallyStable_of_tan_lt ⟨1, 0, 1, 1, 1, 0⟩ (by norm_num
    [Params.D0])
    one_pos one_pos one_pos (θ := 0) (by simp) (by simp) (by simp)
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_euler_realizationSoundUnder_of_large_step family_isAutonomous
    Model.field_contDiff (by norm_num) hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.GFL.RatePLL
