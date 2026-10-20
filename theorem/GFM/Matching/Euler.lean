import theorem.GFM.Matching.StiffGrid
import theorem.Numerics.EulerRealization

/-! # The explicit Euler integration of the stiff-grid matching closed loop: a realization

The stiff-grid matching family (`MatchingStiffGrid.family`, `theorem/GFM/Matching/StiffGrid.lean`)
integrated by the explicit Euler method with a fixed step `h > 0` is an implementation layer over
it: each integration realizes the model it integrates. A locally exponentially stable model has a
step `h₀ > 0` below which its Euler integration is locally exponentially stable, and without a
step constraint the realization is not sound; an instance of the generic template
`theorem/Numerics/EulerRealization.lean`, in the pattern of `theorem/Synchronous/SwingEuler.lean`.
Scaffold: `theorem/EulerDiscretization.agda`.

Model boundary.
* Model layer (M): `MatchingStiffGrid.family`, the matching closed loop on a stiff grid, state
  `(θ_dq, u_dc, i_d, i_q)`, read about its operating point (`Model.translated`), with the model
  boundary of `theorem/GFM/Matching/StiffGrid.lean`.
* Implementation layer (I). `MatchingStiffGrid.Euler`: a model and a step `h > 0`; the system is
  the explicit Euler map `z ↦ z + h f(z)` of the translated closed-loop field, with step length
  `h`, discrete time, exact arithmetic (no round-off), fixed step. Excluded: step-size control,
  implicit or higher-order schemes, the integration error against the continuous trajectory.
* Not instantiated in this directory: `Matching.matchingFamily` and `Matching.swingFamily`
  (arbitrary current and power laws, so the fields are not `C¹` for every model) and
  `MatchingClosedLoop.fullFamily` (its field is `C¹` only by a lemma private to its module, and
  no member is proved locally exponentially stable).
* Level: local exponential stability of the operating point.

Source: `theorem/Numerics/EulerRealization.lean` (`euler_sound_small_step`,
`euler_certified_small_step`, `not_euler_realizationSoundUnder_of_large_step`),
`theorem/GFM/Matching/StiffGrid.lean` (`field_contDiff`, `mem_den_locallyExponentiallyStable`);
work-sync `theory/T-numerical-integration.md` §1.2, §2.7.

Results.
* No static result beyond the family definitions.

Family and connection conclusions.
* `MatchingStiffGrid.eulerFamily : Family MatchingStiffGrid.Euler Requirement 4 0`: every
  integration read as its Euler map; requirements and translation are those of its model, read
  through the design. `MatchingStiffGrid.euler`: the implementation layer, every integration
  realizing its model (`Implementation.ofDesign Euler.design`).
* M–I (realization). `euler_sound_small_step` (scaffold `sound-small-step`): a locally
  exponentially stable model has a step `h₀ > 0` such that every Euler integration with a step
  `h ≤ h₀` is locally exponentially stable. `euler_certified_small_step` (scaffold
  `certified-small-step`): the same for the design of an integration certified for local
  exponential stability. `not_euler_realizationSoundUnder` (scaffold `not-sound-large-step`):
  without a step constraint the realization is not sound — the locally exponentially stable model
  with unit parameters and `K_p = 0` (`margin = 7/8`) has Euler integrations with every multiplier
  outside the unit disk.
-/

noncomputable section

namespace powerlib.GFM.Matching.MatchingStiffGrid

/-- The explicit Euler integration of a stiff-grid matching model about its operating point with
step `h > 0`. -/
structure Euler where
  /-- The integrated stiff-grid matching model. -/
  design : Model
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler Requirement 4 0 :=
  Numerics.eulerFamily family Model.translated Euler.design Euler.h

/-- The Euler realization: every integration realizes its stiff-grid matching model. -/
def euler : Implementation Model Requirement Euler Requirement 4 0 4 0 :=
  Numerics.euler family Model.translated Euler.design Euler.h

/-- The translated field is `C¹`. -/
private theorem contDiff_modelField (m : Model) : ContDiff ℝ 1 (Model.translated m) :=
  (field_contDiff m).comp (contDiff_id.add contDiff_const)

/-- **Small steps realize local exponential stability of the stiff-grid matching models.** A locally
exponentially stable stiff-grid matching model has a step `h₀ > 0` such that its explicit Euler
integration with every step `h ∈ (0, h₀]` is locally exponentially stable. -/
@[powerlib_domain] theorem euler_sound_small_step :
    connection% (∀ m : Model, m ∈ family.den (.flow .locallyExponentiallyStable) →
      ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
        (⟨m, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro m hm
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_sound_small_step (design := Euler.design)
    (step := Euler.h) (fun _ => rfl : family.IsAutonomous Model.translated) contDiff_modelField hm
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨m, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Certified integrations with a small step.** For an Euler integration certified for local
exponential stability (its stiff-grid matching model is locally exponentially stable), every Euler
integration of its stiff-grid matching model with a step below a threshold is locally exponentially
stable. -/
@[powerlib_domain] theorem euler_certified_small_step :
    connection% (∀ y : Euler,
      y ∈ TMIO.certify euler.realizes (euler.model.den (.flow .locallyExponentiallyStable)) →
        ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
          (⟨y.design, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro y hy
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_certified_small_step (fun _ => rfl : family.IsAutonomous
    Model.translated) contDiff_modelField hy
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨y.design, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Without a step constraint the Euler realization of the stiff-grid matching models is not
sound.** A locally exponentially stable model (`C_dc = G_dc = η = μ = u*_dc = v₀ = R_s = L_s = 1`,
`K_p = 0`: `margin = 7/8 > 0`) integrated with a large enough step is not locally exponentially
stable: every Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_euler_realizationSoundUnder_of_large_step`). -/
@[powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := mem_den_locallyExponentiallyStable ⟨1, 1, 0, 1, 1, 1, 1, 1, 1⟩ one_pos one_pos one_pos
    (by norm_num) one_ne_zero (by norm_num [Model.margin, Model.ω0, Model.N])
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_euler_realizationSoundUnder_of_large_step
    (fun _ => rfl : family.IsAutonomous Model.translated)
    contDiff_modelField (by norm_num) hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.GFM.Matching.MatchingStiffGrid
