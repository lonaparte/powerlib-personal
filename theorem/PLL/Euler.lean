import theorem.PLL.PIPLLFamily
import theorem.PLL.Multiscale
import theorem.Numerics.EulerRealization

/-! # The explicit Euler integration of the PLL families: realizations

The PI-PLL family (`PLL.PIPLL.family`, `theorem/PLL/PIPLLFamily.lean`) and the reduced slow SRF-PLL
family (`PLL.ReducedSlow.family`, `theorem/PLL/Multiscale.lean`) integrated by the explicit Euler
method with a fixed step `h > 0` are implementation layers over them: each integration realizes the
model it integrates, and a locally exponentially stable model has a step `h₀ > 0` below which its
Euler integration is locally exponentially stable; instances of the generic template
`theorem/Numerics/EulerRealization.lean`, in the pattern of `theorem/Synchronous/SwingEuler.lean`.
Scaffold: `theorem/EulerDiscretization.agda`.

Model boundary.
* Model layer (M): `PLL.PIPLL.family`, the PI-PLL with a `C¹` phase-detector characteristic, state
  `(θ, η)`, read about its selected point (`theorem/PLL/PIPLLFamily.lean`);
  `PLL.ReducedSlow.family`, the one-state linear reduced slow model `ẏ = −(b/a) y` about the origin
  (`theorem/PLL/Multiscale.lean`); each with the model boundary of its module.
* Implementation layer (I). `PIPLL.Euler`, `ReducedSlow.Euler`: a model and a step `h > 0`; the
  system is the explicit Euler map `z ↦ z + h f(z)` of the model's (translated) field, with step
  length `h`, discrete time, exact arithmetic (no round-off), fixed step. Excluded: step-size
  control, implicit or higher-order schemes, the integration error against the continuous
  trajectory.
* Level: local exponential stability of the selected point.

Source: `theorem/Numerics/EulerRealization.lean` (`euler_sound_small_step`,
`euler_certified_small_step`, `not_euler_realizationSoundUnder_of_large_step`),
`theorem/PLL/PIPLL.lean` (`contDiff_piPLLField`), `theorem/PLL/PIPLLFamily.lean`
(`srf_mem_den_locallyExponentiallyStable`), `theorem/PLL/Multiscale.lean` (`chain_le_semantics`),
`theorem/Linear/Stability.lean` (`Linear.affine_contDiff`); work-sync
`theory/T-numerical-integration.md` §1.2, §2.7.

Results.
* No static result beyond the family definitions.

Family and connection conclusions.
* `PIPLL.eulerFamily : Family PIPLL.Euler PIPLL.Requirement 2 0` and
  `ReducedSlow.eulerFamily : Family ReducedSlow.Euler ReducedSlow.Requirement 1 0`: every
  integration read as its Euler map; requirements and translation are those of its model, read
  through the design. `PIPLL.euler`, `ReducedSlow.euler`: the implementation layers, every
  integration realizing its model (`Implementation.ofDesign Euler.design`).
* M–I (realization), for both families. `euler_sound_small_step` (scaffold `sound-small-step`): a
  locally exponentially stable model has a step `h₀ > 0` such that every Euler integration with a
  step `h ≤ h₀` is locally exponentially stable. `euler_certified_small_step` (scaffold
  `certified-small-step`): the same for the design of an integration certified for local
  exponential stability. `not_euler_realizationSoundUnder` (scaffold `not-sound-large-step`):
  without a step constraint the realization is not sound — for the PI-PLL the SRF detector with
  `V = K_p = K_i = 1` at `θ* = 0`, for the reduced slow model `a = b = 1` (`ẏ = −y`), each locally
  exponentially stable with Euler integrations having every multiplier outside the unit disk.
-/

noncomputable section

namespace powerlib.PLL.PIPLL

/-- The explicit Euler integration of a PI-PLL model about its selected point with step `h > 0`. -/
structure Euler where
  /-- The integrated PI-PLL model. -/
  design : Model
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler Requirement 2 0 :=
  Numerics.eulerFamily family Model.field Euler.design Euler.h

/-- The Euler realization: every integration realizes its PI-PLL model. -/
def euler : Implementation Model Requirement Euler Requirement 2 0 2 0 :=
  Numerics.euler family Model.field Euler.design Euler.h

/-- The translated field is `C¹`. -/
private theorem contDiff_modelField (m : Model) : ContDiff ℝ 1 (Model.field m) :=
  (contDiff_piPLLField m.smooth).comp (contDiff_id.add contDiff_const)

/-- **Small steps realize local exponential stability of the PI-PLL models.** A locally
exponentially stable PI-PLL model has a step `h₀ > 0` such that its explicit Euler integration with
every step `h ∈ (0, h₀]` is locally exponentially stable. -/
@[powerlib_domain] theorem euler_sound_small_step :
    connection% (∀ m : Model, m ∈ family.den (.flow .locallyExponentiallyStable) →
      ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
        (⟨m, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro m hm
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_sound_small_step (design := Euler.design)
    (step := Euler.h) family_isAutonomous contDiff_modelField hm
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨m, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Certified integrations with a small step.** For an Euler integration certified for local
exponential stability (its PI-PLL model is locally exponentially stable), every Euler integration of
its PI-PLL model with a step below a threshold is locally exponentially stable. -/
@[powerlib_domain] theorem euler_certified_small_step :
    connection% (∀ y : Euler,
      y ∈ TMIO.certify euler.realizes (euler.model.den (.flow .locallyExponentiallyStable)) →
        ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
          (⟨y.design, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro y hy
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_certified_small_step family_isAutonomous
    contDiff_modelField hy
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨y.design, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Without a step constraint the Euler realization of the PI-PLL models is not sound.** A locally
exponentially stable PI-PLL (the SRF detector `h = −V sin` with `V = K_p = K_i = 1`, `δω = 0`, at
`θ* = 0`) integrated with a large enough step is not locally exponentially stable: every Euler
multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_euler_realizationSoundUnder_of_large_step`). -/
@[powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := srf_mem_den_locallyExponentiallyStable one_pos one_pos one_pos 0
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_euler_realizationSoundUnder_of_large_step family_isAutonomous
    contDiff_modelField (by norm_num) hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.PLL.PIPLL

namespace powerlib.PLL.ReducedSlow

/-- The explicit Euler integration of a reduced slow PLL model about the origin with step
`h > 0`. -/
structure Euler where
  /-- The integrated reduced slow PLL model. -/
  design : Model
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its model's field, with
step length its step. -/
def eulerFamily : Family Euler Requirement 1 0 :=
  Numerics.eulerFamily family Model.field Euler.design Euler.h

/-- The Euler realization: every integration realizes its reduced slow PLL model. -/
def euler : Implementation Model Requirement Euler Requirement 1 0 1 0 :=
  Numerics.euler family Model.field Euler.design Euler.h

/-- The field is `C¹`. -/
private theorem contDiff_modelField (m : Model) : ContDiff ℝ 1 (Model.field m) :=
  Linear.affine_contDiff _ _

/-- **Small steps realize local exponential stability of the reduced slow PLL models.** A locally
exponentially stable reduced slow PLL model has a step `h₀ > 0` such that its explicit Euler
integration with every step `h ∈ (0, h₀]` is locally exponentially stable. -/
@[powerlib_domain] theorem euler_sound_small_step :
    connection% (∀ m : Model, m ∈ family.den (.flow .locallyExponentiallyStable) →
      ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
        (⟨m, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro m hm
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_sound_small_step (design := Euler.design)
    (step := Euler.h) family_isAutonomous contDiff_modelField hm
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨m, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Certified integrations with a small step.** For an Euler integration certified for local
exponential stability (its reduced slow PLL model is locally exponentially stable), every Euler
integration of its reduced slow PLL model with a step below a threshold is locally exponentially
stable. -/
@[powerlib_domain] theorem euler_certified_small_step :
    connection% (∀ y : Euler,
      y ∈ TMIO.certify euler.realizes (euler.model.den (.flow .locallyExponentiallyStable)) →
        ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
          (⟨y.design, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro y hy
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_certified_small_step family_isAutonomous
    contDiff_modelField hy
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨y.design, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Without a step constraint the Euler realization of the reduced slow PLL models is not
sound.** The locally exponentially stable model `a = b = 1` (`ẏ = −y`) integrated with a large
enough step is not locally exponentially stable: its Euler multiplier `1 − h` leaves the unit disk
(`Numerics.not_euler_realizationSoundUnder_of_large_step`). -/
@[powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hc := chain_le_semantics
  unfold powerlib.TMIO.Statement at hc
  have hm : (⟨1, 1⟩ : Model) ∈ family.den (.flow .locallyExponentiallyStable) :=
    Family.chain_le_semantics_iff.mp hc _ ((TMIO.mem_realize _ _ _).mpr fun q hq => by
      rw [Set.mem_singleton_iff.mp hq]
      show (0 : ℝ) < 1 / 1
      norm_num)
  exact Numerics.not_euler_realizationSoundUnder_of_large_step family_isAutonomous
    contDiff_modelField one_pos hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.PLL.ReducedSlow
