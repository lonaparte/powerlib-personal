import theorem.Limiting.Saturation
import theorem.Numerics.EulerRealization

/-! # The explicit Euler integration of the saturated grid-forming converter: a realization

The saturated-GFM family (`Limiting.family`, `theorem/Limiting/Saturation.lean`) integrated by the
explicit Euler method with a fixed step `h > 0` is an implementation layer over it: each
integration realizes the model it integrates. A locally exponentially stable model has a step
`h₀ > 0` below which its Euler integration is locally exponentially stable, and without a step
constraint the realization is not sound; an instance of the generic template
`theorem/Numerics/EulerRealization.lean`, in the pattern of `theorem/Synchronous/SwingEuler.lean`.
Scaffold: `theorem/EulerDiscretization.agda`.

Model boundary.
* Model layer (M): `Limiting.family`, the swing-type outer loop of a GFM converter in current
  saturation (`P_e = P_sat cos(δ − φ)`), state `(δ, ω)`, read about its selected point `(δ*, 0)`
  (a local spectral family), with the model boundary of `theorem/Limiting/Saturation.lean`.
* Implementation layer (I). `Limiting.Euler`: a model and a step `h > 0`; the system is the
  explicit Euler map `z ↦ z + h f(z)` of the translated saturated field, with step length `h`,
  discrete time, exact arithmetic (no round-off), fixed step. Excluded: step-size control,
  implicit or higher-order schemes, the integration error against the continuous trajectory.
* Level: local exponential stability of the selected point.

Source: `theorem/Numerics/EulerRealization.lean` (`euler_sound_small_step`,
`euler_certified_small_step`, `not_euler_realizationSoundUnder_of_large_step`),
`theorem/Limiting/Saturation.lean` (`satField_contDiff`, `saturated_stable_equilibrium`);
work-sync `theory/T-numerical-integration.md` §1.2, §2.7.

Results.
* No static result beyond the family definitions.

Family and connection conclusions.
* `Limiting.eulerFamily : Family Limiting.Euler Spectral.Requirement 2 0`: every integration read
  as its Euler map; requirements and translation are those of its model, read through the design.
  `Limiting.euler`: the implementation layer, every integration realizing its model
  (`Implementation.ofDesign Euler.design`).
* M–I (realization). `euler_sound_small_step` (scaffold `sound-small-step`): a locally
  exponentially stable model has a step `h₀ > 0` such that every Euler integration with a step
  `h ≤ h₀` is locally exponentially stable. `euler_certified_small_step` (scaffold
  `certified-small-step`): the same for the design of an integration certified for local
  exponential stability. `not_euler_realizationSoundUnder` (scaffold `not-sound-large-step`):
  without a step constraint the realization is not sound — the stable saturated equilibrium with
  `M = D = P_sat = 1`, `P_ref = φ = 0` has Euler integrations with every multiplier outside the
  unit disk.
-/

noncomputable section

namespace powerlib.Limiting

/-- The explicit Euler integration of a saturated GFM model about its selected angle with step
`h > 0`. -/
structure Euler where
  /-- The integrated saturated GFM model. -/
  design : SatModel
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family Euler Spectral.Requirement 2 0 :=
  Numerics.eulerFamily family SatModel.field Euler.design Euler.h

/-- The Euler realization: every integration realizes its saturated GFM model. -/
def euler : Implementation SatModel Spectral.Requirement Euler Spectral.Requirement 2 0 2 0 :=
  Numerics.euler family SatModel.field Euler.design Euler.h

/-- The translated field is `C¹`. -/
private theorem contDiff_modelField (m : SatModel) : ContDiff ℝ 1 (SatModel.field m) :=
  (satField_contDiff _ _ _ _ _).comp (contDiff_id.add contDiff_const)

/-- **Small steps realize local exponential stability of the saturated GFM models.** A locally
exponentially stable saturated GFM model has a step `h₀ > 0` such that its explicit Euler
integration with every step `h ∈ (0, h₀]` is locally exponentially stable. -/
@[powerlib_domain] theorem euler_sound_small_step :
    connection% (∀ m : SatModel, m ∈ family.den (.flow .locallyExponentiallyStable) →
      ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
        (⟨m, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro m hm
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_sound_small_step (design := Euler.design)
    (step := Euler.h) (Spectral.localFamily_isAutonomous _ _ _) contDiff_modelField hm
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨m, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Certified integrations with a small step.** For an Euler integration certified for local
exponential stability (its saturated GFM model is locally exponentially stable), every Euler
integration of its saturated GFM model with a step below a threshold is locally exponentially
stable. -/
@[powerlib_domain] theorem euler_certified_small_step :
    connection% (∀ y : Euler,
      y ∈ TMIO.certify euler.realizes (euler.model.den (.flow .locallyExponentiallyStable)) →
        ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
          (⟨y.design, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro y hy
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_certified_small_step (Spectral.localFamily_isAutonomous _
    _ _) contDiff_modelField hy
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨y.design, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Without a step constraint the Euler realization of the saturated GFM models is not sound.**
The stable saturated equilibrium with `M = D = P_sat = 1`, `P_ref = φ = 0` integrated with a large
enough step is not locally exponentially stable: every Euler multiplier `1 + hλ` leaves the unit
disk (`Numerics.not_euler_realizationSoundUnder_of_large_step`). -/
@[powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := saturated_stable_equilibrium (M := 1) (D := 1) (Pref := 0) (Psat := 1) (φ := 0) one_pos
    one_pos one_pos (by norm_num)
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_euler_realizationSoundUnder_of_large_step
    (Spectral.localFamily_isAutonomous _ _ _)
    contDiff_modelField (by norm_num) hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.Limiting
