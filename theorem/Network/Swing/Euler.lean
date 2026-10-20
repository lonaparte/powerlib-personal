import theorem.Network.Swing.Basic
import theorem.Numerics.EulerRealization

/-! # The explicit Euler integration of the swing network: a realization

The swing-network family (`Network.Swing.family`, `theorem/Network/Swing/Basic.lean`, `n + 1`
machines in relative-angle coordinates) integrated by the explicit Euler method with a fixed step
`h > 0` is an implementation layer over it: each integration realizes the model it integrates. A
locally exponentially stable model has a step `h₀ > 0` below which its Euler integration is
locally exponentially stable, and without a step constraint the realization is not sound; an
instance of the generic template `theorem/Numerics/EulerRealization.lean`, in the pattern of
`theorem/Synchronous/SwingEuler.lean`. Scaffold: `theorem/EulerDiscretization.agda`.

Model boundary.
* Model layer (M): `Network.Swing.family`, the reduced swing network (relative angles and
  frequencies, positive inertia and damping), read about its selected angle profile `θ*`, with the
  model boundary of `theorem/Network/Swing/Basic.lean`.
* Implementation layer (I). `Network.Swing.Euler n`: a model and a step `h > 0`; the system is the
  explicit Euler map `z ↦ z + h f(z)` of the translated reduced field, with step length `h`,
  discrete time, exact arithmetic (no round-off), fixed step. Excluded: step-size control,
  implicit or higher-order schemes, the integration error against the continuous trajectory.
* Level: local exponential stability of the selected point.

Source: `theorem/Numerics/EulerRealization.lean` (`euler_sound_small_step`,
`euler_certified_small_step`, `not_euler_realizationSoundUnder_of_large_step`),
`theorem/Network/Swing/Basic.lean` (`reducedField_contDiff`, `mem_den_locallyExponentiallyStable`);
work-sync `theory/T-numerical-integration.md` §1.2, §2.7.

Results.
* No static result beyond the family definitions.

Family and connection conclusions.
* `Network.Swing.eulerFamily : Family (Network.Swing.Euler n) Requirement (n + (n + 1)) 0`: every
  integration read as its Euler map; requirements and translation are those of its model, read
  through the design. `Network.Swing.euler`: the implementation layer, every integration realizing
  its model (`Implementation.ofDesign Euler.design`).
* M–I (realization), for every number `n + 1` of machines. `euler_sound_small_step` (scaffold
  `sound-small-step`): a locally exponentially stable model has a step `h₀ > 0` such that every
  Euler integration with a step `h ≤ h₀` is locally exponentially stable.
  `euler_certified_small_step` (scaffold `certified-small-step`): the same for the design of an
  integration certified for local exponential stability. `not_euler_realizationSoundUnder`
  (scaffold `not-sound-large-step`): without a step constraint the realization is not sound — the
  locally exponentially stable network with unit inertia, damping and coupling, no injection and
  `θ* = 0` has Euler integrations with every multiplier outside the unit disk.
-/

noncomputable section

namespace powerlib.Network.Swing

variable {n : ℕ}

/-- The explicit Euler integration of a swing-network model about its selected angle profile with
step `h > 0`. -/
structure Euler (n : ℕ) where
  /-- The integrated swing-network model. -/
  design : (Model n)
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its model's translated
field, with step length its step. -/
def eulerFamily : Family (Euler n) Requirement (n + (n + 1)) 0 :=
  Numerics.eulerFamily family Model.field Euler.design Euler.h

/-- The Euler realization: every integration realizes its swing-network model. -/
def euler : Implementation (Model n) Requirement (Euler n) Requirement (n + (n + 1)) 0 (n + (n +
    1)) 0 :=
  Numerics.euler family Model.field Euler.design Euler.h

/-- The translated field is `C¹`. -/
private theorem contDiff_modelField (m : (Model n)) : ContDiff ℝ 1 (Model.field m) :=
  (reducedField_contDiff m.params).comp (contDiff_id.add contDiff_const)

/-- **Small steps realize local exponential stability of the swing-network models.** A locally
exponentially stable swing-network model has a step `h₀ > 0` such that its explicit Euler
integration with every step `h ∈ (0, h₀]` is locally exponentially stable. -/
@[powerlib_domain] theorem euler_sound_small_step :
    connection% (∀ m : (Model n), m ∈ family.den (.flow .locallyExponentiallyStable) →
      ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
        (⟨m, h, hh⟩ : (Euler n)) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro m hm
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_sound_small_step (design := Euler.design)
    (step := Euler.h) family_isAutonomous contDiff_modelField hm
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨m, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Certified integrations with a small step.** For an Euler integration certified for local
exponential stability (its swing-network model is locally exponentially stable), every Euler
integration of its swing-network model with a step below a threshold is locally exponentially
stable. -/
@[powerlib_domain] theorem euler_certified_small_step :
    connection% (∀ y : (Euler n),
      y ∈ TMIO.certify euler.realizes (euler.model.den (.flow .locallyExponentiallyStable)) →
        ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
          (⟨y.design, h, hh⟩ : (Euler n)) ∈
            eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro y hy
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_certified_small_step family_isAutonomous
    contDiff_modelField hy
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨y.design, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Without a step constraint the Euler realization of the swing-network models is not sound.** A
locally exponentially stable network (unit inertia and damping, no injection, unit coupling between
every pair of machines, `θ* = 0`) integrated with a large enough step is not locally exponentially
stable: every Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_euler_realizationSoundUnder_of_large_step`). -/
@[powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ (euler (n := n)).RealizationSoundUnder ∅
      (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := mem_den_locallyExponentiallyStable (n := n)
    ⟨⟨fun _ => 1, fun _ => 1, fun _ => 0, fun _ _ => 1, fun _ => one_pos, fun _ => one_pos,
      fun _ _ => rfl, fun _ _ => zero_le_one⟩, fun _ => 0⟩
    (fun _ => by simp [powerInjection]) (fun _ _ _ => by simp [Real.pi_pos])
    (fun _ _ => .single one_pos)
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_euler_realizationSoundUnder_of_large_step family_isAutonomous
    contDiff_modelField (by omega) hm fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.Network.Swing
