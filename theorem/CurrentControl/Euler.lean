import theorem.CurrentControl.VoltageLimit
import theorem.Numerics.EulerRealization

/-! # The explicit Euler integration of the voltage-limited PI current loop: a realization

The voltage-limited PI current-loop platforms (`CurrentControl.LimitedPI.family`,
`theorem/CurrentControl/VoltageLimit.lean`) integrated by the explicit Euler method with a fixed
step `h > 0`: each integration realizes the platform it integrates. The platform field contains
the saturation of the inverter's modulation range, so it is not `C¹` everywhere; with headroom
(`|R i*| < V_dc/√3`) it is the unsaturated design field near the operating point, hence `C¹`
there (`LimitedPI.contDiffAt_field`), and the local laws of the generic template
`theorem/Numerics/EulerRealization.lean` apply to every platform with headroom. A locally
exponentially stable platform with headroom has a step `h₀ > 0` below which its Euler integration
is locally exponentially stable, and without a step constraint the realization is not sound; in
the pattern of `theorem/Synchronous/SwingEuler.lean`. Scaffold: `theorem/EulerDiscretization.agda`.

Model boundary.
* Model layer (M): `LimitedPI.family`, the PI current loop driven through the modulation limit,
  state `(i, ξ)`, read about its operating point `(i*, R i*/Ki)` (continuous time, autonomous, no
  input), with the model boundary of `theorem/CurrentControl/VoltageLimit.lean` (itself an
  implementation layer over the design family `PIParams.family`; here the model its Euler
  integration realizes).
* Implementation layer (I). `LimitedPI.Euler`: a platform and a step `h > 0`; the system is the
  explicit Euler map `z ↦ z + h f(z)` of the platform field translated to the operating point
  (saturation included), with step length `h`, discrete time, exact arithmetic (no round-off),
  fixed step. Excluded: step-size control, implicit or higher-order schemes, the integration
  error against the continuous trajectory, the sampling of the PI controller itself
  (`theorem/CurrentControl/DigitalPI.lean`).
* The laws are stated for platforms with headroom (`family.meets m .headroom`). Without it they
  are not stated: with overload and integral action the saturation is constant near the point,
  which is then not an equilibrium, so no such platform is locally exponentially stable
  (`LimitedPI.mem_den_unstable_of_overload`); on the boundary `|R i*| = V_dc/√3` the saturation
  has its kink at the operating point and the field is not `C¹` there.
* Level: local exponential stability of the operating point.

Source: `theorem/Numerics/EulerRealization.lean` (`euler_sound_small_step_local`,
`euler_certified_small_step_local`, `not_euler_realizationSoundUnder_of_large_step_local`),
`theorem/CurrentControl/VoltageLimit.lean` (`family_isAutonomous`, `contDiffAt_field`,
`mem_den_iff`, `unloaded`); work-sync `theory/T-numerical-integration.md` §1.2, §2.7.

Results.
* No static result beyond the family definitions.

Family and connection conclusions.
* `LimitedPI.eulerFamily : Family LimitedPI.Euler LimitRequirement 2 0`: every integration read as
  its Euler map; requirements and translation are those of its platform, read through the design
  (`meets y = LimitedPI.Meets y.design`). `LimitedPI.euler`: the implementation layer, every
  integration realizing its platform (`Implementation.ofDesign Euler.design`).
* M–I (realization). `LimitedPI.euler_sound_small_step` (scaffold `sound-small-step`): a locally
  exponentially stable platform with headroom (with `L > 0`: `R + Kp > 0`, `Ki > 0`,
  `LimitedPI.mem_den_iff`) has a step `h₀ > 0` such that every Euler integration with a step
  `h ≤ h₀` is locally exponentially stable. `LimitedPI.euler_certified_small_step` (scaffold
  `certified-small-step`): the same for the platform of an integration certified for local
  exponential stability, with headroom. `LimitedPI.not_euler_realizationSoundUnder` (scaffold
  `not-sound-large-step`): without a step constraint the realization is not sound — the unloaded
  platform `LimitedPI.unloaded` (nominal design `L = R = Kp = Ki = 1`, `i* = 0`, `V_dc = 1`) is
  locally exponentially stable with headroom and has Euler integrations with every multiplier
  outside the unit disk.
-/

noncomputable section

namespace powerlib.CurrentControl.LimitedPI

/-- The explicit Euler integration of a voltage-limited platform about its operating point with
step `h > 0`. -/
structure Euler where
  /-- The integrated platform. -/
  design : LimitedPI
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its platform's
translated field, with step length its step. -/
def eulerFamily : Family Euler LimitRequirement 2 0 :=
  Numerics.eulerFamily family field Euler.design Euler.h

/-- The Euler realization: every integration realizes its platform. -/
def euler : Implementation LimitedPI LimitRequirement Euler LimitRequirement 2 0 2 0 :=
  Numerics.euler family field Euler.design Euler.h

/-- **Small steps realize local exponential stability of the platforms with headroom.** A locally
exponentially stable platform with headroom has a step `h₀ > 0` such that its explicit Euler
integration with every step `h ∈ (0, h₀]` is locally exponentially stable. -/
@[powerlib_domain] theorem euler_sound_small_step :
    connection% (∀ m : LimitedPI, family.meets m .headroom →
      m ∈ family.den (.flow .locallyExponentiallyStable) →
        ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
          (⟨m, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro m hr hm
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_sound_small_step_local (design := Euler.design)
    (step := Euler.h) family_isAutonomous (m.contDiffAt_field hr) hm
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨m, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Certified integrations with a small step.** For an Euler integration certified for local
exponential stability (its platform is locally exponentially stable) whose platform has headroom,
every Euler integration of its platform with a step below a threshold is locally exponentially
stable. -/
@[powerlib_domain] theorem euler_certified_small_step :
    connection% (∀ y : Euler, family.meets y.design .headroom →
      y ∈ TMIO.certify euler.realizes (euler.model.den (.flow .locallyExponentiallyStable)) →
        ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h), h ≤ h₀.1 →
          (⟨y.design, h, hh⟩ : Euler) ∈ eulerFamily.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro y hr hy
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.euler_certified_small_step_local family_isAutonomous
    (y.design.contDiffAt_field hr) hy
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨y.design, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **Without a step constraint the Euler realization of the platforms is not sound.** The
unloaded platform (nominal design `L = R = Kp = Ki = 1`, `i* = 0`, `V_dc = 1`: headroom
`0 < 1/√3`) is locally exponentially stable; integrated with a large enough step it is not: every
Euler multiplier `1 + hλ` leaves the unit disk
(`Numerics.not_euler_realizationSoundUnder_of_large_step_local`). -/
@[powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hr : family.meets unloaded .headroom := by
    show |(1 : ℝ) * 0| < 1 / Real.sqrt 3
    rw [mul_zero, abs_zero]
    positivity
  have hm := mem_den_iff unloaded (by norm_num [unloaded, nominal]) hr
    (P := .locallyExponentiallyStable) (Or.inr rfl)
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_euler_realizationSoundUnder_of_large_step_local family_isAutonomous
    (by norm_num) (unloaded.contDiffAt_field hr)
    (hm.mpr ⟨by norm_num [unloaded, nominal], by norm_num [unloaded, nominal]⟩)
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.CurrentControl.LimitedPI
