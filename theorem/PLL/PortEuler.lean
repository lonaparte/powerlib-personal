import theorem.PLL.PH
import theorem.Numerics.EulerPorts

/-! # The explicit Euler discretization of the SRF-PLL as a port-Hamiltonian system

The SRF-PLL pH family `PLL.PLLPH.family` of `theorem/PLL/PH.lean` (frequency-offset port, output
the phase-detector characteristic `h(θ) = −V sin θ`) discretized by the explicit Euler method with
a fixed step `h > 0`, with its port: each discretization realizes the model it is designed from;
the generic template is `theorem/Numerics/EulerPorts.lean`. The zero-input field is the smooth
SRF-PLL field, so local exponential stability is realized below a step threshold and not without
a step constraint. Passivity is not: the output `−V sin θ` does not depend on the input, so for
`V ≠ 0` one Euler step with a large offset draws energy without bound; a discretization is
passive exactly when the grid is dead (`V = 0`, zero output). Scaffold:
`theorem/EulerPorts.agda`.

Model boundary.
* Model layer (M): `PLLPH.family` (state `(θ_e, η)` centred at the selected point `(θ*, η*)`,
  input the deviation of the frequency offset from `K_i η*`, output `h(θ)`; `V`, `K_p ≥ 0`, `K_i`
  free), continuous time, with the model boundary, requirements and translation of
  `theorem/PLL/PH.lean`.
* Implementation layer (I): `PLLPH.Euler`, a model and a step `h > 0`; the system is the explicit
  Euler discretization `x⁺ = x + h ((J − R) ∇H(x) + B u)` of the centred pH port system with the
  same output (the input held over the step), step length `h`, discrete time, exact arithmetic,
  fixed step. Excluded: step-size control, implicit or discrete-gradient schemes, the integration
  error against the continuous trajectory.
* Level: local exponential stability of the selected point; passivity of the discretized port
  system.

Source: `theorem/Numerics/EulerPorts.lean` (`eulerPorts_sound_small_step_local`,
`not_eulerPorts_realizationSoundUnder_of_large_step_local`,
`eulerPortFamily_not_mem_den_passive`, `not_eulerPorts_realizationSoundUnder_passive`,
`Family.IsNonlinearPH.isPort`), `theorem/Numerics/EulerRealization.lean` (`contDiffAt_shift`),
`theorem/PLL/Model.lean` (`contDiff_srfField`), `theorem/PLL/PH.lean` (`pllPH_zeroInputField`,
`pllPH_output`, members); work-sync `theory/T-numerical-integration.md` §1.2, §2.7,
`theory/T-pll-ph.md` §1.2.

Results.
* `PLLPH.contDiffAt_zeroInput`: the centred zero-input field is `C¹` near the origin, the
  smoothness hypothesis of the generic laws.

Family and connection conclusions.
* `PLLPH.eulerFamily` (every discretization read as the Euler discretization of its model's
  centred pH port system, with the requirements and translation of its model read through the
  design) and `PLLPH.euler` (every discretization realizing its model, `Implementation.ofDesign`).
* M–I (realization). The small-step law is the generic connection law applied to the family, with
  its port structure `PLLPH.family_isNonlinearPH.isPort` and the public smoothness lemma
  `PLLPH.contDiffAt_zeroInput`: `Numerics.eulerPorts_sound_small_step_local` (scaffold
  `sound-small-step`: a locally exponentially stable model has a step `h₀ > 0` below which its
  discretizations are locally exponentially stable). `PLLPH.not_euler_realizationSoundUnder`
  (scaffold `not-sound-large-step`): without a step constraint the realization is not sound
  (`V = K_p = K_i = 1`, `η* = θ* = 0`).
* Passivity: `PLLPH.euler_mem_den_passive_iff`: a discretization is passive exactly when `V = 0`,
  whatever its step; `PLLPH.not_euler_realizationSoundUnder_passive`: the passivity realization
  is not sound (`V = K_p = K_i = 1`, nonnegative energy, passive).
-/

noncomputable section

namespace powerlib.PLL.PLLPH

/-- The explicit Euler discretization of an SRF-PLL pH model with step `h > 0`. -/
structure Euler where
  /-- The discretized model. -/
  design : Model
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler discretization family: every discretization read as the Euler discretization of its
model's centred pH port system, with step length its step. -/
def eulerFamily : Family Euler Requirement 2 1 :=
  Numerics.eulerPortFamily family (fun m => (m.toPH.shift m.point).system) Euler.design Euler.h

/-- The Euler realization: every discretization realizes its model. -/
def euler : Implementation Model Requirement Euler Requirement 2 1 2 1 :=
  Numerics.eulerPorts family (fun m => (m.toPH.shift m.point).system) Euler.design Euler.h

/-- The centred zero-input field is `C¹` near the origin: it is the SRF-PLL field with offset
`K_i η*`, translated to the selected point. The smoothness hypothesis of the generic Euler laws
for port systems (`Numerics.eulerPorts_sound_small_step_local`). -/
@[powerlib_foundation] theorem contDiffAt_zeroInput (m : Model) :
    ContDiffAt ℝ 1 (m.toPH.shift m.point).system.zeroInput 0 := by
  change ContDiffAt ℝ 1 (fun z => m.toPH.zeroInputField (z + m.point)) 0
  rw [show m.toPH.zeroInputField = srfField m.V m.Kp m.Ki (m.Ki * m.ηs) from
    pllPH_zeroInputField m.damping]
  exact Numerics.contDiffAt_shift (contDiff_srfField _ _ _ _).contDiffAt

/-- The model `V = K_p = K_i = 1`, `η* = θ* = 0`. -/
private def unitModel : Model := ⟨1, 1, 1, 0, 0, zero_le_one⟩

/-- At the centred state `(π/2 − θ*, 0)` the phase is `π/2` and the output is `−V`. -/
private theorem output_quarter (m : Model) :
    (m.toPH.shift m.point).output (PhasePlane.mk (Real.pi / 2 - m.θ) 0) = ![-m.V] := by
  rw [PH.NonlinearModel.shift_output, Model.toPH, pllPH_output]
  simp [srfPD, Model.point]

/-- **Without a step constraint the Euler realization of the SRF-PLL pH models is not sound.** The
well bottom of `V = K_p = K_i = 1` is locally exponentially stable, and its discretizations with a
large step are not: every Euler multiplier `1 + hλ` leaves the unit disk. -/
@[tmio MI]
@[powerlib_domain] theorem not_euler_realizationSoundUnder :
    connection% (¬ euler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hm := mem_den_locallyExponentiallyStable unitModel (by norm_num [unitModel])
    (by norm_num [unitModel]) (by simp [unitModel])
  unfold powerlib.TMIO.Statement at hm
  exact Numerics.not_eulerPorts_realizationSoundUnder_of_large_step_local
    family_isNonlinearPH.isPort (by norm_num) (contDiffAt_zeroInput _) hm
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

/-- **An Euler discretization of an SRF-PLL pH model is passive exactly when the grid is dead,
whatever its step.** For `V ≠ 0` the output `−V sin θ` does not depend on the offset input, so one
step from the phase `π/2` with a large offset draws energy without bound; for `V = 0` the output
vanishes and the zero storage proves passivity. -/
@[tmio TM]
@[powerlib_domain] theorem euler_mem_den_passive_iff :
    connection% (∀ (m : Model) (h : ℝ) (hh : 0 < h),
      (⟨m, h, hh⟩ : Euler) ∈ eulerFamily.den .passive ↔ m.V = 0) := by
  unfold powerlib.TMIO.Statement
  intro m h hh
  constructor
  · intro hmem
    by_contra hV
    refine Numerics.eulerPortFamily_not_mem_den_passive (design := Euler.design)
      (step := Euler.h) (y := ⟨m, h, hh⟩) hh (fun _ => output_quarter m) ?_ hmem
    intro h0
    exact hV (by simpa using congrFun h0 0)
  · intro hV
    rw [Family.mem_den]
    change (Numerics.eulerSystem (m.toPH.shift m.point).system h).Passive
    refine ⟨fun _ => 0, fun _ => le_rfl, fun x u => ?_⟩
    change (0 : ℝ) - 0 ≤ h * (u ⬝ᵥ (m.toPH.shift m.point).output x)
    rw [PH.NonlinearModel.shift_output, Model.toPH, pllPH_output]
    simp [srfPD, hV]

/-- **The passivity realization of explicit Euler is not sound for the SRF-PLL pH models.** The
model `V = K_p = K_i = 1` has nonnegative energy and is passive, and its discretizations are
not. -/
@[tmio MI]
@[powerlib_domain] theorem not_euler_realizationSoundUnder_passive :
    connection% (¬ euler.RealizationSoundUnder ∅ .passive) := by
  unfold powerlib.TMIO.Statement
  have hm := mem_den_passive unitModel zero_le_one zero_le_one
  unfold powerlib.TMIO.Statement at hm
  refine Numerics.not_eulerPorts_realizationSoundUnder_passive (y := ⟨unitModel, 1, one_pos⟩) hm
    (by rw [TMIO.realize_empty]; trivial) one_pos (fun _ => output_quarter unitModel) ?_
  intro h0
  simpa [unitModel] using congrFun h0 0

end powerlib.PLL.PLLPH
