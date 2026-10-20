import theorem.GFL.DCLink.Cascade
import theorem.Numerics.EulerPorts

/-! # The explicit Euler discretization of the linearized current-loop/DC-link cascade

The linearized cascade `linearizedFamily` of `theorem/GFL/DCLink/Cascade.lean` (input `Δi_d*`,
output `ΔV_dc`) discretized by the explicit Euler method with a fixed step `h > 0`, with its
port: each discretization realizes the parameter set it is designed from. The family is linear
(`linearizedFamily_isLinear`), so the linear laws of the generic template
`theorem/Numerics/EulerPorts.lean` apply: the Euler zero-input map is `I + hA`, the attractive
sentences and sampled contraction are realized completely at every step and exactly below a step
threshold, and not soundly without a step constraint. No discretization is passive: the output
`ΔV_dc` does not depend on the input (`D = 0`). Scaffold: `theorem/EulerPorts.agda`.

Model boundary.
* Model layer (M): `linearizedFamily : Family CascadeParams Spectral.Requirement 3 1`, the
  small-signal plant `CascadeParams.model` of the d-axis PI current loop feeding the DC-link
  capacitor (state `(Δi_d, Δξ, ΔV_dc)`, input `Δi_d*`, output `ΔV_dc`), continuous time, read
  about the origin, with its requirements (`stable`: positive PI monic coefficients and a positive
  DC-node coefficient `I_dc0/(C V0)`; `unstable`) and translation (`Spectral.linearFamily`).
* Implementation layer (I): `CascadeParams.LinearizedEuler`, a parameter set and a step `h > 0`;
  the system is the explicit Euler discretization `x⁺ = x + h (A x + B u)`, output `C x` (the
  input held over the step), step length `h`, discrete time, exact arithmetic, fixed step.
  Excluded: the nonlinear cascade (its autonomous Euler integration is
  `theorem/GFL/DCLink/Euler.lean`), step-size control, implicit or higher-order schemes.
* Level: the attractive sentences and sampled contraction of the zero-input dynamics about the
  origin; passivity of the discretized port system.

Source: `theorem/Numerics/EulerPorts.lean` (`eulerPorts_exact_small_step_linear`,
`eulerPorts_realizationCompleteUnder_linear`,
`not_eulerPorts_realizationSoundUnder_of_large_step_linear`,
`eulerPortFamily_not_mem_den_passive`) and `theorem/GFL/DCLink/Cascade.lean` (linearity, the
Hurwitz criterion `CascadeParams.isHurwitz_iff`); work-sync `theory/T-numerical-integration.md`
§1.2, §2.7, `theory/T-vsc-dc-voltage-control.md` §1.4.

Results.
* No static result beyond the family definitions.

Family and connection conclusions.
* `linearizedEulerFamily` (every discretization read as the Euler discretization of its
  parameters' small-signal port system, with the requirements and translation of its parameters
  read through the design) and `linearizedEuler` (every discretization realizing its parameter
  set, `Implementation.ofDesign`).
* M–I (realization), for every attractive sentence or sampled contraction `P`:
  `linearizedEuler_exact_small_step` (scaffold `sound-small-step`, with completeness): every
  parameter set has a step `h₀ > 0` below which its discretizations satisfy `P` exactly when its
  linearization does; `linearizedEuler_realizationCompleteUnder`: at every step, within every
  requirement context, a discretization satisfying `P` realizes only parameter sets satisfying
  it; `not_linearizedEuler_realizationSoundUnder` (scaffold `not-sound-large-step`): without a
  step constraint the realization is not sound (the rectifier `L = Kp = Ki = C = V_d0 = V0 =
  I_d0 = 1`, `R = 0`, so `I_dc0 = 1`).
* Passivity: `linearizedEuler_not_mem_den_passive`: no discretization is passive, whatever its
  step. The realization of passivity is not refuted here: the cascade module proves no passive
  linearization, and without a passive model the realization of passivity is vacuously sound.
-/

noncomputable section

open LinearSystems

namespace powerlib.GFL.DCLink

namespace CascadeParams

/-- The explicit Euler discretization of the linearized cascade of a parameter set with step
`h > 0`. -/
structure LinearizedEuler where
  /-- The discretized parameter set. -/
  design : CascadeParams
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

end CascadeParams

open CascadeParams (LinearizedEuler)

/-- The Euler discretization family of the linearized cascade: every discretization read as the
Euler discretization of its small-signal port system, with step length its step. -/
def linearizedEulerFamily : Family LinearizedEuler Spectral.Requirement 3 1 :=
  Numerics.eulerPortFamily linearizedFamily (fun p => p.model.system) LinearizedEuler.design
    LinearizedEuler.h

/-- The Euler realization of the linearized cascade: every discretization realizes its parameter
set. -/
def linearizedEuler :
    Implementation CascadeParams Spectral.Requirement LinearizedEuler Spectral.Requirement
      3 1 3 1 :=
  Numerics.eulerPorts linearizedFamily (fun p => p.model.system) LinearizedEuler.design
    LinearizedEuler.h

/-- **Small steps realize the attractive sentences of the linearized cascade exactly.** Every
parameter set has a step `h₀ > 0` such that its Euler discretizations with a step `h ≤ h₀`
satisfy an attractive sentence (or sampled contraction) exactly when its linearization does. -/
@[powerlib_domain] theorem linearizedEuler_exact_small_step {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (∀ p : CascadeParams, ∃ h₀ : {h : ℝ // 0 < h}, ∀ (h : ℝ) (hh : 0 < h),
      h ≤ h₀.1 → ((⟨p, h, hh⟩ : LinearizedEuler) ∈ linearizedEulerFamily.den (.flow P) ↔
        p ∈ linearizedFamily.den (.flow P))) := by
  unfold powerlib.TMIO.Statement
  intro p
  obtain ⟨h₀, hh₀, hE⟩ := Numerics.eulerPorts_exact_small_step_linear
    (design := LinearizedEuler.design) (step := LinearizedEuler.h) linearizedFamily_isLinear hP p
  exact ⟨⟨h₀, hh₀⟩, fun h hh hle => hE ⟨p, h, hh⟩ rfl ⟨hh, hle⟩⟩

/-- **The Euler realization of the linearized cascade is complete at every step.** A
discretization satisfying an attractive sentence (or sampled contraction) realizes only parameter
sets whose linearization satisfies it, within every requirement context. -/
@[powerlib_domain] theorem linearizedEuler_realizationCompleteUnder {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) (Δ : Set Spectral.Requirement) :
    connection% (linearizedEuler.RealizationCompleteUnder Δ (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact Numerics.eulerPorts_realizationCompleteUnder_linear linearizedFamily_isLinear
    LinearizedEuler.pos hP Δ

/-- **Without a step constraint the Euler realization of the linearized cascade is not sound.**
The rectifier `L = Kp = Ki = C = V_d0 = V0 = I_d0 = 1`, `R = 0` (`I_dc0 = 1`) has a Hurwitz
linearization, and its discretizations with a large step are unstable. -/
@[powerlib_domain] theorem not_linearizedEuler_realizationSoundUnder {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (¬ linearizedEuler.RealizationSoundUnder ∅ (.flow P)) := by
  unfold powerlib.TMIO.Statement
  set p : CascadeParams := ⟨⟨1, 0, 1, 1⟩, 1, 1, 1, 1⟩
  have hA : IsHurwitz p.model.A :=
    (p.isHurwitz_iff one_pos one_pos one_pos).mpr
      ⟨⟨by norm_num [p], by norm_num [p]⟩, by norm_num [p, CascadeParams.Idc0]⟩
  exact Numerics.not_eulerPorts_realizationSoundUnder_of_large_step_linear
    linearizedFamily_isLinear (by norm_num) hP (x := p) hA
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

/-- **No Euler discretization of the linearized cascade is passive, whatever its step.** The
output `ΔV_dc` does not depend on the input, so one step from a unit DC-voltage deviation with a
large reverse input draws energy without bound. -/
@[powerlib_domain] theorem linearizedEuler_not_mem_den_passive :
    connection% (∀ (p : CascadeParams) (h : ℝ) (hh : 0 < h),
      (⟨p, h, hh⟩ : LinearizedEuler) ∉ linearizedEulerFamily.den .passive) := by
  unfold powerlib.TMIO.Statement
  intro p h hh
  refine Numerics.eulerPortFamily_not_mem_den_passive (design := LinearizedEuler.design)
    (step := LinearizedEuler.h) (y := ⟨p, h, hh⟩) hh (x₀ := WithLp.toLp 2 ![0, 0, 1])
    (v := ![1]) (fun u => ?_) (by simp)
  funext i
  fin_cases i
  simp [CascadeParams.model, Linear.Plant.system, dotProduct, Fin.sum_univ_three]

end powerlib.GFL.DCLink
