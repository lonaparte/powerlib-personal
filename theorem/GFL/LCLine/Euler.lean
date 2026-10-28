import theorem.GFL.LCLine.Reduced2D
import theorem.Numerics.EulerRealization

/-! # The explicit Euler integration of the code-frame reduced LCL-line PLL: a realization

The code-frame family of the reduced LCL-line PLL (`LCLine.codeFamily`,
`theorem/GFL/LCLine/Reduced2D.lean`) integrated by the explicit Euler method with a fixed step
`h > 0` is an implementation layer over it: each integration realizes the model it integrates. A
locally exponentially stable model has a step `h₀ > 0` below which its Euler integration is
locally exponentially stable, and without a step constraint the realization is not sound; an
instance of the generic template
`theorem/Numerics/EulerRealization.lean`, in the pattern of `theorem/Synchronous/SwingEuler.lean`.
Scaffold: `theorem/EulerDiscretization.agda`.

Model boundary.
* Model layer (M): `LCLine.codeFamily`, the reduced two-state PLL of the LCL-filtered line in the
  project-code frame, state `(θ_c, η)`, read about its selected point `(θ_c*, 0)`, with the model
  boundary of `theorem/GFL/LCLine/Reduced2D.lean`. Its field is `C¹` for every parameter set (the
  reflection of the reduced field, whose phase-detector characteristic is a trigonometric
  polynomial, `Params.contDiff_h_one`).
* Implementation layer (I). `LCLine.CodeEuler`: a model and a step `h > 0`; the system is the
  explicit Euler map `z ↦ z + h f(z)` of the translated code-frame field, with step length `h`,
  discrete time, exact arithmetic (no round-off), fixed step. Excluded: step-size control, implicit
  or higher-order schemes, the integration error against the continuous trajectory.
* Level: local exponential stability of the selected point.

Source: `theorem/Numerics/EulerRealization.lean` (`euler_sound_small_step`,
`euler_certified_small_step`, `not_euler_realizationSoundUnder_of_large_step`),
`theorem/GFL/LCLine/Reduced2D.lean` (`codeFamily_isAutonomous`, `Params.codeField_eq_transport`,
`Params.reducedField_eq`, `Params.contDiff_h_one`, `code_mem_den_iff`),
`theorem/GFL/LCLine/Reduction.lean` (`Params.h_eq`, `Params.deriv_h_eq`),
`theorem/PLL/PIPLLFamily.lean` (`mem_den_locallyExponentiallyStable_of_pos`); work-sync
`theory/T-numerical-integration.md` §1.2, §2.7.

Results.
* `LCLine.code_contDiff_field`: the translated code-frame field is `C¹`, the smoothness hypothesis
  of the generic laws; the witness parameters `unitLine` are private.

Family and connection conclusions.
* `LCLine.codeEulerFamily : Family LCLine.CodeEuler PLL.PIPLL.Requirement 2 0`: every integration
  read as its Euler map; requirements and translation are those of its model, read through the
  design. `LCLine.codeEuler`: the implementation layer, every integration realizing its model
  (`Implementation.ofDesign CodeEuler.design`).
* M–I (realization). The small-step laws are the generic connection laws applied to the family,
  with its autonomy `LCLine.codeFamily_isAutonomous` and the public smoothness lemma
  `LCLine.code_contDiff_field`: `Numerics.euler_sound_small_step` (scaffold `sound-small-step`: a
  locally exponentially stable model has a step `h₀ > 0` such that every Euler integration with a
  step `h ≤ h₀` is locally exponentially stable) and `Numerics.euler_certified_small_step`
  (scaffold `certified-small-step`). `code_not_euler_realizationSoundUnder` (scaffold
  `not-sound-large-step`): without a step constraint the realization is not sound — the model with
  unit filter capacitance, grid frequency and EMF, a line without impedance, zero current
  references and unit PLL gains at `θ_c* = 0` (`h = −sin`, locally exponentially stable through
  the text frame) has Euler integrations with every multiplier outside the unit disk. The
  statements carry the prefix `code_` of the family's other conclusions.
-/

noncomputable section

namespace powerlib.GFL.LCLine

/-- The explicit Euler integration of a code-frame PLL model about its selected point with step
`h > 0`. -/
structure CodeEuler where
  /-- The integrated code-frame PLL model. -/
  design : CodeModel
  /-- The step. -/
  h : ℝ
  /-- Steps are positive. -/
  pos : 0 < h

/-- The Euler integration family: every integration read as the Euler map of its model's translated
code-frame field, with step length its step. -/
def codeEulerFamily : Family CodeEuler PLL.PIPLL.Requirement 2 0 :=
  Numerics.eulerFamily codeFamily CodeModel.field CodeEuler.design CodeEuler.h

/-- The Euler realization: every integration realizes its code-frame PLL model. -/
def codeEuler : Implementation CodeModel PLL.PIPLL.Requirement CodeEuler PLL.PIPLL.Requirement 2 0
    2 0 :=
  Numerics.euler codeFamily CodeModel.field CodeEuler.design CodeEuler.h

/-- The translated code-frame field is `C¹`: the reflection of the reduced field, whose
phase-detector characteristic `h` is `C¹` for every parameter set. The smoothness hypothesis of the
generic Euler laws (`Numerics.euler_sound_small_step`). -/
@[powerlib_foundation] theorem code_contDiff_field (m : CodeModel) :
    ContDiff ℝ 1 (CodeModel.field m) := by
  have h : ContDiff ℝ 1 m.params.codeField := by
    rw [Params.codeField_eq_transport, Params.reducedField_eq]
    exact Dynamics.contDiff_transportField _ _ (PLL.contDiff_piPLLField m.params.contDiff_h_one)
  exact h.comp (contDiff_id.add contDiff_const)

/-- The parameters of the witness below: unit filter capacitance, grid frequency and grid EMF, a
line without impedance, zero current references and unit PLL gains (`a = b = 0`, `Δ = 1`, so the
phase-detector characteristic is `h = −sin`). -/
private def unitLine : Params := ⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1⟩

/-- **Without a step constraint the Euler realization of the code-frame PLL models is not sound.**
The locally exponentially stable code-frame model `unitLine` at `θ_c* = 0` (a zero of `h = −sin`
with negative slope, read through the text frame, `code_mem_den_iff`) integrated with a large
enough step is not locally exponentially stable: every Euler multiplier `1 + hλ` leaves the unit
disk (`Numerics.not_euler_realizationSoundUnder_of_large_step`). -/
@[tmio MI, powerlib_domain] theorem code_not_euler_realizationSoundUnder :
    connection% (¬ codeEuler.RealizationSoundUnder ∅ (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hwC : unitLine.wC ≠ 0 := by norm_num [unitLine, Params.wC]
  have hΔ : unitLine.Δ ≠ 0 := by norm_num [unitLine, Params.Δ, Params.a, Params.b]
  have h0 : unitLine.h (-0) = 0 := by
    rw [unitLine.h_eq hwC hΔ]
    norm_num [unitLine, Params.c0, Params.a, Params.b, Params.Δ, Params.wC]
  have hg : deriv unitLine.h (-0) < 0 := by
    rw [unitLine.deriv_h_eq hwC hΔ]
    norm_num [unitLine, Params.a, Params.b, Params.Δ]
  have hr := PLL.PIPLL.mem_den_locallyExponentiallyStable_of_pos (unitLine.pllModel (-0))
    one_pos one_pos h0 hg
  have hc := code_mem_den_iff ⟨unitLine, 0⟩ (.flow .locallyExponentiallyStable)
  unfold powerlib.TMIO.Statement at hr hc
  exact Numerics.not_euler_realizationSoundUnder_of_large_step codeFamily_isAutonomous
    code_contDiff_field (by norm_num) (hc.mpr hr)
    fun h₁ => ⟨⟨_, max h₁ 1, by positivity⟩, rfl, le_max_left _ _⟩

end powerlib.GFL.LCLine
