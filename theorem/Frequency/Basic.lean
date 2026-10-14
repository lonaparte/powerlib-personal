import theorem.Linear.Family
import theorem.Dynamics.Shift
import theorem.LTI.Plant

/-! # Frequency-response models: shared load-step input (foundation)

Shared by the `powerlib.Frequency` modules: `load ΔP_L`, the constant scalar input of a one-port
plant (a load step applied at `t = 0`), and its evaluation `load_apply`. Nothing here describes
a specific engineering model; the frequency-response models (state order, signs, parameter
ranges) and their families are fixed in the modules that use them.

The generic constant-input plant lemmas these modules use (`LTI.inputField_apply`,
`LTI.trajectory_eq_solution_Ici`, `LTI.solution_hasDerivAt`, `LTI.solution_continuous`,
`LTI.tendsto_equilibrium`, `LTI.tendsto_apply_of_isHurwitz`, `LTI.hasDerivWithinAt_apply_zero`)
are in `theorem/LTI/Plant.lean`, imported here.

Family and connection conclusions. This module defines no family and states no behaviour
(Rules §3, foundation). The model modules publish their engineering conclusions as connection
statements on their own families. -/

noncomputable section
namespace powerlib.Frequency

/-- A constant scalar load step `ΔP_L` on a one-port plant. -/
def load (ΔPL : ℝ) : Fin 1 → ℝ := fun _ => ΔPL

@[simp, powerlib_foundation] theorem load_apply (ΔPL : ℝ) (i : Fin 1) : load ΔPL i = ΔPL := rfl

end powerlib.Frequency
