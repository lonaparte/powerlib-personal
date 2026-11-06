import theorem.Circuits.RL

/-! A concrete model dependency hidden by a value's generic result type. The importing
admission test must follow this definition; its type alone contains no RL model. -/

namespace GenericModelValueFixture
open powerlib

noncomputable def system (resistance : ℝ) : Port.System 1 1 :=
  (⟨resistance, ⟨1, zero_lt_one⟩⟩ : Circuits.RL.Impedance).plant.system

noncomputable def systemAlias (resistance : ℝ) : Port.System 1 1 := system resistance

end GenericModelValueFixture
