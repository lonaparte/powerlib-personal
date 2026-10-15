import theorem.Family.Basic

/-! A new model domain behind a transparent Family type alias. Admission must infer
this domain from the compiled inventory without an entry in a model-name list. -/

namespace ConnectionFamilyFixture
open powerlib

structure Model where
  field : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)

abbrev FamilyAlias := Family Model Unit 1 0

noncomputable def family : FamilyAlias :=
  ⟨fun m => Port.System.autonomous m.field, fun _ _ => True, fun _ => Set.univ⟩

end ConnectionFamilyFixture
