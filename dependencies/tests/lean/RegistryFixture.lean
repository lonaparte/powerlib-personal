import powerlib

namespace RegistryFixture

universe u

structure Envelope (P : Prop) : Prop where
  proof : P

@[powerlib_foundation] theorem envelope {α : Sort u} (P : α → Prop) (x : α)
    (h : P x) : Envelope (P x) := ⟨h⟩

@[powerlib_foundation] theorem envelope_iff (P : Prop) : Envelope P ↔ P :=
  ⟨fun h => h.proof, fun h => ⟨h⟩⟩

end RegistryFixture
