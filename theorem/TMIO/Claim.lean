import theorem.TMIO.Generate

/-! Kernel-checked syntax for connection conclusions. Neither grammar has an arbitrary
proposition constructor. Metadata cannot construct an endpoint or admit a conclusion. -/

namespace powerlib.TMIO

universe u v w

/-- A value obtained from an actual upper adjoint, its uniquely generated lower adjoint,
or a structural operation on such values. -/
inductive Endpoint : {α : Type u} → α → Prop where
  | upper {A : Type u} {B : Type v} [CompleteLattice A] [CompleteLattice B]
      (back : sInfHom B A) (b : B) : Endpoint (back b)
  | lower {A : Type v} {B : Type u} [CompleteLattice A] [CompleteLattice B]
      (back : sInfHom B A) (a : A) : Endpoint (generate back a)
  | closed {A : Type u} {B : Type v} [CompleteLattice A] [CompleteLattice B]
      (back : sInfHom B A) (a : A) : Endpoint (closure back a)
  | dual {A : Type u} {a : Aᵒᵈ} : Endpoint a → Endpoint (OrderDual.ofDual a)
  | toDual {A : Type u} {a : A} : Endpoint a → Endpoint (OrderDual.toDual a)
  | preimage {X Y : Type u} (f : X → Y) {s : Set Y} : Endpoint s → Endpoint (f ⁻¹' s)
  | compl {X : Type u} {s : Set X} : Endpoint s → Endpoint sᶜ
  | inter {X : Type u} {s t : Set X} : Endpoint s → Endpoint t → Endpoint (s ∩ t)

/-- The closed grammar of admitted connection conclusions, indexed by their meaning.
The kernel checks that each atom really is an endpoint evaluation or a comparison of
infimum-preserving maps. Logical combinations cannot add an unrelated proposition. -/
inductive ConnectionClaim : Prop → Prop where
  | eqLeft {A : Type u} {a b : A} : Endpoint.{u,v} a → ConnectionClaim (a = b)
  | eqRight {A : Type u} {a b : A} : Endpoint.{u,v} b → ConnectionClaim (a = b)
  | leLeft {A : Type u} [CompleteLattice A] {a b : A} : Endpoint.{u,v} a → ConnectionClaim (a ≤ b)
  | leRight {A : Type u} [CompleteLattice A] {a b : A} : Endpoint.{u,v} b → ConnectionClaim (a ≤ b)
  | member {X : Type u} {x : X} {s : Set X} : Endpoint.{u,v} s → ConnectionClaim (x ∈ s)
  | memberIff {X : Type u} (x : X) {s : Set X} (t : Set X) :
      Endpoint.{u,v} s → ConnectionClaim (x ∈ s ↔ x ∈ t)
  | mapsEq {A : Type u} {B : Type v} [CompleteLattice A] [CompleteLattice B]
      (back₁ back₂ : sInfHom B A) : ConnectionClaim (back₁ = back₂)
  | not {P : Prop} : ConnectionClaim P → ConnectionClaim (¬ P)
  | and {P Q : Prop} : ConnectionClaim P → ConnectionClaim Q → ConnectionClaim (P ∧ Q)
  | or {P Q : Prop} : ConnectionClaim P → ConnectionClaim Q → ConnectionClaim (P ∨ Q)
  | iff {P Q : Prop} : ConnectionClaim P → ConnectionClaim Q → ConnectionClaim (P ↔ Q)
  | assuming {P : Prop} {Q : P → Prop} : (∀ h, ConnectionClaim (Q h)) → ConnectionClaim (∀ h, Q h)
  | all {ι : Sort w} {P : ι → Prop} : (∀ i, ConnectionClaim (P i)) → ConnectionClaim (∀ i, P i)
  | exists {ι : Sort w} {P : ι → Prop} : (∀ i, ConnectionClaim (P i)) → ConnectionClaim (∃ i, P i)

/-- A public statement carries its kernel-checked connection syntax. Its meaning is
definitionally the original proposition, so existing mathematical proofs and reuse still work. -/
@[reducible] def Statement {P : Prop} (_shape : ConnectionClaim.{u,v,w} P) : Prop := P

end powerlib.TMIO
