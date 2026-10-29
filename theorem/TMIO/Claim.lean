import theorem.TMIO.ConnectionBase
import Mathlib.Algebra.Order.Ring.Defs

/-! # Connection claims (foundation)

Kernel-checked syntax for connection conclusions. No grammar has an arbitrary
proposition constructor. Metadata cannot construct an endpoint or admit a conclusion.

Scope.
* Generic: values in arbitrary complete lattices obtained from arbitrary-infimum preserving maps,
  and propositions built from them; comparisons of numbers as side conditions; no model and no
  semantics. A claim has two inferred endpoint universes and two further inferred universes for
  binders and four-carrier seeds. Atoms
  may use the endpoint universes in either order, so an adjunction and its generated map can
  occur in the same claim without restricting their carrier types to `Type`. Connection
  statements are written with `connection%` (`theorem/TMIO/ClaimElab.lean`), which builds the
  certificate.

Source: the generated primitives (`theorem/TMIO/ConnectionBase.lean`: `generate`, `closure`)
and their public laws (`theorem/TMIO/Generate.lean`); the
admission rules of `Rules.md` §3a (a published connection result carries a `ConnectionClaim`
certificate in its proposition type).

Results.
* `Endpoint`: a value obtained from an actual upper adjoint (`upper`), its uniquely generated
  lower adjoint (`lower`), its closure (`closed`), or a structural operation on such values
  (`dual`, `toDual`, `preimage`, `compl`, `inter`).
* `Condition`: the closed grammar of side conditions — comparisons (`≤`, `<`, `=`) of numbers,
  values of a linearly and strictly ordered semiring (`ℕ`, `ℤ`, `ℚ`, `ℝ`), and their combinations
  by `¬`, `∧`, `∨`.
* `ConnectionClaim`: the closed grammar of admitted connection conclusions, indexed by their
  meaning — equalities, orders and memberships with an endpoint side, equality of two
  infimum-preserving maps or complete connection seeds, equality of endpoint spaces restricted
  by a common context and its two-inclusion characterization, and logical combinations
  (`not`, `and`, `or`, `iff`, `assuming`,
  `all`, `exists`), which cannot add an unrelated proposition; binders over the types of the
  endpoints' universe (`allType`: a claim about arbitrary families); and side conditions
  in two places only: the characterizing side of an iff (`iffCondition`) and the guard of an
  existential witness (`existsGuard`). Premises are already unrestricted (`assuming`).
* `Statement`: a public statement carries its kernel-checked connection syntax; its meaning is
  definitionally the original proposition, so existing mathematical proofs and reuse still work.
-/

namespace powerlib.TMIO

universe u v w z

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

/-- Side conditions of a claim: comparisons of numbers — values of a linearly and strictly
ordered semiring (`ℕ`, `ℤ`, `ℚ`, `ℝ`) — and their combinations by `¬`, `∧`, `∨`. No other
proposition is a side condition. -/
inductive Condition : Prop → Prop where
  | le {α : Type} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] (a b : α) :
      Condition (a ≤ b)
  | lt {α : Type} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] (a b : α) :
      Condition (a < b)
  | eq {α : Type} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] (a b : α) :
      Condition (a = b)
  | not {P : Prop} : Condition P → Condition (¬ P)
  | and {P Q : Prop} : Condition P → Condition Q → Condition (P ∧ Q)
  | or {P Q : Prop} : Condition P → Condition Q → Condition (P ∨ Q)

/-- The closed grammar of admitted connection conclusions, indexed by their meaning.
The kernel checks that each atom really is an endpoint evaluation or a comparison of
infimum-preserving maps or seeds, including equality under a shared set constraint. Logical
combinations cannot add an unrelated proposition; a side
condition (`Condition`) enters only as the characterizing side of an iff or as the guard of an
existential witness. -/
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
  /-- The same atomic shapes with the two endpoint universes reversed. Generated forward maps
  reverse the carriers of an upper adjoint; both orientations belong to one connection law. -/
  | eqLeftSwap {A : Type v} {a b : A} : Endpoint.{v,u} a → ConnectionClaim (a = b)
  | eqRightSwap {A : Type v} {a b : A} : Endpoint.{v,u} b → ConnectionClaim (a = b)
  | leLeftSwap {A : Type v} [CompleteLattice A] {a b : A} :
      Endpoint.{v,u} a → ConnectionClaim (a ≤ b)
  | leRightSwap {A : Type v} [CompleteLattice A] {a b : A} :
      Endpoint.{v,u} b → ConnectionClaim (a ≤ b)
  | memberSwap {X : Type v} {x : X} {s : Set X} :
      Endpoint.{v,u} s → ConnectionClaim (x ∈ s)
  | memberIffSwap {X : Type v} (x : X) {s : Set X} (t : Set X) :
      Endpoint.{v,u} s → ConnectionClaim (x ∈ s ↔ x ∈ t)
  | mapsEqSwap {A : Type v} {B : Type u} [CompleteLattice A] [CompleteLattice B]
      (back₁ back₂ : sInfHom B A) : ConnectionClaim (back₁ = back₂)
  /-- Equality of complete connection seeds compares their three supplied upper maps. -/
  | seedsEq {T : Type u} {M : Type v} {I : Type w} {O : Type z}
      [CompleteLattice T] [CompleteLattice M] [CompleteLattice I] [CompleteLattice O]
      (S R : Seed T M I O) : ConnectionClaim (S = R)
  /-- A common constraint restricts the comparison domain; it is not a new conclusion. -/
  | interEqLeft {X : Type u} {s t d : Set X} : Endpoint.{u,v} s →
      ConnectionClaim (s ∩ d = t ∩ d)
  | interEqRight {X : Type u} {s t d : Set X} : Endpoint.{u,v} t →
      ConnectionClaim (s ∩ d = t ∩ d)
  | interEqLeftSwap {X : Type v} {s t d : Set X} : Endpoint.{v,u} s →
      ConnectionClaim (s ∩ d = t ∩ d)
  | interEqRightSwap {X : Type v} {s t d : Set X} : Endpoint.{v,u} t →
      ConnectionClaim (s ∩ d = t ∩ d)
  /-- The two inclusions characterize exactly the same constrained endpoint comparison. -/
  | interEqIffSubsetsLeft {X : Type u} {s t d : Set X} : Endpoint.{u,v} s →
      ConnectionClaim (s ∩ d = t ∩ d ↔ s ∩ d ⊆ t ∧ t ∩ d ⊆ s)
  | interEqIffSubsetsRight {X : Type u} {s t d : Set X} : Endpoint.{u,v} t →
      ConnectionClaim (s ∩ d = t ∩ d ↔ s ∩ d ⊆ t ∧ t ∩ d ⊆ s)
  | interEqIffSubsetsLeftSwap {X : Type v} {s t d : Set X} : Endpoint.{v,u} s →
      ConnectionClaim (s ∩ d = t ∩ d ↔ s ∩ d ⊆ t ∧ t ∩ d ⊆ s)
  | interEqIffSubsetsRightSwap {X : Type v} {s t d : Set X} : Endpoint.{v,u} t →
      ConnectionClaim (s ∩ d = t ∩ d ↔ s ∩ d ⊆ t ∧ t ∩ d ⊆ s)
  /-- Extensional equality is admitted only when every evaluation is a connection claim. -/
  | functionEq {ι : Sort w} {A : ι → Type u} {f g : (i : ι) → A i} :
      (∀ i, ConnectionClaim (f i = g i)) → ConnectionClaim (f = g)
  | lowerAdjointEq {A : Type u} {B : Type v} [CompleteLattice A] [CompleteLattice B]
      {back : B → A} {f g : LowerAdjoint back} :
      (∀ a, ConnectionClaim (f a = g a)) → ConnectionClaim (f = g)
  | lowerAdjointEqSwap {A : Type v} {B : Type u} [CompleteLattice A] [CompleteLattice B]
      {back : B → A} {f g : LowerAdjoint back} :
      (∀ a, ConnectionClaim (f a = g a)) → ConnectionClaim (f = g)
  | closureEq {A : Type u} [CompleteLattice A] {f g : ClosureOperator A} :
      (∀ a, ConnectionClaim (f a = g a)) → ConnectionClaim (f = g)
  | not {P : Prop} : ConnectionClaim P → ConnectionClaim (¬ P)
  | and {P Q : Prop} : ConnectionClaim P → ConnectionClaim Q → ConnectionClaim (P ∧ Q)
  | or {P Q : Prop} : ConnectionClaim P → ConnectionClaim Q → ConnectionClaim (P ∨ Q)
  | iff {P Q : Prop} : ConnectionClaim P → ConnectionClaim Q → ConnectionClaim (P ↔ Q)
  | assuming {P : Prop} {Q : P → Prop} : (∀ h, ConnectionClaim (Q h)) → ConnectionClaim (∀ h, Q h)
  | all {ι : Sort w} {P : ι → Prop} : (∀ i, ConnectionClaim (P i)) → ConnectionClaim (∀ i, P i)
  | allLeft {ι : Type u} {P : ι → Prop} : (∀ i, ConnectionClaim (P i)) → ConnectionClaim (∀ i, P i)
  | allRight {ι : Type v} {P : ι → Prop} : (∀ i, ConnectionClaim (P i)) → ConnectionClaim (∀ i, P i)
  | exists {ι : Sort w} {P : ι → Prop} : (∀ i, ConnectionClaim (P i)) → ConnectionClaim (∃ i, P i)
  /-- A binder over the types of the endpoints' universe (`Type u`): a claim about arbitrary
  families. -/
  | allType {P : Type u → Prop} : (∀ X, ConnectionClaim (P X)) → ConnectionClaim (∀ X, P X)
  /-- A claim characterized by a side condition. -/
  | iffCondition {P A : Prop} : ConnectionClaim P → Condition A → ConnectionClaim (P ↔ A)
  /-- An existential whose witness is guarded by a side condition. -/
  | existsGuard {ι : Sort w} {A P : ι → Prop} :
      (∀ i, Condition (A i)) → (∀ i, ConnectionClaim (P i)) → ConnectionClaim (∃ i, A i ∧ P i)

/-- A public statement carries its kernel-checked connection syntax. Its meaning is
definitionally the original proposition, so existing mathematical proofs and reuse still work. -/
@[reducible] def Statement {P : Prop} (_shape : ConnectionClaim.{u,v,w,z} P) : Prop := P

end powerlib.TMIO
