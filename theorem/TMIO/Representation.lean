import theorem.TMIO.Derived

/-! # Representation change (v0.3 §6)

A representation change on both ends of an edge is a pair of order isomorphisms. The new semantic
map is defined as `e_A ∘ u ∘ e_B⁻¹`; the new forward map, its closure operator and the whole
generated chain then follow from uniqueness of adjoints and are not designed again. A bare type
bijection does not establish this structure: the semantic map itself must be transported.

Scope.
* Generic order theory: an edge between arbitrary complete lattices, or a whole seed, changed by
  order isomorphisms of its layers; no model.

Source: TMIO v0.3 §6; scaffold `theorem/TMIO/Representation.agda` (a representation change of
complete systems is an equivalence of carriers preserving satisfaction, hence a path of
satisfaction structures along which the generated legal space transports); Mathlib's
`ClosureOperator.conjBy`.

Results.
* `transport` (`transport_apply`, `transport_refl`), `generate_transport` (the generated forward
  map transports with the structure), `closure_transport`.
* Fixed points: `closedTransport`, `interiorTransport`, `fixedPointsIso_transport` (the
  fixed-point correspondence commutes with representation changes).
* Seeds: `Seed.transport` (all four layers), `Seed.transport_whole` (the whole generated chain
  transports with the four representation changes).
-/

namespace powerlib.TMIO

section Edge

variable {A B A' B' : Type*} [CompleteLattice A] [CompleteLattice B] [CompleteLattice A']
  [CompleteLattice B']

/-- The semantic map in the new representation, `e_A ∘ u ∘ e_B⁻¹`. -/
def transport (u : sInfHom B A) (eA : A ≃o A') (eB : B ≃o B') : sInfHom B' A' where
  toFun b := eA (u (eB.symm b))
  map_sInf' s := by
    rw [map_sInf eB.symm, map_sInf u, map_sInf eA, Set.image_image, Set.image_image]

@[tmio T, simp, powerlib_foundation] theorem transport_apply (u : sInfHom B A) (eA : A ≃o A')
    (eB : B ≃o B') (b : B') : transport u eA eB b = eA (u (eB.symm b)) := rfl

/-- The generated forward map transports with the structure. -/
@[tmio T, powerlib_foundation] theorem generate_transport (u : sInfHom B A) (eA : A ≃o A')
    (eB : B ≃o B') : ⇑(generate (transport u eA eB)) = eB ∘ generate u ∘ eA.symm := by
  symm
  apply generate_unique
  intro a b
  change eB (generate u (eA.symm a)) ≤ b ↔ a ≤ eA (u (eB.symm b))
  rw [← OrderIso.le_symm_apply, gc_generate u, OrderIso.symm_apply_le]

/-- The generated closure operator transports by Mathlib's conjugation of closure operators. -/
@[tmio T, powerlib_foundation] theorem closure_transport (u : sInfHom B A) (eA : A ≃o A')
    (eB : B ≃o B') : closure (transport u eA eB) = (closure u).conjBy eA := by
  ext a
  rw [closure_apply, congrFun (generate_transport u eA eB) a]
  simp only [Function.comp_apply, transport_apply, OrderIso.symm_apply_apply]
  rfl

/-- Transporting along identities changes nothing. -/
@[tmio T, powerlib_foundation] theorem transport_refl (u : sInfHom B A) :
    transport u (OrderIso.refl A) (OrderIso.refl B) = u := by
  ext b
  rfl

/-- Closed source elements are transported by the source order isomorphism. -/
def closedTransport (u : sInfHom B A) (eA : A ≃o A') (eB : B ≃o B') :
    {a : A // u (generate u a) = a} ≃o
      {a : A' // transport u eA eB (generate (transport u eA eB) a) = a} where
  toFun a := ⟨eA a, by
    rw [congrFun (generate_transport u eA eB) (eA a)]
    simp only [Function.comp_apply, transport_apply, OrderIso.symm_apply_apply, a.property]⟩
  invFun a := ⟨eA.symm a, by
    have h := congrArg eA.symm a.property
    rw [congrFun (generate_transport u eA eB) a] at h
    simpa only [Function.comp_apply, transport_apply, OrderIso.symm_apply_apply] using h⟩
  left_inv a := by ext; simp
  right_inv a := by ext; simp
  map_rel_iff' := eA.le_iff_le

/-- Interior-stable target elements are transported by the target order isomorphism. -/
def interiorTransport (u : sInfHom B A) (eA : A ≃o A') (eB : B ≃o B') :
    {b : B // generate u (u b) = b} ≃o
      {b : B' // generate (transport u eA eB) (transport u eA eB b) = b} where
  toFun b := ⟨eB b, by
    rw [congrFun (generate_transport u eA eB) (transport u eA eB (eB b))]
    simp only [Function.comp_apply, transport_apply, OrderIso.symm_apply_apply, b.property]⟩
  invFun b := ⟨eB.symm b, by
    have h := congrArg eB.symm b.property
    rw [congrFun (generate_transport u eA eB) (transport u eA eB b)] at h
    simpa only [Function.comp_apply, transport_apply, OrderIso.symm_apply_apply] using h⟩
  left_inv b := by ext; simp
  right_inv b := by ext; simp
  map_rel_iff' := eB.le_iff_le

/-- Representation change preserves the generated fixed-point correspondence itself. -/
@[tmio T, powerlib_foundation] theorem fixedPointsIso_transport (u : sInfHom B A)
    (eA : A ≃o A') (eB : B ≃o B') (a : {a : A // u (generate u a) = a}) :
    fixedPointsIso (transport u eA eB) (closedTransport u eA eB a) =
      interiorTransport u eA eB (fixedPointsIso u a) := by
  apply Subtype.ext
  change generate (transport u eA eB) (eA a.val) = eB (generate u a.val)
  rw [congrFun (generate_transport u eA eB) (eA a.val)]
  simp

end Edge

namespace Seed

variable {T M I O T' M' I' O' : Type*} [CompleteLattice T] [CompleteLattice M]
  [CompleteLattice I] [CompleteLattice O] [CompleteLattice T'] [CompleteLattice M']
  [CompleteLattice I'] [CompleteLattice O']

/-- The seed in a new representation of all four layers. -/
def transport (S : Seed T M I O) (eT : T ≃o T') (eM : M ≃o M') (eI : I ≃o I')
    (eO : O ≃o O') : Seed T' M' I' O' where
  u₁ := TMIO.transport S.u₁ eT eM
  u₂ := TMIO.transport S.u₂ eM eI
  u₃ := TMIO.transport S.u₃ eI eO

/-- The whole generated chain transports with the four representation changes. -/
@[tmio T, powerlib_foundation] theorem transport_whole (S : Seed T M I O) (eT : T ≃o T') (eM : M ≃o M')
    (eI : I ≃o I') (eO : O ≃o O') :
    ⇑(generate (S.transport eT eM eI eO).uTO) = eO ∘ generate S.uTO ∘ eT.symm := by
  rw [generate_uTO, generate_uTO]
  funext t
  simp only [Function.comp_apply, l₁, l₂, l₃, transport]
  rw [congrFun (generate_transport S.u₁ eT eM), congrFun (generate_transport S.u₂ eM eI),
    congrFun (generate_transport S.u₃ eI eO)]
  simp

end Seed

end powerlib.TMIO
