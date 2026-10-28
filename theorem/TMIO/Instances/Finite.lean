import theorem.TMIO.Relation

/-! # Finite existence witnesses (v0.3 §8)

Two finite instances of the same generator.

Scope.
* `witness`: the strict four-layer chain of v0.3 §8. Theory, model, implementation and
  observation points are `Bool`, `Bool²`, `Bool³` and `Bool`; the first two edges keep every
  extension (`kern` of a coordinate projection, generating its preimage) and the last edge
  observes the second coordinate (`preimage`, generating the direct image).
* The satisfaction witness of v0.3 §4 on two-bit implementations: a coupled space is generated
  exactly by two different requirement sets, and a narrower family is legal but not the space.
* Finite Boolean instances only; no model of the library.

Source: TMIO v0.3 §4 and §8; the constructors of `theorem/TMIO/Relation.lean`.

Results.
* The strict chain: `dropModel`, `dropImplementation`, `observe`, `witness`; its generated maps
  `witness_l₁`, `witness_l₂`, `witness_l₃`; `witness_closure₁` (the extension edge loses
  nothing), `witness_whole_true`, `witness_whole_empty`, `witness_roundtrip_strict` (the
  observation edge compresses information, so the generated adjoints are not inverse functions).
* The satisfaction witness: `member`, `coupled`, `requirementsOne`, `requirementsTwo`,
  `requirementsOne_space`, `requirementsTwo_space`, `narrow_legal_not_space`.
* A concrete counterexample shows that, once implementations are ordered by reverse inclusion
  (the requirement family), the possible-observation image cannot be a generated lower adjoint
  for either order on observations (`image_not_lowerAdjoint_inclusion`,
  `image_not_lowerAdjoint_reverse`); prediction is therefore derived by complement (`predict`).
-/

namespace powerlib.TMIO.Finite

open OrderDual

/-! ## The strict chain -/

/-- Model points refine theory points by one coordinate. -/
def dropModel : Bool × Bool → Bool := Prod.fst

/-- Implementation points refine model points by one coordinate. -/
def dropImplementation : Bool × Bool × Bool → Bool × Bool := fun x => (x.1, x.2.1)

/-- The observation reads the second coordinate of an implementation point. -/
def observe : Bool × Bool × Bool → Bool := fun x => x.2.1

/-- The finite existence witness of v0.3 §8. -/
def witness : Seed (Set Bool) (Set (Bool × Bool)) (Set (Bool × Bool × Bool)) (Set Bool) where
  u₁ := kern dropModel
  u₂ := kern dropImplementation
  u₃ := preimage observe

@[tmio T, powerlib_foundation] theorem witness_l₁ : ⇑witness.l₁ = Set.preimage dropModel :=
  generate_kern dropModel

@[tmio T, powerlib_foundation] theorem witness_l₂ : ⇑witness.l₂ = Set.preimage dropImplementation :=
  generate_kern dropImplementation

@[tmio T, powerlib_foundation] theorem witness_l₃ : ⇑witness.l₃ = Set.image observe :=
  generate_preimage observe

/-- The extension edges lose nothing: their closure is the identity. -/
@[tmio T, powerlib_foundation] theorem witness_closure₁ (A : Set Bool) : witness.u₁ (witness.l₁ A) = A := by
  rw [witness_l₁]
  ext b
  show (∀ ⦃x : Bool × Bool⦄, dropModel x = b → dropModel x ∈ A) ↔ b ∈ A
  exact ⟨fun h => @h (b, false) rfl, fun h _ hx => hx ▸ h⟩

/-- The generated whole chain from the theory `{true}` allows both readings. -/
@[tmio T, powerlib_foundation] theorem witness_whole_true : generate witness.uTO {true} = Set.univ := by
  rw [witness.generate_uTO]
  ext b
  simp only [Function.comp_apply, witness_l₁, witness_l₂, witness_l₃, Set.mem_image,
    Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact ⟨(true, b, false), rfl, rfl⟩

/-- The generated whole chain sends the empty theory to no readings. -/
@[tmio T, powerlib_foundation] theorem witness_whole_empty : generate witness.uTO ∅ = ∅ := by
  rw [witness.generate_uTO]
  ext b
  simp [witness_l₁, witness_l₂, witness_l₃]

/-- The observation edge compresses information: its round trip strictly enlarges a singleton, so
the generated adjoints are not inverse functions. -/
@[tmio T, powerlib_foundation] theorem witness_roundtrip_strict :
    witness.u₃ (witness.l₃ {(true, true, true)}) ≠ {(true, true, true)} := by
  rw [witness_l₃]
  intro h
  have hmem : ((false, true, false) : Bool × Bool × Bool) ∈
      witness.u₃ (observe '' {(true, true, true)}) := ⟨(true, true, true), rfl, rfl⟩
  rw [h] at hmem
  simp at hmem

/-! ## The satisfaction witness -/

/-- Requirements are arbitrary sets of two-bit implementations; satisfaction is membership. -/
def member (x : Bool × Bool) (m : Set (Bool × Bool)) : Prop := x ∈ m

/-- The coupled space `a = b`. -/
def coupled : Set (Bool × Bool) := {(false, false), (true, true)}

/-- One requirement set generating the coupled space. -/
def requirementsOne : Set (Set (Bool × Bool)) := {coupled}

/-- A different requirement set generating the same space. -/
def requirementsTwo : Set (Set (Bool × Bool)) :=
  {{(false, false), (true, true), (false, true)}, {(false, false), (true, true), (true, false)}}

@[tmio T, powerlib_foundation] theorem requirementsOne_space :
    realize member requirementsOne = coupled := by
  ext ⟨a, b⟩
  cases a <;> cases b <;> simp [requirementsOne, coupled, member]

@[tmio T, powerlib_foundation] theorem requirementsTwo_space :
    realize member requirementsTwo = coupled := by
  ext ⟨a, b⟩
  cases a <;> cases b <;> simp [requirementsTwo, coupled, member]

/-- A narrower family is legal for the requirements but is not their complete space. -/
@[tmio T, powerlib_foundation] theorem narrow_legal_not_space :
    ({(false, false)} : Set (Bool × Bool)) ⊆ realize member requirementsOne ∧
      ({(false, false)} : Set (Bool × Bool)) ≠ realize member requirementsOne := by
  rw [requirementsOne_space]
  refine ⟨by simp [coupled], fun h => ?_⟩
  have hmem : ((true, true) : Bool × Bool) ∈ ({(false, false)} : Set (Bool × Bool)) :=
    h ▸ (by simp [coupled])
  simp at hmem

/-! ## Prediction is derived, not generated, in the requirement family -/

/-- With implementations ordered by reverse inclusion, the possible-observation image of
`Prod.fst` is not a lower adjoint into readings ordered by inclusion. -/
@[tmio T, powerlib_foundation] theorem image_not_lowerAdjoint_inclusion :
    ¬ ∃ u : Set Bool → (Set (Bool × Bool))ᵒᵈ,
      GaloisConnection (fun P : (Set (Bool × Bool))ᵒᵈ => Prod.fst '' ofDual P) u := by
  rintro ⟨u, gc⟩
  have h := gc.l_sup (a₁ := toDual ({(false, false)} : Set (Bool × Bool)))
    (a₂ := toDual ({(false, true)} : Set (Bool × Bool)))
  have h' := congrArg (fun s : Set Bool => false ∈ s) h
  simp at h'

/-- The same holds with readings ordered by reverse inclusion. -/
@[tmio T, powerlib_foundation] theorem image_not_lowerAdjoint_reverse :
    ¬ ∃ u : (Set Bool)ᵒᵈ → (Set (Bool × Bool))ᵒᵈ,
      GaloisConnection (fun P : (Set (Bool × Bool))ᵒᵈ => toDual (Prod.fst '' ofDual P)) u := by
  rintro ⟨u, gc⟩
  have h := gc.l_sup (a₁ := toDual ({(false, false)} : Set (Bool × Bool)))
    (a₂ := toDual ({(false, true)} : Set (Bool × Bool)))
  have h' := congrArg (fun s => false ∈ ofDual s) h
  simp at h'

end powerlib.TMIO.Finite
