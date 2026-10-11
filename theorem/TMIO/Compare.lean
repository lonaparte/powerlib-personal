import theorem.TMIO.Relation

/-! # Comparing connections

Two semantic maps on the same edge are compared through their generated forward maps: one lies
below the other exactly when the generated maps are ordered the other way, and they agree exactly
when the generated maps agree (`generate_le_generate_iff`, `generate_inj`).

A semantics is itself a connection: a satisfaction relation between implementations and sentences
gives, through `satisfaction`, the map from implementation families to the sentences they all
satisfy, whose generated map sends sentences to their models. A translation chain — sentences
translated into requirements (`cover`), requirements realized by implementations
(`satisfaction`) — is a second connection between the same layers. The chain agrees with the
semantics exactly when every sentence's translation realizes exactly its models, and lies below
it exactly when every translation realizes only models (`chain_eq_satisfaction_iff`,
`chain_le_satisfaction_iff`). Exactness and soundness of a translation are therefore statements
about two connections, not new notions. -/

namespace powerlib.TMIO

open OrderDual

section Order

variable {A B : Type*} [CompleteLattice A] [CompleteLattice B]

/-- One semantic map lies below another exactly when its generated forward map lies above. -/
@[powerlib_foundation] theorem generate_le_generate_iff (u v : sInfHom B A) :
    (∀ a, generate v a ≤ generate u a) ↔ ∀ b, u b ≤ v b := by
  constructor
  · intro h b
    exact (gc_generate v _ _).mp ((h (u b)).trans (generate_u_le u b))
  · intro h a
    exact (gc_generate v _ _).mpr (((gc_generate u).le_u_l a).trans (h _))

/-- Two semantic maps agree exactly when their generated forward maps agree. -/
@[powerlib_foundation] theorem generate_inj (u v : sInfHom B A) :
    ⇑(generate u) = ⇑(generate v) ↔ u = v := by
  constructor
  · intro h
    ext b : 1
    apply le_antisymm
    · exact (generate_le_generate_iff u v).mp (fun a => (congrFun h a).ge) b
    · exact (generate_le_generate_iff v u).mp (fun a => (congrFun h a).le) b
  · rintro rfl
    rfl

end Order

section Relational

variable {S Q X : Type*}

/-- No requirement leaves every implementation. -/
@[simp, powerlib_foundation] theorem realize_empty (sat : X → Q → Prop) :
    realize sat (∅ : Set Q) = Set.univ := by
  ext x
  simp

/-- A satisfaction relation sends an implementation family to the sentences whose models contain
it. -/
@[powerlib_foundation] theorem mem_satisfaction_iff_subset (holds : X → S → Prop)
    (P : (Set X)ᵒᵈ) (s : S) : s ∈ satisfaction holds P ↔ ofDual P ⊆ realize holds {s} := by
  simp only [mem_satisfaction, Set.subset_def, mem_realize, Set.mem_singleton_iff, forall_eq]

/-- The translation chain sends an implementation family to the sentences whose translation it
realizes. -/
@[powerlib_foundation] theorem mem_chain_iff_subset (tr : SetRel S Q) (sat : X → Q → Prop)
    (P : (Set X)ᵒᵈ) (s : S) :
    s ∈ (cover tr).comp (satisfaction sat) P ↔ ofDual P ⊆ realize sat (tr.image {s}) := by
  change (∀ q, (s, q) ∈ tr → q ∈ satisfaction sat P) ↔ _
  simp only [mem_satisfaction, Set.subset_def, mem_realize, SetRel.mem_image,
    Set.mem_singleton_iff, exists_eq_left]
  exact ⟨fun h x hx q hq => h q hq x hx, fun h q hq x hx => h x hx q hq⟩

/-- The chain's generated value at one sentence is the space of its translation. -/
@[powerlib_foundation] theorem generate_chain_singleton (tr : SetRel S Q) (sat : X → Q → Prop)
    (s : S) :
    ofDual (generate ((cover tr).comp (satisfaction sat)) {s}) = realize sat (tr.image {s}) := by
  rw [generate_comp, Function.comp_apply, congrFun (generate_cover tr)]
  rfl

/-- The chain agrees with the semantics exactly when every translation realizes exactly the
models of its sentence. -/
@[powerlib_foundation] theorem chain_eq_satisfaction_iff (tr : SetRel S Q) (sat : X → Q → Prop)
    (holds : X → S → Prop) :
    (cover tr).comp (satisfaction sat) = satisfaction holds ↔
      ∀ s, realize sat (tr.image {s}) = realize holds {s} := by
  constructor
  · intro h s
    ext x
    have := congrArg (fun u : sInfHom (Set X)ᵒᵈ (Set S) => s ∈ u (toDual {x})) h
    simp only [mem_chain_iff_subset, mem_satisfaction_iff_subset, ofDual_toDual,
      Set.singleton_subset_iff] at this
    exact Iff.of_eq this
  · intro h
    ext P s : 2
    rw [mem_chain_iff_subset, mem_satisfaction_iff_subset, h]

/-- The chain lies below the semantics exactly when every translation realizes only models of its
sentence. -/
@[powerlib_foundation] theorem chain_le_satisfaction_iff (tr : SetRel S Q) (sat : X → Q → Prop)
    (holds : X → S → Prop) :
    (∀ P, (cover tr).comp (satisfaction sat) P ≤ satisfaction holds P) ↔
      ∀ s, realize sat (tr.image {s}) ⊆ realize holds {s} := by
  constructor
  · intro h s
    have hs : s ∈ (cover tr).comp (satisfaction sat) (toDual (realize sat (tr.image {s}))) := by
      rw [mem_chain_iff_subset]
      exact subset_rfl
    have := h _ hs
    rwa [mem_satisfaction_iff_subset] at this
  · intro h P s hs
    rw [mem_chain_iff_subset] at hs
    rw [mem_satisfaction_iff_subset]
    exact hs.trans (h s)

end Relational

end powerlib.TMIO
