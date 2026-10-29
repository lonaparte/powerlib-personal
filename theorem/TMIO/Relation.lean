import Mathlib.Order.Rel.GaloisConnection
import theorem.TMIO.Representation

/-! # Standard semantic constructors (v0.3 §4, §7, §8)

Instances supply their edges through these constructors. Each constructor provides only the
semantic map `u`; the forward map is the generated lower adjoint, identified here with the
corresponding Mathlib construction by uniqueness of adjoints.

Scope.
* Generic: powerset lattices over arbitrary types of sentences, requirements, complete systems
  and readings, related by arbitrary satisfaction predicates, functions and relations; no model.

Source: TMIO v0.3 §4 (satisfaction), §7 (data analysis), §8 (fibre-universal image); Mathlib's
relational Galois connections (`Mathlib.Order.Rel.GaloisConnection`, `SetRel.image`,
`SetRel.core`, `SetRel.equivFixedPoints`) and `GaloisConnection.compl`; the generation theorem
of `theorem/TMIO/Generate.lean` and the seeds of `theorem/TMIO/Derived.lean`.

Results.
* `satisfaction`: requirements and complete systems related by satisfaction (v0.3 §4). The
  implementation layer is ordered by reverse inclusion; the generated map is the maximal legal
  implementation space `realize` (`satRel`, `mem_satisfaction`, `generate_satisfaction`,
  `mem_realize`, maximality `realize_max`, `realize_union`, `realize_antitone`,
  `exists_realize_iff`, `realizableEquiv`).
* `preimage`: a deterministic map such as a data analysis (v0.3 §7); generates the direct image
  (`preimage_apply`, `generate_preimage`, `generate_preimage_comp`).
* `kern`: the fibre-universal image (v0.3 §8); generates the preimage (`kern_apply`,
  `generate_kern`).
* `cover`: a translation relation from theory sentences to requirements; generates its image
  (`gc_image_core`, translation tables `table`, `image_table_singleton`, `image_table`,
  `generate_cover`).
* `possibly`: a relational observation in reverse-inclusion orders; generates certification
  (`certify`, `mem_certify`, `gc_certify`, `mem_possibly`, `generate_possibly`). Prediction
  (possible observations) is then derived by complement through Mathlib's
  `GaloisConnection.compl`, which is available because powerset lattices are Boolean (`predict`,
  `allPre`, `predict_eq_image`, `mem_allPre`, `gc_predict`).
* `relationalSeed`: the seed built from `cover`, `satisfaction` and `possibly`; its whole chain
  translates, realizes and certifies (`relationalSeed_whole`), and soundness of the translation
  propagates to every certified observation (`relationalSeed_sound`).
* Applied forms of the generated maps: `generate_preimage_apply`, `generate_kern_apply`,
  `generate_cover_apply`, `generate_possibly_apply`.
* Satisfaction along maps and products: `realize_comap`; exactness relative to a context,
  `ExactUnder` (`exactUnder_empty_iff`: with an empty context, plain exactness); sums of
  requirement languages, `satSum` and `realize_sum` (component requirements carve out a product
  space).
-/

namespace powerlib.TMIO

open OrderDual

/-! ## Satisfaction: requirements → maximal legal implementation space -/

section Satisfaction

variable {X Q : Type*}

/-- Satisfaction as a Mathlib relation from requirements to complete systems. -/
def satRel (sat : X → Q → Prop) : SetRel Q X := {p | sat p.2 p.1}

/-- The M—I edge: `Guarantees P = {q | ∀ x ∈ P, sat x q}`, from implementations ordered by
reverse inclusion to requirement sets ordered by inclusion. It is the upper adjoint in Mathlib's
`SetRel.gc_leftDual_rightDual`, hence preserves arbitrary infima. -/
def satisfaction (sat : X → Q → Prop) : sInfHom (Set X)ᵒᵈ (Set Q) where
  toFun := (satRel sat).rightDual ∘ ofDual
  map_sInf' s := by
    rw [sInf_image]
    exact (satRel sat).gc_leftDual_rightDual.u_sInf

@[tmio T, simp, powerlib_foundation] theorem mem_satisfaction (sat : X → Q → Prop) (P : (Set X)ᵒᵈ)
    (q : Q) :
    connection% (q ∈ satisfaction sat P ↔ ∀ x ∈ ofDual P, sat x q) := show q ∈ satisfaction sat P ↔ ∀ x ∈ ofDual P, sat x q from Iff.rfl

/-- The generated forward map is Mathlib's `leftDual`. -/
@[tmio T, powerlib_foundation] theorem generate_satisfaction (sat : X → Q → Prop) :
    connection% (⇑(generate (satisfaction sat)) = toDual ∘ (satRel sat).leftDual) := show ⇑(generate (satisfaction sat)) = toDual ∘ (satRel sat).leftDual from
  (generate_unique _ (satRel sat).gc_leftDual_rightDual).symm

/-- The generated maximal legal implementation space of the requirements `Γ`. -/
def realize (sat : X → Q → Prop) (Γ : Set Q) : Set X := ofDual (generate (satisfaction sat) Γ)

@[tmio T, simp, powerlib_foundation] theorem mem_realize (sat : X → Q → Prop) (Γ : Set Q) (x : X) :
    connection% (x ∈ realize sat Γ ↔ ∀ q ∈ Γ, sat x q) := by
  change x ∈ realize sat Γ ↔ ∀ q ∈ Γ, sat x q
  rw [realize, congrFun (generate_satisfaction sat) Γ]
  exact Iff.rfl

/-- Maximality (v0.3 §4): a family is legal exactly when it guarantees every requirement. -/
@[tmio T, powerlib_foundation] theorem realize_max (sat : X → Q → Prop) (Γ : Set Q) (P : Set X) :
    connection% (P ⊆ realize sat Γ ↔ Γ ⊆ satisfaction sat (toDual P)) := show P ⊆ realize sat Γ ↔ Γ ⊆ satisfaction sat (toDual P) from
  gc_generate (satisfaction sat) Γ (toDual P)

/-- Joining requirements intersects their spaces. -/
@[tmio T, powerlib_foundation] theorem realize_union (sat : X → Q → Prop) (Γ Δ : Set Q) :
    connection% (realize sat (Γ ∪ Δ) = realize sat Γ ∩ realize sat Δ) := by
  change realize sat (Γ ∪ Δ) = realize sat Γ ∩ realize sat Δ
  show ofDual (generate (satisfaction sat) (Γ ⊔ Δ)) = _
  rw [generate_sup, ofDual_sup]
  rfl

/-- More requirements never enlarge the space. -/
@[tmio T, powerlib_foundation] theorem realize_antitone (sat : X → Q → Prop) {Γ Δ : Set Q}
    (h : Γ ⊆ Δ) :
    connection% (realize sat Δ ⊆ realize sat Γ) := show realize sat Δ ⊆ realize sat Γ from
  generate_monotone (satisfaction sat) h

/-- A family of systems is the space of some requirement set exactly when it equals the space of
the requirements it guarantees. -/
@[tmio T, powerlib_foundation] theorem exists_realize_iff (sat : X → Q → Prop) (P : Set X) :
    connection% ((∃ Γ, realize sat Γ = P) ↔ realize sat (satisfaction sat (toDual P)) = P) := by
  change (∃ Γ, realize sat Γ = P) ↔ realize sat (satisfaction sat (toDual P)) = P
  constructor
  · rintro ⟨Γ, rfl⟩
    exact congrArg ofDual ((gc_generate (satisfaction sat)).l_u_l_eq_l Γ)
  · intro h
    exact ⟨_, h⟩

/-- Closed requirement sets and realizable spaces correspond (Mathlib `SetRel.equivFixedPoints`).
-/
def realizableEquiv (sat : X → Q → Prop) :
    (satRel sat).leftFixedPoints ≃ (satRel sat).rightFixedPoints :=
  (satRel sat).equivFixedPoints

end Satisfaction

/-! ## Deterministic maps -/

section Function

variable {D Y Z : Type*}

/-- A deterministic map, such as a data analysis, as the edge `B ↦ f⁻¹ B`. -/
def preimage (f : D → Y) : sInfHom (Set Y) (Set D) := (CompleteLatticeHom.setPreimage f).tosInfHom

@[tmio T, simp, powerlib_foundation] theorem preimage_apply (f : D → Y) (B : Set Y) :
    connection% (preimage f B = f ⁻¹' B) := show preimage f B = f ⁻¹' B from rfl

/-- The generated forward map of a deterministic map is its direct image (v0.3 §7). -/
@[tmio T, powerlib_foundation] theorem generate_preimage (f : D → Y) :
    connection% (⇑(generate (preimage f)) = Set.image f) := show ⇑(generate (preimage f)) = Set.image f from
  (generate_unique _ Set.image_preimage).symm

/-- Executing two analyses in sequence is the composite edge. -/
@[tmio T, powerlib_foundation] theorem generate_preimage_comp (f : D → Y) (g : Y → Z) :
    connection% (⇑(generate ((preimage f).comp (preimage g))) = Set.image (g ∘ f)) := by
  change ⇑(generate ((preimage f).comp (preimage g))) = Set.image (g ∘ f)
  rw [generate_comp, generate_preimage, generate_preimage]
  funext s
  exact (Set.image_comp g f s).symm

/-- The fibre-universal image `B ↦ {y | f⁻¹{y} ⊆ B}` (v0.3 §8). -/
def kern (f : D → Y) : sInfHom (Set D) (Set Y) where
  toFun := Set.kernImage f
  map_sInf' s := by
    rw [sInf_image]
    exact Set.preimage_kernImage.u_sInf

@[tmio T, simp, powerlib_foundation] theorem kern_apply (f : D → Y) (B : Set D) :
    connection% (kern f B = Set.kernImage f B) := show kern f B = Set.kernImage f B from rfl

/-- The generated forward map of the fibre-universal image is the preimage. -/
@[tmio T, powerlib_foundation] theorem generate_kern (f : D → Y) :
    connection% (⇑(generate (kern f)) = Set.preimage f) := show ⇑(generate (kern f)) = Set.preimage f from
  (generate_unique _ Set.preimage_kernImage).symm

end Function

/-! ## Relations: translation and relational observation -/

section Relation

variable {S Q X V : Type*}

/-- Relational image and core form a Galois connection (Mathlib `SetRel.image_subset_iff`). -/
@[tmio T, powerlib_foundation] theorem gc_image_core (R : SetRel S Q) :
    connection% (GaloisConnection (generate (cover R)) (cover R)) :=
  (generate (cover R)).gc

/-- A translation table, each sentence listing its requirements, as a relation. -/
def table (t : S → Set Q) : SetRel S Q := {p | p.2 ∈ t p.1}

/-- The generated forward map translates a set of sentences into the union of their
translations. -/
@[tmio T, powerlib_foundation] theorem generate_cover (R : SetRel S Q) :
    connection% (⇑(generate (cover R)) = R.image) := show ⇑(generate (cover R)) = R.image from
  (generate_unique _ (show GaloisConnection R.image (cover R) from
    fun _ _ => SetRel.image_subset_iff)).symm

@[tmio T, simp, powerlib_foundation] theorem image_table_singleton (t : S → Set Q) (φ : S) :
    connection% (generate (cover (table t)) {φ} = t φ) := by
  unfold Statement
  rw [generate_cover]
  ext q
  simp [table]

@[tmio T, powerlib_foundation] theorem image_table (t : S → Set Q) (Φ : Set S) :
    connection% (generate (cover (table t)) Φ = ⋃ φ ∈ Φ, t φ) := by
  unfold Statement
  rw [generate_cover]
  ext q
  simp [table]

/-- Certification: the readings all of whose possible sources lie in `P`. -/
def certify (R : SetRel X V) (P : Set X) : Set V := R.inv.core P

@[tmio T, simp, powerlib_foundation] theorem mem_certify (R : SetRel X V) (P : Set X) (v : V) :
    connection% (v ∈ certify R P ↔ ∀ x, (x, v) ∈ R → x ∈ P) := show v ∈ certify R P ↔ ∀ x, (x, v) ∈ R → x ∈ P from
  ⟨fun h _ hx => h hx, fun h _ hx => h _ hx⟩

/-- Relational observation in the requirement family: `B ↦ R.preimage B`, the implementations
that may produce some reading in `B`, between reverse-inclusion orders. -/
def possibly (R : SetRel X V) : sInfHom (Set V)ᵒᵈ (Set X)ᵒᵈ where
  toFun := toDual ∘ R.preimage ∘ ofDual
  map_sInf' s := by
    rw [sInf_image]
    exact (show GaloisConnection (toDual ∘ certify R ∘ ofDual)
      (toDual ∘ R.preimage ∘ ofDual) from
      (show GaloisConnection R.inv.image R.inv.core from
        fun _ _ => SetRel.image_subset_iff).dual).u_sInf

/-- Certification is the lower adjoint of possible-source preimage in reverse-inclusion orders. -/
@[tmio T, powerlib_foundation] theorem gc_certify (R : SetRel X V) :
    connection% (GaloisConnection (toDual ∘ certify R ∘ ofDual) (possibly R)) :=
  (show GaloisConnection R.inv.image R.inv.core from
    fun _ _ => SetRel.image_subset_iff).dual

@[tmio T, simp, powerlib_foundation] theorem mem_possibly (R : SetRel X V) (B : (Set V)ᵒᵈ) (x : X) :
    connection% (x ∈ ofDual (possibly R B) ↔ ∃ v ∈ ofDual B, (x, v) ∈ R) := show x ∈ ofDual (possibly R B) ↔ ∃ v ∈ ofDual B, (x, v) ∈ R from Iff.rfl

/-- The generated forward map of a relational observation is certification. -/
@[tmio T, powerlib_foundation] theorem generate_possibly (R : SetRel X V) :
    connection% (⇑(generate (possibly R)) = toDual ∘ certify R ∘ ofDual) := show ⇑(generate (possibly R)) = toDual ∘ certify R ∘ ofDual from
  (generate_unique _ (gc_certify R)).symm

/-- Possible observations, derived from certification by complement. -/
def predict (R : SetRel X V) (P : Set X) : Set V := (certify R Pᶜ)ᶜ

/-- The implementations all of whose possible readings lie in `B`. -/
def allPre (R : SetRel X V) (B : Set V) : Set X := (R.preimage Bᶜ)ᶜ

/-- The derived prediction is exactly the possible-observation image. -/
@[tmio T, powerlib_foundation] theorem predict_eq_image (R : SetRel X V) (P : Set X) :
    connection% (predict R P = R.image P) := by
  change predict R P = R.image P
  ext v
  simp only [predict, Set.mem_compl_iff, mem_certify, not_forall, not_not, SetRel.mem_image]
  exact ⟨fun ⟨x, hx, hP⟩ => ⟨x, hP, hx⟩, fun ⟨x, hP, hx⟩ => ⟨x, hx, hP⟩⟩

@[tmio T, simp, powerlib_foundation] theorem mem_allPre (R : SetRel X V) (B : Set V) (x : X) :
    connection% (x ∈ (ofDual (possibly R (toDual Bᶜ)))ᶜ ↔ ∀ v, (x, v) ∈ R → v ∈ B) := by
  change x ∈ allPre R B ↔ ∀ v, (x, v) ∈ R → v ∈ B
  simp only [allPre, Set.mem_compl_iff, SetRel.mem_preimage, not_exists, not_and]
  exact ⟨fun h v hx => by_contra fun hv => h v hv hx, fun h v hv hx => hv (h v hx)⟩

/-- Prediction is again adjoint, obtained from the generated certification edge by Mathlib's
complement transport `GaloisConnection.compl`; nothing new is postulated. -/
@[tmio T, powerlib_foundation] theorem gc_predict (R : SetRel X V) :
    connection% (GaloisConnection
      (fun B : (Set V)ᵒᵈ => toDual (ofDual (possibly R (toDual (ofDual B)ᶜ)))ᶜ)
      (fun P : (Set X)ᵒᵈ => toDual (predict R (ofDual P)))) :=
  (gc_certify R).compl

end Relation

/-! ## The standard relational seed -/

section Seed

variable {S Q X V : Type*}

/-- The standard relational seed: a translation of theory sentences into requirements, the
satisfaction of requirements by complete systems, and a relational observation of systems. -/
def relationalSeed (tr : SetRel S Q) (sat : X → Q → Prop) (obs : SetRel X V) :
    Seed (Set S) (Set Q) (Set X)ᵒᵈ (Set V)ᵒᵈ where
  u₁ := cover tr
  u₂ := satisfaction sat
  u₃ := possibly obs

/-- The generated whole chain of the standard relational seed: translate the sentences, take the
maximal legal space, and certify observations against it. -/
@[tmio T, powerlib_foundation] theorem relationalSeed_whole (tr : SetRel S Q) (sat : X → Q → Prop)
    (obs : SetRel X V) (Φ : Set S) :
    connection% (ofDual (generate (relationalSeed tr sat obs).uTO Φ) =
      certify obs (realize sat (tr.image Φ))) := by
  change ofDual (generate (relationalSeed tr sat obs).uTO Φ) =
        certify obs (realize sat (tr.image Φ))
  rw [Seed.generate_uTO]
  simp only [Function.comp_apply, Seed.l₁, Seed.l₂, Seed.l₃, relationalSeed]
  rw [congrFun (generate_cover tr), congrFun (generate_possibly obs)]
  rfl

/-- Soundness propagates along the generated chain: if the translation of each sentence of `Φ`
is sound for its denotation, every system that may produce an observation certified for `Φ`
satisfies every sentence of `Φ`. -/
@[tmio T, powerlib_foundation] theorem relationalSeed_sound (tr : SetRel S Q) (sat : X → Q → Prop)
    (obs : SetRel X V) {den : S → Set X} {Φ : Set S}
    (hsound : ∀ φ ∈ Φ, realize sat (tr.image {φ}) ⊆ den φ) {v : V}
    (hv : v ∈ ofDual (generate (relationalSeed tr sat obs).uTO Φ)) {x : X}
    (hx : (x, v) ∈ obs) : ∀ φ ∈ Φ, x ∈ den φ := by
  rw [relationalSeed_whole, (connection_proof% mem_certify)] at hv
  intro φ hφ
  exact hsound φ hφ (realize_antitone sat (SetRel.image_mono (Set.singleton_subset_iff.mpr hφ)) (hv x hx))

end Seed

/-! ## Applied forms of the generated maps -/

@[tmio T, simp, powerlib_foundation] theorem generate_preimage_apply {D Y : Type*} (f : D → Y)
    (A : Set D) :
    connection% (generate (preimage f) A = f '' A) := show generate (preimage f) A = f '' A from
  congrFun (generate_preimage f) A

@[tmio T, simp, powerlib_foundation] theorem generate_kern_apply {D Y : Type*} (f : D → Y) (B : Set Y) :
    connection% (generate (kern f) B = f ⁻¹' B) := show generate (kern f) B = f ⁻¹' B from
  congrFun (generate_kern f) B

@[tmio T, simp, powerlib_foundation] theorem generate_cover_apply {S Q : Type*} (R : SetRel S Q)
    (Φ : Set S) :
    connection% (generate (cover R) Φ = R.image Φ) := show generate (cover R) Φ = R.image Φ from
  congrFun (generate_cover R) Φ

@[tmio T, simp, powerlib_foundation] theorem generate_possibly_apply {X V : Type*} (R : SetRel X V)
    (P : (Set X)ᵒᵈ) :
    connection% (ofDual (generate (possibly R) P) = certify R (ofDual P)) := show ofDual (generate (possibly R) P) = certify R (ofDual P) from
  congrArg ofDual (congrFun (generate_possibly R) P)

/-! ## Satisfaction along maps and products -/

/-- Satisfaction read through a map of complete systems pulls the space back. -/
@[tmio T, simp, powerlib_foundation] theorem realize_comap {X Y Q : Type*} (sat : Y → Q → Prop)
    (e : X → Y) (Γ : Set Q) :
    connection% (realize (fun x q => sat (e x) q) Γ = e ⁻¹' realize sat Γ) := by
  change realize (fun x q => sat (e x) q) Γ = e ⁻¹' realize sat Γ
  ext x
  simp

/-- A requirement set `Γ` is exact for `S` relative to the context `Δ`: within the space of `Δ`
it carves out exactly `S`. With an empty context this is plain exactness. -/
def ExactUnder {X Q : Type*} (sat : X → Q → Prop) (Δ Γ : Set Q) (S : Set X) : Prop :=
  realize sat (Γ ∪ Δ) = S ∩ realize sat Δ

@[tmio T, powerlib_foundation] theorem exactUnder_empty_iff {X Q : Type*} (sat : X → Q → Prop)
    (Γ : Set Q) (S : Set X) :
    connection% (ExactUnder sat ∅ Γ S ↔ realize sat Γ = S) := by
  change ExactUnder sat ∅ Γ S ↔ realize sat Γ = S
  have h : realize sat (∅ : Set Q) = Set.univ := by
    ext x
    simp
  simp [ExactUnder, h]

/-- Satisfaction of a sum of requirement languages by pairs of complete systems. -/
def satSum {X₁ X₂ Q₁ Q₂ : Type*} (sat₁ : X₁ → Q₁ → Prop) (sat₂ : X₂ → Q₂ → Prop) :
    X₁ × X₂ → Q₁ ⊕ Q₂ → Prop
  | x, .inl q => sat₁ x.1 q
  | x, .inr q => sat₂ x.2 q

/-- Requirements that each speak about one component carve out a product space. -/
@[tmio T, powerlib_foundation] theorem realize_sum {X₁ X₂ Q₁ Q₂ : Type*} (sat₁ : X₁ → Q₁ → Prop)
    (sat₂ : X₂ → Q₂ → Prop) (Γ₁ : Set Q₁) (Γ₂ : Set Q₂) :
    connection% (realize (satSum sat₁ sat₂) (Sum.inl '' Γ₁ ∪ Sum.inr '' Γ₂) =
      realize sat₁ Γ₁ ×ˢ realize sat₂ Γ₂) := by
  change realize (satSum sat₁ sat₂) (Sum.inl '' Γ₁ ∪ Sum.inr '' Γ₂) =
        realize sat₁ Γ₁ ×ˢ realize sat₂ Γ₂
  ext ⟨x₁, x₂⟩
  simp [mem_realize, satSum, or_imp, forall_and]

end powerlib.TMIO
