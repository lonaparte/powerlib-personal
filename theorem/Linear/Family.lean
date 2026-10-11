import theorem.Linear.Transfer
import theorem.TMIO.Relation

/-! # Linear families

A family of complete systems enters the library through one map, its plant map `X → Plant n p`.
The denotation of every behavioural sentence over the family is the Flow semantics of the plant's
zero-input field, pulled back along the plant map (`den`); it is never restated per family.

A `Family` bundles the three semantic maps a family supplies and nothing else: the plant map,
the satisfaction relation of its requirement language, and the translation table of the
behavioural sentences. Its TMIO seed for any observation, the certified observations, and its
reading in another representation (`comap`) are generated, together with what exactness or
soundness of a translation gives along the whole chain. A family proves one kind of domain fact —
which requirements carve out which denotations — and inherits the rest. -/

noncomputable section

namespace powerlib.Linear

open LinearSystems TMIO OrderDual

variable {n p : ℕ} {X Q : Type*}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The denotation of a sentence over a family: the Flow semantics, pulled back. -/
def den (plant : X → Plant n p) (P : Flow.Property) : Set X :=
  plant ⁻¹' {M | P.holds (affineLinearVectorField M.A 0) 0}

/-- Every attractive sentence denotes the Hurwitz members of the family. -/
@[powerlib_foundation] theorem den_attractive (plant : X → Plant n p) {P : Flow.Property}
    (hP : P.Attractive) : den plant P = {x | IsHurwitz (plant x).A} := by
  ext x
  exact holds_iff_isHurwitz 0 hP

/-- A requirement set that carves out the Hurwitz members is an exact translation of every
attractive sentence. -/
@[powerlib_foundation] theorem realize_eq_den {plant : X → Plant n p} {sat : X → Q → Prop}
    {Γ : Set Q} (h : realize sat Γ = {x | IsHurwitz (plant x).A}) {P : Flow.Property}
    (hP : P.Attractive) : realize sat Γ = den plant P := by
  rw [h, den_attractive plant hP]

/-- The same exactness relative to a context of requirements. -/
@[powerlib_foundation] theorem exactUnder_den {plant : X → Plant n p} {sat : X → Q → Prop}
    {Δ Γ : Set Q} (h : ExactUnder sat Δ Γ {x | IsHurwitz (plant x).A}) {P : Flow.Property}
    (hP : P.Attractive) : ExactUnder sat Δ Γ (den plant P) := by
  rwa [ExactUnder, den_attractive plant hP]

/-- At any constant input with an equilibrium, an attractive sentence holds there exactly when
the plant is Hurwitz: the behaviour about every operating point is the zero-input behaviour. -/
@[powerlib_foundation] theorem holds_input_iff (M : Plant n p) {u : Fin p → ℝ} {e : ℝⁿ}
    (he : IsEquilibrium (M.inputField u) e) {P : Flow.Property} (hP : P.Attractive) :
    P.holds (M.inputField u) e ↔ IsHurwitz M.A := by
  rw [M.inputField_eq he]
  exact holds_iff_isHurwitz e hP

@[simp, powerlib_foundation] theorem mem_den {plant : X → Plant n p} {x : X} {P : Flow.Property} :
    x ∈ den plant P ↔ P.holds (affineLinearVectorField (plant x).A 0) 0 := Iff.rfl

/-- A member with a Hurwitz plant satisfies every attractive sentence. -/
@[powerlib_foundation, aesop unsafe 80% apply] theorem mem_den_of_isHurwitz
    {plant : X → Plant n p} {x : X} {P : Flow.Property} (hP : P.Attractive)
    (h : IsHurwitz (plant x).A) : x ∈ den plant P :=
  (holds_iff_isHurwitz 0 hP).mpr h

/-- A certificate for a member's state matrix proves the member in every attractive sentence. -/
@[powerlib_foundation] theorem Certificate.mem_den {plant : X → Plant n p} {x : X}
    (c : Certificate (plant x).A) {P : Flow.Property} (hP : P.Attractive) : x ∈ den plant P :=
  c.holds 0 hP

/-- A member satisfying an attractive sentence samples to a contraction: over some integer
horizon every zero-input solution segment shrinks by a fixed factor. -/
@[powerlib_foundation] theorem mem_den_contractive {plant : X → Plant n p} {x : X}
    {P : Flow.Property} (hP : P.Attractive) (hx : x ∈ den plant P) :
    ∃ k : ℕ, 0 < k ∧ ∃ c < 1, ∀ (t₀ : ℝ) (φ : ℝ → ℝⁿ),
      IsTrajectoryOn φ (affineLinearVectorField (plant x).A 0) t₀ (t₀ + k) →
        ‖φ (t₀ + k)‖ ≤ c * ‖φ t₀‖ := by
  simpa using contractive_sampling 0 hP hx

/-! ## Families -/

/-- A linear family: the plant map of its complete systems, the satisfaction relation of its
requirement language, and the translation of the behavioural sentences into requirements. -/
structure Family (X Q : Type*) (n p : ℕ) where
  /-- The plant map. -/
  plant : X → Plant n p
  /-- Satisfaction of a requirement by a complete system. -/
  Meets : X → Q → Prop
  /-- The requirements each sentence translates into. -/
  translate : Flow.Property → Set Q

namespace Family

variable {Y V : Type*} (F : Family X Q n p)

/-- The denotation of a sentence over the family. -/
abbrev den (P : Flow.Property) : Set X := Linear.den F.plant P

/-- The translation table as the T–M relation. -/
abbrev translation : SetRel Flow.Property Q := table F.translate

/-- The family's TMIO seed for an observation of its complete systems. -/
abbrev seed (obs : SetRel X V) : Seed (Set Flow.Property) (Set Q) (Set X)ᵒᵈ (Set V)ᵒᵈ :=
  relationalSeed F.translation F.Meets obs

/-- The translation of `P` carves out exactly the denotation of `P`. -/
def Exact (P : Flow.Property) : Prop := realize F.Meets (F.translate P) = F.den P

/-- The translation of `P` carves out only systems satisfying `P`. -/
def Sound (P : Flow.Property) : Prop := realize F.Meets (F.translate P) ⊆ F.den P

/-- Within the space of the requirement context `Δ`, the translation of `P` is exact. -/
def ExactUnder (Δ : Set Q) (P : Flow.Property) : Prop :=
  TMIO.ExactUnder F.Meets Δ (F.translate P) (F.den P)

/-- Within the space of the requirement context `Δ`, the translation of `P` is sound. -/
def SoundUnder (Δ : Set Q) (P : Flow.Property) : Prop :=
  realize F.Meets (F.translate P ∪ Δ) ⊆ F.den P

variable {F}

@[powerlib_foundation] theorem Exact.sound {P : Flow.Property} (h : F.Exact P) : F.Sound P :=
  h.le

@[powerlib_foundation] theorem Sound.soundUnder {P : Flow.Property} (h : F.Sound P) (Δ : Set Q) :
    F.SoundUnder Δ P :=
  (realize_antitone F.Meets Set.subset_union_left).trans h

@[powerlib_foundation] theorem ExactUnder.soundUnder {Δ : Set Q} {P : Flow.Property}
    (h : F.ExactUnder Δ P) : F.SoundUnder Δ P := by
  unfold SoundUnder
  rw [show realize F.Meets (F.translate P ∪ Δ) = F.den P ∩ realize F.Meets Δ from h]
  exact Set.inter_subset_left

@[powerlib_foundation] theorem exactUnder_empty_iff {P : Flow.Property} :
    F.ExactUnder ∅ P ↔ F.Exact P :=
  TMIO.exactUnder_empty_iff F.Meets (F.translate P) (F.den P)

/-- For an attractive sentence, a translation carving out the Hurwitz members is exact. -/
@[powerlib_foundation] theorem exact_of_isHurwitz {P : Flow.Property} (hP : P.Attractive)
    (h : realize F.Meets (F.translate P) = {x | IsHurwitz (F.plant x).A}) : F.Exact P :=
  realize_eq_den h hP

/-- The same relative to a requirement context. -/
@[powerlib_foundation] theorem exactUnder_of_isHurwitz {Δ : Set Q} {P : Flow.Property}
    (hP : P.Attractive)
    (h : TMIO.ExactUnder F.Meets Δ (F.translate P) {x | IsHurwitz (F.plant x).A}) :
    F.ExactUnder Δ P :=
  exactUnder_den h hP

variable (F)

/-- The certified observations of a sentence with an exact translation, generated along the
whole chain, are those whose every possible source satisfies the sentence. -/
@[powerlib_foundation] theorem certified (obs : SetRel X V) {P : Flow.Property} (h : F.Exact P) :
    ofDual (generate (F.seed obs).uTO {P}) = certify obs (F.den P) := by
  rw [relationalSeed_whole, image_table_singleton]
  exact congrArg (certify obs) h

/-- An observation certified for sentences with sound translations proves them for every
system that may produce it. -/
@[powerlib_foundation] theorem certifies {obs : SetRel X V} {Φ : Set Flow.Property}
    (hs : ∀ P ∈ Φ, F.Sound P) {v : V} (hv : v ∈ ofDual (generate (F.seed obs).uTO Φ)) {x : X}
    (hx : (x, v) ∈ obs) : ∀ P ∈ Φ, x ∈ F.den P :=
  relationalSeed_sound F.translation F.Meets obs (den := F.den)
    (fun P hP => by rw [image_table_singleton]; exact hs P hP) hv hx

/-- The family read in another representation, through a map of complete systems. -/
def comap (g : Y → X) : Family Y Q n p :=
  ⟨F.plant ∘ g, fun y q => F.Meets (g y) q, F.translate⟩

@[powerlib_foundation] theorem den_comap (g : Y → X) (P : Flow.Property) :
    (F.comap g).den P = g ⁻¹' F.den P := rfl

@[powerlib_foundation] theorem realize_comap (g : Y → X) (Γ : Set Q) :
    realize (F.comap g).Meets Γ = g ⁻¹' realize F.Meets Γ :=
  TMIO.realize_comap F.Meets g Γ

variable {F}

/-- Exactness survives every change of representation. -/
@[powerlib_foundation] theorem Exact.comap {P : Flow.Property} (h : F.Exact P) (g : Y → X) :
    (F.comap g).Exact P := by
  unfold Exact at h ⊢
  rw [realize_comap, den_comap]
  exact congrArg (g ⁻¹' ·) h

/-- Soundness survives every change of representation. -/
@[powerlib_foundation] theorem Sound.comap {P : Flow.Property} (h : F.Sound P) (g : Y → X) :
    (F.comap g).Sound P := by
  unfold Sound at h ⊢
  rw [realize_comap, den_comap]
  exact Set.preimage_mono h

end Family

/-- A one-state plant is Hurwitz exactly when its state coefficient is negative. -/
@[powerlib_foundation] theorem isHurwitz_one_iff (a : ℝ) : IsHurwitz !![a] ↔ a < 0 := by
  rw [← spectrallyStable_iff_isHurwitz]
  constructor
  · intro h
    have := h a (by simp [characteristicMatrix, Matrix.det_unique])
    simpa using this
  · intro ha s hs
    simp [characteristicMatrix, Matrix.det_unique] at hs
    have : s = a := by linear_combination hs
    rw [this]
    simpa using ha

end powerlib.Linear
