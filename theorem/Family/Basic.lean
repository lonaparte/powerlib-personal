import theorem.Port.Basic
import theorem.TMIO.Compare
import theorem.TMIO.Representation

/-! # Model families

A model family enters the library through three semantic maps and nothing else: its system map,
reading each complete system as a system of one of the kinds the semantic layer reads (a
continuous-time or a discrete-time system with ports, or a random continuous-time system with an
operating envelope, `Behaviour`); the satisfaction relation of
its requirement language; and the translation of every sentence into requirements.

Two connections between sentences and complete systems are generated from them. The semantics
connection (`semantics`) sends a family of complete systems to the sentences they all satisfy;
its generated map sends a sentence to its models, the denotation (`den`). The translation chain
(`chain`) composes the translation table with satisfaction. Exactness of a translation is the
agreement of the two connections at a sentence and soundness is the chain lying below the
semantics there (`exact_iff_generate`, `sound_iff_generate`); over all sentences these are the
equality and the order of the two connections (`chain_eq_semantics_iff`,
`chain_le_semantics_iff`). The relative notions restrict both connections to the space of a
requirement context.

Observations extend the chain to the standard relational seed: certification, refutation and
changes of representation are generated once here. A family proves facts of three shapes only:
the value of a connection at a point, the agreement or order of two connections, and witnesses
where two connections part.

Scope.
* Generic: arbitrary types of complete systems `X`, requirements `Q` and readings `V`, systems
  with `n` states and `p` ports of either kind (`theorem/Port/Defs.lean`); no model.
* Families of autonomous fields (`IsAutonomous`, no ports, continuous time) and of autonomous maps
  (`IsAutonomousMap`, no ports, discrete time with a step length) are recognized here.

Source: the TMIO framework: satisfaction, translation tables and relational observations
(`theorem/TMIO/Relation.lean`), the comparison of connections (`theorem/TMIO/Compare.lean`,
`chain_eq_satisfaction_iff`, `chain_le_satisfaction_iff`) and seeds
(`theorem/TMIO/Derived.lean`); the single semantics `Sentence.holds` (`theorem/Port/Defs.lean`).

Results.
* `Family` (`system`, `meets`, `translate`), `Holds`, `semantics`, `den` (`mem_den`,
  `den_eq_generate`), `chain`, `seed` (the family's seed for an observation, `seed_uTI`),
  `generate_chain_singleton`.
* `Exact`, `Sound`, `ExactUnder`, `SoundUnder`; `exact_iff_generate`, `sound_iff_generate`,
  `chain_eq_semantics_iff`, `chain_le_semantics_iff`, `Exact.sound`, `Sound.soundUnder`,
  `ExactUnder.soundUnder`, `exactUnder_empty_iff`.
* Sentences without a translation: `sound_of_translate_eq_univ`, `exact_of_translate_eq_univ`,
  `exact_of_translate_eq_empty`.
* Observations: `certified` (with an exact translation, the certified observations are those
  whose every possible source satisfies the sentence), `certifies`, `refutes`.
* Changes of representation: `den_comap`, `realize_comap`, `den_extend`, `realize_extend_inl`,
  `Exact.comap`, `Sound.comap`, `Exact.extend`, `Sound.extend`.
* Autonomous families: `IsAutonomous.mem_den_flow`, `IsAutonomous.den_passive`,
  `IsAutonomousMap.mem_den_flow`, `IsAutonomousMap.den_passive` (a system without ports is
  passive).
* Families read without an envelope: `den_envelope_of_continuous`, `IsAutonomous.den_envelope`,
  `IsAutonomousMap.den_envelope` (every envelope sentence denotes the whole family).

Family and connection conclusions.
* `Family.comap g : Family Y Q n p` (the family read in another representation, through a map of
  complete systems) and `Family.extend g extra : Family Y (Q ⊕ R) n p` (its requirement language
  extended by requirements stated on the new representation; sentences keep their translations).
  Exactness and soundness survive both (`Exact.comap`, `Sound.comap`, `Exact.extend`,
  `Sound.extend`).
* No connection statements: the module states the generic laws once; model modules publish their
  conclusions as connection statements.
-/

noncomputable section

namespace powerlib

open TMIO OrderDual

/-- A model family: complete systems `X` read as systems with `n` states and `p` ports, the
satisfaction relation of a requirement language `Q`, and the translation of every sentence. -/
structure Family (X Q : Type*) (n p : ℕ) where
  /-- The system map, to a continuous-time or a discrete-time system. -/
  system : X → Behaviour n p
  /-- Satisfaction of a requirement by a complete system. -/
  meets : X → Q → Prop
  /-- The requirements each sentence translates into. -/
  translate : Sentence → Set Q

namespace Family

variable {X Y Q R V : Type*} {n p : ℕ} (F : Family X Q n p)

/-- Satisfaction of a sentence by a complete system: the single semantics through the system
map. -/
def Holds (x : X) (s : Sentence) : Prop := s.holds (F.system x)

/-- The semantics connection: a family of complete systems is sent to the sentences they all
satisfy. -/
def semantics : sInfHom (Set X)ᵒᵈ (Set Sentence) := satisfaction F.Holds

/-- The denotation of a sentence: its models, generated by the semantics connection. -/
def den (s : Sentence) : Set X := realize F.Holds {s}

@[simp, powerlib_foundation] theorem mem_den {s : Sentence} {x : X} :
    x ∈ F.den s ↔ s.holds (F.system x) := by
  simp [den, Holds]

/-- The denotation is the generated value of the semantics connection at the sentence. -/
@[tmio TM, powerlib_foundation] theorem den_eq_generate (s : Sentence) :
    F.den s = ofDual (generate F.semantics {s}) := rfl

/-- The translation chain: sentences into requirements, requirements into complete systems. -/
def chain : sInfHom (Set X)ᵒᵈ (Set Sentence) :=
  (cover (table F.translate)).comp (satisfaction F.meets)

/-- The family's TMIO seed for an observation of its complete systems. -/
def seed (obs : SetRel X V) : Seed (Set Sentence) (Set Q) (Set X)ᵒᵈ (Set V)ᵒᵈ :=
  relationalSeed (table F.translate) F.meets obs

/-- Every seed of the family carries the translation chain from complete systems to sentences. -/
@[powerlib_foundation] theorem seed_uTI (obs : SetRel X V) : (F.seed obs).uTI = F.chain := rfl

/-- The chain's generated value at a sentence is the space of its translation. -/
@[powerlib_foundation] theorem generate_chain_singleton (s : Sentence) :
    ofDual (generate F.chain {s}) = realize F.meets (F.translate s) := by
  rw [chain, TMIO.generate_chain_singleton, image_table_singleton]

/-- The translation of `s` carves out exactly its models. -/
def Exact (s : Sentence) : Prop := realize F.meets (F.translate s) = F.den s

/-- The translation of `s` carves out only models of `s`. -/
def Sound (s : Sentence) : Prop := realize F.meets (F.translate s) ⊆ F.den s

/-- Within the space of the requirement context `Δ`, the translation of `s` carves out exactly
its models. -/
def ExactUnder (Δ : Set Q) (s : Sentence) : Prop :=
  TMIO.ExactUnder F.meets Δ (F.translate s) (F.den s)

/-- Within the space of the requirement context `Δ`, the translation of `s` carves out only its
models. -/
def SoundUnder (Δ : Set Q) (s : Sentence) : Prop :=
  realize F.meets (F.translate s ∪ Δ) ⊆ F.den s

variable {F}

/-! ## Exactness and soundness compare two connections -/

/-- Exactness is the agreement of the chain and the semantics at the sentence. -/
@[powerlib_foundation] theorem exact_iff_generate {s : Sentence} :
    F.Exact s ↔ generate F.chain {s} = generate F.semantics {s} := by
  unfold Exact
  rw [← F.generate_chain_singleton, den_eq_generate]
  exact ofDual.injective.eq_iff

/-- Soundness is the chain lying below the semantics at the sentence: its generated value is a
smaller family of complete systems. -/
@[powerlib_foundation] theorem sound_iff_generate {s : Sentence} :
    F.Sound s ↔ generate F.semantics {s} ≤ generate F.chain {s} := by
  unfold Sound
  rw [← F.generate_chain_singleton, den_eq_generate]
  rfl

/-- The chain is the semantics exactly when every translation is exact. -/
@[tmio TM, powerlib_foundation] theorem chain_eq_semantics_iff : F.chain = F.semantics ↔ ∀ s, F.Exact s := by
  rw [chain, semantics, chain_eq_satisfaction_iff]
  simp only [image_table_singleton]
  rfl

/-- The chain lies below the semantics exactly when every translation is sound. -/
@[powerlib_foundation] theorem chain_le_semantics_iff :
    (∀ P, F.chain P ≤ F.semantics P) ↔ ∀ s, F.Sound s := by
  rw [chain, semantics, chain_le_satisfaction_iff]
  simp only [image_table_singleton]
  rfl

@[powerlib_foundation] theorem Exact.sound {s : Sentence} (h : F.Exact s) : F.Sound s := h.le

@[powerlib_foundation] theorem Sound.soundUnder {s : Sentence} (h : F.Sound s) (Δ : Set Q) :
    F.SoundUnder Δ s :=
  (realize_antitone F.meets Set.subset_union_left).trans h

@[powerlib_foundation] theorem ExactUnder.soundUnder {Δ : Set Q} {s : Sentence}
    (h : F.ExactUnder Δ s) : F.SoundUnder Δ s := by
  unfold SoundUnder
  rw [show realize F.meets (F.translate s ∪ Δ) = F.den s ∩ realize F.meets Δ from h]
  exact Set.inter_subset_left

@[powerlib_foundation] theorem exactUnder_empty_iff {s : Sentence} :
    F.ExactUnder ∅ s ↔ F.Exact s :=
  TMIO.exactUnder_empty_iff F.meets (F.translate s) (F.den s)

/-! ## Sentences without a translation -/

/-- A sentence translated into the whole requirement language is sound when no complete system
meets every requirement. -/
@[powerlib_foundation] theorem sound_of_translate_eq_univ (h : realize F.meets Set.univ = ∅)
    {s : Sentence} (hs : F.translate s = Set.univ) : F.Sound s := by
  unfold Sound
  rw [hs, h]
  exact Set.empty_subset _

/-- Such a translation is exact exactly when no complete system satisfies the sentence. -/
@[powerlib_foundation] theorem exact_of_translate_eq_univ (h : realize F.meets Set.univ = ∅)
    {s : Sentence} (hs : F.translate s = Set.univ) (hd : F.den s = ∅) : F.Exact s := by
  unfold Exact
  rw [hs, h, hd]

/-- A sentence translated into no requirement is exact when every complete system satisfies it. -/
@[powerlib_foundation] theorem exact_of_translate_eq_empty {s : Sentence}
    (hs : F.translate s = ∅) (hd : F.den s = Set.univ) : F.Exact s := by
  unfold Exact
  rw [hs, realize_empty, hd]

/-! ## Observations -/

variable (F)

/-- With an exact translation, the certified observations of a sentence, generated along the
whole chain, are those whose every possible source satisfies it. -/
@[powerlib_foundation] theorem certified (obs : SetRel X V) {s : Sentence} (h : F.Exact s) :
    ofDual (generate (F.seed obs).uTO {s}) = certify obs (F.den s) := by
  rw [seed, relationalSeed_whole, image_table_singleton]
  exact congrArg (certify obs) h

variable {F}

/-- An observation certified for sentences with sound translations proves them for every complete
system that may produce it. -/
@[powerlib_foundation] theorem certifies {obs : SetRel X V} {Φ : Set Sentence}
    (hs : ∀ s ∈ Φ, F.Sound s) {v : V} (hv : v ∈ ofDual (generate (F.seed obs).uTO Φ)) {x : X}
    (hx : (x, v) ∈ obs) : ∀ s ∈ Φ, x ∈ F.den s :=
  relationalSeed_sound (table F.translate) F.meets obs (den := F.den)
    (fun s hs' => by rw [image_table_singleton]; exact hs s hs') hv hx

/-- An observation outside the possible observations of a sentence's models refutes the sentence
for every complete system that may produce it. -/
@[powerlib_foundation] theorem refutes {obs : SetRel X V} {s : Sentence} {v : V}
    (hv : v ∉ predict obs (F.den s)) {x : X} (hx : (x, v) ∈ obs) : x ∉ F.den s := by
  intro hs
  rw [predict_eq_image] at hv
  exact hv ⟨x, hs, hx⟩

/-! ## Changes of representation -/

variable (F)

/-- The family read in another representation, through a map of complete systems. -/
def comap (g : Y → X) : Family Y Q n p :=
  ⟨F.system ∘ g, fun y q => F.meets (g y) q, F.translate⟩

@[powerlib_foundation] theorem den_comap (g : Y → X) (s : Sentence) :
    (F.comap g).den s = g ⁻¹' F.den s := by
  ext y
  simp [comap]

@[powerlib_foundation] theorem realize_comap (g : Y → X) (Γ : Set Q) :
    realize (F.comap g).meets Γ = g ⁻¹' realize F.meets Γ :=
  TMIO.realize_comap F.meets g Γ

/-- The family read in another representation, its requirement language extended by
requirements stated on the new representation; sentences keep their translations. -/
def extend (g : Y → X) (extra : Y → R → Prop) : Family Y (Q ⊕ R) n p where
  system := F.system ∘ g
  meets y := Sum.elim (F.meets (g y)) (extra y)
  translate s := Sum.inl '' F.translate s

@[powerlib_foundation] theorem den_extend (g : Y → X) (extra : Y → R → Prop) (s : Sentence) :
    (F.extend g extra).den s = g ⁻¹' F.den s := by
  ext y
  simp [extend]

/-- Requirements of the original language keep their spaces, pulled back. -/
@[powerlib_foundation] theorem realize_extend_inl (g : Y → X) (extra : Y → R → Prop)
    (Γ : Set Q) :
    realize (F.extend g extra).meets (Sum.inl '' Γ) = g ⁻¹' realize F.meets Γ := by
  ext y
  simp [extend]

variable {F}

/-- Exactness survives every change of representation. -/
@[powerlib_foundation] theorem Exact.comap {s : Sentence} (h : F.Exact s) (g : Y → X) :
    (F.comap g).Exact s := by
  unfold Exact at h ⊢
  rw [realize_comap, den_comap]
  exact congrArg (g ⁻¹' ·) h

/-- Soundness survives every change of representation. -/
@[powerlib_foundation] theorem Sound.comap {s : Sentence} (h : F.Sound s) (g : Y → X) :
    (F.comap g).Sound s := by
  unfold Sound at h ⊢
  rw [realize_comap, den_comap]
  exact Set.preimage_mono h

/-- Exactness survives an extension of the requirement language. -/
@[powerlib_foundation] theorem Exact.extend {s : Sentence} (h : F.Exact s) (g : Y → X)
    (extra : Y → R → Prop) : (F.extend g extra).Exact s := by
  unfold Exact at h ⊢
  change realize (F.extend g extra).meets (Sum.inl '' F.translate s) = _
  rw [realize_extend_inl, den_extend]
  exact congrArg (g ⁻¹' ·) h

/-- Soundness survives an extension of the requirement language. -/
@[powerlib_foundation] theorem Sound.extend {s : Sentence} (h : F.Sound s) (g : Y → X)
    (extra : Y → R → Prop) : (F.extend g extra).Sound s := by
  unfold Sound at h ⊢
  change realize (F.extend g extra).meets (Sum.inl '' F.translate s) ⊆ _
  rw [realize_extend_inl, den_extend]
  exact Set.preimage_mono h

/-! ## Families of autonomous fields -/

/-- A family whose complete systems are all continuous-time systems read without an envelope
satisfies every envelope sentence. -/
@[powerlib_foundation] theorem den_envelope_of_continuous {X Q : Type*} {n p : ℕ}
    {F : Family X Q n p} {sys : X → Port.System n p} (h : ∀ x, F.system x = .continuous (sys x))
    (E : Envelope.Property) : F.den (.envelope E) = Set.univ :=
  Set.eq_univ_of_forall fun x => by
    rw [mem_den, h x]
    exact Sentence.holds_envelope E _

section Autonomous

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- Every complete system of the family is the autonomous field `field x`. -/
def IsAutonomous (F : Family X Q n 0) (field : X → ℝⁿ → ℝⁿ) : Prop :=
  ∀ x, F.system x = .continuous (Port.System.autonomous (field x))

@[powerlib_foundation] theorem IsAutonomous.mem_den_flow {F : Family X Q n 0}
    {field : X → ℝⁿ → ℝⁿ} (hF : F.IsAutonomous field) {P : Flow.Property} {x : X} :
    x ∈ F.den (.flow P) ↔ P.holds (field x) 0 := by
  rw [mem_den, hF x]
  rfl

/-- A system without ports is passive. -/
@[powerlib_foundation] theorem IsAutonomous.den_passive {F : Family X Q n 0}
    {field : X → ℝⁿ → ℝⁿ} (hF : F.IsAutonomous field) : F.den .passive = Set.univ := by
  ext x
  simp only [mem_den, Set.mem_univ, iff_true, hF x, Sentence.holds_passive]
  exact Port.System.autonomous_passive _

/-- A family read without an envelope satisfies every envelope sentence. -/
@[powerlib_foundation] theorem IsAutonomous.den_envelope {F : Family X Q n 0}
    {field : X → ℝⁿ → ℝⁿ} (hF : F.IsAutonomous field) (E : Envelope.Property) :
    F.den (.envelope E) = Set.univ :=
  den_envelope_of_continuous hF E

end Autonomous

/-! ## Families of autonomous maps -/

section AutonomousMap

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- Every complete system of the family is the autonomous map `map x` with step length
`period x`. -/
def IsAutonomousMap (F : Family X Q n 0) (period : X → ℝ) (map : X → ℝⁿ → ℝⁿ) : Prop :=
  ∀ x, F.system x = .discrete (Map.System.autonomous (period x) (map x))

@[powerlib_foundation] theorem IsAutonomousMap.mem_den_flow {F : Family X Q n 0}
    {period : X → ℝ} {map : X → ℝⁿ → ℝⁿ} (hF : F.IsAutonomousMap period map)
    {P : Flow.Property} {x : X} : x ∈ F.den (.flow P) ↔ P.holdsMap (period x) (map x) 0 := by
  rw [mem_den, hF x]
  rfl

/-- A discrete system without ports is passive. -/
@[powerlib_foundation] theorem IsAutonomousMap.den_passive {F : Family X Q n 0}
    {period : X → ℝ} {map : X → ℝⁿ → ℝⁿ} (hF : F.IsAutonomousMap period map) :
    F.den .passive = Set.univ := by
  ext x
  simp only [mem_den, Set.mem_univ, iff_true, hF x, Sentence.holds_passive_discrete]
  exact ⟨fun _ => 0, fun _ => le_rfl, fun _ u => by
    simp [Map.System.supply, Map.System.autonomous, Subsingleton.elim u 0]⟩

/-- A family of maps is read without an envelope: it satisfies every envelope sentence. -/
@[powerlib_foundation] theorem IsAutonomousMap.den_envelope {F : Family X Q n 0}
    {period : X → ℝ} {map : X → ℝⁿ → ℝⁿ} (hF : F.IsAutonomousMap period map)
    (E : Envelope.Property) : F.den (.envelope E) = Set.univ := by
  ext x
  simp only [mem_den, Set.mem_univ, iff_true, hF x]
  exact Sentence.holds_envelope_discrete E _

end AutonomousMap

end Family

end powerlib
