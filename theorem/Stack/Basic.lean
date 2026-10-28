import theorem.Stack.Implementation

/-! # Four-layer stacks: theory, models, implementations and records

Scope. The four TMIO layers read as follows in this library.
* Theory (T): sentences of the semantic layer (`Sentence`), sets ordered by inclusion. Generic
  mathematics supplies the proofs.
* Model (M): the theory organized for a concrete situation. A model is an idealized mathematical
  description of one situation (topology, control law, parameters) whose behaviour is given
  exactly by the semantic layer; a requirement language describes model classes and organizes
  the theory over them. Carrier: a model family `Family X Q n p`; sets of models are ordered by
  reverse inclusion.
* Implementation (I): a model under realistic constraints: experimental platforms and test rigs,
  sampling and computation delay, sensor and actuator dynamics, quantization, limits the design did
  not intend, parameter tolerances, numerical integration. An implementation has its own
  behaviour, again read by the single semantics, which in general differs from the behaviour of
  the model it realizes. Carrier: a second family `Family Y R m q`, whose requirement language
  states the realistic constraints.
* Observation (O): records produced by implementations: sampled waveforms, frequency sweeps,
  identification results, with their measurement errors. A record has no behaviour; it is related
  to the implementations that may produce it.

Distinguishing criterion: changing the mathematics changes T; keeping the theory and changing the
modelling changes M; keeping the model and changing the conditions of its realization (platform,
digitization, simulation method) changes I; keeping the implementation and changing the run or the
sensor changes O. A constraint that is part of the design intent (a designed current limit, an
averaged model, nominal parameters) belongs to the model; one imposed by hardware or by the test
(a hardware limit, switching, an EMT discretization, a tolerance set) belongs to the
implementation.

A `Stack` extends an `Implementation` (`theorem/Stack/Implementation.lean`: a model family, an
implementation family and the realization `realizes` of models by implementations) by the
production relation `produces` (implementation `y` may produce record `v`). Its TMIO seed has the
semantic maps
* `u₁ = model.semantics : (Set X)ᵒᵈ → Set Sentence` (the sentences all given models satisfy),
* `u₂ = possibly realizes : (Set Y)ᵒᵈ → (Set X)ᵒᵈ` (the models some given implementation
  realizes),
* `u₃ = possibly produces : (Set V)ᵒᵈ → (Set Y)ᵒᵈ` (the implementations that may produce some
  given record).
The generated forward maps are the denotation, certification against the realized models, and
certification of records. Theory-driven work runs forward along the whole chain (`certified`);
data-driven work is the whole backward traversal (`infer`, the seed's `uTO`). The whole-chain
Galois connection reads: records support sentences exactly when they are certified for them
(`subset_certified_iff`).

The seed encoding `Family.seed` places the model instances in the third position and the
requirement sets in the second. In the reading above both belong to the model layer: a `Family`
with its translation supplies a T–M connection: translation/denotation comparisons belong to
T–M, while facts only about static requirement spaces belong to M. The `organized` seed of a stack
keeps that organization: its first edge is the translation chain `model.chain` instead of the
semantics.

Implementations carry their own truth, `impl.semantics`. Its comparison with the composite through
the realized models (`seed.uTI`, the implementation layer's `uTI`) is realization soundness,
completeness and exactness, defined on `Implementation`. Data-driven conclusions of the whole
backward traversal are conclusions about the realized models; they become conclusions about the
producing implementation through realization soundness (`infer_true`), and refutation runs the
same edge backwards (`refutes_realized`).

Source: TMIO v0.3 (`theorem/TMIO/Derived.lean`, `theorem/TMIO/Relation.lean`); the model family
interface (`theorem/Family/Basic.lean`). Scaffold: `theorem/Records.agda` (the generic pattern;
each implementation with records has its own scaffold, listed in the scaffold table of
`Architecture.md`).

Results.
* The stack seed and its organized variant (`seed`, `organized`), data-driven inference
  (`infer`, `mem_infer`) and theory-driven certification (`certified`, `certified_eq`,
  `mem_certified`), the whole-chain Galois connection (`subset_certified_iff`), its monotonicity
  in both directions (`infer_antitone`, `certified_antitone`).
* Truth at the implementation layer (`truth`, `mem_truth`); the seed's composite through the
  realized models is the implementation layer's (`seed_uTI`); transfer of data-driven conclusions
  to the producing implementations under realization soundness (`infer_true`,
  `infer_subset_truth`), and back under realization completeness (`mem_infer_of_truth`).
* Prediction at the implementation layer (`predicted`, `mem_predicted`); refutation of the
  implementation by a record outside the predicted records (`refutes`) and of its realized models
  (`refutes_realized`).
* The organized seed below the semantic seed when translations are sound
  (`mem_infer_of_organized`, `certifiedOrganized_subset`), equal when they are exact
  (`organized_eq_seed_of_exact`). -/

noncomputable section

namespace powerlib

open TMIO OrderDual

/-- A four-layer stack: an implementation layer over a model layer
(`theorem/Stack/Implementation.lean`) and the production of records by implementations. -/
structure Stack (X Q Y R V : Type*) (n p m q : ℕ) extends Implementation X Q Y R n p m q where
  /-- `(y, v) ∈ produces`: the implementation `y` may produce the record `v`. -/
  produces : SetRel Y V

namespace Stack

variable {X Q Y R V : Type*} {n p m q : ℕ} (S : Stack X Q Y R V n p m q)

/-! ## The seeds -/

/-- The TMIO seed of the stack: the semantics of the models, realization and production. -/
def seed : Seed (Set Sentence) (Set X)ᵒᵈ (Set Y)ᵒᵈ (Set V)ᵒᵈ :=
  ⟨S.model.semantics, possibly S.realizes, possibly S.produces⟩

/-- The organized seed: the models read through the translation into their requirement
language. -/
def organized : Seed (Set Sentence) (Set X)ᵒᵈ (Set Y)ᵒᵈ (Set V)ᵒᵈ :=
  ⟨S.model.chain, possibly S.realizes, possibly S.produces⟩

/-- Data-driven inference, the whole backward traversal: the sentences satisfied by every model
realized by a possible producer of some record of `D`. -/
def infer (D : Set V) : Set Sentence := S.seed.uTO (toDual D)

/-- Theory-driven certification, the generated whole forward map: the records all of whose
possible producers realize only models of `Φ`. -/
def certified (Φ : Set Sentence) : Set V := ofDual (generate S.seed.uTO Φ)

/-- Data-driven inference through the requirement language of the models. -/
def inferOrganized (D : Set V) : Set Sentence := S.organized.uTO (toDual D)

/-- Theory-driven certification through the requirement language of the models: the records all
of whose possible producers realize only models meeting the translation of `Φ`. -/
def certifiedOrganized (Φ : Set Sentence) : Set V := ofDual (generate S.organized.uTO Φ)

/-- The truth at the implementation layer: the sentences satisfied by every possible producer of
some record of `D`. -/
def truth (D : Set V) : Set Sentence := S.impl.semantics (possibly S.produces (toDual D))

@[powerlib_foundation] theorem infer_eq (D : Set V) :
    S.infer D = S.model.semantics (possibly S.realizes (possibly S.produces (toDual D))) := rfl

@[simp, powerlib_foundation] theorem mem_infer {D : Set V} {s : Sentence} :
    s ∈ S.infer D ↔
      ∀ v ∈ D, ∀ y, (y, v) ∈ S.produces → ∀ x, (x, y) ∈ S.realizes → x ∈ S.model.den s := by
  rw [infer_eq, Family.semantics, mem_satisfaction]
  simp only [mem_possibly, ofDual_toDual, Family.mem_den, Family.Holds]
  constructor
  · intro h v hv y hy x hx
    exact h x ⟨y, ⟨v, hv, hy⟩, hx⟩
  · rintro h x ⟨y, ⟨v, hv, hy⟩, hx⟩
    exact h v hv y hy x hx

@[simp, powerlib_foundation] theorem mem_truth {D : Set V} {s : Sentence} :
    s ∈ S.truth D ↔ ∀ v ∈ D, ∀ y, (y, v) ∈ S.produces → y ∈ S.impl.den s := by
  rw [truth, Family.semantics, mem_satisfaction]
  simp only [mem_possibly, ofDual_toDual, Family.mem_den, Family.Holds]
  constructor
  · intro h v hv y hy
    exact h y ⟨v, hv, hy⟩
  · rintro h y ⟨v, hv, hy⟩
    exact h v hv y hy

/-- The generated whole forward map: denote, certify against the realized models, certify the
records. -/
@[powerlib_foundation] theorem certified_eq (Φ : Set Sentence) :
    S.certified Φ = certify S.produces (certify S.realizes (realize S.model.Holds Φ)) := by
  unfold certified
  rw [Seed.generate_uTO]
  simp only [Function.comp_apply, Seed.l₁, Seed.l₂, Seed.l₃, seed]
  rw [congrFun (generate_possibly S.produces), congrFun (generate_possibly S.realizes)]
  rfl

@[simp, powerlib_foundation] theorem mem_certified {Φ : Set Sentence} {v : V} :
    v ∈ S.certified Φ ↔
      ∀ y, (y, v) ∈ S.produces → ∀ x, (x, y) ∈ S.realizes → ∀ s ∈ Φ, x ∈ S.model.den s := by
  rw [certified_eq]
  simp only [mem_certify, mem_realize, Family.mem_den, Family.Holds]

/-- The generated whole forward map of the organized seed: translate, realize the translation,
certify against the realized models, certify the records. -/
@[powerlib_foundation] theorem certifiedOrganized_eq (Φ : Set Sentence) :
    S.certifiedOrganized Φ = certify S.produces
      (certify S.realizes (realize S.model.meets ((table S.model.translate).image Φ))) := by
  unfold certifiedOrganized
  rw [Seed.generate_uTO]
  simp only [Function.comp_apply, Seed.l₁, Seed.l₂, Seed.l₃, organized, Family.chain]
  rw [congrFun (generate_possibly S.produces), congrFun (generate_possibly S.realizes),
    congrFun (generate_comp _ _)]
  have h : (generate (cover (table S.model.translate))).toFun Φ =
      (table S.model.translate).image Φ :=
    generate_cover_apply _ Φ
  simp only [Function.comp_apply, h]
  rfl

/-- The whole-chain Galois connection of the stack (`Seed.gc_whole`): a set of records supports
a set of sentences exactly when every record is certified for them. -/
@[tmio IO, powerlib_foundation] theorem subset_certified_iff (D : Set V) (Φ : Set Sentence) :
    D ⊆ S.certified Φ ↔ Φ ⊆ S.infer D := by
  have h := S.seed.gc_whole Φ (toDual D)
  rw [← S.seed.generate_uTO] at h
  exact h

/-- More records support fewer sentences. -/
@[powerlib_foundation] theorem infer_antitone {D E : Set V} (h : D ⊆ E) : S.infer E ⊆ S.infer D :=
  fun _ hs => S.mem_infer.mpr fun v hv => S.mem_infer.mp hs v (h hv)

/-- More sentences certify fewer records. -/
@[powerlib_foundation] theorem certified_antitone {Φ Ψ : Set Sentence} (h : Φ ⊆ Ψ) :
    S.certified Ψ ⊆ S.certified Φ :=
  (gc_generate S.seed.uTO).monotone_l h

/-- The seed's composite from implementations to sentences is the implementation layer's. -/
@[powerlib_foundation] theorem seed_uTI : S.seed.uTI = S.uTI := rfl

/-! ## Prediction and realization along the stack -/

/-- The records predicted by `s` at the implementation layer: those some implementation
satisfying `s` may produce. -/
def predicted (s : Sentence) : Set V := predict S.produces (S.impl.den s)

@[powerlib_foundation] theorem mem_predicted {s : Sentence} {v : V} :
    v ∈ S.predicted s ↔ ∃ y, y ∈ S.impl.den s ∧ (y, v) ∈ S.produces := by
  rw [predicted, predict_eq_image]
  rfl

/-- Data-driven conclusions become conclusions about the producing implementation: under
realization soundness, an implementation within the constraints that may produce a record of
`D` satisfies every sentence inferred from `D`. -/
@[tmio IO, powerlib_foundation] theorem infer_true {Δ : Set R} {s : Sentence}
    (hS : S.RealizationSoundUnder Δ s) {D : Set V} (hs : s ∈ S.infer D) {v : V} (hv : v ∈ D)
    {y : Y} (hy : (y, v) ∈ S.produces) (hΔ : y ∈ realize S.impl.meets Δ) : y ∈ S.impl.den s :=
  hS ⟨(mem_certify _ _ _).mpr fun x hx => S.mem_infer.mp hs v hv y hy x hx, hΔ⟩

/-- When the records are certified for the constraints (every possible producer lies within
`Δ`; the generated observation map at the constraint space), the inferred sentences with sound
realization are true sentences of the implementations. -/
@[powerlib_foundation] theorem infer_subset_truth {Δ : Set R} {D : Set V}
    (hΔ : D ⊆ certify S.produces (realize S.impl.meets Δ))
    {s : Sentence} (hS : S.RealizationSoundUnder Δ s) (hs : s ∈ S.infer D) : s ∈ S.truth D :=
  S.mem_truth.mpr fun _ hv y hy =>
    S.infer_true hS hs hv hy ((mem_certify _ _ _).mp (hΔ hv) y hy)

/-- Conversely, under realization completeness, a sentence true of every possible producer of
records certified for the constraints is inferred from them. -/
@[powerlib_foundation] theorem mem_infer_of_truth {Δ : Set R} {D : Set V}
    (hΔ : D ⊆ certify S.produces (realize S.impl.meets Δ))
    {s : Sentence} (hS : S.RealizationCompleteUnder Δ s) (hs : s ∈ S.truth D) : s ∈ S.infer D :=
  S.mem_infer.mpr fun v hv y hy x hx =>
    (mem_certify _ _ _).mp (hS ⟨S.mem_truth.mp hs v hv y hy,
      (mem_certify _ _ _).mp (hΔ hv) y hy⟩) x hx

/-- A record outside the records predicted by `s` refutes `s` for every implementation that may
produce it. -/
@[powerlib_foundation] theorem refutes {s : Sentence} {y : Y} {v : V} (hy : (y, v) ∈ S.produces)
    (hv : v ∉ S.predicted s) : y ∉ S.impl.den s :=
  fun hs => hv (S.mem_predicted.mpr ⟨y, hs, hy⟩)

/-- Refutation runs back through the realization edge: under realization soundness, a record
refuting `s` for an implementation within the constraints exhibits a realized model violating
`s`. -/
@[powerlib_foundation] theorem refutes_realized {Δ : Set R} {s : Sentence}
    (hS : S.RealizationSoundUnder Δ s) {y : Y} {v : V} (hy : (y, v) ∈ S.produces)
    (hΔ : y ∈ realize S.impl.meets Δ) (hv : v ∉ S.predicted s) :
    ∃ x, (x, y) ∈ S.realizes ∧ x ∉ S.model.den s := by
  by_contra hno
  push Not at hno
  exact S.refutes hy hv (hS ⟨(mem_certify _ _ _).mpr hno, hΔ⟩)

/-! ## The organized seed against the semantic seed -/

@[powerlib_foundation] theorem mem_inferOrganized {D : Set V} {s : Sentence} :
    s ∈ S.inferOrganized D ↔ ∀ v ∈ D, ∀ y, (y, v) ∈ S.produces → ∀ x, (x, y) ∈ S.realizes →
      x ∈ realize S.model.meets (S.model.translate s) := by
  change s ∈ (cover (table S.model.translate)).comp (satisfaction S.model.meets)
    (possibly S.realizes (possibly S.produces (toDual D))) ↔ _
  rw [mem_chain_iff_subset, image_table_singleton]
  constructor
  · intro h v hv y hy x hx
    exact h ((mem_possibly _ _ _).mpr ⟨y, (mem_possibly _ _ _).mpr ⟨v, hv, hy⟩, hx⟩)
  · intro h x hx
    obtain ⟨y, hy', hx⟩ := (mem_possibly _ _ _).mp hx
    obtain ⟨v, hv, hy⟩ := (mem_possibly _ _ _).mp hy'
    exact h v hv y hy x hx

/-- A sentence inferred through a sound translation is inferred. -/
@[powerlib_foundation] theorem mem_infer_of_organized {s : Sentence} (h : S.model.Sound s)
    {D : Set V} (hs : s ∈ S.inferOrganized D) : s ∈ S.infer D :=
  S.mem_infer.mpr fun v hv y hy x hx => h (S.mem_inferOrganized.mp hs v hv y hy x hx)

/-- Records certified through sound translations are certified. -/
@[powerlib_foundation] theorem certifiedOrganized_subset {Φ : Set Sentence}
    (h : ∀ s ∈ Φ, S.model.Sound s) : S.certifiedOrganized Φ ⊆ S.certified Φ := by
  intro v hv
  rw [certifiedOrganized_eq, mem_certify] at hv
  rw [mem_certified]
  intro y hy x hx s hs
  have hy' := (mem_certify _ _ _).mp (hv y hy) x hx
  refine h s hs ((realize_antitone _ ?_) hy')
  rw [image_table]
  exact Set.subset_biUnion_of_mem (u := S.model.translate) hs

/-- With exact translations the organized seed is the semantic seed. -/
@[powerlib_foundation] theorem organized_eq_seed_of_exact (h : ∀ s, S.model.Exact s) :
    S.organized = S.seed := by
  unfold organized seed
  rw [Family.chain_eq_semantics_iff.mpr h]

end Stack

end powerlib
