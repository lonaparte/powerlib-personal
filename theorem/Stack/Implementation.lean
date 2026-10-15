import theorem.Family.Basic

/-! # Implementations of models: the T–M–I part of the four layers

Scope. An `Implementation` relates a model family (M, the theory organized for a situation) to an
implementation family (I, models under realistic constraints: platforms and test rigs, sampling
and computation delay, sensor and actuator dynamics, limits the design did not intend, parameter
tolerances, numerical integration) by a realization relation: `(x, y) ∈ realizes` when the
implementation `y` realizes the model `x`. The layers and the criterion that places a result in
one of them are those of `theorem/Stack/Basic.lean` and `Layers.md`; records (O) are added by a
`Stack`, which extends an `Implementation`.

Both families are read by the single semantics. The composite connection from implementations
back to sentences through the realized models, `uTI = model.semantics ∘ possibly realizes`, is
compared with the implementations' own semantics `impl.semantics`, as the translation chain of a
family is compared with its semantics one layer up:
* realization soundness: within the realistic constraints `Δ`, an implementation all of whose
  realized models satisfy `s` satisfies `s` itself;
* realization completeness: within `Δ`, an implementation satisfying `s` realizes only models of
  `s`;
* realization exactness: both.
Realization soundness reduces to static obligations on requirements
(`realizationSoundUnder_of_requirements`). An implementation realizing its design model through a
map `design : Y → X` uses `ofDesign`.

Source: TMIO v0.3 (`theorem/TMIO/Derived.lean`, `theorem/TMIO/Relation.lean`); the model family
interface (`theorem/Family/Basic.lean`).

Results.
* The composite connection `uTI` and its generated value at a sentence
  (`generate_uTI_singleton`).
* Realization soundness, completeness and exactness (`RealizationSoundUnder`,
  `RealizationCompleteUnder`, `RealizationExactUnder`, `realizationExactUnder_iff`), their
  monotonicity in the constraints (`RealizationSoundUnder.mono`, `RealizationCompleteUnder.mono`),
  and their reading as comparisons of generated connections
  (`realizationSoundUnder_empty_iff_generate`, `realizationCompleteUnder_empty_iff_generate`).
* The reduction of realization soundness to an exact model translation, a sound implementation
  translation and an implication between the requirement languages
  (`realizationSoundUnder_of_requirements`).
* Realization by a design map (`ofDesign`, `mem_ofDesign`, `certify_ofDesign`,
  `certify_realizes_of_design`), and exactness of a realization whose implementation family
  satisfies the model family's sentences pulled back along the design map
  (`realizationExactUnder_of_den_eq_preimage`). -/

noncomputable section

namespace powerlib

open TMIO OrderDual

/-- An implementation layer over a model layer: the model family, the implementation family, and
the realization of models by implementations. -/
structure Implementation (X Q Y R : Type*) (n p m q : ℕ) where
  /-- The model layer: models of a situation and their requirement language. -/
  model : Family X Q n p
  /-- The implementation layer: implementations with their own behaviour and the requirement
  language of their realistic constraints. -/
  impl : Family Y R m q
  /-- `(x, y) ∈ realizes`: the implementation `y` realizes the model `x`. -/
  realizes : SetRel X Y

namespace Implementation

variable {X Q Y R : Type*} {n p m q : ℕ} (I : Implementation X Q Y R n p m q)

/-- The composite connection from implementations back to sentences through the realized models:
a family of implementations is sent to the sentences that every model they realize satisfies. -/
def uTI : sInfHom (Set Y)ᵒᵈ (Set Sentence) := I.model.semantics.comp (possibly I.realizes)

/-- The composite through the realized models, generated at one sentence: the implementations
all of whose realized models satisfy it. -/
@[powerlib_foundation] theorem generate_uTI_singleton (s : Sentence) :
    ofDual (generate I.uTI {s}) = certify I.realizes (I.model.den s) := by
  rw [uTI, generate_comp, Function.comp_apply, congrFun (generate_possibly I.realizes)]
  rfl

/-! ## Realization soundness, completeness and exactness -/

/-- Within the realistic constraints `Δ`, every implementation all of whose realized models
satisfy `s` satisfies `s` itself. -/
def RealizationSoundUnder (Δ : Set R) (s : Sentence) : Prop :=
  certify I.realizes (I.model.den s) ∩ realize I.impl.meets Δ ⊆ I.impl.den s

/-- Within the realistic constraints `Δ`, every implementation satisfying `s` realizes only
models of `s`. -/
def RealizationCompleteUnder (Δ : Set R) (s : Sentence) : Prop :=
  I.impl.den s ∩ realize I.impl.meets Δ ⊆ certify I.realizes (I.model.den s)

/-- Within the realistic constraints `Δ`, an implementation satisfies `s` exactly when all of its
realized models do. -/
def RealizationExactUnder (Δ : Set R) (s : Sentence) : Prop :=
  certify I.realizes (I.model.den s) ∩ realize I.impl.meets Δ =
    I.impl.den s ∩ realize I.impl.meets Δ

/-- Realization soundness without constraints is the implementation semantics lying below the
composite through the realized models at the sentence: its generated value is a larger family
of implementations. -/
@[powerlib_foundation] theorem realizationSoundUnder_empty_iff_generate {s : Sentence} :
    I.RealizationSoundUnder ∅ s ↔ generate I.impl.semantics {s} ≤ generate I.uTI {s} := by
  unfold RealizationSoundUnder
  rw [realize_empty, Set.inter_univ, ← generate_uTI_singleton]
  rfl

/-- Realization completeness without constraints is the reverse order of the two generated
values. -/
@[powerlib_foundation] theorem realizationCompleteUnder_empty_iff_generate {s : Sentence} :
    I.RealizationCompleteUnder ∅ s ↔ generate I.uTI {s} ≤ generate I.impl.semantics {s} := by
  unfold RealizationCompleteUnder
  rw [realize_empty, Set.inter_univ, ← generate_uTI_singleton]
  rfl

/-- Exactness is soundness and completeness. -/
@[powerlib_foundation] theorem realizationExactUnder_iff {Δ : Set R} {s : Sentence} :
    I.RealizationExactUnder Δ s ↔
      I.RealizationSoundUnder Δ s ∧ I.RealizationCompleteUnder Δ s := by
  constructor
  · intro h
    refine ⟨fun y hy => (h ▸ hy).1, fun y hy => (h.symm ▸ hy).1⟩
  · rintro ⟨hs, hc⟩
    exact Set.Subset.antisymm (fun y hy => ⟨hs hy, hy.2⟩) (fun y hy => ⟨hc hy, hy.2⟩)

variable {I} in
@[powerlib_foundation] theorem RealizationExactUnder.soundUnder {Δ : Set R} {s : Sentence}
    (h : I.RealizationExactUnder Δ s) : I.RealizationSoundUnder Δ s :=
  (I.realizationExactUnder_iff.mp h).1

variable {I} in
@[powerlib_foundation] theorem RealizationExactUnder.completeUnder {Δ : Set R} {s : Sentence}
    (h : I.RealizationExactUnder Δ s) : I.RealizationCompleteUnder Δ s :=
  (I.realizationExactUnder_iff.mp h).2

variable {I} in
/-- Soundness survives more constraints. -/
@[powerlib_foundation] theorem RealizationSoundUnder.mono {Δ Δ' : Set R} {s : Sentence}
    (h : I.RealizationSoundUnder Δ s) (hΔ : Δ ⊆ Δ') : I.RealizationSoundUnder Δ' s :=
  fun _ hy => h ⟨hy.1, realize_antitone _ hΔ hy.2⟩

variable {I} in
/-- Completeness survives more constraints. -/
@[powerlib_foundation] theorem RealizationCompleteUnder.mono {Δ Δ' : Set R} {s : Sentence}
    (h : I.RealizationCompleteUnder Δ s) (hΔ : Δ ⊆ Δ') : I.RealizationCompleteUnder Δ' s :=
  fun _ hy => h ⟨hy.1, realize_antitone _ hΔ hy.2⟩

/-- Realization soundness reduces to static obligations on requirements. If the model translation
of `s` is exact within the model context `ΔM`, the implementation translation of `s` is sound,
the constraints `Δ` place every realized model in `ΔM`, and an implementation within `Δ` whose
realized models meet the translation of `s` and `ΔM` meets its own translation of `s`, then `s`
is realized soundly within `Δ`. -/
@[powerlib_foundation] theorem realizationSoundUnder_of_requirements {ΔM : Set Q} {Δ : Set R}
    {s : Sentence} (hM : I.model.ExactUnder ΔM s) (hI : I.impl.Sound s)
    (hctx : realize I.impl.meets Δ ⊆ certify I.realizes (realize I.model.meets ΔM))
    (hreq : certify I.realizes (realize I.model.meets (I.model.translate s ∪ ΔM)) ∩
      realize I.impl.meets Δ ⊆ realize I.impl.meets (I.impl.translate s)) :
    I.RealizationSoundUnder Δ s := by
  rintro y ⟨hd, hΔ⟩
  refine hI (hreq ⟨(mem_certify _ _ _).mpr fun x hx => ?_, hΔ⟩)
  have hM' : realize I.model.meets (I.model.translate s ∪ ΔM) =
      I.model.den s ∩ realize I.model.meets ΔM := hM
  rw [hM']
  exact ⟨(mem_certify _ _ _).mp hd x hx, (mem_certify _ _ _).mp (hctx hΔ) x hx⟩

end Implementation

/-! ## Realization by a design map -/

namespace Implementation

variable {X Q Y R : Type*} {n p m q : ℕ}

/-- The realization relation of a design map: each implementation realizes its design model. -/
def ofDesign (design : Y → X) : SetRel X Y := {p | design p.2 = p.1}

@[simp, powerlib_foundation] theorem mem_ofDesign {design : Y → X} {x : X} {y : Y} :
    (x, y) ∈ ofDesign design ↔ design y = x := Iff.rfl

/-- Certification against a design map is its preimage. -/
@[powerlib_foundation] theorem certify_ofDesign (design : Y → X) (P : Set X) :
    certify (ofDesign design) P = design ⁻¹' P := by
  ext y
  simp only [mem_certify, mem_ofDesign, Set.mem_preimage]
  exact ⟨fun h => h _ rfl, fun h x hx => hx ▸ h⟩

/-- Certification against the realization of an implementation built from a design map
(typically `h := rfl`). -/
@[powerlib_foundation] theorem certify_realizes_of_design {I : Implementation X Q Y R n p m q}
    {design : Y → X} (h : I.realizes = ofDesign design) (P : Set X) :
    certify I.realizes P = design ⁻¹' P := by
  rw [h, certify_ofDesign]

/-- A realization by a design map is exact at `s`, without constraints, when the implementation
family's denotation of `s` is the model family's pulled back along the design map. -/
@[powerlib_foundation] theorem realizationExactUnder_of_den_eq_preimage
    {I : Implementation X Q Y R n p m q} {design : Y → X} (h : I.realizes = ofDesign design)
    {s : Sentence} (hden : I.impl.den s = design ⁻¹' I.model.den s) :
    I.RealizationExactUnder ∅ s := by
  unfold RealizationExactUnder
  rw [certify_realizes_of_design h, hden]

end Implementation

end powerlib
