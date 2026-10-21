{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.FamilyReading where

-- Scaffold of family readings, the generic pattern: a spoke family read through a hub family.
-- Each reading of the library has its own scaffold, named after its two families and listed in
-- the scaffold table of `Architecture.md` (hub content `Swing`, semantic layer `FlowSemantics`).
--
-- A hub is a family whose laws are proved once (the swing equation, the PI-PLL); a spoke is a
-- family whose models are read as hub models: a map of models and, for every model, a reading
-- under which its system and the system of its image satisfy the same sentences (an affine change
-- of state coordinates, or an equality of systems). Univalence turns the readings into a path from
-- the spoke's satisfaction structure to the hub's pulled back along the map (`readPath`), so every
-- construction over satisfaction structures — denotations, legal spaces, generated connections —
-- is the hub's pulled back (`comap`, Lean's `Family.comap`). A reading comes from a conjugacy
-- under which satisfaction is invariant (`viaConjugacy`, `partialConjugacy` for the sentences of
-- a predicate) or from an equality of systems (`viaEquality`). What a spoke still has to supply is
-- the correspondence of its requirement language with the hub's on a context — a set of its
-- requirements (`restrict`) or a predicate on its parameters (`restrictBy`); then exactness and
-- soundness pass from the hub to the spoke (`exactUnder-pullback`, `exact-pullback`,
-- `sound-pullback`). Readings compose (`compose`), so a spoke of a spoke reads through the hub.
--
-- The Lean connection is `theorem/Spectral/Hub.lean`: the transfer laws are connection statements
-- over arbitrary families (`exactUnder_of_hub`, `exact_of_hub`, `sound_of_hub`,
-- `realize_subset_den_of_hub`, `mem_den_iff_of_flow`); readings by conjugacy go through the
-- foundation lemma `mem_den_flow_iff_of_transport`. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma

open import theorem.TMIO.Representation

-- Logical equivalence.
_↔_ : Type → Type → Type
A ↔ B = (A → B) × (B → A)

↔-trans : {A B C : Type} → A ↔ B → B ↔ C → A ↔ C
↔-trans (f , g) (h , k) = (λ a → h (f a)) , (λ c → g (k c))

↔-of-≃ : {A B : Type} → A ≃ B → A ↔ B
↔-of-≃ e = equivFun e , invEq e

-- The semantic layer, abstractly: systems and the satisfaction of sentences.
record Semantics : Type₁ where
  field
    System Sentence : Type
    holds : System → Sentence → Type

module Readings (S : Semantics) where
  open Semantics S

  -- A family: models, their systems, a requirement language and its translation.
  record Family : Type₁ where
    field
      Model Req : Type
      system : Model → System
      meets : Model → Req → Type
      translate : Sentence → Req → Type

  open Family

  den : (F : Family) → Sentence → Model F → Type
  den F s x = holds (system F x) s

  realize : (F : Family) → (Req F → Type) → Model F → Type
  realize F Γ x = (q : Req F) → Γ q → meets F x q

  -- Exactness within a context, model by model, and soundness.
  ExactUnder : (F : Family) → (Req F → Type) → Sentence → Type
  ExactUnder F Δ s = (x : Model F) → realize F Δ x → realize F (translate F s) x ↔ den F s x

  Sound : (F : Family) → Sentence → Type
  Sound F s = (x : Model F) → realize F (translate F s) x → den F s x

  Exact : (F : Family) → Sentence → Type
  Exact F s = (x : Model F) → realize F (translate F s) x ↔ den F s x

  -- The subfamily of the models in a context; exactness within the context is its exactness.
  restrict : (F : Family) → (Req F → Type) → Family
  restrict F Δ = record
    { Model = Σ (Model F) (realize F Δ) ; Req = Req F
    ; system = λ x → system F (fst x) ; meets = λ x → meets F (fst x) ; translate = translate F }

  exactUnder-restrict : (F : Family) (Δ : Req F → Type) (s : Sentence) →
    Exact (restrict F Δ) s → ExactUnder F Δ s
  exactUnder-restrict F Δ s h x hx = h (x , hx)

  sound-restrict : (F : Family) (Δ : Req F → Type) (s : Sentence) →
    ((x : Model F) → realize F (translate F s) x → realize F Δ x) →
    Sound (restrict F Δ) s → Sound F s
  sound-restrict F Δ s hΔ h x hx = h (x , hΔ x hx) hx

  -- The semantics of a family as a satisfaction structure.
  semantics : Family → SatContext Sentence
  semantics F = satContext (Model F) (λ x s → holds (system F x) s)

  -- A family read through a map of models, keeping its requirement language (`Family.comap`).
  comap : (G : Family) {Y : Type} → (Y → Model G) → Family
  comap G {Y} g = record
    { Model = Y ; Req = Req G
    ; system = λ y → system G (g y) ; meets = λ y → meets G (g y) ; translate = translate G }

  -- Two systems that satisfy the same sentences.
  Reading : System → System → Type
  Reading a b = (s : Sentence) → holds a s ≃ holds b s

  -- Readings from a class of conjugacies under which satisfaction is invariant (affine changes of
  -- state coordinates, `Dynamics.holds_transport_iff`): a system that is a conjugate of another
  -- reads as it.
  record Invariance : Type₁ where
    field
      Conj : Type
      act : Conj → System → System
      invariant : (c : Conj) (a : System) (s : Sentence) → holds (act c a) s ≃ holds a s

  conjugateReading : (I : Invariance) {a b : System} (c : Invariance.Conj I) →
    a ≡ Invariance.act I c b → Reading a b
  conjugateReading I {a} {b} c p s =
    compEquiv (pathToEquiv (cong (λ z → holds z s) p)) (Invariance.invariant I c b s)

  -- A reading of the sentences satisfying `P` only (e.g. the flow sentences, when the spoke has a
  -- port and the hub has none).
  record PartialHub (P : Sentence → Type) (F G : Family) : Type where
    field
      map : Model F → Model G
      read : (x : Model F) (s : Sentence) → P s → holds (system F x) s ≃ holds (system G (map x)) s

  module _ {P : Sentence → Type} {F G : Family} (h : PartialHub P F G) where
    open PartialHub h

    exact-pullback : {ΔG : Req G → Type} {s : Sentence} → P s →
      ((x : Model F) → realize G ΔG (map x)) →
      ((x : Model F) → realize F (translate F s) x ↔ realize G (translate G s) (map x)) →
      ExactUnder G ΔG s → Exact F s
    exact-pullback {s = s} ps hΔ corr hG x =
      ↔-trans (corr x) (↔-trans (hG (map x) (hΔ x)) (↔-of-≃ (invEquiv (read x s ps))))

    sound-pullback-partial : {s : Sentence} → P s →
      ((x : Model F) → realize F (translate F s) x → realize G (translate G s) (map x)) →
      Sound G s → Sound F s
    sound-pullback-partial {s = s} ps corr hG x hx = invEq (read x s ps) (hG (map x) (corr x hx))

  -- A spoke `F` read through a hub `G`.
  record Hub (F G : Family) : Type where
    field
      map : Model F → Model G
      read : (x : Model F) → Reading (system F x) (system G (map x))

  module _ {F G : Family} (h : Hub F G) where
    open Hub h

    -- The hub's satisfaction structure pulled back along the map.
    pulledBack : SatContext Sentence
    pulledBack = semantics (comap G map)

    -- Univalence: the spoke's semantics is the pulled-back hub semantics.
    readEquiv : SatEquiv (semantics F) pulledBack
    readEquiv = satEquiv (idEquiv _) (λ x s → ua (read x s))

    readPath : semantics F ≡ pulledBack
    readPath = satPath readEquiv

    -- In particular every legal space of sentence families is the pulled-back one.
    realizeSentences : (Γ : Sentence → Type) →
      Realize (semantics F) Γ ≃ Realize pulledBack Γ
    realizeSentences Γ = realizeEquiv Γ readEquiv

    -- Exactness passes from the hub to the spoke on a context where the requirement languages
    -- correspond and the spoke's context lands in the hub's.
    exactUnder-pullback : {ΔF : Req F → Type} {ΔG : Req G → Type} {s : Sentence} →
      ((x : Model F) → realize F ΔF x → realize G ΔG (map x)) →
      ((x : Model F) → realize F ΔF x →
        realize F (translate F s) x ↔ realize G (translate G s) (map x)) →
      ExactUnder G ΔG s → ExactUnder F ΔF s
    exactUnder-pullback {s = s} hΔ corr hG x hx =
      ↔-trans (corr x hx) (↔-trans (hG (map x) (hΔ x hx)) (↔-of-≃ (invEquiv (read x s))))

    -- Soundness passes when the spoke's translated requirements give the hub's.
    sound-pullback : {s : Sentence} →
      ((x : Model F) → realize F (translate F s) x → realize G (translate G s) (map x)) →
      Sound G s → Sound F s
    sound-pullback {s = s} corr hG x hx = invEq (read x s) (hG (map x) (corr x hx))

  -- A spoke whose systems are conjugates of its images' reads through the hub.
  viaConjugacy : {F G : Family} (I : Invariance) (map : Model F → Model G)
    (conj : Model F → Invariance.Conj I) →
    ((x : Model F) → system F x ≡ Invariance.act I (conj x) (system G (map x))) → Hub F G
  viaConjugacy I map conj p = record
    { map = map ; read = λ x → conjugateReading I (conj x) (p x) }

  -- A spoke whose systems are its images' systems reads through the hub (the same plant written
  -- with other parameters).
  viaEquality : {F G : Family} (map : Model F → Model G) →
    ((x : Model F) → system F x ≡ system G (map x)) → Hub F G
  viaEquality map p = record
    { map = map ; read = λ x s → pathToEquiv (cong (λ a → holds a s) (p x)) }

  -- The subfamily of the models satisfying a predicate that is not a requirement of the family
  -- (a context on the parameters, such as positive inertia or a nonzero inductance).
  restrictBy : (F : Family) → (Model F → Type) → Family
  restrictBy F C = record
    { Model = Σ (Model F) C ; Req = Req F
    ; system = λ x → system F (fst x) ; meets = λ x → meets F (fst x) ; translate = translate F }

  -- A member characterization of the spoke from exactness of the subfamily.
  den-of-restrictBy : (F : Family) (C : Model F → Type) (s : Sentence) →
    Exact (restrictBy F C) s → (x : Model F) → C x → realize F (translate F s) x ↔ den F s x
  den-of-restrictBy F C s h x c = h (x , c)

  -- A reading of every sentence reads the sentences of any `P`.
  partial : {F G : Family} (P : Sentence → Type) → Hub F G → PartialHub P F G
  partial P h = record { map = Hub.map h ; read = λ x s _ → Hub.read h x s }

  -- A reading of the sentences of `P` from a conjugacy that holds for them.
  partialConjugacy : {F G : Family} (I : Invariance) (P : Sentence → Type)
    (map : Model F → Model G) (conj : Model F → Invariance.Conj I) →
    ((x : Model F) (s : Sentence) → P s →
      holds (system F x) s ≃ holds (Invariance.act I (conj x) (system G (map x))) s) →
    PartialHub P F G
  partialConjugacy {G = G} I P map conj p = record
    { map = map
    ; read = λ x s ps →
        compEquiv (p x s ps) (Invariance.invariant I (conj x) (system G (map x)) s) }

  -- Readings compose: a spoke of a spoke reads through the hub.
  compose : {F G H : Family} → Hub F G → Hub G H → Hub F H
  compose h k = record
    { map = λ x → Hub.map k (Hub.map h x)
    ; read = λ x s → compEquiv (Hub.read h x s) (Hub.read k (Hub.map h x) s) }
