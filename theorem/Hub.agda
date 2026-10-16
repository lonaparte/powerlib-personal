{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.Hub where

-- Scaffold of the hub connections: a spoke family read through a hub family.
--
-- A hub is a family whose laws are proved once (the swing equation, the PI-PLL); a spoke is a
-- family whose models are read as hub models: a map of models and, for every model, a reading
-- under which its system and the system of its image satisfy the same sentences (an affine
-- change of state coordinates in the library). Univalence turns the readings into a path from
-- the spoke's satisfaction structure to the hub's pulled back along the map
-- (`readPath`), so every construction over satisfaction structures — denotations, legal spaces,
-- generated connections — is the hub's pulled back (`comap`, Lean's `Family.comap`). A reading
-- comes from a conjugacy under which satisfaction is invariant (`viaConjugacy`). What a spoke still has to supply is the
-- correspondence of its own requirement language with the hub's on a context; then exactness
-- and soundness pass from the hub to the spoke (`exactUnder-pullback`, `sound-pullback`).
-- Readings compose (`compose`), so a spoke of a spoke reads through the hub.
--
-- The Lean connection is `theorem/Spectral/Hub.lean` (`exactUnder_of_hub`, `exact_of_hub`,
-- `sound_of_hub`, `realize_subset_den_of_hub`; readings by conjugacy
-- `mem_den_flow_iff_of_transport`), with the readings proved per spoke
-- (`DroopLPF.mem_den_iff_swing`, `ClassicalSM.mem_den_flow_iff_swing`,
-- `Limiting.mem_den_flow_iff_swing`, `PLLPH.mem_den_flow_iff_srf`,
-- `CascadeControl.mem_den_iff_imc`). Nothing here is exported.

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

module _ (S : Semantics) where
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

  -- Readings compose: a spoke of a spoke reads through the hub.
  compose : {F G H : Family} → Hub F G → Hub G H → Hub F H
  compose h k = record
    { map = λ x → Hub.map k (Hub.map h x)
    ; read = λ x s → compEquiv (Hub.read h x s) (Hub.read k (Hub.map h x) s) }
