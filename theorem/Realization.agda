{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.Realization where

-- Scaffold of realizations, the generic pattern of the model–implementation connections: an
-- implementation layer over a model layer (`Stack.Implementation`,
-- `theorem/Stack/Implementation.lean`) relates a model family to an implementation family —
-- models under realistic constraints: sampling, switching, numerical integration — by a
-- realization relation. An implementation is
-- certified for a sentence when every model it realizes satisfies it; realization soundness within
-- constraints `Δ` says certified implementations satisfy the sentence themselves, completeness the
-- converse, exactness both. Most implementations realize the model they were designed from
-- (`ofDesign`): then certification is the design model's denotation, and a reading of the
-- implementation through its design model on a context — the same kind of reading as a spoke
-- through a hub (`theorem/FamilyReading.agda`) — makes the realization exact there
-- (`exactUnder-of-reading`); a certified implementation outside the sentence refutes soundness
-- (`not-sound-of-witness`). Each realization of the library has its own scaffold, named after its
-- two layers (`ExactSampling`, `SwitchedAveraging`, `EulerDiscretization`). The Lean connection is
-- `theorem/Stack/Implementation.lean` (`ofDesign`, `realizationExactUnder_of_design`,
-- `realizationExactUnder_of_den_eq_preimage`, `not_realizationSoundUnder_of_design`). Nothing here
-- is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import theorem.FamilyReading

module Realizations (S : Semantics) where
  open Semantics S
  open Readings S

  -- An implementation layer over a model layer.
  record Implementation : Type₁ where
    field
      model impl : Family
      realizes : Family.Model model → Family.Model impl → Type

  module _ (L : Implementation) where
    open Implementation L

    -- Implementations all of whose realized models satisfy `s`.
    Certified : Sentence → Family.Model impl → Type
    Certified s y = (x : Family.Model model) → realizes x y → den model s x

    SoundUnder : (Family.Req impl → Type) → Sentence → Type
    SoundUnder Δ s = (y : Family.Model impl) → realize impl Δ y → Certified s y → den impl s y

    CompleteUnder : (Family.Req impl → Type) → Sentence → Type
    CompleteUnder Δ s = (y : Family.Model impl) → realize impl Δ y → den impl s y → Certified s y

    ExactUnder' : (Family.Req impl → Type) → Sentence → Type
    ExactUnder' Δ s = (y : Family.Model impl) → realize impl Δ y → Certified s y ↔ den impl s y

    -- A certified implementation outside the sentence refutes soundness in every context it is
    -- in.
    not-sound-of-witness : {Δ : Family.Req impl → Type} {s : Sentence} (y : Family.Model impl) →
      realize impl Δ y → Certified s y → ¬ den impl s y → ¬ SoundUnder Δ s
    not-sound-of-witness y hΔ hc hn h = hn (h y hΔ hc)

  -- Realization by a design map: an implementation realizes the model it was designed from.
  ofDesign : (m i : Family) → (Family.Model i → Family.Model m) → Implementation
  ofDesign m i design = record { model = m ; impl = i ; realizes = λ x y → design y ≡ x }

  module Design (m i : Family) (design : Family.Model i → Family.Model m) where
    designed : Implementation
    designed = ofDesign m i design

    -- Certification is the design model's denotation.
    certified↔ : (s : Sentence) (y : Family.Model i) → Certified designed s y ↔ den m s (design y)
    certified↔ s y = (λ c → c (design y) refl) , (λ d x p → subst (den m s) p d)

    -- A reading of the implementations of a context `C` through their design models makes the
    -- realization exact on `C`: implementations satisfy the sentence exactly when their design
    -- models do.
    exactUnder-of-reading : (C : Family.Model i → Type) (s : Sentence) →
      ((y : Family.Model i) → C y → den i s y ↔ den m s (design y)) →
      (y : Family.Model i) → C y → Certified designed s y ↔ den i s y
    exactUnder-of-reading C s r y c =
      ↔-trans (certified↔ s y) (snd (r y c) , fst (r y c))
