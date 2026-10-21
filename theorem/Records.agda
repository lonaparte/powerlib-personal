{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.Records where

-- Scaffold of the record layer, the generic pattern: records that implementations may produce, over
-- a model–implementation layer (`theorem/Realization.agda`), as in a four-layer stack
-- (`Stack` of `theorem/Stack/Basic.lean`, which extends an `Implementation` by the production
-- relation `produces`). Data-driven inference is the whole backward traversal (`Infer`: the
-- sentences every model realized by a possible producer of the records satisfies),
-- theory-driven certification the forward one (`CertifiedRecords`); they form the whole-chain
-- Galois connection (`galois`). Inference may check the models' translation instead of their
-- semantics when it is sound (`infer-of-organized`); under realization soundness, with every
-- producer within the constraints, the inferred sentences are true of the producers themselves
-- (`truth-of-infer`); a record outside the records predicted by a sentence refutes it for every
-- producer (`refutes`). Each implementation of the library with records has its own scaffold,
-- listed in the scaffold table of `Architecture.md`. Lean (`theorem/Stack/Basic.lean`): `Infer`,
-- `CertifiedRecords`, `Truth`, `Predicted` are `Stack.mem_infer`, `Stack.mem_certified`,
-- `Stack.mem_truth`, `Stack.mem_predicted`; `galois` is `Stack.subset_certified_iff`,
-- `infer-of-organized` is `Stack.mem_infer_of_organized`, `truth-of-infer` is
-- `Stack.infer_subset_truth`, `refutes` is `Stack.refutes`. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)

open import theorem.FamilyReading
open import theorem.Realization

-- The record layer of a stack: records `V` that implementations may produce
-- (`Stack.produces`), over an implementation layer.
module Stacks (S : Semantics) where
  open Semantics S
  open Readings S
  open Realizations S

  module _ (L : Implementation) {V : Type}
    (produces : Family.Model (Implementation.impl L) → V → Type) where
    open Implementation L

    -- Data-driven inference, the whole backward traversal: the sentences every model realized by
    -- a possible producer of a record of `D` satisfies.
    Infer : (V → Type) → Sentence → Type
    Infer D s = (v : V) → D v → (y : Family.Model impl) → produces y v → Certified L s y

    -- Theory-driven certification: the records all of whose possible producers realize only
    -- models of `Φ`.
    CertifiedRecords : (Sentence → Type) → V → Type
    CertifiedRecords Φ v = (y : Family.Model impl) → produces y v →
      (x : Family.Model model) → realizes x y → (s : Sentence) → Φ s → den model s x

    -- The truth at the implementation layer: the sentences every possible producer satisfies.
    Truth : (V → Type) → Sentence → Type
    Truth D s = (v : V) → D v → (y : Family.Model impl) → produces y v → den impl s y

    -- The records predicted by `s`: those some implementation satisfying `s` may produce.
    Predicted : Sentence → V → Type
    Predicted s v = Σ[ y ∈ Family.Model impl ] den impl s y × produces y v

    -- The whole-chain Galois connection: records support sentences exactly when they are
    -- certified for them.
    galois : (D : V → Type) (Φ : Sentence → Type) →
      ((v : V) → D v → CertifiedRecords Φ v) ↔ ((s : Sentence) → Φ s → Infer D s)
    galois D Φ =
      (λ h s φ v d y p x r → h v d y p x r s φ) , (λ h v d y p x r s φ → h s φ v d y p x r)

    -- Inference through the requirement language of the models and a sound translation.
    infer-of-organized : {D : V → Type} {s : Sentence} → Sound model s →
      ((v : V) → D v → (y : Family.Model impl) → produces y v → (x : Family.Model model) →
        realizes x y → realize model (Family.translate model s) x) → Infer D s
    infer-of-organized hS h v d y p x r = hS x (h v d y p x r)

    -- Under realization soundness, with every possible producer within the constraints, the
    -- inferred sentences are true of the implementations.
    truth-of-infer : {Δ : Family.Req impl → Type} {D : V → Type} {s : Sentence} →
      ((v : V) → D v → (y : Family.Model impl) → produces y v → realize impl Δ y) →
      SoundUnder L Δ s → Infer D s → Truth D s
    truth-of-infer hΔ hS hs v d y p = hS y (hΔ v d y p) (hs v d y p)

    -- A record outside the predicted records refutes the sentence for every producer.
    refutes : {s : Sentence} {y : Family.Model impl} {v : V} → produces y v →
      ¬ Predicted s v → ¬ den impl s y
    refutes p hv hs = hv (_ , hs , p)
