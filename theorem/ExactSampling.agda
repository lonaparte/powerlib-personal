{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.ExactSampling where

-- Scaffold of the exact sampling of continuous linear models: the model is `ẋ = A x`; its
-- implementation with period `T > 0` and zero-order hold is the discrete system
-- `x_{k+1} = e^{TA} x_k`, which realizes the model it was designed from (`ofDesign`, design map
-- `(T, A) ↦ A`). Every attractive sentence (and sampled contraction) of a linear continuous system
-- is the Hurwitz property of its matrix, every such sentence of a linear discrete system is the
-- Schur property, and `A` is Hurwitz exactly when `e^{TA}` is Schur; so the sampled implementation
-- reads through its design model (`reading`) and the realization is exact for every such sentence,
-- with no constraint (`exact`). Lean (`theorem/LTI/ExactSampling.lean`): `sampling` is
-- `LTI.isHurwitz_iff_schurStable_exp`, `continuous-reading` is `Family.IsLinear.den_hurwitz`,
-- `discrete-reading` is `Map.holdsMap_op_iff_schurStable` (`theorem/Map/LinearReading.lean`;
-- family form `Family.IsAutonomousMap.den_schurStable`), `reading` is
-- `LTI.sampled_den_eq_preimage`, `exact` is `LTI.exactSampling_realizationExactUnder`. Nothing
-- here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)

open import theorem.FamilyReading
open import theorem.Realization

module _ (S : Semantics) where
  open Semantics S
  open Readings S
  open Realizations S

  module _ (Mat Period : Type) (exp : Period → Mat → Mat) (Hurwitz Schur : Mat → Type)
    (continuous : Mat → System) (discrete : Period → Mat → System)
    (Attractive : Sentence → Type)
    -- What Lean proves (periods are positive).
    (sampling : (T : Period) (A : Mat) → Hurwitz A ↔ Schur (exp T A))
    (continuous-reading : (s : Sentence) → Attractive s → (A : Mat) →
      holds (continuous A) s ↔ Hurwitz A)
    (discrete-reading : (s : Sentence) → Attractive s → (T : Period) (Φ : Mat) →
      holds (discrete T Φ) s ↔ Schur Φ)
    where

    model : Family
    model = record
      { Model = Mat ; Req = ⊥ ; system = continuous ; meets = λ _ () ; translate = λ _ () }

    sampled : Family
    sampled = record
      { Model = Period × Mat ; Req = ⊥ ; system = λ y → discrete (fst y) (exp (fst y) (snd y))
      ; meets = λ _ () ; translate = λ _ () }

    open Design model sampled snd

    -- The sampled implementation reads through its design model on every attractive sentence.
    reading : (s : Sentence) → Attractive s → (y : Period × Mat) →
      den sampled s y ↔ den model s (snd y)
    reading s a (T , A) =
      ↔-trans (discrete-reading s a T (exp T A))
        (↔-trans (snd (sampling T A) , fst (sampling T A))
          (snd (continuous-reading s a A) , fst (continuous-reading s a A)))

    -- The realization is exact for every attractive sentence, without constraints.
    exact : (s : Sentence) → Attractive s → (y : Period × Mat) →
      Certified designed s y ↔ den sampled s y
    exact s a y = exactUnder-of-reading (λ _ → Unit) s (λ y' _ → reading s a y') y tt
