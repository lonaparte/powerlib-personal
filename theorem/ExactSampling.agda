{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.ExactSampling where

-- Scaffold of the exact sampling of continuous linear models: the model is `ẋ = A x`; its
-- implementation with period `T > 0` and zero-order hold is the discrete system
-- `x_{k+1} = e^{TA} x_k`, which realizes the model it was designed from (`ofDesign`, design map
-- `(T, A) ↦ A`) and reads the model's requirements through the design. Every sentence holds of the
-- sampled system exactly when it holds of the model (`sampling`): the attractive sentences and
-- sampled contraction because `A` is Hurwitz exactly when `e^{TA}` is Schur, Lyapunov stability and
-- instability because the flow is bounded exactly when its samples are, decay rates because every
-- time is `kT + s` with `s ∈ [0, T]`, conservation through the energy averaged over one period, and
-- passivity because neither system has ports. So the sampled family reads through its design
-- model on every sentence (`reading`), the realization is exact for every sentence with no
-- constraint (`exact`), and the sampled family inherits the soundness (`sound`) and the exactness
-- (`exact-transfer`, the design map being onto) of the model's translations. Lean
-- (`theorem/LTI/SampledFlow.lean`, `theorem/LTI/ExactSampling.lean`): `sampling` is
-- `LTI.holds_iff_holdsMap_exp` (with `LTI.isHurwitz_iff_schurStable_exp`,
-- `LTI.lyapunovStable_iff_exp`, `LTI.decay_iff_exp`, `LTI.conservative_iff_exp`; passivity from the
-- families having no ports), `reading` is `LTI.sampled_reading`, `exact` is
-- `LTI.exactSampling_realizationExact`, `sound` is `LTI.sampled_chain_le_semantics`,
-- `exact-transfer` is `LTI.sampled_exact_iff`. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import theorem.FamilyReading
open import theorem.Realization

module _ (S : Semantics) where
  open Semantics S
  open Readings S
  open Realizations S

  module _ (Mat Period : Type) (period : Period) (exp : Period → Mat → Mat)
    (continuous : Mat → System) (discrete : Period → Mat → System)
    -- The model family's requirement language.
    (Req : Type) (meets : Mat → Req → Type) (translate : Sentence → Req → Type)
    -- What Lean proves (periods are positive).
    (sampling : (T : Period) (A : Mat) (s : Sentence) →
      holds (discrete T (exp T A)) s ↔ holds (continuous A) s)
    where

    model : Family
    model = record
      { Model = Mat ; Req = Req ; system = continuous ; meets = meets ; translate = translate }

    -- The sampled family reads the model's requirements through the design.
    sampled : Family
    sampled = record
      { Model = Period × Mat ; Req = Req ; system = λ y → discrete (fst y) (exp (fst y) (snd y))
      ; meets = λ y → meets (snd y) ; translate = translate }

    open Design model sampled snd

    -- The sampled family reads through its design model on every sentence.
    reading : (s : Sentence) (y : Period × Mat) → den sampled s y ↔ den model s (snd y)
    reading s (T , A) = sampling T A s

    -- The realization is exact for every sentence, without constraints.
    exact : (s : Sentence) (y : Period × Mat) → Certified designed s y ↔ den sampled s y
    exact s y = exactUnder-of-reading (λ _ → Unit) s (λ y' _ → reading s y') y tt

    -- Soundness of the model's translations carries over.
    sound : (s : Sentence) → Sound model s → Sound sampled s
    sound s h y r = snd (reading s y) (h (snd y) r)

    -- So does exactness, both ways, since every model is the design of a sampled system.
    exact-transfer : (s : Sentence) → Exact sampled s ↔ Exact model s
    exact-transfer s =
      (λ h A → ↔-trans (h (period , A)) (reading s (period , A)))
      , (λ h y → ↔-trans (h (snd y)) (snd (reading s y) , fst (reading s y)))
