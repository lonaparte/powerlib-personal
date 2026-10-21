{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.DecouplingMismatch where

-- Scaffold of the dq current loop with an inductance estimate in its decoupling, as an
-- implementation of the PI current loop: the model is the single-axis PI current loop with perfect
-- decoupling (`CurrentControl.PIParams.family`); its implementation
-- `CurrentControl.MismatchParams` is the two-axis loop in a frame rotating at the constant speed
-- `ω` whose cross-decoupling `±ω L̂ i` uses the controller's estimate `L̂` of the inductance `L`,
-- leaving the residual `±ω ΔL i`, `ΔL = L − L̂`. The estimate is a parameter tolerance of the
-- controller, and each loop realizes its base PI loop (`ofDesign`, design map
-- `(base, ω, L̂) ↦ base`). The attractive sentences and sampled contraction (`Attractive`) of both
-- are read through their plants: the base loop satisfies them exactly when it is stable (monic
-- coefficients `(R + K_p)/L > 0`, `K_i/L > 0`), and so does the mismatched loop, for every `ω`
-- and every `ΔL` of any sign — its characteristic polynomial is `p(s) p̄(s)`,
-- `p(s) = L s² + (R + K_p + j ω ΔL) s + K_i`, and an imaginary perturbation of the `s`
-- coefficient alone never moves a root across the imaginary axis. So the attractive denotation of
-- the mismatched loops is the design's pulled back along `base` (`den-eq-base`), and the
-- realization is exact for these sentences without constraints (`exact`). Lean
-- (`theorem/CurrentControl/Mismatch.lean`): `design-reading` is
-- `CurrentControl.PIParams.family_isLinear` read by `Family.IsLinear.den_hurwitz` with
-- `CurrentControl.PIParams.isHurwitz_iff_div`, `loop-reading` is the linear reading of
-- `CurrentControl.MismatchParams.family` (`Spectral.linear_den`) with
-- `CurrentControl.MismatchParams.isHurwitz_iff_stable` (from
-- `CurrentControl.MismatchParams.stateMatrix_isHurwitz_iff` and
-- `Criteria.complexQuadratic_realConst_roots_re_neg_iff`), `den-eq-base` is
-- `CurrentControl.MismatchParams.den_eq_base`, `exact` is
-- `CurrentControl.MismatchParams.realizationExactUnder` (through
-- `Implementation.realizationExactUnder_of_den_eq_preimage`). Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)

open import theorem.FamilyReading
open import theorem.Realization

-- The requirement language of both families (`Spectral.Requirement`).
data LinearReq : Type where
  stable unstable' : LinearReq

module _ (S : Semantics) where
  open Semantics S
  open Readings S
  open Realizations S

  module _ (PIParams Speed Estimate : Type)
    (designSystem : PIParams → System) (loopSystem : PIParams → Speed → Estimate → System)
    (Attractive : Sentence → Type)
    -- The base loop: stable (positive monic coefficients), unstable (one of them negative), and
    -- the mismatched loop's instability condition (a negative damping coefficient
    -- `(R + K_p)/L`).
    (Stable Unstable NegativeDamping : PIParams → Type)
    -- What Lean proves.
    (design-reading : (s : Sentence) → Attractive s → (p : PIParams) →
      holds (designSystem p) s ↔ Stable p)
    (loop-reading : (s : Sentence) → Attractive s → (p : PIParams) (ω : Speed) (L̂ : Estimate) →
      holds (loopSystem p ω L̂) s ↔ Stable p)
    where

    -- A decoupled dq loop: the base PI loop, the frame speed and the inductance estimate.
    Loop : Type
    Loop = PIParams × Speed × Estimate

    base : Loop → PIParams
    base = fst

    designMeets : PIParams → LinearReq → Type
    designMeets p stable = Stable p
    designMeets p unstable' = Unstable p

    loopMeets : Loop → LinearReq → Type
    loopMeets y stable = Stable (base y)
    loopMeets y unstable' = NegativeDamping (base y)

    -- The two families; their translations are their own and do not enter the realization laws.
    designFamily : Family
    designFamily = record
      { Model = PIParams ; Req = LinearReq ; system = designSystem ; meets = designMeets
      ; translate = λ _ _ → ⊥ }

    loops : Family
    loops = record
      { Model = Loop ; Req = LinearReq
      ; system = λ y → loopSystem (fst y) (fst (snd y)) (snd (snd y))
      ; meets = loopMeets ; translate = λ _ _ → ⊥ }

    open Design designFamily loops base

    -- The mismatch never changes the stability region: the attractive denotation of the
    -- mismatched loops is the design's pulled back along `base`.
    den-eq-base : (s : Sentence) → Attractive s → (y : Loop) →
      den loops s y ↔ den (comap designFamily base) s y
    den-eq-base s a (p , ω , L̂) =
      ↔-trans (loop-reading s a p ω L̂) (snd (design-reading s a p) , fst (design-reading s a p))

    -- The attractive sentences are realized exactly, without constraints.
    exact : (s : Sentence) → Attractive s → ExactUnder' designed (λ _ → ⊥) s
    exact s a y _ = exactUnder-of-reading (λ _ → Unit) s (λ y' _ → den-eq-base s a y') y tt
