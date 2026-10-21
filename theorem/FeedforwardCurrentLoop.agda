{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.FeedforwardCurrentLoop where

-- Scaffold of the reading of the PI current loop with low-pass PCC-voltage feedforward through the
-- PI current loop (`CurrentControl.LPFLoop.lpfFamily` of `theorem/CurrentControl/Feedforward.lean`
-- read through `CurrentControl.PIParams.family` of `theorem/CurrentControl/PILoop.lean`). A loop
-- is a PI loop `(L, R, K_p, K_i)` with a feedforward filter `τ dṽ/dt = v − ṽ` (`LPFLoop`, map of
-- models `LPFLoop.pi`). Its closed loop is block triangular: the spectrum is the PI loop's
-- together with `−1/τ`, so its plant is Hurwitz exactly when the PI plant is and `τ > 0`
-- (`block`). Both families read their attractive sentences and sampled contraction
-- (`Attractive`) through their plants, so the attractive denotation of the feedforward family is
-- the PI family's pulled back along `LPFLoop.pi` (`Family.comap`), cut by `τ > 0` (`den-eq`).
-- On the context `τ > 0` (a predicate on the parameters) the feedforward loop therefore reads
-- through its PI loop on these sentences (`reading`), and outside it satisfies none of them
-- (`not-den`). The reading is partial: the other sentences are not compared, and the two
-- families' own soundness and exactness (`lpfChain_le_semantics`, `lpfExact`) are proved for
-- each family, not transferred. Lean: `pi-linear` is `CurrentControl.PIParams.family_isLinear`
-- read by `Family.IsLinear.den_hurwitz`, `lpf-linear` is
-- `CurrentControl.LPFLoop.lpfFamily_isLinear` read by `Family.IsLinear.den_hurwitz`, `block` is
-- `CurrentControl.PIParams.lpf_isHurwitz_iff` (from
-- `CurrentControl.PIParams.characteristic_root_iff`), `den-eq` is
-- `CurrentControl.LPFLoop.lpfDen_eq`. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)

open import theorem.FamilyReading
open import theorem.FlowSemantics using (Scalars)

-- The requirement language of both families (`Spectral.Requirement`).
data LinearReq : Type where
  stable unstable' : LinearReq

module _ (Sc : Scalars) where
  open Scalars Sc

  record PIParams : Type where
    constructor piParams
    field
      L R Kp Ki : ℝ

  -- A PI loop with low-pass feedforward of time constant `τ` (Lean `LPFLoop`).
  record LPFLoop : Type where
    constructor lpfLoop
    field
      pi : PIParams
      τ : ℝ

  open LPFLoop

  module Reading (S : Semantics) where
    open Semantics S
    open Readings S

    module _ (Attractive : Sentence → Type)
      (piSystem : PIParams → System) (lpfSystem : LPFLoop → System)
      (piMeets : PIParams → LinearReq → Type) (lpfMeets : LPFLoop → LinearReq → Type)
      (piTranslate lpfTranslate : Sentence → LinearReq → Type)
      -- Hurwitz plants: the PI loop's and the feedforward loop's state matrices.
      (Hurwitz₂ : PIParams → Type) (Hurwitz₃ : LPFLoop → Type)
      -- What Lean proves.
      (pi-linear : (s : Sentence) → Attractive s → (p : PIParams) →
        holds (piSystem p) s ↔ Hurwitz₂ p)
      (lpf-linear : (s : Sentence) → Attractive s → (q : LPFLoop) →
        holds (lpfSystem q) s ↔ Hurwitz₃ q)
      (block : (q : LPFLoop) → Hurwitz₃ q ↔ (Hurwitz₂ (pi q) × (0r < τ q)))
      where

      piFamily lpfFamily : Family
      piFamily = record
        { Model = PIParams ; Req = LinearReq ; system = piSystem ; meets = piMeets
        ; translate = piTranslate }
      lpfFamily = record
        { Model = LPFLoop ; Req = LinearReq ; system = lpfSystem ; meets = lpfMeets
        ; translate = lpfTranslate }

      -- The PI family pulled back along `LPFLoop.pi`.
      alongPI : Family
      alongPI = comap piFamily pi

      -- The attractive denotation of the feedforward family is the pulled-back one, cut by
      -- `τ > 0`.
      den-eq : (s : Sentence) → Attractive s → (q : LPFLoop) →
        den lpfFamily s q ↔ (den alongPI s q × (0r < τ q))
      den-eq s a q = ↔-trans (lpf-linear s a q) (↔-trans (block q) (to , from))
        where
          to : Hurwitz₂ (pi q) × (0r < τ q) → den alongPI s q × (0r < τ q)
          to (h , t) = snd (pi-linear s a (pi q)) h , t
          from : den alongPI s q × (0r < τ q) → Hurwitz₂ (pi q) × (0r < τ q)
          from (d , t) = fst (pi-linear s a (pi q)) d , t

      -- On the context `τ > 0` a feedforward loop satisfies an attractive sentence exactly when
      -- its PI loop does.
      reading : (q : LPFLoop) → 0r < τ q → (s : Sentence) → Attractive s →
        den lpfFamily s q ↔ den piFamily s (pi q)
      reading q t s a = (λ d → fst (fst (den-eq s a q) d)) , (λ d → snd (den-eq s a q) (d , t))

      -- Outside it the feedforward loop satisfies no attractive sentence.
      not-den : (q : LPFLoop) → ¬ (0r < τ q) → (s : Sentence) → Attractive s →
        ¬ den lpfFamily s q
      not-den q n s a d = n (snd (fst (den-eq s a q) d))
