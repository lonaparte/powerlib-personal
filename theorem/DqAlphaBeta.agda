{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.DqAlphaBeta where

-- Scaffold of the comparison of the two descriptions of one series R–L branch: in the dq frame
-- rotating at the constant speed `ω`, `L i̇ = v − R i − ω L J i`, and in the stationary αβ frame,
-- `L i̇ = v − R i` (`CurrentControl.family` of `theorem/CurrentControl/DqRL.lean`, models
-- `CurrentControl.DqBranch` `(R, L, ω)`). The αβ description is the member at speed zero, so the
-- change of frame on models is `alphaBeta (R, L, ω) = (R, L, 0)` (`DqBranch.alphaBeta`), and
-- changing the frame speed (`reframe`) does not change the αβ description
-- (`alphaBeta-reframe`). Park's transformation maps the trajectories of the two descriptions one
-- to one for every differentiable frame angle (`CurrentControl.alphaBetaRL_iff_dqRL`); it is
-- time-varying, so the two fields are not conjugate — their spectra are `−R/L ± jω` and `−R/L` —
-- and the comparison is not a reading by conjugacy (`viaConjugacy`). It holds for the attractive
-- sentences and sampled contraction (`Attractive`), read through the plant: the dq plant is
-- Hurwitz exactly when `R/L > 0`, at every frame speed (`spectrum`). So the attractive
-- denotation of the family is its own pulled back along `alphaBeta` (`den-eq`): the αβ and dq
-- descriptions are stable together, and every two frame speeds agree (`frame-invariant`). The
-- other sentences are not compared. Lean: `linear` is the linear reading of
-- `CurrentControl.family` (`Spectral.linear_den`), `spectrum` is
-- `CurrentControl.DqBranch.isHurwitz_plant_iff` (from
-- `CurrentControl.spectrallyStable_dqRLMatrix_iff`), `damped` is `CurrentControl.mem_den_iff`,
-- `den-eq` is `CurrentControl.den_eq_alphaBeta`; `frame-invariant` is `den-eq` taken at two
-- speeds and has no Lean statement of its own. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import theorem.FamilyReading
open import theorem.FlowSemantics using (Scalars)

-- The requirement language of the family (`Spectral.Requirement`).
data LinearReq : Type where
  stable unstable' : LinearReq

module _ (Sc : Scalars) where
  open Scalars Sc

  -- One series R–L branch read in the dq frame rotating at `ω` (Lean `DqBranch`).
  record DqBranch : Type where
    constructor dqBranch
    field
      R L ω : ℝ

  open DqBranch

  -- The same branch in the stationary αβ frame (Lean `DqBranch.alphaBeta`).
  alphaBeta : DqBranch → DqBranch
  alphaBeta m = dqBranch (R m) (L m) 0r

  -- The same branch read in the frame rotating at `ω'`.
  reframe : ℝ → DqBranch → DqBranch
  reframe ω' m = dqBranch (R m) (L m) ω'

  -- The αβ description does not depend on the frame the branch was read in.
  alphaBeta-reframe : (ω' : ℝ) (m : DqBranch) → alphaBeta (reframe ω' m) ≡ alphaBeta m
  alphaBeta-reframe ω' m = refl

  alphaBeta-zero : (m : DqBranch) → reframe 0r m ≡ alphaBeta m
  alphaBeta-zero m = refl

  module Reading (S : Semantics) where
    open Semantics S
    open Readings S

    module _ (Attractive : Sentence → Type) (branchSystem : DqBranch → System)
      (branchMeets : DqBranch → LinearReq → Type) (branchTranslate : Sentence → LinearReq → Type)
      (Hurwitz : DqBranch → Type)
      -- What Lean proves.
      (linear : (s : Sentence) → Attractive s → (m : DqBranch) →
        holds (branchSystem m) s ↔ Hurwitz m)
      (spectrum : (m : DqBranch) → Hurwitz m ↔ (0r < R m / L m))
      where

      family : Family
      family = record
        { Model = DqBranch ; Req = LinearReq ; system = branchSystem ; meets = branchMeets
        ; translate = branchTranslate }

      -- The αβ descriptions: the family read along `alphaBeta` (`Family.comap`).
      alphaBetaFamily : Family
      alphaBetaFamily = comap family alphaBeta

      -- Every branch is stable as its αβ description is: `R/L > 0` does not see `ω`.
      damped : (s : Sentence) → Attractive s → (m : DqBranch) →
        den family s m ↔ (0r < R m / L m)
      damped s a m = ↔-trans (linear s a m) (spectrum m)

      -- The attractive denotation of the family is its own pulled back along `alphaBeta`.
      den-eq : (s : Sentence) → Attractive s → (m : DqBranch) →
        den family s m ↔ den alphaBetaFamily s m
      den-eq s a m = ↔-trans (damped s a m) (snd (damped s a (alphaBeta m)) ,
        fst (damped s a (alphaBeta m)))

      -- Every two frame speeds agree.
      frame-invariant : (s : Sentence) → Attractive s → (m : DqBranch) (ω' : ℝ) →
        den family s m ↔ den family s (reframe ω' m)
      frame-invariant s a m ω' = ↔-trans (damped s a m) (snd (damped s a (reframe ω' m)) ,
        fst (damped s a (reframe ω' m)))
