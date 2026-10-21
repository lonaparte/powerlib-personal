{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.Similarity where

-- Scaffold of changes of state coordinates of linear plants with ports. A plant changed by
-- invertible state coordinates `x' = T x` (`S T = 1`, `T S = 1`) is a similar plant; its port
-- system is the original one conjugated by `T`, `S` (state dynamics transported, output read back
-- through `S`) (`system-change`), and conjugation preserves every sentence: the flow sentences by
-- the transport law, passivity because a storage pulls back along the inverse coordinates while
-- input and supplied power stay (`conjugate-invariant`). So similar plants satisfy the same
-- sentences (`sentence≃`), and a linear family reads through another along a map of models with
-- similar plants, on every sentence and with no minimality assumption (`reading`, `den↔`). The
-- port-Hamiltonian family reads through itself this way: similar plants
-- (`PH.mem_den_iff_of_similar`) and RL networks whose branches are rescaled by nonzero factors, a
-- diagonal change of coordinates (`PH.Models.rlNetworkPH_scale_mem_den_iff`). Lean
-- (`theorem/Linear/Coordinates.lean`): `system-change` is `Plant.system_changeCoordinates`,
-- `conjugate-invariant` is
-- `Port.System.passive_conjugate` with the flow transport of `Similar.holds_iff`, `sentence≃` is
-- `Similar.sentence_iff`, `den↔` is `Family.IsLinear.den_similar`. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Data.Sigma

open import theorem.FamilyReading

module _ (S : Semantics) where
  open Semantics S
  open Readings S

  -- Plants, their changes of coordinates, and their port systems (Lean `Plant`,
  -- `Plant.changeCoordinates`, `Plant.system`), with the conjugation of port systems (Lean
  -- `Port.System.conjugate`).
  module _ (Plant Change : Type) (change : Change → Plant → Plant)
    (portSystem : Plant → System) (conjugate : Change → System → System)
    -- What Lean proves.
    (system-change : (c : Change) (m : Plant) →
      portSystem (change c m) ≡ conjugate c (portSystem m))
    (conjugate-invariant : (c : Change) (a : System) (s : Sentence) →
      holds (conjugate c a) s ≃ holds a s)
    where

    coordinates : Invariance
    coordinates = record { Conj = Change ; act = conjugate ; invariant = conjugate-invariant }

    -- Similar plants (Lean `Linear.Similar`).
    Similar : Plant → Plant → Type
    Similar m m' = Σ[ c ∈ Change ] m' ≡ change c m

    -- Similar plants satisfy the same sentences, passivity included.
    sentence≃ : {m m' : Plant} → Similar m m' → (s : Sentence) →
      holds (portSystem m') s ≃ holds (portSystem m) s
    sentence≃ {m} (c , p) s =
      conjugateReading coordinates c (cong portSystem p ∙ system-change c m) s

    -- Linear families: models read on the port systems of their plants (Lean `Family.IsLinear`).
    module _ (F G : Family) (plantF : Family.Model F → Plant) (plantG : Family.Model G → Plant)
      (linF : (x : Family.Model F) → Family.system F x ≡ portSystem (plantF x))
      (linG : (y : Family.Model G) → Family.system G y ≡ portSystem (plantG y))
      (g : Family.Model F → Family.Model G)
      (similar : (x : Family.Model F) → Similar (plantF x) (plantG (g x)))
      where

      -- `F` reads through `G` along `g`, on every sentence.
      reading : Hub F G
      reading = record
        { map = g
        ; read = λ x s →
            compEquiv (pathToEquiv (cong (λ a → holds a s) (linF x)))
              (compEquiv (invEquiv (sentence≃ (similar x) s))
                (pathToEquiv (cong (λ a → holds a s) (sym (linG (g x)))))) }

      -- Every denotation of `F` is the preimage of `G`'s along `g`.
      den↔ : (x : Family.Model F) (s : Sentence) → den F s x ↔ den G s (g x)
      den↔ x s = ↔-of-≃ (Hub.read reading x s)
