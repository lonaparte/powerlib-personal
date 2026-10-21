{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.CascadeCurrentLoop where

-- Scaffold of the connection of the linearized current-loop/DC-link cascade with the converter
-- PI current loop (`linearizedFamily` of `theorem/GFL/DCLink/Cascade.lean` and
-- `CurrentControl.PIParams.family` of `theorem/CurrentControl/PILoop.lean`). A cascade carries its
-- current loop (`CascadeParams.pi`) and a DC node. Both families read a parameter set as the port
-- system of a linear plant with the language `{stable, unstable}` and the table of
-- `Spectral.linearFamily`, which sends the attractive sentences and sampled contraction to
-- `stable`; such a sentence holds exactly when the state matrix is Hurwitz. The cascade's state
-- matrix is block triangular (current loop, then DC node), so it is Hurwitz exactly when the
-- current loop's is and the DC-node coefficient `I_dc0/(C V0)` is positive. The connection is a
-- cut, not a reading: on the attractive sentences the cascade's denotation is the PI family's
-- pulled back along `pi` (`comap`) and cut by a positive DC-node coefficient (`den↔`). The
-- cascade's `stable` is the PI loop's at `pi` with that sign, so exactness passes from the PI
-- family to the cascade (`exact-cut`), and with `L, C, V0 > 0` the PI member characterization gives
-- the cascade's (`mem-den↔`). A cascade with a stable current loop and a DC node that is not
-- (inverter mode, `I_dc0 < 0`) refutes any reading along `pi` (`not-reading`): the DC node adds its
-- own pole. Only the attractive sentences are connected; instability, Lyapunov stability and the
-- global sentences of the cascade are not related to the PI family. Lean: `isHurwitz` is
-- `Family.IsLinear.den_hurwitz` (through `Spectral.linear_den`), `block` is
-- `CascadeParams.isHurwitz_iff_pi` (with `CurrentControl.PIParams.isHurwitz_iff_div`); `den↔` is
-- `linearizedDen_eq`; `exact-cut` is `linearizedExact` from `CurrentControl.PIParams.exact` (Lean
-- proves it directly, by `Spectral.linear_exact`); `mem-den↔` is `linearized_mem_den_iff` from
-- `CurrentControl.PIParams.mem_den_iff` and `div_pos_iff_of_pos_right` (Lean proves it directly,
-- by `CascadeParams.isHurwitz_iff`); `not-reading` has no separate Lean statement. Nothing here is
-- exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Relation.Nullary using (¬_)

open import theorem.FamilyReading
open import theorem.FlowSemantics using (Scalars)

↔-refl : {A : Type} → A ↔ A
↔-refl = (λ a → a) , (λ a → a)

↔-sym : {A B : Type} → A ↔ B → B ↔ A
↔-sym (f , g) = g , f

×-↔ : {A A' B B' : Type} → A ↔ A' → B ↔ B' → (A × B) ↔ (A' × B')
×-↔ (f , g) (h , k) = (λ x → f (fst x) , h (snd x)) , (λ x → g (fst x) , k (snd x))

module _ (Sc : Scalars) where
  open Scalars Sc

  -- The current loop `(L, R, K_p, K_i)` (Lean `CurrentControl.PIParams`).
  record PIParams : Type where
    constructor piParams
    field
      L R Kp Ki : ℝ

  -- The cascade: its current loop, the DC-link capacitance, the PCC voltage, the DC operating
  -- voltage and the operating current (Lean `CascadeParams`).
  record CascadeParams : Type where
    constructor cascadeParams
    field
      pi : PIParams
      C Vd0 V0 Id0 : ℝ

  open PIParams
  open CascadeParams

  -- `I_dc0 = (V_d0 − R I_d0) I_d0 / V0` and the DC-node coefficient `I_dc0/(C V0)`.
  Idc0 dcCoeff : CascadeParams → ℝ
  Idc0 p = (Vd0 p - R (pi p) * Id0 p) * Id0 p / V0 p
  dcCoeff p = Idc0 p / (C p * V0 p)

  -- The DC node's pole `−I_dc0/(C V0)` is stable.
  DCNode : CascadeParams → Type
  DCNode p = 0r < dcCoeff p

  -- The requirements of a linear spectral family (`Spectral.Requirement`) and their satisfaction
  -- through static conditions (`Spectral.Meets`).
  data Requirement : Type where
    stable unstable : Requirement

  meetsBy : {X : Type} → (X → Type) → (X → Type) → X → Requirement → Type
  meetsBy S U x stable = S x
  meetsBy S U x unstable = U x

  -- Positive and negative monic coefficients of the PI loop (`CurrentControl.PIParams.Stable`,
  -- `CurrentControl.PIParams.Unstable`).
  PIStable PIUnstable : PIParams → Type
  PIStable q = (0r < (R q + Kp q) / L q) × (0r < Ki q / L q)
  PIUnstable q = ((R q + Kp q) / L q < 0r) ⊎ (Ki q / L q < 0r)

  -- The cascade's: the PI loop's at `pi` and the DC-node sign (`CascadeParams.LinStable`,
  -- `CascadeParams.LinUnstable`).
  LinStable LinUnstable : CascadeParams → Type
  LinStable p = PIStable (pi p) × DCNode p
  LinUnstable p = PIUnstable (pi p) ⊎ (dcCoeff p < 0r)

  -- The semantic layer, the attractive sentences with sampled contraction, and the table both
  -- families share (`Spectral.linearTranslate`), which sends them to `stable` alone.
  module _ (S : Semantics) (Attractive : Semantics.Sentence S → Type)
    (table : Semantics.Sentence S → Requirement → Type)
    (table-stable : (s : Semantics.Sentence S) → Attractive s → (q : Requirement) →
      table s q ↔ (q ≡ stable))
    where
    open Semantics S
    open Readings S

    -- A family of this language realizes the translation of an attractive sentence exactly when
    -- it meets `stable`.
    realize-table : {X : Type} (meets : X → Requirement → Type) (s : Sentence) → Attractive s →
      (x : X) → ((q : Requirement) → table s q → meets x q) ↔ meets x stable
    realize-table meets s a x =
      (λ h → h stable (snd (table-stable s a stable) refl))
      , (λ m q t → subst (meets x) (sym (fst (table-stable s a q) t)) m)

    -- Linear plants of every dimension: their systems and the Hurwitz property of their state
    -- matrices.
    module Linear (Plant : Type) (plantSystem : Plant → System) (Hurwitz : Plant → Type)
      (piPlant : PIParams → Plant) (cascadePlant : CascadeParams → Plant)
      where

      piFamily cascadeFamily : Family
      piFamily = record
        { Model = PIParams ; Req = Requirement ; system = λ q → plantSystem (piPlant q)
        ; meets = meetsBy PIStable PIUnstable ; translate = table }
      cascadeFamily = record
        { Model = CascadeParams ; Req = Requirement ; system = λ p → plantSystem (cascadePlant p)
        ; meets = meetsBy LinStable LinUnstable ; translate = table }

      -- What Lean proves.
      record Obligations : Type where
        field
          -- An attractive sentence holds of a linear plant exactly when its state matrix is
          -- Hurwitz.
          isHurwitz : (a : Plant) (s : Sentence) → Attractive s →
            holds (plantSystem a) s ↔ Hurwitz a
          -- The block-triangular state matrix: current loop, then DC node.
          block : (p : CascadeParams) →
            Hurwitz (cascadePlant p) ↔ (Hurwitz (piPlant (pi p)) × DCNode p)

      module _ (ob : Obligations) where
        open Obligations ob

        -- The PI family read on cascades through their current loops.
        piPulledBack : Family
        piPulledBack = comap piFamily pi

        -- On the attractive sentences the cascade's denotation is the pulled-back one cut by a
        -- positive DC-node coefficient.
        den↔ : (s : Sentence) → Attractive s → (p : CascadeParams) →
          den cascadeFamily s p ↔ (den piPulledBack s p × DCNode p)
        den↔ s a p = ↔-trans (isHurwitz (cascadePlant p) s a)
          (↔-trans (block p) (×-↔ (↔-sym (isHurwitz (piPlant (pi p)) s a)) ↔-refl))

        -- Exactness of the PI family passes to the cascade through the cut.
        exact-cut : (s : Sentence) → Attractive s → Exact piFamily s → Exact cascadeFamily s
        exact-cut s a h p =
          ↔-trans (realize-table (meetsBy LinStable LinUnstable) s a p)
            (↔-trans
              (×-↔ (↔-trans (↔-sym (realize-table (meetsBy PIStable PIUnstable) s a (pi p)))
                (h (pi p))) ↔-refl)
              (↔-sym (den↔ s a p)))

        -- A stable current loop with a DC node that is not stable refutes a reading along `pi`.
        not-reading : (s : Sentence) → Attractive s → (p : CascadeParams) →
          den piFamily s (pi p) → ¬ DCNode p →
          ¬ ((p' : CascadeParams) → den cascadeFamily s p' ↔ den piFamily s (pi p'))
        not-reading s a p hpi hdc r = hdc (snd (fst (den↔ s a p) (snd (r p) hpi)))

        -- With `L, C, V0 > 0` the PI member characterization gives the cascade's.
        module Members
          -- What Lean proves: the PI loop's member characterization and two sign facts.
          (pi-mem : (q : PIParams) → 0r < L q → (s : Sentence) → Attractive s →
            den piFamily s q ↔ ((0r < R q + Kp q) × (0r < Ki q)))
          (div-pos : (a b : ℝ) → 0r < b → (0r < a / b) ↔ (0r < a))
          (mul-pos : (a b : ℝ) → 0r < a → 0r < b → 0r < a * b)
          where

          mem-den↔ : (p : CascadeParams) → 0r < L (pi p) → 0r < C p → 0r < V0 p →
            (s : Sentence) → Attractive s →
            den cascadeFamily s p ↔
              (((0r < R (pi p) + Kp (pi p)) × (0r < Ki (pi p))) × (0r < Idc0 p))
          mem-den↔ p hL hC hV s a = ↔-trans (den↔ s a p)
            (×-↔ (pi-mem (pi p) hL s a)
              (div-pos (Idc0 p) (C p * V0 p) (mul-pos (C p) (V0 p) hC hV)))
