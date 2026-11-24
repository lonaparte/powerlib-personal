{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFM.FullModel.FullModelQVDroop where
-- Lean modules: theorem.GridTiedConverter.GFM.FullModel.Saddle

-- Scaffold of the reading of the 13-state grid-forming converter with Q–V droop
-- (`GFM.FullModel.family` of `theorem/GridTiedConverter/GFM/FullModel/Saddle.lean`) through its
-- quasi-steady reduction, the reduced Q–V droop model (`GFM.QVDroop.family` of
-- `theorem/GridTiedConverter/GFM/QVDroop.lean`). A full-order model is a parameter set with a
-- selected quasi-steady point `(δ*, Q*)`; its reduction (`reduce`) is the droop model
-- `GFM.FullModel.Params.qvDroop` at the point `(δ*, 0, Q*)`: without virtual impedance the
-- reduced field — the slow rows of the 13-state field on its quasi-steady set — is the droop field
-- (`GFM.FullModel.Params.reducedField_eq_qvDroop`), so the two reduced Jacobians agree. The two
-- families have systems of different dimension (13 against 3 states), so the connection is not a
-- reading of systems: it compares, under the context (nondegenerate fast block, no virtual
-- impedance, droop in its physical range), one sentence, in one direction.
-- * Instability transfers from the descending branch of the reduction to the full model, for
--   every choice of the controller gains (`descending→`, Lean
--   `GFM.FullModel.mem_den_unstable_of_qvDroop`): at a physical equilibrium of the droop model on
--   the descending part of its quasi-static characteristic the reduced Jacobian has a positive
--   determinant (`GFM.QVDroop.det_jacobian_eq_slope`, `GFM.QVDroop.one_add_nq_QE_Eplus`), and the
--   Jacobian determinant of the full field is the positive determinant of the fast block times it
--   (`GFM.FullModel.Params.det_jacobian_qssState`, `GFM.FullModel.Params.det_fastBlock_pos`). The
--   reduced model's own conclusion is `reduced-unstable` (Lean
--   `GFM.QVDroop.mem_den_unstable_of_slope_neg`).
-- * The local stability sentences are not compared: the full family translates them into a
--   requirement no model meets, and stability of the reduced ascending branch is not a statement
--   about the full model. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics using (Scalars)

module _ (Sc : Scalars) where
  open Scalars Sc

  module _ (Params : Type)
    -- The reduced droop models (Lean `GFM.QVDroop.Model`) and the reduction of a parameter set at
    -- a selected point `(δ*, Q*)` (Lean `GFM.FullModel.Params.qvDroop`).
    (DroopModel : Type) (toDroop : Params → ℝ → ℝ → DroopModel)
    -- The context: nondegenerate fast block, no virtual impedance, droop in its physical range.
    (Context : Params → Type)
    -- The descending physical branch of a droop model: an equilibrium at its point with positive
    -- EMF where the quasi-static characteristic descends.
    (Descending : DroopModel → Type)
    where

    -- A full-order model: parameters and a selected quasi-steady point `(δ*, Q*)`.
    record Model : Type where
      constructor model
      field
        p : Params
        δ Qf : ℝ

    open Model

    -- The reduction: the droop model of the parameters at the same point.
    reduce : Model → DroopModel
    reduce m = toDroop (p m) (δ m) (Qf m)

    module _ (S : Semantics) where
      open Semantics S
      open Readings S

      module _
        -- Instability. Each family keeps its own requirement language and translation (left
        -- empty here); the comparison reads the descending branch of the droop model directly.
        (unstable : Sentence) (fullSystem : Model → System) (droopSystem : DroopModel → System)
        where

        full reduced : Family
        full = record
          { Model = Model ; Req = ⊥ ; system = fullSystem ; meets = λ _ () ; translate = λ _ () }
        reduced = record
          { Model = DroopModel ; Req = ⊥ ; system = droopSystem ; meets = λ _ ()
          ; translate = λ _ () }

        -- What Lean proves.
        record Obligations : Type where
          field
            reduced-unstable : (r : DroopModel) → Descending r → den reduced unstable r
            descending→ : (m : Model) → Context (p m) → Descending (reduce m) →
              den full unstable m

        module _ (ob : Obligations) where
          open Obligations ob

          -- The descending branch of the reduction is unstable on both levels.
          descending-transfer : (m : Model) → Context (p m) → Descending (reduce m) →
            den reduced unstable (reduce m) × den full unstable m
          descending-transfer m c d = reduced-unstable (reduce m) d , descending→ m c d
