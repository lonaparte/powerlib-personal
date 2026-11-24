{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFM.FullModel.FullModelSwing where
-- Lean modules: theorem.GridTiedConverter.GFM.FullModel.Basic theorem.GridTiedConverter.GFM.FullModel.Saddle theorem.GridTiedConverter.GFM.FullModel.Equilibria

-- Scaffold of the reading of the 13-state grid-forming converter (`GFM.FullModel.family` of
-- `theorem/GridTiedConverter/GFM/FullModel/Saddle.lean`) through its quasi-steady reduction, the
-- swing machine of the swing hub (`Synchronous.Swing.family`). A full-order model is a parameter
-- set with a selected quasi-steady point `(δ*, Q*)`; its reduction (`reduce`) is the swing machine
-- `GFM.FullModel.Params.swingParams` at the same angle: without droop and virtual impedance the
-- angle rows of the reduced field — the slow rows of the 13-state field on its quasi-steady set —
-- are the swing field (`GFM.FullModel.Params.reducedField_eq_swing`,
-- `GFM.FullModel.Params.Pq_eq_swing`), and the slope of the quasi-steady power–angle curve is the
-- swing synchronizing coefficient (`GFM.FullModel.Params.powerSlope_eq_syncCoeff`). The two
-- families have systems of different dimension (13 against 2 states), so the connection is not a
-- reading of systems: it compares, under the context (nondegenerate fast block, no droop, no
-- virtual impedance, positive inertia and reactive-filter bandwidth), the equilibria and one
-- sentence, in one direction.
-- * Equilibria: a selected point is an equilibrium of the full model exactly when its reduction
--   is balanced and the reactive-power filter sits at the quasi-steady reactive power
--   (`GFM.FullModel.Params.field_eq_zero_iff`); an equilibrium exists exactly when the swing
--   machine has one (`GFM.FullModel.Params.exists_equilibrium_iff`, read from
--   `Synchronous.SwingParams.exists_equilibrium_iff`). Per period window of the angle the
--   equilibria of the full model are the lifts of those of the swing machine
--   (`GFM.FullModel.Params.lift`, `GFM.FullModel.Params.equilibria_window`), so the reduced counts
--   carry over: two at `|P_ref − c₀| < A`, one at the fold
--   (`GFM.FullModel.Params.two_equilibria_per_period`,
--   `GFM.FullModel.Params.fold_equilibrium_per_period`, read from
--   `GFM.Reduced.two_equilibria_per_period`, `GFM.Reduced.fold_equilibrium_per_period`).
-- * Instability transfers from the saddle branch of the reduction to the full model, for every
--   choice of the controller gains (`saddle→`, Lean `GFM.FullModel.mem_den_unstable_of_swing`): at
--   a balanced angle with negative synchronizing coefficient the Jacobian determinant of the full
--   field is the positive determinant of the fast block times the determinant of the reduced
--   Jacobian (`GFM.FullModel.Params.det_jacobian_qssState`, the generic Schur law
--   `LinearAlgebra.det_eq_det_fast_mul_det_reduced`, `GFM.FullModel.Params.det_fastBlock_pos`).
--   With Q–V droop the full model alone states the same instability under a negative
--   droop-corrected slope (`GFM.FullModel.mem_den_unstable`); the swing reading needs no droop.
-- * The local stability sentences are not compared here: the full family translates them into a
--   requirement no model meets, and stability of the reduced stable branch is not a statement about
--   the full model at fixed parameters (`GFM.FullModel.witness_mem_den_unstable`); its transfer to
--   time-scaled parameters is `GFM.FullModel.exists_epsStar_mem_den_LES_of_swing`. Nothing here is
--   exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics using (Scalars)
open import theorem.PowerSystem.Synchronous.Swing

module _ (Sc : Scalars) where
  open Scalars Sc
  open SwingContent Sc
  open SwingParams

  module _ (Params : Type)
    -- The reduced swing machine of a parameter set (Lean `GFM.FullModel.Params.swingParams`).
    (toSwingParams : Params → SwingParams)
    -- The context: nondegenerate fast block, no droop, no virtual impedance, `M, ω_q > 0`.
    (Context : Params → Type)
    -- The reactive-power filter at the quasi-steady reactive power of the angle.
    (ReactiveAtRest : Params → ℝ → ℝ → Type)
    where

    -- A full-order model: parameters and a selected quasi-steady point `(δ*, Q*)`.
    record Model : Type where
      constructor model
      field
        p : Params
        δ Qf : ℝ

    open Model

    -- The reduction: the swing machine of the parameters at the same angle.
    reduce : Model → SwingModel
    reduce m = swingModel (toSwingParams (p m)) (δ m)

    -- The saddle branch of the reduction: balanced, negative synchronizing coefficient.
    Saddle : SwingModel → Type
    Saddle r = swingMeets r balanced × (syncCoeff (SwingModel.p r) (SwingModel.δ r) < 0r)

    module _ (S : Semantics) where
      open Semantics S
      open Readings S

      module _
        -- Instability, and the equilibrium property of a field at its selected point. Each family
        -- keeps its own requirement language and translation (left empty here); the comparison
        -- reads the swing requirements `balanced` and the synchronizing coefficient directly.
        (unstable : Sentence) (Equilibrium : System → Type)
        (fullSystem : Model → System) (swingSys : SwingModel → System)
        where

        full reduced : Family
        full = record
          { Model = Model ; Req = ⊥ ; system = fullSystem ; meets = λ _ () ; translate = λ _ () }
        reduced = record
          { Model = SwingModel ; Req = ⊥ ; system = swingSys ; meets = λ _ ()
          ; translate = λ _ () }

        -- What Lean proves.
        record Obligations : Type where
          field
            equilibrium↔ : (m : Model) → Context (p m) → Equilibrium (fullSystem m) ↔
              (swingMeets (reduce m) balanced × ReactiveAtRest (p m) (δ m) (Qf m))
            saddle→ : (m : Model) → Context (p m) → ReactiveAtRest (p m) (δ m) (Qf m) →
              Saddle (reduce m) → den full unstable m

        module _ (ob : Obligations) where
          open Obligations ob

          -- The saddle equilibria of the reduction are unstable equilibria of the full model.
          saddle-transfer : (m : Model) → Context (p m) → ReactiveAtRest (p m) (δ m) (Qf m) →
            Saddle (reduce m) → Equilibrium (fullSystem m) × den full unstable m
          saddle-transfer m c q s = snd (equilibrium↔ m c) (fst s , q) , saddle→ m c q s
