{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFM.FullModel.FullModelTimeScale where
-- Lean modules: theorem.GridTiedConverter.GFM.FullModel.TimeScale theorem.GridTiedConverter.GFM.FullModel.Counterexample

-- Scaffold of the reading of the time-scaled 13-state grid-forming converter
-- (`GFM.FullModel.family` of `theorem/GridTiedConverter/GFM/FullModel/Saddle.lean`, at the
-- parameters `GFM.FullModel.Params.timeScaled ε`) through its quasi-steady reduction, the reduced
-- Q–V droop model (`GFM.QVDroop.family` of `theorem/GridTiedConverter/GFM/QVDroop.lean`). A
-- full-order model is a parameter set with a selected quasi-steady point `(δ*, Q*)`; its time
-- scaling (`timeScale`, Lean `GFM.FullModel.Model.timeScaled`) multiplies every electromagnetic
-- time constant by `ε` at fixed nominal-frequency impedances and divides the PI integral gains by
-- `ε`, so that its field is the `ε`-system (fast rows times `ε⁻¹`) in the coordinates
-- `(εξ, εζ)` (`GFM.FullModel.Params.timeScaled_field`); its reduction (`reduce`) is the droop
-- model `GFM.FullModel.Params.qvDroop` at the point `(δ*, 0, Q*)`, the same for every `ε`. The two
-- families have systems of different dimension (13 against 3 states), so the connection is not a
-- reading of systems: it compares, under the context (nondegenerate fast block, no virtual
-- impedance, spectrally stable boundary layer `GFM.FullModel.Params.fastBlock`), one sentence,
-- in one direction, for every small `ε`.
-- * Local exponential stability transfers from the reduction to the time-scaled full model
--   (`stable→`, Lean `GFM.FullModel.exists_epsStar_mem_den_LES_of_qvDroop`): local exponential
--   stability of the droop model makes its Jacobian Hurwitz (converse linearization), that
--   Jacobian is the Schur complement of the fast block of the full Jacobian on the quasi-steady
--   graph, and the two-time-scale law
--   `SingularPerturbation.exists_epsStar_locallyExponentiallyStable_of_graph` gives an `ε* > 0`
--   below which the `ε`-system, hence the time-scaled model, is locally exponentially stable.
-- * At fixed parameters the transfer fails, under the same context (`Refutation`, Lean
--   `GFM.FullModel.not_forall_mem_den_LES_of_reduced`): the explicit rational parameter set
--   `GFM.FullModel.witness` has a stable boundary layer
--   (`GFM.FullModel.witness_fastBlock_spectrallyStable`, a kernel-checked rational Lyapunov
--   certificate), a locally exponentially stable reduction
--   (`GFM.FullModel.witness_reduced_mem_den_LES`) and an unstable full model at the same point
--   (`GFM.FullModel.witness_mem_den_unstable`: the characteristic determinant of the full Jacobian
--   is nonpositive at `s = 2`, so it has a real eigenvalue `μ ≥ 2`). Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics using (Scalars)

module _ (Sc : Scalars) where
  open Scalars Sc

  module _ (Params : Type)
    -- The time scaling of a parameter set (Lean `GFM.FullModel.Params.timeScaled`).
    (timeScaled : Params → ℝ → Params)
    -- The reduced droop models (Lean `GFM.QVDroop.Model`) and the reduction of a parameter set at
    -- a selected point `(δ*, Q*)` (Lean `GFM.FullModel.Params.qvDroop`).
    (DroopModel : Type) (toDroop : Params → ℝ → ℝ → DroopModel)
    -- The context: nondegenerate fast block, no virtual impedance, stable boundary layer.
    (Context : Params → ℝ → Type)
    where

    -- A full-order model: parameters and a selected quasi-steady point `(δ*, Q*)`.
    record Model : Type where
      constructor model
      field
        p : Params
        δ Qf : ℝ

    open Model

    -- The time-scaled model at the same point.
    timeScale : Model → ℝ → Model
    timeScale m ε = model (timeScaled (p m) ε) (δ m) (Qf m)

    -- The reduction: the droop model of the parameters at the same point.
    reduce : Model → DroopModel
    reduce m = toDroop (p m) (δ m) (Qf m)

    module _ (S : Semantics) where
      open Semantics S
      open Readings S

      module _
        -- Local exponential stability. Each family keeps its own requirement language and
        -- translation (left empty here); the comparison reads the reduced sentence directly.
        (stable unstable : Sentence) (fullSystem : Model → System)
        (droopSystem : DroopModel → System)
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
            stable→ : (m : Model) → Context (p m) (δ m) → den reduced stable (reduce m) →
              Σ ℝ λ εs → (0r < εs) ×
                ((ε : ℝ) → 0r < ε → ε < εs → den full stable (timeScale m ε))

        module _ (ob : Obligations) where
          open Obligations ob

          -- A stable reduction stays stable in every sufficiently time-scaled full model.
          stable-transfer : (m : Model) → Context (p m) (δ m) → den reduced stable (reduce m) →
            Σ ℝ λ εs → (0r < εs) ×
              ((ε : ℝ) → 0r < ε → ε < εs → den full stable (timeScale m ε))
          stable-transfer = stable→

        -- What Lean proves at fixed parameters: a model in the context of `stable→` (stable
        -- boundary layer included) with a stable reduction and an unstable full model.
        record Refutation : Type where
          field
            witness : Model
            witness-context : Context (p witness) (δ witness)
            reduced-stable : den reduced stable (reduce witness)
            full-unstable : den full unstable witness

        module _ (rf : Refutation) where
          open Refutation rf

          -- The witness: the context and both sentences at once.
          no-fixed-transfer : Context (p witness) (δ witness) ×
            (den reduced stable (reduce witness) × den full unstable witness)
          no-fixed-transfer = witness-context , (reduced-stable , full-unstable)
