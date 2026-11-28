{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.PowerSystem.Synchronous.OneAxisLinearization where
-- Lean modules: theorem.PowerSystem.Synchronous.OneAxis

-- Scaffold of the connection of the nonlinear one-axis machine on an infinite bus with its
-- Heffron–Phillips linearization (`Synchronous.OneAxis.family` of
-- `theorem/PowerSystem/Synchronous/OneAxis.lean` and `Synchronous.FluxDecay.family` of
-- `theorem/PowerSystem/Synchronous/FluxDecay.lean`). A one-axis model is a machine with a selected
-- point `(δ*, 0, E'_q*)`; its linearization (`Synchronous.OneAxis.Model.linearization`) is the
-- flux-decay machine whose coefficients `K₁ … K₄` are the partial derivatives of the torque and the
-- field EMF at `(δ*, E'_q*)` (`Synchronous.OneAxis.Machine.hasFDerivAt_field`: the Jacobian of the
-- field is the Heffron–Phillips state matrix). The two families have the same state dimension but
-- are not a reading of one another: the nonlinear machine is read on its field at the selected
-- point, the linearization on its plant, and their sentences agree only where the linearization
-- decides the nonlinear one. The connection compares denotations: at an equilibrium
-- (`Equilibrium`: torque and field-EMF balance), local exponential stability of the machine is
-- equivalent to the Hurwitz property of the linearization (`les-hurwitz`, converse linearization),
-- hence to every Hurwitzian sentence of the linearization (`les-reading`); an equilibrium whose
-- linearization meets the instability requirement (a strict violation of a Routh condition) is
-- unstable (`unstable-transfer`); without damping, in the normal operating range, local
-- exponential stability is the positivity of the steady-state synchronizing coefficient
-- (`undamped-reading`, through the flux-decay family's own law `undamped-law`). Off an
-- equilibrium the machine is unstable whatever its linearization (Lean
-- `Synchronous.OneAxis.mem_den_unstable_of_not_equilibrium`, a law of the one-axis family alone).
-- Lean: `les-hurwitz` is `Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian` with
-- `Synchronous.OneAxis.Model.fderiv_point` and `Synchronous.OneAxis.Model.field_point_eq_zero_iff`;
-- `flux-linear` is `Family.IsLinear.mem_den_hurwitz` (`Synchronous.FluxDecay.family_isLinear`);
-- `les-reading` is `Synchronous.OneAxis.mem_den_locallyExponentiallyStable_iff_linearization`;
-- `root-unstable` is `Synchronous.FluxDecay.exists_root_of_unstable` with
-- `Dynamics.unstable_of_characteristic_root_re_pos`, and `unstable-transfer` is
-- `Synchronous.OneAxis.mem_den_unstable_of_linearization`; `undamped-law` is
-- `Synchronous.FluxDecay.mem_den_undamped_iff`, `normal-range` is
-- `Synchronous.OneAxis.Machine.K₂_pos` with `Synchronous.OneAxis.Machine.K₄_pos`, and
-- `undamped-reading` is `Synchronous.OneAxis.mem_den_undamped_iff`. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics using (Scalars)

module _ (Sc : Scalars) where
  open Scalars Sc

  module Linearization (S : Semantics)
    -- One-axis models (machine and selected point) and flux-decay machines.
    (OneAxisModel FluxMachine : Type)
    -- The linearization at the selected point.
    (linearization : OneAxisModel → FluxMachine)
    -- Torque and field-EMF balance at the selected point; the normal operating range
    -- (`0 < δ* < π`, `V > 0`, `X_d > X'_d`).
    (Equilibrium NormalRange : OneAxisModel → Type)
    -- The flux-decay coefficients read on a flux-decay machine.
    (D K₁ K₂ K₃ K₄ : FluxMachine → ℝ)
    where
    open Semantics S
    open Readings S

    module _
      -- The Hurwitzian sentences, local exponential stability, instability.
      (Hurwitzian : Sentence → Type) (les unstable : Sentence)
      -- The fields at the selected points, the plants of the linearizations.
      (oneAxisSystem : OneAxisModel → System) (fluxSystem : FluxMachine → System)
      -- The Hurwitz property of a flux-decay plant, and the instability requirement of the
      -- flux-decay family (a strict violation of a Routh condition).
      (HurwitzF RouthViolated : FluxMachine → Type)
      where

      oneAxis flux : Family
      oneAxis = record
        { Model = OneAxisModel ; Req = ⊥ ; system = oneAxisSystem ; meets = λ _ ()
        ; translate = λ _ () }
      flux = record
        { Model = FluxMachine ; Req = ⊥ ; system = fluxSystem ; meets = λ _ ()
        ; translate = λ _ () }

      -- What Lean proves.
      record Obligations : Type where
        field
          les-hurwitzian : Hurwitzian les
          les-hurwitz : (x : OneAxisModel) →
            den oneAxis les x ↔ (Equilibrium x × HurwitzF (linearization x))
          flux-linear : (s : Sentence) → Hurwitzian s → (y : FluxMachine) →
            den flux s y ↔ HurwitzF y
          root-unstable : (x : OneAxisModel) → Equilibrium x →
            RouthViolated (linearization x) → den oneAxis unstable x
          undamped-law : (y : FluxMachine) → D y ≡ 0r →
            den flux les y ↔ ((0r < K₂ y * K₄ y) × (K₂ y * K₃ y * K₄ y < K₁ y))
          normal-range : (x : OneAxisModel) → NormalRange x →
            0r < K₂ (linearization x) * K₄ (linearization x)

      module _ (ob : Obligations) where
        open Obligations ob

        -- At an equilibrium, local exponential stability of the machine is every Hurwitzian
        -- sentence of its linearization.
        les-reading : (x : OneAxisModel) → Equilibrium x → (s : Sentence) → Hurwitzian s →
          den oneAxis les x ↔ den flux s (linearization x)
        les-reading x e s h =
          (λ d → snd (flux-linear s h (linearization x)) (snd (fst (les-hurwitz x) d)))
          , (λ d → snd (les-hurwitz x) (e , fst (flux-linear s h (linearization x)) d))

        -- An equilibrium whose linearization violates a Routh condition strictly is unstable.
        unstable-transfer : (x : OneAxisModel) → Equilibrium x →
          RouthViolated (linearization x) → den oneAxis unstable x
        unstable-transfer = root-unstable

        -- Without damping, in the normal range: the steady-state synchronizing coefficient.
        undamped-reading : (x : OneAxisModel) → Equilibrium x → NormalRange x →
          D (linearization x) ≡ 0r →
          den oneAxis les x ↔
            (K₂ (linearization x) * K₃ (linearization x) * K₄ (linearization x)
              < K₁ (linearization x))
        undamped-reading x e n d =
          (λ h → snd (fst (undamped-law (linearization x) d)
            (fst (les-reading x e les les-hurwitzian) h)))
          , (λ k → snd (les-reading x e les les-hurwitzian)
            (snd (undamped-law (linearization x) d) (normal-range x n , k)))
