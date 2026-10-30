{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.ImplicitDiscretization where

-- Scaffold for continuous linear designs and implicit numerical implementations.
-- The implementation carrier Y is arbitrary: only its design and step projections are fixed.
-- The model keeps its arbitrary requirement language, satisfaction and translation; the
-- implementation lifts them and adds positive-step and well-posedness requirements.
-- Trapezoidal realization is exact under both constraints; backward Euler is sound under
-- positive steps, without claiming completeness. Constant-input implementations are read
-- in deviation coordinates about an actual equilibrium, with the same design projection.
-- Lean: theorem/Numerics/ImplicitRealization.lean supplies implicitFamily and
-- implicitRealization, trapezoidal_realizationExactUnder and
-- backwardEuler_realizationSoundUnder. theorem/Numerics/EMT/Plant.lean instantiates
-- these interfaces for RL/LCL designs and constant-input deviation implementations.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import theorem.FamilyReading
open import theorem.Realization

module _ (S : Semantics) where
  open Semantics S
  open Readings S
  open Realizations S

  module _ (model : Family) (Y Step : Type)
    (design : Y → Family.Model model) (step : Y → Step)
    (trapezoidal backwardEuler : Y → System)
    (positive : Step → Type) (trapWellPosed eulerWellPosed : Y → Type)
    (stable : Sentence)
    (Hurwitz : Family.Model model → Type) (TrapSchur EulerSchur : Y → Type)
    (continuous-reading : (m : Family.Model model) → den model stable m ↔ Hurwitz m)
    (trapezoidal-reading : (y : Y) → holds (trapezoidal y) stable ↔ TrapSchur y)
    (euler-reading : (y : Y) → holds (backwardEuler y) stable ↔ EulerSchur y)
    (cayley : (y : Y) → positive (step y) → trapWellPosed y →
      TrapSchur y ↔ Hurwitz (design y))
    (backward-sound : (y : Y) → positive (step y) → Hurwitz (design y) → EulerSchur y)
    where

    data Requirement : Type where
      from-design : Family.Req model → Requirement
      positive-step well-posed : Requirement

    translated : Sentence → Requirement → Type
    translated s (from-design q) = Family.translate model s q
    translated s positive-step = ⊥
    translated s well-posed = ⊥

    trapMeets : Y → Requirement → Type
    trapMeets y (from-design q) = Family.meets model (design y) q
    trapMeets y positive-step = positive (step y)
    trapMeets y well-posed = trapWellPosed y

    eulerMeets : Y → Requirement → Type
    eulerMeets y (from-design q) = Family.meets model (design y) q
    eulerMeets y positive-step = positive (step y)
    eulerMeets y well-posed = eulerWellPosed y

    trap : Family
    trap = record
      { Model = Y ; Req = Requirement ; system = trapezoidal
      ; meets = trapMeets ; translate = translated }

    backward : Family
    backward = record
      { Model = Y ; Req = Requirement ; system = backwardEuler
      ; meets = eulerMeets ; translate = translated }

    data TrapContext : Requirement → Type where
      positive-trap-required : TrapContext positive-step
      invertible-required : TrapContext well-posed

    data PositiveContext : Requirement → Type where
      positive-euler-required : PositiveContext positive-step

    trapezoidal-exact : (y : Y) → positive (step y) → trapWellPosed y →
      den trap stable y ↔ den model stable (design y)
    trapezoidal-exact y hp hw =
      (λ hi → snd (continuous-reading (design y))
        (fst (cayley y hp hw) (fst (trapezoidal-reading y) hi))) ,
      (λ hm → snd (trapezoidal-reading y)
        (snd (cayley y hp hw) (fst (continuous-reading (design y)) hm)))

    trapezoidal-exact-under : ExactUnder' (ofDesign model trap design) TrapContext stable
    trapezoidal-exact-under y hc =
      let reading = trapezoidal-exact y
            (hc positive-step positive-trap-required)
            (hc well-posed invertible-required)
      in ↔-trans (Design.certified↔ model trap design stable y) (snd reading , fst reading)

    backward-euler-sound : SoundUnder (ofDesign model backward design) PositiveContext stable
    backward-euler-sound y hc certified = snd (euler-reading y)
      (backward-sound y (hc positive-step positive-euler-required)
        (fst (continuous-reading (design y))
          (fst (Design.certified↔ model backward design stable y) certified)))
