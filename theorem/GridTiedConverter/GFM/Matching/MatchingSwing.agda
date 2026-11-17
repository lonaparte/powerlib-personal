{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFM.Matching.MatchingSwing where
-- Lean modules: theorem.GridTiedConverter.GFM.Matching.Matching

-- Scaffold of the reading of matching control through the swing family with an arbitrary law
-- (`GFM.Matching.matchingFamily` of `theorem/GridTiedConverter/GFM/Matching/Matching.lean` read
-- through `Synchronous.GeneralSwing.family`, `theorem/PowerSystem/Synchronous/GeneralSwing.agda`).
-- The matching model `θ' = η v`, `C v' = i_dc − i_x(θ, v) − G v` has an arbitrary load-current
-- law and a free selected point `(θ*, v*)` (`C, η ≠ 0`, carried by the Lean model). In the
-- coordinates `(θ, η v)` (`Dynamics.scaleCoord`, `scaleCoords`) it is, for every model and every
-- sentence, the swing model `M = C/η²`, `D = G/η²`, `τ = i_dc/η`, `P_e(θ, ω) = i_x(θ, ω/η)/η` at
-- `(θ*, η v*)` (`toGeneral`): the reading is a conjugacy, not on a context. The matched law depends
-- on the speed whenever the load current depends on the DC voltage, so matching control reads
-- through the swing family with an arbitrary law, and through the swing hub only where that family
-- does: on a speed-independent sinusoidal law with `ω* = 0` (`compose` with `hubReading`). Like the
-- general family, the matching family has no satisfiable requirement (both conditions of its
-- language are empty); its content is its semantics. Lean: `conjugate` is
-- `GFM.Matching.matching_eq_swing` (read by `Dynamics.holds_transport_iff`), `den↔` is
-- `GFM.Matching.matching_den_eq`; the composite with the hub on a sinusoid is the step of
-- `GFM.Matching.matching_not_euler_realizationSoundUnder` through
-- `Synchronous.GeneralSwing.mem_den_locallyExponentiallyStable_iff_of_sinusoid`. Nothing here is
-- exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics
open import theorem.PowerSystem.Synchronous.Swing
open import theorem.PowerSystem.Synchronous.GeneralSwing

module _ (Sc : Scalars) where
  open Scalars Sc
  open SwingContent Sc
  open GeneralSwingContent Sc

  -- A matching model with a selected point `(θ*, v*)`.
  record MatchingModel : Type where
    constructor matchingModel
    field
      C G η idc : ℝ
      ix : ℝ → ℝ → ℝ
      θ v : ℝ

  open MatchingModel

  matchingField : MatchingModel → ℝ × ℝ → ℝ × ℝ
  matchingField m (x , u) = η m * u , ((idc m - ix m x u) - G m * u) / C m

  matchingSystem : MatchingModel → System (ℝ × ℝ)
  matchingSystem m = matchingField m , (θ m , v m)

  -- The coordinates `(θ, v) ↦ (θ, η v)`, their inverse and their linear part.
  scaleCoords : MatchingModel → Affine (ℝ × ℝ)
  scaleCoords m = record
    { point = λ { (x , u) → x , η m * u }
    ; pointInv = λ { (x , w) → x , w / η m }
    ; vector = λ { (a , b) → a , η m * b } }

  -- The matched swing model with an arbitrary law at `(θ*, η v*)`.
  toGeneral : MatchingModel → GeneralModel
  toGeneral m = generalModel (C m / (η m * η m)) (G m / (η m * η m)) (idc m / η m)
    (λ x w → ix m x (w / η m) / η m) (θ m) (η m * v m)

  module Reading (holds : System (ℝ × ℝ) → Sentence → Type)
    (invariant : (A : Affine (ℝ × ℝ)) (a : System (ℝ × ℝ)) (s : Sentence) →
      holds (transportSystem A a) s ≃ holds a s)
    where

    open GeneralSwingFamily holds invariant

    -- The matching family: the language of the general family, met by no model.
    matchingFamily : Family
    matchingFamily = record
      { Model = MatchingModel ; Req = GeneralReq ; system = matchingSystem
      ; meets = λ _ _ → ⊥ ; translate = generalTranslate }

    -- What Lean proves by field algebra (with `C, η ≠ 0`, carried by the model).
    module _ (conjugate : (m : MatchingModel) →
               generalSystem (toGeneral m) ≡ transportSystem (scaleCoords m) (matchingSystem m))
      where

      matched : Hub matchingFamily generalFamily
      matched = record
        { map = toGeneral
        ; read = λ m s → invEquiv (conjugateReading affine (scaleCoords m) (conjugate m) s) }

      -- Every sentence of a matching model is the sentence of its matched swing model.
      den↔ : (m : MatchingModel) (s : Sentence) →
        den matchingFamily s m ↔ den generalFamily s (toGeneral m)
      den↔ m s = ↔-of-≃ (Hub.read matched m s)

      -- On a sinusoidal matched law, through the swing hub.
      hub↔ : (hubField : (k₁ k₂ k₃ : ℝ) (g : GeneralModel) → SinusoidalLaw k₁ k₂ k₃ g →
               generalSystem g ≡ swingSystem (toHub k₁ k₂ k₃ g))
        (k₁ k₂ k₃ : ℝ) (m : MatchingModel) (c : SinusoidalLaw k₁ k₂ k₃ (toGeneral m))
        (s : Sentence) → den matchingFamily s m ↔ den swingFamily s (toHub k₁ k₂ k₃ (toGeneral m))
      hub↔ hubField k₁ k₂ k₃ m c s =
        ↔-trans (den↔ m s) (general-den↔ hubField k₁ k₂ k₃ (toGeneral m) c s)
