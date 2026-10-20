{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.MatchingSwing where

-- Scaffold of the reading of the swing family of matching control through the swing hub
-- (`GFM.Matching.swingFamily` of `theorem/GFM/Matching/Matching.lean` read through
-- `Synchronous.Swing.family`). The matching swing model `M θ̈ + D θ̇ = τ − P_e(θ, θ̇)` has an
-- arbitrary power law, which may depend on the speed (the matched law `i_x(θ, ω/η)/η` does when the
-- load current depends on the DC voltage), and a free selected speed `ω*`; so it stays a family of
-- its own and reads through the hub only on a context: a speed-independent sinusoidal law
-- `P_e(θ, ω) = k₁ + k₂ sin(θ − k₃)` and `ω* = 0`. There it is the swing machine
-- `⟨M, D, τ, k₁, k₂, k₃⟩` at `θ*`, with the same field, so the reading is an equality of systems on
-- every sentence. The matching swing family has no satisfiable requirement (both conditions of its
-- language are empty), so nothing carries over by `exactUnder-pullback`; the hub supplies the
-- denotations themselves: with positive inertia, local exponential stability is the swing
-- conditions of the image (`les↔`). Lean proves the reading
-- (`GFM.Matching.swing_mem_den_iff_hub_of_sinusoid`) and the characterization
-- (`GFM.Matching.swing_mem_den_locallyExponentiallyStable_iff_of_sinusoid`, through
-- `Synchronous.Swing.exactUnder_locallyExponentiallyStable`). Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import theorem.FamilyReading
open import theorem.FlowSemantics
open import theorem.Swing

module _ (Sc : Scalars) where
  open Scalars Sc
  open SwingContent Sc

  record MatchingSwingModel : Type where
    constructor matchingSwingModel
    field
      M D τ : ℝ
      law : ℝ → ℝ → ℝ
      θ ω : ℝ

  open MatchingSwingModel

  mField : MatchingSwingModel → ℝ × ℝ → ℝ × ℝ
  mField m (x , v) = v , ((τ m - law m x v) - D m * v) / M m

  mSystem : MatchingSwingModel → System (ℝ × ℝ)
  mSystem m = mField m , (θ m , ω m)

  -- The coefficients of a sinusoidal law.
  record Sinusoid : Type where
    constructor sinusoid
    field
      c₁ c₂ c₃ : ℝ

  open Sinusoid

  -- The context: the law is the sinusoid `k` (independent of the speed) and `ω* = 0`.
  SinusoidalAt : Sinusoid → MatchingSwingModel → Type
  SinusoidalAt k m = (law m ≡ (λ x _ → c₁ k + c₂ k * sin (x - c₃ k))) × (ω m ≡ 0r)

  toSwing : Sinusoid → MatchingSwingModel → SwingModel
  toSwing k m = swingModel (swingParams (M m) (D m) (τ m) (c₁ k) (c₂ k) (c₃ k)) (θ m)

  module Reading (holds : System (ℝ × ℝ) → Sentence → Type)
    (invariant : (A : Affine (ℝ × ℝ)) (a : System (ℝ × ℝ)) (s : Sentence) →
      holds (transportSystem A a) s ≃ holds a s)
    (laws : SwingFamily.SwingLaws holds invariant)
    (Req : Type) (meets : MatchingSwingModel → Req → Type) (translate : Sentence → Req → Type)
    (k : Sinusoid)
    where

    open SwingFamily holds invariant

    matchingSwingFamily : Family
    matchingSwingFamily = record
      { Model = MatchingSwingModel ; Req = Req ; system = mSystem ; meets = meets
      ; translate = translate }

    -- What Lean proves by field algebra.
    module _ (sameField : (m : MatchingSwingModel) → SinusoidalAt k m →
               mSystem m ≡ swingSystem (toSwing k m)) where

      sinusoidal : Family
      sinusoidal = restrictBy matchingSwingFamily (SinusoidalAt k)

      reading : Hub sinusoidal swingFamily
      reading = viaEquality (λ x → toSwing k (fst x)) (λ x → sameField (fst x) (snd x))

      -- On the context, the sentences of a model are those of its image
      -- (`swing_mem_den_iff_hub_of_sinusoid`).
      den↔ : (m : MatchingSwingModel) → SinusoidalAt k m → (s : Sentence) →
        den matchingSwingFamily s m ↔ den swingFamily s (toSwing k m)
      den↔ m c s = ↔-of-≃ (Hub.read reading (m , c) s)

      -- With positive inertia, local exponential stability is the swing conditions of the image
      -- (`swing_mem_den_locallyExponentiallyStable_iff_of_sinusoid`).
      les↔ : (m : MatchingSwingModel) → SinusoidalAt k m → 0r < M m →
        den matchingSwingFamily locallyExponentiallyStable m ↔
          realize swingFamily swingLocal (toSwing k m)
      les↔ m c hM =
        let h = SwingFamily.SwingLaws.exactUnder-les laws (toSwing k m)
                  (λ r e → subst (swingMeets (toSwing k m)) (sym e) hM)
        in ↔-trans (den↔ m c locallyExponentiallyStable) (snd h , fst h)
