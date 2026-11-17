{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.PowerSystem.Synchronous.GeneralSwing where
-- Lean modules: theorem.PowerSystem.Synchronous.GeneralSwing

-- Scaffold of the swing family with an arbitrary power law (`Synchronous.GeneralSwing.family` of
-- `theorem/PowerSystem/Synchronous/GeneralSwing.lean`) and of its reading through the swing hub
-- (`Synchronous.Swing.family`, `theorem/PowerSystem/Synchronous/Swing.agda`). The model
-- `M θ̈ + D θ̇ = τ − P_e(θ, θ̇)` has an arbitrary law, which may depend on the speed, and a free
-- selected point `(θ*, ω*)`; its requirement language is that of a local spectral family with
-- both conditions empty (Lean `Spectral.localFamily`), so no model meets a requirement, every flow
-- translation is sound (`general-sound`) and the content of the family is its semantics. It reads
-- through the hub only on a context: a speed-independent sinusoidal law
-- `P_e(θ, ω) = k₁ + k₂ sin(θ − k₃)` and `ω* = 0`. There it is the swing machine
-- `⟨M, D, τ, k₁, k₂, k₃⟩` at `θ*`, with the same field, so the reading is an equality of systems on
-- every sentence (`general-den↔`). Nothing carries over by `exactUnder-pullback`; the hub supplies
-- the denotations themselves: with positive inertia, local exponential stability is the swing
-- conditions of the image (`general-les↔`). Its spokes are matching control
-- (`theorem/GridTiedConverter/GFM/Matching/MatchingSwing.agda`, by a change of coordinates) and the
-- VSM with an arbitrary power map (`theorem/GridTiedConverter/GFM/VSMSwing.agda`, by an equality of
-- systems), which compose their readings with `hubReading` on the context (`compose`). Lean:
-- `general-sound` is `Synchronous.GeneralSwing.chain_le_semantics` (passivity there from the
-- absent port), `hubField` is the field identity in the proof of
-- `Synchronous.GeneralSwing.mem_den_iff_hub_of_sinusoid`, `general-den↔` is that theorem and
-- `general-les↔` is `Synchronous.GeneralSwing.mem_den_locallyExponentiallyStable_iff_of_sinusoid`
-- (through `Synchronous.Swing.exactUnder_locallyExponentiallyStable`). Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥; rec)

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics
open import theorem.PowerSystem.Synchronous.Swing

module GeneralSwingContent (Sc : Scalars) where
  open Scalars Sc
  open SwingContent Sc

  -- A swing model with an arbitrary law and a selected point `(θ*, ω*)`.
  record GeneralModel : Type where
    constructor generalModel
    field
      M D τ : ℝ
      law : ℝ → ℝ → ℝ
      θ ω : ℝ

  open GeneralModel

  generalField : GeneralModel → ℝ × ℝ → ℝ × ℝ
  generalField m (x , v) = v , ((τ m - law m x v) - D m * v) / M m

  generalSystem : GeneralModel → System (ℝ × ℝ)
  generalSystem m = generalField m , (θ m , ω m)

  -- The language of a local spectral family (Lean `Spectral.Requirement`,
  -- `Spectral.localTranslate`) with both conditions empty.
  data GeneralReq : Type where
    stable unstable : GeneralReq

  generalMeets : GeneralModel → GeneralReq → Type
  generalMeets _ _ = ⊥

  noGeneral : GeneralReq → Type
  noGeneral _ = ⊥

  generalTranslate : Sentence → GeneralReq → Type
  generalTranslate = localTable (only stable) (only stable) (only unstable) noGeneral

  -- The context: the law is the sinusoid `(k₁, k₂, k₃)`, independent of the speed, and `ω* = 0`.
  SinusoidalLaw : ℝ → ℝ → ℝ → GeneralModel → Type
  SinusoidalLaw k₁ k₂ k₃ m = (law m ≡ (λ x _ → k₁ + k₂ * sin (x - k₃))) × (ω m ≡ 0r)

  -- The hub image: the swing machine `⟨M, D, τ, k₁, k₂, k₃⟩` at `θ*`.
  toHub : ℝ → ℝ → ℝ → GeneralModel → SwingModel
  toHub k₁ k₂ k₃ m = swingModel (swingParams (M m) (D m) (τ m) k₁ k₂ k₃) (θ m)

  module GeneralSwingFamily (holds : System (ℝ × ℝ) → Sentence → Type)
    (invariant : (A : Affine (ℝ × ℝ)) (a : System (ℝ × ℝ)) (s : Sentence) →
      holds (transportSystem A a) s ≃ holds a s)
    where

    open SwingFamily holds invariant public

    generalFamily : Family
    generalFamily = record
      { Model = GeneralModel ; Req = GeneralReq ; system = generalSystem ; meets = generalMeets
      ; translate = generalTranslate }

    -- No model meets a requirement: every flow translation is sound.
    general-sound : (s : Sentence) → Flow s → Sound generalFamily s
    general-sound lyapunovStable _ m h = rec (h stable refl)
    general-sound locallyAsymptoticallyStable _ m h = rec (h stable refl)
    general-sound locallyExponentiallyStable _ m h = rec (h stable refl)
    general-sound unstable _ m h = rec (h unstable refl)
    general-sound global _ m h = rec (h stable tt)
    general-sound passive ()

    -- What Lean proves by field algebra.
    module _ (hubField : (k₁ k₂ k₃ : ℝ) (m : GeneralModel) → SinusoidalLaw k₁ k₂ k₃ m →
               generalSystem m ≡ swingSystem (toHub k₁ k₂ k₃ m)) where

      generalSinusoidal : ℝ → ℝ → ℝ → Family
      generalSinusoidal k₁ k₂ k₃ = restrictBy generalFamily (SinusoidalLaw k₁ k₂ k₃)

      hubReading : (k₁ k₂ k₃ : ℝ) → Hub (generalSinusoidal k₁ k₂ k₃) swingFamily
      hubReading k₁ k₂ k₃ = viaEquality (λ x → toHub k₁ k₂ k₃ (fst x))
        (λ x → hubField k₁ k₂ k₃ (fst x) (snd x))

      -- On the context, the sentences of a model are those of its hub image
      -- (`mem_den_iff_hub_of_sinusoid`).
      general-den↔ : (k₁ k₂ k₃ : ℝ) (m : GeneralModel) → SinusoidalLaw k₁ k₂ k₃ m →
        (s : Sentence) → den generalFamily s m ↔ den swingFamily s (toHub k₁ k₂ k₃ m)
      general-den↔ k₁ k₂ k₃ m c s = ↔-of-≃ (Hub.read (hubReading k₁ k₂ k₃) (m , c) s)

      -- With positive inertia, local exponential stability is the swing conditions of the image
      -- (`mem_den_locallyExponentiallyStable_iff_of_sinusoid`).
      general-les↔ : (laws : SwingLaws) (k₁ k₂ k₃ : ℝ) (m : GeneralModel) →
        SinusoidalLaw k₁ k₂ k₃ m → 0r < M m →
        den generalFamily locallyExponentiallyStable m ↔
          realize swingFamily swingLocal (toHub k₁ k₂ k₃ m)
      general-les↔ laws k₁ k₂ k₃ m c hM =
        let h = SwingLaws.exactUnder-les laws (toHub k₁ k₂ k₃ m)
                  (λ r e → subst (swingMeets (toHub k₁ k₂ k₃ m)) (sym e) hM)
        in ↔-trans (general-den↔ k₁ k₂ k₃ m c locallyExponentiallyStable) (snd h , fst h)
