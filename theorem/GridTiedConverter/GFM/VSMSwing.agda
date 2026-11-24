{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFM.VSMSwing where
-- Lean modules: theorem.GridTiedConverter.GFM.DroopVSM

-- Scaffold of the reading of the VSM family with an arbitrary power map through the swing family
-- with an arbitrary law and, on a context, through the swing hub (`GFM.DroopVSM.vsmFamily` of
-- `theorem/GridTiedConverter/GFM/DroopVSM.lean` read through `Synchronous.GeneralSwing.family`,
-- `theorem/PowerSystem/Synchronous/GeneralSwing.agda`, and through `Synchronous.Swing.family`).
-- The VSM model `θ̇ = ω`, `M ω̇ = P_ref − P(θ) − D (ω − ω_s)` has an arbitrary power map `P`, a
-- frame speed `ω_s` and a free selected state `x* = (θ*, ω*)`. For every model it is the swing
-- model `⟨M, D, P_ref + D ω_s, P(θ), θ*, ω*⟩` with an arbitrary (here speed-independent) law
-- (`toGeneral`; the damping reference `ω_s` shifts the driving power), with the same field, so the
-- reading is an equality of systems on every sentence and the VSM family's denotations are the
-- general family's pulled back (`vsm-den-eq-preimage`). It keeps its own requirement language,
-- since the general family has none. Composed with the hub reading of the general family on its
-- sinusoidal context (`hubReading`, `compose`): on a sinusoidal power curve
-- `P(θ) = k₁ + k₂ sin(θ − k₃)` and `ω* = 0`, in any rotating frame, a model is the swing machine
-- `⟨M, D, P_ref + D ω_s, k₁, k₂, k₃⟩` at `θ*` on every sentence (`den↔`); on an infinite bus in the
-- synchronous frame (`P = K₀ sin`, `ω_s = 0`) the image is `⟨M, D, P_ref, 0, K₀, 0⟩`
-- (`den↔-bus`). No correspondence of the requirement languages is stated, so nothing passes by
-- `exactUnder-pullback`: the VSM family keeps its own laws, which hold for an arbitrary `C¹` power
-- map, outside the hub. The scaffold also fixes the VSM family (`VSMContent`,
-- `VSMReading.vsmFamily`) through which `theorem/GridTiedConverter/GFM/DroopVSM.agda` reads the
-- droop + LPF loop and in which `theorem/GridTiedConverter/GFM/Tracking/GridFrame.agda` places the
-- loop read in the frame of a grid at a constant frequency offset. Lean: `sameGeneral` is
-- `GFM.DroopVSM.VSMModel.field_eq_toSwing`, `vsm-den-eq-preimage` is
-- `GFM.DroopVSM.vsm_den_eq_preimage`, `hubField` is the field identity of
-- `Synchronous.GeneralSwing.mem_den_iff_hub_of_sinusoid`, `den↔` is
-- `GFM.DroopVSM.vsm_mem_den_iff_swing_of_sinusoid` (the composite), `busSinusoid` and `busImage`
-- its instance `k₁ = k₃ = 0`, `ω_s = 0`, `den↔-bus` the same theorem there. The VSM family's own
-- laws are `GFM.DroopVSM.vsmFamily_chain_le_semantics` and
-- `GFM.DroopVSM.vsm_mem_den_locallyExponentiallyStable`. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics
open import theorem.PowerSystem.Synchronous.Swing
open import theorem.PowerSystem.Synchronous.GeneralSwing

module VSMContent (Sc : Scalars) where
  open Scalars Sc
  open SwingContent Sc
  open GeneralSwingContent Sc

  -- A VSM closed loop with an arbitrary power map, read about a selected state `x*`.
  record VSMModel : Type where
    constructor vsmModel
    field
      M D Pref ωs : ℝ
      P : ℝ → ℝ
      x* : ℝ × ℝ

  open VSMModel

  -- The field in the coordinates `(θ, ω)` and the selected state.
  vsmField : VSMModel → ℝ × ℝ → ℝ × ℝ
  vsmField m (θ , ω) = ω , ((Pref m - P m θ) - D m * (ω - ωs m)) / M m

  vsmSystem : VSMModel → System (ℝ × ℝ)
  vsmSystem m = vsmField m , x* m

  -- The requirement language (Lean `DroopVSM.VSMRequirement`) and its translation: the local
  -- sentences into all but `destabilizing`, instability into `smooth`, `balanced`, `inertia` and
  -- `destabilizing`, passivity into nothing.
  data VSMReq : Type where
    smooth balanced inertia damped synchronizing destabilizing : VSMReq

  vsmLocal vsmUnstable noVSM : VSMReq → Type
  vsmLocal destabilizing = ⊥
  vsmLocal _ = Unit
  vsmUnstable damped = ⊥
  vsmUnstable synchronizing = ⊥
  vsmUnstable _ = Unit
  noVSM _ = ⊥

  vsmTranslate : Sentence → VSMReq → Type
  vsmTranslate = localTable vsmLocal vsmLocal vsmUnstable noVSM

  -- Satisfaction, with `C¹` and the derivative abstract (Lean `ContDiff ℝ 1`, `deriv`).
  vsmMeets : ((ℝ → ℝ) → Type) → ((ℝ → ℝ) → ℝ → ℝ) → VSMModel → VSMReq → Type
  vsmMeets C¹ deriv m smooth = C¹ (P m)
  vsmMeets C¹ deriv m balanced = (snd (x* m) ≡ 0r) × (P m (fst (x* m)) ≡ Pref m + D m * ωs m)
  vsmMeets C¹ deriv m inertia = 0r < M m
  vsmMeets C¹ deriv m damped = 0r < D m
  vsmMeets C¹ deriv m synchronizing = 0r < deriv (P m) (fst (x* m))
  vsmMeets C¹ deriv m destabilizing = (deriv (P m) (fst (x* m)) < 0r) ⊎ (D m < 0r)

  -- The swing image with an arbitrary law: `⟨M, D, P_ref + D ω_s, P(θ), θ*, ω*⟩`.
  toGeneral : VSMModel → GeneralModel
  toGeneral m =
    generalModel (M m) (D m) (Pref m + D m * ωs m) (λ θ _ → P m θ) (fst (x* m)) (snd (x* m))

  -- The context: a sinusoidal power curve and `ω* = 0`.
  SinusoidalAt : ℝ → ℝ → ℝ → VSMModel → Type
  SinusoidalAt k₁ k₂ k₃ m = (P m ≡ (λ θ → k₁ + k₂ * sin (θ - k₃))) × (snd (x* m) ≡ 0r)

  -- On the context the swing image has a sinusoidal law.
  sinusoidalLaw : (k₁ k₂ k₃ : ℝ) (m : VSMModel) → SinusoidalAt k₁ k₂ k₃ m →
    SinusoidalLaw k₁ k₂ k₃ (toGeneral m)
  sinusoidalLaw k₁ k₂ k₃ m (p , w) = cong (λ f → λ θ (_ : ℝ) → f θ) p , w

  -- The infinite bus in the synchronous frame: `P = K₀ sin`, `ω_s = 0`, `ω* = 0`.
  InfiniteBus : ℝ → VSMModel → Type
  InfiniteBus K₀ m = (P m ≡ (λ θ → K₀ * sin θ)) × (ωs m ≡ 0r) × (snd (x* m) ≡ 0r)

  -- The composite map of models: the swing machine `⟨M, D, P_ref + D ω_s, k₁, k₂, k₃⟩` at `θ*`.
  toSwing : ℝ → ℝ → ℝ → VSMModel → SwingModel
  toSwing k₁ k₂ k₃ m = toHub k₁ k₂ k₃ (toGeneral m)

  module VSMReading (holds : System (ℝ × ℝ) → Sentence → Type)
    (invariant : (A : Affine (ℝ × ℝ)) (a : System (ℝ × ℝ)) (s : Sentence) →
      holds (transportSystem A a) s ≃ holds a s)
    (C¹ : (ℝ → ℝ) → Type) (deriv : (ℝ → ℝ) → ℝ → ℝ)
    where

    open GeneralSwingFamily holds invariant public

    vsmFamily : Family
    vsmFamily = record
      { Model = VSMModel ; Req = VSMReq ; system = vsmSystem ; meets = vsmMeets C¹ deriv
      ; translate = vsmTranslate }

    -- What Lean proves by field algebra.
    record Obligations : Type where
      field
        sameGeneral : (m : VSMModel) → vsmSystem m ≡ generalSystem (toGeneral m)
        hubField : (k₁ k₂ k₃ : ℝ) (m : GeneralModel) → SinusoidalLaw k₁ k₂ k₃ m →
          generalSystem m ≡ swingSystem (toHub k₁ k₂ k₃ m)
        busSinusoid : (K₀ : ℝ) (m : VSMModel) → InfiniteBus K₀ m → SinusoidalAt 0r K₀ 0r m
        busImage : (K₀ : ℝ) (m : VSMModel) → InfiniteBus K₀ m →
          toSwing 0r K₀ 0r m ≡ swingModel (swingParams (M m) (D m) (Pref m) 0r K₀ 0r) (fst (x* m))

    module _ (ob : Obligations) where
      open Obligations ob

      -- Every VSM model reads as its swing image with an arbitrary law.
      general : Hub vsmFamily generalFamily
      general = viaEquality toGeneral sameGeneral

      -- Every sentence denotes the preimage of the general family's denotation.
      vsm-den-eq-preimage : (s : Sentence) →
        den vsmFamily s ≡ (λ m → den generalFamily s (toGeneral m))
      vsm-den-eq-preimage s = funExt λ m → ua (Hub.read general m s)

      sinusoidal : ℝ → ℝ → ℝ → Family
      sinusoidal k₁ k₂ k₃ = restrictBy vsmFamily (SinusoidalAt k₁ k₂ k₃)

      -- On the context: the general reading restricted, composed with the hub reading.
      reading : (k₁ k₂ k₃ : ℝ) → Hub (sinusoidal k₁ k₂ k₃) swingFamily
      reading k₁ k₂ k₃ = compose
        (record { map = λ x → toGeneral (fst x) , sinusoidalLaw k₁ k₂ k₃ (fst x) (snd x)
                ; read = λ x → Hub.read general (fst x) })
        (hubReading hubField k₁ k₂ k₃)

      -- On the context, the sentences of a model are those of its swing image.
      den↔ : (k₁ k₂ k₃ : ℝ) (m : VSMModel) → SinusoidalAt k₁ k₂ k₃ m → (s : Sentence) →
        den vsmFamily s m ↔ den swingFamily s (toSwing k₁ k₂ k₃ m)
      den↔ k₁ k₂ k₃ m c s = ↔-of-≃ (Hub.read (reading k₁ k₂ k₃) (m , c) s)

      -- On an infinite bus in the synchronous frame the image is `⟨M, D, P_ref, 0, K₀, 0⟩`.
      den↔-bus : (K₀ : ℝ) (m : VSMModel) → InfiniteBus K₀ m → (s : Sentence) →
        den vsmFamily s m ↔
          den swingFamily s (swingModel (swingParams (M m) (D m) (Pref m) 0r K₀ 0r) (fst (x* m)))
      den↔-bus K₀ m b s = subst (λ y → den vsmFamily s m ↔ den swingFamily s y) (busImage K₀ m b)
        (den↔ 0r K₀ 0r m (busSinusoid K₀ m b) s)
