{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.DroopVSM where

-- Scaffold of the large-signal equivalence of droop with a first-order power filter and the VSM
-- (`GFM.DroopVSM.droopFamily` of `theorem/GFM/DroopVSM.lean` read through
-- `GFM.DroopVSM.vsmFamily`, the VSM family of `theorem/VSMSwing.agda`). Both loops have an
-- arbitrary power map `P`, a frame speed `ω_s` and a free selected state. The droop + LPF loop
-- `θ̇ = ω_s − (P_f − P_ref)/K_R`, `τ_p Ṗ_f = P(θ) − P_f` (`K_R, τ_p ≠ 0`, carried by every model)
-- at `y* = (θ*, P_f*)` is, in the coordinates `ω = ω_s − (P_f − P_ref)/K_R` (`vsmCoords`), the
-- VSM `⟨τ_p K_R, K_R, P_ref, ω_s, P⟩` at the image of `y*` (`toVSM`): the reading is a conjugacy
-- for every model and every sentence (both loops are autonomous, without a port), not on a
-- context. The droop family keeps the VSM requirement language read through `toVSM`, with the
-- same translation. By univalence its satisfaction structure is the VSM family's pulled back
-- along `toVSM` (`semantics-eq-comap`), every sentence denotes the preimage of its VSM
-- denotation (`den-eq-preimage`, member-wise `den↔`), and the droop translation is sound because
-- the VSM translation is (`sound`). Composed with the swing reading of the VSM family
-- (`theorem/VSMSwing.agda`): on an infinite bus `P = K₀ sin`, in any rotating frame, an
-- equilibrium with `K_R, τ_p > 0` and `K₀ cos θ* > 0` is locally exponentially stable
-- (`bus-les`), its VSM image being the swing machine `⟨τ_p K_R, K_R, P_ref + K_R ω_s, 0, K₀, 0⟩`
-- at `θ*`, balanced with positive inertia, damping and synchronizing coefficient. In the
-- synchronous frame this loop is `GFM.DroopLPF` of `theorem/GFM/VSMLPF.lean`, read directly
-- through the swing hub with its own requirement language in `theorem/DroopSwing.agda`. Lean:
-- `conjugate` is `GFM.DroopVSM.vsmField_eq_transport` with `GFM.DroopVSM.affineCoord_apply`
-- (read by `Dynamics.holds_transport_iff`; passivity holds of both loops), `semantics-eq-comap`
-- is `GFM.DroopVSM.semantics_eq_comap`, `den-eq-preimage` is `GFM.DroopVSM.den_eq_preimage`,
-- `den↔` gives `GFM.DroopVSM.locallyExponentiallyStable_iff`, `lyapunovStable_iff`,
-- `unstable_iff` and `localAsymptoticStable_iff`, `vsm-sound` is
-- `GFM.DroopVSM.vsmFamily_chain_le_semantics`, `sound` is
-- `GFM.DroopVSM.droopFamily_chain_le_semantics`; `busSinusoid` and `busLocal` are the algebra of
-- `GFM.DroopVSM.infiniteBus_locallyExponentiallyStable` (`GFM.DroopVSM.equilibrium_iff`,
-- `GFM.DroopVSM.VSMModel.vector_eq_zero_iff`), whose conclusion is `bus-les`, through
-- `GFM.DroopVSM.vsm_mem_den_iff_swing_of_sinusoid` and
-- `Synchronous.Swing.mem_den_locallyExponentiallyStable`. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)

open import theorem.FamilyReading
open import theorem.FlowSemantics
open import theorem.Swing
open import theorem.VSMSwing

module _ (Sc : Scalars) where
  open Scalars Sc
  open SwingContent Sc
  open VSMContent Sc

  -- A droop + LPF closed loop with an arbitrary power map, read about a selected state `y*`.
  record DroopModel : Type where
    constructor droopModel
    field
      KR τp Pref ωs : ℝ
      P : ℝ → ℝ
      KR≢0 : ¬ (KR ≡ 0r)
      τp≢0 : ¬ (τp ≡ 0r)
      y* : ℝ × ℝ

  open DroopModel

  -- The loop in the coordinates `(θ, P_f)` and the selected state.
  droopField : DroopModel → ℝ × ℝ → ℝ × ℝ
  droopField m (θ , Pf) = (ωs m - (Pf - Pref m) / KR m) , (P m θ - Pf) / τp m

  droopSystem : DroopModel → System (ℝ × ℝ)
  droopSystem m = droopField m , y* m

  -- From droop to VSM coordinates: `(θ, P_f) ↦ (θ, ω_s − (P_f − P_ref)/K_R)`, its inverse and its
  -- linear part `diag(1, −1/K_R)`.
  vsmCoords : DroopModel → Affine (ℝ × ℝ)
  vsmCoords m = record
    { point = λ { (θ , Pf) → θ , (ωs m - (Pf - Pref m) / KR m) }
    ; pointInv = λ { (θ , ω) → θ , (Pref m - KR m * (ω - ωs m)) }
    ; vector = λ { (a , b) → a , ((- b) / KR m) } }

  -- The map of models: `M = τ_p K_R`, `D = K_R`, at the image of the selected state.
  toVSM : DroopModel → VSMModel
  toVSM m =
    vsmModel (τp m * KR m) (KR m) (Pref m) (ωs m) (P m) (Affine.point (vsmCoords m) (y* m))

  -- Droop + LPF on an infinite bus, in any frame: `P = K₀ sin`, `K_R, τ_p > 0`, an equilibrium
  -- at `y*` and `K₀ cos θ* > 0`.
  DroopBus : ℝ → DroopModel → Type
  DroopBus K₀ m = (P m ≡ (λ θ → K₀ * sin θ)) × (0r < KR m) × (0r < τp m)
    × (droopField m (y* m) ≡ (0r , 0r)) × (0r < K₀ * cos (fst (y* m)))

  module Reading (holds : System (ℝ × ℝ) → Sentence → Type)
    (invariant : (A : Affine (ℝ × ℝ)) (a : System (ℝ × ℝ)) (s : Sentence) →
      holds (transportSystem A a) s ≃ holds a s)
    (C¹ : (ℝ → ℝ) → Type) (deriv : (ℝ → ℝ) → ℝ → ℝ)
    where

    open VSMReading holds invariant C¹ deriv
      renaming (reading to swingReading; den↔ to swing↔; Obligations to SwingObligations)

    -- The droop family keeps the requirements of its VSM image and the same translation.
    droopFamily : Family
    droopFamily = record
      { Model = DroopModel ; Req = VSMReq ; system = droopSystem
      ; meets = λ m → vsmMeets C¹ deriv (toVSM m) ; translate = vsmTranslate }

    -- What Lean proves by field arithmetic (with `K_R, τ_p ≠ 0`, carried by the model).
    module _ (conjugate : (m : DroopModel) →
               vsmSystem (toVSM m) ≡ transportSystem (vsmCoords m) (droopSystem m)) where

      reading : Hub droopFamily vsmFamily
      reading = record
        { map = toVSM
        ; read = λ m s → invEquiv (conjugateReading affine (vsmCoords m) (conjugate m) s) }

      -- The droop semantics is the VSM semantics pulled back along `toVSM`.
      semantics-eq-comap : semantics droopFamily ≡ semantics (comap vsmFamily toVSM)
      semantics-eq-comap = readPath reading

      -- Every sentence denotes the preimage of its VSM denotation.
      den-eq-preimage : (s : Sentence) → den droopFamily s ≡ (λ m → den vsmFamily s (toVSM m))
      den-eq-preimage s = funExt λ m → ua (Hub.read reading m s)

      den↔ : (m : DroopModel) (s : Sentence) → den droopFamily s m ↔ den vsmFamily s (toVSM m)
      den↔ m s = ↔-of-≃ (Hub.read reading m s)

      -- The droop translation is sound: its requirements are its VSM image's.
      sound : (vsm-sound : (s : Sentence) → Sound vsmFamily s) (s : Sentence) →
        Sound droopFamily s
      sound vsm-sound s = sound-pullback reading (λ m h → h) (vsm-sound s)

      -- What Lean proves: the VSM image lies in the sinusoidal context `(0, K₀, 0)` (`ω* = 0` from
      -- the equilibrium) and its swing image meets the local swing conditions.
      module _ (laws : SwingLaws) (vsmOb : SwingObligations)
        (busSinusoid : (K₀ : ℝ) (m : DroopModel) → DroopBus K₀ m → SinusoidalAt 0r K₀ 0r (toVSM m))
        (busLocal : (K₀ : ℝ) (m : DroopModel) → DroopBus K₀ m →
          realize swingFamily swingLocal (toSwing 0r K₀ 0r (toVSM m)))
        where

        -- The composite droop → VSM → swing reading.
        bus-les : (K₀ : ℝ) (m : DroopModel) → DroopBus K₀ m →
          den droopFamily locallyExponentiallyStable m
        bus-les K₀ m b = snd (den↔ m locallyExponentiallyStable)
          (snd (swing↔ vsmOb 0r K₀ 0r (toVSM m) (busSinusoid K₀ m b) locallyExponentiallyStable)
            (SwingLaws.sound laws locallyExponentiallyStable (toSwing 0r K₀ 0r (toVSM m))
              (busLocal K₀ m b)))
