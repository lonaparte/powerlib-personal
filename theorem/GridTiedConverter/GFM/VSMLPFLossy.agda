{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFM.VSMLPFLossy where
-- Lean modules: theorem.GridTiedConverter.GFM.VSMLPFLossy

-- Scaffold of the reading of the VSM with a first-order power filter on a lossy line through the
-- lossless model (`GFM.VSMLPFLossy.family` of `theorem/GridTiedConverter/GFM/VSMLPFLossy.lean`
-- read through `GFM.VSMLPF.family`). The lossy loop `δ̇ = ω`, `M ω̇ = P_ref − P_f − D ω`,
-- `Ṗ_f = ω_c (c₀ + A sin(δ − α) − P_f)` at `(δ*, 0, P_ref)` is the lossless loop
-- `⟨M, D, ω_c, P_ref − c₀, A⟩` at `(δ* − α, 0, P_ref − c₀)` in the coordinates
-- `(δ, ω, P_f) = (δ' + α, ω', P_f' + c₀)`, for every model: no context is needed, and the lossy
-- requirement language is the lossless one read in the lossy parameters. The scaffold fixes the
-- lossless content it reads (`VSMParams`, `vsmField`, `VSMReq`, `vsmMeets`, `vsmTranslate`), the
-- map of models (`toVSMLPF`), the change of coordinates (`lossyCoords`), the requirement
-- correspondence, and derives the reading of every sentence (`den↔`), the transfer of soundness
-- (`sound`), of exactness within `physical` (`exactUnder-les`) and of the local asymptotic
-- characterization (`las↔`). Lean proves the conjugacy as the equality of the translated fields
-- (`VSMLPFLossy.Model.field_eq_toVSMLPF`, from `VSMLPFLossy.field_eq`), the reading
-- (`VSMLPFLossy.den_eq_preimage`), the correspondence (`VSMLPFLossy.realize_eq_preimage`) and the
-- transfers (`VSMLPFLossy.chain_le_semantics` from `VSMLPF.chain_le_semantics`,
-- `VSMLPFLossy.exactUnder_locallyExponentiallyStable` from
-- `VSMLPF.exactUnder_locallyExponentiallyStable` by `Spectral.exactUnder_of_hub`,
-- `VSMLPFLossy.mem_den_locallyAsymptoticallyStable_iff_of_physical` from
-- `VSMLPF.mem_den_locallyAsymptoticallyStable_iff_of_physical`). Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics
open import theorem.PowerSystem.Synchronous.Swing using (only)

module _ (Sc : Scalars) where
  open Scalars Sc

  State3 : Type
  State3 = ℝ × ℝ × ℝ

  -- The lossless content read (`GFM.VSMLPF`): parameters, models about a selected angle, the
  -- field in `(δ, ω, P_f)`, the selected point `(δ*, 0, P₀)`, the requirements and the table.
  record VSMParams : Type where
    constructor vsmParams
    field
      M D ωc P0 K0 : ℝ

  record VSMModel : Type where
    constructor vsmModel
    field
      g : VSMParams
      δ : ℝ

  open VSMParams
  open VSMModel

  vsmField : VSMParams → State3 → State3
  vsmField q (x , w , pf) = w , (P0 q - pf - D q * w) / M q , ωc q * (K0 q * sin x - pf)

  vsmSystem : VSMModel → System State3
  vsmSystem m = vsmField (g m) , (δ m , 0r , P0 (g m))

  -- The fast-filter bound `D ω_c + D²/M`.
  bound : ℝ → ℝ → ℝ → ℝ
  bound m d w = d * w + (d * d) / m

  vsmK : VSMModel → ℝ
  vsmK m = K0 (g m) * cos (δ m)

  data VSMReq : Type where
    balanced physical synchronizing fastFilter destabilizing : VSMReq

  -- A requirement of the lossless language stated on given parameters and coefficients: power
  -- balance, positivity, synchronization, the fast-filter condition and a destabilizing sign.
  reqOf : (bal : Type) (m d w k : ℝ) → VSMReq → Type
  reqOf bal m d w k balanced = bal
  reqOf bal m d w k physical = (0r < m) × (0r < d) × (0r < w)
  reqOf bal m d w k synchronizing = 0r < k
  reqOf bal m d w k fastFilter = k < bound m d w
  reqOf bal m d w k destabilizing = (bound m d w < k) ⊎ (k < 0r)

  vsmMeets : VSMModel → VSMReq → Type
  vsmMeets m = reqOf (K0 (g m) * sin (δ m) ≡ P0 (g m)) (M (g m)) (D (g m)) (ωc (g m)) (vsmK m)

  vsmLocal vsmUnstable noReq : VSMReq → Type
  vsmLocal destabilizing = ⊥
  vsmLocal _ = Unit
  vsmUnstable synchronizing = ⊥
  vsmUnstable fastFilter = ⊥
  vsmUnstable _ = Unit
  noReq _ = ⊥

  vsmTranslate : Sentence → VSMReq → Type
  vsmTranslate = localTable vsmLocal vsmLocal vsmUnstable noReq

  -- The lossy spoke: parameters, models, field, selected point `(δ*, 0, P_ref)`, requirements.
  record LossyParams : Type where
    constructor lossyParams
    field
      lM lD lωc Pref c0 A α : ℝ

  record LossyModel : Type where
    constructor lossyModel
    field
      lp : LossyParams
      lδ : ℝ

  open LossyParams
  open LossyModel

  Pe : LossyParams → ℝ → ℝ
  Pe q x = c0 q + A q * sin (x - α q)

  lossyField : LossyParams → State3 → State3
  lossyField q (x , w , pf) = w , (Pref q - pf - lD q * w) / lM q , lωc q * (Pe q x - pf)

  lossySystem : LossyModel → System State3
  lossySystem m = lossyField (lp m) , (lδ m , 0r , Pref (lp m))

  lossyK : LossyModel → ℝ
  lossyK m = A (lp m) * cos (lδ m - α (lp m))

  lossyMeets : LossyModel → VSMReq → Type
  lossyMeets m = reqOf (Pe (lp m) (lδ m) ≡ Pref (lp m)) (lM (lp m)) (lD (lp m)) (lωc (lp m))
    (lossyK m)

  -- The map of models: the lossless model `⟨M, D, ω_c, P_ref − c₀, A⟩` about `δ* − α`.
  toVSMLPF : LossyModel → VSMModel
  toVSMLPF m = vsmModel (vsmParams (lM q) (lD q) (lωc q) (Pref q - c0 q) (A q)) (lδ m - α q)
    where q = lp m

  -- From lossless to lossy coordinates: `(δ', ω', P_f') ↦ (δ' + α, ω', P_f' + c₀)`.
  lossyCoords : LossyModel → Affine State3
  lossyCoords m = record
    { point = λ { (x , w , pf) → (x + α q) , w , (pf + c0 q) }
    ; pointInv = λ { (x , w , pf) → (x - α q) , w , (pf - c0 q) }
    ; vector = λ v → v }
    where q = lp m

  module Reading (holds : System State3 → Sentence → Type)
    (invariant : (Af : Affine State3) (a : System State3) (s : Sentence) →
      holds (transportSystem Af a) s ≃ holds a s)
    where

    open Flows State3 holds invariant

    vsmFamily : Family
    vsmFamily = record
      { Model = VSMModel ; Req = VSMReq ; system = vsmSystem ; meets = vsmMeets
      ; translate = vsmTranslate }

    lossyFamily : Family
    lossyFamily = record
      { Model = LossyModel ; Req = VSMReq ; system = lossySystem ; meets = lossyMeets
      ; translate = vsmTranslate }

    -- The local asymptotic characterization within `physical`: a balanced angle with
    -- `0 < K ≤ D ω_c + D²/M`.
    vsmLAS : VSMModel → Type
    vsmLAS m = vsmMeets m balanced × (0r < vsmK m) × (vsmK m ≤ bound (M (g m)) (D (g m)) (ωc (g m)))

    lossyLAS : LossyModel → Type
    lossyLAS m = lossyMeets m balanced × (0r < lossyK m)
      × (lossyK m ≤ bound (lM (lp m)) (lD (lp m)) (lωc (lp m)))

    -- The laws the lossless family publishes (Lean `VSMLPF.chain_le_semantics`,
    -- `VSMLPF.exactUnder_locallyExponentiallyStable`,
    -- `VSMLPF.mem_den_locallyAsymptoticallyStable_iff_of_physical`).
    record VSMLaws : Type where
      field
        sound : (s : Sentence) → Sound vsmFamily s
        exactUnder-les : ExactUnder vsmFamily (only physical) locallyExponentiallyStable
        las↔ : (m : VSMModel) → vsmMeets m physical →
          den vsmFamily locallyAsymptoticallyStable m ↔ vsmLAS m

    -- What Lean proves, by field arithmetic.
    record Obligations : Type where
      field
        conjugate : (m : LossyModel) →
          lossySystem m ≡ transportSystem (lossyCoords m) (vsmSystem (toVSMLPF m))
        meets↔ : (m : LossyModel) (q : VSMReq) → lossyMeets m q ↔ vsmMeets (toVSMLPF m) q

    module _ (laws : VSMLaws) (ob : Obligations) where
      open Obligations ob

      reading : Hub lossyFamily vsmFamily
      reading = viaConjugacy affine toVSMLPF lossyCoords conjugate

      -- Every sentence of a lossy model is the sentence of its lossless reading
      -- (Lean `VSMLPFLossy.den_eq_preimage`).
      den↔ : (m : LossyModel) (s : Sentence) → den lossyFamily s m ≃ den vsmFamily s (toVSMLPF m)
      den↔ m s = Hub.read reading m s

      -- Every requirement set corresponds (Lean `VSMLPFLossy.realize_eq_preimage`).
      realize↔ : (Γ : VSMReq → Type) (m : LossyModel) →
        realize lossyFamily Γ m ↔ realize vsmFamily Γ (toVSMLPF m)
      realize↔ Γ m = (λ h q γ → fst (meets↔ m q) (h q γ)) , (λ h q γ → snd (meets↔ m q) (h q γ))

      -- Soundness and exactness within `physical` pass from the lossless family (Lean
      -- `VSMLPFLossy.chain_le_semantics`, `VSMLPFLossy.exactUnder_locallyExponentiallyStable`).
      sound : (s : Sentence) → Sound lossyFamily s
      sound s = sound-pullback reading (λ m → fst (realize↔ (vsmTranslate s) m))
        (VSMLaws.sound laws s)

      exactUnder-les : ExactUnder lossyFamily (only physical) locallyExponentiallyStable
      exactUnder-les = exactUnder-pullback reading (λ m → fst (realize↔ (only physical) m))
        (λ m _ → realize↔ (vsmTranslate locallyExponentiallyStable) m)
        (VSMLaws.exactUnder-les laws)

      -- The local asymptotic characterization on the lossy line
      -- (Lean `VSMLPFLossy.mem_den_locallyAsymptoticallyStable_iff_of_physical`).
      las↔ : (m : LossyModel) → lossyMeets m physical →
        den lossyFamily locallyAsymptoticallyStable m ↔ lossyLAS m
      las↔ m hp = ↔-trans (↔-of-≃ (den↔ m locallyAsymptoticallyStable))
        (↔-trans (VSMLaws.las↔ laws (toVSMLPF m) (fst (meets↔ m physical) hp))
          ((λ h → snd (meets↔ m balanced) (fst h) , snd h) ,
           (λ h → fst (meets↔ m balanced) (fst h) , snd h)))
