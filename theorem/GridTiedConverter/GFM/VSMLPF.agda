{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFM.VSMLPF where
-- Lean modules: theorem.GridTiedConverter.GFM.VSMLPF

-- Scaffold content of the VSM with a first-order power filter on an infinite bus
-- (`GFM.VSMLPF.family`, `theorem/GridTiedConverter/GFM/VSMLPF.lean`): the loop `δ̇ = ω`,
-- `M ω̇ = P₀ − P_f − D ω`, `Ṗ_f = ω_c (K₀ sin δ − P_f)` read at a selected angle `δ*` about the
-- point `(δ*, 0, P₀)` (`GFM.VSMLPF.Model`), its requirement language (`GFM.VSMLPF.Requirement`,
-- `GFM.VSMLPF.Meets`), its translation (`GFM.VSMLPF.translate`) and the laws it publishes for the
-- models read through it: soundness of the translation (`VSMLPF.chain_le_semantics`), exactness of
-- local exponential stability within `physical` (`VSMLPF.exactUnder_locallyExponentiallyStable`)
-- and the local asymptotic characterization within `physical`
-- (`VSMLPF.mem_den_locallyAsymptoticallyStable_iff_of_physical`). The readings through it are
-- `theorem/GridTiedConverter/GFM/VSMLPFLossy.agda` (the loop on a lossy line, a conjugacy for
-- every model) and `theorem/GridTiedConverter/GFM/Tracking/GridFrame.agda` (the loop on a grid at a
-- constant frequency offset, read in the frame of the grid, whose image models are members of this
-- family). The platform stack of `theorem/GridTiedConverter/GFM/VSMPlatform.agda` takes this family
-- as its model layer, there kept abstract. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics
open import theorem.PowerSystem.Synchronous.Swing using (only)

module VSMLPFContent (Sc : Scalars) where
  open Scalars Sc

  State3 : Type
  State3 = ℝ × ℝ × ℝ

  -- Parameters and the models about a selected angle.
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

  -- The field in the coordinates `(δ, ω, P_f)` and the selected point `(δ*, 0, P₀)`.
  vsmField : VSMParams → State3 → State3
  vsmField q (x , w , pf) = w , (P0 q - pf - D q * w) / M q , ωc q * (K0 q * sin x - pf)

  vsmSystem : VSMModel → System State3
  vsmSystem m = vsmField (g m) , (δ m , 0r , P0 (g m))

  -- The fast-filter bound `D ω_c + D²/M` and the synchronizing coefficient `K = K₀ cos δ*`.
  bound : ℝ → ℝ → ℝ → ℝ
  bound m d w = d * w + (d * d) / m

  vsmK : VSMModel → ℝ
  vsmK m = K0 (g m) * cos (δ m)

  data VSMReq : Type where
    balanced physical synchronizing fastFilter destabilizing : VSMReq

  -- A requirement of the language stated on given parameters and coefficients: power balance,
  -- positivity, synchronization, the fast-filter condition and a destabilizing sign. A spoke that
  -- keeps the language states it in its own parameters through `reqOf`.
  reqOf : (bal : Type) (m d w k : ℝ) → VSMReq → Type
  reqOf bal m d w k balanced = bal
  reqOf bal m d w k physical = (0r < m) × (0r < d) × (0r < w)
  reqOf bal m d w k synchronizing = 0r < k
  reqOf bal m d w k fastFilter = k < bound m d w
  reqOf bal m d w k destabilizing = (bound m d w < k) ⊎ (k < 0r)

  vsmMeets : VSMModel → VSMReq → Type
  vsmMeets m = reqOf (K0 (g m) * sin (δ m) ≡ P0 (g m)) (M (g m)) (D (g m)) (ωc (g m)) (vsmK m)

  -- The translation: the local sentences into all but `destabilizing`, instability into
  -- `balanced`, `physical` and `destabilizing`, passivity into nothing.
  vsmLocal vsmUnstable noReq : VSMReq → Type
  vsmLocal destabilizing = ⊥
  vsmLocal _ = Unit
  vsmUnstable synchronizing = ⊥
  vsmUnstable fastFilter = ⊥
  vsmUnstable _ = Unit
  noReq _ = ⊥

  vsmTranslate : Sentence → VSMReq → Type
  vsmTranslate = localTable vsmLocal vsmLocal vsmUnstable noReq

  -- The family on a semantic layer of fields on `ℝ³`.
  module VSMLPFFamily (holds : System State3 → Sentence → Type)
    (invariant : (Af : Affine State3) (a : System State3) (s : Sentence) →
      holds (transportSystem Af a) s ≃ holds a s)
    where

    open Flows State3 holds invariant public

    vsmFamily : Family
    vsmFamily = record
      { Model = VSMModel ; Req = VSMReq ; system = vsmSystem ; meets = vsmMeets
      ; translate = vsmTranslate }

    -- The local asymptotic characterization within `physical`: a balanced angle with
    -- `0 < K ≤ D ω_c + D²/M`, the Hopf boundary included.
    vsmLAS : VSMModel → Type
    vsmLAS m = vsmMeets m balanced × (0r < vsmK m) × (vsmK m ≤ bound (M (g m)) (D (g m)) (ωc (g m)))

    -- The laws the family publishes and the models read through it use.
    record VSMLaws : Type where
      field
        sound : (s : Sentence) → Sound vsmFamily s
        exactUnder-les : ExactUnder vsmFamily (only physical) locallyExponentiallyStable
        las↔ : (m : VSMModel) → vsmMeets m physical →
          den vsmFamily locallyAsymptoticallyStable m ↔ vsmLAS m
