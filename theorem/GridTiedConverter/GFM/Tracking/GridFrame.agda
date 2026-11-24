{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFM.Tracking.GridFrame where
-- Lean modules: theorem.GridTiedConverter.GFM.Tracking.Synchronism

-- Scaffold of the change to the frame of a grid that runs at a constant frequency offset `c`
-- (`GFM.Tracking.gridFrame` of `theorem/GridTiedConverter/GFM/Tracking/Synchronism.lean`). The
-- reduced grid-forming loop in the nominal frame, `θ̇ = ω`, `M ω̇ = P_ref − P(θ − u) − D ω`, has
-- the grid angle `u` as an input (`GFM.Tracking.angleField`); under the moving grid
-- `u(t) = θ₀ + c t` it is not autonomous. The frame change at time `t` is the translation
-- `(θ, ω) ↦ (θ − θ₀ − c t, ω − c)`; it moves with the constant velocity `(c, 0)`, so a curve solves
-- the nominal-frame loop exactly when its image solves the field minus that velocity, which is the
-- autonomous field of the VSM model with the nominal frequency `ω_s = −c` in the grid frame
-- (`gridFrame`, a member of the VSM family of `theorem/GridTiedConverter/GFM/VSMSwing.agda`). The
-- scaffold fixes the nominal-frame data, the frame change, the image model and the one identity
-- Lean proves (`frameVelocity`: Lean `GFM.Tracking.gridFrame_hasDerivAt_iff`, componentwise along
-- solutions, with `GFM.Tracking.gridFrame_vector`: the image field is the swing field with the
-- power reference `P_ref − D c`). The relation is one of solutions under a time-varying change of
-- coordinates, not a conjugacy of two autonomous systems, so no sentence is transported here: the
-- conclusions are stated on the image models in the VSM family, where the swing hub reads them
-- (`DroopVSM.vsm_mem_den_iff_swing_of_sinusoid`): loss of synchronism when
-- `|P_ref − D c − c₀| > A` (`GFM.Tracking.gridFrame_mem_den_unstable`) and synchronism iff
-- `|P_ref − D c − c₀| < A` (`GFM.Tracking.gridFrame_synchronism_iff`). The same frame change on the
-- three-state loop with a power filter gives the VSM + filter model with the power reference
-- `P₀ − D c` (`GFM.Tracking.offsetFilter`, `GFM.Tracking.filterGridFrame_hasDerivAt_iff`), read in
-- `VSMLPF.family` (`GFM.Tracking.filterGridFrame_mem_den_unstable`,
-- `GFM.Tracking.filterGridFrame_synchronism_iff`); that family has no Agda content and is not
-- restated here. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import theorem.Flow.FlowSemantics
open import theorem.GridTiedConverter.GFM.VSMSwing

module _ (Sc : Scalars) where
  open Scalars Sc
  open VSMContent Sc

  -- The nominal-frame data of the two-state loop: inertia, damping, power reference and the power
  -- curve of the power angle.
  record GFMParams : Type where
    constructor gfmParams
    field
      M D Pref : ℝ
      P : ℝ → ℝ

  open GFMParams

  -- The loop with the grid angle `u` as a parameter (Lean `GFM.Tracking.angleField`).
  angleField : GFMParams → ℝ → ℝ × ℝ → ℝ × ℝ
  angleField p u (θ , ω) = ω , ((Pref p - P p (θ - u)) - D p * ω) / M p

  -- The moving grid angle `θ₀ + c t`.
  gridAngle : ℝ → ℝ → ℝ → ℝ
  gridAngle θ₀ c t = θ₀ + c * t

  -- The frame change at time `t`: a translation, whose linear part is the identity.
  frame : ℝ → ℝ → ℝ → Affine (ℝ × ℝ)
  frame θ₀ c t = record
    { point = λ x → fst x - gridAngle θ₀ c t , snd x - c
    ; pointInv = λ y → fst y + gridAngle θ₀ c t , snd y + c
    ; vector = λ w → w }

  -- The image model about the selected power angle `δ*`: the VSM model with the nominal frequency
  -- `−c` in the grid frame (Lean `GFM.Tracking.gridFrame`).
  gridFrame : GFMParams → ℝ → ℝ → VSMModel
  gridFrame p c δ = vsmModel (M p) (D p) (Pref p) (- c) (P p) (δ , 0r)

  -- What Lean proves: in the new coordinates the image field equals the nominal-frame field minus
  -- the frame velocity `(c, 0)` (the field does not depend on the selected angle).
  record Obligations : Type where
    field
      frameVelocity : (p : GFMParams) (θ₀ c t δ : ℝ) (x : ℝ × ℝ) →
        vsmField (gridFrame p c δ) (Affine.point (frame θ₀ c t) x) ≡
          (fst (angleField p (gridAngle θ₀ c t) x) - c , snd (angleField p (gridAngle θ₀ c t) x))
