{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFM.Tracking.GridFrame where
-- Lean modules: theorem.GridTiedConverter.GFM.Tracking.Synchronism

-- Scaffold of the change to the frame of a grid that runs at a constant frequency offset `c`
-- (`GFM.Tracking.gridFrame` of `theorem/GridTiedConverter/GFM/Tracking/Synchronism.lean`). The
-- reduced grid-forming loop in the nominal frame, `θ̇ = ω`, `M ω̇ = P_ref − P_e(θ − u) − D ω`, with
-- the one-harmonic power curve `P_e = k₁ + k₂ sin(· − k₃)` of the swing parameters, has the grid
-- angle `u` as an input (`GFM.Tracking.angleField`, the swing field at `(θ − u, ω)`); under the
-- moving grid `u(t) = θ₀ + c t` it is not autonomous. The frame change at time `t` is the
-- translation `(θ, ω) ↦ (θ − θ₀ − c t, ω − c)`; it moves with the constant velocity `(c, 0)`, so a
-- curve solves the nominal-frame loop exactly when its image solves the field minus that
-- velocity, which is the autonomous field of the VSM model with the nominal frequency `ω_s = −c` in
-- the grid frame (`gridFrame`, a member of the VSM family of
-- `theorem/GridTiedConverter/GFM/VSMSwing.agda`). The same frame change on the three-state loop
-- with a power filter (`GFM.VSMLPF.fieldU`, the grid angle in `Ṗ_f = ω_c (K₀ sin(θ − u) − P_f)`;
-- `frame3` keeps `P_f`) gives the VSM + filter model with the power reference `P₀ − D c`
-- (`offsetFilter`, `filterGridFrame`, a member of the family of
-- `theorem/GridTiedConverter/GFM/VSMLPF.agda`). The scaffold fixes the nominal-frame data, the
-- frame changes, the image models and the two identities Lean proves: `frameVelocity` (Lean
-- `GFM.Tracking.gridFrame_hasDerivAt_iff`, componentwise along solutions, with
-- `GFM.Tracking.gridFrame_vector`: the image field is the swing field with the power reference
-- `P_ref − D c`) and `filterFrameVelocity` (Lean `GFM.Tracking.filterGridFrame_hasDerivAt_iff`,
-- the image model `GFM.Tracking.offsetFilter`). The relation is one of solutions under a
-- time-varying change of coordinates, not a conjugacy of two autonomous systems, so no sentence is
-- transported here: the conclusions are stated on the image models in their families. In the VSM
-- family the swing hub reads them (`DroopVSM.vsm_mem_den_iff_swing_of_sinusoid`): loss of
-- synchronism when `|P_ref − D c − c₀| > A` (`GFM.Tracking.gridFrame_mem_den_unstable`) and
-- synchronism iff `|P_ref − D c − c₀| < A` (`GFM.Tracking.gridFrame_synchronism_iff`); in the
-- VSM + filter family they are its laws at `P₀ − D c`
-- (`GFM.Tracking.filterGridFrame_mem_den_unstable`, `GFM.Tracking.filterGridFrame_synchronism_iff`,
-- through `VSMLPF.exactUnder_locallyExponentiallyStable`). Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import theorem.Flow.FlowSemantics
open import theorem.PowerSystem.Synchronous.Swing
open import theorem.GridTiedConverter.GFM.VSMSwing
open import theorem.GridTiedConverter.GFM.VSMLPF

module _ (Sc : Scalars) where
  open Scalars Sc
  open SwingContent Sc
  open VSMContent Sc
  module LPF = VSMLPFContent Sc

  -- The loop with the grid angle `u` as a parameter (Lean `GFM.Tracking.angleField`): the swing
  -- field of the parameters at `(θ − u, ω)`.
  angleField : SwingParams → ℝ → ℝ × ℝ → ℝ × ℝ
  angleField p u (θ , ω) = swingField p (θ - u , ω)

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
  -- `−c` in the grid frame and the power curve of the parameters (Lean `GFM.Tracking.gridFrame`).
  gridFrame : SwingParams → ℝ → ℝ → VSMModel
  gridFrame p c δ =
    vsmModel (SwingParams.M p) (SwingParams.D p) (SwingParams.Pm p) (- c) (Pe p) (δ , 0r)

  -- The three-state loop with the grid angle `u` as a parameter (Lean `GFM.VSMLPF.fieldU`): the
  -- VSM + filter field at `(θ − u, ω, P_f)`.
  filterAngleField : LPF.VSMParams → ℝ → LPF.State3 → LPF.State3
  filterAngleField q u (θ , ω , pf) = LPF.vsmField q (θ - u , ω , pf)

  -- The frame change at time `t` on three states: the translation of the angle and the frequency,
  -- the filtered power unchanged.
  frame3 : ℝ → ℝ → ℝ → Affine LPF.State3
  frame3 θ₀ c t = record
    { point = λ { (θ , ω , pf) → θ - gridAngle θ₀ c t , ω - c , pf }
    ; pointInv = λ { (θ , ω , pf) → θ + gridAngle θ₀ c t , ω + c , pf }
    ; vector = λ w → w }

  -- The image parameters: the power reference `P₀ − D c` (Lean `GFM.Tracking.offsetFilter`), and
  -- the image model about the selected power angle `δ*`.
  offsetFilter : LPF.VSMParams → ℝ → LPF.VSMParams
  offsetFilter q c = LPF.vsmParams (LPF.VSMParams.M q) (LPF.VSMParams.D q) (LPF.VSMParams.ωc q)
    (LPF.VSMParams.P0 q - LPF.VSMParams.D q * c) (LPF.VSMParams.K0 q)

  filterGridFrame : LPF.VSMParams → ℝ → ℝ → LPF.VSMModel
  filterGridFrame q c δ = LPF.vsmModel (offsetFilter q c) δ

  -- What Lean proves: in the new coordinates the image field equals the nominal-frame field minus
  -- the frame velocity `(c, 0)`, resp. `(c, 0, 0)` (the fields do not depend on the selected
  -- angle).
  record Obligations : Type where
    field
      frameVelocity : (p : SwingParams) (θ₀ c t δ : ℝ) (x : ℝ × ℝ) →
        vsmField (gridFrame p c δ) (Affine.point (frame θ₀ c t) x) ≡
          (fst (angleField p (gridAngle θ₀ c t) x) - c , snd (angleField p (gridAngle θ₀ c t) x))
      filterFrameVelocity : (q : LPF.VSMParams) (θ₀ c t : ℝ) (x : LPF.State3) →
        LPF.vsmField (offsetFilter q c) (Affine.point (frame3 θ₀ c t) x) ≡
          (fst (filterAngleField q (gridAngle θ₀ c t) x) - c ,
            snd (filterAngleField q (gridAngle θ₀ c t) x))
