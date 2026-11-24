{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFM.Noise.DroopVSMNoise where
-- Lean modules: theorem.GridTiedConverter.GFM.Noise.DroopVSMNoise

-- Scaffold of the reading of a power set-point disturbance of droop with a first-order power
-- filter through the VSM coordinates (`theorem/GridTiedConverter/GFM/Noise/DroopVSMNoise.lean`),
-- on top of the deterministic reading of `theorem/GridTiedConverter/GFM/DroopVSM.agda`, whose
-- models, coordinates `vsmCoords` and map `toVSM` are reused. A disturbance value `ξ` enters the
-- droop law as the set-point `P_ref + ξ` (`setpoint`), while the coordinates stay those of the
-- nominal set-point: a disturbance varies in time, so the change of coordinates cannot follow it.
-- The change is affine, so a disturbed field `f + c` (drift `f`, noise column `c`) is transported
-- to `T f(T⁻¹ y) + T c`: the drift by the deterministic conjugacy, the column by the linear part
-- alone (no second-order Itô term). The reading (`noise-reading`): the droop loop with set-point
-- `P_ref + ξ`, in the nominal VSM coordinates, is the VSM image `⟨τ_p K_R, K_R⟩` in the frame of a
-- grid with frequency deviation `ω_g = −ξ/K_R` (`vsmGridField`): droop set-point noise is the
-- VSM's grid-frequency (angle-row) noise of intensity `σ/D`, not its set-point (momentum-row)
-- noise, which the disturbed coordinates would give (`setpoint-vsm`). Lean: `conjugate` is
-- `GFM.DroopVSM.vsmField_eq_transport` with `GFM.DroopVSM.affineCoord_apply`, `setpoint-noise` is
-- `GFM.Noise.Droop.droopField_setpoint`, `setpoint-vsm` is `GFM.Noise.Droop.vsmField_setpoint`,
-- `grid` is `GFM.Noise.Droop.vsmGridField_eq`, `linear` is the linearity of the continuous linear
-- equivalence `GFM.DroopVSM.coord`, `column` is field arithmetic, and `noise-reading` is
-- `GFM.Noise.Droop.setpoint_transport`. The covariance of the reading
-- (`GFM.Noise.Droop.setpoint_cov_unique`) is analytic content proved in Lean alone. Nothing here
-- is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import theorem.Flow.FlowSemantics
open import theorem.GridTiedConverter.GFM.VSMSwing
open import theorem.GridTiedConverter.GFM.DroopVSM

module _ (Sc : Scalars) where
  open Scalars Sc
  open VSMContent Sc

  -- Sum of plane vectors (the scalars carry no laws; Lean proves the facts named below).
  _⊕_ : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ
  (a , b) ⊕ (c , d) = (a + c) , (b + d)

  -- The droop model with the set-point `P_ref + ξ`, everything else unchanged.
  setpoint : DroopModel Sc → ℝ → DroopModel Sc
  setpoint m ξ = record m { Pref = DroopModel.Pref m + ξ }

  -- Noise columns at the value `ξ`: droop set-point `(ξ/K_R, 0)` in `(θ, P_f)`; VSM set-point
  -- `(0, ξ/M)` and VSM grid frequency `(−ω_g, 0)` in `(θ, ω)`.
  droopNoise : DroopModel Sc → ℝ → ℝ × ℝ
  droopNoise m ξ = (ξ / DroopModel.KR m) , 0r

  momentumNoise : VSMModel → ℝ → ℝ × ℝ
  momentumNoise v ξ = 0r , (ξ / VSMModel.M v)

  gridNoise : ℝ → ℝ × ℝ
  gridNoise ωg = (- ωg) , 0r

  -- The VSM in the frame of a grid with frequency deviation `ω_g` (nominal damping reference).
  vsmGridField : VSMModel → ℝ → ℝ × ℝ → ℝ × ℝ
  vsmGridField v ωg (θ , ω) =
    (ω - ωg) , ((VSMModel.Pref v - VSMModel.P v θ) - VSMModel.D v * (ω - VSMModel.ωs v))
      / VSMModel.M v

  -- The VSM model with the set-point `P_ref + ξ`.
  vsmSetpoint : VSMModel → ℝ → VSMModel
  vsmSetpoint v ξ = record v { Pref = VSMModel.Pref v + ξ }

  -- The droop field transported by the nominal VSM coordinates.
  inVSM : DroopModel Sc → (ℝ × ℝ → ℝ × ℝ) → ℝ × ℝ → ℝ × ℝ
  inVSM m f y = Affine.vector (vsmCoords Sc m) (f (Affine.pointInv (vsmCoords Sc m) y))

  -- What Lean proves, by field arithmetic.
  record Obligations : Type where
    field
      conjugate : (m : DroopModel Sc) →
        vsmSystem (toVSM Sc m) ≡ transportSystem (vsmCoords Sc m) (droopSystem Sc m)
      setpoint-noise : (m : DroopModel Sc) (ξ : ℝ) →
        droopField Sc (setpoint m ξ) ≡ (λ x → droopField Sc m x ⊕ droopNoise m ξ)
      setpoint-vsm : (v : VSMModel) (ξ : ℝ) →
        vsmField (vsmSetpoint v ξ) ≡ (λ y → vsmField v y ⊕ momentumNoise v ξ)
      grid : (v : VSMModel) (ωg : ℝ) → vsmGridField v ωg ≡ (λ y → vsmField v y ⊕ gridNoise ωg)
      linear : (m : DroopModel Sc) (u w : ℝ × ℝ) →
        Affine.vector (vsmCoords Sc m) (u ⊕ w) ≡
          Affine.vector (vsmCoords Sc m) u ⊕ Affine.vector (vsmCoords Sc m) w
      column : (m : DroopModel Sc) (ξ : ℝ) →
        Affine.vector (vsmCoords Sc m) (droopNoise m ξ) ≡ gridNoise (- (ξ / DroopModel.KR m))

  module _ (ob : Obligations) where
    open Obligations ob

    -- The drift part of the deterministic reading.
    drift : (m : DroopModel Sc) → vsmField (toVSM Sc m) ≡ inVSM m (droopField Sc m)
    drift m = cong fst (conjugate m)

    -- The reading of the set-point disturbance: grid-frequency noise of the VSM image.
    noise-reading : (m : DroopModel Sc) (ξ : ℝ) →
      inVSM m (droopField Sc (setpoint m ξ)) ≡
        vsmGridField (toVSM Sc m) (- (ξ / DroopModel.KR m))
    noise-reading m ξ = funExt λ y →
      inVSM m (droopField Sc (setpoint m ξ)) y
        ≡⟨ cong (λ f → Affine.vector (vsmCoords Sc m) (f (Affine.pointInv (vsmCoords Sc m) y)))
             (setpoint-noise m ξ) ⟩
      Affine.vector (vsmCoords Sc m)
        (droopField Sc m (Affine.pointInv (vsmCoords Sc m) y) ⊕ droopNoise m ξ)
        ≡⟨ linear m _ _ ⟩
      inVSM m (droopField Sc m) y ⊕ Affine.vector (vsmCoords Sc m) (droopNoise m ξ)
        ≡⟨ cong₂ _⊕_ (sym (funExt⁻ (drift m) y)) (column m ξ) ⟩
      vsmField (toVSM Sc m) y ⊕ gridNoise (- (ξ / DroopModel.KR m))
        ≡⟨ sym (funExt⁻ (grid (toVSM Sc m) _) y) ⟩
      vsmGridField (toVSM Sc m) (- (ξ / DroopModel.KR m)) y ∎
