{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFL.DCLink.FourStatePLLDC where
-- Lean modules: theorem.GridTiedConverter.GFL.DCLink.FourState

-- Scaffold of the four-state GFL model as a parameterization of the PLL–DC model, the library's
-- single four-state DC-link model (`PLLDC.family` of
-- `theorem/GridTiedConverter/GFL/DCLink/PLLDC/Stability.lean`). The four-state models of
-- `theorem/GridTiedConverter/GFL/DCLink/FourState.lean` (parameters and a selected angle `θ₀`)
-- have no family of their own: the parameter map `FourState.Model.toPLLDC` (`ω_s = ω_g = 1`,
-- `V_dc* = 1`, `i_q0 = 0`, `V_g = V₀`, the same lossless line, the reference offset `i_d0`,
-- `I₀ = I_dc0`, the same gains and DC link) sends a four-state model to a PLL–DC system about the
-- operating point `(θ₀, 0, 1, 0)`, and the sentences of a four-state model are those of its image
-- (`fourFamily` is the PLL–DC model pulled back along the map, `comap`). The note's four-state
-- field is the PLL–DC field in other coordinates, the integrator sign flip `diag(1, 1, 1, −1)`,
-- which fixes the operating point (`conjugate`, Lean `FourState.field_eq_transport`), so the
-- note's field at its operating point satisfies exactly the sentences of the image (`noteReading`;
-- Lean proves the four-state trajectory arguments on the note's field and reads them through this
-- conjugacy). The four-state closed forms are readings of the PLL–DC model's requirements at the
-- image: the equilibrium relations with `C ≠ 0` (`FourState.meets_equilibrium_iff`), the quartic
-- Routh conditions on `det(λI − A₀)` (`FourState.meets_routh_iff`, the Jacobian identity
-- `FourState.A0_eq_jacobian`), `a₀ < 0` (`FourState.meets_detNeg_iff`) and the Routh boundary
-- (`FourState.meets_offBoundary_iff`). With the PLL–DC model's characterization of local
-- exponential stability off the singular plane (`p-les`, Lean
-- `PLLDC.mem_den_locallyExponentiallyStable_iff`) this gives the four-state characterization
-- (`les↔`, Lean `FourState.mem_den_locallyExponentiallyStable_iff`). Two four-state models whose
-- images meet the same PLL–DC requirements but differ on a sentence show that no requirement set
-- of the PLL–DC model denotes that sentence (`inexpressible`, Lean
-- `FourStateBoundary.realize_ne_den_lyapunovStable`, `FourStateBoundary.realize_ne_den_unstable`,
-- `FourStateBoundary.realize_ne_den_locallyAsymptoticallyStable`). Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics

module _ (X : Type) (holds : System X → Sentence → Type)
  (invariant : (A : Affine X) (a : System X) (s : Sentence) →
    holds (transportSystem A a) s ≃ holds a s)
  where

  open Flows X holds invariant

  module _ (FourModel PModel PReq : Type)
    (pSystem : PModel → System X)
    (pMeets : PModel → PReq → Type) (pTranslate : Sentence → PReq → Type)
    -- The note's four-state field read at the operating point.
    (noteSystem : FourModel → System X)
    -- The parameter map and the integrator flip.
    (toP : FourModel → PModel) (flip : Affine X)
    -- The PLL–DC model's requirements of a locally exponentially stable state (equilibrium,
    -- Routh), and the four-state closed forms (equilibrium relations with `C ≠ 0`, quartic Routh
    -- conditions).
    (pLes : PReq → Type) (Equilibrium Routh : FourModel → Type)
    where

    pFamily : Family
    pFamily = record
      { Model = PModel ; Req = PReq ; system = pSystem ; meets = pMeets
      ; translate = pTranslate }

    -- The four-state models read as the PLL–DC model: no semantics of their own.
    fourFamily : Family
    fourFamily = comap pFamily toP

    -- What Lean proves.
    record Obligations : Type where
      field
        conjugate : (f : FourModel) → noteSystem f ≡ transportSystem flip (pSystem (toP f))
        p-les : (f : FourModel) →
          den pFamily locallyExponentiallyStable (toP f) ↔ realize pFamily pLes (toP f)
        les-closed : (f : FourModel) →
          realize pFamily pLes (toP f) ↔ (Equilibrium f × Routh f)

    module _ (ob : Obligations) where
      open Obligations ob

      -- The note's field at the operating point satisfies exactly the sentences of the image.
      noteReading : (f : FourModel) → Reading (noteSystem f) (pSystem (toP f))
      noteReading f = conjugateReading affine flip (conjugate f)

      -- Local exponential stability of a four-state model in its own closed forms.
      les↔ : (f : FourModel) →
        den fourFamily locallyExponentiallyStable f ↔ (Equilibrium f × Routh f)
      les↔ f = ↔-trans (p-les f) (les-closed f)

      -- Indistinguishable images on either side of a sentence: no requirement set of the PLL–DC
      -- model denotes it.
      inexpressible : (s : Sentence) (u v : FourModel) →
        ((q : PReq) → pMeets (toP u) q ↔ pMeets (toP v) q) →
        den pFamily s (toP u) → (den pFamily s (toP v) → ⊥) →
        (T : PReq → Type) → ((b : PModel) → realize pFamily T b ↔ den pFamily s b) → ⊥
      inexpressible s u v same du nv T eq =
        nv (fst (eq (toP v)) (λ q t → fst (same q) (snd (eq (toP u)) du q t)))
