{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.Transform.ClarkePark where
-- Lean modules: theorem.Transform.ParkABC theorem.Transform.Park theorem.Transform.PerUnitDq theorem.Transform.SpaceVector

-- Scaffold of the coordinate representations of a three-phase quantity (work-sync
-- `conventions.md` §4, `theory/T-park-transformation.md` §1.2, `theory/T-sync-machine.md` §1.1).
--
-- A three-phase quantity has phase coordinates (abc), stationary coordinates (αβ0) and rotating
-- coordinates (dq0) at a frame angle. A representation is a coordinate space with the power
-- pairing `v·i` (`Rep`); a change of representation is an equivalence of coordinates that
-- preserves the pairing (`Change`). Changes compose (`_⨾_`), and by univalence every change is a
-- path of representations (`changePath`), so whatever is built from the pairing in one
-- representation is the same in the other. Lean has to give only the elementary changes and
-- their preservation, by one generic law for orthogonal changes
-- (`Transform.orthogonal_dotProduct`); each instance supplies its orthogonality.
--
-- The elementary changes Lean fixes: the power-invariant Clarke matrix `Transform.clarkePI`
-- (abc → αβ0) and the rotation of the αβ plane with the zero sequence fixed (αβ0 → dq0).
-- Their composite is the power-invariant Park matrix `Transform.parkMatrix` (`parkMatrix`
-- below); Lean takes `parkMatrix` as the hub, `Transform.clarkePI` as its value at angle 0 and
-- `PerUnit.parkABCPI` as its d and q rows, with orthogonality
-- `Transform.parkMatrix_mul_transpose`. The amplitude-invariant writings `Transform.clarke`
-- and `Transform.parkABC` are the same coordinates scaled by `√(2/3)`
-- (`PerUnit.parkABCPI_eq_smul`); they preserve the pairing up to `3/2` on zero-sequence-free
-- quantities (`Transform.dotProduct_eq_three_halves_clarke`, `PerUnit.power_parkABC`) and are
-- not changes in this sense. The complex space vector is the complex form of the
-- amplitude-invariant αβ coordinates (`SpaceVector.clarke_eq_toComplex`). The balanced and
-- negative-sequence signals are scaled phase-axis cosines (`Transform.balanced_eq_cvec`,
-- `Transform.negSeq_eq_cvec`). Nothing here is exported: the scaffold fixes which relations
-- Lean states, and Lean proves them by its own means.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

module _ (S : Type) where

  -- A representation: coordinates with the power pairing.
  record Rep : Type₁ where
    constructor rep
    field
      Coord : Type
      pair : Coord → Coord → S

  open Rep

  -- A change of representation: an equivalence of coordinates preserving the pairing.
  record Change (A B : Rep) : Type where
    constructor change
    field
      coord : Coord A ≃ Coord B
      preserves : (v w : Coord A) → pair B (equivFun coord v) (equivFun coord w) ≡ pair A v w

  open Change

  idChange : (A : Rep) → Change A A
  idChange A = change (idEquiv (Coord A)) (λ v w → refl)

  -- Changes compose; the composite preserves the pairing because each step does.
  _⨾_ : {A B C : Rep} → Change A B → Change B C → Change A C
  f ⨾ g = change (compEquiv (coord f) (coord g))
    (λ v w → preserves g (equivFun (coord f) v) (equivFun (coord f) w) ∙ preserves f v w)

  -- A change is a path of representations: the pairing of `B` is that of `A` carried along.
  changePath : {A B : Rep} → Change A B → A ≡ B
  changePath {A} {B} f i = rep (ua (coord f) i) (pairP i)
    where
      pairP : PathP (λ i → ua (coord f) i → ua (coord f) i → S) (pair A) (pair B)
      pairP = ua→ (λ v → ua→ (λ w → sym (preserves f v w)))

  -- The three representations, the elementary changes and the power-invariant Park matrix.
  record ThreePhase (Θ : Type) : Type₁ where
    field
      abc αβ0 dq0 : Rep
      clarkePI : Change abc αβ0
      rotation : Θ → Change αβ0 dq0

    parkMatrix : Θ → Change abc dq0
    parkMatrix θ = clarkePI ⨾ rotation θ

    -- The phase and rotating representations are the same representation at every angle.
    abc≡dq0 : Θ → abc ≡ dq0
    abc≡dq0 θ = changePath (parkMatrix θ)
