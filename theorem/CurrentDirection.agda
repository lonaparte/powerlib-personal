{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.CurrentDirection where

-- Scaffold of the unification of reference directions (work-sync `conventions.md` §D1, §D3,
-- §D8). A model written with OUT-positive port current and export-positive power is the same
-- model as the one written with IN-positive current and absorbed-positive power: the two writings
-- are related by the reversal of the directed quantities (`i ↦ −i`, `P ↦ −P`, `P_ref ↦ −P_ref`),
-- an involution, hence an equivalence of written models, and by univalence a path along which
-- every construction on written models is carried over (`rewritePath`). Angles, voltages,
-- reactances and gains are undirected and stay.
--
-- For families: the IN-written family reads through the OUT-written one. When the current is a
-- state coordinate (`GFL.PowerLoop.QuasiStatic`, state `(θ, x, i)`) the fields are conjugate under
-- the reversal of that coordinate, `diag(1, 1, −1)`; when the current is a parameter
-- (`GFL.RatePLL`, frozen `i_d`) the substitution of the parameter gives the same system. The
-- requirement languages correspond by restating each requirement (a sign condition on a directed
-- quantity flips, e.g. `0 ≤ L_g I_d` becomes `L_g i_d ≤ 0`). Then every exactness and soundness
-- result passes between the writings (`exact-rewritten`, `sound-rewritten`); the dispatch law
-- `i̇ = k_P (P_ref − P)` keeps its form because both sides flip. The library keeps one writing:
-- Lean writes the families IN-positive (`GFL.PowerLoop.QuasiStatic`, `GFL.RatePLL`,
-- `GFL.ModelLayers`, `GFL.LCLine.*`) and keeps the OUT writing only as the literature field of
-- each model, with the conjugacy against it (`field_eq_transport_literatureField`,
-- `field_eq_literatureField`, `lift_ccField_eq_transport`,
-- `field10_eq_transport_literatureField10`, `field13_eq_transport_literatureField13`), the §D8
-- boundary translation; the structure the reversal must preserve (linearity of the field in the
-- directed quantities, jointly) is what those proofs check. With one writing, the family-level
-- transfer of this scaffold is not needed in Lean. Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)

open import theorem.FamilyReading

-- Directed quantities: a type with the reversal of the reference direction, an involution.
record Directed : Type₁ where
  field
    Carrier : Type
    turn : Carrier → Carrier
    turn-turn : (x : Carrier) → turn (turn x) ≡ x

reversal : (D : Directed) → Directed.Carrier D ≃ Directed.Carrier D
reversal D = isoToEquiv (iso turn turn turn-turn turn-turn)
  where open Directed D

-- A model written in one reference direction: undirected data and directed data.
Written : Type → Directed → Type
Written U D = U × Directed.Carrier D

rewriteModel : {U : Type} (D : Directed) → Written U D → Written U D
rewriteModel D (u , d) = u , Directed.turn D d

rewrite² : {U : Type} (D : Directed) (x : Written U D) → rewriteModel D (rewriteModel D x) ≡ x
rewrite² D (u , d) = cong (u ,_) (Directed.turn-turn D d)

rewriteEquiv : {U : Type} (D : Directed) → Written U D ≃ Written U D
rewriteEquiv D = isoToEquiv (iso (rewriteModel D) (rewriteModel D) (rewrite² D) (rewrite² D))

-- Univalence: the IN writing is the OUT writing along a path; every construction on written
-- models (families, denotations, requirement spaces) is carried over, and transport computes as
-- the rewriting.
rewritePath : {U : Type} (D : Directed) → Written U D ≡ Written U D
rewritePath D = ua (rewriteEquiv D)

transport-rewrite : {U : Type} (D : Directed) (x : Written U D) →
  transport (rewritePath D) x ≡ rewriteModel D x
transport-rewrite D = uaβ (rewriteEquiv D)

-- Families written in the two directions.
module Families (S : Semantics) where
  open Semantics S
  open Readings S

  record Rewriting (I : Invariance) (outF inF : Family) : Type where
    field
      toOut : Family.Model inF → Family.Model outF
      conj : Family.Model inF → Invariance.Conj I
      conjugate : (m : Family.Model inF) →
        Family.system inF m ≡ Invariance.act I (conj m) (Family.system outF (toOut m))
      req : Family.Req inF ≃ Family.Req outF
      restated : (m : Family.Model inF) (q : Family.Req inF) →
        Family.meets inF m q ≃ Family.meets outF (toOut m) (equivFun req q)
      translated : (s : Sentence) (q : Family.Req inF) →
        Family.translate inF s q ≃ Family.translate outF s (equivFun req q)

  module _ {I : Invariance} {outF inF : Family} (rw : Rewriting I outF inF) where
    open Rewriting rw

    reading : Hub inF outF
    reading = viaConjugacy I toOut conj conjugate

    -- The restated requirements carve out the same models.
    corr : (s : Sentence) (m : Family.Model inF) →
      realize inF (Family.translate inF s) m ↔ realize outF (Family.translate outF s) (toOut m)
    corr s m = forward , backward
      where
      forward : realize inF (Family.translate inF s) m →
        realize outF (Family.translate outF s) (toOut m)
      forward f q' t = subst (Family.meets outF (toOut m)) (secEq req q')
        (equivFun (restated m (invEq req q'))
          (f (invEq req q') (invEq (translated s (invEq req q'))
            (subst (Family.translate outF s) (sym (secEq req q')) t))))
      backward : realize outF (Family.translate outF s) (toOut m) →
        realize inF (Family.translate inF s) m
      backward g q t = invEq (restated m q) (g (equivFun req q) (equivFun (translated s q) t))

    -- Every exactness and soundness result of the OUT writing holds for the IN writing.
    exact-rewritten : (s : Sentence) → Exact outF s → Exact inF s
    exact-rewritten s h = exact-pullback (partial (λ _ → Unit) reading) {ΔG = λ _ → ⊥} tt
      (λ _ _ ()) (corr s) (λ y _ → h y)

    sound-rewritten : (s : Sentence) → Sound outF s → Sound inF s
    sound-rewritten s h = sound-pullback-partial (partial (λ _ → Unit) reading) tt
      (λ m hm → fst (corr s m) hm) h
