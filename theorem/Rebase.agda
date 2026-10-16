{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.Rebase where

-- Scaffold of the rebasing connection of a source–load interconnection.
--
-- The interconnection is a structure over six spaces: the two state spaces, their rate spaces
-- (time derivatives, which carry the time base), the port voltage and the port current. A
-- representation change is an equivalence of each space: state coordinates, per-unit bases,
-- the current direction convention and the time base are all of this form, alone or together.
-- Univalence turns the six equivalences into a path of spaces, so the rebased interconnection
-- and the rebased closed loop are obtained by transport, and the closed loop commutes with every
-- representation change at once (`closedLoop-natural`), with no algebraic law.
--
-- What Lean has to prove is read off here: transport conjugates every map by the equivalences
-- (`transport-map`, `rebase-source-*`, `rebase-load-*`), and it conjugates the additive
-- operations too, so the closed loop of the conjugated source and load, taken with the target's
-- own operations, is the conjugated closed loop exactly when the equivalences preserve those
-- operations (`rebase-ops`, `closedLoop-rebased`). For matrices the operations are preserved
-- by linearity; what remains is that each change of bases is invertible.
--
-- The Lean connection is `theorem/Transform/Rebase.lean`. Nothing here is exported: the
-- scaffold fixes the statement and its generality, and Lean proves it by its own means.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma

-- The spaces of an interconnection.
record Spaces : Type₁ where
  constructor spaces
  field
    X₁ X₂ D₁ D₂ V Cur : Type

open Spaces

-- The additive operations the closed loop uses.
record Ops (S : Spaces) : Type where
  constructor ops
  field
    add₁ : D₁ S → D₁ S → D₁ S
    add₂ : D₂ S → D₂ S → D₂ S
    addV : V S → V S → V S
    neg₁ : D₁ S → D₁ S
    neg₂ : D₂ S → D₂ S
    negV : V S → V S

-- Source: port current in, port voltage out. Load: port voltage in, port current out, no
-- feedthrough.
record Source (S : Spaces) : Type where
  constructor source
  field
    A : X₁ S → D₁ S
    B : Cur S → D₁ S
    C : X₁ S → V S
    D : Cur S → V S

record Load (S : Spaces) : Type where
  constructor load
  field
    A : X₂ S → D₂ S
    B : V S → D₂ S
    C : X₂ S → Cur S

record Interconnection (S : Spaces) : Type where
  constructor interconnection
  field
    operations : Ops S
    src : Source S
    ld : Load S

open Interconnection

-- The closed loop from the injected current to the port voltage:
-- state map [[A₁, B₁C₂], [−B₂C₁, A₂ − B₂D₁C₂]], input [−B₁; B₂D₁], output [−C₁, −D₁C₂],
-- feedthrough D₁.
record ClosedLoop (S : Spaces) : Type where
  constructor closedLoopOf
  field
    A : X₁ S × X₂ S → D₁ S × D₂ S
    B : Cur S → D₁ S × D₂ S
    C : X₁ S × X₂ S → V S
    D : Cur S → V S

closedLoop : (S : Spaces) → Interconnection S → ClosedLoop S
closedLoop S ic = closedLoopOf
  (λ x → add₁ (s.A (fst x)) (s.B (l.C (snd x))) ,
         add₂ (neg₂ (l.B (s.C (fst x)))) (add₂ (l.A (snd x)) (neg₂ (l.B (s.D (l.C (snd x)))))))
  (λ j → neg₁ (s.B j) , l.B (s.D j))
  (λ x → addV (negV (s.C (fst x))) (negV (s.D (l.C (snd x)))))
  s.D
  where
  open Ops (operations ic)
  module s = Source (src ic)
  module l = Load (ld ic)

-- A representation change: an equivalence of each space.
record Rebasing (S S' : Spaces) : Type where
  field
    eX₁ : X₁ S ≃ X₁ S'
    eX₂ : X₂ S ≃ X₂ S'
    eD₁ : D₁ S ≃ D₁ S'
    eD₂ : D₂ S ≃ D₂ S'
    eV : V S ≃ V S'
    eI : Cur S ≃ Cur S'

open Rebasing

path : {S S' : Spaces} → Rebasing S S' → S ≡ S'
path r i = spaces (ua (eX₁ r) i) (ua (eX₂ r) i) (ua (eD₁ r) i) (ua (eD₂ r) i) (ua (eV r) i)
  (ua (eI r) i)

-- The rebased interconnection and closed loop, by transport.
rebase : {S S' : Spaces} → Rebasing S S' → Interconnection S → Interconnection S'
rebase r = subst Interconnection (path r)

rebaseLoop : {S S' : Spaces} → Rebasing S S' → ClosedLoop S → ClosedLoop S'
rebaseLoop r = subst ClosedLoop (path r)

-- Naturality for free: every representation change, no algebraic law.
closedLoop-natural : {S S' : Spaces} (r : Rebasing S S') (ic : Interconnection S) →
  closedLoop S' (rebase r ic) ≡ rebaseLoop r (closedLoop S ic)
closedLoop-natural r ic = sym (substCommSlice Interconnection ClosedLoop closedLoop (path r) ic)

-- Transport conjugates a map by the equivalences of its domain and codomain.
transport-map : {A A' B B' : Type} (eA : A ≃ A') (eB : B ≃ B') (f : A → B) (x : A') →
  transport (λ i → ua eA i → ua eB i) f x ≡ equivFun eB (f (invEq eA x))
transport-map eA eB f x = uaβ eB _ ∙ cong (λ y → equivFun eB (f y)) (~uaβ eA x)

-- and a binary operation by the equivalence of its space.
transport-op : {A A' : Type} (e : A ≃ A') (f : A → A → A) (x y : A') →
  transport (λ i → ua e i → ua e i → ua e i) f x y ≡ equivFun e (f (invEq e x) (invEq e y))
transport-op e f x y =
  uaβ e _ ∙ cong₂ (λ a b → equivFun e (f a b)) (~uaβ e x) (~uaβ e y)

module _ {S S' : Spaces} (r : Rebasing S S') (ic : Interconnection S) where
  private
    s = src ic
    l = ld ic
    s' = src (rebase r ic)
    l' = ld (rebase r ic)

  -- The rebased source and load: each map conjugated by the bases of its spaces.
  rebase-source-A : (x : X₁ S') →
    Source.A s' x ≡ equivFun (eD₁ r) (Source.A s (invEq (eX₁ r) x))
  rebase-source-A = transport-map (eX₁ r) (eD₁ r) (Source.A s)

  rebase-source-B : (j : Cur S') →
    Source.B s' j ≡ equivFun (eD₁ r) (Source.B s (invEq (eI r) j))
  rebase-source-B = transport-map (eI r) (eD₁ r) (Source.B s)

  rebase-source-C : (x : X₁ S') →
    Source.C s' x ≡ equivFun (eV r) (Source.C s (invEq (eX₁ r) x))
  rebase-source-C = transport-map (eX₁ r) (eV r) (Source.C s)

  rebase-source-D : (j : Cur S') →
    Source.D s' j ≡ equivFun (eV r) (Source.D s (invEq (eI r) j))
  rebase-source-D = transport-map (eI r) (eV r) (Source.D s)

  rebase-load-A : (x : X₂ S') →
    Load.A l' x ≡ equivFun (eD₂ r) (Load.A l (invEq (eX₂ r) x))
  rebase-load-A = transport-map (eX₂ r) (eD₂ r) (Load.A l)

  rebase-load-B : (v : V S') →
    Load.B l' v ≡ equivFun (eD₂ r) (Load.B l (invEq (eV r) v))
  rebase-load-B = transport-map (eV r) (eD₂ r) (Load.B l)

  rebase-load-C : (x : X₂ S') →
    Load.C l' x ≡ equivFun (eI r) (Load.C l (invEq (eX₂ r) x))
  rebase-load-C = transport-map (eX₂ r) (eI r) (Load.C l)

-- The obligation: each equivalence of a space with operations preserves them.
record Preserves {S S' : Spaces} (r : Rebasing S S') (o : Ops S) (o' : Ops S') : Type where
  open Ops
  field
    add₁-pres : (a b : D₁ S) → equivFun (eD₁ r) (add₁ o a b) ≡
      add₁ o' (equivFun (eD₁ r) a) (equivFun (eD₁ r) b)
    add₂-pres : (a b : D₂ S) → equivFun (eD₂ r) (add₂ o a b) ≡
      add₂ o' (equivFun (eD₂ r) a) (equivFun (eD₂ r) b)
    addV-pres : (a b : V S) → equivFun (eV r) (addV o a b) ≡
      addV o' (equivFun (eV r) a) (equivFun (eV r) b)
    neg₁-pres : (a : D₁ S) → equivFun (eD₁ r) (neg₁ o a) ≡ neg₁ o' (equivFun (eD₁ r) a)
    neg₂-pres : (a : D₂ S) → equivFun (eD₂ r) (neg₂ o a) ≡ neg₂ o' (equivFun (eD₂ r) a)
    negV-pres : (a : V S) → equivFun (eV r) (negV o a) ≡ negV o' (equivFun (eV r) a)

module _ {S S' : Spaces} (r : Rebasing S S') (ic : Interconnection S) (o' : Ops S')
    (pres : Preserves r (operations ic) o') where
  open Ops
  open Preserves pres
  private
    o = operations ic
    o-r = operations (rebase r ic)

    binary : {A A' : Type} (e : A ≃ A') (f : A → A → A) (f' : A' → A' → A') →
      ((a b : A) → equivFun e (f a b) ≡ f' (equivFun e a) (equivFun e b)) →
      transport (λ i → ua e i → ua e i → ua e i) f ≡ f'
    binary e f f' h = funExt λ x → funExt λ y →
      transport-op e f x y ∙ h _ _ ∙ cong₂ f' (secEq e x) (secEq e y)

    unary : {A A' : Type} (e : A ≃ A') (f : A → A) (f' : A' → A') →
      ((a : A) → equivFun e (f a) ≡ f' (equivFun e a)) →
      transport (λ i → ua e i → ua e i) f ≡ f'
    unary e f f' h = funExt λ x → transport-map e e f x ∙ h _ ∙ cong f' (secEq e x)

  -- Transport carries the operations to the target's own operations.
  rebase-ops : o-r ≡ o'
  rebase-ops i = ops
    (binary (eD₁ r) (add₁ o) (add₁ o') add₁-pres i)
    (binary (eD₂ r) (add₂ o) (add₂ o') add₂-pres i)
    (binary (eV r) (addV o) (addV o') addV-pres i)
    (unary (eD₁ r) (neg₁ o) (neg₁ o') neg₁-pres i)
    (unary (eD₂ r) (neg₂ o) (neg₂ o') neg₂-pres i)
    (unary (eV r) (negV o) (negV o') negV-pres i)

  -- The closed loop of the conjugated source and load, with the target's own operations, is
  -- the conjugated closed loop.
  closedLoop-rebased :
    closedLoop S' (interconnection o' (src (rebase r ic)) (ld (rebase r ic))) ≡
      rebaseLoop r (closedLoop S ic)
  closedLoop-rebased =
    cong (λ q → closedLoop S' (interconnection q (src (rebase r ic)) (ld (rebase r ic))))
      (sym rebase-ops)
    ∙ closedLoop-natural r ic
