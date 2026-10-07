{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.ImpedanceInterconnection where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.List using (List; []; _∷_; _++_)
record PortModel (M : Type) : Type where
  constructor portModel
  field state input output feedthrough : M

record StrictPortModel (M : Type) : Type where
  constructor strictPortModel
  field state input output : M

record Interconnection (M : Type) : Type where
  constructor interconnection
  field
    source : PortModel M
    load : StrictPortModel M
record ClosedLoop (M : Type) : Type where
  constructor closedLoop
  field a₁₁ a₁₂ a₂₁ a₂₂ : M
record Ops (M : Type) : Type where
  field
    times : M → M → M
    minus : M → M
    diff : M → M → M
data Tag : Type where
  A₁ B₁ C₁ D₁ A₂ B₂ C₂ : Tag

entry : {M : Type} → Interconnection M → Tag → M
entry (interconnection (portModel a b c d) (strictPortModel a' b' c')) A₁ = a
entry (interconnection (portModel a b c d) (strictPortModel a' b' c')) B₁ = b
entry (interconnection (portModel a b c d) (strictPortModel a' b' c')) C₁ = c
entry (interconnection (portModel a b c d) (strictPortModel a' b' c')) D₁ = d
entry (interconnection (portModel a b c d) (strictPortModel a' b' c')) A₂ = a'
entry (interconnection (portModel a b c d) (strictPortModel a' b' c')) B₂ = b'
entry (interconnection (portModel a b c d) (strictPortModel a' b' c')) C₂ = c'
data Expr : Type where
  mat : Tag → Expr
  mul : Expr → Expr → Expr
  neg : Expr → Expr
  sub : Expr → Expr → Expr

eval : {M : Type} → Ops M → (Tag → M) → Expr → M
eval ops env (mat t) = env t
eval ops env (mul x y) = Ops.times ops (eval ops env x) (eval ops env y)
eval ops env (neg x) = Ops.minus ops (eval ops env x)
eval ops env (sub x y) = Ops.diff ops (eval ops env x) (eval ops env y)
-- Source: port current in, voltage drop y₁ out, terminal voltage v = -y₁.
-- Load: v in, port current out, strictly proper; blocks are over source ⊕ load states.
body : ClosedLoop Expr
body = closedLoop (mat A₁) (mul (mat B₁) (mat C₂)) (neg (mul (mat B₂) (mat C₁)))
                  (sub (mat A₂) (mul (mul (mat B₂) (mat D₁)) (mat C₂)))
toClosedLoop : {M : Type} → Ops M → Interconnection M → ClosedLoop M
toClosedLoop ops x =
  closedLoop (eval ops (entry x) (ClosedLoop.a₁₁ body)) (eval ops (entry x) (ClosedLoop.a₁₂ body))
             (eval ops (entry x) (ClosedLoop.a₂₁ body)) (eval ops (entry x) (ClosedLoop.a₂₂ body))
toClosedLoop-spec : {M : Type} (ops : Ops M) (a b c d a' b' c' : M) →
  toClosedLoop ops (interconnection (portModel a b c d) (strictPortModel a' b' c')) ≡
    closedLoop a (Ops.times ops b c') (Ops.minus ops (Ops.times ops b' c))
               (Ops.diff ops a' (Ops.times ops (Ops.times ops b' d) c'))
toClosedLoop-spec ops a b c d a' b' c' = refl
Subsystems : Type → Type
Subsystems M = PortModel M × StrictPortModel M

toSubsystems : {M : Type} → Interconnection M → Subsystems M
toSubsystems (interconnection s l) = s , l

fromSubsystems : {M : Type} → Subsystems M → Interconnection M
fromSubsystems (s , l) = interconnection s l

subsystemsEquiv : {M : Type} → Interconnection M ≃ Subsystems M
subsystemsEquiv = isoToEquiv (iso toSubsystems fromSubsystems (λ _ → refl) (λ _ → refl))

subsystemsPath : {M : Type} → Interconnection M ≡ Subsystems M
subsystemsPath = ua subsystemsEquiv

subsystemsTransport : {M : Type} (x : Interconnection M) →
  transport subsystemsPath x ≡ toSubsystems x
subsystemsTransport = uaβ subsystemsEquiv

Table : Type → Type
Table M = (M × M) × (M × M)

toTable : {M : Type} → ClosedLoop M → Table M
toTable (closedLoop a b c d) = (a , b) , (c , d)

fromTable : {M : Type} → Table M → ClosedLoop M
fromTable ((a , b) , (c , d)) = closedLoop a b c d

blocksEquiv : {M : Type} → ClosedLoop M ≃ Table M
blocksEquiv = isoToEquiv (iso toTable fromTable (λ _ → refl) (λ _ → refl))

blocksPath : {M : Type} → ClosedLoop M ≡ Table M
blocksPath = ua blocksEquiv

blocksTransport : {M : Type} (x : ClosedLoop M) → transport blocksPath x ≡ toTable x
blocksTransport = uaβ blocksEquiv
tag : Tag → ℕ
tag A₁ = 0
tag B₁ = 1
tag C₁ = 2
tag D₁ = 3
tag A₂ = 4
tag B₂ = 5
tag C₂ = 6

encode : Expr → List ℕ
encode (mat t) = 0 ∷ tag t ∷ []
encode (mul x y) = 1 ∷ (encode x ++ encode y)
encode (neg x) = 2 ∷ encode x
encode (sub x y) = 3 ∷ (encode x ++ encode y)

wire : List ℕ
wire = 20261006 ∷ 1 ∷
  (encode (ClosedLoop.a₁₁ body) ++ encode (ClosedLoop.a₁₂ body) ++
   encode (ClosedLoop.a₂₁ body) ++ encode (ClosedLoop.a₂₂ body))
