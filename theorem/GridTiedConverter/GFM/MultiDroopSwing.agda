{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.GridTiedConverter.GFM.MultiDroopSwing where
-- Lean modules: theorem.GridTiedConverter.GFM.MultiDroop

-- Scaffold of the reading of droop units on a lossless network through the swing network
-- (`GFM.MultiDroop.family` of `theorem/GridTiedConverter/GFM/MultiDroop.lean` read through
-- `Network.Swing.family`, `theorem/PowerSystem/Network/Swing/Basic.lean`). The `n + 1` units
-- `θ̇ₖ = ω_s − (P_{f,k} − P*ₖ)/K_{R,k}`, `τₖ Ṗ_{f,k} = P_{L,k} + ∑ⱼ Bₖⱼ sin(θₖ − θⱼ) − P_{f,k}`, in
-- relative angles and filtered powers about the state `(θ*, P* + K_R (ω_s − Ω))` (every droop
-- frequency at the synchronous frequency `Ω`), are the swing network with inertia `τ K_R`,
-- damping `K_R` and power `P* − P_L + K_R (ω_s − Ω)` about `(θ*, 0)` (`toSwing`), in the
-- coordinates `(δ, P_f) ↦ (δ, ω_s − Ω − (P_f − P*)/K_R)` (`coords`). The reading is a
-- conjugacy for every model (positive gains and filters are carried by the Lean parameters), so
-- every sentence reads through the hub (`den↔`). The stability requirement of the droop family
-- (balance with a Laplacian of `Bₖⱼ cos(θ*ₖ − θ*ⱼ)` positive on the grounded directions)
-- corresponds to the swing network's local translation (power balance with a Hurwitz reduced
-- Jacobian), so the swing network's exactness of local exponential stability passes to the
-- droop family (`exact-les`). The network data are abstract here: reduced states `X`, droop
-- networks `Net`, angle profiles `Profile`, swing data `SwingData`. Lean: `conjugate` is
-- `MultiDroop.Net.swing_reducedField_eq_transport` with `MultiDroop.Model.equilibrium_eq` (read by
-- `Dynamics.holds_transport_iff`), `den↔` is `MultiDroop.mem_den_iff_swing`, `stable↔` is
-- `MultiDroop.Model.balanced_iff` with `MultiDroop.isHurwitz_jacobian_iff`, the hub law is
-- `Network.Swing.exact_locallyExponentiallyStable`, and `exact-les` is
-- `MultiDroop.mem_den_locallyExponentiallyStable_iff`
-- (`MultiDroop.exact_locallyExponentiallyStable`).
-- Nothing here is exported.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)

open import theorem.Family.FamilyReading
open import theorem.Flow.FlowSemantics

module _ (X Net Profile SwingData : Type)
  -- The reduced droop field and the selected state of a network about an angle profile.
  (droopField : Net → X → X) (selected : Net → Profile → X)
  -- The swing data of a network, the reduced swing field and its synchronous point.
  (toSwingData : Net → SwingData) (swingField : SwingData → X → X) (syncPoint : Profile → X)
  -- The droop coordinates of a network.
  (coords : Net → Affine X)
  where

  record NetModel : Type where
    constructor netModel
    field
      net : Net
      θ : Profile

  record SwingModel : Type where
    constructor swingModel
    field
      params : SwingData
      θ : Profile

  open NetModel
  open SwingModel

  netSystem : NetModel → System X
  netSystem m = droopField (net m) , selected (net m) (NetModel.θ m)

  swingSystem : SwingModel → System X
  swingSystem m = swingField (params m) , syncPoint (SwingModel.θ m)

  -- The map of models: the swing network of the units at the same angle profile.
  toSwing : NetModel → SwingModel
  toSwing m = swingModel (toSwingData (net m)) (NetModel.θ m)

  data NetReq : Type where
    stable unstable : NetReq

  data SwingReq : Type where
    powerFlow jacobianStable jacobianUnstable : SwingReq

  netLocal netUnstable noReq : NetReq → Type
  netLocal unstable = ⊥
  netLocal stable = Unit
  netUnstable stable = ⊥
  netUnstable unstable = Unit
  noReq _ = ⊥

  swingLocal swingUnstable noSwing : SwingReq → Type
  swingLocal jacobianUnstable = ⊥
  swingLocal _ = Unit
  swingUnstable jacobianStable = ⊥
  swingUnstable _ = Unit
  noSwing _ = ⊥

  module Reading (holds : System X → Sentence → Type)
    (invariant : (A : Affine X) (a : System X) (s : Sentence) →
      holds (transportSystem A a) s ≃ holds a s)
    (netMeets : NetModel → NetReq → Type) (swingMeets : SwingModel → SwingReq → Type)
    where

    open Flows X holds invariant

    netFamily : Family
    netFamily = record
      { Model = NetModel ; Req = NetReq ; system = netSystem ; meets = netMeets
      ; translate = localTable netLocal netLocal netUnstable noReq }

    swingFamily : Family
    swingFamily = record
      { Model = SwingModel ; Req = SwingReq ; system = swingSystem ; meets = swingMeets
      ; translate = localTable swingLocal swingLocal swingUnstable noSwing }

    -- What Lean proves by field algebra (with positive gains and filters carried by the model).
    module _ (conjugate : (m : NetModel) →
               swingSystem (toSwing m) ≡ transportSystem (coords (net m)) (netSystem m))
      where

      reading : Hub netFamily swingFamily
      reading = record
        { map = toSwing
        ; read = λ m s → invEquiv (conjugateReading affine (coords (net m)) (conjugate m) s) }

      -- Every sentence of a droop network is the sentence of its swing network.
      den↔ : (m : NetModel) (s : Sentence) → den netFamily s m ↔ den swingFamily s (toSwing m)
      den↔ m s = ↔-of-≃ (Hub.read reading m s)

      -- The stability requirement corresponds to the swing network's local translation (balance
      -- and the exact Hurwitz test), so exactness of local exponential stability passes.
      module _ (stable↔ : (m : NetModel) →
                 realize netFamily netLocal m ↔ realize swingFamily swingLocal (toSwing m))
        (hubLES : Exact swingFamily locallyExponentiallyStable)
        where

        exact-les : Exact netFamily locallyExponentiallyStable
        exact-les = exact-pullback (partial Flow reading) {ΔG = noSwing} tt
          (λ x q ()) (λ x → stable↔ x)
          (λ y _ → hubLES y)
