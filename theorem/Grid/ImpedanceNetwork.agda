{-# OPTIONS --cubical --safe --guardedness #-}
module theorem.Grid.ImpedanceNetwork where
-- Lean modules: theorem.Grid.GridImpedance

-- Scaffold of the reading of the grid-side network of a converter (a shunt at the point of common
-- coupling and a series R–L line branch to a stiff grid, `Grid.networkModel` of
-- `theorem/Grid/GridImpedance.lean`) as an impedance interconnection of
-- `theorem/Grid/ImpedanceInterconnection.agda`. In the coordinates `w = −v_PCC` the shunt is the
-- source: state matrix `aS` (the field of the dual series element of the shunt), input `−c⁻¹`,
-- output `−1`, no feedthrough (`Grid.shuntPlant`); the line branch is the strictly proper load:
-- state matrix `aL`, input `l⁻¹`, output `1` (`Passive.DqRL.dqRLPlant`). The closed loop of
-- the two (`toClosedLoop`) is, block by block, the network realization: state matrix
-- `[[aS, −c⁻¹], [l⁻¹, aL]]`, input `[c⁻¹; 0]`, output `[1, 0]`, no feedthrough
-- (`network-closedLoop`, Lean `Grid.networkModel_eq_closedLoop`, with `Grid.networkA`,
-- `Grid.networkB`, `Grid.networkC`). The laws used are those of a ring with unit `one` and zero
-- `zero` (`NetworkLaws`). The analytic content — the shunt's impedance is the inverse of its dq
-- admittance (`Grid.transfer_shuntPlant_mul_dqAdmittance`), the port impedance of the
-- interconnection is the parallel connection `Z_ext` (`Grid.Zext_eq_portImpedance`), and so the
-- network transfer is `Z_ext` (`Grid.networkModel_transfer`) — is proved in Lean alone. Nothing
-- here is exported.

open import Cubical.Foundations.Prelude

open import theorem.Grid.ImpedanceInterconnection

module _ {M : Type} (ops : Ops M) where
  open Ops ops

  -- The shunt as source and the line branch as load.
  network : (aS invC aL invL one zero : M) → Interconnection M
  network aS invC aL invL one zero =
    interconnection (portModel aS (minus invC) (minus one) zero) (strictPortModel aL invL one)

  -- The network realization: state, input and output blocks.
  networkBlocks : (aS invC aL invL one zero : M) → ClosedLoop M
  networkBlocks aS invC aL invL one zero =
    closedLoop aS (minus invC) invL aL invC zero one zero zero

  record NetworkLaws (one zero : M) : Type where
    field
      mul-one : (x : M) → times x one ≡ x
      mul-zero : (x : M) → times x zero ≡ zero
      mul-minus : (x y : M) → times x (minus y) ≡ minus (times x y)
      minus-minus : (x : M) → minus (minus x) ≡ x
      minus-zero : minus zero ≡ zero
      diff-zero : (x : M) → diff x zero ≡ x

  module _ {one zero : M} (laws : NetworkLaws one zero) where
    open NetworkLaws laws

    network-closedLoop : (aS invC aL invL : M) →
      toClosedLoop ops (network aS invC aL invL one zero) ≡ networkBlocks aS invC aL invL one zero
    network-closedLoop aS invC aL invL =
      λ i → closedLoop aS (mul-one (minus invC) i) (p₂₁ i) (p₂₂ i) (minus-minus invC i)
                       (mul-zero invL i) (minus-minus one i) (pc₂ i) zero
      where
      p₂₁ = cong minus (mul-minus invL one) ∙ minus-minus (times invL one) ∙ mul-one invL
      p₂₂ = cong (diff aL) (mul-one (times invL zero) ∙ mul-zero invL) ∙ diff-zero aL
      pc₂ = cong minus (mul-one zero) ∙ minus-zero
