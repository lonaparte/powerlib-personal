import theorem.Attributes
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Two-ports in impedance parameters: termination, reflected impedance and inverters

The algebra of a linear two-port described by its impedance parameters at one complex frequency:
the port relations of a terminated two-port, its input impedance, and the two-ports with a vanishing
diagonal (immittance inverters), which turn a load impedance into its scaled reciprocal and set the
output current by the input voltage alone. No circuit is fixed here.

Scope.
* A two-port at one fixed complex frequency is a complex 2 × 2 matrix `Z` of impedance parameters,
  both port currents counted into the network: `v₁ = Z₀₀ i₁ + Z₀₁ i₂`, `v₂ = Z₁₀ i₁ + Z₁₁ i₂`
  (`Equations`). Port 2 terminated by a load `Z_L` imposes `v₂ = −Z_L i₂` (`Terminated`).
* Arbitrary complex entries; no reciprocity, passivity or realizability is assumed unless a
  statement says so. Every statement is algebra (foundation).

Source: the impedance-parameter description of a linear two-port and its termination (standard
network theory); the T network as the series arms `Z_a`, `Z_b` with the shunt `Z_c` between them;
the quarter-wave (immittance) inverter as the two-port with `Z₀₀ = Z₁₁ = 0`.

Results.
* `Equations`, `Terminated`, `inputImpedance` (`Z₀₀ − Z₀₁ Z₁₀ / (Z₁₁ + Z_L)`), `tee`.
* `terminated_current`: a terminated two-port carries the output current
  `i₂ = −Z₁₀ i₁ / (Z₁₁ + Z_L)`; `terminated_input`: its input port is the impedance
  `inputImpedance Z Z_L` (`v₁ = Z_in i₁`).
* `tee_apply`: the impedance parameters of a T network, `[[Z_a + Z_c, Z_c], [Z_c, Z_b + Z_c]]`.
* Inverters (`Z₀₀ = Z₁₁ = 0`): `inverter_inputImpedance` (`Z_in = −Z₀₁ Z₁₀ / Z_L`; with
  `Z₀₁ = Z₁₀ = jX` this is `X² / Z_L`), `inverter_current` (the current `i₂ = v₁ / Z₀₁` into port 2
  is fixed by the input voltage, whatever the load), `inverter_voltage` (the voltage
  `v₂ = Z₁₀ i₁` at port 2 is fixed by the input current).
-/

noncomputable section

namespace powerlib.Grid.TwoPort

/-- The port equations of a two-port with impedance parameters `Z`, both currents into the
network. -/
def Equations (Z : Matrix (Fin 2) (Fin 2) ℂ) (v₁ v₂ i₁ i₂ : ℂ) : Prop :=
  v₁ = Z 0 0 * i₁ + Z 0 1 * i₂ ∧ v₂ = Z 1 0 * i₁ + Z 1 1 * i₂

/-- The two-port with port 2 terminated by the load impedance `Z_L` (`v₂ = −Z_L i₂`). -/
def Terminated (Z : Matrix (Fin 2) (Fin 2) ℂ) (ZL v₁ i₁ i₂ : ℂ) : Prop :=
  Equations Z v₁ (-(ZL * i₂)) i₁ i₂

/-- The input impedance of the two-port terminated by `Z_L`. -/
def inputImpedance (Z : Matrix (Fin 2) (Fin 2) ℂ) (ZL : ℂ) : ℂ :=
  Z 0 0 - Z 0 1 * Z 1 0 / (Z 1 1 + ZL)

/-- The T network: series arms `Z_a` (port 1) and `Z_b` (port 2), shunt `Z_c` between them. -/
def tee (Za Zb Zc : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![Za + Zc, Zc; Zc, Zb + Zc]

/-- The impedance parameters of the T network. -/
@[tmio T, powerlib_foundation] theorem tee_apply (Za Zb Zc : ℂ) :
    tee Za Zb Zc 0 0 = Za + Zc ∧ tee Za Zb Zc 0 1 = Zc ∧ tee Za Zb Zc 1 0 = Zc ∧
      tee Za Zb Zc 1 1 = Zb + Zc := by
  simp [tee]

/-- A terminated two-port carries the output current `i₂ = −Z₁₀ i₁ / (Z₁₁ + Z_L)`. -/
@[tmio T, powerlib_foundation] theorem terminated_current {Z : Matrix (Fin 2) (Fin 2) ℂ}
    {ZL v₁ i₁ i₂ : ℂ} (h : Terminated Z ZL v₁ i₁ i₂) (hd : Z 1 1 + ZL ≠ 0) :
    i₂ = -(Z 1 0 * i₁) / (Z 1 1 + ZL) := by
  rw [eq_div_iff hd]
  linear_combination -h.2

/-- The input port of a terminated two-port is its input impedance: `v₁ = Z_in i₁`. -/
@[tmio T, powerlib_foundation] theorem terminated_input {Z : Matrix (Fin 2) (Fin 2) ℂ}
    {ZL v₁ i₁ i₂ : ℂ} (h : Terminated Z ZL v₁ i₁ i₂) (hd : Z 1 1 + ZL ≠ 0) :
    v₁ = inputImpedance Z ZL * i₁ := by
  rw [h.1, terminated_current h hd, inputImpedance]
  field_simp
  ring

/-- An inverter (`Z₀₀ = Z₁₁ = 0`) turns the load into `−Z₀₁ Z₁₀ / Z_L`. -/
@[tmio T, powerlib_foundation] theorem inverter_inputImpedance {Z : Matrix (Fin 2) (Fin 2) ℂ}
    (h00 : Z 0 0 = 0) (h11 : Z 1 1 = 0) (ZL : ℂ) :
    inputImpedance Z ZL = -(Z 0 1 * Z 1 0) / ZL := by
  rw [inputImpedance, h00, h11, zero_add, zero_sub, neg_div]

/-- The current into port 2 of an inverter is fixed by the input voltage: `i₂ = v₁ / Z₀₁`,
whatever is connected to port 2. -/
@[tmio T, powerlib_foundation] theorem inverter_current {Z : Matrix (Fin 2) (Fin 2) ℂ}
    {v₁ v₂ i₁ i₂ : ℂ} (h00 : Z 0 0 = 0) (h : Equations Z v₁ v₂ i₁ i₂) (hz : Z 0 1 ≠ 0) :
    i₂ = v₁ / Z 0 1 := by
  rw [eq_div_iff hz, h.1, h00]
  ring

/-- The voltage at port 2 of an inverter is fixed by the input current: `v₂ = Z₁₀ i₁`,
whatever is connected to port 2. -/
@[tmio T, powerlib_foundation] theorem inverter_voltage {Z : Matrix (Fin 2) (Fin 2) ℂ}
    {v₁ v₂ i₁ i₂ : ℂ} (h11 : Z 1 1 = 0) (h : Equations Z v₁ v₂ i₁ i₂) :
    v₂ = Z 1 0 * i₁ := by
  rw [h.2, h11, zero_mul, add_zero]

end powerlib.Grid.TwoPort
