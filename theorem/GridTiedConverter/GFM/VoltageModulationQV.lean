import theorem.GridTiedConverter.GFM.VoltageModulation

/-! # Voltage-amplitude modulation of a synchronizing core with an arbitrary power map; Q–V droop

`VoltageModulation` derives the voltage pump for a constant EMF behind a lossless reactance. Here
the port power is an arbitrary smooth map `P(δ, V)` of the angle and the grid-voltage magnitude,
entering only through its partial derivatives at the operating point. This covers losses, other
power measurements and voltage controls acting through the EMF `E(δ, V)`. The pump depends on the
map only through two numbers, `κ₁ = V₀ P_δV/P_δ` (relative voltage sensitivity of the stiffness)
and `κ₂ = V₀ P_δδ P_V/P_δ²` (curvature times power sensitivity). The Q–V droop is worked out as an
instance.

Model boundary.
* VSG/droop core `(δ, Δω, P_f)`: `δ̇ = ω₀ Δω`, `2H Δω̇ = P* − P_f − D Δω`,
  `Ṗ_f = ω_c (P(δ, V) − P_f)`. `Core` holds `ω₀, H, D, ω_c` and `P_δ, P_V, P_δδ, P_δV` at
  `(δ₀, V₀)`; `A0`, `Bv = ∂f/∂V` and `A1` (the only modulable element `(P_f, δ)`,
  `ω_c(P_δδ z_δ + P_δV V̂)`) are stated in these derivatives. The linearization of a concrete map is
  `VoltageModulation.Model` (constant EMF) or `qv_partials` (Q–V droop).
* Quasi-static network; network sidebands are in `VoltageModulationNetwork`.
* Q–V droop: `E = E₀ − k_q(Q − Q*)` with the port reactive power `Q = (E² − E V cos δ)/X`, solved
  implicitly for `E(V)`, at no load `δ₀ = 0`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2 (framework: `A₁ = Σ (∂A/∂x_l) z_l + G û`, `g_m = l_mᴴ A₁ r_m*`,
`ĝ = 2|g|/Ω`), §3 (VSG core); the extension to voltage excitation and to an arbitrary power map is
new.

Results.
* `right_eig`, `left_eig`, `left_right` — eigentriple, `D(s) = s(s + a)(s + ω_c) + d₀`;
  `forcedV_eq` — voltage forcing `z_δ = −(ω₀ω_c P_V V̂/2H)/D(s)`.
* `pump_eq`, `rho_voltage` — `g = −(d₀/D'(λ)) ρ` with
  `ρ_V = (P_δδ z_δ + P_δV V̂)/P_δ = (V̂/V₀)(κ₁ − T(s) κ₂)`, `T = d₀/D(s)`.
* `charD_hopf`, `charP_hopf`, `pump_voltage_hopf` — at the Hopf point (`a ω_c = Ω²`,
  `d₀ = d₂Ω²`, `β = Ω/d₂`): `g_V = (jΩ/2)(V̂/V₀)(κ₁(3 + 6jβ) + κ₂)/((3 + 6jβ)(1 + jβ))`;
  `ghat_voltage` — `ĝ_V² = v̂²((3κ₁ + κ₂)² + 36β²κ₁²)/((9 + 36β²)(1 + β²))`.
* `lossless_kappa` — constant EMF, lossless link: `κ₁ = 1`, `κ₂ = −tan² δ₀` (recovers
  `VoltageModulation.ghat_voltage`).
* `qv_dEdV`, `qv_partials`, `qv_noload_kappa`, `ghat_kappa_noload` — Q–V droop at no load:
  `dE/dV = k_q E/(X + k_q(2E − V₀))`, `κ₁ = 1 + k_q V₀/(X + k_q(2E − V₀))`, `κ₂ = 0`,
  `ĝ_V² = v̂² κ₁²/(1 + β²)`: the droop raises the EMF with the grid voltage and strengthens the
  voltage pump.

Corrections.
None: an extension.

Family and connection conclusions.
None: static evidence on the synchronizing core (eigentriple, forced response, pump coefficient).
-/

noncomputable section
namespace powerlib.GFM
namespace VoltageModulation
open Complex Matrix
open powerlib.ParametricResonance

/-- The VSG/droop synchronizing core with an arbitrary smooth power map `P(δ, V)`, through its
partial derivatives at the operating point: `P_δ` (the synchronizing coefficient), `P_V`,
`P_δδ`, `P_δV`. -/
structure Core where
  ω0 : ℝ
  H : ℝ
  D : ℝ
  ωc : ℝ
  Pδ : ℝ
  PV : ℝ
  Pδδ : ℝ
  PδV : ℝ

namespace Core

variable (c : Core)

def A0 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, (c.ω0 : ℂ), 0; 0, -(c.D : ℂ) / (2 * c.H), -1 / (2 * (c.H : ℂ)); c.ωc * c.Pδ, 0, -(c.ωc : ℂ)]
def Bv : Fin 3 → ℂ := ![0, 0, c.ωc * c.PV]
/-- `A₁`: the element `(P_f, δ)` is modulated by `P_δδ z_δ + P_δV V̂`. -/
def A1 (zδ zV : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0; 0, 0, 0; c.ωc * (c.Pδδ * zδ + c.PδV * zV), 0, 0]

def a : ℂ := (c.D : ℂ) / (2 * c.H)
def d0 : ℂ := c.ω0 * c.ωc * c.Pδ / (2 * c.H)
def charP (s : ℂ) : ℂ := s * (s + c.a) * (s + c.ωc) + c.d0
def charD (s : ℂ) : ℂ := 3 * s ^ 2 + 2 * (c.a + c.ωc) * s + c.a * c.ωc
def right (s : ℂ) : Fin 3 → ℂ := ![1, s / c.ω0, -(2 * c.H * s + c.D) * s / c.ω0]
def left (s : ℂ) : Fin 3 → ℂ :=
  let k := -(c.ω0 : ℂ) / (2 * c.H * c.charD s)
  ![k * (-(2 * c.H * (s + c.ωc) * (s + c.a)) / c.ω0), k * (-(2 * c.H * (s + c.ωc))), k]

/-- Forced angle to `V̂`: `z_δ = −(ω₀ω_c P_V V̂/2H)/D(s)`. -/
def forcedVδ (s V : ℂ) : ℂ := -(c.ω0 * c.ωc * c.PV * V / (2 * c.H)) / c.charP s
def forcedV (s V : ℂ) : Fin 3 → ℂ :=
  let z := c.forcedVδ s V
  ![z, s * z / c.ω0, -(2 * c.H * s + c.D) * s * z / c.ω0]

/-- The two voltage sensitivities of the synchronizing element:
`κ₁ = V₀ P_δV/P_δ` (relative change of the stiffness with `V`) and
`κ₂ = V₀ P_δδ P_V/P_δ²` (curvature times the power sensitivity). -/
def κ1 (V0 : ℝ) : ℝ := V0 * c.PδV / c.Pδ
def κ2 (V0 : ℝ) : ℝ := V0 * c.Pδδ * c.PV / c.Pδ ^ 2

@[tmio M, powerlib_domain] theorem right_eig {s : ℂ} (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hs : c.charP s = 0) : c.A0 *ᵥ c.right s = s • c.right s := by
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  simp only [charP, a, d0] at hs
  funext i
  fin_cases i
  · simp [A0, right, mulVec, dotProduct, Fin.sum_univ_three]; field_simp
  · simp [A0, right, mulVec, dotProduct, Fin.sum_univ_three]; field_simp; ring
  · simp [A0, right, mulVec, dotProduct, Fin.sum_univ_three]
    field_simp
    linear_combination (norm := (field_simp; ring)) (2 * (c.H : ℂ)) * hs

@[tmio M, powerlib_domain] theorem left_eig {s : ℂ} (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hs : c.charP s = 0) : c.left s ᵥ* c.A0 = s • c.left s := by
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  simp only [charP, d0] at hs
  simp only [left]
  generalize -(c.ω0 : ℂ) / (2 * c.H * c.charD s) = k
  funext i
  fin_cases i
  · simp [A0, vecMul, dotProduct, Fin.sum_univ_three]
    linear_combination (norm := (field_simp; ring)) (k * (2 * c.H / c.ω0)) * hs
  · simp [A0, vecMul, dotProduct, Fin.sum_univ_three, a]; field_simp; ring
  · simp [A0, vecMul, dotProduct, Fin.sum_univ_three]; field_simp; ring

@[tmio M, powerlib_domain] theorem left_right {s : ℂ} (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hD : c.charD s ≠ 0) : c.left s ⬝ᵥ c.right s = 1 := by
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  have key : -(2 * (c.H : ℂ) * (s + c.ωc) * (s + c.a)) / c.ω0 * 1 +
      -(2 * (c.H : ℂ) * (s + c.ωc)) * (s / c.ω0) + 1 * (-(2 * c.H * s + c.D) * s / c.ω0) =
      -(2 * c.H / c.ω0) * c.charD s := by
    simp only [charD, a]; field_simp; ring
  simp only [left, right, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  calc _ = -(c.ω0 : ℂ) / (2 * c.H * c.charD s) *
        (-(2 * (c.H : ℂ) * (s + c.ωc) * (s + c.a)) / c.ω0 * 1 +
          -(2 * (c.H : ℂ) * (s + c.ωc)) * (s / c.ω0) + 1 * (-(2 * c.H * s + c.D) * s / c.ω0)) := by
        ring
    _ = 1 := by rw [key]; field_simp

@[tmio M, powerlib_domain] theorem forcedV_eq {s : ℂ} (V : ℂ) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0)
    (hs : c.charP s ≠ 0) :
    (s • (1 : Matrix (Fin 3) (Fin 3) ℂ) - c.A0) *ᵥ c.forcedV s V = V • c.Bv := by
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  simp only [forcedV, forcedVδ]
  generalize hP : c.charP s = P at hs
  simp only [charP, d0] at hP
  funext i
  fin_cases i
  · simp [A0, Bv, mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply]; field_simp; ring
  · simp [A0, Bv, mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply]; field_simp; ring
  · simp [A0, Bv, mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply]
    field_simp
    linear_combination (norm := (simp only [a]; field_simp; ring))
      ((c.ωc : ℂ) * c.PV * V * 2 * c.H) * hP

/-- `g = w ρ`, `w = −d₀/D'(λ)`, `ρ = (P_δδ z_δ + P_δV V̂)/P_δ`. -/
@[tmio M, powerlib_domain] theorem pump_eq (s zδ zV : ℂ) (hPδ : c.Pδ ≠ 0) :
    Element.pump (c.A1 zδ zV) (c.left s) (c.right s) =
      -(c.d0 / c.charD s) * ((c.Pδδ * zδ + c.PδV * zV) / c.Pδ) := by
  have hP : (c.Pδ : ℂ) ≠ 0 := by exact_mod_cast hPδ
  simp [Element.pump, A1, left, right, d0, mulVec, dotProduct, Fin.sum_univ_three]
  field_simp

/-- Voltage forcing: `ρ_V = (V̂/V₀)(κ₁ − T(s) κ₂)`, `T = d₀/D(s)`. -/
@[tmio M, powerlib_domain] theorem rho_voltage (s V : ℂ) (V0 : ℝ) (hPδ : c.Pδ ≠ 0) (hV0 : V0 ≠ 0)
    (hH : c.H ≠ 0) :
    (c.Pδδ * c.forcedVδ s V + c.PδV * V) / c.Pδ =
      V / V0 * ((c.κ1 V0 : ℂ) - c.d0 / c.charP s * (c.κ2 V0 : ℂ)) := by
  have hP : (c.Pδ : ℂ) ≠ 0 := by exact_mod_cast hPδ
  have hV : (V0 : ℂ) ≠ 0 := by exact_mod_cast hV0
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  simp only [forcedVδ, κ1, κ2, d0]
  push_cast
  generalize c.charP s = P
  rcases eq_or_ne P 0 with h | h
  · simp [h]; field_simp
  field_simp
  ring

/-! ### At the Hopf point -/

def d2 : ℝ := c.D / (2 * c.H) + c.ωc

@[tmio M, powerlib_domain] theorem a_add_ωc : c.a + (c.ωc : ℂ) = (c.d2 : ℂ) := by simp [a, d2]

@[tmio M, powerlib_domain] theorem charD_hopf (Ω : ℝ) (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) :
    c.charD (Ω * I) = 2 * (Ω * I) * (c.a + c.ωc + Ω * I) := by
  simp only [charD]
  linear_combination hH1 + ((Ω : ℂ) ^ 2) * I_sq

@[tmio M, powerlib_domain] theorem charP_hopf (Ω : ℝ) (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2)
    (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2) :
    c.charP (2 * Ω * I) = -3 * (Ω : ℂ) ^ 2 * (c.a + c.ωc + 2 * Ω * I) := by
  simp only [charP]
  rw [hH2]
  linear_combination (2 * (Ω : ℂ) * I) * hH1 +
    (8 * (Ω : ℂ) ^ 3 * I + 4 * (Ω : ℂ) ^ 2 * (c.a + c.ωc)) * I_sq

/-- The voltage pump at the Hopf point:
`g_V = (jΩ/2) v̂ (κ₁(3 + 6jβ) + κ₂)/((3 + 6jβ)(1 + jβ))`, `β = Ω/d₂`. -/
@[tmio M, powerlib_domain] theorem pump_voltage_hopf (V0 Ω : ℝ) (V : ℂ) (hPδ : c.Pδ ≠ 0)
    (hV0 : V0 ≠ 0) (hH : c.H ≠ 0) (hΩ : Ω ≠ 0) (hd2 : c.d2 ≠ 0)
    (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2) :
    Element.pump (c.A1 (c.forcedVδ (2 * Ω * I) V) V) (c.left (Ω * I)) (c.right (Ω * I)) =
      Ω * I / 2 * (V / V0) * ((c.κ1 V0 : ℂ) * (3 + 6 * ((Ω / c.d2 : ℝ) : ℂ) * I) + (c.κ2 V0 : ℂ)) /
        ((3 + 6 * ((Ω / c.d2 : ℝ) : ℂ) * I) * (1 + ((Ω / c.d2 : ℝ) : ℂ) * I)) := by
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
  have hdc : (c.d2 : ℂ) ≠ 0 := by exact_mod_cast hd2
  have hP2 := c.charP_hopf Ω hH1 hH2
  rw [a_add_ωc] at hP2 hH2
  have hn1 : (c.d2 : ℂ) + 2 * Ω * I ≠ 0 := by
    have := Model.add_mul_I_ne (x := c.d2) (y := 2 * Ω) (by positivity); push_cast at this
    exact this
  have hn2 : (c.d2 : ℂ) + Ω * I ≠ 0 := Model.add_mul_I_ne hΩ
  rw [c.pump_eq _ _ _ hPδ, c.rho_voltage _ V V0 hPδ hV0 hH, c.charD_hopf Ω hH1, hP2, hH2,
    a_add_ωc]
  push_cast
  have hb1 : (1 : ℂ) + Ω / c.d2 * I ≠ 0 := by
    have : (1 : ℂ) + Ω / c.d2 * I = ((c.d2 : ℂ) + Ω * I) / c.d2 := by field_simp
    rw [this]; exact div_ne_zero hn2 hdc
  have hb3 : (3 : ℂ) + 6 * (Ω / c.d2) * I ≠ 0 := by
    have : (3 : ℂ) + 6 * (Ω / c.d2) * I = 3 * ((c.d2 : ℂ) + 2 * Ω * I) / c.d2 := by
      field_simp; ring
    rw [this]; exact div_ne_zero (mul_ne_zero (by norm_num) hn1) hdc
  have hn1' : (c.d2 : ℂ) + Ω * 2 * I ≠ 0 := by rw [mul_comm (Ω : ℂ) 2]; exact hn1
  have hn3 : (c.d2 : ℂ) * 3 + Ω * I * 6 ≠ 0 := by
    have : (c.d2 : ℂ) * 3 + Ω * I * 6 = 3 * ((c.d2 : ℂ) + 2 * Ω * I) := by ring
    rw [this]; exact mul_ne_zero (by norm_num) hn1
  field_simp
  linear_combination (-(V * ((c.κ1 V0 : ℂ) * ((c.d2 : ℂ) * 3 + Ω * I * 6) + c.d2 * (c.κ2 V0 : ℂ)) *
    ((c.d2 : ℂ) * 3 + Ω * I * 6) / V0)) * I_sq

@[tmio T, powerlib_foundation] theorem normSq_kappa_form (Ω x k1 k2 β : ℝ) :
    Complex.normSq (Ω * I / 2 * x * ((k1 : ℂ) * (3 + 6 * (β : ℂ) * I) + (k2 : ℂ)) /
      ((3 + 6 * (β : ℂ) * I) * (1 + β * I))) =
      Ω ^ 2 / 4 * x ^ 2 * ((3 * k1 + k2) ^ 2 + 36 * β ^ 2 * k1 ^ 2) /
        ((9 + 36 * β ^ 2) * (1 + β ^ 2)) := by
  simp only [map_div₀, map_mul]
  simp [Complex.normSq_apply]
  have : (0 : ℝ) < (9 + 36 * β ^ 2) * (1 + β ^ 2) := by positivity
  field_simp
  ring

/-- The normalized pump strength of voltage-amplitude modulation for any power map:
`ĝ_V² = v̂² ((3κ₁ + κ₂)² + 36β²κ₁²)/((9 + 36β²)(1 + β²))`. -/
@[tmio M, powerlib_domain] theorem ghat_voltage (V0 Ω V : ℝ) (hPδ : c.Pδ ≠ 0) (hV0 : V0 ≠ 0)
    (hH : c.H ≠ 0) (hΩ : Ω ≠ 0) (hd2 : c.d2 ≠ 0)
    (hH1 : c.a * c.ωc = (Ω : ℂ) ^ 2) (hH2 : c.d0 = (c.a + c.ωc) * (Ω : ℂ) ^ 2) :
    (2 * ‖Element.pump (c.A1 (c.forcedVδ (2 * Ω * I) V) V) (c.left (Ω * I))
        (c.right (Ω * I))‖ / Ω) ^ 2 =
      (V / V0) ^ 2 * ((3 * c.κ1 V0 + c.κ2 V0) ^ 2 + 36 * (Ω / c.d2) ^ 2 * c.κ1 V0 ^ 2) /
        ((9 + 36 * (Ω / c.d2) ^ 2) * (1 + (Ω / c.d2) ^ 2)) := by
  rw [c.pump_voltage_hopf V0 Ω V hPδ hV0 hH hΩ hd2 hH1 hH2]
  have h := normSq_kappa_form Ω (V / V0) (c.κ1 V0) (c.κ2 V0) (Ω / c.d2)
  rw [div_pow, mul_pow, Complex.sq_norm]
  push_cast at h ⊢
  rw [h]
  have : (0 : ℝ) < (9 + 36 * (Ω / c.d2) ^ 2) * (1 + (Ω / c.d2) ^ 2) := by positivity
  field_simp
  ring

/-! ### Instances: the lossless link and the Q–V droop -/

/-- Constant EMF, lossless link: `P = E V sin δ/X` gives `κ₁ = 1`, `κ₂ = −tan² δ₀`
(`VoltageModulation.Model`). -/
@[tmio M, powerlib_domain] theorem lossless_kappa (ω0 H D ωc E X δ0 V0 : ℝ) (hE : E ≠ 0) (hX : X ≠ 0)
    (hV0 : V0 ≠ 0) (hc : Real.cos δ0 ≠ 0) :
    let c : Core := ⟨ω0, H, D, ωc, E * V0 * Real.cos δ0 / X, E * Real.sin δ0 / X,
      -(E * V0 * Real.sin δ0 / X), E * Real.cos δ0 / X⟩
    c.κ1 V0 = 1 ∧ c.κ2 V0 = -Real.tan δ0 ^ 2 := by
  intro c
  constructor
  · simp only [κ1, c]; field_simp
  · simp only [κ2, c, Real.tan_eq_sin_div_cos]; field_simp

/-- Q–V droop `E = E₀ − k_q(Q − Q*)` with the port reactive power `Q = (E² − E V cos δ)/X`, at no
load (`δ₀ = 0`): implicit differentiation of the droop law along `V` gives
`dE/dV = k_q E/(X + k_q(2E − V))`. -/
@[tmio M, powerlib_domain] theorem qv_dEdV {Ef : ℝ → ℝ} {E0 kq Qs X V0 EV : ℝ}
    (hdroop : ∀ V, Ef V = E0 - kq * ((Ef V ^ 2 - Ef V * V) / X - Qs))
    (hd : HasDerivAt Ef EV V0) (hX : X ≠ 0) (hden : X + kq * (2 * Ef V0 - V0) ≠ 0) :
    EV = kq * Ef V0 / (X + kq * (2 * Ef V0 - V0)) := by
  have h1 : HasDerivAt (fun V => E0 - kq * ((Ef V ^ 2 - Ef V * V) / X - Qs))
      (-(kq * ((2 * Ef V0 * EV - (EV * V0 + Ef V0 * 1)) / X))) V0 := by
    have h := (((hd.pow 2).sub (hd.mul (hasDerivAt_id V0))).div_const X).sub_const Qs
      |>.const_mul kq |>.const_sub E0
    convert h using 1
    · funext V; simp
    · simp
  have h2 : HasDerivAt Ef (-(kq * ((2 * Ef V0 * EV - (EV * V0 + Ef V0 * 1)) / X))) V0 :=
    h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun V => hdroop V)
  have heq := hd.unique h2
  rw [eq_div_iff hden]
  field_simp at heq
  linarith

/-- The Q–V core at no load. With `P(δ, V) = E(δ, V) V sin δ/X`: `P_δ = E V₀/X`, `P_V = 0`,
`P_δV = (E + V₀ dE/dV)/X` (`qv_partials`), so `κ₂ = 0` and `κ₁ = 1 + V₀ (dE/dV)/E`. -/
def qvCore (ω0 H D ωc X V0 E EV Pδδ : ℝ) : Core :=
  ⟨ω0, H, D, ωc, E * V0 / X, 0, Pδδ, (E + V0 * EV) / X⟩

@[tmio M, powerlib_domain] theorem qv_partials {E2 : ℝ → ℝ → ℝ} {X V0 Eδ EV : ℝ}
    (hδ : ∀ V, HasDerivAt (fun δ => E2 δ V) (Eδ) 0) (hV : HasDerivAt (E2 0) EV V0) :
    HasDerivAt (fun δ => E2 δ V0 * V0 * Real.sin δ / X) (E2 0 V0 * V0 / X) 0 ∧
      HasDerivAt (fun V => E2 0 V * V * Real.sin 0 / X) 0 V0 ∧
      (∀ V, HasDerivAt (fun δ => E2 δ V * V * Real.sin δ / X) (E2 0 V * V / X) 0) ∧
      HasDerivAt (fun V => E2 0 V * V / X) ((E2 0 V0 + V0 * EV) / X) V0 := by
  have hs : ∀ V, HasDerivAt (fun δ => E2 δ V * V * Real.sin δ / X) (E2 0 V * V / X) 0 := by
    intro V
    have h := (((hδ V).mul_const V).mul (Real.hasDerivAt_sin 0)).div_const X
    convert h using 1
    simp
  refine ⟨hs V0, ?_, hs, ?_⟩
  · simpa using hasDerivAt_const V0 (0 : ℝ)
  · have h := (hV.mul (hasDerivAt_id V0)).div_const X
    convert h using 1
    · funext V; simp
    · simp; ring

/-- Q–V droop at no load: `κ₁ = 1 + k_q V₀/(X + k_q(2E − V₀))`, `κ₂ = 0`: the droop raises the EMF
with the grid voltage and strengthens the direct stiffness modulation, `ĝ_V² = v̂² κ₁²/(1 + β²)`. -/
@[tmio M, powerlib_domain] theorem qv_noload_kappa {Ef : ℝ → ℝ} {ω0 H D ωc E0 kq Qs X V0 EV Pδδ : ℝ}
    (hdroop : ∀ V, Ef V = E0 - kq * ((Ef V ^ 2 - Ef V * V) / X - Qs))
    (hd : HasDerivAt Ef EV V0) (hX : X ≠ 0) (hden : X + kq * (2 * Ef V0 - V0) ≠ 0)
    (hE : Ef V0 ≠ 0) (hV0 : V0 ≠ 0) :
    (qvCore ω0 H D ωc X V0 (Ef V0) EV Pδδ).κ1 V0 = 1 + kq * V0 / (X + kq * (2 * Ef V0 - V0)) ∧
      (qvCore ω0 H D ωc X V0 (Ef V0) EV Pδδ).κ2 V0 = 0 := by
  rw [qv_dEdV hdroop hd hX hden]
  constructor
  · simp only [κ1, qvCore]
    field_simp
  · simp [κ2, qvCore]

@[tmio M, powerlib_domain] theorem ghat_kappa_noload (κ1 β x : ℝ) :
    x ^ 2 * ((3 * κ1 + 0) ^ 2 + 36 * β ^ 2 * κ1 ^ 2) / ((9 + 36 * β ^ 2) * (1 + β ^ 2)) =
      x ^ 2 * κ1 ^ 2 / (1 + β ^ 2) := by
  have : (0 : ℝ) < 9 + 36 * β ^ 2 := by positivity
  have : (0 : ℝ) < 1 + β ^ 2 := by positivity
  field_simp
  ring

end Core
end VoltageModulation
end powerlib.GFM
