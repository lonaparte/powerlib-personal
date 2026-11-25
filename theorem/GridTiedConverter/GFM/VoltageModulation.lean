import theorem.ParametricResonance.ElementDecomposition

/-! # Grid-voltage amplitude modulation: parametric excitation of the synchronizing stiffness

The unified framework of the source takes the grid angle as the excitation; there the angle enters
the network additively, so `A₁` comes only from the modulation along the forced trajectory and the
pump is proportional to `tan δ₀`. This file takes the grid-voltage magnitude
`V(t) = V₀ + ε Re{V̂ e^{jω_p t}}` instead. The synchronizing coefficient `K = E V cos δ/X` is
proportional to `V`, so `G = ∂A/∂V ≠ 0`: the modulation acts directly on the stiffness (a
Mathieu-type excitation), on top of the curvature along the forced angle. The pump coefficient is
derived exactly on the VSG synchronizing core and compared with grid-angle modulation of the same
core.

Model boundary.
* VSG core `(δ, Δω, P_f)` with a quasi-static lossless link (`field`):
  `δ̇ = ω₀ Δω − θ̇_g`, `2H Δω̇ = P* − P_f − D Δω`, `Ṗ_f = ω_c (E V sin δ/X − P_f)`, constant EMF `E`
  (no Q–V droop), power measured at the EMF; grid-voltage magnitude `V` and grid angle `θ_g` as
  inputs. Droop is the same cubic core (`DroopTwoFilter`).
* Linearization at `(δ₀, V₀)`: the only state- or input-dependent element is `(P_f, δ) = ω_c K₀`
  (`hasDerivAt_Pw_δ`, `A0`); `∂f/∂V` (`hasDerivAt_Pw_V`, `Bv`); `A₁` is the derivative of `ω_c K`
  along `(δ₀, V₀) + t (z_δ, V̂)` (`line_K`, `A1`).
* Network sidebands (the `μ_p` terms of a dynamic link) are not included.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07) §2 (framework:
`A₁ = Σ (∂A/∂x_l) z_l + G û`, `g_m = l_mᴴ A₁ r_m*`, `ε_crit = 4(σ_m/Ω_m)/ĝ_m`, `ĝ = 2|g|/Ω`),
§3 (VSG core), §5.2 (2:1 kinematic factor); the extension to voltage-amplitude excitation is new.

Results.
* `right_eig`, `left_eig`, `left_right` — eigentriple of the core,
  `D(s) = s(s + a)(s + ω_c) + d₀`, `a = D/2H`, `d₀ = ω₀ω_c K₀/2H`.
* `forcedV_eq`, `forcedVδ_eq` — voltage forcing: `z_δ = −T(s) tan δ₀ V̂/V₀`, `T = d₀/D(s)`;
  `forcedθ_eq`, `forcedθδ_eq` — angle forcing: `z_δ = −S(s) θ̂`, `S = 1 − T`.
* `weight_K`, `pump_eq` — `g = w ρ`, `w = −d₀/D'(λ)`, `ρ = −tan δ₀ z_δ + V̂/V₀`; `rho_forced` —
  `ρ_V = (V̂/V₀)(1 + T tan² δ₀)` and `ρ_θ = tan δ₀ S θ̂`.
* At the Hopf point (`aω_c = Ω²`, `d₀ = d₂Ω²`, `β = Ω/d₂`): `pump_voltage_hopf`
  (`g_V = (jΩ/2) v̂ (3 + 6jβ − tan² δ₀)/((3 + 6jβ)(1 + jβ))`), `pump_angle_hopf`
  (`g_θ = (jΩ/2) θ̂ tan δ₀ (4 + 6jβ)/((3 + 6jβ)(1 + jβ))`).
* `ghat_voltage` (`ĝ_V² = v̂²((3 − t)² + 36β²)/((9 + 36β²)(1 + β²))`, `t = tan² δ₀`), `ghat_angle`
  (`ĝ_θ² = θ̂² t (16 + 36β²)/((9 + 36β²)(1 + β²))`).
* `noload` — at `δ₀ = 0` the angle pump vanishes and `ĝ_V² = v̂²/(1 + β²)`;
  `voltage_factor_pos` — the voltage pump vanishes only for `β = 0`, `tan² δ₀ = 3`;
  `voltage_vs_angle` — per unit modulation the voltage pump is the stronger one iff
  `(3 − t)² + 36β² > t(16 + 36β²)` (for `β → 0`: `δ₀ ≲ 33°`).

Corrections.
None: an extension. Voltage-amplitude modulation at `ω_p ≈ 2Ω_m` excites the synchronizing mode
parametrically with `ε_crit = 4(σ_m/Ω_m)/ĝ_V` in relative amplitude, also at no load, where
grid-angle modulation does not pump this core.

Family and connection conclusions.
None: static evidence on the VSG/droop core (linearization, forced response, pump coefficient).
-/

noncomputable section
namespace powerlib.GFM
namespace VoltageModulation
open Complex Matrix
open powerlib.ParametricResonance

/-- Parameters of the VSG synchronizing core `(δ, Δω, P_f)` with a quasi-static lossless link:
`δ̇ = ω₀ Δω − θ̇_g`, `2H Δω̇ = P* − P_f − D Δω`, `Ṗ_f = ω_c (E V sin δ/X − P_f)`. -/
structure Model where
  ω0 : ℝ
  H : ℝ
  D : ℝ
  ωc : ℝ
  E : ℝ
  X : ℝ

namespace Model

variable (p : Model)

/-- The power `E V sin δ/X` and the synchronizing coefficient `E V cos δ/X` (complexified). -/
def Pw (δ V : ℂ) : ℂ := p.E * V * Complex.sin δ / p.X
def Kc (δ V : ℂ) : ℂ := p.E * V * Complex.cos δ / p.X

/-- The field in the coordinates `(δ, Δω, P_f)` with grid-voltage magnitude `V` and the rate
`θ̇_g` of the grid angle as inputs. -/
def field (Pst V θgd : ℂ) (x : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![p.ω0 * x 1 - θgd, (Pst - x 2 - p.D * x 1) / (2 * p.H), p.ωc * (p.Pw (x 0) V - x 2)]

@[tmio M, powerlib_domain] theorem hasDerivAt_Pw_δ (δ V : ℂ) :
    HasDerivAt (fun δ => p.Pw δ V) (p.Kc δ V) δ := by
  have h := ((Complex.hasDerivAt_sin δ).const_mul ((p.E : ℂ) * V)).div_const (p.X : ℂ)
  convert h using 1
  · funext x; simp [Pw]
  · simp [Kc]

@[tmio M, powerlib_domain] theorem hasDerivAt_Pw_V (δ V : ℂ) :
    HasDerivAt (fun V => p.Pw δ V) (p.E * Complex.sin δ / p.X) V := by
  have h := (((hasDerivAt_id V).const_mul (p.E : ℂ)).mul_const (Complex.sin δ)).div_const (p.X : ℂ)
  convert h using 1
  · funext x; simp [Pw]
  · simp

/-- The modulation of the synchronizing coefficient along `(δ, V) + t (z_δ, V̂)`:
`d/dt K = −P z_δ + (E cos δ/X) V̂`. -/
@[tmio M, powerlib_domain] theorem line_K (δ V zδ zV : ℂ) :
    HasDerivAt (fun t : ℂ => p.Kc (δ + t * zδ) (V + t * zV))
      (-p.Pw δ V * zδ + p.E * Complex.cos δ / p.X * zV) 0 := by
  have hδ : HasDerivAt (fun t : ℂ => δ + t * zδ) zδ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const zδ).const_add δ
  have hV : HasDerivAt (fun t : ℂ => V + t * zV) zV 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const zV).const_add V
  have hc := (Complex.hasDerivAt_cos (δ + 0 * zδ)).comp (0 : ℂ) hδ
  have h := ((hV.const_mul (p.E : ℂ)).mul hc).div_const (p.X : ℂ)
  convert h using 1
  · funext t; simp [Kc, Function.comp, mul_assoc]
  · simp [Pw]; ring

/-! ### The linearization at `(δ₀, V₀)` -/

/-- `A₀`: the only state-dependent element is `(P_f, δ) = ω_c K₀`, `K₀ = E V₀ cos δ₀/X`. -/
def A0 (δ0 V0 : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, (p.ω0 : ℂ), 0;
    0, -(p.D : ℂ) / (2 * p.H), -1 / (2 * (p.H : ℂ));
    p.ωc * p.Kc δ0 V0, 0, -(p.ωc : ℂ)]

/-- `∂f/∂V`. -/
def Bv (δ0 : ℝ) : Fin 3 → ℂ := ![0, 0, p.ωc * (p.E * Complex.sin δ0 / p.X)]

/-- `A₁ = Σ_l (∂A/∂x_l) z_l + (∂A/∂V) V̂`: only the element `(P_f, δ)` is modulated. -/
def A1 (δ0 V0 : ℝ) (zδ zV : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0; 0, 0, 0;
    p.ωc * (-p.Pw δ0 V0 * zδ + p.E * Complex.cos δ0 / p.X * zV), 0, 0]

/-- `a = D/2H` and `d₀ = ω₀ ω_c K₀/2H`. -/
def a : ℂ := (p.D : ℂ) / (2 * p.H)
def d0 (δ0 V0 : ℝ) : ℂ := p.ω0 * p.ωc * p.Kc δ0 V0 / (2 * p.H)
/-- Characteristic polynomial `D(s) = s(s + a)(s + ω_c) + d₀` and its derivative. -/
def charP (δ0 V0 : ℝ) (s : ℂ) : ℂ := s * (s + p.a) * (s + p.ωc) + p.d0 δ0 V0
def charD (s : ℂ) : ℂ := 3 * s ^ 2 + 2 * (p.a + p.ωc) * s + p.a * p.ωc

def right (s : ℂ) : Fin 3 → ℂ := ![1, s / p.ω0, -(2 * p.H * s + p.D) * s / p.ω0]
def left (s : ℂ) : Fin 3 → ℂ :=
  let c := -(p.ω0 : ℂ) / (2 * p.H * p.charD s)
  ![c * (-(2 * p.H * (s + p.ωc) * (s + p.a)) / p.ω0), c * (-(2 * p.H * (s + p.ωc))), c]

@[tmio M, powerlib_domain] theorem right_eig (δ0 V0 : ℝ) {s : ℂ} (hω0 : p.ω0 ≠ 0) (hH : p.H ≠ 0)
    (hs : p.charP δ0 V0 s = 0) : p.A0 δ0 V0 *ᵥ p.right s = s • p.right s := by
  have hω : (p.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (p.H : ℂ) ≠ 0 := by exact_mod_cast hH
  simp only [charP, a, d0] at hs
  funext i
  fin_cases i
  · simp [A0, right, mulVec, dotProduct, Fin.sum_univ_three]; field_simp
  · simp [A0, right, mulVec, dotProduct, Fin.sum_univ_three]; field_simp; ring
  · simp [A0, right, mulVec, dotProduct, Fin.sum_univ_three]
    field_simp
    linear_combination (norm := (field_simp; ring)) (2 * (p.H : ℂ)) * hs

@[tmio M, powerlib_domain] theorem left_eig (δ0 V0 : ℝ) {s : ℂ} (hω0 : p.ω0 ≠ 0) (hH : p.H ≠ 0)
    (hs : p.charP δ0 V0 s = 0) : p.left s ᵥ* p.A0 δ0 V0 = s • p.left s := by
  have hω : (p.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (p.H : ℂ) ≠ 0 := by exact_mod_cast hH
  simp only [charP, d0] at hs
  simp only [left]
  generalize -(p.ω0 : ℂ) / (2 * p.H * p.charD s) = c
  funext i
  fin_cases i
  · simp [A0, vecMul, dotProduct, Fin.sum_univ_three]
    linear_combination (norm := (field_simp; ring)) (c * (2 * p.H / p.ω0)) * hs
  · simp [A0, vecMul, dotProduct, Fin.sum_univ_three, a]; field_simp; ring
  · simp [A0, vecMul, dotProduct, Fin.sum_univ_three]; field_simp; ring

/-- `u r = 1`. -/
@[tmio M, powerlib_domain] theorem left_right {s : ℂ} (hω0 : p.ω0 ≠ 0) (hH : p.H ≠ 0)
    (hD : p.charD s ≠ 0) : p.left s ⬝ᵥ p.right s = 1 := by
  have hω : (p.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (p.H : ℂ) ≠ 0 := by exact_mod_cast hH
  have key : -(2 * (p.H : ℂ) * (s + p.ωc) * (s + p.a)) / p.ω0 * 1 +
      -(2 * (p.H : ℂ) * (s + p.ωc)) * (s / p.ω0) + 1 * (-(2 * p.H * s + p.D) * s / p.ω0) =
      -(2 * p.H / p.ω0) * p.charD s := by
    simp only [charD, a]; field_simp; ring
  simp only [left, right, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  calc _ = -(p.ω0 : ℂ) / (2 * p.H * p.charD s) *
        (-(2 * (p.H : ℂ) * (s + p.ωc) * (s + p.a)) / p.ω0 * 1 +
          -(2 * (p.H : ℂ) * (s + p.ωc)) * (s / p.ω0) + 1 * (-(2 * p.H * s + p.D) * s / p.ω0)) := by
        ring
    _ = 1 := by rw [key]; field_simp

/-! ### Forced responses and the pump coefficient -/

/-- Forced angle `z_δ(s)` to the grid-voltage phasor `V̂`. -/
def forcedVδ (δ0 V0 : ℝ) (s V : ℂ) : ℂ :=
  -(p.ω0 * p.ωc * (p.E * Complex.sin δ0 / p.X) * V / (2 * p.H)) / p.charP δ0 V0 s
def forcedV (δ0 V0 : ℝ) (s V : ℂ) : Fin 3 → ℂ :=
  let z := p.forcedVδ δ0 V0 s V
  ![z, s * z / p.ω0, -(2 * p.H * s + p.D) * s * z / p.ω0]

/-- Forced angle `z_δ(s)` to the grid-angle phasor `θ̂` (input `θ̇_g = s θ̂`). -/
def forcedθδ (δ0 V0 : ℝ) (s θ : ℂ) : ℂ :=
  -(s * (s + p.a) * (s + p.ωc) / p.charP δ0 V0 s) * θ
def forcedθ (δ0 V0 : ℝ) (s θ : ℂ) : Fin 3 → ℂ :=
  let z := p.forcedθδ δ0 V0 s θ
  ![z, s * (z + θ) / p.ω0, -(2 * p.H * s + p.D) * s * (z + θ) / p.ω0]

@[tmio M, powerlib_domain] theorem forcedV_eq (δ0 V0 : ℝ) {s : ℂ} (V : ℂ) (hω0 : p.ω0 ≠ 0)
    (hH : p.H ≠ 0) (hs : p.charP δ0 V0 s ≠ 0) :
    (s • (1 : Matrix (Fin 3) (Fin 3) ℂ) - p.A0 δ0 V0) *ᵥ p.forcedV δ0 V0 s V = V • p.Bv δ0 := by
  have hω : (p.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (p.H : ℂ) ≠ 0 := by exact_mod_cast hH
  simp only [forcedV, forcedVδ]
  generalize hP : p.charP δ0 V0 s = P at hs
  simp only [charP, d0] at hP
  funext i
  fin_cases i
  · simp [A0, Bv, mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply]; field_simp; ring
  · simp [A0, Bv, mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply]; field_simp; ring
  · simp [A0, Bv, mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply]
    field_simp
    linear_combination (norm := (simp only [a]; field_simp; ring))
      ((p.ωc : ℂ) * p.E * Complex.sin δ0 * V * 2 * p.H / p.X) * hP

@[tmio M, powerlib_domain] theorem forcedθ_eq (δ0 V0 : ℝ) {s : ℂ} (θ : ℂ) (hω0 : p.ω0 ≠ 0)
    (hH : p.H ≠ 0) (hs : p.charP δ0 V0 s ≠ 0) :
    (s • (1 : Matrix (Fin 3) (Fin 3) ℂ) - p.A0 δ0 V0) *ᵥ p.forcedθ δ0 V0 s θ = ![-(s * θ), 0, 0] := by
  have hω : (p.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (p.H : ℂ) ≠ 0 := by exact_mod_cast hH
  simp only [forcedθ, forcedθδ]
  generalize hP : p.charP δ0 V0 s = P at hs
  simp only [charP, d0] at hP
  funext i
  fin_cases i
  · simp [A0, mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply]; field_simp; ring
  · simp [A0, mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply, a]; field_simp; ring
  · simp [A0, mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply]
    field_simp
    linear_combination (norm := (simp only [a]; field_simp; ring))
      (s * (s + p.ωc) * θ * (p.D + 2 * p.H * s)) * hP

/-- The relative modulation `ρ = (A₁)_{P_f δ}/(A₀)_{P_f δ} = −tan δ₀ z_δ + V̂/V₀` of the
synchronizing element. -/
def rho (δ0 V0 : ℝ) (zδ zV : ℂ) : ℂ := -(Real.tan δ0 : ℂ) * zδ + zV / V0

@[tmio M, powerlib_domain] theorem Kc_real (δ0 V0 : ℝ) :
    p.Kc δ0 V0 = ((p.E * V0 * Real.cos δ0 / p.X : ℝ) : ℂ) ∧
      p.Pw δ0 V0 = ((p.E * V0 * Real.sin δ0 / p.X : ℝ) : ℂ) := by
  constructor <;> simp [Kc, Pw, ← ofReal_cos, ← ofReal_sin]

/-- The weight of the synchronizing element, `w = u_{P_f} (A₀)_{P_f δ} r_δ = −d₀/D'(λ)`. -/
@[tmio M, powerlib_domain] theorem weight_K (δ0 V0 : ℝ) (s : ℂ) :
    Element.weight (p.A0 δ0 V0) (p.left s) (p.right s) 2 0 = -(p.d0 δ0 V0 / p.charD s) := by
  simp [Element.weight, A0, left, right, d0]
  ring

/-- The pump coefficient is the weight times the relative modulation:
`g = u A₁ r̄ = −(d₀/D'(λ)) ρ`. -/
@[tmio M, powerlib_domain] theorem pump_eq (δ0 V0 : ℝ) (s zδ zV : ℂ) (hc : Real.cos δ0 ≠ 0)
    (hV0 : V0 ≠ 0) (hX : p.X ≠ 0) :
    Element.pump (p.A1 δ0 V0 zδ zV) (p.left s) (p.right s) = -(p.d0 δ0 V0 / p.charD s) * rho δ0 V0 zδ zV := by
  have hcc : (Real.cos δ0 : ℂ) ≠ 0 := by exact_mod_cast hc
  have hVc : (V0 : ℂ) ≠ 0 := by exact_mod_cast hV0
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  obtain ⟨hK, hP⟩ := p.Kc_real δ0 V0
  simp only [Element.pump, A1, left, right, rho, d0, hK, hP, Real.tan_eq_sin_div_cos]
  have hcc' : Complex.cos δ0 ≠ 0 := by rw [← ofReal_cos]; exact hcc
  simp [mulVec, dotProduct, Fin.sum_univ_three]
  field_simp

/-- Voltage forcing: `z_δ = −T(s) tan δ₀ V̂/V₀`, `T = d₀/D(s)` (complementary sensitivity). -/
@[tmio M, powerlib_domain] theorem forcedVδ_eq (δ0 V0 : ℝ) (s V : ℂ) (hc : Real.cos δ0 ≠ 0)
    (hV0 : V0 ≠ 0) (hX : p.X ≠ 0) (hH : p.H ≠ 0) :
    p.forcedVδ δ0 V0 s V = -(p.d0 δ0 V0 / p.charP δ0 V0 s) * (Real.tan δ0 : ℂ) * (V / V0) := by
  have hcc : (Real.cos δ0 : ℂ) ≠ 0 := by exact_mod_cast hc
  have hVc : (V0 : ℂ) ≠ 0 := by exact_mod_cast hV0
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hHc : (p.H : ℂ) ≠ 0 := by exact_mod_cast hH
  obtain ⟨hK, -⟩ := p.Kc_real δ0 V0
  simp only [forcedVδ, d0, hK, Real.tan_eq_sin_div_cos]
  generalize p.charP δ0 V0 s = P
  have hcc' : Complex.cos δ0 ≠ 0 := by rw [← ofReal_cos]; exact hcc
  push_cast
  field_simp

/-- Angle forcing: `z_δ = −S(s) θ̂`, `S = 1 − T`. -/
@[tmio M, powerlib_domain] theorem forcedθδ_eq (δ0 V0 : ℝ) (s θ : ℂ) (hs : p.charP δ0 V0 s ≠ 0) :
    p.forcedθδ δ0 V0 s θ = -(1 - p.d0 δ0 V0 / p.charP δ0 V0 s) * θ := by
  simp only [forcedθδ]
  have : s * (s + p.a) * (s + p.ωc) = p.charP δ0 V0 s - p.d0 δ0 V0 := by simp [charP]
  rw [this, sub_div, div_self hs]

/-- The relative modulation of the synchronizing element: `ρ_V = (V̂/V₀)(1 + T tan² δ₀)` for
voltage forcing, `ρ_θ = tan δ₀ S θ̂` for angle forcing. -/
@[tmio M, powerlib_domain] theorem rho_forced (δ0 V0 : ℝ) (s V θ : ℂ) (hc : Real.cos δ0 ≠ 0)
    (hV0 : V0 ≠ 0) (hX : p.X ≠ 0) (hH : p.H ≠ 0) (hs : p.charP δ0 V0 s ≠ 0) :
    rho δ0 V0 (p.forcedVδ δ0 V0 s V) V =
        V / V0 * (1 + p.d0 δ0 V0 / p.charP δ0 V0 s * (Real.tan δ0 : ℂ) ^ 2) ∧
      rho δ0 V0 (p.forcedθδ δ0 V0 s θ) 0 =
        (Real.tan δ0 : ℂ) * (1 - p.d0 δ0 V0 / p.charP δ0 V0 s) * θ := by
  constructor
  · rw [rho, p.forcedVδ_eq δ0 V0 s V hc hV0 hX hH]; ring
  · rw [rho, p.forcedθδ_eq δ0 V0 s θ hs]; ring

/-! ### At the Hopf point -/

@[tmio M, powerlib_domain] theorem charD_hopf (Ω : ℝ) (hH1 : p.a * p.ωc = (Ω : ℂ) ^ 2) :
    p.charD (Ω * I) = 2 * (Ω * I) * (p.a + p.ωc + Ω * I) := by
  simp only [charD]
  linear_combination hH1 + ((Ω : ℂ) ^ 2) * I_sq

@[tmio M, powerlib_domain] theorem charP_hopf (δ0 V0 Ω : ℝ) (hH1 : p.a * p.ωc = (Ω : ℂ) ^ 2)
    (hH2 : p.d0 δ0 V0 = (p.a + p.ωc) * (Ω : ℂ) ^ 2) :
    p.charP δ0 V0 (2 * Ω * I) = -3 * (Ω : ℂ) ^ 2 * (p.a + p.ωc + 2 * Ω * I) := by
  simp only [charP]
  rw [hH2]
  linear_combination (2 * (Ω : ℂ) * I) * hH1 +
    (8 * (Ω : ℂ) ^ 3 * I + 4 * (Ω : ℂ) ^ 2 * (p.a + p.ωc)) * I_sq

/-- `d₂ = D/2H + ω_c` (real). -/
def d2 : ℝ := p.D / (2 * p.H) + p.ωc

@[tmio M, powerlib_domain] theorem a_add_ωc : p.a + (p.ωc : ℂ) = (p.d2 : ℂ) := by
  simp [a, d2]

@[tmio T, powerlib_foundation] theorem add_mul_I_ne {x y : ℝ} (hy : y ≠ 0) : (x : ℂ) + y * I ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this; exact hy this

/-- Voltage-amplitude modulation at the Hopf point (`λ = jΩ`, `ω_p = 2Ω`, `β = Ω/d₂`):
`g_V = (jΩ/2)(V̂/V₀)(3 + 6jβ − tan² δ₀)/((3 + 6jβ)(1 + jβ))`. -/
@[tmio M, powerlib_domain] theorem pump_voltage_hopf (δ0 V0 Ω : ℝ) (V : ℂ) (hc : Real.cos δ0 ≠ 0)
    (hV0 : V0 ≠ 0) (hX : p.X ≠ 0) (hH : p.H ≠ 0) (hΩ : Ω ≠ 0) (hd2 : p.d2 ≠ 0)
    (hH1 : p.a * p.ωc = (Ω : ℂ) ^ 2) (hH2 : p.d0 δ0 V0 = (p.a + p.ωc) * (Ω : ℂ) ^ 2) :
    Element.pump (p.A1 δ0 V0 (p.forcedVδ δ0 V0 (2 * Ω * I) V) V) (p.left (Ω * I)) (p.right (Ω * I)) =
      Ω * I / 2 * (V / V0) * (3 + 6 * ((Ω / p.d2 : ℝ) : ℂ) * I - (Real.tan δ0 : ℂ) ^ 2) /
        ((3 + 6 * ((Ω / p.d2 : ℝ) : ℂ) * I) * (1 + ((Ω / p.d2 : ℝ) : ℂ) * I)) := by
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
  have hdc : (p.d2 : ℂ) ≠ 0 := by exact_mod_cast hd2
  have hP2 := p.charP_hopf δ0 V0 Ω hH1 hH2
  rw [a_add_ωc] at hP2 hH2
  have hn1 : (p.d2 : ℂ) + 2 * Ω * I ≠ 0 := by
    have := add_mul_I_ne (x := p.d2) (y := 2 * Ω) (by positivity); push_cast at this; exact this
  have hn2 : (p.d2 : ℂ) + Ω * I ≠ 0 := add_mul_I_ne hΩ
  have hs : p.charP δ0 V0 (2 * Ω * I) ≠ 0 := by
    rw [hP2]; exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hΩc)) hn1
  rw [p.pump_eq δ0 V0 _ _ _ hc hV0 hX, (p.rho_forced δ0 V0 _ V 0 hc hV0 hX hH hs).1,
    p.charD_hopf Ω hH1, hP2, hH2, a_add_ωc]
  push_cast
  have hb1 : (1 : ℂ) + Ω / p.d2 * I ≠ 0 := by
    have : (1 : ℂ) + Ω / p.d2 * I = ((p.d2 : ℂ) + Ω * I) / p.d2 := by field_simp
    rw [this]; exact div_ne_zero hn2 hdc
  have hb3 : (3 : ℂ) + 6 * (Ω / p.d2) * I ≠ 0 := by
    have : (3 : ℂ) + 6 * (Ω / p.d2) * I = 3 * ((p.d2 : ℂ) + 2 * Ω * I) / p.d2 := by field_simp; ring
    rw [this]; exact div_ne_zero (mul_ne_zero (by norm_num) hn1) hdc
  have hn1' : (p.d2 : ℂ) + Ω * 2 * I ≠ 0 := by rw [mul_comm (Ω : ℂ) 2]; exact hn1
  have hn3 : (p.d2 : ℂ) * 3 + Ω * I * 6 ≠ 0 := by
    have : (p.d2 : ℂ) * 3 + Ω * I * 6 = 3 * ((p.d2 : ℂ) + 2 * Ω * I) := by ring
    rw [this]; exact mul_ne_zero (by norm_num) hn1
  field_simp
  linear_combination (-(V * (3 * ((p.d2 : ℂ) + Ω * 2 * I) - p.d2 * Complex.tan δ0 ^ 2) *
    ((p.d2 : ℂ) * 3 + Ω * I * 6) / V0)) * I_sq

/-- Grid-angle modulation in the same core at the Hopf point:
`g_θ = (jΩ/2) θ̂ tan δ₀ (4 + 6jβ)/((3 + 6jβ)(1 + jβ))`. -/
@[tmio M, powerlib_domain] theorem pump_angle_hopf (δ0 V0 Ω : ℝ) (θ : ℂ) (hc : Real.cos δ0 ≠ 0)
    (hV0 : V0 ≠ 0) (hX : p.X ≠ 0) (hH : p.H ≠ 0) (hΩ : Ω ≠ 0) (hd2 : p.d2 ≠ 0)
    (hH1 : p.a * p.ωc = (Ω : ℂ) ^ 2) (hH2 : p.d0 δ0 V0 = (p.a + p.ωc) * (Ω : ℂ) ^ 2) :
    Element.pump (p.A1 δ0 V0 (p.forcedθδ δ0 V0 (2 * Ω * I) θ) 0) (p.left (Ω * I)) (p.right (Ω * I)) =
      Ω * I / 2 * θ * (Real.tan δ0 : ℂ) * (4 + 6 * ((Ω / p.d2 : ℝ) : ℂ) * I) /
        ((3 + 6 * ((Ω / p.d2 : ℝ) : ℂ) * I) * (1 + ((Ω / p.d2 : ℝ) : ℂ) * I)) := by
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
  have hdc : (p.d2 : ℂ) ≠ 0 := by exact_mod_cast hd2
  have hP2 := p.charP_hopf δ0 V0 Ω hH1 hH2
  rw [a_add_ωc] at hP2 hH2
  have hn1 : (p.d2 : ℂ) + 2 * Ω * I ≠ 0 := by
    have := add_mul_I_ne (x := p.d2) (y := 2 * Ω) (by positivity); push_cast at this; exact this
  have hn2 : (p.d2 : ℂ) + Ω * I ≠ 0 := add_mul_I_ne hΩ
  have hs : p.charP δ0 V0 (2 * Ω * I) ≠ 0 := by
    rw [hP2]; exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hΩc)) hn1
  rw [p.pump_eq δ0 V0 _ _ _ hc hV0 hX, (p.rho_forced δ0 V0 _ 0 θ hc hV0 hX hH hs).2,
    p.charD_hopf Ω hH1, hP2, hH2, a_add_ωc]
  push_cast
  have hb1 : (1 : ℂ) + Ω / p.d2 * I ≠ 0 := by
    have : (1 : ℂ) + Ω / p.d2 * I = ((p.d2 : ℂ) + Ω * I) / p.d2 := by field_simp
    rw [this]; exact div_ne_zero hn2 hdc
  have hb3 : (3 : ℂ) + 6 * (Ω / p.d2) * I ≠ 0 := by
    have : (3 : ℂ) + 6 * (Ω / p.d2) * I = 3 * ((p.d2 : ℂ) + 2 * Ω * I) / p.d2 := by field_simp; ring
    rw [this]; exact div_ne_zero (mul_ne_zero (by norm_num) hn1) hdc
  have hn1' : (p.d2 : ℂ) + Ω * 2 * I ≠ 0 := by rw [mul_comm (Ω : ℂ) 2]; exact hn1
  have hn3 : (p.d2 : ℂ) * 3 + Ω * I * 6 ≠ 0 := by
    have : (p.d2 : ℂ) * 3 + Ω * I * 6 = 3 * ((p.d2 : ℂ) + 2 * Ω * I) := by ring
    rw [this]; exact mul_ne_zero (by norm_num) hn1
  field_simp
  linear_combination (-(Complex.tan δ0 * θ * ((p.d2 : ℂ) * 4 + Ω * I * 6) *
    ((p.d2 : ℂ) * 3 + Ω * I * 6))) * I_sq

/-! ### Normalized pump strengths `ĝ = 2|g|/Ω` -/

@[tmio T, powerlib_foundation] theorem normSq_voltage_form (Ω x β t : ℝ) :
    Complex.normSq (Ω * I / 2 * x * (3 + 6 * (β : ℂ) * I - (t : ℂ)) /
      ((3 + 6 * (β : ℂ) * I) * (1 + β * I))) =
      Ω ^ 2 / 4 * x ^ 2 * ((3 - t) ^ 2 + 36 * β ^ 2) / ((9 + 36 * β ^ 2) * (1 + β ^ 2)) := by
  simp only [map_div₀, map_mul]
  simp [Complex.normSq_apply]
  have : (0 : ℝ) < (9 + 36 * β ^ 2) * (1 + β ^ 2) := by positivity
  field_simp
  ring

@[tmio T, powerlib_foundation] theorem normSq_angle_form (Ω x τ β : ℝ) :
    Complex.normSq (Ω * I / 2 * x * (τ : ℂ) * (4 + 6 * (β : ℂ) * I) /
      ((3 + 6 * (β : ℂ) * I) * (1 + β * I))) =
      Ω ^ 2 / 4 * x ^ 2 * τ ^ 2 * (16 + 36 * β ^ 2) / ((9 + 36 * β ^ 2) * (1 + β ^ 2)) := by
  simp only [map_div₀, map_mul]
  simp [Complex.normSq_apply]
  have : (0 : ℝ) < (9 + 36 * β ^ 2) * (1 + β ^ 2) := by positivity
  field_simp
  ring

/-- Normalized pump strength of voltage-amplitude modulation, `v̂ = V̂/V₀`, `t = tan² δ₀`:
`ĝ_V² = v̂² ((3 − t)² + 36β²)/((9 + 36β²)(1 + β²))`. -/
@[tmio M, powerlib_domain] theorem ghat_voltage (δ0 V0 Ω V : ℝ) (hc : Real.cos δ0 ≠ 0)
    (hV0 : V0 ≠ 0) (hX : p.X ≠ 0) (hH : p.H ≠ 0) (hΩ : Ω ≠ 0) (hd2 : p.d2 ≠ 0)
    (hH1 : p.a * p.ωc = (Ω : ℂ) ^ 2) (hH2 : p.d0 δ0 V0 = (p.a + p.ωc) * (Ω : ℂ) ^ 2) :
    (2 * ‖Element.pump (p.A1 δ0 V0 (p.forcedVδ δ0 V0 (2 * Ω * I) V) V) (p.left (Ω * I))
        (p.right (Ω * I))‖ / Ω) ^ 2 =
      (V / V0) ^ 2 * ((3 - Real.tan δ0 ^ 2) ^ 2 + 36 * (Ω / p.d2) ^ 2) /
        ((9 + 36 * (Ω / p.d2) ^ 2) * (1 + (Ω / p.d2) ^ 2)) := by
  rw [p.pump_voltage_hopf δ0 V0 Ω V hc hV0 hX hH hΩ hd2 hH1 hH2]
  have h := normSq_voltage_form Ω (V / V0) (Ω / p.d2) (Real.tan δ0 ^ 2)
  rw [div_pow, mul_pow, Complex.sq_norm]
  push_cast at h ⊢
  rw [h]
  have : (0 : ℝ) < (9 + 36 * (Ω / p.d2) ^ 2) * (1 + (Ω / p.d2) ^ 2) := by positivity
  field_simp
  ring

/-- Normalized pump strength of grid-angle modulation in the same core:
`ĝ_θ² = θ̂² t (16 + 36β²)/((9 + 36β²)(1 + β²))`. -/
@[tmio M, powerlib_domain] theorem ghat_angle (δ0 V0 Ω θ : ℝ) (hc : Real.cos δ0 ≠ 0)
    (hV0 : V0 ≠ 0) (hX : p.X ≠ 0) (hH : p.H ≠ 0) (hΩ : Ω ≠ 0) (hd2 : p.d2 ≠ 0)
    (hH1 : p.a * p.ωc = (Ω : ℂ) ^ 2) (hH2 : p.d0 δ0 V0 = (p.a + p.ωc) * (Ω : ℂ) ^ 2) :
    (2 * ‖Element.pump (p.A1 δ0 V0 (p.forcedθδ δ0 V0 (2 * Ω * I) θ) 0) (p.left (Ω * I))
        (p.right (Ω * I))‖ / Ω) ^ 2 =
      θ ^ 2 * Real.tan δ0 ^ 2 * (16 + 36 * (Ω / p.d2) ^ 2) /
        ((9 + 36 * (Ω / p.d2) ^ 2) * (1 + (Ω / p.d2) ^ 2)) := by
  rw [p.pump_angle_hopf δ0 V0 Ω θ hc hV0 hX hH hΩ hd2 hH1 hH2]
  have h := normSq_angle_form Ω θ (Real.tan δ0) (Ω / p.d2)
  rw [div_pow, mul_pow, Complex.sq_norm]
  push_cast at h ⊢
  rw [h]
  have : (0 : ℝ) < (9 + 36 * (Ω / p.d2) ^ 2) * (1 + (Ω / p.d2) ^ 2) := by positivity
  field_simp
  ring

/-- No load (`δ₀ = 0`): the angle pump vanishes in this core, the voltage pump does not:
`ĝ_V² = v̂²/(1 + β²)`, i.e. `ε_crit = 4 (σ/Ω) √(1 + β²)` in relative voltage amplitude — the
damped Mathieu threshold of a stiffness `K ∝ V` modulated with depth `v̂`. -/
@[tmio M, powerlib_domain] theorem noload (V0 Ω V θ : ℝ) (hV0 : V0 ≠ 0) (hX : p.X ≠ 0)
    (hH : p.H ≠ 0) (hΩ : Ω ≠ 0) (hd2 : p.d2 ≠ 0)
    (hH1 : p.a * p.ωc = (Ω : ℂ) ^ 2) (hH2 : p.d0 0 V0 = (p.a + p.ωc) * (Ω : ℂ) ^ 2) :
    (2 * ‖Element.pump (p.A1 0 V0 (p.forcedVδ 0 V0 (2 * Ω * I) V) V) (p.left (Ω * I))
        (p.right (Ω * I))‖ / Ω) ^ 2 = (V / V0) ^ 2 / (1 + (Ω / p.d2) ^ 2) ∧
      Element.pump (p.A1 0 V0 (p.forcedθδ 0 V0 (2 * Ω * I) θ) 0) (p.left (Ω * I))
        (p.right (Ω * I)) = 0 := by
  have hc : Real.cos 0 ≠ 0 := by simp
  constructor
  · rw [p.ghat_voltage 0 V0 Ω V hc hV0 hX hH hΩ hd2 hH1 hH2, Real.tan_zero]
    have : (0 : ℝ) < 9 + 36 * (Ω / p.d2) ^ 2 := by positivity
    have : (0 : ℝ) < 1 + (Ω / p.d2) ^ 2 := by positivity
    field_simp
    ring
  · rw [p.pump_angle_hopf 0 V0 Ω θ hc hV0 hX hH hΩ hd2 hH1 hH2, Real.tan_zero]
    simp

/-- The voltage pump vanishes only when `β = 0` and `tan² δ₀ = 3` (`δ₀ = 60°`, where the direct
stiffness modulation and the curvature along the forced angle cancel). -/
@[tmio T, powerlib_foundation] theorem voltage_factor_pos (t β : ℝ) :
    0 < (3 - t) ^ 2 + 36 * β ^ 2 ↔ ¬(β = 0 ∧ t = 3) := by
  constructor
  · rintro h ⟨hβ, ht⟩
    rw [hβ, ht] at h
    norm_num at h
  · intro h
    by_contra h'
    rw [not_lt] at h'
    have h1 : (3 - t) ^ 2 = 0 := by nlinarith [sq_nonneg (3 - t), sq_nonneg β]
    have h2 : β ^ 2 = 0 := by nlinarith [sq_nonneg (3 - t), sq_nonneg β]
    exact h ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2,
      by have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1; linarith⟩

/-- Per unit modulation (`v̂ = 1` against `θ̂ = 1 rad`), the voltage pump is the stronger one
exactly when `(3 − t)² + 36β² > t (16 + 36β²)`, `t = tan² δ₀`; for `β → 0` this is
`t² − 22t + 9 > 0`, i.e. `δ₀ < 32.8°` on the usual branch. -/
@[tmio T, powerlib_foundation] theorem voltage_vs_angle (t β : ℝ) :
    t * (16 + 36 * β ^ 2) / ((9 + 36 * β ^ 2) * (1 + β ^ 2)) <
        ((3 - t) ^ 2 + 36 * β ^ 2) / ((9 + 36 * β ^ 2) * (1 + β ^ 2)) ↔
      t * (16 + 36 * β ^ 2) < (3 - t) ^ 2 + 36 * β ^ 2 := by
  have : (0 : ℝ) < (9 + 36 * β ^ 2) * (1 + β ^ 2) := by positivity
  exact div_lt_div_iff_of_pos_right this

end Model
end VoltageModulation
end powerlib.GFM
