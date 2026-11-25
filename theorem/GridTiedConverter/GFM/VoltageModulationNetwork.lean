import theorem.GridTiedConverter.GFM.MatchingResistance

/-! # Voltage-amplitude modulation through a dynamic network: droop and matching

With a dynamic (`L di/dt`) network in a fixed frame the grid voltage enters the current equation
additively, `di/dt ∝ φ(δ) − V e^{jθ_g} − Z i`. Hence, unlike the quasi-static cores of
`VoltageModulation`, the Jacobian does not depend on `V` (`G_V = 0`): voltage modulation acts only
through the input column, i.e. through the forced response, and the pump is the angle-modulation
kernel of `DroopNetwork`/`MatchingNetwork` evaluated with the voltage input `b_i = b_ī = −a_n`. For
a lossless link the voltage transfers are closed-form rational functions with the sideband
reactances `X(1 ± μ)`, `μ = ω/ω_b`; for `ω_b → ∞` the direct term
`(E/X) ω_b(ω_b cos δ₀ + jω sin δ₀)/(ω_b² − ω²)` tends to `(E/X) cos δ₀`, the stiffness modulation
`∂K/∂V` of the quasi-static core, which here arrives through the forced network current.

Model boundary.
* The droop core of `DroopNetwork.Model` and the matching core of `MatchingNetwork.Model` (their
  states, filters and network current equations), with the grid-voltage magnitude `V` as an extra
  input (`netV`); everything else as in those files.
* The voltage input direction is taken at `θ_g = 0`; the pump formulas are exact (no averaging).

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2 (framework), §5 (network sidebands, `X(1 ± μ)`); the voltage
excitation is new.

Results.
* `lossless_voltage_transfer` — through a lossless link at `jω`:
  `K_V = (E/X) ω_b(ω_b sin δ₀ − jω cos δ₀)/(ω_b² − ω²)`,
  `−H_V = (E/X) ω_b(ω_b cos δ₀ + jω sin δ₀)/(ω_b² − ω²)`.
* Droop: `hasDerivAt_netV` (`∂(net)/∂V = −a_n e^{jθ_g}`, `G_V = 0`), `coeffsV`, `pump_kernel_V`
  (kernel form of the voltage pump), `voltage_lossless`, `pump_lossless_V` —
  `g = u_{p_m} ω_m [(E/X) ω_b(ω_b cos δ₀ + jω sin δ₀)/(ω_b² − ω²)
  − z_δ ((EV/X) sin δ₀ − (H_q(λ) − H_q(jω) − H_q(s₂)))]`, `z_δ = −m_p ω₁ ω_m K_V(jω)/D(jω)`.
* Matching: `coeffsV`, `voltage_lossless`, `pump_hopf_V` — at a Hopf mode `λ = jΩ`, `ω = 2Ω`:
  `D'(λ) g = (m_a V/X) sin δ₀ z_θ − (m_a/X) ω_b(ω_b cos δ₀ + jω sin δ₀)/(ω_b² − ω²)
  − z_θ · 12 (m_a²/X) ω_b Ω⁴/(ω_f(ω_b² − Ω²)(ω_b² − 4Ω²))`, `z_θ = −K_V(jω)/D(jω)`.
* `phi_split` — `φ = E e^{jδ₀}` (droop) in Cartesian form; the matching form is
  `MatchingNetwork.Model.φ_expand`.

Corrections.
None: an extension.

Family and connection conclusions.
None: static evidence on the droop and matching cores with a dynamic link (input column, pump).
-/

noncomputable section
namespace powerlib.GFM
namespace VoltageModulation
open Complex

/-- The transfers of a grid-voltage phasor through a lossless link `X` (base frequency `ω_b`) to
the in-phase and quadrature power of an EMF `E e^{jδ₀}`, at the drive `jω`:
`K_V = (E/X) ω_b(ω_b sin δ₀ − jω cos δ₀)/(ω_b² − ω²)`,
`−H_V = (E/X) ω_b(ω_b cos δ₀ + jω sin δ₀)/(ω_b² − ω²)`; the sidebands see `X(1 ± μ)`. -/
@[tmio T, powerlib_foundation] theorem lossless_voltage_transfer (E X ωb ω c s : ℝ) (hX : X ≠ 0)
    (hμ : ω ^ 2 ≠ ωb ^ 2) :
    (E : ℂ) * ((c : ℂ) - s * I) / 2 * (-((ωb / X : ℝ) : ℂ) / ((ω + ωb : ℝ) * I)) +
        (E : ℂ) * ((c : ℂ) + s * I) / 2 * (-((ωb / X : ℝ) : ℂ) / ((ω - ωb : ℝ) * I)) =
      ((E / X : ℝ) : ℂ) * (ωb * (ωb * (s : ℂ) - I * ω * c) / ((ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2)) ∧
    -(I * ((E : ℂ) * ((c : ℂ) - s * I) / 2 * (-((ωb / X : ℝ) : ℂ) / ((ω + ωb : ℝ) * I)) -
        (E : ℂ) * ((c : ℂ) + s * I) / 2 * (-((ωb / X : ℝ) : ℂ) / ((ω - ωb : ℝ) * I)))) =
      ((E / X : ℝ) : ℂ) * (ωb * (ωb * (c : ℂ) + I * ω * s) / ((ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2)) := by
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX
  have h1 : (ω : ℂ) + ωb ≠ 0 := by
    intro h
    have : ω + ωb = 0 := by exact_mod_cast h
    apply hμ; have : ω = -ωb := by linarith
    rw [this]; ring
  have h2 : (ω : ℂ) - ωb ≠ 0 := by
    intro h
    have : ω - ωb = 0 := by exact_mod_cast h
    apply hμ; have : ω = ωb := by linarith
    rw [this]
  have hD : (ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2 ≠ 0 := by
    rw [show (ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2 = -(((ω : ℂ) + ωb) * ((ω : ℂ) - ωb)) by ring]
    exact neg_ne_zero.mpr (mul_ne_zero h1 h2)
  push_cast
  constructor
  · field_simp
    linear_combination (2 * (E : ℂ) * c * ω * ωb * ((ω : ℂ) - ωb) * ((ω : ℂ) + ωb)) * I_sq
  · field_simp
    ring

end VoltageModulation

/-! ### Droop with a dynamic link -/

namespace DroopNetwork
namespace Model
open Complex ComplexConjugate

variable (p : Model)

/-- The current equation with the grid-voltage magnitude as an input. -/
def netV (V θ δ i : ℂ) : ℂ := p.an * (p.φ δ - V * exp (θ * I) - p.Z * i)

/-- `∂(net)/∂V = −a_n e^{jθ_g}`: the grid voltage enters additively, so the Jacobian does not
depend on it (`G_V = 0`) and only the input column changes. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_netV (V θ δ i : ℂ) :
    HasDerivAt (fun V => p.netV V θ δ i) (-(p.an * exp (θ * I))) V := by
  have h := (((hasDerivAt_id V).mul_const (exp (θ * I))).const_sub (p.φ δ)).sub_const (p.Z * i)
    |>.const_mul (p.an : ℂ)
  convert h using 1
  · funext V; simp [netV]
  · simp

/-- The coefficients with the grid-voltage magnitude as input (`b_i = b_ī = −a_n` at `θ_g = 0`). -/
def coeffsV (δ0 : ℂ) : Coeffs := { p.coeffs δ0 with bi := -(p.an : ℂ), bm := -(p.an : ℂ) }

/-- Kernel form of the voltage pump. -/
@[tmio M, powerlib_domain] theorem pump_kernel_V (δ0 s1 s2 lam : ℂ) :
    Coeffs.pumpc ((p.coeffsV δ0).A1 ((p.coeffsV δ0).forced s1)) ((p.coeffsV δ0).left lam)
        ((p.coeffsV δ0).right s2) =
      (-(p.mp * p.ω1) / (p.coeffsV δ0).Dd lam) * p.ωm *
        ((p.coeffsV δ0).forcedδ s1 * ((p.coeffsV δ0).Pδδ + ((p.coeffsV δ0).Hq lam -
          (p.coeffsV δ0).Hq s1 - (p.coeffsV δ0).Hq s2)) - (p.coeffsV δ0).Hθ s1) :=
  Coeffs.pump_kernel (q := p.coeffsV δ0) rfl rfl s1 s2 lam

/-- `φ = E e^{jδ₀}`, `φ̃ = E e^{−jδ₀}` in Cartesian form. -/
@[tmio M, powerlib_domain] theorem phi_split (δ0 : ℝ) :
    p.φ δ0 = p.E * ((Real.cos δ0 : ℂ) + Real.sin δ0 * I) ∧
      p.φt δ0 = p.E * ((Real.cos δ0 : ℂ) - Real.sin δ0 * I) := by
  constructor
  · simp only [φ]; rw [Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  · simp only [φt]; rw [PSCActiveDamping.exp_neg_mul_I]

/-- Lossless link: the voltage transfers `K_V(jω)` (forcing of the angle loop) and `−H_V(jω)`
(direct term), with the sideband reactances `X(1 ± μ)`. -/
@[tmio M, powerlib_domain] theorem voltage_lossless (δ0 ω : ℝ) (hR : p.R = 0) (hX : p.X ≠ 0)
    (hμ : ω ^ 2 ≠ p.ωb ^ 2) :
    (p.coeffsV δ0).Kθ ((ω : ℂ) * I) = ((p.E / p.X : ℝ) : ℂ) *
        (p.ωb * (p.ωb * (Real.sin δ0 : ℂ) - I * ω * Real.cos δ0) / ((p.ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2)) ∧
      -(p.coeffsV δ0).Hθ ((ω : ℂ) * I) = ((p.E / p.X : ℝ) : ℂ) *
        (p.ωb * (p.ωb * (Real.cos δ0 : ℂ) + I * ω * Real.sin δ0) / ((p.ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2)) := by
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  have he : (p.an : ℂ) * p.Z = p.ωb * I := by
    simp only [an, Z, hR]; push_cast; field_simp; ring
  have heb : (p.an : ℂ) * p.Zc = -(p.ωb * I) := by
    simp only [an, Zc, hR]; push_cast; field_simp; ring
  obtain ⟨hφ, hφt⟩ := p.phi_split δ0
  have hd1 : (ω : ℂ) * I + p.ωb * I = ((ω + p.ωb : ℝ) : ℂ) * I := by push_cast; ring
  have hd2 : (ω : ℂ) * I + -(p.ωb * I) = ((ω - p.ωb : ℝ) : ℂ) * I := by push_cast; ring
  have han : (p.an : ℂ) = ((p.ωb / p.X : ℝ) : ℂ) := by simp [an]
  obtain ⟨t1, t2⟩ := VoltageModulation.lossless_voltage_transfer p.E p.X p.ωb ω (Real.cos δ0)
    (Real.sin δ0) hX hμ
  simp only [Coeffs.Kθ, Coeffs.Hθ, Coeffs.d, Coeffs.dt, coeffsV, coeffs, pwi, pwm, he, heb, hφ,
    hφt, hd1, hd2]
  simp only [han]
  constructor
  · rw [← t1]
  · rw [← t2]

/-- The exact voltage pump of the droop core with a dynamic lossless link:
`g = u_{p_m} ω_m [(E/X) ω_b(ω_b cos δ₀ + jω sin δ₀)/(ω_b² − ω²)
− z_δ ((EV/X) sin δ₀ − (H_q(λ) − H_q(jω) − H_q(s₂)))]`, with the voltage-forced angle
`z_δ = −m_p ω₁ ω_m K_V(jω)/D(jω)`. -/
@[tmio M, powerlib_domain] theorem pump_lossless_V (δ0 ω : ℝ) (s2 lam : ℂ) (hR : p.R = 0)
    (hX : p.X ≠ 0) (hμ : ω ^ 2 ≠ p.ωb ^ 2) :
    Coeffs.pumpc ((p.coeffsV δ0).A1 ((p.coeffsV δ0).forced ((ω : ℂ) * I)))
        ((p.coeffsV δ0).left lam) ((p.coeffsV δ0).right s2) =
      (-(p.mp * p.ω1) / (p.coeffsV δ0).Dd lam) * p.ωm *
        (((p.E / p.X : ℝ) : ℂ) * (p.ωb * (p.ωb * (Real.cos δ0 : ℂ) + I * ω * Real.sin δ0) /
            ((p.ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2)) -
          (p.coeffsV δ0).forcedδ ((ω : ℂ) * I) * (((p.E * p.V * Real.sin δ0 / p.X : ℝ) : ℂ) -
            ((p.coeffsV δ0).Hq lam - (p.coeffsV δ0).Hq ((ω : ℂ) * I) - (p.coeffsV δ0).Hq s2))) := by
  rw [p.pump_kernel_V, show (p.coeffsV δ0).Pδδ = (p.coeffs δ0).Pδδ from rfl,
    p.Pδδ_lossless δ0 hR hX, ← (p.voltage_lossless δ0 ω hR hX hμ).2]
  push_cast
  ring

end Model
end DroopNetwork

/-! ### Matching with a dynamic link -/

namespace MatchingNetwork
namespace Model
open Complex ComplexConjugate

variable (p : Model)

/-- The coefficients with the grid-voltage magnitude as input. -/
def coeffsV (δ0 : ℂ) : Coeffs := { p.coeffs δ0 with bi := -(p.an : ℂ), bm := -(p.an : ℂ) }

/-- Lossless link: the voltage transfers `K_V(jω)` and `−H_V(jω)` of the matching core. -/
@[tmio M, powerlib_domain] theorem voltage_lossless (δ0 ω : ℝ) (hR : p.R = 0) (hX : p.X ≠ 0)
    (hμ : ω ^ 2 ≠ p.ωb ^ 2) :
    (p.coeffsV δ0).Kd ((ω : ℂ) * I) = ((p.ma / p.X : ℝ) : ℂ) *
        (p.ωb * (p.ωb * (Real.sin δ0 : ℂ) - I * ω * Real.cos δ0) / ((p.ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2)) ∧
      -(p.coeffsV δ0).Hd ((ω : ℂ) * I) = ((p.ma / p.X : ℝ) : ℂ) *
        (p.ωb * (p.ωb * (Real.cos δ0 : ℂ) + I * ω * Real.sin δ0) / ((p.ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2)) := by
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  obtain ⟨hφ, hφt⟩ := p.φ_expand δ0
  have hd1 : (ω : ℂ) * I + p.ωb * I = ((ω + p.ωb : ℝ) : ℂ) * I := by push_cast; ring
  have hd2 : (ω : ℂ) * I + -(p.ωb * I) = ((ω - p.ωb : ℝ) : ℂ) * I := by push_cast; ring
  have han : (p.an : ℂ) = ((p.ωb / p.X : ℝ) : ℂ) := by simp [an]
  obtain ⟨t1, t2⟩ := VoltageModulation.lossless_voltage_transfer p.ma p.X p.ωb ω (Real.cos δ0)
    (Real.sin δ0) hX hμ
  simp only [Coeffs.Kd, Coeffs.Hd, Coeffs.d, Coeffs.dt, coeffsV, coeffs, idci, idcm,
    p.e_lossless hR hX, p.eb_lossless hR hX, hφ, hφt, hd1, hd2]
  simp only [han]
  constructor
  · rw [← t1]
  · rw [← t2]

/-- The exact voltage pump of the matching core with a dynamic lossless link at a Hopf mode
`λ = jΩ`, `ω = 2Ω`:
`D'(λ) g = (m_a V/X) sin δ₀ z_θ − (m_a/X) ω_b(ω_b cos δ₀ + jω sin δ₀)/(ω_b² − ω²)
− z_θ · 12 (m_a²/X) ω_b Ω⁴/(ω_f (ω_b² − Ω²)(ω_b² − 4Ω²))`, `z_θ = −K_V(jω)/D(jω)`. -/
@[tmio M, powerlib_domain] theorem pump_hopf_V (δ0 : ℝ) (hR : p.R = 0) (hX : p.X ≠ 0)
    (hωf : p.ωf ≠ 0) (hC : p.C ≠ 0) {Ω : ℝ} (hΩ : 0 < Ω) (hΩb : 2 * Ω < p.ωb)
    (hDd : (p.coeffsV δ0).Dd ((Ω : ℂ) * I) ≠ 0) :
    let q := p.coeffsV δ0; let ω : ℝ := 2 * Ω; let zθ := q.forcedθ ((ω : ℂ) * I);
    q.Dd ((Ω : ℂ) * I) * Coeffs.pumpc (q.A1 (q.forced ((ω : ℂ) * I))) (q.left ((Ω : ℂ) * I))
        (q.right (conj ((Ω : ℂ) * I))) =
      ((p.ma * p.V / p.X : ℝ) : ℂ) * Real.sin δ0 * zθ -
        ((p.ma / p.X : ℝ) : ℂ) * (p.ωb * (p.ωb * (Real.cos δ0 : ℂ) + I * ω * Real.sin δ0) /
          ((p.ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2)) -
        zθ * (12 * ((p.ma : ℂ) ^ 2 / p.X) * p.ωb * (Ω : ℂ) ^ 4 /
          (p.ωf * (((p.ωb : ℂ) ^ 2 - (Ω : ℂ) ^ 2) * ((p.ωb : ℂ) ^ 2 - 4 * (Ω : ℂ) ^ 2)))) := by
  intro q ω zθ
  have hωb : 0 < p.ωb := by linarith
  have hμ : ω ^ 2 ≠ p.ωb ^ 2 := by simp only [ω]; nlinarith
  have hCc : (p.C : ℂ) ≠ 0 := by exact_mod_cast hC
  have hk : -zθ * (q.Kv (((2 * Ω : ℝ) : ℂ) * I) + q.Kv (conj ((Ω : ℂ) * I)) - q.Kv ((Ω : ℂ) * I)) +
      q.ρv (((2 * Ω : ℝ) : ℂ) * I) * zθ * (q.Hj (((2 * Ω : ℝ) : ℂ) * I) - q.Hj ((Ω : ℂ) * I)) +
      zθ * q.ρv (conj ((Ω : ℂ) * I)) * (q.Hj (conj ((Ω : ℂ) * I)) - q.Hj ((Ω : ℂ) * I)) =
      -zθ * (12 * ((p.ma : ℂ) ^ 2 / p.X) * p.ωb * (Ω : ℂ) ^ 4 /
        (p.ωf * (((p.ωb : ℂ) ^ 2 - (Ω : ℂ) ^ 2) * ((p.ωb : ℂ) ^ 2 - 4 * (Ω : ℂ) ^ 2)))) :=
    p.kernel_hopf (δ0 : ℂ) hR hX hωf hΩ hΩb zθ
  have hd := (p.voltage_lossless δ0 ω hR hX hμ).2
  have hp : q.Pθθ = ((-(p.ma * p.V * Real.sin δ0 / p.X)) : ℝ) := (p.Pθ_lossless δ0 hR hX).1
  rw [Coeffs.pump_kernel _ _ _ hCc, ← mul_assoc, mul_one_div_cancel hDd, one_mul]
  have hsplit : -q.Pθθ * zθ - zθ * (q.Kv ((ω : ℂ) * I) + q.Kv (conj ((Ω : ℂ) * I)) -
        q.Kv ((Ω : ℂ) * I)) + q.ρv ((ω : ℂ) * I) * zθ * (q.Hj ((ω : ℂ) * I) - q.Hj ((Ω : ℂ) * I)) +
        zθ * q.ρv (conj ((Ω : ℂ) * I)) * (q.Hj (conj ((Ω : ℂ) * I)) - q.Hj ((Ω : ℂ) * I)) +
        q.Hd ((ω : ℂ) * I) =
      -q.Pθθ * zθ + q.Hd ((ω : ℂ) * I) + (-zθ * (q.Kv (((2 * Ω : ℝ) : ℂ) * I) +
        q.Kv (conj ((Ω : ℂ) * I)) - q.Kv ((Ω : ℂ) * I)) + q.ρv (((2 * Ω : ℝ) : ℂ) * I) * zθ *
        (q.Hj (((2 * Ω : ℝ) : ℂ) * I) - q.Hj ((Ω : ℂ) * I)) + zθ * q.ρv (conj ((Ω : ℂ) * I)) *
        (q.Hj (conj ((Ω : ℂ) * I)) - q.Hj ((Ω : ℂ) * I))) := by
    simp only [ω]; ring
  rw [hsplit, hk, hp, show q.Hd ((ω : ℂ) * I) = -(-q.Hd ((ω : ℂ) * I)) by ring, hd]
  push_cast
  ring

end Model
end MatchingNetwork

namespace VoltageModulation
end VoltageModulation
end powerlib.GFM
