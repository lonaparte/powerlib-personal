import theorem.GridTiedConverter.GFM.DroopNetwork

/-! # Matching control with a dynamic series link: the exact pump and the full-order ratio (20)

The six-state matching core of the source's check 3 (`verification/check_matching.py`): states
`(θ, v_f, v, i_s, i_d, i_q)`, the EMF `m_a v e^{jθ}` proportional to the DC voltage, the series
link with its electromagnetic dynamics in the frame of the nominal grid frequency, the DC current
`i_dc = m_a Re(e^{jθ} ī)`, grid angle `θ_g` as input. The pump coefficient is derived exactly in
kernel form (as `PSCFull`, `DroopNetwork`): Park rotations of the network rows and of the DC row,
plus the bilinearity `E = m_a v`. For a lossless link at a Hopf mode the network kernel cancels
against the `E = m_a v` term through the frequency kinematics `z_v = ρ_v(jω) z_θ`, up to a term of
order `1/ω_f`, and the exact ratio is the matching report's (20).

Model boundary.
* `θ̇ = ω_b(v_f − 1)`, `v̇_f = ω_f(v − v_f)`, `C v̇ = i_s − G v − i_dc`,
  `τ i̇_s = I* − k_dc(v − 1) − i_s`, `(X/ω_b) i̇ = m_a v e^{jθ} − V e^{jθ_g} − Z i`, `Z = R + jX`
  (`field`, `net`, `idc`, `idc_real`); constant `m_a`, `V`, `X` (the grid-frequency dependence of
  the reactance considered in the single matching report is not in this model).
* Coordinates `(θ, v_f, v, i_s, i, ī)` with complexified model functions; the Jacobian entries are
  partial derivatives (`hasDerivAt_idc_θ`, `hasDerivAt_idc_i`, `hasDerivAt_idc_m`,
  `hasDerivAt_net_θ`, `hasDerivAt_net_v`, `hasDerivAt_net_i`, `hasDerivAt_net_θg`), and `A₁` is
  the directional derivative of the Jacobian along the forced response (`line_idcθ`, `line_idci`,
  `line_idcm`, `line_netθ`, `line_netv`); equilibrium `v₀ = v_f0 = 1`, `θ₀ = δ₀`, `θ_g = 0`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §3 (matching core), Table 4 and Table 5 (matching: the Park element
`(v, δ)` and its `K_rot/K = O(δ₀²)`), §5.4 (property (ii): (22) with `S = c_κ` against the
matching report's (20), "差别为 `O((c_κ − 1)μ_p² tan δ₀)`"), §5.5 (matching: "三个 `O(μ_p)` 效应
由运动学关系 `z_v/v = jμ_p z_θc` 精确相消"), §8 ("matching 的全阶形式"), and
`verification/check_matching.py`.

Results (generic core, `Coeffs`).
* `right_eig`, `left_eig`, `left_right` (`u_v = C/D'(λ)`), `forced_eq` (`z_θ = −K_d(s)/D(s)`,
  `D(s) = M(s) ρ_v(s) + K_θ(s)`, `M(s) = Cs + G + k_dc/(τs + 1) + K_v(s)`).
* `pump_kernel` — `g = (1/D'(λ)) [−P_θθ z_θ − z_θ(K_v(s₁) + K_v(s₂) − K_v(λ))
  + z_v(H_j(s₁) − H_j(λ)) + z_θ ρ_v(s₂)(H_j(s₂) − H_j(λ)) + H_d(s₁)]`, `z_v = ρ_v(s₁) z_θ`.

Results (the model, `Model`, lossless link).
* `Kv_Hj_lossless` (`K_v(s) = (m_a²/X) ω_b s/(s² + ω_b²)`, `H_j(s) = (m_a²/X) ω_b²/(s² + ω_b²)`),
  `Hd_lossless` (the direct term with the sideband reactances `X(1 ± μ)`), `Pθ_lossless`
  (`P_θθ = −i_dc0`, the Park element `P_θ = −(m_a² − m_a V cos δ₀)/X`), `Kθ_zero`
  (`K_θ(0) = P_θ + H_j(0) = m_a V cos δ₀/X`: the network path carries `m_a²/X`, the Park element the
  rest), `ρv_imag` (`z_v = jμ(1 + jω/ω_f) z_θ`).
* `kernel_hopf` — at `λ = jΩ`, `ω = 2Ω` the network kernel is
  `−z_θ · 12 (m_a²/X) ω_b Ω⁴/(ω_f (ω_b² − Ω²)(ω_b² − 4Ω²))`: the rotation and `E = m_a v` terms
  cancel except for the measurement filter.
* `pump_hopf` — exactly
  `D'(λ) g = −K [tan δ₀ S + (μ² tan δ₀ − jμ)/(1 − μ²)] − z_θ · 12 (m_a²/X) ω_b Ω⁴/(ω_f …)`,
  `S = 1 − z_θ`, `K = m_a V cos δ₀/X` (in the form without `tan`).
* `report20_sub_report22` — `(20) − (22) = tan δ₀ μ² (1 − S)/(1 − μ²)`.

Corrections.
* The full-order form of the sideband ratio is the matching report's (20),
  `tan δ₀ S + (μ² tan δ₀ − jμ)/(1 − μ²)`, exact at a Hopf mode for an ideal measurement filter
  (`pump_hopf`), not the unified report's (22); the same structure holds for droop
  (`DroopNetwork.pump_lossless`). The numerically smaller deviation of (22) reported in §8 comes from
  `S ≈ c_κ`, `σ ≠ 0` and the `1/ω_f` term, not from the form of (22).
* The exact cancellation of §5.5 is `kernel_hopf`: with `z_v = jμ z_θ` (ideal filter) the network
  kernel vanishes at the Hopf mode; for a finite filter it is `O(Ω⁴/ω_f)`.

Family and connection conclusions.
None: static evidence on the matching core with a dynamic link (linearization, modulation,
eigentriple, pump coefficient).
-/

noncomputable section
namespace powerlib.GFM
namespace MatchingNetwork
open Complex ComplexConjugate Matrix

/-! ## Generic linear algebra of the matching core with a dynamic network -/

/-- Equilibrium data in the coordinates `(θ, v_f, v, i_s, i, ī)` (`v₀ = 1`). -/
structure Coeffs where
  ωb : ℂ
  ωf : ℂ
  C : ℂ
  G : ℂ
  τ : ℂ
  kdc : ℂ
  av : ℂ
  abv : ℂ
  e : ℂ
  eb : ℂ
  bi : ℂ
  bm : ℂ
  Pθ : ℂ
  Pi : ℂ
  Pm : ℂ
  Pθθ : ℂ

namespace Coeffs

variable (q : Coeffs)

/-- `ρ_v(s) = s(s + ω_f)/(ω_b ω_f)`: the DC voltage per converter angle (frequency kinematics). -/
def ρv (s : ℂ) : ℂ := s * (s + q.ωf) / (q.ωb * q.ωf)
/-- Network transfers of the EMF `m_a v e^{jθ}`: `Δi = h(s)(jΔθ + Δv)`, `Δī = h̃(s)(−jΔθ + Δv)`. -/
def h (s : ℂ) : ℂ := q.av / (s + q.e)
def ht (s : ℂ) : ℂ := q.abv / (s + q.eb)
def d (s : ℂ) : ℂ := q.bi / (s + q.e)
def dt (s : ℂ) : ℂ := q.bm / (s + q.eb)
/-- In-phase and quadrature DC-current transfers. -/
def Kv (s : ℂ) : ℂ := q.Pi * q.h s + q.Pm * q.ht s
def Hj (s : ℂ) : ℂ := I * (q.Pi * q.h s - q.Pm * q.ht s)
def Kd (s : ℂ) : ℂ := q.Pi * q.d s + q.Pm * q.dt s
def Hd (s : ℂ) : ℂ := I * (q.Pi * q.d s - q.Pm * q.dt s)
/-- `K_θ(s) = P_θ + H_j(s)`: DC current per converter angle. -/
def Kθ (s : ℂ) : ℂ := q.Pθ + q.Hj s
/-- `M(s) = C s + G + k_dc/(τ s + 1) + K_v(s)`. -/
def M (s : ℂ) : ℂ := q.C * s + q.G + q.kdc / (q.τ * s + 1) + q.Kv s
/-- Characteristic function `D(s) = M(s) ρ_v(s) + K_θ(s)`. -/
def D (s : ℂ) : ℂ := q.M s * q.ρv s + q.Kθ s
/-- `D'(s)`. -/
def Dd (s : ℂ) : ℂ :=
  (2 * s + q.ωf) * q.M s / (q.ωb * q.ωf) + q.C * q.ρv s -
    q.τ * q.kdc * q.ρv s / (q.τ * s + 1) ^ 2 - q.Pi * q.h s * (I + q.ρv s) / (s + q.e) -
      q.Pm * q.ht s * (-I + q.ρv s) / (s + q.eb)

def J : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0, q.ωb, 0, 0, 0, 0;
    0, -q.ωf, q.ωf, 0, 0, 0;
    -q.Pθ / q.C, 0, -q.G / q.C, 1 / q.C, -q.Pi / q.C, -q.Pm / q.C;
    0, 0, -q.kdc / q.τ, -1 / q.τ, 0, 0;
    I * q.av, 0, q.av, 0, -q.e, 0;
    -I * q.abv, 0, q.abv, 0, 0, -q.eb]

def B : Fin 6 → ℂ := ![0, 0, 0, 0, q.bi, q.bm]

/-- `A₁ = DJ[z]`: the Park element and the two current entries of the DC row, and the Park
rotations and the `v`-bilinearity (`E = m_a v`) of the network rows. -/
def A1 (z : Fin 6 → ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    -(q.Pθθ * z 0 - I * q.Pi * z 4 + I * q.Pm * z 5) / q.C, 0, 0, 0, I * q.Pi * z 0 / q.C,
      -(I * q.Pm * z 0) / q.C;
    0, 0, 0, 0, 0, 0;
    -q.av * z 0 + I * q.av * z 2, 0, I * q.av * z 0, 0, 0, 0;
    -q.abv * z 0 - I * q.abv * z 2, 0, -I * q.abv * z 0, 0, 0, 0]

def right (s : ℂ) : Fin 6 → ℂ :=
  ![1, s / q.ωb, q.ρv s, -q.kdc * q.ρv s / (q.τ * s + 1), q.h s * (I + q.ρv s),
    q.ht s * (-I + q.ρv s)]

def left (s : ℂ) : Fin 6 → ℂ :=
  let w := 1 / q.Dd s
  ![w * (s + q.ωf) * q.M s / (q.ωb * q.ωf), w * q.M s / q.ωf, q.C * w,
    w * q.τ / (q.τ * s + 1), -(w * q.Pi) / (s + q.e), -(w * q.Pm) / (s + q.eb)]

/-- Forced response to the grid angle `θ̂_g = 1`: `z_θ = −K_d(s)/D(s)`. -/
def forcedθ (s : ℂ) : ℂ := -q.Kd s / q.D s

def forced (s : ℂ) : Fin 6 → ℂ :=
  ![q.forcedθ s, s * q.forcedθ s / q.ωb, q.ρv s * q.forcedθ s,
    -q.kdc * q.ρv s * q.forcedθ s / (q.τ * s + 1),
    q.h s * (I * q.forcedθ s + q.ρv s * q.forcedθ s) + q.d s,
    q.ht s * (-I * q.forcedθ s + q.ρv s * q.forcedθ s) + q.dt s]

def pumpc (A : Matrix (Fin 6) (Fin 6) ℂ) (u rbar : Fin 6 → ℂ) : ℂ := u ⬝ᵥ (A *ᵥ rbar)

variable {q}

@[tmio T, powerlib_foundation] theorem right_eig {lam : ℂ} (hωb : q.ωb ≠ 0) (hωf : q.ωf ≠ 0) (hC : q.C ≠ 0) (hτ : q.τ ≠ 0)
    (h1 : lam + q.e ≠ 0) (h2 : lam + q.eb ≠ 0) (h3 : q.τ * lam + 1 ≠ 0) (hD : q.D lam = 0) :
    q.J *ᵥ q.right lam = lam • q.right lam := by
  have hD' : (q.C * lam + q.G + q.kdc / (q.τ * lam + 1) + (q.Pi * q.h lam + q.Pm * q.ht lam)) *
      q.ρv lam + (q.Pθ + I * (q.Pi * q.h lam - q.Pm * q.ht lam)) = 0 := hD
  have e1 : q.h lam * (lam + q.e) = q.av := by simp only [h]; field_simp
  have e2 : q.ht lam * (lam + q.eb) = q.abv := by simp only [ht]; field_simp
  have eρ : q.ρv lam * (q.ωb * q.ωf) = lam * (lam + q.ωf) := by simp only [ρv]; field_simp
  funext i
  fin_cases i <;> simp [J, right, mulVec, dotProduct, Fin.sum_univ_six]
  · field_simp
  · field_simp; linear_combination eρ
  · have h3' : 1 + q.τ * lam ≠ 0 := by rwa [add_comm]
    linear_combination (norm := (field_simp; ring)) (-1 / q.C) * hD'
  · field_simp; ring
  · linear_combination (-(I + q.ρv lam)) * e1
  · linear_combination (-(-I + q.ρv lam)) * e2

@[tmio T, powerlib_foundation] theorem left_eig {lam : ℂ} (hωb : q.ωb ≠ 0) (hωf : q.ωf ≠ 0) (hC : q.C ≠ 0) (hτ : q.τ ≠ 0)
    (h1 : lam + q.e ≠ 0) (h2 : lam + q.eb ≠ 0) (h3 : q.τ * lam + 1 ≠ 0) (hD : q.D lam = 0) :
    vecMul (q.left lam) q.J = lam • q.left lam := by
  have hD' : (q.C * lam + q.G + q.kdc / (q.τ * lam + 1) + (q.Pi * (q.av / (lam + q.e)) +
      q.Pm * (q.abv / (lam + q.eb)))) * (lam * (lam + q.ωf) / (q.ωb * q.ωf)) +
      (q.Pθ + I * (q.Pi * (q.av / (lam + q.e)) - q.Pm * (q.abv / (lam + q.eb)))) = 0 := hD
  simp only [left, M, Kv, h, ht]
  generalize 1 / q.Dd lam = w
  funext i
  fin_cases i <;> simp [J, vecMul, dotProduct, Fin.sum_univ_six]
  · field_simp at hD' ⊢
    linear_combination (-w) * hD'
  · field_simp; ring
  · field_simp; ring
  · field_simp; ring
  · field_simp; ring
  · field_simp; ring

@[tmio T, powerlib_foundation] theorem left_right {lam : ℂ} (hωb : q.ωb ≠ 0) (hωf : q.ωf ≠ 0)
    (h1 : lam + q.e ≠ 0) (h2 : lam + q.eb ≠ 0) (hDd : q.Dd lam ≠ 0) :
    q.left lam ⬝ᵥ q.right lam = 1 := by
  have hsum : q.left lam ⬝ᵥ q.right lam = 1 / q.Dd lam *
      ((lam + q.ωf) * q.M lam / (q.ωb * q.ωf) + q.M lam / q.ωf * (lam / q.ωb) +
        q.C * q.ρv lam + q.τ / (q.τ * lam + 1) * (-q.kdc * q.ρv lam / (q.τ * lam + 1)) +
        -q.Pi / (lam + q.e) * (q.h lam * (I + q.ρv lam)) +
        -q.Pm / (lam + q.eb) * (q.ht lam * (-I + q.ρv lam))) := by
    simp [left, right, dotProduct, Fin.sum_univ_six]
    ring
  have hT : (lam + q.ωf) * q.M lam / (q.ωb * q.ωf) + q.M lam / q.ωf * (lam / q.ωb) +
      q.C * q.ρv lam + q.τ / (q.τ * lam + 1) * (-q.kdc * q.ρv lam / (q.τ * lam + 1)) +
      -q.Pi / (lam + q.e) * (q.h lam * (I + q.ρv lam)) +
      -q.Pm / (lam + q.eb) * (q.ht lam * (-I + q.ρv lam)) = q.Dd lam := by
    simp only [Dd]
    generalize q.M lam = MM
    generalize q.h lam = c1
    generalize q.ht lam = c2
    generalize q.ρv lam = r
    field_simp
    ring
  rw [hsum, hT, one_div_mul_cancel hDd]

@[tmio T, powerlib_foundation] theorem forced_eq {s : ℂ} (hωb : q.ωb ≠ 0) (hωf : q.ωf ≠ 0) (hC : q.C ≠ 0) (hτ : q.τ ≠ 0)
    (hD : q.D s ≠ 0) (h1 : s + q.e ≠ 0) (h2 : s + q.eb ≠ 0) (h3 : q.τ * s + 1 ≠ 0) :
    (s • (1 : Matrix (Fin 6) (Fin 6) ℂ) - q.J) *ᵥ q.forced s = q.B := by
  have hDdef : q.D s = q.M s * q.ρv s + q.Kθ s := rfl
  have hM : q.M s = q.C * s + q.G + q.kdc / (q.τ * s + 1) + q.Kv s := rfl
  have hKθ : q.Kθ s = q.Pθ + I * (q.Pi * q.h s - q.Pm * q.ht s) := rfl
  have hKv : q.Kv s = q.Pi * q.h s + q.Pm * q.ht s := rfl
  have hKd : q.Kd s = q.Pi * q.d s + q.Pm * q.dt s := rfl
  have e1 : q.h s * (s + q.e) = q.av := by simp only [h]; field_simp
  have e2 : q.ht s * (s + q.eb) = q.abv := by simp only [ht]; field_simp
  have e3 : q.d s * (s + q.e) = q.bi := by simp only [d]; field_simp
  have e4 : q.dt s * (s + q.eb) = q.bm := by simp only [dt]; field_simp
  have eρ : q.ρv s * (q.ωb * q.ωf) = s * (s + q.ωf) := by simp only [ρv]; field_simp
  funext i
  fin_cases i
  · simp [J, forced, B, mulVec, dotProduct, Fin.sum_univ_six, Matrix.one_apply]
    field_simp; ring
  · simp [J, forced, B, mulVec, dotProduct, Fin.sum_univ_six, Matrix.one_apply]
    field_simp; linear_combination (-(q.forcedθ s)) * eρ
  · simp [J, forced, B, mulVec, dotProduct, Fin.sum_univ_six, Matrix.one_apply, forcedθ]
    generalize q.D s = DD at hD hDdef ⊢
    rw [hKd] at *
    field_simp
    rw [hDdef, hM, hKθ, hKv]
    field_simp
    ring
  · simp [J, forced, B, mulVec, dotProduct, Fin.sum_univ_six, Matrix.one_apply]
    field_simp; ring
  · simp [J, forced, B, mulVec, dotProduct, Fin.sum_univ_six, Matrix.one_apply]
    linear_combination (I * q.forcedθ s + q.ρv s * q.forcedθ s) * e1 + e3
  · simp [J, forced, B, mulVec, dotProduct, Fin.sum_univ_six, Matrix.one_apply]
    linear_combination (-I * q.forcedθ s + q.ρv s * q.forcedθ s) * e2 + e4

/-- Kernel form of the pump coefficient:
`g = (1/D'(λ)) [−P_θθ z_θ − z_θ (K_v(s₁) + K_v(s₂) − K_v(λ)) + z_v (H_j(s₁) − H_j(λ))
+ z_θ ρ_v(s₂) (H_j(s₂) − H_j(λ)) + H_d(s₁)]`, `z_v = ρ_v(s₁) z_θ`. -/
@[tmio T, powerlib_foundation] theorem pump_kernel (s1 s2 lam : ℂ) (hC : q.C ≠ 0) :
    pumpc (q.A1 (q.forced s1)) (q.left lam) (q.right s2) =
      1 / q.Dd lam * (-q.Pθθ * q.forcedθ s1 -
        q.forcedθ s1 * (q.Kv s1 + q.Kv s2 - q.Kv lam) +
        q.ρv s1 * q.forcedθ s1 * (q.Hj s1 - q.Hj lam) +
        q.forcedθ s1 * q.ρv s2 * (q.Hj s2 - q.Hj lam) + q.Hd s1) := by
  simp only [pumpc, A1, forced, left, right, Kv, Hj, Hd, h, ht, d, dt, mulVec, dotProduct,
    Fin.sum_univ_six]
  simp
  field_simp
  ring_nf
  rw [I_sq]
  ring

end Coeffs
/-! ## The model of the source -/

/-- Parameters of the matching control with a DC source and a dynamic series link (the source's
check 3). -/
structure Model where
  ωb : ℝ
  ωf : ℝ
  C : ℝ
  G : ℝ
  τ : ℝ
  kdc : ℝ
  ma : ℝ
  V : ℝ
  R : ℝ
  X : ℝ

namespace Model

variable (p : Model)

def Z : ℂ := (p.R : ℂ) + (p.X : ℂ) * I
def Zc : ℂ := (p.R : ℂ) - (p.X : ℂ) * I
def an : ℝ := p.ωb / p.X
/-- Modulation index times the rotation, `m_a e^{jθ}`, and its conjugate partner. -/
def φ (θ : ℂ) : ℂ := p.ma * exp (θ * I)
def φt (θ : ℂ) : ℂ := p.ma * exp (-(θ * I))
/-- Current dynamics with the EMF `m_a v e^{jθ}`. -/
def net (θg θ v i : ℂ) : ℂ := p.an * (p.φ θ * v - p.V * exp (θg * I) - p.Z * i)
def nett (θg θ v m : ℂ) : ℂ := p.an * (p.φt θ * v - p.V * exp (-(θg * I)) - p.Zc * m)
/-- DC current drawn by the converter, `i_dc = m_a Re(e^{jθ} ī)`. -/
def idc (θ i m : ℂ) : ℂ := (p.φ θ * m + p.φt θ * i) / 2

/-- The field in the coordinates `(θ, v_f, v, i_s, i, ī)`. -/
def field (θg : ℂ) (Ist : ℝ) (x : Fin 6 → ℂ) : Fin 6 → ℂ :=
  ![p.ωb * (x 1 - 1), p.ωf * (x 2 - x 1), (x 3 - p.G * x 2 - p.idc (x 0) (x 4) (x 5)) / p.C,
    (Ist - p.kdc * (x 2 - 1) - x 3) / p.τ, p.net θg (x 0) (x 2) (x 4), p.nett θg (x 0) (x 2) (x 5)]

@[tmio M, powerlib_domain] theorem conj_φ (θ : ℝ) : conj (p.φ θ) = p.φt θ := by
  simp only [φ, φt, map_mul, conj_ofReal, ← Complex.exp_conj, conj_I]
  congr 2; ring

@[tmio M, powerlib_domain] theorem idc_real (θ : ℝ) (i : ℂ) : p.idc θ i (conj i) = ((p.φ θ * conj i).re : ℂ) := by
  rw [idc, ← p.conj_φ]
  apply Complex.ext
  all_goals (simp [Complex.mul_re, Complex.mul_im]; try ring)

/-! ### Partial derivatives -/

def idcθ (θ i m : ℂ) : ℂ := (I * p.φ θ * m - I * p.φt θ * i) / 2
def idci (θ : ℂ) : ℂ := p.φt θ / 2
def idcm (θ : ℂ) : ℂ := p.φ θ / 2
def idcθθ (θ i m : ℂ) : ℂ := (-p.φ θ * m - p.φt θ * i) / 2

@[tmio M, powerlib_domain] theorem hasDerivAt_φ (θ : ℂ) : HasDerivAt p.φ (I * p.φ θ) θ := by
  have h := (((hasDerivAt_id θ).mul_const I).cexp).const_mul (p.ma : ℂ)
  convert h using 1
  · funext x; simp [φ]
  · simp [φ]; ring

@[tmio M, powerlib_domain] theorem hasDerivAt_φt (θ : ℂ) : HasDerivAt p.φt (-I * p.φt θ) θ := by
  have h := (((hasDerivAt_id θ).mul_const I).neg.cexp).const_mul (p.ma : ℂ)
  convert h using 1
  · funext x; simp [φt]
  · simp [φt]; ring

@[tmio M, powerlib_domain] theorem hasDerivAt_idc_θ (θ i m : ℂ) : HasDerivAt (fun θ => p.idc θ i m) (p.idcθ θ i m) θ := by
  have h := (((p.hasDerivAt_φ θ).mul_const m).add ((p.hasDerivAt_φt θ).mul_const i)).div_const 2
  convert h using 1
  · funext x; simp [idc]
  · simp only [idcθ]; ring

@[tmio M, powerlib_domain] theorem hasDerivAt_idc_i (θ i m : ℂ) : HasDerivAt (fun i => p.idc θ i m) (p.idci θ) i := by
  have h := (((hasDerivAt_id i).const_mul (p.φt θ)).const_add (p.φ θ * m)).div_const 2
  convert h using 1
  · funext x; simp [idc]
  · simp [idci]

@[tmio M, powerlib_domain] theorem hasDerivAt_idc_m (θ i m : ℂ) : HasDerivAt (fun m => p.idc θ i m) (p.idcm θ) m := by
  have h := (((hasDerivAt_id m).const_mul (p.φ θ)).add_const (p.φt θ * i)).div_const 2
  convert h using 1
  · funext x; simp [idc]
  · simp [idcm]

@[tmio M, powerlib_domain] theorem hasDerivAt_net_θ (θg θ v i : ℂ) :
    HasDerivAt (fun θ => p.net θg θ v i) (p.an * (I * p.φ θ * v)) θ := by
  have h := ((((p.hasDerivAt_φ θ).mul_const v).sub_const (p.V * exp (θg * I))).sub_const
    (p.Z * i)).const_mul (p.an : ℂ)
  convert h using 1
  funext x; simp [net]

@[tmio M, powerlib_domain] theorem hasDerivAt_net_v (θg θ v i : ℂ) :
    HasDerivAt (fun v => p.net θg θ v i) (p.an * p.φ θ) v := by
  have h := ((((hasDerivAt_id v).const_mul (p.φ θ)).sub_const (p.V * exp (θg * I))).sub_const
    (p.Z * i)).const_mul (p.an : ℂ)
  convert h using 1
  · funext x; simp [net]
  · simp

@[tmio M, powerlib_domain] theorem hasDerivAt_net_i (θg θ v i : ℂ) :
    HasDerivAt (fun i => p.net θg θ v i) (-(p.an * p.Z)) i := by
  have h := (((hasDerivAt_id i).const_mul p.Z).const_sub (p.φ θ * v - p.V * exp (θg * I))).const_mul
    (p.an : ℂ)
  convert h using 1
  · funext x; simp [net]
  · ring

@[tmio M, powerlib_domain] theorem hasDerivAt_net_θg (θg θ v i : ℂ) :
    HasDerivAt (fun θg => p.net θg θ v i) (-(p.an * (p.V * (I * exp (θg * I))))) θg := by
  have h := ((((hasDerivAt_id θg).mul_const I).cexp.const_mul (p.V : ℂ)).const_sub
    (p.φ θ * v)).sub_const (p.Z * i) |>.const_mul (p.an : ℂ)
  convert h using 1
  · funext x; simp [net]
  · simp only [id]; ring

/-! ### The modulation as the directional derivative of the Jacobian -/

@[tmio M, powerlib_domain] theorem line_idcθ (θ i m zθ zi zm : ℂ) :
    HasDerivAt (fun t => p.idcθ (θ + t * zθ) (i + t * zi) (m + t * zm))
      (p.idcθθ θ i m * zθ + (-I * p.idci θ) * zi + (I * p.idcm θ) * zm) 0 := by
  have hL : HasDerivAt (fun t : ℂ => θ + t * zθ) zθ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const zθ).const_add θ
  have hi : HasDerivAt (fun t : ℂ => i + t * zi) zi 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const zi).const_add i
  have hm : HasDerivAt (fun t : ℂ => m + t * zm) zm 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const zm).const_add m
  have hφ := (p.hasDerivAt_φ (θ + 0 * zθ)).comp (0 : ℂ) hL
  have hφt := (p.hasDerivAt_φt (θ + 0 * zθ)).comp (0 : ℂ) hL
  simp only [zero_mul, add_zero] at hφ hφt
  have h := ((((hφ.const_mul I).mul hm).sub ((hφt.const_mul I).mul hi))).div_const 2
  convert h using 1
  · funext t; simp [idcθ]
  · simp only [idcθθ, idci, idcm, Function.comp_def]; ring_nf; rw [I_sq]; ring

@[tmio M, powerlib_domain] theorem line_idci (θ zθ : ℂ) :
    HasDerivAt (fun t => p.idci (θ + t * zθ)) (-I * p.idci θ * zθ) 0 := by
  have hL : HasDerivAt (fun t : ℂ => θ + t * zθ) zθ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const zθ).const_add θ
  have h := ((p.hasDerivAt_φt (θ + 0 * zθ)).comp (0 : ℂ) hL).div_const 2
  simp only [zero_mul, add_zero] at h
  convert h using 1
  · funext t; simp [idci]
  · simp only [idci]; ring

@[tmio M, powerlib_domain] theorem line_idcm (θ zθ : ℂ) :
    HasDerivAt (fun t => p.idcm (θ + t * zθ)) (I * p.idcm θ * zθ) 0 := by
  have hL : HasDerivAt (fun t : ℂ => θ + t * zθ) zθ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const zθ).const_add θ
  have h := ((p.hasDerivAt_φ (θ + 0 * zθ)).comp (0 : ℂ) hL).div_const 2
  simp only [zero_mul, add_zero] at h
  convert h using 1
  · funext t; simp [idcm]
  · simp only [idcm]; ring

/-- `(A₁)_{i θ} = −(ω_b/X) φ z_θ + j (ω_b/X) φ z_v` at `v₀ = 1`: the Park rotation and the
`E = m_a v` bilinearity of the network row. -/
@[tmio M, powerlib_domain] theorem line_netθ (θ zθ zv : ℂ) :
    HasDerivAt (fun t => (p.an : ℂ) * (I * p.φ (θ + t * zθ) * (1 + t * zv)))
      (-((p.an : ℂ) * p.φ θ) * zθ + I * ((p.an : ℂ) * p.φ θ) * zv) 0 := by
  have hL : HasDerivAt (fun t : ℂ => θ + t * zθ) zθ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const zθ).const_add θ
  have hv : HasDerivAt (fun t : ℂ => 1 + t * zv) zv 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const zv).const_add 1
  have hφ := (p.hasDerivAt_φ (θ + 0 * zθ)).comp (0 : ℂ) hL
  simp only [zero_mul, add_zero] at hφ
  have h := (((hφ.const_mul I).mul hv)).const_mul (p.an : ℂ)
  convert h using 1
  · funext t; simp
  · simp; ring_nf; rw [I_sq]; ring

@[tmio M, powerlib_domain] theorem line_netv (θ zθ : ℂ) :
    HasDerivAt (fun t => (p.an : ℂ) * p.φ (θ + t * zθ)) (I * ((p.an : ℂ) * p.φ θ) * zθ) 0 := by
  have hL : HasDerivAt (fun t : ℂ => θ + t * zθ) zθ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const zθ).const_add θ
  have h := ((p.hasDerivAt_φ (θ + 0 * zθ)).comp (0 : ℂ) hL).const_mul (p.an : ℂ)
  simp only [zero_mul, add_zero] at h
  convert h using 1
  simp; ring

/-! ### Equilibrium and coefficients -/

def i0 (δ0 : ℂ) : ℂ := (p.φ δ0 - p.V) / p.Z
def m0 (δ0 : ℂ) : ℂ := (p.φt δ0 - p.V) / p.Zc

/-- The coefficients of the linearized model at the angle `δ₀`, `v₀ = 1`, `θ_g = 0`. -/
def coeffs (δ0 : ℂ) : Coeffs where
  ωb := p.ωb
  ωf := p.ωf
  C := p.C
  G := p.G
  τ := p.τ
  kdc := p.kdc
  av := p.an * p.φ δ0
  abv := p.an * p.φt δ0
  e := p.an * p.Z
  eb := p.an * p.Zc
  bi := -(p.an * (p.V * I))
  bm := p.an * (p.V * I)
  Pθ := p.idcθ δ0 (p.i0 δ0) (p.m0 δ0)
  Pi := p.idci δ0
  Pm := p.idcm δ0
  Pθθ := p.idcθθ δ0 (p.i0 δ0) (p.m0 δ0)

/-! ### Lossless link: closed forms -/

@[tmio M, powerlib_domain] theorem φ_mul_φt (θ : ℂ) : p.φ θ * p.φt θ = (p.ma : ℂ) ^ 2 := by
  simp only [φ, φt]
  rw [show (p.ma : ℂ) * exp (θ * I) * (p.ma * exp (-(θ * I))) =
    (p.ma : ℂ) ^ 2 * (exp (θ * I) * exp (-(θ * I))) by ring, ← Complex.exp_add]
  simp

@[tmio M, powerlib_domain] theorem e_lossless (hR : p.R = 0) (hX : p.X ≠ 0) : (p.an : ℂ) * p.Z = p.ωb * I := by
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  simp only [an, Z, hR]; push_cast; field_simp; ring

@[tmio M, powerlib_domain] theorem eb_lossless (hR : p.R = 0) (hX : p.X ≠ 0) : (p.an : ℂ) * p.Zc = -(p.ωb * I) := by
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  simp only [an, Zc, hR]; push_cast; field_simp; ring

/-- Lossless link: `K_v(s) = (m_a²/X) ω_b s/(s² + ω_b²)` and `H_j(s) = (m_a²/X) ω_b²/(s² + ω_b²)`,
independent of the load. -/
@[tmio M, powerlib_domain] theorem Kv_Hj_lossless (δ0 s : ℂ) (hR : p.R = 0) (hX : p.X ≠ 0)
    (h1 : s + p.ωb * I ≠ 0) (h2 : s - p.ωb * I ≠ 0) :
    (p.coeffs δ0).Kv s = (p.ma : ℂ) ^ 2 / p.X * p.ωb * s / (s ^ 2 + (p.ωb : ℂ) ^ 2) ∧
      (p.coeffs δ0).Hj s = (p.ma : ℂ) ^ 2 / p.X * (p.ωb : ℂ) ^ 2 / (s ^ 2 + (p.ωb : ℂ) ^ 2) := by
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hs : s ^ 2 + (p.ωb : ℂ) ^ 2 = (s + p.ωb * I) * (s - p.ωb * I) := by
    ring_nf; rw [I_sq]; ring
  have hV := p.φ_mul_φt δ0
  simp only [Coeffs.Kv, Coeffs.Hj, Coeffs.h, Coeffs.ht, coeffs, idci, idcm, p.e_lossless hR hX,
    p.eb_lossless hR hX]
  rw [show s + -((p.ωb : ℂ) * I) = s - p.ωb * I by ring, hs]
  have hsum : (s + p.ωb * I) + (s - p.ωb * I) = 2 * s := by ring
  have hdiff : (s + p.ωb * I) - (s - p.ωb * I) = 2 * (p.ωb * I) := by ring
  generalize p.φ δ0 = A at hV ⊢
  generalize p.φt δ0 = B at hV ⊢
  rw [show (p.ma : ℂ) ^ 2 = A * B from hV.symm]
  generalize s + p.ωb * I = u1 at h1 hsum hdiff ⊢
  generalize s - p.ωb * I = u2 at h2 hsum hdiff ⊢
  simp only [an]
  push_cast
  constructor
  · field_simp
    linear_combination (A * B * p.ωb) * hsum
  · field_simp
    linear_combination (-(I * A * B * p.ωb)) * hdiff + (-2 * A * B * (p.ωb : ℂ) ^ 2) * I_sq

/-- Lossless link: `−H_d(jω) = (m_a V/X) ω_b(ω_b sin δ₀ − jω cos δ₀)/(ω_b² − ω²)`: the direct
grid-angle term with the sideband reactances `X(1 ± μ)`. -/
@[tmio M, powerlib_domain] theorem Hd_lossless (δ0 ω : ℝ) (hR : p.R = 0) (hX : p.X ≠ 0) (hωb : p.ωb ≠ 0)
    (hμ : ω ^ 2 ≠ p.ωb ^ 2) :
    -(p.coeffs δ0).Hd ((ω : ℂ) * I) = ((p.ma * p.V / p.X : ℝ) : ℂ) *
      (p.ωb * (p.ωb * (Real.sin δ0 : ℂ) - I * ω * Real.cos δ0) / ((p.ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2)) := by
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hωc : (p.ωb : ℂ) ≠ 0 := by exact_mod_cast hωb
  have h1 : (ω : ℂ) + p.ωb ≠ 0 := by
    intro h
    have : ω + p.ωb = 0 := by exact_mod_cast h
    apply hμ; have : ω = -p.ωb := by linarith
    rw [this]; ring
  have h2 : (ω : ℂ) - p.ωb ≠ 0 := by
    intro h
    have : ω - p.ωb = 0 := by exact_mod_cast h
    apply hμ; have : ω = p.ωb := by linarith
    rw [this]
  have hφ : p.φ δ0 = p.ma * ((Real.cos δ0 : ℂ) + Real.sin δ0 * I) := by
    simp only [φ]; rw [Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have hφt : p.φt δ0 = p.ma * ((Real.cos δ0 : ℂ) - Real.sin δ0 * I) := by
    simp only [φt]; rw [PSCActiveDamping.exp_neg_mul_I]
  simp only [Coeffs.Hd, Coeffs.d, Coeffs.dt, coeffs, idci, idcm, p.e_lossless hR hX,
    p.eb_lossless hR hX, hφ, hφt]
  rw [show (ω : ℂ) * I + p.ωb * I = (ω + p.ωb) * I by ring,
    show (ω : ℂ) * I + -(p.ωb * I) = (ω - p.ωb) * I by ring,
    show (p.ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2 = -((ω + p.ωb) * (ω - p.ωb)) by ring]
  generalize Real.cos δ0 = c
  generalize Real.sin δ0 = sn
  have hsum : ((ω : ℂ) + p.ωb) + ((ω : ℂ) - p.ωb) = 2 * ω := by ring
  have hdiff : ((ω : ℂ) + p.ωb) - ((ω : ℂ) - p.ωb) = 2 * p.ωb := by ring
  generalize (ω : ℂ) + p.ωb = u1 at h1 hsum hdiff ⊢
  generalize (ω : ℂ) - p.ωb = u2 at h2 hsum hdiff ⊢
  simp only [an]
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  linear_combination (I * p.ma * p.V * c) * hsum - (p.ma * p.V * sn) * hdiff

/-- Lossless link: `P_θθ = −i_dc0 = −m_a V sin δ₀/X` and the Park element
`P_θ = −(m_a² − m_a V cos δ₀)/X`. -/
@[tmio M, powerlib_domain] theorem Pθ_lossless (δ0 : ℝ) (hR : p.R = 0) (hX : p.X ≠ 0) :
    (p.coeffs δ0).Pθθ = ((-(p.ma * p.V * Real.sin δ0 / p.X)) : ℝ) ∧
      (p.coeffs δ0).Pθ = ((-(p.ma ^ 2 - p.ma * p.V * Real.cos δ0) / p.X) : ℝ) := by
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hφ : p.φ δ0 = p.ma * ((Real.cos δ0 : ℂ) + Real.sin δ0 * I) := by
    simp only [φ]; rw [Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have hφt : p.φt δ0 = p.ma * ((Real.cos δ0 : ℂ) - Real.sin δ0 * I) := by
    simp only [φt]; rw [PSCActiveDamping.exp_neg_mul_I]
  have hsc := Real.cos_sq_add_sin_sq δ0
  simp only [coeffs, idcθθ, idcθ, i0, m0, Z, Zc, hR, hφ, hφt]
  generalize Real.cos δ0 = c at *
  generalize Real.sin δ0 = sn at *
  have hsc' : (c : ℂ) ^ 2 + (sn : ℂ) ^ 2 = 1 := by exact_mod_cast hsc
  constructor
  · push_cast
    field_simp
    ring_nf
  · have hI4 : I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, I_sq]; norm_num
    push_cast
    field_simp
    ring_nf
    simp only [I_sq, hI4]
    linear_combination (-2 * (p.ma : ℂ) ^ 2 * (p.X : ℂ) ^ 2) * hsc'

/-- The quasi-static synchronizing coefficient is the sum of the Park element and the network
path: `K_θ(0) = P_θ + H_j(0) = m_a V cos δ₀/X`; the Park element is the fraction
`(m_a − V cos δ₀)/m_a`-small part `K_rot = (m_a² − m_a V cos δ₀)/X` (`O(δ₀²)` for `m_a = V`). -/
@[tmio M, powerlib_domain] theorem Kθ_zero (δ0 : ℝ) (hR : p.R = 0) (hX : p.X ≠ 0) (hωb : p.ωb ≠ 0) :
    (p.coeffs δ0).Kθ 0 = ((p.ma * p.V * Real.cos δ0 / p.X : ℝ) : ℂ) := by
  have hωc : (p.ωb : ℂ) ≠ 0 := by exact_mod_cast hωb
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  have h1 : (0 : ℂ) + p.ωb * I ≠ 0 := by simp [hωc]
  have h2 : (0 : ℂ) - p.ωb * I ≠ 0 := by simp [hωc]
  rw [Coeffs.Kθ, (p.Pθ_lossless δ0 hR hX).2, (p.Kv_Hj_lossless δ0 0 hR hX h1 h2).2]
  push_cast
  field_simp
  ring

/-- Frequency kinematics of matching: the forced DC voltage is `z_v = ρ_v(jω) z_θ` with
`ρ_v(jω) = jμ(1 + jω/ω_f)`, `μ = ω/ω_b`: `z_v = jμ z_θ` for an ideal measurement filter. -/
@[tmio M, powerlib_domain] theorem ρv_imag (δ0 : ℂ) (ω : ℝ) (hωb : p.ωb ≠ 0) (hωf : p.ωf ≠ 0) :
    (p.coeffs δ0).ρv ((ω : ℂ) * I) = I * (ω / p.ωb) * (1 + I * ω / p.ωf) := by
  have hωb' : (p.ωb : ℂ) ≠ 0 := by exact_mod_cast hωb
  have hωf' : (p.ωf : ℂ) ≠ 0 := by exact_mod_cast hωf
  simp only [Coeffs.ρv, coeffs]
  field_simp
  ring

/-- The network kernel at a Hopf mode `λ = jΩ` driven at `ω = 2Ω` (lossless link): the
rotation terms and the `E = m_a v` terms cancel up to the measurement filter,
`−z_θ(K_v(s₁) + K_v(s₂) − K_v(λ)) + z_v(H_j(s₁) − H_j(λ)) + z_θ ρ_v(s₂)(H_j(s₂) − H_j(λ))
= −z_θ · 12 (m_a²/X) ω_b Ω⁴/(ω_f (ω_b² − Ω²)(ω_b² − 4Ω²))`. -/
@[tmio M, powerlib_domain] theorem kernel_hopf (δ0 : ℂ) (hR : p.R = 0) (hX : p.X ≠ 0) (hωf : p.ωf ≠ 0) {Ω : ℝ}
    (hΩ : 0 < Ω) (hΩb : 2 * Ω < p.ωb) (zθ : ℂ) :
    let q := p.coeffs δ0; let s1 := ((2 * Ω : ℝ) : ℂ) * I; let lam := (Ω : ℂ) * I;
    -zθ * (q.Kv s1 + q.Kv (conj lam) - q.Kv lam) + q.ρv s1 * zθ * (q.Hj s1 - q.Hj lam) +
        zθ * q.ρv (conj lam) * (q.Hj (conj lam) - q.Hj lam) =
      -zθ * (12 * ((p.ma : ℂ) ^ 2 / p.X) * p.ωb * (Ω : ℂ) ^ 4 /
        (p.ωf * (((p.ωb : ℂ) ^ 2 - (Ω : ℂ) ^ 2) * ((p.ωb : ℂ) ^ 2 - 4 * (Ω : ℂ) ^ 2)))) := by
  intro q s1 lam
  have hωb : 0 < p.ωb := by linarith
  have hne : ∀ x : ℝ, 0 ≤ x → x < p.ωb → ((x : ℂ) * I + p.ωb * I ≠ 0 ∧ (x : ℂ) * I - p.ωb * I ≠ 0 ∧
      -((x : ℂ) * I) + p.ωb * I ≠ 0 ∧ -((x : ℂ) * I) - p.ωb * I ≠ 0) := by
    intro x hx hxb
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> have := congrArg Complex.im h <;> simp at this <;>
      linarith
  have hc : conj lam = -((Ω : ℂ) * I) := by simp [lam, map_mul, conj_ofReal, conj_I]
  obtain ⟨a1, a2, -, -⟩ := hne Ω hΩ.le (by linarith)
  obtain ⟨b1, b2, -, -⟩ := hne (2 * Ω) (by linarith) hΩb
  obtain ⟨-, -, c1, c2⟩ := hne Ω hΩ.le (by linarith)
  have c1' : -((Ω : ℂ) * I) + p.ωb * I ≠ 0 := c1
  have c2' : -((Ω : ℂ) * I) - p.ωb * I ≠ 0 := c2
  have KH1 := p.Kv_Hj_lossless δ0 s1 hR hX b1 b2
  have KH2 := p.Kv_Hj_lossless δ0 (-((Ω : ℂ) * I)) hR hX c1' c2'
  have KHl := p.Kv_Hj_lossless δ0 lam hR hX a1 a2
  rw [hc, KH1.1, KH1.2, KH2.1, KH2.2, KHl.1, KHl.2]
  simp only [Coeffs.ρv, q, coeffs, s1, lam]
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hωc : (p.ωb : ℂ) ≠ 0 := by exact_mod_cast hωb.ne'
  have hωfc : (p.ωf : ℂ) ≠ 0 := by exact_mod_cast hωf
  have d1 : (p.ωb : ℂ) ^ 2 - (Ω : ℂ) ^ 2 ≠ 0 := by
    have : p.ωb ^ 2 - Ω ^ 2 ≠ 0 := by nlinarith
    exact_mod_cast this
  have d2 : (p.ωb : ℂ) ^ 2 - 4 * (Ω : ℂ) ^ 2 ≠ 0 := by
    have : p.ωb ^ 2 - 4 * Ω ^ 2 ≠ 0 := by nlinarith
    exact_mod_cast this
  have e1 : ((Ω : ℂ) * I) ^ 2 + (p.ωb : ℂ) ^ 2 = (p.ωb : ℂ) ^ 2 - (Ω : ℂ) ^ 2 := by
    ring_nf; rw [I_sq]; ring
  have e2 : (((2 * Ω : ℝ) : ℂ) * I) ^ 2 + (p.ωb : ℂ) ^ 2 = (p.ωb : ℂ) ^ 2 - 4 * (Ω : ℂ) ^ 2 := by
    push_cast; ring_nf; rw [I_sq]; ring
  have e3 : (-((Ω : ℂ) * I)) ^ 2 + (p.ωb : ℂ) ^ 2 = (p.ωb : ℂ) ^ 2 - (Ω : ℂ) ^ 2 := by
    ring_nf; rw [I_sq]; ring
  rw [e1, e2, e3]
  have d2' : (p.ωb : ℂ) ^ 2 - (Ω : ℂ) ^ 2 * 4 ≠ 0 := by rwa [mul_comm]
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- The exact pump of the matching core at a Hopf mode (lossless link, `ω = 2Ω`):
`D'(λ) g = −(m_a V/X) [sin δ₀ (1 − z_θ) + (ω² sin δ₀ − jω ω_b cos δ₀)/(ω_b² − ω²)]
− z_θ · 12 (m_a²/X) ω_b Ω⁴/(ω_f (ω_b² − Ω²)(ω_b² − 4Ω²))`: divided by
`−K = −m_a V cos δ₀/X`, the bracket is the matching report's (20),
`ρ = tan δ₀ S + (μ² tan δ₀ − jμ)/(1 − μ²)`, `S = 1 − z_θ`, up to a term of order `1/ω_f`. -/
@[tmio M, powerlib_domain] theorem pump_hopf (δ0 : ℝ) (hR : p.R = 0) (hX : p.X ≠ 0) (hωf : p.ωf ≠ 0) (hC : p.C ≠ 0)
    {Ω : ℝ} (hΩ : 0 < Ω) (hΩb : 2 * Ω < p.ωb) (hDd : (p.coeffs δ0).Dd ((Ω : ℂ) * I) ≠ 0) :
    let q := p.coeffs δ0; let ω : ℝ := 2 * Ω; let zθ := q.forcedθ ((ω : ℂ) * I);
    q.Dd ((Ω : ℂ) * I) * Coeffs.pumpc (q.A1 (q.forced ((ω : ℂ) * I))) (q.left ((Ω : ℂ) * I))
        (q.right (conj ((Ω : ℂ) * I))) =
      -((p.ma * p.V / p.X : ℝ) : ℂ) * ((Real.sin δ0 : ℂ) * (1 - zθ) +
          ((ω : ℂ) ^ 2 * Real.sin δ0 - I * ω * p.ωb * Real.cos δ0) / ((p.ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2)) -
        zθ * (12 * ((p.ma : ℂ) ^ 2 / p.X) * p.ωb * (Ω : ℂ) ^ 4 /
          (p.ωf * (((p.ωb : ℂ) ^ 2 - (Ω : ℂ) ^ 2) * ((p.ωb : ℂ) ^ 2 - 4 * (Ω : ℂ) ^ 2)))) := by
  intro q ω zθ
  have hωb : 0 < p.ωb := by linarith
  have hμ : ω ^ 2 ≠ p.ωb ^ 2 := by simp only [ω]; nlinarith
  have hCc : (p.C : ℂ) ≠ 0 := by exact_mod_cast hC
  have hk := p.kernel_hopf (δ0 : ℂ) hR hX hωf hΩ hΩb zθ
  have hd := p.Hd_lossless δ0 ω hR hX hωb.ne' hμ
  have hp := (p.Pθ_lossless δ0 hR hX).1
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
  have hD : (p.ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2 ≠ 0 := by
    have : p.ωb ^ 2 - ω ^ 2 ≠ 0 := fun h => hμ (by linarith)
    exact_mod_cast this
  push_cast
  field_simp
  ring

/-- (20) against (22), in the common normalization of `pump_hopf` (`K = m_a V cos δ₀/X` times
the ratio): `(20) − (22) = sin δ₀ z_θ ω²/(ω_b² − ω²)`, i.e. `tan δ₀ μ² (1 − S)/(1 − μ²)`; nonzero
at load whenever the forced angle `z_θ` is. -/
@[tmio T, powerlib_foundation] theorem report20_sub_report22 (sd cd ω ωb : ℝ) (z : ℂ)
    (hD : (ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2 ≠ 0) :
    ((sd : ℂ) * (1 - z) + ((ω : ℂ) ^ 2 * sd - I * ω * ωb * cd) / ((ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2)) -
        ωb * (ωb * (sd : ℂ) * (1 - z) - I * ω * cd) / ((ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2) =
      sd * z * (ω : ℂ) ^ 2 / ((ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2) := by
  field_simp
  ring

end Model

end MatchingNetwork
end powerlib.GFM
