import theorem.GridTiedConverter.GFM.PSCFull
import theorem.GridTiedConverter.GFM.NetworkLag

/-! # The droop core with a dynamic series link: the exact full-order sideband ratio (21)/(22)

The five-state droop core of the source's check 1 (`verification/check_droop_vsg.py`, port
measurement): states `(δ, p_m, p_f, i_d, i_q)`, grid angle `θ_g` as input, the series link with
its electromagnetic dynamics. The pump coefficient is derived exactly, in the same kernel form as
the active-damping PSC (`PSCFull`): the Park rotation of the EMF makes the power row and the
network rows pure rotations, and the pump reduces to the network transfers at `s₁ = jω`,
`s₂ = λ̄` and `λ`. For a lossless link this gives the exact full-order ratio and decides (22).

Model boundary.
* Grid frame: `(X/ω_b) i̇ = E e^{jδ} − V e^{jθ_g} − Z i`, `Z = R + jX` (`net`); port power
  `p = Re(E e^{jδ} ī)` (`pw`, `pw_real`); `δ̇ = m_p(P* − p_f)`, `ṗ_m = ω_m(p − p_m)`,
  `ṗ_f = ω₁(p_m − p_f)` (`field`); `E`, `V` constant. Measurement at the PCC (the `x_up` terms) is
  not covered here (`DroopSideband` treats it in the first-order network model).
* Coordinates `(δ, p_m, p_f, i, ī)` with the complexified functions, which agree with the model
  on the real slice (`pw_real`, `nett_real`); the Jacobian entries are the partial derivatives
  (`hasDerivAt_pw_δ`, `hasDerivAt_pw_i`, `hasDerivAt_pw_m`, `hasDerivAt_net_δ`, `hasDerivAt_net_i`,
  `hasDerivAt_net_θ`), the Jacobian does not depend on `θ_g` (the grid angle enters the current
  equation additively), and `A₁` is the directional derivative of the Jacobian along the forced
  response (`line_pwδ`, `line_pwi`, `line_pwm`, `line_netδ`). The passage to the real coordinates
  `(δ, p_m, p_f, i_d, i_q)` is the realification of `PSCFull.pump_realify` (stated there for four
  states and not restated here).
* `ρ_eff := g/(u_{p_m} ω_m K)` with `K = E V cos δ₀/X` is the effective ratio of the source (its
  check compares `|g_full|/|g_qs|` with `|ρ_pred|/|ρ_qs|`).

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §5.4 ((21), the full-order form (22)
`ρ^eff = (tan(δ₀ + φ_R) S_m − jμ_p)/(1 − μ_p²)` with the sideband reactances `X(1 ± μ_p)`),
Appendix B, §8 ("droop 的边带项", "matching 的全阶形式": 2–15% deviations of (22)), and
`verification/check_droop_vsg.py`.

Results (generic core, `Coeffs`).
* `right_eig`, `left_eig`, `left_right` (`u_{p_m} = −m_p ω₁/D'(λ)`), `forced_eq`
  (`z_δ = −m_p ω₁ ω_m K_θ(s)/D(s)`, `D(s) = s(s + ω₁)(s + ω_m) + m_p ω₁ ω_m K(s)`).
* `pump_eq`, `pump_kernel` — `g = u_{p_m} ω_m [z_δ (P_δδ + H_q(λ) − H_q(s₁) − H_q(s₂)) − H_θ(s₁)]`.

Results (the model, `Model`).
* `pump_kernel` — the kernel form holds for every link impedance (`Coeffs.pump_kernel` with the
  Park rotations of the port power).
* Lossless link: `Hq_lossless` (`H_q(s) = −(E²/X) ω_b s/(s² + ω_b²)`, independent of the load),
  `Hθ_lossless` (`−H_θ(jω) = (EV/X)(sin δ₀ − jμ cos δ₀)/(1 − μ²)`), `Pδδ_lossless`
  (`P_δδ = −p₀`), `pump_lossless` — exactly
  `ρ_eff = (tan δ₀ − jμ)/(1 − μ²) − z_δ (tan δ₀ + Q/K)`, `Q = −(H_q(λ) − H_q(jω) − H_q(λ̄))`.
* `hasDerivAt_K_zero` — `K'(0) = −K_d`, `K_d = 2E²RX²/(ω_b|Z|⁴)` (`NetworkLag.lagCoeff`): the lag
  `p ≈ Kδ − K_d δ̇` of §4.4 is the first Taylor term of the exact transfer.
* `exact_sub_report22` — exact minus (22) `= z_δ ((EV/X) sin δ₀ μ²/(1 − μ²) − Q)`;
  `kernel_hopf`, `report22_ne` — at no load and a Hopf mode `λ = jΩ`, `ω = 2Ω`, the kernel is
  `6j (E²/X) ω_b Ω³/((ω_b² − Ω²)(ω_b² − 4Ω²)) ≠ 0` and (22) is not exact.

Corrections.
* (22) is not the exact full-order ratio. In the exact ratio the factor `1/(1 − μ²)` multiplies
  `tan δ₀ − jμ` (the direct grid-angle term, whose two sidebands see `X(1 ± μ)`), while the
  forced-response term `−z_δ tan δ₀` keeps no such factor and acquires the network kernel `Q`
  (at a Hopf mode `Q ∝ Ω³`, `kernel_hopf`). (22) applies `1/(1 − μ²)` to the whole
  `S = 1 − z_δ`; the error is `z_δ (tan δ₀ μ²/(1 − μ²) − Q/K)` (`exact_sub_report22`), second
  order in `μ`, in line with the deviations of 2–15% the source reports at `μ_p ≈ 0.3`–`0.6`.
* (21) at the port, `ρ = S tan δ₀ − jμ_p`, is the first-order term of the exact ratio, with `S`
  the forced response of the dynamic model.

Family and connection conclusions.
None: static evidence on the droop core with a dynamic link (linearization, modulation,
eigentriple, pump coefficient).
-/

noncomputable section
namespace powerlib.GFM
namespace DroopNetwork
open Complex ComplexConjugate Matrix

/-! ## Generic linear algebra of the droop core with a dynamic network -/

/-- Equilibrium data in the coordinates `(δ, p_m, p_f, i, ī)`. -/
structure Coeffs where
  mp : ℂ
  ω1 : ℂ
  ωm : ℂ
  a : ℂ
  ab : ℂ
  e : ℂ
  eb : ℂ
  bi : ℂ
  bm : ℂ
  Pδ : ℂ
  Pi : ℂ
  Pm : ℂ
  Pδδ : ℂ
  Pδi : ℂ
  Pδm : ℂ

namespace Coeffs

variable (q : Coeffs)

/-- Network transfer from the angle to the current, `c(s) = a/(s + e)`. -/
def c (s : ℂ) : ℂ := q.a / (s + q.e)
def ct (s : ℂ) : ℂ := q.ab / (s + q.eb)
/-- Network transfer from the grid angle to the current, `d(s) = b_i/(s + e)`. -/
def d (s : ℂ) : ℂ := q.bi / (s + q.e)
def dt (s : ℂ) : ℂ := q.bm / (s + q.eb)
/-- Power per converter angle, `K(s) = P_δ + P_i c(s) + P_ī c̃(s)`. -/
def K (s : ℂ) : ℂ := q.Pδ + q.Pi * q.c s + q.Pm * q.ct s
/-- Power per grid angle, `K_θ(s) = P_i d(s) + P_ī d̃(s)`. -/
def Kθ (s : ℂ) : ℂ := q.Pi * q.d s + q.Pm * q.dt s
/-- Quadrature transfers `H_q(s) = j(P_i c − P_ī c̃)`, `H_θ(s) = j(P_i d − P_ī d̃)`. -/
def Hq (s : ℂ) : ℂ := I * (q.Pi * q.c s - q.Pm * q.ct s)
def Hθ (s : ℂ) : ℂ := I * (q.Pi * q.d s - q.Pm * q.dt s)
/-- `D(s) = s(s + ω₁)(s + ω_m) + m_p ω₁ ω_m K(s)`. -/
def D (s : ℂ) : ℂ := s * (s + q.ω1) * (s + q.ωm) + q.mp * q.ω1 * q.ωm * q.K s
/-- `D'(s)`. -/
def Dd (s : ℂ) : ℂ :=
  (s + q.ω1) * (s + q.ωm) + s * (s + q.ω1) + s * (s + q.ωm) -
    q.mp * q.ω1 * q.ωm * (q.Pi * q.c s / (s + q.e) + q.Pm * q.ct s / (s + q.eb))

def J : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0, 0, -q.mp, 0, 0;
    q.ωm * q.Pδ, -q.ωm, 0, q.ωm * q.Pi, q.ωm * q.Pm;
    0, q.ω1, -q.ω1, 0, 0;
    q.a, 0, 0, -q.e, 0;
    q.ab, 0, 0, 0, -q.eb]

def B : Fin 5 → ℂ := ![0, 0, 0, q.bi, q.bm]

/-- `A₁ = DJ[z]`: the stiffness entry, the two power entries of the currents and the two Park
rotations of the network rows. -/
def A1 (z : Fin 5 → ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0, 0, 0, 0, 0;
    q.ωm * (q.Pδδ * z 0 + q.Pδi * z 3 + q.Pδm * z 4), 0, 0, q.ωm * q.Pδi * z 0,
      q.ωm * q.Pδm * z 0;
    0, 0, 0, 0, 0;
    I * q.a * z 0, 0, 0, 0, 0;
    -I * q.ab * z 0, 0, 0, 0, 0]

def right (s : ℂ) : Fin 5 → ℂ :=
  ![1, -(s * (s + q.ω1)) / (q.mp * q.ω1), -s / q.mp, q.c s, q.ct s]

def left (s : ℂ) : Fin 5 → ℂ :=
  let upm := -(q.mp * q.ω1) / q.Dd s
  ![upm * (-((s + q.ω1) * (s + q.ωm)) / (q.mp * q.ω1)), upm, upm * ((s + q.ωm) / q.ω1),
    upm * (q.ωm * q.Pi / (s + q.e)), upm * (q.ωm * q.Pm / (s + q.eb))]

def forcedδ (s : ℂ) : ℂ := -(q.mp * q.ω1 * q.ωm * q.Kθ s) / q.D s

def forced (s : ℂ) : Fin 5 → ℂ :=
  ![q.forcedδ s, -(s * (s + q.ω1)) * q.forcedδ s / (q.mp * q.ω1), -s * q.forcedδ s / q.mp,
    q.c s * q.forcedδ s + q.d s, q.ct s * q.forcedδ s + q.dt s]

def pumpc (A : Matrix (Fin 5) (Fin 5) ℂ) (u rbar : Fin 5 → ℂ) : ℂ := u ⬝ᵥ (A *ᵥ rbar)

variable {q}

@[tmio T, powerlib_foundation] theorem right_eig {lam : ℂ} (hmp : q.mp ≠ 0) (hω1 : q.ω1 ≠ 0) (h1 : lam + q.e ≠ 0)
    (h2 : lam + q.eb ≠ 0) (hD : q.D lam = 0) :
    q.J *ᵥ q.right lam = lam • q.right lam := by
  have hD' : lam * (lam + q.ω1) * (lam + q.ωm) + q.mp * q.ω1 * q.ωm *
      (q.Pδ + q.Pi * q.c lam + q.Pm * q.ct lam) = 0 := hD
  have e1 : q.c lam * (lam + q.e) = q.a := by simp only [c]; field_simp
  have e2 : q.ct lam * (lam + q.eb) = q.ab := by simp only [ct]; field_simp
  funext i
  fin_cases i <;> simp [J, right, mulVec, dotProduct, Fin.sum_univ_five]
  · field_simp
  · field_simp
    linear_combination hD'
  · field_simp; ring
  · linear_combination -e1
  · linear_combination -e2

@[tmio T, powerlib_foundation] theorem left_eig {lam : ℂ} (hmp : q.mp ≠ 0) (hω1 : q.ω1 ≠ 0) (h1 : lam + q.e ≠ 0)
    (h2 : lam + q.eb ≠ 0) (hD : q.D lam = 0) :
    vecMul (q.left lam) q.J = lam • q.left lam := by
  have hD' : lam * (lam + q.ω1) * (lam + q.ωm) + q.mp * q.ω1 * q.ωm *
      (q.Pδ + q.Pi * (q.a / (lam + q.e)) + q.Pm * (q.ab / (lam + q.eb))) = 0 := hD
  simp only [left]
  generalize -(q.mp * q.ω1) / q.Dd lam = upm
  generalize hd1 : lam + q.e = d1 at h1 hD'
  generalize hd2 : lam + q.eb = d2 at h2 hD'
  have hD'' : lam * (lam + q.ω1) * (lam + q.ωm) * d1 * d2 + q.mp * q.ω1 * q.ωm *
      (q.Pδ * d1 * d2 + q.Pi * q.a * d2 + q.Pm * q.ab * d1) = 0 := by
    field_simp at hD'; linear_combination hD'
  funext i
  fin_cases i <;> simp [J, vecMul, dotProduct, Fin.sum_univ_five]
  · field_simp
    linear_combination upm * hD''
  · field_simp; ring
  · field_simp; ring
  · field_simp; rw [← hd1]; ring
  · field_simp; rw [← hd2]; ring

@[tmio T, powerlib_foundation] theorem left_right {lam : ℂ} (hmp : q.mp ≠ 0) (hω1 : q.ω1 ≠ 0) (h1 : lam + q.e ≠ 0)
    (h2 : lam + q.eb ≠ 0) (hDd : q.Dd lam ≠ 0) :
    q.left lam ⬝ᵥ q.right lam = 1 := by
  have hdef : q.Dd lam = (lam + q.ω1) * (lam + q.ωm) + lam * (lam + q.ω1) +
      lam * (lam + q.ωm) - q.mp * q.ω1 * q.ωm * (q.Pi * q.c lam / (lam + q.e) +
        q.Pm * q.ct lam / (lam + q.eb)) := rfl
  simp only [left, right, dotProduct, Fin.sum_univ_five, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons]
  generalize q.Dd lam = DD at hDd hdef ⊢
  generalize q.c lam = c1 at hdef ⊢
  generalize q.ct lam = c2 at hdef ⊢
  generalize lam + q.e = d1 at h1 hdef ⊢
  generalize lam + q.eb = d2 at h2 hdef ⊢
  have hDD : DD * (d1 * d2) = ((lam + q.ω1) * (lam + q.ωm) + lam * (lam + q.ω1) +
      lam * (lam + q.ωm)) * d1 * d2 - q.mp * q.ω1 * q.ωm * (q.Pi * c1 * d2 + q.Pm * c2 * d1) := by
    rw [hdef]; field_simp
  field_simp
  linear_combination (-1 : ℂ) * hDD

@[tmio T, powerlib_foundation] theorem forced_eq {s : ℂ} (hmp : q.mp ≠ 0) (hω1 : q.ω1 ≠ 0) (hD : q.D s ≠ 0)
    (h1 : s + q.e ≠ 0) (h2 : s + q.eb ≠ 0) :
    (s • (1 : Matrix (Fin 5) (Fin 5) ℂ) - q.J) *ᵥ q.forced s = q.B := by
  have hDdef : q.D s = s * (s + q.ω1) * (s + q.ωm) + q.mp * q.ω1 * q.ωm * q.K s := rfl
  have hKdef : q.K s = q.Pδ + q.Pi * q.c s + q.Pm * q.ct s := rfl
  have hKθ : q.Kθ s = q.Pi * q.d s + q.Pm * q.dt s := rfl
  have e1 : q.c s * (s + q.e) = q.a := by simp only [c]; field_simp
  have e2 : q.ct s * (s + q.eb) = q.ab := by simp only [ct]; field_simp
  have e3 : q.d s * (s + q.e) = q.bi := by simp only [d]; field_simp
  have e4 : q.dt s * (s + q.eb) = q.bm := by simp only [dt]; field_simp
  funext i
  fin_cases i
  · simp [J, forced, B, mulVec, dotProduct, Fin.sum_univ_five, Matrix.one_apply]
    field_simp
    ring
  · simp [J, forced, B, mulVec, dotProduct, Fin.sum_univ_five, Matrix.one_apply, forcedδ]
    generalize q.D s = DD at hD hDdef ⊢
    rw [hKθ] at *
    field_simp
    rw [hDdef, hKdef]
    ring
  · simp [J, forced, B, mulVec, dotProduct, Fin.sum_univ_five, Matrix.one_apply]
    field_simp; ring
  · simp [J, forced, B, mulVec, dotProduct, Fin.sum_univ_five, Matrix.one_apply]
    linear_combination (q.forcedδ s) * e1 + e3
  · simp [J, forced, B, mulVec, dotProduct, Fin.sum_univ_five, Matrix.one_apply]
    linear_combination (q.forcedδ s) * e2 + e4

/-- The bracket of the angle part of the pump. -/
def G (s1 s2 lam : ℂ) : ℂ :=
  q.Pδδ + q.Pδi * (q.c s1 + q.c s2) + q.Pδm * (q.ct s1 + q.ct s2) +
    I * (q.Pi * q.c lam - q.Pm * q.ct lam)

/-- `g = u_{p_m} ω_m [z_δ G(s₁, s₂, λ) + P_δi d(s₁) + P_δī d̃(s₁)]`, `s₁ = jω`, `s₂ = λ̄`. -/
@[tmio T, powerlib_foundation] theorem pump_eq (s1 s2 lam : ℂ) :
    pumpc (q.A1 (q.forced s1)) (q.left lam) (q.right s2) =
      (-(q.mp * q.ω1) / q.Dd lam) * q.ωm *
        (q.forcedδ s1 * q.G s1 s2 lam + (q.Pδi * q.d s1 + q.Pδm * q.dt s1)) := by
  simp only [pumpc, A1, forced, left, right, G, c, ct, mulVec, dotProduct, Fin.sum_univ_five]
  simp
  ring

/-- Kernel form: with the Park rotations `P_δi = −jP_i`, `P_δī = jP_ī` of the port power,
`g = u_{p_m} ω_m [z_δ (P_δδ + H_q(λ) − H_q(s₁) − H_q(s₂)) − H_θ(s₁)]`. -/
@[tmio T, powerlib_foundation] theorem pump_kernel (hi : q.Pδi = -I * q.Pi) (hm : q.Pδm = I * q.Pm) (s1 s2 lam : ℂ) :
    pumpc (q.A1 (q.forced s1)) (q.left lam) (q.right s2) =
      (-(q.mp * q.ω1) / q.Dd lam) * q.ωm *
        (q.forcedδ s1 * (q.Pδδ + (q.Hq lam - q.Hq s1 - q.Hq s2)) - q.Hθ s1) := by
  rw [pump_eq, G, hi, hm]
  simp only [Hq, Hθ]
  ring

end Coeffs
/-! ## The model of the source -/

/-- Parameters of the droop core with a dynamic series link (the source's check 1, port
measurement). -/
structure Model where
  mp : ℝ
  ω1 : ℝ
  ωm : ℝ
  ωb : ℝ
  E : ℝ
  V : ℝ
  R : ℝ
  X : ℝ

namespace Model

variable (p : Model)

def Z : ℂ := (p.R : ℂ) + (p.X : ℂ) * I
def Zc : ℂ := (p.R : ℂ) - (p.X : ℂ) * I
/-- `ω_b/X`. -/
def an : ℝ := p.ωb / p.X
/-- Converter EMF `E e^{jδ}` (complexified angle) and its conjugate partner. -/
def φ (δ : ℂ) : ℂ := p.E * exp (δ * I)
def φt (δ : ℂ) : ℂ := p.E * exp (-(δ * I))
/-- Current dynamics `(X/ω_b) i̇ = E e^{jδ} − V e^{jθ} − Z i`. -/
def net (θ δ i : ℂ) : ℂ := p.an * (p.φ δ - p.V * exp (θ * I) - p.Z * i)
def nett (θ δ m : ℂ) : ℂ := p.an * (p.φt δ - p.V * exp (-(θ * I)) - p.Zc * m)
/-- Port power `p = (E e^{jδ} ī + E e^{−jδ} i)/2`. -/
def pw (δ i m : ℂ) : ℂ := (p.φ δ * m + p.φt δ * i) / 2

/-- The field in the coordinates `(δ, p_m, p_f, i, ī)`. -/
def field (θ : ℂ) (Pref : ℝ) (x : Fin 5 → ℂ) : Fin 5 → ℂ :=
  ![p.mp * (Pref - x 2), p.ωm * (p.pw (x 0) (x 3) (x 4) - x 1), p.ω1 * (x 1 - x 2),
    p.net θ (x 0) (x 3), p.nett θ (x 0) (x 4)]

@[tmio M, powerlib_domain] theorem conj_φ (δ : ℝ) : conj (p.φ δ) = p.φt δ := by
  simp only [φ, φt, map_mul, conj_ofReal, ← Complex.exp_conj, conj_I]
  congr 2; ring

/-- On the real slice the power is the source's `Re(E e^{jδ} ī)`. -/
@[tmio M, powerlib_domain] theorem pw_real (δ : ℝ) (i : ℂ) : p.pw δ i (conj i) = ((p.φ δ * conj i).re : ℂ) := by
  rw [pw, ← p.conj_φ]
  apply Complex.ext
  all_goals (simp [Complex.mul_re, Complex.mul_im]; try ring)

@[tmio M, powerlib_domain] theorem nett_real (θ δ : ℝ) (i : ℂ) : p.nett θ δ (conj i) = conj (p.net θ δ i) := by
  simp only [nett, net, map_mul, map_sub, conj_ofReal, ← p.conj_φ, ← Complex.exp_conj, conj_I,
    Zc, Z, map_add, an]
  congr 3; simp; ring

/-! ### Partial derivatives -/

def pwδ (δ i m : ℂ) : ℂ := (I * p.φ δ * m - I * p.φt δ * i) / 2
def pwi (δ : ℂ) : ℂ := p.φt δ / 2
def pwm (δ : ℂ) : ℂ := p.φ δ / 2
def pwδδ (δ i m : ℂ) : ℂ := (-p.φ δ * m - p.φt δ * i) / 2

@[tmio M, powerlib_domain] theorem hasDerivAt_φ (δ : ℂ) : HasDerivAt p.φ (I * p.φ δ) δ := by
  have h := (((hasDerivAt_id δ).mul_const I).cexp).const_mul (p.E : ℂ)
  convert h using 1
  · funext x; simp [φ]
  · simp [φ]; ring

@[tmio M, powerlib_domain] theorem hasDerivAt_φt (δ : ℂ) : HasDerivAt p.φt (-I * p.φt δ) δ := by
  have h := (((hasDerivAt_id δ).mul_const I).neg.cexp).const_mul (p.E : ℂ)
  convert h using 1
  · funext x; simp [φt]
  · simp [φt]; ring

@[tmio M, powerlib_domain] theorem hasDerivAt_pw_δ (δ i m : ℂ) : HasDerivAt (fun δ => p.pw δ i m) (p.pwδ δ i m) δ := by
  have h := (((p.hasDerivAt_φ δ).mul_const m).add ((p.hasDerivAt_φt δ).mul_const i)).div_const 2
  convert h using 1
  · funext x; simp [pw]
  · simp only [pwδ]; ring

@[tmio M, powerlib_domain] theorem hasDerivAt_pw_i (δ i m : ℂ) : HasDerivAt (fun i => p.pw δ i m) (p.pwi δ) i := by
  have h := (((hasDerivAt_id i).const_mul (p.φt δ)).const_add (p.φ δ * m)).div_const 2
  convert h using 1
  · funext x; simp [pw]
  · simp [pwi]

@[tmio M, powerlib_domain] theorem hasDerivAt_pw_m (δ i m : ℂ) : HasDerivAt (fun m => p.pw δ i m) (p.pwm δ) m := by
  have h := (((hasDerivAt_id m).const_mul (p.φ δ)).add_const (p.φt δ * i)).div_const 2
  convert h using 1
  · funext x; simp [pw]
  · simp [pwm]

@[tmio M, powerlib_domain] theorem hasDerivAt_net_δ (θ δ i : ℂ) :
    HasDerivAt (fun δ => p.net θ δ i) (p.an * (I * p.φ δ)) δ := by
  have h := (((p.hasDerivAt_φ δ).sub_const (p.V * exp (θ * I))).sub_const (p.Z * i)).const_mul
    (p.an : ℂ)
  convert h using 1
  funext x; simp [net]

@[tmio M, powerlib_domain] theorem hasDerivAt_net_i (θ δ i : ℂ) :
    HasDerivAt (fun i => p.net θ δ i) (-(p.an * p.Z)) i := by
  have h := (((hasDerivAt_id i).const_mul p.Z).const_sub (p.φ δ - p.V * exp (θ * I))).const_mul
    (p.an : ℂ)
  convert h using 1
  · funext x; simp [net]
  · ring

/-- The grid angle enters the current equation additively: `∂(i̇)/∂θ = −(ω_b/X) jV e^{jθ}`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_net_θ (θ δ i : ℂ) :
    HasDerivAt (fun θ => p.net θ δ i) (-(p.an * (p.V * (I * exp (θ * I))))) θ := by
  have h := ((((hasDerivAt_id θ).mul_const I).cexp.const_mul (p.V : ℂ)).const_sub (p.φ δ)).sub_const
    (p.Z * i) |>.const_mul (p.an : ℂ)
  convert h using 1
  · funext x; simp [net]
  · simp only [id]; ring

/-! ### The modulation as the directional derivative of the Jacobian -/

@[tmio M, powerlib_domain] theorem line_pwδ (δ i m zδ zi zm : ℂ) :
    HasDerivAt (fun t => p.pwδ (δ + t * zδ) (i + t * zi) (m + t * zm))
      (p.pwδδ δ i m * zδ + (-I * p.pwi δ) * zi + (I * p.pwm δ) * zm) 0 := by
  have hL : HasDerivAt (fun t : ℂ => δ + t * zδ) zδ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const zδ).const_add δ
  have hi : HasDerivAt (fun t : ℂ => i + t * zi) zi 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const zi).const_add i
  have hm : HasDerivAt (fun t : ℂ => m + t * zm) zm 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const zm).const_add m
  have hφ := (p.hasDerivAt_φ (δ + 0 * zδ)).comp (0 : ℂ) hL
  have hφt := (p.hasDerivAt_φt (δ + 0 * zδ)).comp (0 : ℂ) hL
  simp only [zero_mul, add_zero] at hφ hφt
  have h := ((((hφ.const_mul I).mul hm).sub ((hφt.const_mul I).mul hi))).div_const 2
  convert h using 1
  · funext t; simp [pwδ]
  · simp only [pwδδ, pwi, pwm, Function.comp_def]; ring_nf; rw [I_sq]; ring

@[tmio M, powerlib_domain] theorem line_pwi (δ zδ : ℂ) :
    HasDerivAt (fun t => p.pwi (δ + t * zδ)) (-I * p.pwi δ * zδ) 0 := by
  have hL : HasDerivAt (fun t : ℂ => δ + t * zδ) zδ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const zδ).const_add δ
  have h := ((p.hasDerivAt_φt (δ + 0 * zδ)).comp (0 : ℂ) hL).div_const 2
  simp only [zero_mul, add_zero] at h
  convert h using 1
  · funext t; simp [pwi]
  · simp only [pwi]; ring

@[tmio M, powerlib_domain] theorem line_pwm (δ zδ : ℂ) :
    HasDerivAt (fun t => p.pwm (δ + t * zδ)) (I * p.pwm δ * zδ) 0 := by
  have hL : HasDerivAt (fun t : ℂ => δ + t * zδ) zδ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const zδ).const_add δ
  have h := ((p.hasDerivAt_φ (δ + 0 * zδ)).comp (0 : ℂ) hL).div_const 2
  simp only [zero_mul, add_zero] at h
  convert h using 1
  · funext t; simp [pwm]
  · simp only [pwm]; ring

/-- `(A₁)_{i δ} = j (∂i̇/∂δ) z_δ`: the network row is a pure Park rotation. -/
@[tmio M, powerlib_domain] theorem line_netδ (δ zδ : ℂ) :
    HasDerivAt (fun t => (p.an : ℂ) * (I * p.φ (δ + t * zδ)))
      (I * ((p.an : ℂ) * (I * p.φ δ)) * zδ) 0 := by
  have hL : HasDerivAt (fun t : ℂ => δ + t * zδ) zδ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const zδ).const_add δ
  have h := (((p.hasDerivAt_φ (δ + 0 * zδ)).comp (0 : ℂ) hL).const_mul I).const_mul (p.an : ℂ)
  simp only [zero_mul, add_zero] at h
  convert h using 1
  simp; ring

/-! ### Equilibrium and coefficients -/

def i0 (δ0 : ℂ) : ℂ := (p.φ δ0 - p.V) / p.Z
def m0 (δ0 : ℂ) : ℂ := (p.φt δ0 - p.V) / p.Zc

/-- The coefficients of the linearized model at `δ₀` (grid angle `θ = 0`). -/
def coeffs (δ0 : ℂ) : Coeffs where
  mp := p.mp
  ω1 := p.ω1
  ωm := p.ωm
  a := p.an * (I * p.φ δ0)
  ab := p.an * (-I * p.φt δ0)
  e := p.an * p.Z
  eb := p.an * p.Zc
  bi := -(p.an * (p.V * I))
  bm := p.an * (p.V * I)
  Pδ := p.pwδ δ0 (p.i0 δ0) (p.m0 δ0)
  Pi := p.pwi δ0
  Pm := p.pwm δ0
  Pδδ := p.pwδδ δ0 (p.i0 δ0) (p.m0 δ0)
  Pδi := -I * p.pwi δ0
  Pδm := I * p.pwm δ0

/-- The pump coefficient of the droop core with a dynamic network has the kernel form for every
network impedance (port measurement). -/
@[tmio M, powerlib_domain] theorem pump_kernel (δ0 s1 s2 lam : ℂ) :
    Coeffs.pumpc ((p.coeffs δ0).A1 ((p.coeffs δ0).forced s1)) ((p.coeffs δ0).left lam)
        ((p.coeffs δ0).right s2) =
      (-(p.mp * p.ω1) / (p.coeffs δ0).Dd lam) * p.ωm *
        ((p.coeffs δ0).forcedδ s1 * ((p.coeffs δ0).Pδδ + ((p.coeffs δ0).Hq lam -
          (p.coeffs δ0).Hq s1 - (p.coeffs δ0).Hq s2)) - (p.coeffs δ0).Hθ s1) :=
  Coeffs.pump_kernel rfl rfl s1 s2 lam


/-! ### Lossless link: the full-order sideband ratio -/

@[tmio M, powerlib_domain] theorem φ_mul_φt (δ : ℂ) : p.φ δ * p.φt δ = (p.E : ℂ) ^ 2 := by
  simp only [φ, φt]
  rw [show (p.E : ℂ) * exp (δ * I) * (p.E * exp (-(δ * I))) =
    (p.E : ℂ) ^ 2 * (exp (δ * I) * exp (-(δ * I))) by ring, ← Complex.exp_add]
  simp

/-- Lossless link: `H_q(s) = −(E²/X) ω_b s/(s² + ω_b²)`, independent of the load. -/
@[tmio M, powerlib_domain] theorem Hq_lossless (δ0 s : ℂ) (hR : p.R = 0) (hX : p.X ≠ 0)
    (h1 : s + p.ωb * I ≠ 0) (h2 : s - p.ωb * I ≠ 0) :
    (p.coeffs δ0).Hq s = -((p.E : ℂ) ^ 2 / p.X * p.ωb * s / (s ^ 2 + (p.ωb : ℂ) ^ 2)) := by
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  have he : (p.an : ℂ) * p.Z = p.ωb * I := by
    simp only [an, Z, hR]; push_cast; field_simp; ring
  have heb : (p.an : ℂ) * p.Zc = -(p.ωb * I) := by
    simp only [an, Zc, hR]; push_cast; field_simp; ring
  have hV := p.φ_mul_φt δ0
  have hs : s ^ 2 + (p.ωb : ℂ) ^ 2 = (s + p.ωb * I) * (s - p.ωb * I) := by
    ring_nf; rw [I_sq]; ring
  simp only [Coeffs.Hq, Coeffs.c, Coeffs.ct, coeffs, pwi, pwm, he, heb]
  rw [show s + -((p.ωb : ℂ) * I) = s - p.ωb * I by ring, hs]
  have key : ∀ (an A B : ℂ), I * (B / 2 * (an * (I * A) / (s + p.ωb * I)) -
      A / 2 * (an * (-I * B) / (s - p.ωb * I))) =
        -(an * (A * B) * s / ((s + p.ωb * I) * (s - p.ωb * I))) := by
    intro an A B
    have hsum : (s + p.ωb * I) + (s - p.ωb * I) = 2 * s := by ring
    generalize s + p.ωb * I = u1 at h1 hsum ⊢
    generalize s - p.ωb * I = u2 at h2 hsum ⊢
    calc I * (B / 2 * (an * (I * A) / u1) - A / 2 * (an * (-I * B) / u2))
        = (I * I) * (an * (A * B)) * (u1 + u2) / (2 * (u1 * u2)) := by field_simp; ring
      _ = -(an * (A * B) * s / (u1 * u2)) := by rw [I_mul_I, hsum]; field_simp
  rw [key, p.φ_mul_φt]
  simp only [an]
  push_cast
  field_simp

/-- Lossless link, `s = jω`: the grid-angle part of the pump is
`−H_θ(jω) = (EV/X) ω_b (ω_b sin δ₀ − jω cos δ₀)/(ω_b² − ω²)
= (EV/X)(sin δ₀ − jμ cos δ₀)/(1 − μ²)`, `μ = ω/ω_b`: the two sideband reactances `X(1 ± μ)`. -/
@[tmio M, powerlib_domain] theorem Hθ_lossless (δ0 ω : ℝ) (hR : p.R = 0) (hX : p.X ≠ 0) (hωb : p.ωb ≠ 0)
    (hμ : ω ^ 2 ≠ p.ωb ^ 2) :
    -(p.coeffs δ0).Hθ ((ω : ℂ) * I) = ((p.E * p.V / p.X : ℝ) : ℂ) *
      (p.ωb * (p.ωb * (Real.sin δ0 : ℂ) - I * ω * Real.cos δ0) / ((p.ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2)) := by
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hωc : (p.ωb : ℂ) ≠ 0 := by exact_mod_cast hωb
  have he : (p.an : ℂ) * p.Z = p.ωb * I := by
    simp only [an, Z, hR]; push_cast; field_simp; ring
  have heb : (p.an : ℂ) * p.Zc = -(p.ωb * I) := by
    simp only [an, Zc, hR]; push_cast; field_simp; ring
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
  have hφ : p.φ δ0 = p.E * ((Real.cos δ0 : ℂ) + Real.sin δ0 * I) := by
    simp only [φ]; rw [Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have hφt : p.φt δ0 = p.E * ((Real.cos δ0 : ℂ) - Real.sin δ0 * I) := by
    simp only [φt]; rw [PSCActiveDamping.exp_neg_mul_I]
  simp only [Coeffs.Hθ, Coeffs.d, Coeffs.dt, coeffs, pwi, pwm, he, heb, hφ, hφt]
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
  linear_combination (I * p.E * p.V * c) * hsum - (p.E * p.V * sn) * hdiff

/-- Lossless link: the curvature of the port power is `P_δδ = −p₀ = −EV sin δ₀/X`. -/
@[tmio M, powerlib_domain] theorem Pδδ_lossless (δ0 : ℝ) (hR : p.R = 0) (hX : p.X ≠ 0) :
    (p.coeffs δ0).Pδδ = ((-(p.E * p.V * Real.sin δ0 / p.X)) : ℝ) := by
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hφ : p.φ δ0 = p.E * ((Real.cos δ0 : ℂ) + Real.sin δ0 * I) := by
    simp only [φ]; rw [Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have hφt : p.φt δ0 = p.E * ((Real.cos δ0 : ℂ) - Real.sin δ0 * I) := by
    simp only [φt]; rw [PSCActiveDamping.exp_neg_mul_I]
  have hsc := Real.cos_sq_add_sin_sq δ0
  simp only [coeffs, pwδδ, i0, m0, Z, Zc, hR, hφ, hφt]
  generalize Real.cos δ0 = c at *
  generalize Real.sin δ0 = sn at *
  have hsc' : (c : ℂ) ^ 2 + (sn : ℂ) ^ 2 = 1 := by exact_mod_cast hsc
  push_cast
  field_simp
  ring_nf

/-- The exact pump coefficient of the droop core with a dynamic lossless link (port measurement),
at the drive `s₁ = jω` and any `s₂`, `λ`:
`g = u_{p_m} ω_m [(EV/X) ω_b(ω_b sin δ₀ − jω cos δ₀)/(ω_b² − ω²)
− z_δ ((EV/X) sin δ₀ − (H_q(λ) − H_q(jω) − H_q(s₂)))]`. -/
@[tmio M, powerlib_domain] theorem pump_lossless (δ0 ω : ℝ) (s2 lam : ℂ) (hR : p.R = 0) (hX : p.X ≠ 0) (hωb : p.ωb ≠ 0)
    (hμ : ω ^ 2 ≠ p.ωb ^ 2) :
    Coeffs.pumpc ((p.coeffs δ0).A1 ((p.coeffs δ0).forced ((ω : ℂ) * I)))
        ((p.coeffs δ0).left lam) ((p.coeffs δ0).right s2) =
      (-(p.mp * p.ω1) / (p.coeffs δ0).Dd lam) * p.ωm *
        (((p.E * p.V / p.X : ℝ) : ℂ) * (p.ωb * (p.ωb * (Real.sin δ0 : ℂ) - I * ω * Real.cos δ0) /
            ((p.ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2)) -
          (p.coeffs δ0).forcedδ ((ω : ℂ) * I) * (((p.E * p.V * Real.sin δ0 / p.X : ℝ) : ℂ) -
            ((p.coeffs δ0).Hq lam - (p.coeffs δ0).Hq ((ω : ℂ) * I) - (p.coeffs δ0).Hq s2))) := by
  rw [p.pump_kernel, p.Pδδ_lossless δ0 hR hX, ← p.Hθ_lossless δ0 ω hR hX hωb hμ]
  push_cast
  ring

/-- Exact full-order ratio against (22): with `Q = −(H_q(λ) − H_q(jω) − H_q(λ̄))` and the
source's `K (tan δ₀ S − jμ)/(1 − μ²)` (`S = 1 − z_δ`, in the form
`(EV/X) ω_b (ω_b sin δ₀ (1 − z_δ) − jω cos δ₀)/(ω_b² − ω²)`), the exact bracket exceeds the
source's by `z_δ ((EV/X) sin δ₀ ω²/(ω_b² − ω²) − Q)`: the factor `1/(1 − μ²)` of (22) belongs to
the `1` of `S` only, and `Q` is the kernel of the network. -/
@[tmio T, powerlib_foundation] theorem exact_sub_report22 (E V X ωb ω sd cd : ℝ) (zδ Q : ℂ)
    (hμ : (ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2 ≠ 0) :
    (((E * V / X : ℝ) : ℂ) * (ωb * (ωb * (sd : ℂ) - I * ω * cd) / ((ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2)) -
        zδ * (((E * V * sd / X : ℝ) : ℂ) + Q)) -
      ((E * V / X : ℝ) : ℂ) * (ωb * (ωb * (sd : ℂ) * (1 - zδ) - I * ω * cd) /
        ((ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2)) =
      zδ * (((E * V * sd / X : ℝ) : ℂ) * ((ω : ℂ) ^ 2 / ((ωb : ℂ) ^ 2 - (ω : ℂ) ^ 2)) - Q) := by
  push_cast
  field_simp
  ring

/-- (22) is not exact: at no load (`δ₀ = 0`), at a Hopf mode `λ = jΩ` driven at `ω = 2Ω`
(`0 < 2Ω < ω_b`), the network kernel is
`H_q(λ) − H_q(jω) − H_q(λ̄) = 6j (E²/X) ω_b Ω³/((ω_b² − Ω²)(ω_b² − 4Ω²)) ≠ 0`, so the exact
ratio differs from (22) by `z_δ` times this kernel. -/
@[tmio M, powerlib_domain] theorem kernel_hopf (hR : p.R = 0) (hX : p.X ≠ 0) (hE : p.E ≠ 0) {Ω : ℝ} (hΩ : 0 < Ω)
    (hΩb : 2 * Ω < p.ωb) :
    (p.coeffs 0).Hq ((Ω : ℂ) * I) - (p.coeffs 0).Hq ((2 * Ω : ℝ) * I) -
        (p.coeffs 0).Hq (conj ((Ω : ℂ) * I)) =
      6 * I * ((p.E : ℂ) ^ 2 / p.X * p.ωb * (Ω : ℂ) ^ 3) /
        (((p.ωb : ℂ) ^ 2 - (Ω : ℂ) ^ 2) * ((p.ωb : ℂ) ^ 2 - 4 * (Ω : ℂ) ^ 2)) ∧
      6 * I * ((p.E : ℂ) ^ 2 / p.X * p.ωb * (Ω : ℂ) ^ 3) /
        (((p.ωb : ℂ) ^ 2 - (Ω : ℂ) ^ 2) * ((p.ωb : ℂ) ^ 2 - 4 * (Ω : ℂ) ^ 2)) ≠ 0 := by
  have hωb : 0 < p.ωb := by linarith
  have hne : ∀ x : ℝ, 0 ≤ x → x < p.ωb → ((x : ℂ) * I + p.ωb * I ≠ 0 ∧ (x : ℂ) * I - p.ωb * I ≠ 0 ∧
      -((x : ℂ) * I) + p.ωb * I ≠ 0 ∧ -((x : ℂ) * I) - p.ωb * I ≠ 0) := by
    intro x hx hxb
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> have := congrArg Complex.im h <;> simp at this <;>
      linarith
  have hc : conj ((Ω : ℂ) * I) = -((Ω : ℂ) * I) := by simp [map_mul, conj_ofReal, conj_I]
  obtain ⟨a1, a2, -, -⟩ := hne Ω hΩ.le (by linarith)
  obtain ⟨b1, b2, -, -⟩ := hne (2 * Ω) (by linarith) hΩb
  obtain ⟨-, -, c1, c2⟩ := hne Ω hΩ.le (by linarith)
  rw [hc, p.Hq_lossless 0 _ hR hX a1 a2, p.Hq_lossless 0 _ hR hX b1 b2,
    p.Hq_lossless 0 _ hR hX (by simpa [add_comm, neg_add_eq_sub] using c1)
      (by simpa [sub_eq_add_neg, add_comm] using c2)]
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hEc : (p.E : ℂ) ≠ 0 := by exact_mod_cast hE
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ.ne'
  have hωc : (p.ωb : ℂ) ≠ 0 := by exact_mod_cast hωb.ne'
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
  refine ⟨?_, ?_⟩
  · push_cast
    field_simp
    ring
  · exact div_ne_zero (by simp [hEc, hXc, hωc, hΩc]) (mul_ne_zero d1 d2)

/-- (22) is not exact: at no load, at a Hopf mode `λ = jΩ` driven at `ω = 2Ω < ω_b`, for every
nonzero forced response `z_δ`, the exact bracket of the pump differs from the source's (22). -/
@[tmio M, powerlib_domain] theorem report22_ne (hR : p.R = 0) (hX : p.X ≠ 0) (hE : p.E ≠ 0) {Ω : ℝ} (hΩ : 0 < Ω)
    (hΩb : 2 * Ω < p.ωb) (zδ : ℂ) (hz : zδ ≠ 0) :
    let Q := -((p.coeffs 0).Hq ((Ω : ℂ) * I) - (p.coeffs 0).Hq ((2 * Ω : ℝ) * I) -
      (p.coeffs 0).Hq (conj ((Ω : ℂ) * I)))
    (((p.E * p.V / p.X : ℝ) : ℂ) * (p.ωb * (p.ωb * (Real.sin 0 : ℂ) - I * (2 * Ω : ℝ) *
        Real.cos 0) / ((p.ωb : ℂ) ^ 2 - ((2 * Ω : ℝ) : ℂ) ^ 2)) -
        zδ * (((p.E * p.V * Real.sin 0 / p.X : ℝ) : ℂ) + Q)) ≠
      ((p.E * p.V / p.X : ℝ) : ℂ) * (p.ωb * (p.ωb * (Real.sin 0 : ℂ) * (1 - zδ) -
        I * (2 * Ω : ℝ) * Real.cos 0) / ((p.ωb : ℂ) ^ 2 - ((2 * Ω : ℝ) : ℂ) ^ 2)) := by
  intro Q
  have hωb : 0 < p.ωb := by linarith
  have hμ : (p.ωb : ℂ) ^ 2 - ((2 * Ω : ℝ) : ℂ) ^ 2 ≠ 0 := by
    have : p.ωb ^ 2 - (2 * Ω) ^ 2 ≠ 0 := by nlinarith
    exact_mod_cast this
  intro h
  have hd := exact_sub_report22 p.E p.V p.X p.ωb (2 * Ω) (Real.sin 0) (Real.cos 0) zδ Q hμ
  rw [h, sub_self] at hd
  simp only [Real.sin_zero, mul_zero, zero_div, ofReal_zero, zero_mul, zero_sub] at hd
  have hk := (p.kernel_hopf hR hX hE hΩ hΩb).2
  rw [← (p.kernel_hopf hR hX hE hΩ hΩb).1] at hk
  apply mul_ne_zero hz (neg_ne_zero.mpr (neg_ne_zero.mpr hk))
  simp only [Q] at hd ⊢
  linear_combination -hd

/-- The lag of §4.4 is the first Taylor coefficient of the exact network transfer: for every
link `Z = R + jX` (port measurement), `K'(0) = −2E²RX²/(ω_b |Z|⁴) = −K_d`, the lag coefficient of
`NetworkLag.lagCoeff`; hence `p ≈ K δ − K_d δ̇` is the first-order part of `K(s)`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_K_zero (δ0 : ℝ) (hX : p.X ≠ 0) (hωb : p.ωb ≠ 0) :
    HasDerivAt (p.coeffs δ0).K (-((NetworkLag.lagCoeff p.E p.R p.X p.ωb : ℝ) : ℂ)) 0 := by
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hωc : (p.ωb : ℂ) ≠ 0 := by exact_mod_cast hωb
  have hZ : p.Z ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp [Z] at this; exact hX this
  have hZc : p.Zc ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp [Zc] at this; exact hX this
  have ha : (p.an : ℂ) ≠ 0 := by simp only [an]; push_cast; exact div_ne_zero hωc hXc
  have he : (p.an : ℂ) * p.Z ≠ 0 := mul_ne_zero ha hZ
  have heb : (p.an : ℂ) * p.Zc ≠ 0 := mul_ne_zero ha hZc
  have hc : ∀ (A ee : ℂ), ee ≠ 0 → HasDerivAt (fun s : ℂ => A / (s + ee)) (-(A / ee ^ 2)) 0 := by
    intro A ee hee
    have h := ((hasDerivAt_id (0 : ℂ)).add_const ee).inv (by simpa using hee) |>.const_mul A
    convert h using 1
    · funext s; simp [div_eq_mul_inv]
    · simp; ring
  have h1 := (hc ((p.coeffs δ0).a) (p.an * p.Z) he).const_mul ((p.coeffs δ0).Pi)
  have h2 := (hc ((p.coeffs δ0).ab) (p.an * p.Zc) heb).const_mul ((p.coeffs δ0).Pm)
  have h := (h1.add h2).const_add ((p.coeffs δ0).Pδ)
  have hV := p.φ_mul_φt δ0
  convert h using 1
  · funext s; simp only [Coeffs.K, Coeffs.c, Coeffs.ct, coeffs, Pi.add_apply]; ring
  · simp only [coeffs, pwi, pwm, NetworkLag.lagCoeff, an, Z, Zc]
    generalize p.φ δ0 = A at hV
    generalize p.φt δ0 = B at hV
    push_cast
    rw [show (p.E : ℂ) ^ 2 = A * B from hV.symm]
    have hN : ((p.R : ℂ) ^ 2 + (p.X : ℂ) ^ 2) ≠ 0 := by
      have : (0 : ℝ) < p.R ^ 2 + p.X ^ 2 := by positivity
      exact_mod_cast this.ne'
    have hZ' : (p.R : ℂ) + p.X * I ≠ 0 := hZ
    have hZc' : (p.R : ℂ) - p.X * I ≠ 0 := hZc
    rw [show (p.R : ℂ) ^ 2 + (p.X : ℂ) ^ 2 = ((p.R : ℂ) + p.X * I) * ((p.R : ℂ) - p.X * I) by
      ring_nf; rw [I_sq]; ring]
    field_simp
    ring_nf
    rw [I_sq]
    ring

end Model

end DroopNetwork
end powerlib.GFM
