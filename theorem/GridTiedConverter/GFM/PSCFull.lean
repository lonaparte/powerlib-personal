import theorem.GridTiedConverter.GFM.PSCActiveDamping

/-! # PSC with active damping, the source's check model: exact closure of (13), Table 6 and (24)

The four-state power-synchronization core with the high-pass active resistance of the source's
check model (`verification/check_psc.py`): states `(δ, p_f, ℓ_d, ℓ_q)`, PCC power. Everything is
exact: the linearization and the modulation `A₁` (as derivatives of the model functions), the
characteristic polynomial `D_PSC(s)(s + α_d(1 − b))(s + α_d(1 − b̄))`, the eigentriple, the forced
response to the grid angle, the pump coefficient `g = u A₁ r̄`, and its reduction to the
second-order kernel `H(s₁ + s₂) − H(s₁) − H(s₂)` of the source.

Model boundary.
* Converter frame, quasi-static network: `i = (E + r_a ℓ − V e^{−jδ})/Z`, `Z = R + r_a + jX`,
  `R = R_f + R_g`, `X = X_f + X_g` (`cur`); PCC voltage `u = V e^{−jδ} + Z_g i`, `Z_g = R_g + jX_g`
  (`volt`); power `p = Re(u ī)` (`pw`, `pw_real`); `δ̇ = k(p* − p_f) − θ̇_g`,
  `ṗ_f = ω_f(p − p_f)`, `ℓ̇ = α_d(i − ℓ)` (`field`). `E`, `V` real constants; no AVR, inner loops,
  limits, PLL, delay, PWM or network dynamics. The grid angle enters only as `−θ̇_g`, driven as
  `θ_g = Re e^{jωt}`.
* The analysis is carried out in the coordinates `(δ, p_f, ℓ, ℓ̄)` with the complexified functions
  (independent `ℓ`, `ℓ̄`, complex `δ`), which coincide with the model on the real slice
  (`curt_real`, `pw_real`). The Jacobian entries are the partial derivatives
  (`hasDerivAt_cur_δ`, `hasDerivAt_pw_δ`, …) and the entries of `A₁` the directional derivatives
  of the Jacobian along the forced response (`line_pwδ`, `line_pwℓ`, `line_pwm`, `line_curδ0`,
  `line_curtδ0`). The real-coordinate pump of the source equals the pump in these coordinates with
  the conjugation `swapConj` (`pump_realify`, `swapConj_right`), for Jacobians related by
  `realify`; that relation of the two Jacobians is the definition of the coordinates here; it is
  derived from the real field in `PSCOrbit` (`matX_rfield_eq`).

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §3 (PSC core, `D_PSC`, `K(s) = K_hf + K_ℓ(s)`,
`K_ℓ(0) = ΔK ≈ V₀² sin²α/X`), §4.2 ((13)), Table 4 (PSC weights), Table 5 (PSC: `(p_f, δ)`,
`(ℓ, δ)` column and `(p_f, ℓ)` row), Table 6 (PSC `S_m`), Table 8 (PSC: `ρ = −tan(δ' + α) z_δ`,
rotation `−j z_δ`), §5.5 (Park rotation, `Φ(x, α) = H(jx) − H(−jx) − H(j2x)`, the kernel
`2H₂(s₁, s₂) = H(s₁ + s₂) − H(s₁) − H(s₂)` at `(jω_p, λ_m*)`, (24)), §8 (PSC closed form,
`|E'|`), and `verification/check_psc.py`.

Results (generic core, `Coeffs`).
* `right_eig`, `left_eig`, `left_right` (`u_{p_f} = −k/D'(λ)`), `forced_eq`
  (`z_δ = −s(s + ω_f)/D(s)`), `charPoly` (`det(sI − J) = D(s)(s + α_d(1 − b))(s + α_d(1 − b̄))`).
* `pump_eq` — `g = u_{p_f} ω_f z_δ G(jω, λ̄, λ)` with the bracket `G` (`G`); `G_eq` — exact
  decomposition `G = P_δδ + H_q(λ) − H_q(s₁) − H_q(s₂) + R`, the remainder `R` vanishing when
  `P_δℓ = jP_ℓ`, `P_δℓ̄ = −jP_ℓ̄`, `P_ℓℓ̄ = 0` (`G_kernel`); `tuning` — `jω + λ̄ = λ` at `ω = 2 Im λ`.
* `upf_eq`, `weight_pfδ`, `weight_branch` — Table 4: `w_{p_f δ} = (jΩ/2) c_D K_hf/K_r`,
  `w_{p_f ℓ} + w_{p_f ℓ̄} = (jΩ/2) c_D K_ℓ(λ)/K_r` with `c_D = 2jΩ/D'(λ)`, `K_r = Ω²/(k ω_f)`.
* `sensitivity_eq` — Table 6: `S_m = (4 − 4jζ₀)/(4 − 4jζ₀ − K(2jΩ)/K_r)` exactly.
* `normalizedPump_eq` — `ĝ = 2|g|/Ω = |c_D| |z_δ| |G|/|K_r|` exactly.

Results (the model, `Model`).
* `pw_eq` (the grid reactance does not enter `p`), `cur_ell0` (the operating point does not depend
  on `r_a`), `coeffs`, `rotation_of_Rg` and `G_kernel_of_Rg` — with `R_g = 0` the `(p_f, ℓ)` row
  is a pure Park rotation and the pump bracket is exactly the kernel, `G_tuned` — at 2:1 tuning
  `G = P_δδ + H_q(s₁ + s₂) − H_q(s₁) − H_q(s₂)`, `(s₁, s₂) = (jω, λ̄)`.
* `Hq_eq`, `Kl_eq` — with `R_g = 0` both branch transfers are independent of the load;
  `branch_lossless` — their real rational forms for `R = 0`.
* `Hq_alpha` — `H_q(α_d S) = ΔK H(S)` with the source's `H` (`Hrep`, `Hrep_eq`) and
  `ΔK = V² sin²α/X`; `Kl_alpha` — `K_ℓ(α_d S) = ΔK cos²α (2S + 1)/(S² + 2cos²αS + cos²α)`;
  `Kl_zero` — `K_ℓ(0) = ΔK`; `neg_im_K` — `−Im K(jΩ) = ΔK F_i(Ω/α_d, α)`: all exact for every load
  angle (`R = 0`).
* `curvature_identity`, `curvature_polar` — `P_δδ + jP_δ = −V e^{jδ₀} E'/Z`, hence
  `P_δ = K_hf = (V|E'|/|Z|) cos(δ' + α)`, `P_δδ = −(V|E'|/|Z|) sin(δ' + α)`,
  `E' = E + r_a i₀ = |E'| e^{jβ}`, `δ' = δ₀ + β` (Table 8: `ρ = −tan(δ' + α)`); `curvature_lossless`,
  `emf_lossless` — the closed forms in `δ₀` for `R = 0`.
* `G_lossless` — (24) exactly: `G = −V E sin δ₀/X − V² r_a/(r_a² + X²) +
  ΔK [H(λ/α_d) − H(jω/α_d) − H(λ̄/α_d)]`.
* `damping_eq` — (13) exactly: `σ/Ω = ω_f/(2Ω) + (k ω_f/Ω²) Im K(λ)/2`.
* `reportDt_eq`, `curvature_vs_reportDt`, `curvature_gt_reportDt` — the source's
  `D_t = (sin(δ₀ + 2α) + sin δ₀)/(2cos δ₀)` against the exact curvature term.

Corrections.
* (13): with `K_r := Ω_m²/(k ω_f)` the only approximation is `K(λ) ≈ K(jΩ)`; `ΔK = V₀² sin²α/X`
  and `−Im K(jΩ) = ΔK F_i` are exact at every load angle for `R = 0` (the source writes `≈`).
* Table 6: the PSC `S_m` is exact with `K_r := Ω_m²/(k ω_f)`.
* (24): the source's `Φ = H(jx) − H(−jx) − H(j2x)` is the exact kernel evaluated at `λ ≈ jΩ`
  (`σ → 0`); the exact pump is `ĝ = |c_D||z_δ| |P_δδ + ΔK Φ_λ|/K_r` with
  `Φ_λ = H(λ/α_d) − H(λ̄/α_d) − H(2jΩ/α_d)`. Besides `σ → 0`, the source's form uses `|c_D| = 1`,
  the normalization `K_dc` instead of `K_r`, and `|a + b| ≈ √(a² + b²)` (arg `Φ ≈ 90°`).
* `D_t`: the exact curvature term is `(V|E'|/|Z|) sin(δ' + α)`; the source's `D_t` replaces `E'` by
  `E`, and at load it is strictly smaller than the exact term (`curvature_gt_reportDt`). §8 keeps
  `|E'| ≈ E` because the errors cancel numerically; the exact closed form is `G_lossless`.
* With `R_g ≠ 0` the kernel form is not exact: the remainder of `G_eq` is proportional to `R_g`
  (the `O(κ)`, `κ = 2R_g/|Z|`, correction of Table 7).

Family and connection conclusions.
None: static evidence on the active-damping PSC (linearization, modulation, eigentriple, pump
coefficient and its closed forms).
-/

noncomputable section
namespace powerlib.GFM
namespace PSCFull
open Complex ComplexConjugate Matrix

/-! ## Generic linear algebra of the four-state core -/

/-- The pump coefficient in the coordinates `(δ, p_f, ℓ, ℓ̄)`: `g = u ⬝ (A₁ r̄)`, the conjugate
mode vector given as `rbar`. -/
def pumpc (A : Matrix (Fin 4) (Fin 4) ℂ) (u rbar : Fin 4 → ℂ) : ℂ := u ⬝ᵥ (A *ᵥ rbar)

/-- Conjugation of a vector of the real state space in the coordinates `(δ, p_f, ℓ, ℓ̄)`. -/
def swapConj (v : Fin 4 → ℂ) : Fin 4 → ℂ := ![conj (v 0), conj (v 1), conj (v 3), conj (v 2)]

/-- The coordinates `(δ, p_f, ℓ_d + jℓ_q, ℓ_d − jℓ_q)` of a vector `(δ, p_f, ℓ_d, ℓ_q)`. -/
def realify : Matrix (Fin 4) (Fin 4) ℂ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, I; 0, 0, 1, -I]

def realifyInv : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1 / 2, 1 / 2; 0, 0, -I / 2, I / 2]

@[tmio T, powerlib_foundation] theorem realifyInv_mul : realifyInv * realify = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realify, realifyInv, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals (ring_nf; try simp [I_sq])

@[tmio T, powerlib_foundation] theorem realify_star (v : Fin 4 → ℂ) : realify *ᵥ star v = swapConj (realify *ᵥ v) := by
  funext i
  fin_cases i <;> simp [realify, swapConj, mulVec, dotProduct, Fin.sum_univ_four]

/-- The pump coefficient of the source, `g = l_mᴴ A₁ r_m*` in the real coordinates
`(δ, p_f, ℓ_d, ℓ_q)`, equals the pump in the coordinates `(δ, p_f, ℓ, ℓ̄)` with the conjugate mode
vector `swapConj`. -/
@[tmio T, powerlib_foundation] theorem pump_realify (A : Matrix (Fin 4) (Fin 4) ℂ) (u r : Fin 4 → ℂ) :
    ParametricResonance.Element.pump A u r =
      pumpc (realify * A * realifyInv) (vecMul u realifyInv) (swapConj (realify *ᵥ r)) := by
  rw [pumpc, ← realify_star, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
    realifyInv_mul, Matrix.mul_one, ← Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, realifyInv_mul, Matrix.one_mulVec]
  rfl



/-- The equilibrium data of the linearized PSC core in the coordinates `(δ, p_f, ℓ, ℓ̄)`. -/
structure Coeffs where
  k : ℂ
  ωf : ℂ
  αd : ℂ
  a : ℂ
  ab : ℂ
  b : ℂ
  bb : ℂ
  Pδ : ℂ
  Pℓ : ℂ
  Pm : ℂ
  Pδδ : ℂ
  Pδℓ : ℂ
  Pδm : ℂ
  Pℓm : ℂ

namespace Coeffs

variable (q : Coeffs)

/-- `ℓ` transfer `c(s) = α_d a/(s + α_d(1 − b))`. -/
def c (s : ℂ) : ℂ := q.αd * q.a / (s + q.αd * (1 - q.b))

/-- `ℓ̄` transfer. -/
def ct (s : ℂ) : ℂ := q.αd * q.ab / (s + q.αd * (1 - q.bb))

/-- Synchronizing transfer `K(s) = P_δ + P_ℓ c(s) + P_ℓ̄ c̃(s)`. -/
def K (s : ℂ) : ℂ := q.Pδ + q.Pℓ * q.c s + q.Pm * q.ct s

/-- Branch part `K_ℓ(s) = P_ℓ c(s) + P_ℓ̄ c̃(s)`. -/
def Kl (s : ℂ) : ℂ := q.Pℓ * q.c s + q.Pm * q.ct s

/-- Quadrature branch transfer `H_q(s) = −j(P_ℓ c(s) − P_ℓ̄ c̃(s))`. -/
def Hq (s : ℂ) : ℂ := -I * (q.Pℓ * q.c s - q.Pm * q.ct s)

/-- `D(s) = s(s + ω_f) + k ω_f K(s)`. -/
def D (s : ℂ) : ℂ := s * (s + q.ωf) + q.k * q.ωf * q.K s

/-- `D'(s)`. -/
def Dd (s : ℂ) : ℂ :=
  2 * s + q.ωf - q.k * q.ωf * (q.Pℓ * q.c s / (s + q.αd * (1 - q.b)) +
    q.Pm * q.ct s / (s + q.αd * (1 - q.bb)))

/-- Jacobian at the equilibrium. -/
def J : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, -q.k, 0, 0;
    q.ωf * q.Pδ, -q.ωf, q.ωf * q.Pℓ, q.ωf * q.Pm;
    q.αd * q.a, 0, q.αd * (q.b - 1), 0;
    q.αd * q.ab, 0, 0, q.αd * (q.bb - 1)]

/-- Modulation `A₁ = DJ[z]`. -/
def A1 (z : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 0;
    q.ωf * (q.Pδδ * z 0 + q.Pδℓ * z 2 + q.Pδm * z 3), 0, q.ωf * (q.Pδℓ * z 0 + q.Pℓm * z 3),
      q.ωf * (q.Pδm * z 0 + q.Pℓm * z 2);
    -I * q.αd * q.a * z 0, 0, 0, 0;
    I * q.αd * q.ab * z 0, 0, 0, 0]

/-- Right eigenvector `(1, −λ/k, c(λ), c̃(λ))`. -/
def right (s : ℂ) : Fin 4 → ℂ := ![1, -s / q.k, q.c s, q.ct s]

/-- Left eigenvector with `u_{p_f} = −k/D'(λ)`. -/
def left (s : ℂ) : Fin 4 → ℂ :=
  let upf := -q.k / q.Dd s
  ![upf * (-(s + q.ωf) / q.k), upf, upf * (q.ωf * q.Pℓ / (s + q.αd * (1 - q.b))),
    upf * (q.ωf * q.Pm / (s + q.αd * (1 - q.bb)))]

/-- Forced response to `−θ̇_g` with `θ̂_g = 1` at `s = jω`: `z_δ = −s(s + ω_f)/D(s)`. -/
def forcedδ (s : ℂ) : ℂ := -(s * (s + q.ωf)) / q.D s

def forced (s : ℂ) : Fin 4 → ℂ :=
  ![q.forcedδ s, q.ωf * q.K s * q.forcedδ s / (s + q.ωf), q.c s * q.forcedδ s,
    q.ct s * q.forcedδ s]

/-- The bracket of the pump coefficient. -/
def G (s1 s2 lam : ℂ) : ℂ :=
  q.Pδδ + q.Pδℓ * (q.c s1 + q.c s2) + q.Pδm * (q.ct s1 + q.ct s2) +
    q.Pℓm * (q.c s1 * q.ct s2 + q.ct s1 * q.c s2) - I * (q.Pℓ * q.c lam - q.Pm * q.ct lam)

variable {q}

@[tmio T, powerlib_foundation] theorem c_mul {s : ℂ} (h : s + q.αd * (1 - q.b) ≠ 0) :
    q.c s * (s + q.αd * (1 - q.b)) = q.αd * q.a := by
  simp only [c]; field_simp

@[tmio T, powerlib_foundation] theorem ct_mul {s : ℂ} (h : s + q.αd * (1 - q.bb) ≠ 0) :
    q.ct s * (s + q.αd * (1 - q.bb)) = q.αd * q.ab := by
  simp only [ct]; field_simp

@[tmio T, powerlib_foundation] theorem right_eig {lam : ℂ} (hk : q.k ≠ 0) (h1 : lam + q.αd * (1 - q.b) ≠ 0)
    (h2 : lam + q.αd * (1 - q.bb) ≠ 0) (hD : q.D lam = 0) :
    q.J *ᵥ q.right lam = lam • q.right lam := by
  have e1 := c_mul h1
  have e2 := ct_mul h2
  have hD' : lam * (lam + q.ωf) + q.k * q.ωf * (q.Pδ + q.Pℓ * q.c lam + q.Pm * q.ct lam) = 0 :=
    hD
  funext i
  fin_cases i <;> simp [J, right, mulVec, dotProduct, Fin.sum_univ_four]
  · field_simp
  · field_simp
    linear_combination hD'
  · linear_combination -e1
  · linear_combination -e2

@[tmio T, powerlib_foundation] theorem left_eig {lam : ℂ} (hk : q.k ≠ 0) (h1 : lam + q.αd * (1 - q.b) ≠ 0)
    (h2 : lam + q.αd * (1 - q.bb) ≠ 0) (hD : q.D lam = 0) :
    vecMul (q.left lam) q.J = lam • q.left lam := by
  have hD' : lam * (lam + q.ωf) + q.k * q.ωf * (q.Pδ + q.Pℓ * (q.αd * q.a /
      (lam + q.αd * (1 - q.b))) + q.Pm * (q.αd * q.ab / (lam + q.αd * (1 - q.bb)))) = 0 := hD
  simp only [left]
  generalize -q.k / q.Dd lam = upf
  generalize hd1 : lam + q.αd * (1 - q.b) = d1 at h1 hD'
  generalize hd2 : lam + q.αd * (1 - q.bb) = d2 at h2 hD'
  have hD'' : lam * (lam + q.ωf) * d1 * d2 + q.k * q.ωf * (q.Pδ * d1 * d2 +
      q.Pℓ * q.αd * q.a * d2 + q.Pm * q.αd * q.ab * d1) = 0 := by
    field_simp at hD'; linear_combination hD'
  funext i
  fin_cases i <;> simp [J, vecMul, dotProduct, Fin.sum_univ_four]
  · field_simp
    linear_combination upf * hD''
  · field_simp
    ring
  · field_simp
    rw [← hd1]; ring
  · field_simp
    rw [← hd2]; ring

@[tmio T, powerlib_foundation] theorem left_right {lam : ℂ} (hk : q.k ≠ 0) (h1 : lam + q.αd * (1 - q.b) ≠ 0)
    (h2 : lam + q.αd * (1 - q.bb) ≠ 0) (hDd : q.Dd lam ≠ 0) :
    q.left lam ⬝ᵥ q.right lam = 1 := by
  have hdef : q.Dd lam = 2 * lam + q.ωf - q.k * q.ωf * (q.Pℓ * q.c lam /
      (lam + q.αd * (1 - q.b)) + q.Pm * q.ct lam / (lam + q.αd * (1 - q.bb))) := rfl
  simp only [left, right, dotProduct, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons]
  generalize q.Dd lam = DD at hDd hdef ⊢
  generalize q.c lam = c1 at hdef ⊢
  generalize q.ct lam = c2 at hdef ⊢
  generalize lam + q.αd * (1 - q.b) = d1 at h1 hdef ⊢
  generalize lam + q.αd * (1 - q.bb) = d2 at h2 hdef ⊢
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div] at *
  have hDD : DD * (d1 * d2) = (2 * lam + q.ωf) * d1 * d2 -
      q.k * q.ωf * (q.Pℓ * c1 * d2 + q.Pm * c2 * d1) := by
    rw [hdef]; field_simp
  field_simp
  linear_combination (-1 : ℂ) * hDD

@[tmio T, powerlib_foundation] theorem forced_eq {s : ℂ} (hD : q.D s ≠ 0) (hω : s + q.ωf ≠ 0)
    (h1 : s + q.αd * (1 - q.b) ≠ 0) (h2 : s + q.αd * (1 - q.bb) ≠ 0) :
    (s • (1 : Matrix (Fin 4) (Fin 4) ℂ) - q.J) *ᵥ q.forced s = ![-s, 0, 0, 0] := by
  have e1 := c_mul h1
  have e2 := ct_mul h2
  have hDdef : q.D s = s * (s + q.ωf) + q.k * q.ωf * q.K s := rfl
  have hKdef : q.K s = q.Pδ + q.Pℓ * q.c s + q.Pm * q.ct s := rfl
  funext i
  fin_cases i
  · simp [J, forced, forcedδ, mulVec, dotProduct, Fin.sum_univ_four, Matrix.one_apply]
    generalize q.D s = DD at hD hDdef ⊢
    field_simp
    rw [hDdef]; ring
  · simp [J, forced, mulVec, dotProduct, Fin.sum_univ_four, Matrix.one_apply]
    rw [hKdef]; field_simp; ring
  · simp [J, forced, mulVec, dotProduct, Fin.sum_univ_four, Matrix.one_apply]
    linear_combination (q.forcedδ s) * e1
  · simp [J, forced, mulVec, dotProduct, Fin.sum_univ_four, Matrix.one_apply]
    linear_combination (q.forcedδ s) * e2

/-- `g = u_{p_f} ω_f z_δ G(s₁, s₂, λ)` with the forced response at `s₁ = jω` and the conjugate
mode vector `r(s₂)`, `s₂ = λ̄`. -/
@[tmio T, powerlib_foundation] theorem pump_eq (s1 s2 lam : ℂ) :
    pumpc (q.A1 (q.forced s1)) (q.left lam) (q.right s2) =
      (-q.k / q.Dd lam) * q.ωf * q.forcedδ s1 * q.G s1 s2 lam := by
  simp only [pumpc, A1, forced, left, right, G, c, ct, mulVec, dotProduct, Fin.sum_univ_four]
  simp
  ring

/-- The exact remainder decomposition of the bracket:
`G = P_δδ + H_q(λ) − H_q(s₁) − H_q(s₂) + (P_δℓ − jP_ℓ)(c₁ + c₂) + (P_δℓ̄ + jP_ℓ̄)(c̃₁ + c̃₂)
+ P_ℓℓ̄ (c₁c̃₂ + c̃₁c₂)`. -/
@[tmio T, powerlib_foundation] theorem G_eq (s1 s2 lam : ℂ) :
    q.G s1 s2 lam = q.Pδδ + q.Hq lam - q.Hq s1 - q.Hq s2 +
      (q.Pδℓ - I * q.Pℓ) * (q.c s1 + q.c s2) + (q.Pδm + I * q.Pm) * (q.ct s1 + q.ct s2) +
      q.Pℓm * (q.c s1 * q.ct s2 + q.ct s1 * q.c s2) := by
  simp only [G, Hq]
  ring

/-- Kernel form: when the power row is a pure Park rotation (`P_δℓ = jP_ℓ`, `P_δℓ̄ = −jP_ℓ̄`,
`P_ℓℓ̄ = 0`), `G = P_δδ + H_q(λ) − H_q(s₁) − H_q(s₂)`. -/
@[tmio T, powerlib_foundation] theorem G_kernel (hl : q.Pδℓ = I * q.Pℓ) (hm : q.Pδm = -I * q.Pm) (hlm : q.Pℓm = 0)
    (s1 s2 lam : ℂ) :
    q.G s1 s2 lam = q.Pδδ + (q.Hq lam - q.Hq s1 - q.Hq s2) := by
  rw [G_eq, hl, hm, hlm]
  ring

/-- At exact 2:1 tuning, `jω + λ̄ = λ` with `ω = 2 Im λ`. -/
@[tmio T, powerlib_foundation] theorem tuning (lam : ℂ) : ((2 * lam.im : ℝ) : ℂ) * I + conj lam = lam := by
  apply Complex.ext
  · simp
  · simp; ring

/-- The stiffness weight and the branch weights through `c_D = 2jΩ/D'(λ)` and
`K_r = Ω²/(k ω_f)`: `u_{p_f} ω_f = (jΩ/2) c_D/K_r`. -/
@[tmio T, powerlib_foundation] theorem upf_eq {Ω : ℂ} (lam : ℂ) (hΩ : Ω ≠ 0) (hDd : q.Dd lam ≠ 0) :
    (-q.k / q.Dd lam) * q.ωf = (I * Ω / 2) * (2 * I * Ω / q.Dd lam) / (Ω ^ 2 / (q.k * q.ωf)) := by
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- Table 4: the weight `w_{p_f δ} = u_{p_f} ω_f P_δ r_δ`. -/
@[tmio T, powerlib_foundation] theorem weight_pfδ (lam : ℂ) :
    ParametricResonance.Element.weight q.J (q.left lam) (q.right lam) 1 0 =
      (-q.k / q.Dd lam) * q.ωf * q.Pδ := by
  simp [ParametricResonance.Element.weight, J, left, right]
  ring

/-- Table 4: the weights of the branch entrances `(p_f, ℓ)`, `(p_f, ℓ̄)` sum to
`u_{p_f} ω_f K_ℓ(λ)`. -/
@[tmio T, powerlib_foundation] theorem weight_branch (lam : ℂ) :
    ParametricResonance.Element.weight q.J (q.left lam) (q.right lam) 1 2 +
        ParametricResonance.Element.weight q.J (q.left lam) (q.right lam) 1 3 =
      (-q.k / q.Dd lam) * q.ωf * q.Kl lam := by
  simp [ParametricResonance.Element.weight, J, left, right, Kl]
  ring

/-- Table 6: `S_m = −z_δ(2jΩ) = (4 − 4jζ₀)/(4 − 4jζ₀ − K(2jΩ)/K_r)` with `ζ₀ = ω_f/(2Ω)` and
`K_r = Ω²/(k ω_f)`, exactly. -/
@[tmio T, powerlib_foundation] theorem sensitivity_eq {Ω : ℂ} (hΩ : Ω ≠ 0) (hD : q.D (2 * Ω * I) ≠ 0) :
    -q.forcedδ (2 * Ω * I) =
      (4 - 4 * I * (q.ωf / (2 * Ω))) /
        (4 - 4 * I * (q.ωf / (2 * Ω)) - q.K (2 * Ω * I) / (Ω ^ 2 / (q.k * q.ωf))) := by
  have hden : (4 - 4 * I * (q.ωf / (2 * Ω)) - q.K (2 * Ω * I) / (Ω ^ 2 / (q.k * q.ωf))) =
      -q.D (2 * Ω * I) / Ω ^ 2 := by
    simp only [D]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [hden, forcedδ]
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- The exact normalized pump `ĝ = 2|g|/Ω`: `ĝ = |c_D| |z_δ| |G|/|K_r|` with
`c_D = 2jΩ/D'(λ)`, `K_r = Ω²/(k ω_f)`, `Ω = Im λ`. -/
@[tmio T, powerlib_foundation] theorem normalizedPump_eq (lam : ℂ) (ω : ℂ) (hΩ : 0 < lam.im) (hDd : q.Dd lam ≠ 0)
    (hkω : q.k * q.ωf ≠ 0) :
    ParametricResonance.Element.normalizedPump
        (pumpc (q.A1 (q.forced ω)) (q.left lam) (q.right (conj lam))) lam.im =
      ‖2 * I * (lam.im : ℂ) / q.Dd lam‖ * ‖q.forcedδ ω‖ * ‖q.G ω (conj lam) lam‖ /
        ‖(lam.im : ℂ) ^ 2 / (q.k * q.ωf)‖ := by
  have hΩc : (lam.im : ℂ) ≠ 0 := by exact_mod_cast hΩ.ne'
  rw [ParametricResonance.Element.normalizedPump, pump_eq, upf_eq lam hΩc hDd]
  have hK : ‖(lam.im : ℂ) ^ 2 / (q.k * q.ωf)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact div_ne_zero (pow_ne_zero _ hΩc) hkω
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  simp only [norm_mul, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hΩ, h2] at hK ⊢
  field_simp

/-- The characteristic polynomial of the four-state core:
`det(sI − J) = D(s)(s + α_d(1 − b))(s + α_d(1 − b̄))`. -/
@[tmio T, powerlib_foundation] theorem charPoly {s : ℂ} (h1 : s + q.αd * (1 - q.b) ≠ 0) (h2 : s + q.αd * (1 - q.bb) ≠ 0) :
    (s • (1 : Matrix (Fin 4) (Fin 4) ℂ) - q.J).det =
      q.D s * (s + q.αd * (1 - q.b)) * (s + q.αd * (1 - q.bb)) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, J, Matrix.one_apply, Fin.succAbove,
    Matrix.submatrix]
  simp only [D, K, c, ct]
  field_simp
  ring

end Coeffs
/-! ## The model of the source -/

/-- Parameters of the PSC with active damping (the source's check model). -/
structure Model where
  k : ℝ
  ωf : ℝ
  αd : ℝ
  ra : ℝ
  E : ℝ
  V : ℝ
  Rf : ℝ
  Rg : ℝ
  X : ℝ
  Xg : ℝ

namespace Model

variable (p : Model)

/-- `Z = R + r_a + jX`, `R = R_f + R_g`. -/
def Z : ℂ := ((p.Rf + p.Rg + p.ra : ℝ) : ℂ) + (p.X : ℂ) * I
def Zc : ℂ := ((p.Rf + p.Rg + p.ra : ℝ) : ℂ) - (p.X : ℂ) * I
/-- `Z₀ = R + jX`. -/
def Z0 : ℂ := ((p.Rf + p.Rg : ℝ) : ℂ) + (p.X : ℂ) * I
def Z0c : ℂ := ((p.Rf + p.Rg : ℝ) : ℂ) - (p.X : ℂ) * I
/-- Grid impedance `Z_g = R_g + jX_g` between the PCC and the grid source. -/
def Zg : ℂ := (p.Rg : ℂ) + (p.Xg : ℂ) * I
def Zgc : ℂ := (p.Rg : ℂ) - (p.Xg : ℂ) * I

/-- Grid voltage in the converter frame, `e_g = V e^{−jδ}` (complexified angle). -/
def φ (δ : ℂ) : ℂ := p.V * exp (-(δ * I))
/-- Its conjugate partner `V e^{jδ}`. -/
def φt (δ : ℂ) : ℂ := p.V * exp (δ * I)
/-- `i = (E + r_a ℓ − e_g)/Z`. -/
def cur (δ ℓ : ℂ) : ℂ := (p.E + p.ra * ℓ - p.φ δ) / p.Z
def curt (δ m : ℂ) : ℂ := (p.E + p.ra * m - p.φt δ) / p.Zc
/-- PCC voltage `u = e_g + Z_g i`. -/
def volt (δ ℓ : ℂ) : ℂ := p.φ δ + p.Zg * p.cur δ ℓ
def voltt (δ m : ℂ) : ℂ := p.φt δ + p.Zgc * p.curt δ m
/-- PCC power `p = (u ī + ū i)/2` in the independent coordinates `(δ, ℓ, ℓ̄)`. -/
def pw (δ ℓ m : ℂ) : ℂ := (p.volt δ ℓ * p.curt δ m + p.voltt δ m * p.cur δ ℓ) / 2

/-- The field in the coordinates `(δ, p_f, ℓ, ℓ̄)` with the grid-frequency input `θ̇_g`. -/
def field (θd Pref : ℝ) (x : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![p.k * (Pref - x 1) - θd, p.ωf * (p.pw (x 0) (x 2) (x 3) - x 1),
    p.αd * (p.cur (x 0) (x 2) - x 2), p.αd * (p.curt (x 0) (x 3) - x 3)]

@[tmio M, powerlib_domain] theorem conj_φ (δ : ℝ) : conj (p.φ δ) = p.φt δ := by
  simp only [φ, φt, map_mul, conj_ofReal, ← Complex.exp_conj, map_neg, conj_I]
  congr 2; ring

@[tmio M, powerlib_domain] theorem conj_Z : conj p.Z = p.Zc := by simp [Z, Zc, map_add, map_mul, conj_ofReal, conj_I]; ring

@[tmio M, powerlib_domain] theorem conj_Zg : conj p.Zg = p.Zgc := by simp [Zg, Zgc, map_add, map_mul, conj_ofReal, conj_I]; ring

@[tmio M, powerlib_domain] theorem conj_Z0 : conj p.Z0 = p.Z0c := by simp [Z0, Z0c, map_add, map_mul, conj_ofReal, conj_I]; ring

/-- On the real slice (`δ` real, `ℓ̄ = conj ℓ`) the conjugate current is the conjugate of `i`. -/
@[tmio M, powerlib_domain] theorem curt_real (δ : ℝ) (ℓ : ℂ) : p.curt δ (conj ℓ) = conj (p.cur δ ℓ) := by
  simp only [curt, cur, map_div₀, map_sub, map_add, map_mul, conj_ofReal, conj_φ, conj_Z]

/-- On the real slice the power is the source's PCC power `Re(u ī)`. -/
@[tmio M, powerlib_domain] theorem pw_real (δ : ℝ) (ℓ : ℂ) :
    p.pw δ ℓ (conj ℓ) = ((p.volt δ ℓ * conj (p.cur δ ℓ)).re : ℂ) := by
  have hv : p.voltt δ (conj ℓ) = conj (p.volt δ ℓ) := by
    simp only [voltt, volt, curt_real, map_add, map_mul, conj_φ, conj_Zg]
  rw [pw, curt_real, hv]
  apply Complex.ext
  all_goals (simp [Complex.mul_re, Complex.mul_im]; try ring)

@[tmio M, powerlib_domain] theorem Zg_add : p.Zg + p.Zgc = 2 * p.Rg := by simp only [Zg, Zgc]; ring

/-- `p = (e_g ī + ē_g i)/2 + R_g i ī`: the grid reactance does not enter. -/
@[tmio M, powerlib_domain] theorem pw_eq (δ ℓ m : ℂ) :
    p.pw δ ℓ m = (p.φ δ * p.curt δ m + p.φt δ * p.cur δ ℓ) / 2 +
      p.Rg * p.cur δ ℓ * p.curt δ m := by
  simp only [pw, volt, voltt]
  linear_combination (p.cur δ ℓ * p.curt δ m / 2) * p.Zg_add

/-! ### Partial derivatives -/

def curδ (δ : ℂ) : ℂ := I * p.φ δ / p.Z
def curtδ (δ : ℂ) : ℂ := -I * p.φt δ / p.Zc
def pwδ (δ ℓ m : ℂ) : ℂ :=
  ((-I * p.φ δ) * p.curt δ m + p.φ δ * p.curtδ δ + (I * p.φt δ) * p.cur δ ℓ +
    p.φt δ * p.curδ δ) / 2 + p.Rg * (p.curδ δ * p.curt δ m + p.cur δ ℓ * p.curtδ δ)
def pwℓ (δ m : ℂ) : ℂ := p.φt δ * (p.ra / p.Z) / 2 + p.Rg * (p.ra / p.Z) * p.curt δ m
def pwm (δ ℓ : ℂ) : ℂ := p.φ δ * (p.ra / p.Zc) / 2 + p.Rg * p.cur δ ℓ * (p.ra / p.Zc)
def pwδδ (δ ℓ m : ℂ) : ℂ :=
  (-p.φ δ * p.curt δ m - I * p.φ δ * p.curtδ δ - p.φt δ * p.cur δ ℓ + I * p.φt δ * p.curδ δ) / 2 +
    p.Rg * (-I * p.curδ δ * p.curt δ m + 2 * p.curδ δ * p.curtδ δ + I * p.cur δ ℓ * p.curtδ δ)
def pwδℓ (δ : ℂ) : ℂ := I * p.φt δ * (p.ra / p.Z) / 2 + p.Rg * (p.ra / p.Z) * p.curtδ δ
def pwδm (δ : ℂ) : ℂ := -I * p.φ δ * (p.ra / p.Zc) / 2 + p.Rg * p.curδ δ * (p.ra / p.Zc)
def pwℓm : ℂ := p.Rg * (p.ra / p.Z) * (p.ra / p.Zc)

@[tmio M, powerlib_domain] theorem hasDerivAt_φ (δ : ℂ) : HasDerivAt p.φ (-I * p.φ δ) δ := by
  have h := (((hasDerivAt_id δ).mul_const I).neg.cexp).const_mul (p.V : ℂ)
  convert h using 1
  · funext x; simp [φ]
  · simp [φ]; ring

@[tmio M, powerlib_domain] theorem hasDerivAt_φt (δ : ℂ) : HasDerivAt p.φt (I * p.φt δ) δ := by
  have h := (((hasDerivAt_id δ).mul_const I).cexp).const_mul (p.V : ℂ)
  convert h using 1
  · funext x; simp [φt]
  · simp [φt]; ring

@[tmio M, powerlib_domain] theorem hasDerivAt_cur_δ (δ ℓ : ℂ) :
    HasDerivAt (fun δ => p.cur δ ℓ) (p.curδ δ) δ := by
  have h := ((p.hasDerivAt_φ δ).const_sub ((p.E : ℂ) + p.ra * ℓ)).div_const p.Z
  convert h using 1
  · funext x; simp [cur]
  · simp only [curδ]; ring

@[tmio M, powerlib_domain] theorem hasDerivAt_cur_ℓ (δ ℓ : ℂ) :
    HasDerivAt (fun ℓ => p.cur δ ℓ) (p.ra / p.Z) ℓ := by
  have h := ((((hasDerivAt_id ℓ).const_mul (p.ra : ℂ)).const_add (p.E : ℂ)).sub_const
    (p.φ δ)).div_const p.Z
  convert h using 1
  · funext x; simp [cur]
  · ring

@[tmio M, powerlib_domain] theorem hasDerivAt_curt_δ (δ m : ℂ) :
    HasDerivAt (fun δ => p.curt δ m) (p.curtδ δ) δ := by
  have h := ((p.hasDerivAt_φt δ).const_sub ((p.E : ℂ) + p.ra * m)).div_const p.Zc
  convert h using 1
  · funext x; simp [curt]
  · simp only [curtδ]; ring

@[tmio M, powerlib_domain] theorem hasDerivAt_curt_m (δ m : ℂ) :
    HasDerivAt (fun m => p.curt δ m) (p.ra / p.Zc) m := by
  have h := ((((hasDerivAt_id m).const_mul (p.ra : ℂ)).const_add (p.E : ℂ)).sub_const
    (p.φt δ)).div_const p.Zc
  convert h using 1
  · funext x; simp [curt]
  · ring

@[tmio M, powerlib_domain] theorem hasDerivAt_pw_δ (δ ℓ m : ℂ) :
    HasDerivAt (fun δ => p.pw δ ℓ m) (p.pwδ δ ℓ m) δ := by
  have h := ((((p.hasDerivAt_φ δ).mul (p.hasDerivAt_curt_δ δ m)).add
    ((p.hasDerivAt_φt δ).mul (p.hasDerivAt_cur_δ δ ℓ))).div_const 2).add
    (((p.hasDerivAt_cur_δ δ ℓ).mul (p.hasDerivAt_curt_δ δ m)).const_mul (p.Rg : ℂ))
  convert h using 1
  · funext x; simp only [Pi.add_apply, Pi.mul_apply]; rw [pw_eq]; ring
  · simp only [pwδ]; ring

@[tmio M, powerlib_domain] theorem hasDerivAt_pw_ℓ (δ ℓ m : ℂ) :
    HasDerivAt (fun ℓ => p.pw δ ℓ m) (p.pwℓ δ m) ℓ := by
  have h := ((((p.hasDerivAt_cur_ℓ δ ℓ).const_mul (p.φt δ)).div_const 2).const_add
    (p.φ δ * p.curt δ m / 2)).add
    (((p.hasDerivAt_cur_ℓ δ ℓ).mul_const (p.curt δ m)).const_mul (p.Rg : ℂ))
  convert h using 1
  · funext x; simp only [Pi.add_apply]; rw [pw_eq]; ring
  · simp only [pwℓ]; ring

@[tmio M, powerlib_domain] theorem hasDerivAt_pw_m (δ ℓ m : ℂ) :
    HasDerivAt (fun m => p.pw δ ℓ m) (p.pwm δ ℓ) m := by
  have h := ((((p.hasDerivAt_curt_m δ m).const_mul (p.φ δ)).div_const 2).add_const
    (p.φt δ * p.cur δ ℓ / 2)).add
    (((p.hasDerivAt_curt_m δ m).const_mul (p.cur δ ℓ)).const_mul (p.Rg : ℂ))
  convert h using 1
  · funext x; simp only [Pi.add_apply]; rw [pw_eq]; ring
  · simp only [pwm]; ring

/-! ### The modulation `A₁` as the directional derivative of the Jacobian -/

section Line

variable (δ ℓ m zδ zℓ zm : ℂ)

@[tmio M, powerlib_domain] theorem line_φ (t : ℂ) :
    HasDerivAt (fun t => p.φ (δ + t * zδ)) (-I * p.φ (δ + t * zδ) * zδ) t := by
  have hL : HasDerivAt (fun t : ℂ => δ + t * zδ) zδ t := by
    simpa using ((hasDerivAt_id t).mul_const zδ).const_add δ
  have h := (p.hasDerivAt_φ (δ + t * zδ)).comp t hL
  simpa [Function.comp_def] using h

@[tmio M, powerlib_domain] theorem line_φt (t : ℂ) :
    HasDerivAt (fun t => p.φt (δ + t * zδ)) (I * p.φt (δ + t * zδ) * zδ) t := by
  have hL : HasDerivAt (fun t : ℂ => δ + t * zδ) zδ t := by
    simpa using ((hasDerivAt_id t).mul_const zδ).const_add δ
  have h := (p.hasDerivAt_φt (δ + t * zδ)).comp t hL
  simpa [Function.comp_def] using h

@[tmio M, powerlib_domain] theorem line_cur (t : ℂ) :
    HasDerivAt (fun t => p.cur (δ + t * zδ) (ℓ + t * zℓ))
      (p.curδ (δ + t * zδ) * zδ + p.ra / p.Z * zℓ) t := by
  have hl : HasDerivAt (fun t : ℂ => ℓ + t * zℓ) zℓ t := by
    simpa using ((hasDerivAt_id t).mul_const zℓ).const_add ℓ
  have h := ((((hl.const_mul (p.ra : ℂ)).const_add (p.E : ℂ)).sub
    (p.line_φ δ zδ t))).div_const p.Z
  convert h using 1
  · funext x; simp [cur]
  · simp only [curδ]; ring

@[tmio M, powerlib_domain] theorem line_curt (t : ℂ) :
    HasDerivAt (fun t => p.curt (δ + t * zδ) (m + t * zm))
      (p.curtδ (δ + t * zδ) * zδ + p.ra / p.Zc * zm) t := by
  have hl : HasDerivAt (fun t : ℂ => m + t * zm) zm t := by
    simpa using ((hasDerivAt_id t).mul_const zm).const_add m
  have h := ((((hl.const_mul (p.ra : ℂ)).const_add (p.E : ℂ)).sub
    (p.line_φt δ zδ t))).div_const p.Zc
  convert h using 1
  · funext x; simp [curt]
  · simp only [curtδ]; ring

@[tmio M, powerlib_domain] theorem line_curδ (t : ℂ) :
    HasDerivAt (fun t => p.curδ (δ + t * zδ)) (-I * p.curδ (δ + t * zδ) * zδ) t := by
  have h := ((p.line_φ δ zδ t).const_mul I).div_const p.Z
  convert h using 1
  · funext x; rfl
  · unfold Model.curδ; ring

@[tmio M, powerlib_domain] theorem line_curtδ (t : ℂ) :
    HasDerivAt (fun t => p.curtδ (δ + t * zδ)) (I * p.curtδ (δ + t * zδ) * zδ) t := by
  have h := ((p.line_φt δ zδ t).const_mul (-I)).div_const p.Zc
  convert h using 1
  · funext x; rfl
  · unfold Model.curtδ; ring

/-- `(A₁)_{p_f δ} = ω_f (P_δδ z_δ + P_δℓ z_ℓ + P_δℓ̄ z_ℓ̄)`. -/
@[tmio M, powerlib_domain] theorem line_pwδ :
    HasDerivAt (fun t => p.pwδ (δ + t * zδ) (ℓ + t * zℓ) (m + t * zm))
      (p.pwδδ δ ℓ m * zδ + p.pwδℓ δ * zℓ + p.pwδm δ * zm) 0 := by
  have hφ := p.line_φ δ zδ 0
  have hφt := p.line_φt δ zδ 0
  have hc := p.line_cur δ ℓ zδ zℓ 0
  have hct := p.line_curt δ m zδ zm 0
  have hcd := p.line_curδ δ zδ 0
  have hctd := p.line_curtδ δ zδ 0
  simp only [zero_mul, add_zero] at hφ hφt hc hct hcd hctd
  have h := ((((((hφ.const_mul (-I)).mul hct).add (hφ.mul hctd)).add
    ((hφt.const_mul I).mul hc)).add (hφt.mul hcd)).div_const 2).add
    (((hcd.mul hct).add (hc.mul hctd)).const_mul (p.Rg : ℂ))
  convert h using 1
  · funext t; simp only [pwδ, Pi.add_apply, Pi.mul_apply]
  · simp only [pwδδ, pwδℓ, pwδm]; ring_nf; rw [I_sq]; ring

/-- `(A₁)_{p_f ℓ} = ω_f (P_δℓ z_δ + P_ℓℓ̄ z_ℓ̄)`. -/
@[tmio M, powerlib_domain] theorem line_pwℓ :
    HasDerivAt (fun t => p.pwℓ (δ + t * zδ) (m + t * zm))
      (p.pwδℓ δ * zδ + p.pwℓm * zm) 0 := by
  have hφt := p.line_φt δ zδ 0
  have hct := p.line_curt δ m zδ zm 0
  simp only [zero_mul, add_zero] at hφt hct
  have h := ((hφt.mul_const (p.ra / p.Z)).div_const 2).add
    ((hct.const_mul (p.ra / p.Z)).const_mul (p.Rg : ℂ))
  convert h using 1
  · funext t; simp only [pwℓ, Pi.add_apply]; ring
  · simp only [pwδℓ, pwℓm]; ring

/-- `(A₁)_{p_f ℓ̄} = ω_f (P_δℓ̄ z_δ + P_ℓℓ̄ z_ℓ)`. -/
@[tmio M, powerlib_domain] theorem line_pwm :
    HasDerivAt (fun t => p.pwm (δ + t * zδ) (ℓ + t * zℓ))
      (p.pwδm δ * zδ + p.pwℓm * zℓ) 0 := by
  have hφ := p.line_φ δ zδ 0
  have hc := p.line_cur δ ℓ zδ zℓ 0
  simp only [zero_mul, add_zero] at hφ hc
  have h := ((hφ.mul_const (p.ra / p.Zc)).div_const 2).add
    ((hc.mul_const (p.ra / p.Zc)).const_mul (p.Rg : ℂ))
  convert h using 1
  · funext t; simp only [pwm, Pi.add_apply]; ring
  · simp only [pwδm, pwℓm]; ring

/-- `(A₁)_{ℓ δ} = −j α_d (∂i/∂δ) z_δ`: a pure rotation of the `(ℓ, δ)` column. -/
@[tmio M, powerlib_domain] theorem line_curδ0 :
    HasDerivAt (fun t => p.curδ (δ + t * zδ)) (-I * p.curδ δ * zδ) 0 := by
  simpa using p.line_curδ δ zδ 0

@[tmio M, powerlib_domain] theorem line_curtδ0 :
    HasDerivAt (fun t => p.curtδ (δ + t * zδ)) (I * p.curtδ δ * zδ) 0 := by
  simpa using p.line_curtδ δ zδ 0

end Line

/-! ### Equilibrium and the coefficients of the core -/

/-- Equilibrium high-pass state `ℓ₀ = i₀ = (E − V e^{−jδ₀})/(R + jX)`. -/
def ell0 (δ0 : ℂ) : ℂ := (p.E - p.φ δ0) / p.Z0
def m0 (δ0 : ℂ) : ℂ := (p.E - p.φt δ0) / p.Z0c

@[tmio M, powerlib_domain] theorem Z_eq : p.Z = p.Z0 + p.ra := by simp only [Z, Z0]; push_cast; ring

@[tmio M, powerlib_domain] theorem Zc_eq : p.Zc = p.Z0c + p.ra := by simp only [Zc, Z0c]; push_cast; ring

/-- At the equilibrium `ℓ₀ = i(δ₀, ℓ₀)`: the high-pass branch does not move the operating point. -/
@[tmio M, powerlib_domain] theorem cur_ell0 (δ0 : ℂ) (hZ : p.Z ≠ 0) (hZ0 : p.Z0 ≠ 0) :
    p.cur δ0 (p.ell0 δ0) = p.ell0 δ0 := by
  simp only [cur, ell0]
  rw [div_eq_div_iff hZ hZ0, p.Z_eq]
  field_simp
  ring

@[tmio M, powerlib_domain] theorem curt_m0 (δ0 : ℂ) (hZ : p.Zc ≠ 0) (hZ0 : p.Z0c ≠ 0) :
    p.curt δ0 (p.m0 δ0) = p.m0 δ0 := by
  simp only [curt, m0]
  rw [div_eq_div_iff hZ hZ0, p.Zc_eq]
  field_simp
  ring

/-- The coefficients of the linearized core at the equilibrium angle `δ₀`. -/
def coeffs (δ0 : ℂ) : Coeffs where
  k := p.k
  ωf := p.ωf
  αd := p.αd
  a := p.curδ δ0
  ab := p.curtδ δ0
  b := p.ra / p.Z
  bb := p.ra / p.Zc
  Pδ := p.pwδ δ0 (p.ell0 δ0) (p.m0 δ0)
  Pℓ := p.pwℓ δ0 (p.m0 δ0)
  Pm := p.pwm δ0 (p.ell0 δ0)
  Pδδ := p.pwδδ δ0 (p.ell0 δ0) (p.m0 δ0)
  Pδℓ := p.pwδℓ δ0
  Pδm := p.pwδm δ0
  Pℓm := p.pwℓm

/-- With `R_g = 0` the power row is a pure Park rotation: `P_δℓ = jP_ℓ`, `P_δℓ̄ = −jP_ℓ̄`,
`P_ℓℓ̄ = 0`. -/
@[tmio M, powerlib_domain] theorem rotation_of_Rg (δ0 : ℂ) (hRg : p.Rg = 0) :
    (p.coeffs δ0).Pδℓ = I * (p.coeffs δ0).Pℓ ∧ (p.coeffs δ0).Pδm = -I * (p.coeffs δ0).Pm ∧
      (p.coeffs δ0).Pℓm = 0 := by
  simp only [coeffs, pwδℓ, pwℓ, pwδm, pwm, pwℓm, hRg]
  refine ⟨?_, ?_, ?_⟩ <;> push_cast <;> ring

/-- With `R_g = 0` the exact bracket of the pump coefficient is the kernel
`P_δδ + H_q(λ) − H_q(s₁) − H_q(s₂)`. -/
@[tmio M, powerlib_domain] theorem G_kernel_of_Rg (δ0 : ℂ) (hRg : p.Rg = 0) (s1 s2 lam : ℂ) :
    (p.coeffs δ0).G s1 s2 lam =
      (p.coeffs δ0).Pδδ + ((p.coeffs δ0).Hq lam - (p.coeffs δ0).Hq s1 - (p.coeffs δ0).Hq s2) :=
  let h := p.rotation_of_Rg δ0 hRg
  Coeffs.G_kernel h.1 h.2.1 h.2.2 s1 s2 lam

/-! ### The branch transfers with `R_g = 0` -/

@[tmio M, powerlib_domain] theorem φ_mul_φt (δ : ℂ) : p.φ δ * p.φt δ = (p.V : ℂ) ^ 2 := by
  simp only [φ, φt]
  rw [show (p.V : ℂ) * exp (-(δ * I)) * (p.V * exp (δ * I)) =
    (p.V : ℂ) ^ 2 * (exp (-(δ * I)) * exp (δ * I)) by ring, ← Complex.exp_add]
  simp

/-- `H_q(s) = (V² r_a α_d/2)[1/(Z(Zs + α_d Z₀)) + 1/(Z̄(Z̄s + α_d Z̄₀))]` for `R_g = 0`: the
quadrature branch transfer does not depend on the load. -/
@[tmio M, powerlib_domain] theorem Hq_eq (δ0 s : ℂ) (hRg : p.Rg = 0) (hZ : p.Z ≠ 0) (hZc : p.Zc ≠ 0)
    (h1 : p.Z * s + p.αd * p.Z0 ≠ 0) (h2 : p.Zc * s + p.αd * p.Z0c ≠ 0) :
    (p.coeffs δ0).Hq s = (p.V : ℂ) ^ 2 * p.ra * p.αd / 2 *
      (1 / (p.Z * (p.Z * s + p.αd * p.Z0)) + 1 / (p.Zc * (p.Zc * s + p.αd * p.Z0c))) := by
  have e1 : s + p.αd * (1 - p.ra / p.Z) = (p.Z * s + p.αd * p.Z0) / p.Z := by
    rw [p.Z_eq] at hZ ⊢; field_simp; ring
  have e2 : s + p.αd * (1 - p.ra / p.Zc) = (p.Zc * s + p.αd * p.Z0c) / p.Zc := by
    rw [p.Zc_eq] at hZc ⊢; field_simp; ring
  have hV := p.φ_mul_φt δ0
  simp only [Coeffs.Hq, Coeffs.c, Coeffs.ct, coeffs, pwℓ, pwm, curδ, curtδ, hRg, e1, e2]
  generalize p.φ δ0 = A at hV ⊢
  generalize p.φt δ0 = B at hV ⊢
  generalize p.Z * s + p.αd * p.Z0 = w1 at h1 ⊢
  generalize p.Zc * s + p.αd * p.Z0c = w2 at h2 ⊢
  push_cast
  rw [show (p.V : ℂ) ^ 2 = A * B from hV.symm]
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- `K_ℓ(s) = (jV² r_a α_d/2)[1/(Z(Zs + α_d Z₀)) − 1/(Z̄(Z̄s + α_d Z̄₀))]` for `R_g = 0`: the
in-phase branch transfer does not depend on the load either. -/
@[tmio M, powerlib_domain] theorem Kl_eq (δ0 s : ℂ) (hRg : p.Rg = 0) (hZ : p.Z ≠ 0) (hZc : p.Zc ≠ 0)
    (h1 : p.Z * s + p.αd * p.Z0 ≠ 0) (h2 : p.Zc * s + p.αd * p.Z0c ≠ 0) :
    (p.coeffs δ0).Kl s = I * (p.V : ℂ) ^ 2 * p.ra * p.αd / 2 *
      (1 / (p.Z * (p.Z * s + p.αd * p.Z0)) - 1 / (p.Zc * (p.Zc * s + p.αd * p.Z0c))) := by
  have e1 : s + p.αd * (1 - p.ra / p.Z) = (p.Z * s + p.αd * p.Z0) / p.Z := by
    rw [p.Z_eq] at hZ ⊢; field_simp; ring
  have e2 : s + p.αd * (1 - p.ra / p.Zc) = (p.Zc * s + p.αd * p.Z0c) / p.Zc := by
    rw [p.Zc_eq] at hZc ⊢; field_simp; ring
  have hV := p.φ_mul_φt δ0
  simp only [Coeffs.Kl, Coeffs.c, Coeffs.ct, coeffs, pwℓ, pwm, curδ, curtδ, hRg, e1, e2]
  generalize p.φ δ0 = A at hV ⊢
  generalize p.φt δ0 = B at hV ⊢
  generalize p.Z * s + p.αd * p.Z0 = w1 at h1 ⊢
  generalize p.Zc * s + p.αd * p.Z0c = w2 at h2 ⊢
  push_cast
  rw [show (p.V : ℂ) ^ 2 = A * B from hV.symm]
  field_simp
  ring

/-! ### Lossless network: the closed forms of the source -/

/-- Lossless network (`R_f = R_g = 0`), `s = α_d S`: the branch transfers are the real rational
functions `K_ℓ = V² r_a² X (2S + 1)/(N(NS² + 2X²S + X²))` and
`H_q = V² r_a ((r_a² − X²)S − X²)/(N(NS² + 2X²S + X²))`, `N = r_a² + X²`. -/
@[tmio M, powerlib_domain] theorem branch_lossless (δ0 S : ℂ) (hRf : p.Rf = 0) (hRg : p.Rg = 0) (hX : p.X ≠ 0)
    (hαd : p.αd ≠ 0)
    (hden : ((p.ra ^ 2 + p.X ^ 2 : ℝ) : ℂ) * S ^ 2 + 2 * (p.X : ℂ) ^ 2 * S + (p.X : ℂ) ^ 2 ≠ 0) :
    (p.coeffs δ0).Kl (p.αd * S) = (p.V : ℂ) ^ 2 * p.ra ^ 2 * p.X * (2 * S + 1) /
        (((p.ra ^ 2 + p.X ^ 2 : ℝ) : ℂ) * (((p.ra ^ 2 + p.X ^ 2 : ℝ) : ℂ) * S ^ 2 +
          2 * (p.X : ℂ) ^ 2 * S + (p.X : ℂ) ^ 2)) ∧
      (p.coeffs δ0).Hq (p.αd * S) = (p.V : ℂ) ^ 2 * p.ra * ((p.ra ^ 2 - p.X ^ 2) * S - p.X ^ 2) /
        (((p.ra ^ 2 + p.X ^ 2 : ℝ) : ℂ) * (((p.ra ^ 2 + p.X ^ 2 : ℝ) : ℂ) * S ^ 2 +
          2 * (p.X : ℂ) ^ 2 * S + (p.X : ℂ) ^ 2)) := by
  have hZ : p.Z = (p.ra : ℂ) + p.X * I := by simp [Z, hRf, hRg]
  have hZc : p.Zc = (p.ra : ℂ) - p.X * I := by simp [Zc, hRf, hRg]
  have hZ0 : p.Z0 = (p.X : ℂ) * I := by simp [Z0, hRf, hRg]
  have hZ0c : p.Z0c = -((p.X : ℂ) * I) := by simp [Z0c, hRf, hRg]
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hZne : p.Z ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp [Z] at this; exact hX this
  have hZcne : p.Zc ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp [Zc] at this; exact hX this
  have hprod : (p.Z * (p.αd * S) + p.αd * p.Z0) * (p.Zc * (p.αd * S) + p.αd * p.Z0c) =
      (p.αd : ℂ) ^ 2 * (((p.ra ^ 2 + p.X ^ 2 : ℝ) : ℂ) * S ^ 2 + 2 * (p.X : ℂ) ^ 2 * S +
        (p.X : ℂ) ^ 2) := by
    rw [hZ, hZc, hZ0, hZ0c]; push_cast; ring_nf; rw [I_sq]; ring
  have hα : (p.αd : ℂ) ≠ 0 := by exact_mod_cast hαd
  have hP : (p.Z * (p.αd * S) + p.αd * p.Z0) * (p.Zc * (p.αd * S) + p.αd * p.Z0c) ≠ 0 := by
    rw [hprod]; exact mul_ne_zero (pow_ne_zero _ hα) hden
  have h1 : p.Z * (p.αd * S) + p.αd * p.Z0 ≠ 0 := left_ne_zero_of_mul hP
  have h2 : p.Zc * (p.αd * S) + p.αd * p.Z0c ≠ 0 := right_ne_zero_of_mul hP
  have hN0 : ((p.ra ^ 2 + p.X ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < p.ra ^ 2 + p.X ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hN : p.Z * p.Zc = ((p.ra ^ 2 + p.X ^ 2 : ℝ) : ℂ) := by
    rw [hZ, hZc]; push_cast; ring_nf; rw [I_sq]; ring
  have hnumK : I * (p.Zc * (p.Zc * (p.αd * S) + p.αd * p.Z0c) -
      p.Z * (p.Z * (p.αd * S) + p.αd * p.Z0)) = 2 * p.αd * p.ra * p.X * (2 * S + 1) := by
    rw [hZ, hZc, hZ0, hZ0c]; ring_nf; rw [I_sq]; ring
  have hnumH : p.Zc * (p.Zc * (p.αd * S) + p.αd * p.Z0c) +
      p.Z * (p.Z * (p.αd * S) + p.αd * p.Z0) =
        2 * p.αd * ((p.ra ^ 2 - p.X ^ 2) * S - p.X ^ 2) := by
    rw [hZ, hZc, hZ0, hZ0c]; ring_nf; rw [I_sq]; ring
  generalize hw1 : p.Z * (p.αd * S) + p.αd * p.Z0 = w1 at h1 hprod hnumK hnumH
  generalize hw2 : p.Zc * (p.αd * S) + p.αd * p.Z0c = w2 at h2 hprod hnumK hnumH
  generalize hD : ((p.ra ^ 2 + p.X ^ 2 : ℝ) : ℂ) * S ^ 2 + 2 * (p.X : ℂ) ^ 2 * S +
    (p.X : ℂ) ^ 2 = den at hden hprod
  have key : (p.Z * w1) * (p.Zc * w2) = ((p.ra ^ 2 + p.X ^ 2 : ℝ) : ℂ) * (p.αd ^ 2 * den) := by
    rw [← hN, ← hprod]; ring
  refine ⟨?_, ?_⟩
  · rw [p.Kl_eq δ0 _ hRg hZne hZcne (hw1 ▸ h1) (hw2 ▸ h2), hw1, hw2]
    rw [div_sub_div _ _ (mul_ne_zero hZne h1) (mul_ne_zero hZcne h2), key]
    calc I * (p.V : ℂ) ^ 2 * p.ra * p.αd / 2 * ((1 * (p.Zc * w2) - p.Z * w1 * 1) /
          (((p.ra ^ 2 + p.X ^ 2 : ℝ) : ℂ) * (p.αd ^ 2 * den)))
        = (p.V : ℂ) ^ 2 * p.ra / (2 * p.αd * ((p.ra ^ 2 + p.X ^ 2 : ℝ) : ℂ) * den) *
            (I * (p.Zc * w2 - p.Z * w1)) := by
          field_simp
      _ = _ := by rw [hnumK]; field_simp
  · rw [p.Hq_eq δ0 _ hRg hZne hZcne (hw1 ▸ h1) (hw2 ▸ h2), hw1, hw2]
    rw [div_add_div _ _ (mul_ne_zero hZne h1) (mul_ne_zero hZcne h2), key]
    calc (p.V : ℂ) ^ 2 * p.ra * p.αd / 2 * ((1 * (p.Zc * w2) + p.Z * w1 * 1) /
          (((p.ra ^ 2 + p.X ^ 2 : ℝ) : ℂ) * (p.αd ^ 2 * den)))
        = (p.V : ℂ) ^ 2 * p.ra / (2 * p.αd * ((p.ra ^ 2 + p.X ^ 2 : ℝ) : ℂ) * den) *
            (p.Zc * w2 + p.Z * w1) := by
          field_simp
      _ = _ := by rw [hnumH]; field_simp

/-! ### The curvature of the fast power curve -/

@[tmio T, powerlib_foundation] theorem re_im_eq {a b c d : ℝ} (h : (a : ℂ) + I * (b : ℂ) = (c : ℂ) + I * (d : ℂ)) :
    a = c ∧ b = d := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero, zero_add,
    add_zero, sub_self] at h1 h2
  exact ⟨h1, h2⟩

/-- With `R_g = 0`: `P_δδ + j P_δ = −V e^{jδ} E'/Z`, `E' = E + r_a ℓ` (the EMF behind the fast
impedance). -/
@[tmio M, powerlib_domain] theorem curvature_identity (hRg : p.Rg = 0) (δ ℓ m : ℂ) :
    p.pwδδ δ ℓ m + I * p.pwδ δ ℓ m = -(p.φt δ * (p.E + p.ra * ℓ) / p.Z) := by
  have hV := p.φ_mul_φt δ
  simp only [pwδδ, pwδ, curδ, curtδ, cur, hRg]
  push_cast
  ring_nf
  rw [I_sq]
  ring

@[tmio M, powerlib_domain] theorem conj_curδ (δ : ℝ) : conj (p.curδ δ) = p.curtδ δ := by
  simp only [curδ, curtδ, map_div₀, map_mul, conj_I, conj_φ, conj_Z]

@[tmio M, powerlib_domain] theorem conj_curtδ (δ : ℝ) : conj (p.curtδ δ) = p.curδ δ := by
  rw [← p.conj_curδ, Complex.conj_conj]

@[tmio M, powerlib_domain] theorem conj_φt (δ : ℝ) : conj (p.φt δ) = p.φ δ := by rw [← p.conj_φ, Complex.conj_conj]

@[tmio M, powerlib_domain] theorem conj_curt (δ : ℝ) (ℓ : ℂ) : conj (p.curt δ (conj ℓ)) = p.cur δ ℓ := by
  rw [p.curt_real, Complex.conj_conj]

/-- `P_δ` is real on the real slice. -/
@[tmio M, powerlib_domain] theorem conj_pwδ (δ : ℝ) (ℓ : ℂ) : conj (p.pwδ δ ℓ (conj ℓ)) = p.pwδ δ ℓ (conj ℓ) := by
  have h1 : conj (p.cur δ ℓ) = p.curt δ (conj ℓ) := (p.curt_real δ ℓ).symm
  simp only [pwδ, map_add, map_mul, map_div₀, map_neg, conj_I, conj_ofReal, conj_φ, conj_φt,
    conj_curδ, conj_curtδ, conj_curt, h1, map_ofNat]
  ring

/-- `P_δδ` is real on the real slice. -/
@[tmio M, powerlib_domain] theorem conj_pwδδ (δ : ℝ) (ℓ : ℂ) : conj (p.pwδδ δ ℓ (conj ℓ)) = p.pwδδ δ ℓ (conj ℓ) := by
  have h1 : conj (p.cur δ ℓ) = p.curt δ (conj ℓ) := (p.curt_real δ ℓ).symm
  simp only [pwδδ, map_add, map_sub, map_mul, map_div₀, map_neg, conj_I, conj_ofReal, conj_φ,
    conj_φt, conj_curδ, conj_curtδ, conj_curt, h1, map_ofNat]
  ring

@[tmio M, powerlib_domain] theorem m0_real (δ : ℝ) : p.m0 δ = conj (p.ell0 δ) := by
  simp only [m0, ell0, map_div₀, map_sub, conj_ofReal, conj_φ, conj_Z0]

/-- Polar form (`R_g = 0`, any `R_f` and load): with `E' = E + r_a ℓ₀ = |E'| e^{jβ}` and
`Z = |Z| (sin α + j cos α)` (`α = arctan((R + r_a)/X)`), the fast synchronizing coefficient and
the curvature are `P_δ = (V|E'|/|Z|) cos(δ' + α)`, `P_δδ = −(V|E'|/|Z|) sin(δ' + α)`,
`δ' = δ₀ + β`. -/
@[tmio M, powerlib_domain] theorem curvature_polar (hRg : p.Rg = 0) (δ0 e β z α : ℝ) (hz : z ≠ 0)
    (hE : (p.E : ℂ) + p.ra * p.ell0 δ0 = e * exp (β * I))
    (hZp : p.Z = z * (Real.sin α + Real.cos α * I)) :
    (p.coeffs δ0).Pδ = ((p.V * e / z * Real.cos (δ0 + β + α) : ℝ) : ℂ) ∧
      (p.coeffs δ0).Pδδ = ((-(p.V * e / z * Real.sin (δ0 + β + α)) : ℝ) : ℂ) := by
  have hid := p.curvature_identity hRg δ0 (p.ell0 δ0) (p.m0 δ0)
  have hr1 := p.conj_pwδ δ0 (p.ell0 δ0)
  have hr2 := p.conj_pwδδ δ0 (p.ell0 δ0)
  rw [← p.m0_real] at hr1 hr2
  simp only [coeffs]
  rw [hE, hZp] at hid
  have hu : (Real.sin α : ℂ) + Real.cos α * I ≠ 0 := by
    intro h
    obtain ⟨h1, h2⟩ := re_im_eq (a := Real.sin α) (b := Real.cos α) (c := 0) (d := 0)
      (by rw [mul_comm I (Real.cos α : ℂ), h]; simp)
    have := Real.sin_sq_add_cos_sq α; rw [h1, h2] at this; norm_num at this
  have hinv : 1 / ((Real.sin α : ℂ) + Real.cos α * I) = (Real.sin α : ℂ) - Real.cos α * I := by
    rw [div_eq_iff hu]
    ring_nf; rw [I_sq]
    have := Real.sin_sq_add_cos_sq α
    have hc : (Real.sin α : ℂ) ^ 2 + (Real.cos α : ℂ) ^ 2 = 1 := by exact_mod_cast this
    linear_combination -hc
  have hR : -(p.φt δ0 * (e * exp (β * I)) / (z * (Real.sin α + Real.cos α * I))) =
      ((-(p.V * e / z * Real.sin (δ0 + β + α)) : ℝ) : ℂ) +
        I * ((p.V * e / z * Real.cos (δ0 + β + α) : ℝ) : ℂ) := by
    have hzc : (z : ℂ) ≠ 0 := by exact_mod_cast hz
    rw [show p.φt δ0 * (e * exp (β * I)) / (z * (Real.sin α + Real.cos α * I)) =
      p.V * e / z * (exp (δ0 * I) * exp (β * I)) *
        (1 / ((Real.sin α : ℂ) + Real.cos α * I)) by simp only [φt]; field_simp, hinv,
      ← Complex.exp_add, show (δ0 : ℂ) * I + β * I = ((δ0 + β : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    rw [Real.sin_add (δ0 + β) α, Real.cos_add (δ0 + β) α]
    push_cast
    ring_nf; rw [I_sq]; ring
  rw [hR] at hid
  set A := p.pwδ δ0 (p.ell0 δ0) (p.m0 δ0)
  set B := p.pwδδ δ0 (p.ell0 δ0) (p.m0 δ0)
  have hAre : A = (A.re : ℂ) := by
    apply Complex.ext; · simp
    · have := congrArg Complex.im hr1; simp at this; simp; linarith
  have hBre : B = (B.re : ℂ) := by
    apply Complex.ext; · simp
    · have := congrArg Complex.im hr2; simp at this; simp; linarith
  rw [hAre, hBre] at hid ⊢
  obtain ⟨h1, h2⟩ := re_im_eq hid
  exact ⟨by rw [h2], by rw [h1]⟩

end Model

/-! ## The source's `H(S)` and `F_i` -/

/-- The source's active-damping kernel function
`H(S) = −(cot α/2)[e^{j2α}/(S + cos α e^{jα}) + e^{−j2α}/(S + cos α e^{−jα})]`. -/
def Hrep (α : ℝ) (S : ℂ) : ℂ :=
  -((Real.cos α / Real.sin α : ℝ) / 2 : ℂ) *
    (exp (2 * α * I) / (S + Real.cos α * exp (α * I)) +
      exp (-(2 * α * I)) / (S + Real.cos α * exp (-(α * I))))

@[tmio T, powerlib_foundation] theorem Hrep_alg {c sn : ℝ} (hsc : c ^ 2 + sn ^ 2 = 1) (hsn : sn ≠ 0) {S : ℂ}
    (h1 : S + c * ((c : ℂ) + sn * I) ≠ 0) (h2 : S + c * ((c : ℂ) - sn * I) ≠ 0) :
    -((c / sn : ℝ) / 2 : ℂ) * (((c : ℂ) + sn * I) ^ 2 / (S + c * ((c : ℂ) + sn * I)) +
        ((c : ℂ) - sn * I) ^ 2 / (S + c * ((c : ℂ) - sn * I))) =
      -((c / sn : ℝ) : ℂ) * (((c ^ 2 - sn ^ 2 : ℝ) : ℂ) * S + (c : ℂ) ^ 2) /
        (S ^ 2 + 2 * (c : ℂ) ^ 2 * S + (c : ℂ) ^ 2) := by
  have hsc' : (c : ℂ) ^ 2 + (sn : ℂ) ^ 2 = 1 := by exact_mod_cast hsc
  have hnum : ((c : ℂ) + sn * I) ^ 2 * (S + c * ((c : ℂ) - sn * I)) +
      (S + c * ((c : ℂ) + sn * I)) * ((c : ℂ) - sn * I) ^ 2 =
        2 * (((c ^ 2 - sn ^ 2 : ℝ) : ℂ) * S + (c : ℂ) ^ 2) := by
    push_cast
    linear_combination (2 * (c : ℂ) ^ 2) * hsc' + (-2 * (sn : ℂ) ^ 2 * ((c : ℂ) ^ 2 - S)) * I_sq
  have hden : (S + c * ((c : ℂ) + sn * I)) * (S + c * ((c : ℂ) - sn * I)) =
      S ^ 2 + 2 * (c : ℂ) ^ 2 * S + (c : ℂ) ^ 2 := by
    linear_combination ((c : ℂ) ^ 2) * hsc' + (-(c : ℂ) ^ 2 * (sn : ℂ) ^ 2) * I_sq
  have hd : S ^ 2 + 2 * (c : ℂ) ^ 2 * S + (c : ℂ) ^ 2 ≠ 0 := by rw [← hden]; exact mul_ne_zero h1 h2
  rw [div_add_div _ _ h1 h2, hnum, hden]
  have hsnc : (sn : ℂ) ≠ 0 := by exact_mod_cast hsn
  push_cast
  field_simp

/-- In rational form: `H(S) = −cot α ((cos²α − sin²α) S + cos²α)/(S² + 2cos²α S + cos²α)`. -/
@[tmio T, powerlib_foundation] theorem Hrep_eq {α : ℝ} (hsn : Real.sin α ≠ 0) {S : ℂ}
    (h1 : S + Real.cos α * exp (α * I) ≠ 0) (h2 : S + Real.cos α * exp (-(α * I)) ≠ 0) :
    Hrep α S = -((Real.cos α / Real.sin α : ℝ) : ℂ) *
      (((Real.cos α ^ 2 - Real.sin α ^ 2 : ℝ) : ℂ) * S + (Real.cos α : ℂ) ^ 2) /
        (S ^ 2 + 2 * (Real.cos α : ℂ) ^ 2 * S + (Real.cos α : ℂ) ^ 2) := by
  have e1 : exp (α * I) = (Real.cos α : ℂ) + Real.sin α * I := by
    rw [Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have e2 : exp (-(α * I)) = (Real.cos α : ℂ) - Real.sin α * I := by
    rw [show -((α : ℂ) * I) = ((-α : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
      ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg]; push_cast; ring
  have e3 : exp (2 * α * I) = ((Real.cos α : ℂ) + Real.sin α * I) ^ 2 := by
    rw [← e1, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have e4 : exp (-(2 * α * I)) = ((Real.cos α : ℂ) - Real.sin α * I) ^ 2 := by
    rw [← e2, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [e1] at h1; rw [e2] at h2
  rw [Hrep, e1, e2, e3, e4]
  exact Hrep_alg (Real.cos_sq_add_sin_sq α) hsn h1 h2

/-! ## Lossless network: the closed forms of the source, exactly -/

namespace Model

variable (p : Model)

/-- `K_ℓ(α_d S) = ΔK cos²α (2S + 1)/(S² + 2cos²α S + cos²α)` with `ΔK = V² sin²α/X`, for every
load angle (`R_f = R_g = 0`, `r_a = ρ sin α`, `X = ρ cos α`). -/
@[tmio M, powerlib_domain] theorem Kl_alpha (δ0 S : ℂ) (hRf : p.Rf = 0) (hRg : p.Rg = 0) {ρ α : ℝ} (hρ : 0 < ρ)
    (hc : Real.cos α ≠ 0) (hra : p.ra = ρ * Real.sin α) (hX : p.X = ρ * Real.cos α)
    (hαd : p.αd ≠ 0)
    (hden : S ^ 2 + 2 * (Real.cos α : ℂ) ^ 2 * S + (Real.cos α : ℂ) ^ 2 ≠ 0) :
    (p.coeffs δ0).Kl (p.αd * S) = ((p.V ^ 2 * Real.sin α ^ 2 / p.X : ℝ) : ℂ) *
      ((Real.cos α : ℂ) ^ 2 * (2 * S + 1) /
        (S ^ 2 + 2 * (Real.cos α : ℂ) ^ 2 * S + (Real.cos α : ℂ) ^ 2)) := by
  have hsc := Real.sin_sq_add_cos_sq α
  have hX0 : p.X ≠ 0 := by rw [hX]; exact mul_ne_zero hρ.ne' hc
  have hXX := hX
  generalize Real.sin α = sn at *
  generalize Real.cos α = c at *
  have hN : ((p.ra ^ 2 + p.X ^ 2 : ℝ) : ℂ) = (ρ : ℂ) ^ 2 := by
    rw [hra, hXX]
    push_cast
    have h' : (sn : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast hsc
    linear_combination (ρ : ℂ) ^ 2 * h'
  have hden' : ((p.ra ^ 2 + p.X ^ 2 : ℝ) : ℂ) * S ^ 2 + 2 * (p.X : ℂ) ^ 2 * S + (p.X : ℂ) ^ 2 =
      (ρ : ℂ) ^ 2 * (S ^ 2 + 2 * (c : ℂ) ^ 2 * S + (c : ℂ) ^ 2) := by
    rw [hN, hXX]; push_cast; ring
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hd2 : ((p.ra ^ 2 + p.X ^ 2 : ℝ) : ℂ) * S ^ 2 + 2 * (p.X : ℂ) ^ 2 * S + (p.X : ℂ) ^ 2 ≠ 0 := by
    rw [hden']; exact mul_ne_zero (pow_ne_zero _ hρc) hden
  have hX0' : p.X ≠ 0 := hX0
  rw [(p.branch_lossless δ0 S hRf hRg hX0' hαd hd2).1, hden', hN, hra, hXX]
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  push_cast
  field_simp

/-- `H_q(α_d S) = ΔK H(S)`: the source's kernel function is exact, for every load angle. -/
@[tmio M, powerlib_domain] theorem Hq_alpha (δ0 S : ℂ) (hRf : p.Rf = 0) (hRg : p.Rg = 0) {ρ α : ℝ} (hρ : 0 < ρ)
    (hc : Real.cos α ≠ 0) (hsn : Real.sin α ≠ 0) (hra : p.ra = ρ * Real.sin α)
    (hX : p.X = ρ * Real.cos α) (hαd : p.αd ≠ 0)
    (h1 : S + Real.cos α * exp (α * I) ≠ 0) (h2 : S + Real.cos α * exp (-(α * I)) ≠ 0) :
    (p.coeffs δ0).Hq (p.αd * S) = ((p.V ^ 2 * Real.sin α ^ 2 / p.X : ℝ) : ℂ) * Hrep α S := by
  have hX0 : p.X ≠ 0 := by rw [hX]; exact mul_ne_zero hρ.ne' hc
  have e1 : exp (α * I) = (Real.cos α : ℂ) + Real.sin α * I := by
    rw [Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have e2 : exp (-(α * I)) = (Real.cos α : ℂ) - Real.sin α * I := by
    rw [show -((α : ℂ) * I) = ((-α : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
      ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg]; push_cast; ring
  rw [Hrep_eq hsn h1 h2]
  rw [e1] at h1; rw [e2] at h2
  have hsc := Real.cos_sq_add_sin_sq α
  have hXX := hX
  generalize Real.sin α = sn at *
  generalize Real.cos α = c at *
  have hsc' : (c : ℂ) ^ 2 + (sn : ℂ) ^ 2 = 1 := by exact_mod_cast hsc
  have hd : (S + c * ((c : ℂ) + sn * I)) * (S + c * ((c : ℂ) - sn * I)) =
      S ^ 2 + 2 * (c : ℂ) ^ 2 * S + (c : ℂ) ^ 2 := by
    linear_combination ((c : ℂ) ^ 2) * hsc' + (-(c : ℂ) ^ 2 * (sn : ℂ) ^ 2) * I_sq
  have hden : S ^ 2 + 2 * (c : ℂ) ^ 2 * S + (c : ℂ) ^ 2 ≠ 0 := by
    rw [← hd]; exact mul_ne_zero h1 h2
  have hN : ((p.ra ^ 2 + p.X ^ 2 : ℝ) : ℂ) = (ρ : ℂ) ^ 2 := by
    rw [hra, hXX]
    push_cast
    linear_combination (ρ : ℂ) ^ 2 * hsc'
  have hden' : ((p.ra ^ 2 + p.X ^ 2 : ℝ) : ℂ) * S ^ 2 + 2 * (p.X : ℂ) ^ 2 * S + (p.X : ℂ) ^ 2 =
      (ρ : ℂ) ^ 2 * (S ^ 2 + 2 * (c : ℂ) ^ 2 * S + (c : ℂ) ^ 2) := by
    rw [hN, hXX]; push_cast; ring
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hd2 : ((p.ra ^ 2 + p.X ^ 2 : ℝ) : ℂ) * S ^ 2 + 2 * (p.X : ℂ) ^ 2 * S + (p.X : ℂ) ^ 2 ≠ 0 := by
    rw [hden']; exact mul_ne_zero (pow_ne_zero _ hρc) hden
  have hX0' : p.X ≠ 0 := hX0
  rw [(p.branch_lossless δ0 S hRf hRg hX0' hαd hd2).2, hden', hN, hra, hXX]
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hsnc : (sn : ℂ) ≠ 0 := by exact_mod_cast hsn
  push_cast
  field_simp
  linear_combination (0 : ℂ) * hsc'

/-- `K(s) = P_δ + K_ℓ(s)`. -/
@[tmio M, powerlib_domain] theorem K_eq_Pδ_add_Kl (δ0 s : ℂ) : (p.coeffs δ0).K s = (p.coeffs δ0).Pδ + (p.coeffs δ0).Kl s := by
  simp only [Coeffs.K, Coeffs.Kl]; ring

@[tmio M, powerlib_domain] theorem Pδ_im (δ0 : ℝ) : ((p.coeffs δ0).Pδ).im = 0 := by
  have h := p.conj_pwδ δ0 (p.ell0 δ0)
  rw [← p.m0_real] at h
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  simp only [coeffs]; linarith

/-- (13), active-damping term, exactly: `−Im K(jΩ) = ΔK F_i(Ω/α_d, α)` with `ΔK = V² sin²α/X`,
for every load angle (`R_f = R_g = 0`). -/
@[tmio M, powerlib_domain] theorem neg_im_K (δ0 : ℝ) (x : ℝ) (hRf : p.Rf = 0) (hRg : p.Rg = 0) {ρ α : ℝ} (hρ : 0 < ρ)
    (hc : Real.cos α ≠ 0) (hra : p.ra = ρ * Real.sin α) (hX : p.X = ρ * Real.cos α)
    (hαd : p.αd ≠ 0) :
    -((p.coeffs δ0).K (((x * p.αd : ℝ) : ℂ) * I)).im =
      p.V ^ 2 * Real.sin α ^ 2 / p.X * PSCActiveDamping.branchLag x α := by
  have hsc := Real.sin_sq_add_cos_sq α
  have hpos : 0 < (Real.cos α ^ 2 - x ^ 2) ^ 2 + 4 * x ^ 2 * Real.cos α ^ 4 := by
    rcases eq_or_ne x 0 with hx | hx
    · subst hx; simp; positivity
    · have : 0 < 4 * x ^ 2 * Real.cos α ^ 4 := by positivity
      nlinarith [sq_nonneg (Real.cos α ^ 2 - x ^ 2)]
  have hden : ((x : ℂ) * I) ^ 2 + 2 * (Real.cos α : ℂ) ^ 2 * ((x : ℂ) * I) +
      (Real.cos α : ℂ) ^ 2 ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp only [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat,
      Complex.im_ofNat, Complex.zero_re, Complex.zero_im] at h1 h2
    nlinarith
  rw [p.K_eq_Pδ_add_Kl, Complex.add_im, p.Pδ_im,
    show (((x * p.αd : ℝ) : ℂ) * I) = (p.αd : ℂ) * ((x : ℂ) * I) by push_cast; ring,
    p.Kl_alpha (δ0 : ℂ) _ hRf hRg hρ hc hra hX hαd hden, PSCActiveDamping.branchLag,
    Real.sin_two_mul]
  have hX0 : p.X ≠ 0 := by rw [hX]; exact mul_ne_zero hρ.ne' hc
  generalize Real.sin α = sn at *
  generalize Real.cos α = c at *
  have hdd : (x ^ 2 + c ^ 2) ^ 2 - x ^ 2 * (2 * sn * c) ^ 2 =
      (c ^ 2 - x ^ 2) ^ 2 + 4 * x ^ 2 * c ^ 4 := by
    linear_combination (-4 * x ^ 2 * c ^ 2) * hsc
  rw [hdd]
  have hfrac : (c : ℂ) ^ 2 * (2 * ((x : ℂ) * I) + 1) /
      (((x : ℂ) * I) ^ 2 + 2 * (c : ℂ) ^ 2 * ((x : ℂ) * I) + (c : ℂ) ^ 2) =
      ((c ^ 2 : ℝ) : ℂ) * ((1 : ℝ) + ((2 * x : ℝ) : ℂ) * I) /
        (((c ^ 2 - x ^ 2 : ℝ) : ℂ) + ((2 * c ^ 2 * x : ℝ) : ℂ) * I) := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [hfrac, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add,
    Complex.div_im, Complex.normSq_add_mul_I]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
  have hn : (c ^ 2 - x ^ 2) ^ 2 + (2 * c ^ 2 * x) ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring

/-- `K_ℓ(0) = ΔK = V² sin²α/X` exactly, for every load angle (source: `ΔK ≈ V₀² sin²α/X`). -/
@[tmio M, powerlib_domain] theorem Kl_zero (δ0 : ℂ) (hRf : p.Rf = 0) (hRg : p.Rg = 0) {ρ α : ℝ} (hρ : 0 < ρ)
    (hc : Real.cos α ≠ 0) (hra : p.ra = ρ * Real.sin α) (hX : p.X = ρ * Real.cos α)
    (hαd : p.αd ≠ 0) :
    (p.coeffs δ0).Kl 0 = ((p.V ^ 2 * Real.sin α ^ 2 / p.X : ℝ) : ℂ) := by
  have hcc : (Real.cos α : ℂ) ≠ 0 := by exact_mod_cast hc
  have hden : (0 : ℂ) ^ 2 + 2 * (Real.cos α : ℂ) ^ 2 * 0 + (Real.cos α : ℂ) ^ 2 ≠ 0 := by
    simpa using pow_ne_zero 2 hcc
  have h := p.Kl_alpha δ0 0 hRf hRg hρ hc hra hX hαd hden
  rw [mul_zero] at h
  have h1 : (Real.cos α : ℂ) ^ 2 * (2 * 0 + 1) /
      (0 ^ 2 + 2 * (Real.cos α : ℂ) ^ 2 * 0 + (Real.cos α : ℂ) ^ 2) = 1 := by
    rw [div_eq_one_iff_eq hden]; ring
  rw [h, h1, mul_one]

/-- Lossless network: `P_δδ = −V E sin δ₀/X − V² r_a/(r_a² + X²)` and
`P_δ = K_hf = V E cos δ₀/X − V² r_a²/(X(r_a² + X²))`, every load angle. -/
@[tmio M, powerlib_domain] theorem curvature_lossless (δ0 : ℝ) (hRf : p.Rf = 0) (hRg : p.Rg = 0) (hX : p.X ≠ 0) :
    (p.coeffs δ0).Pδδ = ((-(p.V * p.E * Real.sin δ0 / p.X) - p.V ^ 2 * p.ra /
        (p.ra ^ 2 + p.X ^ 2) : ℝ) : ℂ) ∧
      (p.coeffs δ0).Pδ = ((p.V * p.E * Real.cos δ0 / p.X - p.V ^ 2 * p.ra ^ 2 /
        (p.X * (p.ra ^ 2 + p.X ^ 2)) : ℝ) : ℂ) := by
  have hid := p.curvature_identity hRg δ0 (p.ell0 δ0) (p.m0 δ0)
  have hr1 := p.conj_pwδ δ0 (p.ell0 δ0)
  have hr2 := p.conj_pwδδ δ0 (p.ell0 δ0)
  rw [← p.m0_real] at hr1 hr2
  simp only [coeffs]
  have hZ : p.Z = (p.ra : ℂ) + p.X * I := by simp [Z, hRf, hRg]
  have hZ0 : p.Z0 = (p.X : ℂ) * I := by simp [Z0, hRf, hRg]
  have hφ : p.φ δ0 = p.V * ((Real.cos δ0 : ℂ) - Real.sin δ0 * I) := by
    simp only [φ]; rw [PSCActiveDamping.exp_neg_mul_I]
  have hφt : p.φt δ0 = p.V * ((Real.cos δ0 : ℂ) + Real.sin δ0 * I) := by
    simp only [φt]; rw [Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hZne : (p.ra : ℂ) + p.X * I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hX this
  have hN : (0 : ℝ) < p.ra ^ 2 + p.X ^ 2 := by positivity
  have hXN : ((p.X * (p.ra ^ 2 + p.X ^ 2) : ℝ) : ℂ) ≠ 0 := by
    have : p.X * (p.ra ^ 2 + p.X ^ 2) ≠ 0 := mul_ne_zero hX hN.ne'
    exact_mod_cast this
  have hRHS1 : -(p.φt δ0 * (p.E + p.ra * p.ell0 δ0) / p.Z) =
      (((-(p.V * p.E * Real.sin δ0 * (p.ra ^ 2 + p.X ^ 2)) - p.V ^ 2 * p.ra * p.X : ℝ) : ℂ) +
        I * ((p.V * p.E * Real.cos δ0 * (p.ra ^ 2 + p.X ^ 2) - p.V ^ 2 * p.ra ^ 2 : ℝ) : ℂ)) /
        ((p.X * (p.ra ^ 2 + p.X ^ 2) : ℝ) : ℂ) := by
    have hsc := Real.cos_sq_add_sin_sq δ0
    simp only [ell0, hZ, hZ0, hφ, hφt]
    generalize Real.cos δ0 = c at *
    generalize Real.sin δ0 = sn at *
    have hsc' : (c : ℂ) ^ 2 + (sn : ℂ) ^ 2 = 1 := by exact_mod_cast hsc
    rw [show -((p.V : ℂ) * ((c : ℂ) + sn * I) * (p.E + p.ra * ((p.E - p.V * ((c : ℂ) - sn * I)) /
        (p.X * I))) / (p.ra + p.X * I)) =
        -((p.V : ℂ) * ((c : ℂ) + sn * I) * (p.E * (p.X * I) + p.ra * (p.E - p.V * ((c : ℂ) -
          sn * I)))) / ((p.X * I) * (p.ra + p.X * I)) by field_simp]
    rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero hXc I_ne_zero) hZne) hXN]
    push_cast
    linear_combination (-(p.V : ℂ) * p.X * (p.E * p.X ^ 3 * c * I + p.E * p.X ^ 2 * c * p.ra +
      p.E * p.X * c * I * p.ra ^ 2 + p.E * c * p.ra ^ 3 + p.V * p.X ^ 2 * p.ra * sn ^ 2 -
      p.V * p.X ^ 2 * p.ra - p.V * p.X * I * p.ra ^ 2 + p.V * p.ra ^ 3 * sn ^ 2 -
      p.V * p.ra ^ 3)) * I_sq + (p.V ^ 2 * p.X * p.ra * (p.X ^ 2 + p.ra ^ 2)) * hsc'
  have hRHS : -(p.φt δ0 * (p.E + p.ra * p.ell0 δ0) / p.Z) =
      ((-(p.V * p.E * Real.sin δ0 / p.X) - p.V ^ 2 * p.ra / (p.ra ^ 2 + p.X ^ 2) : ℝ) : ℂ) +
        I * ((p.V * p.E * Real.cos δ0 / p.X - p.V ^ 2 * p.ra ^ 2 /
          (p.X * (p.ra ^ 2 + p.X ^ 2)) : ℝ) : ℂ) := by
    rw [hRHS1]
    have hNc : ((p.ra ^ 2 + p.X ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    generalize Real.cos δ0 = c
    generalize Real.sin δ0 = sn
    push_cast at hXN hNc ⊢
    field_simp
  rw [hRHS] at hid
  set A := p.pwδ δ0 (p.ell0 δ0) (p.m0 δ0)
  set B := p.pwδδ δ0 (p.ell0 δ0) (p.m0 δ0)
  have hAre : A = (A.re : ℂ) := by
    apply Complex.ext; · simp
    · have := congrArg Complex.im hr1; simp at this; simp; linarith
  have hBre : B = (B.re : ℂ) := by
    apply Complex.ext; · simp
    · have := congrArg Complex.im hr2; simp at this; simp; linarith
  rw [hAre, hBre] at hid ⊢
  obtain ⟨h1, h2⟩ := re_im_eq hid
  exact ⟨by rw [h1], by rw [h2]⟩

/-- The source's `D_t` normalization: `(sin(δ₀ + 2α) + sin δ₀)/(2 cos δ₀) · K_dc
= (EV/X) cos α sin(δ₀ + α)` with `K_dc = E V cos δ₀/X`. -/
@[tmio T, powerlib_foundation] theorem reportDt_eq (E V X δ0 α : ℝ) (hc : Real.cos δ0 ≠ 0) :
    (Real.sin (δ0 + 2 * α) + Real.sin δ0) / (2 * Real.cos δ0) * (E * V * Real.cos δ0 / X) =
      E * V / X * Real.cos α * Real.sin (δ0 + α) := by
  have h : Real.sin (δ0 + 2 * α) + Real.sin δ0 = 2 * Real.cos α * Real.sin (δ0 + α) := by
    rw [show δ0 + 2 * α = (δ0 + α) + α by ring, Real.sin_add (δ0 + α) α,
      show δ0 = (δ0 + α) - α by ring, Real.sin_sub (δ0 + α) α]
    simp only [add_sub_cancel_right]
    ring
  rw [h]
  field_simp

/-- The exact curvature term against the source's `D_t` (lossless network, `E = V`): the exact
`−P_δδ` exceeds `D_t K_dc = (V²/X) cos α sin(δ₀ + α)` by `(V²/X) sin α (sin α sin δ₀ +
cos α (1 − cos δ₀))`, which is positive at load (`0 < sin δ₀`). The source's `D_t` is the exact
term with `E' = E + r_a i₀` replaced by `E` (`curvature_polar`). -/
@[tmio M, powerlib_domain] theorem curvature_vs_reportDt (δ0 : ℝ) (hRf : p.Rf = 0) (hRg : p.Rg = 0) (hE : p.E = p.V)
    {ρ α : ℝ} (hρ : 0 < ρ) (hc : Real.cos α ≠ 0) (hra : p.ra = ρ * Real.sin α)
    (hX : p.X = ρ * Real.cos α) :
    -((p.coeffs δ0).Pδδ).re - p.E * p.V / p.X * Real.cos α * Real.sin (δ0 + α) =
      p.V ^ 2 / p.X * Real.sin α * (Real.sin α * Real.sin δ0 + Real.cos α * (1 - Real.cos δ0)) := by
  have hX0 : p.X ≠ 0 := by rw [hX]; exact mul_ne_zero hρ.ne' hc
  rw [(p.curvature_lossless δ0 hRf hRg hX0).1, Complex.ofReal_re, Real.sin_add, hE]
  have hsc := Real.sin_sq_add_cos_sq α
  have hN : p.ra ^ 2 + p.X ^ 2 = ρ ^ 2 := by
    rw [hra, hX]; linear_combination ρ ^ 2 * hsc
  rw [hN]
  rw [hX] at hX0 ⊢
  rw [hra]
  generalize Real.sin α = sn at *
  generalize Real.cos α = c at *
  have hρ0 : ρ ≠ 0 := hρ.ne'
  field_simp
  linear_combination (-(p.V ^ 2 * Real.sin δ0)) * hsc

@[tmio M, powerlib_domain] theorem curvature_gt_reportDt (δ0 : ℝ) (hRf : p.Rf = 0) (hRg : p.Rg = 0) (hE : p.E = p.V)
    (hV : p.V ≠ 0) {ρ α : ℝ} (hρ : 0 < ρ) (hc : 0 < Real.cos α) (hs : 0 < Real.sin α)
    (hra : p.ra = ρ * Real.sin α) (hX : p.X = ρ * Real.cos α) (hδ : 0 < Real.sin δ0) :
    p.E * p.V / p.X * Real.cos α * Real.sin (δ0 + α) < -((p.coeffs δ0).Pδδ).re := by
  have h := p.curvature_vs_reportDt δ0 hRf hRg hE hρ hc.ne' hra hX
  have hXp : 0 < p.X := by rw [hX]; positivity
  have h1 : 0 ≤ 1 - Real.cos δ0 := by linarith [Real.cos_le_one δ0]
  have hpos : 0 < p.V ^ 2 / p.X * Real.sin α *
      (Real.sin α * Real.sin δ0 + Real.cos α * (1 - Real.cos δ0)) := by
    have : 0 < Real.sin α * Real.sin δ0 + Real.cos α * (1 - Real.cos δ0) := by positivity
    positivity
  linarith

/-- The exact damping identity of (13) for the four-state core: along a root `λ = −σ + jΩ` of
`D(λ)`, `σ/Ω = ω_f/(2Ω) + (k ω_f/Ω²) Im K(λ)/2`. -/
@[tmio M, powerlib_domain] theorem damping_eq (δ0 : ℂ) {σ Ω : ℝ} (hΩ : Ω ≠ 0)
    (hD : (p.coeffs δ0).D ((-σ : ℝ) + (Ω : ℂ) * I) = 0) :
    σ / Ω = p.ωf / (2 * Ω) +
      p.k * p.ωf / Ω ^ 2 * ((p.coeffs δ0).K ((-σ : ℝ) + (Ω : ℂ) * I)).im / 2 := by
  apply PSCActiveDamping.relDamping_eq hΩ
  have hk : (p.coeffs δ0).k = p.k := rfl
  have hω : (p.coeffs δ0).ωf = p.ωf := rfl
  simp only [Coeffs.D, hk, hω] at hD
  push_cast at hD ⊢
  linear_combination hD

/-- On the real slice the conjugate mode vector in the coordinates `(δ, p_f, ℓ, ℓ̄)` is
`r(λ̄)`: `swapConj (r(λ)) = r(λ̄)`. -/
@[tmio M, powerlib_domain] theorem swapConj_right (δ0 : ℝ) (lam : ℂ) :
    swapConj ((p.coeffs δ0).right lam) = (p.coeffs δ0).right (conj lam) := by
  have ha : conj (p.curδ δ0) = p.curtδ δ0 := p.conj_curδ δ0
  have hab : conj (p.curtδ δ0) = p.curδ δ0 := p.conj_curtδ δ0
  have hb : conj ((p.ra : ℂ) / p.Z) = p.ra / p.Zc := by
    rw [map_div₀, conj_ofReal, p.conj_Z]
  have hbb : conj ((p.ra : ℂ) / p.Zc) = p.ra / p.Z := by
    rw [← hb, Complex.conj_conj]
  funext i
  fin_cases i <;>
    simp [swapConj, Coeffs.right, Coeffs.c, Coeffs.ct, coeffs, map_div₀, map_mul, map_add,
      map_sub, map_neg, conj_ofReal, ha, hab, hb, hbb]

/-- At exact 2:1 tuning (`ω = 2 Im λ`, `R_g = 0`) the bracket is the second-order kernel of the
source at `(s₁, s₂) = (jω, λ̄)`: `G = P_δδ + H_q(s₁ + s₂) − H_q(s₁) − H_q(s₂)`. -/
@[tmio M, powerlib_domain] theorem G_tuned (δ0 : ℂ) (hRg : p.Rg = 0) (lam : ℂ) :
    (p.coeffs δ0).G (((2 * lam.im : ℝ) : ℂ) * I) (conj lam) lam =
      (p.coeffs δ0).Pδδ + ((p.coeffs δ0).Hq (((2 * lam.im : ℝ) : ℂ) * I + conj lam) -
        (p.coeffs δ0).Hq (((2 * lam.im : ℝ) : ℂ) * I) - (p.coeffs δ0).Hq (conj lam)) := by
  rw [p.G_kernel_of_Rg δ0 hRg, Coeffs.tuning]

/-- (24), exactly (lossless network, 2:1 tuning, every load angle): the bracket of the pump is
`G = P_δδ + ΔK [H(λ/α_d) − H(jω/α_d) − H(λ̄/α_d)]` with the source's `H`, `ΔK = V² sin²α/X` and
`P_δδ = −V E sin δ₀/X − V² r_a/(r_a² + X²)`. -/
@[tmio M, powerlib_domain] theorem G_lossless (δ0 : ℝ) (hRf : p.Rf = 0) (hRg : p.Rg = 0) {ρ α : ℝ} (hρ : 0 < ρ)
    (hc : Real.cos α ≠ 0) (hsn : Real.sin α ≠ 0) (hra : p.ra = ρ * Real.sin α)
    (hX : p.X = ρ * Real.cos α) (hαd : p.αd ≠ 0) (lam : ℂ)
    (hS : ∀ S ∈ ({lam / p.αd, ((2 * lam.im : ℝ) : ℂ) * I / p.αd, conj lam / p.αd} : Set ℂ),
      S + Real.cos α * exp (α * I) ≠ 0 ∧ S + Real.cos α * exp (-(α * I)) ≠ 0) :
    (p.coeffs δ0).G (((2 * lam.im : ℝ) : ℂ) * I) (conj lam) lam =
      ((-(p.V * p.E * Real.sin δ0 / p.X) - p.V ^ 2 * p.ra / (p.ra ^ 2 + p.X ^ 2) : ℝ) : ℂ) +
        ((p.V ^ 2 * Real.sin α ^ 2 / p.X : ℝ) : ℂ) *
          (Hrep α (lam / p.αd) - Hrep α (((2 * lam.im : ℝ) : ℂ) * I / p.αd) -
            Hrep α (conj lam / p.αd)) := by
  have hX0 : p.X ≠ 0 := by rw [hX]; exact mul_ne_zero hρ.ne' hc
  have hα : (p.αd : ℂ) ≠ 0 := by exact_mod_cast hαd
  have key : ∀ s : ℂ, s / p.αd ∈ ({lam / p.αd, ((2 * lam.im : ℝ) : ℂ) * I / p.αd,
      conj lam / p.αd} : Set ℂ) →
      (p.coeffs δ0).Hq s = ((p.V ^ 2 * Real.sin α ^ 2 / p.X : ℝ) : ℂ) * Hrep α (s / p.αd) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hS _ hs
    have h := p.Hq_alpha (δ0 : ℂ) (s / p.αd) hRf hRg hρ hc hsn hra hX hαd h1 h2
    rwa [mul_div_cancel₀ s hα] at h
  rw [p.G_kernel_of_Rg δ0 hRg, (p.curvature_lossless δ0 hRf hRg hX0).1,
    key lam (by simp), key _ (by simp), key _ (by simp)]
  ring

/-- The EMF behind the fast impedance (lossless network):
`E' = E + r_a i₀ = E + (r_a/X)(V sin δ₀ − j(E − V cos δ₀))`. -/
@[tmio M, powerlib_domain] theorem emf_lossless (δ0 : ℝ) (hRf : p.Rf = 0) (hRg : p.Rg = 0) (hX : p.X ≠ 0) :
    (p.E : ℂ) + p.ra * p.ell0 δ0 = ((p.E + p.ra / p.X * p.V * Real.sin δ0 : ℝ) : ℂ) -
      I * ((p.ra / p.X * (p.E - p.V * Real.cos δ0) : ℝ) : ℂ) := by
  have hZ0 : p.Z0 = (p.X : ℂ) * I := by simp [Z0, hRf, hRg]
  have hXc : (p.X : ℂ) ≠ 0 := by exact_mod_cast hX
  simp only [ell0, hZ0, φ]
  rw [PSCActiveDamping.exp_neg_mul_I]
  generalize Real.cos δ0 = c
  generalize Real.sin δ0 = sn
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

end Model

end PSCFull
end powerlib.GFM
