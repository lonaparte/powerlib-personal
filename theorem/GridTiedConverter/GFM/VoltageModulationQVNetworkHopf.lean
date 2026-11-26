import theorem.GridTiedConverter.GFM.VoltageModulationQVNetwork
import theorem.Criteria.Routh4

/-! # Dynamic Q–V loop behind a dynamic line: closed-form eigen-data and explicit conditions

`VoltageModulationQVNetwork` takes the eigenvectors of `±jΩ` of the six-state Jacobian `njac`,
the simplicity of `jΩ` and the left-half-plane condition on the other eigenvalues as hypotheses.
Here all of them are derived in closed form. Write the line current in the EMF frame
(`w = cos δ i_d + sin δ i_q`, `y = sin δ i_d − cos δ i_q`). Every eigenvector `v` of `njac` then
reduces to a null vector `(v₀, v₃, w, y)` of the `4 × 4` pencil `nM(s)`. The determinant of the
pencil is the sextic
`P(s) = (2Hs + D)s(s + ω_c)Λ(s) + ω₀ω_c N(s)`, with `Δ(s) = (Rω_b + sX)² + X²ω_b²`,
`Λ(s) = (τs + 1 + k_q q_E)Δ(s) + k_q E X ω_b²`, and `N` the network part.
So every eigenvalue is a root of `P`. Where `Δ ≠ 0` and `Λ ≠ 0`:
* the eigenspace is spanned by the explicit right eigenvector `nright`;
* the explicit left eigenvector `nleft`, normalized by `−ω₀Λ/P'`, satisfies `u r = 1`.

The sextic factors as `(s² + Ω²)` times the quartic `a₆s⁴ + a₅s³ + q₂s² + q₁s + q₀` exactly when
the two Hopf conditions `a₁ = Ω²q₁` and `a₀ = Ω²q₀` hold. Routh–Hurwitz for the quartic then gives
every other mode. The forced response at `2jΩ` is in closed form as well, `z = z_δ r(2jΩ) + σ`.
So the whole end-to-end statement rests on explicit real conditions on the parameters.

Where `Δ ≠ 0` and `Λ ≠ 0`, `P = 2HΛ F`. Here `F` is the characteristic function in the form of
`DynQV.charF`, built from the dynamic partials:
* `K_δ = p_δ + E²B(s)` and `K_E = p_E + E G(s)`;
* `M_δ = q_δ − E²G(s)` and `M_E = q_E + E B(s)`;
* `G = R'/(R'² + X²)` and `B = X/(R'² + X²)`, with `R' = R + sX/ω_b`.

At `s = 0`, and in the limit `ω_b → ∞` for every `s`, these partials are the quasi-static partials
of `lossyP` and `lossyQ`. In that limit `F` tends to the characteristic function of `lossyCore`,
and `P/ω_b²` tends to `2H(R² + X²)` times its quartic.

Model boundary.
* The field `nfield` of `VoltageModulationQVNetwork`. The algebra is at any state `x`; the
  end-to-end statements are at the operating point `nxeq`.
* Explicit conditions:
  * `ω₀ ≠ 0` and `a₆ = 2HτX² > 0`;
  * `Δ(jΩ) ≠ 0` (automatic when `R ≠ 0`, `nΔ_ne`) and `Λ(jΩ) ≠ 0`;
  * the two Hopf conditions, and Routh–Hurwitz for the quotient quartic;
  * for the closed-form forced response, also `Δ(2jΩ) ≠ 0` and `Λ(2jΩ) ≠ 0`.
* The limit `ω_b → ∞` is stated for fixed `s`, for four quantities:
  * the dynamic partials;
  * the characteristic function, where the quasi-static `τs + b ≠ 0`;
  * the `ΔE` component of the right eigenvector;
  * the sextic over `ω_b²`.

  Convergence of individual roots, of the pump and of the Floquet multipliers is not stated.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2, §5 (network dynamics and sidebands). The dynamic Q–V loop with
a dynamic line and the voltage excitation are new.

Results.
* `npδ`, `npE`, `nqδ`, `nqE`, `nρ`, `nΔ`, `nT`, `nΛ`, `nN`, `ncharP`, `ncharPd`: the sextic.
* `nr3`, `nw`, `ny`, `nright`, `nright_eig`: the right eigenvector.
* `nu3`, `nψ`, `nφ`, `nlv`, `nleft`, `nlv_eig`, `nleft_eig`, `nlv_nright`, `nleft_nright`: the
  left eigenvector and the normalization `u r = 1`.
* `nM`, `nred`, `nM_det`, `neig_reduce`, `neig_charP`, `neig_span`: the reduction to the pencil;
  every eigenvalue is a root of `P`, and the eigenspace is spanned by `nright`.
* The coefficients and the factorization:
  * `nl2`, `nl1`, `nl0`, `nn2`, `nn1`, `nn0`, `na6`, …, `na0`, `nq2`, `nq1`, `nq0`;
  * `ncharP_eq`, `ncharPd_eq`, `hasDerivAt_ncharP`;
  * `ncharP_factor`, `ncharPd_hopf`.
* `nquartic_re_neg`, `neig_stable`, `nhopf_facts`, `nspectral`: Routh–Hurwitz, the other modes
  and the full spectral data.
* `orbit_net_hopf_stable`, `orbit_net_hopf_unstable`, `orbit_net_hopf_exp_stable`, `nΔ_ne`:
  end-to-end with explicit conditions.
* `nσ3`, `nσw`, `nσy`, `nzδ`, `nzc`, `nzc_eq`, `nz_closed`: the forced response in closed form.
* `nG`, `nB`, `nKδ`, `nKE`, `nMδ`, `nME`, `nchar`, `nlag_eq`, `nchar_eq`: the dynamic partials and
  `P = 2HΛF`.
* `nstatic`, `ndyn_zero`, `nΔ_tendsto`, `ndyn_tendsto`, `nchar_tendsto`, `nr3_tendsto`,
  `ncharP_tendsto`: the quasi-static identities and the limit `ω_b → ∞`.

Corrections.
None: an extension (removes the spectral hypotheses of `VoltageModulationQVNetwork`).

Family and connection conclusions.
None: static evidence on the voltage-modulated dynamic Q–V core with a dynamic line.
-/

noncomputable section
namespace powerlib.GFM
namespace VoltageModulation
namespace DynQV
open Complex Matrix Filter Topology
open powerlib.ParametricResonance
open powerlib.ParametricResonance.ForcedOrbit (smJ)

variable (c : DynQV) (R X ωb : ℝ)

/-! ### Sensitivities at fixed current and the characteristic polynomial -/

/-- `∂P/∂δ` at fixed line current, `E(−sin δ i_d + cos δ i_q)`. -/
def npδ (x : Fin 6 → ℝ) : ℝ := x 3 * (-Real.sin (x 0) * x 4 + Real.cos (x 0) * x 5)
/-- `∂P/∂E` at fixed line current. -/
def npE (x : Fin 6 → ℝ) : ℝ := Real.cos (x 0) * x 4 + Real.sin (x 0) * x 5
/-- `∂Q/∂δ` at fixed line current. -/
def nqδ (x : Fin 6 → ℝ) : ℝ := x 3 * (Real.cos (x 0) * x 4 + Real.sin (x 0) * x 5)
/-- `∂Q/∂E` at fixed line current. -/
def nqE (x : Fin 6 → ℝ) : ℝ := Real.sin (x 0) * x 4 - Real.cos (x 0) * x 5

/-- `ω_b (R + sX/ω_b)`. -/
def nρ (s : ℂ) : ℂ := R * ωb + s * X
/-- `ω_b² ((R + sX/ω_b)² + X²)`. -/
def nΔ (s : ℂ) : ℂ := nρ R X ωb s ^ 2 + X ^ 2 * ωb ^ 2
/-- `τ s + 1 + k_q Q_E`. -/
def nT (x : Fin 6 → ℝ) (s : ℂ) : ℂ := c.τ * s + 1 + c.kq * nqE x
/-- `T Δ + k_q E X ω_b²`. -/
def nΛ (x : Fin 6 → ℝ) (s : ℂ) : ℂ := c.nT x s * nΔ R X ωb s + c.kq * x 3 * X * ωb ^ 2
/-- The network part of the characteristic polynomial. -/
def nN (x : Fin 6 → ℝ) (s : ℂ) : ℂ :=
  (npδ x * c.nT x s - c.kq * npE x * nqδ x) * nΔ R X ωb s + x 3 ^ 2 * X * ωb ^ 2 * c.nT x s +
    c.kq * x 3 * (x 3 * npE x - nqδ x) * ωb * nρ R X ωb s +
    c.kq * x 3 * (npδ x * X + x 3 ^ 2) * ωb ^ 2
/-- The sextic whose roots contain every eigenvalue of the six-state Jacobian (`neig_charP`),
leading coefficient `a₆ = 2HτX²`. -/
def ncharP (x : Fin 6 → ℝ) (s : ℂ) : ℂ :=
  (2 * c.H * s + c.D) * s * (s + c.ωc) * c.nΛ R X ωb x s + c.ω0 * c.ωc * c.nN R X ωb x s

/-- Its derivative. -/
def ncharPd (x : Fin 6 → ℝ) (s : ℂ) : ℂ :=
  (2 * c.H * s * (s + c.ωc) + (2 * c.H * s + c.D) * (2 * s + c.ωc)) * c.nΛ R X ωb x s +
    (2 * c.H * s + c.D) * s * (s + c.ωc) *
      (c.τ * nΔ R X ωb s + c.nT x s * (2 * X * nρ R X ωb s)) +
    c.ω0 * c.ωc * (npδ x * c.τ * nΔ R X ωb s +
      (npδ x * c.nT x s - c.kq * npE x * nqδ x) * (2 * X * nρ R X ωb s) +
      x 3 ^ 2 * X * ωb ^ 2 * c.τ + c.kq * x 3 * (x 3 * npE x - nqδ x) * ωb * X)

/-! ### Right and left eigenvectors -/

/-- The `ΔE` component of the right eigenvector. -/
def nr3 (x : Fin 6 → ℝ) (s : ℂ) : ℂ :=
  -(c.kq * (nqδ x * nΔ R X ωb s - x 3 ^ 2 * ωb * nρ R X ωb s)) / c.nΛ R X ωb x s
/-- The current perturbation along the EMF. -/
def nw (x : Fin 6 → ℝ) (s : ℂ) : ℂ :=
  ωb * (nρ R X ωb s * c.nr3 R X ωb x s + X * x 3 * ωb) / nΔ R X ωb s
/-- The current perturbation in quadrature to the EMF. -/
def ny (x : Fin 6 → ℝ) (s : ℂ) : ℂ :=
  ωb * (X * ωb * c.nr3 R X ωb x s - nρ R X ωb s * x 3) / nΔ R X ωb s

/-- The right eigenvector. -/
def nright (x : Fin 6 → ℝ) (s : ℂ) : Fin 6 → ℂ :=
  ![1, s / c.ω0, -(2 * c.H * s + c.D) * s / c.ω0, c.nr3 R X ωb x s,
    Real.cos (x 0) * c.nw R X ωb x s + Real.sin (x 0) * c.ny R X ωb x s,
    Real.sin (x 0) * c.nw R X ωb x s - Real.cos (x 0) * c.ny R X ωb x s]

/-- Off the characteristic polynomial `nright` fails to be an eigenvector only in the `Δω`-row
of the filter: `A r = s r + P(s)/(ω₀Λ(s)) e₂`. -/
@[tmio M, powerlib_domain] theorem nright_res (x : Fin 6 → ℝ) (V : ℝ) {s : ℂ} (hX : X ≠ 0)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : c.τ ≠ 0) (hΔ : nΔ R X ωb s ≠ 0)
    (hΛ : c.nΛ R X ωb x s ≠ 0) :
    (c.njac R X ωb (x, V)).map (algebraMap ℝ ℂ) *ᵥ c.nright R X ωb x s =
      s • c.nright R X ωb x s +
        (c.ncharP R X ωb x s / (c.ω0 * c.nΛ R X ωb x s)) • ![0, 0, 1, 0, 0, 0] := by
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  have hτc : (c.τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  have htr := Complex.cos_sq_add_sin_sq ((x 0 : ℝ) : ℂ)
  funext i
  fin_cases i
  · simp [njac, nright, mulVec, dotProduct, Fin.sum_univ_six]
    field_simp
  · simp [njac, nright, mulVec, dotProduct, Fin.sum_univ_six]
    field_simp
    ring
  · simp [njac, nright, mulVec, dotProduct, Fin.sum_univ_six]
    linear_combination (norm := skip) (c.ωc * x 3 * c.nw R X ωb x s) * htr
    simp only [nw, ny, nr3]
    field_simp
    simp only [ncharP, nN, nΛ, nΔ, nT, nρ, npδ, npE, nqδ, nqE]
    push_cast
    ring
  · simp [njac, nright, mulVec, dotProduct, Fin.sum_univ_six]
    linear_combination (norm := skip) (-(c.kq * x 3 * c.ny R X ωb x s / c.τ)) * htr
    simp only [nw, ny, nr3]
    field_simp
    simp only [nΛ, nΔ, nT, nρ, nqδ, nqE]
    push_cast
    ring
  · simp [njac, nright, mulVec, dotProduct, Fin.sum_univ_six]
    simp only [nw, ny, nr3]
    field_simp
    simp only [nΛ, nΔ, nT, nρ, nqδ, nqE]
    push_cast
    ring
  · simp [njac, nright, mulVec, dotProduct, Fin.sum_univ_six]
    simp only [nw, ny, nr3]
    field_simp
    simp only [nΛ, nΔ, nT, nρ, nqδ, nqE]
    push_cast
    ring

@[tmio M, powerlib_domain] theorem nright_eig (x : Fin 6 → ℝ) (V : ℝ) {s : ℂ} (hX : X ≠ 0)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : c.τ ≠ 0) (hΔ : nΔ R X ωb s ≠ 0)
    (hΛ : c.nΛ R X ωb x s ≠ 0) (hP : c.ncharP R X ωb x s = 0) :
    (c.njac R X ωb (x, V)).map (algebraMap ℝ ℂ) *ᵥ c.nright R X ωb x s =
      s • c.nright R X ωb x s := by
  rw [c.nright_res R X ωb x V hX hω0 hH hτ hΔ hΛ, hP, zero_div, zero_smul, add_zero]

/-- The unnormalized left eigenvector (`u₂ = 1`): `ΔE` part. -/
def nu3 (x : Fin 6 → ℝ) (s : ℂ) : ℂ :=
  c.τ * c.ωc * (npE x * nΔ R X ωb s + x 3 * ωb * nρ R X ωb s) / c.nΛ R X ωb x s
/-- Line part along the EMF. -/
def nψ (x : Fin 6 → ℝ) (s : ℂ) : ℂ :=
  X * (nρ R X ωb s * (c.ωc * x 3) - X * ωb * (c.kq * x 3 / c.τ * c.nu3 R X ωb x s)) /
    nΔ R X ωb s
/-- Line part in quadrature. -/
def nφ (x : Fin 6 → ℝ) (s : ℂ) : ℂ :=
  X * (X * ωb * (c.ωc * x 3) + nρ R X ωb s * (c.kq * x 3 / c.τ * c.nu3 R X ωb x s)) /
    nΔ R X ωb s

/-- The unnormalized left eigenvector. -/
def nlv (x : Fin 6 → ℝ) (s : ℂ) : Fin 6 → ℂ :=
  ![-(s + c.ωc) * (2 * c.H * s + c.D) / c.ω0, -(2 * c.H * (s + c.ωc)), 1, c.nu3 R X ωb x s,
    Real.cos (x 0) * c.nψ R X ωb x s - Real.sin (x 0) * c.nφ R X ωb x s,
    Real.sin (x 0) * c.nψ R X ωb x s + Real.cos (x 0) * c.nφ R X ωb x s]

/-- The left eigenvector, normalized by `u r = 1`. -/
def nleft (x : Fin 6 → ℝ) (s : ℂ) : Fin 6 → ℂ :=
  (-(c.ω0 : ℂ) * c.nΛ R X ωb x s / c.ncharPd R X ωb x s) • c.nlv R X ωb x s

@[tmio M, powerlib_domain] theorem nlv_eig (x : Fin 6 → ℝ) (V : ℝ) {s : ℂ} (hX : X ≠ 0)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : c.τ ≠ 0) (hΔ : nΔ R X ωb s ≠ 0)
    (hΛ : c.nΛ R X ωb x s ≠ 0) (hP : c.ncharP R X ωb x s = 0) :
    c.nlv R X ωb x s ᵥ* (c.njac R X ωb (x, V)).map (algebraMap ℝ ℂ) = s • c.nlv R X ωb x s := by
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  have hτc : (c.τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  have htr := Complex.cos_sq_add_sin_sq ((x 0 : ℝ) : ℂ)
  funext j
  fin_cases j
  · simp [njac, nlv, vecMul, dotProduct, Fin.sum_univ_six]
    linear_combination (norm := skip) (1 / (c.ω0 * c.nΛ R X ωb x s)) * hP +
      (ωb / X * x 3 * c.nφ R X ωb x s) * htr
    simp only [nψ, nφ, nu3]
    field_simp
    simp only [ncharP, nN, nΛ, nΔ, nT, nρ, npδ, npE, nqδ, nqE]
    push_cast
    ring
  · simp [njac, nlv, vecMul, dotProduct, Fin.sum_univ_six]
    field_simp
    ring
  · simp [njac, nlv, vecMul, dotProduct, Fin.sum_univ_six]
    field_simp
    ring
  · simp [njac, nlv, vecMul, dotProduct, Fin.sum_univ_six]
    linear_combination (norm := skip) (ωb / X * c.nψ R X ωb x s) * htr
    simp only [nψ, nφ, nu3]
    field_simp
    simp only [nΛ, nΔ, nT, nρ, npE, nqE]
    push_cast
    ring
  · simp [njac, nlv, vecMul, dotProduct, Fin.sum_univ_six]
    simp only [nψ, nφ, nu3]
    field_simp
    simp only [nΛ, nΔ, nT, nρ, npE, nqE]
    push_cast
    ring
  · simp [njac, nlv, vecMul, dotProduct, Fin.sum_univ_six]
    simp only [nψ, nφ, nu3]
    field_simp
    simp only [nΛ, nΔ, nT, nρ, npE, nqE]
    push_cast
    ring

@[tmio M, powerlib_domain] theorem nleft_eig (x : Fin 6 → ℝ) (V : ℝ) {s : ℂ} (hX : X ≠ 0)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : c.τ ≠ 0) (hΔ : nΔ R X ωb s ≠ 0)
    (hΛ : c.nΛ R X ωb x s ≠ 0) (hP : c.ncharP R X ωb x s = 0) :
    c.nleft R X ωb x s ᵥ* (c.njac R X ωb (x, V)).map (algebraMap ℝ ℂ) =
      s • c.nleft R X ωb x s := by
  rw [nleft, Matrix.smul_vecMul, c.nlv_eig R X ωb x V hX hω0 hH hτ hΔ hΛ hP, smul_comm]

@[tmio M, powerlib_domain] theorem nlv_nright (x : Fin 6 → ℝ) {s : ℂ} (hω0 : c.ω0 ≠ 0)
    (hH : c.H ≠ 0) (hτ : c.τ ≠ 0) (hΔ : nΔ R X ωb s ≠ 0) (hΛ : c.nΛ R X ωb x s ≠ 0)
    (hP : c.ncharP R X ωb x s = 0) :
    c.nlv R X ωb x s ⬝ᵥ c.nright R X ωb x s =
      -(c.ncharPd R X ωb x s) / (c.ω0 * c.nΛ R X ωb x s) := by
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  have hτc : (c.τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  have htr := Complex.cos_sq_add_sin_sq ((x 0 : ℝ) : ℂ)
  simp [nlv, nright, dotProduct, Fin.sum_univ_six]
  linear_combination (norm := skip)
    ((c.τ * nΔ R X ωb s + c.nT x s * (2 * X * nρ R X ωb s)) /
      (c.ω0 * c.nΛ R X ωb x s ^ 2)) * hP +
    (c.nψ R X ωb x s * c.nw R X ωb x s - c.nφ R X ωb x s * c.ny R X ωb x s) * htr
  simp only [nψ, nφ, nu3, nw, ny, nr3]
  field_simp
  simp only [ncharP, ncharPd, nN, nΛ, nΔ, nT, nρ, npδ, npE, nqδ, nqE]
  push_cast
  ring

@[tmio M, powerlib_domain] theorem nleft_nright (x : Fin 6 → ℝ) {s : ℂ} (hω0 : c.ω0 ≠ 0)
    (hH : c.H ≠ 0) (hτ : c.τ ≠ 0) (hΔ : nΔ R X ωb s ≠ 0) (hΛ : c.nΛ R X ωb x s ≠ 0)
    (hP : c.ncharP R X ωb x s = 0) (hd : c.ncharPd R X ωb x s ≠ 0) :
    c.nleft R X ωb x s ⬝ᵥ c.nright R X ωb x s = 1 := by
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  rw [nleft, smul_dotProduct, c.nlv_nright R X ωb x hω0 hH hτ hΔ hΛ hP, smul_eq_mul]
  field_simp

/-! ### Reduction to a 4 × 4 pencil -/

/-- The reduced pencil on `(v₀, v₃, w, y)`, `w`, `y` the current in the EMF frame. -/
def nM (x : Fin 6 → ℝ) (s : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(2 * c.H * s + c.D) * s * (s + c.ωc) + c.ω0 * c.ωc * npδ x, c.ω0 * c.ωc * npE x,
      c.ω0 * c.ωc * x 3, 0;
    c.kq * nqδ x, c.nT x s, 0, c.kq * x 3;
    0, -(ωb : ℂ), nρ R X ωb s, ωb * X;
    ωb * x 3, 0, -(ωb * X : ℂ), nρ R X ωb s]

/-- The reduced coordinates of a state vector. -/
def nred (x : Fin 6 → ℝ) (v : Fin 6 → ℂ) : Fin 4 → ℂ :=
  ![v 0, v 3, Real.cos (x 0) * v 4 + Real.sin (x 0) * v 5,
    Real.sin (x 0) * v 4 - Real.cos (x 0) * v 5]

@[tmio M, powerlib_domain] theorem nM_det (x : Fin 6 → ℝ) (s : ℂ) :
    (c.nM R X ωb x s).det = c.ncharP R X ωb x s := by
  have a1 : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = 3 := rfl
  have a2 : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 := rfl
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, nM, Matrix.submatrix, a1, a2]
  simp only [ncharP, nN, nΛ, nΔ]
  ring

/-- An eigenvector of the six-state Jacobian reduces to a null vector of the pencil. -/
@[tmio M, powerlib_domain] theorem neig_reduce (x : Fin 6 → ℝ) (V : ℝ) {μ : ℂ}
    {v : Fin 6 → ℂ} (hX : X ≠ 0) (hH : c.H ≠ 0) (hτ : c.τ ≠ 0)
    (he : (c.njac R X ωb (x, V)).map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    c.ω0 * v 1 = μ * v 0 ∧ v 2 = -(2 * c.H * μ + c.D) * v 1 ∧
      c.nM R X ωb x μ *ᵥ nred x v = 0 := by
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  have hτc : (c.τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  have htr := Complex.cos_sq_add_sin_sq ((x 0 : ℝ) : ℂ)
  have e : ∀ i, ((c.njac R X ωb (x, V)).map (algebraMap ℝ ℂ) *ᵥ v) i = μ * v i := fun i => by
    rw [he]; rfl
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  have e3 := e 3
  have e4 := e 4
  have e5 := e 5
  simp [njac, mulVec, dotProduct, Fin.sum_univ_six] at e0 e1 e2 e3 e4 e5
  have h1 : v 2 = -(2 * c.H * μ + c.D) * v 1 := by
    field_simp at e1
    linear_combination -e1
  refine ⟨by linear_combination e0, h1, ?_⟩
  funext i
  fin_cases i
  · simp [nM, nred, mulVec, dotProduct, Fin.sum_univ_four]
    rw [h1] at e2
    linear_combination (norm := skip) c.ω0 * e2 - (c.ωc + μ) * (2 * c.H * μ + c.D) * e0
    simp only [npδ, npE]
    push_cast
    ring
  · simp [nM, nred, mulVec, dotProduct, Fin.sum_univ_four]
    linear_combination (norm := skip) (-(c.τ : ℂ)) * e3
    field_simp
    simp only [nT, nqδ, nqE]
    push_cast
    ring
  · simp [nM, nred, mulVec, dotProduct, Fin.sum_univ_four]
    linear_combination (norm := skip) (-(X : ℂ) * Complex.cos (x 0)) * e4 +
      (-(X : ℂ) * Complex.sin (x 0)) * e5 + (ωb * v 3) * htr
    field_simp
    simp only [nρ]
    ring
  · simp [nM, nred, mulVec, dotProduct, Fin.sum_univ_four]
    linear_combination (norm := skip) (-(X : ℂ) * Complex.sin (x 0)) * e4 +
      ((X : ℂ) * Complex.cos (x 0)) * e5 + (-(ωb * x 3 * v 0)) * htr
    field_simp
    simp only [nρ]
    ring

/-- Every eigenvalue of the six-state Jacobian is a root of `ncharP`. -/
@[tmio M, powerlib_domain] theorem neig_charP (x : Fin 6 → ℝ) (V : ℝ) {μ : ℂ}
    {v : Fin 6 → ℂ} (hX : X ≠ 0) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : c.τ ≠ 0)
    (hv : v ≠ 0) (he : (c.njac R X ωb (x, V)).map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    c.ncharP R X ωb x μ = 0 := by
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have htr := Complex.cos_sq_add_sin_sq ((x 0 : ℝ) : ℂ)
  obtain ⟨e0, e1, hM⟩ := c.neig_reduce R X ωb x V hX hH hτ he
  rw [← c.nM_det]
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, fun h0 => hv ?_, hM⟩
  have h0' : v 0 = 0 := by simpa [nred] using congrFun h0 0
  have h3 : v 3 = 0 := by simpa [nred] using congrFun h0 1
  have hw : Complex.cos (x 0) * v 4 + Complex.sin (x 0) * v 5 = 0 := by
    simpa [nred] using congrFun h0 2
  have hy : Complex.sin (x 0) * v 4 - Complex.cos (x 0) * v 5 = 0 := by
    simpa [nred] using congrFun h0 3
  have hv1 : v 1 = 0 := by
    rw [h0', mul_zero] at e0
    exact (mul_eq_zero.1 e0).resolve_left hω
  funext i
  fin_cases i
  · exact h0'
  · exact hv1
  · simp [e1, hv1]
  · exact h3
  · show v 4 = 0
    linear_combination Complex.cos (x 0) * hw + Complex.sin (x 0) * hy - v 4 * htr
  · show v 5 = 0
    linear_combination Complex.sin (x 0) * hw - Complex.cos (x 0) * hy - v 5 * htr

/-- Where `Δ`, `Λ` do not vanish, the eigenspace is spanned by `nright`. -/
@[tmio M, powerlib_domain] theorem neig_span (x : Fin 6 → ℝ) (V : ℝ) {s : ℂ}
    {v : Fin 6 → ℂ} (hX : X ≠ 0) (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : c.τ ≠ 0)
    (hΔ : nΔ R X ωb s ≠ 0) (hΛ : c.nΛ R X ωb x s ≠ 0)
    (he : (c.njac R X ωb (x, V)).map (algebraMap ℝ ℂ) *ᵥ v = s • v) :
    v = v 0 • c.nright R X ωb x s := by
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have htr := Complex.cos_sq_add_sin_sq ((x 0 : ℝ) : ℂ)
  obtain ⟨e0, e1, hM⟩ := c.neig_reduce R X ωb x V hX hH hτ he
  have hb := congrFun hM 1
  have hc := congrFun hM 2
  have hd := congrFun hM 3
  simp [nM, nred, mulVec, dotProduct, Fin.sum_univ_four] at hb hc hd
  have k3 : c.nΛ R X ωb x s * v 3 =
      -(c.kq * (nqδ x * nΔ R X ωb s - x 3 ^ 2 * ωb * nρ R X ωb s)) * v 0 := by
    linear_combination (norm := skip) nΔ R X ωb s * hb -
      c.kq * x 3 * ωb * X * hc - c.kq * x 3 * nρ R X ωb s * hd
    simp only [nΛ, nΔ]
    ring
  have hv3 : v 3 = v 0 * c.nr3 R X ωb x s := by
    simp only [nr3]
    field_simp
    linear_combination k3
  have kw : nΔ R X ωb s * (Complex.cos (x 0) * v 4 + Complex.sin (x 0) * v 5) =
      ωb * (nρ R X ωb s * v 3 + X * x 3 * ωb * v 0) := by
    linear_combination (norm := skip) nρ R X ωb s * hc - ωb * X * hd
    simp only [nΔ]
    ring
  have ky : nΔ R X ωb s * (Complex.sin (x 0) * v 4 - Complex.cos (x 0) * v 5) =
      ωb * (X * ωb * v 3 - nρ R X ωb s * x 3 * v 0) := by
    linear_combination (norm := skip) ωb * X * hc + nρ R X ωb s * hd
    simp only [nΔ]
    ring
  have hw : Complex.cos (x 0) * v 4 + Complex.sin (x 0) * v 5 = v 0 * c.nw R X ωb x s := by
    simp only [nw]
    rw [hv3] at kw
    field_simp
    linear_combination kw
  have hy : Complex.sin (x 0) * v 4 - Complex.cos (x 0) * v 5 = v 0 * c.ny R X ωb x s := by
    simp only [ny]
    rw [hv3] at ky
    field_simp
    linear_combination ky
  funext i
  fin_cases i
  · simp [nright]
  · simp [nright]
    field_simp
    linear_combination e0
  · simp [nright]
    rw [e1]
    field_simp
    linear_combination (-(2 * c.H * s + c.D)) * e0
  · simp [nright, hv3]
  · simp [nright]
    linear_combination Complex.cos (x 0) * hw + Complex.sin (x 0) * hy - v 4 * htr
  · simp [nright]
    linear_combination Complex.sin (x 0) * hw - Complex.cos (x 0) * hy - v 5 * htr

/-! ### Coefficients, Hopf factorization and Routh–Hurwitz -/

/-- `s²` coefficient of `Λ`. -/
def nl2 (x : Fin 6 → ℝ) : ℝ := c.τ * (2 * R * ωb * X) + (1 + c.kq * nqE x) * X ^ 2
/-- `s` coefficient of `Λ`. -/
def nl1 (x : Fin 6 → ℝ) : ℝ :=
  c.τ * ((R ^ 2 + X ^ 2) * ωb ^ 2) + (1 + c.kq * nqE x) * (2 * R * ωb * X)
/-- Constant coefficient of `Λ`. -/
def nl0 (x : Fin 6 → ℝ) : ℝ :=
  (1 + c.kq * nqE x) * ((R ^ 2 + X ^ 2) * ωb ^ 2) + c.kq * x 3 * X * ωb ^ 2
/-- `s²` coefficient of `N`. -/
def nn2 (x : Fin 6 → ℝ) : ℝ :=
  npδ x * c.τ * (2 * R * ωb * X) + (npδ x * (1 + c.kq * nqE x) - c.kq * npE x * nqδ x) * X ^ 2
/-- `s` coefficient of `N`. -/
def nn1 (x : Fin 6 → ℝ) : ℝ :=
  npδ x * c.τ * ((R ^ 2 + X ^ 2) * ωb ^ 2) +
    (npδ x * (1 + c.kq * nqE x) - c.kq * npE x * nqδ x) * (2 * R * ωb * X) +
    x 3 ^ 2 * X * ωb ^ 2 * c.τ + c.kq * x 3 * (x 3 * npE x - nqδ x) * ωb * X
/-- Constant coefficient of `N`. -/
def nn0 (x : Fin 6 → ℝ) : ℝ :=
  (npδ x * (1 + c.kq * nqE x) - c.kq * npE x * nqδ x) * ((R ^ 2 + X ^ 2) * ωb ^ 2) +
    x 3 ^ 2 * X * ωb ^ 2 * (1 + c.kq * nqE x) + c.kq * x 3 * (x 3 * npE x - nqδ x) * ωb ^ 2 * R +
    c.kq * x 3 * (npδ x * X + x 3 ^ 2) * ωb ^ 2

/-- `s⁶` coefficient of `ncharP`. -/
def na6 : ℝ := 2 * c.H * (c.τ * X ^ 2)
/-- `s⁵` coefficient. -/
def na5 (x : Fin 6 → ℝ) : ℝ := 2 * c.H * c.nl2 R X ωb x + (c.D + 2 * c.H * c.ωc) * (c.τ * X ^ 2)
/-- `s⁴` coefficient. -/
def na4 (x : Fin 6 → ℝ) : ℝ :=
  2 * c.H * c.nl1 R X ωb x + (c.D + 2 * c.H * c.ωc) * c.nl2 R X ωb x + c.D * c.ωc * (c.τ * X ^ 2)
/-- `s³` coefficient. -/
def na3 (x : Fin 6 → ℝ) : ℝ :=
  2 * c.H * c.nl0 R X ωb x + (c.D + 2 * c.H * c.ωc) * c.nl1 R X ωb x +
    c.D * c.ωc * c.nl2 R X ωb x + c.ω0 * c.ωc * (npδ x * c.τ * X ^ 2)
/-- `s²` coefficient. -/
def na2 (x : Fin 6 → ℝ) : ℝ :=
  (c.D + 2 * c.H * c.ωc) * c.nl0 R X ωb x + c.D * c.ωc * c.nl1 R X ωb x +
    c.ω0 * c.ωc * c.nn2 R X ωb x
/-- `s` coefficient. -/
def na1 (x : Fin 6 → ℝ) : ℝ := c.D * c.ωc * c.nl0 R X ωb x + c.ω0 * c.ωc * c.nn1 R X ωb x
/-- Constant coefficient. -/
def na0 (x : Fin 6 → ℝ) : ℝ := c.ω0 * c.ωc * c.nn0 R X ωb x

/-- The quotient by `s² + Ω²`: `s²` coefficient. -/
def nq2 (x : Fin 6 → ℝ) (Ω : ℝ) : ℝ := c.na4 R X ωb x - Ω ^ 2 * c.na6 X
/-- `s` coefficient. -/
def nq1 (x : Fin 6 → ℝ) (Ω : ℝ) : ℝ := c.na3 R X ωb x - Ω ^ 2 * c.na5 R X ωb x
/-- Constant coefficient. -/
def nq0 (x : Fin 6 → ℝ) (Ω : ℝ) : ℝ := c.na2 R X ωb x - Ω ^ 2 * c.nq2 R X ωb x Ω

@[tmio M, powerlib_domain] theorem ncharP_eq (x : Fin 6 → ℝ) (s : ℂ) :
    c.ncharP R X ωb x s = c.na6 X * s ^ 6 + c.na5 R X ωb x * s ^ 5 + c.na4 R X ωb x * s ^ 4 +
      c.na3 R X ωb x * s ^ 3 + c.na2 R X ωb x * s ^ 2 + c.na1 R X ωb x * s + c.na0 R X ωb x := by
  simp only [ncharP, nN, nΛ, nΔ, nT, nρ, na6, na5, na4, na3, na2, na1, na0, nl2, nl1, nl0, nn2,
    nn1, nn0]
  push_cast
  ring

@[tmio M, powerlib_domain] theorem ncharPd_eq (x : Fin 6 → ℝ) (s : ℂ) :
    c.ncharPd R X ωb x s = 6 * c.na6 X * s ^ 5 + 5 * c.na5 R X ωb x * s ^ 4 +
      4 * c.na4 R X ωb x * s ^ 3 + 3 * c.na3 R X ωb x * s ^ 2 + 2 * c.na2 R X ωb x * s +
      c.na1 R X ωb x := by
  simp only [ncharPd, nΛ, nΔ, nT, nρ, na6, na5, na4, na3, na2, na1, nl2, nl1, nl0, nn2, nn1]
  push_cast
  ring

@[tmio M, powerlib_domain] theorem hasDerivAt_ncharP (x : Fin 6 → ℝ) (s : ℂ) :
    HasDerivAt (c.ncharP R X ωb x) (c.ncharPd R X ωb x s) s := by
  have e : c.ncharP R X ωb x = fun s => (c.na6 X : ℂ) * s ^ 6 + c.na5 R X ωb x * s ^ 5 +
      c.na4 R X ωb x * s ^ 4 + c.na3 R X ωb x * s ^ 3 + c.na2 R X ωb x * s ^ 2 +
      c.na1 R X ωb x * s + c.na0 R X ωb x := funext (c.ncharP_eq R X ωb x)
  rw [e, c.ncharPd_eq R X ωb x s]
  have d6 := (hasDerivAt_pow 6 s).const_mul (c.na6 X : ℂ)
  have d5 := (hasDerivAt_pow 5 s).const_mul (c.na5 R X ωb x : ℂ)
  have d4 := (hasDerivAt_pow 4 s).const_mul (c.na4 R X ωb x : ℂ)
  have d3 := (hasDerivAt_pow 3 s).const_mul (c.na3 R X ωb x : ℂ)
  have d2 := (hasDerivAt_pow 2 s).const_mul (c.na2 R X ωb x : ℂ)
  have d1 := (hasDerivAt_id' s).const_mul (c.na1 R X ωb x : ℂ)
  have h := (((((d6.add d5).add d4).add d3).add d2).add d1).add_const (c.na0 R X ωb x : ℂ)
  convert h using 1
  norm_num
  ring

/-- Under the two Hopf conditions the characteristic polynomial has the factor `s² + Ω²`. -/
@[tmio M, powerlib_domain] theorem ncharP_factor (x : Fin 6 → ℝ) {Ω : ℝ}
    (hA : c.na1 R X ωb x = Ω ^ 2 * c.nq1 R X ωb x Ω)
    (hB : c.na0 R X ωb x = Ω ^ 2 * c.nq0 R X ωb x Ω) (s : ℂ) :
    c.ncharP R X ωb x s = (s ^ 2 + Ω ^ 2) * (c.na6 X * s ^ 4 + c.na5 R X ωb x * s ^ 3 +
      c.nq2 R X ωb x Ω * s ^ 2 + c.nq1 R X ωb x Ω * s + c.nq0 R X ωb x Ω) := by
  have hA' := congrArg (fun t : ℝ => (t : ℂ)) hA
  have hB' := congrArg (fun t : ℝ => (t : ℂ)) hB
  rw [c.ncharP_eq]
  simp only [nq2, nq1, nq0] at hA' hB' ⊢
  push_cast at hA' hB' ⊢
  linear_combination s * hA' + hB'

/-- The derivative at `jΩ` under the Hopf conditions: `2jΩ` times the quotient. -/
@[tmio M, powerlib_domain] theorem ncharPd_hopf (x : Fin 6 → ℝ) {Ω : ℝ}
    (hA : c.na1 R X ωb x = Ω ^ 2 * c.nq1 R X ωb x Ω) :
    c.ncharPd R X ωb x (Ω * I) = 2 * (Ω * I) * (c.na6 X * (Ω * I) ^ 4 +
      c.na5 R X ωb x * (Ω * I) ^ 3 + c.nq2 R X ωb x Ω * (Ω * I) ^ 2 +
      c.nq1 R X ωb x Ω * (Ω * I) + c.nq0 R X ωb x Ω) := by
  have hA' := congrArg (fun t : ℝ => (t : ℂ)) hA
  rw [c.ncharPd_eq]
  simp only [nq2, nq1, nq0] at hA' ⊢
  push_cast at hA' ⊢
  linear_combination hA' + ((Ω : ℂ) ^ 2 * (4 * c.na6 X * (Ω * I) ^ 3 +
    3 * c.na5 R X ωb x * (Ω * I) ^ 2 + 2 * (c.na4 R X ωb x - Ω ^ 2 * c.na6 X) * (Ω * I) +
    (c.na3 R X ωb x - Ω ^ 2 * c.na5 R X ωb x))) * Complex.I_sq

/-- Routh–Hurwitz for the quotient quartic. -/
@[tmio M, powerlib_domain] theorem nquartic_re_neg (x : Fin 6 → ℝ) {Ω : ℝ} (h6 : 0 < c.na6 X)
    (h5 : 0 < c.na5 R X ωb x) (h1 : 0 < c.nq1 R X ωb x Ω) (h0 : 0 < c.nq0 R X ωb x Ω)
    (hg : c.na6 X * c.nq1 R X ωb x Ω ^ 2 + c.na5 R X ωb x ^ 2 * c.nq0 R X ωb x Ω <
      c.na5 R X ωb x * c.nq2 R X ωb x Ω * c.nq1 R X ωb x Ω) {μ : ℂ}
    (hμ : (c.na6 X : ℂ) * μ ^ 4 + c.na5 R X ωb x * μ ^ 3 + c.nq2 R X ωb x Ω * μ ^ 2 +
      c.nq1 R X ωb x Ω * μ + c.nq0 R X ωb x Ω = 0) : μ.re < 0 := by
  have ha : (c.na6 X : ℂ) ≠ 0 := by exact_mod_cast h6.ne'
  refine Criteria.quartic_roots_re_neg_of (a2 := c.nq2 R X ωb x Ω / c.na6 X) (div_pos h5 h6)
    (div_pos h1 h6) (div_pos h0 h6) ?_ μ ?_
  · have key : c.na5 R X ωb x / c.na6 X * (c.nq2 R X ωb x Ω / c.na6 X) *
        (c.nq1 R X ωb x Ω / c.na6 X) - ((c.nq1 R X ωb x Ω / c.na6 X) ^ 2 +
        (c.na5 R X ωb x / c.na6 X) ^ 2 * (c.nq0 R X ωb x Ω / c.na6 X)) =
        (c.na5 R X ωb x * c.nq2 R X ωb x Ω * c.nq1 R X ωb x Ω -
          (c.na6 X * c.nq1 R X ωb x Ω ^ 2 + c.na5 R X ωb x ^ 2 * c.nq0 R X ωb x Ω)) /
          c.na6 X ^ 3 := by
      field_simp
    have : 0 < (c.na5 R X ωb x * c.nq2 R X ωb x Ω * c.nq1 R X ωb x Ω -
        (c.na6 X * c.nq1 R X ωb x Ω ^ 2 + c.na5 R X ωb x ^ 2 * c.nq0 R X ωb x Ω)) /
        c.na6 X ^ 3 := div_pos (by linarith) (pow_pos h6 3)
    linarith
  · push_cast
    field_simp
    linear_combination hμ

/-- Under the Hopf and Routh–Hurwitz conditions every eigenvalue of the six-state Jacobian other
than `±jΩ` lies in the open left half plane. -/
@[tmio M, powerlib_domain] theorem neig_stable (x : Fin 6 → ℝ) (V : ℝ) {Ω : ℝ}
    (hω0 : c.ω0 ≠ 0) (hA : c.na1 R X ωb x = Ω ^ 2 * c.nq1 R X ωb x Ω)
    (hB : c.na0 R X ωb x = Ω ^ 2 * c.nq0 R X ωb x Ω) (h6 : 0 < c.na6 X)
    (h5 : 0 < c.na5 R X ωb x) (h1 : 0 < c.nq1 R X ωb x Ω) (h0 : 0 < c.nq0 R X ωb x Ω)
    (hg : c.na6 X * c.nq1 R X ωb x Ω ^ 2 + c.na5 R X ωb x ^ 2 * c.nq0 R X ωb x Ω <
      c.na5 R X ωb x * c.nq2 R X ωb x Ω * c.nq1 R X ωb x Ω)
    (μ : ℂ) (v : Fin 6 → ℂ) (hv : v ≠ 0)
    (he : (c.njac R X ωb (x, V)).map (algebraMap ℝ ℂ) *ᵥ v = μ • v)
    (hμ1 : μ ≠ Ω * I) (hμ2 : μ ≠ -(Ω * I)) : μ.re < 0 := by
  have hne : 2 * c.H * (c.τ * X ^ 2) ≠ 0 := h6.ne'
  have hH : c.H ≠ 0 := fun h => hne (by simp [h])
  have hτ : c.τ ≠ 0 := fun h => hne (by simp [h])
  have hX : X ≠ 0 := fun h => hne (by simp [h])
  have hP := c.neig_charP R X ωb x V hX hω0 hH hτ hv he
  rw [c.ncharP_factor R X ωb x hA hB] at hP
  rcases mul_eq_zero.1 hP with h | h
  · exfalso
    have h' : (μ - Ω * I) * (μ + Ω * I) = 0 := by
      linear_combination h - (Ω : ℂ) ^ 2 * Complex.I_sq
    rcases mul_eq_zero.1 h' with h'' | h''
    · exact hμ1 (sub_eq_zero.1 h'')
    · exact hμ2 (eq_neg_of_add_eq_zero_left h'')
  · exact c.nquartic_re_neg R X ωb x h6 h5 h1 h0 hg h

/-- The Hopf facts: `jΩ` is a simple root of the characteristic polynomial. -/
@[tmio M, powerlib_domain] theorem nhopf_facts (x : Fin 6 → ℝ) {Ω : ℝ} (hΩ : Ω ≠ 0)
    (hA : c.na1 R X ωb x = Ω ^ 2 * c.nq1 R X ωb x Ω)
    (hB : c.na0 R X ωb x = Ω ^ 2 * c.nq0 R X ωb x Ω) (h6 : 0 < c.na6 X)
    (h5 : 0 < c.na5 R X ωb x) (h1 : 0 < c.nq1 R X ωb x Ω) (h0 : 0 < c.nq0 R X ωb x Ω)
    (hg : c.na6 X * c.nq1 R X ωb x Ω ^ 2 + c.na5 R X ωb x ^ 2 * c.nq0 R X ωb x Ω <
      c.na5 R X ωb x * c.nq2 R X ωb x Ω * c.nq1 R X ωb x Ω) :
    c.ncharP R X ωb x (Ω * I) = 0 ∧ c.ncharPd R X ωb x (Ω * I) ≠ 0 := by
  constructor
  · rw [c.ncharP_factor R X ωb x hA hB]
    have : (Ω * I) ^ 2 + (Ω : ℂ) ^ 2 = 0 := by linear_combination (Ω : ℂ) ^ 2 * Complex.I_sq
    rw [this, zero_mul]
  · rw [c.ncharPd_hopf R X ωb x hA]
    have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
    refine mul_ne_zero (mul_ne_zero two_ne_zero (mul_ne_zero hΩc I_ne_zero)) ?_
    intro hq
    have := c.nquartic_re_neg R X ωb x h6 h5 h1 h0 hg hq
    simp at this

/-! ### Spectral data and end-to-end statements -/

/-- The spectral data of the six-state network Jacobian at any state `x`, from the explicit
Hopf and Routh–Hurwitz conditions: `nright`, `nleft` are the eigenvectors of `jΩ` with
`u r = 1`, the eigenspace is spanned by `nright`, and every other eigenvalue has negative real
part. -/
@[tmio M, powerlib_domain] theorem nspectral (x : Fin 6 → ℝ) (V : ℝ) {Ω : ℝ} (hΩ : Ω ≠ 0)
    (hω0 : c.ω0 ≠ 0) (hΔ : nΔ R X ωb (Ω * I) ≠ 0) (hΛ : c.nΛ R X ωb x (Ω * I) ≠ 0)
    (hA : c.na1 R X ωb x = Ω ^ 2 * c.nq1 R X ωb x Ω)
    (hB : c.na0 R X ωb x = Ω ^ 2 * c.nq0 R X ωb x Ω) (h6 : 0 < c.na6 X)
    (h5 : 0 < c.na5 R X ωb x) (h1 : 0 < c.nq1 R X ωb x Ω) (h0 : 0 < c.nq0 R X ωb x Ω)
    (hg : c.na6 X * c.nq1 R X ωb x Ω ^ 2 + c.na5 R X ωb x ^ 2 * c.nq0 R X ωb x Ω <
      c.na5 R X ωb x * c.nq2 R X ωb x Ω * c.nq1 R X ωb x Ω) :
    (c.njac R X ωb (x, V)).map (algebraMap ℝ ℂ) *ᵥ c.nright R X ωb x (Ω * I) =
        ((Ω : ℂ) * I) • c.nright R X ωb x (Ω * I) ∧
      c.nleft R X ωb x (Ω * I) ᵥ* (c.njac R X ωb (x, V)).map (algebraMap ℝ ℂ) =
        ((Ω : ℂ) * I) • c.nleft R X ωb x (Ω * I) ∧
      c.nleft R X ωb x (Ω * I) ⬝ᵥ c.nright R X ωb x (Ω * I) = 1 ∧
      (∀ v : Fin 6 → ℂ, (c.njac R X ωb (x, V)).map (algebraMap ℝ ℂ) *ᵥ v = ((Ω : ℂ) * I) • v →
        v = (c.nleft R X ωb x (Ω * I) ⬝ᵥ v) • c.nright R X ωb x (Ω * I)) ∧
      ∀ (μ : ℂ) (v : Fin 6 → ℂ), v ≠ 0 →
        (c.njac R X ωb (x, V)).map (algebraMap ℝ ℂ) *ᵥ v = μ • v →
        μ ≠ (Ω : ℂ) * I → μ ≠ -((Ω : ℂ) * I) → μ.re < 0 := by
  have hne : 2 * c.H * (c.τ * X ^ 2) ≠ 0 := h6.ne'
  have hH : c.H ≠ 0 := fun h => hne (by simp [h])
  have hτ : c.τ ≠ 0 := fun h => hne (by simp [h])
  have hX : X ≠ 0 := fun h => hne (by simp [h])
  obtain ⟨hP, hd⟩ := c.nhopf_facts R X ωb x hΩ hA hB h6 h5 h1 h0 hg
  have hur := c.nleft_nright R X ωb x hω0 hH hτ hΔ hΛ hP hd
  refine ⟨c.nright_eig R X ωb x V hX hω0 hH hτ hΔ hΛ hP,
    c.nleft_eig R X ωb x V hX hω0 hH hτ hΔ hΛ hP, hur, fun v hv => ?_,
    fun μ v hv he h1' h2' => c.neig_stable R X ωb x V hω0 hA hB h6 h5 h1 h0 hg μ v hv he h1' h2'⟩
  obtain ⟨a, ha⟩ : ∃ a : ℂ, v = a • c.nright R X ωb x (Ω * I) :=
    ⟨_, c.neig_span R X ωb x V hX hω0 hH hτ hΔ hΛ hv⟩
  subst ha
  rw [dotProduct_smul, hur, smul_eq_mul, mul_one]

/-- The synchronizing core with a dynamic Q–V loop behind a dynamic `R + jX` line, grid-voltage
modulation, end-to-end, stability, with explicit conditions: the two Hopf conditions
`a₁ = Ω² q₁`, `a₀ = Ω² q₀` on the sextic, Routh–Hurwitz for the quotient quartic, `Δ(jΩ) ≠ 0`,
`Λ(jΩ) ≠ 0`, and the eigenvectors `nright`, `nleft` in closed form. -/
@[tmio M, powerlib_domain] theorem orbit_net_hopf_stable {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω)
    (hω0 : c.ω0 ≠ 0) (hΔ : nΔ R X ωb (Ω * I) ≠ 0)
    (hΛ : c.nΛ R X ωb (nxeq R X δ0 E0 V0) (Ω * I) ≠ 0)
    (hA : c.na1 R X ωb (nxeq R X δ0 E0 V0) = Ω ^ 2 * c.nq1 R X ωb (nxeq R X δ0 E0 V0) Ω)
    (hB : c.na0 R X ωb (nxeq R X δ0 E0 V0) = Ω ^ 2 * c.nq0 R X ωb (nxeq R X δ0 E0 V0) Ω)
    (h6 : 0 < c.na6 X) (h5 : 0 < c.na5 R X ωb (nxeq R X δ0 E0 V0))
    (h1 : 0 < c.nq1 R X ωb (nxeq R X δ0 E0 V0) Ω) (h0 : 0 < c.nq0 R X ωb (nxeq R X δ0 E0 V0) Ω)
    (hg : c.na6 X * c.nq1 R X ωb (nxeq R X δ0 E0 V0) Ω ^ 2 +
        c.na5 R X ωb (nxeq R X δ0 E0 V0) ^ 2 * c.nq0 R X ωb (nxeq R X δ0 E0 V0) Ω <
      c.na5 R X ωb (nxeq R X δ0 E0 V0) * c.nq2 R X ωb (nxeq R X δ0 E0 V0) Ω *
        c.nq1 R X ωb (nxeq R X δ0 E0 V0) Ω)
    (Vh : ℝ) (A0' : Matrix (Fin 6) (Fin 6) ℝ)
    (hs : (c.nleft R X ωb (nxeq R X δ0 E0 V0) (Ω * I) ⬝ᵥ
      (A0'.map (algebraMap ℝ ℂ) *ᵥ c.nright R X ωb (nxeq R X δ0 E0 V0) (Ω * I))).re < 0)
    (hgv : ‖c.nleft R X ωb (nxeq R X δ0 E0 V0) (Ω * I) ⬝ᵥ
        (c.nA1 X ωb (nxeq R X δ0 E0 V0) (c.nz R X ωb δ0 E0 V0 Ω Vh) *ᵥ
          star (c.nright R X ωb (nxeq R X δ0 E0 V0) (Ω * I))) / 2‖ ^ 2 <
      ‖c.nleft R X ωb (nxeq R X δ0 E0 V0) (Ω * I) ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ c.nright R X ωb (nxeq R X δ0 E0 V0) (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 6 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0
          (lossyQ R X ((δ0, E0), V0)) (nxeq R X δ0 E0 V0 + y t,
            V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 6 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0
          (lossyQ R X ((δ0, E0), V0)) (nxeq R X δ0 E0 V0 + y t,
            V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 6 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => smJ (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0
            (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) Vh (2 * Ω) A0' ε t
            (y t)) (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  have hX : X ≠ 0 := fun h => h6.ne' (by simp [na6, h])
  obtain ⟨hr, hu, hur, hsimple, hstab⟩ :=
    c.nspectral R X ωb (nxeq R X δ0 E0 V0) V0 hΩ.ne' hω0 hΔ hΛ hA hB h6 h5 h1 h0 hg
  exact c.orbit_net_stable R X ωb (by positivity) hΩ hr hu hur hsimple hstab Vh A0' hs hgv

/-- The dynamic-network core, end-to-end, parametric instability, with explicit conditions. -/
@[tmio M, powerlib_domain] theorem orbit_net_hopf_unstable {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω)
    (hω0 : c.ω0 ≠ 0) (hΔ : nΔ R X ωb (Ω * I) ≠ 0)
    (hΛ : c.nΛ R X ωb (nxeq R X δ0 E0 V0) (Ω * I) ≠ 0)
    (hA : c.na1 R X ωb (nxeq R X δ0 E0 V0) = Ω ^ 2 * c.nq1 R X ωb (nxeq R X δ0 E0 V0) Ω)
    (hB : c.na0 R X ωb (nxeq R X δ0 E0 V0) = Ω ^ 2 * c.nq0 R X ωb (nxeq R X δ0 E0 V0) Ω)
    (h6 : 0 < c.na6 X) (h5 : 0 < c.na5 R X ωb (nxeq R X δ0 E0 V0))
    (h1 : 0 < c.nq1 R X ωb (nxeq R X δ0 E0 V0) Ω) (h0 : 0 < c.nq0 R X ωb (nxeq R X δ0 E0 V0) Ω)
    (hg : c.na6 X * c.nq1 R X ωb (nxeq R X δ0 E0 V0) Ω ^ 2 +
        c.na5 R X ωb (nxeq R X δ0 E0 V0) ^ 2 * c.nq0 R X ωb (nxeq R X δ0 E0 V0) Ω <
      c.na5 R X ωb (nxeq R X δ0 E0 V0) * c.nq2 R X ωb (nxeq R X δ0 E0 V0) Ω *
        c.nq1 R X ωb (nxeq R X δ0 E0 V0) Ω)
    (Vh : ℝ) (A0' : Matrix (Fin 6) (Fin 6) ℝ)
    (hgv : ‖c.nleft R X ωb (nxeq R X δ0 E0 V0) (Ω * I) ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ c.nright R X ωb (nxeq R X δ0 E0 V0) (Ω * I))‖ ^ 2 <
      ‖c.nleft R X ωb (nxeq R X δ0 E0 V0) (Ω * I) ⬝ᵥ
        (c.nA1 X ωb (nxeq R X δ0 E0 V0) (c.nz R X ωb δ0 E0 V0 Ω Vh) *ᵥ
          star (c.nright R X ωb (nxeq R X δ0 E0 V0) (Ω * I))) / 2‖ ^ 2) :
    ∃ k, 0 ≤ k ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 6 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
        ∀ t, HasDerivAt y (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0
          (lossyQ R X ((δ0, E0), V0)) (nxeq R X δ0 E0 V0 + y t,
            V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 6 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ k * ε) →
        (∀ t, HasDerivAt y (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0
          (lossyQ R X ((δ0, E0), V0)) (nxeq R X δ0 E0 V0 + y t,
            V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJ (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0
          (lossyQ R X ((δ0, E0), V0))) (nxeq R X δ0 E0 V0, V0) Vh (2 * Ω) A0' ε t
          (y t)) (2 * Real.pi / (2 * Ω)) := by
  have hX : X ≠ 0 := fun h => h6.ne' (by simp [na6, h])
  obtain ⟨hr, hu, hur, hsimple, hstab⟩ :=
    c.nspectral R X ωb (nxeq R X δ0 E0 V0) V0 hΩ.ne' hω0 hΔ hΛ hA hB h6 h5 h1 h0 hg
  exact c.orbit_net_unstable R X ωb (by positivity) hΩ hr hu hur hsimple hstab Vh A0' hgv

/-- The dynamic-network core with explicit conditions: the forced orbit exists and is locally
exponentially stable for the nonlinear driven system. -/
@[tmio M, powerlib_domain] theorem orbit_net_hopf_exp_stable {δ0 E0 V0 Ω : ℝ} (hΩ : 0 < Ω)
    (hω0 : c.ω0 ≠ 0) (hΔ : nΔ R X ωb (Ω * I) ≠ 0)
    (hΛ : c.nΛ R X ωb (nxeq R X δ0 E0 V0) (Ω * I) ≠ 0)
    (hA : c.na1 R X ωb (nxeq R X δ0 E0 V0) = Ω ^ 2 * c.nq1 R X ωb (nxeq R X δ0 E0 V0) Ω)
    (hB : c.na0 R X ωb (nxeq R X δ0 E0 V0) = Ω ^ 2 * c.nq0 R X ωb (nxeq R X δ0 E0 V0) Ω)
    (h6 : 0 < c.na6 X) (h5 : 0 < c.na5 R X ωb (nxeq R X δ0 E0 V0))
    (h1 : 0 < c.nq1 R X ωb (nxeq R X δ0 E0 V0) Ω) (h0 : 0 < c.nq0 R X ωb (nxeq R X δ0 E0 V0) Ω)
    (hg : c.na6 X * c.nq1 R X ωb (nxeq R X δ0 E0 V0) Ω ^ 2 +
        c.na5 R X ωb (nxeq R X δ0 E0 V0) ^ 2 * c.nq0 R X ωb (nxeq R X δ0 E0 V0) Ω <
      c.na5 R X ωb (nxeq R X δ0 E0 V0) * c.nq2 R X ωb (nxeq R X δ0 E0 V0) Ω *
        c.nq1 R X ωb (nxeq R X δ0 E0 V0) Ω)
    (Vh : ℝ) (A0' : Matrix (Fin 6) (Fin 6) ℝ)
    (hs : (c.nleft R X ωb (nxeq R X δ0 E0 V0) (Ω * I) ⬝ᵥ
      (A0'.map (algebraMap ℝ ℂ) *ᵥ c.nright R X ωb (nxeq R X δ0 E0 V0) (Ω * I))).re < 0)
    (hgv : ‖c.nleft R X ωb (nxeq R X δ0 E0 V0) (Ω * I) ⬝ᵥ
        (c.nA1 X ωb (nxeq R X δ0 E0 V0) (c.nz R X ωb δ0 E0 V0 Ω Vh) *ᵥ
          star (c.nright R X ωb (nxeq R X δ0 E0 V0) (Ω * I))) / 2‖ ^ 2 <
      ‖c.nleft R X ωb (nxeq R X δ0 E0 V0) (Ω * I) ⬝ᵥ
        (A0'.map (algebraMap ℝ ℂ) *ᵥ c.nright R X ωb (nxeq R X δ0 E0 V0) (Ω * I))‖ ^ 2) :
    ∃ k, 0 ≤ k ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 6 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ k * ε) ∧
      (∀ t, HasDerivAt y (c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0
        (lossyQ R X ((δ0, E0), V0)) (nxeq R X δ0 E0 V0 + y t,
          V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 6 → ℝ),
        IsIntegralCurveOn x (fun t v => c.nfield R X ωb (lossyP R X ((δ0, E0), V0)) E0
          (lossyQ R X ((δ0, E0), V0)) (nxeq R X δ0 E0 V0 + v,
            V0 + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ v)) (Set.Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  have hX : X ≠ 0 := fun h => h6.ne' (by simp [na6, h])
  obtain ⟨hr, hu, hur, hsimple, hstab⟩ :=
    c.nspectral R X ωb (nxeq R X δ0 E0 V0) V0 hΩ.ne' hω0 hΔ hΛ hA hB h6 h5 h1 h0 hg
  exact c.orbit_net_exp_stable R X ωb (by positivity) hΩ hr hu hur hsimple hstab Vh A0' hs hgv

/-- `Δ(jΩ) ≠ 0` as soon as the line has resistance. -/
@[tmio M, powerlib_domain] theorem nΔ_ne {Ω : ℝ} (hR : R ≠ 0) (hX : X ≠ 0) (hωb : ωb ≠ 0)
    (hΩ : Ω ≠ 0) : nΔ R X ωb (Ω * I) ≠ 0 := by
  have him : (nΔ R X ωb (Ω * I)).im = 2 * R * ωb * Ω * X := by
    simp [nΔ, nρ, pow_two, Complex.mul_im, Complex.mul_re]
    ring
  intro h
  rw [h, Complex.zero_im] at him
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hR) hωb) hΩ) hX him.symm

/-! ### The forced response in closed form -/

/-- The line-driven part of the response to `V̂` at `s`: `ΔE` component. -/
def nσ3 (x : Fin 6 → ℝ) (s : ℂ) (Vh : ℝ) : ℂ :=
  c.kq * x 3 * ωb * Vh * (ωb * X * Real.cos (x 0) + nρ R X ωb s * Real.sin (x 0)) /
    c.nΛ R X ωb x s
/-- Its current along the EMF. -/
def nσw (x : Fin 6 → ℝ) (s : ℂ) (Vh : ℝ) : ℂ :=
  ωb * (nρ R X ωb s * c.nσ3 R X ωb x s Vh - nρ R X ωb s * Vh * Real.cos (x 0) +
    ωb * X * Vh * Real.sin (x 0)) / nΔ R X ωb s
/-- Its current in quadrature. -/
def nσy (x : Fin 6 → ℝ) (s : ℂ) (Vh : ℝ) : ℂ :=
  ωb * (ωb * X * c.nσ3 R X ωb x s Vh - ωb * X * Vh * Real.cos (x 0) -
    nρ R X ωb s * Vh * Real.sin (x 0)) / nΔ R X ωb s
/-- The angle response `z_δ = −ω₀ω_c (p_E σ₃ + E σ_w) Λ / P(s)`. -/
def nzδ (x : Fin 6 → ℝ) (s : ℂ) (Vh : ℝ) : ℂ :=
  -(c.ω0 * c.ωc * (npE x * c.nσ3 R X ωb x s Vh + x 3 * c.nσw R X ωb x s Vh)) *
    c.nΛ R X ωb x s / c.ncharP R X ωb x s
/-- The line-driven part `σ` of the forced response. -/
def nσv (x : Fin 6 → ℝ) (s : ℂ) (Vh : ℝ) : Fin 6 → ℂ :=
  ![0, 0, 0, c.nσ3 R X ωb x s Vh,
    Real.cos (x 0) * c.nσw R X ωb x s Vh + Real.sin (x 0) * c.nσy R X ωb x s Vh,
    Real.sin (x 0) * c.nσw R X ωb x s Vh - Real.cos (x 0) * c.nσy R X ωb x s Vh]

/-- The forced response `z = z_δ r(s) + σ`. -/
def nzc (x : Fin 6 → ℝ) (s : ℂ) (Vh : ℝ) : Fin 6 → ℂ :=
  c.nzδ R X ωb x s Vh • c.nright R X ωb x s + c.nσv R X ωb x s Vh

/-- `σ` absorbs the voltage input except in the `Δω`-row of the filter:
`A σ = s σ + ω_c(p_E σ₃ + E σ_w) e₂ − V̂ B_V`. -/
@[tmio M, powerlib_domain] theorem nσv_res (x : Fin 6 → ℝ) (V : ℝ) {s : ℂ} (hX : X ≠ 0)
    (hτ : c.τ ≠ 0) (hΔ : nΔ R X ωb s ≠ 0) (hΛ : c.nΛ R X ωb x s ≠ 0) (Vh : ℝ) :
    (c.njac R X ωb (x, V)).map (algebraMap ℝ ℂ) *ᵥ c.nσv R X ωb x s Vh =
      s • c.nσv R X ωb x s Vh +
        (c.ωc * (npE x * c.nσ3 R X ωb x s Vh + x 3 * c.nσw R X ωb x s Vh)) •
          ![0, 0, 1, 0, 0, 0] - (Vh : ℂ) • Bnet X ωb := by
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX
  have hτc : (c.τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  have htr := Complex.cos_sq_add_sin_sq ((x 0 : ℝ) : ℂ)
  funext i
  fin_cases i
  · simp [njac, nσv, Bnet, mulVec, dotProduct, Fin.sum_univ_six]
  · simp [njac, nσv, Bnet, mulVec, dotProduct, Fin.sum_univ_six]
  · simp [njac, nσv, Bnet, mulVec, dotProduct, Fin.sum_univ_six]
    linear_combination (norm := skip) (c.ωc * x 3 * c.nσw R X ωb x s Vh) * htr
    simp only [npE]
    push_cast
    ring
  · simp [njac, nσv, Bnet, mulVec, dotProduct, Fin.sum_univ_six]
    linear_combination (norm := skip) (-(c.kq * x 3 * c.nσy R X ωb x s Vh / c.τ)) * htr
    simp only [nσw, nσy, nσ3]
    field_simp
    simp only [nΛ, nΔ, nT, nρ, nqE]
    push_cast
    ring
  · simp [njac, nσv, Bnet, mulVec, dotProduct, Fin.sum_univ_six]
    linear_combination (norm := skip) (ωb / X * Vh) * htr
    simp only [nσw, nσy, nσ3]
    field_simp
    simp only [nΛ, nΔ, nT, nρ, nqE]
    push_cast
    ring
  · simp [njac, nσv, Bnet, mulVec, dotProduct, Fin.sum_univ_six]
    simp only [nσw, nσy, nσ3]
    field_simp
    simp only [nΛ, nΔ, nT, nρ, nqE]
    push_cast
    ring

@[tmio M, powerlib_domain] theorem nzc_eq (x : Fin 6 → ℝ) (V : ℝ) {s : ℂ} (hX : X ≠ 0)
    (hω0 : c.ω0 ≠ 0) (hH : c.H ≠ 0) (hτ : c.τ ≠ 0) (hΔ : nΔ R X ωb s ≠ 0)
    (hΛ : c.nΛ R X ωb x s ≠ 0) (hP : c.ncharP R X ωb x s ≠ 0) (Vh : ℝ) :
    s • c.nzc R X ωb x s Vh - (c.njac R X ωb (x, V)).map (algebraMap ℝ ℂ) *ᵥ
      c.nzc R X ωb x s Vh = (Vh : ℂ) • Bnet X ωb := by
  have hω : (c.ω0 : ℂ) ≠ 0 := by exact_mod_cast hω0
  have key : c.nzδ R X ωb x s Vh * (c.ncharP R X ωb x s / (c.ω0 * c.nΛ R X ωb x s)) +
      c.ωc * (npE x * c.nσ3 R X ωb x s Vh + x 3 * c.nσw R X ωb x s Vh) = 0 := by
    simp only [nzδ]
    field_simp
    ring
  rw [nzc, Matrix.mulVec_add, Matrix.mulVec_smul, c.nright_res R X ωb x V hX hω0 hH hτ hΔ hΛ,
    c.nσv_res R X ωb x V hX hτ hΔ hΛ Vh]
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-((![0, 0, 1, 0, 0, 0] : Fin 6 → ℂ) i)) * key

/-- Under the explicit Hopf and Routh–Hurwitz conditions and `Δ(2jΩ) ≠ 0`, `Λ(2jΩ) ≠ 0`, the
forced response `nz` of the network core is the closed form `nzc` at `2jΩ`; in particular the
pump `g_V = u A₁(z) r̄` is explicit. -/
@[tmio M, powerlib_domain] theorem nz_closed {δ0 E0 V0 Ω : ℝ} (hΩ : Ω ≠ 0) (hω0 : c.ω0 ≠ 0)
    (hΔ2 : nΔ R X ωb (((2 * Ω : ℝ) : ℂ) * I) ≠ 0)
    (hΛ2 : c.nΛ R X ωb (nxeq R X δ0 E0 V0) (((2 * Ω : ℝ) : ℂ) * I) ≠ 0)
    (hA : c.na1 R X ωb (nxeq R X δ0 E0 V0) = Ω ^ 2 * c.nq1 R X ωb (nxeq R X δ0 E0 V0) Ω)
    (hB : c.na0 R X ωb (nxeq R X δ0 E0 V0) = Ω ^ 2 * c.nq0 R X ωb (nxeq R X δ0 E0 V0) Ω)
    (h6 : 0 < c.na6 X) (h5 : 0 < c.na5 R X ωb (nxeq R X δ0 E0 V0))
    (h1 : 0 < c.nq1 R X ωb (nxeq R X δ0 E0 V0) Ω) (h0 : 0 < c.nq0 R X ωb (nxeq R X δ0 E0 V0) Ω)
    (hg : c.na6 X * c.nq1 R X ωb (nxeq R X δ0 E0 V0) Ω ^ 2 +
        c.na5 R X ωb (nxeq R X δ0 E0 V0) ^ 2 * c.nq0 R X ωb (nxeq R X δ0 E0 V0) Ω <
      c.na5 R X ωb (nxeq R X δ0 E0 V0) * c.nq2 R X ωb (nxeq R X δ0 E0 V0) Ω *
        c.nq1 R X ωb (nxeq R X δ0 E0 V0) Ω) (Vh : ℝ) :
    c.nz R X ωb δ0 E0 V0 Ω Vh =
      c.nzc R X ωb (nxeq R X δ0 E0 V0) (((2 * Ω : ℝ) : ℂ) * I) Vh := by
  have hne : 2 * c.H * (c.τ * X ^ 2) ≠ 0 := h6.ne'
  have hH : c.H ≠ 0 := fun h => hne (by simp [h])
  have hτ : c.τ ≠ 0 := fun h => hne (by simp [h])
  have hX : X ≠ 0 := fun h => hne (by simp [h])
  have hΩc : (Ω : ℂ) ≠ 0 := by exact_mod_cast hΩ
  have hP : c.ncharP R X ωb (nxeq R X δ0 E0 V0) (((2 * Ω : ℝ) : ℂ) * I) ≠ 0 := by
    rw [c.ncharP_factor R X ωb _ hA hB]
    refine mul_ne_zero ?_ ?_
    · have e : (((2 * Ω : ℝ) : ℂ) * I) ^ 2 + (Ω : ℂ) ^ 2 = -3 * (Ω : ℂ) ^ 2 := by
        push_cast
        linear_combination 4 * (Ω : ℂ) ^ 2 * Complex.I_sq
      rw [e]
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hΩc)
    · intro hq
      have := c.nquartic_re_neg R X ωb _ h6 h5 h1 h0 hg hq
      simp at this
  have hstab := c.neig_stable R X ωb (nxeq R X δ0 E0 V0) V0 hω0 hA hB h6 h5 h1 h0 hg
  have hz1 := c.nz_eq R X ωb hΩ hstab Vh
  have hz2 := c.nzc_eq R X ωb (nxeq R X δ0 E0 V0) V0 hX hω0 hH hτ hΔ2 hΛ2 hP Vh
  by_contra hne'
  have he : (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ
      (c.nz R X ωb δ0 E0 V0 Ω Vh - c.nzc R X ωb (nxeq R X δ0 E0 V0) (((2 * Ω : ℝ) : ℂ) * I) Vh) =
      (((2 * Ω : ℝ) : ℂ) * I) • (c.nz R X ωb δ0 E0 V0 Ω Vh -
        c.nzc R X ωb (nxeq R X δ0 E0 V0) (((2 * Ω : ℝ) : ℂ) * I) Vh) := by
    have h0' : ((((2 * Ω : ℝ) : ℂ) * I) • c.nz R X ωb δ0 E0 V0 Ω Vh -
        (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ
          c.nz R X ωb δ0 E0 V0 Ω Vh) -
        ((((2 * Ω : ℝ) : ℂ) * I) • c.nzc R X ωb (nxeq R X δ0 E0 V0) (((2 * Ω : ℝ) : ℂ) * I) Vh -
          (c.njac R X ωb (nxeq R X δ0 E0 V0, V0)).map (algebraMap ℝ ℂ) *ᵥ
            c.nzc R X ωb (nxeq R X δ0 E0 V0) (((2 * Ω : ℝ) : ℂ) * I) Vh) = 0 := by
      rw [hz1, hz2, sub_self]
    rw [Matrix.mulVec_sub, smul_sub, ← sub_eq_zero, ← neg_eq_zero, ← h0']
    abel
  have h1' : (((2 * Ω : ℝ) : ℂ) * I) ≠ (Ω : ℂ) * I := by
    intro h0'
    have := congrArg Complex.im h0'
    simp at this
    exact hΩ (by linarith)
  have h2' : (((2 * Ω : ℝ) : ℂ) * I) ≠ -((Ω : ℂ) * I) := by
    intro h0'
    have := congrArg Complex.im h0'
    simp at this
    exact hΩ (by linarith)
  have := hstab _ _ (sub_ne_zero.2 hne') he h1' h2'
  simp at this

/-! ### Dynamic partials and the quasi-static limit `ω_b → ∞` -/

/-- The dynamic conductance `G(s) = R'/(R'² + X²)`, `R' = R + sX/ω_b`. -/
def nG (s : ℂ) : ℂ := ωb * nρ R X ωb s / nΔ R X ωb s
/-- The dynamic susceptance `B(s) = X/(R'² + X²)`. -/
def nB (s : ℂ) : ℂ := X * ωb ^ 2 / nΔ R X ωb s
/-- The dynamic synchronizing coefficient `p_δ + E²B(s)`. -/
def nKδ (x : Fin 6 → ℝ) (s : ℂ) : ℂ := npδ x + x 3 ^ 2 * nB R X ωb s
/-- `p_E + E G(s)`. -/
def nKE (x : Fin 6 → ℝ) (s : ℂ) : ℂ := npE x + x 3 * nG R X ωb s
/-- `q_δ − E²G(s)`. -/
def nMδ (x : Fin 6 → ℝ) (s : ℂ) : ℂ := nqδ x - x 3 ^ 2 * nG R X ωb s
/-- `q_E + E B(s)`. -/
def nME (x : Fin 6 → ℝ) (s : ℂ) : ℂ := nqE x + x 3 * nB R X ωb s

/-- The characteristic function of the network core in the form of `DynQV.charF`, with the
dynamic partials. -/
def nchar (x : Fin 6 → ℝ) (s : ℂ) : ℂ :=
  s * (s + c.a) * (s + c.ωc) + c.ω0 * c.ωc * (nKδ R X ωb x s - c.kq * nKE R X ωb x s *
    nMδ R X ωb x s / (c.τ * s + 1 + c.kq * nME R X ωb x s)) / (2 * c.H)

@[tmio M, powerlib_domain] theorem nlag_eq (x : Fin 6 → ℝ) {s : ℂ} (hΔ : nΔ R X ωb s ≠ 0) :
    c.τ * s + 1 + c.kq * nME R X ωb x s = c.nΛ R X ωb x s / nΔ R X ωb s := by
  simp only [nME, nB, nΛ, nT]
  field_simp
  ring

/-- Away from `Δ = 0`, `Λ = 0` the characteristic polynomial is `2HΛ` times the
characteristic function with the dynamic partials. -/
@[tmio M, powerlib_domain] theorem nchar_eq (x : Fin 6 → ℝ) {s : ℂ} (hH : c.H ≠ 0)
    (hΔ : nΔ R X ωb s ≠ 0) (hΛ : c.nΛ R X ωb x s ≠ 0) :
    2 * c.H * c.nΛ R X ωb x s * c.nchar R X ωb x s = c.ncharP R X ωb x s := by
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  rw [nchar, c.nlag_eq R X ωb x hΔ]
  simp only [nKδ, nKE, nMδ, nG, nB, a]
  field_simp
  simp only [ncharP, nN, nΛ, nΔ]
  ring

omit c in
/-- The quasi-static identities: the static partials of `lossyP`, `lossyQ` are the partials
at fixed current plus the line terms `E²X/Z²`, `ER/Z²`, `−E²R/Z²`, `EX/Z²`. -/
@[tmio M, powerlib_domain] theorem nstatic (hZ : R ^ 2 + X ^ 2 ≠ 0) (δ0 E0 V0 : ℝ) :
    dδ (lossyP R X) ((δ0, E0), V0) = npδ (nxeq R X δ0 E0 V0) + E0 ^ 2 * X / (R ^ 2 + X ^ 2) ∧
    dE (lossyP R X) ((δ0, E0), V0) = npE (nxeq R X δ0 E0 V0) + E0 * R / (R ^ 2 + X ^ 2) ∧
    dδ (lossyQ R X) ((δ0, E0), V0) = nqδ (nxeq R X δ0 E0 V0) - E0 ^ 2 * R / (R ^ 2 + X ^ 2) ∧
    dE (lossyQ R X) ((δ0, E0), V0) = nqE (nxeq R X δ0 E0 V0) + E0 * X / (R ^ 2 + X ^ 2) := by
  obtain ⟨h1, h2, -, h4, h5, -⟩ := lossy_partials R X ((δ0, E0), V0)
  have h := Real.sin_sq_add_cos_sq δ0
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1]
    simp only [npδ, nxeq, nid, niq, Matrix.cons_val]
    linear_combination (norm := skip) (E0 ^ 2 * X / (R ^ 2 + X ^ 2)) * h
    field_simp
    ring
  · rw [h2]
    simp only [npE, nxeq, nid, niq, Matrix.cons_val]
    linear_combination (norm := skip) (-(E0 * R / (R ^ 2 + X ^ 2))) * h
    field_simp
    ring
  · rw [h4]
    simp only [nqδ, nxeq, nid, niq, Matrix.cons_val]
    linear_combination (norm := skip) (-(E0 ^ 2 * R / (R ^ 2 + X ^ 2))) * h
    field_simp
    ring
  · rw [h5]
    simp only [nqE, nxeq, nid, niq, Matrix.cons_val]
    linear_combination (norm := skip) (-(E0 * X / (R ^ 2 + X ^ 2))) * h
    field_simp
    ring

/-- At `s = 0` the dynamic partials are the quasi-static ones, for every `ω_b ≠ 0`. -/
@[tmio M, powerlib_domain] theorem ndyn_zero (hZ : R ^ 2 + X ^ 2 ≠ 0) (hωb : ωb ≠ 0)
    (δ0 E0 V0 : ℝ) :
    nKδ R X ωb (nxeq R X δ0 E0 V0) 0 = dδ (lossyP R X) ((δ0, E0), V0) ∧
    nKE R X ωb (nxeq R X δ0 E0 V0) 0 = dE (lossyP R X) ((δ0, E0), V0) ∧
    nMδ R X ωb (nxeq R X δ0 E0 V0) 0 = dδ (lossyQ R X) ((δ0, E0), V0) ∧
    nME R X ωb (nxeq R X δ0 E0 V0) 0 = dE (lossyQ R X) ((δ0, E0), V0) := by
  obtain ⟨h1, h2, h3, h4⟩ := nstatic R X hZ δ0 E0 V0
  have hZc : (R : ℂ) ^ 2 + X ^ 2 ≠ 0 := by exact_mod_cast hZ
  have hωc : (ωb : ℂ) ≠ 0 := by exact_mod_cast hωb
  have e3 : (nxeq R X δ0 E0 V0) 3 = E0 := rfl
  have hΔ0 : nΔ R X ωb 0 = (ωb : ℂ) ^ 2 * (R ^ 2 + X ^ 2) := by
    simp only [nΔ, nρ]
    ring
  have hρ0 : nρ R X ωb 0 = R * ωb := by simp [nρ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1, nKδ, nB, hΔ0, e3]
    push_cast
    field_simp
  · rw [h2, nKE, nG, hΔ0, hρ0, e3]
    push_cast
    field_simp
  · rw [h3, nMδ, nG, hΔ0, hρ0, e3]
    push_cast
    field_simp
  · rw [h4, nME, nB, hΔ0, e3]
    push_cast
    field_simp

/-- `ω_b⁻¹ → 0`. -/
@[tmio T, powerlib_foundation] private theorem tendsto_inv_ofReal :
    Tendsto (fun ωb : ℝ => ((ωb : ℂ))⁻¹) atTop (𝓝 0) := by
  have h := (Complex.continuous_ofReal.tendsto 0).comp
    (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0))
  simpa [Function.comp_def] using h

/-- `R + sX/ω_b → R`. -/
@[tmio M, powerlib_domain] private theorem tendsto_line (s : ℂ) :
    Tendsto (fun ωb : ℝ => (R : ℂ) + s * X * (ωb : ℂ)⁻¹) atTop (𝓝 (R : ℂ)) := by
  simpa using (tendsto_inv_ofReal.const_mul (s * X)).const_add (R : ℂ)

/-- `Δ(s)/ω_b² → R² + X²`. -/
@[tmio M, powerlib_domain] theorem nΔ_tendsto (s : ℂ) :
    Tendsto (fun ωb : ℝ => nΔ R X ωb s / (ωb : ℂ) ^ 2) atTop (𝓝 ((R : ℂ) ^ 2 + X ^ 2)) := by
  refine (((tendsto_line R X s).pow 2).add_const ((X : ℂ) ^ 2)).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with ωb hωb
  have : (ωb : ℂ) ≠ 0 := by exact_mod_cast hωb
  simp only [nΔ, nρ]
  field_simp

/-- As `ω_b → ∞` the dynamic partials tend to the quasi-static partials of `lossyP`, `lossyQ`,
for every `s`. -/
@[tmio M, powerlib_domain] theorem ndyn_tendsto (hZ : R ^ 2 + X ^ 2 ≠ 0) (δ0 E0 V0 : ℝ)
    (s : ℂ) :
    Tendsto (fun ωb => nKδ R X ωb (nxeq R X δ0 E0 V0) s) atTop
        (𝓝 (dδ (lossyP R X) ((δ0, E0), V0))) ∧
      Tendsto (fun ωb => nKE R X ωb (nxeq R X δ0 E0 V0) s) atTop
        (𝓝 (dE (lossyP R X) ((δ0, E0), V0))) ∧
      Tendsto (fun ωb => nMδ R X ωb (nxeq R X δ0 E0 V0) s) atTop
        (𝓝 (dδ (lossyQ R X) ((δ0, E0), V0))) ∧
      Tendsto (fun ωb => nME R X ωb (nxeq R X δ0 E0 V0) s) atTop
        (𝓝 (dE (lossyQ R X) ((δ0, E0), V0))) := by
  obtain ⟨h1, h2, h3, h4⟩ := nstatic R X hZ δ0 E0 V0
  have hZc : (R : ℂ) ^ 2 + X ^ 2 ≠ 0 := by exact_mod_cast hZ
  have hB : Tendsto (fun ωb => nB R X ωb s) atTop (𝓝 ((X : ℂ) / (R ^ 2 + X ^ 2))) := by
    refine ((tendsto_const_nhds (x := (X : ℂ))).div (nΔ_tendsto R X s) hZc).congr' ?_
    filter_upwards with ωb
    show (X : ℂ) / (nΔ R X ωb s / (ωb : ℂ) ^ 2) = nB R X ωb s
    rw [nB, div_div_eq_mul_div]
  have hG : Tendsto (fun ωb => nG R X ωb s) atTop (𝓝 ((R : ℂ) / (R ^ 2 + X ^ 2))) := by
    refine ((tendsto_line R X s).div (nΔ_tendsto R X s) hZc).congr' ?_
    filter_upwards [eventually_ne_atTop 0] with ωb hωb
    have : (ωb : ℂ) ≠ 0 := by exact_mod_cast hωb
    show ((R : ℂ) + s * X * (ωb : ℂ)⁻¹) / (nΔ R X ωb s / (ωb : ℂ) ^ 2) = nG R X ωb s
    rw [nG, div_div_eq_mul_div]
    congr 1
    simp only [nρ]
    field_simp
  have e3 : (nxeq R X δ0 E0 V0) 3 = E0 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1]
    push_cast
    simpa [nKδ, e3, mul_div_assoc] using (hB.const_mul ((E0 : ℂ) ^ 2)).const_add
      ((npδ (nxeq R X δ0 E0 V0) : ℝ) : ℂ)
  · rw [h2]
    push_cast
    simpa [nKE, e3, mul_div_assoc] using (hG.const_mul (E0 : ℂ)).const_add
      ((npE (nxeq R X δ0 E0 V0) : ℝ) : ℂ)
  · rw [h3]
    push_cast
    simpa [nMδ, e3, mul_div_assoc] using (hG.const_mul ((E0 : ℂ) ^ 2)).const_sub
      ((nqδ (nxeq R X δ0 E0 V0) : ℝ) : ℂ)
  · rw [h4]
    push_cast
    simpa [nME, e3, mul_div_assoc] using (hB.const_mul (E0 : ℂ)).const_add
      ((nqE (nxeq R X δ0 E0 V0) : ℝ) : ℂ)

/-- As `ω_b → ∞` the characteristic function of the network core tends to that of the
quasi-static core `lossyCore`, for every `s` with `τ s + b ≠ 0`. -/
@[tmio M, powerlib_domain] theorem nchar_tendsto (hZ : R ^ 2 + X ^ 2 ≠ 0) (δ0 E0 V0 : ℝ)
    {s : ℂ} (hl : (lossyCore c.ω0 c.H c.D c.ωc c.τ c.kq R X δ0 E0 V0).lag s ≠ 0) :
    Tendsto (fun ωb => c.nchar R X ωb (nxeq R X δ0 E0 V0) s) atTop
      (𝓝 ((lossyCore c.ω0 c.H c.D c.ωc c.τ c.kq R X δ0 E0 V0).charF s)) := by
  obtain ⟨hK, hKE, hM, hME⟩ := ndyn_tendsto R X hZ δ0 E0 V0 s
  have hlag := (hME.const_mul (c.kq : ℂ)).const_add (c.τ * s + 1)
  have el : (c.τ : ℂ) * s + 1 + c.kq * (dE (lossyQ R X) ((δ0, E0), V0) : ℝ) =
      (lossyCore c.ω0 c.H c.D c.ωc c.τ c.kq R X δ0 E0 V0).lag s := by
    simp only [lag, b, lossyCore]
    push_cast
    ring
  rw [el] at hlag
  have h := (tendsto_const_nhds (x := s * (s + c.a) * (s + c.ωc))).add
    (((tendsto_const_nhds (x := (c.ω0 : ℂ) * c.ωc)).mul
      (hK.sub (((hKE.const_mul (c.kq : ℂ)).mul hM).div hlag hl))).div_const (2 * (c.H : ℂ)))
  have e : (lossyCore c.ω0 c.H c.D c.ωc c.τ c.kq R X δ0 E0 V0).charF s =
      s * (s + c.a) * (s + c.ωc) + c.ω0 * c.ωc * ((dδ (lossyP R X) ((δ0, E0), V0) : ℂ) -
        c.kq * (dE (lossyP R X) ((δ0, E0), V0) : ℂ) * (dδ (lossyQ R X) ((δ0, E0), V0) : ℂ) /
          (lossyCore c.ω0 c.H c.D c.ωc c.τ c.kq R X δ0 E0 V0).lag s) / (2 * c.H) := by
    simp only [charF, Keff, lossyCore, a]
  rw [e]
  refine h.congr fun ωb => ?_
  simp only [nchar, Pi.div_apply]

/-- The right eigenvector's `ΔE` component tends to that of the quasi-static core. -/
@[tmio M, powerlib_domain] theorem nr3_tendsto (hZ : R ^ 2 + X ^ 2 ≠ 0) (δ0 E0 V0 : ℝ)
    {s : ℂ} (hl : (lossyCore c.ω0 c.H c.D c.ωc c.τ c.kq R X δ0 E0 V0).lag s ≠ 0) :
    Tendsto (fun ωb => c.nr3 R X ωb (nxeq R X δ0 E0 V0) s) atTop
      (𝓝 ((lossyCore c.ω0 c.H c.D c.ωc c.τ c.kq R X δ0 E0 V0).right s 3)) := by
  obtain ⟨-, -, hM, hME⟩ := ndyn_tendsto R X hZ δ0 E0 V0 s
  have hZc : (R : ℂ) ^ 2 + X ^ 2 ≠ 0 := by exact_mod_cast hZ
  have hlag := (hME.const_mul (c.kq : ℂ)).const_add (c.τ * s + 1)
  have el : (c.τ : ℂ) * s + 1 + c.kq * (dE (lossyQ R X) ((δ0, E0), V0) : ℝ) =
      (lossyCore c.ω0 c.H c.D c.ωc c.τ c.kq R X δ0 E0 V0).lag s := by
    simp only [lag, b, lossyCore]
    push_cast
    ring
  rw [el] at hlag
  have h := ((hM.const_mul (c.kq : ℂ)).neg).div hlag hl
  have e : (lossyCore c.ω0 c.H c.D c.ωc c.τ c.kq R X δ0 E0 V0).right s 3 =
      -(c.kq * (dδ (lossyQ R X) ((δ0, E0), V0) : ℂ)) /
        (lossyCore c.ω0 c.H c.D c.ωc c.τ c.kq R X δ0 E0 V0).lag s := by
    simp [right, lossyCore]
  rw [e]
  refine h.congr' ?_
  filter_upwards [(nΔ_tendsto R X s).eventually_ne hZc, eventually_ne_atTop 0]
    with ωb hΔ hωb
  have hΔ' : nΔ R X ωb s ≠ 0 := fun h0 => hΔ (by rw [h0, zero_div])
  have := c.nlag_eq R X ωb (nxeq R X δ0 E0 V0) hΔ'
  show -(c.kq * nMδ R X ωb (nxeq R X δ0 E0 V0) s) /
    (c.τ * s + 1 + c.kq * nME R X ωb (nxeq R X δ0 E0 V0) s) = c.nr3 R X ωb (nxeq R X δ0 E0 V0) s
  rw [this, nr3, nMδ, nG, div_div_eq_mul_div]
  congr 1
  field_simp

/-- The sextic over `ω_b²` tends to `2H(R² + X²)` times the quasi-static quartic `charP4`:
two roots escape (the line poles) and four converge to the quasi-static spectrum. -/
@[tmio M, powerlib_domain] theorem ncharP_tendsto (hZ : R ^ 2 + X ^ 2 ≠ 0) (hH : c.H ≠ 0)
    (δ0 E0 V0 : ℝ) (s : ℂ) :
    Tendsto (fun ωb : ℝ => c.ncharP R X ωb (nxeq R X δ0 E0 V0) s / (ωb : ℂ) ^ 2) atTop
      (𝓝 (2 * c.H * (R ^ 2 + X ^ 2) *
        (lossyCore c.ω0 c.H c.D c.ωc c.τ c.kq R X δ0 E0 V0).charP4 s)) := by
  obtain ⟨h1, h2, h3, h4⟩ := nstatic R X hZ δ0 E0 V0
  have hZc : (R : ℂ) ^ 2 + X ^ 2 ≠ 0 := by exact_mod_cast hZ
  have hHc : (c.H : ℂ) ≠ 0 := by exact_mod_cast hH
  set x := nxeq R X δ0 E0 V0 with hx
  set F : ℂ → ℂ := fun l => (2 * c.H * s + c.D) * s * (s + c.ωc) *
      (c.nT x s * (l ^ 2 + X ^ 2) + c.kq * x 3 * X) +
    c.ω0 * c.ωc * ((npδ x * c.nT x s - c.kq * npE x * nqδ x) * (l ^ 2 + X ^ 2) +
      x 3 ^ 2 * X * c.nT x s + c.kq * x 3 * (x 3 * npE x - nqδ x) * l +
      c.kq * x 3 * (npδ x * X + x 3 ^ 2)) with hF
  have hFc : Continuous F := by rw [hF]; fun_prop
  have h := (hFc.tendsto (R : ℂ)).comp (tendsto_line R X s)
  have e : F R = 2 * c.H * (R ^ 2 + X ^ 2) *
      (lossyCore c.ω0 c.H c.D c.ωc c.τ c.kq R X δ0 E0 V0).charP4 s := by
    have e3 : x 3 = E0 := rfl
    simp only [hF, charP4, lag, b, lossyCore, a, h1, h2, h3, h4, e3, nT]
    push_cast
    field_simp
    ring
  rw [← e]
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with ωb hωb
  have : (ωb : ℂ) ≠ 0 := by exact_mod_cast hωb
  simp only [Function.comp_apply, hF, ncharP, nN, nΛ, nΔ, nρ]
  field_simp

end DynQV
end VoltageModulation
end powerlib.GFM
