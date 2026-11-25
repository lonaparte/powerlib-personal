import theorem.GridTiedConverter.GFM.FullModel.BoundaryLayer
import theorem.Criteria.Bilharz

/-! # The 13-state grid-forming converter: the boundary layer decided symbolically

Model boundary.
The ten-state fast block `fastBlock δ` of
`theorem/GridTiedConverter/GFM/FullModel/BoundaryLayer.lean` (filter current, capacitor voltage,
line current, current- and voltage-loop integrators, dq, linearized in the fast states; the
real form of the complex `5 × 5` matrix `fastMatrix δ`). Continuous time, constant matrices.
Every parameter value with `L_f, C_f, L_g ≠ 0`: any feed-forward `k_ff`, decoupling `k_dv`,
virtual impedance `Z_v = R_v + jX_v`, any signs of the gains and resistances. The normalized
parameters are `k_p = K_pc/L_f`, `k_i = K_ic/L_f`, `ρ = R_f/L_f` (current loop), `r = R_g/L_g`,
`w = ω₀`, `c = 1/(C_f L_g)` (filter and line), `P = K_pv/C_f`, `e = 1 − k_dv`, `q = K_iv/C_f`
(voltage loop), `κ = (1 − k_ff)/(C_f L_g)`, `r_v = R_v/L_g`, `x_v = X_v/L_g`. Excluded: the
expansion of `Δ₆, Δ₈, Δ₁₀` in the parameters (below), and everything excluded by the full-order
model.

Source: GFM counterpart study, full-order model note (t5: "fast block Hurwitz only numerically");
the complex Routh–Hurwitz criterion of H. Bilharz, *Z. Angew. Math. Mech.* 24 (1944), in
determinant form (`theorem/Criteria/Bilharz.lean`), the Routh table of `χ χ̄`
(`theorem/Criteria/RouthTable.lean`, `theorem/Criteria/RouthComplex.lean`). The characteristic
polynomial, its normalized coefficients and the factorizations below were derived by exact
computer algebra (symbolic determinant, fraction-free elimination over `ℤ[parameters]`,
factorization; discovery evidence) and are checked here by `ring`.

Results.
* **The characteristic polynomial for symbolic parameters** (`Params.charDet_fastMatrix`):
  `det(s − fastMatrix 0) = s⁵ + a₄ s⁴ + … + a₀ = (k_p s + k_i) χ_v(s) +
  s²(s + ρ)((s + jω₀)(s + Z_g/L_g) + 1/(C_f L_g))`, `χ_v` the voltage-level cubic
  (`Params.det_voltageMatrix`), with the coefficients `Params.fastCoeff`; in the normalized
  parameters `Params.fastCoeff_eq` (`FastLevel.coeffs`, explicit polynomial real and imaginary
  parts).
* **Exact decision for every parameter value**: `Params.spectrallyStable_fastBlock_iff_fastDelta`,
  the boundary layer is spectrally stable at an angle iff its five Bilharz determinants
  `Params.fastDelta k` (`Criteria.quinticBilharz2 … 10` of the coefficients) are positive;
  explicitly `Params.fastDelta_zero` (`Δ₂ = (K_pc + R_f)/L_f + R_g/L_g`), `Params.fastDelta_one`
  (`Δ₄ = FastLevel.delta4`, 42 terms) and
  `Params.spectrallyStable_fastBlock_iff_explicit`. The remaining three are explicit
  polynomials of the ten coefficient parts (`Criteria.BilharzPoly.quintic6`, `quintic8`,
  `quintic10`: 28, 181 and 549 terms); expanded in the normalized parameters they are irreducible
  over `ℚ` with 1256 terms (`Δ₆`, general) and, in the ideal design `k_ff = k_dv = 1`, `Z_v = 0`,
  398, 2922 and `k_i q` times 7215 terms — too large to state or normalize by `ring` here.
  Computer algebra (not formalized, for the same reason) shows the time-scale structure in the
  ideal design: with the current loop of `currentScaled (1/t)` the leading coefficients in `t` of
  `Δ₂, Δ₄` are `k_p + ρ` and `k_i (k_p + ρ)²`, and that of `Δ_{2k+4}` is `(k_p + ρ)² k_i^{2k+1}`
  times the voltage-level determinant `Δ_{2k}` — the exact form of
  `Params.exists_muStar_spectrallyStable_fastBlock`.
* The voltage level in normalized parameters (`VoltageLevel.delta4`, `VoltageLevel.lineTerm`,
  `VoltageLevel.cross`, `VoltageLevel.third`): `Params.voltage_routh_eq`, the second Routh–Hurwitz
  condition is `VoltageLevel.delta4` (21 terms) and the third `complexCubicDet a₂ a₁ a₀ = q (Δ₄ L +
  q ((P − r_v)² (r + r_v) q − G))` with `L = P|z_t|² + e w (r x_v − r_v w) + κ (r + r_v)`
  (`z_t = r + r_v + j(w + x_v)`) and `G` (42 terms);
  `Params.spectrallyStable_voltageMatrix_iff_normalized`.
* The decision at fixed gains through the Routh table of `χ χ̄`: `Params.charpoly_fastBlock`,
  `Params.spectrallyStable_fastBlock_iff_routhColumn_of_det`.
* Checks, read from the symbolic decision: `blWitness_fastDelta` (`Δ₂ = 21/10`, `Δ₄ = −2257/1000`
  at the witness of `BoundaryLayer.lean`, in agreement with its eigenvalue `1 + 3j`).
* **The exact stability threshold of the witness family** `blWitness.currentScaled μ`
  (`blWitness_currentScaled_threshold`): there is `μ_c ∈ (100/581, 5/29)` with
  `blThresholdPoly (1/μ_c) = 0` (an explicit integer polynomial of degree 11, `μ_c ≈ 0.172306`)
  such that for every `μ > 0` the boundary layer is stable iff `μ < μ_c`. Proof: with `t = 1/μ`
  the five determinants are explicit polynomials of `t` (`(11t + 10)/10`, `R₄/1000`,
  `t R₆/450000`, `t² R₈/12656250`, `128 t⁵ R/31640625`), signed on intervals with rational
  endpoints by exact certificates: Bernstein coefficients on `(0, 1/5]`, `[1/5, 99/40]`,
  `[99/40, 19/4]`, `[19/4, 107/20]`, Taylor coefficients on `[29/5, ∞)`, and the monotonicity
  of `R` on `[107/20, ∞)` (a divided difference with positive coefficients); the root by the
  intermediate value theorem. Its instance `blWitness_currentScaled_spectrallyStable`
  (`μ = 1/10 < μ_c`).
-/

noncomputable section
namespace powerlib.GFM.FullModel
open Complex Polynomial
open scoped ComplexConjugate
open powerlib.SingularPerturbation (realify)

namespace Params

variable (p : Params)

/-- The characteristic polynomial of the fast block is `χ χ̄`, `χ` that of the complex fast
matrix (`Criteria.charpoly_realify`). -/
@[tmio M, powerlib_domain] theorem charpoly_fastBlock (δ : ℝ) :
    (p.fastBlock δ).charpoly.map (algebraMap ℝ ℂ) =
      (p.fastMatrix δ).charpoly * (p.fastMatrix δ).charpoly.map (starRingEnd ℂ) := by
  rw [fastBlock_eq_realify]
  exact Criteria.charpoly_realify _

/-- The decision through a rational coefficient list of `det(s − M) · conj det(s̄ − M)`,
`M = fastMatrix 0`. -/
@[tmio M, powerlib_domain] theorem spectrallyStable_fastBlock_iff_routhColumn_of_det (δ : ℝ)
    {a : ℚ} (ha : 0 < a) (l : List ℚ)
    (h : ∀ s : ℂ, aeval s (Criteria.ofList ((a :: l).map (Rat.castHom ℝ))) =
      (Matrix.scalar (Fin 5) s - p.fastMatrix 0).det *
        conj (Matrix.scalar (Fin 5) (conj s) - p.fastMatrix 0).det) :
    Linear.SpectrallyStable (p.fastBlock δ) ↔
      ∀ c ∈ Criteria.routhColumn l.length (a :: l), 0 < c := by
  rw [p.spectrallyStable_fastBlock_iff, fastBlock_eq_realify]
  exact Criteria.spectrallyStable_realify_iff_routhColumn_of_det_rat _ ha l h

/-! ### The characteristic polynomial for symbolic parameters -/

/-- The coefficients `a₀, …, a₄` of `det(s − fastMatrix 0) = s⁵ + a₄ s⁴ + … + a₀`: with the
voltage-level coefficients `v₂, v₁, v₀` (`voltageA2`, `voltageA1`, `voltageA0`),
`a₄ = (K_pc + R_f)/L_f + Z_g/L_g + jω₀`, `a₃ = k_p v₂ + k_i + jω₀ Z_g/L_g + 1/(C_f L_g) +
ρ (Z_g/L_g + jω₀)`, `a₂ = k_p v₁ + k_i v₂ + ρ (jω₀ Z_g/L_g + 1/(C_f L_g))`, `a₁ = k_p v₀ + k_i v₁`,
`a₀ = k_i v₀`. -/
def fastCoeff : Fin 5 → ℂ :=
  ![((p.Kic / p.Lf : ℝ) : ℂ) * p.voltageA0,
    ((p.Kpc / p.Lf : ℝ) : ℂ) * p.voltageA0 + ((p.Kic / p.Lf : ℝ) : ℂ) * p.voltageA1,
    ((p.Kpc / p.Lf : ℝ) : ℂ) * p.voltageA1 + ((p.Kic / p.Lf : ℝ) : ℂ) * p.voltageA2 +
      ((p.Rf / p.Lf : ℝ) : ℂ) * (p.ω0 * I * (p.Zg / p.Lg) + ((1 / (p.Cf * p.Lg) : ℝ) : ℂ)),
    ((p.Kpc / p.Lf : ℝ) : ℂ) * p.voltageA2 + ((p.Kic / p.Lf : ℝ) : ℂ) + p.ω0 * I * (p.Zg / p.Lg) +
      ((1 / (p.Cf * p.Lg) : ℝ) : ℂ) + ((p.Rf / p.Lf : ℝ) : ℂ) * (p.Zg / p.Lg + p.ω0 * I),
    (((p.Kpc + p.Rf) / p.Lf : ℝ) : ℂ) + p.Zg / p.Lg + p.ω0 * I]

/-- **The characteristic polynomial of the fast matrix** for symbolic parameters
(`L_f, C_f, L_g ≠ 0`): `det(s − fastMatrix 0) = s⁵ + a₄ s⁴ + a₃ s³ + a₂ s² + a₁ s + a₀`. -/
@[tmio M, powerlib_domain] theorem charDet_fastMatrix (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (s : ℂ) :
    (Matrix.scalar (Fin 5) s - p.fastMatrix 0).det =
      s ^ 5 + p.fastCoeff 4 * s ^ 4 + p.fastCoeff 3 * s ^ 3 + p.fastCoeff 2 * s ^ 2 +
        p.fastCoeff 1 * s + p.fastCoeff 0 := by
  have h0 : ej 0 = 1 := by simp [ej]
  have hLf' : (p.Lf : ℂ) ≠ 0 := by exact_mod_cast hLf
  have hCf' : (p.Cf : ℂ) ≠ 0 := by exact_mod_cast hCf
  have hLg' : (p.Lg : ℂ) ≠ 0 := by exact_mod_cast hLg
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_unique, Fin.sum_univ_zero]
  simp [Matrix.submatrix, Fin.succAbove, Fin.lt_def, fastMatrix, h0, fastCoeff, voltageA2,
    voltageA1, voltageA0, Zt, Bf, Matrix.scalar_apply, Matrix.diagonal_apply]
  field_simp
  ring

/-- The five Bilharz determinants `Δ₂, Δ₄, Δ₆, Δ₈, Δ₁₀` of the fast block: those of the monic
quintic `det(s − fastMatrix 0)` (`Criteria.quinticBilharz2` … `quinticBilharz10`). -/
def fastDelta : Fin 5 → ℝ :=
  ![Criteria.quinticBilharz2 (p.fastCoeff 4) (p.fastCoeff 3) (p.fastCoeff 2) (p.fastCoeff 1)
      (p.fastCoeff 0),
    Criteria.quinticBilharz4 (p.fastCoeff 4) (p.fastCoeff 3) (p.fastCoeff 2) (p.fastCoeff 1)
      (p.fastCoeff 0),
    Criteria.quinticBilharz6 (p.fastCoeff 4) (p.fastCoeff 3) (p.fastCoeff 2) (p.fastCoeff 1)
      (p.fastCoeff 0),
    Criteria.quinticBilharz8 (p.fastCoeff 4) (p.fastCoeff 3) (p.fastCoeff 2) (p.fastCoeff 1)
      (p.fastCoeff 0),
    Criteria.quinticBilharz10 (p.fastCoeff 4) (p.fastCoeff 3) (p.fastCoeff 2) (p.fastCoeff 1)
      (p.fastCoeff 0)]

/-- **The boundary layer, exactly, for every parameter value** (`L_f, C_f, L_g ≠ 0`): the fast
block is spectrally stable at the angle `δ` iff its five Bilharz determinants are positive
(`Criteria.complexQuintic_roots_re_neg_iff`). -/
@[tmio M, powerlib_domain] theorem spectrallyStable_fastBlock_iff_fastDelta (hLf : p.Lf ≠ 0)
    (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0) (δ : ℝ) :
    Linear.SpectrallyStable (p.fastBlock δ) ↔ ∀ k, 0 < p.fastDelta k := by
  rw [p.spectrallyStable_fastBlock_iff, fastBlock_eq_realify,
    Criteria.spectrallyStable_realify_iff_charpoly]
  simp only [Matrix.eval_charpoly, p.charDet_fastMatrix hLf hCf hLg]
  rw [Criteria.complexQuintic_roots_re_neg_iff, Fin.forall_fin_succ, Fin.forall_fin_succ,
    Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_one]
  simp [fastDelta]

end Params

/-! ### The coefficients and the first two determinants in normalized parameters -/

namespace FastLevel

/-- The coefficients `a₀, …, a₄` of the fast characteristic polynomial in the normalized
parameters `k_p, k_i, ρ, r, w, c, P, e, q, κ, r_v, x_v` (real and imaginary parts). -/
def coeffs (kp ki ρ r w c P e q κ rv xv : ℝ) : Fin 5 → ℂ :=
  ![⟨ki * r * q + ki * q * rv, ki * w * q + ki * q * xv⟩,
    ⟨-ki * w ^ 2 * e + kp * r * q + kp * q * rv + ki * r * P + ki * P * rv + ki * q + ki * κ,
      ki * r * w * e + kp * w * q + kp * q * xv + ki * w * P + ki * P * xv⟩,
    ⟨-kp * w ^ 2 * e + kp * r * P + kp * P * rv - ρ * w ^ 2 + kp * q + kp * κ + ki * r + ki * P +
        ρ * c,
      kp * r * w * e + kp * w * P + kp * P * xv + ki * w * e + ρ * r * w + ki * w⟩,
    ⟨kp * r + kp * P + ρ * r - w ^ 2 + ki + c, kp * w * e + kp * w + 2 * ρ * w + r * w⟩,
    ⟨kp + ρ + r, 2 * w⟩]

/-- The second Bilharz determinant `Δ₄` of the fast block in the normalized parameters
(42 terms; it does not depend on `x_v`). -/
def delta4 (kp ki ρ r w c P e q κ rv _xv : ℝ) : ℝ :=
  -kp ^ 2 * w ^ 2 * e ^ 2 + kp ^ 2 * w ^ 2 * e - kp * ρ * w ^ 2 * e + kp * r * w ^ 2 * e
  + kp ^ 3 * r + kp ^ 3 * P + 3 * kp ^ 2 * ρ * r + 2 * kp ^ 2 * ρ * P + 2 * kp ^ 2 * r ^ 2
  + kp ^ 2 * r * P - kp ^ 2 * P * rv + 3 * kp * ρ ^ 2 * r + kp * ρ ^ 2 * P
  + 4 * kp * ρ * r ^ 2 + kp * ρ * r * P + kp * ρ * w ^ 2 - kp * ρ * P * rv + kp * r ^ 3
  - kp * r * P * rv + ρ ^ 3 * r + 2 * ρ ^ 2 * r ^ 2 + ρ * r ^ 3 + ρ * r * w ^ 2
  + kp ^ 2 * ki + kp ^ 2 * c - kp ^ 2 * q - kp ^ 2 * κ + 2 * kp * ki * ρ + kp * ki * r
  - kp * ki * P + kp * ρ * c - kp * ρ * q - kp * ρ * κ + 2 * kp * r * c - kp * r * q
  - kp * r * κ + ki * ρ ^ 2 + ki * ρ * r - ki * ρ * P - ki * r * P + ρ * r * c
  + r ^ 2 * c

end FastLevel

namespace Params

variable (p : Params)

/-- **The coefficients in normalized parameters** (`L_f, C_f, L_g ≠ 0`). -/
@[tmio M, powerlib_domain] theorem fastCoeff_eq (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) :
    p.fastCoeff = FastLevel.coeffs (p.Kpc / p.Lf) (p.Kic / p.Lf) (p.Rf / p.Lf) (p.Rg / p.Lg) p.ω0
      (1 / (p.Cf * p.Lg)) (p.Kpv / p.Cf) (1 - p.kdv) (p.Kiv / p.Cf)
      ((1 - p.kff) / (p.Cf * p.Lg)) (p.Rv / p.Lg) (p.Xv / p.Lg) := by
  obtain ⟨r2, i2, r1, i1, r0, i0⟩ := p.voltageA_parts hCf hLg
  have zr : (p.Zg / p.Lg).re = p.Rg / p.Lg := by rw [Complex.div_ofReal_re, Zg_eq]; simp
  have zi : (p.Zg / p.Lg).im = p.ω0 := by
    rw [Complex.div_ofReal_im, Zg_eq]; simp; field_simp
  funext k
  fin_cases k <;> apply Complex.ext <;>
    simp [fastCoeff, FastLevel.coeffs, Complex.mul_re, Complex.mul_im, r2, i2, r1, i1, r0, i0,
      zr, zi] <;> field_simp <;> ring

/-- `Δ₂ = Re a₄ = (K_pc + R_f)/L_f + R_g/L_g`, for every parameter value. -/
@[tmio M, powerlib_domain] theorem fastDelta_zero (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) : p.fastDelta 0 = (p.Kpc + p.Rf) / p.Lf + p.Rg / p.Lg := by
  simp only [fastDelta, p.fastCoeff_eq hLf hCf hLg]
  simp [FastLevel.coeffs, Criteria.quinticBilharz2, Criteria.BilharzPoly.quintic2]
  ring

/-- `Δ₄` in the normalized parameters, for every parameter value. -/
@[tmio M, powerlib_domain] theorem fastDelta_one (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) :
    p.fastDelta 1 = FastLevel.delta4 (p.Kpc / p.Lf) (p.Kic / p.Lf) (p.Rf / p.Lf) (p.Rg / p.Lg)
      p.ω0 (1 / (p.Cf * p.Lg)) (p.Kpv / p.Cf) (1 - p.kdv) (p.Kiv / p.Cf)
      ((1 - p.kff) / (p.Cf * p.Lg)) (p.Rv / p.Lg) (p.Xv / p.Lg) := by
  simp only [fastDelta, p.fastCoeff_eq hLf hCf hLg]
  simp [FastLevel.coeffs, Criteria.quinticBilharz4, Criteria.BilharzPoly.quintic4,
    FastLevel.delta4]
  ring

/-- **The boundary layer with the first two conditions explicit** (`L_f, C_f, L_g ≠ 0`, every
parameter value): spectrally stable iff `(K_pc + R_f)/L_f + R_g/L_g > 0`,
`FastLevel.delta4 > 0` and the remaining Bilharz determinants `Δ₆, Δ₈, Δ₁₀` are positive. -/
@[tmio M, powerlib_domain] theorem spectrallyStable_fastBlock_iff_explicit (hLf : p.Lf ≠ 0)
    (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0) (δ : ℝ) :
    Linear.SpectrallyStable (p.fastBlock δ) ↔
      0 < (p.Kpc + p.Rf) / p.Lf + p.Rg / p.Lg ∧
        0 < FastLevel.delta4 (p.Kpc / p.Lf) (p.Kic / p.Lf) (p.Rf / p.Lf) (p.Rg / p.Lg) p.ω0
          (1 / (p.Cf * p.Lg)) (p.Kpv / p.Cf) (1 - p.kdv) (p.Kiv / p.Cf)
          ((1 - p.kff) / (p.Cf * p.Lg)) (p.Rv / p.Lg) (p.Xv / p.Lg) ∧
        0 < p.fastDelta 2 ∧ 0 < p.fastDelta 3 ∧ 0 < p.fastDelta 4 := by
  rw [p.spectrallyStable_fastBlock_iff_fastDelta hLf hCf hLg, ← p.fastDelta_zero hLf hCf hLg,
    ← p.fastDelta_one hLf hCf hLg, Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_succ,
    Fin.forall_fin_succ, Fin.forall_fin_one]
  rfl

end Params

/-! ### The voltage level in normalized parameters -/

namespace VoltageLevel

/-- The second Routh–Hurwitz condition of the voltage level in the normalized parameters
`r, w, P, e, q, κ, r_v, x_v` (21 terms). -/
def delta4 (r w P e q κ rv xv : ℝ) : ℝ :=
  r * w ^ 2 * P * e ^ 2 - 2 * r * w ^ 2 * P * e - r * w * P * e * xv + w * P ^ 2 * e * xv
  + r ^ 3 * P + 2 * r ^ 2 * P ^ 2 + r ^ 2 * P * rv + r * w ^ 2 * P + r * w * P * xv + r * P ^ 3
  + 2 * r * P ^ 2 * rv - w * P ^ 2 * xv + P ^ 3 * rv - P ^ 2 * xv ^ 2 + r ^ 2 * κ + r * P * q
  + 2 * r * P * κ - r * q * rv + P ^ 2 * q + P ^ 2 * κ - P * q * rv

/-- `L = P |z_t|² + e w (r x_v − r_v w) + κ (r + r_v)`, `z_t = (r + r_v) + j (w + x_v)`. -/
def lineTerm (r w P e _q κ rv xv : ℝ) : ℝ :=
  P * ((r + rv) ^ 2 + (w + xv) ^ 2) + e * w * (r * xv - rv * w) + κ * (r + rv)

/-- The cross term `G` of the third condition (42 terms). -/
def cross (r w P e _q κ rv xv : ℝ) : ℝ :=
  r * w ^ 2 * P * e ^ 2 * rv + w ^ 2 * P * e ^ 2 * rv ^ 2 - 2 * r ^ 2 * w * P * e * xv
  - 2 * r * w ^ 2 * P ^ 2 * e - 3 * r * w * P ^ 2 * e * xv - 3 * r * w * P * e * rv * xv
  - 2 * w ^ 2 * P ^ 2 * e * rv - 3 * w * P ^ 2 * e * rv * xv - w * P * e * rv ^ 2 * xv
  - r ^ 3 * P ^ 2 + r ^ 3 * P * rv + r ^ 3 * xv ^ 2 + 4 * r ^ 2 * w * P * xv
  - 2 * r ^ 2 * w * rv * xv - r ^ 2 * P ^ 3 - r ^ 2 * P ^ 2 * rv + 2 * r ^ 2 * P * rv ^ 2
  + 5 * r ^ 2 * P * xv ^ 2 + 3 * r * w ^ 2 * P ^ 2 - 3 * r * w ^ 2 * P * rv + r * w ^ 2 * rv ^ 2
  + 9 * r * w * P ^ 2 * xv - 3 * r * w * P * rv * xv - 2 * r * P ^ 3 * rv + r * P ^ 2 * rv ^ 2
  + 6 * r * P ^ 2 * xv ^ 2 + r * P * rv ^ 3 + 2 * r * P * rv * xv ^ 2 + w ^ 2 * P ^ 3
  + 2 * w * P ^ 3 * xv + 3 * w * P ^ 2 * rv * xv - w * P * rv ^ 2 * xv - P ^ 3 * rv ^ 2
  + P ^ 3 * xv ^ 2 + P ^ 2 * rv ^ 3 + 3 * P ^ 2 * rv * xv ^ 2 - r ^ 2 * P * κ
  + r ^ 2 * κ * rv - r * P ^ 2 * κ + r * κ * rv ^ 2 - P ^ 2 * κ * rv + P * κ * rv ^ 2

/-- The third condition `q (Δ₄ L + q ((P − r_v)² (r + r_v) q − G))`. -/
def third (r w P e q κ rv xv : ℝ) : ℝ :=
  q * (delta4 r w P e q κ rv xv * lineTerm r w P e q κ rv xv +
    q * ((P - rv) ^ 2 * (r + rv) * q - cross r w P e q κ rv xv))

end VoltageLevel

namespace Params

variable (p : Params)

/-- **The Routh–Hurwitz conditions of the voltage level in normalized parameters**
(`C_f, L_g ≠ 0`, every `k_ff`, `k_dv`, `Z_v`): with `r = R_g/L_g`, `w = ω₀`, `P = K_pv/C_f`,
`e = 1 − k_dv`, `q = K_iv/C_f`, `κ = (1 − k_ff)/(C_f L_g)`, `r_v = R_v/L_g`, `x_v = X_v/L_g`, the
second condition is `VoltageLevel.delta4` and `complexCubicDet a₂ a₁ a₀ = VoltageLevel.third`. -/
@[tmio M, powerlib_domain] theorem voltage_routh_eq (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0) :
    p.voltageA2.re * (p.voltageA1.re * p.voltageA2.re + p.voltageA1.im * p.voltageA2.im -
        p.voltageA0.re) - p.voltageA1.im ^ 2 =
      VoltageLevel.delta4 (p.Rg / p.Lg) p.ω0 (p.Kpv / p.Cf) (1 - p.kdv) (p.Kiv / p.Cf)
        ((1 - p.kff) / (p.Cf * p.Lg)) (p.Rv / p.Lg) (p.Xv / p.Lg) ∧
      Criteria.complexCubicDet p.voltageA2 p.voltageA1 p.voltageA0 =
        VoltageLevel.third (p.Rg / p.Lg) p.ω0 (p.Kpv / p.Cf) (1 - p.kdv) (p.Kiv / p.Cf)
          ((1 - p.kff) / (p.Cf * p.Lg)) (p.Rv / p.Lg) (p.Xv / p.Lg) := by
  obtain ⟨r2, i2, r1, i1, r0, i0⟩ := p.voltageA_parts hCf hLg
  refine ⟨?_, ?_⟩
  · rw [r2, i2, r1, i1, r0]
    simp only [VoltageLevel.delta4]
    field_simp
    ring
  · rw [Criteria.complexCubicDet, r2, i2, r1, i1, r0, i0]
    simp only [VoltageLevel.third, VoltageLevel.delta4, VoltageLevel.lineTerm, VoltageLevel.cross]
    field_simp
    ring

/-- **The voltage level, exactly, in normalized parameters** (`C_f, L_g ≠ 0`, every `k_ff`,
`k_dv`, `Z_v`): its real form is spectrally stable iff `r + P > 0`, `VoltageLevel.delta4 > 0` and
`VoltageLevel.third > 0`. -/
@[tmio M, powerlib_domain] theorem spectrallyStable_voltageMatrix_iff_normalized (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) :
    Linear.SpectrallyStable (realify p.voltageMatrix) ↔
      0 < p.Rg / p.Lg + p.Kpv / p.Cf ∧
        0 < VoltageLevel.delta4 (p.Rg / p.Lg) p.ω0 (p.Kpv / p.Cf) (1 - p.kdv) (p.Kiv / p.Cf)
          ((1 - p.kff) / (p.Cf * p.Lg)) (p.Rv / p.Lg) (p.Xv / p.Lg) ∧
        0 < VoltageLevel.third (p.Rg / p.Lg) p.ω0 (p.Kpv / p.Cf) (1 - p.kdv) (p.Kiv / p.Cf)
          ((1 - p.kff) / (p.Cf * p.Lg)) (p.Rv / p.Lg) (p.Xv / p.Lg) := by
  obtain ⟨e4, e6⟩ := p.voltage_routh_eq hCf hLg
  rw [p.spectrallyStable_voltageMatrix_iff_routh hCf hLg, ← e4, ← e6,
    (p.voltageA_parts hCf hLg).1]

end Params

/-! ### Checks at the witness and at the faster current loop -/

/-- **The decision at the witness**: `Δ₂ = 21/10 > 0` and `Δ₄ = −2257/1000 < 0`, so the
boundary layer of `blWitness` is not spectrally stable — in agreement with its eigenvalue
`1 + 3j` (`blWitness_not_spectrallyStable`). -/
@[tmio M, powerlib_domain] theorem blWitness_fastDelta :
    blWitness.fastDelta 0 = 21 / 10 ∧ blWitness.fastDelta 1 = -2257 / 1000 := by
  have hLf : blWitness.Lf ≠ 0 := by norm_num [blWitness]
  have hCf : blWitness.Cf ≠ 0 := by norm_num [blWitness]
  have hLg : blWitness.Lg ≠ 0 := by norm_num [blWitness]
  rw [blWitness.fastDelta_zero hLf hCf hLg, blWitness.fastDelta_one hLf hCf hLg]
  norm_num [blWitness, FastLevel.delta4, Params.Zv]

/-! ### The exact threshold of the witness family -/

/-- The polynomial `R(t)` of the threshold of the witness family `blWitness.currentScaled (1/t)`:
its last Bilharz determinant is `128/31640625 · t⁵ R(t)` (`blFamily_fastDelta`). -/
def blThresholdPoly (t : ℝ) : ℝ :=
  2190049276800 * t ^ 11 - 2843296542240 * t ^ 10 - 63737204464872 * t ^ 9
  - 147772050603518 * t ^ 8 + 681787966982599 * t ^ 7 + 2410869564820880 * t ^ 6
  + 679706604013275 * t ^ 5 - 8234805387546750 * t ^ 4 - 176272201942500 * t ^ 3
  + 3593275195500000 * t ^ 2 + 456167497500000 * t - 209952000000000

/-- The factor of `Δ₄` of the witness family (`blFamily_fastDelta`). -/
private def blR4 (t : ℝ) : ℝ :=
  2420 * t ^ 4 + 1683 * t ^ 3 - 14560 * t ^ 2 - 1800 * t + 10000

/-- The factor of `Δ₆` of the witness family (`blFamily_fastDelta`). -/
private def blR6 (t : ℝ) : ℝ :=
  12487200 * t ^ 7 - 8791200 * t ^ 6 - 245181462 * t ^ 5 - 208970839 * t ^ 4 + 1164646990 * t ^ 3
  + 324891300 * t ^ 2 - 3994140000 * t + 768900000

/-- The factor of `Δ₈` of the witness family (`blFamily_fastDelta`). -/
private def blR8 (t : ℝ) : ℝ :=
  71367542400 * t ^ 10 - 81811324320 * t ^ 9 - 2008407531096 * t ^ 8 - 4011256434014 * t ^ 7
  + 18857285841937 * t ^ 6 + 59053299404225 * t ^ 5 - 3212809286850 * t ^ 4
  - 166382747026500 * t ^ 3 + 14179579800000 * t ^ 2 + 27026365500000 * t - 4665600000000

/-- The coefficients of the witness family `blWitness.currentScaled t⁻¹` (`t > 0`): `k_p = t`,
`k_i = 2t²`, `ρ = t/10`, `r = w = 1`, `c = 10`, `P = 28/15`, `q = 24`, the ideal design. -/
@[tmio M, powerlib_domain] private theorem blFamily_fastCoeff {t : ℝ} (ht : 0 < t) :
    (blWitness.currentScaled t⁻¹).fastCoeff =
      FastLevel.coeffs t (2 * t ^ 2) (t / 10) 1 1 10 (28 / 15) 0 24 0 0 0 := by
  have hLf : (blWitness.currentScaled t⁻¹).Lf ≠ 0 := by
    simp [Params.currentScaled, blWitness, ht.ne']
  have hCf : (blWitness.currentScaled t⁻¹).Cf ≠ 0 := by norm_num [Params.currentScaled, blWitness]
  have hLg : (blWitness.currentScaled t⁻¹).Lg ≠ 0 := by norm_num [Params.currentScaled, blWitness]
  rw [(blWitness.currentScaled t⁻¹).fastCoeff_eq hLf hCf hLg]
  have ht' : t ≠ 0 := ht.ne'
  congr 1 <;> simp [Params.currentScaled, blWitness] <;> field_simp

/-- `Δ₂` of the witness family. -/
@[tmio M, powerlib_domain] private theorem blFamily_fastDelta0 {t : ℝ} (ht : 0 < t) :
    (blWitness.currentScaled t⁻¹).fastDelta 0 = (11 * t + 10) / 10 := by
  rw [Params.fastDelta, blFamily_fastCoeff ht]
  simp only [FastLevel.coeffs, Criteria.quinticBilharz2, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  simp only [Criteria.BilharzPoly.quintic2]
  ring

/-- `Δ₄` of the witness family. -/
@[tmio M, powerlib_domain] private theorem blFamily_fastDelta1 {t : ℝ} (ht : 0 < t) :
    (blWitness.currentScaled t⁻¹).fastDelta 1 = blR4 t / 1000 := by
  rw [Params.fastDelta, blFamily_fastCoeff ht]
  simp only [FastLevel.coeffs, Criteria.quinticBilharz4, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  simp only [Criteria.BilharzPoly.quintic4, blR4]
  ring

/-- `Δ₆` of the witness family. -/
@[tmio M, powerlib_domain] private theorem blFamily_fastDelta2 {t : ℝ} (ht : 0 < t) :
    (blWitness.currentScaled t⁻¹).fastDelta 2 = t * blR6 t / 450000 := by
  rw [Params.fastDelta, blFamily_fastCoeff ht]
  simp only [FastLevel.coeffs, Criteria.quinticBilharz6, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  simp only [Criteria.BilharzPoly.quintic6, blR6]
  ring

/-- `Δ₈` of the witness family. -/
@[tmio M, powerlib_domain] private theorem blFamily_fastDelta3 {t : ℝ} (ht : 0 < t) :
    (blWitness.currentScaled t⁻¹).fastDelta 3 = t ^ 2 * blR8 t / 12656250 := by
  rw [Params.fastDelta, blFamily_fastCoeff ht]
  simp only [FastLevel.coeffs, Criteria.quinticBilharz8, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  simp only [Criteria.BilharzPoly.quintic8, Criteria.BilharzPoly.quintic8_0,
    Criteria.BilharzPoly.quintic8_1, Criteria.BilharzPoly.quintic8_2,
    Criteria.BilharzPoly.quintic8_3, Criteria.BilharzPoly.quintic8_4, blR8]
  ring

/-- `Δ₁₀` of the witness family. -/
@[tmio M, powerlib_domain] private theorem blFamily_fastDelta4 {t : ℝ} (ht : 0 < t) :
    (blWitness.currentScaled t⁻¹).fastDelta 4 = 128 * t ^ 5 * blThresholdPoly t / 31640625 := by
  rw [Params.fastDelta, blFamily_fastCoeff ht]
  simp only [FastLevel.coeffs, Criteria.quinticBilharz10, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  simp only [Criteria.BilharzPoly.quintic10, Criteria.BilharzPoly.quintic10_0,
    Criteria.BilharzPoly.quintic10_1, Criteria.BilharzPoly.quintic10_2,
    Criteria.BilharzPoly.quintic10_3, Criteria.BilharzPoly.quintic10_4,
    Criteria.BilharzPoly.quintic10_5, Criteria.BilharzPoly.quintic10_6,
    Criteria.BilharzPoly.quintic10_7, Criteria.BilharzPoly.quintic10_8,
    Criteria.BilharzPoly.quintic10_9, Criteria.BilharzPoly.quintic10_10,
    Criteria.BilharzPoly.quintic10_11, Criteria.BilharzPoly.quintic10_12,
    Criteria.BilharzPoly.quintic10_13, blThresholdPoly]
  ring

/-- `R₈ < 0` on `(0, 1/5]` (Bernstein coefficients on `[0, 1/5]`, all negative). -/
@[tmio M, powerlib_domain] private theorem blR8_neg {t : ℝ} (h1 : 0 < t)
    (h2 : t ≤ (1 / 5)) : blR8 t < 0 := by
  have hpos : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → 0 < x + y →
      0 <
        4665600000000 * y ^ 10 + 41250726900000 * x * y ^ 9 + 160737358908000 * x ^ 2 * y ^ 8
        + 362075764840212 * x ^ 3 * y ^ 7 + (12979362613808574 / 25) * x ^ 4 * y ^ 6
        + (61358597257724551 / 125) * x ^ 5 * y ^ 5
        + (4774646100077558688 / 15625) * x ^ 6 * y ^ 4
        + (9418986971360351524 / 78125) * x ^ 7 * y ^ 3
        + (10669685689550750756 / 390625) * x ^ 8 * y ^ 2
        + (1062580070154877941 / 390625) * x ^ 9 * y + (3632334825281534 / 390625) * x ^ 10 := by
    intro x y hx hy hxy
    rcases hx.lt_or_eq with hx' | hx'
    · positivity
    · have hy' : 0 < y := by linarith
      positivity
  have key : blR8 t * ((1 / 5) - 0) ^ 10 = -(
      4665600000000 * ((1 / 5) - t) ^ 10 + 41250726900000 * t * ((1 / 5) - t) ^ 9
      + 160737358908000 * t ^ 2 * ((1 / 5) - t) ^ 8 + 362075764840212 * t ^ 3 * ((1 / 5) - t) ^ 7
      + (12979362613808574 / 25) * t ^ 4 * ((1 / 5) - t) ^ 6
      + (61358597257724551 / 125) * t ^ 5 * ((1 / 5) - t) ^ 5
      + (4774646100077558688 / 15625) * t ^ 6 * ((1 / 5) - t) ^ 4
      + (9418986971360351524 / 78125) * t ^ 7 * ((1 / 5) - t) ^ 3
      + (10669685689550750756 / 390625) * t ^ 8 * ((1 / 5) - t) ^ 2
      + (1062580070154877941 / 390625) * t ^ 9 * ((1 / 5) - t)
      + (3632334825281534 / 390625) * t ^ 10) := by
    unfold blR8; ring
  have hS := hpos t ((1 / 5) - t) (by linarith) (by linarith) (by linarith)
  have hc : (0 : ℝ) < ((1 / 5) - 0) ^ 10 := by norm_num
  nlinarith

/-- `R₆ < 0` on `[1/5, 99/40]` (Bernstein coefficients, all negative). -/
@[tmio M, powerlib_domain] private theorem blR6_neg_left {t : ℝ} (h1 : (1 / 5) ≤ t)
    (h2 : t ≤ (99 / 40)) : blR6 t < 0 := by
  have hpos : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → 0 < x + y →
      0 <
        (25088707159 / 3125) * y ^ 7 + (26715526704566 / 3125) * x * y ^ 6
        + (11547195545781 / 250) * x ^ 2 * y ^ 5 + (14785392594600467 / 160000) * x ^ 3 * y ^ 4
        + (232085571738983389 / 2560000) * x ^ 4 * y ^ 3
        + (3394054655558868693 / 51200000) * x ^ 5 * y ^ 2
        + (1262812004220933201 / 25600000) * x ^ 6 * y + (614297280190593813 / 40960000) * x ^ 7
          := by
    intro x y hx hy hxy
    rcases hx.lt_or_eq with hx' | hx'
    · positivity
    · have hy' : 0 < y := by linarith
      positivity
  have key : blR6 t * ((99 / 40) - (1 / 5)) ^ 7 = -(
      (25088707159 / 3125) * ((99 / 40) - t) ^ 7
      + (26715526704566 / 3125) * (t - (1 / 5)) * ((99 / 40) - t) ^ 6
      + (11547195545781 / 250) * (t - (1 / 5)) ^ 2 * ((99 / 40) - t) ^ 5
      + (14785392594600467 / 160000) * (t - (1 / 5)) ^ 3 * ((99 / 40) - t) ^ 4
      + (232085571738983389 / 2560000) * (t - (1 / 5)) ^ 4 * ((99 / 40) - t) ^ 3
      + (3394054655558868693 / 51200000) * (t - (1 / 5)) ^ 5 * ((99 / 40) - t) ^ 2
      + (1262812004220933201 / 25600000) * (t - (1 / 5)) ^ 6 * ((99 / 40) - t)
      + (614297280190593813 / 40960000) * (t - (1 / 5)) ^ 7) := by
    unfold blR6; ring
  have hS := hpos (t - (1 / 5)) ((99 / 40) - t) (by linarith) (by linarith) (by linarith)
  have hc : (0 : ℝ) < ((99 / 40) - (1 / 5)) ^ 7 := by norm_num
  nlinarith

/-- `R₆ < 0` on `[99/40, 19/4]` (Bernstein coefficients, all negative). -/
@[tmio M, powerlib_domain] private theorem blR6_neg_right {t : ℝ} (h1 : (99 / 40) ≤ t)
    (h2 : t ≤ (19 / 4)) : blR6 t < 0 := by
  have hpos : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → 0 < x + y →
      0 <
        (614297280190593813 / 40960000) * y ^ 7 + (16449156789787050651 / 102400000) * x * y ^ 6
        + (18793890487134411117 / 25600000) * x ^ 2 * y ^ 5
        + (4638272134050243479 / 2560000) * x ^ 3 * y ^ 4
        + (1292680751571065997 / 512000) * x ^ 4 * y ^ 3
        + (96006339477905283 / 51200) * x ^ 5 * y ^ 2 + (372880324741799 / 640) * x ^ 6 * y
        + (320175110469 / 64) * x ^ 7 := by
    intro x y hx hy hxy
    rcases hx.lt_or_eq with hx' | hx'
    · positivity
    · have hy' : 0 < y := by linarith
      positivity
  have key : blR6 t * ((19 / 4) - (99 / 40)) ^ 7 = -(
      (614297280190593813 / 40960000) * ((19 / 4) - t) ^ 7
      + (16449156789787050651 / 102400000) * (t - (99 / 40)) * ((19 / 4) - t) ^ 6
      + (18793890487134411117 / 25600000) * (t - (99 / 40)) ^ 2 * ((19 / 4) - t) ^ 5
      + (4638272134050243479 / 2560000) * (t - (99 / 40)) ^ 3 * ((19 / 4) - t) ^ 4
      + (1292680751571065997 / 512000) * (t - (99 / 40)) ^ 4 * ((19 / 4) - t) ^ 3
      + (96006339477905283 / 51200) * (t - (99 / 40)) ^ 5 * ((19 / 4) - t) ^ 2
      + (372880324741799 / 640) * (t - (99 / 40)) ^ 6 * ((19 / 4) - t)
      + (320175110469 / 64) * (t - (99 / 40)) ^ 7) := by
    unfold blR6; ring
  have hS := hpos (t - (99 / 40)) ((19 / 4) - t) (by linarith) (by linarith) (by linarith)
  have hc : (0 : ℝ) < ((19 / 4) - (99 / 40)) ^ 7 := by norm_num
  nlinarith

/-- `R < 0` on `[19/4, 107/20]` (Bernstein coefficients, all negative). -/
@[tmio M, powerlib_domain] private theorem blThresholdPoly_neg {t : ℝ} (h1 : (19 / 4) ≤ t)
    (h2 : t ≤ (107 / 20)) : blThresholdPoly t < 0 := by
  have hpos : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → 0 < x + y →
      0 <
        (41570762755904261228711 / 4096) * y ^ 11
        + (2523281169962290415632247 / 20480) * x * y ^ 10
        + (69186707458883384266697333 / 102400) * x ^ 2 * y ^ 9
        + (1130908869904267625727657117 / 512000) * x ^ 3 * y ^ 8
        + (6119913715324900623936936411 / 1280000) * x ^ 4 * y ^ 7
        + (46025016656299988485444897659 / 6400000) * x ^ 5 * y ^ 6
        + (245245486110262416631939496493 / 32000000) * x ^ 6 * y ^ 5
        + (924993627077719334371622149317 / 160000000) * x ^ 7 * y ^ 4
        + (4833753471641529738739014259731 / 1600000000) * x ^ 8 * y ^ 3
        + (8317583464320739878560722124611 / 8000000000) * x ^ 9 * y ^ 2
        + (1692282773209500466688277191309 / 8000000000) * x ^ 10 * y
        + (153643358080315100063752364689 / 8000000000) * x ^ 11 := by
    intro x y hx hy hxy
    rcases hx.lt_or_eq with hx' | hx'
    · positivity
    · have hy' : 0 < y := by linarith
      positivity
  have key : blThresholdPoly t * ((107 / 20) - (19 / 4)) ^ 11 = -(
      (41570762755904261228711 / 4096) * ((107 / 20) - t) ^ 11
      + (2523281169962290415632247 / 20480) * (t - (19 / 4)) * ((107 / 20) - t) ^ 10
      + (69186707458883384266697333 / 102400) * (t - (19 / 4)) ^ 2 * ((107 / 20) - t) ^ 9
      + (1130908869904267625727657117 / 512000) * (t - (19 / 4)) ^ 3 * ((107 / 20) - t) ^ 8
      + (6119913715324900623936936411 / 1280000) * (t - (19 / 4)) ^ 4 * ((107 / 20) - t) ^ 7
      + (46025016656299988485444897659 / 6400000) * (t - (19 / 4)) ^ 5 * ((107 / 20) - t) ^ 6
      + (245245486110262416631939496493 / 32000000) * (t - (19 / 4)) ^ 6 * ((107 / 20) - t) ^ 5
      + (924993627077719334371622149317 / 160000000) * (t - (19 / 4)) ^ 7 * ((107 / 20) - t) ^ 4
      + (4833753471641529738739014259731 / 1600000000) * (t - (19 / 4)) ^ 8 * ((107 / 20) - t) ^ 3
      + (8317583464320739878560722124611 / 8000000000) * (t - (19 / 4)) ^ 9 * ((107 / 20) - t) ^ 2
      + (1692282773209500466688277191309 / 8000000000) * (t - (19 / 4)) ^ 10 * ((107 / 20) - t)
      + (153643358080315100063752364689 / 8000000000) * (t - (19 / 4)) ^ 11) := by
    unfold blThresholdPoly; ring
  have hS := hpos (t - (19 / 4)) ((107 / 20) - t) (by linarith) (by linarith) (by linarith)
  have hc : (0 : ℝ) < ((107 / 20) - (19 / 4)) ^ 11 := by norm_num
  nlinarith

/-- `R₄` is positive on `[29/5, ∞)` (all Taylor coefficients at `29/5` positive). -/
@[tmio M, powerlib_domain] private theorem blR4_pos {t : ℝ} (h : 29 / 5 ≤ t) : 0 < blR4 t := by
  have hpos : ∀ u : ℝ, 0 ≤ u → 0 <
      (322090891 / 125) + (47195913 / 25) * u + 503177 * u ^ 2 + 57827 * u ^ 3 + 2420 * u ^ 4
        := fun u hu => by positivity
  have key : blR4 t =
      (322090891 / 125) + (47195913 / 25) * (t - 29 / 5) + 503177 * (t - 29 / 5) ^ 2
      + 57827 * (t - 29 / 5) ^ 3 + 2420 * (t - 29 / 5) ^ 4 := by
    unfold blR4; ring
  rw [key]; exact hpos _ (by linarith)

/-- `R₆` is positive on `[29/5, ∞)` (all Taylor coefficients at `29/5` positive). -/
@[tmio M, powerlib_domain] private theorem blR6_pos {t : ℝ} (h : 29 / 5 ≤ t) : 0 < blR6 t := by
  have hpos : ∀ u : ℝ, 0 ≤ u → 0 <
      (2476582651791369 / 3125) + (967695130358696 / 625) * u + (133997060024952 / 125) * u ^ 2
      + (1870609141998 / 5) * u ^ 3 + 73518817067 * u ^ 4 + 8270342346 * u ^ 5 + 498189120 * u ^ 6
      + 12487200 * u ^ 7 := fun u hu => by positivity
  have key : blR6 t =
      (2476582651791369 / 3125) + (967695130358696 / 625) * (t - 29 / 5)
      + (133997060024952 / 125) * (t - 29 / 5) ^ 2 + (1870609141998 / 5) * (t - 29 / 5) ^ 3
      + 73518817067 * (t - 29 / 5) ^ 4 + 8270342346 * (t - 29 / 5) ^ 5
      + 498189120 * (t - 29 / 5) ^ 6 + 12487200 * (t - 29 / 5) ^ 7 := by
    unfold blR6; ring
  rw [key]; exact hpos _ (by linarith)

/-- `R₈` is positive on `[29/5, ∞)` (all Taylor coefficients at `29/5` positive). -/
@[tmio M, powerlib_domain] private theorem blR8_pos {t : ℝ} (h : 29 / 5 ≤ t) : 0 < blR8 t := by
  have hpos : ∀ u : ℝ, 0 ≤ u → 0 <
      (30926598556365312008494 / 390625) + (62430883521717156332977 / 78125) * u
      + (18759182546182125966131 / 15625) * u ^ 2 + (515906662677476203512 / 625) * u ^ 3
      + (204761856834243123504 / 625) * u ^ 4 + (2057878553398779833 / 25) * u ^ 5
      + (339591063742956503 / 25) * u ^ 6 + (7373407599242474 / 5) * u ^ 7
      + 101757227024520 * u ^ 8 + 4057506134880 * u ^ 9 + 71367542400 * u ^ 10
        := fun u hu => by positivity
  have key : blR8 t =
      (30926598556365312008494 / 390625) + (62430883521717156332977 / 78125) * (t - 29 / 5)
      + (18759182546182125966131 / 15625) * (t - 29 / 5) ^ 2
      + (515906662677476203512 / 625) * (t - 29 / 5) ^ 3
      + (204761856834243123504 / 625) * (t - 29 / 5) ^ 4
      + (2057878553398779833 / 25) * (t - 29 / 5) ^ 5
      + (339591063742956503 / 25) * (t - 29 / 5) ^ 6 + (7373407599242474 / 5) * (t - 29 / 5) ^ 7
      + 101757227024520 * (t - 29 / 5) ^ 8 + 4057506134880 * (t - 29 / 5) ^ 9
      + 71367542400 * (t - 29 / 5) ^ 10 := by
    unfold blR8; ring
  rw [key]; exact hpos _ (by linarith)

/-- The Taylor form of `R` at `107/20`: its coefficient of order `0` is negative, all others
positive. -/
@[tmio M, powerlib_domain] private theorem blThresholdPoly_taylor (u : ℝ) :
    blThresholdPoly (107 / 20 + u) =
      -(153643358080315100063752364689 / 8000000000)
      + (73527810867812199566705991 / 160000000) * u
      + (2150827407735198400217635147 / 40000000) * u ^ 2
      + (518920789335737393990303761 / 8000000) * u ^ 3
      + (7538081571115004696845881 / 200000) * u ^ 4 + (132266237869285740790211 / 10000) * u ^ 5
      + (1517602662280541577089 / 500) * u ^ 6 + (11712944457274219992 / 25) * u ^ 7
      + (242279930629516796 / 5) * u ^ 8 + 3231804128911728 * u ^ 9 + 126041103397440 * u ^ 10
      + 2190049276800 * u ^ 11 := by
  unfold blThresholdPoly; ring

/-- The divided difference of the Taylor form: a polynomial in `u, v` with positive coefficients. -/
@[tmio M, powerlib_domain] private theorem blThreshold_diff (u v : ℝ) :
    (73527810867812199566705991 / 160000000) * (v - u)
    + (2150827407735198400217635147 / 40000000) * (v ^ 2 - u ^ 2)
    + (518920789335737393990303761 / 8000000) * (v ^ 3 - u ^ 3)
    + (7538081571115004696845881 / 200000) * (v ^ 4 - u ^ 4)
    + (132266237869285740790211 / 10000) * (v ^ 5 - u ^ 5)
    + (1517602662280541577089 / 500) * (v ^ 6 - u ^ 6)
    + (11712944457274219992 / 25) * (v ^ 7 - u ^ 7) + (242279930629516796 / 5) * (v ^ 8 - u ^ 8)
    + 3231804128911728 * (v ^ 9 - u ^ 9) + 126041103397440 * (v ^ 10 - u ^ 10)
    + 2190049276800 * (v ^ 11 - u ^ 11) =
      (v - u) * (
        (73527810867812199566705991 / 160000000) + (2150827407735198400217635147 / 40000000) * v
        + (2150827407735198400217635147 / 40000000) * u
        + (518920789335737393990303761 / 8000000) * v ^ 2
        + (518920789335737393990303761 / 8000000) * u * v
        + (518920789335737393990303761 / 8000000) * u ^ 2
        + (7538081571115004696845881 / 200000) * v ^ 3
        + (7538081571115004696845881 / 200000) * u * v ^ 2
        + (7538081571115004696845881 / 200000) * u ^ 2 * v
        + (7538081571115004696845881 / 200000) * u ^ 3
        + (132266237869285740790211 / 10000) * v ^ 4
        + (132266237869285740790211 / 10000) * u * v ^ 3
        + (132266237869285740790211 / 10000) * u ^ 2 * v ^ 2
        + (132266237869285740790211 / 10000) * u ^ 3 * v
        + (132266237869285740790211 / 10000) * u ^ 4 + (1517602662280541577089 / 500) * v ^ 5
        + (1517602662280541577089 / 500) * u * v ^ 4
        + (1517602662280541577089 / 500) * u ^ 2 * v ^ 3
        + (1517602662280541577089 / 500) * u ^ 3 * v ^ 2
        + (1517602662280541577089 / 500) * u ^ 4 * v + (1517602662280541577089 / 500) * u ^ 5
        + (11712944457274219992 / 25) * v ^ 6 + (11712944457274219992 / 25) * u * v ^ 5
        + (11712944457274219992 / 25) * u ^ 2 * v ^ 4
        + (11712944457274219992 / 25) * u ^ 3 * v ^ 3
        + (11712944457274219992 / 25) * u ^ 4 * v ^ 2 + (11712944457274219992 / 25) * u ^ 5 * v
        + (11712944457274219992 / 25) * u ^ 6 + (242279930629516796 / 5) * v ^ 7
        + (242279930629516796 / 5) * u * v ^ 6 + (242279930629516796 / 5) * u ^ 2 * v ^ 5
        + (242279930629516796 / 5) * u ^ 3 * v ^ 4 + (242279930629516796 / 5) * u ^ 4 * v ^ 3
        + (242279930629516796 / 5) * u ^ 5 * v ^ 2 + (242279930629516796 / 5) * u ^ 6 * v
        + (242279930629516796 / 5) * u ^ 7 + 3231804128911728 * v ^ 8
        + 3231804128911728 * u * v ^ 7 + 3231804128911728 * u ^ 2 * v ^ 6
        + 3231804128911728 * u ^ 3 * v ^ 5 + 3231804128911728 * u ^ 4 * v ^ 4
        + 3231804128911728 * u ^ 5 * v ^ 3 + 3231804128911728 * u ^ 6 * v ^ 2
        + 3231804128911728 * u ^ 7 * v + 3231804128911728 * u ^ 8 + 126041103397440 * v ^ 9
        + 126041103397440 * u * v ^ 8 + 126041103397440 * u ^ 2 * v ^ 7
        + 126041103397440 * u ^ 3 * v ^ 6 + 126041103397440 * u ^ 4 * v ^ 5
        + 126041103397440 * u ^ 5 * v ^ 4 + 126041103397440 * u ^ 6 * v ^ 3
        + 126041103397440 * u ^ 7 * v ^ 2 + 126041103397440 * u ^ 8 * v + 126041103397440 * u ^ 9
        + 2190049276800 * v ^ 10 + 2190049276800 * u * v ^ 9 + 2190049276800 * u ^ 2 * v ^ 8
        + 2190049276800 * u ^ 3 * v ^ 7 + 2190049276800 * u ^ 4 * v ^ 6
        + 2190049276800 * u ^ 5 * v ^ 5 + 2190049276800 * u ^ 6 * v ^ 4
        + 2190049276800 * u ^ 7 * v ^ 3 + 2190049276800 * u ^ 8 * v ^ 2
        + 2190049276800 * u ^ 9 * v + 2190049276800 * u ^ 10) := by
  ring

/-- `R` is strictly increasing on `[107/20, ∞)` (`blThresholdPoly_taylor`, `blThreshold_diff`). -/
@[tmio M, powerlib_domain] private theorem blThresholdPoly_lt {x y : ℝ} (hx : 107 / 20 ≤ x)
    (hxy : x < y) : blThresholdPoly x < blThresholdPoly y := by
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 ≤ u ∧ x = 107 / 20 + u := ⟨x - 107 / 20, by linarith, by ring⟩
  obtain ⟨v, hv, rfl⟩ : ∃ v, 0 ≤ v ∧ y = 107 / 20 + v := ⟨y - 107 / 20, by linarith, by ring⟩
  have hS : 0 <
      (73527810867812199566705991 / 160000000) + (2150827407735198400217635147 / 40000000) * v
      + (2150827407735198400217635147 / 40000000) * u
      + (518920789335737393990303761 / 8000000) * v ^ 2
      + (518920789335737393990303761 / 8000000) * u * v
      + (518920789335737393990303761 / 8000000) * u ^ 2
      + (7538081571115004696845881 / 200000) * v ^ 3
      + (7538081571115004696845881 / 200000) * u * v ^ 2
      + (7538081571115004696845881 / 200000) * u ^ 2 * v
      + (7538081571115004696845881 / 200000) * u ^ 3 + (132266237869285740790211 / 10000) * v ^ 4
      + (132266237869285740790211 / 10000) * u * v ^ 3
      + (132266237869285740790211 / 10000) * u ^ 2 * v ^ 2
      + (132266237869285740790211 / 10000) * u ^ 3 * v
      + (132266237869285740790211 / 10000) * u ^ 4 + (1517602662280541577089 / 500) * v ^ 5
      + (1517602662280541577089 / 500) * u * v ^ 4
      + (1517602662280541577089 / 500) * u ^ 2 * v ^ 3
      + (1517602662280541577089 / 500) * u ^ 3 * v ^ 2
      + (1517602662280541577089 / 500) * u ^ 4 * v + (1517602662280541577089 / 500) * u ^ 5
      + (11712944457274219992 / 25) * v ^ 6 + (11712944457274219992 / 25) * u * v ^ 5
      + (11712944457274219992 / 25) * u ^ 2 * v ^ 4 + (11712944457274219992 / 25) * u ^ 3 * v ^ 3
      + (11712944457274219992 / 25) * u ^ 4 * v ^ 2 + (11712944457274219992 / 25) * u ^ 5 * v
      + (11712944457274219992 / 25) * u ^ 6 + (242279930629516796 / 5) * v ^ 7
      + (242279930629516796 / 5) * u * v ^ 6 + (242279930629516796 / 5) * u ^ 2 * v ^ 5
      + (242279930629516796 / 5) * u ^ 3 * v ^ 4 + (242279930629516796 / 5) * u ^ 4 * v ^ 3
      + (242279930629516796 / 5) * u ^ 5 * v ^ 2 + (242279930629516796 / 5) * u ^ 6 * v
      + (242279930629516796 / 5) * u ^ 7 + 3231804128911728 * v ^ 8 + 3231804128911728 * u * v ^ 7
      + 3231804128911728 * u ^ 2 * v ^ 6 + 3231804128911728 * u ^ 3 * v ^ 5
      + 3231804128911728 * u ^ 4 * v ^ 4 + 3231804128911728 * u ^ 5 * v ^ 3
      + 3231804128911728 * u ^ 6 * v ^ 2 + 3231804128911728 * u ^ 7 * v + 3231804128911728 * u ^ 8
      + 126041103397440 * v ^ 9 + 126041103397440 * u * v ^ 8 + 126041103397440 * u ^ 2 * v ^ 7
      + 126041103397440 * u ^ 3 * v ^ 6 + 126041103397440 * u ^ 4 * v ^ 5
      + 126041103397440 * u ^ 5 * v ^ 4 + 126041103397440 * u ^ 6 * v ^ 3
      + 126041103397440 * u ^ 7 * v ^ 2 + 126041103397440 * u ^ 8 * v + 126041103397440 * u ^ 9
      + 2190049276800 * v ^ 10 + 2190049276800 * u * v ^ 9 + 2190049276800 * u ^ 2 * v ^ 8
      + 2190049276800 * u ^ 3 * v ^ 7 + 2190049276800 * u ^ 4 * v ^ 6
      + 2190049276800 * u ^ 5 * v ^ 5 + 2190049276800 * u ^ 6 * v ^ 4
      + 2190049276800 * u ^ 7 * v ^ 3 + 2190049276800 * u ^ 8 * v ^ 2 + 2190049276800 * u ^ 9 * v
      + 2190049276800 * u ^ 10 := by positivity
  have huv : 0 < v - u := by linarith
  have h := mul_pos huv hS
  rw [← blThreshold_diff u v] at h
  rw [blThresholdPoly_taylor, blThresholdPoly_taylor]
  linarith

/-- **The exact stability threshold of the witness family.** There is `μ_c` with
`100/581 < μ_c < 5/29` and `R(1/μ_c) = 0` (`blThresholdPoly`, degree 11; `μ_c ≈ 0.172306`) such
that for every `μ > 0` the boundary layer of `blWitness.currentScaled μ` is spectrally stable at
every angle iff `μ < μ_c`. With `t = 1/μ`: `Δ₈ < 0` on `(0, 1/5]`, `Δ₆ < 0` on `[1/5, 19/4]`,
`Δ₁₀ ≤ 0` on `[19/4, 1/μ_c]`, and all five determinants are positive for `t > 1/μ_c`. -/
@[tmio M, powerlib_domain] theorem blWitness_currentScaled_threshold :
    ∃ μc : ℝ, 100 / 581 < μc ∧ μc < 5 / 29 ∧ blThresholdPoly μc⁻¹ = 0 ∧
      ∀ μ, 0 < μ →
        ((∀ δ, Linear.SpectrallyStable ((blWitness.currentScaled μ).fastBlock δ)) ↔ μ < μc) := by
  have hcont : Continuous blThresholdPoly := by unfold blThresholdPoly; fun_prop
  obtain ⟨tc, ⟨htc1, htc2⟩, hroot⟩ : ∃ tc ∈ Set.Ioo (29 / 5 : ℝ) (581 / 100),
      blThresholdPoly tc = 0 :=
    intermediate_value_Ioo (by norm_num) hcont.continuousOn
      ⟨by norm_num [blThresholdPoly], by norm_num [blThresholdPoly]⟩
  have htc0 : 0 < tc := by linarith
  refine ⟨tc⁻¹, ?_, ?_, by rw [inv_inv]; exact hroot, fun μ hμ => ?_⟩
  · rw [lt_inv_comm₀ (by norm_num) htc0]; norm_num; linarith
  · rw [inv_lt_comm₀ htc0 (by norm_num)]; norm_num; linarith
  have ht : 0 < μ⁻¹ := inv_pos.mpr hμ
  obtain ⟨t, rfl⟩ : ∃ t, μ = t⁻¹ := ⟨μ⁻¹, (inv_inv μ).symm⟩
  rw [inv_inv] at ht
  have hLf : (blWitness.currentScaled t⁻¹).Lf ≠ 0 := by
    simp [Params.currentScaled, blWitness, ht.ne']
  have hCf : (blWitness.currentScaled t⁻¹).Cf ≠ 0 := by norm_num [Params.currentScaled, blWitness]
  have hLg : (blWitness.currentScaled t⁻¹).Lg ≠ 0 := by norm_num [Params.currentScaled, blWitness]
  have hiff : (∀ δ, Linear.SpectrallyStable ((blWitness.currentScaled t⁻¹).fastBlock δ)) ↔
      ∀ k, 0 < (blWitness.currentScaled t⁻¹).fastDelta k :=
    ⟨fun h => ((blWitness.currentScaled t⁻¹).spectrallyStable_fastBlock_iff_fastDelta hLf hCf
      hLg 0).mp (h 0), fun h δ =>
      ((blWitness.currentScaled t⁻¹).spectrallyStable_fastBlock_iff_fastDelta hLf hCf hLg δ).mpr
        h⟩
  rw [hiff, inv_lt_inv₀ ht htc0, Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_succ,
    Fin.forall_fin_succ, Fin.forall_fin_one]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  rw [blFamily_fastDelta0 ht, blFamily_fastDelta1 ht]
  erw [blFamily_fastDelta2 ht, blFamily_fastDelta3 ht, blFamily_fastDelta4 ht]
  constructor
  · rintro ⟨-, -, h6, h8, h10⟩
    by_contra hle'
    have hle := not_lt.mp hle'
    rcases le_or_gt t (1 / 5) with h15 | h15
    · have := blR8_neg ht h15
      nlinarith [pow_pos ht 2]
    rcases le_or_gt t (19 / 4) with h194 | h194
    · have hR : blR6 t < 0 := by
        rcases le_or_gt t (99 / 40) with h | h
        · exact blR6_neg_left h15.le h
        · exact blR6_neg_right h.le h194
      nlinarith
    have hR : blThresholdPoly t ≤ 0 := by
      rcases le_or_gt t (107 / 20) with h | h
      · exact (blThresholdPoly_neg h194.le h).le
      · rcases hle.lt_or_eq with h' | h'
        · exact (blThresholdPoly_lt h.le h').le.trans hroot.le
        · rw [h', hroot]
    have h5 : 0 < t ^ 5 := pow_pos ht 5
    nlinarith
  · intro htc
    have h29 : 29 / 5 ≤ t := by linarith
    have hR : 0 < blThresholdPoly t := hroot ▸ blThresholdPoly_lt (by linarith) htc
    refine ⟨by positivity, by have := blR4_pos h29; positivity, ?_, ?_, ?_⟩
    · have := blR6_pos h29; positivity
    · have := blR8_pos h29; positivity
    · positivity

/-- **A ten times faster current loop stabilizes the witness's boundary layer**: the fast block of
`blWitness.currentScaled (1/10)` is spectrally stable at every angle (`1/10 < μ_c`,
`blWitness_currentScaled_threshold`), while that of `blWitness` is not
(`blWitness_not_spectrallyStable`). -/
@[tmio M, powerlib_domain] theorem blWitness_currentScaled_spectrallyStable (δ : ℝ) :
    Linear.SpectrallyStable ((blWitness.currentScaled (1 / 10)).fastBlock δ) := by
  obtain ⟨μc, h1, -, -, h⟩ := blWitness_currentScaled_threshold
  exact (h (1 / 10) (by norm_num)).mpr (by linarith) δ

end powerlib.GFM.FullModel
