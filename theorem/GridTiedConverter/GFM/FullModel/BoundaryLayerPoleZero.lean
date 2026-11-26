import theorem.GridTiedConverter.GFM.FullModel.BoundaryLayerRouth
import theorem.Dynamics.PolyIdentity

/-! # The 13-state grid-forming converter: the boundary layer with pole–zero cancellation

Model boundary.
The ten-state fast block `fastBlock δ` of
`theorem/GridTiedConverter/GFM/FullModel/BoundaryLayer.lean` (filter current, capacitor voltage,
line current, current- and voltage-loop integrators, dq, linearized in the fast states; the real
form of the complex `5 × 5` matrix `fastMatrix δ`) on the sub-family where the zero of the
current-loop PI cancels the filter pole, `K_ic/K_pc = R_f/L_f` (stated as `K_ic L_f = K_pc R_f`;
in normalized parameters `k_i = k_p ρ`), the standard tuning of the inner current loop. Every
other parameter is free, `L_f, C_f, L_g ≠ 0`: any feed-forward `k_ff`, decoupling `k_dv`, virtual
impedance `Z_v = R_v + jX_v`, any signs of gains and resistances. Normalized parameters as in
`theorem/GridTiedConverter/GFM/FullModel/BoundaryLayerRouth.lean`: `k_p = K_pc/L_f`,
`ρ = R_f/L_f`, `r = R_g/L_g`, `w = ω₀`, `c = 1/(C_f L_g)`, `P = K_pv/C_f`, `e = 1 − k_dv`,
`q = K_iv/C_f`, `κ = (1 − k_ff)/(C_f L_g)`, `r_v = R_v/L_g`, `x_v = X_v/L_g`. Continuous time,
constant matrices; excluded: everything excluded by the boundary layer of the full-order model.

Source: GFM counterpart study, full-order model note (t5: the boundary layer); the current-loop
tuning by pole–zero cancellation, `k_i/k_p = R/L` (A. Yazdani, R. Iravani, *Voltage-Sourced
Converters in Power Systems*, Wiley 2010, §8.3.1); the complex Routh–Hurwitz criterion of
H. Bilharz, *Z. Angew. Math. Mech.* 24 (1944) (`theorem/Criteria/Bilharz.lean`). The quartic
determinants were expanded and factored by exact computer algebra (discovery evidence) and are
checked here by the kernel through the reflective polynomial-identity check of
`theorem/Dynamics/PolyIdentity.lean` (`poly_rfl`).

Results.
* `Params.pzCoeff`, **`Params.charDet_fastMatrix_pz`**: with `K_ic L_f = K_pc R_f` the
  characteristic polynomial of the fast matrix factors, `det(s − fastMatrix 0) = (s + R_f/L_f)
  Q(s)`, `Q(s) = s⁴ + b₃ s³ + b₂ s² + b₁ s + b₀ = k_p χ_v(s) + s²((s + jω₀)(s + Z_g/L_g) +
  1/(C_f L_g))`: the current-loop mode `−R_f/L_f` leaves the loop.
* **`Params.spectrallyStable_fastBlock_iff_pz`**: on that sub-family the boundary layer is
  spectrally stable iff `R_f/L_f > 0` and the four Bilharz determinants of `Q` are positive.
* In normalized parameters (`PZLevel.coeffs`, `Params.pzCoeff_eq`) the four determinants are
  `k_p + r`, `PZLevel.delta4` (17 terms), `k_p · PZLevel.delta6F` (302 terms) and
  `k_p² q · PZLevel.delta8F` (2619 terms) (`PZLevel.quarticBilharz2_eq` … `quarticBilharz8_eq`);
  **`Params.spectrallyStable_fastBlock_iff_pz_explicit`**, for every design.
* Ideal design `k_ff = k_dv = 1`, `Z_v = 0` (`e = κ = r_v = x_v = 0`, `PZLevel.ideal_eq`):
  `Δ₄ = (k_p + r) G`, `G = k_p² r + k_p r² + k_p² P + k_p c + r c − k_p q`
  (`PZLevel.idealDelta4F`), `Δ₆ = k_p F₅₂` (`PZLevel.idealDelta6F`, 52 terms), `Δ₈ = k_p² q F₁₄₇`
  (`PZLevel.idealDelta8F`, 147 terms); **`Params.spectrallyStable_fastBlock_iff_pz_ideal`**:
  stable iff `ρ > 0`, `k_p + r > 0`, `G > 0`, `k_p F₅₂ > 0`, `k_p² q F₁₄₇ > 0`. With `k_p + r > 0`
  the second condition is the explicit bound `k_p q < k_p² r + k_p r² + k_p² P + k_p c + r c` on
  the voltage-loop integral gain. (On the same sub-family the quintic determinant
  `Δ₁₀ = k_p² ρ q F₁₁₅ F₂₆₁₉`, computer algebra, not used: the quartic decides.)
-/

noncomputable section
namespace powerlib.GFM.FullModel
open Complex Polynomial

/-! ### The factorization -/

namespace Params

variable (p : Params)

/-- The coefficients `b₀, …, b₃` of the quartic factor `Q(s) = s⁴ + b₃ s³ + b₂ s² + b₁ s + b₀`:
`b₃ = K_pc/L_f + Z_g/L_g + jω₀`, `b₂ = k_p v₂ + jω₀ Z_g/L_g + 1/(C_f L_g)`, `b₁ = k_p v₁`,
`b₀ = k_p v₀` (`v₂, v₁, v₀` the voltage-level coefficients). -/
def pzCoeff : Fin 4 → ℂ :=
  ![((p.Kpc / p.Lf : ℝ) : ℂ) * p.voltageA0,
    ((p.Kpc / p.Lf : ℝ) : ℂ) * p.voltageA1,
    ((p.Kpc / p.Lf : ℝ) : ℂ) * p.voltageA2 + p.ω0 * I * (p.Zg / p.Lg) +
      ((1 / (p.Cf * p.Lg) : ℝ) : ℂ),
    ((p.Kpc / p.Lf : ℝ) : ℂ) + p.Zg / p.Lg + p.ω0 * I]

/-- **The factorization under pole–zero cancellation** (`L_f, C_f, L_g ≠ 0`, `K_ic L_f = K_pc R_f`):
`det(s − fastMatrix 0) = (s + R_f/L_f)(s⁴ + b₃ s³ + b₂ s² + b₁ s + b₀)`. -/
@[tmio M, powerlib_domain] theorem charDet_fastMatrix_pz (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (hpz : p.Kic * p.Lf = p.Kpc * p.Rf) (s : ℂ) :
    (Matrix.scalar (Fin 5) s - p.fastMatrix 0).det =
      (s + ((p.Rf / p.Lf : ℝ) : ℂ)) * (s ^ 4 + p.pzCoeff 3 * s ^ 3 + p.pzCoeff 2 * s ^ 2 +
        p.pzCoeff 1 * s + p.pzCoeff 0) := by
  have hk : ((p.Kic / p.Lf : ℝ) : ℂ) = ((p.Kpc / p.Lf : ℝ) : ℂ) * ((p.Rf / p.Lf : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hLf hLf), div_mul_eq_mul_div,
      div_eq_iff hLf, ← hpz]
    ring
  have hs : (((p.Kpc + p.Rf) / p.Lf : ℝ) : ℂ) = ((p.Kpc / p.Lf : ℝ) : ℂ) +
      ((p.Rf / p.Lf : ℝ) : ℂ) := by
    rw [← Complex.ofReal_add, add_div]
  rw [p.charDet_fastMatrix hLf hCf hLg]
  simp only [fastCoeff, pzCoeff, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, hk,
    hs]
  ring

end Params

@[tmio T, powerlib_foundation] private theorem roots_re_neg_mul_iff (ρ : ℝ) (f : ℂ → ℂ) :
    (∀ s : ℂ, (s + (ρ : ℂ)) * f s = 0 → s.re < 0) ↔ 0 < ρ ∧ ∀ s : ℂ, f s = 0 → s.re < 0 := by
  constructor
  · intro h
    refine ⟨?_, fun s hs => h s (by rw [hs, mul_zero])⟩
    have := h (-(ρ : ℂ)) (by rw [neg_add_cancel, zero_mul])
    simpa using this
  · rintro ⟨hρ, hf⟩ s hs
    rcases mul_eq_zero.mp hs with h0 | h0
    · have : s = -(ρ : ℂ) := eq_neg_of_add_eq_zero_left h0
      rw [this]; simpa using hρ
    · exact hf s h0

namespace Params

variable (p : Params)

/-- **The boundary layer under pole–zero cancellation** (`L_f, C_f, L_g ≠ 0`,
`K_ic L_f = K_pc R_f`, every other parameter value): spectrally stable at the angle `δ` iff
`R_f/L_f > 0` and the four Bilharz determinants of the quartic factor are positive
(`Criteria.complexQuartic_roots_re_neg_iff`). -/
@[tmio M, powerlib_domain] theorem spectrallyStable_fastBlock_iff_pz (hLf : p.Lf ≠ 0)
    (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0) (hpz : p.Kic * p.Lf = p.Kpc * p.Rf) (δ : ℝ) :
    Linear.SpectrallyStable (p.fastBlock δ) ↔
      0 < p.Rf / p.Lf ∧
        0 < Criteria.quarticBilharz2 1 (p.pzCoeff 3) (p.pzCoeff 2) (p.pzCoeff 1) (p.pzCoeff 0) ∧
        0 < Criteria.quarticBilharz4 1 (p.pzCoeff 3) (p.pzCoeff 2) (p.pzCoeff 1) (p.pzCoeff 0) ∧
        0 < Criteria.quarticBilharz6 1 (p.pzCoeff 3) (p.pzCoeff 2) (p.pzCoeff 1) (p.pzCoeff 0) ∧
        0 < Criteria.quarticBilharz8 1 (p.pzCoeff 3) (p.pzCoeff 2) (p.pzCoeff 1)
          (p.pzCoeff 0) := by
  rw [p.spectrallyStable_fastBlock_iff, fastBlock_eq_realify,
    Criteria.spectrallyStable_realify_iff_charpoly]
  simp only [Matrix.eval_charpoly, p.charDet_fastMatrix_pz hLf hCf hLg hpz]
  rw [roots_re_neg_mul_iff (p.Rf / p.Lf)
    (fun s => s ^ 4 + p.pzCoeff 3 * s ^ 3 + p.pzCoeff 2 * s ^ 2 + p.pzCoeff 1 * s + p.pzCoeff 0),
    Criteria.complexQuartic_roots_re_neg_iff]

end Params

/-! ### The quartic in normalized parameters -/

namespace PZLevel

/-- The coefficients `b₀, …, b₃` of the quartic factor in the normalized parameters
`k_p, r, w, c, P, e, q, κ, r_v, x_v` (real and imaginary parts). -/
def coeffs (kp r w c P e q κ rv xv : ℝ) : Fin 4 → ℂ :=
  ![⟨kp * q * (r + rv), kp * q * (w + xv)⟩,
    ⟨kp * (P * (r + rv) + q + κ - e * w ^ 2), kp * (P * (w + xv) + e * w * r)⟩,
    ⟨-w ^ 2 + c + kp * (r + P), w * r + kp * (w + e * w)⟩,
    ⟨kp + r, 2 * w⟩]

/-- `Δ₄` of the pole–zero quartic (17 terms). -/
def delta4 (kp r w c P e q κ rv _xv : ℝ) : ℝ :=
  ((((-kp ^ (2:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) + kp ^ (2:ℕ) * w ^ (2:ℕ) * e) + (kp * r * w ^ (2:ℕ) *
  e + kp ^ (3:ℕ) * r)) + ((2 * kp ^ (2:ℕ) * r ^ (2:ℕ) + kp * r ^ (3:ℕ)) + (kp ^ (3:ℕ) * P + kp
  ^ (2:ℕ) * r * P))) + (((-kp ^ (2:ℕ) * P * rv - kp * r * P * rv) + (kp ^ (2:ℕ) * c + 2 * kp *
  r * c)) + ((r ^ (2:ℕ) * c - kp ^ (2:ℕ) * q) + (-kp * r * q + (-kp ^ (2:ℕ) * κ - kp * r *
  κ)))))

/-- `Δ₆ / k_p` of the pole–zero quartic (302 terms). -/
def delta6F (kp r w c P e q κ rv xv : ℝ) : ℝ :=
  ((((((((-kp ^ (3:ℕ) * r * w ^ (4:ℕ) * e ^ (4:ℕ) + 3 * kp ^ (3:ℕ) * r * w ^ (4:ℕ) * e ^ (3:ℕ))
  + (2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * e ^ (3:ℕ) - kp ^ (3:ℕ) * w ^ (3:ℕ) * P * e ^
  (3:ℕ) * xv)) + ((-kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) - 2 * kp ^ (2:ℕ) * r ^ (4:ℕ)
  * w ^ (2:ℕ) * e ^ (2:ℕ)) + (-kp * r ^ (5:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) + (-3 * kp ^ (3:ℕ) * r *
  w ^ (4:ℕ) * e ^ (2:ℕ) - 4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * e ^ (2:ℕ))))) + (((-kp * r ^
  (3:ℕ) * w ^ (4:ℕ) * e ^ (2:ℕ) + kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P * e ^ (2:ℕ)) + (-2 * kp ^
  (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) - 2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P *
  e ^ (2:ℕ))) + ((-kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) + kp ^ (2:ℕ) * w ^ (4:ℕ)
  * c * e ^ (3:ℕ)) + (-4 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P * e ^ (2:ℕ) * rv + (-3 * kp ^ (2:ℕ) *
  r ^ (2:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) * rv - kp ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) *
  rv))))) + ((((2 * kp ^ (3:ℕ) * w ^ (3:ℕ) * P * e ^ (2:ℕ) * xv + 2 * kp ^ (2:ℕ) * r * w ^
  (3:ℕ) * P * e ^ (2:ℕ) * xv) + (kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * e + 2 * kp ^ (2:ℕ) * r ^
  (4:ℕ) * w ^ (2:ℕ) * e)) + ((kp * r ^ (5:ℕ) * w ^ (2:ℕ) * e + kp ^ (3:ℕ) * r * w ^ (4:ℕ) * e)
  + (2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * e + (kp * r ^ (3:ℕ) * w ^ (4:ℕ) * e - 2 * kp ^
  (4:ℕ) * r * w ^ (2:ℕ) * P * e)))) + (((2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P * e + kp ^
  (3:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * e) + (kp ^ (3:ℕ) * r * w ^ (2:ℕ) * c * e ^ (2:ℕ) + (2 *
  kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * e ^ (2:ℕ) + kp * r ^ (3:ℕ) * w ^ (2:ℕ) * c * e ^
  (2:ℕ)))) + ((-2 * kp ^ (2:ℕ) * w ^ (4:ℕ) * c * e ^ (2:ℕ) - 2 * kp * r * w ^ (4:ℕ) * c * e ^
  (2:ℕ)) + (-kp ^ (2:ℕ) * r * w ^ (2:ℕ) * c * P * e ^ (2:ℕ) + (-3 * kp ^ (3:ℕ) * r * w ^ (2:ℕ)
  * e ^ (2:ℕ) * q - 2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) * q)))))) + (((((-kp ^
  (3:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) * q - 4 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * e ^ (2:ℕ) * κ) + (-3
  * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) * κ - kp ^ (3:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ)
  * κ)) + ((5 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P * e * rv + 6 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^
  (2:ℕ) * P * e * rv) + (kp * r ^ (3:ℕ) * w ^ (2:ℕ) * P * e * rv + (kp ^ (3:ℕ) * w ^ (2:ℕ) * P
  ^ (2:ℕ) * e * rv - kp ^ (2:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * e * rv)))) + (((-kp ^ (2:ℕ) * w ^
  (2:ℕ) * c * P * e ^ (2:ℕ) * rv + kp ^ (3:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) * q * rv) + (kp ^ (2:ℕ) *
  r * w ^ (2:ℕ) * e ^ (2:ℕ) * q * rv + (-kp ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e * rv ^ (2:ℕ) -
  kp ^ (4:ℕ) * r * w * P * e * xv))) + ((-4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w * P * e * xv - 5 * kp
  ^ (2:ℕ) * r ^ (3:ℕ) * w * P * e * xv) + (-2 * kp * r ^ (4:ℕ) * w * P * e * xv + (-kp ^ (3:ℕ)
  * w ^ (3:ℕ) * P * e * xv - 2 * kp ^ (2:ℕ) * r * w ^ (3:ℕ) * P * e * xv))))) + ((((-kp * r ^
  (2:ℕ) * w ^ (3:ℕ) * P * e * xv + kp ^ (4:ℕ) * w * P ^ (2:ℕ) * e * xv) + (-kp ^ (3:ℕ) * r * w
  * P ^ (2:ℕ) * e * xv - 2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * P ^ (2:ℕ) * e * xv)) + ((-3 * kp ^
  (3:ℕ) * w * P ^ (2:ℕ) * e * rv * xv - 3 * kp ^ (2:ℕ) * r * w * P ^ (2:ℕ) * e * rv * xv) + (kp
  ^ (4:ℕ) * r ^ (3:ℕ) * P + (2 * kp ^ (3:ℕ) * r ^ (4:ℕ) * P + kp ^ (2:ℕ) * r ^ (5:ℕ) * P)))) +
  (((kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P + 2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P) + (kp ^ (2:ℕ)
  * r ^ (3:ℕ) * w ^ (2:ℕ) * P + (2 * kp ^ (4:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ) + 2 * kp ^ (3:ℕ) * r ^
  (3:ℕ) * P ^ (2:ℕ)))) + ((kp ^ (4:ℕ) * r * P ^ (3:ℕ) - kp ^ (3:ℕ) * r * w ^ (2:ℕ) * c * e) +
  (-kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * e + (kp * r ^ (3:ℕ) * w ^ (2:ℕ) * c * e + r ^
  (4:ℕ) * w ^ (2:ℕ) * c * e))))))) + ((((((kp ^ (2:ℕ) * w ^ (4:ℕ) * c * e + 2 * kp * r * w ^
  (4:ℕ) * c * e) + (r ^ (2:ℕ) * w ^ (4:ℕ) * c * e - kp ^ (3:ℕ) * w ^ (2:ℕ) * c * P * e)) + ((2
  * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * c * P * e + 3 * kp * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P * e) + (6 *
  kp ^ (3:ℕ) * r * w ^ (2:ℕ) * e * q + (8 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * e * q + 2 * kp
  * r ^ (3:ℕ) * w ^ (2:ℕ) * e * q)))) + (((kp ^ (3:ℕ) * w ^ (2:ℕ) * P * e * q + kp ^ (2:ℕ) * r
  * w ^ (2:ℕ) * P * e * q) + (-kp ^ (2:ℕ) * w ^ (2:ℕ) * c * e ^ (2:ℕ) * q + (5 * kp ^ (3:ℕ) * r
  * w ^ (2:ℕ) * e * κ + 6 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * e * κ))) + ((kp * r ^ (3:ℕ) *
  w ^ (2:ℕ) * e * κ + kp ^ (3:ℕ) * w ^ (2:ℕ) * P * e * κ) + (-kp ^ (2:ℕ) * r * w ^ (2:ℕ) * P *
  e * κ + (-kp ^ (2:ℕ) * w ^ (2:ℕ) * c * e ^ (2:ℕ) * κ + kp ^ (4:ℕ) * r ^ (2:ℕ) * P * rv))))) +
  ((((2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * P * rv + kp ^ (2:ℕ) * r ^ (4:ℕ) * P * rv) + (-kp ^ (3:ℕ) * r
  * w ^ (2:ℕ) * P * rv - 2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * rv)) + ((-kp * r ^ (3:ℕ)
  * w ^ (2:ℕ) * P * rv + 2 * kp ^ (4:ℕ) * r * P ^ (2:ℕ) * rv) + (-2 * kp ^ (2:ℕ) * r ^ (3:ℕ) *
  P ^ (2:ℕ) * rv + (kp ^ (4:ℕ) * P ^ (3:ℕ) * rv - 2 * kp ^ (3:ℕ) * r * P ^ (3:ℕ) * rv)))) +
  (((4 * kp ^ (2:ℕ) * w ^ (2:ℕ) * c * P * e * rv + 4 * kp * r * w ^ (2:ℕ) * c * P * e * rv) +
  (-kp ^ (3:ℕ) * w ^ (2:ℕ) * e * q * rv + (-2 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * e * q * rv - kp *
  r ^ (2:ℕ) * w ^ (2:ℕ) * e * q * rv))) + ((-2 * kp ^ (2:ℕ) * w ^ (2:ℕ) * P * e * κ * rv - 2 *
  kp ^ (3:ℕ) * r * P ^ (2:ℕ) * rv ^ (2:ℕ)) + (-2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ) * rv ^
  (2:ℕ) + (-2 * kp ^ (3:ℕ) * P ^ (3:ℕ) * rv ^ (2:ℕ) + kp ^ (2:ℕ) * r * P ^ (3:ℕ) * rv ^
  (2:ℕ))))))) + (((((kp ^ (2:ℕ) * P ^ (3:ℕ) * rv ^ (3:ℕ) + kp ^ (4:ℕ) * r * w * P * xv) + (3 *
  kp ^ (3:ℕ) * r ^ (2:ℕ) * w * P * xv + 3 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w * P * xv)) + ((kp * r ^
  (4:ℕ) * w * P * xv - kp ^ (4:ℕ) * w * P ^ (2:ℕ) * xv) + (-2 * kp ^ (3:ℕ) * r * w * P ^ (2:ℕ)
  * xv + (-kp ^ (2:ℕ) * r ^ (2:ℕ) * w * P ^ (2:ℕ) * xv + kp ^ (3:ℕ) * w * c * P * e * xv)))) +
  (((2 * kp ^ (2:ℕ) * r * w * c * P * e * xv + kp * r ^ (2:ℕ) * w * c * P * e * xv) + (2 * kp ^
  (3:ℕ) * r * w * e * q * xv + (4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * e * q * xv + 2 * kp * r ^
  (3:ℕ) * w * e * q * xv))) + ((-3 * kp ^ (3:ℕ) * w * P * e * q * xv - kp ^ (2:ℕ) * r * w * P *
  e * q * xv) + (-3 * kp ^ (3:ℕ) * w * P * e * κ * xv + (-3 * kp ^ (2:ℕ) * r * w * P * e * κ *
  xv + kp ^ (3:ℕ) * w * P ^ (2:ℕ) * rv * xv))))) + ((((2 * kp ^ (2:ℕ) * r * w * P ^ (2:ℕ) * rv
  * xv + kp * r ^ (2:ℕ) * w * P ^ (2:ℕ) * rv * xv) + (2 * kp ^ (2:ℕ) * w * P * e * q * rv * xv
  - kp ^ (4:ℕ) * P ^ (2:ℕ) * xv ^ (2:ℕ))) + ((-3 * kp ^ (3:ℕ) * r * P ^ (2:ℕ) * xv ^ (2:ℕ) - 3
  * kp ^ (2:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ) * xv ^ (2:ℕ)) + (-kp * r ^ (3:ℕ) * P ^ (2:ℕ) * xv ^
  (2:ℕ) + (2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * c * P + 4 * kp ^ (2:ℕ) * r ^ (3:ℕ) * c * P)))) + (((2 *
  kp * r ^ (4:ℕ) * c * P + kp ^ (3:ℕ) * w ^ (2:ℕ) * c * P) + (2 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) *
  c * P + (kp * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P + 2 * kp ^ (3:ℕ) * r * c * P ^ (2:ℕ)))) + ((2 *
  kp ^ (2:ℕ) * r ^ (2:ℕ) * c * P ^ (2:ℕ) - kp ^ (2:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * e) + (-2 * kp *
  r * w ^ (2:ℕ) * c ^ (2:ℕ) * e + (-r ^ (2:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * e - kp ^ (3:ℕ) * r ^
  (3:ℕ) * q)))))))) + (((((((-2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * q - kp * r ^ (5:ℕ) * q) + (-3 * kp ^
  (3:ℕ) * r * w ^ (2:ℕ) * q - 6 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * q)) + ((-3 * kp * r ^
  (3:ℕ) * w ^ (2:ℕ) * q + kp ^ (4:ℕ) * r * P * q) + (-2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * P * q + (-3
  * kp ^ (2:ℕ) * r ^ (3:ℕ) * P * q + kp ^ (4:ℕ) * P ^ (2:ℕ) * q)))) + (((-2 * kp ^ (3:ℕ) * r *
  P ^ (2:ℕ) * q + 4 * kp ^ (2:ℕ) * w ^ (2:ℕ) * c * e * q) + (4 * kp * r * w ^ (2:ℕ) * c * e * q
  + kp ^ (2:ℕ) * w ^ (2:ℕ) * e * q ^ (2:ℕ))) + ((kp ^ (4:ℕ) * r ^ (2:ℕ) * κ + 2 * kp ^ (3:ℕ) *
  r ^ (3:ℕ) * κ) + (kp ^ (2:ℕ) * r ^ (4:ℕ) * κ + (-kp ^ (3:ℕ) * r * w ^ (2:ℕ) * κ - 2 * kp ^
  (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * κ))))) + ((((-kp * r ^ (3:ℕ) * w ^ (2:ℕ) * κ + 2 * kp ^ (4:ℕ)
  * r * P * κ) + (-2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * P * κ + kp ^ (4:ℕ) * P ^ (2:ℕ) * κ)) + ((-2 *
  kp ^ (3:ℕ) * r * P ^ (2:ℕ) * κ + 4 * kp ^ (2:ℕ) * w ^ (2:ℕ) * c * e * κ) + (4 * kp * r * w ^
  (2:ℕ) * c * e * κ + (-kp ^ (2:ℕ) * w ^ (2:ℕ) * e * κ ^ (2:ℕ) + 2 * kp ^ (3:ℕ) * r * c * P *
  rv)))) + (((4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c * P * rv + 2 * kp * r ^ (3:ℕ) * c * P * rv) + (-kp
  ^ (2:ℕ) * w ^ (2:ℕ) * c * P * rv + (-2 * kp * r * w ^ (2:ℕ) * c * P * rv - r ^ (2:ℕ) * w ^
  (2:ℕ) * c * P * rv))) + ((2 * kp ^ (3:ℕ) * c * P ^ (2:ℕ) * rv - 2 * kp * r ^ (2:ℕ) * c * P ^
  (2:ℕ) * rv) + (-kp ^ (4:ℕ) * r * q * rv + (-3 * kp ^ (3:ℕ) * r ^ (2:ℕ) * q * rv - 3 * kp ^
  (2:ℕ) * r ^ (3:ℕ) * q * rv)))))) + (((((-kp * r ^ (4:ℕ) * q * rv - kp ^ (4:ℕ) * P * q * rv) +
  (-5 * kp ^ (3:ℕ) * r * P * q * rv - 3 * kp ^ (2:ℕ) * r ^ (2:ℕ) * P * q * rv)) + ((kp * r ^
  (3:ℕ) * P * q * rv - 4 * kp ^ (3:ℕ) * P ^ (2:ℕ) * q * rv) + (2 * kp ^ (2:ℕ) * r * P ^ (2:ℕ) *
  q * rv + (-4 * kp ^ (3:ℕ) * r * P * κ * rv - 4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * P * κ * rv)))) +
  (((-4 * kp ^ (3:ℕ) * P ^ (2:ℕ) * κ * rv + 2 * kp ^ (2:ℕ) * r * P ^ (2:ℕ) * κ * rv) + (-2 * kp
  ^ (2:ℕ) * c * P ^ (2:ℕ) * rv ^ (2:ℕ) + (-2 * kp * r * c * P ^ (2:ℕ) * rv ^ (2:ℕ) + kp ^ (3:ℕ)
  * P * q * rv ^ (2:ℕ)))) + ((2 * kp ^ (2:ℕ) * r * P * q * rv ^ (2:ℕ) + kp * r ^ (2:ℕ) * P * q
  * rv ^ (2:ℕ)) + (3 * kp ^ (2:ℕ) * P ^ (2:ℕ) * q * rv ^ (2:ℕ) + (3 * kp ^ (2:ℕ) * P ^ (2:ℕ) *
  κ * rv ^ (2:ℕ) + kp ^ (3:ℕ) * w * c * P * xv))))) + ((((3 * kp ^ (2:ℕ) * r * w * c * P * xv +
  3 * kp * r ^ (2:ℕ) * w * c * P * xv) + (r ^ (3:ℕ) * w * c * P * xv - 2 * kp ^ (3:ℕ) * r * w *
  q * xv)) + ((-4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * q * xv - 2 * kp * r ^ (3:ℕ) * w * q * xv) + (3
  * kp ^ (3:ℕ) * w * P * q * xv + (6 * kp ^ (2:ℕ) * r * w * P * q * xv + 3 * kp * r ^ (2:ℕ) * w
  * P * q * xv)))) + (((2 * kp ^ (2:ℕ) * w * e * q ^ (2:ℕ) * xv + kp ^ (3:ℕ) * w * P * κ * xv)
  + (2 * kp ^ (2:ℕ) * r * w * P * κ * xv + (kp * r ^ (2:ℕ) * w * P * κ * xv + 2 * kp ^ (2:ℕ) *
  w * e * q * κ * xv))) + ((2 * kp ^ (3:ℕ) * P * q * xv ^ (2:ℕ) + 4 * kp ^ (2:ℕ) * r * P * q *
  xv ^ (2:ℕ)) + (2 * kp * r ^ (2:ℕ) * P * q * xv ^ (2:ℕ) + (kp ^ (2:ℕ) * r * c ^ (2:ℕ) * P + 2
  * kp * r ^ (2:ℕ) * c ^ (2:ℕ) * P))))))) + ((((((r ^ (3:ℕ) * c ^ (2:ℕ) * P + kp ^ (3:ℕ) * r *
  c * q) + (kp ^ (2:ℕ) * r ^ (2:ℕ) * c * q - kp * r ^ (3:ℕ) * c * q)) + ((-r ^ (4:ℕ) * c * q -
  3 * kp ^ (2:ℕ) * w ^ (2:ℕ) * c * q) + (-6 * kp * r * w ^ (2:ℕ) * c * q + (-3 * r ^ (2:ℕ) * w
  ^ (2:ℕ) * c * q + 2 * kp ^ (3:ℕ) * c * P * q)))) + (((-2 * kp * r ^ (2:ℕ) * c * P * q - kp ^
  (3:ℕ) * r * q ^ (2:ℕ)) + (kp * r ^ (3:ℕ) * q ^ (2:ℕ) + (-kp ^ (2:ℕ) * w ^ (2:ℕ) * q ^ (2:ℕ) -
  kp * r * w ^ (2:ℕ) * q ^ (2:ℕ)))) + ((-2 * kp ^ (3:ℕ) * P * q ^ (2:ℕ) + kp ^ (2:ℕ) * r * P *
  q ^ (2:ℕ)) + (2 * kp ^ (3:ℕ) * r * c * κ + (4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c * κ + 2 * kp * r ^
  (3:ℕ) * c * κ))))) + ((((-kp ^ (2:ℕ) * w ^ (2:ℕ) * c * κ - 2 * kp * r * w ^ (2:ℕ) * c * κ) +
  (-r ^ (2:ℕ) * w ^ (2:ℕ) * c * κ + 2 * kp ^ (3:ℕ) * c * P * κ)) + ((-2 * kp * r ^ (2:ℕ) * c *
  P * κ - 3 * kp ^ (3:ℕ) * r * q * κ) + (-2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * q * κ + (kp * r ^ (3:ℕ)
  * q * κ - 4 * kp ^ (3:ℕ) * P * q * κ)))) + (((2 * kp ^ (2:ℕ) * r * P * q * κ - 2 * kp ^ (3:ℕ)
  * r * κ ^ (2:ℕ)) + (-2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * κ ^ (2:ℕ) + (-2 * kp ^ (3:ℕ) * P * κ ^
  (2:ℕ) + kp ^ (2:ℕ) * r * P * κ ^ (2:ℕ)))) + ((kp ^ (2:ℕ) * c ^ (2:ℕ) * P * rv + 2 * kp * r *
  c ^ (2:ℕ) * P * rv) + (r ^ (2:ℕ) * c ^ (2:ℕ) * P * rv + (-kp ^ (3:ℕ) * c * q * rv - 3 * kp ^
  (2:ℕ) * r * c * q * rv)))))) + (((((-3 * kp * r ^ (2:ℕ) * c * q * rv - r ^ (3:ℕ) * c * q *
  rv) + (-4 * kp ^ (2:ℕ) * c * P * q * rv - 4 * kp * r * c * P * q * rv)) + ((kp ^ (3:ℕ) * q ^
  (2:ℕ) * rv + 2 * kp ^ (2:ℕ) * r * q ^ (2:ℕ) * rv) + (kp * r ^ (2:ℕ) * q ^ (2:ℕ) * rv + (3 *
  kp ^ (2:ℕ) * P * q ^ (2:ℕ) * rv - 4 * kp ^ (2:ℕ) * c * P * κ * rv)))) + (((-4 * kp * r * c *
  P * κ * rv + kp ^ (3:ℕ) * q * κ * rv) + (2 * kp ^ (2:ℕ) * r * q * κ * rv + (kp * r ^ (2:ℕ) *
  q * κ * rv + 6 * kp ^ (2:ℕ) * P * q * κ * rv))) + ((3 * kp ^ (2:ℕ) * P * κ ^ (2:ℕ) * rv - 2 *
  kp ^ (2:ℕ) * w * c * q * xv) + (-4 * kp * r * w * c * q * xv + (-2 * r ^ (2:ℕ) * w * c * q *
  xv - 2 * kp ^ (2:ℕ) * w * q ^ (2:ℕ) * xv))))) + ((((-2 * kp * r * w * q ^ (2:ℕ) * xv - kp ^
  (2:ℕ) * q ^ (2:ℕ) * xv ^ (2:ℕ)) + (-kp * r * q ^ (2:ℕ) * xv ^ (2:ℕ) + kp ^ (2:ℕ) * c ^ (2:ℕ)
  * q)) + ((2 * kp * r * c ^ (2:ℕ) * q + r ^ (2:ℕ) * c ^ (2:ℕ) * q) + (-2 * kp ^ (2:ℕ) * c * q
  ^ (2:ℕ) + (-2 * kp * r * c * q ^ (2:ℕ) + kp ^ (2:ℕ) * q ^ (3:ℕ))))) + (((kp ^ (2:ℕ) * c ^
  (2:ℕ) * κ + 2 * kp * r * c ^ (2:ℕ) * κ) + (r ^ (2:ℕ) * c ^ (2:ℕ) * κ + (-4 * kp ^ (2:ℕ) * c *
  q * κ - 4 * kp * r * c * q * κ))) + ((3 * kp ^ (2:ℕ) * q ^ (2:ℕ) * κ - 2 * kp ^ (2:ℕ) * c * κ
  ^ (2:ℕ)) + (-2 * kp * r * c * κ ^ (2:ℕ) + (3 * kp ^ (2:ℕ) * q * κ ^ (2:ℕ) + kp ^ (2:ℕ) * κ ^
  (3:ℕ))))))))))

/-- Terms 1–873 of `delta8F`. -/
def delta8F0 (kp r w c P e q κ rv xv : ℝ) : ℝ :=
  (((((((((kp ^ (4:ℕ) * r * w ^ (6:ℕ) * e ^ (5:ℕ) * rv + (-kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (5:ℕ) *
  e ^ (5:ℕ) * xv - kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * P * e ^ (4:ℕ))) + (-kp ^ (4:ℕ) * r * w
  ^ (6:ℕ) * P * e ^ (4:ℕ) + (-3 * kp ^ (4:ℕ) * r * w ^ (6:ℕ) * e ^ (4:ℕ) * rv - 2 * kp ^ (3:ℕ)
  * r ^ (2:ℕ) * w ^ (6:ℕ) * e ^ (4:ℕ) * rv))) + ((-2 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * P *
  e ^ (4:ℕ) * rv + (-kp ^ (4:ℕ) * r * w ^ (4:ℕ) * P * e ^ (4:ℕ) * rv ^ (2:ℕ) + 3 * kp ^ (4:ℕ) *
  r ^ (2:ℕ) * w ^ (5:ℕ) * e ^ (4:ℕ) * xv)) + ((2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (5:ℕ) * e ^
  (4:ℕ) * xv - 2 * kp ^ (4:ℕ) * r * w ^ (5:ℕ) * P * e ^ (4:ℕ) * xv) + (kp ^ (4:ℕ) * w ^ (5:ℕ) *
  P * e ^ (4:ℕ) * rv * xv - 2 * kp ^ (4:ℕ) * r * w ^ (4:ℕ) * P * e ^ (4:ℕ) * xv ^ (2:ℕ))))) +
  (((3 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * P * e ^ (3:ℕ) + (2 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^
  (4:ℕ) * P * e ^ (3:ℕ) + 3 * kp ^ (4:ℕ) * r * w ^ (6:ℕ) * P * e ^ (3:ℕ))) + ((2 * kp ^ (3:ℕ) *
  r ^ (2:ℕ) * w ^ (6:ℕ) * P * e ^ (3:ℕ) - kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * e ^ (4:ℕ) * κ) +
  (kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * e ^ (3:ℕ) * rv + 2 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^ (4:ℕ)
  * e ^ (3:ℕ) * rv))) + ((kp ^ (2:ℕ) * r ^ (5:ℕ) * w ^ (4:ℕ) * e ^ (3:ℕ) * rv + (3 * kp ^ (4:ℕ)
  * r * w ^ (6:ℕ) * e ^ (3:ℕ) * rv + 4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (6:ℕ) * e ^ (3:ℕ) * rv))
  + ((kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (6:ℕ) * e ^ (3:ℕ) * rv - kp ^ (5:ℕ) * r * w ^ (4:ℕ) * P * e
  ^ (3:ℕ) * rv) + (8 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * P * e ^ (3:ℕ) * rv + 6 * kp ^ (3:ℕ)
  * r ^ (3:ℕ) * w ^ (4:ℕ) * P * e ^ (3:ℕ) * rv))))) + ((((kp ^ (4:ℕ) * r * w ^ (4:ℕ) * P ^
  (2:ℕ) * e ^ (3:ℕ) * rv + (-kp ^ (3:ℕ) * w ^ (6:ℕ) * c * e ^ (4:ℕ) * rv + kp ^ (4:ℕ) * r * w ^
  (4:ℕ) * e ^ (4:ℕ) * q * rv)) + (-kp ^ (4:ℕ) * r * w ^ (4:ℕ) * e ^ (4:ℕ) * κ * rv + (7 * kp ^
  (4:ℕ) * r * w ^ (4:ℕ) * P * e ^ (3:ℕ) * rv ^ (2:ℕ) + 5 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) *
  P * e ^ (3:ℕ) * rv ^ (2:ℕ)))) + ((kp ^ (4:ℕ) * w ^ (4:ℕ) * P ^ (2:ℕ) * e ^ (3:ℕ) * rv ^ (2:ℕ)
  + (kp ^ (4:ℕ) * w ^ (4:ℕ) * e ^ (4:ℕ) * q * rv ^ (2:ℕ) - kp ^ (4:ℕ) * r ^ (4:ℕ) * w ^ (3:ℕ) *
  e ^ (3:ℕ) * xv)) + ((-2 * kp ^ (3:ℕ) * r ^ (5:ℕ) * w ^ (3:ℕ) * e ^ (3:ℕ) * xv - kp ^ (2:ℕ) *
  r ^ (6:ℕ) * w ^ (3:ℕ) * e ^ (3:ℕ) * xv) + (-3 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (5:ℕ) * e ^
  (3:ℕ) * xv - 4 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (5:ℕ) * e ^ (3:ℕ) * xv)))) + (((-kp ^ (2:ℕ) * r
  ^ (4:ℕ) * w ^ (5:ℕ) * e ^ (3:ℕ) * xv + (kp ^ (5:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * P * e ^ (3:ℕ) *
  xv - 2 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^ (3:ℕ) * P * e ^ (3:ℕ) * xv)) + ((-2 * kp ^ (3:ℕ) * r ^
  (4:ℕ) * w ^ (3:ℕ) * P * e ^ (3:ℕ) * xv + 6 * kp ^ (4:ℕ) * r * w ^ (5:ℕ) * P * e ^ (3:ℕ) * xv)
  + (4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (5:ℕ) * P * e ^ (3:ℕ) * xv - 2 * kp ^ (4:ℕ) * r ^ (2:ℕ) *
  w ^ (3:ℕ) * P ^ (2:ℕ) * e ^ (3:ℕ) * xv))) + ((-kp ^ (4:ℕ) * w ^ (5:ℕ) * P ^ (2:ℕ) * e ^ (3:ℕ)
  * xv + (kp ^ (3:ℕ) * r * w ^ (5:ℕ) * c * e ^ (4:ℕ) * xv - 4 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^
  (3:ℕ) * P * e ^ (3:ℕ) * rv * xv)) + ((-3 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (3:ℕ) * P * e ^ (3:ℕ)
  * rv * xv - 2 * kp ^ (4:ℕ) * w ^ (5:ℕ) * P * e ^ (3:ℕ) * rv * xv) + (-2 * kp ^ (3:ℕ) * r * w
  ^ (5:ℕ) * P * e ^ (3:ℕ) * rv * xv - 3 * kp ^ (4:ℕ) * r * w ^ (3:ℕ) * P ^ (2:ℕ) * e ^ (3:ℕ) *
  rv * xv)))))) + (((((-kp ^ (4:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * e ^ (3:ℕ) * rv ^ (2:ℕ) * xv + (5 *
  kp ^ (4:ℕ) * r * w ^ (4:ℕ) * P * e ^ (3:ℕ) * xv ^ (2:ℕ) + 4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^
  (4:ℕ) * P * e ^ (3:ℕ) * xv ^ (2:ℕ))) + (-2 * kp ^ (4:ℕ) * w ^ (4:ℕ) * P ^ (2:ℕ) * e ^ (3:ℕ) *
  xv ^ (2:ℕ) + (-kp ^ (4:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * e ^ (3:ℕ) * xv ^ (3:ℕ) - kp ^ (4:ℕ) * r ^
  (5:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ)))) + ((-2 * kp ^ (3:ℕ) * r ^ (6:ℕ) * w ^ (2:ℕ) * P * e ^
  (2:ℕ) + (-kp ^ (2:ℕ) * r ^ (7:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) - 4 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w
  ^ (4:ℕ) * P * e ^ (2:ℕ))) + ((-6 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^ (4:ℕ) * P * e ^ (2:ℕ) - 2 *
  kp ^ (2:ℕ) * r ^ (5:ℕ) * w ^ (4:ℕ) * P * e ^ (2:ℕ)) + (-3 * kp ^ (4:ℕ) * r * w ^ (6:ℕ) * P *
  e ^ (2:ℕ) - 4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (6:ℕ) * P * e ^ (2:ℕ))))) + (((-kp ^ (2:ℕ) * r ^
  (3:ℕ) * w ^ (6:ℕ) * P * e ^ (2:ℕ) + (kp ^ (5:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e ^
  (2:ℕ) - 2 * kp ^ (4:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ))) + ((-2 * kp ^ (3:ℕ)
  * r ^ (5:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) + kp ^ (5:ℕ) * r * w ^ (4:ℕ) * P ^ (2:ℕ) * e
  ^ (2:ℕ)) + (-2 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) - 2 * kp ^ (3:ℕ)
  * r ^ (3:ℕ) * w ^ (4:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ)))) + ((-kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) *
  P ^ (3:ℕ) * e ^ (2:ℕ) + (-kp ^ (4:ℕ) * r * w ^ (4:ℕ) * P ^ (3:ℕ) * e ^ (2:ℕ) + kp ^ (3:ℕ) * r
  ^ (2:ℕ) * w ^ (4:ℕ) * c * P * e ^ (3:ℕ))) + ((kp ^ (3:ℕ) * w ^ (6:ℕ) * c * P * e ^ (3:ℕ) + kp
  ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * e ^ (3:ℕ) * q) + (kp ^ (3:ℕ) * r * w ^ (6:ℕ) * e ^ (3:ℕ) *
  q - 2 * kp ^ (4:ℕ) * r * w ^ (4:ℕ) * P * e ^ (3:ℕ) * q))))) + ((((3 * kp ^ (4:ℕ) * r ^ (2:ℕ)
  * w ^ (4:ℕ) * e ^ (3:ℕ) * κ + (2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * e ^ (3:ℕ) * κ - kp ^
  (4:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * e ^ (2:ℕ) * rv)) + ((-2 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^ (4:ℕ)
  * e ^ (2:ℕ) * rv - kp ^ (2:ℕ) * r ^ (5:ℕ) * w ^ (4:ℕ) * e ^ (2:ℕ) * rv) + (-kp ^ (4:ℕ) * r *
  w ^ (6:ℕ) * e ^ (2:ℕ) * rv - 2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (6:ℕ) * e ^ (2:ℕ) * rv))) +
  ((-kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (6:ℕ) * e ^ (2:ℕ) * rv + (-2 * kp ^ (4:ℕ) * r ^ (4:ℕ) * w ^
  (2:ℕ) * P * e ^ (2:ℕ) * rv - 4 * kp ^ (3:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) * rv)) +
  ((-2 * kp ^ (2:ℕ) * r ^ (6:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) * rv + 2 * kp ^ (5:ℕ) * r * w ^
  (4:ℕ) * P * e ^ (2:ℕ) * rv) + (-6 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * P * e ^ (2:ℕ) * rv -
  10 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * P * e ^ (2:ℕ) * rv)))) + (((-2 * kp ^ (2:ℕ) * r ^
  (4:ℕ) * w ^ (4:ℕ) * P * e ^ (2:ℕ) * rv + (2 * kp ^ (5:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ)
  * e ^ (2:ℕ) * rv - 8 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * rv)) +
  ((-7 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * rv - 5 * kp ^ (4:ℕ) * r *
  w ^ (4:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * rv) + (-3 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * P ^
  (2:ℕ) * e ^ (2:ℕ) * rv - 3 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (3:ℕ) * e ^ (2:ℕ) *
  rv))) + ((-kp ^ (4:ℕ) * w ^ (4:ℕ) * P ^ (3:ℕ) * e ^ (2:ℕ) * rv + (-kp ^ (4:ℕ) * r * w ^ (4:ℕ)
  * c * e ^ (3:ℕ) * rv - 2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * c * e ^ (3:ℕ) * rv)) + ((-kp
  ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * c * e ^ (3:ℕ) * rv + 2 * kp ^ (3:ℕ) * w ^ (6:ℕ) * c * e ^
  (3:ℕ) * rv) + (2 * kp ^ (2:ℕ) * r * w ^ (6:ℕ) * c * e ^ (3:ℕ) * rv + 3 * kp ^ (3:ℕ) * r * w ^
  (4:ℕ) * c * P * e ^ (3:ℕ) * rv))))))) + ((((((2 * kp ^ (4:ℕ) * r * w ^ (4:ℕ) * e ^ (3:ℕ) * q
  * rv + (2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * e ^ (3:ℕ) * q * rv - kp ^ (4:ℕ) * w ^ (4:ℕ)
  * P * e ^ (3:ℕ) * q * rv)) + (7 * kp ^ (4:ℕ) * r * w ^ (4:ℕ) * e ^ (3:ℕ) * κ * rv + (5 * kp ^
  (3:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * e ^ (3:ℕ) * κ * rv + kp ^ (4:ℕ) * w ^ (4:ℕ) * P * e ^ (3:ℕ) *
  κ * rv))) + ((-kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) * rv ^ (2:ℕ) + (-2 * kp ^
  (3:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) * rv ^ (2:ℕ) - kp ^ (2:ℕ) * r ^ (5:ℕ) * w ^
  (2:ℕ) * P * e ^ (2:ℕ) * rv ^ (2:ℕ))) + ((-8 * kp ^ (4:ℕ) * r * w ^ (4:ℕ) * P * e ^ (2:ℕ) * rv
  ^ (2:ℕ) - 10 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * P * e ^ (2:ℕ) * rv ^ (2:ℕ)) + (-2 * kp ^
  (2:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * P * e ^ (2:ℕ) * rv ^ (2:ℕ) + kp ^ (5:ℕ) * r * w ^ (2:ℕ) * P ^
  (2:ℕ) * e ^ (2:ℕ) * rv ^ (2:ℕ))))) + (((-10 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ)
  * e ^ (2:ℕ) * rv ^ (2:ℕ) + (-8 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) *
  rv ^ (2:ℕ) - kp ^ (4:ℕ) * w ^ (4:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * rv ^ (2:ℕ))) + ((kp ^ (3:ℕ) * r
  * w ^ (4:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * rv ^ (2:ℕ) - 3 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P ^ (3:ℕ)
  * e ^ (2:ℕ) * rv ^ (2:ℕ)) + (2 * kp ^ (3:ℕ) * w ^ (4:ℕ) * c * P * e ^ (3:ℕ) * rv ^ (2:ℕ) - 2
  * kp ^ (4:ℕ) * w ^ (4:ℕ) * e ^ (3:ℕ) * q * rv ^ (2:ℕ)))) + ((-2 * kp ^ (3:ℕ) * r * w ^ (4:ℕ)
  * e ^ (3:ℕ) * q * rv ^ (2:ℕ) + (-4 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * rv
  ^ (3:ℕ) - 3 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * rv ^ (3:ℕ))) +
  ((kp ^ (3:ℕ) * w ^ (4:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * rv ^ (3:ℕ) - kp ^ (4:ℕ) * w ^ (2:ℕ) * P ^
  (3:ℕ) * e ^ (2:ℕ) * rv ^ (3:ℕ)) + (kp ^ (4:ℕ) * r ^ (4:ℕ) * w ^ (3:ℕ) * e ^ (2:ℕ) * xv + 2 *
  kp ^ (3:ℕ) * r ^ (5:ℕ) * w ^ (3:ℕ) * e ^ (2:ℕ) * xv))))) + ((((kp ^ (2:ℕ) * r ^ (6:ℕ) * w ^
  (3:ℕ) * e ^ (2:ℕ) * xv + (kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (5:ℕ) * e ^ (2:ℕ) * xv + 2 * kp ^
  (3:ℕ) * r ^ (3:ℕ) * w ^ (5:ℕ) * e ^ (2:ℕ) * xv)) + (kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (5:ℕ) * e ^
  (2:ℕ) * xv + (-2 * kp ^ (5:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * P * e ^ (2:ℕ) * xv - 2 * kp ^ (4:ℕ) *
  r ^ (3:ℕ) * w ^ (3:ℕ) * P * e ^ (2:ℕ) * xv))) + ((-2 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^ (3:ℕ) * P
  * e ^ (2:ℕ) * xv + (-2 * kp ^ (2:ℕ) * r ^ (5:ℕ) * w ^ (3:ℕ) * P * e ^ (2:ℕ) * xv - 6 * kp ^
  (4:ℕ) * r * w ^ (5:ℕ) * P * e ^ (2:ℕ) * xv)) + ((-8 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (5:ℕ) * P
  * e ^ (2:ℕ) * xv - 2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (5:ℕ) * P * e ^ (2:ℕ) * xv) + (2 * kp ^
  (5:ℕ) * r * w ^ (3:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * xv - kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * P ^
  (2:ℕ) * e ^ (2:ℕ) * xv)))) + (((-2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * e ^
  (2:ℕ) * xv + (2 * kp ^ (4:ℕ) * w ^ (5:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * xv + 2 * kp ^ (3:ℕ) * r *
  w ^ (5:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * xv)) + ((-2 * kp ^ (4:ℕ) * r * w ^ (3:ℕ) * P ^ (3:ℕ) * e
  ^ (2:ℕ) * xv + kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * c * e ^ (3:ℕ) * xv) + (2 * kp ^ (3:ℕ) * r
  ^ (3:ℕ) * w ^ (3:ℕ) * c * e ^ (3:ℕ) * xv + kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (3:ℕ) * c * e ^ (3:ℕ)
  * xv))) + ((-2 * kp ^ (3:ℕ) * r * w ^ (5:ℕ) * c * e ^ (3:ℕ) * xv + (-2 * kp ^ (2:ℕ) * r ^
  (2:ℕ) * w ^ (5:ℕ) * c * e ^ (3:ℕ) * xv - kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * c * P * e ^
  (3:ℕ) * xv)) + ((2 * kp ^ (3:ℕ) * w ^ (5:ℕ) * c * P * e ^ (3:ℕ) * xv - 5 * kp ^ (4:ℕ) * r ^
  (2:ℕ) * w ^ (3:ℕ) * e ^ (3:ℕ) * q * xv) + (-2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (3:ℕ) * e ^
  (3:ℕ) * q * xv + 2 * kp ^ (3:ℕ) * r * w ^ (5:ℕ) * e ^ (3:ℕ) * q * xv)))))) + (((((-4 * kp ^
  (4:ℕ) * r * w ^ (3:ℕ) * P * e ^ (3:ℕ) * q * xv + (-4 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * e
  ^ (3:ℕ) * κ * xv - 3 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (3:ℕ) * e ^ (3:ℕ) * κ * xv)) + (-2 * kp ^
  (4:ℕ) * r * w ^ (3:ℕ) * P * e ^ (3:ℕ) * κ * xv + (kp ^ (5:ℕ) * r * w ^ (3:ℕ) * P * e ^ (2:ℕ)
  * rv * xv + 9 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * P * e ^ (2:ℕ) * rv * xv))) + ((11 * kp ^
  (3:ℕ) * r ^ (3:ℕ) * w ^ (3:ℕ) * P * e ^ (2:ℕ) * rv * xv + (3 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^
  (3:ℕ) * P * e ^ (2:ℕ) * rv * xv + kp ^ (4:ℕ) * w ^ (5:ℕ) * P * e ^ (2:ℕ) * rv * xv)) + ((2 *
  kp ^ (3:ℕ) * r * w ^ (5:ℕ) * P * e ^ (2:ℕ) * rv * xv + kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (5:ℕ) * P
  * e ^ (2:ℕ) * rv * xv) + (-kp ^ (5:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * rv * xv - 2 * kp
  ^ (4:ℕ) * r * w ^ (3:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * rv * xv)))) + (((-kp ^ (3:ℕ) * r ^ (2:ℕ) *
  w ^ (3:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * rv * xv + (-2 * kp ^ (4:ℕ) * w ^ (3:ℕ) * P ^ (3:ℕ) * e ^
  (2:ℕ) * rv * xv - kp ^ (3:ℕ) * r * w ^ (3:ℕ) * c * P * e ^ (3:ℕ) * rv * xv)) + ((-kp ^ (4:ℕ)
  * r * w ^ (3:ℕ) * e ^ (3:ℕ) * q * rv * xv + kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * e ^ (3:ℕ) *
  q * rv * xv) + (-3 * kp ^ (4:ℕ) * w ^ (3:ℕ) * P * e ^ (3:ℕ) * q * rv * xv - kp ^ (4:ℕ) * w ^
  (3:ℕ) * P * e ^ (3:ℕ) * κ * rv * xv))) + ((5 * kp ^ (4:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ)
  * rv ^ (2:ℕ) * xv + (4 * kp ^ (3:ℕ) * r * w ^ (3:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * rv ^ (2:ℕ) * xv
  - kp ^ (5:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) * xv ^ (2:ℕ))) + ((-5 * kp ^ (4:ℕ) * r ^
  (3:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) * xv ^ (2:ℕ) - 7 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * P *
  e ^ (2:ℕ) * xv ^ (2:ℕ)) + (-3 * kp ^ (2:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) * xv ^
  (2:ℕ) - 4 * kp ^ (4:ℕ) * r * w ^ (4:ℕ) * P * e ^ (2:ℕ) * xv ^ (2:ℕ)))))) + ((((-6 * kp ^
  (3:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * P * e ^ (2:ℕ) * xv ^ (2:ℕ) + (-2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w
  ^ (4:ℕ) * P * e ^ (2:ℕ) * xv ^ (2:ℕ) + 2 * kp ^ (5:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ)
  * xv ^ (2:ℕ))) + ((-3 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * xv ^
  (2:ℕ) - 4 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * xv ^ (2:ℕ)) + (4 *
  kp ^ (4:ℕ) * w ^ (4:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * xv ^ (2:ℕ) + 4 * kp ^ (3:ℕ) * r * w ^ (4:ℕ)
  * P ^ (2:ℕ) * e ^ (2:ℕ) * xv ^ (2:ℕ)))) + ((-kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P ^ (3:ℕ) * e ^
  (2:ℕ) * xv ^ (2:ℕ) + (kp ^ (3:ℕ) * w ^ (4:ℕ) * c * P * e ^ (3:ℕ) * xv ^ (2:ℕ) + kp ^ (3:ℕ) *
  r * w ^ (4:ℕ) * e ^ (3:ℕ) * q * xv ^ (2:ℕ))) + ((-7 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ)
  * e ^ (2:ℕ) * rv * xv ^ (2:ℕ) - 6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e ^
  (2:ℕ) * rv * xv ^ (2:ℕ)) + (-kp ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (3:ℕ) * e ^ (2:ℕ) * rv * xv ^ (2:ℕ)
  + 2 * kp ^ (4:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * xv ^ (3:ℕ))))) + (((2 * kp ^ (3:ℕ) * r
  * w ^ (3:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * xv ^ (3:ℕ) + (kp ^ (4:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * P *
  e + 2 * kp ^ (3:ℕ) * r ^ (6:ℕ) * w ^ (2:ℕ) * P * e)) + ((kp ^ (2:ℕ) * r ^ (7:ℕ) * w ^ (2:ℕ) *
  P * e + 2 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * P * e) + (4 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^
  (4:ℕ) * P * e + 2 * kp ^ (2:ℕ) * r ^ (5:ℕ) * w ^ (4:ℕ) * P * e))) + ((kp ^ (4:ℕ) * r * w ^
  (6:ℕ) * P * e + (2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (6:ℕ) * P * e + kp ^ (2:ℕ) * r ^ (3:ℕ) * w
  ^ (6:ℕ) * P * e)) + ((-2 * kp ^ (5:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e + 2 * kp ^
  (3:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e) + (-2 * kp ^ (5:ℕ) * r * w ^ (4:ℕ) * P ^ (2:ℕ)
  * e + 2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * P ^ (2:ℕ) * e)))))))) + (((((((kp ^ (4:ℕ) * r
  ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (3:ℕ) * e + (kp ^ (4:ℕ) * r * w ^ (4:ℕ) * P ^ (3:ℕ) * e + kp ^
  (4:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * c * P * e ^ (2:ℕ))) + (2 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ)
  * c * P * e ^ (2:ℕ) + (kp ^ (2:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * c * P * e ^ (2:ℕ) + kp ^ (4:ℕ) *
  r * w ^ (4:ℕ) * c * P * e ^ (2:ℕ)))) + ((-kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * c * P * e ^
  (2:ℕ) + (-2 * kp ^ (3:ℕ) * w ^ (6:ℕ) * c * P * e ^ (2:ℕ) - 2 * kp ^ (2:ℕ) * r * w ^ (6:ℕ) * c
  * P * e ^ (2:ℕ))) + ((-kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * e ^ (2:ℕ) - kp ^
  (3:ℕ) * r * w ^ (4:ℕ) * c * P ^ (2:ℕ) * e ^ (2:ℕ)) + (-3 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ)
  * e ^ (2:ℕ) * q - 2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (4:ℕ) * e ^ (2:ℕ) * q)))) + (((-3 * kp ^
  (3:ℕ) * r * w ^ (6:ℕ) * e ^ (2:ℕ) * q + (-2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (6:ℕ) * e ^ (2:ℕ)
  * q - 4 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) * q)) + ((-2 * kp ^ (3:ℕ) * r ^
  (4:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) * q + 2 * kp ^ (4:ℕ) * r * w ^ (4:ℕ) * P * e ^ (2:ℕ) * q) +
  (2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * P * e ^ (2:ℕ) * q - 2 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w
  ^ (2:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * q))) + ((-kp ^ (3:ℕ) * r * w ^ (4:ℕ) * c * e ^ (3:ℕ) * q +
  (-kp ^ (4:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) * κ - 2 * kp ^ (3:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ)
  * e ^ (2:ℕ) * κ)) + ((-kp ^ (2:ℕ) * r ^ (6:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) * κ - 3 * kp ^ (4:ℕ) *
  r ^ (2:ℕ) * w ^ (4:ℕ) * e ^ (2:ℕ) * κ) + (-4 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * e ^ (2:ℕ)
  * κ - kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (4:ℕ) * e ^ (2:ℕ) * κ))))) + ((((kp ^ (5:ℕ) * r ^ (2:ℕ) *
  w ^ (2:ℕ) * P * e ^ (2:ℕ) * κ + (-6 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) * κ
  - 5 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) * κ)) + (-4 * kp ^ (4:ℕ) * r * w ^
  (4:ℕ) * P * e ^ (2:ℕ) * κ + (-3 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * P * e ^ (2:ℕ) * κ - 2
  * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * κ))) + ((-kp ^ (4:ℕ) * w ^
  (4:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * κ + (kp ^ (3:ℕ) * r * w ^ (4:ℕ) * c * e ^ (3:ℕ) * κ - kp ^
  (5:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P * e * rv)) + ((3 * kp ^ (3:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * P *
  e * rv + 2 * kp ^ (2:ℕ) * r ^ (6:ℕ) * w ^ (2:ℕ) * P * e * rv) + (-kp ^ (5:ℕ) * r * w ^ (4:ℕ)
  * P * e * rv + 3 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * P * e * rv)))) + (((2 * kp ^ (2:ℕ) *
  r ^ (4:ℕ) * w ^ (4:ℕ) * P * e * rv + (-6 * kp ^ (5:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e
  * rv + 3 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e * rv)) + ((10 * kp ^ (3:ℕ) * r
  ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e * rv + kp ^ (2:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e
  * rv) + (5 * kp ^ (4:ℕ) * r * w ^ (4:ℕ) * P ^ (2:ℕ) * e * rv + 6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w
  ^ (4:ℕ) * P ^ (2:ℕ) * e * rv))) + ((kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * P ^ (2:ℕ) * e * rv +
  (-kp ^ (5:ℕ) * r * w ^ (2:ℕ) * P ^ (3:ℕ) * e * rv + 3 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) *
  P ^ (3:ℕ) * e * rv)) + ((-kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (3:ℕ) * e * rv + kp ^
  (4:ℕ) * w ^ (4:ℕ) * P ^ (3:ℕ) * e * rv) + (-kp ^ (3:ℕ) * r * w ^ (4:ℕ) * P ^ (3:ℕ) * e * rv +
  kp ^ (4:ℕ) * r * w ^ (4:ℕ) * c * e ^ (2:ℕ) * rv)))))) + (((((kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^
  (4:ℕ) * c * e ^ (2:ℕ) * rv + (-kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * c * e ^ (2:ℕ) * rv - kp *
  r ^ (4:ℕ) * w ^ (4:ℕ) * c * e ^ (2:ℕ) * rv)) + (-kp ^ (3:ℕ) * w ^ (6:ℕ) * c * e ^ (2:ℕ) * rv
  + (-2 * kp ^ (2:ℕ) * r * w ^ (6:ℕ) * c * e ^ (2:ℕ) * rv - kp * r ^ (2:ℕ) * w ^ (6:ℕ) * c * e
  ^ (2:ℕ) * rv))) + ((2 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P * e ^ (2:ℕ) * rv + (4 * kp
  ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * c * P * e ^ (2:ℕ) * rv + 2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^
  (2:ℕ) * c * P * e ^ (2:ℕ) * rv)) + ((kp ^ (4:ℕ) * w ^ (4:ℕ) * c * P * e ^ (2:ℕ) * rv - 6 * kp
  ^ (3:ℕ) * r * w ^ (4:ℕ) * c * P * e ^ (2:ℕ) * rv) + (-7 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ)
  * c * P * e ^ (2:ℕ) * rv - 3 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * e ^ (2:ℕ)
  * rv)))) + (((-kp ^ (3:ℕ) * w ^ (4:ℕ) * c * P ^ (2:ℕ) * e ^ (2:ℕ) * rv + (kp ^ (4:ℕ) * r ^
  (3:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) * q * rv + 2 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) *
  q * rv)) + ((kp ^ (2:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) * q * rv - 9 * kp ^ (4:ℕ) * r * w
  ^ (4:ℕ) * e ^ (2:ℕ) * q * rv) + (-14 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * e ^ (2:ℕ) * q *
  rv - 5 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * e ^ (2:ℕ) * q * rv))) + ((-kp ^ (5:ℕ) * r * w ^
  (2:ℕ) * P * e ^ (2:ℕ) * q * rv + (-6 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) * q
  * rv - kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) * q * rv)) + ((2 * kp ^ (4:ℕ) * w ^
  (4:ℕ) * P * e ^ (2:ℕ) * q * rv + 3 * kp ^ (3:ℕ) * r * w ^ (4:ℕ) * P * e ^ (2:ℕ) * q * rv) +
  (-4 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * q * rv - kp ^ (4:ℕ) * r ^ (3:ℕ) *
  w ^ (2:ℕ) * e ^ (2:ℕ) * κ * rv))))) + ((((-2 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ)
  * κ * rv + (-kp ^ (2:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) * κ * rv - 8 * kp ^ (4:ℕ) * r * w
  ^ (4:ℕ) * e ^ (2:ℕ) * κ * rv)) + ((-10 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * e ^ (2:ℕ) * κ *
  rv - 2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * e ^ (2:ℕ) * κ * rv) + (kp ^ (5:ℕ) * r * w ^
  (2:ℕ) * P * e ^ (2:ℕ) * κ * rv - 14 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) * κ
  * rv))) + ((-11 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) * κ * rv + (-kp ^ (4:ℕ)
  * w ^ (4:ℕ) * P * e ^ (2:ℕ) * κ * rv + kp ^ (3:ℕ) * r * w ^ (4:ℕ) * P * e ^ (2:ℕ) * κ * rv))
  + ((-4 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * κ * rv + 2 * kp ^ (3:ℕ) * w ^
  (4:ℕ) * c * e ^ (3:ℕ) * κ * rv) + (-kp ^ (5:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * e * rv ^ (2:ℕ) -
  kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P * e * rv ^ (2:ℕ))))) + (((kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^
  (2:ℕ) * P * e * rv ^ (2:ℕ) + (kp ^ (2:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * P * e * rv ^ (2:ℕ) + 2 *
  kp ^ (4:ℕ) * r * w ^ (4:ℕ) * P * e * rv ^ (2:ℕ))) + ((4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ)
  * P * e * rv ^ (2:ℕ) + 2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * P * e * rv ^ (2:ℕ)) + (-4 *
  kp ^ (5:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * e * rv ^ (2:ℕ) + 10 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^
  (2:ℕ) * P ^ (2:ℕ) * e * rv ^ (2:ℕ)))) + ((16 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ)
  * e * rv ^ (2:ℕ) + (2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e * rv ^ (2:ℕ) - kp
  ^ (5:ℕ) * w ^ (2:ℕ) * P ^ (3:ℕ) * e * rv ^ (2:ℕ))) + ((5 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P ^
  (3:ℕ) * e * rv ^ (2:ℕ) - 3 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (3:ℕ) * e * rv ^ (2:ℕ))
  + (-kp ^ (3:ℕ) * w ^ (4:ℕ) * P ^ (3:ℕ) * e * rv ^ (2:ℕ) + kp ^ (4:ℕ) * r * w ^ (2:ℕ) * c * P
  * e ^ (2:ℕ) * rv ^ (2:ℕ)))))))) + ((((((2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P * e ^
  (2:ℕ) * rv ^ (2:ℕ) + (kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * c * P * e ^ (2:ℕ) * rv ^ (2:ℕ) - 6
  * kp ^ (3:ℕ) * w ^ (4:ℕ) * c * P * e ^ (2:ℕ) * rv ^ (2:ℕ))) + (-6 * kp ^ (2:ℕ) * r * w ^
  (4:ℕ) * c * P * e ^ (2:ℕ) * rv ^ (2:ℕ) + (-3 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * c * P ^ (2:ℕ) * e
  ^ (2:ℕ) * rv ^ (2:ℕ) + kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) * q * rv ^ (2:ℕ)))) +
  ((2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) * q * rv ^ (2:ℕ) + (kp ^ (2:ℕ) * r ^
  (4:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) * q * rv ^ (2:ℕ) + kp ^ (4:ℕ) * w ^ (4:ℕ) * e ^ (2:ℕ) * q * rv
  ^ (2:ℕ))) + ((2 * kp ^ (3:ℕ) * r * w ^ (4:ℕ) * e ^ (2:ℕ) * q * rv ^ (2:ℕ) + kp ^ (2:ℕ) * r ^
  (2:ℕ) * w ^ (4:ℕ) * e ^ (2:ℕ) * q * rv ^ (2:ℕ)) + (-kp ^ (5:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) *
  q * rv ^ (2:ℕ) + 2 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P * e ^ (2:ℕ) * q * rv ^ (2:ℕ))))) + (((5 *
  kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) * q * rv ^ (2:ℕ) + (-2 * kp ^ (4:ℕ) * w ^
  (2:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * q * rv ^ (2:ℕ) - 8 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P * e ^
  (2:ℕ) * κ * rv ^ (2:ℕ))) + ((-6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) * κ * rv
  ^ (2:ℕ) + 2 * kp ^ (3:ℕ) * w ^ (4:ℕ) * P * e ^ (2:ℕ) * κ * rv ^ (2:ℕ)) + (-2 * kp ^ (4:ℕ) * w
  ^ (2:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) * κ * rv ^ (2:ℕ) + 7 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ)
  * e * rv ^ (3:ℕ)))) + ((8 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e * rv ^ (3:ℕ) +
  (kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e * rv ^ (3:ℕ) + 3 * kp ^ (4:ℕ) * w ^ (2:ℕ)
  * P ^ (3:ℕ) * e * rv ^ (3:ℕ))) + ((-4 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P ^ (3:ℕ) * e * rv ^
  (3:ℕ) - kp ^ (3:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * e ^ (2:ℕ) * rv ^ (3:ℕ)) + (4 * kp ^ (4:ℕ) *
  w ^ (2:ℕ) * P * e ^ (2:ℕ) * q * rv ^ (3:ℕ) + 4 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P * e ^ (2:ℕ) *
  q * rv ^ (3:ℕ)))))) + ((((-2 * kp ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (3:ℕ) * e * rv ^ (4:ℕ) + (kp ^
  (5:ℕ) * r ^ (4:ℕ) * w * P * e * xv + 2 * kp ^ (4:ℕ) * r ^ (5:ℕ) * w * P * e * xv)) + (kp ^
  (3:ℕ) * r ^ (6:ℕ) * w * P * e * xv + (kp ^ (5:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * P * e * xv + 4 *
  kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^ (3:ℕ) * P * e * xv))) + ((5 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^ (3:ℕ)
  * P * e * xv + (2 * kp ^ (2:ℕ) * r ^ (5:ℕ) * w ^ (3:ℕ) * P * e * xv + 2 * kp ^ (4:ℕ) * r * w
  ^ (5:ℕ) * P * e * xv)) + ((4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (5:ℕ) * P * e * xv + 2 * kp ^
  (2:ℕ) * r ^ (3:ℕ) * w ^ (5:ℕ) * P * e * xv) + (kp ^ (5:ℕ) * r ^ (3:ℕ) * w * P ^ (2:ℕ) * e *
  xv - 2 * kp ^ (4:ℕ) * r ^ (4:ℕ) * w * P ^ (2:ℕ) * e * xv)))) + (((-5 * kp ^ (3:ℕ) * r ^ (5:ℕ)
  * w * P ^ (2:ℕ) * e * xv + (-2 * kp ^ (2:ℕ) * r ^ (6:ℕ) * w * P ^ (2:ℕ) * e * xv - 5 * kp ^
  (5:ℕ) * r * w ^ (3:ℕ) * P ^ (2:ℕ) * e * xv)) + ((-5 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * P
  ^ (2:ℕ) * e * xv - 3 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * e * xv) + (-3 * kp ^
  (2:ℕ) * r ^ (4:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * e * xv - kp ^ (4:ℕ) * w ^ (5:ℕ) * P ^ (2:ℕ) * e *
  xv))) + ((-2 * kp ^ (3:ℕ) * r * w ^ (5:ℕ) * P ^ (2:ℕ) * e * xv + (-kp ^ (2:ℕ) * r ^ (2:ℕ) * w
  ^ (5:ℕ) * P ^ (2:ℕ) * e * xv + 2 * kp ^ (5:ℕ) * r ^ (2:ℕ) * w * P ^ (3:ℕ) * e * xv)) + ((-kp
  ^ (4:ℕ) * r ^ (3:ℕ) * w * P ^ (3:ℕ) * e * xv - 2 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w * P ^ (3:ℕ) * e
  * xv) + (kp ^ (5:ℕ) * w ^ (3:ℕ) * P ^ (3:ℕ) * e * xv + kp ^ (4:ℕ) * r * w ^ (3:ℕ) * P ^ (3:ℕ)
  * e * xv)))))) + (((((-2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * P ^ (3:ℕ) * e * xv + (-kp ^
  (4:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * c * e ^ (2:ℕ) * xv - kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (3:ℕ) * c *
  e ^ (2:ℕ) * xv)) + (kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (3:ℕ) * c * e ^ (2:ℕ) * xv + (kp * r ^ (5:ℕ)
  * w ^ (3:ℕ) * c * e ^ (2:ℕ) * xv + kp ^ (3:ℕ) * r * w ^ (5:ℕ) * c * e ^ (2:ℕ) * xv))) + ((2 *
  kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (5:ℕ) * c * e ^ (2:ℕ) * xv + (kp * r ^ (3:ℕ) * w ^ (5:ℕ) * c * e
  ^ (2:ℕ) * xv + kp ^ (4:ℕ) * r * w ^ (3:ℕ) * c * P * e ^ (2:ℕ) * xv)) + ((6 * kp ^ (3:ℕ) * r ^
  (2:ℕ) * w ^ (3:ℕ) * c * P * e ^ (2:ℕ) * xv + 5 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (3:ℕ) * c * P *
  e ^ (2:ℕ) * xv) + (-4 * kp ^ (3:ℕ) * w ^ (5:ℕ) * c * P * e ^ (2:ℕ) * xv - 4 * kp ^ (2:ℕ) * r
  * w ^ (5:ℕ) * c * P * e ^ (2:ℕ) * xv)))) + (((-2 * kp ^ (3:ℕ) * r * w ^ (3:ℕ) * c * P ^ (2:ℕ)
  * e ^ (2:ℕ) * xv + (12 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * e ^ (2:ℕ) * q * xv + 12 * kp ^
  (3:ℕ) * r ^ (3:ℕ) * w ^ (3:ℕ) * e ^ (2:ℕ) * q * xv)) + ((2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^
  (3:ℕ) * e ^ (2:ℕ) * q * xv - 6 * kp ^ (3:ℕ) * r * w ^ (5:ℕ) * e ^ (2:ℕ) * q * xv) + (-4 * kp
  ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (5:ℕ) * e ^ (2:ℕ) * q * xv + 5 * kp ^ (4:ℕ) * r * w ^ (3:ℕ) * P * e
  ^ (2:ℕ) * q * xv))) + ((5 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * P * e ^ (2:ℕ) * q * xv + (kp
  ^ (3:ℕ) * w ^ (5:ℕ) * P * e ^ (2:ℕ) * q * xv - 3 * kp ^ (3:ℕ) * r * w ^ (3:ℕ) * c * e ^ (3:ℕ)
  * q * xv)) + ((5 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * e ^ (2:ℕ) * κ * xv + 6 * kp ^ (3:ℕ) *
  r ^ (3:ℕ) * w ^ (3:ℕ) * e ^ (2:ℕ) * κ * xv) + (kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (3:ℕ) * e ^ (2:ℕ)
  * κ * xv - 5 * kp ^ (4:ℕ) * r * w ^ (3:ℕ) * P * e ^ (2:ℕ) * κ * xv))))) + ((((-5 * kp ^ (3:ℕ)
  * r ^ (2:ℕ) * w ^ (3:ℕ) * P * e ^ (2:ℕ) * κ * xv + (-2 * kp ^ (4:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) *
  e ^ (2:ℕ) * κ * xv - kp ^ (3:ℕ) * r * w ^ (3:ℕ) * c * e ^ (3:ℕ) * κ * xv)) + ((kp ^ (5:ℕ) * r
  ^ (3:ℕ) * w * P * e * rv * xv + 2 * kp ^ (4:ℕ) * r ^ (4:ℕ) * w * P * e * rv * xv) + (kp ^
  (3:ℕ) * r ^ (5:ℕ) * w * P * e * rv * xv - kp ^ (5:ℕ) * r * w ^ (3:ℕ) * P * e * rv * xv))) +
  ((-4 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * P * e * rv * xv + (-5 * kp ^ (3:ℕ) * r ^ (3:ℕ) *
  w ^ (3:ℕ) * P * e * rv * xv - 2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (3:ℕ) * P * e * rv * xv)) +
  ((-8 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w * P ^ (2:ℕ) * e * rv * xv - 12 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w
  * P ^ (2:ℕ) * e * rv * xv) + (-4 * kp ^ (2:ℕ) * r ^ (5:ℕ) * w * P ^ (2:ℕ) * e * rv * xv + kp
  ^ (5:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * e * rv * xv)))) + (((10 * kp ^ (4:ℕ) * r * w ^ (3:ℕ) * P ^
  (2:ℕ) * e * rv * xv + (9 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * e * rv * xv + 3 *
  kp ^ (5:ℕ) * r * w * P ^ (3:ℕ) * e * rv * xv)) + ((-7 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w * P ^
  (3:ℕ) * e * rv * xv - 7 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w * P ^ (3:ℕ) * e * rv * xv) + (-kp ^
  (4:ℕ) * w ^ (3:ℕ) * P ^ (3:ℕ) * e * rv * xv - 5 * kp ^ (3:ℕ) * r * w ^ (3:ℕ) * P ^ (3:ℕ) * e
  * rv * xv))) + ((-kp ^ (4:ℕ) * w ^ (3:ℕ) * c * P * e ^ (2:ℕ) * rv * xv + (2 * kp ^ (3:ℕ) * r
  * w ^ (3:ℕ) * c * P * e ^ (2:ℕ) * rv * xv + 3 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * c * P *
  e ^ (2:ℕ) * rv * xv)) + ((-2 * kp ^ (3:ℕ) * w ^ (3:ℕ) * c * P ^ (2:ℕ) * e ^ (2:ℕ) * rv * xv -
  3 * kp ^ (4:ℕ) * r * w ^ (3:ℕ) * e ^ (2:ℕ) * q * rv * xv) + (-8 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w
  ^ (3:ℕ) * e ^ (2:ℕ) * q * rv * xv - 5 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (3:ℕ) * e ^ (2:ℕ) * q *
  rv * xv))))))))) + ((((((((9 * kp ^ (4:ℕ) * w ^ (3:ℕ) * P * e ^ (2:ℕ) * q * rv * xv + (9 * kp
  ^ (3:ℕ) * r * w ^ (3:ℕ) * P * e ^ (2:ℕ) * q * rv * xv - 2 * kp ^ (3:ℕ) * w ^ (3:ℕ) * c * e ^
  (3:ℕ) * q * rv * xv)) + (5 * kp ^ (4:ℕ) * w ^ (3:ℕ) * P * e ^ (2:ℕ) * κ * rv * xv + (3 * kp ^
  (3:ℕ) * r * w ^ (3:ℕ) * P * e ^ (2:ℕ) * κ * rv * xv - kp ^ (5:ℕ) * r * w * P ^ (2:ℕ) * e * rv
  ^ (2:ℕ) * xv))) + ((-6 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w * P ^ (2:ℕ) * e * rv ^ (2:ℕ) * xv + (-7 *
  kp ^ (3:ℕ) * r ^ (3:ℕ) * w * P ^ (2:ℕ) * e * rv ^ (2:ℕ) * xv - 2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w
  * P ^ (2:ℕ) * e * rv ^ (2:ℕ) * xv)) + ((-2 * kp ^ (4:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * e * rv ^
  (2:ℕ) * xv - 4 * kp ^ (3:ℕ) * r * w ^ (3:ℕ) * P ^ (2:ℕ) * e * rv ^ (2:ℕ) * xv) + (-2 * kp ^
  (2:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * e * rv ^ (2:ℕ) * xv + kp ^ (5:ℕ) * w * P ^ (3:ℕ)
  * e * rv ^ (2:ℕ) * xv)))) + (((-9 * kp ^ (4:ℕ) * r * w * P ^ (3:ℕ) * e * rv ^ (2:ℕ) * xv +
  (-7 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w * P ^ (3:ℕ) * e * rv ^ (2:ℕ) * xv - 2 * kp ^ (3:ℕ) * w ^
  (3:ℕ) * P ^ (3:ℕ) * e * rv ^ (2:ℕ) * xv)) + ((-2 * kp ^ (3:ℕ) * w ^ (3:ℕ) * P * e ^ (2:ℕ) * q
  * rv ^ (2:ℕ) * xv - 3 * kp ^ (4:ℕ) * w * P ^ (3:ℕ) * e * rv ^ (3:ℕ) * xv) + (-2 * kp ^ (3:ℕ)
  * r * w * P ^ (3:ℕ) * e * rv ^ (3:ℕ) * xv + kp ^ (5:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * e * xv ^
  (2:ℕ)))) + ((4 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P * e * xv ^ (2:ℕ) + (5 * kp ^ (3:ℕ) *
  r ^ (4:ℕ) * w ^ (2:ℕ) * P * e * xv ^ (2:ℕ) + 2 * kp ^ (2:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * P * e *
  xv ^ (2:ℕ))) + ((kp ^ (4:ℕ) * r * w ^ (4:ℕ) * P * e * xv ^ (2:ℕ) + 2 * kp ^ (3:ℕ) * r ^ (2:ℕ)
  * w ^ (4:ℕ) * P * e * xv ^ (2:ℕ)) + (kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * P * e * xv ^ (2:ℕ)
  - 5 * kp ^ (5:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * e * xv ^ (2:ℕ)))))) + ((((-10 * kp ^ (4:ℕ) * r
  ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e * xv ^ (2:ℕ) + (-9 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) *
  P ^ (2:ℕ) * e * xv ^ (2:ℕ) - 4 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e * xv ^
  (2:ℕ))) + (-2 * kp ^ (4:ℕ) * w ^ (4:ℕ) * P ^ (2:ℕ) * e * xv ^ (2:ℕ) + (-4 * kp ^ (3:ℕ) * r *
  w ^ (4:ℕ) * P ^ (2:ℕ) * e * xv ^ (2:ℕ) - 2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * P ^ (2:ℕ) *
  e * xv ^ (2:ℕ)))) + ((2 * kp ^ (5:ℕ) * w ^ (2:ℕ) * P ^ (3:ℕ) * e * xv ^ (2:ℕ) + (-kp ^ (4:ℕ)
  * r * w ^ (2:ℕ) * P ^ (3:ℕ) * e * xv ^ (2:ℕ) - 4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^
  (3:ℕ) * e * xv ^ (2:ℕ))) + ((2 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * c * P * e ^ (2:ℕ) * xv ^ (2:ℕ)
  + 4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P * e ^ (2:ℕ) * xv ^ (2:ℕ)) + (2 * kp ^ (2:ℕ)
  * r ^ (3:ℕ) * w ^ (2:ℕ) * c * P * e ^ (2:ℕ) * xv ^ (2:ℕ) - 2 * kp ^ (3:ℕ) * w ^ (4:ℕ) * c * P
  * e ^ (2:ℕ) * xv ^ (2:ℕ))))) + (((-2 * kp ^ (2:ℕ) * r * w ^ (4:ℕ) * c * P * e ^ (2:ℕ) * xv ^
  (2:ℕ) + (-kp ^ (3:ℕ) * r * w ^ (2:ℕ) * c * P ^ (2:ℕ) * e ^ (2:ℕ) * xv ^ (2:ℕ) + 5 * kp ^
  (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) * q * xv ^ (2:ℕ))) + ((7 * kp ^ (3:ℕ) * r ^ (3:ℕ) *
  w ^ (2:ℕ) * e ^ (2:ℕ) * q * xv ^ (2:ℕ) + 3 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) *
  q * xv ^ (2:ℕ)) + (-3 * kp ^ (3:ℕ) * r * w ^ (4:ℕ) * e ^ (2:ℕ) * q * xv ^ (2:ℕ) - 2 * kp ^
  (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * e ^ (2:ℕ) * q * xv ^ (2:ℕ)))) + ((-3 * kp ^ (4:ℕ) * r * w ^
  (2:ℕ) * P * e ^ (2:ℕ) * q * xv ^ (2:ℕ) + (-kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ)
  * q * xv ^ (2:ℕ) + 2 * kp ^ (3:ℕ) * w ^ (4:ℕ) * P * e ^ (2:ℕ) * q * xv ^ (2:ℕ))) + ((-7 * kp
  ^ (4:ℕ) * r * w ^ (2:ℕ) * P * e ^ (2:ℕ) * κ * xv ^ (2:ℕ) - 6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^
  (2:ℕ) * P * e ^ (2:ℕ) * κ * xv ^ (2:ℕ)) + (-kp ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e ^ (2:ℕ) *
  κ * xv ^ (2:ℕ) + kp ^ (5:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e * rv * xv ^ (2:ℕ))))))) + (((((9 * kp
  ^ (4:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * e * rv * xv ^ (2:ℕ) + (11 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w
  ^ (2:ℕ) * P ^ (2:ℕ) * e * rv * xv ^ (2:ℕ) + 3 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^
  (2:ℕ) * e * rv * xv ^ (2:ℕ))) + (-5 * kp ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (3:ℕ) * e * rv * xv ^
  (2:ℕ) + (-7 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P ^ (3:ℕ) * e * rv * xv ^ (2:ℕ) - kp ^ (3:ℕ) * w ^
  (2:ℕ) * c * P ^ (2:ℕ) * e ^ (2:ℕ) * rv * xv ^ (2:ℕ)))) + ((kp ^ (4:ℕ) * w ^ (2:ℕ) * P * e ^
  (2:ℕ) * q * rv * xv ^ (2:ℕ) + (4 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P * e ^ (2:ℕ) * q * rv * xv ^
  (2:ℕ) - kp ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (3:ℕ) * e * rv ^ (2:ℕ) * xv ^ (2:ℕ))) + ((-2 * kp ^
  (5:ℕ) * r * w * P ^ (2:ℕ) * e * xv ^ (3:ℕ) - 7 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w * P ^ (2:ℕ) * e *
  xv ^ (3:ℕ)) + (-8 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w * P ^ (2:ℕ) * e * xv ^ (3:ℕ) - 3 * kp ^ (2:ℕ)
  * r ^ (4:ℕ) * w * P ^ (2:ℕ) * e * xv ^ (3:ℕ))))) + (((-kp ^ (4:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * e
  * xv ^ (3:ℕ) + (-2 * kp ^ (3:ℕ) * r * w ^ (3:ℕ) * P ^ (2:ℕ) * e * xv ^ (3:ℕ) - kp ^ (2:ℕ) * r
  ^ (2:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * e * xv ^ (3:ℕ))) + ((kp ^ (5:ℕ) * w * P ^ (3:ℕ) * e * xv ^
  (3:ℕ) - kp ^ (4:ℕ) * r * w * P ^ (3:ℕ) * e * xv ^ (3:ℕ)) + (-2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w *
  P ^ (3:ℕ) * e * xv ^ (3:ℕ) + kp ^ (3:ℕ) * w ^ (3:ℕ) * P * e ^ (2:ℕ) * q * xv ^ (3:ℕ)))) +
  ((-3 * kp ^ (4:ℕ) * w * P ^ (3:ℕ) * e * rv * xv ^ (3:ℕ) + (-3 * kp ^ (3:ℕ) * r * w * P ^
  (3:ℕ) * e * rv * xv ^ (3:ℕ) + kp ^ (5:ℕ) * r ^ (5:ℕ) * P ^ (2:ℕ))) + ((2 * kp ^ (4:ℕ) * r ^
  (6:ℕ) * P ^ (2:ℕ) + kp ^ (3:ℕ) * r ^ (7:ℕ) * P ^ (2:ℕ)) + (2 * kp ^ (5:ℕ) * r ^ (3:ℕ) * w ^
  (2:ℕ) * P ^ (2:ℕ) + 4 * kp ^ (4:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ)))))) + ((((2 * kp ^
  (3:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) + (kp ^ (5:ℕ) * r * w ^ (4:ℕ) * P ^ (2:ℕ) + 2 * kp
  ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * P ^ (2:ℕ))) + ((kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * P ^
  (2:ℕ) + 2 * kp ^ (5:ℕ) * r ^ (4:ℕ) * P ^ (3:ℕ)) + (2 * kp ^ (4:ℕ) * r ^ (5:ℕ) * P ^ (3:ℕ) + 2
  * kp ^ (5:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (3:ℕ)))) + ((2 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^
  (2:ℕ) * P ^ (3:ℕ) + (kp ^ (5:ℕ) * r ^ (3:ℕ) * P ^ (4:ℕ) + kp ^ (5:ℕ) * r * w ^ (2:ℕ) * P ^
  (4:ℕ))) + ((-kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * c * P * e - kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^
  (2:ℕ) * c * P * e) + (kp ^ (2:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * c * P * e + kp * r ^ (6:ℕ) * w ^
  (2:ℕ) * c * P * e)))) + (((-kp ^ (4:ℕ) * r * w ^ (4:ℕ) * c * P * e + (3 * kp ^ (2:ℕ) * r ^
  (3:ℕ) * w ^ (4:ℕ) * c * P * e + 2 * kp * r ^ (4:ℕ) * w ^ (4:ℕ) * c * P * e)) + ((kp ^ (3:ℕ) *
  w ^ (6:ℕ) * c * P * e + 2 * kp ^ (2:ℕ) * r * w ^ (6:ℕ) * c * P * e) + (kp * r ^ (2:ℕ) * w ^
  (6:ℕ) * c * P * e - kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * e))) + ((2 * kp ^
  (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * e + (3 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) *
  c * P ^ (2:ℕ) * e - kp ^ (4:ℕ) * w ^ (4:ℕ) * c * P ^ (2:ℕ) * e)) + ((2 * kp ^ (3:ℕ) * r * w ^
  (4:ℕ) * c * P ^ (2:ℕ) * e + 3 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * c * P ^ (2:ℕ) * e) + (kp
  ^ (3:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * e * q + 2 * kp ^ (2:ℕ) * r ^ (6:ℕ) * w ^ (2:ℕ) * e *
  q))))))) + ((((((kp * r ^ (7:ℕ) * w ^ (2:ℕ) * e * q + (4 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ)
  * e * q + 6 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (4:ℕ) * e * q)) + (2 * kp * r ^ (5:ℕ) * w ^ (4:ℕ)
  * e * q + (3 * kp ^ (3:ℕ) * r * w ^ (6:ℕ) * e * q + 4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (6:ℕ) *
  e * q))) + ((kp * r ^ (3:ℕ) * w ^ (6:ℕ) * e * q + (6 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P
  * e * q + 8 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * P * e * q)) + ((2 * kp ^ (2:ℕ) * r ^ (5:ℕ)
  * w ^ (2:ℕ) * P * e * q + 2 * kp ^ (4:ℕ) * r * w ^ (4:ℕ) * P * e * q) + (4 * kp ^ (3:ℕ) * r ^
  (2:ℕ) * w ^ (4:ℕ) * P * e * q + 2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * P * e * q)))) + (((2
  * kp ^ (5:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * e * q + (2 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) *
  P ^ (2:ℕ) * e * q + kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e * q)) + ((kp ^ (3:ℕ) *
  r * w ^ (4:ℕ) * P ^ (2:ℕ) * e * q + 3 * kp ^ (3:ℕ) * r * w ^ (4:ℕ) * c * e ^ (2:ℕ) * q) + (kp
  ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * c * e ^ (2:ℕ) * q - kp ^ (2:ℕ) * w ^ (6:ℕ) * c * e ^ (2:ℕ)
  * q))) + ((-2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P * e ^ (2:ℕ) * q + (kp ^ (3:ℕ) * w
  ^ (4:ℕ) * c * P * e ^ (2:ℕ) * q + kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) * q ^
  (2:ℕ))) + ((3 * kp ^ (3:ℕ) * r * w ^ (4:ℕ) * e ^ (2:ℕ) * q ^ (2:ℕ) - kp ^ (4:ℕ) * r * w ^
  (2:ℕ) * P * e ^ (2:ℕ) * q ^ (2:ℕ)) + (kp ^ (4:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * e * κ + 2 * kp ^
  (3:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * e * κ))))) + ((((kp ^ (2:ℕ) * r ^ (6:ℕ) * w ^ (2:ℕ) * e * κ +
  (kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * e * κ + 2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * e *
  κ)) + (kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (4:ℕ) * e * κ + (-2 * kp ^ (5:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ)
  * P * e * κ + 5 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P * e * κ))) + ((8 * kp ^ (3:ℕ) * r ^
  (4:ℕ) * w ^ (2:ℕ) * P * e * κ + (kp ^ (2:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * P * e * κ + 5 * kp ^
  (4:ℕ) * r * w ^ (4:ℕ) * P * e * κ)) + ((6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * P * e * κ +
  kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * P * e * κ) + (2 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P
  ^ (2:ℕ) * e * κ - kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e * κ)))) + (((kp ^ (4:ℕ)
  * w ^ (4:ℕ) * P ^ (2:ℕ) * e * κ + (-kp ^ (3:ℕ) * r * w ^ (4:ℕ) * P ^ (2:ℕ) * e * κ + kp ^
  (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * e ^ (2:ℕ) * κ)) + ((2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^
  (2:ℕ) * c * e ^ (2:ℕ) * κ + kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * c * e ^ (2:ℕ) * κ) + (-2 *
  kp ^ (3:ℕ) * r * w ^ (4:ℕ) * c * e ^ (2:ℕ) * κ - 2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * c *
  e ^ (2:ℕ) * κ))) + ((-2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P * e ^ (2:ℕ) * κ + (-kp ^
  (3:ℕ) * w ^ (4:ℕ) * c * P * e ^ (2:ℕ) * κ - 4 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * e ^
  (2:ℕ) * q * κ)) + ((-2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) * q * κ + kp ^ (3:ℕ)
  * r * w ^ (4:ℕ) * e ^ (2:ℕ) * q * κ) + (-2 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P * e ^ (2:ℕ) * q *
  κ - 4 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) * κ ^ (2:ℕ))))))) + (((((-3 * kp ^
  (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) * κ ^ (2:ℕ) + (-kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P * e
  ^ (2:ℕ) * κ ^ (2:ℕ) + 3 * kp ^ (5:ℕ) * r ^ (4:ℕ) * P ^ (2:ℕ) * rv)) + (6 * kp ^ (4:ℕ) * r ^
  (5:ℕ) * P ^ (2:ℕ) * rv + (3 * kp ^ (3:ℕ) * r ^ (6:ℕ) * P ^ (2:ℕ) * rv + 3 * kp ^ (5:ℕ) * r ^
  (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * rv))) + ((5 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ)
  * rv + (kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * rv - kp ^ (2:ℕ) * r ^ (5:ℕ) * w ^
  (2:ℕ) * P ^ (2:ℕ) * rv)) + ((-kp ^ (4:ℕ) * r * w ^ (4:ℕ) * P ^ (2:ℕ) * rv - 2 * kp ^ (3:ℕ) *
  r ^ (2:ℕ) * w ^ (4:ℕ) * P ^ (2:ℕ) * rv) + (-kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * P ^ (2:ℕ) *
  rv + 6 * kp ^ (5:ℕ) * r ^ (3:ℕ) * P ^ (3:ℕ) * rv)))) + (((4 * kp ^ (4:ℕ) * r ^ (4:ℕ) * P ^
  (3:ℕ) * rv + (-2 * kp ^ (3:ℕ) * r ^ (5:ℕ) * P ^ (3:ℕ) * rv + 2 * kp ^ (5:ℕ) * r * w ^ (2:ℕ) *
  P ^ (3:ℕ) * rv)) + ((-2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (3:ℕ) * rv + 3 * kp ^
  (5:ℕ) * r ^ (2:ℕ) * P ^ (4:ℕ) * rv) + (-2 * kp ^ (4:ℕ) * r ^ (3:ℕ) * P ^ (4:ℕ) * rv + kp ^
  (5:ℕ) * w ^ (2:ℕ) * P ^ (4:ℕ) * rv))) + ((-2 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P ^ (4:ℕ) * rv +
  (-4 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P * e * rv - 6 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^
  (2:ℕ) * c * P * e * rv)) + ((2 * kp * r ^ (5:ℕ) * w ^ (2:ℕ) * c * P * e * rv - kp ^ (4:ℕ) * w
  ^ (4:ℕ) * c * P * e * rv) + (3 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * c * P * e * rv + 2 * kp
  * r ^ (3:ℕ) * w ^ (4:ℕ) * c * P * e * rv))))) + ((((-4 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * c * P ^
  (2:ℕ) * e * rv + (6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * e * rv + 10 * kp ^
  (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * e * rv)) + ((4 * kp ^ (3:ℕ) * w ^ (4:ℕ) * c *
  P ^ (2:ℕ) * e * rv + 4 * kp ^ (2:ℕ) * r * w ^ (4:ℕ) * c * P ^ (2:ℕ) * e * rv) + (kp ^ (3:ℕ) *
  w ^ (4:ℕ) * c ^ (2:ℕ) * e ^ (2:ℕ) * rv + 2 * kp ^ (2:ℕ) * r * w ^ (4:ℕ) * c ^ (2:ℕ) * e ^
  (2:ℕ) * rv))) + ((kp * r ^ (2:ℕ) * w ^ (4:ℕ) * c ^ (2:ℕ) * e ^ (2:ℕ) * rv + (2 * kp ^ (4:ℕ) *
  r ^ (3:ℕ) * w ^ (2:ℕ) * e * q * rv + 6 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * e * q * rv)) +
  ((6 * kp ^ (2:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * e * q * rv + 2 * kp * r ^ (6:ℕ) * w ^ (2:ℕ) * e *
  q * rv) + (8 * kp ^ (4:ℕ) * r * w ^ (4:ℕ) * e * q * rv + 18 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^
  (4:ℕ) * e * q * rv)))) + (((12 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * e * q * rv + (2 * kp *
  r ^ (4:ℕ) * w ^ (4:ℕ) * e * q * rv - kp ^ (5:ℕ) * r * w ^ (2:ℕ) * P * e * q * rv)) + ((16 *
  kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * e * q * rv + 23 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ)
  * P * e * q * rv) + (6 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * P * e * q * rv - kp ^ (4:ℕ) * w
  ^ (4:ℕ) * P * e * q * rv))) + ((-kp ^ (3:ℕ) * r * w ^ (4:ℕ) * P * e * q * rv + (kp ^ (5:ℕ) *
  w ^ (2:ℕ) * P ^ (2:ℕ) * e * q * rv + 2 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * e * q *
  rv)) + ((kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e * q * rv + kp ^ (3:ℕ) * w ^ (4:ℕ)
  * P ^ (2:ℕ) * e * q * rv) + (-kp ^ (4:ℕ) * r * w ^ (2:ℕ) * c * e ^ (2:ℕ) * q * rv - 2 * kp ^
  (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * e ^ (2:ℕ) * q * rv)))))))) + (((((((-kp ^ (2:ℕ) * r ^
  (3:ℕ) * w ^ (2:ℕ) * c * e ^ (2:ℕ) * q * rv + (-4 * kp ^ (3:ℕ) * w ^ (4:ℕ) * c * e ^ (2:ℕ) * q
  * rv - 4 * kp ^ (2:ℕ) * r * w ^ (4:ℕ) * c * e ^ (2:ℕ) * q * rv)) + (-4 * kp ^ (3:ℕ) * r * w ^
  (2:ℕ) * c * P * e ^ (2:ℕ) * q * rv + (4 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * e ^ (2:ℕ) * q ^ (2:ℕ)
  * rv + 5 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) * q ^ (2:ℕ) * rv))) + ((kp ^ (3:ℕ)
  * w ^ (4:ℕ) * e ^ (2:ℕ) * q ^ (2:ℕ) * rv + (-kp ^ (4:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) * q ^
  (2:ℕ) * rv - kp ^ (5:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * e * κ * rv)) + ((-kp ^ (4:ℕ) * r ^ (3:ℕ) *
  w ^ (2:ℕ) * e * κ * rv + kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * e * κ * rv) + (kp ^ (2:ℕ) * r ^
  (5:ℕ) * w ^ (2:ℕ) * e * κ * rv + 2 * kp ^ (4:ℕ) * r * w ^ (4:ℕ) * e * κ * rv)))) + (((4 * kp
  ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * e * κ * rv + (2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * e *
  κ * rv - 4 * kp ^ (5:ℕ) * r * w ^ (2:ℕ) * P * e * κ * rv)) + ((15 * kp ^ (4:ℕ) * r ^ (2:ℕ) *
  w ^ (2:ℕ) * P * e * κ * rv + 22 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P * e * κ * rv) + (3 *
  kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * P * e * κ * rv - kp ^ (5:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e
  * κ * rv))) + ((6 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * e * κ * rv + (-5 * kp ^ (3:ℕ) *
  r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e * κ * rv - 2 * kp ^ (3:ℕ) * w ^ (4:ℕ) * P ^ (2:ℕ) * e *
  κ * rv)) + ((kp ^ (4:ℕ) * r * w ^ (2:ℕ) * c * e ^ (2:ℕ) * κ * rv + 2 * kp ^ (3:ℕ) * r ^ (2:ℕ)
  * w ^ (2:ℕ) * c * e ^ (2:ℕ) * κ * rv) + (kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * c * e ^ (2:ℕ) *
  κ * rv - 6 * kp ^ (3:ℕ) * w ^ (4:ℕ) * c * e ^ (2:ℕ) * κ * rv))))) + ((((-6 * kp ^ (2:ℕ) * r *
  w ^ (4:ℕ) * c * e ^ (2:ℕ) * κ * rv + (-4 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * c * P * e ^ (2:ℕ) * κ
  * rv + 2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) * q * κ * rv)) + (-2 * kp ^ (4:ℕ) *
  w ^ (2:ℕ) * P * e ^ (2:ℕ) * q * κ * rv + (-4 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * e ^ (2:ℕ) * κ ^
  (2:ℕ) * rv - 3 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) * κ ^ (2:ℕ) * rv))) + ((kp ^
  (3:ℕ) * w ^ (4:ℕ) * e ^ (2:ℕ) * κ ^ (2:ℕ) * rv + (-kp ^ (4:ℕ) * w ^ (2:ℕ) * P * e ^ (2:ℕ) * κ
  ^ (2:ℕ) * rv + 3 * kp ^ (5:ℕ) * r ^ (3:ℕ) * P ^ (2:ℕ) * rv ^ (2:ℕ))) + ((6 * kp ^ (4:ℕ) * r ^
  (4:ℕ) * P ^ (2:ℕ) * rv ^ (2:ℕ) + 3 * kp ^ (3:ℕ) * r ^ (5:ℕ) * P ^ (2:ℕ) * rv ^ (2:ℕ)) + (kp ^
  (5:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * rv ^ (2:ℕ) - 3 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^
  (2:ℕ) * rv ^ (2:ℕ))))) + (((-2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * rv ^ (2:ℕ)
  + (6 * kp ^ (5:ℕ) * r ^ (2:ℕ) * P ^ (3:ℕ) * rv ^ (2:ℕ) - 6 * kp ^ (3:ℕ) * r ^ (4:ℕ) * P ^
  (3:ℕ) * rv ^ (2:ℕ))) + ((-2 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P ^ (3:ℕ) * rv ^ (2:ℕ) - 2 * kp ^
  (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (3:ℕ) * rv ^ (2:ℕ)) + (3 * kp ^ (5:ℕ) * r * P ^ (4:ℕ) *
  rv ^ (2:ℕ) - 6 * kp ^ (4:ℕ) * r ^ (2:ℕ) * P ^ (4:ℕ) * rv ^ (2:ℕ)))) + ((kp ^ (3:ℕ) * r ^
  (3:ℕ) * P ^ (4:ℕ) * rv ^ (2:ℕ) + (-2 * kp ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (4:ℕ) * rv ^ (2:ℕ) + kp ^
  (3:ℕ) * r * w ^ (2:ℕ) * P ^ (4:ℕ) * rv ^ (2:ℕ))) + ((-3 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * c * P
  * e * rv ^ (2:ℕ) - 5 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P * e * rv ^ (2:ℕ)) + (-kp ^
  (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * c * P * e * rv ^ (2:ℕ) + kp * r ^ (4:ℕ) * w ^ (2:ℕ) * c * P *
  e * rv ^ (2:ℕ))))))) + (((((2 * kp ^ (3:ℕ) * w ^ (4:ℕ) * c * P * e * rv ^ (2:ℕ) + (4 * kp ^
  (2:ℕ) * r * w ^ (4:ℕ) * c * P * e * rv ^ (2:ℕ) + 2 * kp * r ^ (2:ℕ) * w ^ (4:ℕ) * c * P * e *
  rv ^ (2:ℕ))) + (-3 * kp ^ (4:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * e * rv ^ (2:ℕ) + (10 * kp ^
  (3:ℕ) * r * w ^ (2:ℕ) * c * P ^ (2:ℕ) * e * rv ^ (2:ℕ) + 13 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^
  (2:ℕ) * c * P ^ (2:ℕ) * e * rv ^ (2:ℕ)))) + ((kp ^ (5:ℕ) * r * w ^ (2:ℕ) * e * q * rv ^ (2:ℕ)
  + (4 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * e * q * rv ^ (2:ℕ) + 6 * kp ^ (3:ℕ) * r ^ (3:ℕ) *
  w ^ (2:ℕ) * e * q * rv ^ (2:ℕ))) + ((4 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * e * q * rv ^
  (2:ℕ) + kp * r ^ (5:ℕ) * w ^ (2:ℕ) * e * q * rv ^ (2:ℕ)) + (kp ^ (5:ℕ) * w ^ (2:ℕ) * P * e *
  q * rv ^ (2:ℕ) + 12 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P * e * q * rv ^ (2:ℕ))))) + (((13 * kp ^
  (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * e * q * rv ^ (2:ℕ) + (2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^
  (2:ℕ) * P * e * q * rv ^ (2:ℕ) + 2 * kp ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e * q * rv ^
  (2:ℕ))) + ((-kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * e * q * rv ^ (2:ℕ) - kp ^ (4:ℕ) * w ^
  (2:ℕ) * c * e ^ (2:ℕ) * q * rv ^ (2:ℕ)) + (-2 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * c * e ^ (2:ℕ) *
  q * rv ^ (2:ℕ) - kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * e ^ (2:ℕ) * q * rv ^ (2:ℕ)))) +
  ((-2 * kp ^ (3:ℕ) * w ^ (2:ℕ) * c * P * e ^ (2:ℕ) * q * rv ^ (2:ℕ) + (4 * kp ^ (4:ℕ) * w ^
  (2:ℕ) * e ^ (2:ℕ) * q ^ (2:ℕ) * rv ^ (2:ℕ) + 4 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * e ^ (2:ℕ) * q ^
  (2:ℕ) * rv ^ (2:ℕ))) + ((14 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P * e * κ * rv ^ (2:ℕ) + 16 * kp ^
  (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * e * κ * rv ^ (2:ℕ)) + (2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^
  (2:ℕ) * P * e * κ * rv ^ (2:ℕ) + 6 * kp ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e * κ * rv ^
  (2:ℕ)))))) + ((((-9 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * e * κ * rv ^ (2:ℕ) + (-2 * kp
  ^ (3:ℕ) * w ^ (2:ℕ) * c * P * e ^ (2:ℕ) * κ * rv ^ (2:ℕ) + 4 * kp ^ (4:ℕ) * w ^ (2:ℕ) * e ^
  (2:ℕ) * q * κ * rv ^ (2:ℕ))) + ((4 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * e ^ (2:ℕ) * q * κ * rv ^
  (2:ℕ) + kp ^ (5:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ) * rv ^ (3:ℕ)) + (2 * kp ^ (4:ℕ) * r ^ (3:ℕ) * P ^
  (2:ℕ) * rv ^ (3:ℕ) + kp ^ (3:ℕ) * r ^ (4:ℕ) * P ^ (2:ℕ) * rv ^ (3:ℕ)))) + ((-kp ^ (4:ℕ) * r *
  w ^ (2:ℕ) * P ^ (2:ℕ) * rv ^ (3:ℕ) + (-2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) *
  rv ^ (3:ℕ) - kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * rv ^ (3:ℕ))) + ((2 * kp ^ (5:ℕ)
  * r * P ^ (3:ℕ) * rv ^ (3:ℕ) - 4 * kp ^ (4:ℕ) * r ^ (2:ℕ) * P ^ (3:ℕ) * rv ^ (3:ℕ)) + (-6 *
  kp ^ (3:ℕ) * r ^ (3:ℕ) * P ^ (3:ℕ) * rv ^ (3:ℕ) + kp ^ (5:ℕ) * P ^ (4:ℕ) * rv ^ (3:ℕ))))) +
  (((-6 * kp ^ (4:ℕ) * r * P ^ (4:ℕ) * rv ^ (3:ℕ) + (3 * kp ^ (3:ℕ) * r ^ (2:ℕ) * P ^ (4:ℕ) *
  rv ^ (3:ℕ) + kp ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (4:ℕ) * rv ^ (3:ℕ))) + ((6 * kp ^ (3:ℕ) * w ^ (2:ℕ)
  * c * P ^ (2:ℕ) * e * rv ^ (3:ℕ) + 6 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * c * P ^ (2:ℕ) * e * rv ^
  (3:ℕ)) + (-2 * kp ^ (4:ℕ) * w ^ (2:ℕ) * P * e * q * rv ^ (3:ℕ) - 4 * kp ^ (3:ℕ) * r * w ^
  (2:ℕ) * P * e * q * rv ^ (3:ℕ)))) + ((-2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * e * q *
  rv ^ (3:ℕ) + (-2 * kp ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e * q * rv ^ (3:ℕ) - 6 * kp ^ (3:ℕ) *
  w ^ (2:ℕ) * P ^ (2:ℕ) * e * κ * rv ^ (3:ℕ))) + ((-2 * kp ^ (4:ℕ) * r * P ^ (3:ℕ) * rv ^ (4:ℕ)
  - 2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * P ^ (3:ℕ) * rv ^ (4:ℕ)) + (-2 * kp ^ (4:ℕ) * P ^ (4:ℕ) * rv ^
  (4:ℕ) + 3 * kp ^ (3:ℕ) * r * P ^ (4:ℕ) * rv ^ (4:ℕ)))))))) + ((((((kp ^ (3:ℕ) * P ^ (4:ℕ) *
  rv ^ (5:ℕ) + (3 * kp ^ (5:ℕ) * r ^ (3:ℕ) * w * P ^ (2:ℕ) * xv + 7 * kp ^ (4:ℕ) * r ^ (4:ℕ) *
  w * P ^ (2:ℕ) * xv)) + (5 * kp ^ (3:ℕ) * r ^ (5:ℕ) * w * P ^ (2:ℕ) * xv + (kp ^ (2:ℕ) * r ^
  (6:ℕ) * w * P ^ (2:ℕ) * xv + 3 * kp ^ (5:ℕ) * r * w ^ (3:ℕ) * P ^ (2:ℕ) * xv))) + ((7 * kp ^
  (4:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * xv + (5 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (3:ℕ) * P
  ^ (2:ℕ) * xv + kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * xv)) + ((3 * kp ^ (5:ℕ) * r ^
  (2:ℕ) * w * P ^ (3:ℕ) * xv + 2 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w * P ^ (3:ℕ) * xv) + (-kp ^ (3:ℕ)
  * r ^ (4:ℕ) * w * P ^ (3:ℕ) * xv - kp ^ (5:ℕ) * w ^ (3:ℕ) * P ^ (3:ℕ) * xv)))) + (((-2 * kp ^
  (4:ℕ) * r * w ^ (3:ℕ) * P ^ (3:ℕ) * xv + (-kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * P ^ (3:ℕ) *
  xv + 2 * kp ^ (5:ℕ) * r * w * P ^ (4:ℕ) * xv)) + ((2 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w * c * P * e
  * xv + 4 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w * c * P * e * xv) + (2 * kp ^ (2:ℕ) * r ^ (5:ℕ) * w * c
  * P * e * xv - kp ^ (4:ℕ) * r * w ^ (3:ℕ) * c * P * e * xv))) + ((3 * kp ^ (2:ℕ) * r ^ (3:ℕ)
  * w ^ (3:ℕ) * c * P * e * xv + (2 * kp * r ^ (4:ℕ) * w ^ (3:ℕ) * c * P * e * xv + 2 * kp ^
  (3:ℕ) * w ^ (5:ℕ) * c * P * e * xv)) + ((4 * kp ^ (2:ℕ) * r * w ^ (5:ℕ) * c * P * e * xv + 2
  * kp * r ^ (2:ℕ) * w ^ (5:ℕ) * c * P * e * xv) + (3 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w * c * P ^
  (2:ℕ) * e * xv + 4 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w * c * P ^ (2:ℕ) * e * xv))))) + ((((kp ^
  (2:ℕ) * r ^ (4:ℕ) * w * c * P ^ (2:ℕ) * e * xv + (-kp ^ (4:ℕ) * w ^ (3:ℕ) * c * P ^ (2:ℕ) * e
  * xv + 6 * kp ^ (3:ℕ) * r * w ^ (3:ℕ) * c * P ^ (2:ℕ) * e * xv)) + ((7 * kp ^ (2:ℕ) * r ^
  (2:ℕ) * w ^ (3:ℕ) * c * P ^ (2:ℕ) * e * xv - kp ^ (3:ℕ) * r * w ^ (3:ℕ) * c ^ (2:ℕ) * e ^
  (2:ℕ) * xv) + (-2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * c ^ (2:ℕ) * e ^ (2:ℕ) * xv - kp * r
  ^ (3:ℕ) * w ^ (3:ℕ) * c ^ (2:ℕ) * e ^ (2:ℕ) * xv))) + ((-3 * kp ^ (4:ℕ) * r ^ (4:ℕ) * w * e *
  q * xv + (-6 * kp ^ (3:ℕ) * r ^ (5:ℕ) * w * e * q * xv - 3 * kp ^ (2:ℕ) * r ^ (6:ℕ) * w * e *
  q * xv)) + ((-9 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * e * q * xv - 12 * kp ^ (3:ℕ) * r ^
  (3:ℕ) * w ^ (3:ℕ) * e * q * xv) + (-kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (3:ℕ) * e * q * xv + 2 * kp
  * r ^ (5:ℕ) * w ^ (3:ℕ) * e * q * xv)))) + (((6 * kp ^ (3:ℕ) * r * w ^ (5:ℕ) * e * q * xv +
  (8 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (5:ℕ) * e * q * xv + 2 * kp * r ^ (3:ℕ) * w ^ (5:ℕ) * e * q
  * xv)) + ((3 * kp ^ (5:ℕ) * r ^ (2:ℕ) * w * P * e * q * xv - kp ^ (4:ℕ) * r ^ (3:ℕ) * w * P *
  e * q * xv) + (-3 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w * P * e * q * xv + kp ^ (2:ℕ) * r ^ (5:ℕ) * w
  * P * e * q * xv))) + ((6 * kp ^ (4:ℕ) * r * w ^ (3:ℕ) * P * e * q * xv + (11 * kp ^ (3:ℕ) *
  r ^ (2:ℕ) * w ^ (3:ℕ) * P * e * q * xv + 5 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (3:ℕ) * P * e * q *
  xv)) + ((-2 * kp ^ (3:ℕ) * w ^ (5:ℕ) * P * e * q * xv - 2 * kp ^ (2:ℕ) * r * w ^ (5:ℕ) * P *
  e * q * xv) + (4 * kp ^ (5:ℕ) * r * w * P ^ (2:ℕ) * e * q * xv - 6 * kp ^ (4:ℕ) * r ^ (2:ℕ) *
  w * P ^ (2:ℕ) * e * q * xv)))))) + (((((-3 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w * P ^ (2:ℕ) * e * q *
  xv + (-2 * kp ^ (4:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * e * q * xv + 3 * kp ^ (3:ℕ) * r * w ^ (3:ℕ) *
  P ^ (2:ℕ) * e * q * xv)) + (12 * kp ^ (3:ℕ) * r * w ^ (3:ℕ) * c * e ^ (2:ℕ) * q * xv + (8 *
  kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * c * e ^ (2:ℕ) * q * xv - 2 * kp ^ (2:ℕ) * w ^ (5:ℕ) * c
  * e ^ (2:ℕ) * q * xv))) + ((2 * kp ^ (3:ℕ) * w ^ (3:ℕ) * c * P * e ^ (2:ℕ) * q * xv + (7 * kp
  ^ (3:ℕ) * r * w ^ (3:ℕ) * e ^ (2:ℕ) * q ^ (2:ℕ) * xv + kp ^ (5:ℕ) * r ^ (3:ℕ) * w * e * κ *
  xv)) + ((2 * kp ^ (4:ℕ) * r ^ (4:ℕ) * w * e * κ * xv + kp ^ (3:ℕ) * r ^ (5:ℕ) * w * e * κ *
  xv) + (-kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * e * κ * xv - 2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^
  (3:ℕ) * e * κ * xv)))) + (((-kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (3:ℕ) * e * κ * xv + (kp ^ (5:ℕ) *
  r ^ (2:ℕ) * w * P * e * κ * xv - 4 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w * P * e * κ * xv)) + ((-7 *
  kp ^ (3:ℕ) * r ^ (4:ℕ) * w * P * e * κ * xv - 2 * kp ^ (2:ℕ) * r ^ (5:ℕ) * w * P * e * κ *
  xv) + (9 * kp ^ (4:ℕ) * r * w ^ (3:ℕ) * P * e * κ * xv + 10 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^
  (3:ℕ) * P * e * κ * xv))) + ((kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (3:ℕ) * P * e * κ * xv + (2 * kp ^
  (5:ℕ) * r * w * P ^ (2:ℕ) * e * κ * xv - 6 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w * P ^ (2:ℕ) * e * κ *
  xv)) + ((-5 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w * P ^ (2:ℕ) * e * κ * xv - kp ^ (4:ℕ) * w ^ (3:ℕ) *
  P ^ (2:ℕ) * e * κ * xv) + (-5 * kp ^ (3:ℕ) * r * w ^ (3:ℕ) * P ^ (2:ℕ) * e * κ * xv + 4 * kp
  ^ (3:ℕ) * r * w ^ (3:ℕ) * c * e ^ (2:ℕ) * κ * xv))))) + ((((4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^
  (3:ℕ) * c * e ^ (2:ℕ) * κ * xv + (-2 * kp ^ (3:ℕ) * w ^ (3:ℕ) * c * P * e ^ (2:ℕ) * κ * xv +
  2 * kp ^ (3:ℕ) * r * w ^ (3:ℕ) * e ^ (2:ℕ) * q * κ * xv)) + ((-kp ^ (3:ℕ) * r * w ^ (3:ℕ) * e
  ^ (2:ℕ) * κ ^ (2:ℕ) * xv + 4 * kp ^ (5:ℕ) * r ^ (2:ℕ) * w * P ^ (2:ℕ) * rv * xv) + (10 * kp ^
  (4:ℕ) * r ^ (3:ℕ) * w * P ^ (2:ℕ) * rv * xv + 8 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w * P ^ (2:ℕ) * rv
  * xv))) + ((2 * kp ^ (2:ℕ) * r ^ (5:ℕ) * w * P ^ (2:ℕ) * rv * xv + (-2 * kp ^ (4:ℕ) * r * w ^
  (3:ℕ) * P ^ (2:ℕ) * rv * xv - 4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * rv * xv))
  + ((-2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * rv * xv + 2 * kp ^ (5:ℕ) * r * w *
  P ^ (3:ℕ) * rv * xv) + (-3 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w * P ^ (3:ℕ) * rv * xv - 4 * kp ^
  (3:ℕ) * r ^ (3:ℕ) * w * P ^ (3:ℕ) * rv * xv)))) + (((kp ^ (2:ℕ) * r ^ (4:ℕ) * w * P ^ (3:ℕ) *
  rv * xv + (kp ^ (4:ℕ) * w ^ (3:ℕ) * P ^ (3:ℕ) * rv * xv + 2 * kp ^ (3:ℕ) * r * w ^ (3:ℕ) * P
  ^ (3:ℕ) * rv * xv)) + ((kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * P ^ (3:ℕ) * rv * xv + 2 * kp ^
  (5:ℕ) * w * P ^ (4:ℕ) * rv * xv) + (-4 * kp ^ (4:ℕ) * r * w * P ^ (4:ℕ) * rv * xv + 2 * kp ^
  (4:ℕ) * r ^ (2:ℕ) * w * c * P * e * rv * xv))) + ((4 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w * c * P * e
  * rv * xv + (2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w * c * P * e * rv * xv - kp ^ (4:ℕ) * w ^ (3:ℕ) *
  c * P * e * rv * xv)) + ((-4 * kp ^ (3:ℕ) * r * w ^ (3:ℕ) * c * P * e * rv * xv - 5 * kp ^
  (2:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * c * P * e * rv * xv) + (-2 * kp * r ^ (3:ℕ) * w ^ (3:ℕ) * c *
  P * e * rv * xv + 4 * kp ^ (4:ℕ) * r * w * c * P ^ (2:ℕ) * e * rv * xv))))))))))

/-- Terms 874–1746 of `delta8F`. -/
def delta8F1 (kp r w c P e q κ rv xv : ℝ) : ℝ :=
  (((((((((4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w * c * P ^ (2:ℕ) * e * rv * xv + (8 * kp ^ (3:ℕ) * w ^
  (3:ℕ) * c * P ^ (2:ℕ) * e * rv * xv + 8 * kp ^ (2:ℕ) * r * w ^ (3:ℕ) * c * P ^ (2:ℕ) * e * rv
  * xv)) + (-kp ^ (5:ℕ) * r ^ (2:ℕ) * w * e * q * rv * xv + (-5 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w *
  e * q * rv * xv - 7 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w * e * q * rv * xv))) + ((-3 * kp ^ (2:ℕ) * r
  ^ (5:ℕ) * w * e * q * rv * xv + (6 * kp ^ (4:ℕ) * r * w ^ (3:ℕ) * e * q * rv * xv + 14 * kp ^
  (3:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * e * q * rv * xv)) + ((10 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (3:ℕ)
  * e * q * rv * xv + 2 * kp * r ^ (4:ℕ) * w ^ (3:ℕ) * e * q * rv * xv) + (2 * kp ^ (5:ℕ) * r *
  w * P * e * q * rv * xv - kp ^ (4:ℕ) * r ^ (2:ℕ) * w * P * e * q * rv * xv)))) + (((4 * kp ^
  (3:ℕ) * r ^ (3:ℕ) * w * P * e * q * rv * xv + (7 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w * P * e * q *
  rv * xv - 8 * kp ^ (4:ℕ) * w ^ (3:ℕ) * P * e * q * rv * xv)) + ((-14 * kp ^ (3:ℕ) * r * w ^
  (3:ℕ) * P * e * q * rv * xv - 6 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * P * e * q * rv * xv) +
  (3 * kp ^ (5:ℕ) * w * P ^ (2:ℕ) * e * q * rv * xv - 18 * kp ^ (4:ℕ) * r * w * P ^ (2:ℕ) * e *
  q * rv * xv))) + ((-3 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w * P ^ (2:ℕ) * e * q * rv * xv + (5 * kp ^
  (3:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * e * q * rv * xv + 2 * kp ^ (3:ℕ) * w ^ (3:ℕ) * c * e ^ (2:ℕ)
  * q * rv * xv)) + ((2 * kp ^ (2:ℕ) * r * w ^ (3:ℕ) * c * e ^ (2:ℕ) * q * rv * xv + 2 * kp ^
  (3:ℕ) * w ^ (3:ℕ) * e ^ (2:ℕ) * q ^ (2:ℕ) * rv * xv) + (-kp ^ (5:ℕ) * r * w * P * e * κ * rv
  * xv - 8 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w * P * e * κ * rv * xv))))) + ((((-9 * kp ^ (3:ℕ) * r ^
  (3:ℕ) * w * P * e * κ * rv * xv + (-2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w * P * e * κ * rv * xv - 2
  * kp ^ (4:ℕ) * w ^ (3:ℕ) * P * e * κ * rv * xv)) + (-4 * kp ^ (3:ℕ) * r * w ^ (3:ℕ) * P * e *
  κ * rv * xv + (-2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * P * e * κ * rv * xv + kp ^ (5:ℕ) * w
  * P ^ (2:ℕ) * e * κ * rv * xv))) + ((-14 * kp ^ (4:ℕ) * r * w * P ^ (2:ℕ) * e * κ * rv * xv +
  (-9 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w * P ^ (2:ℕ) * e * κ * rv * xv - 4 * kp ^ (3:ℕ) * w ^ (3:ℕ) *
  P ^ (2:ℕ) * e * κ * rv * xv)) + ((-2 * kp ^ (3:ℕ) * w ^ (3:ℕ) * e ^ (2:ℕ) * q * κ * rv * xv +
  kp ^ (5:ℕ) * r * w * P ^ (2:ℕ) * rv ^ (2:ℕ) * xv) + (3 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w * P ^
  (2:ℕ) * rv ^ (2:ℕ) * xv + 3 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w * P ^ (2:ℕ) * rv ^ (2:ℕ) * xv)))) +
  (((kp ^ (2:ℕ) * r ^ (4:ℕ) * w * P ^ (2:ℕ) * rv ^ (2:ℕ) * xv + (-kp ^ (5:ℕ) * w * P ^ (3:ℕ) *
  rv ^ (2:ℕ) * xv - 4 * kp ^ (4:ℕ) * r * w * P ^ (3:ℕ) * rv ^ (2:ℕ) * xv)) + ((-kp ^ (3:ℕ) * r
  ^ (2:ℕ) * w * P ^ (3:ℕ) * rv ^ (2:ℕ) * xv + 2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w * P ^ (3:ℕ) * rv ^
  (2:ℕ) * xv) + (-4 * kp ^ (4:ℕ) * w * P ^ (4:ℕ) * rv ^ (2:ℕ) * xv + 2 * kp ^ (3:ℕ) * r * w * P
  ^ (4:ℕ) * rv ^ (2:ℕ) * xv))) + ((kp ^ (4:ℕ) * w * c * P ^ (2:ℕ) * e * rv ^ (2:ℕ) * xv + (-kp
  ^ (2:ℕ) * r ^ (2:ℕ) * w * c * P ^ (2:ℕ) * e * rv ^ (2:ℕ) * xv + kp ^ (5:ℕ) * w * P * e * q *
  rv ^ (2:ℕ) * xv)) + ((4 * kp ^ (4:ℕ) * r * w * P * e * q * rv ^ (2:ℕ) * xv + 9 * kp ^ (3:ℕ) *
  r ^ (2:ℕ) * w * P * e * q * rv ^ (2:ℕ) * xv) + (6 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w * P * e * q *
  rv ^ (2:ℕ) * xv - 10 * kp ^ (4:ℕ) * w * P ^ (2:ℕ) * e * q * rv ^ (2:ℕ) * xv)))))) + (((((5 *
  kp ^ (3:ℕ) * r * w * P ^ (2:ℕ) * e * q * rv ^ (2:ℕ) * xv + (-6 * kp ^ (4:ℕ) * w * P ^ (2:ℕ) *
  e * κ * rv ^ (2:ℕ) * xv - 3 * kp ^ (3:ℕ) * r * w * P ^ (2:ℕ) * e * κ * rv ^ (2:ℕ) * xv)) +
  (kp ^ (4:ℕ) * w * P ^ (3:ℕ) * rv ^ (3:ℕ) * xv + (2 * kp ^ (3:ℕ) * r * w * P ^ (3:ℕ) * rv ^
  (3:ℕ) * xv + kp ^ (2:ℕ) * r ^ (2:ℕ) * w * P ^ (3:ℕ) * rv ^ (3:ℕ) * xv))) + ((2 * kp ^ (3:ℕ) *
  w * P ^ (4:ℕ) * rv ^ (3:ℕ) * xv + (4 * kp ^ (3:ℕ) * w * P ^ (2:ℕ) * e * q * rv ^ (3:ℕ) * xv +
  kp ^ (5:ℕ) * r ^ (3:ℕ) * P ^ (2:ℕ) * xv ^ (2:ℕ))) + ((2 * kp ^ (4:ℕ) * r ^ (4:ℕ) * P ^ (2:ℕ)
  * xv ^ (2:ℕ) + kp ^ (3:ℕ) * r ^ (5:ℕ) * P ^ (2:ℕ) * xv ^ (2:ℕ)) + (3 * kp ^ (5:ℕ) * r * w ^
  (2:ℕ) * P ^ (2:ℕ) * xv ^ (2:ℕ) + 8 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * xv ^
  (2:ℕ))))) + (((7 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * xv ^ (2:ℕ) + (2 * kp ^
  (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * xv ^ (2:ℕ) + kp ^ (5:ℕ) * r ^ (2:ℕ) * P ^ (3:ℕ) *
  xv ^ (2:ℕ))) + ((-kp ^ (4:ℕ) * r ^ (3:ℕ) * P ^ (3:ℕ) * xv ^ (2:ℕ) - 3 * kp ^ (3:ℕ) * r ^
  (4:ℕ) * P ^ (3:ℕ) * xv ^ (2:ℕ)) + (-kp ^ (2:ℕ) * r ^ (5:ℕ) * P ^ (3:ℕ) * xv ^ (2:ℕ) - 3 * kp
  ^ (5:ℕ) * w ^ (2:ℕ) * P ^ (3:ℕ) * xv ^ (2:ℕ)))) + ((-7 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P ^
  (3:ℕ) * xv ^ (2:ℕ) + (-5 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (3:ℕ) * xv ^ (2:ℕ) - kp ^
  (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (3:ℕ) * xv ^ (2:ℕ))) + ((kp ^ (5:ℕ) * r * P ^ (4:ℕ) * xv
  ^ (2:ℕ) + 2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P * e * xv ^ (2:ℕ)) + (4 * kp ^ (2:ℕ)
  * r ^ (3:ℕ) * w ^ (2:ℕ) * c * P * e * xv ^ (2:ℕ) + 2 * kp * r ^ (4:ℕ) * w ^ (2:ℕ) * c * P * e
  * xv ^ (2:ℕ)))))) + ((((kp ^ (3:ℕ) * w ^ (4:ℕ) * c * P * e * xv ^ (2:ℕ) + (2 * kp ^ (2:ℕ) * r
  * w ^ (4:ℕ) * c * P * e * xv ^ (2:ℕ) + kp * r ^ (2:ℕ) * w ^ (4:ℕ) * c * P * e * xv ^ (2:ℕ)))
  + ((kp ^ (4:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * e * xv ^ (2:ℕ) + 6 * kp ^ (3:ℕ) * r * w ^ (2:ℕ)
  * c * P ^ (2:ℕ) * e * xv ^ (2:ℕ)) + (5 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) *
  e * xv ^ (2:ℕ) - 7 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * e * q * xv ^ (2:ℕ)))) + ((-12 * kp
  ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * e * q * xv ^ (2:ℕ) + (-5 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^
  (2:ℕ) * e * q * xv ^ (2:ℕ) + 3 * kp ^ (3:ℕ) * r * w ^ (4:ℕ) * e * q * xv ^ (2:ℕ))) + ((4 * kp
  ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * e * q * xv ^ (2:ℕ) + kp * r ^ (3:ℕ) * w ^ (4:ℕ) * e * q *
  xv ^ (2:ℕ)) + (13 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P * e * q * xv ^ (2:ℕ) + 24 * kp ^ (3:ℕ) * r
  ^ (2:ℕ) * w ^ (2:ℕ) * P * e * q * xv ^ (2:ℕ))))) + (((11 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ)
  * P * e * q * xv ^ (2:ℕ) + (-4 * kp ^ (3:ℕ) * w ^ (4:ℕ) * P * e * q * xv ^ (2:ℕ) - 4 * kp ^
  (2:ℕ) * r * w ^ (4:ℕ) * P * e * q * xv ^ (2:ℕ))) + ((-4 * kp ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ)
  * e * q * xv ^ (2:ℕ) + 3 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * e * q * xv ^ (2:ℕ)) + (3
  * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * c * e ^ (2:ℕ) * q * xv ^ (2:ℕ) + kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^
  (2:ℕ) * c * e ^ (2:ℕ) * q * xv ^ (2:ℕ)))) + ((-kp ^ (2:ℕ) * w ^ (4:ℕ) * c * e ^ (2:ℕ) * q *
  xv ^ (2:ℕ) + (kp ^ (3:ℕ) * w ^ (2:ℕ) * c * P * e ^ (2:ℕ) * q * xv ^ (2:ℕ) + 5 * kp ^ (3:ℕ) *
  r * w ^ (2:ℕ) * e ^ (2:ℕ) * q ^ (2:ℕ) * xv ^ (2:ℕ))) + ((6 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P *
  e * κ * xv ^ (2:ℕ) + 8 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * e * κ * xv ^ (2:ℕ)) + (2 *
  kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P * e * κ * xv ^ (2:ℕ) - 5 * kp ^ (4:ℕ) * w ^ (2:ℕ) * P
  ^ (2:ℕ) * e * κ * xv ^ (2:ℕ)))))))) + ((((((-7 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * e *
  κ * xv ^ (2:ℕ) + (-kp ^ (3:ℕ) * w ^ (2:ℕ) * c * P * e ^ (2:ℕ) * κ * xv ^ (2:ℕ) + 3 * kp ^
  (3:ℕ) * r * w ^ (2:ℕ) * e ^ (2:ℕ) * q * κ * xv ^ (2:ℕ))) + (kp ^ (5:ℕ) * r ^ (2:ℕ) * P ^
  (2:ℕ) * rv * xv ^ (2:ℕ) + (2 * kp ^ (4:ℕ) * r ^ (3:ℕ) * P ^ (2:ℕ) * rv * xv ^ (2:ℕ) + kp ^
  (3:ℕ) * r ^ (4:ℕ) * P ^ (2:ℕ) * rv * xv ^ (2:ℕ)))) + ((-kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P ^
  (2:ℕ) * rv * xv ^ (2:ℕ) + (-2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * rv * xv ^
  (2:ℕ) - kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * rv * xv ^ (2:ℕ))) + ((-6 * kp ^
  (4:ℕ) * r ^ (2:ℕ) * P ^ (3:ℕ) * rv * xv ^ (2:ℕ) - 8 * kp ^ (3:ℕ) * r ^ (3:ℕ) * P ^ (3:ℕ) * rv
  * xv ^ (2:ℕ)) + (-2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * P ^ (3:ℕ) * rv * xv ^ (2:ℕ) + 2 * kp ^ (4:ℕ) *
  w ^ (2:ℕ) * P ^ (3:ℕ) * rv * xv ^ (2:ℕ))))) + (((4 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P ^ (3:ℕ) *
  rv * xv ^ (2:ℕ) + (2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (3:ℕ) * rv * xv ^ (2:ℕ) + kp
  ^ (5:ℕ) * P ^ (4:ℕ) * rv * xv ^ (2:ℕ))) + ((-2 * kp ^ (4:ℕ) * r * P ^ (4:ℕ) * rv * xv ^ (2:ℕ)
  + 4 * kp ^ (3:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * e * rv * xv ^ (2:ℕ)) + (4 * kp ^ (2:ℕ) * r * w
  ^ (2:ℕ) * c * P ^ (2:ℕ) * e * rv * xv ^ (2:ℕ) - 5 * kp ^ (4:ℕ) * w ^ (2:ℕ) * P * e * q * rv *
  xv ^ (2:ℕ)))) + ((-9 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P * e * q * rv * xv ^ (2:ℕ) + (-4 * kp ^
  (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * e * q * rv * xv ^ (2:ℕ) + 7 * kp ^ (3:ℕ) * w ^ (2:ℕ) * P
  ^ (2:ℕ) * e * q * rv * xv ^ (2:ℕ))) + ((2 * kp ^ (3:ℕ) * w ^ (2:ℕ) * e ^ (2:ℕ) * q ^ (2:ℕ) *
  rv * xv ^ (2:ℕ) - 2 * kp ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * e * κ * rv * xv ^ (2:ℕ)) + (-kp ^
  (5:ℕ) * P ^ (3:ℕ) * rv ^ (2:ℕ) * xv ^ (2:ℕ) - 5 * kp ^ (4:ℕ) * r * P ^ (3:ℕ) * rv ^ (2:ℕ) *
  xv ^ (2:ℕ)))))) + ((((-5 * kp ^ (3:ℕ) * r ^ (2:ℕ) * P ^ (3:ℕ) * rv ^ (2:ℕ) * xv ^ (2:ℕ) +
  (-kp ^ (2:ℕ) * r ^ (3:ℕ) * P ^ (3:ℕ) * rv ^ (2:ℕ) * xv ^ (2:ℕ) - 2 * kp ^ (4:ℕ) * P ^ (4:ℕ) *
  rv ^ (2:ℕ) * xv ^ (2:ℕ))) + (kp ^ (3:ℕ) * r * P ^ (4:ℕ) * rv ^ (2:ℕ) * xv ^ (2:ℕ) + (kp ^
  (3:ℕ) * P ^ (4:ℕ) * rv ^ (3:ℕ) * xv ^ (2:ℕ) + kp ^ (5:ℕ) * r * w * P ^ (2:ℕ) * xv ^ (3:ℕ))))
  + ((3 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w * P ^ (2:ℕ) * xv ^ (3:ℕ) + (3 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w
  * P ^ (2:ℕ) * xv ^ (3:ℕ) + kp ^ (2:ℕ) * r ^ (4:ℕ) * w * P ^ (2:ℕ) * xv ^ (3:ℕ))) + ((-3 * kp
  ^ (5:ℕ) * w * P ^ (3:ℕ) * xv ^ (3:ℕ) - 8 * kp ^ (4:ℕ) * r * w * P ^ (3:ℕ) * xv ^ (3:ℕ)) + (-7
  * kp ^ (3:ℕ) * r ^ (2:ℕ) * w * P ^ (3:ℕ) * xv ^ (3:ℕ) - 2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w * P ^
  (3:ℕ) * xv ^ (3:ℕ))))) + (((kp ^ (4:ℕ) * w * c * P ^ (2:ℕ) * e * xv ^ (3:ℕ) + (2 * kp ^ (3:ℕ)
  * r * w * c * P ^ (2:ℕ) * e * xv ^ (3:ℕ) + kp ^ (2:ℕ) * r ^ (2:ℕ) * w * c * P ^ (2:ℕ) * e *
  xv ^ (3:ℕ))) + ((7 * kp ^ (4:ℕ) * r * w * P * e * q * xv ^ (3:ℕ) + 13 * kp ^ (3:ℕ) * r ^
  (2:ℕ) * w * P * e * q * xv ^ (3:ℕ)) + (6 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w * P * e * q * xv ^
  (3:ℕ) - 2 * kp ^ (3:ℕ) * w ^ (3:ℕ) * P * e * q * xv ^ (3:ℕ)))) + ((-2 * kp ^ (2:ℕ) * r * w ^
  (3:ℕ) * P * e * q * xv ^ (3:ℕ) + (-2 * kp ^ (4:ℕ) * w * P ^ (2:ℕ) * e * q * xv ^ (3:ℕ) + kp ^
  (3:ℕ) * r * w * P ^ (2:ℕ) * e * q * xv ^ (3:ℕ))) + ((-3 * kp ^ (4:ℕ) * w * P ^ (2:ℕ) * e * κ
  * xv ^ (3:ℕ) - 3 * kp ^ (3:ℕ) * r * w * P ^ (2:ℕ) * e * κ * xv ^ (3:ℕ)) + (kp ^ (4:ℕ) * w * P
  ^ (3:ℕ) * rv * xv ^ (3:ℕ) + 2 * kp ^ (3:ℕ) * r * w * P ^ (3:ℕ) * rv * xv ^ (3:ℕ))))))) +
  (((((kp ^ (2:ℕ) * r ^ (2:ℕ) * w * P ^ (3:ℕ) * rv * xv ^ (3:ℕ) + (3 * kp ^ (3:ℕ) * w * P ^
  (2:ℕ) * e * q * rv * xv ^ (3:ℕ) - kp ^ (5:ℕ) * P ^ (3:ℕ) * xv ^ (4:ℕ))) + (-3 * kp ^ (4:ℕ) *
  r * P ^ (3:ℕ) * xv ^ (4:ℕ) + (-3 * kp ^ (3:ℕ) * r ^ (2:ℕ) * P ^ (3:ℕ) * xv ^ (4:ℕ) - kp ^
  (2:ℕ) * r ^ (3:ℕ) * P ^ (3:ℕ) * xv ^ (4:ℕ)))) + ((2 * kp ^ (4:ℕ) * r ^ (4:ℕ) * c * P ^ (2:ℕ)
  + (4 * kp ^ (3:ℕ) * r ^ (5:ℕ) * c * P ^ (2:ℕ) + 2 * kp ^ (2:ℕ) * r ^ (6:ℕ) * c * P ^ (2:ℕ)))
  + ((3 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) + 6 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^
  (2:ℕ) * c * P ^ (2:ℕ)) + (3 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) + kp ^ (4:ℕ)
  * w ^ (4:ℕ) * c * P ^ (2:ℕ))))) + (((2 * kp ^ (3:ℕ) * r * w ^ (4:ℕ) * c * P ^ (2:ℕ) + (kp ^
  (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * c * P ^ (2:ℕ) + 2 * kp ^ (4:ℕ) * r ^ (3:ℕ) * c * P ^ (3:ℕ)))
  + ((2 * kp ^ (3:ℕ) * r ^ (4:ℕ) * c * P ^ (3:ℕ) + 2 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * c * P ^
  (3:ℕ)) + (2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P ^ (3:ℕ) - kp ^ (3:ℕ) * r ^ (2:ℕ) * w
  ^ (2:ℕ) * c ^ (2:ℕ) * P * e))) + ((-2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * P *
  e + (-kp * r ^ (4:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * P * e - kp ^ (3:ℕ) * w ^ (4:ℕ) * c ^ (2:ℕ) * P
  * e)) + ((-2 * kp ^ (2:ℕ) * r * w ^ (4:ℕ) * c ^ (2:ℕ) * P * e - kp * r ^ (2:ℕ) * w ^ (4:ℕ) *
  c ^ (2:ℕ) * P * e) + (-kp ^ (3:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * q - 2 * kp ^ (2:ℕ) * r ^ (6:ℕ) *
  w ^ (2:ℕ) * q))))) + ((((-kp * r ^ (7:ℕ) * w ^ (2:ℕ) * q + (-2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^
  (4:ℕ) * q - 4 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (4:ℕ) * q)) + ((-2 * kp * r ^ (5:ℕ) * w ^ (4:ℕ)
  * q - kp ^ (3:ℕ) * r * w ^ (6:ℕ) * q) + (-2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (6:ℕ) * q - kp * r
  ^ (3:ℕ) * w ^ (6:ℕ) * q))) + ((-2 * kp ^ (4:ℕ) * r ^ (5:ℕ) * P * q + (-4 * kp ^ (3:ℕ) * r ^
  (6:ℕ) * P * q - 2 * kp ^ (2:ℕ) * r ^ (7:ℕ) * P * q)) + ((-4 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^
  (2:ℕ) * P * q - 10 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * P * q) + (-6 * kp ^ (2:ℕ) * r ^
  (5:ℕ) * w ^ (2:ℕ) * P * q - 2 * kp ^ (4:ℕ) * r * w ^ (4:ℕ) * P * q)))) + (((-6 * kp ^ (3:ℕ) *
  r ^ (2:ℕ) * w ^ (4:ℕ) * P * q + (-4 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * P * q + 2 * kp ^
  (5:ℕ) * r ^ (3:ℕ) * P ^ (2:ℕ) * q)) + ((-2 * kp ^ (4:ℕ) * r ^ (4:ℕ) * P ^ (2:ℕ) * q - 4 * kp
  ^ (3:ℕ) * r ^ (5:ℕ) * P ^ (2:ℕ) * q) + (-2 * kp ^ (5:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * q - 6 *
  kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * q))) + ((-5 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^
  (2:ℕ) * P ^ (2:ℕ) * q + (-kp ^ (3:ℕ) * r * w ^ (4:ℕ) * P ^ (2:ℕ) * q + 2 * kp ^ (5:ℕ) * r ^
  (2:ℕ) * P ^ (3:ℕ) * q)) + ((-2 * kp ^ (4:ℕ) * r ^ (3:ℕ) * P ^ (3:ℕ) * q - 2 * kp ^ (4:ℕ) * r
  * w ^ (2:ℕ) * P ^ (3:ℕ) * q) + (-2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * c * e * q - 4 * kp
  ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * c * e * q)))))))) + (((((((-2 * kp * r ^ (5:ℕ) * w ^ (2:ℕ)
  * c * e * q + (-4 * kp ^ (3:ℕ) * r * w ^ (4:ℕ) * c * e * q - 4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^
  (4:ℕ) * c * e * q)) + (2 * kp ^ (2:ℕ) * w ^ (6:ℕ) * c * e * q + (2 * kp * r * w ^ (6:ℕ) * c *
  e * q + 3 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * c * P * e * q))) + ((10 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w
  ^ (2:ℕ) * c * P * e * q + (7 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * c * P * e * q + kp ^
  (3:ℕ) * w ^ (4:ℕ) * c * P * e * q)) + ((kp ^ (2:ℕ) * r * w ^ (4:ℕ) * c * P * e * q + kp ^
  (2:ℕ) * w ^ (4:ℕ) * c ^ (2:ℕ) * e ^ (2:ℕ) * q) + (-6 * kp ^ (3:ℕ) * r * w ^ (4:ℕ) * e * q ^
  (2:ℕ) - 4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * e * q ^ (2:ℕ))))) + (((-3 * kp ^ (4:ℕ) * r *
  w ^ (2:ℕ) * P * e * q ^ (2:ℕ) + (2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * e * q ^ (2:ℕ) -
  kp ^ (3:ℕ) * r * w ^ (2:ℕ) * c * e ^ (2:ℕ) * q ^ (2:ℕ))) + ((2 * kp ^ (5:ℕ) * r ^ (4:ℕ) * P *
  κ + 4 * kp ^ (4:ℕ) * r ^ (5:ℕ) * P * κ) + (2 * kp ^ (3:ℕ) * r ^ (6:ℕ) * P * κ + 2 * kp ^
  (5:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * κ))) + ((3 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P * κ +
  (-kp ^ (2:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * P * κ - kp ^ (4:ℕ) * r * w ^ (4:ℕ) * P * κ)) + ((-2 *
  kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * P * κ - kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * P * κ) + (4
  * kp ^ (5:ℕ) * r ^ (3:ℕ) * P ^ (2:ℕ) * κ + 2 * kp ^ (4:ℕ) * r ^ (4:ℕ) * P ^ (2:ℕ) * κ))))) +
  ((((-2 * kp ^ (3:ℕ) * r ^ (5:ℕ) * P ^ (2:ℕ) * κ + (2 * kp ^ (5:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ)
  * κ - 2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * κ)) + (2 * kp ^ (5:ℕ) * r ^ (2:ℕ)
  * P ^ (3:ℕ) * κ + (-2 * kp ^ (4:ℕ) * r ^ (3:ℕ) * P ^ (3:ℕ) * κ + kp ^ (5:ℕ) * w ^ (2:ℕ) * P ^
  (3:ℕ) * κ))) + ((-2 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P ^ (3:ℕ) * κ + (-kp ^ (4:ℕ) * r ^ (2:ℕ) *
  w ^ (2:ℕ) * c * e * κ - kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * c * e * κ)) + ((kp ^ (2:ℕ) * r ^
  (4:ℕ) * w ^ (2:ℕ) * c * e * κ + kp * r ^ (5:ℕ) * w ^ (2:ℕ) * c * e * κ) + (kp ^ (3:ℕ) * r * w
  ^ (4:ℕ) * c * e * κ + 2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * c * e * κ)))) + (((kp * r ^
  (3:ℕ) * w ^ (4:ℕ) * c * e * κ + (-kp ^ (4:ℕ) * r * w ^ (2:ℕ) * c * P * e * κ + 6 * kp ^ (3:ℕ)
  * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P * e * κ)) + ((7 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * c * P
  * e * κ + 4 * kp ^ (3:ℕ) * w ^ (4:ℕ) * c * P * e * κ) + (4 * kp ^ (2:ℕ) * r * w ^ (4:ℕ) * c *
  P * e * κ + 9 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * e * q * κ))) + ((14 * kp ^ (3:ℕ) * r ^
  (3:ℕ) * w ^ (2:ℕ) * e * q * κ + (5 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * e * q * κ + kp ^
  (3:ℕ) * r * w ^ (4:ℕ) * e * q * κ)) + ((kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * e * q * κ - 2 *
  kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P * e * q * κ) + (kp ^ (3:ℕ) * w ^ (4:ℕ) * P * e * q * κ - 2 *
  kp ^ (3:ℕ) * r * w ^ (2:ℕ) * c * e ^ (2:ℕ) * q * κ)))))) + (((((5 * kp ^ (4:ℕ) * r ^ (2:ℕ) *
  w ^ (2:ℕ) * e * κ ^ (2:ℕ) + (6 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * e * κ ^ (2:ℕ) + kp ^
  (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * e * κ ^ (2:ℕ))) + (kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P * e * κ ^
  (2:ℕ) + (-2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * e * κ ^ (2:ℕ) - kp ^ (3:ℕ) * w ^ (4:ℕ)
  * P * e * κ ^ (2:ℕ)))) + ((-kp ^ (3:ℕ) * r * w ^ (2:ℕ) * c * e ^ (2:ℕ) * κ ^ (2:ℕ) + (6 * kp
  ^ (4:ℕ) * r ^ (3:ℕ) * c * P ^ (2:ℕ) * rv + 12 * kp ^ (3:ℕ) * r ^ (4:ℕ) * c * P ^ (2:ℕ) * rv))
  + ((6 * kp ^ (2:ℕ) * r ^ (5:ℕ) * c * P ^ (2:ℕ) * rv + 4 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * c * P
  ^ (2:ℕ) * rv) + (7 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * rv + 2 * kp ^ (2:ℕ)
  * r ^ (3:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * rv)))) + (((-kp * r ^ (4:ℕ) * w ^ (2:ℕ) * c * P ^
  (2:ℕ) * rv + (-kp ^ (3:ℕ) * w ^ (4:ℕ) * c * P ^ (2:ℕ) * rv - 2 * kp ^ (2:ℕ) * r * w ^ (4:ℕ) *
  c * P ^ (2:ℕ) * rv)) + ((-kp * r ^ (2:ℕ) * w ^ (4:ℕ) * c * P ^ (2:ℕ) * rv + 6 * kp ^ (4:ℕ) *
  r ^ (2:ℕ) * c * P ^ (3:ℕ) * rv) + (4 * kp ^ (3:ℕ) * r ^ (3:ℕ) * c * P ^ (3:ℕ) * rv - 2 * kp ^
  (2:ℕ) * r ^ (4:ℕ) * c * P ^ (3:ℕ) * rv))) + ((2 * kp ^ (4:ℕ) * w ^ (2:ℕ) * c * P ^ (3:ℕ) * rv
  + (-2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P ^ (3:ℕ) * rv - 3 * kp ^ (3:ℕ) * r * w ^
  (2:ℕ) * c ^ (2:ℕ) * P * e * rv)) + ((-6 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * P
  * e * rv - 3 * kp * r ^ (3:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * P * e * rv) + (-2 * kp ^ (4:ℕ) * r ^
  (3:ℕ) * w ^ (2:ℕ) * q * rv - 6 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * q * rv))))) + ((((-6 *
  kp ^ (2:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * q * rv + (-2 * kp * r ^ (6:ℕ) * w ^ (2:ℕ) * q * rv - 2 *
  kp ^ (4:ℕ) * r * w ^ (4:ℕ) * q * rv)) + ((-6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * q * rv -
  6 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * q * rv) + (-2 * kp * r ^ (4:ℕ) * w ^ (4:ℕ) * q * rv
  - 2 * kp ^ (5:ℕ) * r ^ (3:ℕ) * P * q * rv))) + ((-10 * kp ^ (4:ℕ) * r ^ (4:ℕ) * P * q * rv +
  (-14 * kp ^ (3:ℕ) * r ^ (5:ℕ) * P * q * rv - 6 * kp ^ (2:ℕ) * r ^ (6:ℕ) * P * q * rv)) + ((2
  * kp ^ (5:ℕ) * r * w ^ (2:ℕ) * P * q * rv - 8 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * q *
  rv) + (-24 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P * q * rv - 14 * kp ^ (2:ℕ) * r ^ (4:ℕ) *
  w ^ (2:ℕ) * P * q * rv)))) + (((-2 * kp ^ (3:ℕ) * r * w ^ (4:ℕ) * P * q * rv + (-2 * kp ^
  (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * P * q * rv + 2 * kp ^ (5:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ) * q *
  rv)) + ((-12 * kp ^ (4:ℕ) * r ^ (3:ℕ) * P ^ (2:ℕ) * q * rv - 12 * kp ^ (3:ℕ) * r ^ (4:ℕ) * P
  ^ (2:ℕ) * q * rv) + (2 * kp ^ (2:ℕ) * r ^ (5:ℕ) * P ^ (2:ℕ) * q * rv - kp ^ (5:ℕ) * w ^ (2:ℕ)
  * P ^ (2:ℕ) * q * rv))) + ((-5 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * q * rv + (-3 * kp ^
  (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * q * rv + 3 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) *
  P ^ (2:ℕ) * q * rv)) + ((-kp ^ (3:ℕ) * w ^ (4:ℕ) * P ^ (2:ℕ) * q * rv + kp ^ (2:ℕ) * r * w ^
  (4:ℕ) * P ^ (2:ℕ) * q * rv) + (4 * kp ^ (5:ℕ) * r * P ^ (3:ℕ) * q * rv - 10 * kp ^ (4:ℕ) * r
  ^ (2:ℕ) * P ^ (3:ℕ) * q * rv))))))) + ((((((2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * P ^ (3:ℕ) * q * rv +
  (-2 * kp ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (3:ℕ) * q * rv + 2 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P ^
  (3:ℕ) * q * rv)) + (-2 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * c * e * q * rv + (-6 * kp ^ (3:ℕ) * r ^
  (2:ℕ) * w ^ (2:ℕ) * c * e * q * rv - 6 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * c * e * q *
  rv))) + ((-2 * kp * r ^ (4:ℕ) * w ^ (2:ℕ) * c * e * q * rv + (6 * kp ^ (3:ℕ) * w ^ (4:ℕ) * c
  * e * q * rv + 12 * kp ^ (2:ℕ) * r * w ^ (4:ℕ) * c * e * q * rv)) + ((6 * kp * r ^ (2:ℕ) * w
  ^ (4:ℕ) * c * e * q * rv + kp ^ (4:ℕ) * w ^ (2:ℕ) * c * P * e * q * rv) + (14 * kp ^ (3:ℕ) *
  r * w ^ (2:ℕ) * c * P * e * q * rv + 13 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P * e * q
  * rv)))) + (((-4 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * e * q ^ (2:ℕ) * rv + (-10 * kp ^ (3:ℕ) * r ^
  (2:ℕ) * w ^ (2:ℕ) * e * q ^ (2:ℕ) * rv - 6 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * e * q ^
  (2:ℕ) * rv)) + ((-2 * kp ^ (3:ℕ) * w ^ (4:ℕ) * e * q ^ (2:ℕ) * rv - 2 * kp ^ (2:ℕ) * r * w ^
  (4:ℕ) * e * q ^ (2:ℕ) * rv) + (-kp ^ (4:ℕ) * w ^ (2:ℕ) * P * e * q ^ (2:ℕ) * rv + 6 * kp ^
  (3:ℕ) * r * w ^ (2:ℕ) * P * e * q ^ (2:ℕ) * rv))) + ((-kp ^ (3:ℕ) * w ^ (2:ℕ) * c * e ^ (2:ℕ)
  * q ^ (2:ℕ) * rv + (4 * kp ^ (5:ℕ) * r ^ (3:ℕ) * P * κ * rv + 8 * kp ^ (4:ℕ) * r ^ (4:ℕ) * P
  * κ * rv)) + ((4 * kp ^ (3:ℕ) * r ^ (5:ℕ) * P * κ * rv + kp ^ (5:ℕ) * r * w ^ (2:ℕ) * P * κ *
  rv) + (-kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * κ * rv - 5 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^
  (2:ℕ) * P * κ * rv))))) + ((((-3 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * P * κ * rv + (8 * kp
  ^ (5:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ) * κ * rv - 2 * kp ^ (4:ℕ) * r ^ (3:ℕ) * P ^ (2:ℕ) * κ * rv))
  + (-10 * kp ^ (3:ℕ) * r ^ (4:ℕ) * P ^ (2:ℕ) * κ * rv + (-4 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P ^
  (2:ℕ) * κ * rv - 4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * κ * rv))) + ((4 * kp ^
  (5:ℕ) * r * P ^ (3:ℕ) * κ * rv + (-10 * kp ^ (4:ℕ) * r ^ (2:ℕ) * P ^ (3:ℕ) * κ * rv + 2 * kp
  ^ (3:ℕ) * r ^ (3:ℕ) * P ^ (3:ℕ) * κ * rv)) + ((-4 * kp ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (3:ℕ) * κ *
  rv + 2 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P ^ (3:ℕ) * κ * rv) + (-3 * kp ^ (4:ℕ) * r * w ^ (2:ℕ)
  * c * e * κ * rv - 5 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * e * κ * rv)))) + (((-kp ^
  (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * c * e * κ * rv + (kp * r ^ (4:ℕ) * w ^ (2:ℕ) * c * e * κ * rv
  + 2 * kp ^ (3:ℕ) * w ^ (4:ℕ) * c * e * κ * rv)) + ((4 * kp ^ (2:ℕ) * r * w ^ (4:ℕ) * c * e *
  κ * rv + 2 * kp * r ^ (2:ℕ) * w ^ (4:ℕ) * c * e * κ * rv) + (-3 * kp ^ (4:ℕ) * w ^ (2:ℕ) * c
  * P * e * κ * rv + 14 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * c * P * e * κ * rv))) + ((17 * kp ^
  (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P * e * κ * rv + (11 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * e * q
  * κ * rv + 14 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * e * q * κ * rv)) + ((3 * kp ^ (2:ℕ) * r
  ^ (3:ℕ) * w ^ (2:ℕ) * e * q * κ * rv + 2 * kp ^ (4:ℕ) * w ^ (2:ℕ) * P * e * q * κ * rv) + (-2
  * kp ^ (3:ℕ) * w ^ (2:ℕ) * c * e ^ (2:ℕ) * q * κ * rv + 7 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * e *
  κ ^ (2:ℕ) * rv)))))) + (((((8 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * e * κ ^ (2:ℕ) * rv + (kp
  ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * e * κ ^ (2:ℕ) * rv + 3 * kp ^ (4:ℕ) * w ^ (2:ℕ) * P * e * κ
  ^ (2:ℕ) * rv)) + (-6 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P * e * κ ^ (2:ℕ) * rv + (-kp ^ (3:ℕ) * w
  ^ (2:ℕ) * c * e ^ (2:ℕ) * κ ^ (2:ℕ) * rv + 6 * kp ^ (4:ℕ) * r ^ (2:ℕ) * c * P ^ (2:ℕ) * rv ^
  (2:ℕ)))) + ((12 * kp ^ (3:ℕ) * r ^ (3:ℕ) * c * P ^ (2:ℕ) * rv ^ (2:ℕ) + (6 * kp ^ (2:ℕ) * r ^
  (4:ℕ) * c * P ^ (2:ℕ) * rv ^ (2:ℕ) + kp ^ (4:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * rv ^ (2:ℕ))) +
  ((-3 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * rv ^ (2:ℕ) - 2 * kp * r ^ (3:ℕ) *
  w ^ (2:ℕ) * c * P ^ (2:ℕ) * rv ^ (2:ℕ)) + (6 * kp ^ (4:ℕ) * r * c * P ^ (3:ℕ) * rv ^ (2:ℕ) -
  6 * kp ^ (2:ℕ) * r ^ (3:ℕ) * c * P ^ (3:ℕ) * rv ^ (2:ℕ))))) + (((-2 * kp ^ (3:ℕ) * w ^ (2:ℕ)
  * c * P ^ (3:ℕ) * rv ^ (2:ℕ) + (-2 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * c * P ^ (3:ℕ) * rv ^ (2:ℕ)
  - 2 * kp ^ (3:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * P * e * rv ^ (2:ℕ))) + ((-4 * kp ^ (2:ℕ) * r * w ^
  (2:ℕ) * c ^ (2:ℕ) * P * e * rv ^ (2:ℕ) - 2 * kp * r ^ (2:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * P * e *
  rv ^ (2:ℕ)) + (-kp ^ (5:ℕ) * r * w ^ (2:ℕ) * q * rv ^ (2:ℕ) - 4 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w
  ^ (2:ℕ) * q * rv ^ (2:ℕ)))) + ((-6 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * q * rv ^ (2:ℕ) +
  (-4 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * q * rv ^ (2:ℕ) - kp * r ^ (5:ℕ) * w ^ (2:ℕ) * q *
  rv ^ (2:ℕ))) + ((-4 * kp ^ (5:ℕ) * r ^ (2:ℕ) * P * q * rv ^ (2:ℕ) - 14 * kp ^ (4:ℕ) * r ^
  (3:ℕ) * P * q * rv ^ (2:ℕ)) + (-16 * kp ^ (3:ℕ) * r ^ (4:ℕ) * P * q * rv ^ (2:ℕ) - 6 * kp ^
  (2:ℕ) * r ^ (5:ℕ) * P * q * rv ^ (2:ℕ)))))) + ((((-8 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P * q *
  rv ^ (2:ℕ) + (-16 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * q * rv ^ (2:ℕ) - 8 * kp ^ (2:ℕ)
  * r ^ (3:ℕ) * w ^ (2:ℕ) * P * q * rv ^ (2:ℕ))) + ((-2 * kp ^ (5:ℕ) * r * P ^ (2:ℕ) * q * rv ^
  (2:ℕ) - 16 * kp ^ (4:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ) * q * rv ^ (2:ℕ)) + (-8 * kp ^ (3:ℕ) * r ^
  (3:ℕ) * P ^ (2:ℕ) * q * rv ^ (2:ℕ) + 6 * kp ^ (2:ℕ) * r ^ (4:ℕ) * P ^ (2:ℕ) * q * rv ^
  (2:ℕ)))) + ((-kp ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * q * rv ^ (2:ℕ) + (3 * kp ^ (3:ℕ) * r * w ^
  (2:ℕ) * P ^ (2:ℕ) * q * rv ^ (2:ℕ) + 5 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * q *
  rv ^ (2:ℕ))) + ((kp ^ (2:ℕ) * w ^ (4:ℕ) * P ^ (2:ℕ) * q * rv ^ (2:ℕ) + 2 * kp ^ (5:ℕ) * P ^
  (3:ℕ) * q * rv ^ (2:ℕ)) + (-14 * kp ^ (4:ℕ) * r * P ^ (3:ℕ) * q * rv ^ (2:ℕ) + 8 * kp ^ (3:ℕ)
  * r ^ (2:ℕ) * P ^ (3:ℕ) * q * rv ^ (2:ℕ))))) + (((2 * kp ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (3:ℕ) * q
  * rv ^ (2:ℕ) + (8 * kp ^ (3:ℕ) * w ^ (2:ℕ) * c * P * e * q * rv ^ (2:ℕ) + 8 * kp ^ (2:ℕ) * r
  * w ^ (2:ℕ) * c * P * e * q * rv ^ (2:ℕ))) + ((-6 * kp ^ (4:ℕ) * w ^ (2:ℕ) * e * q ^ (2:ℕ) *
  rv ^ (2:ℕ) - 12 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * e * q ^ (2:ℕ) * rv ^ (2:ℕ)) + (-6 * kp ^ (2:ℕ)
  * r ^ (2:ℕ) * w ^ (2:ℕ) * e * q ^ (2:ℕ) * rv ^ (2:ℕ) + 2 * kp ^ (3:ℕ) * w ^ (2:ℕ) * P * e * q
  ^ (2:ℕ) * rv ^ (2:ℕ)))) + ((2 * kp ^ (5:ℕ) * r ^ (2:ℕ) * P * κ * rv ^ (2:ℕ) + (4 * kp ^ (4:ℕ)
  * r ^ (3:ℕ) * P * κ * rv ^ (2:ℕ) + 2 * kp ^ (3:ℕ) * r ^ (4:ℕ) * P * κ * rv ^ (2:ℕ))) + ((-2 *
  kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P * κ * rv ^ (2:ℕ) - 4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P
  * κ * rv ^ (2:ℕ)) + (-2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P * κ * rv ^ (2:ℕ) + 4 * kp ^
  (5:ℕ) * r * P ^ (2:ℕ) * κ * rv ^ (2:ℕ)))))))))) + ((((((((-10 * kp ^ (4:ℕ) * r ^ (2:ℕ) * P ^
  (2:ℕ) * κ * rv ^ (2:ℕ) + (-14 * kp ^ (3:ℕ) * r ^ (3:ℕ) * P ^ (2:ℕ) * κ * rv ^ (2:ℕ) + 2 * kp
  ^ (5:ℕ) * P ^ (3:ℕ) * κ * rv ^ (2:ℕ))) + (-14 * kp ^ (4:ℕ) * r * P ^ (3:ℕ) * κ * rv ^ (2:ℕ) +
  (8 * kp ^ (3:ℕ) * r ^ (2:ℕ) * P ^ (3:ℕ) * κ * rv ^ (2:ℕ) + 3 * kp ^ (3:ℕ) * w ^ (2:ℕ) * P ^
  (3:ℕ) * κ * rv ^ (2:ℕ)))) + ((12 * kp ^ (3:ℕ) * w ^ (2:ℕ) * c * P * e * κ * rv ^ (2:ℕ) + (12
  * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * c * P * e * κ * rv ^ (2:ℕ) - 2 * kp ^ (4:ℕ) * w ^ (2:ℕ) * e *
  q * κ * rv ^ (2:ℕ))) + ((-4 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * e * q * κ * rv ^ (2:ℕ) - 2 * kp ^
  (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * e * q * κ * rv ^ (2:ℕ)) + (-4 * kp ^ (3:ℕ) * w ^ (2:ℕ) * P *
  e * q * κ * rv ^ (2:ℕ) - 6 * kp ^ (3:ℕ) * w ^ (2:ℕ) * P * e * κ ^ (2:ℕ) * rv ^ (2:ℕ))))) +
  (((2 * kp ^ (4:ℕ) * r * c * P ^ (2:ℕ) * rv ^ (3:ℕ) + (4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * c * P ^
  (2:ℕ) * rv ^ (3:ℕ) + 2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * c * P ^ (2:ℕ) * rv ^ (3:ℕ))) + ((-kp ^
  (3:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * rv ^ (3:ℕ) - 2 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * c * P ^
  (2:ℕ) * rv ^ (3:ℕ)) + (-kp * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * rv ^ (3:ℕ) + 2 * kp ^
  (4:ℕ) * c * P ^ (3:ℕ) * rv ^ (3:ℕ)))) + ((-4 * kp ^ (3:ℕ) * r * c * P ^ (3:ℕ) * rv ^ (3:ℕ) +
  (-6 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c * P ^ (3:ℕ) * rv ^ (3:ℕ) - 2 * kp ^ (5:ℕ) * r * P * q * rv ^
  (3:ℕ))) + ((-6 * kp ^ (4:ℕ) * r ^ (2:ℕ) * P * q * rv ^ (3:ℕ) - 6 * kp ^ (3:ℕ) * r ^ (3:ℕ) * P
  * q * rv ^ (3:ℕ)) + (-2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * P * q * rv ^ (3:ℕ) - 2 * kp ^ (5:ℕ) * P ^
  (2:ℕ) * q * rv ^ (3:ℕ)))))) + ((((-4 * kp ^ (4:ℕ) * r * P ^ (2:ℕ) * q * rv ^ (3:ℕ) + (4 * kp
  ^ (3:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ) * q * rv ^ (3:ℕ) + 6 * kp ^ (2:ℕ) * r ^ (3:ℕ) * P ^ (2:ℕ) * q
  * rv ^ (3:ℕ))) + (2 * kp ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * q * rv ^ (3:ℕ) + (2 * kp ^ (2:ℕ) *
  r * w ^ (2:ℕ) * P ^ (2:ℕ) * q * rv ^ (3:ℕ) - 6 * kp ^ (4:ℕ) * P ^ (3:ℕ) * q * rv ^ (3:ℕ)))) +
  ((10 * kp ^ (3:ℕ) * r * P ^ (3:ℕ) * q * rv ^ (3:ℕ) + (-6 * kp ^ (4:ℕ) * r * P ^ (2:ℕ) * κ *
  rv ^ (3:ℕ) - 6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ) * κ * rv ^ (3:ℕ))) + ((-6 * kp ^ (4:ℕ) *
  P ^ (3:ℕ) * κ * rv ^ (3:ℕ) + 10 * kp ^ (3:ℕ) * r * P ^ (3:ℕ) * κ * rv ^ (3:ℕ)) + (-2 * kp ^
  (3:ℕ) * c * P ^ (3:ℕ) * rv ^ (4:ℕ) - 2 * kp ^ (2:ℕ) * r * c * P ^ (3:ℕ) * rv ^ (4:ℕ))))) +
  (((2 * kp ^ (4:ℕ) * P ^ (2:ℕ) * q * rv ^ (4:ℕ) + (4 * kp ^ (3:ℕ) * r * P ^ (2:ℕ) * q * rv ^
  (4:ℕ) + 2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ) * q * rv ^ (4:ℕ))) + ((4 * kp ^ (3:ℕ) * P ^
  (3:ℕ) * q * rv ^ (4:ℕ) + 4 * kp ^ (3:ℕ) * P ^ (3:ℕ) * κ * rv ^ (4:ℕ)) + (5 * kp ^ (4:ℕ) * r ^
  (2:ℕ) * w * c * P ^ (2:ℕ) * xv + 11 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w * c * P ^ (2:ℕ) * xv))) +
  ((7 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w * c * P ^ (2:ℕ) * xv + (kp * r ^ (5:ℕ) * w * c * P ^ (2:ℕ) *
  xv + 3 * kp ^ (4:ℕ) * w ^ (3:ℕ) * c * P ^ (2:ℕ) * xv)) + ((7 * kp ^ (3:ℕ) * r * w ^ (3:ℕ) * c
  * P ^ (2:ℕ) * xv + 5 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * c * P ^ (2:ℕ) * xv) + (kp * r ^
  (3:ℕ) * w ^ (3:ℕ) * c * P ^ (2:ℕ) * xv + 4 * kp ^ (4:ℕ) * r * w * c * P ^ (3:ℕ) * xv)))))) +
  (((((4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w * c * P ^ (3:ℕ) * xv + (kp ^ (3:ℕ) * r ^ (2:ℕ) * w * c ^
  (2:ℕ) * P * e * xv + 2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w * c ^ (2:ℕ) * P * e * xv)) + (kp * r ^
  (4:ℕ) * w * c ^ (2:ℕ) * P * e * xv + (-2 * kp ^ (3:ℕ) * w ^ (3:ℕ) * c ^ (2:ℕ) * P * e * xv -
  4 * kp ^ (2:ℕ) * r * w ^ (3:ℕ) * c ^ (2:ℕ) * P * e * xv))) + ((-2 * kp * r ^ (2:ℕ) * w ^
  (3:ℕ) * c ^ (2:ℕ) * P * e * xv + (2 * kp ^ (4:ℕ) * r ^ (4:ℕ) * w * q * xv + 4 * kp ^ (3:ℕ) *
  r ^ (5:ℕ) * w * q * xv)) + ((2 * kp ^ (2:ℕ) * r ^ (6:ℕ) * w * q * xv + 2 * kp ^ (4:ℕ) * r ^
  (2:ℕ) * w ^ (3:ℕ) * q * xv) + (2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (3:ℕ) * q * xv - 2 * kp ^
  (2:ℕ) * r ^ (4:ℕ) * w ^ (3:ℕ) * q * xv)))) + (((-2 * kp * r ^ (5:ℕ) * w ^ (3:ℕ) * q * xv +
  (-2 * kp ^ (3:ℕ) * r * w ^ (5:ℕ) * q * xv - 4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (5:ℕ) * q * xv))
  + ((-2 * kp * r ^ (3:ℕ) * w ^ (5:ℕ) * q * xv - 4 * kp ^ (5:ℕ) * r ^ (2:ℕ) * w * P * q * xv) +
  (-9 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w * P * q * xv - 9 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w * P * q *
  xv))) + ((-3 * kp ^ (2:ℕ) * r ^ (5:ℕ) * w * P * q * xv + (kp * r ^ (6:ℕ) * w * P * q * xv - 7
  * kp ^ (4:ℕ) * r * w ^ (3:ℕ) * P * q * xv)) + ((-16 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * P
  * q * xv - 7 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (3:ℕ) * P * q * xv) + (2 * kp * r ^ (4:ℕ) * w ^
  (3:ℕ) * P * q * xv + kp ^ (3:ℕ) * w ^ (5:ℕ) * P * q * xv))))) + ((((2 * kp ^ (2:ℕ) * r * w ^
  (5:ℕ) * P * q * xv + (kp * r ^ (2:ℕ) * w ^ (5:ℕ) * P * q * xv - 7 * kp ^ (5:ℕ) * r * w * P ^
  (2:ℕ) * q * xv)) + ((-13 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w * P ^ (2:ℕ) * q * xv - 5 * kp ^ (3:ℕ) *
  r ^ (3:ℕ) * w * P ^ (2:ℕ) * q * xv) + (3 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w * P ^ (2:ℕ) * q * xv +
  2 * kp ^ (4:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * q * xv))) + ((3 * kp ^ (3:ℕ) * r * w ^ (3:ℕ) * P ^
  (2:ℕ) * q * xv + (3 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * q * xv - 4 * kp ^
  (4:ℕ) * r * w * P ^ (3:ℕ) * q * xv)) + ((3 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w * c * e * q * xv + 3
  * kp ^ (3:ℕ) * r ^ (3:ℕ) * w * c * e * q * xv) + (-3 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w * c * e * q
  * xv - 3 * kp * r ^ (5:ℕ) * w * c * e * q * xv)))) + (((-15 * kp ^ (3:ℕ) * r * w ^ (3:ℕ) * c
  * e * q * xv + (-22 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * c * e * q * xv - 7 * kp * r ^
  (3:ℕ) * w ^ (3:ℕ) * c * e * q * xv)) + ((4 * kp ^ (2:ℕ) * w ^ (5:ℕ) * c * e * q * xv + 4 * kp
  * r * w ^ (5:ℕ) * c * e * q * xv) + (7 * kp ^ (4:ℕ) * r * w * c * P * e * q * xv + 6 * kp ^
  (3:ℕ) * r ^ (2:ℕ) * w * c * P * e * q * xv))) + ((-kp ^ (2:ℕ) * r ^ (3:ℕ) * w * c * P * e * q
  * xv + (3 * kp ^ (3:ℕ) * w ^ (3:ℕ) * c * P * e * q * xv + 3 * kp ^ (2:ℕ) * r * w ^ (3:ℕ) * c
  * P * e * q * xv)) + ((2 * kp ^ (2:ℕ) * w ^ (3:ℕ) * c ^ (2:ℕ) * e ^ (2:ℕ) * q * xv - 5 * kp ^
  (4:ℕ) * r ^ (2:ℕ) * w * e * q ^ (2:ℕ) * xv) + (-4 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w * e * q ^
  (2:ℕ) * xv + kp ^ (2:ℕ) * r ^ (4:ℕ) * w * e * q ^ (2:ℕ) * xv))))))) + ((((((-17 * kp ^ (3:ℕ)
  * r * w ^ (3:ℕ) * e * q ^ (2:ℕ) * xv + (-11 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * e * q ^
  (2:ℕ) * xv - 9 * kp ^ (4:ℕ) * r * w * P * e * q ^ (2:ℕ) * xv)) + (2 * kp ^ (3:ℕ) * r ^ (2:ℕ)
  * w * P * e * q ^ (2:ℕ) * xv + (kp ^ (3:ℕ) * w ^ (3:ℕ) * P * e * q ^ (2:ℕ) * xv + 3 * kp ^
  (5:ℕ) * r ^ (2:ℕ) * w * P * κ * xv))) + ((7 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w * P * κ * xv + (5 *
  kp ^ (3:ℕ) * r ^ (4:ℕ) * w * P * κ * xv + kp ^ (2:ℕ) * r ^ (5:ℕ) * w * P * κ * xv)) + ((-2 *
  kp ^ (4:ℕ) * r * w ^ (3:ℕ) * P * κ * xv - 4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * P * κ *
  xv) + (-2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (3:ℕ) * P * κ * xv + 3 * kp ^ (5:ℕ) * r * w * P ^
  (2:ℕ) * κ * xv)))) + (((-kp ^ (4:ℕ) * r ^ (2:ℕ) * w * P ^ (2:ℕ) * κ * xv + (-3 * kp ^ (3:ℕ) *
  r ^ (3:ℕ) * w * P ^ (2:ℕ) * κ * xv + kp ^ (2:ℕ) * r ^ (4:ℕ) * w * P ^ (2:ℕ) * κ * xv)) + ((kp
  ^ (4:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * κ * xv + 2 * kp ^ (3:ℕ) * r * w ^ (3:ℕ) * P ^ (2:ℕ) * κ *
  xv) + (kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * κ * xv + 2 * kp ^ (5:ℕ) * w * P ^
  (3:ℕ) * κ * xv))) + ((-4 * kp ^ (4:ℕ) * r * w * P ^ (3:ℕ) * κ * xv + (2 * kp ^ (4:ℕ) * r ^
  (2:ℕ) * w * c * e * κ * xv + 4 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w * c * e * κ * xv)) + ((2 * kp ^
  (2:ℕ) * r ^ (4:ℕ) * w * c * e * κ * xv - kp ^ (3:ℕ) * r * w ^ (3:ℕ) * c * e * κ * xv) + (-2 *
  kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * c * e * κ * xv - kp * r ^ (3:ℕ) * w ^ (3:ℕ) * c * e * κ
  * xv))))) + ((((3 * kp ^ (4:ℕ) * r * w * c * P * e * κ * xv + (2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w
  * c * P * e * κ * xv - kp ^ (2:ℕ) * r ^ (3:ℕ) * w * c * P * e * κ * xv)) + (8 * kp ^ (3:ℕ) *
  w ^ (3:ℕ) * c * P * e * κ * xv + (8 * kp ^ (2:ℕ) * r * w ^ (3:ℕ) * c * P * e * κ * xv - 3 *
  kp ^ (4:ℕ) * r ^ (2:ℕ) * w * e * q * κ * xv))) + ((2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w * e * q * κ
  * xv + (5 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w * e * q * κ * xv + 2 * kp ^ (3:ℕ) * r * w ^ (3:ℕ) * e
  * q * κ * xv)) + ((2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * e * q * κ * xv - 14 * kp ^ (4:ℕ)
  * r * w * P * e * q * κ * xv) + (5 * kp ^ (3:ℕ) * w ^ (3:ℕ) * P * e * q * κ * xv - 2 * kp ^
  (4:ℕ) * r ^ (2:ℕ) * w * e * κ ^ (2:ℕ) * xv)))) + (((-2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w * e * κ ^
  (2:ℕ) * xv + (-5 * kp ^ (4:ℕ) * r * w * P * e * κ ^ (2:ℕ) * xv - 2 * kp ^ (3:ℕ) * r ^ (2:ℕ) *
  w * P * e * κ ^ (2:ℕ) * xv)) + ((-2 * kp ^ (3:ℕ) * w ^ (3:ℕ) * P * e * κ ^ (2:ℕ) * xv + 6 *
  kp ^ (4:ℕ) * r * w * c * P ^ (2:ℕ) * rv * xv) + (14 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w * c * P ^
  (2:ℕ) * rv * xv + 10 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w * c * P ^ (2:ℕ) * rv * xv))) + ((2 * kp * r
  ^ (4:ℕ) * w * c * P ^ (2:ℕ) * rv * xv + (-2 * kp ^ (3:ℕ) * w ^ (3:ℕ) * c * P ^ (2:ℕ) * rv *
  xv - 4 * kp ^ (2:ℕ) * r * w ^ (3:ℕ) * c * P ^ (2:ℕ) * rv * xv)) + ((-2 * kp * r ^ (2:ℕ) * w ^
  (3:ℕ) * c * P ^ (2:ℕ) * rv * xv + 4 * kp ^ (4:ℕ) * w * c * P ^ (3:ℕ) * rv * xv) + (-4 * kp ^
  (2:ℕ) * r ^ (2:ℕ) * w * c * P ^ (3:ℕ) * rv * xv + kp ^ (3:ℕ) * r * w * c ^ (2:ℕ) * P * e * rv
  * xv)))))) + (((((2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * c ^ (2:ℕ) * P * e * rv * xv + (kp * r ^
  (3:ℕ) * w * c ^ (2:ℕ) * P * e * rv * xv + 2 * kp ^ (5:ℕ) * r ^ (2:ℕ) * w * q * rv * xv)) + (6
  * kp ^ (4:ℕ) * r ^ (3:ℕ) * w * q * rv * xv + (6 * kp ^ (3:ℕ) * r ^ (4:ℕ) * w * q * rv * xv +
  2 * kp ^ (2:ℕ) * r ^ (5:ℕ) * w * q * rv * xv))) + ((-2 * kp ^ (4:ℕ) * r * w ^ (3:ℕ) * q * rv
  * xv + (-6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * q * rv * xv - 6 * kp ^ (2:ℕ) * r ^ (3:ℕ) *
  w ^ (3:ℕ) * q * rv * xv)) + ((-2 * kp * r ^ (4:ℕ) * w ^ (3:ℕ) * q * rv * xv + kp ^ (5:ℕ) * r
  * w * P * q * rv * xv) + (-3 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w * P * q * rv * xv - 11 * kp ^ (3:ℕ)
  * r ^ (3:ℕ) * w * P * q * rv * xv)))) + (((-5 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w * P * q * rv * xv
  + (2 * kp * r ^ (5:ℕ) * w * P * q * rv * xv + 2 * kp ^ (4:ℕ) * w ^ (3:ℕ) * P * q * rv * xv))
  + ((2 * kp ^ (3:ℕ) * r * w ^ (3:ℕ) * P * q * rv * xv + 2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ)
  * P * q * rv * xv) + (2 * kp * r ^ (3:ℕ) * w ^ (3:ℕ) * P * q * rv * xv - 5 * kp ^ (5:ℕ) * w *
  P ^ (2:ℕ) * q * rv * xv))) + ((-3 * kp ^ (4:ℕ) * r * w * P ^ (2:ℕ) * q * rv * xv + (11 * kp ^
  (3:ℕ) * r ^ (2:ℕ) * w * P ^ (2:ℕ) * q * rv * xv + 13 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w * P ^ (2:ℕ)
  * q * rv * xv)) + ((-kp ^ (3:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * q * rv * xv + 3 * kp ^ (2:ℕ) * r *
  w ^ (3:ℕ) * P ^ (2:ℕ) * q * rv * xv) + (-4 * kp ^ (4:ℕ) * w * P ^ (3:ℕ) * q * rv * xv + 4 *
  kp ^ (3:ℕ) * r * w * P ^ (3:ℕ) * q * rv * xv))))) + ((((kp ^ (4:ℕ) * r * w * c * e * q * rv *
  xv + (-kp ^ (3:ℕ) * r ^ (2:ℕ) * w * c * e * q * rv * xv - 5 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w * c
  * e * q * rv * xv)) + ((-3 * kp * r ^ (4:ℕ) * w * c * e * q * rv * xv + 4 * kp ^ (3:ℕ) * w ^
  (3:ℕ) * c * e * q * rv * xv) + (8 * kp ^ (2:ℕ) * r * w ^ (3:ℕ) * c * e * q * rv * xv + 4 * kp
  * r ^ (2:ℕ) * w ^ (3:ℕ) * c * e * q * rv * xv))) + ((5 * kp ^ (4:ℕ) * w * c * P * e * q * rv
  * xv + (-2 * kp ^ (3:ℕ) * r * w * c * P * e * q * rv * xv - 7 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w *
  c * P * e * q * rv * xv)) + ((-7 * kp ^ (4:ℕ) * r * w * e * q ^ (2:ℕ) * rv * xv - 10 * kp ^
  (3:ℕ) * r ^ (2:ℕ) * w * e * q ^ (2:ℕ) * rv * xv) + (-3 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w * e * q ^
  (2:ℕ) * rv * xv - 4 * kp ^ (3:ℕ) * w ^ (3:ℕ) * e * q ^ (2:ℕ) * rv * xv)))) + (((-4 * kp ^
  (2:ℕ) * r * w ^ (3:ℕ) * e * q ^ (2:ℕ) * rv * xv + (-7 * kp ^ (4:ℕ) * w * P * e * q ^ (2:ℕ) *
  rv * xv + 12 * kp ^ (3:ℕ) * r * w * P * e * q ^ (2:ℕ) * rv * xv)) + ((kp ^ (5:ℕ) * r * w * P
  * κ * rv * xv + 3 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w * P * κ * rv * xv) + (3 * kp ^ (3:ℕ) * r ^
  (3:ℕ) * w * P * κ * rv * xv + kp ^ (2:ℕ) * r ^ (4:ℕ) * w * P * κ * rv * xv))) + ((-kp ^ (5:ℕ)
  * w * P ^ (2:ℕ) * κ * rv * xv + (-7 * kp ^ (4:ℕ) * r * w * P ^ (2:ℕ) * κ * rv * xv - 3 * kp ^
  (3:ℕ) * r ^ (2:ℕ) * w * P ^ (2:ℕ) * κ * rv * xv)) + ((3 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w * P ^
  (2:ℕ) * κ * rv * xv - 8 * kp ^ (4:ℕ) * w * P ^ (3:ℕ) * κ * rv * xv) + (4 * kp ^ (3:ℕ) * r * w
  * P ^ (3:ℕ) * κ * rv * xv + kp ^ (4:ℕ) * w * c * P * e * κ * rv * xv)))))))) + (((((((-2 * kp
  ^ (3:ℕ) * r * w * c * P * e * κ * rv * xv + (-3 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * c * P * e * κ
  * rv * xv + kp ^ (4:ℕ) * r * w * e * q * κ * rv * xv)) + (6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w * e
  * q * κ * rv * xv + (5 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w * e * q * κ * rv * xv - 10 * kp ^ (4:ℕ) *
  w * P * e * q * κ * rv * xv))) + ((12 * kp ^ (3:ℕ) * r * w * P * e * q * κ * rv * xv + (-3 *
  kp ^ (4:ℕ) * w * P * e * κ ^ (2:ℕ) * rv * xv + kp ^ (4:ℕ) * w * c * P ^ (2:ℕ) * rv ^ (2:ℕ) *
  xv)) + ((3 * kp ^ (3:ℕ) * r * w * c * P ^ (2:ℕ) * rv ^ (2:ℕ) * xv + 3 * kp ^ (2:ℕ) * r ^
  (2:ℕ) * w * c * P ^ (2:ℕ) * rv ^ (2:ℕ) * xv) + (kp * r ^ (3:ℕ) * w * c * P ^ (2:ℕ) * rv ^
  (2:ℕ) * xv - 4 * kp ^ (3:ℕ) * w * c * P ^ (3:ℕ) * rv ^ (2:ℕ) * xv)))) + (((-4 * kp ^ (2:ℕ) *
  r * w * c * P ^ (3:ℕ) * rv ^ (2:ℕ) * xv + (kp ^ (5:ℕ) * w * P * q * rv ^ (2:ℕ) * xv - 2 * kp
  ^ (4:ℕ) * r * w * P * q * rv ^ (2:ℕ) * xv)) + ((-6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w * P * q * rv
  ^ (2:ℕ) * xv - 2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w * P * q * rv ^ (2:ℕ) * xv) + (kp * r ^ (4:ℕ) *
  w * P * q * rv ^ (2:ℕ) * xv + 6 * kp ^ (4:ℕ) * w * P ^ (2:ℕ) * q * rv ^ (2:ℕ) * xv))) + ((16
  * kp ^ (3:ℕ) * r * w * P ^ (2:ℕ) * q * rv ^ (2:ℕ) * xv + (12 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * P
  ^ (2:ℕ) * q * rv ^ (2:ℕ) * xv + 2 * kp ^ (2:ℕ) * w ^ (3:ℕ) * P ^ (2:ℕ) * q * rv ^ (2:ℕ) *
  xv)) + ((4 * kp ^ (3:ℕ) * w * P ^ (3:ℕ) * q * rv ^ (2:ℕ) * xv - 4 * kp ^ (3:ℕ) * w * c * P *
  e * q * rv ^ (2:ℕ) * xv) + (-4 * kp ^ (2:ℕ) * r * w * c * P * e * q * rv ^ (2:ℕ) * xv - 4 *
  kp ^ (4:ℕ) * w * e * q ^ (2:ℕ) * rv ^ (2:ℕ) * xv))))) + ((((-8 * kp ^ (3:ℕ) * r * w * e * q ^
  (2:ℕ) * rv ^ (2:ℕ) * xv + (-4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * e * q ^ (2:ℕ) * rv ^ (2:ℕ) * xv
  + 8 * kp ^ (3:ℕ) * w * P * e * q ^ (2:ℕ) * rv ^ (2:ℕ) * xv)) + (2 * kp ^ (4:ℕ) * w * P ^
  (2:ℕ) * κ * rv ^ (2:ℕ) * xv + (4 * kp ^ (3:ℕ) * r * w * P ^ (2:ℕ) * κ * rv ^ (2:ℕ) * xv + 2 *
  kp ^ (2:ℕ) * r ^ (2:ℕ) * w * P ^ (2:ℕ) * κ * rv ^ (2:ℕ) * xv))) + ((6 * kp ^ (3:ℕ) * w * P ^
  (3:ℕ) * κ * rv ^ (2:ℕ) * xv + (8 * kp ^ (3:ℕ) * w * P * e * q * κ * rv ^ (2:ℕ) * xv + 2 * kp
  ^ (3:ℕ) * w * P ^ (2:ℕ) * q * rv ^ (3:ℕ) * xv)) + ((2 * kp ^ (2:ℕ) * r * w * P ^ (2:ℕ) * q *
  rv ^ (3:ℕ) * xv + 2 * kp ^ (4:ℕ) * r ^ (2:ℕ) * c * P ^ (2:ℕ) * xv ^ (2:ℕ)) + (4 * kp ^ (3:ℕ)
  * r ^ (3:ℕ) * c * P ^ (2:ℕ) * xv ^ (2:ℕ) + 2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * c * P ^ (2:ℕ) * xv ^
  (2:ℕ))))) + (((3 * kp ^ (4:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * xv ^ (2:ℕ) + (8 * kp ^ (3:ℕ) * r
  * w ^ (2:ℕ) * c * P ^ (2:ℕ) * xv ^ (2:ℕ) + 7 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P ^
  (2:ℕ) * xv ^ (2:ℕ))) + ((2 * kp * r ^ (3:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * xv ^ (2:ℕ) + 2 * kp
  ^ (4:ℕ) * r * c * P ^ (3:ℕ) * xv ^ (2:ℕ)) + (2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * c * P ^ (3:ℕ) * xv
  ^ (2:ℕ) - kp ^ (3:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * P * e * xv ^ (2:ℕ)))) + ((-2 * kp ^ (2:ℕ) * r
  * w ^ (2:ℕ) * c ^ (2:ℕ) * P * e * xv ^ (2:ℕ) + (-kp * r ^ (2:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * P *
  e * xv ^ (2:ℕ) - kp ^ (5:ℕ) * r ^ (3:ℕ) * q * xv ^ (2:ℕ))) + ((-2 * kp ^ (4:ℕ) * r ^ (4:ℕ) *
  q * xv ^ (2:ℕ) - kp ^ (3:ℕ) * r ^ (5:ℕ) * q * xv ^ (2:ℕ)) + (2 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^
  (2:ℕ) * q * xv ^ (2:ℕ) + 4 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * q * xv ^ (2:ℕ))))))) +
  (((((2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * q * xv ^ (2:ℕ) + (-kp ^ (3:ℕ) * r * w ^ (4:ℕ) *
  q * xv ^ (2:ℕ) - 2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * q * xv ^ (2:ℕ))) + (-kp * r ^ (3:ℕ)
  * w ^ (4:ℕ) * q * xv ^ (2:ℕ) + (-5 * kp ^ (5:ℕ) * r ^ (2:ℕ) * P * q * xv ^ (2:ℕ) - 11 * kp ^
  (4:ℕ) * r ^ (3:ℕ) * P * q * xv ^ (2:ℕ)))) + ((-9 * kp ^ (3:ℕ) * r ^ (4:ℕ) * P * q * xv ^
  (2:ℕ) + (-3 * kp ^ (2:ℕ) * r ^ (5:ℕ) * P * q * xv ^ (2:ℕ) - 10 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) *
  P * q * xv ^ (2:ℕ))) + ((-20 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * q * xv ^ (2:ℕ) - 8 *
  kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P * q * xv ^ (2:ℕ)) + (2 * kp * r ^ (4:ℕ) * w ^ (2:ℕ) *
  P * q * xv ^ (2:ℕ) + 2 * kp ^ (3:ℕ) * w ^ (4:ℕ) * P * q * xv ^ (2:ℕ))))) + (((4 * kp ^ (2:ℕ)
  * r * w ^ (4:ℕ) * P * q * xv ^ (2:ℕ) + (2 * kp * r ^ (2:ℕ) * w ^ (4:ℕ) * P * q * xv ^ (2:ℕ) -
  5 * kp ^ (5:ℕ) * r * P ^ (2:ℕ) * q * xv ^ (2:ℕ))) + ((-9 * kp ^ (4:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ)
  * q * xv ^ (2:ℕ) - 4 * kp ^ (3:ℕ) * r ^ (3:ℕ) * P ^ (2:ℕ) * q * xv ^ (2:ℕ)) + (kp ^ (2:ℕ) * r
  ^ (4:ℕ) * P ^ (2:ℕ) * q * xv ^ (2:ℕ) + 7 * kp ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * q * xv ^
  (2:ℕ)))) + ((15 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * q * xv ^ (2:ℕ) + (9 * kp ^ (2:ℕ) *
  r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * q * xv ^ (2:ℕ) - 2 * kp ^ (4:ℕ) * r * P ^ (3:ℕ) * q * xv
  ^ (2:ℕ))) + ((-9 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * c * e * q * xv ^ (2:ℕ) - 14 * kp ^ (2:ℕ) * r
  ^ (2:ℕ) * w ^ (2:ℕ) * c * e * q * xv ^ (2:ℕ)) + (-5 * kp * r ^ (3:ℕ) * w ^ (2:ℕ) * c * e * q
  * xv ^ (2:ℕ) + 2 * kp ^ (2:ℕ) * w ^ (4:ℕ) * c * e * q * xv ^ (2:ℕ)))))) + ((((2 * kp * r * w
  ^ (4:ℕ) * c * e * q * xv ^ (2:ℕ) + (3 * kp ^ (3:ℕ) * w ^ (2:ℕ) * c * P * e * q * xv ^ (2:ℕ) +
  3 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * c * P * e * q * xv ^ (2:ℕ))) + ((kp ^ (2:ℕ) * w ^ (2:ℕ) * c
  ^ (2:ℕ) * e ^ (2:ℕ) * q * xv ^ (2:ℕ) - 16 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * e * q ^ (2:ℕ) * xv ^
  (2:ℕ)) + (-10 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * e * q ^ (2:ℕ) * xv ^ (2:ℕ) + 2 * kp ^
  (3:ℕ) * w ^ (2:ℕ) * P * e * q ^ (2:ℕ) * xv ^ (2:ℕ)))) + ((kp ^ (5:ℕ) * r ^ (2:ℕ) * P * κ * xv
  ^ (2:ℕ) + (2 * kp ^ (4:ℕ) * r ^ (3:ℕ) * P * κ * xv ^ (2:ℕ) + kp ^ (3:ℕ) * r ^ (4:ℕ) * P * κ *
  xv ^ (2:ℕ))) + ((-kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P * κ * xv ^ (2:ℕ) - 2 * kp ^ (3:ℕ) * r ^
  (2:ℕ) * w ^ (2:ℕ) * P * κ * xv ^ (2:ℕ)) + (-kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P * κ * xv ^
  (2:ℕ) + kp ^ (5:ℕ) * r * P ^ (2:ℕ) * κ * xv ^ (2:ℕ))))) + (((-3 * kp ^ (4:ℕ) * r ^ (2:ℕ) * P
  ^ (2:ℕ) * κ * xv ^ (2:ℕ) + (-5 * kp ^ (3:ℕ) * r ^ (3:ℕ) * P ^ (2:ℕ) * κ * xv ^ (2:ℕ) - kp ^
  (2:ℕ) * r ^ (4:ℕ) * P ^ (2:ℕ) * κ * xv ^ (2:ℕ))) + ((2 * kp ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) *
  κ * xv ^ (2:ℕ) + 4 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * κ * xv ^ (2:ℕ)) + (2 * kp ^
  (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * κ * xv ^ (2:ℕ) + kp ^ (5:ℕ) * P ^ (3:ℕ) * κ * xv
  ^ (2:ℕ)))) + ((-2 * kp ^ (4:ℕ) * r * P ^ (3:ℕ) * κ * xv ^ (2:ℕ) + (4 * kp ^ (3:ℕ) * w ^ (2:ℕ)
  * c * P * e * κ * xv ^ (2:ℕ) + 4 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * c * P * e * κ * xv ^ (2:ℕ)))
  + ((kp ^ (3:ℕ) * r * w ^ (2:ℕ) * e * q * κ * xv ^ (2:ℕ) + kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ)
  * e * q * κ * xv ^ (2:ℕ)) + (7 * kp ^ (3:ℕ) * w ^ (2:ℕ) * P * e * q * κ * xv ^ (2:ℕ) - kp ^
  (3:ℕ) * w ^ (2:ℕ) * P * e * κ ^ (2:ℕ) * xv ^ (2:ℕ)))))))) + ((((((2 * kp ^ (4:ℕ) * r * c * P
  ^ (2:ℕ) * rv * xv ^ (2:ℕ) + (4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * c * P ^ (2:ℕ) * rv * xv ^ (2:ℕ) + 2
  * kp ^ (2:ℕ) * r ^ (3:ℕ) * c * P ^ (2:ℕ) * rv * xv ^ (2:ℕ))) + (-kp ^ (3:ℕ) * w ^ (2:ℕ) * c *
  P ^ (2:ℕ) * rv * xv ^ (2:ℕ) + (-2 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * c * P ^ (2:ℕ) * rv * xv ^
  (2:ℕ) - kp * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * rv * xv ^ (2:ℕ)))) + ((2 * kp ^ (4:ℕ) *
  c * P ^ (3:ℕ) * rv * xv ^ (2:ℕ) + (-2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c * P ^ (3:ℕ) * rv * xv ^
  (2:ℕ) - 3 * kp ^ (5:ℕ) * r * P * q * rv * xv ^ (2:ℕ))) + ((-7 * kp ^ (4:ℕ) * r ^ (2:ℕ) * P *
  q * rv * xv ^ (2:ℕ) - 7 * kp ^ (3:ℕ) * r ^ (3:ℕ) * P * q * rv * xv ^ (2:ℕ)) + (-3 * kp ^
  (2:ℕ) * r ^ (4:ℕ) * P * q * rv * xv ^ (2:ℕ) + 2 * kp ^ (4:ℕ) * w ^ (2:ℕ) * P * q * rv * xv ^
  (2:ℕ))))) + (((4 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P * q * rv * xv ^ (2:ℕ) + (4 * kp ^ (2:ℕ) * r
  ^ (2:ℕ) * w ^ (2:ℕ) * P * q * rv * xv ^ (2:ℕ) + 2 * kp * r ^ (3:ℕ) * w ^ (2:ℕ) * P * q * rv *
  xv ^ (2:ℕ))) + ((-4 * kp ^ (5:ℕ) * P ^ (2:ℕ) * q * rv * xv ^ (2:ℕ) - 2 * kp ^ (4:ℕ) * r * P ^
  (2:ℕ) * q * rv * xv ^ (2:ℕ)) + (6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ) * q * rv * xv ^ (2:ℕ)
  + 6 * kp ^ (2:ℕ) * r ^ (3:ℕ) * P ^ (2:ℕ) * q * rv * xv ^ (2:ℕ)))) + ((kp ^ (3:ℕ) * w ^ (2:ℕ)
  * P ^ (2:ℕ) * q * rv * xv ^ (2:ℕ) + (3 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * q * rv * xv
  ^ (2:ℕ) - 2 * kp ^ (4:ℕ) * P ^ (3:ℕ) * q * rv * xv ^ (2:ℕ))) + ((2 * kp ^ (3:ℕ) * r * P ^
  (3:ℕ) * q * rv * xv ^ (2:ℕ) - 2 * kp ^ (3:ℕ) * w ^ (2:ℕ) * e * q ^ (2:ℕ) * rv * xv ^ (2:ℕ)) +
  (-2 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * e * q ^ (2:ℕ) * rv * xv ^ (2:ℕ) - kp ^ (5:ℕ) * P ^ (2:ℕ) *
  κ * rv * xv ^ (2:ℕ)))))) + ((((-7 * kp ^ (4:ℕ) * r * P ^ (2:ℕ) * κ * rv * xv ^ (2:ℕ) + (-7 *
  kp ^ (3:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ) * κ * rv * xv ^ (2:ℕ) - kp ^ (2:ℕ) * r ^ (3:ℕ) * P ^ (2:ℕ)
  * κ * rv * xv ^ (2:ℕ))) + ((-4 * kp ^ (4:ℕ) * P ^ (3:ℕ) * κ * rv * xv ^ (2:ℕ) + 2 * kp ^
  (3:ℕ) * r * P ^ (3:ℕ) * κ * rv * xv ^ (2:ℕ)) + (-2 * kp ^ (3:ℕ) * c * P ^ (3:ℕ) * rv ^ (2:ℕ)
  * xv ^ (2:ℕ) - 2 * kp ^ (2:ℕ) * r * c * P ^ (3:ℕ) * rv ^ (2:ℕ) * xv ^ (2:ℕ)))) + ((5 * kp ^
  (4:ℕ) * P ^ (2:ℕ) * q * rv ^ (2:ℕ) * xv ^ (2:ℕ) + (9 * kp ^ (3:ℕ) * r * P ^ (2:ℕ) * q * rv ^
  (2:ℕ) * xv ^ (2:ℕ) + 5 * kp ^ (2:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ) * q * rv ^ (2:ℕ) * xv ^ (2:ℕ))) +
  ((kp ^ (2:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * q * rv ^ (2:ℕ) * xv ^ (2:ℕ) + 2 * kp ^ (3:ℕ) * P ^
  (3:ℕ) * q * rv ^ (2:ℕ) * xv ^ (2:ℕ)) + (3 * kp ^ (3:ℕ) * P ^ (3:ℕ) * κ * rv ^ (2:ℕ) * xv ^
  (2:ℕ) + kp ^ (4:ℕ) * w * c * P ^ (2:ℕ) * xv ^ (3:ℕ))))) + (((3 * kp ^ (3:ℕ) * r * w * c * P ^
  (2:ℕ) * xv ^ (3:ℕ) + (3 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * c * P ^ (2:ℕ) * xv ^ (3:ℕ) + kp * r ^
  (3:ℕ) * w * c * P ^ (2:ℕ) * xv ^ (3:ℕ))) + ((-5 * kp ^ (4:ℕ) * r * w * P * q * xv ^ (3:ℕ) -
  10 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w * P * q * xv ^ (3:ℕ)) + (-5 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w * P
  * q * xv ^ (3:ℕ) + kp ^ (3:ℕ) * w ^ (3:ℕ) * P * q * xv ^ (3:ℕ)))) + ((2 * kp ^ (2:ℕ) * r * w
  ^ (3:ℕ) * P * q * xv ^ (3:ℕ) + (kp * r ^ (2:ℕ) * w ^ (3:ℕ) * P * q * xv ^ (3:ℕ) + 8 * kp ^
  (4:ℕ) * w * P ^ (2:ℕ) * q * xv ^ (3:ℕ))) + ((17 * kp ^ (3:ℕ) * r * w * P ^ (2:ℕ) * q * xv ^
  (3:ℕ) + 9 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * P ^ (2:ℕ) * q * xv ^ (3:ℕ)) + (kp ^ (3:ℕ) * w * c *
  P * e * q * xv ^ (3:ℕ) + kp ^ (2:ℕ) * r * w * c * P * e * q * xv ^ (3:ℕ))))))) + (((((-5 * kp
  ^ (3:ℕ) * r * w * e * q ^ (2:ℕ) * xv ^ (3:ℕ) + (-3 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * e * q ^
  (2:ℕ) * xv ^ (3:ℕ) + kp ^ (3:ℕ) * w * P * e * q ^ (2:ℕ) * xv ^ (3:ℕ))) + (kp ^ (4:ℕ) * w * P
  ^ (2:ℕ) * κ * xv ^ (3:ℕ) + (2 * kp ^ (3:ℕ) * r * w * P ^ (2:ℕ) * κ * xv ^ (3:ℕ) + kp ^ (2:ℕ)
  * r ^ (2:ℕ) * w * P ^ (2:ℕ) * κ * xv ^ (3:ℕ)))) + ((3 * kp ^ (3:ℕ) * w * P * e * q * κ * xv ^
  (3:ℕ) + (kp ^ (3:ℕ) * w * P ^ (2:ℕ) * q * rv * xv ^ (3:ℕ) + kp ^ (2:ℕ) * r * w * P ^ (2:ℕ) *
  q * rv * xv ^ (3:ℕ))) + ((3 * kp ^ (4:ℕ) * P ^ (2:ℕ) * q * xv ^ (4:ℕ) + 6 * kp ^ (3:ℕ) * r *
  P ^ (2:ℕ) * q * xv ^ (4:ℕ)) + (3 * kp ^ (2:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ) * q * xv ^ (4:ℕ) + kp ^
  (3:ℕ) * r ^ (3:ℕ) * c ^ (2:ℕ) * P ^ (2:ℕ))))) + (((2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * c ^ (2:ℕ) * P
  ^ (2:ℕ) + (kp * r ^ (5:ℕ) * c ^ (2:ℕ) * P ^ (2:ℕ) + kp ^ (3:ℕ) * r * w ^ (2:ℕ) * c ^ (2:ℕ) *
  P ^ (2:ℕ))) + ((2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * P ^ (2:ℕ) + kp * r ^
  (3:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * P ^ (2:ℕ)) + (2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * c * q
  + 3 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * c * q))) + ((-r ^ (6:ℕ) * w ^ (2:ℕ) * c * q + (2 *
  kp ^ (3:ℕ) * r * w ^ (4:ℕ) * c * q + 2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * c * q)) + ((-2
  * kp * r ^ (3:ℕ) * w ^ (4:ℕ) * c * q - 2 * r ^ (4:ℕ) * w ^ (4:ℕ) * c * q) + (-kp ^ (2:ℕ) * w
  ^ (6:ℕ) * c * q - 2 * kp * r * w ^ (6:ℕ) * c * q))))) + ((((-r ^ (2:ℕ) * w ^ (6:ℕ) * c * q +
  (2 * kp ^ (4:ℕ) * r ^ (3:ℕ) * c * P * q + 2 * kp ^ (3:ℕ) * r ^ (4:ℕ) * c * P * q)) + ((-2 *
  kp ^ (2:ℕ) * r ^ (5:ℕ) * c * P * q - 2 * kp * r ^ (6:ℕ) * c * P * q) + (-2 * kp ^ (4:ℕ) * r *
  w ^ (2:ℕ) * c * P * q - 6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P * q))) + ((-10 * kp ^
  (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * c * P * q + (-6 * kp * r ^ (4:ℕ) * w ^ (2:ℕ) * c * P * q - 2
  * kp ^ (3:ℕ) * w ^ (4:ℕ) * c * P * q)) + ((-6 * kp ^ (2:ℕ) * r * w ^ (4:ℕ) * c * P * q - 4 *
  kp * r ^ (2:ℕ) * w ^ (4:ℕ) * c * P * q) + (4 * kp ^ (4:ℕ) * r ^ (2:ℕ) * c * P ^ (2:ℕ) * q + 2
  * kp ^ (3:ℕ) * r ^ (3:ℕ) * c * P ^ (2:ℕ) * q)))) + (((-2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * c * P ^
  (2:ℕ) * q + (-kp ^ (4:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * q - 2 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * c
  * P ^ (2:ℕ) * q)) + ((-2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * q + kp ^
  (3:ℕ) * r * w ^ (2:ℕ) * c ^ (2:ℕ) * e * q) + (2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c ^
  (2:ℕ) * e * q + kp * r ^ (3:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * e * q))) + ((-2 * kp ^ (2:ℕ) * w ^
  (4:ℕ) * c ^ (2:ℕ) * e * q + (-2 * kp * r * w ^ (4:ℕ) * c ^ (2:ℕ) * e * q + kp ^ (3:ℕ) * r ^
  (5:ℕ) * q ^ (2:ℕ))) + ((2 * kp ^ (2:ℕ) * r ^ (6:ℕ) * q ^ (2:ℕ) + kp * r ^ (7:ℕ) * q ^ (2:ℕ))
  + (2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * q ^ (2:ℕ) + 2 * kp * r ^ (5:ℕ) * w ^ (2:ℕ) * q ^
  (2:ℕ)))))))))))

/-- Terms 1747–2619 of `delta8F`. -/
def delta8F2 (kp r w c P e q κ rv xv : ℝ) : ℝ :=
  (((((((((3 * kp ^ (3:ℕ) * r * w ^ (4:ℕ) * q ^ (2:ℕ) + (4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ)
  * q ^ (2:ℕ) + kp * r ^ (3:ℕ) * w ^ (4:ℕ) * q ^ (2:ℕ))) + (-4 * kp ^ (4:ℕ) * r ^ (3:ℕ) * P * q
  ^ (2:ℕ) + (-2 * kp ^ (3:ℕ) * r ^ (4:ℕ) * P * q ^ (2:ℕ) + 2 * kp ^ (2:ℕ) * r ^ (5:ℕ) * P * q ^
  (2:ℕ)))) + ((4 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P * q ^ (2:ℕ) + (4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w
  ^ (2:ℕ) * P * q ^ (2:ℕ) + 2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P * q ^ (2:ℕ))) + ((kp ^
  (5:ℕ) * r * P ^ (2:ℕ) * q ^ (2:ℕ) - 4 * kp ^ (4:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ) * q ^ (2:ℕ)) + (kp
  ^ (3:ℕ) * r ^ (3:ℕ) * P ^ (2:ℕ) * q ^ (2:ℕ) + kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * q ^
  (2:ℕ))))) + (((-2 * kp ^ (2:ℕ) * w ^ (4:ℕ) * c * e * q ^ (2:ℕ) + (3 * kp ^ (3:ℕ) * r * w ^
  (2:ℕ) * e * q ^ (3:ℕ) + 4 * kp ^ (4:ℕ) * r ^ (3:ℕ) * c * P * κ)) + ((8 * kp ^ (3:ℕ) * r ^
  (4:ℕ) * c * P * κ + 4 * kp ^ (2:ℕ) * r ^ (5:ℕ) * c * P * κ) + (3 * kp ^ (4:ℕ) * r * w ^ (2:ℕ)
  * c * P * κ + 5 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P * κ))) + ((kp ^ (2:ℕ) * r ^
  (3:ℕ) * w ^ (2:ℕ) * c * P * κ + (-kp * r ^ (4:ℕ) * w ^ (2:ℕ) * c * P * κ - kp ^ (3:ℕ) * w ^
  (4:ℕ) * c * P * κ)) + ((-2 * kp ^ (2:ℕ) * r * w ^ (4:ℕ) * c * P * κ - kp * r ^ (2:ℕ) * w ^
  (4:ℕ) * c * P * κ) + (4 * kp ^ (4:ℕ) * r ^ (2:ℕ) * c * P ^ (2:ℕ) * κ + 2 * kp ^ (3:ℕ) * r ^
  (3:ℕ) * c * P ^ (2:ℕ) * κ))))) + ((((-2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * c * P ^ (2:ℕ) * κ + (2 *
  kp ^ (4:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * κ - 2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P ^
  (2:ℕ) * κ)) + (-kp ^ (3:ℕ) * r * w ^ (2:ℕ) * c ^ (2:ℕ) * e * κ + (-2 * kp ^ (2:ℕ) * r ^ (2:ℕ)
  * w ^ (2:ℕ) * c ^ (2:ℕ) * e * κ - kp * r ^ (3:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * e * κ))) + ((-2 *
  kp ^ (4:ℕ) * r ^ (4:ℕ) * q * κ + (-4 * kp ^ (3:ℕ) * r ^ (5:ℕ) * q * κ - 2 * kp ^ (2:ℕ) * r ^
  (6:ℕ) * q * κ)) + ((-6 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * q * κ - 14 * kp ^ (3:ℕ) * r ^
  (3:ℕ) * w ^ (2:ℕ) * q * κ) + (-8 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * q * κ - 2 * kp ^
  (3:ℕ) * r * w ^ (4:ℕ) * q * κ)))) + (((-2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * q * κ + (2 *
  kp ^ (5:ℕ) * r ^ (2:ℕ) * P * q * κ - 6 * kp ^ (4:ℕ) * r ^ (3:ℕ) * P * q * κ)) + ((-6 * kp ^
  (3:ℕ) * r ^ (4:ℕ) * P * q * κ + 2 * kp ^ (2:ℕ) * r ^ (5:ℕ) * P * q * κ) + (-kp ^ (4:ℕ) * r *
  w ^ (2:ℕ) * P * q * κ + 3 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P * q * κ))) + ((-kp ^ (3:ℕ)
  * w ^ (4:ℕ) * P * q * κ + (kp ^ (2:ℕ) * r * w ^ (4:ℕ) * P * q * κ + 2 * kp ^ (5:ℕ) * r * P ^
  (2:ℕ) * q * κ)) + ((-8 * kp ^ (4:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ) * q * κ + 2 * kp ^ (3:ℕ) * r ^
  (3:ℕ) * P ^ (2:ℕ) * q * κ) + (-2 * kp ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * q * κ + 2 * kp ^
  (3:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * q * κ)))))) + (((((4 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * c * e
  * q * κ + (4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * e * q * κ + 5 * kp ^ (3:ℕ) * r * w ^
  (2:ℕ) * e * q ^ (2:ℕ) * κ)) + (kp ^ (5:ℕ) * r ^ (3:ℕ) * κ ^ (2:ℕ) + (2 * kp ^ (4:ℕ) * r ^
  (4:ℕ) * κ ^ (2:ℕ) + kp ^ (3:ℕ) * r ^ (5:ℕ) * κ ^ (2:ℕ)))) + ((-kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^
  (2:ℕ) * κ ^ (2:ℕ) + (-2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * κ ^ (2:ℕ) - kp ^ (2:ℕ) * r ^
  (4:ℕ) * w ^ (2:ℕ) * κ ^ (2:ℕ))) + ((2 * kp ^ (5:ℕ) * r ^ (2:ℕ) * P * κ ^ (2:ℕ) - 2 * kp ^
  (4:ℕ) * r ^ (3:ℕ) * P * κ ^ (2:ℕ)) + (-4 * kp ^ (3:ℕ) * r ^ (4:ℕ) * P * κ ^ (2:ℕ) - 2 * kp ^
  (4:ℕ) * r * w ^ (2:ℕ) * P * κ ^ (2:ℕ))))) + (((-2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P *
  κ ^ (2:ℕ) + (kp ^ (5:ℕ) * r * P ^ (2:ℕ) * κ ^ (2:ℕ) - 4 * kp ^ (4:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ)
  * κ ^ (2:ℕ))) + ((kp ^ (3:ℕ) * r ^ (3:ℕ) * P ^ (2:ℕ) * κ ^ (2:ℕ) - 2 * kp ^ (4:ℕ) * w ^ (2:ℕ)
  * P ^ (2:ℕ) * κ ^ (2:ℕ)) + (kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * κ ^ (2:ℕ) + 4 * kp ^
  (3:ℕ) * r * w ^ (2:ℕ) * c * e * κ ^ (2:ℕ)))) + ((4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c *
  e * κ ^ (2:ℕ) + (kp ^ (3:ℕ) * r * w ^ (2:ℕ) * e * q * κ ^ (2:ℕ) - kp ^ (3:ℕ) * r * w ^ (2:ℕ)
  * e * κ ^ (3:ℕ))) + ((3 * kp ^ (3:ℕ) * r ^ (2:ℕ) * c ^ (2:ℕ) * P ^ (2:ℕ) * rv + 6 * kp ^
  (2:ℕ) * r ^ (3:ℕ) * c ^ (2:ℕ) * P ^ (2:ℕ) * rv) + (3 * kp * r ^ (4:ℕ) * c ^ (2:ℕ) * P ^ (2:ℕ)
  * rv + kp ^ (3:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * P ^ (2:ℕ) * rv))))) + ((((2 * kp ^ (2:ℕ) * r * w
  ^ (2:ℕ) * c ^ (2:ℕ) * P ^ (2:ℕ) * rv + (kp * r ^ (2:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * P ^ (2:ℕ) *
  rv + 2 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * c * q * rv)) + ((4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ)
  * c * q * rv - 4 * kp * r ^ (4:ℕ) * w ^ (2:ℕ) * c * q * rv) + (-2 * r ^ (5:ℕ) * w ^ (2:ℕ) * c
  * q * rv - 2 * kp ^ (3:ℕ) * w ^ (4:ℕ) * c * q * rv))) + ((-6 * kp ^ (2:ℕ) * r * w ^ (4:ℕ) * c
  * q * rv + (-6 * kp * r ^ (2:ℕ) * w ^ (4:ℕ) * c * q * rv - 2 * r ^ (3:ℕ) * w ^ (4:ℕ) * c * q
  * rv)) + ((2 * kp ^ (4:ℕ) * r ^ (2:ℕ) * c * P * q * rv - 2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * c * P *
  q * rv) + (-10 * kp ^ (2:ℕ) * r ^ (4:ℕ) * c * P * q * rv - 6 * kp * r ^ (5:ℕ) * c * P * q *
  rv)))) + (((2 * kp ^ (4:ℕ) * w ^ (2:ℕ) * c * P * q * rv + (-6 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) *
  c * P * q * rv - 22 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P * q * rv)) + ((-14 * kp * r
  ^ (3:ℕ) * w ^ (2:ℕ) * c * P * q * rv - 2 * kp ^ (2:ℕ) * w ^ (4:ℕ) * c * P * q * rv) + (-2 *
  kp * r * w ^ (4:ℕ) * c * P * q * rv + 8 * kp ^ (4:ℕ) * r * c * P ^ (2:ℕ) * q * rv))) + ((-2 *
  kp ^ (3:ℕ) * r ^ (2:ℕ) * c * P ^ (2:ℕ) * q * rv + (-10 * kp ^ (2:ℕ) * r ^ (3:ℕ) * c * P ^
  (2:ℕ) * q * rv - 2 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * c * P ^ (2:ℕ) * q * rv)) + ((2 * kp ^ (4:ℕ)
  * r ^ (3:ℕ) * q ^ (2:ℕ) * rv + 7 * kp ^ (3:ℕ) * r ^ (4:ℕ) * q ^ (2:ℕ) * rv) + (8 * kp ^ (2:ℕ)
  * r ^ (5:ℕ) * q ^ (2:ℕ) * rv + 3 * kp * r ^ (6:ℕ) * q ^ (2:ℕ) * rv))))))) + ((((((4 * kp ^
  (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * q ^ (2:ℕ) * rv + (8 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * q
  ^ (2:ℕ) * rv + 4 * kp * r ^ (4:ℕ) * w ^ (2:ℕ) * q ^ (2:ℕ) * rv)) + (kp ^ (3:ℕ) * w ^ (4:ℕ) *
  q ^ (2:ℕ) * rv + (2 * kp ^ (2:ℕ) * r * w ^ (4:ℕ) * q ^ (2:ℕ) * rv + kp * r ^ (2:ℕ) * w ^
  (4:ℕ) * q ^ (2:ℕ) * rv))) + ((-2 * kp ^ (5:ℕ) * r * P * q ^ (2:ℕ) * rv + (-8 * kp ^ (4:ℕ) * r
  ^ (2:ℕ) * P * q ^ (2:ℕ) * rv + 2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * P * q ^ (2:ℕ) * rv)) + ((8 * kp ^
  (2:ℕ) * r ^ (4:ℕ) * P * q ^ (2:ℕ) * rv + 2 * kp ^ (4:ℕ) * w ^ (2:ℕ) * P * q ^ (2:ℕ) * rv) +
  (2 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P * q ^ (2:ℕ) * rv + 2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ)
  * P * q ^ (2:ℕ) * rv)))) + (((kp ^ (5:ℕ) * P ^ (2:ℕ) * q ^ (2:ℕ) * rv + (-10 * kp ^ (4:ℕ) * r
  * P ^ (2:ℕ) * q ^ (2:ℕ) * rv + 7 * kp ^ (3:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ) * q ^ (2:ℕ) * rv)) +
  ((kp ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * q ^ (2:ℕ) * rv + 2 * kp ^ (3:ℕ) * w ^ (2:ℕ) * c * e *
  q ^ (2:ℕ) * rv) + (2 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * c * e * q ^ (2:ℕ) * rv + 2 * kp ^ (3:ℕ) *
  w ^ (2:ℕ) * e * q ^ (3:ℕ) * rv))) + ((8 * kp ^ (4:ℕ) * r ^ (2:ℕ) * c * P * κ * rv + (16 * kp
  ^ (3:ℕ) * r ^ (3:ℕ) * c * P * κ * rv + 8 * kp ^ (2:ℕ) * r ^ (4:ℕ) * c * P * κ * rv)) + ((kp ^
  (4:ℕ) * w ^ (2:ℕ) * c * P * κ * rv - kp ^ (3:ℕ) * r * w ^ (2:ℕ) * c * P * κ * rv) + (-5 * kp
  ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P * κ * rv - 3 * kp * r ^ (3:ℕ) * w ^ (2:ℕ) * c * P * κ
  * rv))))) + ((((8 * kp ^ (4:ℕ) * r * c * P ^ (2:ℕ) * κ * rv + (-2 * kp ^ (3:ℕ) * r ^ (2:ℕ) *
  c * P ^ (2:ℕ) * κ * rv - 10 * kp ^ (2:ℕ) * r ^ (3:ℕ) * c * P ^ (2:ℕ) * κ * rv)) + (-4 * kp ^
  (3:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * κ * rv + (-4 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * c * P ^ (2:ℕ)
  * κ * rv - 2 * kp ^ (3:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * e * κ * rv))) + ((-4 * kp ^ (2:ℕ) * r * w
  ^ (2:ℕ) * c ^ (2:ℕ) * e * κ * rv + (-2 * kp * r ^ (2:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * e * κ * rv
  - 2 * kp ^ (5:ℕ) * r ^ (2:ℕ) * q * κ * rv)) + ((-8 * kp ^ (4:ℕ) * r ^ (3:ℕ) * q * κ * rv - 10
  * kp ^ (3:ℕ) * r ^ (4:ℕ) * q * κ * rv) + (-4 * kp ^ (2:ℕ) * r ^ (5:ℕ) * q * κ * rv - 8 * kp ^
  (4:ℕ) * r * w ^ (2:ℕ) * q * κ * rv)))) + (((-16 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * q * κ
  * rv + (-8 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * q * κ * rv - 16 * kp ^ (4:ℕ) * r ^ (2:ℕ) *
  P * q * κ * rv)) + ((-8 * kp ^ (3:ℕ) * r ^ (3:ℕ) * P * q * κ * rv + 8 * kp ^ (2:ℕ) * r ^
  (4:ℕ) * P * q * κ * rv) + (-kp ^ (4:ℕ) * w ^ (2:ℕ) * P * q * κ * rv + 4 * kp ^ (3:ℕ) * r * w
  ^ (2:ℕ) * P * q * κ * rv))) + ((7 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * q * κ * rv + (2
  * kp ^ (2:ℕ) * w ^ (4:ℕ) * P * q * κ * rv + 2 * kp ^ (5:ℕ) * P ^ (2:ℕ) * q * κ * rv)) + ((-20
  * kp ^ (4:ℕ) * r * P ^ (2:ℕ) * q * κ * rv + 14 * kp ^ (3:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ) * q * κ *
  rv) + (4 * kp ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * q * κ * rv + 8 * kp ^ (3:ℕ) * w ^ (2:ℕ) * c *
  e * q * κ * rv)))))) + (((((8 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * c * e * q * κ * rv + (2 * kp ^
  (3:ℕ) * w ^ (2:ℕ) * e * q ^ (2:ℕ) * κ * rv + kp ^ (5:ℕ) * r ^ (2:ℕ) * κ ^ (2:ℕ) * rv)) + (2 *
  kp ^ (4:ℕ) * r ^ (3:ℕ) * κ ^ (2:ℕ) * rv + (kp ^ (3:ℕ) * r ^ (4:ℕ) * κ ^ (2:ℕ) * rv - kp ^
  (4:ℕ) * r * w ^ (2:ℕ) * κ ^ (2:ℕ) * rv))) + ((-2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * κ ^
  (2:ℕ) * rv + (-kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * κ ^ (2:ℕ) * rv + 2 * kp ^ (5:ℕ) * r * P *
  κ ^ (2:ℕ) * rv)) + ((-8 * kp ^ (4:ℕ) * r ^ (2:ℕ) * P * κ ^ (2:ℕ) * rv - 10 * kp ^ (3:ℕ) * r ^
  (3:ℕ) * P * κ ^ (2:ℕ) * rv) + (kp ^ (5:ℕ) * P ^ (2:ℕ) * κ ^ (2:ℕ) * rv - 10 * kp ^ (4:ℕ) * r
  * P ^ (2:ℕ) * κ ^ (2:ℕ) * rv)))) + (((7 * kp ^ (3:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ) * κ ^ (2:ℕ) * rv
  + (3 * kp ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * κ ^ (2:ℕ) * rv + 6 * kp ^ (3:ℕ) * w ^ (2:ℕ) * c *
  e * κ ^ (2:ℕ) * rv)) + ((6 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * c * e * κ ^ (2:ℕ) * rv - 2 * kp ^
  (3:ℕ) * w ^ (2:ℕ) * e * q * κ ^ (2:ℕ) * rv) + (-2 * kp ^ (3:ℕ) * w ^ (2:ℕ) * e * κ ^ (3:ℕ) *
  rv + 3 * kp ^ (3:ℕ) * r * c ^ (2:ℕ) * P ^ (2:ℕ) * rv ^ (2:ℕ)))) + ((6 * kp ^ (2:ℕ) * r ^
  (2:ℕ) * c ^ (2:ℕ) * P ^ (2:ℕ) * rv ^ (2:ℕ) + (3 * kp * r ^ (3:ℕ) * c ^ (2:ℕ) * P ^ (2:ℕ) * rv
  ^ (2:ℕ) - kp ^ (4:ℕ) * w ^ (2:ℕ) * c * q * rv ^ (2:ℕ))) + ((-4 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) *
  c * q * rv ^ (2:ℕ) - 6 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * q * rv ^ (2:ℕ)) + (-4 * kp
  * r ^ (3:ℕ) * w ^ (2:ℕ) * c * q * rv ^ (2:ℕ) - r ^ (4:ℕ) * w ^ (2:ℕ) * c * q * rv ^
  (2:ℕ)))))) + ((((-2 * kp ^ (4:ℕ) * r * c * P * q * rv ^ (2:ℕ) + (-10 * kp ^ (3:ℕ) * r ^ (2:ℕ)
  * c * P * q * rv ^ (2:ℕ) - 14 * kp ^ (2:ℕ) * r ^ (3:ℕ) * c * P * q * rv ^ (2:ℕ))) + ((-6 * kp
  * r ^ (4:ℕ) * c * P * q * rv ^ (2:ℕ) - 8 * kp ^ (3:ℕ) * w ^ (2:ℕ) * c * P * q * rv ^ (2:ℕ)) +
  (-16 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * c * P * q * rv ^ (2:ℕ) - 8 * kp * r ^ (2:ℕ) * w ^ (2:ℕ) *
  c * P * q * rv ^ (2:ℕ)))) + ((4 * kp ^ (4:ℕ) * c * P ^ (2:ℕ) * q * rv ^ (2:ℕ) + (-10 * kp ^
  (3:ℕ) * r * c * P ^ (2:ℕ) * q * rv ^ (2:ℕ) - 14 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c * P ^ (2:ℕ) * q
  * rv ^ (2:ℕ))) + ((-kp ^ (2:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * q * rv ^ (2:ℕ) + kp ^ (5:ℕ) * r
  * q ^ (2:ℕ) * rv ^ (2:ℕ)) + (6 * kp ^ (4:ℕ) * r ^ (2:ℕ) * q ^ (2:ℕ) * rv ^ (2:ℕ) + 12 * kp ^
  (3:ℕ) * r ^ (3:ℕ) * q ^ (2:ℕ) * rv ^ (2:ℕ))))) + (((10 * kp ^ (2:ℕ) * r ^ (4:ℕ) * q ^ (2:ℕ) *
  rv ^ (2:ℕ) + (3 * kp * r ^ (5:ℕ) * q ^ (2:ℕ) * rv ^ (2:ℕ) + 2 * kp ^ (4:ℕ) * w ^ (2:ℕ) * q ^
  (2:ℕ) * rv ^ (2:ℕ))) + ((6 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * q ^ (2:ℕ) * rv ^ (2:ℕ) + 6 * kp ^
  (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * q ^ (2:ℕ) * rv ^ (2:ℕ)) + (2 * kp * r ^ (3:ℕ) * w ^ (2:ℕ) * q
  ^ (2:ℕ) * rv ^ (2:ℕ) - 2 * kp ^ (5:ℕ) * P * q ^ (2:ℕ) * rv ^ (2:ℕ)))) + ((12 * kp ^ (3:ℕ) * r
  ^ (2:ℕ) * P * q ^ (2:ℕ) * rv ^ (2:ℕ) + (10 * kp ^ (2:ℕ) * r ^ (3:ℕ) * P * q ^ (2:ℕ) * rv ^
  (2:ℕ) - 6 * kp ^ (4:ℕ) * P ^ (2:ℕ) * q ^ (2:ℕ) * rv ^ (2:ℕ))) + ((12 * kp ^ (3:ℕ) * r * P ^
  (2:ℕ) * q ^ (2:ℕ) * rv ^ (2:ℕ) + 4 * kp ^ (4:ℕ) * r * c * P * κ * rv ^ (2:ℕ)) + (8 * kp ^
  (3:ℕ) * r ^ (2:ℕ) * c * P * κ * rv ^ (2:ℕ) + 4 * kp ^ (2:ℕ) * r ^ (3:ℕ) * c * P * κ * rv ^
  (2:ℕ))))))))) + (((((((-2 * kp ^ (3:ℕ) * w ^ (2:ℕ) * c * P * κ * rv ^ (2:ℕ) + (-4 * kp ^
  (2:ℕ) * r * w ^ (2:ℕ) * c * P * κ * rv ^ (2:ℕ) - 2 * kp * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P * κ *
  rv ^ (2:ℕ))) + (4 * kp ^ (4:ℕ) * c * P ^ (2:ℕ) * κ * rv ^ (2:ℕ) + (-10 * kp ^ (3:ℕ) * r * c *
  P ^ (2:ℕ) * κ * rv ^ (2:ℕ) - 14 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c * P ^ (2:ℕ) * κ * rv ^ (2:ℕ))))
  + ((-2 * kp ^ (5:ℕ) * r * q * κ * rv ^ (2:ℕ) + (-6 * kp ^ (4:ℕ) * r ^ (2:ℕ) * q * κ * rv ^
  (2:ℕ) - 6 * kp ^ (3:ℕ) * r ^ (3:ℕ) * q * κ * rv ^ (2:ℕ))) + ((-2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * q
  * κ * rv ^ (2:ℕ) - 2 * kp ^ (5:ℕ) * P * q * κ * rv ^ (2:ℕ)) + (-6 * kp ^ (4:ℕ) * r * P * q *
  κ * rv ^ (2:ℕ) + 6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * P * q * κ * rv ^ (2:ℕ))))) + (((10 * kp ^ (2:ℕ)
  * r ^ (3:ℕ) * P * q * κ * rv ^ (2:ℕ) + (4 * kp ^ (3:ℕ) * w ^ (2:ℕ) * P * q * κ * rv ^ (2:ℕ) +
  4 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * P * q * κ * rv ^ (2:ℕ))) + ((-12 * kp ^ (4:ℕ) * P ^ (2:ℕ) *
  q * κ * rv ^ (2:ℕ) + 24 * kp ^ (3:ℕ) * r * P ^ (2:ℕ) * q * κ * rv ^ (2:ℕ)) + (-6 * kp ^ (4:ℕ)
  * r * P * κ ^ (2:ℕ) * rv ^ (2:ℕ) - 6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * P * κ ^ (2:ℕ) * rv ^ (2:ℕ))))
  + ((-6 * kp ^ (4:ℕ) * P ^ (2:ℕ) * κ ^ (2:ℕ) * rv ^ (2:ℕ) + (12 * kp ^ (3:ℕ) * r * P ^ (2:ℕ) *
  κ ^ (2:ℕ) * rv ^ (2:ℕ) + kp ^ (3:ℕ) * c ^ (2:ℕ) * P ^ (2:ℕ) * rv ^ (3:ℕ))) + ((2 * kp ^ (2:ℕ)
  * r * c ^ (2:ℕ) * P ^ (2:ℕ) * rv ^ (3:ℕ) + kp * r ^ (2:ℕ) * c ^ (2:ℕ) * P ^ (2:ℕ) * rv ^
  (3:ℕ)) + (-2 * kp ^ (4:ℕ) * c * P * q * rv ^ (3:ℕ) - 6 * kp ^ (3:ℕ) * r * c * P * q * rv ^
  (3:ℕ)))))) + ((((-6 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c * P * q * rv ^ (3:ℕ) + (-2 * kp * r ^ (3:ℕ)
  * c * P * q * rv ^ (3:ℕ) - 6 * kp ^ (3:ℕ) * c * P ^ (2:ℕ) * q * rv ^ (3:ℕ))) + (-6 * kp ^
  (2:ℕ) * r * c * P ^ (2:ℕ) * q * rv ^ (3:ℕ) + (kp ^ (5:ℕ) * q ^ (2:ℕ) * rv ^ (3:ℕ) + 4 * kp ^
  (4:ℕ) * r * q ^ (2:ℕ) * rv ^ (3:ℕ)))) + ((6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * q ^ (2:ℕ) * rv ^ (3:ℕ)
  + (4 * kp ^ (2:ℕ) * r ^ (3:ℕ) * q ^ (2:ℕ) * rv ^ (3:ℕ) + kp * r ^ (4:ℕ) * q ^ (2:ℕ) * rv ^
  (3:ℕ))) + ((4 * kp ^ (4:ℕ) * P * q ^ (2:ℕ) * rv ^ (3:ℕ) + 8 * kp ^ (3:ℕ) * r * P * q ^ (2:ℕ)
  * rv ^ (3:ℕ)) + (4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * P * q ^ (2:ℕ) * rv ^ (3:ℕ) + 6 * kp ^ (3:ℕ) * P
  ^ (2:ℕ) * q ^ (2:ℕ) * rv ^ (3:ℕ))))) + (((-6 * kp ^ (3:ℕ) * c * P ^ (2:ℕ) * κ * rv ^ (3:ℕ) +
  (-6 * kp ^ (2:ℕ) * r * c * P ^ (2:ℕ) * κ * rv ^ (3:ℕ) + 4 * kp ^ (4:ℕ) * P * q * κ * rv ^
  (3:ℕ))) + ((8 * kp ^ (3:ℕ) * r * P * q * κ * rv ^ (3:ℕ) + 4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * P * q
  * κ * rv ^ (3:ℕ)) + (12 * kp ^ (3:ℕ) * P ^ (2:ℕ) * q * κ * rv ^ (3:ℕ) + 6 * kp ^ (3:ℕ) * P ^
  (2:ℕ) * κ ^ (2:ℕ) * rv ^ (3:ℕ)))) + ((2 * kp ^ (3:ℕ) * r * w * c ^ (2:ℕ) * P ^ (2:ℕ) * xv +
  (4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * c ^ (2:ℕ) * P ^ (2:ℕ) * xv + 2 * kp * r ^ (3:ℕ) * w * c ^
  (2:ℕ) * P ^ (2:ℕ) * xv)) + ((-2 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w * c * q * xv + 6 * kp ^ (2:ℕ) *
  r ^ (4:ℕ) * w * c * q * xv) + (4 * kp * r ^ (5:ℕ) * w * c * q * xv + 6 * kp ^ (3:ℕ) * r * w ^
  (3:ℕ) * c * q * xv)))))) + (((((10 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * c * q * xv + (2 *
  kp * r ^ (3:ℕ) * w ^ (3:ℕ) * c * q * xv - 2 * r ^ (4:ℕ) * w ^ (3:ℕ) * c * q * xv)) + (-2 * kp
  ^ (2:ℕ) * w ^ (5:ℕ) * c * q * xv + (-4 * kp * r * w ^ (5:ℕ) * c * q * xv - 2 * r ^ (2:ℕ) * w
  ^ (5:ℕ) * c * q * xv))) + ((-9 * kp ^ (4:ℕ) * r * w * c * P * q * xv + (-17 * kp ^ (3:ℕ) * r
  ^ (2:ℕ) * w * c * P * q * xv - 15 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w * c * P * q * xv)) + ((-7 * kp
  * r ^ (4:ℕ) * w * c * P * q * xv - 9 * kp ^ (3:ℕ) * w ^ (3:ℕ) * c * P * q * xv) + (-22 * kp ^
  (2:ℕ) * r * w ^ (3:ℕ) * c * P * q * xv - 13 * kp * r ^ (2:ℕ) * w ^ (3:ℕ) * c * P * q * xv))))
  + (((-2 * kp ^ (4:ℕ) * w * c * P ^ (2:ℕ) * q * xv + (-4 * kp ^ (3:ℕ) * r * w * c * P ^ (2:ℕ)
  * q * xv - 4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * c * P ^ (2:ℕ) * q * xv)) + ((3 * kp ^ (3:ℕ) * r *
  w * c ^ (2:ℕ) * e * q * xv + 6 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * c ^ (2:ℕ) * e * q * xv) + (3 *
  kp * r ^ (3:ℕ) * w * c ^ (2:ℕ) * e * q * xv - 4 * kp ^ (2:ℕ) * w ^ (3:ℕ) * c ^ (2:ℕ) * e * q
  * xv))) + ((-4 * kp * r * w ^ (3:ℕ) * c ^ (2:ℕ) * e * q * xv + (6 * kp ^ (4:ℕ) * r ^ (2:ℕ) *
  w * q ^ (2:ℕ) * xv + 10 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w * q ^ (2:ℕ) * xv)) + ((6 * kp ^ (2:ℕ) *
  r ^ (4:ℕ) * w * q ^ (2:ℕ) * xv + 2 * kp * r ^ (5:ℕ) * w * q ^ (2:ℕ) * xv) + (10 * kp ^ (3:ℕ)
  * r * w ^ (3:ℕ) * q ^ (2:ℕ) * xv + 12 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * q ^ (2:ℕ) *
  xv))))) + ((((2 * kp * r ^ (3:ℕ) * w ^ (3:ℕ) * q ^ (2:ℕ) * xv + (15 * kp ^ (4:ℕ) * r * w * P
  * q ^ (2:ℕ) * xv + 18 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w * P * q ^ (2:ℕ) * xv)) + ((7 * kp ^ (2:ℕ)
  * r ^ (3:ℕ) * w * P * q ^ (2:ℕ) * xv - kp ^ (3:ℕ) * w ^ (3:ℕ) * P * q ^ (2:ℕ) * xv) + (-3 *
  kp ^ (2:ℕ) * r * w ^ (3:ℕ) * P * q ^ (2:ℕ) * xv + 2 * kp ^ (3:ℕ) * r * w * P ^ (2:ℕ) * q ^
  (2:ℕ) * xv))) + ((-6 * kp ^ (3:ℕ) * r * w * c * e * q ^ (2:ℕ) * xv + (-6 * kp ^ (2:ℕ) * r ^
  (2:ℕ) * w * c * e * q ^ (2:ℕ) * xv - 6 * kp ^ (2:ℕ) * w ^ (3:ℕ) * c * e * q ^ (2:ℕ) * xv)) +
  ((5 * kp ^ (3:ℕ) * r * w * e * q ^ (3:ℕ) * xv + 5 * kp ^ (4:ℕ) * r * w * c * P * κ * xv) +
  (11 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w * c * P * κ * xv + 7 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w * c * P *
  κ * xv)))) + (((kp * r ^ (4:ℕ) * w * c * P * κ * xv + (-2 * kp ^ (3:ℕ) * w ^ (3:ℕ) * c * P *
  κ * xv - 4 * kp ^ (2:ℕ) * r * w ^ (3:ℕ) * c * P * κ * xv)) + ((-2 * kp * r ^ (2:ℕ) * w ^
  (3:ℕ) * c * P * κ * xv + 4 * kp ^ (4:ℕ) * w * c * P ^ (2:ℕ) * κ * xv) + (-4 * kp ^ (2:ℕ) * r
  ^ (2:ℕ) * w * c * P ^ (2:ℕ) * κ * xv + kp ^ (3:ℕ) * r * w * c ^ (2:ℕ) * e * κ * xv))) + ((2 *
  kp ^ (2:ℕ) * r ^ (2:ℕ) * w * c ^ (2:ℕ) * e * κ * xv + (kp * r ^ (3:ℕ) * w * c ^ (2:ℕ) * e * κ
  * xv - 2 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w * q * κ * xv)) + ((-8 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w * q
  * κ * xv - 6 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w * q * κ * xv) + (-4 * kp ^ (3:ℕ) * r * w ^ (3:ℕ) *
  q * κ * xv - 4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (3:ℕ) * q * κ * xv))))))) + ((((((6 * kp ^
  (4:ℕ) * r * w * P * q * κ * xv + (12 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w * P * q * κ * xv + 10 * kp
  ^ (2:ℕ) * r ^ (3:ℕ) * w * P * q * κ * xv)) + (-kp ^ (3:ℕ) * w ^ (3:ℕ) * P * q * κ * xv + (3 *
  kp ^ (2:ℕ) * r * w ^ (3:ℕ) * P * q * κ * xv - 4 * kp ^ (4:ℕ) * w * P ^ (2:ℕ) * q * κ * xv)))
  + ((4 * kp ^ (3:ℕ) * r * w * P ^ (2:ℕ) * q * κ * xv + (-8 * kp ^ (3:ℕ) * r * w * c * e * q *
  κ * xv - 8 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * c * e * q * κ * xv)) + ((11 * kp ^ (3:ℕ) * r * w *
  e * q ^ (2:ℕ) * κ * xv - 3 * kp ^ (4:ℕ) * r * w * P * κ ^ (2:ℕ) * xv) + (-2 * kp ^ (3:ℕ) * r
  ^ (2:ℕ) * w * P * κ ^ (2:ℕ) * xv + kp ^ (2:ℕ) * r ^ (3:ℕ) * w * P * κ ^ (2:ℕ) * xv)))) +
  (((-4 * kp ^ (4:ℕ) * w * P ^ (2:ℕ) * κ ^ (2:ℕ) * xv + (2 * kp ^ (3:ℕ) * r * w * P ^ (2:ℕ) * κ
  ^ (2:ℕ) * xv - 2 * kp ^ (3:ℕ) * r * w * c * e * κ ^ (2:ℕ) * xv)) + ((-2 * kp ^ (2:ℕ) * r ^
  (2:ℕ) * w * c * e * κ ^ (2:ℕ) * xv + 7 * kp ^ (3:ℕ) * r * w * e * q * κ ^ (2:ℕ) * xv) + (kp ^
  (3:ℕ) * r * w * e * κ ^ (3:ℕ) * xv + 2 * kp ^ (3:ℕ) * w * c ^ (2:ℕ) * P ^ (2:ℕ) * rv * xv)))
  + ((4 * kp ^ (2:ℕ) * r * w * c ^ (2:ℕ) * P ^ (2:ℕ) * rv * xv + (2 * kp * r ^ (2:ℕ) * w * c ^
  (2:ℕ) * P ^ (2:ℕ) * rv * xv + 4 * kp ^ (4:ℕ) * r * w * c * q * rv * xv)) + ((12 * kp ^ (3:ℕ)
  * r ^ (2:ℕ) * w * c * q * rv * xv + 12 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w * c * q * rv * xv) + (4 *
  kp * r ^ (4:ℕ) * w * c * q * rv * xv - 2 * kp ^ (3:ℕ) * w ^ (3:ℕ) * c * q * rv * xv))))) +
  ((((-6 * kp ^ (2:ℕ) * r * w ^ (3:ℕ) * c * q * rv * xv + (-6 * kp * r ^ (2:ℕ) * w ^ (3:ℕ) * c
  * q * rv * xv - 2 * r ^ (3:ℕ) * w ^ (3:ℕ) * c * q * rv * xv)) + (-kp ^ (4:ℕ) * w * c * P * q
  * rv * xv + (-7 * kp ^ (3:ℕ) * r * w * c * P * q * rv * xv - 19 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w
  * c * P * q * rv * xv))) + ((-13 * kp * r ^ (3:ℕ) * w * c * P * q * rv * xv + (-4 * kp ^
  (2:ℕ) * w ^ (3:ℕ) * c * P * q * rv * xv - 4 * kp * r * w ^ (3:ℕ) * c * P * q * rv * xv)) +
  ((-4 * kp ^ (2:ℕ) * r * w * c * P ^ (2:ℕ) * q * rv * xv + 2 * kp ^ (3:ℕ) * w * c ^ (2:ℕ) * e
  * q * rv * xv) + (4 * kp ^ (2:ℕ) * r * w * c ^ (2:ℕ) * e * q * rv * xv + 2 * kp * r ^ (2:ℕ) *
  w * c ^ (2:ℕ) * e * q * rv * xv)))) + (((4 * kp ^ (4:ℕ) * r * w * q ^ (2:ℕ) * rv * xv + (12 *
  kp ^ (3:ℕ) * r ^ (2:ℕ) * w * q ^ (2:ℕ) * rv * xv + 12 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w * q ^
  (2:ℕ) * rv * xv)) + ((4 * kp * r ^ (4:ℕ) * w * q ^ (2:ℕ) * rv * xv + 2 * kp ^ (3:ℕ) * w ^
  (3:ℕ) * q ^ (2:ℕ) * rv * xv) + (4 * kp ^ (2:ℕ) * r * w ^ (3:ℕ) * q ^ (2:ℕ) * rv * xv + 2 * kp
  * r ^ (2:ℕ) * w ^ (3:ℕ) * q ^ (2:ℕ) * rv * xv))) + ((11 * kp ^ (4:ℕ) * w * P * q ^ (2:ℕ) * rv
  * xv + (10 * kp ^ (3:ℕ) * r * w * P * q ^ (2:ℕ) * rv * xv + 3 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w *
  P * q ^ (2:ℕ) * rv * xv)) + ((-2 * kp ^ (2:ℕ) * w ^ (3:ℕ) * P * q ^ (2:ℕ) * rv * xv + 2 * kp
  ^ (3:ℕ) * w * P ^ (2:ℕ) * q ^ (2:ℕ) * rv * xv) + (-4 * kp ^ (3:ℕ) * w * c * e * q ^ (2:ℕ) *
  rv * xv - 4 * kp ^ (2:ℕ) * r * w * c * e * q ^ (2:ℕ) * rv * xv)))))) + (((((4 * kp ^ (3:ℕ) *
  w * e * q ^ (3:ℕ) * rv * xv + (kp ^ (4:ℕ) * w * c * P * κ * rv * xv + 3 * kp ^ (3:ℕ) * r * w
  * c * P * κ * rv * xv)) + (3 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * c * P * κ * rv * xv + (kp * r ^
  (3:ℕ) * w * c * P * κ * rv * xv - 8 * kp ^ (3:ℕ) * w * c * P ^ (2:ℕ) * κ * rv * xv))) + ((-8
  * kp ^ (2:ℕ) * r * w * c * P ^ (2:ℕ) * κ * rv * xv + (-6 * kp ^ (4:ℕ) * r * w * q * κ * rv *
  xv - 12 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w * q * κ * rv * xv)) + ((-6 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w
  * q * κ * rv * xv + 6 * kp ^ (4:ℕ) * w * P * q * κ * rv * xv) + (16 * kp ^ (3:ℕ) * r * w * P
  * q * κ * rv * xv + 14 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * P * q * κ * rv * xv)))) + (((4 * kp ^
  (2:ℕ) * w ^ (3:ℕ) * P * q * κ * rv * xv + (8 * kp ^ (3:ℕ) * w * P ^ (2:ℕ) * q * κ * rv * xv -
  4 * kp ^ (3:ℕ) * w * c * e * q * κ * rv * xv)) + ((-4 * kp ^ (2:ℕ) * r * w * c * e * q * κ *
  rv * xv + 8 * kp ^ (3:ℕ) * w * e * q ^ (2:ℕ) * κ * rv * xv) + (kp ^ (4:ℕ) * w * P * κ ^ (2:ℕ)
  * rv * xv + 2 * kp ^ (3:ℕ) * r * w * P * κ ^ (2:ℕ) * rv * xv))) + ((kp ^ (2:ℕ) * r ^ (2:ℕ) *
  w * P * κ ^ (2:ℕ) * rv * xv + (6 * kp ^ (3:ℕ) * w * P ^ (2:ℕ) * κ ^ (2:ℕ) * rv * xv + 4 * kp
  ^ (3:ℕ) * w * e * q * κ ^ (2:ℕ) * rv * xv)) + ((-6 * kp ^ (3:ℕ) * w * c * P * q * rv ^ (2:ℕ)
  * xv - 12 * kp ^ (2:ℕ) * r * w * c * P * q * rv ^ (2:ℕ) * xv) + (-6 * kp * r ^ (2:ℕ) * w * c
  * P * q * rv ^ (2:ℕ) * xv - 2 * kp ^ (2:ℕ) * w * c * P ^ (2:ℕ) * q * rv ^ (2:ℕ) * xv))))) +
  ((((2 * kp ^ (4:ℕ) * w * q ^ (2:ℕ) * rv ^ (2:ℕ) * xv + (6 * kp ^ (3:ℕ) * r * w * q ^ (2:ℕ) *
  rv ^ (2:ℕ) * xv + 6 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * q ^ (2:ℕ) * rv ^ (2:ℕ) * xv)) + ((2 * kp *
  r ^ (3:ℕ) * w * q ^ (2:ℕ) * rv ^ (2:ℕ) * xv - 4 * kp ^ (3:ℕ) * w * P * q ^ (2:ℕ) * rv ^ (2:ℕ)
  * xv) + (-4 * kp ^ (2:ℕ) * r * w * P * q ^ (2:ℕ) * rv ^ (2:ℕ) * xv + 4 * kp ^ (3:ℕ) * w * P *
  q * κ * rv ^ (2:ℕ) * xv))) + ((4 * kp ^ (2:ℕ) * r * w * P * q * κ * rv ^ (2:ℕ) * xv + (kp ^
  (3:ℕ) * r * c ^ (2:ℕ) * P ^ (2:ℕ) * xv ^ (2:ℕ) + 2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c ^ (2:ℕ) * P ^
  (2:ℕ) * xv ^ (2:ℕ))) + ((kp * r ^ (3:ℕ) * c ^ (2:ℕ) * P ^ (2:ℕ) * xv ^ (2:ℕ) - 3 * kp ^ (4:ℕ)
  * r ^ (2:ℕ) * c * q * xv ^ (2:ℕ)) + (-6 * kp ^ (3:ℕ) * r ^ (3:ℕ) * c * q * xv ^ (2:ℕ) - 3 *
  kp ^ (2:ℕ) * r ^ (4:ℕ) * c * q * xv ^ (2:ℕ))))) + (((4 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * c * q *
  xv ^ (2:ℕ) + (8 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * q * xv ^ (2:ℕ) + 4 * kp * r ^
  (3:ℕ) * w ^ (2:ℕ) * c * q * xv ^ (2:ℕ))) + ((-kp ^ (2:ℕ) * w ^ (4:ℕ) * c * q * xv ^ (2:ℕ) - 2
  * kp * r * w ^ (4:ℕ) * c * q * xv ^ (2:ℕ)) + (-r ^ (2:ℕ) * w ^ (4:ℕ) * c * q * xv ^ (2:ℕ) - 7
  * kp ^ (4:ℕ) * r * c * P * q * xv ^ (2:ℕ)))) + ((-13 * kp ^ (3:ℕ) * r ^ (2:ℕ) * c * P * q *
  xv ^ (2:ℕ) + (-9 * kp ^ (2:ℕ) * r ^ (3:ℕ) * c * P * q * xv ^ (2:ℕ) - 3 * kp * r ^ (4:ℕ) * c *
  P * q * xv ^ (2:ℕ))) + ((-12 * kp ^ (3:ℕ) * w ^ (2:ℕ) * c * P * q * xv ^ (2:ℕ) - 26 * kp ^
  (2:ℕ) * r * w ^ (2:ℕ) * c * P * q * xv ^ (2:ℕ)) + (-14 * kp * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P *
  q * xv ^ (2:ℕ) - kp ^ (4:ℕ) * c * P ^ (2:ℕ) * q * xv ^ (2:ℕ)))))))))) + ((((((((-2 * kp ^
  (3:ℕ) * r * c * P ^ (2:ℕ) * q * xv ^ (2:ℕ) + (-2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c * P ^ (2:ℕ) * q
  * xv ^ (2:ℕ) - 2 * kp ^ (2:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * e * q * xv ^ (2:ℕ))) + (-2 * kp * r *
  w ^ (2:ℕ) * c ^ (2:ℕ) * e * q * xv ^ (2:ℕ) + (5 * kp ^ (4:ℕ) * r ^ (2:ℕ) * q ^ (2:ℕ) * xv ^
  (2:ℕ) + 8 * kp ^ (3:ℕ) * r ^ (3:ℕ) * q ^ (2:ℕ) * xv ^ (2:ℕ)))) + ((3 * kp ^ (2:ℕ) * r ^ (4:ℕ)
  * q ^ (2:ℕ) * xv ^ (2:ℕ) + (11 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * q ^ (2:ℕ) * xv ^ (2:ℕ) + 12 *
  kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * q ^ (2:ℕ) * xv ^ (2:ℕ))) + ((kp * r ^ (3:ℕ) * w ^ (2:ℕ)
  * q ^ (2:ℕ) * xv ^ (2:ℕ) + 10 * kp ^ (4:ℕ) * r * P * q ^ (2:ℕ) * xv ^ (2:ℕ)) + (12 * kp ^
  (3:ℕ) * r ^ (2:ℕ) * P * q ^ (2:ℕ) * xv ^ (2:ℕ) + 4 * kp ^ (2:ℕ) * r ^ (3:ℕ) * P * q ^ (2:ℕ) *
  xv ^ (2:ℕ))))) + (((-5 * kp ^ (3:ℕ) * w ^ (2:ℕ) * P * q ^ (2:ℕ) * xv ^ (2:ℕ) + (-9 * kp ^
  (2:ℕ) * r * w ^ (2:ℕ) * P * q ^ (2:ℕ) * xv ^ (2:ℕ) + kp ^ (3:ℕ) * r * P ^ (2:ℕ) * q ^ (2:ℕ) *
  xv ^ (2:ℕ))) + ((-6 * kp ^ (2:ℕ) * w ^ (2:ℕ) * c * e * q ^ (2:ℕ) * xv ^ (2:ℕ) + 2 * kp ^
  (4:ℕ) * r * c * P * κ * xv ^ (2:ℕ)) + (4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * c * P * κ * xv ^ (2:ℕ) +
  2 * kp ^ (2:ℕ) * r ^ (3:ℕ) * c * P * κ * xv ^ (2:ℕ)))) + ((-kp ^ (3:ℕ) * w ^ (2:ℕ) * c * P *
  κ * xv ^ (2:ℕ) + (-2 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * c * P * κ * xv ^ (2:ℕ) - kp * r ^ (2:ℕ) *
  w ^ (2:ℕ) * c * P * κ * xv ^ (2:ℕ))) + ((2 * kp ^ (4:ℕ) * c * P ^ (2:ℕ) * κ * xv ^ (2:ℕ) - 2
  * kp ^ (2:ℕ) * r ^ (2:ℕ) * c * P ^ (2:ℕ) * κ * xv ^ (2:ℕ)) + (2 * kp ^ (4:ℕ) * r ^ (2:ℕ) * q
  * κ * xv ^ (2:ℕ) + 2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * q * κ * xv ^ (2:ℕ)))))) + ((((-2 * kp ^ (3:ℕ)
  * r * w ^ (2:ℕ) * q * κ * xv ^ (2:ℕ) + (-2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * q * κ * xv
  ^ (2:ℕ) + 5 * kp ^ (4:ℕ) * r * P * q * κ * xv ^ (2:ℕ))) + (8 * kp ^ (3:ℕ) * r ^ (2:ℕ) * P * q
  * κ * xv ^ (2:ℕ) + (5 * kp ^ (2:ℕ) * r ^ (3:ℕ) * P * q * κ * xv ^ (2:ℕ) + kp ^ (3:ℕ) * w ^
  (2:ℕ) * P * q * κ * xv ^ (2:ℕ)))) + ((3 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * P * q * κ * xv ^ (2:ℕ)
  + (-2 * kp ^ (4:ℕ) * P ^ (2:ℕ) * q * κ * xv ^ (2:ℕ) + 2 * kp ^ (3:ℕ) * r * P ^ (2:ℕ) * q * κ
  * xv ^ (2:ℕ))) + ((-2 * kp ^ (4:ℕ) * r * P * κ ^ (2:ℕ) * xv ^ (2:ℕ) - 2 * kp ^ (3:ℕ) * r ^
  (2:ℕ) * P * κ ^ (2:ℕ) * xv ^ (2:ℕ)) + (-2 * kp ^ (4:ℕ) * P ^ (2:ℕ) * κ ^ (2:ℕ) * xv ^ (2:ℕ) +
  kp ^ (3:ℕ) * r * P ^ (2:ℕ) * κ ^ (2:ℕ) * xv ^ (2:ℕ))))) + (((kp ^ (3:ℕ) * c ^ (2:ℕ) * P ^
  (2:ℕ) * rv * xv ^ (2:ℕ) + (2 * kp ^ (2:ℕ) * r * c ^ (2:ℕ) * P ^ (2:ℕ) * rv * xv ^ (2:ℕ) + kp
  * r ^ (2:ℕ) * c ^ (2:ℕ) * P ^ (2:ℕ) * rv * xv ^ (2:ℕ))) + ((-3 * kp ^ (4:ℕ) * c * P * q * rv
  * xv ^ (2:ℕ) - 5 * kp ^ (3:ℕ) * r * c * P * q * rv * xv ^ (2:ℕ)) + (-5 * kp ^ (2:ℕ) * r ^
  (2:ℕ) * c * P * q * rv * xv ^ (2:ℕ) - 3 * kp * r ^ (3:ℕ) * c * P * q * rv * xv ^ (2:ℕ)))) +
  ((-2 * kp ^ (2:ℕ) * w ^ (2:ℕ) * c * P * q * rv * xv ^ (2:ℕ) + (-2 * kp * r * w ^ (2:ℕ) * c *
  P * q * rv * xv ^ (2:ℕ) - 2 * kp ^ (2:ℕ) * r * c * P ^ (2:ℕ) * q * rv * xv ^ (2:ℕ))) + ((3 *
  kp ^ (4:ℕ) * r * q ^ (2:ℕ) * rv * xv ^ (2:ℕ) + 6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * q ^ (2:ℕ) * rv *
  xv ^ (2:ℕ)) + (3 * kp ^ (2:ℕ) * r ^ (3:ℕ) * q ^ (2:ℕ) * rv * xv ^ (2:ℕ) + kp ^ (3:ℕ) * w ^
  (2:ℕ) * q ^ (2:ℕ) * rv * xv ^ (2:ℕ))))))) + (((((2 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * q ^ (2:ℕ) *
  rv * xv ^ (2:ℕ) + (kp * r ^ (2:ℕ) * w ^ (2:ℕ) * q ^ (2:ℕ) * rv * xv ^ (2:ℕ) + 8 * kp ^ (4:ℕ)
  * P * q ^ (2:ℕ) * rv * xv ^ (2:ℕ))) + (6 * kp ^ (3:ℕ) * r * P * q ^ (2:ℕ) * rv * xv ^ (2:ℕ) +
  (-4 * kp ^ (2:ℕ) * w ^ (2:ℕ) * P * q ^ (2:ℕ) * rv * xv ^ (2:ℕ) + kp ^ (3:ℕ) * P ^ (2:ℕ) * q ^
  (2:ℕ) * rv * xv ^ (2:ℕ)))) + ((-4 * kp ^ (3:ℕ) * c * P ^ (2:ℕ) * κ * rv * xv ^ (2:ℕ) + (-4 *
  kp ^ (2:ℕ) * r * c * P ^ (2:ℕ) * κ * rv * xv ^ (2:ℕ) + 5 * kp ^ (4:ℕ) * P * q * κ * rv * xv ^
  (2:ℕ))) + ((8 * kp ^ (3:ℕ) * r * P * q * κ * rv * xv ^ (2:ℕ) + 5 * kp ^ (2:ℕ) * r ^ (2:ℕ) * P
  * q * κ * rv * xv ^ (2:ℕ)) + (2 * kp ^ (2:ℕ) * w ^ (2:ℕ) * P * q * κ * rv * xv ^ (2:ℕ) + 4 *
  kp ^ (3:ℕ) * P ^ (2:ℕ) * q * κ * rv * xv ^ (2:ℕ))))) + (((3 * kp ^ (3:ℕ) * P ^ (2:ℕ) * κ ^
  (2:ℕ) * rv * xv ^ (2:ℕ) + (-kp ^ (2:ℕ) * c * P ^ (2:ℕ) * q * rv ^ (2:ℕ) * xv ^ (2:ℕ) - 4 * kp
  ^ (3:ℕ) * P * q ^ (2:ℕ) * rv ^ (2:ℕ) * xv ^ (2:ℕ))) + ((-4 * kp ^ (2:ℕ) * r * P * q ^ (2:ℕ) *
  rv ^ (2:ℕ) * xv ^ (2:ℕ) - 5 * kp ^ (3:ℕ) * w * c * P * q * xv ^ (3:ℕ)) + (-10 * kp ^ (2:ℕ) *
  r * w * c * P * q * xv ^ (3:ℕ) - 5 * kp * r ^ (2:ℕ) * w * c * P * q * xv ^ (3:ℕ)))) + ((4 *
  kp ^ (3:ℕ) * r * w * q ^ (2:ℕ) * xv ^ (3:ℕ) + (4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * q ^ (2:ℕ) *
  xv ^ (3:ℕ) - 7 * kp ^ (3:ℕ) * w * P * q ^ (2:ℕ) * xv ^ (3:ℕ))) + ((-9 * kp ^ (2:ℕ) * r * w *
  P * q ^ (2:ℕ) * xv ^ (3:ℕ) - 2 * kp ^ (2:ℕ) * w * c * e * q ^ (2:ℕ) * xv ^ (3:ℕ)) + (kp ^
  (3:ℕ) * w * P * q * κ * xv ^ (3:ℕ) + kp ^ (2:ℕ) * r * w * P * q * κ * xv ^ (3:ℕ)))))) +
  ((((-2 * kp ^ (2:ℕ) * w * P * q ^ (2:ℕ) * rv * xv ^ (3:ℕ) + (-3 * kp ^ (3:ℕ) * P * q ^ (2:ℕ)
  * xv ^ (4:ℕ) - 3 * kp ^ (2:ℕ) * r * P * q ^ (2:ℕ) * xv ^ (4:ℕ))) + ((-kp ^ (3:ℕ) * r * w ^
  (2:ℕ) * c ^ (2:ℕ) * q + 3 * kp * r ^ (3:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * q) + (2 * r ^ (4:ℕ) * w
  ^ (2:ℕ) * c ^ (2:ℕ) * q + 2 * kp ^ (2:ℕ) * w ^ (4:ℕ) * c ^ (2:ℕ) * q))) + ((4 * kp * r * w ^
  (4:ℕ) * c ^ (2:ℕ) * q + (2 * r ^ (2:ℕ) * w ^ (4:ℕ) * c ^ (2:ℕ) * q + 2 * kp ^ (3:ℕ) * r ^
  (2:ℕ) * c ^ (2:ℕ) * P * q)) + ((4 * kp ^ (2:ℕ) * r ^ (3:ℕ) * c ^ (2:ℕ) * P * q + 2 * kp * r ^
  (4:ℕ) * c ^ (2:ℕ) * P * q) + (-2 * kp ^ (3:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * P * q - 2 * kp ^
  (2:ℕ) * r * w ^ (2:ℕ) * c ^ (2:ℕ) * P * q)))) + (((-2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * c * q ^
  (2:ℕ) + (-4 * kp ^ (2:ℕ) * r ^ (4:ℕ) * c * q ^ (2:ℕ) - 2 * kp * r ^ (5:ℕ) * c * q ^ (2:ℕ))) +
  ((-4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * q ^ (2:ℕ) - 4 * kp * r ^ (3:ℕ) * w ^ (2:ℕ) *
  c * q ^ (2:ℕ)) + (2 * kp ^ (2:ℕ) * w ^ (4:ℕ) * c * q ^ (2:ℕ) + 2 * kp * r * w ^ (4:ℕ) * c * q
  ^ (2:ℕ)))) + ((2 * kp ^ (4:ℕ) * r * c * P * q ^ (2:ℕ) + (-2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * c * P
  * q ^ (2:ℕ) - 4 * kp ^ (2:ℕ) * r ^ (3:ℕ) * c * P * q ^ (2:ℕ))) + ((2 * kp ^ (3:ℕ) * w ^ (2:ℕ)
  * c * P * q ^ (2:ℕ) + 2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * q ^ (3:ℕ)) + (2 * kp ^ (2:ℕ) * r ^ (4:ℕ) *
  q ^ (3:ℕ) - 3 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * q ^ (3:ℕ)))))))) + ((((((-2 * kp ^ (2:ℕ) * r ^
  (2:ℕ) * w ^ (2:ℕ) * q ^ (3:ℕ) + (-2 * kp ^ (4:ℕ) * r * P * q ^ (3:ℕ) + 2 * kp ^ (3:ℕ) * r ^
  (2:ℕ) * P * q ^ (3:ℕ))) + (2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * c ^ (2:ℕ) * P * κ + (4 * kp ^ (2:ℕ) *
  r ^ (3:ℕ) * c ^ (2:ℕ) * P * κ + 2 * kp * r ^ (4:ℕ) * c ^ (2:ℕ) * P * κ))) + ((kp ^ (3:ℕ) * w
  ^ (2:ℕ) * c ^ (2:ℕ) * P * κ + (2 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * c ^ (2:ℕ) * P * κ + kp * r ^
  (2:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * P * κ)) + ((2 * kp ^ (4:ℕ) * r ^ (2:ℕ) * c * q * κ + 2 * kp ^
  (3:ℕ) * r ^ (3:ℕ) * c * q * κ) + (-2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * c * q * κ - 2 * kp * r ^
  (5:ℕ) * c * q * κ)))) + (((-4 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * c * q * κ + (-12 * kp ^ (2:ℕ) *
  r ^ (2:ℕ) * w ^ (2:ℕ) * c * q * κ - 8 * kp * r ^ (3:ℕ) * w ^ (2:ℕ) * c * q * κ)) + ((-2 * kp
  ^ (2:ℕ) * w ^ (4:ℕ) * c * q * κ - 2 * kp * r * w ^ (4:ℕ) * c * q * κ) + (4 * kp ^ (4:ℕ) * r *
  c * P * q * κ - 4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * c * P * q * κ))) + ((-8 * kp ^ (2:ℕ) * r ^ (3:ℕ)
  * c * P * q * κ + (-2 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * c * P * q * κ - 2 * kp ^ (4:ℕ) * r ^
  (2:ℕ) * q ^ (2:ℕ) * κ)) + ((2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * q ^ (2:ℕ) * κ + 4 * kp ^ (2:ℕ) * r ^
  (4:ℕ) * q ^ (2:ℕ) * κ) + (-2 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * q ^ (2:ℕ) * κ - 6 * kp ^ (4:ℕ) *
  r * P * q ^ (2:ℕ) * κ))))) + ((((6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * P * q ^ (2:ℕ) * κ + (kp ^ (3:ℕ)
  * w ^ (2:ℕ) * P * q ^ (2:ℕ) * κ + 2 * kp ^ (4:ℕ) * r ^ (2:ℕ) * c * κ ^ (2:ℕ))) + (4 * kp ^
  (3:ℕ) * r ^ (3:ℕ) * c * κ ^ (2:ℕ) + (2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * c * κ ^ (2:ℕ) - kp ^ (3:ℕ)
  * r * w ^ (2:ℕ) * c * κ ^ (2:ℕ)))) + ((-2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * κ ^
  (2:ℕ) + (-kp * r ^ (3:ℕ) * w ^ (2:ℕ) * c * κ ^ (2:ℕ) + 2 * kp ^ (4:ℕ) * r * c * P * κ ^
  (2:ℕ))) + ((-2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * c * P * κ ^ (2:ℕ) - 4 * kp ^ (2:ℕ) * r ^ (3:ℕ) * c
  * P * κ ^ (2:ℕ)) + (-2 * kp ^ (3:ℕ) * w ^ (2:ℕ) * c * P * κ ^ (2:ℕ) - 2 * kp ^ (2:ℕ) * r * w
  ^ (2:ℕ) * c * P * κ ^ (2:ℕ))))) + (((-4 * kp ^ (4:ℕ) * r ^ (2:ℕ) * q * κ ^ (2:ℕ) + (-2 * kp ^
  (3:ℕ) * r ^ (3:ℕ) * q * κ ^ (2:ℕ) + 2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * q * κ ^ (2:ℕ))) + ((kp ^
  (3:ℕ) * r * w ^ (2:ℕ) * q * κ ^ (2:ℕ) + 2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * q * κ ^
  (2:ℕ)) + (kp ^ (2:ℕ) * w ^ (4:ℕ) * q * κ ^ (2:ℕ) - 6 * kp ^ (4:ℕ) * r * P * q * κ ^ (2:ℕ))))
  + ((6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * P * q * κ ^ (2:ℕ) + (2 * kp ^ (3:ℕ) * w ^ (2:ℕ) * P * q * κ
  ^ (2:ℕ) - 2 * kp ^ (4:ℕ) * r ^ (2:ℕ) * κ ^ (3:ℕ))) + ((-2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * κ ^
  (3:ℕ) - 2 * kp ^ (4:ℕ) * r * P * κ ^ (3:ℕ)) + (2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * P * κ ^ (3:ℕ) +
  kp ^ (3:ℕ) * w ^ (2:ℕ) * P * κ ^ (3:ℕ))))))) + (((((2 * kp ^ (3:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) *
  q * rv + (6 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * c ^ (2:ℕ) * q * rv + 6 * kp * r ^ (2:ℕ) * w ^
  (2:ℕ) * c ^ (2:ℕ) * q * rv)) + (2 * r ^ (3:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * q * rv + (4 * kp ^
  (3:ℕ) * r * c ^ (2:ℕ) * P * q * rv + 8 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c ^ (2:ℕ) * P * q * rv))) +
  ((4 * kp * r ^ (3:ℕ) * c ^ (2:ℕ) * P * q * rv + (2 * kp ^ (2:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * P *
  q * rv + 2 * kp * r * w ^ (2:ℕ) * c ^ (2:ℕ) * P * q * rv)) + ((-2 * kp ^ (4:ℕ) * r * c * q ^
  (2:ℕ) * rv - 8 * kp ^ (3:ℕ) * r ^ (2:ℕ) * c * q ^ (2:ℕ) * rv) + (-10 * kp ^ (2:ℕ) * r ^ (3:ℕ)
  * c * q ^ (2:ℕ) * rv - 4 * kp * r ^ (4:ℕ) * c * q ^ (2:ℕ) * rv)))) + (((-4 * kp ^ (3:ℕ) * w ^
  (2:ℕ) * c * q ^ (2:ℕ) * rv + (-8 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * c * q ^ (2:ℕ) * rv - 4 * kp *
  r ^ (2:ℕ) * w ^ (2:ℕ) * c * q ^ (2:ℕ) * rv)) + ((2 * kp ^ (4:ℕ) * c * P * q ^ (2:ℕ) * rv - 8
  * kp ^ (3:ℕ) * r * c * P * q ^ (2:ℕ) * rv) + (-10 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c * P * q ^
  (2:ℕ) * rv - 2 * kp ^ (2:ℕ) * w ^ (2:ℕ) * c * P * q ^ (2:ℕ) * rv))) + ((2 * kp ^ (4:ℕ) * r *
  q ^ (3:ℕ) * rv + (6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * q ^ (3:ℕ) * rv + 4 * kp ^ (2:ℕ) * r ^ (3:ℕ) *
  q ^ (3:ℕ) * rv)) + ((-2 * kp ^ (3:ℕ) * w ^ (2:ℕ) * q ^ (3:ℕ) * rv - 2 * kp ^ (2:ℕ) * r * w ^
  (2:ℕ) * q ^ (3:ℕ) * rv) + (-2 * kp ^ (4:ℕ) * P * q ^ (3:ℕ) * rv + 6 * kp ^ (3:ℕ) * r * P * q
  ^ (3:ℕ) * rv))))) + ((((4 * kp ^ (3:ℕ) * r * c ^ (2:ℕ) * P * κ * rv + (8 * kp ^ (2:ℕ) * r ^
  (2:ℕ) * c ^ (2:ℕ) * P * κ * rv + 4 * kp * r ^ (3:ℕ) * c ^ (2:ℕ) * P * κ * rv)) + ((-4 * kp ^
  (3:ℕ) * r ^ (2:ℕ) * c * q * κ * rv - 8 * kp ^ (2:ℕ) * r ^ (3:ℕ) * c * q * κ * rv) + (-4 * kp
  * r ^ (4:ℕ) * c * q * κ * rv - 8 * kp ^ (3:ℕ) * w ^ (2:ℕ) * c * q * κ * rv))) + ((-16 * kp ^
  (2:ℕ) * r * w ^ (2:ℕ) * c * q * κ * rv + (-8 * kp * r ^ (2:ℕ) * w ^ (2:ℕ) * c * q * κ * rv +
  4 * kp ^ (4:ℕ) * c * P * q * κ * rv)) + ((-16 * kp ^ (3:ℕ) * r * c * P * q * κ * rv - 20 * kp
  ^ (2:ℕ) * r ^ (2:ℕ) * c * P * q * κ * rv) + (-2 * kp ^ (2:ℕ) * w ^ (2:ℕ) * c * P * q * κ * rv
  + 2 * kp ^ (4:ℕ) * r * q ^ (2:ℕ) * κ * rv)))) + (((10 * kp ^ (3:ℕ) * r ^ (2:ℕ) * q ^ (2:ℕ) *
  κ * rv + (8 * kp ^ (2:ℕ) * r ^ (3:ℕ) * q ^ (2:ℕ) * κ * rv - 6 * kp ^ (4:ℕ) * P * q ^ (2:ℕ) *
  κ * rv)) + ((18 * kp ^ (3:ℕ) * r * P * q ^ (2:ℕ) * κ * rv + 2 * kp ^ (4:ℕ) * r * c * κ ^
  (2:ℕ) * rv) + (4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * c * κ ^ (2:ℕ) * rv + 2 * kp ^ (2:ℕ) * r ^ (3:ℕ) *
  c * κ ^ (2:ℕ) * rv))) + ((-kp ^ (3:ℕ) * w ^ (2:ℕ) * c * κ ^ (2:ℕ) * rv + (-2 * kp ^ (2:ℕ) * r
  * w ^ (2:ℕ) * c * κ ^ (2:ℕ) * rv - kp * r ^ (2:ℕ) * w ^ (2:ℕ) * c * κ ^ (2:ℕ) * rv)) + ((2 *
  kp ^ (4:ℕ) * c * P * κ ^ (2:ℕ) * rv - 8 * kp ^ (3:ℕ) * r * c * P * κ ^ (2:ℕ) * rv) + (-10 *
  kp ^ (2:ℕ) * r ^ (2:ℕ) * c * P * κ ^ (2:ℕ) * rv - 2 * kp ^ (4:ℕ) * r * q * κ ^ (2:ℕ) *
  rv)))))))) + (((((((2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * q * κ ^ (2:ℕ) * rv + (4 * kp ^ (2:ℕ) * r ^
  (3:ℕ) * q * κ ^ (2:ℕ) * rv + 2 * kp ^ (3:ℕ) * w ^ (2:ℕ) * q * κ ^ (2:ℕ) * rv)) + (2 * kp ^
  (2:ℕ) * r * w ^ (2:ℕ) * q * κ ^ (2:ℕ) * rv + (-6 * kp ^ (4:ℕ) * P * q * κ ^ (2:ℕ) * rv + 18 *
  kp ^ (3:ℕ) * r * P * q * κ ^ (2:ℕ) * rv))) + ((-2 * kp ^ (4:ℕ) * r * κ ^ (3:ℕ) * rv + (-2 *
  kp ^ (3:ℕ) * r ^ (2:ℕ) * κ ^ (3:ℕ) * rv - 2 * kp ^ (4:ℕ) * P * κ ^ (3:ℕ) * rv)) + ((6 * kp ^
  (3:ℕ) * r * P * κ ^ (3:ℕ) * rv + 2 * kp ^ (3:ℕ) * c ^ (2:ℕ) * P * q * rv ^ (2:ℕ)) + (4 * kp ^
  (2:ℕ) * r * c ^ (2:ℕ) * P * q * rv ^ (2:ℕ) + 2 * kp * r ^ (2:ℕ) * c ^ (2:ℕ) * P * q * rv ^
  (2:ℕ))))) + (((-2 * kp ^ (4:ℕ) * c * q ^ (2:ℕ) * rv ^ (2:ℕ) + (-6 * kp ^ (3:ℕ) * r * c * q ^
  (2:ℕ) * rv ^ (2:ℕ) - 6 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c * q ^ (2:ℕ) * rv ^ (2:ℕ))) + ((-2 * kp *
  r ^ (3:ℕ) * c * q ^ (2:ℕ) * rv ^ (2:ℕ) - 6 * kp ^ (3:ℕ) * c * P * q ^ (2:ℕ) * rv ^ (2:ℕ)) +
  (-6 * kp ^ (2:ℕ) * r * c * P * q ^ (2:ℕ) * rv ^ (2:ℕ) + 2 * kp ^ (4:ℕ) * q ^ (3:ℕ) * rv ^
  (2:ℕ)))) + ((4 * kp ^ (3:ℕ) * r * q ^ (3:ℕ) * rv ^ (2:ℕ) + (2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * q ^
  (3:ℕ) * rv ^ (2:ℕ) + 4 * kp ^ (3:ℕ) * P * q ^ (3:ℕ) * rv ^ (2:ℕ))) + ((2 * kp ^ (3:ℕ) * c ^
  (2:ℕ) * P * κ * rv ^ (2:ℕ) + 4 * kp ^ (2:ℕ) * r * c ^ (2:ℕ) * P * κ * rv ^ (2:ℕ)) + (2 * kp *
  r ^ (2:ℕ) * c ^ (2:ℕ) * P * κ * rv ^ (2:ℕ) - 2 * kp ^ (4:ℕ) * c * q * κ * rv ^ (2:ℕ)))))) +
  ((((-6 * kp ^ (3:ℕ) * r * c * q * κ * rv ^ (2:ℕ) + (-6 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c * q * κ *
  rv ^ (2:ℕ) - 2 * kp * r ^ (3:ℕ) * c * q * κ * rv ^ (2:ℕ))) + (-12 * kp ^ (3:ℕ) * c * P * q *
  κ * rv ^ (2:ℕ) + (-12 * kp ^ (2:ℕ) * r * c * P * q * κ * rv ^ (2:ℕ) + 4 * kp ^ (4:ℕ) * q ^
  (2:ℕ) * κ * rv ^ (2:ℕ)))) + ((8 * kp ^ (3:ℕ) * r * q ^ (2:ℕ) * κ * rv ^ (2:ℕ) + (4 * kp ^
  (2:ℕ) * r ^ (2:ℕ) * q ^ (2:ℕ) * κ * rv ^ (2:ℕ) + 12 * kp ^ (3:ℕ) * P * q ^ (2:ℕ) * κ * rv ^
  (2:ℕ))) + ((-6 * kp ^ (3:ℕ) * c * P * κ ^ (2:ℕ) * rv ^ (2:ℕ) - 6 * kp ^ (2:ℕ) * r * c * P * κ
  ^ (2:ℕ) * rv ^ (2:ℕ)) + (2 * kp ^ (4:ℕ) * q * κ ^ (2:ℕ) * rv ^ (2:ℕ) + 4 * kp ^ (3:ℕ) * r * q
  * κ ^ (2:ℕ) * rv ^ (2:ℕ))))) + (((2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * q * κ ^ (2:ℕ) * rv ^ (2:ℕ) +
  (12 * kp ^ (3:ℕ) * P * q * κ ^ (2:ℕ) * rv ^ (2:ℕ) + 4 * kp ^ (3:ℕ) * P * κ ^ (3:ℕ) * rv ^
  (2:ℕ))) + ((-4 * kp ^ (3:ℕ) * r * w * c ^ (2:ℕ) * q * xv - 6 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * c
  ^ (2:ℕ) * q * xv) + (2 * r ^ (4:ℕ) * w * c ^ (2:ℕ) * q * xv + 4 * kp ^ (2:ℕ) * w ^ (3:ℕ) * c
  ^ (2:ℕ) * q * xv))) + ((8 * kp * r * w ^ (3:ℕ) * c ^ (2:ℕ) * q * xv + (4 * r ^ (2:ℕ) * w ^
  (3:ℕ) * c ^ (2:ℕ) * q * xv - 4 * kp ^ (3:ℕ) * w * c ^ (2:ℕ) * P * q * xv)) + ((-4 * kp ^
  (2:ℕ) * r * w * c ^ (2:ℕ) * P * q * xv + 8 * kp ^ (3:ℕ) * r * w * c * q ^ (2:ℕ) * xv) + (8 *
  kp ^ (2:ℕ) * r ^ (2:ℕ) * w * c * q ^ (2:ℕ) * xv + 8 * kp ^ (2:ℕ) * w ^ (3:ℕ) * c * q ^ (2:ℕ)
  * xv)))))) + (((((8 * kp * r * w ^ (3:ℕ) * c * q ^ (2:ℕ) * xv + (4 * kp ^ (3:ℕ) * w * c * P *
  q ^ (2:ℕ) * xv - 8 * kp ^ (3:ℕ) * r * w * q ^ (3:ℕ) * xv)) + (-6 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w
  * q ^ (3:ℕ) * xv + (2 * kp ^ (3:ℕ) * w * c ^ (2:ℕ) * P * κ * xv + 4 * kp ^ (2:ℕ) * r * w * c
  ^ (2:ℕ) * P * κ * xv))) + ((2 * kp * r ^ (2:ℕ) * w * c ^ (2:ℕ) * P * κ * xv + (2 * kp ^ (3:ℕ)
  * r * w * c * q * κ * xv - 4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * c * q * κ * xv)) + ((-6 * kp * r
  ^ (3:ℕ) * w * c * q * κ * xv - 4 * kp ^ (2:ℕ) * w ^ (3:ℕ) * c * q * κ * xv) + (-4 * kp * r *
  w ^ (3:ℕ) * c * q * κ * xv - 4 * kp ^ (2:ℕ) * r * w * c * P * q * κ * xv)))) + (((-8 * kp ^
  (3:ℕ) * r * w * q ^ (2:ℕ) * κ * xv + (-4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * q ^ (2:ℕ) * κ * xv -
  2 * kp ^ (2:ℕ) * w ^ (3:ℕ) * q ^ (2:ℕ) * κ * xv)) + ((2 * kp ^ (3:ℕ) * w * P * q ^ (2:ℕ) * κ
  * xv - 4 * kp ^ (3:ℕ) * w * c * P * κ ^ (2:ℕ) * xv) + (-4 * kp ^ (2:ℕ) * r * w * c * P * κ ^
  (2:ℕ) * xv + 2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w * q * κ ^ (2:ℕ) * xv))) + ((2 * kp ^ (2:ℕ) * w ^
  (3:ℕ) * q * κ ^ (2:ℕ) * xv + (4 * kp ^ (3:ℕ) * w * P * q * κ ^ (2:ℕ) * xv + 2 * kp ^ (3:ℕ) *
  w * P * κ ^ (3:ℕ) * xv)) + ((2 * kp ^ (3:ℕ) * w * c ^ (2:ℕ) * q * rv * xv + 6 * kp ^ (2:ℕ) *
  r * w * c ^ (2:ℕ) * q * rv * xv) + (6 * kp * r ^ (2:ℕ) * w * c ^ (2:ℕ) * q * rv * xv + 2 * r
  ^ (3:ℕ) * w * c ^ (2:ℕ) * q * rv * xv))))) + ((((4 * kp ^ (2:ℕ) * w * c ^ (2:ℕ) * P * q * rv
  * xv + (4 * kp * r * w * c ^ (2:ℕ) * P * q * rv * xv - 4 * kp ^ (2:ℕ) * w * c * P * q ^ (2:ℕ)
  * rv * xv)) + ((-6 * kp ^ (3:ℕ) * w * q ^ (3:ℕ) * rv * xv - 6 * kp ^ (2:ℕ) * r * w * q ^
  (3:ℕ) * rv * xv) + (-6 * kp ^ (3:ℕ) * w * c * q * κ * rv * xv - 12 * kp ^ (2:ℕ) * r * w * c *
  q * κ * rv * xv))) + ((-6 * kp * r ^ (2:ℕ) * w * c * q * κ * rv * xv + (-4 * kp ^ (2:ℕ) * w *
  c * P * q * κ * rv * xv - 4 * kp ^ (3:ℕ) * w * q ^ (2:ℕ) * κ * rv * xv)) + ((-4 * kp ^ (2:ℕ)
  * r * w * q ^ (2:ℕ) * κ * rv * xv + 2 * kp ^ (3:ℕ) * w * q * κ ^ (2:ℕ) * rv * xv) + (2 * kp ^
  (2:ℕ) * r * w * q * κ ^ (2:ℕ) * rv * xv - 3 * kp ^ (3:ℕ) * r * c ^ (2:ℕ) * q * xv ^ (2:ℕ)))))
  + (((-6 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c ^ (2:ℕ) * q * xv ^ (2:ℕ) + (-3 * kp * r ^ (3:ℕ) * c ^
  (2:ℕ) * q * xv ^ (2:ℕ) + 2 * kp ^ (2:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * q * xv ^ (2:ℕ))) + ((4 * kp
  * r * w ^ (2:ℕ) * c ^ (2:ℕ) * q * xv ^ (2:ℕ) + 2 * r ^ (2:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * q * xv
  ^ (2:ℕ)) + (-2 * kp ^ (3:ℕ) * c ^ (2:ℕ) * P * q * xv ^ (2:ℕ) - 2 * kp ^ (2:ℕ) * r * c ^ (2:ℕ)
  * P * q * xv ^ (2:ℕ)))) + ((7 * kp ^ (3:ℕ) * r * c * q ^ (2:ℕ) * xv ^ (2:ℕ) + (10 * kp ^
  (2:ℕ) * r ^ (2:ℕ) * c * q ^ (2:ℕ) * xv ^ (2:ℕ) + 3 * kp * r ^ (3:ℕ) * c * q ^ (2:ℕ) * xv ^
  (2:ℕ))) + ((10 * kp ^ (2:ℕ) * w ^ (2:ℕ) * c * q ^ (2:ℕ) * xv ^ (2:ℕ) + 10 * kp * r * w ^
  (2:ℕ) * c * q ^ (2:ℕ) * xv ^ (2:ℕ)) + (2 * kp ^ (3:ℕ) * c * P * q ^ (2:ℕ) * xv ^ (2:ℕ) - 5 *
  kp ^ (3:ℕ) * r * q ^ (3:ℕ) * xv ^ (2:ℕ)))))))) + ((((((-4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * q ^
  (3:ℕ) * xv ^ (2:ℕ) + (kp ^ (2:ℕ) * w ^ (2:ℕ) * q ^ (3:ℕ) * xv ^ (2:ℕ) + kp ^ (3:ℕ) * c ^
  (2:ℕ) * P * κ * xv ^ (2:ℕ))) + (2 * kp ^ (2:ℕ) * r * c ^ (2:ℕ) * P * κ * xv ^ (2:ℕ) + (kp * r
  ^ (2:ℕ) * c ^ (2:ℕ) * P * κ * xv ^ (2:ℕ) + 4 * kp ^ (3:ℕ) * r * c * q * κ * xv ^ (2:ℕ)))) +
  ((4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c * q * κ * xv ^ (2:ℕ) + (-2 * kp ^ (2:ℕ) * w ^ (2:ℕ) * c * q
  * κ * xv ^ (2:ℕ) - 2 * kp * r * w ^ (2:ℕ) * c * q * κ * xv ^ (2:ℕ))) + ((-2 * kp ^ (2:ℕ) * r
  * c * P * q * κ * xv ^ (2:ℕ) - 6 * kp ^ (3:ℕ) * r * q ^ (2:ℕ) * κ * xv ^ (2:ℕ)) + (-4 * kp ^
  (2:ℕ) * r ^ (2:ℕ) * q ^ (2:ℕ) * κ * xv ^ (2:ℕ) - 4 * kp ^ (2:ℕ) * w ^ (2:ℕ) * q ^ (2:ℕ) * κ *
  xv ^ (2:ℕ))))) + (((kp ^ (3:ℕ) * P * q ^ (2:ℕ) * κ * xv ^ (2:ℕ) + (-2 * kp ^ (3:ℕ) * c * P *
  κ ^ (2:ℕ) * xv ^ (2:ℕ) - 2 * kp ^ (2:ℕ) * r * c * P * κ ^ (2:ℕ) * xv ^ (2:ℕ))) + ((-kp ^
  (3:ℕ) * r * q * κ ^ (2:ℕ) * xv ^ (2:ℕ) + kp ^ (2:ℕ) * w ^ (2:ℕ) * q * κ ^ (2:ℕ) * xv ^ (2:ℕ))
  + (2 * kp ^ (3:ℕ) * P * q * κ ^ (2:ℕ) * xv ^ (2:ℕ) + kp ^ (3:ℕ) * P * κ ^ (3:ℕ) * xv ^
  (2:ℕ)))) + ((2 * kp ^ (2:ℕ) * c ^ (2:ℕ) * P * q * rv * xv ^ (2:ℕ) + (2 * kp * r * c ^ (2:ℕ) *
  P * q * rv * xv ^ (2:ℕ) + 3 * kp ^ (3:ℕ) * c * q ^ (2:ℕ) * rv * xv ^ (2:ℕ))) + ((6 * kp ^
  (2:ℕ) * r * c * q ^ (2:ℕ) * rv * xv ^ (2:ℕ) + 3 * kp * r ^ (2:ℕ) * c * q ^ (2:ℕ) * rv * xv ^
  (2:ℕ)) + (-2 * kp ^ (2:ℕ) * c * P * q ^ (2:ℕ) * rv * xv ^ (2:ℕ) - 4 * kp ^ (3:ℕ) * q ^ (3:ℕ)
  * rv * xv ^ (2:ℕ)))))) + ((((-4 * kp ^ (2:ℕ) * r * q ^ (3:ℕ) * rv * xv ^ (2:ℕ) + (-2 * kp ^
  (2:ℕ) * c * P * q * κ * rv * xv ^ (2:ℕ) - 4 * kp ^ (3:ℕ) * q ^ (2:ℕ) * κ * rv * xv ^ (2:ℕ)))
  + ((-4 * kp ^ (2:ℕ) * r * q ^ (2:ℕ) * κ * rv * xv ^ (2:ℕ) + 4 * kp ^ (2:ℕ) * w * c * q ^
  (2:ℕ) * xv ^ (3:ℕ)) + (4 * kp * r * w * c * q ^ (2:ℕ) * xv ^ (3:ℕ) + 2 * kp ^ (2:ℕ) * w * q ^
  (3:ℕ) * xv ^ (3:ℕ)))) + ((-2 * kp ^ (2:ℕ) * w * q ^ (2:ℕ) * κ * xv ^ (3:ℕ) + (kp ^ (2:ℕ) * q
  ^ (3:ℕ) * xv ^ (4:ℕ) - kp ^ (2:ℕ) * w ^ (2:ℕ) * c ^ (3:ℕ) * q)) + ((-2 * kp * r * w ^ (2:ℕ) *
  c ^ (3:ℕ) * q - r ^ (2:ℕ) * w ^ (2:ℕ) * c ^ (3:ℕ) * q) + (kp ^ (3:ℕ) * r * c ^ (2:ℕ) * q ^
  (2:ℕ) + 2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c ^ (2:ℕ) * q ^ (2:ℕ))))) + (((kp * r ^ (3:ℕ) * c ^
  (2:ℕ) * q ^ (2:ℕ) + (2 * kp ^ (2:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * q ^ (2:ℕ) + 2 * kp * r * w ^
  (2:ℕ) * c ^ (2:ℕ) * q ^ (2:ℕ))) + ((-2 * kp ^ (3:ℕ) * r * c * q ^ (3:ℕ) - 2 * kp ^ (2:ℕ) * r
  ^ (2:ℕ) * c * q ^ (3:ℕ)) + (-kp ^ (2:ℕ) * w ^ (2:ℕ) * c * q ^ (3:ℕ) + kp ^ (3:ℕ) * r * q ^
  (4:ℕ)))) + ((2 * kp ^ (3:ℕ) * r * c ^ (2:ℕ) * q * κ + (4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c ^ (2:ℕ)
  * q * κ + 2 * kp * r ^ (3:ℕ) * c ^ (2:ℕ) * q * κ)) + ((2 * kp ^ (2:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ)
  * q * κ + 2 * kp * r * w ^ (2:ℕ) * c ^ (2:ℕ) * q * κ) + (-6 * kp ^ (3:ℕ) * r * c * q ^ (2:ℕ)
  * κ - 6 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c * q ^ (2:ℕ) * κ)))))) + (((((-2 * kp ^ (2:ℕ) * w ^ (2:ℕ)
  * c * q ^ (2:ℕ) * κ + (4 * kp ^ (3:ℕ) * r * q ^ (3:ℕ) * κ + kp ^ (3:ℕ) * r * c ^ (2:ℕ) * κ ^
  (2:ℕ))) + (2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c ^ (2:ℕ) * κ ^ (2:ℕ) + (kp * r ^ (3:ℕ) * c ^ (2:ℕ) *
  κ ^ (2:ℕ) - 6 * kp ^ (3:ℕ) * r * c * q * κ ^ (2:ℕ)))) + ((-6 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c * q
  * κ ^ (2:ℕ) + (-kp ^ (2:ℕ) * w ^ (2:ℕ) * c * q * κ ^ (2:ℕ) + 6 * kp ^ (3:ℕ) * r * q ^ (2:ℕ) *
  κ ^ (2:ℕ))) + ((-2 * kp ^ (3:ℕ) * r * c * κ ^ (3:ℕ) - 2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c * κ ^
  (3:ℕ)) + (4 * kp ^ (3:ℕ) * r * q * κ ^ (3:ℕ) + kp ^ (3:ℕ) * r * κ ^ (4:ℕ))))) + (((kp ^ (3:ℕ)
  * c ^ (2:ℕ) * q ^ (2:ℕ) * rv + (2 * kp ^ (2:ℕ) * r * c ^ (2:ℕ) * q ^ (2:ℕ) * rv + kp * r ^
  (2:ℕ) * c ^ (2:ℕ) * q ^ (2:ℕ) * rv)) + ((-2 * kp ^ (3:ℕ) * c * q ^ (3:ℕ) * rv - 2 * kp ^
  (2:ℕ) * r * c * q ^ (3:ℕ) * rv) + (kp ^ (3:ℕ) * q ^ (4:ℕ) * rv + 2 * kp ^ (3:ℕ) * c ^ (2:ℕ) *
  q * κ * rv))) + ((4 * kp ^ (2:ℕ) * r * c ^ (2:ℕ) * q * κ * rv + (2 * kp * r ^ (2:ℕ) * c ^
  (2:ℕ) * q * κ * rv - 6 * kp ^ (3:ℕ) * c * q ^ (2:ℕ) * κ * rv)) + ((-6 * kp ^ (2:ℕ) * r * c *
  q ^ (2:ℕ) * κ * rv + 4 * kp ^ (3:ℕ) * q ^ (3:ℕ) * κ * rv) + (kp ^ (3:ℕ) * c ^ (2:ℕ) * κ ^
  (2:ℕ) * rv + 2 * kp ^ (2:ℕ) * r * c ^ (2:ℕ) * κ ^ (2:ℕ) * rv))))) + ((((kp * r ^ (2:ℕ) * c ^
  (2:ℕ) * κ ^ (2:ℕ) * rv + (-6 * kp ^ (3:ℕ) * c * q * κ ^ (2:ℕ) * rv - 6 * kp ^ (2:ℕ) * r * c *
  q * κ ^ (2:ℕ) * rv)) + ((6 * kp ^ (3:ℕ) * q ^ (2:ℕ) * κ ^ (2:ℕ) * rv - 2 * kp ^ (3:ℕ) * c * κ
  ^ (3:ℕ) * rv) + (-2 * kp ^ (2:ℕ) * r * c * κ ^ (3:ℕ) * rv + 4 * kp ^ (3:ℕ) * q * κ ^ (3:ℕ) *
  rv))) + ((kp ^ (3:ℕ) * κ ^ (4:ℕ) * rv + (-2 * kp ^ (2:ℕ) * w * c ^ (3:ℕ) * q * xv - 4 * kp *
  r * w * c ^ (3:ℕ) * q * xv)) + ((-2 * r ^ (2:ℕ) * w * c ^ (3:ℕ) * q * xv + 4 * kp ^ (2:ℕ) * w
  * c ^ (2:ℕ) * q ^ (2:ℕ) * xv) + (4 * kp * r * w * c ^ (2:ℕ) * q ^ (2:ℕ) * xv - 2 * kp ^ (2:ℕ)
  * w * c * q ^ (3:ℕ) * xv)))) + (((4 * kp ^ (2:ℕ) * w * c ^ (2:ℕ) * q * κ * xv + (4 * kp * r *
  w * c ^ (2:ℕ) * q * κ * xv - 4 * kp ^ (2:ℕ) * w * c * q ^ (2:ℕ) * κ * xv)) + ((-2 * kp ^
  (2:ℕ) * w * c * q * κ ^ (2:ℕ) * xv - kp ^ (2:ℕ) * c ^ (3:ℕ) * q * xv ^ (2:ℕ)) + (-2 * kp * r
  * c ^ (3:ℕ) * q * xv ^ (2:ℕ) - r ^ (2:ℕ) * c ^ (3:ℕ) * q * xv ^ (2:ℕ)))) + ((2 * kp ^ (2:ℕ) *
  c ^ (2:ℕ) * q ^ (2:ℕ) * xv ^ (2:ℕ) + (2 * kp * r * c ^ (2:ℕ) * q ^ (2:ℕ) * xv ^ (2:ℕ) - kp ^
  (2:ℕ) * c * q ^ (3:ℕ) * xv ^ (2:ℕ))) + ((2 * kp ^ (2:ℕ) * c ^ (2:ℕ) * q * κ * xv ^ (2:ℕ) + 2
  * kp * r * c ^ (2:ℕ) * q * κ * xv ^ (2:ℕ)) + (-2 * kp ^ (2:ℕ) * c * q ^ (2:ℕ) * κ * xv ^
  (2:ℕ) - kp ^ (2:ℕ) * c * q * κ ^ (2:ℕ) * xv ^ (2:ℕ)))))))))))

/-- `Δ₈ / (k_p² q)` of the pole–zero quartic (2619 terms). -/
def delta8F (kp r w c P e q κ rv xv : ℝ) : ℝ :=
  delta8F0 kp r w c P e q κ rv xv +
    delta8F1 kp r w c P e q κ rv xv +
    delta8F2 kp r w c P e q κ rv xv

/-- The factor `G` of `Δ₄ = (k_p + r) G` in the ideal design (6 terms). -/
def idealDelta4F (kp r _w c P q : ℝ) : ℝ :=
  ((kp ^ (2:ℕ) * r + (kp * r ^ (2:ℕ) + kp ^ (2:ℕ) * P)) + (kp * c + (r * c - kp * q)))

/-- `Δ₆ / k_p` in the ideal design (52 terms). -/
def idealDelta6F (kp r w c P q : ℝ) : ℝ :=
  (((((kp ^ (4:ℕ) * r ^ (3:ℕ) * P + (2 * kp ^ (3:ℕ) * r ^ (4:ℕ) * P + kp ^ (2:ℕ) * r ^ (5:ℕ) *
  P)) + (kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P + (2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P + kp ^
  (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P))) + ((2 * kp ^ (4:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ) + (2 * kp ^
  (3:ℕ) * r ^ (3:ℕ) * P ^ (2:ℕ) + kp ^ (4:ℕ) * r * P ^ (3:ℕ))) + ((2 * kp ^ (3:ℕ) * r ^ (2:ℕ) *
  c * P + 4 * kp ^ (2:ℕ) * r ^ (3:ℕ) * c * P) + (2 * kp * r ^ (4:ℕ) * c * P + kp ^ (3:ℕ) * w ^
  (2:ℕ) * c * P)))) + (((2 * kp ^ (2:ℕ) * r * w ^ (2:ℕ) * c * P + (kp * r ^ (2:ℕ) * w ^ (2:ℕ) *
  c * P + 2 * kp ^ (3:ℕ) * r * c * P ^ (2:ℕ))) + (2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c * P ^ (2:ℕ) +
  (-kp ^ (3:ℕ) * r ^ (3:ℕ) * q - 2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * q))) + ((-kp * r ^ (5:ℕ) * q +
  (-3 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * q - 6 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * q)) + ((-3 *
  kp * r ^ (3:ℕ) * w ^ (2:ℕ) * q + kp ^ (4:ℕ) * r * P * q) + (-2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * P *
  q - 3 * kp ^ (2:ℕ) * r ^ (3:ℕ) * P * q))))) + ((((kp ^ (4:ℕ) * P ^ (2:ℕ) * q + (-2 * kp ^
  (3:ℕ) * r * P ^ (2:ℕ) * q + kp ^ (2:ℕ) * r * c ^ (2:ℕ) * P)) + (2 * kp * r ^ (2:ℕ) * c ^
  (2:ℕ) * P + (r ^ (3:ℕ) * c ^ (2:ℕ) * P + kp ^ (3:ℕ) * r * c * q))) + ((kp ^ (2:ℕ) * r ^ (2:ℕ)
  * c * q + (-kp * r ^ (3:ℕ) * c * q - r ^ (4:ℕ) * c * q)) + ((-3 * kp ^ (2:ℕ) * w ^ (2:ℕ) * c
  * q - 6 * kp * r * w ^ (2:ℕ) * c * q) + (-3 * r ^ (2:ℕ) * w ^ (2:ℕ) * c * q + 2 * kp ^ (3:ℕ)
  * c * P * q)))) + (((-2 * kp * r ^ (2:ℕ) * c * P * q + (-kp ^ (3:ℕ) * r * q ^ (2:ℕ) + kp * r
  ^ (3:ℕ) * q ^ (2:ℕ))) + (-kp ^ (2:ℕ) * w ^ (2:ℕ) * q ^ (2:ℕ) + (-kp * r * w ^ (2:ℕ) * q ^
  (2:ℕ) - 2 * kp ^ (3:ℕ) * P * q ^ (2:ℕ)))) + ((kp ^ (2:ℕ) * r * P * q ^ (2:ℕ) + (kp ^ (2:ℕ) *
  c ^ (2:ℕ) * q + 2 * kp * r * c ^ (2:ℕ) * q)) + ((r ^ (2:ℕ) * c ^ (2:ℕ) * q - 2 * kp ^ (2:ℕ) *
  c * q ^ (2:ℕ)) + (-2 * kp * r * c * q ^ (2:ℕ) + kp ^ (2:ℕ) * q ^ (3:ℕ)))))))

/-- `Δ₈ / (k_p² q)` in the ideal design (147 terms). -/
def idealDelta8F (kp r w c P q : ℝ) : ℝ :=
  (((((((kp ^ (5:ℕ) * r ^ (5:ℕ) * P ^ (2:ℕ) + 2 * kp ^ (4:ℕ) * r ^ (6:ℕ) * P ^ (2:ℕ)) + (kp ^
  (3:ℕ) * r ^ (7:ℕ) * P ^ (2:ℕ) + 2 * kp ^ (5:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ))) + ((4 *
  kp ^ (4:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) + 2 * kp ^ (3:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * P ^
  (2:ℕ)) + (kp ^ (5:ℕ) * r * w ^ (4:ℕ) * P ^ (2:ℕ) + (2 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) *
  P ^ (2:ℕ) + kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * P ^ (2:ℕ))))) + (((2 * kp ^ (5:ℕ) * r ^
  (4:ℕ) * P ^ (3:ℕ) + 2 * kp ^ (4:ℕ) * r ^ (5:ℕ) * P ^ (3:ℕ)) + (2 * kp ^ (5:ℕ) * r ^ (2:ℕ) * w
  ^ (2:ℕ) * P ^ (3:ℕ) + 2 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (3:ℕ))) + ((kp ^ (5:ℕ) * r
  ^ (3:ℕ) * P ^ (4:ℕ) + kp ^ (5:ℕ) * r * w ^ (2:ℕ) * P ^ (4:ℕ)) + (2 * kp ^ (4:ℕ) * r ^ (4:ℕ) *
  c * P ^ (2:ℕ) + (4 * kp ^ (3:ℕ) * r ^ (5:ℕ) * c * P ^ (2:ℕ) + 2 * kp ^ (2:ℕ) * r ^ (6:ℕ) * c
  * P ^ (2:ℕ)))))) + ((((3 * kp ^ (4:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) + 6 * kp ^
  (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ)) + (3 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * c
  * P ^ (2:ℕ) + kp ^ (4:ℕ) * w ^ (4:ℕ) * c * P ^ (2:ℕ))) + ((2 * kp ^ (3:ℕ) * r * w ^ (4:ℕ) * c
  * P ^ (2:ℕ) + kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * c * P ^ (2:ℕ)) + (2 * kp ^ (4:ℕ) * r ^
  (3:ℕ) * c * P ^ (3:ℕ) + (2 * kp ^ (3:ℕ) * r ^ (4:ℕ) * c * P ^ (3:ℕ) + 2 * kp ^ (4:ℕ) * r * w
  ^ (2:ℕ) * c * P ^ (3:ℕ))))) + (((2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P ^ (3:ℕ) - kp
  ^ (3:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * q) + (-2 * kp ^ (2:ℕ) * r ^ (6:ℕ) * w ^ (2:ℕ) * q - kp * r
  ^ (7:ℕ) * w ^ (2:ℕ) * q)) + ((-2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * q - 4 * kp ^ (2:ℕ) *
  r ^ (4:ℕ) * w ^ (4:ℕ) * q) + (-2 * kp * r ^ (5:ℕ) * w ^ (4:ℕ) * q + (-kp ^ (3:ℕ) * r * w ^
  (6:ℕ) * q - 2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (6:ℕ) * q)))))) + (((((-kp * r ^ (3:ℕ) * w ^
  (6:ℕ) * q - 2 * kp ^ (4:ℕ) * r ^ (5:ℕ) * P * q) + (-4 * kp ^ (3:ℕ) * r ^ (6:ℕ) * P * q - 2 *
  kp ^ (2:ℕ) * r ^ (7:ℕ) * P * q)) + ((-4 * kp ^ (4:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P * q - 10 *
  kp ^ (3:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * P * q) + (-6 * kp ^ (2:ℕ) * r ^ (5:ℕ) * w ^ (2:ℕ) * P *
  q + (-2 * kp ^ (4:ℕ) * r * w ^ (4:ℕ) * P * q - 6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * P *
  q)))) + (((-4 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (4:ℕ) * P * q + 2 * kp ^ (5:ℕ) * r ^ (3:ℕ) * P ^
  (2:ℕ) * q) + (-2 * kp ^ (4:ℕ) * r ^ (4:ℕ) * P ^ (2:ℕ) * q - 4 * kp ^ (3:ℕ) * r ^ (5:ℕ) * P ^
  (2:ℕ) * q)) + ((-2 * kp ^ (5:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * q - 6 * kp ^ (4:ℕ) * r ^ (2:ℕ)
  * w ^ (2:ℕ) * P ^ (2:ℕ) * q) + (-5 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P ^ (2:ℕ) * q +
  (-kp ^ (3:ℕ) * r * w ^ (4:ℕ) * P ^ (2:ℕ) * q + 2 * kp ^ (5:ℕ) * r ^ (2:ℕ) * P ^ (3:ℕ) *
  q))))) + ((((-2 * kp ^ (4:ℕ) * r ^ (3:ℕ) * P ^ (3:ℕ) * q - 2 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * P
  ^ (3:ℕ) * q) + (kp ^ (3:ℕ) * r ^ (3:ℕ) * c ^ (2:ℕ) * P ^ (2:ℕ) + 2 * kp ^ (2:ℕ) * r ^ (4:ℕ) *
  c ^ (2:ℕ) * P ^ (2:ℕ))) + ((kp * r ^ (5:ℕ) * c ^ (2:ℕ) * P ^ (2:ℕ) + kp ^ (3:ℕ) * r * w ^
  (2:ℕ) * c ^ (2:ℕ) * P ^ (2:ℕ)) + (2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * P ^
  (2:ℕ) + (kp * r ^ (3:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * P ^ (2:ℕ) + 2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * w
  ^ (2:ℕ) * c * q)))) + (((3 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * c * q - r ^ (6:ℕ) * w ^
  (2:ℕ) * c * q) + (2 * kp ^ (3:ℕ) * r * w ^ (4:ℕ) * c * q + (2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^
  (4:ℕ) * c * q - 2 * kp * r ^ (3:ℕ) * w ^ (4:ℕ) * c * q))) + ((-2 * r ^ (4:ℕ) * w ^ (4:ℕ) * c
  * q - kp ^ (2:ℕ) * w ^ (6:ℕ) * c * q) + (-2 * kp * r * w ^ (6:ℕ) * c * q + (-r ^ (2:ℕ) * w ^
  (6:ℕ) * c * q + 2 * kp ^ (4:ℕ) * r ^ (3:ℕ) * c * P * q))))))) + ((((((2 * kp ^ (3:ℕ) * r ^
  (4:ℕ) * c * P * q - 2 * kp ^ (2:ℕ) * r ^ (5:ℕ) * c * P * q) + (-2 * kp * r ^ (6:ℕ) * c * P *
  q - 2 * kp ^ (4:ℕ) * r * w ^ (2:ℕ) * c * P * q)) + ((-6 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ)
  * c * P * q - 10 * kp ^ (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * c * P * q) + (-6 * kp * r ^ (4:ℕ) * w
  ^ (2:ℕ) * c * P * q + (-2 * kp ^ (3:ℕ) * w ^ (4:ℕ) * c * P * q - 6 * kp ^ (2:ℕ) * r * w ^
  (4:ℕ) * c * P * q)))) + (((-4 * kp * r ^ (2:ℕ) * w ^ (4:ℕ) * c * P * q + 4 * kp ^ (4:ℕ) * r ^
  (2:ℕ) * c * P ^ (2:ℕ) * q) + (2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * c * P ^ (2:ℕ) * q - 2 * kp ^ (2:ℕ)
  * r ^ (4:ℕ) * c * P ^ (2:ℕ) * q)) + ((-kp ^ (4:ℕ) * w ^ (2:ℕ) * c * P ^ (2:ℕ) * q - 2 * kp ^
  (3:ℕ) * r * w ^ (2:ℕ) * c * P ^ (2:ℕ) * q) + (-2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * P
  ^ (2:ℕ) * q + (kp ^ (3:ℕ) * r ^ (5:ℕ) * q ^ (2:ℕ) + 2 * kp ^ (2:ℕ) * r ^ (6:ℕ) * q ^
  (2:ℕ)))))) + ((((kp * r ^ (7:ℕ) * q ^ (2:ℕ) + 2 * kp ^ (2:ℕ) * r ^ (4:ℕ) * w ^ (2:ℕ) * q ^
  (2:ℕ)) + (2 * kp * r ^ (5:ℕ) * w ^ (2:ℕ) * q ^ (2:ℕ) + 3 * kp ^ (3:ℕ) * r * w ^ (4:ℕ) * q ^
  (2:ℕ))) + ((4 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (4:ℕ) * q ^ (2:ℕ) + kp * r ^ (3:ℕ) * w ^ (4:ℕ) *
  q ^ (2:ℕ)) + (-4 * kp ^ (4:ℕ) * r ^ (3:ℕ) * P * q ^ (2:ℕ) + (-2 * kp ^ (3:ℕ) * r ^ (4:ℕ) * P
  * q ^ (2:ℕ) + 2 * kp ^ (2:ℕ) * r ^ (5:ℕ) * P * q ^ (2:ℕ))))) + (((4 * kp ^ (4:ℕ) * r * w ^
  (2:ℕ) * P * q ^ (2:ℕ) + 4 * kp ^ (3:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * P * q ^ (2:ℕ)) + (2 * kp ^
  (2:ℕ) * r ^ (3:ℕ) * w ^ (2:ℕ) * P * q ^ (2:ℕ) + (kp ^ (5:ℕ) * r * P ^ (2:ℕ) * q ^ (2:ℕ) - 4 *
  kp ^ (4:ℕ) * r ^ (2:ℕ) * P ^ (2:ℕ) * q ^ (2:ℕ)))) + ((kp ^ (3:ℕ) * r ^ (3:ℕ) * P ^ (2:ℕ) * q
  ^ (2:ℕ) + kp ^ (3:ℕ) * r * w ^ (2:ℕ) * P ^ (2:ℕ) * q ^ (2:ℕ)) + (-kp ^ (3:ℕ) * r * w ^ (2:ℕ)
  * c ^ (2:ℕ) * q + (3 * kp * r ^ (3:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * q + 2 * r ^ (4:ℕ) * w ^ (2:ℕ)
  * c ^ (2:ℕ) * q)))))) + (((((2 * kp ^ (2:ℕ) * w ^ (4:ℕ) * c ^ (2:ℕ) * q + 4 * kp * r * w ^
  (4:ℕ) * c ^ (2:ℕ) * q) + (2 * r ^ (2:ℕ) * w ^ (4:ℕ) * c ^ (2:ℕ) * q + 2 * kp ^ (3:ℕ) * r ^
  (2:ℕ) * c ^ (2:ℕ) * P * q)) + ((4 * kp ^ (2:ℕ) * r ^ (3:ℕ) * c ^ (2:ℕ) * P * q + 2 * kp * r ^
  (4:ℕ) * c ^ (2:ℕ) * P * q) + (-2 * kp ^ (3:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * P * q + (-2 * kp ^
  (2:ℕ) * r * w ^ (2:ℕ) * c ^ (2:ℕ) * P * q - 2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * c * q ^ (2:ℕ))))) +
  (((-4 * kp ^ (2:ℕ) * r ^ (4:ℕ) * c * q ^ (2:ℕ) - 2 * kp * r ^ (5:ℕ) * c * q ^ (2:ℕ)) + (-4 *
  kp ^ (2:ℕ) * r ^ (2:ℕ) * w ^ (2:ℕ) * c * q ^ (2:ℕ) - 4 * kp * r ^ (3:ℕ) * w ^ (2:ℕ) * c * q ^
  (2:ℕ))) + ((2 * kp ^ (2:ℕ) * w ^ (4:ℕ) * c * q ^ (2:ℕ) + 2 * kp * r * w ^ (4:ℕ) * c * q ^
  (2:ℕ)) + (2 * kp ^ (4:ℕ) * r * c * P * q ^ (2:ℕ) + (-2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * c * P * q ^
  (2:ℕ) - 4 * kp ^ (2:ℕ) * r ^ (3:ℕ) * c * P * q ^ (2:ℕ)))))) + ((((2 * kp ^ (3:ℕ) * w ^ (2:ℕ)
  * c * P * q ^ (2:ℕ) + 2 * kp ^ (3:ℕ) * r ^ (3:ℕ) * q ^ (3:ℕ)) + (2 * kp ^ (2:ℕ) * r ^ (4:ℕ) *
  q ^ (3:ℕ) - 3 * kp ^ (3:ℕ) * r * w ^ (2:ℕ) * q ^ (3:ℕ))) + ((-2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * w
  ^ (2:ℕ) * q ^ (3:ℕ) - 2 * kp ^ (4:ℕ) * r * P * q ^ (3:ℕ)) + (2 * kp ^ (3:ℕ) * r ^ (2:ℕ) * P *
  q ^ (3:ℕ) + (-kp ^ (2:ℕ) * w ^ (2:ℕ) * c ^ (3:ℕ) * q - 2 * kp * r * w ^ (2:ℕ) * c ^ (3:ℕ) *
  q)))) + (((-r ^ (2:ℕ) * w ^ (2:ℕ) * c ^ (3:ℕ) * q + kp ^ (3:ℕ) * r * c ^ (2:ℕ) * q ^ (2:ℕ)) +
  (2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c ^ (2:ℕ) * q ^ (2:ℕ) + (kp * r ^ (3:ℕ) * c ^ (2:ℕ) * q ^ (2:ℕ)
  + 2 * kp ^ (2:ℕ) * w ^ (2:ℕ) * c ^ (2:ℕ) * q ^ (2:ℕ)))) + ((2 * kp * r * w ^ (2:ℕ) * c ^
  (2:ℕ) * q ^ (2:ℕ) - 2 * kp ^ (3:ℕ) * r * c * q ^ (3:ℕ)) + (-2 * kp ^ (2:ℕ) * r ^ (2:ℕ) * c *
  q ^ (3:ℕ) + (-kp ^ (2:ℕ) * w ^ (2:ℕ) * c * q ^ (3:ℕ) + kp ^ (3:ℕ) * r * q ^ (4:ℕ)))))))))

/-- The Horner form of `Criteria.BilharzPoly.quartic4 1 0` (proof device). -/
private def quartic4H (x3 y3 x2 y2 x1 _y1 _x0 _y0 : ℝ) : ℝ :=
  (y2 * (y2 * (-1)) + x3 * ((x1 * (-1) + y3 * y2) + x3 * x2))

/-- The Horner form of `Criteria.BilharzPoly.quartic6 1 0` (proof device). -/
private def quartic6H (x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  ((x1 * (x1 * x1) + y2 * (x1 * (y0 * 2 + y3 * x1) + y2 * ((y2 * (y1 * (-1)) + x2 * (x1 *
  (-1))) + y3 * y0))) + x3 * ((((y0 * (y0 * (-1)) + x2 * (x1 * (x1 * (-2)))) + y2 * (x1 * (y1 *
  (-3)) + y2 * x0)) + y3 * (x1 * (y0 * (-1) + y3 * (x1 * (-1))) + y2 * ((y2 * y1 + x2 * x1) +
  y3 * (y0 * (-1))))) + x3 * ((x0 * (x1 + y3 * (y2 * (-1))) + y1 * ((y0 * 2 + y3 * (x1 * 2)) +
  x3 * (y1 * (-1)))) + x2 * (((y2 * y1 + x2 * x1) + y3 * (y0 * (-1))) + x3 * (x0 * (-1))))))

/-- The Horner form of `Criteria.BilharzPoly.quartic8 1 0` (proof device). -/
private def quartic8H (x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) : ℝ :=
  (((y0 * (y0 * (y0 * y0)) + x1 * (y3 * (y0 * (y0 * (y0 * (-1)))) + x1 * (x2 * (y0 * (y0 *
  (-1))) + x1 * (y1 * y0 + x1 * x0)))) + y2 * (x0 * (y3 * (x1 * (x1 * x1)) + y2 * (x2 * (x1 *
  (x1 * (-1))) + y2 * (x1 * (y1 * (-1)) + y2 * x0))) + y0 * ((y0 * (y0 * (x2 * (-2) + y3 * (y3
  * (-1)))) + x1 * ((y1 * (y0 * 3) + x1 * (x0 * 4)) + y3 * (x1 * y1 + x2 * (y0 * (-1))))) + y2
  * (((x0 * (y0 * 2) + y2 * (y1 * (y1 * (-1)))) + y3 * (y1 * (y0 * 2) + x1 * (x0 * 3))) + x2 *
  ((x1 * (y1 * (-1)) + y2 * (x0 * (-2))) + x2 * y0))))) + x3 * (x0 * (x0 * (y3 * (y2 * (y2 *
  (y2 * (-1)))) + x3 * (x2 * (y2 * (y2 * (-1))) + x3 * (y2 * y1 + x3 * x0))) + x1 * ((x1 * (x1
  * (x2 * (-2) + y3 * (y3 * (-1)))) + y2 * ((x1 * (y1 * (-3)) + y2 * (x0 * 4)) + y3 * (y2 * y1
  + x2 * x1))) + x3 * (((x1 * (x0 * 2) + x3 * (y1 * (y1 * (-1)))) + y3 * (x1 * (y1 * 2) + y2 *
  (x0 * (-3)))) + x2 * ((y2 * y1 + x2 * x1) + x3 * (x0 * (-2)))))) + y0 * (((x0 * (x1 * (y0 *
  (-4)) + x3 * (y2 * (x0 * (-4)))) + x2 * (x1 * (y2 * (x0 * (-4)) + x2 * (y0 * 2)) + x3 * (x0 *
  (y0 * 3) + x2 * (y2 * (x0 * 2) + x2 * (y0 * (-1)))))) + y1 * (((y0 * (y0 * (-3)) + x2 * (x1 *
  (x1 * (-2)))) + y2 * ((x1 * (y1 * (-3)) + y2 * x0) + x2 * y0)) + x3 * ((x1 * (x0 * 5) + y1 *
  (y0 * 3 + x3 * (y1 * (-1)))) + x2 * ((y2 * y1 + x2 * x1) + x3 * (x0 * (-3)))))) + y3 * (((x3
  * (x3 * (x0 * (x0 * 3))) + y2 * (x3 * (y1 * (x0 * (-1))) + y2 * (y1 * y1 + x2 * (x0 * 2)))) +
  x1 * (x0 * ((x1 * (-1) + y3 * (y2 * (-3))) + x3 * (x2 * (-1))) + y1 * ((x2 * y2 + y3 * (x1 *
  (-1))) + x3 * (y1 * 2)))) + y0 * (((x1 * (y1 * (-1)) + y2 * (x0 * (-5))) + x2 * ((y0 * 3 + x2
  * (y2 * (-1))) + x3 * (y1 * (-3)))) + y3 * (((y2 * (y1 * (-2)) + x2 * x1) + y3 * y0) + x3 *
  (x0 * 3)))))))


@[tmio T, powerlib_foundation] private theorem quartic4_H (x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) :
    Criteria.BilharzPoly.quartic4 1 0 x3 y3 x2 y2 x1 y1 x0 y0 =
      quartic4H x3 y3 x2 y2 x1 y1 x0 y0 := by
  simp only [Criteria.BilharzPoly.quartic4, quartic4H]
  poly_rfl

@[tmio T, powerlib_foundation] private theorem quartic6_H (x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) :
    Criteria.BilharzPoly.quartic6 1 0 x3 y3 x2 y2 x1 y1 x0 y0 =
      quartic6H x3 y3 x2 y2 x1 y1 x0 y0 := by
  simp only [Criteria.BilharzPoly.quartic6, Criteria.BilharzPoly.quartic6_0,
    Criteria.BilharzPoly.quartic6_1, quartic6H]
  poly_rfl

@[tmio T, powerlib_foundation] private theorem quartic8_H (x3 y3 x2 y2 x1 y1 x0 y0 : ℝ) :
    Criteria.BilharzPoly.quartic8 1 0 x3 y3 x2 y2 x1 y1 x0 y0 =
      quartic8H x3 y3 x2 y2 x1 y1 x0 y0 := by
  simp only [Criteria.BilharzPoly.quartic8, Criteria.BilharzPoly.quartic8_0,
    Criteria.BilharzPoly.quartic8_1, Criteria.BilharzPoly.quartic8_2,
    Criteria.BilharzPoly.quartic8_3, Criteria.BilharzPoly.quartic8_4,
    Criteria.BilharzPoly.quartic8_5, quartic8H]
  poly_rfl

/-- `Δ₂ = Re b₃ = k_p + r`. -/
@[tmio M, powerlib_domain] theorem quarticBilharz2_eq (kp r w c P e q κ rv xv : ℝ) :
    Criteria.quarticBilharz2 1 (coeffs kp r w c P e q κ rv xv 3) (coeffs kp r w c P e q κ rv xv 2)
      (coeffs kp r w c P e q κ rv xv 1) (coeffs kp r w c P e q κ rv xv 0) = kp + r := by
  simp [Criteria.quarticBilharz2, Criteria.BilharzPoly.quartic2, coeffs]

/-- `Δ₄` in normalized parameters (17 terms). -/
@[tmio M, powerlib_domain] theorem quarticBilharz4_eq (kp r w c P e q κ rv xv : ℝ) :
    Criteria.quarticBilharz4 1 (coeffs kp r w c P e q κ rv xv 3) (coeffs kp r w c P e q κ rv xv 2)
      (coeffs kp r w c P e q κ rv xv 1) (coeffs kp r w c P e q κ rv xv 0) =
        delta4 kp r w c P e q κ rv xv := by
  simp only [Criteria.quarticBilharz4, coeffs, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one, Complex.one_re, Complex.one_im]
  rw [quartic4_H]
  simp only [quartic4H, delta4]
  poly_rfl

/-- `Δ₆ = k_p · delta6F` in normalized parameters. -/
@[tmio M, powerlib_domain] theorem quarticBilharz6_eq (kp r w c P e q κ rv xv : ℝ) :
    Criteria.quarticBilharz6 1 (coeffs kp r w c P e q κ rv xv 3) (coeffs kp r w c P e q κ rv xv 2)
      (coeffs kp r w c P e q κ rv xv 1) (coeffs kp r w c P e q κ rv xv 0) =
        kp * delta6F kp r w c P e q κ rv xv := by
  simp only [Criteria.quarticBilharz6, coeffs, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one, Complex.one_re, Complex.one_im]
  rw [quartic6_H]
  simp only [quartic6H, delta6F]
  poly_rfl

/-- `Δ₈ = k_p² q · delta8F` in normalized parameters. -/
@[tmio M, powerlib_domain] theorem quarticBilharz8_eq (kp r w c P e q κ rv xv : ℝ) :
    Criteria.quarticBilharz8 1 (coeffs kp r w c P e q κ rv xv 3) (coeffs kp r w c P e q κ rv xv 2)
      (coeffs kp r w c P e q κ rv xv 1) (coeffs kp r w c P e q κ rv xv 0) =
        kp ^ 2 * q * delta8F kp r w c P e q κ rv xv := by
  simp only [Criteria.quarticBilharz8, coeffs, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one, Complex.one_re, Complex.one_im]
  rw [quartic8_H]
  simp only [quartic8H, delta8F, delta8F0, delta8F1, delta8F2]
  poly_rfl

/-- **The ideal design** (`e = κ = r_v = x_v = 0`): `Δ₄ = (k_p + r) G`, `Δ₆ = k_p F₅₂`,
`Δ₈ = k_p² q F₁₄₇`. -/
@[tmio M, powerlib_domain] theorem ideal_eq (kp r w c P q : ℝ) :
    delta4 kp r w c P 0 q 0 0 0 = (kp + r) * idealDelta4F kp r w c P q ∧
      delta6F kp r w c P 0 q 0 0 0 = idealDelta6F kp r w c P q ∧
      delta8F kp r w c P 0 q 0 0 0 = idealDelta8F kp r w c P q := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [delta4, idealDelta4F]; poly_rfl
  · simp only [delta6F, idealDelta6F]; poly_rfl
  · simp only [delta8F, delta8F0, delta8F1, delta8F2, idealDelta8F]; poly_rfl

end PZLevel

namespace Params

variable (p : Params)

/-- **The quartic factor in normalized parameters** (`C_f, L_g ≠ 0`). -/
@[tmio M, powerlib_domain] theorem pzCoeff_eq (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0) :
    p.pzCoeff = PZLevel.coeffs (p.Kpc / p.Lf) (p.Rg / p.Lg) p.ω0 (1 / (p.Cf * p.Lg))
      (p.Kpv / p.Cf) (1 - p.kdv) (p.Kiv / p.Cf) ((1 - p.kff) / (p.Cf * p.Lg)) (p.Rv / p.Lg)
      (p.Xv / p.Lg) := by
  obtain ⟨r2, i2, r1, i1, r0, i0⟩ := p.voltageA_parts hCf hLg
  have zr : (p.Zg / p.Lg).re = p.Rg / p.Lg := by rw [Complex.div_ofReal_re, Zg_eq]; simp
  have zi : (p.Zg / p.Lg).im = p.ω0 := by
    rw [Complex.div_ofReal_im, Zg_eq]; simp; field_simp
  funext k
  fin_cases k <;> apply Complex.ext <;>
    simp [pzCoeff, PZLevel.coeffs, Complex.mul_re, Complex.mul_im, r2, i2, r1, i1, r0, i0, zr,
      zi, -mul_eq_mul_left_iff] <;> field_simp <;> ring

/-- **The boundary layer under pole–zero cancellation, explicit** (`L_f, C_f, L_g ≠ 0`,
`K_ic L_f = K_pc R_f`, every other parameter value): with `k_p = K_pc/L_f`, `r = R_g/L_g`,
`q = K_iv/C_f` and the normalized parameters of `PZLevel.coeffs`, spectrally stable iff
`R_f/L_f > 0`, `k_p + r > 0`, `PZLevel.delta4 > 0`, `k_p · PZLevel.delta6F > 0` and
`k_p² q · PZLevel.delta8F > 0`. -/
@[tmio M, powerlib_domain] theorem spectrallyStable_fastBlock_iff_pz_explicit (hLf : p.Lf ≠ 0)
    (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0) (hpz : p.Kic * p.Lf = p.Kpc * p.Rf) (δ : ℝ) :
    Linear.SpectrallyStable (p.fastBlock δ) ↔
      0 < p.Rf / p.Lf ∧ 0 < p.Kpc / p.Lf + p.Rg / p.Lg ∧
        0 < PZLevel.delta4 (p.Kpc / p.Lf) (p.Rg / p.Lg) p.ω0 (1 / (p.Cf * p.Lg)) (p.Kpv / p.Cf)
          (1 - p.kdv) (p.Kiv / p.Cf) ((1 - p.kff) / (p.Cf * p.Lg)) (p.Rv / p.Lg) (p.Xv / p.Lg) ∧
        0 < p.Kpc / p.Lf * PZLevel.delta6F (p.Kpc / p.Lf) (p.Rg / p.Lg) p.ω0 (1 / (p.Cf * p.Lg))
          (p.Kpv / p.Cf) (1 - p.kdv) (p.Kiv / p.Cf) ((1 - p.kff) / (p.Cf * p.Lg)) (p.Rv / p.Lg)
          (p.Xv / p.Lg) ∧
        0 < (p.Kpc / p.Lf) ^ 2 * (p.Kiv / p.Cf) * PZLevel.delta8F (p.Kpc / p.Lf) (p.Rg / p.Lg)
          p.ω0 (1 / (p.Cf * p.Lg)) (p.Kpv / p.Cf) (1 - p.kdv) (p.Kiv / p.Cf)
          ((1 - p.kff) / (p.Cf * p.Lg)) (p.Rv / p.Lg) (p.Xv / p.Lg) := by
  rw [p.spectrallyStable_fastBlock_iff_pz hLf hCf hLg hpz δ, p.pzCoeff_eq hCf hLg,
    PZLevel.quarticBilharz2_eq, PZLevel.quarticBilharz4_eq, PZLevel.quarticBilharz6_eq,
    PZLevel.quarticBilharz8_eq]

/-- **The ideal design under pole–zero cancellation** (`L_f, C_f, L_g ≠ 0`,
`K_ic L_f = K_pc R_f`, `k_ff = k_dv = 1`, `Z_v = 0`): spectrally stable iff `R_f/L_f > 0`,
`k_p + r > 0`, `G > 0` (the bound `k_p q < k_p² r + k_p r² + k_p² P + k_p c + r c` on the
voltage-loop integral gain), `k_p F₅₂ > 0` and `k_p² q F₁₄₇ > 0`. -/
@[tmio M, powerlib_domain] theorem spectrallyStable_fastBlock_iff_pz_ideal (hLf : p.Lf ≠ 0)
    (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0) (hpz : p.Kic * p.Lf = p.Kpc * p.Rf)
    (hid : p.kff = 1 ∧ p.kdv = 1 ∧ p.Rv = 0 ∧ p.Xv = 0) (δ : ℝ) :
    Linear.SpectrallyStable (p.fastBlock δ) ↔
      0 < p.Rf / p.Lf ∧ 0 < p.Kpc / p.Lf + p.Rg / p.Lg ∧
        0 < PZLevel.idealDelta4F (p.Kpc / p.Lf) (p.Rg / p.Lg) p.ω0 (1 / (p.Cf * p.Lg))
          (p.Kpv / p.Cf) (p.Kiv / p.Cf) ∧
        0 < p.Kpc / p.Lf * PZLevel.idealDelta6F (p.Kpc / p.Lf) (p.Rg / p.Lg) p.ω0
          (1 / (p.Cf * p.Lg)) (p.Kpv / p.Cf) (p.Kiv / p.Cf) ∧
        0 < (p.Kpc / p.Lf) ^ 2 * (p.Kiv / p.Cf) * PZLevel.idealDelta8F (p.Kpc / p.Lf)
          (p.Rg / p.Lg) p.ω0 (1 / (p.Cf * p.Lg)) (p.Kpv / p.Cf) (p.Kiv / p.Cf) := by
  obtain ⟨hff, hdv, hRv, hXv⟩ := hid
  obtain ⟨e4, e6, e8⟩ := PZLevel.ideal_eq (p.Kpc / p.Lf) (p.Rg / p.Lg) p.ω0 (1 / (p.Cf * p.Lg))
    (p.Kpv / p.Cf) (p.Kiv / p.Cf)
  rw [p.spectrallyStable_fastBlock_iff_pz_explicit hLf hCf hLg hpz δ, hff, hdv, hRv, hXv]
  simp only [sub_self, zero_div, e4, e6, e8]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, pos_of_mul_pos_right h3 h2.le, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, mul_pos h2 h3, h4, h5⟩

end Params
