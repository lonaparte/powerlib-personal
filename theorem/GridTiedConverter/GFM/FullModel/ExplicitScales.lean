import theorem.GridTiedConverter.GFM.FullModel.BoundaryLayer
import theorem.GridTiedConverter.GFM.FullModel.Jacobian

/-! # The 13-state grid-forming converter: closed-form Lyapunov matrices, `μ*` and `ε*`

Model boundary.
The 13-state model of `theorem/GridTiedConverter/GFM/FullModel/Basic.lean`, its fast block split
into the current loop and the voltage level
(`theorem/GridTiedConverter/GFM/FullModel/BoundaryLayer.lean`) and its reduced Jacobian
(`theorem/GridTiedConverter/GFM/FullModel/Saddle.lean`). Design with full
line-current feed-forward `k_ff = 1`, no virtual impedance `Z_v = 0`, any decoupling gain `k_dv`,
positive `L_f, C_f, L_g, R_g`, `K_pc + R_f`, `K_ic, K_pv, K_iv`; for the reduced Jacobian, no Q–V
droop (`n_q = 0`) and positive `M, D, ω_q` and synchronizing slope `K = ∂P/∂δ`. Constant
matrices, local (equilibrium-level) statements. The Lyapunov matrices solve `P M + Mᴴ P = −1`
exactly; they are rational functions of the parameters, defined by back substitution in the
Lyapunov equations.

Source: the continuous Lyapunov equation and its unique positive definite solution for a Hurwitz
matrix (LeanForControl `IsHurwitz.exists_posDef_unique_solution_continuous_lyapunov`); the
explicit `ε* = 1/(2c + 1)` of Kokotović–Khalil–O'Reilly, *Singular Perturbation Methods in
Control* (1986), Ch. 2 (`SingularPerturbation.LinearSP.epsStar`); the closed forms were solved
symbolically (sympy) and are verified here by the kernel.

Results.
* The voltage level, `VoltageLevel.shape A B c g r w = [[−(A + jB), 0, c], [g, −(r + jw), 0],
  [−1, 0, 0]]`: `VoltageLevel.lyap` (entries `VoltageLevel.x0 … x8`, with
  `VoltageLevel.den = |z² + (A − jB) z + c|²`, `z = r + jw`) and `VoltageLevel.lyap_lyapunov`;
  `VoltageLevel.den_ne_zero` for `A, c, r > 0`. `Params.voltageMatrix_eq_shape`,
  `Params.voltageLyap`, `Params.voltageLyap_lyapunov`, `Params.posDef_realify_voltageLyap`.
* The current loop: `Params.currentLyap` (`[[(k+1)/(2ak), −1/(2k)], [−1/(2k), (a²+k²+k)/(2ak)]]`,
  `a = (K_pc + R_f)/L_f`, `k = K_ic/L_f`), `Params.currentLyap_lyapunov`,
  `Params.posDef_realify_currentLyap`.
* `Params.voltageFromCurrent`, `Params.fastMatrix_toBlocks₂₁`: the voltage rows against the
  current loop. **`Params.muStarClosed`**, a closed formula of the parameters:
  `1/(2c + 1)`, `c = S(2S + 1)/2 + |P₂ H C|₁`, `S = |P₀ C|₁ + |P₂ H R|₁` with the real forms of
  `P₀ = voltageLyap`, `P₂ = currentLyap`, `H = currentGain`, `R = voltageMatrix`,
  `C = voltageFromCurrent` (`|realify N|₁ = Σ 2(|Re Nᵢⱼ| + |Im Nᵢⱼ|)`,
  `SingularPerturbation.absSum_realify`); `Params.muStar_eq_closed`: it is `Params.muStar` at the
  closed-form Lyapunov matrices.
  **`Params.spectrallyStable_fastBlock_currentScaled_of_lt_muStarClosed`**: the boundary layer
  of `currentScaled μ` is spectrally stable at every angle for every `μ ∈ (0, muStarClosed)` —
  the time-scale sufficient condition with `μ*` an explicit formula.
* The reduced Jacobian without droop: `SwingLevel.shape K D M ω_q q`, `SwingLevel.lyap`
  (back substitution, `SwingLevel.y0 … y5`), `SwingLevel.lyap_lyapunov`;
  `Params.reducedJacobian_eq_shape`, `Params.swingLyap`, `Params.swingLyap_lyapunov`,
  `Params.isHurwitz_reducedJacobian_of_noDroop`.

Family and connection conclusions.
* `mem_den_LES_of_lt_epsStar_of_noDroop` (connection, `FullModel.family`): without droop, with
  positive `M, D, ω_q` and slope `K` at a balanced quasi-steady point, and a positive definite
  Lyapunov matrix `P₂` of the fast block, the time-scaled full model is locally exponentially
  stable for every `ε ∈ (0, Params.epsStar δ* Q* (swingLyap δ* Q*) P₂)` — the reduced Lyapunov
  matrix in closed form (`Params.epsStar_eq_closed` gives the Jacobian in closed form); the fast
  block is a `10 × 10` matrix without a closed-form Lyapunov matrix, so `P₂` stays data.
-/

noncomputable section
namespace powerlib.GFM.FullModel
open Complex Matrix
open powerlib.SingularPerturbation (realify absSum)

/-! ### The voltage level -/

namespace VoltageLevel

/-- Real part of `q(z) = z² + (A − jB) z + c` at `z = r + jw`. -/
def qr (A B c r w : ℝ) : ℝ := r ^ 2 - w ^ 2 + A * r + B * w + c

/-- Imaginary part of `q(z) = z² + (A − jB) z + c` at `z = r + jw`. -/
def qi (A B r w : ℝ) : ℝ := 2 * r * w + A * w - B * r

/-- `|q(z)|²`. -/
def den (A B c r w : ℝ) : ℝ := qr A B c r w ^ 2 + qi A B r w ^ 2

/-- The voltage level `[[−(A + jB), 0, c], [g, −(r + jw), 0], [−1, 0, 0]]`. -/
def shape (A B c g r w : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-((A : ℂ) + B * I), 0, c; g, -((r : ℂ) + w * I), 0; -1, 0, 0]

/-- Entry `(v_c, i_g)` (real part) of the Lyapunov matrix. -/
def x3 (A B c g r w : ℝ) : ℝ := g * (r * qr A B c r w + w * qi A B r w) / (2 * r * den A B c r w)
/-- Entry `(v_c, i_g)` (imaginary part). -/
def x4 (A B c g r w : ℝ) : ℝ := g * (w * qr A B c r w - r * qi A B r w) / (2 * r * den A B c r w)
/-- Entry `(i_g, ζ)` (real part). -/
def x7 (A B c g r w : ℝ) : ℝ := c * g * qr A B c r w / (2 * r * den A B c r w)
/-- Entry `(i_g, ζ)` (imaginary part). -/
def x8 (A B c g r w : ℝ) : ℝ := c * g * qi A B r w / (2 * r * den A B c r w)
/-- Entry `(v_c, ζ)` (real part). -/
def x5 (c : ℝ) : ℝ := -1 / (2 * c)
/-- Entry `(i_g, i_g)`. -/
def x1 (r : ℝ) : ℝ := 1 / (2 * r)
/-- Entry `(v_c, ζ)` (imaginary part). -/
def x6 (A B c g r w : ℝ) : ℝ := (B * x5 c + g * x8 A B c g r w) / A
/-- Entry `(v_c, v_c)`. -/
def x0 (A B c g r w : ℝ) : ℝ := (1 / 2 + g * x3 A B c g r w + 1 / (2 * c)) / A
/-- Entry `(ζ, ζ)`. -/
def x2 (A B c g r w : ℝ) : ℝ :=
  c * x0 A B c g r w - (A * x5 c + B * x6 A B c g r w) + g * x7 A B c g r w

/-- The Hermitian Lyapunov matrix of the voltage level. -/
def lyap (A B c g r w : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(x0 A B c g r w : ℂ), x3 A B c g r w + x4 A B c g r w * I, (x5 c : ℂ) + x6 A B c g r w * I;
    x3 A B c g r w - x4 A B c g r w * I, (x1 r : ℂ), x7 A B c g r w + x8 A B c g r w * I;
    (x5 c : ℂ) - x6 A B c g r w * I, x7 A B c g r w - x8 A B c g r w * I, x2 A B c g r w]

/-- **The closed-form Lyapunov matrix of the voltage level**: `P M + Mᴴ P = −1`. -/
@[tmio M, powerlib_domain] theorem lyap_lyapunov (A B c g r w : ℝ) (hA : A ≠ 0) (hc : c ≠ 0)
    (hr : r ≠ 0) (hD : den A B c r w ≠ 0) :
    lyap A B c g r w * shape A B c g r w + (shape A B c g r w)ᴴ * lyap A B c g r w = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lyap, shape, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply] <;>
    apply Complex.ext <;> simp <;> (try simp only [x0, x1, x2, x3, x4, x5, x6, x7, x8]) <;>
    field_simp <;> (try simp only [den, qr, qi]) <;> ring_nf

/-- `|q(z)|² ≠ 0` for `A, c, r > 0`: a zero would make `r − jw` a root, with positive real part, of
the Hurwitz polynomial `s² + (A + jB) s + c`. -/
@[tmio M, powerlib_domain] theorem den_ne_zero {A B c r w : ℝ} (hA : 0 < A) (hc : 0 < c)
    (hr : 0 < r) : den A B c r w ≠ 0 := by
  intro h0
  obtain ⟨h1, h2⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg (qr A B c r w))
    (sq_nonneg (qi A B r w))).mp h0
  have h1 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
  have h2 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  have hroot : ((r : ℂ) - w * I) ^ 2 + (⟨A, B⟩ : ℂ) * ((r : ℂ) - w * I) + (c : ℂ) = 0 := by
    simp only [qr, qi] at h1 h2
    apply Complex.ext <;> simp [sq, Complex.mul_re, Complex.mul_im] <;> linarith
  have := (Criteria.complexQuadratic_realConst_roots_re_neg_iff A B c).mpr ⟨hA, hc⟩ _ hroot
  simp at this
  linarith

end VoltageLevel

/-! ### The current loop shape -/

namespace CurrentLoop

/-- The current loop `[[−a, k], [−1, 0]]`. -/
def shape (a k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![-(a : ℂ), k; -1, 0]

/-- Entry `(i, i)` of the Lyapunov matrix. -/
def l00 (a k : ℝ) : ℝ := (k + 1) / (2 * a * k)
/-- Entry `(i, ξ)`. -/
def l01 (k : ℝ) : ℝ := -1 / (2 * k)
/-- Entry `(ξ, ξ)`. -/
def l11 (a k : ℝ) : ℝ := (a ^ 2 + k ^ 2 + k) / (2 * a * k)

/-- `[[(k + 1)/(2ak), −1/(2k)], [−1/(2k), (a² + k² + k)/(2ak)]]`. -/
def lyap (a k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(l00 a k : ℂ), (l01 k : ℂ); (l01 k : ℂ), (l11 a k : ℂ)]

/-- **The closed-form Lyapunov matrix of the current loop**: `P M + Mᴴ P = −1`. -/
@[tmio M, powerlib_domain] theorem lyap_lyapunov (a k : ℝ) (ha : a ≠ 0) (hk : k ≠ 0) :
    lyap a k * shape a k + (shape a k)ᴴ * lyap a k = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lyap, shape, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
    apply Complex.ext <;> simp <;> (try simp only [l00, l01, l11]) <;> field_simp <;> ring_nf

end CurrentLoop

/-! ### The reduced Jacobian without droop -/

namespace SwingLevel

/-- The reduced Jacobian without droop, `[[0, 1, 0], [−K/M, −D/M, 0], [q, 0, −ω_q]]`. -/
def shape (K D M wq q : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; -K / M, -D / M, 0; q, 0, -wq]

/-- Entry `(Q_f, Q_f)` of the Lyapunov matrix. -/
def y2 (wq : ℝ) : ℝ := 1 / (2 * wq)
/-- Entry `(Δω, Q_f)`. -/
def y5 (K D M wq q : ℝ) : ℝ := M * q * y2 wq / (K + D * wq + M * wq ^ 2)
/-- Entry `(δ, Q_f)`. -/
def y4 (K D M wq q : ℝ) : ℝ := (D / M + wq) * y5 K D M wq q
/-- Entry `(δ, Δω)`. -/
def y3 (K D M wq q : ℝ) : ℝ := M * (2 * q * y4 K D M wq q + 1) / (2 * K)
/-- Entry `(Δω, Δω)`. -/
def y1 (K D M wq q : ℝ) : ℝ := M * (2 * y3 K D M wq q + 1) / (2 * D)
/-- Entry `(δ, δ)`. -/
def y0 (K D M wq q : ℝ) : ℝ :=
  D * y3 K D M wq q / M + K * y1 K D M wq q / M - q * y5 K D M wq q

/-- The Lyapunov matrix of the reduced Jacobian without droop (back substitution). -/
def lyap (K D M wq q : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![y0 K D M wq q, y3 K D M wq q, y4 K D M wq q;
    y3 K D M wq q, y1 K D M wq q, y5 K D M wq q;
    y4 K D M wq q, y5 K D M wq q, y2 wq]

/-- **The closed-form Lyapunov matrix of the reduced Jacobian**: `P J + Jᵀ P = −1`. -/
@[tmio M, powerlib_domain] theorem lyap_lyapunov (K D M wq q : ℝ) (hK : K ≠ 0) (hD : D ≠ 0)
    (hM : M ≠ 0) (hwq : wq ≠ 0) (hS : K + D * wq + M * wq ^ 2 ≠ 0) :
    lyap K D M wq q * shape K D M wq q + (shape K D M wq q)ᵀ * lyap K D M wq q = -1 := by
  have hS2 : K + wq * D + wq ^ 2 * M ≠ 0 := by convert hS using 1; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lyap, shape, Matrix.mul_apply, Fin.sum_univ_three] <;>
    (try simp only [y0, y1, y2, y3, y4, y5]) <;> field_simp <;> ring_nf
  field_simp
  ring_nf

end SwingLevel

namespace Params

variable (p : Params)

/-- With `k_ff = 1`, `Z_v = 0`, `L_g ≠ 0`, the voltage level is
`VoltageLevel.shape (K_pv/C_f) ((1 − k_dv)ω₀C_f/C_f) (K_iv/C_f) (1/L_g) (R_g/L_g) ω₀`. -/
@[tmio M, powerlib_domain] theorem voltageMatrix_eq_shape (hkff : p.kff = 1) (hZv : p.Zv = 0)
    (hLg : p.Lg ≠ 0) :
    p.voltageMatrix = VoltageLevel.shape (p.Kpv / p.Cf) ((1 - p.kdv) * p.Bf / p.Cf)
      (p.Kiv / p.Cf) (1 / p.Lg) (p.Rg / p.Lg) p.ω0 := by
  have hLg' : (p.Lg : ℂ) ≠ 0 := by exact_mod_cast hLg
  ext i j
  fin_cases i <;> fin_cases j <;> simp [voltageMatrix, VoltageLevel.shape, hkff, hZv, Zg_eq]
  · ring
  · field_simp

/-- The closed-form Lyapunov matrix of the voltage level of `p`. -/
def voltageLyap : Matrix (Fin 3) (Fin 3) ℂ :=
  VoltageLevel.lyap (p.Kpv / p.Cf) ((1 - p.kdv) * p.Bf / p.Cf) (p.Kiv / p.Cf) (1 / p.Lg)
    (p.Rg / p.Lg) p.ω0

/-- `voltageLyap` solves the Lyapunov equation of the voltage level. -/
@[tmio M, powerlib_domain] theorem voltageLyap_lyapunov (hkff : p.kff = 1) (hZv : p.Zv = 0)
    (hCf : 0 < p.Cf) (hLg : 0 < p.Lg) (hRg : 0 < p.Rg) (hKpv : 0 < p.Kpv) (hKiv : 0 < p.Kiv) :
    p.voltageLyap * p.voltageMatrix + p.voltageMatrixᴴ * p.voltageLyap = -1 := by
  rw [p.voltageMatrix_eq_shape hkff hZv hLg.ne', voltageLyap]
  exact VoltageLevel.lyap_lyapunov _ _ _ _ _ _ (div_pos hKpv hCf).ne' (div_pos hKiv hCf).ne'
    (div_pos hRg hLg).ne' (VoltageLevel.den_ne_zero (div_pos hKpv hCf) (div_pos hKiv hCf)
      (div_pos hRg hLg))

/-- The real form of `voltageLyap` is positive definite (the unique solution for a stable
voltage level, `SingularPerturbation.posDef_of_lyapunov_of_spectrallyStable`). -/
@[tmio M, powerlib_domain] theorem posDef_realify_voltageLyap (hkff : p.kff = 1) (hZv : p.Zv = 0)
    (hCf : 0 < p.Cf) (hLg : 0 < p.Lg) (hRg : 0 < p.Rg) (hKpv : 0 < p.Kpv) (hKiv : 0 < p.Kiv) :
    (realify p.voltageLyap).PosDef :=
  SingularPerturbation.posDef_of_lyapunov_of_spectrallyStable
    ((p.spectrallyStable_voltageMatrix_iff hkff hZv).mpr
      ⟨div_pos hKpv hCf, div_pos hKiv hCf, div_pos hRg hLg⟩)
    (SingularPerturbation.realify_lyapunov
      (p.voltageLyap_lyapunov hkff hZv hCf hLg hRg hKpv hKiv))

/-! ### The current loop -/

/-- With `a = (K_pc + R_f)/L_f`, `k = K_ic/L_f`, the current loop is `[[−a, k], [−1, 0]]`. -/
@[tmio M, powerlib_domain] theorem currentMatrix_eq_shape :
    p.currentMatrix = CurrentLoop.shape ((p.Kpc + p.Rf) / p.Lf) (p.Kic / p.Lf) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [currentMatrix, CurrentLoop.shape]
  ring

/-- The closed-form Lyapunov matrix of the current loop of `p`. -/
def currentLyap : Matrix (Fin 2) (Fin 2) ℂ :=
  CurrentLoop.lyap ((p.Kpc + p.Rf) / p.Lf) (p.Kic / p.Lf)

/-- `currentLyap` solves the Lyapunov equation of the current loop. -/
@[tmio M, powerlib_domain] theorem currentLyap_lyapunov (ha : (p.Kpc + p.Rf) / p.Lf ≠ 0)
    (hk : p.Kic / p.Lf ≠ 0) :
    p.currentLyap * p.currentMatrix + p.currentMatrixᴴ * p.currentLyap = -1 := by
  rw [currentMatrix_eq_shape, currentLyap]
  exact CurrentLoop.lyap_lyapunov _ _ ha hk

/-- The real form of `currentLyap` is positive definite. -/
@[tmio M, powerlib_domain] theorem posDef_realify_currentLyap (h1 : 0 < (p.Kpc + p.Rf) / p.Lf)
    (h0 : 0 < p.Kic / p.Lf) : (realify p.currentLyap).PosDef :=
  SingularPerturbation.posDef_of_lyapunov_of_spectrallyStable
    (p.spectrallyStable_currentMatrix_iff.mpr ⟨h1, h0⟩)
    (SingularPerturbation.realify_lyapunov (p.currentLyap_lyapunov h1.ne' h0.ne'))

/-! ### `μ*` in closed form -/

/-- The voltage rows against the current loop: only the capacitor sees the filter current. -/
def voltageFromCurrent : Matrix (Fin 3) (Fin 2) ℂ := !![1 / (p.Cf : ℂ), 0; 0, 0; 0, 0]

@[tmio M, powerlib_domain] theorem fastMatrix_toBlocks₂₁ :
    ((p.fastMatrix 0).reindex loopSplit loopSplit).toBlocks₂₁ = p.voltageFromCurrent := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.toBlocks₂₁, loopSplit, fastMatrix, voltageFromCurrent]

/-- **`μ*` as a closed formula of the parameters**: Kokotović's `1/(2c + 1)` with
`S = |P₀ C|₁ + |P₂ H R|₁`, `c = S (2S + 1)/2 + |P₂ H C|₁` for the real forms of
`P₀ = voltageLyap`, `P₂ = currentLyap`, `H = currentGain`, `R = voltageMatrix`,
`C = voltageFromCurrent`. -/
def muStarClosed : ℝ :=
  1 / (2 * ((absSum (realify (p.voltageLyap * p.voltageFromCurrent)) +
      absSum (realify (p.currentLyap * p.currentGain * p.voltageMatrix))) *
    (2 * (absSum (realify (p.voltageLyap * p.voltageFromCurrent)) +
      absSum (realify (p.currentLyap * p.currentGain * p.voltageMatrix))) + 1) / 2 +
    absSum (realify (p.currentLyap * p.currentGain * p.voltageFromCurrent))) + 1)

/-- `muStarClosed` is `muStar` at the closed-form Lyapunov matrices. -/
@[tmio M, powerlib_domain] theorem muStar_eq_closed (hLf : 0 < p.Lf) (hKpc : 0 < p.Kpc + p.Rf)
    (hKic : 0 < p.Kic) :
    p.muStar (realify p.voltageLyap) (realify p.currentLyap) = p.muStarClosed := by
  obtain ⟨h11, hH, hR⟩ := p.fastMatrix_blocks hKic.ne'
  obtain ⟨r11, r12, r21, r22⟩ := SingularPerturbation.toBlocks_reindex_realify loopSplit
    (p.fastMatrix 0)
  have hA := p.spectrallyStable_currentMatrix_iff.mpr ⟨div_pos hKpc hLf, div_pos hKic hLf⟩
  rw [muStar, fastBlock_eq_realify,
    SingularPerturbation.graphEpsStar_eq_of_blocks (SingularPerturbation.realifySplit loopSplit)
      (A := realify p.currentMatrix) (H := realify p.currentGain) (R := realify p.voltageMatrix)
      (by rw [r11, h11]) (SingularPerturbation.isUnit_det_of_spectrallyStable hA)
      (by rw [r12, ← SingularPerturbation.realify_mul, ← SingularPerturbation.realify_add, hH,
        SingularPerturbation.realify_zero])
      (by rw [r21, r22, ← SingularPerturbation.realify_mul, ← SingularPerturbation.realify_add,
        hR]),
    r21, p.fastMatrix_toBlocks₂₁]
  simp only [← SingularPerturbation.realify_mul, muStarClosed]

/-- **Time-scale separation with an explicit `μ*`.** With `k_ff = 1`, `Z_v = 0`, positive
`L_f, C_f, L_g, R_g`, `K_pc + R_f`, `K_ic, K_pv, K_iv`, the boundary layer of `currentScaled μ` is
spectrally stable at every angle for every `μ ∈ (0, muStarClosed)`. -/
@[tmio M, powerlib_domain] theorem spectrallyStable_fastBlock_currentScaled_of_lt_muStarClosed
    (hLf : 0 < p.Lf) (hCf : 0 < p.Cf) (hLg : 0 < p.Lg) (hRg : 0 < p.Rg)
    (hKpc : 0 < p.Kpc + p.Rf) (hKic : 0 < p.Kic) (hKpv : 0 < p.Kpv) (hKiv : 0 < p.Kiv)
    (hkff : p.kff = 1) (hZv : p.Zv = 0) {μ : ℝ} (hμ : 0 < μ) (hlt : μ < p.muStarClosed)
    (δ : ℝ) : Linear.SpectrallyStable ((p.currentScaled μ).fastBlock δ) :=
  p.spectrallyStable_fastBlock_currentScaled_of_lt hKic.ne'
    (p.posDef_realify_voltageLyap hkff hZv hCf hLg hRg hKpv hKiv)
    (p.posDef_realify_currentLyap (div_pos hKpc hLf) (div_pos hKic hLf))
    (SingularPerturbation.realify_lyapunov (p.voltageLyap_lyapunov hkff hZv hCf hLg hRg hKpv hKiv))
    (SingularPerturbation.realify_lyapunov
      (p.currentLyap_lyapunov (div_pos hKpc hLf).ne' (div_pos hKic hLf).ne'))
    hμ (by rw [p.muStar_eq_closed hLf hKpc hKic]; exact hlt) δ

/-! ### `ε*` with the reduced Lyapunov matrix in closed form -/

/-- Without droop the reduced Jacobian is `SwingLevel.shape K D M ω_q q` with the power–angle
slope `K = ∂P/∂δ` and `q = ω_q ∂Q/∂δ`. -/
@[tmio M, powerlib_domain] theorem reducedJacobian_eq_shape (hnq : p.nq = 0) (δ Qf : ℝ) :
    p.reducedJacobian δ Qf = SwingLevel.shape (p.powerSlope δ (p.emf Qf)) p.D p.M p.ωq
      (p.ωq * p.reactiveSlope δ (p.emf Qf)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reducedJacobian, SwingLevel.shape, hnq]

/-- The closed-form Lyapunov matrix of the reduced Jacobian without droop. -/
def swingLyap (δ Qf : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  SwingLevel.lyap (p.powerSlope δ (p.emf Qf)) p.D p.M p.ωq (p.ωq * p.reactiveSlope δ (p.emf Qf))

/-- `swingLyap` solves the Lyapunov equation of the reduced Jacobian without droop. -/
@[tmio M, powerlib_domain] theorem swingLyap_lyapunov (hnq : p.nq = 0) (hM : 0 < p.M)
    (hD : 0 < p.D) (hωq : 0 < p.ωq) {δ : ℝ} (Qf : ℝ) (hK : 0 < p.powerSlope δ (p.emf Qf)) :
    p.swingLyap δ Qf * p.reducedJacobian δ Qf + (p.reducedJacobian δ Qf)ᵀ * p.swingLyap δ Qf =
      -1 := by
  rw [p.reducedJacobian_eq_shape hnq, swingLyap]
  exact SwingLevel.lyap_lyapunov _ _ _ _ _ hK.ne' hD.ne' hM.ne' hωq.ne' (by positivity)

/-- `swingLyap` is positive definite (the unique solution for a Hurwitz reduced Jacobian). -/
@[tmio M, powerlib_domain] theorem posDef_swingLyap (hnq : p.nq = 0) (hM : 0 < p.M)
    (hD : 0 < p.D) (hωq : 0 < p.ωq) {δ : ℝ} (Qf : ℝ) (hK : 0 < p.powerSlope δ (p.emf Qf)) :
    (p.swingLyap δ Qf).PosDef :=
  SingularPerturbation.posDef_of_lyapunov_of_spectrallyStable
    ((Linear.spectrallyStable_iff_isHurwitz _).mpr
      (p.isHurwitz_reducedJacobian_of_noDroop hnq hM hD hωq Qf hK))
    (p.swingLyap_lyapunov hnq hM hD hωq Qf hK)

end Params

/-- **Stability transfer with the reduced Lyapunov matrix in closed form (connection).** Without
droop, with positive `M, D, ω_q` and power–angle slope `∂P/∂δ` at a balanced quasi-steady point
and a positive definite Lyapunov matrix `P₂` of the fast block, the time-scaled full model is in
the denotation of local exponential stability for every
`ε ∈ (0, Params.epsStar δ* Q* (swingLyap δ* Q*) P₂)`. -/
@[tmio TM, powerlib_domain] theorem mem_den_LES_of_lt_epsStar_of_noDroop (m : Model)
    (hLf : m.p.Lf ≠ 0) (hCf : m.p.Cf ≠ 0) (hLg : m.p.Lg ≠ 0) (hKic : m.p.Kic ≠ 0)
    (hKiv : m.p.Kiv ≠ 0) (hZt : m.p.Zt ≠ 0) (hnq : m.p.nq = 0) (hM : 0 < m.p.M)
    (hD : 0 < m.p.D) (hωq : 0 < m.p.ωq) (hK : 0 < m.p.powerSlope m.δ (m.p.emf m.Qf))
    (hP : m.p.Pq m.δ (m.p.emf m.Qf) = m.p.Pref) (hQ : m.p.Qq m.δ (m.p.emf m.Qf) = m.Qf)
    {P2 : Matrix (Fin 5 × Fin 2) (Fin 5 × Fin 2) ℝ} (hP2 : P2.PosDef)
    (hL2 : P2 * m.p.fastBlock m.δ + (m.p.fastBlock m.δ)ᵀ * P2 = -1) :
    connection% (∀ ε, 0 < ε → ε < m.p.epsStar m.δ m.Qf (m.p.swingLyap m.δ m.Qf) P2 →
      m.timeScaled ε ∈ family.den (.flow .locallyExponentiallyStable)) :=
  mem_den_LES_of_lt_epsStar m hLf hCf hLg hKic hKiv hZt hM.ne' hωq.ne' hP hQ
    (m.p.posDef_swingLyap hnq hM hD hωq m.Qf hK) hP2
    (m.p.swingLyap_lyapunov hnq hM hD hωq m.Qf hK) hL2

end powerlib.GFM.FullModel
