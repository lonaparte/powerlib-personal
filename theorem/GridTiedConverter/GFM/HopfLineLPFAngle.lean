import theorem.GridTiedConverter.GFM.HopfLineLPF
import theorem.GridTiedConverter.GFM.HopfLineLPFAnglePattern

/-! # The first Lyapunov coefficient of the VSM with a power filter at every operating angle

Model boundary.
* The five-state VSM + power filter (droop + LPF) `Line.VSMLPF` of
  `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged: state `(δ, ω, P_f, i_d, i_q)`, grid dq
  frame at `ω₀`, export-positive power, constant `E`, `M ω̇ = P_ref − P_f − D ω`,
  `Ṗ_f = ω_c (P_e − P_f)`, `L i̇ = E e^{jδ} − V − (R + jX) i`; no voltage loop, inner loops, PLL,
  delay or PWM. Read about a selected angle (`Line.VSMLPF.Model`), translated so that the
  operating point is the origin; every operating angle `δ*`, every load (`P_ref`, `Q`), every
  physical parameter value (`R ≥ 0`).
* A Hopf point of the quintic at `ω` (`Line.VSMLPF.Model.HopfAt`): `±iω` roots of the
  characteristic quintic `s⁵ + a₄ s⁴ + … + a₀` at the operating point, Hurwitz cubic cofactor
  `ĉ(s) = s³ + a₄ s² + (a₃ − ω²) s + (a₂ − a₄ ω²)`.
* Level: Lyapunov instability and local asymptotic stability (LeanForControl's `Unstable`,
  `LocalAsymptoticStable`) of the operating point, through `Line.VSMLPF.family`. Bautin points
  (`𝔅 = 0`) are located, not decided; no complete local asymptotic membership off the
  zero-current slice is stated (it needs the degenerate set of the fold, of `Δ₃ = 0` and of the
  Bautin points at every angle).

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.5 and §5.4 (the
projection formula `NormalForm.LyapunovCoefficient.firstLyapunov_eq_of_solve`); the Hopf laws of
`theorem/GridTiedConverter/GFM/HopfLineLPF.lean` and `theorem/Dynamics/HopfDichotomy.lean`. The
closed form was derived with exact computer algebra (python-flint, untrusted discovery): in the
frame rotated with `δ*` and scaled (`P_f/M`, `(L/E) i`) the two Hopf relations are linear in the
reactive power `Q/M` (leading coefficient `2σω_c`) and in the gain `E²/(M L)` (leading
coefficient `2σω_c ω₀`), so both are eliminated with monomial denominators; the four pairings of
the projection formula then factor through `Λ = |L(iω)|²`, `L(iω) = (σ + iω)² + ω₀²` and the
cubic cofactor values. The algebra is in
`theorem/GridTiedConverter/GFM/HopfLineLPFAngleKey.lean` (the Bautin forms and the key identity)
and `theorem/GridTiedConverter/GFM/HopfLineLPFAnglePattern.lean` (the pattern and the
reductions). Sanity check (untrusted, outside the proof): the closed form reproduces the exact
witnesses of `HopfLineLPF.lean`, `ℓ₁ = −14341/14450` and
`ℓ₁ = 795686360348046533/264278927960175000`.

Results.
* The rotated reading `Line.VSMLPF.angleRead`; the critical pair at every operating angle
  `Line.VSMLPF.Model.critQ`, `Line.VSMLPF.Model.critP` (**`Line.VSMLPF.Model.isCriticalPair_crit`**,
  every balanced physical model, `R ≥ 0`).
* **`Line.VSMLPF.Model.firstLyapunov_crit`** (closed form, `R > 0`): at a Hopf point `ω`,
  `ℓ₁ = Λ 𝔅 / (64 σ⁴ ω₀² ω a₀ |ĉ(iω)|² |ĉ(2iω)|²)`, `σ = R/L`, `Λ = (σ² + ω₀² − ω²)² + 4σ²ω²`,
  `𝔅 = Line.VSMLPF.angleBautin ω_c (D/M) (P_ref/M) σ ω₀ ω`, `a₀` the constant coefficient of the
  quintic; **`Line.VSMLPF.Model.sign_firstLyapunov_crit`** (sign law, every critical pair):
  `sign ℓ₁ = sign 𝔅`.
* **`Line.VSMLPF.Model.firstLyapunov_crit_lossless`** (closed form, `R = 0`; there `ω₀² ≠ ω²` and
  `ω_c D/M = ω²`): `ℓ₁ = −(ω₀² − ω²)³ 𝔅_L / (4 ω_c⁴ ω₀² ω a₀ |ĉ(iω)|² |ĉ(2iω)|²)`,
  `𝔅_L = Line.VSMLPF.lossBautin ω_c (Q/M) (P_ref/M) ω₀ ω`;
  **`Line.VSMLPF.Model.sign_firstLyapunov_crit_lossless`**: `sign ℓ₁ = −sign((ω₀² − ω²) 𝔅_L)`.
* On the zero-current slice (`δ* = 0`, `V = E`) the closed form restricts to that of
  `theorem/GridTiedConverter/GFM/HopfLineLPFSlice.lean` (a different elimination: there `ω_c` is
  eliminated, here `Q/M`).

Family and connection conclusions.
No new family: connection conclusions on `Line.VSMLPF.family`.
* **`Line.VSMLPF.mem_den_locallyAsymptoticallyStable_of_angleBautin_neg`** (supercritical,
  `𝔅 < 0`) and **`Line.VSMLPF.mem_den_unstable_of_angleBautin_pos`** (subcritical, `𝔅 > 0`) at a
  Hopf point of a balanced physical model with `R > 0`, every operating angle.
* **`Line.VSMLPF.mem_den_locallyAsymptoticallyStable_of_lossBautin_pos`** and
  **`Line.VSMLPF.mem_den_unstable_of_lossBautin_neg`** on the lossless line (`R = 0`), by the sign
  of `(ω₀² − ω²) 𝔅_L`.
-/

noncomputable section
namespace powerlib.GFM.Line
namespace VSMLPF
open Complex Matrix Polynomial
open powerlib.Dynamics (State coord)
open powerlib.NormalForm.LyapunovCoefficient

@[tmio M, powerlib_domain] private theorem ag_star_Q (d σ w ω : ℝ) :
    star (angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I) =
      angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (-(ω : ℂ)) I := by
  ext k
  fin_cases k <;> simp only [Pi.star_apply, RCLike.star_def, angleVecQ, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, map_mul, map_add, map_neg,
    map_pow, Complex.conj_ofReal, Complex.conj_I, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk] <;> ring

@[tmio M, powerlib_domain] private theorem ag_star_P (c d g σ w ω : ℝ) :
    star (angleVecP (c : ℂ) (d : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I) =
      angleVecP (c : ℂ) (d : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ) (-(ω : ℂ)) I := by
  ext k
  fin_cases k <;> simp only [Pi.star_apply, RCLike.star_def, angleVecP, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, map_mul, map_add, map_sub, map_neg,
    map_pow, Complex.conj_ofReal, Complex.conj_I, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk] <;> ring

/-- The projection-formula combination in the factored reduced quantities. -/
@[tmio M, powerlib_domain] private theorem ag_alg {Y1 Y2 Y3 Cp X a σ c w O j Λ L Z1 G2 Z3 B1 B2
    Ap : ℂ} (hσ : σ ≠ 0) (hc : c ≠ 0) (hw : w ≠ 0) (hO : O ≠ 0) (hj : j ≠ 0) (hL : L ≠ 0)
    (hB1 : B1 ≠ 0) (hB2 : B2 ≠ 0) (hAp : Ap ≠ 0)
    (e1 : 2 * σ * c * (2 * σ * c * w) * Y1 = 2 * w * σ * c ^ 2 * Λ * L * Z1)
    (e2 : 2 * σ * c * (2 * σ * c * w) ^ 2 * Y2 = 2 * σ * c ^ 3 * Λ * G2 * L ^ 2)
    (e3 : 2 * σ * c * (2 * σ * c * w) ^ 2 * Y3 = 2 * σ * c ^ 3 * Λ * L * Z3)
    (eC : 2 * σ * c * w * Cp = c * w * (-2 * O * j) * B1 * L)
    (eX : 2 * σ * c * (2 * σ * c * w) * X = 2 * c ^ 2 * σ * w * (-3 * O ^ 2) * B2)
    (eA : 2 * σ * c * (2 * σ * c * w) * a = 2 * w * σ * O ^ 2 * c ^ 2 * Ap) :
    Cp⁻¹ * Y1 - 2 * (a⁻¹ * (Cp⁻¹ * Y2)) + X⁻¹ * (Cp⁻¹ * Y3) =
      Λ * (-3 * w ^ 2 * O ^ 2 * Ap * (Z1 * B2) + 6 * G2 * (L * B2) + Ap * Z3) /
        (6 * w ^ 2 * O ^ 3 * Ap * (j * B1 * B2)) := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hT : 2 * σ * c ≠ 0 := mul_ne_zero (mul_ne_zero h2 hσ) hc
  have hT3 : 2 * σ * c * w ≠ 0 := mul_ne_zero hT hw
  have hY1 : Y1 = 2 * w * σ * c ^ 2 * Λ * L * Z1 / (2 * σ * c * (2 * σ * c * w)) := by
    rw [← e1]; field_simp
  have hY2 : Y2 = 2 * σ * c ^ 3 * Λ * G2 * L ^ 2 / (2 * σ * c * (2 * σ * c * w) ^ 2) := by
    rw [← e2]; field_simp
  have hY3 : Y3 = 2 * σ * c ^ 3 * Λ * L * Z3 / (2 * σ * c * (2 * σ * c * w) ^ 2) := by
    rw [← e3]; field_simp
  have hCp : Cp = c * w * (-2 * O * j) * B1 * L / (2 * σ * c * w) := by
    rw [← eC]; field_simp
  have hX : X = 2 * c ^ 2 * σ * w * (-3 * O ^ 2) * B2 / (2 * σ * c * (2 * σ * c * w)) := by
    rw [← eX]; field_simp
  have ha : a = 2 * w * σ * O ^ 2 * c ^ 2 * Ap / (2 * σ * c * (2 * σ * c * w)) := by
    rw [← eA]; field_simp
  rw [hY1, hY2, hY3, hCp, hX, ha]
  field_simp
  ring

/-- The real part of the reduced quotient. -/
@[tmio M, powerlib_domain] private theorem ag_re (a b e f t : ℝ) (ht : t ≠ 0)
    (hef : e ^ 2 + f ^ 2 ≠ 0) :
    (((a : ℂ) + (b : ℂ) * I) / ((t : ℂ) * ((e : ℂ) + (f : ℂ) * I))).re =
      (a * e + b * f) / (t * (e ^ 2 + f ^ 2)) := by
  have hz : (t : ℂ) * ((e : ℂ) + (f : ℂ) * I) = ((t * e : ℝ) : ℂ) + ((t * f : ℝ) : ℂ) * I := by
    push_cast; ring
  have hd : t * e * (t * e) + t * f * (t * f) ≠ 0 := by
    rw [show t * e * (t * e) + t * f * (t * f) = t ^ 2 * (e ^ 2 + f ^ 2) by ring]
    exact mul_ne_zero (pow_ne_zero 2 ht) hef
  rw [hz, Complex.div_re]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im, Complex.normSq_apply, mul_zero, sub_zero,
    zero_add, add_zero, mul_one]
  field_simp

/-- **The cubic cofactor does not vanish on the imaginary axis**: if `s³ + a₄ s² + (a₃ − ω²) s +
(a₂ − a₄ ω²)` is Hurwitz, its modulus squared at `j t ω` (`t ω ≠ 0`) is positive. -/
@[tmio M, powerlib_domain] private theorem ag_cub_pos {a4 a3 a2 ω t : ℝ}
    (k4 : 0 < a4) (k0 : 0 < a2 - a4 * ω ^ 2) (kg : a2 - a4 * ω ^ 2 < a4 * (a3 - ω ^ 2)) :
    0 < (a2 - (1 + t ^ 2) * a4 * ω ^ 2) ^ 2 + t ^ 2 * ω ^ 2 * (a3 - (1 + t ^ 2) * ω ^ 2) ^ 2 := by
  rcases (add_nonneg (sq_nonneg (a2 - (1 + t ^ 2) * a4 * ω ^ 2))
    (mul_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg ω))
      (sq_nonneg (a3 - (1 + t ^ 2) * ω ^ 2)))).lt_or_eq with h | h
  · exact h
  · exfalso
    have hB : 0 ≤ t ^ 2 * ω ^ 2 * (a3 - (1 + t ^ 2) * ω ^ 2) ^ 2 := by positivity
    have hA : (a2 - (1 + t ^ 2) * a4 * ω ^ 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a2 - (1 + t ^ 2) * a4 * ω ^ 2)]
    have hr : a2 - (1 + t ^ 2) * a4 * ω ^ 2 = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp hA
    have hi2 : (t * ω * (a3 - (1 + t ^ 2) * ω ^ 2)) ^ 2 = 0 := by
      linear_combination (-1 : ℝ) * h + (-(a2 - (1 + t ^ 2) * a4 * ω ^ 2)) * hr
    have hi : t * ω * (a3 - (1 + t ^ 2) * ω ^ 2)
        = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp hi2
    have hs : (((t * ω : ℝ) : ℂ) * I) ^ 3 + (a4 : ℂ) * (((t * ω : ℝ) : ℂ) * I) ^ 2 +
        ((a3 - ω ^ 2 : ℝ) : ℂ) * (((t * ω : ℝ) : ℂ) * I) + ((a2 - a4 * ω ^ 2 : ℝ) : ℂ) = 0 := by
      have e : (((t * ω : ℝ) : ℂ) * I) ^ 3 + (a4 : ℂ) * (((t * ω : ℝ) : ℂ) * I) ^ 2 +
          ((a3 - ω ^ 2 : ℝ) : ℂ) * (((t * ω : ℝ) : ℂ) * I) + ((a2 - a4 * ω ^ 2 : ℝ) : ℂ) =
          ((a2 - (1 + t ^ 2) * a4 * ω ^ 2 : ℝ) : ℂ) +
            ((t * ω * (a3 - (1 + t ^ 2) * ω ^ 2) : ℝ) : ℂ) * I := by
        push_cast
        linear_combination ((t : ℂ) ^ 3 * (ω : ℂ) ^ 3 * I + (a4 : ℂ) * (t : ℂ) ^ 2 * (ω : ℂ) ^ 2) *
          I_sq
      rw [e, hr, hi]
      simp
    have hre := Criteria.cubic_roots_re_neg_of k4 k0 kg _ hs
    simp at hre

/-- A complex number with nonzero imaginary part is nonzero. -/
@[tmio T, powerlib_foundation] private theorem ag_ne_of_im {a b : ℝ} (hb : b ≠ 0) :
    (a : ℂ) + (b : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hb this

/-- **The critical pair of the rotated pattern**. -/
@[tmio M, powerlib_domain] private theorem ag_isCriticalPair {f : State 5 → State 5}
    {c d K g σ w ω : ℝ} (hω : 0 < ω)
    (hK : 2 * σ * c * K = (d * c - ω ^ 2) * (σ ^ 2 + w ^ 2 - ω ^ 2) - 2 * σ * (d + c) * ω ^ 2)
    (hR : c * g * w = c * K * (σ ^ 2 + w ^ 2 - ω ^ 2) +
      ω ^ 2 * ((d + c) * (σ ^ 2 + w ^ 2 - ω ^ 2) + 2 * σ * (d * c - ω ^ 2)))
    (hc0 : angleVecP (c : ℂ) (d : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ) (-(ω : ℂ)) I ⬝ᵥ
      angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I ≠ 0) (hf : f 0 = 0)
    (hJ : jacobianC f 0 = AnglePattern.jac (c : ℂ) (d : ℂ) (K : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ)) :
    IsCriticalPair f 0 ω (angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I)
      ((starRingEnd ℂ (angleVecP (c : ℂ) (d : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ) (-(ω : ℂ)) I ⬝ᵥ
        angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I))⁻¹ •
        angleVecP (c : ℂ) (d : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I) := by
  have hKc : (2 : ℂ) * σ * c * K = ((d : ℂ) * c - (ω : ℂ) ^ 2) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 -
      (ω : ℂ) ^ 2) - 2 * σ * (d + c) * ω ^ 2 := by exact_mod_cast hK
  have hRc : (c : ℂ) * g * w = c * K * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) +
      (ω : ℂ) ^ 2 * (((d : ℂ) + c) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) +
        2 * σ * (d * c - (ω : ℂ) ^ 2)) := by exact_mod_cast hR
  refine ⟨hf, hω, ?_, ?_, ?_⟩
  · rw [hJ]
    exact AnglePattern.right I_sq hKc hRc
  · rw [hJ, Matrix.mulVec_smul, AnglePattern.left I_sq hKc hRc, smul_comm]
  · have hstar : star ((starRingEnd ℂ (angleVecP (c : ℂ) (d : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ)
        (-(ω : ℂ)) I ⬝ᵥ angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I))⁻¹ •
        angleVecP (c : ℂ) (d : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I) =
        (angleVecP (c : ℂ) (d : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ) (-(ω : ℂ)) I ⬝ᵥ
          angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I)⁻¹ •
          star (angleVecP (c : ℂ) (d : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I) := by
      ext k
      simp [Pi.star_apply]
    rw [hstar, smul_dotProduct, ag_star_P, smul_eq_mul, inv_mul_cancel₀ hc0]

/-- The pairing `⟨p̃, q⟩` of the pattern does not vanish at a Hopf point (`σ > 0`). -/
@[tmio M, powerlib_domain] private theorem ag_pairing_ne {c d g σ w ω a4 a3 a2 : ℝ}
    (hω : 0 < ω) (hσ : 0 < σ) (hw : 0 < w) (hc : 0 < c)
    (hg : 2 * σ * c * w * g = (d * c - ω ^ 2) * ((σ ^ 2 + w ^ 2 - ω ^ 2) ^ 2 + 4 * σ ^ 2 * ω ^ 2))
    (hB : AngleKey.cubRe c d σ w ω ^ 2 + AngleKey.cubIm c d σ w ω ^ 2 =
      4 * σ ^ 2 * ((a2 - 2 * a4 * ω ^ 2) ^ 2 + ω ^ 2 * (a3 - 2 * ω ^ 2) ^ 2))
    (k4 : 0 < a4) (k0 : 0 < a2 - a4 * ω ^ 2) (kg : a2 - a4 * ω ^ 2 < a4 * (a3 - ω ^ 2)) :
    angleVecP (c : ℂ) (d : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ) (-(ω : ℂ)) I ⬝ᵥ
      angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I ≠ 0 := by
  have hgc : (2 : ℂ) * σ * c * w * g = ((d : ℂ) * c - (ω : ℂ) ^ 2) *
      (((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) ^ 2 + 4 * (σ : ℂ) ^ 2 * (ω : ℂ) ^ 2) := by
    exact_mod_cast hg
  have eC := AnglePattern.pairing_eq I_sq hgc
  rw [AngleKey.cubRe_cast, AngleKey.cubIm_cast] at eC
  have hc1 := ag_cub_pos (t := 1) k4 k0 kg
  norm_num at hc1
  intro h
  rw [h, mul_zero] at eC
  have hB0 : ((AngleKey.cubRe c d σ w ω : ℝ) : ℂ) + ((AngleKey.cubIm c d σ w ω : ℝ) : ℂ)
      * I ≠ 0 := by
    intro h'
    have hr := congrArg Complex.re h'
    have hi := congrArg Complex.im h'
    simp at hr hi
    have : (4 * σ ^ 2 * ((a2 - 2 * a4 * ω ^ 2) ^ 2 + ω ^ 2 * (a3 - 2 * ω ^ 2) ^ 2) : ℝ) = 0 := by
      rw [← hB, hr, hi]; ring
    have : 0 < 4 * σ ^ 2 * ((a2 - 2 * a4 * ω ^ 2) ^ 2 + ω ^ 2 * (a3 - 2 * ω ^ 2) ^ 2) := by
      positivity
    linarith
  have hL : ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) + 2 * (σ : ℂ) * (ω : ℂ) * I ≠ 0 := by
    rw [show ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) + 2 * (σ : ℂ) * (ω : ℂ) * I =
      ((σ ^ 2 + w ^ 2 - ω ^ 2 : ℝ) : ℂ) + ((2 * σ * ω : ℝ) : ℂ) * I by push_cast; ring]
    exact ag_ne_of_im (by positivity)
  have h0 : (c : ℂ) * w * (-2 * ω * I) ≠ 0 := by
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hw' : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
    have hω' : (ω : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
    exact mul_ne_zero (mul_ne_zero hc' hw') (mul_ne_zero (mul_ne_zero (by norm_num) hω') I_ne_zero)
  exact mul_ne_zero (mul_ne_zero h0 hB0) hL eC.symm

/-- The structural reduced numerator `Û` (complex form of `AngleKey.numRe + i AngleKey.numIm`). -/
@[tmio M, powerlib_domain] private theorem ag_U (c d N σ w ω : ℝ) :
    -3 * (w : ℂ) ^ 2 * (ω : ℂ) ^ 2 * ((AngleKey.constRed c d σ w ω : ℝ) : ℂ) *
        ((((AngleKey.trilinRe c d σ w ω : ℝ) : ℂ) + ((AngleKey.trilinIm c d σ w ω : ℝ) : ℂ) * I) *
          (((AngleKey.cub2Re c d σ w ω : ℝ) : ℂ) + ((AngleKey.cub2Im c d σ w ω : ℝ) : ℂ) * I)) +
      6 * ((AngleKey.bilinRed c d N σ w ω : ℝ) : ℂ) *
        ((((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) + 2 * (σ : ℂ) * (ω : ℂ) * I) *
          (((AngleKey.cub2Re c d σ w ω : ℝ) : ℂ) + ((AngleKey.cub2Im c d σ w ω : ℝ) : ℂ) * I)) +
      ((AngleKey.constRed c d σ w ω : ℝ) : ℂ) *
        (((AngleKey.shiftRe c d N σ w ω : ℝ) : ℂ) + ((AngleKey.shiftIm c d N σ w ω : ℝ) : ℂ) * I) =
      ((AngleKey.numRe c d N σ w ω : ℝ) : ℂ) + ((AngleKey.numIm c d N σ w ω : ℝ) : ℂ) * I := by
  rw [AngleKey.numRe_eq, AngleKey.numIm_eq]
  push_cast
  linear_combination (-3 * (w : ℂ) ^ 2 * (ω : ℂ) ^ 2 * ((AngleKey.constRed c d σ w ω : ℝ) : ℂ) *
    ((AngleKey.trilinIm c d σ w ω : ℝ) : ℂ) * ((AngleKey.cub2Im c d σ w ω : ℝ) : ℂ) +
    6 * ((AngleKey.bilinRed c d N σ w ω : ℝ) : ℂ) * (2 * (σ : ℂ) * (ω : ℂ)) *
      ((AngleKey.cub2Im c d σ w ω : ℝ) : ℂ)) * I_sq

/-- `W = j ĉ(jO) ĉ(2jO)` in complex form. -/
@[tmio M, powerlib_domain] private theorem ag_W (c d σ w ω : ℝ) :
    I * (((AngleKey.cubRe c d σ w ω : ℝ) : ℂ) + ((AngleKey.cubIm c d σ w ω : ℝ) : ℂ) * I) *
      (((AngleKey.cub2Re c d σ w ω : ℝ) : ℂ) + ((AngleKey.cub2Im c d σ w ω : ℝ) : ℂ) * I) =
      ((AngleKey.denRe c d σ w ω : ℝ) : ℂ) + ((AngleKey.denIm c d σ w ω : ℝ) : ℂ) * I := by
  simp only [AngleKey.denRe, AngleKey.denIm]
  push_cast
  linear_combination (((AngleKey.cubRe c d σ w ω : ℝ) : ℂ) * ((AngleKey.cub2Im c d σ w ω : ℝ) : ℂ) +
    ((AngleKey.cubIm c d σ w ω : ℝ) : ℂ) * ((AngleKey.cub2Re c d σ w ω : ℝ) : ℂ) +
    ((AngleKey.cubIm c d σ w ω : ℝ) : ℂ) * ((AngleKey.cub2Im c d σ w ω : ℝ) : ℂ) * I) * I_sq

/-- **The real part of the reduced projection formula**:
`Re(Λ Û / (6 w² ω³ A W)) = Λ · 6σω𝔅 / (6 w² ω³ A |ĉ(jω)|² |ĉ(2jω)|²)` (each cubic value times
`2σ`). -/
@[tmio M, powerlib_domain] private theorem ag_realPart {c d N σ w ω : ℝ} (hw : w ≠ 0)
    (hω : ω ≠ 0) (hAp : AngleKey.constRed c d σ w ω ≠ 0)
    (hB1 : 0 < AngleKey.cubRe c d σ w ω ^ 2 + AngleKey.cubIm c d σ w ω ^ 2)
    (hB2 : 0 < AngleKey.cub2Re c d σ w ω ^ 2 + AngleKey.cub2Im c d σ w ω ^ 2) :
    ((((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) ^ 2 + 4 * (σ : ℂ) ^ 2 * (ω : ℂ) ^ 2) *
        (-3 * (w : ℂ) ^ 2 * (ω : ℂ) ^ 2 * ((AngleKey.constRed c d σ w ω : ℝ) : ℂ) *
          ((((AngleKey.trilinRe c d σ w ω : ℝ) : ℂ) + ((AngleKey.trilinIm c d σ w ω : ℝ) : ℂ) * I) *
            (((AngleKey.cub2Re c d σ w ω : ℝ) : ℂ) + ((AngleKey.cub2Im c d σ w ω : ℝ) : ℂ) * I)) +
        6 * ((AngleKey.bilinRed c d N σ w ω : ℝ) : ℂ) *
          ((((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) + 2 * (σ : ℂ) * (ω : ℂ) * I) *
            (((AngleKey.cub2Re c d σ w ω : ℝ) : ℂ) + ((AngleKey.cub2Im c d σ w ω : ℝ) : ℂ) * I)) +
        ((AngleKey.constRed c d σ w ω : ℝ) : ℂ) *
          (((AngleKey.shiftRe c d N σ w ω : ℝ) : ℂ) + ((AngleKey.shiftIm c d N σ w ω : ℝ) : ℂ)
              * I)) /
      (6 * (w : ℂ) ^ 2 * (ω : ℂ) ^ 3 * ((AngleKey.constRed c d σ w ω : ℝ) : ℂ) *
        (I * (((AngleKey.cubRe c d σ w ω : ℝ) : ℂ) + ((AngleKey.cubIm c d σ w ω : ℝ) : ℂ) * I) *
          (((AngleKey.cub2Re c d σ w ω : ℝ) : ℂ) + ((AngleKey.cub2Im c d σ w ω : ℝ) : ℂ)
              * I)))).re =
      ((σ ^ 2 + w ^ 2 - ω ^ 2) ^ 2 + 4 * σ ^ 2 * ω ^ 2) * (6 * σ * ω * angleBautin c d N σ w ω) /
        (6 * w ^ 2 * ω ^ 3 * AngleKey.constRed c d σ w ω * ((AngleKey.cubRe c d σ w ω ^ 2
            + AngleKey.cubIm c d σ w ω ^ 2) *
          (AngleKey.cub2Re c d σ w ω ^ 2 + AngleKey.cub2Im c d σ w ω ^ 2))) := by
  have hWsq : AngleKey.denRe c d σ w ω ^ 2 + AngleKey.denIm c d σ w ω ^ 2 =
      (AngleKey.cubRe c d σ w ω ^ 2 + AngleKey.cubIm c d σ w ω ^ 2) *
        (AngleKey.cub2Re c d σ w ω ^ 2 + AngleKey.cub2Im c d σ w ω ^ 2) := by
    simp only [AngleKey.denRe, AngleKey.denIm]; ring
  have hWp : AngleKey.denRe c d σ w ω ^ 2 + AngleKey.denIm c d σ w ω ^ 2 ≠ 0 := by
    rw [hWsq]; positivity
  rw [ag_U, ag_W]
  have hnum : (((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) ^ 2 + 4 * (σ : ℂ) ^ 2 * (ω : ℂ) ^ 2) *
      (((AngleKey.numRe c d N σ w ω : ℝ) : ℂ) + ((AngleKey.numIm c d N σ w ω : ℝ) : ℂ) * I) =
      ((((σ ^ 2 + w ^ 2 - ω ^ 2) ^ 2 + 4 * σ ^ 2 * ω ^ 2) * AngleKey.numRe c d N σ w ω : ℝ) : ℂ) +
        ((((σ ^ 2 + w ^ 2 - ω ^ 2) ^ 2 + 4 * σ ^ 2 * ω ^ 2) * AngleKey.numIm c d N σ w ω : ℝ) : ℂ)
            * I := by
    push_cast; ring
  have hden : 6 * (w : ℂ) ^ 2 * (ω : ℂ) ^ 3 * ((AngleKey.constRed c d σ w ω : ℝ) : ℂ) =
      ((6 * w ^ 2 * ω ^ 3 * AngleKey.constRed c d σ w ω : ℝ) : ℂ) := by push_cast; ring
  have hden0 : 6 * w ^ 2 * ω ^ 3 * AngleKey.constRed c d σ w ω ≠ 0 := by
    have : 6 * w ^ 2 * ω ^ 3 ≠ 0 := by positivity
    exact mul_ne_zero this hAp
  rw [hnum, hden, ag_re _ _ _ _ _ hden0 hWp, hWsq]
  have hkey := AngleKey.key c d N σ w ω
  congr 1
  rw [← hkey]
  ring

/-- **The first Lyapunov coefficient of the rotated pattern, reduced** (`σ > 0`): the
projection formula of the critical pair of the pattern equals the real part of
`Λ Û / (6 w² ω³ A W)`. -/
@[tmio M, powerlib_domain] private theorem ag_projection {f : State 5 → State 5}
    {c d K g N σ w ω : ℝ} (hω : 0 < ω) (hσ : 0 < σ) (hw : 0 < w) (hc : 0 < c)
    (hK : 2 * σ * c * K = (d * c - ω ^ 2) * (σ ^ 2 + w ^ 2 - ω ^ 2) - 2 * σ * (d + c) * ω ^ 2)
    (hR : c * g * w = c * K * (σ ^ 2 + w ^ 2 - ω ^ 2) +
      ω ^ 2 * ((d + c) * (σ ^ 2 + w ^ 2 - ω ^ 2) + 2 * σ * (d * c - ω ^ 2)))
    (ha0 : 0 < c * (g * w - K * (σ ^ 2 + w ^ 2)))
    (hB1p : 0 < AngleKey.cubRe c d σ w ω ^ 2 + AngleKey.cubIm c d σ w ω ^ 2)
    (hB2p : 0 < AngleKey.cub2Re c d σ w ω ^ 2 + AngleKey.cub2Im c d σ w ω ^ 2)
    (hJ : jacobianC f 0 = AnglePattern.jac (c : ℂ) (d : ℂ) (K : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ))
    (hB : ∀ u v, bilinC f 0 u v = AnglePattern.bilin (c : ℂ) (g : ℂ) (N : ℂ) u v)
    (hC : ∀ u v z, trilinC f 0 u v z = AnglePattern.trilin (c : ℂ) (g : ℂ) (K : ℂ) u v z)
    (hA : IsUnit (jacobianC f 0).det) (h2' : IsUnit (shift2 (jacobianC f 0) ω).det) :
    firstLyapunov f 0 ω (angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I)
        ((starRingEnd ℂ (angleVecP (c : ℂ) (d : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ) (-(ω : ℂ)) I ⬝ᵥ
          angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I))⁻¹ •
          angleVecP (c : ℂ) (d : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I) =
      1 / (2 * ω) *
      ((((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) ^ 2 + 4 * (σ : ℂ) ^ 2 * (ω : ℂ) ^ 2) *
          (-3 * (w : ℂ) ^ 2 * (ω : ℂ) ^ 2 * ((AngleKey.constRed c d σ w ω : ℝ) : ℂ) *
            ((((AngleKey.trilinRe c d σ w ω : ℝ) : ℂ) + ((AngleKey.trilinIm c d σ w ω : ℝ) : ℂ)
                * I) *
              (((AngleKey.cub2Re c d σ w ω : ℝ) : ℂ) + ((AngleKey.cub2Im c d σ w ω : ℝ) : ℂ) * I)) +
          6 * ((AngleKey.bilinRed c d N σ w ω : ℝ) : ℂ) *
            ((((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) + 2 * (σ : ℂ) * (ω : ℂ) * I) *
              (((AngleKey.cub2Re c d σ w ω : ℝ) : ℂ) + ((AngleKey.cub2Im c d σ w ω : ℝ) : ℂ) * I)) +
          ((AngleKey.constRed c d σ w ω : ℝ) : ℂ) *
            (((AngleKey.shiftRe c d N σ w ω : ℝ) : ℂ) + ((AngleKey.shiftIm c d N σ w ω : ℝ) : ℂ)
                * I)) /
        (6 * (w : ℂ) ^ 2 * (ω : ℂ) ^ 3 * ((AngleKey.constRed c d σ w ω : ℝ) : ℂ) *
          (I * (((AngleKey.cubRe c d σ w ω : ℝ) : ℂ) + ((AngleKey.cubIm c d σ w ω : ℝ) : ℂ) * I) *
            (((AngleKey.cub2Re c d σ w ω : ℝ) : ℂ) + ((AngleKey.cub2Im c d σ w ω : ℝ) : ℂ)
                * I)))).re := by
  have hKc : (2 : ℂ) * σ * c * K = ((d : ℂ) * c - (ω : ℂ) ^ 2) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 -
      (ω : ℂ) ^ 2) - 2 * σ * (d + c) * ω ^ 2 := by exact_mod_cast hK
  have hRc : (c : ℂ) * g * w = c * K * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) +
      (ω : ℂ) ^ 2 * (((d : ℂ) + c) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) +
        2 * σ * (d * c - (ω : ℂ) ^ 2)) := by exact_mod_cast hR
  have hgc : (2 : ℂ) * σ * c * w * g = ((d : ℂ) * c - (ω : ℂ) ^ 2) *
      (((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) ^ 2 + 4 * (σ : ℂ) ^ 2 * (ω : ℂ) ^ 2) := by
    linear_combination 2 * (σ : ℂ) * hRc + ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) * hKc
  have hcne : ∀ x y : ℝ, 0 < x ^ 2 + y ^ 2 → (x : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro x y hxy h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    simp at hr hi
    rw [hr, hi] at hxy
    norm_num at hxy
  have e1 := AnglePattern.trilin_pairing I_sq hKc hgc
  have e2' := AnglePattern.bilin_pairing (N := (N : ℂ)) I_sq hKc hgc
  have e3' := AnglePattern.shift_pairing (N := (N : ℂ)) I_sq hKc hgc
  have eC := AnglePattern.pairing_eq I_sq hgc
  have eX := AnglePattern.shiftDet_eq I_sq hKc hgc
  have eA := AnglePattern.det_eq hKc hgc
  rw [AngleKey.trilinRe_cast, AngleKey.trilinIm_cast] at e1
  rw [AngleKey.bilinRed_cast] at e2'
  rw [AngleKey.shiftRe_cast, AngleKey.shiftIm_cast] at e3'
  rw [AngleKey.cubRe_cast, AngleKey.cubIm_cast] at eC
  rw [AngleKey.cub2Re_cast, AngleKey.cub2Im_cast] at eX
  rw [AngleKey.constRed_cast] at eA
  have hσc : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hwc : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have hωc : (ω : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
  have ha : (c : ℂ) * (g * w - K * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2)) ≠ 0 := by
    have : c * (g * w - K * (σ ^ 2 + w ^ 2)) ≠ 0 := ha0.ne'
    exact_mod_cast this
  have hApc : ((AngleKey.constRed c d σ w ω : ℝ) : ℂ) ≠ 0 := by
    intro h
    rw [h, mul_zero] at eA
    have h0 : (2 : ℂ) * σ * c * (2 * σ * c * w) ≠ 0 := by
      have : (2 * σ * c * (2 * σ * c * w) : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    exact mul_ne_zero h0 ha eA
  have hL : ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) + 2 * (σ : ℂ) * (ω : ℂ) * I ≠ 0 := by
    rw [show ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) + 2 * (σ : ℂ) * (ω : ℂ) * I =
      ((σ ^ 2 + w ^ 2 - ω ^ 2 : ℝ) : ℂ) + ((2 * σ * ω : ℝ) : ℂ) * I by push_cast; ring]
    exact ag_ne_of_im (by positivity)
  have hB1 := hcne _ _ hB1p
  have hB2 := hcne _ _ hB2p
  have hX0 : AnglePattern.shiftDet (c : ℂ) (d : ℂ) (K : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I ≠
      0 := by
    intro h
    rw [h, mul_zero] at eX
    have : (2 : ℂ) * c ^ 2 * σ * w * (-3 * ω ^ 2) ≠ 0 := by
      have h3 : (-3 * ω ^ 2 : ℝ) ≠ 0 := (by nlinarith [pow_pos hω 2] : (-3 * ω ^ 2 : ℝ) < 0).ne
      have : (2 * c ^ 2 * σ * w * (-3 * ω ^ 2) : ℝ) ≠ 0 := mul_ne_zero (by positivity) h3
      exact_mod_cast this
    exact mul_ne_zero this hB2 eX.symm
  have hq : star (angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I) =
      angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (-(ω : ℂ)) I := ag_star_Q d σ w ω
  have hr : jacobianC f 0 *ᵥ (((c : ℂ) * (g * w - K * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2)))⁻¹ •
      AnglePattern.solveJ (c : ℂ) (K : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ) (AnglePattern.bilin (c : ℂ) (g :
          ℂ) (N : ℂ)
        (angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I)
        (angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (-(ω : ℂ)) I))) =
      bilinC f 0 (angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I)
        (star (angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I)) := by
    rw [Matrix.mulVec_smul, hJ, AnglePattern.jac_solveJ, hB, hq, smul_smul, inv_mul_cancel₀ ha,
        one_smul]
  have hs : shift2 (jacobianC f 0) ω *ᵥ ((AnglePattern.shiftDet (c : ℂ) (d : ℂ) (K : ℂ) (g : ℂ) (σ
      : ℂ) (w : ℂ)
      (ω : ℂ) I)⁻¹ • AnglePattern.solveShift (c : ℂ) (d : ℂ) (K : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ) (ω :
          ℂ) I
        (AnglePattern.bilin (c : ℂ) (g : ℂ) (N : ℂ) (angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I)
          (angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I))) =
      bilinC f 0 (angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I)
        (angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I) := by
    rw [Matrix.mulVec_smul, hJ, shift2, AnglePattern.shift_solveShift, hB, smul_smul,
        inv_mul_cancel₀ hX0, one_smul]
  have hpair : ∀ (z : ℂ) (v : Fin 5 → ℂ),
      pairing ((starRingEnd ℂ z)⁻¹ • angleVecP (c : ℂ) (d : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I)
        v = z⁻¹ * (angleVecP (c : ℂ) (d : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ) (-(ω : ℂ)) I ⬝ᵥ v) := by
    intro z v
    rw [← ag_star_P, ← pairing_eq_dotProduct]
    simp [pairing_apply, Finset.mul_sum, mul_assoc]
  rw [firstLyapunov_eq_of_solve hA h2' hr hs, (bilinC f 0 _).map_smul, (bilinC f 0 _).map_smul,
    hC, hB, hB, hq, (pairing _).map_smul, (pairing _).map_smul, hpair, hpair, hpair, smul_eq_mul,
    smul_eq_mul, ag_alg hσc hcc hwc hωc I_ne_zero hL hB1 hB2 hApc e1 e2' e3' eC eX eA]

/-- **The first Lyapunov coefficient of the rotated pattern in closed form** (`σ > 0`): with the
quintic coefficients `a₄, a₃, a₂, a₀` in the atoms, the projection formula reduces to
`Λ 𝔅 / (64 σ⁴ w² ω a₀ |ĉ(jω)|² |ĉ(2jω)|²)`, `Λ = (σ² + w² − ω²)² + 4σ²ω²`, `ĉ` the cubic
cofactor. -/
@[tmio M, powerlib_domain] private theorem ag_firstLyapunov {f : State 5 → State 5}
    {c d K g N σ w ω a4 a3 a2 a0 : ℝ} (hω : 0 < ω) (hσ : 0 < σ) (hw : 0 < w) (hc : 0 < c)
    (hK : 2 * σ * c * K = (d * c - ω ^ 2) * (σ ^ 2 + w ^ 2 - ω ^ 2) - 2 * σ * (d + c) * ω ^ 2)
    (hR : c * g * w = c * K * (σ ^ 2 + w ^ 2 - ω ^ 2) +
      ω ^ 2 * ((d + c) * (σ ^ 2 + w ^ 2 - ω ^ 2) + 2 * σ * (d * c - ω ^ 2)))
    (e4 : a4 = c + d + 2 * σ) (e3 : a3 = σ ^ 2 + w ^ 2 + 2 * σ * (d + c) + d * c)
    (e2 : a2 = (d + c) * (σ ^ 2 + w ^ 2) + 2 * σ * d * c - c * K)
    (e0 : a0 = c * (g * w - K * (σ ^ 2 + w ^ 2)))
    (k4 : 0 < a4) (k0 : 0 < a2 - a4 * ω ^ 2) (kg : a2 - a4 * ω ^ 2 < a4 * (a3 - ω ^ 2))
    (hJ : jacobianC f 0 = AnglePattern.jac (c : ℂ) (d : ℂ) (K : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ))
    (hB : ∀ u v, bilinC f 0 u v = AnglePattern.bilin (c : ℂ) (g : ℂ) (N : ℂ) u v)
    (hC : ∀ u v z, trilinC f 0 u v z = AnglePattern.trilin (c : ℂ) (g : ℂ) (K : ℂ) u v z)
    (hA : IsUnit (jacobianC f 0).det) (h2' : IsUnit (shift2 (jacobianC f 0) ω).det) :
    firstLyapunov f 0 ω (angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I)
        ((starRingEnd ℂ (angleVecP (c : ℂ) (d : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ) (-(ω : ℂ)) I ⬝ᵥ
          angleVecQ (d : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I))⁻¹ •
          angleVecP (c : ℂ) (d : ℂ) (g : ℂ) (σ : ℂ) (w : ℂ) (ω : ℂ) I) =
      ((σ ^ 2 + w ^ 2 - ω ^ 2) ^ 2 + 4 * σ ^ 2 * ω ^ 2) * angleBautin c d N σ w ω /
        (64 * σ ^ 4 * w ^ 2 * ω * a0 *
          ((a2 - 2 * a4 * ω ^ 2) ^ 2 + ω ^ 2 * (a3 - 2 * ω ^ 2) ^ 2) *
          ((a2 - 5 * a4 * ω ^ 2) ^ 2 + 4 * ω ^ 2 * (a3 - 5 * ω ^ 2) ^ 2)) := by
  have ha0 : a0 = ω ^ 2 * (a2 - a4 * ω ^ 2) := by rw [e0, e2, e4]; linear_combination hR
  have ha0p : 0 < a0 := by rw [ha0]; positivity
  have hc1 := ag_cub_pos (t := 1) k4 k0 kg
  have hc2 := ag_cub_pos (t := 2) k4 k0 kg
  norm_num at hc1 hc2
  have eB1 : AngleKey.cubRe c d σ w ω ^ 2 + AngleKey.cubIm c d σ w ω ^ 2 =
      4 * σ ^ 2 * ((a2 - 2 * a4 * ω ^ 2) ^ 2 + ω ^ 2 * (a3 - 2 * ω ^ 2) ^ 2) := by
    have h1 : AngleKey.cubRe c d σ w ω = 2 * σ * (a2 - 2 * a4 * ω ^ 2) := by
      rw [e2, e4]; simp only [AngleKey.cubRe]; linear_combination hK
    have h2 : AngleKey.cubIm c d σ w ω = 2 * σ * ω * (a3 - 2 * ω ^ 2) := by
      rw [e3]; unfold AngleKey.cubIm; ring
    rw [h1, h2]; ring
  have eB2 : AngleKey.cub2Re c d σ w ω ^ 2 + AngleKey.cub2Im c d σ w ω ^ 2 =
      4 * σ ^ 2 * ((a2 - 5 * a4 * ω ^ 2) ^ 2 + 4 * ω ^ 2 * (a3 - 5 * ω ^ 2) ^ 2) := by
    have h1 : AngleKey.cub2Re c d σ w ω = 2 * σ * (a2 - 5 * a4 * ω ^ 2) := by
      rw [e2, e4]; simp only [AngleKey.cub2Re]; linear_combination hK
    have h2 : AngleKey.cub2Im c d σ w ω = 4 * σ * ω * (a3 - 5 * ω ^ 2) := by
      rw [e3]; unfold AngleKey.cub2Im; ring
    rw [h1, h2]; ring
  have hB1p : 0 < AngleKey.cubRe c d σ w ω ^ 2
      + AngleKey.cubIm c d σ w ω ^ 2 := by rw [eB1]; positivity
  have hB2p : 0 < AngleKey.cub2Re c d σ w ω ^ 2
      + AngleKey.cub2Im c d σ w ω ^ 2 := by rw [eB2]; positivity
  have hKc : (2 : ℂ) * σ * c * K = ((d : ℂ) * c - (ω : ℂ) ^ 2) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 -
      (ω : ℂ) ^ 2) - 2 * σ * (d + c) * ω ^ 2 := by exact_mod_cast hK
  have hRc : (c : ℂ) * g * w = c * K * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) +
      (ω : ℂ) ^ 2 * (((d : ℂ) + c) * ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) +
        2 * σ * (d * c - (ω : ℂ) ^ 2)) := by exact_mod_cast hR
  have hgc : (2 : ℂ) * σ * c * w * g = ((d : ℂ) * c - (ω : ℂ) ^ 2) *
      (((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) ^ 2 + 4 * (σ : ℂ) ^ 2 * (ω : ℂ) ^ 2) := by
    linear_combination 2 * (σ : ℂ) * hRc + ((σ : ℂ) ^ 2 + (w : ℂ) ^ 2 - (ω : ℂ) ^ 2) * hKc
  have eA := AnglePattern.det_eq hKc hgc
  rw [AngleKey.constRed_cast] at eA
  have eAr : 2 * σ * c * (2 * σ * c * w) * (c * (g * w - K * (σ ^ 2 + w ^ 2))) =
      2 * w * σ * ω ^ 2 * c ^ 2 * AngleKey.constRed c d σ w ω := by exact_mod_cast eA
  rw [← e0] at eAr
  have hAp' : AngleKey.constRed c d σ w ω * ω ^ 2 = 2 * σ * a0 := by
    have hcw : 2 * σ * c ^ 2 * w ≠ 0 := by positivity
    have : 2 * σ * c ^ 2 * w * (AngleKey.constRed c d σ w ω * ω ^ 2 - 2 * σ * a0) = 0 := by
      linear_combination -eAr
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hcw
    · linarith
  have hAp : AngleKey.constRed c d σ w ω ≠ 0 := by
    intro h
    rw [h, zero_mul] at hAp'
    have : 0 < 2 * σ * a0 := by positivity
    linarith
  rw [ag_projection hω hσ hw hc hK hR (by rw [← e0]; exact ha0p) hB1p hB2p hJ hB hC hA h2',
    ag_realPart hw.ne' hω.ne' hAp hB1p hB2p, eB1, eB2]
  have ha0' : a0 = AngleKey.constRed c d σ w ω * ω ^ 2 / (2 * σ) := by
    rw [hAp']; field_simp
  rw [ha0']
  field_simp
  ring

/-- The projection-formula combination of the lossless line in the factored reduced
quantities. -/
@[tmio M, powerlib_domain] private theorem ag0_alg {Y1 Y2 Y3 Cp X a c w O j τ P1 G Z3 B1 B2
    Ap : ℂ} (hc : c ≠ 0) (hw : w ≠ 0) (hO : O ≠ 0) (hj : j ≠ 0) (hτ : τ ≠ 0)
    (hB1 : B1 ≠ 0) (hB2 : B2 ≠ 0) (hAp : Ap ≠ 0)
    (e1 : c ^ 2 * w * Y1 = -(w * c * τ ^ 4 * P1))
    (e2 : c ^ 4 * w ^ 2 * Y2 = -(c ^ 2 * τ ^ 4 * G))
    (e3 : c ^ 5 * w ^ 2 * Y3 = τ ^ 4 * Z3)
    (eC : c ^ 3 * w * Cp = -2 * O * j * w * c ^ 2 * τ * B1)
    (eX : c ^ 3 * w * X = -3 * O ^ 2 * w * c ^ 2 * B2)
    (eA : c ^ 2 * w * a = w * c * O ^ 2 * Ap) :
    Cp⁻¹ * Y1 - 2 * (a⁻¹ * (Cp⁻¹ * Y2)) + X⁻¹ * (Cp⁻¹ * Y3) =
      τ ^ 3 * (3 * c ^ 3 * w ^ 2 * O ^ 2 * P1 * Ap * B2 - 6 * c ^ 3 * G * B2 + Z3 * Ap) /
        (6 * c ^ 3 * w ^ 2 * O ^ 3 * Ap * (j * B1 * B2)) := by
  have hY1 : Y1 = -(w * c * τ ^ 4 * P1) / (c ^ 2 * w) := by rw [← e1]; field_simp
  have hY2 : Y2 = -(c ^ 2 * τ ^ 4 * G) / (c ^ 4 * w ^ 2) := by rw [← e2]; field_simp
  have hY3 : Y3 = τ ^ 4 * Z3 / (c ^ 5 * w ^ 2) := by rw [← e3]; field_simp
  have hCp : Cp = -2 * O * j * w * c ^ 2 * τ * B1 / (c ^ 3 * w) := by rw [← eC]; field_simp
  have hX : X = -3 * O ^ 2 * w * c ^ 2 * B2 / (c ^ 3 * w) := by rw [← eX]; field_simp
  have ha : a = w * c * O ^ 2 * Ap / (c ^ 2 * w) := by rw [← eA]; field_simp
  rw [hY1, hY2, hY3, hCp, hX, ha]
  field_simp
  ring

@[tmio M, powerlib_domain] private theorem ag0_star_Q (d w ω : ℝ) :
    star (angleVecQ (d : ℂ) 0 (w : ℂ) (ω : ℂ) I) = angleVecQ (d : ℂ) 0 (w : ℂ) (-(ω : ℂ)) I := by
  simpa using ag_star_Q d 0 w ω

@[tmio M, powerlib_domain] private theorem ag0_star_P (c d g w ω : ℝ) :
    star (angleVecP (c : ℂ) (d : ℂ) (g : ℂ) 0 (w : ℂ) (ω : ℂ) I) =
      angleVecP (c : ℂ) (d : ℂ) (g : ℂ) 0 (w : ℂ) (-(ω : ℂ)) I := by
  simpa using ag_star_P c d g 0 w ω

/-- The lossless Hopf relations in the form of the general pattern (`σ = 0`). -/
@[tmio M, powerlib_domain] private theorem ag0_rel {c d K g w O : ℂ} (hc : c ≠ 0)
    (hd : c * d = O ^ 2)
    (hg0 : c ^ 2 * w * g = (w ^ 2 - O ^ 2) * (c ^ 2 * K + O ^ 4 + c ^ 2 * O ^ 2)) :
    2 * 0 * c * K = (d * c - O ^ 2) * (0 ^ 2 + w ^ 2 - O ^ 2) - 2 * 0 * (d + c) * O ^ 2 ∧
      c * g * w = c * K * (0 ^ 2 + w ^ 2 - O ^ 2) +
        O ^ 2 * ((d + c) * (0 ^ 2 + w ^ 2 - O ^ 2) + 2 * 0 * (d * c - O ^ 2)) := by
  refine ⟨by linear_combination (-(0 ^ 2 + w ^ 2 - O ^ 2)) * hd, ?_⟩
  have h : c * (c * g * w - (c * K * (0 ^ 2 + w ^ 2 - O ^ 2) +
      O ^ 2 * ((d + c) * (0 ^ 2 + w ^ 2 - O ^ 2) + 2 * 0 * (d * c - O ^ 2)))) = 0 := by
    linear_combination hg0 + (-(w ^ 2 - O ^ 2) * O ^ 2) * hd
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hc)

/-- The real part of the reduced projection formula of the lossless line. -/
@[tmio M, powerlib_domain] private theorem ag0_realPart {c K N w ω : ℝ} (hc : c ≠ 0)
    (hw : w ≠ 0) (hω : ω ≠ 0) (hAp : AngleKey.lossConstRed c K w ω ≠ 0)
    (hB1 : 0 < AngleKey.lossCubRe c K w ω ^ 2 + AngleKey.lossCubIm c w ω ^ 2)
    (hB2 : 0 < AngleKey.lossCub2Re c K w ω ^ 2 + AngleKey.lossCub2Im c w ω ^ 2) :
    (((w : ℂ) ^ 2 - (ω : ℂ) ^ 2) ^ 3 * (3 * (c : ℂ) ^ 3 * (w : ℂ) ^ 2 * (ω : ℂ) ^ 2 *
        ((AngleKey.lossTrilin c K ω : ℝ) : ℂ) * ((AngleKey.lossConstRed c K w ω : ℝ) : ℂ) *
          (((AngleKey.lossCub2Re c K w ω : ℝ) : ℂ) + ((AngleKey.lossCub2Im c w ω : ℝ) : ℂ) * I) -
        6 * (c : ℂ) ^ 3 * ((AngleKey.lossBilinRed c K N w ω : ℝ) : ℂ) *
          (((AngleKey.lossCub2Re c K w ω : ℝ) : ℂ) + ((AngleKey.lossCub2Im c w ω : ℝ) : ℂ) * I) +
        (((AngleKey.lossShiftRe c K N w ω : ℝ) : ℂ) + ((AngleKey.lossShiftIm c K N w ω : ℝ) : ℂ)
            * I) *
          ((AngleKey.lossConstRed c K w ω : ℝ) : ℂ)) /
      (6 * (c : ℂ) ^ 3 * (w : ℂ) ^ 2 * (ω : ℂ) ^ 3 * ((AngleKey.lossConstRed c K w ω : ℝ) : ℂ) *
        (I * (((AngleKey.lossCubRe c K w ω : ℝ) : ℂ) + ((AngleKey.lossCubIm c w ω : ℝ) : ℂ) * I) *
          (((AngleKey.lossCub2Re c K w ω : ℝ) : ℂ) + ((AngleKey.lossCub2Im c w ω : ℝ) : ℂ)
              * I)))).re =
      (w ^ 2 - ω ^ 2) ^ 3 * (-3 * ω * c ^ 4 * lossBautin c K N w ω) /
        (6 * c ^ 3 * w ^ 2 * ω ^ 3 * AngleKey.lossConstRed c K w ω
            * ((AngleKey.lossCubRe c K w ω ^ 2 + AngleKey.lossCubIm c w ω ^ 2) *
          (AngleKey.lossCub2Re c K w ω ^ 2 + AngleKey.lossCub2Im c w ω ^ 2))) := by
  have hU : 3 * (c : ℂ) ^ 3 * (w : ℂ) ^ 2 * (ω : ℂ) ^ 2 * ((AngleKey.lossTrilin c K ω : ℝ) : ℂ) *
        ((AngleKey.lossConstRed c K w ω : ℝ) : ℂ) * (((AngleKey.lossCub2Re c K w ω : ℝ) : ℂ)
            + ((AngleKey.lossCub2Im c w ω : ℝ) : ℂ) * I) -
      6 * (c : ℂ) ^ 3 * ((AngleKey.lossBilinRed c K N w ω : ℝ) : ℂ) *
        (((AngleKey.lossCub2Re c K w ω : ℝ) : ℂ) + ((AngleKey.lossCub2Im c w ω : ℝ) : ℂ) * I) +
      (((AngleKey.lossShiftRe c K N w ω : ℝ) : ℂ) + ((AngleKey.lossShiftIm c K N w ω : ℝ) : ℂ)
          * I) *
        ((AngleKey.lossConstRed c K w ω : ℝ) : ℂ) =
      ((AngleKey.lossNumRe c K N w ω : ℝ) : ℂ) + ((AngleKey.lossNumIm c K N w ω : ℝ) : ℂ) * I := by
    rw [AngleKey.lossNumRe_eq, AngleKey.lossNumIm_eq]; push_cast; ring
  have hW : I * (((AngleKey.lossCubRe c K w ω : ℝ) : ℂ) + ((AngleKey.lossCubIm c w ω : ℝ) : ℂ)
      * I) *
      (((AngleKey.lossCub2Re c K w ω : ℝ) : ℂ) + ((AngleKey.lossCub2Im c w ω : ℝ) : ℂ) * I) =
      ((AngleKey.lossDenRe c K w ω : ℝ) : ℂ) + ((AngleKey.lossDenIm c K w ω : ℝ) : ℂ) * I := by
    simp only [AngleKey.lossDenRe, AngleKey.lossDenIm]
    push_cast
    linear_combination (((AngleKey.lossCubRe c K w ω : ℝ) : ℂ)
        * ((AngleKey.lossCub2Im c w ω : ℝ) : ℂ) +
      ((AngleKey.lossCubIm c w ω : ℝ) : ℂ) * ((AngleKey.lossCub2Re c K w ω : ℝ) : ℂ) +
      ((AngleKey.lossCubIm c w ω : ℝ) : ℂ) * ((AngleKey.lossCub2Im c w ω : ℝ) : ℂ) * I) * I_sq
  have hWsq : AngleKey.lossDenRe c K w ω ^ 2 + AngleKey.lossDenIm c K w ω ^ 2 =
      (AngleKey.lossCubRe c K w ω ^ 2 + AngleKey.lossCubIm c w ω ^ 2)
          * (AngleKey.lossCub2Re c K w ω ^ 2 + AngleKey.lossCub2Im c w ω ^ 2) := by
    simp only [AngleKey.lossDenRe, AngleKey.lossDenIm]; ring
  have hWp : AngleKey.lossDenRe c K w ω ^ 2
      + AngleKey.lossDenIm c K w ω ^ 2 ≠ 0 := by rw [hWsq]; positivity
  rw [hU, hW]
  have hnum : ((w : ℂ) ^ 2 - (ω : ℂ) ^ 2) ^ 3 *
      (((AngleKey.lossNumRe c K N w ω : ℝ) : ℂ) + ((AngleKey.lossNumIm c K N w ω : ℝ) : ℂ) * I) =
      (((w ^ 2 - ω ^ 2) ^ 3 * AngleKey.lossNumRe c K N w ω : ℝ) : ℂ) +
        (((w ^ 2 - ω ^ 2) ^ 3 * AngleKey.lossNumIm c K N w ω : ℝ) : ℂ) * I := by push_cast; ring
  have hden : 6 * (c : ℂ) ^ 3 * (w : ℂ) ^ 2 * (ω : ℂ) ^ 3
      * ((AngleKey.lossConstRed c K w ω : ℝ) : ℂ) =
      ((6 * c ^ 3 * w ^ 2 * ω ^ 3 * AngleKey.lossConstRed c K w ω : ℝ) : ℂ) := by push_cast; ring
  have hden0 : 6 * c ^ 3 * w ^ 2 * ω ^ 3 * AngleKey.lossConstRed c K w ω ≠ 0 := by
    have : 6 * c ^ 3 * w ^ 2 * ω ^ 3 ≠ 0 := by positivity
    exact mul_ne_zero this hAp
  rw [hnum, hden, ag_re _ _ _ _ _ hden0 hWp, hWsq]
  have hkey := AngleKey.lossKey c K N w ω
  congr 1
  rw [← hkey]
  ring

/-- **The first Lyapunov coefficient of the lossless pattern, reduced** (`σ = 0`). -/
@[tmio M, powerlib_domain] private theorem ag0_projection {f : State 5 → State 5}
    {c d K g N w ω : ℝ} (hω : 0 < ω) (hw : 0 < w) (hc : 0 < c) (hd : c * d = ω ^ 2)
    (hg0 : c ^ 2 * w * g = (w ^ 2 - ω ^ 2) * (c ^ 2 * K + ω ^ 4 + c ^ 2 * ω ^ 2))
    (hτ : w ^ 2 - ω ^ 2 ≠ 0) (ha0 : 0 < c * (g * w - K * (0 ^ 2 + w ^ 2)))
    (hB1p : 0 < AngleKey.lossCubRe c K w ω ^ 2 + AngleKey.lossCubIm c w ω ^ 2)
    (hB2p : 0 < AngleKey.lossCub2Re c K w ω ^ 2 + AngleKey.lossCub2Im c w ω ^ 2)
    (hJ : jacobianC f 0 = AnglePattern.jac (c : ℂ) (d : ℂ) (K : ℂ) (g : ℂ) 0 (w : ℂ))
    (hB : ∀ u v, bilinC f 0 u v = AnglePattern.bilin (c : ℂ) (g : ℂ) (N : ℂ) u v)
    (hC : ∀ u v z, trilinC f 0 u v z = AnglePattern.trilin (c : ℂ) (g : ℂ) (K : ℂ) u v z)
    (hA : IsUnit (jacobianC f 0).det) (h2' : IsUnit (shift2 (jacobianC f 0) ω).det) :
    firstLyapunov f 0 ω (angleVecQ (d : ℂ) 0 (w : ℂ) (ω : ℂ) I)
        ((starRingEnd ℂ (angleVecP (c : ℂ) (d : ℂ) (g : ℂ) 0 (w : ℂ) (-(ω : ℂ)) I ⬝ᵥ
          angleVecQ (d : ℂ) 0 (w : ℂ) (ω : ℂ) I))⁻¹ •
          angleVecP (c : ℂ) (d : ℂ) (g : ℂ) 0 (w : ℂ) (ω : ℂ) I) =
      1 / (2 * ω) *
      (((w : ℂ) ^ 2 - (ω : ℂ) ^ 2) ^ 3 * (3 * (c : ℂ) ^ 3 * (w : ℂ) ^ 2 * (ω : ℂ) ^ 2 *
        ((AngleKey.lossTrilin c K ω : ℝ) : ℂ) * ((AngleKey.lossConstRed c K w ω : ℝ) : ℂ) *
          (((AngleKey.lossCub2Re c K w ω : ℝ) : ℂ) + ((AngleKey.lossCub2Im c w ω : ℝ) : ℂ) * I) -
        6 * (c : ℂ) ^ 3 * ((AngleKey.lossBilinRed c K N w ω : ℝ) : ℂ) *
          (((AngleKey.lossCub2Re c K w ω : ℝ) : ℂ) + ((AngleKey.lossCub2Im c w ω : ℝ) : ℂ) * I) +
        (((AngleKey.lossShiftRe c K N w ω : ℝ) : ℂ) + ((AngleKey.lossShiftIm c K N w ω : ℝ) : ℂ)
            * I) *
          ((AngleKey.lossConstRed c K w ω : ℝ) : ℂ)) /
      (6 * (c : ℂ) ^ 3 * (w : ℂ) ^ 2 * (ω : ℂ) ^ 3 * ((AngleKey.lossConstRed c K w ω : ℝ) : ℂ) *
        (I * (((AngleKey.lossCubRe c K w ω : ℝ) : ℂ) + ((AngleKey.lossCubIm c w ω : ℝ) : ℂ) * I) *
          (((AngleKey.lossCub2Re c K w ω : ℝ) : ℂ) + ((AngleKey.lossCub2Im c w ω : ℝ) : ℂ)
              * I)))).re := by
  have hdc : (c : ℂ) * d = (ω : ℂ) ^ 2 := by exact_mod_cast hd
  have hg0c : (c : ℂ) ^ 2 * w * g = ((w : ℂ) ^ 2 - (ω : ℂ) ^ 2) *
      ((c : ℂ) ^ 2 * K + (ω : ℂ) ^ 4 + (c : ℂ) ^ 2 * (ω : ℂ) ^ 2) := by exact_mod_cast hg0
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hwc : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have hωc : (ω : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
  have hτc : (w : ℂ) ^ 2 - (ω : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hτ
  obtain ⟨hKc, hRc⟩ := ag0_rel hcc hdc hg0c
  have hcne : ∀ x y : ℝ, 0 < x ^ 2 + y ^ 2 → (x : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro x y hxy h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    simp at hr hi
    rw [hr, hi] at hxy
    norm_num at hxy
  have e1 := AnglePattern.loss_trilin_pairing (d := (d : ℂ)) I_sq hg0c
  have e2' := AnglePattern.loss_bilin_pairing (d := (d : ℂ)) (N := (N : ℂ)) I_sq hg0c
  have e3' := AnglePattern.loss_shift_pairing (N := (N : ℂ)) I_sq hdc hg0c
  have eC := AnglePattern.loss_pairing_eq I_sq hdc hg0c
  have eX := AnglePattern.loss_shiftDet_eq I_sq hdc hg0c
  have eA := AnglePattern.loss_det_eq hg0c
  rw [AngleKey.lossTrilin_cast] at e1
  rw [AngleKey.lossBilinRed_cast] at e2'
  rw [AngleKey.lossShiftRe_cast, AngleKey.lossShiftIm_cast] at e3'
  rw [AngleKey.lossCubRe_cast, AngleKey.lossCubIm_cast] at eC
  rw [AngleKey.lossCub2Re_cast, AngleKey.lossCub2Im_cast] at eX
  rw [AngleKey.lossConstRed_cast] at eA
  have ha : (c : ℂ) * (g * w - K * (0 ^ 2 + (w : ℂ) ^ 2)) ≠ 0 := by
    have : c * (g * w - K * (0 ^ 2 + w ^ 2)) ≠ 0 := ha0.ne'
    exact_mod_cast this
  have hApc : ((AngleKey.lossConstRed c K w ω : ℝ) : ℂ) ≠ 0 := by
    intro h
    rw [h, mul_zero] at eA
    have h0 : (c : ℂ) ^ 2 * w ≠ 0 := mul_ne_zero (pow_ne_zero 2 hcc) hwc
    exact mul_ne_zero h0 ha eA
  have hB1 := hcne _ _ hB1p
  have hB2 := hcne _ _ hB2p
  have hX0 : AnglePattern.shiftDet (c : ℂ) (d : ℂ) (K : ℂ) (g : ℂ) 0 (w : ℂ) (ω : ℂ) I ≠ 0 := by
    intro h
    rw [h, mul_zero] at eX
    have : (-3 : ℂ) * (ω : ℂ) ^ 2 * w * c ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hωc)) hwc)
        (pow_ne_zero 2 hcc)
    exact mul_ne_zero this hB2 eX.symm
  have hq := ag0_star_Q d w ω
  have hr : jacobianC f 0 *ᵥ (((c : ℂ) * (g * w - K * (0 ^ 2 + (w : ℂ) ^ 2)))⁻¹ •
      AnglePattern.solveJ (c : ℂ) (K : ℂ) (g : ℂ) 0 (w : ℂ) (AnglePattern.bilin (c : ℂ) (g : ℂ) (N
          : ℂ)
        (angleVecQ (d : ℂ) 0 (w : ℂ) (ω : ℂ) I) (angleVecQ (d : ℂ) 0 (w : ℂ) (-(ω : ℂ)) I))) =
      bilinC f 0 (angleVecQ (d : ℂ) 0 (w : ℂ) (ω : ℂ) I)
        (star (angleVecQ (d : ℂ) 0 (w : ℂ) (ω : ℂ) I)) := by
    rw [Matrix.mulVec_smul, hJ, AnglePattern.jac_solveJ, hB, hq, smul_smul, inv_mul_cancel₀ ha,
        one_smul]
  have hs : shift2 (jacobianC f 0) ω *ᵥ ((AnglePattern.shiftDet (c : ℂ) (d : ℂ) (K : ℂ) (g : ℂ) 0
      (w : ℂ)
      (ω : ℂ) I)⁻¹ • AnglePattern.solveShift (c : ℂ) (d : ℂ) (K : ℂ) (g : ℂ) 0 (w : ℂ) (ω : ℂ) I
        (AnglePattern.bilin (c : ℂ) (g : ℂ) (N : ℂ) (angleVecQ (d : ℂ) 0 (w : ℂ) (ω : ℂ) I)
          (angleVecQ (d : ℂ) 0 (w : ℂ) (ω : ℂ) I))) =
      bilinC f 0 (angleVecQ (d : ℂ) 0 (w : ℂ) (ω : ℂ) I)
        (angleVecQ (d : ℂ) 0 (w : ℂ) (ω : ℂ) I) := by
    rw [Matrix.mulVec_smul, hJ, shift2, AnglePattern.shift_solveShift, hB, smul_smul,
        inv_mul_cancel₀ hX0, one_smul]
  have hpair : ∀ (z : ℂ) (v : Fin 5 → ℂ),
      pairing ((starRingEnd ℂ z)⁻¹ • angleVecP (c : ℂ) (d : ℂ) (g : ℂ) 0 (w : ℂ) (ω : ℂ) I)
        v = z⁻¹ * (angleVecP (c : ℂ) (d : ℂ) (g : ℂ) 0 (w : ℂ) (-(ω : ℂ)) I ⬝ᵥ v) := by
    intro z v
    rw [← ag0_star_P, ← pairing_eq_dotProduct]
    simp [pairing_apply, Finset.mul_sum, mul_assoc]
  rw [firstLyapunov_eq_of_solve hA h2' hr hs, (bilinC f 0 _).map_smul, (bilinC f 0 _).map_smul,
    hC, hB, hB, hq, (pairing _).map_smul, (pairing _).map_smul, hpair, hpair, hpair, smul_eq_mul,
    smul_eq_mul, ag0_alg hcc hwc hωc I_ne_zero hτc hB1 hB2 hApc e1 e2' e3' eC eX eA]

/-- **The first Lyapunov coefficient of the lossless pattern in closed form** (`σ = 0`,
`c d = ω²`): `ℓ₁ = −(w² − ω²)³ 𝔅_L / (4 c⁴ w² ω a₀ |ĉ(jω)|² |ĉ(2jω)|²)`. -/
@[tmio M, powerlib_domain] private theorem ag0_firstLyapunov {f : State 5 → State 5}
    {c d K g N w ω a4 a3 a2 a0 : ℝ} (hω : 0 < ω) (hw : 0 < w) (hc : 0 < c) (hd : c * d = ω ^ 2)
    (hg0 : c ^ 2 * w * g = (w ^ 2 - ω ^ 2) * (c ^ 2 * K + ω ^ 4 + c ^ 2 * ω ^ 2))
    (hτ : w ^ 2 - ω ^ 2 ≠ 0)
    (e4 : a4 = c + d) (e3 : a3 = w ^ 2 + d * c) (e2 : a2 = (d + c) * w ^ 2 - c * K)
    (e0 : a0 = c * (g * w - K * w ^ 2))
    (k4 : 0 < a4) (k0 : 0 < a2 - a4 * ω ^ 2) (kg : a2 - a4 * ω ^ 2 < a4 * (a3 - ω ^ 2))
    (hJ : jacobianC f 0 = AnglePattern.jac (c : ℂ) (d : ℂ) (K : ℂ) (g : ℂ) 0 (w : ℂ))
    (hB : ∀ u v, bilinC f 0 u v = AnglePattern.bilin (c : ℂ) (g : ℂ) (N : ℂ) u v)
    (hC : ∀ u v z, trilinC f 0 u v z = AnglePattern.trilin (c : ℂ) (g : ℂ) (K : ℂ) u v z)
    (hA : IsUnit (jacobianC f 0).det) (h2' : IsUnit (shift2 (jacobianC f 0) ω).det) :
    firstLyapunov f 0 ω (angleVecQ (d : ℂ) 0 (w : ℂ) (ω : ℂ) I)
        ((starRingEnd ℂ (angleVecP (c : ℂ) (d : ℂ) (g : ℂ) 0 (w : ℂ) (-(ω : ℂ)) I ⬝ᵥ
          angleVecQ (d : ℂ) 0 (w : ℂ) (ω : ℂ) I))⁻¹ •
          angleVecP (c : ℂ) (d : ℂ) (g : ℂ) 0 (w : ℂ) (ω : ℂ) I) =
      -((w ^ 2 - ω ^ 2) ^ 3 * lossBautin c K N w ω /
        (4 * c ^ 4 * w ^ 2 * ω * a0 *
          ((a2 - 2 * a4 * ω ^ 2) ^ 2 + ω ^ 2 * (a3 - 2 * ω ^ 2) ^ 2) *
          ((a2 - 5 * a4 * ω ^ 2) ^ 2 + 4 * ω ^ 2 * (a3 - 5 * ω ^ 2) ^ 2))) := by
  have hc1 := ag_cub_pos (t := 1) k4 k0 kg
  have hc2 := ag_cub_pos (t := 2) k4 k0 kg
  norm_num at hc1 hc2
  have ha0 : a0 = ω ^ 2 * (a2 - a4 * ω ^ 2) := by
    have h : c * (a0 - ω ^ 2 * (a2 - a4 * ω ^ 2)) = 0 := by
      rw [e0, e2, e4]
      linear_combination hg0 + (-ω ^ 2 * (w ^ 2 - ω ^ 2)) * hd
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hc.ne')
  have ha0p : 0 < a0 := by rw [ha0]; positivity
  have eB1 : AngleKey.lossCubRe c K w ω ^ 2 + AngleKey.lossCubIm c w ω ^ 2 =
      c ^ 2 * ((a2 - 2 * a4 * ω ^ 2) ^ 2 + ω ^ 2 * (a3 - 2 * ω ^ 2) ^ 2) := by
    have h1 : AngleKey.lossCubRe c K w ω = c * (a2 - 2 * a4 * ω ^ 2) := by
      rw [e2, e4]; simp only [AngleKey.lossCubRe]; linear_combination (-(w ^ 2 - 2 * ω ^ 2)) * hd
    have h2 : AngleKey.lossCubIm c w ω = c * ω * (a3 - 2 * ω ^ 2) := by
      rw [e3]; simp only [AngleKey.lossCubIm]; linear_combination (-(c * ω)) * hd
    rw [h1, h2]; ring
  have eB2 : AngleKey.lossCub2Re c K w ω ^ 2 + AngleKey.lossCub2Im c w ω ^ 2 =
      c ^ 2 * ((a2 - 5 * a4 * ω ^ 2) ^ 2 + 4 * ω ^ 2 * (a3 - 5 * ω ^ 2) ^ 2) := by
    have h1 : AngleKey.lossCub2Re c K w ω = c * (a2 - 5 * a4 * ω ^ 2) := by
      rw [e2, e4]; simp only [AngleKey.lossCub2Re]; linear_combination (-(w ^ 2 - 5 * ω ^ 2)) * hd
    have h2 : AngleKey.lossCub2Im c w ω = c * (2 * ω) * (a3 - 5 * ω ^ 2) := by
      rw [e3]; simp only [AngleKey.lossCub2Im]; linear_combination (-(2 * c * ω)) * hd
    rw [h1, h2]; ring
  have hB1p : 0 < AngleKey.lossCubRe c K w ω ^ 2
      + AngleKey.lossCubIm c w ω ^ 2 := by rw [eB1]; positivity
  have hB2p : 0 < AngleKey.lossCub2Re c K w ω ^ 2
      + AngleKey.lossCub2Im c w ω ^ 2 := by rw [eB2]; positivity
  have hg0c : (c : ℂ) ^ 2 * w * g = ((w : ℂ) ^ 2 - (ω : ℂ) ^ 2) *
      ((c : ℂ) ^ 2 * K + (ω : ℂ) ^ 4 + (c : ℂ) ^ 2 * (ω : ℂ) ^ 2) := by exact_mod_cast hg0
  have eA := AnglePattern.loss_det_eq hg0c
  rw [AngleKey.lossConstRed_cast] at eA
  have eAr : c ^ 2 * w * (c * (g * w - K * (0 ^ 2 + w ^ 2))) = w * c * ω ^ 2
      * AngleKey.lossConstRed c K w ω := by
    exact_mod_cast eA
  have hAp' : AngleKey.lossConstRed c K w ω * ω ^ 2 = c * a0 := by
    have h : c * w * (AngleKey.lossConstRed c K w ω * ω ^ 2 - c * a0) = 0 := by
      rw [e0]; linear_combination -eAr
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (by positivity)
    · linarith
  have hAp : AngleKey.lossConstRed c K w ω ≠ 0 := by
    intro h
    rw [h, zero_mul] at hAp'
    have : 0 < c * a0 := by positivity
    linarith
  have ha0g : 0 < c * (g * w - K * (0 ^ 2 + w ^ 2)) := by
    have : c * (g * w - K * (0 ^ 2 + w ^ 2)) = a0 := by rw [e0]; ring
    rw [this]; exact ha0p
  rw [ag0_projection hω hw hc hd hg0 hτ ha0g hB1p hB2p hJ hB hC hA h2',
    ag0_realPart hc.ne' hw.ne' hω.ne' hAp hB1p hB2p, eB1, eB2]
  have ha0' : a0 = AngleKey.lossConstRed c K w ω * ω ^ 2 / c := by rw [hAp']; field_simp
  rw [ha0']
  field_simp
  ring

/-- The pairing `⟨p̃, q⟩` of the lossless pattern does not vanish at a Hopf point. -/
@[tmio M, powerlib_domain] private theorem ag0_pairing_ne {c d K g w ω a4 a3 a2 : ℝ}
    (hω : 0 < ω) (hw : 0 < w) (hc : 0 < c) (hd : c * d = ω ^ 2)
    (hg0 : c ^ 2 * w * g = (w ^ 2 - ω ^ 2) * (c ^ 2 * K + ω ^ 4 + c ^ 2 * ω ^ 2))
    (hτ : w ^ 2 - ω ^ 2 ≠ 0)
    (hB : AngleKey.lossCubRe c K w ω ^ 2 + AngleKey.lossCubIm c w ω ^ 2 =
      c ^ 2 * ((a2 - 2 * a4 * ω ^ 2) ^ 2 + ω ^ 2 * (a3 - 2 * ω ^ 2) ^ 2))
    (k4 : 0 < a4) (k0 : 0 < a2 - a4 * ω ^ 2) (kg : a2 - a4 * ω ^ 2 < a4 * (a3 - ω ^ 2)) :
    angleVecP (c : ℂ) (d : ℂ) (g : ℂ) 0 (w : ℂ) (-(ω : ℂ)) I ⬝ᵥ
      angleVecQ (d : ℂ) 0 (w : ℂ) (ω : ℂ) I ≠ 0 := by
  have hdc : (c : ℂ) * d = (ω : ℂ) ^ 2 := by exact_mod_cast hd
  have hg0c : (c : ℂ) ^ 2 * w * g = ((w : ℂ) ^ 2 - (ω : ℂ) ^ 2) *
      ((c : ℂ) ^ 2 * K + (ω : ℂ) ^ 4 + (c : ℂ) ^ 2 * (ω : ℂ) ^ 2) := by exact_mod_cast hg0
  have eC := AnglePattern.loss_pairing_eq I_sq hdc hg0c
  rw [AngleKey.lossCubRe_cast, AngleKey.lossCubIm_cast] at eC
  have hc1 := ag_cub_pos (t := 1) k4 k0 kg
  norm_num at hc1
  intro h
  rw [h, mul_zero] at eC
  have hB0 : ((AngleKey.lossCubRe c K w ω : ℝ) : ℂ) + ((AngleKey.lossCubIm c w ω : ℝ) : ℂ)
      * I ≠ 0 := by
    intro h'
    have hr := congrArg Complex.re h'
    have hi := congrArg Complex.im h'
    simp at hr hi
    have : (c ^ 2 * ((a2 - 2 * a4 * ω ^ 2) ^ 2 + ω ^ 2 * (a3 - 2 * ω ^ 2) ^ 2) : ℝ) = 0 := by
      rw [← hB, hr, hi]; ring
    have : 0 < c ^ 2 * ((a2 - 2 * a4 * ω ^ 2) ^ 2 + ω ^ 2 * (a3 - 2 * ω ^ 2) ^ 2) := by
      positivity
    linarith
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hwc : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have hωc : (ω : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
  have hτc : (w : ℂ) ^ 2 - (ω : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hτ
  have h0 : -2 * (ω : ℂ) * I * w * c ^ 2 * ((w : ℂ) ^ 2 - (ω : ℂ) ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hωc)
      I_ne_zero) hwc) (pow_ne_zero 2 hcc)) hτc
  exact mul_ne_zero h0 hB0 eC.symm

/-! ## The model in the rotated frame -/

/-- The rotation of the current by `θ` with the scalings `a` (filtered power) and `b` (current). -/
private def agMat (a b θ : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, a, 0, 0; 0, 0, 0, b * Real.cos θ, -(b * Real.sin θ);
    0, 0, 0, b * Real.sin θ, b * Real.cos θ]

@[tmio M, powerlib_domain] private theorem agMat_inv {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (θ : ℝ) (x : State 5) :
    Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (agMat a b θ)
      (Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (agMat a⁻¹ b⁻¹ (-θ)) x) = x := by
  have hcs := Real.cos_sq_add_sin_sq θ
  ext i
  fin_cases i <;> simp [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_five, agMat, Real.cos_neg,
    Real.sin_neg, ha]
  · field_simp
    linear_combination (x 3) * hcs
  · field_simp
    linear_combination (x 4) * hcs

/-- The rotation-and-scaling as a linear isomorphism (grid frame to the rotated scaled frame). -/
private def agT (a b θ : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : State 5 ≃L[ℝ] State 5 :=
  ContinuousLinearEquiv.equivOfInverse (Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (agMat a b θ))
    (Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (agMat a⁻¹ b⁻¹ (-θ)))
    (fun x => by simpa using agMat_inv (inv_ne_zero ha) (inv_ne_zero hb) (-θ) x)
    (agMat_inv ha hb θ)

/-- **The rotated scaled reading of a vector**:
`(v₀, v₁, a v₂, b (cos θ v₃ − sin θ v₄), b (sin θ v₃ + cos θ v₄))`. -/
def angleRead (a b θ : ℝ) (v : Fin 5 → ℂ) : Fin 5 → ℂ :=
  ![v 0, v 1, a * v 2, b * ((Real.cos θ : ℂ) * v 3 - (Real.sin θ : ℂ) * v 4),
    b * ((Real.sin θ : ℂ) * v 3 + (Real.cos θ : ℂ) * v 4)]

@[tmio M, powerlib_domain] private theorem agT_cmat {a b θ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (v : Fin 5 → ℂ) : cmat (agT a b θ ha hb : State 5 →L[ℝ] State 5) *ᵥ v = angleRead a b θ v := by
  rw [show (agT a b θ ha hb : State 5 →L[ℝ] State 5) =
    Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (agMat a b θ) from rfl, cmat_toEuclideanCLM]
  ext i
  fin_cases i <;> simp [angleRead, agMat, Matrix.mulVec, dotProduct, Fin.sum_univ_five] <;> ring

@[tmio M, powerlib_domain] private theorem agT_symm_cmat {a b θ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (v : Fin 5 → ℂ) :
    cmat ((agT a b θ ha hb).symm : State 5 →L[ℝ] State 5) *ᵥ v = angleRead a⁻¹ b⁻¹ (-θ) v := by
  rw [show ((agT a b θ ha hb).symm : State 5 →L[ℝ] State 5) =
    Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (agMat a⁻¹ b⁻¹ (-θ)) from rfl,
    cmat_toEuclideanCLM]
  ext i
  fin_cases i <;> simp [angleRead, agMat, Matrix.mulVec, dotProduct, Fin.sum_univ_five] <;> ring

@[tmio M, powerlib_domain] private theorem agT_transpose {a b θ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (v : Fin 5 → ℂ) :
    (cmat (agT a b θ ha hb : State 5 →L[ℝ] State 5))ᵀ *ᵥ v = angleRead a b (-θ) v := by
  rw [show (agT a b θ ha hb : State 5 →L[ℝ] State 5) =
    Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (agMat a b θ) from rfl, cmat_toEuclideanCLM]
  ext i
  fin_cases i <;> simp [angleRead, agMat, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
    Real.cos_neg, Real.sin_neg] <;> ring

@[tmio M, powerlib_domain] private theorem agT_mul_symm {a b θ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    cmat (agT a b θ ha hb : State 5 →L[ℝ] State 5) *
      cmat ((agT a b θ ha hb).symm : State 5 →L[ℝ] State 5) = 1 := by
  rw [← cmat_comp, (agT a b θ ha hb).coe_comp_coe_symm, cmat_id]

@[tmio M, powerlib_domain] private theorem ag_model_hess (m : Model) :
    hess m.field 0 = hess m.g.field m.point := by
  funext k i j
  show iteratedFDeriv ℝ 2 (fun z => m.g.field (z + m.point)) 0 _ _ = _
  simp only [iteratedFDeriv_comp_add_right, zero_add, hess]

@[tmio M, powerlib_domain] private theorem ag_model_third (m : Model) :
    third m.field 0 = third m.g.field m.point := by
  funext k i j l
  show iteratedFDeriv ℝ 3 (fun z => m.g.field (z + m.point)) 0 _ _ = _
  simp only [iteratedFDeriv_comp_add_right, zero_add, third]

@[tmio T, powerlib_foundation] private theorem ag_trig {x y δ : ℂ}
    (h : x = y * (Complex.cos δ ^ 2 + Complex.sin δ ^ 2)) : x = y := by
  rw [h, Complex.cos_sq_add_sin_sq, mul_one]

/-- The frame of the model: rotation by `−δ*`, `P_f ↦ P_f/M`, `i ↦ (L/E) i`. -/
private def Model.agFrame (m : Model) (hp : Meets m .physical) : State 5 ≃L[ℝ] State 5 :=
  agT m.g.M⁻¹ (m.g.L / m.g.E) (-m.δ) (inv_ne_zero hp.2.1.ne') (div_ne_zero hp.1.L.ne' hp.1.E.ne')

/-- **The derivatives in the rotated frame**: in the frame `Model.agFrame` the Jacobian, the
second and the third derivative of a physical balanced model are the patterns with `c = ω_c`,
`d = D/M`, `K = Q/M`, `g = E²/(M L)`, `N = P_ref/M`, `σ = R/L`, `w = ω₀`. -/
@[tmio M, powerlib_domain] private theorem ag_data {m : Model} (hp : Meets m .physical)
    (hb : Meets m .balanced) :
    jacobianC (fun z => m.agFrame hp (m.field ((m.agFrame hp).symm z))) 0 =
        AnglePattern.jac (m.g.ωc : ℂ) ((m.g.D / m.g.M : ℝ) : ℂ) ((m.Q / m.g.M : ℝ) : ℂ)
          ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) ∧
      (∀ u v, bilinC (fun z => m.agFrame hp (m.field ((m.agFrame hp).symm z))) 0 u v =
        AnglePattern.bilin (m.g.ωc : ℂ) ((m.g.E ^ 2 / (m.g.M
            * m.g.L) : ℝ) : ℂ) ((m.g.Pref / m.g.M : ℝ) : ℂ)
          u v) ∧
      (∀ u v z, trilinC (fun z => m.agFrame hp (m.field ((m.agFrame hp).symm z))) 0 u v z =
        AnglePattern.trilin (m.g.ωc : ℂ) ((m.g.E ^ 2 / (m.g.M
            * m.g.L) : ℝ) : ℂ) ((m.Q / m.g.M : ℝ) : ℂ)
          u v z) := by
  have hM := hp.2.1.ne'
  have hL := hp.1.L.ne'
  have hE := hp.1.E.ne'
  set T := m.agFrame hp with hTdef
  have hcsC := Complex.cos_sq_add_sin_sq (m.δ : ℂ)
  have hcs := Real.cos_sq_add_sin_sq m.δ
  have hinv : ∀ u : Fin 5 → ℂ, cmat (T : State 5 →L[ℝ] State 5) *ᵥ
      (cmat (T.symm : State 5 →L[ℝ] State 5) *ᵥ u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, ← cmat_comp, T.coe_comp_coe_symm, cmat_id, Matrix.one_mulVec]
  have hS : ∀ u, cmat (T.symm : State 5 →L[ℝ] State 5) *ᵥ u =
      angleRead m.g.M (m.g.E / m.g.L) m.δ u := fun u => by
    rw [hTdef, Model.agFrame, agT_symm_cmat, inv_inv, inv_div, neg_neg]
  have hT : ∀ u, cmat (T : State 5 →L[ℝ] State 5) *ᵥ u =
      angleRead m.g.M⁻¹ (m.g.L / m.g.E) (-m.δ) u := fun u => agT_cmat _ _ u
  have p0 : m.point 0 = m.δ := by simp [Model.point, qss]
  have p3 : m.point 3 = (m.g.is m.δ).re := by simp [Model.point, qss]
  have p4 : m.point 4 = (m.g.is m.δ).im := by simp [Model.point, qss]
  have hP : m.g.power m.δ (m.g.is m.δ).re (m.g.is m.δ).im = m.g.Pref := hb
  have hQ : m.g.reactive m.δ (m.g.is m.δ).re (m.g.is m.δ).im = m.Q := rfl
  have hMc : (m.g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hLc : (m.g.L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hEc : (m.g.E : ℂ) ≠ 0 := by exact_mod_cast hE
  have hXc : (m.g.X : ℂ) = m.g.ω0 * m.g.L := by simp [Network.X]
  have hLE : (m.g.L : ℂ) / m.g.E * ((m.g.E : ℂ) / m.g.L) = 1 := by field_simp
  refine ⟨?_, fun u v => ?_, fun u v z => ?_⟩
  · have h := jacobianC_conj T m.field 0
    rw [map_zero] at h
    rw [h, Model.jacobianC_field, show (T : State 5 →L[ℝ] State 5) = Matrix.toEuclideanCLM
      (n := Fin 5) (𝕜 := ℝ) (agMat m.g.M⁻¹ (m.g.L / m.g.E) (-m.δ)) from rfl,
      show (T.symm : State 5 →L[ℝ] State 5) = Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ)
        (agMat m.g.M⁻¹⁻¹ (m.g.L / m.g.E)⁻¹ (-(-m.δ))) from rfl, cmat_toEuclideanCLM,
      cmat_toEuclideanCLM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [AnglePattern.jac, agMat, Matrix.mul_apply,
        Fin.sum_univ_five,
      Model.jac, jacobian, Real.cos_neg, Real.sin_neg, hQ, Linear.complexify, hXc]
    all_goals first | ring1 | (field_simp; done) |
      (apply ag_trig (δ := (m.δ : ℂ)); field_simp; done) |
      (apply ag_trig (δ := (m.δ : ℂ)); field_simp; ring1)
  · have h := bilinC_conj T m.field 0 (cmat (T.symm : State 5 →L[ℝ] State 5) *ᵥ u)
      (cmat (T.symm : State 5 →L[ℝ] State 5) *ᵥ v)
    rw [hinv, hinv, map_zero] at h
    rw [h, hS, hS, show bilinC m.field 0 = bilinC m.g.field m.point by
      unfold bilinC; rw [ag_model_hess], bilinC_field_eq, hT, p0, p3, p4, hP]
    ext k
    fin_cases k <;> simp only [AnglePattern.bilin, angleRead, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, Real.cos_neg, Real.sin_neg, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk] <;> push_cast
    all_goals first | ring1 |
      linear_combination ((m.g.ωc : ℂ) * (m.g.E : ℂ) ^ 2 * (m.g.M : ℂ)⁻¹ * (m.g.L : ℂ)⁻¹ *
        (u 0 * v 4 + u 4 * v 0)) * hcsC |
      linear_combination (-((m.g.L : ℂ) / m.g.E) * ((m.g.E : ℂ) / m.g.L) * (u 0 * v 0)) * hcsC +
        (-(u 0 * v 0)) * hLE
  · have h := trilinC_conj T m.field 0 (cmat (T.symm : State 5 →L[ℝ] State 5) *ᵥ u)
      (cmat (T.symm : State 5 →L[ℝ] State 5) *ᵥ v) (cmat (T.symm : State 5 →L[ℝ] State 5) *ᵥ z)
    rw [hinv, hinv, hinv, map_zero] at h
    rw [h, hS, hS, hS, show trilinC m.field 0 = trilinC m.g.field m.point by
      unfold trilinC; rw [ag_model_third], trilinC_field_eq, hT, p0, p3, p4, hQ]
    ext k
    fin_cases k <;> simp only [AnglePattern.trilin, angleRead, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, Real.cos_neg, Real.sin_neg, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk] <;> push_cast
    all_goals first | ring1 |
      linear_combination (-(m.g.ωc : ℂ) * (m.g.E : ℂ) ^ 2 * (m.g.M : ℂ)⁻¹ * (m.g.L : ℂ)⁻¹ *
        (u 0 * v 0 * z 3 + u 0 * v 3 * z 0 + u 3 * v 0 * z 0)) * hcsC |
      linear_combination (-((m.g.L : ℂ) / m.g.E) * ((m.g.E : ℂ) / m.g.L) * (u 0 * v 0 * z 0)) *
        hcsC + (-(u 0 * v 0 * z 0)) * hLE

@[tmio M, powerlib_domain] private theorem agT_symm_transpose {a b θ : ℝ} (ha : a ≠ 0)
    (hb : b ≠ 0) (v : Fin 5 → ℂ) :
    (cmat ((agT a b θ ha hb).symm : State 5 →L[ℝ] State 5))ᵀ *ᵥ v = angleRead a⁻¹ b⁻¹ θ v := by
  rw [show ((agT a b θ ha hb).symm : State 5 →L[ℝ] State 5) =
    Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (agMat a⁻¹ b⁻¹ (-θ)) from rfl,
    cmat_toEuclideanCLM]
  ext i
  fin_cases i <;> simp [angleRead, agMat, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
    Real.cos_neg, Real.sin_neg] <;> ring

@[tmio M, powerlib_domain] private theorem angleRead_inv {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (θ : ℝ) (v : Fin 5 → ℂ) : angleRead a b (-θ) (angleRead a⁻¹ b⁻¹ θ v) = v := by
  have hcsC := Complex.cos_sq_add_sin_sq (θ : ℂ)
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  ext i
  fin_cases i <;> simp only [angleRead, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, Real.cos_neg, Real.sin_neg, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk] <;> push_cast <;> field_simp
  · linear_combination (v 3) * hcsC
  · linear_combination (v 4) * hcsC

/-- The quintic coefficients in the atoms of the rotated pattern (`c = ω_c`, `d = D/M`,
`K = Q/M`, `g = E²/(M L)`, `σ = R/L`, `w = ω₀`). -/
@[tmio M, powerlib_domain] private theorem ag_coeffs {m : Model} (hp : Meets m .physical) :
    m.g.coeff4 = m.g.ωc + m.g.D / m.g.M + 2 * (m.g.R / m.g.L) ∧
    m.g.coeff3 = (m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 + 2 * (m.g.R / m.g.L) *
      (m.g.D / m.g.M + m.g.ωc) + m.g.D / m.g.M * m.g.ωc ∧
    m.g.coeff2 m.Q = (m.g.D / m.g.M + m.g.ωc) * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2) +
      2 * (m.g.R / m.g.L) * (m.g.D / m.g.M) * m.g.ωc - m.g.ωc * (m.Q / m.g.M) ∧
    m.g.coeff1 m.Q = m.g.ωc * (m.g.D / m.g.M * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2) -
      2 * (m.g.R / m.g.L) * (m.Q / m.g.M)) ∧
    m.g.coeff0 m.Q = m.g.ωc * (m.g.E ^ 2 / (m.g.M * m.g.L) * m.g.ω0 -
      m.Q / m.g.M * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2)) := by
  have hM := hp.2.1.ne'
  have hL := hp.1.L.ne'
  have hXL : m.g.X / m.g.L = m.g.ω0 := by simp only [Network.X]; field_simp
  have hρ : m.g.ρ = (m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 := by
    rw [Network.ρ, hXL, Network.σ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [coeff4, Network.σ]; ring
  · rw [coeff3, hρ, Network.σ]; ring
  · rw [coeff2, hρ, Network.σ]; ring
  · rw [coeff1, VSM.coeff1, show m.g.toVSM.ρ = m.g.ρ from rfl, hρ,
      show m.g.toVSM.D = m.g.D from rfl, show m.g.toVSM.M = m.g.M from rfl,
      show m.g.toVSM.σ = m.g.σ from rfl, Network.σ]
    field_simp
  · rw [coeff0, VSM.coeff0, show m.g.toVSM.E = m.g.E from rfl,
      show m.g.toVSM.X = m.g.X from rfl, show m.g.toVSM.L = m.g.L from rfl,
      show m.g.toVSM.M = m.g.M from rfl, show m.g.toVSM.ρ = m.g.ρ from rfl, hρ, Network.X]
    field_simp

/-- The Hopf relations of a model in the atoms of the rotated pattern. -/
@[tmio M, powerlib_domain] private theorem ag_hopf {m : Model} (hp : Meets m .physical) {ω : ℝ}
    (hH : m.HopfAt ω) :
    2 * (m.g.R / m.g.L) * m.g.ωc * (m.Q / m.g.M) =
        (m.g.D / m.g.M * m.g.ωc - ω ^ 2) * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2) -
          2 * (m.g.R / m.g.L) * (m.g.D / m.g.M + m.g.ωc) * ω ^ 2 ∧
      m.g.ωc * (m.g.E ^ 2 / (m.g.M * m.g.L)) * m.g.ω0 =
        m.g.ωc * (m.Q / m.g.M) * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2) +
          ω ^ 2 * ((m.g.D / m.g.M + m.g.ωc) * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2) +
            2 * (m.g.R / m.g.L) * (m.g.D / m.g.M * m.g.ωc - ω ^ 2)) := by
  obtain ⟨c4, c3, c2, c1, c0⟩ := ag_coeffs hp
  obtain ⟨-, e1, e2, -, -, -⟩ := hH
  rw [c3, c1] at e1
  rw [c4, c2, c0] at e2
  exact ⟨by linear_combination -e1, by linear_combination e2⟩

@[tmio M, powerlib_domain] private theorem ag_equilibrium {m : Model} (hp : Meets m .physical)
    (hb : Meets m .balanced) : m.field 0 = 0 := by
  have h' := (m.field_point_eq_zero_iff hp.2.1.ne' hp.2.2.2.ne' hp.1.L.ne'
    hp.1.absSq_pos.ne').mpr hb
  simpa [Model.field] using h'

/-- The determinants of the Jacobian and of `2iω − J` are units in the rotated frame. -/
@[tmio M, powerlib_domain] private theorem ag_isUnit {m : Model} (hp : Meets m .physical)
    {ω : ℝ} (hH : m.HopfAt ω) :
    IsUnit (jacobianC (fun z => m.agFrame hp (m.field ((m.agFrame hp).symm z))) 0).det ∧
      IsUnit (shift2 (jacobianC (fun z => m.agFrame hp (m.field ((m.agFrame hp).symm z))) 0)
        ω).det := by
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_hopfAt hH
  obtain ⟨hA, h2⟩ := Dynamics.CenterManifold.isUnit_det_of_charpoly hH.1.ne' hchar hr
  set T := m.agFrame hp
  have hTS : cmat (T : State 5 →L[ℝ] State 5) * cmat (T.symm : State 5 →L[ℝ] State 5) = 1 := by
    rw [← cmat_comp, T.coe_comp_coe_symm, cmat_id]
  have hdet : ∀ X : Matrix (Fin 5) (Fin 5) ℂ, (cmat (T : State 5 →L[ℝ] State 5) * X *
      cmat (T.symm : State 5 →L[ℝ] State 5)).det = X.det := fun X => by
    have h := congrArg Matrix.det hTS
    rw [Matrix.det_mul, Matrix.det_one] at h
    rw [Matrix.det_mul, Matrix.det_mul]
    linear_combination X.det * h
  have h0 := jacobianC_conj T m.field 0
  rw [map_zero] at h0
  rw [h0]
  refine ⟨by rw [hdet]; exact hA, ?_⟩
  have hs : shift2 (cmat (T : State 5 →L[ℝ] State 5) * jacobianC m.field 0 *
      cmat (T.symm : State 5 →L[ℝ] State 5)) ω = cmat (T : State 5 →L[ℝ] State 5) *
        shift2 (jacobianC m.field 0) ω * cmat (T.symm : State 5 →L[ℝ] State 5) := by
    rw [shift2, shift2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hTS]
  rw [hs, hdet]
  exact h2

/-! ## The critical pair and the first Lyapunov coefficient at every operating angle -/

/-- **The critical right eigenvector at every operating angle**: `angleVecQ` (`d = D/M`,
`σ = R/L`, `w = ω₀`) of the frame rotated with `δ*`, read in the model coordinates
(`P_f = M y₂`, `i = (E/L) e^{jδ*} y`). -/
def Model.critQ (m : Model) (ω : ℝ) : Fin 5 → ℂ :=
  angleRead m.g.M (m.g.E / m.g.L) m.δ (angleVecQ ((m.g.D / m.g.M : ℝ) : ℂ)
    ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) (ω : ℂ) I)

/-- **The critical left eigenvector at every operating angle** (`⟨p, q⟩ = 1`; `c = ω_c`,
`g = E²/(M L)`). -/
def Model.critP (m : Model) (ω : ℝ) : Fin 5 → ℂ :=
  angleRead m.g.M⁻¹ (m.g.L / m.g.E) m.δ
    ((starRingEnd ℂ (angleVecP (m.g.ωc : ℂ) ((m.g.D / m.g.M : ℝ) : ℂ)
      ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) (-(ω : ℂ))
        I ⬝ᵥ angleVecQ ((m.g.D / m.g.M : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) (ω : ℂ)
          I))⁻¹ •
      angleVecP (m.g.ωc : ℂ) ((m.g.D / m.g.M : ℝ) : ℂ) ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ)
        ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) (ω : ℂ) I)

@[tmio M, powerlib_domain] private theorem ag_pos {m : Model} (hp : Meets m .physical)
    (hR : 0 < m.g.R) :
    0 < m.g.R / m.g.L ∧ 0 < m.g.ω0 ∧ 0 < m.g.ωc := by
  obtain ⟨hN, -, -, hc⟩ := hp
  exact ⟨div_pos hR hN.L, hN.ω0, hc⟩

/-- **The cubic-cofactor data at a Hopf point** in the atoms. -/
@[tmio M, powerlib_domain] private theorem ag_cub {m : Model} {ω : ℝ} (hH : m.HopfAt ω) :
    0 < m.g.coeff4 ∧ 0 < m.g.coeff2 m.Q - m.g.coeff4 * ω ^ 2 ∧
      m.g.coeff2 m.Q - m.g.coeff4 * ω ^ 2 < m.g.coeff4 * (m.g.coeff3 - ω ^ 2) :=
  ⟨hH.2.2.2.1, hH.2.2.2.2.1, hH.2.2.2.2.2⟩

/-- **The Hopf relations of the lossless line** (`R = 0`): `ω₀² ≠ ω²`, `ω_c D/M = ω²` and the
gain relation. -/
@[tmio M, powerlib_domain] private theorem ag0_hopf {m : Model} (hp : Meets m .physical)
    (hR : m.g.R = 0) {ω : ℝ} (hH : m.HopfAt ω) :
    m.g.ωc * (m.g.D / m.g.M) = ω ^ 2 ∧
      m.g.ωc ^ 2 * m.g.ω0 * (m.g.E ^ 2 / (m.g.M * m.g.L)) = (m.g.ω0 ^ 2 - ω ^ 2) *
        (m.g.ωc ^ 2 * (m.Q / m.g.M) + ω ^ 4 + m.g.ωc ^ 2 * ω ^ 2) ∧
      m.g.ω0 ^ 2 - ω ^ 2 ≠ 0 := by
  obtain ⟨h1, h2⟩ := ag_hopf hp hH
  have hσ : m.g.R / m.g.L = 0 := by rw [hR, zero_div]
  rw [hσ] at h1 h2
  obtain ⟨hN, hM, -, hc⟩ := hp
  have hE := hN.E
  have hL := hN.L
  have hw := hN.ω0
  have hg : 0 < m.g.ωc * (m.g.E ^ 2 / (m.g.M * m.g.L)) * m.g.ω0 := by positivity
  have hτ : m.g.ω0 ^ 2 - ω ^ 2 ≠ 0 := by
    intro hτ0
    have : m.g.ωc * (m.g.E ^ 2 / (m.g.M * m.g.L)) * m.g.ω0 = 0 := by
      rw [h2]
      have : (0 : ℝ) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2 = 0 := by linarith
      rw [this]
      ring
    linarith
  have hd : m.g.ωc * (m.g.D / m.g.M) = ω ^ 2 := by
    have h : (m.g.D / m.g.M * m.g.ωc - ω ^ 2) * (m.g.ω0 ^ 2 - ω ^ 2) = 0 := by
      linear_combination -h1
    have := (mul_eq_zero.mp h).resolve_right hτ
    linarith
  refine ⟨hd, ?_, hτ⟩
  linear_combination m.g.ωc * h2 + (m.g.ω0 ^ 2 - ω ^ 2) * ω ^ 2 * hd

@[tmio M, powerlib_domain] private theorem ag_pattern_coeffs {m : Model}
    (hp : Meets m .physical) :
    m.g.coeff4 = m.g.ωc + m.g.D / m.g.M + 2 * (m.g.R / m.g.L) ∧
    m.g.coeff3 = (m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 + 2 * (m.g.R / m.g.L) *
      (m.g.D / m.g.M + m.g.ωc) + m.g.D / m.g.M * m.g.ωc ∧
    m.g.coeff2 m.Q = (m.g.D / m.g.M + m.g.ωc) * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2) +
      2 * (m.g.R / m.g.L) * (m.g.D / m.g.M) * m.g.ωc - m.g.ωc * (m.Q / m.g.M) ∧
    m.g.coeff0 m.Q = m.g.ωc * (m.g.E ^ 2 / (m.g.M * m.g.L) * m.g.ω0 -
      m.Q / m.g.M * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2)) := by
  obtain ⟨c4, c3, c2, -, c0⟩ := ag_coeffs hp
  exact ⟨c4, c3, c2, c0⟩

/-- **The critical pair at every operating angle**: at a Hopf point `ω` of its quintic
(`Line.VSMLPF.Model.HopfAt`), (`Model.critQ`, `Model.critP`) is a critical pair of every
balanced physical model (the rotated pattern,
`NormalForm.LyapunovCoefficient.isCriticalPair_conj`; `R > 0` and the lossless line `R = 0`).
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.isCriticalPair_crit {m : Model} (hp : Meets m .physical)
    (hb : Meets m .balanced) {ω : ℝ} (hH : m.HopfAt ω) :
    IsCriticalPair m.field 0 ω (m.critQ ω) (m.critP ω) := by
  obtain ⟨h1, h2⟩ := ag_hopf hp hH
  obtain ⟨hJ, -, -⟩ := ag_data hp hb
  obtain ⟨c4, c3, c2, c0⟩ := ag_pattern_coeffs hp
  obtain ⟨k4, k0, kg⟩ := ag_cub hH
  have hM := hp.2.1.ne'
  have hL := hp.1.L.ne'
  have hE := hp.1.E.ne'
  have hw := hp.1.ω0
  have hc := hp.2.2.2
  set T := m.agFrame hp with hTdef
  have hf : (fun z => T (m.field (T.symm z))) 0 = 0 := by simp [ag_equilibrium hp hb]
  have hc0 : angleVecP (m.g.ωc : ℂ) ((m.g.D / m.g.M : ℝ) : ℂ)
      ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) (-(ω : ℂ))
        I ⬝ᵥ angleVecQ ((m.g.D / m.g.M : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) (ω : ℂ)
          I ≠ 0 := by
    rcases hp.1.R.lt_or_eq with hR | hR
    · have hσ := div_pos hR hp.1.L
      have hg : 2 * (m.g.R / m.g.L) * m.g.ωc * m.g.ω0 * (m.g.E ^ 2 / (m.g.M * m.g.L)) =
          (m.g.D / m.g.M * m.g.ωc - ω ^ 2) * (((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2) ^ 2 +
            4 * (m.g.R / m.g.L) ^ 2 * ω ^ 2) := by
        linear_combination 2 * (m.g.R / m.g.L) * h2 +
          ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2) * h1
      have hB : AngleKey.cubRe m.g.ωc (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 +
          AngleKey.cubIm m.g.ωc (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 =
          4 * (m.g.R / m.g.L) ^ 2 * ((m.g.coeff2 m.Q - 2 * m.g.coeff4 * ω ^ 2) ^ 2 +
            ω ^ 2 * (m.g.coeff3 - 2 * ω ^ 2) ^ 2) := by
        have e1 : AngleKey.cubRe m.g.ωc (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω =
            2 * (m.g.R / m.g.L) * (m.g.coeff2 m.Q - 2 * m.g.coeff4 * ω ^ 2) := by
          rw [c2, c4]; simp only [AngleKey.cubRe]; linear_combination h1
        have e2 : AngleKey.cubIm m.g.ωc (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω =
            2 * (m.g.R / m.g.L) * ω * (m.g.coeff3 - 2 * ω ^ 2) := by
          rw [c3]; unfold AngleKey.cubIm; ring
        rw [e1, e2]; ring
      exact ag_pairing_ne hH.1 hσ hw hc hg hB k4 k0 kg
    · obtain ⟨hd, hg0, hτ⟩ := ag0_hopf hp hR.symm hH
      have hσ : ((m.g.R / m.g.L : ℝ) : ℂ) = 0 := by rw [← hR]; simp
      have hσr : m.g.R / m.g.L = 0 := by rw [← hR, zero_div]
      have hB : AngleKey.lossCubRe m.g.ωc (m.Q / m.g.M) m.g.ω0 ω ^ 2
          + AngleKey.lossCubIm m.g.ωc m.g.ω0 ω ^ 2 =
          m.g.ωc ^ 2 * ((m.g.coeff2 m.Q - 2 * m.g.coeff4 * ω ^ 2) ^ 2 +
            ω ^ 2 * (m.g.coeff3 - 2 * ω ^ 2) ^ 2) := by
        have e1 : AngleKey.lossCubRe m.g.ωc (m.Q / m.g.M) m.g.ω0 ω =
            m.g.ωc * (m.g.coeff2 m.Q - 2 * m.g.coeff4 * ω ^ 2) := by
          rw [c2, c4, hσr]; simp only [AngleKey.lossCubRe]
          linear_combination (-(m.g.ω0 ^ 2 - 2 * ω ^ 2)) * hd
        have e2 : AngleKey.lossCubIm m.g.ωc m.g.ω0 ω = m.g.ωc * ω * (m.g.coeff3 - 2 * ω ^ 2) := by
          rw [c3, hσr]; simp only [AngleKey.lossCubIm]; linear_combination (-(m.g.ωc * ω)) * hd
        rw [e1, e2]; ring
      rw [hσ]
      exact ag0_pairing_ne hH.1 hw hc hd hg0 hτ hB k4 k0 kg
  have hcp := ag_isCriticalPair hH.1 h1 h2 hc0 hf hJ
  have h := isCriticalPair_conj T.symm hcp
  have e : (fun z => T.symm ((fun z => T (m.field (T.symm z))) (T.symm.symm z))) = m.field := by
    funext z
    simp
  rw [e, map_zero, ContinuousLinearEquiv.symm_symm] at h
  rw [hTdef, Model.agFrame, agT_symm_cmat, agT_transpose, inv_inv, inv_div, neg_neg] at h
  exact h

/-- **The first Lyapunov coefficient at every operating angle in closed form** (`R > 0`): for
every balanced physical model with a Hopf point of its quintic at `ω`, at (`Model.critQ`,
`Model.critP`),
`ℓ₁ = Λ 𝔅 / (64 σ⁴ ω₀² ω a₀ |ĉ(iω)|² |ĉ(2iω)|²)`, `σ = R/L`, `Λ = (σ² + ω₀² − ω²)² + 4σ²ω²`,
`𝔅 = Line.VSMLPF.angleBautin ω_c (D/M) (P_ref/M) σ ω₀ ω`, `a₀` the constant coefficient of the
quintic and `ĉ(s) = s³ + a₄ s² + (a₃ − ω²) s + (a₂ − a₄ ω²)` its Hurwitz cubic cofactor
(`|ĉ(iω)|² = (a₂ − 2a₄ω²)² + ω²(a₃ − 2ω²)²`, `|ĉ(2iω)|² = (a₂ − 5a₄ω²)² + 4ω²(a₃ − 5ω²)²`); the
reactive power `Q/M` and the gain `E²/(M L)` are eliminated by the two Hopf relations. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.firstLyapunov_crit {m : Model} (hp : Meets m .physical)
    (hb : Meets m .balanced) (hR : 0 < m.g.R) {ω : ℝ} (hH : m.HopfAt ω) :
    firstLyapunov m.field 0 ω (m.critQ ω) (m.critP ω) =
      (((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2) ^ 2 + 4 * (m.g.R / m.g.L) ^ 2 * ω ^ 2) *
        angleBautin m.g.ωc (m.g.D / m.g.M) (m.g.Pref / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω /
      (64 * (m.g.R / m.g.L) ^ 4 * m.g.ω0 ^ 2 * ω * m.g.coeff0 m.Q *
        ((m.g.coeff2 m.Q - 2 * m.g.coeff4 * ω ^ 2) ^ 2 + ω ^ 2 * (m.g.coeff3 - 2 * ω ^ 2) ^ 2) *
        ((m.g.coeff2 m.Q - 5 * m.g.coeff4 * ω ^ 2) ^ 2 +
          4 * ω ^ 2 * (m.g.coeff3 - 5 * ω ^ 2) ^ 2)) := by
  obtain ⟨h1, h2⟩ := ag_hopf hp hH
  obtain ⟨hσ, hw, hc⟩ := ag_pos hp hR
  obtain ⟨hJ, hB, hC⟩ := ag_data hp hb
  obtain ⟨hA, h2'⟩ := ag_isUnit hp hH
  obtain ⟨c4, c3, c2, c0⟩ := ag_pattern_coeffs hp
  obtain ⟨k4, k0, kg⟩ := ag_cub hH
  have hM := hp.2.1.ne'
  have hL := hp.1.L.ne'
  have hE := hp.1.E.ne'
  set T := m.agFrame hp with hTdef
  rw [← firstLyapunov_conj T m.field 0 ω (m.critQ ω) (m.critP ω), map_zero]
  have hq : cmat (T : State 5 →L[ℝ] State 5) *ᵥ m.critQ ω = angleVecQ ((m.g.D / m.g.M : ℝ) : ℂ)
      ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) (ω : ℂ) I := by
    rw [hTdef, Model.agFrame, agT_cmat, Model.critQ]
    have h := angleRead_inv (inv_ne_zero hM) (div_ne_zero hL hE) m.δ (angleVecQ
      ((m.g.D / m.g.M : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) (ω : ℂ) I)
    rwa [inv_inv, inv_div] at h
  have hp' : (cmat (T.symm : State 5 →L[ℝ] State 5))ᵀ *ᵥ m.critP ω =
      (starRingEnd ℂ (angleVecP (m.g.ωc : ℂ) ((m.g.D / m.g.M : ℝ) : ℂ)
        ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ)
          (-(ω : ℂ)) I ⬝ᵥ angleVecQ ((m.g.D / m.g.M : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ)
            (m.g.ω0 : ℂ) (ω : ℂ) I))⁻¹ •
        angleVecP (m.g.ωc : ℂ) ((m.g.D / m.g.M : ℝ) : ℂ) ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ)
          ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) (ω : ℂ) I := by
    rw [hTdef, Model.agFrame, agT_symm_transpose, Model.critP, inv_inv, inv_div]
    have h := angleRead_inv hM (div_ne_zero hE hL) m.δ ((starRingEnd ℂ (angleVecP (m.g.ωc : ℂ)
      ((m.g.D / m.g.M : ℝ) : ℂ) ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ)
        (m.g.ω0 : ℂ) (-(ω : ℂ)) I ⬝ᵥ angleVecQ ((m.g.D / m.g.M : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ)
          (m.g.ω0 : ℂ) (ω : ℂ) I))⁻¹ • angleVecP (m.g.ωc : ℂ) ((m.g.D / m.g.M : ℝ) : ℂ)
        ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) ((m.g.R / m.g.L : ℝ) : ℂ) (m.g.ω0 : ℂ) (ω : ℂ) I)
    rwa [inv_div] at h
  rw [hq, hp']
  exact ag_firstLyapunov hH.1 hσ hw hc h1 h2 c4 c3 c2 c0 k4 k0 kg hJ hB hC hA h2'

@[tmio M, powerlib_domain] private theorem ag_den_pos {m : Model} (hp : Meets m .physical)
    (hR : 0 < m.g.R) {ω : ℝ} (hH : m.HopfAt ω) :
    0 < (((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2) ^ 2 + 4 * (m.g.R / m.g.L) ^ 2 * ω ^ 2) /
      (64 * (m.g.R / m.g.L) ^ 4 * m.g.ω0 ^ 2 * ω * m.g.coeff0 m.Q *
        ((m.g.coeff2 m.Q - 2 * m.g.coeff4 * ω ^ 2) ^ 2 + ω ^ 2 * (m.g.coeff3 - 2 * ω ^ 2) ^ 2) *
        ((m.g.coeff2 m.Q - 5 * m.g.coeff4 * ω ^ 2) ^ 2 +
          4 * ω ^ 2 * (m.g.coeff3 - 5 * ω ^ 2) ^ 2)) := by
  obtain ⟨hσ, hw, -⟩ := ag_pos hp hR
  obtain ⟨k4, k0, kg⟩ := ag_cub hH
  have hω := hH.1
  have ha0 : 0 < m.g.coeff0 m.Q := by
    have e := hH.2.2.1
    have : m.g.coeff0 m.Q = ω ^ 2 * (m.g.coeff2 m.Q - m.g.coeff4 * ω ^ 2) := by
      linear_combination e
    rw [this]; positivity
  have hc1 := ag_cub_pos (t := 1) k4 k0 kg
  have hc2 := ag_cub_pos (t := 2) k4 k0 kg
  norm_num at hc1 hc2
  positivity

/-- **The symbolic boundary between sub- and supercritical Hopf points at every operating
angle** (`R > 0`): for every critical pair of a balanced physical model at a Hopf point of its
quintic, `sign ℓ₁ = sign 𝔅(ω_c, D/M, P_ref/M, R/L, ω₀, ω)` (`Line.VSMLPF.angleBautin`). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.sign_firstLyapunov_crit {m : Model}
    (hp : Meets m .physical) (hb : Meets m .balanced) (hR : 0 < m.g.R) {ω : ℝ}
    (hH : m.HopfAt ω) {q p : Fin 5 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p) :
    SignType.sign (firstLyapunov m.field 0 ω q p) =
      SignType.sign (angleBautin m.g.ωc (m.g.D / m.g.M) (m.g.Pref / m.g.M) (m.g.R / m.g.L)
        m.g.ω0 ω) := by
  rw [m.sign_firstLyapunov_eq_of_hopfAt hH (m.isCriticalPair_crit hp hb hH) hcp,
    m.firstLyapunov_crit hp hb hR hH, mul_div_right_comm, sign_mul,
    sign_pos (ag_den_pos hp hR hH), one_mul]

/-- **Supercritical Hopf points at every operating angle are locally asymptotically stable**
(`R > 0`): a balanced physical model with a Hopf point at `ω` and
`𝔅(ω_c, D/M, P_ref/M, R/L, ω₀, ω) < 0` is locally asymptotically stable. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_of_angleBautin_neg
    (m : Model) (hp : Meets m .physical) (hb : Meets m .balanced) (hR : 0 < m.g.R) {ω : ℝ}
    (hH : m.HopfAt ω)
    (hB : angleBautin m.g.ωc (m.g.D / m.g.M) (m.g.Pref / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω < 0) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  have hcp := m.isCriticalPair_crit hp hb hH
  have hs := m.sign_firstLyapunov_crit hp hb hR hH hcp
  rw [sign_neg hB] at hs
  exact mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg m hH hcp
    (sign_eq_neg_one_iff.mp hs)

/-- **Subcritical Hopf points at every operating angle are unstable** (`R > 0`): a balanced
physical model with a Hopf point at `ω` and `𝔅(ω_c, D/M, P_ref/M, R/L, ω₀, ω) > 0` is unstable. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_angleBautin_pos (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hR : 0 < m.g.R) {ω : ℝ} (hH : m.HopfAt ω)
    (hB : 0 < angleBautin m.g.ωc (m.g.D / m.g.M) (m.g.Pref / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  have hcp := m.isCriticalPair_crit hp hb hH
  have hs := m.sign_firstLyapunov_crit hp hb hR hH hcp
  rw [sign_pos hB] at hs
  exact mem_den_unstable_of_firstLyapunov_pos m hH hcp (sign_eq_one_iff.mp hs)

/-! ## The lossless line -/

@[tmio M, powerlib_domain] private theorem ag0_den_pos {m : Model} (hp : Meets m .physical)
    {ω : ℝ} (hH : m.HopfAt ω) :
    0 < 4 * m.g.ωc ^ 4 * m.g.ω0 ^ 2 * ω * m.g.coeff0 m.Q *
        ((m.g.coeff2 m.Q - 2 * m.g.coeff4 * ω ^ 2) ^ 2 + ω ^ 2 * (m.g.coeff3 - 2 * ω ^ 2) ^ 2) *
        ((m.g.coeff2 m.Q - 5 * m.g.coeff4 * ω ^ 2) ^ 2 +
          4 * ω ^ 2 * (m.g.coeff3 - 5 * ω ^ 2) ^ 2) := by
  obtain ⟨k4, k0, kg⟩ := ag_cub hH
  have hω := hH.1
  have hw := hp.1.ω0
  have hc := hp.2.2.2
  have ha0 : 0 < m.g.coeff0 m.Q := by
    have e := hH.2.2.1
    have : m.g.coeff0 m.Q = ω ^ 2 * (m.g.coeff2 m.Q - m.g.coeff4 * ω ^ 2) := by
      linear_combination e
    rw [this]; positivity
  have hc1 := ag_cub_pos (t := 1) k4 k0 kg
  have hc2 := ag_cub_pos (t := 2) k4 k0 kg
  norm_num at hc1 hc2
  positivity

/-- **The first Lyapunov coefficient of the lossless line in closed form** (`R = 0`): at a Hopf
point `ω` of a balanced physical model (`ω₀² ≠ ω²` and `ω_c D/M = ω²` there), at
(`Model.critQ`, `Model.critP`),
`ℓ₁ = −(ω₀² − ω²)³ 𝔅_L / (4 ω_c⁴ ω₀² ω a₀ |ĉ(iω)|² |ĉ(2iω)|²)`,
`𝔅_L = Line.VSMLPF.lossBautin ω_c (Q/M) (P_ref/M) ω₀ ω` (`D/M` and the gain `E²/(M L)` eliminated
by the two Hopf relations). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.firstLyapunov_crit_lossless {m : Model}
    (hp : Meets m .physical) (hb : Meets m .balanced) (hR : m.g.R = 0) {ω : ℝ}
    (hH : m.HopfAt ω) :
    firstLyapunov m.field 0 ω (m.critQ ω) (m.critP ω) =
      -((m.g.ω0 ^ 2 - ω ^ 2) ^ 3 *
          lossBautin m.g.ωc (m.Q / m.g.M) (m.g.Pref / m.g.M) m.g.ω0 ω /
        (4 * m.g.ωc ^ 4 * m.g.ω0 ^ 2 * ω * m.g.coeff0 m.Q *
          ((m.g.coeff2 m.Q - 2 * m.g.coeff4 * ω ^ 2) ^ 2 + ω ^ 2 * (m.g.coeff3 - 2 * ω ^ 2) ^ 2) *
          ((m.g.coeff2 m.Q - 5 * m.g.coeff4 * ω ^ 2) ^ 2 +
            4 * ω ^ 2 * (m.g.coeff3 - 5 * ω ^ 2) ^ 2))) := by
  obtain ⟨hd, hg0, hτ⟩ := ag0_hopf hp hR hH
  obtain ⟨hJ, hB, hC⟩ := ag_data hp hb
  obtain ⟨hA, h2'⟩ := ag_isUnit hp hH
  obtain ⟨c4, c3, c2, c0⟩ := ag_pattern_coeffs hp
  obtain ⟨k4, k0, kg⟩ := ag_cub hH
  have hσ : ((m.g.R / m.g.L : ℝ) : ℂ) = 0 := by rw [hR]; simp
  have hσr : m.g.R / m.g.L = 0 := by rw [hR, zero_div]
  rw [hσ] at hJ
  have e4 : m.g.coeff4 = m.g.ωc + m.g.D / m.g.M := by rw [c4, hσr]; ring
  have e3 : m.g.coeff3 = m.g.ω0 ^ 2 + m.g.D / m.g.M * m.g.ωc := by rw [c3, hσr]; ring
  have e2 : m.g.coeff2 m.Q = (m.g.D / m.g.M + m.g.ωc) * m.g.ω0 ^ 2 - m.g.ωc * (m.Q / m.g.M) := by
    rw [c2, hσr]; ring
  have e0 : m.g.coeff0 m.Q = m.g.ωc * (m.g.E ^ 2 / (m.g.M * m.g.L) * m.g.ω0 -
      m.Q / m.g.M * m.g.ω0 ^ 2) := by rw [c0, hσr]; ring
  have hM := hp.2.1.ne'
  have hL := hp.1.L.ne'
  have hE := hp.1.E.ne'
  set T := m.agFrame hp with hTdef
  rw [← firstLyapunov_conj T m.field 0 ω (m.critQ ω) (m.critP ω), map_zero]
  have hq : cmat (T : State 5 →L[ℝ] State 5) *ᵥ m.critQ ω = angleVecQ ((m.g.D / m.g.M : ℝ) : ℂ)
      0 (m.g.ω0 : ℂ) (ω : ℂ) I := by
    rw [hTdef, Model.agFrame, agT_cmat, Model.critQ, hσ]
    have h := angleRead_inv (inv_ne_zero hM) (div_ne_zero hL hE) m.δ (angleVecQ
      ((m.g.D / m.g.M : ℝ) : ℂ) 0 (m.g.ω0 : ℂ) (ω : ℂ) I)
    rwa [inv_inv, inv_div] at h
  have hp' : (cmat (T.symm : State 5 →L[ℝ] State 5))ᵀ *ᵥ m.critP ω =
      (starRingEnd ℂ (angleVecP (m.g.ωc : ℂ) ((m.g.D / m.g.M : ℝ) : ℂ)
        ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) 0 (m.g.ω0 : ℂ) (-(ω : ℂ)) I ⬝ᵥ
          angleVecQ ((m.g.D / m.g.M : ℝ) : ℂ) 0 (m.g.ω0 : ℂ) (ω : ℂ) I))⁻¹ •
        angleVecP (m.g.ωc : ℂ) ((m.g.D / m.g.M : ℝ) : ℂ) ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ)
          0 (m.g.ω0 : ℂ) (ω : ℂ) I := by
    rw [hTdef, Model.agFrame, agT_symm_transpose, Model.critP, inv_inv, inv_div, hσ]
    have h := angleRead_inv hM (div_ne_zero hE hL) m.δ ((starRingEnd ℂ (angleVecP (m.g.ωc : ℂ)
      ((m.g.D / m.g.M : ℝ) : ℂ) ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) 0
        (m.g.ω0 : ℂ) (-(ω : ℂ)) I ⬝ᵥ angleVecQ ((m.g.D / m.g.M : ℝ) : ℂ) 0
          (m.g.ω0 : ℂ) (ω : ℂ) I))⁻¹ • angleVecP (m.g.ωc : ℂ) ((m.g.D / m.g.M : ℝ) : ℂ)
        ((m.g.E ^ 2 / (m.g.M * m.g.L) : ℝ) : ℂ) 0 (m.g.ω0 : ℂ) (ω : ℂ) I)
    rwa [inv_div] at h
  rw [hq, hp']
  exact ag0_firstLyapunov hH.1 hp.1.ω0 hp.2.2.2 hd hg0 hτ e4 e3 e2 e0 k4 k0 kg hJ hB hC hA h2'

/-- **The sign law of the lossless line** (`R = 0`): for every critical pair at a Hopf point of
a balanced physical model, `sign ℓ₁ = −sign((ω₀² − ω²) 𝔅_L)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.sign_firstLyapunov_crit_lossless {m : Model}
    (hp : Meets m .physical) (hb : Meets m .balanced) (hR : m.g.R = 0) {ω : ℝ}
    (hH : m.HopfAt ω) {q p : Fin 5 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p) :
    SignType.sign (firstLyapunov m.field 0 ω q p) =
      -SignType.sign ((m.g.ω0 ^ 2 - ω ^ 2) *
        lossBautin m.g.ωc (m.Q / m.g.M) (m.g.Pref / m.g.M) m.g.ω0 ω) := by
  obtain ⟨-, -, hτ⟩ := ag0_hopf hp hR hH
  have hden := ag0_den_pos hp hH
  rw [m.sign_firstLyapunov_eq_of_hopfAt hH (m.isCriticalPair_crit hp hb hH) hcp,
    m.firstLyapunov_crit_lossless hp hb hR hH]
  have e : ∀ x y z : ℝ, -(x ^ 3 * y / z) = (-(x ^ 2 / z)) * (x * y) := fun x y z => by ring
  rw [e, sign_mul, sign_neg (neg_neg_of_pos (div_pos (sq_pos_of_ne_zero hτ) hden)), neg_one_mul]

/-- **Supercritical Hopf points of the lossless line are locally asymptotically stable**: a
balanced physical model with `R = 0`, a Hopf point at `ω` and `(ω₀² − ω²) 𝔅_L > 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_of_lossBautin_pos
    (m : Model) (hp : Meets m .physical) (hb : Meets m .balanced) (hR : m.g.R = 0) {ω : ℝ}
    (hH : m.HopfAt ω) (hB : 0 < (m.g.ω0 ^ 2 - ω ^ 2) *
      lossBautin m.g.ωc (m.Q / m.g.M) (m.g.Pref / m.g.M) m.g.ω0 ω) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  have hcp := m.isCriticalPair_crit hp hb hH
  have hs := m.sign_firstLyapunov_crit_lossless hp hb hR hH hcp
  rw [sign_pos hB] at hs
  exact mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg m hH hcp
    (sign_eq_neg_one_iff.mp hs)

/-- **Subcritical Hopf points of the lossless line are unstable**: a balanced physical model with
`R = 0`, a Hopf point at `ω` and `(ω₀² − ω²) 𝔅_L < 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_lossBautin_neg (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hR : m.g.R = 0) {ω : ℝ} (hH : m.HopfAt ω)
    (hB : (m.g.ω0 ^ 2 - ω ^ 2) * lossBautin m.g.ωc (m.Q / m.g.M) (m.g.Pref / m.g.M) m.g.ω0 ω < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  have hcp := m.isCriticalPair_crit hp hb hH
  have hs := m.sign_firstLyapunov_crit_lossless hp hb hR hH hcp
  rw [sign_neg hB, neg_neg] at hs
  exact mem_den_unstable_of_firstLyapunov_pos m hH hcp (sign_eq_one_iff.mp hs)

end VSMLPF
end powerlib.GFM.Line
