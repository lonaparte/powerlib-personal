import theorem.PH.PositiveReal
import theorem.Transform.Planar

/-! # Positive realness of `2 × 2` complex matrices and the two-channel port law

Static foundation for port admittances with two real channels (dq frame).

Scope.
* Complex `2 × 2` matrices at one fixed Laplace variable; positive realness in the sense of
  `PositiveRealAt` (`Re uᴴ (G + Gᴴ) u ≥ 0` for every complex `u`,
  `theorem/PH/PositiveReal.lean`); real orthogonal changes of frame (`Q Qᵀ = I`, any size).
* The port law is pure matrix algebra (invertibility of `N + B K C_i` as hypothesis); no
  realization, pole or stability statement.

Source: the trace–determinant test for a `2 × 2` Hermitian matrix (R. A. Horn and C. R. Johnson,
*Matrix Analysis*, 2nd ed., Cambridge 2013, §7.1, §7.2 (positive semidefiniteness of principal
minors)); positive realness at one frequency, work-sync `theory/T-ph.md` §1.10; the port
admittances of `theorem/GridTiedConverter/GFM/Port/Admittance.lean`,
`theorem/GridTiedConverter/GFM/Port/DroopAdmittance.lean` and
`theorem/GridTiedConverter/GFM/Port/CascadeAdmittance.lean`, which read these laws.

Results.
* `syncY N T B K C_i C_v = (N + B K C_i)⁻¹ (T + B K C_v)` solves
  `(N + B K C_i) Y = T + B K C_v` (`syncY_spec`): the elimination of two feedback channels
  `c = −K (C_i i + C_v v)` from `N i + T v = B c`.
* `positiveRealAt_fin_two_iff`: `G + Gᴴ ⪰ 0` iff `Re G₀₀ ≥ 0`, `Re G₁₁ ≥ 0` and
  `|G₀₁ + conj G₁₀|² ≤ 4 Re G₀₀ Re G₁₁`.
* `positiveRealAt_complexSymm_add_iff`: for `Z = (z I + x J) + K` with `x` real and `K` traceless
  on the diagonal (`K₁₁ = −K₀₀`), positive real iff `Re z ≥ 0` and
  `4 (Re K₀₀)² + |K₀₁ + conj K₁₀|² ≤ 4 (Re z)²`.
* `positiveRealAt_orthogonal_iff`: `Qᵀ G Q` is positive real iff `G` is (`Q Qᵀ = I`, real `Q`).
* `normSq_mul_hermDefect`: for `t K₀₀ = r` (`r` real) and `t (K₀₀² + K₀₁ K₁₀) = −λ` (`λ` real),
  `|t|² (4 (Re K₀₀)² + |K₀₁ + conj K₁₀|²) = 4 r² + |t K₀₁ + conj (t K₁₀)|²`.

Family and connection conclusions.
* None: every result is a static matrix identity or criterion (public foundation).
-/

noncomputable section
namespace powerlib.PH
open Matrix Linear

/-- The two-channel port law: a two-port whose port quantity `i` obeys `N i + T v = B c`
(`v` the port input) and whose two channels answer `c = −K (C_i i + C_v v)` has the transfer
`−i = (N + B K C_i)⁻¹ (T + B K C_v) v`. -/
def syncY (N T B K Ci Cv : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (N + B * K * Ci)⁻¹ * (T + B * K * Cv)

/-- The port law solves its port equation `(N + B K C_i) Y = T + B K C_v`. -/
@[tmio T, powerlib_foundation] theorem syncY_spec {N T B K Ci Cv : Matrix (Fin 2) (Fin 2) ℂ}
    (h : (N + B * K * Ci).det ≠ 0) : (N + B * K * Ci) * syncY N T B K Ci Cv = T + B * K * Cv := by
  rw [syncY, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h),
    Matrix.one_mul]

/-! ## Positive realness of `2 × 2` matrices -/

/-- The quadratic form of a `2 × 2` complex matrix:
`Re uᴴ G u = Re G₀₀ |u₀|² + Re G₁₁ |u₁|² + Re (conj u₀ u₁ β)`, `β = G₀₁ + conj G₁₀`. -/
@[tmio T, powerlib_foundation] private theorem form_fin_two (G : Matrix (Fin 2) (Fin 2) ℂ)
    (u : Fin 2 → ℂ) :
    (star u ⬝ᵥ (G *ᵥ u)).re = (G 0 0).re * Complex.normSq (u 0) +
      (G 1 1).re * Complex.normSq (u 1) +
        ((starRingEnd ℂ) (u 0) * u 1 * (G 0 1 + (starRingEnd ℂ) (G 1 0))).re := by
  simp only [dotProduct, mulVec, Fin.sum_univ_two, Pi.star_apply, Complex.star_def,
    Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.mul_im,
    Complex.add_im, Complex.normSq_apply]
  ring

/-- **Positive realness of a `2 × 2` matrix.** `G + Gᴴ ⪰ 0` iff the diagonal of `G` has
nonnegative real parts and `|G₀₁ + conj G₁₀|² ≤ 4 Re G₀₀ Re G₁₁` (the trace and determinant of
the Hermitian part `G + Gᴴ`). -/
@[tmio T, powerlib_foundation] theorem positiveRealAt_fin_two_iff
    (G : Matrix (Fin 2) (Fin 2) ℂ) :
    PositiveRealAt G ↔ 0 ≤ (G 0 0).re ∧ 0 ≤ (G 1 1).re ∧
      Complex.normSq (G 0 1 + (starRingEnd ℂ) (G 1 0)) ≤ 4 * (G 0 0).re * (G 1 1).re := by
  rw [positiveRealAt_iff_re]
  simp only [form_fin_two]
  set a := (G 0 0).re
  set d := (G 1 1).re
  set β := G 0 1 + (starRingEnd ℂ) (G 1 0)
  constructor
  · intro h
    have ha : 0 ≤ a := by simpa using h ![1, 0]
    have hd : 0 ≤ d := by simpa using h ![0, 1]
    refine ⟨ha, hd, ?_⟩
    rcases ha.lt_or_eq with ha' | ha'
    · have h1 := h ![-β, ((2 * a : ℝ) : ℂ)]
      have e : (starRingEnd ℂ) (-β) * ((2 * a : ℝ) : ℂ) * β =
          ((-(2 * a * Complex.normSq β) : ℝ) : ℂ) := by
        push_cast; rw [map_neg, Complex.normSq_eq_conj_mul_self]; ring
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e, Complex.ofReal_re,
        Complex.normSq_neg, Complex.normSq_ofReal] at h1
      have h2 : 0 ≤ a * (4 * a * d - Complex.normSq β) := by nlinarith [h1]
      nlinarith [(mul_nonneg_iff_of_pos_left ha').mp h2]
    · by_contra hlt
      rw [not_le, ← ha', mul_zero, zero_mul] at hlt
      set t : ℝ := (d + 1) / Complex.normSq β with ht
      have h1 := h ![-((t : ℂ) * β), 1]
      have e : (starRingEnd ℂ) (-((t : ℂ) * β)) * β = ((-(t * Complex.normSq β)) : ℝ) := by
        push_cast
        rw [map_neg, map_mul, Complex.conj_ofReal, Complex.normSq_eq_conj_mul_self]
        ring
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, e, Complex.ofReal_re,
        Complex.normSq_one, ← ha', zero_mul, zero_add] at h1
      have : t * Complex.normSq β = d + 1 := by rw [ht]; field_simp
      linarith
  · rintro ⟨ha, hd, hβ⟩ u
    have hre : -(‖β‖ * (‖u 0‖ * ‖u 1‖)) ≤ ((starRingEnd ℂ) (u 0) * u 1 * β).re := by
      have := Complex.abs_re_le_norm ((starRingEnd ℂ) (u 0) * u 1 * β)
      rw [norm_mul, norm_mul, Complex.norm_conj] at this
      nlinarith [neg_abs_le ((starRingEnd ℂ) (u 0) * u 1 * β).re]
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_eq_norm_sq] at hβ
    have hb : 0 ≤ ‖β‖ := norm_nonneg _
    have hp : 0 ≤ ‖u 0‖ := norm_nonneg _
    have hq : 0 ≤ ‖u 1‖ := norm_nonneg _
    have hS : 0 ≤ a * ‖u 0‖ ^ 2 + d * ‖u 1‖ ^ 2 := by positivity
    have h4 := mul_le_mul_of_nonneg_right hβ (by positivity : (0 : ℝ) ≤ (‖u 0‖ * ‖u 1‖) ^ 2)
    have hsq : (‖β‖ * (‖u 0‖ * ‖u 1‖)) ^ 2 ≤ (a * ‖u 0‖ ^ 2 + d * ‖u 1‖ ^ 2) ^ 2 := by
      nlinarith [sq_nonneg (a * ‖u 0‖ ^ 2 - d * ‖u 1‖ ^ 2)]
    have hle := (pow_le_pow_iff_left₀ (by positivity) hS two_ne_zero).mp hsq
    linarith

/-- **A traceless perturbation of a complex-symmetric matrix.** For `Z = (z I + x J) + K` with
`x` real and `K₁₁ = −K₀₀`: `Z + Zᴴ ⪰ 0` iff `Re z ≥ 0` and
`4 (Re K₀₀)² + |K₀₁ + conj K₁₀|² ≤ 4 (Re z)²` (the eigenvalues of the Hermitian part are
`2 Re z ± √(4 (Re K₀₀)² + |K₀₁ + conj K₁₀|²)`). -/
@[tmio T, powerlib_foundation] theorem positiveRealAt_complexSymm_add_iff (z : ℂ) (x : ℝ)
    {K : Matrix (Fin 2) (Fin 2) ℂ} (hK : K 1 1 = -K 0 0) :
    PositiveRealAt (Transform.complexSymm z (x : ℂ) + K) ↔ 0 ≤ z.re ∧
      4 * (K 0 0).re ^ 2 + Complex.normSq (K 0 1 + (starRingEnd ℂ) (K 1 0)) ≤ 4 * z.re ^ 2 := by
  rw [positiveRealAt_fin_two_iff]
  have hβ : (Transform.complexSymm z (x : ℂ) + K) 0 1 +
      (starRingEnd ℂ) ((Transform.complexSymm z (x : ℂ) + K) 1 0) =
      K 0 1 + (starRingEnd ℂ) (K 1 0) := by
    simp [Transform.complexSymm]
    ring
  rw [hβ]
  simp only [Matrix.add_apply, Transform.complexSymm, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, hK,
    Complex.add_re, Complex.neg_re]
  have hn := Complex.normSq_nonneg (K 0 1 + (starRingEnd ℂ) (K 1 0))
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨by linarith, by nlinarith⟩
  · rintro ⟨h0, h1⟩
    obtain ⟨hl, hr⟩ := abs_le_of_sq_le_sq' (a := (K 0 0).re) (b := z.re) (by nlinarith) h0
    exact ⟨by linarith, by linarith, by nlinarith⟩

/-- **Positive realness is invariant under a real orthogonal change of frame**:
`Qᵀ G Q` is positive real iff `G` is (`Q Qᵀ = I`). -/
@[tmio T, powerlib_foundation] theorem positiveRealAt_orthogonal_iff {m : ℕ}
    {Q : Matrix (Fin m) (Fin m) ℝ} (hQ : Q * Qᵀ = 1) (G : Matrix (Fin m) (Fin m) ℂ) :
    PositiveRealAt (complexify Qᵀ * G * complexify Q) ↔ PositiveRealAt G := by
  have key : ∀ u : Fin m → ℂ, star u ⬝ᵥ ((complexify Qᵀ * G * complexify Q) *ᵥ u) =
      star (complexify Q *ᵥ u) ⬝ᵥ (G *ᵥ (complexify Q *ᵥ u)) := by
    intro u
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.star_mulVec, phCx_complexify_conjTranspose]
  rw [positiveRealAt_iff_re, positiveRealAt_iff_re]
  constructor
  · intro h w
    have := h (complexify Qᵀ *ᵥ w)
    rwa [key, Matrix.mulVec_mulVec, ← Matrix.map_mul, hQ, Matrix.map_one _ (map_zero _)
      (map_one _), Matrix.one_mulVec] at this
  · intro h u
    rw [key]
    exact h _

/-- **The Hermitian defect of a traceless `2 × 2` matrix with a real determinant law.** For
`K₀₀ = r/t`, `K₀₁ = b/t`, `K₁₀ = c/t` with `r` real and `r² + b c = −λ t` (`λ` real):
`|t|² (4 (Re K₀₀)² + |K₀₁ + conj K₁₀|²) = 4 r² + |b + conj c|²`, stated with `t K₀₀ = r` and
`t (K₀₀² + K₀₁ K₁₀) = −λ`. -/
@[tmio T, powerlib_foundation] theorem normSq_mul_hermDefect {t k0 k1 k2 : ℂ} {r l : ℝ}
    (h0 : t * k0 = r) (hrel : t * (k0 ^ 2 + k1 * k2) = -l) :
    Complex.normSq t * (4 * k0.re ^ 2 + Complex.normSq (k1 + (starRingEnd ℂ) k2)) =
      4 * r ^ 2 + Complex.normSq (t * k1 + (starRingEnd ℂ) (t * k2)) := by
  have h0' : (starRingEnd ℂ) t * (starRingEnd ℂ) k0 = r := by
    rw [← map_mul, h0, Complex.conj_ofReal]
  have hrel' : (starRingEnd ℂ) t * ((starRingEnd ℂ) k0 ^ 2 +
      (starRingEnd ℂ) k1 * (starRingEnd ℂ) k2) = -l := by
    have := congrArg (starRingEnd ℂ) hrel
    simpa only [map_mul, map_add, map_pow, map_neg, Complex.conj_ofReal] using this
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_ofNat,
    ← Complex.mul_conj, Complex.re_eq_add_conj, map_add, map_mul, Complex.conj_conj]
  linear_combination (t * k0 + (starRingEnd ℂ) t * (starRingEnd ℂ) k0 + 2 * (r : ℂ)) * h0 +
    (t * k0 + (starRingEnd ℂ) t * (starRingEnd ℂ) k0 + 2 * (r : ℂ)) * h0' +
    ((starRingEnd ℂ) t - t) * hrel + (t - (starRingEnd ℂ) t) * hrel'

end powerlib.PH
