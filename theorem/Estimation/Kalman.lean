import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.Matrix.Order

/-! # Kalman measurement update: Joseph form, optimal gain, information form

Matrix identities and Loewner inequalities for one Kalman measurement update: the Joseph form,
optimality of the Kalman gain, and the information form.

Scope.
* Linear algebra, not an engineering result. One measurement update with real matrices: prior
  covariance `P : n × n`, observation matrix `H : p × n`, noise covariance `R : p × p`, gain
  `K : n × p`.
* That `P⁺` is the conditional covariance of a linear-Gaussian model is proved in
  `theorem/Estimation/KalmanGaussian.lean` (scalar, `kalman_condExp_eq`, `kalman_condVar_eq`)
  and `theorem/Estimation/KalmanGaussianVector.lean` (vector).

Source: work-sync theory/T-kalman-filter.md §1.1 (measurement update `S = H P Hᵀ + R`,
`K = P Hᵀ S⁻¹`, `P⁺ = (I − K H) P`, Joseph form `(I − KH) P (I − KH)ᵀ + K R Kᵀ`, "symmetric PSD
by construction"), §1.3 (Joseph form equals the short form at the exact gain), §1.8 (information
form `Ω⁺ = Ω⁻ + Σⱼ Hⱼᵀ Rⱼ⁻¹ Hⱼ` for independent sensors).

Results.
* `joseph_posSemidef` — for **any** gain `K`, `P ⪰ 0`, `R ⪰ 0` ⇒ Joseph form `⪰ 0`.
* `joseph_eq_short` — if `K S = P Hᵀ` (exact gain), the Joseph form equals `(I − K H) P`.
* `joseph_eq_optimal_add` — for symmetric `P, R`, `J(K) = J(K*) + (K − K*) S (K − K*)ᵀ`; hence
  `joseph_optimal_le`: the Kalman gain minimizes the posterior covariance in the Loewner order.
* `information_form` — `(P⁻¹ + Hᵀ R⁻¹ H)⁻¹ = (I − K H) P` (Woodbury, Mathlib
  `Matrix.add_mul_mul_inv_eq_sub`), and `gain_information_form`: `K = P⁺ Hᵀ R⁻¹`.
* `information_add_two_sensors` — stacked independent sensors add their information.
-/

noncomputable section
namespace powerlib.Estimation

open Matrix
open scoped MatrixOrder

variable {n p : ℕ}

/-- Joseph-form posterior covariance `(I − K H) P (I − K H)ᵀ + K R Kᵀ`. -/
def joseph (P : Matrix (Fin n) (Fin n) ℝ) (H : Matrix (Fin p) (Fin n) ℝ)
    (R : Matrix (Fin p) (Fin p) ℝ) (K : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 - K * H) * P * (1 - K * H)ᵀ + K * R * Kᵀ

/-- Innovation covariance `S = H P Hᵀ + R`. -/
def innov (P : Matrix (Fin n) (Fin n) ℝ) (H : Matrix (Fin p) (Fin n) ℝ)
    (R : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ := H * P * Hᵀ + R

@[tmio T, powerlib_foundation] private lemma psd_congr {m k : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) (B : Matrix (Fin k) (Fin m) ℝ) : (B * A * Bᵀ).PosSemidef := by
  simpa [conjTranspose_eq_transpose_of_trivial] using hA.mul_mul_conjTranspose_same B

/-- **The Joseph form is PSD for every gain** (§1.1). -/
@[tmio T, powerlib_foundation] theorem joseph_posSemidef {P : Matrix (Fin n) (Fin n) ℝ}
    {R : Matrix (Fin p) (Fin p) ℝ} (hP : P.PosSemidef) (hR : R.PosSemidef)
    (H : Matrix (Fin p) (Fin n) ℝ) (K : Matrix (Fin n) (Fin p) ℝ) :
    (joseph P H R K).PosSemidef :=
  (psd_congr hP _).add (psd_congr hR K)

/-- Expanded Joseph form `P − K H P − P Hᵀ Kᵀ + K S Kᵀ`. -/
@[tmio T, powerlib_foundation] theorem joseph_expand (P : Matrix (Fin n) (Fin n) ℝ)
    (H : Matrix (Fin p) (Fin n) ℝ) (R : Matrix (Fin p) (Fin p) ℝ) (K : Matrix (Fin n) (Fin p) ℝ) :
    joseph P H R K = P - K * H * P - P * Hᵀ * Kᵀ + K * innov P H R * Kᵀ := by
  simp only [joseph, innov, transpose_sub, transpose_one, transpose_mul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc]
  abel

/-- **At the exact gain `K S = P Hᵀ` the Joseph form equals `(I − K H) P`** (§1.3). -/
@[tmio T, powerlib_foundation] theorem joseph_eq_short {P : Matrix (Fin n) (Fin n) ℝ}
    {H : Matrix (Fin p) (Fin n) ℝ} {R : Matrix (Fin p) (Fin p) ℝ} {K : Matrix (Fin n) (Fin p) ℝ}
    (hK : K * innov P H R = P * Hᵀ) : joseph P H R K = (1 - K * H) * P := by
  rw [joseph_expand, hK]
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  abel

/-- The exact gain `K* = P Hᵀ S⁻¹` satisfies `K* S = P Hᵀ` when `S` is invertible. -/
@[tmio T, powerlib_foundation] theorem kalmanGain_mul_innov {P : Matrix (Fin n) (Fin n) ℝ}
    {H : Matrix (Fin p) (Fin n) ℝ} {R : Matrix (Fin p) (Fin p) ℝ}
    (hS : IsUnit (innov P H R).det) :
    P * Hᵀ * (innov P H R)⁻¹ * innov P H R = P * Hᵀ := by
  rw [Matrix.mul_assoc, nonsing_inv_mul _ hS, Matrix.mul_one]

/-- **Completion of squares**: for symmetric `P`, `R` and the exact gain `K*`,
`J(K) = J(K*) + (K − K*) S (K − K*)ᵀ`. -/
@[tmio T, powerlib_foundation] theorem joseph_eq_optimal_add {P : Matrix (Fin n) (Fin n) ℝ}
    {H : Matrix (Fin p) (Fin n) ℝ} {R : Matrix (Fin p) (Fin p) ℝ}
    (hPs : Pᵀ = P) (hRs : Rᵀ = R) {Ks : Matrix (Fin n) (Fin p) ℝ}
    (hK : Ks * innov P H R = P * Hᵀ) (K : Matrix (Fin n) (Fin p) ℝ) :
    joseph P H R K = joseph P H R Ks + (K - Ks) * innov P H R * (K - Ks)ᵀ := by
  have hSs : (innov P H R)ᵀ = innov P H R := by
    simp [innov, transpose_add, transpose_mul, hPs, hRs, Matrix.mul_assoc]
  -- `K S Ks ᵀ = K H P` and `Ks S Ks ᵀ = Ks H P`
  have h1 : K * innov P H R * Ksᵀ = K * H * P := by
    have : innov P H R * Ksᵀ = H * P := by
      have := congrArg transpose hK
      rw [transpose_mul, transpose_mul, hSs, hPs, transpose_transpose] at this
      exact this
    rw [Matrix.mul_assoc, this, ← Matrix.mul_assoc]
  have h2 : Ks * innov P H R * Ksᵀ = Ks * H * P := by
    have : innov P H R * Ksᵀ = H * P := by
      have := congrArg transpose hK
      rw [transpose_mul, transpose_mul, hSs, hPs, transpose_transpose] at this
      exact this
    rw [Matrix.mul_assoc, this, ← Matrix.mul_assoc]
  rw [joseph_expand, joseph_expand, hK]
  simp only [transpose_sub, Matrix.sub_mul, Matrix.mul_sub]
  rw [h1, h2, hK]
  simp only [Matrix.mul_assoc]
  abel

/-- **The Kalman gain is Loewner-optimal**: `J(K*) ⪯ J(K)` for every gain `K` (when `S ⪰ 0`). -/
@[tmio T, powerlib_foundation] theorem joseph_optimal_le {P : Matrix (Fin n) (Fin n) ℝ}
    {H : Matrix (Fin p) (Fin n) ℝ} {R : Matrix (Fin p) (Fin p) ℝ}
    (hPs : Pᵀ = P) (hRs : Rᵀ = R) (hS : (innov P H R).PosSemidef) {Ks : Matrix (Fin n) (Fin p) ℝ}
    (hK : Ks * innov P H R = P * Hᵀ) (K : Matrix (Fin n) (Fin p) ℝ) :
    joseph P H R Ks ≤ joseph P H R K := by
  rw [Matrix.le_iff, joseph_eq_optimal_add hPs hRs hK K, add_sub_cancel_left]
  exact psd_congr hS _

/-! ## Information form -/

/-- **Information form (§1.8, Woodbury)**: for invertible `P`, `R` and `S = H P Hᵀ + R`,
`(P⁻¹ + Hᵀ R⁻¹ H)⁻¹ = P − P Hᵀ S⁻¹ H P = (I − K H) P` with `K = P Hᵀ S⁻¹`. -/
@[tmio T, powerlib_foundation] theorem information_form {P : Matrix (Fin n) (Fin n) ℝ}
    {H : Matrix (Fin p) (Fin n) ℝ} {R : Matrix (Fin p) (Fin p) ℝ}
    (hP : IsUnit P) (hR : IsUnit R) (hS : IsUnit (innov P H R)) :
    (P⁻¹ + Hᵀ * R⁻¹ * H)⁻¹ = (1 - P * Hᵀ * (innov P H R)⁻¹ * H) * P := by
  have hPi : IsUnit P⁻¹ := (isUnit_nonsing_inv_iff).mpr hP
  have hRi : IsUnit R⁻¹ := (isUnit_nonsing_inv_iff).mpr hR
  have hP' : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hP
  have hR' : IsUnit R.det := (isUnit_iff_isUnit_det R).mp hR
  have hAC : IsUnit (R⁻¹⁻¹ + H * P⁻¹⁻¹ * Hᵀ) := by
    rw [nonsing_inv_nonsing_inv _ hP', nonsing_inv_nonsing_inv _ hR', add_comm]
    exact hS
  rw [add_mul_mul_inv_eq_sub P⁻¹ Hᵀ R⁻¹ H hPi hRi hAC,
    nonsing_inv_nonsing_inv _ hP', nonsing_inv_nonsing_inv _ hR',
    show R + H * P * Hᵀ = innov P H R by rw [innov, add_comm]]
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]

/-- The gain in information form: `K = P⁺ Hᵀ R⁻¹` with `P⁺ = (P⁻¹ + Hᵀ R⁻¹ H)⁻¹`. -/
@[tmio T, powerlib_foundation] theorem gain_information_form {P : Matrix (Fin n) (Fin n) ℝ}
    {H : Matrix (Fin p) (Fin n) ℝ} {R : Matrix (Fin p) (Fin p) ℝ}
    (hP : IsUnit P) (hR : IsUnit R) (hS : IsUnit (innov P H R)) :
    (P⁻¹ + Hᵀ * R⁻¹ * H)⁻¹ * Hᵀ * R⁻¹ = P * Hᵀ * (innov P H R)⁻¹ := by
  rw [information_form hP hR hS]
  have hR' : IsUnit R.det := (isUnit_iff_isUnit_det R).mp hR
  have hS' : IsUnit (innov P H R).det := (isUnit_iff_isUnit_det _).mp hS
  set S := innov P H R with hSdef
  have hRS : R = S - H * P * Hᵀ := by rw [hSdef, innov]; abel
  have e : P * Hᵀ * S⁻¹ * R = P * Hᵀ - P * Hᵀ * S⁻¹ * H * P * Hᵀ := by
    rw [hRS, Matrix.mul_sub, Matrix.mul_assoc (P * Hᵀ) S⁻¹ S, nonsing_inv_mul _ hS',
      Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  have lhs : (1 - P * Hᵀ * S⁻¹ * H) * P * Hᵀ * R⁻¹ =
      (P * Hᵀ - P * Hᵀ * S⁻¹ * H * P * Hᵀ) * R⁻¹ := by
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  rw [lhs, ← e, Matrix.mul_assoc, mul_nonsing_inv _ hR', Matrix.mul_one]

/-- **Independent sensors add information**: stacking `H = [H₁; H₂]`, `R = blockdiag(R₁, R₂)`
gives `Hᵀ R⁻¹ H = H₁ᵀ R₁⁻¹ H₁ + H₂ᵀ R₂⁻¹ H₂`. -/
@[tmio T, powerlib_foundation] theorem information_add_two_sensors {p₁ p₂ : ℕ}
    (H₁ : Matrix (Fin p₁) (Fin n) ℝ) (H₂ : Matrix (Fin p₂) (Fin n) ℝ)
    {R₁ : Matrix (Fin p₁) (Fin p₁) ℝ} {R₂ : Matrix (Fin p₂) (Fin p₂) ℝ}
    (h₁ : IsUnit R₁.det) (h₂ : IsUnit R₂.det) :
    (fromRows H₁ H₂)ᵀ * (fromBlocks R₁ 0 0 R₂)⁻¹ * fromRows H₁ H₂ =
      H₁ᵀ * R₁⁻¹ * H₁ + H₂ᵀ * R₂⁻¹ * H₂ := by
  have hinv : (fromBlocks R₁ 0 0 R₂)⁻¹ = fromBlocks R₁⁻¹ 0 0 R₂⁻¹ := by
    apply inv_eq_left_inv
    rw [fromBlocks_multiply]
    simp [nonsing_inv_mul _ h₁, nonsing_inv_mul _ h₂, fromBlocks_one]
  rw [hinv, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  simp

end powerlib.Estimation
