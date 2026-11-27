import theorem.Periodic.RobustThreshold
import theorem.LinearAlgebra.ConjugateGradient

/-! # The Lyapunov form of the robust threshold in matrix-norm terms

`Periodic.Robust.schurStable_of_lyapunov` certifies `ẋ = (A₀ + B(t)) x` with
`A₀ᵀ P + P A₀ = −Q` through four quadratic-form constants: `p₁ |x|² ≤ xᵀ P x ≤ p₂ |x|²`,
`xᵀ Q x ≥ q |x|²` and `xᵀ (P B(t) + B(t)ᵀ P) x ≤ β |x|²` with `β < q`. This module supplies those
constants from spectral data and operator norms, so that the threshold can be read off the
matrices:
* `p₁ = λ_min(P)`, `p₂ = λ_max(P)`, `q = λ_min(Q)` (the smallest and largest eigenvalues of the
  symmetric matrices, `Matrix.IsHermitian.eigenvalues`), by the Rayleigh bounds
  `λ_min |x|² ≤ xᵀ S x ≤ λ_max |x|²` of the spectral theorem;
* `β = sup_t ‖P B(t) + B(t)ᵀ P‖₂` (operator norm of `EuclideanSpace ℝ (Fin n)`), by
  `|xᵀ S x| ≤ ‖S‖₂ |x|²`.
The threshold `sup_t ‖P B(t) + B(t)ᵀ P‖₂ < λ_min(Q)` gives a Schur-stable monodromy matrix for
every period and waveform, with `V(x(t)) ≤ e^{−((λ_min(Q) − β)/λ_max(P))(t − s)} V(x(s))`. Since
`‖Bᵀ‖₂ = ‖B‖₂`, `‖P B + Bᵀ P‖₂ ≤ 2 ‖P‖₂ ‖B‖₂`, and the threshold takes the classical form
`2 ‖P‖₂ sup_t ‖B(t)‖₂ < λ_min(Q)` (Khalil's bound for vanishing perturbations; for `Q = I` it reads
`sup ‖B‖₂ < 1 / (2 ‖P‖₂)`).

Scope.
* `ẋ = (A₀ + B(t)) x` on `ℝⁿ` (`Fin n`), constant real `A₀`, continuous real `T`-periodic `B`,
  `T > 0`; `P` symmetric positive definite and `Q` symmetric with `A₀ᵀ P + P A₀ = −Q`.
* Matrix norms here are the Euclidean operator norms `‖Matrix.toEuclideanCLM A‖` (Mathlib's
  `Matrix.Norms.L2Operator` norm, `Matrix.cstar_norm_def`), not the `L∞` operator norm used
  elsewhere in `theorem/Periodic/`; quadratic forms are `x ⬝ᵥ S x`, `|x|² = x ⬝ᵥ x`.
* Eigenvalues are Mathlib's `Matrix.IsHermitian.eigenvalues`; `λ_min = ⨅ i, eigenvalues i`,
  `λ_max = ⨆ i, eigenvalues i`.
* Generic mathematics; no model family.

Source: Khalil, *Nonlinear Systems*, 3rd ed., §9.1 (vanishing perturbations: `‖g(t, x)‖ ≤ γ ‖x‖`
with `γ < λ_min(Q) / (2 λ_max(P))`); the spectral theorem for symmetric matrices
(`Matrix.IsHermitian.spectral_theorem`, orthogonal diagonalization as in
`LinearAlgebra.anorm2_conj`); LeanForControl `MatrixAlgebra.abs_quadraticForm_le`; the Lyapunov
form `Periodic.Robust.schurStable_of_lyapunov` of `theorem/Periodic/RobustThreshold.lean`.

Results.
* `rayleigh_bounds` — `λ_min(S) |x|² ≤ xᵀ S x ≤ λ_max(S) |x|²` for symmetric `S`;
  `eigenvalues_iInf_pos` — `λ_min(P) > 0` for `P ≻ 0` (`n > 0`).
* `abs_quadratic_le_opNorm` — `|xᵀ S x| ≤ ‖S‖₂ |x|²`.
* `opNorm_lyapunovPerturbation_le` — `‖P B + Bᵀ P‖₂ ≤ 2 ‖P‖₂ ‖B‖₂`.
* `schurStable_of_opNorm_lt` — `sup_t ‖P B(t) + B(t)ᵀ P‖₂ ≤ β < λ_min(Q)`: Schur-stable monodromy
  for every period and waveform, and the decay of `V = xᵀ P x` at the rate
  `(λ_min(Q) − β) / λ_max(P)`.
* `schurStable_of_two_mul_opNorm_lt` — the classical form `2 ‖P‖₂ sup_t ‖B(t)‖₂ < λ_min(Q)`.
-/

noncomputable section
namespace powerlib.Periodic.Robust

open Set Matrix Function

variable {n : ℕ}

/-! ## Rayleigh bounds and operator norms -/

section Rayleigh

/-- **Rayleigh bounds.** For a symmetric real matrix `S` with eigenvalues `λᵢ`,
`(min λᵢ) |x|² ≤ xᵀ S x ≤ (max λᵢ) |x|²`: with the orthogonal diagonalization
`S = U diag(λ) Uᵀ` (`Matrix.IsHermitian.spectral_theorem`) and `y = Uᵀ x`,
`xᵀ S x = Σ λᵢ yᵢ²` and `|x|² = Σ yᵢ²` (`LinearAlgebra.anorm2_conj`). -/
@[tmio T, powerlib_foundation] theorem rayleigh_bounds {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.IsHermitian) (x : Fin n → ℝ) :
    (⨅ i, hS.eigenvalues i) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (S *ᵥ x) ∧
      x ⬝ᵥ (S *ᵥ x) ≤ (⨆ i, hS.eigenvalues i) * (x ⬝ᵥ x) := by
  set U : Matrix (Fin n) (Fin n) ℝ := (hS.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  set lam := hS.eigenvalues
  have hstar : star U = Uᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hUU : Uᵀ * U = 1 := by
    rw [← hstar]; exact Unitary.coe_star_mul_self hS.eigenvectorUnitary
  have hUU' : U * Uᵀ = 1 := mul_eq_one_comm.mp hUU
  have hdec : S = U * diagonal lam * Uᵀ := by
    conv_lhs => rw [hS.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    change U * _ * star U = _
    rw [hstar]
    congr 2
  have hone : (1 : Matrix (Fin n) (Fin n) ℝ) = U * 1 * Uᵀ := by rw [Matrix.mul_one, hUU']
  set y := Uᵀ *ᵥ x
  have hx : x = U *ᵥ y := by rw [mulVec_mulVec, hUU', one_mulVec]
  have hS' : x ⬝ᵥ (S *ᵥ x) = ∑ i, lam i * y i ^ 2 := by
    have h := LinearAlgebra.anorm2_conj hUU hdec y
    rw [← hx] at h
    rw [show x ⬝ᵥ (S *ᵥ x) = LinearAlgebra.anorm2 S x from rfl, h]
    simp only [dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h1 : x ⬝ᵥ x = ∑ i, y i ^ 2 := by
    have h := LinearAlgebra.anorm2_conj hUU hone y
    rw [← hx] at h
    rw [show x ⬝ᵥ x = LinearAlgebra.anorm2 1 x by simp [LinearAlgebra.anorm2], h]
    simp only [one_mulVec, dotProduct]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hbdd : BddBelow (range lam) := (Set.finite_range lam).bddBelow
  have hbdd' : BddAbove (range lam) := (Set.finite_range lam).bddAbove
  rw [hS', h1, Finset.mul_sum, Finset.mul_sum]
  constructor
  · exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (ciInf_le hbdd i) (sq_nonneg _)
  · exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (le_ciSup hbdd' i) (sq_nonneg _)

/-- The smallest eigenvalue of a positive definite matrix is positive (`n > 0`). -/
@[tmio T, powerlib_foundation] theorem eigenvalues_iInf_pos [NeZero n]
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosDef) : 0 < ⨅ i, hP.1.eigenvalues i := by
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := hP.1.eigenvalues)
  rw [← hi]
  exact hP.eigenvalues_pos i

/-- `|xᵀ S x| ≤ ‖S‖₂ |x|²` for the Euclidean operator norm (LeanForControl
`MatrixAlgebra.abs_quadraticForm_le`). -/
@[tmio T, powerlib_foundation] theorem abs_quadratic_le_opNorm (S : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    |x ⬝ᵥ (S *ᵥ x)| ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) S‖ * (x ⬝ᵥ x) := by
  have h := MatrixAlgebra.abs_quadraticForm_le S (WithLp.toLp 2 x)
  rw [MatrixAlgebra.quadraticForm, Matrix.inner_toEuclideanCLM, EuclideanSpace.norm_sq_eq] at h
  convert h using 2
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs, sq]

open scoped Matrix.Norms.L2Operator in
/-- `‖P B + Bᵀ P‖₂ ≤ 2 ‖P‖₂ ‖B‖₂` (submultiplicativity and `‖Bᵀ‖₂ = ‖B‖₂`,
`Matrix.l2_opNorm_conjTranspose`). -/
@[tmio T, powerlib_foundation] theorem opNorm_lyapunovPerturbation_le
    (P B : Matrix (Fin n) (Fin n) ℝ) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (P * B + Bᵀ * P)‖ ≤
      2 * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P‖ *
        ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B‖ := by
  have hT : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Bᵀ‖ =
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B‖ := by
    have h := Matrix.l2_opNorm_conjTranspose (𝕜 := ℝ) B
    rw [conjTranspose_eq_transpose_of_trivial, Matrix.cstar_norm_def, Matrix.cstar_norm_def] at h
    exact h
  rw [map_add, map_mul, map_mul]
  calc _ ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P *
          Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B‖ +
        ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Bᵀ *
          Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P‖ := norm_add_le _ _
    _ ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P‖ *
          ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B‖ +
        ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Bᵀ‖ *
          ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by rw [hT]; ring

end Rayleigh

/-! ## The threshold in norm form -/

section Threshold

variable {A₀ P Q : Matrix (Fin n) (Fin n) ℝ} {β T : ℝ}

/-- **Lyapunov threshold in matrix-norm form.** Let `P ≻ 0` and `Q = Qᵀ` solve
`A₀ᵀ P + P A₀ = −Q`, and let the continuous `T`-periodic modulation satisfy
`‖P B(t) + B(t)ᵀ P‖₂ ≤ β < λ_min(Q)`. Then the monodromy matrix of `ẋ = (A₀ + B(t)) x` is Schur
stable — for every period and waveform — and every solution satisfies
`V(x(t)) ≤ e^{−((λ_min(Q) − β)/λ_max(P))(t − s)} V(x(s))`, `V = xᵀ P x`. The quadratic-form
hypotheses of `schurStable_of_lyapunov` hold with `p₁ = λ_min(P)`, `p₂ = λ_max(P)`,
`q = λ_min(Q)` (`rayleigh_bounds`) and `β` (`abs_quadratic_le_opNorm`). -/
@[tmio T, powerlib_foundation] theorem schurStable_of_opNorm_lt (hP : P.PosDef)
    (hQ : Q.IsHermitian) (hlyap : A₀ᵀ * P + P * A₀ = -Q) (hT : 0 < T)
    {B : ℝ → Matrix (Fin n) (Fin n) ℝ} (hB : Continuous B) (hBP : Periodic B T)
    (hβ : ∀ t, ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (P * B t + (B t)ᵀ * P)‖ ≤ β)
    (hβq : β < ⨅ i, hQ.eigenvalues i) :
    LTI.SchurStable (monodromy (fun t => A₀ + B t) T 0) ∧
      ∀ x : ℝ → Fin n → ℝ, (∀ t, HasDerivAt x ((A₀ + B t) *ᵥ x t) t) → ∀ s t, s ≤ t →
        x t ⬝ᵥ (P *ᵥ x t) ≤ Real.exp (-(((⨅ i, hQ.eigenvalues i) - β) /
          (⨆ i, hP.1.eigenvalues i) * (t - s))) * (x s ⬝ᵥ (P *ᵥ x s)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun μ v hv _ => absurd (Subsingleton.elim v 0) hv, fun x _ s t _ => ?_⟩
    simp [dotProduct]
  have : NeZero n := ⟨hn.ne'⟩
  have hPs : Pᵀ = P := by
    have h := hP.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hp₁ := eigenvalues_iInf_pos hP
  have hp₂ : 0 < ⨆ i, hP.1.eigenvalues i := by
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := hP.1.eigenvalues)
    have hle : hP.1.eigenvalues i ≤ ⨆ j, hP.1.eigenvalues j :=
      le_ciSup (Set.finite_range _).bddAbove i
    linarith
  refine schurStable_of_lyapunov hPs hlyap hp₁ hp₂ (fun x => (rayleigh_bounds hP.1 x).1)
    (fun x => (rayleigh_bounds hP.1 x).2) (fun x => (rayleigh_bounds hQ x).1) hβq hT hB hBP
    fun t x => ?_
  have hxx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  exact (le_abs_self _).trans ((abs_quadratic_le_opNorm _ x).trans
    (mul_le_mul_of_nonneg_right (hβ t) hxx))

/-- **The classical norm threshold** `2 ‖P‖₂ sup_t ‖B(t)‖₂ < λ_min(Q)`. If
`‖B(t)‖₂ ≤ b` and `2 ‖P‖₂ b < λ_min(Q)`, the monodromy matrix is Schur stable for every period
and waveform, with the decay rate `(λ_min(Q) − 2‖P‖₂ b) / λ_max(P)` of `V = xᵀ P x`
(`opNorm_lyapunovPerturbation_le`, `schurStable_of_opNorm_lt`). -/
@[tmio T, powerlib_foundation] theorem schurStable_of_two_mul_opNorm_lt (hP : P.PosDef)
    (hQ : Q.IsHermitian) (hlyap : A₀ᵀ * P + P * A₀ = -Q) (hT : 0 < T)
    {B : ℝ → Matrix (Fin n) (Fin n) ℝ} (hB : Continuous B) (hBP : Periodic B T) {b : ℝ}
    (hb : ∀ t, ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (B t)‖ ≤ b)
    (hbq : 2 * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P‖ * b < ⨅ i, hQ.eigenvalues i) :
    LTI.SchurStable (monodromy (fun t => A₀ + B t) T 0) ∧
      ∀ x : ℝ → Fin n → ℝ, (∀ t, HasDerivAt x ((A₀ + B t) *ᵥ x t) t) → ∀ s t, s ≤ t →
        x t ⬝ᵥ (P *ᵥ x t) ≤ Real.exp (-(((⨅ i, hQ.eigenvalues i) -
          2 * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P‖ * b) /
          (⨆ i, hP.1.eigenvalues i) * (t - s))) * (x s ⬝ᵥ (P *ᵥ x s)) :=
  schurStable_of_opNorm_lt hP hQ hlyap hT hB hBP (fun t =>
    (opNorm_lyapunovPerturbation_le P (B t)).trans (mul_le_mul_of_nonneg_left (hb t)
      (by positivity))) hbq

end Threshold

end powerlib.Periodic.Robust
