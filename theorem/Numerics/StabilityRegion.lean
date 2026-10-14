import theorem.Attributes
import dependencies.Mathlib
import Mathlib.Analysis.Matrix.Normed

/-! # "Numerically stable ⇔ every `hλᵢ` lies in the stability region": the correct version

Bounded trajectories of a linear recursion force every eigenvalue into the closed unit disk;
the converse holds for diagonalizable matrices and fails for a Jordan block.

Model boundary.
* Complex linear recursions `x_{k+1} = Φ x_k` on `Fin n → ℂ` (a real system is the special case
  of real entries), with boundedness of every trajectory as the stability notion: "bounded
  trajectories" means `∀ x₀, ∃ C, ∀ k, ‖Φ^k x₀‖ ≤ C` (every trajectory `x_k = Φ^k x₀` of the
  recursion is bounded), written out in each statement. The stability region is the closed set
  `‖R(z)‖ ≤ 1`.

Source: work-sync theory/T-numerical-integration.md §1.7 ("数值解不爆炸 ⇔ hλ ∈ S") and §2.7
("数值稳定 ⇔ ρ(R(hA)) ≤ 1 ⇔ hλᵢ ∈ S").

Results.
* `norm_le_one_of_boundedTrajectories` — bounded trajectories ⇒ every eigenvalue of `Φ` has
  modulus `≤ 1` (the "⇒" direction holds for every matrix).
* `boundedTrajectories_iff_of_diagonalizable` — if `Φ = P diag(d) P⁻¹`, bounded trajectories ⇔
  `‖dᵢ‖ ≤ 1` for all `i`.
* `forwardEuler_boundedTrajectories_iff` — for a diagonalizable `A = P diag(λ) P⁻¹`, the forward
  Euler recursion `1 + hA` has bounded trajectories ⇔ `‖1 + hλᵢ‖ ≤ 1` for all `i` (i.e. every
  `hλᵢ` in the forward-Euler region).
* `jordan_counterexample` — without diagonalizability the "⇐" direction fails: for the Jordan
  block `A = [[0,1],[0,0]]` the only eigenvalue gives `R(hλ) = R(0) = 1` (on the boundary of the
  region), yet the forward-Euler trajectory from `(0, 1)` is `(kh, 1)`, unbounded.

Corrections.
* The note states the equivalence without conditions. "⇒" is true; "⇐" needs the eigenvalues
  with `‖R(hλᵢ)‖ = 1` to be semisimple; the formalized version assumes diagonalizability, and
  `jordan_counterexample` refutes the unconditional statement. The strict version (`‖R‖ < 1`
  for every eigenvalue ⇔ geometric decay) needs no such assumption; see
  `powerlib.LTI.exponentiallyStable_iff_schurStable`.
-/

noncomputable section
namespace powerlib.Numerics
open Matrix Filter
open scoped Matrix.Norms.Operator

variable {n : ℕ}

@[powerlib_foundation] theorem pow_mulVec_eigen {Φ : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ}
    {v : Fin n → ℂ} (heig : Φ *ᵥ v = μ • v) (k : ℕ) : (Φ ^ k) *ᵥ v = μ ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul, ih, smul_smul, ← pow_succ']

/-- Bounded trajectories (every trajectory `Φ^k x₀` of `x_{k+1} = Φ x_k` is bounded) force
every eigenvalue into the closed unit disk. -/
@[powerlib_foundation] theorem norm_le_one_of_boundedTrajectories
    {Φ : Matrix (Fin n) (Fin n) ℂ} (hB : ∀ x₀ : Fin n → ℂ, ∃ C : ℝ, ∀ k : ℕ, ‖(Φ ^ k) *ᵥ x₀‖ ≤ C)
    {μ : ℂ} {v : Fin n → ℂ} (hv : v ≠ 0) (heig : Φ *ᵥ v = μ • v) : ‖μ‖ ≤ 1 := by
  by_contra hμ
  push Not at hμ
  obtain ⟨C, hC⟩ := hB v
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hlim : Tendsto (fun k : ℕ => ‖μ‖ ^ k * ‖v‖) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hμ).atTop_mul_const hvpos
  obtain ⟨k, hk⟩ := (hlim.eventually_gt_atTop C).exists
  have := hC k
  rw [pow_mulVec_eigen heig, norm_smul, norm_pow] at this
  linarith

@[powerlib_foundation] private lemma conj_pow {P Pinv : Matrix (Fin n) (Fin n) ℂ}
    (hP : P * Pinv = 1) (hP' : Pinv * P = 1) (D : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    (P * D * Pinv) ^ k = P * D ^ k * Pinv := by
  induction k with
  | zero => simp only [pow_zero, Matrix.mul_one, hP]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    calc P * D ^ k * Pinv * (P * D * Pinv) = P * D ^ k * (Pinv * P) * D * Pinv := by
          simp only [Matrix.mul_assoc]
      _ = P * (D ^ k * D) * Pinv := by rw [hP', Matrix.mul_one]; simp only [Matrix.mul_assoc]

/-- Diagonalizable recursion: bounded trajectories (every `Φ^k x₀` bounded, for
`Φ = P diag(d) P⁻¹`) ⇔ all eigenvalues in the closed unit disk. -/
@[powerlib_foundation] theorem boundedTrajectories_iff_of_diagonalizable
    {P Pinv : Matrix (Fin n) (Fin n) ℂ} (hP : P * Pinv = 1) (hP' : Pinv * P = 1)
    (d : Fin n → ℂ) :
    (∀ x₀ : Fin n → ℂ, ∃ C : ℝ, ∀ k : ℕ, ‖((P * diagonal d * Pinv) ^ k) *ᵥ x₀‖ ≤ C) ↔
      ∀ i, ‖d i‖ ≤ 1 := by
  constructor
  · intro hB i
    have hv : P *ᵥ Pi.single i 1 ≠ 0 := by
      intro h0
      have := congrArg (Pinv *ᵥ ·) h0
      simp only [Matrix.mulVec_mulVec, hP', Matrix.one_mulVec, Matrix.mulVec_zero] at this
      have h1 := congrFun this i
      simp at h1
    refine norm_le_one_of_boundedTrajectories hB hv ?_
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hP', Matrix.mul_one, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_single, ← Matrix.mulVec_smul]
    congr 1
    ext j
    by_cases hij : j = i
    · subst hij; simp
    · simp [hij]
  · intro hd x₀
    refine ⟨‖P‖ * ‖Pinv‖ * ‖x₀‖, fun k => ?_⟩
    rw [conj_pow hP hP', diagonal_pow]
    have hdk : ‖diagonal (d ^ k)‖ ≤ 1 := by
      rw [linfty_opNorm_diagonal]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
      rw [Pi.pow_apply, norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hd i)
    calc ‖(P * diagonal (d ^ k) * Pinv) *ᵥ x₀‖
        ≤ ‖P * diagonal (d ^ k) * Pinv‖ * ‖x₀‖ := linfty_opNorm_mulVec _ _
      _ ≤ ‖P‖ * ‖diagonal (d ^ k)‖ * ‖Pinv‖ * ‖x₀‖ := by
          gcongr
          exact (linfty_opNorm_mul _ _).trans
            (mul_le_mul_of_nonneg_right (linfty_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ ‖P‖ * 1 * ‖Pinv‖ * ‖x₀‖ := by gcongr
      _ = ‖P‖ * ‖Pinv‖ * ‖x₀‖ := by ring

/-- Forward Euler on a diagonalizable linear system: bounded numerical trajectories (every
`(1 + hA)^k x₀` bounded) exactly when every `hλᵢ` lies in the forward-Euler region
`‖1 + z‖ ≤ 1`. -/
@[powerlib_foundation] theorem forwardEuler_boundedTrajectories_iff
    {P Pinv : Matrix (Fin n) (Fin n) ℂ} (hP : P * Pinv = 1) (hP' : Pinv * P = 1)
    (lam : Fin n → ℂ) (h : ℂ) :
    (∀ x₀ : Fin n → ℂ, ∃ C : ℝ, ∀ k : ℕ,
        ‖((1 + h • (P * diagonal lam * Pinv)) ^ k) *ᵥ x₀‖ ≤ C) ↔
      ∀ i, ‖1 + h * lam i‖ ≤ 1 := by
  have hconj : 1 + h • (P * diagonal lam * Pinv) = P * diagonal (fun i => 1 + h * lam i) * Pinv := by
    have : diagonal (fun i => 1 + h * lam i) = 1 + h • diagonal lam := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [this, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hP, Matrix.mul_smul,
      Matrix.smul_mul]
  rw [hconj]
  exact boundedTrajectories_iff_of_diagonalizable hP hP' _

/-- The unconditional "⇐" fails: a Jordan block whose eigenvalue maps to the boundary point
`R(0) = 1` of the forward-Euler region has unbounded forward-Euler trajectories (not every
`(1 + hA)^k x₀` is bounded). -/
@[powerlib_foundation] theorem jordan_counterexample {h : ℝ} (hh : 0 < h) :
    (∀ (μ : ℂ) (v : Fin 2 → ℂ), v ≠ 0 → !![0, 1; 0, 0] *ᵥ v = μ • v →
        ‖1 + (h : ℂ) * μ‖ ≤ 1) ∧
      ¬ ∀ x₀ : Fin 2 → ℂ, ∃ C : ℝ, ∀ k : ℕ,
        ‖((1 + (h : ℂ) • !![(0 : ℂ), 1; 0, 0]) ^ k) *ᵥ x₀‖ ≤ C := by
  constructor
  · intro μ v hv heig
    have h0 := congrFun heig 0
    have h1 := congrFun heig 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    have hμ : μ = 0 := by
      by_contra hμ
      have hv1 : v 1 = 0 := by simpa [hμ] using h1
      have hv0 : v 0 = 0 := by
        rw [hv1] at h0
        simpa [hμ, eq_comm] using h0
      exact hv (by ext i; fin_cases i <;> simp [hv0, hv1])
    simp [hμ]
  · intro hB
    obtain ⟨C, hC⟩ := hB ![0, 1]
    have hpow : ∀ k : ℕ, (1 + (h : ℂ) • !![(0 : ℂ), 1; 0, 0]) ^ k = !![1, (k : ℂ) * h; 0, 1] := by
      intro k
      induction k with
      | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
      | succ k ih =>
        rw [pow_succ, ih]
        ext i j; fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_two]; try ring)
    obtain ⟨k, hk⟩ := exists_nat_gt (C / h)
    have := hC k
    rw [hpow k] at this
    have hcomp : ‖(!![1, (k : ℂ) * h; 0, 1] *ᵥ ![0, 1]) 0‖ ≤ C :=
      (norm_le_pi_norm _ 0).trans this
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hcomp
    rw [abs_of_pos hh] at hcomp
    have : C < k * h := by rwa [div_lt_iff₀ hh] at hk
    linarith

end powerlib.Numerics
