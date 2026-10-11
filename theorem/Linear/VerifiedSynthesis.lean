import theorem.Linear.Certificate
import theorem.Linear.Positive

/-! A complete rational backend for Lyapunov synthesis. The full finite Lyapunov operator is
inverted over ℚ. The result is checked by the equation and verified Schur elimination. This
backend is also the fallback for an untrusted faster proposal; no invariant of the proposal
algorithm is assumed. -/

namespace powerlib.Linear.VerifiedSynthesis
open Matrix LinearSystems
variable {n : ℕ}

/-- Flatten the full Lyapunov operator, without assuming a symmetric solution. -/
def operatorMap (A : Matrix (Fin n) (Fin n) ℚ) :
    (Fin n × Fin n → ℚ) →ₗ[ℚ] (Fin n × Fin n → ℚ) where
  toFun x q :=
    (Aᵀ * Matrix.of (fun i j => x (i, j)) + Matrix.of (fun i j => x (i, j)) * A) q.1 q.2
  map_add' x y := by
    ext q
    simp [Matrix.mul_apply, Finset.sum_add_distrib, mul_add, add_mul]
    ring
  map_smul' c x := by
    ext q
    simp [Matrix.mul_apply, mul_assoc, mul_left_comm, smul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum, mul_add]

def operator (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℚ := LinearMap.toMatrix' (operatorMap A)

/-- A computable field inverse, expressed by cofactors. -/
def inverse (M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℚ) := M.det⁻¹ • M.adjugate

/-- The total rational candidate. Singular operators produce a candidate that the check rejects. -/
def candidate (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  let x := inverse (operator A) *ᵥ (fun q => (-1 : Matrix (Fin n) (Fin n) ℚ) q.1 q.2)
  fun i j => x (i, j)

def solutionCheck (A P : Matrix (Fin n) (Fin n) ℚ) : Bool := decide (Aᵀ * P + P * A = -1)

def check (A P : Matrix (Fin n) (Fin n) ℚ) : Bool :=
  solutionCheck A P && Positive.check n P

noncomputable section
abbrev real (P : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ := Positive.real P

@[powerlib_foundation] theorem inverse_eq (M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℚ) :
    inverse M = M⁻¹ := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rfl

@[powerlib_foundation] theorem real_lyapunov {A P : Matrix (Fin n) (Fin n) ℚ}
    (h : Aᵀ * P + P * A = -1) : (real A)ᵀ * real P + real P * real A = -1 := by
  have h' := congrArg (Rat.castHom ℝ).mapMatrix h
  rw [map_add, map_mul, map_mul, map_neg, map_one] at h'
  simpa [RingHom.mapMatrix_apply, Matrix.transpose_map] using h'

/-- A Hurwitz real image makes the full rational operator injective. Uniqueness in the upstream
Lyapunov theorem is among all matrices, so no symmetry premise is needed. -/
@[powerlib_foundation] theorem operator_injective {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : IsHurwitz (real A)) : Function.Injective (operator A).mulVec := by
  intro x y hxy
  have hzero : operatorMap A (x - y) = 0 := by
    rw [map_sub]
    simpa [operator, LinearMap.toMatrix'_mulVec] using sub_eq_zero.mpr hxy
  let Q : Matrix (Fin n) (Fin n) ℚ := fun i j => (x - y) (i, j)
  have hQ : Aᵀ * Q + Q * A = 0 := by
    ext i j
    change (fun q : Fin n × Fin n => (Aᵀ * Q + Q * A) q.1 q.2) = 0 at hzero
    exact congrFun hzero (i, j)
  have hQR : (real A)ᵀ * real Q + real Q * real A = 0 := by
    have h := congrArg (Rat.castHom ℝ).mapMatrix hQ
    rw [map_add, map_mul, map_mul, map_zero] at h
    simpa [RingHom.mapMatrix_apply, Matrix.transpose_map] using h
  obtain ⟨P, _, hP, hunique⟩ := hA.exists_posDef_unique_solution_continuous_lyapunov 1 PosDef.one
  change P * real A + (real A)ᵀ * P = -1 at hP
  have hplus : SolvesContinuousLyapunovEquation (real A) (P + real Q) 1 := by
    change (P + real Q) * real A + (real A)ᵀ * (P + real Q) = -1
    calc
      _ = (P * real A + (real A)ᵀ * P) + ((real A)ᵀ * real Q + real Q * real A) := by
        noncomm_ring
      _ = -1 := by rw [hP, hQR, add_zero]
  have hQr : real Q = 0 := by
    have hpq := hunique (P + real Q) hplus
    exact add_left_cancel (hpq.trans (add_zero P).symm)
  funext q
  have h := congrFun (congrFun hQr q.1) q.2
  change ((x q - y q : ℚ) : ℝ) = 0 at h
  have hq : x q - y q = 0 := by exact_mod_cast h
  exact sub_eq_zero.mp hq

/-- On a Hurwitz input the computed rational candidate solves the equation. -/
@[powerlib_foundation] theorem candidate_solves {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : IsHurwitz (real A)) : Aᵀ * candidate A + candidate A * A = -1 := by
  have hu : IsUnit (operator A).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp (operator_injective hA))
  have h := congrArg
    (fun M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℚ =>
      M *ᵥ (fun q => (-1 : Matrix (Fin n) (Fin n) ℚ) q.1 q.2))
    (Matrix.mul_nonsing_inv (operator A) hu)
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at h
  rw [← inverse_eq] at h
  rw [operator, LinearMap.toMatrix'_mulVec] at h
  change operatorMap A (fun q => candidate A q.1 q.2) = _ at h
  ext i j
  change (fun q : Fin n × Fin n => (Aᵀ * candidate A + candidate A * A) q.1 q.2) = _ at h
  exact congrFun h (i, j)

/-- Every rational solution for a Hurwitz matrix passes the verified positivity check. -/
@[powerlib_foundation] theorem check_of_solution {A P : Matrix (Fin n) (Fin n) ℚ}
    (hA : IsHurwitz (real A)) (hP : Aᵀ * P + P * A = -1) : check A P = true := by
  obtain ⟨S, hS, _, hunique⟩ := hA.exists_posDef_unique_solution_continuous_lyapunov 1 PosDef.one
  have hR : SolvesContinuousLyapunovEquation (real A) (real P) 1 := by
    change real P * real A + (real A)ᵀ * real P = -1
    rw [add_comm]
    exact real_lyapunov hP
  have hpos : (real P).PosDef := (hunique (real P) hR).symm ▸ hS
  simp only [check, solutionCheck, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hP, (Positive.check_iff n P).mpr hpos⟩

/-- The backend is complete for every finite rational state matrix. -/
@[powerlib_foundation] theorem candidate_checked {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : IsHurwitz (real A)) : check A (candidate A) = true :=
  check_of_solution hA (candidate_solves hA)

/-- The checked finite data constructs the same real certificate used throughout the library. -/
def certificate (A P : Matrix (Fin n) (Fin n) ℚ) (h : check A P = true) : Certificate (real A) := by
  have h' : solutionCheck A P = true ∧ Positive.check n P = true := by
    simpa only [check, Bool.and_eq_true] using h
  have hs : Aᵀ * P + P * A = -1 := by simpa [solutionCheck] using h'.1
  have hp := (Positive.check_iff n P).mp h'.2
  exact ⟨real P,
    by simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hp.isHermitian.eq,
    fun x hx => by simpa using hp.dotProduct_mulVec_pos hx, real_lyapunov hs⟩

@[powerlib_foundation] theorem isHurwitz_of_check {A P : Matrix (Fin n) (Fin n) ℚ}
    (h : check A P = true) : IsHurwitz (real A) := (certificate A P h).isHurwitz

end
end powerlib.Linear.VerifiedSynthesis
