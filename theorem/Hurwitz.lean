import theorem.LTI
import theorem.Lyapunov
import theorem.StateSpacePassivity
import theorem.Dynamics.LyapunovDefs

noncomputable section
namespace powerlib.LTI
open Matrix Filter
open scoped Topology

variable {n : ℕ} {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

@[powerlib_foundation] theorem spectrallyStable_iff_isHurwitz (A : Matrix (Fin n) (Fin n) ℝ) :
    SpectrallyStable A ↔ LinearSystems.IsHurwitz A := by
  constructor
  · intro h μ v hv heigen
    simpa only [neg_zero] using (show μ.re < 0 by
      apply h μ
      apply Matrix.exists_mulVec_eq_zero_iff.mp
      refine ⟨v, hv, ?_⟩
      rw [characteristicMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, heigen]
      exact sub_self _)
  · intro h μ hdet
    obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    simpa only [neg_zero] using (show μ.re < -0 by
      apply h μ v hv
      rw [characteristicMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hzero
      exact (sub_eq_zero.mp hzero).symm)

@[powerlib_domain] theorem accepted_nonempty_of_isHurwitz {m : AutonomousModel n}
    (h : LinearSystems.IsHurwitz m.A) : Nonempty (Accepted m) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨⟨1, 1, 1, one_pos, one_pos, Matrix.transpose_one,
      fun x => (by simp [sqNorm, energy]), fun x => (by simp [sqNorm, energy]),
      Subsingleton.elim _ _⟩⟩
  obtain ⟨P, hP, hlyap, -⟩ :=
    h.exists_posDef_unique_solution_continuous_lyapunov 1 Matrix.PosDef.one
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  obtain ⟨α, hα, β, hβα, hb⟩ := powerlib.quadratic_bounds
    (fun y => StateSpacePassivity.energy P (e y))
    ((StateSpacePassivity.energy_continuous P).comp e.continuous)
    (fun a y => by simpa only [map_smul] using StateSpacePassivity.energy_smul P a (e y))
    (fun y hy => StateSpacePassivity.energy_positive hP _
      fun h0 => hy (e.injective (by simpa using h0)))
  have hbound (x : State n) :
      2 * α * sqNorm x ≤ energy P x ∧ energy P x ≤ 2 * β * sqNorm x := by
    have h : α * sqNorm x ≤ StateSpacePassivity.energy P x ∧
        StateSpacePassivity.energy P x ≤ β * sqNorm x := by
      simpa [sqNorm_eq_norm_sq, euclidean] using! hb (euclidean x)
    have hx : energy P x = 2 * StateSpacePassivity.energy P x := by
      simp only [StateSpacePassivity.energy]
      ring
    rw [hx]
    constructor <;> linarith [h.1, h.2]
  exact ⟨⟨P, 2 * α, 2 * β, mul_pos two_pos hα, mul_pos two_pos (hα.trans_le hβα),
    StateSpacePassivity.symmetric_of_posDef hP, fun x => (hbound x).1, fun x => (hbound x).2,
    by rw [add_comm]; exact hlyap⟩⟩

@[powerlib_domain, aesop norm forward (immediate := [h])]
theorem exponentiallyStable_of_isHurwitz {m : AutonomousModel n}
    (h : LinearSystems.IsHurwitz m.A) : ExponentiallyStable m :=
  (accepted_nonempty_of_isHurwitz h).some.exponentially_stable

@[powerlib_foundation]
private lemma eigenmode_hasDerivAt (A : Matrix (Fin n) (Fin n) ℝ) {μ : ℂ} {v : Fin n → ℂ}
    (heig : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) (t : ℝ) (j : Fin n) :
    HasDerivAt (fun s : ℝ => Complex.exp (μ * s) * v j)
      (∑ k, (A j k : ℂ) * (Complex.exp (μ * t) * v k)) t := by
  have hcoe : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have hexp := ((hcoe.const_mul μ).cexp).mul_const (v j)
  convert! hexp using 1
  have hj := congrFun heig j
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.coe_algebraMap,
    Pi.smul_apply, smul_eq_mul] at hj
  calc ∑ k, (A j k : ℂ) * (Complex.exp (μ * t) * v k)
      = Complex.exp (μ * t) * ∑ k, (A j k : ℂ) * v k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by rw [hj]; ring

@[powerlib_foundation]
private lemma isTrajectory_part (m : AutonomousModel n) {μ : ℂ} {v : Fin n → ℂ}
    (heig : m.A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) (part : ℂ →L[ℝ] ℝ)
    (hpart : ∀ (a : ℝ) (z : ℂ), part ((a : ℂ) * z) = a * part z) :
    IsTrajectory m (fun t j => part (Complex.exp (μ * t) * v j)) := by
  intro t
  refine hasDerivAt_pi.2 fun j => ?_
  have h := part.hasFDerivAt.comp_hasDerivAt t (eigenmode_hasDerivAt m.A heig t j)
  convert! h using 1
  simp [AutonomousModel.field, generated.linearField_spec, Matrix.mulVec, dotProduct, map_sum, hpart]

@[powerlib_domain, aesop norm forward (immediate := [h])]
theorem isHurwitz_of_exponentiallyStable {m : AutonomousModel n}
    (h : ExponentiallyStable m) : LinearSystems.IsHurwitz m.A := by
  obtain ⟨K, -, r, hr, hdecay⟩ := h
  intro μ v hv heig
  by_contra hμ
  have hre : 0 ≤ μ.re := by simpa using hμ
  let x : ℝ → State n := fun t j => Complex.reCLM (Complex.exp (μ * t) * v j)
  let y : ℝ → State n := fun t j => Complex.imCLM (Complex.exp (μ * t) * v j)
  have hx : IsTrajectory m x := isTrajectory_part m heig Complex.reCLM (by simp)
  have hy : IsTrajectory m y := isTrajectory_part m heig Complex.imCLM (by simp)
  have hsq {w : ℝ → State n} (hw : IsTrajectory m w) {t : ℝ} (ht : 0 ≤ t) :
      sqNorm (w t) ≤ (K * Real.exp (-(r * t))) ^ 2 * sqNorm (w 0) := by
    have hb := pow_le_pow_left₀ (norm_nonneg _) (hdecay w hw t ht) 2
    rw [sqNorm_eq_norm_sq, sqNorm_eq_norm_sq]
    nlinarith [hb]
  let N : ℝ := ∑ j, Complex.normSq (v j)
  have hsum (t : ℝ) :
      sqNorm (x t) + sqNorm (y t) = Real.exp (μ.re * t) ^ 2 * N := by
    have hexp : Complex.normSq (Complex.exp (μ * t)) = Real.exp (μ.re * t) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
      simp [Complex.mul_re]
    simp only [sqNorm, x, y, N, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Complex.reCLM_apply, Complex.imCLM_apply]
    rw [← hexp, ← Complex.normSq_mul, Complex.normSq_apply]
    ring
  have hN : 0 < N := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
    exact Finset.sum_pos' (fun k _ => Complex.normSq_nonneg _)
      ⟨j, Finset.mem_univ _, Complex.normSq_pos.mpr hj⟩
  have hlarge (t : ℝ) (ht : 0 ≤ t) : 1 ≤ (K * Real.exp (-(r * t))) ^ 2 := by
    have h0 := hsum 0
    simp only [mul_zero, Real.exp_zero, one_pow, one_mul] at h0
    have hgrow : N ≤ Real.exp (μ.re * t) ^ 2 * N :=
      le_mul_of_one_le_left hN.le
        (one_le_pow₀ (Real.one_le_exp_iff.mpr (mul_nonneg hre ht)))
    have hle : Real.exp (μ.re * t) ^ 2 * N ≤ (K * Real.exp (-(r * t))) ^ 2 * N := by
      rw [← hsum t, ← h0, mul_add]
      exact add_le_add (hsq hx ht) (hsq hy ht)
    exact le_of_mul_le_mul_right (by rw [one_mul]; exact hgrow.trans hle) hN
  have hlim : Tendsto (fun t : ℝ => (K * Real.exp (-(r * t))) ^ 2) atTop (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => Real.exp (-(r * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hr)
    simpa using (he.const_mul K).pow 2
  obtain ⟨t, ht, hsmall⟩ :=
    ((eventually_ge_atTop (0 : ℝ)).and (hlim.eventually (gt_mem_nhds zero_lt_one))).exists
  exact absurd (hlarge t ht) (not_le.mpr hsmall)

@[powerlib_domain] theorem exponentiallyStable_iff_isHurwitz (m : AutonomousModel n) :
    ExponentiallyStable m ↔ LinearSystems.IsHurwitz m.A :=
  ⟨isHurwitz_of_exponentiallyStable, exponentiallyStable_of_isHurwitz⟩

@[powerlib_domain] theorem exponentiallyStable_iff_spectrallyStable (m : AutonomousModel n) :
    ExponentiallyStable m ↔ SpectrallyStable m.A :=
  (exponentiallyStable_iff_isHurwitz m).trans (spectrallyStable_iff_isHurwitz m.A).symm

@[powerlib_domain] theorem accepted_nonempty_iff_isHurwitz (m : AutonomousModel n) :
    Nonempty (Accepted m) ↔ LinearSystems.IsHurwitz m.A :=
  ⟨fun ⟨c⟩ => isHurwitz_of_exponentiallyStable c.exponentially_stable,
    accepted_nonempty_of_isHurwitz⟩

end powerlib.LTI

namespace powerlib.Dynamics
open Matrix

variable {n : ℕ}

@[powerlib_domain] theorem locallyExponentiallyStable_of_isHurwitz_jacobian
    {f : State n → State n} {x_eq : State n} (A : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hA : LinearSystems.IsHurwitz A) : LocallyExponentiallyStable f x_eq :=
  _root_.hurwitz_linearization_locally_exponentially_stable A hf heq hJac hA

@[powerlib_domain] theorem locallyExponentiallyStable_of_spectrallyStable_jacobian
    {f : State n → State n} {x_eq : State n} (A : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hA : LTI.SpectrallyStable A) : LocallyExponentiallyStable f x_eq :=
  locallyExponentiallyStable_of_isHurwitz_jacobian A hf heq hJac
    ((LTI.spectrallyStable_iff_isHurwitz A).mp hA)

@[powerlib_domain] theorem unstable_of_jacobian_eigenvalue_re_pos
    {f : State n → State n} {x_eq : State n} (A : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hunstable : ∃ (μ : ℂ) (v : Fin n → ℂ),
      v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re) :
    Unstable f x_eq :=
  _root_.unstable_of_exists_complex_eigenvalue_re_pos A hf heq hJac hunstable

@[powerlib_domain] theorem unstable_of_characteristic_root_re_pos
    {f : State n → State n} {x_eq : State n} (A : Matrix (Fin n) (Fin n) ℝ)
    (hf : ContDiff ℝ 1 f) (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    {s : ℂ} (hroot : (LTI.characteristicMatrix A s).det = 0) (hs : 0 < s.re) :
    Unstable f x_eq := by
  obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
  refine unstable_of_jacobian_eigenvalue_re_pos A hf heq hJac ⟨s, v, hv, ?_, hs⟩
  rw [LTI.characteristicMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hzero
  exact (sub_eq_zero.mp hzero).symm

end powerlib.Dynamics
