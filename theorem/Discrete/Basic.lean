import dependencies.Mathlib
import dependencies.LeanForControl
import theorem.Attributes

/-! Discrete-time autonomous linear time-invariant systems `x (k+1) = Φ x k`.

Model boundary.
* Time is discrete: `k : ℕ`.  The state is `Fin n → ℝ` in the submitted coordinate order.
* There is no input, no noise, no switching, no delay and no nonlinear remainder; any
  controller or numerical scheme must already be folded into the single real matrix `Φ`.
* Norms: the state norm is the default sup norm on `Fin n → ℝ`.  All norms on a
  finite-dimensional space are equivalent, so exponential decay does not depend on this choice
  (only the constant `C` does).
* Exponential stability (uniform geometric decay of every trajectory) is
  `∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x, IsTrajectory m x → ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖`;
  it quantifies real constants, so it is written out in each statement that uses it rather
  than defined (single-semantics rule).
* `SchurStable Φ` is stated through complex eigenpairs of the complexification, exactly like
  `LinearSystems.IsHurwitz`.  `schurStable_iff_spectralRadius_lt_one` connects it with the
  Banach-algebra spectral radius.

Results (all trajectory-level, for every initial state):
* `exponentiallyStable_of_schurStable`: Schur stability gives `‖x k‖ ≤ C ρ^k ‖x 0‖` with
  `ρ < 1`, via the LeanForControl Gelfand-formula lemma
  `exists_pow_norm_lt_one_of_spectralRadius_lt_one`.
* `exists_trajectory_not_tendsto_zero`: one eigenvalue with `‖μ‖ ≥ 1` yields a real
  trajectory that does not converge to zero.
* `exponentiallyStable_iff_schurStable`, `asymptoticallyStable_iff_schurStable`.

Source: work-sync theory/T-numerical-integration.md §2.7 (discrete recursion
`x_{n+1} = R(hA) x_n`), required as the discrete semantic layer for the A9 numerics
formalization.  These are general mathematics: foundation results.
-/

noncomputable section
namespace powerlib.Discrete
open Matrix Filter
open scoped Topology

abbrev State (n : ℕ) := Fin n → ℝ

/-- A discrete-time autonomous LTI model `x (k+1) = Φ *ᵥ x k`. -/
@[ext] structure Model (n : ℕ) where
  Φ : Matrix (Fin n) (Fin n) ℝ

variable {n : ℕ}

def Model.step (m : Model n) (x : State n) : State n := m.Φ *ᵥ x

/-- A forward trajectory of the recursion. -/
def IsTrajectory (m : Model n) (x : ℕ → State n) : Prop :=
  ∀ k, x (k + 1) = m.step (x k)

/-- The explicit forward solution. -/
def response (m : Model n) (initial : State n) (k : ℕ) : State n :=
  (m.Φ ^ k) *ᵥ initial

@[simp, powerlib_foundation] theorem response_zero (m : Model n) (initial : State n) :
    response m initial 0 = initial := by
  simp [response]

@[powerlib_foundation] theorem response_isTrajectory (m : Model n) (initial : State n) :
    IsTrajectory m (response m initial) := by
  intro k
  simp [response, Model.step, pow_succ', Matrix.mulVec_mulVec]

/-- Every trajectory is the explicit response of its initial state. -/
@[powerlib_foundation] theorem IsTrajectory.eq_response {m : Model n} {x : ℕ → State n}
    (hx : IsTrajectory m x) (k : ℕ) : x k = response m (x 0) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hx k, ih]
    exact (response_isTrajectory m (x 0) k).symm

/-- Schur stability: every complex eigenvalue lies in the open unit disk. -/
def SchurStable (Φ : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ (μ : ℂ) (v : Fin n → ℂ), v ≠ 0 → Φ.map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1

/-- Every trajectory converges to the origin. -/
def AsymptoticallyStable (m : Model n) : Prop :=
  ∀ x, IsTrajectory m x → Tendsto x atTop (𝓝 0)

section Spectral

open scoped Matrix.Norms.Frobenius

@[powerlib_foundation] private lemma mem_spectrum_iff_eigenpair
    (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    z ∈ spectrum ℂ M ↔ ∃ v : Fin n → ℂ, v ≠ 0 ∧ M *ᵥ v = z • v := by
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    exact ⟨v, hv.2, by simpa [Matrix.toLin'_apply] using hv.apply_eq_smul⟩
  · rintro ⟨v, hv, hMv⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (by simpa [Matrix.toLin'_apply] using hMv), hv⟩

/-- Schur stability is exactly spectral radius below one (spectral radius of the
complexification in the Banach algebra of complex matrices). -/
@[powerlib_foundation] theorem schurStable_iff_spectralRadius_lt_one
    (Φ : Matrix (Fin n) (Fin n) ℝ) :
    SchurStable Φ ↔ spectralRadius ℂ (Φ.map (algebraMap ℝ ℂ)) < 1 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Subsingleton.elim (Φ.map (algebraMap ℝ ℂ)) 0, spectrum.spectralRadius_zero]
      exact zero_lt_one
    · have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
      have h1 : ((1 : NNReal) : ENNReal) = 1 := rfl
      rw [← h1]
      apply spectrum.spectralRadius_lt_of_forall_lt
      intro z hz
      obtain ⟨v, hv, hMv⟩ := (mem_spectrum_iff_eigenpair _ z).mp hz
      have := h z v hv hMv
      exact_mod_cast this
  · intro h μ v hv hMv
    have hz : μ ∈ spectrum ℂ (Φ.map (algebraMap ℝ ℂ)) :=
      (mem_spectrum_iff_eigenpair _ μ).mpr ⟨v, hv, hMv⟩
    have hle : (‖μ‖₊ : ENNReal) ≤ spectralRadius ℂ (Φ.map (algebraMap ℝ ℂ)) := by
      rw [spectralRadius_eq_of_unital]
      exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ (Φ.map (algebraMap ℝ ℂ))) =>
        (‖k‖₊ : ENNReal)) μ hz
    have hlt : (‖μ‖₊ : ENNReal) < 1 := hle.trans_lt h
    exact_mod_cast hlt

end Spectral

section Decay

open scoped Matrix.Norms.Operator

@[powerlib_foundation] private lemma norm_map_complex (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖A.map (algebraMap ℝ ℂ)‖ = ‖A‖ := by
  simp only [Matrix.linfty_opNorm_def, Matrix.map_apply, Complex.coe_algebraMap,
    Complex.nnnorm_real]

/-- A power of a Schur matrix has operator norm below one. -/
@[powerlib_foundation] private lemma exists_pow_norm_lt_one {Φ : Matrix (Fin n) (Fin n) ℝ}
    (h : SchurStable Φ) : ∃ m : ℕ, 0 < m ∧ ‖Φ ^ m‖ < 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, one_pos, by rw [Subsingleton.elim (Φ ^ 1) 0]; simp⟩
  · have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    obtain ⟨m, hm, hlt⟩ := exists_pow_norm_lt_one_of_spectralRadius_lt_one
      (Φ.map (algebraMap ℝ ℂ)) ((schurStable_iff_spectralRadius_lt_one Φ).mp h)
    refine ⟨m, hm, ?_⟩
    rw [← norm_map_complex, Matrix.map_pow]
    exact hlt

/-- Geometric bound on all powers of a Schur matrix. -/
@[powerlib_foundation] theorem SchurStable.exists_pow_bound {Φ : Matrix (Fin n) (Fin n) ℝ}
    (h : SchurStable Φ) :
    ∃ C > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ k : ℕ, ‖Φ ^ k‖ ≤ C * ρ ^ k := by
  obtain ⟨m, hm, hlt⟩ := exists_pow_norm_lt_one h
  set q : ℝ := max ‖Φ ^ m‖ (1 / 2) with hq
  have hq0 : 0 < q := lt_max_of_lt_right (by norm_num)
  have hq1 : q < 1 := max_lt hlt (by norm_num)
  set ρ : ℝ := q ^ ((m : ℝ)⁻¹) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hq0 _
  have hρm : ρ ^ m = q := Real.rpow_inv_natCast_pow hq0.le (Nat.pos_iff_ne_zero.mp hm)
  have hρ1 : ρ < 1 := by
    by_contra hge
    have : (1 : ℝ) ≤ ρ ^ m := one_le_pow₀ (not_lt.mp hge)
    linarith
  set M : ℝ := ∑ r ∈ Finset.range m, ‖Φ ^ r‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun r _ => norm_nonneg _
  refine ⟨M / q + 1, by positivity, ρ, hρ0, hρ1, fun k => ?_⟩
  have hk : k = m * (k / m) + k % m := (Nat.div_add_mod k m).symm
  have hr : k % m < m := Nat.mod_lt k hm
  have hrM : ‖Φ ^ (k % m)‖ ≤ M := Finset.single_le_sum (f := fun r => ‖Φ ^ r‖)
    (fun r _ => norm_nonneg _) (Finset.mem_range.mpr hr)
  have hpow : ‖Φ ^ k‖ ≤ q ^ (k / m) * M := by
    rcases Nat.eq_zero_or_pos (k / m) with h0 | h0
    · have hkr : k = k % m := by
        have h' := hk
        rw [h0, mul_zero, zero_add] at h'
        exact h'
      rw [h0, pow_zero, one_mul, hkr]
      exact hrM
    calc ‖Φ ^ k‖ = ‖(Φ ^ m) ^ (k / m) * Φ ^ (k % m)‖ := by
          rw [← pow_mul, ← pow_add, ← hk]
      _ ≤ ‖(Φ ^ m) ^ (k / m)‖ * ‖Φ ^ (k % m)‖ := norm_mul_le _ _
      _ ≤ q ^ (k / m) * M := by
          apply mul_le_mul _ hrM (norm_nonneg _) (pow_nonneg hq0.le _)
          exact (norm_pow_le' _ h0).trans
            (pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) _)
  have hρk : q ^ (k / m) ≤ ρ ^ k / q := by
    rw [le_div_iff₀ hq0, ← hρm, ← pow_mul, ← pow_add]
    apply pow_le_pow_of_le_one hρ0.le hρ1.le
    omega
  calc ‖Φ ^ k‖ ≤ q ^ (k / m) * M := hpow
    _ ≤ ρ ^ k / q * M := mul_le_mul_of_nonneg_right hρk hM0
    _ = M / q * ρ ^ k := by ring
    _ ≤ (M / q + 1) * ρ ^ k := by
        have : 0 ≤ ρ ^ k := pow_nonneg hρ0.le _
        nlinarith

/-- Schur stability implies uniform exponential decay of every trajectory:
`‖x k‖ ≤ C ρ^k ‖x 0‖` with `C > 0`, `0 ≤ ρ < 1`. -/
@[powerlib_foundation] theorem exponentiallyStable_of_schurStable {m : Model n}
    (h : SchurStable m.Φ) :
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ x, IsTrajectory m x → ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖ := by
  obtain ⟨C, hC, ρ, hρ0, hρ1, hb⟩ := h.exists_pow_bound
  refine ⟨C, hC, ρ, hρ0.le, hρ1, fun x hx k => ?_⟩
  rw [hx.eq_response k, response]
  exact (Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul_of_nonneg_right (hb k) (norm_nonneg _))

end Decay

section Converse

/-- An eigenvalue on or outside the unit circle produces a real trajectory (the real or the
imaginary part of the complex eigenmode `μ^k v`) that does not converge to zero. -/
@[powerlib_foundation] theorem exists_trajectory_not_tendsto_zero {m : Model n} {μ : ℂ}
    {v : Fin n → ℂ} (hv : v ≠ 0) (heig : m.Φ.map (algebraMap ℝ ℂ) *ᵥ v = μ • v)
    (hμ : 1 ≤ ‖μ‖) : ∃ x, IsTrajectory m x ∧ ¬ Tendsto x atTop (𝓝 0) := by
  let x : ℕ → State n := fun k j => (μ ^ k * v j).re
  let y : ℕ → State n := fun k j => (μ ^ k * v j).im
  have hx : IsTrajectory m x := by
    intro k
    have h := MatrixAlgebra.matrixMulVec_re_smul_eigenpair m.Φ μ (μ ^ k) v heig
    simpa [x, Model.step, pow_succ] using h
  have hy : IsTrajectory m y := by
    intro k
    have h := MatrixAlgebra.matrixMulVec_im_smul_eigenpair m.Φ μ (μ ^ k) v heig
    simpa [y, Model.step, pow_succ] using h
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hxt := hcon x hx
  have hyt := hcon y hy
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  have hxj : Tendsto (fun k => x k j) atTop (𝓝 0) :=
    ((continuous_apply j).tendsto 0).comp hxt
  have hyj : Tendsto (fun k => y k j) atTop (𝓝 0) :=
    ((continuous_apply j).tendsto 0).comp hyt
  have hsum : Tendsto (fun k => x k j ^ 2 + y k j ^ 2) atTop (𝓝 0) := by
    simpa using (hxj.pow 2).add (hyj.pow 2)
  have hpos : 0 < Complex.normSq (v j) := Complex.normSq_pos.mpr (by simpa using hj)
  have hlow : ∀ k, Complex.normSq (v j) ≤ x k j ^ 2 + y k j ^ 2 := by
    intro k
    have he : x k j ^ 2 + y k j ^ 2 = Complex.normSq (μ ^ k * v j) := by
      simp only [x, y, Complex.normSq_apply]
      ring
    rw [he, Complex.normSq_mul, map_pow]
    have h1 : 1 ≤ Complex.normSq μ := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg μ]
    have h2 : 1 ≤ Complex.normSq μ ^ k := one_le_pow₀ h1
    nlinarith [Complex.normSq_nonneg (v j)]
  have hev := hsum.eventually (gt_mem_nhds hpos)
  obtain ⟨k, hk⟩ := hev.exists
  exact absurd (hlow k) (not_le.mpr hk)

@[powerlib_foundation] theorem schurStable_of_asymptoticallyStable {m : Model n}
    (h : AsymptoticallyStable m) : SchurStable m.Φ := by
  intro μ v hv heig
  by_contra hμ
  obtain ⟨x, hx, hnot⟩ := exists_trajectory_not_tendsto_zero hv heig (not_lt.mp hμ)
  exact hnot (h x hx)

/-- Uniform exponential decay of every trajectory implies convergence of every trajectory. -/
@[powerlib_foundation] theorem asymptoticallyStable_of_exponentiallyStable {m : Model n}
    (h : ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ x, IsTrajectory m x → ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖) : AsymptoticallyStable m := by
  obtain ⟨C, -, ρ, hρ0, hρ1, hb⟩ := h
  intro x hx
  have hlim : Tendsto (fun k : ℕ => C * ρ ^ k * ‖x 0‖) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul C).mul_const ‖x 0‖
  exact squeeze_zero_norm (hb x hx) hlim

/-- Uniform exponential decay of every trajectory (`‖x k‖ ≤ C ρ^k ‖x 0‖`, `C > 0`,
`0 ≤ ρ < 1`) holds exactly for a Schur matrix. -/
@[powerlib_foundation] theorem exponentiallyStable_iff_schurStable (m : Model n) :
    (∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ x, IsTrajectory m x → ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖) ↔ SchurStable m.Φ :=
  ⟨fun h => schurStable_of_asymptoticallyStable (asymptoticallyStable_of_exponentiallyStable h),
    exponentiallyStable_of_schurStable⟩

@[powerlib_foundation] theorem asymptoticallyStable_iff_schurStable (m : Model n) :
    AsymptoticallyStable m ↔ SchurStable m.Φ :=
  ⟨schurStable_of_asymptoticallyStable,
    fun h => asymptoticallyStable_of_exponentiallyStable (exponentiallyStable_of_schurStable h)⟩

end Converse

end powerlib.Discrete
