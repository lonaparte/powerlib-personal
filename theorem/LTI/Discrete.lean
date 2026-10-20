import dependencies.Mathlib
import dependencies.LeanForControl
import theorem.Attributes

/-! # Discrete-time autonomous linear time-invariant systems `x (k+1) = Φ x k`

Schur stability of the state matrix and geometric decay of every trajectory of a discrete-time
autonomous linear recursion, and the closed form of an affine recursion.

Scope.
* Time is discrete: `k : ℕ`.  The state is `Fin n → ℝ` in the submitted coordinate order.
* There is no input, no noise, no switching, no delay and no nonlinear remainder; any
  controller or numerical scheme must already be folded into the single real matrix `Φ`.
* Norms: the state norm is the default sup norm on `Fin n → ℝ`.  All norms on a
  finite-dimensional space are equivalent, so exponential decay does not depend on this choice
  (only the constant `C` does).
* Exponential stability (uniform geometric decay of every trajectory) is
  `∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x : ℕ → State n, (∀ k, x (k + 1) = m.step (x k)) → ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖`;
  it quantifies real constants, so it is written out in each statement that uses it rather
  than defined (single-semantics rule).
* `SchurStable Φ` is stated through complex eigenpairs of the complexification, exactly like
  `LinearSystems.IsHurwitz`.  `schurStable_iff_spectralRadius_lt_one` connects it with the
  Banach-algebra spectral radius, through `spectrum_eq_setOf_eigenpair` (the spectrum of a
  complex matrix over any finite index type is its set of eigenvalues; its membership form is
  `Modal.mem_spectrum_iff_exists_eigvec`).
* These are general mathematics: foundation results.

Source: work-sync theory/T-numerical-integration.md §2.7 (discrete recursion
`x_{n+1} = R(hA) x_n`), required as the discrete semantic layer for the numerics formalization
(`theorem/Numerics/`).

Results (all trajectory-level, for every initial state).
* `exponentiallyStable_of_schurStable`: Schur stability gives `‖x k‖ ≤ C ρ^k ‖x 0‖` with
  `ρ < 1`, via the LeanForControl Gelfand-formula lemma
  `exists_pow_norm_lt_one_of_spectralRadius_lt_one`.
* `exists_trajectory_not_tendsto_zero`: one eigenvalue with `‖μ‖ ≥ 1` yields a real
  trajectory that does not converge to zero.
* `exponentiallyStable_iff_schurStable`, `asymptoticallyStable_iff_schurStable`.
* Powers in blocks, in any seminormed ring: `norm_pow_le_of_block` (`‖x^m‖ ≤ e^{−γ}` and
  `‖x^r‖ ≤ B` for `r < m` give `‖x^k‖ ≤ B e^{γ} (e^{−γ/m})^k`), from the scalar
  `exp_neg_pow_div_le`; also used for the switched period map
  (`theorem/Averaging/SwitchedStability.lean`) and the linearization of maps
  (`theorem/Map/Linearization.lean`).
* Matrix powers on any finite index type (`L∞` operator norm): `norm_map_algebraMap`
  (complexification preserves the norm), `norm_pow_le_norm_one_mul`, `exists_pow_norm_lt_one`
  (spectral radius `< 1` of the complexification gives a contractive power, through the
  LeanForControl Gelfand-formula lemma) and `exists_pow_norm_le_exp` (a contractive power gives
  `‖P ^ n‖ ≤ C e^{-γ n}`); used by the Floquet criterion `theorem/Periodic/Floquet.lean`.
  `SchurStable.exists_pow_bound` is their composite for a Schur matrix.
* `prediction_closedForm`: the affine recursion `x⁺ = A x + B u + d` (any finite index types)
  has `x[k+j] = A^j x[k] + Σ_{i<j} A^{j−1−i}(B u[k+i] + d)` (multi-step prediction of
  theory/T-predictive-machine-control.md).
-/

noncomputable section
namespace powerlib.LTI
open Matrix Filter
open scoped Topology

abbrev State (n : ℕ) := Fin n → ℝ

/-- A discrete-time autonomous LTI model `x (k+1) = Φ *ᵥ x k`. -/
@[ext] structure Model (n : ℕ) where
  Φ : Matrix (Fin n) (Fin n) ℝ

variable {n : ℕ}

def Model.step (m : Model n) (x : State n) : State n := m.Φ *ᵥ x

/-- The explicit forward solution. -/
def response (m : Model n) (initial : State n) (k : ℕ) : State n :=
  (m.Φ ^ k) *ᵥ initial

@[simp, powerlib_foundation] theorem response_zero (m : Model n) (initial : State n) :
    response m initial 0 = initial := by
  simp [response]

/-- The explicit response solves the recursion. -/
@[powerlib_foundation] theorem response_isTrajectory (m : Model n) (initial : State n) :
    ∀ k, response m initial (k + 1) = m.step (response m initial k) := by
  intro k
  simp [response, Model.step, pow_succ', Matrix.mulVec_mulVec]

/-- Every trajectory is the explicit response of its initial state. -/
@[powerlib_foundation] theorem eq_response {m : Model n} {x : ℕ → State n}
    (hx : ∀ k, x (k + 1) = m.step (x k)) (k : ℕ) : x k = response m (x 0) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hx k, ih]
    exact (response_isTrajectory m (x 0) k).symm

/-- Schur stability: every complex eigenvalue lies in the open unit disk. -/
def SchurStable (Φ : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ (μ : ℂ) (v : Fin n → ℂ), v ≠ 0 → Φ.map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1

section Spectral

open scoped Matrix.Norms.Frobenius

/-- The spectrum of a complex square matrix (any finite index type) is its set of eigenvalues. -/
@[powerlib_foundation] theorem spectrum_eq_setOf_eigenpair {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι ℂ) :
    spectrum ℂ M = {z | ∃ v : ι → ℂ, v ≠ 0 ∧ M *ᵥ v = z • v} := by
  ext z
  rw [Set.mem_ofPred_eq, ← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
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
      rw [spectrum_eq_setOf_eigenpair] at hz
      obtain ⟨v, hv, hMv⟩ := hz
      have := h z v hv hMv
      exact_mod_cast this
  · intro h μ v hv hMv
    have hz : μ ∈ spectrum ℂ (Φ.map (algebraMap ℝ ℂ)) := by
      rw [spectrum_eq_setOf_eigenpair]
      exact ⟨v, hv, hMv⟩
    have hle : (‖μ‖₊ : ENNReal) ≤ spectralRadius ℂ (Φ.map (algebraMap ℝ ℂ)) := by
      rw [spectralRadius_eq_of_unital]
      exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ (Φ.map (algebraMap ℝ ℂ))) =>
        (‖k‖₊ : ENNReal)) μ hz
    have hlt : (‖μ‖₊ : ENNReal) < 1 := hle.trans_lt h
    exact_mod_cast hlt

end Spectral

section Blocks

/-- Whole blocks of `m` steps decay per step: `(e^{−γ})^{⌊k/m⌋} ≤ e^{γ} (e^{−γ/m})^k` for
`γ ≥ 0`, `m > 0`. -/
@[powerlib_foundation] theorem exp_neg_pow_div_le {γ : ℝ} (hγ : 0 ≤ γ) {m : ℕ} (hm : 0 < m)
    (k : ℕ) : Real.exp (-γ) ^ (k / m) ≤ Real.exp γ * Real.exp (-(γ / m)) ^ k := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have h1 : (k : ℝ) < m * ((k / m : ℕ) + 1) := by
    have : k < m * (k / m + 1) := by
      rw [mul_add, mul_one]
      exact lt_of_lt_of_le (Nat.lt_div_mul_add hm) (by rw [mul_comm])
    exact_mod_cast this
  have h2 : (k : ℝ) / m - 1 ≤ (k / m : ℕ) := by
    rw [div_sub_one hmR.ne', div_le_iff₀ hmR]
    linarith
  have h3 : γ * ((k : ℝ) / m - 1) ≤ γ * (k / m : ℕ) := mul_le_mul_of_nonneg_left h2 hγ
  have e : (k : ℝ) * -(γ / m) = -(γ * ((k : ℝ) / m)) := by ring
  rw [e]
  linarith

/-- **Block bound for powers.** In a seminormed ring, a bound `‖x^m‖ ≤ e^{−γ}` (`γ ≥ 0`) on one
block of `m > 0` steps and a bound `B` on the shorter powers give
`‖x^k‖ ≤ B e^{γ} (e^{−γ/m})^k` for every `k`. -/
@[powerlib_foundation] theorem norm_pow_le_of_block {R : Type*} [SeminormedRing R] {x : R}
    {m : ℕ} (hm : 0 < m) {γ B : ℝ} (hγ : 0 ≤ γ) (hx : ‖x ^ m‖ ≤ Real.exp (-γ))
    (hB : ∀ r < m, ‖x ^ r‖ ≤ B) (k : ℕ) :
    ‖x ^ k‖ ≤ B * Real.exp γ * Real.exp (-(γ / m)) ^ k := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 hm)
  have hblock : ‖x ^ k‖ ≤ Real.exp (-γ) ^ (k / m) * B := by
    rcases Nat.eq_zero_or_pos (k / m) with h0 | h0
    · have hk : k < m := by
        by_contra h
        exact absurd h0 (Nat.div_pos (not_lt.mp h) hm).ne'
      rw [h0, pow_zero, one_mul]
      exact hB k hk
    calc ‖x ^ k‖ = ‖(x ^ m) ^ (k / m) * x ^ (k % m)‖ := by
          rw [← pow_mul, ← pow_add, Nat.div_add_mod]
      _ ≤ ‖x ^ m‖ ^ (k / m) * ‖x ^ (k % m)‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_pow_le' _ h0) (norm_nonneg _))
      _ ≤ Real.exp (-γ) ^ (k / m) * B :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx _) (hB _ (Nat.mod_lt k hm))
            (norm_nonneg _) (pow_nonneg (Real.exp_pos _).le _)
  calc ‖x ^ k‖ ≤ Real.exp (-γ) ^ (k / m) * B := hblock
    _ ≤ Real.exp γ * Real.exp (-(γ / m)) ^ k * B :=
        mul_le_mul_of_nonneg_right (exp_neg_pow_div_le hγ hm k) hB0
    _ = B * Real.exp γ * Real.exp (-(γ / m)) ^ k := by ring

end Blocks

section MatrixPowers

open scoped Matrix.Norms.Operator

variable {X : Type*} [Fintype X] [DecidableEq X]

@[powerlib_foundation] theorem norm_map_algebraMap (P : Matrix X X ℝ) :
    ‖P.map (algebraMap ℝ ℂ)‖ = ‖P‖ := by
  rw [Matrix.linfty_opNorm_def, Matrix.linfty_opNorm_def]
  simp [Complex.nnnorm_real]

@[powerlib_foundation] theorem norm_pow_le_norm_one_mul {Q : Matrix X X ℝ} (k : ℕ) :
    ‖Q ^ k‖ ≤ ‖(1 : Matrix X X ℝ)‖ * ‖Q‖ ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    calc ‖Q ^ k * Q‖ ≤ ‖Q ^ k‖ * ‖Q‖ := norm_mul_le _ _
      _ ≤ ‖(1 : Matrix X X ℝ)‖ * ‖Q‖ ^ k * ‖Q‖ :=
        mul_le_mul_of_nonneg_right ih (norm_nonneg _)
      _ = _ := by ring

/-- Spectral radius `< 1` gives a contractive power (wraps LeanForControl
`exists_pow_norm_lt_one_of_spectralRadius_lt_one` on the complexification). -/
@[powerlib_foundation] theorem exists_pow_norm_lt_one (P : Matrix X X ℝ)
    (hρ : spectralRadius ℂ (P.map (algebraMap ℝ ℂ)) < 1) : ∃ m : ℕ, 0 < m ∧ ‖P ^ m‖ < 1 := by
  rcases isEmpty_or_nonempty X with hX | hX
  · refine ⟨1, one_pos, ?_⟩
    rw [Subsingleton.elim (P ^ 1) 0, norm_zero]
    norm_num
  · obtain ⟨m, hm, hlt⟩ := exists_pow_norm_lt_one_of_spectralRadius_lt_one
      (P.map (algebraMap ℝ ℂ)) hρ
    refine ⟨m, hm, ?_⟩
    have hmap : (P ^ m).map (algebraMap ℝ ℂ) = (P.map (algebraMap ℝ ℂ)) ^ m := by
      have h := map_pow ((algebraMap ℝ ℂ).mapMatrix (m := X)) P m
      simpa [RingHom.mapMatrix_apply] using h
    rw [← norm_map_algebraMap, hmap]
    exact hlt

/-- A contractive power gives geometric decay of all powers (`norm_pow_le_of_block` with
`e^{−γ} = max ‖P^m‖ (1/2)` and `B = Σ_{r<m} ‖P^r‖`). -/
@[powerlib_foundation] theorem exists_pow_norm_le_exp {P : Matrix X X ℝ} {m : ℕ} (hm : 0 < m)
    (hq : ‖P ^ m‖ < 1) :
    ∃ C γ : ℝ, 0 ≤ C ∧ 0 < γ ∧ ∀ n : ℕ, ‖P ^ n‖ ≤ C * Real.exp (-(γ * n)) := by
  set q : ℝ := max ‖P ^ m‖ (1 / 2) with hq_def
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hγ : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq0 (max_lt hq (by norm_num)))
  set C₀ : ℝ := ∑ r ∈ Finset.range m, ‖P ^ r‖ with hC₀
  have hC₀nn : 0 ≤ C₀ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨C₀ * Real.exp (-Real.log q), -Real.log q / m, mul_nonneg hC₀nn (Real.exp_pos _).le,
    div_pos hγ (Nat.cast_pos.mpr hm), fun n => ?_⟩
  have h := norm_pow_le_of_block hm hγ.le
    (by rw [neg_neg, Real.exp_log hq0]; exact le_max_left _ _)
    (fun r hr => Finset.single_le_sum (f := fun r => ‖P ^ r‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_range.mpr hr)) n
  rwa [← Real.exp_nat_mul, show (n : ℝ) * -(-Real.log q / m) = -(-Real.log q / m * n) by ring]
    at h

end MatrixPowers

section Decay

open scoped Matrix.Norms.Operator

/-- Geometric bound on all powers of a Schur matrix (`exists_pow_norm_lt_one`,
`exists_pow_norm_le_exp`). -/
@[powerlib_foundation] theorem SchurStable.exists_pow_bound {Φ : Matrix (Fin n) (Fin n) ℝ}
    (h : SchurStable Φ) :
    ∃ C > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ k : ℕ, ‖Φ ^ k‖ ≤ C * ρ ^ k := by
  obtain ⟨m, hm, hlt⟩ :=
    exists_pow_norm_lt_one Φ ((schurStable_iff_spectralRadius_lt_one Φ).mp h)
  obtain ⟨C, γ, hC, hγ, hb⟩ := exists_pow_norm_le_exp hm hlt
  refine ⟨C + 1, by linarith, Real.exp (-γ), Real.exp_pos _,
    Real.exp_lt_one_iff.mpr (by linarith), fun k => ?_⟩
  calc ‖Φ ^ k‖ ≤ C * Real.exp (-(γ * k)) := hb k
    _ = C * Real.exp (-γ) ^ k := by rw [← Real.exp_nat_mul]; congr 2; ring
    _ ≤ (C + 1) * Real.exp (-γ) ^ k := by gcongr; linarith

/-- Schur stability implies uniform exponential decay of every trajectory:
`‖x k‖ ≤ C ρ^k ‖x 0‖` with `C > 0`, `0 ≤ ρ < 1`. -/
@[powerlib_foundation] theorem exponentiallyStable_of_schurStable {m : Model n}
    (h : SchurStable m.Φ) :
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ x : ℕ → State n, (∀ k, x (k + 1) = m.step (x k)) → ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖ := by
  obtain ⟨C, hC, ρ, hρ0, hρ1, hb⟩ := h.exists_pow_bound
  refine ⟨C, hC, ρ, hρ0.le, hρ1, fun x hx k => ?_⟩
  rw [eq_response hx k, response]
  exact (Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul_of_nonneg_right (hb k) (norm_nonneg _))

end Decay

section Converse

/-- An eigenvalue on or outside the unit circle produces a real trajectory (the real or the
imaginary part of the complex eigenmode `μ^k v`) that does not converge to zero. -/
@[powerlib_foundation] theorem exists_trajectory_not_tendsto_zero {m : Model n} {μ : ℂ}
    {v : Fin n → ℂ} (hv : v ≠ 0) (heig : m.Φ.map (algebraMap ℝ ℂ) *ᵥ v = μ • v)
    (hμ : 1 ≤ ‖μ‖) :
    ∃ x : ℕ → State n, (∀ k, x (k + 1) = m.step (x k)) ∧ ¬ Tendsto x atTop (𝓝 0) := by
  let x : ℕ → State n := fun k j => (μ ^ k * v j).re
  let y : ℕ → State n := fun k j => (μ ^ k * v j).im
  have hx : ∀ k, x (k + 1) = m.step (x k) := by
    intro k
    have h := MatrixAlgebra.matrixMulVec_re_smul_eigenpair m.Φ μ (μ ^ k) v heig
    simpa [x, Model.step, pow_succ] using h
  have hy : ∀ k, y (k + 1) = m.step (y k) := by
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

/-- Convergence of every trajectory forces a Schur matrix. -/
@[powerlib_foundation] theorem schurStable_of_asymptoticallyStable {m : Model n}
    (h : (∀ x : ℕ → State n, (∀ k, x (k + 1) = m.step (x k)) → Tendsto x atTop (𝓝 0))) : SchurStable m.Φ := by
  intro μ v hv heig
  by_contra hμ
  obtain ⟨x, hx, hnot⟩ := exists_trajectory_not_tendsto_zero hv heig (not_lt.mp hμ)
  exact hnot (h x hx)

/-- Uniform exponential decay of every trajectory implies convergence of every trajectory. -/
@[powerlib_foundation] theorem asymptoticallyStable_of_exponentiallyStable {m : Model n}
    (h : ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ x : ℕ → State n, (∀ k, x (k + 1) = m.step (x k)) → ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖) :
    (∀ x : ℕ → State n, (∀ k, x (k + 1) = m.step (x k)) → Tendsto x atTop (𝓝 0)) := by
  obtain ⟨C, -, ρ, hρ0, hρ1, hb⟩ := h
  intro x hx
  have hlim : Tendsto (fun k : ℕ => C * ρ ^ k * ‖x 0‖) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul C).mul_const ‖x 0‖
  exact squeeze_zero_norm (hb x hx) hlim

/-- Uniform exponential decay of every trajectory (`‖x k‖ ≤ C ρ^k ‖x 0‖`, `C > 0`,
`0 ≤ ρ < 1`) holds exactly for a Schur matrix. -/
@[powerlib_foundation] theorem exponentiallyStable_iff_schurStable (m : Model n) :
    (∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ x : ℕ → State n, (∀ k, x (k + 1) = m.step (x k)) → ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖) ↔ SchurStable m.Φ :=
  ⟨fun h => schurStable_of_asymptoticallyStable (asymptoticallyStable_of_exponentiallyStable h),
    exponentiallyStable_of_schurStable⟩

@[powerlib_foundation] theorem asymptoticallyStable_iff_schurStable (m : Model n) :
    (∀ x : ℕ → State n, (∀ k, x (k + 1) = m.step (x k)) → Tendsto x atTop (𝓝 0)) ↔ SchurStable m.Φ :=
  ⟨schurStable_of_asymptoticallyStable,
    fun h => asymptoticallyStable_of_exponentiallyStable (exponentiallyStable_of_schurStable h)⟩

end Converse

section AffineRecursion

open Finset

/-- Closed form of the `j`-step prediction of the affine model `x⁺ = A x + B u + d`. -/
@[powerlib_foundation] theorem prediction_closedForm {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] (A : Matrix n n ℝ) (B : Matrix n m ℝ) (d : n → ℝ) (x : ℕ → n → ℝ)
    (u : ℕ → m → ℝ) (hx : ∀ k, x (k + 1) = A *ᵥ x k + B *ᵥ u k + d) (k j : ℕ) :
    x (k + j) = (A ^ j) *ᵥ x k +
      ∑ i ∈ range j, (A ^ (j - 1 - i)) *ᵥ (B *ᵥ u (k + i) + d) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← add_assoc, hx, ih, sum_range_succ, Matrix.mulVec_add, Matrix.mulVec_sum,
      Matrix.mulVec_mulVec, ← pow_succ']
    have hterm : ∀ i ∈ range j, A *ᵥ ((A ^ (j - 1 - i)) *ᵥ (B *ᵥ u (k + i) + d)) =
        (A ^ (j + 1 - 1 - i)) *ᵥ (B *ᵥ u (k + i) + d) := by
      intro i hi
      rw [Matrix.mulVec_mulVec, ← pow_succ']
      congr 2
      have := mem_range.mp hi
      omega
    rw [sum_congr rfl hterm]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, Matrix.one_mulVec]
    abel

end AffineRecursion

end powerlib.LTI
