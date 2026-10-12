import dependencies.Mathlib
import dependencies.LeanForControl
import theorem.Attributes
import theorem.Linear.Transfer

/-! # Covariance Lyapunov equation of a vector OU process (foundation)

Source: work-sync `theory/T-sde-systems.md` §1.8.2 (stationary covariance
`A P∞ + P∞ Aᵀ + B Bᵀ = 0`), §1.12.2 (differential Lyapunov equation
`Ṗ = A P + P Aᵀ + B Bᵀ`), §2.5 ("A Hurwitz ⇔ P∞ exists, unique, positive definite").

Conventions (as in the note): drift `dX = A X dt + B dW` with a **plus** sign, `A` Hurwitz means
every complex eigenvalue has negative real part (`LinearSystems.IsHurwitz`).  All objects are
real matrices `Matrix (Fin n) (Fin n) ℝ`; `B : Matrix (Fin n) (Fin m) ℝ`.

Scope (Rules §3).  These are linear-algebra / matrix-ODE facts about the covariance equations.
That `P(t)` *is* the covariance of the Itô solution of `dX = AX dt + B dW` is not proved here
(it needs Itô calculus); the results are not stochastic stability theorems.

Reuse (Rules §15).  Existence and uniqueness for positive-definite forcing is
`LinearSystems.IsHurwitz.exists_posDef_unique_solution_continuous_lyapunov` (LeanForControl,
equation `P Aᵀᵀ + Aᵀ P = -Q`, applied to `Aᵀ`).  LeanForControl requires `Q ≻ 0`; the
semidefinite forcing `B Bᵀ` is handled by linearity: `P_Q = P_{Q+I} - P_I`, and
`P_Q + ε P_I = P_{Q+εI} ≻ 0` for every `ε > 0` gives `P_Q ⪰ 0`.  Transposition of Hurwitz
matrices goes through `powerlib.Linear.spectrallyStable_iff_isHurwitz`.  The decay
`‖e^{tA}‖ → 0` is derived from LeanForControl's contraction block
`IsHurwitz.exists_norm_exp_nat_smul_lt_one`.

Correction (T-sde-systems §2.5, §1.12.2).  "A Hurwitz ⇔ P∞ exists, is unique and positive
definite" is false in both directions without controllability:
* `posDef_solution_not_imp_hurwitz`: `A = 0`, `B = 0`, `P = I` solves the equation with
  `P ≻ 0` although `A` is not Hurwitz (and every matrix solves it, so uniqueness fails too);
* `hurwitz_not_imp_posDef_solution`: `A = -I`, `B = 0` is Hurwitz but every solution is `0`.
What holds is `exists_unique_posSemidef_covLyapunov`: `A` Hurwitz ⇒ a unique solution exists
and it is positive *semi*definite; it is positive *definite* exactly when `(A, B)` is
controllable (`posDef_iff_isControllable`, below).

Controllability and the Gramian (T-sde-systems §2.5, corrected statement).
* `integral_gramian_eq`: if `A P + P Aᵀ + Q = 0` then `∫₀ᵀ e^{tA} Q e^{tAᵀ} dt = P − e^{TA} P e^{TAᵀ}`
  for every `T` (fundamental theorem of calculus; no stability assumption).
* `tendsto_integral_gramian`: for Hurwitz `A`, `∫₀ᵀ e^{tA} Q e^{tAᵀ} dt → P∞` as `T → ∞`, i.e.
  `P∞ = ∫₀^∞ e^{tA} B Bᵀ e^{tAᵀ} dt` (improper integral) for `Q = B Bᵀ`.
* `posDef_of_isControllable`: `A` Hurwitz, `(A, B)` controllable ⇒ `P∞ ≻ 0` (the kernel of `P∞`
  is `Aᵀ`-invariant and contained in `ker Bᵀ`; purely algebraic).
* `isControllable_of_posDef`: `A` Hurwitz and some `P ≻ 0` solves the equation ⇒ `(A, B)`
  controllable (a vector orthogonal to the reachable subspace makes `xᵀ e^{tA} P e^{tAᵀ} x`
  constant and positive, while it tends to `0`).
* `posDef_iff_isControllable`, `stationaryCov_gramian`: for Hurwitz `A`, `P∞ ≻ 0 ⇔ (A, B)`
  controllable.
Controllability is LeanForControl's `LinearSystems.IsControllable` (reachability in `n` steps);
the proof reuses its rank characterization, reachable-subspace invariance (Cayley–Hamilton) and
`MatrixAlgebra.mulVec_kernel_trivial_iff_rank_eq_card_cols`.
-/

noncomputable section
namespace powerlib.Stochastic.Lyapunov

open Matrix Filter
open scoped Matrix.Norms.Frobenius Topology

variable {n m : ℕ}

-- Compatibility with the pinned Mathlib (same local instances as LeanForControl's
-- `LyapunovEquation`): expose the Frobenius-derived instances explicitly.
noncomputable local instance frobeniusENormedAddMonoid' :
    ENormedAddMonoid (Matrix (Fin n) (Fin n) ℝ) :=
  (NormedAddCommGroup.toENormedAddCommMonoid :
    ENormedAddCommMonoid (Matrix (Fin n) (Fin n) ℝ)).toENormedAddMonoid

/-- The covariance Lyapunov equation `A P + P Aᵀ + Q = 0`. -/
def SolvesCovLyapunov (A P Q : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A * P + P * Aᵀ + Q = 0

@[powerlib_foundation] theorem solvesCovLyapunov_iff (A P Q : Matrix (Fin n) (Fin n) ℝ) :
    SolvesCovLyapunov A P Q ↔ LinearSystems.SolvesContinuousLyapunovEquation Aᵀ P Q := by
  unfold SolvesCovLyapunov LinearSystems.SolvesContinuousLyapunovEquation
  rw [transpose_transpose]
  constructor
  · intro h; rw [eq_neg_iff_add_eq_zero, ← h]; abel
  · intro h; rw [add_comm (A * P), h]; abel

/-- Transposition preserves the Hurwitz property. -/
@[powerlib_foundation] theorem isHurwitz_transpose {A : Matrix (Fin n) (Fin n) ℝ}
    (h : LinearSystems.IsHurwitz A) : LinearSystems.IsHurwitz Aᵀ := by
  rw [← powerlib.Linear.spectrallyStable_iff_isHurwitz] at h ⊢
  intro s hs
  apply h s
  have e : powerlib.Linear.characteristicMatrix Aᵀ s =
      (powerlib.Linear.characteristicMatrix A s)ᵀ := by
    ext i j
    simp [powerlib.Linear.characteristicMatrix, Matrix.one_apply, eq_comm]
  rwa [e, det_transpose] at hs

@[powerlib_foundation] theorem solvesCovLyapunov_add {A P P' Q Q' : Matrix (Fin n) (Fin n) ℝ}
    (h : SolvesCovLyapunov A P Q) (h' : SolvesCovLyapunov A P' Q') :
    SolvesCovLyapunov A (P + P') (Q + Q') := by
  unfold SolvesCovLyapunov at *
  calc A * (P + P') + (P + P') * Aᵀ + (Q + Q')
      = (A * P + P * Aᵀ + Q) + (A * P' + P' * Aᵀ + Q') := by
        rw [mul_add, add_mul]; abel
    _ = 0 := by rw [h, h', add_zero]

@[powerlib_foundation] theorem solvesCovLyapunov_smul {A P Q : Matrix (Fin n) (Fin n) ℝ}
    (c : ℝ) (h : SolvesCovLyapunov A P Q) : SolvesCovLyapunov A (c • P) (c • Q) := by
  unfold SolvesCovLyapunov at *
  rw [mul_smul_comm, smul_mul_assoc, ← smul_add, ← smul_add, h, smul_zero]

@[powerlib_foundation] theorem solvesCovLyapunov_sub {A P P' Q Q' : Matrix (Fin n) (Fin n) ℝ}
    (h : SolvesCovLyapunov A P Q) (h' : SolvesCovLyapunov A P' Q') :
    SolvesCovLyapunov A (P - P') (Q - Q') := by
  have := solvesCovLyapunov_add h (solvesCovLyapunov_smul (-1) h')
  simpa [sub_eq_add_neg] using this

/-- For Hurwitz `A` the homogeneous equation has only the zero solution. -/
@[powerlib_foundation] theorem eq_zero_of_solvesCovLyapunov_zero {A S : Matrix (Fin n) (Fin n) ℝ}
    (hA : LinearSystems.IsHurwitz A) (hS : SolvesCovLyapunov A S 0) : S = 0 := by
  obtain ⟨P₁, -, hP₁, huniq⟩ :=
    (isHurwitz_transpose hA).exists_posDef_unique_solution_continuous_lyapunov 1 PosDef.one
  have h1 : SolvesCovLyapunov A P₁ 1 := (solvesCovLyapunov_iff _ _ _).mpr hP₁
  have h2 : SolvesCovLyapunov A (P₁ + S) 1 := by simpa using solvesCovLyapunov_add h1 hS
  have := huniq _ ((solvesCovLyapunov_iff _ _ _).mp h2)
  simpa using this

/-- Uniqueness of solutions for Hurwitz `A` and any forcing `Q`. -/
@[powerlib_foundation] theorem solvesCovLyapunov_unique {A P P' Q : Matrix (Fin n) (Fin n) ℝ}
    (hA : LinearSystems.IsHurwitz A) (h : SolvesCovLyapunov A P Q)
    (h' : SolvesCovLyapunov A P' Q) : P = P' := by
  have := eq_zero_of_solvesCovLyapunov_zero hA (by simpa using solvesCovLyapunov_sub h h')
  exact sub_eq_zero.mp this

/-- Existence for Hurwitz `A`, any forcing `Q` (via `P_{Q+I} - P_I`). -/
@[powerlib_foundation] theorem exists_solvesCovLyapunov {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : LinearSystems.IsHurwitz A) (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosSemidef) :
    ∃ P, SolvesCovLyapunov A P Q := by
  have hAt := isHurwitz_transpose hA
  obtain ⟨P₁, -, hP₁, -⟩ := hAt.exists_posDef_unique_solution_continuous_lyapunov 1 PosDef.one
  obtain ⟨P₂, -, hP₂, -⟩ := hAt.exists_posDef_unique_solution_continuous_lyapunov (Q + 1)
    (PosDef.posSemidef_add hQ PosDef.one)
  refine ⟨P₂ - P₁, ?_⟩
  simpa using solvesCovLyapunov_sub ((solvesCovLyapunov_iff _ _ _).mpr hP₂)
    ((solvesCovLyapunov_iff _ _ _).mpr hP₁)

/-- **Stationary covariance.** For Hurwitz `A` and positive-semidefinite forcing `Q`, the
equation `A P + P Aᵀ + Q = 0` has a unique solution, and it is positive semidefinite. -/
@[powerlib_foundation] theorem exists_unique_posSemidef_covLyapunov
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : LinearSystems.IsHurwitz A)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosSemidef) :
    ∃ P, P.PosSemidef ∧ SolvesCovLyapunov A P Q ∧
      ∀ S, SolvesCovLyapunov A S Q → S = P := by
  have hAt := isHurwitz_transpose hA
  obtain ⟨P, hP⟩ := exists_solvesCovLyapunov hA Q hQ
  obtain ⟨P₁, hP₁pd, hP₁, -⟩ := hAt.exists_posDef_unique_solution_continuous_lyapunov 1 PosDef.one
  have hP₁' : SolvesCovLyapunov A P₁ 1 := (solvesCovLyapunov_iff _ _ _).mpr hP₁
  refine ⟨P, ?_, hP, fun S hS => solvesCovLyapunov_unique hA hS hP⟩
  -- symmetry: `Pᵀ` solves the same equation
  have hQt : Qᵀ = Q := by
    have := hQ.1; rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hPt : SolvesCovLyapunov A Pᵀ Q := by
    unfold SolvesCovLyapunov at hP ⊢
    have := congrArg transpose hP
    rw [transpose_add, transpose_add, transpose_mul, transpose_mul, transpose_transpose, hQt,
      transpose_zero] at this
    rw [← this]; abel
  have hsymm : Pᵀ = P := solvesCovLyapunov_unique hA hPt hP
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨by rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hsymm], fun x => ?_⟩
  -- `P + ε P₁` is the positive-definite solution for `Q + ε I`
  have key : ∀ ε : ℝ, 0 < ε → 0 ≤ star x ⬝ᵥ ((P + ε • P₁) *ᵥ x) := by
    intro ε hε
    obtain ⟨Pε, hPεpd, hPε, -⟩ := hAt.exists_posDef_unique_solution_continuous_lyapunov
      (Q + ε • 1) (PosDef.posSemidef_add hQ (PosDef.one.smul hε))
    have hsum : SolvesCovLyapunov A (P + ε • P₁) (Q + ε • 1) :=
      solvesCovLyapunov_add hP (solvesCovLyapunov_smul ε hP₁')
    have := solvesCovLyapunov_unique hA hsum ((solvesCovLyapunov_iff _ _ _).mpr hPε)
    rw [this]
    exact hPεpd.posSemidef.dotProduct_mulVec_nonneg x
  have hP₁x : 0 ≤ star x ⬝ᵥ (P₁ *ᵥ x) := hP₁pd.posSemidef.dotProduct_mulVec_nonneg x
  by_contra hneg
  push Not at hneg
  set a := star x ⬝ᵥ (P *ᵥ x)
  set b := star x ⬝ᵥ (P₁ *ᵥ x)
  have hε : 0 < -a / (b + 1) := div_pos (by linarith) (by linarith)
  have := key _ hε
  rw [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, smul_eq_mul] at this
  have h2 : a + -a / (b + 1) * b = a / (b + 1) := by field_simp; ring
  have h3 : a / (b + 1) < 0 := div_neg_of_neg_of_pos hneg (by linarith)
  linarith

/-- The covariance equation of `dX = A X dt + B dW`: forcing `B Bᵀ`. -/
@[powerlib_foundation] theorem exists_unique_posSemidef_stationaryCov
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : LinearSystems.IsHurwitz A)
    (B : Matrix (Fin n) (Fin m) ℝ) :
    ∃ P, P.PosSemidef ∧ SolvesCovLyapunov A P (B * Bᵀ) ∧
      ∀ S, SolvesCovLyapunov A S (B * Bᵀ) → S = P := by
  apply exists_unique_posSemidef_covLyapunov hA
  simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose B

/-! ## Counterexamples to "A Hurwitz ⇔ P∞ unique positive definite" -/

@[powerlib_foundation] theorem not_isHurwitz_zero :
    ¬ LinearSystems.IsHurwitz (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
  intro h
  have := h 0 (fun _ => 1) (by
    intro hv; have := congrFun hv 0; simp at this) (by simp)
  simp at this

/-- `A = 0`, `B = 0`, `P = I`: a positive-definite solution with `A` not Hurwitz. -/
@[powerlib_foundation] theorem posDef_solution_not_imp_hurwitz :
    ∃ (A P : Matrix (Fin 1) (Fin 1) ℝ) (B : Matrix (Fin 1) (Fin 1) ℝ),
      P.PosDef ∧ SolvesCovLyapunov A P (B * Bᵀ) ∧ ¬ LinearSystems.IsHurwitz A ∧
      ∀ S, SolvesCovLyapunov A S (B * Bᵀ) :=
  ⟨0, 1, 0, PosDef.one, by simp [SolvesCovLyapunov], not_isHurwitz_zero,
    fun S => by simp [SolvesCovLyapunov]⟩

@[powerlib_foundation] theorem isHurwitz_neg_one :
    LinearSystems.IsHurwitz (-1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  intro μ v hv heig
  have hv0 : v 0 ≠ 0 := by
    intro h0; apply hv; funext i; fin_cases i; exact h0
  have := congrFun heig 0
  simp [Matrix.mulVec, dotProduct] at this
  have hμ : μ = -1 := by
    have : (μ + 1) * v 0 = 0 := by linear_combination -this
    have := (mul_eq_zero.mp this).resolve_right hv0
    linear_combination this
  rw [hμ]; norm_num

/-- `A = -1` is Hurwitz, `B = 0`, yet no solution is positive definite (it is `0`). -/
@[powerlib_foundation] theorem hurwitz_not_imp_posDef_solution :
    ∃ (A B : Matrix (Fin 1) (Fin 1) ℝ), LinearSystems.IsHurwitz A ∧
      ∀ P, SolvesCovLyapunov A P (B * Bᵀ) → ¬ P.PosDef := by
  refine ⟨-1, 0, isHurwitz_neg_one, fun P hP hPd => ?_⟩
  have h0 : P = 0 := solvesCovLyapunov_unique isHurwitz_neg_one hP
    (by simp [SolvesCovLyapunov])
  subst h0
  have := hPd.diag_pos (i := 0)
  simp at this

/-! ## Decay of the matrix exponential of a Hurwitz matrix -/

/-- `‖e^{tA}‖ → 0` as `t → ∞` for Hurwitz `A`. -/
@[powerlib_foundation] theorem tendsto_norm_exp_smul_zero {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : LinearSystems.IsHurwitz A) :
    Tendsto (fun t : ℝ => ‖NormedSpace.exp (t • A)‖) atTop (𝓝 0) := by
  obtain ⟨m, hm, hc⟩ := hA.exists_norm_exp_nat_smul_lt_one
  set C := NormedSpace.exp ((m : ℝ) • A) with hC
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hcont : Continuous (fun r : ℝ => NormedSpace.exp (r • A)) :=
    continuous_iff_continuousAt.2 fun r => (hasDerivAt_exp_smul_const A r).continuousAt
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := m)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hbound : ∀ t : ℝ, 0 ≤ t →
      ‖NormedSpace.exp (t • A)‖ ≤ ‖C‖ ^ (⌊t / m⌋₊) * K := by
    intro t ht
    set k := ⌊t / m⌋₊
    set r := t - k * m
    have hk1 : (k : ℝ) ≤ t / m := Nat.floor_le (div_nonneg ht hmpos.le)
    have hk2 : t / m < k + 1 := Nat.lt_floor_add_one _
    have hr0 : 0 ≤ r := by
      have := (le_div_iff₀ hmpos).mp hk1; simp only [r]; linarith
    have hr1 : r ≤ m := by
      have := (div_lt_iff₀ hmpos).mp hk2; simp only [r]; nlinarith
    have hsplit : t • A = ((k : ℝ) * m) • A + r • A := by
      rw [← add_smul]; congr 1; simp only [r]; ring
    have hexp : NormedSpace.exp (t • A) = C ^ k * NormedSpace.exp (r • A) := by
      rw [hsplit, Matrix.exp_add_of_commute _ _ (((Commute.refl A).smul_left _).smul_right _)]
      congr 1
      rw [hC, ← Matrix.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    have hEr := hK r ⟨hr0, hr1⟩
    rw [hexp]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, pow_zero, one_mul, pow_zero, one_mul]; exact hEr
    · calc ‖C ^ k * NormedSpace.exp (r • A)‖ ≤ ‖C ^ k‖ * ‖NormedSpace.exp (r • A)‖ :=
            norm_mul_le _ _
        _ ≤ ‖C‖ ^ k * K := by
            apply mul_le_mul (norm_pow_le' C hkpos) hEr (norm_nonneg _)
            positivity
  have hfloor : Tendsto (fun t : ℝ => ⌊t / m⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_id.atTop_div_const hmpos)
  have hpow : Tendsto (fun t : ℝ => ‖C‖ ^ (⌊t / m⌋₊) * K) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg C) hc).comp hfloor).mul_const K
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hpow
  filter_upwards [eventually_ge_atTop 0] with t ht using hbound t ht

/-! ## Differential Lyapunov equation `Ṗ = A P + P Aᵀ + Q` -/

/-- Closed-form solution `e^{tA} (P₀ - P∞) e^{tAᵀ} + P∞`. -/
def covSol (A Pinf P₀ : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  NormedSpace.exp (t • A) * (P₀ - Pinf) * NormedSpace.exp (t • Aᵀ) + Pinf

@[powerlib_foundation] theorem covSol_zero (A Pinf P₀ : Matrix (Fin n) (Fin n) ℝ) :
    covSol A Pinf P₀ 0 = P₀ := by
  simp [covSol, NormedSpace.exp_zero]

/-- `covSol` solves `Ṗ = A P + P Aᵀ + Q` whenever `P∞` solves the algebraic equation. -/
@[powerlib_foundation] theorem covSol_hasDerivAt {A Pinf Q : Matrix (Fin n) (Fin n) ℝ}
    (hinf : SolvesCovLyapunov A Pinf Q) (P₀ : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (covSol A Pinf P₀)
      (A * covSol A Pinf P₀ t + covSol A Pinf P₀ t * Aᵀ + Q) t := by
  have hl := (hasDerivAt_exp_smul_const' A t).mul_const (P₀ - Pinf)
  have hr := hasDerivAt_exp_smul_const Aᵀ t
  have h := (hl.mul hr).add_const Pinf
  unfold covSol
  convert! h using 1
  unfold SolvesCovLyapunov at hinf
  have hQ : Q = -(A * Pinf + Pinf * Aᵀ) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hinf
  rw [hQ]
  simp only [mul_add, add_mul, mul_assoc]
  abel

/-- Uniqueness: any differentiable solution with `P 0 = P₀` is `covSol`. -/
@[powerlib_foundation] theorem covODE_unique {A Pinf Q P₀ : Matrix (Fin n) (Fin n) ℝ}
    (hinf : SolvesCovLyapunov A Pinf Q) {P : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ t, HasDerivAt P (A * P t + P t * Aᵀ + Q) t) (h0 : P 0 = P₀) :
    P = covSol A Pinf P₀ := by
  -- `E = P - covSol` solves `Ė = A E + E Aᵀ`, `E 0 = 0`; conjugate by `e^{-tA}`.
  set E : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t => P t - covSol A Pinf P₀ t with hE
  have hEd : ∀ t, HasDerivAt E (A * E t + E t * Aᵀ) t := by
    intro t
    have := (hP t).sub (covSol_hasDerivAt hinf P₀ t)
    convert! this using 1
    simp only [hE, mul_sub, sub_mul]; abel
  set F : ℝ → Matrix (Fin n) (Fin n) ℝ :=
    fun t => NormedSpace.exp (t • (-A)) * E t * NormedSpace.exp (t • (-Aᵀ)) with hF
  have hFd : ∀ t, HasDerivAt F 0 t := by
    intro t
    have h := (((hasDerivAt_exp_smul_const' (-A) t).mul (hEd t)).mul
      (hasDerivAt_exp_smul_const (-Aᵀ) t))
    set e := NormedSpace.exp (t • (-A))
    set e' := NormedSpace.exp (t • (-Aᵀ))
    have c1 : A * e = e * A := ((((Commute.refl A).neg_right).smul_right t).exp_right).eq
    have c2 : Aᵀ * e' = e' * Aᵀ := ((((Commute.refl Aᵀ).neg_right).smul_right t).exp_right).eq
    have hval : (-A * e * E t + e * (A * E t + E t * Aᵀ)) * e' + e * E t * (e' * -Aᵀ) = 0 := by
      simp only [neg_mul, mul_neg, add_mul, mul_add]
      rw [c1, ← c2]
      simp only [mul_assoc]
      abel
    convert! h using 1
    exact hval.symm
  have hFc : ∀ t, F t = F 0 := fun t =>
    is_const_of_deriv_eq_zero (fun s => (hFd s).differentiableAt) (fun s => (hFd s).deriv) t 0
  have hF0 : F 0 = 0 := by
    simp [hF, hE, h0, covSol_zero, NormedSpace.exp_zero]
  have hinvL : ∀ t : ℝ, NormedSpace.exp (t • A) * NormedSpace.exp (t • (-A)) = 1 := by
    intro t
    rw [← Matrix.exp_add_of_commute _ _ ((((Commute.refl A).neg_right).smul_left t).smul_right t)]
    simp [NormedSpace.exp_zero]
  have hinvR : ∀ t : ℝ, NormedSpace.exp (t • (-Aᵀ)) * NormedSpace.exp (t • Aᵀ) = 1 := by
    intro t
    rw [← Matrix.exp_add_of_commute _ _ ((((Commute.refl Aᵀ).neg_left).smul_left t).smul_right t)]
    simp [NormedSpace.exp_zero]
  funext t
  have hEt : E t = 0 := by
    have : E t = NormedSpace.exp (t • A) * F t * NormedSpace.exp (t • Aᵀ) := by
      simp only [hF, ← mul_assoc]
      rw [hinvL, one_mul, mul_assoc, hinvR, mul_one]
    rw [this, hFc t, hF0, mul_zero, zero_mul]
  exact sub_eq_zero.mp hEt

/-- Entries are bounded by the Frobenius norm. -/
@[powerlib_foundation] theorem abs_entry_le_norm (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    |M i j| ≤ ‖M‖ := by
  rw [frobenius_norm_def]
  have h : ‖M i j‖ ^ (2 : ℝ) ≤ ∑ i, ∑ j, ‖M i j‖ ^ (2 : ℝ) :=
    le_trans (Finset.single_le_sum (f := fun j => ‖M i j‖ ^ (2 : ℝ))
      (fun _ _ => by positivity) (Finset.mem_univ j))
      (Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖ ^ (2 : ℝ))
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i))
  calc |M i j| = (‖M i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_mul (norm_nonneg _)]; norm_num
    _ ≤ _ := Real.rpow_le_rpow (by positivity) h (by norm_num)

/-- For Hurwitz `A`, the solution of the differential Lyapunov equation converges to `P∞`
from every initial matrix (Frobenius norm). -/
@[powerlib_foundation] theorem covSol_tendsto_norm {A Pinf P₀ : Matrix (Fin n) (Fin n) ℝ}
    (hA : LinearSystems.IsHurwitz A) :
    Tendsto (fun t => ‖covSol A Pinf P₀ t - Pinf‖) atTop (𝓝 0) := by
  have h1 := tendsto_norm_exp_smul_zero hA
  have h2 := tendsto_norm_exp_smul_zero (isHurwitz_transpose hA)
  have hprod : Tendsto (fun t : ℝ => ‖NormedSpace.exp (t • A)‖ * ‖P₀ - Pinf‖ *
      ‖NormedSpace.exp (t • Aᵀ)‖) atTop (𝓝 0) := by
    simpa using (h1.mul_const ‖P₀ - Pinf‖).mul h2
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) hprod
  simp only [covSol, add_sub_cancel_right]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

/-- Entrywise convergence `P(t)ᵢⱼ → (P∞)ᵢⱼ`. -/
@[powerlib_foundation] theorem covSol_tendsto_entry {A Pinf P₀ : Matrix (Fin n) (Fin n) ℝ}
    (hA : LinearSystems.IsHurwitz A) (i j : Fin n) :
    Tendsto (fun t => covSol A Pinf P₀ t i j) atTop (𝓝 (Pinf i j)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun t => ‖covSol A Pinf P₀ t - Pinf‖) (fun t => norm_nonneg _)
    (fun t => ?_) (covSol_tendsto_norm hA)
  have := abs_entry_le_norm (covSol A Pinf P₀ t - Pinf) i j
  simpa [Real.norm_eq_abs] using this

/-! ## Controllability and positive definiteness of the stationary covariance -/

section Controllability

open scoped Nat

/-- `x ⬝ (M y) = (Mᵀ x) ⬝ y`. -/
private lemma dot_mulVec_eq {ι : Type*} [Fintype ι] (M : Matrix (Fin n) ι ℝ) (x : Fin n → ℝ)
    (y : ι → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = (Mᵀ *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, mulVec_transpose]

/-- Quadratic form of the covariance equation: for symmetric `P` solving
`A P + P Aᵀ + B Bᵀ = 0`, `2 (P x)·(Aᵀ x) + |Bᵀ x|² = 0`. -/
@[powerlib_foundation] theorem cov_quadratic {A P : Matrix (Fin n) (Fin n) ℝ}
    {B : Matrix (Fin n) (Fin m) ℝ} (hP : SolvesCovLyapunov A P (B * Bᵀ)) (hs : Pᵀ = P)
    (x : Fin n → ℝ) :
    2 * ((P *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x)) + (Bᵀ *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ x) = 0 := by
  have h := congrArg (fun M => x ⬝ᵥ (M *ᵥ x)) hP
  simp only [add_mulVec, dotProduct_add, zero_mulVec, dotProduct_zero] at h
  have e1 : x ⬝ᵥ ((A * P) *ᵥ x) = (P *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) := by
    rw [← mulVec_mulVec, dot_mulVec_eq, dotProduct_comm]
  have e2 : x ⬝ᵥ ((P * Aᵀ) *ᵥ x) = (P *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) := by
    rw [← mulVec_mulVec, dot_mulVec_eq, hs]
  have e3 : x ⬝ᵥ ((B * Bᵀ) *ᵥ x) = (Bᵀ *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ x) := by
    rw [← mulVec_mulVec, dot_mulVec_eq]
  rw [e1, e2, e3] at h
  linarith

/-- Kernel invariance: if `P x = 0` then `Bᵀ x = 0` and `P Aᵀ x = 0`. -/
@[powerlib_foundation] theorem cov_kernel_invariant {A P : Matrix (Fin n) (Fin n) ℝ}
    {B : Matrix (Fin n) (Fin m) ℝ} (hP : SolvesCovLyapunov A P (B * Bᵀ)) (hs : Pᵀ = P)
    {x : Fin n → ℝ} (hx : P *ᵥ x = 0) : Bᵀ *ᵥ x = 0 ∧ P *ᵥ (Aᵀ *ᵥ x) = 0 := by
  have hq := cov_quadratic hP hs x
  rw [hx, zero_dotProduct, mul_zero, zero_add, dotProduct_self_eq_zero] at hq
  refine ⟨hq, ?_⟩
  have h := congrArg (· *ᵥ x) hP
  simp only [add_mulVec, zero_mulVec] at h
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hx, hq, mulVec_zero, mulVec_zero,
    zero_add, add_zero] at h
  exact h

/-- **Controllability ⇒ positive definite stationary covariance.**  For Hurwitz `A`, the solution
of `A P + P Aᵀ + B Bᵀ = 0` is positive definite when `(A, B)` is controllable. -/
@[powerlib_foundation] theorem posDef_of_isControllable {A P : Matrix (Fin n) (Fin n) ℝ}
    {B : Matrix (Fin n) (Fin m) ℝ} (hA : LinearSystems.IsHurwitz A)
    (hP : SolvesCovLyapunov A P (B * Bᵀ)) (hc : LinearSystems.IsControllable A B) :
    P.PosDef := by
  obtain ⟨P', hpsd, hP', huniq⟩ := exists_unique_posSemidef_stationaryCov hA B
  obtain rfl : P = P' := huniq P hP
  have hs : Pᵀ = P := by
    have := hpsd.isHermitian.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  refine PosDef.of_dotProduct_mulVec_pos hpsd.isHermitian fun x hx => ?_
  rcases (hpsd.dotProduct_mulVec_nonneg x).lt_or_eq with h | h
  · exact h
  exfalso; apply hx
  have hPx : P *ᵥ x = 0 := hpsd.dotProduct_mulVec_zero_iff.mp h.symm
  have hpow : ∀ k : ℕ, P *ᵥ ((Aᵀ) ^ k *ᵥ x) = 0 := by
    intro k
    induction k with
    | zero => simpa using hPx
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec]
      exact (cov_kernel_invariant hP hs ih).2
  have hB : ∀ k : ℕ, Bᵀ *ᵥ ((Aᵀ) ^ k *ᵥ x) = 0 := fun k =>
    (cov_kernel_invariant hP hs (hpow k)).1
  obtain ⟨u, hu⟩ := hc x
  have hxx : x ⬝ᵥ x = 0 := by
    calc x ⬝ᵥ x = x ⬝ᵥ ∑ k : Fin n, (A ^ (k : ℕ) * B) *ᵥ u k := congrArg (x ⬝ᵥ ·) hu
      _ = ∑ k : Fin n, x ⬝ᵥ ((A ^ (k : ℕ) * B) *ᵥ u k) := dotProduct_sum _ _ _
      _ = 0 := Finset.sum_eq_zero fun k _ => by
          rw [dot_mulVec_eq, transpose_mul, transpose_pow, ← mulVec_mulVec, hB, zero_dotProduct]
  exact dotProduct_self_eq_zero.mp hxx

/-- A vector orthogonal to the reachable subspace of an uncontrollable pair. -/
@[powerlib_foundation] theorem exists_orthogonal_of_not_isControllable
    {A : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin m) ℝ}
    (hc : ¬ LinearSystems.IsControllable A B) :
    ∃ x : Fin n → ℝ, x ≠ 0 ∧ ∀ (k : ℕ) (u : Fin m → ℝ), x ⬝ᵥ ((A ^ k * B) *ᵥ u) = 0 := by
  rw [LinearSystems.isControllable_iff_controllabilityMatrix_rank_eq, ← rank_transpose] at hc
  have hker := (MatrixAlgebra.mulVec_kernel_trivial_iff_rank_eq_card_cols
    (LinearSystems.controllabilityMatrix A B)ᵀ).not.mpr (by simpa using hc)
  push Not at hker
  obtain ⟨x, hxk, hx0⟩ := hker
  refine ⟨x, hx0, ?_⟩
  have horth : ∀ r ∈ LinearSystems.reachableSubspace A B, x ⬝ᵥ r = 0 := by
    intro r hr
    obtain ⟨w, rfl⟩ := (LinearSystems.mem_reachableSubspace_iff r).mp hr
    rw [dot_mulVec_eq, hxk, zero_dotProduct]
  have hmem : ∀ (k : ℕ) (u : Fin m → ℝ),
      (A ^ k * B) *ᵥ u ∈ LinearSystems.reachableSubspace A B := by
    intro k
    induction k with
    | zero => intro u; simpa using LinearSystems.range_B_le_reachableSubspace A B ⟨u, rfl⟩
    | succ k ih =>
      intro u
      have hinv := LinearSystems.reachableSubspace_invariant A B
      rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at hinv
      have := hinv _ (ih u)
      rw [mulVecLin_apply, mulVec_mulVec] at this
      rwa [pow_succ', Matrix.mul_assoc]
  exact fun k u => horth _ (hmem k u)

/-- `x ⊥ e^{tA} B u` for every `t` when `x ⊥ A^k B u` for every `k` (exponential series). -/
@[powerlib_foundation] theorem dot_exp_mul_eq_zero {A : Matrix (Fin n) (Fin n) ℝ}
    {B : Matrix (Fin n) (Fin m) ℝ} {x : Fin n → ℝ}
    (hx : ∀ (k : ℕ) (u : Fin m → ℝ), x ⬝ᵥ ((A ^ k * B) *ᵥ u) = 0) (t : ℝ) (u : Fin m → ℝ) :
    x ⬝ᵥ ((NormedSpace.exp (t • A) * B) *ᵥ u) = 0 := by
  let L : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun M => x ⬝ᵥ ((M * B) *ᵥ u)
      map_add' := fun M N => by simp [Matrix.add_mul, add_mulVec, dotProduct_add]
      map_smul' := fun c M => by simp [Matrix.smul_mul, smul_mulVec, dotProduct_smul] }
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • A)).map L
    L.continuous_of_finiteDimensional
  have h0 : ∀ k : ℕ, L ((k !⁻¹ : ℝ) • (t • A) ^ k) = 0 := by
    intro k
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, smul_pow, Matrix.smul_mul, smul_mulVec,
      dotProduct_smul, hx, smul_zero]
  simp only [Function.comp_def, h0] at hs
  exact hs.unique hasSum_zero

/-- **Positive definite stationary covariance ⇒ controllability.**  If `A` is Hurwitz and a positive
definite `P` solves `A P + P Aᵀ + B Bᵀ = 0`, then `(A, B)` is controllable.  (A vector `x ≠ 0`
orthogonal to the reachable subspace has `Bᵀ e^{tAᵀ} x = 0`, so `xᵀ e^{tA} P e^{tAᵀ} x` is
constant `= xᵀ P x > 0`, while it tends to `0`.) -/
@[powerlib_foundation] theorem isControllable_of_posDef {A P : Matrix (Fin n) (Fin n) ℝ}
    {B : Matrix (Fin n) (Fin m) ℝ} (hA : LinearSystems.IsHurwitz A)
    (hP : SolvesCovLyapunov A P (B * Bᵀ)) (hpd : P.PosDef) :
    LinearSystems.IsControllable A B := by
  by_contra hc
  obtain ⟨x, hx0, hx⟩ := exists_orthogonal_of_not_isControllable hc
  set G : ℝ → Matrix (Fin n) (Fin n) ℝ :=
    fun t => NormedSpace.exp (t • A) * P * NormedSpace.exp (t • Aᵀ) with hG
  have hQ : A * P + P * Aᵀ = -(B * Bᵀ) := by
    rw [eq_neg_iff_add_eq_zero]; exact hP
  have hGd : ∀ t, HasDerivAt G
      (-(NormedSpace.exp (t • A) * (B * Bᵀ) * NormedSpace.exp (t • Aᵀ))) t := by
    intro t
    have h := ((hasDerivAt_exp_smul_const' A t).mul_const P).mul
      (hasDerivAt_exp_smul_const Aᵀ t)
    have c1 : A * NormedSpace.exp (t • A) = NormedSpace.exp (t • A) * A :=
      (((Commute.refl A).smul_right t).exp_right).eq
    have c2 : NormedSpace.exp (t • Aᵀ) * Aᵀ = Aᵀ * NormedSpace.exp (t • Aᵀ) :=
      (((Commute.refl Aᵀ).smul_right t).exp_right).eq.symm
    have hBB : B * Bᵀ = -(A * P + P * Aᵀ) := by rw [hQ, neg_neg]
    have hval : -(NormedSpace.exp (t • A) * (B * Bᵀ) * NormedSpace.exp (t • Aᵀ)) =
        A * NormedSpace.exp (t • A) * P * NormedSpace.exp (t • Aᵀ) +
          NormedSpace.exp (t • A) * P * (NormedSpace.exp (t • Aᵀ) * Aᵀ) := by
      rw [c1, c2, hBB]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_neg,
        Matrix.neg_mul, neg_neg]
    convert! h using 1
  let Lx : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun M => x ⬝ᵥ (M *ᵥ x)
      map_add' := fun M N => by simp [add_mulVec, dotProduct_add]
      map_smul' := fun c M => by simp [smul_mulVec, dotProduct_smul] }
  let Lc : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap Lx
  have hfd : ∀ t, HasDerivAt (⇑Lc ∘ G) 0 t := by
    intro t
    refine (Lc.hasFDerivAt.comp_hasDerivAt t (hGd t)).congr_deriv ?_
    show x ⬝ᵥ ((-(NormedSpace.exp (t • A) * (B * Bᵀ) * NormedSpace.exp (t • Aᵀ))) *ᵥ x)
      = 0
    rw [neg_mulVec, dotProduct_neg, ← Matrix.mul_assoc, Matrix.mul_assoc _ Bᵀ,
      ← mulVec_mulVec, dot_exp_mul_eq_zero hx, neg_zero]
  have hconst : ∀ t, (⇑Lc ∘ G) t = (⇑Lc ∘ G) 0 := fun t =>
    is_const_of_deriv_eq_zero (fun s => (hfd s).differentiableAt) (fun s => (hfd s).deriv) t 0
  have hG0 : (⇑Lc ∘ G) 0 = x ⬝ᵥ (P *ᵥ x) := by
    simp [Lc, Lx, hG, NormedSpace.exp_zero]
  have hpos : 0 < x ⬝ᵥ (P *ᵥ x) := by
    simpa using hpd.dotProduct_mulVec_pos hx0
  have hGt : Tendsto G atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    have h1 := tendsto_norm_exp_smul_zero hA
    have h2 := tendsto_norm_exp_smul_zero (isHurwitz_transpose hA)
    have hprod : Tendsto (fun t : ℝ => ‖NormedSpace.exp (t • A)‖ * ‖P‖ *
        ‖NormedSpace.exp (t • Aᵀ)‖) atTop (𝓝 0) := by
      simpa using (h1.mul_const ‖P‖).mul h2
    refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) hprod
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  have hlim : Tendsto (⇑Lc ∘ G) atTop (𝓝 0) := by
    simpa using (Lc.continuous.tendsto 0).comp hGt
  have : (⇑Lc ∘ G) 0 = 0 := by
    have hc' : Tendsto (⇑Lc ∘ G) atTop (𝓝 ((⇑Lc ∘ G) 0)) := by
      rw [show (⇑Lc ∘ G) = fun _ => (⇑Lc ∘ G) 0 from funext hconst]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hc' hlim
  linarith [hG0 ▸ this]

/-- **Stationary covariance and controllability** (T-sde-systems §2.5, corrected form).  For
Hurwitz `A`, the solution `P∞` of `A P∞ + P∞ Aᵀ + B Bᵀ = 0` is positive definite if and only if
`(A, B)` is controllable. -/
@[powerlib_foundation] theorem posDef_iff_isControllable {A P : Matrix (Fin n) (Fin n) ℝ}
    {B : Matrix (Fin n) (Fin m) ℝ} (hA : LinearSystems.IsHurwitz A)
    (hP : SolvesCovLyapunov A P (B * Bᵀ)) :
    P.PosDef ↔ LinearSystems.IsControllable A B :=
  ⟨isControllable_of_posDef hA hP, posDef_of_isControllable hA hP⟩

/-! ## Gramian (integral) representation of the stationary covariance -/

/-- Derivative of `t ↦ e^{tA} P e^{tAᵀ}` along a solution of the covariance equation:
`d/dt (e^{tA} P e^{tAᵀ}) = −e^{tA} Q e^{tAᵀ}` when `A P + P Aᵀ + Q = 0`. -/
@[powerlib_foundation] theorem hasDerivAt_exp_conj {A P Q : Matrix (Fin n) (Fin n) ℝ}
    (hP : SolvesCovLyapunov A P Q) (t : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • A) * P * NormedSpace.exp (t • Aᵀ))
      (-(NormedSpace.exp (t • A) * Q * NormedSpace.exp (t • Aᵀ))) t := by
  have h := ((hasDerivAt_exp_smul_const' A t).mul_const P).mul (hasDerivAt_exp_smul_const Aᵀ t)
  have c1 : A * NormedSpace.exp (t • A) = NormedSpace.exp (t • A) * A :=
    (((Commute.refl A).smul_right t).exp_right).eq
  have c2 : NormedSpace.exp (t • Aᵀ) * Aᵀ = Aᵀ * NormedSpace.exp (t • Aᵀ) :=
    (((Commute.refl Aᵀ).smul_right t).exp_right).eq.symm
  have hQ : Q = -(A * P + P * Aᵀ) := by
    unfold SolvesCovLyapunov at hP
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hP
  have hval : -(NormedSpace.exp (t • A) * Q * NormedSpace.exp (t • Aᵀ)) =
      A * NormedSpace.exp (t • A) * P * NormedSpace.exp (t • Aᵀ) +
        NormedSpace.exp (t • A) * P * (NormedSpace.exp (t • Aᵀ) * Aᵀ) := by
    rw [c1, c2, hQ]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_neg,
      Matrix.neg_mul, neg_neg]
  convert! h using 1

/-- **Finite-horizon Gramian identity.**  If `A P + P Aᵀ + Q = 0`, then for every `T`,
`∫₀ᵀ e^{tA} Q e^{tAᵀ} dt = P − e^{TA} P e^{TAᵀ}` (no stability assumption). -/
@[powerlib_foundation] theorem integral_gramian_eq {A P Q : Matrix (Fin n) (Fin n) ℝ}
    (hP : SolvesCovLyapunov A P Q) (T : ℝ) :
    ∫ t in (0 : ℝ)..T, NormedSpace.exp (t • A) * Q * NormedSpace.exp (t • Aᵀ) =
      P - NormedSpace.exp (T • A) * P * NormedSpace.exp (T • Aᵀ) := by
  have hd : ∀ t, HasDerivAt
      (fun t : ℝ => -(NormedSpace.exp (t • A) * P * NormedSpace.exp (t • Aᵀ)))
      (-(-(NormedSpace.exp (t • A) * Q * NormedSpace.exp (t • Aᵀ)))) t := fun t =>
    (hasDerivAt_exp_conj hP t).neg
  simp only [neg_neg] at hd
  have hcont : Continuous fun t : ℝ => NormedSpace.exp (t • A) * Q * NormedSpace.exp (t • Aᵀ) :=
    continuous_iff_continuousAt.2 fun t =>
      (((hasDerivAt_exp_smul_const A t).mul_const Q).mul
        (hasDerivAt_exp_smul_const Aᵀ t)).continuousAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hcont.intervalIntegrable _ _)]
  simp [NormedSpace.exp_zero]
  abel

/-- **Gramian representation of the stationary covariance.**  For Hurwitz `A` and
`A P∞ + P∞ Aᵀ + Q = 0`, `∫₀ᵀ e^{tA} Q e^{tAᵀ} dt → P∞` as `T → ∞`; i.e.
`P∞ = ∫₀^∞ e^{tA} Q e^{tAᵀ} dt` as an improper integral. -/
@[powerlib_foundation] theorem tendsto_integral_gramian {A P Q : Matrix (Fin n) (Fin n) ℝ}
    (hA : LinearSystems.IsHurwitz A) (hP : SolvesCovLyapunov A P Q) :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T,
      NormedSpace.exp (t • A) * Q * NormedSpace.exp (t • Aᵀ)) atTop (𝓝 P) := by
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  simp only [integral_gramian_eq hP, sub_sub_cancel_left, norm_neg]
  have h1 := tendsto_norm_exp_smul_zero hA
  have h2 := tendsto_norm_exp_smul_zero (isHurwitz_transpose hA)
  have hprod : Tendsto (fun t : ℝ => ‖NormedSpace.exp (t • A)‖ * ‖P‖ *
      ‖NormedSpace.exp (t • Aᵀ)‖) atTop (𝓝 0) := by
    simpa using (h1.mul_const ‖P‖).mul h2
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) hprod
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

/-- **Controllability Gramian.**  For Hurwitz `A`, the stationary covariance
`P∞ = lim_{T→∞} ∫₀ᵀ e^{tA} B Bᵀ e^{tAᵀ} dt` of `dX = A X dt + B dW` exists, is the unique solution
of `A P∞ + P∞ Aᵀ + B Bᵀ = 0`, and is positive definite exactly when `(A, B)` is controllable. -/
@[powerlib_foundation] theorem stationaryCov_gramian {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : LinearSystems.IsHurwitz A) (B : Matrix (Fin n) (Fin m) ℝ) :
    ∃ P, SolvesCovLyapunov A P (B * Bᵀ) ∧ (∀ S, SolvesCovLyapunov A S (B * Bᵀ) → S = P) ∧
      Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T,
        NormedSpace.exp (t • A) * (B * Bᵀ) * NormedSpace.exp (t • Aᵀ)) atTop (𝓝 P) ∧
      P.PosSemidef ∧ (P.PosDef ↔ LinearSystems.IsControllable A B) := by
  obtain ⟨P, hpsd, hP, huniq⟩ := exists_unique_posSemidef_stationaryCov hA B
  exact ⟨P, hP, huniq, tendsto_integral_gramian hA hP, hpsd, posDef_iff_isControllable hA hP⟩

end Controllability

end powerlib.Stochastic.Lyapunov
