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
and it is positive *semi*definite.  (`P∞ ≻ 0 ⇔ (A,B)` controllable needs the Gramian and is not
formalized here.)
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

end powerlib.Stochastic.Lyapunov
