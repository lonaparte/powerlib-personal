import dependencies.LeanForControl
import theorem.Estimation.KalmanLTV

/-! # LTV Kalman covariance with LeanForControl's state-transition matrix

The fundamental-matrix hypothesis of `theorem/Estimation/KalmanLTV.lean`, discharged for every
continuous time-varying `A(t)` with LeanForControl's Peano–Baker state-transition matrix.

Scope.
* Linear algebra / matrix ODE, not an engineering result.
* The state-transition matrix is `LinearSystems.stateTransitionMatrix` (Hespanha, *Linear
  Systems Theory*, Ch. 5), reused directly through the dependency interface
  (`dependencies/LeanForControl.lean` imports `LeanForControl.LinearSystems.Solutions.CtsLTV`).
  The upstream norm on matrices is the `L∞`-operator norm (`Matrix.Norms.Operator`), used here
  only to supply its segment bounds.

Source: work-sync theory/T-kalman-filter.md §1.2, §1.4 (as in
`theorem/Estimation/KalmanLTV.lean`).

Results.
* `stm_hasDerivAt`, `stm_self` — `∂_t Φ(t, s) = A(t) Φ(t, s)` at every `t ∈ ℝ` (the upstream
  theorem `hasDerivAt_stateTransitionMatrix` holds on open segments `(s, t₁)`; the anchor is
  shifted with `stateTransitionMatrix_comp`, `stateTransitionMatrix_comp_of_mem`,
  `stateTransitionMatrix_inv`) and `Φ(s, s) = I`.
* `ltv_cov_stateTransition` — **LTV prediction covariance**: for continuous `A(t)`, `Q(t)`,
  `P(t) = Φ(t, t₀) P₀ Φ(t, t₀)ᵀ + ∫_{t₀}^t Φ(t, τ) Q(τ) Φ(t, τ)ᵀ dτ` is the unique solution of
  `Ṗ = A(t) P + P A(t)ᵀ + Q(t)`, `P(t₀) = P₀`.
* `riccati_joseph_form_stateTransition` — a symmetric Riccati solution equals its closed-loop
  (Joseph) integral representation with `Φ_K` the state-transition matrix of `A − P Cᵀ R⁻¹ C`.
* `riccati_posSemidef_of_continuous` — `Q ⪰ 0`, `R ≻ 0`, `P(t₀) ⪰ 0` ⇒ the Riccati solution is
  `⪰ 0` for `t ≥ t₀` (no fundamental-matrix hypothesis left).
-/

noncomputable section
namespace powerlib.Estimation.LTV

open Matrix Set
open scoped Matrix.Norms.Operator

variable {n : ℕ} {A : ℝ → Matrix (Fin n) (Fin n) ℝ}

/-- A bound for `‖A‖` (operator norm, as in LeanForControl's Peano–Baker theory) on a segment. -/
private lemma exists_opNorm_bound (hA : Continuous A) (a b : ℝ) :
    ∃ M, ∀ r ∈ uIcc a b, ‖A r‖ ≤ M :=
  isCompact_uIcc.exists_bound_of_continuousOn hA.continuousOn

/-- `Φ(s, a) Φ(a, s) = I` for LeanForControl's state-transition matrix. -/
private lemma stm_mul_inv (hA : Continuous A) (s a : ℝ) :
    LinearSystems.stateTransitionMatrix A s a * LinearSystems.stateTransitionMatrix A a s = 1 := by
  obtain ⟨M, hM⟩ := exists_opNorm_bound hA a s
  obtain ⟨hunit, hinv⟩ := LinearSystems.stateTransitionMatrix_inv hA hM
  rw [← hinv]
  exact mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hunit)

/-- **LeanForControl's state-transition matrix is a fundamental matrix on all of `ℝ`:**
`∂_t Φ(t, s) = A(t) Φ(t, s)` at every `t` (including `t = s`), for continuous `A`.  The
upstream theorem (`LinearSystems.hasDerivAt_stateTransitionMatrix`, Peano–Baker) gives the
derivative on open segments `t ∈ (s, t₁)`; at `t = s` the anchor is moved with the upstream
composition laws. -/
@[tmio T, powerlib_foundation] theorem stm_hasDerivAt (hA : Continuous A) (t s : ℝ) :
    HasDerivAt (fun z => LinearSystems.stateTransitionMatrix A z s)
      (A t * LinearSystems.stateTransitionMatrix A t s) t := by
  -- derivative with the anchor `a = t - 1`, at an interior point of `(a, t + 1)`
  set a := t - 1 with ha
  obtain ⟨M, hM⟩ := exists_opNorm_bound hA a (t + 1)
  have hmem : t ∈ uIoo a (t + 1) := by
    rw [uIoo_of_le (by rw [ha]; linarith)]; constructor <;> linarith [ha]
  have hda := LinearSystems.hasDerivAt_stateTransitionMatrix hA hM hmem
  -- `Φ(z, s) = Φ(z, a) Φ(a, s)` for all `z` (via the upstream composition laws)
  have hcomp : ∀ z, LinearSystems.stateTransitionMatrix A z s =
      LinearSystems.stateTransitionMatrix A z a * LinearSystems.stateTransitionMatrix A a s := by
    intro z
    obtain ⟨N, hN⟩ := exists_opNorm_bound hA (min (min z s) a) (max (max z s) a)
    have hsub : ∀ x y, x ∈ uIcc (min (min z s) a) (max (max z s) a) →
        y ∈ uIcc (min (min z s) a) (max (max z s) a) → ∀ r ∈ uIcc x y, ‖A r‖ ≤ N := by
      intro x y hx hy r hr
      exact hN r (uIcc_subset_uIcc hx hy hr)
    have mz : z ∈ uIcc (min (min z s) a) (max (max z s) a) := by
      rw [uIcc_of_le (by simp [le_max_iff, min_le_iff])]; constructor <;> simp
    have ms : s ∈ uIcc (min (min z s) a) (max (max z s) a) := by
      rw [uIcc_of_le (by simp [le_max_iff, min_le_iff])]; constructor <;> simp
    have ma : a ∈ uIcc (min (min z s) a) (max (max z s) a) := by
      rw [uIcc_of_le (by simp [le_max_iff, min_le_iff])]; constructor <;> simp
    -- `Φ(z, s) Φ(s, a) = Φ(z, a)` needs `s` between `a` and `z`; otherwise use the other
    -- orderings and invertibility
    rcases le_total a s with has | hsa
    · rcases le_total s z with hsz | hzs
      · -- a ≤ s ≤ z
        have h := LinearSystems.stateTransitionMatrix_comp hA (hsub a z ma mz)
          (show s ∈ uIcc a z from by rw [uIcc_of_le (has.trans hsz)]; exact ⟨has, hsz⟩)
        rw [← h, Matrix.mul_assoc, stm_mul_inv hA s a, Matrix.mul_one]
      · -- z ≤ s and a ≤ s: `Φ(z, s) = Φ(z, a) Φ(a, s)` on the segment between `s` and `a`
        -- or with `z` outside it
        rcases le_total a z with haz | hza
        · exact LinearSystems.stateTransitionMatrix_comp_of_mem hA (hsub s a ms ma)
            (show z ∈ uIcc s a from by rw [uIcc_comm, uIcc_of_le has]; exact ⟨haz, hzs⟩)
        · -- z ≤ a ≤ s
          have h := LinearSystems.stateTransitionMatrix_comp hA (hsub s z ms mz)
            (show a ∈ uIcc s z from by rw [uIcc_comm, uIcc_of_le (hza.trans has)]; exact ⟨hza, has⟩)
          exact h.symm
    · -- s ≤ a
      rcases le_total a z with haz | hza
      · -- s ≤ a ≤ z
        have h := LinearSystems.stateTransitionMatrix_comp hA (hsub s z ms mz)
          (show a ∈ uIcc s z from by rw [uIcc_of_le (hsa.trans haz)]; exact ⟨hsa, haz⟩)
        exact h.symm
      · rcases le_total s z with hsz | hzs
        · -- s ≤ z ≤ a
          exact LinearSystems.stateTransitionMatrix_comp_of_mem hA (hsub s a ms ma)
            (show z ∈ uIcc s a from by rw [uIcc_of_le hsa]; exact ⟨hsz, hza⟩)
        · -- z ≤ s ≤ a
          have h := LinearSystems.stateTransitionMatrix_comp hA (hsub a z ma mz)
            (show s ∈ uIcc a z from by rw [uIcc_comm, uIcc_of_le (hzs.trans hsa)]; exact ⟨hzs, hsa⟩)
          rw [← h, Matrix.mul_assoc, stm_mul_inv hA s a, Matrix.mul_one]
  have hfun : (fun z => LinearSystems.stateTransitionMatrix A z s) =
      fun z => LinearSystems.stateTransitionMatrix A z a *
        LinearSystems.stateTransitionMatrix A a s :=
    funext hcomp
  rw [hfun, hcomp t, ← Matrix.mul_assoc]
  exact hda.mul_const _

/-- `Φ(s, s) = I` (LeanForControl `stateTransitionMatrix_self`). -/
@[powerlib_foundation] theorem stm_self (s : ℝ) :
    LinearSystems.stateTransitionMatrix A s s = 1 :=
  LinearSystems.stateTransitionMatrix_self s

/-- **LTV prediction covariance with LeanForControl's state-transition matrix.**  For continuous
`A(t)`, `Q(t)`, the matrix
`P(t) = Φ(t, t₀) P₀ Φ(t, t₀)ᵀ + ∫_{t₀}^t Φ(t, τ) Q(τ) Φ(t, τ)ᵀ dτ`, with `Φ` the Peano–Baker
state-transition matrix of `ẋ = A(t) x`, is the unique solution of
`Ṗ = A(t) P + P A(t)ᵀ + Q(t)`, `P(t₀) = P₀`. -/
@[powerlib_foundation] theorem ltv_cov_stateTransition (hA : Continuous A)
    {Q : ℝ → Matrix (Fin n) (Fin n) ℝ} (hQ : Continuous Q) (P₀ : Matrix (Fin n) (Fin n) ℝ)
    (t₀ : ℝ) :
    ltvCov (LinearSystems.stateTransitionMatrix A) Q P₀ t₀ t₀ = P₀ ∧
      (∀ t, HasDerivAt (ltvCov (LinearSystems.stateTransitionMatrix A) Q P₀ t₀)
        (A t * ltvCov (LinearSystems.stateTransitionMatrix A) Q P₀ t₀ t +
          ltvCov (LinearSystems.stateTransitionMatrix A) Q P₀ t₀ t * (A t)ᵀ + Q t) t) ∧
      ∀ P : ℝ → Matrix (Fin n) (Fin n) ℝ, (∀ t, HasDerivAt P (A t * P t + P t * (A t)ᵀ + Q t) t) →
        P t₀ = P₀ → P = ltvCov (LinearSystems.stateTransitionMatrix A) Q P₀ t₀ :=
  ⟨ltvCov_self _ stm_self Q P₀ t₀,
    fun t => hasDerivAt_ltvCov hA hQ (stm_hasDerivAt hA) stm_self P₀ t₀ t,
    fun _ hP h0 => ltvCov_unique hA hQ (stm_hasDerivAt hA) stm_self hP h0⟩

variable {p : ℕ} {C : ℝ → Matrix (Fin p) (Fin n) ℝ} {Q : ℝ → Matrix (Fin n) (Fin n) ℝ}
  {R : ℝ → Matrix (Fin p) (Fin p) ℝ}

/-- Continuity of the closed-loop matrix `A − P Cᵀ R⁻¹ C`. -/
private lemma closedLoop_continuous (hA : Continuous A) (hC : Continuous C) (hR : Continuous R)
    (hRu : ∀ t, IsUnit (R t).det) {P : ℝ → Matrix (Fin n) (Fin n) ℝ} (hPc : Continuous P) :
    Continuous fun t => A t - P t * (C t)ᵀ * (R t)⁻¹ * C t := by
  have hRi : Continuous fun t => (R t)⁻¹ := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    have hinv : ContinuousAt Ring.inverse (R t).det := by
      rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ (hRu t).ne_zero
    exact ContinuousAt.comp (f := R) (continuousAt_matrix_inv _ hinv) hR.continuousAt
  exact hA.sub (((hPc.matrix_mul hC.matrix_transpose).matrix_mul hRi).matrix_mul hC)

/-- **Riccati solution, closed-loop integral form, with LeanForControl's state-transition
matrix**: a symmetric solution of `Ṗ = A P + P Aᵀ + Q − P Cᵀ R⁻¹ C P` (continuous coefficients,
`R` symmetric invertible) equals
`Φ_K(t, t₀) P(t₀) Φ_K(t, t₀)ᵀ + ∫_{t₀}^t Φ_K(t, τ) (Q + K R Kᵀ)(τ) Φ_K(t, τ)ᵀ dτ`, where
`K = P Cᵀ R⁻¹` and `Φ_K` is the Peano–Baker state-transition matrix of `A − K C`. -/
@[powerlib_foundation] theorem riccati_joseph_form_stateTransition (hA : Continuous A)
    (hC : Continuous C) (hQ : Continuous Q) (hR : Continuous R) (hRs : ∀ t, (R t)ᵀ = R t)
    (hRu : ∀ t, IsUnit (R t).det) {P : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ t, HasDerivAt P
      (A t * P t + P t * (A t)ᵀ + Q t - P t * (C t)ᵀ * (R t)⁻¹ * C t * P t) t)
    (hPs : ∀ t, (P t)ᵀ = P t) (t₀ : ℝ) :
    P = ltvCov (LinearSystems.stateTransitionMatrix
        fun t => A t - P t * (C t)ᵀ * (R t)⁻¹ * C t)
      (fun t => Q t + (P t * (C t)ᵀ * (R t)⁻¹) * R t * (P t * (C t)ᵀ * (R t)⁻¹)ᵀ) (P t₀) t₀ := by
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun t => (hP t).continuousAt
  exact riccati_joseph_form hA hC hQ hR hRs hRu hP hPs
    (stm_hasDerivAt (closedLoop_continuous hA hC hR hRu hPc)) stm_self t₀

/-- **The Kalman–Bucy Riccati covariance stays positive semidefinite** (no extra hypothesis):
for continuous `A, C, Q, R` with `Q(t) ⪰ 0`, `R(t) ≻ 0`, every solution of
`Ṗ = A P + P Aᵀ + Q − P Cᵀ R⁻¹ C P` with `P(t₀) ⪰ 0` has `P(t) ⪰ 0` for all `t ≥ t₀`. -/
@[powerlib_foundation] theorem riccati_posSemidef_of_continuous (hA : Continuous A)
    (hC : Continuous C) (hQ : Continuous Q) (hR : Continuous R) (hQp : ∀ t, (Q t).PosSemidef)
    (hRp : ∀ t, (R t).PosDef) {P : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ t, HasDerivAt P
      (A t * P t + P t * (A t)ᵀ + Q t - P t * (C t)ᵀ * (R t)⁻¹ * C t * P t) t)
    {t₀ : ℝ} (hP₀ : (P t₀).PosSemidef) {t : ℝ} (ht : t₀ ≤ t) : (P t).PosSemidef := by
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun t => (hP t).continuousAt
  have hRu : ∀ t, IsUnit (R t).det := fun t => (hRp t).isUnit.map Matrix.detMonoidHom
  exact riccati_posSemidef hA hC hQ hR hQp hRp hP
    (stm_hasDerivAt (closedLoop_continuous hA hC hR hRu hPc)) stm_self hP₀ ht

end powerlib.Estimation.LTV
