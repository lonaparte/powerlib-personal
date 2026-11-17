import dependencies.Mathlib
import dependencies.LeanForControl
import theorem.Attributes
import theorem.Dynamics.VariationOfConstants

/-! # Periodic linear time-varying systems: transition and monodromy matrices

The transition matrix of a bounded linear time-varying system (LeanForControl's Peano–Baker
state-transition matrix), its monodromy matrix for a periodic state matrix, and the independence
of the Floquet multipliers from the initial time.

Scope.
* The linear time-varying system `ẋ = A(t) x` with a continuous real state matrix
  `A : ℝ → Matrix X X ℝ` that is uniformly bounded, `‖A t‖ ≤ M` (operator `L∞` norm,
  `Matrix.Norms.Operator`; vectors carry the sup norm). Every `T`-periodic continuous `A` is
  uniformly bounded (`exists_bound_of_periodic`).
* No model family; every statement is generic in the state matrix `A`.
* One transition matrix. `transition A t s` is an abbreviation of LeanForControl's Peano–Baker
  state-transition matrix `LinearSystems.stateTransitionMatrix A t s`
  (`LinearSystems/Solutions/CtsLTV.lean`, imported through `dependencies/LeanForControl.lean`),
  the matrix of the variation-of-constants formula of
  `theorem/Dynamics/VariationOfConstants.lean`. Its upstream laws (continuous `A`, a bound on the
  segment, implied by `‖A t‖ ≤ M`) apply to `transition` directly: `Φ(s, s) = I`
  (`LinearSystems.stateTransitionMatrix_self`), `Φ(t, s) Φ(s, τ) = Φ(t, τ)` for `s` between `τ`
  and `t` (`LinearSystems.stateTransitionMatrix_comp`), and `∂_t Φ(t, s) = A(t) Φ(t, s)` on all
  of `ℝ` (`Dynamics.stm_hasDerivAt`). The statements below use forward times `t ≥ s`.

Source: work-sync theory/T-harmonic-linearization.md §1.6 (monodromy `Φ(T, 0)`, multipliers);
projects/basin-guard/notes/concepts/guard-object.md §1, §5; projects/vsc-parametric-oscillation/
references/gfm-driven-gfl-parametric-resonance/notes/concepts/coupled-parametric-resonance.md §2
(`Φ' = J Φ`, `Φ(0) = I`).

Results.
* `transition_unique`, `trajectory_eq` — every forward matrix or vector solution is
  `Φ(t, s) C`, resp. `Φ(t, s) x(s)` (upstream uniqueness `stateTransitionMatrix_mul_unique`,
  `stateTransitionMatrix_mulVec_unique` on `[s, t]`).
* `norm_transition_le` — `‖Φ(t, s)‖ ≤ ‖I‖ e^{M (t - s)}` (Peano–Baker term bounds).
* `transition_add_period` — `Φ(t + T, s + T) = Φ(t, s)` for a `T`-periodic `A` (any real
  period).
* `monodromy`, `transition_add_nat_mul_period`, `monodromy_add_int_mul` —
  `monodromy A T s = Φ(s + T, s)`; `Φ(s + nT, s) = M_s^n`; `M_{s + kT} = M_s`.
* `charpoly_monodromy`, `spectrum_monodromy` — the characteristic polynomial and the complex
  spectrum (Floquet multipliers) of `M_s` do not depend on the initial time `s`
  (`M_0 = Q P`, `M_s = P Q` with `P = Φ(s, 0)`, `Q = Φ(T, s)`).
-/

noncomputable section
namespace powerlib.Periodic

open Set Matrix Function
open scoped Matrix.Norms.Operator

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The linear matrix field `Y ↦ A(t) Y`. -/
def matField (A : ℝ → Matrix X X ℝ) (t : ℝ) (Y : Matrix X X ℝ) : Matrix X X ℝ := A t * Y

/-- The linear vector field `x ↦ A(t) x`. -/
def vecField (A : ℝ → Matrix X X ℝ) (t : ℝ) (x : X → ℝ) : X → ℝ := A t *ᵥ x

/-- State-transition matrix `Φ(t, s)` of `ẋ = A(t) x`: LeanForControl's Peano–Baker series. -/
abbrev transition (A : ℝ → Matrix X X ℝ) (t s : ℝ) : Matrix X X ℝ :=
  LinearSystems.stateTransitionMatrix A t s

/-- One-period (monodromy) matrix from the initial time `s`. -/
def monodromy (A : ℝ → Matrix X X ℝ) (T s : ℝ) : Matrix X X ℝ := transition A (s + T) s

variable {A : ℝ → Matrix X X ℝ} {M : ℝ}

/-! ## Bounds -/

@[tmio T, powerlib_foundation] theorem vecField_lipschitz (hM : ∀ t, ‖A t‖ ≤ M) (t : ℝ) :
    LipschitzWith (Real.toNNReal M) (vecField A t) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, vecField, vecField, ← Matrix.mulVec_sub, Real.coe_toNNReal']
  exact (Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul_of_nonneg_right ((hM t).trans (le_max_left _ _)) (norm_nonneg _))

/-- A continuous periodic state matrix (period `T > 0`) is uniformly bounded. -/
@[tmio T, powerlib_foundation] theorem exists_bound_of_periodic {T : ℝ} (hA : Continuous A)
    (hP : Periodic A T) (hT : 0 < T) : ∃ M, ∀ t, ‖A t‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hA.continuousOn
  refine ⟨M, fun t => ?_⟩
  obtain ⟨y, hy, hty⟩ := hP.exists_mem_Ico₀ hT t
  rw [hty]
  exact hM y (Ico_subset_Icc_self hy)

/-! ## Uniqueness and growth -/

/-- Every forward matrix solution of `Ẏ = A(t) Y` with `Y(s) = C` is `Φ(t, s) C`. -/
@[tmio T, powerlib_foundation] theorem transition_unique (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    {s : ℝ} {Y : ℝ → Matrix X X ℝ} (hY : IsIntegralCurveOn Y (matField A) (Ici s)) :
    ∀ t, s ≤ t → Y t = transition A t s * Y s := by
  intro t hst
  have hYs : IsIntegralCurveOn Y (matField A) (uIcc s t) :=
    hY.mono (by rw [uIcc_of_le hst]; exact Icc_subset_Ici_self)
  exact LinearSystems.stateTransitionMatrix_mul_unique hA (fun r _ => hM r) (Y s)
    (hYs.isIntegralSolution (hA.continuousOn.mul hYs.continuousOn)) hYs.continuousOn t
    right_mem_uIcc

/-- Every forward vector solution of `ẋ = A(t) x` is `x(t) = Φ(t, s) x(s)`. -/
@[tmio T, powerlib_foundation] theorem trajectory_eq (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    {s : ℝ} {x : ℝ → X → ℝ} (hx : IsIntegralCurveOn x (vecField A) (Ici s)) :
    ∀ t, s ≤ t → x t = transition A t s *ᵥ x s := by
  intro t hst
  have hxs : IsIntegralCurveOn x (vecField A) (uIcc s t) :=
    hx.mono (by rw [uIcc_of_le hst]; exact Icc_subset_Ici_self)
  exact LinearSystems.stateTransitionMatrix_mulVec_unique hA (fun r _ => hM r) (x s)
    (hxs.isIntegralSolution ((continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      (hA.continuousOn.prodMk hxs.continuousOn))) hxs.continuousOn t right_mem_uIcc

/-- Growth bound `‖Φ(t, s)‖ ≤ ‖I‖ e^{M (t - s)}`: the Peano–Baker terms are bounded by the
exponential series (LeanForControl `norm_peanoBakerTerm_le`). -/
@[tmio T, powerlib_foundation] theorem norm_transition_le (hM : ∀ t, ‖A t‖ ≤ M) {s t : ℝ}
    (hst : s ≤ t) :
    ‖transition A t s‖ ≤ ‖(1 : Matrix X X ℝ)‖ * Real.exp (Real.toNNReal M * (t - s)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rw [Real.coe_toNNReal _ hM0, ← abs_of_nonneg (sub_nonneg.2 hst), Real.exp_eq_exp_ℝ]
  exact tsum_of_norm_bounded
    ((NormedSpace.expSeries_div_hasSum_exp (M * |t - s|)).mul_left ‖(1 : Matrix X X ℝ)‖)
    fun k => (LinearSystems.norm_peanoBakerTerm_le (fun r _ => hM r) k t right_mem_uIcc).trans_eq
      (mul_div_assoc _ _ _)

/-! ## Periodicity -/

/-- `Φ(t + T, s + T) = Φ(t, s)` for a `T`-periodic state matrix (any real period `T`). -/
@[tmio T, powerlib_foundation] theorem transition_add_period (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    {T : ℝ} (hP : Periodic A T) {s t : ℝ} (hst : s ≤ t) :
    transition A (t + T) (s + T) = transition A t s := by
  have hY : IsIntegralCurveOn (fun r => transition A (r + T) (s + T)) (matField A) (Ici s) :=
    fun r _ => by
      simpa only [matField, hP r] using
        ((Dynamics.stm_hasDerivAt hA (r + T) (s + T)).comp_add_const r T).hasDerivWithinAt
  simpa [LinearSystems.stateTransitionMatrix_self] using transition_unique hA hM hY t hst

@[tmio T, powerlib_foundation] theorem monodromy_add_period (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    {T c : ℝ} (hT : 0 ≤ T) (hP : Periodic A c) (s : ℝ) :
    monodromy A T (s + c) = monodromy A T s := by
  rw [monodromy, monodromy, show s + c + T = s + T + c by ring]
  exact transition_add_period hA hM hP (by linarith)

@[tmio T, powerlib_foundation] theorem monodromy_add_int_mul (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    {T : ℝ} (hT : 0 ≤ T) (hP : Periodic A T) (s : ℝ) (k : ℤ) :
    monodromy A T (s + k * T) = monodromy A T s :=
  monodromy_add_period hA hM hT (hP.int_mul k) s

/-- `Φ(s + n T, s) = (monodromy A T s)^n`. -/
@[tmio T, powerlib_foundation] theorem transition_add_nat_mul_period (hA : Continuous A)
    (hM : ∀ t, ‖A t‖ ≤ M) {T : ℝ} (hT : 0 ≤ T) (hP : Periodic A T) (s : ℝ) (n : ℕ) :
    transition A (s + n * T) s = monodromy A T s ^ n := by
  induction n with
  | zero => simp [LinearSystems.stateTransitionMatrix_self]
  | succ n ih =>
    have hn : (0 : ℝ) ≤ n * T := mul_nonneg (Nat.cast_nonneg n) hT
    have hshift : transition A (s + T + n * T) (s + n * T) = transition A (s + T) s :=
      transition_add_period hA hM (hP.nat_mul n) (by linarith)
    rw [pow_succ', ← ih, monodromy, ← hshift,
      show s + ((n + 1 : ℕ) : ℝ) * T = s + T + n * T by push_cast; ring]
    exact (LinearSystems.stateTransitionMatrix_comp hA (fun r _ => hM r)
      (mem_uIcc_of_le (by linarith) (by linarith))).symm

/-- On `[0, T]`: `M_0 = Q P` and `M_s = P Q` with `P = Φ(s, 0)`, `Q = Φ(T, s)`. -/
@[tmio T, powerlib_foundation] theorem monodromy_eq_mul_swap (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    {T : ℝ} (hP : Periodic A T) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s ≤ T) :
    monodromy A T 0 = transition A T s * transition A s 0 ∧
      monodromy A T s = transition A s 0 * transition A T s := by
  constructor
  · rw [monodromy, zero_add]
    exact (LinearSystems.stateTransitionMatrix_comp hA (fun r _ => hM r)
      (mem_uIcc_of_le hs0 hsT)).symm
  · have hshift : transition A (s + T) (0 + T) = transition A s 0 :=
      transition_add_period hA hM hP hs0
    rw [zero_add] at hshift
    rw [monodromy, ← hshift]
    exact (LinearSystems.stateTransitionMatrix_comp hA (fun r _ => hM r)
      (mem_uIcc_of_le hsT (by linarith))).symm

/-- The characteristic polynomial of the monodromy matrix does not depend on the initial
time. -/
@[tmio T, powerlib_foundation] theorem charpoly_monodromy (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    {T : ℝ} (hT : 0 ≤ T) (hP : Periodic A T) (s : ℝ) :
    (monodromy A T s).charpoly = (monodromy A T 0).charpoly := by
  rcases hT.eq_or_lt with hT0 | hTpos
  · subst hT0
    simp [monodromy, LinearSystems.stateTransitionMatrix_self]
  · set k : ℤ := ⌊s / T⌋
    set s' : ℝ := s - k * T
    have hs'0 : 0 ≤ s' := by
      have := Int.floor_le (s / T)
      have h2 : (k : ℝ) * T ≤ s := by
        calc (k : ℝ) * T ≤ s / T * T := mul_le_mul_of_nonneg_right this hTpos.le
          _ = s := by field_simp
      simp only [s']; linarith
    have hs'T : s' ≤ T := by
      have := Int.lt_floor_add_one (s / T)
      have h2 : s < ((k : ℝ) + 1) * T := by
        calc s = s / T * T := by field_simp
          _ < ((k : ℝ) + 1) * T := mul_lt_mul_of_pos_right this hTpos
      simp only [s']; nlinarith
    have hred : monodromy A T s = monodromy A T s' := by
      have := monodromy_add_int_mul hA hM hT hP s' k
      rwa [show s' + k * T = s by simp [s']] at this
    obtain ⟨h0, hs⟩ := monodromy_eq_mul_swap hA hM hP hs'0 hs'T
    rw [hred, hs, h0, Matrix.charpoly_mul_comm]

/-- The Floquet multipliers (complex spectrum of the complexified monodromy matrix) do not
depend on the initial time. -/
@[tmio T, powerlib_foundation] theorem spectrum_monodromy (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    {T : ℝ} (hT : 0 ≤ T) (hP : Periodic A T) (s : ℝ) :
    spectrum ℂ ((monodromy A T s).map (algebraMap ℝ ℂ)) =
      spectrum ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ)) := by
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.mem_spectrum_iff_isRoot_charpoly,
    Matrix.charpoly_map, Matrix.charpoly_map, charpoly_monodromy hA hM hT hP s]

end powerlib.Periodic
