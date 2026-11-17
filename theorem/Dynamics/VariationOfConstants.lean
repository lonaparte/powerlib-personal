import dependencies.LeanForControl
import theorem.Attributes

/-! # Variation of constants for linear time-varying systems (LeanForControl wrappers)

The variation-of-constants formula for continuous-time LTV systems, by direct reuse of upstream
theorems (Rules §15–§16), and exact zero-order-hold sampling of a constant-input linear system.

Scope.
* Continuous time, finite state index `X`, input index `U`, real coefficients:
  `ẋ = A(t) x + B(t) u(t)` with continuous `A : ℝ → Matrix X X ℝ`, `B : ℝ → Matrix X U ℝ` and
  input `u : ℝ → U → ℝ`. The state transition matrix `Φ(t, t₀)` is LeanForControl's Peano–Baker
  series `LinearSystems.stateTransitionMatrix`; the forced response is LeanForControl's
  `LinearSystems.forcedResponse A B u t₀ x₀ t = Φ(t, t₀) x₀ + ∫_{t₀}^{t} Φ(t, τ) B(τ) u(τ) dτ`
  (Hespanha, *Linear Systems Theory*, Thm. 5.2).
* Generic mathematical support (no `Family`, no definitions); the statements are about arbitrary
  continuous coefficient maps, so they are public foundation.

Source: work-sync theory/T-singular-perturbation.md and theory/T-tikhonov.md use the linear
solution formula for the slow and boundary-layer subsystems; the formula itself is Hespanha,
Ch. 5, Thm. 5.2, as formalized upstream.

Results (each upstream item invokes the upstream theorems; no upstream proof is copied). That the
forced response solves the state equation and starts at `x₀` is upstream and used directly
(`LinearSystems.ContinuousLinearSystem.isTrajectory_forcedResponse` at the system `(A, B, 0, 0)`,
`LinearSystems.variationOfConstants_self`).
* `eq_forcedResponse_of_isIntegralCurveOn`: every solution on the segment between `t₀` and `t₁`
  (a Mathlib integral curve, one-sided at the endpoints) with `x(t₀) = x₀` equals the forced
  response there (upstream `IsIntegralCurveOn.isIntegralSolution`,
  `LinearSystems.isIntegralSolution_forcedResponse`, `LinearSystems.continuousOn_forcedResponse`
  and the uniqueness theorem `LinearSystems.variationOfConstants_unique`).
* `eq_variationOfConstants_of_hasDerivAt`: the variation-of-constants formula for every global
  solution, written out with `Φ`.
* `stm_hasDerivAt`: `∂_t Φ(t, s) = A(t) Φ(t, s)` at every `t ∈ ℝ` (a fundamental matrix on all of
  `ℝ`; upstream `LinearSystems.hasDerivAt_stateTransitionMatrix` holds on open segments `(s, t₁)`,
  the anchor is moved with `stateTransitionMatrix_comp`, `stateTransitionMatrix_comp_of_mem`,
  `stateTransitionMatrix_inv`); with `Φ(s, s) = I` (upstream `stateTransitionMatrix_self`) it
  discharges the fundamental-matrix hypotheses of `theorem/LinearAlgebra/LyapunovODE.lean`.
* `zoh_exact` (proved directly, not an upstream wrapper): exact zero-order-hold sampling of
  `ẋ = A x + c` with constant `c` on a Banach space over one period,
  `x(T) = e^{TA} x(0) + ∫₀ᵀ e^{σA} c dσ` (operator exponential; used by the predictive
  machine-control note theory/T-predictive-machine-control.md §1.1).

The only additional step is the compactness bound `‖A s‖ ≤ M` on the segment (operator `L∞`
norm, `Matrix.Norms.Operator`, the norm of the upstream track) required by the upstream
hypotheses.

The library has one LTV transition matrix: `Periodic.transition A t s`
(`theorem/Periodic/Transition.lean`, monodromy and Floquet multipliers of periodic systems) is an
abbreviation of the Peano–Baker `LinearSystems.stateTransitionMatrix A t s` used here.

Dependency note: LeanForControl's `LinearSystems/Solutions/CtsLTV.lean` did not build against the
pinned Mathlib; `dependencies/LeanForControl-4.34.1.patch` contains the minimal compatibility diff
(three proof-local changes, no statement changes) and `dependencies/LeanForControl.lean` imports
the module.
-/

noncomputable section
namespace powerlib.Dynamics
open Matrix Set
open scoped Matrix.Norms.Operator

variable {X U : Type*} [Fintype X] [DecidableEq X] [Fintype U]

/-- Every solution of `ẋ = A(t) x + B(t) u(t)` on the segment between `t₀` and `t₁` with
`x(t₀) = x₀` is the forced response there. -/
@[tmio T, powerlib_foundation] theorem eq_forcedResponse_of_isIntegralCurveOn {A : ℝ → Matrix X X ℝ}
    {B : ℝ → Matrix X U ℝ} {u : ℝ → U → ℝ} (hA : Continuous A) (hB : Continuous B)
    (hu : Continuous u) {t₀ t₁ : ℝ} {x₀ : X → ℝ} {x : ℝ → X → ℝ}
    (hx : IsIntegralCurveOn x (fun s v => A s *ᵥ v + B s *ᵥ u s) (uIcc t₀ t₁))
    (h0 : x t₀ = x₀) :
    ∀ t ∈ uIcc t₀ t₁, x t = LinearSystems.forcedResponse A B u t₀ x₀ t := by
  obtain ⟨M, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn (f := A)
    (s := uIcc t₀ t₁) hA.continuousOn
  have hxc : ContinuousOn x (uIcc t₀ t₁) := hx.continuousOn
  have hFx : ContinuousOn (fun s => A s *ᵥ x s + B s *ᵥ u s) (uIcc t₀ t₁) :=
    ((continuous_fst.matrix_mulVec continuous_snd).comp_continuousOn
      (hA.continuousOn.prodMk hxc)).add (hB.matrix_mulVec hu).continuousOn
  have hsol := hx.isIntegralSolution hFx
  rw [h0] at hsol
  exact LinearSystems.variationOfConstants_unique hA hB hu hM hsol
    (LinearSystems.isIntegralSolution_forcedResponse hA hB hu hM x₀) hxc
    (LinearSystems.continuousOn_forcedResponse hA hB hu hM x₀)

/-- **Variation of constants.** Every global solution of `ẋ = A(t) x + B(t) u(t)` satisfies
`x(t) = Φ(t, t₀) x(t₀) + ∫_{t₀}^{t} Φ(t, τ) B(τ) u(τ) dτ` for all `t`. -/
@[tmio T, powerlib_foundation] theorem eq_variationOfConstants_of_hasDerivAt {A : ℝ → Matrix X X ℝ}
    {B : ℝ → Matrix X U ℝ} {u : ℝ → U → ℝ} (hA : Continuous A) (hB : Continuous B)
    (hu : Continuous u) {x : ℝ → X → ℝ} (hx : ∀ t, HasDerivAt x (A t *ᵥ x t + B t *ᵥ u t) t)
    (t₀ t : ℝ) :
    x t = LinearSystems.stateTransitionMatrix A t t₀ *ᵥ x t₀ +
      ∫ τ in t₀..t, LinearSystems.stateTransitionMatrix A t τ *ᵥ (B τ *ᵥ u τ) :=
  eq_forcedResponse_of_isIntegralCurveOn hA hB hu (t₁ := t)
    (fun s _ => (hx s).hasDerivWithinAt) rfl t right_mem_uIcc

/-! ## The state-transition matrix as a fundamental matrix on `ℝ` -/

/-- A bound for `‖A‖` (operator norm, as in LeanForControl's Peano–Baker theory) on a segment. -/
@[tmio T, powerlib_foundation] private lemma exists_opNorm_bound {A : ℝ → Matrix X X ℝ}
    (hA : Continuous A) (a b : ℝ) : ∃ M, ∀ r ∈ uIcc a b, ‖A r‖ ≤ M :=
  isCompact_uIcc.exists_bound_of_continuousOn hA.continuousOn

/-- `Φ(s, a) Φ(a, s) = I` for LeanForControl's state-transition matrix. -/
@[tmio T, powerlib_foundation] private lemma stm_mul_inv {A : ℝ → Matrix X X ℝ}
    (hA : Continuous A) (s a : ℝ) :
    LinearSystems.stateTransitionMatrix A s a * LinearSystems.stateTransitionMatrix A a s = 1 := by
  obtain ⟨M, hM⟩ := exists_opNorm_bound hA a s
  obtain ⟨hunit, hinv⟩ := LinearSystems.stateTransitionMatrix_inv hA hM
  rw [← hinv]
  exact mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hunit)

/-- `∂_t Φ(t, s) = A(t) Φ(t, s)` at every `t` (including `t = s`), for continuous `A`: the
Peano–Baker state-transition matrix is a fundamental matrix on all of `ℝ`. The upstream theorem
(`LinearSystems.hasDerivAt_stateTransitionMatrix`) gives the derivative on open segments
`t ∈ (s, t₁)`; at `t = s` the anchor is moved with the upstream composition laws. -/
@[tmio T, powerlib_foundation] theorem stm_hasDerivAt {A : ℝ → Matrix X X ℝ} (hA : Continuous A)
    (t s : ℝ) :
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

/-! ## Exact zero-order-hold sampling -/

section ZOH

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Exact ZOH discretization.** If `ẋ = A x + c` with `c` constant on `[0, T]` (input held by
a zero-order hold), then `x(T) = e^{TA} x(0) + ∫₀ᵀ e^{σA} c dσ`. -/
@[tmio T, powerlib_foundation] theorem zoh_exact (A : E →L[ℝ] E) (c : E) (x : ℝ → E) (T : ℝ)
    (hx : ∀ t ∈ Set.uIcc 0 T, HasDerivAt x (A (x t) + c) t) :
    x T = NormedSpace.exp (T • A) (x 0) +
      ∫ σ in (0 : ℝ)..T, NormedSpace.exp (σ • A) c := by
  -- g(t) = e^{-tA} x(t) has derivative e^{-tA} c.
  have hg : ∀ t ∈ Set.uIcc 0 T, HasDerivAt (fun s => NormedSpace.exp (s • (-A)) (x s))
      (NormedSpace.exp (t • (-A)) c) t := by
    intro t ht
    have he := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) t
    have h := he.clm_apply (hx t ht)
    convert h using 1
    simp only [mul_apply_eq_comp, _root_.neg_apply, map_add, map_neg]
    abel
  have hexp : Continuous fun s : ℝ => NormedSpace.exp (s • (-A)) :=
    continuous_iff_continuousAt.2 fun s =>
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) s).continuousAt
  have hcont : Continuous fun s : ℝ => NormedSpace.exp (s • (-A)) c :=
    hexp.clm_apply continuous_const
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hg
    (hcont.intervalIntegrable 0 T)
  simp only [zero_smul, NormedSpace.exp_zero, one_apply_eq_self] at hint
  have hrad : ∀ y : E →L[ℝ] E,
      y ∈ Metric.eball (0 : E →L[ℝ] E) (NormedSpace.expSeries ℝ (E →L[ℝ] E)).radius := by
    intro y
    rw [NormedSpace.expSeries_radius_eq_top]
    exact edist_lt_top _ _
  -- multiply by e^{TA}
  have hcomm : ∀ s : ℝ, NormedSpace.exp (T • A) * NormedSpace.exp (s • (-A)) =
      NormedSpace.exp ((T - s) • A) := by
    intro s
    have hc : Commute (T • A) (s • (-A)) :=
      ((Commute.refl A).neg_right.smul_left T).smul_right s
    rw [← NormedSpace.exp_add_of_commute_of_mem_ball hc (hrad _) (hrad _)]
    congr 1
    rw [smul_neg, sub_smul]
    abel
  have hinv : NormedSpace.exp (T • A) (NormedSpace.exp (T • (-A)) (x T)) = x T := by
    rw [← mul_apply_eq_comp, hcomm, sub_self, zero_smul, NormedSpace.exp_zero,
      one_apply_eq_self]
  have hxT : x T = NormedSpace.exp (T • A) (x 0) +
      NormedSpace.exp (T • A) (∫ s in (0 : ℝ)..T, NormedSpace.exp (s • (-A)) c) := by
    rw [hint, map_sub, hinv]
    abel
  rw [hxT, ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hcont.intervalIntegrable 0 T)]
  congr 1
  have h1 : ∫ s in (0 : ℝ)..T, NormedSpace.exp (T • A) (NormedSpace.exp (s • (-A)) c) =
      ∫ s in (0 : ℝ)..T, NormedSpace.exp ((T - s) • A) c := by
    congr 1
    funext s
    rw [← mul_apply_eq_comp, hcomm]
  rw [h1, intervalIntegral.integral_comp_sub_left (fun σ => NormedSpace.exp (σ • A) c) T]
  simp

end ZOH

end powerlib.Dynamics
