import theorem.Dynamics.LaSalle.Basin

/-! # Local asymptotic stability at degenerate minima (foundation)

At a degenerate minimum of an energy (a singular Hessian), the linearization decides nothing and a
strict Lyapunov function is not available: the energy only satisfies `V̇ ≤ 0`. Asymptotic stability
then follows from LaSalle's invariance principle once no solution segment can stay in
`{V̇ = 0}` near the point unless it starts there.

Scope.
* Autonomous continuous-time ODE `ẋ = f x` on `Dynamics.State n = EuclideanSpace ℝ (Fin n)` with
  a `C¹` field supplied by the caller; no input, delay, switching or time variation.
  `V̇ x = fderiv ℝ V x (f x)`.
* Nothing here describes a physical system: every statement is a generic implication about an
  arbitrary field and function, a foundation result. No model family is defined or fixed here;
  `theorem/Dynamics/Mechanical.lean` applies the criterion to damped mechanical systems
  (`Mechanical.localAsymptoticStable_of_strictMin`), which `theorem/Network/Swing/Degenerate.lean`
  uses inside its connection proofs.

Source: LaSalle's invariance principle (Khalil, *Nonlinear Systems*, 3rd ed., Theorem 4.4 and
Corollary 4.1) and Lyapunov's stability theorem (Theorem 4.1).

Results.
* `localAsymptoticStable_of_lasalle_ball`: `f(x*) = 0`, a `C¹` function `W` with `W(x*) = 0`,
  `W > 0` on a punctured ball, `Ẇ ≤ 0` on the ball, and every solution segment of positive length
  that stays in the ball inside `{Ẇ = 0}` starts at `x*` ⇒ local asymptotic stability. Lyapunov
  stability comes from LeanForControl's `lyapunov_stable` on the ball; attraction from LaSalle's
  principle for `C¹` fields (`regionOfAttraction_of_lasalle_sublevel`,
  `lasalle_condition_of_trajectories`, `theorem/Dynamics/LaSalle/Basin.lean`) on a sublevel set
  inside the ball built from the minimum of `W` on a compact annulus. No global compact sublevel
  set and no global Lipschitz bound are required.
-/

noncomputable section
namespace powerlib.Dynamics.LaSalle
open Set Filter Topology Metric

variable {n : ℕ}
local notation "ℝⁿ" => State n

/-- **Local asymptotic stability by LaSalle on a ball.** -/
@[powerlib_foundation] theorem localAsymptoticStable_of_lasalle_ball (hn : 0 < n)
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {W : ℝⁿ → ℝ} {r : ℝ} (hf : ContDiff ℝ 1 f) (hfx : f x_eq = 0)
    (hW : ContDiff ℝ 1 W) (hW0 : W x_eq = 0) (hr : 0 < r)
    (hpos : ∀ x, ‖x - x_eq‖ < r → x ≠ x_eq → 0 < W x)
    (hLie : ∀ x, ‖x - x_eq‖ < r → fderiv ℝ W x (f x) ≤ 0)
    (hstay : ∀ (T : ℝ) (φ : ℝ → ℝⁿ), 0 < T → IsTrajectoryOn φ f 0 T →
      (∀ t ∈ Icc 0 T, ‖φ t - x_eq‖ < r ∧ fderiv ℝ W (φ t) (f (φ t)) = 0) → φ 0 = x_eq) :
    LocalAsymptoticStable f x_eq := by
  have hWd : Differentiable ℝ W := hW.differentiable one_ne_zero
  have hLS : LyapunovStable f x_eq := lyapunov_stable hn
    ⟨isOpen_ball, mem_ball_self hr, hW.continuous, hWd, hW0,
      fun x hx hne => hpos x (by rwa [mem_ball, dist_eq_norm] at hx) hne,
      fun x hx => hLie x (by rwa [mem_ball, dist_eq_norm] at hx)⟩
  refine ⟨hLS, ?_⟩
  -- the minimum of `W` on the compact annulus `r/4 ≤ ‖x − x*‖ ≤ r/2`
  set K := {x : ℝⁿ | r / 4 ≤ ‖x - x_eq‖ ∧ ‖x - x_eq‖ ≤ r / 2} with hKdef
  have hKc : IsCompact K := by
    refine (isCompact_closedBall x_eq (r / 2)).of_isClosed_subset ?_ fun x hx => ?_
    · exact (isClosed_le continuous_const (continuous_norm.comp (continuous_sub_right x_eq))).inter
        (isClosed_le (continuous_norm.comp (continuous_sub_right x_eq)) continuous_const)
    · rw [mem_closedBall, dist_eq_norm]; exact hx.2
  obtain ⟨m, hm, hmK⟩ : ∃ m > 0, ∀ x ∈ K, m ≤ W x := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, fun x hx => by rw [hKe] at hx; exact hx.elim⟩
    · obtain ⟨x₀, hx₀, hmin⟩ := hKc.exists_isMinOn hKne hW.continuous.continuousOn
      have hne : x₀ ≠ x_eq := fun h => by
        have := hx₀.1
        rw [h, sub_self, norm_zero] at this
        linarith
      exact ⟨W x₀, hpos x₀ (by linarith [hx₀.2]) hne, fun x hx => hmin hx⟩
  set c := m / 2 with hc
  set Ω := {x ∈ ball x_eq (r / 2) | W x ≤ c} with hΩdef
  have hΩsub : Ω ⊆ closedBall x_eq (r / 4) := by
    rintro x ⟨hx, hWx⟩
    rw [mem_closedBall, dist_eq_norm]
    rw [mem_ball, dist_eq_norm] at hx
    by_contra hlt
    push Not at hlt
    have := hmK x ⟨hlt.le, hx.le⟩
    linarith
  have hΩc : IsCompact Ω := by
    have hΩeq : Ω = closedBall x_eq (r / 4) ∩ {x | W x ≤ c} := by
      ext x
      constructor
      · intro hx
        exact ⟨hΩsub hx, hx.2⟩
      · rintro ⟨hx, hWx⟩
        refine ⟨?_, hWx⟩
        rw [mem_closedBall] at hx
        rw [mem_ball]
        linarith
    rw [hΩeq]
    exact (isCompact_closedBall _ _).inter_right (isClosed_le hW.continuous continuous_const)
  have hroa := regionOfAttraction_of_lasalle_sublevel (f := f) (V := W)
    (W := ball x_eq (r / 2)) (c := c) (x_eq := x_eq) isOpen_ball hf hW
    (fun x hx => by
      rw [mem_ball, dist_eq_norm] at hx
      exact hLie x (by linarith))
    hΩc (lasalle_condition_of_trajectories hf fun T φ hT hφ hin => hstay T φ hT hφ
      fun t ht => by
        have hx := hin t ht
        rw [lieDerivZeroSet_def] at hx
        have hb := hx.1.1
        rw [mem_ball, dist_eq_norm] at hb
        exact ⟨by linarith, hx.2⟩)
  obtain ⟨δ, hδ, hδW⟩ := Metric.continuousAt_iff.mp hW.continuous.continuousAt c (by positivity)
  refine ⟨min δ (r / 2), lt_min hδ (by linarith), fun t₀ φ hφ hφ0 =>
    RegionOfAttraction.tendsto hroa hφ ?_⟩
  have h1 : dist (φ t₀) x_eq < δ := by rw [dist_eq_norm]; exact hφ0.trans_le (min_le_left _ _)
  have h2 := hδW h1
  rw [Real.dist_eq, hW0, sub_zero] at h2
  refine ⟨?_, (le_abs_self _).trans h2.le⟩
  rw [mem_ball, dist_eq_norm]
  exact hφ0.trans_le (min_le_right _ _)

end powerlib.Dynamics.LaSalle
