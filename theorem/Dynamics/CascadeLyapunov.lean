import theorem.Dynamics.Basin

/-! # Local strict Lyapunov functions on a ball

**Model boundary.** Generic: an autonomous continuous-time field `f : ℝⁿ → ℝⁿ` on
`Dynamics.State n = EuclideanSpace ℝ (Fin n)` that coincides, on a ball around the point `x₀`,
with a globally `C¹` field `g`; `f` itself need not be continuous elsewhere (the case of a
physical field with a `1 / V` term regularized away from `V = 0`). No input, delay, switching or
time variation. Solutions are `IsIntegralCurveOn` curves, `V̇ x = fderiv ℝ V x (f x)`.

**Results.**
* `localAsymptoticStable_of_strictLyapunov_ball`: a `C¹` function `W` vanishing at `x₀`,
  positive on the punctured ball `0 < ‖x − x₀‖ < r` and strictly decreasing along `f` there
  makes `x₀` locally asymptotically stable for `f`. Unlike LeanForControl's
  `lyapunov_local_asymptotic_stable` (`IsStrictLocalLyapunovFunction`), no global sublevel set of
  `W` has to be compact and `f` need not be globally continuous: this is the form needed for a
  composite Lyapunov function (a cascade energy plus an averaging correction plus a quadratic
  form on the slaved coordinates) that is only valid near the point.
  The proof: Lyapunov stability from LeanForControl's `lyapunov_stable`; a compact sublevel set
  `{x ∈ B(x₀, r/2) | W x ≤ c}` below the minimum of `W` on the sphere is positively invariant
  (`isPositivelyInvariant_sublevel_of_isOpen`), and LaSalle's principle for the `C¹` field `g`
  (`regionOfAttraction_of_lasalle`) with the strict decrease gives convergence; solutions of `f`
  starting in it stay in it, where they are solutions of `g`.

Family and connection conclusions: none; this is a generic implication about an arbitrary field
and function (foundation).

Source: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.1 (local form); infrastructure for
work-sync `projects/vsc-parametric-oscillation` (four-state GFL weak focus).
-/

noncomputable section
namespace powerlib.Dynamics
open Set Filter Topology Metric
variable {n : ℕ}
local notation "ℝⁿ" => State n

/-- **Local strict Lyapunov theorem on a ball.** If `f` agrees on the ball `‖x − x₀‖ < r` with a
globally `C¹` field `g`, and a `C¹` function `W` with `W x₀ = 0` is positive and strictly
decreasing along `f` on the punctured ball, then `x₀` is locally asymptotically stable for `f`. -/
@[powerlib_foundation] theorem localAsymptoticStable_of_strictLyapunov_ball
    {f g : ℝⁿ → ℝⁿ} {W : ℝⁿ → ℝ} {x₀ : ℝⁿ} {r : ℝ} (hn : 0 < n) (hr : 0 < r)
    (hg : ContDiff ℝ 1 g) (hfg : ∀ x, ‖x - x₀‖ < r → f x = g x)
    (hW : ContDiff ℝ 1 W) (hW0 : W x₀ = 0)
    (hpos : ∀ x, ‖x - x₀‖ < r → x ≠ x₀ → 0 < W x)
    (hLie : ∀ x, ‖x - x₀‖ < r → x ≠ x₀ → fderiv ℝ W x (f x) < 0) :
    LocalAsymptoticStable f x₀ := by
  have hWd : Differentiable ℝ W := hW.differentiable (by norm_num)
  have hball : ∀ {ρ : ℝ} {x : ℝⁿ}, x ∈ ball x₀ ρ → ‖x - x₀‖ < ρ := fun hx => by
    rwa [mem_ball, dist_eq_norm] at hx
  -- `x₀` is a local minimum of `W`, so `W'(x₀) = 0` and `W` does not increase on the ball
  have hmin : IsLocalMin W x₀ := by
    filter_upwards [ball_mem_nhds x₀ hr] with x hx
    rcases eq_or_ne x x₀ with rfl | hne
    · exact le_rfl
    · rw [hW0]; exact (hpos x (hball hx) hne).le
  have hd0 : fderiv ℝ W x₀ = 0 := hmin.fderiv_eq_zero
  have hle : ∀ x, ‖x - x₀‖ < r → fderiv ℝ W x (f x) ≤ 0 := by
    intro x hx
    rcases eq_or_ne x x₀ with rfl | hne
    · rw [hd0]; simp
    · exact (hLie x hx hne).le
  have hLS : LyapunovStable f x₀ := lyapunov_stable hn
    ⟨isOpen_ball, mem_ball_self hr, hWd.continuous, hWd, hW0,
      fun x hx hne => hpos x (hball hx) hne, fun x hx => hle x (hball hx)⟩
  refine ⟨hLS, ?_⟩
  -- the minimum of `W` on the sphere of radius `r / 2`
  have hρ0 : 0 < r / 2 := by positivity
  have hsph : (sphere x₀ (r / 2)).Nonempty := by
    refine ⟨x₀ + EuclideanSpace.single (⟨0, hn⟩ : Fin n) (r / 2), ?_⟩
    rw [mem_sphere, dist_eq_norm]
    simp [PiLp.norm_single]
    exact hr.le
  obtain ⟨xm, hxm, hxmin⟩ := (isCompact_sphere x₀ (r / 2)).exists_isMinOn hsph
    hWd.continuous.continuousOn
  have hxm' : ‖xm - x₀‖ = r / 2 := by rwa [mem_sphere, dist_eq_norm] at hxm
  have hm : 0 < W xm := hpos xm (by rw [hxm']; linarith) fun h => by
    rw [h, sub_self, norm_zero] at hxm'; linarith
  set c := W xm / 2 with hc
  have hc0 : 0 < c := by positivity
  set Ω := {x ∈ ball x₀ (r / 2) | W x ≤ c} with hΩ
  have hΩeq : Ω = closedBall x₀ (r / 2) ∩ {x | W x ≤ c} := by
    ext x
    constructor
    · rintro ⟨hx, hcx⟩
      exact ⟨ball_subset_closedBall hx, hcx⟩
    · rintro ⟨hx, hcx⟩
      refine ⟨?_, hcx⟩
      rcases (mem_closedBall.mp hx).lt_or_eq with h | h
      · exact mem_ball.mpr h
      · have : W xm ≤ W x := hxmin (mem_sphere.mpr h)
        have : W x ≤ c := hcx
        linarith
  have hΩc : IsCompact Ω := by
    rw [hΩeq]
    exact (isCompact_closedBall x₀ (r / 2)).inter_right
      (isClosed_le hWd.continuous continuous_const)
  have hin : ∀ x ∈ ball x₀ (r / 2), ‖x - x₀‖ < r := fun x hx => by
    have := hball hx; linarith
  have hgf : ∀ x ∈ ball x₀ (r / 2), g x = f x := fun x hx => (hfg x (hin x hx)).symm
  have hΩinv_f : IsPositivelyInvariant Ω f :=
    isPositivelyInvariant_sublevel_of_isOpen isOpen_ball hWd (fun x hx => hle x (hin x hx))
      hΩc.isClosed
  have hΩinv_g : IsPositivelyInvariant Ω g :=
    isPositivelyInvariant_sublevel_of_isOpen isOpen_ball hWd
      (fun x hx => by rw [hgf x hx]; exact hle x (hin x hx)) hΩc.isClosed
  have hroa := regionOfAttraction_of_lasalle (x_eq := x₀) hΩc hΩinv_g hg hW
    (fun x hx => by rw [hgf x hx.1]; exact hle x (hin x hx.1)) (by
      intro N hN _ x hx
      obtain ⟨hxΩ, hx0⟩ := hN hx
      by_contra hne
      have := hLie x (hin x hxΩ.1) hne
      rw [← hgf x hxΩ.1] at this
      exact absurd hx0 this.ne)
  -- a ball inside `Ω`
  obtain ⟨δ, hδ, hδW⟩ := Metric.continuousAt_iff.mp (hWd.continuous.continuousAt (x := x₀)) c hc0
  refine ⟨min δ (r / 2), lt_min hδ hρ0, fun t₀ φ hφ hφ0 => ?_⟩
  have hφ0Ω : φ t₀ ∈ Ω := by
    refine ⟨mem_ball.mpr (by rw [dist_eq_norm]; exact hφ0.trans_le (min_le_right _ _)), ?_⟩
    have h := hδW (x := φ t₀) (by rw [dist_eq_norm]; exact hφ0.trans_le (min_le_left _ _))
    rw [Real.dist_eq, hW0, sub_zero] at h
    exact (abs_lt.mp h).2.le
  have hstay : ∀ t ∈ Ici t₀, φ t ∈ Ω := fun t ht =>
    hΩinv_f t₀ t φ (hφ.mono Icc_subset_Ici_self) hφ0Ω t ⟨ht, le_rfl⟩
  have hφg : IsIntegralCurveOn φ (fun _ x => g x) (Ici t₀) :=
    isIntegralCurveOn_of_eq_on_curve hφ fun t ht => (hgf _ (hstay t ht).1).symm
  exact RegionOfAttraction.tendsto hroa hφg hφ0Ω

end powerlib.Dynamics
