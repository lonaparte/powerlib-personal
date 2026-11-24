import Mathlib.Analysis.ODE.ExistUnique
import theorem.Dynamics.CenterManifoldDefs
import theorem.Dynamics.Lyapunov
import theorem.Dynamics.Degenerate.PlanarFocus
import theorem.Dynamics.CenterManifoldApprox
import theorem.Dynamics.CenterReductionHopf

/-! # Reduction to a centre manifold (foundation)

For a field `ẋ = A x + f x` on `ℝⁿ` and a locally invariant Lipschitz graph `x = u + h(u)` over
the range of a projection `P` commuting with `A` (a centre manifold, whose existence is
`theorem/Dynamics/CenterManifold.lean`), the dynamics on the graph is the reduced field
`u̇ = g(u) = PAu + Pf(u + h u)`: reduced solutions lift to full solutions, instability of the
reduced field at `0` is instability of the full field, the quadratic part of the graph is fixed
by the homological equation, and the reduced field has an explicit cubic expansion, so the planar
weak-focus law decides instability of the full field.

Scope.
* Generic: `State n = ℝⁿ` (the expansion and homological laws on any real normed space `E`), `A`,
  `P` with `P² = P`, `AP = PA` (`IsCommutingProjection`), `f` of class `C¹`, a graph map `h`
  (`IsGraphMap`: `h = h ∘ P`, `P h = 0`, `h 0 = 0`) that is `K`-Lipschitz, and local invariance
  of its graph as a hypothesis (solutions of the full field starting on the graph stay on it
  while they stay in a ball of radius `ρ`; the form fixed in
  `theorem/Dynamics/CenterManifoldDefs.lean`). The reduced field is read on `range P`
  (`reducedField`) or in linear coordinates `ι : ℝᵐ → ℝⁿ`, `π : ℝⁿ → ℝᵐ` of `range P` (`IsChart`,
  `chartField`); stability notions are LeanForControl's, read on `ℝᵐ`. Expansions are exact
  asymptotic statements (`IsBigO`, `IsLittleO` as `u → 0` in `range P`). The dichotomy is
  `‖e^{tA}(1 − P)‖ ≤ K e^{−βt}`, `‖e^{−tA}P‖ ≤ K e^{εt}` (`t ≥ 0`), `2ε < β`.
* Only instability is transferred; the stability half of the reduction principle (attraction of
  the stable directions) is not proved here.
* Nothing here describes a physical system (foundation).

Source: Carr, *Applications of Centre Manifold Theory* (1981), §2.4 (Theorem 2: the reduction
principle; its instability half) and §2.5 (Theorem 3 and the computation of the quadratic part);
Kelley (1967); Vanderbauwhede, "Centre manifolds, normal forms and elementary bifurcations"
(1989), §2; Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §5.1 (Theorem 5.2),
§5.4 (the homological equation of the quadratic part and the projection formula).

Results.
* Tools: `eqOn_of_lipschitzOnWith` (uniqueness of solution segments in a set where the field is
  Lipschitz), `exists_lipschitzOnWith_closedBall`, `exists_lipschitzOnWith_chartField` (the chart
  field of a `C¹` nonlinearity and a Lipschitz graph is Lipschitz on a ball),
  `exists_trajectory_of_lyapunovStable` (a Lyapunov stable equilibrium of a `C¹` field has
  solution segments through every nearby state), `reducedField_eq_chartField`,
  `proj_fullField_of_mem_graph`, `IsChart.isTrajectoryOn_ι`.
* (1) Lifting: `lift_isTrajectoryOn` — there is `r > 0` such that every solution segment of the
  reduced field in `range P` that stays in the ball of radius `r` lifts to the solution segment
  `u + h(u)` of the full field; `chart_lift_isTrajectoryOn`, the same in coordinates.
* (2) Instability transfer: `unstable_of_unstable_chartField` — if `0` is unstable for the
  reduced field in coordinates, it is unstable for the full field.
* (3) The homological equation (`IsHomological`:
  `H₀(u, PAu) + H₀(PAu, u) = (1 − P)A H₀(u, u) + (1 − P)Q(u, u)` on `range P`, i.e.
  `((1 − P)A ∘ H₀ − H₀ ∘ (PA ⊗ 1 + 1 ⊗ PA))(u, u) = −(1 − P)Q(u, u)`):
  `isOrder_invarianceDefect_quadGraph` (a solution makes the quadratic graph `quadGraph P H₀`
  an approximate centre manifold: invariance defect `O(‖u‖³)` when `f = Q + O(‖x‖³)`, Carr's
  hypothesis with `q = 3`); `HasQuadraticPart.apply_eq` (the quadratic part of a graph is unique
  on `range P`); `HasQuadraticPart.apply_eq_of_homological` (with Carr's approximation property
  the quadratic part of a centre manifold is the solution of the homological equation: `H` is
  determined by `A`, `P` and `Q = D²f(0)/2`). Solvability under the dichotomy:
  `homological_eq_zero` (the homological operator is injective on bilinear maps
  `range P × range P → range (1 − P)`), `IsHomological.apply_eq` (uniqueness of the quadratic
  form), `homologicalOp`, `rangeProj`, `bilinOnRange`, `existsUnique_homological` (finite
  dimension: unique solvability for every right-hand side), `exists_isHomological`.
* (4) Expansion of the reduced field: `reducedField_expansion`
  (`g(u) = PAu + P[Q(u, u) + Q(u, H(u, u)) + Q(H(u, u), u) + C(u, u, u)] + o(‖u‖³)`, i.e.
  `2Q(u, H(u, u))` for symmetric `Q`), `chartField_expansion` (the same in coordinates, the
  hypothesis form of the planar laws); helpers `norm_pow_isLittleO`, `isBigO_bilin`,
  `isBigO_trilin`, `trilin_add_zero`, `trilin_add_one`, `trilin_add_two`.
  `unstable_of_reduced_l1_pos`: with a planar `range P`, `l₁ > 0` of the reduced linear,
  quadratic and cubic parts (`Dynamics.Degenerate.PlanarFocus.l1`) gives instability of the full
  field. The identity of this reduced `l₁` with Kuznetsov's projection formula
  `NormalForm.LyapunovCoefficient.firstLyapunov` of the full field is
  `IsCritical.l1_reduced_eq_firstLyapunov` (`theorem/Dynamics/CenterReductionHopf.lean`).
* (5) End to end, with `theorem/Dynamics/CenterManifoldApprox.lean`:
  `exists_centerManifold_hasQuadraticPart` (under the dichotomy with `3ε < β` there is a
  locally invariant Lipschitz centre manifold whose quadratic part is the solution of the
  homological equation), `exists_isHomological_of_dichotomy` (that solution exists),
  `unstable_of_dichotomy_reduced_l1_pos` (the planar `l₁` of the reduced linear, quadratic and
  cubic parts, positive, gives instability of the full field in any dimension).
* (6) `unstable_of_firstLyapunov_pos`: for a critical pair `(q, p)`, the spectral projection of
  the critical chart with the centre–stable dichotomy and `A`, `2iω − A` invertible,
  `firstLyapunov (fullField A f) 0 ω q p > 0` gives instability: the projection formula decides
  instability in any dimension.
-/

noncomputable section
namespace powerlib.Dynamics.CenterManifold

open Set Filter Topology Metric

/-! ## Uniqueness, Lipschitz bounds, existence -/

section Tools

variable {n m : ℕ}

/-- Uniqueness of solution segments that stay in a set where the field is Lipschitz. -/
@[tmio T, powerlib_foundation] theorem eqOn_of_lipschitzOnWith {G : State n → State n}
    {L : NNReal} {S : Set (State n)} (hG : LipschitzOnWith L G S) {u v : ℝ → State n}
    {t₀ t₁ : ℝ} (hu : IsTrajectoryOn u G t₀ t₁) (hv : IsTrajectoryOn v G t₀ t₁)
    (huS : ∀ t ∈ Icc t₀ t₁, u t ∈ S) (hvS : ∀ t ∈ Icc t₀ t₁, v t ∈ S) (h0 : u t₀ = v t₀) :
    EqOn u v (Icc t₀ t₁) :=
  ODE_solution_unique_of_mem_Icc_right (v := fun _ => G) (s := fun _ => S) (fun _ _ => hG)
    hu.continuousOn
    (fun t ht => (hu t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => huS t (Ico_subset_Icc_self ht)) hv.continuousOn
    (fun t ht => (hv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => hvS t (Ico_subset_Icc_self ht)) h0

/-- A `C¹` map is Lipschitz on a closed ball around `0`. -/
@[tmio T, powerlib_foundation] theorem exists_lipschitzOnWith_closedBall
    {f : State n → State n} (hf : ContDiff ℝ 1 f) :
    ∃ R > 0, ∃ L : NNReal, LipschitzOnWith L f (closedBall 0 R) := by
  obtain ⟨L, t, ht, hL⟩ := (hf.contDiffAt (x := 0)).exists_lipschitzOnWith
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ht
  exact ⟨ε / 2, by positivity, L, hL.mono ((closedBall_subset_ball (by linarith)).trans hball)⟩

/-- The chart field of a nonlinearity that is Lipschitz on the ball of radius `R` and a
`K`-Lipschitz graph map is Lipschitz on the ball of radius `r` when `(1 + K)‖ι‖ r ≤ R`. -/
@[tmio T, powerlib_foundation] theorem exists_lipschitzOnWith_chartField
    {A : State n →L[ℝ] State n} {f h : State n → State n} {ι : State m →L[ℝ] State n}
    {π : State n →L[ℝ] State m} {K Lf : NNReal} {R r : ℝ} (hh0 : h 0 = 0)
    (hK : LipschitzWith K h) (hLf : LipschitzOnWith Lf f (closedBall 0 R))
    (hr : (1 + K) * ‖ι‖ * r ≤ R) :
    ∃ L : NNReal, LipschitzOnWith L (chartField A f h ι π) (closedBall 0 r) := by
  set c : ℝ := ‖π‖ * (‖A‖ * ‖ι‖ + Lf * ((1 + K) * ‖ι‖)) with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨Real.toNNReal c, LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_⟩
  rw [Real.coe_toNNReal _ hc0, dist_eq_norm, dist_eq_norm]
  have hlift : ∀ z ∈ closedBall (0 : State m) r, ι z + h (ι z) ∈ closedBall (0 : State n) R := by
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz ⊢
    have h1 : ‖h (ι z)‖ ≤ K * ‖ι z‖ := by simpa [hh0] using hK.norm_sub_le (ι z) 0
    have h2 : ‖ι z‖ ≤ ‖ι‖ * r := (ι.le_opNorm z).trans (by gcongr)
    calc ‖ι z + h (ι z)‖ ≤ ‖ι z‖ + ‖h (ι z)‖ := norm_add_le _ _
      _ ≤ (1 + K) * (‖ι‖ * r) := by nlinarith [norm_nonneg (ι z), K.coe_nonneg]
      _ = (1 + K) * ‖ι‖ * r := by ring
      _ ≤ R := hr
  have hfd : ‖f (ι y + h (ι y)) - f (ι y' + h (ι y'))‖ ≤ Lf * ((1 + K) * ‖ι‖ * ‖y - y'‖) := by
    have := hLf.dist_le_mul _ (hlift y hy) _ (hlift y' hy')
    rw [dist_eq_norm, dist_eq_norm] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ Lf.coe_nonneg)
    have e : ι y + h (ι y) - (ι y' + h (ι y')) = ι (y - y') + (h (ι y) - h (ι y')) := by
      rw [map_sub]; abel
    have hk : ‖h (ι y) - h (ι y')‖ ≤ K * ‖ι (y - y')‖ := by
      rw [map_sub]; exact hK.norm_sub_le _ _
    have hι : ‖ι (y - y')‖ ≤ ‖ι‖ * ‖y - y'‖ := ι.le_opNorm _
    rw [e]
    calc ‖ι (y - y') + (h (ι y) - h (ι y'))‖ ≤ ‖ι (y - y')‖ + K * ‖ι (y - y')‖ :=
          (norm_add_le _ _).trans (by linarith)
      _ = (1 + K) * ‖ι (y - y')‖ := by ring
      _ ≤ (1 + K) * (‖ι‖ * ‖y - y'‖) := by gcongr
      _ = (1 + K) * ‖ι‖ * ‖y - y'‖ := by ring
  have hdiff : chartField A f h ι π y - chartField A f h ι π y' =
      π (A (ι (y - y')) + (f (ι y + h (ι y)) - f (ι y' + h (ι y')))) := by
    simp only [chartField, map_sub, map_add]; abel
  rw [hdiff]
  have hA : ‖A (ι (y - y'))‖ ≤ ‖A‖ * ‖ι‖ * ‖y - y'‖ := by
    calc ‖A (ι (y - y'))‖ ≤ ‖A‖ * ‖ι (y - y')‖ := A.le_opNorm _
      _ ≤ ‖A‖ * (‖ι‖ * ‖y - y'‖) := by gcongr; exact ι.le_opNorm _
      _ = ‖A‖ * ‖ι‖ * ‖y - y'‖ := by ring
  calc ‖π (A (ι (y - y')) + (f (ι y + h (ι y)) - f (ι y' + h (ι y'))))‖
      ≤ ‖π‖ * ‖A (ι (y - y')) + (f (ι y + h (ι y)) - f (ι y' + h (ι y')))‖ := π.le_opNorm _
    _ ≤ ‖π‖ * (‖A‖ * ‖ι‖ * ‖y - y'‖ + Lf * ((1 + K) * ‖ι‖ * ‖y - y'‖)) := by
        gcongr; exact (norm_add_le _ _).trans (add_le_add hA hfd)
    _ = c * ‖y - y'‖ := by rw [hc]; ring

/-- A Lyapunov stable equilibrium `0` of a `C¹` field has, through every state close enough to
`0` and at every initial time, a solution segment on any interval that stays in the ball of
radius `ε`. -/
@[tmio T, powerlib_foundation] theorem exists_trajectory_of_lyapunovStable
    {F : State n → State n} (hF : ContDiff ℝ 1 F) (hLS : LyapunovStable F 0) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ (t₀ t₁ : ℝ) (x₀ : State n), ‖x₀‖ < δ → ∃ φ : ℝ → State n, φ t₀ = x₀ ∧
      IsTrajectoryOn φ F t₀ t₁ ∧ ∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ε := by
  obtain ⟨g, -, ⟨K, hK⟩, hgF⟩ := exists_contDiff_lipschitz_extension hF ε
  obtain ⟨δ, hδ, hb⟩ := hLS (ε / 2) (by positivity)
  refine ⟨min δ ε, lt_min hδ hε, fun t₀ t₁ x₀ hx₀ => ?_⟩
  obtain ⟨φ, hφ0, hφ⟩ := Flow.forwardComplete_of_lipschitzWith hK t₀ x₀
  have hφI : IsIntegralCurveOn φ (fun _ x => g x) (Icc t₀ t₁) := hφ.mono Icc_subset_Ici_self
  have hseg : ∀ s, (∀ τ ∈ Icc t₀ s, ‖φ τ‖ < ε) → IsTrajectoryOn φ F t₀ s := by
    intro s hin
    exact isIntegralCurveOn_of_eq_on_curve (hφ.mono Icc_subset_Ici_self) fun τ hτ =>
      hgF _ (hin τ hτ).le
  have h0 : ‖φ t₀‖ < ε := by rw [hφ0]; exact hx₀.trans_le (min_le_right _ _)
  have hstay : ∀ t ∈ Icc t₀ t₁, ‖φ t - 0‖ < ε := by
    refine forall_norm_sub_lt_of_bootstrap hφI.continuousOn (by simpa using h0) ?_
    intro s hs hin
    have hin' : ∀ τ ∈ Icc t₀ s, ‖φ τ‖ < ε := fun τ hτ => by simpa using hin τ hτ
    have hδ0 : ‖φ t₀ - 0‖ < δ := by
      rw [hφ0, sub_zero]; exact hx₀.trans_le (min_le_left _ _)
    have := hb t₀ s φ (hseg s hin') hδ0 s ⟨hs.1, le_rfl⟩
    rw [sub_zero] at this ⊢
    exact this.le
  have hstay' : ∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ε := fun t ht => by simpa using hstay t ht
  exact ⟨φ, hφ0, hseg t₁ hstay', hstay'⟩

end Tools

/-! ## The reduced field on the graph -/

section Graph

variable {n m : ℕ} {A P : State n →L[ℝ] State n} {f h : State n → State n}

/-- The reduced field is the chart field with the trivial coordinates `ι = 1`, `π = P`. -/
@[tmio T, powerlib_foundation] theorem reducedField_eq_chartField :
    reducedField A P f h = chartField A f h (ContinuousLinearMap.id ℝ (State n)) P := by
  funext u
  simp [reducedField, chartField, map_add]

/-- On the graph, `P` of the full field is the reduced field at `P x`. -/
@[tmio T, powerlib_foundation] theorem proj_fullField_of_mem_graph
    (hP : IsCommutingProjection A P) (hh : IsGraphMap P h) {x : State n}
    (hx : x ∈ graph P h) : P (fullField A f x) = reducedField A P f h (P x) := by
  have hx' : x = P x + h (P x) := hh.eq_lift_of_mem_graph hx
  have hsplit := fullField_lift (f := f) hP hh (hP.idem x)
  rw [← hx'] at hsplit
  rw [hsplit, map_add, normalField, map_add, hP.proj_compl, hP.proj_compl, add_zero, add_zero,
    reducedField, map_add, hP.idem, hP.idem]

/-- A solution segment of the chart field is carried by `ι` to one of the reduced field. -/
@[tmio T, powerlib_foundation] theorem IsChart.isTrajectoryOn_ι {ι : State m →L[ℝ] State n}
    {π : State n →L[ℝ] State m} (hc : IsChart P ι π) {ψ : ℝ → State m} {t₀ t₁ : ℝ}
    (hψ : IsTrajectoryOn ψ (chartField A f h ι π) t₀ t₁) :
    IsTrajectoryOn (fun t => ι (ψ t)) (reducedField A P f h) t₀ t₁ := by
  intro t ht
  have := ι.hasFDerivAt.comp_hasDerivWithinAt t (hψ t ht)
  simpa only [Function.comp_def, hc.ι_chartField] using this

end Graph

/-! ## (1) Reduced solutions lift to full solutions -/

section Lift

variable {n m : ℕ} {A P : State n →L[ℝ] State n} {f h : State n → State n}

/-- **Lifting.** Let the graph of a `K`-Lipschitz graph map `h` be locally invariant for
`ẋ = A x + f x` (`f` of class `C¹`): solutions starting on it stay on it while they stay in the
ball of radius `ρ`. Then there is `r > 0` such that every solution segment `u` of the reduced
field `u̇ = PAu + Pf(u + h u)` with `u(t₀) ∈ range P` that stays in the ball of radius `r` lifts
to the solution segment `u + h(u)` of the full field. -/
@[tmio T, powerlib_foundation] theorem lift_isTrajectoryOn {K : NNReal} {ρ : ℝ}
    (hP : IsCommutingProjection A P) (hh : IsGraphMap P h) (hK : LipschitzWith K h)
    (hf : ContDiff ℝ 1 f) (hρ : 0 < ρ)
    (hinv : ∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
      φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h) :
    ∃ r > 0, ∀ (t₀ t₁ : ℝ) (u : ℝ → State n), IsTrajectoryOn u (reducedField A P f h) t₀ t₁ →
      P (u t₀) = u t₀ → (∀ t ∈ Icc t₀ t₁, ‖u t‖ < r) →
      IsTrajectoryOn (fun t => u t + h (u t)) (fullField A f) t₀ t₁ := by
  obtain ⟨R₀, hR₀, Lf, hLf⟩ := exists_lipschitzOnWith_closedBall hf
  have hK1 : (0 : ℝ) < 1 + K := by positivity
  have hP1 : (0 : ℝ) < ‖P‖ + 1 := by positivity
  set ρ' := min ρ (R₀ / ((1 + K) * (‖P‖ + 1))) with hρ'
  have hρ'0 : 0 < ρ' := lt_min hρ (by positivity)
  set r₁ := (‖P‖ + 1) * ρ' with hr₁
  have hρ'r₁ : ρ' ≤ r₁ := by rw [hr₁]; nlinarith [norm_nonneg P]
  have hr₁R : (1 + K) * ‖ContinuousLinearMap.id ℝ (State n)‖ * r₁ ≤ R₀ := by
    have hid := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := State n)
    have h1 : ρ' * ((1 + K) * (‖P‖ + 1)) ≤ R₀ :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    calc (1 + K) * ‖ContinuousLinearMap.id ℝ (State n)‖ * r₁ ≤ (1 + K) * 1 * r₁ := by
          gcongr
      _ = ρ' * ((1 + K) * (‖P‖ + 1)) := by rw [hr₁]; ring
      _ ≤ R₀ := h1
  obtain ⟨Lg, hLg⟩ := exists_lipschitzOnWith_chartField (A := A) (π := P) hh.map_zero hK hLf hr₁R
  rw [← reducedField_eq_chartField] at hLg
  have hF : ContDiff ℝ 1 (fullField A f) := A.contDiff.add hf
  obtain ⟨g, -, ⟨Kg, hKg⟩, hgF⟩ := exists_contDiff_lipschitz_extension hF ρ'
  refine ⟨ρ' / (2 * (1 + K)), by positivity, fun t₀ t₁ u hu hu0 hur => ?_⟩
  rcases lt_or_ge t₁ t₀ with hlt | hle
  · intro t ht
    exact absurd (ht.1.trans ht.2) (not_le.mpr hlt)
  have hr2 : (1 + K) * (ρ' / (2 * (1 + K))) = ρ' / 2 := by field_simp
  have hliftb : ∀ t ∈ Icc t₀ t₁, ‖u t + h (u t)‖ ≤ ρ' / 2 := fun t ht => by
    rw [← hr2]
    exact (hh.norm_lift_le hK (u t)).trans (by gcongr; exact (hur t ht).le)
  obtain ⟨φ, hφ0, hφ⟩ := Flow.forwardComplete_of_lipschitzWith hKg t₀ (u t₀ + h (u t₀))
  have hseg : ∀ s, (∀ τ ∈ Icc t₀ s, ‖φ τ‖ < ρ') → IsTrajectoryOn φ (fullField A f) t₀ s :=
    fun s hin => isIntegralCurveOn_of_eq_on_curve (hφ.mono Icc_subset_Ici_self) fun τ hτ =>
      hgF _ (hin τ hτ).le
  have hkey : ∀ s, s ≤ t₁ → (∀ τ ∈ Icc t₀ s, ‖φ τ‖ < ρ') →
      ∀ τ ∈ Icc t₀ s, φ τ = u τ + h (u τ) := by
    intro s hs hin
    have htraj := hseg s hin
    have hgr := hinv t₀ s φ htraj (by rw [hφ0]; exact hh.lift_mem_graph hu0)
      fun τ hτ => (hin τ hτ).trans_le (min_le_left _ _)
    have hv : IsTrajectoryOn (fun τ => P (φ τ)) (reducedField A P f h) t₀ s := by
      intro τ hτ
      have := P.hasFDerivAt.comp_hasDerivWithinAt τ (htraj τ hτ)
      simpa only [Function.comp_def, proj_fullField_of_mem_graph hP hh (hgr τ hτ)] using this
    have heq := eqOn_of_lipschitzOnWith hLg (hu.mono (Icc_subset_Icc le_rfl hs)) hv
      (fun τ hτ => by
        rw [mem_closedBall, dist_zero_right]
        exact (hur τ ⟨hτ.1, hτ.2.trans hs⟩).le.trans
          ((div_le_self hρ'0.le (by nlinarith [K.coe_nonneg])).trans hρ'r₁))
      (fun τ hτ => by
        rw [mem_closedBall, dist_zero_right, hr₁]
        calc ‖P (φ τ)‖ ≤ ‖P‖ * ‖φ τ‖ := P.le_opNorm _
          _ ≤ ‖P‖ * ρ' := by gcongr; exact (hin τ hτ).le
          _ ≤ (‖P‖ + 1) * ρ' := by nlinarith)
      (by rw [hφ0, hh.proj_lift hu0])
    intro τ hτ
    have hx := hh.eq_lift_of_mem_graph (hgr τ hτ)
    have hτ' : u τ = P (φ τ) := heq hτ
    rw [hx, hτ']
  have h0 : ‖φ t₀ - 0‖ < ρ' := by
    rw [sub_zero, hφ0]
    exact (hliftb t₀ ⟨le_rfl, hle⟩).trans_lt (by linarith)
  have hstay : ∀ t ∈ Icc t₀ t₁, ‖φ t - 0‖ < ρ' := by
    refine forall_norm_sub_lt_of_bootstrap
      ((hφ.mono Icc_subset_Ici_self).continuousOn) h0 fun s hs hin => ?_
    have hin' : ∀ τ ∈ Icc t₀ s, ‖φ τ‖ < ρ' := fun τ hτ => by simpa using hin τ hτ
    rw [sub_zero, hkey s hs.2 hin' s ⟨hs.1, le_rfl⟩]
    exact hliftb s hs
  have hstay' : ∀ τ ∈ Icc t₀ t₁, ‖φ τ‖ < ρ' := fun τ hτ => by simpa using hstay τ hτ
  have hfin := hkey t₁ le_rfl hstay'
  intro t ht
  have hd := hseg t₁ hstay' t ht
  rw [hfin t ht] at hd
  exact hd.congr_of_mem (fun τ hτ => (hfin τ hτ).symm) ht

/-- **Lifting in coordinates.** The same for solution segments `ψ` of the chart field: `ι ψ +
h(ι ψ)` is a solution segment of the full field while `ψ` stays in the ball of radius `r`. -/
@[tmio T, powerlib_foundation] theorem chart_lift_isTrajectoryOn {K : NNReal} {ρ : ℝ}
    {ι : State m →L[ℝ] State n} {π : State n →L[ℝ] State m}
    (hP : IsCommutingProjection A P) (hh : IsGraphMap P h) (hK : LipschitzWith K h)
    (hc : IsChart P ι π) (hf : ContDiff ℝ 1 f) (hρ : 0 < ρ)
    (hinv : ∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
      φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h) :
    ∃ r > 0, ∀ (t₀ t₁ : ℝ) (ψ : ℝ → State m), IsTrajectoryOn ψ (chartField A f h ι π) t₀ t₁ →
      (∀ t ∈ Icc t₀ t₁, ‖ψ t‖ < r) →
      IsTrajectoryOn (fun t => ι (ψ t) + h (ι (ψ t))) (fullField A f) t₀ t₁ := by
  obtain ⟨r, hr, hlift⟩ := lift_isTrajectoryOn hP hh hK hf hρ hinv
  refine ⟨r / (‖ι‖ + 1), by positivity, fun t₀ t₁ ψ hψ hψr => ?_⟩
  refine hlift t₀ t₁ (fun t => ι (ψ t)) (hc.isTrajectoryOn_ι hψ) (hc.proj_ι _) fun t ht => ?_
  have h1 := hψr t ht
  calc ‖ι (ψ t)‖ ≤ ‖ι‖ * ‖ψ t‖ := ι.le_opNorm _
    _ ≤ (‖ι‖ + 1) * ‖ψ t‖ := by nlinarith [norm_nonneg (ψ t)]
    _ < (‖ι‖ + 1) * (r / (‖ι‖ + 1)) := by gcongr
    _ = r := by field_simp

end Lift

/-! ## (2) Instability of the reduced field is instability of the full field -/

section Instability

variable {n m : ℕ} {A P : State n →L[ℝ] State n} {f h : State n → State n}

/-- **Instability transfer** (the instability half of the reduction principle). Let the graph
of a `K`-Lipschitz graph map `h` be locally invariant for `ẋ = A x + f x` (`f` of class `C¹`).
If `0` is unstable for the reduced field read in linear coordinates `ι, π` of `range P`, then
`0` is unstable for the full field. -/
@[tmio T, powerlib_foundation] theorem unstable_of_unstable_chartField {K : NNReal} {ρ : ℝ}
    {ι : State m →L[ℝ] State n} {π : State n →L[ℝ] State m}
    (hP : IsCommutingProjection A P) (hh : IsGraphMap P h) (hK : LipschitzWith K h)
    (hc : IsChart P ι π) (hf : ContDiff ℝ 1 f) (hρ : 0 < ρ)
    (hinv : ∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
      φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h)
    (hred : Unstable (chartField A f h ι π) 0) : Unstable (fullField A f) 0 := by
  intro hLS
  apply hred
  have hF : ContDiff ℝ 1 (fullField A f) := A.contDiff.add hf
  obtain ⟨R₀, hR₀, Lf, hLf⟩ := exists_lipschitzOnWith_closedBall hf
  have hK1 : (0 : ℝ) < 1 + K := by positivity
  set r₁ := R₀ / ((1 + K) * (‖ι‖ + 1)) with hr₁
  have hr₁0 : 0 < r₁ := by positivity
  have hr₁R : (1 + K) * ‖ι‖ * r₁ ≤ R₀ := by
    have : (1 + K) * ‖ι‖ * r₁ ≤ (1 + K) * (‖ι‖ + 1) * r₁ := by gcongr; linarith
    refine this.trans (le_of_eq ?_)
    rw [hr₁]; field_simp
  obtain ⟨Lg, hLg⟩ := exists_lipschitzOnWith_chartField (A := A) (π := π) hh.map_zero hK hLf
    hr₁R
  have hπh : ∀ z, π (h z) = 0 := fun z => by rw [← hc.π_proj, hh.proj_apply, map_zero]
  intro ε hε
  set ε₁ := min ρ (min r₁ ε) / (2 * (‖π‖ + 1)) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  have hπε : ‖π‖ * ε₁ < min r₁ ε / 2 ∧ ε₁ < ρ := by
    have hm : 0 < min ρ (min r₁ ε) := lt_min hρ (lt_min hr₁0 hε)
    have e1 : (‖π‖ + 1) * ε₁ = min ρ (min r₁ ε) / 2 := by rw [hε₁]; field_simp
    constructor
    · have : ‖π‖ * ε₁ < (‖π‖ + 1) * ε₁ := by nlinarith
      rw [e1] at this
      exact this.trans_le (by linarith [min_le_right ρ (min r₁ ε)])
    · have : ε₁ ≤ (‖π‖ + 1) * ε₁ := by nlinarith [norm_nonneg π]
      rw [e1] at this
      exact this.trans_lt (by linarith [min_le_left ρ (min r₁ ε)])
  obtain ⟨δ₁, hδ₁, hex⟩ := exists_trajectory_of_lyapunovStable hF hLS hε₁0
  refine ⟨min δ₁ r₁ / ((1 + K) * (‖ι‖ + 1)), by positivity, fun t₀ t₁ ψ hψ hψ0 => ?_⟩
  rw [sub_zero] at hψ0
  have hψ0r : ‖ψ t₀‖ < min δ₁ r₁ := by
    refine hψ0.trans_le ?_
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ (1 + K) * (‖ι‖ + 1) := by nlinarith [norm_nonneg ι, K.coe_nonneg]
    nlinarith [lt_min hδ₁ hr₁0]
  set x₀ := ι (ψ t₀) + h (ι (ψ t₀)) with hx₀
  have hx₀b : ‖x₀‖ < δ₁ := by
    have h1 := hh.norm_lift_le hK (ι (ψ t₀))
    have h2 : ‖ι (ψ t₀)‖ ≤ ‖ι‖ * ‖ψ t₀‖ := ι.le_opNorm _
    calc ‖x₀‖ ≤ (1 + K) * ‖ι (ψ t₀)‖ := h1
      _ ≤ (1 + K) * (‖ι‖ * ‖ψ t₀‖) := by gcongr
      _ ≤ (1 + K) * ((‖ι‖ + 1) * ‖ψ t₀‖) := by gcongr; linarith
      _ < (1 + K) * (‖ι‖ + 1) * (min δ₁ r₁ / ((1 + K) * (‖ι‖ + 1))) := by
          rw [← mul_assoc]; gcongr
      _ = min δ₁ r₁ := by field_simp
      _ ≤ δ₁ := min_le_left _ _
  intro t ht
  rw [sub_zero]
  obtain ⟨φ, hφ0, hφ, hφb⟩ := hex t₀ t₁ x₀ hx₀b
  have hgr := hinv t₀ t₁ φ hφ (by rw [hφ0]; exact hh.lift_mem_graph (hc.proj_ι _))
    fun τ hτ => (hφb τ hτ).trans hπε.2
  have hy : IsTrajectoryOn (fun τ => π (φ τ)) (chartField A f h ι π) t₀ t₁ := by
    intro τ hτ
    have := π.hasFDerivAt.comp_hasDerivWithinAt τ (hφ τ hτ)
    simpa only [Function.comp_def, hc.π_fullField_of_mem_graph hP hh (hgr τ hτ)] using this
  have hy0 : π (φ t₀) = ψ t₀ := by rw [hφ0, hx₀, map_add, hc.left_inv, hπh, add_zero]
  have hyb : ∀ τ ∈ Icc t₀ t₁, ‖π (φ τ)‖ < min r₁ ε / 2 := fun τ hτ =>
    calc ‖π (φ τ)‖ ≤ ‖π‖ * ‖φ τ‖ := π.le_opNorm _
      _ ≤ ‖π‖ * ε₁ := by gcongr; exact (hφb τ hτ).le
      _ < min r₁ ε / 2 := hπε.1
  have hyb' : ∀ τ ∈ Icc t₀ t₁, π (φ τ) ∈ closedBall (0 : State m) r₁ := fun τ hτ => by
    rw [mem_closedBall, dist_zero_right]
    linarith [hyb τ hτ, min_le_left r₁ ε]
  have huniq : ∀ s, s ≤ t₁ → (∀ τ ∈ Icc t₀ s, ‖ψ τ - 0‖ < r₁) →
      EqOn ψ (fun τ => π (φ τ)) (Icc t₀ s) := fun s hs hin =>
    eqOn_of_lipschitzOnWith hLg (hψ.mono (Icc_subset_Icc le_rfl hs))
      (hy.mono (Icc_subset_Icc le_rfl hs))
      (fun τ hτ => by
        rw [mem_closedBall, dist_zero_right]
        simpa using (hin τ hτ).le)
      (fun τ hτ => hyb' τ ⟨hτ.1, hτ.2.trans hs⟩) hy0.symm
  have hstay : ∀ τ ∈ Icc t₀ t₁, ‖ψ τ - 0‖ < r₁ := by
    refine forall_norm_sub_lt_of_bootstrap hψ.continuousOn
      (by rw [sub_zero]; exact hψ0r.trans_le (min_le_right _ _)) fun s hs hin => ?_
    rw [sub_zero, huniq s hs.2 hin ⟨hs.1, le_rfl⟩]
    linarith [hyb s hs, min_le_left r₁ ε]
  rw [huniq t₁ le_rfl hstay ht]
  linarith [hyb t ht, min_le_right r₁ ε]

end Instability

/-! ## (4a) Expansion of the reduced field -/

section Expansion

open Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- `‖u‖^k' = o(‖u‖^k)` as `u → 0` within any set, for `k < k'`. -/
@[tmio T, powerlib_foundation] theorem norm_pow_isLittleO {k k' : ℕ} (hk : k < k')
    (s : Set E) : (fun u : E => ‖u‖ ^ k') =o[𝓝[s] 0] fun u => ‖u‖ ^ k :=
  (isLittleO_pow_pow (𝕜 := ℝ) hk).comp_tendsto
    ((continuous_norm.tendsto' 0 0 norm_zero).mono_left nhdsWithin_le_nhds)

/-- A bilinear map of two curves is `O(‖a‖ ‖b‖)`. -/
@[tmio T, powerlib_foundation] theorem isBigO_bilin {α : Type*} {l : Filter α}
    (Q : E →L[ℝ] E →L[ℝ] E) (a b : α → E) :
    (fun u => Q (a u) (b u)) =O[l] fun u => ‖a u‖ * ‖b u‖ :=
  IsBigO.of_bound ‖Q‖ (Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_assoc]
    exact Q.le_opNorm₂ _ _)

/-- A trilinear map `C ![a, b, c]` of three curves is `O(‖a‖ ‖b‖ ‖c‖)`. -/
@[tmio T, powerlib_foundation] theorem isBigO_trilin {α : Type*} {l : Filter α}
    (C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E) (a b c : α → E) :
    (fun u => C ![a u, b u, c u]) =O[l] fun u => ‖a u‖ * ‖b u‖ * ‖c u‖ :=
  IsBigO.of_bound ‖C‖ (Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simpa [Fin.prod_univ_three, mul_assoc] using C.le_opNorm ![a u, b u, c u])

@[tmio T, powerlib_foundation] theorem trilin_add_zero
    (C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E) (a b c d : E) :
    C ![a + d, b, c] = C ![a, b, c] + C ![d, b, c] := by
  have := C.map_update_add ![a, b, c] 0 a d
  have e1 : Function.update ![a, b, c] 0 (a + d) = ![a + d, b, c] := by
    funext i; fin_cases i <;> simp
  have e2 : Function.update ![a, b, c] 0 a = ![a, b, c] := by funext i; fin_cases i <;> simp
  have e3 : Function.update ![a, b, c] 0 d = ![d, b, c] := by funext i; fin_cases i <;> simp
  rwa [e1, e2, e3] at this

@[tmio T, powerlib_foundation] theorem trilin_add_one
    (C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E) (a b c d : E) :
    C ![a, b + d, c] = C ![a, b, c] + C ![a, d, c] := by
  have := C.map_update_add ![a, b, c] 1 b d
  have e1 : Function.update ![a, b, c] 1 (b + d) = ![a, b + d, c] := by
    funext i; fin_cases i <;> simp
  have e2 : Function.update ![a, b, c] 1 b = ![a, b, c] := by funext i; fin_cases i <;> simp
  have e3 : Function.update ![a, b, c] 1 d = ![a, d, c] := by funext i; fin_cases i <;> simp
  rwa [e1, e2, e3] at this

@[tmio T, powerlib_foundation] theorem trilin_add_two
    (C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E) (a b c d : E) :
    C ![a, b, c + d] = C ![a, b, c] + C ![a, b, d] := by
  have := C.map_update_add ![a, b, c] 2 c d
  have e1 : Function.update ![a, b, c] 2 (c + d) = ![a, b, c + d] := by
    funext i; fin_cases i <;> simp
  have e2 : Function.update ![a, b, c] 2 c = ![a, b, c] := by funext i; fin_cases i <;> simp
  have e3 : Function.update ![a, b, c] 2 d = ![a, b, d] := by funext i; fin_cases i <;> simp
  rwa [e1, e2, e3] at this

/-- **Expansion of the reduced field.** If `f(x) = Q(x, x) + C(x, x, x) + o(‖x‖³)` at `0` and
`h(u) = H(u, u) + O(‖u‖³)` on `range P`, then on `range P`
`g(u) = PAu + P[Q(u, u) + Q(u, H(u, u)) + Q(H(u, u), u) + C(u, u, u)] + o(‖u‖³)`
(`Q(u, H) + Q(H, u) = 2Q(u, H)` for symmetric `Q`). -/
@[tmio T, powerlib_foundation] theorem reducedField_expansion {A P : E →L[ℝ] E} {f h : E → E}
    {H Q : E →L[ℝ] E →L[ℝ] E} {C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    (hfQC : (fun x => f x - (Q x x + C ![x, x, x])) =o[𝓝 0] fun x => ‖x‖ ^ 3)
    (hH : HasQuadraticPart P h H) :
    IsLittleOrder P (fun u => reducedField A P f h u -
      (P (A u) + P (Q u u + Q u (H u u) + Q (H u u) u + C ![u, u, u]))) 3 := by
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, isLittleOrder_natCast_iff]
  set l := 𝓝[Set.range P] (0 : E)
  have hr : (fun u => h u - H u u) =O[l] fun u => ‖u‖ ^ 3 := hasQuadraticPart_iff.mp hH
  have hn1 : (fun u : E => u) =O[l] fun u => ‖u‖ := (isBigO_refl (fun u : E => u) l).norm_right
  have hH2 : (fun u => H u u) =O[l] fun u => ‖u‖ ^ 2 :=
    (isBigO_bilin H (fun u => u) (fun u => u)).congr_right fun u => (sq _).symm
  have h32 : (fun u : E => ‖u‖ ^ 3) =O[l] fun u => ‖u‖ ^ 2 :=
    (norm_pow_isLittleO (by norm_num) _).isBigO
  have h21 : (fun u : E => ‖u‖ ^ 2) =O[l] fun u => ‖u‖ :=
    ((norm_pow_isLittleO (k := 1) (by norm_num) _).isBigO).congr_right fun u => pow_one _
  have h43 : (fun u : E => ‖u‖ ^ 4) =o[l] fun u => ‖u‖ ^ 3 := norm_pow_isLittleO (by norm_num) _
  have hw : h =O[l] fun u => ‖u‖ ^ 2 :=
    ((hr.trans h32).add hH2).congr_left fun u => sub_add_cancel _ _
  have hx : (fun u => u + h u) =O[l] fun u => ‖u‖ := hn1.add (hw.trans h21)
  have ht : Tendsto (fun u => u + h u) l (𝓝 0) :=
    hx.trans_tendsto ((continuous_norm.tendsto' 0 0 norm_zero).mono_left nhdsWithin_le_nhds)
  -- the three remainders
  have hT1 : (fun u => f (u + h u) - (Q (u + h u) (u + h u) +
      C ![u + h u, u + h u, u + h u])) =o[l] fun u => ‖u‖ ^ 3 :=
    (hfQC.comp_tendsto ht).trans_isBigO (hx.norm_left.pow 3)
  have hT2 : (fun u => Q u (h u - H u u) + Q (h u - H u u) u + Q (h u) (h u))
      =o[l] fun u => ‖u‖ ^ 3 := by
    have e1 : (fun u => Q u (h u - H u u)) =O[l] fun u => ‖u‖ ^ 4 :=
      ((isBigO_bilin Q (fun u => u) fun u => h u - H u u).trans
        (hn1.norm_left.mul hr.norm_left)).congr_right fun u => by ring
    have e2 : (fun u => Q (h u - H u u) u) =O[l] fun u => ‖u‖ ^ 4 :=
      ((isBigO_bilin Q (fun u => h u - H u u) fun u => u).trans
        (hr.norm_left.mul hn1.norm_left)).congr_right fun u => by ring
    have e3 : (fun u => Q (h u) (h u)) =O[l] fun u => ‖u‖ ^ 4 :=
      ((isBigO_bilin Q h h).trans (hw.norm_left.mul hw.norm_left)).congr_right fun u => by ring
    exact ((e1.add e2).add e3).trans_isLittleO h43
  have hT3 : (fun u => C ![h u, u + h u, u + h u] + C ![u, h u, u + h u] + C ![u, u, h u])
      =o[l] fun u => ‖u‖ ^ 3 := by
    have e1 : (fun u => C ![h u, u + h u, u + h u]) =O[l] fun u => ‖u‖ ^ 4 :=
      ((isBigO_trilin C h (fun u => u + h u) fun u => u + h u).trans
        ((hw.norm_left.mul hx.norm_left).mul hx.norm_left)).congr_right fun u => by ring
    have e2 : (fun u => C ![u, h u, u + h u]) =O[l] fun u => ‖u‖ ^ 4 :=
      ((isBigO_trilin C (fun u => u) h fun u => u + h u).trans
        ((hn1.norm_left.mul hw.norm_left).mul hx.norm_left)).congr_right fun u => by ring
    have e3 : (fun u => C ![u, u, h u]) =O[l] fun u => ‖u‖ ^ 4 :=
      ((isBigO_trilin C (fun u => u) (fun u => u) h).trans
        ((hn1.norm_left.mul hn1.norm_left).mul hw.norm_left)).congr_right fun u => by ring
    exact ((e1.add e2).add e3).trans_isLittleO h43
  have hsum := (P.isBigO_comp _ l).trans_isLittleO ((hT1.add hT2).add hT3)
  refine hsum.congr_left fun u => ?_
  have e3 : C ![u + h u, u + h u, u + h u] = C ![h u, u + h u, u + h u] +
      C ![u, h u, u + h u] + C ![u, u, h u] + C ![u, u, u] := by
    rw [trilin_add_zero, trilin_add_one, trilin_add_two]; abel
  simp only [reducedField, ← map_sub, ← map_add]
  congr 1
  rw [e3]
  simp only [map_add, add_apply, map_sub, sub_apply]
  abel

/-- **Expansion of the reduced field in coordinates.** Under the hypotheses of
`reducedField_expansion`, the chart field on `ℝᵐ` is
`G(y) = πAιy + π[Q(ιy, ιy) + Q(ιy, H(ιy, ιy)) + Q(H(ιy, ιy), ιy) + C(ιy, ιy, ιy)] + o(‖y‖³)`
as `y → 0`: a planar (or `m`-dimensional) field with linear, quadratic and cubic parts, the form
of hypothesis of the weak-focus laws. -/
@[tmio T, powerlib_foundation] theorem chartField_expansion {n m : ℕ}
    {A P : State n →L[ℝ] State n} {f h : State n → State n} {ι : State m →L[ℝ] State n}
    {π : State n →L[ℝ] State m} {H Q : State n →L[ℝ] State n →L[ℝ] State n}
    {C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State n) (State n)}
    (hc : IsChart P ι π)
    (hfQC : (fun x => f x - (Q x x + C ![x, x, x])) =o[𝓝 0] fun x => ‖x‖ ^ 3)
    (hH : HasQuadraticPart P h H) :
    (fun y => chartField A f h ι π y - (π (A (ι y)) + π (Q (ι y) (ι y) +
      Q (ι y) (H (ι y) (ι y)) + Q (H (ι y) (ι y)) (ι y) + C ![ι y, ι y, ι y])))
      =o[𝓝 0] fun y => ‖y‖ ^ 3 := by
  have hexp := reducedField_expansion (A := A) hfQC hH
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, isLittleOrder_natCast_iff] at hexp
  have ht : Tendsto ι (𝓝 0) (𝓝[Set.range P] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun y => ⟨ι y, hc.proj_ι y⟩⟩
    simpa using ι.continuous.tendsto 0
  have hι : (fun y => ‖ι y‖ ^ 3) =O[𝓝 (0 : State m)] fun y => ‖y‖ ^ 3 :=
    ((ι.isBigO_id (𝓝 0)).norm_left.norm_right).pow 3 |>.congr_right fun y => by simp
  have h2 := (π.isBigO_comp _ (𝓝 0)).trans_isLittleO ((hexp.comp_tendsto ht).trans_isBigO hι)
  refine h2.congr_left fun y => ?_
  simp only [Function.comp_apply, map_sub, map_add, hc.π_proj]
  rw [← hc.ι_chartField, hc.left_inv]

end Expansion

/-! ## (3) The homological equation for the quadratic part -/

section Homological

open Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The quadratic graph `x ↦ H₀(P x, P x)` of a bilinear map. -/
def quadGraph (P : E →L[ℝ] E) (H₀ : E →L[ℝ] E →L[ℝ] E) (x : E) : E := H₀ (P x) (P x)

/-- The homological equation of the quadratic part: for `u ∈ range P`,
`H₀(u, PAu) + H₀(PAu, u) = (1 − P) A H₀(u, u) + (1 − P) Q(u, u)`, i.e.
`((1 − P)A ∘ H₀ − H₀ ∘ (PA ⊗ 1 + 1 ⊗ PA))(u, u) = −(1 − P) Q(u, u)`. -/
def IsHomological (A P : E →L[ℝ] E) (Q H₀ : E →L[ℝ] E →L[ℝ] E) : Prop :=
  ∀ u, P u = u → H₀ u (P (A u)) + H₀ (P (A u)) u = (1 - P) (A (H₀ u u)) + (1 - P) (Q u u)

@[tmio T, powerlib_foundation] theorem isGraphMap_quadGraph {A P : E →L[ℝ] E}
    (hP : IsCommutingProjection A P) {H₀ : E →L[ℝ] E →L[ℝ] E} (hPH : ∀ u v, P (H₀ u v) = 0) :
    IsGraphMap P (quadGraph P H₀) :=
  ⟨fun x => by simp [quadGraph, hP.idem], fun x => hPH _ _, by simp [quadGraph]⟩

@[tmio T, powerlib_foundation] theorem fderiv_quadGraph (P : E →L[ℝ] E)
    (H₀ : E →L[ℝ] E →L[ℝ] E) (u v : E) :
    fderiv ℝ (quadGraph P H₀) u v = H₀ (P u) (P v) + H₀ (P v) (P u) := by
  have hd := H₀.hasFDerivAt_of_bilinear P.hasFDerivAt P.hasFDerivAt (x := u)
  rw [show quadGraph P H₀ = fun y => H₀ (P y) (P y) from rfl, hd.fderiv]
  simp

@[tmio T, powerlib_foundation] theorem contDiff_quadGraph (P : E →L[ℝ] E)
    (H₀ : E →L[ℝ] E →L[ℝ] E) : ContDiff ℝ 1 (quadGraph P H₀) :=
  H₀.isBoundedBilinearMap.contDiff.comp (P.contDiff.prodMk P.contDiff)

@[tmio T, powerlib_foundation] theorem fderiv_quadGraph_zero (P : E →L[ℝ] E)
    (H₀ : E →L[ℝ] E →L[ℝ] E) : fderiv ℝ (quadGraph P H₀) 0 = 0 := by
  ext v
  simp [fderiv_quadGraph]

/-- **The homological equation makes the quadratic graph an approximate centre manifold.** If
`f(x) = Q(x, x) + O(‖x‖³)` at `0` and `H₀` solves the
homological equation, the invariance defect of `u ↦ H₀(u, u)` is `O(‖u‖³)` on `range P`: the
hypothesis of Carr's approximation theorem with `q = 3`. -/
@[tmio T, powerlib_foundation] theorem isOrder_invarianceDefect_quadGraph
    {A P : E →L[ℝ] E} {f : E → E} {Q H₀ : E →L[ℝ] E →L[ℝ] E}
    (hP : IsCommutingProjection A P) (hhom : IsHomological A P Q H₀)
    (hf2 : (fun x => f x - Q x x) =O[𝓝 0] fun x => ‖x‖ ^ 3) :
    IsOrder P (invarianceDefect A P f (quadGraph P H₀)) 3 := by
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, isOrder_natCast_iff]
  set l := 𝓝[Set.range P] (0 : E)
  set w := quadGraph P H₀
  have hn1 : (fun u : E => u) =O[l] fun u => ‖u‖ := (isBigO_refl (fun u : E => u) l).norm_right
  have hPn : (fun u => P u) =O[l] fun u => ‖u‖ := (P.isBigO_comp _ l).trans hn1
  have hw : w =O[l] fun u => ‖u‖ ^ 2 :=
    ((isBigO_bilin H₀ (fun u => P u) fun u => P u).trans
      (hPn.norm_left.mul hPn.norm_left)).congr_right fun u => by ring
  have h21 : (fun u : E => ‖u‖ ^ 2) =O[l] fun u => ‖u‖ :=
    ((norm_pow_isLittleO (k := 1) (by norm_num) _).isBigO).congr_right fun u => pow_one _
  have h32 : (fun u : E => ‖u‖ ^ 3) =O[l] fun u => ‖u‖ ^ 2 :=
    (norm_pow_isLittleO (by norm_num) _).isBigO
  have h43 : (fun u : E => ‖u‖ ^ 4) =O[l] fun u => ‖u‖ ^ 3 :=
    (norm_pow_isLittleO (by norm_num) _).isBigO
  have hx : (fun u => u + w u) =O[l] fun u => ‖u‖ := hn1.add (hw.trans h21)
  have ht : Tendsto (fun u => u + w u) l (𝓝 0) :=
    hx.trans_tendsto ((continuous_norm.tendsto' 0 0 norm_zero).mono_left nhdsWithin_le_nhds)
  have hR : (fun u => f (u + w u) - Q (u + w u) (u + w u)) =O[l] fun u => ‖u‖ ^ 3 :=
    (hf2.comp_tendsto ht).trans (hx.norm_left.pow 3)
  have hQx : (fun u => Q (u + w u) (u + w u)) =O[l] fun u => ‖u‖ ^ 2 :=
    ((isBigO_bilin Q (fun u => u + w u) fun u => u + w u).trans
      (hx.norm_left.mul hx.norm_left)).congr_right fun u => by ring
  have hfx : (fun u => f (u + w u)) =O[l] fun u => ‖u‖ ^ 2 :=
    ((hR.trans h32).add hQx).congr_left fun u => sub_add_cancel _ _
  have hPf : (fun u => P (f (u + w u))) =O[l] fun u => ‖u‖ ^ 2 := (P.isBigO_comp _ l).trans hfx
  have e1 : (fun u => H₀ u (P (f (u + w u)))) =O[l] fun u => ‖u‖ ^ 3 :=
    ((isBigO_bilin H₀ (fun u => u) fun u => P (f (u + w u))).trans
      (hn1.norm_left.mul hPf.norm_left)).congr_right fun u => by ring
  have e2 : (fun u => H₀ (P (f (u + w u))) u) =O[l] fun u => ‖u‖ ^ 3 :=
    ((isBigO_bilin H₀ (fun u => P (f (u + w u))) fun u => u).trans
      (hPf.norm_left.mul hn1.norm_left)).congr_right fun u => by ring
  have e3 : (fun u => (1 - P) (f (u + w u) - Q (u + w u) (u + w u))) =O[l]
      fun u => ‖u‖ ^ 3 := ((1 - P).isBigO_comp _ l).trans hR
  have e4 : (fun u => (1 - P) (Q u (w u) + Q (w u) u + Q (w u) (w u))) =O[l]
      fun u => ‖u‖ ^ 3 := by
    have a1 : (fun u => Q u (w u)) =O[l] fun u => ‖u‖ ^ 3 :=
      ((isBigO_bilin Q (fun u => u) w).trans (hn1.norm_left.mul hw.norm_left)).congr_right
        fun u => by ring
    have a2 : (fun u => Q (w u) u) =O[l] fun u => ‖u‖ ^ 3 :=
      ((isBigO_bilin Q w fun u => u).trans (hw.norm_left.mul hn1.norm_left)).congr_right
        fun u => by ring
    have a3 : (fun u => Q (w u) (w u)) =O[l] fun u => ‖u‖ ^ 3 :=
      (((isBigO_bilin Q w w).trans (hw.norm_left.mul hw.norm_left)).congr_right
        fun u => by ring).trans h43
    exact ((1 - P).isBigO_comp _ l).trans ((a1.add a2).add a3)
  have hsum := ((e1.add e2).sub e3).sub e4
  refine hsum.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [self_mem_nhdsWithin] with u hu
  obtain ⟨v, rfl⟩ := hu
  have hPu : P (P v) = P v := hP.idem v
  set u := P v
  have hwu : w u = H₀ u u := by simp only [w, quadGraph, hPu]
  have hhu := hhom u hPu
  have hPg : P (reducedField A P f w u) = P (A u) + P (f (u + w u)) := by
    simp only [reducedField, map_add, hP.idem]
  have hD : invarianceDefect A P f w u = (H₀ u (P (A u)) + H₀ (P (A u)) u) +
      (H₀ u (P (f (u + w u))) + H₀ (P (f (u + w u))) u) -
      ((1 - P) (A (H₀ u u)) + (1 - P) (f (u + w u))) := by
    rw [invarianceDefect, normalField, show fderiv ℝ w u = fderiv ℝ (quadGraph P H₀) u from rfl,
      fderiv_quadGraph, hPu, hPg, ← hwu]
    simp only [map_add, add_apply]
    abel
  have hQ : Q (u + w u) (u + w u) = Q u u + (Q u (w u) + Q (w u) u + Q (w u) (w u)) := by
    simp only [map_add, add_apply]; abel
  rw [hD, hhu, hQ]
  simp only [map_add, map_sub]
  abel

/-- The quadratic part of a graph is unique on `range P`: two bilinear maps `H`, `H'` with
`h(u) = H(u, u) + O(‖u‖³)` and `h(u) = H'(u, u) + O(‖u‖³)` agree on the diagonal of
`range P`. -/
@[tmio T, powerlib_foundation] theorem HasQuadraticPart.apply_eq {P : E →L[ℝ] E} {h : E → E}
    {H H' : E →L[ℝ] E →L[ℝ] E} (hH : HasQuadraticPart P h H) (hH' : HasQuadraticPart P h H')
    {u : E} (hu : u ∈ Set.range P) : H u u = H' u u := by
  have hd : (fun v => H v v - H' v v) =O[𝓝[Set.range P] 0] fun v => ‖v‖ ^ 3 :=
    ((hasQuadraticPart_iff.mp hH').sub (hasQuadraticPart_iff.mp hH)).congr_left fun v => by abel
  obtain ⟨c, hc⟩ := hd.bound
  have hseg : Tendsto (fun t : ℝ => t • u) (𝓝[>] 0) (𝓝[Set.range P] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun t => ?_⟩
    · have : Tendsto (fun t : ℝ => t • u) (𝓝 0) (𝓝 ((0 : ℝ) • u)) := tendsto_id.smul_const u
      rw [zero_smul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · obtain ⟨v, rfl⟩ := hu
      exact ⟨t • v, by simp⟩
  have hev := hseg.eventually hc
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖H u u - H' u u‖ ≤ c * t * ‖u‖ ^ 3 := by
    filter_upwards [hev, self_mem_nhdsWithin] with t ht htpos
    have htp : (0 : ℝ) < t := htpos
    have e : H (t • u) (t • u) - H' (t • u) (t • u) = (t ^ 2) • (H u u - H' u u) := by
      simp only [map_smul, smul_apply, smul_smul, smul_sub, pow_two]
    have en : ‖t • u‖ = t * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos htp]
    rw [e, Real.norm_of_nonneg (by positivity), en, norm_smul, Real.norm_of_nonneg
      (by positivity)] at ht
    have ht2 : (0 : ℝ) < t ^ 2 := by positivity
    have : t ^ 2 * ‖H u u - H' u u‖ ≤ t ^ 2 * (c * t * ‖u‖ ^ 3) := by
      calc t ^ 2 * ‖H u u - H' u u‖ ≤ c * (t * ‖u‖) ^ 3 := ht
        _ = t ^ 2 * (c * t * ‖u‖ ^ 3) := by ring
    exact le_of_mul_le_mul_left this ht2
  have hlim : Tendsto (fun t : ℝ => c * t * ‖u‖ ^ 3) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => c * t * ‖u‖ ^ 3) (𝓝 0) (𝓝 (c * 0 * ‖u‖ ^ 3)) :=
      ((continuous_const.mul continuous_id).mul continuous_const).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hle : ‖H u u - H' u u‖ ≤ 0 := ge_of_tendsto hlim hsmall
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hle)

/-- **The quadratic part is determined by `A`, `P` and `Q`** (combination with Carr's
approximation theorem, `theorem/Dynamics/CenterManifoldApprox.lean`). Let `H₀` solve the
homological equation and `f(x) = Q(x, x) + O(‖x‖³)`. If Carr's approximation property holds for
the quadratic graph of `H₀` (its `O(‖u‖³)` invariance defect, `isOrder_invarianceDefect_quadGraph`,
gives `h(u) − H₀(u, u) = O(‖u‖³)`), then every bilinear `H` with `h(u) = H(u, u) + O(‖u‖³)`
agrees with `H₀` on the diagonal of `range P`. -/
@[tmio T, powerlib_foundation] theorem HasQuadraticPart.apply_eq_of_homological
    {A P : E →L[ℝ] E} {f h : E → E} {Q H H₀ : E →L[ℝ] E →L[ℝ] E}
    (hP : IsCommutingProjection A P) (hhom : IsHomological A P Q H₀)
    (hf2 : (fun x => f x - Q x x) =O[𝓝 0] fun x => ‖x‖ ^ 3)
    (hcarr : IsOrder P (invarianceDefect A P f (quadGraph P H₀)) 3 →
      IsOrder P (fun u => h u - quadGraph P H₀ u) 3)
    (hH : HasQuadraticPart P h H) {u : E} (hu : u ∈ Set.range P) : H u u = H₀ u u := by
  have h0 : HasQuadraticPart P h H₀ := by
    have hc := hcarr (isOrder_invarianceDefect_quadGraph hP hhom hf2)
    refine hc.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [self_mem_nhdsWithin] with v hv
    obtain ⟨w, rfl⟩ := hv
    simp [quadGraph, hP.idem]
  exact hH.apply_eq h0 hu

end Homological

/-! ## The homological operator on bilinear maps -/

section Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `(1 − P)` is idempotent with `P`. -/
@[tmio T, powerlib_foundation] theorem compl_idem {P : E →L[ℝ] E} (hP : ∀ x, P (P x) = P x)
    (y : E) : (1 - P) ((1 - P) y) = (1 - P) y := by
  rw [compl_apply, compl_apply, map_sub, hP]; abel

/-- Bilinear maps `range P × range P → range (1 − P)`, read on `E × E`:
`H(u, v) = (1 − P) H(P u, P v)`. -/
def bilinOnRange (P : E →L[ℝ] E) : Submodule ℝ (E →L[ℝ] E →L[ℝ] E) where
  carrier := {H | ∀ u v, H u v = (1 - P) (H (P u) (P v))}
  add_mem' {H H'} hH hH' u v := by
    simp only [Set.mem_ofPred_eq] at hH hH' ⊢
    rw [add_apply, add_apply, add_apply, add_apply, map_add, ← hH, ← hH']
  zero_mem' u v := by simp
  smul_mem' c H hH u v := by
    simp only [Set.mem_ofPred_eq] at hH ⊢
    rw [smul_apply, smul_apply, smul_apply, smul_apply, map_smul, ← hH]

/-- The homological operator on bilinear maps,
`T H (u, v) = (1 − P)A(1 − P) H(Pu, Pv) − (1 − P) H(PAPu, Pv) − (1 − P) H(Pu, PAPv)`; on
`bilinOnRange P` and `range P` it is `(1 − P)A ∘ H − H ∘ (PA ⊗ 1 + 1 ⊗ PA)`. -/
def homologicalOp (A P : E →L[ℝ] E) :
    (E →L[ℝ] E →L[ℝ] E) →ₗ[ℝ] (E →L[ℝ] E →L[ℝ] E) where
  toFun H := (ContinuousLinearMap.compL ℝ E E E ((1 - P) * A * (1 - P))).comp
      (H.bilinearComp P P) -
    (ContinuousLinearMap.compL ℝ E E E (1 - P)).comp (H.bilinearComp (P * A * P) P) -
    (ContinuousLinearMap.compL ℝ E E E (1 - P)).comp (H.bilinearComp P (P * A * P))
  map_add' H H' := by
    ext u v
    simp only [sub_apply, add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.bilinearComp_apply, map_add]
    abel
  map_smul' c H := by
    ext u v
    simp only [sub_apply, smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.bilinearComp_apply, map_smul,
      RingHom.id_apply, smul_sub]

/-- The projection `H ↦ (1 − P) H(P ·, P ·)` onto `bilinOnRange P`. -/
def rangeProj (P : E →L[ℝ] E) : (E →L[ℝ] E →L[ℝ] E) →ₗ[ℝ] (E →L[ℝ] E →L[ℝ] E) where
  toFun H := (ContinuousLinearMap.compL ℝ E E E (1 - P)).comp (H.bilinearComp P P)
  map_add' H H' := by
    ext u v
    simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.bilinearComp_apply, map_add]
  map_smul' c H := by
    ext u v
    simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.bilinearComp_apply, map_smul,
      RingHom.id_apply]

@[tmio T, powerlib_foundation] theorem rangeProj_apply (P : E →L[ℝ] E)
    (H : E →L[ℝ] E →L[ℝ] E) (u v : E) : rangeProj P H u v = (1 - P) (H (P u) (P v)) := by
  simp only [rangeProj, LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.bilinearComp_apply]

@[tmio T, powerlib_foundation] theorem homologicalOp_apply (A P : E →L[ℝ] E)
    (H : E →L[ℝ] E →L[ℝ] E) (u v : E) :
    homologicalOp A P H u v = (1 - P) (A ((1 - P) (H (P u) (P v)))) -
      (1 - P) (H (P (A (P u))) (P v)) - (1 - P) (H (P u) (P (A (P v)))) := by
  simp only [homologicalOp, LinearMap.coe_mk, AddHom.coe_mk, sub_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.bilinearComp_apply]
  rfl

/-- On `bilinOnRange P` and `range P` the homological operator is
`(1 − P)A H(u, v) − H(PAu, v) − H(u, PAv)`. -/
@[tmio T, powerlib_foundation] theorem homologicalOp_apply_of_mem {A P : E →L[ℝ] E}
    (hP : IsCommutingProjection A P) {H : E →L[ℝ] E →L[ℝ] E} (hH : H ∈ bilinOnRange P)
    {u v : E} (hu : P u = u) (hv : P v = v) :
    homologicalOp A P H u v = (1 - P) (A (H u v)) - H (P (A u)) v - H u (P (A v)) := by
  have h1 : ∀ x y, (1 - P) (H x y) = H x y := fun x y => by
    rw [hH x y, compl_idem hP.idem]
  rw [homologicalOp_apply, hu, hv, h1, h1, h1]

end Operator

/-! ## (3b) Unique solvability of the homological equation under the dichotomy -/

section Solvability

open Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Injectivity of the homological operator under the centre–stable dichotomy.** Let
`‖e^{tA}(1 − P)‖ ≤ K e^{−βt}` and `‖e^{−tA}P‖ ≤ K e^{εt}` for `t ≥ 0`, with `2ε < β` (the
non-resonance of the centre–stable case: `Re μ ≤ −β` for the stable spectrum, `|Re λ| ≤ ε` for the
centre spectrum, so `μ ≠ λ + λ'`). A bilinear `H` with values in `range (1 − P)` and
`(1 − P)A H(u, v) = H(PAu, v) + H(u, PAv)` on `range P` vanishes on `range P`: the function
`t ↦ e^{tA}(1 − P) H(e^{−tA}u, e^{−tA}v)` is constant and decays like `e^{(2ε − β)t}`. -/
@[tmio T, powerlib_foundation] theorem homological_eq_zero {A P : E →L[ℝ] E}
    (hP : IsCommutingProjection A P) {K β ε : ℝ} (hgap : 2 * ε < β)
    (hs : ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp (t • A) * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    (hc : ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((-t) • A) * P‖ ≤ K * Real.exp (ε * t))
    {H : E →L[ℝ] E →L[ℝ] E} (hH1 : ∀ u v, (1 - P) (H u v) = H u v)
    (hL : ∀ u v, P u = u → P v = v → (1 - P) (A (H u v)) = H (P (A u)) v + H u (P (A v)))
    {u v : E} (hu : P u = u) (hv : P v = v) : H u v = 0 := by
  have hcomm : Commute P A := (ContinuousLinearMap.ext fun x => (hP.comm x).symm :
    P * A = A * P)
  have hPe : ∀ t : ℝ, ∀ x, P (NormedSpace.exp (t • (-A)) x) = NormedSpace.exp (t • (-A)) (P x) :=
    fun t x => by
      have := ((hcomm.neg_right).smul_right t).exp_right
      exact congrArg (fun T : E →L[ℝ] E => T x) this.eq
  have hcA : Commute (1 - P) A := (Commute.one_left A).sub_left hcomm
  have hAc : ∀ x, A ((1 - P) x) = (1 - P) (A x) := fun x =>
    (congrArg (fun T : E →L[ℝ] E => T x) hcA.eq).symm
  set a : ℝ → E := fun t => NormedSpace.exp (t • (-A)) u with ha
  set b : ℝ → E := fun t => NormedSpace.exp (t • (-A)) v with hb
  set Φ : ℝ → E := fun t => NormedSpace.exp (t • A) ((1 - P) (H (a t) (b t))) with hΦ
  have hPa : ∀ t, P (a t) = a t := fun t => by simp only [ha, hPe, hu]
  have hPb : ∀ t, P (b t) = b t := fun t => by simp only [hb, hPe, hv]
  have hda : ∀ t, HasDerivAt a (-(A (a t))) t := fun t => by
    have := (hasDerivAt_exp_smul_const' (-A) t).clm_apply (hasDerivAt_const t u)
    simpa [ha] using this
  have hdb : ∀ t, HasDerivAt b (-(A (b t))) t := fun t => by
    have := (hasDerivAt_exp_smul_const' (-A) t).clm_apply (hasDerivAt_const t v)
    simpa [hb] using this
  have hdΦ : ∀ t, HasDerivAt Φ 0 t := by
    intro t
    have h1 := ((1 - P).hasFDerivAt.comp_hasDerivAt t
      ((H.hasFDerivAt.comp_hasDerivAt t (hda t)).clm_apply (hdb t)))
    have h2 := (hasDerivAt_exp_smul_const' A t).clm_apply h1
    refine HasDerivAt.congr_deriv (f := Φ) h2 ?_
    simp only [Function.comp_apply]
    have e1 : P (A (a t)) = A (a t) := by rw [← hP.comm, hPa]
    have e2 : P (A (b t)) = A (b t) := by rw [← hP.comm, hPb]
    have hLab : (1 - P) (A (H (a t) (b t))) = H (A (a t)) (b t) + H (a t) (A (b t)) := by
      rw [hL (a t) (b t) (hPa t) (hPb t), e1, e2]
    have hy : A ((1 - P) (H (a t) (b t))) = H (A (a t)) (b t) + H (a t) (A (b t)) := by
      rw [hAc, hLab]
    have e4 : (A * NormedSpace.exp (t • A)) ((1 - P) (H (a t) (b t))) =
        NormedSpace.exp (t • A) (A ((1 - P) (H (a t) (b t)))) := by
      have := ((Commute.refl A).smul_right t).exp_right
      exact congrArg (fun T : E →L[ℝ] E => T ((1 - P) (H (a t) (b t)))) this.eq
    rw [e4, hy]
    simp only [map_neg, neg_apply, map_add, hH1]
    abel
  have hconst : ∀ t, Φ t = Φ 0 := fun t =>
    is_const_of_deriv_eq_zero (fun s => (hdΦ s).differentiableAt) (fun s => (hdΦ s).deriv) t 0
  have hΦ0 : Φ 0 = H u v := by simp [hΦ, ha, hb, hH1]
  have hK : 0 ≤ K := by
    have := (norm_nonneg _).trans (hs 0 le_rfl)
    simpa using this
  have hbound : ∀ t : ℝ, 0 ≤ t → ‖H u v‖ ≤
      K ^ 3 * ‖H‖ * ‖u‖ * ‖v‖ * Real.exp ((2 * ε - β) * t) := by
    intro t ht
    rw [← hΦ0, ← hconst t]
    have hat : a t = (NormedSpace.exp ((-t) • A) * P) u := by
      show NormedSpace.exp (t • (-A)) u = NormedSpace.exp ((-t) • A) (P u)
      rw [hu, neg_smul, smul_neg]
    have hbt : b t = (NormedSpace.exp ((-t) • A) * P) v := by
      show NormedSpace.exp (t • (-A)) v = NormedSpace.exp ((-t) • A) (P v)
      rw [hv, neg_smul, smul_neg]
    have hΦt : Φ t = (NormedSpace.exp (t • A) * (1 - P)) (H (a t) (b t)) := rfl
    have hna : ‖a t‖ ≤ K * Real.exp (ε * t) * ‖u‖ := by
      rw [hat]; exact ((NormedSpace.exp ((-t) • A) * P).le_opNorm u).trans
        (by gcongr; exact hc t ht)
    have hnb : ‖b t‖ ≤ K * Real.exp (ε * t) * ‖v‖ := by
      rw [hbt]; exact ((NormedSpace.exp ((-t) • A) * P).le_opNorm v).trans
        (by gcongr; exact hc t ht)
    have hHab : ‖H (a t) (b t)‖ ≤ ‖H‖ * (K * Real.exp (ε * t) * ‖u‖) *
        (K * Real.exp (ε * t) * ‖v‖) :=
      (H.le_opNorm₂ _ _).trans (by gcongr)
    rw [hΦt]
    calc ‖(NormedSpace.exp (t • A) * (1 - P)) (H (a t) (b t))‖
        ≤ ‖NormedSpace.exp (t • A) * (1 - P)‖ * ‖H (a t) (b t)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * Real.exp (-(β * t)) * (‖H‖ * (K * Real.exp (ε * t) * ‖u‖) *
          (K * Real.exp (ε * t) * ‖v‖)) := by gcongr; exact hs t ht
      _ = K ^ 3 * ‖H‖ * ‖u‖ * ‖v‖ * Real.exp ((2 * ε - β) * t) := by
          rw [show (2 * ε - β) * t = -(β * t) + ε * t + ε * t by ring, Real.exp_add,
            Real.exp_add]
          ring
  have hlim : Tendsto (fun t : ℝ => K ^ 3 * ‖H‖ * ‖u‖ * ‖v‖ * Real.exp ((2 * ε - β) * t))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => (2 * ε - β) * t) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by linarith)
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (K ^ 3 * ‖H‖ * ‖u‖ * ‖v‖)
  have hle : ‖H u v‖ ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.mpr ⟨0, fun t ht => hbound t ht⟩)
  exact norm_le_zero_iff.mp hle

/-- Uniqueness of the quadratic form: two solutions of the homological equation with values in
`range (1 − P)` agree on the diagonal of `range P` (polarize the difference and apply
`homological_eq_zero` to its symmetric part). -/
@[tmio T, powerlib_foundation] theorem IsHomological.apply_eq {A P : E →L[ℝ] E}
    (hP : IsCommutingProjection A P) {K β ε : ℝ} (hgap : 2 * ε < β)
    (hs : ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp (t • A) * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    (hc : ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((-t) • A) * P‖ ≤ K * Real.exp (ε * t))
    {Q H₀ H₁ : E →L[ℝ] E →L[ℝ] E} (h₀ : IsHomological A P Q H₀) (h₁ : IsHomological A P Q H₁)
    (hP₀ : ∀ u v, P (H₀ u v) = 0) (hP₁ : ∀ u v, P (H₁ u v) = 0) {u : E} (hu : P u = u) :
    H₀ u u = H₁ u u := by
  set D := H₀ - H₁
  set Ds := D + D.flip
  have hD1 : ∀ x y, (1 - P) (Ds x y) = Ds x y := fun x y => by
    simp [Ds, D, hP₀, hP₁]
  have hdiag : ∀ w, P w = w → D w (P (A w)) + D (P (A w)) w = (1 - P) (A (D w w)) := by
    intro w hw
    have e₀ := h₀ w hw
    have e₁ := h₁ w hw
    have hDa : ∀ x y, D x y = H₀ x y - H₁ x y := fun x y => rfl
    rw [hDa, hDa, hDa, map_sub, map_sub]
    rw [show H₀ w (P (A w)) - H₁ w (P (A w)) + (H₀ (P (A w)) w - H₁ (P (A w)) w) =
      (H₀ w (P (A w)) + H₀ (P (A w)) w) - (H₁ w (P (A w)) + H₁ (P (A w)) w) by abel, e₀, e₁]
    abel
  have hL : ∀ x y, P x = x → P y = y →
      (1 - P) (A (Ds x y)) = Ds (P (A x)) y + Ds x (P (A y)) := by
    intro x y hx hy
    have hxy : P (x + y) = x + y := by rw [map_add, hx, hy]
    have h3 := hdiag (x + y) hxy
    have h4 := hdiag x hx
    have h5 := hdiag y hy
    simp only [map_add, add_apply] at h3
    simp only [Ds, add_apply, ContinuousLinearMap.flip_apply, map_add]
    rw [← h4, ← h5] at h3
    linear_combination (norm := abel) -h3
  have h0 := homological_eq_zero hP hgap hs hc hD1 hL hu hu
  simp only [Ds, add_apply, ContinuousLinearMap.flip_apply, D, sub_apply] at h0
  have : (2 : ℝ) • (H₀ u u - H₁ u u) = 0 := by rw [two_smul]; exact h0
  exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_left two_ne_zero)

/-- **Unique solvability of the homological equation** (finite dimension, centre–stable
dichotomy with `2ε < β`). For every bilinear `R` there is exactly one `H ∈ bilinOnRange P` with
`(1 − P)A H(u, v) − H(PAu, v) − H(u, PAv) = −(1 − P) R(u, v)` on `range P`: the homological
operator is injective (`homological_eq_zero`), hence bijective, on `bilinOnRange P`. -/
@[tmio T, powerlib_foundation] theorem existsUnique_homological [FiniteDimensional ℝ E]
    {A P : E →L[ℝ] E} (hP : IsCommutingProjection A P) {K β ε : ℝ} (hgap : 2 * ε < β)
    (hs : ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp (t • A) * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    (hc : ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((-t) • A) * P‖ ≤ K * Real.exp (ε * t))
    (R : E →L[ℝ] E →L[ℝ] E) :
    ∃! H : E →L[ℝ] E →L[ℝ] E, H ∈ bilinOnRange P ∧ ∀ u v, P u = u → P v = v →
      (1 - P) (A (H u v)) - H (P (A u)) v - H u (P (A v)) = -(1 - P) (R u v) := by
  have hmem1 : ∀ H ∈ bilinOnRange P, ∀ x y, (1 - P) (H x y) = H x y := fun H hH x y => by
    rw [hH x y, compl_idem hP.idem]
  have hmemP : ∀ H ∈ bilinOnRange P, ∀ x y, H (P x) (P y) = H x y := fun H hH x y => by
    rw [hH (P x) (P y), hP.idem, hP.idem, ← hH x y]
  have hTS : ∀ H : E →L[ℝ] E →L[ℝ] E, ∀ u v,
      homologicalOp A P H u v = (1 - P) (homologicalOp A P H (P u) (P v)) := fun H u v => by
    simp only [homologicalOp_apply, hP.idem, map_sub, compl_idem hP.idem]
  -- the homogeneous equation has only the zero solution in `bilinOnRange P`
  have hzero : ∀ H ∈ bilinOnRange P,
      (∀ u v, P u = u → P v = v → homologicalOp A P H u v = 0) → H = 0 := by
    intro H hH hT
    have hL : ∀ u v, P u = u → P v = v →
        (1 - P) (A (H u v)) = H (P (A u)) v + H u (P (A v)) := fun u v hu hv => by
      have := hT u v hu hv
      rw [homologicalOp_apply_of_mem hP hH hu hv] at this
      rw [← sub_eq_zero, ← this]; abel
    ext u v
    rw [← hmemP H hH, homological_eq_zero hP hgap hs hc (hmem1 H hH) hL (hP.idem u)
      (hP.idem v)]
    simp
  -- an operator on the whole (finite-dimensional) space of bilinear maps
  set T' := homologicalOp A P + (LinearMap.id - rangeProj P) with hT'
  have hT'app : ∀ (H : E →L[ℝ] E →L[ℝ] E) (u v : E), T' H u v =
      homologicalOp A P H u v + (H u v - (1 - P) (H (P u) (P v))) := fun H u v => by
    rw [← rangeProj_apply]
    rfl
  -- reading `T' H = R` with `R ∈ bilinOnRange P`
  have hsplit : ∀ H R : E →L[ℝ] E →L[ℝ] E, R ∈ bilinOnRange P → T' H = R →
      H ∈ bilinOnRange P ∧ homologicalOp A P H = R := by
    intro H R hR hHR
    have hpt : ∀ u v, homologicalOp A P H u v + (H u v - (1 - P) (H (P u) (P v))) = R u v :=
      fun u v => by rw [← hT'app, hHR]
    have hT0 : ∀ u v, homologicalOp A P H u v = R u v := fun u v => by
      have h1 := congrArg (fun y : E => (1 - P) y) (hpt (P u) (P v))
      rw [map_add, map_sub, compl_idem hP.idem, hP.idem, hP.idem, sub_self, add_zero,
        ← hTS, ← hR] at h1
      exact h1
    have hS : H ∈ bilinOnRange P := fun u v => by
      have := hpt u v
      rw [hT0, add_eq_left, sub_eq_zero] at this
      exact this
    exact ⟨hS, ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun v => hT0 u v⟩
  have hinj : Function.Injective T' := by
    intro a b hab
    have h0 : T' (a - b) = 0 := by rw [map_sub, hab, sub_self]
    obtain ⟨hS, hT⟩ := hsplit (a - b) 0 (bilinOnRange P).zero_mem h0
    exact sub_eq_zero.mp (hzero _ hS fun u v _ _ => by rw [hT]; rfl)
  have hR : (ContinuousLinearMap.compL ℝ E E E (-(1 - P))).comp (R.bilinearComp P P) ∈
      bilinOnRange P := fun u v => by simp [hP.idem]
  obtain ⟨x, hx⟩ := LinearMap.injective_iff_surjective.mp hinj
    ((ContinuousLinearMap.compL ℝ E E E (-(1 - P))).comp (R.bilinearComp P P))
  obtain ⟨hxS, hx'⟩ := hsplit x _ hR hx
  have hsol : ∀ u v, P u = u → P v = v →
      (1 - P) (A (x u v)) - x (P (A u)) v - x u (P (A v)) = -(1 - P) (R u v) := by
    intro u v hu hv
    have := congrArg (fun T : E →L[ℝ] E →L[ℝ] E => T u v) hx'
    rw [homologicalOp_apply_of_mem hP hxS hu hv] at this
    rw [this]
    simp [hu, hv]
  refine ⟨x, ⟨hxS, hsol⟩, ?_⟩
  rintro H ⟨hH, hHeq⟩
  have hsub : H - x ∈ bilinOnRange P := (bilinOnRange P).sub_mem hH hxS
  have := hzero (H - x) hsub fun u v hu hv => by
    rw [homologicalOp_apply_of_mem hP hsub hu hv]
    have e1 := hHeq u v hu hv
    have e2 := hsol u v hu hv
    have hsa : ∀ a b, (H - x) a b = H a b - x a b := fun a b => rfl
    rw [hsa, hsa, hsa, map_sub, map_sub]
    linear_combination (norm := abel) e1 - e2
  exact sub_eq_zero.mp this

/-- **Existence of the quadratic part.** Under the dichotomy (finite dimension, `2ε < β`) the
homological equation of `Q` has a solution `H₀` with values in `range (1 − P)`. -/
@[tmio T, powerlib_foundation] theorem exists_isHomological [FiniteDimensional ℝ E]
    {A P : E →L[ℝ] E} (hP : IsCommutingProjection A P) {K β ε : ℝ} (hgap : 2 * ε < β)
    (hs : ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp (t • A) * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    (hc : ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((-t) • A) * P‖ ≤ K * Real.exp (ε * t))
    (Q : E →L[ℝ] E →L[ℝ] E) :
    ∃ H₀ : E →L[ℝ] E →L[ℝ] E, IsHomological A P Q H₀ ∧ ∀ u v, P (H₀ u v) = 0 := by
  obtain ⟨H₀, ⟨hS, hH⟩, -⟩ := existsUnique_homological hP hgap hs hc Q
  refine ⟨H₀, fun u hu => ?_, fun u v => ?_⟩
  · have := hH u u hu hu
    linear_combination (norm := abel) -this
  · rw [hS u v]; simp [hP.idem]

end Solvability

/-! ## (4c) The planar first Lyapunov coefficient of the reduced field decides instability -/

section PlanarReduction

open Asymptotics

variable {n : ℕ} {A P : State n →L[ℝ] State n} {f h : State n → State n}

/-- **Instability from the reduced planar `l₁`** (combination of the reduction with the planar
weak-focus law `Dynamics.Degenerate.PlanarFocus.unstable_of_l1_pos`). Let the graph of a
`K`-Lipschitz graph map `h` over a plane `range P` (coordinates `ι : ℝ² → ℝⁿ`, `π`) be locally
invariant for `ẋ = A x + f x`, `f` of class `C¹` with `f(x) = Q(x, x) + C(x, x, x) + o(‖x‖³)`,
and `h(u) = H(u, u) + O(‖u‖³)` on `range P`. Read the reduced field in the coordinates: linear
part `L₂ = πAι` with `L₂² = −ω²`, quadratic part `Q₂(y, y) = πQ(ιy, ιy)`, cubic part
`C₂(y, y, y) = π[Q(ιy, H(ιy, ιy)) + Q(H(ιy, ιy), ιy) + C(ιy, ιy, ιy)]`. If the planar
coefficient `l1 L₂ Q₂ C₂ ω` is positive, `0` is unstable for the full field. -/
@[tmio T, powerlib_foundation] theorem unstable_of_reduced_l1_pos {K : NNReal} {ρ ω : ℝ}
    {ι : State 2 →L[ℝ] State n} {π : State n →L[ℝ] State 2}
    {H Q : State n →L[ℝ] State n →L[ℝ] State n}
    {C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State n) (State n)}
    {L₂ : State 2 →L[ℝ] State 2} {Q₂ : State 2 →L[ℝ] State 2 →L[ℝ] State 2}
    {C₂ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State 2) (State 2)}
    (hP : IsCommutingProjection A P) (hh : IsGraphMap P h) (hK : LipschitzWith K h)
    (hc : IsChart P ι π) (hf : ContDiff ℝ 1 f) (hρ : 0 < ρ)
    (hinv : ∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
      φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h)
    (hfQC : (fun x => f x - (Q x x + C ![x, x, x])) =o[𝓝 0] fun x => ‖x‖ ^ 3)
    (hH : HasQuadraticPart P h H) (hL₂ : ∀ y, L₂ y = π (A (ι y)))
    (hQ₂ : ∀ y, Q₂ y y = π (Q (ι y) (ι y)))
    (hC₂ : ∀ y, C₂ ![y, y, y] = π (Q (ι y) (H (ι y) (ι y)) + Q (H (ι y) (ι y)) (ι y) +
      C ![ι y, ι y, ι y]))
    (hω : 0 < ω) (hrot : ∀ y, L₂ (L₂ y) = -(ω ^ 2) • y)
    (hl : 0 < Degenerate.PlanarFocus.l1 L₂ Q₂ C₂ ω) : Unstable (fullField A f) 0 := by
  obtain ⟨R₀, hR₀, Lf, hLf⟩ := exists_lipschitzOnWith_closedBall hf
  have hK1 : (0 : ℝ) < 1 + K := by positivity
  set r₁ := R₀ / ((1 + K) * (‖ι‖ + 1)) with hr₁
  have hr₁0 : 0 < r₁ := by positivity
  have hr₁R : (1 + K) * ‖ι‖ * r₁ ≤ R₀ := by
    have : (1 + K) * ‖ι‖ * r₁ ≤ (1 + K) * (‖ι‖ + 1) * r₁ := by gcongr; linarith
    refine this.trans (le_of_eq ?_)
    rw [hr₁]; field_simp
  obtain ⟨Lg, hLg⟩ := exists_lipschitzOnWith_chartField (A := A) (π := π) hh.map_zero hK hLf
    hr₁R
  have hexp := chartField_expansion (A := A) hc hfQC hH
  have hexp' : (fun y => chartField A f h ι π y - (L₂ y + Q₂ y y + C₂ ![y, y, y]))
      =o[𝓝 0] fun y => ‖y‖ ^ 3 := by
    refine hexp.congr_left fun y => ?_
    rw [hL₂, hQ₂, hC₂]
    simp only [map_add]
    abel
  exact unstable_of_unstable_chartField hP hh hK hc hf hρ hinv
    (Degenerate.PlanarFocus.unstable_of_l1_pos hω hrot (closedBall_mem_nhds 0 hr₁0) hLg hexp' hl)

end PlanarReduction

/-! ## (5) End to end: dichotomy, centre manifold, quadratic part, planar `l₁` -/

section EndToEnd

open Asymptotics LyapunovPerron

variable {n : ℕ} {A P : State n →L[ℝ] State n}

/-- **The quadratic part of the centre manifold** (combination with Carr's approximation theorem
`exists_centerManifold_approx`). Under the centre–stable dichotomy with `3ε < β`, `f` of class
`C¹` with `f(0) = 0`, `Df(0) = 0`, `f(x) = Q(x, x) + O(‖x‖³)`, and `H₀` (values in `ker P`)
solving the homological equation, there is a locally invariant Lipschitz centre manifold `h`
with `h(u) = H₀(u, u) + O(‖u‖³)` on `range P`. -/
@[tmio T, powerlib_foundation] theorem exists_centerManifold_hasQuadraticPart
    (hP : IsCommutingProjection A P) {K ε β : ℝ} (hε : 0 ≤ ε) (hgap : 3 * ε < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {f : State n → State n} (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0) (hDf : fderiv ℝ f 0 = 0)
    {Q H₀ : State n →L[ℝ] State n →L[ℝ] State n}
    (hf2 : (fun x => f x - Q x x) =O[𝓝 0] fun x => ‖x‖ ^ 3)
    (hhom : IsHomological A P Q H₀) (hPH : ∀ u v, P (H₀ u v) = 0) :
    ∃ ρ > 0, ∃ h : State n → State n, ∃ L : NNReal, IsGraphMap P h ∧ LipschitzWith L h ∧
      HasQuadraticPart P h H₀ ∧
      ∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
        φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h := by
  obtain ⟨ρ, hρ, h, L, hh, hL, -, hinv, hcarr⟩ := exists_centerManifold_approx hP hε (q := 3)
    (by norm_num) hgap hcen hst hf hf0 hDf
  have hd := hcarr (quadGraph P H₀) (contDiff_quadGraph P H₀).contDiffAt
    (by simp [quadGraph]) (fderiv_quadGraph_zero P H₀) (fun x => hPH _ _)
    (isOrder_invarianceDefect_quadGraph hP hhom hf2)
  refine ⟨ρ, hρ, h, L, hh, hL, ?_, hinv⟩
  refine hd.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [self_mem_nhdsWithin] with v hv
  obtain ⟨w, rfl⟩ := hv
  simp [quadGraph, hP.idem]

/-- **The reduced planar `l₁` decides instability in any dimension.** Let `A` have a
two-dimensional centre subspace `range P` (coordinates `ι : ℝ² → ℝⁿ`, `π`) with the
centre–stable dichotomy, `3ε < β`; `f` of class `C¹`, `f(0) = 0`, `Df(0) = 0`,
`f(x) = Q(x, x) + C(x, x, x) + o(‖x‖³)`; `H₀` (values in `ker P`) the solution of the homological
equation. Let `L₂ = πAι` (`L₂² = −ω²`, `ω > 0`), `Q₂(y, y) = πQ(ιy, ιy)` and
`C₂(y, y, y) = π[Q(ιy, H₀(ιy, ιy)) + Q(H₀(ιy, ιy), ιy) + C(ιy, ιy, ιy)]`. If
`l1 L₂ Q₂ C₂ ω > 0`, the origin is unstable for `ẋ = A x + f x`. -/
@[tmio T, powerlib_foundation] theorem unstable_of_dichotomy_reduced_l1_pos
    (hP : IsCommutingProjection A P) {K ε β ω : ℝ} (hε : 0 ≤ ε) (hgap : 3 * ε < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {f : State n → State n} (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0) (hDf : fderiv ℝ f 0 = 0)
    {Q H₀ : State n →L[ℝ] State n →L[ℝ] State n}
    {C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State n) (State n)}
    (hfQC : (fun x => f x - (Q x x + C ![x, x, x])) =o[𝓝 0] fun x => ‖x‖ ^ 3)
    (hhom : IsHomological A P Q H₀) (hPH : ∀ u v, P (H₀ u v) = 0)
    {ι : State 2 →L[ℝ] State n} {π : State n →L[ℝ] State 2} (hc : IsChart P ι π)
    {L₂ : State 2 →L[ℝ] State 2} {Q₂ : State 2 →L[ℝ] State 2 →L[ℝ] State 2}
    {C₂ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State 2) (State 2)}
    (hL₂ : ∀ y, L₂ y = π (A (ι y))) (hQ₂ : ∀ y, Q₂ y y = π (Q (ι y) (ι y)))
    (hC₂ : ∀ y, C₂ ![y, y, y] = π (Q (ι y) (H₀ (ι y) (ι y)) + Q (H₀ (ι y) (ι y)) (ι y) +
      C ![ι y, ι y, ι y]))
    (hω : 0 < ω) (hrot : ∀ y, L₂ (L₂ y) = -(ω ^ 2) • y)
    (hl : 0 < Degenerate.PlanarFocus.l1 L₂ Q₂ C₂ ω) : Unstable (fullField A f) 0 := by
  have hf2 : (fun x => f x - Q x x) =O[𝓝 0] fun x => ‖x‖ ^ 3 := by
    have hCb : (fun x : State n => C ![x, x, x]) =O[𝓝 0] fun x => ‖x‖ ^ 3 :=
      (isBigO_trilin C (fun x => x) (fun x => x) fun x => x).congr_right fun x => by ring
    exact (hfQC.isBigO.add hCb).congr_left fun x => by abel
  obtain ⟨ρ, hρ, h, L, hh, hL, hH, hinv⟩ :=
    exists_centerManifold_hasQuadraticPart hP hε hgap hcen hst hf hf0 hDf hf2 hhom hPH
  exact unstable_of_reduced_l1_pos hP hh hL hc hf hρ hinv hfQC hH hL₂ hQ₂ hC₂ hω hrot hl

/-- Under the dichotomy of the centre manifold theorem with `2ε < β` (finite dimension), the
homological equation of every `Q` has a solution with values in `ker P`
(`exists_isHomological` read with `expFlow`). -/
@[tmio T, powerlib_foundation] theorem exists_isHomological_of_dichotomy
    (hP : IsCommutingProjection A P) {K ε β : ℝ} (hgap : 2 * ε < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    (Q : State n →L[ℝ] State n →L[ℝ] State n) :
    ∃ H₀ : State n →L[ℝ] State n →L[ℝ] State n, IsHomological A P Q H₀ ∧
      ∀ u v, P (H₀ u v) = 0 := by
  refine exists_isHomological hP hgap (K := K) (fun t ht => hst t ht) (fun t ht => ?_) Q
  have := hcen (-t)
  rwa [abs_neg, abs_of_nonneg ht] at this

end EndToEnd

/-! ## (6) Kuznetsov's projection formula decides instability in any dimension -/

section ProjectionFormula

open Asymptotics LyapunovPerron NormalForm.LyapunovCoefficient

variable {n : ℕ} {A : State n →L[ℝ] State n}

/-- **`ℓ₁ > 0` gives instability in any dimension** (projection-formula form). Let `(q, p)` be a
critical pair of the field `ẋ = A x + f x` at `0` (`f` of class `C¹`, `f(0) = 0`, `Df(0) = 0`),
let `P` be the spectral projection of the critical chart (`critP q p`) with the centre–stable
dichotomy (`3ε < β`), let `A` and `2iω − A` be invertible, and let
`f(x) = Q(x, x) + C(x, x, x) + o(‖x‖³)` with `D²F(0)`, `D³F(0)` the symmetrizations of `Q`, `C`.
If Kuznetsov's first Lyapunov coefficient `firstLyapunov (fullField A f) 0 ω q p` is positive,
the origin is unstable. (Centre manifold: `exists_centerManifold_approx`; quadratic part:
`exists_isHomological_of_dichotomy`; identity of the coefficients:
`IsCritical.l1_reduced_eq_firstLyapunov`; planar law: `unstable_of_dichotomy_reduced_l1_pos`.) -/
@[tmio T, powerlib_foundation] theorem unstable_of_firstLyapunov_pos {f : State n → State n}
    {Q : State n →L[ℝ] State n →L[ℝ] State n}
    {C : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => State n) (State n)} {ω K ε β : ℝ}
    {q p : Fin n → ℂ} (hcp : IsCriticalPair (fullField A f) 0 ω q p) (hε : 0 ≤ ε)
    (hgap : 3 * ε < β) (hcen : ∀ t, ‖expFlow A t * critP q p‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - critP q p)‖ ≤ K * Real.exp (-(β * t)))
    (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0) (hDf : fderiv ℝ f 0 = 0)
    (hfQC : (fun x => f x - (Q x x + C ![x, x, x])) =o[𝓝 0] fun x => ‖x‖ ^ 3)
    (hd2 : ∀ u w, iteratedFDeriv ℝ 2 (fullField A f) 0 ![u, w] = Q u w + Q w u)
    (hd3 : ∀ u w z, iteratedFDeriv ℝ 3 (fullField A f) 0 ![u, w, z] = C ![u, w, z] +
      C ![u, z, w] + C ![w, u, z] + C ![w, z, u] + C ![z, u, w] + C ![z, w, u])
    (hA : IsUnit (cmat A).det) (h2 : IsUnit (shift2 (cmat A) ω).det)
    (hl : 0 < firstLyapunov (fullField A f) 0 ω q p) : Unstable (fullField A f) 0 := by
  have hdA : fderiv ℝ (fullField A f) 0 = A := by
    have hd : HasFDerivAt (fullField A f) (A + 0) 0 := by
      have := A.hasFDerivAt.add ((hf.differentiable one_ne_zero 0).hasFDerivAt)
      rw [hDf] at this
      exact this
    rw [hd.fderiv, add_zero]
  have hc := IsCriticalPair.isCritical hcp hdA
  have hP := hc.isCommutingProjection
  obtain ⟨H₀, hhom, hPH⟩ := exists_isHomological_of_dichotomy hP (by linarith) hcen hst Q
  have hbr := hc.l1_reduced_eq_firstLyapunov (C := C) hdA hd2 hd3 hA h2 hhom hPH
  exact unstable_of_dichotomy_reduced_l1_pos hP hε hgap hcen hst hf hf0 hDf hfQC hhom hPH
    hc.isChart (fun y => (hc.critπ_comp y).symm) (fun y => redQ_apply q p Q y y)
    (fun y => redC_apply q p Q H₀ C y y y) hc.freq_pos (rotL_rotL ω) (hbr ▸ hl)

end ProjectionFormula

end powerlib.Dynamics.CenterManifold
