import theorem.Dynamics.OrbitLaSalle
import theorem.Dynamics.Coordinates
import theorem.PhasePlane.Conservative

/-! # Bounded forward solutions converge to an equilibrium

A function that does not increase along a `C¹` (or globally Lipschitz) field, whose Lie derivative
vanishes along no whole forward solution except at equilibria, and isolated equilibria: then every
forward solution that stays bounded converges to a single equilibrium. No positively invariant set
and no lower bound of the function are assumed (it is bounded on the bounded orbit), so the
function may be an indefinite "energy" such as the potential of a loaded swing machine or
Barbashin's function of a third-order loop.

Scope.
* `ẋ = f(x)` on `State n = ℝⁿ`, `f` globally Lipschitz or `C¹`; solutions are `IsIntegralCurveOn`
  curves on `[0, ∞)` (one-sided derivative at `0`). Generic dynamical-systems foundation; no model
  family.
* The conclusion is about one forward solution (trajectory, ω-limit level), outside the sentence
  language of the library; model families read it as implementation evidence.

Source: work-sync theory/T-lyapunov-function-method.md §1.4 (LaSalle invariance principle);
H. K. Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.1 (a bounded orbit converges to its
nonempty, compact, connected, invariant ω-limit set) and Theorem 4.4; the GFL counterpart
`theorem/GridTiedConverter/GFL/LCLine/Convergence.lean` (`piPLL_tendsto_of_bounded`, a direct
Barbalat argument for the PI-PLL).

Results.
* `exists_tendsto_of_tendsto_nhdsSet`: a curve, continuous on `[0, ∞)` with bounded forward image,
  that converges to a closed set `Z` whose points in the closure of the curve are isolated in `Z`
  converges to one point of `Z` (the curve cannot cross an annulus around a cluster point
  infinitely often).
* `sinusoid_level_isolated`: the level sets of `c + A sin(θ − α)`, `A ≠ 0`, are discrete.
* `fderiv_apply_eq_zero_of_const`, `field_apply_eq_zero_of_coord_const`: a differentiable function
  (a coordinate) constant along a forward solution has zero derivative along the field there.
* `forwardSolution_mem_closure_orbit`: for a globally Lipschitz field the closure of a forward
  orbit is forward invariant (continuity of the flow in the initial state).
* `exists_tendsto_of_bounded_of_lipschitzWith` (globally Lipschitz `f`), `exists_tendsto_of_bounded`
  (`C¹` `f`, through a cutoff `Flow.exists_lipschitz_cutoff` equal to one on a ball containing the
  orbit): `V` differentiable, `V̇ = DV·f ≤ 0` along the solution, every forward solution in the
  closure of the orbit along which `V̇ ≡ 0` starts at an equilibrium, and the equilibria there
  isolated ⇒ the bounded forward solution converges to an equilibrium
  (`Dynamics.tendsto_nhdsSet_of_antitone` along the orbit, then
  `exists_tendsto_of_tendsto_nhdsSet`).
* `conservative_exists_tendsto_of_bounded`: the damped mechanical field
  `m ẍ + γ ẋ + V'(x) = 0` (`PhasePlane.Conservative.field`, `m, γ > 0`, `V'` `C¹` with isolated
  zeros): every bounded forward solution converges to `(x*, 0)` with `V'(x*) = 0` (energy
  `V(x) + m v²/2`, `Ė = −γ v²`, `V = ∫ V'`).
-/

noncomputable section
namespace powerlib.Dynamics

open Set Filter Topology NNReal

/-! ## Convergence to a set of isolated points -/

section Topology

variable {E : Type*} [MetricSpace E] [ProperSpace E]

/-- **A bounded curve converging to a set of isolated points converges to one of them.** -/
@[tmio T, powerlib_foundation] theorem exists_tendsto_of_tendsto_nhdsSet {x : ℝ → E}
    (hx : ContinuousOn x (Ici 0)) (hb : Bornology.IsBounded (x '' Ici 0)) {Z : Set E}
    (hZ : IsClosed Z)
    (hiso : ∀ z ∈ Z, z ∈ closure (x '' Ici 0) → ∃ ε > 0, ∀ y ∈ Z, dist y z < ε → y = z)
    (h : Tendsto x atTop (𝓝ˢ Z)) : ∃ z ∈ Z, Tendsto x atTop (𝓝 z) := by
  obtain ⟨z, hzc, hz⟩ := hb.isCompact_closure.exists_mapClusterPt (f := atTop) (u := x) (by
    rw [le_principal_iff, mem_map]
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact subset_closure ⟨t, ht, rfl⟩)
  have hzZ : z ∈ Z := by
    by_contra hzn
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hZ.isOpen_compl z hzn
    have hU : (Metric.closedBall z (ε / 2))ᶜ ∈ 𝓝ˢ Z := by
      refine (isOpen_compl_iff.mpr Metric.isClosed_closedBall).mem_nhdsSet.mpr fun y hy hyb => ?_
      exact hball (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hyb)
        (half_lt_self hε))) hy
    obtain ⟨t, ht1, ht2⟩ :=
      ((hz.frequently (Metric.closedBall_mem_nhds z (half_pos hε))).and_eventually (h hU)).exists
    exact ht2 ht1
  refine ⟨z, hzZ, ?_⟩
  obtain ⟨ε, hε, hiso'⟩ := hiso z hzZ hzc
  rw [Metric.tendsto_atTop]
  intro η hη
  set r := min η ε / 3 with hr
  have hr0 : 0 < r := by positivity
  have hrη : r < η := by
    have := min_le_left η ε
    simp only [hr]; linarith
  have h2rε : 2 * r < ε := by
    have := min_le_right η ε
    simp only [hr]; linarith
  set A : Set E := {y | r ≤ dist y z ∧ dist y z ≤ 2 * r}
  have hAc : IsClosed A :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le (continuous_id.dist continuous_const) continuous_const)
  have hAZ : Aᶜ ∈ 𝓝ˢ Z := by
    refine hAc.isOpen_compl.mem_nhdsSet.mpr fun y hy hyA => ?_
    have hyz := hiso' y hy (lt_of_le_of_lt hyA.2 h2rε)
    have h1 : r ≤ dist y z := hyA.1
    rw [hyz, dist_self] at h1
    linarith
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (h hAZ)
  obtain ⟨T₂, hT₂, hT₂z⟩ := (hz.frequently (Metric.ball_mem_nhds z hr0)).forall_exists_of_atTop
    (max T₁ 0)
  refine ⟨T₂, fun t ht => ?_⟩
  by_contra hnot
  push Not at hnot
  have hT0 : 0 ≤ T₂ := (le_max_right _ _).trans hT₂
  have hsub : Icc T₂ t ⊆ Ici 0 := fun s hs => (hT0.trans hs.1 : (0 : ℝ) ≤ s)
  have hcont : ContinuousOn (fun s => dist (x s) z) (Icc T₂ t) :=
    (continuous_id.dist continuous_const).comp_continuousOn (hx.mono hsub)
  obtain ⟨s, hs, hsr⟩ := intermediate_value_Icc ht hcont
    ⟨(Metric.mem_ball.mp hT₂z).le, hrη.le.trans hnot⟩
  exact hT₁ s ((le_max_left _ _).trans (hT₂.trans hs.1)) ⟨hsr.ge, by simp only at hsr; linarith⟩

end Topology

/-! ## Isolated level points of a sinusoid -/

/-- The level sets of a non-constant sinusoid `c + A sin(θ − α)` (`A ≠ 0`) are discrete: around
every angle there is a radius inside which no other angle has the same value (at most two
solutions per period, `SpecialFunctions.sinusoidZeros_subset`). -/
@[tmio T, powerlib_foundation] theorem sinusoid_level_isolated {c A α p : ℝ} (hA : A ≠ 0)
    (θ : ℝ) : ∃ ε > 0, ∀ θ', c + A * Real.sin (θ' - α) = p → |θ' - θ| < ε → θ' = θ := by
  obtain ⟨c', A', hA', hiff⟩ : ∃ c' A' : ℝ, 0 < A' ∧ ∀ x,
      c + A * Real.sin (x - α) = p ↔ c' - A' * Real.sin (x + -α) = 0 := by
    rcases lt_or_gt_of_ne hA with h | h
    · exact ⟨c - p, -A, neg_pos.mpr h, fun x => by
        rw [← sub_eq_add_neg]; constructor <;> intro hx <;> linarith⟩
    · exact ⟨p - c, A, h, fun x => by
        rw [← sub_eq_add_neg]; constructor <;> intro hx <;> linarith⟩
  set Z := SpecialFunctions.sinusoidZeros c' A' (-α) (θ - Real.pi)
  have hfin : (Z \ {θ}).Finite :=
    ((Set.toFinite _).subset (SpecialFunctions.sinusoidZeros_subset hA')).subset sdiff_subset
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hfin.isClosed.isOpen_compl θ (by simp)
  refine ⟨min ε Real.pi, lt_min hε Real.pi_pos, fun θ' hθ' hd => ?_⟩
  by_contra hne
  have hπ := abs_lt.mp (lt_of_lt_of_le hd (min_le_right _ _))
  have hmem : θ' ∈ Z \ {θ} :=
    ⟨⟨⟨by linarith [hπ.1], by linarith [hπ.2]⟩, (hiff θ').mp hθ'⟩, hne⟩
  exact hball (by rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hd (min_le_left _ _))
    hmem

/-! ## Derivatives along a forward solution -/

section Along

variable {n : ℕ} {f : State n → State n}

/-- A differentiable function constant along a forward solution has zero derivative along the
field at every time `t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem fderiv_apply_eq_zero_of_const {ψ : ℝ → State n}
    (hψ : IsIntegralCurveOn ψ (fun _ y => f y) (Ici 0)) {g : State n → ℝ}
    (hg : Differentiable ℝ g) {c : ℝ} (hc : ∀ t, 0 ≤ t → g (ψ t) = c) {t : ℝ} (ht : 0 ≤ t) :
    fderiv ℝ g (ψ t) (f (ψ t)) = 0 := by
  have h1 : HasDerivWithinAt (fun s => g (ψ s)) (fderiv ℝ g (ψ t) (f (ψ t))) (Ici 0) t :=
    (hg (ψ t)).hasFDerivAt.comp_hasDerivWithinAt t (hψ t ht)
  have h2 : HasDerivWithinAt (fun s => g (ψ s)) 0 (Ici 0) t :=
    (hasDerivWithinAt_const t (Ici 0) c).congr (fun s hs => hc s hs) (hc t ht)
  exact (uniqueDiffOn_Ici 0 t ht).eq_deriv _ h1 h2

/-- A coordinate constant along a forward solution: the field's coordinate vanishes there. -/
@[tmio T, powerlib_foundation] theorem field_apply_eq_zero_of_coord_const {ψ : ℝ → State n}
    (hψ : IsIntegralCurveOn ψ (fun _ y => f y) (Ici 0)) (i : Fin n) {c : ℝ}
    (hc : ∀ t, 0 ≤ t → ψ t i = c) {t : ℝ} (ht : 0 ≤ t) : f (ψ t) i = 0 := by
  have h := fderiv_apply_eq_zero_of_const hψ (coord i).differentiable hc ht
  rwa [(coord i).fderiv, coord_apply] at h

end Along

/-! ## Bounded solutions converge -/

section Converge

variable {n : ℕ} {f : State n → State n} {K : ℝ≥0}

/-- For a globally Lipschitz field the closure of a forward orbit is forward invariant. -/
@[tmio T, powerlib_foundation] theorem forwardSolution_mem_closure_orbit (hf : LipschitzWith K f)
    {φ : ℝ → State n} (hφ : IsIntegralCurveOn φ (fun _ y => f y) (Ici 0)) {p : State n}
    (hp : p ∈ closure (φ '' Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    forwardSolution hf p t ∈ closure (φ '' Ici 0) := by
  have huniq := forwardSolution_unique hf (φ 0) φ rfl hφ
  have hc : Continuous fun q => forwardSolution hf q t :=
    (lipschitzFlow hf).continuous (t := fun _ => (⟨t, ht⟩ : ℝ≥0)) continuous_const continuous_id
  refine closure_mono ?_ (image_closure_subset_closure_image hc ⟨p, hp, rfl⟩)
  rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
  refine ⟨t + s, add_nonneg ht hs, ?_⟩
  rw [huniq (show s ∈ Ici 0 from hs), huniq (show t + s ∈ Ici 0 from add_nonneg ht hs)]
  exact forwardSolution_add hf (φ 0) hs ht

/-- **A bounded forward solution of a globally Lipschitz field converges to an equilibrium**:
`V` differentiable and nonincreasing along the solution (`V̇ = DV·f ≤ 0` there), every forward
solution in the closure of the orbit along which `V̇ ≡ 0` starts at an equilibrium, and the
equilibria in that closure isolated among the equilibria. -/
@[tmio T, powerlib_foundation] theorem exists_tendsto_of_bounded_of_lipschitzWith
    (hf : LipschitzWith K f) {V : State n → ℝ} (hV : Differentiable ℝ V) {φ : ℝ → State n}
    (hφ : IsIntegralCurveOn φ (fun _ y => f y) (Ici 0)) (hb : Bornology.IsBounded (φ '' Ici 0))
    (hlie : ∀ t, 0 ≤ t → fderiv ℝ V (φ t) (f (φ t)) ≤ 0)
    (hinv : ∀ ψ : ℝ → State n, IsIntegralCurveOn ψ (fun _ y => f y) (Ici 0) →
      (∀ t, 0 ≤ t → ψ t ∈ closure (φ '' Ici 0)) →
      (∀ t, 0 ≤ t → fderiv ℝ V (ψ t) (f (ψ t)) = 0) → f (ψ 0) = 0)
    (hiso : ∀ z ∈ closure (φ '' Ici 0), f z = 0 →
      ∃ ε > 0, ∀ y, f y = 0 → dist y z < ε → y = z) :
    ∃ z, f z = 0 ∧ Tendsto φ atTop (𝓝 z) := by
  have huniq := forwardSolution_unique hf (φ 0) φ rfl hφ
  set B := closure (φ '' Ici 0)
  have hxB : ∀ t : ℝ, 0 ≤ t → forwardSolution hf (φ 0) t ∈ B := fun t ht => by
    rw [← huniq (show t ∈ Ici 0 from ht)]
    exact subset_closure ⟨t, ht, rfl⟩
  have hanti : AntitoneOn (V ∘ φ) (Ici 0) :=
    antitoneOn_V_comp_traj hV hV.continuous (convex_Ici 0) hφ fun t ht =>
      hlie t (interior_subset ht)
  have hZ : ∀ p ∈ B, (∀ t : ℝ, 0 ≤ t → V (forwardSolution hf p t) = V p) → p ∈ {y | f y = 0} :=
    fun p hpB hp => by
      have hψ := lipschitzFlow_solution hf p
      have h := hinv _ hψ (fun t ht => forwardSolution_mem_closure_orbit hf hφ hpB ht)
        fun t ht => fderiv_apply_eq_zero_of_const hψ hV hp ht
      rwa [forwardSolution_zero] at h
  have hconv := tendsto_nhdsSet_of_antitone hf hb.isCompact_closure hxB hV.continuous
    (fun s t hs hst => by
      rw [← huniq (show t ∈ Ici 0 from hs.trans hst), ← huniq (show s ∈ Ici 0 from hs)]
      exact hanti hs (hs.trans hst) hst) hZ
  have hφconv : Tendsto φ atTop (𝓝ˢ {y | f y = 0}) :=
    hconv.congr' (by
      filter_upwards [eventually_ge_atTop 0] with t ht
      exact (huniq (show t ∈ Ici 0 from ht)).symm)
  obtain ⟨z, hz, hzt⟩ := exists_tendsto_of_tendsto_nhdsSet hφ.continuousOn hb
    (isClosed_eq hf.continuous continuous_const) (fun z hz hzB => hiso z hzB hz) hφconv
  exact ⟨z, hz, hzt⟩

/-- **A bounded forward solution of a `C¹` field converges to an equilibrium** (the hypotheses of
`exists_tendsto_of_bounded_of_lipschitzWith`; the field is made globally Lipschitz by a cutoff
equal to one on a ball containing the orbit, `Flow.exists_lipschitz_cutoff`). -/
@[tmio T, powerlib_foundation] theorem exists_tendsto_of_bounded (hf : ContDiff ℝ 1 f)
    {V : State n → ℝ} (hV : Differentiable ℝ V) {φ : ℝ → State n}
    (hφ : IsIntegralCurveOn φ (fun _ y => f y) (Ici 0)) (hb : Bornology.IsBounded (φ '' Ici 0))
    (hlie : ∀ t, 0 ≤ t → fderiv ℝ V (φ t) (f (φ t)) ≤ 0)
    (hinv : ∀ ψ : ℝ → State n, IsIntegralCurveOn ψ (fun _ y => f y) (Ici 0) →
      (∀ t, 0 ≤ t → ψ t ∈ closure (φ '' Ici 0)) →
      (∀ t, 0 ≤ t → fderiv ℝ V (ψ t) (f (ψ t)) = 0) → f (ψ 0) = 0)
    (hiso : ∀ z ∈ closure (φ '' Ici 0), f z = 0 →
      ∃ ε > 0, ∀ y, f y = 0 → dist y z < ε → y = z) :
    ∃ z, f z = 0 ∧ Tendsto φ atTop (𝓝 z) := by
  obtain ⟨R₀, hR₀⟩ := hb.isCompact_closure.isBounded.subset_closedBall (0 : State n)
  have hB : ∀ y ∈ closure (φ '' Ici 0), ‖y‖ ≤ R₀ := fun y hy => by
    simpa [dist_zero_right] using hR₀ hy
  obtain ⟨χ, -, hχ1, K', hχ⟩ := Flow.exists_lipschitz_cutoff hf (R₀ + 1)
  set g : State n → State n := fun x => χ x • f x
  have hgf : ∀ y, ‖y‖ ≤ R₀ + 1 → g y = f y := fun y hy => by simp [g, hχ1 y hy]
  have hgB : ∀ y ∈ closure (φ '' Ici 0), g y = f y := fun y hy => hgf y (by linarith [hB y hy])
  have hφB : ∀ t, 0 ≤ t → φ t ∈ closure (φ '' Ici 0) := fun t ht =>
    subset_closure ⟨t, ht, rfl⟩
  have hφg : IsIntegralCurveOn φ (fun _ y => g y) (Ici 0) := fun t ht => by
    simp only [hgB _ (hφB t ht)]
    exact hφ t ht
  obtain ⟨z, hz, hzt⟩ := exists_tendsto_of_bounded_of_lipschitzWith hχ hV hφg hb
    (fun t ht => by rw [hgB _ (hφB t ht)]; exact hlie t ht)
    (fun ψ hψ hψB hψ0 => by
      have hψf : IsIntegralCurveOn ψ (fun _ y => f y) (Ici 0) := fun t ht => by
        have := hψ t ht
        simp only [hgB _ (hψB t ht)] at this
        exact this
      rw [hgB _ (hψB 0 le_rfl)]
      exact hinv ψ hψf hψB fun t ht => by rw [← hgB _ (hψB t ht)]; exact hψ0 t ht)
    (fun z hzB hz => by
      rw [hgB z hzB] at hz
      obtain ⟨ε, hε, hzε⟩ := hiso z hzB hz
      refine ⟨min ε 1, by positivity, fun y hy hyz => hzε y ?_ (lt_of_lt_of_le hyz
        (min_le_left _ _))⟩
      have hy' : ‖y‖ ≤ R₀ + 1 := by
        have h1 : ‖y - z‖ < 1 := by
          rw [← dist_eq_norm]; exact lt_of_lt_of_le hyz (min_le_right _ _)
        have h2 := norm_le_insert' y z
        linarith [hB z hzB]
      rwa [hgf y hy'] at hy)
  have hzB : z ∈ closure (φ '' Ici 0) :=
    mem_closure_of_tendsto hzt (by
      filter_upwards [eventually_ge_atTop 0] with t ht
      exact ⟨t, ht, rfl⟩)
  exact ⟨z, by rwa [hgB z hzB] at hz, hzt⟩

end Converge

/-! ## The damped mechanical system -/

section Conservative

open PhasePlane PhasePlane.Conservative

/-- **Bounded solutions of a damped mechanical system converge.** For `m, γ > 0` and a `C¹`
`V'` with isolated zeros, every forward solution of `m ẍ + γ ẋ + V'(x) = 0` that stays bounded
converges to an equilibrium `(x*, 0)`, `V'(x*) = 0` (possibly a saddle or a degenerate critical
point of `V`, reached on its stable set). The energy `V(x) + m v²/2` with `V = ∫ V'` decreases at
the rate `γ v²`; a solution with `v ≡ 0` has `v̇ = −V'(x)/m ≡ 0`. -/
@[tmio T, powerlib_foundation] theorem conservative_exists_tendsto_of_bounded {m γ : ℝ}
    (hm : 0 < m) (hγ : 0 < γ) {dV : ℝ → ℝ} (hdV : ContDiff ℝ 1 dV)
    (hiso : ∀ θ, dV θ = 0 → ∀ᶠ θ' in 𝓝[≠] θ, dV θ' ≠ 0) {φ : ℝ → State 2}
    (hφ : IsIntegralCurveOn φ (fun _ y => field m γ dV y) (Ici 0))
    (hb : Bornology.IsBounded (φ '' Ici 0)) :
    ∃ θs, dV θs = 0 ∧ Tendsto φ atTop (𝓝 (mk θs 0)) := by
  set U : ℝ → ℝ := fun θ => ∫ s in (0 : ℝ)..θ, dV s
  have hU : ∀ θ, HasDerivAt U (dV θ) θ := fun θ =>
    (hdV.continuous.integral_hasStrictDerivAt 0 θ).hasDerivAt
  have hUd : Differentiable ℝ U := fun θ => (hU θ).differentiableAt
  have hzero : ∀ y : State 2, field m γ dV y = 0 ↔ y 1 = 0 ∧ dV (y 0) = 0 :=
    field_eq_zero_iff hm.ne'
  obtain ⟨z, hz, hzt⟩ := exists_tendsto_of_bounded (field_contDiff hdV)
    (differentiable_separableEnergy hUd m 0) hφ hb (fun t _ => by
      rw [energy_lie hm.ne' hU]
      nlinarith [sq_nonneg (φ t 1)])
    (fun ψ hψ _ hzero' => by
      have hv : ∀ t, 0 ≤ t → ψ t 1 = 0 := fun t ht => by
        have h := hzero' t ht
        rw [energy_lie hm.ne' hU] at h
        have : γ * ψ t 1 ^ 2 = 0 := by linarith
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
          ((mul_eq_zero.mp this).resolve_left hγ.ne')
      have h1 := field_apply_eq_zero_of_coord_const hψ 1 hv le_rfl
      rw [field_apply_one, hv 0 le_rfl, mul_zero, zero_sub, div_eq_zero_iff, neg_eq_zero] at h1
      exact (hzero _).mpr ⟨hv 0 le_rfl, h1.resolve_right hm.ne'⟩)
    (fun z _ hz => by
      obtain ⟨hz1, hz0⟩ := (hzero z).mp hz
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
        (eventually_nhdsWithin_iff.mp (hiso _ hz0))
      refine ⟨ε, hε, fun y hy hyz => ?_⟩
      obtain ⟨hy1, hy0⟩ := (hzero y).mp hy
      by_contra hne
      have h0ne : y 0 ≠ z 0 := fun h0 => hne (ext_iff'.2 ⟨h0, by rw [hy1, hz1]⟩)
      have hd : dist (y 0) (z 0) < ε := by
        rw [Real.dist_eq]
        have := abs_apply_le_norm (y - z) 0
        simp only [PiLp.sub_apply] at this
        exact lt_of_le_of_lt this (by rwa [← dist_eq_norm])
      exact hball hd h0ne hy0)
  obtain ⟨hz1, hz0⟩ := (hzero z).mp hz
  refine ⟨z 0, hz0, ?_⟩
  have : z = mk (z 0) 0 := ext_iff'.2 ⟨by simp, by simp [hz1]⟩
  rwa [← this]

end Conservative

end powerlib.Dynamics
