import theorem.Dynamics.CenterManifoldSmooth
import theorem.Dynamics.CenterManifoldApproxAny

/-! # Small bounded solutions lie on the centre manifold (foundation)

The Lyapunov–Perron centre manifold contains every whole-line solution of the cutoff field of
weighted growth `e^{η|t|}`; consequently a centre manifold of the construction contains every
whole-line solution of the original field that stays in a small ball (equilibria, periodic
orbits, homoclinic orbits near the point).

Scope.
* A real Banach space `E` (the theorem on `ℝⁿ` takes `E = State n`), `A`, `P` with `P² = P`,
  `AP = PA` (`IsCommutingProjection`), the centre–stable dichotomy `‖e^{tA}P‖ ≤ K e^{ε|t|}` (all
  `t`), `‖e^{tA}(1 − P)‖ ≤ K e^{−βt}` (`t ≥ 0`) as theorem hypotheses.
* The characterization is proved for the graph map built by the Lyapunov–Perron method
  (`CenterManifold.exists_graph_of_lipschitz`, data of `exists_centerManifold_contDiff_data`):
  through every graph point passes a whole-line solution of the cutoff field on the graph.
  Centre manifolds are not unique; other centre manifolds need not contain the small bounded
  solutions of the cutoff field, but each contains those of the original field only where it
  agrees with the constructed one.
* The theorem on `ℝⁿ` combines the `C¹` construction (`theorem/Dynamics/CenterManifoldSmooth.lean`)
  with the quadratic part of any tangent centre manifold
  (`hasQuadraticPart_of_invariantGraph`, `theorem/Dynamics/CenterManifoldApproxAny.lean`).
  Generic; nothing here describes a physical system (foundation).

Source: Carr, *Applications of Centre Manifold Theory* (1981), Ch. 2, §2.4 (the centre manifold
contains all solutions that stay near the equilibrium for all time); Vanderbauwhede, "Centre
manifolds, normal forms and elementary bifurcations" (1989), §2, Theorem 2.1 (the Lyapunov–Perron
characterization of the centre manifold by bounded solutions); Kelley (1967).

Results.
* `mem_graph_of_globalSolution`: for a `δ`-Lipschitz cutoff `g`, `Kδκ < 1`, and a graph map
  carrying whole-line solutions of weighted growth through its points, every whole-line solution
  of `ẋ = A x + g(x)` of growth `C e^{η|t|}` stays on the graph (both are fixed points of the
  Lyapunov–Perron transform with the same centre datum: `LyapunovPerron.eq_lpMap_of_hasDerivAt`,
  `LyapunovPerron.fixedPoint_unique`).
* `exists_centerManifold_bounded` (`ℝⁿ`, `3ε < β`): a locally invariant Lipschitz centre manifold
  `h` of class `C¹` with `Dh(0) = 0` and quadratic part `H₀`, such that every whole-line solution
  of `ẋ = A x + f(x)` staying in the ball of radius `ρ` lies on its graph.
-/

noncomputable section
namespace powerlib.Dynamics.CenterManifold

open Set Filter Topology Asymptotics
open powerlib.Dynamics.LyapunovPerron

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {A P : E →L[ℝ] E}

/-- **Bounded whole-line solutions lie on the Lyapunov–Perron graph.** Let `g` be
`δ`-Lipschitz with `g 0 = 0` and `K δ κ < 1` (`κ = gapConst ε η β`), and let the graph map `h`
carry through every point `P u + h u` a whole-line solution of `ẋ = A x + g(x)` of growth
`C₁ ‖P u‖ e^{η|t|}` staying on the graph. Then every whole-line solution of `ẏ = A y + g(y)` with
`‖y(t)‖ ≤ C e^{η|t|}` stays on the graph. -/
@[tmio T, powerlib_foundation] theorem mem_graph_of_globalSolution
    (hP : IsCommutingProjection A P) {K ε η β C₁ C : ℝ} (hε : 0 ≤ ε) (hεη : ε < η)
    (hηβ : η < β) (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {g : E → E} {δ : NNReal} (hg : LipschitzWith δ g) (hg0 : g 0 = 0)
    (hk : K * δ * gapConst ε η β < 1) {h : E → E} (hh : IsGraphMap P h)
    (hglob : ∀ u, ∃ x : ℝ → E, x 0 = P u + h u ∧ (∀ t, HasDerivAt x (A (x t) + g (x t)) t) ∧
      (∀ t, x t ∈ graph P h) ∧ ∀ t, ‖x t‖ ≤ C₁ * ‖P u‖ * Real.exp (η * |t|))
    {y : ℝ → E} (hy : ∀ t, HasDerivAt y (A (y t) + g (y t)) t)
    (hyb : ∀ t, ‖y t‖ ≤ C * Real.exp (η * |t|)) (t : ℝ) : y t ∈ graph P h := by
  obtain ⟨x, hx0, hxd, hxg, hxb⟩ := hglob (y 0)
  have hη : 0 ≤ η := hε.trans hεη.le
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hxd t).continuousAt
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hy t).continuousAt
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (hyb 0); simpa using this
  have hCx : 0 ≤ C₁ * ‖P (y 0)‖ := by
    have := (norm_nonneg _).trans (hxb 0); simpa using this
  have hgb : ∀ {z : ℝ → E} {D : ℝ}, (∀ s, ‖z s‖ ≤ D * Real.exp (η * |s|)) →
      ∀ s, ‖g (z s)‖ ≤ (δ * D) * Real.exp (η * |s|) := fun hz s =>
    (hg.norm_le_mul hg0 _).trans (by rw [mul_assoc]; gcongr; exact hz s)
  have hP0 : P (x 0) = P (y 0) := by rw [hx0, map_add, hP.idem, hh.proj_apply, add_zero]
  have hx : ∀ t, x t = lpMap A P (P (y 0)) (fun s => g (x s)) t := fun t => by
    rw [eq_lpMap_of_hasDerivAt hP.commute hη hηβ hst (hg.continuous.comp hxc)
      (mul_nonneg δ.2 hCx) (hgb hxb) hxb hxd t, ← hP0, hP.lpMap_proj]
    rfl
  have hy' : ∀ t, y t = lpMap A P (P (y 0)) (fun s => g (y s)) t := fun t => by
    rw [eq_lpMap_of_hasDerivAt hP.commute hη hηβ hst (hg.continuous.comp hyc)
      (mul_nonneg δ.2 hC) (hgb hyb) hyb hy t, hP.lpMap_proj]
    rfl
  have he := fixedPoint_unique hε hεη hηβ hcen hst hg hg0 hk hxc hyc hxb hyb hx hy'
  rw [← he]
  exact hxg t

end Generic

/-! ## The state space `ℝⁿ` -/

section State

variable {n : ℕ} {A P : State n →L[ℝ] State n}

/-- **A centre manifold containing the small bounded solutions** (centre–stable case, `3ε < β`).
For `f` of class `C¹` with `f(0) = 0`, `Df(0) = 0`, `f(x) = Q(x, x) + O(‖x‖³)` and `H₀` (values in
`ker P`) solving the homological equation, there are `ρ > 0` and a Lipschitz graph map `h` of class
`C¹` with `Dh(0) = 0` and quadratic part `H₀`, whose graph is locally invariant in the ball of
radius `ρ` and contains every whole-line solution of `ẋ = A x + f(x)` staying in that ball. -/
@[tmio T, powerlib_foundation] theorem exists_centerManifold_bounded
    (hP : IsCommutingProjection A P) {K ε β : ℝ} (hε : 0 ≤ ε) (hgap : 3 * ε < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {f : State n → State n} (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0) (hDf : fderiv ℝ f 0 = 0)
    {Q H₀ : State n →L[ℝ] State n →L[ℝ] State n}
    (hf2 : (fun x => f x - Q x x) =O[𝓝 0] fun x => ‖x‖ ^ 3)
    (hhom : IsHomological A P Q H₀) (hPH : ∀ u v, P (H₀ u v) = 0) :
    ∃ ρ > 0, ∃ h : State n → State n, ∃ L : NNReal, IsGraphMap P h ∧ LipschitzWith L h ∧
      HasQuadraticPart P h H₀ ∧ ContDiff ℝ 1 h ∧ fderiv ℝ h 0 = 0 ∧
      (∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
        φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h) ∧
      ∀ φ : ℝ → State n, (∀ t, HasDerivAt φ (fullField A f (φ t)) t) → (∀ t, ‖φ t‖ < ρ) →
        ∀ t, φ t ∈ graph P h := by
  have hK := nonneg_of_stable_bound hst
  have hεβ : ε < β := by linarith
  set η := ε + (β - ε) / 3 with hηdef
  set ζ := ε + 2 * (β - ε) / 3 with hζdef
  have hεη : ε < η := by rw [hηdef]; linarith
  have hηζ : η < ζ := by rw [hηdef, hζdef]; linarith
  have hζβ : ζ < β := by rw [hζdef]; linarith
  have hκη := gapConst_pos hεη (hηζ.trans hζβ)
  have hκζ := gapConst_pos (hεη.trans hηζ) hζβ
  set S := K * (gapConst ε η β + gapConst ε ζ β) with hS
  have hS0 : 0 ≤ S := mul_nonneg hK (add_pos hκη hκζ).le
  set δ : ℝ := 1 / (2 * (S + 1)) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; exact div_pos one_pos (by linarith)
  have hδS : δ * S < 1 := by
    rw [hδdef, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    linarith
  have hkη : K * δ * gapConst ε η β < 1 := by
    have : K * δ * gapConst ε η β ≤ δ * S := by
      rw [hS]; nlinarith [mul_nonneg (mul_nonneg hδ.le hK) hκζ.le]
    linarith
  have hkζ : K * δ * gapConst ε ζ β < 1 := by
    have : K * δ * gapConst ε ζ β ≤ δ * S := by
      rw [hS]; nlinarith [mul_nonneg (mul_nonneg hδ.le hK) hκη.le]
    linarith
  obtain ⟨ρ, hρ, g, hg, hg0, -, hgf, h, L, hh, hL, -, hh1, hfd0, -, hinv, hglob⟩ :=
    exists_centerManifold_contDiff_data hP hε hεη hηζ hζβ hcen hst hf.contDiffAt hf0 hDf hδ
      hkη hkζ
  have hfs : HasStrictFDerivAt f (0 : State n →L[ℝ] State n) 0 := by
    have := (hf.contDiffAt (x := 0)).hasStrictFDerivAt (by norm_num)
    rwa [hDf] at this
  have hhs : HasStrictFDerivAt h (0 : State n →L[ℝ] State n) 0 := by
    have := (hh1.contDiffAt (x := 0)).hasStrictFDerivAt (by norm_num)
    rwa [hfd0] at this
  have hinv' : ∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
      φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h :=
    hinv
  have hk' : K * (Real.toNNReal δ : ℝ) * gapConst ε η β < 1 := by
    rwa [Real.coe_toNNReal _ hδ.le]
  refine ⟨ρ, hρ, h, L, hh, hL, hasQuadraticPart_of_invariantGraph hP hε hgap hcen hst hf0 hfs
    hf2 hhom hPH hh hhs hρ hinv', hh1, hfd0, hinv', fun φ hφ hφρ t => ?_⟩
  have hη : 0 ≤ η := hε.trans hεη.le
  refine mem_graph_of_globalSolution hP hε hεη (hηζ.trans hζβ) hcen hst hg hg0 hk' hh hglob
    (C := ρ) (fun t => ?_) (fun t => ?_) t
  · rw [hgf (φ t) (hφρ t).le]
    exact hφ t
  · have h1 : 1 ≤ Real.exp (η * |t|) := Real.one_le_exp (by positivity)
    nlinarith [hφρ t]

end State

end powerlib.Dynamics.CenterManifold
