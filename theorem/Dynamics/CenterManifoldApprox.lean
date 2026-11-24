import theorem.Dynamics.CenterManifold
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Carr's approximation theorem for centre manifolds (foundation)

A candidate graph `φ` over `range P` whose invariance defect is `O(‖u‖^q)` approximates the
centre manifold to the same order: `h(u) − φ(u) = O(‖u‖^q)`. This is how centre manifolds are
computed in practice (Taylor coefficients from the invariance equation, e.g. the homological
equation of `theorem/Dynamics/CenterReduction.lean`).

Scope.
* A finite-dimensional real inner product space `E` (the applications take `E = State n`), the
  setting of `theorem/Dynamics/CenterManifold.lean`: a projection `P` commuting with `A`, the
  dichotomy `‖e^{tA}P‖ ≤ K e^{ε|t|}` (all `t`), `‖e^{tA}(1 − P)‖ ≤ K e^{−βt}` (`t ≥ 0`), and
  `f(0) = 0` with strict derivative `0` at `0` (`C¹` with `Df(0) = 0` on `ℝⁿ`; no third
  derivative is needed). The gap condition is `q ε < β` with `q ≥ 1`: the weight `e^{η|t|}` of
  the construction must satisfy `ε < η` and `qη < β`.
* A candidate `φ : E → E` is `C¹` near `0`, `φ(0) = 0`, `Dφ(0) = 0`, with values in `ker P`; its
  invariance defect is `invarianceDefect A P f φ` (Carr's `(Mφ)(u)`), its order on `range P` is
  `IsOrder` (`theorem/Dynamics/CenterManifoldDefs.lean`).
* The approximation is proved here for the centre manifold that the theorem constructs (built
  with a weight adapted to `q`). Centre manifolds are not unique: for every graph map with strict
  derivative `0` at `0` whose graph is locally invariant it is `isOrder_sub_of_invariantGraph`
  (`theorem/Dynamics/CenterManifoldApproxAny.lean`). Generic; nothing here describes a physical
  system (foundation).

Source: Carr, *Applications of Centre Manifold Theory* (1981), Ch. 2, Theorem 3 (approximation);
the proof here works along the solutions of the Lyapunov–Perron construction instead of Carr's
space of Lipschitz graphs: `z = (1 − P)x − ψ(P x)` solves `ż = A z + b` with
`‖b‖ ≤ M ‖P x‖^q + (‖1 − P‖ + ‖P‖) δ ‖z‖`, and the stable integral representation of `z` is a
contraction for the weight `e^{−qηt}` on `t ≤ 0` (Vanderbauwhede, "Centre manifolds, normal
forms and elementary bifurcations" (1989), §2; Kelley (1967)).

Results.
* `exists_contDiff_cutoff`: `φ` agrees near `0` with a globally `C¹` map `ψ` into `ker P` with
  `ψ(0) = 0` and `‖Dψ‖ ≤ 1` (a scaled smooth bump `χ(x/r) φ(x)`).
* `exists_defect_bound`: the defect of `ψ` for the cutoff field `g` is at most `M ‖v‖^q` on all
  of `range P` (equal to the defect of `φ` near `0`, linear growth away from `0`).
* `IsCommutingProjection.compl_expFlow`, `IsCommutingProjection.compl_lpMap` (the stable
  component of the Lyapunov–Perron transform is `∫_{−∞}^t e^{(t−s)A}(1 − P) b(s) ds`).
* `exists_forcing_graphDeviation`: along a solution of `ẋ = A x + g(x)` the deviation
  `z = (1 − P)x − ψ(P x)` solves `ż = A z + b`, `‖b‖ ≤ M ‖P x‖^q + (‖1 − P‖ + ‖P‖) δ ‖z‖`.
* `norm_sub_cutoff_le` (Carr's estimate): `‖h u − ψ(P u)‖ ≤ C ‖P u‖^q` for every `u`.
* **The theorem**: `exists_centerManifold_approx_of_hasStrictFDerivAt` (finite-dimensional inner
  product space) and `exists_centerManifold_approx` (`ℝⁿ`, `C¹`, canonical local-invariance
  form): a centre manifold as in `exists_centerManifold`, with
  `IsOrder P (invarianceDefect A P f φ) q → IsOrder P (fun u => h u − φ u) q` for every
  admissible candidate `φ`. Combined with
  `isOrder_invarianceDefect_quadGraph` (`q = 3`) it supplies the hypothesis
  `hcarr` of `HasQuadraticPart.apply_eq_of_homological`.
-/

noncomputable section
namespace powerlib.Dynamics.CenterManifold

open Set Filter Topology MeasureTheory Asymptotics Metric
open powerlib.Dynamics.LyapunovPerron

section Bump

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A `C¹` cutoff of a candidate graph.** A map `φ` of class `C¹` near `0` with `φ 0 = 0`,
`Dφ(0) = 0` and values in `ker P` agrees near `0` with a globally `C¹` map `ψ` with `ψ 0 = 0`,
`‖Dψ‖ ≤ 1` everywhere and values in `ker P`: `ψ = χ(x/r) φ` for a smooth bump `χ` and `r`
small. -/
@[tmio T, powerlib_foundation] theorem exists_contDiff_cutoff {P : E →L[ℝ] E} {φ : E → E}
    (hφ : ContDiffAt ℝ 1 φ 0) (hφ0 : φ 0 = 0) (hDφ : fderiv ℝ φ 0 = 0)
    (hφP : ∀ x, P (φ x) = 0) :
    ∃ r > 0, ∃ ψ : E → E, ContDiff ℝ 1 ψ ∧ ψ 0 = 0 ∧ (∀ x, ‖fderiv ℝ ψ x‖ ≤ 1) ∧
      (∀ x, P (ψ x) = 0) ∧ ∀ x, ‖x‖ < r → ψ x = φ x := by
  -- the fixed bump and the bound of its derivative
  let b : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  have hbC : ContDiff ℝ 1 b := b.contDiff
  obtain ⟨C, hC⟩ := (hbC.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (b.hasCompactSupport.fderiv (𝕜 := ℝ))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  -- a ball on which `φ` is `C¹` with small derivative
  set θ : ℝ := 1 / (1 + 2 * C) with hθ
  have hθ0 : 0 < θ := by positivity
  obtain ⟨R₀, hR₀, hR₀C⟩ := Metric.eventually_nhds_iff.1 (hφ.eventually (by simp))
  have hcont : ContinuousAt (fderiv ℝ φ) 0 := hφ.continuousAt_fderiv (by simp)
  obtain ⟨R₁, hR₁, hR₁b⟩ := Metric.eventually_nhds_iff.1
    (hcont.eventually (closedBall_mem_nhds (fderiv ℝ φ 0) hθ0))
  set r := min R₀ R₁ / 4 with hr
  have hr0 : 0 < r := by positivity
  have h2rR₀ : 2 * r < R₀ := by
    have := min_le_left R₀ R₁; rw [hr]; linarith
  have h2rR₁ : 2 * r < R₁ := by
    have := min_le_right R₀ R₁; rw [hr]; linarith
  have hball : ∀ y : E, ‖y‖ ≤ 2 * r →
      ContDiffAt ℝ 1 φ y ∧ ‖fderiv ℝ φ y‖ ≤ θ := fun y hy => by
    refine ⟨hR₀C (by rw [dist_zero_right]; linarith), ?_⟩
    have := hR₁b (y := y) (by rw [dist_zero_right]; linarith)
    rwa [hDφ, dist_zero_right] at this
  have hφn : ∀ y : E, ‖y‖ ≤ 2 * r → ‖φ y‖ ≤ θ * ‖y‖ := fun y hy => by
    have h := (convex_closedBall (0 : E) (2 * r)).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => ((hball z (by simpa using hz)).1.differentiableAt one_ne_zero))
      (fun z hz => (hball z (by simpa using hz)).2) (mem_closedBall_self (by positivity))
      (show y ∈ closedBall (0 : E) (2 * r) by simpa using hy)
    simpa [hφ0] using h
  -- the scaled bump
  set χ : E → ℝ := fun x => b (r⁻¹ • x) with hχ
  have hχC : ContDiff ℝ 1 χ := hbC.comp (contDiff_id.const_smul r⁻¹)
  have hχ1 : ∀ x : E, ‖x‖ ≤ r → χ x = 1 := fun x hx => by
    refine b.one_of_mem_closedBall ?_
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr0]
    change r⁻¹ * ‖x‖ ≤ 1
    rw [inv_mul_le_iff₀ hr0, mul_one]; exact hx
  have hχ0 : ∀ x : E, 2 * r ≤ ‖x‖ → χ x = 0 := fun x hx => by
    refine b.zero_of_le_dist ?_
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr0]
    change (2 : ℝ) ≤ r⁻¹ * ‖x‖
    rw [le_inv_mul_iff₀ hr0]; linarith
  have hχd : ∀ x : E, HasFDerivAt χ
      ((fderiv ℝ b (r⁻¹ • x)).comp (r⁻¹ • ContinuousLinearMap.id ℝ E)) x := fun x =>
    ((hbC.differentiable one_ne_zero (r⁻¹ • x)).hasFDerivAt).comp x
      ((hasFDerivAt_id x).const_smul r⁻¹)
  have hχdn : ∀ x : E, ‖(fderiv ℝ b (r⁻¹ • x)).comp (r⁻¹ • ContinuousLinearMap.id ℝ E)‖ ≤
      C * r⁻¹ := fun x => by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine mul_le_mul (hC _) ?_ (norm_nonneg _) hC0
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr0]
    exact mul_le_of_le_one_right (by positivity) (ContinuousLinearMap.norm_id_le)
  set ψ : E → E := fun x => χ x • φ x with hψ
  have hψ0 : ∀ x : E, 2 * r < ‖x‖ → ψ =ᶠ[𝓝 x] fun _ => 0 := fun x hx => by
    have hopen : IsOpen {y : E | 2 * r < ‖y‖} := isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds hx] with y hy
    simp [ψ, hχ0 y (le_of_lt hy)]
  refine ⟨r, hr0, ψ, contDiff_iff_contDiffAt.2 fun x => ?_, by simp [ψ, hφ0], fun x => ?_,
    fun x => by simp [ψ, hφP], fun x hx => by simp [ψ, hχ1 x hx.le]⟩
  · rcases le_or_gt ‖x‖ (2 * r) with hx | hx
    · exact hχC.contDiffAt.smul (hball x hx).1
    · exact contDiffAt_const.congr_of_eventuallyEq (hψ0 x hx)
  · rcases le_or_gt ‖x‖ (2 * r) with hx | hx
    · have hφd : HasFDerivAt φ (fderiv ℝ φ x) x :=
        ((hball x hx).1.differentiableAt one_ne_zero).hasFDerivAt
      have hd := (hχd x).smul hφd
      rw [show ψ = χ • φ from rfl, hd.fderiv]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (b.nonneg' _),
        ContinuousLinearMap.norm_smulRight_apply]
      have h1 : χ x * ‖fderiv ℝ φ x‖ ≤ θ :=
        (mul_le_of_le_one_left (norm_nonneg _) (b.le_one)).trans (hball x hx).2
      have h2 : ‖(fderiv ℝ b (r⁻¹ • x)).comp (r⁻¹ • ContinuousLinearMap.id ℝ E)‖ * ‖φ x‖ ≤
          C * r⁻¹ * (θ * (2 * r)) :=
        mul_le_mul (hχdn x) ((hφn x hx).trans (by gcongr)) (norm_nonneg _) (by positivity)
      have h3 : C * r⁻¹ * (θ * (2 * r)) = 2 * C * θ := by field_simp
      have h4 : θ + 2 * C * θ = 1 := by rw [hθ]; field_simp
      linarith
    · rw [(hψ0 x hx).fderiv_eq, fderiv_const_apply, norm_zero]
      exact zero_le_one

end Bump

/-! ## The global defect bound -/

section Defect

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A P : E →L[ℝ] E}

/-- **The defect of the cutoff graph is globally `O(‖v‖^q)`.** If `ψ = φ` near `0`, `g = f` on a
ball, `ψ` is `1`-Lipschitz with `‖Dψ‖ ≤ 1`, `g` is `δ`-Lipschitz with `g 0 = 0`, and the defect of
`φ` for `f` is `O(‖u‖^q)` on `range P` (`q ≥ 1`), then the defect of `ψ` for `g` is bounded by
`M ‖v‖^q` on all of `range P`: near `0` it is the defect of `φ`, away from `0` it grows
linearly. -/
@[tmio T, powerlib_foundation] theorem exists_defect_bound {f g φ ψ : E → E} {δ : NNReal}
    {ρ q r : ℝ} (hq : 1 ≤ q) (hρ : 0 < ρ) (hr : 0 < r)
    (hg : LipschitzWith δ g) (hgf : ∀ y, ‖y‖ ≤ ρ → g y = f y) (hg0 : g 0 = 0)
    (hψd : ∀ x, ‖fderiv ℝ ψ x‖ ≤ 1) (hψn : ∀ x, ‖ψ x‖ ≤ ‖x‖)
    (hψφ : ∀ x, ‖x‖ < r → ψ x = φ x) (hdef : IsOrder P (invarianceDefect A P f φ) q) :
    ∃ M, 0 ≤ M ∧ ∀ v, P v = v → ‖invarianceDefect A P g ψ v‖ ≤ M * ‖v‖ ^ q := by
  obtain ⟨c, hc⟩ := hdef.bound
  rw [eventually_nhdsWithin_iff] at hc
  obtain ⟨r₂, hr₂, hc⟩ := Metric.eventually_nhds_iff.1 hc
  set r₁ := min r (min r₂ (ρ / 2)) with hr₁
  have hr₁0 : 0 < r₁ := lt_min hr (lt_min hr₂ (by positivity))
  set c₁ := ‖P‖ * ‖A‖ + 2 * ‖P‖ * δ + ‖1 - P‖ * ‖A‖ + 2 * ‖1 - P‖ * δ with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  refine ⟨max (max c 0) (c₁ * r₁ ^ (1 - q)), by positivity, fun v hv => ?_⟩
  have hvq : 0 ≤ ‖v‖ ^ q := Real.rpow_nonneg (norm_nonneg _) _
  rcases lt_or_ge ‖v‖ r₁ with hvr | hvr
  · -- near `0` the defect is the defect of `φ`
    have hvr' : ‖v‖ < r := hvr.trans_le (min_le_left _ _)
    have hev : ψ =ᶠ[𝓝 v] φ :=
      Filter.eventuallyEq_of_mem ((Metric.isOpen_ball (x := (0 : E)) (ε := r)).mem_nhds
        (by rw [mem_ball, dist_zero_right]; exact hvr'))
        fun y hy => hψφ y (by rwa [mem_ball, dist_zero_right] at hy)
    have hψv : ψ v = φ v := hψφ v hvr'
    have hgv : g (v + ψ v) = f (v + φ v) := by
      rw [← hψv]
      refine hgf _ ((norm_add_le _ _).trans ?_)
      have := hψn v
      have : ‖v‖ < ρ / 2 := hvr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      linarith
    have heq : invarianceDefect A P g ψ v = invarianceDefect A P f φ v := by
      simp only [invarianceDefect, reducedField, normalField, hev.fderiv_eq, hψv]
      rw [← hψv, hgv, hψv]
    rw [heq]
    have := hc (y := v) (by rw [dist_zero_right]
                            exact hvr.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
      ⟨v, hv⟩
    rw [Real.norm_eq_abs, abs_of_nonneg hvq] at this
    exact this.trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) hvq)
  · -- away from `0` the defect grows linearly
    have hw : ‖v + ψ v‖ ≤ 2 * ‖v‖ := (norm_add_le _ _).trans (by linarith [hψn v])
    have hgw : ‖g (v + ψ v)‖ ≤ δ * (2 * ‖v‖) := by
      refine (by simpa [hg0] using hg.norm_sub_le (v + ψ v) 0 : ‖g (v + ψ v)‖ ≤ _).trans ?_
      gcongr
    have hlin : ‖invarianceDefect A P g ψ v‖ ≤ c₁ * ‖v‖ := by
      simp only [invarianceDefect, reducedField, normalField]
      refine (norm_sub_le _ _).trans ?_
      have hAv : ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
      have hAψ : ‖A (ψ v)‖ ≤ ‖A‖ * ‖v‖ :=
        (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hψn v) (norm_nonneg _))
      have hP1 : ‖P (A v)‖ ≤ ‖P‖ * (‖A‖ * ‖v‖) :=
        (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left hAv (norm_nonneg _))
      have hP2 : ‖P (g (v + ψ v))‖ ≤ ‖P‖ * (δ * (2 * ‖v‖)) :=
        (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left hgw (norm_nonneg _))
      have hQ1 : ‖(1 - P) (A (ψ v))‖ ≤ ‖1 - P‖ * (‖A‖ * ‖v‖) :=
        ((1 - P).le_opNorm _).trans (mul_le_mul_of_nonneg_left hAψ (norm_nonneg _))
      have hQ2 : ‖(1 - P) (g (v + ψ v))‖ ≤ ‖1 - P‖ * (δ * (2 * ‖v‖)) :=
        ((1 - P).le_opNorm _).trans (mul_le_mul_of_nonneg_left hgw (norm_nonneg _))
      have e1 : ‖fderiv ℝ ψ v (P (A v) + P (g (v + ψ v)))‖ ≤
          1 * (‖P‖ * (‖A‖ * ‖v‖) + ‖P‖ * (δ * (2 * ‖v‖))) :=
        (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hψd v)
          ((norm_add_le _ _).trans (add_le_add hP1 hP2)) (norm_nonneg _) zero_le_one)
      have e2 : ‖(1 - P) (A (ψ v)) + (1 - P) (g (v + ψ v))‖ ≤
          ‖1 - P‖ * (‖A‖ * ‖v‖) + ‖1 - P‖ * (δ * (2 * ‖v‖)) :=
        (norm_add_le _ _).trans (add_le_add hQ1 hQ2)
      calc _ ≤ 1 * (‖P‖ * (‖A‖ * ‖v‖) + ‖P‖ * (δ * (2 * ‖v‖))) +
            (‖1 - P‖ * (‖A‖ * ‖v‖) + ‖1 - P‖ * (δ * (2 * ‖v‖))) := add_le_add e1 e2
        _ = c₁ * ‖v‖ := by rw [hc₁]; ring
    have hvpos : 0 < ‖v‖ := hr₁0.trans_le hvr
    have hsplit : ‖v‖ = ‖v‖ ^ q * ‖v‖ ^ (1 - q) := by
      rw [← Real.rpow_add hvpos, add_sub_cancel, Real.rpow_one]
    have hpow : ‖v‖ ^ (1 - q) ≤ r₁ ^ (1 - q) :=
      Real.rpow_le_rpow_of_nonpos hr₁0 hvr (by linarith)
    calc ‖invarianceDefect A P g ψ v‖ ≤ c₁ * ‖v‖ := hlin
      _ = c₁ * ‖v‖ ^ (1 - q) * ‖v‖ ^ q := by
          conv_lhs => rw [hsplit]
          ring
      _ ≤ c₁ * r₁ ^ (1 - q) * ‖v‖ ^ q := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hvq

end Defect

/-! ## Carr's estimate -/

section Carr

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {A P : E →L[ℝ] E}

omit [CompleteSpace E] in
@[tmio T, powerlib_foundation] theorem IsCommutingProjection.compl_expFlow
    (hP : IsCommutingProjection A P) (τ : ℝ) (y : E) :
    (1 - P) (expFlow A τ y) = expFlow A τ ((1 - P) y) := by
  change ((1 - P) * expFlow A τ) y = (expFlow A τ * (1 - P)) y
  rw [(expFlow_commute ((Commute.one_right A).sub_right hP.commute) τ).eq]

/-- The stable component of the Lyapunov–Perron transform:
`(1 − P) lpMap u b t = ∫_{−∞}^t e^{(t−s)A}(1 − P) b(s) ds`. -/
@[tmio T, powerlib_foundation] theorem IsCommutingProjection.compl_lpMap
    (hP : IsCommutingProjection A P) {K β η C : ℝ} {b : ℝ → E} (hb : Continuous b)
    (hC : 0 ≤ C) (hbC : ∀ s, ‖b s‖ ≤ C * Real.exp (η * |s|)) (hη : 0 ≤ η) (hηβ : η < β)
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t))) (u : E) (t : ℝ) :
    (1 - P) (lpMap A P u b t) = ∫ s in Iic t, expFlow A (t - s) ((1 - P) (b s)) := by
  have hcP : Continuous fun s => expFlow A (t - s) (P (b s)) :=
    (continuous_expFlow.comp (continuous_const.sub continuous_id)).clm_apply (P.continuous.comp hb)
  have hI := (integrableOn_stable hb hC hbC hη hηβ hst t).1
  rw [lpMap_eq hb hC hbC hη hηβ hst u t, map_add, map_add, hP.compl_expFlow, hP.compl_proj,
    map_zero, zero_add, ← (1 - P).intervalIntegral_comp_comm (hcP.intervalIntegrable _ _),
    ← (1 - P).integral_comp_comm hI]
  have h1 : ∀ s, (1 - P) (expFlow A (t - s) (P (b s))) = 0 := fun s => by
    rw [hP.compl_expFlow, hP.compl_proj, map_zero]
  have h2 : ∀ s, (1 - P) (expFlow A (t - s) ((1 - P) (b s))) =
      expFlow A (t - s) ((1 - P) (b s)) := fun s => by
    rw [hP.compl_expFlow, compl_apply P ((1 - P) (b s)), hP.proj_compl, sub_zero]
  simp only [h1, h2, intervalIntegral.integral_zero, zero_add]

omit [CompleteSpace E] in
/-- **The deviation from a candidate graph along a solution.** If `x` solves
`ẋ = A x + g(x)` on a set of times `s` (`g` `δ`-Lipschitz) and `ψ` is a `C¹` map into `ker P`
with `‖Dψ‖ ≤ 1` whose invariance defect for `g` is at most `M ‖v‖^q` on `range P`, then the
deviation `z = (1 − P)x − ψ(P x)` solves `ż = A z + b` on `s` with a forcing `b` continuous on
`s` and `‖b‖ ≤ M ‖P x‖^q + (‖1 − P‖ + ‖P‖) δ ‖z‖`: the defect at `P x` plus a Lipschitz
remainder, `b = (1 − P) g(x) + A ψ(P x) − Dψ(P x)(A P x + P g(x))`. -/
@[tmio T, powerlib_foundation] theorem exists_forcing_graphDeviation
    (hP : IsCommutingProjection A P) {g ψ : E → E} {δ : NNReal} (hg : LipschitzWith δ g)
    (hψ : ContDiff ℝ 1 ψ) (hψd : ∀ x, ‖fderiv ℝ ψ x‖ ≤ 1) (hψP : ∀ x, P (ψ x) = 0) {M q : ℝ}
    (hdef : ∀ v, P v = v → ‖invarianceDefect A P g ψ v‖ ≤ M * ‖v‖ ^ q)
    {x : ℝ → E} {s : Set ℝ} (hx : ∀ t ∈ s, HasDerivWithinAt x (A (x t) + g (x t)) s t) :
    ∃ b : ℝ → E, ContinuousOn b s ∧
      (∀ t ∈ s, HasDerivWithinAt (fun t => (1 - P) (x t) - ψ (P (x t)))
        (A ((1 - P) (x t) - ψ (P (x t))) + b t) s t) ∧
      ∀ t, ‖b t‖ ≤ M * ‖P (x t)‖ ^ q + (‖1 - P‖ + ‖P‖) * δ * ‖(1 - P) (x t) - ψ (P (x t))‖ := by
  have hxc : ContinuousOn x s := fun t ht => (hx t ht).continuousWithinAt
  set v : ℝ → E := fun t => P (x t) with hv
  set z : ℝ → E := fun t => (1 - P) (x t) - ψ (v t) with hz
  set b : ℝ → E := fun t =>
    (1 - P) (g (x t)) + A (ψ (v t)) - fderiv ℝ ψ (v t) (A (v t) + P (g (x t))) with hb
  have hcA : ∀ y, (1 - P) (A y) = A ((1 - P) y) := fun y => by
    rw [compl_apply, compl_apply, map_sub, hP.comm]
  have hPA : ∀ y, P (A y) = A (P y) := fun y => (hP.comm y).symm
  have hvc : ContinuousOn v s := P.continuous.comp_continuousOn hxc
  have hgc : ContinuousOn (fun t => g (x t)) s := hg.continuous.comp_continuousOn hxc
  have hbc : ContinuousOn b s := by
    have h1 : ContinuousOn (fun t => (1 - P) (g (x t))) s :=
      (1 - P).continuous.comp_continuousOn hgc
    have h2 : ContinuousOn (fun t => A (ψ (v t))) s :=
      A.continuous.comp_continuousOn (hψ.continuous.comp_continuousOn hvc)
    have h3 : ContinuousOn (fun t => fderiv ℝ ψ (v t) (A (v t) + P (g (x t)))) s :=
      ((hψ.continuous_fderiv one_ne_zero).comp_continuousOn hvc).clm_apply
        ((A.continuous.comp_continuousOn hvc).add (P.continuous.comp_continuousOn hgc))
    exact (h1.add h2).sub h3
  -- the equation of `z`
  have hzd : ∀ t ∈ s, HasDerivWithinAt z (A (z t) + b t) s t := fun t ht => by
    have h1 : HasDerivWithinAt (fun t => (1 - P) (x t)) ((1 - P) (A (x t) + g (x t))) s t :=
      (1 - P).hasFDerivAt.comp_hasDerivWithinAt t (hx t ht)
    have hvd : HasDerivWithinAt v (P (A (x t) + g (x t))) s t :=
      P.hasFDerivAt.comp_hasDerivWithinAt t (hx t ht)
    have h2 : HasDerivWithinAt (fun t => ψ (v t)) (fderiv ℝ ψ (v t) (P (A (x t) + g (x t))))
        s t := ((hψ.differentiable one_ne_zero (v t)).hasFDerivAt).comp_hasDerivWithinAt t hvd
    refine (h1.sub h2).congr_deriv ?_
    simp only [hz, hb, hv, map_add, map_sub, hcA, hPA]
    abel
  -- the forcing: defect plus a Lipschitz remainder
  set y : ℝ → E := fun t => v t + ψ (v t) with hy
  have hxy : ∀ t, x t - y t = z t := fun t => by
    simp only [hy, hz, hv, compl_apply]; abel
  have hbN : ∀ t, b t = -(invarianceDefect A P g ψ (v t)) + (1 - P) (g (x t) - g (y t)) -
      fderiv ℝ ψ (v t) (P (g (x t) - g (y t))) := fun t => by
    have hPv : P (A (v t)) = A (v t) := by simp only [hv]; rw [hPA, hP.idem]
    have hQψ : (1 - P) (A (ψ (v t))) = A (ψ (v t)) := by
      rw [hcA, compl_apply, hψP, sub_zero]
    simp only [invarianceDefect, reducedField, normalField, hPv, hQψ, hb, hy, map_add, map_sub]
    abel
  refine ⟨b, hbc, hzd, fun t => ?_⟩
  change ‖b t‖ ≤ M * ‖v t‖ ^ q + (‖1 - P‖ + ‖P‖) * δ * ‖z t‖
  rw [hbN t]
  have hN := hdef (v t) (hP.idem (x t))
  have hgz : ‖g (x t) - g (y t)‖ ≤ δ * ‖z t‖ := by
    rw [← hxy t]; simpa [dist_eq_norm] using hg.dist_le_mul (x t) (y t)
  have e1 : ‖(1 - P) (g (x t) - g (y t))‖ ≤ ‖1 - P‖ * (δ * ‖z t‖) :=
    ((1 - P).le_opNorm _).trans (mul_le_mul_of_nonneg_left hgz (norm_nonneg _))
  have e2 : ‖fderiv ℝ ψ (v t) (P (g (x t) - g (y t)))‖ ≤ 1 * (‖P‖ * (δ * ‖z t‖)) :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hψd _)
      ((P.le_opNorm _).trans (mul_le_mul_of_nonneg_left hgz (norm_nonneg _))) (norm_nonneg _)
      zero_le_one)
  calc _ ≤ ‖-(invarianceDefect A P g ψ (v t)) + (1 - P) (g (x t) - g (y t))‖ +
        ‖fderiv ℝ ψ (v t) (P (g (x t) - g (y t)))‖ := norm_sub_le _ _
    _ ≤ ‖invarianceDefect A P g ψ (v t)‖ + ‖(1 - P) (g (x t) - g (y t))‖ +
        ‖fderiv ℝ ψ (v t) (P (g (x t) - g (y t)))‖ := by
        gcongr; exact (norm_add_le _ _).trans_eq (by rw [norm_neg])
    _ ≤ M * ‖v t‖ ^ q + ‖1 - P‖ * (δ * ‖z t‖) + 1 * (‖P‖ * (δ * ‖z t‖)) := by gcongr
    _ = M * ‖v t‖ ^ q + (‖1 - P‖ + ‖P‖) * δ * ‖z t‖ := by ring

/-- **Carr's estimate.** Let `h` be the graph map of the Lyapunov–Perron construction for a
`δ`-Lipschitz `g` (through every point `P u + h u` a solution of `ẋ = A x + g(x)` of growth
`C₁ ‖P u‖ e^{η|t|}`), and `ψ` a `C¹` map into `ker P` with `‖Dψ‖ ≤ 1`, `‖ψ x‖ ≤ ‖x‖`, whose
invariance defect for `g` is at most `M ‖v‖^q` on `range P`. If `qη < β` and
`K (‖1 − P‖ + ‖P‖) δ/(β − qη) < 1`, then `‖h u − ψ(P u)‖ ≤ C ‖P u‖^q`: along the solution,
`z = (1 − P)x − ψ(P x)` solves `ż = A z + b` with `‖b‖ ≤ M ‖P x‖^q + (‖1 − P‖ + ‖P‖) δ ‖z‖`,
and its stable integral representation on `t ≤ 0` contracts in the weight `e^{−qηt}`. -/
@[tmio T, powerlib_foundation] theorem norm_sub_cutoff_le (hP : IsCommutingProjection A P)
    {K β η q : ℝ} (hη : 0 ≤ η) (hq : 1 ≤ q) (hqη : q * η < β)
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {g h ψ : E → E} {δ : NNReal} (hg : LipschitzWith δ g) (hh : IsGraphMap P h) {C₁ : ℝ}
    (hC₁ : 0 ≤ C₁)
    (hglob : ∀ u, ∃ x : ℝ → E, x 0 = P u + h u ∧ (∀ t, HasDerivAt x (A (x t) + g (x t)) t) ∧
      ∀ t, ‖x t‖ ≤ C₁ * ‖P u‖ * Real.exp (η * |t|))
    (hψ : ContDiff ℝ 1 ψ) (hψd : ∀ x, ‖fderiv ℝ ψ x‖ ≤ 1) (hψn : ∀ x, ‖ψ x‖ ≤ ‖x‖)
    (hψP : ∀ x, P (ψ x) = 0) {M : ℝ} (hM : 0 ≤ M)
    (hdef : ∀ v, P v = v → ‖invarianceDefect A P g ψ v‖ ≤ M * ‖v‖ ^ q)
    (hsmall : K * ((‖1 - P‖ + ‖P‖) * δ) / (β - q * η) < 1) (u : E) :
    ‖h u - ψ (P u)‖ ≤ K * M * (‖P‖ * C₁) ^ q /
      ((β - q * η) * (1 - K * ((‖1 - P‖ + ‖P‖) * δ) / (β - q * η))) * ‖P u‖ ^ q := by
  have hK := nonneg_of_stable_bound hst
  have hβq : 0 < β - q * η := sub_pos.2 hqη
  have hq0 : 0 ≤ q := by linarith
  have hqη0 : 0 ≤ q * η := mul_nonneg hq0 hη
  obtain ⟨x, hx0, hxd, hxb⟩ := hglob u
  set a := ‖P u‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  set κ' : ℝ := (‖1 - P‖ + ‖P‖) * δ with hκ'
  have hκ'0 : 0 ≤ κ' := by positivity
  set k := K * κ' / (β - q * η) with hk
  have hk0 : 0 ≤ k := by positivity
  set v : ℝ → E := fun t => P (x t) with hv
  set z : ℝ → E := fun t => (1 - P) (x t) - ψ (v t) with hz
  obtain ⟨b, hbc', hzd', hbb'⟩ := exists_forcing_graphDeviation hP hg hψ hψd hψP hdef
    (s := univ) fun t _ => (hxd t).hasDerivWithinAt
  have hbc : Continuous b := continuousOn_univ.1 hbc'
  -- the equation of `z`
  have hzd : ∀ t, HasDerivAt z (A (z t) + b t) t := fun t =>
    hasDerivWithinAt_univ.1 (hzd' t (mem_univ t))
  have hPz : ∀ t, P (z t) = 0 := fun t => by
    simp only [hz, map_sub, hP.proj_compl, hψP, sub_zero]
  -- growth bounds
  have hvb : ∀ t, ‖v t‖ ≤ ‖P‖ * C₁ * a * Real.exp (η * |t|) := fun t =>
    (P.le_opNorm _).trans (by rw [mul_assoc, mul_assoc, ← mul_assoc C₁]; gcongr; exact hxb t)
  have hzb : ∀ t, ‖z t‖ ≤ (‖1 - P‖ + ‖P‖) * C₁ * a * Real.exp (η * |t|) := fun t => by
    calc ‖z t‖ ≤ ‖(1 - P) (x t)‖ + ‖ψ (v t)‖ := norm_sub_le _ _
      _ ≤ ‖1 - P‖ * ‖x t‖ + ‖P‖ * ‖x t‖ :=
          add_le_add ((1 - P).le_opNorm _) ((hψn _).trans (P.le_opNorm _))
      _ = (‖1 - P‖ + ‖P‖) * ‖x t‖ := by ring
      _ ≤ (‖1 - P‖ + ‖P‖) * (C₁ * a * Real.exp (η * |t|)) := by gcongr; exact hxb t
      _ = _ := by ring
  -- the forcing: defect plus a Lipschitz remainder
  have hbb : ∀ t, ‖b t‖ ≤ M * ‖v t‖ ^ q + κ' * ‖z t‖ := hbb'
  have hexpq : ∀ t, Real.exp (η * |t|) ≤ Real.exp (q * η * |t|) := fun t =>
    Real.exp_le_exp.2
      (by nlinarith [mul_nonneg (sub_nonneg.2 hq) (mul_nonneg hη (abs_nonneg t))])
  have hvq : ∀ t, ‖v t‖ ^ q ≤ (‖P‖ * C₁ * a) ^ q * Real.exp (q * η * |t|) := fun t => by
    refine (Real.rpow_le_rpow (norm_nonneg _) (hvb t) hq0).trans_eq ?_
    rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
    ring_nf
  set M' := M * (‖P‖ * C₁ * a) ^ q with hM'
  have hM'0 : 0 ≤ M' := by positivity
  set Cz := (‖1 - P‖ + ‖P‖) * C₁ * a with hCz
  have hCz0 : 0 ≤ Cz := by positivity
  have hbC : ∀ s, ‖b s‖ ≤ (M' + κ' * Cz) * Real.exp (q * η * |s|) := fun s => by
    calc ‖b s‖ ≤ M * ‖v s‖ ^ q + κ' * ‖z s‖ := hbb s
      _ ≤ M * ((‖P‖ * C₁ * a) ^ q * Real.exp (q * η * |s|)) +
          κ' * (Cz * Real.exp (q * η * |s|)) := by
          gcongr
          · exact hvq s
          · exact (hzb s).trans (mul_le_mul_of_nonneg_left (hexpq s) hCz0)
      _ = _ := by rw [hM']; ring
  have hzC : ∀ s, ‖z s‖ ≤ Cz * Real.exp (q * η * |s|) := fun s =>
    (hzb s).trans (mul_le_mul_of_nonneg_left (hexpq s) hCz0)
  -- the stable representation of `z`
  have hvoc := eq_lpMap_of_hasDerivAt hP.commute hqη0 hqη hst hbc (by positivity) hbC hzC hzd
  have hzst : ∀ t, z t = ∫ s in Iic t, expFlow A (t - s) ((1 - P) (b s)) := fun t => by
    have : z t = (1 - P) (z t) := by rw [compl_apply, hPz, sub_zero]
    rw [this, hvoc t, hP.compl_lpMap hbc (by positivity) hbC hqη0 hqη hst]
  -- the contraction on `t ≤ 0` in the weight `e^{−qηt}`
  have hstep : ∀ Z, (∀ i : Iic (0 : ℝ), ‖z i‖ ≤ Z * Real.exp (-(q * η * i))) →
      ∀ i : Iic (0 : ℝ), ‖z i‖ ≤ (k * Z + K * M' / (β - q * η)) *
        Real.exp (-(q * η * i)) := by
    intro Z hZ i
    have hZ0 : 0 ≤ Z := by
      have := (norm_nonneg _).trans (hZ ⟨0, Set.mem_Iic.2 le_rfl⟩); simpa using this
    obtain ⟨t, ht⟩ := i
    change ‖z t‖ ≤ _
    set G : ℝ → ℝ := fun s => K * Real.exp (-(β * t)) * (M' + κ' * Z) *
      Real.exp ((β - q * η) * s) with hG
    have hGi : IntegrableOn G (Iic t) := (integrableOn_exp_mul_Iic hβq t).const_mul _
    have hpt : ∀ s ∈ Iic t, ‖expFlow A (t - s) ((1 - P) (b s))‖ ≤ G s := by
      intro s hs
      have hs' : s ≤ t := hs
      have hs0 : s ≤ 0 := hs'.trans ht
      have hbs : ‖b s‖ ≤ (M' + κ' * Z) * Real.exp (-(q * η * s)) := by
        calc ‖b s‖ ≤ M * ‖v s‖ ^ q + κ' * ‖z s‖ := hbb s
          _ ≤ M * ((‖P‖ * C₁ * a) ^ q * Real.exp (q * η * |s|)) +
              κ' * (Z * Real.exp (-(q * η * s))) := by
              gcongr
              · exact hvq s
              · exact hZ ⟨s, hs0⟩
          _ = _ := by rw [abs_of_nonpos hs0, hM']; ring_nf
      calc ‖expFlow A (t - s) ((1 - P) (b s))‖ = ‖(expFlow A (t - s) * (1 - P)) (b s)‖ := rfl
        _ ≤ ‖expFlow A (t - s) * (1 - P)‖ * ‖b s‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ K * Real.exp (-(β * (t - s))) * ((M' + κ' * Z) * Real.exp (-(q * η * s))) :=
            mul_le_mul (hst _ (sub_nonneg.2 hs')) hbs (norm_nonneg _)
              (mul_nonneg hK (Real.exp_pos _).le)
        _ = G s := by
            simp only [hG]
            have e : Real.exp (-(β * (t - s))) * Real.exp (-(q * η * s)) =
                Real.exp (-(β * t)) * Real.exp ((β - q * η) * s) := by
              rw [← Real.exp_add, ← Real.exp_add]; ring_nf
            linear_combination (K * (M' + κ' * Z)) * e
    have hint : ∫ s in Iic t, G s =
        (k * Z + K * M' / (β - q * η)) * Real.exp (-(q * η * t)) := by
      simp only [hG]
      rw [integral_const_mul, integral_exp_mul_Iic hβq]
      have e : Real.exp (-(β * t)) * Real.exp ((β - q * η) * t) = Real.exp (-(q * η * t)) := by
        rw [← Real.exp_add]; ring_nf
      calc K * Real.exp (-(β * t)) * (M' + κ' * Z) * (Real.exp ((β - q * η) * t) / (β - q * η))
          = K * (M' + κ' * Z) / (β - q * η) *
            (Real.exp (-(β * t)) * Real.exp ((β - q * η) * t)) := by ring
        _ = K * (M' + κ' * Z) / (β - q * η) * Real.exp (-(q * η * t)) := by rw [e]
        _ = _ := by rw [hk]; ring
    rw [hzst t, ← hint]
    exact norm_integral_le_of_norm_le hGi (ae_restrict_of_forall_mem measurableSet_Iic hpt)
  have h0 : ∀ i : Iic (0 : ℝ), ‖z i‖ ≤ Cz * Real.exp (-(q * η * i)) := fun ⟨t, ht⟩ => by
    refine (hzb t).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCz0)
    rw [abs_of_nonpos ht]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sub_nonneg.2 hq) hη) ht]
  have hfin := le_of_contract hk0 hsmall h0 hstep ⟨0, Set.mem_Iic.2 le_rfl⟩
  -- read off `z 0 = h u − ψ (P u)`
  have hPx0 : P (x 0) = P u := by rw [hx0, map_add, hP.idem, hh.proj_apply, add_zero]
  have hz0 : z 0 = h u - ψ (P u) := by
    simp only [hz, hv, hPx0]
    rw [compl_apply, hPx0, hx0, add_sub_cancel_left]
  change ‖z 0‖ ≤ _ at hfin
  rw [hz0] at hfin
  refine hfin.trans_eq ?_
  rw [mul_zero, neg_zero, Real.exp_zero, mul_one, hM', Real.mul_rpow (by positivity) ha0, hk]
  field_simp

end Carr

/-! ## The approximation theorem -/

section Approx

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A P : E →L[ℝ] E}

/-- **Carr's approximation theorem** (centre–stable case). Under the dichotomy with
`q ε < β` (`q ≥ 1`), for `f` with `f(0) = 0` and strict derivative `0` at `0`, there is a
centre manifold — `ρ > 0`, a Lipschitz graph map `h`, `h(u) = o(‖u‖)`, locally invariant in the
ball of radius `ρ` — such that every candidate graph `φ` of class `C¹` near `0` with
`φ(0) = 0`, `Dφ(0) = 0`, values in `ker P` and invariance defect
`Dφ(u)(PAu + Pf(u + φ u)) − ((1 − P)Aφ(u) + (1 − P)f(u + φ u)) = O(‖u‖^q)` on `range P`
approximates it: `h(u) − φ(u) = O(‖u‖^q)` on `range P`. -/
@[tmio T, powerlib_foundation] theorem exists_centerManifold_approx_of_hasStrictFDerivAt
    (hP : IsCommutingProjection A P) {K ε β q : ℝ} (hε : 0 ≤ ε) (hq : 1 ≤ q)
    (hqε : q * ε < β) (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {f : E → E} (hf0 : f 0 = 0) (hf : HasStrictFDerivAt f (0 : E →L[ℝ] E) 0) :
    ∃ ρ > 0, ∃ h : E → E, ∃ L : NNReal, IsGraphMap P h ∧ LipschitzWith L h ∧
      IsLittleOrder P h 1 ∧
      (∀ (t₀ t₁ : ℝ) (φ : ℝ → E), IsIntegralCurveOn φ (fun _ y => fullField A f y) (Icc t₀ t₁) →
        φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h) ∧
      ∀ φ : E → E, ContDiffAt ℝ 1 φ 0 → φ 0 = 0 → fderiv ℝ φ 0 = 0 → (∀ x, P (φ x) = 0) →
        IsOrder P (invarianceDefect A P f φ) q → IsOrder P (fun u => h u - φ u) q := by
  have hK := nonneg_of_stable_bound hst
  have hq0 : 0 < q := by linarith
  have hβ : 0 < β := lt_of_le_of_lt (mul_nonneg hq0.le hε) hqε
  set η := (ε + β / q) / 2 with hηdef
  have hεβq : ε < β / q := by rw [lt_div_iff₀ hq0]; linarith
  have hεη : ε < η := by rw [hηdef]; linarith
  have hηβq : η < β / q := by rw [hηdef]; linarith
  have hqη : q * η < β := by have := (lt_div_iff₀ hq0).1 hηβq; linarith
  have hηβ : η < β := hηβq.trans_le (div_le_self hβ.le hq)
  have hη : 0 ≤ η := hε.trans hεη.le
  have hβq : 0 < β - q * η := sub_pos.2 hqη
  set κ := gapConst ε η β
  have hκ : 0 < κ := gapConst_pos hεη hηβ
  set D := K * κ + K * (‖1 - P‖ + ‖P‖) / (β - q * η) with hD
  have hD0 : 0 ≤ D := by positivity
  set δ : ℝ := 1 / (2 * (D + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hδD : δ * D < 1 := by
    rw [hδdef, show 1 / (2 * (D + 1)) * D = D / (2 * (D + 1)) by ring,
      div_lt_one (by positivity)]
    linarith
  have hk : K * δ * κ < 1 := by
    have : K * δ * κ ≤ δ * D := by
      rw [hD]; nlinarith [mul_nonneg hδ.le (show 0 ≤ K * (‖1 - P‖ + ‖P‖) / (β - q * η) by
        positivity)]
    linarith
  have hsmall : K * ((‖1 - P‖ + ‖P‖) * (Real.toNNReal δ : ℝ)) / (β - q * η) < 1 := by
    rw [Real.coe_toNNReal _ hδ.le]
    have : K * ((‖1 - P‖ + ‖P‖) * δ) / (β - q * η) ≤ δ * D := by
      rw [hD, mul_add]
      have e : K * ((‖1 - P‖ + ‖P‖) * δ) / (β - q * η) =
          δ * (K * (‖1 - P‖ + ‖P‖) / (β - q * η)) := by ring
      rw [e]; nlinarith [mul_nonneg hδ.le (mul_nonneg hK hκ.le)]
    linarith
  obtain ⟨ρ, hρ, g, hg, hg0, hgf, h, L, hh, hL, htan, hinv, hglob⟩ :=
    exists_centerManifold_data hP hε hεη hηβ hcen hst hf0 hf hδ hk
  refine ⟨ρ, hρ, h, L, hh, hL, htan, hinv, fun φ hφ hφ0 hDφ hφP hdef => ?_⟩
  obtain ⟨r, hr, ψ, hψ, hψ0, hψd, hψP, hψφ⟩ := exists_contDiff_cutoff hφ hφ0 hDφ hφP
  have hψn : ∀ x, ‖ψ x‖ ≤ ‖x‖ := fun x => by
    have := convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hψ.differentiable one_ne_zero y) (fun y _ => hψd y) (mem_univ 0) (mem_univ x)
    simpa [hψ0] using this
  obtain ⟨M, hM, hMb⟩ := exists_defect_bound (A := A) (P := P) hq hρ hr hg hgf hg0 hψd hψn hψφ hdef
  have hk1 : 0 < 1 - K * δ * κ := sub_pos.2 hk
  have hC := norm_sub_cutoff_le hP hη hq hqη hst hg hh (C₁ := K / (1 - K * δ * κ))
    (by positivity) (fun u => by
      obtain ⟨x, hx0, hxd, -, hxb⟩ := hglob u
      exact ⟨x, hx0, hxd, hxb⟩) hψ hψd hψn hψP hM hMb hsmall
  obtain ⟨C, hC⟩ : ∃ C, ∀ u, ‖h u - ψ (P u)‖ ≤ C * ‖P u‖ ^ q := ⟨_, hC⟩
  refine IsBigO.of_bound C ?_
  filter_upwards [inter_mem_nhdsWithin (Set.range P) (Metric.ball_mem_nhds 0 hr)]
    with u ⟨⟨w, hw⟩, hu⟩
  subst hw
  rw [Metric.mem_ball, dist_zero_right] at hu
  have hPu : P (P w) = P w := hP.idem w
  have h1 := hC (P w)
  rw [hPu, hψφ _ hu] at h1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact h1

end Approx

/-! ## The state space `ℝⁿ` -/

section State

variable {n : ℕ} {A P : State n →L[ℝ] State n}

/-- **Carr's approximation theorem on `ℝⁿ`** (centre–stable case, `f` of class `C¹` with
`f(0) = 0`, `Df(0) = 0`, gap `q ε < β`, `q ≥ 1`): a locally invariant Lipschitz centre manifold
`h`, `h(u) = o(‖u‖)`, such that every `C¹` candidate `φ` into `ker P` with `φ(0) = 0`,
`Dφ(0) = 0` and invariance defect `O(‖u‖^q)` satisfies `h(u) − φ(u) = O(‖u‖^q)` on `range P`.
Local invariance is in the canonical form of `theorem/Dynamics/CenterManifoldDefs.lean`. -/
@[tmio T, powerlib_foundation] theorem exists_centerManifold_approx
    (hP : IsCommutingProjection A P) {K ε β q : ℝ} (hε : 0 ≤ ε) (hq : 1 ≤ q)
    (hqε : q * ε < β) (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {f : State n → State n} (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0) (hDf : fderiv ℝ f 0 = 0) :
    ∃ ρ > 0, ∃ h : State n → State n, ∃ L : NNReal, IsGraphMap P h ∧ LipschitzWith L h ∧
      IsLittleOrder P h 1 ∧
      (∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
        φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h) ∧
      ∀ φ : State n → State n, ContDiffAt ℝ 1 φ 0 → φ 0 = 0 → fderiv ℝ φ 0 = 0 →
        (∀ x, P (φ x) = 0) → IsOrder P (invarianceDefect A P f φ) q →
        IsOrder P (fun u => h u - φ u) q := by
  have hs : HasStrictFDerivAt f (0 : State n →L[ℝ] State n) 0 := by
    have := (hf.contDiffAt (x := 0)).hasStrictFDerivAt (by norm_num)
    rwa [hDf] at this
  exact exists_centerManifold_approx_of_hasStrictFDerivAt hP hε hq hqε hcen hst hf0 hs

end State

end powerlib.Dynamics.CenterManifold
