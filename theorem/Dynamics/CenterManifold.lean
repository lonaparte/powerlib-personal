import theorem.Dynamics.LyapunovPerron
import theorem.Dynamics.CenterManifoldDefs
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # The centre manifold theorem (foundation)

Existence of a locally invariant, Lipschitz, tangent centre manifold for `ẋ = A x + f(x)` at an
equilibrium whose linearization has an exponential dichotomy into a centre part and a stable part
(the centre–stable case, no unstable part), by the Lyapunov–Perron method.

Scope.
* A real Banach space `E` (the applications take `E = State n = ℝⁿ`), `A`, `P : E →L[ℝ] E` with
  `P² = P`, `AP = PA` (`IsCommutingProjection`), the dichotomy as theorem hypotheses
  `‖e^{tA}P‖ ≤ K e^{ε|t|}` (all `t`) and `‖e^{tA}(1 − P)‖ ≤ K e^{−βt}` (`t ≥ 0`), with the gap
  condition `0 ≤ ε < β` (no further gap is needed for existence and tangency; the
  approximation theorem needs `qε < β`, `theorem/Dynamics/CenterManifoldApprox.lean`).
  The nonlinearity `f` has `f(0) = 0` and strict derivative `0` at `0` (on `ℝⁿ`: `C¹` with
  `Df(0) = 0`).
* Graph maps, graphs and orders are those of `theorem/Dynamics/CenterManifoldDefs.lean`; local
  invariance is the theorem conclusion in the form fixed there (no notion quantifies over time).
  The reduction theorems consuming it are `theorem/Dynamics/CenterReduction.lean`.
* The centre manifold is not unique; the theorem asserts existence of one (built from a cutoff of
  `f` of small Lipschitz constant). Smoothness of `h` beyond Lipschitz is not claimed; tangency is
  `h(u) = o(‖u‖)`.
* Generic; nothing here describes a physical system (foundation).

Source: Carr, *Applications of Centre Manifold Theory* (1981), Ch. 2, Theorem 1 (existence; here
by the Lyapunov–Perron integral equation rather than Carr's contraction on a space of Lipschitz
graphs); Vanderbauwhede, "Centre manifolds, normal forms and elementary bifurcations" (1989), §2
(the Lyapunov–Perron construction with exponentially weighted norms); Kelley, "The stable,
center-stable, center, center-unstable and unstable manifolds" (1967).

Results.
* Splitting tools: `IsCommutingProjection.commute`, `proj_stableInit`, `compl_stableInit`,
  `lpMap_proj`, `lpMap_zero`.
* The globally Lipschitz case (`exists_graph_of_lipschitz`): for a `δ`-Lipschitz `g`, `g 0 = 0`,
  `Kδκ < 1` (`κ = LyapunovPerron.gapConst`), the map `h(u) = (1 − P) x_u(0)`, `x_u` the fixed point
  of the Lyapunov–Perron transform (`theorem/Dynamics/LyapunovPerron.lean`), is a Lipschitz graph
  map, and through every graph point passes a whole-line solution of `ẋ = A x + g(x)` that stays on
  the graph (the shift of `x_u` is the fixed point of its own centre datum, by
  `LyapunovPerron.eq_lpMap_of_hasDerivAt` and `fixedPoint_unique`).
* Local invariance (`mem_graph_of_isIntegralCurveOn`): where `f = g`, solution segments of the
  original field starting on the graph coincide with these solutions (uniqueness for the Lipschitz
  field, LeanForControl `eqOn_of_isIntegralCurveOn_Icc`).
* The cutoff (`cutoff`, `cutoff_nonneg`, `cutoff_le_one`, `cutoff_eq_one`, `cutoff_eq_zero`,
  `abs_cutoff_sub_le`, `exists_small_lipschitz_cutoff`): `g = χ f` with the piecewise linear
  cutoff `χ` of radius `ρ` is `δ`-Lipschitz for `ρ` small. The smooth cutoffs of LeanForControl
  (`Stability/LyapunovIndirect/Chetaev.lean`) and `Flow.exists_lipschitz_cutoff` give a Lipschitz
  constant without a bound, which the contraction cannot use.
* Tangency (`tangent_of_stableInit`): `h(u) = o(‖P u‖)` from `g(y) = o(‖y‖)`; a tangent graph
  map is differentiable at `0` with `Dh(0) = 0` (`IsGraphMap.hasFDerivAt_zero`). A `C¹` centre
  manifold is `CenterManifoldSmooth.exists_centerManifold_contDiff`
  (`theorem/Dynamics/CenterManifoldSmooth.lean`): a separately constructed `h`, built with a
  `C¹` cutoff of `f` instead of the piecewise linear one used here.
* The construction with its parameters (`exists_centerManifold_data`: weight `η`, Lipschitz
  bound `δ`, the cutoff field and the whole-line solutions on the graph), used by the
  approximation theorem.
* **The theorem**: `exists_centerManifold_of_hasStrictFDerivAt` (Banach space) and
  `exists_centerManifold` (`ℝⁿ`, `C¹`, in the canonical local-invariance form with
  `IsTrajectoryOn`): `ρ > 0`, a Lipschitz graph map `h` with `IsLittleOrder P h 1`, and local
  invariance of its graph in the ball of radius `ρ`.
-/

noncomputable section
namespace powerlib.Dynamics.CenterManifold

open Set Filter Topology MeasureTheory Asymptotics
open powerlib.Dynamics.LyapunovPerron

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {A P : E →L[ℝ] E}

omit [CompleteSpace E] in
@[tmio T, powerlib_foundation] theorem IsCommutingProjection.commute
    (hP : IsCommutingProjection A P) : Commute A P :=
  ContinuousLinearMap.ext fun x => hP.comm x

/-- The stable initial value lies in `range (1 − P)`. -/
@[tmio T, powerlib_foundation] theorem IsCommutingProjection.proj_stableInit
    (hP : IsCommutingProjection A P) {b : ℝ → E}
    (hb : IntegrableOn (fun s => expFlow A (-s) ((1 - P) (b s))) (Iic 0)) :
    P (stableInit A P b) = 0 := by
  rw [stableInit, ← P.integral_comp_comm hb]
  have h : ∀ s, P (expFlow A (-s) ((1 - P) (b s))) = 0 := fun s => by
    change (P * expFlow A (-s)) _ = 0
    rw [← (expFlow_commute hP.commute (-s)).eq]
    change expFlow A (-s) (P ((1 - P) (b s))) = 0
    rw [hP.proj_compl, map_zero]
  rw [show (fun s => P (expFlow A (-s) ((1 - P) (b s)))) = fun _ => (0 : E) from funext h,
    integral_zero]

@[tmio T, powerlib_foundation] theorem IsCommutingProjection.compl_stableInit
    (hP : IsCommutingProjection A P) {b : ℝ → E}
    (hb : IntegrableOn (fun s => expFlow A (-s) ((1 - P) (b s))) (Iic 0)) :
    (1 - P) (stableInit A P b) = stableInit A P b := by
  rw [compl_apply, hP.proj_stableInit hb, sub_zero]

omit [CompleteSpace E] in
@[tmio T, powerlib_foundation] theorem IsCommutingProjection.lpMap_proj
    (hP : IsCommutingProjection A P) (u : E) (b : ℝ → E) (t : ℝ) :
    lpMap A P (P u) b t = lpMap A P u b t := by
  simp only [lpMap, hP.idem]

omit [CompleteSpace E] in
@[tmio T, powerlib_foundation] theorem lpMap_zero (u : E) (b : ℝ → E) :
    lpMap A P u b 0 = P u + stableInit A P b := by
  simp [lpMap, expFlow_zero]

/-- **The centre manifold of a globally Lipschitz nonlinearity.** Under the dichotomy, for a
`δ`-Lipschitz `g` with `g 0 = 0` and `K δ κ < 1`, there is a Lipschitz graph map `h` over
`range P` such that through every point `P u + h u` of its graph passes a solution of
`ẋ = A x + g(x)` on the whole line that stays on the graph, grows at most like
`K ‖P u‖ e^{η|t|}/(1 − Kδκ)`, and whose stable initial value is `h u`. -/
@[tmio T, powerlib_foundation] theorem exists_graph_of_lipschitz
    (hP : IsCommutingProjection A P) {K ε η β : ℝ} (hε : 0 ≤ ε) (hεη : ε < η) (hηβ : η < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {g : E → E} {δ : NNReal} (hg : LipschitzWith δ g) (hg0 : g 0 = 0)
    (hk : K * δ * gapConst ε η β < 1) :
    ∃ h : E → E, IsGraphMap P h ∧ (∃ L : NNReal, LipschitzWith L h) ∧
      ∀ u, ∃ x : ℝ → E, x 0 = P u + h u ∧ (∀ t, HasDerivAt x (A (x t) + g (x t)) t) ∧
        (∀ t, x t ∈ graph P h) ∧
        (∀ t, ‖x t‖ ≤ K / (1 - K * δ * gapConst ε η β) * ‖P u‖ * Real.exp (η * |t|)) ∧
        h u = stableInit A P (fun s => g (x s)) := by
  have hη : 0 ≤ η := hε.trans hεη.le
  have hk1 : 0 < 1 - K * δ * gapConst ε η β := sub_pos.2 hk
  choose X hXc hXb hXfix using fun u =>
    exists_fixedPoint (A := A) (P := P) hε hεη hηβ hcen hst hg hg0 hk u
  choose CX hCX hXb using hXb
  have hgX : ∀ u s, ‖g (X u s)‖ ≤ (δ * CX u) * Real.exp (η * |s|) := fun u s =>
    (hg.norm_le_mul hg0 _).trans (by rw [mul_assoc]; gcongr; exact hXb u s)
  have hgXc : ∀ u, Continuous fun s => g (X u s) := fun u => hg.continuous.comp (hXc u)
  -- uniqueness among functions of weighted growth
  have huniq : ∀ u (x : ℝ → E) (C : ℝ), Continuous x → (∀ t, ‖x t‖ ≤ C * Real.exp (η * |t|)) →
      (∀ t, x t = lpMap A P u (fun s => g (x s)) t) → x = X u := fun u x C hc hb hx =>
    fixedPoint_unique hε hεη hηβ hcen hst hg hg0 hk hc (hXc u) hb (hXb u) hx (hXfix u)
  have hX0 : X 0 = fun _ => 0 := by
    symm
    refine huniq 0 _ 0 continuous_const (fun t => by simp) fun t => ?_
    simp [lpMap, stableInit, hg0]
  have hXP : ∀ u, X (P u) = X u := fun u =>
    huniq u _ _ (hXc (P u)) (hXb (P u)) fun t => by
      rw [hXfix (P u) t, hP.lpMap_proj]
  have hXbd : ∀ u t, ‖X u t‖ ≤ K / (1 - K * δ * gapConst ε η β) * ‖P u‖ *
      Real.exp (η * |t|) := fun u t => by
    have h := norm_sub_fixedPoint_le hε hεη hηβ hcen hst hg hg0 hk (hXc (P u)) (hXc 0)
      (hXb (P u)) (hXb 0) (hXfix (P u)) (hXfix 0) t
    rw [hXP, hX0, sub_zero, sub_zero] at h
    refine h.trans_eq ?_
    ring
  have hint : ∀ u, IntegrableOn (fun s => expFlow A (-s) ((1 - P) (g (X u s)))) (Iic 0) :=
    fun u => integrableOn_stableInit (hgXc u) (mul_nonneg δ.coe_nonneg (hCX u)) (hgX u) hη hηβ
      hst 0
  have hderiv : ∀ u t, HasDerivAt (X u) (A (X u t) + g (X u t)) t := fun u t => by
    have he : X u = lpMap A P u (fun s => g (X u s)) := funext (hXfix u)
    have h := hasDerivAt_lpMap (A := A) (P := P) (hgXc u) u t
    rw [← he] at h
    exact h
  set h : E → E := fun u => (1 - P) (X u 0) with hdef
  have hX00 : ∀ u, X u 0 = P u + h u := fun u => by
    simp only [hdef]
    rw [hXfix u 0, lpMap_zero, map_add, hP.compl_proj, zero_add, hP.compl_stableInit (hint u)]
  have hhst : ∀ u, h u = stableInit A P (fun s => g (X u s)) := fun u => by
    simp only [hdef]
    rw [hXfix u 0, lpMap_zero, map_add, hP.compl_proj, zero_add, hP.compl_stableInit (hint u)]
  have hgraph : IsGraphMap P h :=
    ⟨fun x => by simp only [hdef, hXP], fun x => hP.proj_compl _, by simp [hdef, hX0]⟩
  refine ⟨h, hgraph, ⟨Real.toNNReal (‖1 - P‖ * (K / (1 - K * δ * gapConst ε η β))),
    LipschitzWith.of_dist_le_mul fun u v => ?_⟩, fun u => ⟨X u, hX00 u, hderiv u, fun τ => ?_,
    hXbd u, hhst u⟩⟩
  · -- Lipschitz bound
    have hK := nonneg_of_stable_bound hst
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm]
    have h0 := norm_sub_fixedPoint_le hε hεη hηβ hcen hst hg hg0 hk (hXc u) (hXc v) (hXb u)
      (hXb v) (hXfix u) (hXfix v) 0
    simp only [abs_zero, mul_zero, Real.exp_zero, mul_one] at h0
    calc ‖h u - h v‖ = ‖(1 - P) (X u 0 - X v 0)‖ := by simp only [hdef, map_sub]
      _ ≤ ‖1 - P‖ * ‖X u 0 - X v 0‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖1 - P‖ * (K * ‖u - v‖ / (1 - K * δ * gapConst ε η β)) := by gcongr
      _ = _ := by ring
  · -- the solution stays on the graph: its shift is the fixed point of its own centre datum
    set y : ℝ → E := fun t => X u (τ + t)
    have hyc : Continuous y := (hXc u).comp (continuous_const.add continuous_id)
    have hyb : ∀ t, ‖y t‖ ≤ (CX u * Real.exp (η * |τ|)) * Real.exp (η * |t|) := fun t => by
      refine (hXb u (τ + t)).trans ?_
      rw [mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hCX u)
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left (abs_add_le τ t) hη
    have hgy : ∀ s, ‖g (y s)‖ ≤ (δ * (CX u * Real.exp (η * |τ|))) * Real.exp (η * |s|) :=
      fun s => (hg.norm_le_mul hg0 _).trans (by rw [mul_assoc]; gcongr; exact hyb s)
    have hyd : ∀ t, HasDerivAt y (A (y t) + g (y t)) t := fun t =>
      (hderiv u (τ + t)).comp_const_add τ t
    have hvoc := eq_lpMap_of_hasDerivAt hP.commute hη hηβ hst (hg.continuous.comp hyc)
      (mul_nonneg δ.coe_nonneg (mul_nonneg (hCX u) (Real.exp_pos _).le)) hgy hyb hyd
    have hy0 : y 0 = X u τ := by simp [y]
    rw [hy0] at hvoc
    have hyX : y = X (X u τ) := huniq _ y _ hyc hyb hvoc
    have hh : h (X u τ) = (1 - P) (X u τ) := by
      simp only [hdef]; rw [← hyX, hy0]
    show X u τ = P (X u τ) + h (X u τ)
    rw [hh, compl_apply]; abel

omit [CompleteSpace E] in
/-- **Local invariance.** If through every point of the graph of `h` passes a solution of the
globally Lipschitz field `x ↦ A x + g(x)` on the whole line that stays on the graph, and `f = g`
on the ball of radius `ρ`, then every solution segment of `ẋ = A x + f(x)` that starts on the
graph and stays in that ball stays on the graph. -/
@[tmio T, powerlib_foundation] theorem mem_graph_of_isIntegralCurveOn {h g f : E → E}
    {δ : NNReal} {ρ : ℝ} (hg : LipschitzWith δ g)
    (hglob : ∀ u, ∃ x : ℝ → E, x 0 = P u + h u ∧ (∀ t, HasDerivAt x (A (x t) + g (x t)) t) ∧
      ∀ t, x t ∈ graph P h)
    (hfg : ∀ y, ‖y‖ < ρ → f y = g y) {φ : ℝ → E} {t₀ t₁ : ℝ}
    (hφ : IsIntegralCurveOn φ (fun _ y => fullField A f y) (Icc t₀ t₁)) (h0 : φ t₀ ∈ graph P h)
    (hρ : ∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) : ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h := by
  obtain ⟨x, hx0, hxd, hxg⟩ := hglob (φ t₀)
  have hφ' : IsIntegralCurveOn φ (fun _ y => A y + g y) (Icc t₀ t₁) := fun t ht => by
    have := hφ t ht
    simp only [fullField, hfg _ (hρ t ht)] at this
    exact this
  have hψ : IsIntegralCurveOn (fun t => x (t - t₀)) (fun _ y => A y + g y) (Icc t₀ t₁) :=
    fun t _ => ((hxd (t - t₀)).comp_sub_const t t₀).hasDerivWithinAt
  have heq := eqOn_of_isIntegralCurveOn_Icc (K := ‖A‖₊ + δ) (fun _ => A.lipschitzWith.add hg) hφ'
    hψ (by simp only [sub_self, hx0]; exact h0)
  intro t ht
  rw [heq ht]
  exact hxg _

/-! ## The cutoff -/

/-- The piecewise linear cutoff `χ(y) = min 1 (max 0 (2 − ‖y‖/ρ))`: `1` on the ball of radius
`ρ`, `0` outside the ball of radius `2ρ`, `1/ρ`-Lipschitz. -/
def cutoff (ρ : ℝ) (y : E) : ℝ := min 1 (max 0 (2 - ‖y‖ / ρ))

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[tmio T, powerlib_foundation] theorem cutoff_nonneg (ρ : ℝ) (y : E) : 0 ≤ cutoff ρ y :=
  le_min zero_le_one (le_max_left _ _)

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[tmio T, powerlib_foundation] theorem cutoff_le_one (ρ : ℝ) (y : E) : cutoff ρ y ≤ 1 :=
  min_le_left _ _

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[tmio T, powerlib_foundation] theorem cutoff_eq_one {ρ : ℝ} (hρ : 0 < ρ) {y : E}
    (hy : ‖y‖ ≤ ρ) : cutoff ρ y = 1 := by
  have : 1 ≤ 2 - ‖y‖ / ρ := by
    have := (div_le_one hρ).2 hy; linarith
  exact min_eq_left (this.trans (le_max_right _ _))

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[tmio T, powerlib_foundation] theorem cutoff_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {y : E}
    (hy : 2 * ρ ≤ ‖y‖) : cutoff ρ y = 0 := by
  have : 2 - ‖y‖ / ρ ≤ 0 := by
    have := (le_div_iff₀ hρ).2 hy; linarith
  rw [cutoff, max_eq_left this, min_eq_right zero_le_one]

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[tmio T, powerlib_foundation] theorem abs_cutoff_sub_le {ρ : ℝ} (hρ : 0 < ρ) (x y : E) :
    |cutoff ρ x - cutoff ρ y| ≤ ‖x - y‖ / ρ := by
  unfold cutoff
  refine (abs_min_sub_min_le_max (1 : ℝ) (max 0 (2 - ‖x‖ / ρ)) 1 (max 0 (2 - ‖y‖ / ρ))).trans
    (max_le (by simp only [sub_self, abs_zero]; positivity) ?_)
  rw [max_comm 0, max_comm 0]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [show (2 - ‖x‖ / ρ) - (2 - ‖y‖ / ρ) = (‖y‖ - ‖x‖) / ρ by ring, abs_div, abs_of_pos hρ]
  gcongr
  rw [abs_sub_comm]
  exact abs_norm_sub_norm_le x y

omit [CompleteSpace E] in
/-- **Globalization.** A nonlinearity with `f 0 = 0` that is strictly differentiable at `0` with
derivative `0` agrees, on a ball, with a `δ`-Lipschitz map `g` with `g 0 = 0` and `‖g‖ ≤ ‖f‖`:
`g = χ f` with the cutoff `χ` of a small radius. -/
@[tmio T, powerlib_foundation] theorem exists_small_lipschitz_cutoff {f : E → E} (hf0 : f 0 = 0)
    (hf : HasStrictFDerivAt f (0 : E →L[ℝ] E) 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ > 0, ∃ g : E → E, LipschitzWith (Real.toNNReal δ) g ∧ g 0 = 0 ∧
      (∀ y, ‖y‖ ≤ ρ → g y = f y) ∧ ∀ y, ‖g y‖ ≤ ‖f y‖ := by
  have hlo := hf.isLittleO.def (show 0 < δ / 3 by positivity)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hlo
  have hfL : ∀ x y : E, ‖x‖ < r → ‖y‖ < r → ‖f x - f y‖ ≤ δ / 3 * ‖x - y‖ := by
    intro x y hx hy
    have h := hball (y := (x, y)) (by
      rw [Prod.dist_eq, max_lt_iff]; simpa [dist_eq_norm] using And.intro hx hy)
    simpa using h
  have hfn : ∀ x : E, ‖x‖ < r → ‖f x‖ ≤ δ / 3 * ‖x‖ := fun x hx => by
    simpa [hf0] using hfL x 0 hx (by simpa using hr)
  set ρ := r / 3 with hρdef
  have hρ : 0 < ρ := by positivity
  have h2ρ : 2 * ρ < r := by rw [hρdef]; linarith
  refine ⟨ρ, hρ, fun y => cutoff ρ y • f y, LipschitzWith.of_dist_le_mul fun x y => ?_,
    by simp [hf0], fun y hy => by simp [cutoff_eq_one hρ hy], fun y => ?_⟩
  · rw [Real.coe_toNNReal _ hδ.le, dist_eq_norm, dist_eq_norm]
    have hc := abs_cutoff_sub_le hρ x y
    -- the bound when `x` lies in the ball of radius `2ρ` and `y` outside
    have hout : ∀ x y : E, ‖x‖ < 2 * ρ → 2 * ρ ≤ ‖y‖ →
        ‖cutoff ρ x • f x - cutoff ρ y • f y‖ ≤ δ * ‖x - y‖ := by
      intro x y hx hy
      rw [cutoff_eq_zero hρ hy, zero_smul, sub_zero, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (cutoff_nonneg _ _)]
      have hcx : cutoff ρ x ≤ ‖x - y‖ / ρ := by
        have := abs_cutoff_sub_le hρ x y
        rwa [cutoff_eq_zero hρ hy, sub_zero, abs_of_nonneg (cutoff_nonneg _ _)] at this
      calc cutoff ρ x * ‖f x‖ ≤ ‖x - y‖ / ρ * (δ / 3 * (2 * ρ)) :=
            mul_le_mul hcx ((hfn x (by linarith)).trans (by gcongr)) (norm_nonneg _)
              (by positivity)
        _ = 2 / 3 * δ * ‖x - y‖ := by field_simp
        _ ≤ δ * ‖x - y‖ := by nlinarith [norm_nonneg (x - y)]
    rcases lt_or_ge ‖x‖ (2 * ρ) with hx | hx <;> rcases lt_or_ge ‖y‖ (2 * ρ) with hy | hy
    · calc ‖cutoff ρ x • f x - cutoff ρ y • f y‖
          = ‖(cutoff ρ x - cutoff ρ y) • f x + cutoff ρ y • (f x - f y)‖ := by
            congr 1; rw [sub_smul, smul_sub]; abel
        _ ≤ |cutoff ρ x - cutoff ρ y| * ‖f x‖ + cutoff ρ y * ‖f x - f y‖ := by
            refine (norm_add_le _ _).trans_eq ?_
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (cutoff_nonneg ρ y)]
        _ ≤ ‖x - y‖ / ρ * (δ / 3 * (2 * ρ)) + 1 * (δ / 3 * ‖x - y‖) := by
            gcongr
            · exact (hfn x (by linarith)).trans (by gcongr)
            · exact cutoff_le_one _ _
            · exact hfL x y (by linarith) (by linarith)
        _ = δ * ‖x - y‖ := by field_simp; ring
    · exact hout x y hx hy
    · rw [← norm_neg, neg_sub, ← norm_neg (x - y), neg_sub]
      exact hout y x hy hx
    · rw [cutoff_eq_zero hρ hx, cutoff_eq_zero hρ hy]
      simp only [zero_smul, sub_self, norm_zero]
      positivity
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one _ _)

/-! ## Tangency -/

omit [CompleteSpace E] in
/-- **Tangency.** If `g(y) = o(‖y‖)` at `0` and every value `h u` is the stable initial value of
a forcing `g ∘ x` along a function of growth `C₁ ‖P u‖ e^{η|t|}`, then `h(u) = o(‖P u‖)`. -/
@[tmio T, powerlib_foundation] theorem tangent_of_stableInit {K η β C₁ : ℝ} (hη : 0 ≤ η)
    (hηβ : η < β) (hC₁ : 0 ≤ C₁)
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {g h : E → E} {δ : NNReal} (hg : LipschitzWith δ g) (hg0 : g 0 = 0)
    (hgo : ∀ θ > 0, ∃ r > 0, ∀ y, ‖y‖ ≤ r → ‖g y‖ ≤ θ * ‖y‖)
    (hrep : ∀ u, ∃ x : ℝ → E, Continuous x ∧
      (∀ t, ‖x t‖ ≤ C₁ * ‖P u‖ * Real.exp (η * |t|)) ∧ h u = stableInit A P (fun s => g (x s)))
    {θ : ℝ} (hθ : 0 < θ) : ∃ r > 0, ∀ u, ‖P u‖ ≤ r → ‖h u‖ ≤ θ * ‖P u‖ := by
  have hK := nonneg_of_stable_bound hst
  have hd : 0 < β - η := sub_pos.2 hηβ
  set γ := (β - η) / 2 with hγ
  have hγ0 : 0 < γ := by positivity
  set M := K * C₁ with hM
  have hM0 : 0 ≤ M := mul_nonneg hK hC₁
  -- a horizon `T` after which the crude bound `δ` is small enough
  have hev : ∀ᶠ T in atTop, M * δ * Real.exp (-(γ * T)) / γ < θ / 2 := by
    have ht : Tendsto (fun T : ℝ => M * δ * Real.exp (-(γ * T)) / γ) atTop
        (𝓝 (M * δ * 0 / γ)) :=
      ((Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hγ0)).const_mul
        _).div_const _
    rw [mul_zero, zero_div] at ht
    exact ht.eventually (gt_mem_nhds (by positivity))
  obtain ⟨T, hT, hT0⟩ := (hev.and (eventually_ge_atTop 0)).exists
  -- the small Lipschitz-type bound on the window `[−T, 0]`
  set θ' := θ * (β - η) / (2 * (M + 1)) with hθ'
  have hθ'0 : 0 < θ' := by positivity
  obtain ⟨r', hr', hgr'⟩ := hgo θ' hθ'0
  set r := r' / ((C₁ + 1) * Real.exp (η * T)) with hr
  refine ⟨r, by positivity, fun u hu => ?_⟩
  obtain ⟨x, hxc, hxb, hhu⟩ := hrep u
  set a := ‖P u‖
  have ha : 0 ≤ a := norm_nonneg _
  have hgx : ∀ s ≤ 0, ‖g (x s)‖ ≤
      C₁ * a * (θ' * Real.exp (-(η * s)) +
        δ * Real.exp (-(γ * T)) * Real.exp (-((η + γ) * s))) := by
    intro s hs
    have hxs : ‖x s‖ ≤ C₁ * a * Real.exp (-(η * s)) := by
      have := hxb s; rwa [abs_of_nonpos hs, mul_neg] at this
    have hn1 : 0 ≤ C₁ * a * (θ' * Real.exp (-(η * s))) := by positivity
    have hn2 : 0 ≤ C₁ * a * (δ * Real.exp (-(γ * T)) * Real.exp (-((η + γ) * s))) := by
      positivity
    rcases le_or_gt (-T) s with hsT | hsT
    · -- inside the window the state is small
      have hsm : ‖x s‖ ≤ r' := by
        refine hxs.trans ?_
        have h1 : Real.exp (-(η * s)) ≤ Real.exp (η * T) :=
          Real.exp_le_exp.2 (by nlinarith)
        calc C₁ * a * Real.exp (-(η * s)) ≤ C₁ * r * Real.exp (η * T) := by gcongr
          _ ≤ (C₁ + 1) * r * Real.exp (η * T) := by gcongr; linarith
          _ = r' := by rw [hr]; field_simp
      calc ‖g (x s)‖ ≤ θ' * ‖x s‖ := hgr' _ hsm
        _ ≤ θ' * (C₁ * a * Real.exp (-(η * s))) := by gcongr
        _ = C₁ * a * (θ' * Real.exp (-(η * s))) := by ring
        _ ≤ _ := by rw [mul_add]; linarith
    · -- outside it the global Lipschitz bound suffices
      have he : Real.exp (-(η * s)) ≤ Real.exp (-(γ * T)) * Real.exp (-((η + γ) * s)) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
      calc ‖g (x s)‖ ≤ δ * ‖x s‖ := hg.norm_le_mul hg0 _
        _ ≤ δ * (C₁ * a * Real.exp (-(η * s))) := by gcongr
        _ ≤ δ * (C₁ * a * (Real.exp (-(γ * T)) * Real.exp (-((η + γ) * s)))) := by gcongr
        _ = C₁ * a * (δ * Real.exp (-(γ * T)) * Real.exp (-((η + γ) * s))) := by ring
        _ ≤ _ := by rw [mul_add]; linarith
  -- integrate the bound against `‖e^{−sA}(1 − P)‖ ≤ K e^{βs}`
  set B : ℝ → ℝ := fun s => M * a * (θ' * Real.exp ((β - η) * s) +
    δ * Real.exp (-(γ * T)) * Real.exp ((β - η - γ) * s)) with hB
  have hd2 : 0 < β - η - γ := by rw [hγ]; linarith
  have hBi : IntegrableOn B (Iic 0) :=
    (((integrableOn_exp_mul_Iic hd 0).const_mul θ').add
      ((integrableOn_exp_mul_Iic hd2 0).const_mul _)).const_mul _
  have hpt : ∀ s ∈ Iic (0 : ℝ), ‖expFlow A (-s) ((1 - P) (g (x s)))‖ ≤ B s := by
    intro s hs
    have hs' : s ≤ 0 := hs
    calc ‖expFlow A (-s) ((1 - P) (g (x s)))‖ = ‖(expFlow A (-s) * (1 - P)) (g (x s))‖ := rfl
      _ ≤ ‖expFlow A (-s) * (1 - P)‖ * ‖g (x s)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * Real.exp (-(β * -s)) * (C₁ * a * (θ' * Real.exp (-(η * s)) +
          δ * Real.exp (-(γ * T)) * Real.exp (-((η + γ) * s)))) :=
          mul_le_mul (hst _ (neg_nonneg.2 hs')) (hgx s hs') (norm_nonneg _)
            (mul_nonneg hK (Real.exp_pos _).le)
      _ = B s := by
          simp only [hB, hM]
          have e1 : Real.exp (-(β * -s)) * Real.exp (-(η * s)) = Real.exp ((β - η) * s) := by
            rw [← Real.exp_add]; ring_nf
          have e2 : Real.exp (-(β * -s)) * Real.exp (-((η + γ) * s)) =
              Real.exp ((β - η - γ) * s) := by
            rw [← Real.exp_add]; ring_nf
          linear_combination (K * C₁ * a * θ') * e1 +
            (K * C₁ * a * δ * Real.exp (-(γ * T))) * e2
  have hint : ∫ s in Iic (0 : ℝ), B s = M * a * (θ' / (β - η) + δ * Real.exp (-(γ * T)) / γ) := by
    simp only [hB]
    rw [integral_const_mul, integral_add ((integrableOn_exp_mul_Iic hd 0).const_mul θ')
      ((integrableOn_exp_mul_Iic hd2 0).const_mul _), integral_const_mul, integral_const_mul,
      integral_exp_mul_Iic hd, integral_exp_mul_Iic hd2]
    have : β - η - γ = γ := by rw [hγ]; ring
    rw [this]; simp only [mul_zero, Real.exp_zero]; ring
  have hle : ‖h u‖ ≤ M * a * (θ' / (β - η) + δ * Real.exp (-(γ * T)) / γ) := by
    rw [hhu, stableInit, ← hint]
    exact norm_integral_le_of_norm_le hBi (ae_restrict_of_forall_mem measurableSet_Iic hpt)
  refine hle.trans ?_
  have h1 : M * θ' / (β - η) ≤ θ / 2 := by
    rw [hθ']
    rw [div_le_iff₀ hd]
    have : M * (θ * (β - η) / (2 * (M + 1))) = θ * (β - η) / 2 * (M / (M + 1)) := by
      field_simp
    rw [this]
    have hMM : M / (M + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    nlinarith [mul_pos hθ hd]
  have h2 : M * (δ * Real.exp (-(γ * T)) / γ) ≤ θ / 2 := by
    have := hT.le; rw [mul_div_assoc', ← mul_assoc]; exact this
  calc M * a * (θ' / (β - η) + δ * Real.exp (-(γ * T)) / γ)
      = a * (M * θ' / (β - η) + M * (δ * Real.exp (-(γ * T)) / γ)) := by ring
    _ ≤ a * (θ / 2 + θ / 2) := by gcongr
    _ = θ * a := by ring

omit [CompleteSpace E] in
/-- A graph map tangent to `range P` is differentiable at `0` with derivative `0`: `h = h ∘ P`
turns `h(u) = o(‖u‖)` on `range P` into `h(x) = o(‖x‖)` on `E`. -/
@[tmio T, powerlib_foundation] theorem IsGraphMap.hasFDerivAt_zero {h : E → E}
    (hh : IsGraphMap P h) (ht : IsLittleOrder P h 1) : HasFDerivAt h (0 : E →L[ℝ] E) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hT : Tendsto (fun y => P y) (𝓝 0) (𝓝[Set.range P] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using P.continuous.tendsto 0,
      Eventually.of_forall fun y => ⟨y, rfl⟩⟩
  have h1 := ht.comp_tendsto hT
  have h2 : (fun y : E => ‖P y‖ ^ (1 : ℝ)) =O[𝓝 0] fun y => y := by
    simp only [Real.rpow_one]
    exact (P.isBigO_comp _ _).norm_left.trans (isBigO_refl _ _)
  refine (h1.trans_isBigO h2).congr_left fun y => ?_
  simp [hh.comp_proj, hh.map_zero]

/-! ## The centre manifold theorem -/

/-- **The construction with its parameters.** For a weight `η ∈ (ε, β)` and a Lipschitz bound
`δ > 0` with `K δ κ < 1`: a cutoff `g` of `f` agreeing with it on the ball of radius `ρ`, and a
Lipschitz graph map `h` tangent to `range P`, whose graph is locally invariant for
`ẋ = A x + f(x)` in that ball, with through every graph point a whole-line solution of the cutoff
field that stays on the graph and grows at most like `K ‖P u‖ e^{η|t|}/(1 − Kδκ)`. -/
@[tmio T, powerlib_foundation] theorem exists_centerManifold_data
    (hP : IsCommutingProjection A P) {K ε η β : ℝ} (hε : 0 ≤ ε) (hεη : ε < η) (hηβ : η < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {f : E → E} (hf0 : f 0 = 0) (hf : HasStrictFDerivAt f (0 : E →L[ℝ] E) 0) {δ : ℝ}
    (hδ : 0 < δ) (hk : K * δ * gapConst ε η β < 1) :
    ∃ ρ > 0, ∃ g : E → E, LipschitzWith (Real.toNNReal δ) g ∧ g 0 = 0 ∧
      (∀ y, ‖y‖ ≤ ρ → g y = f y) ∧ ∃ h : E → E, ∃ L : NNReal, IsGraphMap P h ∧
      LipschitzWith L h ∧ IsLittleOrder P h 1 ∧
      (∀ (t₀ t₁ : ℝ) (φ : ℝ → E), IsIntegralCurveOn φ (fun _ y => fullField A f y) (Icc t₀ t₁) →
        φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h) ∧
      ∀ u, ∃ x : ℝ → E, x 0 = P u + h u ∧ (∀ t, HasDerivAt x (A (x t) + g (x t)) t) ∧
        (∀ t, x t ∈ graph P h) ∧
        ∀ t, ‖x t‖ ≤ K / (1 - K * δ * gapConst ε η β) * ‖P u‖ * Real.exp (η * |t|) := by
  have hη : 0 ≤ η := hε.trans hεη.le
  have hK := nonneg_of_stable_bound hst
  have hk' : K * (Real.toNNReal δ : ℝ) * gapConst ε η β < 1 := by
    rwa [Real.coe_toNNReal _ hδ.le]
  obtain ⟨ρ, hρ, g, hg, hg0, hgf, hgle⟩ := exists_small_lipschitz_cutoff hf0 hf hδ
  obtain ⟨h, hh, ⟨L, hL⟩, hglob⟩ := exists_graph_of_lipschitz hP hε hεη hηβ hcen hst hg hg0 hk'
  have hk1 : 0 < 1 - K * δ * gapConst ε η β := sub_pos.2 hk
  refine ⟨ρ, hρ, g, hg, hg0, hgf, h, L, hh, hL, ?_, fun t₀ t₁ φ hφ h0 hφρ => ?_, fun u => ?_⟩
  · -- tangency
    have hgo : ∀ θ > 0, ∃ r > 0, ∀ y, ‖y‖ ≤ r → ‖g y‖ ≤ θ * ‖y‖ := by
      intro θ hθ
      have := (hf.hasFDerivAt.isLittleO.def hθ)
      obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 this
      refine ⟨r / 2, by positivity, fun y hy => (hgle y).trans ?_⟩
      have := hball (y := y) (by rw [dist_zero_right]; linarith)
      simpa [hf0] using this
    have htan := fun θ (hθ : 0 < θ) => tangent_of_stableInit
      (C₁ := K / (1 - K * (Real.toNNReal δ : ℝ) * gapConst ε η β)) hη hηβ (by positivity) hst hg
      hg0 hgo (h := h) (fun u => by
        obtain ⟨x, -, hxd, -, hxb, hhu⟩ := hglob u
        exact ⟨x, continuous_iff_continuousAt.2 fun t => (hxd t).continuousAt, hxb, hhu⟩) hθ
    rw [IsLittleOrder, isLittleO_iff]
    intro c hc
    obtain ⟨r, hr, hbd⟩ := htan c hc
    filter_upwards [inter_mem_nhdsWithin (Set.range P) (Metric.closedBall_mem_nhds 0 hr)]
      with u ⟨⟨w, hw⟩, hu⟩
    subst hw
    rw [Metric.mem_closedBall, dist_zero_right] at hu
    have hPu : P (P w) = P w := hP.idem w
    rw [Real.rpow_one, norm_norm]
    have := hbd (P w) (by rwa [hPu])
    rwa [hPu] at this
  · -- local invariance
    exact mem_graph_of_isIntegralCurveOn hg (fun u => by
      obtain ⟨x, hx0, hxd, hxg, -⟩ := hglob u
      exact ⟨x, hx0, hxd, hxg⟩) (fun y hy => (hgf y hy.le).symm) hφ h0 hφρ
  · obtain ⟨x, hx0, hxd, hxg, hxb, -⟩ := hglob u
    refine ⟨x, hx0, hxd, hxg, fun t => ?_⟩
    rw [Real.coe_toNNReal _ hδ.le] at hxb
    exact hxb t

/-- **Centre manifold theorem** (centre–stable case). Let `P` be a projection commuting with `A`
with the dichotomy `‖e^{tA}P‖ ≤ K e^{ε|t|}` (all `t`), `‖e^{tA}(1 − P)‖ ≤ K e^{−βt}` (`t ≥ 0`),
`0 ≤ ε < β`, and let `f(0) = 0` with strict derivative `0` at `0`. There are `ρ > 0` and a
Lipschitz graph map `h : range P → range (1 − P)` tangent to `range P` (`h(u) = o(‖u‖)`) whose
graph is locally invariant: solution segments of `ẋ = A x + f(x)` starting on it stay on it while
they stay in the ball of radius `ρ`. -/
@[tmio T, powerlib_foundation] theorem exists_centerManifold_of_hasStrictFDerivAt
    (hP : IsCommutingProjection A P) {K ε β : ℝ} (hε : 0 ≤ ε) (hεβ : ε < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {f : E → E} (hf0 : f 0 = 0) (hf : HasStrictFDerivAt f (0 : E →L[ℝ] E) 0) :
    ∃ ρ > 0, ∃ h : E → E, ∃ L : NNReal, IsGraphMap P h ∧ LipschitzWith L h ∧
      IsLittleOrder P h 1 ∧
      ∀ (t₀ t₁ : ℝ) (φ : ℝ → E), IsIntegralCurveOn φ (fun _ y => fullField A f y) (Icc t₀ t₁) →
        φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h := by
  have hK := nonneg_of_stable_bound hst
  set η := (ε + β) / 2 with hηdef
  have hεη : ε < η := by rw [hηdef]; linarith
  have hηβ : η < β := by rw [hηdef]; linarith
  set κ := gapConst ε η β
  have hκ : 0 < κ := gapConst_pos hεη hηβ
  set δ : ℝ := 1 / (2 * (K * κ + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hk : K * δ * κ < 1 := by
    rw [hδdef]
    have h1 : 0 < K * κ + 1 := by positivity
    rw [show K * (1 / (2 * (K * κ + 1))) * κ = (K * κ) / (2 * (K * κ + 1)) by ring,
      div_lt_one (by positivity)]
    linarith
  obtain ⟨ρ, hρ, -, -, -, -, h, L, hh, hL, htan, hinv, -⟩ :=
    exists_centerManifold_data hP hε hεη hηβ hcen hst hf0 hf hδ hk
  exact ⟨ρ, hρ, h, L, hh, hL, htan, hinv⟩

end Generic

/-! ## The state space `ℝⁿ` -/

section State

variable {n : ℕ} {A P : State n →L[ℝ] State n}

/-- **Centre manifold theorem on `ℝⁿ`** (centre–stable case): the form consumed by
`theorem/Dynamics/CenterReduction.lean`. For `f` of class `C¹` with `f(0) = 0`, `Df(0) = 0`, and
the dichotomy `‖e^{tA}P‖ ≤ K e^{ε|t|}`, `‖e^{tA}(1 − P)‖ ≤ K e^{−βt}` (`t ≥ 0`), `0 ≤ ε < β`,
there are `ρ > 0` and a Lipschitz graph map `h` with `h(u) = o(‖u‖)` on `range P` whose graph is
locally invariant in the ball of radius `ρ`. -/
@[tmio T, powerlib_foundation] theorem exists_centerManifold (hP : IsCommutingProjection A P)
    {K ε β : ℝ} (hε : 0 ≤ ε) (hεβ : ε < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {f : State n → State n} (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0) (hDf : fderiv ℝ f 0 = 0) :
    ∃ ρ > 0, ∃ h : State n → State n, ∃ L : NNReal, IsGraphMap P h ∧ LipschitzWith L h ∧
      IsLittleOrder P h 1 ∧
      ∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
        φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h := by
  have hs : HasStrictFDerivAt f (0 : State n →L[ℝ] State n) 0 := by
    have := (hf.contDiffAt (x := 0)).hasStrictFDerivAt (by norm_num)
    rwa [hDf] at this
  exact exists_centerManifold_of_hasStrictFDerivAt hP hε hεβ hcen hst hf0 hs

end State

end powerlib.Dynamics.CenterManifold
