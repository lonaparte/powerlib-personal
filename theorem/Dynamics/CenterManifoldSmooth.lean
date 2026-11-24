import theorem.Dynamics.CenterManifoldApprox

/-! # Smoothness of the centre manifold (foundation)

The centre manifold built by the Lyapunov–Perron method from a `C¹` cutoff of a `C¹`
nonlinearity is a `C¹` graph with `Dh(0) = 0` satisfying the invariance equation near `0`; the
gap condition of the existence theorem, `ε < β`, suffices.

Scope.
* The setting of `theorem/Dynamics/CenterManifold.lean`: a projection `P` commuting with `A`, the
  dichotomy `‖e^{tA}P‖ ≤ K e^{ε|t|}` (all `t`), `‖e^{tA}(1 − P)‖ ≤ K e^{−βt}` (`t ≥ 0`),
  `0 ≤ ε < β`, as theorem hypotheses. The Lyapunov–Perron estimates are stated on a real Banach
  space; the smoothness of the fixed points needs closed balls to be compact (`ProperSpace`), the
  `C¹` cutoff a finite-dimensional inner product space (the applications take `E = State n`).
* The nonlinearity `f` is `C¹` near `0` (on `ℝⁿ`: `C¹`), `f(0) = 0`, `Df(0) = 0`. The centre
  manifold is the one constructed with a `C¹` cutoff `g` of `f` with `‖Dg‖ ≤ δ` (not the
  piecewise linear cutoff of `exists_centerManifold`); centre manifolds are not unique, the
  theorem asserts that this one is `C¹` (globally, since `g` is). Higher smoothness (`C^k` under
  `kε < β`) is not treated.
* Generic analysis; nothing here describes a physical system (foundation).

Source: Vanderbauwhede, "Centre manifolds, normal forms and elementary bifurcations" (1989),
§2–3 (smoothness of the Lyapunov–Perron fixed point in the centre datum on a scale of weighted
spaces; the variational equation is solved at the weight `η`, the remainder is estimated at a
larger weight `ζ < β`); Vanderbauwhede & van Gils, "Center manifolds and contractions on a scale
of Banach spaces" (1987); Carr, *Applications of Centre Manifold Theory* (1981), Ch. 2.
The fibre contraction theorem (Hirsch–Pugh) is not used: the derivative candidate is the fixed
point of the variational equation, and the loss of weight `η → ζ` replaces the fibre iteration.

Results.
* The a priori bound of the linear Lyapunov–Perron equation `r = lpMap w (B r + b)`,
  `‖B‖ ≤ δ` (`norm_le_of_eq_lpMap`); the solutions of the variational equation are the
  time-dependent fixed points `LyapunovPerron.exists_fixedPoint_timeDep`.
* `exists_uniform_taylor`: on the balls of a proper space, a `C¹` map has a uniformly small
  first-order remainder and a uniformly small oscillation of its derivative at small distances.
* **Smoothness of the fixed points** (`hasFDerivAt_fixedPoint`, `contDiff_fixedPoint`): for a
  `C¹` nonlinearity `g` with `‖Dg‖ ≤ δ` and `Kδκ < 1` at two weights `ε < η < ζ < β`, the fixed
  points `x_u` of `x = lpMap u (g ∘ x)` satisfy, for every `t`, `u ↦ x_u(t)` is `C¹`; its
  derivative `D_u(t)` solves the variational equation `D_u v = lpMap v (Dg(x_u) D_u v)` and is
  continuous in `u`.
* `invarianceDefect_eq_zero_of_mem_graph`: a graph carrying, through each of its points, a
  solution that stays on it satisfies the invariance equation wherever `h` is differentiable.
* `exists_contDiff_small_cutoff`: a `C¹` cutoff `g` of `f` with `‖Dg‖ ≤ δ` (the cutoff
  `exists_contDiff_cutoff` of `f/δ`, rescaled).
* **The theorem**: `exists_centerManifold_contDiff_data` (the construction with its parameters,
  the cutoff field and the whole-line solutions on the graph),
  `exists_centerManifold_contDiff_of_contDiffAt` (finite-dimensional inner product space) and
  `exists_centerManifold_contDiff` (`ℝⁿ`, canonical local-invariance form): a locally invariant
  Lipschitz centre manifold `h` with `h(u) = o(‖u‖)`, `h` of class `C¹`, `Dh(0) = 0`, and
  the invariance equation near `0` (`IsInvariantGraph`).
-/

noncomputable section
namespace powerlib.Dynamics.CenterManifold

open Set Filter Topology MeasureTheory Asymptotics Metric
open powerlib.Dynamics.LyapunovPerron

/-! ## The linear Lyapunov–Perron equation -/

section Weighted

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {A P : E →L[ℝ] E} {K ε η β : ℝ}

/-- **The a priori bound of the linear Lyapunov–Perron equation.** If `r = lpMap w (B r + b)`
with `‖B(s)‖ ≤ δ`, `‖b(s)‖ ≤ M e^{η|s|}`, `K δ κ < 1` and `r` of weighted growth `e^{η|t|}`,
then `‖r(t)‖ ≤ K (‖w‖ + M κ)/(1 − K δ κ) e^{η|t|}`. -/
@[tmio T, powerlib_foundation] theorem norm_le_of_eq_lpMap (hε : 0 ≤ ε) (hεη : ε < η)
    (hηβ : η < β) (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {B : ℝ → E →L[ℝ] E} {δ : NNReal} (hB : Continuous B) (hBδ : ∀ s, ‖B s‖ ≤ δ)
    (hk : K * δ * gapConst ε η β < 1) {b r : ℝ → E} {w : E} {M Z : ℝ} (hb : Continuous b)
    (hM : 0 ≤ M) (hbM : ∀ s, ‖b s‖ ≤ M * Real.exp (η * |s|)) (hr : Continuous r)
    (hrZ : ∀ t, ‖r t‖ ≤ Z * Real.exp (η * |t|))
    (hrw : ∀ t, r t = lpMap A P w (fun s => B s (r s) + b s) t) (t : ℝ) :
    ‖r t‖ ≤ K * (‖w‖ + M * gapConst ε η β) / (1 - K * δ * gapConst ε η β) *
      Real.exp (η * |t|) := by
  have hK := nonneg_of_stable_bound hst
  have hκ := (gapConst_pos hεη hηβ).le
  refine le_of_contract (a := fun t => ‖r t‖) (w := fun t => Real.exp (η * |t|))
    (k := K * δ * gapConst ε η β) (Z₀ := Z) (by positivity) hk hrZ (fun Z' hZ' t => ?_) t
  have hZ0 : 0 ≤ Z' := by
    have := (norm_nonneg _).trans (hZ' 0); simpa using this
  have hd : ∀ s, ‖B s (r s) + b s‖ ≤ (δ * Z' + M) * Real.exp (η * |s|) := by
    intro s
    calc ‖B s (r s) + b s‖ ≤ ‖B s‖ * ‖r s‖ + ‖b s‖ :=
          (norm_add_le _ _).trans (add_le_add ((B s).le_opNorm _) le_rfl)
      _ ≤ δ * (Z' * Real.exp (η * |s|)) + M * Real.exp (η * |s|) :=
          add_le_add (mul_le_mul (hBδ s) (hZ' s) (norm_nonneg _) δ.coe_nonneg) (hbM s)
      _ = _ := by ring
  have hbd := norm_lpMap_le (A := A) (P := P) (b := fun s => B s (r s) + b s)
    ((hB.clm_apply hr).add hb) (by positivity) hd hε hεη hηβ hcen hst w t
  change ‖r t‖ ≤ (K * δ * gapConst ε η β * Z' + K * (‖w‖ + M * gapConst ε η β)) *
    Real.exp (η * |t|)
  rw [hrw t]
  refine hbd.trans_eq ?_
  ring

end Weighted

/-! ## Scalar estimates of the loss of weight -/

/-- A function of growth `c₁ e^{η|s|}` that is at most `c₂` on `[−T, T]` is at most
`(c₂ + c₁ e^{−(ζ−η)T}) e^{ζ|s|}` for `ζ ≥ η ≥ 0`. -/
@[tmio T, powerlib_foundation] private theorem le_exp_of_le_window {a : ℝ → ℝ}
    {η ζ c₁ c₂ T : ℝ} (hη : 0 ≤ η) (hηζ : η ≤ ζ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (h₁ : ∀ s, a s ≤ c₁ * Real.exp (η * |s|)) (h₂ : ∀ s, |s| ≤ T → a s ≤ c₂) (s : ℝ) :
    a s ≤ (c₂ + c₁ * Real.exp (-((ζ - η) * T))) * Real.exp (ζ * |s|) := by
  have hζ : 0 ≤ ζ := hη.trans hηζ
  have he : 1 ≤ Real.exp (ζ * |s|) := Real.one_le_exp (mul_nonneg hζ (abs_nonneg s))
  have hp : 0 ≤ c₁ * Real.exp (-((ζ - η) * T)) := mul_nonneg hc₁ (Real.exp_pos _).le
  rcases le_or_gt |s| T with hs | hs
  · calc a s ≤ c₂ := h₂ s hs
      _ ≤ c₂ * Real.exp (ζ * |s|) := le_mul_of_one_le_right hc₂ he
      _ ≤ _ := by gcongr; linarith
  · have hm : (ζ - η) * T ≤ (ζ - η) * |s| :=
      mul_le_mul_of_nonneg_left hs.le (sub_nonneg.2 hηζ)
    calc a s ≤ c₁ * Real.exp (η * |s|) := h₁ s
      _ = c₁ * Real.exp (-((ζ - η) * |s|)) * Real.exp (ζ * |s|) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ c₁ * Real.exp (-((ζ - η) * T)) * Real.exp (ζ * |s|) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.2 (by linarith)) hc₁) (Real.exp_pos _).le
      _ ≤ _ := by gcongr; linarith

@[tmio T, powerlib_foundation] private theorem exists_mul_exp_neg_le (c : ℝ) {γ θ : ℝ}
    (hγ : 0 < γ) (hθ : 0 < θ) : ∃ T ≥ 0, c * Real.exp (-(γ * T)) ≤ θ := by
  have ht : Tendsto (fun T : ℝ => c * Real.exp (-(γ * T))) atTop (𝓝 (c * 0)) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hγ)).const_mul c
  rw [mul_zero] at ht
  obtain ⟨T, hT, hT0⟩ := ((ht.eventually (gt_mem_nhds hθ)).and (eventually_ge_atTop 0)).exists
  exact ⟨T, hT0, hT.le⟩

/-! ## Smoothness of the fixed points -/

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ProperSpace E]
  {A P : E →L[ℝ] E}

omit [CompleteSpace E] in
/-- **Uniform first-order estimates on balls.** For `g` of class `C¹` on a proper space and
`θ > 0`, on the ball of radius `R` there is `ρ > 0` with `‖Dg(y') − Dg(y)‖ ≤ θ` and
`‖g(y') − g(y) − Dg(y)(y' − y)‖ ≤ θ ‖y' − y‖` whenever `‖y' − y‖ ≤ ρ` (uniform continuity of
`Dg` on the compact ball and the mean value inequality). -/
@[tmio T, powerlib_foundation] theorem exists_uniform_taylor {g : E → E} (hg : ContDiff ℝ 1 g)
    (R : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ ρ > 0, ∀ y y' : E, ‖y‖ ≤ R → ‖y'‖ ≤ R → ‖y' - y‖ ≤ ρ →
      ‖fderiv ℝ g y' - fderiv ℝ g y‖ ≤ θ ∧
        ‖g y' - g y - fderiv ℝ g y (y' - y)‖ ≤ θ * ‖y' - y‖ := by
  have hc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  obtain ⟨ρ, hρ, hρu⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : E) R).uniformContinuousOn_of_continuous hc.continuousOn) θ hθ
  have hD : ∀ y z : E, ‖y‖ ≤ R → ‖z‖ ≤ R → ‖z - y‖ ≤ ρ / 2 →
      ‖fderiv ℝ g z - fderiv ℝ g y‖ ≤ θ := fun y z hy hz hzy => by
    have := hρu z (by simpa using hz) y (by simpa using hy)
      (by rw [dist_eq_norm]; linarith)
    rw [dist_eq_norm] at this
    exact this.le
  refine ⟨ρ / 2, by positivity, fun y y' hy hy' hyy => ⟨hD y y' hy hy' hyy, ?_⟩⟩
  have hs : Convex ℝ (closedBall (0 : E) R ∩ closedBall y (ρ / 2)) :=
    (convex_closedBall _ _).inter (convex_closedBall _ _)
  refine hs.norm_image_sub_le_of_norm_fderiv_le'
    (fun z _ => hg.differentiable one_ne_zero z) (fun z hz => ?_)
    ⟨by simpa using hy, mem_closedBall_self (by positivity)⟩
    ⟨by simpa using hy', by rw [mem_closedBall, dist_eq_norm]; exact hyy⟩
  obtain ⟨hz1, hz2⟩ := hz
  rw [mem_closedBall, dist_zero_right] at hz1
  rw [mem_closedBall, dist_eq_norm] at hz2
  exact hD y z hy hz1 hz2

/-- **Differentiability of the Lyapunov–Perron fixed points in the centre datum** (loss of
weight). Let `g` be `C¹` with `‖Dg‖ ≤ δ`, `g(0) = 0`, and `K δ κ < 1` at two weights
`ε < η < ζ < β`. If `x_u = lpMap u (g ∘ x_u)` for every `u` (continuous, of growth `e^{η|t|}`),
then for every `t` the map `u ↦ x_u(t)` has a derivative `D_u(t)`, continuous in `u`, that
solves the variational equation `D_u(t) v = lpMap v (s ↦ Dg(x_u(s)) D_u(s) v) t`. The
derivative is the fixed point of the variational equation at the weight `η`; the remainder
`x_{u+v} − x_u − D_u v` and the variation `D_{u'} − D_u` solve the variational equation with a
forcing that is small on a window `[−T, T]` and `O(e^{η|s|})` outside, hence small at the
weight `ζ`. -/
@[tmio T, powerlib_foundation] theorem hasFDerivAt_fixedPoint {K ε η ζ β : ℝ} (hε : 0 ≤ ε)
    (hεη : ε < η) (hηζ : η < ζ) (hζβ : ζ < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {g : E → E} {δ : NNReal} (hg : ContDiff ℝ 1 g) (hDg : ∀ x, ‖fderiv ℝ g x‖ ≤ δ)
    (hg0 : g 0 = 0) (hkη : K * δ * gapConst ε η β < 1) (hkζ : K * δ * gapConst ε ζ β < 1)
    {X : E → ℝ → E} (hXc : ∀ u, Continuous (X u))
    (hXb : ∀ u, ∃ C, ∀ t, ‖X u t‖ ≤ C * Real.exp (η * |t|))
    (hX : ∀ u t, X u t = lpMap A P u (fun s => g (X u s)) t) :
    ∃ D : E → ℝ → E →L[ℝ] E, (∀ u t, HasFDerivAt (fun u => X u t) (D u t) u) ∧
      (∀ t, Continuous fun u => D u t) ∧
      ∀ u v t, D u t v = lpMap A P v (fun s => fderiv ℝ g (X u s) (D u s v)) t := by
  have hK := nonneg_of_stable_bound hst
  have hη : 0 ≤ η := hε.trans hεη.le
  have hηβ : η < β := hηζ.trans hζβ
  have hεζ : ε < ζ := hεη.trans hηζ
  have hκη := gapConst_pos hεη hηβ
  have hκζ := gapConst_pos hεζ hζβ
  have hk1 : 0 < 1 - K * δ * gapConst ε η β := sub_pos.2 hkη
  have hk2 : 0 < 1 - K * δ * gapConst ε ζ β := sub_pos.2 hkζ
  have hgL : LipschitzWith δ g := lipschitzWith_of_nnnorm_fderiv_le
    (hg.differentiable one_ne_zero) fun x => by
      rw [← NNReal.coe_le_coe, coe_nnnorm]; exact hDg x
  have hDc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  choose CX hCX using hXb
  set L₀ := K / (1 - K * δ * gapConst ε η β) with hL₀
  have hL₀0 : 0 ≤ L₀ := div_nonneg hK hk1.le
  -- Lipschitz dependence of the fixed points on the centre datum
  have hXL : ∀ u u' t, ‖X u' t - X u t‖ ≤ L₀ * ‖u' - u‖ * Real.exp (η * |t|) := by
    intro u u' t
    have := norm_sub_fixedPoint_le hε hεη hηβ hcen hst hgL hg0 hkη (hXc u') (hXc u) (hCX u')
      (hCX u) (hX u') (hX u) t
    refine this.trans_eq ?_
    rw [hL₀]; ring
  have hgX : ∀ u s, ‖g (X u s)‖ ≤ (δ * |CX u|) * Real.exp (η * |s|) := fun u s =>
    (hgL.norm_le_mul hg0 _).trans (by
      rw [mul_assoc]; gcongr; exact (hCX u s).trans (by gcongr; exact le_abs_self _))
  -- the variational equation and its solutions
  have hBc : ∀ u, Continuous fun s => fderiv ℝ g (X u s) := fun u => hDc.comp (hXc u)
  have hex : ∀ u v, ∃ y : ℝ → E, Continuous y ∧
      (∃ C, 0 ≤ C ∧ ∀ t, ‖y t‖ ≤ C * Real.exp (η * |t|)) ∧
      ∀ t, y t = lpMap A P v (fun s => fderiv ℝ g (X u s) (y s)) t := fun u v =>
    exists_fixedPoint_timeDep hε hεη hηβ hcen hst (G := fun s y => fderiv ℝ g (X u s) y)
      (((hBc u).comp continuous_fst).clm_apply continuous_snd)
      (fun s => (fderiv ℝ g (X u s)).lipschitzWith.weaken (by
        rw [← NNReal.coe_le_coe, coe_nnnorm]; exact hDg _))
      (fun s => map_zero _) hkη v
  choose Y hYc hYb hY using hex
  choose CY hCY0 hCY using hYb
  have hF : ∀ u v, Continuous (fun s => fderiv ℝ g (X u s) (Y u v s)) ∧
      ∀ s, ‖fderiv ℝ g (X u s) (Y u v s)‖ ≤ (δ * CY u v) * Real.exp (η * |s|) := fun u v =>
    ⟨(hBc u).clm_apply (hYc u v), fun s => ((fderiv ℝ g (X u s)).le_opNorm _).trans (by
      rw [mul_assoc]; exact mul_le_mul (hDg _) (hCY u v s) (norm_nonneg _) δ.coe_nonneg)⟩
  have hYbd : ∀ u v t, ‖Y u v t‖ ≤ L₀ * ‖v‖ * Real.exp (η * |t|) := by
    intro u v t
    have := norm_le_of_eq_lpMap hε hεη hηβ hcen hst (hBc u) (fun s => hDg _) hkη
      (b := fun _ => 0) continuous_const le_rfl (fun s => by simp) (hYc u v) (hCY u v)
      (fun t => by simpa using hY u v t) t
    refine this.trans_eq ?_
    rw [hL₀]; ring
  have hδC : ∀ u v, 0 ≤ (δ : ℝ) * CY u v := fun u v => mul_nonneg δ.coe_nonneg (hCY0 u v)
  have hn3 : ∀ a b c : E, ‖a - b - c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := fun a b c =>
    (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  -- additivity of the solutions in the centre datum (uniqueness)
  have hadd : ∀ u v v' t, Y u (v + v') t = Y u v t + Y u v' t := by
    intro u v v' t
    set r : ℝ → E := fun s => Y u (v + v') s - Y u v s - Y u v' s with hr
    have hreq : ∀ s, r s = lpMap A P 0
        (fun s => fderiv ℝ g (X u s) (r s) + (fun _ => (0 : E)) s) s := by
      intro s
      have e1 := lpMap_sub (A := A) (P := P) (hF u (v + v')).1 (hF u v).1 (hδC _ _)
        (hδC _ _) (hF u (v + v')).2 (hF u v).2 hη hηβ hst (v + v') v s
      have e2 := lpMap_sub (A := A) (P := P)
        (b₁ := fun s => fderiv ℝ g (X u s) (Y u (v + v') s) - fderiv ℝ g (X u s) (Y u v s))
        ((hF u (v + v')).1.sub (hF u v).1) (hF u v').1
        (C₁ := δ * CY u (v + v') + δ * CY u v) (add_nonneg (hδC _ _) (hδC _ _)) (hδC _ _)
        (fun s => (norm_sub_le _ _).trans (by
          rw [add_mul]; exact add_le_add ((hF u _).2 s) ((hF u v).2 s))) (hF u v').2 hη hηβ hst
        (v + v' - v) v' s
      simp only [hr]
      rw [hY u (v + v') s, hY u v s, hY u v' s, e1, e2, show v + v' - v - v' = 0 by abel]
      refine congrArg (fun b => lpMap A P 0 b s) (funext fun s => ?_)
      simp only [map_sub, add_zero]
    have hbd := norm_le_of_eq_lpMap hε hεη hηβ hcen hst (hBc u) (fun s => hDg _) hkη
      (b := fun _ => 0) (r := r) (w := 0) continuous_const le_rfl (fun s => by simp)
      (((hYc u (v + v')).sub (hYc u v)).sub (hYc u v'))
      (Z := CY u (v + v') + CY u v + CY u v') (fun s => (hn3 _ _ _).trans (by
        rw [add_mul, add_mul]
        exact add_le_add (add_le_add (hCY _ _ s) (hCY _ _ s)) (hCY _ _ s))) hreq t
    simp only [norm_zero, zero_add, zero_mul, mul_zero, zero_div] at hbd
    have h0 : r t = 0 := norm_le_zero_iff.1 hbd
    simp only [hr, sub_sub, sub_eq_zero] at h0
    exact h0
  -- the derivative candidate
  let D : E → ℝ → E →L[ℝ] E := fun u t =>
    (AddMonoidHom.mk' (fun v => Y u v t) fun v v' => hadd u v v' t).toRealLinearMap
      (AddMonoidHomClass.continuous_of_bound _ (L₀ * Real.exp (η * |t|)) fun v =>
        (hYbd u v t).trans_eq (by ring))
  have hDapp : ∀ u t v, D u t v = Y u v t := fun _ _ _ => rfl
  -- uniform control on a window `[−T, T]` for nearby centre data
  have hloc : ∀ u (T θ : ℝ), 0 ≤ T → 0 < θ → ∃ ρ > 0, ∀ u', ‖u' - u‖ ≤ ρ → ∀ s, |s| ≤ T →
      ‖X u' s - X u s‖ ≤ L₀ * ‖u' - u‖ * Real.exp (η * T) ∧
      ‖fderiv ℝ g (X u' s) - fderiv ℝ g (X u s)‖ ≤ θ ∧
      ‖g (X u' s) - g (X u s) - fderiv ℝ g (X u s) (X u' s - X u s)‖ ≤
        θ * ‖X u' s - X u s‖ := by
    intro u T θ hT hθ
    set R := |CX u| * Real.exp (η * T) + L₀ * Real.exp (η * T) with hR
    obtain ⟨ρ, hρ, hρt⟩ := exists_uniform_taylor hg R hθ
    have hm : 0 < L₀ * Real.exp (η * T) + 1 := by positivity
    refine ⟨min 1 (ρ / (L₀ * Real.exp (η * T) + 1)), by positivity, fun u' hu' s hs => ?_⟩
    have hu1 : ‖u' - u‖ ≤ 1 := hu'.trans (min_le_left _ _)
    have hu2 : ‖u' - u‖ ≤ ρ / (L₀ * Real.exp (η * T) + 1) := hu'.trans (min_le_right _ _)
    have heT : Real.exp (η * |s|) ≤ Real.exp (η * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs hη)
    have hd : ‖X u' s - X u s‖ ≤ L₀ * ‖u' - u‖ * Real.exp (η * T) :=
      (hXL u u' s).trans (by gcongr)
    have hxu : ‖X u s‖ ≤ |CX u| * Real.exp (η * T) :=
      (hCX u s).trans (mul_le_mul (le_abs_self _) heT (Real.exp_pos _).le (abs_nonneg _))
    have hxu' : ‖X u' s‖ ≤ R := by
      calc ‖X u' s‖ = ‖X u s + (X u' s - X u s)‖ := by rw [add_sub_cancel]
        _ ≤ ‖X u s‖ + ‖X u' s - X u s‖ := norm_add_le _ _
        _ ≤ |CX u| * Real.exp (η * T) + L₀ * 1 * Real.exp (η * T) := by
            refine add_le_add hxu (hd.trans ?_); gcongr
        _ = R := by rw [hR]; ring
    have hdρ : ‖X u' s - X u s‖ ≤ ρ := by
      calc _ ≤ L₀ * ‖u' - u‖ * Real.exp (η * T) := hd
        _ ≤ (L₀ * Real.exp (η * T) + 1) * ‖u' - u‖ := by nlinarith [norm_nonneg (u' - u)]
        _ ≤ (L₀ * Real.exp (η * T) + 1) * (ρ / (L₀ * Real.exp (η * T) + 1)) := by gcongr
        _ = ρ := by field_simp
    exact ⟨hd, hρt _ _ (hxu.trans (le_add_of_nonneg_right (by positivity))) hxu' hdρ⟩
  -- the final estimate at the weight `ζ`
  have hfinal : ∀ (u : E) (t T θ a : ℝ) (r R : ℝ → E), 0 ≤ θ → 0 ≤ a → Continuous r →
      (∃ Z, ∀ s, ‖r s‖ ≤ Z * Real.exp (η * |s|)) → Continuous R →
      (∀ s, ‖R s‖ ≤ (2 * δ * L₀ * a) * Real.exp (η * |s|)) →
      (∀ s, |s| ≤ T → ‖R s‖ ≤ θ * (L₀ * Real.exp (η * T)) * a) →
      (∀ s, r s = lpMap A P 0 (fun s => fderiv ℝ g (X u s) (r s) + R s) s) →
      ‖r t‖ ≤ K * gapConst ε ζ β * Real.exp (ζ * |t|) / (1 - K * δ * gapConst ε ζ β) *
        (θ * (L₀ * Real.exp (η * T)) + 2 * δ * L₀ * Real.exp (-((ζ - η) * T))) * a := by
    intro u t T θ a r R hθ ha hrc ⟨Z, hZ⟩ hRc hRg hRw hreq
    have hc₁ : 0 ≤ 2 * δ * L₀ * a := by positivity
    have hc₂ : 0 ≤ θ * (L₀ * Real.exp (η * T)) * a := by positivity
    have hRζ := le_exp_of_le_window (a := fun s => ‖R s‖) (ζ := ζ) hη hηζ.le hc₁ hc₂ hRg hRw
    have hrζ : ∀ s, ‖r s‖ ≤ |Z| * Real.exp (ζ * |s|) := fun s =>
      (hZ s).trans (mul_le_mul (le_abs_self Z)
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hηζ.le (abs_nonneg s)))
        (Real.exp_pos _).le (abs_nonneg Z))
    have := norm_le_of_eq_lpMap hε hεζ hζβ hcen hst (hBc u) (fun s => hDg _) hkζ hRc
      (by positivity) hRζ hrc hrζ hreq t
    refine this.trans_eq ?_
    rw [norm_zero]; ring
  -- the choice of the window and of the tolerance
  have hchoose : ∀ (t c : ℝ), 0 < c → ∃ T ≥ 0, ∃ θ > 0,
      K * gapConst ε ζ β * Real.exp (ζ * |t|) / (1 - K * δ * gapConst ε ζ β) *
        (θ * (L₀ * Real.exp (η * T)) + 2 * δ * L₀ * Real.exp (-((ζ - η) * T))) ≤ c := by
    intro t c hc
    set Λ := K * gapConst ε ζ β * Real.exp (ζ * |t|) / (1 - K * δ * gapConst ε ζ β) with hΛ
    have hΛ0 : 0 ≤ Λ :=
      div_nonneg (mul_nonneg (mul_nonneg hK hκζ.le) (Real.exp_pos _).le) hk2.le
    obtain ⟨T, hT, hTle⟩ := exists_mul_exp_neg_le (Λ * (2 * δ * L₀)) (sub_pos.2 hηζ)
      (half_pos hc)
    set m := Λ * (L₀ * Real.exp (η * T)) with hm
    have hm0 : 0 ≤ m := by positivity
    refine ⟨T, hT, c / (2 * (m + 1)), by positivity, ?_⟩
    have h1 : c / (2 * (m + 1)) * m ≤ c / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
      nlinarith
    calc Λ * (c / (2 * (m + 1)) * (L₀ * Real.exp (η * T)) +
          2 * δ * L₀ * Real.exp (-((ζ - η) * T)))
        = c / (2 * (m + 1)) * m + Λ * (2 * δ * L₀) * Real.exp (-((ζ - η) * T)) := by
          rw [hm]; ring
      _ ≤ c / 2 + c / 2 := add_le_add h1 hTle
      _ = c := by ring
  refine ⟨D, fun u t => ?_, fun t => ?_, fun u v t => ?_⟩
  · -- differentiability: the first-order remainder is small at the weight `ζ`
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
    intro c hc
    obtain ⟨T, hT, θ, hθ, hΛ⟩ := hchoose t c hc
    obtain ⟨ρ, hρ, hρl⟩ := hloc u T θ hT hθ
    filter_upwards [closedBall_mem_nhds (0 : E) hρ] with v hv
    rw [mem_closedBall, dist_zero_right] at hv
    have hv' : ‖(u + v) - u‖ = ‖v‖ := by rw [add_sub_cancel_left]
    show ‖X (u + v) t - X u t - D u t v‖ ≤ c * ‖v‖
    rw [hDapp]
    set r : ℝ → E := fun s => X (u + v) s - X u s - Y u v s with hr
    set R : ℝ → E := fun s => g (X (u + v) s) - g (X u s) -
      fderiv ℝ g (X u s) (X (u + v) s - X u s) with hR
    have hreq : ∀ s, r s = lpMap A P 0 (fun s => fderiv ℝ g (X u s) (r s) + R s) s := by
      intro s
      have e1 := lpMap_sub (A := A) (P := P) (b₁ := fun s => g (X (u + v) s))
        (b₂ := fun s => g (X u s)) (hgL.continuous.comp (hXc (u + v)))
        (hgL.continuous.comp (hXc u)) (by positivity) (by positivity) (hgX (u + v)) (hgX u) hη
        hηβ hst (u + v) u s
      have e2 := lpMap_sub (A := A) (P := P) (b₁ := fun s => g (X (u + v) s) - g (X u s))
        ((hgL.continuous.comp (hXc (u + v))).sub (hgL.continuous.comp (hXc u))) (hF u v).1
        (C₁ := δ * |CX (u + v)| + δ * |CX u|) (by positivity) (hδC _ _)
        (fun s => (norm_sub_le _ _).trans (by
          rw [add_mul]; exact add_le_add (hgX (u + v) s) (hgX u s))) (hF u v).2 hη hηβ hst
        (u + v - u) v s
      simp only [hr]
      rw [hX (u + v) s, hX u s, hY u v s]
      rw [e1, e2, show u + v - u - v = 0 by abel]
      refine congrArg (fun b => lpMap A P 0 b s) (funext fun s => ?_)
      simp only [hR, map_sub]
      abel
    have hRc : Continuous R :=
      ((hg.continuous.comp (hXc (u + v))).sub (hg.continuous.comp (hXc u))).sub
        ((hBc u).clm_apply ((hXc (u + v)).sub (hXc u)))
    have hRg : ∀ s, ‖R s‖ ≤ (2 * δ * L₀ * ‖v‖) * Real.exp (η * |s|) := by
      intro s
      have hd := hXL u (u + v) s
      rw [hv'] at hd
      calc ‖R s‖ ≤ ‖g (X (u + v) s) - g (X u s)‖ +
            ‖fderiv ℝ g (X u s) (X (u + v) s - X u s)‖ := norm_sub_le _ _
        _ ≤ δ * ‖X (u + v) s - X u s‖ + δ * ‖X (u + v) s - X u s‖ := by
            refine add_le_add ?_ (((fderiv ℝ g _).le_opNorm _).trans
              (mul_le_mul_of_nonneg_right (hDg _) (norm_nonneg _)))
            simpa [dist_eq_norm] using hgL.dist_le_mul (X (u + v) s) (X u s)
        _ = 2 * δ * ‖X (u + v) s - X u s‖ := by ring
        _ ≤ 2 * δ * (L₀ * ‖v‖ * Real.exp (η * |s|)) := by gcongr
        _ = _ := by ring
    have hRw : ∀ s, |s| ≤ T → ‖R s‖ ≤ θ * (L₀ * Real.exp (η * T)) * ‖v‖ := by
      intro s hs
      obtain ⟨hd, -, htay⟩ := hρl (u + v) (by rw [hv']; exact hv) s hs
      rw [hv'] at hd
      calc ‖R s‖ ≤ θ * ‖X (u + v) s - X u s‖ := htay
        _ ≤ θ * (L₀ * ‖v‖ * Real.exp (η * T)) := by gcongr
        _ = _ := by ring
    have hrc : Continuous r := (((hXc (u + v)).sub (hXc u)).sub (hYc u v))
    have hrZ : ∃ Z, ∀ s, ‖r s‖ ≤ Z * Real.exp (η * |s|) :=
      ⟨|CX (u + v)| + |CX u| + CY u v, fun s => (hn3 _ _ _).trans (by
        rw [add_mul, add_mul]
        refine add_le_add (add_le_add ?_ ?_) (hCY u v s)
        · exact (hCX _ s).trans (by gcongr; exact le_abs_self _)
        · exact (hCX _ s).trans (by gcongr; exact le_abs_self _))⟩
    have hfin := hfinal u t T θ ‖v‖ r R hθ.le (norm_nonneg _) hrc hrZ hRc hRg hRw hreq
    exact hfin.trans (mul_le_mul_of_nonneg_right hΛ (norm_nonneg _))
  · -- continuity of the derivative in the operator norm
    rw [Metric.continuous_iff]
    intro u c hc
    obtain ⟨T, hT, θ, hθ, hΛ⟩ := hchoose t (c / 2) (half_pos hc)
    obtain ⟨ρ, hρ, hρl⟩ := hloc u T θ hT hθ
    refine ⟨ρ, hρ, fun u' hu' => ?_⟩
    rw [dist_eq_norm] at hu' ⊢
    refine lt_of_le_of_lt ?_ (half_lt_self hc)
    refine ContinuousLinearMap.opNorm_le_bound _ (half_pos hc).le fun v => ?_
    rw [sub_apply, hDapp, hDapp]
    set w : ℝ → E := fun s => Y u' v s - Y u v s with hw
    set R : ℝ → E := fun s => (fderiv ℝ g (X u' s) - fderiv ℝ g (X u s)) (Y u' v s) with hR
    have hweq : ∀ s, w s = lpMap A P 0 (fun s => fderiv ℝ g (X u s) (w s) + R s) s := by
      intro s
      have e1 := lpMap_sub (A := A) (P := P) (hF u' v).1 (hF u v).1 (hδC _ _)
        (hδC _ _) (hF u' v).2 (hF u v).2 hη hηβ hst v v s
      simp only [hw]
      rw [hY u' v s, hY u v s, e1, sub_self]
      refine congrArg (fun b => lpMap A P 0 b s) (funext fun s => ?_)
      simp only [hR, sub_apply, map_sub]
      abel
    have hRc : Continuous R := ((hBc u').sub (hBc u)).clm_apply (hYc u' v)
    have hRg : ∀ s, ‖R s‖ ≤ (2 * δ * L₀ * ‖v‖) * Real.exp (η * |s|) := by
      intro s
      calc ‖R s‖ ≤ ‖fderiv ℝ g (X u' s) - fderiv ℝ g (X u s)‖ * ‖Y u' v s‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (δ + δ) * (L₀ * ‖v‖ * Real.exp (η * |s|)) := by
            refine mul_le_mul ((norm_sub_le _ _).trans (add_le_add (hDg _) (hDg _)))
              (hYbd u' v s) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hRw : ∀ s, |s| ≤ T → ‖R s‖ ≤ θ * (L₀ * Real.exp (η * T)) * ‖v‖ := by
      intro s hs
      obtain ⟨-, hDd, -⟩ := hρl u' hu'.le s hs
      have heT : Real.exp (η * |s|) ≤ Real.exp (η * T) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs hη)
      calc ‖R s‖ ≤ ‖fderiv ℝ g (X u' s) - fderiv ℝ g (X u s)‖ * ‖Y u' v s‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ θ * (L₀ * ‖v‖ * Real.exp (η * T)) :=
            mul_le_mul hDd ((hYbd u' v s).trans (by gcongr)) (norm_nonneg _) hθ.le
        _ = _ := by ring
    have hwc : Continuous w := (hYc u' v).sub (hYc u v)
    have hwZ : ∃ Z, ∀ s, ‖w s‖ ≤ Z * Real.exp (η * |s|) :=
      ⟨CY u' v + CY u v, fun s => (norm_sub_le _ _).trans (by
        rw [add_mul]; exact add_le_add (hCY u' v s) (hCY u v s))⟩
    have hfin := hfinal u t T θ ‖v‖ w R hθ.le (norm_nonneg _) hwc hwZ hRc hRg hRw hweq
    exact hfin.trans (mul_le_mul_of_nonneg_right hΛ (norm_nonneg _))
  · -- the variational equation
    rw [hDapp]
    exact hY u v t

/-- **The fixed points are `C¹` in the centre datum**: under the hypotheses of
`hasFDerivAt_fixedPoint`, `u ↦ x_u(t)` is of class `C¹` for every `t`. -/
@[tmio T, powerlib_foundation] theorem contDiff_fixedPoint {K ε η ζ β : ℝ} (hε : 0 ≤ ε)
    (hεη : ε < η) (hηζ : η < ζ) (hζβ : ζ < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {g : E → E} {δ : NNReal} (hg : ContDiff ℝ 1 g) (hDg : ∀ x, ‖fderiv ℝ g x‖ ≤ δ)
    (hg0 : g 0 = 0) (hkη : K * δ * gapConst ε η β < 1) (hkζ : K * δ * gapConst ε ζ β < 1)
    {X : E → ℝ → E} (hXc : ∀ u, Continuous (X u))
    (hXb : ∀ u, ∃ C, ∀ t, ‖X u t‖ ≤ C * Real.exp (η * |t|))
    (hX : ∀ u t, X u t = lpMap A P u (fun s => g (X u s)) t) (t : ℝ) :
    ContDiff ℝ 1 fun u => X u t := by
  obtain ⟨D, hD, hDc, -⟩ := hasFDerivAt_fixedPoint hε hεη hηζ hζβ hcen hst hg hDg hg0 hkη hkζ
    hXc hXb hX
  refine contDiff_one_iff_fderiv.2 ⟨fun u => (hD u t).differentiableAt, ?_⟩
  rw [show fderiv ℝ (fun u => X u t) = fun u => D u t from funext fun u => (hD u t).fderiv]
  exact hDc t

end Smooth

/-! ## The invariance equation -/

section Invariance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A P : E →L[ℝ] E}

/-- **The invariance equation of an invariant graph.** If through every point of the graph of a
graph map `h` passes a solution of `ẋ = A x + g(x)` that stays on the graph, then at every
`u ∈ range P` where `h` is differentiable the invariance defect vanishes:
`Dh(u)(PAu + Pg(u + h u)) = (1 − P)A h(u) + (1 − P) g(u + h u)` (differentiate
`x(t) = P x(t) + h(x(t))` at the graph point `u + h u`). -/
@[tmio T, powerlib_foundation] theorem invarianceDefect_eq_zero_of_mem_graph
    (hP : IsCommutingProjection A P) {g h : E → E} (hh : IsGraphMap P h)
    (hglob : ∀ u, ∃ x : ℝ → E, x 0 = P u + h u ∧ (∀ t, HasDerivAt x (A (x t) + g (x t)) t) ∧
      ∀ t, x t ∈ graph P h) {u : E} (hu : P u = u) (hd : DifferentiableAt ℝ h u) :
    invarianceDefect A P g h u = 0 := by
  obtain ⟨x, hx0, hxd, hxg⟩ := hglob u
  rw [hu] at hx0
  have hPx0 : P (x 0) = u := by rw [hx0, map_add, hh.proj_apply, add_zero, hu]
  have hd' : HasFDerivAt h (fderiv ℝ h u) (P (x 0)) := by rw [hPx0]; exact hd.hasFDerivAt
  have hhd : HasFDerivAt h ((fderiv ℝ h u).comp P) (x 0) := by
    have := hd'.comp (x 0) P.hasFDerivAt
    rwa [show h ∘ P = h from funext hh.comp_proj] at this
  set x' := A (x 0) + g (x 0) with hx'
  have hsum : HasDerivAt (fun t => P (x t) + h (x t)) (P x' + fderiv ℝ h u (P x')) 0 :=
    (P.hasFDerivAt.comp_hasDerivAt 0 (hxd 0)).add (hhd.comp_hasDerivAt 0 (hxd 0))
  have key : x' = P x' + fderiv ℝ h u (P x') :=
    (hxd 0).unique (hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hxg t))
  have hPAh : P (A (h u)) = 0 := by rw [← hP.comm, hh.proj_apply, map_zero]
  have hPAu : P (A u) = A u := by rw [← hP.comm, hu]
  have hred : reducedField A P g h u = P x' := by
    simp only [reducedField, hx', hx0, map_add, hPAh, add_zero]
  have hnorm : normalField A P g h u = x' - P x' := by
    simp only [normalField, compl_apply, hx', hx0, map_add, hPAh, hPAu, sub_zero, add_zero]
    abel
  rw [invarianceDefect, hred, hnorm, sub_eq_zero, eq_sub_iff_add_eq, add_comm]
  exact key.symm

end Invariance

/-! ## The `C¹` centre manifold -/

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A P : E →L[ℝ] E}

/-- **A `C¹` cutoff with small derivative.** A map `f` of class `C¹` near `0` with `f(0) = 0`,
`Df(0) = 0` agrees near `0` with a globally `C¹` map `g`, `g(0) = 0`, `‖Dg‖ ≤ δ` everywhere:
`g = δ ψ` for the cutoff `ψ` of `f/δ` given by `exists_contDiff_cutoff`. -/
@[tmio T, powerlib_foundation] theorem exists_contDiff_small_cutoff {f : E → E}
    (hf : ContDiffAt ℝ 1 f 0) (hf0 : f 0 = 0) (hDf : fderiv ℝ f 0 = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r > 0, ∃ g : E → E, ContDiff ℝ 1 g ∧ g 0 = 0 ∧ (∀ x, ‖fderiv ℝ g x‖ ≤ δ) ∧
      ∀ x, ‖x‖ < r → g x = f x := by
  obtain ⟨r, hr, ψ, hψ, hψ0, hψd, -, hψf⟩ := exists_contDiff_cutoff (P := (0 : E →L[ℝ] E))
    (φ := fun x => δ⁻¹ • f x) (hf.const_smul δ⁻¹) (by simp [hf0])
    (by rw [fderiv_fun_const_smul (hf.differentiableAt one_ne_zero), hDf, smul_zero])
    (fun x => by simp)
  refine ⟨r, hr, fun x => δ • ψ x, hψ.const_smul δ, by simp [hψ0], fun x => ?_,
    fun x hx => ?_⟩
  · rw [fderiv_fun_const_smul (hψ.differentiable one_ne_zero x), norm_smul, Real.norm_eq_abs,
      abs_of_pos hδ]
    exact mul_le_of_le_one_right hδ.le (hψd x)
  · change δ • ψ x = f x
    rw [hψf x hx, smul_smul, mul_inv_cancel₀ hδ.ne', one_smul]

/-- **The `C¹` centre manifold with its parameters.** For weights `ε < η < ζ < β` and a bound
`δ > 0` with `K δ κ < 1` at `η` and at `ζ`: a `C¹` cutoff `g` of `f`, `δ`-Lipschitz, agreeing
with `f` on the ball of radius `ρ`, and a Lipschitz graph map `h` of class `C¹`, tangent to
`range P` (`h(u) = o(‖u‖)`, `Dh(0) = 0`) and satisfying the invariance equation near `0`,
whose graph is locally invariant for `ẋ = A x + f(x)` in that ball, with through every graph
point a whole-line solution of the cutoff field that stays on the graph and grows at most like
`K ‖P u‖ e^{η|t|}/(1 − Kδκ)`. -/
@[tmio T, powerlib_foundation] theorem exists_centerManifold_contDiff_data
    (hP : IsCommutingProjection A P) {K ε η ζ β : ℝ} (hε : 0 ≤ ε) (hεη : ε < η)
    (hηζ : η < ζ) (hζβ : ζ < β) (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {f : E → E} (hf : ContDiffAt ℝ 1 f 0) (hf0 : f 0 = 0) (hDf : fderiv ℝ f 0 = 0) {δ : ℝ}
    (hδ : 0 < δ) (hkη : K * δ * gapConst ε η β < 1) (hkζ : K * δ * gapConst ε ζ β < 1) :
    ∃ ρ > 0, ∃ g : E → E, LipschitzWith (Real.toNNReal δ) g ∧ g 0 = 0 ∧ ContDiff ℝ 1 g ∧
      (∀ y, ‖y‖ ≤ ρ → g y = f y) ∧ ∃ h : E → E, ∃ L : NNReal, IsGraphMap P h ∧
      LipschitzWith L h ∧ IsLittleOrder P h 1 ∧ ContDiff ℝ 1 h ∧ fderiv ℝ h 0 = 0 ∧
      IsInvariantGraph A P f h ∧
      (∀ (t₀ t₁ : ℝ) (φ : ℝ → E), IsIntegralCurveOn φ (fun _ y => fullField A f y) (Icc t₀ t₁) →
        φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h) ∧
      ∀ u, ∃ x : ℝ → E, x 0 = P u + h u ∧ (∀ t, HasDerivAt x (A (x t) + g (x t)) t) ∧
        (∀ t, x t ∈ graph P h) ∧
        ∀ t, ‖x t‖ ≤ K / (1 - K * δ * gapConst ε η β) * ‖P u‖ * Real.exp (η * |t|) := by
  have hK := nonneg_of_stable_bound hst
  have hη : 0 ≤ η := hε.trans hεη.le
  have hηβ : η < β := hηζ.trans hζβ
  have hk1 : 0 < 1 - K * δ * gapConst ε η β := sub_pos.2 hkη
  obtain ⟨r, hr, g, hg, hg0, hDg, hgf⟩ := exists_contDiff_small_cutoff hf hf0 hDf hδ
  have hδN : (Real.toNNReal δ : ℝ) = δ := Real.coe_toNNReal _ hδ.le
  have hDg' : ∀ x, ‖fderiv ℝ g x‖ ≤ Real.toNNReal δ := fun x => by rw [hδN]; exact hDg x
  have hgL : LipschitzWith (Real.toNNReal δ) g :=
    lipschitzWith_of_nnnorm_fderiv_le (hg.differentiable one_ne_zero) fun x => by
      rw [← NNReal.coe_le_coe, coe_nnnorm]; exact hDg' x
  have hkη' : K * (Real.toNNReal δ : ℝ) * gapConst ε η β < 1 := by rwa [hδN]
  have hkζ' : K * (Real.toNNReal δ : ℝ) * gapConst ε ζ β < 1 := by rwa [hδN]
  obtain ⟨h, hh, ⟨L, hL⟩, hglob⟩ :=
    exists_graph_of_lipschitz hP hε hεη hηβ hcen hst hgL hg0 hkη'
  choose x hx0 hxd hxg hxb hxs using hglob
  have hxc : ∀ u, Continuous (x u) := fun u =>
    continuous_iff_continuousAt.2 fun t => (hxd u t).continuousAt
  set C₁ := K / (1 - K * (Real.toNNReal δ : ℝ) * gapConst ε η β) with hC₁
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁, hδN]; exact div_nonneg hK hk1.le
  -- the solutions are the Lyapunov–Perron fixed points of their centre data
  have hxfix : ∀ u t, x u t = lpMap A P u (fun s => g (x u s)) t := by
    intro u t
    have hgx : ∀ s, ‖g (x u s)‖ ≤ ((Real.toNNReal δ : ℝ) * (C₁ * ‖P u‖)) *
        Real.exp (η * |s|) := fun s =>
      (hgL.norm_le_mul hg0 _).trans (by
        rw [mul_assoc]; gcongr; exact (hxb u s).trans_eq (by ring))
    have hv := eq_lpMap_of_hasDerivAt (b := fun s => g (x u s)) hP.commute hη hηβ hst
      (hgL.continuous.comp (hxc u)) (by positivity) hgx (C' := C₁ * ‖P u‖)
      (fun s => (hxb u s).trans_eq (by ring)) (hxd u) t
    have hPx : P (x u 0) = P u := by rw [hx0 u, map_add, hh.proj_apply, add_zero, hP.idem]
    rw [hv, ← hP.lpMap_proj (x u 0), hPx, hP.lpMap_proj]
  have hxb' : ∀ u, ∃ C, ∀ t, ‖x u t‖ ≤ C * Real.exp (η * |t|) := fun u =>
    ⟨C₁ * ‖P u‖, fun t => (hxb u t).trans_eq (by ring)⟩
  -- smoothness
  obtain ⟨D, hD, -, hDeq⟩ := hasFDerivAt_fixedPoint hε hεη hηζ hζβ hcen hst hg hDg' hg0 hkη'
    hkζ' hxc hxb' hxfix
  have hhx : h = fun u => (1 - P) (x u 0) := by
    funext u
    rw [hx0 u, map_add, hP.compl_proj, zero_add, compl_apply, hh.proj_apply, sub_zero]
  have hh1 : ContDiff ℝ 1 h := by
    rw [hhx]
    exact (1 - P).contDiff.comp (contDiff_fixedPoint hε hεη hηζ hζβ hcen hst hg hDg' hg0 hkη'
      hkζ' hxc hxb' hxfix 0)
  have hhD : HasFDerivAt h ((1 - P).comp (D 0 0)) 0 := by
    rw [hhx]; exact (1 - P).hasFDerivAt.comp 0 (hD 0 0)
  -- the derivative at `0`
  have hx00 : ∀ s, x 0 s = 0 := fun s => by
    have := hxb 0 s
    rw [map_zero, norm_zero, mul_zero, zero_mul] at this
    exact norm_le_zero_iff.1 this
  have hDg0 : fderiv ℝ g 0 = 0 := by
    have hev : g =ᶠ[𝓝 0] f := Filter.eventually_of_mem (ball_mem_nhds 0 hr) fun y hy =>
      hgf y (by simpa using hy)
    rw [hev.fderiv_eq, hDf]
  have hD0 : ∀ v, D 0 0 v = P v := fun v => by
    rw [hDeq, lpMap_zero]
    simp only [hx00, hDg0]
    simp [stableInit]
  have hfd0 : fderiv ℝ h 0 = 0 := by
    rw [hhD.fderiv]
    ext v
    rw [ContinuousLinearMap.comp_apply, hD0, hP.compl_proj]
    rfl
  have hd0 : HasFDerivAt h (0 : E →L[ℝ] E) 0 := by
    rw [← hfd0]; exact hh1.differentiable one_ne_zero 0 |>.hasFDerivAt
  -- tangency
  have htan : IsLittleOrder P h 1 := by
    have h1 : h =o[𝓝 0] fun v => v :=
      hd0.isLittleO.congr (fun v => by simp [hh.map_zero]) (fun v => by simp)
    rw [IsLittleOrder]
    simp only [Real.rpow_one]
    exact (h1.mono nhdsWithin_le_nhds).norm_right
  -- the invariance equation near `0`, where `f = g` on the graph
  have hinvg : IsInvariantGraph A P f h := by
    rw [IsInvariantGraph]
    have hL1 : 0 < 1 + (L : ℝ) := by positivity
    filter_upwards [inter_mem_nhdsWithin (Set.range P)
      (Metric.closedBall_mem_nhds (0 : E) (div_pos (half_pos hr) hL1))] with u ⟨⟨w, hw⟩, hu⟩
    subst hw
    rw [Metric.mem_closedBall, dist_zero_right] at hu
    refine ⟨hh1.differentiable one_ne_zero _, ?_⟩
    have hlift : ‖P w + h (P w)‖ ≤ r / 2 :=
      calc ‖P w + h (P w)‖ ≤ (1 + L) * ‖P w‖ := hh.norm_lift_le hL (P w)
        _ ≤ (1 + L) * ((r / 2) / (1 + L)) := mul_le_mul_of_nonneg_left hu hL1.le
        _ = r / 2 := by field_simp
    have hfg : f (P w + h (P w)) = g (P w + h (P w)) := (hgf _ (by linarith)).symm
    have heq : invarianceDefect A P f h (P w) = invarianceDefect A P g h (P w) := by
      simp only [invarianceDefect, reducedField, normalField, hfg]
    rw [heq]
    exact invarianceDefect_eq_zero_of_mem_graph hP hh (fun u => ⟨x u, hx0 u, hxd u, hxg u⟩)
      (hP.idem w) (hh1.differentiable one_ne_zero _)
  refine ⟨r / 2, half_pos hr, g, hgL, hg0, hg, fun y hy => hgf y (by linarith),
    h, L, hh, hL, htan, hh1, hfd0, hinvg, fun t₀ t₁ φ hφ h0 hφρ => ?_, fun u => ?_⟩
  · exact mem_graph_of_isIntegralCurveOn hgL (fun u => ⟨x u, hx0 u, hxd u, hxg u⟩)
      (fun y hy => (hgf y (by linarith)).symm) hφ h0 hφρ
  · refine ⟨x u, hx0 u, hxd u, hxg u, fun t => ?_⟩
    have := hxb u t
    rw [hC₁, hδN] at this
    exact this

/-- **`C¹` centre manifold theorem** (centre–stable case). Under the dichotomy
`‖e^{tA}P‖ ≤ K e^{ε|t|}` (all `t`), `‖e^{tA}(1 − P)‖ ≤ K e^{−βt}` (`t ≥ 0`), `0 ≤ ε < β`, for
`f` of class `C¹` near `0` with `f(0) = 0`, `Df(0) = 0`, there are `ρ > 0` and a Lipschitz graph
map `h : range P → range (1 − P)` of class `C¹` with `Dh(0) = 0` (hence `h(u) = o(‖u‖)`),
satisfying the invariance equation near `0`, whose graph is locally invariant in the ball of
radius `ρ`. -/
@[tmio T, powerlib_foundation] theorem exists_centerManifold_contDiff_of_contDiffAt
    (hP : IsCommutingProjection A P) {K ε β : ℝ} (hε : 0 ≤ ε) (hεβ : ε < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {f : E → E} (hf : ContDiffAt ℝ 1 f 0) (hf0 : f 0 = 0) (hDf : fderiv ℝ f 0 = 0) :
    ∃ ρ > 0, ∃ h : E → E, ∃ L : NNReal, IsGraphMap P h ∧ LipschitzWith L h ∧
      IsLittleOrder P h 1 ∧ ContDiff ℝ 1 h ∧ fderiv ℝ h 0 = 0 ∧ IsInvariantGraph A P f h ∧
      ∀ (t₀ t₁ : ℝ) (φ : ℝ → E), IsIntegralCurveOn φ (fun _ y => fullField A f y) (Icc t₀ t₁) →
        φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h := by
  have hK := nonneg_of_stable_bound hst
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
  obtain ⟨ρ, hρ, -, -, -, -, -, h, L, hh, hL, htan, hh1, hfd0, hig, hinv, -⟩ :=
    exists_centerManifold_contDiff_data hP hε hεη hηζ hζβ hcen hst hf hf0 hDf hδ hkη hkζ
  exact ⟨ρ, hρ, h, L, hh, hL, htan, hh1, hfd0, hig, hinv⟩

end Manifold

/-! ## The state space `ℝⁿ` -/

section State

variable {n : ℕ} {A P : State n →L[ℝ] State n}

/-- **`C¹` centre manifold theorem on `ℝⁿ`** (centre–stable case), in the canonical
local-invariance form: for `f` of class `C¹` with `f(0) = 0`, `Df(0) = 0`, and the dichotomy
with `0 ≤ ε < β`, there are `ρ > 0` and a Lipschitz graph map `h` of class `C¹` with
`Dh(0) = 0`, `h(u) = o(‖u‖)` on `range P` and the invariance equation near `0`, whose graph is
locally invariant in the ball of radius `ρ`. -/
@[tmio T, powerlib_foundation] theorem exists_centerManifold_contDiff
    (hP : IsCommutingProjection A P) {K ε β : ℝ} (hε : 0 ≤ ε) (hεβ : ε < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {f : State n → State n} (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0) (hDf : fderiv ℝ f 0 = 0) :
    ∃ ρ > 0, ∃ h : State n → State n, ∃ L : NNReal, IsGraphMap P h ∧ LipschitzWith L h ∧
      IsLittleOrder P h 1 ∧ ContDiff ℝ 1 h ∧ fderiv ℝ h 0 = 0 ∧ IsInvariantGraph A P f h ∧
      ∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
        φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h :=
  exists_centerManifold_contDiff_of_contDiffAt hP hε hεβ hcen hst hf.contDiffAt hf0 hDf

end State

end powerlib.Dynamics.CenterManifold
