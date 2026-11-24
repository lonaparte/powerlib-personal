import theorem.Dynamics.CenterReduction
import theorem.Dynamics.CenterManifoldPhase

/-! # Carr's approximation theorem for any tangent centre manifold (foundation)

Carr's approximation theorem is proved in `theorem/Dynamics/CenterManifoldApprox.lean` for the
centre manifold that the Lyapunov–Perron construction produces. Centre manifolds are not unique;
here the theorem is proved for every graph map `h` over `range P` with strict derivative `0` at
`0` whose graph is locally invariant: a candidate `φ` with invariance defect `O(‖u‖^q)` satisfies
`h(u) − φ(u) = O(‖u‖^q)`. Consequences: the quadratic part of every tangent centre manifold is
the solution of the homological equation, and two tangent centre manifolds (one of them `C¹`)
agree to every order `q` with `qε < β`.

Scope.
* Generic: `State n = ℝⁿ` (the segment estimates on any real Banach space `E`), `A`, `P` with
  `P² = P`, `AP = PA` (`IsCommutingProjection`), the dichotomy `‖e^{tA}P‖ ≤ K e^{ε|t|}` (all `t`),
  `‖e^{tA}(1 − P)‖ ≤ K e^{−βt}` (`t ≥ 0`) as theorem hypotheses with the gap `qε < β` (`q ≥ 1`);
  `f(0) = 0` with strict derivative `0` at `0` (`C¹` with `Df(0) = 0` suffices).
* The graph map `h` only has strict derivative `0` at `0`: no `C¹`, no Lipschitz bound away from
  `0`, no construction, no uniqueness. Its local invariance is the forward form of
  `theorem/Dynamics/CenterManifoldDefs.lean` (solutions of the full field starting on the graph
  stay on it while they stay in the ball of radius `ρ`). The candidate `φ` is as in
  `CenterManifoldApprox`: `C¹` near `0`, `φ(0) = 0`, `Dφ(0) = 0`, values in `ker P`.
* Nothing here describes a physical system (foundation).

Source: Carr, *Applications of Centre Manifold Theory* (1981), Ch. 2, Theorem 3 (§2.5);
Sijbrand, "Properties of center manifolds", Trans. AMS 289 (1985) (non-uniqueness of centre
manifolds, common Taylor expansion); Vanderbauwhede, "Centre manifolds, normal forms and
elementary bifurcations" (1989), §2. Carr's graph transform characterizes only the constructed
manifold, so the proof works along backward solutions on the graph of `h`: for `u ∈ range P`
small, the backward solution of the reduced cutoff field `u̇ = PAu + Pg(u + h'(u))` (`g`, `h'`
globally Lipschitz cutoffs of `f`, `h`) grows at most like `e^{η|t|}` (`ε < η`, `qη < β`), so it
stays in a small ball on `[−T, 0]` with `‖u‖ e^{ηT} = c₀`; forward local invariance and
uniqueness lift it to a solution of the full field on the graph of `h`; along it
`z = (1 − P)x − ψ(P x)` (`ψ` a `C¹` cutoff of `φ`) solves `ż = A z + b` with
`‖b‖ ≤ M ‖P x‖^q + (‖1 − P‖ + ‖P‖) δ ‖z‖`, its stable representation on `[−T, 0]` contracts in
the weight `e^{−qηt}`, and the boundary term `K e^{−βT} ‖z(−T)‖` is `O(‖u‖^q)` because `qη < β`.

Results.
* Segment estimates (any Banach space): `eq_expFlow_add_integral_of_Icc` (variation of constants
  on `[a, c]`), `norm_le_of_segment_stable` (`‖z(c)‖ ≤ K e^{−β(c−a)} ‖z(a)‖ + K B e^{−γc}/(β − γ)`
  for the stable component), `norm_le_of_segment_center`, `norm_le_of_segment_centerBound`
  (backward growth `‖w(t)‖ ≤ K ‖w(0)‖/(1 − Kc/(η − ε)) e^{−ηt}` on the centre subspace),
  `norm_sub_cutoff_le_of_segment` (Carr's estimate on a segment, with its boundary term).
* Tools on `ℝⁿ`: `exists_isIntegralCurveOn_Iic` (backward solutions of a globally Lipschitz
  field), `isIntegralCurveOn_lift_of_cutoff` (solutions of the reduced cutoff field lift to
  solutions on the graph), `invarianceDefect_eq_zero_of_invariantGraph` (a locally invariant graph
  satisfies the invariance equation near `0` wherever it is differentiable).
* **The theorem**: `isOrder_sub_of_invariantGraph`.
* Consequences: `hasQuadraticPart_of_invariantGraph` (`q = 3`, `3ε < β`: the quadratic part of
  every tangent centre manifold is the homological solution `H₀`, the hypothesis `hcarr` of
  `HasQuadraticPart.apply_eq_of_homological` for any such `h`), `isOrder_sub_of_invariantGraphs`
  (two tangent centre manifolds, one of them `C¹`, agree to order `q` for every `q ≥ 1` with
  `qε < β`). The end-to-end `ℓ₁` laws (`unstable_of_firstLyapunov_pos`,
  `localAsymptoticStable_of_firstLyapunov_neg`) conclude about the full field only and need no
  change.
-/

noncomputable section
namespace powerlib.Dynamics.CenterManifold

open Set Filter Topology MeasureTheory Asymptotics Metric
open powerlib.Dynamics.LyapunovPerron

/-! ## Estimates on a segment -/

section Segment

@[tmio T, powerlib_foundation] private theorem integral_exp_le {d : ℝ} (hd : 0 < d) (a c : ℝ) :
    ∫ s in a..c, Real.exp (d * s) ≤ Real.exp (d * c) / d := by
  have hG : ∀ s, HasDerivAt (fun s => Real.exp (d * s) / d) (Real.exp (d * s)) s := fun s => by
    have h := (((hasDerivAt_id' s).const_mul d).exp).div_const d
    refine h.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hG s)
    ((by fun_prop : Continuous fun s : ℝ => Real.exp (d * s)).intervalIntegrable _ _)]
  have : 0 ≤ Real.exp (d * a) / d := by positivity
  linarith

@[tmio T, powerlib_foundation] private theorem integral_exp_neg_le {d : ℝ} (hd : 0 < d)
    (a c : ℝ) : ∫ s in a..c, Real.exp (-(d * s)) ≤ Real.exp (-(d * a)) / d := by
  have hG : ∀ s, HasDerivAt (fun s => -Real.exp (-(d * s)) / d) (Real.exp (-(d * s))) s :=
    fun s => by
      have h1 : HasDerivAt (fun s : ℝ => -(d * s)) (-(d * 1)) s :=
        ((hasDerivAt_id' s).const_mul d).neg
      have h2 : HasDerivAt (fun s : ℝ => -Real.exp (-(d * s)) / d)
          (-(Real.exp (-(d * s)) * -(d * 1)) / d) s := (h1.exp.neg).div_const d
      exact h2.congr_deriv (by field_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hG s)
    ((by fun_prop : Continuous fun s : ℝ => Real.exp (-(d * s))).intervalIntegrable _ _)]
  have : 0 ≤ Real.exp (-(d * c)) / d := by positivity
  have e : -Real.exp (-(d * c)) / d - -Real.exp (-(d * a)) / d =
      Real.exp (-(d * a)) / d - Real.exp (-(d * c)) / d := by ring
  rw [e]
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {A P : E →L[ℝ] E}

/-- **Variation of constants on a segment.** A solution of `ẋ = A x + b(t)` on `[a, c]`
(one-sided derivatives at the ends) with `b` continuous satisfies
`x(c) = e^{(c−a)A} x(a) + ∫_a^c e^{(c−s)A} b(s) ds`. -/
@[tmio T, powerlib_foundation] theorem eq_expFlow_add_integral_of_Icc {x b : ℝ → E} {a c : ℝ}
    (hac : a ≤ c) (hx : ∀ t ∈ Icc a c, HasDerivWithinAt x (A (x t) + b t) (Icc a c) t)
    (hb : ContinuousOn b (Icc a c)) :
    x c = expFlow A (c - a) (x a) + ∫ s in a..c, expFlow A (c - s) (b s) := by
  set F : ℝ → E := fun s => expFlow A (-s) (x s) with hFdef
  have hF : ∀ s ∈ Icc a c, HasDerivWithinAt F (expFlow A (-s) (b s)) (Icc a c) s := by
    intro s hs
    have h1 : HasDerivAt (fun s => expFlow A (-s)) (-(expFlow A (-s) * A)) s := by
      have := (hasDerivAt_expFlow (A := A) (-s)).scomp s (hasDerivAt_neg s)
      rw [neg_one_smul] at this
      exact this
    refine (h1.hasDerivWithinAt.clm_apply (hx s hs)).congr_deriv ?_
    rw [map_add]
    change -(expFlow A (-s) (A (x s))) + (expFlow A (-s) (A (x s)) + expFlow A (-s) (b s)) = _
    abel
  have hcF : ContinuousOn F (Icc a c) := fun s hs => (hF s hs).continuousWithinAt
  have hcb : ContinuousOn (fun s => expFlow A (-s) (b s)) (Icc a c) :=
    (continuous_expFlow.comp continuous_neg).continuousOn.clm_apply hb
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hac hcF
    (fun s hs => (hF s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2))
    (hcb.intervalIntegrable_of_Icc hac)
  have hxc : x c = expFlow A c (F c) := (expFlow_apply_neg_apply c (x c)).symm
  have hFc : F c = F a + ∫ s in a..c, expFlow A (-s) (b s) := by rw [hint]; abel
  rw [hxc, hFc, map_add,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hcb.intervalIntegrable_of_Icc hac)]
  congr 1
  · show expFlow A c (expFlow A (-a) (x a)) = _
    rw [expFlow_apply_apply, ← sub_eq_add_neg]
  · congr 1
    funext s
    rw [expFlow_apply_apply, ← sub_eq_add_neg]

/-- **The stable component on a segment.** If `ż = A z + b` on `[a, c]`, `P z(c) = 0` and
`‖b(s)‖ ≤ B e^{−γs}` there (`γ < β`), then
`‖z(c)‖ ≤ K e^{−β(c−a)} ‖z(a)‖ + K B e^{−γc}/(β − γ)`. -/
@[tmio T, powerlib_foundation] theorem norm_le_of_segment_stable
    (hP : IsCommutingProjection A P) {K β γ : ℝ} (hγβ : γ < β)
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {a c : ℝ} (hac : a ≤ c) {z b : ℝ → E}
    (hz : ∀ t ∈ Icc a c, HasDerivWithinAt z (A (z t) + b t) (Icc a c) t)
    (hb : ContinuousOn b (Icc a c)) (hPz : P (z c) = 0) {B : ℝ}
    (hbB : ∀ s ∈ Icc a c, ‖b s‖ ≤ B * Real.exp (-(γ * s))) :
    ‖z c‖ ≤ K * Real.exp (-(β * (c - a))) * ‖z a‖ + K * B * Real.exp (-(γ * c)) / (β - γ) := by
  have hK := nonneg_of_stable_bound hst
  have hd : 0 < β - γ := sub_pos.2 hγβ
  have hB : 0 ≤ B := by
    have h1 := (norm_nonneg _).trans (hbB a ⟨le_rfl, hac⟩)
    have := Real.exp_pos (-(γ * a))
    nlinarith
  have hcb : ContinuousOn (fun s => expFlow A (c - s) (b s)) (Icc a c) :=
    (continuous_expFlow.comp (continuous_const.sub continuous_id)).continuousOn.clm_apply hb
  have hvoc := eq_expFlow_add_integral_of_Icc hac hz hb
  have hz' : z c = (1 - P) (z c) := by rw [compl_apply, hPz, sub_zero]
  rw [hz', hvoc, map_add, hP.compl_expFlow,
    ← (1 - P).intervalIntegral_comp_comm (hcb.intervalIntegrable_of_Icc hac)]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · calc ‖expFlow A (c - a) ((1 - P) (z a))‖ = ‖(expFlow A (c - a) * (1 - P)) (z a)‖ := rfl
      _ ≤ ‖expFlow A (c - a) * (1 - P)‖ * ‖z a‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * Real.exp (-(β * (c - a))) * ‖z a‖ := by
          gcongr; exact hst _ (sub_nonneg.2 hac)
  · set G : ℝ → ℝ := fun s => K * B * Real.exp (-(β * c)) * Real.exp ((β - γ) * s) with hG
    have hpt : ∀ s ∈ Ioc a c, ‖(1 - P) (expFlow A (c - s) (b s))‖ ≤ G s := by
      intro s hs
      have e : Real.exp (-(β * (c - s))) * Real.exp (-(γ * s)) =
          Real.exp (-(β * c)) * Real.exp ((β - γ) * s) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      calc ‖(1 - P) (expFlow A (c - s) (b s))‖ = ‖(expFlow A (c - s) * (1 - P)) (b s)‖ := by
            rw [hP.compl_expFlow]; rfl
        _ ≤ ‖expFlow A (c - s) * (1 - P)‖ * ‖b s‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ K * Real.exp (-(β * (c - s))) * (B * Real.exp (-(γ * s))) :=
            mul_le_mul (hst _ (sub_nonneg.2 hs.2)) (hbB s ⟨hs.1.le, hs.2⟩) (norm_nonneg _)
              (by positivity)
        _ = G s := by simp only [hG]; linear_combination (K * B) * e
    have hle := intervalIntegral.norm_integral_le_of_norm_le hac (ae_of_all volume hpt)
      ((by fun_prop : Continuous G).intervalIntegrable a c)
    refine hle.trans ?_
    simp only [hG]
    rw [intervalIntegral.integral_const_mul]
    have e2 : Real.exp (-(β * c)) * Real.exp ((β - γ) * c) = Real.exp (-(γ * c)) := by
      rw [← Real.exp_add]; ring_nf
    calc K * B * Real.exp (-(β * c)) * ∫ s in a..c, Real.exp ((β - γ) * s)
        ≤ K * B * Real.exp (-(β * c)) * (Real.exp ((β - γ) * c) / (β - γ)) := by
          gcongr; exact integral_exp_le hd a c
      _ = K * B * Real.exp (-(γ * c)) / (β - γ) := by rw [← e2]; ring

/-- **The centre component on a segment, backwards.** If `ẇ = A w + b` on `[t, 0]` (`t ≤ 0`)
with `P w(0) = w(0)`, `P b = b` and `‖b(s)‖ ≤ B e^{−ηs}` there (`ε < η`), then
`‖w(t)‖ ≤ K e^{−εt} ‖w(0)‖ + K B e^{−ηt}/(η − ε)`. -/
@[tmio T, powerlib_foundation] theorem norm_le_of_segment_center {K ε η : ℝ} (hεη : ε < η)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|)) {t : ℝ} (ht : t ≤ 0)
    {w b : ℝ → E} (hw : ∀ s ∈ Icc t 0, HasDerivWithinAt w (A (w s) + b s) (Icc t 0) s)
    (hb : ContinuousOn b (Icc t 0)) (hw0 : P (w 0) = w 0)
    (hbP : ∀ s ∈ Icc t 0, P (b s) = b s) {B : ℝ}
    (hbB : ∀ s ∈ Icc t 0, ‖b s‖ ≤ B * Real.exp (-(η * s))) :
    ‖w t‖ ≤ K * Real.exp (-(ε * t)) * ‖w 0‖ + K * B * Real.exp (-(η * t)) / (η - ε) := by
  have hK : 0 ≤ K := by have := (norm_nonneg _).trans (hcen 0); simpa using this
  have hd : 0 < η - ε := sub_pos.2 hεη
  have hB : 0 ≤ B := by
    have h1 := (norm_nonneg _).trans (hbB t ⟨le_rfl, ht⟩)
    have := Real.exp_pos (-(η * t))
    nlinarith
  have hcb : ContinuousOn (fun s => expFlow A (0 - s) (b s)) (Icc t 0) :=
    (continuous_expFlow.comp (continuous_const.sub continuous_id)).continuousOn.clm_apply hb
  have hvoc := eq_expFlow_add_integral_of_Icc ht hw hb
  have hwt : w t = expFlow A t (w 0) - ∫ s in t..0, expFlow A (t - s) (b s) := by
    have h1 : expFlow A t (w 0) = w t + ∫ s in t..0, expFlow A (t - s) (b s) := by
      rw [hvoc, map_add,
        ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hcb.intervalIntegrable_of_Icc ht),
        expFlow_apply_apply, zero_sub, add_neg_cancel, expFlow_zero]
      congr 1
      congr 1
      funext s
      rw [expFlow_apply_apply, zero_sub, ← sub_eq_add_neg]
    rw [h1, add_sub_cancel_right]
  rw [hwt]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · calc ‖expFlow A t (w 0)‖ = ‖(expFlow A t * P) (w 0)‖ := by
          rw [show (expFlow A t * P) (w 0) = expFlow A t (P (w 0)) from rfl, hw0]
      _ ≤ ‖expFlow A t * P‖ * ‖w 0‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * Real.exp (ε * |t|) * ‖w 0‖ := by gcongr; exact hcen t
      _ = K * Real.exp (-(ε * t)) * ‖w 0‖ := by rw [abs_of_nonpos ht, mul_neg]
  · set G : ℝ → ℝ := fun s => K * B * Real.exp (-(ε * t)) * Real.exp (-((η - ε) * s)) with hG
    have hpt : ∀ s ∈ Ioc t 0, ‖expFlow A (t - s) (b s)‖ ≤ G s := by
      intro s hs
      have e : Real.exp (ε * |t - s|) * Real.exp (-(η * s)) =
          Real.exp (-(ε * t)) * Real.exp (-((η - ε) * s)) := by
        rw [abs_of_nonpos (by linarith [hs.1]), ← Real.exp_add, ← Real.exp_add]; ring_nf
      calc ‖expFlow A (t - s) (b s)‖ = ‖(expFlow A (t - s) * P) (b s)‖ := by
            rw [show (expFlow A (t - s) * P) (b s) = expFlow A (t - s) (P (b s)) from rfl,
              hbP s ⟨hs.1.le, hs.2⟩]
        _ ≤ ‖expFlow A (t - s) * P‖ * ‖b s‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ K * Real.exp (ε * |t - s|) * (B * Real.exp (-(η * s))) :=
            mul_le_mul (hcen _) (hbB s ⟨hs.1.le, hs.2⟩) (norm_nonneg _) (by positivity)
        _ = G s := by simp only [hG]; linear_combination (K * B) * e
    have hle := intervalIntegral.norm_integral_le_of_norm_le ht (ae_of_all volume hpt)
      ((by fun_prop : Continuous G).intervalIntegrable t 0)
    refine hle.trans ?_
    simp only [hG]
    rw [intervalIntegral.integral_const_mul]
    have e2 : Real.exp (-(ε * t)) * Real.exp (-((η - ε) * t)) = Real.exp (-(η * t)) := by
      rw [← Real.exp_add]; ring_nf
    calc K * B * Real.exp (-(ε * t)) * ∫ s in t..0, Real.exp (-((η - ε) * s))
        ≤ K * B * Real.exp (-(ε * t)) * (Real.exp (-((η - ε) * t)) / (η - ε)) := by
          gcongr; exact integral_exp_neg_le hd t 0
      _ = K * B * Real.exp (-(η * t)) / (η - ε) := by rw [← e2]; ring

/-- **Backward growth on the centre subspace.** If `ẇ = A w + b` on `[a, 0]` with
`P w(0) = w(0)`, `P b = b` and `‖b‖ ≤ c ‖w‖` there, and `K c/(η − ε) < 1` (`ε < η`, `0 ≤ η`),
then `‖w(t)‖ ≤ K ‖w(0)‖/(1 − K c/(η − ε)) e^{−ηt}` on `[a, 0]` (a contraction in the weight
`e^{η|t|}`). -/
@[tmio T, powerlib_foundation] theorem norm_le_of_segment_centerBound {K ε η c : ℝ}
    (hη : 0 ≤ η) (hεη : ε < η) (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    {a : ℝ} {w b : ℝ → E}
    (hw : ∀ t ∈ Icc a 0, HasDerivWithinAt w (A (w t) + b t) (Icc a 0) t)
    (hb : ContinuousOn b (Icc a 0)) (hw0 : P (w 0) = w 0) (hbP : ∀ t ∈ Icc a 0, P (b t) = b t)
    (hc : 0 ≤ c) (hbw : ∀ t ∈ Icc a 0, ‖b t‖ ≤ c * ‖w t‖) (hk : K * c / (η - ε) < 1) :
    ∀ t ∈ Icc a 0, ‖w t‖ ≤ K * ‖w 0‖ / (1 - K * c / (η - ε)) * Real.exp (-(η * t)) := by
  have hK : 0 ≤ K := by have := (norm_nonneg _).trans (hcen 0); simpa using this
  have hd : 0 < η - ε := sub_pos.2 hεη
  have hwc : ContinuousOn w (Icc a 0) := fun t ht => (hw t ht).continuousWithinAt
  obtain ⟨Cb, hCb⟩ := isCompact_Icc.exists_bound_of_continuousOn hwc
  have h0 : ∀ i : Icc a 0, ‖w i‖ ≤ max Cb 0 * Real.exp (-(η * i)) := fun ⟨t, ht⟩ => by
    have h1 : 1 ≤ Real.exp (-(η * t)) := Real.one_le_exp (by nlinarith [ht.2])
    change ‖w t‖ ≤ _
    calc ‖w t‖ ≤ max Cb 0 := (hCb t ht).trans (le_max_left _ _)
      _ = max Cb 0 * 1 := (mul_one _).symm
      _ ≤ _ := by gcongr
  have hstep : ∀ Z, (∀ i : Icc a 0, ‖w i‖ ≤ Z * Real.exp (-(η * i))) →
      ∀ i : Icc a 0, ‖w i‖ ≤ (K * c / (η - ε) * Z + K * ‖w 0‖) * Real.exp (-(η * i)) := by
    intro Z hZ ⟨t, ht⟩
    have hsub : Icc t 0 ⊆ Icc a 0 := Icc_subset_Icc ht.1 le_rfl
    have h1 := norm_le_of_segment_center hεη hcen ht.2 (w := w) (b := b)
      (fun s hs => (hw s (hsub hs)).mono hsub) (hb.mono hsub) hw0 (fun s hs => hbP s (hsub hs))
      (B := c * Z) (fun s hs => by
        calc ‖b s‖ ≤ c * ‖w s‖ := hbw s (hsub hs)
          _ ≤ c * (Z * Real.exp (-(η * s))) := by gcongr; exact hZ ⟨s, hsub hs⟩
          _ = c * Z * Real.exp (-(η * s)) := by ring)
    have he : Real.exp (-(ε * t)) ≤ Real.exp (-(η * t)) :=
      Real.exp_le_exp.2 (by nlinarith [ht.2])
    change ‖w t‖ ≤ _
    calc ‖w t‖ ≤ K * Real.exp (-(ε * t)) * ‖w 0‖ +
          K * (c * Z) * Real.exp (-(η * t)) / (η - ε) := h1
      _ ≤ K * Real.exp (-(η * t)) * ‖w 0‖ + K * (c * Z) * Real.exp (-(η * t)) / (η - ε) := by
          gcongr
      _ = _ := by ring
  have hk0 : 0 ≤ K * c / (η - ε) := by positivity
  intro t ht
  exact le_of_contract hk0 hk h0 hstep ⟨t, ht⟩

/-- **Carr's estimate on a segment.** Let `x` solve `ẋ = A x + g(x)` on `[a, 0]` (`g`
`δ`-Lipschitz) with `‖P x(t)‖ ≤ V e^{−ηt}`, and `ψ` a `C¹` map into `ker P` with `‖Dψ‖ ≤ 1` whose
invariance defect for `g` is at most `M ‖v‖^q` on `range P` (`q ≥ 1`, `qη < β`,
`K (‖1 − P‖ + ‖P‖) δ/(β − qη) < 1`). If the deviation `z = (1 − P)x − ψ(P x)` is at most `B` at
`t = a`, then `‖z(0)‖ ≤ (K B e^{qηa} + K M V^q/(β − qη))/(1 − K(‖1 − P‖ + ‖P‖)δ/(β − qη))`:
`ż = A z + b` with `‖b‖ ≤ M ‖P x‖^q + (‖1 − P‖ + ‖P‖) δ ‖z‖`, and the stable representation of `z`
on `[a, 0]` contracts in the weight `e^{−qηt}`. -/
@[tmio T, powerlib_foundation] theorem norm_sub_cutoff_le_of_segment
    (hP : IsCommutingProjection A P) {K β η q : ℝ} (hη : 0 ≤ η) (hq : 1 ≤ q) (hqη : q * η < β)
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {g ψ : E → E} {δ : NNReal} (hg : LipschitzWith δ g) (hψ : ContDiff ℝ 1 ψ)
    (hψd : ∀ x, ‖fderiv ℝ ψ x‖ ≤ 1) (hψP : ∀ x, P (ψ x) = 0) {M : ℝ} (hM : 0 ≤ M)
    (hdef : ∀ v, P v = v → ‖invarianceDefect A P g ψ v‖ ≤ M * ‖v‖ ^ q)
    (hsmall : K * ((‖1 - P‖ + ‖P‖) * δ) / (β - q * η) < 1) {a : ℝ} (ha : a ≤ 0)
    {x : ℝ → E} (hx : ∀ t ∈ Icc a 0, HasDerivWithinAt x (A (x t) + g (x t)) (Icc a 0) t)
    {V B : ℝ} (hV : 0 ≤ V) (hvb : ∀ t ∈ Icc a 0, ‖P (x t)‖ ≤ V * Real.exp (-(η * t)))
    (hB : ‖(1 - P) (x a) - ψ (P (x a))‖ ≤ B) :
    ‖(1 - P) (x 0) - ψ (P (x 0))‖ ≤
      (K * B * Real.exp (q * η * a) + K * M * V ^ q / (β - q * η)) /
        (1 - K * ((‖1 - P‖ + ‖P‖) * δ) / (β - q * η)) := by
  have hK := nonneg_of_stable_bound hst
  have hβq : 0 < β - q * η := sub_pos.2 hqη
  have hq0 : 0 ≤ q := by linarith
  have hqη0 : 0 ≤ q * η := mul_nonneg hq0 hη
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  set κ' : ℝ := (‖1 - P‖ + ‖P‖) * δ with hκ'
  have hκ'0 : 0 ≤ κ' := by positivity
  set k := K * κ' / (β - q * η) with hk
  have hk0 : 0 ≤ k := by positivity
  set v : ℝ → E := fun t => P (x t) with hv
  set z : ℝ → E := fun t => (1 - P) (x t) - ψ (v t) with hz
  -- `ż = A z + b` with `‖b‖ ≤ M ‖v‖^q + κ' ‖z‖` (`exists_forcing_graphDeviation`)
  obtain ⟨b, hbc, hzd, hbb'⟩ := exists_forcing_graphDeviation hP hg hψ hψd hψP hdef hx
  have hbb : ∀ t, ‖b t‖ ≤ M * ‖v t‖ ^ q + κ' * ‖z t‖ := hbb'
  have hPz : ∀ t, P (z t) = 0 := fun t => by
    simp only [hz, map_sub, hP.proj_compl, hψP, sub_zero]
  have hvq : ∀ t ∈ Icc a 0, ‖v t‖ ^ q ≤ V ^ q * Real.exp (-(q * η * t)) := fun t ht => by
    refine (Real.rpow_le_rpow (norm_nonneg _) (hvb t ht) hq0).trans_eq ?_
    rw [Real.mul_rpow hV (Real.exp_pos _).le, ← Real.exp_mul]
    ring_nf
  -- an initial bound on the compact segment
  have hzc : ContinuousOn z (Icc a 0) := fun t ht => (hzd t ht).continuousWithinAt
  obtain ⟨Cb, hCb⟩ := isCompact_Icc.exists_bound_of_continuousOn hzc
  have h0 : ∀ i : Icc a 0, ‖z i‖ ≤ max Cb 0 * Real.exp (-(q * η * i)) := fun ⟨t, ht⟩ => by
    have h1 : 1 ≤ Real.exp (-(q * η * t)) := Real.one_le_exp (by nlinarith [ht.2])
    change ‖z t‖ ≤ _
    calc ‖z t‖ ≤ max Cb 0 := (hCb t ht).trans (le_max_left _ _)
      _ = max Cb 0 * 1 := (mul_one _).symm
      _ ≤ _ := by gcongr
  -- the boundary term
  have hbd : ∀ t ∈ Icc a 0, K * Real.exp (-(β * (t - a))) * ‖z a‖ ≤
      K * B * Real.exp (q * η * a) * Real.exp (-(q * η * t)) := fun t ht => by
    have h1 : Real.exp (-(β * (t - a))) ≤ Real.exp (-(q * η * (t - a))) :=
      Real.exp_le_exp.2 (by nlinarith [ht.1])
    have e : Real.exp (-(q * η * (t - a))) = Real.exp (q * η * a) * Real.exp (-(q * η * t)) := by
      rw [← Real.exp_add]; ring_nf
    calc K * Real.exp (-(β * (t - a))) * ‖z a‖ ≤ K * Real.exp (-(q * η * (t - a))) * B := by
          gcongr
      _ = _ := by rw [e]; ring
  -- the contraction step
  have hstep : ∀ Z, (∀ i : Icc a 0, ‖z i‖ ≤ Z * Real.exp (-(q * η * i))) →
      ∀ i : Icc a 0, ‖z i‖ ≤ (k * Z + (K * B * Real.exp (q * η * a) +
        K * M * V ^ q / (β - q * η))) * Real.exp (-(q * η * i)) := by
    intro Z hZ ⟨t, ht⟩
    have hsub : Icc a t ⊆ Icc a 0 := Icc_subset_Icc le_rfl ht.2
    have hbs : ∀ s ∈ Icc a t, ‖b s‖ ≤ (M * V ^ q + κ' * Z) * Real.exp (-(q * η * s)) :=
      fun s hs => by
        calc ‖b s‖ ≤ M * ‖v s‖ ^ q + κ' * ‖z s‖ := hbb s
          _ ≤ M * (V ^ q * Real.exp (-(q * η * s))) + κ' * (Z * Real.exp (-(q * η * s))) := by
              gcongr
              · exact hvq s (hsub hs)
              · exact hZ ⟨s, hsub hs⟩
          _ = _ := by ring
    have h1 := norm_le_of_segment_stable hP hqη hst ht.1 (z := z) (b := b)
      (fun s hs => (hzd s (hsub hs)).mono hsub) (hbc.mono hsub) (hPz t) hbs
    change ‖z t‖ ≤ _
    calc ‖z t‖ ≤ K * Real.exp (-(β * (t - a))) * ‖z a‖ +
          K * (M * V ^ q + κ' * Z) * Real.exp (-(q * η * t)) / (β - q * η) := h1
      _ ≤ K * B * Real.exp (q * η * a) * Real.exp (-(q * η * t)) +
          K * (M * V ^ q + κ' * Z) * Real.exp (-(q * η * t)) / (β - q * η) :=
          add_le_add_left (hbd t ht) _
      _ = _ := by rw [hk]; ring
  have hfin := le_of_contract hk0 hsmall h0 hstep ⟨0, ⟨ha, le_rfl⟩⟩
  change ‖z 0‖ ≤ _ at hfin
  rw [mul_zero, neg_zero, Real.exp_zero, mul_one] at hfin
  exact hfin

end Segment

/-! ## Backward solutions on a locally invariant graph and the theorem -/

section State

variable {n : ℕ} {A P : State n →L[ℝ] State n} {f h : State n → State n}

/-- A globally Lipschitz field on `ℝⁿ` has a solution on `(−∞, 0]` through every point at
time `0` (forward completeness of the reversed field). -/
@[tmio T, powerlib_foundation] theorem exists_isIntegralCurveOn_Iic {F : State n → State n}
    {L : NNReal} (hF : LipschitzWith L F) (x₀ : State n) :
    ∃ w : ℝ → State n, w 0 = x₀ ∧ IsIntegralCurveOn w (fun _ y => F y) (Iic 0) := by
  obtain ⟨W, hW0, hW⟩ := Flow.forwardComplete_of_lipschitzWith hF.neg 0 x₀
  refine ⟨fun t => W (-t), by simpa using hW0, fun t ht => ?_⟩
  have ht' : -t ∈ Ici (0 : ℝ) := by simpa using ht
  have h1 := (hW (-t) ht').scomp t (hasDerivAt_neg t).hasDerivWithinAt
    (show MapsTo (fun s : ℝ => -s) (Iic 0) (Ici 0) from fun s hs => by
      simp only [mem_Iic, mem_Ici] at hs ⊢; linarith)
  have e : (-1 : ℝ) • (-F) (W (-t)) = F (W (-t)) := by simp
  rw [e] at h1
  exact h1

/-- **Lifting with cutoffs.** Let the graph of `h` be locally invariant for `ẋ = A x + f(x)` in
the ball of radius `ρ`, `g` a globally Lipschitz field equal to `f` on the ball of radius `r`, and
`h'` a Lipschitz graph map equal to `h` where `‖P x‖ ≤ r`. Then, for `R ≤ ρ`, `R ≤ r`,
`‖P‖ R ≤ r`, every solution `w` of the reduced cutoff field `u̇ = PAu + Pg(u + h' u)` on `[a, b]`
with `w(a) ∈ range P` whose lift stays in the ball of radius `R/2` lifts to the solution
`w + h'(w)` of `ẋ = A x + g(x)` on `[a, b]`. -/
@[tmio T, powerlib_foundation] theorem isIntegralCurveOn_lift_of_cutoff
    (hP : IsCommutingProjection A P) (hh : IsGraphMap P h) {ρ : ℝ}
    (hinv : ∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
      φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h)
    {g : State n → State n} {δ : NNReal} (hg : LipschitzWith δ g) {r : ℝ}
    (hgf : ∀ y, ‖y‖ ≤ r → g y = f y) {h' : State n → State n} {L : NNReal}
    (hh' : IsGraphMap P h') (hL : LipschitzWith L h') (hh'h : ∀ x, ‖P x‖ ≤ r → h' x = h x)
    {R : ℝ} (hR : 0 < R) (hRρ : R ≤ ρ) (hRr : R ≤ r) (hPR : ‖P‖ * R ≤ r) {a b : ℝ}
    {w : ℝ → State n} (hw : IsIntegralCurveOn w (fun _ y => reducedField A P g h' y) (Icc a b))
    (hwa : P (w a) = w a) (hsmall : ∀ t ∈ Icc a b, ‖w t + h' (w t)‖ ≤ R / 2) :
    IsIntegralCurveOn (fun t => w t + h' (w t)) (fun _ y => A y + g y) (Icc a b) := by
  rcases lt_or_ge b a with hlt | hle
  · intro t ht
    exact absurd (ht.1.trans ht.2) (not_le.mpr hlt)
  have hRl : LipschitzWith (‖P‖₊ * ‖A‖₊ + ‖P‖₊ * (δ * (1 + L))) (reducedField A P g h') := by
    have h1 : LipschitzWith (‖P‖₊ * ‖A‖₊) (fun y => P (A y)) := P.lipschitzWith.comp A.lipschitzWith
    have h2 : LipschitzWith (‖P‖₊ * (δ * (1 + L))) (fun y => P (g (y + h' y))) :=
      P.lipschitzWith.comp (hg.comp (LipschitzWith.id.add hL))
    exact h1.add h2
  have hGl : LipschitzWith (‖A‖₊ + δ) (fullField A g) := A.lipschitzWith.add hg
  -- in the ball of radius `R` the two graphs coincide
  have hPx : ∀ x : State n, ‖x‖ ≤ R → ‖P x‖ ≤ r := fun x hx =>
    (P.le_opNorm x).trans ((mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans hPR)
  have hgraph : ∀ x : State n, ‖x‖ ≤ R → (x ∈ graph P h ↔ x ∈ graph P h') := fun x hx => by
    have e : h x = h' x := by
      rw [← hh.comp_proj, ← hh'.comp_proj, hh'h _ (by rw [hP.idem]; exact hPx x hx)]
    show x = P x + h x ↔ x = P x + h' x
    rw [e]
  obtain ⟨φ, hφ0, hφ⟩ := Flow.forwardComplete_of_lipschitzWith hGl a (w a + h' (w a))
  have hkey : ∀ s, s ≤ b → (∀ τ ∈ Icc a s, ‖φ τ‖ < R) → ∀ τ ∈ Icc a s, φ τ = w τ + h' (w τ) := by
    intro s hs hin
    have htraj : IsTrajectoryOn φ (fullField A f) a s :=
      isIntegralCurveOn_of_eq_on_curve (hφ.mono Icc_subset_Ici_self) fun τ hτ => by
        show A (φ τ) + g (φ τ) = A (φ τ) + f (φ τ)
        rw [hgf _ ((hin τ hτ).le.trans hRr)]
    have hφa : φ a ∈ graph P h := by
      rw [hφ0]
      exact (hgraph _ (by linarith [hsmall a ⟨le_rfl, hle⟩])).2 (hh'.lift_mem_graph hwa)
    have hgr := hinv a s φ htraj hφa fun τ hτ => (hin τ hτ).trans_le hRρ
    have hgr' : ∀ τ ∈ Icc a s, φ τ ∈ graph P h' := fun τ hτ =>
      (hgraph _ (hin τ hτ).le).1 (hgr τ hτ)
    have hv : IsIntegralCurveOn (fun τ => P (φ τ)) (fun _ y => reducedField A P g h' y)
        (Icc a s) := by
      intro τ hτ
      have := P.hasFDerivAt.comp_hasDerivWithinAt τ
        ((hφ τ hτ.1).mono (Icc_subset_Ici_self : Icc a s ⊆ Ici a))
      simpa only [Function.comp_def, proj_fullField_of_mem_graph hP hh' (hgr' τ hτ)] using this
    have heq := eqOn_of_isIntegralCurveOn_Icc (fun _ => hRl)
      (hw.mono (Icc_subset_Icc le_rfl hs)) hv (by rw [hφ0, hh'.proj_lift hwa])
    intro τ hτ
    rw [heq hτ]
    exact hh'.eq_lift_of_mem_graph (hgr' τ hτ)
  have h0 : ‖φ a - 0‖ < R := by
    rw [sub_zero, hφ0]; linarith [hsmall a ⟨le_rfl, hle⟩]
  have hstay : ∀ t ∈ Icc a b, ‖φ t - 0‖ < R := by
    refine forall_norm_sub_lt_of_bootstrap ((hφ.mono Icc_subset_Ici_self).continuousOn) h0
      fun s hs hin => ?_
    have hin' : ∀ τ ∈ Icc a s, ‖φ τ‖ < R := fun τ hτ => by simpa using hin τ hτ
    rw [sub_zero, hkey s hs.2 hin' s ⟨hs.1, le_rfl⟩]
    exact hsmall s hs
  have hstay' : ∀ τ ∈ Icc a b, ‖φ τ‖ < R := fun τ hτ => by simpa using hstay τ hτ
  have hfin := hkey b le_rfl hstay'
  intro t ht
  have hd := (hφ t ht.1).mono (Icc_subset_Ici_self : Icc a b ⊆ Ici a)
  rw [hfin t ht] at hd
  exact hd.congr_of_mem (fun τ hτ => (hfin τ hτ).symm) ht

/-- **Carr's approximation theorem for any tangent centre manifold** (Carr, Theorem 3, for every
centre manifold). Under the centre–stable dichotomy `‖e^{tA}P‖ ≤ K e^{ε|t|}`,
`‖e^{tA}(1 − P)‖ ≤ K e^{−βt}` (`t ≥ 0`) with `qε < β` (`q ≥ 1`), let `f(0) = 0` with strict
derivative `0` at `0`, and let `h` be any graph map over `range P` with strict derivative `0` at
`0` whose graph is locally invariant in the ball of radius `ρ` (neither the construction nor
uniqueness of `h` is used). Every candidate `φ`, `C¹` near `0`, `φ(0) = 0`, `Dφ(0) = 0`, values
in `ker P`, with invariance defect `O(‖u‖^q)` on `range P` satisfies `h(u) − φ(u) = O(‖u‖^q)` on
`range P`. -/
@[tmio T, powerlib_foundation] theorem isOrder_sub_of_invariantGraph
    (hP : IsCommutingProjection A P) {K ε β q : ℝ} (hε : 0 ≤ ε) (hq : 1 ≤ q)
    (hqε : q * ε < β) (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    (hf0 : f 0 = 0) (hf : HasStrictFDerivAt f (0 : State n →L[ℝ] State n) 0)
    (hh : IsGraphMap P h) (hhs : HasStrictFDerivAt h (0 : State n →L[ℝ] State n) 0)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hinv : ∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
      φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h)
    {φ : State n → State n} (hφ : ContDiffAt ℝ 1 φ 0) (hφ0 : φ 0 = 0)
    (hDφ : fderiv ℝ φ 0 = 0) (hφP : ∀ x, P (φ x) = 0)
    (hdef : IsOrder P (invarianceDefect A P f φ) q) :
    IsOrder P (fun u => h u - φ u) q := by
  have hK := nonneg_of_stable_bound hst
  have hq0 : 0 < q := by linarith
  have hβ : 0 < β := lt_of_le_of_lt (mul_nonneg hq0.le hε) hqε
  -- the weight: `ε < η`, `qη < β`
  set η := (ε + β / q) / 2 with hηdef
  have hεβq : ε < β / q := by rw [lt_div_iff₀ hq0]; linarith
  have hεη : ε < η := by rw [hηdef]; linarith
  have hηβq : η < β / q := by rw [hηdef]; linarith
  have hqη : q * η < β := by have := (lt_div_iff₀ hq0).1 hηβq; linarith
  have hη : 0 < η := lt_of_le_of_lt hε hεη
  have hβq : 0 < β - q * η := sub_pos.2 hqη
  have hd : 0 < η - ε := sub_pos.2 hεη
  -- a globally Lipschitz graph map equal to `h` near `0`
  obtain ⟨rh, hrh, h', L, hh', hL, hh'h⟩ := exists_lipschitz_graphMap_cutoff hP hh hhs
  -- the Lipschitz bound `δ` of the cutoff of `f`, small for both contractions
  set D₁ := K * (‖P‖ * (1 + L)) / (η - ε) with hD₁
  set D₂ := K * (‖1 - P‖ + ‖P‖) / (β - q * η) with hD₂
  have hD₁0 : 0 ≤ D₁ := by positivity
  have hD₂0 : 0 ≤ D₂ := by positivity
  set δ : ℝ := 1 / (2 * (D₁ + D₂ + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hδD : δ * (D₁ + D₂) < 1 := by
    rw [hδdef, show 1 / (2 * (D₁ + D₂ + 1)) * (D₁ + D₂) = (D₁ + D₂) / (2 * (D₁ + D₂ + 1)) by
      ring, div_lt_one (by positivity)]
    linarith
  obtain ⟨rf, hrf, g, hg, hg0, hgf, -⟩ := exists_small_lipschitz_cutoff hf0 hf hδ
  have hδ' : ((Real.toNNReal δ : NNReal) : ℝ) = δ := Real.coe_toNNReal _ hδ.le
  set k₁ := K * (‖P‖ * (δ * (1 + L))) / (η - ε) with hk₁def
  have hk₁ : k₁ < 1 := by
    have : k₁ = δ * D₁ := by rw [hk₁def, hD₁]; ring
    have e : δ * (D₁ + D₂) = δ * D₁ + δ * D₂ := mul_add _ _ _
    rw [this]; linarith [mul_nonneg hδ.le hD₂0]
  have hk₂ : K * ((‖1 - P‖ + ‖P‖) * (Real.toNNReal δ : ℝ)) / (β - q * η) < 1 := by
    have : K * ((‖1 - P‖ + ‖P‖) * (Real.toNNReal δ : ℝ)) / (β - q * η) = δ * D₂ := by
      rw [hδ', hD₂]; ring
    have e : δ * (D₁ + D₂) = δ * D₁ + δ * D₂ := mul_add _ _ _
    rw [this]; linarith [mul_nonneg hδ.le hD₁0]
  -- the cutoff of the candidate and its global defect bound
  obtain ⟨rψ, hrψ, ψ, hψ, hψ0, hψd, hψP, hψφ⟩ := exists_contDiff_cutoff hφ hφ0 hDφ hφP
  have hψn : ∀ x, ‖ψ x‖ ≤ ‖x‖ := fun x => by
    have := convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hψ.differentiable one_ne_zero y) (fun y _ => hψd y) (mem_univ 0) (mem_univ x)
    simpa [hψ0] using this
  obtain ⟨M, hM, hMb⟩ :=
    exists_defect_bound (A := A) (P := P) hq hrf hrψ hg hgf hg0 hψd hψn hψφ hdef
  -- radii
  set r := min rf rh with hrdef
  have hr : 0 < r := lt_min hrf hrh
  have hgf' : ∀ y, ‖y‖ ≤ r → g y = f y := fun y hy => hgf y (hy.trans (min_le_left _ _))
  have hh'h' : ∀ x, ‖P x‖ ≤ r → h' x = h x := fun x hx => hh'h x (hx.trans (min_le_right _ _))
  set R := min ρ r / (‖P‖ + 1) with hRdef
  have hR : 0 < R := div_pos (lt_min hρ hr) (by positivity)
  have hRm : R ≤ min ρ r := div_le_self (lt_min hρ hr).le (by linarith [norm_nonneg P])
  have hRρ : R ≤ ρ := hRm.trans (min_le_left _ _)
  have hRr : R ≤ r := hRm.trans (min_le_right _ _)
  have hPR : ‖P‖ * R ≤ r := by
    have h1 : ‖P‖ * R ≤ (‖P‖ + 1) * R := by
      have e : (‖P‖ + 1) * R = ‖P‖ * R + R := by ring
      linarith
    have h2 : (‖P‖ + 1) * R = min ρ r := by rw [hRdef]; field_simp
    linarith [min_le_right ρ r]
  have hk₁1 : 0 < 1 - k₁ := sub_pos.2 hk₁
  set Cw := K / (1 - k₁) with hCwdef
  have hCw : 0 ≤ Cw := by positivity
  set c₀ := R / (2 * ((1 + L) * Cw + 1)) with hc₀def
  have hc₀ : 0 < c₀ := by positivity
  have hc₀R : (1 + L) * Cw * c₀ ≤ R / 2 := by
    have e : c₀ * (2 * ((1 + L) * Cw + 1)) = R := by rw [hc₀def]; field_simp
    have e2 : (1 + L) * Cw * c₀ = R / 2 - c₀ := by linear_combination e / 2
    linarith
  set k₂ := K * ((‖1 - P‖ + ‖P‖) * (Real.toNNReal δ : ℝ)) / (β - q * η) with hk₂def
  set Cfin := (K * ((1 + L) * Cw * c₀) / c₀ ^ q + K * M * Cw ^ q / (β - q * η)) / (1 - k₂)
    with hCfin
  -- the estimate on `range P` near `0`
  have key : ∀ u : State n, P u = u → ‖u‖ ≤ c₀ → ‖h' u - ψ u‖ ≤ Cfin * ‖u‖ ^ q := by
    intro u hu hu0
    rcases (norm_nonneg u).eq_or_lt with h0 | hpos
    · have hu00 : u = 0 := norm_eq_zero.1 h0.symm
      subst hu00
      rw [hh'.map_zero, hψ0, sub_zero, norm_zero, Real.zero_rpow hq0.ne', mul_zero]
    have hu' : ‖u‖ ≠ 0 := hpos.ne'
    -- the horizon `a = −T` with `‖u‖ e^{ηT} = c₀`
    set a := Real.log (‖u‖ / c₀) / η with hadef
    have hla : Real.log (‖u‖ / c₀) = η * a := by rw [hadef]; field_simp
    have hea : Real.exp (η * a) = ‖u‖ / c₀ := by
      rw [← hla, Real.exp_log (div_pos hpos hc₀)]
    have ha : a ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (Real.log_nonpos (div_pos hpos hc₀).le ((div_le_one hc₀).2 hu0)) hη.le
    -- the backward solution of the reduced cutoff field through `u`
    have hRl : LipschitzWith (‖P‖₊ * ‖A‖₊ + ‖P‖₊ * (Real.toNNReal δ * (1 + L)))
        (reducedField A P g h') := by
      have h1 : LipschitzWith (‖P‖₊ * ‖A‖₊) (fun y => P (A y)) :=
        P.lipschitzWith.comp A.lipschitzWith
      have h2 : LipschitzWith (‖P‖₊ * (Real.toNNReal δ * (1 + L)))
          (fun y => P (g (y + h' y))) :=
        P.lipschitzWith.comp (hg.comp (LipschitzWith.id.add hL))
      exact h1.add h2
    obtain ⟨W, hW0, hW⟩ := exists_isIntegralCurveOn_Iic (hRl.comp P.lipschitzWith) u
    set w : ℝ → State n := fun t => P (W t) with hwdef
    have hwP : ∀ t, P (w t) = w t := fun t => hP.idem _
    have hw0 : w 0 = u := by simp only [hwdef, hW0, hu]
    have hwI : IsIntegralCurveOn w (fun _ y => reducedField A P g h' y) (Iic 0) := fun t ht => by
      have h1 := P.hasFDerivAt.comp_hasDerivWithinAt t (hW t ht)
      have e : P (reducedField A P g h' (P (W t))) = reducedField A P g h' (w t) := by
        simp only [reducedField, map_add, hP.idem, hwdef]
      exact h1.congr_deriv e
    -- `ẇ = A w + P g(w + h' w)` and the backward growth `‖w(t)‖ ≤ C_w ‖u‖ e^{−ηt}`
    set bw : ℝ → State n := fun t => P (g (w t + h' (w t))) with hbwdef
    have hwd : ∀ t ∈ Icc a 0, HasDerivWithinAt w (A (w t) + bw t) (Icc a 0) t := fun t ht => by
      have h1 := (hwI t ht.2).mono (Icc_subset_Iic_self : Icc a 0 ⊆ Iic 0)
      have e : reducedField A P g h' (w t) = A (w t) + bw t := by
        simp only [reducedField, hbwdef]
        rw [← hP.comm, hwP]
      exact h1.congr_deriv e
    have hwc : ContinuousOn w (Icc a 0) := fun t ht => (hwd t ht).continuousWithinAt
    have hbwc : ContinuousOn bw (Icc a 0) :=
      P.continuous.comp_continuousOn (hg.continuous.comp_continuousOn
        (hwc.add (hL.continuous.comp_continuousOn hwc)))
    have hbwb : ∀ t ∈ Icc a 0, ‖bw t‖ ≤ ‖P‖ * (δ * (1 + L)) * ‖w t‖ := fun t _ => by
      have hgw : ‖g (w t + h' (w t))‖ ≤ δ * ((1 + L) * ‖w t‖) := by
        have := hg.norm_le_mul hg0 (w t + h' (w t))
        rw [hδ'] at this
        exact this.trans (mul_le_mul_of_nonneg_left (hh'.norm_lift_le hL (w t)) hδ.le)
      calc ‖bw t‖ ≤ ‖P‖ * ‖g (w t + h' (w t))‖ := P.le_opNorm _
        _ ≤ ‖P‖ * (δ * ((1 + L) * ‖w t‖)) := by gcongr
        _ = _ := by ring
    have hwb : ∀ t ∈ Icc a 0, ‖w t‖ ≤ K * ‖w 0‖ / (1 - k₁) * Real.exp (-(η * t)) :=
      norm_le_of_segment_centerBound hη.le hεη hcen hwd hbwc (hwP 0) (fun t _ => hP.idem _)
        (by positivity) hbwb hk₁
    have hwb' : ∀ t ∈ Icc a 0, ‖w t‖ ≤ Cw * (‖u‖ * Real.exp (-(η * t))) := fun t ht =>
      (hwb t ht).trans_eq (by rw [hw0, hCwdef]; ring)
    have hexp : ∀ t ∈ Icc a 0, ‖u‖ * Real.exp (-(η * t)) ≤ c₀ := fun t ht => by
      have h1 : Real.exp (-(η * t)) ≤ Real.exp (-(η * a)) :=
        Real.exp_le_exp.2 (by linarith [mul_le_mul_of_nonneg_left ht.1 hη.le])
      have h2 : ‖u‖ * Real.exp (-(η * a)) = c₀ := by
        rw [Real.exp_neg, hea, inv_div]; field_simp
      calc ‖u‖ * Real.exp (-(η * t)) ≤ ‖u‖ * Real.exp (-(η * a)) := by gcongr
        _ = c₀ := h2
    have hwc₀ : ∀ t ∈ Icc a 0, ‖w t‖ ≤ Cw * c₀ := fun t ht =>
      (hwb' t ht).trans (mul_le_mul_of_nonneg_left (hexp t ht) hCw)
    have hwsmall : ∀ t ∈ Icc a 0, ‖w t + h' (w t)‖ ≤ R / 2 := fun t ht => by
      calc ‖w t + h' (w t)‖ ≤ (1 + L) * ‖w t‖ := hh'.norm_lift_le hL (w t)
        _ ≤ (1 + L) * (Cw * c₀) := by gcongr; exact hwc₀ t ht
        _ = (1 + L) * Cw * c₀ := by ring
        _ ≤ R / 2 := hc₀R
    -- the lift is a solution of the cutoff field on `[a, 0]`
    have hlift := isIntegralCurveOn_lift_of_cutoff hP hh hinv hg hgf' hh' hL hh'h' hR hRρ hRr
      hPR (hwI.mono (Icc_subset_Iic_self : Icc a 0 ⊆ Iic 0)) (hwP a) hwsmall
    -- Carr's estimate along it
    have hPX : ∀ t, P (w t + h' (w t)) = w t := fun t => hh'.proj_lift (hwP t)
    have hBa : ‖(1 - P) (w a + h' (w a)) - ψ (P (w a + h' (w a)))‖ ≤ (1 + L) * Cw * c₀ := by
      rw [hPX, compl_apply, hPX, add_sub_cancel_left]
      have hLa : ‖h' (w a)‖ ≤ L * ‖w a‖ := by
        simpa [hh'.map_zero] using hL.norm_sub_le (w a) 0
      calc ‖h' (w a) - ψ (w a)‖ ≤ ‖h' (w a)‖ + ‖ψ (w a)‖ := norm_sub_le _ _
        _ ≤ L * ‖w a‖ + ‖w a‖ := add_le_add hLa (hψn _)
        _ = (1 + L) * ‖w a‖ := by ring
        _ ≤ (1 + L) * (Cw * c₀) := by gcongr; exact hwc₀ a ⟨le_rfl, ha⟩
        _ = (1 + L) * Cw * c₀ := by ring
    have hcarr := norm_sub_cutoff_le_of_segment hP hη.le hq hqη hst hg hψ hψd hψP hM hMb hk₂
      ha (x := fun t => w t + h' (w t)) (fun t ht => hlift t ht) (V := Cw * ‖u‖)
      (by positivity) (fun t ht => by
        show ‖P (w t + h' (w t))‖ ≤ _
        rw [hPX]; exact (hwb' t ht).trans_eq (by ring)) hBa
    beta_reduce at hcarr
    rw [hPX, compl_apply, hPX, add_sub_cancel_left, hw0] at hcarr
    have hpow : Real.exp (q * η * a) = ‖u‖ ^ q / c₀ ^ q := by
      rw [← Real.div_rpow (norm_nonneg _) hc₀.le, Real.rpow_def_of_pos (div_pos hpos hc₀), hla]
      ring_nf
    refine hcarr.trans_eq ?_
    rw [hpow, Real.mul_rpow hCw (norm_nonneg _), hCfin, hk₂def]
    ring
  -- conclusion
  refine IsBigO.of_bound Cfin ?_
  filter_upwards [inter_mem_nhdsWithin (Set.range P)
    (Metric.ball_mem_nhds 0 (lt_min hc₀ (lt_min hrψ hr)))] with u ⟨⟨w₀, hw₀⟩, hu⟩
  subst hw₀
  rw [Metric.mem_ball, dist_zero_right] at hu
  have hPu : P (P w₀) = P w₀ := hP.idem w₀
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have hu1 : ‖P w₀‖ ≤ c₀ := hu.le.trans (min_le_left _ _)
  have hu2 : ‖P w₀‖ < rψ := hu.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hu3 : ‖P (P w₀)‖ ≤ r := by
    rw [hPu]; exact hu.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  rw [← hh'h' _ hu3, ← hψφ _ hu2]
  exact key (P w₀) hPu hu1

/-- **The quadratic part of every tangent centre manifold** (`3ε < β`). If `f(0) = 0`, `f` has
strict derivative `0` at `0`, `f(x) = Q(x, x) + O(‖x‖³)` and `H₀` (values in `ker P`) solves the
homological equation, then every graph map `h` with strict derivative `0` at `0` and locally
invariant graph has quadratic part `H₀`: `h(u) = H₀(u, u) + O(‖u‖³)` on `range P`
(`isOrder_sub_of_invariantGraph` with the candidate `quadGraph P H₀`). -/
@[tmio T, powerlib_foundation] theorem hasQuadraticPart_of_invariantGraph
    (hP : IsCommutingProjection A P) {K ε β : ℝ} (hε : 0 ≤ ε) (hgap : 3 * ε < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    (hf0 : f 0 = 0) (hf : HasStrictFDerivAt f (0 : State n →L[ℝ] State n) 0)
    {Q H₀ : State n →L[ℝ] State n →L[ℝ] State n}
    (hf2 : (fun x => f x - Q x x) =O[𝓝 0] fun x => ‖x‖ ^ 3)
    (hhom : IsHomological A P Q H₀) (hPH : ∀ u v, P (H₀ u v) = 0)
    (hh : IsGraphMap P h) (hhs : HasStrictFDerivAt h (0 : State n →L[ℝ] State n) 0)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hinv : ∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
      φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h) :
    HasQuadraticPart P h H₀ := by
  have hd := isOrder_sub_of_invariantGraph hP hε (q := 3) (by norm_num) hgap hcen hst hf0 hf hh
    hhs hρ hinv (contDiff_quadGraph P H₀).contDiffAt (by simp [quadGraph])
    (fderiv_quadGraph_zero P H₀) (fun x => hPH _ _) (isOrder_invarianceDefect_quadGraph hP hhom hf2)
  refine hd.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [self_mem_nhdsWithin] with v hv
  obtain ⟨w, rfl⟩ := hv
  simp [quadGraph, hP.idem]

/-- **The invariance equation of a locally invariant graph.** Let `f(0) = 0` with strict
derivative `0` at `0`, and let the graph of a graph map `h`, continuous at `0`, be locally
invariant in the ball of radius `ρ`. There is `r > 0` such that at every `u ∈ range P` with
`‖u‖ < r` where `h` is differentiable the invariance defect vanishes:
`Dh(u)(PAu + Pf(u + h u)) = (1 − P)A h(u) + (1 − P) f(u + h u)` (differentiate
`x = P x + h(P x)` from the right along the solution through `u + h u`). -/
@[tmio T, powerlib_foundation] theorem invarianceDefect_eq_zero_of_invariantGraph
    (hP : IsCommutingProjection A P) (hf0 : f 0 = 0)
    (hf : HasStrictFDerivAt f (0 : State n →L[ℝ] State n) 0) (hh : IsGraphMap P h)
    (hhc : ContinuousAt h 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hinv : ∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
      φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h) :
    ∃ r > 0, ∀ u, P u = u → ‖u‖ < r → DifferentiableAt ℝ h u →
      invarianceDefect A P f h u = 0 := by
  obtain ⟨rf, hrf, g, hg, -, hgf, -⟩ := exists_small_lipschitz_cutoff hf0 hf one_pos
  set R := min ρ rf with hRdef
  have hR : 0 < R := lt_min hρ hrf
  obtain ⟨r₁, hr₁, hr₁h⟩ := Metric.continuousAt_iff.1 hhc (R / 4) (by positivity)
  refine ⟨min r₁ (R / 4), lt_min hr₁ (by positivity), fun u hu hur hd => ?_⟩
  have hu1 : ‖u‖ < r₁ := hur.trans_le (min_le_left _ _)
  have hu2 : ‖u‖ < R / 4 := hur.trans_le (min_le_right _ _)
  have hhu : ‖h u‖ < R / 4 := by
    have := hr₁h (x := u) (by rwa [dist_zero_right])
    rwa [hh.map_zero, dist_zero_right] at this
  set x₀ := u + h u with hx₀
  have hx₀n : ‖x₀‖ < R / 2 := (norm_add_le _ _).trans_lt (by linarith)
  have hGl : LipschitzWith (‖A‖₊ + Real.toNNReal 1) (fullField A g) := A.lipschitzWith.add hg
  obtain ⟨x, hx0, hx⟩ := Flow.forwardComplete_of_lipschitzWith hGl 0 x₀
  -- a short segment in the ball
  obtain ⟨τ₀, hτ₀, hτ₀x⟩ := Metric.continuousWithinAt_iff.1
    (hx.continuousOn 0 (mem_Ici.2 le_rfl)) (R / 2) (by positivity)
  set τ := τ₀ / 2 with hτdef
  have hτ : 0 < τ := by positivity
  have hball : ∀ t ∈ Icc 0 τ, ‖x t‖ < R := fun t ht => by
    have h1 := hτ₀x (x := t) ht.1
      (by rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]; linarith [ht.2])
    rw [dist_eq_norm, hx0] at h1
    have := norm_sub_norm_le (x t) x₀
    linarith
  have hRrf : R ≤ rf := min_le_right _ _
  have htraj : IsTrajectoryOn x (fullField A f) 0 τ :=
    isIntegralCurveOn_of_eq_on_curve (hx.mono Icc_subset_Ici_self) fun t ht => by
      show A (x t) + g (x t) = A (x t) + f (x t)
      rw [hgf _ ((hball t ht).le.trans hRrf)]
  have hgr := hinv 0 τ x htraj (by rw [hx0]; exact hh.lift_mem_graph hu)
    fun t ht => (hball t ht).trans_le (min_le_left _ _)
  -- differentiate `x = P x + h (P x)` at `0` from the right
  set x' := A x₀ + f x₀ with hx'
  have hxd : HasDerivWithinAt x x' (Icc 0 τ) 0 := by
    have h1 := (hx 0 (mem_Ici.2 le_rfl)).mono (Icc_subset_Ici_self : Icc 0 τ ⊆ Ici 0)
    have e : fullField A g (x 0) = x' := by
      rw [hx0, hx', fullField, hgf _ (hx₀n.le.trans (by linarith))]
    exact h1.congr_deriv e
  have hPx0 : P (x 0) = u := by rw [hx0, hh.proj_lift hu]
  have hd' : HasFDerivAt h (fderiv ℝ h u) (P (x 0)) := by rw [hPx0]; exact hd.hasFDerivAt
  have hPd : HasDerivWithinAt (fun t => P (x t)) (P x') (Icc 0 τ) 0 :=
    P.hasFDerivAt.comp_hasDerivWithinAt 0 hxd
  have hsum : HasDerivWithinAt (fun t => P (x t) + h (P (x t)))
      (P x' + fderiv ℝ h u (P x')) (Icc 0 τ) 0 :=
    hPd.add (hd'.comp_hasDerivWithinAt 0 hPd)
  have hsum' : HasDerivWithinAt x (P x' + fderiv ℝ h u (P x')) (Icc 0 τ) 0 :=
    hsum.congr_of_mem (fun t ht => hh.eq_lift_of_mem_graph (hgr t ht)) ⟨le_rfl, hτ.le⟩
  have key : x' = P x' + fderiv ℝ h u (P x') :=
    (uniqueDiffOn_Icc hτ 0 ⟨le_rfl, hτ.le⟩).eq_deriv _ hxd hsum'
  -- the invariance defect
  have hPAh : P (A (h u)) = 0 := by rw [← hP.comm, hh.proj_apply, map_zero]
  have hPAu : P (A u) = A u := by rw [← hP.comm, hu]
  have hred : reducedField A P f h u = P x' := by
    simp only [reducedField, hx', hx₀, map_add, hPAh, add_zero]
  have hnorm : normalField A P f h u = x' - P x' := by
    simp only [normalField, compl_apply, hx', hx₀, map_add, hPAh, hPAu, sub_zero, add_zero]
    abel
  rw [invarianceDefect, hred, hnorm, sub_eq_zero, eq_sub_iff_add_eq, add_comm]
  exact key.symm

/-- **Tangent centre manifolds agree to every order the gap allows.** Under the dichotomy with
`qε < β` (`q ≥ 1`), for `f(0) = 0` with strict derivative `0` at `0`: if `h₁`, `h₂` are graph
maps whose graphs are locally invariant, `h₁` with strict derivative `0` at `0` and `h₂` of class
`C¹` near `0` with `Dh₂(0) = 0`, then `h₁(u) − h₂(u) = O(‖u‖^q)` on `range P` (the defect of `h₂`
vanishes near `0`, `invarianceDefect_eq_zero_of_invariantGraph`). Centre manifolds are not
unique, but they are indistinguishable at every polynomial order below `β/ε` (every order when
`ε = 0`). -/
@[tmio T, powerlib_foundation] theorem isOrder_sub_of_invariantGraphs
    (hP : IsCommutingProjection A P) {K ε β q : ℝ} (hε : 0 ≤ ε) (hq : 1 ≤ q)
    (hqε : q * ε < β) (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    (hf0 : f 0 = 0) (hf : HasStrictFDerivAt f (0 : State n →L[ℝ] State n) 0)
    {h₁ h₂ : State n → State n} (hh₁ : IsGraphMap P h₁)
    (hhs₁ : HasStrictFDerivAt h₁ (0 : State n →L[ℝ] State n) 0) {ρ₁ : ℝ} (hρ₁ : 0 < ρ₁)
    (hinv₁ : ∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
      φ t₀ ∈ graph P h₁ → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ₁) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h₁)
    (hh₂ : IsGraphMap P h₂) (hh₂c : ContDiffAt ℝ 1 h₂ 0) (hDh₂ : fderiv ℝ h₂ 0 = 0)
    {ρ₂ : ℝ} (hρ₂ : 0 < ρ₂)
    (hinv₂ : ∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
      φ t₀ ∈ graph P h₂ → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ₂) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h₂) :
    IsOrder P (fun u => h₁ u - h₂ u) q := by
  obtain ⟨r, hr, hzero⟩ := invarianceDefect_eq_zero_of_invariantGraph hP hf0 hf hh₂
    hh₂c.continuousAt hρ₂ hinv₂
  have hdiff : ∀ᶠ u in 𝓝 (0 : State n), DifferentiableAt ℝ h₂ u :=
    (hh₂c.eventually (by simp)).mono fun u hu => hu.differentiableAt one_ne_zero
  have hdef : IsOrder P (invarianceDefect A P f h₂) q := by
    refine IsBigO.of_bound 0 ?_
    filter_upwards [inter_mem_nhdsWithin (Set.range P)
      (inter_mem (Metric.ball_mem_nhds 0 hr) hdiff)] with u ⟨⟨w, hw⟩, hu, hdu⟩
    subst hw
    rw [Metric.mem_ball, dist_zero_right] at hu
    rw [hzero (P w) (hP.idem w) hu hdu, norm_zero, zero_mul]
  exact isOrder_sub_of_invariantGraph hP hε hq hqε hcen hst hf0 hf hh₁ hhs₁ hρ₁ hinv₁ hh₂c
    hh₂.map_zero hDh₂ hh₂.proj_apply hdef

end State

end powerlib.Dynamics.CenterManifold
