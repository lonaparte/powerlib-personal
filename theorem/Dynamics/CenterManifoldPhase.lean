import theorem.Dynamics.CenterManifold

/-! # Asymptotic phase: the centre manifold attracts (foundation)

For the globally Lipschitz cutoff field `ẋ = A x + g(x)` of the centre-manifold construction
(`theorem/Dynamics/CenterManifold.lean`), every forward solution has an asymptotic phase on the
centre manifold: a whole-line solution on the graph that it approaches like `e^{−γt}`, with a
constant times the initial distance `‖(1 − P)x(0) − h(P x(0))‖` to the graph.

Scope.
* A real Banach space `E`, `A`, `P` with `P² = P`, `AP = PA` (`IsCommutingProjection`), the
  centre–stable dichotomy as theorem hypotheses `‖e^{tA}P‖ ≤ K e^{ε|t|}` (all `t`),
  `‖e^{tA}(1 − P)‖ ≤ K e^{−βt}` (`t ≥ 0`), and a rate `γ` with `ε < γ < β`.
* `g` is `δ`-Lipschitz on all of `E` (the cutoff of the construction), `h` is an `L`-Lipschitz map
  into `ker P` (the graph map); the contraction needs `K δ ((1 + K L)/(γ − ε) + 1/(β − γ)) < 1`.
  No differentiability of `h` is used (the route of Carr's Lemma 1 through `D h` is replaced by
  a Lyapunov–Perron contraction for the difference on `[0, ∞)`).
* The local statements for `ẋ = A x + f(x)` near `0` and the stability transfer are in
  `theorem/Dynamics/CenterReductionStability.lean`. Generic; no physical system (foundation).

Source: Carr, *Applications of Centre Manifold Theory* (1981), Ch. 2, Lemma 1 and the proof of
Theorem 2 (exponential attraction to the centre manifold and asymptotic phase); Vanderbauwhede,
"Centre manifolds, normal forms and elementary bifurcations" (1989), §2 (Lyapunov–Perron operators
in exponentially weighted spaces); Kelley (1967); Pliss (1964) (the reduction principle).

Results.
* Estimates for a forcing `b` with `‖b(s)‖ ≤ M e^{−γs}` (`s ≥ 0`): `nonneg_of_center_bound`,
  `integrableOn_center_Ioi` (the centre integrand `e^{−sA}P b(s)` on `(0, ∞)`),
  `norm_center_Ioi_le` (`‖e^{tA}∫_t^∞ e^{−sA}P b‖ ≤ K M e^{−γt}/(γ − ε)`), `norm_stable_conv_le`
  (`‖∫₀ᵗ e^{(t−s)A}(1 − P) b‖ ≤ K M e^{−γt}/(β − γ)`), `norm_phase_le` (the transform
  `e^{tA}(c − ∫_0^∞ e^{−sA}P b + ∫₀ᵗ e^{−sA} b)`, `P c = 0`, decays like `e^{−γt}`),
  `hasDerivAt_phase` (it solves `ẋ = A x + b`).
* `exists_phase`: for a continuous `x`, a solution `w` on `[0, ∞)` of
  `ẇ = A w + g(x + w) − g(x)` with `x(0) + w(0)` on the graph of `h` and
  `‖w(t)‖ ≤ K/(1 − θ) e^{−γt} ‖(1 − P)x(0) − h(P x(0))‖` (contraction on bounded continuous
  functions with the weight `e^{γt}`).
* `exists_phase_of_isIntegralCurveOn`: the same from time `t₀` for a forward solution `φ` of
  `ẋ = A x + g(x)`: a forward solution of the same field starting on the graph of `h` (any
  Lipschitz map into `ker P`) at distance `≤ C e^{−γ(t−t₀)}` from `φ`.
* `exists_graph_phase`: through every graph point passes a whole-line solution on the graph
  (the hypothesis supplied by `exists_graph_of_lipschitz`); then every forward solution of
  `ẋ = A x + g(x)` from time `t₀` has an asymptotic phase on the graph.
* `exists_lipschitz_graphMap_cutoff`: a graph map with strict derivative `0` at `0` agrees, where
  `‖P x‖ ≤ r`, with a globally Lipschitz graph map `h' = (1 − P) h₁ P`.
* `exists_tangentGraph_phase`: for `f` and any graph map `h` with strict derivative `0` at `0`,
  cutoffs `g` of `f` and `h'` of `h` (`exists_lipschitz_graphMap_cutoff`) for which the previous
  item holds; with local invariance of the graph of `h` this gives the reduction principle for
  any tangent centre manifold (`theorem/Dynamics/CenterReductionStability.lean`).
* `lipschitzWith_of_globalSolutions`: the graph map of the construction is Lipschitz with the
  explicit constant `‖1 − P‖ K ‖P‖/(1 − Kδκ)` (from `norm_sub_fixedPoint_le`).
* `exists_centerManifold_phase`: the construction of `exists_centerManifold_data`, for `δ` small,
  with the asymptotic phase of every forward solution of the cutoff field.
-/

noncomputable section
namespace powerlib.Dynamics.CenterManifold

open Set Filter Topology MeasureTheory
open powerlib.Dynamics.LyapunovPerron

section Estimates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {A P : E →L[ℝ] E} {K ε γ β M : ℝ} {b : ℝ → E}

omit [CompleteSpace E] in
@[tmio T, powerlib_foundation] theorem nonneg_of_center_bound
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|)) : 0 ≤ K := by
  have h := (norm_nonneg _).trans (hcen 0)
  simpa using h

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[tmio T, powerlib_foundation] private theorem nonneg_of_decay_bound
    (hbM : ∀ s, 0 ≤ s → ‖b s‖ ≤ M * Real.exp (-(γ * s))) : 0 ≤ M := by
  have h := (norm_nonneg _).trans (hbM 0 le_rfl)
  simpa using h

/-- The centre integrand of a forcing decaying like `e^{−γs}` is integrable on `(0, ∞)`:
`‖e^{−sA} P b(s)‖ ≤ K M e^{(ε − γ)s}`. -/
@[tmio T, powerlib_foundation] theorem integrableOn_center_Ioi (hb : Continuous b)
    (hεγ : ε < γ) (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hbM : ∀ s, 0 ≤ s → ‖b s‖ ≤ M * Real.exp (-(γ * s))) :
    IntegrableOn (fun s => expFlow A (-s) (P (b s))) (Ioi 0) := by
  have hK := nonneg_of_center_bound hcen
  have hM := nonneg_of_decay_bound hbM
  have hc : Continuous fun s => expFlow A (-s) (P (b s)) :=
    continuous_expFlow_neg_apply (P.continuous.comp hb)
  refine ((integrableOn_exp_mul_Ioi (a := ε - γ) (by linarith) 0).const_mul (K * M)).mono'
    hc.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_)
  have hs' : 0 < s := hs
  calc ‖expFlow A (-s) (P (b s))‖ = ‖(expFlow A (-s) * P) (b s)‖ := rfl
    _ ≤ ‖expFlow A (-s) * P‖ * ‖b s‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ K * Real.exp (ε * |-s|) * (M * Real.exp (-(γ * s))) :=
        mul_le_mul (hcen _) (hbM s hs'.le) (norm_nonneg _) (by positivity)
    _ = K * M * Real.exp ((ε - γ) * s) := by
        rw [abs_neg, abs_of_pos hs', mul_mul_mul_comm, ← Real.exp_add]; ring_nf

/-- The centre tail: `‖e^{tA} ∫_t^∞ e^{−sA} P b(s) ds‖ ≤ K M e^{−γt}/(γ − ε)` for `t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem norm_center_Ioi_le (hb : Continuous b) (hεγ : ε < γ)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hbM : ∀ s, 0 ≤ s → ‖b s‖ ≤ M * Real.exp (-(γ * s))) {t : ℝ} (ht : 0 ≤ t) :
    ‖expFlow A t (∫ s in Ioi t, expFlow A (-s) (P (b s)))‖ ≤
      K * M / (γ - ε) * Real.exp (-(γ * t)) := by
  have hK := nonneg_of_center_bound hcen
  have hM := nonneg_of_decay_bound hbM
  have hd : 0 < γ - ε := sub_pos.2 hεγ
  have hint := (integrableOn_center_Ioi hb hεγ hcen hbM).mono_set (Ioi_subset_Ioi ht)
  rw [← (expFlow A t).integral_comp_comm hint]
  set B : ℝ → ℝ := fun s => K * M * Real.exp (-(ε * t)) * Real.exp ((ε - γ) * s) with hB
  have hBi : IntegrableOn B (Ioi t) :=
    (integrableOn_exp_mul_Ioi (by linarith) t).const_mul _
  have hpt : ∀ s ∈ Ioi t, ‖expFlow A t (expFlow A (-s) (P (b s)))‖ ≤ B s := by
    intro s hs
    have hs' : t < s := hs
    rw [expFlow_apply_apply]
    calc ‖expFlow A (t + -s) (P (b s))‖ = ‖(expFlow A (t + -s) * P) (b s)‖ := rfl
      _ ≤ ‖expFlow A (t + -s) * P‖ * ‖b s‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * Real.exp (ε * |t + -s|) * (M * Real.exp (-(γ * s))) :=
          mul_le_mul (hcen _) (hbM s (ht.trans hs'.le)) (norm_nonneg _) (by positivity)
      _ = B s := by
          simp only [hB]
          rw [abs_of_neg (by linarith), mul_mul_mul_comm, ← Real.exp_add, mul_assoc (K * M),
            ← Real.exp_add]
          ring_nf
  refine (norm_integral_le_of_norm_le hBi
    (ae_restrict_of_forall_mem measurableSet_Ioi hpt)).trans_eq ?_
  have he : Real.exp (-(ε * t)) * Real.exp ((ε - γ) * t) = Real.exp (-(γ * t)) := by
    rw [← Real.exp_add]; ring_nf
  have hne : ε - γ ≠ 0 := by linarith
  rw [hB, integral_const_mul, integral_exp_mul_Ioi (by linarith), ← he]
  field_simp
  ring

omit [CompleteSpace E] in
/-- The stable convolution: `‖∫₀ᵗ e^{(t−s)A}(1 − P) b(s) ds‖ ≤ K M e^{−γt}/(β − γ)` for
`t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem norm_stable_conv_le (hγβ : γ < β)
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    (hbM : ∀ s, 0 ≤ s → ‖b s‖ ≤ M * Real.exp (-(γ * s))) {t : ℝ} (ht : 0 ≤ t) :
    ‖∫ s in (0)..t, expFlow A (t - s) ((1 - P) (b s))‖ ≤
      K * M / (β - γ) * Real.exp (-(γ * t)) := by
  have hK := nonneg_of_stable_bound hst
  have hM := nonneg_of_decay_bound hbM
  have hd : 0 < β - γ := sub_pos.2 hγβ
  set G : ℝ → ℝ := fun s => K * M * Real.exp (-(β * t)) * Real.exp ((β - γ) * s) / (β - γ)
    with hG
  have hc : Continuous fun s => K * M * Real.exp (-(β * t)) * Real.exp ((β - γ) * s) := by
    fun_prop
  have hGd : ∀ s, HasDerivAt G (K * M * Real.exp (-(β * t)) * Real.exp ((β - γ) * s)) s := by
    intro s
    have h := ((((hasDerivAt_id' s).const_mul (β - γ)).exp).const_mul
      (K * M * Real.exp (-(β * t)))).div_const (β - γ)
    refine h.congr_deriv ?_
    field_simp
  have hint : ∫ s in (0)..t, K * M * Real.exp (-(β * t)) * Real.exp ((β - γ) * s) =
      G t - G 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hGd s) (hc.intervalIntegrable _ _)
  have hle := intervalIntegral.norm_integral_le_of_norm_le ht
    (ae_of_all volume fun s (hs : s ∈ Ioc 0 t) => by
      calc ‖expFlow A (t - s) ((1 - P) (b s))‖ = ‖(expFlow A (t - s) * (1 - P)) (b s)‖ := rfl
        _ ≤ ‖expFlow A (t - s) * (1 - P)‖ * ‖b s‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ K * Real.exp (-(β * (t - s))) * (M * Real.exp (-(γ * s))) :=
            mul_le_mul (hst _ (sub_nonneg.2 hs.2)) (hbM s hs.1.le) (norm_nonneg _)
              (by positivity)
        _ = K * M * Real.exp (-(β * t)) * Real.exp ((β - γ) * s) := by
            rw [mul_mul_mul_comm, ← Real.exp_add, mul_assoc (K * M), ← Real.exp_add]
            ring_nf)
    (hc.intervalIntegrable _ _)
  rw [hint] at hle
  refine hle.trans ?_
  have hG0 : 0 ≤ G 0 := by positivity
  have hGt : G t = K * M / (β - γ) * Real.exp (-(γ * t)) := by
    simp only [hG]
    rw [mul_assoc (K * M), ← Real.exp_add, show -(β * t) + (β - γ) * t = -(γ * t) by ring]
    ring
  linarith

/-- **The transform on `[0, ∞)` decays.** For `t ≥ 0` and `P c = 0`,
`‖e^{tA}(c − ∫_0^∞ e^{−sA}P b + ∫₀ᵗ e^{−sA} b)‖ ≤ (K‖c‖ + K M/(γ − ε) + K M/(β − γ)) e^{−γt}`:
the expression is `e^{tA}c − e^{tA}∫_t^∞ e^{−sA}P b + ∫₀ᵗ e^{(t−s)A}(1 − P) b`. -/
@[tmio T, powerlib_foundation] theorem norm_phase_le (hb : Continuous b) (hεγ : ε < γ)
    (hγβ : γ < β) (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    (hbM : ∀ s, 0 ≤ s → ‖b s‖ ≤ M * Real.exp (-(γ * s))) {c : E} (hc : P c = 0) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖expFlow A t (c - (∫ s in Ioi 0, expFlow A (-s) (P (b s))) +
        ∫ s in (0)..t, expFlow A (-s) (b s))‖ ≤
      (K * ‖c‖ + K * M / (γ - ε) + K * M / (β - γ)) * Real.exp (-(γ * t)) := by
  have hK := nonneg_of_stable_bound hst
  have hI0 := integrableOn_center_Ioi hb hεγ hcen hbM
  have hIt := hI0.mono_set (Ioi_subset_Ioi ht)
  have hcP : Continuous fun s => expFlow A (-s) (P (b s)) :=
    continuous_expFlow_neg_apply (P.continuous.comp hb)
  have hcQ : Continuous fun s => expFlow A (-s) ((1 - P) (b s)) :=
    continuous_expFlow_neg_apply ((1 - P).continuous.comp hb)
  have hsplit : ∫ s in (0)..t, expFlow A (-s) (b s) =
      (∫ s in (0)..t, expFlow A (-s) (P (b s))) +
        ∫ s in (0)..t, expFlow A (-s) ((1 - P) (b s)) := by
    rw [← intervalIntegral.integral_add (hcP.intervalIntegrable _ _)
      (hcQ.intervalIntegrable _ _)]
    congr 1; funext s
    rw [← map_add, compl_apply, add_sub_cancel]
  have htail : ∫ s in Ioi 0, expFlow A (-s) (P (b s)) =
      (∫ s in (0)..t, expFlow A (-s) (P (b s))) + ∫ s in Ioi t, expFlow A (-s) (P (b s)) :=
    (intervalIntegral.integral_interval_add_Ioi hI0 hIt).symm
  have hconv : expFlow A t (∫ s in (0)..t, expFlow A (-s) ((1 - P) (b s))) =
      ∫ s in (0)..t, expFlow A (t - s) ((1 - P) (b s)) := by
    rw [← (expFlow A t).intervalIntegral_comp_comm (hcQ.intervalIntegrable _ _)]
    congr 1; funext s; rw [expFlow_apply_apply, ← sub_eq_add_neg]
  have heq : expFlow A t (c - (∫ s in Ioi 0, expFlow A (-s) (P (b s))) +
      ∫ s in (0)..t, expFlow A (-s) (b s)) = expFlow A t c -
      expFlow A t (∫ s in Ioi t, expFlow A (-s) (P (b s))) +
      ∫ s in (0)..t, expFlow A (t - s) ((1 - P) (b s)) := by
    rw [hsplit, htail, ← hconv, ← map_sub, ← map_add]
    congr 1
    abel
  rw [heq]
  have h1 : ‖expFlow A t c‖ ≤ K * ‖c‖ * Real.exp (-(γ * t)) := by
    have hc' : expFlow A t c = (expFlow A t * (1 - P)) c := by
      change _ = expFlow A t ((1 - P) c)
      rw [compl_apply, hc, sub_zero]
    calc ‖expFlow A t c‖ ≤ ‖expFlow A t * (1 - P)‖ * ‖c‖ := by
          rw [hc']; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * Real.exp (-(β * t)) * ‖c‖ := by gcongr; exact hst t ht
      _ ≤ K * Real.exp (-(γ * t)) * ‖c‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.2 (by nlinarith)) hK) (norm_nonneg _)
      _ = K * ‖c‖ * Real.exp (-(γ * t)) := by ring
  have h2 := norm_center_Ioi_le hb hεγ hcen hbM ht
  have h3 := norm_stable_conv_le hγβ hst hbM ht
  calc _ ≤ ‖expFlow A t c‖ + ‖expFlow A t (∫ s in Ioi t, expFlow A (-s) (P (b s)))‖ +
        ‖∫ s in (0)..t, expFlow A (t - s) ((1 - P) (b s))‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ K * ‖c‖ * Real.exp (-(γ * t)) + K * M / (γ - ε) * Real.exp (-(γ * t)) +
        K * M / (β - γ) * Real.exp (-(γ * t)) := by gcongr
    _ = _ := by ring

/-- The transform solves `ẋ = A x + b`: `t ↦ e^{tA}(v + ∫₀ᵗ e^{−sA} b(s) ds)`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_phase (hb : Continuous b) (v : E) (t : ℝ) :
    HasDerivAt (fun t => expFlow A t (v + ∫ s in (0)..t, expFlow A (-s) (b s)))
      (A (expFlow A t (v + ∫ s in (0)..t, expFlow A (-s) (b s))) + b t) t := by
  have hY := ((continuous_expFlow_neg_apply (A := A) hb).integral_hasStrictDerivAt 0
    t).hasDerivAt.const_add v
  have h := (hasDerivAt_expFlow (A := A) t).clm_apply hY
  refine h.congr_deriv ?_
  rw [expFlow_mul_comm, expFlow_apply_neg_apply]
  rfl

end Estimates

/-! ## The contraction on `[0, ∞)` -/

section Phase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {A P : E →L[ℝ] E} {K ε γ β : ℝ}

/-- **Asymptotic phase, the contraction.** Under the dichotomy with `ε < γ < β`, for a
`δ`-Lipschitz `g`, an `L`-Lipschitz `h` into `ker P` with
`θ = K δ ((1 + K L)/(γ − ε) + 1/(β − γ)) < 1`, and a continuous `x`, there is `w` solving
`ẇ = A w + g(x + w) − g(x)` on `[0, ∞)` with `x(0) + w(0)` on the graph of `h`
(`(1 − P)(x(0) + w(0)) = h(P(x(0) + w(0)))`) and
`‖w(t)‖ ≤ K/(1 − θ) e^{−γt} ‖(1 − P)x(0) − h(P x(0))‖`. The unknown is `y = e^{γt} w`, a bounded
continuous function; the map is
`w ↦ e^{tA}(c − ∫_0^∞ e^{−sA}P b + ∫₀ᵗ e^{−sA} b)`, `b = g(x + w) − g(x)`,
`c = h(P x(0) − ∫_0^∞ e^{−sA}P b) − (1 − P)x(0)`. -/
@[tmio T, powerlib_foundation] theorem exists_phase (hP : IsCommutingProjection A P)
    (hεγ : ε < γ) (hγβ : γ < β) (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {g : E → E} {δ : NNReal} (hg : LipschitzWith δ g) {h : E → E} {L : NNReal}
    (hh : LipschitzWith L h) (hhP : ∀ x, P (h x) = 0)
    (hk : K * δ * ((1 + K * L) / (γ - ε) + 1 / (β - γ)) < 1) {x : ℝ → E} (hx : Continuous x) :
    ∃ w : ℝ → E, (∀ t, 0 ≤ t → HasDerivAt w (A (w t) + (g (x t + w t) - g (x t))) t) ∧
      (1 - P) (x 0 + w 0) = h (P (x 0 + w 0)) ∧
      ∀ t, 0 ≤ t → ‖w t‖ ≤ K / (1 - K * δ * ((1 + K * L) / (γ - ε) + 1 / (β - γ))) *
        Real.exp (-(γ * t)) * ‖(1 - P) (x 0) - h (P (x 0))‖ := by
  have hK := nonneg_of_stable_bound hst
  have hd1 : 0 < γ - ε := sub_pos.2 hεγ
  have hd2 : 0 < β - γ := sub_pos.2 hγβ
  set θ := K * δ * ((1 + K * L) / (γ - ε) + 1 / (β - γ)) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : 0 < 1 - θ := sub_pos.2 hk
  have hcancel : ∀ t, Real.exp (γ * t) * Real.exp (-(γ * t)) = 1 := fun t => by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  -- the weighted unknown `w = e^{−γt} y` and the forcing `b = g(x + w) − g(x)`
  let W : BoundedContinuousFunction ℝ E → ℝ → E := fun y s => Real.exp (-(γ * s)) • y s
  let B : BoundedContinuousFunction ℝ E → ℝ → E := fun y s => g (x s + W y s) - g (x s)
  have hWc : ∀ y, Continuous (W y) := fun y =>
    (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).smul y.continuous
  have hBc : ∀ y, Continuous (B y) := fun y =>
    (hg.continuous.comp (hx.add (hWc y))).sub (hg.continuous.comp hx)
  have hBd : ∀ y₁ y₂ s, ‖B y₁ s - B y₂ s‖ ≤ (δ * dist y₁ y₂) * Real.exp (-(γ * s)) := by
    intro y₁ y₂ s
    have e : B y₁ s - B y₂ s = g (x s + W y₁ s) - g (x s + W y₂ s) := by
      simp only [B]; abel
    have hW : ‖W y₁ s - W y₂ s‖ ≤ dist y₁ y₂ * Real.exp (-(γ * s)) := by
      simp only [W, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [mul_comm, ← dist_eq_norm]
      exact mul_le_mul_of_nonneg_right (BoundedContinuousFunction.dist_coe_le_dist s)
        (Real.exp_pos _).le
    rw [e]
    calc ‖g (x s + W y₁ s) - g (x s + W y₂ s)‖ ≤ δ * ‖(x s + W y₁ s) - (x s + W y₂ s)‖ := by
          simpa [dist_eq_norm] using hg.dist_le_mul (x s + W y₁ s) (x s + W y₂ s)
      _ = δ * ‖W y₁ s - W y₂ s‖ := by rw [add_sub_add_left_eq_sub]
      _ ≤ δ * (dist y₁ y₂ * Real.exp (-(γ * s))) := by gcongr
      _ = _ := by ring
  have hB0 : ∀ s, B 0 s = 0 := fun s => by simp [B, W]
  have hbM : ∀ y s, 0 ≤ s → ‖B y s‖ ≤ (δ * ‖y‖) * Real.exp (-(γ * s)) := fun y s _ => by
    have := hBd y 0 s; rwa [hB0, sub_zero, dist_zero_right] at this
  -- the centre integral, the stable datum and the transform
  let I : BoundedContinuousFunction ℝ E → E := fun y =>
    ∫ s in Ioi 0, expFlow A (-s) (P (B y s))
  let c : BoundedContinuousFunction ℝ E → E := fun y => h (P (x 0) - I y) - (1 - P) (x 0)
  let Φ : BoundedContinuousFunction ℝ E → ℝ → E := fun y t =>
    expFlow A t (c y - I y + ∫ s in (0)..t, expFlow A (-s) (B y s))
  have hIi : ∀ y, IntegrableOn (fun s => expFlow A (-s) (P (B y s))) (Ioi 0) := fun y =>
    integrableOn_center_Ioi (hBc y) hεγ hcen (hbM y)
  have hcP : ∀ y, P (c y) = 0 := fun y => by
    simp only [c, map_sub, hhP, hP.proj_compl, sub_zero]
  have hIsub : ∀ y₁ y₂, ∫ s in Ioi 0, expFlow A (-s) (P (B y₁ s - B y₂ s)) = I y₁ - I y₂ := by
    intro y₁ y₂
    rw [← integral_sub (hIi y₁) (hIi y₂)]
    congr 1; funext s; rw [map_sub, map_sub]
  have hΦsub : ∀ y₁ y₂ t, Φ y₁ t - Φ y₂ t = expFlow A t ((c y₁ - c y₂) -
      (∫ s in Ioi 0, expFlow A (-s) (P (B y₁ s - B y₂ s))) +
      ∫ s in (0)..t, expFlow A (-s) (B y₁ s - B y₂ s)) := by
    intro y₁ y₂ t
    have e2 : ∫ s in (0)..t, expFlow A (-s) (B y₁ s - B y₂ s) =
        (∫ s in (0)..t, expFlow A (-s) (B y₁ s)) - ∫ s in (0)..t, expFlow A (-s) (B y₂ s) := by
      rw [← intervalIntegral.integral_sub
        ((continuous_expFlow_neg_apply (hBc y₁)).intervalIntegrable _ _)
        ((continuous_expFlow_neg_apply (hBc y₂)).intervalIntegrable _ _)]
      congr 1; funext s; rw [map_sub]
    simp only [Φ]
    rw [hIsub, e2, ← map_sub]
    congr 1
    abel
  have hIb : ∀ y₁ y₂, ‖I y₁ - I y₂‖ ≤ K * (δ * dist y₁ y₂) / (γ - ε) := by
    intro y₁ y₂
    have h0 := norm_center_Ioi_le (A := A) (P := P) (b := fun s => B y₁ s - B y₂ s)
      ((hBc y₁).sub (hBc y₂)) hεγ hcen (fun s _ => hBd y₁ y₂ s) le_rfl
    simp only [expFlow_zero, one_apply_eq_self, mul_zero, neg_zero, Real.exp_zero,
      mul_one] at h0
    rwa [hIsub] at h0
  have hΦb : ∀ y t, 0 ≤ t → ‖Φ y t‖ ≤ (K * ‖c y‖ + K * (δ * ‖y‖) / (γ - ε) +
      K * (δ * ‖y‖) / (β - γ)) * Real.exp (-(γ * t)) := fun y t ht =>
    norm_phase_le (hBc y) hεγ hγβ hcen hst (hbM y) (hcP y) ht
  have hΦd : ∀ y₁ y₂ t, 0 ≤ t →
      ‖Φ y₁ t - Φ y₂ t‖ ≤ θ * dist y₁ y₂ * Real.exp (-(γ * t)) := by
    intro y₁ y₂ t ht
    have hcd : P (c y₁ - c y₂) = 0 := by rw [map_sub, hcP, hcP, sub_zero]
    rw [hΦsub]
    refine (norm_phase_le ((hBc y₁).sub (hBc y₂)) hεγ hγβ hcen hst (M := δ * dist y₁ y₂)
      (fun s _ => hBd y₁ y₂ s) hcd ht).trans ?_
    have hcb : ‖c y₁ - c y₂‖ ≤ L * (K * (δ * dist y₁ y₂) / (γ - ε)) := by
      have e : c y₁ - c y₂ = h (P (x 0) - I y₁) - h (P (x 0) - I y₂) := by
        simp only [c]; abel
      rw [e]
      refine (hh.norm_sub_le _ _).trans ?_
      gcongr
      rw [show P (x 0) - I y₁ - (P (x 0) - I y₂) = -(I y₁ - I y₂) by abel, norm_neg]
      exact hIb y₁ y₂
    have hsum : K * ‖c y₁ - c y₂‖ + K * (δ * dist y₁ y₂) / (γ - ε) +
        K * (δ * dist y₁ y₂) / (β - γ) ≤ θ * dist y₁ y₂ := by
      calc _ ≤ K * (L * (K * (δ * dist y₁ y₂) / (γ - ε))) + K * (δ * dist y₁ y₂) / (γ - ε) +
            K * (δ * dist y₁ y₂) / (β - γ) := by gcongr
        _ = θ * dist y₁ y₂ := by rw [hθ]; field_simp; ring
    exact mul_le_mul_of_nonneg_right hsum (Real.exp_pos _).le
  have hΦc : ∀ y, Continuous (Φ y) := fun y => continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_phase (A := A) (hBc y) (c y - I y) t).continuousAt
  -- the map on bounded continuous functions
  let F : BoundedContinuousFunction ℝ E → ℝ → E := fun y t =>
    Real.exp (γ * max t 0) • Φ y (max t 0)
  have hFc : ∀ y, Continuous (F y) := fun y =>
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id.max continuous_const))).smul
      ((hΦc y).comp (continuous_id.max continuous_const))
  have hFb : ∀ y t, ‖F y t‖ ≤ K * ‖c y‖ + K * (δ * ‖y‖) / (γ - ε) +
      K * (δ * ‖y‖) / (β - γ) := by
    intro y t
    simp only [F, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc _ ≤ Real.exp (γ * max t 0) * ((K * ‖c y‖ + K * (δ * ‖y‖) / (γ - ε) +
          K * (δ * ‖y‖) / (β - γ)) * Real.exp (-(γ * max t 0))) := by
          gcongr; exact hΦb y _ (le_max_right _ _)
      _ = (K * ‖c y‖ + K * (δ * ‖y‖) / (γ - ε) + K * (δ * ‖y‖) / (β - γ)) *
          (Real.exp (γ * max t 0) * Real.exp (-(γ * max t 0))) := by ring
      _ = _ := by rw [hcancel, mul_one]
  let S : BoundedContinuousFunction ℝ E → BoundedContinuousFunction ℝ E := fun y =>
    BoundedContinuousFunction.ofNormedAddCommGroup (F y) (hFc y) _ (hFb y)
  have hS : ContractingWith ⟨θ, hθ0⟩ S := by
    refine ⟨hk, LipschitzWith.of_dist_le_mul fun y₁ y₂ => ?_⟩
    change dist (S y₁) (S y₂) ≤ θ * dist y₁ y₂
    rw [BoundedContinuousFunction.dist_le (by positivity)]
    intro t
    change dist (F y₁ t) (F y₂ t) ≤ θ * dist y₁ y₂
    rw [dist_eq_norm]
    simp only [F, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc _ ≤ Real.exp (γ * max t 0) * (θ * dist y₁ y₂ * Real.exp (-(γ * max t 0))) := by
          gcongr; exact hΦd y₁ y₂ _ (le_max_right _ _)
      _ = θ * dist y₁ y₂ * (Real.exp (γ * max t 0) * Real.exp (-(γ * max t 0))) := by ring
      _ = θ * dist y₁ y₂ := by rw [hcancel, mul_one]
  set y := ContractingWith.fixedPoint S hS
  have hy : S y = y := hS.fixedPoint_isFixedPt
  have hyt : ∀ t, 0 ≤ t → W y t = Φ y t := by
    intro t ht
    have h1 := congrArg (fun z : BoundedContinuousFunction ℝ E => z t) hy
    change Real.exp (γ * max t 0) • Φ y (max t 0) = y t at h1
    rw [max_eq_left ht] at h1
    change Real.exp (-(γ * t)) • y t = _
    rw [← h1, smul_smul, mul_comm, hcancel, one_smul]
  -- the size of the fixed point
  have hS0 : ‖S 0‖ ≤ K * ‖(1 - P) (x 0) - h (P (x 0))‖ := by
    have hI0 : I 0 = 0 := by
      simp only [I, hB0, map_zero, integral_zero]
    have hc0 : ‖c 0‖ = ‖(1 - P) (x 0) - h (P (x 0))‖ := by
      simp only [c, hI0, sub_zero]; rw [norm_sub_rev]
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun t => ?_
    have := hFb 0 t
    simp only [norm_zero, mul_zero, zero_div, add_zero, hc0] at this
    exact this
  have hynorm : ‖y‖ ≤ K * ‖(1 - P) (x 0) - h (P (x 0))‖ / (1 - θ) := by
    have h1 := hS.dist_fixedPoint_le 0
    rw [dist_comm, dist_zero_right, dist_comm, dist_zero_right] at h1
    refine h1.trans ?_
    change ‖S 0‖ / (1 - θ) ≤ _
    gcongr
  refine ⟨Φ y, fun t ht => ?_, ?_, fun t ht => ?_⟩
  · refine (hasDerivAt_phase (A := A) (hBc y) (c y - I y) t).congr_deriv ?_
    change A (Φ y t) + (g (x t + W y t) - g (x t)) = _
    rw [hyt t ht]
  · have hw0 : Φ y 0 = c y - I y := by simp [Φ, expFlow_zero]
    have hPI : P (I y) = I y := by
      simp only [I]
      rw [← P.integral_comp_comm (hIi y)]
      congr 1; funext s
      change (P * expFlow A (-s)) (P (B y s)) = _
      rw [← (expFlow_commute hP.commute (-s)).eq]
      change expFlow A (-s) (P (P (B y s))) = _
      rw [hP.idem]
    have h1 : P (x 0 + Φ y 0) = P (x 0) - I y := by
      rw [hw0, map_add, map_sub, hcP, hPI, zero_sub, ← sub_eq_add_neg]
    rw [compl_apply, h1, hw0]
    simp only [c, compl_apply]
    abel
  · rw [← hyt t ht]
    change ‖Real.exp (-(γ * t)) • y t‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-(γ * t)) * ‖y t‖ ≤ Real.exp (-(γ * t)) *
          (K * ‖(1 - P) (x 0) - h (P (x 0))‖ / (1 - θ)) := by
          gcongr; exact (y.norm_coe_le_norm t).trans hynorm
      _ = _ := by ring

end Phase

/-! ## Asymptotic phase on the graph -/

section Graph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {A P : E →L[ℝ] E} {K ε γ β : ℝ}

/-- **Asymptotic phase towards a graph** (`exists_phase` from time `t₀`). For a `δ`-Lipschitz `g`,
an `L`-Lipschitz `h` into `ker P` and `θ = K δ ((1 + K L)/(γ − ε) + 1/(β − γ)) < 1`, every forward
solution `φ` of `ẋ = A x + g(x)` from time `t₀` has a forward solution `X` of the same field that
starts on the graph of `h` with
`‖φ(t) − X(t)‖ ≤ K/(1 − θ) e^{−γ(t − t₀)} ‖(1 − P)φ(t₀) − h(P φ(t₀))‖` for `t ≥ t₀`. -/
@[tmio T, powerlib_foundation] theorem exists_phase_of_isIntegralCurveOn
    (hP : IsCommutingProjection A P) (hεγ : ε < γ) (hγβ : γ < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {g : E → E} {δ : NNReal} (hg : LipschitzWith δ g) {h : E → E} {L : NNReal}
    (hL : LipschitzWith L h) (hhP : ∀ x, P (h x) = 0)
    (hk : K * δ * ((1 + K * L) / (γ - ε) + 1 / (β - γ)) < 1)
    {t₀ : ℝ} {φ : ℝ → E} (hφ : IsIntegralCurveOn φ (fun _ y => A y + g y) (Ici t₀)) :
    ∃ X : ℝ → E, IsIntegralCurveOn X (fun _ y => A y + g y) (Ici t₀) ∧
      X t₀ = P (X t₀) + h (P (X t₀)) ∧
      ∀ t, t₀ ≤ t → ‖φ t - X t‖ ≤ K / (1 - K * δ * ((1 + K * L) / (γ - ε) + 1 / (β - γ))) *
        Real.exp (-(γ * (t - t₀))) * ‖(1 - P) (φ t₀) - h (P (φ t₀))‖ := by
  set x : ℝ → E := fun s => φ (t₀ + max s 0) with hxdef
  have hmap : ∀ s, t₀ + max s 0 ∈ Ici t₀ := fun s => by
    simp only [mem_Ici, le_add_iff_nonneg_right, le_max_right]
  have hxc : Continuous x :=
    hφ.continuousOn.comp_continuous (continuous_const.add (continuous_id.max continuous_const))
      hmap
  have hx0 : x 0 = φ t₀ := by simp [x]
  obtain ⟨w, hwd, hw0, hwb⟩ := exists_phase hP hεγ hγβ hcen hst hg hL hhP hk hxc
  -- `x + w` solves the field on `[0, ∞)`
  have hX : IsIntegralCurveOn (fun s => x s + w s) (fun _ y => A y + g y) (Ici 0) := by
    intro s hs
    have hs' : (0 : ℝ) ≤ s := hs
    have hxs : x s = φ (t₀ + s) := by simp [x, max_eq_left hs']
    have hc : HasDerivWithinAt (fun r => φ (t₀ + r)) (A (φ (t₀ + s)) + g (φ (t₀ + s)))
        (Ici 0) s := by
      have h1 : HasDerivWithinAt φ (A (φ (t₀ + s)) + g (φ (t₀ + s))) (Ici t₀) (t₀ + s) :=
        hφ (t₀ + s) (by simp [hs'])
      have h2 : HasDerivWithinAt (fun r : ℝ => t₀ + r) 1 (Ici 0) s :=
        ((hasDerivAt_id s).const_add t₀).hasDerivWithinAt
      have h3 : MapsTo (fun r : ℝ => t₀ + r) (Ici 0) (Ici t₀) := fun r (hr : 0 ≤ r) => by
        show t₀ ≤ t₀ + r; linarith
      have := h1.scomp s h2 h3
      rwa [one_smul] at this
    have h1 : HasDerivWithinAt x (A (x s) + g (x s)) (Ici 0) s := by
      rw [hxs]
      exact hc.congr_of_mem (fun r (hr : 0 ≤ r) => by simp [x, max_eq_left hr]) hs
    have h2 := (h1.add (hwd s hs').hasDerivWithinAt)
    show HasDerivWithinAt _ (A (x s + w s) + g (x s + w s)) _ _
    convert h2 using 1
    rw [map_add]; abel
  refine ⟨fun t => x (t - t₀) + w (t - t₀), fun t ht => ?_, ?_, fun t ht => ?_⟩
  · have ht' : (0 : ℝ) ≤ t - t₀ := sub_nonneg.2 ht
    have h2 : HasDerivWithinAt (fun r : ℝ => r - t₀) 1 (Ici t₀) t :=
      ((hasDerivAt_id t).sub_const t₀).hasDerivWithinAt
    have h3 : MapsTo (fun r : ℝ => r - t₀) (Ici t₀) (Ici 0) := fun r (hr : t₀ ≤ r) =>
      sub_nonneg.2 hr
    have := (hX (t - t₀) ht').scomp t h2 h3
    rwa [one_smul] at this
  · show x (t₀ - t₀) + w (t₀ - t₀) =
      P (x (t₀ - t₀) + w (t₀ - t₀)) + h (P (x (t₀ - t₀) + w (t₀ - t₀)))
    rw [sub_self, ← hw0, compl_apply]; abel
  · have hs : 0 ≤ t - t₀ := sub_nonneg.2 ht
    have hxt : x (t - t₀) = φ t := by simp [x, max_eq_left hs]
    have hb := hwb _ hs
    rw [hx0] at hb
    show ‖φ t - (x (t - t₀) + w (t - t₀))‖ ≤ _
    rw [← hxt, sub_add_cancel_left, norm_neg]
    exact hb

/-- **Asymptotic phase on the centre manifold** (globally Lipschitz field). Let through every
point `P u + h u` of the graph of an `L`-Lipschitz graph map `h` pass a whole-line solution of
`ẋ = A x + g(x)` that stays on the graph. Then every forward solution `φ` of `ẋ = A x + g(x)`
from time `t₀` has an asymptotic phase: a whole-line solution `ψ` on the graph with
`‖φ(t) − ψ(t)‖ ≤ K/(1 − θ) e^{−γ(t − t₀)} ‖(1 − P)φ(t₀) − h(P φ(t₀))‖` for `t ≥ t₀`,
`θ = K δ ((1 + K L)/(γ − ε) + 1/(β − γ)) < 1`. -/
@[tmio T, powerlib_foundation] theorem exists_graph_phase (hP : IsCommutingProjection A P)
    (hεγ : ε < γ) (hγβ : γ < β) (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {g : E → E} {δ : NNReal} (hg : LipschitzWith δ g) {h : E → E} {L : NNReal}
    (hh : IsGraphMap P h) (hL : LipschitzWith L h)
    (hk : K * δ * ((1 + K * L) / (γ - ε) + 1 / (β - γ)) < 1)
    (hglob : ∀ u, ∃ X : ℝ → E, X 0 = P u + h u ∧ (∀ t, HasDerivAt X (A (X t) + g (X t)) t) ∧
      ∀ t, X t ∈ graph P h)
    {t₀ : ℝ} {φ : ℝ → E} (hφ : IsIntegralCurveOn φ (fun _ y => A y + g y) (Ici t₀)) :
    ∃ ψ : ℝ → E, (∀ t, HasDerivAt ψ (A (ψ t) + g (ψ t)) t) ∧ (∀ t, ψ t ∈ graph P h) ∧
      ∀ t, t₀ ≤ t → ‖φ t - ψ t‖ ≤ K / (1 - K * δ * ((1 + K * L) / (γ - ε) + 1 / (β - γ))) *
        Real.exp (-(γ * (t - t₀))) * ‖(1 - P) (φ t₀) - h (P (φ t₀))‖ := by
  obtain ⟨X, hX, hX0, hXb⟩ :=
    exists_phase_of_isIntegralCurveOn hP hεγ hγβ hcen hst hg hL hh.proj_apply hk hφ
  -- the graph solution through `X(t₀)`, shifted to start at `t₀`, is `X`
  obtain ⟨Y, hY0, hYd, hYg⟩ := hglob (P (X t₀))
  have hY0' : X t₀ = Y (t₀ - t₀) := by rw [sub_self, hY0, hP.idem]; exact hX0
  have hYc : IsIntegralCurveOn (fun t => Y (t - t₀)) (fun _ y => A y + g y) (Ici t₀) :=
    fun t _ => ((hYd (t - t₀)).comp_sub_const t t₀).hasDerivWithinAt
  have heq : ∀ t, t₀ ≤ t → X t = Y (t - t₀) := fun t ht =>
    eqOn_of_isIntegralCurveOn_Icc (K := ‖A‖₊ + δ) (fun _ => A.lipschitzWith.add hg)
      (hX.mono Icc_subset_Ici_self) (hYc.mono Icc_subset_Ici_self) hY0' ⟨ht, le_rfl⟩
  refine ⟨fun t => Y (t - t₀), fun t => (hYd (t - t₀)).comp_sub_const t t₀,
    fun t => hYg _, fun t ht => ?_⟩
  show ‖φ t - Y (t - t₀)‖ ≤ _
  rw [← heq t ht]
  exact hXb t ht

/-- **The graph map of the construction is Lipschitz with an explicit constant.** If through
every point `P u + h u` passes a solution of `ẋ = A x + g(x)` of growth `C₁ ‖P u‖ e^{η|t|}`
(`g` `δ`-Lipschitz, `g 0 = 0`, `K δ κ < 1`), then
`‖h u − h v‖ ≤ ‖1 − P‖ K/(1 − Kδκ) ‖P‖ ‖u − v‖` (fixed points of the Lyapunov–Perron transform
depend Lipschitz-continuously on their centre data, `norm_sub_fixedPoint_le`). -/
@[tmio T, powerlib_foundation] theorem lipschitzWith_of_globalSolutions
    (hP : IsCommutingProjection A P) {η : ℝ} (hε : 0 ≤ ε) (hεη : ε < η) (hηβ : η < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {g : E → E} {δ : NNReal} (hg : LipschitzWith δ g) (hg0 : g 0 = 0)
    (hk : K * δ * gapConst ε η β < 1) {h : E → E} (hh : IsGraphMap P h) {C₁ : ℝ}
    (hglob : ∀ u, ∃ x : ℝ → E, x 0 = P u + h u ∧ (∀ t, HasDerivAt x (A (x t) + g (x t)) t) ∧
      ∀ t, ‖x t‖ ≤ C₁ * ‖P u‖ * Real.exp (η * |t|)) :
    LipschitzWith (Real.toNNReal (‖1 - P‖ * (K / (1 - K * δ * gapConst ε η β)) * ‖P‖)) h := by
  have hη : 0 ≤ η := hε.trans hεη.le
  have hk1 : 0 < 1 - K * δ * gapConst ε η β := sub_pos.2 hk
  have hK := nonneg_of_stable_bound hst
  have hfix : ∀ u, ∃ x : ℝ → E, x 0 = P u + h u ∧ Continuous x ∧
      (∃ C, ∀ t, ‖x t‖ ≤ C * Real.exp (η * |t|)) ∧
      ∀ t, x t = lpMap A P (P u) (fun s => g (x s)) t := by
    intro u
    obtain ⟨x, hx0, hxd, hxb⟩ := hglob u
    have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hxd t).continuousAt
    have hC0 : 0 ≤ C₁ * ‖P u‖ := by
      have := (norm_nonneg _).trans (hxb 0); simpa using this
    refine ⟨x, hx0, hxc, ⟨_, hxb⟩, fun t => ?_⟩
    have hgx : ∀ s, ‖g (x s)‖ ≤ (δ * (C₁ * ‖P u‖)) * Real.exp (η * |s|) := fun s =>
      (hg.norm_le_mul hg0 _).trans (by rw [mul_assoc]; gcongr; exact hxb s)
    have := eq_lpMap_of_hasDerivAt hP.commute hη hηβ hst (hg.continuous.comp hxc)
      (mul_nonneg δ.coe_nonneg hC0) hgx hxb hxd t
    rw [this, ← hP.lpMap_proj, hx0, ← hh.comp_proj u, hh.proj_lift (hP.idem u)]
    rfl
  have hcomp : ∀ u, (1 - P) (P u + h u) = h u := fun u => by
    rw [compl_apply, map_add, hP.idem, hh.proj_apply]; abel
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  obtain ⟨x, hx0, hxc, ⟨Cx, hxb⟩, hx⟩ := hfix u
  obtain ⟨y, hy0, hyc, ⟨Cy, hyb⟩, hy⟩ := hfix v
  have h0 := norm_sub_fixedPoint_le hε hεη hηβ hcen hst hg hg0 hk hxc hyc hxb hyb hx hy 0
  simp only [abs_zero, mul_zero, Real.exp_zero, mul_one] at h0
  rw [hx0, hy0] at h0
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm]
  calc ‖h u - h v‖ = ‖(1 - P) ((P u + h u) - (P v + h v))‖ := by rw [map_sub, hcomp, hcomp]
    _ ≤ ‖1 - P‖ * ‖(P u + h u) - (P v + h v)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖1 - P‖ * (K * ‖P u - P v‖ / (1 - K * δ * gapConst ε η β)) := by gcongr
    _ ≤ ‖1 - P‖ * (K * (‖P‖ * ‖u - v‖) / (1 - K * δ * gapConst ε η β)) := by
        gcongr; rw [← map_sub]; exact P.le_opNorm _
    _ = _ := by ring

/-- **The centre manifold with its asymptotic phase.** The construction of
`exists_centerManifold_data` (weight `η ∈ (ε, β)`, Lipschitz bound `δ` with `Kδκ < 1`), for `δ`
also so small that `K δ ((1 + K L_δ)/(γ − ε) + 1/(β − γ)) < 1` with
`L_δ = ‖1 − P‖ K ‖P‖/(1 − Kδκ)` and a rate `γ ∈ (ε, β)`: besides the cutoff `g`, the graph map
`h` and its local invariance, every forward solution of the cutoff field `ẋ = A x + g(x)` has
an asymptotic phase on the graph, at the rate `γ`. -/
@[tmio T, powerlib_foundation] theorem exists_centerManifold_phase
    (hP : IsCommutingProjection A P) {η : ℝ} (hε : 0 ≤ ε) (hεη : ε < η) (hηβ : η < β)
    (hεγ : ε < γ) (hγβ : γ < β) (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {f : E → E} (hf0 : f 0 = 0) (hf : HasStrictFDerivAt f (0 : E →L[ℝ] E) 0) {δ : ℝ}
    (hδ : 0 < δ) (hk : K * δ * gapConst ε η β < 1)
    (hph : K * δ * ((1 + K * (‖1 - P‖ * (K / (1 - K * δ * gapConst ε η β)) * ‖P‖)) / (γ - ε) +
      1 / (β - γ)) < 1) :
    ∃ ρ > 0, ∃ g : E → E, LipschitzWith (Real.toNNReal δ) g ∧ g 0 = 0 ∧
      (∀ y, ‖y‖ ≤ ρ → g y = f y) ∧ ∃ h : E → E, ∃ L : NNReal, IsGraphMap P h ∧
      LipschitzWith L h ∧ IsLittleOrder P h 1 ∧
      (∀ (t₀ t₁ : ℝ) (φ : ℝ → E), IsIntegralCurveOn φ (fun _ y => fullField A f y) (Icc t₀ t₁) →
        φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h) ∧
      (∀ u, ∃ x : ℝ → E, x 0 = P u + h u ∧ (∀ t, HasDerivAt x (A (x t) + g (x t)) t) ∧
        (∀ t, x t ∈ graph P h) ∧
        ∀ t, ‖x t‖ ≤ K / (1 - K * δ * gapConst ε η β) * ‖P u‖ * Real.exp (η * |t|)) ∧
      ∃ C, 0 ≤ C ∧ ∀ (t₀ : ℝ) (φ : ℝ → E),
        IsIntegralCurveOn φ (fun _ y => A y + g y) (Ici t₀) →
        ∃ ψ : ℝ → E, (∀ t, HasDerivAt ψ (A (ψ t) + g (ψ t)) t) ∧ (∀ t, ψ t ∈ graph P h) ∧
          ∀ t, t₀ ≤ t → ‖φ t - ψ t‖ ≤ C * Real.exp (-(γ * (t - t₀))) *
            ‖(1 - P) (φ t₀) - h (P (φ t₀))‖ := by
  have hK := nonneg_of_stable_bound hst
  have hd1 : 0 < γ - ε := sub_pos.2 hεγ
  have hd2 : 0 < β - γ := sub_pos.2 hγβ
  have hk1 : 0 < 1 - K * δ * gapConst ε η β := sub_pos.2 hk
  obtain ⟨ρ, hρ, g, hg, hg0, hgf, h, L, hh, hL, htan, hinv, hglob⟩ :=
    exists_centerManifold_data hP hε hεη hηβ hcen hst hf0 hf hδ hk
  have hk' : K * (Real.toNNReal δ : ℝ) * gapConst ε η β < 1 := by
    rwa [Real.coe_toNNReal _ hδ.le]
  have hL' := lipschitzWith_of_globalSolutions hP hε hεη hηβ hcen hst hg hg0 hk' hh
    (C₁ := K / (1 - K * δ * gapConst ε η β)) fun u => by
      obtain ⟨x, hx0, hxd, -, hxb⟩ := hglob u
      exact ⟨x, hx0, hxd, hxb⟩
  set L' := Real.toNNReal (‖1 - P‖ * (K / (1 - K * (Real.toNNReal δ : ℝ) * gapConst ε η β)) *
    ‖P‖) with hL'def
  have hL'c : (L' : ℝ) = ‖1 - P‖ * (K / (1 - K * δ * gapConst ε η β)) * ‖P‖ := by
    rw [hL'def, Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ hδ.le]
  have hph' : K * (Real.toNNReal δ : ℝ) * ((1 + K * L') / (γ - ε) + 1 / (β - γ)) < 1 := by
    rwa [hL'c, Real.coe_toNNReal _ hδ.le]
  have hθ1 : 0 < 1 - K * (Real.toNNReal δ : ℝ) * ((1 + K * L') / (γ - ε) + 1 / (β - γ)) :=
    sub_pos.2 hph'
  refine ⟨ρ, hρ, g, hg, hg0, hgf, h, L, hh, hL, htan, hinv, hglob,
    K / (1 - K * (Real.toNNReal δ : ℝ) * ((1 + K * L') / (γ - ε) + 1 / (β - γ))),
    by positivity, fun t₀ φ hφ => ?_⟩
  exact exists_graph_phase hP hεγ hγβ hcen hst hg hh hL' hph'
    (fun u => by obtain ⟨x, hx0, hxd, hxg, -⟩ := hglob u; exact ⟨x, hx0, hxd, hxg⟩) hφ

omit [CompleteSpace E] in
/-- **A globally Lipschitz cutoff of a tangent graph map.** A graph map `h` with strict
derivative `0` at `0` agrees, where `‖P x‖ ≤ r`, with a globally Lipschitz graph map `h'`:
`h' = (1 − P) h₁ P` for a Lipschitz cutoff `h₁` of `h` (`exists_small_lipschitz_cutoff`). -/
@[tmio T, powerlib_foundation] theorem exists_lipschitz_graphMap_cutoff
    (hP : IsCommutingProjection A P) {h : E → E} (hh : IsGraphMap P h)
    (hhs : HasStrictFDerivAt h (0 : E →L[ℝ] E) 0) :
    ∃ r > 0, ∃ h' : E → E, ∃ L : NNReal, IsGraphMap P h' ∧ LipschitzWith L h' ∧
      ∀ x, ‖P x‖ ≤ r → h' x = h x := by
  obtain ⟨rh, hrh, h₁, hh₁, hh₁0, hh₁h, -⟩ := exists_small_lipschitz_cutoff hh.map_zero hhs one_pos
  set h' : E → E := fun x => (1 - P) (h₁ (P x)) with hh'def
  refine ⟨rh, hrh, h', _, ⟨fun x => by simp only [hh'def, hP.idem], fun x => hP.proj_compl _,
    by simp [hh'def, hh₁0]⟩, (1 - P).lipschitzWith.comp (hh₁.comp P.lipschitzWith),
    fun x hx => ?_⟩
  simp only [hh'def]
  rw [hh₁h _ hx, hh.comp_proj, compl_apply, hh.proj_apply, sub_zero]

/-- **Asymptotic phase towards any tangent graph.** Under the dichotomy with `0 ≤ ε < β`, for `f`
with `f(0) = 0` and strict derivative `0` at `0`, and for every graph map `h` with strict
derivative `0` at `0` (for instance `C¹` near `0` with `Dh(0) = 0`; no invariance is used here):
there are a radius `r > 0`, a globally Lipschitz `g` equal to `f` on the ball of radius `r`, a
globally Lipschitz graph map `h'` equal to `h` where `‖P x‖ ≤ r`, and constants `C ≥ 0`, `γ > 0`
such that every forward solution of `ẋ = A x + g(x)` from `t₀` has a forward solution of the same
field starting on the graph of `h'` within `C e^{−γ(t − t₀)} ‖(1 − P)φ(t₀) − h'(P φ(t₀))‖`
(`exists_phase_of_isIntegralCurveOn` with the cutoff of `f` from `exists_small_lipschitz_cutoff`
and that of `h` from `exists_lipschitz_graphMap_cutoff`). -/
@[tmio T, powerlib_foundation] theorem exists_tangentGraph_phase
    (hP : IsCommutingProjection A P) (hε : 0 ≤ ε) (hεβ : ε < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {f : E → E} (hf0 : f 0 = 0) (hf : HasStrictFDerivAt f (0 : E →L[ℝ] E) 0) {h : E → E}
    (hh : IsGraphMap P h) (hhs : HasStrictFDerivAt h (0 : E →L[ℝ] E) 0) :
    ∃ r > 0, ∃ g : E → E, ∃ δ : NNReal, LipschitzWith δ g ∧ (∀ y, ‖y‖ ≤ r → g y = f y) ∧
      ∃ h' : E → E, ∃ L : NNReal, IsGraphMap P h' ∧ LipschitzWith L h' ∧
      (∀ x, ‖P x‖ ≤ r → h' x = h x) ∧ ∃ C γ : ℝ, 0 ≤ C ∧ 0 < γ ∧
      ∀ (t₀ : ℝ) (φ : ℝ → E), IsIntegralCurveOn φ (fun _ y => A y + g y) (Ici t₀) →
        ∃ X : ℝ → E, IsIntegralCurveOn X (fun _ y => A y + g y) (Ici t₀) ∧ X t₀ ∈ graph P h' ∧
          ∀ t, t₀ ≤ t → ‖φ t - X t‖ ≤ C * Real.exp (-(γ * (t - t₀))) *
            ‖(1 - P) (φ t₀) - h' (P (φ t₀))‖ := by
  have hK := nonneg_of_stable_bound hst
  -- a globally Lipschitz graph map equal to `h` near `0`
  obtain ⟨rh, hrh, h', L, hh', hL', hh'h⟩ := exists_lipschitz_graphMap_cutoff hP hh hhs
  -- the rate and the Lipschitz bound of the cutoff of `f`
  set γ := (ε + β) / 2 with hγdef
  have hεγ : ε < γ := by rw [hγdef]; linarith
  have hγβ : γ < β := by rw [hγdef]; linarith
  have hd1 : 0 < γ - ε := sub_pos.2 hεγ
  have hd2 : 0 < β - γ := sub_pos.2 hγβ
  set Y := K * ((1 + K * L) / (γ - ε) + 1 / (β - γ)) with hYdef
  have hY0 : 0 ≤ Y := by positivity
  set δ : ℝ := 1 / (2 * (Y + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hk : K * (Real.toNNReal δ : ℝ) * ((1 + K * L) / (γ - ε) + 1 / (β - γ)) < 1 := by
    rw [Real.coe_toNNReal _ hδ.le]
    have e : K * δ * ((1 + K * L) / (γ - ε) + 1 / (β - γ)) = δ * Y := by rw [hYdef]; ring
    rw [e, hδdef, show 1 / (2 * (Y + 1)) * Y = Y / (2 * (Y + 1)) by ring,
      div_lt_one (by positivity)]
    linarith
  have hk1 : 0 < 1 - K * (Real.toNNReal δ : ℝ) * ((1 + K * L) / (γ - ε) + 1 / (β - γ)) :=
    sub_pos.2 hk
  obtain ⟨rf, hrf, g, hg, -, hgf, -⟩ := exists_small_lipschitz_cutoff hf0 hf hδ
  refine ⟨min rf rh, lt_min hrf hrh, g, _, hg, fun y hy => hgf y (hy.trans (min_le_left _ _)),
    h', L, hh', hL', fun x hx => hh'h x (hx.trans (min_le_right _ _)),
    K / (1 - K * (Real.toNNReal δ : ℝ) * ((1 + K * L) / (γ - ε) + 1 / (β - γ))), γ,
    by positivity, by linarith, fun t₀ φ hφ => ?_⟩
  obtain ⟨X, hX, hX0, hXb⟩ :=
    exists_phase_of_isIntegralCurveOn hP hεγ hγβ hcen hst hg hL' hh'.proj_apply hk hφ
  refine ⟨X, hX, ?_, hXb⟩
  show X t₀ = P (X t₀) + h' (X t₀)
  rw [← hh'.comp_proj]; exact hX0

end Graph

end powerlib.Dynamics.CenterManifold
