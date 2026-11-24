import theorem.Dynamics.CenterManifoldPhase
import theorem.Dynamics.CenterReduction

/-! # The reduction principle: stability (foundation)

The stability half of the reduction principle (Pliss; Carr, Theorem 2): for `ẋ = A x + f(x)` on
`ℝⁿ` with a centre–stable dichotomy, the constructed centre manifold attracts every small
solution with an asymptotic phase, and Lyapunov stability or local asymptotic stability of the
reduced field at `0` is that of the full field. With the planar weak-focus law and the
projection-formula bridge, `ℓ₁ < 0` gives local asymptotic stability in any dimension.

Scope.
* Generic: `State n = ℝⁿ`, `A`, `P` with `P² = P`, `AP = PA` (`IsCommutingProjection`), the
  dichotomy `‖e^{tA}P‖ ≤ K e^{ε|t|}` (all `t`), `‖e^{tA}(1 − P)‖ ≤ K e^{−βt}` (`t ≥ 0`) as theorem
  hypotheses, with the gap `qε < β` (`q ≥ 1`; `q = 1` is `ε < β`, `q = 3` serves the cubic laws),
  `f` of class `C¹` with `f(0) = 0`, `Df(0) = 0`. The reduced field is read in linear
  coordinates `ι`, `π` of `range P` (`IsChart`, `chartField`); stability notions are
  LeanForControl's (`LyapunovStable`, `LocalAsymptoticStable` on `ℝᵐ`).
* Two forms of the transfer. (i) For any centre manifold (Carr's Theorem 2 in its generality):
  any graph map `h` with strict derivative `0` at `0` (for instance `C¹` near `0` with
  `Dh(0) = 0`) whose graph is locally invariant (`lyapunovStable_of_invariantGraph`,
  `localAsymptoticStable_of_invariantGraph`, `exists_phase_of_invariantGraph`); here `f` has
  `f(0) = 0` and strict derivative `0` at `0`. (ii) With the cutoff field `g` and the asymptotic
  phase of its forward solutions on the whole graph as hypotheses (`lyapunovStable_of_chartField`,
  `localAsymptoticStable_of_chartField`, `exists_phase_of_cutoff`, the form supplied by
  `exists_centerManifold_phase`, `theorem/Dynamics/CenterManifoldPhase.lean`): no
  differentiability of `h`, which serves the merely Lipschitz constructed manifold of
  `exists_centerManifold_stable`. Neither form uses uniqueness of centre manifolds.
* Nothing here describes a physical system (foundation).

Source: Carr, *Applications of Centre Manifold Theory* (1981), §2.4, Theorem 2 and Lemma 1;
Pliss, "A reduction principle in the theory of stability of motion" (1964); Kelley (1967);
Vanderbauwhede, "Centre manifolds, normal forms and elementary bifurcations" (1989), §2;
Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §5.1 (Theorem 5.2), §5.4.

Results.
* Tools: `IsChart.isIntegralCurveOn_π_of_mem`, `IsChart.isIntegralCurveOn_π` (on the graph and
  in the ball, `π` of a cutoff solution is a chart-field solution),
  `IsChart.norm_le_of_mem_graph` (`‖x‖ ≤ (1 + L)‖ι‖‖π x‖` on the graph),
  `norm_graphDist_le` (`‖(1 − P)x − h(P x)‖ ≤ (‖1 − P‖ + L‖P‖)‖x‖`),
  `forall_norm_lt_of_lyapunovStable_chartField` (graph solutions starting small stay small).
* (1) Attraction with asymptotic phase: `exists_phase_of_cutoff` — solutions of
  `ẋ = A x + f(x)` staying in a small ball for `t ≥ t₀` have a solution `ψ` on the centre
  manifold, in the ball of radius `ρ`, with `‖φ(t) − ψ(t)‖ ≤ C e^{−γ(t−t₀)} ‖(1 − P)φ(t₀) −
  h(P φ(t₀))‖`.
* (2) Stability transfer: `lyapunovStable_of_chartField`, `localAsymptoticStable_of_chartField`.
* Carr's Theorem 2 for any tangent locally invariant graph: `lyapunovStable_of_invariantGraph`,
  `localAsymptoticStable_of_invariantGraph`, `exists_phase_of_invariantGraph` (the asymptotic
  phase on that graph), with `forall_mem_graph_of_lyapunovStable_chartField` (solutions on the
  graph starting small stay small and on the graph). The proof does not pass through the ODE of
  the deviation `z = (1 − P)x − h(P x)`: the Lyapunov–Perron contraction of
  `exists_phase_of_isIntegralCurveOn` towards a Lipschitz cutoff of `h`, followed by local
  invariance, gives the phase directly.
* The theorem: `exists_centerManifold_stable` — under the dichotomy with `qε < β`, a centre
  manifold with local invariance, Carr's approximation property of order `q`, the asymptotic
  phase (1), and the transfers (2) for every chart of `range P`.
* (3) `localAsymptoticStable_of_dichotomy_reduced_l1_neg` (planar `l₁ < 0` of the reduced linear,
  quadratic and cubic parts) and `localAsymptoticStable_of_firstLyapunov_neg` (Kuznetsov's
  projection formula, `ℓ₁ < 0`): local asymptotic stability of the full field in any dimension,
  the counterparts of `unstable_of_dichotomy_reduced_l1_pos`, `unstable_of_firstLyapunov_pos`.
-/

noncomputable section
namespace powerlib.Dynamics.CenterManifold

open Set Filter Topology Metric

/-! ## Tools -/

section Tools

variable {n m : ℕ} {A P : State n →L[ℝ] State n} {f h g : State n → State n}
  {ι : State m →L[ℝ] State n} {π : State n →L[ℝ] State m} {L : NNReal} {ρ : ℝ}

/-- On a set of times where a solution of the cutoff field stays on the graph and in the ball of
radius `ρ` where `g = f`, `π` carries it to a solution of the chart field. -/
@[tmio T, powerlib_foundation] theorem IsChart.isIntegralCurveOn_π_of_mem
    (hP : IsCommutingProjection A P) (hh : IsGraphMap P h) (hc : IsChart P ι π)
    (hgf : ∀ y, ‖y‖ ≤ ρ → g y = f y) {ψ : ℝ → State n} {s : Set ℝ}
    (hψ : IsIntegralCurveOn ψ (fun _ y => A y + g y) s)
    (hs : ∀ t ∈ s, ‖ψ t‖ ≤ ρ ∧ ψ t ∈ graph P h) :
    IsIntegralCurveOn (fun t => π (ψ t)) (fun _ y => chartField A f h ι π y) s := by
  intro t ht
  have h1 := π.hasFDerivAt.comp_hasDerivWithinAt t (hψ t ht)
  have h2 : π (A (ψ t) + g (ψ t)) = chartField A f h ι π (π (ψ t)) := by
    rw [hgf _ (hs t ht).1]; exact hc.π_fullField_of_mem_graph hP hh (hs t ht).2
  simpa only [Function.comp_def, h2] using h1

/-- In the ball of radius `ρ` where `g = f`, `π` carries a solution of the cutoff field on the
graph to a solution of the chart field. -/
@[tmio T, powerlib_foundation] theorem IsChart.isIntegralCurveOn_π
    (hP : IsCommutingProjection A P) (hh : IsGraphMap P h) (hc : IsChart P ι π)
    (hgf : ∀ y, ‖y‖ ≤ ρ → g y = f y) {ψ : ℝ → State n}
    (hψd : ∀ t, HasDerivAt ψ (A (ψ t) + g (ψ t)) t) (hψg : ∀ t, ψ t ∈ graph P h)
    {s : Set ℝ} (hs : ∀ t ∈ s, ‖ψ t‖ ≤ ρ) :
    IsIntegralCurveOn (fun t => π (ψ t)) (fun _ y => chartField A f h ι π y) s :=
  hc.isIntegralCurveOn_π_of_mem hP hh hgf (fun t _ => (hψd t).hasDerivWithinAt)
    fun t ht => ⟨hs t ht, hψg t⟩

/-- On the graph of an `L`-Lipschitz graph map, `‖x‖ ≤ (1 + L) ‖ι‖ ‖π x‖`. -/
@[tmio T, powerlib_foundation] theorem IsChart.norm_le_of_mem_graph (hh : IsGraphMap P h)
    (hL : LipschitzWith L h) (hc : IsChart P ι π) {x : State n} (hx : x ∈ graph P h) :
    ‖x‖ ≤ (1 + L) * ‖ι‖ * ‖π x‖ := by
  have hx' : x = ι (π x) + h (ι (π x)) := by rw [hc.ι_π, hh.comp_proj]; exact hx
  calc ‖x‖ = ‖ι (π x) + h (ι (π x))‖ := congrArg _ hx'
    _ ≤ (1 + L) * ‖ι (π x)‖ := hh.norm_lift_le hL _
    _ ≤ (1 + L) * (‖ι‖ * ‖π x‖) := by gcongr; exact ι.le_opNorm _
    _ = _ := by ring

/-- The distance to the graph: `‖(1 − P)x − h(P x)‖ ≤ (‖1 − P‖ + L ‖P‖) ‖x‖`. -/
@[tmio T, powerlib_foundation] theorem norm_graphDist_le (hh : IsGraphMap P h)
    (hL : LipschitzWith L h) (x : State n) :
    ‖(1 - P) x - h (P x)‖ ≤ (‖1 - P‖ + L * ‖P‖) * ‖x‖ := by
  have h1 : ‖h (P x)‖ ≤ L * ‖P x‖ := by simpa [hh.map_zero] using hL.norm_sub_le (P x) 0
  calc _ ≤ ‖(1 - P) x‖ + ‖h (P x)‖ := norm_sub_le _ _
    _ ≤ ‖1 - P‖ * ‖x‖ + L * (‖P‖ * ‖x‖) :=
        add_le_add ((1 - P).le_opNorm x) (h1.trans (by gcongr; exact P.le_opNorm x))
    _ = _ := by ring

/-- **Graph solutions starting small stay small.** If the chart field is Lyapunov stable at `0`,
solutions of the cutoff field (`g = f` on the ball of radius `ρ`) on the graph that start close
enough to `0` stay in any prescribed ball for all later times. -/
@[tmio T, powerlib_foundation] theorem forall_norm_lt_of_lyapunovStable_chartField
    (hP : IsCommutingProjection A P) (hh : IsGraphMap P h) (hL : LipschitzWith L h)
    (hc : IsChart P ι π) (hρ : 0 < ρ) (hgf : ∀ y, ‖y‖ ≤ ρ → g y = f y)
    (hLS : LyapunovStable (chartField A f h ι π) 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ (t₀ : ℝ) (ψ : ℝ → State n), (∀ t, HasDerivAt ψ (A (ψ t) + g (ψ t)) t) →
      (∀ t, ψ t ∈ graph P h) → ‖ψ t₀‖ < d → ∀ t, t₀ ≤ t → ‖ψ t‖ < ε := by
  set ε' := min ε ρ with hε'
  have hε'0 : 0 < ε' := lt_min hε hρ
  set εr := ε' / (2 * ((1 + L) * (‖ι‖ + 1))) with hεr
  have hεr0 : 0 < εr := by positivity
  obtain ⟨dr, hdr, hLSr⟩ := hLS εr hεr0
  refine ⟨min (dr / (‖π‖ + 1)) ε', by positivity, fun t₀ ψ hψd hψg hψ0 t ht => ?_⟩
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun t => (hψd t).continuousAt
  have hstay : ∀ τ ∈ Icc t₀ t, ‖ψ τ - 0‖ < ε' := by
    refine forall_norm_sub_lt_of_bootstrap hψc.continuousOn
      (by rw [sub_zero]; exact hψ0.trans_le (min_le_right _ _)) fun s hs hin => ?_
    have hcurve := hc.isIntegralCurveOn_π hP hh hgf hψd hψg (s := Icc t₀ s) fun τ hτ => by
      have := hin τ hτ; rw [sub_zero] at this; exact this.le.trans (min_le_right _ _)
    have hπ0 : ‖π (ψ t₀) - 0‖ < dr := by
      rw [sub_zero]
      calc ‖π (ψ t₀)‖ ≤ ‖π‖ * ‖ψ t₀‖ := π.le_opNorm _
        _ ≤ (‖π‖ + 1) * ‖ψ t₀‖ := by nlinarith [norm_nonneg (ψ t₀)]
        _ < (‖π‖ + 1) * (dr / (‖π‖ + 1)) := by
            gcongr; exact hψ0.trans_le (min_le_left _ _)
        _ = dr := by field_simp
    have hπs := hLSr t₀ s (fun τ => π (ψ τ)) hcurve hπ0 s ⟨hs.1, le_rfl⟩
    rw [sub_zero] at hπs ⊢
    calc ‖ψ s‖ ≤ (1 + L) * ‖ι‖ * ‖π (ψ s)‖ := hc.norm_le_of_mem_graph hh hL (hψg s)
      _ ≤ (1 + L) * (‖ι‖ + 1) * εr :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hπs.le
            (norm_nonneg _) (by positivity)
      _ = ε' / 2 := by rw [hεr]; field_simp
  have := hstay t ⟨ht, le_rfl⟩
  rw [sub_zero] at this
  exact this.trans_le (min_le_left _ _)

end Tools

/-! ## (1) Asymptotic phase and (2) stability transfer -/

section Transfer

variable {n m : ℕ} {A P : State n →L[ℝ] State n} {f h g : State n → State n}
  {ι : State m →L[ℝ] State n} {π : State n →L[ℝ] State m} {L δ : NNReal} {ρ C γ : ℝ}

/-- **Attraction with asymptotic phase** (Carr, Lemma 1 and Theorem 2). Let `g` be globally
Lipschitz with `g = f` on the ball of radius `ρ`, and let every forward solution of
`ẋ = A x + g(x)` have an asymptotic phase on the graph of `h` at the rate `γ` with the constant
`C`. Then there is `r > 0` such that every solution `φ` of `ẋ = A x + f(x)` that stays in the
ball of radius `r` for `t ≥ t₀` has a solution `ψ` of `ẋ = A x + f(x)` on the graph, in the
ball of radius `ρ`, with `‖φ(t) − ψ(t)‖ ≤ C e^{−γ(t−t₀)} ‖(1 − P)φ(t₀) − h(P φ(t₀))‖`. -/
@[tmio T, powerlib_foundation] theorem exists_phase_of_cutoff (hh : IsGraphMap P h)
    (hL : LipschitzWith L h) (hρ : 0 < ρ) (hgf : ∀ y, ‖y‖ ≤ ρ → g y = f y) (hC : 0 ≤ C)
    (hγ : 0 ≤ γ)
    (hphase : ∀ (t₀ : ℝ) (φ : ℝ → State n), IsIntegralCurveOn φ (fun _ y => A y + g y) (Ici t₀) →
      ∃ ψ : ℝ → State n, (∀ t, HasDerivAt ψ (A (ψ t) + g (ψ t)) t) ∧ (∀ t, ψ t ∈ graph P h) ∧
        ∀ t, t₀ ≤ t → ‖φ t - ψ t‖ ≤ C * Real.exp (-(γ * (t - t₀))) *
          ‖(1 - P) (φ t₀) - h (P (φ t₀))‖) :
    ∃ r > 0, ∀ (t₀ : ℝ) (φ : ℝ → State n),
      IsIntegralCurveOn φ (fun _ y => fullField A f y) (Ici t₀) → (∀ t, t₀ ≤ t → ‖φ t‖ < r) →
      ∃ ψ : ℝ → State n, IsIntegralCurveOn ψ (fun _ y => fullField A f y) (Ici t₀) ∧
        (∀ t, t₀ ≤ t → ψ t ∈ graph P h ∧ ‖ψ t‖ < ρ) ∧
        ∀ t, t₀ ≤ t → ‖φ t - ψ t‖ ≤ C * Real.exp (-(γ * (t - t₀))) *
          ‖(1 - P) (φ t₀) - h (P (φ t₀))‖ := by
  set Cz := ‖1 - P‖ + L * ‖P‖ with hCz
  have hCz0 : 0 ≤ Cz := by positivity
  have hD : 1 ≤ 1 + C * Cz := by nlinarith [mul_nonneg hC hCz0]
  refine ⟨ρ / (2 * (1 + C * Cz)), by positivity, fun t₀ φ hφ hφr => ?_⟩
  have hrρ : ρ / (2 * (1 + C * Cz)) ≤ ρ / 2 :=
    div_le_div_of_nonneg_left hρ.le (by positivity) (by linarith)
  have hφg : IsIntegralCurveOn φ (fun _ y => A y + g y) (Ici t₀) :=
    isIntegralCurveOn_of_eq_on_curve (f := fun y => A y + g y) hφ fun t ht => by
      show A (φ t) + f (φ t) = A (φ t) + g (φ t)
      rw [hgf _ ((hφr t ht).le.trans (by linarith))]
  obtain ⟨ψ, hψd, hψg, hψb⟩ := hphase t₀ φ hφg
  have hψρ : ∀ t, t₀ ≤ t → ‖ψ t‖ < ρ := by
    intro t ht
    have hz := norm_graphDist_le hh hL (φ t₀)
    have he : Real.exp (-(γ * (t - t₀))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [sub_nonneg.2 ht])
    have hd : ‖φ t - ψ t‖ ≤ C * Cz * (ρ / (2 * (1 + C * Cz))) := by
      refine (hψb t ht).trans ?_
      calc C * Real.exp (-(γ * (t - t₀))) * ‖(1 - P) (φ t₀) - h (P (φ t₀))‖
          ≤ C * 1 * (Cz * ‖φ t₀‖) := by gcongr
        _ ≤ C * 1 * (Cz * (ρ / (2 * (1 + C * Cz)))) := by
            gcongr; exact (hφr t₀ le_rfl).le
        _ = _ := by ring
    have e : (1 + C * Cz) * (ρ / (2 * (1 + C * Cz))) = ρ / 2 := by field_simp
    calc ‖ψ t‖ ≤ ‖φ t‖ + ‖φ t - ψ t‖ := by
          have := norm_sub_le (φ t) (φ t - ψ t); rwa [sub_sub_cancel] at this
      _ < ρ / (2 * (1 + C * Cz)) + C * Cz * (ρ / (2 * (1 + C * Cz))) :=
          add_lt_add_of_lt_of_le (hφr t ht) hd
      _ = ρ / 2 := by rw [← e]; ring
      _ < ρ := by linarith
  refine ⟨ψ, fun t ht => ?_, fun t ht => ⟨hψg t, hψρ t ht⟩, hψb⟩
  have h1 := (hψd t).hasDerivWithinAt (s := Ici t₀)
  rw [hgf _ (hψρ t ht).le] at h1
  exact h1

/-- **Lyapunov stability transfers from the reduced field** (Carr, Theorem 2 (a); Pliss). With
the cutoff `g` (`δ`-Lipschitz, `g = f` on the ball of radius `ρ`) and the asymptotic phase of its
forward solutions on the graph of the `L`-Lipschitz graph map `h` (constant `C ≥ 0`, rate
`γ ≥ 0`): if the chart field is Lyapunov stable at `0`, so is the full field. -/
@[tmio T, powerlib_foundation] theorem lyapunovStable_of_chartField
    (hP : IsCommutingProjection A P) (hh : IsGraphMap P h) (hL : LipschitzWith L h)
    (hc : IsChart P ι π) (hρ : 0 < ρ) (hg : LipschitzWith δ g)
    (hgf : ∀ y, ‖y‖ ≤ ρ → g y = f y) (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (hphase : ∀ (t₀ : ℝ) (φ : ℝ → State n), IsIntegralCurveOn φ (fun _ y => A y + g y) (Ici t₀) →
      ∃ ψ : ℝ → State n, (∀ t, HasDerivAt ψ (A (ψ t) + g (ψ t)) t) ∧ (∀ t, ψ t ∈ graph P h) ∧
        ∀ t, t₀ ≤ t → ‖φ t - ψ t‖ ≤ C * Real.exp (-(γ * (t - t₀))) *
          ‖(1 - P) (φ t₀) - h (P (φ t₀))‖)
    (hLS : LyapunovStable (chartField A f h ι π) 0) : LyapunovStable (fullField A f) 0 := by
  intro ε hε
  set ε' := min ε ρ with hε'
  have hε'0 : 0 < ε' := lt_min hε hρ
  obtain ⟨d₁, hd₁, hstay⟩ :=
    forall_norm_lt_of_lyapunovStable_chartField hP hh hL hc hρ hgf hLS (ε := ε' / 4)
      (by positivity)
  set Cz := ‖1 - P‖ + L * ‖P‖ with hCz
  have hCz0 : 0 ≤ Cz := by positivity
  have hD : 0 < 1 + C * Cz := by positivity
  refine ⟨min d₁ (ε' / 4) / (1 + C * Cz), by positivity, fun t₀ t₁ φ hφ hφ0 => ?_⟩
  rw [sub_zero] at hφ0
  have hφ0' : (1 + C * Cz) * ‖φ t₀‖ < min d₁ (ε' / 4) := by
    rwa [lt_div_iff₀ hD, mul_comm] at hφ0
  have hφ1 : ‖φ t₀‖ ≤ (1 + C * Cz) * ‖φ t₀‖ := by nlinarith [norm_nonneg (φ t₀), mul_nonneg hC hCz0]
  have hlip : LipschitzWith (‖A‖₊ + δ) (fun y => A y + g y) := A.lipschitzWith.add hg
  obtain ⟨x, hx0, hx⟩ := Flow.forwardComplete_of_lipschitzWith hlip t₀ (φ t₀)
  obtain ⟨ψ, hψd, hψg, hψb⟩ := hphase t₀ x hx
  have hdiff : ∀ t, t₀ ≤ t → ‖x t - ψ t‖ ≤ C * Cz * ‖φ t₀‖ := fun t ht => by
    refine (hψb t ht).trans ?_
    have he : Real.exp (-(γ * (t - t₀))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [sub_nonneg.2 ht])
    have hz := norm_graphDist_le hh hL (x t₀)
    rw [hx0] at hz
    calc C * Real.exp (-(γ * (t - t₀))) * ‖(1 - P) (x t₀) - h (P (x t₀))‖
        ≤ C * 1 * (Cz * ‖φ t₀‖) := by rw [hx0]; gcongr
      _ = C * Cz * ‖φ t₀‖ := by ring
  have hψ0 : ‖ψ t₀‖ < d₁ := by
    calc ‖ψ t₀‖ ≤ ‖x t₀‖ + ‖x t₀ - ψ t₀‖ := by
          have := norm_sub_le (x t₀) (x t₀ - ψ t₀); rwa [sub_sub_cancel] at this
      _ ≤ ‖φ t₀‖ + C * Cz * ‖φ t₀‖ := add_le_add (le_of_eq (by rw [hx0])) (hdiff t₀ le_rfl)
      _ = (1 + C * Cz) * ‖φ t₀‖ := by ring
      _ < min d₁ (ε' / 4) := hφ0'
      _ ≤ d₁ := min_le_left _ _
  have hψs := hstay t₀ ψ hψd hψg hψ0
  have hCzφ : C * Cz * ‖φ t₀‖ < ε' / 4 := by
    have : C * Cz * ‖φ t₀‖ ≤ (1 + C * Cz) * ‖φ t₀‖ := by nlinarith [norm_nonneg (φ t₀)]
    linarith [min_le_right d₁ (ε' / 4)]
  have hxs : ∀ t, t₀ ≤ t → ‖x t‖ < ε' / 2 := fun t ht => by
    calc ‖x t‖ ≤ ‖ψ t‖ + ‖x t - ψ t‖ := by
          have := norm_add_le (ψ t) (x t - ψ t); rwa [add_sub_cancel] at this
      _ < ε' / 4 + ε' / 4 := add_lt_add_of_lt_of_le (hψs t ht) ((hdiff t ht).trans hCzφ.le)
      _ = ε' / 2 := by ring
  -- the segment `φ` is the cutoff solution `x` while it stays in the ball
  have hφx : ∀ t ∈ Icc t₀ t₁, ‖φ t - 0‖ < ε' := by
    refine forall_norm_sub_lt_of_bootstrap hφ.continuousOn
      (by rw [sub_zero]; linarith [min_le_right d₁ (ε' / 4)]) fun s hs hin => ?_
    have hφg : IsIntegralCurveOn φ (fun _ y => A y + g y) (Icc t₀ s) :=
      isIntegralCurveOn_of_eq_on_curve (f := fun y => A y + g y)
        (hφ.mono (Icc_subset_Icc le_rfl hs.2)) fun τ hτ => by
          have := hin τ hτ; rw [sub_zero] at this
          show A (φ τ) + f (φ τ) = A (φ τ) + g (φ τ)
          rw [hgf _ (this.le.trans (min_le_right _ _))]
    have heq := eqOn_of_isIntegralCurveOn_Icc (K := ‖A‖₊ + δ) (fun _ => hlip) hφg
      (hx.mono Icc_subset_Ici_self) hx0.symm ⟨hs.1, le_rfl⟩
    rw [sub_zero, heq]
    exact (hxs s hs.1).le
  intro t ht
  exact (hφx t ht).trans_le (min_le_left _ _)

/-- **Local asymptotic stability transfers from the reduced field** (Carr, Theorem 2 (b);
Pliss). Under the hypotheses of `lyapunovStable_of_chartField` with a positive rate `γ`: if the
chart field is locally asymptotically stable at `0`, so is the full field (a solution starting
close to `0` stays in the ball, is a solution of the cutoff field, tends to its asymptotic phase,
and the phase is a solution of the reduced field). -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_chartField
    (hP : IsCommutingProjection A P) (hh : IsGraphMap P h) (hL : LipschitzWith L h)
    (hc : IsChart P ι π) (hρ : 0 < ρ) (hg : LipschitzWith δ g)
    (hgf : ∀ y, ‖y‖ ≤ ρ → g y = f y) (hC : 0 ≤ C) (hγ : 0 < γ)
    (hphase : ∀ (t₀ : ℝ) (φ : ℝ → State n), IsIntegralCurveOn φ (fun _ y => A y + g y) (Ici t₀) →
      ∃ ψ : ℝ → State n, (∀ t, HasDerivAt ψ (A (ψ t) + g (ψ t)) t) ∧ (∀ t, ψ t ∈ graph P h) ∧
        ∀ t, t₀ ≤ t → ‖φ t - ψ t‖ ≤ C * Real.exp (-(γ * (t - t₀))) *
          ‖(1 - P) (φ t₀) - h (P (φ t₀))‖)
    (hLAS : LocalAsymptoticStable (chartField A f h ι π) 0) :
    LocalAsymptoticStable (fullField A f) 0 := by
  obtain ⟨hLSr, cr, hcr, hattr⟩ := hLAS
  have hLS := lyapunovStable_of_chartField hP hh hL hc hρ hg hgf hC hγ.le hphase hLSr
  refine ⟨hLS, ?_⟩
  obtain ⟨d₀, hd₀, hLS₀⟩ := hLS ρ hρ
  obtain ⟨d₂, hd₂, hstay⟩ :=
    forall_norm_lt_of_lyapunovStable_chartField hP hh hL hc hρ hgf hLSr hρ
  set Cz := ‖1 - P‖ + L * ‖P‖ with hCz
  have hCz0 : 0 ≤ Cz := by positivity
  have hD : 0 < 1 + C * Cz := by positivity
  set c₀ := min d₀ (min d₂ (cr / (‖π‖ + 1))) with hc₀
  have hc₀0 : 0 < c₀ := lt_min hd₀ (lt_min hd₂ (by positivity))
  refine ⟨c₀ / (1 + C * Cz), by positivity, fun t₀ φ hφ hφ0 => ?_⟩
  rw [sub_zero] at hφ0
  have hφ0' : (1 + C * Cz) * ‖φ t₀‖ < c₀ := by
    rwa [lt_div_iff₀ hD, mul_comm] at hφ0
  have hφ1 : ‖φ t₀‖ ≤ (1 + C * Cz) * ‖φ t₀‖ := by
    nlinarith [norm_nonneg (φ t₀), mul_nonneg hC hCz0]
  -- the solution stays in the ball of radius `ρ`, hence solves the cutoff field
  have hφρ : ∀ t, t₀ ≤ t → ‖φ t‖ < ρ := fun t ht => by
    have := hLS₀ t₀ t φ (hφ.mono Icc_subset_Ici_self)
      (by rw [sub_zero]; linarith [min_le_left d₀ (min d₂ (cr / (‖π‖ + 1)))]) t ⟨ht, le_rfl⟩
    rwa [sub_zero] at this
  have hφg : IsIntegralCurveOn φ (fun _ y => A y + g y) (Ici t₀) :=
    isIntegralCurveOn_of_eq_on_curve (f := fun y => A y + g y) hφ fun t ht => by
      show A (φ t) + f (φ t) = A (φ t) + g (φ t)
      rw [hgf _ (hφρ t ht).le]
  obtain ⟨ψ, hψd, hψg, hψb⟩ := hphase t₀ φ hφg
  have hψ0 : ‖ψ t₀‖ ≤ (1 + C * Cz) * ‖φ t₀‖ := by
    have h1 := hψb t₀ le_rfl
    rw [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one] at h1
    have hz := norm_graphDist_le hh hL (φ t₀)
    calc ‖ψ t₀‖ ≤ ‖φ t₀‖ + ‖φ t₀ - ψ t₀‖ := by
          have := norm_sub_le (φ t₀) (φ t₀ - ψ t₀); rwa [sub_sub_cancel] at this
      _ ≤ ‖φ t₀‖ + C * (Cz * ‖φ t₀‖) := by gcongr; exact h1.trans (by gcongr)
      _ = (1 + C * Cz) * ‖φ t₀‖ := by ring
  have hψc₀ : ‖ψ t₀‖ < c₀ := hψ0.trans_lt hφ0'
  -- the asymptotic phase is a reduced solution starting close to `0`
  have hψρ := hstay t₀ ψ hψd hψg
    (hψc₀.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hcurve := hc.isIntegralCurveOn_π hP hh hgf hψd hψg (s := Ici t₀) fun t ht =>
    (hψρ t ht).le
  have hπ0 : ‖π (ψ t₀) - 0‖ < cr := by
    rw [sub_zero]
    have hlt : ‖ψ t₀‖ < cr / (‖π‖ + 1) :=
      hψc₀.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    calc ‖π (ψ t₀)‖ ≤ ‖π‖ * ‖ψ t₀‖ := π.le_opNorm _
      _ ≤ (‖π‖ + 1) * ‖ψ t₀‖ := by nlinarith [norm_nonneg (ψ t₀)]
      _ < (‖π‖ + 1) * (cr / (‖π‖ + 1)) := by gcongr
      _ = cr := by field_simp
  have hlim := hattr t₀ (fun t => π (ψ t)) hcurve hπ0
  -- hence the phase tends to `0`
  have hψlim : Tendsto ψ atTop (𝓝 0) := by
    have hι := (ι.continuous.tendsto 0).comp hlim
    have hh0 := (hL.continuous.tendsto _).comp hι
    have hsum := hι.add hh0
    rw [map_zero, hh.map_zero, add_zero] at hsum
    refine hsum.congr fun t => ?_
    simp only [Function.comp_def]
    rw [hc.ι_π, hh.comp_proj]
    exact (hψg t).symm
  -- and the solution tends to its phase
  have hdiff : Tendsto (fun t => φ t - ψ t) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => γ * (t - t₀)) atTop atTop :=
      (tendsto_atTop_add_const_right atTop (-t₀) tendsto_id).const_mul_atTop hγ |>.congr
        fun t => by simp [sub_eq_add_neg]
    have h2 := ((Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul C).mul_const
      ‖(1 - P) (φ t₀) - h (P (φ t₀))‖
    rw [mul_zero, zero_mul] at h2
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [eventually_ge_atTop t₀] with t ht
    exact hψb t ht
  have := hdiff.add hψlim
  rw [zero_add] at this
  exact this.congr fun t => sub_add_cancel _ _

end Transfer

/-! ## The centre manifold theorem with the stability half of the reduction principle -/

section Theorem

open Asymptotics LyapunovPerron

variable {n : ℕ} {A P : State n →L[ℝ] State n}

/-- **Centre manifold theorem with attraction and the reduction principle** (centre–stable case,
Carr, Theorems 1–3; Pliss). Under the dichotomy `‖e^{tA}P‖ ≤ K e^{ε|t|}`,
`‖e^{tA}(1 − P)‖ ≤ K e^{−βt}` (`t ≥ 0`) with `qε < β` (`q ≥ 1`), for `f` of class `C¹` with
`f(0) = 0`, `Df(0) = 0`, there is a centre manifold — `ρ > 0`, a Lipschitz graph map `h`,
`h(u) = o(‖u‖)`, locally invariant in the ball of radius `ρ` — such that
* (Carr's approximation) every `C¹` candidate `φ` into `ker P` with `φ(0) = 0`, `Dφ(0) = 0` and
  invariance defect `O(‖u‖^q)` satisfies `h(u) − φ(u) = O(‖u‖^q)` on `range P`;
* (attraction) solutions staying in a small ball for `t ≥ t₀` have an asymptotic phase on the
  manifold at an exponential rate `γ > 0`;
* (reduction principle) for every chart `ι`, `π` of `range P`, Lyapunov stability and local
  asymptotic stability of the chart field at `0` are those of the full field. -/
@[tmio T, powerlib_foundation] theorem exists_centerManifold_stable
    (hP : IsCommutingProjection A P) {K ε β q : ℝ} (hε : 0 ≤ ε) (hq : 1 ≤ q)
    (hqε : q * ε < β) (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    {f : State n → State n} (hf : ContDiff ℝ 1 f) (hf0 : f 0 = 0) (hDf : fderiv ℝ f 0 = 0) :
    ∃ ρ > 0, ∃ h : State n → State n, ∃ L : NNReal, IsGraphMap P h ∧ LipschitzWith L h ∧
      IsLittleOrder P h 1 ∧
      (∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
        φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h) ∧
      (∀ φ : State n → State n, ContDiffAt ℝ 1 φ 0 → φ 0 = 0 → fderiv ℝ φ 0 = 0 →
        (∀ x, P (φ x) = 0) → IsOrder P (invarianceDefect A P f φ) q →
        IsOrder P (fun u => h u - φ u) q) ∧
      (∃ C γ : ℝ, 0 ≤ C ∧ 0 < γ ∧ ∃ r > 0, ∀ (t₀ : ℝ) (φ : ℝ → State n),
        IsIntegralCurveOn φ (fun _ y => fullField A f y) (Ici t₀) → (∀ t, t₀ ≤ t → ‖φ t‖ < r) →
        ∃ ψ : ℝ → State n, IsIntegralCurveOn ψ (fun _ y => fullField A f y) (Ici t₀) ∧
          (∀ t, t₀ ≤ t → ψ t ∈ graph P h ∧ ‖ψ t‖ < ρ) ∧
          ∀ t, t₀ ≤ t → ‖φ t - ψ t‖ ≤ C * Real.exp (-(γ * (t - t₀))) *
            ‖(1 - P) (φ t₀) - h (P (φ t₀))‖) ∧
      (∀ {m : ℕ} (ι : State m →L[ℝ] State n) (π : State n →L[ℝ] State m), IsChart P ι π →
        LyapunovStable (chartField A f h ι π) 0 → LyapunovStable (fullField A f) 0) ∧
      (∀ {m : ℕ} (ι : State m →L[ℝ] State n) (π : State n →L[ℝ] State m), IsChart P ι π →
        LocalAsymptoticStable (chartField A f h ι π) 0 →
        LocalAsymptoticStable (fullField A f) 0) := by
  have hs : HasStrictFDerivAt f (0 : State n →L[ℝ] State n) 0 := by
    have := (hf.contDiffAt (x := 0)).hasStrictFDerivAt (by norm_num)
    rwa [hDf] at this
  have hK := nonneg_of_stable_bound hst
  have hq0 : 0 < q := by linarith
  have hβ : 0 < β := lt_of_le_of_lt (mul_nonneg hq0.le hε) hqε
  -- the weight of the construction (as in Carr's approximation theorem) and the phase rate
  set η := (ε + β / q) / 2 with hηdef
  have hεβq : ε < β / q := by rw [lt_div_iff₀ hq0]; linarith
  have hεη : ε < η := by rw [hηdef]; linarith
  have hηβq : η < β / q := by rw [hηdef]; linarith
  have hqη : q * η < β := by have := (lt_div_iff₀ hq0).1 hηβq; linarith
  have hηβ : η < β := hηβq.trans_le (div_le_self hβ.le hq)
  have hη : 0 ≤ η := hε.trans hεη.le
  have hβq : 0 < β - q * η := sub_pos.2 hqη
  set γ := (ε + β) / 2 with hγdef
  have hεγ : ε < γ := by rw [hγdef]; linarith
  have hγβ : γ < β := by rw [hγdef]; linarith
  have hd1 : 0 < γ - ε := sub_pos.2 hεγ
  have hd2 : 0 < β - γ := sub_pos.2 hγβ
  have hγ0 : 0 < γ := lt_of_le_of_lt hε hεγ
  set κ := gapConst ε η β with hκdef
  have hκ : 0 < κ := gapConst_pos hεη hηβ
  -- the Lipschitz bound `δ`, small for the construction, the approximation and the phase
  set L₀ := ‖1 - P‖ * (2 * K) * ‖P‖ with hL₀
  have hL₀0 : 0 ≤ L₀ := by positivity
  set X := K * (‖1 - P‖ + ‖P‖) / (β - q * η) with hX
  set Y := K * ((1 + K * L₀) / (γ - ε) + 1 / (β - γ)) with hY
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  set D := K * κ + X + Y with hD
  have hD0 : 0 ≤ D := by positivity
  set δ : ℝ := 1 / (2 * (D + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hδD : δ * D < 1 / 2 := by
    rw [hδdef, show 1 / (2 * (D + 1)) * D = D / (2 * (D + 1)) by ring,
      div_lt_iff₀ (by positivity)]
    linarith
  have hDsplit : δ * D = δ * (K * κ) + δ * X + δ * Y := by rw [hD]; ring
  have hδX : 0 ≤ δ * X := mul_nonneg hδ.le hX0
  have hδY : 0 ≤ δ * Y := mul_nonneg hδ.le hY0
  have hδK : 0 ≤ δ * (K * κ) := mul_nonneg hδ.le (mul_nonneg hK hκ.le)
  have hk2 : K * δ * κ ≤ δ * D := by
    rw [hDsplit, show K * δ * κ = δ * (K * κ) by ring]; linarith
  have hk : K * δ * κ < 1 := by linarith
  have hk1 : 0 < 1 - K * δ * κ := sub_pos.2 hk
  have hLδ : ‖1 - P‖ * (K / (1 - K * δ * κ)) * ‖P‖ ≤ L₀ := by
    have h1 : K / (1 - K * δ * κ) ≤ 2 * K := by
      rw [div_le_iff₀ hk1]; nlinarith
    rw [hL₀]; gcongr
  have hph : K * δ * ((1 + K * (‖1 - P‖ * (K / (1 - K * δ * κ)) * ‖P‖)) / (γ - ε) +
      1 / (β - γ)) < 1 := by
    have h1 : K * δ * ((1 + K * (‖1 - P‖ * (K / (1 - K * δ * κ)) * ‖P‖)) / (γ - ε) +
        1 / (β - γ)) ≤ δ * Y := by
      rw [hY, show δ * (K * ((1 + K * L₀) / (γ - ε) + 1 / (β - γ))) =
        K * δ * ((1 + K * L₀) / (γ - ε) + 1 / (β - γ)) by ring]
      gcongr
    have h2 : δ * Y ≤ δ * D := by rw [hDsplit]; linarith
    linarith
  have hsmall : K * ((‖1 - P‖ + ‖P‖) * (Real.toNNReal δ : ℝ)) / (β - q * η) < 1 := by
    rw [Real.coe_toNNReal _ hδ.le]
    have h1 : K * ((‖1 - P‖ + ‖P‖) * δ) / (β - q * η) = δ * X := by rw [hX]; ring
    have h2 : δ * X ≤ δ * D := by rw [hDsplit]; linarith
    linarith
  obtain ⟨ρ, hρ, g, hg, hg0, hgf, h, L, hh, hL, htan, hinv, hglob, C, hC, hphase⟩ :=
    exists_centerManifold_phase hP hε hεη hηβ hεγ hγβ hcen hst hf0 hs hδ hk hph
  -- Carr's approximation property for this manifold
  have happrox : ∀ φ : State n → State n, ContDiffAt ℝ 1 φ 0 → φ 0 = 0 →
      fderiv ℝ φ 0 = 0 → (∀ x, P (φ x) = 0) → IsOrder P (invarianceDefect A P f φ) q →
      IsOrder P (fun u => h u - φ u) q := by
    intro φ hφ hφ0 hDφ hφP hdef
    obtain ⟨r, hr, ψ, hψ, hψ0, hψd, hψP, hψφ⟩ := exists_contDiff_cutoff hφ hφ0 hDφ hφP
    have hψn : ∀ x, ‖ψ x‖ ≤ ‖x‖ := fun x => by
      have := convex_univ.norm_image_sub_le_of_norm_fderiv_le
        (fun y _ => hψ.differentiable one_ne_zero y) (fun y _ => hψd y) (mem_univ 0)
        (mem_univ x)
      simpa [hψ0] using this
    obtain ⟨M, hM, hMb⟩ :=
      exists_defect_bound (A := A) (P := P) hq hρ hr hg hgf hg0 hψd hψn hψφ hdef
    have hCb := norm_sub_cutoff_le hP hη hq hqη hst hg hh (C₁ := K / (1 - K * δ * κ))
      (by positivity) (fun u => by
        obtain ⟨x, hx0, hxd, -, hxb⟩ := hglob u
        exact ⟨x, hx0, hxd, hxb⟩) hψ hψd hψn hψP hM hMb hsmall
    obtain ⟨C', hC'⟩ : ∃ C', ∀ u, ‖h u - ψ (P u)‖ ≤ C' * ‖P u‖ ^ q := ⟨_, hCb⟩
    refine IsBigO.of_bound C' ?_
    filter_upwards [inter_mem_nhdsWithin (Set.range P) (Metric.ball_mem_nhds 0 hr)]
      with u ⟨⟨w, hw⟩, hu⟩
    subst hw
    rw [Metric.mem_ball, dist_zero_right] at hu
    have hPu : P (P w) = P w := hP.idem w
    have h1 := hC' (P w)
    rw [hPu, hψφ _ hu] at h1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact h1
  refine ⟨ρ, hρ, h, L, hh, hL, htan, hinv, happrox,
    ⟨C, γ, hC, hγ0, exists_phase_of_cutoff hh hL hρ hgf hC hγ0.le hphase⟩,
    fun ι π hc hLS => lyapunovStable_of_chartField hP hh hL hc hρ hg hgf hC hγ0.le hphase hLS,
    fun ι π hc hLAS =>
      localAsymptoticStable_of_chartField hP hh hL hc hρ hg hgf hC hγ0 hphase hLAS⟩

end Theorem

/-! ## (3) `ℓ₁ < 0` gives local asymptotic stability in any dimension -/

section FirstLyapunov

open Asymptotics LyapunovPerron NormalForm.LyapunovCoefficient

variable {n : ℕ} {A P : State n →L[ℝ] State n}

/-- **The reduced planar `l₁ < 0` gives local asymptotic stability in any dimension** (the
stability counterpart of `unstable_of_dichotomy_reduced_l1_pos`). Let `A` have a
two-dimensional centre subspace `range P` (coordinates `ι : ℝ² → ℝⁿ`, `π`) with the
centre–stable dichotomy, `3ε < β`; `f` of class `C¹`, `f(0) = 0`, `Df(0) = 0`,
`f(x) = Q(x, x) + C(x, x, x) + o(‖x‖³)`; `H₀` (values in `ker P`) the solution of the
homological equation; `L₂ = πAι` (`L₂² = −ω²`, `ω > 0`), `Q₂(y, y) = πQ(ιy, ιy)`,
`C₂(y, y, y) = π[Q(ιy, H₀(ιy, ιy)) + Q(H₀(ιy, ιy), ιy) + C(ιy, ιy, ιy)]`. If
`l1 L₂ Q₂ C₂ ω < 0`, the origin is locally asymptotically stable for `ẋ = A x + f x`. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_dichotomy_reduced_l1_neg
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
    (hl : Degenerate.PlanarFocus.l1 L₂ Q₂ C₂ ω < 0) :
    LocalAsymptoticStable (fullField A f) 0 := by
  have hf2 : (fun x => f x - Q x x) =O[𝓝 0] fun x => ‖x‖ ^ 3 := by
    have hCb : (fun x : State n => C ![x, x, x]) =O[𝓝 0] fun x => ‖x‖ ^ 3 :=
      (isBigO_trilin C (fun x => x) (fun x => x) fun x => x).congr_right fun x => by ring
    exact (hfQC.isBigO.add hCb).congr_left fun x => by abel
  obtain ⟨ρ, hρ, h, L, hh, hL, -, -, happrox, -, -, hLAS⟩ :=
    exists_centerManifold_stable hP hε (q := 3) (by norm_num) hgap hcen hst hf hf0 hDf
  -- the quadratic part of this centre manifold is the homological solution
  have hH : HasQuadraticPart P h H₀ := by
    have hd := happrox (quadGraph P H₀) (contDiff_quadGraph P H₀).contDiffAt
      (by simp [quadGraph]) (fderiv_quadGraph_zero P H₀) (fun x => hPH _ _)
      (isOrder_invarianceDefect_quadGraph hP hhom hf2)
    refine hd.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [self_mem_nhdsWithin] with v hv
    obtain ⟨w, rfl⟩ := hv
    simp [quadGraph, hP.idem]
  have hexp := chartField_expansion (A := A) hc hfQC hH
  have hexp' : (fun y => chartField A f h ι π y - (L₂ y + Q₂ y y + C₂ ![y, y, y]))
      =o[𝓝 0] fun y => ‖y‖ ^ 3 := by
    refine hexp.congr_left fun y => ?_
    rw [hL₂, hQ₂, hC₂]
    simp only [map_add]
    abel
  have hcont : Continuous (chartField A f h ι π) :=
    π.continuous.comp ((A.continuous.comp ι.continuous).add
      (hf.continuous.comp (ι.continuous.add (hL.continuous.comp ι.continuous))))
  exact hLAS ι π hc (Degenerate.PlanarFocus.localAsymptoticStable_of_l1_neg hω hrot
    Filter.univ_mem hcont.continuousOn hexp' hl)

/-- **`ℓ₁ < 0` gives local asymptotic stability in any dimension** (projection-formula form;
the stability counterpart of `unstable_of_firstLyapunov_pos`). Let `(q, p)` be a critical pair of
`ẋ = A x + f x` at `0` (`f` of class `C¹`, `f(0) = 0`, `Df(0) = 0`), let `P = critP q p` have the
centre–stable dichotomy (`3ε < β`), let `A` and `2iω − A` be invertible, and let
`f(x) = Q(x, x) + C(x, x, x) + o(‖x‖³)` with `D²F(0)`, `D³F(0)` the symmetrizations of `Q`, `C`.
If Kuznetsov's first Lyapunov coefficient `firstLyapunov (fullField A f) 0 ω q p` is negative,
the origin is locally asymptotically stable. (Centre manifold with attraction:
`exists_centerManifold_stable`; identity of the coefficients:
`IsCritical.l1_reduced_eq_firstLyapunov`; planar law:
`Degenerate.PlanarFocus.localAsymptoticStable_of_l1_neg`.) -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_firstLyapunov_neg
    {f : State n → State n} {Q : State n →L[ℝ] State n →L[ℝ] State n}
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
    (hl : firstLyapunov (fullField A f) 0 ω q p < 0) :
    LocalAsymptoticStable (fullField A f) 0 := by
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
  exact localAsymptoticStable_of_dichotomy_reduced_l1_neg hP hε hgap hcen hst hf hf0 hDf hfQC
    hhom hPH hc.isChart (fun y => (hc.critπ_comp y).symm) (fun y => redQ_apply q p Q y y)
    (fun y => redC_apply q p Q H₀ C y y y) hc.freq_pos (rotL_rotL ω) (hbr ▸ hl)

end FirstLyapunov

/-! ## The reduction principle for any tangent locally invariant graph -/

section AnyGraph

open LyapunovPerron

variable {n m : ℕ} {A P : State n →L[ℝ] State n} {f h : State n → State n}
  {ι : State m →L[ℝ] State n} {π : State n →L[ℝ] State m} {ρ : ℝ}

@[tmio T, powerlib_foundation] private theorem norm_proj_le_of_le {r : ℝ} (hr : 0 ≤ r)
    {x : State n} (hx : ‖x‖ ≤ r / (‖P‖ + 1)) : ‖P x‖ ≤ r := by
  refine (P.le_opNorm x).trans ?_
  calc ‖P‖ * ‖x‖ ≤ ‖P‖ * (r / (‖P‖ + 1)) := by gcongr
    _ ≤ r := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg P]

/-- **Solutions on a locally invariant graph starting small stay small and on the graph.** Let
the graph of `h` be locally invariant for `ẋ = A x + f(x)` in the ball of radius `ρ`, `g = f` on
the ball of radius `r`, and `h'` an `L`-Lipschitz graph map equal to `h` where `‖P x‖ ≤ r`. If the
chart field of `h` is Lyapunov stable at `0`, every forward solution of `ẋ = A x + g(x)` that
starts on the graph of `h` close enough to `0` stays in any prescribed ball and on the graph. -/
@[tmio T, powerlib_foundation] theorem forall_mem_graph_of_lyapunovStable_chartField
    {g : State n → State n} {L : NNReal} (hP : IsCommutingProjection A P) (hh : IsGraphMap P h)
    (hc : IsChart P ι π) (hρ : 0 < ρ)
    (hinv : ∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
      φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h)
    {r : ℝ} (hr : 0 < r) (hgf : ∀ y, ‖y‖ ≤ r → g y = f y) {h' : State n → State n}
    (hh' : IsGraphMap P h') (hL' : LipschitzWith L h') (hh'h : ∀ x, ‖P x‖ ≤ r → h' x = h x)
    (hLS : LyapunovStable (chartField A f h ι π) 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ (t₀ : ℝ) (X : ℝ → State n), IsIntegralCurveOn X (fun _ y => A y + g y) (Ici t₀) →
      X t₀ ∈ graph P h → ‖X t₀‖ < d → ∀ t, t₀ ≤ t → ‖X t‖ < ε ∧ X t ∈ graph P h := by
  set ε' := min ε (min ρ (r / (‖P‖ + 1))) with hε'
  have hε'0 : 0 < ε' := lt_min hε (lt_min hρ (by positivity))
  have hε'P : ε' ≤ r / (‖P‖ + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hε'r : ε' ≤ r := hε'P.trans (div_le_self hr.le (by linarith [norm_nonneg P]))
  have hε'ρ : ε' ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
  set εr := ε' / (2 * ((1 + L) * (‖ι‖ + 1))) with hεr
  have hεr0 : 0 < εr := by positivity
  obtain ⟨dr, hdr, hLSr⟩ := hLS εr hεr0
  -- on a segment inside the ball a solution starting on the graph stays on it
  have hseg : ∀ (t₀ s : ℝ) (X : ℝ → State n),
      IsIntegralCurveOn X (fun _ y => A y + g y) (Ici t₀) → X t₀ ∈ graph P h →
      (∀ τ ∈ Icc t₀ s, ‖X τ‖ < ε') → ∀ τ ∈ Icc t₀ s, X τ ∈ graph P h := by
    intro t₀ s X hX hX0 hin
    refine hinv t₀ s X ?_ hX0 fun τ hτ => (hin τ hτ).trans_le hε'ρ
    exact isIntegralCurveOn_of_eq_on_curve (g := fun y => A y + g y)
      (hX.mono Icc_subset_Ici_self) fun τ hτ => by
        show A (X τ) + g (X τ) = A (X τ) + f (X τ)
        rw [hgf _ ((hin τ hτ).le.trans hε'r)]
  refine ⟨min (dr / (‖π‖ + 1)) ε', by positivity, fun t₀ X hX hX0 hXd t ht => ?_⟩
  have hstay : ∀ τ ∈ Icc t₀ t, ‖X τ - 0‖ < ε' := by
    refine forall_norm_sub_lt_of_bootstrap (hX.continuousOn.mono Icc_subset_Ici_self)
      (by rw [sub_zero]; exact hXd.trans_le (min_le_right _ _)) fun s hs hin => ?_
    have hin' : ∀ τ ∈ Icc t₀ s, ‖X τ‖ < ε' := fun τ hτ => by simpa using hin τ hτ
    have hgr := hseg t₀ s X hX hX0 hin'
    have hcurve := hc.isIntegralCurveOn_π_of_mem hP hh hgf (s := Icc t₀ s)
      (hX.mono Icc_subset_Ici_self) fun τ hτ => ⟨(hin' τ hτ).le.trans hε'r, hgr τ hτ⟩
    have hπ0 : ‖π (X t₀) - 0‖ < dr := by
      rw [sub_zero]
      calc ‖π (X t₀)‖ ≤ ‖π‖ * ‖X t₀‖ := π.le_opNorm _
        _ ≤ (‖π‖ + 1) * ‖X t₀‖ := by nlinarith [norm_nonneg (X t₀)]
        _ < (‖π‖ + 1) * (dr / (‖π‖ + 1)) := by
            gcongr; exact hXd.trans_le (min_le_left _ _)
        _ = dr := by field_simp
    have hπs := hLSr t₀ s (fun τ => π (X τ)) hcurve hπ0 s ⟨hs.1, le_rfl⟩
    rw [sub_zero] at hπs ⊢
    have hXs' : X s ∈ graph P h' := by
      have hgs := hgr s ⟨hs.1, le_rfl⟩
      show X s = P (X s) + h' (X s)
      rw [hh'h _ (norm_proj_le_of_le hr.le ((hin' s ⟨hs.1, le_rfl⟩).le.trans hε'P))]
      exact hgs
    calc ‖X s‖ ≤ (1 + L) * ‖ι‖ * ‖π (X s)‖ := hc.norm_le_of_mem_graph hh' hL' hXs'
      _ ≤ (1 + L) * (‖ι‖ + 1) * εr :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hπs.le
            (norm_nonneg _) (by positivity)
      _ = ε' / 2 := by rw [hεr]; field_simp
  have hin : ∀ τ ∈ Icc t₀ t, ‖X τ‖ < ε' := fun τ hτ => by simpa using hstay τ hτ
  exact ⟨(hin t ⟨ht, le_rfl⟩).trans_le (min_le_left _ _),
    hseg t₀ t X hX hX0 hin t ⟨ht, le_rfl⟩⟩

/-- **The reduction principle, Lyapunov stability, for any tangent invariant graph** (Carr,
Theorem 2 (a), in its stated generality). Under the centre–stable dichotomy (`0 ≤ ε < β`), let
`f(0) = 0` with strict derivative `0` at `0`, and let `h` be any graph map over `range P` with
strict derivative `0` at `0` (e.g. `C¹` near `0` with `Dh(0) = 0`) whose graph is locally
invariant in the ball of radius `ρ` (no uniqueness or construction of `h` is used). If the chart
field of `h` is Lyapunov stable at `0`, so is the full field. -/
@[tmio T, powerlib_foundation] theorem lyapunovStable_of_invariantGraph
    (hP : IsCommutingProjection A P) {K ε β : ℝ} (hε : 0 ≤ ε) (hεβ : ε < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    (hf0 : f 0 = 0) (hf : HasStrictFDerivAt f (0 : State n →L[ℝ] State n) 0)
    (hh : IsGraphMap P h) (hhs : HasStrictFDerivAt h (0 : State n →L[ℝ] State n) 0)
    (hρ : 0 < ρ)
    (hinv : ∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
      φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h)
    (hc : IsChart P ι π) (hLS : LyapunovStable (chartField A f h ι π) 0) :
    LyapunovStable (fullField A f) 0 := by
  obtain ⟨r, hr, g, δ, hg, hgf, h', L, hh', hL', hh'h, C, γ, hC, hγ, hphase⟩ :=
    exists_tangentGraph_phase hP hε hεβ hcen hst hf0 hf hh hhs
  intro ε₀ hε₀
  set ε' := min ε₀ r with hε'
  have hε'0 : 0 < ε' := lt_min hε₀ hr
  have hε'r : ε' ≤ r := min_le_right _ _
  obtain ⟨d₁, hd₁, hstay⟩ := forall_mem_graph_of_lyapunovStable_chartField hP hh hc hρ hinv hr
    hgf hh' hL' hh'h hLS (ε := ε' / 4) (by positivity)
  set Cz := ‖1 - P‖ + L * ‖P‖ with hCz
  have hCz0 : 0 ≤ Cz := by positivity
  have hD : 0 < 1 + C * Cz := by positivity
  set c₀ := min d₁ (min (ε' / 4) (r / (‖P‖ + 1))) with hc₀
  have hc₀0 : 0 < c₀ := lt_min hd₁ (lt_min (by positivity) (by positivity))
  have hc₀4 : c₀ ≤ ε' / 4 := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨c₀ / (1 + C * Cz), by positivity, fun t₀ t₁ φ hφ hφ0 => ?_⟩
  rw [sub_zero] at hφ0
  have hφ0' : (1 + C * Cz) * ‖φ t₀‖ < c₀ := by
    rwa [lt_div_iff₀ hD, mul_comm] at hφ0
  have hφ1 : ‖φ t₀‖ ≤ (1 + C * Cz) * ‖φ t₀‖ := by
    nlinarith [norm_nonneg (φ t₀), mul_nonneg hC hCz0]
  have hlip : LipschitzWith (‖A‖₊ + δ) (fun y => A y + g y) := A.lipschitzWith.add hg
  obtain ⟨x, hx0, hx⟩ := Flow.forwardComplete_of_lipschitzWith hlip t₀ (φ t₀)
  obtain ⟨X, hX, hXg', hXb⟩ := hphase t₀ x hx
  have hdiff : ∀ t, t₀ ≤ t → ‖x t - X t‖ ≤ C * Cz * ‖φ t₀‖ := fun t ht => by
    refine (hXb t ht).trans ?_
    have he : Real.exp (-(γ * (t - t₀))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [sub_nonneg.2 ht])
    have hz := norm_graphDist_le hh' hL' (x t₀)
    rw [hx0] at hz
    calc C * Real.exp (-(γ * (t - t₀))) * ‖(1 - P) (x t₀) - h' (P (x t₀))‖
        ≤ C * 1 * (Cz * ‖φ t₀‖) := by rw [hx0]; gcongr
      _ = C * Cz * ‖φ t₀‖ := by ring
  have hX0 : ‖X t₀‖ < c₀ := by
    calc ‖X t₀‖ ≤ ‖x t₀‖ + ‖x t₀ - X t₀‖ := by
          have := norm_sub_le (x t₀) (x t₀ - X t₀); rwa [sub_sub_cancel] at this
      _ ≤ ‖φ t₀‖ + C * Cz * ‖φ t₀‖ := add_le_add (le_of_eq (by rw [hx0])) (hdiff t₀ le_rfl)
      _ = (1 + C * Cz) * ‖φ t₀‖ := by ring
      _ < c₀ := hφ0'
  have hXg : X t₀ ∈ graph P h := by
    show X t₀ = P (X t₀) + h (X t₀)
    rw [← hh'h _ (norm_proj_le_of_le hr.le
      (hX0.le.trans ((min_le_right _ _).trans (min_le_right _ _))))]
    exact hXg'
  have hXs := hstay t₀ X hX hXg (hX0.trans_le (min_le_left _ _))
  have hCzφ : C * Cz * ‖φ t₀‖ < ε' / 4 := by
    have : C * Cz * ‖φ t₀‖ ≤ (1 + C * Cz) * ‖φ t₀‖ := by nlinarith [norm_nonneg (φ t₀)]
    linarith
  have hxs : ∀ t, t₀ ≤ t → ‖x t‖ < ε' / 2 := fun t ht => by
    calc ‖x t‖ ≤ ‖X t‖ + ‖x t - X t‖ := by
          have := norm_add_le (X t) (x t - X t); rwa [add_sub_cancel] at this
      _ < ε' / 4 + ε' / 4 :=
          add_lt_add_of_lt_of_le (hXs t ht).1 ((hdiff t ht).trans hCzφ.le)
      _ = ε' / 2 := by ring
  -- the segment `φ` is the cutoff solution `x` while it stays in the ball
  have hφx : ∀ t ∈ Icc t₀ t₁, ‖φ t - 0‖ < ε' := by
    refine forall_norm_sub_lt_of_bootstrap hφ.continuousOn
      (by rw [sub_zero]; linarith) fun s hs hin => ?_
    have hφg : IsIntegralCurveOn φ (fun _ y => A y + g y) (Icc t₀ s) :=
      isIntegralCurveOn_of_eq_on_curve (f := fun y => A y + g y)
        (hφ.mono (Icc_subset_Icc le_rfl hs.2)) fun τ hτ => by
          have := hin τ hτ; rw [sub_zero] at this
          show A (φ τ) + f (φ τ) = A (φ τ) + g (φ τ)
          rw [hgf _ (this.le.trans hε'r)]
    have heq := eqOn_of_isIntegralCurveOn_Icc (K := ‖A‖₊ + δ) (fun _ => hlip) hφg
      (hx.mono Icc_subset_Ici_self) hx0.symm ⟨hs.1, le_rfl⟩
    rw [sub_zero, heq]
    exact (hxs s hs.1).le
  intro t ht
  exact (hφx t ht).trans_le (min_le_left _ _)

/-- **The reduction principle, local asymptotic stability, for any tangent invariant graph**
(Carr, Theorem 2 (b), in its stated generality). Under the hypotheses of
`lyapunovStable_of_invariantGraph`: if the chart field of `h` is locally asymptotically stable
at `0`, so is the full field. -/
@[tmio T, powerlib_foundation] theorem localAsymptoticStable_of_invariantGraph
    (hP : IsCommutingProjection A P) {K ε β : ℝ} (hε : 0 ≤ ε) (hεβ : ε < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    (hf0 : f 0 = 0) (hf : HasStrictFDerivAt f (0 : State n →L[ℝ] State n) 0)
    (hh : IsGraphMap P h) (hhs : HasStrictFDerivAt h (0 : State n →L[ℝ] State n) 0)
    (hρ : 0 < ρ)
    (hinv : ∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
      φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h)
    (hc : IsChart P ι π) (hLAS : LocalAsymptoticStable (chartField A f h ι π) 0) :
    LocalAsymptoticStable (fullField A f) 0 := by
  obtain ⟨hLSr, cr, hcr, hattr⟩ := hLAS
  have hLS := lyapunovStable_of_invariantGraph hP hε hεβ hcen hst hf0 hf hh hhs hρ hinv hc hLSr
  refine ⟨hLS, ?_⟩
  obtain ⟨r, hr, g, δ, hg, hgf, h', L, hh', hL', hh'h, C, γ, hC, hγ, hphase⟩ :=
    exists_tangentGraph_phase hP hε hεβ hcen hst hf0 hf hh hhs
  set r' := r / (‖P‖ + 1) with hr'def
  have hr' : 0 < r' := by positivity
  have hr'r : r' ≤ r := div_le_self hr.le (by linarith [norm_nonneg P])
  obtain ⟨d₀, hd₀, hLS₀⟩ := hLS r' hr'
  obtain ⟨d₂, hd₂, hstay⟩ := forall_mem_graph_of_lyapunovStable_chartField hP hh hc hρ hinv hr
    hgf hh' hL' hh'h hLSr hr'
  set Cz := ‖1 - P‖ + L * ‖P‖ with hCz
  have hCz0 : 0 ≤ Cz := by positivity
  have hD : 0 < 1 + C * Cz := by positivity
  set c₀ := min d₀ (min d₂ (min (cr / (‖π‖ + 1)) r')) with hc₀
  have hc₀0 : 0 < c₀ := lt_min hd₀ (lt_min hd₂ (lt_min (by positivity) hr'))
  refine ⟨c₀ / (1 + C * Cz), by positivity, fun t₀ φ hφ hφ0 => ?_⟩
  rw [sub_zero] at hφ0
  have hφ0' : (1 + C * Cz) * ‖φ t₀‖ < c₀ := by
    rwa [lt_div_iff₀ hD, mul_comm] at hφ0
  have hφ1 : ‖φ t₀‖ ≤ (1 + C * Cz) * ‖φ t₀‖ := by
    nlinarith [norm_nonneg (φ t₀), mul_nonneg hC hCz0]
  -- the solution stays in the ball of radius `r'`, hence solves the cutoff field
  have hφr : ∀ t, t₀ ≤ t → ‖φ t‖ < r' := fun t ht => by
    have := hLS₀ t₀ t φ (hφ.mono Icc_subset_Ici_self)
      (by rw [sub_zero]; linarith [min_le_left d₀ (min d₂ (min (cr / (‖π‖ + 1)) r'))]) t
      ⟨ht, le_rfl⟩
    rwa [sub_zero] at this
  have hφg : IsIntegralCurveOn φ (fun _ y => A y + g y) (Ici t₀) :=
    isIntegralCurveOn_of_eq_on_curve (f := fun y => A y + g y) hφ fun t ht => by
      show A (φ t) + f (φ t) = A (φ t) + g (φ t)
      rw [hgf _ ((hφr t ht).le.trans hr'r)]
  obtain ⟨X, hX, hXg', hXb⟩ := hphase t₀ φ hφg
  have hX0 : ‖X t₀‖ < c₀ := by
    have h1 := hXb t₀ le_rfl
    rw [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one] at h1
    have hz := norm_graphDist_le hh' hL' (φ t₀)
    calc ‖X t₀‖ ≤ ‖φ t₀‖ + ‖φ t₀ - X t₀‖ := by
          have := norm_sub_le (φ t₀) (φ t₀ - X t₀); rwa [sub_sub_cancel] at this
      _ ≤ ‖φ t₀‖ + C * (Cz * ‖φ t₀‖) := by gcongr; exact h1.trans (by gcongr)
      _ = (1 + C * Cz) * ‖φ t₀‖ := by ring
      _ < c₀ := hφ0'
  have hc₀r' : c₀ ≤ r' := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hXg : X t₀ ∈ graph P h := by
    show X t₀ = P (X t₀) + h (X t₀)
    rw [← hh'h _ (norm_proj_le_of_le hr.le (hX0.le.trans hc₀r'))]
    exact hXg'
  -- the asymptotic phase is a reduced solution starting close to `0`
  have hXs := hstay t₀ X hX hXg (hX0.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hcurve := hc.isIntegralCurveOn_π_of_mem hP hh hgf (s := Ici t₀) hX fun t ht =>
    ⟨(hXs t ht).1.le.trans hr'r, (hXs t ht).2⟩
  have hπ0 : ‖π (X t₀) - 0‖ < cr := by
    rw [sub_zero]
    have hlt : ‖X t₀‖ < cr / (‖π‖ + 1) :=
      hX0.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    calc ‖π (X t₀)‖ ≤ ‖π‖ * ‖X t₀‖ := π.le_opNorm _
      _ ≤ (‖π‖ + 1) * ‖X t₀‖ := by nlinarith [norm_nonneg (X t₀)]
      _ < (‖π‖ + 1) * (cr / (‖π‖ + 1)) := by gcongr
      _ = cr := by field_simp
  have hlim := hattr t₀ (fun t => π (X t)) hcurve hπ0
  -- hence the phase tends to `0`
  have hXlim : Tendsto X atTop (𝓝 0) := by
    have hι := (ι.continuous.tendsto 0).comp hlim
    have hh0 := (hL'.continuous.tendsto _).comp hι
    have hsum := hι.add hh0
    rw [map_zero, hh'.map_zero, add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop t₀] with t ht
    simp only [Function.comp_def]
    rw [hc.ι_π, hh'.comp_proj, hh'h _ (norm_proj_le_of_le hr.le (hXs t ht).1.le)]
    exact (hXs t ht).2.symm
  -- and the solution tends to its phase
  have hdiff : Tendsto (fun t => φ t - X t) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => γ * (t - t₀)) atTop atTop :=
      (tendsto_atTop_add_const_right atTop (-t₀) tendsto_id).const_mul_atTop hγ |>.congr
        fun t => by simp [sub_eq_add_neg]
    have h2 := ((Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul C).mul_const
      ‖(1 - P) (φ t₀) - h' (P (φ t₀))‖
    rw [mul_zero, zero_mul] at h2
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [eventually_ge_atTop t₀] with t ht
    exact hXb t ht
  have := hdiff.add hXlim
  rw [zero_add] at this
  exact this.congr fun t => sub_add_cancel _ _

/-- **Asymptotic phase on any tangent invariant graph** (Carr, Theorem 2 (b), the phase). Under
the hypotheses of `lyapunovStable_of_invariantGraph` without any stability assumption: there
are `C ≥ 0`, `γ > 0` and `r > 0` such that every solution `φ` of `ẋ = A x + f(x)` that stays in
the ball of radius `r` for `t ≥ t₀` has a solution `ψ` on the graph of `h`, in the ball of radius
`ρ`, with `‖φ(t) − ψ(t)‖ ≤ C e^{−γ(t−t₀)} ‖(1 − P)φ(t₀) − h(P φ(t₀))‖`. -/
@[tmio T, powerlib_foundation] theorem exists_phase_of_invariantGraph
    (hP : IsCommutingProjection A P) {K ε β : ℝ} (hε : 0 ≤ ε) (hεβ : ε < β)
    (hcen : ∀ t, ‖expFlow A t * P‖ ≤ K * Real.exp (ε * |t|))
    (hst : ∀ t, 0 ≤ t → ‖expFlow A t * (1 - P)‖ ≤ K * Real.exp (-(β * t)))
    (hf0 : f 0 = 0) (hf : HasStrictFDerivAt f (0 : State n →L[ℝ] State n) 0)
    (hh : IsGraphMap P h) (hhs : HasStrictFDerivAt h (0 : State n →L[ℝ] State n) 0)
    (hρ : 0 < ρ)
    (hinv : ∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
      φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h) :
    ∃ C γ : ℝ, 0 ≤ C ∧ 0 < γ ∧ ∃ r > 0, ∀ (t₀ : ℝ) (φ : ℝ → State n),
      IsIntegralCurveOn φ (fun _ y => fullField A f y) (Ici t₀) → (∀ t, t₀ ≤ t → ‖φ t‖ < r) →
      ∃ ψ : ℝ → State n, IsIntegralCurveOn ψ (fun _ y => fullField A f y) (Ici t₀) ∧
        (∀ t, t₀ ≤ t → ψ t ∈ graph P h ∧ ‖ψ t‖ < ρ) ∧
        ∀ t, t₀ ≤ t → ‖φ t - ψ t‖ ≤ C * Real.exp (-(γ * (t - t₀))) *
          ‖(1 - P) (φ t₀) - h (P (φ t₀))‖ := by
  obtain ⟨r₀, hr₀, g, δ, hg, hgf, h', L, hh', hL', hh'h, C, γ, hC, hγ, hphase⟩ :=
    exists_tangentGraph_phase hP hε hεβ hcen hst hf0 hf hh hhs
  set R := min r₀ ρ / (‖P‖ + 1) with hRdef
  have hR : 0 < R := by positivity
  have hRm : R ≤ min r₀ ρ := div_le_self (lt_min hr₀ hρ).le (by linarith [norm_nonneg P])
  have hRr₀ : R ≤ r₀ := hRm.trans (min_le_left _ _)
  have hRρ : R ≤ ρ := hRm.trans (min_le_right _ _)
  have hRP : R ≤ r₀ / (‖P‖ + 1) := div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
  set Cz := ‖1 - P‖ + L * ‖P‖ with hCz
  have hCz0 : 0 ≤ Cz := by positivity
  have hD : 0 < 1 + C * Cz := by positivity
  refine ⟨C, γ, hC, hγ, R / (2 * (1 + C * Cz)), by positivity, fun t₀ φ hφ hφr => ?_⟩
  have hD1 : 1 ≤ 1 + C * Cz := by nlinarith [mul_nonneg hC hCz0]
  have hrR : R / (2 * (1 + C * Cz)) ≤ R / 2 :=
    div_le_div_of_nonneg_left hR.le (by positivity) (by linarith)
  have hφg : IsIntegralCurveOn φ (fun _ y => A y + g y) (Ici t₀) :=
    isIntegralCurveOn_of_eq_on_curve (f := fun y => A y + g y) hφ fun t ht => by
      show A (φ t) + f (φ t) = A (φ t) + g (φ t)
      rw [hgf _ ((hφr t ht).le.trans (by linarith))]
  obtain ⟨X, hX, hXg', hXb⟩ := hphase t₀ φ hφg
  have hφ0 : ‖φ t₀‖ ≤ R := (hφr t₀ le_rfl).le.trans (by linarith)
  have hz' : h' (P (φ t₀)) = h (P (φ t₀)) := by
    refine hh'h _ ?_
    rw [hP.idem]
    exact norm_proj_le_of_le hr₀.le (hφ0.trans hRP)
  have hXR : ∀ t, t₀ ≤ t → ‖X t‖ < R := by
    intro t ht
    have he : Real.exp (-(γ * (t - t₀))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [sub_nonneg.2 ht])
    have hz := norm_graphDist_le hh' hL' (φ t₀)
    have hd : ‖φ t - X t‖ ≤ C * Cz * (R / (2 * (1 + C * Cz))) := by
      refine (hXb t ht).trans ?_
      calc C * Real.exp (-(γ * (t - t₀))) * ‖(1 - P) (φ t₀) - h' (P (φ t₀))‖
          ≤ C * 1 * (Cz * ‖φ t₀‖) := by gcongr
        _ ≤ C * 1 * (Cz * (R / (2 * (1 + C * Cz)))) := by
            gcongr; exact (hφr t₀ le_rfl).le
        _ = _ := by ring
    have e : (1 + C * Cz) * (R / (2 * (1 + C * Cz))) = R / 2 := by field_simp
    calc ‖X t‖ ≤ ‖φ t‖ + ‖φ t - X t‖ := by
          have := norm_sub_le (φ t) (φ t - X t); rwa [sub_sub_cancel] at this
      _ < R / (2 * (1 + C * Cz)) + C * Cz * (R / (2 * (1 + C * Cz))) :=
          add_lt_add_of_lt_of_le (hφr t ht) hd
      _ = R / 2 := by rw [← e]; ring
      _ < R := by linarith
  have hXg : X t₀ ∈ graph P h := by
    show X t₀ = P (X t₀) + h (X t₀)
    rw [← hh'h _ (norm_proj_le_of_le hr₀.le ((hXR t₀ le_rfl).le.trans hRP))]
    exact hXg'
  have hXf : IsIntegralCurveOn X (fun _ y => fullField A f y) (Ici t₀) :=
    isIntegralCurveOn_of_eq_on_curve (g := fun y => A y + g y) hX fun t ht => by
      show A (X t) + g (X t) = A (X t) + f (X t)
      rw [hgf _ ((hXR t ht).le.trans hRr₀)]
  refine ⟨X, hXf, fun t ht => ⟨?_, (hXR t ht).trans_le hRρ⟩, fun t ht => ?_⟩
  · exact hinv t₀ t X (hXf.mono Icc_subset_Ici_self) hXg
      (fun τ hτ => (hXR τ hτ.1).trans_le hRρ) t ⟨ht, le_rfl⟩
  · rw [← hz']
    exact hXb t ht

end AnyGraph

end powerlib.Dynamics.CenterManifold
