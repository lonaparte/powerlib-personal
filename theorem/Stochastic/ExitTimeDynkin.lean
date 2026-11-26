import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.ItoFormula
import theorem.Stochastic.ExitTimeLower
import theorem.Stochastic.MFPT
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # The mean exit time solves `L u = −1`: Dynkin's formula at the exit time

For the additive-noise solution `x = S(x₀, c B)` of `x(t) = x₀ + c N B(t) + ∫₀ᵗ b(x)` and a closed
set `K ∋ x₀`, the exit time `τ_K = Stochastic.LDP.exitTime` is an optional time of the natural
filtration (capped at `k`, `{s ≤ τ_K ∧ k}` is read on rational times), the path stays in `K` up to
`τ_K` and exits through `∂K`. Dynkin's formula (`Ito.integral_dynkin`) at `τ_K ∧ k` for a `C²`
solution of `L u = −1` on `K`, `u = 0` on `∂K` gives `E(τ_K ∧ k) = u(x₀) − E[u(x_k); τ_K > k]`,
hence `E τ_K < ∞` and, by monotone convergence, **`E τ_K = u(x₀)`**.

Scope.
* Generic probability theory. `E` a real Banach space (finite-dimensional for the compact-set
  form), `b` globally Lipschitz, one noise column, `B` a pre-Brownian motion with continuous paths
  and strongly measurable `B t`. Absorbing boundary only: a reflecting boundary (the Kramers
  double integral of `theorem/Stochastic/MFPT.lean` with `T'(θ_r) = 0`) needs a reflected
  diffusion, which the library does not construct.
* `u` is assumed to exist and to be `C²` on the whole space (in finite dimension it is cut off
  outside a ball, so only its values near `K` matter); existence and regularity of solutions of
  the Dirichlet problem are not formalized.
* The high-barrier (Kramers–Langer) asymptotics of `u` are not formalized: they are Laplace
  asymptotics of the solution, see the header of `theorem/Stochastic/MFPT.lean`.

Source: B. Øksendal, *Stochastic Differential Equations*, 6th ed. (2003), Thm 7.4.1 (Dynkin's
formula), Ex. 7.4.2 (mean exit time of Brownian motion from a ball/interval), §9.1 (the Dirichlet
problem `L u = −1`, `u = 0` on `∂D`); work-sync theory/T-first-passage-time.md (`L m = −1`, `m = 0`
on `∂𝒟`); theory/T-kramers-escape.md §1.2 (backward equation for the MFPT).

Results.
* `ofReal_le_exitTime_iff` (before the exit time the path stays in `K`),
  `mem_of_forall_Ico_mem`, `pathExt_exitTime_mem_frontier` (**the exit point lies on `∂K`**),
  `measurableSet_le_min_exitTime` (**`τ_K ∧ T₀` is an optional time**),
  `measurable_of_measurableSet_le`.
* **`lintegral_exitTime_eq`** — `E τ_K = u(x₀)` for `u ∈ C²_b` (bounded derivatives, uniformly
  continuous `D²u`, bounded `L u`) with `L u = −1` on `K`, `u = 0` on `∂K`.
* `hasCompactSupport_gen`, `exists_bound_of_hasCompactSupport`, `uniformContinuous_fderiv_fderiv`;
  **`lintegral_exitTime_eq_of_isCompact`** — the same for compact `K` in finite dimension and any
  `C²` solution `u` (cut off by a smooth bump).
* `gen_eq_gen1` — in one dimension `L u = b u' + ½ n² u''` is `FP.gen1 b n²`.
* **`lintegral_exitTime_Icc_brownian`** — `x = x₀ + √(2D) B`: `E τ_{[a, b]} = (x₀ − a)(b − x₀)/(2D)`
  (`MFPT.mfpt_free_diffusion` is the mean exit time).
-/

noncomputable section
namespace powerlib.Stochastic.Ito

open MeasureTheory ProbabilityTheory Real Filter Finset Set
open scoped NNReal ENNReal Topology
open powerlib.Stochastic.LDP (solMap pathExt brownPath exitTime firstExit pathExt_of_mem
  le_exitTime_of_forall_mem exists_notMem_of_exitTime_lt restrictPath_solMap_brownPath)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}

/-! ## The exit time read on one horizon -/

/-- **Before the exit time the path stays in `K`**: for `0 ≤ s ≤ H` and closed `K`,
`s ≤ τ_K` iff the solution on `[0, H]` stays in `K` on `[0, s)`. -/
@[tmio T, powerlib_foundation] theorem ofReal_le_exitTime_iff
    (hBc : ∀ ω, Continuous fun t => B t ω) {L : ℝ≥0} {b : E → E} (hb : LipschitzWith L b)
    (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) {K : Set E} (hK : IsClosed K) (c : ℝ) {H : ℝ≥0}
    {s : ℝ} (hs : 0 ≤ s) (hsH : s ≤ H) (ω : Ω) :
    ENNReal.ofReal s ≤ exitTime b N x₀ K c B hBc ω ↔
      ∀ t ∈ Ico (0 : ℝ) s, pathExt (solMap b N x₀ (c • brownPath B hBc H ω)) t ∈ K := by
  set X := pathExt (solMap b N x₀ (c • brownPath B hBc H ω)) with hX
  constructor
  · intro h t ht
    by_contra hnot
    have htH : t ∈ Icc (0 : ℝ) H := ⟨ht.1, ht.2.le.trans hsH⟩
    have h1 : exitTime b N x₀ K c B hBc ω ≤ ENNReal.ofReal t := by
      refine (iInf_le _ H).trans (iInf₂_le (⟨t, htH⟩ : Icc (0 : ℝ) H) ?_)
      rwa [hX, pathExt_of_mem _ htH] at hnot
    have h2 : ENNReal.ofReal t < ENNReal.ofReal s :=
      (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt ht.1 ht.2)).2 ht.2
    exact absurd (h.trans h1) (not_le.mpr h2)
  · intro h
    rcases eq_or_lt_of_le hs with hs0 | hs0
    · rw [← hs0, ENNReal.ofReal_zero]; exact bot_le
    have hXc : Continuous X := LDP.continuous_pathExt _
    have hall : ∀ t ∈ Icc (0 : ℝ) s, X t ∈ K := by
      intro t ht
      rcases eq_or_lt_of_le ht.2 with hts | hts
      · -- the end point, by closedness
        have hlim : Tendsto X (𝓝[<] s) (𝓝 (X s)) := hXc.continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
        refine hts ▸ hK.mem_of_tendsto hlim ?_
        filter_upwards [Ioo_mem_nhdsLT hs0] with u hu using h u ⟨hu.1.le, hu.2⟩
      · exact h t ⟨ht.1, hts⟩
    have hsH' : s.toNNReal ≤ H := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal s hs]; exact hsH
    have := le_exitTime_of_forall_mem hBc hb N x₀ c (H := s.toNNReal) (ω := ω) fun t => by
      have e := congrArg (fun φ => φ t) (restrictPath_solMap_brownPath hBc hb N x₀ c hsH' ω)
      rw [← e]
      have ht2 : (t : ℝ) ≤ s := by
        have h1 : (t : ℝ) ≤ (s.toNNReal : ℝ) := t.2.2
        exact h1.trans (le_of_eq (Real.coe_toNNReal s hs))
      have hmem : (t : ℝ) ∈ Icc (0 : ℝ) H := ⟨t.2.1, ht2.trans hsH⟩
      have := hall t ⟨t.2.1, ht2⟩
      rwa [hX, pathExt_of_mem _ hmem] at this
    exact this

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- A path that stays in a closed `K` on `[0, s)`, `s > 0`, is in `K` at `s`. -/
@[tmio T, powerlib_foundation] theorem mem_of_forall_Ico_mem {X : ℝ → E} (hX : Continuous X)
    {K : Set E} (hK : IsClosed K) {s : ℝ} (hs : 0 < s) (h : ∀ t ∈ Ico (0 : ℝ) s, X t ∈ K) :
    X s ∈ K := by
  have hlim : Tendsto X (𝓝[<] s) (𝓝 (X s)) := hX.continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds
  refine hK.mem_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hs] with u hu using h u ⟨hu.1.le, hu.2⟩

/-- **The exit point lies on the boundary**: if the solution starts in the closed set `K` and
exits by time `T₀ < H`, its position at the exit time is in `∂K`. -/
@[tmio T, powerlib_foundation] theorem pathExt_exitTime_mem_frontier
    (hBc : ∀ ω, Continuous fun t => B t ω) {L : ℝ≥0} {b : E → E} (hb : LipschitzWith L b)
    (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) {K : Set E} (hK : IsClosed K) (c : ℝ) {H : ℝ≥0}
    {T₀ : ℝ≥0} (hT₀ : T₀ < H) {ω : Ω}
    (h0 : pathExt (solMap b N x₀ (c • brownPath B hBc H ω)) 0 ∈ K)
    (hτ : exitTime b N x₀ K c B hBc ω ≤ T₀) :
    pathExt (solMap b N x₀ (c • brownPath B hBc H ω))
      (exitTime b N x₀ K c B hBc ω).toReal ∈ frontier K := by
  set X := pathExt (solMap b N x₀ (c • brownPath B hBc H ω)) with hX
  set τ := (exitTime b N x₀ K c B hBc ω).toReal with hτdef
  have hXc : Continuous X := LDP.continuous_pathExt _
  have hτtop : exitTime b N x₀ K c B hBc ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hτ
  have hτ0 : 0 ≤ τ := ENNReal.toReal_nonneg
  have hτT : τ ≤ T₀ := ENNReal.toReal_le_of_le_ofReal T₀.2 (by rwa [ENNReal.ofReal_coe_nnreal])
  have hT₀' : (T₀ : ℝ) < H := hT₀
  have hτH : τ ≤ H := hτT.trans hT₀'.le
  have hofτ : ENNReal.ofReal τ = exitTime b N x₀ K c B hBc ω := ENNReal.ofReal_toReal hτtop
  have hbefore : ∀ t ∈ Ico (0 : ℝ) τ, X t ∈ K :=
    (ofReal_le_exitTime_iff hBc hb N x₀ hK c hτ0 hτH ω).1 hofτ.le
  have hin : X τ ∈ K := by
    rcases eq_or_lt_of_le hτ0 with h | h
    · rw [← h]; exact h0
    · exact mem_of_forall_Ico_mem hXc hK h hbefore
  have hout : X τ ∈ closure Kᶜ := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδX⟩ := Metric.continuousAt_iff.1 hXc.continuousAt ε hε
    set δ' := min (δ / 2) ((H : ℝ) - T₀) with hδ'
    have hT₀'' := hT₀'
    have hδ'0 : 0 < δ' := lt_min (by positivity) (by linarith)
    have hlt : exitTime b N x₀ K c B hBc ω < ((τ + δ').toNNReal : ℝ≥0∞) := by
      rw [← hofτ, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (by positivity),
        ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      linarith
    obtain ⟨t, ht⟩ := exists_notMem_of_exitTime_lt hBc hb N x₀ c hlt
    have hle : (τ + δ').toNNReal ≤ H := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)]
      linarith [min_le_right (δ / 2) ((H : ℝ) - T₀)]
    have e := congrArg (fun φ => φ t) (restrictPath_solMap_brownPath hBc hb N x₀ c hle ω)
    have htle : (t : ℝ) ≤ τ + δ' := t.2.2.trans (le_of_eq (Real.coe_toNNReal _ (by positivity)))
    have hmem : (t : ℝ) ∈ Icc (0 : ℝ) H := ⟨t.2.1, htle.trans (by
      rw [← Real.coe_toNNReal (τ + δ') (by positivity)]; exact NNReal.coe_le_coe.mpr hle)⟩
    have hXt : X t ∉ K := by
      rw [hX, pathExt_of_mem _ hmem]
      rw [← e] at ht
      exact ht
    have hτt : τ ≤ t := by
      by_contra hc
      push Not at hc
      exact hXt (hbefore t ⟨t.2.1, hc⟩)
    refine ⟨X t, hXt, ?_⟩
    rw [dist_comm]
    refine hδX ?_
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith [min_le_left (δ / 2) ((H : ℝ) - T₀)]
  rw [frontier_eq_closure_inter_closure, hK.closure_eq]
  exact ⟨hin, hout⟩

/-- **The capped exit time is an optional time**: `{s ≤ min(τ_K, T₀)} ∈ 𝓕_s` (natural filtration of
`B`) for every `s`, `K` closed. -/
@[tmio T, powerlib_foundation] theorem measurableSet_le_min_exitTime
    (hm : ∀ t, StronglyMeasurable (B t)) (hBc : ∀ ω, Continuous fun t => B t ω) {L : ℝ≥0}
    {b : E → E} (hb : LipschitzWith L b) (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) {K : Set E}
    (hK : IsClosed K) (c : ℝ) {T₀ H : ℝ≥0} (hT₀ : T₀ ≤ H) (s : ℝ≥0) :
    MeasurableSet[Filtration.natural B hm s]
      {ω | (s : ℝ) ≤ (min (exitTime b N x₀ K c B hBc ω) T₀).toReal} := by
  set X : Ω → ℝ → E := fun ω => pathExt (solMap b N x₀ (c • brownPath B hBc H ω)) with hX
  rcases le_or_gt s T₀ with hs | hs
  · have e : {ω | (s : ℝ) ≤ (min (exitTime b N x₀ K c B hBc ω) T₀).toReal} =
        ⋂ q : ℚ, {ω | (q : ℝ) ∈ Ico (0 : ℝ) s → X ω q ∈ K} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      have hA := ofReal_le_exitTime_iff hBc hb N x₀ hK c (H := H) s.2
        (NNReal.coe_le_coe.mpr (hs.trans hT₀)) ω
      have hne : min (exitTime b N x₀ K c B hBc ω) (T₀ : ℝ≥0∞) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
      rw [← ENNReal.ofReal_le_iff_le_toReal hne, le_min_iff]
      have hsT : ENNReal.ofReal s ≤ T₀ := by
        rw [ENNReal.ofReal_coe_nnreal]; exact_mod_cast hs
      constructor
      · rintro ⟨h1, -⟩ q hq; exact hA.1 h1 q hq
      · intro h
        refine ⟨hA.2 fun t ht => ?_, hsT⟩
        by_contra hnot
        have hU : IsOpen {u : ℝ | X ω u ∉ K} :=
          hK.isOpen_compl.preimage (LDP.continuous_pathExt _)
        obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU t hnot
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min (lt_add_of_pos_right t hδ) ht.2)
        have hqs : (q : ℝ) < s := hq2.trans_le (min_le_right _ _)
        refine hball ?_ (h q ⟨ht.1.trans hq1.le, hqs⟩)
        have hqδ : (q : ℝ) < t + δ := hq2.trans_le (min_le_left _ _)
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]
        linarith
    rw [e]
    refine MeasurableSet.iInter fun q => ?_
    by_cases hq : (q : ℝ) ∈ Ico (0 : ℝ) s
    · have hset : {ω | (q : ℝ) ∈ Ico (0 : ℝ) s → X ω q ∈ K} = {ω | X ω q ∈ K} := by
        ext ω; simp [hq]
      rw [hset]
      rcases K.eq_empty_or_nonempty with hK0 | hK0
      · rw [hK0]; simp only [Set.mem_empty_iff_false, Set.ofPred_false]
        exact @MeasurableSet.empty _ (Filtration.natural B hm s)
      have hset' : {ω | X ω q ∈ K} = (fun ω => Metric.infDist (X ω q) K) ⁻¹' {0} := by
        ext ω; simp [hK.mem_iff_infDist_zero hK0]
      rw [hset']
      have hq' : (⟨q, hq.1⟩ : ℝ≥0) ≤ s := hq.2.le
      have := measurable_comp_solMap_natural' hb N x₀ c hm hBc H ⟨q, hq.1⟩
        (g := fun y => Metric.infDist y K) (Metric.continuous_infDist_pt K)
      exact (this.mono ((Filtration.natural B hm).mono hq') le_rfl) (measurableSet_singleton 0)
    · have hset : {ω | (q : ℝ) ∈ Ico (0 : ℝ) s → X ω q ∈ K} = Set.univ := by
        ext ω; simp [hq]
      rw [hset]; exact @MeasurableSet.univ _ (Filtration.natural B hm s)
  · have e : {ω | (s : ℝ) ≤ (min (exitTime b N x₀ K c B hBc ω) T₀).toReal} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      calc (min (exitTime b N x₀ K c B hBc ω) T₀).toReal ≤ (T₀ : ℝ≥0∞).toReal :=
            ENNReal.toReal_mono ENNReal.coe_ne_top (min_le_right _ _)
        _ = T₀ := rfl
        _ < s := hs
    rw [e]; exact @MeasurableSet.empty _ (Filtration.natural B hm s)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
/-- A nonnegative random time is measurable when every event `{s ≤ σ}` is. -/
@[tmio T, powerlib_foundation] theorem measurable_of_measurableSet_le {σ : Ω → ℝ}
    (hσ0 : ∀ ω, 0 ≤ σ ω) (h : ∀ s : ℝ≥0, MeasurableSet {ω | (s : ℝ) ≤ σ ω}) : Measurable σ := by
  refine measurable_of_Ici fun x => ?_
  rcases le_or_gt 0 x with hx | hx
  · exact h ⟨x, hx⟩
  · have : σ ⁻¹' Ici x = Set.univ := by
      ext ω; simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_univ, iff_true]
      linarith [hσ0 ω]
    rw [this]; exact MeasurableSet.univ

variable {P : Measure Ω}

/-- **The mean exit time solves `L u = −1`** (Dynkin's formula at the exit time): for the
additive-noise solution `x = S(x₀, c B)`, `n = c N(1)`, a closed set `K ∋ x₀` and a `C²` function
`u` with `|u|, ‖Du‖, ‖D²u‖, |Lu| ≤ C`, uniformly continuous `D²u`, `L u = −1` on `K` and `u = 0`
on `∂K`: `E τ_K = u(x₀)` (in particular `τ_K < ∞` almost surely). -/
@[tmio T, powerlib_foundation] theorem lintegral_exitTime_eq [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) {L : ℝ≥0} {b : E → E} (hb : LipschitzWith L b)
    (N : (Fin 1 → ℝ) →L[ℝ] E) {x₀ : E} (c : ℝ) {K : Set E} (hK : IsClosed K) (hx₀ : x₀ ∈ K)
    {u : E → ℝ} (hu : ContDiff ℝ 2 u) {C : ℝ}
    (hC : ∀ y, |u y| ≤ C ∧ ‖fderiv ℝ u y‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ u) y‖ ≤ C ∧
      |gen b (c • N (fun _ => 1)) u y| ≤ C)
    (huc : UniformContinuous (fderiv ℝ (fderiv ℝ u)))
    (hL : ∀ y ∈ K, gen b (c • N (fun _ => 1)) u y = -1) (h0 : ∀ y ∈ frontier K, u y = 0) :
    ∫⁻ ω, exitTime b N x₀ K c B hBc ω ∂P = ENNReal.ofReal (u x₀) := by
  set n := c • N (fun _ => 1) with hn
  set τ : Ω → ℝ≥0∞ := fun ω => exitTime b N x₀ K c B hBc ω with hτ
  have hCnn : 0 ≤ C := (abs_nonneg _).trans (hC 0).1
  -- the capped times `σ_k = min(τ, k + 1)`
  set T : ℕ → ℝ≥0 := fun k => ((k + 1 : ℕ) : ℝ≥0) with hT
  set σ : ℕ → Ω → ℝ := fun k ω => (min (τ ω) (T k)).toReal with hσ
  have hσ0 : ∀ k ω, 0 ≤ σ k ω := fun k ω => ENNReal.toReal_nonneg
  have hσT : ∀ k ω, σ k ω ≤ T k := fun k ω =>
    (ENNReal.toReal_mono ENNReal.coe_ne_top (min_le_right _ _)).trans_eq rfl
  have hσ_meas : ∀ k (s : ℝ≥0), MeasurableSet[Filtration.natural B hm s]
      {ω | (s : ℝ) ≤ σ k ω} := fun k s =>
    measurableSet_le_min_exitTime hm hBc hb N x₀ hK c (H := T k + 1) le_self_add s
  have hσm : ∀ k, Measurable (σ k) := fun k =>
    measurable_of_measurableSet_le (hσ0 k) fun s => (Filtration.natural B hm).le s _ (hσ_meas k s)
  have hσi : ∀ k, Integrable (σ k) P := fun k =>
    Integrable.of_bound (hσm k).aestronglyMeasurable (T k) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hσ0 k ω)]; exact hσT k ω)
  have hmin : ∀ k ω, min (τ ω) (T k) = ENNReal.ofReal (σ k ω) := fun k ω =>
    (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))).symm
  -- Dynkin's formula for each `k`, read pathwise
  have hkey : ∀ k, |(∫ ω, σ k ω ∂P) - u x₀| ≤ C / (k + 1) * (∫ ω, σ k ω ∂P) ∧
      (∫ ω, σ k ω ∂P) ≤ u x₀ + C := by
    intro k
    set H : ℝ≥0 := T k + 1 with hH
    have hTH : (T k : ℝ) < H := by rw [hH]; push_cast; linarith
    set X : Ω → ℝ → E := fun ω => pathExt (solMap b N x₀ (c • brownPath B hBc H ω)) with hX
    obtain ⟨hYi, hY⟩ := integral_dynkin (T := H) (T' := T k) hB hm hBc hb N x₀ c hu hC huc hTH
      (hσ0 k) (hσT k) (hσ_meas k)
    -- pathwise identities on `B₀ = 0`
    have hpath : ∀ᵐ ω ∂P, (u (X ω (σ k ω)) - ∫ v in (0 : ℝ)..σ k ω, gen b n u (X ω v)) =
        u (X ω (σ k ω)) + σ k ω ∧ |u (X ω (σ k ω))| ≤ C * σ k ω / (k + 1) := by
      filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
      have hX0 : X ω 0 = x₀ := pathExt_solMap_brownPath_zero hb N x₀ c hBc H hω
      have hσH : σ k ω ≤ H := (hσT k ω).trans hTH.le
      have hle : ENNReal.ofReal (σ k ω) ≤ τ ω := (hmin k ω) ▸ min_le_left _ _
      have hIco := (ofReal_le_exitTime_iff hBc hb N x₀ hK c (hσ0 k ω) hσH ω).1 hle
      have hIcc : ∀ v ∈ Icc (0 : ℝ) (σ k ω), X ω v ∈ K := by
        intro v hv
        rcases eq_or_lt_of_le hv.2 with hvs | hvs
        · rcases eq_or_lt_of_le (hσ0 k ω) with h0' | h0'
          · rw [hvs, ← h0', hX0]; exact hx₀
          · rw [hvs]; exact mem_of_forall_Ico_mem (LDP.continuous_pathExt _) hK h0' hIco
        · exact hIco v ⟨hv.1, hvs⟩
      have hint : ∫ v in (0 : ℝ)..σ k ω, gen b n u (X ω v) = -σ k ω := by
        rw [intervalIntegral.integral_congr (g := fun _ => (-1 : ℝ)) fun v hv => by
          rw [uIcc_of_le (hσ0 k ω)] at hv; exact hL _ (hIcc v hv)]
        simp
      refine ⟨by rw [hint]; ring, ?_⟩
      by_cases hτk : τ ω ≤ T k
      · have hfr := pathExt_exitTime_mem_frontier hBc hb N x₀ hK c hTH (ω := ω)
          (by rw [show pathExt (solMap b N x₀ (c • brownPath B hBc H ω)) 0 = x₀ from hX0]
              exact hx₀) hτk
        have hσe : σ k ω = (τ ω).toReal := by simp only [hσ, min_eq_left hτk]
        rw [hσe, h0 _ hfr, abs_zero]
        positivity
      · push Not at hτk
        have hσe : σ k ω = T k := by
          simp only [hσ, min_eq_right hτk.le]; rfl
        rw [hσe]
        have hT1 : ((T k : ℝ≥0) : ℝ) = k + 1 := by simp [hT]
        rw [hT1, mul_div_assoc, div_self (by positivity), mul_one]
        exact (hC _).1
    have hYeq : (fun ω => u (X ω (σ k ω)) - ∫ v in (0 : ℝ)..σ k ω, gen b n u (X ω v)) =ᵐ[P]
        fun ω => u (X ω (σ k ω)) + σ k ω := hpath.mono fun ω h => h.1
    have hUi : Integrable (fun ω => u (X ω (σ k ω))) P :=
      ((hYi.congr hYeq).sub (hσi k)).congr (ae_of_all _ fun ω => by simp)
    have hsplit : ∫ ω, σ k ω ∂P = u x₀ - ∫ ω, u (X ω (σ k ω)) ∂P := by
      rw [← hY, integral_congr_ae hYeq, integral_add hUi (hσi k)]; ring
    have hUb : |∫ ω, u (X ω (σ k ω)) ∂P| ≤ C / (k + 1) * ∫ ω, σ k ω ∂P := by
      refine (abs_integral_le_integral_abs).trans ?_
      rw [← integral_const_mul]
      refine integral_mono_ae hUi.abs ((hσi k).const_mul _) (hpath.mono fun ω h => ?_)
      show |u (X ω (σ k ω))| ≤ C / (k + 1) * σ k ω
      rw [div_mul_eq_mul_div]
      exact h.2
    have hUC : |∫ ω, u (X ω (σ k ω)) ∂P| ≤ C := by
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ ω, |u (X ω (σ k ω))| ∂P ≤ ∫ _, C ∂P :=
            integral_mono hUi.abs (integrable_const _) fun ω => (hC _).1
        _ = C := by simp
    refine ⟨?_, ?_⟩
    · rw [hsplit, sub_sub_cancel_left, abs_neg, ← hsplit]; exact hUb
    · rw [hsplit]; linarith [neg_abs_le (∫ ω, u (X ω (σ k ω)) ∂P)]
  -- `E σ_k → u(x₀)`
  have hconv : Tendsto (fun k : ℕ => ∫ ω, σ k ω ∂P) atTop (𝓝 (u x₀)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k₀, hk₀⟩ := exists_nat_gt (C * (|u x₀| + C) / ε)
    refine ⟨k₀, fun k hk => ?_⟩
    rw [Real.dist_eq]
    obtain ⟨h1, h2⟩ := hkey k
    have hk1 : (0 : ℝ) < k + 1 := by positivity
    have hpos : 0 ≤ ∫ ω, σ k ω ∂P := integral_nonneg (hσ0 k)
    have hb2 : C / (k + 1) * (∫ ω, σ k ω ∂P) ≤ C / (k + 1) * (|u x₀| + C) :=
      mul_le_mul_of_nonneg_left (h2.trans (by linarith [le_abs_self (u x₀)])) (by positivity)
    have hk' : C * (|u x₀| + C) / ε < k + 1 := by
      have : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have : C / (k + 1) * (|u x₀| + C) < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hk1]
      rw [div_lt_iff₀ hε] at hk'
      linarith
    linarith
  -- monotone convergence
  have hmono : ∀ ω, Monotone fun k => ENNReal.ofReal (σ k ω) := by
    intro ω i j hij
    show ENNReal.ofReal (σ i ω) ≤ ENNReal.ofReal (σ j ω)
    rw [← hmin, ← hmin]
    refine min_le_min le_rfl ?_
    simp only [hT]
    exact_mod_cast Nat.add_le_add_right hij 1
  have hsup : ∀ ω, ⨆ k, ENNReal.ofReal (σ k ω) = τ ω := by
    intro ω
    simp_rw [← hmin]
    rw [← inf_iSup_eq]
    have : ⨆ k, ((T k : ℝ≥0) : ℝ≥0∞) = ⊤ := by
      refine top_unique ?_
      rw [← ENNReal.iSup_natCast]
      refine iSup_le fun k => le_iSup_of_le k ?_
      simp only [hT]
      exact_mod_cast Nat.le_succ k
    rw [this, inf_top_eq]
  have hlin : ∫⁻ ω, τ ω ∂P = ⨆ k, ENNReal.ofReal (∫ ω, σ k ω ∂P) := by
    simp_rw [← hsup]
    rw [lintegral_iSup' (fun k => (hσm k).ennreal_ofReal.aemeasurable)
      (ae_of_all _ hmono)]
    refine iSup_congr fun k => ?_
    exact (ofReal_integral_eq_lintegral_ofReal (hσi k) (ae_of_all _ (hσ0 k))).symm
  rw [hlin]
  have hmono' : Monotone fun k => ENNReal.ofReal (∫ ω, σ k ω ∂P) := by
    intro i j hij
    refine ENNReal.ofReal_le_ofReal (integral_mono (hσi i) (hσi j) fun ω => ?_)
    have := hmono ω hij
    exact (ENNReal.ofReal_le_ofReal_iff (hσ0 j ω)).1 this
  exact tendsto_nhds_unique (tendsto_atTop_iSup hmono') (ENNReal.tendsto_ofReal hconv)

omit [CompleteSpace E] in
/-- The generator of a compactly supported `C²` function has compact support. -/
@[tmio T, powerlib_foundation] theorem hasCompactSupport_gen {b : E → E} (n : E) {φ : E → ℝ}
    (hcs : HasCompactSupport φ) : HasCompactSupport (gen b n φ) := by
  refine hcs.mono' fun y hy => ?_
  by_contra hnot
  have h1 : fderiv ℝ φ y = 0 := by
    by_contra h; exact hnot (support_fderiv_subset ℝ h)
  have h2 : fderiv ℝ (fderiv ℝ φ) y = 0 := by
    by_contra h; exact hnot (tsupport_fderiv_subset ℝ (support_fderiv_subset ℝ h))
  apply hy
  simp only [gen, h1, h2, _root_.zero_apply, mul_zero, add_zero]

omit [CompleteSpace E] in
/-- **Bounds from compact support**: a `C²` function with compact support has bounded
`φ, Dφ, D²φ, Lφ` (continuous `b`). -/
@[tmio T, powerlib_foundation] theorem exists_bound_of_hasCompactSupport {b : E → E}
    (hb : Continuous b) (n : E) {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hcs : HasCompactSupport φ) :
    ∃ C, ∀ y, |φ y| ≤ C ∧ ‖fderiv ℝ φ y‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ C ∧
      |gen b n φ y| ≤ C := by
  have hD1c : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have hD2c : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hcs1 : HasCompactSupport fun y => ‖fderiv ℝ φ y‖ := by
    refine hcs.mono' fun y hy => ?_
    by_contra hnot
    have h1 : fderiv ℝ φ y = 0 := by
      by_contra h; exact hnot (support_fderiv_subset ℝ h)
    exact hy (by simp only [h1, norm_zero])
  have hcs2 : HasCompactSupport fun y => ‖fderiv ℝ (fderiv ℝ φ) y‖ := by
    refine hcs.mono' fun y hy => ?_
    by_contra hnot
    have h2 : fderiv ℝ (fderiv ℝ φ) y = 0 := by
      by_contra h; exact hnot (tsupport_fderiv_subset ℝ (support_fderiv_subset ℝ h))
    exact hy (by show ‖fderiv ℝ (fderiv ℝ φ) y‖ = 0; rw [h2]; exact ContinuousLinearMap.opNorm_zero)
  obtain ⟨C0, h0⟩ := hφ.continuous.bounded_above_of_compact_support hcs
  have hn1 : Continuous fun y => ‖fderiv ℝ φ y‖ :=
    Continuous.norm (f := fderiv ℝ φ) (by exact hD1c)
  have hn2 : Continuous fun y => ‖fderiv ℝ (fderiv ℝ φ) y‖ :=
    Continuous.norm (f := fderiv ℝ (fderiv ℝ φ)) (by exact hD2c)
  obtain ⟨C1, h1'⟩ := hn1.bounded_above_of_compact_support hcs1
  obtain ⟨C2, h2'⟩ := hn2.bounded_above_of_compact_support hcs2
  have h1 : ∀ y, ‖fderiv ℝ φ y‖ ≤ C1 := fun y =>
    (le_of_eq (Real.norm_of_nonneg (norm_nonneg _)).symm).trans (h1' y)
  have h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ C2 := fun y =>
    (le_of_eq (Real.norm_of_nonneg (ContinuousLinearMap.opNorm_nonneg _)).symm).trans (h2' y)
  obtain ⟨C3, h3⟩ := (continuous_gen hb n hφ).bounded_above_of_compact_support
    (hasCompactSupport_gen n hcs)
  refine ⟨max (max C0 C1) (max C2 C3), fun y => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [← Real.norm_eq_abs]; exact (h0 y).trans (le_max_left _ _ |>.trans (le_max_left _ _))
  · exact (h1 y).trans (le_max_right _ _ |>.trans (le_max_left _ _))
  · exact (h2 y).trans (le_max_left _ _ |>.trans (le_max_right _ _))
  · rw [← Real.norm_eq_abs]; exact (h3 y).trans (le_max_right _ _ |>.trans (le_max_right _ _))

omit [CompleteSpace E] in
/-- A compactly supported `C²` function has uniformly continuous second derivative. -/
@[tmio T, powerlib_foundation] theorem uniformContinuous_fderiv_fderiv {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hcs : HasCompactSupport φ) :
    UniformContinuous (fderiv ℝ (fderiv ℝ φ)) :=
  ((hcs.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).uniformContinuous_of_continuous
    ((hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num))

/-- **Mean exit time of a compact set** (finite dimension): if `u ∈ C²` solves `L u = −1` on the
compact `K ∋ x₀` and `u = 0` on `∂K`, then `E τ_K = u(x₀)` (no global bounds: `u` is cut off
outside a ball containing `K`). -/
@[tmio T, powerlib_foundation] theorem lintegral_exitTime_eq_of_isCompact [FiniteDimensional ℝ E]
    [IsProbabilityMeasure P] (hB : IsPreBrownianReal B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) {L : ℝ≥0} {b : E → E} (hb : LipschitzWith L b)
    (N : (Fin 1 → ℝ) →L[ℝ] E) {x₀ : E} (c : ℝ) {K : Set E} (hK : IsCompact K) (hx₀ : x₀ ∈ K)
    {u : E → ℝ} (hu : ContDiff ℝ 2 u) (hL : ∀ y ∈ K, gen b (c • N (fun _ => 1)) u y = -1)
    (h0 : ∀ y ∈ frontier K, u y = 0) :
    ∫⁻ ω, exitTime b N x₀ K c B hBc ω ∂P = ENNReal.ofReal (u x₀) := by
  set n := c • N (fun _ => 1) with hn
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  set R' := max R 0 with hR'
  have hR'0 : 0 ≤ R' := le_max_right _ _
  let f : ContDiffBump (0 : E) := ⟨R' + 1, R' + 2, by positivity, by linarith⟩
  set φ : E → ℝ := fun y => f y * u y with hφdef
  have hφ : ContDiff ℝ 2 φ := f.contDiff.mul hu
  have hcs : HasCompactSupport φ := f.hasCompactSupport.mul_right
  have hU : ∀ y ∈ Metric.ball (0 : E) (R' + 1), φ y = u y := fun y hy => by
    simp only [hφdef, f.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), one_mul]
  have hKU : K ⊆ Metric.ball (0 : E) (R' + 1) := fun y hy => by
    have := Metric.mem_closedBall.1 (hR hy)
    rw [Metric.mem_ball]; linarith [le_max_left R 0]
  have hev : ∀ y ∈ K, φ =ᶠ[𝓝 y] u := fun y hy =>
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds (hKU hy)) hU
  have hgen : ∀ y ∈ K, gen b n φ y = gen b n u y := by
    intro y hy
    have e1 := (hev y hy).fderiv_eq (𝕜 := ℝ)
    have e2 := ((hev y hy).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    simp only [gen, e1, e2]
  obtain ⟨C, hC⟩ := exists_bound_of_hasCompactSupport hb.continuous n hφ hcs
  have huc := uniformContinuous_fderiv_fderiv hφ hcs
  have hfr : frontier K ⊆ K := hK.isClosed.frontier_subset
  have := lintegral_exitTime_eq (P := P) hB hm hBc hb N c hK.isClosed hx₀ hφ hC huc
    (fun y hy => (hgen y hy).trans (hL y hy))
    (fun y hy => (hU y (hKU (hfr hy))).trans (h0 y hy))
  rw [this, hU x₀ (hKU hx₀)]

/-! ## One dimension: the generator `μ φ' + ½ σ² φ''`, free diffusion between two points -/

/-- **In one dimension the generator is `L φ = b φ' + ½ n² φ''`**, i.e. the Fokker–Planck
generator expression `FP.gen1 b (n²)`. -/
@[tmio T, powerlib_foundation] theorem gen_eq_gen1 {b : ℝ → ℝ} (n : ℝ) {u u1 u2 : ℝ → ℝ}
    (h1 : ∀ y, HasDerivAt u (u1 y) y) (h2 : ∀ y, HasDerivAt u1 (u2 y) y) (y : ℝ) :
    gen b n u y = FP.gen1 b (fun _ => n ^ 2) u y ∧ gen b n u y = b y * u1 y + n ^ 2 / 2 * u2 y := by
  have hd1 : deriv u = u1 := funext fun z => (h1 z).deriv
  have hf1 : fderiv ℝ u = fun z => u1 z • ContinuousLinearMap.id ℝ ℝ := by
    funext z
    rw [(h1 z).hasFDerivAt.fderiv]
    ext; simp
  have hf2 : fderiv ℝ (fderiv ℝ u) y = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      (u2 y • ContinuousLinearMap.id ℝ ℝ) := by
    rw [hf1]
    exact ((h2 y).smul_const (ContinuousLinearMap.id ℝ ℝ)).hasFDerivAt.fderiv
  have e : gen b n u y = b y * u1 y + n ^ 2 / 2 * u2 y := by
    unfold gen
    rw [hf2, hf1]
    simp
    ring
  refine ⟨?_, e⟩
  rw [e, FP.gen1, hd1, (h2 y).deriv]

/-- **Mean exit time of Brownian motion from an interval**: for `x = x₀ + √(2D) B`,
`E τ_{[a, b]} = (x₀ − a)(b − x₀)/(2D)` — the free-diffusion solution `MFPT.mfpt_free_diffusion`
of `D m'' = −1`, `m(a) = m(b) = 0`, is the mean exit time. -/
@[tmio T, powerlib_foundation] theorem lintegral_exitTime_Icc_brownian [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) {D a b x₀ : ℝ} (hD : 0 < D) (hx₀ : x₀ ∈ Icc a b) :
    ∫⁻ ω, exitTime (fun _ : ℝ => (0 : ℝ)) (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin 1 => ℝ) 0) x₀ (Icc a b) (√(2 * D)) B hBc ω ∂P =
      ENNReal.ofReal ((x₀ - a) * (b - x₀) / (2 * D)) := by
  have hab : a ≤ b := hx₀.1.trans hx₀.2
  have hfd := fun θ => MFPT.mfpt_free_diffusion (a := a) (b := b) hD.ne' θ
  have hN : (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
      (fun _ => (1 : ℝ)) = 1 := rfl
  have hsq : √(2 * D) ^ 2 = 2 * D := Real.sq_sqrt (by positivity)
  have hu : ContDiff ℝ 2 fun x : ℝ => (x - a) * (b - x) / (2 * D) := by fun_prop
  refine lintegral_exitTime_eq_of_isCompact (P := P) hB hm hBc (LipschitzWith.const 0) _
    (√(2 * D)) isCompact_Icc hx₀ hu ?_ ?_
  · intro y _
    have := (gen_eq_gen1 (b := fun _ : ℝ => (0 : ℝ)) (√(2 * D) • (1 : ℝ))
      (fun θ => (hfd θ).1) (fun θ => (hfd θ).2.1) y).2
    rw [hN, this, smul_eq_mul, mul_one, hsq, zero_mul, zero_add]
    have := (hfd y).2.2.1
    rw [show 2 * D / 2 = D by ring]
    exact this
  · intro y hy
    rw [frontier_Icc hab] at hy
    rcases hy with rfl | rfl
    · exact (hfd 0).2.2.2.1
    · exact (hfd 0).2.2.2.2

end Ito
end powerlib.Stochastic
