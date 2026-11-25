import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.Brownian
import theorem.Stochastic.SchilderRate
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! # Gaussian maximal inequality, the path-space version of Brownian motion, exponential
equivalence of its polygonal interpolations

For a Brownian motion `B` (Mathlib's `IsBrownianReal`: the laws of a Brownian motion and almost
surely continuous paths) on `[0, T]`:
* a measurable `C([0, T])`-valued version `X` (`X(ω)(t) = B_t(ω)` for almost every `ω`, all `t`);
* the Gaussian maximal inequality `P(max_{k ≤ N} B_{t_k} ≥ c) ≤ e^{−c²/(2τ)}` (Doob's maximal
  inequality for the exponential martingale `exp(θ B_t − θ² t/2)` on the grid, `θ = c/τ`), and its
  path form `P(sup_{s ∈ [a, a+Δ]} |X_s − X_a| > c) ≤ 2 e^{−c²/(2Δ)}` (dyadic grids and
  continuity);
* the exponential equivalence of `√ε X` and its polygonal interpolations `√ε π_n X`:
  `P(‖√ε π_n X − √ε X‖ > δ) ≤ 2n e^{−δ² n/(8 ε T)}`.

Scope.
* Probability theory, not an engineering result. Time `ℝ≥0` as in Mathlib's Brownian motion; paths
  in `C([0, T], ℝ)` written `C([0, T], Fin 1 → ℝ)`, `T > 0`, uniform mesh `Δ = T/n`.
* No Itô calculus: the exponential martingale is `Stochastic.BM.martingale_brownian_exp`
  (independence of increments) on a measurable modification of `B`.

Source: D. Revuz, M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed. (1999),
Ch. II §1 (Doob's maximal inequality, exponential martingale bound); A. Dembo, O. Zeitouni,
*Large Deviations Techniques and Applications*, 2nd ed. (1998), proof of Thm 5.2.3 (exponential
equivalence of the polygonal approximations).

Results.
* `measure_exists_le_brownian` (grid maximal inequality, pre-Brownian motion),
  `measure_exists_abs_lt_le` (two-sided, on a step, through a version), `exists_version`
  (a measurable path-space version of a Brownian motion, starting at `0`),
  `measure_dist_polyInterp_le` (exponential equivalence bound),
  `expApprox_polyInterp` (the bound in the form of `isLDP_of_expApprox`).
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped ENNReal NNReal Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

/-- **Gaussian maximal inequality on a grid**: for a pre-Brownian motion, times
`t_0 ≤ t_1 ≤ … ≤ τ` and `c ≥ 0`, `P(∃ k ≤ N, B_{t_k} ≥ c) ≤ e^{−c²/(2τ)}` (Doob's maximal
inequality for the exponential martingale with `θ = c/τ`). -/
@[tmio T, powerlib_foundation] theorem measure_exists_le_brownian (hB : IsPreBrownianReal B P)
    {τ : ℝ≥0} (hτ : 0 < (τ : ℝ)) (t : ℕ → ℝ≥0) (ht : Monotone t) (htτ : ∀ k, t k ≤ τ) (N : ℕ)
    {c : ℝ} (hc : 0 ≤ c) :
    P {ω | ∃ k ≤ N, c ≤ B (t k) ω} ≤ ENNReal.ofReal (Real.exp (-(c ^ 2) / (2 * τ))) := by
  set B' : ℝ≥0 → Ω → ℝ := fun s => (hB.aemeasurable s).mk (B s) with hB'def
  have hBB' : ∀ s, B s =ᵐ[P] B' s := fun s => (hB.aemeasurable s).ae_eq_mk
  have hB' : IsPreBrownianReal B' P := hB.congr hBB'
  have hm : ∀ s, StronglyMeasurable (B' s) := fun s =>
    (hB.aemeasurable s).measurable_mk.stronglyMeasurable
  set θ := c / τ with hθ
  have hθ0 : 0 ≤ θ := div_nonneg hc hτ.le
  have hM := Stochastic.BM.martingale_brownian_exp hB' hm θ
  set ℱ := Filtration.natural B' hm
  let 𝒢 : Filtration ℕ mΩ := ⟨fun k => ℱ (t k), fun i j hij => ℱ.mono (ht hij), fun k => ℱ.le _⟩
  set f : ℕ → Ω → ℝ := fun k ω => Real.exp (θ * B' (t k) ω - θ ^ 2 * (t k : ℝ) / 2) with hf
  have hfm : Martingale f 𝒢 P :=
    ⟨fun k => hM.1 (t k), fun i j hij => hM.2 (t i) (t j) (ht hij)⟩
  have hf0 : 0 ≤ f := fun k ω => (Real.exp_pos _).le
  set lam := Real.exp (c ^ 2 / (2 * τ)) with hlam
  have hlam0 : 0 ≤ lam := (Real.exp_pos _).le
  have hmax := maximal_ineq hfm.submartingale hf0 (ε := ⟨lam, hlam0⟩) N
  set S := {ω | ((⟨lam, hlam0⟩ : ℝ≥0) : ℝ) ≤
    (range (N + 1)).sup' nonempty_range_add_one fun k => f k ω} with hS
  have hint : ∫ ω, f N ω ∂P = 1 := by
    have h1 : (fun ω => f N ω) = fun ω => Real.exp (θ * B' (t N) ω) *
        Real.exp (-(θ ^ 2 * (t N : ℝ) / 2)) := by
      funext ω; rw [hf, ← Real.exp_add]; ring_nf
    rw [h1, integral_mul_const, Stochastic.BM.integral_exp_brownian hB', ← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hle1 : ENNReal.ofReal lam * P S ≤ 1 := by
    have h2 : ∫ ω in S, f N ω ∂P ≤ ∫ ω, f N ω ∂P :=
      setIntegral_le_integral (hfm.integrable N) (Eventually.of_forall fun ω => hf0 N ω)
    have h3 := hmax.trans (ENNReal.ofReal_le_ofReal (h2.trans hint.le))
    rw [ENNReal.ofReal_one] at h3
    rw [ENNReal.ofReal_eq_coe_nnreal hlam0]
    exact h3
  have hsub : {ω | ∃ k ≤ N, c ≤ B (t k) ω} ≤ᵐ[P] S := by
    have hae : ∀ᵐ ω ∂P, ∀ k, B (t k) ω = B' (t k) ω := ae_all_iff.mpr fun k => hBB' (t k)
    filter_upwards [hae] with ω hω hmem
    obtain ⟨k, hk, hck⟩ := hmem
    show lam ≤ _
    refine le_trans ?_ (Finset.le_sup' (fun k => f k ω)
      (Finset.mem_range.mpr (show k < N + 1 by omega)))
    simp only [hf, hlam]
    refine Real.exp_le_exp.mpr ?_
    rw [hω k] at hck
    have h4 : θ * c ≤ θ * B' (t k) ω := mul_le_mul_of_nonneg_left hck hθ0
    have h5 : θ ^ 2 * (t k : ℝ) ≤ θ ^ 2 * τ :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast htτ k) (sq_nonneg _)
    have h6 : c ^ 2 / (2 * τ) = θ * c - θ ^ 2 * τ / 2 := by
      rw [hθ]; field_simp; ring
    rw [h6]
    linarith
  refine (measure_mono_ae hsub).trans ?_
  rw [← ofReal_measureReal] at hle1 ⊢
  rw [← ENNReal.ofReal_mul hlam0, ENNReal.ofReal_le_one] at hle1
  refine ENNReal.ofReal_le_ofReal ?_
  rw [neg_div, Real.exp_neg, ← hlam, inv_eq_one_div, le_div_iff₀ (Real.exp_pos _)]
  linarith [mul_comm lam (P.real S)]

/-- Dyadic times `(min(j, 2^m)/2^m) Δ` of `[0, Δ]`. -/
private def dyadic (Δ : ℝ≥0) (m j : ℕ) : ℝ≥0 := ((min j (2 ^ m) : ℕ) / (2 ^ m : ℝ≥0)) * Δ

@[tmio T, powerlib_foundation] private theorem dyadic_mono (Δ : ℝ≥0) (m : ℕ) :
    Monotone (dyadic Δ m) := fun i j hij => by
  unfold dyadic
  gcongr

@[tmio T, powerlib_foundation] private theorem dyadic_le (Δ : ℝ≥0) (m j : ℕ) :
    dyadic Δ m j ≤ Δ := by
  unfold dyadic
  refine mul_le_of_le_one_left (zero_le) ?_
  rw [div_le_one (by positivity)]
  exact_mod_cast min_le_right _ _

/-- **Two-sided maximal inequality on a step, through a version**: if `X` is a path-space version
of the pre-Brownian motion `B` and `[a, a + Δ] ⊆ [0, T]`, then
`P(∃ s ∈ [a, a + Δ], |X_s − X_a| > c) ≤ 2 e^{−c²/(2Δ)}` (`c ≥ 0`). -/
@[tmio T, powerlib_foundation] theorem measure_exists_abs_lt_le (hB : IsPreBrownianReal B P)
    {X : Ω → C(Icc (0 : ℝ) T, Fin 1 → ℝ)}
    (hXB : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T, X ω t 0 = B ⟨t, t.2.1⟩ ω) {a Δ : ℝ} (ha : 0 ≤ a)
    (hΔ : 0 < Δ) (haT : a + Δ ≤ T) {c : ℝ} (hc : 0 ≤ c) :
    P {ω | ∃ s ∈ Icc a (a + Δ), c < |pathExt (X ω) s 0 - pathExt (X ω) a 0|} ≤
      ENNReal.ofReal (2 * Real.exp (-(c ^ 2) / (2 * Δ))) := by
  set a' : ℝ≥0 := ⟨a, ha⟩
  set Δ' : ℝ≥0 := ⟨Δ, hΔ.le⟩
  set E : ℕ → Set Ω := fun m => {ω | ∃ j ≤ 2 ^ m,
    c < |pathExt (X ω) (a + dyadic Δ' m j) 0 - pathExt (X ω) a 0|} with hE
  have hmemT : ∀ m j, a + (dyadic Δ' m j : ℝ) ∈ Icc (0 : ℝ) T := fun m j =>
    ⟨by positivity, by have := dyadic_le Δ' m j; have : (dyadic Δ' m j : ℝ) ≤ Δ := this; linarith⟩
  have hamem : a ∈ Icc (0 : ℝ) T := ⟨ha, by linarith⟩
  -- the path event is the union of the dyadic events
  have hsub : {ω | ∃ s ∈ Icc a (a + Δ), c < |pathExt (X ω) s 0 - pathExt (X ω) a 0|} ⊆
      ⋃ m, E m := by
    rintro ω ⟨s, hs, hcs⟩
    have hφ : Continuous fun r => pathExt (X ω) r 0 - pathExt (X ω) a 0 :=
      ((continuous_apply 0).comp (continuous_pathExt (X ω))).sub continuous_const
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp
      ((isOpen_lt continuous_const hφ.abs).mem_nhds hcs)
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (Δ / ρ) (by norm_num : (1 : ℝ) < 2)
    set lam := (s - a) / Δ with hlam
    have hl0 : 0 ≤ lam := div_nonneg (by linarith [hs.1]) hΔ.le
    have hl1 : lam ≤ 1 := by rw [div_le_one hΔ]; linarith [hs.2]
    set j := ⌊lam * 2 ^ m⌋₊ with hj
    have hj1 : (j : ℝ) ≤ lam * 2 ^ m := Nat.floor_le (by positivity)
    have hj2 : lam * 2 ^ m < j + 1 := Nat.lt_floor_add_one _
    have hjm : j ≤ 2 ^ m := by
      have : (j : ℝ) ≤ 2 ^ m := hj1.trans (by nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) m])
      exact_mod_cast this
    have hdy : (dyadic Δ' m j : ℝ) = j / 2 ^ m * Δ := by
      have hΔ'c : (Δ' : ℝ) = Δ := rfl
      rw [dyadic, min_eq_left hjm]
      push_cast
      rw [hΔ'c]
    refine mem_iUnion.mpr ⟨m, j, hjm, ?_⟩
    have hin := hball (show a + (dyadic Δ' m j : ℝ) ∈ Metric.ball s ρ from by
      rw [Metric.mem_ball, Real.dist_eq, hdy]
      have h2m : (0 : ℝ) < 2 ^ m := by positivity
      have e : a + j / 2 ^ m * Δ - s = Δ * ((j - lam * 2 ^ m) / 2 ^ m) := by
        rw [hlam]; field_simp; ring
      rw [e, abs_mul, abs_of_pos hΔ, abs_div, abs_of_pos h2m]
      have h3 : |(j : ℝ) - lam * 2 ^ m| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      calc Δ * (|(j : ℝ) - lam * 2 ^ m| / 2 ^ m) ≤ Δ * (1 / 2 ^ m) := by gcongr
        _ < ρ := by
          rw [mul_one_div, div_lt_iff₀ h2m]
          rw [div_lt_iff₀ hρ] at hm
          linarith)
    exact hin
  -- the dyadic events increase
  have hmono : Monotone E := by
    refine monotone_nat_of_le_succ fun m ω hω => ?_
    obtain ⟨j, hj, hcj⟩ := hω
    refine ⟨2 * j, by rw [pow_succ]; omega, ?_⟩
    have e : dyadic Δ' (m + 1) (2 * j) = dyadic Δ' m j := by
      have h1 : 2 * j ≤ 2 ^ (m + 1) := by rw [pow_succ]; omega
      unfold dyadic
      rw [min_eq_left h1, min_eq_left hj, pow_succ]
      push_cast
      field_simp
    rwa [e]
  -- each dyadic event is bounded
  have hshift := hB.shift a'
  have hneg := hshift.neg
  have hbound : ∀ m, P (E m) ≤ ENNReal.ofReal (2 * Real.exp (-(c ^ 2) / (2 * Δ))) := by
    intro m
    have hΔ' : 0 < (Δ' : ℝ) := hΔ
    have h1 := measure_exists_le_brownian hshift hΔ' (dyadic Δ' m) (dyadic_mono Δ' m)
      (dyadic_le Δ' m) (2 ^ m) hc
    have h2 := measure_exists_le_brownian hneg hΔ' (dyadic Δ' m) (dyadic_mono Δ' m)
      (dyadic_le Δ' m) (2 ^ m) hc
    have hae : E m ≤ᵐ[P] {ω | ∃ k ≤ 2 ^ m, c ≤ B (a' + dyadic Δ' m k) ω - B a' ω} ∪
        {ω | ∃ k ≤ 2 ^ m, c ≤ (-fun t ω => B (a' + t) ω - B a' ω) (dyadic Δ' m k) ω} := by
      filter_upwards [hXB] with ω hω hmem
      obtain ⟨k, hk, hck⟩ := hmem
      rw [pathExt_of_mem _ (hmemT m k), pathExt_of_mem _ hamem, hω, hω] at hck
      have e1 : (⟨(⟨a + (dyadic Δ' m k : ℝ), hmemT m k⟩ : Icc (0 : ℝ) T),
          (hmemT m k).1⟩ : ℝ≥0) = a' + dyadic Δ' m k := rfl
      have e2 : (⟨(⟨a, hamem⟩ : Icc (0 : ℝ) T), hamem.1⟩ : ℝ≥0) = a' := rfl
      rw [e1, e2] at hck
      rcases lt_abs.mp hck with h | h
      · exact Or.inl ⟨k, hk, h.le⟩
      · exact Or.inr ⟨k, hk, by simp only [Pi.neg_apply]; linarith⟩
    calc P (E m) ≤ _ := measure_mono_ae hae
      _ ≤ _ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (-(c ^ 2) / (2 * Δ))) +
          ENNReal.ofReal (Real.exp (-(c ^ 2) / (2 * Δ))) := add_le_add h1 h2
      _ = _ := by
          rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
          congr 1
          ring
  calc _ ≤ P (⋃ m, E m) := measure_mono hsub
    _ = ⨆ m, P (E m) := hmono.measure_iUnion
    _ ≤ _ := iSup_le hbound

omit [IsProbabilityMeasure P] in
/-- **A path-space version of a Brownian motion**: if `B` has almost surely continuous paths, there
is a measurable `X : Ω → C([0, T])` with `X(ω)(0) = 0` for every `ω` and `X(ω)(t) = B_t(ω)` for
almost every `ω` and every `t` (`B` on a full-measure measurable set, `0` elsewhere; measurable as
the limit of its polygonal interpolations). -/
@[tmio T, powerlib_foundation] theorem exists_version (hB : IsBrownianReal B P)
    (hT : 0 < (T : ℝ)) [MeasurableSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)]
    [BorelSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)] :
    ∃ X : Ω → C(Icc (0 : ℝ) T, Fin 1 → ℝ), Measurable X ∧ (∀ ω, pathExt (X ω) 0 0 = 0) ∧
      ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T, X ω t 0 = B ⟨t, t.2.1⟩ ω := by
  set g : ℕ → ℕ → Ω → ℝ := fun n j => (hB.aemeasurable (node T n j)).mk _ with hg
  have hgm : ∀ n j, Measurable (g n j) := fun n j => (hB.aemeasurable _).measurable_mk
  set N₁ := ⋃ (n : ℕ) (j : ℕ), {ω | B (node T n j) ω ≠ g n j ω} with hN₁
  set N₂ := {ω | ¬ Continuous fun t => B t ω} with hN₂
  set N₃ := {ω | B 0 ω ≠ 0} with hN₃
  have h1 : P N₁ = 0 := measure_iUnion_null fun n => measure_iUnion_null fun j =>
    (hB.aemeasurable (node T n j)).ae_eq_mk
  have h2 : P N₂ = 0 := hB.cont
  have h3 : P N₃ = 0 := hB.eval_zero_ae_eq_zero
  set S := (toMeasurable P (N₁ ∪ N₂ ∪ N₃))ᶜ with hS
  have hSm : MeasurableSet S := (measurableSet_toMeasurable _ _).compl
  have hSae : ∀ᵐ ω ∂P, ω ∈ S := by
    rw [ae_iff]
    simp only [hS, mem_compl_iff, not_not, ofPred_mem_eq, measure_toMeasurable]
    exact measure_union_null (measure_union_null h1 h2) h3
  have hSgood : ∀ ω ∈ S, ω ∉ N₁ ∧ ω ∉ N₂ ∧ ω ∉ N₃ := fun ω hω => by
    have := fun h => hω (subset_toMeasurable _ _ h)
    exact ⟨fun h => this (Or.inl (Or.inl h)), fun h => this (Or.inl (Or.inr h)),
      fun h => this (Or.inr h)⟩
  have hcont : ∀ ω ∈ S, Continuous fun t : Icc (0 : ℝ) T => fun _ : Fin 1 => B ⟨t, t.2.1⟩ ω :=
    fun ω hω => continuous_pi fun _ => by
      have hc : Continuous fun t => B t ω := not_not.mp (hSgood ω hω).2.1
      exact hc.comp (continuous_subtype_val.subtype_mk _)
  set X : Ω → C(Icc (0 : ℝ) T, Fin 1 → ℝ) := fun ω =>
    if h : ω ∈ S then ⟨_, hcont ω h⟩ else 0 with hX
  have hX0 : ∀ ω, pathExt (X ω) 0 0 = 0 := by
    intro ω
    rw [pathExt_of_mem _ ⟨le_rfl, T.coe_nonneg⟩]
    by_cases h : ω ∈ S
    · simp only [hX, h, ↓reduceDIte, ContinuousMap.coe_mk]
      exact not_not.mp (hSgood ω h).2.2
    · simp [hX, h]
  have hXB : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T, X ω t 0 = B ⟨t, t.2.1⟩ ω := by
    filter_upwards [hSae] with ω hω t
    simp [hX, hω]
  refine ⟨X, ?_, hX0, hXB⟩
  -- measurable as the limit of its polygonal interpolations
  have hnode : ∀ n j, j ≤ n → 0 < n →
      (fun ω => pathExt (X ω) (node T n j) 0) = S.indicator (g n j) := by
    intro n j hj hn
    funext ω
    rw [pathExt_of_mem _ (node_mem hn hj)]
    by_cases h : ω ∈ S
    · rw [indicator_of_mem h]
      simp only [hX, h, ↓reduceDIte, ContinuousMap.coe_mk]
      have hN := (hSgood ω h).1
      simp only [hN₁, mem_iUnion, mem_ofPred_eq, not_exists, not_not] at hN
      exact hN n j
    · rw [indicator_of_notMem h]
      simp [hX, h]
  have hmeas : ∀ n, Measurable fun ω => polyInterp T n (X ω) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : (fun ω => polyInterp T 0 (X ω)) = fun _ => polyPath T 0 (fun k => 0) := by
        funext ω; unfold polyInterp; congr 1; funext k; exact k.elim0
      rw [this]; exact measurable_const
    refine continuous_polyPath.measurable.comp (measurable_pi_iff.mpr fun k => ?_)
    have hk := k.2
    have e : (fun ω => nodeIncr T n (X ω) k) = fun ω =>
        (S.indicator (g n (k + 1)) ω - S.indicator (g n k) ω) / √(mesh T n) := by
      funext ω
      have h1 := congrFun (hnode n (k + 1) hk hn) ω
      have h2 := congrFun (hnode n k hk.le hn) ω
      rw [nodeIncr, h1, h2]
    rw [e]
    exact (((hgm _ _).indicator hSm).sub ((hgm _ _).indicator hSm)).div_const _
  exact measurable_of_tendsto_metrizable hmeas
    (tendsto_pi_nhds.mpr fun ω => tendsto_polyInterp hT (X ω) (hX0 ω))

/-- **Exponential equivalence of the polygonal interpolations**: for a version `X` of a
pre-Brownian motion, `P(‖√ε π_n X − √ε X‖ > δ) ≤ 2n e^{−δ² n/(8 ε T)}`. -/
@[tmio T, powerlib_foundation] theorem measure_dist_polyInterp_le (hB : IsPreBrownianReal B P)
    {X : Ω → C(Icc (0 : ℝ) T, Fin 1 → ℝ)}
    (hXB : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T, X ω t 0 = B ⟨t, t.2.1⟩ ω) (hT : 0 < (T : ℝ)) {n : ℕ}
    (hn : 0 < n) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    P {ω | δ < dist (√ε • polyInterp T n (X ω)) (√ε • X ω)} ≤
      ENNReal.ofReal (2 * n * Real.exp (-(δ ^ 2 * n) / (8 * ε * T))) := by
  have hΔ := mesh_pos hT hn
  have hsε := Real.sqrt_pos.mpr hε
  set c := δ / (2 * √ε) with hc
  have hc0 : 0 ≤ c := by positivity
  set E : Fin n → Set Ω := fun k => {ω | ∃ s ∈ Icc (((k : ℕ) : ℝ) * mesh T n)
    (((k : ℕ) : ℝ) * mesh T n + mesh T n), c < |pathExt (X ω) s 0 -
      pathExt (X ω) (((k : ℕ) : ℝ) * mesh T n) 0|} with hE
  set N₀ := {ω | pathExt (X ω) 0 0 ≠ 0} with hN₀
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, T.coe_nonneg⟩
  have hN₀ae : P N₀ = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hXB, hB.eval_zero_ae_eq_zero] with ω hω h0
    simp only [hN₀, mem_ofPred_eq, not_not]
    rw [pathExt_of_mem _ h0mem, hω]
    exact h0
  have hsub : {ω | δ < dist (√ε • polyInterp T n (X ω)) (√ε • X ω)} ⊆ N₀ ∪ ⋃ k, E k := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, mem_iUnion, not_or, not_exists] at hnot
    obtain ⟨h0, hk⟩ := hnot
    simp only [hN₀, mem_ofPred_eq, not_not] at h0
    have hdist : dist (polyInterp T n (X ω)) (X ω) ≤ 2 * c := by
      refine (ContinuousMap.dist_le (by positivity)).mpr fun t => ?_
      obtain ⟨k, h1, h2, hb⟩ := abs_polyInterp_sub_le hT hn (X ω) t
      rw [dist_fin_one]
      have hnk := hk k
      simp only [hE, mem_ofPred_eq, not_exists, not_and, not_lt] at hnk
      have e1 := hnk t ⟨h1, h2⟩
      have e2 := hnk (((k : ℕ) : ℝ) * mesh T n + mesh T n) ⟨by linarith, le_rfl⟩
      rw [pathExt_of_mem _ t.2] at e1
      have hn1 : (node T n (k + 1) : ℝ) = ((k : ℕ) : ℝ) * mesh T n + mesh T n := by
        rw [coe_node]; push_cast; ring
      rw [h0, coe_node, hn1] at hb
      simp only [abs_zero, zero_add] at hb
      linarith
    have := hω
    simp only [mem_ofPred_eq] at this
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hsε,
      ← dist_eq_norm] at this
    have h4 : √ε * (2 * c) = δ := by rw [hc]; field_simp
    nlinarith
  have hEk : ∀ k : Fin n, P (E k) ≤ ENNReal.ofReal (2 * Real.exp (-(c ^ 2) / (2 * mesh T n))) :=
    fun k => by
      have hk : ((k : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast k.2
      have hTn : (T : ℝ) = n * mesh T n := by rw [mesh]; field_simp
      exact measure_exists_abs_lt_le hB hXB (by positivity) hΔ (by nlinarith) hc0
  have hexp : c ^ 2 / (2 * mesh T n) = δ ^ 2 * n / (8 * ε * T) := by
    rw [hc, mesh, div_pow, mul_pow, Real.sq_sqrt hε.le]
    field_simp
    ring
  calc _ ≤ P (N₀ ∪ ⋃ k, E k) := measure_mono hsub
    _ ≤ P N₀ + P (⋃ k, E k) := measure_union_le _ _
    _ ≤ 0 + ∑ k, P (E k) := add_le_add (le_of_eq hN₀ae) (measure_iUnion_fintype_le _ _)
    _ ≤ 0 + ∑ _k : Fin n, ENNReal.ofReal (2 * Real.exp (-(c ^ 2) / (2 * mesh T n))) :=
        add_le_add le_rfl (Finset.sum_le_sum fun k _ => hEk k)
    _ = _ := by
        rw [zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), neg_div, hexp,
          ← neg_div]
        congr 1
        ring

/-- **The exponential equivalence in the form of `isLDP_of_expApprox`**: for every `δ > 0` and
`M`, once `n` is large, `ε log P(‖√ε π_n X − √ε X‖ > δ) ≤ M` for all small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem expApprox_polyInterp (hB : IsPreBrownianReal B P)
    {X : Ω → C(Icc (0 : ℝ) T, Fin 1 → ℝ)}
    (hXB : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T, X ω t 0 = B ⟨t, t.2.1⟩ ω) (hT : 0 < (T : ℝ)) :
    ∀ δ > 0, ∀ M : ℝ, ∃ n₀, ∀ n ≥ n₀, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ((ε : ℝ) : EReal) * ENNReal.log
        (P {ω | δ < dist (√ε • polyInterp T n (X ω)) (√ε • X ω)}) ≤ M := by
  intro δ hδ M
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt ((1 - M) * (8 * T) / δ ^ 2)
  refine ⟨n₀ + 1, fun n hn => ?_⟩
  have hn0 : 0 < n := by omega
  have hnR : (n₀ : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hlog : Tendsto (fun ε : ℝ => ε * Real.log (2 * n)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun ε : ℝ => ε * Real.log (2 * n) := continuous_id.mul continuous_const
    have := hc.tendsto 0
    simp only [zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlog.eventually (gt_mem_nhds one_pos)]
    with ε (hε : 0 < ε) h1
  have hb := measure_dist_polyInterp_le hB hXB hT hn0 hε hδ
  have e : 2 * n * Real.exp (-(δ ^ 2 * n) / (8 * ε * T)) =
      Real.exp ((ε * Real.log (2 * n) - δ ^ 2 * n / (8 * T)) / ε) := by
    have h1 : (ε * Real.log (2 * n) - δ ^ 2 * n / (8 * T)) / ε =
        Real.log (2 * n) + -(δ ^ 2 * n) / (8 * ε * T) := by
      field_simp
      ring
    rw [h1, Real.exp_add, Real.exp_log (by positivity)]
  rw [e] at hb
  refine (mul_log_le_of_le_exp hε hb).trans ?_
  have h2 : (1 - M) < δ ^ 2 * n / (8 * T) := by
    rw [lt_div_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hn₀
    nlinarith
  exact_mod_cast (by linarith : ε * Real.log (2 * n) - δ ^ 2 * n / (8 * T) ≤ M)

end powerlib.Stochastic.LDP
