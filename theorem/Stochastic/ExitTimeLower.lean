import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.BrownPathMarkov

/-! # The Freidlin–Wentzell lower bound for the mean exit time, by deterministic time blocks

For the solution `x^ε = S(x₀, √ε B)` of `x(t) = x₀ + √ε N B(t) + ∫₀ᵗ b(x)` and a compact `K ∋ x₀`,
a lower bound `liminf_{ε→0⁺} ε log E τ_ε ≥ v_t − v_b` for the exit time `τ_ε` from `K` from two
deterministic rate inequalities for a continuous function `V` on `K` (in the applications a
multiple of a Lyapunov function): leaving `K` from `y` within one block costs at least
`v_t − V(y)`, and every path from `y` that ends in `K` costs at least
`V(φ(T)) − max(V(y) − δ, v_b)`. The proof needs only the Markov property at the deterministic
times `kT` (`Stochastic.LDP.measure_brownPath_markov`): the band sums
`m_k ≈ E[e^{V(x(kT))/ε}; τ > kT]` satisfy `m_{k+1} ≤ ρ_ε m_k + C_ε` with
`ρ_ε ≤ m e^{−(δ − 2κ)/ε} → 0` and `C_ε ≈ e^{v_b/ε}`, so they stay bounded by `2 m C_ε`; an exit in
block `k + 1` then has probability at most `e^{−(v_t − κ)/ε} m_k`, and `e^{(v_t − v_b − o(1))/ε}`
blocks survive with probability `≥ 1/2`. This replaces the strong Markov property at the hitting
times of small spheres around the attractor in the classical proof.

Scope.
* Generic: `E` a real Banach space, `b` globally Lipschitz, one noise column
  `N : (Fin 1 → ℝ) →L[ℝ] E`, `B` a Brownian motion all of whose paths are continuous, `K`
  compact, the exit time `Stochastic.LDP.exitTime` (`⊤` if the path never leaves `K`), its
  expectation the lower Lebesgue integral. The two rate inequalities are hypotheses on the
  Freidlin–Wentzell rate `pushRate (solMap b N y) (schilderRate T)` (deterministic variational
  statements, checked model by model).

Source: M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 4 §2 (Thm 4.2.1, lower bound for the exit time); A. Dembo, O. Zeitouni, *Large Deviations
Techniques and Applications*, 2nd ed. (1998), Thm 5.7.11(a) and Lemmas 5.7.19–5.7.23 (the
classical route through the strong Markov property); exponential moments of a Lyapunov function
over deterministic time blocks as in the Varadhan lemma (Dembo–Zeitouni Thm 4.3.1).

Results.
* `continuous_pathExt_apply`, `isClosed_stay_end`, `isOpen_leave`: path events used for the
  blocks; `sum_lintegral_le` (superadditivity of the lower integral over finite sums),
  `eventually_exp_neg_div_le` (`e^{−c/ε} ≤ η` for small `ε`), `exists_bands` (closed bands of a
  continuous function over a compact set).
* `restrictPath_solMap_brownPath`, `le_exitTime_of_forall_mem`, `exists_notMem_of_exitTime_lt`
  (an exit before `H` is an exit on `[0, H]`), `mul_le_lintegral_exitTime`
  (`H (1 − P(leave by H)) ≤ E τ`), `measure_exitTime_gt_le` (**uniform exponential tail**: if
  `E_y τ ≤ M` on `K`, then `P(τ > (n + 1) 2M) ≤ 2^{−(n+1)}`).
* `chain_step` (**one block of the chain**), `measure_leave_le_chain` (**survival over many
  blocks**: `P(leave by (n + 1)T) ≤ (n + 1) r M`), `measure_leave_le_of_bands` (the chain at a
  fixed noise level: `P(leave by (n + 1)T) ≤ (n + 1) 2m² e^{−(v_t − v_b − Δ − 2κ)/ε}`),
  `exp_le_lintegral_exitTime_of_bands` (`E τ ≥ e^{β/ε}`), `eventually_band_bounds` (the
  one-block bounds for all small `ε`).
* `le_liminf_log_lintegral_exitTime` (**Freidlin–Wentzell lower bound for the mean exit time**:
  `liminf ε log E τ_ε ≥ v_t − v_b`), `eventually_measure_exitTime_le` (**in probability**:
  `P(τ_ε ≤ e^{β/ε}) ≤ e^{−γ/ε}` for every `β < v_t − v_b`).
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

omit [NormedSpace ℝ E] in
@[tmio T, powerlib_foundation] theorem continuous_pathExt_apply {T : ℝ≥0} (s : ℝ) :
    Continuous fun φ : C(Icc (0 : ℝ) T, E) => pathExt φ s :=
  continuous_eval_const _

omit [NormedSpace ℝ E] in
/-- Paths staying in a closed `K` with end point in a closed `C` form a closed set. -/
@[tmio T, powerlib_foundation] theorem isClosed_stay_end {K C : Set E} (hK : IsClosed K)
    (hC : IsClosed C) (T : ℝ≥0) :
    IsClosed {φ : C(Icc (0 : ℝ) T, E) | (∀ t, φ t ∈ K) ∧ pathExt φ T ∈ C} := by
  have h1 : IsClosed {φ : C(Icc (0 : ℝ) T, E) | ∀ t, φ t ∈ K} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => hK.preimage (continuous_eval_const t)
  exact h1.inter (hC.preimage (continuous_pathExt_apply _))

omit [NormedSpace ℝ E] in
@[tmio T, powerlib_foundation] theorem isOpen_leave {K : Set E} (hK : IsClosed K) (T : ℝ≥0) :
    IsOpen {φ : C(Icc (0 : ℝ) T, E) | ∃ t, φ t ∉ K} := by
  have : {φ : C(Icc (0 : ℝ) T, E) | ∃ t, φ t ∉ K} = ⋃ t, (fun φ => φ t) ⁻¹' Kᶜ := by
    ext φ; simp
  rw [this]
  exact isOpen_iUnion fun t => hK.isOpen_compl.preimage (continuous_eval_const t)

/-- Superadditivity of the lower Lebesgue integral over a finite sum. -/
@[tmio T, powerlib_foundation] theorem sum_lintegral_le {ι : Type*} (s : Finset ι)
    (f : ι → Ω → ℝ≥0∞) (μ : Measure Ω) :
    ∑ i ∈ s, ∫⁻ ω, f i ω ∂μ ≤ ∫⁻ ω, ∑ i ∈ s, f i ω ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

/-- `e^{−c/ε} ≤ η` for all small `ε > 0` (`c, η > 0`). -/
@[tmio T, powerlib_foundation] theorem eventually_exp_neg_div_le {c η : ℝ} (hc : 0 < c)
    (hη : 0 < η) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Real.exp (-c / ε) ≤ η := by
  have h1 : Tendsto (fun ε : ℝ => -c * ε⁻¹) (𝓝[>] 0) atBot :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg (by linarith)
  have h2 := Real.tendsto_exp_atBot.comp h1
  filter_upwards [(tendsto_order.1 h2).2 η hη] with ε hε
  simp only [Function.comp_apply] at hε
  rw [div_eq_mul_inv]
  exact hε.le

omit [NormedSpace ℝ E] in
/-- **Bands of a continuous function over a compact set**: for `κ > 0`, closed bands
`Pc i = K ∩ V⁻¹[h_i, h_{i+1}]` (`i < m`, `h_{k+1} = h_k + Δ`, `0 ≤ Δ ≤ κ`) cover `K`. -/
@[tmio T, powerlib_foundation] theorem exists_bands {K : Set E} (hK : IsCompact K) {x₀ : E}
    (hx₀ : x₀ ∈ K) {V : E → ℝ} (hV : Continuous V) {κ : ℝ} (hκ : 0 < κ) :
    ∃ m : ℕ, 0 < m ∧ ∃ h : ℕ → ℝ, ∃ Δ : ℝ, Δ ≤ κ ∧ (∀ k, h (k + 1) = h k + Δ) ∧
      ∃ Pc : Fin m → Set E, (∀ i, IsCompact (Pc i)) ∧ (∀ i, Pc i ⊆ K) ∧ K ⊆ ⋃ i, Pc i ∧
        ∀ i : Fin m, ∀ y ∈ Pc i, h i ≤ V y ∧ V y ≤ h ((i : ℕ) + 1) := by
  obtain ⟨y₁, -, hmin⟩ := hK.exists_isMinOn ⟨x₀, hx₀⟩ hV.continuousOn
  obtain ⟨y₂, -, hmax⟩ := hK.exists_isMaxOn ⟨x₀, hx₀⟩ hV.continuousOn
  set hlo := V y₁ with hlo_def
  set hhi := V y₂ with hhi_def
  set m := ⌈(hhi - hlo) / κ⌉₊ + 1 with hm_def
  have hm : 0 < m := Nat.succ_pos _
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set Δ := (hhi - hlo) / m with hΔ_def
  have hmΔ : (m : ℝ) * Δ = hhi - hlo := by rw [hΔ_def]; field_simp
  have hlohi : hlo ≤ hhi := (hmin hx₀).trans (hmax hx₀)
  have hΔ0 : 0 ≤ Δ := div_nonneg (by linarith) hm0.le
  have hΔ : Δ ≤ κ := by
    have h1 := Nat.le_ceil ((hhi - hlo) / κ)
    rw [div_le_iff₀ hκ] at h1
    have h2 : (⌈(hhi - hlo) / κ⌉₊ : ℝ) ≤ m := by rw [hm_def]; push_cast; linarith
    by_contra hc
    rw [not_le] at hc
    nlinarith
  set h : ℕ → ℝ := fun k => hlo + k * Δ with hh_def
  have hh : ∀ k, h (k + 1) = h k + Δ := fun k => by simp only [hh_def]; push_cast; ring
  refine ⟨m, hm, h, Δ, hΔ, hh, fun i => K ∩ V ⁻¹' Icc (h i) (h ((i : ℕ) + 1)),
    fun i => hK.inter_right (isClosed_Icc.preimage hV), fun i => inter_subset_left, ?_,
    fun i y hy => hy.2⟩
  intro y hy
  have hy1 : hlo ≤ V y := hmin hy
  have hy2 : V y ≤ hhi := hmax hy
  set k := min ⌊(V y - hlo) / Δ⌋₊ (m - 1) with hk
  have hkm : k < m := lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hm one_pos)
  refine mem_iUnion.mpr ⟨⟨k, hkm⟩, hy, ?_, ?_⟩
  · show hlo + ((k : ℕ) : ℝ) * Δ ≤ V y
    rcases hΔ0.eq_or_lt with hΔe | hΔp
    · rw [← hΔe, mul_zero, add_zero]; exact hy1
    · have h1 : (k : ℝ) ≤ (V y - hlo) / Δ :=
        (Nat.cast_le.mpr (min_le_left _ _)).trans
          (Nat.floor_le (div_nonneg (by linarith) hΔp.le))
      rw [le_div_iff₀ hΔp] at h1
      linarith
  · show V y ≤ hlo + (((k + 1 : ℕ)) : ℝ) * Δ
    push_cast
    by_cases hcase : ⌊(V y - hlo) / Δ⌋₊ ≤ m - 1
    · rw [hk, min_eq_left hcase]
      rcases hΔ0.eq_or_lt with hΔe | hΔp
      · rw [← hΔe] at hmΔ ⊢
        rw [mul_zero] at hmΔ
        linarith
      · have h1 := Nat.lt_floor_add_one ((V y - hlo) / Δ)
        rw [div_lt_iff₀ hΔp] at h1
        linarith
    · rw [not_le] at hcase
      rw [hk, min_eq_right hcase.le]
      have : ((m - 1 : ℕ) : ℝ) + 1 = m := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hm.ne')]; push_cast; ring
      rw [this, hmΔ]
      linarith

variable [CompleteSpace E]

/-- The restriction of the solution on `[0, T₁ + T₂]` to `[0, T₁]` is the solution on `[0, T₁]`
(paths of `B`). -/
@[tmio T, powerlib_foundation] theorem restrictPath_solMap_brownPath
    (hBc : ∀ ω, Continuous fun t => B t ω) {L : ℝ≥0} {b : E → E} (hb : LipschitzWith L b)
    (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) (c : ℝ) {T₁ T : ℝ≥0} (h : T₁ ≤ T) (ω : Ω) :
    restrictPath h (solMap b N x₀ (c • brownPath B hBc T ω)) =
      solMap b N x₀ (c • brownPath B hBc T₁ ω) := by
  rw [restrictPath_solMap hb, restrictPath_smul, restrictPath_brownPath]

/-- A solution staying in `K` up to time `H` has exit time at least `H`. -/
@[tmio T, powerlib_foundation] theorem le_exitTime_of_forall_mem
    (hBc : ∀ ω, Continuous fun t => B t ω) {L : ℝ≥0} {b : E → E} (hb : LipschitzWith L b)
    (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) {K : Set E} (c : ℝ) {H : ℝ≥0} {ω : Ω}
    (h : ∀ t, solMap b N x₀ (c • brownPath B hBc H ω) t ∈ K) :
    (H : ℝ≥0∞) ≤ exitTime b N x₀ K c B hBc ω := by
  refine le_iInf fun T' => le_iInf₂ fun t ht => ?_
  by_contra hlt
  rw [not_le, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff'] at hlt
  have htH : (t : ℝ) ≤ H := hlt.1.le
  have e1 := restrictPath_solMap_brownPath hBc hb N x₀ c (le_sup_left : T' ≤ T' ⊔ H) ω
  have e2 := restrictPath_solMap_brownPath hBc hb N x₀ c (le_sup_right : H ≤ T' ⊔ H) ω
  have v1 := congrArg (fun φ => φ t) e1
  have v2 := congrArg (fun φ => φ ⟨t, t.2.1, htH⟩) e2
  rw [← v1] at ht
  exact ht (v2 ▸ h _)

/-- An exit before the horizon `H` is an exit of the solution on `[0, H]`. -/
@[tmio T, powerlib_foundation] theorem exists_notMem_of_exitTime_lt
    (hBc : ∀ ω, Continuous fun t => B t ω) {L : ℝ≥0} {b : E → E} (hb : LipschitzWith L b)
    (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) {K : Set E} (c : ℝ) {H : ℝ≥0} {ω : Ω}
    (h : exitTime b N x₀ K c B hBc ω < H) :
    ∃ t, solMap b N x₀ (c • brownPath B hBc H ω) t ∉ K := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  exact absurd (le_exitTime_of_forall_mem hBc hb N x₀ c hall) (not_le.mpr h)

/-- **One block of the chain** (time `T` after `T₁`), for closed bands `Pc i` covering a closed
`K`, weights `e i`, and the one-block bounds `Σⱼ e_j P_y(stay, end ∈ Pc j) ≤ ρ e_i + C₀`,
`P_y(leave) ≤ r e_i` for `y ∈ Pc i`: with `m_H = Σᵢ e_i P(stay on [0, H], x(H) ∈ Pc i)`,
`m_{T₁+T} ≤ ρ m_{T₁} + m C₀` and `P(leave by T₁ + T) ≤ P(leave by T₁) + r m_{T₁}`. -/
@[tmio T, powerlib_foundation] theorem chain_step [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω) {T₁ T : ℝ≥0}
    (hT₁ : 0 < (T₁ : ℝ)) (hT : 0 < (T : ℝ)) {L : ℝ≥0} {b : E → E} (hb : LipschitzWith L b)
    (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) (c : ℝ) {K : Set E} (hK : IsClosed K) {m : ℕ}
    {Pc : Fin m → Set E} (hPc : ∀ i, IsClosed (Pc i)) (hcov : K ⊆ ⋃ i, Pc i)
    (e : Fin m → ℝ≥0∞) {ρ C₀ r : ℝ≥0∞}
    (hstep : ∀ i, ∀ y ∈ Pc i, ∑ j, e j * P {ω | solMap b N y (c • brownPath B hBc T ω) ∈
      {φ : C(Icc (0 : ℝ) T, E) | (∀ t, φ t ∈ K) ∧ pathExt φ T ∈ Pc j}} ≤ ρ * e i + C₀)
    (hleave : ∀ i, ∀ y ∈ Pc i, P {ω | solMap b N y (c • brownPath B hBc T ω) ∈
      {φ : C(Icc (0 : ℝ) T, E) | ∃ t, φ t ∉ K}} ≤ r * e i) :
    ∑ j, e j * P {ω | solMap b N x₀ (c • brownPath B hBc (T₁ + T) ω) ∈
        {φ : C(Icc (0 : ℝ) (T₁ + T : ℝ≥0), E) |
          (∀ t, φ t ∈ K) ∧ pathExt φ (T₁ + T : ℝ≥0) ∈ Pc j}} ≤
      ρ * ∑ i, e i * P {ω | solMap b N x₀ (c • brownPath B hBc T₁ ω) ∈
        {φ : C(Icc (0 : ℝ) T₁, E) | (∀ t, φ t ∈ K) ∧ pathExt φ T₁ ∈ Pc i}} + m * C₀ ∧
    P {ω | solMap b N x₀ (c • brownPath B hBc (T₁ + T) ω) ∈
        {φ : C(Icc (0 : ℝ) (T₁ + T : ℝ≥0), E) | ∃ t, φ t ∉ K}} ≤
      P {ω | solMap b N x₀ (c • brownPath B hBc T₁ ω) ∈
          {φ : C(Icc (0 : ℝ) T₁, E) | ∃ t, φ t ∉ K}} +
        r * ∑ i, e i * P {ω | solMap b N x₀ (c • brownPath B hBc T₁ ω) ∈
          {φ : C(Icc (0 : ℝ) T₁, E) | (∀ t, φ t ∈ K) ∧ pathExt φ T₁ ∈ Pc i}} := by
  classical
  let _ : MeasurableSpace C(Icc (0 : ℝ) T₁, E) := borel _
  have : BorelSpace C(Icc (0 : ℝ) T₁, E) := ⟨rfl⟩
  let _ : MeasurableSpace C(Icc (0 : ℝ) T, E) := borel _
  have : BorelSpace C(Icc (0 : ℝ) T, E) := ⟨rfl⟩
  set A : Fin m → Set C(Icc (0 : ℝ) T₁, E) :=
    fun i => {φ | (∀ t, φ t ∈ K) ∧ pathExt φ T₁ ∈ Pc i} with hA
  set Cs : Fin m → Set C(Icc (0 : ℝ) T, E) :=
    fun j => {φ | (∀ t, φ t ∈ K) ∧ pathExt φ T ∈ Pc j} with hCs
  set Lv : Set C(Icc (0 : ℝ) T, E) := {φ | ∃ t, φ t ∉ K} with hLv
  set X₁ : Ω → C(Icc (0 : ℝ) T₁, E) := fun ω => solMap b N x₀ (c • brownPath B hBc T₁ ω)
    with hX₁
  set X₂ : Ω → C(Icc (0 : ℝ) (T₁ + T : ℝ≥0), E) :=
    fun ω => solMap b N x₀ (c • brownPath B hBc (T₁ + T) ω) with hX₂
  have hAm : ∀ i, MeasurableSet (A i) := fun i =>
    (isClosed_stay_end hK (hPc i) T₁).measurableSet
  have hCm : ∀ j, MeasurableSet (Cs j) := fun j =>
    (isClosed_stay_end hK (hPc j) T).measurableSet
  have hLm : MeasurableSet Lv := (isOpen_leave hK T).measurableSet
  have hAn : ∀ i, NullMeasurableSet {ω | X₁ ω ∈ A i} P := fun i =>
    nullMeasurableSet_brownPath hB hBc hT₁ hb N x₀ c (hAm i)
  have hres : ∀ ω, restrictPath le_self_add (X₂ ω) = X₁ ω := fun ω =>
    restrictPath_solMap_brownPath hBc hb N x₀ c le_self_add ω
  have hend : ∀ φ : C(Icc (0 : ℝ) (T₁ + T : ℝ≥0), E),
      pathExt (restartPath T₁ T φ) T = pathExt φ (T₁ + T : ℝ≥0) := by
    intro φ
    rw [pathExt_of_mem _ ⟨T.coe_nonneg, le_rfl⟩, NNReal.coe_add]
    rfl
  have hband : ∀ ω, (∀ t, X₁ ω t ∈ K) → ∃ i, X₁ ω ∈ A i := by
    intro ω hω
    have : pathExt (X₁ ω) T₁ ∈ K := by
      rw [pathExt_of_mem _ ⟨T₁.coe_nonneg, le_rfl⟩]; exact hω _
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov this)
    exact ⟨i, hω, hi⟩
  have hmk : ∀ i (C : Set C(Icc (0 : ℝ) T, E)), MeasurableSet C →
      P {ω | X₁ ω ∈ A i ∧ restartPath T₁ T (X₂ ω) ∈ C} =
        ∫⁻ ω in {ω | X₁ ω ∈ A i},
          P {ω' | solMap b N (pathExt (X₁ ω) T₁) (c • brownPath B hBc T ω') ∈ C} ∂P :=
    fun i C hC => measure_brownPath_markov hB hBc hT₁ hT hb N x₀ c (hAm i) hC
  have hint : ∀ i (g : Ω → ℝ≥0∞) (k : ℝ≥0∞), (∀ ω, X₁ ω ∈ A i → g ω ≤ k) →
      ∫⁻ ω in {ω | X₁ ω ∈ A i}, g ω ∂P ≤ k * P {ω | X₁ ω ∈ A i} := by
    intro i g k hg
    rw [← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_mem₀ (hAn i)).mono fun ω hω => hg ω hω)
  have hsumP : ∑ i, P {ω | X₁ ω ∈ A i} ≤ m := by
    calc ∑ i, P {ω | X₁ ω ∈ A i} ≤ ∑ _i : Fin m, (1 : ℝ≥0∞) :=
          Finset.sum_le_sum fun i _ => prob_le_one
      _ = m := by simp
  constructor
  · have h1 : ∀ j, P {ω | X₂ ω ∈ {φ : C(Icc (0 : ℝ) (T₁ + T : ℝ≥0), E) |
        (∀ t, φ t ∈ K) ∧ pathExt φ (T₁ + T : ℝ≥0) ∈ Pc j}} ≤
        ∑ i, P {ω | X₁ ω ∈ A i ∧ restartPath T₁ T (X₂ ω) ∈ Cs j} := by
      intro j
      refine (measure_mono fun ω hω => ?_).trans (measure_iUnion_fintype_le P _)
      obtain ⟨hst, hj⟩ := hω
      obtain ⟨h1, h2⟩ := (forall_mem_iff_restrict_restart (X₂ ω)).mp hst
      rw [hres] at h1
      obtain ⟨i, hi⟩ := hband ω h1
      exact mem_iUnion.mpr ⟨i, hi, h2, by rw [hend]; exact hj⟩
    calc ∑ j, e j * P {ω | X₂ ω ∈ {φ : C(Icc (0 : ℝ) (T₁ + T : ℝ≥0), E) |
          (∀ t, φ t ∈ K) ∧ pathExt φ (T₁ + T : ℝ≥0) ∈ Pc j}}
        ≤ ∑ j, e j * ∑ i, P {ω | X₁ ω ∈ A i ∧ restartPath T₁ T (X₂ ω) ∈ Cs j} :=
          Finset.sum_le_sum fun j _ => mul_le_mul_right (h1 j) _
      _ = ∑ i, ∑ j, e j * ∫⁻ ω in {ω | X₁ ω ∈ A i},
            P {ω' | solMap b N (pathExt (X₁ ω) T₁) (c • brownPath B hBc T ω') ∈ Cs j} ∂P := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [hmk i _ (hCm j)]
      _ ≤ ∑ i, (ρ * e i + C₀) * P {ω | X₁ ω ∈ A i} := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine (Finset.sum_le_sum fun j _ => lintegral_const_mul_le _ _).trans
            ((sum_lintegral_le _ _ _).trans (hint i _ _ fun ω hω => ?_))
          exact hstep i _ hω.2
      _ = ρ * ∑ i, e i * P {ω | X₁ ω ∈ A i} + C₀ * ∑ i, P {ω | X₁ ω ∈ A i} := by
          simp_rw [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
      _ ≤ _ := by
          rw [mul_comm (m : ℝ≥0∞) C₀]
          exact add_le_add le_rfl (mul_le_mul_right hsumP _)
  · have h1 : P {ω | X₂ ω ∈ {φ : C(Icc (0 : ℝ) (T₁ + T : ℝ≥0), E) | ∃ t, φ t ∉ K}} ≤
        P {ω | X₁ ω ∈ {φ : C(Icc (0 : ℝ) T₁, E) | ∃ t, φ t ∉ K}} +
          ∑ i, P {ω | X₁ ω ∈ A i ∧ restartPath T₁ T (X₂ ω) ∈ Lv} := by
      refine (measure_mono fun ω hω => ?_).trans ((measure_union_le _ _).trans
        (add_le_add le_rfl (measure_iUnion_fintype_le P _)))
      by_cases hst : ∀ t, X₁ ω t ∈ K
      · obtain ⟨i, hi⟩ := hband ω hst
        right
        refine mem_iUnion.mpr ⟨i, hi, ?_⟩
        by_contra hno
        simp only [hLv, mem_ofPred_eq, not_exists, not_not] at hno
        obtain ⟨t, ht⟩ := hω
        have := (forall_mem_iff_restrict_restart (X₂ ω)).mpr ⟨by rw [hres]; exact hst, hno⟩
        exact ht (this t)
      · left
        simp only [not_forall] at hst
        exact hst
    calc _ ≤ _ := h1
      _ = P {ω | X₁ ω ∈ {φ : C(Icc (0 : ℝ) T₁, E) | ∃ t, φ t ∉ K}} +
            ∑ i, ∫⁻ ω in {ω | X₁ ω ∈ A i},
              P {ω' | solMap b N (pathExt (X₁ ω) T₁) (c • brownPath B hBc T ω') ∈ Lv} ∂P := by
          rw [Finset.sum_congr rfl fun i _ => hmk i Lv hLm]
      _ ≤ _ := by
          refine add_le_add le_rfl ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun i _ => (hint i _ _ fun ω hω => hleave i _ hω.2).trans ?_
          rw [mul_assoc]

/-- **Survival over many blocks**: under the one-block bounds of `chain_step`, if `m_T ≤ M`,
`P(leave by T) ≤ r M` and `ρ M + m C₀ ≤ M`, then `P(leave by (n + 1) T) ≤ (n + 1) r M`. -/
@[tmio T, powerlib_foundation] theorem measure_leave_le_chain [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω) {T : ℝ≥0}
    (hT : 0 < (T : ℝ)) {L : ℝ≥0} {b : E → E} (hb : LipschitzWith L b)
    (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) (c : ℝ) {K : Set E} (hK : IsClosed K) {m : ℕ}
    {Pc : Fin m → Set E} (hPc : ∀ i, IsClosed (Pc i)) (hcov : K ⊆ ⋃ i, Pc i)
    (e : Fin m → ℝ≥0∞) {ρ C₀ r M : ℝ≥0∞}
    (hstep : ∀ i, ∀ y ∈ Pc i, ∑ j, e j * P {ω | solMap b N y (c • brownPath B hBc T ω) ∈
      {φ : C(Icc (0 : ℝ) T, E) | (∀ t, φ t ∈ K) ∧ pathExt φ T ∈ Pc j}} ≤ ρ * e i + C₀)
    (hleave : ∀ i, ∀ y ∈ Pc i, P {ω | solMap b N y (c • brownPath B hBc T ω) ∈
      {φ : C(Icc (0 : ℝ) T, E) | ∃ t, φ t ∉ K}} ≤ r * e i)
    (hM : ρ * M + m * C₀ ≤ M)
    (h1 : ∑ j, e j * P {ω | solMap b N x₀ (c • brownPath B hBc T ω) ∈
      {φ : C(Icc (0 : ℝ) T, E) | (∀ t, φ t ∈ K) ∧ pathExt φ T ∈ Pc j}} ≤ M)
    (h1' : P {ω | solMap b N x₀ (c • brownPath B hBc T ω) ∈
      {φ : C(Icc (0 : ℝ) T, E) | ∃ t, φ t ∉ K}} ≤ r * M) (n : ℕ) :
    P {ω | solMap b N x₀ (c • brownPath B hBc ((n + 1) * T) ω) ∈
      {φ : C(Icc (0 : ℝ) ((n + 1) * T : ℝ≥0), E) | ∃ t, φ t ∉ K}} ≤ (n + 1) * (r * M) := by
  suffices h : ∀ n : ℕ, (∑ j, e j * P {ω | solMap b N x₀ (c • brownPath B hBc ((n + 1) * T) ω) ∈
      {φ : C(Icc (0 : ℝ) ((n + 1) * T : ℝ≥0), E) |
        (∀ t, φ t ∈ K) ∧ pathExt φ ((n + 1) * T : ℝ≥0) ∈ Pc j}} ≤ M) ∧
      P {ω | solMap b N x₀ (c • brownPath B hBc ((n + 1) * T) ω) ∈
        {φ : C(Icc (0 : ℝ) ((n + 1) * T : ℝ≥0), E) | ∃ t, φ t ∉ K}} ≤ (n + 1) * (r * M) from
    (h n).2
  intro n
  induction n with
  | zero =>
    rw [show (((0 : ℕ) : ℝ≥0) + 1) * T = T by simp]
    simp only [Nat.cast_zero, zero_add, one_mul]
    exact ⟨h1, h1'⟩
  | succ n ih =>
    have e' : (((n + 1 : ℕ) : ℝ≥0) + 1) * T = ((n : ℝ≥0) + 1) * T + T := by push_cast; ring
    have hT₁ : 0 < ((((n : ℝ≥0) + 1) * T : ℝ≥0) : ℝ) := by
      have : (0 : ℝ≥0) < T := by exact_mod_cast hT
      have : (0 : ℝ≥0) < ((n : ℝ≥0) + 1) * T := by positivity
      exact_mod_cast this
    rw [e']
    obtain ⟨hA, hL⟩ := chain_step hB hBc hT₁ hT hb N x₀ c hK hPc hcov e hstep hleave
    refine ⟨hA.trans ((add_le_add (mul_le_mul_right ih.1 _) le_rfl).trans hM), hL.trans ?_⟩
    calc _ ≤ ((n : ℝ≥0∞) + 1) * (r * M) + r * M := add_le_add ih.2 (mul_le_mul_right ih.1 _)
      _ = (((n + 1 : ℕ) : ℝ≥0∞) + 1) * (r * M) := by push_cast; ring

/-- **The mean exit time dominates the survival time**: `H (1 − P(leave by H)) ≤ E τ`. -/
@[tmio T, powerlib_foundation] theorem mul_le_lintegral_exitTime [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω) {H : ℝ≥0}
    (hH : 0 < (H : ℝ)) {L : ℝ≥0} {b : E → E} (hb : LipschitzWith L b)
    (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) {K : Set E} (hK : IsClosed K) (c : ℝ) :
    (H : ℝ≥0∞) * (1 - P {ω | solMap b N x₀ (c • brownPath B hBc H ω) ∈
      {φ : C(Icc (0 : ℝ) H, E) | ∃ t, φ t ∉ K}}) ≤ ∫⁻ ω, exitTime b N x₀ K c B hBc ω ∂P := by
  let _ : MeasurableSpace C(Icc (0 : ℝ) H, E) := borel _
  have : BorelSpace C(Icc (0 : ℝ) H, E) := ⟨rfl⟩
  set St := {ω | solMap b N x₀ (c • brownPath B hBc H ω) ∈
    {φ : C(Icc (0 : ℝ) H, E) | ∀ t, φ t ∈ K}} with hSt
  have hcl : IsClosed {φ : C(Icc (0 : ℝ) H, E) | ∀ t, φ t ∈ K} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => hK.preimage (continuous_eval_const t)
  have hStn : NullMeasurableSet St P :=
    nullMeasurableSet_brownPath hB hBc hH hb N x₀ c hcl.measurableSet
  have h1 : 1 - P {ω | solMap b N x₀ (c • brownPath B hBc H ω) ∈
      {φ : C(Icc (0 : ℝ) H, E) | ∃ t, φ t ∉ K}} ≤ P St := by
    refine tsub_le_iff_right.mpr ?_
    rw [← measure_univ (μ := P)]
    refine (measure_mono fun ω _ => ?_).trans (measure_union_le _ _)
    by_cases h : ∀ t, solMap b N x₀ (c • brownPath B hBc H ω) t ∈ K
    · exact Or.inl h
    · right
      simp only [not_forall] at h
      exact h
  calc (H : ℝ≥0∞) * (1 - _) ≤ H * P St := mul_le_mul_right h1 _
    _ = ∫⁻ _ in St, (H : ℝ≥0∞) ∂P := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ ω in St, exitTime b N x₀ K c B hBc ω ∂P :=
        lintegral_mono_ae ((ae_restrict_mem₀ hStn).mono fun ω hω =>
          le_exitTime_of_forall_mem hBc hb N x₀ c hω)
    _ ≤ _ := setLIntegral_le_lintegral _ _

/-- **Survival over many blocks at a fixed noise level `√ε`**: for closed bands `Pc i ⊆ K` of
`V`-values `[h_i, h_{i+1}]` (`h_{i+1} = h_i + Δ`) covering `K`, the one-block exit bound
`P_y(leave) ≤ e^{−(vt − h_{i+1} − κ)/ε}` and the one-block band bounds
`P_y(stay, end ∈ Pc j) ≤ e^{−(h_j − max(h_{i+1} − δ, v_b) − κ)/ε}` (`y ∈ Pc i`), and the
smallness `e^{−δ/(2ε)} ≤ 1/(2m)` (`κ ≤ δ/4`, `Δ ≤ κ`): for every `n`,
`P(leave by (n + 1)T) ≤ (n + 1) · 2m² e^{−(vt − v_b − Δ − 2κ)/ε}`. -/
@[tmio T, powerlib_foundation] theorem measure_leave_le_of_bands
    [IsProbabilityMeasure P] (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω)
    {K : Set E} (hK : IsClosed K) {x₀ : E} {T : ℝ≥0} (hT : 0 < (T : ℝ)) {L : ℝ≥0} {b : E → E}
    (hb : LipschitzWith L b) (N : (Fin 1 → ℝ) →L[ℝ] E) {V : E → ℝ} {vt vb δ κ Δ ε : ℝ}
    (hε : 0 < ε) (hκ : 0 < κ) (hκδ : κ ≤ δ / 4) (hΔ : Δ ≤ κ) {m : ℕ} (hm : 0 < m)
    {h : ℕ → ℝ} (hh : ∀ k, h (k + 1) = h k + Δ) {Pc : Fin m → Set E} (hPc : ∀ i, IsClosed (Pc i))
    (hcov : K ⊆ ⋃ i, Pc i) (hPcV : ∀ i : Fin m, ∀ y ∈ Pc i, h i ≤ V y ∧ V y ≤ h ((i : ℕ) + 1))
    (hx₀ : x₀ ∈ K) (hx₀V : V x₀ ≤ vb)
    (hF1 : ∀ i : Fin m, ∀ y ∈ Pc i, P {ω | solMap b N y (√ε • brownPath B hBc T ω) ∈
      {φ : C(Icc (0 : ℝ) T, E) | ∃ t, φ t ∉ K}} ≤
        ENNReal.ofReal (Real.exp (-((vt - h ((i : ℕ) + 1)) - κ) / ε)))
    (hF2 : ∀ i j : Fin m, ∀ y ∈ Pc i, P {ω | solMap b N y (√ε • brownPath B hBc T ω) ∈
      {φ : C(Icc (0 : ℝ) T, E) | (∀ t, φ t ∈ K) ∧ pathExt φ T ∈ Pc j}} ≤
        ENNReal.ofReal (Real.exp (-((h j - max (h ((i : ℕ) + 1) - δ) vb) - κ) / ε)))
    (hF3 : Real.exp (-(δ / 2) / ε) ≤ 1 / (2 * (m : ℝ))) (n : ℕ) :
    P {ω | solMap b N x₀ (√ε • brownPath B hBc ((n + 1) * T) ω) ∈
      {φ : C(Icc (0 : ℝ) ((n + 1) * T : ℝ≥0), E) | ∃ t, φ t ∉ K}} ≤
      ((n : ℝ≥0∞) + 1) *
        ENNReal.ofReal (2 * (m : ℝ) ^ 2 * Real.exp (-(vt - vb - Δ - 2 * κ) / ε)) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  set ew : Fin m → ℝ := fun j => Real.exp (h ((j : ℕ) + 1) / ε) with hew
  set ρr := (m : ℝ) * Real.exp (-(δ - Δ - κ) / ε) with hρr_def
  set C₀r := (m : ℝ) * Real.exp ((Δ + κ + vb) / ε) with hC₀r
  set rr := Real.exp (-(vt - κ) / ε) with hrr
  set Mr := 2 * m * C₀r with hMr
  have hρr : ρr ≤ 1 / 2 := by
    have h1 : Real.exp (-(δ - Δ - κ) / ε) ≤ Real.exp (-(δ / 2) / ε) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hε.le)
    calc ρr ≤ m * (1 / (2 * m)) := mul_le_mul_of_nonneg_left (h1.trans hF3) hm0.le
      _ = 1 / 2 := by field_simp
  have hρ0 : 0 ≤ ρr := by positivity
  have hC₀0 : 0 ≤ C₀r := by positivity
  have hM0 : 0 ≤ Mr := by positivity
  have hew0 : ∀ j, 0 ≤ ew j := fun j => (Real.exp_pos _).le
  obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp (hcov hx₀)
  have hew₀ : ew i₀ ≤ C₀r := by
    have h1 : h ((i₀ : ℕ) + 1) ≤ Δ + κ + vb := by
      rw [hh]; have := (hPcV i₀ x₀ hi₀).1; linarith
    calc ew i₀ ≤ Real.exp ((Δ + κ + vb) / ε) :=
          Real.exp_le_exp.mpr (div_le_div_of_nonneg_right h1 hε.le)
      _ ≤ C₀r := le_mul_of_one_le_left (Real.exp_pos _).le hm1
  have hCM : C₀r ≤ Mr := by rw [hMr]; nlinarith
  -- the one-block bounds
  have hstep : ∀ i, ∀ y ∈ Pc i, ∑ j, ENNReal.ofReal (ew j) *
      P {ω | solMap b N y (√ε • brownPath B hBc T ω) ∈
        {φ : C(Icc (0 : ℝ) T, E) | (∀ t, φ t ∈ K) ∧ pathExt φ T ∈ Pc j}} ≤
      ENNReal.ofReal ρr * ENNReal.ofReal (ew i) + ENNReal.ofReal C₀r := by
    intro i y hy
    set Mi := max (h ((i : ℕ) + 1) - δ) vb with hMi
    have hterm : ∀ j : Fin m, ew j * Real.exp (-((h j - Mi) - κ) / ε) =
        Real.exp ((Δ + Mi + κ) / ε) := by
      intro j
      show Real.exp (h ((j : ℕ) + 1) / ε) * _ = _
      rw [← Real.exp_add, hh]
      congr 1
      ring
    have hsum : ∑ j, ENNReal.ofReal (ew j) * P {ω | solMap b N y (√ε • brownPath B hBc T ω) ∈
        {φ : C(Icc (0 : ℝ) T, E) | (∀ t, φ t ∈ K) ∧ pathExt φ T ∈ Pc j}} ≤
        ∑ _j : Fin m, ENNReal.ofReal (Real.exp ((Δ + Mi + κ) / ε)) := by
      refine Finset.sum_le_sum fun j _ => ?_
      refine (mul_le_mul_right (hF2 i j y hy) _).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_mul (hew0 j), hterm]
    refine hsum.trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hm0.le, ← ENNReal.ofReal_mul hρ0,
      ← ENNReal.ofReal_add (mul_nonneg hρ0 (hew0 i)) hC₀0]
    refine ENNReal.ofReal_le_ofReal ?_
    have he1 : Real.exp ((Δ + (h ((i : ℕ) + 1) - δ) + κ) / ε) =
        Real.exp (-(δ - Δ - κ) / ε) * ew i := by
      show _ = _ * Real.exp (h ((i : ℕ) + 1) / ε)
      rw [← Real.exp_add]
      congr 1
      ring
    have hmax : Real.exp ((Δ + Mi + κ) / ε) ≤
        Real.exp (-(δ - Δ - κ) / ε) * ew i + Real.exp ((Δ + κ + vb) / ε) := by
      rw [← he1]
      rcases le_total (h ((i : ℕ) + 1) - δ) vb with hle | hle
      · rw [hMi, max_eq_right hle, show Δ + vb + κ = Δ + κ + vb by ring]
        have := Real.exp_pos ((Δ + (h ((i : ℕ) + 1) - δ) + κ) / ε)
        linarith
      · rw [hMi, max_eq_left hle]
        have := Real.exp_pos ((Δ + κ + vb) / ε)
        linarith
    calc (m : ℝ) * Real.exp ((Δ + Mi + κ) / ε) ≤
          m * (Real.exp (-(δ - Δ - κ) / ε) * ew i + Real.exp ((Δ + κ + vb) / ε)) :=
          mul_le_mul_of_nonneg_left hmax hm0.le
      _ = ρr * ew i + C₀r := by rw [hρr_def, hC₀r]; ring
  have hleave : ∀ i, ∀ y ∈ Pc i, P {ω | solMap b N y (√ε • brownPath B hBc T ω) ∈
      {φ : C(Icc (0 : ℝ) T, E) | ∃ t, φ t ∉ K}} ≤ ENNReal.ofReal rr * ENNReal.ofReal (ew i) := by
    intro i y hy
    refine (hF1 i y hy).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    show _ = Real.exp (-(vt - κ) / ε) * Real.exp (h ((i : ℕ) + 1) / ε)
    rw [← Real.exp_add]
    congr 1
    ring
  have hM : ENNReal.ofReal ρr * ENNReal.ofReal Mr + m * ENNReal.ofReal C₀r ≤
      ENNReal.ofReal Mr := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hρ0, ← ENNReal.ofReal_mul hm0.le,
      ← ENNReal.ofReal_add (mul_nonneg hρ0 hM0) (mul_nonneg hm0.le hC₀0)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := mul_le_mul_of_nonneg_right hρr hM0
    rw [hMr] at this ⊢
    nlinarith
  have h1 : ∑ j, ENNReal.ofReal (ew j) * P {ω | solMap b N x₀ (√ε • brownPath B hBc T ω) ∈
      {φ : C(Icc (0 : ℝ) T, E) | (∀ t, φ t ∈ K) ∧ pathExt φ T ∈ Pc j}} ≤ ENNReal.ofReal Mr := by
    refine (hstep i₀ x₀ hi₀).trans ?_
    rw [← ENNReal.ofReal_mul hρ0, ← ENNReal.ofReal_add (mul_nonneg hρ0 (hew0 i₀)) hC₀0]
    refine ENNReal.ofReal_le_ofReal ?_
    have : ρr * ew i₀ ≤ C₀r := by nlinarith
    rw [hMr]
    nlinarith
  have h1' : P {ω | solMap b N x₀ (√ε • brownPath B hBc T ω) ∈
      {φ : C(Icc (0 : ℝ) T, E) | ∃ t, φ t ∉ K}} ≤ ENNReal.ofReal rr * ENNReal.ofReal Mr :=
    (hleave i₀ x₀ hi₀).trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal (hew₀.trans hCM)) _)
  refine (measure_leave_le_chain hB hBc hT hb N x₀ (√ε) hK hPc hcov
    (fun j => ENNReal.ofReal (ew j)) hstep hleave hM h1 h1' n).trans
    (mul_le_mul_right (le_of_eq ?_) _)
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  rw [hMr, hC₀r]
  have : Real.exp (-(vt - vb - Δ - 2 * κ) / ε) =
      Real.exp (-(vt - κ) / ε) * Real.exp ((Δ + κ + vb) / ε) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]; ring

/-- **Uniform exponential tail of the exit time** (any noise level `c`): if the mean exit time
from a closed `K` is at most `M > 0` from every state of `K`, then from every state of `K`,
`P(τ > (n + 1) · 2M) ≤ 2^{−(n+1)}`: each block of length `2M` is left with probability at least
`1/2` (`mul_le_lintegral_exitTime`), and the blocks chain by the Markov property
(`Stochastic.LDP.measure_stay_le_pow`). -/
@[tmio T, powerlib_foundation] theorem measure_exitTime_gt_le [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω) {L : ℝ≥0} {b : E → E}
    (hb : LipschitzWith L b) (N : (Fin 1 → ℝ) →L[ℝ] E) (c : ℝ) {K : Set E} (hK : IsClosed K)
    {M : ℝ≥0} (hM : 0 < (M : ℝ))
    (hmean : ∀ y ∈ K, ∫⁻ ω, exitTime b N y K c B hBc ω ∂P ≤ M) {x₀ : E} (hx₀ : x₀ ∈ K)
    (n : ℕ) :
    P {ω | ((((n : ℝ≥0) + 1) * (2 * M) : ℝ≥0) : ℝ≥0∞) < exitTime b N x₀ K c B hBc ω} ≤
      2⁻¹ ^ (n + 1) := by
  set T : ℝ≥0 := 2 * M with hT
  have hT0 : 0 < (T : ℝ) := by rw [hT]; push_cast; linarith
  -- every block is left with probability at least `1/2`
  have hq : ∀ y ∈ K, 2⁻¹ ≤ P {ω | ∃ t, solMap b N y (c • brownPath B hBc T ω) t ∉ K} := by
    intro y hy
    have h := (mul_le_lintegral_exitTime hB hBc hT0 hb N y hK c).trans (hmean y hy)
    have hT' : (T : ℝ≥0∞) = 2 * M := by rw [hT]; push_cast; rfl
    rw [hT'] at h
    have hM0 : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show (M : ℝ) ≠ 0 from hM.ne')
    have hMt : (M : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have h2 : 2 * (1 - P {ω | ∃ t, solMap b N y (c • brownPath B hBc T ω) t ∉ K}) ≤ 1 := by
      have h' : (M : ℝ≥0∞) * (2 * (1 - P {ω | ∃ t, solMap b N y (c • brownPath B hBc T ω) t ∉
          K})) ≤ M * 1 := by
        rw [mul_one, ← mul_assoc, mul_comm (M : ℝ≥0∞) 2]; exact h
      exact (ENNReal.mul_le_mul_iff_right hM0 hMt).mp h'
    have h3 : 1 - P {ω | ∃ t, solMap b N y (c • brownPath B hBc T ω) t ∉ K} ≤ 2⁻¹ := by
      rw [ENNReal.le_inv_iff_mul_le, mul_comm]; exact h2
    have h4 := tsub_le_iff_right.mp h3
    have hP1 : P {ω | ∃ t, solMap b N y (c • brownPath B hBc T ω) t ∉ K} ≤ 1 := prob_le_one
    calc (2⁻¹ : ℝ≥0∞) = 1 - 2⁻¹ := by rw [ENNReal.one_sub_inv_two]
      _ ≤ P {ω | ∃ t, solMap b N y (c • brownPath B hBc T ω) t ∉ K} := by
          rw [tsub_le_iff_right]; rwa [add_comm]
  have hinf : 1 - ⨅ y ∈ K, P {ω | ∃ t, solMap b N y (c • brownPath B hBc T ω) t ∉ K} ≤ 2⁻¹ := by
    rw [tsub_le_iff_right]
    calc (1 : ℝ≥0∞) = 2⁻¹ + 2⁻¹ := ENNReal.inv_two_add_inv_two.symm
      _ ≤ 2⁻¹ + ⨅ y ∈ K, P {ω | ∃ t, solMap b N y (c • brownPath B hBc T ω) t ∉ K} :=
          add_le_add le_rfl (le_iInf₂ hq)
  -- an exit after `(n + 1) T` means staying in `K` on `[0, (n + 1) T]`
  have hsub : {ω | ((((n : ℝ≥0) + 1) * T : ℝ≥0) : ℝ≥0∞) < exitTime b N x₀ K c B hBc ω} ⊆
      {ω | ∀ t, solMap b N x₀ (c • brownPath B hBc ((n + 1) * T) ω) t ∈ K} := by
    intro ω hω
    by_contra hst
    simp only [mem_ofPred_eq, not_forall] at hst
    obtain ⟨t, ht⟩ := hst
    have hle : exitTime b N x₀ K c B hBc ω ≤ ENNReal.ofReal t :=
      (iInf_le _ ((n + 1) * T)).trans (iInf₂_le t ht)
    have htH : ENNReal.ofReal t ≤ ((((n : ℝ≥0) + 1) * T : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal t.2.2
    exact absurd (hle.trans htH) (not_le.mpr hω)
  refine (measure_mono hsub).trans ((measure_stay_le_pow hB hBc hT0 hb N c hK hx₀ n).trans ?_)
  exact pow_le_pow_left₀ zero_le hinf _

/-- **The chain at a fixed noise level `√ε`**: for closed bands `Pc i ⊆ K` of `V`-values
`[h_i, h_{i+1}]` (`h_{i+1} = h_i + Δ`) covering `K`, the one-block exit bound
`P_y(leave) ≤ e^{−(vt − h_{i+1} − κ)/ε}` and the one-block band bounds
`P_y(stay, end ∈ Pc j) ≤ e^{−(h_j − max(h_{i+1} − δ, v_b) − κ)/ε}` (`y ∈ Pc i`), and the
smallness `e^{−δ/(2ε)} ≤ 1/(2m)`, `e^{−5κ/ε} ≤ min(1/(8m²), T/(16m²))`, the mean exit time is at
least `e^{β/ε}` (`κ ≤ δ/4`, `κ ≤ (vt − v_b − β)/8`, `Δ ≤ κ`). -/
@[tmio T, powerlib_foundation] theorem exp_le_lintegral_exitTime_of_bands
    [IsProbabilityMeasure P] (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω)
    {K : Set E} (hK : IsClosed K) {x₀ : E} {T : ℝ≥0} (hT : 0 < (T : ℝ)) {L : ℝ≥0} {b : E → E}
    (hb : LipschitzWith L b) (N : (Fin 1 → ℝ) →L[ℝ] E) {V : E → ℝ} {vt vb δ κ β Δ ε : ℝ}
    (hε : 0 < ε) (hκ : 0 < κ) (hκδ : κ ≤ δ / 4) (hκβ : κ ≤ (vt - vb - β) / 8) (hβ : 0 < β)
    (hΔ : Δ ≤ κ) {m : ℕ} (hm : 0 < m) {h : ℕ → ℝ}
    (hh : ∀ k, h (k + 1) = h k + Δ) {Pc : Fin m → Set E} (hPc : ∀ i, IsClosed (Pc i))
    (hcov : K ⊆ ⋃ i, Pc i) (hPcV : ∀ i : Fin m, ∀ y ∈ Pc i, h i ≤ V y ∧ V y ≤ h ((i : ℕ) + 1))
    (hx₀ : x₀ ∈ K) (hx₀V : V x₀ ≤ vb)
    (hF1 : ∀ i : Fin m, ∀ y ∈ Pc i, P {ω | solMap b N y (√ε • brownPath B hBc T ω) ∈
      {φ : C(Icc (0 : ℝ) T, E) | ∃ t, φ t ∉ K}} ≤
        ENNReal.ofReal (Real.exp (-((vt - h ((i : ℕ) + 1)) - κ) / ε)))
    (hF2 : ∀ i j : Fin m, ∀ y ∈ Pc i, P {ω | solMap b N y (√ε • brownPath B hBc T ω) ∈
      {φ : C(Icc (0 : ℝ) T, E) | (∀ t, φ t ∈ K) ∧ pathExt φ T ∈ Pc j}} ≤
        ENNReal.ofReal (Real.exp (-((h j - max (h ((i : ℕ) + 1) - δ) vb) - κ) / ε)))
    (hF3 : Real.exp (-(δ / 2) / ε) ≤ 1 / (2 * (m : ℝ)))
    (hF4 : Real.exp (-(5 * κ) / ε) ≤ min (1 / (8 * (m : ℝ) ^ 2)) ((T : ℝ) / (16 * (m : ℝ) ^ 2))) :
    ENNReal.ofReal (Real.exp (β / ε)) ≤ ∫⁻ ω, exitTime b N x₀ K (√ε) B hBc ω ∂P := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hsurv := measure_leave_le_of_bands hB hBc hK hT hb N hε hκ hκδ hΔ hm hh hPc hcov hPcV
    hx₀ hx₀V hF1 hF2 hF3
  -- the number of blocks
  set D := vt - vb - Δ - 2 * κ with hD
  set q := 2 * (m : ℝ) ^ 2 * Real.exp (-D / ε) with hq_def
  have hq : q = 2 * m ^ 2 * Real.exp (-D / ε) := rfl
  have hq0 : 0 < q := by rw [hq]; positivity
  set u := Real.exp (-(5 * κ) / ε) with hu
  have hDu : Real.exp (-D / ε) ≤ u :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by rw [hD]; linarith) hε.le)
  have hDβu : Real.exp (-(D - β) / ε) ≤ u :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by rw [hD]; linarith) hε.le)
  have hu1 : u ≤ 1 / (8 * m ^ 2) := hF4.trans (min_le_left _ _)
  have hu2 : u ≤ T / (16 * m ^ 2) := hF4.trans (min_le_right _ _)
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have hq4 : q ≤ 1 / 4 := by
    rw [hq]
    calc 2 * (m : ℝ) ^ 2 * Real.exp (-D / ε) ≤ 2 * m ^ 2 * (1 / (8 * m ^ 2)) := by gcongr; linarith
      _ = 1 / 4 := by field_simp; ring
  set x := 1 / (2 * q) with hx
  have hx2 : 2 ≤ x := by
    rw [hx, le_div_iff₀ (by positivity)]; linarith
  set n₁ := ⌊x⌋₊ with hn₁
  have hn₁1 : 1 ≤ n₁ := (Nat.one_le_floor_iff x).mpr (by linarith)
  have hn₁x : (n₁ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxn₁ : x < n₁ + 1 := Nat.lt_floor_add_one x
  set n := n₁ - 1 with hn
  have hnn : (n : ℝ) + 1 = n₁ := by
    rw [hn]; push_cast [Nat.cast_sub hn₁1]; ring
  -- the mean exit time
  have hH : 0 < ((((n : ℝ≥0) + 1) * T : ℝ≥0) : ℝ) := by
    have : (0 : ℝ≥0) < T := by exact_mod_cast hT
    have : (0 : ℝ≥0) < ((n : ℝ≥0) + 1) * T := by positivity
    exact_mod_cast this
  have hE := mul_le_lintegral_exitTime hB hBc hH hb N x₀ hK (√ε)
  refine le_trans ?_ (le_trans (mul_le_mul_right (tsub_le_tsub_left (hsurv n) 1) _) hE)
  rw [show ((n : ℝ≥0∞) + 1) =
    ENNReal.ofReal ((n : ℝ) + 1) by rw [ENNReal.ofReal_add (by positivity) zero_le_one]; simp,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ (by positivity), ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hnn]
  have hq' : (n₁ : ℝ) * q ≤ 1 / 2 := by
    calc (n₁ : ℝ) * q ≤ x * q := mul_le_mul_of_nonneg_right hn₁x hq0.le
      _ = 1 / 2 := by rw [hx]; field_simp
  have hxq : x * q = 1 / 2 := by rw [hx]; field_simp
  have hT0 : (0 : ℝ) ≤ T := T.coe_nonneg
  have hcoe : ((((n : ℝ≥0) + 1) * T : ℝ≥0) : ℝ) = n₁ * T := by
    push_cast; rw [hnn]
  rw [hcoe]
  -- `n₁ T (1 − n₁ q) ≥ T/(8q) ≥ e^{β/ε}`
  have hn₁2 : x / 2 ≤ n₁ := by linarith
  have key : Real.exp (β / ε) * (8 * q) ≤ (T : ℝ) := by
    rw [hq]
    have : Real.exp (β / ε) * Real.exp (-D / ε) = Real.exp (-(D - β) / ε) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.exp (β / ε) * (8 * (2 * (m : ℝ) ^ 2 * Real.exp (-D / ε))) =
          16 * (m : ℝ) ^ 2 * (Real.exp (β / ε) * Real.exp (-D / ε)) := by ring
      _ ≤ 16 * (m : ℝ) ^ 2 * ((T : ℝ) / (16 * (m : ℝ) ^ 2)) := by
          rw [this]
          exact mul_le_mul_of_nonneg_left (hDβu.trans hu2) (by positivity)
      _ = T := by field_simp
  have h8 : Real.exp (β / ε) ≤ (T : ℝ) / (8 * q) := by
    rw [le_div_iff₀ (by positivity)]; exact key
  refine h8.trans ?_
  have hxq' : (T : ℝ) / (8 * q) = x / 4 * T := by rw [hx]; field_simp; ring
  rw [hxq']
  have h12 : (1 : ℝ) / 2 ≤ 1 - n₁ * q := by linarith
  calc x / 4 * (T : ℝ) = (x / 2) * T * (1 / 2) := by ring
    _ ≤ n₁ * T * (1 - n₁ * q) := by gcongr

/-- **The eventual one-block bounds on the bands**: the exit and moment rate inequalities and the
explicit uniform large-deviation bound give, for all small `ε`,
`P_y(leave) ≤ e^{−(vt − h_{i+1} − κ)/ε}` and
`P_y(stay, end ∈ Pc j) ≤ e^{−(h_j − max(h_{i+1} − δ, v_b) − κ)/ε}` for `y ∈ Pc i`. -/
@[tmio T, powerlib_foundation] theorem eventually_band_bounds [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω) {K : Set E}
    (hK : IsCompact K) {T : ℝ≥0} (hT : 0 < (T : ℝ)) {L : ℝ≥0} {b : E → E}
    (hb : LipschitzWith L b) (N : (Fin 1 → ℝ) →L[ℝ] E) {V : E → ℝ} {vt vb δ κ : ℝ}
    (hκ : 0 < κ)
    (hexit : ∀ y ∈ K, ∀ φ ∈ closure {φ : C(Icc (0 : ℝ) T, E) | ∃ t, φ t ∉ K},
      ENNReal.ofReal (vt - V y) ≤ pushRate (solMap b N y) (schilderRate T) φ)
    (hmom : ∀ y ∈ K, ∀ φ : C(Icc (0 : ℝ) T, E), pathExt φ T ∈ K →
      ENNReal.ofReal (V (pathExt φ T) - max (V y - δ) vb) ≤
        pushRate (solMap b N y) (schilderRate T) φ)
    {m : ℕ} {h : ℕ → ℝ} {Pc : Fin m → Set E} (hPcc : ∀ i, IsCompact (Pc i))
    (hPcK : ∀ i, Pc i ⊆ K) (hPcV : ∀ i : Fin m, ∀ y ∈ Pc i, h i ≤ V y ∧ V y ≤ h ((i : ℕ) + 1)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∀ i : Fin m, ∀ y ∈ Pc i,
      P {ω | solMap b N y (√ε • brownPath B hBc T ω) ∈
        {φ : C(Icc (0 : ℝ) T, E) | ∃ t, φ t ∉ K}} ≤
        ENNReal.ofReal (Real.exp (-((vt - h ((i : ℕ) + 1)) - κ) / ε))) ∧
      ∀ i j : Fin m, ∀ y ∈ Pc i,
        P {ω | solMap b N y (√ε • brownPath B hBc T ω) ∈
          {φ : C(Icc (0 : ℝ) T, E) | (∀ t, φ t ∈ K) ∧ pathExt φ T ∈ Pc j}} ≤
          ENNReal.ofReal (Real.exp (-((h j - max (h ((i : ℕ) + 1) - δ) vb) - κ) / ε)) := by
  have hF1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i : Fin m, ∀ y ∈ Pc i,
      P {ω | solMap b N y (√ε • brownPath B hBc T ω) ∈
        {φ : C(Icc (0 : ℝ) T, E) | ∃ t, φ t ∉ K}} ≤
        ENNReal.ofReal (Real.exp (-((vt - h ((i : ℕ) + 1)) - κ) / ε)) := by
    refine Filter.eventually_all.mpr fun i => ?_
    refine eventually_measure_brownPath_le hB hBc hT hb N (hPcc i) _ (fun y hy φ hφ => ?_) hκ
    exact (ENNReal.ofReal_le_ofReal (by linarith [(hPcV i y hy).2])).trans
      (hexit y (hPcK i hy) φ hφ)
  have hF2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i j : Fin m, ∀ y ∈ Pc i,
      P {ω | solMap b N y (√ε • brownPath B hBc T ω) ∈
        {φ : C(Icc (0 : ℝ) T, E) | (∀ t, φ t ∈ K) ∧ pathExt φ T ∈ Pc j}} ≤
        ENNReal.ofReal (Real.exp (-((h j - max (h ((i : ℕ) + 1) - δ) vb) - κ) / ε)) := by
    refine Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => ?_
    refine eventually_measure_brownPath_le hB hBc hT hb N (hPcc i) _ (fun y hy φ hφ => ?_) hκ
    rw [(isClosed_stay_end hK.isClosed (hPcc j).isClosed T).closure_eq] at hφ
    obtain ⟨-, hend⟩ := hφ
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hmom y (hPcK i hy) φ (hPcK j hend))
    have h1 := (hPcV j _ hend).1
    have h2 : max (V y - δ) vb ≤ max (h ((i : ℕ) + 1) - δ) vb :=
      max_le_max (by linarith [(hPcV i y hy).2]) le_rfl
    linarith
  exact hF1.and hF2

/-- **Freidlin–Wentzell lower bound for the mean exit time**, by a chain of deterministic time
blocks. `K` compact, `x₀ ∈ K`, `V` continuous with `V(x₀) ≤ v_b < v_t`, `δ > 0`, block length
`T > 0`, and the two rate inequalities for the Freidlin–Wentzell rate `J_y` from `y ∈ K` on
`[0, T]`:
* (exit) `J_y(φ) ≥ v_t − V(y)` for every `φ` in the closure of the paths leaving `K`;
* (moment) `J_y(φ) ≥ V(φ(T)) − max(V(y) − δ, v_b)` for every `φ` ending in `K`.
Then `liminf_{ε→0⁺} ε log E τ_ε ≥ v_t − v_b`. The proof bounds the exponential moments
`E[e^{V(x(kT))/ε}; τ > kT]` uniformly in `k` (the moment inequality makes them contract at rate
`e^{−δ/ε}` above `v_b`), so that the probability of an exit within each block is at most
`e^{−(v_t − v_b − o(1))/ε}`; only the Markov property at the times `kT` is used. -/
@[tmio T, powerlib_foundation] theorem le_liminf_log_lintegral_exitTime [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω) {K : Set E}
    (hK : IsCompact K) {x₀ : E} (hx₀ : x₀ ∈ K) {T : ℝ≥0} (hT : 0 < (T : ℝ)) {L : ℝ≥0}
    {b : E → E} (hb : LipschitzWith L b) (N : (Fin 1 → ℝ) →L[ℝ] E) {V : E → ℝ}
    (hV : Continuous V) {vt vb δ : ℝ} (hδ : 0 < δ) (hvb : vb < vt) (hx₀V : V x₀ ≤ vb)
    (hexit : ∀ y ∈ K, ∀ φ ∈ closure {φ : C(Icc (0 : ℝ) T, E) | ∃ t, φ t ∉ K},
      ENNReal.ofReal (vt - V y) ≤ pushRate (solMap b N y) (schilderRate T) φ)
    (hmom : ∀ y ∈ K, ∀ φ : C(Icc (0 : ℝ) T, E), pathExt φ T ∈ K →
      ENNReal.ofReal (V (pathExt φ T) - max (V y - δ) vb) ≤
        pushRate (solMap b N y) (schilderRate T) φ) :
    ((vt - vb : ℝ) : EReal) ≤ liminf (fun ε : ℝ => (ε : EReal) *
        ENNReal.log (∫⁻ ω, exitTime b N x₀ K (√ε) B hBc ω ∂P)) (𝓝[>] 0) := by
  refine le_of_forall_lt_imp_le_of_dense fun β₀ hβ₀ => ?_
  induction β₀ using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd hβ₀ not_top_lt
  | coe β₀ =>
  have hβ₀' : β₀ < vt - vb := EReal.coe_lt_coe_iff.mp hβ₀
  obtain ⟨β, hβ₀β, hβ⟩ := exists_between (max_lt hβ₀' (by linarith : (0 : ℝ) < vt - vb))
  have hβ0 : 0 < β := lt_of_le_of_lt (le_max_right _ _) hβ₀β
  refine le_trans (EReal.coe_le_coe_iff.mpr (le_of_max_le_left hβ₀β.le)) ?_
  refine le_liminf_of_le (by isBoundedDefault) ?_
  -- the bands of `V` over `K`
  set κ := min (δ / 4) ((vt - vb - β) / 8) with hκ_def
  have hκ : 0 < κ := lt_min (by linarith) (by linarith)
  have hκδ : κ ≤ δ / 4 := min_le_left _ _
  have hκβ : κ ≤ (vt - vb - β) / 8 := min_le_right _ _
  obtain ⟨m, hm, h, Δ, hΔ, hh, Pc, hPcc, hPcK, hcov, hPcV⟩ := exists_bands hK hx₀ hV hκ
  -- the eventual one-block bounds
  have hF12 := eventually_band_bounds hB hBc hK hT hb N hκ hexit hmom hPcc hPcK hPcV
  have hF3 := eventually_exp_neg_div_le (c := δ / 2) (η := 1 / (2 * (m : ℝ))) (by linarith)
    (by positivity)
  have hF4 := eventually_exp_neg_div_le (c := 5 * κ)
    (η := min (1 / (8 * (m : ℝ) ^ 2)) ((T : ℝ) / (16 * (m : ℝ) ^ 2))) (by linarith)
    (lt_min (by positivity) (by positivity))
  filter_upwards [hF12, hF3, hF4, self_mem_nhdsWithin] with ε ⟨h1, h2⟩ h3 h4 (hε : 0 < ε)
  exact le_mul_log_of_exp_le hε (exp_le_lintegral_exitTime_of_bands hB hBc hK.isClosed hT hb N
    hε hκ hκδ hκβ hβ0 hΔ hm hh (fun i => (hPcc i).isClosed) hcov hPcV hx₀ hx₀V h1 h2 h3 h4)

/-- **The exit time is exponentially large in probability**: under the two rate inequalities of
`le_liminf_log_lintegral_exitTime` (`v_b < v_t`), for every `β < v_t − v_b` there is `γ > 0`
with `P(τ_ε ≤ e^{β/ε}) ≤ e^{−γ/ε}` for all small `ε > 0`: the chain of
`measure_leave_le_of_bands` over `⌈e^{β/ε}/T⌉ + 1` blocks of length `T`. -/
@[tmio T, powerlib_foundation] theorem eventually_measure_exitTime_le [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω) {K : Set E}
    (hK : IsCompact K) {x₀ : E} (hx₀ : x₀ ∈ K) {T : ℝ≥0} (hT : 0 < (T : ℝ)) {L : ℝ≥0}
    {b : E → E} (hb : LipschitzWith L b) (N : (Fin 1 → ℝ) →L[ℝ] E) {V : E → ℝ}
    (hV : Continuous V) {vt vb δ : ℝ} (hδ : 0 < δ) (hvb : vb < vt) (hx₀V : V x₀ ≤ vb)
    (hexit : ∀ y ∈ K, ∀ φ ∈ closure {φ : C(Icc (0 : ℝ) T, E) | ∃ t, φ t ∉ K},
      ENNReal.ofReal (vt - V y) ≤ pushRate (solMap b N y) (schilderRate T) φ)
    (hmom : ∀ y ∈ K, ∀ φ : C(Icc (0 : ℝ) T, E), pathExt φ T ∈ K →
      ENNReal.ofReal (V (pathExt φ T) - max (V y - δ) vb) ≤
        pushRate (solMap b N y) (schilderRate T) φ) {β : ℝ} (hβ : β < vt - vb) :
    ∃ γ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | exitTime b N x₀ K (√ε) B hBc ω ≤
      ENNReal.ofReal (Real.exp (β / ε))} ≤ ENNReal.ofReal (Real.exp (-γ / ε)) := by
  set β₁ := max β 0 with hβ₁_def
  have hβ₁ : β₁ < vt - vb := max_lt hβ (by linarith)
  have hβ₁0 : 0 ≤ β₁ := le_max_right _ _
  set g := vt - vb - β₁ with hg_def
  have hg : 0 < g := by linarith
  set κ := min (δ / 4) (g / 16) with hκ_def
  have hκ : 0 < κ := lt_min (by linarith) (by linarith)
  have hκδ : κ ≤ δ / 4 := min_le_left _ _
  have hκg : κ ≤ g / 16 := min_le_right _ _
  obtain ⟨m, hm, h, Δ, hΔ, hh, Pc, hPcc, hPcK, hcov, hPcV⟩ := exists_bands hK hx₀ hV hκ
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hF12 := eventually_band_bounds hB hBc hK hT hb N hκ hexit hmom hPcc hPcK hPcV
  have hF3 := eventually_exp_neg_div_le (c := δ / 2) (η := 1 / (2 * (m : ℝ))) (by linarith)
    (by positivity)
  have hF5 := eventually_exp_neg_div_le (c := 5 * g / 16)
    (η := min ((T : ℝ) / (4 * (m : ℝ) ^ 2)) (1 / (8 * (m : ℝ) ^ 2))) (by linarith)
    (lt_min (div_pos hT (by positivity)) (by positivity))
  refine ⟨g / 2, by positivity, ?_⟩
  filter_upwards [hF12, hF3, hF5, self_mem_nhdsWithin] with ε ⟨h1, h2⟩ h3 h5 (hε : 0 < ε)
  have hsurv := measure_leave_le_of_bands hB hBc hK.isClosed hT hb N hε hκ hκδ hΔ hm hh
    (fun i => (hPcc i).isClosed) hcov hPcV hx₀ hx₀V h1 h2 h3
  -- the number of blocks
  set E1 := Real.exp (β₁ / ε) with hE1
  set n := ⌈E1 / T⌉₊ with hn
  have hnT : E1 / T ≤ n := Nat.le_ceil _
  have hn2 : (n : ℝ) < E1 / T + 1 := Nat.ceil_lt_add_one (by positivity)
  have hH : Real.exp (β / ε) < ((((n : ℝ≥0) + 1) * T : ℝ≥0) : ℝ) := by
    push_cast
    have h1 : Real.exp (β / ε) ≤ E1 :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (le_max_left _ _) hε.le)
    have h2 : E1 ≤ n * T := by rwa [div_le_iff₀ hT] at hnT
    nlinarith
  have hsub : {ω | exitTime b N x₀ K (√ε) B hBc ω ≤ ENNReal.ofReal (Real.exp (β / ε))} ⊆
      {ω | solMap b N x₀ (√ε • brownPath B hBc ((n + 1) * T) ω) ∈
        {φ : C(Icc (0 : ℝ) ((n + 1) * T : ℝ≥0), E) | ∃ t, φ t ∉ K}} := by
    intro ω hω
    refine exists_notMem_of_exitTime_lt hBc hb N x₀ (√ε) (lt_of_le_of_lt hω ?_)
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff ((Real.exp_pos _).trans hH)).mpr hH
  refine (measure_mono hsub).trans ((hsurv n).trans ?_)
  rw [show ((n : ℝ≥0∞) + 1) = ENNReal.ofReal ((n : ℝ) + 1) by
    rw [ENNReal.ofReal_add (by positivity) zero_le_one]; simp, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- `(n + 1) 2m² e^{−D/ε} ≤ e^{−g/(2ε)}`
  set u := Real.exp (-(5 * g / 16) / ε) with hu
  set w := Real.exp (-(g / 2) / ε) with hw
  set E1' := Real.exp (-β₁ / ε) with hE1'
  have hEE : E1 * E1' = 1 := by rw [hE1, hE1', ← Real.exp_add]; simp [neg_div]
  have hE1'1 : E1' ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
    (by linarith) hε.le)
  have hu1 : u ≤ (T : ℝ) / (4 * (m : ℝ) ^ 2) := h5.trans (min_le_left _ _)
  have hu2 : u ≤ 1 / (8 * (m : ℝ) ^ 2) := h5.trans (min_le_right _ _)
  have hDexp : Real.exp (-(vt - vb - Δ - 2 * κ) / ε) ≤ E1' * u * w := by
    rw [hE1', hu, hw, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have e : -β₁ / ε + -(5 * g / 16) / ε + -(g / 2) / ε = -(β₁ + 13 * g / 16) / ε := by ring
    rw [e]
    exact div_le_div_of_nonneg_right (by rw [hg_def]; linarith) hε.le
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hu0 : 0 ≤ u := (Real.exp_pos _).le
  have hw0 : 0 ≤ w := (Real.exp_pos _).le
  have hE1'0 : 0 ≤ E1' := (Real.exp_pos _).le
  calc ((n : ℝ) + 1) * (2 * (m : ℝ) ^ 2 * Real.exp (-(vt - vb - Δ - 2 * κ) / ε))
      ≤ (E1 / T + 2) * (2 * (m : ℝ) ^ 2 * (E1' * u * w)) :=
        mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hDexp (by positivity))
          (by positivity) (by positivity)
    _ = 2 * (m : ℝ) ^ 2 / T * u * w * (E1 * E1') + 4 * (m : ℝ) ^ 2 * E1' * u * w := by
        field_simp; ring
    _ ≤ 2 * (m : ℝ) ^ 2 / T * ((T : ℝ) / (4 * (m : ℝ) ^ 2)) * w * 1 +
          4 * (m : ℝ) ^ 2 * 1 * (1 / (8 * (m : ℝ) ^ 2)) * w := by
        rw [hEE]
        gcongr
    _ = w := by field_simp; ring

end powerlib.Stochastic.LDP
