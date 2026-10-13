import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.Markov
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Probabilistic safety / reachability of a discrete-time Markov chain by dynamic programming

Source: work-sync `theory/T-reachability-stochastic.md` (reach / safety probability
`r(x, t)` of a Markov process, Abate et al. 2008 dynamic programming recursion for discrete-time
Markov kernels: `V_N = 1`, `V_k(x) = ∫ 1_A(y) V_{k+1}(y) Q(x, dy)`).

Foundation (probability), not an engineering result.

Setting: a process `X` adapted to a filtration `𝓕` on a probability space that is Markov with
kernels `K s t` (conditional-expectation form, written out as the hypothesis `h` of each theorem:
for `s ≤ t` and bounded measurable `g`, `E[g(X_t) | 𝓕_s] = ∫ g dK_{s,t}(X_s)` a.s.) and
time-homogeneous one-step kernel `Q = K k (k+1)`; a measurable safe set `A`.
* `safeValue Q A N`: the value function `V_0 = 1`, `V_{N+1}(x) = ∫ 1_A(y) V_N(y) Q(x, dy)`
  (`0 ≤ V_N ≤ 1`, measurable).
* `stayIn X A k N = ∏_{i<N} 1_A(X_{k+1+i})`: indicator that the path stays in `A` during the next
  `N` steps after time `k`.
* `safety_dp`: `P(X_{k+1}, …, X_{k+N} ∈ A | 𝓕_k) = V_N(X_k)` a.s. (dynamic programming).
* `safety_prob_eq`: `P(X_1, …, X_N ∈ A) = E[V_N(X_0)]`; the hitting probability of `Aᶜ`
  within `N` steps is `1 − E[V_N(X_0)]`.
* Reach-avoid (the note's `r(x, t) = P_x(τ_T ≤ t, τ_∂D > τ_T)` in discrete time):
  `reachAvoid X T D k N` is defined by the recursion `R_{k,0} = 1_T(X_k)`,
  `R_{k,N+1} = 1_T(X_k) + 1_{D∖T}(X_k) R_{k+1,N}`, and `reachAvoid_eq_indicator` shows it is the
  indicator of `{∃ j ≤ N, X_{k+j} ∈ T ∧ ∀ i < j, X_{k+i} ∈ D ∖ T}`; `reachValue` is
  `W_0 = 1_T`, `W_{N+1} = 1_T + 1_{D∖T} ∫ W_N dQ` (`0 ≤ W_N ≤ 1`), and `reachAvoid_dp`:
  `P(reach-avoid within N | 𝓕_k) = W_N(X_k)` a.s. (Abate et al. 2008 recursion).

Continuous-time HJB (deterministic optimal control; verification direction).
* `hjb_le_cost`: a `C¹` function `V` satisfying the HJB inequality
  `∂ₜV + D_yV · f(t, y, w) + L(t, y, w) ≥ 0` (all states `y`, all admissible `w`) and `V(T, ·) = g`
  is a lower bound for the cost of every admissible pair from `x(0)`;
* `hjb_eq_cost`: equality along a pair on which the HJB expression vanishes;
* `hjb_verification`: hence `V(0, x₀)` is the least admissible cost (the value) and a pair
  attaining the minimum in the HJB equation along its trajectory is optimal;
* `lq_value` (non-vacuity): for `ẋ = u`, cost `∫₀ᵀ (x² + u²)`, the Riccati solution
  `V(t, x) = tanh(T − t) x²` verifies HJB and the minimal cost from `x₀` is `tanh(T) x₀²`.
Proof: chain rule for `t ↦ V(t, x(t))` and the integral comparison
`intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le` / FTC.  The converse direction (the
value function, when `C¹`, satisfies HJB) and the stochastic HJB `∂ₜr + sup_u Lᵘ r = 0` of the note
are not formalized (the latter needs the generator of a controlled diffusion / Itô calculus).
-/

noncomputable section
namespace powerlib.Stochastic.Markov

open MeasureTheory ProbabilityTheory Filter Finset

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E]

/-- Safety value function: `V_0 = 1`, `V_{N+1}(x) = ∫ 1_A(y) V_N(y) Q(x, dy)`. -/
def safeValue (Q : Kernel E E) (A : Set E) : ℕ → E → ℝ
  | 0 => fun _ => 1
  | N + 1 => fun x => ∫ y, A.indicator (safeValue Q A N) y ∂(Q x)

@[powerlib_foundation] theorem safeValue_stronglyMeasurable (Q : Kernel E E) {A : Set E}
    (hA : MeasurableSet A) : ∀ N, StronglyMeasurable (safeValue Q A N)
  | 0 => stronglyMeasurable_const
  | N + 1 => ((safeValue_stronglyMeasurable Q hA N).indicator hA).integral_kernel

@[powerlib_foundation] theorem safeValue_mem_Icc (Q : Kernel E E) [IsMarkovKernel Q] (A : Set E) :
    ∀ N x, 0 ≤ safeValue Q A N x ∧ safeValue Q A N x ≤ 1
  | 0, x => by simp [safeValue]
  | N + 1, x => by
    have hb := safeValue_mem_Icc Q A N
    have h0 : ∀ y, 0 ≤ A.indicator (safeValue Q A N) y := fun y =>
      Set.indicator_nonneg (fun z _ => (hb z).1) y
    have h1 : ∀ y, A.indicator (safeValue Q A N) y ≤ 1 := fun y => by
      by_cases hy : y ∈ A
      · rw [Set.indicator_of_mem hy]; exact (hb y).2
      · rw [Set.indicator_of_notMem hy]; norm_num
    constructor
    · exact integral_nonneg h0
    · calc ∫ y, A.indicator (safeValue Q A N) y ∂(Q x) ≤ ∫ _, (1 : ℝ) ∂(Q x) := by
            refine integral_mono_of_nonneg (ae_of_all _ h0) (integrable_const 1)
              (ae_of_all _ h1)
        _ = 1 := by simp

/-- Indicator that the path stays in `A` at times `k+1, …, k+N`. -/
def stayIn (X : ℕ → Ω → E) (A : Set E) (k N : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ range N, A.indicator (fun _ => (1 : ℝ)) (X (k + 1 + i) ω)

omit [MeasurableSpace E] in
@[powerlib_foundation] theorem stayIn_succ (X : ℕ → Ω → E) (A : Set E) (k N : ℕ) :
    stayIn X A k (N + 1) = fun ω =>
      A.indicator (fun _ => (1 : ℝ)) (X (k + 1) ω) * stayIn X A (k + 1) N ω := by
  funext ω
  unfold stayIn
  rw [prod_range_succ', add_zero, mul_comm]
  congr 1
  refine prod_congr rfl fun i _ => ?_
  rw [show k + 1 + (i + 1) = k + 1 + 1 + i by omega]

@[powerlib_foundation] theorem stayIn_measurable {X : ℕ → Ω → E} (hX : ∀ n, Measurable (X n))
    {A : Set E} (hA : MeasurableSet A) (k N : ℕ) : Measurable (stayIn X A k N) := by
  unfold stayIn
  exact Finset.measurable_prod _ fun i _ => (measurable_const.indicator hA).comp (hX _)

omit [MeasurableSpace E] in
@[powerlib_foundation] theorem stayIn_abs_le (X : ℕ → Ω → E) (A : Set E) (k N : ℕ) (ω : Ω) :
    |stayIn X A k N ω| ≤ 1 := by
  unfold stayIn
  rw [abs_prod]
  refine prod_le_one₀ (fun i _ => abs_nonneg _) fun i _ => ?_
  by_cases h : X (k + 1 + i) ω ∈ A <;> simp [h]

/-- **Dynamic programming for safety probabilities**:
`P(X_{k+1}, …, X_{k+N} ∈ A | 𝓕_k) = V_N(X_k)` almost surely. -/
@[powerlib_foundation] theorem safety_dp {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℕ mΩ} {X : ℕ → Ω → E} {K : ℕ → ℕ → Kernel E E} {Q : Kernel E E}
    [IsMarkovKernel Q]
    (h : ∀ s t, s ≤ t → ∀ g : E → ℝ, Measurable g → (∃ C, ∀ y, |g y| ≤ C) →
      P[fun ω => g (X t ω) | 𝓕 s] =ᵐ[P] fun ω => ∫ y, g y ∂(K s t (X s ω)))
    (hQ : ∀ k, K k (k + 1) = Q)
    (hadapt : ∀ k, Measurable[𝓕 k] (X k)) {A : Set E} (hA : MeasurableSet A) :
    ∀ N k, P[stayIn X A k N | 𝓕 k] =ᵐ[P] fun ω => safeValue Q A N (X k ω) := by
  have hX : ∀ n, Measurable (X n) := fun n => (hadapt n).mono (𝓕.le n) le_rfl
  have hint : ∀ k N, Integrable (stayIn X A k N) P := fun k N =>
    Integrable.of_bound (stayIn_measurable hX hA k N).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using stayIn_abs_le X A k N ω)
  intro N
  induction N with
  | zero =>
    intro k
    have e : stayIn X A k 0 = fun _ => (1 : ℝ) := by funext ω; simp [stayIn]
    rw [e, condExp_const (𝓕.le k)]
    rfl
  | succ N ih =>
    intro k
    set ind : Ω → ℝ := fun ω => A.indicator (fun _ => (1 : ℝ)) (X (k + 1) ω) with hind
    have hindm : StronglyMeasurable[𝓕 (k + 1)] ind :=
      ((measurable_const.indicator hA).comp (hadapt (k + 1))).stronglyMeasurable
    have hindi : Integrable ind P :=
      Integrable.of_bound ((measurable_const.indicator hA).comp (hX (k + 1))).aestronglyMeasurable 1
        (ae_of_all _ fun ω => by
          by_cases hω : X (k + 1) ω ∈ A <;> simp [hind, hω])
    have hprod : stayIn X A k (N + 1) = ind * stayIn X A (k + 1) N := by
      rw [stayIn_succ]; rfl
    -- tower property
    have htower := condExp_condExp_of_le (𝓕.mono (Nat.le_succ k)) (𝓕.le (k + 1))
      (μ := P) (f := stayIn X A k (N + 1))
    -- inner conditional expectation
    have hinner : P[stayIn X A k (N + 1) | 𝓕 (k + 1)] =ᵐ[P]
        fun ω => A.indicator (safeValue Q A N) (X (k + 1) ω) := by
      rw [hprod]
      have hpull := condExp_mul_of_stronglyMeasurable_left hindm
        (by rw [← hprod]; exact hint k (N + 1)) (hint (k + 1) N)
      filter_upwards [hpull, ih (k + 1)] with ω h1 h2
      rw [h1, Pi.mul_apply, h2]
      by_cases hω : X (k + 1) ω ∈ A <;> simp [hind, hω]
    -- Markov step
    have hg : Measurable (A.indicator (safeValue Q A N)) :=
      ((safeValue_stronglyMeasurable Q hA N).measurable).indicator hA
    have hgb : ∃ C, ∀ y, |A.indicator (safeValue Q A N) y| ≤ C := ⟨1, fun y => by
      have hb := safeValue_mem_Icc Q A N y
      by_cases hy : y ∈ A
      · rw [Set.indicator_of_mem hy, abs_of_nonneg hb.1]; exact hb.2
      · rw [Set.indicator_of_notMem hy]; norm_num⟩
    have hmk := h k (k + 1) (Nat.le_succ k) _ hg hgb
    refine htower.symm.trans ((condExp_congr_ae hinner).trans (hmk.trans ?_))
    refine Filter.Eventually.of_forall fun ω => ?_
    simp only [hQ, safeValue]

/-- **Safety probability from the initial law**: `P(X_1, …, X_N ∈ A) = E[V_N(X_0)]`. -/
@[powerlib_foundation] theorem safety_prob_eq {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℕ mΩ} {X : ℕ → Ω → E} {K : ℕ → ℕ → Kernel E E} {Q : Kernel E E}
    [IsMarkovKernel Q]
    (h : ∀ s t, s ≤ t → ∀ g : E → ℝ, Measurable g → (∃ C, ∀ y, |g y| ≤ C) →
      P[fun ω => g (X t ω) | 𝓕 s] =ᵐ[P] fun ω => ∫ y, g y ∂(K s t (X s ω)))
    (hQ : ∀ k, K k (k + 1) = Q)
    (hadapt : ∀ k, Measurable[𝓕 k] (X k)) {A : Set E} (hA : MeasurableSet A) (N : ℕ) :
    ∫ ω, stayIn X A 0 N ω ∂P = ∫ ω, safeValue Q A N (X 0 ω) ∂P := by
  rw [← integral_condExp (𝓕.le 0)]
  exact integral_congr_ae (safety_dp h hQ hadapt hA N 0)

/-! ## Reach-avoid probability `r(x, t)` -/

/-- Reach-avoid indicator from time `k` with horizon `N`: `1` iff the path enters the target `T`
at some step `j ≤ N` while staying in `D \ T` before (`r(x, t) = P_x(τ_T ≤ t, τ_∂D > τ_T)` in
discrete time). Defined by the recursion `R_{k,0} = 1_T(X_k)`,
`R_{k,N+1} = 1_T(X_k) + 1_{D∖T}(X_k) R_{k+1,N}`. -/
def reachAvoid (X : ℕ → Ω → E) (T D : Set E) : ℕ → ℕ → Ω → ℝ
  | k, 0 => fun ω => T.indicator (fun _ => (1 : ℝ)) (X k ω)
  | k, N + 1 => fun ω => T.indicator (fun _ => (1 : ℝ)) (X k ω) +
      (D \ T).indicator (fun _ => (1 : ℝ)) (X k ω) * reachAvoid X T D (k + 1) N ω

omit [MeasurableSpace E] in
open scoped Classical in
/-- The recursion computes the indicator of the reach-avoid event
`∃ j ≤ N, X_{k+j} ∈ T ∧ ∀ i < j, X_{k+i} ∈ D \ T`. -/
@[powerlib_foundation] theorem reachAvoid_eq_indicator (X : ℕ → Ω → E) (T D : Set E) :
    ∀ N k ω, reachAvoid X T D k N ω =
      if ∃ j ≤ N, X (k + j) ω ∈ T ∧ ∀ i < j, X (k + i) ω ∈ D \ T then 1 else 0 := by
  intro N
  induction N with
  | zero =>
    intro k ω
    by_cases h : X k ω ∈ T
    · simp [reachAvoid, h]
    · simp [reachAvoid, h]
  | succ N ih =>
    intro k ω
    simp only [reachAvoid]
    rw [ih (k + 1) ω]
    by_cases hT : X k ω ∈ T
    · have hex : ∃ j ≤ N + 1, X (k + j) ω ∈ T ∧ ∀ i < j, X (k + i) ω ∈ D \ T :=
        ⟨0, Nat.zero_le _, by simpa using hT, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
      have hDT : X k ω ∉ D \ T := fun h => h.2 hT
      rw [Set.indicator_of_mem hT, Set.indicator_of_notMem hDT, zero_mul, add_zero]
      simp only [hex, ↓reduceIte]
    · by_cases hD : X k ω ∈ D \ T
      · -- the event from `k` is the event from `k+1`, shifted by one step
        have hiff : (∃ j ≤ N + 1, X (k + j) ω ∈ T ∧ ∀ i < j, X (k + i) ω ∈ D \ T) ↔
            (∃ j ≤ N, X (k + 1 + j) ω ∈ T ∧ ∀ i < j, X (k + 1 + i) ω ∈ D \ T) := by
          constructor
          · rintro ⟨j, hj, hjT, hjD⟩
            rcases j with _ | j
            · exact absurd (by simpa using hjT) hT
            · refine ⟨j, by omega, by rwa [show k + 1 + j = k + (j + 1) by omega], fun i hi => ?_⟩
              have := hjD (i + 1) (by omega)
              rwa [show k + 1 + i = k + (i + 1) by omega]
          · rintro ⟨j, hj, hjT, hjD⟩
            refine ⟨j + 1, by omega, by rwa [show k + (j + 1) = k + 1 + j by omega], fun i hi => ?_⟩
            rcases i with _ | i
            · simpa using hD
            · have := hjD i (by omega)
              rwa [show k + (i + 1) = k + 1 + i by omega]
        simp only [hT, hD, hiff, Set.indicator_of_notMem, Set.indicator_of_mem, not_false_eq_true,
          zero_add, one_mul]
      · have hno : ¬ ∃ j ≤ N + 1, X (k + j) ω ∈ T ∧ ∀ i < j, X (k + i) ω ∈ D \ T := by
          rintro ⟨j, hj, hjT, hjD⟩
          rcases j with _ | j
          · exact hT (by simpa using hjT)
          · exact hD (by simpa using hjD 0 (by omega))
        simp only [hT, hD, hno, Set.indicator_of_notMem, not_false_eq_true, zero_mul, add_zero,
          ite_false]

/-- Reach-avoid value function: `W_0 = 1_T`, `W_{N+1}(x) = 1_T(x) + 1_{D∖T}(x) ∫ W_N dQ(x)`. -/
def reachValue (Q : Kernel E E) (T D : Set E) : ℕ → E → ℝ
  | 0 => fun x => T.indicator (fun _ => (1 : ℝ)) x
  | N + 1 => fun x => T.indicator (fun _ => (1 : ℝ)) x +
      (D \ T).indicator (fun _ => (1 : ℝ)) x * ∫ y, reachValue Q T D N y ∂(Q x)

@[powerlib_foundation] theorem reachValue_stronglyMeasurable (Q : Kernel E E) {T D : Set E}
    (hT : MeasurableSet T) (hD : MeasurableSet D) :
    ∀ N, StronglyMeasurable (reachValue Q T D N)
  | 0 => (measurable_const.indicator hT).stronglyMeasurable
  | N + 1 => (measurable_const.indicator hT).stronglyMeasurable.add
      ((measurable_const.indicator (hD.diff hT)).stronglyMeasurable.mul
        (reachValue_stronglyMeasurable Q hT hD N).integral_kernel)

@[powerlib_foundation] theorem reachValue_mem_Icc (Q : Kernel E E) [IsMarkovKernel Q]
    (T D : Set E) : ∀ N x, 0 ≤ reachValue Q T D N x ∧ reachValue Q T D N x ≤ 1
  | 0, x => by
    by_cases h : x ∈ T <;> simp [reachValue, h]
  | N + 1, x => by
    have hb := reachValue_mem_Icc Q T D N
    have hI0 : 0 ≤ ∫ y, reachValue Q T D N y ∂(Q x) := integral_nonneg fun y => (hb y).1
    have hI1 : ∫ y, reachValue Q T D N y ∂(Q x) ≤ 1 := by
      calc ∫ y, reachValue Q T D N y ∂(Q x) ≤ ∫ _, (1 : ℝ) ∂(Q x) :=
            integral_mono_of_nonneg (ae_of_all _ fun y => (hb y).1) (integrable_const 1)
              (ae_of_all _ fun y => (hb y).2)
        _ = 1 := by simp
    simp only [reachValue]
    by_cases hT : x ∈ T
    · have hDT : x ∉ D \ T := fun h => h.2 hT
      simp [hT, hDT]
    · by_cases hD : x ∈ D \ T
      · simp only [hT, hD, Set.indicator_of_notMem, Set.indicator_of_mem, not_false_eq_true,
          zero_add, one_mul]
        exact ⟨hI0, hI1⟩
      · simp [hT, hD]

@[powerlib_foundation] theorem reachAvoid_measurable {X : ℕ → Ω → E}
    (hX : ∀ n, Measurable (X n)) {T D : Set E} (hT : MeasurableSet T) (hD : MeasurableSet D) :
    ∀ N k, Measurable (reachAvoid X T D k N) := by
  intro N
  induction N with
  | zero => intro k; exact (measurable_const.indicator hT).comp (hX k)
  | succ N ih =>
    intro k
    exact ((measurable_const.indicator hT).comp (hX k)).add
      (((measurable_const.indicator (hD.diff hT)).comp (hX k)).mul (ih (k + 1)))

omit [MeasurableSpace E] in
@[powerlib_foundation] theorem reachAvoid_abs_le (X : ℕ → Ω → E) (T D : Set E) (N k : ℕ)
    (ω : Ω) : |reachAvoid X T D k N ω| ≤ 1 := by
  rw [reachAvoid_eq_indicator]
  split_ifs <;> simp

/-- **Dynamic programming for the reach-avoid probability**:
`P(reach T within N steps while staying in D | 𝓕_k) = W_N(X_k)` almost surely. -/
@[powerlib_foundation] theorem reachAvoid_dp {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℕ mΩ} {X : ℕ → Ω → E} {K : ℕ → ℕ → Kernel E E} {Q : Kernel E E}
    [IsMarkovKernel Q]
    (h : ∀ s t, s ≤ t → ∀ g : E → ℝ, Measurable g → (∃ C, ∀ y, |g y| ≤ C) →
      P[fun ω => g (X t ω) | 𝓕 s] =ᵐ[P] fun ω => ∫ y, g y ∂(K s t (X s ω)))
    (hQ : ∀ k, K k (k + 1) = Q)
    (hadapt : ∀ k, Measurable[𝓕 k] (X k)) {T D : Set E} (hT : MeasurableSet T)
    (hD : MeasurableSet D) :
    ∀ N k, P[reachAvoid X T D k N | 𝓕 k] =ᵐ[P] fun ω => reachValue Q T D N (X k ω) := by
  have hX : ∀ n, Measurable (X n) := fun n => (hadapt n).mono (𝓕.le n) le_rfl
  have hint : ∀ N k, Integrable (reachAvoid X T D k N) P := fun N k =>
    Integrable.of_bound (reachAvoid_measurable hX hT hD N k).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using reachAvoid_abs_le X T D N k ω)
  have hindT : ∀ k, StronglyMeasurable[𝓕 k] (fun ω => T.indicator (fun _ => (1 : ℝ)) (X k ω)) :=
    fun k => ((measurable_const.indicator hT).comp (hadapt k)).stronglyMeasurable
  have hindD : ∀ k, StronglyMeasurable[𝓕 k]
      (fun ω => (D \ T).indicator (fun _ => (1 : ℝ)) (X k ω)) :=
    fun k => ((measurable_const.indicator (hD.diff hT)).comp (hadapt k)).stronglyMeasurable
  have hbdd : ∀ (S : Set E) (k : ℕ), MeasurableSet S →
      Integrable (fun ω => S.indicator (fun _ => (1 : ℝ)) (X k ω)) P := fun S k hS =>
    Integrable.of_bound ((measurable_const.indicator hS).comp (hX k)).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by by_cases hω : X k ω ∈ S <;> simp [hω])
  intro N
  induction N with
  | zero =>
    intro k
    exact (condExp_of_stronglyMeasurable (𝓕.le k) (hindT k) (hbdd T k hT)).eventuallyEq
  | succ N ih =>
    intro k
    set a : Ω → ℝ := fun ω => T.indicator (fun _ => (1 : ℝ)) (X k ω) with ha
    set b : Ω → ℝ := fun ω => (D \ T).indicator (fun _ => (1 : ℝ)) (X k ω) with hb
    set R : Ω → ℝ := reachAvoid X T D (k + 1) N with hR
    have hsplit : reachAvoid X T D k (N + 1) = a + b * R := by
      funext ω; simp only [reachAvoid, Pi.add_apply, Pi.mul_apply, ha, hb, hR]
    have hbR : Integrable (b * R) P := by
      have : b * R = fun ω => b ω * R ω := rfl
      exact Integrable.of_bound
        (((measurable_const.indicator (hD.diff hT)).comp (hX k)).mul
          (reachAvoid_measurable hX hT hD N (k + 1))).aestronglyMeasurable 1
        (ae_of_all _ fun ω => by
          have h1 := reachAvoid_abs_le X T D N (k + 1) ω
          simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, hb, hR]
          by_cases hω : X k ω ∈ D \ T <;> simp [hω, h1])
    have hadd := condExp_add (hbdd T k hT) hbR (𝓕 k) (μ := P)
    rw [condExp_of_stronglyMeasurable (𝓕.le k) (hindT k) (hbdd T k hT)] at hadd
    have hpull := condExp_mul_of_stronglyMeasurable_left (hindD k) hbR (hint N (k + 1))
    -- `E[R | 𝓕_k] = E[W_N(X_{k+1}) | 𝓕_k] = ∫ W_N dQ(X_k)`
    have htower := condExp_condExp_of_le (𝓕.mono (Nat.le_succ k)) (𝓕.le (k + 1))
      (μ := P) (f := R)
    have hg : Measurable (reachValue Q T D N) :=
      (reachValue_stronglyMeasurable Q hT hD N).measurable
    have hgb : ∃ C, ∀ y, |reachValue Q T D N y| ≤ C := ⟨1, fun y => by
      have := reachValue_mem_Icc Q T D N y
      rw [abs_of_nonneg this.1]; exact this.2⟩
    have hmk := h k (k + 1) (Nat.le_succ k) _ hg hgb
    have hRk : P[R | 𝓕 k] =ᵐ[P] fun ω => ∫ y, reachValue Q T D N y ∂(Q (X k ω)) := by
      refine htower.symm.trans ((condExp_congr_ae (ih (k + 1))).trans (hmk.trans ?_))
      refine Filter.Eventually.of_forall fun ω => ?_
      simp only [hQ]
    rw [hsplit]
    filter_upwards [hadd, hpull, hRk] with ω h1 h2 h3
    rw [h1, Pi.add_apply, h2, Pi.mul_apply, h3]
    simp only [reachValue]

/-! ## Continuous-time HJB: verification theorem (deterministic optimal control)

Finite-horizon problem: state `x(t) ∈ H` (a real normed space), control `u(t) ∈ Uad`, dynamics
`ẋ = f(t, x, u)` on `(0, T)`, cost `J(x, u) = ∫₀ᵀ L(t, x, u) dt + g(x(T))`.  The trajectories and
the cost are written out in the statements (no trajectory predicate is defined). -/

section HJB

variable {H A : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Chain rule along a trajectory: `d/dt V(t, x(t)) = DV(t, x(t)) (1, ẋ(t))`. -/
private theorem hasDerivAt_value_along {V : ℝ × H → ℝ} {DV : ℝ × H → (ℝ × H →L[ℝ] ℝ)}
    (hV : ∀ p, HasFDerivAt V (DV p) p) {x : ℝ → H} {v : H} {t : ℝ} (hx : HasDerivAt x v t) :
    HasDerivAt (fun s => V (s, x s)) (DV (t, x t) (1, v)) t := by
  have hp : HasDerivAt (fun s => (s, x s)) ((1 : ℝ), v) t := (hasDerivAt_id t).prodMk hx
  exact (hV (t, x t)).comp_hasDerivAt t hp

private theorem continuousOn_value_along {V : ℝ × H → ℝ} {DV : ℝ × H → (ℝ × H →L[ℝ] ℝ)}
    (hV : ∀ p, HasFDerivAt V (DV p) p) {x : ℝ → H} {T : ℝ} (hxc : ContinuousOn x (Set.Icc 0 T)) :
    ContinuousOn (fun s => V (s, x s)) (Set.Icc 0 T) := by
  have hVc : Continuous V := continuous_iff_continuousAt.mpr fun p => (hV p).continuousAt
  exact hVc.comp_continuousOn (continuousOn_id.prodMk hxc)

/-- **HJB verification, lower bound.**  If `V` is `C¹` on `ℝ × H` and satisfies the HJB
inequality `∂ₜV(t, y) + D_yV(t, y) f(t, y, w) + L(t, y, w) ≥ 0` for every state `y`, every
admissible control value `w ∈ Uad` and `t ∈ (0, T)`, with terminal condition `V(T, ·) = g`, then
for every admissible pair (`x` continuous on `[0, T]`, `ẋ = f(t, x, u)` and `u(t) ∈ Uad` on
`(0, T)`, running cost integrable) `V(0, x(0)) ≤ ∫₀ᵀ L(t, x, u) dt + g(x(T))`.
(`DV p (1, v)` is `∂ₜV + D_yV · v`.) -/
theorem hjb_le_cost {f : ℝ → H → A → H} {L : ℝ → H → A → ℝ} {g : H → ℝ} {Uad : Set A}
    {V : ℝ × H → ℝ} {DV : ℝ × H → (ℝ × H →L[ℝ] ℝ)} {T : ℝ} (hT : 0 ≤ T)
    (hV : ∀ p, HasFDerivAt V (DV p) p)
    (hHJB : ∀ t ∈ Set.Ioo 0 T, ∀ y, ∀ w ∈ Uad, 0 ≤ DV (t, y) (1, f t y w) + L t y w)
    (hterm : ∀ y, V (T, y) = g y)
    {x : ℝ → H} {u : ℝ → A} (hxc : ContinuousOn x (Set.Icc 0 T))
    (hx : ∀ t ∈ Set.Ioo 0 T, HasDerivAt x (f t (x t) (u t)) t) (hu : ∀ t ∈ Set.Ioo 0 T, u t ∈ Uad)
    (hL : IntegrableOn (fun t => L t (x t) (u t)) (Set.Icc 0 T)) :
    V (0, x 0) ≤ (∫ t in (0 : ℝ)..T, L t (x t) (u t)) + g (x T) := by
  have h := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hT
    (continuousOn_value_along hV hxc).neg
    (fun t ht => ((hasDerivAt_value_along hV (hx t ht)).neg).hasDerivWithinAt) hL
    (fun t ht => by
      have := hHJB t ht (x t) (u t) (hu t ht)
      linarith)
  simp only [Pi.neg_apply] at h
  rw [← hterm]
  linarith

/-- **HJB verification, equality along a minimizing pair**: if the HJB expression vanishes along
`(x, u)` (the control attains the minimum in the Hamiltonian along its own trajectory), the cost of
`(x, u)` equals `V(0, x(0))`. -/
theorem hjb_eq_cost {f : ℝ → H → A → H} {L : ℝ → H → A → ℝ} {g : H → ℝ}
    {V : ℝ × H → ℝ} {DV : ℝ × H → (ℝ × H →L[ℝ] ℝ)} {T : ℝ} (hT : 0 ≤ T)
    (hV : ∀ p, HasFDerivAt V (DV p) p)
    (hterm : ∀ y, V (T, y) = g y)
    {x : ℝ → H} {u : ℝ → A} (hxc : ContinuousOn x (Set.Icc 0 T))
    (hx : ∀ t ∈ Set.Ioo 0 T, HasDerivAt x (f t (x t) (u t)) t)
    (hopt : ∀ t ∈ Set.Ioo 0 T, DV (t, x t) (1, f t (x t) (u t)) + L t (x t) (u t) = 0)
    (hL : IntervalIntegrable (fun t => L t (x t) (u t)) volume 0 T) :
    V (0, x 0) = (∫ t in (0 : ℝ)..T, L t (x t) (u t)) + g (x T) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
    (continuousOn_value_along hV hxc).neg
    (fun t ht => by
      have h1 := (hasDerivAt_value_along hV (hx t ht)).neg
      have h2 : -(DV (t, x t)) (1, f t (x t) (u t)) = L t (x t) (u t) := by
        linarith [hopt t ht]
      rwa [h2] at h1) hL
  simp only [Pi.neg_apply] at h
  rw [← hterm]
  linarith

/-- **HJB verification theorem (finite horizon, deterministic, continuous time).**  Let `V` be
`C¹` with `V(T, ·) = g` and satisfy the HJB equation in the form
`min_{w ∈ Uad} [∂ₜV + D_yV · f(t, y, w) + L(t, y, w)] = 0`: the expression is `≥ 0` for all `w`, and
`= 0` along an admissible pair `(x*, u*)` from `x₀`.  Then `V(0, x₀)` is the **least** cost over all
admissible pairs from `x₀` — `V(0, x₀)` is the value of the problem and `(x*, u*)` is optimal. -/
theorem hjb_verification {f : ℝ → H → A → H} {L : ℝ → H → A → ℝ} {g : H → ℝ} {Uad : Set A}
    {V : ℝ × H → ℝ} {DV : ℝ × H → (ℝ × H →L[ℝ] ℝ)} {T : ℝ} (hT : 0 ≤ T)
    (hV : ∀ p, HasFDerivAt V (DV p) p)
    (hHJB : ∀ t ∈ Set.Ioo 0 T, ∀ y, ∀ w ∈ Uad, 0 ≤ DV (t, y) (1, f t y w) + L t y w)
    (hterm : ∀ y, V (T, y) = g y) (x₀ : H)
    {xs : ℝ → H} {us : ℝ → A} (hxs0 : xs 0 = x₀) (hxsc : ContinuousOn xs (Set.Icc 0 T))
    (hxs : ∀ t ∈ Set.Ioo 0 T, HasDerivAt xs (f t (xs t) (us t)) t)
    (hus : ∀ t ∈ Set.Ioo 0 T, us t ∈ Uad)
    (hopt : ∀ t ∈ Set.Ioo 0 T, DV (t, xs t) (1, f t (xs t) (us t)) + L t (xs t) (us t) = 0)
    (hLs : IntegrableOn (fun t => L t (xs t) (us t)) (Set.Icc 0 T)) :
    IsLeast {J | ∃ (x : ℝ → H) (u : ℝ → A), x 0 = x₀ ∧ ContinuousOn x (Set.Icc 0 T) ∧
        (∀ t ∈ Set.Ioo 0 T, HasDerivAt x (f t (x t) (u t)) t) ∧ (∀ t ∈ Set.Ioo 0 T, u t ∈ Uad) ∧
        IntegrableOn (fun t => L t (x t) (u t)) (Set.Icc 0 T) ∧
        J = (∫ t in (0 : ℝ)..T, L t (x t) (u t)) + g (x T)} (V (0, x₀)) := by
  refine ⟨⟨xs, us, hxs0, hxsc, hxs, hus, hLs, ?_⟩, ?_⟩
  · rw [← hxs0]
    exact hjb_eq_cost hT hV hterm hxsc hxs hopt
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr hLs)
  · rintro J ⟨x, u, hx0, hxc, hx, hu, hL, rfl⟩
    rw [← hx0]
    exact hjb_le_cost hT hV hHJB hterm hxc hx hu hL

end HJB

section LQ

open Real

/-- Riccati solution `p(t) = tanh(T − t)` of `ṗ = p² − 1`, `p(T) = 0`. -/
def lqGain (T t : ℝ) : ℝ := sinh (T - t) / cosh (T - t)

private theorem lqGain_hasDerivAt (T t : ℝ) :
    HasDerivAt (lqGain T) (lqGain T t ^ 2 - 1) t := by
  have hc : cosh (T - t) ≠ 0 := (cosh_pos _).ne'
  have hs : HasDerivAt (fun s => sinh (T - s)) (-cosh (T - t)) t := by
    have := ((hasDerivAt_id' t).const_sub T).sinh
    convert this using 1; ring
  have hco : HasDerivAt (fun s => cosh (T - s)) (-sinh (T - t)) t := by
    have := ((hasDerivAt_id' t).const_sub T).cosh
    convert this using 1; ring
  have h := hs.div hco hc
  refine h.congr_deriv ?_
  unfold lqGain
  have hid := cosh_sq_sub_sinh_sq (T - t)
  field_simp
  linarith

private theorem lqGain_continuous (T : ℝ) : Continuous (lqGain T) :=
  continuous_iff_continuousAt.mpr fun t => (lqGain_hasDerivAt T t).continuousAt

/-- `V(t, x) = p(t) x²`. -/
def lqValue (T : ℝ) (q : ℝ × ℝ) : ℝ := lqGain T q.1 * q.2 ^ 2

/-- Its derivative `DV(t, x)(τ, ξ) = ṗ(t) x² τ + 2 p(t) x ξ`. -/
def lqDValue (T : ℝ) (q : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  ((lqGain T q.1 ^ 2 - 1) * q.2 ^ 2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (2 * lqGain T q.1 * q.2) • ContinuousLinearMap.snd ℝ ℝ ℝ

private theorem lqValue_hasFDerivAt (T : ℝ) (q : ℝ × ℝ) :
    HasFDerivAt (lqValue T) (lqDValue T q) q := by
  have h1 : HasFDerivAt (fun r : ℝ × ℝ => lqGain T r.1)
      ((lqGain T q.1 ^ 2 - 1) • ContinuousLinearMap.fst ℝ ℝ ℝ) q :=
    (lqGain_hasDerivAt T q.1).comp_hasFDerivAt q (hasFDerivAt_fst (𝕜 := ℝ) (p := q))
  have h2 := (hasDerivAt_pow 2 q.2).comp_hasFDerivAt q (hasFDerivAt_snd (𝕜 := ℝ) (p := q))
  have h : HasFDerivAt (lqValue T) _ q := h1.mul h2
  refine h.congr_fderiv (ContinuousLinearMap.ext fun r => ?_)
  simp [lqDValue]
  ring

/-- **Linear–quadratic example of the HJB verification theorem.**  For `ẋ = u` on `[0, T]`
(`T ≥ 0`), `u` unconstrained, and cost `∫₀ᵀ (x² + u²) dt`, the minimal cost from `x₀` is
`tanh(T) x₀²`, attained by the feedback `u = −tanh(T − t) x`, i.e.
`x*(t) = x₀ cosh(T − t) / cosh T`. -/
@[powerlib_foundation] theorem lq_value {T : ℝ} (hT : 0 ≤ T) (x₀ : ℝ) :
    IsLeast {J | ∃ (x u : ℝ → ℝ), x 0 = x₀ ∧ ContinuousOn x (Set.Icc 0 T) ∧
        (∀ t ∈ Set.Ioo 0 T, HasDerivAt x (u t) t) ∧
        MeasureTheory.IntegrableOn (fun t => x t ^ 2 + u t ^ 2) (Set.Icc 0 T) ∧
        J = ∫ t in (0 : ℝ)..T, (x t ^ 2 + u t ^ 2)}
      (sinh T / cosh T * x₀ ^ 2) := by
  set xs : ℝ → ℝ := fun t => x₀ * cosh (T - t) / cosh T with hxs
  set us : ℝ → ℝ := fun t => -(lqGain T t * xs t) with hus
  have hcT : cosh T ≠ 0 := (cosh_pos _).ne'
  have hxsd : ∀ t, HasDerivAt xs (us t) t := by
    intro t
    have hco : HasDerivAt (fun s => cosh (T - s)) (-sinh (T - t)) t := by
      have := ((hasDerivAt_id' t).const_sub T).cosh
      convert this using 1; ring
    have := (hco.const_mul x₀).div_const (cosh T)
    refine this.congr_deriv ?_
    simp only [hus, hxs, lqGain]
    have : cosh (T - t) ≠ 0 := (cosh_pos _).ne'
    field_simp
  have hxsc : Continuous xs := continuous_iff_continuousAt.mpr fun t => (hxsd t).continuousAt
  have hc : Continuous fun t => xs t ^ 2 + us t ^ 2 := by
    have : Continuous us := ((lqGain_continuous T).mul hxsc).neg
    fun_prop
  have h := hjb_verification (f := fun _ _ w => w) (L := fun _ y w => y ^ 2 + w ^ 2)
    (g := fun _ => 0) (Uad := Set.univ) (V := lqValue T) (DV := lqDValue T) hT
    (lqValue_hasFDerivAt T)
    (fun t _ y w _ => by
      simp only [lqDValue, add_apply, smul_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
      nlinarith [sq_nonneg (w + lqGain T t * y)])
    (fun y => by simp [lqValue, lqGain]) x₀ (xs := xs) (us := us)
    (by simp [hxs, hcT]) hxsc.continuousOn (fun t _ => hxsd t) (fun _ _ => Set.mem_univ _)
    (fun t _ => by
      simp only [lqDValue, add_apply, smul_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, hus]
      ring)
    (hc.continuousOn.integrableOn_Icc)
  simp only [Set.mem_univ, implies_true, true_and, add_zero] at h
  have hv : lqValue T (0, x₀) = sinh T / cosh T * x₀ ^ 2 := by simp [lqValue, lqGain]
  rw [hv] at h
  exact h

end LQ

end powerlib.Stochastic.Markov
