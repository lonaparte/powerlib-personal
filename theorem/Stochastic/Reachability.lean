import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.Markov
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

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

The note's continuous-time backward PDE / HJB characterization is not formalized (it needs the
generator of a diffusion).
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

end powerlib.Stochastic.Markov
