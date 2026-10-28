import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.Brownian
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.Variance

/-! # Quadratic variation of Brownian motion in `L²`

The quadratic sums of Brownian motion along deterministic partitions converge to the elapsed
time in `L²`; along path-dependent partitions they need not.

Scope.
* `W` is Mathlib's `IsPreBrownianReal` (finite-dimensional laws of Brownian motion; path
  continuity is not used). Everything is proved from independence of increments and the
  Gaussian moments `E X² = v`, `E X⁴ = 3v²` (the fourth moment is obtained from the moment
  generating function `exp(v s²/2)`).
* A result about Brownian motion, not an engineering stability conclusion.

Source: work-sync theory/T-sde-systems.md §1.2 (quadratic variation `[W]_t = t`:
`∑ (W_{t_{i+1}} − W_{t_i})² → t` as the mesh of the partition of `[0, t]` tends to `0`).

Results.
* `integral_pow_four_gaussianReal_zero` — `∫ x⁴ dN(0, v) = 3 v²`;
  `variance_sq_of_hasLaw_gaussian`: `Var(X²) = 2v²` for `X ~ N(0, v)`.
* `qvSum_mean` — `E ∑ (ΔW_i)² = t_n − t_0`.
* `qvSum_L2_identity` — `E[(∑ (ΔW_i)² − (t_n − t_0))²] = 2 ∑ (Δt_i)²` for every monotone
  partition (independent increments + Gaussian fourth moment).
* `qvSum_L2_le` — if every step is `≤ δ`, the `L²` error is `≤ 2 δ (t_n − t_0)`.
* `qv_tendsto_L2` — for partitions of `[0, T]` with mesh `δ_k → 0` the `L²` error tends to `0`;
  `qv_tendsto_inProbability`: hence convergence in probability (Chebyshev).

Corrections.
* T-sde-systems §1.2: the quadratic-variation limit holds in `L²` (hence in probability) for
  **arbitrary deterministic** partitions with vanishing mesh, which is what is proved here.
  "`∑ (ΔW)² → t` almost surely along any partitions with mesh → 0" is false once the partitions
  may depend on the path; formal counterexample:
  * `greedyPartition B T k ω`: start from the dyadic grid of `[0, T]` with `2^(k+1)` steps and
    delete the midpoint `t_{2j+1}` of each pair exactly when the two half-increments have the
    same strict sign (encoded as a time sequence with a repeated point);
    `greedyPartition_spec`: a partition of `[0, T]` with mesh `≤ T / 2^k`;
    `qvSum_greedyPartition`: its quadratic sum is `∑_j g(a_j, b_j)`, `g(a, b) = (a + b)²` if
    `ab > 0` and `a² + b²` otherwise;
  * `greedyQV_mean`: `E = T (1 + 2m²)` with `m = E[Z⁺] > 0` (`posPartMean_pos`; Gaussian scaling
    and independence of the half-increments); `greedyQV_variance_le`: `Var ≤ 12 T² / 2^k`;
  * `greedyQV_tendstoInMeasure`: the sums converge in probability to `T (1 + 2m²) ≠ T`;
  * `qv_pathDependent_not_ae`: for `T > 0`, for `P`-almost every path the quadratic sums along
    these path-dependent partitions with mesh `→ 0` do **not** converge to `T`.
  (`m = 1/√(2π)`, so the limit is `T (1 + 1/π)`; the exact value is not needed and not
  formalized.)

Not formalized.
* Whether `a.s.` convergence can fail along **deterministic** partitions with mesh `→ 0` (it
  can, for slowly shrinking non-nested meshes).
-/

noncomputable section
namespace powerlib.Stochastic.QV

open MeasureTheory ProbabilityTheory Real Filter Finset
open scoped NNReal ENNReal Topology

/-! ## Gaussian fourth moment -/

/-- Every exponential moment of `N(μ, v)` is finite, so `0` lies in the interior of the
exponential-integrability set. -/
@[tmio T, powerlib_foundation] theorem zero_mem_interior_integrableExpSet_gaussianReal (m : ℝ)
    (v : ℝ≥0) : (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal m v)) := by
  have : integrableExpSet id (gaussianReal m v) = Set.univ := by
    ext s
    simp only [integrableExpSet, id, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact integrable_exp_mul_gaussianReal s
  simp [this]

/-- All polynomial moments of a Gaussian are finite. -/
@[powerlib_foundation] theorem integrable_pow_gaussianReal (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal m v) :=
  integrable_pow_of_mem_interior_integrableExpSet
    (zero_mem_interior_integrableExpSet_gaussianReal m v) n

/-- `∫ x⁴ dN(0, v) = 3 v²`. -/
@[powerlib_foundation] theorem integral_pow_four_gaussianReal_zero (v : ℝ≥0) :
    ∫ x, x ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  have h := iteratedDeriv_mgf_zero (zero_mem_interior_integrableExpSet_gaussianReal 0 v) 4
  rw [mgf_id_gaussianReal] at h
  set a : ℝ := (v : ℝ) / 2 with ha
  let E : ℝ → ℝ := fun s => rexp (a * s ^ 2)
  have hf : (fun s : ℝ => rexp (0 * s + (v : ℝ) * s ^ 2 / 2)) = E := by
    funext s; simp only [E, ha]; congr 1; ring
  have dE : ∀ s, HasDerivAt E (2 * a * s * E s) s := by
    intro s
    have := ((hasDerivAt_pow 2 s).const_mul a).exp
    convert this using 1
    simp only [E]; ring
  have e1 : deriv E = fun s => (2 * a * s) * E s := funext fun s => (dE s).deriv
  have e2 : deriv (fun s => (2 * a * s) * E s) = fun s => (2 * a + 4 * a ^ 2 * s ^ 2) * E s := by
    funext s
    have hp : HasDerivAt (fun s : ℝ => 2 * a * s) (2 * a) s := by
      simpa using (hasDerivAt_id s).const_mul (2 * a)
    have hd : HasDerivAt (fun s => (2 * a * s) * E s) ((2 * a + 4 * a ^ 2 * s ^ 2) * E s) s := by
      convert hp.mul (dE s) using 1; ring
    exact hd.deriv
  have e3 : deriv (fun s => (2 * a + 4 * a ^ 2 * s ^ 2) * E s) =
      fun s => (12 * a ^ 2 * s + 8 * a ^ 3 * s ^ 3) * E s := by
    funext s
    have hp : HasDerivAt (fun s : ℝ => 2 * a + 4 * a ^ 2 * s ^ 2) (4 * a ^ 2 * (2 * s)) s := by
      have := ((hasDerivAt_pow 2 s).const_mul (4 * a ^ 2)).const_add (2 * a)
      convert this using 1; push_cast; ring
    have hd : HasDerivAt (fun s => (2 * a + 4 * a ^ 2 * s ^ 2) * E s)
        ((12 * a ^ 2 * s + 8 * a ^ 3 * s ^ 3) * E s) s := by
      convert hp.mul (dE s) using 1; ring
    exact hd.deriv
  have e4 : deriv (fun s => (12 * a ^ 2 * s + 8 * a ^ 3 * s ^ 3) * E s) =
      fun s => (12 * a ^ 2 + 48 * a ^ 3 * s ^ 2 + 16 * a ^ 4 * s ^ 4) * E s := by
    funext s
    have hp : HasDerivAt (fun s : ℝ => 12 * a ^ 2 * s + 8 * a ^ 3 * s ^ 3)
        (12 * a ^ 2 + 8 * a ^ 3 * (3 * s ^ 2)) s := by
      have h1 : HasDerivAt (fun s : ℝ => 12 * a ^ 2 * s) (12 * a ^ 2) s := by
        simpa using (hasDerivAt_id s).const_mul (12 * a ^ 2)
      have h2 := (hasDerivAt_pow 3 s).const_mul (8 * a ^ 3)
      convert h1.add h2 using 1
    have hd : HasDerivAt (fun s => (12 * a ^ 2 * s + 8 * a ^ 3 * s ^ 3) * E s)
        ((12 * a ^ 2 + 48 * a ^ 3 * s ^ 2 + 16 * a ^ 4 * s ^ 4) * E s) s := by
      convert hp.mul (dE s) using 1; ring
    exact hd.deriv
  have hit : iteratedDeriv 4 E =
      fun s => (12 * a ^ 2 + 48 * a ^ 3 * s ^ 2 + 16 * a ^ 4 * s ^ 4) * E s := by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    rw [e1, e2, e3, e4]
  rw [hf, hit] at h
  simp only [E] at h
  have hr : ∫ x, x ^ 4 ∂(gaussianReal 0 v) = (gaussianReal 0 v)[id ^ 4] := by
    congr 1
  rw [hr, ← h, ha]
  simp
  ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- `X ~ N(0, v)` has all moments: `X^n` is integrable. -/
@[powerlib_foundation] theorem integrable_pow_of_hasLaw {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) (n : ℕ) : Integrable (fun ω => X ω ^ n) P :=
  hX.integrable_comp (f := fun x : ℝ => x ^ n) (integrable_pow_gaussianReal 0 v n)

omit [IsProbabilityMeasure P] in
/-- `X ~ N(0, v)` ⇒ `X² ∈ L²`. -/
@[powerlib_foundation] theorem memLp_sq_of_hasLaw {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) : MemLp (fun ω => X ω ^ 2) 2 P := by
  rw [memLp_two_iff_integrable_sq (hX.aemeasurable.pow_const 2).aestronglyMeasurable]
  have := integrable_pow_of_hasLaw hX 4
  refine this.congr (ae_of_all _ fun ω => ?_)
  simp only; ring

omit [IsProbabilityMeasure P] in
/-- `E X² = v` for `X ~ N(0, v)`. -/
@[powerlib_foundation] theorem integral_sq_of_hasLaw {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) : ∫ ω, X ω ^ 2 ∂P = v := by
  have := hX.integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
  simp only [Function.comp_def] at this
  rw [this, BM.integral_sq_gaussianReal_zero]

omit [IsProbabilityMeasure P] in
/-- `E X⁴ = 3v²` for `X ~ N(0, v)`. -/
@[powerlib_foundation] theorem integral_pow_four_of_hasLaw {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) : ∫ ω, X ω ^ 4 ∂P = 3 * (v : ℝ) ^ 2 := by
  have := hX.integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
  simp only [Function.comp_def] at this
  rw [this, integral_pow_four_gaussianReal_zero]

/-- `Var(X²) = 2v²` for `X ~ N(0, v)`. -/
@[powerlib_foundation] theorem variance_sq_of_hasLaw_gaussian {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) : variance (fun ω => X ω ^ 2) P = 2 * (v : ℝ) ^ 2 := by
  rw [variance_eq_sub (memLp_sq_of_hasLaw hX)]
  have e : (fun ω => X ω ^ 2) ^ 2 = fun ω => X ω ^ 4 := by
    funext ω; simp only [Pi.pow_apply]; ring
  rw [e, integral_pow_four_of_hasLaw hX, integral_sq_of_hasLaw hX]
  ring

/-! ## Quadratic variation along a partition -/

variable {B : ℝ≥0 → Ω → ℝ}

/-- Increment of `B` over the `i`-th step of the partition `t`. -/
def incr (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (i : ℕ) (ω : Ω) : ℝ := B (t (i + 1)) ω - B (t i) ω

/-- Quadratic-variation sum `∑_{i < n} (B_{t_{i+1}} − B_{t_i})²`. -/
def qvSum (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ range n, incr B t i ω ^ 2

/-- Step length `t_{i+1} − t_i` (as a real number). -/
def step (t : ℕ → ℝ≥0) (i : ℕ) : ℝ := (t (i + 1) : ℝ) - t i

@[powerlib_foundation] theorem step_nonneg {t : ℕ → ℝ≥0} (ht : Monotone t) (i : ℕ) :
    0 ≤ step t i := by
  unfold step; have := ht (Nat.le_succ i); rw [sub_nonneg]; exact_mod_cast this

@[powerlib_foundation] theorem sum_step (t : ℕ → ℝ≥0) (n : ℕ) :
    ∑ i ∈ range n, step t i = (t n : ℝ) - t 0 :=
  sum_range_sub (fun i => (t i : ℝ)) n

omit [IsProbabilityMeasure P] in
@[powerlib_foundation] theorem incr_hasLaw (hB : IsPreBrownianReal B P) {t : ℕ → ℝ≥0}
    (ht : Monotone t) (i : ℕ) : HasLaw (incr B t i) (gaussianReal 0 (t (i + 1) - t i)) P :=
  BM.increment_hasLaw hB (ht (Nat.le_succ i))

@[powerlib_foundation] theorem coe_step {t : ℕ → ℝ≥0} (ht : Monotone t) (i : ℕ) :
    ((t (i + 1) - t i : ℝ≥0) : ℝ) = step t i := by
  rw [NNReal.coe_sub (ht (Nat.le_succ i))]; rfl

omit [IsProbabilityMeasure P] in
/-- `E (ΔW_i)² = Δt_i`. -/
@[powerlib_foundation] theorem integral_incr_sq (hB : IsPreBrownianReal B P) {t : ℕ → ℝ≥0}
    (ht : Monotone t) (i : ℕ) : ∫ ω, incr B t i ω ^ 2 ∂P = step t i := by
  rw [integral_sq_of_hasLaw (incr_hasLaw hB ht i), coe_step ht]

/-- `E ∑ (ΔW_i)² = t_n − t_0`. -/
@[powerlib_foundation] theorem qvSum_mean (hB : IsPreBrownianReal B P) {t : ℕ → ℝ≥0}
    (ht : Monotone t) (n : ℕ) : ∫ ω, qvSum B t n ω ∂P = (t n : ℝ) - t 0 := by
  unfold qvSum
  rw [integral_finsetSum _ fun i _ => (memLp_sq_of_hasLaw (incr_hasLaw hB ht i)).integrable
    one_le_two]
  simp_rw [integral_incr_sq hB ht]
  exact sum_step t n

/-- `Var ∑ (ΔW_i)² = 2 ∑ (Δt_i)²` (pairwise independent increments). -/
@[powerlib_foundation] theorem qvSum_variance (hB : IsPreBrownianReal B P) {t : ℕ → ℝ≥0}
    (ht : Monotone t) (n : ℕ) : variance (qvSum B t n) P = 2 * ∑ i ∈ range n, step t i ^ 2 := by
  have hind := hB.hasIndepIncrements.nat (P := P) ht
  have e : qvSum B t n = ∑ i ∈ range n, fun ω => incr B t i ω ^ 2 := by
    funext ω; simp [qvSum, Finset.sum_apply]
  rw [e, IndepFun.variance_sum (fun i _ => memLp_sq_of_hasLaw (incr_hasLaw hB ht i))]
  · rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [variance_sq_of_hasLaw_gaussian (incr_hasLaw hB ht i), coe_step ht]
  · intro i _ j _ hij
    have := hind.indepFun hij
    exact this.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)

/-- **`L²` identity for the quadratic variation**:
`E[(∑ (ΔW_i)² − (t_n − t_0))²] = 2 ∑ (Δt_i)²`. -/
@[powerlib_foundation] theorem qvSum_L2_identity (hB : IsPreBrownianReal B P) {t : ℕ → ℝ≥0}
    (ht : Monotone t) (n : ℕ) :
    ∫ ω, (qvSum B t n ω - ((t n : ℝ) - t 0)) ^ 2 ∂P = 2 * ∑ i ∈ range n, step t i ^ 2 := by
  have hmeas : AEMeasurable (qvSum B t n) P := by
    unfold qvSum
    exact Finset.aemeasurable_fun_sum _ fun i _ =>
      ((incr_hasLaw hB ht i).aemeasurable.pow_const 2)
  rw [← qvSum_variance hB ht n, variance_eq_integral hmeas, qvSum_mean hB ht n]

/-- `L²` error bound by the mesh: if every step is `≤ δ` then the error is `≤ 2 δ (t_n − t_0)`. -/
@[powerlib_foundation] theorem qvSum_L2_le (hB : IsPreBrownianReal B P) {t : ℕ → ℝ≥0}
    (ht : Monotone t) (n : ℕ) {δ : ℝ} (hδ : ∀ i < n, step t i ≤ δ) :
    ∫ ω, (qvSum B t n ω - ((t n : ℝ) - t 0)) ^ 2 ∂P ≤ 2 * δ * ((t n : ℝ) - t 0) := by
  rw [qvSum_L2_identity hB ht n, ← sum_step t n, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  have h0 := step_nonneg ht i
  have h1 := hδ i (mem_range.mp hi)
  nlinarith

/-- **Quadratic variation in `L²`**: for partitions `0 = par_k(0) ≤ … ≤ par_k(N_k) = T` of `[0, T]`
whose mesh `δ_k → 0`, `E[(∑ (ΔW)² − T)²] → 0`. -/
@[powerlib_foundation] theorem qv_tendsto_L2 (hB : IsPreBrownianReal B P) {T : ℝ≥0}
    {par : ℕ → ℕ → ℝ≥0} {N : ℕ → ℕ} {δ : ℕ → ℝ} (hmono : ∀ k, Monotone (par k))
    (h0 : ∀ k, par k 0 = 0) (hT : ∀ k, par k (N k) = T)
    (hmesh : ∀ k, ∀ i < N k, step (par k) i ≤ δ k) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, (qvSum B (par k) (N k) ω - T) ^ 2 ∂P) atTop (𝓝 0) := by
  have hle : ∀ k, ∫ ω, (qvSum B (par k) (N k) ω - T) ^ 2 ∂P ≤ 2 * δ k * T := by
    intro k
    have := qvSum_L2_le hB (hmono k) (N k) (hmesh k)
    rwa [hT k, h0 k, NNReal.coe_zero, sub_zero] at this
  have hnn : ∀ k, 0 ≤ ∫ ω, (qvSum B (par k) (N k) ω - T) ^ 2 ∂P :=
    fun k => integral_nonneg fun ω => sq_nonneg _
  have hlim : Tendsto (fun k => 2 * δ k * (T : ℝ)) atTop (𝓝 0) := by
    have := (hδ.const_mul 2).mul_const (T : ℝ)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim hnn hle

/-- **Quadratic variation in probability**: under the same hypotheses,
`P(|∑ (ΔW)² − T| ≥ ε) → 0` for every `ε > 0` (Chebyshev). -/
@[powerlib_foundation] theorem qv_tendsto_inProbability (hB : IsPreBrownianReal B P) {T : ℝ≥0}
    {par : ℕ → ℕ → ℝ≥0} {N : ℕ → ℕ} {δ : ℕ → ℝ} (hmono : ∀ k, Monotone (par k))
    (h0 : ∀ k, par k 0 = 0) (hT : ∀ k, par k (N k) = T)
    (hmesh : ∀ k, ∀ i < N k, step (par k) i ≤ δ k)
    (hδ : Tendsto δ atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => P {ω | ε ≤ |qvSum B (par k) (N k) ω - T|}) atTop (𝓝 0) := by
  have hL2 := qv_tendsto_L2 hB hmono h0 hT hmesh hδ
  have hle : ∀ k, P {ω | ε ≤ |qvSum B (par k) (N k) ω - T|} ≤
      ENNReal.ofReal ((∫ ω, (qvSum B (par k) (N k) ω - T) ^ 2 ∂P) / ε ^ 2) := by
    intro k
    have hmeas : AEMeasurable (qvSum B (par k) (N k)) P := by
      unfold qvSum
      exact Finset.aemeasurable_fun_sum _ fun i _ =>
        ((incr_hasLaw hB (hmono k) i).aemeasurable.pow_const 2)
    have hm : MemLp (qvSum B (par k) (N k)) 2 P := by
      have e : qvSum B (par k) (N k) = ∑ i ∈ range (N k), fun ω => incr B (par k) i ω ^ 2 := by
        funext ω; simp [qvSum, Finset.sum_apply]
      rw [e]
      exact memLp_finsetSum' _ fun i _ => memLp_sq_of_hasLaw (incr_hasLaw hB (hmono k) i)
    have := meas_ge_le_variance_div_sq hm hε
    rw [variance_eq_integral hmeas, qvSum_mean hB (hmono k), hT k, h0 k, NNReal.coe_zero,
      sub_zero] at this
    exact this
  have hlim : Tendsto
      (fun k => ENNReal.ofReal ((∫ ω, (qvSum B (par k) (N k) ω - T) ^ 2 ∂P) / ε ^ 2))
      atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    apply ENNReal.tendsto_ofReal
    simpa using hL2.div_const (ε ^ 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hle

/-! ## Path-dependent partitions: no almost-sure quadratic variation -/

/-- Dyadic grid of `[0, T]` with `2^(k+1)` steps: `t_i = T i / 2^(k+1)`. -/
def dyadic (T : ℝ≥0) (k i : ℕ) : ℝ≥0 := T * ((i : ℝ≥0) / 2 ^ (k + 1))

@[powerlib_foundation] theorem coe_dyadic (T : ℝ≥0) (k i : ℕ) :
    (dyadic T k i : ℝ) = T * i / 2 ^ (k + 1) := by
  simp [dyadic, mul_div_assoc]

@[powerlib_foundation] theorem dyadic_monotone (T : ℝ≥0) (k : ℕ) : Monotone (dyadic T k) := by
  intro i j hij
  rw [← NNReal.coe_le_coe, coe_dyadic, coe_dyadic]
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  gcongr

@[powerlib_foundation] theorem dyadic_zero (T : ℝ≥0) (k : ℕ) : dyadic T k 0 = 0 := by
  simp [dyadic]

@[powerlib_foundation] theorem dyadic_last (T : ℝ≥0) (k : ℕ) : dyadic T k (2 ^ (k + 1)) = T := by
  rw [← NNReal.coe_inj, coe_dyadic]
  push_cast
  field_simp

@[powerlib_foundation] theorem step_dyadic (T : ℝ≥0) (k i : ℕ) :
    step (dyadic T k) i = T / 2 ^ (k + 1) := by
  unfold step
  rw [coe_dyadic, coe_dyadic]
  push_cast
  ring

/-- The merge rule: `(a + b)²` if `ab > 0` (drop the midpoint), `a² + b²` otherwise. -/
def mergeSq (a b : ℝ) : ℝ := if 0 < a * b then (a + b) ^ 2 else a ^ 2 + b ^ 2

@[powerlib_foundation] theorem mergeSq_eq (a b : ℝ) :
    mergeSq a b = a ^ 2 + b ^ 2 + 2 * max (a * b) 0 := by
  unfold mergeSq
  split_ifs with h
  · rw [max_eq_left h.le]; ring
  · rw [max_eq_right (not_lt.mp h)]; ring

@[powerlib_foundation] theorem max_mul_zero (a b : ℝ) :
    max (a * b) 0 = max a 0 * max b 0 + max (-a) 0 * max (-b) 0 := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · rw [max_eq_left (mul_nonneg_of_nonpos_of_nonpos ha hb), max_eq_right ha, max_eq_right hb,
      max_eq_left (neg_nonneg.mpr ha), max_eq_left (neg_nonneg.mpr hb)]; ring
  · rw [max_eq_right (mul_nonpos_of_nonpos_of_nonneg ha hb), max_eq_right ha, max_eq_left hb,
      max_eq_left (neg_nonneg.mpr ha), max_eq_right (neg_nonpos.mpr hb)]; ring
  · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos ha hb), max_eq_left ha, max_eq_right hb,
      max_eq_right (neg_nonpos.mpr ha), max_eq_left (neg_nonneg.mpr hb)]; ring
  · rw [max_eq_left (mul_nonneg ha hb), max_eq_left ha, max_eq_left hb,
      max_eq_right (neg_nonpos.mpr ha), max_eq_right (neg_nonpos.mpr hb)]; ring

@[powerlib_foundation] theorem mergeSq_nonneg (a b : ℝ) : 0 ≤ mergeSq a b := by
  rw [mergeSq_eq]; positivity

@[powerlib_foundation] theorem mergeSq_le (a b : ℝ) : mergeSq a b ≤ 2 * (a ^ 2 + b ^ 2) := by
  unfold mergeSq
  split_ifs
  · nlinarith [sq_nonneg (a - b)]
  · nlinarith [sq_nonneg a, sq_nonneg b]

@[powerlib_foundation] theorem measurable_mergeSq :
    Measurable fun p : ℝ × ℝ => mergeSq p.1 p.2 := by
  unfold mergeSq
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_fst.mul measurable_snd))
    (by fun_prop) (by fun_prop)

/-- **Greedy path-dependent partition** of `[0, T]` at level `k`, written as a time sequence on the
indices `0, …, 2^(k+1)` of the dyadic grid: the odd grid point `t_{2j+1}` is replaced by `t_{2j}`
(i.e. deleted, since a repeated time contributes `0`) exactly when the two half-increments
`a_j = B(t_{2j+1}) − B(t_{2j})`, `b_j = B(t_{2j+2}) − B(t_{2j+1})` have the same strict sign. -/
def greedyPartition (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (k : ℕ) (ω : Ω) (i : ℕ) : ℝ≥0 :=
  if i % 2 = 1 ∧ 0 < incr B (dyadic T k) (i - 1) ω * incr B (dyadic T k) i ω then
    dyadic T k (i - 1) else dyadic T k i

theorem greedyPartition_le (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (k : ℕ) (ω : Ω) (i : ℕ) :
    greedyPartition B T k ω i ≤ dyadic T k i := by
  unfold greedyPartition
  split_ifs
  · exact dyadic_monotone T k (Nat.sub_le i 1)
  · exact le_rfl

theorem dyadic_pred_le_greedyPartition (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (k : ℕ) (ω : Ω) (i : ℕ) :
    dyadic T k (i - 1) ≤ greedyPartition B T k ω i := by
  unfold greedyPartition
  split_ifs
  · exact le_rfl
  · exact dyadic_monotone T k (Nat.sub_le i 1)

/-- The greedy partition is a genuine partition of `[0, T]` (monotone, from `0` to `T`) with mesh
at most `T / 2^k`. -/
@[powerlib_foundation] theorem greedyPartition_spec (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (k : ℕ) (ω : Ω) :
    Monotone (greedyPartition B T k ω) ∧ greedyPartition B T k ω 0 = 0 ∧
      greedyPartition B T k ω (2 ^ (k + 1)) = T ∧
      ∀ i, step (greedyPartition B T k ω) i ≤ T / 2 ^ k := by
  refine ⟨monotone_nat_of_le_succ fun i => ?_, ?_, ?_, fun i => ?_⟩
  · refine (greedyPartition_le B T k ω i).trans ?_
    have := dyadic_pred_le_greedyPartition B T k ω (i + 1)
    simpa using this
  · simp [greedyPartition, dyadic_zero]
  · have : 2 ^ (k + 1) % 2 = 0 := by
      rw [pow_succ]; exact Nat.mul_mod_left _ _
    simp [greedyPartition, this, dyadic_last]
  · unfold step
    have h1 : (greedyPartition B T k ω (i + 1) : ℝ) ≤ dyadic T k (i + 1) :=
      NNReal.coe_le_coe.mpr (greedyPartition_le B T k ω (i + 1))
    have h2 : (dyadic T k (i - 1) : ℝ) ≤ greedyPartition B T k ω i :=
      NNReal.coe_le_coe.mpr (dyadic_pred_le_greedyPartition B T k ω i)
    have h3 : (dyadic T k (i + 1) : ℝ) - dyadic T k (i - 1) ≤ T / 2 ^ k := by
      rw [coe_dyadic, coe_dyadic]
      have hi : ((i + 1 : ℕ) : ℝ) - ((i - 1 : ℕ) : ℝ) ≤ 2 := by
        rcases Nat.eq_zero_or_pos i with h | h
        · subst h; norm_num
        · rw [Nat.cast_sub h]; push_cast; linarith
      have hT : (0 : ℝ) ≤ T := T.coe_nonneg
      rw [pow_succ, ← sub_div, ← mul_sub, div_le_div_iff₀ (by positivity) (by positivity)]
      have hp : (0 : ℝ) ≤ 2 ^ k := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hi (mul_nonneg hT hp)]
    linarith

/-- Splitting a sum over `range (2n)` into consecutive pairs. -/
theorem sum_range_two_mul (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range (2 * n), f i = ∑ j ∈ range n, (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring

/-- The quadratic sum along the greedy partition is the sum of the merge rule over the pairs of
dyadic half-increments. -/
@[powerlib_foundation] theorem qvSum_greedyPartition (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (k : ℕ)
    (ω : Ω) :
    qvSum B (greedyPartition B T k ω) (2 ^ (k + 1)) ω =
      ∑ j ∈ range (2 ^ k), mergeSq (incr B (dyadic T k) (2 * j) ω)
        (incr B (dyadic T k) (2 * j + 1) ω) := by
  unfold qvSum
  rw [pow_succ, mul_comm, sum_range_two_mul]
  refine sum_congr rfl fun j _ => ?_
  have h0 : greedyPartition B T k ω (2 * j) = dyadic T k (2 * j) := by
    simp [greedyPartition, Nat.mul_mod_right]
  have h2 : greedyPartition B T k ω (2 * j + 1 + 1) = dyadic T k (2 * j + 2) := by
    have : (2 * j + 1 + 1) % 2 = 0 := by omega
    simp [greedyPartition, this]
  have hodd : (2 * j + 1) % 2 = 1 := by omega
  unfold incr mergeSq
  rw [h0, h2]
  by_cases hc : 0 < (B (dyadic T k (2 * j + 1)) ω - B (dyadic T k (2 * j)) ω) *
      (B (dyadic T k (2 * j + 1 + 1)) ω - B (dyadic T k (2 * j + 1)) ω)
  · have h1 : greedyPartition B T k ω (2 * j + 1) = dyadic T k (2 * j) := by
      simp only [greedyPartition, incr, hodd, Nat.add_sub_cancel, true_and]
      simp only [hc, ↓reduceIte]
    rw [h1]
    simp only [hc, ↓reduceIte]
    ring
  · have h1 : greedyPartition B T k ω (2 * j + 1) = dyadic T k (2 * j + 1) := by
      simp only [greedyPartition, incr, hodd, Nat.add_sub_cancel, true_and]
      simp only [hc, ↓reduceIte]
    rw [h1]
    simp only [hc, ↓reduceIte]

/-! ### Gaussian positive parts -/

/-- `m = E[Z⁺]` for a standard normal `Z` (`m = 1/√(2π)`, not needed here). -/
def posPartMean : ℝ := ∫ x, max x 0 ∂(gaussianReal 0 1)

theorem hasLaw_neg_gaussian (v : ℝ≥0) :
    HasLaw (fun x : ℝ => -x) (gaussianReal 0 v) (gaussianReal 0 v) where
  aemeasurable := by fun_prop
  map_eq := by rw [gaussianReal_map_neg, neg_zero]

theorem hasLaw_sqrt_mul_gaussian (v : ℝ≥0) :
    HasLaw (fun x : ℝ => √(v : ℝ) * x) (gaussianReal 0 v) (gaussianReal 0 1) where
  aemeasurable := by fun_prop
  map_eq := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr
    exact Real.sq_sqrt v.coe_nonneg

omit [IsProbabilityMeasure P] in
/-- `E[X⁺] = √v · m` for `X ∼ N(0, v)`. -/
theorem integral_posPart_of_hasLaw {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) : ∫ ω, max (X ω) 0 ∂P = √(v : ℝ) * posPartMean := by
  have h1 := hX.integral_comp (f := fun x : ℝ => max x 0) (by fun_prop)
  have h2 := (hasLaw_sqrt_mul_gaussian v).integral_comp (f := fun x : ℝ => max x 0) (by fun_prop)
  simp only [Function.comp_def] at h1 h2
  rw [h1, ← h2]
  have e : ∀ x : ℝ, max (√(v : ℝ) * x) 0 = √(v : ℝ) * max x 0 := fun x => by
    rw [mul_max_of_nonneg _ _ (Real.sqrt_nonneg _), mul_zero]
  simp_rw [e]
  rw [integral_const_mul]
  rfl

omit [IsProbabilityMeasure P] in
/-- `E[X⁻] = √v · m` for `X ∼ N(0, v)`. -/
theorem integral_negPart_of_hasLaw {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) : ∫ ω, max (-X ω) 0 ∂P = √(v : ℝ) * posPartMean :=
  integral_posPart_of_hasLaw ((hasLaw_neg_gaussian v).fun_comp hX)

/-- `m = E[Z⁺] > 0`. -/
theorem posPartMean_pos : 0 < posPartMean := by
  have hint : Integrable (fun x : ℝ => max x 0) (gaussianReal 0 1) := by
    have := integrable_pow_gaussianReal 0 1 1
    simpa using this.pos_part
  have hnn : 0 ≤ posPartMean := integral_nonneg fun x => le_max_right _ _
  refine lt_of_le_of_ne hnn fun h0 => ?_
  have hzero : (fun x : ℝ => max x 0) =ᵐ[gaussianReal 0 1] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => le_max_right _ _) hint).mp h0.symm
  -- the negative part also has mean `m = 0`
  have hneg : ∫ x, max (-x) 0 ∂(gaussianReal 0 1) = 0 := by
    have := integral_negPart_of_hasLaw (P := gaussianReal 0 1) (X := id) (v := 1) HasLaw.id
    simp only [id] at this
    rw [this, ← h0, mul_zero]
  have hintn : Integrable (fun x : ℝ => max (-x) 0) (gaussianReal 0 1) := by
    have := (integrable_pow_gaussianReal 0 1 1).neg
    simpa using this.pos_part
  have hzero' : (fun x : ℝ => max (-x) 0) =ᵐ[gaussianReal 0 1] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => le_max_right _ _) hintn).mp hneg
  have hx : (fun x : ℝ => x ^ 2) =ᵐ[gaussianReal 0 1] 0 := by
    filter_upwards [hzero, hzero'] with x h1 h2
    simp only [Pi.zero_apply] at h1 h2 ⊢
    have : x = max x 0 - max (-x) 0 := by
      rcases le_total x 0 with h | h
      · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
      · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
    rw [this, h1, h2]; ring
  have hsq := BM.integral_sq_gaussianReal_zero (1 : ℝ≥0)
  rw [integral_congr_ae hx] at hsq
  simp at hsq

/-! ### Mean and variance of the greedy quadratic sum -/

omit [IsProbabilityMeasure P] in
theorem incr_dyadic_hasLaw (hB : IsPreBrownianReal B P) (T : ℝ≥0) (k i : ℕ) :
    HasLaw (incr B (dyadic T k) i) (gaussianReal 0 (T / 2 ^ (k + 1))) P := by
  have h := incr_hasLaw hB (dyadic_monotone T k) i
  have e : dyadic T k (i + 1) - dyadic T k i = T / 2 ^ (k + 1) := by
    rw [← NNReal.coe_inj, coe_step (dyadic_monotone T k), step_dyadic]
    push_cast; ring
  rwa [e] at h

omit [IsProbabilityMeasure P] in
theorem incr_dyadic_indep (hB : IsPreBrownianReal B P) (T : ℝ≥0) (k : ℕ) :
    iIndepFun (fun i => incr B (dyadic T k) i) P :=
  hB.hasIndepIncrements.nat (dyadic_monotone T k)

omit [IsProbabilityMeasure P] in
/-- One merged block has mean `2v(1 + 2m²)`, `v = T / 2^(k+1)`. -/
theorem integral_mergeSq (hB : IsPreBrownianReal B P) (T : ℝ≥0) (k j : ℕ) :
    ∫ ω, mergeSq (incr B (dyadic T k) (2 * j) ω) (incr B (dyadic T k) (2 * j + 1) ω) ∂P =
      2 * ((T / 2 ^ (k + 1) : ℝ≥0) : ℝ) * (1 + 2 * posPartMean ^ 2) := by
  set a := incr B (dyadic T k) (2 * j) with hadef
  set b := incr B (dyadic T k) (2 * j + 1) with hbdef
  set v : ℝ≥0 := T / 2 ^ (k + 1) with hv
  have ha : HasLaw a (gaussianReal 0 v) P := incr_dyadic_hasLaw hB T k (2 * j)
  have hb : HasLaw b (gaussianReal 0 v) P := incr_dyadic_hasLaw hB T k (2 * j + 1)
  have hab : IndepFun a b P := (incr_dyadic_indep hB T k).indepFun (by omega)
  have hφ : Measurable fun x : ℝ => max x 0 := by fun_prop
  have hψ : Measurable fun x : ℝ => max (-x) 0 := by fun_prop
  have hia : Integrable a P := by simpa using integrable_pow_of_hasLaw ha 1
  have hib : Integrable b P := by simpa using integrable_pow_of_hasLaw hb 1
  have I1 : Integrable (fun ω => a ω ^ 2) P := integrable_pow_of_hasLaw ha 2
  have I2 : Integrable (fun ω => b ω ^ 2) P := integrable_pow_of_hasLaw hb 2
  have hab1 : IndepFun (fun ω => max (a ω) 0) (fun ω => max (b ω) 0) P := hab.comp hφ hφ
  have hab2 : IndepFun (fun ω => max (-a ω) 0) (fun ω => max (-b ω) 0) P := hab.comp hψ hψ
  have I3 : Integrable (fun ω => max (a ω) 0 * max (b ω) 0) P :=
    hab1.integrable_mul hia.pos_part hib.pos_part
  have I4 : Integrable (fun ω => max (-a ω) 0 * max (-b ω) 0) P :=
    hab2.integrable_mul hia.neg.pos_part hib.neg.pos_part
  have e3 : ∫ ω, max (a ω) 0 * max (b ω) 0 ∂P = v * posPartMean ^ 2 := by
    rw [hab1.integral_fun_mul_eq_mul_integral
      (hφ.comp_aemeasurable ha.aemeasurable).aestronglyMeasurable
      (hφ.comp_aemeasurable hb.aemeasurable).aestronglyMeasurable,
      integral_posPart_of_hasLaw ha, integral_posPart_of_hasLaw hb]
    have := Real.mul_self_sqrt v.coe_nonneg
    nlinarith [this]
  have e4 : ∫ ω, max (-a ω) 0 * max (-b ω) 0 ∂P = v * posPartMean ^ 2 := by
    rw [hab2.integral_fun_mul_eq_mul_integral
      (hψ.comp_aemeasurable ha.aemeasurable).aestronglyMeasurable
      (hψ.comp_aemeasurable hb.aemeasurable).aestronglyMeasurable,
      integral_negPart_of_hasLaw ha, integral_negPart_of_hasLaw hb]
    have := Real.mul_self_sqrt v.coe_nonneg
    nlinarith [this]
  have hpt : (fun ω => mergeSq (a ω) (b ω)) = fun ω => (a ω ^ 2 + b ω ^ 2) +
      2 * (max (a ω) 0 * max (b ω) 0 + max (-a ω) 0 * max (-b ω) 0) := by
    funext ω; rw [mergeSq_eq, max_mul_zero]
  have I12 : Integrable (fun ω => a ω ^ 2 + b ω ^ 2) P := I1.add I2
  have I34 : Integrable (fun ω => max (a ω) 0 * max (b ω) 0 + max (-a ω) 0 * max (-b ω) 0) P :=
    I3.add I4
  rw [hpt, integral_add I12 (I34.const_mul 2), integral_add I1 I2,
    integral_const_mul, integral_add I3 I4, e3, e4, integral_sq_of_hasLaw ha,
    integral_sq_of_hasLaw hb]
  ring

omit [IsProbabilityMeasure P] in
/-- Each merged block is in `L²`. -/
theorem memLp_mergeSq (hB : IsPreBrownianReal B P) (T : ℝ≥0) (k j : ℕ) :
    MemLp (fun ω => mergeSq (incr B (dyadic T k) (2 * j) ω)
      (incr B (dyadic T k) (2 * j + 1) ω)) 2 P := by
  have ha := incr_dyadic_hasLaw hB T k (2 * j)
  have hb := incr_dyadic_hasLaw hB T k (2 * j + 1)
  refine MemLp.of_le (((memLp_sq_of_hasLaw ha).add (memLp_sq_of_hasLaw hb)).const_mul 2)
    (measurable_mergeSq.comp_aemeasurable
      (ha.aemeasurable.prodMk hb.aemeasurable)).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (mergeSq_nonneg _ _), abs_of_nonneg (by positivity)]
  exact mergeSq_le _ _

/-- `Var(block) ≤ 48 v²`. -/
theorem variance_mergeSq_le (hB : IsPreBrownianReal B P) (T : ℝ≥0) (k j : ℕ) :
    variance (fun ω => mergeSq (incr B (dyadic T k) (2 * j) ω)
      (incr B (dyadic T k) (2 * j + 1) ω)) P ≤ 48 * ((T / 2 ^ (k + 1) : ℝ≥0) : ℝ) ^ 2 := by
  set a := incr B (dyadic T k) (2 * j)
  set b := incr B (dyadic T k) (2 * j + 1)
  set v : ℝ≥0 := T / 2 ^ (k + 1)
  have ha : HasLaw a (gaussianReal 0 v) P := incr_dyadic_hasLaw hB T k (2 * j)
  have hb : HasLaw b (gaussianReal 0 v) P := incr_dyadic_hasLaw hB T k (2 * j + 1)
  refine (variance_le_expectation_sq (measurable_mergeSq.comp_aemeasurable
    (ha.aemeasurable.prodMk hb.aemeasurable)).aestronglyMeasurable).trans ?_
  have hint : Integrable (fun ω => 8 * (a ω ^ 4 + b ω ^ 4)) P :=
    ((integrable_pow_of_hasLaw ha 4).add (integrable_pow_of_hasLaw hb 4)).const_mul 8
  calc ∫ ω, ((fun ω => mergeSq (a ω) (b ω)) ^ 2) ω ∂P ≤ ∫ ω, 8 * (a ω ^ 4 + b ω ^ 4) ∂P := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ω => by
            simp only [Pi.pow_apply, Pi.zero_apply]; positivity) hint
          (Eventually.of_forall fun ω => ?_)
        simp only [Pi.pow_apply]
        have h0 := mergeSq_nonneg (a ω) (b ω)
        have h1 := mergeSq_le (a ω) (b ω)
        have h2 : mergeSq (a ω) (b ω) ^ 2 ≤ (2 * (a ω ^ 2 + b ω ^ 2)) ^ 2 :=
          pow_le_pow_left₀ h0 h1 2
        nlinarith [sq_nonneg (a ω ^ 2 - b ω ^ 2)]
    _ = 48 * (v : ℝ) ^ 2 := by
        rw [integral_const_mul, integral_add (integrable_pow_of_hasLaw ha 4)
          (integrable_pow_of_hasLaw hb 4), integral_pow_four_of_hasLaw ha,
          integral_pow_four_of_hasLaw hb]
        ring

/-- The greedy quadratic sum as a function of `ω`. -/
theorem greedyQV_eq_sum (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (k : ℕ) :
    (fun ω => qvSum B (greedyPartition B T k ω) (2 ^ (k + 1)) ω) =
      ∑ j ∈ range (2 ^ k), fun ω => mergeSq (incr B (dyadic T k) (2 * j) ω)
        (incr B (dyadic T k) (2 * j + 1) ω) := by
  funext ω
  rw [qvSum_greedyPartition, Finset.sum_apply]

/-- **Mean of the greedy quadratic sum**: `E = T (1 + 2m²)` for every level `k`. -/
@[powerlib_foundation] theorem greedyQV_mean (hB : IsPreBrownianReal B P) (T : ℝ≥0) (k : ℕ) :
    ∫ ω, qvSum B (greedyPartition B T k ω) (2 ^ (k + 1)) ω ∂P =
      T * (1 + 2 * posPartMean ^ 2) := by
  simp_rw [qvSum_greedyPartition]
  rw [integral_finsetSum _ fun j _ => (memLp_mergeSq hB T k j).integrable one_le_two]
  simp_rw [integral_mergeSq hB T k]
  rw [sum_const, card_range, nsmul_eq_mul]
  push_cast
  rw [pow_succ]
  field_simp

/-- **Variance of the greedy quadratic sum**: `Var ≤ 12 T² / 2^k` (independent blocks). -/
@[powerlib_foundation] theorem greedyQV_variance_le (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    (k : ℕ) :
    variance (fun ω => qvSum B (greedyPartition B T k ω) (2 ^ (k + 1)) ω) P ≤
      12 * (T : ℝ) ^ 2 / 2 ^ k := by
  have hind := incr_dyadic_indep hB T k
  have haem : ∀ i, AEMeasurable (incr B (dyadic T k) i) P :=
    fun i => (incr_dyadic_hasLaw hB T k i).aemeasurable
  rw [greedyQV_eq_sum, IndepFun.variance_sum (fun j _ => memLp_mergeSq hB T k j)]
  · calc ∑ j ∈ range (2 ^ k), variance (fun ω => mergeSq (incr B (dyadic T k) (2 * j) ω)
          (incr B (dyadic T k) (2 * j + 1) ω)) P
        ≤ ∑ _j ∈ range (2 ^ k), 48 * ((T / 2 ^ (k + 1) : ℝ≥0) : ℝ) ^ 2 :=
          sum_le_sum fun j _ => variance_mergeSq_le hB T k j
      _ = 12 * (T : ℝ) ^ 2 / 2 ^ k := by
          rw [sum_const, card_range, nsmul_eq_mul]
          push_cast
          rw [pow_succ]
          field_simp
          ring
  · intro j _ l _ hjl
    have h := hind.indepFun_prodMk_prodMk₀ haem (2 * j) (2 * j + 1) (2 * l) (2 * l + 1)
      (by omega) (by omega) (by omega) (by omega)
    exact h.comp measurable_mergeSq measurable_mergeSq

/-- **Convergence in probability to `T (1 + 2m²)`**, not to `T`. -/
@[powerlib_foundation] theorem greedyQV_tendstoInMeasure (hB : IsPreBrownianReal B P)
    (T : ℝ≥0) :
    TendstoInMeasure P (fun k ω => qvSum B (greedyPartition B T k ω) (2 ^ (k + 1)) ω) atTop
      (fun _ => (T : ℝ) * (1 + 2 * posPartMean ^ 2)) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hle : ∀ k, P {ω | ε ≤ dist (qvSum B (greedyPartition B T k ω) (2 ^ (k + 1)) ω)
      ((T : ℝ) * (1 + 2 * posPartMean ^ 2))} ≤
        ENNReal.ofReal (12 * (T : ℝ) ^ 2 / 2 ^ k / ε ^ 2) := by
    intro k
    have hm : MemLp (fun ω => qvSum B (greedyPartition B T k ω) (2 ^ (k + 1)) ω) 2 P := by
      rw [greedyQV_eq_sum]
      exact memLp_finsetSum' _ fun j _ => memLp_mergeSq hB T k j
    have := meas_ge_le_variance_div_sq hm hε
    rw [greedyQV_mean hB T k] at this
    refine (le_of_eq ?_).trans (this.trans (ENNReal.ofReal_le_ofReal ?_))
    · simp only [Real.dist_eq]
    · exact div_le_div_of_nonneg_right (greedyQV_variance_le hB T k) (sq_nonneg ε)
  have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal (12 * (T : ℝ) ^ 2 / 2 ^ k / ε ^ 2)) atTop
      (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    apply ENNReal.tendsto_ofReal
    have h2 : Tendsto (fun k : ℕ => ((1 : ℝ) / 2) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have := (h2.const_mul (12 * (T : ℝ) ^ 2)).div_const (ε ^ 2)
    simp only [mul_zero, zero_div] at this
    refine this.congr fun k => ?_
    rw [div_pow, one_pow]; field_simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hle

/-- **No almost-sure quadratic variation along path-dependent partitions.**  For a pre-Brownian
motion `B` and `T > 0`, the greedy partitions `greedyPartition B T k ω` are partitions of `[0, T]`
with mesh `≤ T / 2^k → 0`, chosen from the path, yet for `P`-almost every `ω` the quadratic sums
`∑ (ΔB)²` along them do **not** converge to `T` (they converge in probability to
`T (1 + 2m²) > T`, `m = E[Z⁺] > 0`). -/
@[powerlib_foundation] theorem qv_pathDependent_not_ae (hB : IsPreBrownianReal B P) {T : ℝ≥0}
    (hT : 0 < T) :
    (∀ k ω, Monotone (greedyPartition B T k ω) ∧ greedyPartition B T k ω 0 = 0 ∧
      greedyPartition B T k ω (2 ^ (k + 1)) = T ∧
      ∀ i, step (greedyPartition B T k ω) i ≤ T / 2 ^ k) ∧
    ∀ᵐ ω ∂P, ¬ Tendsto (fun k => qvSum B (greedyPartition B T k ω) (2 ^ (k + 1)) ω) atTop
      (𝓝 (T : ℝ)) := by
  refine ⟨fun k ω => greedyPartition_spec B T k ω, ?_⟩
  obtain ⟨ns, hns, hae⟩ := (greedyQV_tendstoInMeasure hB T).exists_seq_tendsto_ae
  filter_upwards [hae] with ω hω hlim
  have h1 := hlim.comp hns.tendsto_atTop
  have heq := tendsto_nhds_unique h1 hω
  have hm := posPartMean_pos
  have hT' : (0 : ℝ) < T := hT
  nlinarith [sq_pos_of_pos hm]

end powerlib.Stochastic.QV
