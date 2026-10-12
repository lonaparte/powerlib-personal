import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.Brownian
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.Variance

/-! # Quadratic variation of Brownian motion in `L²`

Source: work-sync `theory/T-sde-systems.md` §1.2 (quadratic variation `[W]_t = t`:
`∑ (W_{t_{i+1}} − W_{t_i})² → t` as the mesh of the partition of `[0, t]` tends to `0`).

Scope (Rules §3).  `W` is Mathlib's `IsPreBrownianReal` (finite-dimensional laws of Brownian
motion; path continuity is not used).  Everything is proved from independence of increments
and the Gaussian moments `E X² = v`, `E X⁴ = 3v²` (the fourth moment is obtained from the
moment generating function `exp(v s²/2)`).  Foundation result about Brownian motion, not an
engineering stability conclusion.

Main results.
* `integral_pow_four_gaussianReal_zero`: `∫ x⁴ dN(0, v) = 3 v²`;
  `variance_sq_of_hasLaw_gaussian`: `Var(X²) = 2v²` for `X ~ N(0, v)`.
* `qvSum_mean`: `E ∑ (ΔW_i)² = t_n − t_0`.
* `qvSum_L2_identity`: `E[(∑ (ΔW_i)² − (t_n − t_0))²] = 2 ∑ (Δt_i)²` for every monotone
  partition (independent increments + Gaussian fourth moment).
* `qvSum_L2_le`: if every step is `≤ δ`, the `L²` error is `≤ 2 δ (t_n − t_0)`.
* `qv_tendsto_L2`: for partitions of `[0, T]` with mesh `δ_k → 0` the `L²` error tends to `0`;
  `qv_tendsto_inProbability`: hence convergence in probability (Chebyshev).

Correction (T-sde-systems §1.2).  The quadratic-variation limit holds in `L²` (hence in
probability) for **arbitrary** partitions with vanishing mesh, which is what is proved here.
"`∑ (ΔW)² → t` almost surely along any refining sequence" is not true in that generality
(a.s. convergence needs e.g. `∑_k mesh_k < ∞` or nested dyadic partitions); this module makes
no almost-sure claim.
-/

noncomputable section
namespace powerlib.Stochastic.QV

open MeasureTheory ProbabilityTheory Real Filter Finset
open scoped NNReal ENNReal Topology

/-! ## Gaussian fourth moment -/

/-- Every exponential moment of `N(μ, v)` is finite, so `0` lies in the interior of the
exponential-integrability set. -/
@[powerlib_foundation] theorem zero_mem_interior_integrableExpSet_gaussianReal (m : ℝ)
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
  have hit : iteratedDeriv 4 E = fun s => (12 * a ^ 2 + 48 * a ^ 3 * s ^ 2 + 16 * a ^ 4 * s ^ 4) * E s := by
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
    (h0 : ∀ k, par k 0 = 0) (hT : ∀ k, par k (N k) = T) (hmesh : ∀ k, ∀ i < N k, step (par k) i ≤ δ k)
    (hδ : Tendsto δ atTop (𝓝 0)) :
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
    (h0 : ∀ k, par k 0 = 0) (hT : ∀ k, par k (N k) = T) (hmesh : ∀ k, ∀ i < N k, step (par k) i ≤ δ k)
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
  have hlim : Tendsto (fun k => ENNReal.ofReal ((∫ ω, (qvSum B (par k) (N k) ω - T) ^ 2 ∂P) / ε ^ 2))
      atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    apply ENNReal.tendsto_ofReal
    simpa using hL2.div_const (ε ^ 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hle

end powerlib.Stochastic.QV
