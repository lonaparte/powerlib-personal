import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # Rare-event Monte Carlo: importance sampling and subset simulation

The importance-sampling identity (and its absolute-continuity premise), unbiasedness and the
strong law for plain Monte Carlo, the zero-variance proposal, and the subset-simulation product.

Scope.
* Probability theory, not an engineering result.

Source: work-sync theory/T-importance-sampling.md (head: `P_F = E_q[1_F(X) π(X)/q(X)]`, weight
`w = π/q` gives an unbiased estimator, the zero-variance proposal is proportional to `1_F π`),
theory/T-subset-simulation.md (head: `P(F_m) = P(F_1) Π_{k=2}^m P(F_k | F_{k−1})` for nested
events).

Results.
* `importance_sampling_identity` — wrapper of Mathlib `Measure.setLIntegral_rnDeriv`:
  `π(F) = ∫_F (dπ/dq) dq` **provided `π ≪ q`**; `importance_sampling_needs_ac`: without absolute
  continuity the identity fails (`π = δ₀`, `q = δ₁`, `F = {0}`).
* `mc_mean_unbiased`, `mc_strong_law` — wrapper of Mathlib `ProbabilityTheory.strong_law_ae`:
  the plain Monte Carlo average is unbiased and converges almost surely for pairwise
  independent, identically distributed, integrable samples.
* `zero_variance_proposal` — with densities, the proposal `q* = 1_F p / P_F` makes the weighted
  indicator equal to `P_F` wherever `q* > 0`, so the estimator has zero variance.
* `subset_simulation_product` — `μ(F_m) = μ(F_0) Π_{k<m} μ(F_{k+1} | F_k)` for a decreasing
  chain of measurable events (induction on `ProbabilityTheory.cond_mul_eq_inter`).

Corrections.
* Importance sampling, frontmatter: the weight is `dπ/dq` (target over proposal); the
  frontmatter's `dQ/dP` (proposal over target) is its reciprocal. The identity needs `π ≪ q`
  (every set the target charges must be reachable by the proposal), which the note omits.
* Subset simulation: the note indexes the chain both as `F = F_0 ⊃ F_1 ⊃ ⋯ ⊃ F_m`
  (assumptions) and as `F_1 ⊃ ⋯ ⊃ F_m` with target `F_m` (formula). Here one indexing is fixed:
  `F 0 ⊇ F 1 ⊇ ⋯`, target `F m`.
-/

noncomputable section
namespace powerlib.Estimation

open MeasureTheory ProbabilityTheory Filter Finset Function
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α]

/-! ## Importance sampling -/

/-- **Importance-sampling identity**: if `π ≪ q` then `π(F) = E_q[1_F · dπ/dq]`
(Mathlib `MeasureTheory.Measure.setLIntegral_rnDeriv`). -/
@[tmio T, powerlib_foundation] theorem importance_sampling_identity {π q : Measure α}
    [π.HaveLebesgueDecomposition q] [SFinite q] (hac : π ≪ q) (F : Set α) :
    ∫⁻ x in F, π.rnDeriv q x ∂q = π F :=
  Measure.setLIntegral_rnDeriv hac F

/-- Real-valued form for a finite target: `P_F = ∫ 1_F (dπ/dq) dq`. -/
@[powerlib_foundation] theorem importance_sampling_identity_real {π q : Measure α}
    [IsFiniteMeasure π] [SigmaFinite q] (hac : π ≪ q) {F : Set α} (hF : MeasurableSet F) :
    ∫ x, F.indicator (fun x => (π.rnDeriv q x).toReal) x ∂q = π.real F := by
  rw [integral_indicator hF, Measure.setIntegral_toReal_rnDeriv hac]

/-- **Absolute continuity cannot be dropped**: for `π = δ₀`, `q = δ₁`, `F = {0}` the importance
identity fails (`π F = 1`, while any `q`-integral over `F` vanishes). -/
@[powerlib_foundation] theorem importance_sampling_needs_ac :
    ∃ (π q : Measure ℝ) (F : Set ℝ), MeasurableSet F ∧ ¬ π ≪ q ∧
      ∀ w : ℝ → ℝ≥0∞, ∫⁻ x in F, w x ∂q ≠ π F := by
  refine ⟨Measure.dirac 0, Measure.dirac 1, {0}, measurableSet_singleton 0, ?_, fun w => ?_⟩
  · intro h
    have := h (s := {0}) (by simp)
    simp at this
  · have hq : (Measure.dirac (1 : ℝ)).restrict {0} = 0 := by
      rw [Measure.restrict_eq_zero]; simp
    rw [hq, lintegral_zero_measure]
    simp

/-! ## Plain Monte Carlo -/

/-- **Unbiasedness of the Monte Carlo mean** for identically distributed samples. -/
@[powerlib_foundation] theorem mc_mean_unbiased {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} (hint : Integrable (X 0) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, (n : ℝ)⁻¹ * ∑ i ∈ range n, X i ω ∂μ = ∫ ω, X 0 ω ∂μ := by
  have hi : ∀ i, Integrable (X i) μ := fun i => (hident i).integrable_iff.mpr hint
  rw [integral_const_mul, integral_finsetSum _ fun i _ => hi i]
  simp_rw [fun i => (hident i).integral_eq]
  simp [hn]

/-- **Strong law for the Monte Carlo estimator** (Mathlib `ProbabilityTheory.strong_law_ae`). -/
@[powerlib_foundation] theorem mc_strong_law {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hint : Integrable (X 0) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X)) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, X i ω) atTop
      (𝓝 (∫ ω, X 0 ω ∂μ)) := by
  simpa [smul_eq_mul] using strong_law_ae X hint hindep hident

/-! ## Zero-variance proposal -/

/-- **Zero-variance proposal**: for a target density `p ≥ 0` and `P_F = ∫_F p > 0`, the proposal
density `q* = 1_F p / P_F` makes the importance weight `1_F p / q*` equal to `P_F` wherever
`q* > 0`; hence `∫ q* (1_F p/q* − P_F)² = 0` (zero variance). -/
@[powerlib_foundation] theorem zero_variance_proposal {ν : Measure α} {p : α → ℝ} {F : Set α}
    {PF : ℝ} (hPF : PF ≠ 0) :
    (∀ x, F.indicator p x / PF ≠ 0 → F.indicator p x / (F.indicator p x / PF) = PF) ∧
      ∫ x, F.indicator p x / PF * (F.indicator p x / (F.indicator p x / PF) - PF) ^ 2 ∂ν = 0 := by
  have hpt : ∀ x, F.indicator p x / PF ≠ 0 →
      F.indicator p x / (F.indicator p x / PF) = PF := by
    intro x hx
    have hne : F.indicator p x ≠ 0 := by
      intro h; apply hx; rw [h, zero_div]
    field_simp
  refine ⟨hpt, ?_⟩
  have : (fun x => F.indicator p x / PF * (F.indicator p x / (F.indicator p x / PF) - PF) ^ 2) =
      fun _ => (0 : ℝ) := by
    funext x
    by_cases hx : F.indicator p x / PF = 0
    · rw [hx, zero_mul]
    · rw [hpt x hx, sub_self]; ring
  rw [this, integral_zero]

/-! ## Subset simulation -/

/-- **Subset simulation product formula**: for a decreasing chain of measurable events
`F 0 ⊇ F 1 ⊇ ⋯`, `μ(F m) = μ(F 0) Π_{k<m} μ(F (k+1) | F k)`. -/
@[powerlib_foundation] theorem subset_simulation_product {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {F : ℕ → Set Ω} (hF : ∀ k, MeasurableSet (F k))
    (hmono : ∀ k, F (k + 1) ⊆ F k) (m : ℕ) :
    μ (F m) = μ (F 0) * ∏ k ∈ range m, μ[F (k + 1) | F k] := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, ← mul_assoc, ← ih, mul_comm, cond_mul_eq_inter (hF m),
      Set.inter_eq_right.mpr (hmono m)]

end powerlib.Estimation
