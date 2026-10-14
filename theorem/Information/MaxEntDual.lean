import dependencies.Mathlib
import theorem.Attributes
import theorem.Information.MaxEnt
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.Covariance

/-! # Multi-constraint MaxEnt dual: gradient and Hessian

The gradient of the multi-constraint MaxEnt dual is the moment mismatch and its Hessian is the
covariance matrix of the constraint functions, so the dual is convex.

Scope.
* Probability theory, not an engineering result.
* Along a line `s ↦ λ + s u` the dual equals a constant plus the one-constraint dual of the
  direction statistic `g_u = ∑ u_k f_k` under the Gibbs measure `p_λ = gibbs m f λ`
  (`dualVec_line`), because `exp(−∑ (λ + s u)_k f_k) = exp(−∑ λ_k f_k) · exp(−s g_u)`; the
  one-dimensional results `deriv_dual` / `iteratedDeriv_two_dual` (Mathlib
  `integral_tilted_mul_self`, `variance_tilted_mul`) then apply.
* Hypotheses: `Z(λ) < ∞` and `Z(λ + s u) < ∞` for `s` near `0` (interior of the natural
  parameter domain along `u`). Directional (Gateaux) derivatives are used instead of a Fréchet
  gradient on `ι → ℝ`; for the smooth function at hand they carry the same information.

Source: work-sync theory/T-maximum-entropy.md §1.1 (dual `D(λ) = log Z(λ) + λ · F`,
`Z(λ) = ∫ exp(−∑ λ_k f_k) dm`; `∂_k D = F_k − E_{p_λ}[f_k]`;
`∂_k ∂_l D = Cov_{p_λ}(f_k, f_l) ⪰ 0`, so the dual is convex).

Results.
* `deriv_dualVec_line` — the directional derivative `⟨∇D(λ), u⟩ = u · F − E_{p_λ}[g_u]`, and
  `deriv_dualVec_line_eq_sum`: `= ∑ u_k (F_k − E_{p_λ}[f_k])` (gradient formula).
* `iteratedDeriv_two_dualVec_line` — the second directional derivative
  `uᵀ ∇²D(λ) u = Var_{p_λ}[g_u]`, `iteratedDeriv_two_dualVec_line_eq_sum`:
  `= ∑_{k,l} u_k u_l Cov(f_k, f_l)` (Hessian = covariance matrix), and
  `iteratedDeriv_two_dualVec_line_nonneg` (convexity).
-/

noncomputable section
namespace powerlib.Information

open MeasureTheory Real ProbabilityTheory Filter
open scoped Topology

variable {α : Type*} {mα : MeasurableSpace α} {ι : Type*} [Fintype ι]

/-- Multi-constraint MaxEnt dual `D(λ) = log ∫ exp(−∑ λ_k f_k) dm + ∑ λ_k F_k`. -/
def dualVec (m : Measure α) (f : ι → α → ℝ) (F lam : ι → ℝ) : ℝ :=
  log (∫ x, exp (-∑ i, lam i * f i x) ∂m) + ∑ i, lam i * F i

/-- Direction statistic `g_u = ∑ u_k f_k`. -/
def dirFun (f : ι → α → ℝ) (u : ι → ℝ) (x : α) : ℝ := ∑ i, u i * f i x

@[powerlib_foundation] theorem tilt_line (f : ι → α → ℝ) (lam u : ι → ℝ) (s : ℝ) (x : α) :
    -∑ i, lam i * f i x + -s * dirFun f u x = -∑ i, (lam + s • u) i * f i x := by
  simp only [dirFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc, neg_mul, Finset.sum_neg_distrib]
  ring

variable {m : Measure α} [NeZero m] {f : ι → α → ℝ} {lam u F : ι → ℝ}

omit [NeZero m] in
/-- Moment generating function of the direction statistic under the Gibbs measure. -/
@[powerlib_foundation] theorem mgf_dirFun_gibbs (s : ℝ) :
    mgf (dirFun f u) (gibbs m f lam) (-s) =
      (∫ x, exp (-∑ i, (lam + s • u) i * f i x) ∂m) / ∫ x, exp (-∑ i, lam i * f i x) ∂m := by
  rw [mgf, gibbs, integral_tilted]
  simp_rw [smul_eq_mul, div_mul_eq_mul_div, ← exp_add, tilt_line]
  rw [integral_div]

/-- Along the line `λ + s u`, the dual is a constant plus the one-constraint dual of `g_u` under
`p_λ` (wherever `Z(λ + s u) < ∞`). -/
@[powerlib_foundation] theorem dualVec_line
    (hZ : Integrable (fun x => exp (-∑ i, lam i * f i x)) m) {s : ℝ}
    (hs : Integrable (fun x => exp (-∑ i, (lam + s • u) i * f i x)) m) :
    dualVec m f F (lam + s • u) =
      dualVec m f F lam + dual (gibbs m f lam) (dirFun f u) (∑ i, u i * F i) s := by
  have hZpos := integral_exp_pos hZ
  have hIpos := integral_exp_pos hs
  have e : ∑ i, (lam + s • u) i * F i = ∑ i, lam i * F i + s * ∑ i, u i * F i := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
  rw [dual, cgf, mgf_dirFun_gibbs, log_div hIpos.ne' hZpos.ne', dualVec, dualVec, e]
  ring

omit [NeZero m] in
/-- `0` is an interior point of the exponential-integrability set of `g_u` under `p_λ`. -/
@[powerlib_foundation] theorem zero_mem_interior_dirFun
    (hZ : Integrable (fun x => exp (-∑ i, lam i * f i x)) m)
    (hU : ∀ᶠ s in 𝓝 (0 : ℝ), Integrable (fun x => exp (-∑ i, (lam + s • u) i * f i x)) m) :
    (0 : ℝ) ∈ interior (integrableExpSet (dirFun f u) (gibbs m f lam)) := by
  rw [mem_interior_iff_mem_nhds]
  have h2 : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.tendsto (0 : ℝ))
  filter_upwards [h2.eventually hU] with t ht
  change Integrable (fun x => exp (t * dirFun f u x)) (gibbs m f lam)
  rw [gibbs, integrable_tilted_iff hZ]
  refine ht.congr (ae_of_all _ fun x => ?_)
  simp only [smul_eq_mul]
  rw [← exp_add, ← tilt_line f lam u (-t) x, neg_neg]

@[powerlib_foundation] theorem gibbs_tilted_zero
    (hZ : Integrable (fun x => exp (-∑ i, lam i * f i x)) m) :
    (gibbs m f lam).tilted (fun x => (-0 : ℝ) * dirFun f u x) = gibbs m f lam := by
  have : IsProbabilityMeasure (gibbs m f lam) := isProbabilityMeasure_tilted hZ
  simp only [neg_zero, zero_mul]
  exact tilted_const _ 0

@[powerlib_foundation] theorem dualVec_line_eventuallyEq
    (hZ : Integrable (fun x => exp (-∑ i, lam i * f i x)) m)
    (hU : ∀ᶠ s in 𝓝 (0 : ℝ), Integrable (fun x => exp (-∑ i, (lam + s • u) i * f i x)) m) :
    (fun s : ℝ => dualVec m f F (lam + s • u)) =ᶠ[𝓝 0]
      fun s => dualVec m f F lam + dual (gibbs m f lam) (dirFun f u) (∑ i, u i * F i) s := by
  filter_upwards [hU] with s hs using dualVec_line hZ hs

/-- **Directional derivative of the dual**: `⟨∇D(λ), u⟩ = u · F − E_{p_λ}[∑ u_k f_k]`. -/
@[powerlib_foundation] theorem deriv_dualVec_line
    (hZ : Integrable (fun x => exp (-∑ i, lam i * f i x)) m)
    (hU : ∀ᶠ s in 𝓝 (0 : ℝ), Integrable (fun x => exp (-∑ i, (lam + s • u) i * f i x)) m) :
    deriv (fun s : ℝ => dualVec m f F (lam + s • u)) 0 =
      ∑ i, u i * F i - ∫ x, dirFun f u x ∂(gibbs m f lam) := by
  rw [(dualVec_line_eventuallyEq (F := F) hZ hU).deriv_eq, deriv_const_add,
    deriv_dual (by rw [neg_zero]; exact zero_mem_interior_dirFun hZ hU), gibbs_tilted_zero hZ]

/-- **Gradient formula** `∂_k D(λ) = F_k − E_{p_λ}[f_k]`, in directional form. -/
@[powerlib_foundation] theorem deriv_dualVec_line_eq_sum
    (hZ : Integrable (fun x => exp (-∑ i, lam i * f i x)) m)
    (hU : ∀ᶠ s in 𝓝 (0 : ℝ), Integrable (fun x => exp (-∑ i, (lam + s • u) i * f i x)) m)
    (hf : ∀ i, Integrable (f i) (gibbs m f lam)) :
    deriv (fun s : ℝ => dualVec m f F (lam + s • u)) 0 =
      ∑ i, u i * (F i - ∫ x, f i x ∂(gibbs m f lam)) := by
  rw [deriv_dualVec_line hZ hU]
  unfold dirFun
  rw [integral_finsetSum _ fun i _ => (hf i).const_mul (u i)]
  simp only [integral_const_mul, mul_sub, Finset.sum_sub_distrib]

/-- **Second directional derivative of the dual**: `uᵀ ∇²D(λ) u = Var_{p_λ}[∑ u_k f_k]`. -/
@[powerlib_foundation] theorem iteratedDeriv_two_dualVec_line
    (hZ : Integrable (fun x => exp (-∑ i, lam i * f i x)) m)
    (hU : ∀ᶠ s in 𝓝 (0 : ℝ), Integrable (fun x => exp (-∑ i, (lam + s • u) i * f i x)) m) :
    iteratedDeriv 2 (fun s : ℝ => dualVec m f F (lam + s • u)) 0 =
      Var[dirFun f u; gibbs m f lam] := by
  rw [((dualVec_line_eventuallyEq (F := F) hZ hU).iteratedDeriv 2).eq_of_nhds,
    iteratedDeriv_const_add (by norm_num),
    iteratedDeriv_two_dual (by rw [neg_zero]; exact zero_mem_interior_dirFun hZ hU),
    gibbs_tilted_zero hZ]

/-- **Convexity of the dual** along every direction. -/
@[powerlib_foundation] theorem iteratedDeriv_two_dualVec_line_nonneg
    (hZ : Integrable (fun x => exp (-∑ i, lam i * f i x)) m)
    (hU : ∀ᶠ s in 𝓝 (0 : ℝ), Integrable (fun x => exp (-∑ i, (lam + s • u) i * f i x)) m) :
    0 ≤ iteratedDeriv 2 (fun s : ℝ => dualVec m f F (lam + s • u)) 0 := by
  rw [iteratedDeriv_two_dualVec_line hZ hU]
  exact variance_nonneg _ _

/-- **Hessian = covariance matrix**: `uᵀ ∇²D(λ) u = ∑_{k,l} u_k u_l Cov_{p_λ}(f_k, f_l)`. -/
@[powerlib_foundation] theorem iteratedDeriv_two_dualVec_line_eq_sum
    (hZ : Integrable (fun x => exp (-∑ i, lam i * f i x)) m)
    (hU : ∀ᶠ s in 𝓝 (0 : ℝ), Integrable (fun x => exp (-∑ i, (lam + s • u) i * f i x)) m)
    (hf : ∀ i, MemLp (f i) 2 (gibbs m f lam)) :
    iteratedDeriv 2 (fun s : ℝ => dualVec m f F (lam + s • u)) 0 =
      ∑ i, ∑ j, u i * u j * cov[f i, f j; gibbs m f lam] := by
  have : IsProbabilityMeasure (gibbs m f lam) := isProbabilityMeasure_tilted hZ
  rw [iteratedDeriv_two_dualVec_line hZ hU]
  have e : dirFun f u = ∑ i ∈ Finset.univ, fun x => u i * f i x := by
    funext x; simp [dirFun, Finset.sum_apply]
  rw [e, variance_sum' fun i _ => (hf i).const_mul (u i)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right]
  ring

end powerlib.Information
