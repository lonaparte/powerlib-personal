import Mathlib.Analysis.Complex.Exponential
import theorem.Dynamics.CenterManifoldDefs
import theorem.Dynamics.Degenerate.WeakFocus

/-! # Polynomial candidate graphs read in a chart (foundation)

The tools for checking a polynomial approximate centre manifold `φ = H ∘ π` of a field with
trigonometric nonlinearities: the invariance defect and its order read in the chart `ι`, `π` of
the centre subspace, the partial derivatives of a planar polynomial, and the sixth-order Taylor
remainders of `cos` and `sin` at `0`.

Scope.
* Generic: normed spaces `E`, `F` (the applications take `E = State n`, `F = State 2`), a chart
  `ι : F → E`, `π : E → F` of `range P` (`IsChart`), a candidate `φ(x) = H(π x)` with `H`
  differentiable at the chart point; planar polynomials as lists of monomials (`poly3`,
  `dpoly3` of `theorem/Dynamics/Degenerate/WeakFocus.lean`); real `sin` and `cos`. No model.

Source: Carr, *Applications of Centre Manifold Theory* (1981), §2.5 (the invariance defect of a
candidate graph); Mathlib's `Complex.exp_bound` (the remainder of the exponential series, read at
`x i` for the real and imaginary parts).

Results.
* `IsChart.isOrder_of_isBigO`: `G ∘ ι = O(‖y‖^k)` at `0` gives `G = O(‖u‖^k)` on `range P`.
* `invarianceDefect_comp_chart`: for `φ = H ∘ π`, the invariance defect at `ι y` is
  `DH(y) (chart field of φ at y) − normalField(ι y)`.
* `Degenerate.dxTerm`, `Degenerate.dyTerm` (the monomials of the two partial derivatives) and
  `Degenerate.dpoly3_eq_partials` (`dpoly3` in the plane as `∂ₓp · dx + ∂ᵧp · dy`).
* `abs_cos_sub_taylor_le`, `abs_sin_sub_taylor_le` (`|x| ≤ 1`: the remainders of
  `1 − x²/2 + x⁴/24` and `x − x³/6 + x⁵/120` are at most `(7/4320)|x|⁶`),
  `cos_sub_taylor_isBigO`, `sin_sub_taylor5_isBigO` (both remainders are `O(x⁶)` at `0`).
-/

noncomputable section

namespace powerlib.Dynamics

open Filter Topology Asymptotics

/-! ## Sixth-order Taylor remainders of `cos` and `sin` -/

open Complex in
@[tmio T, powerlib_foundation] private theorem exp_I_sub_taylor (x : ℝ) :
    exp (x * I) - ∑ m ∈ Finset.range 6, ((x : ℂ) * I) ^ m / (m.factorial : ℂ) =
      ((Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24) : ℝ) : ℂ) +
        ((Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120) : ℝ) : ℂ) * I := by
  have h3 : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, mul_pow]
  push_cast
  simp only [h3, I_sq, pow_zero, pow_one]
  ring

open Complex in
@[tmio T, powerlib_foundation] private theorem norm_taylor_le {x : ℝ} (hx : |x| ≤ 1) :
    ‖((Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24) : ℝ) : ℂ) +
        ((Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120) : ℝ) : ℂ) * I‖ ≤ |x| ^ 6 * (7 / 4320) := by
  have hn : ‖(x : ℂ) * I‖ ≤ 1 := by simpa using hx
  have h := Complex.exp_bound hn (n := 6) (by norm_num)
  rw [exp_I_sub_taylor] at h
  have hn' : ‖(x : ℂ) * I‖ = |x| := by simp
  rw [hn'] at h
  refine h.trans (le_of_eq ?_)
  norm_num [Nat.factorial]

/-- `|cos x − (1 − x²/2 + x⁴/24)| ≤ (7/4320)|x|⁶` for `|x| ≤ 1`. -/
@[tmio T, powerlib_foundation] theorem abs_cos_sub_taylor_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)| ≤ |x| ^ 6 * (7 / 4320) := by
  set a : ℝ := Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)
  set b : ℝ := Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120)
  have hre : ((a : ℂ) + (b : ℂ) * Complex.I).re = a := by simp
  calc |a| = |((a : ℂ) + (b : ℂ) * Complex.I).re| := by rw [hre]
    _ ≤ ‖(a : ℂ) + (b : ℂ) * Complex.I‖ := Complex.abs_re_le_norm _
    _ ≤ |x| ^ 6 * (7 / 4320) := norm_taylor_le hx

/-- `|sin x − (x − x³/6 + x⁵/120)| ≤ (7/4320)|x|⁶` for `|x| ≤ 1`. -/
@[tmio T, powerlib_foundation] theorem abs_sin_sub_taylor_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120)| ≤ |x| ^ 6 * (7 / 4320) := by
  set a : ℝ := Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)
  set b : ℝ := Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120)
  have him : ((a : ℂ) + (b : ℂ) * Complex.I).im = b := by simp
  calc |b| = |((a : ℂ) + (b : ℂ) * Complex.I).im| := by rw [him]
    _ ≤ ‖(a : ℂ) + (b : ℂ) * Complex.I‖ := Complex.abs_im_le_norm _
    _ ≤ |x| ^ 6 * (7 / 4320) := norm_taylor_le hx

/-- `cos x − (1 − x²/2 + x⁴/24) = O(x⁶)` at `0`. -/
@[tmio T, powerlib_foundation] theorem cos_sub_taylor_isBigO :
    (fun x : ℝ => Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)) =O[𝓝 0] fun x => x ^ 6 := by
  refine IsBigO.of_bound (7 / 4320) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with x hx
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, mul_comm]
  exact abs_cos_sub_taylor_le hx.le

/-- `sin x − (x − x³/6 + x⁵/120) = O(x⁶)` at `0`. -/
@[tmio T, powerlib_foundation] theorem sin_sub_taylor5_isBigO :
    (fun x : ℝ => Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120)) =O[𝓝 0] fun x => x ^ 6 := by
  refine IsBigO.of_bound (7 / 4320) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with x hx
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, mul_comm]
  exact abs_sin_sub_taylor_le hx.le

/-! ## Partial derivatives of planar polynomials -/

namespace Degenerate

/-- The monomial of `∂ₐ` of `κ aⁱ bʲ cᵏ`. -/
def dxTerm (t : ℝ × ℕ × ℕ × ℕ) : ℝ × ℕ × ℕ × ℕ := (t.1 * t.2.1, t.2.1 - 1, t.2.2.1, t.2.2.2)

/-- The monomial of `∂_b` of `κ aⁱ bʲ cᵏ`. -/
def dyTerm (t : ℝ × ℕ × ℕ × ℕ) : ℝ × ℕ × ℕ × ℕ := (t.1 * t.2.2.1, t.2.1, t.2.2.1 - 1, t.2.2.2)

/-- **`dpoly3` with `dc = 0` is `∂ₐp · da + ∂_b p · db`.** -/
@[tmio T, powerlib_foundation] theorem dpoly3_eq_partials (l : List (ℝ × ℕ × ℕ × ℕ))
    (a b c da db : ℝ) :
    dpoly3 l a b c da db 0 = poly3 (l.map dxTerm) a b c * da + poly3 (l.map dyTerm) a b c * db := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [dpoly3_cons, List.map_cons, poly3_cons, ih, dxTerm, dyTerm]
    ring

end Degenerate

/-! ## Candidate graphs read in a chart -/

namespace CenterManifold

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup V] {P : E →L[ℝ] E} {ι : F →L[ℝ] E} {π : E →L[ℝ] F}

/-- **The order of a map on `range P` read in a chart.** If `G(ι y) = O(‖y‖^k)` at `0`, then
`G(u) = O(‖u‖^k)` as `u → 0` in `range P`. -/
@[tmio T, powerlib_foundation] theorem IsChart.isOrder_of_isBigO (hc : IsChart P ι π) {G : E → V}
    {k : ℕ} (h : (fun y => G (ι y)) =O[𝓝 0] fun y => ‖y‖ ^ k) : IsOrder P G k := by
  rw [isOrder_natCast_iff]
  have hπ : Tendsto π (𝓝[Set.range P] 0) (𝓝 0) := by
    simpa using (π.continuous.tendsto 0).mono_left nhdsWithin_le_nhds
  have h1 := h.comp_tendsto hπ
  have h2 : (fun u : E => ‖π u‖ ^ k) =O[𝓝[Set.range P] 0] fun u => ‖u‖ ^ k := by
    refine IsBigO.of_bound (‖π‖ ^ k) (Eventually.of_forall fun u => ?_)
    simp only [norm_pow, norm_norm]
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (π.le_opNorm u) k
  refine (h1.trans h2).congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [self_mem_nhdsWithin] with u hu
  obtain ⟨v, rfl⟩ := hu
  simp only [Function.comp_apply, hc.ι_π, hc.idem]

variable {A : E →L[ℝ] E} {f : E → E}

/-- **The invariance defect of `φ = H ∘ π` at a chart point**:
`Dφ(ι y)(reducedField) − normalField = DH(y)(chartField y) − normalField`. -/
@[tmio T, powerlib_foundation] theorem invarianceDefect_comp_chart (hc : IsChart P ι π)
    {H : F → E} {y : F} (hH : DifferentiableAt ℝ H y) :
    invarianceDefect A P f (fun x => H (π x)) (ι y) =
      fderiv ℝ H y (chartField A f (fun x => H (π x)) ι π y) -
        normalField A P f (fun x => H (π x)) (ι y) := by
  have hH' : DifferentiableAt ℝ H (π (ι y)) := by rwa [hc.left_inv]
  have hd : fderiv ℝ (fun x => H (π x)) (ι y) = (fderiv ℝ H (π (ι y))).comp π := by
    have h := fderiv_comp (ι y) hH' π.differentiableAt
    rwa [ContinuousLinearMap.fderiv] at h
  rw [invarianceDefect, hd, ContinuousLinearMap.comp_apply, hc.left_inv]
  congr 2
  simp only [reducedField, chartField, map_add, hc.π_proj]

end CenterManifold

end powerlib.Dynamics
