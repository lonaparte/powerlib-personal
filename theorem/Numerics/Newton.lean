import theorem.Numerics.LocalError

/-! # Local quadratic convergence of Newton's method

Local quadratic convergence of Newton's method (corrected statement), and a refutation of the
bound boxed in the source note.

Model boundary.
* `F : E → E` on a real Banach space, an explicit derivative field `J : E → (E →L[ℝ] E)` with
  `HasFDerivAt F (J z) z` on a ball around a root `x*`, `J` `L`-Lipschitz on that ball and `J x*`
  invertible. The Newton step is `N(x) = x - J(x)⁻¹ F(x)` (`Ring.inverse` in the operator
  algebra; the linear system is solved exactly — no inexact solve, no damping).

Source: work-sync theory/T-newton-method.md §1.1–§1.2.

Results.
* `norm_sub_sub_apply_le` — `‖F y - F x - J x (y - x)‖ ≤ (L/2)‖y - x‖²` on a convex set.
* `isUnit_of_norm_inverse_mul_le` — `‖A⁻¹‖ ‖B - A‖ ≤ 1/2` ⇒ `B` invertible and
  `‖B⁻¹‖ ≤ 2 ‖A⁻¹‖` (Neumann series).
* `newtonStep_sub_le` — `‖N(x) - x*‖ ≤ (L/2) ‖J(x)⁻¹‖ ‖x - x*‖²` (the `½` belongs to the
  `‖J(x_k)⁻¹‖` version).
* `newton_local_quadratic` — there is `r > 0` such that on `ball x* r` the Jacobian is
  invertible, `N` maps the ball into itself and `‖N(x) - x*‖ ≤ L ‖J(x*)⁻¹‖ ‖x - x*‖²`
  (no `½` in the `‖J(x*)⁻¹‖` version).
* `newton_iterates_converge` — from any start in that ball the iterates stay in the ball,
  converge to `x*`, and satisfy the quadratic error recursion.
* `newton_boxed_bound_false` — for `F(x) = x + x²/2` (`J` 1-Lipschitz, `J(0) = 1`) and every
  `ε ∈ (0, 1)`, `N(-ε) = ε²/(2(1-ε)) > (L ‖J(0)⁻¹‖/2) ε²`; hence the boxed bound fails on
  every neighbourhood of the root.

Corrections.
* The boxed estimate `‖e_{k+1}‖ ≤ (L ‖J(x*)⁻¹‖ / 2) ‖e_k‖²` is false
  (`newton_boxed_bound_false`); correct versions are `newtonStep_sub_le` (`‖J(x_k)⁻¹‖`, with
  `½`) and `newton_local_quadratic` (`‖J(x*)⁻¹‖`, without `½`). The note's proof sketch
  silently replaces `‖J(x_k)⁻¹‖` by `‖J(x*)⁻¹‖`.
* The note calls this result a "Newton–Kantorovich theorem (simplified)". It is the standard
  local convergence theorem: it assumes a root and an invertible `J(x*)`, whereas Kantorovich's
  theorem proves existence of a root from conditions at `x₀` alone.
-/

noncomputable section
namespace powerlib.Numerics
open Set Metric Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Newton step `x - J(x)⁻¹ F(x)`. -/
def newtonStep (F : E → E) (J : E → E →L[ℝ] E) (x : E) : E := x - Ring.inverse (J x) (F x)

/-- First-order Taylor remainder with a Lipschitz derivative. -/
@[powerlib_foundation] theorem norm_sub_sub_apply_le {F : E → E} {J : E → E →L[ℝ] E}
    {U : Set E} (hU : Convex ℝ U) (hF : ∀ z ∈ U, HasFDerivAt F (J z) z) {L : ℝ}
    (hJ : ∀ z ∈ U, ∀ w ∈ U, ‖J z - J w‖ ≤ L * ‖z - w‖) {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ‖F y - F x - J x (y - x)‖ ≤ L / 2 * ‖y - x‖ ^ 2 := by
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, x + s • (y - x) ∈ U :=
    fun s hs => hU.add_smul_sub_mem hx hy hs
  have hderiv : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => F (x + s • (y - x)) - F x -
      s • J x (y - x)) (J (x + s • (y - x)) (y - x) - J x (y - x)) s := by
    intro s hs
    have hpath : HasDerivAt (fun s : ℝ => x + s • (y - x)) (y - x) s := by
      simpa using ((hasDerivAt_id s).smul_const (y - x)).const_add x
    have h1 := (hF _ (hmem s hs)).comp_hasDerivAt s hpath
    have h2 := (h1.sub_const (F x)).sub ((hasDerivAt_id s).smul_const (J x (y - x)))
    exact h2.congr_deriv (by simp)
  have hbound := norm_le_of_hasDerivAt_le_pow (M := L * ‖y - x‖ ^ 2) (h := 1) 1 hderiv
    (by simp) (fun s hs => by
      rw [← sub_apply]
      calc ‖(J (x + s • (y - x)) - J x) (y - x)‖ ≤ ‖J (x + s • (y - x)) - J x‖ * ‖y - x‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ L * ‖x + s • (y - x) - x‖ * ‖y - x‖ := by
            gcongr; exact hJ _ (hmem s hs) _ hx
        _ = L * ‖y - x‖ ^ 2 * s ^ 1 := by
            rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.1]; ring)
    1 ⟨zero_le_one, le_rfl⟩
  have hb : ‖F (x + (1 : ℝ) • (y - x)) - F x - (1 : ℝ) • J x (y - x)‖ ≤
      L * ‖y - x‖ ^ 2 * (1 : ℝ) ^ (1 + 1) / (((1 : ℕ) : ℝ) + 1) := hbound
  rw [one_smul, one_smul, add_sub_cancel] at hb
  calc _ ≤ _ := hb
    _ = L / 2 * ‖y - x‖ ^ 2 := by push_cast; ring

/-- Perturbation of an invertible operator (Neumann series). -/
@[powerlib_foundation] theorem isUnit_of_norm_inverse_mul_le {A B : E →L[ℝ] E}
    [CompleteSpace E] (hA : IsUnit A) (h : ‖Ring.inverse A‖ * ‖B - A‖ ≤ 1 / 2) :
    IsUnit B ∧ ‖Ring.inverse B‖ ≤ 2 * ‖Ring.inverse A‖ := by
  obtain ⟨u, rfl⟩ := hA
  rw [Ring.inverse_unit] at h ⊢
  set s : E →L[ℝ] E := -((↑u⁻¹ : E →L[ℝ] E) * (B - ↑u)) with hs
  have hsn : ‖s‖ ≤ 1 / 2 := by
    rw [hs, norm_neg]
    exact (norm_mul_le _ _).trans h
  have hs1 : ‖s‖ < 1 := by linarith
  set w := Units.oneSub s hs1
  have hB : B = ↑(u * w) := by
    rw [Units.val_mul, Units.val_oneSub, hs, sub_neg_eq_add, mul_add, mul_one, ← mul_assoc,
      Units.mul_inv, one_mul, add_sub_cancel]
  refine ⟨hB ▸ (u * w).isUnit, ?_⟩
  rw [hB, Ring.inverse_unit, mul_inv_rev, Units.val_mul]
  have hw : ‖(↑w⁻¹ : E →L[ℝ] E)‖ ≤ 2 := by
    change ‖∑' k : ℕ, s ^ k‖ ≤ 2
    have h1 := tsum_geometric_le_of_norm_lt_one s hs1
    have h2 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have h3 : (1 - ‖s‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) two_pos]; linarith
    linarith
  calc ‖(↑w⁻¹ : E →L[ℝ] E) * ↑u⁻¹‖ ≤ ‖(↑w⁻¹ : E →L[ℝ] E)‖ * ‖(↑u⁻¹ : E →L[ℝ] E)‖ :=
        norm_mul_le _ _
    _ ≤ 2 * ‖(↑u⁻¹ : E →L[ℝ] E)‖ := by gcongr

/-- One Newton step with an invertible Jacobian: `‖N(x) - x*‖ ≤ (L/2)‖J(x)⁻¹‖‖x - x*‖²`. -/
@[powerlib_foundation] theorem newtonStep_sub_le {F : E → E} {J : E → E →L[ℝ] E} {U : Set E}
    (hU : Convex ℝ U) (hF : ∀ z ∈ U, HasFDerivAt F (J z) z) {L : ℝ}
    (hJ : ∀ z ∈ U, ∀ w ∈ U, ‖J z - J w‖ ≤ L * ‖z - w‖) {x xs : E} (hx : x ∈ U) (hxs : xs ∈ U)
    (hroot : F xs = 0) (hJx : IsUnit (J x)) :
    ‖newtonStep F J x - xs‖ ≤ L / 2 * ‖Ring.inverse (J x)‖ * ‖x - xs‖ ^ 2 := by
  have htay := norm_sub_sub_apply_le hU hF hJ hx hxs
  have hid : ∀ v, Ring.inverse (J x) (J x v) = v := fun v => by
    have h := congrArg (fun T : E →L[ℝ] E => T v) (Ring.inverse_mul_cancel _ hJx)
    simpa using h
  have heq : newtonStep F J x - xs =
      Ring.inverse (J x) (F xs - F x - J x (xs - x)) := by
    rw [map_sub (Ring.inverse (J x)) (F xs - F x) (J x (xs - x)), hid, hroot, zero_sub,
      map_neg, newtonStep]
    abel
  rw [heq]
  calc ‖Ring.inverse (J x) (F xs - F x - J x (xs - x))‖
      ≤ ‖Ring.inverse (J x)‖ * ‖F xs - F x - J x (xs - x)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖Ring.inverse (J x)‖ * (L / 2 * ‖xs - x‖ ^ 2) := by
        gcongr
    _ = L / 2 * ‖Ring.inverse (J x)‖ * ‖x - xs‖ ^ 2 := by rw [norm_sub_rev]; ring

/-- Local quadratic convergence of Newton's method (correct constant). -/
@[powerlib_foundation] theorem newton_local_quadratic [CompleteSpace E] {F : E → E}
    {J : E → E →L[ℝ] E} {xs : E} {r₀ L : ℝ} (hr₀ : 0 < r₀) (hL : 0 ≤ L)
    (hF : ∀ z ∈ ball xs r₀, HasFDerivAt F (J z) z)
    (hJ : ∀ z ∈ ball xs r₀, ∀ w ∈ ball xs r₀, ‖J z - J w‖ ≤ L * ‖z - w‖)
    (hroot : F xs = 0) (hinv : IsUnit (J xs)) :
    ∃ r > 0, r ≤ r₀ ∧ ∀ x ∈ ball xs r, IsUnit (J x) ∧ newtonStep F J x ∈ ball xs r ∧
      ‖newtonStep F J x - xs‖ ≤ L * ‖Ring.inverse (J xs)‖ * ‖x - xs‖ ^ 2 ∧
      ‖newtonStep F J x - xs‖ ≤ ‖x - xs‖ / 2 := by
  set c := L * ‖Ring.inverse (J xs)‖ with hc
  have hc0 : 0 ≤ c := mul_nonneg hL (norm_nonneg _)
  set r := min r₀ (1 / (2 * (c + 1))) with hr
  have hr0 : 0 < r := lt_min hr₀ (by positivity)
  have hcr : c * r ≤ 1 / 2 := by
    have : r ≤ 1 / (2 * (c + 1)) := min_le_right _ _
    calc c * r ≤ c * (1 / (2 * (c + 1))) := by gcongr
      _ ≤ 1 / 2 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) two_pos]; nlinarith
  refine ⟨r, hr0, min_le_left _ _, fun x hx => ?_⟩
  have hxr₀ : x ∈ ball xs r₀ := ball_subset_ball (min_le_left _ _) hx
  have hxs : xs ∈ ball xs r₀ := mem_ball_self hr₀
  have hd : ‖x - xs‖ < r := by rwa [mem_ball, dist_eq_norm] at hx
  have hpert : ‖Ring.inverse (J xs)‖ * ‖J x - J xs‖ ≤ 1 / 2 := by
    calc ‖Ring.inverse (J xs)‖ * ‖J x - J xs‖ ≤ ‖Ring.inverse (J xs)‖ * (L * ‖x - xs‖) := by
          gcongr; exact hJ x hxr₀ xs hxs
      _ = c * ‖x - xs‖ := by rw [hc]; ring
      _ ≤ c * r := by gcongr
      _ ≤ 1 / 2 := hcr
  obtain ⟨hJx, hnorm⟩ := isUnit_of_norm_inverse_mul_le hinv hpert
  have hstep := newtonStep_sub_le (convex_ball xs r₀) hF hJ hxr₀ hxs hroot hJx
  have hquad : ‖newtonStep F J x - xs‖ ≤ c * ‖x - xs‖ ^ 2 := by
    calc _ ≤ L / 2 * ‖Ring.inverse (J x)‖ * ‖x - xs‖ ^ 2 := hstep
      _ ≤ L / 2 * (2 * ‖Ring.inverse (J xs)‖) * ‖x - xs‖ ^ 2 := by gcongr
      _ = c * ‖x - xs‖ ^ 2 := by rw [hc]; ring
  have hhalf : ‖newtonStep F J x - xs‖ ≤ ‖x - xs‖ / 2 := by
    calc _ ≤ c * ‖x - xs‖ ^ 2 := hquad
      _ = (c * ‖x - xs‖) * ‖x - xs‖ := by ring
      _ ≤ (1 / 2) * ‖x - xs‖ := by
          gcongr
          calc c * ‖x - xs‖ ≤ c * r := by gcongr
            _ ≤ 1 / 2 := hcr
      _ = ‖x - xs‖ / 2 := by ring
  refine ⟨hJx, ?_, hquad, hhalf⟩
  rw [mem_ball, dist_eq_norm]
  calc _ ≤ ‖x - xs‖ / 2 := hhalf
    _ < r := by linarith [norm_nonneg (x - xs)]

/-- Newton iterates from the convergence ball stay there, satisfy the quadratic error
recursion, halve the error at least, and converge to the root. -/
@[powerlib_foundation] theorem newton_iterates_converge [CompleteSpace E] {F : E → E}
    {J : E → E →L[ℝ] E} {xs : E} {r₀ L : ℝ} (hr₀ : 0 < r₀) (hL : 0 ≤ L)
    (hF : ∀ z ∈ ball xs r₀, HasFDerivAt F (J z) z)
    (hJ : ∀ z ∈ ball xs r₀, ∀ w ∈ ball xs r₀, ‖J z - J w‖ ≤ L * ‖z - w‖)
    (hroot : F xs = 0) (hinv : IsUnit (J xs)) :
    ∃ r > 0, ∀ x : ℕ → E, x 0 ∈ ball xs r → (∀ k, x (k + 1) = newtonStep F J (x k)) →
      (∀ k, x k ∈ ball xs r ∧
        ‖x (k + 1) - xs‖ ≤ L * ‖Ring.inverse (J xs)‖ * ‖x k - xs‖ ^ 2 ∧
        ‖x k - xs‖ ≤ (1 / 2) ^ k * ‖x 0 - xs‖) ∧ Tendsto x atTop (𝓝 xs) := by
  obtain ⟨r, hr, -, hball⟩ := newton_local_quadratic hr₀ hL hF hJ hroot hinv
  refine ⟨r, hr, fun x hx0 hx => ?_⟩
  have hmem : ∀ k, x k ∈ ball xs r := by
    intro k
    induction k with
    | zero => exact hx0
    | succ k ih => rw [hx k]; exact (hball _ ih).2.1
  have hgeom : ∀ k, ‖x k - xs‖ ≤ (1 / 2) ^ k * ‖x 0 - xs‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [hx k]
      calc _ ≤ ‖x k - xs‖ / 2 := (hball _ (hmem k)).2.2.2
        _ ≤ (1 / 2) ^ k * ‖x 0 - xs‖ / 2 := by gcongr
        _ = (1 / 2) ^ (k + 1) * ‖x 0 - xs‖ := by ring
  refine ⟨fun k => ⟨hmem k, by rw [hx k]; exact (hball _ (hmem k)).2.2.1, hgeom k⟩, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k * ‖x 0 - xs‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).mul_const ‖x 0 - xs‖
  exact squeeze_zero (fun k => norm_nonneg _) hgeom hlim

/-! ### The boxed bound of the source note is false -/

/-- Counterexample field `F(x) = x + x²/2`. -/
def counterF (x : ℝ) : ℝ := x + x ^ 2 / 2

/-- Its derivative field `J(x) = (1 + x)·id`. -/
def counterJ (x : ℝ) : ℝ →L[ℝ] ℝ := (1 + x) • ContinuousLinearMap.id ℝ ℝ

@[powerlib_foundation] theorem counterF_hasFDerivAt (x : ℝ) :
    HasFDerivAt counterF (counterJ x) x := by
  have h : HasDerivAt counterF (1 + x) x := by
    have h1 := (hasDerivAt_id' x).add ((hasDerivAt_pow 2 x).div_const 2)
    convert h1 using 1
    · funext y; simp [counterF]
    · norm_num
  have hJ : counterJ x = ContinuousLinearMap.toSpanSingleton ℝ (1 + x) := by
    ext; simp [counterJ]
  rw [hJ]
  exact h.hasFDerivAt

@[powerlib_foundation] theorem counterJ_lipschitz (x y : ℝ) :
    ‖counterJ x - counterJ y‖ = 1 * ‖x - y‖ := by
  have h : counterJ x - counterJ y = (x - y) • ContinuousLinearMap.id ℝ ℝ := by
    ext; simp [counterJ]
  rw [h, norm_smul, ContinuousLinearMap.norm_id, mul_one, one_mul]

@[powerlib_foundation] private lemma inverse_counterJ {x : ℝ} (hx : 1 + x ≠ 0) :
    Ring.inverse (counterJ x) = (1 + x)⁻¹ • ContinuousLinearMap.id ℝ ℝ := by
  let u : (ℝ →L[ℝ] ℝ)ˣ :=
    ⟨counterJ x, (1 + x)⁻¹ • ContinuousLinearMap.id ℝ ℝ,
      by ext; simp [counterJ, hx], by ext; simp [counterJ, hx]⟩
  exact Ring.inverse_unit u

@[powerlib_foundation] theorem counter_newtonStep {ε : ℝ} (hε1 : ε < 1) :
    newtonStep counterF counterJ (-ε) = ε ^ 2 / (2 * (1 - ε)) := by
  have hx : 1 + -ε ≠ 0 := by linarith
  rw [newtonStep, inverse_counterJ hx]
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    counterF]
  have : (1 : ℝ) - ε ≠ 0 := by linarith
  field_simp
  ring

/-- The note's boxed estimate `‖e₁‖ ≤ (L ‖J(x*)⁻¹‖/2)‖e₀‖²` fails for `F(x) = x + x²/2`
(`L = 1`, `x* = 0`, `J(0) = 1`) at every starting point `x₀ = -ε`, `0 < ε < 1`. -/
@[powerlib_foundation] theorem newton_boxed_bound_false {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    1 * ‖Ring.inverse (counterJ 0)‖ / 2 * ‖(-ε) - 0‖ ^ 2 <
      ‖newtonStep counterF counterJ (-ε) - 0‖ := by
  rw [inverse_counterJ (by norm_num), counter_newtonStep hε1]
  have hnorm : ‖(1 + (0 : ℝ))⁻¹ • ContinuousLinearMap.id ℝ ℝ‖ = 1 := by
    simp [ContinuousLinearMap.norm_id]
  rw [hnorm, sub_zero, sub_zero, norm_neg, Real.norm_of_nonneg hε0.le,
    Real.norm_of_nonneg (by positivity)]
  rw [lt_div_iff₀ (by nlinarith)]
  have h3 : 0 < ε ^ 2 * ε := by positivity
  nlinarith

/-- Equivalently: no neighbourhood of the root satisfies the boxed bound. -/
@[powerlib_foundation] theorem newton_boxed_bound_not_local :
    ¬ ∃ r > 0, ∀ x : ℝ, ‖x - 0‖ < r →
      ‖newtonStep counterF counterJ x - 0‖ ≤
        1 * ‖Ring.inverse (counterJ 0)‖ / 2 * ‖x - 0‖ ^ 2 := by
  rintro ⟨r, hr, h⟩
  set ε := min (r / 2) (1 / 2) with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hεr : ‖-ε - 0‖ < r := by
    rw [sub_zero, norm_neg, Real.norm_of_nonneg hε0.le]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  exact absurd (h (-ε) hεr) (not_le.mpr (newton_boxed_bound_false hε0 hε1))

end powerlib.Numerics
