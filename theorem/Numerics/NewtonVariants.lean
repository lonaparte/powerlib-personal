import theorem.Numerics.Newton
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Variants of Newton's method: chord, inexact Newton, Broyden, Armijo, Levenberg–Marquardt

Chord (frozen Jacobian) iteration, inexact Newton, Broyden's secant update, Armijo backtracking
for damped Newton, and the Levenberg–Marquardt limits.

Model boundary.
* Deterministic iterations for a nonlinear equation `F(x) = 0`; every linear system is either
  solved exactly or with an explicitly stated residual; no rounding, no step-size heuristics
  other than the ones stated.
* General results are on a real Banach space `E` with a derivative field `J`
  (`HasFDerivAt F (J z) z`); the Armijo / merit-function and Levenberg–Marquardt results use a
  real inner-product space (complete for the adjoint); Broyden's update is stated for real
  matrices on `Fin n → ℝ`.

Source: work-sync theory/T-newton-method.md §1.4 (Armijo), §1.5 (chord), §1.6 (Broyden),
§1.7 (Levenberg–Marquardt), §1.8 (inexact Newton, `η_k = O(‖F‖)` ⇒ quadratic).

Results.
* Chord: `chordStep_lipschitz` (`‖C x − C y‖ ≤ ‖A⁻¹‖ c ‖x − y‖` when `‖J z − A‖ ≤ c` on a
  convex set), `chord_contractingWith` (the chord map is a `ContractingWith` self-map of a
  closed ball around the root), `chord_iterates_converge` (linear convergence
  `‖x_k − x*‖ ≤ qᵏ ‖x₀ − x*‖`), `chord_rate_of_lipschitz` (with `A = J(x₀)` and an
  `L`-Lipschitz `J` on `ball x* r` one may take `c = 2Lr`).
* `inexactNewton_step_le` — inexact Newton: if the linear residual satisfies
  `‖J(x)δ + F(x)‖ ≤ η‖F(x)‖` with forcing term `η ≤ c‖F(x)‖` (i.e. `η = O(‖F‖)`), the step is
  still quadratic: `‖x + δ − x*‖ ≤ ‖J(x)⁻¹‖ (L/2 + c M²) ‖x − x*‖²`.
* `broydenUpdate_secant`, `broydenUpdate_orthogonal` — Broyden: `B⁺ Δx = ΔF` and `B⁺ v = B v`
  for `v ⊥ Δx`.
* Armijo: `armijo_exists` (sufficient decrease holds for all small step lengths along a
  descent direction), `armijo_backtracking_terminates` (`α = ρᵐ` for some `m`),
  `newtonDirection_descent` (the Newton direction is a descent direction of
  `φ = ½‖F‖²` with `φ'(x) δ = −‖F(x)‖²`), `dampedNewton_armijo_terminates`.
* Levenberg–Marquardt `(JᵀJ + μI) δ = −Jᵀ r`: `lmStep_unique` (`μ > 0`), `lmStep_exists`
  (`μ > 0`, finite dimension), `lmStep_norm_le` (`‖δ‖ ≤ ‖Jᵀ r‖/μ`), `lmStep_tendsto_zero` and
  `lmStep_smul_tendsto` (`δ(μ) → 0`, `μ δ(μ) → −Jᵀ r`, the steepest-descent direction of
  `½‖r‖²`, as `μ → ∞`), `lmStep_zero_eq_newton` (`μ = 0` with square invertible `J` is the
  Newton step `−J⁻¹ r`).

Scope notes.
* §1.5's "speed coefficient `∝ L ‖x⁽⁰⁾ − x*‖`" is formalized in the weaker but rigorous form
  `q = 2 L r ‖J(x₀)⁻¹‖` on `ball x* r` (`chord_rate_of_lipschitz`).
* The Broyden superlinear rate (Dennis–Moré) and the Eisenstat–Walker forcing rule are not
  formalized.
-/

noncomputable section
namespace powerlib.Numerics
open Set Metric Filter
open scoped Topology

/-! ### Chord method -/

section Chord

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Chord step with a frozen operator `A` (e.g. `A = J(x₀)`): `x − A⁻¹ F(x)`. -/
def chordStep (F : E → E) (A : E →L[ℝ] E) (x : E) : E := x - Ring.inverse A (F x)

/-- The chord map is Lipschitz with constant `‖A⁻¹‖ c` on a convex set where `‖J − A‖ ≤ c`. -/
@[powerlib_foundation] theorem chordStep_lipschitz {F : E → E} {J : E → E →L[ℝ] E} {U : Set E}
    (hU : Convex ℝ U) (hF : ∀ z ∈ U, HasFDerivAt F (J z) z) {A : E →L[ℝ] E} (hA : IsUnit A)
    {c : ℝ} (hJA : ∀ z ∈ U, ‖J z - A‖ ≤ c) {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ‖chordStep F A x - chordStep F A y‖ ≤ ‖Ring.inverse A‖ * c * ‖x - y‖ := by
  have hmv := hU.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (hF z hz).hasFDerivWithinAt) hJA hy hx
  have hid : Ring.inverse A (A (x - y)) = x - y := by
    have h := congrArg (fun T : E →L[ℝ] E => T (x - y)) (Ring.inverse_mul_cancel _ hA)
    simpa using h
  have heq : chordStep F A x - chordStep F A y =
      -Ring.inverse A (F x - F y - A (x - y)) := by
    rw [map_sub (Ring.inverse A) (F x - F y) (A (x - y)), hid, map_sub, chordStep, chordStep]
    abel
  rw [heq, norm_neg]
  calc ‖Ring.inverse A (F x - F y - A (x - y))‖
      ≤ ‖Ring.inverse A‖ * ‖F x - F y - A (x - y)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖Ring.inverse A‖ * (c * ‖x - y‖) := by gcongr
    _ = ‖Ring.inverse A‖ * c * ‖x - y‖ := by ring

/-- The chord map fixes a root. -/
@[powerlib_foundation] theorem chordStep_root {F : E → E} {A : E →L[ℝ] E} {xs : E}
    (hroot : F xs = 0) : chordStep F A xs = xs := by
  simp [chordStep, hroot]

/-- Contraction towards the root: `‖C(x) − x*‖ ≤ q ‖x − x*‖` on the closed ball. -/
@[powerlib_foundation] theorem chordStep_sub_root_le {F : E → E} {J : E → E →L[ℝ] E}
    {A : E →L[ℝ] E} {xs : E} {r c : ℝ} (hF : ∀ z ∈ closedBall xs r, HasFDerivAt F (J z) z)
    (hA : IsUnit A) (hJA : ∀ z ∈ closedBall xs r, ‖J z - A‖ ≤ c) (hroot : F xs = 0)
    (hr : 0 ≤ r) {x : E} (hx : x ∈ closedBall xs r) :
    ‖chordStep F A x - xs‖ ≤ ‖Ring.inverse A‖ * c * ‖x - xs‖ := by
  have h := chordStep_lipschitz (convex_closedBall xs r) hF hA hJA hx (mem_closedBall_self hr)
  rwa [chordStep_root hroot] at h

/-- **Chord method is a contraction.** If `‖J z − A‖ ≤ c` on `closedBall x* r` and
`q = ‖A⁻¹‖ c < 1`, the chord map restricted to the closed ball is `ContractingWith q`;
its unique fixed point is the root. -/
@[powerlib_foundation] theorem chord_contractingWith [CompleteSpace E] {F : E → E}
    {J : E → E →L[ℝ] E} {A : E →L[ℝ] E} {xs : E} {r c : ℝ}
    (hF : ∀ z ∈ closedBall xs r, HasFDerivAt F (J z) z) (hA : IsUnit A)
    (hJA : ∀ z ∈ closedBall xs r, ‖J z - A‖ ≤ c) (hroot : F xs = 0) (hr : 0 ≤ r)
    (hq0 : 0 ≤ ‖Ring.inverse A‖ * c) (hq : ‖Ring.inverse A‖ * c < 1) :
    ∃ hmaps : MapsTo (chordStep F A) (closedBall xs r) (closedBall xs r),
      ContractingWith ⟨‖Ring.inverse A‖ * c, hq0⟩ (hmaps.restrict) := by
  have hmaps : MapsTo (chordStep F A) (closedBall xs r) (closedBall xs r) := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm]
    calc ‖chordStep F A x - xs‖ ≤ ‖Ring.inverse A‖ * c * ‖x - xs‖ :=
          chordStep_sub_root_le hF hA hJA hroot hr hx
      _ ≤ 1 * ‖x - xs‖ := by gcongr
      _ ≤ r := by rw [one_mul, ← dist_eq_norm]; exact hx
  refine ⟨hmaps, ?_, ?_⟩
  · exact_mod_cast hq
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [MapsTo.restrict, Subtype.dist_eq, dist_eq_norm]
    exact chordStep_lipschitz (convex_closedBall xs r) hF hA hJA x.2 y.2

/-- **Linear convergence of the chord method.** Iterates started in `closedBall x* r` stay
there and `‖x_k − x*‖ ≤ qᵏ ‖x₀ − x*‖` with `q = ‖A⁻¹‖ c < 1`; hence `x_k → x*`. -/
@[powerlib_foundation] theorem chord_iterates_converge {F : E → E} {J : E → E →L[ℝ] E}
    {A : E →L[ℝ] E} {xs : E} {r c : ℝ} (hF : ∀ z ∈ closedBall xs r, HasFDerivAt F (J z) z)
    (hA : IsUnit A) (hJA : ∀ z ∈ closedBall xs r, ‖J z - A‖ ≤ c) (hroot : F xs = 0)
    (hr : 0 ≤ r) (hq0 : 0 ≤ ‖Ring.inverse A‖ * c) (hq : ‖Ring.inverse A‖ * c < 1)
    (x : ℕ → E) (hx0 : x 0 ∈ closedBall xs r) (hx : ∀ k, x (k + 1) = chordStep F A (x k)) :
    (∀ k, x k ∈ closedBall xs r ∧ ‖x k - xs‖ ≤ (‖Ring.inverse A‖ * c) ^ k * ‖x 0 - xs‖) ∧
      Tendsto x atTop (𝓝 xs) := by
  set q := ‖Ring.inverse A‖ * c with hqdef
  have hstep : ∀ k, x k ∈ closedBall xs r → x (k + 1) ∈ closedBall xs r ∧
      ‖x (k + 1) - xs‖ ≤ q * ‖x k - xs‖ := by
    intro k hk
    have h := chordStep_sub_root_le hF hA hJA hroot hr hk
    rw [← hx k] at h
    refine ⟨?_, h⟩
    rw [mem_closedBall, dist_eq_norm]
    calc _ ≤ q * ‖x k - xs‖ := h
      _ ≤ 1 * ‖x k - xs‖ := by gcongr
      _ ≤ r := by rw [one_mul, ← dist_eq_norm]; exact hk
  have hall : ∀ k, x k ∈ closedBall xs r ∧ ‖x k - xs‖ ≤ q ^ k * ‖x 0 - xs‖ := by
    intro k
    induction k with
    | zero => exact ⟨hx0, by simp⟩
    | succ k ih =>
      obtain ⟨hmem, hle⟩ := hstep k ih.1
      refine ⟨hmem, ?_⟩
      calc _ ≤ q * ‖x k - xs‖ := hle
        _ ≤ q * (q ^ k * ‖x 0 - xs‖) := by gcongr; exact ih.2
        _ = q ^ (k + 1) * ‖x 0 - xs‖ := by ring
  refine ⟨hall, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun k : ℕ => q ^ k * ‖x 0 - xs‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).mul_const ‖x 0 - xs‖
  exact squeeze_zero (fun k => norm_nonneg _) (fun k => (hall k).2) hlim

/-- With the frozen Jacobian `A = J(x₀)`, `x₀ ∈ closedBall x* r` and `J` `L`-Lipschitz on the
ball, the hypothesis of the chord results holds with `c = 2Lr`, so the contraction factor is
`q = 2 L r ‖J(x₀)⁻¹‖`. -/
@[powerlib_foundation] theorem chord_rate_of_lipschitz {J : E → E →L[ℝ] E} {xs x₀ : E}
    {r L : ℝ} (hL : 0 ≤ L) (hJ : ∀ z ∈ closedBall xs r, ∀ w ∈ closedBall xs r,
      ‖J z - J w‖ ≤ L * ‖z - w‖) (hx₀ : x₀ ∈ closedBall xs r) :
    ∀ z ∈ closedBall xs r, ‖J z - J x₀‖ ≤ 2 * L * r := by
  intro z hz
  have hz' : ‖z - xs‖ ≤ r := by rw [← dist_eq_norm]; exact hz
  have hx' : ‖x₀ - xs‖ ≤ r := by rw [← dist_eq_norm]; exact hx₀
  calc ‖J z - J x₀‖ ≤ L * ‖z - x₀‖ := hJ z hz x₀ hx₀
    _ ≤ L * (‖z - xs‖ + ‖x₀ - xs‖) := by
        gcongr
        calc ‖z - x₀‖ = ‖(z - xs) - (x₀ - xs)‖ := by rw [sub_sub_sub_cancel_right]
          _ ≤ ‖z - xs‖ + ‖x₀ - xs‖ := norm_sub_le _ _
    _ ≤ L * (r + r) := by gcongr
    _ = 2 * L * r := by ring

end Chord

/-! ### Inexact Newton -/

section Inexact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Inexact Newton with `η = O(‖F‖)` is still quadratic.** If the inner linear solve leaves
a residual `‖J(x)δ + F(x)‖ ≤ c ‖F(x)‖²` (forcing term `η = c‖F(x)‖`) and
`‖F(x)‖ ≤ M ‖x − x*‖`, then `‖x + δ − x*‖ ≤ ‖J(x)⁻¹‖ (L/2 + c M²) ‖x − x*‖²`. -/
@[powerlib_foundation] theorem inexactNewton_step_le {F : E → E} {J : E → E →L[ℝ] E}
    {U : Set E} (hU : Convex ℝ U) (hF : ∀ z ∈ U, HasFDerivAt F (J z) z) {L : ℝ}
    (hJ : ∀ z ∈ U, ∀ w ∈ U, ‖J z - J w‖ ≤ L * ‖z - w‖) {x xs : E} (hx : x ∈ U) (hxs : xs ∈ U)
    (hroot : F xs = 0) (hJx : IsUnit (J x)) {M c : ℝ} (hc : 0 ≤ c)
    (hM : ‖F x‖ ≤ M * ‖x - xs‖) (δ : E) (hres : ‖J x δ + F x‖ ≤ c * ‖F x‖ ^ 2) :
    ‖x + δ - xs‖ ≤ ‖Ring.inverse (J x)‖ * (L / 2 + c * M ^ 2) * ‖x - xs‖ ^ 2 := by
  have hid : Ring.inverse (J x) (J x δ) = δ := by
    have h := congrArg (fun T : E →L[ℝ] E => T δ) (Ring.inverse_mul_cancel _ hJx)
    simpa using h
  have hsplit : x + δ - xs =
      (newtonStep F J x - xs) + Ring.inverse (J x) (J x δ + F x) := by
    rw [map_add, hid, newtonStep]
    abel
  have hN := newtonStep_sub_le hU hF hJ hx hxs hroot hJx
  have hFsq : ‖F x‖ ^ 2 ≤ M ^ 2 * ‖x - xs‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hM 2
  have hR : ‖Ring.inverse (J x) (J x δ + F x)‖ ≤
      ‖Ring.inverse (J x)‖ * (c * M ^ 2 * ‖x - xs‖ ^ 2) := by
    calc _ ≤ ‖Ring.inverse (J x)‖ * ‖J x δ + F x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖Ring.inverse (J x)‖ * (c * ‖F x‖ ^ 2) := by gcongr
      _ ≤ ‖Ring.inverse (J x)‖ * (c * (M ^ 2 * ‖x - xs‖ ^ 2)) := by gcongr
      _ = _ := by ring
  rw [hsplit]
  calc _ ≤ ‖newtonStep F J x - xs‖ + ‖Ring.inverse (J x) (J x δ + F x)‖ := norm_add_le _ _
    _ ≤ L / 2 * ‖Ring.inverse (J x)‖ * ‖x - xs‖ ^ 2 +
        ‖Ring.inverse (J x)‖ * (c * M ^ 2 * ‖x - xs‖ ^ 2) := add_le_add hN hR
    _ = _ := by ring

end Inexact

/-! ### Broyden's update -/

section Broyden

open Matrix

variable {n : ℕ}

/-- Broyden's "good" update `B⁺ = B + (ΔF − B Δx) Δxᵀ / ‖Δx‖²`. -/
def broydenUpdate (B : Matrix (Fin n) (Fin n) ℝ) (s y : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  B + (1 / (s ⬝ᵥ s)) • vecMulVec (y - B *ᵥ s) s

/-- **Secant condition**: `B⁺ Δx = ΔF` whenever `Δx ≠ 0`. -/
@[powerlib_foundation] theorem broydenUpdate_secant (B : Matrix (Fin n) (Fin n) ℝ)
    {s : Fin n → ℝ} (hs : s ≠ 0) (y : Fin n → ℝ) : broydenUpdate B s y *ᵥ s = y := by
  have hss : s ⬝ᵥ s ≠ 0 := by
    intro h
    exact hs (dotProduct_self_eq_zero.mp h)
  rw [broydenUpdate, add_mulVec, smul_mulVec, vecMulVec_mulVec]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  field_simp
  ring

/-- **Least change**: directions orthogonal to `Δx` are not modified. -/
@[powerlib_foundation] theorem broydenUpdate_orthogonal (B : Matrix (Fin n) (Fin n) ℝ)
    (s y v : Fin n → ℝ) (hv : s ⬝ᵥ v = 0) : broydenUpdate B s y *ᵥ v = B *ᵥ v := by
  rw [broydenUpdate, add_mulVec, smul_mulVec, vecMulVec_mulVec, hv]
  simp

end Broyden

/-! ### Armijo backtracking -/

section Armijo

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Armijo condition is satisfiable.** If `φ` is differentiable at `x` and `d` is a descent
direction (`φ'(x) d < 0`), then for `c₁ < 1` there is `ᾱ > 0` such that every
`α ∈ (0, ᾱ]` satisfies `φ(x + α d) ≤ φ(x) + c₁ α φ'(x) d`. -/
@[powerlib_foundation] theorem armijo_exists {φ : E → ℝ} {φ' : E →L[ℝ] ℝ} {x d : E}
    (hφ : HasFDerivAt φ φ' x) (hd : φ' d < 0) {c₁ : ℝ} (hc₁ : c₁ < 1) :
    ∃ αbar > 0, ∀ α ∈ Ioc 0 αbar, φ (x + α • d) ≤ φ x + c₁ * α * φ' d := by
  set g : ℝ → ℝ := fun α => φ (x + α • d) with hg
  have hline : HasDerivAt (fun α : ℝ => x + α • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
  have hφ0 : HasFDerivAt φ φ' (x + (0 : ℝ) • d) := by simpa using hφ
  have hgd : HasDerivAt g (φ' d) 0 := hφ0.comp_hasDerivAt (0 : ℝ) hline
  have hslope := hgd.tendsto_slope_zero_right
  have hlt : φ' d < c₁ * φ' d := by nlinarith
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (g (0 + t) - g 0) < c₁ * φ' d :=
    hslope (Iio_mem_nhds hlt)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  refine ⟨ε / 2, by positivity, fun α hα => ?_⟩
  have hαpos : 0 < α := hα.1
  have hαε : dist α 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hαpos]; linarith [hα.2]
  have h := hball hαε hαpos
  simp only [zero_add, smul_eq_mul] at h
  have h0 : g 0 = φ x := by simp [hg]
  rw [h0] at h
  have h2 : φ (x + α • d) - φ x < c₁ * φ' d * α := by
    rw [inv_mul_lt_iff₀ hαpos] at h; linarith
  change g α ≤ _ at *
  show φ (x + α • d) ≤ φ x + c₁ * α * φ' d
  nlinarith

/-- **Backtracking terminates**: for `ρ ∈ (0, 1)` some `α = ρᵐ` passes the Armijo test. -/
@[powerlib_foundation] theorem armijo_backtracking_terminates {φ : E → ℝ} {φ' : E →L[ℝ] ℝ}
    {x d : E} (hφ : HasFDerivAt φ φ' x) (hd : φ' d < 0) {c₁ ρ : ℝ} (hc₁ : c₁ < 1)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ m : ℕ, φ (x + ρ ^ m • d) ≤ φ x + c₁ * ρ ^ m * φ' d := by
  obtain ⟨αbar, hαbar, h⟩ := armijo_exists hφ hd hc₁
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hαbar hρ1
  exact ⟨m, h _ ⟨pow_pos hρ0 m, hm.le⟩⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

open scoped RealInnerProductSpace

/-- **Newton direction is a descent direction** of the merit function `φ = ½‖F‖²`:
`φ'(x) (−J(x)⁻¹ F(x)) = −‖F(x)‖²`. -/
@[powerlib_foundation] theorem newtonDirection_descent {F : H → H} {J : H →L[ℝ] H} {x : H}
    (hF : HasFDerivAt F J x) (hJ : IsUnit J) :
    ∃ φ' : H →L[ℝ] ℝ, HasFDerivAt (fun y => ‖F y‖ ^ 2 / 2) φ' x ∧
      φ' (-Ring.inverse J (F x)) = -‖F x‖ ^ 2 := by
  refine ⟨(1 / 2 : ℝ) • (2 • (innerSL ℝ (F x)).comp J), ?_, ?_⟩
  · have h := hF.norm_sq.const_mul (1 / 2 : ℝ)
    convert h using 1
    funext y; ring
  · have hid : J (Ring.inverse J (F x)) = F x := by
      have h := congrArg (fun T : H →L[ℝ] H => T (F x)) (Ring.mul_inverse_cancel _ hJ)
      simpa using h
    rw [smul_apply, smul_apply,
      ContinuousLinearMap.comp_apply, map_neg, hid, innerSL_apply_apply, inner_neg_right,
      real_inner_self_eq_norm_sq, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring

/-- **Damped Newton with Armijo backtracking is well defined**: away from a root, some
`α = ρᵐ` gives `½‖F(x + α δ)‖² ≤ ½‖F(x)‖² − c₁ α ‖F(x)‖²`, `δ = −J(x)⁻¹F(x)`. -/
@[powerlib_foundation] theorem dampedNewton_armijo_terminates {F : H → H} {J : H →L[ℝ] H}
    {x : H} (hF : HasFDerivAt F J x) (hJ : IsUnit J) (hFx : F x ≠ 0) {c₁ ρ : ℝ}
    (hc₁ : c₁ < 1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ m : ℕ, ‖F (x + ρ ^ m • (-Ring.inverse J (F x)))‖ ^ 2 / 2 ≤
      ‖F x‖ ^ 2 / 2 - c₁ * ρ ^ m * ‖F x‖ ^ 2 := by
  obtain ⟨φ', hφ', hval⟩ := newtonDirection_descent hF hJ
  have hd : φ' (-Ring.inverse J (F x)) < 0 := by
    rw [hval]; have := norm_pos_iff.mpr hFx; nlinarith
  obtain ⟨m, hm⟩ := armijo_backtracking_terminates hφ' hd hc₁ hρ0 hρ1
  refine ⟨m, ?_⟩
  rw [hval] at hm
  linarith

end Armijo

/-! ### Levenberg–Marquardt -/

section LM

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [CompleteSpace E']

open scoped RealInnerProductSpace

/-- Levenberg–Marquardt step: `(JᵀJ + μI) δ = −Jᵀ r` (`r = F(x)` the residual). -/
def IsLMStep (J : E →L[ℝ] E') (r : E') (μ : ℝ) (δ : E) : Prop :=
  (ContinuousLinearMap.adjoint J) (J δ) + μ • δ = -(ContinuousLinearMap.adjoint J) r

@[powerlib_foundation] theorem inner_adjoint_self (J : E →L[ℝ] E') (v : E) :
    ⟪(ContinuousLinearMap.adjoint J) (J v), v⟫ = ‖J v‖ ^ 2 := by
  rw [ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]

/-- A priori bound `μ ‖δ‖ ≤ ‖Jᵀ r‖`. -/
@[powerlib_foundation] theorem lmStep_norm_le {J : E →L[ℝ] E'} {r : E'} {μ : ℝ} (hμ : 0 < μ)
    {δ : E} (h : IsLMStep J r μ δ) : ‖δ‖ ≤ ‖(ContinuousLinearMap.adjoint J) r‖ / μ := by
  set g := (ContinuousLinearMap.adjoint J) r
  have hin := congrArg (fun w => ⟪w, δ⟫) h
  simp only [inner_add_left, real_inner_smul_left, inner_neg_left, inner_adjoint_self,
    real_inner_self_eq_norm_sq] at hin
  have hcs : -⟪g, δ⟫ ≤ ‖g‖ * ‖δ‖ := by
    have := real_inner_le_norm (-g) δ
    rwa [inner_neg_left, norm_neg] at this
  have hsq : 0 ≤ ‖J δ‖ ^ 2 := sq_nonneg _
  have hkey : μ * ‖δ‖ ^ 2 ≤ ‖g‖ * ‖δ‖ := by linarith
  rw [le_div_iff₀ hμ]
  rcases (norm_nonneg δ).eq_or_lt with h0 | hpos
  · rw [← h0]; simp [norm_nonneg]
  · nlinarith

/-- For `μ > 0` the Levenberg–Marquardt step is unique. -/
@[powerlib_foundation] theorem lmStep_unique {J : E →L[ℝ] E'} {r : E'} {μ : ℝ} (hμ : 0 < μ)
    {δ₁ δ₂ : E} (h₁ : IsLMStep J r μ δ₁) (h₂ : IsLMStep J r μ δ₂) : δ₁ = δ₂ := by
  have hd : IsLMStep J 0 μ (δ₁ - δ₂) := by
    unfold IsLMStep at *
    simp only [map_sub, smul_sub, map_zero, neg_zero]
    rw [sub_add_sub_comm, h₁, h₂, sub_self]
  have := lmStep_norm_le hμ hd
  simp only [map_zero, norm_zero, zero_div] at this
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

/-- For `μ > 0` the Levenberg–Marquardt step exists (finite dimension). -/
@[powerlib_foundation] theorem lmStep_exists [FiniteDimensional ℝ E] (J : E →L[ℝ] E') (r : E')
    {μ : ℝ} (hμ : 0 < μ) : ∃ δ, IsLMStep J r μ δ := by
  set T : E →ₗ[ℝ] E :=
    ((ContinuousLinearMap.adjoint J).comp J + μ • ContinuousLinearMap.id ℝ E).toLinearMap
    with hT
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hstep : IsLMStep J 0 μ v := by
      unfold IsLMStep
      simpa [hT] using hv
    have := lmStep_norm_le hμ hstep
    simp only [map_zero, norm_zero, zero_div] at this
    exact norm_le_zero_iff.mp this
  obtain ⟨δ, hδ⟩ := (LinearMap.injective_iff_surjective.mp hinj)
    (-(ContinuousLinearMap.adjoint J) r)
  exact ⟨δ, by simpa [IsLMStep, hT] using hδ⟩

/-- `μ → ∞`: the step shrinks, `δ(μ) → 0`. -/
@[powerlib_foundation] theorem lmStep_tendsto_zero {J : E →L[ℝ] E'} {r : E'} {δ : ℝ → E}
    (hδ : ∀ μ > 0, IsLMStep J r μ (δ μ)) : Tendsto δ atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun μ : ℝ => ‖(ContinuousLinearMap.adjoint J) r‖ / μ) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero' (Eventually.of_forall fun μ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with μ hμ
  exact lmStep_norm_le hμ (hδ μ hμ)

/-- `μ → ∞`: `μ δ(μ) → −Jᵀ r`, the steepest-descent direction of `½‖r‖²`. -/
@[powerlib_foundation] theorem lmStep_smul_tendsto {J : E →L[ℝ] E'} {r : E'} {δ : ℝ → E}
    (hδ : ∀ μ > 0, IsLMStep J r μ (δ μ)) :
    Tendsto (fun μ => μ • δ μ) atTop (𝓝 (-(ContinuousLinearMap.adjoint J) r)) := by
  set G : E →L[ℝ] E := (ContinuousLinearMap.adjoint J).comp J
  have heq : ∀ μ > 0, μ • δ μ = -(ContinuousLinearMap.adjoint J) r - G (δ μ) := by
    intro μ hμ
    have h := hδ μ hμ
    unfold IsLMStep at h
    simp only [G, ContinuousLinearMap.comp_apply]
    rw [← h]; abel
  have hG : Tendsto (fun μ => G (δ μ)) atTop (𝓝 0) := by
    have h := (G.continuous.tendsto 0).comp (lmStep_tendsto_zero hδ)
    rw [map_zero] at h
    exact h
  have hlim := (tendsto_const_nhds (x := -(ContinuousLinearMap.adjoint J) r)).sub hG
  rw [sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with μ hμ
  exact (heq μ hμ).symm

/-- `μ = 0` with a square invertible `J`: the Levenberg–Marquardt (Gauss–Newton) step is the
Newton step `−J⁻¹ r`. -/
@[powerlib_foundation] theorem lmStep_zero_eq_newton {J : E →L[ℝ] E} (hJ : IsUnit J) (r δ : E)
    (h : IsLMStep J r 0 δ) : δ = -Ring.inverse J r := by
  unfold IsLMStep at h
  rw [zero_smul, add_zero, ← map_neg] at h
  have hadj : Function.Injective (ContinuousLinearMap.adjoint J) := by
    obtain ⟨u, rfl⟩ := hJ
    intro a b hab
    have hu : (ContinuousLinearMap.adjoint (↑u⁻¹ : E →L[ℝ] E)).comp
        (ContinuousLinearMap.adjoint (↑u : E →L[ℝ] E)) = ContinuousLinearMap.id ℝ E := by
      rw [← ContinuousLinearMap.adjoint_comp]
      have : (↑u : E →L[ℝ] E).comp (↑u⁻¹ : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := by
        have h1 := u.mul_inv
        exact h1
      rw [this, ContinuousLinearMap.adjoint_id]
    have := congrArg (ContinuousLinearMap.adjoint (↑u⁻¹ : E →L[ℝ] E)) hab
    simpa [← ContinuousLinearMap.comp_apply, hu] using this
  have hJδ : J δ = -r := hadj h
  have hid : Ring.inverse J (J δ) = δ := by
    have h := congrArg (fun T : E →L[ℝ] E => T δ) (Ring.inverse_mul_cancel _ hJ)
    simpa using h
  rw [← hid, hJδ, map_neg]

end LM

end powerlib.Numerics
