import theorem.Numerics.LinearSchemes

/-! # Local truncation errors of one-step schemes and first-order convergence of forward Euler

Local truncation errors of forward Euler, backward Euler and the trapezoidal rule with explicit
constants, and first-order global convergence of forward Euler.

Model boundary.
* A curve `x : ℝ → E` in a real normed space with an explicit chain of derivatives
  `x' = x₁, x₁' = x₂, …` on `[t, t + h]` and a uniform bound on the last derivative. When `x`
  solves `ẋ = f(x)`, `x₁ = f ∘ x` and the residuals below are exactly the residuals of the
  schemes in `LinearSchemes` evaluated on the exact solution.
* The sign of the BE coefficient is relative to the residual convention
  `τ = x(t_{n+1}) - Φ(x(t_n))` with the implicit update evaluated on the exact solution.

Source: work-sync theory/T-numerical-integration.md §1.1–§1.3 (LTE `±h²ẍ/2`, `-h³x‴/12`,
convergence order).

Results.
* `norm_le_of_hasDerivAt_le_pow` — if `φ 0 = 0` and `‖φ' s‖ ≤ M sᵐ` on `[0, h]` then
  `‖φ s‖ ≤ M s^(m+1)/(m+1)` (comparison with a boundary function; Mathlib
  `image_norm_le_of_norm_deriv_right_le_deriv_boundary`).
* `taylor_one_bound`, `taylor_two_bound`, `taylor_three_bound` — Taylor bounds of order one, two
  and three.
* `forwardEuler_lte` — `‖τ_FE - (h²/2) x₂(t)‖ ≤ M₃ h³/6`, `τ_FE = x(t+h) - x(t) - h x₁(t)`.
* `backwardEuler_lte` — `‖τ_BE + (h²/2) x₂(t)‖ ≤ (2/3) M₃ h³`,
  `τ_BE = x(t+h) - x(t) - h x₁(t+h)`.
* `trapezoidal_lte` — `‖τ_T + (h³/12) x₃(t)‖ ≤ M₄ h⁴/8`,
  `τ_T = x(t+h) - x(t) - (h/2)(x₁(t) + x₁(t+h))`.
* `forwardEuler_global_error` — for a `K`-Lipschitz field and an exact solution with
  `‖ẍ‖ ≤ M` on `[0, T]`, `T = N h`, every forward-Euler trajectory started at `x(0)` obeys
  `‖y_n - x(n h)‖ ≤ (M T / 2) e^{K T} h` for `n ≤ N` (first-order convergence; discrete
  Grönwall recursion `e_{n+1} ≤ (1 + hK) e_n + M h²/2`).
-/

noncomputable section
namespace powerlib.Numerics
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integrating a power bound on the derivative. -/
@[powerlib_foundation] theorem norm_le_of_hasDerivAt_le_pow {φ φ' : ℝ → E} {M h : ℝ} (m : ℕ)
    (hφ : ∀ s ∈ Icc 0 h, HasDerivAt φ (φ' s) s) (h0 : φ 0 = 0)
    (hb : ∀ s ∈ Icc 0 h, ‖φ' s‖ ≤ M * s ^ m) :
    ∀ s ∈ Icc 0 h, ‖φ s‖ ≤ M * s ^ (m + 1) / (m + 1) := by
  have hB : ∀ s, HasDerivAt (fun s : ℝ => M * s ^ (m + 1) / (m + 1)) (M * s ^ m) s := by
    intro s
    have := ((hasDerivAt_pow (m + 1) s).const_mul M).div_const ((m : ℝ) + 1)
    convert this using 1
    have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  exact image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun s hs => (hφ s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hφ s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (by simp [h0]) hB (fun s hs => hb s (Ico_subset_Icc_self hs))

@[powerlib_foundation] private lemma shift_mem {t h s : ℝ} (hs : s ∈ Icc 0 h) :
    t + s ∈ Icc t (t + h) := ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- First-order Taylor bound: `‖x(t+s) - x(t) - s x₁(t)‖ ≤ M s²/2`. -/
@[powerlib_foundation] theorem taylor_one_bound {x x₁ x₂ : ℝ → E} {t h M : ℝ}
    (hx : ∀ s ∈ Icc t (t + h), HasDerivAt x (x₁ s) s)
    (hx₁ : ∀ s ∈ Icc t (t + h), HasDerivAt x₁ (x₂ s) s)
    (hM : ∀ s ∈ Icc t (t + h), ‖x₂ s‖ ≤ M) :
    ∀ s ∈ Icc 0 h, ‖x (t + s) - x t - s • x₁ t‖ ≤ M * s ^ 2 / 2 := by
  have h1 := norm_le_of_hasDerivAt_le_pow (φ := fun s => x₁ (t + s) - x₁ t)
    (φ' := fun s => x₂ (t + s)) (M := M) (h := h) 0
    (fun s hs => ((hx₁ (t + s) (shift_mem hs)).comp_const_add t s).sub_const _)
    (by simp) (fun s hs => by simpa using hM (t + s) (shift_mem hs))
  have h2 := norm_le_of_hasDerivAt_le_pow (φ := fun s => x (t + s) - x t - s • x₁ t)
    (φ' := fun s => x₁ (t + s) - x₁ t) (M := M) (h := h) 1
    (fun s hs => by
      have := (((hx (t + s) (shift_mem hs)).comp_const_add t s).sub_const (x t)).sub
        ((hasDerivAt_id s).smul_const (x₁ t))
      exact HasDerivAt.congr_deriv (f := fun s => x (t + s) - x t - s • x₁ t) this (by simp))
    (by simp) (fun s hs => by simpa using h1 s hs)
  intro s hs
  calc _ ≤ M * s ^ (1 + 1) / ((1 : ℕ) + 1) := h2 s hs
    _ = M * s ^ 2 / 2 := by norm_num

/-- Second-order Taylor bound. -/
@[powerlib_foundation] theorem taylor_two_bound {x x₁ x₂ x₃ : ℝ → E} {t h M : ℝ}
    (hx : ∀ s ∈ Icc t (t + h), HasDerivAt x (x₁ s) s)
    (hx₁ : ∀ s ∈ Icc t (t + h), HasDerivAt x₁ (x₂ s) s)
    (hx₂ : ∀ s ∈ Icc t (t + h), HasDerivAt x₂ (x₃ s) s)
    (hM : ∀ s ∈ Icc t (t + h), ‖x₃ s‖ ≤ M) :
    ∀ s ∈ Icc 0 h, ‖x (t + s) - x t - s • x₁ t - (s ^ 2 / 2) • x₂ t‖ ≤ M * s ^ 3 / 6 := by
  have h1 := taylor_one_bound hx₁ hx₂ hM
  have h2 := norm_le_of_hasDerivAt_le_pow
    (φ := fun s => x (t + s) - x t - s • x₁ t - (s ^ 2 / 2) • x₂ t)
    (φ' := fun s => x₁ (t + s) - x₁ t - s • x₂ t) (M := M / 2) (h := h) 2
    (fun s hs => by
      have hp : HasDerivAt (fun s : ℝ => s ^ 2 / 2) s s := by
        have := (hasDerivAt_pow 2 s).div_const 2
        convert this using 1; ring
      have := ((((hx (t + s) (shift_mem hs)).comp_const_add t s).sub_const (x t)).sub
        ((hasDerivAt_id s).smul_const (x₁ t))).sub (hp.smul_const (x₂ t))
      exact HasDerivAt.congr_deriv
        (f := fun s => x (t + s) - x t - s • x₁ t - (s ^ 2 / 2) • x₂ t) this (by simp))
    (by simp) (fun s hs => by
      have := h1 s hs
      calc _ ≤ M * s ^ 2 / 2 := this
        _ = M / 2 * s ^ 2 := by ring)
  intro s hs
  have := h2 s hs
  calc _ ≤ M / 2 * s ^ (2 + 1) / ((2 : ℕ) + 1) := this
    _ = M * s ^ 3 / 6 := by norm_num; ring

/-- Third-order Taylor bound. -/
@[powerlib_foundation] theorem taylor_three_bound {x x₁ x₂ x₃ x₄ : ℝ → E} {t h M : ℝ}
    (hx : ∀ s ∈ Icc t (t + h), HasDerivAt x (x₁ s) s)
    (hx₁ : ∀ s ∈ Icc t (t + h), HasDerivAt x₁ (x₂ s) s)
    (hx₂ : ∀ s ∈ Icc t (t + h), HasDerivAt x₂ (x₃ s) s)
    (hx₃ : ∀ s ∈ Icc t (t + h), HasDerivAt x₃ (x₄ s) s)
    (hM : ∀ s ∈ Icc t (t + h), ‖x₄ s‖ ≤ M) :
    ∀ s ∈ Icc 0 h, ‖x (t + s) - x t - s • x₁ t - (s ^ 2 / 2) • x₂ t - (s ^ 3 / 6) • x₃ t‖ ≤
      M * s ^ 4 / 24 := by
  have h1 := taylor_two_bound hx₁ hx₂ hx₃ hM
  have h2 := norm_le_of_hasDerivAt_le_pow
    (φ := fun s => x (t + s) - x t - s • x₁ t - (s ^ 2 / 2) • x₂ t - (s ^ 3 / 6) • x₃ t)
    (φ' := fun s => x₁ (t + s) - x₁ t - s • x₂ t - (s ^ 2 / 2) • x₃ t) (M := M / 6) (h := h) 3
    (fun s hs => by
      have hp2 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) s s := by
        have := (hasDerivAt_pow 2 s).div_const 2
        convert this using 1; ring
      have hp3 : HasDerivAt (fun s : ℝ => s ^ 3 / 6) (s ^ 2 / 2) s := by
        have := (hasDerivAt_pow 3 s).div_const 6
        convert this using 1; ring
      have := (((((hx (t + s) (shift_mem hs)).comp_const_add t s).sub_const (x t)).sub
        ((hasDerivAt_id s).smul_const (x₁ t))).sub (hp2.smul_const (x₂ t))).sub
        (hp3.smul_const (x₃ t))
      exact HasDerivAt.congr_deriv
        (f := fun s => x (t + s) - x t - s • x₁ t - (s ^ 2 / 2) • x₂ t - (s ^ 3 / 6) • x₃ t)
        this (by simp))
    (by simp) (fun s hs => by
      have := h1 s hs
      calc _ ≤ M * s ^ 3 / 6 := this
        _ = M / 6 * s ^ 3 := by ring)
  intro s hs
  have := h2 s hs
  calc _ ≤ M / 6 * s ^ (3 + 1) / ((3 : ℕ) + 1) := this
    _ = M * s ^ 4 / 24 := by norm_num; ring

@[powerlib_foundation] private lemma right_mem {h : ℝ} (hh : 0 ≤ h) : h ∈ Icc (0 : ℝ) h :=
  ⟨hh, le_rfl⟩

/-- Forward Euler local truncation error: `τ_FE = (h²/2) x₂(t) + O(h³)`. -/
@[powerlib_foundation] theorem forwardEuler_lte {x x₁ x₂ x₃ : ℝ → E} {t h M : ℝ} (hh : 0 ≤ h)
    (hx : ∀ s ∈ Icc t (t + h), HasDerivAt x (x₁ s) s)
    (hx₁ : ∀ s ∈ Icc t (t + h), HasDerivAt x₁ (x₂ s) s)
    (hx₂ : ∀ s ∈ Icc t (t + h), HasDerivAt x₂ (x₃ s) s)
    (hM : ∀ s ∈ Icc t (t + h), ‖x₃ s‖ ≤ M) :
    ‖(x (t + h) - x t - h • x₁ t) - (h ^ 2 / 2) • x₂ t‖ ≤ M * h ^ 3 / 6 :=
  taylor_two_bound hx hx₁ hx₂ hM h (right_mem hh)

/-- Backward Euler local truncation error: `τ_BE = -(h²/2) x₂(t) + O(h³)`. -/
@[powerlib_foundation] theorem backwardEuler_lte {x x₁ x₂ x₃ : ℝ → E} {t h M : ℝ} (hh : 0 ≤ h)
    (hx : ∀ s ∈ Icc t (t + h), HasDerivAt x (x₁ s) s)
    (hx₁ : ∀ s ∈ Icc t (t + h), HasDerivAt x₁ (x₂ s) s)
    (hx₂ : ∀ s ∈ Icc t (t + h), HasDerivAt x₂ (x₃ s) s)
    (hM : ∀ s ∈ Icc t (t + h), ‖x₃ s‖ ≤ M) :
    ‖(x (t + h) - x t - h • x₁ (t + h)) + (h ^ 2 / 2) • x₂ t‖ ≤ 2 / 3 * M * h ^ 3 := by
  have hA := taylor_two_bound hx hx₁ hx₂ hM h (right_mem hh)
  have hB := taylor_one_bound hx₁ hx₂ hM h (right_mem hh)
  have heq : (x (t + h) - x t - h • x₁ (t + h)) + (h ^ 2 / 2) • x₂ t =
      (x (t + h) - x t - h • x₁ t - (h ^ 2 / 2) • x₂ t) - h • (x₁ (t + h) - x₁ t - h • x₂ t) := by
    simp only [smul_sub, smul_smul]
    module
  rw [heq]
  calc _ ≤ ‖x (t + h) - x t - h • x₁ t - (h ^ 2 / 2) • x₂ t‖ +
        ‖h • (x₁ (t + h) - x₁ t - h • x₂ t)‖ := norm_sub_le _ _
    _ ≤ M * h ^ 3 / 6 + h * (M * h ^ 2 / 2) := by
        rw [norm_smul, Real.norm_of_nonneg hh]
        exact add_le_add hA (mul_le_mul_of_nonneg_left hB hh)
    _ = 2 / 3 * M * h ^ 3 := by ring

/-- Trapezoidal local truncation error: `τ_T = -(h³/12) x₃(t) + O(h⁴)`. -/
@[powerlib_foundation] theorem trapezoidal_lte {x x₁ x₂ x₃ x₄ : ℝ → E} {t h M : ℝ} (hh : 0 ≤ h)
    (hx : ∀ s ∈ Icc t (t + h), HasDerivAt x (x₁ s) s)
    (hx₁ : ∀ s ∈ Icc t (t + h), HasDerivAt x₁ (x₂ s) s)
    (hx₂ : ∀ s ∈ Icc t (t + h), HasDerivAt x₂ (x₃ s) s)
    (hx₃ : ∀ s ∈ Icc t (t + h), HasDerivAt x₃ (x₄ s) s)
    (hM : ∀ s ∈ Icc t (t + h), ‖x₄ s‖ ≤ M) :
    ‖(x (t + h) - x t - (h / 2) • (x₁ t + x₁ (t + h))) + (h ^ 3 / 12) • x₃ t‖ ≤ M * h ^ 4 / 8 := by
  have hA := taylor_three_bound hx hx₁ hx₂ hx₃ hM h (right_mem hh)
  have hB := taylor_two_bound hx₁ hx₂ hx₃ hM h (right_mem hh)
  have heq : (x (t + h) - x t - (h / 2) • (x₁ t + x₁ (t + h))) + (h ^ 3 / 12) • x₃ t =
      (x (t + h) - x t - h • x₁ t - (h ^ 2 / 2) • x₂ t - (h ^ 3 / 6) • x₃ t) -
        (h / 2) • (x₁ (t + h) - x₁ t - h • x₂ t - (h ^ 2 / 2) • x₃ t) := by
    simp only [smul_sub, smul_add, smul_smul]
    module
  rw [heq]
  have hh2 : 0 ≤ h / 2 := by linarith
  calc _ ≤ ‖x (t + h) - x t - h • x₁ t - (h ^ 2 / 2) • x₂ t - (h ^ 3 / 6) • x₃ t‖ +
        ‖(h / 2) • (x₁ (t + h) - x₁ t - h • x₂ t - (h ^ 2 / 2) • x₃ t)‖ := norm_sub_le _ _
    _ ≤ M * h ^ 4 / 24 + h / 2 * (M * h ^ 3 / 6) := by
        rw [norm_smul, Real.norm_of_nonneg hh2]
        exact add_le_add hA (mul_le_mul_of_nonneg_left hB hh2)
    _ = M * h ^ 4 / 8 := by ring

/-- First-order global convergence of forward Euler. -/
@[powerlib_foundation] theorem forwardEuler_global_error {f : E → E} {K : NNReal}
    (hf : LipschitzWith K f) {x x₂ : ℝ → E} {M h : ℝ} (hh : 0 < h) (N : ℕ)
    (hx : ∀ s ∈ Icc 0 (N * h), HasDerivAt x (f (x s)) s)
    (hx₁ : ∀ s ∈ Icc 0 (N * h), HasDerivAt (fun r => f (x r)) (x₂ s) s)
    (hM : ∀ s ∈ Icc 0 (N * h), ‖x₂ s‖ ≤ M)
    {y : ℕ → E} (hy : IsForwardEulerTrajectory f h y) (h0 : y 0 = x 0) :
    ∀ n ≤ N, ‖y n - x (n * h)‖ ≤ M * (N * h) / 2 * Real.exp (K * (N * h)) * h := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, by positivity⟩)
  set q : ℝ := 1 + h * K with hq
  have hq1 : 1 ≤ q := by have : 0 ≤ h * K := by positivity
                         linarith
  -- local truncation error along the exact solution
  have hlte : ∀ n, n < N →
      ‖x ((n + 1 : ℕ) * h) - x (n * h) - h • f (x (n * h))‖ ≤ M * h ^ 2 / 2 := by
    intro n hn
    have hsub : Icc (n * h) (n * h + h) ⊆ Icc 0 (N * h) := by
      intro s hs
      refine ⟨le_trans (by positivity) hs.1, le_trans hs.2 ?_⟩
      have : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
      nlinarith
    have := taylor_one_bound (t := n * h) (h := h) (x₁ := fun r => f (x r))
      (fun s hs => hx s (hsub hs)) (fun s hs => hx₁ s (hsub hs)) (fun s hs => hM s (hsub hs))
      h ⟨hh.le, le_rfl⟩
    have he : ((n + 1 : ℕ) : ℝ) * h = n * h + h := by push_cast; ring
    rw [he]
    exact this
  -- discrete Grönwall recursion
  have hrec : ∀ n ≤ N, ‖y n - x (n * h)‖ ≤ n * (M * h ^ 2 / 2) * q ^ n := by
    intro n
    induction n with
    | zero => intro _; simp [h0]
    | succ n ih =>
      intro hn
      have ihn := ih (Nat.le_of_succ_le hn)
      have hstep : y (n + 1) - x ((n + 1 : ℕ) * h) =
          (y n - x (n * h)) + h • (f (y n) - f (x (n * h))) -
            (x ((n + 1 : ℕ) * h) - x (n * h) - h • f (x (n * h))) := by
        rw [hy n, smul_sub]; abel
      have hlip : ‖f (y n) - f (x (n * h))‖ ≤ K * ‖y n - x (n * h)‖ := by
        simpa [dist_eq_norm] using hf.dist_le_mul (y n) (x (n * h))
      have hqn : 1 ≤ q ^ n := one_le_pow₀ hq1
      have hτ : 0 ≤ M * h ^ 2 / 2 := by positivity
      rw [hstep]
      calc _ ≤ ‖(y n - x (n * h)) + h • (f (y n) - f (x (n * h)))‖ +
            ‖x ((n + 1 : ℕ) * h) - x (n * h) - h • f (x (n * h))‖ := norm_sub_le _ _
        _ ≤ (‖y n - x (n * h)‖ + h * (K * ‖y n - x (n * h)‖)) + M * h ^ 2 / 2 := by
            gcongr
            · refine (norm_add_le _ _).trans ?_
              rw [norm_smul, Real.norm_of_nonneg hh.le]
              gcongr
            · exact hlte n (Nat.lt_of_succ_le hn)
        _ = q * ‖y n - x (n * h)‖ + M * h ^ 2 / 2 := by rw [hq]; ring
        _ ≤ q * (n * (M * h ^ 2 / 2) * q ^ n) + M * h ^ 2 / 2 := by
            gcongr
        _ ≤ ((n + 1 : ℕ) : ℝ) * (M * h ^ 2 / 2) * q ^ (n + 1) := by
            push_cast
            have : M * h ^ 2 / 2 ≤ M * h ^ 2 / 2 * q ^ (n + 1) :=
              le_mul_of_one_le_right hτ (one_le_pow₀ hq1)
            have e : q * (↑n * (M * h ^ 2 / 2) * q ^ n) = ↑n * (M * h ^ 2 / 2) * q ^ (n + 1) := by
              ring
            linarith [this, e]
  intro n hn
  have hqexp : q ^ n ≤ Real.exp (K * (N * h)) := by
    calc q ^ n ≤ Real.exp (h * K) ^ n := by
          gcongr
          rw [hq, add_comm]; exact Real.add_one_le_exp _
      _ = Real.exp (n * (h * K)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (K * (N * h)) := by
          apply Real.exp_le_exp.mpr
          have : (n : ℝ) ≤ N := by exact_mod_cast hn
          have hK : (0 : ℝ) ≤ K := K.2
          nlinarith [mul_nonneg hh.le hK]
  have hnN : (n : ℝ) * h ≤ N * h := by
    have : (n : ℝ) ≤ N := by exact_mod_cast hn
    nlinarith
  calc ‖y n - x (n * h)‖ ≤ n * (M * h ^ 2 / 2) * q ^ n := hrec n hn
    _ = M * (n * h) / 2 * q ^ n * h := by ring
    _ ≤ M * (N * h) / 2 * Real.exp (K * (N * h)) * h := by
        gcongr

end powerlib.Numerics
