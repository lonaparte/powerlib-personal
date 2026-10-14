import theorem.Numerics.StabilityFunctions

/-! # Explicit Runge–Kutta methods: polynomial stability function, no A-stability

The stability function of an explicit Runge–Kutta method is a polynomial, hence no consistent
explicit Runge–Kutta method is A-stable.

Model boundary.
* An `s`-stage explicit Runge–Kutta tableau (`a` strictly lower triangular, weights `b`) applied
  to an arbitrary autonomous field with fixed step `h`; the stage equations are a predicate
  (`IsStages`), so the step is defined from the method itself. For the Dahlquist test field the
  stage vector exists, is unique, and equals `λ x pᵢ(hλ)` for explicit stage polynomials `pᵢ`,
  which yields the stability polynomial `R(z) = 1 + z Σ bᵢ pᵢ(z)` with `R(0) = 1` and
  `R'(0) = Σ bᵢ`.

Source: work-sync theory/T-numerical-integration.md §1.4, §1.7 ("显式 RK 的稳定域有限——没有
显式 A-stable 单步法"), §2.4.

Results.
* `ExplicitRK.trajectory_testEquation` — every RK trajectory of `ẋ = λ x` satisfies
  `x_{n+1} = R(hλ) x_n`.
* `ExplicitRK.not_aStable` — if `Σ bᵢ = 1`, `R` is not A-stable.
* `ExplicitRK.exists_stable_mode_divergent` — there is a decaying test mode (`Re λ < 0`) for
  which every nonzero numerical trajectory with `h = 1` diverges.

Not formalized.
* Dahlquist and Butcher order barriers.
-/

noncomputable section
namespace powerlib.Numerics
open Polynomial Filter
open scoped Topology

/-- An `s`-stage explicit Runge–Kutta tableau. -/
structure ExplicitRK (s : ℕ) where
  a : Fin s → Fin s → ℝ
  b : Fin s → ℝ
  lower : ∀ i j, i ≤ j → a i j = 0

namespace ExplicitRK

variable {s : ℕ} (M : ExplicitRK s)

section General

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Stage equations `kᵢ = f (x + h Σⱼ aᵢⱼ kⱼ)`. -/
def IsStages (f : E → E) (h : ℝ) (x : E) (k : Fin s → E) : Prop :=
  ∀ i, k i = f (x + h • ∑ j, M.a i j • k j)

/-- The RK update from stage values. -/
def update (h : ℝ) (x : E) (k : Fin s → E) : E := x + h • ∑ i, M.b i • k i

/-- A trajectory of the explicit Runge–Kutta method. -/
def IsTrajectory (f : E → E) (h : ℝ) (x : ℕ → E) : Prop :=
  ∀ n, ∃ k, M.IsStages f h (x n) k ∧ x (n + 1) = M.update h (x n) k

end General

/-- Stage polynomials: `pᵢ = 1 + Σ_{j<i} aᵢⱼ X pⱼ`. -/
def stagePoly (i : Fin s) : ℂ[X] :=
  1 + ∑ j : Fin s, if hj : j < i then C (M.a i j : ℂ) * X * stagePoly j else 0
termination_by i.val
decreasing_by exact hj

/-- The stability polynomial `R = 1 + X Σᵢ bᵢ pᵢ`. -/
def stabilityPoly : ℂ[X] := 1 + X * ∑ i, C (M.b i : ℂ) * M.stagePoly i

@[powerlib_foundation] private lemma stage_rhs (lam : ℂ) (h : ℝ) (x : ℂ) (k : Fin s → ℂ)
    (i : Fin s) (hlt : ∀ j, j < i → k j = lam * x * (M.stagePoly j).eval (h * lam)) :
    testField lam (x + h • ∑ j, M.a i j • k j) = lam * x * (M.stagePoly i).eval (h * lam) := by
  have hsum : ∑ j, M.a i j • k j =
      ∑ j : Fin s, if j < i then (M.a i j : ℂ) * (lam * x * (M.stagePoly j).eval (h * lam))
        else 0 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · rw [hlt j hj, Complex.real_smul]
    · rw [M.lower i j (not_lt.mp hj), zero_smul]
  rw [hsum, stagePoly, testField, Complex.real_smul]
  simp only [eval_add, eval_one, eval_finsetSum]
  rw [mul_add, mul_add, mul_one]
  simp only [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · simp; ring
  · simp

/-- For the test field, every stage vector is `kᵢ = λ x pᵢ(hλ)`. -/
@[powerlib_foundation] theorem stages_testEquation (lam : ℂ) (h : ℝ) (x : ℂ) (k : Fin s → ℂ)
    (hk : M.IsStages (testField lam) h x k) (i : Fin s) :
    k i = lam * x * (M.stagePoly i).eval (h * lam) := by
  induction' hm : i.val using Nat.strong_induction_on with m ih generalizing i
  rw [hk i]
  apply M.stage_rhs lam h x k i
  intro j hj
  exact ih j.val (hm ▸ hj) j rfl

/-- For the test field the stage equations are solvable. -/
@[powerlib_foundation] theorem stages_testEquation_exist (lam : ℂ) (h : ℝ) (x : ℂ) :
    M.IsStages (testField lam) h x (fun i => lam * x * (M.stagePoly i).eval (h * lam)) :=
  fun i => (M.stage_rhs lam h x _ i (fun _ _ => rfl)).symm

/-- One RK step on the test equation multiplies by the stability polynomial. -/
@[powerlib_foundation] theorem update_testEquation (lam : ℂ) (h : ℝ) (x : ℂ) (k : Fin s → ℂ)
    (hk : M.IsStages (testField lam) h x k) :
    M.update h x k = M.stabilityPoly.eval (h * lam) * x := by
  simp only [update, stabilityPoly, M.stages_testEquation lam h x k hk, Complex.real_smul,
    eval_add, eval_one, eval_mul, eval_X, eval_finsetSum, eval_C, Finset.mul_sum]
  rw [add_mul, one_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

@[powerlib_foundation] theorem trajectory_testEquation (lam : ℂ) (h : ℝ) (x : ℕ → ℂ)
    (hx : M.IsTrajectory (testField lam) h x) (n : ℕ) :
    x (n + 1) = M.stabilityPoly.eval (h * lam) * x n := by
  obtain ⟨k, hk, hn⟩ := hx n
  rw [hn, M.update_testEquation lam h (x n) k hk]

@[powerlib_foundation] theorem stagePoly_eval_zero (i : Fin s) : (M.stagePoly i).eval 0 = 1 := by
  rw [stagePoly]
  simp only [eval_add, eval_one, eval_finsetSum]
  rw [Finset.sum_eq_zero]
  · ring
  · intro j _
    split_ifs <;> simp

@[powerlib_foundation] theorem stabilityPoly_coeff_one :
    M.stabilityPoly.coeff 1 = ∑ i, (M.b i : ℂ) := by
  rw [stabilityPoly, coeff_add, coeff_one, coeff_X_mul, coeff_zero_eq_eval_zero]
  simp only [eval_finsetSum, eval_mul, eval_C, M.stagePoly_eval_zero, mul_one]
  simp

/-- No consistent explicit Runge–Kutta method is A-stable. -/
@[powerlib_foundation] theorem not_aStable (hcons : ∑ i, M.b i = 1) :
    ¬ AStable (fun z => M.stabilityPoly.eval z) := by
  apply polynomial_not_aStable
  rw [stabilityPoly_coeff_one]
  exact_mod_cast hcons

/-- A consistent explicit Runge–Kutta method with `h = 1` diverges on some decaying test
mode: every nonzero numerical trajectory has `‖x n‖ → ∞` although `Re λ < 0`. -/
@[powerlib_foundation] theorem exists_stable_mode_divergent (hcons : ∑ i, M.b i = 1) :
    ∃ lam : ℂ, lam.re < 0 ∧ ∀ x : ℕ → ℂ, M.IsTrajectory (testField lam) 1 x → x 0 ≠ 0 →
      Tendsto (fun n => ‖x n‖) atTop atTop := by
  have hdeg : 0 < M.stabilityPoly.degree := by
    by_contra hle
    have h1 := M.stabilityPoly_coeff_one
    rw [Polynomial.eq_C_of_degree_le_zero (not_lt.mp hle), coeff_C] at h1
    have : (∑ i, (M.b i : ℂ)) = 1 := by exact_mod_cast hcons
    rw [this] at h1
    simp at h1
  obtain ⟨t, ht0, ht⟩ := polynomial_exists_neg_real_one_lt M.stabilityPoly hdeg
  refine ⟨((-t : ℝ) : ℂ), by simp; linarith, fun x hx h0 => ?_⟩
  have hnorm : ∀ n, ‖x n‖ = ‖M.stabilityPoly.eval ((-t : ℝ) : ℂ)‖ ^ n * ‖x 0‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [M.trajectory_testEquation _ 1 x hx n, norm_mul, ih, pow_succ]
      push_cast
      ring_nf
  exact ((tendsto_pow_atTop_atTop_of_one_lt ht).atTop_mul_const (norm_pos_iff.mpr h0)).congr
    fun n => (hnorm n).symm

end ExplicitRK

end powerlib.Numerics
