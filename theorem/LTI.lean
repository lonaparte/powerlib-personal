import dependencies.Mathlib
import theorem.Attributes
import theorem.generated.LTIFoundation

/-! Arbitrary finite-dimensional continuous-time autonomous LTI systems.
The submitted matrix is the vector field in the submitted state order. External
input perturbations are zero; any controller dynamics must already be included
in the matrix. This module makes no claim about an unprovided physical model,
nonlinear remainder, delay, switching law, or differential-algebraic system.

`sqNorm` is the squared Euclidean norm, expressed without square roots.
`ExponentiallyStable` bounds every solution, not just a certificate expression.
Global solutions are constructed independently by the operator exponential.
-/
noncomputable section
namespace powerlib.LTI
open Matrix
open scoped BigOperators
open scoped Topology

abbrev State (n : ℕ) := Fin n → ℝ

@[ext] structure Model (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ

variable {n : ℕ}

def Model.field (m : Model n) (x : State n) : State n := generated.linearField m.A x

@[simp, powerlib_foundation] theorem Model.zero_equilibrium (m : Model n) :
    m.field 0 = 0 := by simp [Model.field]

@[powerlib_foundation, aesop safe apply] theorem Model.perturbation (m : Model n) (x dx : State n) :
    m.field (x + dx) - m.field x = m.field dx := by
  simp [Model.field, Matrix.mulVec_add]

def Model.operator (m : Model n) : State n →L[ℝ] State n :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' m.A)

@[simp, powerlib_foundation] theorem Model.operator_apply (m : Model n) (x : State n) :
    m.operator x = m.field x := rfl

def sqNorm (x : State n) : ℝ := ∑ i, x i ^ 2

def euclidean (x : State n) : PiLp 2 (fun _ : Fin n => ℝ) :=
  (WithLp.equiv 2 (State n)).symm x

@[powerlib_foundation, aesop safe apply] theorem sqNorm_eq_norm_sq (x : State n) :
    sqNorm x = ‖euclidean x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [sqNorm, euclidean, Real.norm_eq_abs, sq_abs]

def energy (P : Matrix (Fin n) (Fin n) ℝ) (x : State n) : ℝ :=
  dotProduct x (P.mulVec x)

def IsTrajectory (m : Model n) (x : ℝ → State n) : Prop :=
  ∀ t, HasDerivAt x (m.field (x t)) t

def response (m : Model n) (initial : State n) (t : ℝ) : State n :=
  (NormedSpace.exp (t • m.operator)) initial

@[simp, powerlib_domain] theorem response_initial (m : Model n) (initial : State n) :
    response m initial 0 = initial := by
  simp [response]

@[powerlib_domain, aesop safe apply] theorem response_solves (m : Model n) (initial : State n) :
    IsTrajectory m (response m initial) := by
  intro t
  have h := (hasDerivAt_exp_smul_const' m.operator t).clm_apply
    (hasDerivAt_const t initial)
  simpa [response, mul_apply_eq_comp] using! h

@[powerlib_domain, aesop safe apply] theorem trajectory_exists (m : Model n) (initial : State n) :
    ∃ x, IsTrajectory m x ∧ x 0 = initial :=
  ⟨response m initial, response_solves m initial, response_initial m initial⟩

/-- Standard Euclidean-norm exponential decay of every global solution. -/
def ExponentiallyStable (m : Model n) : Prop :=
  ∃ K > 0, ∃ rate > 0, ∀ x, IsTrajectory m x → ∀ t, 0 ≤ t →
    ‖euclidean (x t)‖ ≤ K * Real.exp (-(rate * t)) * ‖euclidean (x 0)‖

/-- Exact, model-indexed certificate. The bounds have semantic meaning for all
states; the untrusted synthesizer proves them by rational sums of squares. -/
structure Accepted (m : Model n) where
  P : Matrix (Fin n) (Fin n) ℝ
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  symmetric : P.transpose = P
  lower_bound : ∀ x, lower * sqNorm x ≤ energy P x
  upper_bound : ∀ x, energy P x ≤ upper * sqNorm x
  lyapunov : m.A.transpose * P + P * m.A = -1

@[powerlib_foundation, aesop safe apply] theorem sqNorm_nonneg (x : State n) : 0 ≤ sqNorm x :=
  Finset.sum_nonneg fun i _ => sq_nonneg (x i)

@[simp, powerlib_foundation] theorem sqNorm_zero : sqNorm (0 : State n) = 0 := by
  simp [sqNorm]

@[simp, powerlib_foundation] theorem sqNorm_eq_zero_iff (x : State n) : sqNorm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    have hi : x i ^ 2 ≤ sqNorm x :=
      Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    have hz : x i ^ 2 = 0 := le_antisymm (by simpa [h] using hi) (sq_nonneg _)
    exact sq_eq_zero_iff.mp hz
  · rintro rfl
    exact sqNorm_zero

@[powerlib_foundation, aesop safe apply] theorem energy_derivative {m : Model n} (P : Matrix (Fin n) (Fin n) ℝ)
    {x : ℝ → State n} (hx : IsTrajectory m x) (t : ℝ) :
    HasDerivAt (fun s => energy P (x s))
      (dotProduct (m.field (x t)) (P.mulVec (x t)) +
       dotProduct (x t) (P.mulVec (m.field (x t)))) t := by
  have hi := fun i => hasDerivAt_pi.mp (hx t) i
  have hp : ∀ i, HasDerivAt (fun s => P.mulVec (x s) i)
      (P.mulVec (m.field (x t)) i) t := by
    intro i
    simpa only [Matrix.mulVec, dotProduct] using!
      (HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (hi j).const_mul (P i j))
  simpa [energy, dotProduct, Pi.mul_apply, Finset.sum_add_distrib] using!
    (HasDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) => (hi i).mul (hp i))

@[powerlib_foundation, aesop safe apply] theorem lyapunov_dissipation {m : Model n} (c : Accepted m) (x : State n) :
    dotProduct (m.field x) (c.P.mulVec x) +
      dotProduct x (c.P.mulVec (m.field x)) = -sqNorm x := by
  calc
    _ = energy (m.A.transpose * c.P + c.P * m.A) x := by
      simp only [energy, Model.field, generated.linearField_spec, Matrix.add_mulVec,
        dotProduct_add, ← Matrix.mulVec_mulVec]
      rw [Matrix.dotProduct_mulVec x m.A.transpose (c.P.mulVec x), Matrix.vecMul_transpose]
    _ = energy (-1) x := congrArg (fun Q => energy Q x) c.lyapunov
    _ = -sqNorm x := by
      simp [energy, Matrix.neg_mulVec, sqNorm, dotProduct, pow_two]

@[powerlib_domain, aesop safe apply] theorem Accepted.energy_derivative {m : Model n} (c : Accepted m)
    {x : ℝ → State n} (hx : IsTrajectory m x) (t : ℝ) :
    HasDerivAt (fun s => energy c.P (x s)) (-sqNorm (x t)) t := by
  simpa only [lyapunov_dissipation c] using powerlib.LTI.energy_derivative c.P hx t

@[powerlib_domain, aesop safe apply] theorem Accepted.energy_decay {m : Model n} (c : Accepted m)
    {x : ℝ → State n} (hx : IsTrajectory m x) (t : ℝ) (ht : 0 ≤ t) :
    energy c.P (x t) ≤ Real.exp (-(t / c.upper)) * energy c.P (x 0) := by
  let F := fun s => Real.exp (s / c.upper) * energy c.P (x s)
  have hd : ∀ s, HasDerivAt F
      (Real.exp (s / c.upper) * (energy c.P (x s) / c.upper - sqNorm (x s))) s := by
    intro s
    convert! (((hasDerivAt_id s).div_const c.upper).exp).mul (c.energy_derivative hx s) using 1
    dsimp [F]
    ring
  have hmono : Antitone F := antitone_of_hasDerivAt_nonpos hd (by
    intro s
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    exact sub_nonpos.mpr ((div_le_iff₀ c.upper_pos).mpr
      (by simpa [mul_comm] using c.upper_bound (x s))))
  have h := hmono ht
  dsimp [F] at h
  simp only [zero_div, Real.exp_zero, one_mul] at h
  have h' := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(t / c.upper))).le
  simpa [← mul_assoc, ← Real.exp_add] using h'

@[powerlib_domain, aesop safe apply] theorem Accepted.decay_bound {m : Model n} (c : Accepted m)
    {x : ℝ → State n} (hx : IsTrajectory m x) (t : ℝ) (ht : 0 ≤ t) :
    sqNorm (x t) ≤ (c.upper / c.lower) * Real.exp (-(t / c.upper)) * sqNorm (x 0) := by
  have h := (c.lower_bound (x t)).trans ((c.energy_decay hx t ht).trans
    (mul_le_mul_of_nonneg_left (c.upper_bound (x 0)) (Real.exp_pos _).le))
  calc
    _ ≤ (Real.exp (-(t / c.upper)) * (c.upper * sqNorm (x 0))) / c.lower :=
      (le_div_iff₀ c.lower_pos).mpr (by simpa [mul_comm] using h)
    _ = _ := by ring

@[powerlib_domain, aesop safe apply] theorem Accepted.norm_bound {m : Model n} (c : Accepted m)
    {x : ℝ → State n} (hx : IsTrajectory m x) (t : ℝ) (ht : 0 ≤ t) :
    ‖euclidean (x t)‖ ≤ Real.sqrt (c.upper / c.lower) *
      Real.exp (-(t / c.upper) / 2) * ‖euclidean (x 0)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ (c.upper / c.lower) * Real.exp (-(t / c.upper)) * ‖euclidean (x 0)‖ ^ 2 := by
      simpa only [sqNorm_eq_norm_sq] using c.decay_bound hx t ht
    _ = _ := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (div_pos c.upper_pos c.lower_pos).le,
        ← Real.exp_nat_mul]
      congr 2
      ring_nf

@[powerlib_domain, aesop safe apply] theorem Accepted.exponentially_stable {m : Model n}
    (c : Accepted m) : ExponentiallyStable m := by
  refine ⟨Real.sqrt (c.upper / c.lower), Real.sqrt_pos.2 (div_pos c.upper_pos c.lower_pos),
    1 / (2 * c.upper), div_pos zero_lt_one (mul_pos (by norm_num) c.upper_pos), ?_⟩
  intro x hx t ht
  convert! c.norm_bound hx t ht using 1
  congr 2
  ring_nf

@[powerlib_domain, aesop safe apply] theorem Accepted.response_bound {m : Model n}
    (c : Accepted m) (initial : State n) (t : ℝ) (ht : 0 ≤ t) :
    sqNorm (response m initial t) ≤
      (c.upper / c.lower) * Real.exp (-(t / c.upper)) * sqNorm initial := by
  simpa using c.decay_bound (response_solves m initial) t ht

-- A broad equality rule needs backtracking. Aesop's "unsafe" search category
-- still produces an ordinary kernel-checked proof; it is not a proof escape.
@[powerlib_domain, aesop unsafe 80% apply] theorem Accepted.trajectory_unique {m : Model n} (c : Accepted m)
    {x y : ℝ → State n} (hx : IsTrajectory m x) (hy : IsTrajectory m y)
    (h0 : x 0 = y 0) (t : ℝ) (ht : 0 ≤ t) : x t = y t := by
  have hd : IsTrajectory m (fun s => x s - y s) := by
    intro s
    simpa only [Model.field, generated.linearField_spec, Matrix.mulVec_sub] using!
      (hx s).sub (hy s)
  have h := c.decay_bound hd t ht
  simp only [h0, sub_self, sqNorm_zero, mul_zero] at h
  exact sub_eq_zero.mp ((sqNorm_eq_zero_iff _).mp (le_antisymm h (sqNorm_nonneg _)))

@[powerlib_domain, aesop safe apply] theorem Accepted.response_unique {m : Model n} (c : Accepted m)
    {x : ℝ → State n} (hx : IsTrajectory m x) (t : ℝ) (ht : 0 ≤ t) :
    x t = response m (x 0) t :=
  c.trajectory_unique hx (response_solves m (x 0)) (by simp) t ht

@[powerlib_domain, aesop norm forward (immediate := [c, hx])]
theorem Accepted.sqNorm_tendsto_zero {m : Model n} (c : Accepted m)
    {x : ℝ → State n} (hx : IsTrajectory m x) :
    Filter.Tendsto (fun t => sqNorm (x t)) Filter.atTop (𝓝 0) := by
  have he : Filter.Tendsto (fun t : ℝ => Real.exp (-(t / c.upper)))
      Filter.atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.tendsto_id.atTop_div_const c.upper_pos)
  have hb := (he.const_mul (c.upper / c.lower)).mul_const (sqNorm (x 0))
  simp only [mul_zero, zero_mul] at hb
  exact squeeze_zero' (Filter.Eventually.of_forall fun t => sqNorm_nonneg (x t))
    (Filter.eventually_atTop.2 ⟨0, fun t ht => c.decay_bound hx t ht⟩) hb

end powerlib.LTI
