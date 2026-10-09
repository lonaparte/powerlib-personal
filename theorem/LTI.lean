import dependencies.Mathlib
import dependencies.LeanForControl
import theorem.Attributes
import theorem.generated.LTIFoundation

/-! Finite-dimensional continuous-time LTI systems.

`Model` is the input-state-output realization `(A, B, C, D)`. `AutonomousModel`
is the zero-input state dynamics used by trajectory stability results. The
submitted matrices use the submitted state and port orders. Any controller
dynamics must already be included in the model. This module makes no claim
about an unprovided physical model, nonlinear remainder, delay, switching law,
or differential-algebraic system.

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

@[ext] structure AutonomousModel (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ

@[ext] structure Model (ι κ : Type*) where
  A : Matrix ι ι ℝ
  B : Matrix ι κ ℝ
  C : Matrix κ ι ℝ
  D : Matrix κ κ ℝ

variable {n : ℕ}

def AutonomousModel.field (m : AutonomousModel n) (x : State n) : State n :=
  generated.linearField m.A x

def Model.field {ι κ : Type*} [Fintype ι] [Fintype κ]
    (m : Model ι κ) (x : ι → ℝ) (u : κ → ℝ) : ι → ℝ :=
  m.A.mulVec x + m.B.mulVec u

def Model.output {ι κ : Type*} [Fintype ι] [Fintype κ]
    (m : Model ι κ) (x : ι → ℝ) (u : κ → ℝ) : κ → ℝ :=
  m.C.mulVec x + m.D.mulVec u

def Model.autonomous {κ : Type*} (m : Model (Fin n) κ) : AutonomousModel n :=
  ⟨m.A⟩

@[simp, powerlib_foundation] theorem AutonomousModel.zero_equilibrium (m : AutonomousModel n) :
    m.field 0 = 0 := by simp [AutonomousModel.field]

@[powerlib_foundation, aesop safe apply] theorem AutonomousModel.perturbation
    (m : AutonomousModel n) (x dx : State n) :
    m.field (x + dx) - m.field x = m.field dx := by
  simp [AutonomousModel.field, Matrix.mulVec_add]

def AutonomousModel.operator (m : AutonomousModel n) : State n →L[ℝ] State n :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' m.A)

@[simp, powerlib_foundation] theorem AutonomousModel.operator_apply
    (m : AutonomousModel n) (x : State n) :
    m.operator x = m.field x := rfl

def sqNorm (x : State n) : ℝ := ∑ i, x i ^ 2

def euclidean (x : State n) : PiLp 2 (fun _ : Fin n => ℝ) :=
  (WithLp.equiv 2 (State n)).symm x

@[powerlib_foundation, aesop safe apply] theorem sqNorm_eq_norm_sq (x : State n) :
    sqNorm x = ‖euclidean x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [sqNorm, euclidean, Real.norm_eq_abs, sq_abs]

def energy {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  dotProduct x (P.mulVec x)

def IsTrajectory (m : AutonomousModel n) (x : ℝ → State n) : Prop :=
  ∀ t, HasDerivAt x (m.field (x t)) t

def response (m : AutonomousModel n) (initial : State n) (t : ℝ) : State n :=
  (NormedSpace.exp (t • m.operator)) initial

@[simp, powerlib_foundation] theorem response_initial (m : AutonomousModel n) (initial : State n) :
    response m initial 0 = initial := by
  simp [response]

@[powerlib_domain, aesop safe apply] theorem response_solves (m : AutonomousModel n) (initial : State n) :
    IsTrajectory m (response m initial) := by
  intro t
  have h := (hasDerivAt_exp_smul_const' m.operator t).clm_apply
    (hasDerivAt_const t initial)
  simpa [response, mul_apply_eq_comp] using! h

@[powerlib_domain, aesop safe apply] theorem trajectory_exists (m : AutonomousModel n) (initial : State n) :
    ∃ x, IsTrajectory m x ∧ x 0 = initial :=
  ⟨response m initial, response_solves m initial, response_initial m initial⟩

section ZeroInput

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

def Model.operator (m : Model ι κ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' m.A)

omit [Fintype κ] in
@[simp, powerlib_foundation] theorem Model.operator_apply (m : Model ι κ) (x : ι → ℝ) :
    m.operator x = m.A.mulVec x := rfl

@[powerlib_foundation] theorem Model.operator_field (m : Model ι κ) (x : ι → ℝ) :
    m.operator x = m.field x 0 := by
  simp [Model.field]

@[powerlib_foundation] theorem Model.field_lipschitz (m : Model ι κ) (u : κ → ℝ) :
    LipschitzWith ‖m.operator‖₊ (fun x => m.field x u) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  simpa only [Model.field, Model.operator_apply, add_sub_add_right_eq_sub] using
    (lipschitzWith_iff_norm_sub_le.mp m.operator.lipschitzWith x y)

def Model.response (m : Model ι κ) (initial : ι → ℝ) (t : ℝ) : ι → ℝ :=
  (NormedSpace.exp (t • m.operator)) initial

omit [Fintype κ] in
@[simp, powerlib_foundation] theorem Model.response_initial (m : Model ι κ) (initial : ι → ℝ) :
    m.response initial 0 = initial := by
  simp [Model.response, NormedSpace.exp_zero]

omit [Fintype κ] in
@[powerlib_domain, aesop safe apply (transparency! := default)] theorem Model.response_solves
    (m : Model ι κ) (initial : ι → ℝ) (t : ℝ) :
    HasDerivAt (m.response initial) (m.operator (m.response initial t)) t := by
  have h := (hasDerivAt_exp_smul_const' m.operator t).clm_apply
    (hasDerivAt_const t initial)
  simpa [Model.response, mul_apply_eq_comp] using! h

def Model.IsEquilibrium (m : Model ι κ) (u : κ → ℝ) (e : ι → ℝ) : Prop :=
  m.field e u = 0

@[powerlib_foundation] theorem Model.field_shift {m : Model ι κ} {u : κ → ℝ} {e : ι → ℝ}
    (he : m.IsEquilibrium u e) (x : ι → ℝ) :
    m.field x u = m.operator (x - e) := by
  change m.A.mulVec x + m.B.mulVec u = m.A.mulVec (x - e)
  rw [mulVec_sub]
  have he' : m.A.mulVec e + m.B.mulVec u = 0 := he
  calc
    _ = m.A.mulVec x + m.B.mulVec u - (m.A.mulVec e + m.B.mulVec u) := by
      rw [he']; simp
    _ = _ := by abel

def Model.equilibriumResponse (m : Model ι κ) (e initial : ι → ℝ) (t : ℝ) : ι → ℝ :=
  m.response (initial - e) t + e

omit [Fintype κ] in
@[simp, powerlib_foundation] theorem Model.equilibriumResponse_initial
    (m : Model ι κ) (e initial : ι → ℝ) : m.equilibriumResponse e initial 0 = initial := by
  simp [Model.equilibriumResponse]

end ZeroInput

section Autonomous

variable {κ : Type*}

@[powerlib_foundation] theorem Model.autonomous_field [Fintype κ] (m : Model (Fin n) κ)
    (x : State n) : m.autonomous.field x = m.field x 0 := by
  simp [AutonomousModel.field, Model.autonomous, Model.field]

@[powerlib_foundation] theorem Model.autonomous_operator (m : Model (Fin n) κ) :
    m.autonomous.operator = m.operator := rfl

@[powerlib_foundation] theorem Model.response_autonomous (m : Model (Fin n) κ) :
    powerlib.LTI.response m.autonomous = m.response := rfl

end Autonomous

/-- Standard Euclidean-norm exponential decay of every global solution. -/
def ExponentiallyStable (m : AutonomousModel n) : Prop :=
  ∃ K > 0, ∃ rate > 0, ∀ x, IsTrajectory m x → ∀ t, 0 ≤ t →
    ‖euclidean (x t)‖ ≤ K * Real.exp (-(rate * t)) * ‖euclidean (x 0)‖

/-- Exact, model-indexed certificate. The bounds have semantic meaning for all
states; the untrusted synthesizer proves them by rational sums of squares. -/
structure Accepted (m : AutonomousModel n) where
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

@[powerlib_foundation, aesop safe apply] theorem energy_derivative {m : AutonomousModel n} (P : Matrix (Fin n) (Fin n) ℝ)
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

@[powerlib_foundation, aesop safe apply] theorem lyapunov_dissipation {m : AutonomousModel n} (c : Accepted m) (x : State n) :
    dotProduct (m.field x) (c.P.mulVec x) +
      dotProduct x (c.P.mulVec (m.field x)) = -sqNorm x := by
  calc
    _ = energy (m.A.transpose * c.P + c.P * m.A) x := by
      simp only [energy, AutonomousModel.field, generated.linearField_spec, Matrix.add_mulVec,
        dotProduct_add, ← Matrix.mulVec_mulVec]
      rw [Matrix.dotProduct_mulVec x m.A.transpose (c.P.mulVec x), Matrix.vecMul_transpose]
    _ = energy (-1) x := congrArg (fun Q => energy Q x) c.lyapunov
    _ = -sqNorm x := by
      simp [energy, Matrix.neg_mulVec, sqNorm, dotProduct, pow_two]

@[powerlib_domain, aesop safe apply] theorem Accepted.energy_derivative {m : AutonomousModel n} (c : Accepted m)
    {x : ℝ → State n} (hx : IsTrajectory m x) (t : ℝ) :
    HasDerivAt (fun s => energy c.P (x s)) (-sqNorm (x t)) t := by
  simpa only [lyapunov_dissipation c] using powerlib.LTI.energy_derivative c.P hx t

@[powerlib_domain, aesop safe apply] theorem Accepted.energy_decay {m : AutonomousModel n} (c : Accepted m)
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

@[powerlib_domain, aesop safe apply] theorem Accepted.decay_bound {m : AutonomousModel n} (c : Accepted m)
    {x : ℝ → State n} (hx : IsTrajectory m x) (t : ℝ) (ht : 0 ≤ t) :
    sqNorm (x t) ≤ (c.upper / c.lower) * Real.exp (-(t / c.upper)) * sqNorm (x 0) := by
  have h := (c.lower_bound (x t)).trans ((c.energy_decay hx t ht).trans
    (mul_le_mul_of_nonneg_left (c.upper_bound (x 0)) (Real.exp_pos _).le))
  calc
    _ ≤ (Real.exp (-(t / c.upper)) * (c.upper * sqNorm (x 0))) / c.lower :=
      (le_div_iff₀ c.lower_pos).mpr (by simpa [mul_comm] using h)
    _ = _ := by ring

@[powerlib_domain, aesop safe apply] theorem Accepted.norm_bound {m : AutonomousModel n} (c : Accepted m)
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

@[powerlib_domain, aesop safe apply] theorem Accepted.exponentially_stable {m : AutonomousModel n}
    (c : Accepted m) : ExponentiallyStable m := by
  refine ⟨Real.sqrt (c.upper / c.lower), Real.sqrt_pos.2 (div_pos c.upper_pos c.lower_pos),
    1 / (2 * c.upper), div_pos zero_lt_one (mul_pos (by norm_num) c.upper_pos), ?_⟩
  intro x hx t ht
  convert! c.norm_bound hx t ht using 1
  congr 2
  ring_nf

@[powerlib_domain, aesop safe apply] theorem Accepted.response_bound {m : AutonomousModel n}
    (c : Accepted m) (initial : State n) (t : ℝ) (ht : 0 ≤ t) :
    sqNorm (response m initial t) ≤
      (c.upper / c.lower) * Real.exp (-(t / c.upper)) * sqNorm initial := by
  simpa using c.decay_bound (response_solves m initial) t ht

-- A broad equality rule needs backtracking. Aesop's "unsafe" search category
-- still produces an ordinary kernel-checked proof; it is not a proof escape.
@[powerlib_domain, aesop unsafe 80% apply] theorem Accepted.trajectory_unique {m : AutonomousModel n} (c : Accepted m)
    {x y : ℝ → State n} (hx : IsTrajectory m x) (hy : IsTrajectory m y)
    (h0 : x 0 = y 0) (t : ℝ) (ht : 0 ≤ t) : x t = y t := by
  have hd : IsTrajectory m (fun s => x s - y s) := by
    intro s
    simpa only [AutonomousModel.field, generated.linearField_spec, Matrix.mulVec_sub] using!
      (hx s).sub (hy s)
  have h := c.decay_bound hd t ht
  simp only [h0, sub_self, sqNorm_zero, mul_zero] at h
  exact sub_eq_zero.mp ((sqNorm_eq_zero_iff _).mp (le_antisymm h (sqNorm_nonneg _)))

@[powerlib_domain, aesop safe apply] theorem Accepted.response_unique {m : AutonomousModel n} (c : Accepted m)
    {x : ℝ → State n} (hx : IsTrajectory m x) (t : ℝ) (ht : 0 ≤ t) :
    x t = response m (x 0) t :=
  c.trajectory_unique hx (response_solves m (x 0)) (by simp) t ht

@[powerlib_domain, aesop norm forward (immediate := [c, hx])]
theorem Accepted.sqNorm_tendsto_zero {m : AutonomousModel n} (c : Accepted m)
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

/-! ## Spectral and transfer-function semantics -/

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

def characteristicMatrix (A : Matrix ι ι ℝ) (s : ℂ) : Matrix ι ι ℂ :=
  s • (1 : Matrix ι ι ℂ) - A.map (algebraMap ℝ ℂ)

def SpectrallyStable (A : Matrix ι ι ℝ) : Prop :=
  ∀ s : ℂ, (characteristicMatrix A s).det = 0 → s.re < 0

@[powerlib_foundation] theorem det_characteristicMatrix (A : Matrix ι ι ℝ) (s : ℂ) :
    (characteristicMatrix A s).det = (A.map (algebraMap ℝ ℂ)).charpoly.eval s := by
  rw [Matrix.eval_charpoly, characteristicMatrix, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

@[powerlib_foundation] theorem spectrallyStable_reindex (e : ι ≃ ι') (A : Matrix ι ι ℝ) :
    SpectrallyStable (A.reindex e e) ↔ SpectrallyStable A := by
  have h (s : ℂ) :
      characteristicMatrix (A.reindex e e) s = (characteristicMatrix A s).reindex e e := by
    ext i j
    simp [characteristicMatrix, Matrix.one_apply]
  simp only [SpectrallyStable, h, Matrix.det_reindex_self]

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

abbrev complexify {m n : Type*} (M : Matrix m n ℝ) : Matrix m n ℂ := M.map (algebraMap ℝ ℂ)

def transfer (m : Model ι κ) (s : ℂ) : Matrix κ κ ℂ :=
  complexify m.C * (characteristicMatrix m.A s)⁻¹ * complexify m.B + complexify m.D

@[powerlib_foundation] theorem complexify_mul {m n p : Type*} [Fintype n]
    (M : Matrix m n ℝ) (N : Matrix n p ℝ) : complexify (M * N) = complexify M * complexify N :=
  Matrix.map_mul

@[powerlib_foundation] theorem complexify_neg {m n : Type*} (M : Matrix m n ℝ) :
    complexify (-M) = -complexify M :=
  Matrix.map_neg _ (fun a => map_neg _ a) M

@[powerlib_foundation] theorem complexify_sub {m n : Type*} (M N : Matrix m n ℝ) :
    complexify (M - N) = complexify M - complexify N :=
  Matrix.map_sub _ (fun a b => map_sub _ a b) M N

@[powerlib_foundation] theorem complexify_zero {m n : Type*} :
    complexify (0 : Matrix m n ℝ) = 0 :=
  Matrix.map_zero _ (map_zero _)

@[powerlib_foundation] theorem complexify_fromRows {m₁ m₂ n : Type*}
    (A₁ : Matrix m₁ n ℝ) (A₂ : Matrix m₂ n ℝ) :
    complexify (fromRows A₁ A₂) = fromRows (complexify A₁) (complexify A₂) :=
  fromRows_map _ _ _

@[powerlib_foundation] theorem complexify_fromCols {m n₁ n₂ : Type*}
    (A₁ : Matrix m n₁ ℝ) (A₂ : Matrix m n₂ ℝ) :
    complexify (fromCols A₁ A₂) = fromCols (complexify A₁) (complexify A₂) :=
  fromCols_map _ _ _

@[powerlib_foundation] theorem complexify_fromBlocks {l m n o : Type*}
    (A : Matrix n l ℝ) (B : Matrix n m ℝ) (C : Matrix o l ℝ) (D : Matrix o m ℝ) :
    complexify (fromBlocks A B C D) =
      fromBlocks (complexify A) (complexify B) (complexify C) (complexify D) :=
  Matrix.fromBlocks_map _ _ _ _ _

@[powerlib_foundation] theorem transfer_eq_adjugate (m : Model ι κ) (s : ℂ) :
    transfer m s = ((characteristicMatrix m.A s).det)⁻¹ •
      (complexify m.C * (characteristicMatrix m.A s).adjugate * complexify m.B) +
      complexify m.D := by
  rw [transfer, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.mul_smul, Matrix.smul_mul]

/-! ## Coordinate invariance and minimal realization -/

variable {ι ι' κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [Fintype κ] [DecidableEq κ]

def changeCoordinates (T : Matrix ι' ι ℝ) (S : Matrix ι ι' ℝ) (m : Model ι κ) :
    Model ι' κ :=
  ⟨T * m.A * S, T * m.B, m.C * S, m.D⟩

def Similar (m : Model ι κ) (m' : Model ι' κ) : Prop :=
  ∃ (T : Matrix ι' ι ℝ) (S : Matrix ι ι' ℝ), T * S = 1 ∧ S * T = 1 ∧ m' = changeCoordinates T S m

omit [DecidableEq ι] [Fintype ι'] in
@[powerlib_foundation] private lemma complexify_mul_eq_one {T : Matrix ι' ι ℝ} {S : Matrix ι ι' ℝ}
    (h : T * S = 1) : complexify T * complexify S = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]

@[powerlib_foundation] theorem inv_conj {T : Matrix ι' ι ℂ} {S : Matrix ι ι' ℂ}
    (hTS : T * S = 1) (hST : S * T = 1) (N : Matrix ι ι ℂ) :
    (T * N * S)⁻¹ = T * N⁻¹ * S := by
  by_cases h : IsUnit N.det
  · apply Matrix.inv_eq_right_inv
    calc T * N * S * (T * N⁻¹ * S) = T * (N * (S * T) * N⁻¹) * S := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hST, Matrix.mul_one, Matrix.mul_nonsing_inv _ h, Matrix.mul_one, hTS]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ (by rwa [Matrix.det_conj_of_mul_eq_one hTS hST]),
      Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.mul_zero, Matrix.zero_mul]

omit [Fintype ι'] in
@[powerlib_foundation] theorem characteristicMatrix_conj {T : Matrix ι' ι ℝ} {S : Matrix ι ι' ℝ}
    (hTS : T * S = 1) (A : Matrix ι ι ℝ) (s : ℂ) :
    characteristicMatrix (T * A * S) s =
      complexify T * characteristicMatrix A s * complexify S := by
  simp only [characteristicMatrix, Matrix.map_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, complexify_mul_eq_one hTS]

@[powerlib_foundation] theorem det_characteristicMatrix_conj {T : Matrix ι' ι ℝ}
    {S : Matrix ι ι' ℝ} (hTS : T * S = 1) (hST : S * T = 1) (A : Matrix ι ι ℝ) (s : ℂ) :
    (characteristicMatrix (T * A * S) s).det = (characteristicMatrix A s).det := by
  rw [characteristicMatrix_conj hTS,
    Matrix.det_conj_of_mul_eq_one (complexify_mul_eq_one hTS) (complexify_mul_eq_one hST)]

@[powerlib_foundation] theorem spectrallyStable_conj_iff {T : Matrix ι' ι ℝ} {S : Matrix ι ι' ℝ}
    (hTS : T * S = 1) (hST : S * T = 1) (A : Matrix ι ι ℝ) :
    SpectrallyStable (T * A * S) ↔ SpectrallyStable A := by
  simp only [SpectrallyStable, det_characteristicMatrix_conj hTS hST]

omit [Fintype κ] [DecidableEq κ] in
@[powerlib_foundation] theorem transfer_changeCoordinates {T : Matrix ι' ι ℝ} {S : Matrix ι ι' ℝ}
    (hTS : T * S = 1) (hST : S * T = 1) (m : Model ι κ) (s : ℂ) :
    transfer (changeCoordinates T S m) s = transfer m s := by
  simp only [transfer, changeCoordinates]
  rw [characteristicMatrix_conj hTS,
    inv_conj (complexify_mul_eq_one hTS) (complexify_mul_eq_one hST), complexify_mul,
    complexify_mul]
  congr 1
  calc complexify m.C * complexify S * (complexify T * (characteristicMatrix m.A s)⁻¹ *
        complexify S) * (complexify T * complexify m.B)
      = complexify m.C * (complexify S * complexify T) * (characteristicMatrix m.A s)⁻¹ *
          (complexify S * complexify T) * complexify m.B := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [complexify_mul_eq_one hST, Matrix.mul_one, Matrix.mul_one]

omit [Fintype κ] [DecidableEq κ] in
@[powerlib_foundation] theorem Similar.transfer_eq {m : Model ι κ} {m' : Model ι' κ}
    (h : Similar m m') (s : ℂ) : transfer m' s = transfer m s := by
  obtain ⟨T, S, hTS, hST, rfl⟩ := h
  exact transfer_changeCoordinates hTS hST m s

def markov (m : Model ι κ) (k : ℕ) : Matrix κ κ ℝ := m.C * m.A ^ k * m.B

section Expansion

variable (m : Model ι κ)

omit [Fintype κ] [DecidableEq κ] in
@[powerlib_foundation] private lemma smul_resolvent {s : ℂ}
    (h : (characteristicMatrix m.A s).det ≠ 0) :
    s • (characteristicMatrix m.A s)⁻¹ = 1 + complexify m.A * (characteristicMatrix m.A s)⁻¹ := by
  have hinv := Matrix.mul_nonsing_inv (characteristicMatrix m.A s) (isUnit_iff_ne_zero.mpr h)
  generalize (characteristicMatrix m.A s)⁻¹ = R at hinv ⊢
  rw [show characteristicMatrix m.A s = s • 1 - complexify m.A from rfl, Matrix.sub_mul,
    Matrix.smul_mul, Matrix.one_mul] at hinv
  rw [← hinv]
  abel

omit [Fintype κ] [DecidableEq κ] in
@[powerlib_foundation] private lemma resolvent_expansion {s : ℂ} (hs : s ≠ 0)
    (h : (characteristicMatrix m.A s).det ≠ 0) (N : ℕ) :
    (characteristicMatrix m.A s)⁻¹ =
      ∑ j ∈ Finset.range N, (s ^ (j + 1))⁻¹ • complexify m.A ^ j +
        (s ^ N)⁻¹ • (complexify m.A ^ N * (characteristicMatrix m.A s)⁻¹) := by
  have hR := smul_resolvent m h
  generalize (characteristicMatrix m.A s)⁻¹ = R at hR ⊢
  have hR' : R = s⁻¹ • (1 + complexify m.A * R) := by
    rw [← hR, smul_smul, inv_mul_cancel₀ hs, one_smul]
  induction N with
  | zero => simp
  | succ N ih =>
    have step : (s ^ N)⁻¹ • (complexify m.A ^ N * R) =
        (s ^ (N + 1))⁻¹ • complexify m.A ^ N +
          (s ^ (N + 1))⁻¹ • (complexify m.A ^ (N + 1) * R) := by
      conv_lhs => rw [hR']
      rw [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, smul_smul, ← Matrix.mul_assoc,
        ← mul_inv, ← pow_succ, ← pow_succ, smul_add]
    rw [Finset.sum_range_succ, add_assoc, ← step]
    exact ih

omit [Fintype κ] [DecidableEq κ] in
@[powerlib_foundation] private lemma transfer_expansion {s : ℂ} (hs : s ≠ 0)
    (h : (characteristicMatrix m.A s).det ≠ 0) (N : ℕ) :
    transfer m s = complexify m.D +
      ∑ j ∈ Finset.range N, (s ^ (j + 1))⁻¹ • complexify (markov m j) +
        (s ^ N)⁻¹ • (complexify m.C * complexify m.A ^ N * (characteristicMatrix m.A s)⁻¹ *
          complexify m.B) := by
  rw [transfer]
  conv_lhs => rw [resolvent_expansion m hs h N]
  simp only [markov, complexify_mul, Matrix.map_pow, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  abel

omit [Fintype κ] [DecidableEq κ] in
open scoped Matrix.Norms.Operator in
@[powerlib_foundation] private lemma resolvent_bound :
    ∃ s₀ > 0, ∀ x : ℝ, s₀ ≤ x → (characteristicMatrix m.A (x : ℂ)).det ≠ 0 ∧
      ‖(characteristicMatrix m.A (x : ℂ))⁻¹‖ ≤ 2 * ‖(1 : Matrix ι ι ℂ)‖ / x := by
  refine ⟨2 * ‖complexify m.A‖ + 1, by positivity, fun x hx => ?_⟩
  have ha := norm_nonneg (complexify m.A)
  have hx0 : 0 < x := by linarith
  have hxn : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real, Real.norm_of_nonneg hx0.le]
  have hdet : (characteristicMatrix m.A (x : ℂ)).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hAv : complexify m.A *ᵥ v = (x : ℂ) • v := by
      rw [show characteristicMatrix m.A (x : ℂ) = (x : ℂ) • 1 - complexify m.A from rfl,
        Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hzero
      exact hzero.symm
    have hle : x * ‖v‖ ≤ ‖complexify m.A‖ * ‖v‖ := by
      rw [← hxn, ← norm_smul, ← hAv]
      exact Matrix.linfty_opNorm_mulVec _ _
    have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
    nlinarith
  refine ⟨hdet, ?_⟩
  have hR := smul_resolvent m hdet
  generalize (characteristicMatrix m.A (x : ℂ))⁻¹ = R at hR ⊢
  have h1 : x * ‖R‖ ≤ ‖(1 : Matrix ι ι ℂ)‖ + ‖complexify m.A‖ * ‖R‖ := by
    rw [← hxn, ← norm_smul, hR]
    exact (norm_add_le _ _).trans (by gcongr; exact Matrix.linfty_opNorm_mul _ _)
  rw [le_div_iff₀ hx0]
  nlinarith [norm_nonneg R, mul_nonneg (show (0 : ℝ) ≤ x - 2 * ‖complexify m.A‖ by linarith)
    (norm_nonneg R)]

end Expansion

omit [Fintype κ] [DecidableEq κ] in
@[powerlib_foundation] theorem exists_det_characteristicMatrix_ne_zero (m : Model ι κ) :
    ∃ s₀ : ℝ, ∀ x : ℝ, s₀ ≤ x → (characteristicMatrix m.A (x : ℂ)).det ≠ 0 := by
  obtain ⟨s₀, -, h⟩ := resolvent_bound m
  exact ⟨s₀, fun x hx => (h x hx).1⟩

@[powerlib_foundation] private lemma eq_zero_of_norm_le_div {E : Type*} [NormedAddCommGroup E]
    (X : E) (K s₀ : ℝ) (h : ∀ x : ℝ, s₀ ≤ x → ‖X‖ ≤ K / x) : X = 0 := by
  have ht : Filter.Tendsto (fun x : ℝ => K / x) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  exact norm_le_zero_iff.mp (ge_of_tendsto ht (Filter.eventually_atTop.2 ⟨s₀, h⟩))

open scoped Matrix.Norms.Operator in
@[powerlib_foundation] private lemma remainder_bound (m : Model ι κ) (N : ℕ) :
    ∃ s₀ > 0, ∃ K, ∀ x : ℝ, s₀ ≤ x → (characteristicMatrix m.A (x : ℂ)).det ≠ 0 ∧
      ‖complexify m.C * complexify m.A ^ N * (characteristicMatrix m.A (x : ℂ))⁻¹ *
        complexify m.B‖ ≤ K / x := by
  obtain ⟨s₀, hs₀, hb⟩ := resolvent_bound m
  refine ⟨s₀, hs₀, ‖complexify m.C * complexify m.A ^ N‖ * (2 * ‖(1 : Matrix ι ι ℂ)‖) *
    ‖complexify m.B‖, fun x hx => ⟨(hb x hx).1, ?_⟩⟩
  have hx0 : 0 < x := hs₀.trans_le hx
  calc _ ≤ ‖complexify m.C * complexify m.A ^ N‖ * ‖(characteristicMatrix m.A (x : ℂ))⁻¹‖ *
        ‖complexify m.B‖ :=
        (Matrix.linfty_opNorm_mul _ _).trans
          (by gcongr; exact Matrix.linfty_opNorm_mul _ _)
    _ ≤ ‖complexify m.C * complexify m.A ^ N‖ * (2 * ‖(1 : Matrix ι ι ℂ)‖ / x) *
        ‖complexify m.B‖ := by gcongr; exact (hb x hx).2
    _ = _ := by field_simp

open scoped Matrix.Norms.Operator in
@[powerlib_foundation] theorem markov_eq_of_transfer_eventually_eq {m : Model ι κ}
    {m' : Model ι' κ} (h : ∃ s₁ : ℝ, ∀ x : ℝ, s₁ ≤ x → transfer m x = transfer m' x) :
    m.D = m'.D ∧ ∀ k, markov m k = markov m' k := by
  obtain ⟨s₁, hs₁⟩ := h
  have hinj : Function.Injective fun M : Matrix κ κ ℝ => complexify M :=
    Matrix.map_injective (algebraMap ℝ ℂ).injective
  have key : ∀ N, ∃ s₀ > 0, ∃ K, ∀ x : ℝ, s₀ ≤ x →
      complexify m.D + ∑ j ∈ Finset.range N, ((x : ℂ) ^ (j + 1))⁻¹ • complexify (markov m j) +
          ((x : ℂ) ^ N)⁻¹ • (complexify m.C * complexify m.A ^ N *
            (characteristicMatrix m.A (x : ℂ))⁻¹ * complexify m.B) =
        complexify m'.D +
          ∑ j ∈ Finset.range N, ((x : ℂ) ^ (j + 1))⁻¹ • complexify (markov m' j) +
          ((x : ℂ) ^ N)⁻¹ • (complexify m'.C * complexify m'.A ^ N *
            (characteristicMatrix m'.A (x : ℂ))⁻¹ * complexify m'.B) ∧
      ‖complexify m.C * complexify m.A ^ N * (characteristicMatrix m.A (x : ℂ))⁻¹ *
          complexify m.B - complexify m'.C * complexify m'.A ^ N *
          (characteristicMatrix m'.A (x : ℂ))⁻¹ * complexify m'.B‖ ≤ K / x := by
    intro N
    obtain ⟨a, ha, K, hK⟩ := remainder_bound m N
    obtain ⟨a', ha', K', hK'⟩ := remainder_bound m' N
    refine ⟨max (max a a') s₁, lt_max_of_lt_left (lt_max_of_lt_left ha), K + K',
      fun x hx => ?_⟩
    have hxa : a ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    have hxa' : a' ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have hx₁ : s₁ ≤ x := le_trans (le_max_right _ _) hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ha.trans_le hxa).ne'
    refine ⟨?_, ?_⟩
    · rw [← transfer_expansion m hx0 (hK x hxa).1 N, ← transfer_expansion m' hx0 (hK' x hxa').1 N]
      exact hs₁ x hx₁
    · rw [add_div]
      exact (norm_sub_le _ _).trans (add_le_add (hK x hxa).2 (hK' x hxa').2)
  have hD : complexify m.D = complexify m'.D := by
    obtain ⟨s₀, -, K, hK⟩ := key 0
    refine sub_eq_zero.mp (eq_zero_of_norm_le_div _ K s₀ fun x hx => ?_)
    obtain ⟨e, hb⟩ := hK x hx
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, pow_zero, inv_one, one_smul,
      Matrix.mul_one] at e hb
    rw [norm_sub_rev] at hb
    have hdiff : complexify m.D - complexify m'.D =
        complexify m'.C * (characteristicMatrix m'.A (x : ℂ))⁻¹ * complexify m'.B -
          complexify m.C * (characteristicMatrix m.A (x : ℂ))⁻¹ * complexify m.B := by
      rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
    rw [hdiff]
    exact hb
  have hM : ∀ k, complexify (markov m k) = complexify (markov m' k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      obtain ⟨s₀, hs₀, K, hK⟩ := key (k + 1)
      refine sub_eq_zero.mp (eq_zero_of_norm_le_div _ K s₀ fun x hx => ?_)
      obtain ⟨e, hb⟩ := hK x hx
      have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hs₀.trans_le hx).ne'
      rw [Finset.sum_range_succ, Finset.sum_range_succ, hD,
        Finset.sum_congr rfl fun j hj => by rw [ih j (Finset.mem_range.mp hj)]] at e
      set c : ℂ := ((x : ℂ) ^ (k + 1))⁻¹
      have hc : c ≠ 0 := inv_ne_zero (pow_ne_zero _ hx0)
      have hsc : c • (complexify (markov m k) - complexify (markov m' k)) =
          c • ((complexify m'.C * complexify m'.A ^ (k + 1) *
            (characteristicMatrix m'.A (x : ℂ))⁻¹ * complexify m'.B) -
          (complexify m.C * complexify m.A ^ (k + 1) * (characteristicMatrix m.A (x : ℂ))⁻¹ *
            complexify m.B)) := by
        rw [smul_sub, smul_sub]
        rw [← sub_eq_zero] at e ⊢
        rw [← e]
        abel
      rw [smul_right_injective _ hc hsc, norm_sub_rev]
      exact hb
  exact ⟨hinj hD, fun k => hinj (hM k)⟩

open scoped Matrix.Norms.Operator in
@[powerlib_foundation] private lemma norm_mul_pow_le {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] (C : Matrix β α ℂ) (A : Matrix α α ℂ) (N : ℕ) : ‖C * A ^ N‖ ≤ ‖C‖ * ‖A‖ ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, ← Matrix.mul_assoc]
    calc ‖C * A ^ N * A‖ ≤ ‖C * A ^ N‖ * ‖A‖ := Matrix.linfty_opNorm_mul _ _
      _ ≤ ‖C‖ * ‖A‖ ^ N * ‖A‖ := by gcongr
      _ = ‖C‖ * ‖A‖ ^ (N + 1) := by ring

open scoped Matrix.Norms.Operator in
@[powerlib_foundation] private lemma norm_remainder_le (m : Model ι κ) (N : ℕ) (s : ℂ) :
    ‖complexify m.C * complexify m.A ^ N * (characteristicMatrix m.A s)⁻¹ * complexify m.B‖ ≤
      ‖complexify m.A‖ ^ N * (‖complexify m.C‖ * ‖(characteristicMatrix m.A s)⁻¹‖ *
        ‖complexify m.B‖) := by
  calc _ ≤ ‖complexify m.C * complexify m.A ^ N * (characteristicMatrix m.A s)⁻¹‖ *
        ‖complexify m.B‖ := Matrix.linfty_opNorm_mul _ _
    _ ≤ ‖complexify m.C * complexify m.A ^ N‖ * ‖(characteristicMatrix m.A s)⁻¹‖ *
        ‖complexify m.B‖ := by gcongr; exact Matrix.linfty_opNorm_mul _ _
    _ ≤ ‖complexify m.C‖ * ‖complexify m.A‖ ^ N * ‖(characteristicMatrix m.A s)⁻¹‖ *
        ‖complexify m.B‖ := by gcongr; exact norm_mul_pow_le _ _ _
    _ = _ := by ring

open scoped Matrix.Norms.Operator in
@[powerlib_foundation] theorem transfer_eventually_eq_of_markov_eq {m : Model ι κ}
    {m' : Model ι' κ} (hD : m.D = m'.D) (hM : ∀ k, markov m k = markov m' k) :
    ∃ s₁ : ℝ, ∀ x : ℝ, s₁ ≤ x → transfer m x = transfer m' x := by
  obtain ⟨a, ha, hb⟩ := resolvent_bound m
  obtain ⟨a', ha', hb'⟩ := resolvent_bound m'
  refine ⟨max (max a a') (‖complexify m.A‖ + ‖complexify m'.A‖ + 1), fun x hx => ?_⟩
  obtain ⟨hxa₁, hxn⟩ := max_le_iff.mp hx
  obtain ⟨hxa, hxa'⟩ := max_le_iff.mp hxa₁
  have hx0 : 0 < x := ha.trans_le hxa
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  have hn := norm_nonneg (complexify m.A)
  have hn' := norm_nonneg (complexify m'.A)
  have hdiff : ∀ N, transfer m x - transfer m' x = ((x : ℂ) ^ N)⁻¹ •
      (complexify m.C * complexify m.A ^ N * (characteristicMatrix m.A (x : ℂ))⁻¹ *
        complexify m.B - complexify m'.C * complexify m'.A ^ N *
        (characteristicMatrix m'.A (x : ℂ))⁻¹ * complexify m'.B) := by
    intro N
    rw [transfer_expansion m hxc (hb x hxa).1 N, transfer_expansion m' hxc (hb' x hxa').1 N, hD]
    simp only [hM, smul_sub]
    abel
  set K := ‖complexify m.C‖ * ‖(characteristicMatrix m.A (x : ℂ))⁻¹‖ * ‖complexify m.B‖
  set K' := ‖complexify m'.C‖ * ‖(characteristicMatrix m'.A (x : ℂ))⁻¹‖ * ‖complexify m'.B‖
  have hlim : Filter.Tendsto (fun N : ℕ => (‖complexify m.A‖ / x) ^ N * K +
      (‖complexify m'.A‖ / x) ^ N * K') Filter.atTop (nhds 0) := by
    have h₁ := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hn hx0.le)
      ((div_lt_one hx0).mpr (by linarith))
    have h₂ := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hn' hx0.le)
      ((div_lt_one hx0).mpr (by linarith))
    simpa using (h₁.mul_const K).add (h₂.mul_const K')
  refine sub_eq_zero.mp (norm_le_zero_iff.mp (ge_of_tendsto' hlim fun N => ?_))
  have hxN : ‖((x : ℂ) ^ N)⁻¹‖ = (x ^ N)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx0.le]
  rw [hdiff N, norm_smul, hxN]
  calc (x ^ N)⁻¹ * ‖_ - _‖ ≤ (x ^ N)⁻¹ * (‖complexify m.A‖ ^ N * K + ‖complexify m'.A‖ ^ N * K') := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add (norm_remainder_le m N _)
          (norm_remainder_le m' N _))
    _ = _ := by
        rw [div_pow, div_pow]
        field_simp

omit [Fintype κ] [DecidableEq κ] in
@[powerlib_foundation] private lemma transfer_eq_numerator (m : Model ι κ) (s : ℂ) :
    transfer m s = ((complexify m.A).charpoly.eval s)⁻¹ •
      ((complexify m.C).map Polynomial.C * (charmatrix (complexify m.A)).adjugate *
        (complexify m.B).map Polynomial.C).map (Polynomial.eval s) + complexify m.D := by
  have hchar : (Polynomial.evalRingHom s).mapMatrix (charmatrix (complexify m.A)) =
      characteristicMatrix m.A s := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [characteristicMatrix, charmatrix_apply_eq]
    · simp [characteristicMatrix, charmatrix_apply_ne _ _ _ h, Matrix.one_apply_ne h]
  have hadj : (charmatrix (complexify m.A)).adjugate.map (Polynomial.evalRingHom s) =
      (characteristicMatrix m.A s).adjugate := by
    rw [← hchar, ← RingHom.map_adjugate]
    rfl
  rw [transfer_eq_adjugate, LTI.det_characteristicMatrix]
  congr 2
  rw [show (Polynomial.eval s : Polynomial ℂ → ℂ) = Polynomial.evalRingHom s from rfl,
    Matrix.map_mul, Matrix.map_mul, hadj]
  congr 2 <;> ext <;> simp

omit [Fintype κ] [DecidableEq κ] in
@[powerlib_foundation] theorem transfer_eq_of_eventually_eq {m : Model ι κ}
    {m' : Model ι' κ} (h : ∃ s₁ : ℝ, ∀ x : ℝ, s₁ ≤ x → transfer m x = transfer m' x)
    (s : ℂ) (hs : (characteristicMatrix m.A s).det ≠ 0)
    (hs' : (characteristicMatrix m'.A s).det ≠ 0) : transfer m s = transfer m' s := by
  obtain ⟨s₁, hs₁⟩ := h
  obtain ⟨a, -, ha⟩ := resolvent_bound m
  obtain ⟨a', -, ha'⟩ := resolvent_bound m'
  have hnum := transfer_eq_numerator m
  have hnum' := transfer_eq_numerator m'
  have hdet := LTI.det_characteristicMatrix m.A
  have hdet' := LTI.det_characteristicMatrix m'.A
  generalize (complexify m.A).charpoly = χ at hnum hdet
  generalize (complexify m'.A).charpoly = χ' at hnum' hdet'
  generalize (complexify m.C).map Polynomial.C * (charmatrix (complexify m.A)).adjugate *
    (complexify m.B).map Polynomial.C = N at hnum
  generalize (complexify m'.C).map Polynomial.C * (charmatrix (complexify m'.A)).adjugate *
    (complexify m'.B).map Polynomial.C = N' at hnum'
  have key : ∀ z, χ.eval z ≠ 0 → χ'.eval z ≠ 0 → ∀ i j,
      (χ' * N i j + χ * χ' * Polynomial.C (complexify m.D i j) -
        (χ * N' i j + χ * χ' * Polynomial.C (complexify m'.D i j))).eval z =
      χ.eval z * χ'.eval z * (transfer m z i j - transfer m' z i j) := by
    intro z hz hz' i j
    rw [hnum z, hnum' z]
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    field_simp
  have hzero : ∀ i j, χ' * N i j + χ * χ' * Polynomial.C (complexify m.D i j) -
      (χ * N' i j + χ * χ' * Polynomial.C (complexify m'.D i j)) = 0 := by
    intro i j
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ ((Set.Ici_infinite (max (max a a') s₁)).image
      Complex.ofReal_injective.injOn)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxa₁, hx₁⟩ := max_le_iff.mp (Set.mem_Ici.mp hx)
    obtain ⟨hxa, hxa'⟩ := max_le_iff.mp hxa₁
    have hz := (ha x hxa).1
    have hz' := (ha' x hxa').1
    rw [hdet] at hz
    rw [hdet'] at hz'
    show Polynomial.IsRoot _ _
    rw [Polynomial.IsRoot, key x hz hz' i j, hs₁ x hx₁, sub_self, mul_zero]
  rw [hdet] at hs
  rw [hdet'] at hs'
  ext i j
  have e := key s hs hs' i j
  rw [hzero i j, Polynomial.eval_zero] at e
  exact sub_eq_zero.mp ((mul_eq_zero.mp e.symm).resolve_left (mul_ne_zero hs hs'))

@[powerlib_foundation] theorem transfer_eq_iff_markov_eq {m : Model ι κ}
    {m' : Model ι' κ} :
    (∀ s : ℂ, (characteristicMatrix m.A s).det ≠ 0 → (characteristicMatrix m'.A s).det ≠ 0 →
      transfer m s = transfer m' s) ↔ m.D = m'.D ∧ ∀ k, markov m k = markov m' k := by
  refine ⟨fun h => ?_, fun ⟨hD, hM⟩ =>
    transfer_eq_of_eventually_eq (transfer_eventually_eq_of_markov_eq hD hM)⟩
  obtain ⟨a, -, ha⟩ := resolvent_bound m
  obtain ⟨a', -, ha'⟩ := resolvent_bound m'
  exact markov_eq_of_transfer_eventually_eq ⟨max a a', fun x hx =>
    h x (ha x (le_of_max_le_left hx)).1 (ha' x (le_of_max_le_right hx)).1⟩

section Minimal

variable {n n' p : ℕ}

def obsv (A : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin p) (Fin n) ℝ) (N : ℕ) :
    Matrix (Fin N × Fin p) (Fin n) ℝ :=
  Matrix.of fun ki j => (C * A ^ (ki.1 : ℕ)) ki.2 j

def ctrb (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ) (N : ℕ) :
    Matrix (Fin n) (Fin N × Fin p) ℝ :=
  Matrix.of fun i kj => (A ^ (kj.1 : ℕ) * B) i kj.2

@[powerlib_foundation] private lemma obsv_mul {β : Type*} (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (N : ℕ) (X : Matrix (Fin n) β ℝ) :
    obsv A C N * X = Matrix.of fun ki j => (C * A ^ (ki.1 : ℕ) * X) ki.2 j := by
  ext ⟨k, i⟩ j
  simp [obsv, Matrix.mul_apply]

@[powerlib_foundation] private lemma mul_ctrb {β : Type*} [Fintype β]
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ) (N : ℕ)
    (X : Matrix β (Fin n) ℝ) :
    X * ctrb A B N = Matrix.of fun i kj => (X * A ^ (kj.1 : ℕ) * B) i kj.2 := by
  ext i ⟨k, j⟩
  simp only [Matrix.of_apply]
  rw [Matrix.mul_assoc]
  simp [ctrb, Matrix.mul_apply]

@[powerlib_foundation] private lemma hankel (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) (C : Matrix (Fin p) (Fin n) ℝ) (N₁ N₂ r : ℕ) :
    obsv A C N₁ * A ^ r * ctrb A B N₂ =
      Matrix.of fun ki lj => (C * A ^ ((ki.1 : ℕ) + r + lj.1) * B) ki.2 lj.2 := by
  rw [mul_ctrb]
  ext ⟨k, i⟩ ⟨l, j⟩
  simp only [Matrix.of_apply, Matrix.mul_assoc]
  rw [obsv_mul]
  simp only [Matrix.of_apply, pow_add, Matrix.mul_assoc]

@[powerlib_foundation] theorem ctrb_eq (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) : ctrb A B n = LinearSystems.controllabilityMatrix A B := rfl

@[powerlib_foundation] theorem obsv_eq (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) : obsv A C n = LinearSystems.observabilityMatrix A C := rfl

@[powerlib_foundation] private lemma ctrb_right_inverse {A : Matrix (Fin n) (Fin n) ℝ}
    {B : Matrix (Fin n) (Fin p) ℝ} (h : LinearSystems.IsControllable A B) :
    ∃ R : Matrix (Fin n × Fin p) (Fin n) ℝ, ctrb A B n * R = 1 := by
  rw [ctrb_eq]
  exact Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    ((MatrixAlgebra.mulVec_range_top_iff_rank_eq_card_rows _).mpr (by
      rw [Fintype.card_fin]
      exact (LinearSystems.isControllable_iff_controllabilityMatrix_rank_eq A B).mp h))

@[powerlib_foundation] private lemma obsv_left_inverse {A : Matrix (Fin n) (Fin n) ℝ}
    {C : Matrix (Fin p) (Fin n) ℝ} (h : LinearSystems.IsObservable A C) :
    ∃ L : Matrix (Fin n) (Fin n × Fin p) ℝ, L * obsv A C n = 1 := by
  have hr : (LinearSystems.observabilityMatrix A C)ᵀ.rank = Fintype.card (Fin n) := by
    rw [Matrix.rank_transpose, Fintype.card_fin]
    exact (LinearSystems.isObservable_iff_observabilityMatrix_rank_eq A C).mp h
  rw [obsv_eq]
  refine Matrix.vecMul_surjective_iff_exists_left_inverse.mp fun y => ?_
  obtain ⟨x, hx⟩ := (MatrixAlgebra.mulVec_range_top_iff_rank_eq_card_rows _).mpr hr y
  exact ⟨x, by simpa only [Matrix.mulVec_transpose] using hx⟩

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
@[powerlib_foundation] private lemma model_eq {m m' : Model ι κ} (hA : m.A = m'.A)
    (hB : m.B = m'.B) (hC : m.C = m'.C) (hD : m.D = m'.D) : m = m' := by
  cases m
  cases m'
  simp_all

@[powerlib_foundation] theorem similar_of_markov_eq {m : Model (Fin n) (Fin p)}
    {m' : Model (Fin n') (Fin p)}
    (hc : LinearSystems.IsControllable m.A m.B) (ho : LinearSystems.IsObservable m.A m.C)
    (hc' : LinearSystems.IsControllable m'.A m'.B) (ho' : LinearSystems.IsObservable m'.A m'.C)
    (hD : m.D = m'.D) (hM : ∀ k, markov m k = markov m' k) : Similar m m' := by
  obtain ⟨R, hR⟩ := ctrb_right_inverse hc
  obtain ⟨R', hR'⟩ := ctrb_right_inverse hc'
  obtain ⟨L, hL⟩ := obsv_left_inverse ho
  obtain ⟨L', hL'⟩ := obsv_left_inverse ho'
  have hH : ∀ N₁ N₂ r, obsv m.A m.C N₁ * m.A ^ r * ctrb m.A m.B N₂ =
      obsv m'.A m'.C N₁ * m'.A ^ r * ctrb m'.A m'.B N₂ := by
    intro N₁ N₂ r
    rw [hankel, hankel]
    ext ⟨k, i⟩ ⟨l, j⟩
    exact congrFun (congrFun (hM _) i) j
  have hH0 : ∀ N₁ N₂, obsv m.A m.C N₁ * ctrb m.A m.B N₂ =
      obsv m'.A m'.C N₁ * ctrb m'.A m'.B N₂ := by
    intro N₁ N₂
    simpa only [pow_zero, Matrix.mul_one] using hH N₁ N₂ 0
  set T := L' * obsv m.A m.C n' with hT
  set S := L * obsv m'.A m'.C n with hS
  have hTK : ∀ N, T * ctrb m.A m.B N = ctrb m'.A m'.B N := by
    intro N
    rw [hT, Matrix.mul_assoc, hH0, ← Matrix.mul_assoc, hL', Matrix.one_mul]
  have hSK : ∀ N, S * ctrb m'.A m'.B N = ctrb m.A m.B N := by
    intro N
    rw [hS, Matrix.mul_assoc, ← hH0, ← Matrix.mul_assoc, hL, Matrix.one_mul]
  have hTS : T * S = 1 := by
    calc T * S = T * S * (ctrb m'.A m'.B n' * R') := by rw [hR', Matrix.mul_one]
      _ = T * (S * ctrb m'.A m'.B n') * R' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hSK, hTK, hR']
  have hST : S * T = 1 := by
    calc S * T = S * T * (ctrb m.A m.B n * R) := by rw [hR, Matrix.mul_one]
      _ = S * (T * ctrb m.A m.B n) * R := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hTK, hSK, hR]
  have hB : T * m.B = m'.B := by
    have hOB : obsv m.A m.C n' * m.B = obsv m'.A m'.C n' * m'.B := by
      rw [obsv_mul, obsv_mul]
      ext ⟨k, i⟩ j
      exact congrFun (congrFun (hM k) i) j
    rw [hT, Matrix.mul_assoc, hOB, ← Matrix.mul_assoc, hL', Matrix.one_mul]
  have hC : m'.C * T = m.C := by
    have hCK : m'.C * ctrb m'.A m'.B n = m.C * ctrb m.A m.B n := by
      rw [mul_ctrb, mul_ctrb]
      ext i ⟨l, j⟩
      exact (congrFun (congrFun (hM l) i) j).symm
    calc m'.C * T = m'.C * T * (ctrb m.A m.B n * R) := by rw [hR, Matrix.mul_one]
      _ = m'.C * (T * ctrb m.A m.B n) * R := by simp only [Matrix.mul_assoc]
      _ = m.C := by rw [hTK, hCK, Matrix.mul_assoc, hR, Matrix.mul_one]
  have hA : T * m.A = m'.A * T := by
    have hshift : T * (m.A * ctrb m.A m.B n) = m'.A * ctrb m'.A m'.B n := by
      calc T * (m.A * ctrb m.A m.B n) = L' * (obsv m.A m.C n' * m.A ^ 1 * ctrb m.A m.B n) := by
            rw [hT, pow_one]
            simp only [Matrix.mul_assoc]
        _ = L' * (obsv m'.A m'.C n' * m'.A ^ 1 * ctrb m'.A m'.B n) := by rw [hH]
        _ = m'.A * ctrb m'.A m'.B n := by
            rw [pow_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hL', Matrix.one_mul]
    calc T * m.A = T * m.A * (ctrb m.A m.B n * R) := by rw [hR, Matrix.mul_one]
      _ = T * (m.A * ctrb m.A m.B n) * R := by simp only [Matrix.mul_assoc]
      _ = m'.A * (T * ctrb m.A m.B n) * R := by rw [hshift, hTK]
      _ = m'.A * T := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hR, Matrix.mul_one]
  refine ⟨T, S, hTS, hST, model_eq ?_ hB.symm ?_ hD.symm⟩
  · show m'.A = T * m.A * S
    rw [hA, Matrix.mul_assoc, hTS, Matrix.mul_one]
  · show m'.C = m.C * S
    rw [← hC, Matrix.mul_assoc, hTS, Matrix.mul_one]

@[powerlib_foundation] theorem similar_iff_transfer_eq {m : Model (Fin n) (Fin p)}
    {m' : Model (Fin n') (Fin p)}
    (hc : LinearSystems.IsControllable m.A m.B) (ho : LinearSystems.IsObservable m.A m.C)
    (hc' : LinearSystems.IsControllable m'.A m'.B) (ho' : LinearSystems.IsObservable m'.A m'.C) :
    Similar m m' ↔ ∀ s : ℂ, (characteristicMatrix m.A s).det ≠ 0 →
      (characteristicMatrix m'.A s).det ≠ 0 → transfer m s = transfer m' s := by
  refine ⟨fun h s _ _ => (h.transfer_eq s).symm, fun h => ?_⟩
  obtain ⟨a, -, ha⟩ := resolvent_bound m
  obtain ⟨a', -, ha'⟩ := resolvent_bound m'
  obtain ⟨hD, hM⟩ := markov_eq_of_transfer_eventually_eq ⟨max a a', fun x hx =>
    h x (ha x (le_of_max_le_left hx)).1 (ha' x (le_of_max_le_right hx)).1⟩
  exact similar_of_markov_eq hc ho hc' ho' hD hM

def basisMatrix {r : ℕ} {V : Submodule ℝ (Fin n → ℝ)} (b : Module.Basis (Fin r) ℝ V) :
    Matrix (Fin n) (Fin r) ℝ :=
  Matrix.of fun i j => (b j : Fin n → ℝ) i

@[powerlib_foundation] private lemma exists_coords {r : ℕ} {β : Type*}
    {V : Submodule ℝ (Fin n → ℝ)} (b : Module.Basis (Fin r) ℝ V) (M : Matrix (Fin n) β ℝ)
    (hM : ∀ j, (fun i => M i j) ∈ V) : ∃ M' : Matrix (Fin r) β ℝ, basisMatrix b * M' = M := by
  refine ⟨Matrix.of fun l j => b.repr ⟨fun i => M i j, hM j⟩ l, ?_⟩
  ext i j
  have h := congrArg (fun y : V => (y : Fin n → ℝ) i) (b.sum_repr ⟨fun i => M i j, hM j⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  rw [← h]
  simp only [basisMatrix, Matrix.mul_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

@[powerlib_foundation] theorem reduce_uncontrollable {m : Model (Fin n) (Fin p)}
    (h : ¬ LinearSystems.IsControllable m.A m.B) :
    ∃ (r : ℕ) (m' : Model (Fin r) (Fin p)), r < n ∧ m'.D = m.D ∧
      ∀ k, markov m' k = markov m k := by
  set V := LinearSystems.reachableSubspace m.A m.B
  let b := Module.finBasis ℝ V
  have hinv := (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp
    (LinearSystems.reachableSubspace_invariant m.A m.B)
  obtain ⟨Ar, hAr⟩ := exists_coords b (m.A * basisMatrix b) fun j => by
    have hcol : (fun i => (m.A * basisMatrix b) i j) = m.A *ᵥ (b j : Fin n → ℝ) := by
      funext i
      simp [basisMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [hcol]
    exact hinv _ (b j).2
  obtain ⟨Br, hBr⟩ := exists_coords b m.B fun j => by
    have hcol : (fun i => m.B i j) = m.B *ᵥ Pi.single j 1 := by
      funext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hcol]
    exact LinearSystems.range_B_le_reachableSubspace m.A m.B ⟨Pi.single j 1, rfl⟩
  refine ⟨Module.finrank ℝ V, ⟨Ar, Br, m.C * basisMatrix b, m.D⟩, ?_, rfl, fun k => ?_⟩
  · have hV : V ≠ ⊤ := fun hV =>
      h ((LinearSystems.reachableSubspace_eq_top_iff_isControllable m.A m.B).mp hV)
    simpa using Submodule.finrank_lt hV
  · have hpow : ∀ k, m.A ^ k * basisMatrix b = basisMatrix b * Ar ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, ← hAr, Matrix.mul_assoc,
          ← pow_succ']
    calc m.C * basisMatrix b * Ar ^ k * Br = m.C * (basisMatrix b * Ar ^ k) * Br := by
          simp only [Matrix.mul_assoc]
      _ = m.C * (m.A ^ k * basisMatrix b) * Br := by rw [hpow]
      _ = m.C * m.A ^ k * (basisMatrix b * Br) := by simp only [Matrix.mul_assoc]
      _ = markov m k := by rw [hBr, markov]

def dualModel (m : Model ι κ) : Model ι κ := ⟨m.Aᵀ, m.Cᵀ, m.Bᵀ, m.Dᵀ⟩

omit [Fintype κ] [DecidableEq κ] in
@[powerlib_foundation] theorem markov_dualModel (m : Model ι κ) (k : ℕ) :
    markov (dualModel m) k = (markov m k)ᵀ := by
  simp [markov, dualModel, Matrix.transpose_mul, Matrix.transpose_pow, Matrix.mul_assoc]

@[powerlib_foundation] theorem isObservable_iff_isControllable_transpose
    (A : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin p) (Fin n) ℝ) :
    LinearSystems.IsObservable A C ↔ LinearSystems.IsControllable Aᵀ Cᵀ := by
  have hO : LinearSystems.observabilityMatrix A C =
      (LinearSystems.controllabilityMatrix Aᵀ Cᵀ)ᵀ := by
    ext ⟨k, i⟩ j
    simp [LinearSystems.observabilityMatrix, LinearSystems.controllabilityMatrix,
      ← Matrix.transpose_pow, ← Matrix.transpose_mul]
  rw [LinearSystems.isObservable_iff_observabilityMatrix_rank_eq,
    LinearSystems.isControllable_iff_controllabilityMatrix_rank_eq, hO, Matrix.rank_transpose]

@[powerlib_foundation] private lemma reduce_unobservable {m : Model (Fin n) (Fin p)}
    (h : ¬ LinearSystems.IsObservable m.A m.C) :
    ∃ (r : ℕ) (m' : Model (Fin r) (Fin p)), r < n ∧ m'.D = m.D ∧
      ∀ k, markov m' k = markov m k := by
  have hd : ¬ LinearSystems.IsControllable (dualModel m).A (dualModel m).B := by
    show ¬ LinearSystems.IsControllable m.Aᵀ m.Cᵀ
    rwa [← isObservable_iff_isControllable_transpose]
  obtain ⟨r, m₁, hr, hD, hM⟩ := reduce_uncontrollable hd
  refine ⟨r, dualModel m₁, hr, ?_, fun k => ?_⟩
  · simp [dualModel, hD]
  · rw [markov_dualModel, hM, markov_dualModel, Matrix.transpose_transpose]

@[powerlib_foundation] theorem exists_minimal_markov (m : Model (Fin n) (Fin p)) :
    ∃ (n' : ℕ) (m' : Model (Fin n') (Fin p)), n' ≤ n ∧
      LinearSystems.IsControllable m'.A m'.B ∧ LinearSystems.IsObservable m'.A m'.C ∧
        m'.D = m.D ∧ ∀ k, markov m' k = markov m k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hc : LinearSystems.IsControllable m.A m.B
    · by_cases ho : LinearSystems.IsObservable m.A m.C
      · exact ⟨n, m, le_rfl, hc, ho, rfl, fun _ => rfl⟩
      · obtain ⟨r, m₁, hr, hD, hM⟩ := reduce_unobservable ho
        obtain ⟨n', m', hn', hc', ho', hD', hM'⟩ := ih r hr m₁
        exact ⟨n', m', hn'.trans hr.le, hc', ho', hD'.trans hD, fun k => (hM' k).trans (hM k)⟩
    · obtain ⟨r, m₁, hr, hD, hM⟩ := reduce_uncontrollable hc
      obtain ⟨n', m', hn', hc', ho', hD', hM'⟩ := ih r hr m₁
      exact ⟨n', m', hn'.trans hr.le, hc', ho', hD'.trans hD, fun k => (hM' k).trans (hM k)⟩

@[powerlib_foundation] theorem exists_minimal_realization (m : Model (Fin n) (Fin p)) :
    ∃ (n' : ℕ) (m' : Model (Fin n') (Fin p)), n' ≤ n ∧
      LinearSystems.IsControllable m'.A m'.B ∧ LinearSystems.IsObservable m'.A m'.C ∧
        ∀ s : ℂ, (characteristicMatrix m'.A s).det ≠ 0 → (characteristicMatrix m.A s).det ≠ 0 →
          transfer m' s = transfer m s := by
  obtain ⟨n', m', hn, hc, ho, hD, hM⟩ := exists_minimal_markov m
  exact ⟨n', m', hn, hc, ho, transfer_eq_iff_markov_eq.mpr ⟨hD, hM⟩⟩

@[powerlib_foundation] theorem controllable_observable_iff_minimal
    {m : Model (Fin n) (Fin p)} :
    (LinearSystems.IsControllable m.A m.B ∧ LinearSystems.IsObservable m.A m.C) ↔
      ∀ (n₂ : ℕ) (m₂ : Model (Fin n₂) (Fin p)),
        (∀ s : ℂ, (characteristicMatrix m.A s).det ≠ 0 → (characteristicMatrix m₂.A s).det ≠ 0 →
          transfer m s = transfer m₂ s) → n ≤ n₂ := by
  constructor
  · rintro ⟨hc, ho⟩ n₂ m₂ h
    obtain ⟨hD, hM⟩ := transfer_eq_iff_markov_eq.mp h
    obtain ⟨n₃, m₃, hn₃, hc₃, ho₃, hD₃, hM₃⟩ := exists_minimal_markov m₂
    obtain ⟨T, S, hTS, hST, -⟩ := similar_of_markov_eq hc ho hc₃ ho₃ (hD.trans hD₃.symm)
      fun k => (hM k).trans (hM₃ k).symm
    have hcard := Fintype.card_congr (Matrix.indexEquivOfInv hST hTS)
    simp only [Fintype.card_fin] at hcard
    omega
  · intro h
    by_contra hco
    rcases not_and_or.mp hco with hc | ho
    · obtain ⟨r, m', hr, hD, hM⟩ := reduce_uncontrollable hc
      exact absurd (h r m' (transfer_eq_iff_markov_eq.mpr ⟨hD.symm, fun k => (hM k).symm⟩))
        (by omega)
    · obtain ⟨r, m', hr, hD, hM⟩ := reduce_unobservable ho
      exact absurd (h r m' (transfer_eq_iff_markov_eq.mpr ⟨hD.symm, fun k => (hM k).symm⟩))
        (by omega)

end Minimal

end powerlib.LTI
