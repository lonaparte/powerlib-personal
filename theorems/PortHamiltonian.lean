import theorems.Passivity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.ODE.Gronwall

/-!
Finite-dimensional constant-coefficient continuous-time port-Hamiltonian ODEs.
States are indexed real coordinates, ports are indexed real effort inputs with
collocated flow outputs. The original constitutive model supplies positive
diagonal energy weights, nonnegative diagonal dissipation, a skew interconnection
matrix, and an arbitrary constant port matrix. Its equation is
`x' = (J - diag d) diag w x + B u`, and `y = Bᵀ diag w x`.

The physical storage `H = ∑ i, w i * x i ^ 2 / 2` is constructed from these
constitutive parameters. The model includes no nonlinear, descriptor/algebraic,
sampled, delayed, switching, or additional controller dynamics. Stability is of
the origin under zero port input; no strict decay or asymptotic claim follows
from the allowed semidefinite damping.
-/
noncomputable section
namespace powerlib.PortHamiltonian
open Set Filter Matrix
open scoped Topology

abbrev State (ι : Type*) := ι → ℝ

structure Model (ι κ : Type*) where
  J : Matrix ι ι ℝ
  d : ι → ℝ
  w : ι → ℝ
  B : Matrix ι κ ℝ
  skew : J.transpose = -J
  damping_nonneg : ∀ i, 0 ≤ d i
  weights_pos : ∀ i, 0 < w i

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

def gradient (m : Model ι κ) (x : State ι) : State ι := fun i => m.w i * x i

def field (m : Model ι κ) (x : State ι) (u : κ → ℝ) : State ι :=
  (m.J - diagonal m.d).mulVec (gradient m x) + m.B.mulVec u

def output (m : Model ι κ) (x : State ι) : κ → ℝ :=
  m.B.transpose.mulVec (gradient m x)

def system (m : Model ι κ) : Passivity.System (State ι) κ :=
  ⟨field m, output m⟩

def energy (m : Model ι κ) (x : State ι) : ℝ :=
  ∑ i, m.w i * x i ^ 2 / 2

def dampingPower (m : Model ι κ) (x : State ι) : ℝ :=
  ∑ i, m.d i * (gradient m x i) ^ 2

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
@[simp, powerlib_foundation] theorem gradient_zero (m : Model ι κ) : gradient m 0 = 0 := by
  ext i
  simp [gradient]

@[simp, powerlib_foundation] theorem zero_equilibrium (m : Model ι κ) :
    Passivity.IsEquilibrium (system m) 0 := by
  simp [Passivity.IsEquilibrium, system, field]

omit [DecidableEq ι] [Fintype κ] in
@[simp, powerlib_foundation] theorem energy_zero (m : Model ι κ) : energy m 0 = 0 := by
  simp [energy]

omit [DecidableEq ι] [Fintype κ] in
@[powerlib_foundation] theorem energy_continuous (m : Model ι κ) : Continuous (energy m) := by
  unfold energy
  fun_prop

omit [DecidableEq ι] [Fintype κ] in
@[powerlib_foundation] theorem energy_smul (m : Model ι κ) (a : ℝ) (x : State ι) :
    energy m (a • x) = a ^ 2 * energy m x := by
  simp only [energy, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [DecidableEq ι] [Fintype κ] in
@[powerlib_foundation] theorem energy_positive (m : Model ι κ) (x : State ι) (hx : x ≠ 0) :
    0 < energy m x := by
  have hnonneg : ∀ i, 0 ≤ m.w i * x i ^ 2 / 2 := fun i => by
    exact div_nonneg (mul_nonneg (m.weights_pos i).le (sq_nonneg _)) (by norm_num)
  have hsome : ∃ i, x i ≠ 0 := by
    exact Function.ne_iff.mp hx
  obtain ⟨i, hi⟩ := hsome
  apply Finset.sum_pos' (fun j _ => hnonneg j)
  exact ⟨i, Finset.mem_univ i, div_pos (mul_pos (m.weights_pos i) (sq_pos_of_ne_zero hi))
    (by norm_num)⟩

omit [DecidableEq ι] [Fintype κ] in
@[powerlib_foundation] theorem dampingPower_nonneg (m : Model ι κ) (x : State ι) :
    0 ≤ dampingPower m x :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (m.damping_nonneg i) (sq_nonneg _))

omit [DecidableEq ι] [Fintype κ] in
@[powerlib_foundation] theorem energy_derivative (m : Model ι κ)
    {x : ℝ → State ι} {dx : State ι} {t : ℝ}
    (hx : HasDerivWithinAt x dx (Ici 0) t) :
    HasDerivWithinAt (fun τ => energy m (x τ))
      (dotProduct (gradient m (x t)) dx) (Ici 0) t := by
  have hd (i : ι) : HasDerivWithinAt (fun τ => x τ i) (dx i) (Ici 0) t :=
    (ContinuousLinearMap.proj i : State ι →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t hx
  have hsum := HasDerivWithinAt.sum (u := Finset.univ)
    (fun i _ => (((hd i).pow 2).const_mul (m.w i)).div_const 2)
  convert hsum using 1
  dsimp [dotProduct, gradient]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[powerlib_foundation] theorem power_balance (m : Model ι κ) (x : State ι) (u : κ → ℝ) :
    dotProduct (gradient m x) (field m x u) =
      Passivity.supply (system m) x u - dampingPower m x := by
  have hskew : dotProduct (gradient m x) (m.J.mulVec (gradient m x)) = 0 := by
    have h : dotProduct (gradient m x) (m.J.mulVec (gradient m x)) =
        -dotProduct (gradient m x) (m.J.mulVec (gradient m x)) := by
      calc
        _ = dotProduct (m.J.transpose.mulVec (gradient m x)) (gradient m x) := by
          rw [dotProduct_mulVec, mulVec_transpose]
        _ = _ := by rw [m.skew, neg_mulVec, neg_dotProduct, dotProduct_comm]
    linarith
  have hport : dotProduct (gradient m x) (m.B.mulVec u) =
      Passivity.supply (system m) x u := by
    change dotProduct (gradient m x) (m.B.mulVec u) =
      dotProduct u (m.B.transpose.mulVec (gradient m x))
    rw [dotProduct_mulVec, mulVec_transpose, dotProduct_comm]
  have hdamping : dotProduct (gradient m x) ((diagonal m.d).mulVec (gradient m x)) =
      dampingPower m x := by
    simp only [dotProduct, mulVec_diagonal, dampingPower]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [field, sub_mulVec, dotProduct_add, dotProduct_sub, hskew, hport, hdamping]
  ring

@[powerlib_domain] theorem trajectory_energy_derivative (m : Model ι κ)
    {u : ℝ → (κ → ℝ)} {x : ℝ → State ι}
    (hx : Passivity.IsTrajectory (system m) u x) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun τ => energy m (x τ))
      (Passivity.supply (system m) (x t) (u t) - dampingPower m (x t)) (Ici 0) t := by
  simpa only [system, power_balance] using energy_derivative m (hx t ht)

/-- The storage is derived from constitutive model data, without an external
Lyapunov or passivity certificate. -/
def storage (m : Model ι κ) : Passivity.QuadraticStorage (system m) where
  energy := energy m
  rate := fun x u => Passivity.supply (system m) x u - dampingPower m x
  energyDerivative := trajectory_energy_derivative m
  dissipation := fun x _ => sub_le_self _ (dampingPower_nonneg m x)
  continuous := energy_continuous m
  homogeneous := energy_smul m
  positive := energy_positive m

@[powerlib_domain, aesop safe apply] theorem passiveWithStorage (m : Model ι κ) :
    Passivity.PassiveWithStorage (system m) (energy m) :=
  (storage m).passiveWithStorage

@[powerlib_domain] theorem integral_passivity (m : Model ι κ)
    {u : ℝ → (κ → ℝ)} {x : ℝ → State ι}
    (hx : Passivity.IsTrajectory (system m) u x) {t : ℝ} (ht : 0 ≤ t)
    (hsupply : IntervalIntegrable (fun τ => Passivity.supply (system m) (x τ) (u τ))
      MeasureTheory.volume 0 t) :
    energy m (x t) - energy m (x 0) ≤
      ∫ τ in (0 : ℝ)..t, Passivity.supply (system m) (x τ) (u τ) :=
  (storage m).integral_passivity hx ht hsupply

@[powerlib_domain] theorem zeroInput_energy_antitone (m : Model ι κ)
    {x : ℝ → State ι} (hx : Passivity.IsTrajectory (system m) (fun _ => 0) x) :
    AntitoneOn (fun t => energy m (x t)) (Ici 0) :=
  (storage m).toDissipativeStorage.zeroInput_energy_antitone hx

@[powerlib_domain, aesop safe apply] theorem lyapunovStable [Nonempty ι] (m : Model ι κ) :
    Passivity.LyapunovStable (system m) :=
  (storage m).lyapunovStable (zero_equilibrium m)

def stateMatrix (m : Model ι κ) : Matrix ι ι ℝ :=
  (m.J - diagonal m.d) * diagonal m.w

def operator (m : Model ι κ) : State ι →L[ℝ] State ι :=
  (Matrix.toLin' (stateMatrix m)).toContinuousLinearMap

@[powerlib_foundation] theorem operator_field (m : Model ι κ) (x : State ι) :
    operator m x = field m x 0 := by
  change (stateMatrix m).mulVec x = field m x 0
  simp only [stateMatrix, field, mulVec_zero, add_zero]
  rw [← mulVec_mulVec]
  have hw : (diagonal m.w).mulVec x = gradient m x := by
    ext i
    exact mulVec_diagonal m.w x i
  rw [hw]

def response (m : Model ι κ) (initial : State ι) (t : ℝ) : State ι :=
  (NormedSpace.exp ℝ (t • operator m)) initial

omit [Fintype κ] in
@[simp, powerlib_domain] theorem response_initial (m : Model ι κ) (initial : State ι) :
    response m initial 0 = initial := by
  simp [response, NormedSpace.exp_zero]

omit [Fintype κ] in
@[powerlib_domain] theorem response_solves (m : Model ι κ) (initial : State ι) (t : ℝ) :
    HasDerivAt (response m initial) (operator m (response m initial t)) t := by
  have h := (hasDerivAt_exp_smul_const' (operator m) t).clm_apply
    (hasDerivAt_const t initial)
  simpa [response, ContinuousLinearMap.mul_apply] using h

@[powerlib_domain] theorem response_trajectory (m : Model ι κ) (initial : State ι) :
    Passivity.IsTrajectory (system m) (fun _ => 0) (response m initial) := by
  intro t _
  simpa only [operator_field, system] using (response_solves m initial t).hasDerivWithinAt

@[powerlib_domain] theorem trajectory_exists (m : Model ι κ) (initial : State ι) :
    ∃ x, Passivity.IsTrajectory (system m) (fun _ => 0) x ∧ x 0 = initial :=
  ⟨response m initial, response_trajectory m initial, response_initial m initial⟩

@[powerlib_domain] theorem trajectory_unique (m : Model ι κ)
    {x y : ℝ → State ι}
    (hx : Passivity.IsTrajectory (system m) (fun _ => 0) x)
    (hy : Passivity.IsTrajectory (system m) (fun _ => 0) y) (h0 : x 0 = y 0) :
    EqOn x y (Ici 0) := by
  intro t ht
  have hc (z : ℝ → State ι) (hz : Passivity.IsTrajectory (system m) (fun _ => 0) z) :
      ContinuousOn z (Icc 0 t) := by
    intro r hr
    exact (hz r hr.1).continuousWithinAt.mono (fun _ hh => hh.1)
  have hd (z : ℝ → State ι) (hz : Passivity.IsTrajectory (system m) (fun _ => 0) z) :
      ∀ r ∈ Ico 0 t, HasDerivWithinAt z (operator m (z r)) (Ici r) r := by
    intro r hr
    rw [operator_field]
    exact (hz r hr.1).mono (fun _ hh => hr.1.trans hh)
  exact ODE_solution_unique (v := fun _ => operator m) (fun _ => (operator m).lipschitz)
    (hc x hx) (hd x hx) (hc y hy) (hd y hy) h0 ⟨ht, le_rfl⟩

@[powerlib_domain] theorem trajectory_eq_response (m : Model ι κ)
    {x : ℝ → State ι} (hx : Passivity.IsTrajectory (system m) (fun _ => 0) x)
    {t : ℝ} (ht : 0 ≤ t) : x t = response m (x 0) t :=
  trajectory_unique m hx (response_trajectory m (x 0)) (response_initial m (x 0)).symm ht

end powerlib.PortHamiltonian
