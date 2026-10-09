import dependencies.Mathlib
import theorem.StateSpacePassivity
import theorem.StateSpaceTrajectories

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
  ⟨field m, fun x _ => output m x⟩

def energy (m : Model ι κ) (x : State ι) : ℝ :=
  ∑ i, m.w i * x i ^ 2 / 2

def dampingPower (m : Model ι κ) (x : State ι) : ℝ :=
  ∑ i, m.d i * (gradient m x i) ^ 2

def stateMatrix (m : Model ι κ) : Matrix ι ι ℝ :=
  (m.J - diagonal m.d) * diagonal m.w

def linearModel (m : Model ι κ) : LTI.Model ι κ where
  A := stateMatrix m
  B := m.B
  C := m.B.transpose * diagonal m.w
  D := 0

omit [Fintype κ] in
@[simp, powerlib_foundation] theorem diagonal_mulVec_gradient (m : Model ι κ)
    (x : State ι) : (diagonal m.w).mulVec x = gradient m x := by
  ext i
  exact mulVec_diagonal m.w x i

@[simp, powerlib_foundation] theorem linearModel_field (m : Model ι κ)
    (x : State ι) (u : κ → ℝ) :
    LTI.Model.field (linearModel m) x u = field m x u := by
  simp only [LTI.Model.field, linearModel, stateMatrix, field,
    ← mulVec_mulVec, diagonal_mulVec_gradient]

@[simp, powerlib_foundation] theorem linearModel_output (m : Model ι κ)
    (x : State ι) (u : κ → ℝ) :
    LTI.Model.output (linearModel m) x u = output m x := by
  simp only [LTI.Model.output, linearModel, output, zero_mulVec, add_zero,
    ← mulVec_mulVec, diagonal_mulVec_gradient]

@[simp, powerlib_foundation] theorem system_eq (m : Model ι κ) :
    StateSpacePassivity.system (linearModel m) = system m := by
  exact congrArg₂ Passivity.System.mk
    (funext fun x => funext fun u => linearModel_field m x u)
    (funext fun x => funext fun u => linearModel_output m x u)

omit [Fintype κ] in
@[simp, powerlib_foundation] theorem energy_eq (m : Model ι κ) (x : State ι) :
    StateSpacePassivity.energy (diagonal m.w) x = energy m x := by
  simp only [StateSpacePassivity.energy, LTI.energy, energy, dotProduct, Finset.sum_div,
    mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fintype κ] in
@[simp, powerlib_foundation] theorem energy_fun_eq (m : Model ι κ) :
    StateSpacePassivity.energy (diagonal m.w) = energy m := funext (energy_eq m)

omit [Fintype κ] in
@[powerlib_foundation] theorem dissipation_matrix (m : Model ι κ) :
    -(diagonal m.w * stateMatrix m + (stateMatrix m).transpose * diagonal m.w) =
      diagonal (fun i => 2 * m.d i * m.w i ^ 2) := by
  ext i j
  have hs : m.J j i = -m.J i j := congrFun (congrFun m.skew i) j
  by_cases hij : i = j
  · subst j
    have hJii : m.J i i = 0 := by linarith
    simp [stateMatrix, diagonal_mul, mul_diagonal, transpose_apply, hJii]
    ring
  · simp [stateMatrix, diagonal_mul, mul_diagonal, transpose_apply, hs, hij]
    ring

def collocatedCertificate (m : Model ι κ) :
    StateSpacePassivity.CollocatedCertificate (linearModel m) where
  P := diagonal m.w
  positive := Matrix.PosDef.diagonal m.weights_pos
  dissipation := by
    change (-(diagonal m.w * stateMatrix m +
      (stateMatrix m).transpose * diagonal m.w)).PosSemidef
    rw [dissipation_matrix]
    exact Matrix.PosSemidef.diagonal (fun i =>
      mul_nonneg (mul_nonneg (by norm_num) (m.damping_nonneg i)) (sq_nonneg _))
  collocated := by
    simp only [linearModel, transpose_mul, transpose_transpose, diagonal_transpose]
  feedthrough := Matrix.PosSemidef.zero

def certificate (m : Model ι κ) : StateSpacePassivity.Certificate (linearModel m) :=
  (collocatedCertificate m).toCertificate

@[simp, powerlib_foundation] theorem certificate_P (m : Model ι κ) :
    (certificate m).P = diagonal m.w := rfl

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
@[simp, powerlib_foundation] theorem gradient_zero (m : Model ι κ) : gradient m 0 = 0 := by
  ext i
  simp [gradient]

@[simp, powerlib_foundation] theorem zero_equilibrium (m : Model ι κ) :
    Passivity.IsEquilibrium (system m) 0 := by
  simpa only [system_eq] using StateSpacePassivity.zero_equilibrium (linearModel m)

omit [DecidableEq ι] [Fintype κ] in
@[simp, powerlib_foundation] theorem energy_zero (m : Model ι κ) : energy m 0 = 0 := by
  classical
  simpa only [energy_eq] using StateSpacePassivity.energy_zero (diagonal m.w)

omit [DecidableEq ι] [Fintype κ] in
@[powerlib_foundation] theorem energy_continuous (m : Model ι κ) : Continuous (energy m) := by
  classical
  simpa only [energy_fun_eq] using StateSpacePassivity.energy_continuous (diagonal m.w)

omit [DecidableEq ι] [Fintype κ] in
@[powerlib_foundation] theorem energy_smul (m : Model ι κ) (a : ℝ) (x : State ι) :
    energy m (a • x) = a ^ 2 * energy m x := by
  classical
  simpa only [energy_eq] using StateSpacePassivity.energy_smul (diagonal m.w) a x

omit [DecidableEq ι] [Fintype κ] in
@[powerlib_foundation, aesop safe apply] theorem energy_positive (m : Model ι κ) (x : State ι) (hx : x ≠ 0) :
    0 < energy m x := by
  classical
  simpa only [energy_eq] using
    StateSpacePassivity.energy_positive (Matrix.PosDef.diagonal m.weights_pos) x hx

omit [DecidableEq ι] [Fintype κ] in
@[powerlib_foundation, aesop safe apply] theorem dampingPower_nonneg (m : Model ι κ) (x : State ι) :
    0 ≤ dampingPower m x :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (m.damping_nonneg i) (sq_nonneg _))

omit [DecidableEq ι] [Fintype κ] in
@[powerlib_foundation] theorem energy_derivative (m : Model ι κ)
    {x : ℝ → State ι} {dx : State ι} {t : ℝ}
    (hx : HasDerivWithinAt x dx (Ici 0) t) :
    HasDerivWithinAt (fun τ => energy m (x τ))
      (dotProduct (gradient m (x t)) dx) (Ici 0) t := by
  classical
  simpa only [energy_eq, diagonal_mulVec_gradient] using
    StateSpacePassivity.energy_derivative (diagonal m.w) (diagonal_transpose m.w) hx

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

def storage (m : Model ι κ) : Passivity.QuadraticStorage (system m) where
  energy := energy m
  rate := (certificate m).storage.rate
  energyDerivative := fun {u} {x} hx {t} ht => by
    have hg : Passivity.IsTrajectory (StateSpacePassivity.system (linearModel m)) u x := by
      simpa only [system_eq] using hx
    simpa only [StateSpacePassivity.Certificate.storage, certificate_P, energy_eq] using
      (certificate m).storage.energyDerivative hg ht
  dissipation := fun x u => by
    simpa only [system_eq] using (certificate m).storage.dissipation x u
  continuous := energy_continuous m
  homogeneous := energy_smul m
  positive := energy_positive m

@[powerlib_domain, aesop safe apply] theorem passiveWithStorage (m : Model ι κ) :
    Passivity.PassiveWithStorage (system m) (energy m) := by
  simpa only [system_eq, certificate_P, energy_fun_eq] using (certificate m).passiveWithStorage

@[powerlib_domain] theorem integral_passivity (m : Model ι κ)
    {u : ℝ → (κ → ℝ)} {x : ℝ → State ι}
    (hx : Passivity.IsTrajectory (system m) u x) {t : ℝ} (ht : 0 ≤ t)
    (hsupply : IntervalIntegrable (fun τ => Passivity.supply (system m) (x τ) (u τ))
      MeasureTheory.volume 0 t) :
    energy m (x t) - energy m (x 0) ≤
      ∫ τ in (0 : ℝ)..t, Passivity.supply (system m) (x τ) (u τ) := by
  have hg : Passivity.IsTrajectory (StateSpacePassivity.system (linearModel m)) u x := by
    simpa only [system_eq] using hx
  have hp : IntervalIntegrable (fun τ => Passivity.supply
      (StateSpacePassivity.system (linearModel m)) (x τ) (u τ)) MeasureTheory.volume 0 t := by
    simpa only [system_eq] using hsupply
  simpa only [system_eq, certificate_P, energy_eq] using
    (certificate m).integral_passivity hg ht hp

@[powerlib_domain] theorem zeroInput_energy_antitone (m : Model ι κ)
    {x : ℝ → State ι} (hx : Passivity.IsTrajectory (system m) (fun _ => 0) x) :
    AntitoneOn (fun t => energy m (x t)) (Ici 0) := by
  have hg : Passivity.IsTrajectory (StateSpacePassivity.system (linearModel m)) (fun _ => 0) x := by
    simpa only [system_eq] using hx
  simpa only [certificate_P, energy_eq] using (certificate m).zeroInput_energy_antitone hg

@[powerlib_domain, aesop safe apply] theorem lyapunovStable [Nonempty ι] (m : Model ι κ) :
    Passivity.LyapunovStable (system m) := by
  simpa only [system_eq] using (certificate m).lyapunovStable

def operator (m : Model ι κ) : State ι →L[ℝ] State ι :=
  (linearModel m).operator

@[powerlib_foundation] theorem operator_field (m : Model ι κ) (x : State ι) :
    operator m x = field m x 0 := by
  simpa only [operator, linearModel_field] using
    (linearModel m).operator_field x

def response (m : Model ι κ) (initial : State ι) (t : ℝ) : State ι :=
  (linearModel m).response initial t

omit [Fintype κ] in
@[simp, powerlib_foundation] theorem response_initial (m : Model ι κ) (initial : State ι) :
    response m initial 0 = initial :=
  (linearModel m).response_initial initial

omit [Fintype κ] in
@[powerlib_domain, aesop safe apply] theorem response_solves (m : Model ι κ) (initial : State ι) (t : ℝ) :
    HasDerivAt (response m initial) (operator m (response m initial t)) t :=
  (linearModel m).response_solves initial t

@[powerlib_domain, aesop safe apply] theorem response_trajectory (m : Model ι κ) (initial : State ι) :
    Passivity.IsTrajectory (system m) (fun _ => 0) (response m initial) := by
  simpa only [system_eq, response] using!
    StateSpacePassivity.response_trajectory (linearModel m) initial

@[powerlib_domain, aesop safe apply] theorem trajectory_exists (m : Model ι κ) (initial : State ι) :
    ∃ x, Passivity.IsTrajectory (system m) (fun _ => 0) x ∧ x 0 = initial := by
  simpa only [system_eq] using StateSpacePassivity.trajectory_exists (linearModel m) initial

@[powerlib_domain] theorem trajectory_unique (m : Model ι κ)
    {x y : ℝ → State ι}
    (hx : Passivity.IsTrajectory (system m) (fun _ => 0) x)
    (hy : Passivity.IsTrajectory (system m) (fun _ => 0) y) (h0 : x 0 = y 0) :
    EqOn x y (Ici 0) := by
  have hgx : Passivity.IsTrajectory (StateSpacePassivity.system (linearModel m)) (fun _ => 0) x := by
    simpa only [system_eq] using hx
  have hgy : Passivity.IsTrajectory (StateSpacePassivity.system (linearModel m)) (fun _ => 0) y := by
    simpa only [system_eq] using hy
  exact StateSpacePassivity.trajectory_unique (linearModel m) hgx hgy h0

@[powerlib_domain] theorem trajectory_eq_response (m : Model ι κ)
    {x : ℝ → State ι} (hx : Passivity.IsTrajectory (system m) (fun _ => 0) x)
    {t : ℝ} (ht : 0 ≤ t) : x t = response m (x 0) t := by
  have hg : Passivity.IsTrajectory (StateSpacePassivity.system (linearModel m)) (fun _ => 0) x := by
    simpa only [system_eq] using hx
  exact StateSpacePassivity.trajectory_eq_response (linearModel m) hg ht

end powerlib.PortHamiltonian
