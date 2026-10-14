import theorem.Synchronous.Swing
import theorem.Port.PortHamiltonian

/-! # The linearized swing equation as a port-Hamiltonian model

Model boundary: the LTI linearization of the canonical swing model
(`theorem/Synchronous/Swing.lean`) at an equilibrium angle `δ₀` with synchronizing
coefficient `K = k₂ cos(δ₀ − k₃) > 0`, written in the coordinates `(Δδ, M Δω)` (angle deviation,
momentum deviation) with one input `u` entering the momentum equation (a power perturbation,
export-positive) and the collocated output `y = Δω`.  Continuous time; no PLL, delay or PWM.
In these coordinates it is exactly a linear port-Hamiltonian plant `Port.PortHamiltonian 2 1`
(`theorem/Port/PortHamiltonian.lean`) with `J = [[0, 1], [−1, 0]]`, dissipation
`R = diag(0, D)`, energy matrix `Q = diag(K, 1/M)` and `B = (0, 1)ᵀ`, i.e.
`H = ½ K Δδ² + (M Δω)² / (2M)`.

Family and connection conclusions. No new family: the plant is a member of the
port-Hamiltonian family `Port.PortHamiltonian.family`. Passivity and Lyapunov stability are not
re-proved: they are the family's `mem_den_passive` and `mem_den_lyapunovStable` applied to this
plant (`linearPH_passive`, `linearPH_lyapunovStable`, connection statements; reuse).
`stateMatrix_mul` identifies the pH state matrix with the swing Jacobian under the change of
coordinates `diag(1, M)`; through it every flow sentence of the pH plant is the same sentence of
the linearized swing family `Synchronous.Swing.Linearized.family` at `(p, δ₀)`
(`linearPH_mem_den_flow_iff`, a comparison of the two families' denotations).

Source: work-sync theory/T-vsg-control.md §2.9 (pH form `H = ½ J ω² + ½ K_E δ²`, `R = D_p`);
projects/vsc-stochastic-stability/notes/concepts/damping-class-dichotomy.md §2.
-/

noncomputable section
namespace powerlib.Synchronous
open Matrix
open powerlib.Dynamics (State)

namespace SwingParams

variable (p : SwingParams)

/-- The linearized swing equation at `δ₀` in `(Δδ, M Δω)` coordinates as a pH plant. -/
def linearPH (δ₀ : ℝ) (hM : 0 < p.M) (hD : 0 ≤ p.D) (hK : 0 < p.syncCoeff δ₀) :
    Port.PortHamiltonian 2 1 where
  J := !![0, 1; -1, 0]
  R := !![0, 0; 0, p.D]
  Q := !![p.syncCoeff δ₀, 0; 0, 1 / p.M]
  B := !![0; 1]
  skew := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  dissipation_symmetric := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  dissipation_nonneg := by
    intro x
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    nlinarith [mul_nonneg hD (mul_self_nonneg (x 1))]
  energy_symmetric := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  energy_pos := by
    intro x hx
    have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hx (funext fun i => by fin_cases i <;> simp [hc.1, hc.2])
    have hM' : 0 < 1 / p.M := one_div_pos.mpr hM
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    rcases hx' with h0 | h1
    · have : 0 < x 0 * x 0 := mul_self_pos.mpr h0
      nlinarith [mul_nonneg hM'.le (mul_self_nonneg (x 1))]
    · have : 0 < x 1 * x 1 := mul_self_pos.mpr h1
      nlinarith [mul_nonneg hK.le (mul_self_nonneg (x 0))]

/-- Coordinate change `(Δδ, Δω) ↦ (Δδ, M Δω)`. -/
def momentumCoord : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, p.M]

/-- The pH state matrix is the swing Jacobian in momentum coordinates:
`A_pH · diag(1, M) = diag(1, M) · J_swing`. -/
@[powerlib_foundation] theorem stateMatrix_mul (δ₀ : ℝ) (hM : 0 < p.M) (hD : 0 ≤ p.D)
    (hK : 0 < p.syncCoeff δ₀) :
    (p.linearPH δ₀ hM hD hK).plant.A * p.momentumCoord = p.momentumCoord * p.jacobian δ₀ := by
  have hM' := hM.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Port.PortHamiltonian.plant, linearPH, momentumCoord, jacobian, Matrix.mul_apply,
      Fin.sum_univ_two] <;> field_simp

/-- The pH state matrix is the swing Jacobian conjugated by the momentum coordinates. -/
@[powerlib_foundation] theorem stateMatrix_eq_conj (δ₀ : ℝ) (hM : 0 < p.M) (hD : 0 ≤ p.D)
    (hK : 0 < p.syncCoeff δ₀) :
    (p.linearPH δ₀ hM hD hK).plant.A =
      p.momentumCoord * p.jacobian δ₀ * !![1, 0; 0, 1 / p.M] := by
  have hM' := hM.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Port.PortHamiltonian.plant, linearPH, momentumCoord, jacobian, Matrix.mul_apply,
      Fin.sum_univ_two] <;> field_simp

/-- The pH field reproduces the linearized swing equation:
`d(Δδ)/dt = Δω`, `d(M Δω)/dt = −K Δδ − D Δω + u` with `x = (Δδ, M Δω)`. -/
@[powerlib_foundation] theorem linearPH_field (δ₀ : ℝ) (hM : 0 < p.M) (hD : 0 ≤ p.D)
    (hK : 0 < p.syncCoeff δ₀) (x : State 2) (u : Fin 1 → ℝ) :
    (p.linearPH δ₀ hM hD hK).plant.system.field x u =
      PhasePlane.mk (x 1 / p.M) (-p.syncCoeff δ₀ * x 0 - p.D * (x 1 / p.M) + u 0) := by
  refine PhasePlane.ext_iff'.2 ⟨?_, ?_⟩
  · simp [Linear.Plant.system, Port.PortHamiltonian.plant, linearPH, PhasePlane.toEuclideanCLM_apply_zero,
      dotProduct]
    ring
  · simp [Linear.Plant.system, Port.PortHamiltonian.plant, linearPH, PhasePlane.toEuclideanCLM_apply_one,
      dotProduct]
    ring

/-- Reuse of the port-Hamiltonian family: the linearized swing equation is passive from the power
perturbation `u` to `Δω`, with storage `H`. -/
@[powerlib_domain] theorem linearPH_passive (δ₀ : ℝ) (hM : 0 < p.M) (hD : 0 ≤ p.D)
    (hK : 0 < p.syncCoeff δ₀) :
    connection% (p.linearPH δ₀ hM hD hK ∈ Port.PortHamiltonian.family.den .passive) :=
  Port.PortHamiltonian.mem_den_passive _

/-- Reuse of the port-Hamiltonian family: the unforced linearized swing equation is Lyapunov
stable for every `D ≥ 0` (including `D = 0`). -/
@[powerlib_domain] theorem linearPH_lyapunovStable (δ₀ : ℝ) (hM : 0 < p.M) (hD : 0 ≤ p.D)
    (hK : 0 < p.syncCoeff δ₀) :
    connection% (p.linearPH δ₀ hM hD hK ∈ Port.PortHamiltonian.family.den (.flow .lyapunovStable)) :=
  Port.PortHamiltonian.mem_den_lyapunovStable _

/-- Every flow sentence of the pH plant is the same sentence of the linearized swing family at
`(p, δ₀)`: the two families' denotations agree through the momentum coordinates. -/
@[powerlib_domain] theorem linearPH_mem_den_flow_iff (δ₀ : ℝ) (hM : 0 < p.M) (hD : 0 ≤ p.D)
    (hK : 0 < p.syncCoeff δ₀) (P : Flow.Property) :
    connection% (p.linearPH δ₀ hM hD hK ∈ Port.PortHamiltonian.family.den (.flow P) ↔
      Swing.Model.mk p δ₀ ∈ Swing.Linearized.family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  have hM' := hM.ne'
  have hTS : p.momentumCoord * !![1, 0; 0, 1 / p.M] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [momentumCoord, Matrix.mul_apply, Fin.sum_univ_two, hM']
  have hST : !![1, 0; 0, 1 / p.M] * p.momentumCoord = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [momentumCoord, Matrix.mul_apply, Fin.sum_univ_two, hM']
  rw [Port.PortHamiltonian.family_isLinear.mem_den_flow,
    Swing.Linearized.family_isLinear.mem_den_flow, p.stateMatrix_eq_conj δ₀ hM hD hK]
  exact Linear.holds_conj P hTS hST _

end SwingParams
end powerlib.Synchronous
