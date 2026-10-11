import theorem.Synchronous.Swing
import theorem.PortHamiltonian

/-! # The linearized swing equation as a port-Hamiltonian model

Model boundary: the LTI linearization of the canonical swing model
(`theorem/Synchronous/Swing.lean`) at an equilibrium angle `δ₀` with synchronizing
coefficient `K = k₂ cos(δ₀ − k₃) > 0`, written in the coordinates `(Δδ, M Δω)` (angle deviation,
momentum deviation) with one input `u` entering the momentum equation (a power perturbation,
export-positive) and the collocated output `y = Δω`.  Continuous time; no PLL, delay or PWM.
In these coordinates it is exactly the existing `powerlib.PortHamiltonian.Model` with
`J = [[0, 1], [−1, 0]]`, damping `d = (0, D)`, Hamiltonian weights `w = (K, 1/M)` and
`B = (0, 1)ᵀ`, i.e. `H = ½ K Δδ² + (M Δω)² / (2M)`.

Passivity and Lyapunov stability are not re-proved: they are the existing
`PortHamiltonian.passiveWithStorage` and `PortHamiltonian.lyapunovStable` applied to this
instance (category C, reuse).  `stateMatrix_mul` identifies the pH state matrix with the
swing Jacobian under the change of coordinates `diag(1, M)`.

Source: work-sync theory/T-vsg-control.md §2.9 (pH form `H = ½ J ω² + ½ K_E δ²`, `R = D_p`);
projects/vsc-stochastic-stability/notes/concepts/damping-class-dichotomy.md §2.
-/

noncomputable section
namespace powerlib.Synchronous
open Matrix

namespace SwingParams

variable (p : SwingParams)

/-- The linearized swing equation at `δ₀` in `(Δδ, M Δω)` coordinates as a pH model. -/
def linearPH (δ₀ : ℝ) (hM : 0 < p.M) (hD : 0 ≤ p.D) (hK : 0 < p.syncCoeff δ₀) :
    PortHamiltonian.Model (Fin 2) (Fin 1) where
  J := !![0, 1; -1, 0]
  d := ![0, p.D]
  w := ![p.syncCoeff δ₀, 1 / p.M]
  B := !![0; 1]
  skew := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  damping_nonneg := by
    intro i
    fin_cases i
    · simp
    · simpa using hD
  weights_pos := by
    intro i
    fin_cases i
    · simpa using hK
    · simpa using hM

/-- Coordinate change `(Δδ, Δω) ↦ (Δδ, M Δω)`. -/
def momentumCoord : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, p.M]

/-- The pH state matrix is the swing Jacobian in momentum coordinates:
`A_pH · diag(1, M) = diag(1, M) · J_swing`. -/
@[powerlib_foundation] theorem stateMatrix_mul (δ₀ : ℝ) (hM : 0 < p.M) (hD : 0 ≤ p.D)
    (hK : 0 < p.syncCoeff δ₀) :
    PortHamiltonian.stateMatrix (p.linearPH δ₀ hM hD hK) * p.momentumCoord =
      p.momentumCoord * p.jacobian δ₀ := by
  have hM' := hM.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PortHamiltonian.stateMatrix, linearPH, momentumCoord, jacobian, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.sub_apply] <;> field_simp

/-- The pH field reproduces the linearized swing equation:
`d(Δδ)/dt = Δω`, `d(M Δω)/dt = −K Δδ − D Δω + u` with `x = (Δδ, M Δω)`. -/
@[powerlib_foundation] theorem linearPH_field (δ₀ : ℝ) (hM : 0 < p.M) (hD : 0 ≤ p.D)
    (hK : 0 < p.syncCoeff δ₀) (x : Fin 2 → ℝ) (u : Fin 1 → ℝ) :
    PortHamiltonian.field (p.linearPH δ₀ hM hD hK) x u =
      ![x 1 / p.M, -p.syncCoeff δ₀ * x 0 - p.D * (x 1 / p.M) + u 0] := by
  ext i
  fin_cases i <;>
    simp [PortHamiltonian.field, PortHamiltonian.gradient, linearPH, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.sub_apply] <;> ring

/-- Category C (reuse of `powerlib.PortHamiltonian.passiveWithStorage`): the linearized swing
equation is passive from the power perturbation `u` to `Δω`, with storage `H`. -/
@[powerlib_domain] theorem linearPH_passive (δ₀ : ℝ) (hM : 0 < p.M) (hD : 0 ≤ p.D)
    (hK : 0 < p.syncCoeff δ₀) :
    Passivity.PassiveWithStorage (PortHamiltonian.system (p.linearPH δ₀ hM hD hK))
      (PortHamiltonian.energy (p.linearPH δ₀ hM hD hK)) :=
  PortHamiltonian.passiveWithStorage _

/-- Category C (reuse of `powerlib.PortHamiltonian.lyapunovStable`): the unforced linearized
swing equation is Lyapunov stable for every `D ≥ 0` (including `D = 0`). -/
@[powerlib_domain] theorem linearPH_lyapunovStable (δ₀ : ℝ) (hM : 0 < p.M) (hD : 0 ≤ p.D)
    (hK : 0 < p.syncCoeff δ₀) :
    Passivity.LyapunovStable (PortHamiltonian.system (p.linearPH δ₀ hM hD hK)) :=
  PortHamiltonian.lyapunovStable _

end SwingParams
end powerlib.Synchronous
