import theorem.Port.Linear

/-! # Linear port-Hamiltonian plants

Model boundary: `x' = (J - R) Q x + B u`, `y = Bᵀ Q x`, with a skew-symmetric interconnection
`J`, a symmetric positive semidefinite dissipation `R`, a symmetric positive definite energy
matrix `Q` (stored energy `xᵀ Q x / 2`) and `p` ports. Continuous time with constant matrices;
no switching, delay, saturation or nonlinear element.

The energy matrix is a KYP certificate, so passivity and zero-input Lyapunov stability follow
from the generic theorems of `Port.Linear`; nothing about trajectories is restated here. -/

noncomputable section

namespace powerlib.Port

open Matrix LinearSystems

variable {n p : ℕ}

/-- A linear port-Hamiltonian plant. -/
structure PortHamiltonian (n p : ℕ) where
  J : Matrix (Fin n) (Fin n) ℝ
  R : Matrix (Fin n) (Fin n) ℝ
  Q : Matrix (Fin n) (Fin n) ℝ
  B : Matrix (Fin n) (Fin p) ℝ
  skew : Jᵀ = -J
  dissipation_symmetric : Rᵀ = R
  dissipation_nonneg : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (R *ᵥ x)
  energy_symmetric : Qᵀ = Q
  energy_pos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (Q *ᵥ x)

/-- The linear plant of a port-Hamiltonian system. -/
def PortHamiltonian.plant (h : PortHamiltonian n p) : Linear.Plant n p :=
  ⟨(h.J - h.R) * h.Q, h.B, h.Bᵀ * h.Q, 0⟩

/-- The energy matrix is a KYP certificate. -/
def PortHamiltonian.kyp (h : PortHamiltonian n p) : Linear.KYP h.plant where
  P := h.Q
  symmetric := h.energy_symmetric
  nonneg x := by
    by_cases hx : x = 0
    · simp [hx]
    · exact (h.energy_pos x hx).le
  dissipation x := by
    have hA : h.plant.Aᵀ * h.Q + h.Q * h.plant.A = -(h.Q * h.R * h.Q) - h.Q * h.R * h.Q := by
      simp only [PortHamiltonian.plant, Matrix.transpose_mul, Matrix.transpose_sub, h.skew,
        h.dissipation_symmetric, h.energy_symmetric]
      noncomm_ring
    have hQ : x ⬝ᵥ (h.Q *ᵥ (h.R *ᵥ (h.Q *ᵥ x))) = (h.Q *ᵥ x) ⬝ᵥ (h.R *ᵥ (h.Q *ᵥ x)) := by
      rw [Matrix.dotProduct_mulVec]
      congr 1
      conv_lhs => rw [← h.energy_symmetric]
      rw [Matrix.vecMul_transpose]
    rw [hA, Matrix.sub_mulVec, Matrix.neg_mulVec, dotProduct_sub, dotProduct_neg,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQ]
    linarith [h.dissipation_nonneg (h.Q *ᵥ x)]
  output := rfl
  feedthrough u := by simp [PortHamiltonian.plant]

/-- Port-Hamiltonian plants are passive with their stored energy. -/
@[powerlib_foundation] theorem PortHamiltonian.passiveWith (h : PortHamiltonian n p) :
    h.plant.system.PassiveWith h.kyp.storage :=
  h.kyp.passiveWith

/-- With the ports at zero, port-Hamiltonian plants are Lyapunov stable. -/
@[powerlib_foundation] theorem PortHamiltonian.lyapunovStable (h : PortHamiltonian n p) :
    LyapunovStable (affineLinearVectorField h.plant.A 0) 0 :=
  h.kyp.lyapunovStable_of_pos h.energy_pos

end powerlib.Port
