import theorem.TMIO.ClaimElab
import theorem.Linear.Family

/-! # Linear port-Hamiltonian plants

The energy matrix is a KYP certificate, so passivity and zero-input Lyapunov stability follow
from the generic theorems of `Port.Linear`; nothing about trajectories is restated here.

Model boundary.
* `x' = (J - R) Q x + B u`, `y = Bᵀ Q x`, with a skew-symmetric interconnection `J`, a symmetric
  positive semidefinite dissipation `R`, a symmetric positive definite energy matrix `Q` (stored
  energy `xᵀ Q x / 2`) and `p` ports.
* Continuous time with constant matrices; no switching, delay, saturation or nonlinear element.

Source: the KYP certificates of `theorem/Port/Linear.lean` (`KYP.passiveWith`,
`KYP.lyapunovStable_of_pos`) and the linear family laws of `theorem/Linear/Family.lean`
(`Family.IsLinear.mem_den_passive`, `Family.IsLinear.den_hurwitz`).

Results.
* Static: `PortHamiltonian` (`J`, `R`, `Q`, `B` and their structure), `PortHamiltonian.plant`,
  `PortHamiltonian.kyp` (the energy matrix is a KYP certificate), `Requirement`, `Meets`,
  `translate`, `family_isLinear`.

Family and connection conclusions.
* `Port.PortHamiltonian.family : Family (PortHamiltonian n p) Requirement n p`: requirements
  `hurwitz` and `impossible` (the structure fields already enforce passivity and positive stored
  energy). Passivity and Lyapunov stability translate into nothing, the attractive sentences and
  sampled contraction into `hurwitz`, instability, decay rates and conservation into the whole,
  inconsistent, language.
* `mem_den_passive`: stored energy places each submitted plant in the passivity denotation;
  `mem_den_lyapunovStable`: positive stored energy places it in the zero-input stability
  denotation.
* `chain_le_semantics`: the translation chain is sound for every sentence.
-/

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

namespace PortHamiltonian

/-- Static requirements of the port-Hamiltonian family. Structure fields already enforce
passivity and positive stored energy; unavailable sentences use an inconsistent language. -/
inductive Requirement
  | hurwitz
  | impossible

def Meets (h : PortHamiltonian n p) : Requirement → Prop
  | .hurwitz => IsHurwitz h.plant.A
  | .impossible => False

def translate : Sentence → Set Requirement
  | .passive | .flow .lyapunovStable => ∅
  | .flow .unstable | .flow (.decay _) | .flow .conservative => Set.univ
  | .flow _ => {.hurwitz}
  | .envelope _ => ∅

def family : Family (PortHamiltonian n p) Requirement n p :=
  ⟨fun h => h.plant.system, Meets, translate⟩

@[powerlib_foundation] theorem family_isLinear :
    (family (n := n) (p := p)).IsLinear PortHamiltonian.plant := fun _ => rfl

/-- Stored energy places each submitted plant in the passivity denotation. -/
@[powerlib_domain] theorem mem_den_passive (h : PortHamiltonian n p) :
    connection% (h ∈ family.den .passive) := family_isLinear.mem_den_passive h.kyp

/-- Positive stored energy places each submitted plant in the zero-input stability denotation. -/
@[powerlib_domain] theorem mem_den_lyapunovStable (h : PortHamiltonian n p) :
    connection% (h ∈ family.den (.flow .lyapunovStable)) :=
  family_isLinear.mem_den_flow.mpr (h.kyp.lyapunovStable_of_pos h.energy_pos)

/-- The translation chain is sound for every sentence of a port-Hamiltonian plant. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, (family (n := n) (p := p)).chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s h hh => ?_
  rw [TMIO.mem_realize] at hh
  change ∀ q ∈ translate s, Meets h q at hh
  rcases s with P | _ | E
  · cases P
    case lyapunovStable => exact h.mem_den_lyapunovStable
    case unstable => exact (hh .impossible (Set.mem_univ _)).elim
    case decay a => exact (hh .impossible (Set.mem_univ _)).elim
    case conservative => exact (hh .impossible (Set.mem_univ _)).elim
    all_goals
      rw [family_isLinear.den_hurwitz (by simp)]
      exact hh .hurwitz rfl
  · exact h.mem_den_passive
  · rw [family_isLinear.den_envelope]
    trivial

end PortHamiltonian

end powerlib.Port
