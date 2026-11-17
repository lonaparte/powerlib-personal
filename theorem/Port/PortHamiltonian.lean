import theorem.TMIO.ClaimElab
import theorem.Linear.Family
import theorem.Spectral.Local

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
  `PortHamiltonian.lyapunov` (the Lyapunov identity `Aᵀ Q + Q A = −2 Q R Q` of `A = (J − R) Q`,
  for any skew `J` and symmetric `R`, `Q`), `PortHamiltonian.energy_rate` (`xᵀ Q A x =
  −(Q x)ᵀ R (Q x)`), `PortHamiltonian.kyp` (the energy matrix is a KYP certificate),
  `Requirement`, `Meets`, `translate`, `family_isLinear`.

Family and connection conclusions.
* `Port.PortHamiltonian.family : Family (PortHamiltonian n p) Requirement n p`: requirements
  `hurwitz` and `impossible` (the structure fields already enforce passivity and positive stored
  energy). Passivity and Lyapunov stability translate into nothing, the attractive sentences and
  sampled contraction into `hurwitz`, instability, decay rates and conservation into the whole,
  inconsistent, language.
* `mem_den_passive`: stored energy places each submitted plant in the passivity denotation;
  `mem_den_lyapunovStable`: positive stored energy places it in the zero-input stability
  denotation.
* `chain_le_semantics`: the translation chain is sound for every sentence (the translation is an
  instance of `Spectral.table`, `Spectral.chain_le_semantics_of_table`).
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

/-- The Lyapunov identity of a port-Hamiltonian state matrix: for a skew-symmetric `J` and
symmetric `R` and `Q`, `((J − R) Q)ᵀ Q + Q (J − R) Q = −2 Q R Q`. -/
@[tmio T, powerlib_foundation] theorem PortHamiltonian.lyapunov {J R Q : Matrix (Fin n) (Fin n) ℝ}
    (hJ : Jᵀ = -J) (hR : Rᵀ = R) (hQ : Qᵀ = Q) :
    ((J - R) * Q)ᵀ * Q + Q * ((J - R) * Q) = -(2 : ℝ) • (Q * R * Q) := by
  rw [Matrix.transpose_mul, Matrix.transpose_sub, hJ, hR, hQ, neg_smul, two_smul]
  noncomm_ring

/-- In a linear port-Hamiltonian plant the energy matrix turns the state matrix into the
dissipation: `xᵀ Q A x = −(Q x)ᵀ R (Q x)` (the Lyapunov identity read on `x`). -/
@[tmio T, powerlib_foundation] theorem PortHamiltonian.energy_rate (h : PortHamiltonian n p)
    (x : Fin n → ℝ) :
    x ⬝ᵥ (h.Q *ᵥ (h.plant.A *ᵥ x)) = -((h.Q *ᵥ x) ⬝ᵥ (h.R *ᵥ (h.Q *ᵥ x))) := by
  have hq := Linear.quadratic_sym (A := (h.J - h.R) * h.Q) h.energy_symmetric x
  rw [PortHamiltonian.lyapunov h.skew h.dissipation_symmetric h.energy_symmetric,
    Matrix.smul_mulVec, dotProduct_smul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec x h.Q, ← Matrix.mulVec_transpose, h.energy_symmetric,
    smul_eq_mul] at hq
  change x ⬝ᵥ (h.Q *ᵥ (((h.J - h.R) * h.Q) *ᵥ x)) = _
  linarith

/-- The energy matrix is a KYP certificate. -/
def PortHamiltonian.kyp (h : PortHamiltonian n p) : Linear.KYP h.plant where
  P := h.Q
  symmetric := h.energy_symmetric
  nonneg x := by
    by_cases hx : x = 0
    · simp [hx]
    · exact (h.energy_pos x hx).le
  dissipation x := by
    rw [Linear.quadratic_sym h.energy_symmetric, h.energy_rate]
    nlinarith [h.dissipation_nonneg (h.Q *ᵥ x)]
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

/-- The table (`Spectral.table`): passivity, Lyapunov stability and the envelope sentences to
nothing, the attractive sentences and sampled contraction to `hurwitz`, instability, decay rates
and conservation to the whole, inconsistent, language. -/
def translate : Sentence → Set Requirement :=
  Spectral.table ∅ {.hurwitz} {.hurwitz} Set.univ Set.univ ∅ (fun _ => Set.univ) ∅

def family : Family (PortHamiltonian n p) Requirement n p :=
  ⟨fun h => h.plant.system, Meets, translate⟩

@[tmio M, powerlib_foundation] theorem family_isLinear :
    (family (n := n) (p := p)).IsLinear PortHamiltonian.plant := fun _ => rfl

/-- Stored energy places each submitted plant in the passivity denotation. -/
@[tmio TM, powerlib_foundation] theorem mem_den_passive (h : PortHamiltonian n p) :
    connection% (h ∈ family.den .passive) := family_isLinear.mem_den_passive h.kyp

/-- Positive stored energy places each submitted plant in the zero-input stability denotation. -/
@[tmio TM, powerlib_foundation] theorem mem_den_lyapunovStable (h : PortHamiltonian n p) :
    connection% (h ∈ family.den (.flow .lyapunovStable)) :=
  family_isLinear.mem_den_flow.mpr (h.kyp.lyapunovStable_of_pos h.energy_pos)

/-- The translation chain is sound for every sentence of a port-Hamiltonian plant
(`Spectral.chain_le_semantics_of_table`). -/
@[tmio TM, powerlib_foundation] theorem chain_le_semantics :
    connection% (∀ P, (family (n := n) (p := p)).chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  have hu := Spectral.realize_univ_subset_of_eq_empty (meets := Meets (n := n) (p := p))
    (Spectral.realize_univ_eq_empty_of_forall fun _ h => h .impossible)
  have hH : ∀ {P : Flow.Property}, P.Attractive →
      TMIO.realize Meets {.hurwitz} ⊆ (family (n := n) (p := p)).den (.flow P) := fun hP h hh =>
    (connection_proof% family_isLinear.mem_den_hurwitz (Or.inl hP)).mpr
      ((TMIO.mem_realize _ _ _).mp hh .hurwitz rfl)
  exact Spectral.chain_le_semantics_of_table (fun _ => rfl)
    (fun h _ => h.mem_den_lyapunovStable) (hH trivial) (hH trivial) (fun _ => hu _) (hu _) (hu _)
    (fun h _ => h.mem_den_passive) (fun _ _ _ => (Family.mem_den _).mpr trivial)

end PortHamiltonian

end powerlib.Port
