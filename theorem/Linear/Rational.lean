import theorem.Linear.Family
import theorem.Linear.Synthesis

/-! # Rational state matrices

Model boundary: the linear plant without ports `x' = A x` of an exact rational state matrix `A`,
in continuous time, about the origin. The family reads every submitted matrix as that plant. Its
requirements are the Hurwitz property, acceptance by the rational synthesizer of
`Linear.Synthesis`, and a root of the characteristic polynomial in the open right half plane.

The Hurwitz property is the exact translation of the attractive sentences and sampled
contraction (`exact_hurwitz`) and every translation is sound (`chain_le_semantics`). Acceptance
entails the Hurwitz property (`realize_accepted`), so a submission accepted by the kernel's run of
the synthesizer is placed in those sentences along the chain. -/

noncomputable section

namespace powerlib.Linear.Rational

open LinearSystems TMIO Synthesis

variable {n : ℕ}

/-- The plant of a rational state matrix: no ports. -/
def plant (A : Matrix (Fin n) (Fin n) ℚ) : Plant n 0 := ⟨real A, 0, 0, 0⟩

/-- Requirements on a rational state matrix. -/
inductive Requirement
  | hurwitz
  | accepted
  | rightHalfPlaneRoot

/-- Satisfaction of a requirement by a submitted matrix. -/
def Meets (A : Matrix (Fin n) (Fin n) ℚ) : Requirement → Prop
  | .hurwitz => IsHurwitz (real A)
  | .accepted => accepts A = true
  | .rightHalfPlaneRoot => ∃ s : ℂ, (characteristicMatrix (real A) s).det = 0 ∧ 0 < s.re

/-- The translation of the sentences. A decay rate and conservation have no requirement in the
language and are translated into the whole language, which no matrix meets; passivity of a plant
without ports needs no requirement. -/
def translate : Sentence → Set Requirement
  | .flow .unstable => {.rightHalfPlaneRoot}
  | .flow (.decay _) | .flow .conservative => Set.univ
  | .passive => ∅
  | .flow _ => {.hurwitz}

/-- The family of rational state matrices. -/
def family : Family (Matrix (Fin n) (Fin n) ℚ) Requirement n 0 :=
  ⟨fun A => (plant A).system, Meets, translate⟩

@[powerlib_foundation] theorem family_isLinear : (family (n := n)).IsLinear plant := fun _ => rfl

/-- No matrix is Hurwitz with a right-half-plane root. -/
@[powerlib_foundation] theorem realize_univ : realize (Meets (n := n)) Set.univ = ∅ := by
  ext A
  simp only [mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨s, hs, hre⟩ := h .rightHalfPlaneRoot
  have hH : IsHurwitz (real A) := h .hurwitz
  exact absurd ((spectrallyStable_iff_isHurwitz _).mpr hH s hs) (not_lt.mpr hre.le)

/-- The Hurwitz property is the exact translation of the attractive sentences and sampled
contraction. -/
@[powerlib_domain] theorem exact_hurwitz {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) : (family (n := n)).Exact (.flow P) := by
  have ht : translate (.flow P) = {.hurwitz} := by
    rcases hP with hP | rfl
    · cases P <;> first | rfl | exact absurd hP id
    · rfl
  unfold Family.Exact
  change realize Meets (translate (.flow P)) = _
  rw [ht, family_isLinear.den_hurwitz hP]
  ext A
  simp [Meets, plant]

/-- Every translation is sound: the Hurwitz property proves Lyapunov stability, the attractive
sentences and sampled contraction, a right-half-plane root proves instability, and a plant without
ports is passive. -/
@[powerlib_domain] theorem chain_le_semantics :
    ∀ P, (family (n := n)).chain P ≤ (family (n := n)).semantics P := by
  refine Family.chain_le_semantics_iff.mpr fun s A hA => ?_
  rw [mem_realize] at hA
  change ∀ q ∈ translate s, Meets A q at hA
  have huniv : translate s = Set.univ → A ∈ family.den s := fun hs => by
    have : A ∈ realize Meets Set.univ :=
      (mem_realize _ _ _).mpr fun q _ => hA q (hs ▸ Set.mem_univ q)
    rw [realize_univ] at this
    exact this.elim
  rcases s with P | _
  · cases P
    case unstable =>
      obtain ⟨s, hs, hre⟩ := hA .rightHalfPlaneRoot rfl
      exact family_isLinear.mem_den_flow.mpr (unstable_of_root 0 hs hre)
    case lyapunovStable =>
      exact family_isLinear.mem_den_flow.mpr (lyapunovStable_of_isHurwitz 0 (hA .hurwitz rfl))
    case decay a => exact huniv rfl
    case conservative => exact huniv rfl
    all_goals
      rw [family_isLinear.den_hurwitz (by simp)]
      exact hA .hurwitz rfl
  · exact (Family.mem_den _).mpr (Port.System.passive_of_noPorts _)

/-- Acceptance by the synthesizer entails the Hurwitz property: the accepted proposal is a
kernel-checked certificate. -/
@[powerlib_domain] theorem realize_accepted :
    realize (Meets (n := n)) {.accepted} ⊆ realize Meets {.hurwitz} := by
  intro A hA
  simp only [mem_realize, Set.mem_singleton_iff, forall_eq] at hA ⊢
  exact (certificateOf A hA).isHurwitz

end powerlib.Linear.Rational
