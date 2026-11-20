import theorem.TMIO.ClaimElab
import theorem.Linear.Rate
import theorem.Linear.Synthesis
import theorem.Spectral.LinearNamed

/-! # Rational state matrices

The family of exact rational state matrices, read as linear plants without ports. Its
requirements are the Hurwitz property, acceptance by the rational synthesizer of
`Linear.Synthesis`, a strict rate margin, and a root of the characteristic polynomial in the open
right half plane.

Model boundary.
* The linear plant without ports `x' = A x` of an exact rational state matrix `A`, in continuous
  time, about the origin. The family reads every submitted matrix as that plant
  (`Family.IsLinear`).
* No inputs, outputs, delay, sampling or switching; any dimension `n`.

Source: the rational synthesizer and its completeness (`theorem/Linear/Synthesis.lean`,
`accepts_iff_isHurwitz`, `certificateOf`); strict rate margins (`theorem/Linear/Rate.lean`);
pole stability and right-half-plane roots (`theorem/Linear/Transfer.lean`,
`spectrallyStable_iff_isHurwitz`, `unstable_of_root`); the linear family laws of
`theorem/Linear/Family.lean` (`Family.IsLinear.den_hurwitz`) and the linear table
(`theorem/Spectral/LinearNamed.lean`).

Results.
* Static: `plant`, `Requirement`, `Meets`, `translate`, `family_isLinear`.

Family and connection conclusions.
* `Linear.Rational.family : Family (Matrix (Fin n) (Fin n) ℚ) Requirement n 0`: requirements
  `hurwitz`, `accepted`, `rightHalfPlaneRoot` and `rate a` (`RateMargin`). The attractive
  sentences, Lyapunov stability and sampled contraction translate into `hurwitz`, instability into
  `rightHalfPlaneRoot`, decay at `a` into `rate a` (a strict matrix margin), conservation into the
  inconsistent whole language, passivity of a plant without ports into nothing.
* The translation is the linear table (`Spectral.linearTable`); its generic laws give
  `realize_univ` (no matrix is Hurwitz with a right-half-plane root: the whole language is
  inconsistent, `Spectral.realize_univ_of_linearTable`), the exactness of the Hurwitz property for
  the attractive sentences and sampled contraction (`exact_hurwitz`,
  `Spectral.exact_of_linearTable`) and the soundness of every translation (`chain_le_semantics`,
  `Spectral.chain_le_semantics_of_linearTable`).
* Acceptance entails the Hurwitz property (`realize_accepted`), so a submission accepted by the
  kernel's run of the synthesizer is placed in those sentences along the chain; acceptance is
  itself an exact requirement for them (`accepted_eq_den`: the executable synthesizer is
  complete, not merely sound).
-/

noncomputable section

namespace powerlib.Linear.Rational

open LinearSystems TMIO Synthesis
open powerlib.Linear.Positive (real)

variable {n : ℕ}

/-- The plant of a rational state matrix: no ports. -/
def plant (A : Matrix (Fin n) (Fin n) ℚ) : Plant n 0 := ⟨real A, 0, 0, 0⟩

/-- Requirements on a rational state matrix. -/
inductive Requirement
  | hurwitz
  | accepted
  | rightHalfPlaneRoot
  | rate (a : ℝ)

/-- Satisfaction of a requirement by a submitted matrix. -/
def Meets (A : Matrix (Fin n) (Fin n) ℚ) : Requirement → Prop
  | .hurwitz => IsHurwitz (real A)
  | .accepted => accepts A = true
  | .rate a => RateMargin (real A) a
  | .rightHalfPlaneRoot => ∃ s : ℂ, (characteristicMatrix (real A) s).det = 0 ∧ 0 < s.re

/-- The linear table (`Spectral.linearTable`): the attractive sentences, Lyapunov stability and
sampled contraction to the Hurwitz property, instability to a right-half-plane root, decay at `a`
to a strict matrix margin. Conservation is unavailable and uses the inconsistent whole language;
passivity of a plant without ports needs no requirement. -/
def translate : Sentence → Set Requirement :=
  Spectral.linearTable {.hurwitz} {.rightHalfPlaneRoot} Set.univ ∅ fun a => {.rate a}

/-- The family of rational state matrices. -/
def family : Family (Matrix (Fin n) (Fin n) ℚ) Requirement n 0 :=
  ⟨fun A => (plant A).system, Meets, translate⟩

@[tmio M, powerlib_foundation] theorem family_isLinear : (family (n := n)).IsLinear plant :=
  fun _ => rfl

/-- No matrix is Hurwitz with a right-half-plane root. -/
@[tmio M, powerlib_foundation] theorem realize_univ :
    connection% (realize (Meets (n := n)) Set.univ = ∅) :=
  Spectral.realize_univ_of_linearTable (F := family) (plant := plant) (Rs := {.hurwitz})
    (Ru := {.rightHalfPlaneRoot}) (fun _A hA => (mem_realize _ _ _).mp hA .hurwitz rfl)
    (fun _A hA => (mem_realize _ _ _).mp hA .rightHalfPlaneRoot rfl)

/-- The Hurwitz property is the exact translation of the attractive sentences and sampled
contraction. -/
@[tmio TM, powerlib_foundation] theorem exact_hurwitz {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% ((family (n := n)).Exact (.flow P)) :=
  Spectral.exact_of_linearTable family_isLinear (fun _ => rfl)
    (fun _ => Spectral.mem_realize_singleton) hP

/-- Every translation is sound: the Hurwitz property proves Lyapunov stability, the attractive
sentences and sampled contraction, a right-half-plane root proves instability, a strict margin
decay at its rate, and a plant without ports is passive. -/
@[tmio TM, powerlib_foundation] theorem chain_le_semantics :
    connection% (∀ P, (family (n := n)).chain P ≤ (family (n := n)).semantics P) :=
  Spectral.chain_le_semantics_of_linearTable family_isLinear (fun _ => rfl)
    (fun A hA => (mem_realize _ _ _).mp hA .hurwitz rfl)
    (fun A hA => (mem_realize _ _ _).mp hA .rightHalfPlaneRoot rfl)
    (fun a A hA =>
      family_isLinear.mem_den_decay_of_rateMargin ((mem_realize _ _ _).mp hA (.rate a) rfl))
    (Spectral.realize_univ_subset_of_eq_empty realize_univ _)
    (fun A _ => by rw [(connection_proof% family_isLinear.den_passive)]; trivial)

/-- Acceptance by the synthesizer entails the Hurwitz property: the accepted proposal is a
kernel-checked certificate. -/
@[tmio M, powerlib_foundation] theorem realize_accepted :
    connection% (realize (Meets (n := n)) {.accepted} ⊆ realize Meets {.hurwitz}) := by
  unfold powerlib.TMIO.Statement
  intro A hA
  simp only [mem_realize, Set.mem_singleton_iff, forall_eq] at hA ⊢
  exact (certificateOf A hA).isHurwitz

/-- Acceptance is an exact requirement for the attractive sentences and sampled contraction:
the executable synthesizer is complete, not merely sound. -/
@[tmio TM, powerlib_foundation] theorem accepted_eq_den {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (realize (Meets (n := n)) {.accepted} = family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  rw [family_isLinear.den_hurwitz hP]
  ext A
  simp only [mem_realize, Set.mem_singleton_iff, forall_eq, Set.mem_ofPred_eq, Meets]
  exact accepts_iff_isHurwitz A

end powerlib.Linear.Rational
