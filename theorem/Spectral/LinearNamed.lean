import theorem.Spectral.Global
import theorem.Linear.Family

/-! # Linear families with named requirement languages (foundation)

`Spectral.linearFamily` (`theorem/Spectral/Family.lean`) reads every complete system as the port
system of its linear plant with the two-element language `{stable, unstable}`. The frequency,
current-loop and digital-platform families read their members the same way but keep requirement
languages of their own — Routh–Hurwitz conditions in their parameters, a matrix language with a
spectral rate margin, platform constraints — and re-proved the laws of the linear table one by
one. This module states them once, as the instance of the global table
(`theorem/Spectral/Global.lean`) in which a Hurwitz state matrix decides every attractive sentence.

Scope.
* A generic template, not a model: an arbitrary family `F : Family X Q n p` that is linear
  (`Family.IsLinear plant`: every member is the port system of its plant), an arbitrary
  requirement language `Q` and requirement sets. The obligations are static conditions on the
  state matrix (Hurwitz, a characteristic root in the open right half plane) and, for decay
  rates, conservation and passivity, on denotations.

Source: the linear hub `theorem/Linear/Stability.lean` (`holds_iff_isHurwitz`,
`sampledContraction_iff_isHurwitz`) and `theorem/Linear/Family.lean` (`IsLinear.den_hurwitz`); the
families of `theorem/Frequency/` and `theorem/CurrentControl/DigitalPI.lean` (audit of the library).

Results.
* The table: `linearTable Rs Ru Rc Rp Rd` — Lyapunov stability, the attractive sentences and
  sampled contraction to `Rs`, instability to `Ru`, conservation to `Rc`, passivity to `Rp`, decay
  at the rate `a` to `Rd a`; it is `globalTable Rs Rs Ru Rc Rp Rd`. The common table sends
  conservation and passivity to the whole language (`Rc = Rp = univ`, unavailable coverage)
  (`linearTable_flow`: the attractive and contractive values).
* Soundness: `chain_le_semantics_of_linearTable`, when `Rs` gives a Hurwitz state matrix, `Ru` a
  characteristic root in the open right half plane, `Rd a` decay at the rate `a`, `Rc`
  conservation and `Rp` passivity; `chain_le_semantics_of_linearTable_univ`, the common table, in
  which the whole language is inconsistent by itself (`realize_univ_of_linearTable`).
* Exactness: `exactUnder_of_linearTable` (within a context on which `Rs` is equivalent to the
  Hurwitz property, the attractive and contractive translations are exact) and
  `exact_of_linearTable` (without a context).

Family and connection conclusions.
* `chain_le_semantics_of_linearTable` is a generic foundation connection establishing
  translation soundness. Model modules instantiate it for their own engineering conclusions.
-/

noncomputable section

namespace powerlib.Spectral

open TMIO Set Matrix Linear LinearSystems

variable {X Q : Type*} {n p : ℕ}

/-- The table of a linear family with named requirements: Lyapunov stability, the attractive
sentences and sampled contraction to `Rs`, instability to `Ru`, conservation to `Rc`, passivity to
`Rp`, decay at the rate `a` to `Rd a`. -/
def linearTable (Rs Ru Rc Rp : Set Q) (Rd : ℝ → Set Q) : Sentence → Set Q :=
  globalTable Rs Rs Ru Rc Rp Rd

/-- The attractive sentences and sampled contraction are translated into `Rs`. -/
@[tmio T, powerlib_foundation] theorem linearTable_flow {Rs Ru Rc Rp : Set Q} {Rd : ℝ → Set Q}
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    linearTable Rs Ru Rc Rp Rd (.flow P) = Rs := by
  rcases hP with hP | rfl
  · cases P <;> first | rfl | exact hP.elim
  · rfl

section Linear

variable {F : Family X Q n p} {plant : X → Plant n p} {Rs Ru Rc Rp : Set Q} {Rd : ℝ → Set Q}

/-- A requirement set giving a Hurwitz state matrix and one giving a right-half-plane root are
mutually exclusive, so the whole language is inconsistent. -/
@[powerlib_foundation] theorem realize_univ_of_linearTable
    (hS : ∀ x ∈ realize F.meets Rs, IsHurwitz (plant x).A)
    (hU : ∀ x ∈ realize F.meets Ru,
      ∃ s : ℂ, (characteristicMatrix (plant x).A s).det = 0 ∧ 0 < s.re) :
    realize F.meets univ = ∅ :=
  realize_univ_eq_empty_of_forall fun x h => by
    have hx : x ∈ realize F.meets univ := (mem_realize _ _ _).mpr fun q _ => h q
    obtain ⟨s, hs, hre⟩ := hU x (realize_antitone _ (subset_univ _) hx)
    exact absurd ((spectrallyStable_iff_isHurwitz _).mpr
      (hS x (realize_antitone _ (subset_univ _) hx)) s hs) (not_lt.mpr hre.le)

/-- Soundness of every translation of a linear family with the linear table: `Rs` gives a
Hurwitz state matrix, `Ru` a characteristic root in the open right half plane, `Rd a` decay at
the rate `a`, `Rc` conservation and `Rp` passivity. -/
@[tmio TM, powerlib_foundation] theorem chain_le_semantics_of_linearTable (hF : F.IsLinear plant)
    (ht : ∀ s, F.translate s = linearTable Rs Ru Rc Rp Rd s)
    (hS : ∀ x ∈ realize F.meets Rs, IsHurwitz (plant x).A)
    (hU : ∀ x ∈ realize F.meets Ru,
      ∃ s : ℂ, (characteristicMatrix (plant x).A s).det = 0 ∧ 0 < s.re)
    (hD : ∀ a, realize F.meets (Rd a) ⊆ F.den (.flow (.decay a)))
    (hC : realize F.meets Rc ⊆ F.den (.flow .conservative))
    (hP : realize F.meets Rp ⊆ F.den .passive) :
    connection% (∀ P, F.chain P ≤ F.semantics P) := by
  unfold powerlib.TMIO.Statement
  have hG : realize F.meets Rs ⊆ F.den (.flow .globallyExponentiallyStable) := fun x hx =>
    hF.mem_den_flow.mpr (holds_of_isHurwitz 0 trivial (hS x hx))
  exact chain_le_semantics_of_globalTable ht
    (fun x hx => den_globallyExponentiallyStable_subset_les (hG hx)) hG hD
    (fun x hx => by
      obtain ⟨s, hs, hre⟩ := hU x hx
      exact hF.mem_den_flow.mpr (unstable_of_root 0 hs hre)) hC hP hF.den_envelope

/-- The common table: conservation and passivity are translated into the whole language, which
`Rs` and `Ru` make inconsistent. -/
@[powerlib_foundation] theorem chain_le_semantics_of_linearTable_univ (hF : F.IsLinear plant)
    (ht : ∀ s, F.translate s = linearTable Rs Ru univ univ Rd s)
    (hS : ∀ x ∈ realize F.meets Rs, IsHurwitz (plant x).A)
    (hU : ∀ x ∈ realize F.meets Ru,
      ∃ s : ℂ, (characteristicMatrix (plant x).A s).det = 0 ∧ 0 < s.re)
    (hD : ∀ a, realize F.meets (Rd a) ⊆ F.den (.flow (.decay a))) :
    ∀ P, F.chain P ≤ F.semantics P :=
  chain_le_semantics_of_linearTable hF ht hS hU hD
    (realize_univ_subset_of_eq_empty (realize_univ_of_linearTable hS hU) _)
    (realize_univ_subset_of_eq_empty (realize_univ_of_linearTable hS hU) _)

/-- Exactness within a context: where `Rs` is equivalent to the Hurwitz property of the state
matrix, the attractive and contractive translations are exact. -/
@[powerlib_foundation] theorem exactUnder_of_linearTable (hF : F.IsLinear plant)
    (ht : ∀ s, F.translate s = linearTable Rs Ru Rc Rp Rd s) (Δ : Set Q)
    (hS : ∀ x ∈ realize F.meets Δ, (x ∈ realize F.meets Rs ↔ IsHurwitz (plant x).A))
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    F.ExactUnder Δ (.flow P) := by
  refine exactUnder_iff_forall.mpr fun x hΔ => ?_
  rw [ht, linearTable_flow hP, hF.den_hurwitz hP, mem_ofPred_eq]
  exact hS x hΔ

/-- Exactness: with `Rs` equivalent to the Hurwitz property of the state matrix, the attractive
and contractive translations are exact. -/
@[powerlib_foundation] theorem exact_of_linearTable (hF : F.IsLinear plant)
    (ht : ∀ s, F.translate s = linearTable Rs Ru Rc Rp Rd s)
    (hS : ∀ x, x ∈ realize F.meets Rs ↔ IsHurwitz (plant x).A)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    F.Exact (.flow P) :=
  exact_of_exactUnder_empty (exactUnder_of_linearTable hF ht ∅ (fun x _ => hS x) hP)

end Linear

end powerlib.Spectral
