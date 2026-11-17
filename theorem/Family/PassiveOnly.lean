import theorem.Family.Basic

/-! # Passivity-only families

A family of continuous-time port systems whose requirement language offers nothing beyond
passivity: passivity is translated into no requirement, every flow sentence into the whole,
inconsistent, language (unavailable translation coverage) and every envelope sentence into no
requirement. The generic connection laws of such a family are proved here once; an instance
supplies only its system map and the facts that carry its own content (every member passive,
or no member satisfying a flow sentence).

Scope.
* Generic: arbitrary complete systems `X` read as continuous-time port systems
  `Port.System n p` (`theorem/Port/Defs.lean`); no model.

Source: the framework of `theorem/Family/Basic.lean` (`exact_of_translate_eq_empty`,
`exact_of_translate_eq_univ`, `chain_le_semantics_iff`).

Results.
* `PassiveOnly.Requirement` (the single requirement `impossible`), `PassiveOnly.Meets` (never
  met), `PassiveOnly.translate`, `Family.passiveOnly sys` (the family of the system map `sys`).

Family and connection conclusions.
* `PassiveOnly.realize_univ`: the whole requirement language is inconsistent.
* Laws for every family `F` with this language (`F.meets = Meets`, `F.translate = translate`;
  `Family.passiveOnly sys` is one, by `rfl`): `PassiveOnly.exact_passive` (if every member is
  passive, passivity is translated exactly), `PassiveOnly.chain_le_semantics` (if moreover `F` is
  a family of port systems, `Family.IsPort`, every translation is sound) and
  `PassiveOnly.exact_flow` (if no member satisfies a flow sentence, its translation is exact).
* Instances: the seven-state dq machine (`Synchronous.SyncMachine7.family`,
  `theorem/PowerSystem/Synchronous/PH.lean`) and the 11-state single machine, node and link
  models (`Synchronous.SMIB11.family`, `Synchronous.SMIB11Rel.family`,
  `theorem/PowerSystem/Synchronous/SMIB11PH.lean`).
-/

noncomputable section

namespace powerlib

namespace PassiveOnly

/-- The requirement language of a passivity-only family: one requirement, never met. -/
inductive Requirement
  | impossible

/-- Satisfaction of a requirement: never. -/
def Meets {X : Type*} (_ : X) : Requirement → Prop
  | .impossible => False

/-- Passivity and the envelope sentences need no requirement; the flow sentences have no
translation. -/
def translate : Sentence → Set Requirement
  | .passive => ∅
  | .flow _ => Set.univ
  | .envelope _ => ∅

end PassiveOnly

/-- The passivity-only family of a system map: every complete system read as its continuous-time
port system. -/
def Family.passiveOnly {X : Type*} {n p : ℕ} (sys : X → Port.System n p) :
    Family X PassiveOnly.Requirement n p :=
  ⟨fun x => .continuous (sys x), PassiveOnly.Meets, PassiveOnly.translate⟩

namespace PassiveOnly

variable {X : Type*} {n p : ℕ} {sys : X → Port.System n p}

/-- The whole requirement language of a passivity-only family is inconsistent. -/
@[tmio TM, powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize (Meets (X := X)) Set.univ = ∅) := by
  change TMIO.realize (Meets (X := X)) Set.univ = ∅
  ext x
  simp only [TMIO.mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  exact fun h => h .impossible

variable {F : Family X Requirement n p}

/-- If every member is passive, passivity is translated exactly. -/
@[tmio TM, powerlib_foundation] theorem exact_passive (ht : F.translate = translate)
    (h : ∀ x, x ∈ F.den .passive) :
    connection% (F.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_empty (by rw [ht]; rfl) (Set.eq_univ_of_forall h)

/-- If every member is passive, every translation of a passivity-only family is sound. -/
@[tmio TM, powerlib_foundation] theorem chain_le_semantics (hF : F.IsPort sys)
    (hm : F.meets = Meets) (ht : F.translate = translate) (h : ∀ x, x ∈ F.den .passive) :
    connection% (∀ P, F.chain P ≤ F.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s x hx => ?_
  rw [(connection_proof% TMIO.mem_realize), hm, ht] at hx
  rcases s with P | _ | E
  · exact (hx .impossible trivial).elim
  · exact h x
  · rw [(connection_proof% hF.den_envelope E)]
    trivial

/-- If no member satisfies a flow sentence, its translation (the whole, inconsistent, language) is
exact. -/
@[tmio TM, powerlib_foundation] theorem exact_flow {P : Flow.Property} (hm : F.meets = Meets)
    (ht : F.translate = translate) (h : ∀ x, x ∉ F.den (.flow P)) :
    connection% (F.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  have hu := realize_univ (X := X)
  unfold powerlib.TMIO.Statement at hu
  exact Family.exact_of_translate_eq_univ (by rw [hm]; exact hu) (by rw [ht]; rfl)
    (Set.eq_empty_of_forall_notMem h)

end PassiveOnly

end powerlib
