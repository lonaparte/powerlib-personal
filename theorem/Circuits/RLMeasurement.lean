import theorem.TMIO.ClaimElab
import theorem.Circuits.RL
import theorem.Data.Analysis

/-! # RL candidate models from symbolic resistance constraints

The relation `reading ε` is a formal compatibility assumption between an RL model and a symbolic
resistance value. It constrains candidate models within M and supplies criteria for their T–M
properties. This module defines no implementation or I–O production interface and proves no claim
that a physical implementation produces a reading or record.

The family's compatibility seed generates certified values, possible values and a closure of
candidate models. Because the family is faithful, a value certifies a sentence exactly when its
tolerance interval lies in the resistances all of whose models satisfy the sentence
(`certified_readings`). With `ε ≥ 0` a positive decay rate is never certified: it
depends on the inductance, which this compatibility relation cannot separate (`closure_resistance`).

Model boundary.
* The RL family of `theorem.Circuits.RL`.
* The formal compatibility assumption for a symbolic resistance value `r` and tolerance `ε` is
  `|r - R| ≤ ε`; this constraint supplies no information about the inductance.
* The parameterized record interface is reduced to symbolic resistance values by the deterministic
  least-squares analysis of `Data.Analysis`.

Source: TMIO relational calculus (`Family.seed`, certification and prediction,
`theorem/TMIO/Relation.lean`; representation change, `theorem/TMIO/Representation.lean`); the
data analysis of `theorem/Data/Analysis.lean`; the Agda-generated conversion of
`theorem/Circuits/RL.lean` for the state-space representation.

Results.
* Model compatibility: `rl` (`rl_resistance`, `rl_inductance`), `reading`, `seed`.
* Windows: `window` (the resistances all of whose models satisfy a sentence),
  `kernImage_resistance`, `kernImage_decayRate`, `kernImage_den` (the window of every sentence is
  the resistance kernel of its denotation).
* Record interface: `recordEdge` (the deterministic analysis relation).
* The state-space representation: `stateSpaceIso`, `stateSpaceSeed`, `stateSpace_whole`
  (certified values do not depend on the model representation).

Family and connection conclusions.
* No new family: the module constrains candidate models of `Circuits.RL.family` through `seed ε`.
  This is a model-side compatibility construction; it does not establish an I–O relation. Scaffold:
  `theorem/RLMeasurement.agda`.
* `certify_reading`: a reading certifies a set of models exactly when its accuracy interval lies
  in the resistances all of whose models belong to the set; `predict_reading`: the possible
  readings, derived from certification by complement; `candidates`: the candidates of a reading
  are the semantic map itself.
* `certified_readings`: a symbolic value is certified through the compatibility seed when its
  tolerance interval lies in the sentence's window; a positive decay rate has an empty window, so with
  `ε ≥ 0` (a nonempty interval) it is never certified.
* `closure_resistance`: the generated compatibility closure cannot separate models of equal
  resistance; the constraint does not identify the inductance or the decay rate.
* `certified_records`: the chain extended by the analysis edge certifies a record exactly when it
  certifies the record's estimate.
-/

noncomputable section

namespace powerlib.Circuits.RL

open OrderDual LinearSystems TMIO Data.Analysis

/-- The impedance model with resistance `R` and inductance `L`. -/
def rl (R L : ℝ) (hL : 0 < L) : Impedance := ⟨R, ⟨L, hL⟩⟩

@[simp, powerlib_foundation] theorem rl_resistance (R L : ℝ) (hL : 0 < L) :
    (rl R L hL).resistance = R := rfl

@[simp, powerlib_foundation] theorem rl_inductance (R L : ℝ) (hL : 0 < L) :
    (rl R L hL).inductance.val = L := rfl

/-! ## Model compatibility -/

/-- Formal compatibility between a model and a symbolic resistance value with tolerance `ε`. -/
def reading (ε : ℝ) : SetRel Impedance ℝ := {p | |p.2 - p.1.resistance| ≤ ε}

/-- The family's seed for the model compatibility relation. -/
def seed (ε : ℝ) : Seed (Set Sentence) (Set Requirement) (Set Impedance)ᵒᵈ (Set ℝ)ᵒᵈ :=
  family.seed (reading ε)

/-- A reading certifies a set of models exactly when its accuracy interval lies in the
resistances all of whose models belong to the set. -/
@[tmio M]
@[powerlib_foundation] theorem certify_reading (ε : ℝ) (D : Set Impedance) :
    connection% (certify (reading ε) D =
      {r | Set.Icc (r - ε) (r + ε) ⊆ Set.kernImage Impedance.resistance D}) := by
  unfold powerlib.TMIO.Statement
  ext r
  simp only [mem_certify, Set.mem_ofPred_eq]
  constructor
  · intro h R hR m hm
    apply h
    change |r - m.resistance| ≤ ε
    rw [hm, abs_sub_le_iff]
    exact ⟨by linarith [hR.1], by linarith [hR.2]⟩
  · intro h m hm
    obtain ⟨h1, h2⟩ := abs_sub_le_iff.mp (show |r - m.resistance| ≤ ε from hm)
    exact h ⟨by linarith, by linarith⟩ rfl

/-- The possible readings of a set of models, derived from certification by complement: those
within the accuracy of some model's resistance. -/
@[tmio M]
@[powerlib_foundation] theorem predict_reading (ε : ℝ) (D : Set Impedance) :
    connection% (predict (reading ε) D =
      {r | (Set.Icc (r - ε) (r + ε) ∩ Impedance.resistance '' D).Nonempty}) := by
  unfold powerlib.TMIO.Statement
  rw [predict_eq_image]
  ext r
  simp only [SetRel.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm, hr⟩
    obtain ⟨h1, h2⟩ := abs_sub_le_iff.mp (show |r - m.resistance| ≤ ε from hr)
    exact ⟨m.resistance, ⟨by linarith, by linarith⟩, m, hm, rfl⟩
  · rintro ⟨_, hR, m, hm, rfl⟩
    refine ⟨m, hm, ?_⟩
    change |r - m.resistance| ≤ ε
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hR.1], by linarith [hR.2]⟩

/-! ## Certified readings -/

/-- The resistances all of whose models satisfy a sentence. -/
def window : Sentence → Set ℝ
  | .flow .lyapunovStable => Set.Ici 0
  | .flow .unstable => Set.Iio 0
  | .flow (.decay a) => {R | 0 ≤ R ∧ a ≤ 0}
  | .flow .conservative => {0}
  | .flow _ => Set.Ioi 0
  | .passive => Set.Ici 0
  | .envelope _ => Set.univ

/-- A requirement on the resistance alone has the resistances satisfying it as its kernel. -/
@[powerlib_foundation] theorem kernImage_resistance (S : Set ℝ) :
    Set.kernImage Impedance.resistance {m | m.resistance ∈ S} = S := by
  ext R
  exact ⟨fun h => h (x := rl R 1 one_pos) rfl, fun h m hm => by rw [Set.mem_ofPred_eq, hm]; exact h⟩

/-- The decay rate `R / L` is at least `a` for every inductance exactly when `R ≥ 0` and `a ≤ 0`. -/
@[powerlib_foundation] theorem kernImage_decayRate (a : ℝ) :
    Set.kernImage Impedance.resistance {m | a ≤ m.resistance / m.inductance.val} =
      {R | 0 ≤ R ∧ a ≤ 0} := by
  ext R
  constructor
  · intro h
    have h1 : a ≤ R := by simpa using h (x := rl R 1 one_pos) rfl
    have hR : 0 ≤ R := by
      by_contra hR
      push Not at hR
      have hL : 0 < R / (a - 1) := div_pos_of_neg_of_neg hR (by linarith)
      have h2 : a ≤ R / (R / (a - 1)) := by simpa using h (x := rl R _ hL) rfl
      rw [div_div_cancel₀ hR.ne] at h2
      linarith
    refine ⟨hR, ?_⟩
    by_contra ha
    push Not at ha
    have hL : 0 < (R + 1) / a := div_pos (by linarith) ha
    have h2 : a ≤ R / ((R + 1) / a) := by simpa using h (x := rl R _ hL) rfl
    rw [div_div_eq_mul_div, le_div_iff₀ (by linarith)] at h2
    nlinarith
  · rintro ⟨hR, ha⟩ m hm
    rw [Set.mem_ofPred_eq, hm]
    exact ha.trans (div_nonneg hR m.inductance.property.le)

/-- The window of every sentence is the resistance kernel of its denotation. -/
@[powerlib_foundation] theorem kernImage_den (s : Sentence) :
    Set.kernImage Impedance.resistance (family.den s) = window s := by
  have hexact : realize Meets (translate s) = family.den s :=
    Family.chain_eq_semantics_iff.mp chain_eq_semantics s
  rw [← hexact]
  rcases s with P | _ | E
  · cases P
    case decay a =>
      change _ = {R | 0 ≤ R ∧ a ≤ 0}
      rw [← kernImage_decayRate]
      congr 1
      ext m
      simp [translate, Meets]
    all_goals
      first
      | (rw [← kernImage_resistance (window _)]
         congr 1
         ext m
         simp [translate, Meets, window])
  all_goals
    rw [← kernImage_resistance (window _)]
    congr 1
    ext m
    simp [translate, Meets, window]

/-- The certified symbolic values of every sentence, generated through the compatibility seed: a
value is certified when its tolerance interval lies in the sentence's window. A positive decay rate
has an empty window, so with `ε ≥ 0` it is never certified. -/
@[tmio TM]
@[powerlib_domain] theorem certified_readings (ε : ℝ) (s : Sentence) :
    connection% (ofDual (generate (seed ε).uTO {s}) =
      {r | Set.Icc (r - ε) (r + ε) ⊆ window s}) := by
  unfold powerlib.TMIO.Statement
  rw [seed, family.certified (reading ε) (Family.chain_eq_semantics_iff.mp chain_eq_semantics s),
    certify_reading, kernImage_den]

/-! ## The compatibility closure -/

/-- The candidates of a reading are the semantic map itself. -/
@[tmio M]
@[powerlib_foundation] theorem candidates (ε r : ℝ) :
    connection% (ofDual ((seed ε).u₃ (toDual {r})) = {m : Impedance | |r - m.resistance| ≤ ε}) := by
  unfold powerlib.TMIO.Statement
  ext m
  simp [seed, Family.seed, relationalSeed, reading]

/-- The generated compatibility closure cannot separate models of equal resistance: the symbolic
resistance constraint does not identify the inductance or the decay rate. -/
@[tmio M]
@[powerlib_domain] theorem closure_resistance (ε : ℝ) (P : (Set Impedance)ᵒᵈ)
    {m m' : Impedance} (h : m.resistance = m'.resistance) :
    connection% (m ∈ ofDual (closure (seed ε).u₃ P) ↔ m' ∈ ofDual (closure (seed ε).u₃ P)) := by
  unfold powerlib.TMIO.Statement
  change m ∈ ofDual (possibly (reading ε) (generate (possibly (reading ε)) P)) ↔
    m' ∈ ofDual (possibly (reading ε) (generate (possibly (reading ε)) P))
  simp only [mem_possibly, reading, Set.mem_ofPred_eq, h]

/-! ## The parameterized record interface -/

/-- A symbolic record is read through its least-squares resistance: the deterministic analysis of
`Data.Analysis` as a relation composed with model compatibility. -/
def recordEdge : sInfHom (Set (Record ℝ))ᵒᵈ (Set ℝ)ᵒᵈ :=
  possibly (Function.graph (estimate (K := ℝ))).inv

/-- The certified records of any sentences: the chain extended by the analysis edge, generated
as a composite, certifies a record exactly when it certifies the record's estimate. -/
@[tmio TM]
@[powerlib_foundation] theorem certified_records (ε : ℝ) (Φ : Set Sentence) :
    connection% (ofDual (generate ((seed ε).uTO.comp recordEdge) Φ) =
      estimate ⁻¹' ofDual (generate (seed ε).uTO Φ)) := by
  unfold powerlib.TMIO.Statement
  rw [generate_comp, Function.comp_apply, recordEdge, generate_possibly_apply]
  ext d
  rw [mem_certify]
  exact ⟨fun h => h _ rfl, fun h r hr => (show estimate d = r from hr) ▸ h⟩

/-! ## The state-space representation -/

/-- The model representation in state-space coordinates, along the Agda-generated conversion. -/
def stateSpaceIso : (Set Impedance)ᵒᵈ ≃o (Set StateSpace)ᵒᵈ :=
  (Equiv.toOrderIsoSet modelEquiv.symm).dual

/-- The compatibility seed transported to the state-space model representation. -/
def stateSpaceSeed (ε : ℝ) :
    Seed (Set Sentence) (Set Requirement) (Set StateSpace)ᵒᵈ (Set ℝ)ᵒᵈ :=
  (seed ε).transport (OrderIso.refl _) (OrderIso.refl _) stateSpaceIso (OrderIso.refl _)

/-- Certified symbolic values do not depend on the model representation. -/
@[powerlib_foundation] theorem stateSpace_whole (ε : ℝ) :
    ⇑(generate (stateSpaceSeed ε).uTO) = ⇑(generate (seed ε).uTO) := by
  rw [stateSpaceSeed, Seed.transport_whole]
  rfl

end powerlib.Circuits.RL
