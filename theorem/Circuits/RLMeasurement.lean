import theorem.Circuits.RL
import theorem.Data.Analysis

/-! # Measuring the RL branch

Model boundary: the RL branch of `theorem.Circuits.RL`, with behavioural sentences read through
its plant map (`Linear.den Impedance.plant`). A DC resistance reading `r` with accuracy `ε` may be
produced by a model exactly when `|r - R| ≤ ε`; the inductance is not observed. DC test records
are reduced to readings by the least-squares analysis of `Data.Analysis`.

The seed is the standard relational seed. Only the translation table, the satisfaction relation
and the reading relation are supplied; certified readings, possible readings, candidates and the
observation closure are generated, for all six sentences at once. -/

noncomputable section

namespace powerlib.Circuits.RL

open OrderDual LinearSystems TMIO Data.Analysis

/-- The impedance model with resistance `R` and inductance `L`. -/
def rl (R L : ℝ) (hL : 0 < L) : Impedance := ⟨R, ⟨L, hL⟩⟩

@[simp, powerlib_foundation] theorem rl_resistance (R L : ℝ) (hL : 0 < L) :
    (rl R L hL).resistance = R := rfl

@[simp, powerlib_foundation] theorem rl_inductance (R L : ℝ) (hL : 0 < L) :
    (rl R L hL).inductance.val = L := rfl

/-! ## Sentences as resistance windows -/

/-- The resistances admitted by a sentence. -/
def window : Flow.Property → Set ℝ
  | .lyapunovStable => Set.Ici 0
  | .unstable => Set.Iio 0
  | _ => Set.Ioi 0

/-- Every sentence denotes a resistance window. -/
@[powerlib_domain] theorem den_window (P : Flow.Property) :
    Linear.den Impedance.plant P = {m | m.resistance ∈ window P} := by
  rw [← realize_translate]
  cases P <;> ext m <;> simp [translate, Meets, window]

/-! ## The seed -/

/-- The DC resistance reading with accuracy `ε`. -/
def reading (ε : ℝ) : SetRel Impedance ℝ := {p | |p.2 - p.1.resistance| ≤ ε}

/-- The RL measurement seed: the family's seed for the reading relation. -/
def seed (ε : ℝ) : Seed (Set Flow.Property) (Set Requirement) (Set Impedance)ᵒᵈ (Set ℝ)ᵒᵈ :=
  family.seed (reading ε)

/-- The readings certifying a resistance window. -/
@[powerlib_foundation] theorem certify_reading (ε : ℝ) (S : Set ℝ) :
    certify (reading ε) {m | m.resistance ∈ S} = {r | Set.Icc (r - ε) (r + ε) ⊆ S} := by
  ext r
  simp only [mem_certify, Set.mem_ofPred_eq]
  constructor
  · intro h R hR
    have hm : |r - (rl R 1 one_pos).resistance| ≤ ε := by
      rw [rl_resistance, abs_sub_le_iff]
      exact ⟨by linarith [hR.1], by linarith [hR.2]⟩
    exact h _ hm
  · intro h m hm
    obtain ⟨h1, h2⟩ := abs_sub_le_iff.mp (show |r - m.resistance| ≤ ε from hm)
    exact h ⟨by linarith, by linarith⟩

/-- The certified readings of every sentence, generated along the whole chain: a reading is
certified when its whole accuracy interval lies in the sentence's window. -/
@[powerlib_domain] theorem certified_readings (ε : ℝ) (P : Flow.Property) :
    ofDual (generate (seed ε).uTO {P}) = {r | Set.Icc (r - ε) (r + ε) ⊆ window P} := by
  have h : ofDual (generate (seed ε).uTO {P}) = certify (reading ε) (Linear.den Impedance.plant P) :=
    family.certified (reading ε) (realize_translate P)
  rw [h, den_window, certify_reading]

/-- A certified reading proves every sentence it certifies for every model that may produce it:
the family's generic `certifies`, with the exactness of `realize_translate`. -/
@[powerlib_domain] theorem reading_certifies {ε r : ℝ} {Φ : Set Flow.Property}
    (hr : r ∈ ofDual (generate (seed ε).uTO Φ)) {m : Impedance} (hm : |r - m.resistance| ≤ ε) :
    ∀ P ∈ Φ, P.holds (affineLinearVectorField m.plant.A 0) 0 :=
  family.certifies (fun P _ => (realize_translate P).le) hr hm

/-- With a nonnegative accuracy, the attractive sentences are certified exactly by the readings
above the accuracy. -/
@[powerlib_domain] theorem certified_readings_attractive {ε : ℝ} (hε : 0 ≤ ε)
    {P : Flow.Property} (hP : P.Attractive) :
    ofDual (generate (seed ε).uTO {P}) = {r | ε < r} := by
  rw [certified_readings]
  ext r
  have hw : window P = Set.Ioi 0 := by cases P <;> first | rfl | exact absurd hP id
  rw [hw, Set.mem_ofPred_eq, Set.Icc_subset_Ioi_iff (by linarith), Set.mem_ofPred_eq, sub_pos]

/-- Lyapunov stability is certified by the readings at or above the accuracy. -/
@[powerlib_domain] theorem certified_readings_lyapunovStable {ε : ℝ} (hε : 0 ≤ ε) :
    ofDual (generate (seed ε).uTO {.lyapunovStable}) = {r | ε ≤ r} := by
  rw [certified_readings]
  ext r
  rw [Set.mem_ofPred_eq, window, Set.Icc_subset_Ici_iff (by linarith), Set.mem_ofPred_eq,
    sub_nonneg]

/-- Instability is certified by the readings below minus the accuracy. -/
@[powerlib_domain] theorem certified_readings_unstable {ε : ℝ} (hε : 0 ≤ ε) :
    ofDual (generate (seed ε).uTO {.unstable}) = {r | r < -ε} := by
  rw [certified_readings]
  ext r
  rw [Set.mem_ofPred_eq, window, Set.Icc_subset_Iio_iff (by linarith), Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

/-! ## Possible readings and refutation -/

/-- The possible readings of the models satisfying a sentence, derived from certification by
complement: those whose accuracy interval meets the window. -/
@[powerlib_domain] theorem predicted_readings (ε : ℝ) (P : Flow.Property) :
    predict (reading ε) (Linear.den Impedance.plant P) =
      {r | (Set.Icc (r - ε) (r + ε) ∩ window P).Nonempty} := by
  rw [predict_eq_image, den_window]
  ext r
  simp only [SetRel.mem_image, Set.mem_ofPred_eq, reading]
  constructor
  · rintro ⟨m, hm, hr⟩
    obtain ⟨h1, h2⟩ := abs_sub_le_iff.mp hr
    exact ⟨m.resistance, ⟨by linarith, by linarith⟩, hm⟩
  · rintro ⟨R, hR, hw⟩
    have hm : |r - (rl R 1 one_pos).resistance| ≤ ε := by
      rw [rl_resistance, abs_sub_le_iff]
      exact ⟨by linarith [hR.1], by linarith [hR.2]⟩
    exact ⟨rl R 1 one_pos, hw, hm⟩

/-- A reading outside the possible readings of a sentence refutes it for every model that may
produce the reading. -/
@[powerlib_domain] theorem reading_refutes {ε r : ℝ} {P : Flow.Property}
    (hr : r ∉ predict (reading ε) (Linear.den Impedance.plant P)) {m : Impedance}
    (hm : |r - m.resistance| ≤ ε) : ¬ P.holds (affineLinearVectorField m.plant.A 0) 0 := by
  intro hP
  rw [predict_eq_image] at hr
  exact hr ⟨m, hP, hm⟩

/-- A reading at or below minus the accuracy refutes every attractive sentence. -/
@[powerlib_domain] theorem reading_refutes_attractive {ε r : ℝ} (hr : r ≤ -ε)
    {P : Flow.Property} (hP : P.Attractive) {m : Impedance} (hm : |r - m.resistance| ≤ ε) :
    ¬ P.holds (affineLinearVectorField m.plant.A 0) 0 := by
  refine reading_refutes ?_ hm
  have hw : window P = Set.Ioi 0 := by cases P <;> first | rfl | exact absurd hP id
  rw [predicted_readings, hw]
  rintro ⟨R, hR, hpos⟩
  have := hR.2
  simp only [Set.mem_Ioi] at hpos
  linarith

/-! ## Candidates and the observation closure -/

/-- The candidates of a reading are the semantic map itself. -/
@[powerlib_foundation] theorem candidates (ε r : ℝ) :
    ofDual ((seed ε).u₃ (toDual {r})) = {m : Impedance | |r - m.resistance| ≤ ε} := by
  ext m
  simp [seed, relationalSeed, reading]

/-- The generated observation closure cannot separate models of equal resistance: the inductance
is not identifiable from DC readings. -/
@[powerlib_foundation] theorem closure_resistance (ε : ℝ) (P : (Set Impedance)ᵒᵈ)
    {m m' : Impedance} (h : m.resistance = m'.resistance) :
    m ∈ ofDual (closure (seed ε).u₃ P) ↔ m' ∈ ofDual (closure (seed ε).u₃ P) := by
  change m ∈ ofDual (possibly (reading ε) (generate (possibly (reading ε)) P)) ↔
    m' ∈ ofDual (possibly (reading ε) (generate (possibly (reading ε)) P))
  simp only [mem_possibly, reading, Set.mem_ofPred_eq, h]

/-! ## Test records -/

/-- A DC test record is read through its least-squares resistance: the analysis of
`Data.Analysis` as one more relational observation edge. -/
def recordEdge : sInfHom (Set (Record ℝ))ᵒᵈ (Set ℝ)ᵒᵈ :=
  possibly (Function.graph (estimate (K := ℝ))).inv

/-- The certified records of any sentences: the chain extended by the analysis edge, generated
as a composite, certifies a record exactly when it certifies the record's estimate. -/
@[powerlib_foundation] theorem certified_records (ε : ℝ) (Φ : Set Flow.Property) :
    ofDual (generate ((seed ε).uTO.comp recordEdge) Φ) =
      estimate ⁻¹' ofDual (generate (seed ε).uTO Φ) := by
  rw [generate_comp, Function.comp_apply, recordEdge, generate_possibly_apply]
  ext d
  rw [mem_certify]
  exact ⟨fun h => h _ rfl, fun h r hr => (show estimate d = r from hr) ▸ h⟩

/-- Two DC samples, `(2 V, 1 A)` and `(4 V, 2 A)`. -/
def dcTest : Record ℝ := [⟨2, 1⟩, ⟨4, 2⟩]

@[powerlib_foundation] theorem estimate_dcTest : estimate dcTest = 2 := by
  norm_num [dcTest, estimate, fit, stats]

/-- With accuracy `1/2`, the record `dcTest` proves every attractive sentence for every RL model
that may have produced its estimate. -/
@[powerlib_domain] theorem dcTest_certifies {m : Impedance}
    (hm : |estimate dcTest - m.resistance| ≤ 1 / 2) {P : Flow.Property} (hP : P.Attractive) :
    P.holds (affineLinearVectorField m.plant.A 0) 0 := by
  have hd : dcTest ∈ ofDual (generate ((seed (1 / 2)).uTO.comp recordEdge) {P}) := by
    rw [certified_records, Set.mem_preimage, certified_readings_attractive (by norm_num) hP,
      Set.mem_ofPred_eq, estimate_dcTest]
    norm_num
  rw [certified_records, Set.mem_preimage] at hd
  exact reading_certifies hd hm P rfl

/-! ## The state-space representation -/

/-- The denotation does not depend on the representation: both have the same plant. -/
@[powerlib_foundation] theorem den_stateSpace (P : Flow.Property) :
    Linear.den StateSpace.plant P = toImpedance ⁻¹' Linear.den Impedance.plant P := by
  ext s
  simp [Linear.den]

/-- The RL family read in state-space parameters, through the Agda-generated conversion. -/
def stateSpaceFamily : Linear.Family StateSpace Requirement 1 1 := family.comap toImpedance

/-- The translations stay exact in state-space parameters; nothing is reproved. -/
@[powerlib_domain] theorem stateSpace_exact (P : Flow.Property) : stateSpaceFamily.Exact P :=
  Linear.Family.Exact.comap (F := family) (realize_translate P) toImpedance

/-- The implementation layer in state-space coordinates, along the Agda-generated conversion. -/
def stateSpaceIso : (Set Impedance)ᵒᵈ ≃o (Set StateSpace)ᵒᵈ :=
  (Equiv.toOrderIsoSet modelEquiv.symm).dual

/-- The seed transported to state-space implementations. -/
def stateSpaceSeed (ε : ℝ) :
    Seed (Set Flow.Property) (Set Requirement) (Set StateSpace)ᵒᵈ (Set ℝ)ᵒᵈ :=
  (seed ε).transport (OrderIso.refl _) (OrderIso.refl _) stateSpaceIso (OrderIso.refl _)

/-- Certified readings do not depend on the implementation representation. -/
@[powerlib_foundation] theorem stateSpace_whole (ε : ℝ) :
    ⇑(generate (stateSpaceSeed ε).uTO) = ⇑(generate (seed ε).uTO) := by
  rw [stateSpaceSeed, Seed.transport_whole]
  rfl

/-- The generated state-space space of a translated sentence is its state-space denotation. -/
@[powerlib_domain] theorem stateSpace_space (ε : ℝ) (P : Flow.Property) :
    ofDual (generate (stateSpaceSeed ε).u₂ (translate P)) = Linear.den StateSpace.plant P := by
  change ofDual (generate (TMIO.transport (seed ε).u₂ (OrderIso.refl _) stateSpaceIso)
    (translate P)) = _
  rw [congrFun (generate_transport _ _ _), den_stateSpace]
  change modelEquiv.symm '' realize Meets (translate P) = _
  rw [realize_translate, Equiv.image_eq_preimage_symm]
  rfl

end powerlib.Circuits.RL
