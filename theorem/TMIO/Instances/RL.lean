import theorem.RLStability
import theorem.TMIO.Instances.Analysis

/-! # The RL instance of TMIO

Model boundary: the canonical single-port RL family of `theorem.RL` with the trajectory semantics
of `theorem.RLStability`. The single state is the physical branch current in a stationary frame;
the dynamics `L * i' = v - R * i` are in continuous time from `t = 0`; `L > 0` and `R` is real.
Stability sentences concern the zero equilibrium with zero input. No controller, feedback
interconnection, PWM, PLL, delay, switching or discretization is included.

The seed is the standard relational seed:

* T: sets of sentences (`Sentence`), ordered by inclusion;
* M: sets of parameter-box requirements (`Requirement`), ordered by inclusion;
* I: sets of complete impedance models, ordered by reverse inclusion;
* O: sets of DC resistance readings, ordered by reverse inclusion. A model may produce the
  reading `r` exactly when `|r - R| ≤ ε` for the accuracy `ε`; the inductance is not observed.

Only the translation table, the satisfaction relation and the reading relation are supplied.
Spaces, certified readings, candidates and the observation closure are generated. DC test records
attach to O through the least-squares analysis of `Analysis`, as one more generated edge; the
state-space representation is reached by transporting the seed along `modelEquiv`. -/

noncomputable section

namespace powerlib.TMIO.RL

open OrderDual powerlib powerlib.TMIO.Analysis

/-! ## Supplied semantics -/

/-- Theory sentences about the RL model. -/
inductive Sentence
  /-- The zero equilibrium with zero input is asymptotically stable (trajectory semantics). -/
  | asymptoticallyStable
  /-- Positive resistance and time constant `L / R` of at most one second (parametric). -/
  | timeConstantAtMostOne

/-- The models satisfying each sentence. -/
def Sentence.den : Sentence → Set Impedance
  | .asymptoticallyStable => {m | AsymptoticallyStable m 0 0}
  | .timeConstantAtMostOne => {m | 0 < m.resistance ∧ m.inductance.val ≤ m.resistance}

/-- Engineering requirements: parameter boxes. -/
inductive Requirement
  | positiveResistance
  | resistanceAtLeast (r : ℝ)
  | resistanceAtMost (r : ℝ)
  | inductanceAtLeast (l : ℝ)
  | inductanceAtMost (l : ℝ)

/-- Satisfaction of a requirement by a complete impedance model. -/
def Meets (m : Impedance) : Requirement → Prop
  | .positiveResistance => 0 < m.resistance
  | .resistanceAtLeast r => r ≤ m.resistance
  | .resistanceAtMost r => m.resistance ≤ r
  | .inductanceAtLeast l => l ≤ m.inductance.val
  | .inductanceAtMost l => m.inductance.val ≤ l

/-- The translation table from sentences to requirements. -/
def translate : Sentence → Set Requirement
  | .asymptoticallyStable => {.positiveResistance}
  | .timeConstantAtMostOne => {.resistanceAtLeast 1, .inductanceAtMost 1}

/-- The translation as a relation. -/
def translation : SetRel Sentence Requirement := {p | p.2 ∈ translate p.1}

/-- The DC resistance reading with accuracy `ε`. -/
def reading (ε : ℝ) : SetRel Impedance ℝ := {p | |p.2 - p.1.resistance| ≤ ε}

/-- The RL seed. -/
def seed (ε : ℝ) : Seed (Set Sentence) (Set Requirement) (Set Impedance)ᵒᵈ (Set ℝ)ᵒᵈ :=
  relationalSeed translation Meets (reading ε)

/-- The impedance model with resistance `R` and inductance `L`. -/
def rl (R L : ℝ) (hL : 0 < L) : Impedance := ⟨R, ⟨L, hL⟩⟩

@[simp, powerlib_foundation] theorem rl_resistance (R L : ℝ) (hL : 0 < L) :
    (rl R L hL).resistance = R := rfl

@[simp, powerlib_foundation] theorem rl_inductance (R L : ℝ) (hL : 0 < L) :
    (rl R L hL).inductance.val = L := rfl

@[simp, powerlib_foundation] theorem image_translation_singleton (φ : Sentence) :
    translation.image {φ} = translate φ := by
  ext q
  simp [translation]

/-! ## Generated spaces -/

/-- The generated space of the stability requirement. -/
@[powerlib_foundation] theorem realize_positiveResistance :
    realize Meets {Requirement.positiveResistance} = {m | 0 < m.resistance} := by
  ext m
  simp [Meets]

/-- The stability requirement is an exact translation of asymptotic stability. -/
@[powerlib_domain] theorem realize_translate_asymptoticallyStable :
    realize Meets (translate .asymptoticallyStable) = Sentence.den .asymptoticallyStable := by
  ext m
  rw [translate, realize_positiveResistance]
  exact (asymptoticallyStable_iff_resistance_pos (zero_equilibrium m)).symm

/-- Added requirements reuse the conclusion: no new stability proof is needed. -/
@[powerlib_domain] theorem realize_reuse (Δ : Set Requirement) {m : Impedance}
    (hm : m ∈ realize Meets (translate .asymptoticallyStable ∪ Δ)) : AsymptoticallyStable m 0 0 := by
  rw [realize_union, realize_translate_asymptoticallyStable] at hm
  exact hm.1

/-- The box translation of the time-constant sentence is sound. -/
@[powerlib_foundation] theorem realize_translate_timeConstant_subset :
    realize Meets (translate .timeConstantAtMostOne) ⊆ Sentence.den .timeConstantAtMostOne := by
  intro m hm
  rw [mem_realize] at hm
  have hR : 1 ≤ m.resistance := hm (.resistanceAtLeast 1) (by simp [translate])
  have hL : m.inductance.val ≤ 1 := hm (.inductanceAtMost 1) (by simp [translate])
  exact ⟨by linarith, by linarith⟩

/-- It is not exact. -/
@[powerlib_foundation] theorem realize_translate_timeConstant_ne :
    realize Meets (translate .timeConstantAtMostOne) ≠ Sentence.den .timeConstantAtMostOne := by
  intro h
  have hm : rl (1 / 2) (1 / 2) (by norm_num) ∈ Sentence.den .timeConstantAtMostOne := by
    simp [Sentence.den]
  rw [← h, mem_realize] at hm
  have := hm (.resistanceAtLeast 1) (by simp [translate])
  simp [Meets] at this
  linarith

/-- No requirement set is exact for the time-constant sentence: the box language cannot couple
`L` and `R`. -/
@[powerlib_foundation] theorem not_exists_realize_timeConstant :
    ¬ ∃ Γ : Set Requirement, realize Meets Γ = Sentence.den .timeConstantAtMostOne := by
  rintro ⟨Γ, hΓ⟩
  have h11 : rl 1 1 one_pos ∈ realize Meets Γ := hΓ ▸ ⟨by simp, by simp⟩
  have h22 : rl 2 2 two_pos ∈ realize Meets Γ := hΓ ▸ ⟨by simp, by simp⟩
  rw [mem_realize] at h11 h22
  have h12 : rl 1 2 two_pos ∈ realize Meets Γ := by
    rw [mem_realize]
    intro q hq
    have a := h11 q hq
    have b := h22 q hq
    cases q with
    | positiveResistance => exact one_pos
    | resistanceAtLeast r => exact a
    | resistanceAtMost r => exact a
    | inductanceAtLeast l => exact b
    | inductanceAtMost l => exact b
  rw [hΓ] at h12
  have := h12.2
  simp at this

/-! ## Generated observation semantics -/

/-- The certified readings of asymptotic stability, generated along the whole chain. -/
@[powerlib_foundation] theorem certified_readings {ε : ℝ} (hε : 0 ≤ ε) :
    ofDual (generate (seed ε).uTO {Sentence.asymptoticallyStable}) = {r | ε < r} := by
  rw [seed, relationalSeed_whole, image_translation_singleton, translate,
    realize_positiveResistance]
  ext r
  simp only [mem_certify, Set.mem_ofPred_eq]
  constructor
  · intro h
    have hm := h (rl (r - ε) 1 one_pos) (by simp [reading, abs_of_nonneg hε])
    simp only [rl_resistance] at hm
    linarith
  · intro hr m hm
    have := (abs_le.mp (show |r - m.resistance| ≤ ε from hm)).2
    linarith

/-- A reading above the accuracy certifies asymptotic stability of every model that may produce
it. -/
@[powerlib_domain] theorem reading_certifies {ε r : ℝ} (hr : ε < r) {m : Impedance}
    (hm : |r - m.resistance| ≤ ε) : AsymptoticallyStable m 0 0 := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans hm
  have hv : r ∈ ofDual (generate (seed ε).uTO {Sentence.asymptoticallyStable}) := by
    rw [certified_readings hε]
    exact hr
  exact relationalSeed_sound translation Meets (reading ε) (den := Sentence.den)
    (fun φ => by
      cases φ
      · rw [image_translation_singleton, realize_translate_asymptoticallyStable]
      · rw [image_translation_singleton]
        exact realize_translate_timeConstant_subset)
    hv hm _ rfl

/-- The possible readings of stable models, derived from certification by complement. -/
@[powerlib_foundation] theorem predicted_readings {ε : ℝ} (hε : 0 ≤ ε) :
    predict (reading ε) (realize Meets {Requirement.positiveResistance}) = {r | -ε < r} := by
  rw [predict_eq_image, realize_positiveResistance]
  ext r
  simp only [SetRel.mem_image, Set.mem_ofPred_eq, reading]
  constructor
  · rintro ⟨m, hm, hr⟩
    have := (abs_le.mp hr).1
    linarith
  · intro hr
    refine ⟨rl (r + ε) 1 one_pos, by simp; linarith, ?_⟩
    simp [abs_of_nonneg hε]

/-- A reading at or below `-ε` refutes asymptotic stability of every model that may produce it. -/
@[powerlib_domain] theorem reading_refutes {ε r : ℝ} (hr : r ≤ -ε) {m : Impedance}
    (hm : |r - m.resistance| ≤ ε) : ¬ AsymptoticallyStable m 0 0 := by
  intro hs
  have hε : 0 ≤ ε := (abs_nonneg _).trans hm
  have hpos : 0 < m.resistance :=
    (asymptoticallyStable_iff_resistance_pos (zero_equilibrium m)).mp hs
  have hpred : r ∈ predict (reading ε) (realize Meets {Requirement.positiveResistance}) := by
    rw [predict_eq_image]
    exact ⟨m, by simpa [realize_positiveResistance] using hpos, hm⟩
  rw [predicted_readings hε] at hpred
  exact absurd hpred (not_lt.mpr hr)

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

/-- Every observation-closed family of models contains, with a model, all models of the same
resistance. -/
@[powerlib_foundation] theorem closed_resistance (ε : ℝ) {P : (Set Impedance)ᵒᵈ}
    (hP : closure (seed ε).u₃ P = P) {m m' : Impedance} (h : m.resistance = m'.resistance) :
    m ∈ ofDual P ↔ m' ∈ ofDual P := by
  rw [← hP]
  exact closure_resistance ε P h

/-! ## Data records -/

/-- A DC test record is read through its least-squares resistance: the analysis edge of
`Analysis` as a relational observation, with no separate entry point. -/
def recordEdge : sInfHom (Set (Record ℝ))ᵒᵈ (Set ℝ)ᵒᵈ :=
  possibly (Function.graph (estimate (K := ℝ))).inv

/-- The certified records of asymptotic stability: the reading chain extended by the analysis
edge, generated as a composite. -/
@[powerlib_foundation] theorem certified_records {ε : ℝ} (hε : 0 ≤ ε) :
    ofDual (generate ((seed ε).uTO.comp recordEdge) {Sentence.asymptoticallyStable}) =
      {d | ε < estimate d} := by
  rw [generate_comp, Function.comp_apply, recordEdge, congrFun (generate_possibly _)]
  simp only [Function.comp_apply, ofDual_toDual]
  rw [certified_readings hε]
  ext d
  rw [mem_certify]
  change (∀ r, estimate d = r → r ∈ {r | ε < r}) ↔ ε < estimate d
  exact ⟨fun h => h _ rfl, fun h r hr => hr ▸ h⟩

/-- Two DC samples, `(2 V, 1 A)` and `(4 V, 2 A)`. -/
def dcTest : Record ℝ := [⟨2, 1⟩, ⟨4, 2⟩]

@[powerlib_foundation] theorem estimate_dcTest : estimate dcTest = 2 := by
  norm_num [dcTest, estimate, fit, stats]

/-- With accuracy `1/2`, the record `dcTest` certifies asymptotic stability of every RL model that
may have produced it. -/
@[powerlib_domain] theorem dcTest_certifies {m : Impedance}
    (hm : |estimate dcTest - m.resistance| ≤ 1 / 2) : AsymptoticallyStable m 0 0 := by
  have hd : dcTest ∈ ofDual (generate ((seed (1 / 2)).uTO.comp recordEdge)
      {Sentence.asymptoticallyStable}) := by
    rw [certified_records (by norm_num), Set.mem_ofPred_eq, estimate_dcTest]
    norm_num
  rw [certified_records (by norm_num), Set.mem_ofPred_eq] at hd
  exact reading_certifies hd hm

/-! ## The state-space representation -/

/-- The implementation layer in state-space coordinates, along the Agda-generated conversion. -/
def stateSpaceIso : (Set Impedance)ᵒᵈ ≃o (Set StateSpace)ᵒᵈ :=
  (Equiv.toOrderIsoSet modelEquiv.symm).dual

/-- The seed transported to state-space implementations. -/
def stateSpaceSeed (ε : ℝ) :
    Seed (Set Sentence) (Set Requirement) (Set StateSpace)ᵒᵈ (Set ℝ)ᵒᵈ :=
  (seed ε).transport (OrderIso.refl _) (OrderIso.refl _) stateSpaceIso (OrderIso.refl _)

/-- Certified readings do not depend on the implementation representation. -/
@[powerlib_foundation] theorem stateSpace_whole (ε : ℝ) :
    ⇑(generate (stateSpaceSeed ε).uTO) = ⇑(generate (seed ε).uTO) := by
  rw [stateSpaceSeed, Seed.transport_whole]
  rfl

/-- The generated state-space space is the impedance space carried along the conversion. -/
@[powerlib_foundation] theorem stateSpace_space (ε : ℝ) (Γ : Set Requirement) :
    ofDual (generate (stateSpaceSeed ε).u₂ Γ) = modelEquiv.symm '' realize Meets Γ := by
  change ofDual (generate (TMIO.transport (seed ε).u₂ (OrderIso.refl _) stateSpaceIso) Γ) = _
  rw [congrFun (generate_transport _ _ _)]
  rfl

/-- Every state-space model in the generated space of the stability requirement is stable; the
only domain bridge used is `stability_agrees`. -/
@[powerlib_domain] theorem stateSpace_space_stable (ε : ℝ) {s : StateSpace}
    (hs : s ∈ ofDual (generate (stateSpaceSeed ε).u₂ (translate .asymptoticallyStable))) :
    s.Stable := by
  rw [stateSpace_space, translate, realize_positiveResistance] at hs
  obtain ⟨m, hm, rfl⟩ := hs
  exact (stability_agrees m).mpr ((impedance_stable_iff m).mpr hm)

end powerlib.TMIO.RL
