import theorem.Family.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Order.IsLUB

/-! # Envelope sentences: horizons, levels, safe sets and storage certificates

The finite-time sentences about an operating envelope (`theorem/Port/Defs.lean`) carry
parameters: a horizon and a probability level in the sentence, an initial set and a safe set in
the system. This module proves how the denotations depend on them.

The horizon and the level enter through Galois connections. The infinite horizon is the meet of
the finite horizons, and the generated adjoints of the two connections are the longest certified
horizon and the worst exceedance probability of a set of models. The safe set enters through
meets only when the sentence is almost sure: the safe sets certified almost surely are closed
under countable intersections, and an undisturbed system is safe exactly when its reachable set
lies in the safe set, so the reachable set is the least certified safe set. At a positive
probability level two certified safe sets can have an uncertified intersection, and no least
certified safe set exists.

A storage that starts below `v₀` on the initial set, is at least `ℓ` outside the safe set and grows
along every solution at most at a random rate `c ω` bounds the exceedance probability over a
horizon `T` by `E[c] T / (ℓ − v₀)`: the pathwise form of Kushner's finite-time bound, whose rate
term is the expected growth. A mean-square bound bounds, at each time, the probability of a large
state.

Scope.
* Generic: arbitrary families with `n` states and `p` ports read by the single semantics, and the
  random continuous-time systems with an envelope (`Behaviour.disturbed`: a system for each sample
  of the disturbance, read under zero input); no model. Probabilities are outer measures of the
  exceedance events: no measurability is assumed except where an expectation is taken (Markov's
  inequality).
* The disturbance is a random, time-invariant perturbation of the system; no stochastic integral
  is involved.

Source: finite-time stability over a horizon with given bounds (Dorato 1961; Amato, Ariola and
Dorato 2001) and its stochastic form bounded through a nonnegative storage (Kushner 1966); the
engineering reading of stability as the exceedance of thresholds on a few physical quantities
(work-sync `theory/T-converter-stochastic-paradigm.md` §1.3, F3); generated adjoints
(`theorem/TMIO/Generate.lean`). Scaffold: `theorem/Envelope.agda`.

Results.
* Horizons: `exceeds_mono`, `exceeds_sSup_iff`, `exceedance_mono`, `exceedance_sSup` (continuity
  from below, no measurability), `holds_safe_sSup`, `den_safe_sSup` (the infinite horizon is the
  meet of the finite horizons), `den_safe_antitone`, `holds_meanSquare_sSup`.
* Levels: `holds_safe_iInf`, `den_safe_iInf`, `holds_meanSquare_iInf`.
* The connections: `certifiedHorizon F ε` and `worstExceedance F T`, arbitrary-infimum
  preserving maps from sets of models; `le_certifiedHorizon_iff`, `gc_certifiedHorizon`,
  `generate_certifiedHorizon`, `gc_worstExceedance`, `generate_worstExceedance` (the generated
  adjoints are the safety denotations).
* Safe sets: `exceedance_antitone_safe`, `holds_safe_iInter_null` (almost surely: countable
  intersections), `holds_safe_undisturbed_iff`, `isLeast_safe_undisturbed` (the reachable set is
  the least certified safe set); `not_holds_safe_inter`, `not_isLeast_safe` (at a positive level,
  for the drift `ẋ = ω₀` from the origin with `ω₀ = ±1`, each with probability `1/2`);
  `drift_exceeds_iff` (the drift leaves a set exactly when the line `t ↦ c t` does).
* Certificates: `exceedance_le_of_storage` (Kushner's bound), `holds_safe_of_storage`;
  `meas_ge_le_of_meanSquare` (a mean-square bound bounds the probability of a large state at each
  time).

Family and connection conclusions.
* No family: the laws hold for every family, which uses them through its own denotations.
-/

noncomputable section

namespace powerlib.Envelope

open MeasureTheory Set TMIO OrderDual Filter Topology
open scoped ENNReal

variable {n p : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## Horizons -/

/-- A later horizon leaves more time to leave the safe set. -/
@[tmio T, powerlib_foundation] theorem exceeds_mono {s : Port.System n p} {S A : Set ℝⁿ}
    {T T' : ℝ≥0∞} (h : T ≤ T') (he : s.Exceeds S A T) : s.Exceeds S A T' := by
  obtain ⟨x, t, ht, hT, hS, hx, hA⟩ := he
  exact ⟨x, t, ht, hT.trans_le h, hS, hx, hA⟩

/-- Leaving before the supremum of a set of horizons is leaving before one of them. -/
@[powerlib_foundation] theorem exceeds_sSup_iff {s : Port.System n p} {S A : Set ℝⁿ}
    {H : Set ℝ≥0∞} : s.Exceeds S A (sSup H) ↔ ∃ T ∈ H, s.Exceeds S A T := by
  constructor
  · rintro ⟨x, t, ht, hT, hS, hx, hA⟩
    obtain ⟨T, hTH, hlt⟩ := lt_sSup_iff.mp hT
    exact ⟨T, hTH, x, t, ht, hlt, hS, hx, hA⟩
  · rintro ⟨T, hTH, he⟩
    exact exceeds_mono (le_sSup hTH) he

/-- The exceedance probability grows with the horizon. -/
@[powerlib_foundation] theorem exceedance_mono (b : Behaviour n p) {T T' : ℝ≥0∞} (h : T ≤ T') :
    b.exceedance T ≤ b.exceedance T' := by
  cases b with
  | continuous s => exact le_rfl
  | discrete s => exact le_rfl
  | disturbed s S A ν => exact measure_mono fun ω hω => exceeds_mono h hω

/-- Continuity from below: the exceedance probability at the supremum of a set of horizons is the
supremum of the exceedance probabilities. No measurability is needed. -/
@[powerlib_foundation] theorem exceedance_sSup (b : Behaviour n p) (H : Set ℝ≥0∞) :
    b.exceedance (sSup H) = ⨆ T ∈ H, b.exceedance T := by
  refine le_antisymm ?_ (iSup₂_le fun T hT => exceedance_mono b (le_sSup hT))
  rcases H.eq_empty_or_nonempty with rfl | hH
  · cases b with
    | continuous s => exact zero_le
    | discrete s => exact zero_le
    | disturbed s S A ν =>
      refine le_of_eq_of_le (measure_mono_null (fun ω hω => ?_) measure_empty) zero_le
      obtain ⟨x, t, -, hT, -⟩ := hω
      rw [sSup_empty] at hT
      exact (not_lt_bot hT).elim
  · cases b with
    | continuous s => exact zero_le
    | discrete s => exact zero_le
    | disturbed s S A ν =>
      obtain ⟨u, hmono, hlim, hmem⟩ := exists_seq_tendsto_sSup hH (OrderTop.bddAbove H)
      have hsub : {ω | (s ω).Exceeds S A (sSup H)} ⊆ ⋃ k, {ω | (s ω).Exceeds S A (u k)} := by
        rintro ω ⟨x, t, ht, hT, hS, hx, hA⟩
        obtain ⟨k, hk⟩ := (hlim.eventually (lt_mem_nhds hT)).exists
        exact mem_iUnion.mpr ⟨k, x, t, ht, hk, hS, hx, hA⟩
      calc ν {ω | (s ω).Exceeds S A (sSup H)}
          ≤ ν (⋃ k, {ω | (s ω).Exceeds S A (u k)}) := measure_mono hsub
        _ = ⨆ k, ν {ω | (s ω).Exceeds S A (u k)} :=
          Monotone.measure_iUnion fun i j hij ω hω => exceeds_mono (hmono hij) hω
        _ ≤ ⨆ T ∈ H, (Behaviour.disturbed s S A ν).exceedance T :=
          iSup_le fun k => le_iSup₂_of_le (u k) (hmem k) le_rfl

/-- The safety sentence at the supremum of a set of horizons is the conjunction of the safety
sentences at the horizons of the set. -/
@[powerlib_foundation] theorem holds_safe_sSup (b : Behaviour n p) (H : Set ℝ≥0∞) (ε : ℝ≥0∞) :
    (Sentence.envelope (.safe (sSup H) ε)).holds b ↔
      ∀ T ∈ H, (Sentence.envelope (.safe T ε)).holds b := by
  simp only [Sentence.holds_safe_iff_exceedance, exceedance_sSup, iSup₂_le_iff]

/-- The infinite horizon is the meet of the finite horizons: the denotation of safety at the
supremum of a set of horizons is the intersection of the denotations, for every family. -/
@[tmio TM, powerlib_foundation] theorem den_safe_sSup {X Q : Type*} (F : Family X Q n p) (H : Set ℝ≥0∞)
    (ε : ℝ≥0∞) :
    connection% (F.den (.envelope (.safe (sSup H) ε)) =
      ⋂ T ∈ H, F.den (.envelope (.safe T ε))) := by
  unfold powerlib.TMIO.Statement
  ext x
  simp only [Family.mem_den, mem_iInter₂]
  exact holds_safe_sSup _ H ε

/-- Safety over a longer horizon is safety over a shorter one. -/
@[tmio TM, powerlib_foundation] theorem den_safe_antitone {X Q : Type*} (F : Family X Q n p) (ε : ℝ≥0∞)
    {T T' : ℝ≥0∞} (h : T ≤ T') :
    connection% (F.den (.envelope (.safe T' ε)) ⊆ F.den (.envelope (.safe T ε))) := show F.den (.envelope (.safe T' ε)) ⊆ F.den (.envelope (.safe T ε)) from fun x hx => by
  rw [(connection_proof% Family.mem_den), Sentence.holds_safe_iff_exceedance] at hx ⊢
  exact (exceedance_mono _ h).trans hx

/-- The mean-square sentence at the supremum of a set of horizons is the conjunction of the
mean-square sentences at the horizons of the set. -/
@[powerlib_foundation] theorem holds_meanSquare_sSup (b : Behaviour n p) (H : Set ℝ≥0∞)
    (c : ℝ≥0∞) :
    (Sentence.envelope (.meanSquare (sSup H) c)).holds b ↔
      ∀ T ∈ H, (Sentence.envelope (.meanSquare T c)).holds b := by
  cases b with
  | continuous s => exact ⟨fun _ _ _ => trivial, fun _ => trivial⟩
  | discrete s => exact ⟨fun _ _ _ => trivial, fun _ => trivial⟩
  | disturbed s S A ν =>
    simp only [Sentence.holds_meanSquare_disturbed]
    constructor
    · intro h T hT t ht htT
      exact h t ht (htT.trans_le (le_sSup hT))
    · intro h t ht htT
      obtain ⟨T, hT, hlt⟩ := lt_sSup_iff.mp htT
      exact h T hT t ht hlt

/-! ## Levels -/

/-- The safety sentence at the infimum of levels is the conjunction of the safety sentences at
the levels. -/
@[powerlib_foundation] theorem holds_safe_iInf {ι : Sort*} (b : Behaviour n p) (T : ℝ≥0∞)
    (ε : ι → ℝ≥0∞) :
    (Sentence.envelope (.safe T (⨅ i, ε i))).holds b ↔
      ∀ i, (Sentence.envelope (.safe T (ε i))).holds b := by
  simp only [Sentence.holds_safe_iff_exceedance, le_iInf_iff]

/-- The denotation of safety at the infimum of levels is the intersection of the denotations. -/
@[tmio TM, powerlib_foundation] theorem den_safe_iInf {X Q : Type*} {ι : Sort*} (F : Family X Q n p)
    (T : ℝ≥0∞) (ε : ι → ℝ≥0∞) :
    connection% (F.den (.envelope (.safe T (⨅ i, ε i))) = ⋂ i, F.den (.envelope (.safe T (ε i)))) := by
  change F.den (.envelope (.safe T (⨅ i, ε i))) = ⋂ i, F.den (.envelope (.safe T (ε i)))
  ext x
  simp only [Family.mem_den, mem_iInter]
  exact holds_safe_iInf _ T ε

/-- The mean-square sentence at the infimum of bounds is the conjunction of the mean-square
sentences at the bounds. -/
@[powerlib_foundation] theorem holds_meanSquare_iInf {ι : Sort*} (b : Behaviour n p) (T : ℝ≥0∞)
    (c : ι → ℝ≥0∞) :
    (Sentence.envelope (.meanSquare T (⨅ i, c i))).holds b ↔
      ∀ i, (Sentence.envelope (.meanSquare T (c i))).holds b := by
  cases b with
  | continuous s => exact ⟨fun _ _ => trivial, fun _ => trivial⟩
  | discrete s => exact ⟨fun _ _ => trivial, fun _ => trivial⟩
  | disturbed s S A ν =>
    simp only [Sentence.holds_meanSquare_disturbed, le_iInf_iff]
    exact ⟨fun h i t ht htT => h t ht htT i, fun h t ht htT i => h i t ht htT⟩

/-! ## The connections of the horizon and of the level -/

/-- Construction evidence for the horizon upper map. The forward candidate proves the
Galois law here and is therefore the adjoint generated from that map. -/
private def horizonAdjunction {X Q : Type*} (F : Family X Q n p) (ε : ℝ≥0∞) :
    LowerAdjoint (fun D : (Set X)ᵒᵈ => sSup {T | ofDual D ⊆ F.den (.envelope (.safe T ε))}) where
  toFun T := toDual (F.den (.envelope (.safe T ε)))
  gc' T D := by
    change ofDual D ⊆ F.den (.envelope (.safe T ε)) ↔
      T ≤ sSup {T | ofDual D ⊆ F.den (.envelope (.safe T ε))}
    refine ⟨fun h => le_sSup h, fun h => ?_⟩
    have hsup : ofDual D ⊆
        F.den (.envelope (.safe (sSup {T | ofDual D ⊆ F.den (.envelope (.safe T ε))}) ε)) := by
      rw [den_safe_sSup]
      exact subset_iInter₂ fun T hT => hT
    exact hsup.trans (den_safe_antitone F ε h)

/-- The certified horizon: a set of models is sent to the longest horizon over which every model
of the set is safe at the level `ε`. It preserves arbitrary infima (unions of sets of models). -/
def certifiedHorizon {X Q : Type*} (F : Family X Q n p) (ε : ℝ≥0∞) :
    sInfHom (Set X)ᵒᵈ ℝ≥0∞ where
  toFun D := sSup {T | ofDual D ⊆ F.den (.envelope (.safe T ε))}
  map_sInf' _ := by
    rw [sInf_image]
    exact (horizonAdjunction F ε).gc.u_sInf

/-- A horizon is certified for a set of models exactly when it is at most the supremum of the
horizons certified for it, evaluated through the certified-horizon connection. -/
@[tmio TM, powerlib_foundation] theorem le_sSup_certified_iff {X Q : Type*} (F : Family X Q n p)
    (ε : ℝ≥0∞) (D : Set X) (T : ℝ≥0∞) :
    connection% (T ≤ certifiedHorizon F ε (toDual D) ↔ D ⊆ F.den (.envelope (.safe T ε))) :=
  ((horizonAdjunction F ε).gc T (toDual D)).symm

@[tmio TM, powerlib_foundation] theorem le_certifiedHorizon_iff {X Q : Type*} (F : Family X Q n p)
    (ε : ℝ≥0∞) (D : (Set X)ᵒᵈ) (T : ℝ≥0∞) :
    connection% (T ≤ certifiedHorizon F ε D ↔ ofDual D ⊆ F.den (.envelope (.safe T ε))) := show T ≤ certifiedHorizon F ε D ↔ ofDual D ⊆ F.den (.envelope (.safe T ε)) from
  le_sSup_certified_iff F ε (ofDual D) T

/-- The certified horizon is the upper adjoint of the safety denotation along the horizon. -/
@[tmio TM, powerlib_foundation] theorem gc_certifiedHorizon {X Q : Type*} (F : Family X Q n p)
    (ε : ℝ≥0∞) :
    connection% (GaloisConnection (fun T => toDual (F.den (.envelope (.safe T ε)))) (certifiedHorizon F ε)) := show GaloisConnection (fun T => toDual (F.den (.envelope (.safe T ε)))) (certifiedHorizon F ε) from
  fun T D => by
    rw [toDual_le, (connection_proof% le_certifiedHorizon_iff)]

/-- The adjoint generated from the certified horizon is the safety denotation. -/
@[tmio TM, powerlib_foundation] theorem generate_certifiedHorizon {X Q : Type*} (F : Family X Q n p)
    (ε : ℝ≥0∞) :
    connection% (⇑(generate (certifiedHorizon F ε)) = fun T => toDual (F.den (.envelope (.safe T ε)))) := show ⇑(generate (certifiedHorizon F ε)) = fun T => toDual (F.den (.envelope (.safe T ε))) from
  (generate_unique _ (gc_certifiedHorizon F ε)).symm

/-- The worst exceedance: a set of models is sent to the largest exceedance probability over the
horizon `T` among its models (in the dual order). It preserves arbitrary infima. -/
def worstExceedance {X Q : Type*} (F : Family X Q n p) (T : ℝ≥0∞) :
    sInfHom (Set X)ᵒᵈ ℝ≥0∞ᵒᵈ where
  toFun D := toDual (⨆ x ∈ ofDual D, (F.system x).exceedance T)
  map_sInf' 𝒟 := by
    refine eq_of_forall_le_iff fun e => ?_
    rw [le_toDual, le_sInf_iff, forall_mem_image, iSup₂_le_iff, ofDual_sInf, sSup_eq_sUnion]
    constructor
    · intro h D hD
      rw [le_toDual, iSup₂_le_iff]
      exact fun x hx => h x ⟨ofDual D, hD, hx⟩
    · rintro h x ⟨D, hD, hx⟩
      exact iSup₂_le_iff.mp (le_toDual.mp (h hD)) x hx

/-- The worst exceedance is the upper adjoint of the safety denotation along the level. -/
@[tmio TM, powerlib_foundation] theorem gc_worstExceedance {X Q : Type*} (F : Family X Q n p)
    (T : ℝ≥0∞) :
    connection% (GaloisConnection (fun ε : ℝ≥0∞ᵒᵈ => toDual (F.den (.envelope (.safe T (ofDual ε)))))
      (worstExceedance F T)) := show GaloisConnection (fun ε : ℝ≥0∞ᵒᵈ => toDual (F.den (.envelope (.safe T (ofDual ε)))))
      (worstExceedance F T) from fun ε D => by
  change toDual _ ≤ D ↔ ε ≤ toDual (⨆ x ∈ ofDual D, (F.system x).exceedance T)
  rw [toDual_le, le_toDual, iSup₂_le_iff]
  exact ⟨fun h x hx => (Sentence.holds_safe_iff_exceedance _ _ _).mp ((Family.mem_den _).mp (h hx)),
    fun h x hx => (Family.mem_den _).mpr ((Sentence.holds_safe_iff_exceedance _ _ _).mpr (h x hx))⟩

/-- The adjoint generated from the worst exceedance is the safety denotation. -/
@[tmio TM, powerlib_foundation] theorem generate_worstExceedance {X Q : Type*} (F : Family X Q n p)
    (T : ℝ≥0∞) :
    connection% (⇑(generate (worstExceedance F T)) =
      fun ε : ℝ≥0∞ᵒᵈ => toDual (F.den (.envelope (.safe T (ofDual ε))))) := show ⇑(generate (worstExceedance F T)) =
      fun ε : ℝ≥0∞ᵒᵈ => toDual (F.den (.envelope (.safe T (ofDual ε)))) from
  (generate_unique _ (gc_worstExceedance F T)).symm

/-! ## Safe sets -/

/-- A larger safe set is left less often. -/
@[powerlib_foundation] theorem exceedance_antitone_safe (s : Sample → Port.System n p)
    (S : Set ℝⁿ) (ν : Measure Sample) (T : ℝ≥0∞) {A A' : Set ℝⁿ} (h : A ⊆ A') :
    (Behaviour.disturbed s S A' ν).exceedance T ≤ (Behaviour.disturbed s S A ν).exceedance T :=
  measure_mono fun _ ⟨x, t, ht, hT, hS, hx, hA⟩ => ⟨x, t, ht, hT, hS, hx, fun h' => hA (h h')⟩

/-- Almost surely, safety in an intersection of countably many safe sets is safety in each. -/
@[powerlib_foundation] theorem holds_safe_iInter_null {ι : Type*} [Countable ι]
    (s : Sample → Port.System n p) (S : Set ℝⁿ) (ν : Measure Sample) (T : ℝ≥0∞)
    (A : ι → Set ℝⁿ) :
    (Sentence.envelope (.safe T 0)).holds (Behaviour.disturbed s S (⋂ i, A i) ν) ↔
      ∀ i, (Sentence.envelope (.safe T 0)).holds (Behaviour.disturbed s S (A i) ν) := by
  simp only [Sentence.holds_safe_disturbed, nonpos_iff_eq_zero]
  have hU : {ω | (s ω).Exceeds S (⋂ i, A i) T} = ⋃ i, {ω | (s ω).Exceeds S (A i) T} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨x, t, ht, hT, hS, hx, hA⟩
      obtain ⟨i, hi⟩ := not_forall.mp (fun h => hA (mem_iInter.mpr h))
      exact ⟨i, x, t, ht, hT, hS, hx, hi⟩
    · rintro ⟨i, x, t, ht, hT, hS, hx, hA⟩
      exact ⟨x, t, ht, hT, hS, hx, fun h => hA (mem_iInter.mp h i)⟩
  rw [hU, measure_iUnion_null_iff]

/-- An undisturbed system with an envelope (the same system for every sample) is safe at a level
below one exactly when the states it reaches before the horizon lie in the safe set. -/
@[powerlib_foundation] theorem holds_safe_undisturbed_iff (s : Port.System n p) (S A : Set ℝⁿ)
    (ν : Measure Sample) [IsProbabilityMeasure ν] (T : ℝ≥0∞) {ε : ℝ≥0∞} (hε : ε < 1) :
    (Sentence.envelope (.safe T ε)).holds (Behaviour.disturbed (fun _ => s) S A ν) ↔
      s.reach S T ⊆ A := by
  rw [Sentence.holds_safe_disturbed]
  by_cases h : s.Exceeds S A T
  · have hU : {_ω : Sample | s.Exceeds S A T} = univ := eq_univ_of_forall fun _ => h
    rw [hU, measure_univ]
    exact iff_of_false (not_le.mpr hε) ((s.exceeds_iff_not_reach_subset S A T).mp h)
  · have hE : {_ω : Sample | s.Exceeds S A T} = ∅ := eq_empty_of_forall_notMem fun _ => h
    rw [hE, measure_empty]
    exact iff_of_true zero_le
      (not_not.mp fun h' => h ((s.exceeds_iff_not_reach_subset S A T).mpr h'))

/-- For an undisturbed system the reachable set is the least certified safe set: the certified
safe sets are exactly its supersets. -/
@[powerlib_foundation] theorem isLeast_safe_undisturbed (s : Port.System n p) (S : Set ℝⁿ)
    (ν : Measure Sample) [IsProbabilityMeasure ν] (T : ℝ≥0∞) {ε : ℝ≥0∞} (hε : ε < 1) :
    IsLeast {A | (Sentence.envelope (.safe T ε)).holds (Behaviour.disturbed (fun _ => s) S A ν)}
      (s.reach S T) :=
  ⟨(holds_safe_undisturbed_iff s S _ ν T hε).mpr subset_rfl,
    fun _ hA => (holds_safe_undisturbed_iff s S _ ν T hε).mp hA⟩

/-! ## A positive level does not preserve meets -/

/-- The unit vector of the scalar state. -/
def e₁ : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1

@[simp] theorem smul_e₁_apply (a : ℝ) : (a • e₁) 0 = a := by
  simp [e₁]

/-- The scalar drift `ẋ = c`. -/
def drift (c : ℝ) : Port.System 1 1 := ⟨fun _ _ => c • e₁, fun _ _ => 0⟩

theorem hasDerivAt_line (c τ : ℝ) : HasDerivAt (fun τ : ℝ => (c * τ) • e₁) (c • e₁) τ := by
  simpa using ((hasDerivAt_id τ).const_mul c).smul_const e₁

/-- The solution of the drift `ẋ = c` from the origin is `τ ↦ c τ`. -/
@[powerlib_foundation] theorem drift_trajectory {c t : ℝ} {x : ℝ → EuclideanSpace ℝ (Fin 1)}
    (h0 : x 0 = 0) (hx : (drift c).IsTrajectoryOn 0 x 0 t) :
    ∀ τ ∈ Icc 0 t, x τ = (c * τ) • e₁ :=
  eq_of_has_deriv_right_eq (f' := fun _ => c • e₁)
    (fun τ hτ => (hx τ (Ico_subset_Icc_self hτ)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hτ))
    (fun τ _ => (hasDerivAt_line c τ).hasDerivWithinAt) (fun τ hτ => (hx τ hτ).continuousWithinAt)
    (fun τ _ => (hasDerivAt_line c τ).continuousAt.continuousWithinAt) (by simp [h0])

/-- The drift from the origin leaves a set before the horizon exactly when the line `τ ↦ c τ`
does. -/
@[powerlib_foundation] theorem drift_exceeds_iff {c : ℝ} {A : Set (EuclideanSpace ℝ (Fin 1))}
    {T : ℝ≥0∞} :
    (drift c).Exceeds {0} A T ↔ ∃ t, 0 ≤ t ∧ ENNReal.ofReal t < T ∧ (c * t) • e₁ ∉ A := by
  constructor
  · rintro ⟨x, t, ht, hT, hS, hx, hA⟩
    rw [drift_trajectory hS hx t ⟨ht, le_rfl⟩] at hA
    exact ⟨t, ht, hT, hA⟩
  · rintro ⟨t, ht, hT, hA⟩
    exact ⟨fun τ => (c * τ) • e₁, t, ht, hT, by simp,
      fun τ _ => (hasDerivAt_line c τ).hasDerivWithinAt, hA⟩

/-- The random drift `ẋ = ω₀`: the drift read from the first coordinate of the sample. -/
def randomDrift (ω : Sample) : Port.System 1 1 := drift (ω 0)

/-- The constant sample `c`. -/
def constSample (c : ℝ) : Sample := fun _ => c

/-- The two-point disturbance: the drifts `1` and `−1`, each with probability `1/2`. -/
def twoPoint : Measure Sample :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (constSample 1) + Measure.dirac (constSample (-1)))

/-- The safe sets `x < 1/2` and `x > −1/2`. -/
def below : Set (EuclideanSpace ℝ (Fin 1)) := {y | y 0 < 1 / 2}

def above : Set (EuclideanSpace ℝ (Fin 1)) := {y | -1 / 2 < y 0}

theorem exceeds_below_iff (c : ℝ) : (drift c).Exceeds {0} below ⊤ ↔ 0 < c := by
  rw [drift_exceeds_iff]
  simp only [below, mem_ofPred_eq, smul_e₁_apply, not_lt, ENNReal.ofReal_lt_top, true_and]
  constructor
  · rintro ⟨t, ht, h⟩
    by_contra hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) ht]
  · intro hc
    exact ⟨1 / c, by positivity, by rw [mul_one_div_cancel hc.ne']; norm_num⟩

theorem exceeds_above_iff (c : ℝ) : (drift c).Exceeds {0} above ⊤ ↔ c < 0 := by
  rw [drift_exceeds_iff]
  simp only [above, mem_ofPred_eq, smul_e₁_apply, not_lt, ENNReal.ofReal_lt_top, true_and]
  constructor
  · rintro ⟨t, ht, h⟩
    by_contra hc
    nlinarith [mul_nonneg (not_lt.mp hc) ht]
  · intro hc
    exact ⟨-1 / c, div_nonneg_of_nonpos (by norm_num) hc.le, by
      rw [mul_div_assoc', mul_neg_one, neg_div, div_self hc.ne]; norm_num⟩

/-- Leaving a safe set is leaving every smaller one. -/
@[powerlib_foundation] theorem exceeds_antitone_safe {s : Port.System n p} {S A A' : Set ℝⁿ}
    {T : ℝ≥0∞} (h : A' ⊆ A) (he : s.Exceeds S A T) : s.Exceeds S A' T := by
  obtain ⟨x, t, ht, hT, hS, hx, hA⟩ := he
  exact ⟨x, t, ht, hT, hS, hx, fun h' => hA (h h')⟩

theorem twoPoint_apply (E : Set Sample) :
    twoPoint E = 2⁻¹ * (E.indicator 1 (constSample 1) + E.indicator 1 (constSample (-1))) := by
  simp [twoPoint, Measure.dirac_apply, mul_add]

/-- At the level `1/2`, the random drift from the origin with `ω₀ = ±1` is safe in `x < 1/2` and
in `x > −1/2` over the infinite horizon, but not in their intersection: each drift leaves exactly
one of the two sets. -/
@[tmio T, powerlib_foundation] theorem not_holds_safe_inter :
    (Sentence.envelope (.safe ⊤ 2⁻¹)).holds (Behaviour.disturbed randomDrift {0} below twoPoint) ∧
      (Sentence.envelope (.safe ⊤ 2⁻¹)).holds
        (Behaviour.disturbed randomDrift {0} above twoPoint) ∧
      ¬ (Sentence.envelope (.safe ⊤ 2⁻¹)).holds
        (Behaviour.disturbed randomDrift {0} (below ∩ above) twoPoint) := by
  have hbp : (randomDrift (constSample 1)).Exceeds {0} below ⊤ :=
    (exceeds_below_iff 1).mpr one_pos
  have hbm : ¬ (randomDrift (constSample (-1))).Exceeds {0} below ⊤ :=
    fun h => absurd ((exceeds_below_iff (-1)).mp h) (by norm_num)
  have hap : ¬ (randomDrift (constSample 1)).Exceeds {0} above ⊤ :=
    fun h => absurd ((exceeds_above_iff 1).mp h) (by norm_num)
  have ham : (randomDrift (constSample (-1))).Exceeds {0} above ⊤ :=
    (exceeds_above_iff (-1)).mpr (by norm_num)
  let E : Set (EuclideanSpace ℝ (Fin 1)) → Set Sample :=
    fun A => {ω | (randomDrift ω).Exceeds {0} A ⊤}
  have hI : ∀ A, E A = {ω | (randomDrift ω).Exceeds {0} A ⊤} := fun _ => rfl
  simp only [Sentence.holds_safe_disturbed, twoPoint_apply, ← hI]
  refine ⟨?_, ?_, ?_⟩
  · rw [indicator_of_mem (show constSample 1 ∈ E below from hbp),
      indicator_of_notMem (show constSample (-1) ∉ E below from hbm)]
    simp
  · rw [indicator_of_notMem (show constSample 1 ∉ E above from hap),
      indicator_of_mem (show constSample (-1) ∈ E above from ham)]
    simp
  · have hp : constSample 1 ∈ E (below ∩ above) := exceeds_antitone_safe inter_subset_left hbp
    have hm : constSample (-1) ∈ E (below ∩ above) := exceeds_antitone_safe inter_subset_right ham
    rw [indicator_of_mem hp, indicator_of_mem hm]
    simp only [Pi.one_apply, one_add_one_eq_two,
      ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, not_le]
    exact ENNReal.inv_lt_one.mpr ENNReal.one_lt_two

/-- At a positive level the certified safe sets have no least element: the random drift with
`ω₀ = ±1` at the level `1/2`. -/
@[powerlib_foundation] theorem not_isLeast_safe :
    ¬ ∃ L, IsLeast {A | (Sentence.envelope (.safe ⊤ 2⁻¹)).holds
      (Behaviour.disturbed randomDrift {0} A twoPoint)} L := by
  rintro ⟨L, hL, hlow⟩
  obtain ⟨hb, ha, hba⟩ := not_holds_safe_inter
  apply hba
  exact (Sentence.holds_safe_iff_exceedance _ _ _).mpr
    ((exceedance_antitone_safe randomDrift {0} twoPoint ⊤
      (subset_inter (hlow hb) (hlow ha))).trans ((Sentence.holds_safe_iff_exceedance _ _ _).mp hL))

/-! ## Certificates -/

/-- **Kushner's bound, pathwise.** A storage `V` that is at most `v₀` on the initial set, at least
`ℓ > v₀` outside the safe set, and grows along every solution of the sample `ω` at most at the
rate `c ω` bounds the probability of leaving the safe set before the horizon `T` by
`E[c] T / (ℓ − v₀)`. -/
@[powerlib_foundation] theorem exceedance_le_of_storage {s : Sample → Port.System n p}
    {S A : Set ℝⁿ} {ν : Measure Sample} {T : ℝ≥0∞} (V : ℝⁿ → ℝ≥0∞) (c : Sample → ℝ≥0∞)
    {v₀ ℓ : ℝ≥0∞} (hS : ∀ x ∈ S, V x ≤ v₀) (hA : ∀ x ∉ A, ℓ ≤ V x) (hv : v₀ < ℓ) (hℓ : ℓ ≠ ⊤)
    (hV : ∀ ω (x : ℝ → ℝⁿ) (t : ℝ), 0 ≤ t → (s ω).IsTrajectoryOn 0 x 0 t →
      V (x t) ≤ V (x 0) + c ω * ENNReal.ofReal t)
    (hmeas : AEMeasurable c ν) :
    (Behaviour.disturbed s S A ν).exceedance T ≤ (∫⁻ ω, c ω ∂ν) * T / (ℓ - v₀) := by
  have hsub : {ω | (s ω).Exceeds S A T} ⊆ {ω | ℓ - v₀ ≤ c ω * T} := by
    rintro ω ⟨x, t, ht, hT, hx0, hx, hxA⟩
    calc ℓ - v₀ ≤ V (x t) - V (x 0) := tsub_le_tsub (hA _ hxA) (hS _ hx0)
      _ ≤ c ω * ENNReal.ofReal t := tsub_le_iff_left.mpr (hV ω x t ht hx)
      _ ≤ c ω * T := by gcongr
  calc ν {ω | (s ω).Exceeds S A T}
      ≤ ν {ω | ℓ - v₀ ≤ c ω * T} := measure_mono hsub
    _ ≤ (∫⁻ ω, c ω * T ∂ν) / (ℓ - v₀) :=
      meas_ge_le_lintegral_div (hmeas.mul_const T) (tsub_pos_of_lt hv).ne' (ENNReal.sub_ne_top hℓ)
    _ = (∫⁻ ω, c ω ∂ν) * T / (ℓ - v₀) := by rw [lintegral_mul_const'' T hmeas]

/-- The storage certifies safety at every level above Kushner's bound. -/
@[powerlib_foundation] theorem holds_safe_of_storage {s : Sample → Port.System n p}
    {S A : Set ℝⁿ} {ν : Measure Sample} {T ε : ℝ≥0∞} (V : ℝⁿ → ℝ≥0∞) (c : Sample → ℝ≥0∞)
    {v₀ ℓ : ℝ≥0∞} (hS : ∀ x ∈ S, V x ≤ v₀) (hA : ∀ x ∉ A, ℓ ≤ V x) (hv : v₀ < ℓ) (hℓ : ℓ ≠ ⊤)
    (hV : ∀ ω (x : ℝ → ℝⁿ) (t : ℝ), 0 ≤ t → (s ω).IsTrajectoryOn 0 x 0 t →
      V (x t) ≤ V (x 0) + c ω * ENNReal.ofReal t)
    (hmeas : AEMeasurable c ν) (hε : (∫⁻ ω, c ω ∂ν) * T / (ℓ - v₀) ≤ ε) :
    (Sentence.envelope (.safe T ε)).holds (Behaviour.disturbed s S A ν) :=
  (Sentence.holds_safe_iff_exceedance _ _ _).mpr
    ((exceedance_le_of_storage V c hS hA hv hℓ hV hmeas).trans hε)

/-- A mean-square bound bounds, at each time before the horizon, the probability that some solution
from the initial set has norm at least `r`. -/
@[powerlib_foundation] theorem meas_ge_le_of_meanSquare {s : Sample → Port.System n p}
    {S A : Set ℝⁿ} {ν : Measure Sample} {T c r : ℝ≥0∞}
    (h : (Sentence.envelope (.meanSquare T c)).holds (Behaviour.disturbed s S A ν)) {t : ℝ}
    (ht : 0 ≤ t) (htT : ENNReal.ofReal t < T) (hr : r ≠ 0) (hr' : r ≠ ⊤)
    (hmeas : AEMeasurable (fun ω => (s ω).squareAt S t) ν) :
    ν {ω | ∃ x : ℝ → ℝⁿ, x 0 ∈ S ∧ (s ω).IsTrajectoryOn 0 x 0 t ∧ r ≤ ‖x t‖ₑ} ≤ c / r ^ 2 := by
  have hsub : {ω | ∃ x : ℝ → ℝⁿ, x 0 ∈ S ∧ (s ω).IsTrajectoryOn 0 x 0 t ∧ r ≤ ‖x t‖ₑ} ⊆
      {ω | r ^ 2 ≤ (s ω).squareAt S t} := by
    rintro ω ⟨x, hx0, hx, hrx⟩
    exact (pow_le_pow_left₀ zero_le hrx 2).trans
      (le_iSup₂ (f := fun (x : ℝ → ℝⁿ) (_ : x 0 ∈ S ∧ (s ω).IsTrajectoryOn 0 x 0 t) =>
        ‖x t‖ₑ ^ 2) x ⟨hx0, hx⟩)
  calc _ ≤ ν {ω | r ^ 2 ≤ (s ω).squareAt S t} := measure_mono hsub
    _ ≤ (∫⁻ ω, (s ω).squareAt S t ∂ν) / r ^ 2 :=
      meas_ge_le_lintegral_div hmeas (pow_ne_zero 2 hr) (ENNReal.pow_ne_top hr')
    _ ≤ c / r ^ 2 := ENNReal.div_le_div_right
      ((Sentence.holds_meanSquare_disturbed T c s S A ν).mp h t ht htT) _

end powerlib.Envelope
