import theorem.Port.Defs

/-! # Storage functions

The general facts about passivity, proved once: a storage whose rate along solutions is bounded
by the supplied power proves passivity; a solution segment returning to its initial state while
drawing net energy out of the ports refutes it; with the ports at zero the storage cannot increase;
a storage between two positive quadratic bounds proves Lyapunov stability of the zero-input field
in the Flow semantics; and a system without ports is passive with the zero storage.

Scope.
* Generic: an arbitrary continuous-time system with ports `Port.System n p`
  (`theorem/Port/Defs.lean`) and storage `V`; no model.

Source: the port semantics of `theorem/Port/Defs.lean` (passivity as dissipativity with respect
to the supplied power) and the flow semantics of `theorem/Flow/Defs.lean`.

Results.
* Proving passivity: `System.passiveWith_of_rate`, `System.passive_of_noPorts`,
  `System.autonomous_passive`.
* Refuting passivity: `System.not_passive_of_cycle`, `System.not_passive_of_equilibrium` (an
  equilibrium held by a constant input that draws energy out of the ports).
* Consequences of a storage: `System.PassiveWith.zeroInput_le`,
  `System.PassiveWith.lyapunovStable`.
* Simplification: `System.supply_zero`, `System.autonomous_zeroInput`, and the interpretation of
  the sentences on every kind of system, `Sentence.holds_flow`, `Sentence.holds_passive`,
  `Sentence.holds_flow_discrete`, `Sentence.holds_passive_discrete`, `Sentence.holds_envelope`,
  `Sentence.holds_envelope_discrete` (a system read without an envelope satisfies every envelope
  sentence), `Sentence.holds_flow_disturbed`, `Sentence.holds_passive_disturbed`,
  `Sentence.holds_safe_disturbed`, `Sentence.holds_meanSquare_disturbed`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace powerlib

namespace Port

open Set MeasureTheory Filter Topology

variable {n p : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- A storage whose rate along every solution is bounded by the supply proves passivity. -/
@[powerlib_foundation] theorem System.passiveWith_of_rate (s : System n p) (V : ℝⁿ → ℝ)
    (hV : ∀ x, 0 ≤ V x) (rate : ℝⁿ → (Fin p → ℝ) → ℝ)
    (hderiv : ∀ (u : ℝ → Fin p → ℝ) (x : ℝ → ℝⁿ) (t₀ t₁ t : ℝ), s.IsTrajectoryOn u x t₀ t₁ →
      t ∈ Icc t₀ t₁ → HasDerivWithinAt (fun τ => V (x τ)) (rate (x t) (u t)) (Icc t₀ t₁) t)
    (hrate : ∀ x u, rate x u ≤ s.supply x u) : s.PassiveWith V := by
  refine ⟨hV, fun u x t₀ t₁ hle hx hint => ?_⟩
  apply intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hle
    (fun τ hτ => (hderiv u x t₀ t₁ τ hx hτ).continuousWithinAt)
    (fun τ hτ => ((hderiv u x t₀ t₁ τ hx (Ioo_subset_Icc_self hτ)).hasDerivAt
      (Icc_mem_nhds hτ.1 hτ.2)).hasDerivWithinAt)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hle).mp hint)
  intro τ _
  exact hrate (x τ) (u τ)

@[simp, powerlib_foundation] theorem System.supply_zero (s : System n p) (x : ℝⁿ) :
    s.supply x 0 = 0 := by
  simp [System.supply]

/-- With the ports at zero, the storage does not increase along solutions. -/
@[powerlib_foundation] theorem System.PassiveWith.zeroInput_le {s : System n p} {V : ℝⁿ → ℝ}
    (hV : s.PassiveWith V) {x : ℝ → ℝⁿ} {t₀ t₁ : ℝ}
    (hx : _root_.IsTrajectoryOn x s.zeroInput t₀ t₁) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    V (x t) ≤ V (x t₀) := by
  have hseg : s.IsTrajectoryOn (fun _ => 0) x t₀ t :=
    hx.mono (Icc_subset_Icc_right ht.2)
  have h := hV.2 (fun _ => 0) x t₀ t ht.1 hseg (by simp)
  simp only [System.supply_zero, intervalIntegral.integral_zero] at h
  linarith

/-- A storage between two positive quadratic bounds proves Lyapunov stability of the zero-input
field. -/
@[powerlib_foundation] theorem System.PassiveWith.lyapunovStable {s : System n p} {V : ℝⁿ → ℝ}
    (hV : s.PassiveWith V) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x, a * ‖x‖ ^ 2 ≤ V x ∧ V x ≤ b * ‖x‖ ^ 2) :
    LyapunovStable s.zeroInput 0 := by
  have hb : 0 < b := ha.trans_le hab
  intro ε hε
  refine ⟨ε * Real.sqrt (a / b), by positivity, fun t₀ t₁ φ hφ h0 t ht => ?_⟩
  simp only [sub_zero] at h0 ⊢
  have hle := hV.zeroInput_le hφ ht
  have hlow := (hbounds (φ t)).1
  have hup := (hbounds (φ t₀)).2
  have hsq : ‖φ t₀‖ ^ 2 < ε ^ 2 * (a / b) := by
    have h0' : ‖φ t₀‖ ^ 2 < (ε * Real.sqrt (a / b)) ^ 2 :=
      pow_lt_pow_left₀ h0 (norm_nonneg _) two_ne_zero
    rwa [mul_pow, Real.sq_sqrt (div_nonneg ha.le hb.le)] at h0'
  have hfin : a * ‖φ t‖ ^ 2 < a * ε ^ 2 := by
    calc a * ‖φ t‖ ^ 2 ≤ b * ‖φ t₀‖ ^ 2 := by linarith
      _ < b * (ε ^ 2 * (a / b)) := by gcongr
      _ = a * ε ^ 2 := by field_simp
  have hsq' : ‖φ t‖ ^ 2 < ε ^ 2 := lt_of_mul_lt_mul_left hfin ha.le
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq'

/-- A solution segment that returns to its initial state while the ports deliver net energy
refutes passivity: no storage can absorb a negative supply over a closed cycle. -/
@[powerlib_foundation] theorem System.not_passive_of_cycle (s : System n p)
    {u : ℝ → Fin p → ℝ} {x : ℝ → ℝⁿ} {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁)
    (hx : s.IsTrajectoryOn u x t₀ t₁) (hcycle : x t₁ = x t₀)
    (hint : IntervalIntegrable (fun t => s.supply (x t) (u t)) volume t₀ t₁)
    (hneg : ∫ t in t₀..t₁, s.supply (x t) (u t) < 0) : ¬ s.Passive := by
  rintro ⟨V, -, hV⟩
  have h := hV u x t₀ t₁ hle hx hint
  rw [hcycle, sub_self] at h
  linarith

/-- An equilibrium held by a constant input that draws energy out of the ports refutes
passivity. -/
@[powerlib_foundation] theorem System.not_passive_of_equilibrium (s : System n p)
    {x₀ : ℝⁿ} {u₀ : Fin p → ℝ} (hfield : s.field x₀ u₀ = 0) (hsupply : s.supply x₀ u₀ < 0) :
    ¬ s.Passive := by
  refine s.not_passive_of_cycle (u := fun _ => u₀) (x := fun _ => x₀) zero_le_one
    (fun t _ => ?_) rfl intervalIntegrable_const ?_
  · simpa [hfield] using (hasDerivAt_const t x₀).hasDerivWithinAt
  · simpa using hsupply

@[simp, powerlib_foundation] theorem System.autonomous_zeroInput (f : ℝⁿ → ℝⁿ) :
    (System.autonomous f).zeroInput = f := rfl

/-- A system without ports is passive: the zero storage never increases, and nothing is
supplied. -/
@[powerlib_foundation] theorem System.passive_of_noPorts (s : System n 0) : s.Passive :=
  ⟨fun _ => 0, fun _ => le_rfl, fun u x t₀ t₁ _ _ _ => by simp [System.supply]⟩

@[powerlib_foundation] theorem System.autonomous_passive (f : ℝⁿ → ℝⁿ) :
    (System.autonomous f).Passive :=
  (System.autonomous f).passive_of_noPorts

end Port

/-- A sentence about the flow holds on a system exactly when it holds for its zero-input field. -/
@[simp, powerlib_foundation] theorem Sentence.holds_flow {n p : ℕ} (P : Flow.Property)
    (s : Port.System n p) : (Sentence.flow P).holds (s : Behaviour n p) ↔ P.holds s.zeroInput 0 :=
  Iff.rfl

@[simp, powerlib_foundation] theorem Sentence.holds_passive {n p : ℕ} (s : Port.System n p) :
    Sentence.passive.holds (s : Behaviour n p) ↔ s.Passive := Iff.rfl

@[simp, powerlib_foundation] theorem Sentence.holds_flow_discrete {n p : ℕ} (P : Flow.Property)
    (s : Map.System n p) :
    (Sentence.flow P).holds (Behaviour.discrete s) ↔ P.holdsMap s.period s.zeroInput 0 :=
  Iff.rfl

@[simp, powerlib_foundation] theorem Sentence.holds_passive_discrete {n p : ℕ}
    (s : Map.System n p) : Sentence.passive.holds (Behaviour.discrete s) ↔ s.Passive := Iff.rfl

/-- A system read without an envelope has no initial states: its envelope sentences hold. -/
@[simp, powerlib_foundation] theorem Sentence.holds_envelope {n p : ℕ} (E : Envelope.Property)
    (s : Port.System n p) : (Sentence.envelope E).holds (s : Behaviour n p) := trivial

@[simp, powerlib_foundation] theorem Sentence.holds_envelope_discrete {n p : ℕ}
    (E : Envelope.Property) (s : Map.System n p) :
    (Sentence.envelope E).holds (Behaviour.discrete s) := trivial

@[simp, powerlib_foundation] theorem Sentence.holds_flow_disturbed {n p : ℕ} (P : Flow.Property)
    (s : Envelope.Sample → Port.System n p) (S A : Set (EuclideanSpace ℝ (Fin n)))
    (ν : Measure Envelope.Sample) :
    (Sentence.flow P).holds (Behaviour.disturbed s S A ν) ↔ ∀ ω, P.holds (s ω).zeroInput 0 :=
  Iff.rfl

@[simp, powerlib_foundation] theorem Sentence.holds_passive_disturbed {n p : ℕ}
    (s : Envelope.Sample → Port.System n p) (S A : Set (EuclideanSpace ℝ (Fin n)))
    (ν : Measure Envelope.Sample) :
    Sentence.passive.holds (Behaviour.disturbed s S A ν) ↔ ∀ ω, (s ω).Passive := Iff.rfl

@[simp, powerlib_foundation] theorem Sentence.holds_safe_disturbed {n p : ℕ} (T ε : ℝ≥0∞)
    (s : Envelope.Sample → Port.System n p) (S A : Set (EuclideanSpace ℝ (Fin n)))
    (ν : Measure Envelope.Sample) :
    (Sentence.envelope (.safe T ε)).holds (Behaviour.disturbed s S A ν) ↔
      ν {ω | (s ω).Exceeds S A T} ≤ ε := Iff.rfl

/-- A solution leaves the safe set exactly when the reached states are not all in it. -/
@[powerlib_foundation] theorem Port.System.exceeds_iff_not_reach_subset {n p : ℕ}
    (s : Port.System n p) (S A : Set (EuclideanSpace ℝ (Fin n))) (T : ℝ≥0∞) :
    s.Exceeds S A T ↔ ¬ s.reach S T ⊆ A := by
  constructor
  · rintro ⟨x, t, ht, hT, hS, hx, hA⟩ hsub
    exact hA (hsub ⟨x, t, ht, hT, hS, hx, rfl⟩)
  · intro h
    obtain ⟨y, ⟨x, t, ht, hT, hS, hx, rfl⟩, hA⟩ := Set.not_subset.mp h
    exact ⟨x, t, ht, hT, hS, hx, hA⟩

/-- The safety sentence bounds the exceedance probability, on every kind of system. -/
@[powerlib_foundation] theorem Sentence.holds_safe_iff_exceedance {n p : ℕ} (T ε : ℝ≥0∞)
    (b : Behaviour n p) :
    (Sentence.envelope (.safe T ε)).holds b ↔ b.exceedance T ≤ ε := by
  cases b with
  | continuous s => exact ⟨fun _ => zero_le, fun _ => trivial⟩
  | discrete s => exact ⟨fun _ => zero_le, fun _ => trivial⟩
  | disturbed s S A ν => exact Iff.rfl

@[simp, powerlib_foundation] theorem Sentence.holds_meanSquare_disturbed {n p : ℕ} (T c : ℝ≥0∞)
    (s : Envelope.Sample → Port.System n p) (S A : Set (EuclideanSpace ℝ (Fin n)))
    (ν : Measure Envelope.Sample) :
    (Sentence.envelope (.meanSquare T c)).holds (Behaviour.disturbed s S A ν) ↔
      ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < T → ∫⁻ ω, (s ω).squareAt S t ∂ν ≤ c := Iff.rfl

end powerlib
