import theorem.Linear.Transfer
import theorem.TMIO.Relation

/-! # Linear families

A family of complete systems enters the library through one map, its plant map `X → Plant n p`.
The denotation of every behavioural sentence over the family is the Flow semantics of the plant's
zero-input field, pulled back along the plant map (`den`); it is never restated per family.
Consequently a family proves one domain fact — which requirement set carves out the Hurwitz
plants — and inherits exact translations of every attractive sentence, at every constant-input
equilibrium, together with the meaning of every Lyapunov certificate. -/

noncomputable section

namespace powerlib.Linear

open LinearSystems TMIO

variable {n p : ℕ} {X Q : Type*}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The denotation of a sentence over a family: the Flow semantics, pulled back. -/
def den (plant : X → Plant n p) (P : Flow.Property) : Set X :=
  plant ⁻¹' {M | P.holds (affineLinearVectorField M.A 0) 0}

/-- Every attractive sentence denotes the Hurwitz members of the family. -/
@[powerlib_foundation] theorem den_attractive (plant : X → Plant n p) {P : Flow.Property}
    (hP : P.Attractive) : den plant P = {x | IsHurwitz (plant x).A} := by
  ext x
  exact holds_iff_isHurwitz 0 hP

/-- A requirement set that carves out the Hurwitz members is an exact translation of every
attractive sentence. -/
@[powerlib_foundation] theorem realize_eq_den {plant : X → Plant n p} {sat : X → Q → Prop}
    {Γ : Set Q} (h : realize sat Γ = {x | IsHurwitz (plant x).A}) {P : Flow.Property}
    (hP : P.Attractive) : realize sat Γ = den plant P := by
  rw [h, den_attractive plant hP]

/-- The same exactness relative to a context of requirements. -/
@[powerlib_foundation] theorem exactUnder_den {plant : X → Plant n p} {sat : X → Q → Prop}
    {Δ Γ : Set Q} (h : ExactUnder sat Δ Γ {x | IsHurwitz (plant x).A}) {P : Flow.Property}
    (hP : P.Attractive) : ExactUnder sat Δ Γ (den plant P) := by
  rwa [ExactUnder, den_attractive plant hP]

/-- At any constant input with an equilibrium, an attractive sentence holds there exactly when
the plant is Hurwitz: the behaviour about every operating point is the zero-input behaviour. -/
@[powerlib_foundation] theorem holds_input_iff (M : Plant n p) {u : Fin p → ℝ} {e : ℝⁿ}
    (he : IsEquilibrium (M.inputField u) e) {P : Flow.Property} (hP : P.Attractive) :
    P.holds (M.inputField u) e ↔ IsHurwitz M.A := by
  rw [M.inputField_eq he]
  exact holds_iff_isHurwitz e hP

/-- A certificate for a member's state matrix proves the member in every attractive sentence. -/
@[powerlib_foundation] theorem Certificate.mem_den {plant : X → Plant n p} {x : X}
    (c : Certificate (plant x).A) {P : Flow.Property} (hP : P.Attractive) : x ∈ den plant P :=
  c.holds 0 hP

/-- A one-state plant is Hurwitz exactly when its state coefficient is negative. -/
@[powerlib_foundation] theorem isHurwitz_one_iff (a : ℝ) : IsHurwitz !![a] ↔ a < 0 := by
  rw [← spectrallyStable_iff_isHurwitz]
  constructor
  · intro h
    have := h a (by simp [characteristicMatrix, Matrix.det_unique])
    simpa using this
  · intro ha s hs
    simp [characteristicMatrix, Matrix.det_unique] at hs
    have : s = a := by linear_combination hs
    rw [this]
    simpa using ha

end powerlib.Linear
