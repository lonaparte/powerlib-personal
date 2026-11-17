import theorem.Family.Basic
import theorem.Linear.Transfer
import theorem.Port.Linear
import theorem.Dynamics.Shift

/-! # Linear families

A linear family reads each of its complete systems as the port system of a linear plant
(`Family.IsLinear`). The semantics connection of every such family is then evaluated by the hub,
once for all of them: the attractive sentences and sampled contraction denote the Hurwitz members,
a conserved energy excludes the Hurwitz members of a nontrivial family, a positive definite
quadratic energy conserved by the plant places a member in conservation, and a KYP certificate
places it in passivity. The families supply only their plant maps, requirement languages and
translations, and their own model facts.

Scope.
* Generic: an arbitrary family `F : Family X Q n p` with a plant map `plant : X → Plant n p`,
  read through the port systems of its plants (`theorem/Port/Linear.lean`); no model.

Source: the linear stability hub (`theorem/Linear/Stability.lean`), certificates
(`theorem/Linear/Certificate.lean`), pole stability (`theorem/Linear/Transfer.lean`) and KYP
certificates (`theorem/Port/Linear.lean`); the family interface of `theorem/Family/Basic.lean`.

Results.
* Plants: `Linear.holds_input_iff` (at any constant input with an equilibrium, an attractive
  sentence holds there exactly when the plant is Hurwitz), `Linear.isHurwitz_one_iff`.
* `Family.IsLinear`, a family of port systems (`Family.IsPort`): the generic laws
  `Family.IsPort.den_envelope` (read without an envelope), `Family.IsPort.den_passive` (without
  ports every member is passive), `Family.IsPort.comap` and `Family.IsPort.extend` apply.
  `IsLinear.mem_den_flow` (a flow sentence holds for a member exactly when it holds for the
  zero-input field of its plant), `IsLinear.den_hurwitz`,
  `IsLinear.not_isHurwitz_of_mem_den_conservative`, `IsLinear.mem_den_conservative`,
  `IsLinear.mem_den_passive`.
* Constant inputs: `Family.constantInput F plant u e` reads every member under the constant
  input `u` of its plant, translated about the selected point `e x` (the forced field
  `z ↦ A (z + e x) + B u`, no ports), with the family's requirements and translation.
  `Family.mem_den_constantInput_iff`: when `e x` is an equilibrium of the forced field, an
  attractive sentence holds for `x` exactly when its plant is Hurwitz.

Family and connection conclusions.
* `Family.constantInput` is a generic construction over an arbitrary family and plant map, not a
  model family; its only connection law is `Family.mem_den_constantInput_iff` (a generic
  implication, through `Flow.Property.holds_shift_iff` and `Linear.holds_input_iff`).
-/

noncomputable section

namespace powerlib

open Matrix LinearSystems TMIO Linear

variable {X Q : Type*} {n p : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

namespace Linear

/-- At any constant input with an equilibrium, an attractive sentence holds there exactly when
the plant is Hurwitz: the behaviour about every operating point is the zero-input behaviour. -/
@[tmio T, powerlib_foundation] theorem holds_input_iff (M : Plant n p) {u : Fin p → ℝ} {e : ℝⁿ}
    (he : IsEquilibrium (M.inputField u) e) {P : Flow.Property} (hP : P.Attractive) :
    P.holds (M.inputField u) e ↔ IsHurwitz M.A := by
  rw [M.inputField_eq he]
  exact holds_iff_isHurwitz e hP

/-- A one-state plant is Hurwitz exactly when its state coefficient is negative. -/
@[tmio T, powerlib_foundation] theorem isHurwitz_one_iff (a : ℝ) : IsHurwitz !![a] ↔ a < 0 := by
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

end Linear

namespace Family

/-- Every complete system of the family is the port system of its linear plant: a family of port
systems (`Family.IsPort`), whose generic laws (`den_envelope`, `den_passive` without ports,
`comap`, `extend`) apply. -/
abbrev IsLinear (F : Family X Q n p) (plant : X → Plant n p) : Prop :=
  F.IsPort fun x => (plant x).system

variable {F : Family X Q n p} {plant : X → Plant n p}

/-- A flow sentence holds for a member of a linear family exactly when it holds for the zero-input
field of its plant. -/
@[tmio TM, powerlib_foundation] theorem IsLinear.mem_den_flow (hF : F.IsLinear plant)
    {P : Flow.Property} {x : X} :
    connection% (x ∈ F.den (.flow P) ↔ P.holds (affineLinearVectorField (plant x).A 0) 0) := by
  change x ∈ F.den (.flow P) ↔ P.holds (affineLinearVectorField (plant x).A 0) 0
  rw [(connection_proof% IsPort.mem_den_flow hF), Plant.system_zeroInput]

/-- The attractive sentences and sampled contraction denote the Hurwitz members. -/
@[tmio TM, powerlib_foundation] theorem IsLinear.den_hurwitz (hF : F.IsLinear plant) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (F.den (.flow P) = {x | IsHurwitz (plant x).A}) := by
  unfold powerlib.TMIO.Statement
  ext x
  rw [(connection_proof% hF.mem_den_flow), Set.mem_ofPred_eq]
  rcases hP with hP | rfl
  · exact holds_iff_isHurwitz 0 hP
  · exact sampledContraction_iff_isHurwitz 0

/-- Membership in an attractive or contractive denotation is exactly the plant's Hurwitz
condition. This pointwise view lets spectral proofs consume certified denotation results. -/
@[tmio TM, powerlib_foundation] theorem IsLinear.mem_den_hurwitz (hF : F.IsLinear plant)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) {x : X} :
    connection% (x ∈ F.den (.flow P) ↔ IsHurwitz (plant x).A) := by
  unfold TMIO.Statement
  rw [hF.den_hurwitz hP]
  rfl

/-- A conserving member of a nontrivial linear family lies outside the globally exponentially
stable denotation, equivalently its plant is not Hurwitz. -/
@[tmio TM, powerlib_foundation] theorem IsLinear.not_isHurwitz_of_mem_den_conservative
    (hF : F.IsLinear plant) (hn : 0 < n) {x : X} (h : x ∈ F.den (.flow .conservative)) :
    connection% (x ∉ F.den (.flow .globallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [hF.den_hurwitz (P := .globallyExponentiallyStable) (Or.inl trivial)]
  exact not_isHurwitz_of_conservative hn (hF.mem_den_flow.mp h)

/-- A positive definite quadratic energy conserved by the plant places a member in conservation. -/
@[tmio TM, powerlib_foundation] theorem IsLinear.mem_den_conservative (hF : F.IsLinear plant) {x : X}
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : Pᵀ = P) (hpos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (P *ᵥ v))
    (hl : (plant x).Aᵀ * P + P * (plant x).A = 0) :
    connection% (x ∈ F.den (.flow .conservative)) := show x ∈ F.den (.flow .conservative) from
  hF.mem_den_flow.mpr (conservative_of_quadratic hP hpos hl)

/-- A KYP certificate places a member in passivity. -/
@[tmio TM, powerlib_foundation] theorem IsLinear.mem_den_passive (hF : F.IsLinear plant) {x : X}
    (c : KYP (plant x)) :
    connection% (x ∈ F.den .passive) := show x ∈ F.den .passive from
  (connection_proof% IsPort.mem_den_passive_iff hF).mpr ⟨_, c.passiveWith⟩

/-- The members under the constant input `u` of their plants, translated about the selected
points `e x`: the system map reads the forced field `z ↦ A (z + e x) + B u` with the input held
constant; requirements and translation are the family's. -/
def constantInput (F : Family X Q n p) (plant : X → Plant n p) (u : Fin p → ℝ) (e : X → ℝⁿ) :
    Family X Q n 0 :=
  ⟨fun x => Port.System.autonomous fun z => (plant x).inputField u (z + e x), F.meets,
    F.translate⟩

/-- At an equilibrium `e x` of the forced field, an attractive sentence holds for a member of the
constant-input family exactly when its plant is Hurwitz. -/
@[tmio TM, powerlib_foundation] theorem mem_den_constantInput_iff (F : Family X Q n p)
    (plant : X → Plant n p) {u : Fin p → ℝ} {e : X → ℝⁿ} {x : X}
    (he : IsEquilibrium ((plant x).inputField u) (e x)) {P : Flow.Property} (hP : P.Attractive) :
    connection% (x ∈ (F.constantInput plant u e).den (.flow P) ↔ IsHurwitz (plant x).A) := by
  unfold TMIO.Statement
  rw [(connection_proof% IsAutonomous.mem_den_flow
    (show (F.constantInput plant u e).IsAutonomous
      (fun x z => (plant x).inputField u (z + e x)) from fun _ => rfl))]
  exact (Flow.Property.holds_shift_iff P).trans (Linear.holds_input_iff (plant x) he hP)

end Family

end powerlib
