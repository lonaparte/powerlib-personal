import theorem.Family.Basic
import theorem.Linear.Transfer
import theorem.Port.Linear

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
* `Family.IsLinear`; `IsLinear.mem_den_flow` (a flow sentence holds for a member exactly when it
  holds for the zero-input field of its plant), `IsLinear.den_hurwitz`,
  `IsLinear.not_isHurwitz_of_mem_den_conservative`, `IsLinear.mem_den_conservative`,
  `IsLinear.mem_den_passive`, `IsLinear.den_envelope` (a linear family is read without an
  envelope: every envelope sentence denotes the whole family).
* Representations: `IsLinear.comap` (a family read in another representation stays linear),
  `IsLinear.extend` (with an extended requirement language).
-/

noncomputable section

namespace powerlib

open Matrix LinearSystems TMIO Linear

variable {X Y Q R : Type*} {n p : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

namespace Linear

/-- At any constant input with an equilibrium, an attractive sentence holds there exactly when
the plant is Hurwitz: the behaviour about every operating point is the zero-input behaviour. -/
@[powerlib_foundation] theorem holds_input_iff (M : Plant n p) {u : Fin p → ℝ} {e : ℝⁿ}
    (he : IsEquilibrium (M.inputField u) e) {P : Flow.Property} (hP : P.Attractive) :
    P.holds (M.inputField u) e ↔ IsHurwitz M.A := by
  rw [M.inputField_eq he]
  exact holds_iff_isHurwitz e hP

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

end Linear

namespace Family

/-- Every complete system of the family is the port system of its linear plant. -/
def IsLinear (F : Family X Q n p) (plant : X → Plant n p) : Prop :=
  ∀ x, F.system x = (plant x).system

variable {F : Family X Q n p} {plant : X → Plant n p}

/-- A linear family is read without an envelope: it satisfies every envelope sentence. -/
@[powerlib_foundation] theorem IsLinear.den_envelope (hF : F.IsLinear plant)
    (E : Envelope.Property) : F.den (.envelope E) = Set.univ :=
  Family.den_envelope_of_continuous hF E

/-- A flow sentence holds for a member of a linear family exactly when it holds for the zero-input
field of its plant. -/
@[powerlib_foundation] theorem IsLinear.mem_den_flow (hF : F.IsLinear plant) {P : Flow.Property}
    {x : X} : x ∈ F.den (.flow P) ↔ P.holds (affineLinearVectorField (plant x).A 0) 0 := by
  rw [mem_den, hF x, Sentence.holds_flow, Plant.system_zeroInput]

/-- The attractive sentences and sampled contraction denote the Hurwitz members. -/
@[powerlib_foundation] theorem IsLinear.den_hurwitz (hF : F.IsLinear plant) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) : F.den (.flow P) = {x | IsHurwitz (plant x).A} := by
  ext x
  rw [hF.mem_den_flow, Set.mem_ofPred_eq]
  rcases hP with hP | rfl
  · exact holds_iff_isHurwitz 0 hP
  · exact sampledContraction_iff_isHurwitz 0

/-- A member of a nontrivial linear family that conserves an energy is not Hurwitz. -/
@[powerlib_foundation] theorem IsLinear.not_isHurwitz_of_mem_den_conservative
    (hF : F.IsLinear plant) (hn : 0 < n) {x : X} (h : x ∈ F.den (.flow .conservative)) :
    ¬ IsHurwitz (plant x).A :=
  not_isHurwitz_of_conservative hn (hF.mem_den_flow.mp h)

/-- A positive definite quadratic energy conserved by the plant places a member in conservation. -/
@[powerlib_foundation] theorem IsLinear.mem_den_conservative (hF : F.IsLinear plant) {x : X}
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : Pᵀ = P) (hpos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (P *ᵥ v))
    (hl : (plant x).Aᵀ * P + P * (plant x).A = 0) : x ∈ F.den (.flow .conservative) :=
  hF.mem_den_flow.mpr (conservative_of_quadratic hP hpos hl)

/-- A KYP certificate places a member in passivity. -/
@[powerlib_foundation] theorem IsLinear.mem_den_passive (hF : F.IsLinear plant) {x : X}
    (c : KYP (plant x)) : x ∈ F.den .passive := by
  rw [mem_den, hF x]
  exact ⟨_, c.passiveWith⟩

/-- A family read in another representation stays linear. -/
@[powerlib_foundation] theorem IsLinear.comap (hF : F.IsLinear plant) (g : Y → X) :
    (F.comap g).IsLinear (plant ∘ g) := fun y => hF (g y)

/-- A family with an extended requirement language stays linear. -/
@[powerlib_foundation] theorem IsLinear.extend (hF : F.IsLinear plant) (g : Y → X)
    (extra : Y → R → Prop) : (F.extend g extra).IsLinear (plant ∘ g) := fun y => hF (g y)

end Family

end powerlib
