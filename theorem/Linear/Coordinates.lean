import theorem.Linear.Family

/-! # Coordinate changes and port passivity (foundation)

Coordinate changes preserve every sentence, including port passivity.

Scope.
* Generic: an arbitrary continuous-time system with ports conjugated by continuous linear maps
  `L`, `K` with `K ∘ L = id`; linear plants under invertible state coordinate changes; linear
  families (`Family.IsLinear`). No model.

Source: the port semantics (`theorem/Port/Defs.lean`); coordinate changes and similarity of
plants (`theorem/Linear/Transfer.lean`); the port systems of plants (`theorem/Port/Linear.lean`);
linear families (`theorem/Linear/Family.lean`). Scaffold: `theorem/Similarity.agda`.

Results.
* `Port.System.conjugate` (state dynamics and port output transported through a coordinate
  change), `Port.System.passiveWith_conjugate` (the storage pulls back along the inverse
  coordinates; input and supplied power are preserved), `Port.System.passive_conjugate`.
* Plants: `Plant.system_changeCoordinates`, `Plant.passive_changeCoordinates`,
  `Similar.passive_iff` (with no minimality assumption), `Similar.sentence_iff` (similar plants
  agree on the complete sentence language).
* `Family.IsLinear.den_similar`: all denotations are invariant when system maps are read in
  similar state coordinates.
-/

noncomputable section
namespace powerlib
open LinearSystems
variable {n p : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

namespace Port.System

/-- Transport both the state dynamics and port output through a state coordinate change. -/
def conjugate (s : Port.System n p) (L K : ℝⁿ →L[ℝ] ℝⁿ) : Port.System n p :=
  ⟨fun x u => L (s.field (K x) u), fun x u => s.output (K x) u⟩

/-- Storage pulls back along the inverse coordinates; input and supplied power are preserved. -/
@[tmio T, powerlib_foundation] theorem passiveWith_conjugate (s : Port.System n p)
    (L K : ℝⁿ →L[ℝ] ℝⁿ) (hKL : ∀ x, K (L x) = x) {V : ℝⁿ → ℝ}
    (h : s.PassiveWith V) : (s.conjugate L K).PassiveWith (V ∘ K) := by
  refine ⟨fun x => h.1 _, fun u φ t₀ t₁ ht hφ hi => ?_⟩
  have hψ : s.IsTrajectoryOn u (fun t => K (φ t)) t₀ t₁ := by
    intro t ht
    have hd := K.hasFDerivAt.comp_hasDerivWithinAt t (hφ t ht)
    simpa [Function.comp_def, conjugate, hKL] using hd
  exact h.2 u (fun t => K (φ t)) t₀ t₁ ht hψ hi

@[powerlib_foundation] theorem passive_conjugate (s : Port.System n p)
    (L K : ℝⁿ →L[ℝ] ℝⁿ) (hKL : ∀ x, K (L x) = x)
    (h : s.Passive) : (s.conjugate L K).Passive := by
  obtain ⟨V, hV⟩ := h
  exact ⟨_, s.passiveWith_conjugate L K hKL hV⟩

end Port.System

namespace Linear
open Matrix

@[powerlib_foundation] theorem Plant.system_changeCoordinates (m : Plant n p)
    (T S : Matrix (Fin n) (Fin n) ℝ) :
    (m.changeCoordinates T S).system = m.system.conjugate (op T) (op S) := by
  change Port.System.mk _ _ = Port.System.mk _ _
  congr 1 <;> funext x u <;> ext i <;>
    simp [Plant.system, Plant.changeCoordinates, op,
      Matrix.mulVec_mulVec]

@[powerlib_foundation] theorem Plant.passive_changeCoordinates (m : Plant n p)
    {T S : Matrix (Fin n) (Fin n) ℝ} (hST : S * T = 1) (h : m.system.Passive) :
    (m.changeCoordinates T S).system.Passive := by
  rw [m.system_changeCoordinates]
  exact m.system.passive_conjugate (op T) (op S)
    (fun x => op_cancel hST x) h

/-- State similarity also preserves port passivity, with no minimality assumption. -/
@[powerlib_foundation] theorem Similar.passive_iff {m m' : Plant n p} (h : Similar m m') :
    m'.system.Passive ↔ m.system.Passive := by
  obtain ⟨T, S, hTS, hST, rfl⟩ := h
  constructor
  · intro hp
    have hback := (m.changeCoordinates T S).passive_changeCoordinates hTS hp
    simpa [Plant.changeCoordinates_changeCoordinates, hST, Plant.changeCoordinates_one] using hback
  · exact m.passive_changeCoordinates hST

/-- Similar plants agree on the complete sentence language, including passivity. -/
@[powerlib_foundation] theorem Similar.sentence_iff {m m' : Plant n p} (h : Similar m m')
    (s : Sentence) : s.holds (.continuous m'.system) ↔ s.holds (.continuous m.system) := by
  cases s with
  | flow P =>
    simp only [Sentence.holds_flow, Plant.system_zeroInput]
    exact h.holds_iff P
  | passive => exact h.passive_iff
  | envelope E => exact Iff.rfl

end Linear

namespace Family
open Linear
variable {X Y Q R : Type*} {F : Family X Q n p} {G : Family Y R n p}
    {plant : X → Plant n p} {plant' : Y → Plant n p}

/-- All denotations are invariant when system maps are read in similar state coordinates. -/
@[tmio TM, powerlib_foundation] theorem IsLinear.den_similar (hF : F.IsLinear plant)
    (hG : G.IsLinear plant') (g : X → Y) (hg : ∀ x, Similar (plant x) (plant' (g x)))
    (s : Sentence) : connection% (g ⁻¹' G.den s = F.den s) := by
  unfold powerlib.TMIO.Statement
  ext x
  simp only [Set.mem_preimage, mem_den, hF x, hG (g x)]
  exact (hg x).sentence_iff s

end Family
end powerlib
