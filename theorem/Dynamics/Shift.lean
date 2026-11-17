import theorem.Flow.Basic
import theorem.Dynamics.SpaceTime

/-! # Moving an equilibrium to the origin

Each behavioural sentence of the Flow semantics holds for `f` at `e` exactly when it holds for
`z ↦ f (z + e)` at `0` (`Flow.Property.holds_shift_iff`). Model families read about a non-zero
operating point use it to place the operating point at the origin, where the sentences of the
library are interpreted.

Scope.
* Generic foundation, independent of any model: autonomous fields `f : ℝⁿ → ℝⁿ` on
  `ℝⁿ = EuclideanSpace ℝ (Fin n)`, read through the Flow semantics.

Source: work-sync `theory/T-dynamical-systems.md` §1.3 (deviation coordinates `ξ = x − x*` about
an equilibrium).

Results.
* `Flow.Property.holds_shift_iff`: every behavioural sentence is invariant under moving the
  equilibrium to the origin. It keeps the namespace of the semantic-layer type `Flow.Property` it
  extends (dot notation). It is the instance `c = 1`, `T = 1`, `b = −e` of the space-time law
  `Dynamics.holds_spaceTime_iff` (`theorem/Dynamics/SpaceTime.lean`), where every sentence is
  transported once.
* `Dynamics.globallyExponentiallyStable_shift_iff`: its reading for global exponential stability.
-/

noncomputable section

namespace powerlib.Flow

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- Every behavioural sentence of the Flow semantics is invariant under moving the equilibrium to
the origin: the sentence holds for `f` at `e` exactly when it holds for `z ↦ f (z + e)` at `0`. -/
@[tmio T, powerlib_foundation] theorem Property.holds_shift_iff {f : ℝⁿ → ℝⁿ} {e : ℝⁿ}
    (P : Property) :
    P.holds (fun z => f (z + e)) 0 ↔ P.holds f e := by
  have h := Dynamics.holds_spaceTime_iff one_pos (ContinuousLinearEquiv.refl ℝ ℝⁿ) (-e)
    (P := P) (Or.inr rfl) (f := f) (x := e)
  have hf : (1 : ℝ) • Dynamics.transportField (ContinuousLinearEquiv.refl ℝ ℝⁿ) (-e) f =
      fun z => f (z + e) := by
    funext z
    simp [Dynamics.transportField]
  have hx : Dynamics.affineCoord (ContinuousLinearEquiv.refl ℝ ℝⁿ) (-e) e = 0 := by
    simp [Dynamics.affineCoord]
  rwa [Property.timeScale_one, hf, hx] at h

end powerlib.Flow

namespace powerlib.Dynamics

open powerlib.Flow (GloballyExponentiallyStable)

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

@[tmio T, powerlib_foundation] theorem globallyExponentiallyStable_shift_iff {f : ℝⁿ → ℝⁿ}
    {e : ℝⁿ} :
    GloballyExponentiallyStable (fun z => f (z + e)) 0 ↔ GloballyExponentiallyStable f e :=
  Flow.Property.holds_shift_iff .globallyExponentiallyStable

end powerlib.Dynamics
