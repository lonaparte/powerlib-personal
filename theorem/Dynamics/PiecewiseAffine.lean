import theorem.Dynamics.ConverseLinearization
import theorem.Dynamics.Shift
import theorem.Linear.Family

/-! # Fields decided near a point by one affine piece (foundation)

A field that agrees near a point with the field of a linear plant under a constant input — a
piecewise-affine control law, such as a saturated one whose saturation is inactive near the point —
has there the local sentences of that affine piece (locality, `theorem/Dynamics/Locality.lean`).
For the affine piece the attractive sentences are decided without linearizing a nonlinear field:
they hold exactly at an equilibrium with a Hurwitz state matrix. The field itself need not be `C¹`
or Lipschitz away from the point.

Scope.
* Generic fields `f : ℝⁿ → ℝⁿ` on `EuclideanSpace ℝ (Fin n)` and linear plants `Linear.Plant n p`
  under a constant input `u`; no model family. The local sentences are Lyapunov stability, local
  asymptotic and local exponential stability and instability; the global sentences are not local
  and are excluded.

Source: locality of the local sentences (`theorem/Dynamics/Locality.lean`), the equilibrium step of
converse linearization (`Dynamics.isEquilibrium_of_lyapunovStable`,
`theorem/Dynamics/ConverseLinearization.lean`) and the linear hub (`Linear.holds_input_iff`,
`theorem/Linear/Family.lean`); used by the PI current loop under the inverter's voltage limit
(`theorem/CurrentControl/VoltageLimit.lean`).

Results.
* `holds_congr_nhds`: the local sentences at a point depend only on the field near the point.
* `holds_inputField_iff`: an attractive sentence of a constant-input plant field holds at `e`
  exactly when `e` is an equilibrium and the state matrix is Hurwitz.
* `holds_iff_of_eventuallyEq_inputField`: a field equal near the origin to a constant-input plant
  field translated to `e` is locally asymptotically (exponentially) stable at the origin exactly
  when `e` is an equilibrium of the plant field and the state matrix is Hurwitz.

Family and connection conclusions.
* None: foundation only; `CurrentControl.LimitedPI` derives the exactness of its local
  asymptotic and local exponential translations within headroom from it.
-/

noncomputable section

namespace powerlib.Dynamics

open Filter LinearSystems
open scoped Topology

variable {n p : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The local sentences at a point depend only on the field near the point. -/
@[tmio T, powerlib_foundation] theorem holds_congr_nhds {f g : ℝⁿ → ℝⁿ} {x : ℝⁿ} (hfg : f =ᶠ[𝓝 x] g)
    {P : Flow.Property}
    (hP : P = .lyapunovStable ∨ P = .locallyAsymptoticallyStable ∨
      P = .locallyExponentiallyStable ∨ P = .unstable) :
    P.holds f x ↔ P.holds g x := by
  rcases hP with rfl | rfl | rfl | rfl
  · exact ⟨lyapunovStable_congr_nhds hfg.symm, lyapunovStable_congr_nhds hfg⟩
  · exact ⟨localAsymptoticStable_congr_nhds hfg.symm, localAsymptoticStable_congr_nhds hfg⟩
  · exact ⟨locallyExponentiallyStable_congr_nhds hfg.symm,
      locallyExponentiallyStable_congr_nhds hfg⟩
  · exact unstable_congr_nhds hfg

/-- An attractive sentence of a constant-input plant field holds at `e` exactly when `e` is an
equilibrium and the state matrix is Hurwitz (an attractive point of a `C¹` field is an
equilibrium; `Linear.holds_input_iff` there). -/
@[powerlib_foundation] theorem holds_inputField_iff (M : Linear.Plant n p) (u : Fin p → ℝ)
    (e : ℝⁿ) {P : Flow.Property} (hP : P.Attractive) :
    P.holds (M.inputField u) e ↔ IsEquilibrium (M.inputField u) e ∧ IsHurwitz M.A := by
  refine ⟨fun h => ?_, fun ⟨he, hA⟩ => (Linear.holds_input_iff M he hP).mpr hA⟩
  have hC : ContDiff ℝ 1 (M.inputField u) := (Linear.op M.A).contDiff.add contDiff_const
  have he := isEquilibrium_of_lyapunovStable hC (Flow.Property.localAsymptoticStable hP h).1
  exact ⟨he, (Linear.holds_input_iff M he hP).mp h⟩

/-- **A field decided by one affine piece.** If near the origin `f` is the field of a linear plant
under a constant input `u`, translated to `e`, then `f` is locally asymptotically (exponentially)
stable at the origin exactly when `e` is an equilibrium of the plant field and the state matrix is
Hurwitz. -/
@[powerlib_foundation] theorem holds_iff_of_eventuallyEq_inputField (M : Linear.Plant n p)
    (u : Fin p → ℝ) {f : ℝⁿ → ℝⁿ} {e : ℝⁿ} (h : f =ᶠ[𝓝 0] fun z => M.inputField u (z + e))
    {P : Flow.Property}
    (hP : P = .locallyAsymptoticallyStable ∨ P = .locallyExponentiallyStable) :
    P.holds f 0 ↔ IsEquilibrium (M.inputField u) e ∧ IsHurwitz M.A := by
  have hP' : P.Attractive := by rcases hP with rfl | rfl <;> trivial
  have hloc : P = .lyapunovStable ∨ P = .locallyAsymptoticallyStable ∨
      P = .locallyExponentiallyStable ∨ P = .unstable := by
    rcases hP with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  rw [holds_congr_nhds h hloc, Flow.Property.holds_shift_iff, holds_inputField_iff M u e hP']

end powerlib.Dynamics
