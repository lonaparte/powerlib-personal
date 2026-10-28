import theorem.ParametricResonance.ForcedResponse
import theorem.Periodic.Shift
import theorem.Periodic.Floquet

/-! # Half-period symmetry of the single-tone pump

An exact identity (no expansion): reversing the sign of a single-tone pump is a half-period time
shift, so forced orbits, Floquet multipliers and the flip threshold are invariant under `δ ↦ −δ`.

Scope.
* Any plant `ż = f(z, u(t))` on `ℝⁿ = EuclideanSpace ℝ (Fin n)` driven by the single-tone pump
  `u_δ(t) = δ cos(ω_p t)` (`pump`), `T = 2π/ω_p`, continuous time; no assumption on `f`.

Source: work-sync projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/
gfl-gfm-parametric-contrast.md §11 (半周期对称性).

Results.
* `pump_add_half` — `u_δ(t + T/2) = u_{−δ}(t)`, so `δ ↦ −δ` is a time shift by `T/2`.
* `drivenTrajectory_half_shift` — every solution for `δ` shifted by `T/2` is a solution for `−δ`
  (forced orbits correspond).
* `floquetUnstable_half_shift` — if the variational matrix for `−δ` is the `T/2`-shift of the one
  for `δ` (as it is along corresponding forced orbits), the Floquet multipliers coincide
  (`Periodic.spectrum_monodromy_shift`); in particular "some multiplier outside the unit circle"
  holds for `δ` iff it holds for `−δ`: monodromy spectrum and flip threshold are invariant.

The Hill-level gauge `φ_m ↦ (−1)^m φ_m` of the source is proved in `theorem/Periodic/Hill.lean`:
`hillGauge_conj` (the gauge flips the odd bands), `hill3_neg_similar` (third-order Hill matrices at
`±δ̂₁` are gauge-similar) and `exactHill_half_shift` (a half-period shift of `J(t)` gives
gauge-similar exact Hill matrices).
-/

noncomputable section
namespace powerlib.ParametricResonance

open Matrix Function
open scoped Matrix.Norms.Operator

/-- Single-tone pump `u_δ(t) = δ cos(ω_p t)`. -/
def pump (δ ωp t : ℝ) : ℝ := δ * Real.cos (ωp * t)

@[tmio T, powerlib_foundation] theorem pump_add_half {δ ωp T : ℝ} (hT : ωp * T = 2 * Real.pi) (t : ℝ) :
    pump δ ωp (t + T / 2) = pump (-δ) ωp t := by
  simp only [pump]
  rw [show ωp * (t + T / 2) = ωp * t + Real.pi by linarith [hT], Real.cos_add_pi]
  ring

/-- Every global solution of `ż = f(z, u_δ(t))`, shifted by `T/2`, is a global solution of
`ż = f(z, u_{−δ}(t))`. -/
@[powerlib_foundation] theorem drivenTrajectory_half_shift {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n)} {δ ωp T : ℝ}
    (hT : ωp * T = 2 * Real.pi) {z : ℝ → EuclideanSpace ℝ (Fin n)}
    (hz : ∀ t, HasDerivAt z (f (z t) (pump δ ωp t)) t) :
    ∀ t, HasDerivAt (fun t => z (t + T / 2)) (f (z (t + T / 2)) (pump (-δ) ωp t)) t := by
  intro t
  have h := (hz (t + T / 2)).comp_add_const t (T / 2)
  rw [pump_add_half hT] at h
  exact h

/-- If `J_{−δ}(t) = J_δ(t + T/2)`, the Floquet multipliers (and hence Floquet instability) of the
two variational systems coincide. -/
@[powerlib_foundation] theorem floquetUnstable_half_shift {X : Type*} [Fintype X] [DecidableEq X]
    {Jp Jm : ℝ → Matrix X X ℝ} {M T : ℝ} (hA : Continuous Jp) (hM : ∀ t, ‖Jp t‖ ≤ M)
    (hT : 0 ≤ T) (hP : Periodic Jp T) (hshift : ∀ t, Jm t = Jp (t + T / 2)) :
    spectrum ℂ ((Periodic.monodromy Jm T 0).map (algebraMap ℝ ℂ)) =
        spectrum ℂ ((Periodic.monodromy Jp T 0).map (algebraMap ℝ ℂ)) ∧
      (Periodic.FloquetUnstable Jm T ↔ Periodic.FloquetUnstable Jp T) := by
  have hJ : Jm = fun t => Jp (t + T / 2) := funext hshift
  have hs := Periodic.spectrum_monodromy_shift hA hM hT hP (T / 2)
  rw [← hJ] at hs
  refine ⟨hs, ?_⟩
  simp only [Periodic.FloquetUnstable, hs]

end powerlib.ParametricResonance
