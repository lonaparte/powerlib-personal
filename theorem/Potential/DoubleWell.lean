import theorem.Attributes
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-! # The quartic double well

The symmetric quartic `V(θ) = −aθ²/2 + bθ⁴/4`, defined once: its derivative, critical points,
square-completion identity, global minimum and barrier. The quartic potentials of the library
are this one object (see "Instances" below).

Scope.
* Generic real algebra and one-variable calculus of `V` for real parameters `a, b` (signs as
  stated per result); no dynamics, noise model or engineering system (no model family).

Source: work-sync theory/T-potential-wells.md §1.2–1.3; theory/T-nonlinear-phase-plane.md §1.4;
theory/T-endpoint-laplace-asymptotics.md §1.2.

Results.
* `doubleWell a b θ = −aθ²/2 + bθ⁴/4`; `hasDerivAt_doubleWell`: `V' = −aθ + bθ³`.
* `doubleWell_critical_iff` (`0 ≤ a`, `0 < b`): critical points `0, ±√(a/b)`.
* `doubleWell_identity` (`a, b ≠ 0`): `V = (a²/4b)[1 − bθ²/a]² − a²/4b` (positive sign in front
  of the square; correction to T-potential-wells §1.2).
* `doubleWell_min` (`b > 0`, any `a`): `−a²/4b ≤ V`; `doubleWell_eq_min_iff` (`a, b > 0`): the
  global minimum value `−a²/4b` is attained exactly at `±√(a/b)`.
* `doubleWell_barrier` (`0 ≤ a`, `0 < b`): `V(0) − V(±√(a/b)) = a²/4b`.
* `doubleWell_sub`: `V(x) − V(y) = (x² − y²)(−a/2 + b(x² + y²)/4)`.

Instances: the Boltzmann weights, curvatures and monotonicity of `V` are in
`theorem/Potential/Wells.lean`; the supercritical pitchfork potential is `doubleWell μ 1`
(`NormalForm.Pitchfork.potential`), the Duffing potential `doubleWell 1 1`
(`PhasePlane.Duffing.potential`, also the large-deviation example `Stochastic.LDP.dwU`), and the
subcritical-Hopf guard potential its negative `−doubleWell α l₁`
(`Asymptotics.Guard.guardPotential`).

Family and connection conclusions.
* None: generic algebra of one scalar function.
-/

noncomputable section
namespace powerlib.Potential

/-- Symmetric double well `−aθ²/2 + bθ⁴/4`. -/
def doubleWell (a b θ : ℝ) : ℝ := -a * θ ^ 2 / 2 + b * θ ^ 4 / 4

@[tmio T, powerlib_foundation] theorem hasDerivAt_doubleWell (a b θ : ℝ) :
    HasDerivAt (doubleWell a b) (-a * θ + b * θ ^ 3) θ := by
  have h := (((hasDerivAt_pow 2 θ).const_mul (-a)).div_const 2).add
    (((hasDerivAt_pow 4 θ).const_mul b).div_const 4)
  exact h.congr_deriv (by push_cast; ring)

/-- Correction: `V = (a²/4b)[1 − bθ²/a]² − a²/4b` (positive sign in front of the square). -/
@[tmio T, powerlib_foundation] theorem doubleWell_identity {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (θ : ℝ) :
    doubleWell a b θ = a ^ 2 / (4 * b) * (1 - b * θ ^ 2 / a) ^ 2 - a ^ 2 / (4 * b) := by
  simp only [doubleWell]; field_simp; ring

@[tmio T, powerlib_foundation] theorem doubleWell_critical_iff {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 < b) (θ : ℝ) :
    -a * θ + b * θ ^ 3 = 0 ↔ θ = 0 ∨ θ = √(a / b) ∨ θ = -√(a / b) := by
  have hr : √(a / b) ^ 2 = a / b := Real.sq_sqrt (by positivity)
  constructor
  · intro h
    have h' : θ * (θ ^ 2 - a / b) = 0 := by field_simp; linarith
    rcases mul_eq_zero.mp h' with h | h
    · exact Or.inl h
    · right
      have : θ ^ 2 = √(a / b) ^ 2 := by rw [hr]; linarith
      exact sq_eq_sq_iff_eq_or_eq_neg.mp this
  · rintro (rfl | rfl | rfl)
    · ring
    · have : √(a / b) ^ 3 = a / b * √(a / b) := by rw [pow_succ, hr]
      rw [this]; field_simp; ring
    · have : (-√(a / b)) ^ 3 = -(a / b * √(a / b)) := by
        rw [show (-√(a / b)) ^ 3 = -(√(a / b) ^ 2 * √(a / b)) by ring, hr]
      rw [this]; field_simp; ring

/-- Global minimum value of the double well: `−a²/4b ≤ V(θ)`. -/
@[tmio T, powerlib_foundation] theorem doubleWell_min {a b : ℝ} (hb : 0 < b) (θ : ℝ) :
    -a ^ 2 / (4 * b) ≤ doubleWell a b θ := by
  have h : doubleWell a b θ + a ^ 2 / (4 * b) = (b * θ ^ 2 - a) ^ 2 / (4 * b) := by
    simp only [doubleWell]; field_simp; ring
  have : 0 ≤ (b * θ ^ 2 - a) ^ 2 / (4 * b) := by positivity
  rw [neg_div]
  linarith

/-- The global minimum value `−a²/4b` of the double well is attained exactly at `±√(a/b)`. -/
@[tmio T, powerlib_foundation] theorem doubleWell_eq_min_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (θ : ℝ) : doubleWell a b θ = -a ^ 2 / (4 * b) ↔ θ = √(a / b) ∨ θ = -√(a / b) := by
  have hr : √(a / b) ^ 2 = a / b := Real.sq_sqrt (by positivity)
  have hid := doubleWell_identity ha.ne' hb.ne' θ
  have hc : 0 < a ^ 2 / (4 * b) := by positivity
  rw [hid]
  constructor
  · intro h
    have hsq : (1 - b * θ ^ 2 / a) ^ 2 = 0 := by
      have : a ^ 2 / (4 * b) * (1 - b * θ ^ 2 / a) ^ 2 = 0 := by
        have hn : -a ^ 2 / (4 * b) = -(a ^ 2 / (4 * b)) := neg_div _ _
        linarith
      exact (mul_eq_zero.mp this).resolve_left hc.ne'
    have h1 : 1 - b * θ ^ 2 / a = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    have hθ : θ ^ 2 = √(a / b) ^ 2 := by rw [hr]; field_simp at h1 ⊢; linarith
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hθ
  · rintro (rfl | rfl) <;>
      simp only [neg_sq, hr] <;> field_simp <;> ring

/-- Barrier of the double well: `V(0) − V(±√(a/b)) = a²/4b` (also at `a = 0`). -/
@[tmio T, powerlib_foundation] theorem doubleWell_barrier {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    doubleWell a b 0 - doubleWell a b √(a / b) = a ^ 2 / (4 * b) ∧
      doubleWell a b 0 - doubleWell a b (-√(a / b)) = a ^ 2 / (4 * b) := by
  have h2 : √(a / b) ^ 2 = a / b := Real.sq_sqrt (by positivity)
  have h4 : √(a / b) ^ 4 = (a / b) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2]
  have h2' : (-√(a / b)) ^ 2 = a / b := by rw [neg_sq, h2]
  have h4' : (-√(a / b)) ^ 4 = (a / b) ^ 2 := by
    rw [show (-√(a / b)) ^ 4 = √(a / b) ^ 4 by ring, h4]
  unfold doubleWell
  rw [h2, h4, h2', h4']
  constructor <;> field_simp <;> ring

@[tmio T, powerlib_foundation] theorem doubleWell_sub (a b x y : ℝ) :
    doubleWell a b x - doubleWell a b y =
      (x ^ 2 - y ^ 2) * (-a / 2 + b * (x ^ 2 + y ^ 2) / 4) := by
  simp only [doubleWell]; ring

end powerlib.Potential
