import theorem.Attributes
import dependencies.Mathlib
import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Circular current-reference limiter (CSA radial projection), foundation

`radialLimit I x = x` if `‖x‖ ≤ I`, otherwise `(I/‖x‖) x` — the current saturation algorithm
`i* ← I i*/|i*|` of work-sync T-current-limiting §1.1 / T-gfm-control §1.10, on any real inner
product space (in particular dq or αβ current vectors `EuclideanSpace ℝ (Fin 2)`).

* `norm_radialLimit_le`, `norm_radialLimit_of_lt`: the output never exceeds `I` and saturates
  exactly at `I` when the input exceeds it.
* `radialLimit_of_norm_le`: no action inside the limit.
* `radialLimit_direction`: the direction is preserved (`radialLimit I x = c • x` with `c > 0`).
* `radialLimit_inner_le`, `radialLimit_nearest`: it is the metric projection onto the closed
  ball of radius `I` (variational inequality, nearest point).
* `radialLimit_lipschitz`: it is 1-Lipschitz (nonexpansive).
* `radialLimit_isometry`: it commutes with every linear isometry, in particular with the Park
  rotation; hence circular limiting in the αβ frame and in any dq frame give the same physical
  current (T-current-limiting §1.1 "αβ 圆形限幅"). Component-wise clipping does not have this
  property (`clamp_not_rotation_invariant` in `DAxisPriority.lean`).

These are properties of a static map (foundation); the dynamics of a limited converter are
not modelled here.

Source: work-sync `theory/T-current-limiting.md` §1.1, `theory/T-gfm-control.md` §1.10.
-/

noncomputable section
namespace powerlib.Limiting
open RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Circular (radial) current limiter with limit `I`. -/
def radialLimit (I : ℝ) (x : E) : E := if ‖x‖ ≤ I then x else (I / ‖x‖) • x

@[powerlib_foundation] theorem radialLimit_of_norm_le {I : ℝ} {x : E} (h : ‖x‖ ≤ I) :
    radialLimit I x = x := by
  simp [radialLimit, h]

@[powerlib_foundation] theorem radialLimit_of_lt {I : ℝ} {x : E} (h : I < ‖x‖) :
    radialLimit I x = (I / ‖x‖) • x := by
  simp [radialLimit, not_le.mpr h]

@[powerlib_foundation] theorem norm_radialLimit_of_lt {I : ℝ} (hI : 0 ≤ I) {x : E}
    (h : I < ‖x‖) : ‖radialLimit I x‖ = I := by
  have hx : 0 < ‖x‖ := hI.trans_lt h
  rw [radialLimit_of_lt h, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hI hx.le),
    div_mul_cancel₀ _ hx.ne']

/-- The limited current never exceeds the limit. -/
@[powerlib_foundation] theorem norm_radialLimit_le {I : ℝ} (hI : 0 ≤ I) (x : E) :
    ‖radialLimit I x‖ ≤ I := by
  by_cases h : ‖x‖ ≤ I
  · rwa [radialLimit_of_norm_le h]
  · exact (norm_radialLimit_of_lt hI (not_le.mp h)).le

/-- The limiter preserves the direction of the reference. -/
@[powerlib_foundation] theorem radialLimit_direction {I : ℝ} (hI : 0 < I) (x : E) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ radialLimit I x = c • x := by
  by_cases h : ‖x‖ ≤ I
  · exact ⟨1, one_pos, le_rfl, by rw [radialLimit_of_norm_le h, one_smul]⟩
  · have h' := not_le.mp h
    have hx : 0 < ‖x‖ := hI.trans h'
    exact ⟨I / ‖x‖, div_pos hI hx, (div_le_one hx).mpr h'.le, radialLimit_of_lt h'⟩

/-- Variational inequality of the projection onto the ball of radius `I`. -/
@[powerlib_foundation] theorem radialLimit_inner_le {I : ℝ} (hI : 0 ≤ I) (x : E) {z : E}
    (hz : ‖z‖ ≤ I) : ⟪x - radialLimit I x, z - radialLimit I x⟫ ≤ 0 := by
  by_cases h : ‖x‖ ≤ I
  · simp [radialLimit_of_norm_le h]
  · have h' := not_le.mp h
    have hx : 0 < ‖x‖ := hI.trans_lt h'
    rw [radialLimit_of_lt h']
    have hdecomp : x - (I / ‖x‖) • x = (1 - I / ‖x‖) • x := by
      rw [sub_smul, one_smul]
    rw [hdecomp, real_inner_smul_left, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    have hc : 0 ≤ 1 - I / ‖x‖ := sub_nonneg.mpr ((div_le_one hx).mpr h'.le)
    have hxz : ⟪x, z⟫ ≤ ‖x‖ * I :=
      (real_inner_le_norm x z).trans (mul_le_mul_of_nonneg_left hz hx.le)
    have : ⟪x, z⟫ - I / ‖x‖ * ‖x‖ ^ 2 ≤ 0 := by
      have he : I / ‖x‖ * ‖x‖ ^ 2 = ‖x‖ * I := by field_simp
      rw [he]
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos hc this

/-- The limiter output is the nearest point of the ball of radius `I`. -/
@[powerlib_foundation] theorem radialLimit_nearest {I : ℝ} (hI : 0 ≤ I) (x : E) {z : E}
    (hz : ‖z‖ ≤ I) : ‖x - radialLimit I x‖ ≤ ‖x - z‖ := by
  have hv := radialLimit_inner_le hI x hz
  set p := radialLimit I x
  have hsq : ‖x - z‖ ^ 2 = ‖x - p‖ ^ 2 - 2 * ⟪x - p, z - p⟫ + ‖z - p‖ ^ 2 := by
    have : x - z = (x - p) - (z - p) := by abel
    rw [this, norm_sub_sq_real]
  have : ‖x - p‖ ^ 2 ≤ ‖x - z‖ ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg ‖z - p‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this

/-- The circular limiter is nonexpansive. -/
@[powerlib_foundation] theorem radialLimit_dist_le {I : ℝ} (hI : 0 ≤ I) (x y : E) :
    ‖radialLimit I x - radialLimit I y‖ ≤ ‖x - y‖ := by
  set a := radialLimit I x
  set b := radialLimit I y
  have h1 := radialLimit_inner_le hI x (norm_radialLimit_le hI y)
  have h2 := radialLimit_inner_le hI y (norm_radialLimit_le hI x)
  have key : ‖a - b‖ ^ 2 ≤ ⟪x - y, a - b⟫ := by
    have e1 : ⟪x - a, b - a⟫ + ⟪y - b, a - b⟫ = ‖a - b‖ ^ 2 - ⟪x - y, a - b⟫ := by
      have hba : b - a = -(a - b) := by abel
      rw [hba, inner_neg_right, ← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right]
      ring
    linarith
  have hle : ‖a - b‖ ^ 2 ≤ ‖x - y‖ * ‖a - b‖ := key.trans (real_inner_le_norm _ _)
  by_cases hab : ‖a - b‖ = 0
  · rw [hab]
    exact norm_nonneg _
  · have hpos : 0 < ‖a - b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hab)
    nlinarith

@[powerlib_foundation] theorem radialLimit_lipschitz {I : ℝ} (hI : 0 ≤ I) :
    LipschitzWith 1 (radialLimit (E := E) I) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa [dist_eq_norm] using radialLimit_dist_le hI x y

/-- The circular limiter commutes with every linear isometry (e.g. Park rotation): limiting
in the αβ frame equals limiting in a dq frame. -/
@[powerlib_foundation] theorem radialLimit_isometry (I : ℝ) (R : E ≃ₗᵢ[ℝ] E) (x : E) :
    radialLimit I (R x) = R (radialLimit I x) := by
  by_cases h : ‖x‖ ≤ I
  · rw [radialLimit_of_norm_le h, radialLimit_of_norm_le (by rwa [R.norm_map])]
  · have h' := not_le.mp h
    rw [radialLimit_of_lt h', radialLimit_of_lt (by rwa [R.norm_map]), R.norm_map,
      LinearIsometryEquiv.map_smul]

end powerlib.Limiting
