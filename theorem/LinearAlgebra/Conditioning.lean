import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Ring.Units

/-! # Condition number and perturbation bounds for linear systems

The condition number bounds the relative error of a linear system under right-hand-side and
matrix perturbations.

Scope.
* General numerical linear algebra: `A : Matrix n n 𝕜` (`𝕜 = ℝ` or `ℂ`) acting on
  `EuclideanSpace 𝕜 n` through `Matrix.toEuclideanCLM`; matrix norms are the spectral (`ℓ²`
  operator) norms (`Matrix.Norms.L2Operator`, Mathlib `Matrix.l2_opNorm_*`).
  `cond A = ‖A‖ ‖A⁻¹‖` (`= σ_max/σ_min` for invertible `A`).
* Exact arithmetic: these are the mathematical sensitivity bounds, not floating-point error
  analysis.

Source: work-sync theory/T-linear-algebra.md §1.1 (`‖Δx‖/‖x‖ ≤ κ(A)‖Δb‖/‖b‖` and the bound
with a perturbed matrix, valid for `‖ΔA‖/‖A‖ < 1/κ(A)`).

Results.
* `one_le_cond` — `κ(A) ≥ 1` for invertible `A` (nonempty index type).
* `rhs_perturbation` — `A x = b`, `A (x + Δx) = b + Δb`, `b ≠ 0` ⇒
  `‖Δx‖/‖x‖ ≤ κ(A) ‖Δb‖/‖b‖`.
* `isUnit_add_of_norm_lt` — Neumann series, Mathlib `Units.add`: `‖A⁻¹‖ ‖ΔA‖ < 1` ⇒ `A + ΔA` is
  invertible, so the perturbed system has a unique solution.
* `matrix_perturbation` — with also `(A + ΔA)(x + Δx) = b + Δb` and `κ ‖ΔA‖/‖A‖ < 1`,
  `‖Δx‖/‖x‖ ≤ κ/(1 − κ‖ΔA‖/‖A‖) · (‖ΔA‖/‖A‖ + ‖Δb‖/‖b‖)`.
-/

noncomputable section
namespace powerlib.LinearAlgebra
open Matrix
open scoped Matrix.Norms.L2Operator

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- Spectral condition number `κ(A) = ‖A‖ ‖A⁻¹‖`. -/
def cond (A : Matrix n n 𝕜) : ℝ := ‖A‖ * ‖A⁻¹‖

/-- The linear map of `A` on `EuclideanSpace 𝕜 n`. -/
abbrev act (A : Matrix n n 𝕜) : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n :=
  Matrix.toEuclideanCLM (n := n) (𝕜 := 𝕜) A

@[tmio T, powerlib_foundation] theorem norm_act_le (A : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ‖act A x‖ ≤ ‖A‖ * ‖x‖ := by
  have := (act A).le_opNorm x
  rwa [act, Matrix.l2_opNorm_toEuclideanCLM] at this

@[powerlib_foundation] theorem act_inv_act {A : Matrix n n 𝕜} (hA : IsUnit A.det)
    (x : EuclideanSpace 𝕜 n) : act A⁻¹ (act A x) = x := by
  have h : act (A⁻¹ * A) x = x := by
    rw [Matrix.nonsing_inv_mul _ hA, act, map_one]; rfl
  rw [act, map_mul] at h
  exact h

@[powerlib_foundation] theorem one_le_cond [Nonempty n] {A : Matrix n n 𝕜} (hA : IsUnit A.det) :
    1 ≤ cond A := by
  have h1 : ‖(1 : Matrix n n 𝕜)‖ = 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp
  calc (1 : ℝ) = ‖(1 : Matrix n n 𝕜)‖ := h1.symm
    _ = ‖A * A⁻¹‖ := by rw [Matrix.mul_nonsing_inv _ hA]
    _ ≤ ‖A‖ * ‖A⁻¹‖ := Matrix.l2_opNorm_mul A A⁻¹

/-- **Right-hand-side perturbation bound** `‖Δx‖/‖x‖ ≤ κ(A) ‖Δb‖/‖b‖`. -/
@[powerlib_foundation] theorem rhs_perturbation {A : Matrix n n 𝕜} (hA : IsUnit A.det)
    {x dx b db : EuclideanSpace 𝕜 n} (hx : act A x = b) (hdx : act A (x + dx) = b + db)
    (hb : b ≠ 0) : ‖dx‖ / ‖x‖ ≤ cond A * (‖db‖ / ‖b‖) := by
  have hAdx : act A dx = db := by
    rw [map_add, hx] at hdx; exact add_left_cancel hdx
  have hdx' : dx = act A⁻¹ db := by rw [← hAdx, act_inv_act hA]
  have hxne : x ≠ 0 := by rintro rfl; rw [map_zero] at hx; exact hb hx.symm
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have h1 : ‖dx‖ ≤ ‖A⁻¹‖ * ‖db‖ := by rw [hdx']; exact norm_act_le _ _
  have h2 : ‖b‖ ≤ ‖A‖ * ‖x‖ := by rw [← hx]; exact norm_act_le _ _
  rw [cond, div_le_iff₀ hxpos]
  calc ‖dx‖ ≤ ‖A⁻¹‖ * ‖db‖ := h1
    _ = ‖A⁻¹‖ * ‖db‖ / ‖b‖ * ‖b‖ := by field_simp
    _ ≤ ‖A⁻¹‖ * ‖db‖ / ‖b‖ * (‖A‖ * ‖x‖) := by gcongr
    _ = ‖A‖ * ‖A⁻¹‖ * (‖db‖ / ‖b‖) * ‖x‖ := by ring

/-- **Neumann series**: a perturbation with `‖A⁻¹‖ ‖ΔA‖ < 1` keeps `A` invertible. -/
@[powerlib_foundation] theorem isUnit_add_of_norm_lt {A dA : Matrix n n 𝕜} (hA : IsUnit A.det)
    (h : ‖A⁻¹‖ * ‖dA‖ < 1) : IsUnit (A + dA) := by
  have hU : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr hA
  obtain ⟨u, rfl⟩ := hU
  rw [← Matrix.coe_units_inv] at h
  set c := ‖((u⁻¹ : (Matrix n n 𝕜)ˣ) : Matrix n n 𝕜)‖ with hc
  rcases (norm_nonneg ((u⁻¹ : (Matrix n n 𝕜)ˣ) : Matrix n n 𝕜)).lt_or_eq with hpos | h0
  · rw [← hc] at hpos
    have hc0 : c ≠ 0 := hpos.ne'
    have hlt : ‖dA‖ < c⁻¹ := by
      calc ‖dA‖ = c⁻¹ * (c * ‖dA‖) := by field_simp
        _ < c⁻¹ * 1 := by gcongr
        _ = c⁻¹ := mul_one _
    exact ⟨Units.add u dA hlt, rfl⟩
  · have hz : ((u⁻¹ : (Matrix n n 𝕜)ˣ) : Matrix n n 𝕜) = 0 := norm_eq_zero.mp h0.symm
    have h10 : (1 : Matrix n n 𝕜) = 0 := by rw [← Units.inv_mul u, hz, zero_mul]
    have : Subsingleton (Matrix n n 𝕜) := subsingleton_of_zero_eq_one h10.symm
    exact isUnit_of_subsingleton _

/-- **Perturbation bound with a perturbed matrix**:
`‖Δx‖/‖x‖ ≤ κ/(1 − κ‖ΔA‖/‖A‖) · (‖ΔA‖/‖A‖ + ‖Δb‖/‖b‖)` whenever `κ‖ΔA‖/‖A‖ < 1`. -/
@[powerlib_foundation] theorem matrix_perturbation {A dA : Matrix n n 𝕜} (hA : IsUnit A.det)
    {x dx b db : EuclideanSpace 𝕜 n} (hx : act A x = b)
    (hdx : act (A + dA) (x + dx) = b + db) (hb : b ≠ 0)
    (hsmall : cond A * (‖dA‖ / ‖A‖) < 1) :
    ‖dx‖ / ‖x‖ ≤ cond A / (1 - cond A * (‖dA‖ / ‖A‖)) * (‖dA‖ / ‖A‖ + ‖db‖ / ‖b‖) := by
  have hxne : x ≠ 0 := by rintro rfl; rw [map_zero] at hx; exact hb hx.symm
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have h2 : ‖b‖ ≤ ‖A‖ * ‖x‖ := by rw [← hx]; exact norm_act_le _ _
  have hApos : 0 < ‖A‖ := by
    by_contra hle
    have : ‖A‖ = 0 := le_antisymm (not_lt.mp hle) (norm_nonneg _)
    rw [this, zero_mul] at h2; linarith
  -- `A Δx = Δb − ΔA (x + Δx)`
  have hAdx : act A dx = db - act dA x - act dA dx := by
    have e : act (A + dA) = act A + act dA := map_add _ _ _
    have h' : act A (x + dx) + act dA (x + dx) = b + db := by rw [← hdx, e]; rfl
    rw [map_add, map_add, hx] at h'
    rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq]
    calc act A dx + act dA dx + act dA x = b + act A dx + (act dA x + act dA dx) - b := by abel
      _ = b + db - b := by rw [h']
      _ = db := by abel
  have hdx' : dx = act A⁻¹ (db - act dA x - act dA dx) := by rw [← hAdx, act_inv_act hA]
  have hbound : ‖dx‖ ≤ ‖A⁻¹‖ * (‖db‖ + ‖dA‖ * ‖x‖ + ‖dA‖ * ‖dx‖) := by
    calc ‖dx‖ ≤ ‖A⁻¹‖ * ‖db - act dA x - act dA dx‖ := by
          conv_lhs => rw [hdx']
          exact norm_act_le _ _
      _ ≤ ‖A⁻¹‖ * (‖db‖ + ‖dA‖ * ‖x‖ + ‖dA‖ * ‖dx‖) := by
          gcongr
          calc ‖db - act dA x - act dA dx‖ ≤ ‖db - act dA x‖ + ‖act dA dx‖ := norm_sub_le _ _
            _ ≤ ‖db‖ + ‖act dA x‖ + ‖act dA dx‖ := by gcongr; exact norm_sub_le _ _
            _ ≤ ‖db‖ + ‖dA‖ * ‖x‖ + ‖dA‖ * ‖dx‖ := by
                gcongr <;> exact norm_act_le _ _
  set k := cond A with hk
  have hkdef : k * (‖dA‖ / ‖A‖) = ‖A⁻¹‖ * ‖dA‖ := by
    rw [hk, cond]; field_simp
  have hden : 0 < 1 - k * (‖dA‖ / ‖A‖) := by linarith
  -- `(1 − ‖A⁻¹‖‖ΔA‖) ‖Δx‖ ≤ ‖A⁻¹‖ (‖Δb‖ + ‖ΔA‖ ‖x‖)`
  have hmain : (1 - k * (‖dA‖ / ‖A‖)) * ‖dx‖ ≤ ‖A⁻¹‖ * (‖db‖ + ‖dA‖ * ‖x‖) := by
    rw [hkdef]; nlinarith [hbound]
  have hdb : ‖db‖ ≤ ‖A‖ * ‖x‖ * (‖db‖ / ‖b‖) := by
    rw [mul_div_assoc', le_div_iff₀ hbpos]
    nlinarith [norm_nonneg db]
  have key : ‖dx‖ * (1 - k * (‖dA‖ / ‖A‖)) ≤ k * (‖dA‖ / ‖A‖ + ‖db‖ / ‖b‖) * ‖x‖ := by
    calc ‖dx‖ * (1 - k * (‖dA‖ / ‖A‖)) ≤ ‖A⁻¹‖ * (‖db‖ + ‖dA‖ * ‖x‖) := by linarith [hmain]
      _ ≤ ‖A⁻¹‖ * (‖A‖ * ‖x‖ * (‖db‖ / ‖b‖) + ‖dA‖ * ‖x‖) := by gcongr
      _ = k * (‖dA‖ / ‖A‖ + ‖db‖ / ‖b‖) * ‖x‖ := by rw [hk, cond]; field_simp; ring
  rw [div_le_iff₀ hxpos, show k / (1 - k * (‖dA‖ / ‖A‖)) * (‖dA‖ / ‖A‖ + ‖db‖ / ‖b‖) * ‖x‖ =
    k * (‖dA‖ / ‖A‖ + ‖db‖ / ‖b‖) * ‖x‖ / (1 - k * (‖dA‖ / ‖A‖)) by ring, le_div_iff₀ hden]
  exact key

end powerlib.LinearAlgebra
