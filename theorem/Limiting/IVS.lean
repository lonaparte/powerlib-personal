import theorem.Attributes
import dependencies.Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Adaptive fast/slow internal-voltage-source switching signal

Trigonometric facts (foundation) about the switching signal of the adaptive IVS scheme; the
switching logic itself is not modelled.

Model boundary.
Wu–Wang (2023) current magnitude of a grid-forming converter before current limiting
(work-sync T-dc-voltage-gfm §1.7): internal voltage `E∠δ` behind the total reactance
`X = X_f + X_g` against the grid `V_g∠0`,
`I_omag(δ) = √(E² + V_g² − 2 E V_g cos δ)/X` (`iMag`); a static formula, no converter dynamics.

Source: work-sync `theory/T-dc-voltage-gfm.md` §1.7.

Results.
* `iMag_hasDerivAt`: `dI_omag/dδ = E V_g sin δ / (X² I_omag)` wherever `I_omag > 0` (the
  note's derivative).
* `iMag_strictMonoOn`: for `E, V_g, X > 0`, `I_omag` is strictly increasing in `δ` on
  `[0, π]` (in particular on `(0, π)`), so `I_omag` can replace the unmeasurable `δ` as the
  switching signal.
* `iMag_worstCase`: for `δ_th ∈ [0, π]` and `E ≥ 0`, `E sin δ_th/X ≤ I_omag(δ_th; V_g)` for
  every `V_g`, with equality at `V_g = E cos δ_th` (`iMag_at_worstCase`): the note's threshold
  `I_omag,th,min = E sin δ_th/(X_f + X_g)` is exactly the minimum over the grid voltage.
  (It is attained by a positive grid voltage iff `cos δ_th > 0`, i.e. `δ_th < π/2`.)
-/

noncomputable section
namespace powerlib.Limiting

/-- `I_omag(δ) = √(E² + V² − 2 E V cos δ)/X`. -/
def iMag (E V X δ : ℝ) : ℝ := Real.sqrt (E ^ 2 + V ^ 2 - 2 * E * V * Real.cos δ) / X

@[powerlib_foundation] theorem iMag_radicand (E V δ : ℝ) :
    E ^ 2 + V ^ 2 - 2 * E * V * Real.cos δ =
      (V - E * Real.cos δ) ^ 2 + (E * Real.sin δ) ^ 2 := by
  have := Real.sin_sq_add_cos_sq δ
  linear_combination (-E ^ 2) * this

@[powerlib_foundation] theorem iMag_radicand_nonneg (E V δ : ℝ) :
    0 ≤ E ^ 2 + V ^ 2 - 2 * E * V * Real.cos δ := by
  rw [iMag_radicand]
  positivity

/-- Derivative `E V sin δ/(X² I_omag)`. -/
@[powerlib_foundation] theorem iMag_hasDerivAt {E V X δ : ℝ} (hX : X ≠ 0)
    (hu : 0 < E ^ 2 + V ^ 2 - 2 * E * V * Real.cos δ) :
    HasDerivAt (iMag E V X) (E * V * Real.sin δ / (X ^ 2 * iMag E V X δ)) δ := by
  have hu' : HasDerivAt (fun d => E ^ 2 + V ^ 2 - 2 * E * V * Real.cos d)
      (2 * E * V * Real.sin δ) δ := by
    have := ((Real.hasDerivAt_cos δ).const_mul (2 * E * V)).const_sub (E ^ 2 + V ^ 2)
    convert this using 1
    ring
  have h := (hu'.sqrt hu.ne').div_const X
  have hs : 0 < Real.sqrt (E ^ 2 + V ^ 2 - 2 * E * V * Real.cos δ) := Real.sqrt_pos.mpr hu
  have hval : E * V * Real.sin δ / (X ^ 2 * iMag E V X δ) =
      2 * E * V * Real.sin δ / (2 * Real.sqrt (E ^ 2 + V ^ 2 - 2 * E * V * Real.cos δ)) / X := by
    rw [iMag]
    field_simp
  rw [hval]
  exact h

/-- `I_omag` is strictly increasing in `δ` on `[0, π]`. -/
@[powerlib_foundation] theorem iMag_strictMonoOn {E V X : ℝ} (hE : 0 < E) (hV : 0 < V)
    (hX : 0 < X) : StrictMonoOn (iMag E V X) (Set.Icc 0 Real.pi) := by
  intro a ha b hb hab
  have hcos : Real.cos b < Real.cos a := Real.strictAntiOn_cos ha hb hab
  apply div_lt_div_of_pos_right _ hX
  apply Real.sqrt_lt_sqrt (iMag_radicand_nonneg E V a)
  nlinarith [mul_pos hE hV]

/-- The worst-case threshold `E sin δ_th/X` is a lower bound over all grid voltages. -/
@[powerlib_foundation] theorem iMag_worstCase {E X δ : ℝ} (hE : 0 ≤ E) (hX : 0 < X)
    (hδ0 : 0 ≤ δ) (hδπ : δ ≤ Real.pi) (V : ℝ) :
    E * Real.sin δ / X ≤ iMag E V X δ := by
  apply div_le_div_of_nonneg_right _ hX.le
  have hs : 0 ≤ E * Real.sin δ := mul_nonneg hE (Real.sin_nonneg_of_nonneg_of_le_pi hδ0 hδπ)
  rw [iMag_radicand]
  calc E * Real.sin δ = Real.sqrt ((E * Real.sin δ) ^ 2) := (Real.sqrt_sq hs).symm
    _ ≤ Real.sqrt ((V - E * Real.cos δ) ^ 2 + (E * Real.sin δ) ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (V - E * Real.cos δ)])

/-- Equality at `V_g = E cos δ_th`. -/
@[powerlib_foundation] theorem iMag_at_worstCase {E X δ : ℝ} (hE : 0 ≤ E) (hδ0 : 0 ≤ δ)
    (hδπ : δ ≤ Real.pi) : iMag E (E * Real.cos δ) X δ = E * Real.sin δ / X := by
  have hs : 0 ≤ E * Real.sin δ := mul_nonneg hE (Real.sin_nonneg_of_nonneg_of_le_pi hδ0 hδπ)
  simp only [iMag]
  rw [iMag_radicand, sub_self, zero_pow two_ne_zero, zero_add, Real.sqrt_sq hs]

/-- The threshold is the minimum of `I_omag(δ_th; ·)` over the grid voltage. -/
@[powerlib_foundation] theorem iMag_isLeast {E X δ : ℝ} (hE : 0 ≤ E) (hX : 0 < X)
    (hδ0 : 0 ≤ δ) (hδπ : δ ≤ Real.pi) :
    IsLeast (Set.range fun V => iMag E V X δ) (E * Real.sin δ / X) :=
  ⟨⟨E * Real.cos δ, iMag_at_worstCase hE hδ0 hδπ⟩,
    by rintro _ ⟨V, rfl⟩; exact iMag_worstCase hE hX hδ0 hδπ V⟩

end powerlib.Limiting
