/-
  Theorem B, full system — the slow-mode equation reframed as a SCALAR root problem (path C).

  Reviewer's observation (correct): locating the slow eigenvalue λ_slow ≈ −b of the full 9×9 J_S
  does NOT require matrix perturbation theory (Bauer–Fike / Kato) or complex Rouché.  By the Schur
  determinant identity (`variantS_schur_det`), for μ ∉ spec(A),

      det(J_S − μ·I) = det(A − μ·I) · h(μ),   h(μ) := (j99 − μ) − ρᵀ(A − μ·I)⁻¹ c,

  so μ is an eigenvalue of J_S iff the SCALAR function h vanishes.  This file machine-checks the
  backbone of the scalar route (all pure linear algebra, no `sorry`):

    * `slowModeH`               : the scalar slow-mode function h.
    * `slowMode_det_factor`     : det(J_S − μI) = det(A − μI)·h(μ)  (Schur identity, renamed).
    * `slowMode_det_zero_iff`   : for μ ∉ spec(A),  det(J_S − μI) = 0 ↔ h(μ) = 0.
    * `eigenvalue_of_slowMode_zero` : h(μ) = 0  ⟹  μ is a genuine eigenvalue of J_S
                                      (∃ nonzero v, J_S·v = μ•v) — the scalar zero IS an eigenvalue.
    * `slowModeH_at_neg_b`      : h(−b) = −(3/2)·(wn/(Sn·D))·Vg·b²·[(A+bI)⁻¹A⁻¹c]₀  — the residual
                                  of the leading guess μ = −b is EXACTLY O(b²).

  What remains for the full existence statement |λ_slow − (−b)| ≤ C·b² (documented in TODO.md, and
  NOT a Mathlib blocker — see C in the review): h is C¹ in μ near −b with h'(−b) = −1 + O(b) ≠ 0,
  so the scalar inverse function theorem (`Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv`)
  produces the unique nearby root μ* = −b + O(b²).  The matrix-free O(b²) residual proved here is
  the substance of that bound.
-/
import GFL.AsymptoticB
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

namespace GFL

open Matrix Filter Topology

/-- The scalar slow-mode function `h(μ) := (j99 − μ) − ρᵀ(A − μ·I)⁻¹ c`.
For `μ ∉ spec(A)`, `μ ∈ spec(J_S) ↔ h(μ) = 0` (`slowMode_det_zero_iff`). -/
noncomputable def slowModeH (A : Matrix (Fin 8) (Fin 8) ℝ) (c ρ : Fin 8 → ℝ) (j99 μ : ℝ) : ℝ :=
  (j99 - μ) - ρ ⬝ᵥ ((A - μ • 1)⁻¹ *ᵥ c)

/-- Schur determinant identity, restated with `h`: `det(J_S − μI) = det(A − μI)·h(μ)`. -/
theorem slowMode_det_factor (A : Matrix (Fin 8) (Fin 8) ℝ) (c ρ : Fin 8 → ℝ) (j99 μ : ℝ)
    (hA : IsUnit (A - μ • 1).det) :
    (JSblock A c ρ j99 - μ • 1).det = (A - μ • 1).det * slowModeH A c ρ j99 μ :=
  variantS_schur_det A c ρ j99 μ hA

/-- **Eigenvalue ⟺ scalar zero.**  For `μ ∉ spec(A)` (`A − μI` invertible), `μ` is an eigenvalue
of `J_S` iff the scalar slow-mode function vanishes: `det(J_S − μI) = 0 ↔ h(μ) = 0`. -/
theorem slowMode_det_zero_iff (A : Matrix (Fin 8) (Fin 8) ℝ) (c ρ : Fin 8 → ℝ) (j99 μ : ℝ)
    (hA : IsUnit (A - μ • 1).det) :
    (JSblock A c ρ j99 - μ • 1).det = 0 ↔ slowModeH A c ρ j99 μ = 0 := by
  rw [slowMode_det_factor A c ρ j99 μ hA, mul_eq_zero, or_iff_right hA.ne_zero]

/-- **The scalar zero IS an eigenvalue.**  If `h(μ) = 0` (and `μ ∉ spec(A)`), then `J_S − μI` is
singular, so there is a nonzero `v` with `J_S · v = μ · v`: `μ` is a genuine eigenvalue of the
full block system `J_S`.  (Same nontrivial-kernel argument as Theorem A, via
`exists_mulVec_eq_zero_iff`.) -/
theorem eigenvalue_of_slowMode_zero (A : Matrix (Fin 8) (Fin 8) ℝ) (c ρ : Fin 8 → ℝ) (j99 μ : ℝ)
    (hA : IsUnit (A - μ • 1).det) (hh : slowModeH A c ρ j99 μ = 0) :
    ∃ v : (Fin 8 ⊕ Unit) → ℝ, v ≠ 0 ∧ JSblock A c ρ j99 *ᵥ v = μ • v := by
  have hdet : (JSblock A c ρ j99 - μ • 1).det = 0 :=
    (slowMode_det_zero_iff A c ρ j99 μ hA).mpr hh
  obtain ⟨v, hv0, hvk⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv0, ?_⟩
  have h := hvk
  rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at h
  exact h

/-- **The residual of the leading guess `μ = −b` is exactly `O(b²)`.**
With `j99 = −b` (Variant S) and the Power-Lock hypotheses,
`h(−b) = −(3/2)·(wn/(Sn·D))·Vg · b² · [(A+bI)⁻¹A⁻¹c]₀`.  So the scalar function `h` — whose zero is
the slow eigenvalue — is already `O(b²)` at the leading guess `−b`; this is the matrix-free content
of `λ_slow = −b + O(b²)`.  (Proof: `h(−b) = (j99 + b) − ρᵀ(A+bI)⁻¹c = 0 − [b² term]` via
`schur_term_b_sq`.) -/
theorem slowModeH_at_neg_b (p : Params)
    (A : Matrix (Fin 8) (Fin 8) ℝ) (hA : IsUnit A.det) (hB : IsUnit (A + p.b • 1).det)
    (c v : Fin 8 → ℝ) (hAv : A *ᵥ v = -c) (hv0 : v 0 = 0)
    (ρ : Fin 8 → ℝ) (hρ : ρ = (-(3 / 2) * p.kappa * p.Vg) • Pi.single 0 1)
    (j99 : ℝ) (hj99 : j99 = -p.b) :
    slowModeH A c ρ j99 (-p.b)
      = -((3 / 2) * (p.wn / (p.Sn * p.D)) * p.Vg * p.b ^ 2 *
          (((A + p.b • 1)⁻¹ *ᵥ (A⁻¹ *ᵥ c)) 0)) := by
  have hsub : A - (-p.b) • (1 : Matrix (Fin 8) (Fin 8) ℝ) = A + p.b • 1 := by
    rw [neg_smul, sub_neg_eq_add]
  unfold slowModeH
  rw [hsub, hj99, schur_term_b_sq p A hA hB c v hAv hv0 ρ hρ]
  ring

/-! ### C, step T1 — `h` is differentiable in `μ` (the analytic input is just continuity)

The earlier (wrong) framing said this needs operator-norm / Rouché machinery.  It does not: the
resolvent `μ ↦ (A − μI)⁻¹` is continuous wherever `det(A − μI) ≠ 0` (`inv = det⁻¹ • adjugate`, both
continuous, `det ≠ 0` near `ν`), and the resolvent identity `resolvent_sub` is the exact difference
quotient.  Continuity of the slope + the exact quotient ⟹ `HasDerivAt`. -/

/-- `μ ↦ (A − μI)⁻¹` is continuous at any `ν` with `det(A − νI) ≠ 0`. -/
theorem resolvent_continuousAt (A : Matrix (Fin 8) (Fin 8) ℝ) (ν : ℝ)
    (hν : (A - ν • 1).det ≠ 0) :
    ContinuousAt (fun μ : ℝ => (A - μ • (1 : Matrix (Fin 8) (Fin 8) ℝ))⁻¹) ν := by
  have hAμ : Continuous (fun μ : ℝ => A - μ • (1 : Matrix (Fin 8) (Fin 8) ℝ)) :=
    continuous_const.sub (continuous_id.smul continuous_const)
  have hdet : ContinuousAt (fun μ : ℝ => (A - μ • 1).det) ν := hAμ.matrix_det.continuousAt
  have hadj : ContinuousAt (fun μ : ℝ => (A - μ • 1).adjugate) ν := hAμ.matrix_adjugate.continuousAt
  have hinv : ContinuousAt (fun μ : ℝ => Ring.inverse (A - μ • 1).det) ν := by
    simp_rw [Ring.inverse_eq_inv]
    exact hdet.inv₀ hν
  have hrw : (fun μ : ℝ => (A - μ • (1 : Matrix (Fin 8) (Fin 8) ℝ))⁻¹)
      = fun μ => Ring.inverse (A - μ • 1).det • (A - μ • 1).adjugate := by
    funext μ; rw [Matrix.inv_def]
  rw [hrw]
  exact hinv.smul hadj

/-- **C, T1 — the scalar slow-mode function `h` is differentiable.**  At any `ν` with
`det(A − νI) ≠ 0`,
`d/dμ h(μ)|_ν = −1 − ρᵀ(A − νI)⁻¹(A − νI)⁻¹c`,
the standard resolvent-derivative formula `d/dμ (A−μI)⁻¹ = (A−μI)⁻²`.  Proof: the resolvent identity
`resolvent_sub` makes the slope of `r(μ) = ρᵀ(A−μI)⁻¹c` exactly `ρᵀ(A−μI)⁻¹(A−νI)⁻¹c`, which is
continuous at `ν` (`resolvent_continuousAt`); `hasDerivAt_iff_tendsto_slope` closes it. -/
theorem slowModeH_hasDerivAt (A : Matrix (Fin 8) (Fin 8) ℝ) (c ρ : Fin 8 → ℝ) (j99 ν : ℝ)
    (hν : (A - ν • 1).det ≠ 0) :
    HasDerivAt (fun μ => slowModeH A c ρ j99 μ)
      (-1 - ρ ⬝ᵥ ((A - ν • 1)⁻¹ *ᵥ ((A - ν • 1)⁻¹ *ᵥ c))) ν := by
  set w : Fin 8 → ℝ := (A - ν • 1)⁻¹ *ᵥ c with hw
  -- the resolvent term r(μ) = ρ ⬝ᵥ ((A−μI)⁻¹ *ᵥ c) has derivative ρ ⬝ᵥ ((A−νI)⁻¹ *ᵥ w)
  have hr : HasDerivAt (fun μ => ρ ⬝ᵥ ((A - μ • 1)⁻¹ *ᵥ c))
      (ρ ⬝ᵥ ((A - ν • 1)⁻¹ *ᵥ w)) ν := by
    rw [hasDerivAt_iff_tendsto_slope]
    -- s(μ) := ρ ⬝ᵥ ((A−μI)⁻¹ *ᵥ w) is continuous at ν
    have hcont : ContinuousAt (fun μ => ρ ⬝ᵥ ((A - μ • 1)⁻¹ *ᵥ w)) ν := by
      have hφ : Continuous (fun M : Matrix (Fin 8) (Fin 8) ℝ => ρ ⬝ᵥ (M *ᵥ w)) :=
        continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
      exact hφ.continuousAt.comp (resolvent_continuousAt A ν hν)
    -- det(A−μI) ≠ 0 near ν
    have hUnit : ∀ᶠ μ in 𝓝 ν, (A - μ • 1).det ≠ 0 := by
      have : Continuous (fun μ : ℝ => (A - μ • (1 : Matrix (Fin 8) (Fin 8) ℝ)).det) :=
        (continuous_const.sub (continuous_id.smul continuous_const)).matrix_det
      exact this.continuousAt.eventually_ne hν
    -- on 𝓝[≠] ν the slope equals s(μ)
    have hslope : slope (fun μ => ρ ⬝ᵥ ((A - μ • 1)⁻¹ *ᵥ c)) ν
        =ᶠ[𝓝[≠] ν] fun μ => ρ ⬝ᵥ ((A - μ • 1)⁻¹ *ᵥ w) := by
      have hev : ∀ᶠ μ in 𝓝[≠] ν, (A - μ • 1).det ≠ 0 := nhdsWithin_le_nhds hUnit
      filter_upwards [hev, self_mem_nhdsWithin] with μ hμdet hμν
      have hμν' : μ ≠ ν := hμν
      rw [slope_def_field]
      have hrr : ρ ⬝ᵥ ((A - μ • 1)⁻¹ *ᵥ c) - ρ ⬝ᵥ ((A - ν • 1)⁻¹ *ᵥ c)
          = (μ - ν) * (ρ ⬝ᵥ ((A - μ • 1)⁻¹ *ᵥ w)) := by
        rw [hw, ← dotProduct_sub, ← Matrix.sub_mulVec,
            resolvent_sub A μ ν (isUnit_iff_ne_zero.mpr hμdet) (isUnit_iff_ne_zero.mpr hν),
            Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_mulVec]
      rw [hrr, mul_comm, mul_div_assoc, div_self (sub_ne_zero.mpr hμν'), mul_one]
    rw [tendsto_congr' hslope]
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  -- h(μ) = (j99 − μ) − r(μ);  derivative = −1 − r'(ν)
  have hlin : HasDerivAt (fun μ : ℝ => j99 - μ) (-1 : ℝ) ν := by
    simpa using (hasDerivAt_id ν).const_sub j99
  exact hlin.sub hr

/-- **C, existence — a sign change of `h` yields a genuine eigenvalue of `J_S`.**
If `A − μI` is invertible on `[a,b]` and the scalar slow-mode function `h` changes sign across
`[a,b]`, then (h continuous there, IVT) `h` has a zero `μ* ∈ [a,b]`, which is a genuine eigenvalue
of `J_S` (`eigenvalue_of_slowMode_zero`).  Instantiating `[a,b]` around `−b` — where
`h(−b) = O(b²)` (`slowModeH_at_neg_b`) and `h' = −1 + O(b) < 0` (`slowModeH_hasDerivAt`) — gives the
slow eigenvalue `λ_slow ≈ −b`; the only quantitative input is the sign change (i.e. `−b` lies on the
correct side of the root by an `O(b²)` margin), which replaces the operator-norm bound. -/
theorem exists_eigenvalue_of_slowMode_sign_change
    (A : Matrix (Fin 8) (Fin 8) ℝ) (c ρ : Fin 8 → ℝ) (j99 : ℝ) {a b : ℝ} (hab : a ≤ b)
    (hinv : ∀ μ ∈ Set.Icc a b, (A - μ • 1).det ≠ 0)
    (hsign : (slowModeH A c ρ j99 a ≤ 0 ∧ 0 ≤ slowModeH A c ρ j99 b) ∨
             (slowModeH A c ρ j99 b ≤ 0 ∧ 0 ≤ slowModeH A c ρ j99 a)) :
    ∃ μ ∈ Set.Icc a b, ∃ v : (Fin 8 ⊕ Unit) → ℝ, v ≠ 0 ∧ JSblock A c ρ j99 *ᵥ v = μ • v := by
  -- h is continuous on [a,b] (it is differentiable there, by slowModeH_hasDerivAt)
  have hcont : ContinuousOn (fun μ => slowModeH A c ρ j99 μ) (Set.Icc a b) := fun μ hμ =>
    (slowModeH_hasDerivAt A c ρ j99 μ (hinv μ hμ)).continuousAt.continuousWithinAt
  -- IVT: a zero of h in [a,b]
  obtain ⟨μ, hμmem, hμ0⟩ : ∃ μ ∈ Set.Icc a b, slowModeH A c ρ j99 μ = 0 := by
    rcases hsign with h | h
    · obtain ⟨μ, hm, hv⟩ := intermediate_value_Icc hab hcont (Set.mem_Icc.mpr h); exact ⟨μ, hm, hv⟩
    · obtain ⟨μ, hm, hv⟩ := intermediate_value_Icc' hab hcont (Set.mem_Icc.mpr h); exact ⟨μ, hm, hv⟩
  -- the zero is an eigenvalue of J_S
  obtain ⟨v, hv0, hvk⟩ :=
    eigenvalue_of_slowMode_zero A c ρ j99 μ (isUnit_iff_ne_zero.mpr (hinv μ hμmem)) hμ0
  exact ⟨μ, hμmem, v, hv0, hvk⟩

/-! ### C, step T6 — the quantitative `O(b²)` bound (replaces the sign-change with a derivative bound)

The only quantitative input the existence needs is a **derivative lower bound** `h' ≤ −m < 0` on an
interval (nondegeneracy of the slow mode), NOT an operator-norm estimate.  Given that, the
mean-value theorem turns the small residual `|h(ν₀)|` into a sign change over `[ν₀−δ, ν₀+δ]` with
`δ = |h(ν₀)|/m`, so a root sits within `δ` of `ν₀`.  Taking `ν₀ = −b`, `|h(−b)| = O(b²)`
(`slowModeH_at_neg_b`) gives `|λ_slow + b| ≤ O(b²)/m`. -/

/-- **Quantitative root from a derivative bound (general, no operator norm).**  If `h` is
differentiable on `[ν₀−δ, ν₀+δ]` with `h' ≤ −m < 0` there, and `|h ν₀| ≤ m·δ`, then `h` has a zero
`μ*` with `|μ* − ν₀| ≤ δ`.  (MVT bounds `h(ν₀∓δ)` away from `h ν₀` by `m·δ ≥ |h ν₀|`, forcing a sign
change; IVT gives the root.) -/
theorem exists_root_of_deriv_le (h h' : ℝ → ℝ) (ν₀ δ m : ℝ) (hm : 0 < m)
    (hderiv : ∀ μ ∈ Set.Icc (ν₀ - δ) (ν₀ + δ), HasDerivAt h (h' μ) μ)
    (hbd : ∀ μ ∈ Set.Icc (ν₀ - δ) (ν₀ + δ), h' μ ≤ -m)
    (hmδ : |h ν₀| ≤ m * δ) :
    ∃ μ ∈ Set.Icc (ν₀ - δ) (ν₀ + δ), h μ = 0 := by
  have h0 : 0 ≤ m * δ := le_trans (abs_nonneg _) hmδ
  have hδ : 0 ≤ δ := by
    by_contra hc
    nlinarith [mul_pos hm (neg_pos.mpr (not_le.mp hc))]
  have habs := abs_le.mp hmδ
  have hcont : ContinuousOn h (Set.Icc (ν₀ - δ) (ν₀ + δ)) := fun μ hμ =>
    (hderiv μ hμ).continuousAt.continuousWithinAt
  rcases eq_or_lt_of_le hδ with hδ0 | hδ0
  · -- δ = 0: |h ν₀| ≤ 0 ⟹ h ν₀ = 0
    refine ⟨ν₀, by simp [← hδ0], abs_nonpos_iff.mp ?_⟩
    rw [← hδ0] at hmδ; simpa using hmδ
  · -- δ > 0: sign change at the endpoints, then IVT
    have hden : ν₀ - (ν₀ - δ) = δ := by ring
    have hden' : ν₀ + δ - ν₀ = δ := by ring
    have hleft : 0 ≤ h (ν₀ - δ) := by
      obtain ⟨ξ, hξmem, hξ⟩ := exists_hasDerivAt_eq_slope h h' (by linarith : ν₀ - δ < ν₀)
        (hcont.mono (Set.Icc_subset_Icc le_rfl (by linarith)))
        (fun x hx => hderiv x ⟨le_of_lt hx.1, by linarith [hx.2]⟩)
      rw [hden] at hξ
      have hbξ : h' ξ ≤ -m := hbd ξ ⟨by linarith [hξmem.1], by linarith [hξmem.2]⟩
      rw [hξ] at hbξ
      have := (div_le_iff₀ hδ0).mp hbξ
      linarith [habs.1]
    have hright : h (ν₀ + δ) ≤ 0 := by
      obtain ⟨ξ, hξmem, hξ⟩ := exists_hasDerivAt_eq_slope h h' (by linarith : ν₀ < ν₀ + δ)
        (hcont.mono (Set.Icc_subset_Icc (by linarith) le_rfl))
        (fun x hx => hderiv x ⟨by linarith [hx.1], le_of_lt hx.2⟩)
      rw [hden'] at hξ
      have hbξ : h' ξ ≤ -m := hbd ξ ⟨by linarith [hξmem.1], by linarith [hξmem.2]⟩
      rw [hξ] at hbξ
      have := (div_le_iff₀ hδ0).mp hbξ
      linarith [habs.2]
    obtain ⟨μ, hμmem, hμ0⟩ :=
      intermediate_value_Icc' (by linarith : ν₀ - δ ≤ ν₀ + δ) hcont ⟨hright, hleft⟩
    exact ⟨μ, hμmem, hμ0⟩

/-- **C / T6 — the slow eigenvalue exists within `O(b²)` of `−b` (quantitative, no operator norm).**
If `A − μI` is invertible on `[−b−δ, −b+δ]`, the slow-mode derivative is `≤ −m < 0` there
(nondegeneracy of the slow mode — a clean named hypothesis, replacing any operator-norm estimate),
and `|h(−b)| ≤ m·δ`, then `J_S` has a genuine eigenvalue `μ*` with `|μ* + b| ≤ δ`.  Since
`|h(−b)| = O(b²)` (`slowModeH_at_neg_b`), `δ` may be taken `O(b²)/m`, so `|λ_slow + b| ≤ O(b²)/m`. -/
theorem exists_eigenvalue_near_neg_b (A : Matrix (Fin 8) (Fin 8) ℝ) (c ρ : Fin 8 → ℝ) (j99 b δ m : ℝ)
    (hm : 0 < m)
    (hinv : ∀ μ ∈ Set.Icc (-b - δ) (-b + δ), (A - μ • 1).det ≠ 0)
    (hbd : ∀ μ ∈ Set.Icc (-b - δ) (-b + δ),
      -1 - ρ ⬝ᵥ ((A - μ • 1)⁻¹ *ᵥ ((A - μ • 1)⁻¹ *ᵥ c)) ≤ -m)
    (hmδ : |slowModeH A c ρ j99 (-b)| ≤ m * δ) :
    ∃ μ ∈ Set.Icc (-b - δ) (-b + δ), ∃ v : (Fin 8 ⊕ Unit) → ℝ, v ≠ 0 ∧
      JSblock A c ρ j99 *ᵥ v = μ • v := by
  obtain ⟨μ, hμmem, hμ0⟩ := exists_root_of_deriv_le (fun μ => slowModeH A c ρ j99 μ)
    (fun μ => -1 - ρ ⬝ᵥ ((A - μ • 1)⁻¹ *ᵥ ((A - μ • 1)⁻¹ *ᵥ c))) (-b) δ m hm
    (fun μ hμ => slowModeH_hasDerivAt A c ρ j99 μ (hinv μ hμ)) hbd hmδ
  obtain ⟨v, hv0, hvk⟩ :=
    eigenvalue_of_slowMode_zero A c ρ j99 μ (isUnit_iff_ne_zero.mpr (hinv μ hμmem)) hμ0
  exact ⟨μ, hμmem, v, hv0, hvk⟩

end GFL
