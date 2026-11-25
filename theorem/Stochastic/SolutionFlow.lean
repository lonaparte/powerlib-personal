import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.AdditiveNoise

/-! # The flow property of the pathwise additive-noise solution

The pathwise solution of `x(t) = x₀ + N w(t) + ∫₀ᵗ b(x)` on `[0, T₁ + T₂]` restarted at time
`T₁` is the solution on `[0, T₂]` from `x(T₁)` driven by the increments
`θ_{T₁} w(t) = w(T₁ + t) − w(T₁)`: `x(T₁ + t) = S(x(T₁), θ_{T₁} w)(t)`. With the weak Markov
property of Brownian motion (Mathlib's `IsPreBrownianReal.shift`,
`IsPreBrownianReal.indepFun_shift`: `θ_{t₀} B` is a Brownian motion independent of
`(B_t)_{t ≤ t₀}`) this is the pathwise half of the Markov property of the solution at
deterministic times.

Scope.
* Generic: `E`, `F` real Banach spaces, `b` globally Lipschitz, `N : F →L[ℝ] E`; deterministic
  (path by path). The probabilistic Markov property (conditional law given the past) is not
  formalized here.

Source: M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 3 §1 (the solution as a functional of the driving path; its restarts).

Results.
* `shiftPath` (the increments after `T₁`), `pathExt_solMap_add` (**flow property**).
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory Set
open scoped NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The increments `θ_{T₁} w(t) = w(T₁ + t) − w(T₁)` of a path on `[0, T₁ + T₂]`, as a path on
`[0, T₂]`. -/
def shiftPath (T₁ T₂ : ℝ≥0) (w : C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), F)) : C(Icc (0 : ℝ) T₂, F) :=
  ⟨fun t => pathExt w (T₁ + t) - pathExt w T₁,
    ((continuous_pathExt w).comp (continuous_const.add continuous_subtype_val)).sub
      continuous_const⟩

/-- **Flow property**: `x(T₁ + t) = S(x(T₁), θ_{T₁} w)(t)` for `t ∈ [0, T₂]`, `x = S(x₀, w)` on
`[0, T₁ + T₂]`. -/
@[tmio T, powerlib_foundation] theorem pathExt_solMap_add {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : F →L[ℝ] E) (x₀ : E) {T₁ T₂ : ℝ≥0}
    (w : C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), F)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T₂) :
    pathExt (solMap b N x₀ w) (T₁ + t) =
      pathExt (solMap b N (pathExt (solMap b N x₀ w) T₁) (shiftPath T₁ T₂ w)) t := by
  have hspec := solMap_spec hb N x₀ w
  generalize hx : solMap b N x₀ w = x at hspec ⊢
  have hsum : ((T₁ + T₂ : ℝ≥0) : ℝ) = T₁ + T₂ := NNReal.coe_add T₁ T₂
  have hmem : ∀ s ∈ Icc (0 : ℝ) T₂, (T₁ : ℝ) + s ∈ Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0) := fun s hs => by
    rw [hsum]; exact ⟨by linarith [hs.1, T₁.coe_nonneg], by linarith [hs.2]⟩
  have hmem1 : (T₁ : ℝ) ∈ Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0) := by
    rw [hsum]; exact ⟨T₁.coe_nonneg, by linarith [T₂.coe_nonneg]⟩
  have hbx : Continuous fun s => b (pathExt x s) := hb.continuous.comp (continuous_pathExt x)
  let z : C(Icc (0 : ℝ) T₂, E) :=
    ⟨fun s => pathExt x (T₁ + s),
      (continuous_pathExt x).comp (continuous_const.add continuous_subtype_val)⟩
  have hz : ∀ s : Icc (0 : ℝ) T₂, z s = pathExt x T₁ + N (shiftPath T₁ T₂ w s) +
      ∫ r in (0 : ℝ)..s, b (pathExt z r) := by
    intro s
    have hs := s.2
    have hcongr : ∫ r in (0 : ℝ)..s, b (pathExt z r) =
        ∫ r in (0 : ℝ)..s, b (pathExt x (T₁ + r)) := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hs.1] at hr
      have hrT : r ∈ Icc (0 : ℝ) T₂ := ⟨hr.1, hr.2.trans hs.2⟩
      simp only [pathExt_of_mem z hrT]
      rfl
    have hshift : ∫ r in (0 : ℝ)..s, b (pathExt x (T₁ + r)) =
        ∫ r in (T₁ : ℝ)..(T₁ + s), b (pathExt x r) := by
      rw [intervalIntegral.integral_comp_add_left (fun r => b (pathExt x r)), add_zero]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hbx.intervalIntegrable (μ := volume) 0 (T₁ : ℝ))
      (hbx.intervalIntegrable (μ := volume) (T₁ : ℝ) (T₁ + s))
    have h1 : z s = pathExt x (T₁ + s) := rfl
    rw [h1, hcongr, hshift, pathExt_of_mem x (hmem s hs), hspec,
      pathExt_of_mem x hmem1, hspec]
    simp only [shiftPath, ContinuousMap.coe_mk, pathExt_of_mem w (hmem s hs),
      pathExt_of_mem w hmem1, map_sub]
    rw [← hsplit]
    abel
  have hzS := eq_solMap hb hz
  rw [pathExt_of_mem _ ht, ← hzS]
  rfl

end powerlib.Stochastic.LDP
