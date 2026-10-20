import theorem.GFL.DCLink.FourState

/-! # Integrator time-average constraints on periodic solutions

Integral identities (foundation; fundamental theorem of calculus) for periodic solutions of the
angle-driven four-state GFL field.

Model boundary.
The angle-driven four-state GFL field `FourState.fieldAngle` (state `(θ, x, V, η)`, IN-positive,
grid angle `θ_g` entering only as `−θ̇_g`). Any solution `φ` over `[0, T]` that returns to its
initial state, with a grid angle `θ_g` that also returns to its initial value and has a
continuous rate. Nothing is assumed about the existence or stability of the periodic solution.

Source: work-sync `projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/
gfl-gfm-parametric-contrast.md` §14 (积分器约束).

Results.
* `∫₀ᵀ (V − 1) = 0` (from `η̇ = V − 1`), i.e. `⟨V⟩ = 1`;
* `∫₀ᵀ v_q = 0` (from `ẋ = v_q`);
* `k_i ∫₀ᵀ x = 0` (from `θ̇ = k_p v_q + k_i x − θ̇_g`), so `⟨x⟩ = 0` when `k_i ≠ 0`.

Family and connection conclusions.
No new family and no connection conclusion. The integral identities concern solutions of the
input-driven field `fieldAngle` of this specific model, which lies outside the autonomous sentence
language of `FourState.family`; they are kept as private implementation evidence (Rules §3a). The
public result is the static component form `fieldAngle_apply`.
-/

noncomputable section
namespace powerlib.GFL.Parametric.Averages
open powerlib.GFL.DCLink
open FourState intervalIntegral

variable (p : FourState.Params)

/-- Component form of the angle-driven field. -/
@[powerlib_foundation] theorem fieldAngle_apply (u ud : ℝ) (z : Dynamics.State 4) :
    (fieldAngle p u ud z) 0 =
        p.kp * vq p (z 0) (z 2) (z 3) + p.ki * z 1 - ud ∧
      (fieldAngle p u ud z) 1 = vq p (z 0) (z 2) (z 3) ∧
      (fieldAngle p u ud z) 3 = z 2 - 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [fieldAngle, field, Dynamics.lift, coordField]

@[powerlib_foundation] private theorem hasDerivAt_coord {φ : ℝ → Dynamics.State 4} {θg θgd : ℝ → ℝ}
    (hφ : ∀ t, HasDerivAt φ (fieldAngle p (θg t) (θgd t) (φ t)) t) (i : Fin 4) (t : ℝ) :
    HasDerivAt (fun s => φ s i) (fieldAngle p (θg t) (θgd t) (φ t) i) t := by
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt t (hφ t)

@[powerlib_foundation] private theorem continuous_coord {φ : ℝ → Dynamics.State 4} {θg θgd : ℝ → ℝ}
    (hφ : ∀ t, HasDerivAt φ (fieldAngle p (θg t) (θgd t) (φ t)) t) (i : Fin 4) :
    Continuous fun s => φ s i :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_coord p hφ i t).continuousAt

@[powerlib_foundation] private theorem continuous_vq {φ : ℝ → Dynamics.State 4} {θg θgd : ℝ → ℝ}
    (hφ : ∀ t, HasDerivAt φ (fieldAngle p (θg t) (θgd t) (φ t)) t) :
    Continuous fun s => vq p (φ s 0) (φ s 2) (φ s 3) := by
  have h0 := continuous_coord p hφ 0
  have h2 := continuous_coord p hφ 2
  have h3 := continuous_coord p hφ 3
  exact (continuous_const.mul (Real.continuous_sin.comp h0)).sub (continuous_const.mul
    ((continuous_const.sub (continuous_const.mul (h2.sub continuous_const))).sub
      (continuous_const.mul h3)))

/-- `⟨V⟩ = 1`: `∫₀ᵀ (V − 1) dt = 0` on a returning solution. -/
@[powerlib_foundation] private theorem integral_V_sub_one {φ : ℝ → Dynamics.State 4}
    {θg θgd : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (fieldAngle p (θg t) (θgd t) (φ t)) t)
    {T : ℝ} (hT : φ T = φ 0) :
    ∫ t in (0 : ℝ)..T, (φ t 2 - 1) = 0 := by
  have hd : ∀ t ∈ Set.uIcc 0 T, HasDerivAt (fun s => φ s 3) (φ t 2 - 1) t := by
    intro t _
    have := hasDerivAt_coord p hφ 3 t
    rwa [(fieldAngle_apply p _ _ _).2.2] at this
  rw [integral_eq_sub_of_hasDerivAt hd
    (((continuous_coord p hφ 2).sub continuous_const).intervalIntegrable _ _), hT, sub_self]

/-- `⟨v_q⟩ = 0`: `∫₀ᵀ v_q dt = 0` on a returning solution. -/
@[powerlib_foundation] private theorem integral_vq {φ : ℝ → Dynamics.State 4} {θg θgd : ℝ → ℝ}
    (hφ : ∀ t, HasDerivAt φ (fieldAngle p (θg t) (θgd t) (φ t)) t) {T : ℝ} (hT : φ T = φ 0) :
    ∫ t in (0 : ℝ)..T, vq p (φ t 0) (φ t 2) (φ t 3) = 0 := by
  have hd : ∀ t ∈ Set.uIcc 0 T,
      HasDerivAt (fun s => φ s 1) (vq p (φ t 0) (φ t 2) (φ t 3)) t := by
    intro t _
    have := hasDerivAt_coord p hφ 1 t
    rwa [(fieldAngle_apply p _ _ _).2.1] at this
  rw [integral_eq_sub_of_hasDerivAt hd ((continuous_vq p hφ).intervalIntegrable _ _), hT,
    sub_self]

/-- `k_i ⟨x⟩ = 0`: `k_i ∫₀ᵀ x dt = 0` on a returning solution with returning grid angle. -/
@[powerlib_foundation] private theorem ki_mul_integral_x {φ : ℝ → Dynamics.State 4} {θg θgd : ℝ → ℝ}
    (hφ : ∀ t, HasDerivAt φ (fieldAngle p (θg t) (θgd t) (φ t)) t)
    (hθg : ∀ t, HasDerivAt θg (θgd t) t) (hθgd : Continuous θgd) {T : ℝ} (hT : φ T = φ 0)
    (hTg : θg T = θg 0) :
    p.ki * ∫ t in (0 : ℝ)..T, φ t 1 = 0 := by
  have hvq := continuous_vq p hφ
  have hx := continuous_coord p hφ 1
  have hd : ∀ t ∈ Set.uIcc 0 T, HasDerivAt (fun s => φ s 0)
      (p.kp * vq p (φ t 0) (φ t 2) (φ t 3) + p.ki * φ t 1 - θgd t) t := by
    intro t _
    have := hasDerivAt_coord p hφ 0 t
    rwa [(fieldAngle_apply p _ _ _).1] at this
  have hi1 : IntervalIntegrable (fun y => p.kp * vq p (φ y 0) (φ y 2) (φ y 3))
      MeasureTheory.volume 0 T := (continuous_const.mul hvq).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun y => p.ki * φ y 1) MeasureTheory.volume 0 T :=
    (continuous_const.mul hx).intervalIntegrable _ _
  have hi3 : IntervalIntegrable θgd MeasureTheory.volume 0 T := hθgd.intervalIntegrable _ _
  have h0 := integral_eq_sub_of_hasDerivAt hd ((hi1.add hi2).sub hi3)
  rw [hT, sub_self] at h0
  have hg := integral_eq_sub_of_hasDerivAt (fun t _ => hθg t) hi3
  rw [hTg, sub_self] at hg
  have hq := integral_vq p hφ hT
  rw [integral_sub (hi1.add hi2) hi3, integral_add hi1 hi2, integral_const_mul,
    integral_const_mul, hq, hg] at h0
  linarith

/-- `⟨x⟩ = 0` when `k_i ≠ 0`. -/
@[powerlib_foundation] private theorem integral_x {φ : ℝ → Dynamics.State 4} {θg θgd : ℝ → ℝ}
    (hφ : ∀ t, HasDerivAt φ (fieldAngle p (θg t) (θgd t) (φ t)) t)
    (hθg : ∀ t, HasDerivAt θg (θgd t) t) (hθgd : Continuous θgd) (hki : p.ki ≠ 0) {T : ℝ}
    (hT : φ T = φ 0) (hTg : θg T = θg 0) :
    ∫ t in (0 : ℝ)..T, φ t 1 = 0 := by
  have := ki_mul_integral_x p hφ hθg hθgd hT hTg
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hki
  · exact h

end powerlib.GFL.Parametric.Averages
