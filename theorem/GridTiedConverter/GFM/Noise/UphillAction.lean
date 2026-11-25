import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.ControlledAction
import theorem.GridTiedConverter.GFM.Noise.FilterQuasiPotential

/-! # Action of the noisy three-state GFM along the uphill flow: an exact energy identity

Domain module: an exact pointwise identity for the action density of every admissible pair of the
three-state set-point noise model (`GFM.Noise.Params3.setPointQP`), read through the energy
`F = M ω²/2 + U(δ) + ω (P_ref − P_f)/ω_c + D ω²/(2 ω_c)` (`Params3.uphillEnergy`). Along the
uphill feedback `σ_P u = 2 D ω` (the feedback of the exact two-state solution, applied to three
states) `F` grows at the rate `D ω² + (M/ω_c) ω̇²`, so the action of an uphill pair is
`(2D/σ_P²)(F(end) − F(start) − (M/ω_c)∫ ω̇²)`: below the two-state value `(2D/σ_P²) ΔF` by
the explicit amount `(2DM/(σ_P² ω_c))∫ ω̇²`.

Model boundary.
* The three-state model of `GFM.Noise.FilterQuasiPotential` (`Params3.sdeDrift`: `δ̇ = ω`,
  `M ω̇ = P_ref − P_f − D ω`, `Ṗ_f = ω_c (P(δ) − P_f)`, `P(δ) = c₀ + A sin(δ − α)`), set-point
  noise column `(0, σ_P/M, 0)`, admissible pairs of `Stochastic.LDP.controlQuasiPotential`; any
  parameters of `Params3` (`M, ω_c, A > 0`, `D ≥ 0`), any `σ_P` (`σ_P ≠ 0` where a feedback is
  divided by it).
* `U(δ) = Params.potential (δ − α)` (`U' = P − P_ref`); at a rest point `(δ, 0, P_ref)`,
  `F = U(δ)`.
* Deterministic variational statements only, as in `GFM.Noise.FilterQuasiPotential`.

Source: Freidlin, Wentzell, *Random Perturbations of Dynamical Systems* (1984), Ch. 4 (uphill
paths of a damped system with momentum noise follow the feedback of the energy); the energy `F`,
the identity and the uphill rate were derived and checked symbolically (sympy, exact, symbolic
parameters) in the audit scratch notes outside the repository; the controlled-action objects of
`theorem/Stochastic/ControlledAction.lean`.

Results.
* `Params3.uphillEnergy`, `Params3.uphillEnergyDeriv`, `Params3.hasFDerivAt_uphillEnergy`,
  `Params3.uphillEnergy_rest` (`F(δ, 0, P_ref) = U(δ)`); `Params3.controlField_setPoint` (the
  controlled field in coordinates).
* `Params3.action_identity` (every control value): with `W = σ_P u`, `v = W − 2Dω` and
  `a = ω̇` the frequency row of the controlled field,
  `½ W² = 2D dF(ẋ) + ½ v² + (2D/ω_c) a v − (2DM/ω_c) a²`;
  `Params3.action_le_energy`: `½ W² ≤ 2D dF(ẋ) + ½ (1 + D/(M ω_c)) v²` (the gap is
  `(2DM/ω_c)(a − v/(2M))²`).
* `Params3.uphill_rate`: along the uphill feedback `σ_P u = 2Dω` (`v = 0`),
  `dF(ẋ) = D ω² + (M/ω_c) a²`, `a = (P_ref − P_f + D ω)/M`.
* `Params3.uphillEnergy_sub_eq` (energy balance `F(φ(T)) − F(φ(0)) = D∫ω² + (M/ω_c)∫a²`
  along an uphill path), `Params3.controlAction_uphill`, `Params3.setPointQP_le_uphill`: an
  admissible uphill pair
  `(φ, u)` on `[0, T]` has the action `(2D/σ_P²)(F(φ(T)) − F(φ(0)) − (M/ω_c)∫₀ᵀ a²)`, which
  bounds the quasi-potential from `φ(0)` to `φ(T)`.
-/

noncomputable section
namespace powerlib.GFM.Noise

open Real Set
open scoped ENNReal
open powerlib.Stochastic.LDP

local notation "π₃" i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i

namespace Params3

variable (p : Params3)

/-- The uphill energy `F = M ω²/2 + U(δ) + ω (P_ref − P_f)/ω_c + D ω²/(2 ω_c)`. -/
def uphillEnergy (x : Fin 3 → ℝ) : ℝ :=
  p.M * x 1 ^ 2 / 2 + p.potential (x 0 - p.α) + x 1 * (p.Pref - x 2) / p.ωc +
    p.D * x 1 ^ 2 / (2 * p.ωc)

/-- Its derivative. -/
def uphillEnergyDeriv (x : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  p.potentialDeriv (x 0 - p.α) • (π₃ 0) +
    (p.M * x 1 + (p.Pref - x 2) / p.ωc + p.D * x 1 / p.ωc) • (π₃ 1) + (-(x 1 / p.ωc)) • (π₃ 2)

@[tmio M, powerlib_domain] theorem hasFDerivAt_uphillEnergy (x : Fin 3 → ℝ) :
    HasFDerivAt p.uphillEnergy (p.uphillEnergyDeriv x) x := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 0 x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 1 x
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 2 x
  have hU := (p.hasDerivAt_potential (x 0 - p.α)).comp_hasFDerivAt x (h0.sub_const p.α)
  have hK := (h1.pow 2).const_mul (p.M / 2 + p.D / (2 * p.ωc))
  have hC := (h1.mul (h2.const_sub p.Pref)).const_mul (1 / p.ωc)
  have h := (hK.add hU).add hC
  have hf : p.uphillEnergy = fun y => ((p.M / 2 + p.D / (2 * p.ωc)) * y 1 ^ 2 +
      (p.potential ∘ fun y => y 0 - p.α) y) + 1 / p.ωc * (y 1 * (p.Pref - y 2)) := by
    funext y; simp only [uphillEnergy, Function.comp]; ring
  rw [hf]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  have hω := p.ωc_pos.ne'
  simp [uphillEnergyDeriv]
  field_simp
  ring

/-- At a rest point `(δ, 0, P_f)` the uphill energy is the potential: `F = U(δ)`. -/
@[tmio M, powerlib_domain] theorem uphillEnergy_rest (δ z : ℝ) :
    p.uphillEnergy ![δ, 0, z] = p.potential (δ - p.α) := by
  simp [uphillEnergy]

/-- The controlled three-state field in coordinates. -/
@[tmio M, powerlib_domain] theorem controlField_setPoint (σP v : ℝ) (x : Fin 3 → ℝ) :
    controlField p.sdeDrift (fun _ (_ : Fin 1) => p.setPointColumn σP) x ![v] =
      ![x 1, (p.Pref - x 2 - p.D * x 1) / p.M + v * (σP / p.M),
        p.ωc * (p.c0 + p.A * Real.sin (x 0 - p.α) - x 2)] := by
  ext i; fin_cases i <;>
    simp [controlField, sdeDrift_apply, setPointColumn, VSMLPFLossy.Pe, toLossy]

/-- **Exact action identity** (every state `x`, every control value `u`): with `W = σ_P u`,
`v = W − 2Dω` and `a = (P_ref − P_f − Dω)/M + σ_P u/M` (the frequency row of the controlled
field), `½ W² = 2D dF(x)(ẋ) + ½ v² + (2D/ω_c) a v − (2DM/ω_c) a²`. -/
@[tmio M, powerlib_domain] theorem action_identity (σP u : ℝ) (x : Fin 3 → ℝ) :
    1 / 2 * (σP * u) ^ 2 = 2 * p.D * p.uphillEnergyDeriv x
        (controlField p.sdeDrift (fun _ (_ : Fin 1) => p.setPointColumn σP) x ![u]) +
      1 / 2 * (σP * u - 2 * p.D * x 1) ^ 2 +
      2 * p.D / p.ωc * ((p.Pref - x 2 - p.D * x 1) / p.M + u * (σP / p.M)) *
        (σP * u - 2 * p.D * x 1) -
      2 * p.D * p.M / p.ωc * ((p.Pref - x 2 - p.D * x 1) / p.M + u * (σP / p.M)) ^ 2 := by
  have hM := p.M_pos.ne'
  have hω := p.ωc_pos.ne'
  rw [controlField_setPoint]
  simp [uphillEnergyDeriv, Params.potentialDeriv, Params.toSM]
  field_simp
  ring

/-- **Energy bound for every control value**: `½ W² ≤ 2D dF(x)(ẋ) + ½ (1 + D/(M ω_c)) v²`
(`v = W − 2Dω`); the gap is `(2DM/ω_c)(a − v/(2M))²` (`Params3.action_identity`). -/
@[tmio M, powerlib_domain] theorem action_le_energy (σP u : ℝ) (x : Fin 3 → ℝ) :
    1 / 2 * (σP * u) ^ 2 ≤ 2 * p.D * p.uphillEnergyDeriv x
        (controlField p.sdeDrift (fun _ (_ : Fin 1) => p.setPointColumn σP) x ![u]) +
      1 / 2 * (1 + p.D / (p.M * p.ωc)) * (σP * u - 2 * p.D * x 1) ^ 2 := by
  have hM := p.M_pos
  have hω := p.ωc_pos
  have hD := p.D_nonneg
  rw [p.action_identity σP u x]
  set a := (p.Pref - x 2 - p.D * x 1) / p.M + u * (σP / p.M)
  set v := σP * u - 2 * p.D * x 1
  have key : 1 / 2 * (1 + p.D / (p.M * p.ωc)) * v ^ 2 - (1 / 2 * v ^ 2 +
      2 * p.D / p.ωc * a * v - 2 * p.D * p.M / p.ωc * a ^ 2) =
      2 * p.D * p.M / p.ωc * (a - v / (2 * p.M)) ^ 2 := by
    field_simp; ring
  have : 0 ≤ 2 * p.D * p.M / p.ωc * (a - v / (2 * p.M)) ^ 2 := by positivity
  linarith

/-- The frequency row of the uphill field: `a = (P_ref − P_f + D ω)/M`. -/
def uphillAcc (x : Fin 3 → ℝ) : ℝ := (p.Pref - x 2 + p.D * x 1) / p.M

/-- **Growth rate along the uphill feedback** (`σ_P ≠ 0`, `σ_P u = 2Dω`):
`dF(x)(ẋ) = D ω² + (M/ω_c) a²`, `a = Params3.uphillAcc x` (`Params3.action_identity` with
`v = 0`). -/
@[tmio M, powerlib_domain] theorem uphill_rate {σP : ℝ} (hσ : σP ≠ 0) (hD : 0 < p.D)
    (x : Fin 3 → ℝ) :
    p.uphillEnergyDeriv x (controlField p.sdeDrift (fun _ (_ : Fin 1) => p.setPointColumn σP) x
        ![2 * p.D * x 1 / σP]) = p.D * x 1 ^ 2 + p.M / p.ωc * p.uphillAcc x ^ 2 := by
  have h := p.action_identity σP (2 * p.D * x 1 / σP) x
  have e1 : σP * (2 * p.D * x 1 / σP) = 2 * p.D * x 1 := by field_simp
  have e2 : (p.Pref - x 2 - p.D * x 1) / p.M + 2 * p.D * x 1 / σP * (σP / p.M) =
      p.uphillAcc x := by
    have hM := p.M_pos.ne'
    simp only [uphillAcc]; field_simp; ring
  rw [e1, e2, sub_self] at h
  have h2 : 2 * p.D * (p.uphillEnergyDeriv x (controlField p.sdeDrift
      (fun _ (_ : Fin 1) => p.setPointColumn σP) x ![2 * p.D * x 1 / σP]) -
      (p.D * x 1 ^ 2 + p.M / p.ωc * p.uphillAcc x ^ 2)) = 0 := by
    have hω := p.ωc_pos.ne'
    field_simp at h ⊢
    linear_combination (-1 / 2 : ℝ) * h
  have := (mul_eq_zero.mp h2).resolve_left (by positivity)
  linarith

/-- **Energy balance along an uphill pair** (`σ_P ≠ 0`, `D > 0`): for a path `φ` on `[0, T]`
following the uphill feedback `σ_P u = 2Dω`,
`F(φ(T)) − F(φ(0)) = D ∫₀ᵀ ω² + (M/ω_c) ∫₀ᵀ a²` (`Params3.uphill_rate`). -/
@[tmio M, powerlib_domain] theorem uphillEnergy_sub_eq {σP : ℝ} (hσ : σP ≠ 0) (hD : 0 < p.D)
    {T : ℝ} (hT : 0 ≤ T) {φ : ℝ → Fin 3 → ℝ} (hc : ContinuousOn φ (Icc 0 T))
    (hφ : ∀ t ∈ Ico 0 T, HasDerivWithinAt φ (controlField p.sdeDrift
      (fun _ (_ : Fin 1) => p.setPointColumn σP) (φ t) ![2 * p.D * φ t 1 / σP]) (Ici t) t) :
    p.uphillEnergy (φ T) - p.uphillEnergy (φ 0) = p.D * (∫ t in (0 : ℝ)..T, φ t 1 ^ 2) +
      p.M / p.ωc * ∫ t in (0 : ℝ)..T, p.uphillAcc (φ t) ^ 2 := by
  have hc1 : ContinuousOn (fun t => φ t 1) (Icc 0 T) := (continuous_apply 1).comp_continuousOn hc
  have hca : ContinuousOn (fun t => p.uphillAcc (φ t)) (Icc 0 T) := by
    have h2 : ContinuousOn (fun t => φ t 2) (Icc 0 T) := (continuous_apply 2).comp_continuousOn hc
    simp only [uphillAcc]
    exact ((continuousOn_const.sub h2).add (continuousOn_const.mul hc1)).div_const _
  have hEc : ContinuousOn (fun t => p.uphillEnergy (φ t)) (Icc 0 T) := fun t ht =>
    (p.hasFDerivAt_uphillEnergy (φ t)).continuousAt.comp_continuousWithinAt (hc t ht)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT hEc
    (f' := fun t => p.D * φ t 1 ^ 2 + p.M / p.ωc * p.uphillAcc (φ t) ^ 2)
    (fun t ht => by
      have hd := ((p.hasFDerivAt_uphillEnergy (φ t)).comp_hasDerivWithinAt t
        (hφ t ⟨ht.1.le, ht.2⟩)).mono Ioi_subset_Ici_self
      rwa [p.uphill_rate hσ hD] at hd)
    (((continuousOn_const.mul (hc1.pow 2)).add (continuousOn_const.mul (hca.pow 2))
      ).intervalIntegrable_of_Icc hT)
  have i1 : IntervalIntegrable (fun t => φ t 1 ^ 2) MeasureTheory.volume 0 T :=
    (hc1.pow 2).intervalIntegrable_of_Icc hT
  have i2 : IntervalIntegrable (fun t => p.uphillAcc (φ t) ^ 2) MeasureTheory.volume 0 T :=
    (hca.pow 2).intervalIntegrable_of_Icc hT
  rw [intervalIntegral.integral_add (i1.const_mul _) (i2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hFTC
  exact hFTC.symm

/-- **Action of an uphill pair** (`σ_P ≠ 0`, `D > 0`): an admissible pair `(φ, u)` on `[0, T]`
with the uphill feedback `σ_P u = 2Dω` has the action
`S_T(u) = (2D/σ_P²)(F(φ(T)) − F(φ(0)) − (M/ω_c)∫₀ᵀ a²)`, `a = Params3.uphillAcc`
(`Params3.uphillEnergy_sub_eq`). -/
@[tmio M, powerlib_domain] theorem controlAction_uphill {σP : ℝ} (hσ : σP ≠ 0) (hD : 0 < p.D)
    {T : ℝ} (hT : 0 ≤ T) {φ : ℝ → Fin 3 → ℝ} (hc : ContinuousOn φ (Icc 0 T))
    (hφ : ∀ t ∈ Ico 0 T, HasDerivWithinAt φ (controlField p.sdeDrift
      (fun _ (_ : Fin 1) => p.setPointColumn σP) (φ t) ![2 * p.D * φ t 1 / σP]) (Ici t) t) :
    controlAction (fun t => ![2 * p.D * φ t 1 / σP]) T =
      2 * p.D / σP ^ 2 * (p.uphillEnergy (φ T) - p.uphillEnergy (φ 0) -
        p.M / p.ωc * ∫ t in (0 : ℝ)..T, p.uphillAcc (φ t) ^ 2) := by
  have hS : controlAction (fun t => ![2 * p.D * φ t 1 / σP]) T =
      2 * p.D ^ 2 / σP ^ 2 * ∫ t in (0 : ℝ)..T, φ t 1 ^ 2 := by
    simp only [controlAction, Fin.sum_univ_one, Matrix.cons_val_zero]
    have e : (fun t => (2 * p.D * φ t 1 / σP) ^ 2) = fun t => 4 * p.D ^ 2 / σP ^ 2 * φ t 1 ^ 2 := by
      funext t; field_simp; ring
    rw [e, intervalIntegral.integral_const_mul]; ring
  rw [hS, p.uphillEnergy_sub_eq hσ hD hT hc hφ]
  field_simp
  ring

/-- **Quasi-potential along an uphill pair**: `V₃(φ(0), φ(T)) ≤
(2D/σ_P²)(F(φ(T)) − F(φ(0)) − (M/ω_c)∫₀ᵀ a²)` (`Params3.controlAction_uphill`). -/
@[tmio M, powerlib_domain] theorem setPointQP_le_uphill {σP : ℝ} (hσ : σP ≠ 0) (hD : 0 < p.D)
    {T : ℝ} (hT : 0 ≤ T) {φ : ℝ → Fin 3 → ℝ} (hc : ContinuousOn φ (Icc 0 T))
    (hφ : ∀ t ∈ Ico 0 T, HasDerivWithinAt φ (controlField p.sdeDrift
      (fun _ (_ : Fin 1) => p.setPointColumn σP) (φ t) ![2 * p.D * φ t 1 / σP]) (Ici t) t) :
    p.setPointQP σP (φ 0) (φ T) ≤ ENNReal.ofReal (2 * p.D / σP ^ 2 *
      (p.uphillEnergy (φ T) - p.uphillEnergy (φ 0) -
        p.M / p.ωc * ∫ t in (0 : ℝ)..T, p.uphillAcc (φ t) ^ 2)) := by
  have hc1 : ContinuousOn (fun t => φ t 1) (Icc 0 T) := (continuous_apply 1).comp_continuousOn hc
  have hu : IntervalIntegrable (fun t => ∑ j, (![2 * p.D * φ t 1 / σP] : Fin 1 → ℝ) j ^ 2)
      MeasureTheory.volume 0 T := by
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
    exact ((continuousOn_const.mul hc1).div_const _).pow 2 |>.intervalIntegrable_of_Icc hT
  rw [← p.controlAction_uphill hσ hD hT hc hφ]
  exact controlQuasiPotential_le hT rfl rfl hc hφ hu

end Params3

end powerlib.GFM.Noise
