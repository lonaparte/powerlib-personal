import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.MomentumNoise
import theorem.Stochastic.FilterNoise
import theorem.GridTiedConverter.GFM.Noise.FreidlinWentzell

/-! # The Freidlin–Wentzell quasi-potential of the noisy GFM equals the escape exponent

Domain module: for the two-state and three-state GFM models with set-point noise
(`theorem/GridTiedConverter/GFM/Noise/FreidlinWentzell.lean`), the quasi-potential of the
large-deviation rate, `inf_T inf {J_T(φ) : φ(T) = x}` from `x_A`, equals the controlled
quasi-potential of `theorem/GridTiedConverter/GFM/Noise/FilterQuasiPotential.lean`
(`Params.swingQP`, `Params3.setPointQP`) for every pair of endpoints and every filter bandwidth
`ω_c > 0`. The rate admits square-integrable set-point disturbances, the controlled
quasi-potential only those along which the path has a right derivative everywhere; the
regularisation keeping the endpoints is `Stochastic.LDP.fwQP_eq_controlQuasiPotential_planar`
(two states: the swing `δ̇ = p/M`, `ṗ = … + σ_P u` is flat, the endpoints are two moments of `ṗ`)
and `Stochastic.LDP.fwQP_eq_controlQuasiPotential_filter` (three states: the filtered power
endpoint is corrected by the intermediate value theorem along a bump perturbation of the angle).

Model boundary.
* The models and parameters of `FreidlinWentzell.lean` (export-positive `P(δ) = c₀ + A sin(δ − α)`,
  per unit, `M, ω_c > 0`, `D ≥ 0`, set-point noise `σ_P ≠ 0`); deterministic variational
  statements on the rate. The noise is degenerate (one column); no ellipticity is used.

Source: M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 4 §1–3 (the quasi-potential of the action functional).

Results.
* `Params.fwQP_eq_swingQP`: two states, `V_FW(x_A, x) = V₂(x_A, x)` for all endpoints.
* `Params3.fwQP_eq_setPointQP`: three states, `V_FW,3(x_A, x) = V₃(x_A, x)` for all endpoints and
  every `ω_c > 0`.
-/

noncomputable section
namespace powerlib.GFM.Noise

open MeasureTheory Set
open scoped ENNReal NNReal
open powerlib.Stochastic.LDP

namespace Params

variable (p : Params)

/-- **Two states: the quasi-potential of the rate is the escape exponent**, for all endpoints:
`inf_T inf {J_T(φ) : φ(T) = x} = V₂(x_A, x)` (`Params.swingQP`). -/
@[tmio M, powerlib_domain] theorem fwQP_eq_swingQP {σP : ℝ} (hσ : σP ≠ 0) (xA x : Fin 2 → ℝ) :
    ⨅ (T : ℝ≥0) (φ : C(Icc (0 : ℝ) T, Fin 2 → ℝ))
        (_ : φ ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩ = x),
        fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) xA T φ = p.swingQP σP xA x := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  have hb0 : ∀ y, p.swingDrift y 0 = 1 / p.M * y 1 := fun y => by
    rw [swingDrift_apply]; simp; ring
  exact fwQP_eq_controlQuasiPotential_planar hK hb0 hσ xA x

end Params

namespace Params3

variable (p : Params3)

/-- **Three states: the quasi-potential of the rate is the escape exponent**, for all endpoints
and every filter bandwidth: `inf_T inf {J_T(φ) : φ(T) = x} = V₃(x_A, x)` (`Params3.setPointQP`). -/
@[tmio M, powerlib_domain] theorem fwQP_eq_setPointQP {σP : ℝ} (hσ : σP ≠ 0)
    (xA x : Fin 3 → ℝ) :
    ⨅ (T : ℝ≥0) (φ : C(Icc (0 : ℝ) T, Fin 3 → ℝ))
        (_ : φ ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩ = x),
        fwRate p.sdeDrift (fun _ : Fin 1 => p.setPointColumn σP) xA T φ =
      p.setPointQP σP xA x := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_sdeDrift
  have hb0 : ∀ y, p.sdeDrift y 0 = y 1 := fun y => by rw [sdeDrift_apply]; simp
  have hb2 : ∀ y, p.sdeDrift y 2 = p.ωc * (p.c0 + p.A * Real.sin (y 0 - p.α) - y 2) :=
    fun y => by rw [sdeDrift_apply]; simp [VSMLPFLossy.Pe, toLossy]
  have hσ' : σP / p.M ≠ 0 := div_ne_zero hσ p.M_pos.ne'
  exact fwQP_eq_controlQuasiPotential_filter hK hb0 hb2 hσ' xA x

end Params3

end powerlib.GFM.Noise
