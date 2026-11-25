import dependencies.Mathlib
import theorem.Attributes
import theorem.GridTiedConverter.GFM.Noise.FreidlinWentzell
import theorem.GridTiedConverter.GFM.Noise.EscapeExponent

/-! # The Freidlin–Wentzell escape exponent of the noisy GFM at the saddle

Domain module: the quasi-potential of the large-deviation rate of the set-point noise models
(`GFM.Noise.Params.isLDP_setPoint`, `GFM.Noise.Params3.isLDP_setPoint`), i.e. the infimum of the
rate `J_T(φ)` over `T` and over paths from the stable equilibrium to the saddle, compared with the
escape exponents of `theorem/GridTiedConverter/GFM/Noise/EscapeExponent.lean`.

Model boundary.
* The two-state and three-state models of
  `theorem/GridTiedConverter/GFM/Noise/FreidlinWentzell.lean` (export-positive
  `P(δ) = c₀ + A sin(δ − α)`, per unit, set-point noise `σ_P ≠ 0`), with `D > 0` and
  `c₀ ≤ P_ref < c₀ + A`: stable equilibrium `δ_s = arcsin s + α`, saddle
  `δ_u = π − arcsin s + α`, `s = (P_ref − c₀)/A`.
* Deterministic variational statements on the rate. For the exit time only upper bounds are
  proved: by the sup–inf of the rate over a compact set
  (`theorem/GridTiedConverter/GFM/Noise/FreidlinWentzellExit.lean`) and, from the two-state
  potential well below the level `H(x_u) − η`, by `2D(ΔU − η)/σ_P²`, which tends to this saddle
  value as `η → 0` (`theorem/GridTiedConverter/GFM/Noise/FreidlinWentzellWell.lean`); the law
  `ε log E τ → V` is not formalized.

Source: M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 4 (the quasi-potential of the action functional is the escape exponent); the upper bounds
`GFM.Noise.Params.swingQP_saddle_eq`, `GFM.Noise.Params.tendsto_setPointQP` and the
verification theorem `Stochastic.LDP.le_fwQP_of_hj`.

Results.
* `Params.fwQP_saddle_eq`: two states, the quasi-potential of the rate from the stable
  equilibrium to the saddle equals `2D (U(δ_u) − U(δ_s))/σ_P²`, the value of the escape exponent
  `V₂` (`Params.swingQP_saddle_eq`).
* `Params.tendsto_fwQP3`: three states, the quasi-potential of the rate tends to the same value as
  `ω_c → ∞` (squeezed between `2(D − A/ω_c)ΔU/σ_P²` and `V₃`).
* For all endpoints and every `ω_c` the quasi-potential of the rate equals `V₂` / `V₃`:
  `theorem/GridTiedConverter/GFM/Noise/FreidlinWentzellExact.lean`.
-/

noncomputable section
namespace powerlib.GFM.Noise

open MeasureTheory Set Filter Topology Real
open scoped ENNReal NNReal
open powerlib.Stochastic.LDP

namespace Params

variable (p : Params)

/-- **Two-state escape exponent of the rate**: from the stable equilibrium to the saddle,
`inf_T inf {J_T(φ) : φ(T) = (δ_u, 0)} = 2D (U(δ_u) − U(δ_s))/σ_P²` (the value of `V₂`,
`Params.swingQP_saddle_eq`, met by the Hamilton–Jacobi lower bound `Params.fwQP_rest_ge`). -/
@[tmio M, powerlib_domain] theorem fwQP_saddle_eq {σP : ℝ} (hσ : σP ≠ 0) (hD : 0 < p.D)
    (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) :
    ⨅ (T : ℝ≥0) (φ : C(Icc (0 : ℝ) T, Fin 2 → ℝ))
        (_ : φ ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩ =
          ![π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0]),
        fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP)
          ![Real.arcsin ((p.Pref - p.c0) / p.A) + p.α, 0] T φ =
      ENNReal.ofReal (2 * p.D * (p.potential (π - Real.arcsin ((p.Pref - p.c0) / p.A)) -
        p.potential (Real.arcsin ((p.Pref - p.c0) / p.A))) / σP ^ 2) := by
  refine le_antisymm ((p.fwQP_le_swingQP hσ _ _).trans (p.swingQP_saddle_eq hσ hD h0 h1).le) ?_
  have h := p.fwQP_rest_ge hσ (Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)
    (π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)
  simp only [add_sub_cancel_right] at h
  exact h

/-- **Three-state escape exponent of the rate, fast-filter limit**: as `ω_c → ∞` the
quasi-potential of the three-state rate from the stable equilibrium to the saddle tends to the
two-state value `2D (U(δ_u) − U(δ_s))/σ_P²`. -/
@[tmio M, powerlib_domain] theorem tendsto_fwQP3 {σP : ℝ} (hσ : σP ≠ 0) (hD : 0 < p.D)
    (h0 : p.c0 ≤ p.Pref) (h1 : p.Pref < p.c0 + p.A) {δs δu : ℝ}
    (hδs : δs = Real.arcsin ((p.Pref - p.c0) / p.A) + p.α)
    (hδu : δu = π - Real.arcsin ((p.Pref - p.c0) / p.A) + p.α) :
    Tendsto (fun ωc : Ioi (0 : ℝ) =>
        ⨅ (T : ℝ≥0) (φ : C(Icc (0 : ℝ) T, Fin 3 → ℝ))
          (_ : φ ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩ =
            ![δu, 0, p.c0 + p.A * Real.sin (δu - p.α)]),
          fwRate (⟨p, ωc, mem_Ioi.mp ωc.2⟩ : Params3).sdeDrift
            (fun _ : Fin 1 => (⟨p, ωc, mem_Ioi.mp ωc.2⟩ : Params3).setPointColumn σP)
            ![δs, 0, p.c0 + p.A * Real.sin (δs - p.α)] T φ)
      atTop (𝓝 (ENNReal.ofReal
        (2 * p.D * (p.potential (δu - p.α) - p.potential (δs - p.α)) / σP ^ 2))) := by
  set ΔU := p.potential (δu - p.α) - p.potential (δs - p.α) with hΔU
  have hup := p.tendsto_setPointQP hσ hD h0 h1 hδs hδu
  -- lower comparison function
  have hω : Tendsto (fun ωc : Ioi (0 : ℝ) => (ωc : ℝ)) atTop atTop :=
    tendsto_Ioi_atTop.mp tendsto_id
  have hlow : Tendsto (fun ωc : Ioi (0 : ℝ) =>
      ENNReal.ofReal (2 * (p.D - p.A / ωc) * ΔU / σP ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (2 * p.D * ΔU / σP ^ 2))) := by
    refine ENNReal.tendsto_ofReal ?_
    have hA : Tendsto (fun ωc : Ioi (0 : ℝ) => p.A / ωc) atTop (𝓝 0) :=
      (tendsto_const_nhds.div_atTop hω)
    have h1 : Tendsto (fun ωc : Ioi (0 : ℝ) => p.D - p.A / ωc) atTop (𝓝 (p.D - 0)) :=
      tendsto_const_nhds.sub hA
    have h2 := ((h1.const_mul 2).mul_const ΔU).div_const (σP ^ 2)
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · -- `V_FW ≥ 2(D − A/ω_c) ΔU/σ_P²` once `A ≤ D ω_c`
    have hev : ∀ᶠ ωc : Ioi (0 : ℝ) in atTop, p.A / p.D ≤ (ωc : ℝ) :=
      hω.eventually (eventually_ge_atTop _)
    filter_upwards [hev] with ωc hωc
    have hA : (⟨p, ωc, mem_Ioi.mp ωc.2⟩ : Params3).A ≤
        (⟨p, ωc, mem_Ioi.mp ωc.2⟩ : Params3).D * (⟨p, ωc, mem_Ioi.mp ωc.2⟩ : Params3).ωc := by
      show p.A ≤ p.D * ωc
      rw [div_le_iff₀ hD] at hωc; linarith
    have h := (⟨p, ωc, mem_Ioi.mp ωc.2⟩ : Params3).fwQP_rest_ge hσ hA δs δu
    have e : ∀ δ, (⟨p, ωc, mem_Ioi.mp ωc.2⟩ : Params3).toLossy.Pe δ =
        p.c0 + p.A * Real.sin (δ - p.α) := fun δ => rfl
    simp only [e] at h
    exact h
  · exact Eventually.of_forall fun ωc => (Params3.fwQP_le_setPointQP _ hσ _ _)

end Params

end powerlib.GFM.Noise
