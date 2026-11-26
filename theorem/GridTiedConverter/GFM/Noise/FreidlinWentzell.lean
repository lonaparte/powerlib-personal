import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.AdditiveNoise
import theorem.Stochastic.SchilderPolygonal
import theorem.Stochastic.AdditiveVerification
import theorem.Stochastic.Schilder
import theorem.GridTiedConverter.GFM.Noise.FilterQuasiPotential

/-! # Freidlin–Wentzell large deviations of the noisy GFM with set-point noise

Domain module: the two-state and three-state GFM models of
`theorem/GridTiedConverter/GFM/Noise/FilterQuasiPotential.lean` driven by set-point noise
`ΔP = √ε σ_P Ẇ` solved path by path (the noise enters one row additively), and the transport of
a large-deviation principle of the noise `√ε W` to the solutions, with the rate identified as the
controlled action of `theorem/Stochastic/ControlledAction.lean`.

Model boundary.
* Two-state: state `(δ, p)` on `Fin 2 → ℝ` (`p = M Δω`), drift `Params.swingDrift`
  (`δ̇ = p/M`, `ṗ = P_ref − c₀ − A sin(δ − α) − D p/M`), noise column `(0, σ_P)`.
  Three-state: state `(δ, ω, P_f)` on `Fin 3 → ℝ`, drift `Params3.sdeDrift` (VSM + power filter,
  `Ṗ_f = ω_c (P(δ) − P_f)`), noise column `(0, σ_P/M, 0)`. Voltage source behind a lossy
  quasi-static line, export-positive power `P(δ) = c₀ + A sin(δ − α)`, per unit; `M, ω_c > 0`,
  `D ≥ 0`, `σ_P ≠ 0`. Only the power set-point channel (grid-frequency and voltage channels
  excluded).
* The stochastic model is the integral equation `x(t) = x₀ + √ε σ_P W(t) e + ∫₀ᵗ b(x)` on
  `[0, T]` (`e` the noise row), solved for every continuous driving path (`Stochastic.LDP.solMap`);
  for a Brownian path this is the solution of `dx = b(x) dt + √ε σ dW` (no Itô integral is needed
  for additive noise).
* The noise: `B` a Brownian motion (Mathlib's `IsBrownianReal`) and `X` a measurable path-space
  version of it on `[0, T]` (`Stochastic.LDP.exists_version`); Schilder's theorem for `√ε X` is
  `Stochastic.LDP.isLDP_schilder`.
* The exit-time asymptotics (`ε log E τ → V`): proved elsewhere are the principle uniform over
  compact sets of initial points, the exit exponent through an energy level and the upper bound
  `limsup ε log E τ_ε ≤ sup_{x ∈ K} inf_{φ leaves K} J_x^T(φ)` for the mean exit time from a
  compact set (`theorem/GridTiedConverter/GFM/Noise/FreidlinWentzellExit.lean`), the flow
  property (`theorem/Stochastic/SolutionFlow.lean`) and the Markov property at deterministic
  times (`theorem/Stochastic/AdditiveMarkov.lean`); for the two-state potential well below the
  level `H(x_u) − η` the bound is the boundary-level value `2D(ΔU − η)/σ_P²`, which also bounds
  the exit before a fixed time
  (`theorem/GridTiedConverter/GFM/Noise/FreidlinWentzellWell.lean`); the matching lower bound
  (`theorem/GridTiedConverter/GFM/Noise/FreidlinWentzellLower.lean`), the three-state lower bound
  (`theorem/GridTiedConverter/GFM/Noise/FreidlinWentzellFilter.lean`) and the exit place of a cut
  well (`theorem/GridTiedConverter/GFM/Noise/FreidlinWentzellPlace.lean`); missing: the exit
  from the basin of attraction and the law of `τ_ε/E τ_ε`.

Source: M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 3 §1–2 (additive noise; the action functional `½∫|u|²` of the controlled skeleton) and Ch. 4
(quasi-potential); A. Dembo, O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed.
(1998), Thm 4.2.1 (contraction principle), Thm 5.2.3 (Schilder), Thm 5.6.3 (Freidlin–Wentzell
for diffusions); GFM counterpart study, note t2-noise item 7 (escape exponent of the set-point
noise models; scratch notes outside the repository).

Results.
* `Params.lipschitzWith_swingDrift`, `Params3.lipschitzWith_sdeDrift`: the drifts are globally
  Lipschitz (so `solMap` is the unique, continuous solution map); `Params.leftInverse_swing`,
  `Params3.leftInverse_setPoint`: the noise row is recovered linearly from the noise column.
* `Params.solMap_setPoint_apply`, `Params3.solMap_setPoint_apply`: the solution of the noisy model
  in coordinates (`x(t) = x₀ + σ_P w(t) e + ∫₀ᵗ b(x)`), for every continuous `w`.
* `Params.isLDP_setPoint`, `Params3.isLDP_setPoint` (**Freidlin–Wentzell**): the laws of the
  solutions `solMap(√ε X)` satisfy the large-deviation principle as `ε → 0⁺` with the rate
  `fwRate` (`pushRate` of the Schilder rate through the solution map).
* `Params.fwRate_setPoint_eq`, `Params3.fwRate_setPoint_eq`: on every admissible pair `(φ, u)` of
  the quasi-potential `Params.swingQP` / `Params3.setPointQP` (the controlled model with
  `ΔP = σ_P u`, `GFM.Noise.Params.noisyField_setPoint`), the rate equals the controlled action
  `½ ∫₀ᵀ u²`; `Params.fwQP_le_swingQP`, `Params3.fwQP_le_setPointQP`: the quasi-potential of the
  rate, `inf_T inf {J_T(φ) : φ(T) = x}`, is at most the escape exponent of
  `FilterQuasiPotential`; `Params.fwQP_ge`, `Params.fwQP_rest_ge`, `Params3.fwQP_ge`,
  `Params3.fwQP_rest_ge`: the Hamilton–Jacobi lower bounds `(2D/σ_P²)ΔH` and
  `(2(D − A/ω_c)/σ_P²)ΔE` for the rate's quasi-potential (verification theorem for absolutely
  continuous paths, `Stochastic.LDP.le_fwQP_of_hj`). At the saddle the two bounds meet:
  `theorem/GridTiedConverter/GFM/Noise/FreidlinWentzellSaddle.lean`; the quasi-potential of the
  rate equals the escape exponent for all endpoints:
  `theorem/GridTiedConverter/GFM/Noise/FreidlinWentzellExact.lean`.
* `Params.isLDP_setPoint_polygon`, `Params3.isLDP_setPoint_polygon` (**unconditional**): with the
  noise replaced by the polygonal interpolation of `√ε B` over `n` uniform steps of `[0, T]`
  (`B` a pre-Brownian motion), the solution laws satisfy the large-deviation principle, with the
  rate pushed from the Schilder rate on polygonal noise paths
  (`Stochastic.LDP.isLDP_polygon`).
-/

noncomputable section
namespace powerlib.GFM.Noise

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Classical
open powerlib.Stochastic.LDP

/-- Coordinate bound `|x i − y i| ≤ dist x y` on `Fin n → ℝ`. -/
@[tmio M, powerlib_domain] private theorem abs_sub_le_dist {n : ℕ} (x y : Fin n → ℝ) (i : Fin n) :
    |x i - y i| ≤ dist x y := by
  have := dist_le_pi_dist x y i
  rwa [Real.dist_eq] at this

namespace Params

variable (p : Params)

/-- **The two-state drift is globally Lipschitz** (sup norm). -/
@[tmio M, powerlib_domain] theorem lipschitzWith_swingDrift :
    ∃ K : ℝ≥0, LipschitzWith K p.swingDrift := by
  have hM := p.M_pos
  refine ⟨Real.toNNReal (1 / p.M + |p.A| + p.D / p.M), LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hK : 0 ≤ 1 / p.M + |p.A| + p.D / p.M := by
    have := p.D_nonneg; positivity
  rw [Real.coe_toNNReal _ hK]
  refine dist_pi_le_iff (by positivity) |>.mpr fun i => ?_
  have h0 := abs_sub_le_dist x y 0
  have h1 := abs_sub_le_dist x y 1
  have hd := dist_nonneg (x := x) (y := y)
  have hs := Real.abs_sin_sub_sin_le (x 0 - p.α) (y 0 - p.α)
  rw [sub_sub_sub_cancel_right] at hs
  rw [Real.dist_eq, swingDrift_apply, swingDrift_apply]
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    rw [← sub_div, abs_div, abs_of_pos hM, div_le_iff₀ hM]
    have : 0 ≤ (|p.A| + p.D / p.M) * dist x y * p.M := by
      have := p.D_nonneg; positivity
    have e : (1 / p.M + |p.A| + p.D / p.M) * dist x y * p.M =
        dist x y + (|p.A| + p.D / p.M) * dist x y * p.M := by
      field_simp
      ring
    linarith
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    have e : p.Pref - (p.c0 + p.A * Real.sin (x 0 - p.α)) - p.D * (x 1 / p.M) -
        (p.Pref - (p.c0 + p.A * Real.sin (y 0 - p.α)) - p.D * (y 1 / p.M)) =
        -(p.A * (Real.sin (x 0 - p.α) - Real.sin (y 0 - p.α))) - p.D / p.M * (x 1 - y 1) := by
      ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_neg, abs_mul, abs_mul, abs_div, abs_of_pos hM, abs_of_nonneg p.D_nonneg]
    have h2 : |p.A| * |Real.sin (x 0 - p.α) - Real.sin (y 0 - p.α)| ≤ |p.A| * dist x y :=
      mul_le_mul_of_nonneg_left (hs.trans h0) (abs_nonneg _)
    have h3 : p.D / p.M * |x 1 - y 1| ≤ p.D / p.M * dist x y :=
      mul_le_mul_of_nonneg_left h1 (div_nonneg p.D_nonneg hM.le)
    have : 0 ≤ 1 / p.M * dist x y := by positivity
    nlinarith

/-- The set-point row is recovered from the noise column `(0, σ_P)`: `L x = x₁/σ_P`. -/
@[tmio M, powerlib_domain] theorem leftInverse_swing {σP : ℝ} (hσ : σP ≠ 0) :
    ∃ L : (Fin 2 → ℝ) →L[ℝ] Fin 1 → ℝ,
      ∀ v, L (columnsCLM (fun _ : Fin 1 => swingColumn σP) v) = v := by
  refine ⟨ContinuousLinearMap.pi fun _ => σP⁻¹ • ContinuousLinearMap.proj 1, fun v => ?_⟩
  ext j
  fin_cases j
  simp [columnsCLM_apply, swingColumn]
  field_simp

/-- **The noisy two-state model, solved path by path**: for every continuous noise path `w`,
the solution is `x(t) = x₀ + (0, σ_P w(t)) + ∫₀ᵗ b(x)`. -/
@[tmio M, powerlib_domain] theorem solMap_setPoint_apply (σP : ℝ) (x₀ : Fin 2 → ℝ) {T : ℝ≥0}
    (w : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) (t : Icc (0 : ℝ) T) :
    solMap p.swingDrift (columnsCLM fun _ : Fin 1 => swingColumn σP) x₀ w t =
      x₀ + ![0, σP * w t 0] + ∫ s in (0 : ℝ)..t,
        p.swingDrift (pathExt (solMap p.swingDrift (columnsCLM fun _ : Fin 1 => swingColumn σP)
          x₀ w) s) := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  rw [solMap_spec hK]
  congr 2
  ext i
  fin_cases i <;> simp [columnsCLM_apply, swingColumn, mul_comm]

/-- **Freidlin–Wentzell for the two-state model** (set-point noise): for a Brownian motion `B`
and a measurable path-space version `X` of it on `[0, T]`, the laws of the solutions
`x^ε = solMap(√ε X)` of `dx = b(x) dt + √ε σ_P e₂ dB` satisfy the large-deviation principle as
`ε → 0⁺` with the rate `fwRate = pushRate solMap schilderRate` (Schilder's theorem
`Stochastic.LDP.isLDP_schilder` and the contraction principle). -/
@[tmio M, powerlib_domain] theorem isLDP_setPoint {σP : ℝ} (hσ : σP ≠ 0) (x₀ : Fin 2 → ℝ)
    {T : ℝ≥0} (hT : 0 < (T : ℝ)) [MeasurableSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)]
    [BorelSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)] [MeasurableSpace C(Icc (0 : ℝ) T, Fin 2 → ℝ)]
    [BorelSpace C(Icc (0 : ℝ) T, Fin 2 → ℝ)] {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {X : Ω → C(Icc (0 : ℝ) T, Fin 1 → ℝ)} (hX : Measurable X)
    (hXB : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T, X ω t 0 = B ⟨t, t.2.1⟩ ω) :
    IsLDP (𝓝[>] (0 : ℝ)) id (fun ε => P.map fun ω =>
        solMap p.swingDrift (columnsCLM fun _ : Fin 1 => swingColumn σP) x₀ (√ε • X ω))
      (fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) x₀ T) := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  obtain ⟨L, hL⟩ := leftInverse_swing hσ
  refine ((isLDP_schilder hB hT hX hXB).map_solMap hK hL x₀).congr
    (Eventually.of_forall fun ε => ?_)
  exact Measure.map_map (continuous_solMap hK _ x₀).measurable (by exact hX.const_smul (√ε))

/-- **The rate is the controlled action**: on every admissible pair `(φ, u)` of the two-state
quasi-potential `Params.swingQP` on `[0, T]` from `x₀`, `J(φ) = ½ ∫₀ᵀ u²`. -/
@[tmio M, powerlib_domain] theorem fwRate_setPoint_eq {σP : ℝ} (hσ : σP ≠ 0) {x₀ : Fin 2 → ℝ}
    {T : ℝ≥0} {φ : ℝ → Fin 2 → ℝ} {u : ℝ → Fin 1 → ℝ} (h0 : φ 0 = x₀)
    (hc : ContinuousOn φ (Icc 0 T))
    (hφ : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt φ
      (controlField p.swingDrift (fun _ (_ : Fin 1) => swingColumn σP) (φ t) (u t)) (Ici t) t)
    (hu2 : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) volume 0 T)
    {x : C(Icc (0 : ℝ) T, Fin 2 → ℝ)} (hx : ∀ t : Icc (0 : ℝ) T, x t = φ t) :
    fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) x₀ T x =
      ENNReal.ofReal (controlAction u T) := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  obtain ⟨L, hL⟩ := leftInverse_swing hσ
  exact fwRate_eq_controlAction hK _ hL h0 hc hφ
    (intervalIntegrable_of_admissible hK _ hL hc hφ hu2) hu2 hx

/-- **Quasi-potential of the rate, upper bound**: `inf_T inf {J_T(φ) : φ(T) = x}` from `x_A` is
at most the two-state escape exponent `V₂(x_A, x)` (`Params.swingQP`). -/
@[tmio M, powerlib_domain] theorem fwQP_le_swingQP {σP : ℝ} (hσ : σP ≠ 0) (xA x : Fin 2 → ℝ) :
    ⨅ (T : ℝ≥0) (φ : C(Icc (0 : ℝ) T, Fin 2 → ℝ))
        (_ : φ ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩ = x),
        fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) xA T φ ≤ p.swingQP σP xA x := by
  unfold swingQP controlQuasiPotential
  refine le_iInf fun T' => le_iInf fun φ => le_iInf fun u => le_iInf fun hadm => ?_
  obtain ⟨hT, h0, hTx, hc, hφ, hu⟩ := hadm
  let y : C(Icc (0 : ℝ) (⟨T', hT⟩ : ℝ≥0), Fin 2 → ℝ) := ⟨_, hc.domRestrict⟩
  refine iInf_le_of_le ⟨T', hT⟩ (iInf_le_of_le y (iInf_le_of_le hTx ?_))
  exact (p.fwRate_setPoint_eq (T := ⟨T', hT⟩) hσ h0 hc hφ hu fun t => rfl).le

/-- The derivative of the swing energy is continuous in the state. -/
@[tmio M, powerlib_domain] private theorem continuous_swingEnergyDeriv :
    Continuous p.swingEnergyDeriv := by
  unfold swingEnergyDeriv potentialDeriv
  fun_prop

/-- **Quasi-potential of the rate, lower bound** (two states, verification theorem for
absolutely continuous paths): `inf_T inf {J_T(φ) : φ(T) = x} ≥ (2D/σ_P²)(H(x) − H(x_A))`. -/
@[tmio M, powerlib_domain] theorem fwQP_ge {σP : ℝ} (hσ : σP ≠ 0) (xA x : Fin 2 → ℝ) :
    ENNReal.ofReal (2 * p.D / σP ^ 2 * (p.swingEnergy x - p.swingEnergy xA)) ≤
      ⨅ (T : ℝ≥0) (φ : C(Icc (0 : ℝ) T, Fin 2 → ℝ))
        (_ : φ ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩ = x),
        fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) xA T φ := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  have h := le_fwQP_of_hj hK (fun _ : Fin 1 => swingColumn σP)
    (W := fun y => 2 * p.D / σP ^ 2 * p.swingEnergy y)
    (fun y => (p.hasFDerivAt_swingEnergy y).const_mul _)
    (by exact p.continuous_swingEnergyDeriv.const_smul (2 * p.D / σP ^ 2))
    (fun y => (p.hj_swing hσ y).le) xA x
  rw [← mul_sub] at h
  exact h

/-- **Between rest points** (two states): the quasi-potential of the rate from `(δ_s, 0)` to
`(δ_u, 0)` is at least `2D (U(δ_u) − U(δ_s))/σ_P²`. -/
@[tmio M, powerlib_domain] theorem fwQP_rest_ge {σP : ℝ} (hσ : σP ≠ 0) (δs δu : ℝ) :
    ENNReal.ofReal (2 * p.D * (p.potential (δu - p.α) - p.potential (δs - p.α)) / σP ^ 2) ≤
      ⨅ (T : ℝ≥0) (φ : C(Icc (0 : ℝ) T, Fin 2 → ℝ))
        (_ : φ ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩ = ![δu, 0]),
        fwRate p.swingDrift (fun _ : Fin 1 => swingColumn σP) ![δs, 0] T φ := by
  convert p.fwQP_ge hσ ![δs, 0] ![δu, 0] using 2
  simp [swingEnergy]
  ring

/-- **Unconditional large deviations for polygonal set-point noise** (two states): driven by the
polygonal interpolation of `√ε B` over `n` uniform steps (`B` a pre-Brownian motion), the laws of
the solutions satisfy the large-deviation principle as `ε → 0⁺`, with the rate pushed from the
Schilder rate on polygonal noise paths (`Stochastic.LDP.isLDP_polygon`). -/
@[tmio M, powerlib_domain] theorem isLDP_setPoint_polygon {σP : ℝ} (hσ : σP ≠ 0)
    (x₀ : Fin 2 → ℝ) {T : ℝ≥0} (hT : 0 < (T : ℝ)) {n : ℕ} (hn : 0 < n)
    [MeasurableSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)] [BorelSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)]
    [MeasurableSpace C(Icc (0 : ℝ) T, Fin 2 → ℝ)] [BorelSpace C(Icc (0 : ℝ) T, Fin 2 → ℝ)]
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    IsLDP (𝓝[>] (0 : ℝ)) id
      (fun ε => (P.map fun ω => polyPath T n (polyNoise B T n ε ω)).map
        (solMap p.swingDrift (columnsCLM fun _ : Fin 1 => swingColumn σP) x₀))
      (pushRate (solMap p.swingDrift (columnsCLM fun _ : Fin 1 => swingColumn σP) x₀)
        fun w => if w ∈ range (polyPath T n) then schilderRate T w else ⊤) := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_swingDrift
  obtain ⟨L, hL⟩ := leftInverse_swing hσ
  exact (isLDP_polygon hB hT hn).map_solMap hK hL x₀

end Params

namespace Params3

variable (p : Params3)

/-- **The three-state drift is globally Lipschitz** (sup norm). -/
@[tmio M, powerlib_domain] theorem lipschitzWith_sdeDrift :
    ∃ K : ℝ≥0, LipschitzWith K p.sdeDrift := by
  have hM := p.M_pos
  have hω := p.ωc_pos
  have hD := p.D_nonneg
  set c : ℝ := 1 + (1 + p.D) / p.M + p.ωc * (|p.A| + 1) with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨Real.toNNReal c, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [Real.coe_toNNReal _ hc0]
  refine dist_pi_le_iff (by positivity) |>.mpr fun i => ?_
  have h0 := abs_sub_le_dist x y 0
  have h1 := abs_sub_le_dist x y 1
  have h2 := abs_sub_le_dist x y 2
  have hd := dist_nonneg (x := x) (y := y)
  have hs := Real.abs_sin_sub_sin_le (x 0 - p.α) (y 0 - p.α)
  rw [sub_sub_sub_cancel_right] at hs
  have hA : |p.A| * |Real.sin (x 0 - p.α) - Real.sin (y 0 - p.α)| ≤ |p.A| * dist x y :=
    mul_le_mul_of_nonneg_left (hs.trans h0) (abs_nonneg _)
  have hpos1 : 0 ≤ (1 + p.D) / p.M * dist x y := by positivity
  have hpos2 : 0 ≤ p.ωc * (|p.A| + 1) * dist x y := by positivity
  rw [Real.dist_eq, sdeDrift_apply, sdeDrift_apply]
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    nlinarith
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    have e : (p.Pref - x 2 - p.D * x 1) / p.M - (p.Pref - y 2 - p.D * y 1) / p.M =
        (-(x 2 - y 2) - p.D * (x 1 - y 1)) / p.M := by ring
    rw [e, abs_div, abs_of_pos hM, div_le_iff₀ hM]
    have h3 : |-(x 2 - y 2) - p.D * (x 1 - y 1)| ≤ (1 + p.D) * dist x y := by
      refine (abs_sub _ _).trans ?_
      rw [abs_neg, abs_mul, abs_of_nonneg hD]
      nlinarith
    have h4 : (1 + p.D) * dist x y = (1 + p.D) / p.M * dist x y * p.M := by
      field_simp
    have : 0 ≤ (1 + p.ωc * (|p.A| + 1)) * dist x y * p.M := by positivity
    nlinarith
  · simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    have e : p.ωc * (p.toLossy.Pe (x 0) - x 2) - p.ωc * (p.toLossy.Pe (y 0) - y 2) =
        p.ωc * (p.A * (Real.sin (x 0 - p.α) - Real.sin (y 0 - p.α)) - (x 2 - y 2)) := by
      simp only [VSMLPFLossy.Pe, toLossy]
      ring
    rw [e, abs_mul, abs_of_pos hω]
    have h3 : |p.A * (Real.sin (x 0 - p.α) - Real.sin (y 0 - p.α)) - (x 2 - y 2)| ≤
        (|p.A| + 1) * dist x y := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul]
      nlinarith
    have h4 : p.ωc * |p.A * (Real.sin (x 0 - p.α) - Real.sin (y 0 - p.α)) - (x 2 - y 2)| ≤
        p.ωc * ((|p.A| + 1) * dist x y) := mul_le_mul_of_nonneg_left h3 hω.le
    nlinarith

/-- The set-point row is recovered from the noise column `(0, σ_P/M, 0)`:
`L x = M x₁/σ_P`. -/
@[tmio M, powerlib_domain] theorem leftInverse_setPoint {σP : ℝ} (hσ : σP ≠ 0) :
    ∃ L : (Fin 3 → ℝ) →L[ℝ] Fin 1 → ℝ,
      ∀ v, L (columnsCLM (fun _ : Fin 1 => p.setPointColumn σP) v) = v := by
  have hM := p.M_pos.ne'
  refine ⟨ContinuousLinearMap.pi fun _ => (p.M / σP) • ContinuousLinearMap.proj 1,
    fun v => ?_⟩
  ext j
  fin_cases j
  simp [columnsCLM_apply, setPointColumn]
  field_simp

/-- **The noisy three-state model, solved path by path**: for every continuous noise path `w`,
the solution is `x(t) = x₀ + (0, σ_P w(t)/M, 0) + ∫₀ᵗ b(x)`. -/
@[tmio M, powerlib_domain] theorem solMap_setPoint_apply (σP : ℝ) (x₀ : Fin 3 → ℝ) {T : ℝ≥0}
    (w : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) (t : Icc (0 : ℝ) T) :
    solMap p.sdeDrift (columnsCLM fun _ : Fin 1 => p.setPointColumn σP) x₀ w t =
      x₀ + ![0, σP / p.M * w t 0, 0] + ∫ s in (0 : ℝ)..t,
        p.sdeDrift (pathExt (solMap p.sdeDrift
          (columnsCLM fun _ : Fin 1 => p.setPointColumn σP) x₀ w) s) := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_sdeDrift
  rw [solMap_spec hK]
  congr 2
  ext i
  fin_cases i <;> simp [columnsCLM_apply, setPointColumn, mul_comm]

/-- **Freidlin–Wentzell for the three-state model** (set-point noise): as
`Params.isLDP_setPoint`, for the VSM + power filter. -/
@[tmio M, powerlib_domain] theorem isLDP_setPoint {σP : ℝ} (hσ : σP ≠ 0) (x₀ : Fin 3 → ℝ)
    {T : ℝ≥0} (hT : 0 < (T : ℝ)) [MeasurableSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)]
    [BorelSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)] [MeasurableSpace C(Icc (0 : ℝ) T, Fin 3 → ℝ)]
    [BorelSpace C(Icc (0 : ℝ) T, Fin 3 → ℝ)] {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {X : Ω → C(Icc (0 : ℝ) T, Fin 1 → ℝ)} (hX : Measurable X)
    (hXB : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T, X ω t 0 = B ⟨t, t.2.1⟩ ω) :
    IsLDP (𝓝[>] (0 : ℝ)) id (fun ε => P.map fun ω =>
        solMap p.sdeDrift (columnsCLM fun _ : Fin 1 => p.setPointColumn σP) x₀ (√ε • X ω))
      (fwRate p.sdeDrift (fun _ : Fin 1 => p.setPointColumn σP) x₀ T) := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_sdeDrift
  obtain ⟨L, hL⟩ := p.leftInverse_setPoint hσ
  refine ((isLDP_schilder hB hT hX hXB).map_solMap hK hL x₀).congr
    (Eventually.of_forall fun ε => ?_)
  exact Measure.map_map (continuous_solMap hK _ x₀).measurable (by exact hX.const_smul (√ε))

/-- **The rate is the controlled action** on every admissible pair of `Params3.setPointQP`. -/
@[tmio M, powerlib_domain] theorem fwRate_setPoint_eq {σP : ℝ} (hσ : σP ≠ 0) {x₀ : Fin 3 → ℝ}
    {T : ℝ≥0} {φ : ℝ → Fin 3 → ℝ} {u : ℝ → Fin 1 → ℝ} (h0 : φ 0 = x₀)
    (hc : ContinuousOn φ (Icc 0 T))
    (hφ : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt φ
      (controlField p.sdeDrift (fun _ (_ : Fin 1) => p.setPointColumn σP) (φ t) (u t)) (Ici t) t)
    (hu2 : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) volume 0 T)
    {x : C(Icc (0 : ℝ) T, Fin 3 → ℝ)} (hx : ∀ t : Icc (0 : ℝ) T, x t = φ t) :
    fwRate p.sdeDrift (fun _ : Fin 1 => p.setPointColumn σP) x₀ T x =
      ENNReal.ofReal (controlAction u T) := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_sdeDrift
  obtain ⟨L, hL⟩ := p.leftInverse_setPoint hσ
  exact fwRate_eq_controlAction hK _ hL h0 hc hφ
    (intervalIntegrable_of_admissible hK _ hL hc hφ hu2) hu2 hx

/-- **Quasi-potential of the rate, upper bound** (three states): at most `V₃(x_A, x)`
(`Params3.setPointQP`). -/
@[tmio M, powerlib_domain] theorem fwQP_le_setPointQP {σP : ℝ} (hσ : σP ≠ 0)
    (xA x : Fin 3 → ℝ) :
    ⨅ (T : ℝ≥0) (φ : C(Icc (0 : ℝ) T, Fin 3 → ℝ))
        (_ : φ ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩ = x),
        fwRate p.sdeDrift (fun _ : Fin 1 => p.setPointColumn σP) xA T φ ≤
      p.setPointQP σP xA x := by
  unfold setPointQP controlQuasiPotential
  refine le_iInf fun T' => le_iInf fun φ => le_iInf fun u => le_iInf fun hadm => ?_
  obtain ⟨hT, h0, hTx, hc, hφ, hu⟩ := hadm
  let y : C(Icc (0 : ℝ) (⟨T', hT⟩ : ℝ≥0), Fin 3 → ℝ) := ⟨_, hc.domRestrict⟩
  refine iInf_le_of_le ⟨T', hT⟩ (iInf_le_of_le y (iInf_le_of_le hTx ?_))
  exact (p.fwRate_setPoint_eq (T := ⟨T', hT⟩) hσ h0 hc hφ hu fun t => rfl).le

/-- The derivative of the filter energy is continuous in the state. -/
@[tmio M, powerlib_domain] private theorem continuous_filterEnergyDeriv :
    Continuous p.filterEnergyDeriv := by
  unfold filterEnergyDeriv Params.potentialDeriv VSMLPFLossy.Pe
  fun_prop

/-- **Quasi-potential of the rate, lower bound** (three states, `A ≤ D ω_c`):
`inf_T inf {J_T(φ) : φ(T) = x} ≥ (2(D − A/ω_c)/σ_P²)(E(x) − E(x_A))`, `E = filterEnergy`. -/
@[tmio M, powerlib_domain] theorem fwQP_ge {σP : ℝ} (hσ : σP ≠ 0) (hA : p.A ≤ p.D * p.ωc)
    (xA x : Fin 3 → ℝ) :
    ENNReal.ofReal (2 * (p.D - p.A / p.ωc) / σP ^ 2 * (p.filterEnergy x - p.filterEnergy xA)) ≤
      ⨅ (T : ℝ≥0) (φ : C(Icc (0 : ℝ) T, Fin 3 → ℝ))
        (_ : φ ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩ = x),
        fwRate p.sdeDrift (fun _ : Fin 1 => p.setPointColumn σP) xA T φ := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_sdeDrift
  have h := le_fwQP_of_hj hK (fun _ : Fin 1 => p.setPointColumn σP)
    (W := fun y => 2 * (p.D - p.A / p.ωc) / σP ^ 2 * p.filterEnergy y)
    (fun y => (p.hasFDerivAt_filterEnergy y).const_mul _)
    (by exact p.continuous_filterEnergyDeriv.const_smul (2 * (p.D - p.A / p.ωc) / σP ^ 2))
    (fun y => p.hj_filter_nonpos hσ hA y)
    xA x
  rw [← mul_sub] at h
  exact h

/-- **Between rest points of the slow set** (three states, `A ≤ D ω_c`): at least
`2(D − A/ω_c)(U(δ_u) − U(δ_s))/σ_P²`. -/
@[tmio M, powerlib_domain] theorem fwQP_rest_ge {σP : ℝ} (hσ : σP ≠ 0) (hA : p.A ≤ p.D * p.ωc)
    (δs δu : ℝ) :
    ENNReal.ofReal (2 * (p.D - p.A / p.ωc) *
        (p.potential (δu - p.α) - p.potential (δs - p.α)) / σP ^ 2) ≤
      ⨅ (T : ℝ≥0) (φ : C(Icc (0 : ℝ) T, Fin 3 → ℝ))
        (_ : φ ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩ = ![δu, 0, p.toLossy.Pe δu]),
        fwRate p.sdeDrift (fun _ : Fin 1 => p.setPointColumn σP) ![δs, 0, p.toLossy.Pe δs] T φ := by
  convert p.fwQP_ge hσ hA ![δs, 0, p.toLossy.Pe δs] ![δu, 0, p.toLossy.Pe δu] using 2
  simp [filterEnergy]
  ring

/-- **Unconditional large deviations for polygonal set-point noise** (three states). -/
@[tmio M, powerlib_domain] theorem isLDP_setPoint_polygon {σP : ℝ} (hσ : σP ≠ 0)
    (x₀ : Fin 3 → ℝ) {T : ℝ≥0} (hT : 0 < (T : ℝ)) {n : ℕ} (hn : 0 < n)
    [MeasurableSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)] [BorelSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)]
    [MeasurableSpace C(Icc (0 : ℝ) T, Fin 3 → ℝ)] [BorelSpace C(Icc (0 : ℝ) T, Fin 3 → ℝ)]
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    IsLDP (𝓝[>] (0 : ℝ)) id
      (fun ε => (P.map fun ω => polyPath T n (polyNoise B T n ε ω)).map
        (solMap p.sdeDrift (columnsCLM fun _ : Fin 1 => p.setPointColumn σP) x₀))
      (pushRate (solMap p.sdeDrift (columnsCLM fun _ : Fin 1 => p.setPointColumn σP) x₀)
        fun w => if w ∈ range (polyPath T n) then schilderRate T w else ⊤) := by
  obtain ⟨K, hK⟩ := p.lipschitzWith_sdeDrift
  obtain ⟨L, hL⟩ := p.leftInverse_setPoint hσ
  exact (isLDP_polygon hB hT hn).map_solMap hK hL x₀

end Params3

end powerlib.GFM.Noise
