import theorem.Periodic.FlipOrbit
import theorem.Map.CenterReduction

/-! # The flip reduction of a periodic solution from every initial time

`theorem/Periodic/FlipOrbit.lean` decides a periodic solution `x_*` of a `T`-periodic system
`ẋ = G(t, x)` at a simple multiplier `−1` by the flip coefficient `a² + b` and states the solution
conclusions from the initial time `0`. For a `T`-periodic field these conclusions hold from every
initial time `τ`, with constants independent of `τ`: a positive flip coefficient makes `x_*`
uniformly Lyapunov stable and uniformly attracting (one `δ` and, for every `ε`, one settling
time `S` serve every initial time), a negative one makes it unstable with one escape radius for
every initial time.

The proof is a reduction to the period map `P` read from time `0`. Periodicity of `G` and of
`x_*` (`x_*(T) = x_*(0)` and uniqueness of solutions give `x_*(t + T) = x_*(t)`) moves an initial
time `τ` to the next multiple `b = ⌈τ/T⌉ T` of the period, `τ ≤ b < τ + T`; on `[τ, b]`
Grönwall's estimate bounds the deviation by `e^{KT}` times its initial size, and from `b` on the
solution, shifted by `b`, is a solution from time `0`. Uniform attraction comes from the uniform
attraction of a continuous locally asymptotically stable map on a closed ball
(`Map.LocalAsymptoticStable.exists_uniform`, a compactness argument) and the sampling estimate
`FlipOrbit.norm_sub_le_iterate`; the escape from an unstable period map happens after at least
one period, hence after every initial time of the first period, and is shifted to the others.

Scope.
* The setting of `theorem/Periodic/FlipOrbit.lean`: solutions in `ℝ^{Fin n}` with the sup norm,
  `G` `T`-periodic in `t` (`T > 0`), continuous and globally `K`-Lipschitz in `x` (for a field
  that is only locally Lipschitz see `theorem/Periodic/LocalField.lean`), `x_*` a global solution
  with `x_*(T) = x_*(0)`; the map semantics on `ℝⁿ` through `FlipOrbit.euclidMap`.
* Solutions from the initial time `τ` are integral curves on `[τ, ∞)` (Mathlib
  `IsIntegralCurveOn`); `τ` is any real number.
* The degenerate flip `a² + b = 0` is not decided (as in `FlipOrbit`).
* Generic mathematics; no model family.

Source: W. Hahn, *Stability of Motion* (1967), §§ 36–38 (for periodic right-hand sides stability
and asymptotic stability are uniform in the initial time); the open item of
`theorem/Periodic/FlipOrbit.lean` (Scope: "the solution statements concern the initial time
`0`").

Results.
* `periodic_of_fixed` — a solution of a `T`-periodic globally Lipschitz field with
  `x_*(T) = x_*(0)` is `T`-periodic.
* `isIntegralCurveOn_shift` — a solution on `[τ, ∞)` shifted by a period is a solution on
  `[τ − c, ∞)`.
* `lipschitzWith_periodMap` — the period map is `e^{KT}`-Lipschitz.
* `uniformlyStable_of_map` — a locally asymptotically stable period map gives uniform Lyapunov
  stability and uniform attraction of `x_*` from every initial time.
* `uniformlyUnstable_of_map` — an unstable period map gives one escape radius `ε` for every
  initial time.
* **The theorems**: `orbit_uniformly_stable_of_flipCoeff_pos` (`a² + b > 0`: the period map is
  locally asymptotically, not exponentially, stable and `x_*` is uniformly asymptotically stable)
  and `orbit_uniformly_unstable_of_flipCoeff_neg` (`a² + b < 0`: the period map is unstable and
  `x_*` is unstable with an escape radius independent of the initial time).

Corrections.
None: an extension (the solution conclusions of `FlipOrbit` from every initial time, uniformly).

Family and connection conclusions.
None: static evidence on periodic ODEs (uniform stability of a periodic solution).
-/

noncomputable section
namespace powerlib.Periodic.FlipOrbitUniform

open Set Matrix Function Filter Topology
open scoped Matrix.Norms.Operator
open FlowDerivative PeriodMapTaylor FlipOrbit

/-! ## Periodic solutions and shifts by a period -/

section Shift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : ℝ → E → E}

/-- **A returning solution is periodic.** For a `T`-periodic, globally `K`-Lipschitz field a
global solution with `x_*(T) = x_*(0)` satisfies `x_*(t + T) = x_*(t)` for all `t` (uniqueness of
solutions, Mathlib `ODE_solution_unique_univ`, applied to `x_*` and `x_*(· + T)`). -/
@[tmio T, powerlib_foundation] theorem periodic_of_fixed {K : NNReal}
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hGper : Periodic G T) {xs : ℝ → E}
    (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0) : Periodic xs T := by
  have h := ODE_solution_unique_univ (v := G) (s := fun _ => univ) (K := K) (t₀ := 0)
    (f := fun t => xs (t + T)) (g := xs) (fun t => (hK t).lipschitzOnWith)
    (fun t => ⟨by simpa only [hGper t] using (hxs (t + T)).comp_add_const t T, trivial⟩)
    (fun t => ⟨hxs t, trivial⟩) (by simpa using hfix)
  exact fun t => congrFun h t

/-- **Shift by a period.** For a `c`-periodic field a solution on `[τ, ∞)` read from `c` on,
`v ↦ x(v + c)`, is a solution on `[τ − c, ∞)`. -/
@[tmio T, powerlib_foundation] theorem isIntegralCurveOn_shift {c : ℝ} (hc : Periodic G c)
    {x : ℝ → E} {τ : ℝ} (hx : IsIntegralCurveOn x G (Ici τ)) :
    IsIntegralCurveOn (fun v => x (v + c)) G (Ici (τ - c)) := by
  intro v hv
  have hmaps : MapsTo (fun v : ℝ => v + c) (Ici (τ - c)) (Ici τ) := fun q hq => by
    simp only [mem_Ici] at hq ⊢; linarith
  have h := HasDerivWithinAt.scomp v (hx (v + c) (hmaps hv))
    ((hasDerivAt_id' v).hasDerivWithinAt.add_const c) hmaps
  simpa only [Function.comp_def, one_smul, hc v] using h

end Shift

section Orbit

variable {n : ℕ} {G : ℝ → (Fin n → ℝ) → Fin n → ℝ} {K : NNReal}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The period map of a `K`-Lipschitz field is `e^{KT}`-Lipschitz (Grönwall). -/
@[tmio T, powerlib_foundation] theorem lipschitzWith_periodMap (hGc : Continuous (uncurry G))
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 ≤ T) :
    LipschitzWith ⟨Real.exp (K * T), (Real.exp_pos _).le⟩ (periodMap hGc hK T) := by
  refine LipschitzWith.of_dist_le_mul fun ξ ξ' => ?_
  have h := dist_le_of_isIntegralCurveOn_Icc hK
    ((flow_solution hGc hK 0 ξ).mono Icc_subset_Ici_self)
    ((flow_solution hGc hK 0 ξ').mono Icc_subset_Ici_self) T ⟨hT, le_rfl⟩
  rw [flow_start, flow_start, sub_zero] at h
  show dist (flow hGc hK 0 ξ T) (flow hGc hK 0 ξ' T) ≤ Real.exp (K * T) * dist ξ ξ'
  exact h.trans_eq (mul_comm _ _)

/-- **The next period boundary.** For an initial time `τ` the multiple `b = ⌈τ/T⌉ T` of the
period satisfies `τ ≤ b < τ + T`; a solution on `[τ, ∞)` deviates from `x_*` on `[τ, b]` by at
most `e^{KT}` times its initial deviation, and from `b` on, shifted by `b`, it is a solution on
`[0, ∞)`, while `x_*(v + b) = x_*(v)`. -/
@[tmio T, powerlib_foundation] private theorem next_period (hK : ∀ t, LipschitzWith K (G t))
    {T : ℝ} (hT : 0 < T) (hGper : Periodic G T) {xs : ℝ → Fin n → ℝ}
    (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hxsp : Periodic xs T) {τ : ℝ}
    {x : ℝ → Fin n → ℝ} (hx : IsIntegralCurveOn x G (Ici τ)) :
    ∃ b : ℝ, τ ≤ b ∧ b < τ + T ∧
      (∀ u ∈ Icc τ b, ‖x u - xs u‖ ≤ Real.exp (K * T) * ‖x τ - xs τ‖) ∧
      IsIntegralCurveOn (fun v => x (v + b)) G (Ici 0) ∧ ∀ v, xs (v + b) = xs v := by
  have hτb : τ ≤ ⌈τ / T⌉ * T := by
    have := Int.le_ceil (τ / T)
    calc τ = τ / T * T := by field_simp
      _ ≤ (⌈τ / T⌉ : ℝ) * T := mul_le_mul_of_nonneg_right this hT.le
  have hbτ : (⌈τ / T⌉ : ℝ) * T < τ + T := by
    have := Int.ceil_lt_add_one (τ / T)
    calc (⌈τ / T⌉ : ℝ) * T < (τ / T + 1) * T := mul_lt_mul_of_pos_right this hT
      _ = τ + T := by field_simp
  refine ⟨⌈τ / T⌉ * T, hτb, hbτ, fun u hu => ?_, ?_, fun v => (hxsp.int_mul ⌈τ / T⌉) v⟩
  · have h := dist_le_of_isIntegralCurveOn_Icc hK (hx.mono fun q hq => hq.1)
      (fun r _ => (hxs r).hasDerivWithinAt) u hu
    rw [dist_eq_norm, dist_eq_norm] at h
    have he : Real.exp (K * (u - τ)) ≤ Real.exp (K * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [hu.2]) K.2)
    calc ‖x u - xs u‖ ≤ ‖x τ - xs τ‖ * Real.exp (K * (u - τ)) := h
      _ ≤ ‖x τ - xs τ‖ * Real.exp (K * T) := mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ = Real.exp (K * T) * ‖x τ - xs τ‖ := mul_comm _ _
  · have h := isIntegralCurveOn_shift (hGper.int_mul ⌈τ / T⌉) hx
    exact h.mono fun q hq => by simp only [mem_Ici] at hq ⊢; linarith

/-- **From the period map to the solutions, uniformly in the initial time: stability.** For a
`T`-periodic, globally Lipschitz field and a solution `x_*` with `x_*(T) = x_*(0)`: if the period
map (read on `ℝⁿ`) is locally asymptotically stable at `x_*(0)`, then `x_*` is uniformly Lyapunov
stable (for every `ε` one `δ` serves every initial time `τ`) and uniformly attracting (one `δ`,
and for every `ε` one time `S`, serve every initial time: deviations below `δ` at `τ` are below
`ε` from `τ + S` on). -/
@[tmio T, powerlib_foundation] theorem uniformlyStable_of_map (hGc : Continuous (uncurry G))
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    (h : Map.LocalAsymptoticStable (euclidMap (periodMap hGc hK T))
      ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) :
    (∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ (τ : ℝ) (x : ℝ → Fin n → ℝ), IsIntegralCurveOn x G (Ici τ) →
      ‖x τ - xs τ‖ < δ → ∀ t, τ ≤ t → ‖x t - xs t‖ < ε) ∧
    ∃ δ, 0 < δ ∧ ∀ ε, 0 < ε → ∃ S, 0 ≤ S ∧ ∀ (τ : ℝ) (x : ℝ → Fin n → ℝ),
      IsIntegralCurveOn x G (Ici τ) → ‖x τ - xs τ‖ < δ → ∀ t, τ + S ≤ t → ‖x t - xs t‖ < ε := by
  have hxsp := periodic_of_fixed hK hGper hxs hfix
  obtain ⟨hstab, -⟩ := solution_stable_of_map hGc hK hT hGper hxs hfix h
  have hC0 : 0 < Real.exp (K * T) := Real.exp_pos _
  -- uniform Lyapunov stability
  have hunif : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ (τ : ℝ) (x : ℝ → Fin n → ℝ),
      IsIntegralCurveOn x G (Ici τ) → ‖x τ - xs τ‖ < δ → ∀ t, τ ≤ t → ‖x t - xs t‖ < ε := by
    intro ε hε
    obtain ⟨δ₁, hδ₁, hb₁⟩ := hstab ε hε
    refine ⟨min δ₁ ε / Real.exp (K * T), div_pos (lt_min hδ₁ hε) hC0,
      fun τ x hx hx0 t ht => ?_⟩
    obtain ⟨b, hτb, -, hdev, hz, hxsb⟩ := next_period hK hT hGper hxs hxsp hx
    have hsmall : Real.exp (K * T) * ‖x τ - xs τ‖ < min δ₁ ε := by
      rw [lt_div_iff₀ hC0] at hx0; linarith
    rcases le_total t b with htb | hbt
    · exact ((hdev t ⟨ht, htb⟩).trans_lt hsmall).trans_le (min_le_right _ _)
    · have hz0 : ‖(fun v => x (v + b)) 0 - xs 0‖ < δ₁ := by
        have e1 : (fun v => x (v + b)) 0 - xs 0 = x b - xs b := by
          simp only [zero_add]; rw [← hxsb 0, zero_add]
        rw [e1]
        exact ((hdev b ⟨hτb, le_rfl⟩).trans_lt hsmall).trans_le (min_le_left _ _)
      have h1 := hb₁ (fun v => x (v + b)) hz hz0 (t - b) (by linarith)
      have e2 : (fun v => x (v + b)) (t - b) - xs (t - b) = x t - xs t := by
        simp only [sub_add_cancel]; rw [← hxsb (t - b), sub_add_cancel]
      rwa [e2] at h1
  refine ⟨hunif, ?_⟩
  -- uniform attraction of the period map on a closed ball
  set Em := EuclideanSpace.equiv (Fin n) ℝ with hEm
  set εL : ℝⁿ →L[ℝ] (Fin n → ℝ) := (Em : ℝⁿ →L[ℝ] (Fin n → ℝ)) with hεL
  set εS : (Fin n → ℝ) →L[ℝ] ℝⁿ := (Em.symm : (Fin n → ℝ) →L[ℝ] ℝⁿ) with hεS
  set P := periodMap hGc hK T with hP
  set pE := Em.symm (xs 0) with hpE
  set r : ℝⁿ → ℝⁿ := fun e => euclidMap P (pE + e) - pE with hr
  have hPc : Continuous P := (lipschitzWith_periodMap hGc hK hT.le).continuous
  have hrc : Continuous r := by
    have : Continuous (euclidMap P) := Em.symm.continuous.comp (hPc.comp Em.continuous)
    exact (this.comp (continuous_const.add continuous_id)).sub continuous_const
  have hrLAS : Map.LocalAsymptoticStable r 0 := by
    obtain ⟨hLS, c, hc, hatt⟩ := h
    refine ⟨FlipReduction.lyapunovStable_translate hLS, c, hc, fun e he => ?_⟩
    have h1 := (hatt (pE + e) (by simpa using he)).sub_const pE
    rw [sub_self] at h1
    refine h1.congr fun k => ?_
    rw [hr, FlipReduction.iterate_translate]
  obtain ⟨β, hβ, hunifr⟩ := Map.LocalAsymptoticStable.exists_uniform hrc hrLAS
  -- the sampled deviation in the two norms
  have hdev : ∀ (ξ : Fin n → ℝ) (j : ℕ),
      ‖P^[j] ξ - xs 0‖ ≤ ‖εL‖ * ‖r^[j] (Em.symm ξ - pE)‖ := fun ξ j => by
    rw [hr, FlipReduction.iterate_translate, add_sub_cancel, iterate_euclidMap,
      ContinuousLinearEquiv.apply_symm_apply]
    have : P^[j] ξ - xs 0 = Em (Em.symm (P^[j] ξ) - pE) := by
      rw [map_sub, ContinuousLinearEquiv.apply_symm_apply, hpE,
        ContinuousLinearEquiv.apply_symm_apply]
    rw [this]
    exact εL.le_opNorm _
  have hstart : ∀ ξ : Fin n → ℝ, ‖Em.symm ξ - pE‖ ≤ ‖εS‖ * ‖ξ - xs 0‖ := fun ξ => by
    rw [hpE, ← map_sub]; exact εS.le_opNorm _
  -- the attraction radius: deviations that stay below `β / (‖εS‖ + 1)`
  obtain ⟨δ, hδ, hδb⟩ := hunif (β / (‖εS‖ + 1)) (by positivity)
  refine ⟨δ, hδ, fun ε hε => ?_⟩
  have hCL : 0 ≤ Real.exp (K * T) * ‖εL‖ := mul_nonneg hC0.le (norm_nonneg _)
  have hη0 : 0 < ε / (Real.exp (K * T) * ‖εL‖ + 1) := div_pos hε (by linarith)
  obtain ⟨N, hN⟩ := hunifr _ hη0
  refine ⟨(N + 1) * T, by positivity, fun τ x hx hx0 t ht => ?_⟩
  obtain ⟨b, hτb, hbτ, -, hz, hxsb⟩ := next_period hK hT hGper hxs hxsp hx
  have hNT : 0 ≤ (N : ℝ) * T := by positivity
  have htb : (N : ℝ) * T ≤ t - b := by
    have : τ + ((N : ℝ) + 1) * T ≤ t := ht
    nlinarith
  have hz0 : ‖Em.symm ((fun v => x (v + b)) 0) - pE‖ ≤ β := by
    have h1 := hδb τ x hx hx0 b hτb
    have h2 : (fun v => x (v + b)) 0 - xs 0 = x b - xs b := by
      simp only [zero_add]; rw [← hxsb 0, zero_add]
    refine (hstart _).trans ?_
    rw [h2]
    refine (mul_le_mul_of_nonneg_left h1.le (norm_nonneg εS)).trans ?_
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg εS]
  have hj : N ≤ ⌊(t - b) / T⌋₊ := by
    apply Nat.le_floor
    rw [le_div_iff₀ hT]; exact htb
  have h1 := norm_sub_le_iterate hGc hK hT hGper hxs hfix hz (by linarith : 0 ≤ t - b)
  have h2 := hdev ((fun v => x (v + b)) 0) ⌊(t - b) / T⌋₊
  have h3 := hN _ hz0 _ hj
  have hxt : (fun v => x (v + b)) (t - b) - xs (t - b) = x t - xs t := by
    simp only [sub_add_cancel]; rw [← hxsb (t - b), sub_add_cancel]
  rw [hxt] at h1
  have h4 : Real.exp (K * T) * ‖εL‖ * (ε / (Real.exp (K * T) * ‖εL‖ + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  calc ‖x t - xs t‖
      ≤ Real.exp (K * T) * ‖P^[⌊(t - b) / T⌋₊] ((fun v => x (v + b)) 0) - xs 0‖ := h1
    _ ≤ Real.exp (K * T) * (‖εL‖ *
        ‖r^[⌊(t - b) / T⌋₊] (Em.symm ((fun v => x (v + b)) 0) - pE)‖) :=
        mul_le_mul_of_nonneg_left h2 hC0.le
    _ ≤ Real.exp (K * T) * (‖εL‖ * (ε / (Real.exp (K * T) * ‖εL‖ + 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3.le (norm_nonneg _)) hC0.le
    _ = Real.exp (K * T) * ‖εL‖ * (ε / (Real.exp (K * T) * ‖εL‖ + 1)) := by ring
    _ < ε := h4

/-- **From the period map to the solutions, uniformly in the initial time: instability.** For a
`T`-periodic, globally Lipschitz field and a solution `x_*` with `x_*(T) = x_*(0)`: if the period
map (read on `ℝⁿ`) is unstable at `x_*(0)`, one `ε > 0` serves every initial time: for every
`δ > 0` and every `τ` a solution on `[τ, ∞)` starts within `δ` of `x_*(τ)` and reaches the
distance `ε` from `x_*` at some `t ≥ τ`. -/
@[tmio T, powerlib_foundation] theorem uniformlyUnstable_of_map (hGc : Continuous (uncurry G))
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    (h : Map.Unstable (euclidMap (periodMap hGc hK T))
      ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) :
    ∃ ε, 0 < ε ∧ ∀ δ, 0 < δ → ∀ τ : ℝ, ∃ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici τ) ∧
      ‖x τ - xs τ‖ < δ ∧ ∃ t, τ ≤ t ∧ ε ≤ ‖x t - xs t‖ := by
  have hxsp := periodic_of_fixed hK hGper hxs hfix
  set Em := EuclideanSpace.equiv (Fin n) ℝ with hEm
  set εL : ℝⁿ →L[ℝ] (Fin n → ℝ) := (Em : ℝⁿ →L[ℝ] (Fin n → ℝ)) with hεL
  set εS : (Fin n → ℝ) →L[ℝ] ℝⁿ := (Em.symm : (Fin n → ℝ) →L[ℝ] ℝⁿ) with hεS
  set P := periodMap hGc hK T with hP
  set pE := Em.symm (xs 0) with hpE
  have hC0 : 0 < Real.exp (K * T) := Real.exp_pos _
  unfold Map.Unstable Map.LyapunovStable at h
  push Not at h
  obtain ⟨ε₁, hε₁, hesc⟩ := h
  refine ⟨ε₁ / (‖εS‖ + 1), by positivity, fun δ hδ τ => ?_⟩
  have hδ' : 0 < δ / (Real.exp (K * T) * (‖εL‖ + 1)) :=
    div_pos hδ (mul_pos hC0 (by positivity))
  obtain ⟨ŷ, hŷ, j, hj⟩ := hesc (min ε₁ (δ / (Real.exp (K * T) * (‖εL‖ + 1)))) (lt_min hε₁ hδ')
  -- the escape takes at least one period
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      simp only [Function.iterate_zero, id_eq] at hj
      linarith [hŷ.trans_le (min_le_left _ _)]
    · exact h0
  -- the period window `[a, a + T)` of `τ`
  obtain ⟨a, haτ, hτa, hGa, hxsa⟩ : ∃ a : ℝ, a ≤ τ ∧ τ < a + T ∧ Periodic G (-a) ∧
      ∀ v, xs (v + -a) = xs v := by
    refine ⟨⌊τ / T⌋ * T, ?_, ?_, ?_, ?_⟩
    · have := Int.floor_le (τ / T)
      calc (⌊τ / T⌋ : ℝ) * T ≤ τ / T * T := mul_le_mul_of_nonneg_right this hT.le
        _ = τ := by field_simp
    · have := Int.lt_floor_add_one (τ / T)
      calc τ = τ / T * T := by field_simp
        _ < ((⌊τ / T⌋ : ℝ) + 1) * T := mul_lt_mul_of_pos_right this hT
        _ = ⌊τ / T⌋ * T + T := by ring
    · have := hGper.int_mul (-⌊τ / T⌋)
      simpa only [Int.cast_neg, neg_mul] using this
    · intro v
      have := hxsp.int_mul (-⌊τ / T⌋) v
      simpa only [Int.cast_neg, neg_mul] using this
  -- the solution from time `0`, shifted to the window of `τ`
  have hyI : IsIntegralCurveOn (flow hGc hK 0 (Em ŷ)) G (Ici 0) := flow_solution hGc hK 0 _
  have hy0 : flow hGc hK 0 (Em ŷ) 0 = Em ŷ := flow_start hGc hK 0 _
  have hxI : IsIntegralCurveOn (fun v => flow hGc hK 0 (Em ŷ) (v + -a)) G (Ici a) := by
    have := isIntegralCurveOn_shift hGa hyI
    rwa [zero_sub, neg_neg] at this
  refine ⟨fun v => flow hGc hK 0 (Em ŷ) (v + -a), hxI.mono (Ici_subset_Ici.2 haτ), ?_,
    a + j * T, ?_, ?_⟩
  · -- the start is close
    show ‖flow hGc hK 0 (Em ŷ) (τ + -a) - xs τ‖ < δ
    rw [← hxsa τ]
    have h0 : ‖flow hGc hK 0 (Em ŷ) 0 - xs 0‖ ≤ ‖εL‖ * ‖ŷ - pE‖ := by
      rw [hy0, show Em ŷ - xs 0 = Em (ŷ - pE) by
        rw [map_sub, hpE, ContinuousLinearEquiv.apply_symm_apply]]
      exact εL.le_opNorm _
    have hg := dist_le_of_isIntegralCurveOn_Icc hK (hyI.mono Icc_subset_Ici_self)
      (fun r _ => (hxs r).hasDerivWithinAt) (τ + -a) ⟨by linarith, le_rfl⟩
    rw [dist_eq_norm, dist_eq_norm, sub_zero] at hg
    have he : Real.exp (K * (τ + -a)) ≤ Real.exp (K * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) K.2)
    have hŷδ : ‖ŷ - pE‖ < δ / (Real.exp (K * T) * (‖εL‖ + 1)) :=
      hŷ.trans_le (min_le_right _ _)
    calc ‖flow hGc hK 0 (Em ŷ) (τ + -a) - xs (τ + -a)‖
        ≤ ‖flow hGc hK 0 (Em ŷ) 0 - xs 0‖ * Real.exp (K * (τ + -a)) := hg
      _ ≤ ‖εL‖ * ‖ŷ - pE‖ * Real.exp (K * T) := by gcongr
      _ ≤ (‖εL‖ + 1) * ‖ŷ - pE‖ * Real.exp (K * T) := by gcongr; linarith
      _ < (‖εL‖ + 1) * (δ / (Real.exp (K * T) * (‖εL‖ + 1))) * Real.exp (K * T) := by gcongr
      _ = δ := by field_simp
  · have : (1 : ℝ) * T ≤ j * T :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hj1) hT.le
    linarith
  · -- the escape at the period `j`
    show ε₁ / (‖εS‖ + 1) ≤ ‖flow hGc hK 0 (Em ŷ) (a + j * T + -a) - xs (a + j * T)‖
    rw [← hxsa (a + j * T), show a + j * T + -a = j * T by ring,
      iterate_periodMap hGc hK hT.le hGper hyI j,
      solution_nat_mul_period hGc hK hT.le hGper hxs hfix j, hy0]
    have h1 : (euclidMap P)^[j] ŷ - pE = Em.symm (P^[j] (Em ŷ) - xs 0) := by
      rw [iterate_euclidMap, map_sub]
    rw [h1] at hj
    have h2 := hj.trans (εS.le_opNorm _)
    rw [div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg (P^[j] (Em ŷ) - xs 0)]

/-- **The flip reduction of a periodic solution from every initial time, stable side.** Under
the hypotheses of `FlipOrbit.orbit_stable_of_flipCoeff_pos` (`G` `T`-periodic, continuous, `C¹`
in `x` with jointly continuous `D_xG`, globally `K`-Lipschitz; `x_*(T) = x_*(0)`; the cubic
Taylor expansion along `x_*`; a simple multiplier `−1` of the monodromy with stable complement),
a positive flip coefficient `a² + b` makes the period map locally asymptotically, not
exponentially, stable at `x_*(0)` and `x_*` uniformly Lyapunov stable and uniformly attracting:
for every `ε` one `δ` serves every initial time `τ`, and one `δ` with, for every `ε`, one time
`S` makes every solution starting within `δ` of `x_*(τ)` stay within `ε` from `τ + S` on. -/
@[tmio T, powerlib_foundation] theorem orbit_uniformly_stable_of_flipCoeff_pos
    (hGc : Continuous (uncurry G)) (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    {Q₂ : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    (hQ₂ : Continuous Q₂) (hQ₃ : Continuous Q₃) {c₄ ρ : ℝ} (hρ : 0 < ρ)
    (hTay : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) -
      fderiv ℝ (G r) (xs r) u - Q₂ r u u - Q₃ r (fun _ => u)‖ ≤ c₄ * ‖u‖ ^ 4)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = -vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 + vecMulVec vm wm))
    {k : Fin n → ℝ} (hk : k - monodromy (jacobianAlong G xs) T 0 *ᵥ k =
      secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm -
        (wm ⬝ᵥ secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm) • vm)
    (hab : 0 < (wm ⬝ᵥ secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm) ^ 2 +
      (wm ⬝ᵥ thirdVariation (jacobianAlong G xs) Q₂ Q₃ 0 T (fun _ => vm) +
        wm ⬝ᵥ (secondVariation (jacobianAlong G xs) Q₂ 0 T vm k +
          secondVariation (jacobianAlong G xs) Q₂ 0 T k vm))) :
    (Map.LocalAsymptoticStable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
      ¬ Map.LocallyExponentiallyStable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0))) ∧
    (∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ (τ : ℝ) (x : ℝ → Fin n → ℝ), IsIntegralCurveOn x G (Ici τ) →
      ‖x τ - xs τ‖ < δ → ∀ t, τ ≤ t → ‖x t - xs t‖ < ε) ∧
    ∃ δ, 0 < δ ∧ ∀ ε, 0 < ε → ∃ S, 0 ≤ S ∧ ∀ (τ : ℝ) (x : ℝ → Fin n → ℝ),
      IsIntegralCurveOn x G (Ici τ) → ‖x τ - xs τ‖ < δ → ∀ t, τ + S ≤ t → ‖x t - xs t‖ < ε := by
  obtain ⟨hmap, -⟩ := orbit_stable_of_flipCoeff_pos hGc hGd hD hK hT hGper hxs hfix hQ₂ hQ₃ hρ
    hTay hv hw hwv hS hk hab
  exact ⟨hmap, uniformlyStable_of_map hGc hK hT hGper hxs hfix hmap.1⟩

/-- **The flip reduction of a periodic solution from every initial time, unstable side.** Under
the hypotheses of `orbit_uniformly_stable_of_flipCoeff_pos`, a negative flip coefficient
`a² + b` makes the period map unstable at `x_*(0)` and `x_*` unstable with one escape radius for
every initial time: there is `ε > 0` such that for every `δ > 0` and every `τ` a solution on
`[τ, ∞)` starts within `δ` of `x_*(τ)` and reaches the distance `ε` from `x_*`. -/
@[tmio T, powerlib_foundation] theorem orbit_uniformly_unstable_of_flipCoeff_neg
    (hGc : Continuous (uncurry G)) (hGd : ∀ t x, DifferentiableAt ℝ (G t) x)
    (hD : Continuous fun p : ℝ × (Fin n → ℝ) => fderiv ℝ (G p.1) p.2)
    (hK : ∀ t, LipschitzWith K (G t)) {T : ℝ} (hT : 0 < T) (hGper : Periodic G T)
    {xs : ℝ → Fin n → ℝ} (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) (hfix : xs T = xs 0)
    {Q₂ : ℝ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ}
    {Q₃ : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Fin n → ℝ) (Fin n → ℝ)}
    (hQ₂ : Continuous Q₂) (hQ₃ : Continuous Q₃) {c₄ ρ : ℝ} (hρ : 0 < ρ)
    (hTay : ∀ r ∈ Icc 0 T, ∀ u, ‖u‖ ≤ ρ → ‖G r (xs r + u) - G r (xs r) -
      fderiv ℝ (G r) (xs r) u - Q₂ r u u - Q₃ r (fun _ => u)‖ ≤ c₄ * ‖u‖ ^ 4)
    {vm wm : Fin n → ℝ} (hv : monodromy (jacobianAlong G xs) T 0 *ᵥ vm = -vm)
    (hw : wm ᵥ* monodromy (jacobianAlong G xs) T 0 = -wm) (hwv : wm ⬝ᵥ vm = 1)
    (hS : LTI.SchurStable (monodromy (jacobianAlong G xs) T 0 + vecMulVec vm wm))
    {k : Fin n → ℝ} (hk : k - monodromy (jacobianAlong G xs) T 0 *ᵥ k =
      secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm -
        (wm ⬝ᵥ secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm) • vm)
    (hab : (wm ⬝ᵥ secondVariation (jacobianAlong G xs) Q₂ 0 T vm vm) ^ 2 +
      (wm ⬝ᵥ thirdVariation (jacobianAlong G xs) Q₂ Q₃ 0 T (fun _ => vm) +
        wm ⬝ᵥ (secondVariation (jacobianAlong G xs) Q₂ 0 T vm k +
          secondVariation (jacobianAlong G xs) Q₂ 0 T k vm)) < 0) :
    Map.Unstable (euclidMap (periodMap hGc hK T))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (xs 0)) ∧
    ∃ ε, 0 < ε ∧ ∀ δ, 0 < δ → ∀ τ : ℝ, ∃ x : ℝ → Fin n → ℝ, IsIntegralCurveOn x G (Ici τ) ∧
      ‖x τ - xs τ‖ < δ ∧ ∃ t, τ ≤ t ∧ ε ≤ ‖x t - xs t‖ := by
  obtain ⟨hmap, -⟩ := orbit_unstable_of_flipCoeff_neg hGc hGd hD hK hT hGper hxs hfix hQ₂ hQ₃
    hρ hTay hv hw hwv hS hk hab
  exact ⟨hmap, uniformlyUnstable_of_map hGc hK hT hGper hxs hfix hmap⟩

end Orbit

end powerlib.Periodic.FlipOrbitUniform
