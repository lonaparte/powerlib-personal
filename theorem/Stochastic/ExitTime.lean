import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.AdditiveMarkov
import theorem.Stochastic.Schilder

/-! # The Freidlin–Wentzell upper bound for the mean exit time of an additive-noise system

For the solution `x^ε = S(x₀, √ε B)` of `x(t) = x₀ + √ε N B(t) + ∫₀ᵗ b(x)` (`b` globally
Lipschitz, one Brownian noise column, all paths of `B` continuous) and a compact set `K ∋ x₀`, the
exit time `τ_ε = inf {t : x^ε(t) ∉ K}` satisfies
`limsup_{ε→0⁺} ε log E τ_ε ≤ sup_{x ∈ K} inf {J_x^T(φ) : φ leaves K before T}` for every horizon
`T > 0` (`J_x^T` the Freidlin–Wentzell rate from `x` on `[0, T]`, the push-forward of the Schilder
rate through the solution map). The proof is the first half of Freidlin–Wentzell's exit theorem:
the Markov property at the times `kT` (`Stochastic.LDP.measure_solMap_markov_le`) gives
`P(τ > (n + 1)T) ≤ (1 − q_ε)^{n+1}` with `q_ε = inf_{x ∈ K} P_x(τ ≤ T)`, hence
`E τ_ε ≤ 2T/q_ε`, and the uniform large-deviation lower bound
(`Stochastic.LDP.IsLDP.le_liminf_iInf_solMap` with Schilder's theorem) bounds `q_ε` below.

Scope.
* Generic: `E` a real Banach space, `N : (Fin 1 → ℝ) →L[ℝ] E`, `B` a Brownian motion (Mathlib's
  `IsBrownianReal`) all of whose paths are continuous (a modification of any Brownian motion),
  `K` compact. The exit time is `Stochastic.LDP.exitTime` (`⊤` if the path never leaves `K`),
  its expectation the lower Lebesgue integral.
* Upper bound. The matching lower bound is `Stochastic.LDP.le_liminf_log_lintegral_exitTime`
  (`theorem/Stochastic/ExitTimeLower.lean`: from an exit and a moment inequality for the rate, by
  a chain of deterministic time blocks); the strong Markov property is
  `Stochastic.LDP.integral_solMap_strongMarkov` (`theorem/Stochastic/StrongMarkov.lean`).

Source: M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 4 §2 (Thm 4.2.1, upper bound for the exit time); A. Dembo, O. Zeitouni, *Large Deviations
Techniques and Applications*, 2nd ed. (1998), Lemma 5.7.18 and the proof of Thm 5.7.11(a)
(geometric trials over time blocks).

Results.
* `brownPath` (the path of `B` on `[0, T]`), `firstExit` (first exit time of a path on
  `[0, T]`), `exitTime` (exit time over all horizons); `brownPath_ae_eq` (a version agrees with
  it almost surely), `restrictPath_brownPath`, `forall_mem_iff_restrict_restart` (a path stays in
  `K` on `[0, T₁ + T₂]` iff its restriction and its restart do).
* `delayPath` (a driving path delayed by `a` and continued at its final value),
  `schilderRate_delayPath_le` (its Schilder rate is at most that of the path): concatenation of a
  noiseless stretch with a given driving path and extension to a longer horizon.
* `concatPath`, `restrictPath_concatPath`, `shiftPath_concatPath`, `schilderRate_concatPath_le`
  (concatenated driving paths: their Schilder rates add up at most);
  `eq_solMap_of_hasDerivAt` (a path with derivative `b + N u` inside `(0, T)` is the solution
  driven by `∫ u`), `schilderRate_le_of_continuous` (the rate of `∫ u` is at most the action of
  `u`).
* `schilderRate_restrictPath_le` (the Schilder rate of a restriction is at most that of the
  path), `iInf_pushRate_le_of_le` (**the rate of a path dominates the quasi-potential of each of
  its intermediate states**: the restricted driving path reaches `φ(t)` at no higher rate).
* `measure_stay_le_pow` (**geometric survival bound**): `P(x stays in K on [0, (n + 1)T]) ≤
  (1 − q)^{n+1}`; `lintegral_exitTime_le`: `E τ ≤ 2T/q`.
* `limsup_log_lintegral_exitTime_le` (**Freidlin–Wentzell upper bound for the mean exit time**).
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The path of `B` on `[0, T]`, for a process all of whose paths are continuous. -/
def brownPath (B : ℝ≥0 → Ω → ℝ) (hBc : ∀ ω, Continuous fun t => B t ω) (T : ℝ≥0) (ω : Ω) :
    C(Icc (0 : ℝ) T, Fin 1 → ℝ) :=
  ⟨fun t _ => B ⟨t, t.2.1⟩ ω, continuous_pi fun _ =>
    (hBc ω).comp (continuous_subtype_val.subtype_mk _)⟩

/-- First exit time of a path on `[0, T]` from `K` (`⊤` if it stays in `K`). -/
def firstExit (K : Set E) {T : ℝ≥0} (φ : C(Icc (0 : ℝ) T, E)) : ℝ≥0∞ :=
  ⨅ (t : Icc (0 : ℝ) T) (_ : φ t ∉ K), ENNReal.ofReal t

/-- Exit time from `K` of the solution `S(x₀, c B)` of `x(t) = x₀ + c N B(t) + ∫₀ᵗ b(x)`: the
infimum over all horizons `T` of its first exit on `[0, T]`. -/
def exitTime (b : E → E) (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) (K : Set E) (c : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hBc : ∀ ω, Continuous fun t => B t ω) (ω : Ω) : ℝ≥0∞ :=
  ⨅ T : ℝ≥0, firstExit K (solMap b N x₀ (c • brownPath B hBc T ω))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A version of `B` on `[0, T]` agrees with its path almost surely. -/
@[tmio T, powerlib_foundation] theorem brownPath_ae_eq (hBc : ∀ ω, Continuous fun t => B t ω)
    {T : ℝ≥0} {X : Ω → C(Icc (0 : ℝ) T, Fin 1 → ℝ)}
    (hXB : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) T, X ω t 0 = B ⟨t, t.2.1⟩ ω) :
    ∀ᵐ ω ∂P, brownPath B hBc T ω = X ω := by
  filter_upwards [hXB] with ω hω
  ext t j
  fin_cases j
  exact (hω t).symm

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[tmio T, powerlib_foundation] theorem restrictPath_brownPath
    (hBc : ∀ ω, Continuous fun t => B t ω) {T₁ T : ℝ≥0} (h : T₁ ≤ T) (ω : Ω) :
    restrictPath h (brownPath B hBc T ω) = brownPath B hBc T₁ ω := rfl

omit [NormedSpace ℝ E] in
/-- A path stays in `K` on `[0, T₁ + T₂]` iff its restriction to `[0, T₁]` and its restart after
`T₁` stay in `K`. -/
@[tmio T, powerlib_foundation] theorem forall_mem_iff_restrict_restart {K : Set E}
    {T₁ T₂ : ℝ≥0} (φ : C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), E)) :
    (∀ t, φ t ∈ K) ↔
      (∀ t, restrictPath le_self_add φ t ∈ K) ∧ (∀ t, restartPath T₁ T₂ φ t ∈ K) := by
  have hsum : ((T₁ + T₂ : ℝ≥0) : ℝ) = T₁ + T₂ := NNReal.coe_add T₁ T₂
  constructor
  · intro h
    refine ⟨fun t => h _, fun t => ?_⟩
    have hmem : (T₁ : ℝ) + t ∈ Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0) :=
      ⟨by linarith [t.2.1, T₁.coe_nonneg], by rw [hsum]; linarith [t.2.2]⟩
    simp only [restartPath, ContinuousMap.coe_mk]
    rw [pathExt_of_mem _ hmem]
    exact h _
  · rintro ⟨h1, h2⟩ t
    by_cases ht : (t : ℝ) ≤ T₁
    · exact h1 ⟨t, t.2.1, ht⟩
    · have ht2 : (t : ℝ) ≤ T₁ + T₂ := le_trans t.2.2 (le_of_eq hsum)
      have hs : (t : ℝ) - T₁ ∈ Icc (0 : ℝ) T₂ := ⟨by linarith, by linarith⟩
      have h := h2 ⟨_, hs⟩
      simp only [restartPath, ContinuousMap.coe_mk, add_sub_cancel] at h
      rwa [pathExt_of_mem _ t.2] at h

/-! ## Delayed driving paths -/

/-- The path `t ↦ w(t − a)` on `[0, T]`, for `w` on `[0, T₀]` extended by its end values: `w`
delayed by `a` and continued at its final value. -/
def delayPath {m : ℕ} (a : ℝ) {T₀ : ℝ≥0} (T : ℝ≥0) (w : C(Icc (0 : ℝ) T₀, Fin m → ℝ)) :
    C(Icc (0 : ℝ) T, Fin m → ℝ) :=
  ⟨fun t => pathExt w (t - a),
    (continuous_pathExt w).comp (continuous_subtype_val.sub continuous_const)⟩

/-- The integral of `u` restricted to `[0, T₀]` over `[c, d]`, `c ≤ 0`, is the integral of `u` up
to `d` clamped to `[0, T₀]`. -/
@[tmio T, powerlib_foundation] private theorem integral_indicator_clamp {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {T₀ : ℝ≥0} {u : ℝ → F}
    (hu : IntervalIntegrable u volume 0 T₀) {c d : ℝ} (hc : c ≤ 0) (hcd : c ≤ d) :
    ∫ x in c..d, (Icc (0 : ℝ) T₀).indicator u x =
      ∫ x in (0 : ℝ)..(projIcc (0 : ℝ) T₀ T₀.coe_nonneg d : ℝ), u x := by
  have hT := T₀.coe_nonneg
  have hgi : Integrable ((Icc (0 : ℝ) T₀).indicator u) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact (integrableOn_Icc_iff_integrableOn_Ioc).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hu)
  have hz : ∀ p q : ℝ, (∀ x ∈ Ioo p q, x ∉ Icc (0 : ℝ) T₀) → p ≤ q →
      ∫ x in p..q, (Icc (0 : ℝ) T₀).indicator u x = 0 := by
    intro p q hpq hle
    rw [intervalIntegral.integral_of_le hle]
    refine setIntegral_eq_zero_of_ae_eq_zero ?_
    have : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ q := by
      rw [ae_iff]; simp
    filter_upwards [this] with x hxq hx
    exact indicator_of_notMem (hpq x ⟨hx.1, lt_of_le_of_ne hx.2 hxq⟩) _
  have hsplit : ∀ p q r : ℝ, (∫ x in p..q, (Icc (0 : ℝ) T₀).indicator u x) +
      ∫ x in q..r, (Icc (0 : ℝ) T₀).indicator u x =
        ∫ x in p..r, (Icc (0 : ℝ) T₀).indicator u x := fun p q r =>
    intervalIntegral.integral_add_adjacent_intervals hgi.intervalIntegrable
      hgi.intervalIntegrable
  have hon : ∀ q : ℝ, 0 ≤ q → q ≤ (T₀ : ℝ) →
      ∫ x in (0 : ℝ)..q, (Icc (0 : ℝ) T₀).indicator u x = ∫ x in (0 : ℝ)..q, u x := by
    intro q hq0 hqT
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hq0] at hx
    exact indicator_of_mem (show x ∈ Icc (0 : ℝ) T₀ from ⟨hx.1, hx.2.trans hqT⟩) _
  rcases le_or_gt d 0 with hd | hd
  · rw [projIcc_of_le_left _ hd]
    simp only [intervalIntegral.integral_same]
    exact hz c d (fun x hx hx' => by linarith [hx.2, hx'.1]) hcd
  rcases le_or_gt d T₀ with hdT | hdT
  · rw [projIcc_of_mem _ ⟨hd.le, hdT⟩, ← hsplit c 0 d, hz c 0 (fun x hx hx' => by
      linarith [hx.2, hx'.1]) hc, zero_add, hon d hd.le hdT]
  · rw [projIcc_of_right_le _ hdT.le, ← hsplit c 0 d, hz c 0 (fun x hx hx' => by
      linarith [hx.2, hx'.1]) hc, zero_add, ← hsplit 0 T₀ d, hon T₀ hT le_rfl,
      hz T₀ d (fun x hx hx' => by linarith [hx.1, hx'.2]) hdT.le, add_zero]

/-- **The Schilder rate of a delayed and continued path** is at most that of the path: the
control is `u(t − a)` on `[a, a + T₀]` and `0` elsewhere. -/
@[tmio T, powerlib_foundation] theorem schilderRate_delayPath_le {m : ℕ} {a : ℝ} (ha : 0 ≤ a)
    {T₀ T : ℝ≥0} (hT : a + T₀ ≤ T) (w : C(Icc (0 : ℝ) T₀, Fin m → ℝ)) :
    schilderRate T (delayPath a T w) ≤ schilderRate T₀ w := by
  unfold schilderRate
  refine le_iInf₂ fun u hu => ?_
  obtain ⟨hu1, hu2, hw⟩ := hu
  set g : ℝ → Fin m → ℝ := (Icc (0 : ℝ) T₀).indicator u with hg
  have hT₀ := T₀.coe_nonneg
  have hgi : Integrable g := by
    rw [hg, integrable_indicator_iff measurableSet_Icc]
    exact (integrableOn_Icc_iff_integrableOn_Ioc).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT₀).mp hu1)
  have hsq : (fun t => ∑ j, g t j ^ 2) = (Icc (0 : ℝ) T₀).indicator (fun t => ∑ j, u t j ^ 2) := by
    funext t
    by_cases ht : t ∈ Icc (0 : ℝ) T₀
    · simp [hg, indicator_of_mem ht]
    · simp [hg, indicator_of_notMem ht]
  have hsqi : Integrable fun t => ∑ j, g t j ^ 2 := by
    rw [hsq, integrable_indicator_iff measurableSet_Icc]
    exact (integrableOn_Icc_iff_integrableOn_Ioc).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT₀).mp hu2)
  have hrep : ∀ t : Icc (0 : ℝ) T, delayPath a T w t = ∫ s in (0 : ℝ)..t, g (s - a) := by
    intro t
    have ht := t.2
    show pathExt w (t - a) = _
    rw [intervalIntegral.integral_comp_sub_right (fun x => g x) a, zero_sub,
      integral_indicator_clamp hu1 (by linarith) (by linarith [ht.1])]
    simp only [pathExt, IccExtend]
    exact hw _
  refine (iInf₂_le (fun t => g (t - a)) ⟨(hgi.comp_sub_right a).intervalIntegrable,
    (hsqi.comp_sub_right a).intervalIntegrable, hrep⟩).trans (le_of_eq ?_)
  have hTa : (T₀ : ℝ) ≤ T - a := by linarith
  unfold controlAction
  congr 2
  rw [intervalIntegral.integral_comp_sub_right (fun x => ∑ j, g x j ^ 2) a, zero_sub, hsq,
    integral_indicator_clamp hu2 (by linarith) (by linarith [T.coe_nonneg]),
    projIcc_of_right_le _ hTa]

/-! ## Restrictions and intermediate times -/

/-- **The Schilder rate of a restriction** is at most that of the path. -/
@[tmio T, powerlib_foundation] theorem schilderRate_restrictPath_le {m : ℕ} {T₁ T : ℝ≥0}
    (h : T₁ ≤ T) (w : C(Icc (0 : ℝ) T, Fin m → ℝ)) :
    schilderRate T₁ (restrictPath h w) ≤ schilderRate T w := by
  unfold schilderRate
  refine le_iInf₂ fun u hu => ?_
  obtain ⟨hu1, hu2, hw⟩ := hu
  have hT₁ : (T₁ : ℝ) ≤ T := h
  have hsub : uIcc (0 : ℝ) T₁ ⊆ uIcc (0 : ℝ) T :=
    uIcc_subset_uIcc left_mem_uIcc (by rw [uIcc_of_le T.coe_nonneg]; exact ⟨T₁.coe_nonneg, hT₁⟩)
  refine (iInf₂_le u ⟨hu1.mono_set hsub, hu2.mono_set hsub, fun t => hw _⟩).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  unfold controlAction
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine intervalIntegral.integral_mono_interval le_rfl T₁.coe_nonneg hT₁ ?_ hu2
  exact Eventually.of_forall fun t => Finset.sum_nonneg fun j _ => sq_nonneg _

/-! ## Concatenated driving paths -/

/-- Concatenation of driving paths: `w₁` on `[0, T₁]` followed by the increments of `w₂` on
`[0, T₂]`, `t ↦ w₁(t ∧ T₁) + w₂((t − T₁) ∨ 0)` on `[0, T₁ + T₂]`. -/
def concatPath {m : ℕ} {T₁ T₂ : ℝ≥0} (w₁ : C(Icc (0 : ℝ) T₁, Fin m → ℝ))
    (w₂ : C(Icc (0 : ℝ) T₂, Fin m → ℝ)) : C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), Fin m → ℝ) :=
  ⟨fun t => pathExt w₁ t + pathExt w₂ (t - T₁),
    ((continuous_pathExt w₁).comp continuous_subtype_val).add
      ((continuous_pathExt w₂).comp (continuous_subtype_val.sub continuous_const))⟩

@[tmio T, powerlib_foundation] theorem restrictPath_concatPath {m : ℕ} {T₁ T₂ : ℝ≥0}
    (w₁ : C(Icc (0 : ℝ) T₁, Fin m → ℝ)) (w₂ : C(Icc (0 : ℝ) T₂, Fin m → ℝ))
    (hw₂ : pathExt w₂ 0 = 0) : restrictPath le_self_add (concatPath w₁ w₂) = w₁ := by
  ext t j
  have ht : (t : ℝ) - T₁ ≤ 0 := by linarith [t.2.2]
  have e : pathExt w₂ ((t : ℝ) - T₁) = pathExt w₂ 0 := by
    simp only [pathExt, IccExtend, Function.comp_apply]
    rw [projIcc_of_le_left _ ht, projIcc_of_le_left _ le_rfl]
  show (pathExt w₁ t + pathExt w₂ ((t : ℝ) - T₁)) j = w₁ t j
  rw [e, hw₂, add_zero, pathExt_of_mem _ t.2]

@[tmio T, powerlib_foundation] theorem shiftPath_concatPath {m : ℕ} {T₁ T₂ : ℝ≥0}
    (w₁ : C(Icc (0 : ℝ) T₁, Fin m → ℝ)) (w₂ : C(Icc (0 : ℝ) T₂, Fin m → ℝ))
    (hw₂ : pathExt w₂ 0 = 0) : shiftPath T₁ T₂ (concatPath w₁ w₂) = w₂ := by
  ext t j
  have hsum : ((T₁ + T₂ : ℝ≥0) : ℝ) = T₁ + T₂ := NNReal.coe_add T₁ T₂
  have hmem : (T₁ : ℝ) + t ∈ Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0) :=
    ⟨by linarith [t.2.1, T₁.coe_nonneg], by rw [hsum]; linarith [t.2.2]⟩
  have hmem0 : (T₁ : ℝ) ∈ Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0) :=
    ⟨T₁.coe_nonneg, by rw [hsum]; linarith [T₂.coe_nonneg]⟩
  have e1 : pathExt w₁ ((T₁ : ℝ) + t) = pathExt w₁ T₁ := by
    simp only [pathExt, IccExtend, Function.comp_apply]
    rw [projIcc_of_right_le _ (by linarith [t.2.1]), projIcc_right]
  simp only [shiftPath, ContinuousMap.coe_mk]
  rw [pathExt_of_mem _ hmem, pathExt_of_mem _ hmem0]
  show (pathExt w₁ ((T₁ : ℝ) + t) + pathExt w₂ ((T₁ : ℝ) + t - T₁) -
    (pathExt w₁ T₁ + pathExt w₂ ((T₁ : ℝ) - T₁))) j = w₂ t j
  rw [e1, add_sub_cancel_left, sub_self, hw₂, pathExt_of_mem _ t.2]
  simp

/-- **The Schilder rate is subadditive under concatenation** (the controls have disjoint
supports). -/
@[tmio T, powerlib_foundation] theorem schilderRate_concatPath_le {m : ℕ} {T₁ T₂ : ℝ≥0}
    (w₁ : C(Icc (0 : ℝ) T₁, Fin m → ℝ)) (w₂ : C(Icc (0 : ℝ) T₂, Fin m → ℝ)) :
    schilderRate (T₁ + T₂) (concatPath w₁ w₂) ≤ schilderRate T₁ w₁ + schilderRate T₂ w₂ := by
  have hT₁ := T₁.coe_nonneg
  have hT₂ := T₂.coe_nonneg
  have hsum : ((T₁ + T₂ : ℝ≥0) : ℝ) = T₁ + T₂ := NNReal.coe_add T₁ T₂
  unfold schilderRate
  refine ENNReal.le_iInf_add_iInf fun u₁ u₂ => ENNReal.le_iInf_add_iInf fun h₁ h₂ => ?_
  obtain ⟨hu1, hs1, hw1⟩ := h₁
  obtain ⟨hu2, hs2, hw2⟩ := h₂
  set g₁ : ℝ → Fin m → ℝ := (Icc (0 : ℝ) T₁).indicator u₁ with hg₁
  set g₂ : ℝ → Fin m → ℝ := (Icc (0 : ℝ) T₂).indicator u₂ with hg₂
  have hint : ∀ {T : ℝ≥0} {v : ℝ → Fin m → ℝ}, IntervalIntegrable v volume 0 T →
      Integrable ((Icc (0 : ℝ) T).indicator v) := fun {T} {v} hv => by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact (integrableOn_Icc_iff_integrableOn_Ioc).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mp hv)
  have hintr : ∀ {T : ℝ≥0} {v : ℝ → ℝ}, IntervalIntegrable v volume 0 T →
      Integrable ((Icc (0 : ℝ) T).indicator v) := fun {T} {v} hv => by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact (integrableOn_Icc_iff_integrableOn_Ioc).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mp hv)
  have hsq : ∀ {T : ℝ≥0} (v : ℝ → Fin m → ℝ) (t : ℝ),
      ∑ j, (Icc (0 : ℝ) T).indicator v t j ^ 2 =
        (Icc (0 : ℝ) T).indicator (fun t => ∑ j, v t j ^ 2) t := fun {T} v t => by
    by_cases ht : t ∈ Icc (0 : ℝ) T
    · simp [indicator_of_mem ht]
    · simp [indicator_of_notMem ht]
  have hg₁i := hint hu1
  have hg₂i := hint hu2
  set u : ℝ → Fin m → ℝ := fun t => g₁ t + g₂ (t - T₁) with hu
  -- the square sum splits away from `T₁`
  have hsplit : ∀ t, t ≠ (T₁ : ℝ) → ∑ j, u t j ^ 2 =
      (Icc (0 : ℝ) T₁).indicator (fun t => ∑ j, u₁ t j ^ 2) t +
        (Icc (0 : ℝ) T₂).indicator (fun t => ∑ j, u₂ t j ^ 2) (t - T₁) := by
    intro t ht
    have e : ∑ j, u t j ^ 2 = ∑ j, g₁ t j ^ 2 + ∑ j, g₂ (t - T₁) j ^ 2 := by
      rcases lt_or_gt_of_ne ht with hlt | hgt
      · have h0 : g₂ (t - T₁) = 0 := indicator_of_notMem (fun h => by linarith [h.1]) _
        simp [hu, h0]
      · have h0 : g₁ t = 0 := indicator_of_notMem (fun h => by linarith [h.2]) _
        simp [hu, h0]
    rw [e, hg₁, hg₂, hsq, hsq]
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), ∑ j, u t j ^ 2 =
      (Icc (0 : ℝ) T₁).indicator (fun t => ∑ j, u₁ t j ^ 2) t +
        (Icc (0 : ℝ) T₂).indicator (fun t => ∑ j, u₂ t j ^ 2) (t - T₁) := by
    have : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ (T₁ : ℝ) := by rw [ae_iff]; simp
    filter_upwards [this] with t ht using hsplit t ht
  have hsqi : Integrable fun t => (Icc (0 : ℝ) T₁).indicator (fun t => ∑ j, u₁ t j ^ 2) t +
      (Icc (0 : ℝ) T₂).indicator (fun t => ∑ j, u₂ t j ^ 2) (t - T₁) :=
    (hintr hs1).add ((hintr hs2).comp_sub_right _)
  have hrep : ∀ t : Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), concatPath w₁ w₂ t = ∫ s in (0 : ℝ)..t, u s := by
    intro t
    have ht : (t : ℝ) ∈ Icc (0 : ℝ) (T₁ + T₂) := ⟨t.2.1, le_trans t.2.2 (le_of_eq hsum)⟩
    show pathExt w₁ t + pathExt w₂ ((t : ℝ) - T₁) = _
    rw [intervalIntegral.integral_add hg₁i.intervalIntegrable
        (hg₂i.comp_sub_right _).intervalIntegrable,
      intervalIntegral.integral_comp_sub_right (fun x => g₂ x) (T₁ : ℝ), zero_sub,
      integral_indicator_clamp hu1 le_rfl ht.1,
      integral_indicator_clamp hu2 (by linarith) (by linarith [ht.1])]
    simp only [pathExt, IccExtend, Function.comp_apply]
    rw [hw1, hw2]
  refine (iInf₂_le u ⟨(hg₁i.add (hg₂i.comp_sub_right _)).intervalIntegrable,
    (hsqi.congr (hae.mono fun t ht => ht.symm)).intervalIntegrable, hrep⟩).trans ?_
  refine (ENNReal.ofReal_le_ofReal (le_of_eq ?_)).trans ENNReal.ofReal_add_le
  unfold controlAction
  rw [intervalIntegral.integral_congr_ae (hae.mono fun t ht _ => ht),
    intervalIntegral.integral_add (hintr hs1).intervalIntegrable
      ((hintr hs2).comp_sub_right _).intervalIntegrable,
    intervalIntegral.integral_comp_sub_right
      (fun x => (Icc (0 : ℝ) T₂).indicator (fun t => ∑ j, u₂ t j ^ 2) x) (T₁ : ℝ), zero_sub,
    integral_indicator_clamp hs1 le_rfl (by rw [hsum]; linarith),
    integral_indicator_clamp hs2 (by linarith) (by rw [hsum]; linarith),
    projIcc_of_right_le _ (by rw [hsum]; linarith),
    projIcc_of_right_le _ (by rw [hsum]; linarith)]
  ring


section Bounds

variable [CompleteSpace E]

/-- **A path whose derivative inside `(0, T)` is `b + N u` is the solution driven by `∫ u`**
(`u` continuous). -/
@[tmio T, powerlib_foundation] theorem eq_solMap_of_hasDerivAt {m : ℕ} {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : (Fin m → ℝ) →L[ℝ] E) {T : ℝ≥0} {ψ : C(Icc (0 : ℝ) T, E)}
    {u : ℝ → Fin m → ℝ} (hu : Continuous u) {W : C(Icc (0 : ℝ) T, Fin m → ℝ)}
    (hW : ∀ t : Icc (0 : ℝ) T, W t = ∫ s in (0 : ℝ)..t, u s)
    (hψ : ∀ s ∈ Ioo (0 : ℝ) T, HasDerivAt (pathExt ψ) (b (pathExt ψ s) + N (u s)) s) :
    ψ = solMap b N (pathExt ψ 0) W := by
  refine eq_solMap hb fun t => ?_
  have hbc : Continuous fun s => b (pathExt ψ s) := hb.continuous.comp (continuous_pathExt ψ)
  have hNc : Continuous fun s => N (u s) := N.continuous.comp hu
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.2.1
    ((continuous_pathExt ψ).continuousOn)
    (fun s hs => hψ s ⟨hs.1, hs.2.trans_le t.2.2⟩)
    ((hbc.add hNc).intervalIntegrable 0 t)
  rw [intervalIntegral.integral_add (hbc.intervalIntegrable 0 t) (hNc.intervalIntegrable 0 t),
    N.intervalIntegral_comp_comm (hu.intervalIntegrable 0 t), ← hW t,
    pathExt_of_mem _ t.2] at hftc
  have e : ψ t = ψ ⟨(t : ℝ), t.2⟩ := rfl
  have h2 := sub_eq_iff_eq_add.mp hftc.symm
  rw [e, h2]
  abel

/-- The Schilder rate of the primitive of a continuous control is at most its action. -/
@[tmio T, powerlib_foundation] theorem schilderRate_le_of_continuous {m : ℕ} {T : ℝ≥0}
    {u : ℝ → Fin m → ℝ} (hu : Continuous u) {W : C(Icc (0 : ℝ) T, Fin m → ℝ)}
    (hW : ∀ t : Icc (0 : ℝ) T, W t = ∫ s in (0 : ℝ)..t, u s) :
    schilderRate T W ≤ ENNReal.ofReal (controlAction u T) :=
  iInf₂_le u ⟨hu.intervalIntegrable 0 T,
    (continuous_finsetSum _ fun j _ => ((continuous_apply j).comp hu).pow 2).intervalIntegrable 0 T,
    hW⟩

/-- **The rate dominates the quasi-potential at intermediate times**: for a path `φ` on `[0, T]`
and `t ≤ T`, some path on `[0, t]` from `x₀` ends at `φ(t)` with a Freidlin–Wentzell rate at most
that of `φ`. -/
@[tmio T, powerlib_foundation] theorem iInf_pushRate_le_of_le {m : ℕ} {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : (Fin m → ℝ) →L[ℝ] E) (x₀ : E) {T : ℝ≥0}
    (φ : C(Icc (0 : ℝ) T, E)) {t : ℝ≥0} (ht : t ≤ T) :
    ⨅ (T₁ : ℝ≥0) (ψ : C(Icc (0 : ℝ) T₁, E))
        (_ : ψ ⟨T₁, right_mem_Icc.mpr T₁.coe_nonneg⟩ = φ ⟨t, t.coe_nonneg, ht⟩),
        pushRate (solMap b N x₀) (schilderRate T₁) ψ ≤
      pushRate (solMap b N x₀) (schilderRate T) φ := by
  conv_rhs => unfold pushRate
  refine le_iInf₂ fun w hw => ?_
  refine (iInf₂_le t (solMap b N x₀ (restrictPath ht w))).trans ?_
  refine (iInf_le _ ?_).trans ((pushRate_le _ _ _).trans (schilderRate_restrictPath_le ht w))
  rw [← restrictPath_solMap hb, hw]
  rfl


/-- The event that the solution from `y` driven by `c B` stays in a closed `K` on `[0, T]` is
null-measurable, and its probability is `1 − P(it leaves K)`, computed on a version. -/
@[tmio T, powerlib_foundation] private theorem stay_version [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω) {T : ℝ≥0}
    (hT : 0 < (T : ℝ)) {L : ℝ≥0} {b : E → E} (hb : LipschitzWith L b)
    (N : (Fin 1 → ℝ) →L[ℝ] E) (y : E) (c : ℝ) {K : Set E} (hK : IsClosed K) :
    NullMeasurableSet {ω | ∀ t, solMap b N y (c • brownPath B hBc T ω) t ∈ K} P ∧
      P {ω | ∀ t, solMap b N y (c • brownPath B hBc T ω) t ∈ K} =
        1 - P {ω | ∃ t, solMap b N y (c • brownPath B hBc T ω) t ∉ K} := by
  let _ : MeasurableSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ) := borel _
  have : BorelSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ) := ⟨rfl⟩
  let _ : MeasurableSpace C(Icc (0 : ℝ) T, E) := borel _
  have : BorelSpace C(Icc (0 : ℝ) T, E) := ⟨rfl⟩
  obtain ⟨X, hX, -, hXB⟩ := exists_version (P := P) hB hT
  have hS : IsClosed {φ : C(Icc (0 : ℝ) T, E) | ∀ t, φ t ∈ K} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => hK.preimage (continuous_eval_const t)
  have hm : MeasurableSet {ω | solMap b N y (c • X ω) ∈ {φ : C(Icc (0 : ℝ) T, E) | ∀ t, φ t ∈ K}} :=
    ((continuous_solMap hb N y).comp (continuous_const_smul c)).measurable.comp hX hS.measurableSet
  have hae : {ω | ∀ t, solMap b N y (c • brownPath B hBc T ω) t ∈ K} =ᵐ[P]
      {ω | solMap b N y (c • X ω) ∈ {φ : C(Icc (0 : ℝ) T, E) | ∀ t, φ t ∈ K}} := by
    filter_upwards [brownPath_ae_eq hBc hXB] with ω hω
    simp only [hω]
  have hc : {ω | ∃ t, solMap b N y (c • brownPath B hBc T ω) t ∉ K} =
      {ω | ∀ t, solMap b N y (c • brownPath B hBc T ω) t ∈ K}ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, not_forall]
  refine ⟨hm.nullMeasurableSet.congr hae.symm, ?_⟩
  rw [hc, prob_compl_eq_one_sub₀ (hm.nullMeasurableSet.congr hae.symm),
    ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]

/-- **One Markov step**: with `q = inf_{y ∈ K} P(S(y, c B) leaves K on [0, T₂])`,
`P(stays on [0, T₁ + T₂]) ≤ (1 − q) P(stays on [0, T₁])`. -/
@[tmio T, powerlib_foundation] private theorem measure_stay_add_le [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω) {T₁ T₂ : ℝ≥0}
    (hT₁ : 0 < (T₁ : ℝ)) (hT₂ : 0 < (T₂ : ℝ)) {L : ℝ≥0} {b : E → E}
    (hb : LipschitzWith L b) (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) (c : ℝ) {K : Set E}
    (hK : IsClosed K) :
    P {ω | ∀ t, solMap b N x₀ (c • brownPath B hBc (T₁ + T₂) ω) t ∈ K} ≤
      (1 - ⨅ y ∈ K, P {ω | ∃ t, solMap b N y (c • brownPath B hBc T₂ ω) t ∉ K}) *
        P {ω | ∀ t, solMap b N x₀ (c • brownPath B hBc T₁ ω) t ∈ K} := by
  let _ : MeasurableSpace C(Icc (0 : ℝ) T₁, Fin 1 → ℝ) := borel _
  have : BorelSpace C(Icc (0 : ℝ) T₁, Fin 1 → ℝ) := ⟨rfl⟩
  let _ : MeasurableSpace C(Icc (0 : ℝ) T₂, Fin 1 → ℝ) := borel _
  have : BorelSpace C(Icc (0 : ℝ) T₂, Fin 1 → ℝ) := ⟨rfl⟩
  let _ : MeasurableSpace C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), Fin 1 → ℝ) := borel _
  have : BorelSpace C(Icc (0 : ℝ) (T₁ + T₂ : ℝ≥0), Fin 1 → ℝ) := ⟨rfl⟩
  let _ : MeasurableSpace C(Icc (0 : ℝ) T₁, E) := borel _
  have : BorelSpace C(Icc (0 : ℝ) T₁, E) := ⟨rfl⟩
  let _ : MeasurableSpace C(Icc (0 : ℝ) T₂, E) := borel _
  have : BorelSpace C(Icc (0 : ℝ) T₂, E) := ⟨rfl⟩
  have hT : 0 < ((T₁ + T₂ : ℝ≥0) : ℝ) := by push_cast; linarith
  obtain ⟨X, hX, -, hXB⟩ := exists_version (P := P) hB hT
  obtain ⟨X', hX', -, hXB'⟩ := exists_version (P := P) hB hT₂
  have hS : ∀ T : ℝ≥0, IsClosed {φ : C(Icc (0 : ℝ) T, E) | ∀ t, φ t ∈ K} := fun T => by
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => hK.preimage (continuous_eval_const t)
  set q := ⨅ y ∈ K, P {ω | ∃ t, solMap b N y (c • brownPath B hBc T₂ ω) t ∉ K} with hq_def
  have hq : ∀ y ∈ K, P {ω' | solMap b N y (c • X' ω') ∈ {φ : C(Icc (0 : ℝ) T₂, E) |
      ∀ t, φ t ∈ K}} ≤ 1 - q := by
    intro y hy
    have hae : {ω | ∀ t, solMap b N y (c • brownPath B hBc T₂ ω) t ∈ K} =ᵐ[P]
        {ω | solMap b N y (c • X' ω) ∈ {φ : C(Icc (0 : ℝ) T₂, E) | ∀ t, φ t ∈ K}} := by
      filter_upwards [brownPath_ae_eq hBc hXB'] with ω hω
      simp only [hω]
    rw [← measure_congr hae, (stay_version hB hBc hT₂ hb N y c hK).2]
    refine tsub_le_tsub_left ?_ 1
    exact iInf₂_le y hy
  have hmk := measure_solMap_markov_le hB hT₁ hT₂ hb N x₀ c hX hXB hX' hXB'
    (hS T₁).measurableSet (hS T₂).measurableSet (Kset := K)
    (fun φ hφ => hφ _) hq
  have hae1 : {ω | ∀ t, solMap b N x₀ (c • brownPath B hBc (T₁ + T₂) ω) t ∈ K} =ᵐ[P]
      {ω | restrictPath le_self_add (solMap b N x₀ (c • X ω)) ∈
          {φ : C(Icc (0 : ℝ) T₁, E) | ∀ t, φ t ∈ K} ∧
        restartPath T₁ T₂ (solMap b N x₀ (c • X ω)) ∈
          {φ : C(Icc (0 : ℝ) T₂, E) | ∀ t, φ t ∈ K}} := by
    filter_upwards [brownPath_ae_eq hBc hXB] with ω hω
    simp only [hω]
    exact propext (forall_mem_iff_restrict_restart _)
  have hae2 : {ω | restrictPath le_self_add (solMap b N x₀ (c • X ω)) ∈
      {φ : C(Icc (0 : ℝ) T₁, E) | ∀ t, φ t ∈ K}} =ᵐ[P]
        {ω | ∀ t, solMap b N x₀ (c • brownPath B hBc T₁ ω) t ∈ K} := by
    filter_upwards [brownPath_ae_eq hBc hXB] with ω hω
    show (∀ t, _) = (∀ t, _)
    rw [restrictPath_solMap hb, restrictPath_smul, ← hω, restrictPath_brownPath]
  rw [measure_congr hae1]
  exact hmk.trans_eq (by rw [measure_congr hae2])

/-- **Geometric survival bound**: for `x₀ ∈ K` (closed) and
`q = inf_{y ∈ K} P(S(y, c B) leaves K on [0, T])`,
`P(S(x₀, c B) stays in K on [0, (n + 1)T]) ≤ (1 − q)^{n+1}`. -/
@[tmio T, powerlib_foundation] theorem measure_stay_le_pow [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω) {T : ℝ≥0}
    (hT : 0 < (T : ℝ)) {L : ℝ≥0} {b : E → E} (hb : LipschitzWith L b)
    (N : (Fin 1 → ℝ) →L[ℝ] E) {x₀ : E} (c : ℝ) {K : Set E} (hK : IsClosed K) (hx₀ : x₀ ∈ K)
    (n : ℕ) :
    P {ω | ∀ t, solMap b N x₀ (c • brownPath B hBc ((n + 1) * T) ω) t ∈ K} ≤
      (1 - ⨅ y ∈ K, P {ω | ∃ t, solMap b N y (c • brownPath B hBc T ω) t ∉ K}) ^ (n + 1) := by
  induction n with
  | zero =>
    rw [show (((0 : ℕ) : ℝ≥0) + 1) * T = T by simp, pow_one,
      (stay_version hB hBc hT hb N x₀ c hK).2]
    refine tsub_le_tsub_left ?_ 1
    exact iInf₂_le x₀ hx₀
  | succ n ih =>
    have e : (((n + 1 : ℕ) : ℝ≥0) + 1) * T = ((n : ℝ≥0) + 1) * T + T := by push_cast; ring
    have hT₁ : 0 < (((n : ℝ≥0) + 1) * T : ℝ≥0) := by
      have : (0 : ℝ≥0) < T := by exact_mod_cast hT
      positivity
    rw [e, pow_succ, mul_comm _ (1 - _)]
    refine (measure_stay_add_le hB hBc (by exact_mod_cast hT₁) hT hb N x₀ c hK).trans ?_
    gcongr

/-- **Mean exit time by geometric trials**: for `x₀ ∈ K` (closed),
`E τ ≤ 2T/q`, `q = inf_{y ∈ K} P(S(y, c B) leaves K on [0, T])`. -/
@[tmio T, powerlib_foundation] theorem lintegral_exitTime_le [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω) {T : ℝ≥0}
    (hT : 0 < (T : ℝ)) {L : ℝ≥0} {b : E → E} (hb : LipschitzWith L b)
    (N : (Fin 1 → ℝ) →L[ℝ] E) {x₀ : E} (c : ℝ) {K : Set E} (hK : IsClosed K) (hx₀ : x₀ ∈ K) :
    ∫⁻ ω, exitTime b N x₀ K c B hBc ω ∂P ≤
      2 * T * (⨅ y ∈ K, P {ω | ∃ t, solMap b N y (c • brownPath B hBc T ω) t ∉ K})⁻¹ := by
  set q := ⨅ y ∈ K, P {ω | ∃ t, solMap b N y (c • brownPath B hBc T ω) t ∉ K} with hq_def
  set S : ℕ → Set Ω := fun n =>
    {ω | ∀ t, solMap b N x₀ (c • brownPath B hBc ((n + 1) * T) ω) t ∈ K} with hS_def
  have hSn : ∀ n, NullMeasurableSet (S n) P := fun n =>
    (stay_version hB hBc (by have : (0 : ℝ≥0) < T := by exact_mod_cast hT
                             exact_mod_cast (show (0 : ℝ≥0) < (n + 1) * T by positivity))
      hb N x₀ c hK).1
  -- the pointwise bound `τ ≤ T + Σ_n T 1_{S n}`
  have hpt : ∀ ω, exitTime b N x₀ K c B hBc ω ≤
      (T : ℝ≥0∞) + ∑' n, (T : ℝ≥0∞) * (S n).indicator 1 ω := by
    intro ω
    by_cases hall : ∀ n, ω ∈ S n
    · have : ∑' n, (T : ℝ≥0∞) * (S n).indicator 1 ω = ⊤ := by
        simp only [indicator_of_mem (hall _), Pi.one_apply, mul_one]
        exact ENNReal.tsum_const_eq_top_of_ne_zero (by
          have : (0 : ℝ≥0) < T := by exact_mod_cast hT
          exact_mod_cast this.ne')
      rw [this, add_top]
      exact le_top
    simp only [not_forall] at hall
    classical
    let m := Nat.find hall
    have hm : ω ∉ S m := Nat.find_spec hall
    have hlt : ∀ n < m, ω ∈ S n := fun n hn => by
      by_contra h
      exact Nat.find_min hall hn h
    obtain ⟨t, ht⟩ := not_forall.mp (show ¬ ∀ t, solMap b N x₀
      (c • brownPath B hBc ((m + 1) * T) ω) t ∈ K from hm)
    have h1 : exitTime b N x₀ K c B hBc ω ≤ ((m + 1 : ℕ) : ℝ≥0∞) * T := by
      refine (iInf_le _ (((m : ℝ≥0) + 1) * T)).trans ((iInf₂_le t ht).trans ?_)
      have ht' : (t : ℝ) ≤ (((m : ℝ≥0) + 1) * T : ℝ≥0) := t.2.2
      calc ENNReal.ofReal t ≤ ENNReal.ofReal ((((m : ℝ≥0) + 1) * T : ℝ≥0) : ℝ) :=
            ENNReal.ofReal_le_ofReal ht'
        _ = ((m + 1 : ℕ) : ℝ≥0∞) * T := by rw [ENNReal.ofReal_coe_nnreal]; push_cast; rfl
    refine h1.trans ?_
    have h2 : ∑ n ∈ Finset.range m, (T : ℝ≥0∞) * (S n).indicator 1 ω =
        (m : ℝ≥0∞) * T := by
      rw [Finset.sum_congr rfl fun n hn => by
        rw [indicator_of_mem (hlt n (Finset.mem_range.mp hn)), Pi.one_apply, mul_one]]
      simp
    calc ((m + 1 : ℕ) : ℝ≥0∞) * T = T + (m : ℝ≥0∞) * T := by push_cast; ring
      _ ≤ _ := add_le_add le_rfl (h2 ▸ ENNReal.sum_le_tsum _)
  have hmeas : ∀ n, AEMeasurable (fun ω => (T : ℝ≥0∞) * (S n).indicator 1 ω) P := fun n =>
    (aemeasurable_const.indicator₀ (hSn n)).const_mul _
  calc ∫⁻ ω, exitTime b N x₀ K c B hBc ω ∂P
      ≤ ∫⁻ ω, ((T : ℝ≥0∞) + ∑' n, (T : ℝ≥0∞) * (S n).indicator 1 ω) ∂P := lintegral_mono hpt
    _ = T + ∑' n, (T : ℝ≥0∞) * P (S n) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_tsum hmeas]
        congr 1
        refine tsum_congr fun n => ?_
        have h : AEMeasurable ((S n).indicator (1 : Ω → ℝ≥0∞)) P := by
          exact aemeasurable_const.indicator₀ (hSn n)
        rw [lintegral_const_mul'' _ h, lintegral_indicator_one₀ (hSn n)]
    _ ≤ T + ∑' n : ℕ, (T : ℝ≥0∞) * (1 - q) ^ (n + 1) := by
        gcongr with n
        exact measure_stay_le_pow hB hBc hT hb N c hK hx₀ n
    _ = T + T * ((1 - q) * (1 - (1 - q))⁻¹) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
    _ ≤ T * q⁻¹ + T * q⁻¹ := by
        have hq1 : q ≤ 1 := (iInf₂_le x₀ hx₀).trans prob_le_one
        rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hq1]
        gcongr
        · calc (T : ℝ≥0∞) = T * 1 := (mul_one _).symm
            _ ≤ T * q⁻¹ := by gcongr; exact ENNReal.one_le_inv.mpr hq1
        · calc (1 - q) * q⁻¹ ≤ 1 * q⁻¹ := by gcongr; exact tsub_le_self
            _ = q⁻¹ := one_mul _
    _ = 2 * T * q⁻¹ := by ring

/-- **Freidlin–Wentzell upper bound for the mean exit time**: for `K` compact, `x₀ ∈ K` and every
horizon `T > 0`, the exit time `τ_ε` of `S(x₀, √ε B)` from `K` satisfies
`limsup_{ε→0⁺} ε log E τ_ε ≤ sup_{x ∈ K} inf {J_x^T(φ) : φ leaves K on [0, T]}`, with
`J_x^T = pushRate (solMap b N x) (schilderRate T)` the Freidlin–Wentzell rate from `x`. -/
@[tmio T, powerlib_foundation] theorem limsup_log_lintegral_exitTime_le
    [IsProbabilityMeasure P] (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω)
    {K : Set E} (hK : IsCompact K) {x₀ : E} (hx₀ : x₀ ∈ K) {T : ℝ≥0} (hT : 0 < (T : ℝ))
    {L : ℝ≥0} {b : E → E} (hb : LipschitzWith L b) (N : (Fin 1 → ℝ) →L[ℝ] E) :
    limsup (fun ε : ℝ => (ε : EReal) *
        ENNReal.log (∫⁻ ω, exitTime b N x₀ K (√ε) B hBc ω ∂P)) (𝓝[>] 0) ≤
      (((⨆ x ∈ K, ⨅ φ ∈ {φ : C(Icc (0 : ℝ) T, E) | ∃ t, φ t ∉ K},
        pushRate (solMap b N x) (schilderRate T) φ : ℝ≥0∞)) : EReal) := by
  let _ : MeasurableSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ) := borel _
  have : BorelSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ) := ⟨rfl⟩
  obtain ⟨X, hX, -, hXB⟩ := exists_version (P := P) hB hT
  set V := ⨆ x ∈ K, ⨅ φ ∈ {φ : C(Icc (0 : ℝ) T, E) | ∃ t, φ t ∉ K},
    pushRate (solMap b N x) (schilderRate T) φ with hV
  have hO : IsOpen {φ : C(Icc (0 : ℝ) T, E) | ∃ t, φ t ∉ K} := by
    have : {φ : C(Icc (0 : ℝ) T, E) | ∃ t, φ t ∉ K} = ⋃ t, (fun φ => φ t) ⁻¹' Kᶜ := by
      ext φ; simp
    rw [this]
    exact isOpen_iUnion fun t => hK.isClosed.isOpen_compl.preimage (continuous_eval_const t)
  have hs : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ id ε :=
    eventually_nhdsWithin_of_forall fun ε hε => le_of_lt hε
  have hlow := (isLDP_schilder hB hT hX hXB).le_liminf_iInf_solMap hs hb N hK hO
  -- the probability of leaving, on the version and on the paths of `B`
  have hq : ∀ ε, 0 < ε → ⨅ x ∈ K, (P.map fun ω => √ε • X ω)
      (solMap b N x ⁻¹' {φ : C(Icc (0 : ℝ) T, E) | ∃ t, φ t ∉ K}) =
      ⨅ y ∈ K, P {ω | ∃ t, solMap b N y (√ε • brownPath B hBc T ω) t ∉ K} := by
    intro ε _
    refine iInf_congr fun y => iInf_congr fun _ => ?_
    rw [Measure.map_apply (show Measurable fun ω => √ε • X ω from hX.const_smul (√ε))
      ((hO.preimage (continuous_solMap hb N y)).measurableSet)]
    refine measure_congr ?_
    filter_upwards [brownPath_ae_eq hBc hXB] with ω hω
    simp only [mem_preimage, mem_ofPred_eq, hω]
  refine le_of_forall_gt_imp_ge_of_dense fun γ hγ => ?_
  induction γ using EReal.rec with
  | bot => exact absurd hγ (not_lt_bot)
  | top => exact le_top
  | coe γ =>
    obtain ⟨γ₀, hVγ₀, hγ₀γ⟩ := EReal.lt_iff_exists_real_btwn.mp hγ
    have hγ₀γ' : γ₀ < γ := by exact_mod_cast hγ₀γ
    -- eventually `q_ε ≥ e^{−γ₀/ε}`, hence `E τ_ε ≤ 2T e^{γ₀/ε}`
    have hlt : ((-γ₀ : ℝ) : EReal) < liminf (fun ε : ℝ => (id ε : EReal) * ENNReal.log
        (⨅ x ∈ K, (P.map fun ω => √ε • X ω)
          (solMap b N x ⁻¹' {φ : C(Icc (0 : ℝ) T, E) | ∃ t, φ t ∉ K}))) (𝓝[>] 0) := by
      refine lt_of_lt_of_le ?_ hlow
      rw [EReal.coe_neg]
      exact EReal.neg_lt_neg_iff.mpr hVγ₀
    have hev := eventually_lt_of_lt_liminf hlt
    have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε * Real.log (2 * T) < γ - γ₀ := by
      have hc : Tendsto (fun ε : ℝ => ε * Real.log (2 * T)) (𝓝 0) (𝓝 (0 * Real.log (2 * T))) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at hc
      exact (hc.eventually (gt_mem_nhds (by linarith))).filter_mono nhdsWithin_le_nhds
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [hev, hsmall, self_mem_nhdsWithin] with ε hε hεs (hε0 : 0 < ε)
    rw [id, hq ε hε0] at hε
    have hqe := exp_le_of_le_mul_log hε0 hε.le
    have hE := lintegral_exitTime_le hB hBc hT hb N (√ε) hK.isClosed hx₀
    have hbound : ∫⁻ ω, exitTime b N x₀ K (√ε) B hBc ω ∂P ≤
        ENNReal.ofReal (Real.exp ((γ₀ + ε * Real.log (2 * T)) / ε)) := by
      refine hE.trans ?_
      have hinv : (⨅ y ∈ K, P {ω | ∃ t, solMap b N y (√ε • brownPath B hBc T ω) t ∉ K})⁻¹ ≤
          (ENNReal.ofReal (Real.exp (-γ₀ / ε)))⁻¹ := ENNReal.inv_le_inv.mpr hqe
      refine (mul_le_mul_of_nonneg_left hinv (by positivity)).trans (le_of_eq ?_)
      have h2T : (0 : ℝ) < 2 * T := by positivity
      have e : Real.exp ((γ₀ + ε * Real.log (2 * T)) / ε) = 2 * T * Real.exp (-(-γ₀ / ε)) := by
        rw [add_div, mul_div_cancel_left₀ _ hε0.ne', Real.exp_add, Real.exp_log h2T, neg_div,
          neg_neg]
        ring
      rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg, e,
        ENNReal.ofReal_mul h2T.le, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
        ENNReal.ofReal_coe_nnreal]
    refine (mul_log_le_of_le_exp hε0 hbound).trans ?_
    exact_mod_cast (by linarith : γ₀ + ε * Real.log (2 * T) ≤ γ)

end Bounds

end powerlib.Stochastic.LDP
