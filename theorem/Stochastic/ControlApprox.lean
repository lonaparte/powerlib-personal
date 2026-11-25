import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.SchilderGood
import theorem.Stochastic.AdditiveVerification

/-! # Right-continuous approximation of square-integrable controls

The quasi-potential of `theorem/Stochastic/ControlledAction.lean` (`controlQuasiPotential`) is an
infimum over controls with a right derivative of the path at every time; the Freidlin–Wentzell
rate (`fwRate` of `theorem/Stochastic/AdditiveNoise.lean`) admits every square-integrable control.
This module supplies the approximation step between them: a square-integrable `v` on `[0, T]` is
the `L²` limit of right-continuous functions `g` (dyadic step functions plus a linear correction)
with the same first two moments, `∫₀ᵀ g = ∫₀ᵀ v` and `∫₀ᵀ ∫₀ᵗ g = ∫₀ᵀ ∫₀ᵗ v`. For a mechanical
system `q̇ = c p`, `ṗ = f(q, p) + σ u` (noise in the momentum row only) these moments are the two
endpoints, so the approximation keeps both endpoints exactly
(`theorem/Stochastic/MomentumNoise.lean`, `theorem/Stochastic/FilterNoise.lean`).

Scope.
* Analysis on `[0, T]`, `T > 0`. `L²` convergence of the dyadic derivatives `u_m` of `W = ∫ v`:
  `∫ u_m v = ∫ u_m²` and the closure lemma `schilderRate_le_of_energy` give
  `∫ (u_m − v)² = ∫ v² − ∫ u_m² → 0`.

Source: M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 3 §2 and Ch. 4 §1 (the action functional on absolutely continuous paths, its infimum attained
along regular paths); A. Dembo, O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd
ed. (1998), §5.2 (Cameron–Martin space).

Results.
* `continuousWithinAt_indicator_Ico`, `continuousWithinAt_stepDeriv` (right-continuity),
  `measurable_stepDeriv`, `integral_stepDeriv_mul_of_primitive` (`∫ u_n f = Σ_k y_k²` for
  `x = ∫ f`), `exists_integral_sq_sub_stepDeriv_lt` (**`L²` convergence**),
  `exists_rc_approx` (**right-continuous approximation with two moments**).
* `pathExt_solMap_of_primitive`: the solution driven by `w = ∫ u` as an integral equation.
* `integral_one_sub_two_mul_div`, `sq_integral_sub_le` (primitive error bound),
  `integral_sq_le_add` (`∫ f² ≤ (1 + θ) ∫ g² + (1 + 1/θ) ∫ (f − g)²`).
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

variable {T : ℝ≥0}

/-! ## The dyadic step derivatives -/

/-- The indicator of `[a, b)` with a constant value is right-continuous. -/
@[tmio T, powerlib_foundation] theorem continuousWithinAt_indicator_Ico (a b c t : ℝ) :
    ContinuousWithinAt ((Ico a b).indicator fun _ => c) (Ioi t) t := by
  by_cases h1 : t < a
  · have hev : ((Ico a b).indicator fun _ => c) =ᶠ[𝓝[>] t] fun _ => (0 : ℝ) := by
      filter_upwards [Ioo_mem_nhdsGT h1] with s hs
      exact indicator_of_notMem (fun h => absurd h.1 (not_le.mpr hs.2)) _
    exact continuousWithinAt_const.congr_of_eventuallyEq hev
      (indicator_of_notMem (fun h => absurd h.1 (not_le.mpr h1)) _)
  push Not at h1
  by_cases h2 : t < b
  · have hev : ((Ico a b).indicator fun _ => c) =ᶠ[𝓝[>] t] fun _ => c := by
      filter_upwards [Ioo_mem_nhdsGT h2] with s hs
      exact indicator_of_mem (show s ∈ Ico a b from ⟨h1.trans hs.1.le, hs.2⟩) _
    exact continuousWithinAt_const.congr_of_eventuallyEq hev
      (indicator_of_mem (show t ∈ Ico a b from ⟨h1, h2⟩) _)
  push Not at h2
  have hev : ((Ico a b).indicator fun _ => c) =ᶠ[𝓝[>] t] fun _ => (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr (h2.trans (le_of_lt hs)))) _
  exact continuousWithinAt_const.congr_of_eventuallyEq hev
    (indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr h2)) _)

/-- The step derivative `u_n` is right-continuous everywhere. -/
@[tmio T, powerlib_foundation] theorem continuousWithinAt_stepDeriv (n : ℕ)
    (x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) (t : ℝ) :
    ContinuousWithinAt (stepDeriv T n x) (Ioi t) t := by
  unfold stepDeriv
  exact tendsto_finsetSum _ fun k _ => continuousWithinAt_indicator_Ico _ _ _ t

@[tmio T, powerlib_foundation] theorem measurable_stepDeriv (n : ℕ)
    (x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) : Measurable (stepDeriv T n x) := by
  unfold stepDeriv
  exact Finset.measurable_sum _ fun k _ => measurable_const.indicator measurableSet_Ico

/-- **The step derivative against an integrand**: if `x(t) = ∫₀ᵗ f` on `[0, T]`, then
`∫₀ᵀ u_n f = Σ_k y_k²` (`y` the node increments of `x`, so this is `∫₀ᵀ u_n²`). -/
@[tmio T, powerlib_foundation] theorem integral_stepDeriv_mul_of_primitive (hT : 0 < (T : ℝ))
    {n : ℕ} (hn : 0 < n) (x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 T)
    (hxf : ∀ t ∈ Icc (0 : ℝ) T, pathExt x t 0 = ∫ s in (0 : ℝ)..t, f s) :
    ∫ s in (0 : ℝ)..T, stepDeriv T n x s * f s = ∑ k : Fin n, nodeIncr T n x k ^ 2 := by
  have hΔ := mesh_pos hT hn
  have hsΔ := Real.sqrt_pos.mpr hΔ
  have hT0 := T.coe_nonneg
  have hTn : (T : ℝ) = n * mesh T n := by rw [mesh]; field_simp
  have e : (fun s => stepDeriv T n x s * f s) = fun s =>
      ∑ k : Fin n, (Ico ((k : ℕ) * mesh T n) ((k : ℕ) * mesh T n + mesh T n)).indicator
        (fun _ => nodeIncr T n x k / √(mesh T n)) s * f s := by
    funext s; rw [stepDeriv, Finset.sum_mul]
  rw [e, intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    have hk : ((k : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast k.2
    have hb : ((k : ℕ) : ℝ) * mesh T n + mesh T n ≤ T := by rw [hTn]; nlinarith
    have hk0 : (0 : ℝ) ≤ (k : ℕ) * mesh T n := by positivity
    have hmem1 : ((k : ℕ) : ℝ) * mesh T n + mesh T n ∈ Icc (0 : ℝ) T := ⟨by positivity, hb⟩
    have hmem0 : ((k : ℕ) : ℝ) * mesh T n ∈ Icc (0 : ℝ) T := ⟨hk0, by linarith⟩
    have hsub : ∀ t ∈ Icc (0 : ℝ) T, uIcc (0 : ℝ) t ⊆ uIcc 0 T := fun t ht => by
      rw [uIcc_of_le ht.1, uIcc_of_le hT0]; exact Icc_subset_Icc_right ht.2
    rw [integral_indicator_mul _ hk0 (by linarith) hb,
      ← intervalIntegral.integral_interval_sub_left (hf.mono_set (hsub _ hmem1))
        (hf.mono_set (hsub _ hmem0)), ← hxf _ hmem1, ← hxf _ hmem0]
    have hy : pathExt x (((k : ℕ) : ℝ) * mesh T n + mesh T n) 0 -
        pathExt x (((k : ℕ) : ℝ) * mesh T n) 0 = √(mesh T n) * nodeIncr T n x k := by
      rw [nodeIncr, mul_div_cancel₀ _ hsΔ.ne', coe_node, coe_node]
      push_cast; ring_nf
    rw [hy]
    field_simp
  · intro k _
    have e2 : (fun s => (Ico ((k : ℕ) * mesh T n) ((k : ℕ) * mesh T n + mesh T n)).indicator
          (fun _ => nodeIncr T n x k / √(mesh T n)) s * f s) =
        fun s => nodeIncr T n x k / √(mesh T n) *
          (Ico ((k : ℕ) * mesh T n) ((k : ℕ) * mesh T n + mesh T n)).indicator f s := by
      funext s
      by_cases hs : s ∈ Ico ((k : ℕ) * mesh T n) ((k : ℕ) * mesh T n + mesh T n)
      · rw [indicator_of_mem hs, indicator_of_mem hs]
      · rw [indicator_of_notMem hs, indicator_of_notMem hs]; ring
    rw [e2]
    exact ⟨(hf.1.indicator measurableSet_Ico).const_mul _,
      (hf.2.indicator measurableSet_Ico).const_mul _⟩

/-- **`L²` convergence of the dyadic derivatives**: if `x(t) = ∫₀ᵗ v` on `[0, T]` with `v`
square integrable, then `∫₀ᵀ (u_m − v)² = ∫₀ᵀ v² − ∫₀ᵀ u_m²` and it is `< η` for some `m` (the
closure lemma `schilderRate_le_of_energy` and `schilderRate_eq`). -/
@[tmio T, powerlib_foundation] theorem exists_integral_sq_sub_stepDeriv_lt (hT : 0 < (T : ℝ))
    (x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) {v : ℝ → ℝ} (hv : IntervalIntegrable v volume 0 T)
    (hv2 : IntervalIntegrable (fun s => v s ^ 2) volume 0 T)
    (hxv : ∀ t ∈ Icc (0 : ℝ) T, pathExt x t 0 = ∫ s in (0 : ℝ)..t, v s) {η : ℝ} (hη : 0 < η) :
    ∃ m : ℕ, ∫ s in (0 : ℝ)..T, (stepDeriv T (2 ^ m) x s - v s) ^ 2 < η := by
  have hT0 := T.coe_nonneg
  set S : ℕ → ℝ := fun m => ∑ k : Fin (2 ^ m), nodeIncr T (2 ^ m) x k ^ 2 with hS
  set E := ∫ s in (0 : ℝ)..T, v s ^ 2 with hE
  have hpos : ∀ m, 0 < 2 ^ m := fun m => by positivity
  have hdiff : ∀ m, ∫ s in (0 : ℝ)..T, (stepDeriv T (2 ^ m) x s - v s) ^ 2 = E - S m := by
    intro m
    have h1 := intervalIntegrable_sq_stepDeriv hT (hpos m) x 0 T
    have h3 := intervalIntegrable_stepDeriv_mul (2 ^ m) x hv
    have e : (fun s => (stepDeriv T (2 ^ m) x s - v s) ^ 2) = fun s =>
        (stepDeriv T (2 ^ m) x s ^ 2 - 2 * (stepDeriv T (2 ^ m) x s * v s)) + v s ^ 2 := by
      funext s; ring
    rw [e, intervalIntegral.integral_add (h1.sub (h3.const_mul 2)) hv2,
      intervalIntegral.integral_sub h1 (h3.const_mul 2), intervalIntegral.integral_const_mul,
      integral_sq_stepDeriv hT (hpos m) x,
      integral_stepDeriv_mul_of_primitive hT (hpos m) x hv hxv]
    simp only [hS, hE]; ring
  have hSE : ∀ m, S m ≤ E := fun m => by
    have := intervalIntegral.integral_nonneg (μ := volume) hT0 fun s _ =>
      sq_nonneg (stepDeriv T (2 ^ m) x s - v s)
    rw [hdiff] at this; linarith
  have hbdd : BddAbove (range S) := ⟨E, by rintro _ ⟨m, rfl⟩; exact hSE m⟩
  have hx0 : pathExt x 0 0 = 0 := by rw [hxv 0 ⟨le_rfl, hT0⟩]; simp
  have hS0 : 0 ≤ ⨆ m, S m :=
    (Finset.sum_nonneg fun k _ => sq_nonneg _).trans (le_ciSup hbdd 0)
  have hcl := schilderRate_le_of_energy hT x hx0 (a := (⨆ m, S m) / 2) fun m => by
    rw [← Finset.sum_div]; exact div_le_div_of_nonneg_right (le_ciSup hbdd m) two_pos.le
  set U : ℝ → Fin 1 → ℝ := fun s => v s • fun _ => (1 : ℝ) with hU
  have hUi : IntervalIntegrable U volume 0 T := ⟨hv.1.smul_const _, hv.2.smul_const _⟩
  have hUsq : (fun s => ∑ j, U s j ^ 2) = fun s => v s ^ 2 := by funext s; simp [hU]
  have hU2 : IntervalIntegrable (fun s => ∑ j, U s j ^ 2) volume 0 T := by rw [hUsq]; exact hv2
  have hxU : ∀ t : Icc (0 : ℝ) T, x t = ∫ s in (0 : ℝ)..t, U s := by
    intro t
    rw [intervalIntegral.integral_smul_const, ← hxv t t.2, pathExt_of_mem x t.2]
    funext j; fin_cases j; simp
  rw [schilderRate_eq hUi hU2 hxU] at hcl
  unfold controlAction at hcl
  rw [hUsq] at hcl
  have hle : 1 / 2 * E ≤ (⨆ m, S m) / 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcl
  obtain ⟨m, hm⟩ := exists_lt_of_lt_ciSup (show E - η < ⨆ m, S m by linarith)
  exact ⟨m, by rw [hdiff]; linarith⟩

/-- The linear correction `h(s) = 1 − 2s/T` has the primitive `s − s²/T`. -/
@[tmio T, powerlib_foundation] theorem integral_one_sub_two_mul_div (T t : ℝ) :
    ∫ s in (0 : ℝ)..t, (1 - 2 * s / T) = t - t ^ 2 / T := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) t, HasDerivAt (fun s : ℝ => s - s ^ 2 / T) (1 - 2 * s / T) s := by
    intro s _
    have := ((hasDerivAt_id' s).sub ((hasDerivAt_pow 2 s).div_const (T : ℝ)))
    convert this using 1
    norm_num
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous fun s : ℝ =>
    1 - 2 * s / T).intervalIntegrable 0 t)]
  simp

/-- **Right-continuous approximation with two moments**: a square-integrable `v` on `[0, T]` is
approximated in `L²` (`∫₀ᵀ (g − v)² ≤ η`) by a measurable, right-continuous, locally square
integrable `g` (a dyadic step function plus a multiple of `1 − 2s/T`) with `∫₀ᵀ g = ∫₀ᵀ v` and
`∫₀ᵀ ∫₀ᵗ g = ∫₀ᵀ ∫₀ᵗ v`. -/
@[tmio T, powerlib_foundation] theorem exists_rc_approx (hT : 0 < (T : ℝ)) {v : ℝ → ℝ}
    (hv : IntervalIntegrable v volume 0 T)
    (hv2 : IntervalIntegrable (fun s => v s ^ 2) volume 0 T) {η : ℝ} (hη : 0 < η) :
    ∃ g : ℝ → ℝ, Measurable g ∧ (∀ t, ContinuousWithinAt g (Ioi t) t) ∧
      (∀ a b, IntervalIntegrable g volume a b) ∧
      (∀ a b, IntervalIntegrable (fun s => g s ^ 2) volume a b) ∧
      ∫ s in (0 : ℝ)..T, g s = ∫ s in (0 : ℝ)..T, v s ∧
      ∫ t in (0 : ℝ)..T, (∫ s in (0 : ℝ)..t, g s) =
        ∫ t in (0 : ℝ)..T, (∫ s in (0 : ℝ)..t, v s) ∧
      IntervalIntegrable (fun s => (g s - v s) ^ 2) volume 0 T ∧
      ∫ s in (0 : ℝ)..T, (g s - v s) ^ 2 ≤ η := by
  have hT0 := T.coe_nonneg
  have hIcc : uIcc (0 : ℝ) T = Icc (0 : ℝ) T := uIcc_of_le hT0
  -- the primitive of `v` as a path
  set U : ℝ → Fin 1 → ℝ := fun s => v s • fun _ => (1 : ℝ) with hU
  have hUi : IntervalIntegrable U volume 0 T := ⟨hv.1.smul_const _, hv.2.smul_const _⟩
  obtain ⟨W, hW⟩ := exists_primitive_path (T := T) hUi
  have hxv : ∀ t ∈ Icc (0 : ℝ) T, pathExt W t 0 = ∫ s in (0 : ℝ)..t, v s := by
    intro t ht
    rw [pathExt_of_mem W ht, hW, intervalIntegral.integral_smul_const]
    simp
  obtain ⟨m, hm⟩ := exists_integral_sq_sub_stepDeriv_lt hT W hv hv2 hxv
    (show (0 : ℝ) < η / 74 by positivity)
  have hn : 0 < 2 ^ m := by positivity
  set u := stepDeriv T (2 ^ m) W with hu
  set e := ∫ s in (0 : ℝ)..T, (u s - v s) ^ 2 with he
  have hui : ∀ a b, IntervalIntegrable u volume a b := intervalIntegrable_stepDeriv _ W
  have hu2 : ∀ a b, IntervalIntegrable (fun s => u s ^ 2) volume a b :=
    intervalIntegrable_sq_stepDeriv hT hn W
  have huv : IntervalIntegrable (fun s => u s * v s) volume 0 T :=
    intervalIntegrable_stepDeriv_mul _ W hv
  have hsq : IntervalIntegrable (fun s => (u s - v s) ^ 2) volume 0 T := by
    have e1 : (fun s => (u s - v s) ^ 2) = fun s =>
        (u s ^ 2 - 2 * (u s * v s)) + v s ^ 2 := by funext s; ring
    rw [e1]; exact ((hu2 0 T).sub (huv.const_mul 2)).add hv2
  have hsub : ∀ t ∈ Icc (0 : ℝ) T, uIcc (0 : ℝ) t ⊆ uIcc 0 T := fun t ht => by
    rw [uIcc_of_le ht.1, hIcc]; exact Icc_subset_Icc_right ht.2
  -- the primitive error `D(t) = ∫₀ᵗ (u − v)`, `D(t)² ≤ T e`
  set D : ℝ → ℝ := fun t => (∫ s in (0 : ℝ)..t, u s) - ∫ s in (0 : ℝ)..t, v s with hD
  have hDb : ∀ t ∈ Icc (0 : ℝ) T, D t ^ 2 ≤ T * e := by
    intro t ht
    have hvt := hv.mono_set (hsub t ht)
    simp only [hD]
    rw [← intervalIntegral.integral_sub (hui 0 t) hvt]
    calc _ ≤ (t - 0) * ∫ s in (0 : ℝ)..t, (u s - v s) ^ 2 :=
          sq_integral_le ht.1 ((hui 0 t).sub hvt) (hsq.mono_set (hsub t ht))
      _ ≤ T * e := by
          refine mul_le_mul (by linarith [ht.2]) ?_
            (intervalIntegral.integral_nonneg ht.1 fun s _ => sq_nonneg _) hT0
          exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
            (Eventually.of_forall fun s => sq_nonneg _) hsq
  have hVc : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, v s) (uIcc 0 T) :=
    intervalIntegral.continuousOn_primitive_interval' hv left_mem_uIcc
  have hUc : Continuous fun t => ∫ s in (0 : ℝ)..t, u s :=
    intervalIntegral.continuous_primitive hui 0
  have hDc : ContinuousOn D (uIcc 0 T) := hUc.continuousOn.sub hVc
  have hDi : IntervalIntegrable D volume 0 T := hDc.intervalIntegrable
  have hD2 : IntervalIntegrable (fun t => D t ^ 2) volume 0 T := (hDc.pow 2).intervalIntegrable
  set I := ∫ t in (0 : ℝ)..T, D t with hI
  have hIb : I ^ 2 ≤ T ^ 3 * e := by
    calc I ^ 2 ≤ (T - 0) * ∫ t in (0 : ℝ)..T, D t ^ 2 := sq_integral_le hT0 hDi hD2
      _ ≤ (T - 0) * ∫ t in (0 : ℝ)..T, (T * e) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          exact intervalIntegral.integral_mono_on hT0 hD2 intervalIntegrable_const hDb
      _ = T ^ 3 * e := by simp; ring
  -- the correction
  set c : ℝ := -(6 * I / T ^ 2) with hc
  set h : ℝ → ℝ := fun s => 1 - 2 * s / T with hh
  have hhc : Continuous h := by fun_prop
  have hh1 : ∀ s ∈ Icc (0 : ℝ) T, h s ^ 2 ≤ 1 := by
    intro s hs
    have h1 : 2 * s / T ≤ 2 := by rw [div_le_iff₀ hT]; linarith [hs.2]
    have h2 : 0 ≤ 2 * s / T := by have := hs.1; positivity
    simp only [hh]; nlinarith
  have hc2 : c ^ 2 * T ≤ 36 * e := by
    have he0 : 0 ≤ e := intervalIntegral.integral_nonneg hT0 fun s _ => sq_nonneg _
    have : c ^ 2 * T = 36 * I ^ 2 / T ^ 3 := by simp only [hc]; field_simp; ring
    rw [this, div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨fun s => u s + c * h s, (measurable_stepDeriv _ W).add
      (measurable_const.mul hhc.measurable), fun t => (continuousWithinAt_stepDeriv _ W t).add
      (continuousWithinAt_const.mul hhc.continuousWithinAt),
    fun a b => (hui a b).add (hhc.intervalIntegrable a b |>.const_mul c), fun a b => ?_, ?_, ?_,
    ?_⟩
  · have e1 : (fun s => (u s + c * h s) ^ 2) = fun s =>
        u s ^ 2 + 2 * c * (u s * h s) + c ^ 2 * h s ^ 2 := by funext s; ring
    rw [e1]
    exact ((hu2 a b).add ((intervalIntegrable_stepDeriv_mul _ W
      (hhc.intervalIntegrable a b)).const_mul _)).add
        ((hhc.pow 2).intervalIntegrable a b |>.const_mul _)
  · -- first moment
    have hTn : (T : ℝ) = ((2 ^ m : ℕ) : ℝ) * mesh T (2 ^ m) := by rw [mesh]; field_simp
    have hx0 : pathExt W 0 0 = 0 := by rw [hxv 0 ⟨le_rfl, hT0⟩]; simp
    have h1 : ∫ s in (0 : ℝ)..T, u s = pathExt W T 0 := by
      have := integral_stepDeriv_node hT W hx0 (le_refl m) (j := 2 ^ m) le_rfl
      rwa [← hTn] at this
    rw [intervalIntegral.integral_add (hui 0 T) (hhc.intervalIntegrable 0 T |>.const_mul c),
      intervalIntegral.integral_const_mul, integral_one_sub_two_mul_div, h1,
      hxv T ⟨hT0, le_rfl⟩]
    field_simp
    ring
  · -- second moment
    have e1 : (fun t => ∫ s in (0 : ℝ)..t, (u s + c * h s)) = fun t =>
        ((∫ s in (0 : ℝ)..t, v s) + D t) + c * (t - t ^ 2 / T) := by
      funext t
      rw [intervalIntegral.integral_add (hui 0 t) (hhc.intervalIntegrable 0 t |>.const_mul c),
        intervalIntegral.integral_const_mul, integral_one_sub_two_mul_div]
      simp only [hD]; ring
    have hpoly : ∫ t in (0 : ℝ)..T, (t - t ^ 2 / T) = T ^ 2 / 6 := by
      have hd : ∀ s ∈ uIcc (0 : ℝ) T, HasDerivAt (fun s : ℝ => s ^ 2 / 2 - s ^ 3 / (3 * T))
          (s - s ^ 2 / T) s := by
        intro s _
        have := ((hasDerivAt_pow 2 s).div_const 2).sub ((hasDerivAt_pow 3 s).div_const (3 * T))
        convert this using 1
        norm_num
        field_simp
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous
        fun s : ℝ => s - s ^ 2 / T).intervalIntegrable 0 T)]
      field_simp; ring
    rw [e1, intervalIntegral.integral_add (hVc.intervalIntegrable.add hDi)
        ((by fun_prop : Continuous fun t : ℝ => t - t ^ 2 / T).intervalIntegrable 0 T
          |>.const_mul c),
      intervalIntegral.integral_add hVc.intervalIntegrable hDi, intervalIntegral.integral_const_mul,
      hpoly, ← hI]
    simp only [hc]
    field_simp
    ring
  · -- the `L²` error
    have hvh : IntervalIntegrable (fun s => v s * h s) volume 0 T :=
      hv.mul_continuousOn hhc.continuousOn
    have huh : IntervalIntegrable (fun s => u s * h s) volume 0 T :=
      intervalIntegrable_stepDeriv_mul _ W (hhc.intervalIntegrable 0 T)
    have e1 : (fun s => (u s + c * h s - v s) ^ 2) = fun s =>
        (u s - v s) ^ 2 + 2 * c * (u s * h s) - 2 * c * (v s * h s) + c ^ 2 * h s ^ 2 := by
      funext s; ring
    have hL : IntervalIntegrable (fun s => (u s + c * h s - v s) ^ 2) volume 0 T := by
      rw [e1]
      exact ((hsq.add (huh.const_mul _)).sub (hvh.const_mul _)).add
        ((hhc.pow 2).intervalIntegrable 0 T |>.const_mul _)
    refine ⟨hL, ?_⟩
    calc ∫ s in (0 : ℝ)..T, (u s + c * h s - v s) ^ 2
        ≤ ∫ s in (0 : ℝ)..T, (2 * (u s - v s) ^ 2 + 2 * c ^ 2) := by
          refine intervalIntegral.integral_mono_on hT0 hL
            ((hsq.const_mul 2).add intervalIntegrable_const) fun s hs => ?_
          have := hh1 s hs
          nlinarith [sq_nonneg (u s - v s - c * h s), sq_nonneg c]
      _ = 2 * e + 2 * c ^ 2 * T := by
          rw [intervalIntegral.integral_add (hsq.const_mul 2) intervalIntegrable_const,
            intervalIntegral.integral_const_mul]
          simp; ring
      _ ≤ η := by linarith

/-! ## Elementary estimates and the solution as an integral equation -/

/-- **Primitive error bound**: `(∫₀ᵗ f₁ − ∫₀ᵗ f₂)² ≤ T ∫₀ᵀ (f₁ − f₂)²` for `t ∈ [0, T]`. -/
@[tmio T, powerlib_foundation] theorem sq_integral_sub_le {f₁ f₂ : ℝ → ℝ}
    (hf₁ : IntervalIntegrable f₁ volume 0 T) (hf₂ : IntervalIntegrable f₂ volume 0 T)
    (hf : IntervalIntegrable (fun s => (f₁ s - f₂ s) ^ 2) volume 0 T) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    ((∫ s in (0 : ℝ)..t, f₁ s) - ∫ s in (0 : ℝ)..t, f₂ s) ^ 2 ≤
      T * ∫ s in (0 : ℝ)..T, (f₁ s - f₂ s) ^ 2 := by
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 T := by
    rw [uIcc_of_le ht.1, uIcc_of_le T.coe_nonneg]; exact Icc_subset_Icc_right ht.2
  rw [← intervalIntegral.integral_sub (hf₁.mono_set hsub) (hf₂.mono_set hsub)]
  calc _ ≤ (t - 0) * ∫ s in (0 : ℝ)..t, (f₁ s - f₂ s) ^ 2 :=
        sq_integral_le ht.1 ((hf₁.mono_set hsub).sub (hf₂.mono_set hsub)) (hf.mono_set hsub)
    _ ≤ T * ∫ s in (0 : ℝ)..T, (f₁ s - f₂ s) ^ 2 := by
        refine mul_le_mul (by linarith [ht.2]) ?_
          (intervalIntegral.integral_nonneg ht.1 fun s _ => sq_nonneg _) T.coe_nonneg
        exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
          (Eventually.of_forall fun s => sq_nonneg _) hf

/-- **Young's inequality in `L²`**: `∫ f² ≤ (1 + θ) ∫ g² + (1 + 1/θ) ∫ (f − g)²`, `θ > 0`. -/
@[tmio T, powerlib_foundation] theorem integral_sq_le_add {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable (fun s => f s ^ 2) volume a b)
    (hg : IntervalIntegrable (fun s => g s ^ 2) volume a b)
    (hfg : IntervalIntegrable (fun s => (f s - g s) ^ 2) volume a b) {θ : ℝ} (hθ : 0 < θ) :
    ∫ s in a..b, f s ^ 2 ≤
      (1 + θ) * (∫ s in a..b, g s ^ 2) + (1 + 1 / θ) * ∫ s in a..b, (f s - g s) ^ 2 := by
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (hg.const_mul _) (hfg.const_mul _)]
  refine intervalIntegral.integral_mono_on hab hf ((hg.const_mul _).add (hfg.const_mul _))
    fun s _ => ?_
  have key : (1 + θ) * g s ^ 2 + (1 + 1 / θ) * (f s - g s) ^ 2 - f s ^ 2 =
      (θ * g s - (f s - g s)) ^ 2 / θ := by
    field_simp; ring
  have : 0 ≤ (θ * g s - (f s - g s)) ^ 2 / θ := by positivity
  linarith

section Solution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The solution driven by a primitive** is an integral equation: for `w = ∫ u`,
`x(t) = x₀ + ∫₀ᵗ (N u + b(x))` on `[0, T]`. -/
@[tmio T, powerlib_foundation] theorem pathExt_solMap_of_primitive {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : F →L[ℝ] E) (x₀ : E) {u : ℝ → F}
    (hu : IntervalIntegrable u volume 0 T) {w : C(Icc (0 : ℝ) T, F)}
    (hw : ∀ t : Icc (0 : ℝ) T, w t = ∫ s in (0 : ℝ)..t, u s) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    pathExt (solMap b N x₀ w) t =
      x₀ + ∫ s in (0 : ℝ)..t, (N (u s) + b (pathExt (solMap b N x₀ w) s)) := by
  have hspec := solMap_spec hb N x₀ w
  generalize hx : solMap b N x₀ w = x at hspec ⊢
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 T := by
    rw [uIcc_of_le ht.1, uIcc_of_le T.coe_nonneg]; exact Icc_subset_Icc_right ht.2
  have hus : IntervalIntegrable u volume 0 t := hu.mono_set hsub
  have hNus : IntervalIntegrable (fun r => N (u r)) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
      (N.integrable_comp ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mp hus))
  have hbx : Continuous fun r => b (pathExt x r) := hb.continuous.comp (continuous_pathExt x)
  rw [pathExt_of_mem x ht, hspec, hw, intervalIntegral.integral_add hNus
    (hbx.intervalIntegrable _ _), ← N.intervalIntegral_comp_comm hus]
  abel

end Solution

end powerlib.Stochastic.LDP
