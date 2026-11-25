import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.SchilderRate
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-! # The Schilder rate is a good rate function

`I(x) = ½ ∫₀ᵀ ẋ²` on `H¹₀` (`∞` elsewhere, `schilderRate`) is lower semicontinuous on
`C([0, T])` and its sublevel sets are compact. The key step identifies `I` through the dyadic
polygonal energies `E_m(x) = Σ_k (Δ_k x)²/(2Δ_m)` (`Δ_m = T/2^m`): if `x(0) = 0` and
`E_m(x) ≤ a` for every `m`, the derivatives `u_m` of the dyadic interpolations form a Cauchy
sequence in `L²(0, T)` (`‖u_{m'} − u_m‖² = 2(E_{m'} − E_m)` for `m ≤ m'`), whose limit `u`
satisfies `x = ∫ u` and `½ ∫ u² ≤ a`. Compactness is then Arzelà–Ascoli (`I(x) ≤ b` gives
`|x(t) − x(s)|² ≤ 2(b + 1)|t − s|`).

Scope.
* Analysis on `C([0, T], ℝ)` (written `C([0, T], Fin 1 → ℝ)`), `T > 0`; not an engineering
  result. `L²` is Mathlib's `Lp ℝ 2` on `(0, T]`.

Source: A. Dembo, O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed. (1998),
proof of Thm 5.2.3 (the rate of Schilder's theorem is good, via Arzelà–Ascoli); D. Stroock,
*An Introduction to the Theory of Large Deviations* (1984), §1.3 (the dyadic energies).

Results.
* `stepDeriv` (derivative of the `n`-step interpolation), `integral_stepDeriv`
  (`∫₀ᵗ u_n = π_n x(t)`), `integral_sq_stepDeriv` (`∫₀ᵀ u_n² = Σ_k y_k²`),
  `integral_indicator_mul`, `integral_stepDeriv_mul` (`∫ u_m u_{m'} = ∫ u_m²`, `m ≤ m'`),
  `integral_sq_sub_stepDeriv` (`∫ (u_{m'} − u_m)² = ∫ u_{m'}² − ∫ u_m²`), `norm_sq_toLp`,
  `integral_stepDeriv_node`.
* `schilderRate_le_of_energy` (**closure lemma**: bounded dyadic energies and `x(0) = 0` give
  `I(x) ≤ a`), `pathExt_zero_of_schilderRate_ne_top`, `energy_le_of_schilderRate`,
  `schilderRate_preimage_Iic` (`{I ≤ b} = {x(0) = 0} ∩ ⋂_m {E_m ≤ b}`),
  `isClosed_schilderRate_le`, `lowerSemicontinuous_schilderRate`, `sq_sub_le_of_schilderRate`
  (Hölder bound), `isGoodRate_schilderRate` (**the Schilder rate is good**).
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

variable {T : ℝ≥0}

/-- Derivative of the `n`-step polygonal interpolation of `x`: the step function with value
`y_k/√Δ` on `[kΔ, (k+1)Δ)`, `y = nodeIncr T n x`. -/
def stepDeriv (T : ℝ≥0) (n : ℕ) (x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) (s : ℝ) : ℝ :=
  ∑ k : Fin n, (Ico ((k : ℕ) * mesh T n) ((k : ℕ) * mesh T n + mesh T n)).indicator
    (fun _ => nodeIncr T n x k / √(mesh T n)) s

@[tmio T, powerlib_foundation] theorem intervalIntegrable_stepDeriv (n : ℕ)
    (x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) (a b : ℝ) :
    IntervalIntegrable (stepDeriv T n x) volume a b :=
  intervalIntegrable_steps _ a b

@[tmio T, powerlib_foundation] theorem sq_stepDeriv (hT : 0 < (T : ℝ)) {n : ℕ} (hn : 0 < n)
    (x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) (s : ℝ) :
    stepDeriv T n x s ^ 2 = ∑ k : Fin n,
      (Ico ((k : ℕ) * mesh T n) ((k : ℕ) * mesh T n + mesh T n)).indicator
        (fun _ => (nodeIncr T n x k / √(mesh T n)) ^ 2) s :=
  sq_sum_steps (mesh_pos hT hn) _ s

@[tmio T, powerlib_foundation] theorem intervalIntegrable_sq_stepDeriv (hT : 0 < (T : ℝ))
    {n : ℕ} (hn : 0 < n) (x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) (a b : ℝ) :
    IntervalIntegrable (fun s => stepDeriv T n x s ^ 2) volume a b := by
  simp_rw [sq_stepDeriv hT hn x]
  exact intervalIntegrable_steps _ a b

/-- `∫₀ᵗ u_n = π_n x(t)`. -/
@[tmio T, powerlib_foundation] theorem integral_stepDeriv (hT : 0 < (T : ℝ)) {n : ℕ}
    (hn : 0 < n) (x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) (t : Icc (0 : ℝ) T) :
    ∫ s in (0 : ℝ)..t, stepDeriv T n x s = polyInterp T n x t 0 := by
  have hΔ := mesh_pos hT hn
  have hsΔ := Real.sqrt_pos.mpr hΔ
  simp only [stepDeriv]
  rw [integral_steps hΔ _ t.2.1]
  simp only [polyInterp, polyPath, ContinuousMap.coe_mk]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : mesh T n * (nodeIncr T n x k / √(mesh T n)) = √(mesh T n) * nodeIncr T n x k := by
    rw [mul_div_assoc', div_eq_iff hsΔ.ne']
    linear_combination (-(nodeIncr T n x k)) * Real.mul_self_sqrt hΔ.le
  rw [← mul_assoc, this, mul_assoc]

/-- `∫₀ᵀ u_n² = Σ_k y_k²`. -/
@[tmio T, powerlib_foundation] theorem integral_sq_stepDeriv (hT : 0 < (T : ℝ)) {n : ℕ}
    (hn : 0 < n) (x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) :
    ∫ s in (0 : ℝ)..T, stepDeriv T n x s ^ 2 = ∑ k : Fin n, nodeIncr T n x k ^ 2 := by
  have hΔ := mesh_pos hT hn
  simp_rw [sq_stepDeriv hT hn x]
  rw [integral_steps hΔ _ T.coe_nonneg, Finset.mul_sum]
  have hTn : (T : ℝ) = n * mesh T n := by rw [mesh]; field_simp
  refine Finset.sum_congr rfl fun k _ => ?_
  have hr : ramp (mesh T n) ((k : ℕ) * mesh T n) T = 1 := by
    rw [hTn, ramp_node hΔ]; simp [k.2]
  rw [hr, mul_one, div_pow, Real.sq_sqrt hΔ.le]
  field_simp

/-- `∫₀ᵀ 1_{[a, b)} c f = c ∫ₐᵇ f` for `[a, b] ⊆ [0, T]`. -/
@[tmio T, powerlib_foundation] theorem integral_indicator_mul (f : ℝ → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T) (c : ℝ) :
    ∫ s in (0 : ℝ)..T, (Ico a b).indicator (fun _ => c) s * f s = c * ∫ s in a..b, f s := by
  have hT0 := T.coe_nonneg
  have e : (fun s => (Ico a b).indicator (fun _ => c) s * f s) =
      (Ico a b).indicator (fun s => c * f s) := by
    funext s
    by_cases hs : s ∈ Ico a b
    · rw [indicator_of_mem hs, indicator_of_mem hs]
    · rw [indicator_of_notMem hs, indicator_of_notMem hs, zero_mul]
  rw [e, intervalIntegral.integral_of_le hT0, integral_indicator measurableSet_Ico,
    Measure.restrict_restrict measurableSet_Ico, intervalIntegral.integral_of_le hab,
    ← integral_const_mul]
  have hsub : Ico a b ∩ Ioc 0 T =ᵐ[volume] Ioc a b := by
    have h1 : Ico a b ∩ Ioc 0 T ⊆ Icc a b := fun s hs => ⟨hs.1.1, hs.1.2.le⟩
    have h2 : Ioo a b ⊆ Ico a b ∩ Ioc 0 T := fun s hs =>
      ⟨⟨hs.1.le, hs.2⟩, ⟨lt_of_le_of_lt ha hs.1, (hs.2.trans_le hbT).le⟩⟩
    refine (ae_eq_of_subset_of_measure_ge h2 ?_ measurableSet_Ioo.nullMeasurableSet
      ?_).symm.trans Ioo_ae_eq_Ioc
    · rw [Real.volume_Ioo]
      exact (measure_mono h1).trans_eq (by rw [Real.volume_Icc])
    · exact measure_ne_top_of_subset h1 (by simp)
  rw [setIntegral_congr_set hsub]

/-- The product of the step function `u_n` with an integrable function is integrable. -/
@[tmio T, powerlib_foundation] theorem intervalIntegrable_stepDeriv_mul (n : ℕ)
    (x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun s => stepDeriv T n x s * f s) volume a b := by
  have e : (fun s => stepDeriv T n x s * f s) = fun s => ∑ k : Fin n,
      (Ico ((k : ℕ) * mesh T n) ((k : ℕ) * mesh T n + mesh T n)).indicator
        (fun s => nodeIncr T n x k / √(mesh T n) * f s) s := by
    funext s
    rw [stepDeriv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hs : s ∈ Ico ((k : ℕ) * mesh T n) ((k : ℕ) * mesh T n + mesh T n)
    · rw [indicator_of_mem hs, indicator_of_mem hs]
    · rw [indicator_of_notMem hs, indicator_of_notMem hs, zero_mul]
  rw [e]
  have h := IntervalIntegrable.sum (μ := volume) (a := a) (b := b) Finset.univ
    (f := fun (k : Fin n) (s : ℝ) =>
      (Ico ((k : ℕ) * mesh T n) ((k : ℕ) * mesh T n + mesh T n)).indicator
        (fun s => nodeIncr T n x k / √(mesh T n) * f s) s)
    fun k _ => ⟨(hf.1.const_mul _).indicator measurableSet_Ico,
      (hf.2.const_mul _).indicator measurableSet_Ico⟩
  convert h using 1
  funext s
  simp [Finset.sum_apply]

/-- Coarse dyadic nodes are fine dyadic nodes: `k T/2^m = (k 2^{m'−m}) T/2^{m'}`. -/
@[tmio T, powerlib_foundation] theorem coe_node_pow {m m' : ℕ} (hmm : m ≤ m') (k : ℕ) :
    (node T (2 ^ m') (k * 2 ^ (m' - m)) : ℝ) = (k : ℝ) * mesh T (2 ^ m) := by
  rw [coe_node, mesh, mesh]
  have h : (2 : ℝ) ^ m' = 2 ^ m * 2 ^ (m' - m) := by
    rw [← pow_add, Nat.add_sub_cancel' hmm]
  push_cast
  rw [h]
  field_simp

/-- **Orthogonality of the dyadic derivatives**: for `m ≤ m'` and `x(0) = 0`,
`∫₀ᵀ u_m u_{m'} = Σ_k y_k² = ∫₀ᵀ u_m²` (`y` the level-`m` node increments). -/
@[tmio T, powerlib_foundation] theorem integral_stepDeriv_mul (hT : 0 < (T : ℝ))
    (x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) (hx0 : pathExt x 0 0 = 0) {m m' : ℕ} (hmm : m ≤ m') :
    ∫ s in (0 : ℝ)..T, stepDeriv T (2 ^ m) x s * stepDeriv T (2 ^ m') x s =
      ∑ k : Fin (2 ^ m), nodeIncr T (2 ^ m) x k ^ 2 := by
  have hn : 0 < 2 ^ m := by positivity
  have hn' : 0 < 2 ^ m' := by positivity
  have hΔ := mesh_pos hT hn
  have hsΔ := Real.sqrt_pos.mpr hΔ
  have hT0 := T.coe_nonneg
  have hu' := intervalIntegrable_stepDeriv (T := T) (2 ^ m') x
  have hTn : (T : ℝ) = (2 ^ m : ℕ) * mesh T (2 ^ m) := by rw [mesh]; field_simp
  -- the value of `π_{m'} x` at a coarse node
  have hval : ∀ j : ℕ, j ≤ 2 ^ m →
      ∫ s in (0 : ℝ)..(j : ℝ) * mesh T (2 ^ m), stepDeriv T (2 ^ m') x s =
        pathExt x ((j : ℝ) * mesh T (2 ^ m)) 0 := by
    intro j hj
    have hjr : j * 2 ^ (m' - m) ≤ 2 ^ m' := by
      have : 2 ^ m' = 2 ^ m * 2 ^ (m' - m) := by rw [← pow_add, Nat.add_sub_cancel' hmm]
      rw [this]; exact Nat.mul_le_mul_right _ hj
    have hmem := node_mem (T := T) hn' hjr
    have h1 := integral_stepDeriv hT hn' x ⟨_, hmem⟩
    have h2 := polyInterp_node hT hn' x hjr
    rw [h2] at h1
    simp only [coe_node_pow hmm j] at h1
    rw [h1]
    have h0 : (node T (2 ^ m') 0 : ℝ) = 0 := by simp [node]
    rw [h0, hx0, sub_zero]
  have e : (fun s => stepDeriv T (2 ^ m) x s * stepDeriv T (2 ^ m') x s) = fun s =>
      ∑ k : Fin (2 ^ m), (Ico ((k : ℕ) * mesh T (2 ^ m))
        ((k : ℕ) * mesh T (2 ^ m) + mesh T (2 ^ m))).indicator
          (fun _ => nodeIncr T (2 ^ m) x k / √(mesh T (2 ^ m))) s * stepDeriv T (2 ^ m') x s := by
    funext s; rw [stepDeriv, Finset.sum_mul]
  rw [e, intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    have hk : ((k : ℕ) : ℝ) + 1 ≤ (2 ^ m : ℕ) := by exact_mod_cast k.2
    have hb : ((k : ℕ) : ℝ) * mesh T (2 ^ m) + mesh T (2 ^ m) ≤ T := by rw [hTn]; nlinarith
    rw [integral_indicator_mul _ (by positivity) (by linarith) hb,
      ← intervalIntegral.integral_interval_sub_left (hu' 0 _) (hu' 0 _)]
    have e1 : ((k : ℕ) : ℝ) * mesh T (2 ^ m) + mesh T (2 ^ m) =
        (((k : ℕ) + 1 : ℕ) : ℝ) * mesh T (2 ^ m) := by push_cast; ring
    rw [e1, hval _ k.2, hval _ k.2.le]
    have hy : pathExt x ((((k : ℕ) + 1 : ℕ) : ℝ) * mesh T (2 ^ m)) 0 -
        pathExt x (((k : ℕ) : ℝ) * mesh T (2 ^ m)) 0 =
        √(mesh T (2 ^ m)) * nodeIncr T (2 ^ m) x k := by
      rw [nodeIncr, mul_div_cancel₀ _ hsΔ.ne', coe_node, coe_node]
    rw [hy]
    field_simp
  · intro k _
    have hk := ((hu' 0 T).1.indicator (measurableSet_Ico (a := ((k : ℕ) : ℝ) * mesh T (2 ^ m))
      (b := ((k : ℕ) : ℝ) * mesh T (2 ^ m) + mesh T (2 ^ m)))).const_mul
        (nodeIncr T (2 ^ m) x k / √(mesh T (2 ^ m)))
    have hk2 := ((hu' 0 T).2.indicator (measurableSet_Ico (a := ((k : ℕ) : ℝ) * mesh T (2 ^ m))
      (b := ((k : ℕ) : ℝ) * mesh T (2 ^ m) + mesh T (2 ^ m)))).const_mul
        (nodeIncr T (2 ^ m) x k / √(mesh T (2 ^ m)))
    have e2 : (fun s => (Ico ((k : ℕ) * mesh T (2 ^ m))
        ((k : ℕ) * mesh T (2 ^ m) + mesh T (2 ^ m))).indicator
          (fun _ => nodeIncr T (2 ^ m) x k / √(mesh T (2 ^ m))) s * stepDeriv T (2 ^ m') x s) =
        fun s => nodeIncr T (2 ^ m) x k / √(mesh T (2 ^ m)) *
          (Ico ((k : ℕ) * mesh T (2 ^ m)) ((k : ℕ) * mesh T (2 ^ m) + mesh T (2 ^ m))).indicator
            (stepDeriv T (2 ^ m') x) s := by
      funext s
      by_cases hs : s ∈ Ico ((k : ℕ) * mesh T (2 ^ m))
        ((k : ℕ) * mesh T (2 ^ m) + mesh T (2 ^ m))
      · rw [indicator_of_mem hs, indicator_of_mem hs]
      · rw [indicator_of_notMem hs, indicator_of_notMem hs]; ring
    rw [e2]
    exact ⟨hk, hk2⟩

/-- **The dyadic `L²` identity**: for `m ≤ m'` and `x(0) = 0`,
`∫₀ᵀ (u_{m'} − u_m)² = Σ y'² − Σ y²` (the level-`m'` minus the level-`m` energy, times `2`). -/
@[tmio T, powerlib_foundation] theorem integral_sq_sub_stepDeriv (hT : 0 < (T : ℝ))
    (x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) (hx0 : pathExt x 0 0 = 0) {m m' : ℕ} (hmm : m ≤ m') :
    ∫ s in (0 : ℝ)..T, (stepDeriv T (2 ^ m') x s - stepDeriv T (2 ^ m) x s) ^ 2 =
      ∑ k : Fin (2 ^ m'), nodeIncr T (2 ^ m') x k ^ 2 -
        ∑ k : Fin (2 ^ m), nodeIncr T (2 ^ m) x k ^ 2 := by
  have hn : 0 < 2 ^ m := by positivity
  have hn' : 0 < 2 ^ m' := by positivity
  have h1 := intervalIntegrable_sq_stepDeriv hT hn' x 0 T
  have h2 := intervalIntegrable_sq_stepDeriv hT hn x 0 T
  have h3 := intervalIntegrable_stepDeriv_mul (2 ^ m) x
    (intervalIntegrable_stepDeriv (2 ^ m') x 0 T)
  have e : (fun s => (stepDeriv T (2 ^ m') x s - stepDeriv T (2 ^ m) x s) ^ 2) = fun s =>
      (stepDeriv T (2 ^ m') x s ^ 2 - 2 * (stepDeriv T (2 ^ m) x s * stepDeriv T (2 ^ m') x s)) +
        stepDeriv T (2 ^ m) x s ^ 2 := by
    funext s; ring
  rw [e, intervalIntegral.integral_add (h1.sub (h3.const_mul 2)) h2,
    intervalIntegral.integral_sub h1 (h3.const_mul 2), intervalIntegral.integral_const_mul,
    integral_sq_stepDeriv hT hn' x, integral_sq_stepDeriv hT hn x,
    integral_stepDeriv_mul hT x hx0 hmm]
  ring

/-- `‖f‖² = ∫ f²` in `L²`. -/
@[tmio T, powerlib_foundation] theorem norm_sq_toLp {μ : Measure ℝ} {f : ℝ → ℝ}
    (hf : MemLp f 2 μ) : ‖hf.toLp f‖ ^ 2 = ∫ s, f s ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with s hs
  simp [hs, sq]

/-- The node value of `∫ u_{m'}` at a coarse node `j Δ_m` (`m ≤ m'`, `x(0) = 0`) is `x(j Δ_m)`. -/
@[tmio T, powerlib_foundation] theorem integral_stepDeriv_node (hT : 0 < (T : ℝ))
    (x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) (hx0 : pathExt x 0 0 = 0) {m m' : ℕ} (hmm : m ≤ m')
    {j : ℕ} (hj : j ≤ 2 ^ m) :
    ∫ s in (0 : ℝ)..(j : ℝ) * mesh T (2 ^ m), stepDeriv T (2 ^ m') x s =
      pathExt x ((j : ℝ) * mesh T (2 ^ m)) 0 := by
  have hn' : 0 < 2 ^ m' := by positivity
  have hjr : j * 2 ^ (m' - m) ≤ 2 ^ m' := by
    have : 2 ^ m' = 2 ^ m * 2 ^ (m' - m) := by rw [← pow_add, Nat.add_sub_cancel' hmm]
    rw [this]; exact Nat.mul_le_mul_right _ hj
  have hmem := node_mem (T := T) hn' hjr
  have h1 := integral_stepDeriv hT hn' x ⟨_, hmem⟩
  have h2 := polyInterp_node hT hn' x hjr
  rw [h2] at h1
  simp only [coe_node_pow hmm j] at h1
  rw [h1]
  have h0 : (node T (2 ^ m') 0 : ℝ) = 0 := by simp [node]
  rw [h0, hx0, sub_zero]

/-- **Closure lemma**: if `x(0) = 0` and the dyadic energies are bounded,
`Σ_k (Δ_k x)²/(2Δ_m) ≤ a` for every `m`, then `I(x) ≤ a`. The derivatives of the dyadic
interpolations are Cauchy in `L²(0, T)`; their limit `v` satisfies `x = ∫ v` and `½ ∫ v² ≤ a`. -/
@[tmio T, powerlib_foundation] theorem schilderRate_le_of_energy (hT : 0 < (T : ℝ))
    (x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) (hx0 : pathExt x 0 0 = 0) {a : ℝ}
    (hE : ∀ m, ∑ k : Fin (2 ^ m), nodeIncr T (2 ^ m) x k ^ 2 / 2 ≤ a) :
    schilderRate T x ≤ ENNReal.ofReal a := by
  have hT0 := T.coe_nonneg
  set S : ℕ → ℝ := fun m => ∑ k : Fin (2 ^ m), nodeIncr T (2 ^ m) x k ^ 2 with hSdef
  have hS : ∀ m, S m ≤ 2 * a := fun m => by
    have := hE m; rw [← Finset.sum_div] at this; simp only [hSdef]; linarith
  have hSmono : Monotone S := fun m m' h => by
    have h1 := integral_sq_sub_stepDeriv hT x hx0 h
    have h0 : 0 ≤ ∫ s in (0 : ℝ)..T, (stepDeriv T (2 ^ m') x s - stepDeriv T (2 ^ m) x s) ^ 2 :=
      intervalIntegral.integral_nonneg hT0 fun s _ => sq_nonneg _
    simp only [hSdef]; linarith
  have hbdd : BddAbove (range S) := ⟨2 * a, by rintro _ ⟨m, rfl⟩; exact hS m⟩
  set e := ⨆ m, S m with he
  have hSe : Tendsto S atTop (𝓝 e) := tendsto_atTop_ciSup hSmono hbdd
  have hSle : ∀ m, S m ≤ e := fun m => le_ciSup hbdd m
  have he2 : e ≤ 2 * a := ciSup_le hS
  -- the dyadic derivatives in `L²(0, T)`
  set μ := volume.restrict (Ioc (0 : ℝ) T) with hμ
  set u : ℕ → ℝ → ℝ := fun m => stepDeriv T (2 ^ m) x with hu
  have hpos : ∀ m, 0 < 2 ^ m := fun m => by positivity
  have hmem : ∀ m, MemLp (u m) 2 μ := fun m =>
    (memLp_two_iff_integrable_sq
      (intervalIntegrable_stepDeriv (T := T) (2 ^ m) x 0 T).1.aestronglyMeasurable).mpr
      (intervalIntegrable_sq_stepDeriv hT (hpos m) x 0 T).1
  set F : ℕ → Lp ℝ 2 μ := fun m => (hmem m).toLp (u m) with hF
  have hint : ∀ {g : ℝ → ℝ}, ∫ s, g s ∂μ = ∫ s in (0 : ℝ)..T, g s := fun {g} =>
    (intervalIntegral.integral_of_le hT0).symm
  have hnorm : ∀ m, ‖F m‖ ^ 2 = S m := fun m => by
    rw [hF, norm_sq_toLp, hint]; exact integral_sq_stepDeriv hT (hpos m) x
  have hdist : ∀ m m', m ≤ m' → ‖F m' - F m‖ ^ 2 = S m' - S m := fun m m' h => by
    rw [hF, ← MemLp.toLp_sub, norm_sq_toLp, hint]
    exact integral_sq_sub_stepDeriv hT x hx0 h
  have hcauchy : CauchySeq F := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hSe (ε ^ 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    have h1 := hdist N n hn
    have h2 := hN N le_rfl
    rw [Real.dist_eq, abs_lt] at h2
    have h3 : ‖F n - F N‖ ^ 2 < ε ^ 2 := by rw [h1]; linarith [hSle n]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h3
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcauchy
  set v : ℝ → ℝ := ⇑G with hv
  have hv2 : MemLp v 2 μ := Lp.memLp G
  have hGv : hv2.toLp v = G := Lp.toLp_coeFn _ _
  have hvI : IntegrableOn v (Ioc 0 T) := hv2.integrable one_le_two
  have hvi : IntervalIntegrable v volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).mpr hvI
  have hvsq : IntervalIntegrable (fun s => v s ^ 2) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).mpr hv2.integrable_sq
  -- `∫₀ᵀ v² = e`
  have hGe : ‖G‖ ^ 2 = e := by
    have h1 : Tendsto (fun m => ‖F m‖ ^ 2) atTop (𝓝 (‖G‖ ^ 2)) :=
      (continuous_norm.tendsto G).pow 2 |>.comp hG
    exact tendsto_nhds_unique h1 (by simpa only [hnorm] using hSe)
  have hv2int : ∫ s in (0 : ℝ)..T, v s ^ 2 = e := by
    rw [← hint, ← norm_sq_toLp hv2, hGv, hGe]
  -- the primitives converge on `[0, T]`
  have hdiff : ∀ m, ‖F m - G‖ ^ 2 = ∫ s in (0 : ℝ)..T, (u m s - v s) ^ 2 := fun m => by
    rw [hF, ← hGv, ← MemLp.toLp_sub, norm_sq_toLp, hint]
    rfl
  have hFG : Tendsto (fun m => ‖F m - G‖ ^ 2) atTop (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp hG).pow 2
    simpa using this
  have hprim : ∀ t ∈ Icc (0 : ℝ) T,
      Tendsto (fun m => ∫ s in (0 : ℝ)..t, u m s) atTop (𝓝 (∫ s in (0 : ℝ)..t, v s)) := by
    intro t ht
    have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 T := by
      rw [uIcc_of_le ht.1, uIcc_of_le hT0]; exact Icc_subset_Icc_right ht.2
    have hb : ∀ m, ((∫ s in (0 : ℝ)..t, u m s) - ∫ s in (0 : ℝ)..t, v s) ^ 2 ≤
        T * ‖F m - G‖ ^ 2 := fun m => by
      have hum : IntervalIntegrable (u m) volume 0 t := intervalIntegrable_stepDeriv _ x 0 t
      have hsq : IntervalIntegrable (fun s => (u m s - v s) ^ 2) volume 0 T :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).mpr ((hmem m).sub hv2).integrable_sq
      rw [← intervalIntegral.integral_sub hum (hvi.mono_set hsub), hdiff]
      calc _ ≤ (t - 0) * ∫ s in (0 : ℝ)..t, (u m s - v s) ^ 2 :=
            sq_integral_le ht.1 (hum.sub (hvi.mono_set hsub)) (hsq.mono_set hsub)
        _ ≤ T * ∫ s in (0 : ℝ)..T, (u m s - v s) ^ 2 := by
            refine mul_le_mul (by linarith [ht.2]) ?_
              (intervalIntegral.integral_nonneg ht.1 fun s _ => sq_nonneg _) hT0
            exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
              (Eventually.of_forall fun s => sq_nonneg _) hsq
    have hlim : Tendsto (fun m => (T : ℝ) * ‖F m - G‖ ^ 2) atTop (𝓝 0) := by
      simpa using hFG.const_mul (T : ℝ)
    have hsq0 : Tendsto (fun m => ((∫ s in (0 : ℝ)..t, u m s) - ∫ s in (0 : ℝ)..t, v s) ^ 2)
        atTop (𝓝 0) :=
      squeeze_zero (fun m => sq_nonneg _) hb hlim
    have habs : Tendsto (fun m => |(∫ s in (0 : ℝ)..t, u m s) - ∫ s in (0 : ℝ)..t, v s|)
        atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hsq0
      rw [Real.sqrt_zero] at this
      refine this.congr fun m => ?_
      simp only [Function.comp, Real.sqrt_sq_eq_abs]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.norm_eq_abs] using habs
  -- `x = ∫ v` at the dyadic nodes, then everywhere
  have hnode : ∀ m j : ℕ, j ≤ 2 ^ m →
      ∫ s in (0 : ℝ)..(j : ℝ) * mesh T (2 ^ m), v s = pathExt x ((j : ℝ) * mesh T (2 ^ m)) 0 := by
    intro m j hj
    have hmemj : (j : ℝ) * mesh T (2 ^ m) ∈ Icc (0 : ℝ) T := by
      have := node_mem (T := T) (hpos m) hj; rwa [coe_node] at this
    refine tendsto_nhds_unique (hprim _ hmemj) ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop m] with m' hm'
    exact (integral_stepDeriv_node hT x hx0 hm' hj).symm
  have hall : ∀ t ∈ Icc (0 : ℝ) T, ∫ s in (0 : ℝ)..t, v s = pathExt x t 0 := by
    intro t ht
    have hc1 : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, v s) (Icc 0 T) := by
      have := intervalIntegral.continuousOn_primitive_interval' hvi left_mem_uIcc
      rwa [uIcc_of_le hT0] at this
    have hc2 : Continuous fun t => pathExt x t 0 :=
      (continuous_apply 0).comp (continuous_pathExt x)
    set d : ℕ → ℝ := fun m => (⌊t / mesh T (2 ^ m)⌋₊ : ℝ) * mesh T (2 ^ m) with hd
    have hdmem : ∀ m, d m ∈ Icc (0 : ℝ) T ∧ ⌊t / mesh T (2 ^ m)⌋₊ ≤ 2 ^ m ∧
        |d m - t| ≤ mesh T (2 ^ m) := by
      intro m
      have hΔ := mesh_pos hT (hpos m)
      have hTn : (T : ℝ) = (2 ^ m : ℕ) * mesh T (2 ^ m) := by rw [mesh]; field_simp
      have h1 : (⌊t / mesh T (2 ^ m)⌋₊ : ℝ) ≤ t / mesh T (2 ^ m) :=
        Nat.floor_le (div_nonneg ht.1 hΔ.le)
      have h2 : t / mesh T (2 ^ m) < ⌊t / mesh T (2 ^ m)⌋₊ + 1 := Nat.lt_floor_add_one _
      rw [le_div_iff₀ hΔ] at h1
      rw [div_lt_iff₀ hΔ] at h2
      have hj : ⌊t / mesh T (2 ^ m)⌋₊ ≤ 2 ^ m := by
        have : t / mesh T (2 ^ m) ≤ ((2 ^ m : ℕ) : ℝ) := by
          rw [div_le_iff₀ hΔ]; linarith [ht.2]
        have := Nat.floor_le_floor this
        rwa [Nat.floor_natCast] at this
      refine ⟨⟨by positivity, by linarith [ht.2]⟩, hj, ?_⟩
      rw [abs_le]; constructor <;> nlinarith
    have hdt : Tendsto d atTop (𝓝[Icc 0 T] t) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun m => (hdmem m).1⟩
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hm : Tendsto (fun m => mesh T (2 ^ m)) atTop (𝓝 0) := by
        simp only [mesh]
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num)).const_mul (T : ℝ)
        simp only [mul_zero] at this
        refine this.congr fun m => ?_
        push_cast
        rw [one_div_pow]; ring
      exact squeeze_zero (fun m => norm_nonneg _) (fun m => by
        rw [Real.norm_eq_abs]; exact (hdmem m).2.2) hm
    have hl1 := (hc1 t ht).tendsto.comp hdt
    have hl2 := (hc2.tendsto t).comp (tendsto_nhdsWithin_iff.mp hdt).1
    refine tendsto_nhds_unique hl1 (hl2.congr fun m => ?_)
    simp only [Function.comp, hd]
    exact (hnode m _ (hdmem m).2.1).symm
  -- conclusion
  set U : ℝ → Fin 1 → ℝ := fun s => v s • fun _ => (1 : ℝ) with hU
  have hUi : IntervalIntegrable U volume 0 T := ⟨hvi.1.smul_const _, hvi.2.smul_const _⟩
  have hUsq : (fun s => ∑ j, U s j ^ 2) = fun s => v s ^ 2 := by
    funext s; simp [hU]
  have hU2 : IntervalIntegrable (fun s => ∑ j, U s j ^ 2) volume 0 T := by rw [hUsq]; exact hvsq
  have hxU : ∀ t : Icc (0 : ℝ) T, x t = ∫ s in (0 : ℝ)..t, U s := by
    intro t
    rw [intervalIntegral.integral_smul_const, hall t t.2, pathExt_of_mem x t.2]
    funext j
    fin_cases j
    simp
  refine (iInf₂_le_of_le U ⟨hUi, hU2, hxU⟩ le_rfl).trans (ENNReal.ofReal_le_ofReal ?_)
  unfold controlAction
  rw [hUsq, hv2int]
  linarith

/-- A path of finite Schilder rate starts at `0`. -/
@[tmio T, powerlib_foundation] theorem pathExt_zero_of_schilderRate_ne_top
    {x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)} (h : schilderRate T x ≠ ⊤) : pathExt x 0 0 = 0 := by
  have h' : schilderRate T x < ⊤ := lt_top_iff_ne_top.mpr h
  simp only [schilderRate, iInf_lt_iff] at h'
  obtain ⟨u, ⟨-, -, hxu⟩, -⟩ := h'
  rw [pathExt_of_mem x ⟨le_rfl, T.coe_nonneg⟩, hxu]
  simp

/-- **Energies are bounded by the rate**: `I(x) ≤ b` gives `x(0) = 0` and
`Σ_k (Δ_k x)²/(2Δ) ≤ b` for every uniform partition. -/
@[tmio T, powerlib_foundation] theorem energy_le_of_schilderRate (hT : 0 < (T : ℝ)) {n : ℕ}
    (hn : 0 < n) {x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)} {b : ℝ} (hb : 0 ≤ b)
    (h : schilderRate T x ≤ ENNReal.ofReal b) :
    ∑ k : Fin n, nodeIncr T n x k ^ 2 / 2 ≤ b := by
  have h1 := (schilderRate_polyInterp_le hT hn x).trans h
  rw [polyInterp, schilderRate_polyPath hT hn, gaussRate] at h1
  exact (ENNReal.ofReal_le_ofReal_iff hb).mp h1

/-- **Sublevel sets through the dyadic energies**: for `b ≥ 0`,
`{I ≤ b} = {x(0) = 0} ∩ ⋂_m {E_m ≤ b}`. -/
@[tmio T, powerlib_foundation] theorem schilderRate_preimage_Iic (hT : 0 < (T : ℝ)) {b : ℝ}
    (hb : 0 ≤ b) :
    schilderRate (m := 1) T ⁻¹' Iic (ENNReal.ofReal b) =
      {x : C(Icc (0 : ℝ) T, Fin 1 → ℝ) | pathExt x 0 0 = 0} ∩ ⋂ m : ℕ,
        {x : C(Icc (0 : ℝ) T, Fin 1 → ℝ) |
          ∑ k : Fin (2 ^ m), nodeIncr T (2 ^ m) x k ^ 2 / 2 ≤ b} := by
  ext x
  simp only [mem_preimage, mem_Iic, mem_inter_iff, mem_iInter, mem_ofPred_eq]
  constructor
  · intro h
    exact ⟨pathExt_zero_of_schilderRate_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h),
      fun m => energy_le_of_schilderRate hT (by positivity) hb h⟩
  · rintro ⟨h0, hE⟩
    exact schilderRate_le_of_energy hT x h0 hE

@[tmio T, powerlib_foundation] theorem isClosed_schilderRate_le (hT : 0 < (T : ℝ)) {b : ℝ}
    (hb : 0 ≤ b) : IsClosed (schilderRate (m := 1) T ⁻¹' Iic (ENNReal.ofReal b)) := by
  rw [schilderRate_preimage_Iic hT hb]
  have hev : Continuous fun x : C(Icc (0 : ℝ) T, Fin 1 → ℝ) => pathExt x 0 0 :=
    (continuous_apply (0 : Fin 1)).comp (continuous_eval_const _)
  refine IsClosed.inter (isClosed_eq hev continuous_const)
    (isClosed_iInter fun m => isClosed_le ?_ continuous_const)
  exact continuous_finsetSum _ fun k _ =>
    (((continuous_apply k).comp (continuous_nodeIncr (T := T) (n := 2 ^ m))).pow 2).div_const 2

/-- **The Schilder rate is lower semicontinuous** on `C([0, T])`. -/
@[tmio T, powerlib_foundation] theorem lowerSemicontinuous_schilderRate (hT : 0 < (T : ℝ)) :
    LowerSemicontinuous (schilderRate (m := 1) T) := by
  refine lowerSemicontinuous_iff_isClosed_preimage.mpr fun c => ?_
  by_cases hc : c = ⊤
  · subst hc; simp
  rw [← ENNReal.ofReal_toReal hc]
  exact isClosed_schilderRate_le hT ENNReal.toReal_nonneg

/-- **Hölder bound**: `I(x) ≤ b` gives `|x(t) − x(s)|² ≤ 2(b + 1)|t − s|`. -/
@[tmio T, powerlib_foundation] theorem sq_sub_le_of_schilderRate {x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)}
    {b : ℝ} (hb : 0 ≤ b) (h : schilderRate T x ≤ ENNReal.ofReal b) (s t : Icc (0 : ℝ) T)
    (hst : s ≤ t) : (x t 0 - x s 0) ^ 2 ≤ 2 * (b + 1) * ((t : ℝ) - s) := by
  have hst' : (s : ℝ) ≤ t := hst
  have hlt : schilderRate T x < ENNReal.ofReal (b + 1) :=
    h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
  simp only [schilderRate, iInf_lt_iff] at hlt
  obtain ⟨u, ⟨hu, hu2, hxu⟩, hact⟩ := hlt
  have hT0 := T.coe_nonneg
  set v : ℝ → ℝ := fun r => u r 0 with hv
  have hvi : IntervalIntegrable v volume 0 T :=
    ⟨(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).integrable_comp hu.1,
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).integrable_comp hu.2⟩
  have hv2 : IntervalIntegrable (fun r => v r ^ 2) volume 0 T := by simpa [hv] using hu2
  have hsub : ∀ r : Icc (0 : ℝ) T, uIcc (0 : ℝ) r ⊆ uIcc 0 T := fun r => by
    rw [uIcc_of_le r.2.1, uIcc_of_le hT0]; exact Icc_subset_Icc_right r.2.2
  have hxv : ∀ r : Icc (0 : ℝ) T, x r 0 = ∫ s in (0 : ℝ)..r, v s := fun r => by
    rw [hxu]
    exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0
      ).intervalIntegral_comp_comm (hu.mono_set (hsub r))).symm
  have hstsub : uIcc (s : ℝ) t ⊆ uIcc 0 T := by
    rw [uIcc_of_le hst', uIcc_of_le hT0]; exact Icc_subset_Icc s.2.1 t.2.2
  rw [hxv, hxv, intervalIntegral.integral_interval_sub_left (hvi.mono_set (hsub t))
    (hvi.mono_set (hsub s))]
  have hcs := sq_integral_le hst' (hvi.mono_set hstsub) (hv2.mono_set hstsub)
  have hmono : ∫ r in (s : ℝ)..t, v r ^ 2 ≤ ∫ r in (0 : ℝ)..T, v r ^ 2 :=
    intervalIntegral.integral_mono_interval s.2.1 hst' t.2.2
      (Eventually.of_forall fun r => sq_nonneg _) hv2
  have hact' : controlAction u T < b + 1 := by
    by_contra hc; push Not at hc
    exact absurd hact (not_lt.mpr (ENNReal.ofReal_le_ofReal hc))
  have hca : controlAction u T = 1 / 2 * ∫ r in (0 : ℝ)..T, v r ^ 2 := by
    unfold controlAction; congr 1; simp [hv]
  have hst'' : 0 ≤ (t : ℝ) - s := by linarith
  calc _ ≤ ((t : ℝ) - s) * ∫ r in (s : ℝ)..t, v r ^ 2 := hcs
    _ ≤ ((t : ℝ) - s) * ∫ r in (0 : ℝ)..T, v r ^ 2 := mul_le_mul_of_nonneg_left hmono hst''
    _ ≤ ((t : ℝ) - s) * (2 * (b + 1)) := mul_le_mul_of_nonneg_left (by linarith) hst''
    _ = _ := by ring

/-- **The Schilder rate is good**: its sublevel sets are compact (Arzelà–Ascoli). -/
@[tmio T, powerlib_foundation] theorem isGoodRate_schilderRate (hT : 0 < (T : ℝ)) :
    IsGoodRate (schilderRate (m := 1) T) := by
  intro c hc
  set b := c.toReal with hbdef
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  set S := schilderRate (m := 1) T ⁻¹' Iic c with hS
  have hcS : S = schilderRate (m := 1) T ⁻¹' Iic (ENNReal.ofReal b) := by
    rw [hbdef, ENNReal.ofReal_toReal hc]
  have hSc : IsClosed S := hcS ▸ isClosed_schilderRate_le hT hb
  set e := ContinuousMap.isometryEquivBoundedOfCompact (Icc (0 : ℝ) T) (Fin 1 → ℝ) with he
  have hmemS : ∀ x ∈ S, schilderRate T x ≤ ENNReal.ofReal b := fun x hx => by
    rw [hcS] at hx; exact hx
  set R := √(2 * (b + 1) * T) with hR
  have hval : ∀ x ∈ S, ∀ t : Icc (0 : ℝ) T, x t ∈ Metric.closedBall (0 : Fin 1 → ℝ) R := by
    intro x hx t
    have h0 := pathExt_zero_of_schilderRate_ne_top
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hmemS x hx))
    rw [pathExt_of_mem x ⟨le_rfl, T.coe_nonneg⟩] at h0
    have h1 := sq_sub_le_of_schilderRate hb (hmemS x hx) ⟨0, le_rfl, T.coe_nonneg⟩ t t.2.1
    rw [h0, sub_zero] at h1
    rw [Metric.mem_closedBall, dist_fin_one, Pi.zero_apply, sub_zero, hR]
    refine Real.abs_le_sqrt (h1.trans ?_)
    have : (t : ℝ) - 0 ≤ T := by linarith [t.2.2]
    nlinarith
  have hA : IsCompact (e '' S) := by
    refine BoundedContinuousFunction.arzela_ascoli₂ (Metric.closedBall (0 : Fin 1 → ℝ) R)
      (isCompact_closedBall _ _) (e '' S) (e.toHomeomorph.isClosedMap _ hSc) ?_ ?_
    · rintro f t ⟨x, hx, rfl⟩
      exact hval x hx t
    · intro t₀
      rw [Metric.equicontinuousAt_iff]
      intro ε hε
      refine ⟨ε ^ 2 / (2 * (b + 1)), by positivity, fun t ht f => ?_⟩
      obtain ⟨x, hx, hfx⟩ := f.2
      have hxf : ∀ r, f.1 r = x r := fun r => by rw [← hfx]; rfl
      show dist (f.1 t₀) (f.1 t) < ε
      rw [hxf, hxf, dist_fin_one]
      have key : ∀ s t : Icc (0 : ℝ) T, s ≤ t → |x t 0 - x s 0| < ε ∨ ε ^ 2 / (2 * (b + 1)) ≤
          (t : ℝ) - s := by
        intro s t hst
        by_cases hd : ε ^ 2 / (2 * (b + 1)) ≤ (t : ℝ) - s
        · exact Or.inr hd
        · left
          push Not at hd
          have h1 := sq_sub_le_of_schilderRate hb (hmemS x hx) s t hst
          have h2 : 2 * (b + 1) * ((t : ℝ) - s) < ε ^ 2 := by
            rw [lt_div_iff₀ (by positivity)] at hd; linarith
          exact abs_lt_of_sq_lt_sq (by linarith) hε.le
      rw [Subtype.dist_eq, Real.dist_eq] at ht
      rcases le_total t₀ t with h | h
      · rcases key t₀ t h with h1 | h1
        · rwa [abs_sub_comm]
        · rw [abs_of_nonneg (by linarith [show (t₀ : ℝ) ≤ t from h])] at ht; linarith
      · rcases key t t₀ h with h1 | h1
        · exact h1
        · rw [abs_of_nonpos (by linarith [show (t : ℝ) ≤ t₀ from h])] at ht; linarith
  have : S = e.symm '' (e '' S) := (e.symm_image_image S).symm
  rw [this]
  exact hA.image e.symm.continuous

end powerlib.Stochastic.LDP
