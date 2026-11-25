import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.SchilderPolygonal

/-! # The Schilder rate and polygonal interpolation

Properties of the Schilder rate `½ ∫ ẇ²` (`schilderRate`) needed to pass from the polygonal
approximations of `√ε B` to `√ε B` itself: the polygonal interpolation `polyInterp n x` of a path
converges uniformly to it, its rate is at most the rate of the path (discrete Cauchy–Schwarz), and
the polygonal interpolation is affine on each step with an explicit deviation bound.

Scope.
* Analysis on `C([0, T], ℝ)` (written `C([0, T], Fin 1 → ℝ)`), uniform mesh `Δ = T/n`, `T > 0`,
  `n ≥ 1`; not an engineering result.

Source: A. Dembo, O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed. (1998),
proof of Thm 5.2.3 (`I(π_n x) ≤ I(x)` and `π_n x → x`).

Results.
* `ramp_of_le`, `ramp_of_ge`, `ramp_of_mem` (values of the ramp), `polyPath_step` (affine on each
  step), `sum_incr_node`, `polyInterp_node` (`π_n x(kΔ) = x(kΔ) − x(0)`), `exists_step`
  (every time lies in a step), `abs_polyInterp_sub_le` (`|π_n x(t) − x(t)| ≤ |x(0)| +
  |x(t) − x(kΔ)| + |x((k+1)Δ) − x(kΔ)|` on the `k`-th step), `dist_fin_one`,
  `tendsto_polyInterp` (`π_n x → x` uniformly when `x(0) = 0`).
* `sq_integral_le` (Cauchy–Schwarz on an interval), `schilderRate_polyInterp_le`
  (`I(π_n x) ≤ I(x)`).
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

variable {T : ℝ≥0} {n : ℕ}

@[tmio T, powerlib_foundation] theorem ramp_of_le {Δ a t : ℝ} (hΔ : 0 < Δ) (h : t ≤ a) :
    ramp Δ a t = 0 := by
  have : (t - a) / Δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hΔ.le
  rw [ramp, min_eq_right (this.trans zero_le_one), max_eq_left this]

@[tmio T, powerlib_foundation] theorem ramp_of_ge {Δ a t : ℝ} (hΔ : 0 < Δ) (h : a + Δ ≤ t) :
    ramp Δ a t = 1 := by
  have : 1 ≤ (t - a) / Δ := by rw [le_div_iff₀ hΔ]; linarith
  rw [ramp, min_eq_left this, max_eq_right zero_le_one]

@[tmio T, powerlib_foundation] theorem ramp_of_mem {Δ a t : ℝ} (hΔ : 0 < Δ) (h1 : a ≤ t)
    (h2 : t ≤ a + Δ) : ramp Δ a t = (t - a) / Δ := by
  have h0 : 0 ≤ (t - a) / Δ := div_nonneg (by linarith) hΔ.le
  have h1' : (t - a) / Δ ≤ 1 := by rw [div_le_one hΔ]; linarith
  rw [ramp, min_eq_right h1', max_eq_right h0]

/-- **Affine on each step**: on `[kΔ, (k+1)Δ]`,
`w(t) = w(kΔ) + √Δ y_k (t − kΔ)/Δ`. -/
@[tmio T, powerlib_foundation] theorem polyPath_step (hT : 0 < (T : ℝ)) (hn : 0 < n)
    (y : Fin n → ℝ) (k : Fin n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (h1 : ((k : ℕ) : ℝ) * mesh T n ≤ t) (h2 : t ≤ ((k : ℕ) : ℝ) * mesh T n + mesh T n) :
    polyPath T n y ⟨t, ht⟩ 0 = polyPath T n y ⟨node T n k, node_mem hn k.2.le⟩ 0 +
      √(mesh T n) * y k * ((t - ((k : ℕ) : ℝ) * mesh T n) / mesh T n) := by
  have hΔ := mesh_pos hT hn
  simp only [polyPath, ContinuousMap.coe_mk, coe_node]
  rw [← sub_eq_iff_eq_add', ← mul_sub, ← Finset.sum_sub_distrib, mul_assoc]
  congr 1
  rw [Finset.sum_eq_single k]
  · rw [ramp_of_mem hΔ h1 h2, ramp_of_le hΔ le_rfl]; ring
  · intro j _ hjk
    rcases lt_or_gt_of_ne (fun h : (j : ℕ) = k => hjk (Fin.ext h)) with hlt | hgt
    · have hj1 : ((j : ℕ) : ℝ) * mesh T n + mesh T n ≤ ((k : ℕ) : ℝ) * mesh T n := by
        have : ((j : ℕ) : ℝ) + 1 ≤ (k : ℕ) := by exact_mod_cast hlt
        nlinarith
      rw [ramp_of_ge hΔ (hj1.trans h1), ramp_of_ge hΔ hj1, sub_self]
    · have hj1 : ((k : ℕ) : ℝ) * mesh T n + mesh T n ≤ ((j : ℕ) : ℝ) * mesh T n := by
        have : ((k : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast hgt
        nlinarith
      rw [ramp_of_le hΔ (h2.trans hj1), ramp_of_le hΔ (by linarith), sub_self]
  · simp

/-- Telescoping at the nodes: with coefficients `(g(j+1) − g(j))/√Δ`, the node value at `kΔ` is
`g(k) − g(0)`. -/
@[tmio T, powerlib_foundation] theorem sum_incr_node (hT : 0 < (T : ℝ)) (hn : 0 < n)
    (g : ℕ → ℝ) {k : ℕ} (hk : k ≤ n) :
    polyPath T n (fun j : Fin n => (g (j + 1) - g j) / √(mesh T n))
      ⟨node T n k, node_mem hn hk⟩ 0 = g k - g 0 := by
  rw [polyPath_node hT hn _ hk]
  have hΔ := Real.sqrt_pos.mpr (mesh_pos hT hn)
  have e : ∀ j : Fin n, (if (j : ℕ) < k then (g (j + 1) - g j) / √(mesh T n) else 0) =
      (if (j : ℕ) < k then g (j + 1) - g j else 0) / √(mesh T n) := by
    intro j; split_ifs <;> simp
  simp_rw [e, ← Finset.sum_div]
  rw [mul_div_cancel₀ _ hΔ.ne']
  have hsum : (∑ j : Fin n, if (j : ℕ) < k then g (j + 1) - g j else 0) =
      ∑ j ∈ Finset.range k, (g (j + 1) - g j) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => if j < k then g (j + 1) - g j else 0) n,
      ← Finset.sum_range_add_sum_Ico _ hk]
    rw [Finset.sum_eq_zero (s := Finset.Ico k n) fun j hj => by
      simp [not_lt.mpr (Finset.mem_Ico.mp hj).1]]
    rw [add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp [Finset.mem_range.mp hj]
  rw [hsum, Finset.sum_range_sub g]

/-- **Node values of the interpolation**: `π_n x(kΔ) = x(kΔ) − x(0)`. -/
@[tmio T, powerlib_foundation] theorem polyInterp_node (hT : 0 < (T : ℝ)) (hn : 0 < n)
    (x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) {k : ℕ} (hk : k ≤ n) :
    polyInterp T n x ⟨node T n k, node_mem hn hk⟩ 0 =
      pathExt x (node T n k) 0 - pathExt x (node T n 0) 0 :=
  sum_incr_node hT hn (fun j => pathExt x (node T n j) 0) hk

/-- Every time of `[0, T]` lies in some step `[kΔ, (k+1)Δ]`. -/
@[tmio T, powerlib_foundation] theorem exists_step (hT : 0 < (T : ℝ)) (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    ∃ k : Fin n, ((k : ℕ) : ℝ) * mesh T n ≤ t ∧ t ≤ ((k : ℕ) : ℝ) * mesh T n + mesh T n := by
  have hΔ := mesh_pos hT hn
  have hTn : (T : ℝ) = n * mesh T n := by rw [mesh]; field_simp
  by_cases hf : ⌊t / mesh T n⌋₊ < n
  · refine ⟨⟨_, hf⟩, ?_, ?_⟩
    · have := Nat.floor_le (div_nonneg ht.1 hΔ.le)
      simp only
      rwa [le_div_iff₀ hΔ] at this
    · have := Nat.lt_floor_add_one (t / mesh T n)
      simp only
      rw [div_lt_iff₀ hΔ] at this
      linarith
  · push Not at hf
    refine ⟨⟨n - 1, Nat.sub_lt hn one_pos⟩, ?_, ?_⟩
    · have h1 : (n : ℝ) ≤ t / mesh T n := (Nat.le_floor_iff (div_nonneg ht.1 hΔ.le)).mp hf
      rw [le_div_iff₀ hΔ] at h1
      rw [Nat.cast_sub (show 1 ≤ n from hn), Nat.cast_one]
      nlinarith
    · rw [Nat.cast_sub (show 1 ≤ n from hn), Nat.cast_one]
      nlinarith [ht.2]

/-- Distance in `Fin 1 → ℝ`. -/
@[tmio T, powerlib_foundation] theorem dist_fin_one (v w : Fin 1 → ℝ) :
    dist v w = |v 0 - w 0| := by
  refine le_antisymm ((dist_pi_le_iff (abs_nonneg _)).mpr fun i => ?_) ?_
  · fin_cases i; simp [Real.dist_eq]
  · simpa [Real.dist_eq] using dist_le_pi_dist v w 0

/-- **Deviation of the interpolation** on the step containing `t`:
`|π_n x(t) − x(t)| ≤ |x(0)| + |x(t) − x(kΔ)| + |x((k+1)Δ) − x(kΔ)|`. -/
@[tmio T, powerlib_foundation] theorem abs_polyInterp_sub_le (hT : 0 < (T : ℝ)) (hn : 0 < n)
    (x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) (t : Icc (0 : ℝ) T) :
    ∃ k : Fin n, ((k : ℕ) : ℝ) * mesh T n ≤ t ∧ (t : ℝ) ≤ ((k : ℕ) : ℝ) * mesh T n + mesh T n ∧
      |polyInterp T n x t 0 - x t 0| ≤ |pathExt x 0 0| + |x t 0 - pathExt x (node T n k) 0| +
        |pathExt x (node T n (k + 1)) 0 - pathExt x (node T n k) 0| := by
  have hΔ := mesh_pos hT hn
  have hsΔ := Real.sqrt_pos.mpr hΔ
  obtain ⟨k, h1, h2⟩ := exists_step hT hn t.2
  refine ⟨k, h1, h2, ?_⟩
  have hstep := polyPath_step hT hn (nodeIncr T n x) k t.2 h1 h2
  have hnode := polyInterp_node hT hn x k.2.le
  have h0 : (node T n 0 : ℝ) = 0 := by simp [node]
  rw [h0] at hnode
  have hl0 : 0 ≤ (t - ((k : ℕ) : ℝ) * mesh T n) / mesh T n := div_nonneg (by linarith) hΔ.le
  have hl1 : (t - ((k : ℕ) : ℝ) * mesh T n) / mesh T n ≤ 1 := by
    rw [div_le_one hΔ]; linarith
  set lam := (t - ((k : ℕ) : ℝ) * mesh T n) / mesh T n with hlam
  set d := pathExt x (node T n (k + 1)) 0 - pathExt x (node T n k) 0 with hd
  have hy : √(mesh T n) * nodeIncr T n x k = d := by
    rw [nodeIncr, mul_div_cancel₀ _ hsΔ.ne']
  have e : polyInterp T n x t 0 - x t 0 =
      (pathExt x (node T n k) 0 - x t 0) - pathExt x 0 0 + lam * d := by
    have ht' : t = ⟨(t : ℝ), t.2⟩ := rfl
    rw [polyInterp, ht', hstep]
    change polyInterp T n x _ 0 + _ - _ = _
    rw [hnode, mul_assoc, ← mul_assoc (√(mesh T n)) _ lam, hy]
    ring
  rw [e]
  calc |(pathExt x (node T n k) 0 - x t 0) - pathExt x 0 0 + lam * d|
      ≤ |pathExt x (node T n k) 0 - x t 0| + |pathExt x 0 0| + |lam * d| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ |pathExt x (node T n k) 0 - x t 0| + |pathExt x 0 0| + |d| := by
        rw [abs_mul, abs_of_nonneg hl0]
        nlinarith [abs_nonneg d]
    _ = _ := by rw [abs_sub_comm]; ring

/-- **The polygonal interpolations converge uniformly** to a path starting at `0`. -/
@[tmio T, powerlib_foundation] theorem tendsto_polyInterp (hT : 0 < (T : ℝ))
    (x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) (hx0 : pathExt x 0 0 = 0) :
    Tendsto (fun n => polyInterp T n x) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨ρ, hρ, hux⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous x.continuous) (η / 3) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt ((T : ℝ) / ρ)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn0 : 0 < n := by omega
  have hΔ := mesh_pos hT hn0
  have hΔρ : mesh T n < ρ := by
    rw [mesh, div_lt_iff₀ (by exact_mod_cast hn0)]
    rw [div_lt_iff₀ hρ] at hN
    have : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
    nlinarith
  have hdist : ∀ t : Icc (0 : ℝ) T, dist (polyInterp T n x t) (x t) ≤ 2 * (η / 3) := by
    intro t
    obtain ⟨k, h1, h2, hb⟩ := abs_polyInterp_sub_le hT hn0 x t
    rw [dist_fin_one]
    have hk : ((k : ℕ) : ℝ) ≤ n := by exact_mod_cast k.2.le
    have hk1 : ((k : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast k.2
    have hTn : (T : ℝ) = n * mesh T n := by rw [mesh]; field_simp
    have hmk : (node T n k : ℝ) ∈ Icc (0 : ℝ) T := node_mem hn0 k.2.le
    have hmk1 : (node T n (k + 1) : ℝ) ∈ Icc (0 : ℝ) T := node_mem hn0 k.2
    rw [pathExt_of_mem x hmk, pathExt_of_mem x hmk1, hx0] at hb
    have hd1 : dist t (⟨_, hmk⟩ : Icc (0 : ℝ) T) < ρ := by
      simp only [Subtype.dist_eq, Real.dist_eq]
      rw [coe_node, abs_of_nonneg (by linarith)]
      linarith
    have hd2 : dist (⟨_, hmk1⟩ : Icc (0 : ℝ) T) (⟨_, hmk⟩ : Icc (0 : ℝ) T) < ρ := by
      simp only [Subtype.dist_eq, Real.dist_eq]
      rw [coe_node, coe_node]
      push_cast
      rw [show (((k : ℕ) : ℝ) + 1) * mesh T n - ((k : ℕ) : ℝ) * mesh T n = mesh T n by ring,
        abs_of_pos hΔ]
      exact hΔρ
    have e1 : |x t 0 - x ⟨_, hmk⟩ 0| < η / 3 := by
      have := hux hd1
      rwa [dist_fin_one] at this
    have e2 : |x ⟨_, hmk1⟩ 0 - x ⟨_, hmk⟩ 0| < η / 3 := by
      have := hux hd2
      rwa [dist_fin_one] at this
    simp only [abs_zero, zero_add] at hb
    linarith
  calc dist (polyInterp T n x) x ≤ 2 * (η / 3) :=
        (ContinuousMap.dist_le (by positivity)).mpr hdist
    _ < η := by linarith

/-! ## The rate of the interpolation -/

/-- **Cauchy–Schwarz on an interval**: `(∫_a^b u)² ≤ (b − a) ∫_a^b u²`. -/
@[tmio T, powerlib_foundation] theorem sq_integral_le {u : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hu : IntervalIntegrable u volume a b)
    (hu2 : IntervalIntegrable (fun t => u t ^ 2) volume a b) :
    (∫ t in a..b, u t) ^ 2 ≤ (b - a) * ∫ t in a..b, u t ^ 2 := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  set L := b - a with hL
  have hL0 : 0 < L := by rw [hL]; linarith
  set c := (∫ t in a..b, u t) / L with hc
  have hnn : 0 ≤ ∫ t in a..b, (u t - c) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun t _ => sq_nonneg _
  have e : ∫ t in a..b, (u t - c) ^ 2 =
      (∫ t in a..b, u t ^ 2) - 2 * c * (∫ t in a..b, u t) + c ^ 2 * L := by
    have h1 : (fun t => (u t - c) ^ 2) = fun t => (u t ^ 2 - 2 * c * u t) + c ^ 2 := by
      funext t; ring
    rw [h1, intervalIntegral.integral_add (hu2.sub (hu.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub hu2 (hu.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [e] at hnn
  have : c * L = ∫ t in a..b, u t := by rw [hc]; field_simp
  nlinarith

/-- **The rate does not increase under polygonal interpolation**: `I(π_n x) ≤ I(x)`
(discrete Cauchy–Schwarz on each step). -/
@[tmio T, powerlib_foundation] theorem schilderRate_polyInterp_le (hT : 0 < (T : ℝ))
    (hn : 0 < n) (x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) :
    schilderRate T (polyInterp T n x) ≤ schilderRate T x := by
  rw [polyInterp, schilderRate_polyPath hT hn]
  unfold schilderRate
  refine le_iInf₂ fun u ⟨hu, hu2, hxu⟩ => ENNReal.ofReal_le_ofReal ?_
  have hΔ := mesh_pos hT hn
  have hsΔ := Real.sqrt_pos.mpr hΔ
  set v : ℝ → ℝ := fun s => u s 0 with hv
  have hT0 := T.coe_nonneg
  have hvi : IntervalIntegrable v volume 0 T :=
    ⟨(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).integrable_comp hu.1,
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).integrable_comp hu.2⟩
  have hv2 : IntervalIntegrable (fun s => v s ^ 2) volume 0 T := by
    simpa [hv] using hu2
  set t : ℕ → ℝ := fun j => (node T n j : ℝ) with ht
  have hmem : ∀ j, j ≤ n → t j ∈ Icc (0 : ℝ) T := fun j hj => node_mem hn hj
  have hsubI : ∀ j, j ≤ n → uIcc (0 : ℝ) (t j) ⊆ uIcc 0 T := fun j hj => by
    rw [uIcc_of_le (hmem j hj).1, uIcc_of_le hT0]; exact Icc_subset_Icc_right (hmem j hj).2
  have hsubJ : ∀ j, j < n → uIcc (t j) (t (j + 1)) ⊆ uIcc 0 T := fun j hj => by
    have h1 := hmem j hj.le
    have h2 := hmem (j + 1) hj
    rw [uIcc_of_le (by simp only [ht, coe_node]; push_cast; nlinarith), uIcc_of_le hT0]
    exact Icc_subset_Icc h1.1 h2.2
  -- the node values are integrals of `v`
  have hxv : ∀ j, j ≤ n → pathExt x (node T n j) 0 = ∫ s in (0 : ℝ)..t j, v s := by
    intro j hj
    rw [pathExt_of_mem x (hmem j hj), hxu]
    change (∫ s in (0 : ℝ)..t j, u s) 0 = ∫ s in (0 : ℝ)..t j, u s 0
    exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0
      ).intervalIntegral_comp_comm (hu.mono_set (hsubI j hj))).symm
  have hinc : ∀ k : Fin n, (nodeIncr T n x k) ^ 2 ≤ ∫ s in t k..t (k + 1), v s ^ 2 := by
    intro k
    have hk := k.2
    rw [nodeIncr, hxv _ hk, hxv _ hk.le,
      intervalIntegral.integral_interval_sub_left (hvi.mono_set (hsubI _ hk))
        (hvi.mono_set (hsubI _ hk.le)), div_pow, Real.sq_sqrt hΔ.le]
    have hlen : t (k + 1) - t k = mesh T n := by
      simp only [ht, coe_node]; push_cast; ring
    have hcs := sq_integral_le (by linarith : t k ≤ t (k + 1)) (hvi.mono_set (hsubJ _ hk))
      (hv2.mono_set (hsubJ _ hk))
    rw [hlen] at hcs
    rw [div_le_iff₀ hΔ]
    linarith
  have hsum : ∑ k : Fin n, ∫ s in t k..t (k + 1), v s ^ 2 = ∫ s in (0 : ℝ)..T, v s ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => ∫ s in t k..t (k + 1), v s ^ 2) n,
      intervalIntegral.sum_integral_adjacent_intervals fun k hk => hv2.mono_set (hsubJ k hk)]
    have h0 : t 0 = 0 := by simp [ht, node]
    have hn' : t n = T := by simp only [ht, coe_node, mesh]; field_simp
    rw [h0, hn']
  unfold controlAction
  have hu2' : (fun s => ∑ j, u s j ^ 2) = fun s => v s ^ 2 := by
    funext s; simp [hv]
  rw [hu2', ← hsum, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  linarith [hinc k]

end powerlib.Stochastic.LDP
