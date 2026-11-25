import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.Brownian
import theorem.Stochastic.GaussianLDP
import theorem.Stochastic.AdditiveNoise

/-! # Schilder's theorem for the polygonal approximation of Brownian motion

The finite-dimensional step of Schilder's theorem: for a fixed uniform partition of `[0, T]` into
`n` steps, the polygonal interpolation of `√ε B` (`B` a pre-Brownian motion, Mathlib's
`IsPreBrownianReal`) satisfies the large-deviation principle on `C([0, T])` as `ε → 0⁺`, with the
Schilder rate `½ ∫ ẇ²` on polygonal paths and `∞` elsewhere.

Scope.
* Probability theory, not an engineering result. Uniform mesh `Δ = T/n`, `T > 0`, `n ≥ 1`; paths
  in `C([0, T], ℝ)` written `C([0, T], Fin 1 → ℝ)` (the noise space of
  `theorem/Stochastic/AdditiveNoise.lean`).
* Only the polygonal approximation is treated here; the passage to `√ε B` itself (exponential
  equivalence, goodness of the rate, transfer) is `theorem/Stochastic/Schilder.lean`.

Source: A. Dembo, O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed. (1998),
proof of Thm 5.2.3 (Schilder), first step (the polygonal approximations), and Thm 4.2.1
(contraction principle); Mathlib's `ProbabilityTheory.IsPreBrownianReal` (independent Gaussian
increments).

Results.
* `ramp`, `mesh`, `node`, `polyPath` (`w(t) = √Δ Σ_k y_k ramp_k(t)`, increments `√Δ y_k`),
  `polyNoise` (the normalized scaled increments `√ε (B_{(k+1)Δ} − B_{kΔ})/√Δ`).
* `polyPath_node` (`w(kΔ) = √Δ Σ_{j<k} y_j`) and `polyPath_polyNoise_node`
  (`polyPath (polyNoise B ε) (kΔ) = √ε (B_{kΔ} − B_0)`): the path is the polygonal interpolation of
  `√ε B` (exactly, when `B_0 = 0`).
* `continuous_polyPath`, `nodeIncr`, `polyInterp` (the polygonal interpolation of a path),
  `continuous_nodeIncr`, `continuous_polyInterp`, `nodeIncr_polyPath`,
  `exists_leftInverse_polyPath` (the normalized increments are recovered continuously);
  `hasDerivWithinAt_ramp`; `schilderRate_polyPath` (the Schilder rate of a polygonal path is
  `|y|²/2`).
* `map_polyNoise`: the scaled increments of a pre-Brownian motion have the law `gaussLaw n ε`
  (independent increments).
* **`isLDP_polygon`**: the laws of the polygonal interpolations of `√ε B` satisfy the
  large-deviation principle with the rate `schilderRate T` on polygonal paths (`∞` elsewhere).
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped ENNReal NNReal Classical

variable {T : ℝ≥0} {n : ℕ}

/-- The ramp `t ↦ min(1, max(0, (t − a)/Δ))`. -/
def ramp (Δ a t : ℝ) : ℝ := max 0 (min 1 ((t - a) / Δ))

/-- Mesh `Δ = T/n` of the uniform partition. -/
def mesh (T : ℝ≥0) (n : ℕ) : ℝ := T / n

/-- Partition node `j Δ` (as a time in `ℝ≥0`). -/
def node (T : ℝ≥0) (n j : ℕ) : ℝ≥0 := j * (T / n)

@[tmio T, powerlib_foundation] theorem continuous_ramp (Δ a : ℝ) : Continuous (ramp Δ a) :=
  continuous_const.max (continuous_const.min ((continuous_id.sub continuous_const).div_const Δ))

/-- **Polygonal path** with normalized increments `y`: `w(t) = √Δ Σ_k y_k ramp_k(t)` (linear on
each step, increment `√Δ y_k` over `[kΔ, (k+1)Δ]`, `w(0) = 0`). -/
def polyPath (T : ℝ≥0) (n : ℕ) (y : Fin n → ℝ) : C(Icc (0 : ℝ) T, Fin 1 → ℝ) :=
  ⟨fun t _ => √(mesh T n) * ∑ k : Fin n, y k * ramp (mesh T n) (k * mesh T n) t,
    continuous_pi fun _ => continuous_const.mul (continuous_finsetSum _ fun _ _ =>
      continuous_const.mul ((continuous_ramp _ _).comp continuous_subtype_val))⟩

/-- Normalized scaled increments `√ε (B_{(k+1)Δ} − B_{kΔ})/√Δ` of `B` over the partition. -/
def polyNoise {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ε : ℝ) (ω : Ω) :
    Fin n → ℝ :=
  fun k => √ε * (B (node T n (k + 1)) ω - B (node T n k) ω) / √(mesh T n)

@[tmio T, powerlib_foundation] theorem coe_node (T : ℝ≥0) (n j : ℕ) :
    (node T n j : ℝ) = j * mesh T n := by
  simp [node, mesh]

@[tmio T, powerlib_foundation] theorem mesh_pos (hT : 0 < (T : ℝ)) (hn : 0 < n) :
    0 < mesh T n :=
  div_pos hT (by exact_mod_cast hn)

@[tmio T, powerlib_foundation] theorem node_mem (hn : 0 < n) {j : ℕ} (hj : j ≤ n) :
    (node T n j : ℝ) ∈ Icc (0 : ℝ) T := by
  rw [coe_node, mesh]
  refine ⟨by positivity, ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [mul_div_assoc', div_le_iff₀ hn']
  have : (j : ℝ) ≤ n := by exact_mod_cast hj
  nlinarith [T.coe_nonneg]

/-- The ramp at a node: `ramp_j(kΔ) = 1` if `j < k`, `0` otherwise. -/
@[tmio T, powerlib_foundation] theorem ramp_node {Δ : ℝ} (hΔ : 0 < Δ) (j k : ℕ) :
    ramp Δ (j * Δ) (k * Δ) = if j < k then 1 else 0 := by
  have e : ((k : ℝ) * Δ - j * Δ) / Δ = (k : ℝ) - j := by field_simp
  rw [ramp, e]
  split_ifs with h
  · have : (1 : ℝ) ≤ (k : ℝ) - j := by
      have : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
      linarith
    rw [min_eq_left this, max_eq_right zero_le_one]
  · have : (k : ℝ) - j ≤ 0 := by
      have : (k : ℝ) ≤ j := by exact_mod_cast not_lt.mp h
      linarith
    rw [min_eq_right (this.trans zero_le_one), max_eq_left this]

/-- **Values at the nodes**: `w(kΔ) = √Δ Σ_{j<k} y_j`. -/
@[tmio T, powerlib_foundation] theorem polyPath_node (hT : 0 < (T : ℝ)) (hn : 0 < n)
    (y : Fin n → ℝ) {k : ℕ} (hk : k ≤ n) :
    polyPath T n y ⟨node T n k, node_mem hn hk⟩ 0 =
      √(mesh T n) * ∑ j : Fin n, if (j : ℕ) < k then y j else 0 := by
  simp only [polyPath, ContinuousMap.coe_mk, coe_node, ramp_node (mesh_pos hT hn)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- **The path is the polygonal interpolation of `√ε B`**: at the node `kΔ` it equals
`√ε (B_{kΔ} − B_0)`. -/
@[tmio T, powerlib_foundation] theorem polyPath_polyNoise_node {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (hT : 0 < (T : ℝ)) (hn : 0 < n) {ε : ℝ} (ω : Ω) {k : ℕ} (hk : k ≤ n) :
    polyPath T n (polyNoise B T n ε ω) ⟨node T n k, node_mem hn hk⟩ 0 =
      √ε * (B (node T n k) ω - B (node T n 0) ω) := by
  rw [polyPath_node hT hn _ hk]
  have hΔ := Real.sqrt_pos.mpr (mesh_pos hT hn)
  have e : ∀ j : Fin n, (if (j : ℕ) < k then polyNoise B T n ε ω j else 0) =
      (if (j : ℕ) < k then √ε * (B (node T n (j + 1)) ω - B (node T n j) ω) else 0) /
        √(mesh T n) := by
    intro j; split_ifs <;> simp [polyNoise]
  simp_rw [e, ← Finset.sum_div]
  rw [mul_div_cancel₀ _ hΔ.ne']
  have hsum : (∑ j : Fin n, if (j : ℕ) < k then
      √ε * (B (node T n (j + 1)) ω - B (node T n j) ω) else 0) =
      ∑ j ∈ Finset.range k, √ε * (B (node T n (j + 1)) ω - B (node T n j) ω) := by
    rw [Finset.sum_fin_eq_sum_range]
    rw [← Finset.sum_range_add_sum_Ico _ hk]
    rw [Finset.sum_eq_zero (s := Finset.Ico k n) fun j hj => by
      simp [not_lt.mpr (Finset.mem_Ico.mp hj).1]]
    rw [add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk := Finset.mem_range.mp hj
    simp [hjk, hjk.trans_le hk]
  rw [hsum, ← Finset.mul_sum, Finset.sum_range_sub (fun j => B (node T n j) ω)]

/-- `y ↦ w` is continuous (it is linear on a finite-dimensional space). -/
@[tmio T, powerlib_foundation] theorem continuous_polyPath : Continuous (polyPath T n) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  refine continuous_pi fun _ => continuous_const.mul (continuous_finsetSum _ fun k _ => ?_)
  exact ((continuous_apply k).comp continuous_fst).mul
    ((continuous_ramp _ _).comp (continuous_subtype_val.comp continuous_snd))

/-- Normalized node increments `(x((k+1)Δ) − x(kΔ))/√Δ` of a path. -/
def nodeIncr (T : ℝ≥0) (n : ℕ) (x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) : Fin n → ℝ :=
  fun k => (pathExt x (node T n (k + 1)) 0 - pathExt x (node T n k) 0) / √(mesh T n)

/-- **Polygonal interpolation** of a path over the uniform partition: the polygonal path with the
node increments of `x` (it equals `x(kΔ) − x(0)` at the nodes, `polyInterp_node`). -/
def polyInterp (T : ℝ≥0) (n : ℕ) (x : C(Icc (0 : ℝ) T, Fin 1 → ℝ)) :
    C(Icc (0 : ℝ) T, Fin 1 → ℝ) :=
  polyPath T n (nodeIncr T n x)

@[tmio T, powerlib_foundation] theorem continuous_nodeIncr : Continuous (nodeIncr T n) := by
  have hev : ∀ s : ℝ, Continuous fun x : C(Icc (0 : ℝ) T, Fin 1 → ℝ) => pathExt x s 0 :=
    fun s => (continuous_apply (0 : Fin 1)).comp (continuous_eval_const _)
  exact continuous_pi fun k => ((hev _).sub (hev _)).div_const _

@[tmio T, powerlib_foundation] theorem continuous_polyInterp : Continuous (polyInterp T n) :=
  continuous_polyPath.comp continuous_nodeIncr

/-- The node increments of a polygonal path are its coefficients. -/
@[tmio T, powerlib_foundation] theorem nodeIncr_polyPath (hT : 0 < (T : ℝ)) (hn : 0 < n)
    (y : Fin n → ℝ) : nodeIncr T n (polyPath T n y) = y := by
  funext k
  have hΔ := Real.sqrt_pos.mpr (mesh_pos hT hn)
  have hm : (k : ℕ) + 1 ≤ n := k.2
  rw [nodeIncr, pathExt_of_mem _ (node_mem hn hm), pathExt_of_mem _ (node_mem hn k.2.le),
    polyPath_node hT hn y hm, polyPath_node hT hn y k.2.le, ← mul_sub,
    mul_div_cancel_left₀ _ hΔ.ne', ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hjk
    have : (j : ℕ) ≠ k := fun h => hjk (Fin.ext h)
    split_ifs with h1 h2 <;> first | omega | exact sub_self _
  · simp

/-- **Continuous left inverse**: the normalized increments
`(w((k+1)Δ) − w(kΔ))/√Δ` of a polygonal path are its coefficients. -/
@[tmio T, powerlib_foundation] theorem exists_leftInverse_polyPath (hT : 0 < (T : ℝ))
    (hn : 0 < n) :
    ∃ G : C(Icc (0 : ℝ) T, Fin 1 → ℝ) → (Fin n → ℝ), Continuous G ∧
      ∀ y, G (polyPath T n y) = y :=
  ⟨nodeIncr T n, continuous_nodeIncr, nodeIncr_polyPath hT hn⟩

/-! ## The law of the scaled increments -/

/-- **Increments of a pre-Brownian motion**: the normalized scaled increments over the uniform
partition have the law of `√ε Z`, `Z` standard Gaussian in `ℝⁿ`. -/
@[tmio T, powerlib_foundation] theorem map_polyNoise {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hT : 0 < (T : ℝ)) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    P.map (polyNoise B T n ε) = gaussLaw n ε := by
  have hΔ := mesh_pos hT hn
  set c : ℝ := √ε / √(mesh T n) with hc
  set f : Fin n → Ω → ℝ := fun k ω => B (node T n (k + 1)) ω - B (node T n k) ω with hf
  have hmono : Monotone fun j : Fin (n + 1) => node T n j := fun i j hij => by
    simp only [node]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) zero_le
  have hind : iIndepFun f P := by
    have := hB.hasIndepIncrements n (fun j : Fin (n + 1) => node T n j) hmono
    simpa [hf, Fin.val_succ] using this
  have hind' : iIndepFun (fun k => (fun x => c * x) ∘ f k) P :=
    hind.comp _ fun _ => measurable_const_mul c
  have hfm : ∀ k, AEMeasurable (f k) P := fun k =>
    (hB.aemeasurable _).sub (hB.aemeasurable _)
  have hlaw : ∀ k : Fin n, P.map ((fun x => c * x) ∘ f k) =
      gaussianReal 0 (Real.toNNReal ε) := by
    intro k
    have hst : node T n k ≤ node T n (k + 1) := by
      simp only [node]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ _) zero_le
    have h1 := (Stochastic.BM.increment_hasLaw hB hst).map_eq
    rw [← AEMeasurable.map_map_of_aemeasurable (measurable_const_mul c).aemeasurable (hfm k)]
    simp only [hf]
    rw [h1, gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_sub hst, coe_node,
      Real.coe_toNNReal _ hε.le]
    rw [hc, div_pow, Real.sq_sqrt hε.le, Real.sq_sqrt hΔ.le]
    push_cast
    field_simp
    ring
  have hmap := hind'.map_fun_eq_pi_map fun k =>
    (measurable_const_mul c).comp_aemeasurable (hfm k)
  have e : polyNoise B T n ε = fun ω k => ((fun x => c * x) ∘ f k) ω := by
    funext ω k
    simp only [polyNoise, hf, hc, Function.comp]
    ring
  rw [e, hmap, gaussLaw]
  simp_rw [hlaw]

/-! ## The Schilder rate of a polygonal path -/

/-- **Right derivative of the ramp**: `1/Δ` on `[a, a + Δ)`, `0` elsewhere. -/
@[tmio T, powerlib_foundation] theorem hasDerivWithinAt_ramp {Δ : ℝ} (hΔ : 0 < Δ) (a t : ℝ) :
    HasDerivWithinAt (ramp Δ a) ((Ico a (a + Δ)).indicator (fun _ => 1 / Δ) t) (Ici t) t := by
  rcases lt_or_ge t a with h1 | h1
  · rw [indicator_of_notMem (fun h => absurd h.1 (not_le.mpr h1))]
    have hz : ∀ s, s ≤ a → ramp Δ a s = 0 := fun s hs => by
      have : (s - a) / Δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hΔ.le
      rw [ramp, min_eq_right (this.trans zero_le_one), max_eq_left this]
    refine (hasDerivWithinAt_const t (Ici t) (0 : ℝ)).congr_of_eventuallyEq ?_ (hz t h1.le)
    filter_upwards [Ico_mem_nhdsGE h1] with s hs using hz s hs.2.le
  rcases lt_or_ge t (a + Δ) with h2 | h2
  · rw [indicator_of_mem (show t ∈ Ico a (a + Δ) from ⟨h1, h2⟩)]
    have hl : ∀ s, a ≤ s → s < a + Δ → ramp Δ a s = (s - a) / Δ := fun s hs1 hs2 => by
      have h0 : 0 ≤ (s - a) / Δ := div_nonneg (by linarith) hΔ.le
      have h1' : (s - a) / Δ ≤ 1 := by rw [div_le_one hΔ]; linarith
      rw [ramp, min_eq_right h1', max_eq_right h0]
    have hd := ((hasDerivAt_id t).sub_const a).div_const Δ
    refine hd.hasDerivWithinAt.congr_of_eventuallyEq ?_ (hl t h1 h2)
    filter_upwards [Ico_mem_nhdsGE h2] with s hs using hl s (h1.trans hs.1) hs.2
  · rw [indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr h2))]
    have ho : ∀ s, a + Δ ≤ s → ramp Δ a s = 1 := fun s hs => by
      have : 1 ≤ (s - a) / Δ := by rw [le_div_iff₀ hΔ]; linarith
      rw [ramp, min_eq_left this, max_eq_right zero_le_one]
    refine (hasDerivWithinAt_const t (Ici t) (1 : ℝ)).congr_of_eventuallyEq ?_ (ho t h2)
    filter_upwards [self_mem_nhdsWithin] with s (hs : t ≤ s) using ho s (h2.trans hs)

/-- The steps `[kΔ, (k+1)Δ)` are disjoint. -/
@[tmio T, powerlib_foundation] theorem step_unique {Δ : ℝ} (hΔ : 0 < Δ) {j k : Fin n}
    {s : ℝ} (hj : s ∈ Ico ((j : ℕ) * Δ) ((j : ℕ) * Δ + Δ))
    (hk : s ∈ Ico ((k : ℕ) * Δ) ((k : ℕ) * Δ + Δ)) : j = k := by
  have h1 : ((j : ℕ) : ℝ) < (k : ℕ) + 1 := by
    have : ((j : ℕ) : ℝ) * Δ < ((k : ℕ) + 1) * Δ := by linarith [hj.1, hk.2]
    exact lt_of_mul_lt_mul_right this hΔ.le
  have h2 : ((k : ℕ) : ℝ) < (j : ℕ) + 1 := by
    have : ((k : ℕ) : ℝ) * Δ < ((j : ℕ) + 1) * Δ := by linarith [hk.1, hj.2]
    exact lt_of_mul_lt_mul_right this hΔ.le
  have h1' : (j : ℕ) < k + 1 := by exact_mod_cast h1
  have h2' : (k : ℕ) < j + 1 := by exact_mod_cast h2
  exact Fin.ext (by omega)

/-- The square of a step function is the step function of the squares. -/
@[tmio T, powerlib_foundation] theorem sq_sum_steps {Δ : ℝ} (hΔ : 0 < Δ) (c : Fin n → ℝ)
    (s : ℝ) :
    (∑ k : Fin n, (Ico ((k : ℕ) * Δ) ((k : ℕ) * Δ + Δ)).indicator (fun _ => c k) s) ^ 2 =
      ∑ k : Fin n, (Ico ((k : ℕ) * Δ) ((k : ℕ) * Δ + Δ)).indicator (fun _ => c k ^ 2) s := by
  by_cases h : ∃ m : Fin n, s ∈ Ico ((m : ℕ) * Δ) ((m : ℕ) * Δ + Δ)
  · obtain ⟨m, hm⟩ := h
    have hz : ∀ (g : Fin n → ℝ) (k : Fin n), k ≠ m →
        (Ico ((k : ℕ) * Δ) ((k : ℕ) * Δ + Δ)).indicator (fun _ => g k) s = 0 :=
      fun g k hk => indicator_of_notMem (fun hs => hk (step_unique hΔ hs hm)) _
    rw [Finset.sum_eq_single m (fun k _ hk => hz c k hk) (by simp),
      Finset.sum_eq_single m (fun k _ hk => hz (fun k => c k ^ 2) k hk) (by simp),
      indicator_of_mem hm, indicator_of_mem hm]
  · push Not at h
    simp [indicator_of_notMem (h _)]

@[tmio T, powerlib_foundation] theorem intervalIntegrable_steps {Δ : ℝ} (c : Fin n → ℝ)
    (a b : ℝ) :
    IntervalIntegrable
      (fun s => ∑ k : Fin n, (Ico ((k : ℕ) * Δ) ((k : ℕ) * Δ + Δ)).indicator (fun _ => c k) s)
      volume a b := by
  have h := IntervalIntegrable.sum (μ := volume) (a := a) (b := b) Finset.univ
    (f := fun (k : Fin n) (s : ℝ) =>
      (Ico ((k : ℕ) * Δ) ((k : ℕ) * Δ + Δ)).indicator (fun _ => c k) s)
    fun k _ => ⟨(integrableOn_const (by simp)).indicator measurableSet_Ico,
      (integrableOn_const (by simp)).indicator measurableSet_Ico⟩
  convert h using 1
  funext s
  simp [Finset.sum_apply]

/-- `∫₀ᵗ Σ_k c_k 1_{[kΔ,(k+1)Δ)} = Δ Σ_k c_k ramp_k(t)` for `t ≥ 0` (right-derivative FTC). -/
@[tmio T, powerlib_foundation] theorem integral_steps {Δ : ℝ} (hΔ : 0 < Δ)
    (c : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in (0 : ℝ)..t,
      ∑ k : Fin n, (Ico ((k : ℕ) * Δ) ((k : ℕ) * Δ + Δ)).indicator (fun _ => c k) s =
      Δ * ∑ k : Fin n, c k * ramp Δ ((k : ℕ) * Δ) t := by
  set F : ℝ → ℝ := fun s => Δ * ∑ k : Fin n, c k * ramp Δ ((k : ℕ) * Δ) s with hF
  have hFc : Continuous F := continuous_const.mul (continuous_finsetSum _ fun k _ =>
    continuous_const.mul (continuous_ramp _ _))
  have hF0 : F 0 = 0 := by
    have h0 : ∀ k : Fin n, c k * ramp Δ ((k : ℕ) * Δ) 0 = 0 := by
      intro k
      have h0 := ramp_node hΔ (k : ℕ) 0
      simp only [Nat.cast_zero, zero_mul, Nat.not_lt_zero, ↓reduceIte] at h0
      rw [h0, mul_zero]
    simp only [hF, h0, Finset.sum_const_zero, mul_zero]
  have hder : ∀ s, HasDerivWithinAt F
      (∑ k : Fin n, (Ico ((k : ℕ) * Δ) ((k : ℕ) * Δ + Δ)).indicator (fun _ => c k) s)
      (Ici s) s := by
    intro s
    have h := (HasDerivWithinAt.fun_sum (u := (Finset.univ : Finset (Fin n))) fun k _ =>
      (hasDerivWithinAt_ramp hΔ ((k : ℕ) * Δ) s).const_mul (c k)).const_mul Δ
    convert h using 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hs : s ∈ Ico ((k : ℕ) * Δ) ((k : ℕ) * Δ + Δ)
    · rw [indicator_of_mem hs, indicator_of_mem hs]; field_simp
    · rw [indicator_of_notMem hs, indicator_of_notMem hs]; simp
  have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hFc.continuousOn
    (fun s _ => (hder s).mono Ioi_subset_Ici_self) (intervalIntegrable_steps c 0 t)
  rw [this, hF0, sub_zero]

/-- **The Schilder rate of a polygonal path** is `|y|²/2`. -/
@[tmio T, powerlib_foundation] theorem schilderRate_polyPath (hT : 0 < (T : ℝ)) (hn : 0 < n)
    (y : Fin n → ℝ) : schilderRate T (polyPath T n y) = gaussRate n y := by
  set Δ := mesh T n with hΔdef
  have hΔ : 0 < Δ := mesh_pos hT hn
  have hsΔ : 0 < √Δ := Real.sqrt_pos.mpr hΔ
  set g : ℝ → ℝ := fun s =>
    ∑ k : Fin n, (Ico ((k : ℕ) * Δ) ((k : ℕ) * Δ + Δ)).indicator (fun _ => y k / √Δ) s with hg
  set u : ℝ → Fin 1 → ℝ := fun s => g s • fun _ => (1 : ℝ) with hu
  have hgi : ∀ a b, IntervalIntegrable g volume a b := fun a b => intervalIntegrable_steps _ a b
  have hui : IntervalIntegrable u volume 0 T :=
    ⟨(hgi 0 T).1.smul_const _, (hgi 0 T).2.smul_const _⟩
  have hsq : ∀ s, ∑ j, u s j ^ 2 =
      ∑ k : Fin n, (Ico ((k : ℕ) * Δ) ((k : ℕ) * Δ + Δ)).indicator
        (fun _ => (y k / √Δ) ^ 2) s := by
    intro s
    simp only [hu, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, mul_one, hg]
    exact sq_sum_steps hΔ _ s
  have hu2 : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) volume 0 T := by
    simp_rw [hsq]; exact intervalIntegrable_steps _ 0 T
  have hW : ∀ t : Icc (0 : ℝ) T, polyPath T n y t = ∫ s in (0 : ℝ)..t, u s := by
    intro t
    rw [intervalIntegral.integral_smul_const, integral_steps hΔ _ t.2.1]
    funext j
    simp only [polyPath, ContinuousMap.coe_mk, Pi.smul_apply, smul_eq_mul, mul_one]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : √Δ * y k = Δ * (y k / √Δ) := by
      rw [mul_div_assoc', eq_div_iff hsΔ.ne']
      linear_combination y k * Real.mul_self_sqrt hΔ.le
    rw [← mul_assoc, this, mul_assoc]
  rw [schilderRate_eq hui hu2 hW, gaussRate]
  congr 1
  unfold controlAction
  simp_rw [hsq]
  rw [integral_steps hΔ _ T.coe_nonneg]
  have hTn : (T : ℝ) = n * Δ := by
    rw [hΔdef, mesh]; field_simp
  have hr : ∀ k : Fin n, ramp Δ ((k : ℕ) * Δ) T = 1 := by
    intro k
    rw [hTn, ramp_node hΔ]
    simp [k.2]
  have hsum : Δ * ∑ k : Fin n, (y k / √Δ) ^ 2 * ramp Δ ((k : ℕ) * Δ) T = ∑ k, y k ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hr k, mul_one, div_pow, Real.sq_sqrt hΔ.le]
    field_simp
  rw [hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ## Schilder's theorem for the polygonal approximation -/

/-- **Schilder, polygonal approximation**: for a pre-Brownian motion `B`, the laws of the
polygonal interpolations of `√ε B` over the uniform partition of `[0, T]` into `n` steps satisfy
the large-deviation principle as `ε → 0⁺`, with the Schilder rate `½ ∫ ẇ²` on polygonal paths and
`∞` elsewhere. -/
@[tmio T, powerlib_foundation] theorem isLDP_polygon {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hT : 0 < (T : ℝ)) (hn : 0 < n) [MeasurableSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)]
    [BorelSpace C(Icc (0 : ℝ) T, Fin 1 → ℝ)] :
    IsLDP (𝓝[>] (0 : ℝ)) id (fun ε => P.map fun ω => polyPath T n (polyNoise B T n ε ω))
      (fun w => if w ∈ range (polyPath T n) then schilderRate T w else ⊤) := by
  obtain ⟨G, hGc, hG⟩ := exists_leftInverse_polyPath (T := T) hT hn
  have h := (isLDP_gaussLaw n).map_of_leftInverse continuous_polyPath hGc hG
  have hrate : pushRate (polyPath T n) (gaussRate n) =
      fun w => if w ∈ range (polyPath T n) then schilderRate T w else ⊤ := by
    funext w
    rw [pushRate_eq_of_leftInverse hG]
    by_cases hw : polyPath T n (G w) = w
    · have hmem : w ∈ range (polyPath T n) := ⟨G w, hw⟩
      simp only [hw, hmem, ↓reduceIte]
      conv_rhs => rw [← hw]
      rw [schilderRate_polyPath hT hn]
    · have hmem : w ∉ range (polyPath T n) := by
        rintro ⟨y, rfl⟩
        exact hw (by rw [hG])
      simp only [hw, hmem, ↓reduceIte]
  rw [hrate] at h
  refine h.congr ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hm : AEMeasurable (polyNoise B T n ε) P :=
    AEMeasurable.of_eval fun k =>
      (((hB.aemeasurable _).sub (hB.aemeasurable _)).const_mul _).div_const _
  rw [← map_polyNoise hB hT hn hε,
    AEMeasurable.map_map_of_aemeasurable continuous_polyPath.aemeasurable hm]
  rfl

end powerlib.Stochastic.LDP
