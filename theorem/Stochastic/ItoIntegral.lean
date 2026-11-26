import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.ItoFormula
import Mathlib.MeasureTheory.Function.L2Space

/-! # The Itô integral of continuous adapted integrands

For a bounded integrand `H` known at time `t` (natural filtration of a Brownian motion `B`) with
continuous paths, the left Riemann sums `∑_{i<2^k} H(tᵢ)(B(t_{i+1}) − B(tᵢ))` along the dyadic
grids of `[0, T]` form a Cauchy sequence in `L²` (refined sums differ by a martingale transform
whose coefficients are oscillations of `H` over one cell; isometry and dominated convergence), so
they converge in `L²` to the **Itô integral** `I = ∫₀ᵀ H dB`, which is centred and satisfies the
**Itô isometry** `E I² = ∫₀ᵀ E H_s² ds`. For `H = Dφ(x) n` along an additive-noise solution the
integral is the one of Itô's formula: `I = φ(x_T) − φ(x_0) − ∫₀ᵀ Lφ(x)` almost surely.

Scope.
* Generic probability theory. `B` Mathlib's `IsPreBrownianReal` with strongly measurable `B t`;
  integrands bounded with continuous paths (no localisation, no predictable σ-algebra); dyadic
  grids (the limit along any refining sequence of partitions with mesh `→ 0` is the same; not
  stated). The integral is the `L²` limit (a class of functions up to null sets): the theorem
  provides a representative.
* The process `t ↦ ∫₀ᵗ H dB`, its martingale property and path continuity are not stated.

Source: I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed. (1991),
§3.2 (construction for simple integrands, the isometry (3.2.12), extension by `L²` limits,
Prop. 3.2.6 for continuous adapted integrands); B. Øksendal, *Stochastic Differential Equations*,
6th ed. (2003), Def. 3.1.6 and Cor. 3.1.7 (Itô isometry), Thm 3.2.1 (`E ∫ f dB = 0`);
work-sync theory/T-sde-systems.md §1.3.2 (left-point Riemann sums), §1.3.3 (the isometry).

Results.
* `toReal_eLpNorm_two_sq`, `dist_toLp_sq` — `L²` distances as second moments.
* `sum_range_mul_eq`, `grid_refine`, `riemann_refine` (a level-`k` dyadic sum read on level `l`),
  `tendsto_riemann_sum` (Riemann sums of a continuous function).
* **`exists_itoIntegral`** — existence of the `L²` limit, `E I = 0`, `E I² = ∫₀ᵀ E H_s² ds`.
* **`exists_itoIntegral_eq_ito_formula`** — Itô's formula with the Itô integral (additive noise).
-/

noncomputable section
namespace powerlib.Stochastic.Ito

open MeasureTheory ProbabilityTheory Real Filter Finset Set
open scoped NNReal ENNReal Topology
open powerlib.Stochastic.BM (incr)
open powerlib.Stochastic.QV (step)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-! ## Distances in `L²` -/

/-- `‖f‖₂² = E f²`. -/
@[tmio T, powerlib_foundation] theorem toReal_eLpNorm_two_sq {f : Ω → ℝ} (hf : MemLp f 2 P) :
    (eLpNorm f 2 P).toReal ^ 2 = ∫ ω, f ω ^ 2 ∂P := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have h0 : 0 ≤ ∫ ω, ‖f ω‖ ^ (2 : ℝ≥0∞).toReal ∂P := integral_nonneg fun ω => by positivity
  rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num

/-- `dist(f, g)² = E (f − g)²` in `L²`. -/
@[tmio T, powerlib_foundation] theorem dist_toLp_sq {f g : Ω → ℝ} (hf : MemLp f 2 P)
    (hg : MemLp g 2 P) : dist (hf.toLp f) (hg.toLp g) ^ 2 = ∫ ω, (f ω - g ω) ^ 2 ∂P := by
  rw [Lp.dist_def, eLpNorm_congr_ae ((hf.coeFn_toLp).sub (hg.coeFn_toLp))]
  exact toReal_eLpNorm_two_sq (hf.sub hg)

/-! ## Refinement of dyadic Riemann sums -/

/-- `∑_{j < r m} g j = ∑_{i<m} ∑_{q<r} g (r i + q)`. -/
@[tmio T, powerlib_foundation] theorem sum_range_mul_eq (g : ℕ → ℝ) (r m : ℕ) :
    ∑ j ∈ range (r * m), g j = ∑ i ∈ range m, ∑ q ∈ range r, g (r * i + q) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

/-- The dyadic grid of level `l` refines that of level `k ≤ l`: `t_k(i) = t_l(2^{l−k} i)`. -/
@[tmio T, powerlib_foundation] theorem grid_refine (T : ℝ≥0) {k l : ℕ} (hkl : k ≤ l) (i : ℕ) :
    ((2 ^ (l - k) * i : ℕ) : ℝ≥0) * (T / (2 ^ l : ℕ)) = (i : ℝ≥0) * (T / (2 ^ k : ℕ)) := by
  have h : (2 : ℝ≥0) ^ l = 2 ^ (l - k) * 2 ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkl]
  push_cast
  rw [h]
  field_simp

/-- **Left Riemann sums along refined grids**: the level-`k` sum of `H` against `B` is the
level-`l` sum with the coefficients frozen at the level-`k` left points. -/
@[tmio T, powerlib_foundation] theorem riemann_refine (H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) {k l : ℕ}
    (hkl : k ≤ l) (ω : Ω) :
    ∑ i ∈ range (2 ^ k), H ((i : ℝ≥0) * (T / (2 ^ k : ℕ))) ω *
        incr B (fun i : ℕ => (i : ℝ≥0) * (T / (2 ^ k : ℕ))) i ω =
      ∑ j ∈ range (2 ^ l), H (((2 ^ (l - k) * (j / 2 ^ (l - k)) : ℕ) : ℝ≥0) *
        (T / (2 ^ l : ℕ))) ω * incr B (fun i : ℕ => (i : ℝ≥0) * (T / (2 ^ l : ℕ))) j ω := by
  set r := 2 ^ (l - k) with hr
  have hr0 : 0 < r := by positivity
  have hrl : r * 2 ^ k = 2 ^ l := by rw [hr, ← pow_add, Nat.sub_add_cancel hkl]
  have key := sum_range_mul_eq (fun j => H (((r * (j / r) : ℕ) : ℝ≥0) * (T / (2 ^ l : ℕ))) ω *
    incr B (fun i : ℕ => (i : ℝ≥0) * (T / (2 ^ l : ℕ))) j ω) r (2 ^ k)
  rw [hrl] at key
  rw [key]
  refine sum_congr rfl fun i _ => ?_
  have hdiv : ∀ q < r, (r * i + q) / r = i := fun q hq => by
    rw [Nat.mul_add_div hr0, Nat.div_eq_of_lt hq, add_zero]
  rw [sum_congr rfl fun q hq => by rw [hdiv q (mem_range.mp hq)], ← mul_sum]
  congr 1
  · rw [grid_refine T hkl]
  · have := sum_range_sub (fun q => B (((r * i + q : ℕ) : ℝ≥0) * (T / (2 ^ l : ℕ))) ω) r
    simp only [incr]
    rw [show (fun q => B (((r * i + (q + 1) : ℕ) : ℝ≥0) * (T / (2 ^ l : ℕ))) ω -
        B (((r * i + q : ℕ) : ℝ≥0) * (T / (2 ^ l : ℕ))) ω) = fun q =>
        B (((r * i + q + 1 : ℕ) : ℝ≥0) * (T / (2 ^ l : ℕ))) ω -
        B (((r * i + q : ℕ) : ℝ≥0) * (T / (2 ^ l : ℕ))) ω from rfl] at this
    rw [this, add_zero, ← grid_refine T hkl i, ← grid_refine T hkl (i + 1), ← hr, Nat.mul_succ]

/-- **Riemann sums of a continuous function**: `∑_{i<m} (T/m) g(i T/m) → ∫₀ᵀ g`. -/
@[tmio T, powerlib_foundation] theorem tendsto_riemann_sum {g : ℝ → ℝ} (hg : Continuous g)
    {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun m : ℕ => ∑ i ∈ range m, T / m * g (i * (T / m))) atTop
      (𝓝 (∫ u in (0 : ℝ)..T, g u)) := by
  rcases eq_or_lt_of_le hT with rfl | hT0
  · simp
  have hgu := (isCompact_Icc (a := (0 : ℝ)) (b := T)).uniformContinuousOn_of_continuous
    hg.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hgu
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨ρ, hρ, hgρ⟩ := hgu (ε / (2 * T)) (by positivity)
  have hmesh : Tendsto (fun m : ℕ => T / m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨m₀, hm₀⟩ := (tendsto_order.1 hmesh).2 ρ hρ |>.exists_forall_of_atTop
  refine ⟨max m₀ 1, fun m hm => ?_⟩
  have hm1 : 0 < m := lt_of_lt_of_le one_pos (le_of_max_le_right hm)
  have hh0 : 0 < T / m := by positivity
  have hmh : (m : ℝ) * (T / m) = T := by field_simp
  have hR := abs_riemann_sub_integral_le hg hh0.le (T := T) (η := ε / (2 * T))
    (fun u hu v hv huv => (hgρ u hu v hv (by
      rw [Real.dist_eq]; exact huv.trans_lt (hm₀ m (le_of_max_le_left hm)))).le) m hmh.le
  rw [hmh, show T * (ε / (2 * T)) = ε / 2 by field_simp] at hR
  rw [Real.dist_eq]
  linarith

variable [IsProbabilityMeasure P]

/-- **The Itô integral of a continuous adapted integrand**: for `H` known at time `t` (natural
filtration of `B`), with continuous paths and `|H| ≤ C`, the left Riemann sums
`S_k = ∑_{i<2^k} H(tᵢ) (B(t_{i+1}) − B(tᵢ))` along the dyadic grids of `[0, T]` converge in `L²`
to a limit `I = ∫₀ᵀ H dB`; it is centred and satisfies the **Itô isometry**
`E I² = ∫₀ᵀ E H_s² ds`. -/
@[tmio T, powerlib_foundation] theorem exists_itoIntegral (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) {H : ℝ≥0 → Ω → ℝ} {C : ℝ}
    (hHa : ∀ t, Measurable[Filtration.natural B hm t] (H t))
    (hHc : ∀ ω, Continuous fun t => H t ω) (hHC : ∀ t ω, |H t ω| ≤ C) (T : ℝ≥0) :
    ∃ I : Ω → ℝ, MemLp I 2 P ∧
      Tendsto (fun k : ℕ => ∫ ω, (∑ i ∈ range (2 ^ k), H ((i : ℝ≥0) * (T / (2 ^ k : ℕ))) ω *
        incr B (fun i : ℕ => (i : ℝ≥0) * (T / (2 ^ k : ℕ))) i ω - I ω) ^ 2 ∂P) atTop (𝓝 0) ∧
      ∫ ω, I ω ∂P = 0 ∧ ∫ ω, I ω ^ 2 ∂P = ∫ s in (0 : ℝ)..T, ∫ ω, H s.toNNReal ω ^ 2 ∂P := by
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure P
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hHC 0 ω₀)
  set t : ℕ → ℕ → ℝ≥0 := fun k i => (i : ℝ≥0) * (T / (2 ^ k : ℕ)) with ht
  set S : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ range (2 ^ k), H (t k i) ω * incr B (t k) i ω with hS
  have hle : ∀ s, Filtration.natural B hm s ≤ mΩ := fun s => (Filtration.natural B hm).le s
  have hHm : ∀ s, Measurable (H s) := fun s => (hHa s).mono (hle s) le_rfl
  have hSmem : ∀ k, MemLp (S k) 2 P := fun k =>
    memLp_sum_mul (𝓕 := fun i => Filtration.natural B hm (t k i)) (fun i => hle _)
      (fun i => hHa _) (fun i ω => hHC _ ω)
      (fun i => (QV.incr_hasLaw hB (monotone_grid T (2 ^ k)) i).memLp (memLp_id_gaussianReal 2))
      (2 ^ k)
  have hSm : ∀ k, Measurable (S k) := fun k => Finset.measurable_fun_sum _ fun i _ =>
    (hHm _).mul ((hm _).measurable.sub (hm _).measurable)
  -- the squared increments of the Riemann sums
  set V : ℕ → ℕ → Ω → ℝ := fun k l ω => ∑ j ∈ range (2 ^ l),
    (H (t l j) ω - H (t l (2 ^ (l - k) * (j / 2 ^ (l - k)))) ω) ^ 2 * (T / (2 ^ l : ℕ)) with hV
  have hVm : ∀ k l, Measurable (V k l) := fun k l => Finset.measurable_fun_sum _ fun j _ =>
    (((hHm _).sub (hHm _)).pow_const 2).mul_const _
  have hVb : ∀ k l ω, 0 ≤ V k l ω ∧ V k l ω ≤ 4 * C ^ 2 * T := by
    intro k l ω
    refine ⟨sum_nonneg fun j _ => by positivity, ?_⟩
    calc V k l ω ≤ ∑ j ∈ range (2 ^ l), (2 * C) ^ 2 * (T / (2 ^ l : ℕ)) := by
          refine sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
          have h1 := abs_le.mp (hHC (t l j) ω)
          have h2 := abs_le.mp (hHC (t l (2 ^ (l - k) * (j / 2 ^ (l - k)))) ω)
          nlinarith [h1.1, h1.2, h2.1, h2.2]
      _ = 4 * C ^ 2 * T := by
          rw [sum_const, card_range, nsmul_eq_mul]; push_cast; field_simp; ring
  have hdiff : ∀ k l, k ≤ l → ∫ ω, (S l ω - S k ω) ^ 2 ∂P = ∫ ω, V k l ω ∂P := by
    intro k l hkl
    have hrep : ∀ ω, S l ω - S k ω = ∑ j ∈ range (2 ^ l),
        (H (t l j) ω - H (t l (2 ^ (l - k) * (j / 2 ^ (l - k)))) ω) * incr B (t l) j ω := by
      intro ω
      simp only [hS]
      rw [riemann_refine H T hkl ω, ← sum_sub_distrib]
      refine sum_congr rfl fun j _ => ?_
      ring
    have hmono : ∀ j, 2 ^ (l - k) * (j / 2 ^ (l - k)) ≤ j := fun j => Nat.mul_div_le j _
    have hiso := integral_sq_sum_mul_incr hB hm (monotone_grid T (2 ^ l))
      (a := fun j ω => H (t l j) ω - H (t l (2 ^ (l - k) * (j / 2 ^ (l - k)))) ω) (C := 2 * C)
      (fun j => (hHa _).sub ((hHa _).mono ((Filtration.natural B hm).mono
        (monotone_grid T (2 ^ l) (hmono j))) le_rfl))
      (fun j ω => by
        have h1 := abs_le.mp (hHC (t l j) ω)
        have h2 := abs_le.mp (hHC (t l (2 ^ (l - k) * (j / 2 ^ (l - k)))) ω)
        rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]) (2 ^ l)
    rw [show (fun ω => (S l ω - S k ω) ^ 2) = fun ω => (∑ j ∈ range (2 ^ l),
        (H (t l j) ω - H (t l (2 ^ (l - k) * (j / 2 ^ (l - k)))) ω) * incr B (t l) j ω) ^ 2
        from funext fun ω => by rw [hrep ω], hiso]
    simp only [hV, step_grid]
    have hint : ∀ j, Integrable (fun ω =>
        (H (t l j) ω - H (t l (2 ^ (l - k) * (j / 2 ^ (l - k)))) ω) ^ 2 * (T / (2 ^ l : ℕ))) P :=
      fun j => Integrable.of_bound ((((hHm _).sub (hHm _)).pow_const 2).mul_const
        _).aestronglyMeasurable ((2 * C) ^ 2 * (T / (2 ^ l : ℕ))) (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have h1 := abs_le.mp (hHC (t l j) ω)
          have h2 := abs_le.mp (hHC (t l (2 ^ (l - k) * (j / 2 ^ (l - k)))) ω)
          nlinarith [h1.1, h1.2, h2.1, h2.2])
    rw [integral_finsetSum _ fun j _ => hint j]
    refine sum_congr rfl fun j _ => ?_
    rw [integral_mul_const]
  -- pathwise: the increments vanish uniformly as `k → ∞`
  have hpath : ∀ ω η, 0 < η → ∀ᶠ k in atTop, ∀ l, k ≤ l → V k l ω ≤ T * η ^ 2 := by
    intro ω η hη
    have hu := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).uniformContinuousOn_of_continuous
      (hHc ω).continuousOn
    rw [Metric.uniformContinuousOn_iff] at hu
    obtain ⟨δ, hδ, hδu⟩ := hu η hη
    have hmesh : Tendsto (fun k : ℕ => (T : ℝ) / (2 ^ k : ℕ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2)))
    filter_upwards [(tendsto_order.1 hmesh).2 δ hδ] with k hk l hkl
    have hpow : (0 : ℝ) < (2 ^ l : ℕ) := by positivity
    calc V k l ω ≤ ∑ j ∈ range (2 ^ l), η ^ 2 * (T / (2 ^ l : ℕ)) := by
          refine sum_le_sum fun j hj => mul_le_mul_of_nonneg_right ?_ (by positivity)
          set r := 2 ^ (l - k) with hr
          have hjl : j < 2 ^ l := mem_range.mp hj
          have hrj : r * (j / r) ≤ j := Nat.mul_div_le j r
          have hm1 : t l j ∈ Icc (0 : ℝ≥0) T := ⟨bot_le, grid_le hjl.le⟩
          have hm2 : t l (r * (j / r)) ∈ Icc (0 : ℝ≥0) T := ⟨bot_le, grid_le (hrj.trans hjl.le)⟩
          have hdist : dist (t l j) (t l (r * (j / r))) < δ := by
            rw [NNReal.dist_eq]
            simp only [ht, coe_grid]
            have hmod : j - r * (j / r) < r := by
              have := Nat.mod_lt j (show 0 < r by positivity)
              rw [Nat.mod_def] at this
              exact this
            have hcast : ((j : ℕ) : ℝ) - ((r * (j / r) : ℕ) : ℝ) < r := by
              have := (Nat.cast_lt (α := ℝ)).2 hmod
              rw [Nat.cast_sub hrj] at this
              exact this
            have hrl : ((2 ^ l : ℕ) : ℝ) = r * (2 ^ k : ℕ) := by
              rw [hr]; push_cast; rw [← pow_add, Nat.sub_add_cancel hkl]
            rw [← sub_mul, abs_of_nonneg (mul_nonneg (by linarith [(Nat.cast_le (α := ℝ)).2 hrj])
              (by positivity))]
            calc ((j : ℝ) - ((r * (j / r) : ℕ) : ℝ)) * (T / (2 ^ l : ℕ)) ≤
                (r : ℝ) * (T / (2 ^ l : ℕ)) :=
                  mul_le_mul_of_nonneg_right hcast.le (by positivity)
              _ = T / (2 ^ k : ℕ) := by
                  have hr0 : (r : ℝ) ≠ 0 := by positivity
                  rw [hrl]; field_simp
              _ < δ := hk
          have := hδu _ hm1 _ hm2 hdist
          rw [Real.dist_eq] at this
          have h0 := abs_nonneg (H (t l j) ω - H (t l (r * (j / r))) ω)
          nlinarith [sq_abs (H (t l j) ω - H (t l (r * (j / r))) ω)]
      _ = T * η ^ 2 := by
          rw [sum_const, card_range, nsmul_eq_mul]; field_simp
  -- Cauchy in `L²`
  set u : ℕ → Lp ℝ 2 P := fun k => (hSmem k).toLp (S k) with hu
  have hdu : ∀ k l, k ≤ l → dist (u l) (u k) ^ 2 = ∫ ω, V k l ω ∂P := fun k l hkl => by
    rw [hu, dist_toLp_sq, hdiff k l hkl]
  have hcau : CauchySeq u := by
    rw [Metric.cauchySeq_iff']
    by_contra hc
    push Not at hc
    obtain ⟨ε, hε, hN⟩ := hc
    choose n hn hdist using hN
    have hlim : Tendsto (fun N => ∫ ω, V N (n N) ω ∂P) atTop (𝓝 0) := by
      have := tendsto_integral_of_dominated_convergence (μ := P) (f := fun _ => (0 : ℝ))
        (fun _ => 4 * C ^ 2 * T) (fun N => (hVm N (n N)).aestronglyMeasurable) (integrable_const _)
        (fun N => ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hVb _ _ ω).1]; exact (hVb _ _ ω).2)
        (ae_of_all _ fun ω => ?_)
      · simpa using this
      · rw [Metric.tendsto_atTop]
        intro η hη
        have hη' : 0 < η / (2 * (T + 1)) := by positivity
        obtain ⟨N₀, hN₀⟩ := (hpath ω (Real.sqrt (η / (2 * (T + 1))))
          (Real.sqrt_pos.2 hη')).exists_forall_of_atTop
        refine ⟨N₀, fun N hN => ?_⟩
        have h1 := hN₀ N hN (n N) (hn N)
        rw [Real.sq_sqrt hη'.le] at h1
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (hVb _ _ ω).1]
        calc V N (n N) ω ≤ T * (η / (2 * (T + 1))) := h1
          _ < η := by
            rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
            nlinarith [T.2]
    have hge : ∀ N, ε ^ 2 ≤ ∫ ω, V N (n N) ω ∂P := fun N => by
      rw [← hdu N (n N) (hn N)]
      exact pow_le_pow_left₀ hε.le (hdist N) 2
    have := ge_of_tendsto' hlim hge
    nlinarith
  obtain ⟨Ilim, hlim⟩ := cauchySeq_tendsto_of_complete hcau
  have hImem : MemLp (⇑Ilim) 2 P := Lp.memLp Ilim
  have hIm : Measurable (⇑Ilim) := (Lp.stronglyMeasurable Ilim).measurable
  have hdI : ∀ k, dist (u k) Ilim ^ 2 = ∫ ω, (S k ω - Ilim ω) ^ 2 ∂P := fun k => by
    conv_lhs => rw [← Lp.toLp_coeFn Ilim hImem]
    exact dist_toLp_sq _ _
  have hL2 : Tendsto (fun k => ∫ ω, (S k ω - Ilim ω) ^ 2 ∂P) atTop (𝓝 0) := by
    have := ((tendsto_iff_dist_tendsto_zero.1 hlim).pow 2)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
    exact this.congr hdI
  refine ⟨Ilim, hImem, hL2, ?_, ?_⟩
  · -- the mean
    obtain ⟨C', hC'⟩ := hL2.bddAbove_range
    have hX := tendsto_integral_of_tendstoInMeasure (X := fun k ω => S k ω - Ilim ω) (C := C')
      (fun k => (hSm k).sub hIm) (fun k => (hSmem k).sub hImem)
      (fun k => hC' ⟨k, rfl⟩) (tendstoInMeasure_of_integral_sq (fun k => (hSmem k).sub hImem) hL2)
    have hE : ∀ k, ∫ ω, (S k ω - Ilim ω) ∂P = -∫ ω, Ilim ω ∂P := fun k => by
      rw [integral_sub ((hSmem k).integrable one_le_two) (hImem.integrable one_le_two)]
      have := integral_sum_mul_incr hB hm (monotone_grid T (2 ^ k)) (a := fun i => H (t k i))
        (fun i => hHa _) (fun i ω => hHC _ ω) (2 ^ k)
      rw [show (∫ ω, S k ω ∂P) = 0 from this, zero_sub]
    simp only [hE] at hX
    have := tendsto_nhds_unique hX tendsto_const_nhds
    linarith
  · -- the isometry
    have hnorm : Tendsto (fun k => ‖u k‖ ^ 2) atTop (𝓝 (‖Ilim‖ ^ 2)) :=
      (continuous_norm.tendsto _ |>.comp hlim).pow 2
    have hnk : ∀ k, ‖u k‖ ^ 2 = ∫ ω, S k ω ^ 2 ∂P := fun k => by
      rw [hu, Lp.norm_def, eLpNorm_congr_ae (hSmem k).coeFn_toLp]
      exact toReal_eLpNorm_two_sq (hSmem k)
    have hnI : ‖Ilim‖ ^ 2 = ∫ ω, Ilim ω ^ 2 ∂P := by
      rw [Lp.norm_def]; exact toReal_eLpNorm_two_sq hImem
    rw [← hnI]
    refine tendsto_nhds_unique hnorm ?_
    -- `E S_k² = ∑ E H(tᵢ)² Δ → ∫₀ᵀ E H_s² ds`
    set g : ℝ → ℝ := fun s => ∫ ω, H s.toNNReal ω ^ 2 ∂P with hg
    have hgc : Continuous g := by
      refine continuous_of_dominated (bound := fun _ => C ^ 2)
        (fun s => ((hHm _).pow_const 2).aestronglyMeasurable) (fun s => ae_of_all _ fun ω => ?_)
        (integrable_const _) (ae_of_all _ fun ω => ?_)
      · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hHC _ ω) 2
      · exact ((hHc ω).comp continuous_real_toNNReal).pow 2
    have hpow : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (α := ℕ) (by norm_num)
    have hR := (tendsto_riemann_sum hgc T.2).comp hpow
    refine hR.congr fun k => ?_
    simp only [Function.comp_apply, hnk]
    rw [integral_sq_sum_mul_incr hB hm (monotone_grid T (2 ^ k)) (a := fun i => H (t k i))
      (fun i => hHa _) (fun i ω => hHC _ ω) (2 ^ k)]
    refine sum_congr rfl fun i _ => ?_
    rw [step_grid, mul_comm]
    congr 1
    simp only [hg]
    congr 1
    funext ω
    congr 2
    exact (congrArg Real.toNNReal (coe_grid T (2 ^ k) i).symm).trans Real.toNNReal_coe

open powerlib.Stochastic.LDP (solMap pathExt brownPath)

/-- **Itô's formula with the Itô integral** (additive noise): for `x = S(x₀, c B)` on `[0, T]`,
`n = c N(1)` and `φ ∈ C²` with bounded `Dφ`, `D²φ` and uniformly continuous `D²φ`, the Itô
integral `I = ∫₀ᵀ Dφ(x) n dB` (the `L²` limit of the dyadic left Riemann sums, centred) satisfies
`I = φ(x_T) − φ(x_0) − ∫₀ᵀ Lφ(x(u)) du` almost surely. -/
@[tmio T, powerlib_foundation] theorem exists_itoIntegral_eq_ito_formula
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hB : IsPreBrownianReal B P) (hm : ∀ t, StronglyMeasurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) {T : ℝ≥0} (hT : 0 < (T : ℝ)) {K : ℝ≥0} {b : E → E}
    (hb : LipschitzWith K b) (N : (Fin 1 → ℝ) →L[ℝ] E) (x₀ : E) (c : ℝ) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) {C : ℝ} (hC1 : ∀ y, ‖fderiv ℝ φ y‖ ≤ C)
    (hC2 : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ C) (hu : UniformContinuous (fderiv ℝ (fderiv ℝ φ))) :
    ∃ I : Ω → ℝ, MemLp I 2 P ∧
      Tendsto (fun k : ℕ => ∫ ω, (∑ i ∈ range (2 ^ k), fderiv ℝ φ
        (pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) ((i : ℝ≥0) * (T / (2 ^ k : ℕ))))
          (c • N (fun _ => 1)) * incr B (fun i : ℕ => (i : ℝ≥0) * (T / (2 ^ k : ℕ))) i ω -
            I ω) ^ 2 ∂P) atTop (𝓝 0) ∧ ∫ ω, I ω ∂P = 0 ∧
      I =ᵐ[P] fun ω => φ (pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) T) -
        φ (pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) 0) -
        ∫ u in (0 : ℝ)..T, gen b (c • N (fun _ => 1)) φ
          (pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) u) := by
  set n := c • N (fun _ => 1) with hn
  set X : Ω → ℝ → E := fun ω => pathExt (solMap b N x₀ (c • brownPath B hBc T ω)) with hX
  have hD1c : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have hHa : ∀ t : ℝ≥0, Measurable[Filtration.natural B hm t] fun ω => fderiv ℝ φ (X ω t) n :=
    fun t => measurable_comp_solMap_natural' hb N x₀ c hm hBc T t
      (g := fun y => fderiv ℝ φ y n) (hD1c.clm_apply continuous_const)
  have hHc : ∀ ω, Continuous fun t : ℝ≥0 => fderiv ℝ φ (X ω t) n := fun ω =>
    (hD1c.comp ((LDP.continuous_pathExt _).comp NNReal.continuous_coe)).clm_apply
      continuous_const
  have hHC : ∀ (t : ℝ≥0) ω, |fderiv ℝ φ (X ω t) n| ≤ C * ‖n‖ := fun t ω => by
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ φ _).le_opNorm n).trans (mul_le_mul_of_nonneg_right (hC1 _) (norm_nonneg _))
  obtain ⟨I, hImem, hL2, hI0, -⟩ := exists_itoIntegral (P := P) hB hm
    (H := fun t ω => fderiv ℝ φ (X ω t) n) hHa hHc hHC T
  refine ⟨I, hImem, hL2, hI0, ?_⟩
  -- the Riemann sums converge in probability both to `I` and to the Itô-formula value
  have hSmem : ∀ k : ℕ, MemLp (fun ω => ∑ i ∈ range (2 ^ k),
      fderiv ℝ φ (X ω ((i : ℝ≥0) * (T / (2 ^ k : ℕ)))) n *
        incr B (fun i : ℕ => (i : ℝ≥0) * (T / (2 ^ k : ℕ))) i ω) 2 P := fun k =>
    memLp_sum_mul (𝓕 := fun i => Filtration.natural B hm ((i : ℝ≥0) * (T / (2 ^ k : ℕ))))
      (fun i => (Filtration.natural B hm).le _) (fun i => hHa _) (fun i ω => hHC _ ω)
      (fun i => (QV.incr_hasLaw hB (monotone_grid T (2 ^ k)) i).memLp
        (memLp_id_gaussianReal 2)) (2 ^ k)
  have h1 : TendstoInMeasure P (fun k : ℕ => fun ω => ∑ i ∈ range (2 ^ k),
      fderiv ℝ φ (X ω ((i : ℝ≥0) * (T / (2 ^ k : ℕ)))) n *
        incr B (fun i : ℕ => (i : ℝ≥0) * (T / (2 ^ k : ℕ))) i ω) atTop I := by
    have := tendstoInMeasure_of_integral_sq (fun k => (hSmem k).sub hImem) hL2
    rw [tendstoInMeasure_iff_measureReal_dist] at this ⊢
    intro ε hε
    refine (this ε hε).congr fun k => ?_
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, Pi.sub_apply, Real.dist_eq, sub_zero]
  have hpow : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (α := ℕ) (by norm_num)
  have h2 := (tendstoInMeasure_ito_formula hB hm hBc hT hb N x₀ c hφ hC1 hC2 hu).comp hpow
  have h2' : TendstoInMeasure P (fun k : ℕ => fun ω => ∑ i ∈ range (2 ^ k),
      fderiv ℝ φ (X ω ((i : ℝ≥0) * (T / (2 ^ k : ℕ)))) n *
        incr B (fun i : ℕ => (i : ℝ≥0) * (T / (2 ^ k : ℕ))) i ω) atTop
      (fun ω => φ (X ω T) - φ (X ω 0) - ∫ u in (0 : ℝ)..T, gen b n φ (X ω u)) := by
    refine h2.congr_left fun k => ae_of_all _ fun ω => ?_
    simp only [Function.comp_apply, NNReal.coe_natCast]
    rfl
  exact tendstoInMeasure_ae_unique h1 h2'

end Ito
end powerlib.Stochastic
