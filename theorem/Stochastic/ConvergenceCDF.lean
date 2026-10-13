import dependencies.Mathlib
import theorem.Attributes
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.CDF
import Mathlib.Topology.Algebra.Module.Cardinality

/-! # Convergence in distribution on `ℝ` ⇔ convergence of distribution functions

Source: work-sync `theory/T-convergence-stochastic.md` §1.4 (convergence in distribution:
`F_n(x) → F(x)` at every continuity point `x` of `F`, equivalently `∫ f dμ_n → ∫ f dμ` for bounded
continuous `f`).

Foundation (probability), not an engineering result.

Setting: probability measures on `ℝ` with the weak topology (`ProbabilityMeasure ℝ`); the
distribution function is Mathlib's `ProbabilityTheory.cdf`.  A point `x` with `ν {x} = 0` is
exactly a continuity point of `F = cdf ν` (the jump of `F` at `x` is `ν {x}`); the statements use
the measure-zero form.
* `cdf_tendsto_of_tendsto` (forward direction): weak convergence ⇒ `F_n(x) → F(x)` whenever
  `ν {x} = 0` (portmanteau, `frontier (Iic x) = {x}`).
* `tendsto_of_cdf_tendsto` (reverse direction): `F_n(x) → F(x)` at every `x` with `ν {x} = 0`
  ⇒ weak convergence.  Proof: the half-open intervals `(a, b]` with atom-free endpoints form a
  π-system containing arbitrarily small neighbourhoods of every point (atoms of a finite measure
  are countable, so atom-free points are dense), and their masses converge; Mathlib's criterion
  `IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem` concludes.
* `tendsto_iff_cdf_tendsto`: the equivalence.

Skorokhod representation on `ℝ` (`T-convergence-stochastic.md`, stretch item), by the quantile
coupling on `((0, 1), Lebesgue)` (`unifI`):
* `quantile μ u = inf {x | u ≤ F_μ(x)}`; `quantile_le_iff`: `Q(u) ≤ x ↔ u ≤ F(x)` for `u ∈ (0, 1)`
  (right-continuity of `F`); `quantile_monotoneOn`;
* `map_quantile`: `Q_μ(U) ∼ μ` for `U` uniform on `(0, 1)`;
* `tendsto_quantile`, `ae_tendsto_quantile`: `F_n → F` at atom-free points ⇒ `Q_n(u) → Q(u)` at
  every continuity point `u` of `Q`, hence for a.e. `u` (countably many discontinuities);
* `skorokhod_representation`: if `μ_n → μ` weakly, then `Y_n = Q_{μ_n}`, `Y = Q_μ` on `(0, 1)`
  have laws `μ_n`, `μ` and `Y_n → Y` almost surely.
-/

noncomputable section
namespace powerlib.Stochastic.Conv

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

variable {ι : Type*} {l : Filter ι}

/-- Mass of `(a, b]` through the distribution function. -/
@[powerlib_foundation] theorem coe_apply_Ioc (μ : ProbabilityMeasure ℝ) (a b : ℝ) :
    ((μ (Ioc a b) : ℝ≥0) : ℝ) = max (cdf (μ : Measure ℝ) b - cdf (μ : Measure ℝ) a) 0 := by
  have h := (cdf (μ : Measure ℝ)).measure_Ioc a b
  rw [measure_cdf] at h
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn, Measure.real, h, ENNReal.toReal_ofReal']

/-- Atom-free points of a finite measure on `ℝ` are dense. -/
@[powerlib_foundation] theorem dense_atomFree (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Dense {t : ℝ | ν {t} = 0} := by
  have hc := Measure.countable_meas_level_set_pos (μ := ν) (g := id) measurable_id
  have h := hc.dense_compl ℝ
  convert h using 1
  ext t
  simp [pos_iff_ne_zero]

/-- **Forward direction**: weak convergence implies convergence of the distribution functions at
atom-free points (continuity points) of the limit. -/
@[powerlib_foundation] theorem cdf_tendsto_of_tendsto {μs : ι → ProbabilityMeasure ℝ}
    {ν : ProbabilityMeasure ℝ} (h : Tendsto μs l (𝓝 ν)) {x : ℝ} (hx : (ν : Measure ℝ) {x} = 0) :
    Tendsto (fun i => cdf (μs i : Measure ℝ) x) l (𝓝 (cdf (ν : Measure ℝ) x)) := by
  have hfr : (ν : Measure ℝ) (frontier (Iic x)) = 0 := by rw [frontier_Iic]; exact hx
  have := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h hfr
  simp_rw [cdf_eq_real]
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this

/-- **Reverse direction**: convergence of the distribution functions at every atom-free point of
the limit implies weak convergence. -/
@[powerlib_foundation] theorem tendsto_of_cdf_tendsto [l.IsCountablyGenerated]
    {μs : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (h : ∀ x, (ν : Measure ℝ) {x} = 0 →
      Tendsto (fun i => cdf (μs i : Measure ℝ) x) l (𝓝 (cdf (ν : Measure ℝ) x))) :
    Tendsto μs l (𝓝 ν) := by
  set S : Set (Set ℝ) :=
    {s | ∃ a b, (ν : Measure ℝ) {a} = 0 ∧ (ν : Measure ℝ) {b} = 0 ∧ s = Ioc a b} with hSdef
  have hS : IsPiSystem S := by
    rintro s ⟨a, b, ha, hb, rfl⟩ t ⟨c, d, hc, hd, rfl⟩ -
    refine ⟨max a c, min b d, ?_, ?_, Ioc_inter_Ioc⟩
    · rcases le_total a c with hac | hac
      · rwa [max_eq_right hac]
      · rwa [max_eq_left hac]
    · rcases le_total b d with hbd | hbd
      · rwa [min_eq_left hbd]
      · rwa [min_eq_right hbd]
  have hmeas : ∀ s ∈ S, MeasurableSet s := by
    rintro s ⟨a, b, -, -, rfl⟩
    exact measurableSet_Ioc
  have hdense := dense_atomFree (ν : Measure ℝ)
  have hnbhd : ∀ u : Set ℝ, IsOpen u → ∀ x ∈ u, ∃ s ∈ S, s ∈ 𝓝 x ∧ s ⊆ u := by
    intro u hu x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu x hx
    obtain ⟨a, ha, hax⟩ := hdense.exists_between (show x - ε < x by linarith)
    obtain ⟨b, hb, hxb⟩ := hdense.exists_between (show x < x + ε by linarith)
    refine ⟨Ioc a b, ⟨a, b, ha, hb, rfl⟩, Ioc_mem_nhds hax.2 hxb.1, ?_⟩
    intro y hy
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2, hax.1, hxb.2]
  have hconv : ∀ s ∈ S, Tendsto (fun i => μs i s) l (𝓝 (ν s)) := by
    rintro s ⟨a, b, ha, hb, rfl⟩
    rw [← NNReal.tendsto_coe]
    simp_rw [coe_apply_Ioc]
    exact (((h b hb).sub (h a ha)).max tendsto_const_nhds)
  exact hS.tendsto_probabilityMeasure_of_tendsto_of_mem hmeas hnbhd hconv

/-- **Convergence in distribution on `ℝ` ⇔ convergence of distribution functions at the
continuity (atom-free) points of the limit.** -/
@[powerlib_foundation] theorem tendsto_iff_cdf_tendsto [l.IsCountablyGenerated]
    {μs : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ} :
    Tendsto μs l (𝓝 ν) ↔ ∀ x, (ν : Measure ℝ) {x} = 0 →
      Tendsto (fun i => cdf (μs i : Measure ℝ) x) l (𝓝 (cdf (ν : Measure ℝ) x)) :=
  ⟨fun h _ hx => cdf_tendsto_of_tendsto h hx, tendsto_of_cdf_tendsto⟩

/-! ## Skorokhod representation on `ℝ` (quantile coupling) -/

/-- **Quantile function** (generalized inverse of the distribution function):
`Q_μ(u) = inf {x | u ≤ F_μ(x)}`. -/
def quantile (μ : Measure ℝ) (u : ℝ) : ℝ := sInf {x | u ≤ cdf μ x}

section Quantile

variable {μ : Measure ℝ} {u : ℝ}

private theorem quantile_set_nonempty (hu1 : u < 1) : {x | u ≤ cdf μ x}.Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_order.1 (tendsto_cdf_atTop (μ := μ))).1 u hu1).exists
  exact ⟨x, hx.le⟩

private theorem quantile_set_bddBelow (hu0 : 0 < u) : BddBelow {x | u ≤ cdf μ x} := by
  obtain ⟨x₀, hx₀⟩ := eventually_atBot.mp ((tendsto_order.1 (tendsto_cdf_atBot (μ := μ))).2 u hu0)
  refine ⟨x₀, fun y hy => ?_⟩
  by_contra h
  exact absurd hy (not_le.mpr (hx₀ y (not_le.mp h).le))

/-- **Galois connection** of the quantile: for `u ∈ (0, 1)`, `Q(u) ≤ x ↔ u ≤ F(x)`. -/
@[powerlib_foundation] theorem quantile_le_iff (hu0 : 0 < u) (hu1 : u < 1) (x : ℝ) :
    quantile μ u ≤ x ↔ u ≤ cdf μ x := by
  have hne := quantile_set_nonempty (μ := μ) hu1
  have hbdd := quantile_set_bddBelow (μ := μ) hu0
  constructor
  · intro h
    refine le_trans ?_ (monotone_cdf μ h)
    -- `Q(u)` belongs to the set, by right-continuity of `F`
    have hcont : ContinuousWithinAt (cdf μ) (Ioi (quantile μ u)) (quantile μ u) :=
      ((cdf μ).right_continuous _).mono Ioi_subset_Ici_self
    refine ge_of_tendsto hcont ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    obtain ⟨s, hs, hsy⟩ := exists_lt_of_csInf_lt hne hy
    exact le_trans hs (monotone_cdf μ hsy.le)
  · intro h
    exact csInf_le hbdd h

/-- The quantile is monotone on `(0, 1)`. -/
@[powerlib_foundation] theorem quantile_monotoneOn : MonotoneOn (quantile μ) (Ioo 0 1) := by
  intro u hu v hv huv
  rw [quantile_le_iff hu.1 hu.2]
  exact huv.trans ((quantile_le_iff hv.1 hv.2 _).mp le_rfl)

end Quantile

/-- The uniform probability on `(0, 1)`. -/
abbrev unifI : Measure ℝ := volume.restrict (Ioo 0 1)

instance : IsProbabilityMeasure unifI := ⟨by simp⟩

/-- The quantile is a.e.-measurable for the uniform law on `(0, 1)`. -/
@[powerlib_foundation] theorem aemeasurable_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    AEMeasurable (quantile μ) unifI :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo quantile_monotoneOn

/-- **The quantile transform has law `μ`**: if `U` is uniform on `(0, 1)`, `Q_μ(U) ∼ μ`. -/
@[powerlib_foundation] theorem map_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    unifI.map (quantile μ) = μ := by
  refine Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_quantile μ) measurableSet_Iic,
    Measure.restrict_apply' measurableSet_Ioo, ← ofReal_cdf]
  have e : quantile μ ⁻¹' Iic x ∩ Ioo 0 1 = Ioo 0 1 ∩ Iic (cdf μ x) := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioo]
    constructor
    · rintro ⟨h, h0, h1⟩
      exact ⟨⟨h0, h1⟩, (quantile_le_iff h0 h1 x).mp h⟩
    · rintro ⟨⟨h0, h1⟩, h⟩
      exact ⟨(quantile_le_iff h0 h1 x).mpr h, h0, h1⟩
  rw [e]
  have h0 := cdf_nonneg μ x
  have h1 := cdf_le_one μ x
  apply le_antisymm
  · calc volume (Ioo 0 1 ∩ Iic (cdf μ x)) ≤ volume (Icc 0 (cdf μ x)) :=
          measure_mono fun y hy => ⟨hy.1.1.le, hy.2⟩
      _ = ENNReal.ofReal (cdf μ x) := by rw [Real.volume_Icc, sub_zero]
  · rcases h1.lt_or_eq with h1 | h1
    · calc ENNReal.ofReal (cdf μ x) = volume (Ioo 0 (cdf μ x)) := by rw [Real.volume_Ioo, sub_zero]
        _ ≤ volume (Ioo 0 1 ∩ Iic (cdf μ x)) :=
            measure_mono fun y hy => ⟨⟨hy.1, hy.2.trans h1⟩, hy.2.le⟩
    · calc ENNReal.ofReal (cdf μ x) = volume (Ioo (0 : ℝ) 1) := by rw [Real.volume_Ioo, h1]; simp
        _ ≤ volume (Ioo 0 1 ∩ Iic (cdf μ x)) :=
            measure_mono fun y hy => ⟨hy, by rw [h1]; exact hy.2.le⟩

/-- **Quantiles converge at continuity points.**  If `F_n(x) → F(x)` at every atom-free point `x`
of the finite measure `μ`, then `Q_n(u) → Q(u)` at every `u ∈ (0, 1)` where `Q = Q_μ` is continuous
(relative to `(0, 1)`). -/
@[powerlib_foundation] theorem tendsto_quantile {μs : ℕ → Measure ℝ} {μ : Measure ℝ}
    [IsFiniteMeasure μ]
    (hF : ∀ x, μ {x} = 0 → Tendsto (fun n => cdf (μs n) x) atTop (𝓝 (cdf μ x)))
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hc : ContinuousWithinAt (quantile μ) (Ioo 0 1) u) :
    Tendsto (fun n => quantile (μs n) u) atTop (𝓝 (quantile μ u)) := by
  have hdense := dense_atomFree μ
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨x, hx, hax, hxq⟩ := hdense.exists_between ha
    have hFx : cdf μ x < u := by
      by_contra h
      exact absurd ((quantile_le_iff hu.1 hu.2 x).mpr (not_lt.mp h)) (not_le.mpr hxq)
    filter_upwards [(tendsto_order.1 (hF x hx)).2 u hFx] with n hn
    have : ¬ quantile (μs n) u ≤ x := fun h =>
      absurd ((quantile_le_iff hu.1 hu.2 x).mp h) (not_le.mpr hn)
    exact hax.trans (not_le.mp this)
  · intro b hb
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.mp hc (b - quantile μ u) (by linarith)
    set v := min (u + δ / 2) ((u + 1) / 2) with hvdef
    have huv : u < v := lt_min (by linarith) (by linarith [hu.2])
    have hv : v ∈ Ioo (0 : ℝ) 1 :=
      ⟨hu.1.trans huv, (min_le_right _ _).trans_lt (by linarith [hu.2])⟩
    have hdist : dist v u < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith [min_le_left (u + δ / 2) ((u + 1) / 2)]
    have hQv : quantile μ v < b := by
      have := hδc hv hdist
      rw [Real.dist_eq, abs_lt] at this
      linarith [this.2]
    obtain ⟨x, hx, hvx, hxb⟩ := hdense.exists_between hQv
    have hFx : u < cdf μ x := huv.trans_le ((quantile_le_iff hv.1 hv.2 x).mp hvx.le)
    filter_upwards [(tendsto_order.1 (hF x hx)).1 u hFx] with n hn
    exact ((quantile_le_iff hu.1 hu.2 x).mpr hn.le).trans_lt hxb

/-- **Almost-sure convergence of the quantile coupling**: under the hypothesis of
`tendsto_quantile`, `Q_n(U) → Q(U)` for Lebesgue-a.e. `U ∈ (0, 1)` (the discontinuities of the
monotone `Q` on `(0, 1)` are countable). -/
@[powerlib_foundation] theorem ae_tendsto_quantile {μs : ℕ → Measure ℝ} {μ : Measure ℝ}
    [IsFiniteMeasure μ]
    (hF : ∀ x, μ {x} = 0 → Tendsto (fun n => cdf (μs n) x) atTop (𝓝 (cdf μ x))) :
    ∀ᵐ u ∂unifI, Tendsto (fun n => quantile (μs n) u) atTop (𝓝 (quantile μ u)) := by
  have hcount := (quantile_monotoneOn (μ := μ)).countable_not_continuousWithinAt
  have hnull := hcount.measure_zero (volume : Measure ℝ)
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with u hu hu01
  exact tendsto_quantile hF hu01 (by by_contra h; exact hu ⟨hu01, h⟩)

/-- **Skorokhod representation on `ℝ`** (quantile coupling).  If `μ_n → μ` weakly (convergence in
distribution), then on the probability space `((0, 1), Lebesgue)` the random variables
`Y_n = Q_{μ_n}` and `Y = Q_μ` have laws `μ_n` and `μ`, and `Y_n → Y` almost surely. -/
@[powerlib_foundation] theorem skorokhod_representation {μs : ℕ → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} (h : Tendsto μs atTop (𝓝 μ)) :
    (∀ n, AEMeasurable (quantile (μs n : Measure ℝ)) unifI ∧
        unifI.map (quantile (μs n : Measure ℝ)) = μs n) ∧
      AEMeasurable (quantile (μ : Measure ℝ)) unifI ∧
      unifI.map (quantile (μ : Measure ℝ)) = μ ∧
      ∀ᵐ u ∂unifI, Tendsto (fun n => quantile (μs n : Measure ℝ) u) atTop
        (𝓝 (quantile (μ : Measure ℝ) u)) :=
  ⟨fun _ => ⟨aemeasurable_quantile _, map_quantile _⟩, aemeasurable_quantile _, map_quantile _,
    ae_tendsto_quantile fun _ hx => cdf_tendsto_of_tendsto h hx⟩

end powerlib.Stochastic.Conv
