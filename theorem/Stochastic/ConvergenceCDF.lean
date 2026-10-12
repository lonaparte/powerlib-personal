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

end powerlib.Stochastic.Conv
