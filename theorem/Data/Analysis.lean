import theorem.TMIO.Relation
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Field.Basic

/-! # A data analysis instance (v0.3 §7)

A DC test record is a finite list of samples `(voltage, current)` with entries in a field `K`:
exact rationals for computation, reals when the record is attached to the RL instance. The
analysis is the least-squares resistance of `v = R * i` through the origin. It enters TMIO as an
ordinary edge built from one deterministic map (`preimage`); its forward map, the direct image,
is generated.

The fit factors through the sufficient statistics `(Σ vₖ iₖ, Σ iₖ²)`. Two areas may therefore
exchange statistics instead of records: the statistics of merged records are the sums of the
statistics, so the distributed and the central pipelines have the same semantic map and hence
the same generated forward map.

Scope.
* Records over an arbitrary field `K`; the analysis is the least-squares fit through the origin,
  with no noise model. No circuit is modelled here; `theorem/Circuits/RLMeasurement.lean`
  attaches real records to the RL instance.
* A record whose samples carry no nonzero current has zero denominator; Lean's convention
  `x / 0 = 0` then returns `0`, and no theorem below concludes anything about such records.

Source: TMIO v0.3 §7 (data analysis as a deterministic edge); the constructor `preimage` and its
generated direct image (`theorem/TMIO/Relation.lean`).

Results.
* Records and the analysis: `Sample`, `Record`, `stats`, `fit`, `estimate`.
* Edges: `estimateEdge`, `statsEdge`, `fitEdge`; `generate_estimateEdge` (the direct image),
  `generate_estimateEdge_comp` (the analysis is the composite of the statistics and fit edges).
* Distribution: `stats_append` (merging records adds their statistics), `distributedEdge`,
  `centralEdge`, `distributedEdge_eq_centralEdge` (the same semantic map),
  `generate_distributedEdge` (the distributed pipeline computes the central estimates).
* Evaluation: `estimate_eq_of_exact` (a noiseless record with some nonzero current fits `R`).
-/

namespace powerlib.Data.Analysis

open powerlib.TMIO

/-- One DC test sample: terminal voltage and branch current. -/
structure Sample (K : Type*) where
  voltage : K
  current : K

/-- A test record. -/
abbrev Record (K : Type*) := List (Sample K)

variable {K : Type*} [Field K]

/-- Sufficient statistics of the least-squares fit: `(Σ vₖ iₖ, Σ iₖ²)`. -/
def stats (d : Record K) : K × K :=
  ((d.map fun s => s.voltage * s.current).sum, (d.map fun s => s.current ^ 2).sum)

/-- The fitted resistance from the statistics. -/
def fit (s : K × K) : K := s.1 / s.2

/-- The data analysis: the least-squares resistance of a record. -/
def estimate (d : Record K) : K := fit (stats d)

/-- The analysis edge, supplied by its deterministic map alone. -/
def estimateEdge : sInfHom (Set K) (Set (Record K)) := preimage estimate

/-- The statistics edge. -/
def statsEdge : sInfHom (Set (K × K)) (Set (Record K)) := preimage stats

/-- The fit edge. -/
def fitEdge : sInfHom (Set K) (Set (K × K)) := preimage fit

/-- The generated forward map of the analysis is its direct image. -/
@[tmio T, powerlib_foundation] theorem generate_estimateEdge :
    connection% (⇑(generate (estimateEdge (K := K))) = Set.image estimate) := show ⇑(generate (estimateEdge (K := K))) = Set.image estimate from
  generate_preimage estimate

/-- The analysis is the composite of the statistics and the fit edges, and its generated forward
map is the composite of their generated forward maps. -/
@[tmio T, powerlib_foundation] theorem generate_estimateEdge_comp :
    connection% (⇑(generate (estimateEdge (K := K))) = Set.image fit ∘ Set.image stats) := by
  change ⇑(generate (estimateEdge (K := K))) = Set.image fit ∘ Set.image stats
  have h : estimateEdge (K := K) = statsEdge.comp fitEdge := rfl
  rw [h, generate_comp, statsEdge, fitEdge, generate_preimage, generate_preimage]

/-- Merging two records adds their statistics. -/
@[tmio T, simp, powerlib_foundation] theorem stats_append (d₁ d₂ : Record K) :
    connection% (d₁ ++ d₂ ∈ statsEdge {stats d₁ + stats d₂}) := by
  change stats (d₁ ++ d₂) = stats d₁ + stats d₂
  simp [stats]

/-- Distributed pipeline: each area computes its statistics, the sums are transmitted, and the
receiver fits. -/
def distributedEdge : sInfHom (Set K) (Set (Record K × Record K)) :=
  (preimage (Prod.map stats stats)).comp
    ((preimage fun s : (K × K) × (K × K) => s.1 + s.2).comp fitEdge)

/-- Central pipeline: the records are merged and analysed. -/
def centralEdge : sInfHom (Set K) (Set (Record K × Record K)) :=
  (preimage fun p : Record K × Record K => p.1 ++ p.2).comp estimateEdge

/-- The two pipelines have the same semantic map; the proof is the statistic identity. -/
@[tmio T, powerlib_foundation] theorem distributedEdge_eq_centralEdge :
    connection% (distributedEdge (K := K) = centralEdge) := by
  change distributedEdge (K := K) = centralEdge
  ext B p
  simp [distributedEdge, centralEdge, estimateEdge, fitEdge, estimate,
    connection_proof% stats_append]

/-- Hence the distributed pipeline, generated stage by stage, computes the central estimates. -/
@[tmio T, powerlib_foundation] theorem generate_distributedEdge :
    connection% (⇑(generate (distributedEdge (K := K))) = ⇑(generate centralEdge)) := by
  unfold Statement
  rw [distributedEdge_eq_centralEdge]

/-- On a noiseless record `vₖ = R * iₖ` with some nonzero current, the fit returns `R`. -/
@[tmio T, powerlib_foundation] theorem estimate_eq_of_exact {R : K} (d : Record K)
    (hd : ∀ s ∈ d, s.voltage = R * s.current) (h : (stats d).2 ≠ 0) : connection% (d ∈ estimateEdge {R}) := by
  change estimate d = R
  have h1 : (stats d).1 = R * (stats d).2 := by
    change (d.map fun s => s.voltage * s.current).sum = R * (d.map fun s => s.current ^ 2).sum
    rw [← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun s hs => ?_
    rw [hd s hs, pow_two, mul_assoc]
  rw [estimate, fit, h1, mul_div_cancel_right₀ R h]

end powerlib.Data.Analysis
