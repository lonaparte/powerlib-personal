import theorem.TMIO.Relation

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

A record whose samples carry no nonzero current has zero denominator; Lean's convention
`x / 0 = 0` then returns `0`, and no theorem below concludes anything about such records. -/

namespace powerlib.TMIO.Analysis

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
@[powerlib_foundation] theorem generate_estimateEdge :
    ⇑(generate (estimateEdge (K := K))) = Set.image estimate :=
  generate_preimage estimate

/-- The analysis is the composite of the statistics and the fit edges, and its generated forward
map is the composite of their generated forward maps. -/
@[powerlib_foundation] theorem generate_estimateEdge_comp :
    ⇑(generate (estimateEdge (K := K))) = Set.image fit ∘ Set.image stats := by
  have h : estimateEdge (K := K) = statsEdge.comp fitEdge := rfl
  rw [h, generate_comp, statsEdge, fitEdge, generate_preimage, generate_preimage]

/-- Merging two records adds their statistics. -/
@[simp, powerlib_foundation] theorem stats_append (d₁ d₂ : Record K) :
    stats (d₁ ++ d₂) = stats d₁ + stats d₂ := by
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
@[powerlib_foundation] theorem distributedEdge_eq_centralEdge :
    distributedEdge (K := K) = centralEdge := by
  ext B p
  simp [distributedEdge, centralEdge, estimateEdge, fitEdge, estimate]

/-- Hence the distributed pipeline, generated stage by stage, computes the central estimates. -/
@[powerlib_foundation] theorem generate_distributedEdge :
    Set.image fit ∘ Set.image (fun s : (K × K) × (K × K) => s.1 + s.2) ∘
        Set.image (Prod.map stats stats) =
      Set.image estimate ∘ Set.image fun p : Record K × Record K => p.1 ++ p.2 := by
  have hd : ⇑(generate (distributedEdge (K := K))) = Set.image fit ∘
      Set.image (fun s : (K × K) × (K × K) => s.1 + s.2) ∘ Set.image (Prod.map stats stats) := by
    rw [distributedEdge, generate_comp, generate_comp, fitEdge, generate_preimage,
      generate_preimage, generate_preimage]
    rfl
  have hc : ⇑(generate (centralEdge (K := K))) =
      Set.image estimate ∘ Set.image fun p : Record K × Record K => p.1 ++ p.2 := by
    rw [centralEdge, generate_comp, generate_estimateEdge, generate_preimage]
  rw [← hd, ← hc, distributedEdge_eq_centralEdge]

/-- On a noiseless record `vₖ = R * iₖ` with some nonzero current, the fit returns `R`. -/
@[powerlib_foundation] theorem estimate_eq_of_exact {R : K} (d : Record K)
    (hd : ∀ s ∈ d, s.voltage = R * s.current) (h : (stats d).2 ≠ 0) : estimate d = R := by
  have h1 : (stats d).1 = R * (stats d).2 := by
    change (d.map fun s => s.voltage * s.current).sum = R * (d.map fun s => s.current ^ 2).sum
    rw [← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun s hs => ?_
    rw [hd s hs]
    ring
  rw [estimate, fit, h1, mul_div_cancel_right₀ R h]

/-- A concrete exact evaluation: samples `(2 V, 1 A)` and `(4 V, 2 A)` fit `2 Ω`. -/
@[powerlib_foundation] theorem estimate_example :
    estimate ([⟨2, 1⟩, ⟨4, 2⟩] : Record ℚ) = 2 := by
  norm_num [estimate, fit, stats]

end powerlib.TMIO.Analysis
