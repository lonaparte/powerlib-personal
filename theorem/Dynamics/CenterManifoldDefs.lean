import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import theorem.Dynamics.State

/-! # Centre manifolds: graphs over the centre subspace and their order of tangency (foundation)

The notions shared by the centre-manifold modules: a projection `P` commuting with the linear
part `A`, a graph map `h` over `range P` with values in `range (1 − P)`, its graph, the reduced
field `g(u) = PAu + Pf(u + h(u))`, the invariance defect of a candidate graph and its static
invariance equation, linear coordinates of `range P`, and the order predicates
`F(u) = O(‖u‖^q)`, `F(u) = o(‖u‖^q)` as `u → 0` in `range P`.

Scope.
* A real normed space `E` (the applications take `E = State n = ℝⁿ`), a continuous linear map
  `A`, a nonlinearity `f : E → E`; the full field is `x ↦ A x + f x` (`fullField`). A continuous
  linear projection `P` commuting with `A` (`IsCommutingProjection`: `P² = P`, `AP = PA`). A map
  `h : E → E` is read through `P`: it is a graph map (`IsGraphMap`) when `h (P x) = h x`,
  `P (h x) = 0` and `h 0 = 0`, i.e. a map `range P → range (1 − P)` vanishing at `0`; its graph
  is `{x | x = P x + h x}` (`graph`). Lipschitz bounds and smoothness are theorem hypotheses.
* No notion here quantifies over time (semantic rule T). Local invariance of the graph under the
  flow is a statement about solutions and is therefore a theorem hypothesis, in the form (for a
  radius `ρ > 0`, `E = State n`)
  `∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ (fullField A f) t₀ t₁ →
    φ t₀ ∈ graph P h → (∀ t ∈ Icc t₀ t₁, ‖φ t‖ < ρ) → ∀ t ∈ Icc t₀ t₁, φ t ∈ graph P h`:
  solutions starting on the graph stay on it as long as they stay in the ball of radius `ρ`.
  The reduction theorems consuming it are in `theorem/Dynamics/CenterReduction.lean`; its
  static counterpart for differentiable graphs is the invariance equation `IsInvariantGraph`.
* Everything is generic; nothing here describes a physical system (foundation).

Source: Carr, *Applications of Centre Manifold Theory* (1981), §2.1–§2.4 (Theorems 1–3:
existence, reduction, approximation; the invariance defect `(Mφ)(u)` of Theorem 3); Kelley,
"The stable, center-stable, center, center-unstable and unstable manifolds" (1967);
Vanderbauwhede, "Centre manifolds, normal forms and elementary bifurcations" (1989), §2;
Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §5.1.

Results.
* Definitions: `fullField`, `IsCommutingProjection`, `IsGraphMap`, `graph`, `reducedField`
  (`g(u) = PAu + Pf(u + h u)`), `normalField` (`(1 − P)A h(u) + (1 − P) f(u + h u)`, the
  field normal to `range P` along the graph), `invarianceDefect` (`Dφ(u) g(u) − normalField`),
  `IsInvariantGraph` (the defect vanishes and `h` is differentiable near `0` in `range P`),
  `IsChart` / `chartField` (linear coordinates `ι : F → E`, `π : E → F` of `range P`,
  `π ι = 1`, `ι π = P`, and the reduced field read in them), `IsOrder`, `IsLittleOrder`
  (`O(‖u‖^q)`, `o(‖u‖^q)` on `range P`), `HasQuadraticPart` (`h(u) = H(u, u) + O(‖u‖³)`).
* Algebra of the splitting: `IsCommutingProjection.proj_compl`, `compl_proj`,
  `proj_apply_compl`; `IsGraphMap.lift_mem_graph`, `proj_lift`, `eq_lift_of_mem_graph`,
  `norm_lift_le` (`‖u + h u‖ ≤ (1 + K)‖u‖` for a `K`-Lipschitz `h`), `reducedField_zero`;
  `fullField_lift`: on the graph the full field splits as `g(u) + normalField(u)`.
* Coordinates: `IsChart.idem`, `IsChart.proj_ι`, `IsChart.π_proj`, `IsChart.ι_chartField`
  (`ι (chartField y) = g(ι y)`), `IsChart.π_fullField_of_mem_graph` (on the graph, `π` of the
  full field is the chart field at `π x`).
* Orders: `isOrder_natCast_iff`, `isLittleOrder_natCast_iff` (natural exponents),
  `hasQuadraticPart_iff`,
  `IsOrder.isLittleOrder` (`O(‖u‖^q')` is `o(‖u‖^q)` for `q < q'`).
-/

noncomputable section
namespace powerlib.Dynamics.CenterManifold

open Filter Topology Asymptotics

section Defs

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The full field `x ↦ A x + f x`. -/
def fullField (A : E →L[ℝ] E) (f : E → E) (x : E) : E := A x + f x

/-- A projection commuting with the linear part: `P² = P`, `AP = PA`. -/
structure IsCommutingProjection (A P : E →L[ℝ] E) : Prop where
  /-- `P` is idempotent. -/
  idem : ∀ x, P (P x) = P x
  /-- `P` commutes with `A`. -/
  comm : ∀ x, A (P x) = P (A x)

/-- A graph map over `range P`: `h` reads `x` through `P x`, takes values in `range (1 − P)`
and vanishes at `0`. -/
structure IsGraphMap (P : E →L[ℝ] E) (h : E → E) : Prop where
  /-- `h` depends on `P x` only. -/
  comp_proj : ∀ x, h (P x) = h x
  /-- `h` takes values in `range (1 − P) = ker P`. -/
  proj_apply : ∀ x, P (h x) = 0
  /-- `h 0 = 0`. -/
  map_zero : h 0 = 0

/-- The graph `{u + h u | u ∈ range P}` of a graph map, as the set `{x | x = P x + h x}`. -/
def graph (P : E →L[ℝ] E) (h : E → E) : Set E := {x | x = P x + h x}

/-- The reduced field `g(u) = PAu + Pf(u + h u)` on `range P`. -/
def reducedField (A P : E →L[ℝ] E) (f h : E → E) (u : E) : E := P (A u) + P (f (u + h u))

/-- The component of the full field normal to `range P` at the graph point `u + h u`:
`(1 − P)A h(u) + (1 − P) f(u + h u)`. -/
def normalField (A P : E →L[ℝ] E) (f h : E → E) (u : E) : E :=
  (1 - P) (A (h u)) + (1 - P) (f (u + h u))

/-- Carr's invariance defect of a candidate graph `φ`:
`Dφ(u) (PAu + Pf(u + φ u)) − ((1 − P)A φ(u) + (1 − P) f(u + φ u))`. -/
def invarianceDefect (A P : E →L[ℝ] E) (f φ : E → E) (u : E) : E :=
  fderiv ℝ φ u (reducedField A P f φ u) - normalField A P f φ u

/-- The graph of `h` satisfies the invariance equation near `0`: for `u ∈ range P` near `0`, `h`
is differentiable at `u` and its invariance defect vanishes. -/
def IsInvariantGraph (A P : E →L[ℝ] E) (f h : E → E) : Prop :=
  ∀ᶠ u in 𝓝[Set.range P] 0, DifferentiableAt ℝ h u ∧ invarianceDefect A P f h u = 0

/-- Linear coordinates of `range P`: `ι : F → E`, `π : E → F` with `π ι = 1` and `ι π = P`. -/
structure IsChart (P : E →L[ℝ] E) (ι : F →L[ℝ] E) (π : E →L[ℝ] F) : Prop where
  /-- `π` is a left inverse of `ι`. -/
  left_inv : ∀ y, π (ι y) = y
  /-- `ι π = P`. -/
  ι_π : ∀ x, ι (π x) = P x

/-- The reduced field read in coordinates: `y ↦ π (A (ι y) + f (ι y + h (ι y)))`. -/
def chartField (A : E →L[ℝ] E) (f h : E → E) (ι : F →L[ℝ] E) (π : E →L[ℝ] F) (y : F) : F :=
  π (A (ι y) + f (ι y + h (ι y)))

section OrderDefs

variable {V : Type*} [NormedAddCommGroup V]

/-- `G(u) = O(‖u‖^q)` as `u → 0` in `range P`. -/
def IsOrder (P : E →L[ℝ] E) (G : E → V) (q : ℝ) : Prop :=
  G =O[𝓝[Set.range P] 0] fun u => ‖u‖ ^ q

/-- `G(u) = o(‖u‖^q)` as `u → 0` in `range P`. -/
def IsLittleOrder (P : E →L[ℝ] E) (G : E → V) (q : ℝ) : Prop :=
  G =o[𝓝[Set.range P] 0] fun u => ‖u‖ ^ q

end OrderDefs

/-- `h(u) = H(u, u) + O(‖u‖³)` on `range P`, for a bilinear map `H`. -/
def HasQuadraticPart (P : E →L[ℝ] E) (h : E → E) (H : E →L[ℝ] E →L[ℝ] E) : Prop :=
  IsOrder P (fun u => h u - H u u) 3

end Defs

/-! ## The splitting along the graph -/

section Splitting

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {A P : E →L[ℝ] E} {f h : E → E}

@[tmio T, powerlib_foundation] theorem compl_apply (P : E →L[ℝ] E) (x : E) :
    (1 - P) x = x - P x := by
  simp

@[tmio T, powerlib_foundation] theorem IsCommutingProjection.proj_compl
    (hP : IsCommutingProjection A P) (x : E) : P ((1 - P) x) = 0 := by
  simp [hP.idem]

@[tmio T, powerlib_foundation] theorem IsCommutingProjection.compl_proj
    (hP : IsCommutingProjection A P) (x : E) : (1 - P) (P x) = 0 := by
  simp [hP.idem]

/-- `PA(1 − P) = 0`. -/
@[tmio T, powerlib_foundation] theorem IsCommutingProjection.proj_apply_compl
    (hP : IsCommutingProjection A P) (x : E) : P (A ((1 - P) x)) = 0 := by
  rw [← hP.comm, hP.proj_compl, map_zero]

@[tmio T, powerlib_foundation] theorem IsGraphMap.proj_lift (hh : IsGraphMap P h)
    {u : E} (hu : P u = u) : P (u + h u) = u := by
  simp [hh.proj_apply, hu]

@[tmio T, powerlib_foundation] theorem IsGraphMap.lift_mem_graph (hh : IsGraphMap P h)
    {u : E} (hu : P u = u) : u + h u ∈ graph P h := by
  show u + h u = P (u + h u) + h (u + h u)
  rw [hh.proj_lift hu, ← hh.comp_proj (u + h u), hh.proj_lift hu]

@[tmio T, powerlib_foundation] theorem IsGraphMap.eq_lift_of_mem_graph (hh : IsGraphMap P h)
    {x : E} (hx : x ∈ graph P h) : x = P x + h (P x) := by
  rw [hh.comp_proj]; exact hx

@[tmio T, powerlib_foundation] theorem IsGraphMap.zero_mem_graph (hh : IsGraphMap P h) :
    (0 : E) ∈ graph P h := by
  simp [graph, hh.map_zero]

/-- A `K`-Lipschitz graph map: `‖u + h u‖ ≤ (1 + K) ‖u‖`. -/
@[tmio T, powerlib_foundation] theorem IsGraphMap.norm_lift_le (hh : IsGraphMap P h)
    {K : NNReal} (hK : LipschitzWith K h) (u : E) : ‖u + h u‖ ≤ (1 + K) * ‖u‖ := by
  have h1 : ‖h u‖ ≤ K * ‖u‖ := by
    simpa [hh.map_zero] using hK.norm_sub_le u 0
  calc ‖u + h u‖ ≤ ‖u‖ + ‖h u‖ := norm_add_le _ _
    _ ≤ (1 + K) * ‖u‖ := by nlinarith

@[tmio T, powerlib_foundation] theorem reducedField_zero (hh : IsGraphMap P h) (hf : f 0 = 0) :
    reducedField A P f h 0 = 0 := by
  simp [reducedField, hh.map_zero, hf]

/-- On the graph the full field splits into the reduced field and the normal field:
`A x + f x = g(u) + normalField(u)` at `x = u + h u`, `u ∈ range P`. -/
@[tmio T, powerlib_foundation] theorem fullField_lift (hP : IsCommutingProjection A P)
    (hh : IsGraphMap P h) {u : E} (hu : P u = u) :
    fullField A f (u + h u) = reducedField A P f h u + normalField A P f h u := by
  have hAu : P (A u) = A u := by
    conv_rhs => rw [← hu]
    exact (hP.comm u).symm
  have hAh : P (A (h u)) = 0 := by rw [← hP.comm, hh.proj_apply, map_zero]
  simp only [fullField, reducedField, normalField, map_add, compl_apply, hAu, hAh]
  abel

end Splitting

/-! ## Coordinates of the centre subspace -/

section Chart

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {A P : E →L[ℝ] E} {f h : E → E} {ι : F →L[ℝ] E} {π : E →L[ℝ] F}

@[tmio T, powerlib_foundation] theorem IsChart.idem (hc : IsChart P ι π) (x : E) :
    P (P x) = P x := by
  rw [← hc.ι_π x, ← hc.ι_π (ι (π x)), hc.left_inv]

@[tmio T, powerlib_foundation] theorem IsChart.proj_ι (hc : IsChart P ι π) (y : F) :
    P (ι y) = ι y := by
  rw [← hc.ι_π, hc.left_inv]

@[tmio T, powerlib_foundation] theorem IsChart.π_proj (hc : IsChart P ι π) (x : E) :
    π (P x) = π x := by
  rw [← hc.ι_π, hc.left_inv]

/-- The chart field is the reduced field read in coordinates: `ι (chartField y) = g(ι y)`. -/
@[tmio T, powerlib_foundation] theorem IsChart.ι_chartField (hc : IsChart P ι π) (y : F) :
    ι (chartField A f h ι π y) = reducedField A P f h (ι y) := by
  simp only [chartField, reducedField, hc.ι_π, map_add]

/-- On the graph, `π` of the full field is the chart field at `π x`. -/
@[tmio T, powerlib_foundation] theorem IsChart.π_fullField_of_mem_graph
    (hP : IsCommutingProjection A P) (hh : IsGraphMap P h) (hc : IsChart P ι π) {x : E}
    (hx : x ∈ graph P h) : π (fullField A f x) = chartField A f h ι π (π x) := by
  have hx' : x = P x + h (P x) := hh.eq_lift_of_mem_graph hx
  have hu : P (P x) = P x := hP.idem x
  have hsplit := fullField_lift (f := f) hP hh hu
  rw [← hx'] at hsplit
  have hnorm : π (normalField A P f h (P x)) = 0 := by
    rw [← hc.π_proj, normalField, map_add, hP.proj_compl, hP.proj_compl, add_zero, map_zero]
  rw [hsplit, map_add, hnorm, add_zero, reducedField, map_add, hc.π_proj, hc.π_proj,
    chartField, hc.ι_π, map_add]

end Chart

/-! ## Orders on the centre subspace -/

section Order

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
  {P : E →L[ℝ] E}

@[tmio T, powerlib_foundation] theorem isOrder_natCast_iff (G : E → V) (k : ℕ) :
    IsOrder P G k ↔ G =O[𝓝[Set.range P] 0] fun u => ‖u‖ ^ k := by
  simp only [IsOrder, Real.rpow_natCast]

@[tmio T, powerlib_foundation] theorem isLittleOrder_natCast_iff (G : E → V) (k : ℕ) :
    IsLittleOrder P G k ↔ G =o[𝓝[Set.range P] 0] fun u => ‖u‖ ^ k := by
  simp only [IsLittleOrder, Real.rpow_natCast]

@[tmio T, powerlib_foundation] theorem hasQuadraticPart_iff {h : E → E}
    {H : E →L[ℝ] E →L[ℝ] E} :
    HasQuadraticPart P h H ↔ (fun u => h u - H u u) =O[𝓝[Set.range P] 0] fun u => ‖u‖ ^ 3 := by
  rw [HasQuadraticPart, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, isOrder_natCast_iff]

/-- `O(‖u‖^q')` is `o(‖u‖^q)` for `q < q'`. -/
@[tmio T, powerlib_foundation] theorem IsOrder.isLittleOrder {G : E → V} {q q' : ℝ}
    (hG : IsOrder P G q') (hq : q < q') (hq0 : 0 ≤ q) : IsLittleOrder P G q := by
  refine hG.trans_isLittleO ?_
  have hlim : Tendsto (fun u : E => ‖u‖) (𝓝[Set.range P] 0) (𝓝[≥] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (continuous_norm.tendsto' 0 0 norm_zero).mono_left nhdsWithin_le_nhds
    · exact Eventually.of_forall fun u => norm_nonneg u
  have hpow : (fun x : ℝ => x ^ q') =o[𝓝[≥] 0] fun x => x ^ q := by
    refine (isLittleO_iff.mpr fun c hc => ?_)
    have hd : 0 < q' - q := sub_pos.mpr hq
    have ht : Tendsto (fun x : ℝ => x ^ (q' - q)) (𝓝[≥] 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 (q' - q) (Or.inr hd.le)).tendsto
      rw [Real.zero_rpow hd.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    filter_upwards [ht.eventually (gt_mem_nhds hc), self_mem_nhdsWithin] with x hx hx0
    have hx0' : (0 : ℝ) ≤ x := hx0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0' _),
      abs_of_nonneg (Real.rpow_nonneg hx0' _)]
    have hsplit : x ^ q' = x ^ (q' - q) * x ^ q := by
      rcases hx0'.eq_or_lt with h0 | hpos
      · subst h0
        rw [Real.zero_rpow (by linarith), Real.zero_rpow hd.ne', zero_mul]
      · rw [← Real.rpow_add hpos, sub_add_cancel]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hx.le (Real.rpow_nonneg hx0' _)
  exact hpow.comp_tendsto hlim

end Order

end powerlib.Dynamics.CenterManifold
