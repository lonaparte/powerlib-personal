import theorem.Dynamics.LipschitzFlow
import theorem.Dynamics.State

/-! # Basins of attraction are open and invariant

The region of attraction of the flow semantics (`Flow.regionOfAttraction`,
`theorem/Flow/Defs.lean`) read through the forward flow of a globally Lipschitz field
(`theorem/Dynamics/LipschitzFlow.lean`, forward flow `φ_t`, `t ∈ ℝ≥0`).

Scope.
* Basin. For a globally Lipschitz field on `State n` every state starts a unique forward
  solution, so the region of attraction of `x*` is the basin of the forward flow,
  `𝓑(x*) = {x | φ_t x → x* as t → ∞}`.
* Generic statements about an arbitrary globally Lipschitz field on `State n`; no model family.

Source: work-sync theory/T-attractors-basins.md §1.2 (`𝓑(A)`), and its premise "basin of
attraction 是开集" (proved here for asymptotically stable equilibria of Lipschitz fields).

Results.
* `regionOfAttraction_eq_setOf_tendsto`: the region of attraction is
  `{x | Tendsto (fun t : ℝ≥0 => lipschitzFlow hf t x) atTop (𝓝 xs)}`.
* `basin_isInvariant`: `φ_s(𝓑) ⊆ 𝓑` for every `s ≥ 0` (Mathlib `IsInvariant`).
* `basin_isOpen`: if some ball around `x*` lies in the basin (local attraction), the basin is
  open; the proof uses only the continuity of `φ_T` (continuous dependence on initial data).
* `basin_isOpen_of_localAsymptoticStable`: local asymptotic stability (LeanForControl
  `LocalAsymptoticStable`) of `x*` gives local attraction, so its basin is open.
-/

noncomputable section
namespace powerlib.Dynamics.LaSalle

open Set Filter Topology NNReal

variable {n : ℕ} {f : State n → State n} {K : ℝ≥0}

/-- For a globally Lipschitz field the region of attraction of `x*` is the basin of the forward
flow, `{x | φ_t x → x*}`: every forward solution from `x` is `t ↦ φ_t x`. -/
@[tmio T, powerlib_foundation] theorem regionOfAttraction_eq_setOf_tendsto
    (hf : LipschitzWith K f) (xs : State n) :
    Flow.regionOfAttraction f xs =
      {x | Tendsto (fun t : ℝ≥0 => lipschitzFlow hf t x) atTop (𝓝 xs)} := by
  ext x
  refine ⟨fun h => ?_, fun h => ⟨⟨_, forwardSolution_zero hf x, lipschitzFlow_solution hf x⟩,
    fun φ hφ0 hφ => ?_⟩⟩
  · exact (h.2 _ (forwardSolution_zero hf x) (lipschitzFlow_solution hf x)).comp
      (NNReal.tendsto_coe_atTop.2 tendsto_id)
  · refine (h.comp tendsto_real_toNNReal_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [Function.comp_apply, ← lipschitzFlow_unique hf hφ0 hφ, Real.coe_toNNReal t ht]

/-- The region of attraction of `x*` is invariant under the forward flow. -/
@[tmio T, powerlib_foundation] theorem basin_isInvariant (hf : LipschitzWith K f) (xs : State n) :
    IsInvariant (lipschitzFlow hf) (Flow.regionOfAttraction f xs) := by
  rw [regionOfAttraction_eq_setOf_tendsto hf]
  intro s x hx
  show Tendsto (fun t : ℝ≥0 => lipschitzFlow hf t (lipschitzFlow hf s x)) atTop (𝓝 xs)
  have : (fun t : ℝ≥0 => lipschitzFlow hf t (lipschitzFlow hf s x)) =
      (fun t => lipschitzFlow hf t x) ∘ (fun t => t + s) := by
    funext t; simp [Flow.map_add]
  rw [this]
  exact hx.comp (tendsto_atTop_mono (fun _ => le_self_add) tendsto_id)

/-- Local attraction, a ball in the region of attraction, makes the region of attraction open. -/
@[tmio T, powerlib_foundation] theorem basin_isOpen (hf : LipschitzWith K f) {xs : State n}
    (hattr : ∃ r > 0, Metric.ball xs r ⊆ Flow.regionOfAttraction f xs) :
    IsOpen (Flow.regionOfAttraction f xs) := by
  rw [regionOfAttraction_eq_setOf_tendsto hf] at hattr ⊢
  obtain ⟨r, hr, hball⟩ := hattr
  rw [Metric.isOpen_iff]
  intro x hx
  -- some time `T` brings `x` into the ball of radius `r/2`
  obtain ⟨T, hT⟩ := (hx.eventually (Metric.ball_mem_nhds xs (half_pos hr))).exists
  -- continuity of `φ_T`
  have hcont : Continuous (lipschitzFlow hf T) := (lipschitzFlow hf).continuous_toFun T
  obtain ⟨δ, hδ, hδball⟩ := Metric.continuous_iff.mp hcont x (r / 2) (half_pos hr)
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have hyT : dist (lipschitzFlow hf T y) xs < r := by
    have h1 := hδball y hy
    have h2 : dist (lipschitzFlow hf T x) xs < r / 2 := hT
    calc dist (lipschitzFlow hf T y) xs
        ≤ dist (lipschitzFlow hf T y) (lipschitzFlow hf T x) + dist (lipschitzFlow hf T x) xs :=
          dist_triangle _ _ _
      _ < r := by linarith
  have hin := hball hyT
  show Tendsto (fun t : ℝ≥0 => lipschitzFlow hf t y) atTop (𝓝 xs)
  have hsub : Tendsto (fun t : ℝ≥0 => t - T) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b + T, fun t ht => ?_⟩
    calc b = b + T - T := (add_tsub_cancel_right b T).symm
      _ ≤ t - T := tsub_le_tsub_right ht T
  apply (hin.comp hsub).congr'
  filter_upwards [eventually_ge_atTop T] with t ht
  simp only [Function.comp_def]
  rw [← Flow.map_add, tsub_add_cancel_of_le ht]

/-- Local asymptotic stability gives local attraction, hence an open region of attraction. -/
@[tmio T, powerlib_foundation] theorem basin_isOpen_of_localAsymptoticStable
    (hf : LipschitzWith K f) {xs : State n} (hlas : LocalAsymptoticStable f xs) :
    IsOpen (Flow.regionOfAttraction f xs) := by
  obtain ⟨-, c, hc, hconv⟩ := hlas
  refine basin_isOpen hf ⟨c, hc, fun y hy =>
    ⟨⟨_, forwardSolution_zero hf y, lipschitzFlow_solution hf y⟩, fun φ hφ0 hφ => ?_⟩⟩
  exact hconv 0 φ hφ (by rw [hφ0, ← dist_eq_norm]; exact hy)

end powerlib.Dynamics.LaSalle
