import theorem.PhasePlane.Flow
import theorem.Dynamics.State

/-! # Basins of attraction are open and invariant

Foundation layer for the attractor/basin language, under the completeness premise of
`PhasePlane/Flow.lean` (globally Lipschitz field, forward flow `φ_t`, `t ∈ ℝ≥0`).

Basin. The basin of attraction of `x*` for the forward flow is `𝓑(x*) = {x | φ_t x → x* as
t → ∞}`, written out in the statements as the set
`{x | Tendsto (fun t : ℝ≥0 => lipschitzFlow hf t x) atTop (𝓝 xs)}` (the former definition
`basin` is removed: behaviour is defined only in the semantic layer).

Results.
* `basin_isInvariant`: `φ_s(𝓑) ⊆ 𝓑` for every `s ≥ 0` (Mathlib `IsInvariant`).
* `basin_isOpen`: if some ball around `x*` lies in the basin (local attraction), the basin is
  open; the proof uses only the continuity of `φ_T` (continuous dependence on initial data).
* `basin_isOpen_of_localAsymptoticStable`: on `State n`, local asymptotic stability
  (LeanForControl `LocalAsymptoticStable`) of `x*` gives local attraction, so its basin is open.

Source: work-sync theory/T-attractors-basins.md §1.2 (`𝓑(A)`), and its premise "basin of
attraction 是开集" (proved here for asymptotically stable equilibria of Lipschitz fields).
-/

noncomputable section
namespace powerlib.PhasePlane

open Set Filter Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : E → E} {K : ℝ≥0}

/-- The basin of attraction `{x | φ_t x → x*}` of `x*` for the forward flow is forward
invariant. -/
@[powerlib_foundation] theorem basin_isInvariant (hf : LipschitzWith K f) (xs : E) :
    IsInvariant (lipschitzFlow hf)
      {x | Tendsto (fun t : ℝ≥0 => lipschitzFlow hf t x) atTop (𝓝 xs)} := by
  intro s x hx
  show Tendsto (fun t : ℝ≥0 => lipschitzFlow hf t (lipschitzFlow hf s x)) atTop (𝓝 xs)
  have : (fun t : ℝ≥0 => lipschitzFlow hf t (lipschitzFlow hf s x)) =
      (fun t => lipschitzFlow hf t x) ∘ (fun t => t + s) := by
    funext t; simp [lipschitzFlow_add]
  rw [this]
  exact hx.comp (tendsto_atTop_mono (fun _ => le_self_add) tendsto_id)

/-- Local attraction makes the basin of attraction `{x | φ_t x → x*}` open. -/
@[powerlib_foundation] theorem basin_isOpen (hf : LipschitzWith K f) {xs : E}
    (hattr : ∃ r > 0, ∀ y, dist y xs < r →
      y ∈ {x | Tendsto (fun t : ℝ≥0 => lipschitzFlow hf t x) atTop (𝓝 xs)}) :
    IsOpen {x | Tendsto (fun t : ℝ≥0 => lipschitzFlow hf t x) atTop (𝓝 xs)} := by
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
  have hin := hball _ hyT
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
  rw [← lipschitzFlow_add, tsub_add_cancel_of_le ht]

/-- Coercion `ℝ≥0 → ℝ` tends to `+∞`. -/
@[powerlib_foundation] theorem tendsto_nnreal_coe_atTop :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  exact ⟨⟨max b 0, le_max_right _ _⟩, fun a ha => le_trans (le_max_left _ _) ha⟩

/-- On `State n`, local asymptotic stability gives local attraction, hence an open basin of
attraction `{x | φ_t x → x*}`. -/
@[powerlib_foundation] theorem basin_isOpen_of_localAsymptoticStable {n : ℕ}
    {g : Dynamics.State n → Dynamics.State n} (hg : LipschitzWith K g) {xs : Dynamics.State n}
    (hlas : LocalAsymptoticStable g xs) :
    IsOpen {x | Tendsto (fun t : ℝ≥0 => lipschitzFlow hg t x) atTop (𝓝 xs)} := by
  obtain ⟨-, c, hc, hconv⟩ := hlas
  apply basin_isOpen hg ⟨c, hc, fun y hy => ?_⟩
  have h := hconv 0 (forwardSolution hg y) (lipschitzFlow_solution hg y)
    (by rw [(forwardSolution_spec hg y).1, ← dist_eq_norm]; exact hy)
  exact h.comp tendsto_nnreal_coe_atTop

end powerlib.PhasePlane
