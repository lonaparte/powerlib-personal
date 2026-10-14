import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.Processes
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! # Optional stopping for uniformly integrable stopped martingales

The optional stopping theorem in discrete time for an almost surely finite stopping time whose
stopped martingale is uniformly integrable.

Scope.
* Probability theory, not an engineering result. Discrete time `ℕ`, real martingale `M` on a
  probability space.

Source: work-sync theory/T-martingales-stopping-times.md §1.5 (optional stopping theorem,
discrete time: if `τ ≤ N` a.s. **or** `(M_{n∧τ})_n` is uniformly integrable, then
`E[M_τ] = E[M_0]`).

Results.
* `martingale_integral_eq` — `E M_n = E M_0`.
* `stoppedProcess_tendsto_stoppedValue` — if `τ < ∞` a.s. then `M_{n∧τ} → M_τ` a.s.
* `optional_stopping_UI` — if `τ` is a stopping time with `τ < ∞` a.s. and the stopped process
  `(M_{n∧τ})_n` is uniformly integrable, then `M_τ` is integrable and `E[M_τ] = E[M_0]`
  (bounded optional stopping for `M_{n∧τ}` + Vitali convergence theorem).

Corrections.
* §1.5, condition 2: "`(M_{n∧τ})` UI ⇒ `E[M_τ] = E[M_0]`" needs `τ < ∞` a.s. (or a definition
  of `M_∞`): on `{τ = ∞}` the value `M_τ` is not defined by the note. The formal statement
  assumes `τ < ∞` a.s. explicitly.
-/

noncomputable section
namespace powerlib.Stochastic.Proc

open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m}
  {f : ℕ → Ω → ℝ} {τ : Ω → WithTop ℕ}

/-- A martingale has constant expectation. -/
@[powerlib_foundation] theorem martingale_integral_eq [IsFiniteMeasure μ]
    (h : Martingale f 𝒢 μ) (n : ℕ) : ∫ ω, f n ω ∂μ = ∫ ω, f 0 ω ∂μ := by
  rw [← integral_condExp (𝒢.le 0)]
  exact integral_congr_ae (h.condExp_ae_eq (Nat.zero_le n))

/-- If `τ < ∞` a.s., the stopped process converges a.s. to the stopped value. -/
@[powerlib_foundation] theorem stoppedProcess_tendsto_stoppedValue
    (hfin : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => stoppedProcess f τ n ω) atTop (𝓝 (stoppedValue f τ ω)) := by
  filter_upwards [hfin] with ω hω
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hω
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop k] with n hn
  rw [stoppedProcess_eq_of_ge (by rw [← hk]; exact_mod_cast hn)]
  rfl

/-- **Optional stopping, uniformly integrable version**: `τ < ∞` a.s. and `(M_{n∧τ})` UI ⇒
`E[M_τ] = E[M_0]`. -/
@[powerlib_foundation] theorem optional_stopping_UI [IsProbabilityMeasure μ]
    (h : Martingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ) (hfin : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    (hUI : UniformIntegrable (stoppedProcess f τ) 1 μ) :
    Integrable (stoppedValue f τ) μ ∧ ∫ ω, stoppedValue f τ ω ∂μ = ∫ ω, f 0 ω ∂μ := by
  have hconv := stoppedProcess_tendsto_stoppedValue (f := f) hfin
  have hg : MemLp (stoppedValue f τ) 1 μ := hUI.memLp_of_ae_tendsto hconv
  refine ⟨memLp_one_iff_integrable.mp hg, ?_⟩
  have hL1 := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
    (fun n => (hUI.memLp n).aestronglyMeasurable) hg hUI.unifIntegrable hconv
  have hint := tendsto_integral_of_L1' (stoppedValue f τ)
    (Eventually.of_forall fun n => (hUI.memLp n).integrable le_rfl) hL1
  have hconst : ∀ n, ∫ ω, stoppedProcess f τ n ω ∂μ = ∫ ω, f 0 ω ∂μ := by
    intro n
    rw [martingale_integral_eq (martingale_stoppedProcess h hτ) n]
    congr 1
    funext ω
    exact stoppedProcess_eq_of_le zero_le
  simp_rw [hconst] at hint
  exact tendsto_nhds_unique hint tendsto_const_nhds

end powerlib.Stochastic.Proc
