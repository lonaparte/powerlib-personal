/-
  R2b — loss of synchronism when the synchronous equilibrium disappears.

  Problem R2b (parametric): outside the fold manifold Σ₂ the field has NO synchronous
  equilibrium ⟹ θ_e is unbounded ⟹ loss of synchronism, independent of any local modal damping.

  Mechanism (model-agnostic, which is exactly why "independent of local damping"):
  on the synchronisation manifold the PLL integrator obeys  η' = v_cqc(θ_e) =: G(θ_e),
  and equilibria require `G = 0`.  "Beyond Σ₂" means `G` has no zero, hence (continuous,
  2π-periodic) is sign-definite with a positive margin `m`.  Then `η' = G ≥ m > 0`, so `η`
  grows at least linearly and is unbounded — no equilibrium can be approached.

  This file proves the core (`loss_of_sync_core`) and the "no zero ⟹ margin" reduction
  (`exists_margin_of_no_zero`), combined in `loss_of_sync`.  Fully parametric (abstract `G`),
  no `sorry`.
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Field.Periodic

namespace GFL

open Set

/-- **R2b core — a positive lower bound on the integrator rate forces unbounded drift.**
If `η' = G(θ_e)` along a trajectory and `G ≥ m > 0` everywhere, then `η(t) ≥ η(0) + m·t`
for `t ≥ 0`, so `η` is unbounded (`∀ M, ∃ t ≥ 0, η t > M`). -/
theorem loss_of_sync_core (m : ℝ) (hm : 0 < m) (η θe G : ℝ → ℝ)
    (hη : ∀ t, HasDerivAt η (G (θe t)) t) (hbound : ∀ θ, m ≤ G θ) :
    (∀ t, 0 ≤ t → η 0 + m * t ≤ η t) ∧ (∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ M < η t) := by
  -- mean value theorem: η(t) − η(0) = η'(c)·t = G(θe c)·t ≥ m·t
  have hlin : ∀ t, 0 ≤ t → η 0 + m * t ≤ η t := by
    intro t ht
    rcases ht.eq_or_lt with h | h
    · simp [← h]
    · obtain ⟨c, _, hslope⟩ := exists_hasDerivAt_eq_slope η (fun s => G (θe s)) h
        (fun s _ => (hη s).continuousAt.continuousWithinAt) (fun s _ => hη s)
      have hmc : m ≤ (η t - η 0) / (t - 0) := hslope ▸ hbound (θe c)
      rw [sub_zero] at hmc
      have := (le_div_iff₀ h).mp hmc
      linarith
  refine ⟨hlin, fun M => ?_⟩
  refine ⟨max 0 ((M - η 0) / m + 1), le_max_left _ _, ?_⟩
  have h1 := hlin _ (le_max_left 0 ((M - η 0) / m + 1))
  have h3 : m * ((M - η 0) / m + 1) ≤ m * max 0 ((M - η 0) / m + 1) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hm.le
  have h4 : m * ((M - η 0) / m + 1) = M - η 0 + m := by field_simp
  linarith

/-- If `G` is continuous, `T`-periodic (`T > 0`), positive somewhere, and has **no zero**, then
it has a positive lower bound `m > 0`.  (Continuous + no zero ⟹ sign-definite by IVT; periodic
⟹ the min over one period `[0,T]` is the global infimum.) -/
theorem exists_margin_of_no_zero (G : ℝ → ℝ) (hG : Continuous G) {T : ℝ} (hT : 0 < T)
    (hper : Function.Periodic G T) {θ₀ : ℝ} (hpos : 0 < G θ₀) (hnz : ∀ θ, G θ ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ θ, m ≤ G θ := by
  -- `G > 0` everywhere: otherwise IVT gives a zero between `θ₀` and a point where `G ≤ 0`.
  have hallpos : ∀ θ, 0 < G θ := by
    intro θ
    rcases lt_trichotomy (G θ) 0 with hneg | hz | hp
    · -- a sign change between θ and θ₀ ⟹ a zero (IVT), contradicting `hnz`
      rcases le_total θ θ₀ with hle | hle
      · obtain ⟨ξ, _, hξ⟩ := intermediate_value_Icc hle hG.continuousOn
          (show (0:ℝ) ∈ Icc (G θ) (G θ₀) from ⟨hneg.le, hpos.le⟩)
        exact absurd hξ (hnz ξ)
      · obtain ⟨ξ, _, hξ⟩ := intermediate_value_Icc' hle hG.continuousOn
          (show (0:ℝ) ∈ Icc (G θ) (G θ₀) from ⟨hneg.le, hpos.le⟩)
        exact absurd hξ (hnz ξ)
    · exact absurd hz (hnz θ)
    · exact hp
  -- min over the compact period `[0,T]`
  obtain ⟨c, _, hc⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_isMinOn
    (nonempty_Icc.2 hT.le) hG.continuousOn
  refine ⟨G c, hallpos c, fun θ => ?_⟩
  -- reduce `θ` into `[0,T)` by periodicity, then use the min on `[0,T]`
  obtain ⟨k, hmem, hk⟩ := hper.exists_mem_Ico₀ hT θ
  rw [hk]
  exact hc ⟨hmem.1, le_of_lt hmem.2⟩

/-- **R2b — loss of synchronism (full).**  If the PLL projection `G = v_cqc` is continuous,
`T`-periodic, has no zero (no synchronous equilibrium — "beyond Σ₂") and is positive somewhere,
then along any trajectory of the integrator `η' = G(θ_e)`, the state `η` is unbounded:
`∀ M, ∃ t ≥ 0, η t > M`.  The converter cannot synchronise. -/
theorem loss_of_sync (η θe G : ℝ → ℝ) (hG : Continuous G) {T : ℝ} (hT : 0 < T)
    (hper : Function.Periodic G T) {θ₀ : ℝ} (hpos : 0 < G θ₀) (hnz : ∀ θ, G θ ≠ 0)
    (hη : ∀ t, HasDerivAt η (G (θe t)) t) :
    ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ M < η t := by
  obtain ⟨m, hm, hbound⟩ := exists_margin_of_no_zero G hG hT hper hpos hnz
  exact (loss_of_sync_core m hm η θe G hη hbound).2

end GFL
