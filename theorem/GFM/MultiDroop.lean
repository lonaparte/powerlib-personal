import theorem.GFM.DroopAlgebra

/-! # N droop units on a network: synchronous steady states share power by their droop gains

Model boundary.
* `N` grid-forming units with droop + first-order power filter, state
  `x = (θ, P_f) ∈ (Fin N → ℝ) × (Fin N → ℝ)` (unit angles in a frame rotating at an arbitrary
  constant speed, filtered powers):
  `θ̇_k = ω_s − (P_{f,k} − P*_k)/K_{R,k}`, `τ_k Ṗ_{f,k} = P_k(θ) − P_{f,k}`.
* Network: an arbitrary static map `P : (Fin N → ℝ) → (Fin N → ℝ)` (export-positive unit
  powers) that depends only on angle differences (`P (θ + c·1) = P θ`); for the frequency
  formula, additionally a constant total load `Σ_k P_k(θ) = P_L` (lossless network with
  constant-power loads).  Continuous time; no voltage loops, inner loops, PLL, limiters.
* A *synchronous steady state* is a solution of the form `θ(t) = θ₀ + ω t · 1`,
  `P_f(t) ≡ P_{f0}` — an equilibrium of the closed loop in the frame rotating with the common
  frequency `ω`.

Results: such a curve is a solution iff `P_{f0} = P(θ₀)` and every unit's droop frequency
equals `ω` (`synchronous_solution_iff`); then every unit obeys `ΔP_k = −K_{R,k} (ω − ω_s)`
(`synchronous_sharing`), the common frequency is `ω = ω_s − (P_L − Σ P*)/Σ K` (consensus
formula), and the per-rating shares are equal iff `K_{R,k} ∝ S_{N,k}`.

Source: work-sync theory/T-droop-control.md §1.6–§1.8; theory/T-gfm-control.md §2.3.
-/

noncomputable section
namespace powerlib.GFM

/-- Parameters of `N` droop + LPF units on a static network. -/
structure MultiDroop (N : ℕ) where
  KR : Fin N → ℝ
  τ : Fin N → ℝ
  Pstar : Fin N → ℝ
  ωs : ℝ
  P : (Fin N → ℝ) → (Fin N → ℝ)

namespace MultiDroop

variable {N : ℕ} (m : MultiDroop N)

/-- Closed-loop field on `(θ, P_f)`. -/
def field (x : (Fin N → ℝ) × (Fin N → ℝ)) : (Fin N → ℝ) × (Fin N → ℝ) :=
  (fun k => m.ωs - (x.2 k - m.Pstar k) / m.KR k, fun k => (m.P x.1 k - x.2 k) / m.τ k)

/-- The uniformly rotating candidate `t ↦ (θ₀ + ω t · 1, P_{f0})`. -/
def syncCurve (θ₀ Pf₀ : Fin N → ℝ) (ω : ℝ) (t : ℝ) : (Fin N → ℝ) × (Fin N → ℝ) :=
  (fun k => θ₀ k + ω * t, Pf₀)

@[powerlib_foundation] theorem hasDerivAt_syncCurve (θ₀ Pf₀ : Fin N → ℝ) (ω t : ℝ) :
    HasDerivAt (syncCurve θ₀ Pf₀ ω) ((fun _ => ω), (0 : Fin N → ℝ)) t := by
  apply HasDerivAt.prodMk
  · apply hasDerivAt_pi.mpr
    intro k
    simpa using ((hasDerivAt_id t).const_mul ω).const_add (θ₀ k)
  · exact hasDerivAt_const _ _

/-- A uniformly rotating curve is a solution iff the filtered powers equal the network powers
and every unit's droop frequency equals the common frequency `ω`. -/
@[powerlib_domain] theorem synchronous_solution_iff (hτ : ∀ k, m.τ k ≠ 0)
    (hshift : ∀ θ c, m.P (fun k => θ k + c) = m.P θ) (θ₀ Pf₀ : Fin N → ℝ) (ω : ℝ) :
    (∀ t, HasDerivAt (syncCurve θ₀ Pf₀ ω) (m.field (syncCurve θ₀ Pf₀ ω t)) t) ↔
      (∀ k, Pf₀ k = m.P θ₀ k) ∧ ∀ k, m.ωs - (Pf₀ k - m.Pstar k) / m.KR k = ω := by
  have hval : ∀ t, m.field (syncCurve θ₀ Pf₀ ω t) =
      (fun k => m.ωs - (Pf₀ k - m.Pstar k) / m.KR k, fun k => (m.P θ₀ k - Pf₀ k) / m.τ k) := by
    intro t
    simp only [field, syncCurve]
    rw [hshift θ₀ (ω * t)]
  constructor
  · intro h
    have heq := (h 0).unique (hasDerivAt_syncCurve θ₀ Pf₀ ω 0)
    rw [hval] at heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    refine ⟨fun k => ?_, fun k => congrFun h1 k⟩
    have := congrFun h2 k
    simp only [Pi.zero_apply, div_eq_zero_iff, hτ k, or_false, sub_eq_zero] at this
    exact this.symm
  · rintro ⟨h1, h2⟩ t
    rw [hval]
    convert hasDerivAt_syncCurve θ₀ Pf₀ ω t using 1
    ext k
    · exact h2 k
    · simp [h1 k]

/-- In a synchronous steady state every unit shares `ΔP_k = P_k − P*_k = −K_{R,k} (ω − ω_s)`. -/
@[powerlib_domain] theorem synchronous_sharing (hτ : ∀ k, m.τ k ≠ 0) (hK : ∀ k, m.KR k ≠ 0)
    (hshift : ∀ θ c, m.P (fun k => θ k + c) = m.P θ) {θ₀ Pf₀ : Fin N → ℝ} {ω : ℝ}
    (hsol : ∀ t, HasDerivAt (syncCurve θ₀ Pf₀ ω) (m.field (syncCurve θ₀ Pf₀ ω t)) t) :
    ∀ k, m.P θ₀ k - m.Pstar k = -m.KR k * (ω - m.ωs) := by
  obtain ⟨h1, h2⟩ := (m.synchronous_solution_iff hτ hshift θ₀ Pf₀ ω).mp hsol
  intro k
  have := h2 k
  rw [h1 k] at this
  have hk := hK k
  field_simp at this ⊢
  linarith

/-- The common frequency of any synchronous steady state is
`ω = ω_s − (P_L − Σ P*_k)/Σ K_{R,k}` when the network delivers the constant total load `P_L`. -/
@[powerlib_domain] theorem synchronous_frequency (hτ : ∀ k, m.τ k ≠ 0) (hK : ∀ k, m.KR k ≠ 0)
    (hshift : ∀ θ c, m.P (fun k => θ k + c) = m.P θ) {PL : ℝ}
    (hload : ∀ θ, ∑ k, m.P θ k = PL) (hsum : ∑ k, m.KR k ≠ 0) {θ₀ Pf₀ : Fin N → ℝ} {ω : ℝ}
    (hsol : ∀ t, HasDerivAt (syncCurve θ₀ Pf₀ ω) (m.field (syncCurve θ₀ Pf₀ ω t)) t) :
    ω = m.ωs - (PL - ∑ k, m.Pstar k) / ∑ k, m.KR k := by
  have hs := m.synchronous_sharing hτ hK hshift hsol
  exact consensus_frequency m.KR (m.P θ₀) m.Pstar hsum
    (fun k => by have := hs k; linarith) (hload θ₀)

/-- Proportional (per-rating) sharing in a synchronous steady state off nominal frequency holds
iff the droop gains are proportional to the ratings. -/
@[powerlib_domain] theorem synchronous_proportionalSharing_iff (hτ : ∀ k, m.τ k ≠ 0)
    (hK : ∀ k, m.KR k ≠ 0) (hshift : ∀ θ c, m.P (fun k => θ k + c) = m.P θ) (S : Fin N → ℝ)
    (hS : ∀ k, S k ≠ 0) {θ₀ Pf₀ : Fin N → ℝ} {ω : ℝ} (hω : ω ≠ m.ωs)
    (hsol : ∀ t, HasDerivAt (syncCurve θ₀ Pf₀ ω) (m.field (syncCurve θ₀ Pf₀ ω t)) t) :
    (∃ ρ, ∀ k, (m.P θ₀ k - m.Pstar k) / S k = ρ) ↔ ∃ κ, ∀ k, m.KR k = κ * S k :=
  proportionalSharing_iff m.KR S (fun k => m.P θ₀ k - m.Pstar k) hS (sub_ne_zero.mpr hω)
    (m.synchronous_sharing hτ hK hshift hsol)

end MultiDroop
end powerlib.GFM
