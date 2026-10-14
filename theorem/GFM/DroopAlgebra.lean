import theorem.Attributes
import dependencies.Mathlib
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Algebraic identities of droop, VSM and matching control (foundation)

Every statement here is an algebraic identity, a Laplace-domain relation or a
fundamental-theorem-of-calculus identity; none asserts a stability property of a power system.

* Complex power `S̄ = V̄ Ī*` in `dq` components (IN-positive current) and the export-positive
  translation `P^ext = −P^abs`, `Q^ext = −Q^abs` (T-vsg-control §1.1): `Transform.complexPower_dq`,
  `Transform.exportPower_dq` (`theorem/Transform/ComplexPower.lean`).
* Inertia conversions `K_d = J ω_s / S_b`, `H = ½ J ω_s² / S_b`, `M_vsm = 2H/ω_s = K_d`
  (T-vsg-control §1.0, §1.2; T-gfm-control §1.4).
* Line powers (export from the source `E ∠ δ` through `R + jX` into `V ∠ 0`) from `S̄ = Ē Ī*`,
  their partial derivatives at `δ = 0, E = V`, and the rotation `R(β)`, `β = π/2 − θ_l`,
  that diagonalizes this Jacobian (T-droop-control §1.2): `Network.linePower`, `Network.lineP`,
  `Network.lineQ`, `Network.rotation_diagonalizes` (`theorem/Network/PowerFlow.lean`).
* Static droop `u = u* − K (y − y*)`: DC gain `−K`; shared `Δu` gives
  `Δy_k / Δy_l = K_l / K_k` (T-droop-control §1.1).
* Governor `T_g ΔṖ_m = −ΔP_m − K_R Δω` ⇒ `ΔP_m = −K_R/(1 + T_g s) Δω` (T-droop-control §1.3).
* Multi-unit droop: `ΔP_k = −K_{R,k} Δω`, system droop `Σ K`, steady deviation
  `Δω = −ΔP_L/(Σ K + D_eff)`, proportional sharing `⇔ K_{R,k} ∝ S_{N,k}`, the weighted
  consensus formula (T-droop-control §1.6–§1.8; T-gfm-control §2.3).
* Virtual-inertia energy `∫ K_d ω̇ ω = ½ K_d (ω(t)² − ω(t₀)²)` (T-gfm-control §2.4).
* Matching control `θ̇ = η u_dc`, `C u̇_dc = i_dc − G u_dc − i_x`: the frequency obeys a swing
  equation with `M = C/η²`, `D = G/η²`, torque `i_dc/η` (T-gfm-control §1.6 table):
  `GFM.Matching.matching_swing` (`theorem/GFM/Matching/Matching.lean`).
* Rotated droop limits: inductive line `θ_l = π/2` ⇒ `R(β) = I`; resistive line `θ_l = 0` ⇒
  `(P̂, Q̂) = (−Q, P)` (T-droop-control §1.5): `Network.rotation_inductive`,
  `Network.rotation_resistive`.

Family and connection conclusions: none.  The module has no behavioural content; every statement
is public foundation (Rules §3).

Source: work-sync theory/T-vsg-control.md §1.0–§1.2; theory/T-gfm-control.md §1.4, §1.6, §2.3,
§2.4; theory/T-droop-control.md §1.1–§1.8.
-/

noncomputable section
namespace powerlib.GFM
open Complex

/-! ## Inertia conversions -/

/-- `M_vsm = 2H/ω_s` equals `K_d = J ω_s / S_b` when `H = ½ J ω_s² / S_b`. -/
@[powerlib_foundation] theorem Mvsm_eq_Kd {J ωs Sb : ℝ} (hω : ωs ≠ 0) (hS : Sb ≠ 0) :
    2 * (J * ωs ^ 2 / (2 * Sb)) / ωs = J * ωs / Sb := by
  field_simp

/-! ## Static droop and sharing -/

/-- Static droop `u = u* − K (y − y*)` has DC gain `Δu/Δy = −K`, i.e. `Δy = −Δu/K`. -/
@[powerlib_foundation] theorem droop_deviation {K u ustar y ystar : ℝ} (hK : K ≠ 0)
    (h : u = ustar - K * (y - ystar)) : y - ystar = -(u - ustar) / K := by
  rw [h]; field_simp; ring

/-- Units sharing the same `Δu` split `Δy` inversely to their gains: `Δy_k/Δy_l = K_l/K_k`. -/
@[powerlib_foundation] theorem droop_sharing {Kk Kl Δu Δyk Δyl : ℝ} (hk : Kk ≠ 0)
    (hu : Δu ≠ 0) (hyk : Δu = -Kk * Δyk) (hyl : Δu = -Kl * Δyl) : Δyk / Δyl = Kl / Kk := by
  have hyl0 : Δyl ≠ 0 := by rintro rfl; simp at hyl; exact hu hyl
  field_simp
  linarith

/-- Governor: from `T_g s ΔP_m = −ΔP_m − K_R Δω`, `ΔP_m = −K_R/(1 + T_g s) Δω`. -/
@[powerlib_foundation] theorem governor_transfer {KR Tg : ℝ} {s ΔPm Δω : ℂ}
    (hden : 1 + (Tg : ℂ) * s ≠ 0) (h : (Tg : ℂ) * s * ΔPm = -ΔPm - (KR : ℂ) * Δω) :
    ΔPm = -(KR : ℂ) / (1 + (Tg : ℂ) * s) * Δω := by
  field_simp
  linear_combination h

/-- Multi-unit droop: if `ΔP_k = −K_k Δω` and the units together balance `ΔP_L` with frequency
damping `D_eff Δω`, i.e. `Σ ΔP_k − D_eff Δω = ΔP_L`, then `Δω = −ΔP_L/(Σ K_k + D_eff)`. -/
@[powerlib_foundation] theorem steadyState_frequency {N : ℕ} (K ΔP : Fin N → ℝ) {Δω ΔPL Deff : ℝ}
    (hden : ∑ k, K k + Deff ≠ 0) (hk : ∀ k, ΔP k = -K k * Δω)
    (hbal : ∑ k, ΔP k - Deff * Δω = ΔPL) : Δω = -ΔPL / (∑ k, K k + Deff) := by
  rw [Finset.sum_congr rfl (fun k _ => hk k), ← Finset.sum_mul] at hbal
  field_simp
  rw [Finset.sum_neg_distrib] at hbal
  linarith

/-- Proportional sharing: with `ΔP_k = −K_k Δω`, `Δω ≠ 0`, the per-rating shares `ΔP_k / S_k`
are all equal iff the gains are proportional to the ratings. -/
@[powerlib_foundation] theorem proportionalSharing_iff {N : ℕ} (K S ΔP : Fin N → ℝ) {Δω : ℝ}
    (hS : ∀ k, S k ≠ 0) (hω : Δω ≠ 0) (hk : ∀ k, ΔP k = -K k * Δω) :
    (∃ ρ, ∀ k, ΔP k / S k = ρ) ↔ ∃ κ, ∀ k, K k = κ * S k := by
  constructor
  · rintro ⟨ρ, hρ⟩
    refine ⟨-ρ / Δω, fun k => ?_⟩
    have := hρ k
    rw [hk k] at this
    have hSk := hS k
    field_simp at this ⊢
    linarith
  · rintro ⟨κ, hκ⟩
    refine ⟨-κ * Δω, fun k => ?_⟩
    rw [hk k, hκ k]
    field_simp [hS k]

/-- Weighted consensus: `P_k = K_k (ω_s − ω) + P*_k` with `Σ P_k = P_L` gives the common
frequency `ω = ω_s − (P_L − Σ P*_k)/Σ K_k`. -/
@[powerlib_foundation] theorem consensus_frequency {N : ℕ} (K P Pstar : Fin N → ℝ) {ω ωs PL : ℝ}
    (hK : ∑ k, K k ≠ 0) (hP : ∀ k, P k = K k * (ωs - ω) + Pstar k) (hsum : ∑ k, P k = PL) :
    ω = ωs - (PL - ∑ k, Pstar k) / ∑ k, K k := by
  rw [Finset.sum_congr rfl (fun k _ => hP k), Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
  field_simp
  linarith

/-! ## Virtual-inertia energy -/

/-- `∫_{t₀}^{t} K_d ω̇ ω = ½ K_d (ω(t)² − ω(t₀)²)` for a `C¹` frequency deviation. -/
@[powerlib_foundation] theorem virtualInertia_energy {ω ω' : ℝ → ℝ} (Kd t₀ t : ℝ)
    (hd : ∀ s, HasDerivAt ω (ω' s) s) (hc : Continuous ω') :
    ∫ s in t₀..t, Kd * ω' s * ω s = Kd / 2 * (ω t ^ 2 - ω t₀ ^ 2) := by
  have hcω : Continuous ω := continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt
  have hF : ∀ s ∈ Set.uIcc t₀ t, HasDerivAt (fun s => Kd / 2 * ω s ^ 2) (Kd * ω' s * ω s) s := by
    intro s _
    have := ((hd s).pow 2).const_mul (Kd / 2)
    convert this using 1
    simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((by fun_prop : Continuous fun s => Kd * ω' s * ω s).intervalIntegrable _ _)]
  ring

end powerlib.GFM
