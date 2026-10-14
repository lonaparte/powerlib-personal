import dependencies.Mathlib
import theorem.Attributes

/-! # Frequency-response aggregation identities

Static foundation: algebraic and differential identities between frequency-response signals (COI
aggregation, droop aggregation, virtual inertia, kinetic energy, current-limited power), with the
premises the source notes leave implicit.  They do not by themselves claim stability of any
system.

Model boundary.
* Conventions: Kundur per-unit (`Δω` per-unit, `M = 2H` [s]); generator-side balance
  `M Δω̇ = ΔP_m − ΔP_e − D Δω` (power delivered to the network positive, as in the source
  notes).
* Identities between signals; no network, controller or limiter dynamics beyond the stated
  equations.

Source: work-sync `theory/T-frequency-stability.md` §1.1–§1.4 (single-machine swing, COI
aggregation, droop aggregation, virtual inertia), `theory/T-synthetic-inertia-ffr.md` §1.2–§1.3
(kinetic energy, VSM merged into `M_eff`, current-limit power bound).

Results (and the premises the note leaves implicit).
* `coi_swing_of_proportional_damping` (§1.2): summing the machine swing equations gives the
  boxed COI swing `M_sys Δω̇_COI = ΔP_m − ΔP_L − D_sys Δω_COI` **only** under two extra premises
  that the note uses silently: network power conservation `Σ ΔP_e,k = ΔP_L + ΔP_loss` (the
  "machine exchanges cancel" step; losses kept explicit) and damping proportional to inertia
  `D_k = λ M_k` (or all machines at one frequency, `coi_swing_of_common_frequency`).
  `coi_damping_counterexample` shows the damping step fails without such a premise.
* `droop_aggregate` (§1.3): with one common `T_g`, the aggregate `ΔP_m = Σ ΔP_m,k` obeys
  `T_g ΔṖ_m = −ΔP_m − (Σ K_R,k) Δω`.
* `virtualInertia_merge`, `virtualInertia_rate` (§1.4, `T-synthetic-inertia-ffr.md` §1.3):
  linear inertia/damping injections `−K_d Δω̇ − K_R^inv Δω` merge into `M_eff`, `D_eff`; solving
  for `Δω̇` needs `M_eff ≠ 0`.
* `kineticEnergy_expansion` (`T-synthetic-inertia-ffr.md` §1.2): exact
  `½ J (ω_s + Δω)² = ½ J ω_s² + J ω_s Δω + ½ J Δω²`; the note's "≈" drops the remainder
  `½ J Δω²` (`kineticEnergy_remainder_nonneg`).
* `activePower_abs_le` (`T-synthetic-inertia-ffr.md` §1.3): from `S̄ = 3 V̄ Ī*`
  (`|V_LL| = √3 |V̄|`), a current limit `|Ī| ≤ i_max` bounds the **total** active power,
  `|P| ≤ |S̄| ≤ √3 V_LL i_max`.

Correction (`T-synthetic-inertia-ffr.md` §1.3).
* The note writes the current-limit bound for `ΔP`; `deltaPower_counterexample` shows a power
  *change* can reach `2 √3 V_LL i_max`.
-/

noncomputable section
namespace powerlib.Frequency.Aggregation
open scoped BigOperators

/-! ## COI aggregation (§1.2) -/

section COI

variable {ι : Type*} [Fintype ι]

/-- Inertia-weighted centre-of-inertia frequency `Σ M_k Δω_k / Σ M_k`. -/
def coi (M ω : ι → ℝ) : ℝ := (∑ k, M k * ω k) / ∑ k, M k

/-- The COI frequency of signals `Δω_k(t)` is differentiable with the weighted-mean rate. -/
@[powerlib_foundation] theorem hasDerivAt_coi {M : ι → ℝ} {ω ω' : ι → ℝ → ℝ} {t : ℝ}
    (hω : ∀ k, HasDerivAt (ω k) (ω' k t) t) :
    HasDerivAt (fun s => coi M (fun k => ω k s)) ((∑ k, M k * ω' k t) / ∑ k, M k) t := by
  unfold coi
  have h := HasDerivAt.sum (u := Finset.univ) (fun k _ => (hω k).const_mul (M k))
  simpa [Finset.sum_fn] using h.div_const (∑ k, M k)

/-- §1.2 boxed COI swing, under network power conservation and `D_k = λ M_k`. -/
@[powerlib_foundation] theorem coi_swing_of_proportional_damping
    {M D Pm Pe ω ω' : ι → ℝ} {lam PL Ploss : ℝ} (hMsys : (∑ k, M k) ≠ 0)
    (hswing : ∀ k, M k * ω' k = Pm k - Pe k - D k * ω k)
    (hcons : ∑ k, Pe k = PL + Ploss) (hD : ∀ k, D k = lam * M k) :
    (∑ k, M k) * ((∑ k, M k * ω' k) / ∑ k, M k) =
      ∑ k, Pm k - (PL + Ploss) - (∑ k, D k) * coi M ω := by
  rw [mul_div_cancel₀ _ hMsys, Finset.sum_congr rfl fun k _ => hswing k,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, hcons]
  have h1 : ∑ k, D k * ω k = lam * ∑ k, M k * ω k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by rw [hD k]; ring
  have h2 : ∑ k, D k = lam * ∑ k, M k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => hD k
  rw [h1, h2, coi]
  field_simp

/-- §1.2 with all machines at one common frequency deviation `Δω`. -/
@[powerlib_foundation] theorem coi_swing_of_common_frequency
    {M D Pm Pe : ι → ℝ} {w w' PL Ploss : ℝ} (hMsys : (∑ k, M k) ≠ 0)
    (hswing : ∀ k, M k * w' = Pm k - Pe k - D k * w)
    (hcons : ∑ k, Pe k = PL + Ploss) :
    coi M (fun _ => w) = w ∧
      (∑ k, M k) * w' = ∑ k, Pm k - (PL + Ploss) - (∑ k, D k) * w := by
  refine ⟨by unfold coi; rw [← Finset.sum_mul]; field_simp, ?_⟩
  rw [Finset.sum_mul, Finset.sum_congr rfl fun k _ => hswing k, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, hcons, Finset.sum_mul]

/-- Without a premise linking `D_k` to `M_k` (or a common frequency), the damping sum is not
`D_sys Δω_COI`: two equal-inertia machines, `D = (1, 0)`, `Δω = (1, 0)`. -/
@[powerlib_foundation] theorem coi_damping_counterexample :
    ∑ k : Fin 2, ![(1 : ℝ), 0] k * ![(1 : ℝ), 0] k ≠
      (∑ k : Fin 2, ![(1 : ℝ), 0] k) * coi ![1, 1] ![1, 0] := by
  simp [coi, Fin.sum_univ_two]

end COI

/-! ## Droop aggregation (§1.3) -/

/-- With a common governor time constant, the aggregate mechanical power obeys the single
first-order droop law with `K_R = Σ K_R,k`. -/
@[powerlib_foundation] theorem droop_aggregate {ι : Type*} [Fintype ι] {Tg : ℝ} {K : ι → ℝ}
    {P : ι → ℝ → ℝ} {P' : ι → ℝ} {w t : ℝ} (hP : ∀ k, HasDerivAt (P k) (P' k) t)
    (hgov : ∀ k, Tg * P' k = -P k t - K k * w) :
    HasDerivAt (fun s => ∑ k, P k s) (∑ k, P' k) t ∧
      Tg * ∑ k, P' k = -(∑ k, P k t) - (∑ k, K k) * w := by
  refine ⟨?_, ?_⟩
  · have h := HasDerivAt.sum (u := Finset.univ) (fun k _ => hP k)
    simpa [Finset.sum_fn] using h
  · rw [Finset.mul_sum, Finset.sum_congr rfl fun k _ => hgov k, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib, Finset.sum_mul]

/-! ## Virtual inertia (§1.4) -/

/-- Linear virtual-inertia / virtual-damping injections `ΔP_inv,j = −K_d,j Δω̇ − K_R,j Δω`
merge into `M_eff = M_sys + Σ K_d,j`, `D_eff = D_sys + Σ K_R,j`. -/
@[powerlib_foundation] theorem virtualInertia_merge {ι : Type*} [Fintype ι]
    {Msys Dsys Pm PL w w' : ℝ} {Kd KR : ι → ℝ}
    (hswing : Msys * w' = Pm + ∑ j, (-Kd j * w' - KR j * w) - PL - Dsys * w) :
    (Msys + ∑ j, Kd j) * w' = Pm - PL - (Dsys + ∑ j, KR j) * w := by
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul] at hswing
  simp only [Finset.sum_neg_distrib, neg_mul] at hswing
  linarith

/-- §1.4 solved for the frequency rate; this needs `M_eff ≠ 0`. -/
@[powerlib_foundation] theorem virtualInertia_rate {Meff Deff Pm PL w w' : ℝ} (hM : Meff ≠ 0)
    (h : Meff * w' = Pm - PL - Deff * w) : w' = (Pm - PL - Deff * w) / Meff := by
  rw [eq_div_iff hM, mul_comm, h]

/-! ## Kinetic energy (`T-synthetic-inertia-ffr.md` §1.2) -/

/-- Exact expansion of `½ J ω²` around `ω_s`; the remainder `½ J Δω²` is what the note's
linear approximation drops. -/
@[powerlib_foundation] theorem kineticEnergy_expansion (J ωs Δω : ℝ) :
    J * (ωs + Δω) ^ 2 / 2 = J * ωs ^ 2 / 2 + J * ωs * Δω + J * Δω ^ 2 / 2 := by
  ring

/-- The released energy `½J(ω_s + Δω)² − ½Jω_s² − Jω_sΔω` equals `½JΔω² ≥ 0` (`J ≥ 0`). -/
@[powerlib_foundation] theorem kineticEnergy_remainder_nonneg {J : ℝ} (hJ : 0 ≤ J) (ωs Δω : ℝ) :
    0 ≤ J * (ωs + Δω) ^ 2 / 2 - (J * ωs ^ 2 / 2 + J * ωs * Δω) := by
  have : J * (ωs + Δω) ^ 2 / 2 - (J * ωs ^ 2 / 2 + J * ωs * Δω) = J * Δω ^ 2 / 2 := by ring
  rw [this]; positivity

/-! ## Current-limited active power (`T-synthetic-inertia-ffr.md` §1.3) -/

/-- Three-phase complex power `S̄ = 3 V̄ Ī*` from phase phasors (rms). -/
def complexPower (V I : ℂ) : ℂ := 3 * V * (starRingEnd ℂ) I

/-- `|P| ≤ |S̄| = √3 V_LL |Ī| ≤ √3 V_LL i_max`, with `V_LL = √3 |V̄|`. The bound is on the
total active power `P = Re S̄`. -/
@[powerlib_foundation] theorem activePower_abs_le {V I : ℂ} {imax : ℝ} (hI : ‖I‖ ≤ imax) :
    |(complexPower V I).re| ≤ Real.sqrt 3 * (Real.sqrt 3 * ‖V‖) * imax := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hS : ‖complexPower V I‖ = 3 * ‖V‖ * ‖I‖ := by
    simp [complexPower]
  calc |(complexPower V I).re| ≤ ‖complexPower V I‖ := Complex.abs_re_le_norm _
    _ = 3 * ‖V‖ * ‖I‖ := hS
    _ ≤ 3 * ‖V‖ * imax := by gcongr
    _ = Real.sqrt 3 * (Real.sqrt 3 * ‖V‖) * imax := by rw [← mul_assoc, h3]

/-- Correction: the current limit does not bound the *change* `ΔP` by `√3 V_LL i_max`.
Reversing an admissible current from `+i_max` (in phase with `V̄`) to `−i_max` changes the
active power by `−2 · √3 V_LL i_max`. -/
@[powerlib_foundation] theorem deltaPower_counterexample {v imax : ℝ} (hv : 0 < v)
    (himax : 0 < imax) :
    ∃ I₀ I₁ : ℂ, ‖I₀‖ ≤ imax ∧ ‖I₁‖ ≤ imax ∧
      |(complexPower v I₁).re - (complexPower v I₀).re| =
        2 * (Real.sqrt 3 * (Real.sqrt 3 * ‖(v : ℂ)‖) * imax) := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  refine ⟨imax, -imax, by simp [abs_of_pos himax], by simp [abs_of_pos himax], ?_⟩
  simp only [complexPower, map_neg, Complex.conj_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hv]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, Complex.mul_im]
  norm_num
  rw [show -(3 * v * imax) - 3 * v * imax = -(2 * (3 * v * imax)) by ring, abs_neg,
    abs_of_pos (by positivity), ← mul_assoc (Real.sqrt 3), h3]

end powerlib.Frequency.Aggregation
