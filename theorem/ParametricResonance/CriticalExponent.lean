import theorem.ParametricResonance.ThirdOrderBoundary

/-! # The critical Floquet exponent on the first-order boundary

On the first-order boundary `det M = 0 > tr M` of the 2:1 criterion the verdict is the sign of
the second-order quantity `mixedDet(M, N)` (`Boundary.critical_jury`,
`Boundary.full_boundary_decided`, `SecondOrder.full_boundary_closed_form`); what was proved there
is only the sign of `det(I − Φ_y) = ε³ T mixedDet(M, N) + O(ε⁴)`, and its reading as the critical
exponent was not formalized. This file proves the expansion of the multipliers themselves.

For a family `P(ε) = I + εT M + ε² N + O(ε³)` of real `2 × 2` matrices with `det M = 0 > tr M` the
characteristic polynomial at `μ = 1 + ξ` is `ξ² − tr Y ξ + det Y`, `Y = P − I`, with
`tr Y = εT tr M + O(ε²)` and `det Y = ε³ T mixedDet(M, N) + O(ε⁴)`; its two roots are real and
separated (`quadratic_roots`, by sign changes and the intermediate value theorem), and
(`critical_multipliers`):

* the critical multiplier is `μ₁ = 1 + (mixedDet(M, N)/tr M) ε² + O(ε³)`;
* the other is `μ₂ = 1 + T tr M ε + O(ε²)`;
* the critical Floquet exponent is `ln μ₁ / T = λ₂ ε² + O(ε³)`, `λ₂ = mixedDet(M, N)/(T tr M)`.

For the complete two-state system `TwoToOne.full s d ω A ε` (`s > 0`, boundary
`s² + d² = |g/2|²`), where `Φ = −Φ_y`, `tr M = −2s` and `mixedDet(M, N₂) = T d |g'|²/(4ω)`
(`SecondOrder.mixedDet_secondTerm_stdForm`): `μ_c = −1 + (T d|g'|²/(8sω)) ε² + O(ε³)`,
`μ_o = −1 + 2sT ε + O(ε²)` and `λ₂ = −d |g'|²/(8sω)` (`full_critical_exponent`); the reading of
`Boundary.full_boundary_shift` (`λ₂ = −mixedDet(M, N₂)/(2sT)`) is thereby a theorem. With an added
`ε²θ I` the exponent shifts by `θ ε²` exactly (the monodromy is multiplied by `e^{ε²θT}`); this
shift is not restated here.

Scope.
* Generic: real `2 × 2` matrices with the operator `L∞` norm, families on `(0, 1]` with constants
  uniform in `ε`, `T > 0`; real quadratics `ξ² − aξ + b` with `a = αε + O(ε²)`,
  `b = βε³ + O(ε⁴)`, `α < 0`; statements for all sufficiently small `ε > 0`, constants existential.
* Two-state system: `TwoToOne.full s d ω A ε`, `s > 0`, `ω > 0`, `T = 2π/ω`, arbitrary complex
  modulation `A`, on the first-order boundary.
* Not covered here: the `n`-state Schur complement (`BlockBoundary`): there the same expansion
  with `N_eff = N + Q₁(I + E)⁻¹R₁` needs resolvent bounds inside the unit circle (those of
  `BlockBoundary.stable_block_resolvent` hold for `|μ| ≥ 1` only); it is
  `theorem/ParametricResonance/BlockCriticalExponent.lean` (`block_boundary_multipliers`,
  `block_critical_localization`, `averagingN_multipliers`, `averagingB_multipliers`).
* Generic mathematics; no model family.

Source: the wave-6 question of this library (the critical exponent left as a reading in
`theorem/ParametricResonance/BoundaryUndecided.lean`); perturbation of a simple eigenvalue of a
`2 × 2` matrix (Kato, *Perturbation Theory for Linear Operators*, Ch. II); the Floquet exponent
`ln|μ|/T` (Yakubovich–Starzhinskii, *Linear Differential Equations with Periodic Coefficients*);
`Boundary.monodromy_expansion_two`, `TwoToOne.monodromy_full`, `Periodic.mem_spectrum_iff_root`,
`BlockAveraging.exists_zero_of_mul_neg`.

Results.
* `quadratic_roots` — the two real roots `ξ₁ = (β/α)ε² + O(ε³)`, `ξ₂ = αε + O(ε²)`.
* `critical_multipliers` — the multipliers and the critical exponent of a `2 × 2` family at a
  simple critical exponent.
* `full_critical_exponent` — the two-state 2:1 system on its boundary: `μ_c`, `μ_o` and
  `λ₂ = −d|g'|²/(8sω)`.

Corrections.
None: an extension (the expansion read but not formalized in
`Boundary.full_boundary_shift`).

Family and connection conclusions.
None: static evidence on periodic linear systems.
-/

noncomputable section
namespace powerlib.ParametricResonance.CriticalExponent

open Matrix Complex Set Filter Topology
open scoped Matrix.Norms.Operator
open Boundary (secondTerm mixedDet)

/-! ## Two real roots of a perturbed quadratic -/

set_option maxHeartbeats 1000000 in
/-- **The roots of `ξ² − aξ + b` with `a = αε + O(ε²)`, `b = βε³ + O(ε⁴)`, `α < 0`.** For all
`0 < ε < ε₀` there are two distinct real roots, `ξ₁ = (β/α) ε² + O(ε³)` and `ξ₂ = αε + O(ε²)`,
with constants `K`, `ε₀` depending only on `α, β` and the error constants `c₂, c₄`. -/
@[tmio T, powerlib_foundation] theorem quadratic_roots {α β c₂ c₄ : ℝ} (hα : α < 0)
    (hc₂ : 0 ≤ c₂) (hc₄ : 0 ≤ c₄) :
    ∃ K ε₀ : ℝ, 0 ≤ K ∧ 0 < ε₀ ∧ ∀ ε a b : ℝ, 0 < ε → ε < ε₀ →
      |a - α * ε| ≤ c₂ * ε ^ 2 → |b - β * ε ^ 3| ≤ c₄ * ε ^ 4 →
      ∃ ξ₁ ξ₂ : ℝ, ξ₁ ^ 2 - a * ξ₁ + b = 0 ∧ ξ₂ ^ 2 - a * ξ₂ + b = 0 ∧ ξ₁ ≠ ξ₂ ∧
        |ξ₁ - β / α * ε ^ 2| ≤ K * ε ^ 3 ∧ |ξ₂ - α * ε| ≤ K * ε ^ 2 := by
  set γ := β / α with hγ
  have hαa : |α| = -α := abs_of_neg hα
  have hα0 : 0 < |α| := abs_pos.mpr hα.ne
  have hγα : γ * α = β := by rw [hγ, div_mul_cancel₀ β hα.ne]
  set D := γ ^ 2 + c₂ * |γ| + c₄ with hD
  have hD0 : 0 ≤ D := by positivity
  set K₁ := (D + 1) / |α| with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₁α : |α| * K₁ = D + 1 := by rw [hK₁]; field_simp
  set E := 2 * |γ| * K₁ + K₁ ^ 2 + c₂ * K₁ with hE
  have hE0 : 0 ≤ E := by positivity
  set L := (|α| * c₂ + |β| + 1) / |α| with hL
  have hL0 : 0 ≤ L := by positivity
  have hLα : |α| * L = |α| * c₂ + |β| + 1 := by rw [hL]; field_simp
  set F := L ^ 2 + L * c₂ + c₄ with hF
  have hF0 : 0 ≤ F := by positivity
  set ε₀ := min 1 (min (1 / (E + 1)) (min (1 / (F + 1)) (|α| / (L + |γ| + K₁ + 1)))) with hε₀
  have hε₀0 : 0 < ε₀ := by
    rw [hε₀]
    exact lt_min one_pos (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  refine ⟨max K₁ L, ε₀, le_max_of_le_left hK₁0, hε₀0, fun ε a b h0 hε ha hb => ?_⟩
  have hε1 : ε ≤ 1 := (hε.trans_le (min_le_left _ _)).le
  have hεE : ε * (E + 1) < 1 := by
    have := hε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    rwa [lt_div_iff₀ (by positivity)] at this
  have hεF : ε * (F + 1) < 1 := by
    have := hε.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    rwa [lt_div_iff₀ (by positivity)] at this
  have hεS : ε * (L + |γ| + K₁ + 1) < |α| := by
    have := hε.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    rwa [lt_div_iff₀ (by positivity)] at this
  set q : ℝ → ℝ := fun ξ => ξ ^ 2 - a * ξ + b with hq
  have hqc : Continuous q := by simp only [hq]; fun_prop
  set a₂ := a - α * ε with ha₂
  set b₄ := b - β * ε ^ 3 with hb₄
  have ha₂b := abs_le.mp ha
  have hb₄b := abs_le.mp hb
  have e2 : ε ^ 2 ≤ ε := by
    have := pow_le_pow_of_le_one h0.le hε1 (show 1 ≤ 2 by norm_num); simpa using this
  have e3 : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one h0.le hε1 (by norm_num)
  have e4 : ε ^ 4 ≤ ε ^ 3 := pow_le_pow_of_le_one h0.le hε1 (by norm_num)
  have e5 : ε ^ 5 ≤ ε ^ 4 := pow_le_pow_of_le_one h0.le hε1 (by norm_num)
  have e6 : ε ^ 6 ≤ ε ^ 5 := pow_le_pow_of_le_one h0.le hε1 (by norm_num)
  -- the small root: `q(γε² + η) = −αεη + R`
  have hsmall : ∀ η, |η| ≤ K₁ * ε ^ 3 →
      |q (γ * ε ^ 2 + η) - (-(α * ε * η))| ≤ D * ε ^ 4 + E * ε ^ 5 := by
    intro η hη
    have e : q (γ * ε ^ 2 + η) - (-(α * ε * η)) =
        γ ^ 2 * ε ^ 4 + 2 * (γ * ε ^ 2) * η + η ^ 2 - a₂ * (γ * ε ^ 2) + b₄ - a₂ * η := by
      simp only [hq, ha₂, hb₄]
      rw [← hγα]
      ring
    rw [e]
    have hηa : |η| ^ 2 ≤ K₁ ^ 2 * ε ^ 6 := by
      calc |η| ^ 2 ≤ (K₁ * ε ^ 3) ^ 2 := pow_le_pow_left₀ (abs_nonneg η) hη 2
        _ = K₁ ^ 2 * ε ^ 6 := by ring
    have t1 : |2 * (γ * ε ^ 2) * η| ≤ 2 * |γ| * K₁ * ε ^ 5 := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2)]
      calc 2 * (|γ| * ε ^ 2) * |η| ≤ 2 * (|γ| * ε ^ 2) * (K₁ * ε ^ 3) := by gcongr
        _ = 2 * |γ| * K₁ * ε ^ 5 := by ring
    have t2 : |a₂ * (γ * ε ^ 2)| ≤ c₂ * |γ| * ε ^ 4 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2)]
      calc |a₂| * (|γ| * ε ^ 2) ≤ c₂ * ε ^ 2 * (|γ| * ε ^ 2) := by gcongr
        _ = c₂ * |γ| * ε ^ 4 := by ring
    have t3 : |a₂ * η| ≤ c₂ * K₁ * ε ^ 5 := by
      rw [abs_mul]
      calc |a₂| * |η| ≤ c₂ * ε ^ 2 * (K₁ * ε ^ 3) := by gcongr
        _ = c₂ * K₁ * ε ^ 5 := by ring
    have t4 : |γ ^ 2 * ε ^ 4| = γ ^ 2 * ε ^ 4 := abs_of_nonneg (by positivity)
    have t5 : |η ^ 2| ≤ K₁ ^ 2 * ε ^ 5 := by
      rw [abs_pow]; exact hηa.trans (by gcongr)
    calc |γ ^ 2 * ε ^ 4 + 2 * (γ * ε ^ 2) * η + η ^ 2 - a₂ * (γ * ε ^ 2) + b₄ - a₂ * η|
        ≤ |γ ^ 2 * ε ^ 4| + |2 * (γ * ε ^ 2) * η| + |η ^ 2| + |a₂ * (γ * ε ^ 2)| + |b₄| +
          |a₂ * η| := by
          have := abs_sub (γ ^ 2 * ε ^ 4 + 2 * (γ * ε ^ 2) * η + η ^ 2 - a₂ * (γ * ε ^ 2) + b₄)
            (a₂ * η)
          have := abs_add_le (γ ^ 2 * ε ^ 4 + 2 * (γ * ε ^ 2) * η + η ^ 2 - a₂ * (γ * ε ^ 2)) b₄
          have := abs_sub (γ ^ 2 * ε ^ 4 + 2 * (γ * ε ^ 2) * η + η ^ 2) (a₂ * (γ * ε ^ 2))
          have := abs_add_le (γ ^ 2 * ε ^ 4 + 2 * (γ * ε ^ 2) * η) (η ^ 2)
          have := abs_add_le (γ ^ 2 * ε ^ 4) (2 * (γ * ε ^ 2) * η)
          linarith
      _ ≤ γ ^ 2 * ε ^ 4 + 2 * |γ| * K₁ * ε ^ 5 + K₁ ^ 2 * ε ^ 5 + c₂ * |γ| * ε ^ 4 +
          c₄ * ε ^ 4 + c₂ * K₁ * ε ^ 5 := by
          rw [t4]; have := hb; linarith
      _ = D * ε ^ 4 + E * ε ^ 5 := by rw [hD, hE]; ring
  -- the large root: `q(αε + η) = αεη + R'`
  have hlarge : ∀ η, |η| ≤ L * ε ^ 2 →
      |q (α * ε + η) - α * ε * η| ≤ (|α| * c₂ + |β|) * ε ^ 3 + F * ε ^ 4 := by
    intro η hη
    have e : q (α * ε + η) - α * ε * η =
        -(α * ε * a₂) + η ^ 2 - η * a₂ + β * ε ^ 3 + b₄ := by
      simp only [hq, ha₂, hb₄]; ring
    rw [e]
    have t1 : |α * ε * a₂| ≤ |α| * c₂ * ε ^ 3 := by
      rw [abs_mul, abs_mul, abs_of_pos h0]
      calc |α| * ε * |a₂| ≤ |α| * ε * (c₂ * ε ^ 2) := by gcongr
        _ = |α| * c₂ * ε ^ 3 := by ring
    have t2 : |η ^ 2| ≤ L ^ 2 * ε ^ 4 := by
      rw [abs_pow]
      calc |η| ^ 2 ≤ (L * ε ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg η) hη 2
        _ = L ^ 2 * ε ^ 4 := by ring
    have t3 : |η * a₂| ≤ L * c₂ * ε ^ 4 := by
      rw [abs_mul]
      calc |η| * |a₂| ≤ L * ε ^ 2 * (c₂ * ε ^ 2) := by gcongr
        _ = L * c₂ * ε ^ 4 := by ring
    have t4 : |β * ε ^ 3| = |β| * ε ^ 3 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 3)]
    calc |-(α * ε * a₂) + η ^ 2 - η * a₂ + β * ε ^ 3 + b₄|
        ≤ |α * ε * a₂| + |η ^ 2| + |η * a₂| + |β * ε ^ 3| + |b₄| := by
          have := abs_add_le (-(α * ε * a₂) + η ^ 2 - η * a₂ + β * ε ^ 3) b₄
          have := abs_add_le (-(α * ε * a₂) + η ^ 2 - η * a₂) (β * ε ^ 3)
          have := abs_sub (-(α * ε * a₂) + η ^ 2) (η * a₂)
          have := abs_add_le (-(α * ε * a₂)) (η ^ 2)
          have := abs_neg (α * ε * a₂)
          linarith
      _ ≤ |α| * c₂ * ε ^ 3 + L ^ 2 * ε ^ 4 + L * c₂ * ε ^ 4 + |β| * ε ^ 3 + c₄ * ε ^ 4 := by
          rw [t4]; linarith
      _ = (|α| * c₂ + |β|) * ε ^ 3 + F * ε ^ 4 := by rw [hF]; ring
  -- sign changes and the intermediate value theorem
  have hs1 := hsmall (K₁ * ε ^ 3) (by rw [abs_of_nonneg (by positivity)])
  have hs2 := hsmall (-(K₁ * ε ^ 3)) (by rw [abs_neg, abs_of_nonneg (by positivity)])
  have hl1 := hlarge (L * ε ^ 2) (by rw [abs_of_nonneg (by positivity)])
  have hl2 := hlarge (-(L * ε ^ 2)) (by rw [abs_neg, abs_of_nonneg (by positivity)])
  have hε4 : 0 < ε ^ 4 := by positivity
  have hε3 : 0 < ε ^ 3 := by positivity
  have hEε : E * ε ^ 5 < ε ^ 4 := by
    have : E * ε < 1 := by
      have e : E * ε = ε * (E + 1) - ε := by ring
      linarith
    calc E * ε ^ 5 = (E * ε) * ε ^ 4 := by ring
      _ < 1 * ε ^ 4 := by gcongr
      _ = ε ^ 4 := one_mul _
  have hFε : F * ε ^ 4 < ε ^ 3 := by
    have : F * ε < 1 := by
      have e : F * ε = ε * (F + 1) - ε := by ring
      linarith
    calc F * ε ^ 4 = (F * ε) * ε ^ 3 := by ring
      _ < 1 * ε ^ 3 := by gcongr
      _ = ε ^ 3 := one_mul _
  have hq1 : 0 < q (γ * ε ^ 2 + K₁ * ε ^ 3) := by
    have h1 := (abs_le.mp hs1).1
    have : -(α * ε * (K₁ * ε ^ 3)) = (D + 1) * ε ^ 4 := by rw [← hK₁α, hαa]; ring
    linarith
  have hq2 : q (γ * ε ^ 2 + -(K₁ * ε ^ 3)) < 0 := by
    have h1 := (abs_le.mp hs2).2
    have : -(α * ε * -(K₁ * ε ^ 3)) = -((D + 1) * ε ^ 4) := by rw [← hK₁α, hαa]; ring
    linarith
  have hq3 : q (α * ε + L * ε ^ 2) < 0 := by
    have h1 := (abs_le.mp hl1).2
    have : α * ε * (L * ε ^ 2) = -((|α| * c₂ + |β| + 1) * ε ^ 3) := by rw [← hLα, hαa]; ring
    linarith
  have hq4 : 0 < q (α * ε + -(L * ε ^ 2)) := by
    have h1 := (abs_le.mp hl2).1
    have : α * ε * -(L * ε ^ 2) = (|α| * c₂ + |β| + 1) * ε ^ 3 := by rw [← hLα, hαa]; ring
    linarith
  obtain ⟨ξ₁, hξ₁, hq₁⟩ := BlockAveraging.exists_zero_of_mul_neg
    (show γ * ε ^ 2 + -(K₁ * ε ^ 3) ≤ γ * ε ^ 2 + K₁ * ε ^ 3 by
      have := mul_nonneg hK₁0 hε3.le; linarith)
    hqc.continuousOn (mul_neg_of_neg_of_pos hq2 hq1)
  obtain ⟨ξ₂, hξ₂, hq₂⟩ := BlockAveraging.exists_zero_of_mul_neg
    (show α * ε + -(L * ε ^ 2) ≤ α * ε + L * ε ^ 2 by
      have := mul_nonneg hL0 (sq_nonneg ε); linarith)
    hqc.continuousOn (mul_neg_of_pos_of_neg hq4 hq3)
  have hb1 : |ξ₁ - γ * ε ^ 2| ≤ K₁ * ε ^ 3 := by
    rw [abs_le]; constructor <;> linarith [hξ₁.1, hξ₁.2]
  have hb2 : |ξ₂ - α * ε| ≤ L * ε ^ 2 := by
    rw [abs_le]; constructor <;> linarith [hξ₂.1, hξ₂.2]
  refine ⟨ξ₁, ξ₂, hq₁, hq₂, ?_, hb1.trans (by gcongr; exact le_max_left _ _),
    hb2.trans (by gcongr; exact le_max_right _ _)⟩
  -- the two windows are disjoint
  intro heq
  have hγ2 : -(|γ| * ε ^ 2) ≤ γ * ε ^ 2 := by
    have := neg_abs_le γ
    have : -|γ| * ε ^ 2 ≤ γ * ε ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
    linarith
  have h1 : -(|γ| * ε ^ 2) - K₁ * ε ^ 3 ≤ ξ₁ := by linarith [hξ₁.1]
  have h2 : ξ₂ ≤ α * ε + L * ε ^ 2 := hξ₂.2
  rw [heq] at h1
  have h3 : K₁ * ε ^ 3 ≤ K₁ * ε ^ 2 := mul_le_mul_of_nonneg_left e3 hK₁0
  have h4 : |α| * ε ≤ (L + |γ| + K₁) * ε * ε := by
    rw [hαa]
    have e : (L + |γ| + K₁) * ε * ε = L * ε ^ 2 + |γ| * ε ^ 2 + K₁ * ε ^ 2 := by ring
    rw [e]
    linarith
  have h5 : |α| ≤ (L + |γ| + K₁) * ε := le_of_mul_le_mul_right h4 h0
  have e : ε * (L + |γ| + K₁ + 1) = (L + |γ| + K₁) * ε + ε := by ring
  linarith


/-! ## The multipliers of a `2 × 2` family at a simple critical exponent -/

@[tmio T, powerlib_foundation] private theorem abs_det_le₃ (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    |Z.det| ≤ 2 * ‖Z‖ ^ 2 := by
  rw [Matrix.det_fin_two]
  have h : ∀ i j k l, |Z i j * Z k l| ≤ ‖Z‖ ^ 2 := fun i j k l => by
    rw [abs_mul, sq]
    exact mul_le_mul (Averaging.entry_le_norm Z i j) (Averaging.entry_le_norm Z k l)
      (abs_nonneg _) (norm_nonneg _)
  calc |Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0| ≤ |Z 0 0 * Z 1 1| + |Z 0 1 * Z 1 0| := abs_sub _ _
    _ ≤ 2 * ‖Z‖ ^ 2 := by linarith [h 0 0 1 1, h 0 1 1 0]

@[tmio T, powerlib_foundation] private theorem abs_trace_le₃ (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    |Z.trace| ≤ 2 * ‖Z‖ := by
  rw [Matrix.trace_fin_two]
  have h0 := Averaging.entry_le_norm Z 0 0
  have h1 := Averaging.entry_le_norm Z 1 1
  calc |Z 0 0 + Z 1 1| ≤ |Z 0 0| + |Z 1 1| := abs_add_le _ _
    _ ≤ 2 * ‖Z‖ := by linarith

@[tmio T, powerlib_foundation] private theorem abs_mixedDet_le₃ (M Z : Matrix (Fin 2) (Fin 2) ℝ) :
    |mixedDet M Z| ≤ 4 * (‖M‖ * ‖Z‖) := by
  have e : mixedDet M Z = M 0 0 * Z 1 1 + M 1 1 * Z 0 0 - M 0 1 * Z 1 0 - M 1 0 * Z 0 1 := by
    simp [mixedDet, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have h : ∀ i j k l, |M i j * Z k l| ≤ ‖M‖ * ‖Z‖ := fun i j k l => by
    rw [abs_mul]
    exact mul_le_mul (Averaging.entry_le_norm M i j) (Averaging.entry_le_norm Z k l)
      (abs_nonneg _) (norm_nonneg _)
  rw [e]
  have a1 := abs_le.mp (h 0 0 1 1)
  have a2 := abs_le.mp (h 1 1 0 0)
  have a3 := abs_le.mp (h 0 1 1 0)
  have a4 := abs_le.mp (h 1 0 0 1)
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]

/-- `|log(1 + ξ) − ξ| ≤ 2ξ²` for `|ξ| ≤ 1/2`. -/
@[tmio T, powerlib_foundation] private theorem abs_log_one_add_sub_le {ξ : ℝ} (h : |ξ| ≤ 1 / 2) :
    |Real.log (1 + ξ) - ξ| ≤ 2 * ξ ^ 2 := by
  have hb := abs_le.mp h
  have hpos : 0 < 1 + ξ := by linarith
  have h1 := Real.log_le_sub_one_of_pos hpos
  have h2 := Real.one_sub_inv_le_log_of_pos hpos
  have h3 : 1 - (1 + ξ)⁻¹ - ξ = -(ξ ^ 2 / (1 + ξ)) := by field_simp; ring
  have h4 : ξ ^ 2 / (1 + ξ) ≤ 2 * ξ ^ 2 := by
    rw [div_le_iff₀ hpos]; nlinarith [sq_nonneg ξ]
  rw [abs_le]; constructor <;> linarith

/-- **The multipliers at a simple critical exponent, to second order.** Let a family of real
`2 × 2` matrices satisfy `P(ε) = I + εT M + ε² N + O(ε³)` (`‖·‖ ≤ Cε³` on `(0, 1]`, `T > 0`) with
`det M = 0 > tr M`. Then for all small `ε > 0` the two multipliers are real and distinct, and
* the critical one is `μ₁ = 1 + (mixedDet(M, N)/tr M) ε² + O(ε³)`,
* the other is `μ₂ = 1 + T tr M ε + O(ε²)`,
* the critical Floquet exponent is `ln μ₁ / T = λ₂ ε² + O(ε³)` with
  `λ₂ = mixedDet(M, N)/(T tr M)`,
with one constant `K` (`det(P − I) = (μ₁ − 1)(μ₂ − 1)`, `tr(P − I) = (μ₁ − 1) + (μ₂ − 1)`; the sign
statement is `Boundary.critical_jury`). -/
@[tmio T, powerlib_foundation] theorem critical_multipliers {P : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {M N : Matrix (Fin 2) (Fin 2) ℝ} {T C : ℝ} (hT : 0 < T) (hC : 0 ≤ C)
    (hP : ∀ ε, 0 < ε → ε ≤ 1 → ‖P ε - 1 - (ε * T) • M - ε ^ 2 • N‖ ≤ C * ε ^ 3)
    (hdet : M.det = 0) (htr : M.trace < 0) :
    ∃ K, 0 ≤ K ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ μ₁ μ₂ : ℝ,
      (μ₁ : ℂ) ∈ spectrum ℂ ((P ε).map (algebraMap ℝ ℂ)) ∧
      (μ₂ : ℂ) ∈ spectrum ℂ ((P ε).map (algebraMap ℝ ℂ)) ∧ μ₁ ≠ μ₂ ∧
      (∀ μ ∈ spectrum ℂ ((P ε).map (algebraMap ℝ ℂ)), μ = μ₁ ∨ μ = μ₂) ∧
      |μ₁ - (1 + mixedDet M N / M.trace * ε ^ 2)| ≤ K * ε ^ 3 ∧
      |μ₂ - (1 + T * M.trace * ε)| ≤ K * ε ^ 2 ∧
      |Real.log μ₁ / T - mixedDet M N / (T * M.trace) * ε ^ 2| ≤ K * ε ^ 3 := by
  set τ := M.trace with hτ
  set m := mixedDet M N with hm
  set c₂ := 2 * ‖N‖ + 2 * C with hc₂
  set c₄ := 2 * (‖N‖ + C) ^ 2 + 4 * T * ‖M‖ * C with hc₄
  have hα : T * τ < 0 := mul_neg_of_pos_of_neg hT htr
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hc₄0 : 0 ≤ c₄ := by positivity
  obtain ⟨K₀, ε₀, hK₀, hε₀, hroots⟩ := quadratic_roots (β := T * m) (c₂ := c₂) (c₄ := c₄) hα
    hc₂0 hc₄0
  have hγ : T * m / (T * τ) = m / τ := by rw [mul_div_mul_left _ _ hT.ne']
  set G := |m / τ| + K₀ with hG
  have hG0 : 0 ≤ G := by positivity
  refine ⟨max K₀ ((2 * G ^ 2 + K₀) / T), le_max_of_le_left hK₀, ?_⟩
  have hδ : 0 < min ε₀ (min 1 (1 / (2 * G + 1))) := lt_min hε₀ (lt_min one_pos (by positivity))
  filter_upwards [BlockAveraging.eventually_lt_nhdsGT hδ] with ε ⟨h0, hε⟩
  have hεε₀ : ε < ε₀ := hε.trans_le (min_le_left _ _)
  have hε1 : ε ≤ 1 := (hε.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hεG : ε * (2 * G + 1) < 1 := by
    have := hε.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    rwa [lt_div_iff₀ (by positivity)] at this
  -- the deviation `Y = P − I`
  set Y := P ε - 1 with hY
  set R := P ε - 1 - (ε * T) • M - ε ^ 2 • N with hR
  have hRb : ‖R‖ ≤ C * ε ^ 3 := hP ε h0 hε1
  have e2 : ε ^ 2 ≤ ε := by
    have := pow_le_pow_of_le_one h0.le hε1 (show 1 ≤ 2 by norm_num); simpa using this
  have e3 : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one h0.le hε1 (by norm_num)
  have e4 : ε ^ 4 ≤ ε ^ 3 := pow_le_pow_of_le_one h0.le hε1 (by norm_num)
  have hYe : Y = (ε * T) • M + (ε ^ 2 • N + R) := by rw [hY, hR]; abel
  have htrY : |Y.trace - T * τ * ε| ≤ c₂ * ε ^ 2 := by
    rw [hYe, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      smul_eq_mul, smul_eq_mul]
    have e : ε * T * τ + (ε ^ 2 * N.trace + R.trace) - T * τ * ε = ε ^ 2 * N.trace + R.trace := by
      ring
    rw [e]
    have tN := abs_trace_le₃ N
    have tR := abs_trace_le₃ R
    calc |ε ^ 2 * N.trace + R.trace| ≤ |ε ^ 2 * N.trace| + |R.trace| := abs_add_le _ _
      _ = ε ^ 2 * |N.trace| + |R.trace| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2)]
      _ ≤ ε ^ 2 * (2 * ‖N‖) + 2 * (C * ε ^ 2) := by
          have : |R.trace| ≤ 2 * (C * ε ^ 2) :=
            tR.trans (by gcongr; exact hRb.trans (mul_le_mul_of_nonneg_left e3 hC))
          have : ε ^ 2 * |N.trace| ≤ ε ^ 2 * (2 * ‖N‖) := by gcongr
          linarith
      _ = c₂ * ε ^ 2 := by rw [hc₂]; ring
  have hdetY : |Y.det - T * m * ε ^ 3| ≤ c₄ * ε ^ 4 := by
    set Z := ε ^ 2 • N + R with hZ
    have e : Y.det - T * m * ε ^ 3 = Z.det + ε * T * mixedDet M R := by
      rw [hYe]
      have hd := hdet
      simp only [Matrix.det_fin_two, mixedDet, Matrix.trace_fin_two, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hm, hZ] at hd ⊢
      linear_combination (ε * T) ^ 2 * hd
    rw [e]
    have hZb : ‖Z‖ ≤ (‖N‖ + C) * ε ^ 2 := by
      calc ‖Z‖ ≤ ‖ε ^ 2 • N‖ + ‖R‖ := norm_add_le _ _
        _ = ε ^ 2 * ‖N‖ + ‖R‖ := by rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        _ ≤ ε ^ 2 * ‖N‖ + C * ε ^ 2 := by
            gcongr; exact hRb.trans (mul_le_mul_of_nonneg_left e3 hC)
        _ = (‖N‖ + C) * ε ^ 2 := by ring
    have h1 : |Z.det| ≤ 2 * (‖N‖ + C) ^ 2 * ε ^ 4 := by
      calc |Z.det| ≤ 2 * ‖Z‖ ^ 2 := abs_det_le₃ Z
        _ ≤ 2 * ((‖N‖ + C) * ε ^ 2) ^ 2 := by gcongr
        _ = 2 * (‖N‖ + C) ^ 2 * ε ^ 4 := by ring
    have h2 : |ε * T * mixedDet M R| ≤ 4 * T * ‖M‖ * C * ε ^ 4 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε * T)]
      calc ε * T * |mixedDet M R| ≤ ε * T * (4 * (‖M‖ * (C * ε ^ 3))) := by
            gcongr; exact (abs_mixedDet_le₃ M R).trans (by gcongr)
        _ = 4 * T * ‖M‖ * C * ε ^ 4 := by ring
    calc |Z.det + ε * T * mixedDet M R| ≤ |Z.det| + |ε * T * mixedDet M R| := abs_add_le _ _
      _ ≤ _ := by rw [hc₄]; linarith
  have htrY' : |Y.trace - T * τ * ε| ≤ c₂ * ε ^ 2 := htrY
  obtain ⟨ξ₁, ξ₂, hq1, hq2, hne, hb1, hb2⟩ := hroots ε Y.trace Y.det h0 hεε₀ htrY' hdetY
  rw [hγ] at hb1
  -- the characteristic polynomial of `P = I + Y`
  have htrP : (P ε).trace = 2 + Y.trace := by
    rw [hY, Matrix.trace_sub, Matrix.trace_one]; simp
  have hdetP : (P ε).det = 1 + Y.trace + Y.det := by
    have h := Boundary.det_add_fin_two 1 Y
    rw [hY, add_sub_cancel, Matrix.det_one] at h
    rw [h, ← hY]
    simp [mixedDet, Matrix.trace_fin_two]
    ring
  have hroot : ∀ ξ : ℝ, ξ ^ 2 - Y.trace * ξ + Y.det = 0 →
      ((1 + ξ : ℝ) : ℂ) ∈ spectrum ℂ ((P ε).map (algebraMap ℝ ℂ)) := by
    intro ξ hξ
    rw [Periodic.mem_spectrum_iff_root, htrP, hdetP]
    have : (1 + ξ) ^ 2 - (2 + Y.trace) * (1 + ξ) + (1 + Y.trace + Y.det) = 0 := by
      linear_combination hξ
    exact_mod_cast this
  -- Vieta
  have hsum : Y.trace = ξ₁ + ξ₂ := by
    have h := sub_eq_zero.mpr (hq1.trans hq2.symm)
    have : (ξ₁ - ξ₂) * (ξ₁ + ξ₂ - Y.trace) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h') hne
    · linarith
  have hprod : Y.det = ξ₁ * ξ₂ := by
    have := hq1; rw [hsum] at this; linarith
  refine ⟨1 + ξ₁, 1 + ξ₂, hroot ξ₁ hq1, hroot ξ₂ hq2, fun h => hne (by linarith), ?_, ?_, ?_, ?_⟩
  · intro μ hμ
    rw [Periodic.mem_spectrum_iff_root, htrP, hdetP, hsum, hprod] at hμ
    have : (μ - ((1 + ξ₁ : ℝ) : ℂ)) * (μ - ((1 + ξ₂ : ℝ) : ℂ)) = 0 := by
      push_cast at hμ ⊢; linear_combination hμ
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  · have e : 1 + ξ₁ - (1 + m / τ * ε ^ 2) = ξ₁ - m / τ * ε ^ 2 := by ring
    rw [e]; exact hb1.trans (by gcongr; exact le_max_left _ _)
  · have e : 1 + ξ₂ - (1 + T * τ * ε) = ξ₂ - T * τ * ε := by ring
    rw [e]; exact hb2.trans (by gcongr; exact le_max_left _ _)
  · -- the exponent
    have hξ₁ : |ξ₁| ≤ G * ε ^ 2 := by
      have h1 : |ξ₁| ≤ |m / τ * ε ^ 2| + |ξ₁ - m / τ * ε ^ 2| := by
        have := abs_add_le (m / τ * ε ^ 2) (ξ₁ - m / τ * ε ^ 2); simpa using this
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2)] at h1
      have : K₀ * ε ^ 3 ≤ K₀ * ε ^ 2 := mul_le_mul_of_nonneg_left e3 hK₀
      rw [hG]; linarith
    have hhalf : |ξ₁| ≤ 1 / 2 := by
      have : G * ε ^ 2 ≤ G * ε := mul_le_mul_of_nonneg_left e2 hG0
      have : G * ε < 1 / 2 := by
        have e : ε * (2 * G + 1) = 2 * (G * ε) + ε := by ring
        linarith
      linarith
    have hlog := abs_log_one_add_sub_le hhalf
    have hξsq : 2 * ξ₁ ^ 2 ≤ 2 * G ^ 2 * ε ^ 3 := by
      have h1 : ξ₁ ^ 2 ≤ (G * ε ^ 2) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hξ₁ 2
      have e : (G * ε ^ 2) ^ 2 = G ^ 2 * ε ^ 4 := by ring
      have h2 : G ^ 2 * ε ^ 4 ≤ G ^ 2 * ε ^ 3 := mul_le_mul_of_nonneg_left e4 (sq_nonneg G)
      rw [e] at h1
      linarith
    have hτT : m / (T * τ) * ε ^ 2 = (m / τ * ε ^ 2) / T := by
      field_simp
    rw [hτT, ← sub_div, abs_div, abs_of_pos hT, div_le_iff₀ hT]
    have e : Real.log (1 + ξ₁) - m / τ * ε ^ 2 =
        (Real.log (1 + ξ₁) - ξ₁) + (ξ₁ - m / τ * ε ^ 2) := by ring
    rw [e]
    calc |(Real.log (1 + ξ₁) - ξ₁) + (ξ₁ - m / τ * ε ^ 2)|
        ≤ |Real.log (1 + ξ₁) - ξ₁| + |ξ₁ - m / τ * ε ^ 2| := abs_add_le _ _
      _ ≤ 2 * G ^ 2 * ε ^ 3 + K₀ * ε ^ 3 := by linarith
      _ = (2 * G ^ 2 + K₀) / T * ε ^ 3 * T := by field_simp
      _ ≤ max K₀ ((2 * G ^ 2 + K₀) / T) * ε ^ 3 * T := by gcongr; exact le_max_right _ _

/-! ## The complete two-state system on its first-order boundary -/

section Full

open TwoToOne (full stdForm left right)
open SecondOrder (antiPump)

@[tmio T, powerlib_foundation] private theorem mem_spectrum_neg_iff
    {P : Matrix (Fin 2) (Fin 2) ℝ} {μ : ℂ} :
    μ ∈ spectrum ℂ ((-P).map (algebraMap ℝ ℂ)) ↔ -μ ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ)) := by
  have key : ∀ (Q : Matrix (Fin 2) (Fin 2) ℝ) (ν : ℂ), ν ∈ spectrum ℂ (Q.map (algebraMap ℝ ℂ)) →
      -ν ∈ spectrum ℂ ((-Q).map (algebraMap ℝ ℂ)) := by
    intro Q ν h
    obtain ⟨v, hv, hQv⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp h
    refine LTI.mem_spectrum_iff_exists_eigvec.mpr ⟨v, hv, ?_⟩
    rw [Matrix.map_neg _ (fun a => map_neg (algebraMap ℝ ℂ) a), Matrix.neg_mulVec, hQv, neg_smul]
  constructor
  · intro h
    have := key (-P) μ h
    rwa [neg_neg] at this
  · intro h
    have := key P (-μ) h
    rwa [neg_neg] at this

/-- **The critical Floquet multiplier and exponent of the damped two-state system on its
boundary.** For `TwoToOne.full s d ω A ε` with `s > 0` on the first-order boundary
`s² + d² = |g/2|²` (`T = 2π/ω`, `g' = SecondOrder.antiPump A`), for all small `ε > 0` the two
Floquet multipliers are real and distinct:
* the critical one `μ_c = −1 + (T d |g'|²/(8sω)) ε² + O(ε³)`,
* the other `μ_o = −1 + 2sT ε + O(ε²)` (the damped slow exponent `−2s`),
and the critical Floquet exponent is `ln(−μ_c)/T = λ₂ ε² + O(ε³)` with
`λ₂ = −d |g'|²/(8sω)` (`critical_multipliers` with `mixedDet(M, N₂) = T d|g'|²/(4ω)`,
`SecondOrder.mixedDet_secondTerm_stdForm`, and `tr M = −2s`). The sign of `λ₂` is the verdict of
`SecondOrder.full_boundary_closed_form`. -/
@[tmio T, powerlib_foundation] theorem full_critical_exponent {s d ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hs : 0 < s)
    (hb : s ^ 2 + d ^ 2 = ‖Element.pump A left right / 2‖ ^ 2) :
    ∃ K, 0 ≤ K ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ μc μo : ℝ,
      (μc : ℂ) ∈ spectrum ℂ ((Periodic.monodromy (full s d ω A ε) (2 * Real.pi / ω) 0).map
        (algebraMap ℝ ℂ)) ∧
      (μo : ℂ) ∈ spectrum ℂ ((Periodic.monodromy (full s d ω A ε) (2 * Real.pi / ω) 0).map
        (algebraMap ℝ ℂ)) ∧
      (∀ μ ∈ spectrum ℂ ((Periodic.monodromy (full s d ω A ε) (2 * Real.pi / ω) 0).map
        (algebraMap ℝ ℂ)), μ = μc ∨ μ = μo) ∧
      |μc - (-1 + 2 * Real.pi / ω * d * ‖antiPump A‖ ^ 2 / (8 * s * ω) * ε ^ 2)| ≤ K * ε ^ 3 ∧
      |μo - (-1 + 2 * s * (2 * Real.pi / ω) * ε)| ≤ K * ε ^ 2 ∧
      |Real.log (-μc) / (2 * Real.pi / ω) - -(d * ‖antiPump A‖ ^ 2 / (8 * s * ω)) * ε ^ 2| ≤
        K * ε ^ 3 := by
  set T := 2 * Real.pi / ω with hTdef
  have hT : 0 < T := by positivity
  set M := slowFlowMatrix s d (Element.pump A left right / 2) with hM
  set F := stdForm s d ω A with hF
  obtain ⟨MF, hMF0, hMF⟩ := TwoToOne.exists_bound_stdForm s d hω A
  set C := MF * T * (MF * T * (MF * T * (‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ *
    Real.exp (MF * T)))) with hC
  have hC0 : 0 ≤ C := by positivity
  have hexp : ∀ ε, 0 < ε → ε ≤ 1 → ‖Periodic.monodromy (fun t => ε • F t) T 0 - 1 -
      (ε * T) • M - ε ^ 2 • secondTerm F T‖ ≤ C * ε ^ 3 := fun ε h0 h1 => by
    have h := Boundary.monodromy_expansion_two (TwoToOne.continuous_stdForm s d ω A) hMF hMF0
      hT.le (TwoToOne.integral_stdForm s d hω A) h0.le h1
    rw [← hC] at h
    exact h.trans (le_of_eq (mul_comm _ _))
  have hdet : M.det = 0 := by rw [hM, det_slowFlowMatrix, ← hb]; ring
  have htrM : M.trace = -2 * s := trace_slowFlowMatrix s d _
  have htr : M.trace < 0 := by rw [htrM]; linarith
  have hmix : mixedDet M (secondTerm F T) = T * d * ‖antiPump A‖ ^ 2 / (4 * ω) := by
    rw [hM, hF, SecondOrder.mixedDet_secondTerm_stdForm s d hω A, ← hb]; ring
  obtain ⟨K, hK, hev⟩ := critical_multipliers (P := fun ε => Periodic.monodromy
    (fun t => ε • F t) T 0) hT hC0 hexp hdet htr
  refine ⟨K, hK, ?_⟩
  filter_upwards [hev] with ε ⟨μ₁, μ₂, h1, h2, hne, hall, hb1, hb2, hlog⟩
  have hmono : Periodic.monodromy (full s d ω A ε) T 0 =
      -Periodic.monodromy (fun t => ε • F t) T 0 := TwoToOne.monodromy_full s d hω A ε
  rw [hmix, htrM] at hb1 hlog
  rw [htrM] at hb2
  refine ⟨-μ₁, -μ₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmono, mem_spectrum_neg_iff]; push_cast; rw [neg_neg]; exact h1
  · rw [hmono, mem_spectrum_neg_iff]; push_cast; rw [neg_neg]; exact h2
  · intro μ hμ
    rw [hmono, mem_spectrum_neg_iff] at hμ
    rcases hall _ hμ with h | h
    · left; push_cast; rw [← h, neg_neg]
    · right; push_cast; rw [← h, neg_neg]
  · have e : -μ₁ - (-1 + T * d * ‖antiPump A‖ ^ 2 / (8 * s * ω) * ε ^ 2) =
        -(μ₁ - (1 + T * d * ‖antiPump A‖ ^ 2 / (4 * ω) / (-2 * s) * ε ^ 2)) := by
      field_simp; ring
    rw [e, abs_neg]; exact hb1
  · have e : -μ₂ - (-1 + 2 * s * T * ε) = -(μ₂ - (1 + T * (-2 * s) * ε)) := by ring
    rw [e, abs_neg]; exact hb2
  · have e : -(d * ‖antiPump A‖ ^ 2 / (8 * s * ω)) =
        T * d * ‖antiPump A‖ ^ 2 / (4 * ω) / (T * (-2 * s)) := by
      field_simp; ring
    rw [neg_neg, e]; exact hlog

end Full

end powerlib.ParametricResonance.CriticalExponent
