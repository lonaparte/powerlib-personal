import theorem.Periodic.Transition

/-! # Time shifts of a periodic linear system and Floquet exponents

A time shift does not change the Floquet multipliers, and Floquet exponents are determined by
the multipliers up to harmonic aliases.

Scope.
* `ẋ = A(t) x` with continuous, uniformly bounded `A` (sup norm), as in
  `Periodic/Transition.lean`.

Source: work-sync theory/T-harmonic-linearization.md §1.6 (`ρ_i = λ_i(Φ(T, 0))`,
`|ρ_i| < 1 ⇔ Re μ_i < 0`, `μ_i` unique modulo `jω_s`);
projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/gfl-gfm-parametric-contrast.md
§11 (half-period symmetry; used by `ParametricResonance/HalfPeriod.lean`).

Results.
* `transition_shift` — for the time-shifted matrix `A_c(t) = A(t + c)`,
  `Φ_c(t, s) = Φ(t + c, s + c)` (`s ≤ t`); `monodromy_shift`: `M_{A_c}(s) = M_A(s + c)`.
* `spectrum_monodromy_shift` — for a `T`-periodic `A` the Floquet multipliers of `A_c` and `A`
  coincide, for every shift `c` (the monodromy matrix from a shifted start is similar).
* `exp_floquetExponent`, `norm_lt_one_iff_re_neg`, `exp_alias` — Floquet exponents: for a
  multiplier `ρ ≠ 0` and `T > 0`, `μ = log ρ / T` satisfies `e^{μT} = ρ`, `|ρ| < 1 ↔ Re μ < 0`,
  and the harmonic aliases `μ + jkω_s` (`ω_s T = 2π`, `k ∈ ℤ`) give the same multiplier; hence
  only `Re μ` matters for stability.
-/

noncomputable section
namespace powerlib.Periodic

open Set Matrix Function
open scoped Matrix.Norms.Operator

variable {X : Type*} [Fintype X] [DecidableEq X] {A : ℝ → Matrix X X ℝ} {M : ℝ}

/-- Transition matrix of the time-shifted system `A_c(t) = A(t + c)`. -/
@[powerlib_foundation] theorem transition_shift (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    (c : ℝ) {s t : ℝ} (hst : s ≤ t) :
    transition (fun r => A (r + c)) t s = transition A (t + c) (s + c) := by
  have hAc : Continuous fun r => A (r + c) := hA.comp (continuous_id.add continuous_const)
  have hMc : ∀ r, ‖(fun r => A (r + c)) r‖ ≤ M := fun r => hM (r + c)
  obtain ⟨h1, hΦ⟩ := transition_spec hA hM (s + c)
  have hY : IsIntegralCurveOn (fun r => transition A (r + c) (s + c))
      (matField fun r => A (r + c)) (Ici s) := by
    intro r hr
    have hmaps : MapsTo (fun r : ℝ => r + c) (Ici s) (Ici (s + c)) :=
      fun x hx => by simpa using add_le_add_right (show s ≤ x from hx) c
    have h := HasDerivWithinAt.scomp r (hΦ (r + c) (hmaps hr))
      ((hasDerivAt_id' r).hasDerivWithinAt.add_const c) hmaps
    simpa only [matField, Function.comp_def, one_smul] using h
  have := transition_unique hAc hMc hY t hst
  simpa [h1] using this.symm

/-- `M_{A_c}(s) = M_A(s + c)`. -/
@[powerlib_foundation] theorem monodromy_shift (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)
    (c : ℝ) {T : ℝ} (hT : 0 ≤ T) (s : ℝ) :
    monodromy (fun r => A (r + c)) T s = monodromy A T (s + c) := by
  rw [monodromy, monodromy, transition_shift hA hM c (by linarith)]
  congr 1; ring

/-- A time shift does not change the Floquet multipliers of a periodic system. -/
@[powerlib_foundation] theorem spectrum_monodromy_shift (hA : Continuous A)
    (hM : ∀ t, ‖A t‖ ≤ M) {T : ℝ} (hT : 0 ≤ T) (hP : Periodic A T) (c : ℝ) :
    spectrum ℂ ((monodromy (fun r => A (r + c)) T 0).map (algebraMap ℝ ℂ)) =
      spectrum ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ)) := by
  rw [monodromy_shift hA hM c hT 0, zero_add, spectrum_monodromy hA hM hT hP c]

/-! ## Floquet exponents -/

/-- `e^{μT} = ρ` for `μ = log ρ / T` (`ρ ≠ 0`, `T ≠ 0`). -/
@[powerlib_foundation] theorem exp_floquetExponent {ρ : ℂ} (hρ : ρ ≠ 0) {T : ℝ} (hT : T ≠ 0) :
    Complex.exp (Complex.log ρ / T * T) = ρ := by
  rw [div_mul_cancel₀ _ (by exact_mod_cast hT), Complex.exp_log hρ]

/-- `|ρ| < 1 ↔ Re μ < 0` for the exponent `μ = log ρ / T`, `T > 0`. -/
@[powerlib_foundation] theorem norm_lt_one_iff_re_neg {ρ : ℂ} (hρ : ρ ≠ 0) {T : ℝ} (hT : 0 < T) :
    ‖ρ‖ < 1 ↔ (Complex.log ρ / T).re < 0 := by
  rw [show (Complex.log ρ / T).re = (Complex.log ρ).re / T by
    rw [Complex.div_ofReal_re], Complex.log_re, div_neg_iff]
  constructor
  · intro h
    right
    exact ⟨Real.log_neg (norm_pos_iff.mpr hρ) h, hT⟩
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · linarith
    · exact (Real.log_neg_iff (norm_pos_iff.mpr hρ)).mp h

/-- Harmonic aliases `μ + jkω_s` (`ω_s T = 2π`) give the same Floquet multiplier. -/
@[powerlib_foundation] theorem exp_alias (μ : ℂ) {ωs T : ℝ} (hT : ωs * T = 2 * Real.pi) (k : ℤ) :
    Complex.exp ((μ + k * ωs * Complex.I) * T) = Complex.exp (μ * T) := by
  have hT' : (ωs : ℂ) * T = 2 * Real.pi := by exact_mod_cast hT
  rw [show (μ + k * ωs * Complex.I) * T = μ * T + k * (2 * Real.pi * Complex.I) by
    linear_combination (k * Complex.I) * hT', Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
    mul_one]

end powerlib.Periodic
