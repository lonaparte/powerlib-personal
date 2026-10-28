import theorem.Linear.Transfer

/-! # Pure transport delay and its Padé(1,1) / Padé(2,2) rational approximants

The exact transcendental delay, its Padé(1,1) and Padé(2,2) approximants, their all-pass,
non-minimum-phase and Taylor-order properties, and a state-space realization of Padé(1,1).

Model boundary.
* Statements about the delay operator models only: continuous time, linear time invariant,
  constant delay `τ`. No plant, PLL, PWM switching, sampling or closed loop is included; the
  stability statements concern only the internal state of the Padé realization. The real
  transcendental closed loop with `e^{-τ s}` is not treated.
* All transfer functions are complex functions of the Laplace variable `s`; `τ : ℝ` is the
  equivalent delay, normally `τ > 0`:
  * `pureDelay τ s = exp (-(τ s))`, the exact transcendental delay `e^{-τ s}`;
  * `pade11 τ s = (1 - τ s / 2) / (1 + τ s / 2)`;
  * `pade22 τ s = (1 - τ s / 2 + (τ s)² / 12) / (1 + τ s / 2 + (τ s)² / 12)`;
  * `pade11Model τ`, the SISO realization `(A, B, C, D) = (-2/τ, 1, 4/τ, -1)` as a
    `powerlib.Linear.Plant 1 1`;
  * `pade11DqModel τ`, the same realization on both axes of a dq frame
    (`Linear.Plant 2 2`, matrices `(-2/τ) I₂, I₂, (4/τ) I₂, -I₂`).
* The realizations are `Linear.Plant` values and their zero-input behaviour is the generic Flow
  semantics of the affine linear field.

Source: work-sync theory/T-control-delay.md §1.1 (cascade, 1.5 Tₛ), §1.2 (pure delay),
§1.3 (Padé(1,1), Padé(2,2)), §1.7 (dq delay matrix `G_del · I₂`);
theory/T-gfl-impedance.md §1.2 (Padé(1,1) used with the delay realization).

Results.
* `pureDelay_add`, `prod_pureDelay`, `pureDelay_three_half_periods` — delay cascade:
  `pureDelay (τ₁ + τ₂) = pureDelay τ₁ · pureDelay τ₂`, the finite-product version, and the
  "1.5 Tₛ" total of three half-period delays.
* `norm_pureDelay_jω`, `norm_pade11_jω`, `norm_pade22_jω` — frequency response on the imaginary
  axis `s = jω` (`ω : ℝ`): `|e^{-jωτ}| = 1`, `|pade11 τ (jω)| = 1`, `|pade22 τ (jω)| = 1`
  (all-pass).
* `pade11Num_eq_zero_iff`, `pade22Num_factor`, `pade11_rhp_zero`, `pade22_rhp_zeros` —
  non-minimum phase: the Padé(1,1) numerator vanishes exactly at `s = 2/τ`; the Padé(2,2)
  numerator factors as `(τs - (3 + √3 j))(τs - (3 - √3 j))/12`; every such zero lies in the
  open right half-plane when `τ > 0`, while the denominators do not vanish there.
* `norm_pureDelay_sub_pade11_le`, `norm_pureDelay_sub_pade22_le` — Taylor matching orders with
  explicit constants on the unit disc `‖τ s‖ ≤ 1`: `‖e^{-τ s} - pade11 τ s‖ ≤ 2 ‖τ s‖³` and
  `‖e^{-τ s} - pade22 τ s‖ ≤ ‖τ s‖⁵ / 10` (i.e. `O((τ s)³)` and `O((τ s)⁵)`).
* `transfer_pade11Model`, `pade11Model_exponentiallyStable`, `transfer_pade11DqModel` — the
  realization `pade11Model τ` has `Linear.transfer = pade11 τ s` for `s ≠ -2/τ`, and its
  zero-input dynamics (the affine linear field of its state matrix, Flow semantics) are
  globally exponentially stable for `τ > 0`; the dq version has transfer `pade11 τ s • I₂`
  (per-axis delay, no cross coupling).

Scope notes.
* The GFL impedance module `theorem/GFL/Impedance/Admittance.lean` does not use `pade11`: it
  defines its own delay factor `Gdel` with `G_del = (1 − a s)/(1 + a s)`, `a = τ_d/2`
  (`Gdel_eq`), the same Padé(1,1) form.
-/

noncomputable section
namespace powerlib.Delay
open Complex Matrix

/-- The exact delay transfer function `e^{-τ s}`. -/
def pureDelay (τ : ℝ) (s : ℂ) : ℂ := Complex.exp (-((τ : ℂ) * s))

def pade11Num (τ : ℝ) (s : ℂ) : ℂ := 1 - (τ : ℂ) * s / 2

def pade11Den (τ : ℝ) (s : ℂ) : ℂ := 1 + (τ : ℂ) * s / 2

/-- Padé(1,1) approximant `(1 - τ s / 2)/(1 + τ s / 2)` of `e^{-τ s}`. -/
def pade11 (τ : ℝ) (s : ℂ) : ℂ := pade11Num τ s / pade11Den τ s

def pade22Num (τ : ℝ) (s : ℂ) : ℂ := 1 - (τ : ℂ) * s / 2 + ((τ : ℂ) * s) ^ 2 / 12

def pade22Den (τ : ℝ) (s : ℂ) : ℂ := 1 + (τ : ℂ) * s / 2 + ((τ : ℂ) * s) ^ 2 / 12

/-- Padé(2,2) approximant of `e^{-τ s}`. -/
def pade22 (τ : ℝ) (s : ℂ) : ℂ := pade22Num τ s / pade22Den τ s

/-! ## Delay cascade -/

@[tmio T, powerlib_foundation] theorem pureDelay_add (τ₁ τ₂ : ℝ) (s : ℂ) :
    pureDelay (τ₁ + τ₂) s = pureDelay τ₁ s * pureDelay τ₂ s := by
  simp only [pureDelay, ← Complex.exp_add]
  congr 1
  push_cast
  ring

@[powerlib_foundation] theorem pureDelay_zero (s : ℂ) : pureDelay 0 s = 1 := by
  simp [pureDelay]

/-- A multiplicative cascade of constant delays is the delay by the total time. -/
@[powerlib_foundation] theorem prod_pureDelay {ι : Type*} (t : Finset ι) (τ : ι → ℝ) (s : ℂ) :
    ∏ i ∈ t, pureDelay (τ i) s = pureDelay (∑ i ∈ t, τ i) s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [pureDelay_zero]
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, pureDelay_add]

/-- Sampling, computation and PWM, each a half-period delay, total `1.5 Tₛ`. -/
@[powerlib_foundation] theorem pureDelay_three_half_periods (Ts : ℝ) (s : ℂ) :
    pureDelay (Ts / 2) s * pureDelay (Ts / 2) s * pureDelay (Ts / 2) s =
      pureDelay (3 * Ts / 2) s := by
  rw [← pureDelay_add, ← pureDelay_add]
  congr 1
  ring

/-! ## Frequency response: all-pass -/

@[powerlib_foundation] theorem pureDelay_jω (τ ω : ℝ) :
    pureDelay τ (ω * I) = Complex.exp (((-(τ * ω) : ℝ) : ℂ) * I) := by
  simp only [pureDelay]
  congr 1
  push_cast
  ring

@[powerlib_foundation] theorem norm_pureDelay_jω (τ ω : ℝ) : ‖pureDelay τ (ω * I)‖ = 1 := by
  rw [pureDelay_jω, Complex.norm_exp_ofReal_mul_I]

@[powerlib_foundation] private lemma norm_conj_div_self {z : ℂ} (hz : z ≠ 0) :
    ‖(starRingEnd ℂ) z / z‖ = 1 := by
  rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hz)]

@[powerlib_foundation] theorem pade11Num_jω (τ ω : ℝ) :
    pade11Num τ (ω * I) = 1 - ((τ * ω / 2 : ℝ) : ℂ) * I := by
  simp only [pade11Num]; push_cast; ring

@[powerlib_foundation] theorem pade11Den_jω (τ ω : ℝ) :
    pade11Den τ (ω * I) = 1 + ((τ * ω / 2 : ℝ) : ℂ) * I := by
  simp only [pade11Den]; push_cast; ring

@[powerlib_foundation] theorem pade11Den_jω_ne_zero (τ ω : ℝ) : pade11Den τ (ω * I) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [pade11Den_jω] at this
  simp at this

@[powerlib_foundation] theorem pade11Num_jω_eq_conj (τ ω : ℝ) :
    pade11Num τ (ω * I) = (starRingEnd ℂ) (pade11Den τ (ω * I)) := by
  rw [pade11Num_jω, pade11Den_jω, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
    map_one]
  ring

@[powerlib_foundation] theorem norm_pade11_jω (τ ω : ℝ) : ‖pade11 τ (ω * I)‖ = 1 := by
  rw [pade11, pade11Num_jω_eq_conj]
  exact norm_conj_div_self (pade11Den_jω_ne_zero τ ω)

@[powerlib_foundation] theorem pade22Num_jω (τ ω : ℝ) :
    pade22Num τ (ω * I) =
      ((1 - (τ * ω) ^ 2 / 12 : ℝ) : ℂ) - ((τ * ω / 2 : ℝ) : ℂ) * I := by
  simp only [pade22Num]; push_cast; ring_nf; rw [I_sq]; ring

@[powerlib_foundation] theorem pade22Den_jω (τ ω : ℝ) :
    pade22Den τ (ω * I) =
      ((1 - (τ * ω) ^ 2 / 12 : ℝ) : ℂ) + ((τ * ω / 2 : ℝ) : ℂ) * I := by
  simp only [pade22Den]; push_cast; ring_nf; rw [I_sq]; ring

@[powerlib_foundation] theorem pade22Den_jω_ne_zero (τ ω : ℝ) : pade22Den τ (ω * I) ≠ 0 := by
  intro h
  rw [pade22Den_jω] at h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add, zero_im, add_re, ofReal_re, mul_re, sub_self, zero_re] at him hre
  have hx : τ * ω = 0 := by linarith
  rw [hx] at hre
  norm_num at hre

@[powerlib_foundation] theorem pade22Num_jω_eq_conj (τ ω : ℝ) :
    pade22Num τ (ω * I) = (starRingEnd ℂ) (pade22Den τ (ω * I)) := by
  rw [pade22Num_jω, pade22Den_jω, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
    Complex.conj_I]
  ring

@[powerlib_foundation] theorem norm_pade22_jω (τ ω : ℝ) : ‖pade22 τ (ω * I)‖ = 1 := by
  rw [pade22, pade22Num_jω_eq_conj]
  exact norm_conj_div_self (pade22Den_jω_ne_zero τ ω)

/-! ## Zeros and poles: non-minimum phase -/

@[powerlib_foundation] theorem pade11Num_eq_zero_iff {τ : ℝ} (hτ : τ ≠ 0) (s : ℂ) :
    pade11Num τ s = 0 ↔ s = 2 / τ := by
  have hτ' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  simp only [pade11Num]
  constructor
  · intro h
    field_simp
    linear_combination -2 * h
  · rintro rfl
    field_simp
    ring

@[powerlib_foundation] theorem pade11Den_eq_zero_iff {τ : ℝ} (hτ : τ ≠ 0) (s : ℂ) :
    pade11Den τ s = 0 ↔ s = -2 / τ := by
  have hτ' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  simp only [pade11Den]
  constructor
  · intro h
    field_simp
    linear_combination 2 * h
  · rintro rfl
    field_simp
    ring

/-- Padé(1,1) has its only zero at `s = 2/τ`, in the open right half-plane. -/
@[powerlib_foundation] theorem pade11_rhp_zero {τ : ℝ} (hτ : 0 < τ) :
    pade11 τ (2 / τ) = 0 ∧ pade11Den τ (2 / τ) ≠ 0 ∧ 0 < (2 / (τ : ℂ)).re := by
  have hτ0 : τ ≠ 0 := hτ.ne'
  refine ⟨?_, ?_, ?_⟩
  · simp [pade11, (pade11Num_eq_zero_iff hτ0 _).mpr rfl]
  · rw [Ne, pade11Den_eq_zero_iff hτ0]
    intro h
    have := congrArg Complex.re h
    have h2 : (2 / (τ : ℂ)).re = 2 / τ := by
      rw [show (2 / (τ : ℂ)) = ((2 / τ : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
    have h3 : (-2 / (τ : ℂ)).re = -2 / τ := by
      rw [show (-2 / (τ : ℂ)) = ((-2 / τ : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
    rw [h2, h3] at this
    have h4 : 0 < 2 / τ := by positivity
    have h5 : -2 / τ < 0 := by rw [neg_div]; linarith
    linarith
  · rw [show (2 / (τ : ℂ)) = ((2 / τ : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
    positivity

/-- Factorization of the Padé(2,2) numerator; its roots are `τ s = 3 ± √3 j`. -/
@[powerlib_foundation] theorem pade22Num_factor (τ : ℝ) (s : ℂ) :
    pade22Num τ s =
      ((τ : ℂ) * s - (3 + (Real.sqrt 3 : ℂ) * I)) *
        ((τ : ℂ) * s - (3 - (Real.sqrt 3 : ℂ) * I)) / 12 := by
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; rfl
  simp only [pade22Num]
  linear_combination (-(1 : ℂ) / 12) * h3 + ((Real.sqrt 3 : ℂ) ^ 2 / 12) * I_sq

@[powerlib_foundation] theorem pade22Den_factor (τ : ℝ) (s : ℂ) :
    pade22Den τ s =
      ((τ : ℂ) * s - (-3 + (Real.sqrt 3 : ℂ) * I)) *
        ((τ : ℂ) * s - (-3 - (Real.sqrt 3 : ℂ) * I)) / 12 := by
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; rfl
  simp only [pade22Den]
  linear_combination (-(1 : ℂ) / 12) * h3 + ((Real.sqrt 3 : ℂ) ^ 2 / 12) * I_sq

@[powerlib_foundation] theorem pade22Num_eq_zero_iff {τ : ℝ} (hτ : τ ≠ 0) (s : ℂ) :
    pade22Num τ s = 0 ↔
      s = (3 + (Real.sqrt 3 : ℂ) * I) / τ ∨ s = (3 - (Real.sqrt 3 : ℂ) * I) / τ := by
  have hτ' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  rw [pade22Num_factor, div_eq_zero_iff, mul_eq_zero]
  simp only [OfNat.ofNat_ne_zero, or_false, sub_eq_zero]
  constructor
  · rintro (h | h)
    · left; rw [← h]; field_simp
    · right; rw [← h]; field_simp
  · rintro (h | h)
    · left; rw [h]; field_simp
    · right; rw [h]; field_simp

/-- Both Padé(2,2) zeros lie in the open right half-plane (real part `3/τ`) and the
denominator does not vanish there. -/
@[powerlib_foundation] theorem pade22_rhp_zeros {τ : ℝ} (hτ : 0 < τ) (s : ℂ)
    (hs : pade22Num τ s = 0) : 0 < s.re ∧ pade22Den τ s ≠ 0 ∧ pade22 τ s = 0 := by
  have hτ0 : τ ≠ 0 := hτ.ne'
  have hre : s.re = 3 / τ := by
    rcases (pade22Num_eq_zero_iff hτ0 s).mp hs with h | h <;>
    · rw [h, Complex.div_ofReal_re]
      simp
  refine ⟨by rw [hre]; positivity, ?_, by simp [pade22, hs]⟩
  intro hd
  have hz : pade22Num τ s - pade22Den τ s = 0 := by rw [hs, hd, sub_zero]
  have : (τ : ℂ) * s = 0 := by
    have h' : pade22Num τ s - pade22Den τ s = -((τ : ℂ) * s) := by
      simp only [pade22Num, pade22Den]; ring
    rw [h'] at hz
    exact neg_eq_zero.mp hz
  have hs0 : s = 0 := by
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by exact_mod_cast h) hτ0
    · exact h
  rw [hs0] at hre
  simp at hre
  exact (div_ne_zero (by norm_num : (3 : ℝ) ≠ 0) hτ0) hre.symm

/-! ## Taylor matching order -/

@[powerlib_foundation] private lemma exp_neg_taylor3 {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp (-z) - (1 - z + z ^ 2 / 2)‖ ≤ ‖z‖ ^ 3 * (2 / 9) := by
  have h := Complex.exp_bound (x := -z) (by simpa using hz) (n := 3) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 3, (-z) ^ m / (m.factorial : ℂ) = 1 - z + z ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  rw [hsum, norm_neg] at h
  convert h using 2
  norm_num [Nat.factorial]

@[powerlib_foundation] private lemma exp_neg_taylor5 {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp (-z) - (1 - z + z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24)‖ ≤ ‖z‖ ^ 5 * (1 / 100) := by
  have h := Complex.exp_bound (x := -z) (by simpa using hz) (n := 5) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 5, (-z) ^ m / (m.factorial : ℂ) =
      1 - z + z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  rw [hsum, norm_neg] at h
  convert h using 2
  norm_num [Nat.factorial]

/-- Padé(1,1) matches `e^{-z}` to third order: explicit bound on the unit disc. -/
@[powerlib_foundation] theorem norm_exp_neg_sub_pade11_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp (-z) - (1 - z / 2) / (1 + z / 2)‖ ≤ 2 * ‖z‖ ^ 3 := by
  have hden : (1 / 2 : ℝ) ≤ ‖1 + z / 2‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(z / 2))
    simp only [sub_neg_eq_add, norm_one, norm_neg, norm_div, Complex.norm_ofNat] at this
    linarith
  have hden0 : (1 + z / 2 : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hden; norm_num at hden
  have hkey : Complex.exp (-z) - (1 - z / 2) / (1 + z / 2) =
      ((1 + z / 2) * (Complex.exp (-z) - (1 - z + z ^ 2 / 2)) + z ^ 3 / 4) / (1 + z / 2) := by
    rw [eq_div_iff hden0, sub_mul, div_mul_cancel₀ _ hden0]
    ring
  rw [hkey, norm_div]
  rw [div_le_iff₀ (by linarith)]
  have hT := exp_neg_taylor3 hz
  have h1 : ‖(1 + z / 2 : ℂ)‖ ≤ 3 / 2 := by
    calc ‖(1 + z / 2 : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖z / 2‖ := norm_add_le _ _
      _ ≤ 3 / 2 := by
        simp only [norm_one, norm_div, Complex.norm_ofNat]; linarith
  have hz3 : ‖z ^ 3 / 4‖ = ‖z‖ ^ 3 / 4 := by simp [norm_pow]
  have hnn : 0 ≤ ‖z‖ ^ 3 := by positivity
  calc ‖(1 + z / 2) * (Complex.exp (-z) - (1 - z + z ^ 2 / 2)) + z ^ 3 / 4‖
      ≤ ‖(1 + z / 2 : ℂ)‖ * ‖Complex.exp (-z) - (1 - z + z ^ 2 / 2)‖ + ‖z ^ 3 / 4‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul]
    _ ≤ 3 / 2 * (‖z‖ ^ 3 * (2 / 9)) + ‖z‖ ^ 3 / 4 := by
        rw [hz3]
        gcongr
    _ ≤ 2 * ‖z‖ ^ 3 * (1 / 2) := by nlinarith
    _ ≤ 2 * ‖z‖ ^ 3 * ‖1 + z / 2‖ := by gcongr

/-- Padé(2,2) matches `e^{-z}` to fifth order: explicit bound on the unit disc. -/
@[powerlib_foundation] theorem norm_exp_neg_sub_pade22_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp (-z) - (1 - z / 2 + z ^ 2 / 12) / (1 + z / 2 + z ^ 2 / 12)‖ ≤
      ‖z‖ ^ 5 / 10 := by
  have hn0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hz2 : ‖z ^ 2 / 12‖ ≤ 1 / 12 := by
    rw [norm_div, norm_pow, Complex.norm_ofNat]
    have : ‖z‖ ^ 2 ≤ 1 := pow_le_one₀ hn0 hz
    linarith
  have hden : (5 / 12 : ℝ) ≤ ‖1 + z / 2 + z ^ 2 / 12‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) (-(z / 2 + z ^ 2 / 12))
    have h2 : ‖z / 2 + z ^ 2 / 12‖ ≤ 1 / 2 + 1 / 12 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_div, Complex.norm_ofNat]
      linarith
    rw [sub_neg_eq_add, ← add_assoc, norm_neg, norm_one] at h1
    linarith
  have hden0 : (1 + z / 2 + z ^ 2 / 12 : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hden; norm_num at hden
  have hkey : Complex.exp (-z) - (1 - z / 2 + z ^ 2 / 12) / (1 + z / 2 + z ^ 2 / 12) =
      ((1 + z / 2 + z ^ 2 / 12) *
          (Complex.exp (-z) - (1 - z + z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24)) +
        (z ^ 5 / 144 + z ^ 6 / 288)) / (1 + z / 2 + z ^ 2 / 12) := by
    rw [eq_div_iff hden0, sub_mul, div_mul_cancel₀ _ hden0]
    ring
  rw [hkey, norm_div, div_le_iff₀ (by linarith)]
  have hT := exp_neg_taylor5 hz
  have h1 : ‖(1 + z / 2 + z ^ 2 / 12 : ℂ)‖ ≤ 19 / 12 := by
    calc ‖(1 + z / 2 + z ^ 2 / 12 : ℂ)‖ ≤ ‖(1 + z / 2 : ℂ)‖ + ‖z ^ 2 / 12‖ := norm_add_le _ _
      _ ≤ ‖(1 : ℂ)‖ + ‖z / 2‖ + ‖z ^ 2 / 12‖ := by gcongr; exact norm_add_le _ _
      _ ≤ 19 / 12 := by
        rw [norm_one, norm_div, Complex.norm_ofNat]; linarith
  have h6 : ‖z‖ ^ 6 ≤ ‖z‖ ^ 5 := by
    calc ‖z‖ ^ 6 = ‖z‖ ^ 5 * ‖z‖ := by ring
      _ ≤ ‖z‖ ^ 5 * 1 := by gcongr
      _ = ‖z‖ ^ 5 := by ring
  have hpoly : ‖z ^ 5 / 144 + z ^ 6 / 288‖ ≤ ‖z‖ ^ 5 / 144 + ‖z‖ ^ 6 / 288 := by
    refine (norm_add_le _ _).trans ?_
    simp [norm_pow]
  have h5 : 0 ≤ ‖z‖ ^ 5 := by positivity
  calc ‖(1 + z / 2 + z ^ 2 / 12) *
          (Complex.exp (-z) - (1 - z + z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24)) +
        (z ^ 5 / 144 + z ^ 6 / 288)‖
      ≤ ‖(1 + z / 2 + z ^ 2 / 12 : ℂ)‖ *
          ‖Complex.exp (-z) - (1 - z + z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24)‖ +
        ‖z ^ 5 / 144 + z ^ 6 / 288‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul]
    _ ≤ 19 / 12 * (‖z‖ ^ 5 * (1 / 100)) + (‖z‖ ^ 5 / 144 + ‖z‖ ^ 6 / 288) := by
        gcongr
    _ ≤ ‖z‖ ^ 5 / 10 * (5 / 12) := by nlinarith
    _ ≤ ‖z‖ ^ 5 / 10 * ‖1 + z / 2 + z ^ 2 / 12‖ := by gcongr

/-- `‖e^{-τ s} - pade11 τ s‖ ≤ 2 ‖τ s‖³` whenever `‖τ s‖ ≤ 1`. -/
@[powerlib_foundation] theorem norm_pureDelay_sub_pade11_le (τ : ℝ) {s : ℂ}
    (hs : ‖(τ : ℂ) * s‖ ≤ 1) :
    ‖pureDelay τ s - pade11 τ s‖ ≤ 2 * ‖(τ : ℂ) * s‖ ^ 3 := by
  have h := norm_exp_neg_sub_pade11_le hs
  simpa [pureDelay, pade11, pade11Num, pade11Den, mul_div_assoc] using h

/-- `‖e^{-τ s} - pade22 τ s‖ ≤ ‖τ s‖⁵ / 10` whenever `‖τ s‖ ≤ 1`. -/
@[powerlib_foundation] theorem norm_pureDelay_sub_pade22_le (τ : ℝ) {s : ℂ}
    (hs : ‖(τ : ℂ) * s‖ ≤ 1) :
    ‖pureDelay τ s - pade22 τ s‖ ≤ ‖(τ : ℂ) * s‖ ^ 5 / 10 := by
  have h := norm_exp_neg_sub_pade22_le hs
  simpa [pureDelay, pade22, pade22Num, pade22Den, mul_div_assoc] using h

/-! ## State-space realization of Padé(1,1) -/

/-- `(A, B, C, D) = (-2/τ, 1, 4/τ, -1)`. -/
def pade11Model (τ : ℝ) : Linear.Plant 1 1 :=
  ⟨!![-2 / τ], !![1], !![4 / τ], !![-1]⟩

/-- Scalar identity behind the realization: `(4/τ)(s + 2/τ)⁻¹ - 1 = pade11 τ s`. -/
@[powerlib_foundation] theorem pade11_eq_realization {τ : ℝ} (hτ : τ ≠ 0) {s : ℂ}
    (hs : s + 2 / (τ : ℂ) ≠ 0) :
    4 / (τ : ℂ) * (s + 2 / (τ : ℂ))⁻¹ - 1 = pade11 τ s := by
  have hτ' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  have hden : pade11Den τ s ≠ 0 := by
    intro h; apply hs
    have : pade11Den τ s = (τ : ℂ) / 2 * (s + 2 / τ) := by
      simp only [pade11Den]; field_simp; ring
    rw [this] at h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h (div_ne_zero hτ' two_ne_zero)
    · exact h
  rw [pade11, eq_div_iff hden]
  simp only [pade11Num, pade11Den]
  linear_combination (2 * s * (s + 2 / (τ : ℂ))⁻¹) * inv_mul_cancel₀ hτ' +
    2 * inv_mul_cancel₀ hs

/-- The state-space realization `(-2/τ, 1, 4/τ, -1)` has transfer function `pade11 τ s`. -/
@[powerlib_foundation] theorem transfer_pade11Model {τ : ℝ} (hτ : τ ≠ 0) {s : ℂ}
    (hs : s ≠ -2 / τ) : Linear.transfer (pade11Model τ) s = !![pade11 τ s] := by
  have hden : s + 2 / (τ : ℂ) ≠ 0 := by
    intro h; apply hs; linear_combination h
  have hinv : (Linear.characteristicMatrix (pade11Model τ).A s)⁻¹ =
      !![(s + 2 / (τ : ℂ))⁻¹] := by
    have hchar : Linear.characteristicMatrix (pade11Model τ).A s = !![s + 2 / (τ : ℂ)] := by
      ext i j
      fin_cases i; fin_cases j
      simp [Linear.characteristicMatrix, pade11Model]
      ring
    rw [hchar]
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, inv_mul_cancel₀ hden]
  rw [Linear.transfer, hinv, ← pade11_eq_realization hτ hden]
  ext i j
  fin_cases i; fin_cases j
  simp [pade11Model, Matrix.mul_apply, Linear.complexify]
  ring

/-- The realization's internal state is exponentially stable when `τ > 0`. -/
@[powerlib_foundation] theorem pade11Model_exponentiallyStable {τ : ℝ} (hτ : 0 < τ) :
    Flow.GloballyExponentiallyStable
      (LinearSystems.affineLinearVectorField (pade11Model τ).A 0) 0 := by
  apply Linear.globallyExponentiallyStable_of_isHurwitz
  have h := LinearSystems.isHurwitzWithRate_neg_one_by_one (α := 0) (γ := 2 / τ)
    (by positivity)
  convert h using 1
  ext i j
  fin_cases i; fin_cases j
  simp [pade11Model]
  ring

/-- dq realization: the Padé(1,1) delay applied independently on the d and q axes. -/
def pade11DqModel (τ : ℝ) : Linear.Plant 2 2 :=
  ⟨(-2 / τ) • 1, 1, (4 / τ) • 1, -1⟩

/-- The dq delay matrix is the scalar Padé(1,1) delay times `I₂` (no cross coupling). -/
@[powerlib_foundation] theorem transfer_pade11DqModel {τ : ℝ} (hτ : τ ≠ 0) {s : ℂ}
    (hs : s ≠ -2 / τ) :
    Linear.transfer (pade11DqModel τ) s = pade11 τ s • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hτ' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  have hden : s + 2 / (τ : ℂ) ≠ 0 := by
    intro h; apply hs; linear_combination h
  have hchar : Linear.characteristicMatrix (pade11DqModel τ).A s =
      (s + 2 / (τ : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Linear.characteristicMatrix, pade11DqModel] <;> ring
  have hinv : (Linear.characteristicMatrix (pade11DqModel τ).A s)⁻¹ =
      (s + 2 / (τ : ℂ))⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hchar]
    apply Matrix.inv_eq_left_inv
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hden, Matrix.one_mul, one_smul]
  rw [Linear.transfer, hinv, ← pade11_eq_realization hτ hden]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pade11DqModel, Linear.complexify] <;> ring

end powerlib.Delay
