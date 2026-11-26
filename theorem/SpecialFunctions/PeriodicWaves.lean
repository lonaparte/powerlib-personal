import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Harmonic content of periodic waves

Fourier coefficients over one period of the square, triangle and sawtooth waves and of the pure
sinusoid, their harmonic amplitudes, and the harmonic content index `h = (m₂ + m₃)/m₁` that the
method of §3.4 compares with a threshold to recognize a forced oscillation by its non-sinusoidal
steady-state waveform.

Scope.
* Real signals `f : ℝ → ℝ` and a period `T > 0`. The `n`-th coefficient is Mathlib's
  `fourierCoeffOn` over `[0, T]` of the complexified signal,
  `c_n = (1/T) ∫₀^T e^{−2πint/T} f(t) dt` (`coeff`); the harmonic amplitude is `m_n = 2|c_n|`
  (`amp`), equal to `√(a_n² + b_n²)` with the classical cosine and sine coefficients
  (`cosCoeff`, `sinCoeff`) for every interval-integrable signal.
* The waves of amplitude `V` and period `T` are defined through `Int.fract (t/T)`, hence
  `T`-periodic: the square wave (`V` on the first half period, `−V` on the second), the triangle
  wave (`V` at `t ≡ 0`, `−V` at `t ≡ T/2`), the sawtooth `V(1 − 2 frac(t/T))` (convention: falls
  from `V` to `−V`), and the sinusoid `V cos(2πt/T + φ)`.
* Pure analysis; no model family. Which waveform a measured oscillation has, the fundamental
  frequency estimation of Step 1 and the nonlinearity allowance of natural oscillations are not
  formalized.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.4, Steps 1–3 (harmonic
content index and the threshold `0.11`); §3.1 (harmonics and non-sinusoidal waveforms as
indicators of forcing).

Corrections and sharpenings.
* The report's threshold "0.11, the harmonic content index of a triangle wave" is exactly
  `h = 1/9` (`harmonicContent_triangleWave`); the square and sawtooth waves have `h = 1/3` and
  `h = 5/6` (above it), the pure sinusoid `h = 0` (`threshold_separates`).

Results.
* `coeff_eq_integral`, `coeff_eq_cos_sin`, `amp_eq_sqrt` — the coefficient as an interval
  integral with the kernel `e^{κ_n t}`, `κ_n = −2πin/T` (`kernelExp`); `c_n = (a_n − j b_n)/2`,
  `m_n = √(a_n² + b_n²)`.
* `coeff_squareWave`, `amp_squareWave_of_odd`, `amp_squareWave_of_even` —
  `c_n = −jV(1 − (−1)ⁿ)/(nπ)`, `m_n = 4|V|/(nπ)` for odd `n`, `0` for even `n`.
* `coeff_triangleWave`, `amp_triangleWave_of_odd`, `amp_triangleWave_of_even` —
  `c_n = 2V(1 − (−1)ⁿ)/(π²n²)`, `m_n = 8|V|/(π²n²)` for odd `n`, `0` for even `n`.
* `coeff_sawtoothWave`, `amp_sawtoothWave` — `c_n = −jV/(nπ)`, `m_n = 2|V|/(nπ)`.
* `coeff_cosineWave`, `amp_cosineWave` — `c_{±1} = (V/2)e^{±jφ}`, every other coefficient
  vanishes; `m₁ = |V|`, `m_n = 0` for `n ≥ 2`.
* `harmonicContent`, `harmonicContent_cosineWave`, `harmonicContent_triangleWave`,
  `harmonicContent_squareWave`, `harmonicContent_sawtoothWave`, `threshold_separates` —
  `h = 0, 1/9, 1/3, 5/6` for the sinusoid, triangle, square and sawtooth waves (`V ≠ 0`).
* `coeff_const_mul`, `amp_const_mul`, `harmonicContent_const_mul` — `m_n(Vf) = |V| m_n(f)`, so
  `h` is invariant under amplitude scaling `V ≠ 0`.
* `coeff_shift`, `amp_shift`, `harmonicContent_shift`, `squareWave_periodic`,
  `triangleWave_periodic`, `sawtoothWave_periodic` — for a `T`-periodic signal a time shift
  multiplies `c_n` by `e^{2πinτ/T}`, so `m_n` and `h` are shift invariant; the three waves are
  `T`-periodic.
-/

noncomputable section
namespace powerlib.SpecialFunctions.PeriodicWaves
open Complex Set MeasureTheory intervalIntegral

variable {T : ℝ}

/-- The `n`-th complex Fourier coefficient of a real signal over the period `[0, T]`:
`c_n = (1/T) ∫₀^T e^{−2πint/T} f(t) dt` (Mathlib's `fourierCoeffOn`). -/
def coeff (hT : 0 < T) (f : ℝ → ℝ) (n : ℤ) : ℂ := fourierCoeffOn hT (fun t => (f t : ℂ)) n

/-- The exponent `κ_n = −2πin/T` of the Fourier kernel `e^{κ_n t}`. -/
def kernelExp (T : ℝ) (n : ℤ) : ℂ := -(2 * Real.pi * I * n / T)

@[tmio T, powerlib_foundation] theorem coeff_eq_integral (hT : 0 < T) (f : ℝ → ℝ) (n : ℤ) :
    coeff hT f n = (1 / T : ℂ) * ∫ x in (0 : ℝ)..T, cexp (kernelExp T n * x) * f x := by
  rw [coeff, fourierCoeffOn_eq_integral, Complex.real_smul]
  congr 1
  · push_cast; ring
  · apply intervalIntegral.integral_congr
    intro x _
    simp only
    rw [fourier_coe_apply, smul_eq_mul, kernelExp]
    congr 2
    push_cast
    ring

@[tmio T, powerlib_foundation] private theorem integral_exp_mul_affine {k : ℂ} (hk : k ≠ 0)
    (α β : ℂ) (a b : ℝ) :
    ∫ x in a..b, cexp (k * x) * (α + β * x) =
      cexp (k * b) * ((α + β * b) / k - β / k ^ 2) -
        cexp (k * a) * ((α + β * a) / k - β / k ^ 2) := by
  apply integral_eq_sub_of_hasDerivAt
  · intro x _
    have h1 : HasDerivAt (fun y : ℝ => k * (y : ℂ)) k x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).const_mul k
    have h2 := h1.cexp
    have h3 : HasDerivAt (fun y : ℝ => (α + β * (y : ℂ)) / k - β / k ^ 2) (β / k) x := by
      have := ((((hasDerivAt_id x).ofReal_comp).const_mul β).const_add α).div_const k
      simpa using this.sub_const (β / k ^ 2)
    convert h2.mul h3 using 1
    field_simp
    ring
  · exact (by fun_prop : Continuous fun x : ℝ => cexp (k * x) * (α + β * x)).intervalIntegrable a b

@[tmio T, powerlib_foundation] private theorem piece {f g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hg : Continuous g) (h : EqOn g f (Ioo a b)) :
    IntervalIntegrable f volume a b ∧ ∫ x in a..b, f x = ∫ x in a..b, g x :=
  ⟨(hg.intervalIntegrable a b).congr_uIoo (by rwa [uIoo_of_le hab]),
    (integral_congr_Ioo_of_le hab h).symm⟩

@[tmio T, powerlib_foundation] private theorem kernelExp_ne_zero (hT : T ≠ 0) {n : ℤ}
    (hn : n ≠ 0) : kernelExp T n ≠ 0 := by
  have : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have := Real.pi_pos.ne'
  simp only [kernelExp, neg_ne_zero]
  apply div_ne_zero _ (by assumption)
  simp [Complex.I_ne_zero, *]

@[tmio T, powerlib_foundation] private theorem exp_kernelExp_period (hT : T ≠ 0) (n : ℤ) :
    cexp (kernelExp T n * T) = 1 := by
  have : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  rw [show kernelExp T n * T = n * (-(2 * Real.pi * I)) by
      simp only [kernelExp]; field_simp,
    Complex.exp_int_mul, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, one_zpow]

@[tmio T, powerlib_foundation] private theorem exp_kernelExp_half (hT : T ≠ 0) (n : ℕ) :
    cexp (kernelExp T n * ((T / 2 : ℝ) : ℂ)) = (-1) ^ n := by
  have : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  rw [show kernelExp T n * ((T / 2 : ℝ) : ℂ) = n * (-(Real.pi * I)) by
      simp only [kernelExp, Int.cast_natCast]; push_cast; field_simp,
    Complex.exp_nat_mul, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]

@[tmio T, powerlib_foundation] private theorem exp_kernelExp_zero (n : ℤ) :
    cexp (kernelExp T n * ((0 : ℝ) : ℂ)) = 1 := by
  simp

/-! ## The square wave -/

/-- Square wave of amplitude `V` and period `T`: `V` on the first half period, `−V` on the
second. -/
def squareWave (V T t : ℝ) : ℝ := if Int.fract (t / T) < 1 / 2 then V else -V

@[tmio T, powerlib_foundation] private theorem fract_div_eq (hT : 0 < T) {t : ℝ}
    (ht : t ∈ Ico 0 T) : Int.fract (t / T) = t / T := by
  rw [Int.fract_eq_self]
  exact ⟨div_nonneg ht.1 hT.le, (div_lt_one hT).mpr ht.2⟩

@[tmio T, powerlib_foundation] theorem coeff_squareWave (hT : 0 < T) (V : ℝ) {n : ℕ}
    (hn : n ≠ 0) :
    coeff hT (squareWave V T) n = -I * V * (1 - (-1) ^ n) / (Real.pi * n) := by
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hk := kernelExp_ne_zero hT.ne' (Int.natCast_ne_zero.mpr hn)
  set k := kernelExp T n with hkdef
  have hh : 0 ≤ T / 2 := by positivity
  have h1 := piece (f := fun x : ℝ => cexp (k * x) * (squareWave V T x : ℂ))
    (g := fun x : ℝ => cexp (k * x) * ((V : ℂ) + 0 * x)) hh (by fun_prop) (fun x hx => by
      have hc : x / T < 2⁻¹ := by rw [div_lt_iff₀ hT]; linarith [hx.2]
      simp [squareWave, fract_div_eq hT ⟨hx.1.le, by linarith [hx.2]⟩, hc])
  have h2 := piece (f := fun x : ℝ => cexp (k * x) * (squareWave V T x : ℂ))
    (g := fun x : ℝ => cexp (k * x) * ((-V : ℂ) + 0 * x)) (a := T / 2) (b := T) (by linarith)
    (by fun_prop) (fun x hx => by
      have hc : ¬ x / T < 2⁻¹ := by rw [not_lt, le_div_iff₀ hT]; linarith [hx.1]
      simp [squareWave, fract_div_eq hT ⟨by linarith [hx.1], hx.2⟩, hc])
  rw [coeff_eq_integral, ← hkdef, ← integral_add_adjacent_intervals h1.1 h2.1, h1.2, h2.2,
    integral_exp_mul_affine hk, integral_exp_mul_affine hk, exp_kernelExp_period hT.ne',
    exp_kernelExp_half hT.ne', exp_kernelExp_zero, hkdef, kernelExp]
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_pow_three]
  ring_nf

/-! ## The triangle and sawtooth waves -/

/-- Triangle wave of amplitude `V` and period `T`: `V` at `t ≡ 0`, `−V` at `t ≡ T/2`, linear in
between. -/
def triangleWave (V T t : ℝ) : ℝ := V * (4 * |Int.fract (t / T) - 1 / 2| - 1)

/-- Sawtooth wave of amplitude `V` and period `T`: falls linearly from `V` to `−V` over each
period, `V (1 − 2 frac(t/T))`. -/
def sawtoothWave (V T t : ℝ) : ℝ := V * (1 - 2 * Int.fract (t / T))

@[tmio T, powerlib_foundation] theorem coeff_triangleWave (hT : 0 < T) (V : ℝ) {n : ℕ}
    (hn : n ≠ 0) :
    coeff hT (triangleWave V T) n = 2 * V * (1 - (-1) ^ n) / (Real.pi ^ 2 * n ^ 2) := by
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hk := kernelExp_ne_zero hT.ne' (Int.natCast_ne_zero.mpr hn)
  set k := kernelExp T n with hkdef
  have hh : 0 ≤ T / 2 := by positivity
  have h1 := piece (f := fun x : ℝ => cexp (k * x) * (triangleWave V T x : ℂ))
    (g := fun x : ℝ => cexp (k * x) * ((V : ℂ) + (-4 * V / T : ℂ) * x)) hh (by fun_prop)
    (fun x hx => by
      have hc : x / T - 1 / 2 < 0 := by
        have : x / T < 1 / 2 := by rw [div_lt_iff₀ hT]; linarith [hx.2]
        linarith
      simp only [triangleWave, fract_div_eq hT ⟨hx.1.le, by linarith [hx.2]⟩, abs_of_neg hc]
      push_cast
      field_simp
      ring)
  have h2 := piece (f := fun x : ℝ => cexp (k * x) * (triangleWave V T x : ℂ))
    (g := fun x : ℝ => cexp (k * x) * ((-3 * V : ℂ) + (4 * V / T : ℂ) * x)) (a := T / 2)
    (b := T) (by linarith) (by fun_prop) (fun x hx => by
      have hc : 0 < x / T - 1 / 2 := by
        have : 1 / 2 < x / T := by rw [lt_div_iff₀ hT]; linarith [hx.1]
        linarith
      simp only [triangleWave, fract_div_eq hT ⟨by linarith [hx.1], hx.2⟩, abs_of_pos hc]
      push_cast
      field_simp
      ring)
  rw [coeff_eq_integral, ← hkdef, ← integral_add_adjacent_intervals h1.1 h2.1, h1.2, h2.2,
    integral_exp_mul_affine hk, integral_exp_mul_affine hk, exp_kernelExp_period hT.ne',
    exp_kernelExp_half hT.ne', exp_kernelExp_zero, hkdef, kernelExp]
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring_nf

@[tmio T, powerlib_foundation] theorem coeff_sawtoothWave (hT : 0 < T) (V : ℝ) {n : ℕ}
    (hn : n ≠ 0) :
    coeff hT (sawtoothWave V T) n = -I * V / (Real.pi * n) := by
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hk := kernelExp_ne_zero hT.ne' (Int.natCast_ne_zero.mpr hn)
  set k := kernelExp T n with hkdef
  have h1 := piece (f := fun x : ℝ => cexp (k * x) * (sawtoothWave V T x : ℂ))
    (g := fun x : ℝ => cexp (k * x) * ((V : ℂ) + (-2 * V / T : ℂ) * x)) hT.le (by fun_prop)
    (fun x hx => by
      simp only [sawtoothWave, fract_div_eq hT ⟨hx.1.le, hx.2⟩]
      push_cast
      field_simp
      ring)
  rw [coeff_eq_integral, ← hkdef, h1.2, integral_exp_mul_affine hk, exp_kernelExp_period hT.ne',
    exp_kernelExp_zero, hkdef, kernelExp]
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_pow_three]
  ring_nf

/-! ## The pure sinusoid -/

/-- The pure sinusoid `V cos(2πt/T + φ)`. -/
def cosineWave (V T φ t : ℝ) : ℝ := V * Real.cos (2 * Real.pi * t / T + φ)

@[tmio T, powerlib_foundation] private theorem integral_kernel (hT : 0 < T) (m : ℤ) :
    ∫ x in (0 : ℝ)..T, cexp (kernelExp T m * x) = if m = 0 then (T : ℂ) else 0 := by
  split_ifs with hm
  · subst hm; simp [kernelExp]
  · rw [integral_exp_mul_complex (kernelExp_ne_zero hT.ne' hm), exp_kernelExp_period hT.ne']
    simp

@[tmio T, powerlib_foundation] private theorem kernel_mul_cos (V φ : ℝ) (n : ℤ) (x : ℝ) :
    cexp (kernelExp T n * x) * (cosineWave V T φ x : ℂ) =
      (V / 2 * cexp (φ * I)) * cexp (kernelExp T (n - 1) * x) +
        (V / 2 * cexp (-(φ * I))) * cexp (kernelExp T (n + 1) * x) := by
  have e1 : kernelExp T n * x + ((2 * Real.pi * x / T + φ : ℝ) : ℂ) * I =
      φ * I + kernelExp T (n - 1) * x := by
    simp only [kernelExp]; push_cast; ring
  have e2 : kernelExp T n * x + -(((2 * Real.pi * x / T + φ : ℝ) : ℂ) * I) =
      -(φ * I) + kernelExp T (n + 1) * x := by
    simp only [kernelExp]; push_cast; ring
  rw [cosineWave, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  calc cexp (kernelExp T n * x) * (V * ((cexp (((2 * Real.pi * x / T + φ : ℝ) : ℂ) * I) +
          cexp (-((2 * Real.pi * x / T + φ : ℝ) : ℂ) * I)) / 2))
      = V / 2 * (cexp (kernelExp T n * x + ((2 * Real.pi * x / T + φ : ℝ) : ℂ) * I) +
          cexp (kernelExp T n * x + -(((2 * Real.pi * x / T + φ : ℝ) : ℂ) * I))) := by
        rw [Complex.exp_add, Complex.exp_add, neg_mul]; ring
    _ = _ := by rw [e1, e2, Complex.exp_add, Complex.exp_add]; ring

/-- The Fourier coefficients of `V cos(2πt/T + φ)`: `c_{±1} = (V/2) e^{±jφ}`, all others vanish. -/
@[tmio T, powerlib_foundation] theorem coeff_cosineWave (hT : 0 < T) (V φ : ℝ) (n : ℤ) :
    coeff hT (cosineWave V T φ) n =
      (if n = 1 then V / 2 * cexp (φ * I) else 0) +
        (if n = -1 then V / 2 * cexp (-(φ * I)) else 0) := by
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [coeff_eq_integral, intervalIntegral.integral_congr (fun x _ => kernel_mul_cos V φ n x),
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_kernel hT, integral_kernel hT]
  by_cases ha : n = 1
  · subst ha
    simp only [show (1 : ℤ) - 1 = 0 by norm_num, show (1 : ℤ) + 1 ≠ 0 by norm_num,
      show (1 : ℤ) ≠ -1 by norm_num, ↓reduceIte]
    field_simp
    ring
  · by_cases hb : n = -1
    · subst hb
      simp only [show (-1 : ℤ) - 1 ≠ 0 by norm_num, show (-1 : ℤ) + 1 = 0 by norm_num,
        show (-1 : ℤ) ≠ 1 by norm_num, ↓reduceIte]
      field_simp
      ring
    · simp only [ha, hb, show n - 1 ≠ 0 from fun h => ha (by omega),
        show n + 1 ≠ 0 from fun h => hb (by omega), ↓reduceIte]
      simp

/-! ## Harmonic amplitudes and the harmonic content index -/

/-- The amplitude `m_n = 2|c_n|` of the `n`-th harmonic (`n ≥ 1`); with the sine and cosine
coefficients `a_n = 2 Re c_n`, `b_n = −2 Im c_n` this is `√(a_n² + b_n²)`. -/
def amp (hT : 0 < T) (f : ℝ → ℝ) (n : ℕ) : ℝ := 2 * ‖coeff hT f n‖

/-- The harmonic content index `h = (m₂ + m₃)/m₁` of §3.4, Step 3. -/
def harmonicContent (hT : 0 < T) (f : ℝ → ℝ) : ℝ := (amp hT f 2 + amp hT f 3) / amp hT f 1

@[tmio T, powerlib_foundation] private theorem norm_I_mul_div (r q : ℝ) :
    ‖-I * (r : ℂ) / (q : ℂ)‖ = |r| / |q| := by
  rw [norm_div, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]

/-- Square wave: `m_n = 4|V|/(nπ)` for odd `n`. -/
@[tmio T, powerlib_foundation] theorem amp_squareWave_of_odd (hT : 0 < T) (V : ℝ) {n : ℕ}
    (hn : Odd n) : amp hT (squareWave V T) n = 4 * |V| / (Real.pi * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.pos
  rw [amp, coeff_squareWave hT V hn.pos.ne', hn.neg_one_pow,
    show -I * (V : ℂ) * (1 - -1) / (Real.pi * n) = -I * ((2 * V : ℝ) : ℂ) / ((Real.pi * n : ℝ) : ℂ)
      by push_cast; ring,
    norm_I_mul_div, abs_mul, abs_of_pos (mul_pos Real.pi_pos hn0)]
  norm_num
  ring

/-- Square wave: `m_n = 0` for even `n ≥ 2`. -/
@[tmio T, powerlib_foundation] theorem amp_squareWave_of_even (hT : 0 < T) (V : ℝ) {n : ℕ}
    (hn : Even n) (hn0 : n ≠ 0) : amp hT (squareWave V T) n = 0 := by
  rw [amp, coeff_squareWave hT V hn0, hn.neg_one_pow]
  simp

/-- Triangle wave: `m_n = 8|V|/(π² n²)` for odd `n`. -/
@[tmio T, powerlib_foundation] theorem amp_triangleWave_of_odd (hT : 0 < T) (V : ℝ) {n : ℕ}
    (hn : Odd n) : amp hT (triangleWave V T) n = 8 * |V| / (Real.pi ^ 2 * n ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.pos
  rw [amp, coeff_triangleWave hT V hn.pos.ne', hn.neg_one_pow,
    show 2 * (V : ℂ) * (1 - -1) / (Real.pi ^ 2 * n ^ 2) =
      ((4 * V / (Real.pi ^ 2 * n ^ 2) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < Real.pi ^ 2 * n ^ 2)]
  norm_num
  ring

/-- Triangle wave: `m_n = 0` for even `n ≥ 2`. -/
@[tmio T, powerlib_foundation] theorem amp_triangleWave_of_even (hT : 0 < T) (V : ℝ) {n : ℕ}
    (hn : Even n) (hn0 : n ≠ 0) : amp hT (triangleWave V T) n = 0 := by
  rw [amp, coeff_triangleWave hT V hn0, hn.neg_one_pow]
  simp

/-- Sawtooth wave: `m_n = 2|V|/(nπ)` for every `n ≥ 1`. -/
@[tmio T, powerlib_foundation] theorem amp_sawtoothWave (hT : 0 < T) (V : ℝ) {n : ℕ}
    (hn : n ≠ 0) : amp hT (sawtoothWave V T) n = 2 * |V| / (Real.pi * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [amp, coeff_sawtoothWave hT V hn,
    show -I * (V : ℂ) / (Real.pi * n) = -I * (V : ℂ) / ((Real.pi * n : ℝ) : ℂ) by push_cast; ring,
    norm_I_mul_div, abs_of_pos (mul_pos Real.pi_pos hn0)]
  ring

/-- Pure sinusoid: `m₁ = |V|` and `m_n = 0` for `n ≥ 2`. -/
@[tmio T, powerlib_foundation] theorem amp_cosineWave (hT : 0 < T) (V φ : ℝ) (n : ℕ) :
    amp hT (cosineWave V T φ) n = if n = 1 then |V| else 0 := by
  rw [amp, coeff_cosineWave hT V φ n]
  have hb : ¬ ((n : ℤ) = -1) := by omega
  simp only [hb, ↓reduceIte, add_zero]
  by_cases ha : n = 1
  · subst ha
    simp only [Nat.cast_one, ↓reduceIte]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_div, Complex.norm_real,
      Real.norm_eq_abs]
    norm_num
    ring
  · simp [ha, show ¬ ((n : ℤ) = 1) by omega]

/-- The pure sinusoid has harmonic content index `h = 0`. -/
@[tmio T, powerlib_foundation] theorem harmonicContent_cosineWave (hT : 0 < T) (V φ : ℝ) :
    harmonicContent hT (cosineWave V T φ) = 0 := by
  simp [harmonicContent, amp_cosineWave]

/-- The triangle wave has `h = 1/9` (the report's threshold `0.11`). -/
@[tmio T, powerlib_foundation] theorem harmonicContent_triangleWave (hT : 0 < T) {V : ℝ}
    (hV : V ≠ 0) : harmonicContent hT (triangleWave V T) = 1 / 9 := by
  have hV' := abs_pos.mpr hV
  rw [harmonicContent, amp_triangleWave_of_even hT V (by decide) (by decide),
    amp_triangleWave_of_odd hT V (by decide), amp_triangleWave_of_odd hT V (by decide)]
  have := Real.pi_pos
  field_simp
  norm_num

/-- The square wave has `h = 1/3`. -/
@[tmio T, powerlib_foundation] theorem harmonicContent_squareWave (hT : 0 < T) {V : ℝ}
    (hV : V ≠ 0) : harmonicContent hT (squareWave V T) = 1 / 3 := by
  have hV' := abs_pos.mpr hV
  rw [harmonicContent, amp_squareWave_of_even hT V (by decide) (by decide),
    amp_squareWave_of_odd hT V (by decide), amp_squareWave_of_odd hT V (by decide)]
  have := Real.pi_pos
  field_simp
  norm_num

/-- The sawtooth wave has `h = 5/6`. -/
@[tmio T, powerlib_foundation] theorem harmonicContent_sawtoothWave (hT : 0 < T) {V : ℝ}
    (hV : V ≠ 0) : harmonicContent hT (sawtoothWave V T) = 5 / 6 := by
  have hV' := abs_pos.mpr hV
  rw [harmonicContent, amp_sawtoothWave hT V (by decide), amp_sawtoothWave hT V (by decide),
    amp_sawtoothWave hT V (by decide)]
  have := Real.pi_pos
  field_simp
  norm_num

/-- With the threshold `h_m = h(triangle)` of Step 3, the square and sawtooth waves lie above it
and the pure sinusoid below it. -/
@[tmio T, powerlib_foundation] theorem threshold_separates (hT : 0 < T) {V : ℝ} (hV : V ≠ 0)
    (φ : ℝ) :
    harmonicContent hT (cosineWave V T φ) < harmonicContent hT (triangleWave V T) ∧
      harmonicContent hT (triangleWave V T) < harmonicContent hT (squareWave V T) ∧
      harmonicContent hT (triangleWave V T) < harmonicContent hT (sawtoothWave V T) := by
  rw [harmonicContent_cosineWave, harmonicContent_triangleWave hT hV,
    harmonicContent_squareWave hT hV, harmonicContent_sawtoothWave hT hV]
  norm_num

/-! ## Invariance under amplitude scaling and time shift -/

@[tmio T, powerlib_foundation] theorem coeff_const_mul (hT : 0 < T) (V : ℝ) (f : ℝ → ℝ)
    (n : ℤ) : coeff hT (fun t => V * f t) n = V * coeff hT f n := by
  rw [coeff, coeff, ← fourierCoeffOn.const_mul]
  congr 1
  funext t
  push_cast
  ring

@[tmio T, powerlib_foundation] theorem amp_const_mul (hT : 0 < T) (V : ℝ) (f : ℝ → ℝ) (n : ℕ) :
    amp hT (fun t => V * f t) n = |V| * amp hT f n := by
  rw [amp, amp, coeff_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  ring

/-- `h` is invariant under amplitude scaling `f ↦ V f`, `V ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem harmonicContent_const_mul (hT : 0 < T) {V : ℝ}
    (hV : V ≠ 0) (f : ℝ → ℝ) :
    harmonicContent hT (fun t => V * f t) = harmonicContent hT f := by
  rw [harmonicContent, harmonicContent, amp_const_mul, amp_const_mul, amp_const_mul, ← mul_add,
    mul_div_mul_left _ _ (abs_pos.mpr hV).ne']

/-- A time shift of a `T`-periodic signal rotates its coefficients:
`c_n(f(· + τ)) = e^{2πinτ/T} c_n(f)`. -/
@[tmio T, powerlib_foundation] theorem coeff_shift (hT : 0 < T) {f : ℝ → ℝ}
    (hf : Function.Periodic f T) (τ : ℝ) (n : ℤ) :
    coeff hT (fun t => f (t + τ)) n = cexp (-(kernelExp T n * τ)) * coeff hT f n := by
  set g : ℝ → ℂ := fun u => cexp (kernelExp T n * (u - τ : ℝ)) * f u with hg
  have hgp : Function.Periodic g T := by
    intro u
    simp only [hg, hf u]
    rw [show ((u + T - τ : ℝ) : ℂ) = ((u - τ : ℝ) : ℂ) + T by push_cast; ring, mul_add,
      Complex.exp_add, exp_kernelExp_period hT.ne', mul_one]
  rw [coeff_eq_integral, coeff_eq_integral]
  have h1 : ∫ x in (0 : ℝ)..T, cexp (kernelExp T n * x) * (f (x + τ) : ℂ) =
      ∫ x in (0 : ℝ)..T, g (x + τ) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [hg, add_sub_cancel_right]
  rw [h1, intervalIntegral.integral_comp_add_right, zero_add,
    show T + τ = τ + T by ring, hgp.intervalIntegral_add_eq τ 0, zero_add]
  have h2 : ∀ u : ℝ, g u = cexp (-(kernelExp T n * τ)) * (cexp (kernelExp T n * u) * f u) := by
    intro u
    simp only [hg]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [h2]
  rw [intervalIntegral.integral_const_mul]
  ring

@[tmio T, powerlib_foundation] private theorem norm_exp_neg_kernelExp (n : ℤ) (τ : ℝ) :
    ‖cexp (-(kernelExp T n * τ))‖ = 1 := by
  rw [show -(kernelExp T n * τ) = ((2 * Real.pi * n * τ / T : ℝ) : ℂ) * I by
      simp only [kernelExp]; push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

@[tmio T, powerlib_foundation] theorem amp_shift (hT : 0 < T) {f : ℝ → ℝ}
    (hf : Function.Periodic f T) (τ : ℝ) (n : ℕ) :
    amp hT (fun t => f (t + τ)) n = amp hT f n := by
  rw [amp, amp, coeff_shift hT hf, norm_mul, norm_exp_neg_kernelExp, one_mul]

/-- `h` is invariant under time shift of a `T`-periodic signal. -/
@[tmio T, powerlib_foundation] theorem harmonicContent_shift (hT : 0 < T) {f : ℝ → ℝ}
    (hf : Function.Periodic f T) (τ : ℝ) :
    harmonicContent hT (fun t => f (t + τ)) = harmonicContent hT f := by
  rw [harmonicContent, harmonicContent, amp_shift hT hf, amp_shift hT hf, amp_shift hT hf]

@[tmio T, powerlib_foundation] private theorem fract_add_period (hT : T ≠ 0) (t : ℝ) :
    Int.fract ((t + T) / T) = Int.fract (t / T) := by
  rw [add_div, div_self hT, Int.fract_add_one]

@[tmio T, powerlib_foundation] theorem squareWave_periodic (hT : T ≠ 0) (V : ℝ) :
    Function.Periodic (squareWave V T) T := fun t => by
  simp only [squareWave, fract_add_period hT]

@[tmio T, powerlib_foundation] theorem triangleWave_periodic (hT : T ≠ 0) (V : ℝ) :
    Function.Periodic (triangleWave V T) T := fun t => by
  simp only [triangleWave, fract_add_period hT]

@[tmio T, powerlib_foundation] theorem sawtoothWave_periodic (hT : T ≠ 0) (V : ℝ) :
    Function.Periodic (sawtoothWave V T) T := fun t => by
  simp only [sawtoothWave, fract_add_period hT]

/-! ## Sine and cosine coefficients -/

/-- The cosine coefficient `a_n = (2/T) ∫₀^T f(t) cos(2πnt/T) dt`. -/
def cosCoeff (T : ℝ) (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  2 / T * ∫ t in (0 : ℝ)..T, f t * Real.cos (2 * Real.pi * n * t / T)

/-- The sine coefficient `b_n = (2/T) ∫₀^T f(t) sin(2πnt/T) dt`. -/
def sinCoeff (T : ℝ) (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  2 / T * ∫ t in (0 : ℝ)..T, f t * Real.sin (2 * Real.pi * n * t / T)

/-- For an integrable real signal, `c_n = (a_n − j b_n)/2`. -/
@[tmio T, powerlib_foundation] theorem coeff_eq_cos_sin (hT : 0 < T) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 T) (n : ℕ) :
    coeff hT f n = ((cosCoeff T f n : ℂ) - (sinCoeff T f n : ℂ) * I) / 2 := by
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hc : IntervalIntegrable (fun t => f t * Real.cos (2 * Real.pi * n * t / T)) volume 0 T :=
    hf.mul_continuousOn (by fun_prop : Continuous fun t => Real.cos (2 * Real.pi * n * t / T)).continuousOn
  have hs : IntervalIntegrable (fun t => f t * Real.sin (2 * Real.pi * n * t / T)) volume 0 T :=
    hf.mul_continuousOn (by fun_prop : Continuous fun t => Real.sin (2 * Real.pi * n * t / T)).continuousOn
  have hc' : IntervalIntegrable (fun t => ((f t * Real.cos (2 * Real.pi * n * t / T) : ℝ) : ℂ))
      volume 0 T := ⟨hc.1.ofReal, hc.2.ofReal⟩
  have hs₀ : IntervalIntegrable (fun t => ((f t * Real.sin (2 * Real.pi * n * t / T) : ℝ) : ℂ))
      volume 0 T := ⟨hs.1.ofReal, hs.2.ofReal⟩
  have hs' : IntervalIntegrable (fun t => ((f t * Real.sin (2 * Real.pi * n * t / T) : ℝ) : ℂ) * I)
      volume 0 T := hs₀.mul_const I
  have hpt : ∀ x : ℝ, cexp (kernelExp T n * x) * (f x : ℂ) =
      ((f x * Real.cos (2 * Real.pi * n * x / T) : ℝ) : ℂ) -
        ((f x * Real.sin (2 * Real.pi * n * x / T) : ℝ) : ℂ) * I := by
    intro x
    rw [show kernelExp T n * x = ((-(2 * Real.pi * n * x / T) : ℝ) : ℂ) * I by
        simp only [kernelExp]; push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [coeff_eq_integral, intervalIntegral.integral_congr (fun x _ => hpt x),
    intervalIntegral.integral_sub hc' hs', intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal, cosCoeff, sinCoeff]
  push_cast
  field_simp

/-- The harmonic amplitude is `m_n = √(a_n² + b_n²)`. -/
@[tmio T, powerlib_foundation] theorem amp_eq_sqrt (hT : 0 < T) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 T) (n : ℕ) :
    amp hT f n = Real.sqrt (cosCoeff T f n ^ 2 + sinCoeff T f n ^ 2) := by
  rw [amp, coeff_eq_cos_sin hT hf, norm_div, Complex.norm_two, Complex.norm_def,
    Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, sub_zero, Complex.sub_im, Complex.mul_im,
    zero_sub]
  field_simp
  congr 1
  ring

end powerlib.SpecialFunctions.PeriodicWaves
