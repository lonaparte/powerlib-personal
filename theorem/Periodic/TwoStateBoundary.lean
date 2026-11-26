import theorem.Periodic.Liouville
import theorem.ParametricResonance.PeriodicAveraging

/-! # The exact Floquet boundary of a two-state periodic system

For a real `2 × 2` monodromy matrix `M` the multipliers are the roots of `μ² − (tr M) μ + det M`.
When `0 < det M < 1` — the case of every damped second-order system, whose multipliers have the
product `det M = e^{−2cT}` by Liouville's formula — the stability region is exactly
`|tr M| < 1 + det M`; a pair of complex multipliers always has `|μ|² = det M < 1`, so the system
can lose stability only through a real multiplier crossing `−1` (`tr M = −(1 + det M)`,
subharmonic, period-doubling) or `+1` (`tr M = 1 + det M`, harmonic); a multiplier on the unit
circle is `±1`.

Scope.
* Real `2 × 2` matrices `P` and the complex spectrum of their complexification (the Floquet
  multipliers when `P` is a monodromy matrix); `LTI.SchurStable` is "every eigenvalue inside the
  unit circle" (`theorem/LTI/Discrete.lean`).
* The periodic statements concern `ẋ = A(t) x` with `A(t) = [[0, 1], [−k(t), −2c]]`
  (`oscMatrix`): the state form `(x, ẋ)` of `ẍ + 2c ẋ + k(t) x = 0` with a continuous
  `T`-periodic stiffness `k` (`T > 0`) and constant damping `c ≥ 0`; the monodromy matrix is
  `monodromy A T 0` of `theorem/Periodic/Transition.lean`.
* Generic mathematics; no model family.

Source: Floquet theory of second-order periodic equations (Hill/Mathieu type; Yakubovich–
Starzhinskii; Nayfeh–Mook, *Nonlinear Oscillations*, parametrically excited systems: the
boundaries `tr M = ±(1 + det M)` of the instability tongues); the two-state Jury conditions `ParametricResonance.Averaging.schurStable_of_jury`,
`ParametricResonance.Averaging.eig_root`, `ParametricResonance.Averaging.mem_spectrum_of_root` of
`theorem/ParametricResonance/PeriodicAveraging.lean`, and Liouville's formula
`det_monodromy_of_trace` of `theorem/Periodic/Liouville.lean`.

Results.
* `mem_spectrum_iff_root` — `μ` is a multiplier iff `μ² − tr μ + det = 0`.
* `sq_norm_eq_det_of_im_ne_zero` — a non-real multiplier has `|μ|² = det`.
* `exists_real_eig_of_le`, `exists_real_eig_of_lt` — `|tr| ≥ 1 + det` (resp. `>`) gives a real
  multiplier with `|μ| ≥ 1` (resp. `> 1`).
* `norm_le_one_of_abs_trace_le` — for `0 < det ≤ 1`, `|tr| ≤ 1 + det` puts every multiplier in
  the closed unit disk.
* `exists_one_lt_norm_iff` — for `0 < det ≤ 1`: a multiplier outside the unit circle iff
  `1 + det < |tr|`; `schurStable_iff_abs_trace_lt` — for `det < 1`: Schur stability iff
  `|tr| < 1 + det`.
* `neg_one_mem_spectrum_iff`, `one_mem_spectrum_iff` — `−1` is a multiplier iff
  `tr = −(1 + det)`, `+1` iff `tr = 1 + det`.
* `im_eq_zero_of_one_le_norm`, `eq_one_or_eq_neg_one_of_norm_eq_one` — for `det < 1` every
  multiplier on or outside the unit circle is real, and one on the circle is `±1`.
* `oscMatrix`, `trace_oscMatrix`, `det_oscMatrix` — `[[0, 1], [−k, −2c]]`, trace `−2c`, determinant
  `k`.
* `damped_floquetUnstable_iff` — `ẍ + 2cẋ + k(t)x = 0`, `c ≥ 0`: `det M = e^{−2cT}` and Floquet
  instability iff `1 + e^{−2cT} < |tr M|` (undamped: `2 < |tr M|`).
* `damped_boundary` — for `c > 0`: Schur stability iff `|tr M| < 1 + e^{−2cT}`; every multiplier
  with `|μ| ≥ 1` is real; `−1` is a multiplier iff `tr M = −(1 + e^{−2cT})`, `+1` iff
  `tr M = 1 + e^{−2cT}`.
-/

noncomputable section
namespace powerlib.Periodic

open Set Matrix Function
open scoped Matrix.Norms.Operator

/-! ## Multipliers of a real `2 × 2` matrix -/

section TwoByTwo

variable {P : Matrix (Fin 2) (Fin 2) ℝ}

/-- The multipliers of a real `2 × 2` matrix are the roots of `μ² − tr μ + det`. -/
@[tmio T, powerlib_foundation] theorem mem_spectrum_iff_root {μ : ℂ} :
    μ ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ)) ↔ μ ^ 2 - (P.trace : ℂ) * μ + (P.det : ℂ) = 0 := by
  constructor
  · intro h
    obtain ⟨v, hv, hP⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp h
    exact ParametricResonance.Averaging.eig_root hv hP
  · exact ParametricResonance.Averaging.mem_spectrum_of_root

/-- A non-real multiplier of a real `2 × 2` matrix has `|μ|² = det`. -/
@[tmio T, powerlib_foundation] theorem sq_norm_eq_det_of_im_ne_zero {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ))) (him : μ.im ≠ 0) : ‖μ‖ ^ 2 = P.det := by
  have h := mem_spectrum_iff_root.mp hμ
  have hre := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hre hi
  have hx : 2 * μ.re = P.trace := by
    have : μ.im * (2 * μ.re - P.trace) = 0 := by linarith
    linarith [(mul_eq_zero.mp this).resolve_left him]
  have hm : P.trace * μ.re = 2 * μ.re * μ.re := by rw [← hx]
  rw [Complex.sq_norm, Complex.normSq_apply]
  linarith

/-- The real root of larger modulus: a real multiplier `r` with `|tr| ≤ 2|r|` and
`|r|² − |tr| |r| + det = 0`, when the discriminant is nonnegative. -/
@[tmio T, powerlib_foundation] private theorem exists_real_root (h : 4 * P.det ≤ P.trace ^ 2) :
    ∃ r : ℝ, (r : ℂ) ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ)) ∧ |P.trace| ≤ 2 * |r| ∧
      |r| ^ 2 - |P.trace| * |r| + P.det = 0 := by
  set a := P.trace
  set b := P.det
  set s := √(a ^ 2 - 4 * b)
  have hs : s ^ 2 = a ^ 2 - 4 * b := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set z := (|a| + s) / 2
  have hz0 : 0 ≤ z := by positivity
  have hza : |a| ≤ 2 * z := by simp only [z]; linarith
  have hzq : z ^ 2 - |a| * z + b = 0 := by
    simp only [z]
    have : |a| ^ 2 = a ^ 2 := sq_abs a
    nlinarith
  refine ⟨if 0 ≤ a then z else -z, ?_, ?_, ?_⟩
  · rw [mem_spectrum_iff_root]
    have hr : (if 0 ≤ a then z else -z) ^ 2 - a * (if 0 ≤ a then z else -z) + b = 0 := by
      split_ifs with ha
      · rw [abs_of_nonneg ha] at hzq; exact hzq
      · rw [abs_of_neg (not_le.mp ha)] at hzq; linarith
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hr
  · split_ifs <;> simp [abs_of_nonneg hz0, hza]
  · split_ifs <;> simp [abs_of_nonneg hz0, hzq]

/-- `|tr| ≥ 1 + det` gives a real multiplier on or outside the unit circle. -/
@[tmio T, powerlib_foundation] theorem exists_real_eig_of_le (h : 1 + P.det ≤ |P.trace|) :
    ∃ r : ℝ, (r : ℂ) ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ)) ∧ 1 ≤ |r| := by
  have hdisc : 4 * P.det ≤ P.trace ^ 2 := by
    rcases le_or_gt 0 (1 + P.det) with h0 | h0
    · have : (1 + P.det) ^ 2 ≤ |P.trace| ^ 2 := pow_le_pow_left₀ h0 h 2
      rw [sq_abs] at this
      nlinarith [sq_nonneg (1 - P.det)]
    · nlinarith [sq_nonneg P.trace]
  obtain ⟨r, hr, hra, hrq⟩ := exists_real_root hdisc
  refine ⟨r, hr, ?_⟩
  by_contra hlt
  push Not at hlt
  have h1 : 0 < 1 - |r| := by linarith
  have h2 : 0 < 1 - (|P.trace| - |r|) := by linarith
  have : (1 - |r|) * (1 - (|P.trace| - |r|)) = 1 - |P.trace| + P.det := by linarith
  nlinarith [mul_pos h1 h2]

/-- `|tr| > 1 + det` gives a real multiplier strictly outside the unit circle. -/
@[tmio T, powerlib_foundation] theorem exists_real_eig_of_lt (h : 1 + P.det < |P.trace|) :
    ∃ r : ℝ, (r : ℂ) ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ)) ∧ 1 < |r| := by
  have hdisc : 4 * P.det ≤ P.trace ^ 2 := by
    rcases le_or_gt 0 (1 + P.det) with h0 | h0
    · have : (1 + P.det) ^ 2 ≤ |P.trace| ^ 2 := pow_le_pow_left₀ h0 h.le 2
      rw [sq_abs] at this
      nlinarith [sq_nonneg (1 - P.det)]
    · nlinarith [sq_nonneg P.trace]
  obtain ⟨r, hr, hra, hrq⟩ := exists_real_root hdisc
  refine ⟨r, hr, ?_⟩
  by_contra hle
  push Not at hle
  have h1 : 0 ≤ 1 - |r| := by linarith
  have h2 : 0 ≤ 1 - (|P.trace| - |r|) := by linarith
  have : (1 - |r|) * (1 - (|P.trace| - |r|)) = 1 - |P.trace| + P.det := by linarith
  nlinarith [mul_nonneg h1 h2]

/-- For `0 < det ≤ 1`, `|tr| ≤ 1 + det` keeps every multiplier in the closed unit disk. -/
@[tmio T, powerlib_foundation] theorem norm_le_one_of_abs_trace_le (h0 : 0 < P.det)
    (h1 : P.det ≤ 1) (h : |P.trace| ≤ 1 + P.det) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ))) : ‖μ‖ ≤ 1 := by
  by_cases him : μ.im = 0
  · have hroot := mem_spectrum_iff_root.mp hμ
    have hre := congrArg Complex.re hroot
    simp [pow_two, Complex.mul_re, him] at hre
    have hμr : μ = (μ.re : ℂ) := Complex.ext rfl (by simp [him])
    rw [hμr, Complex.norm_real, Real.norm_eq_abs]
    set x := μ.re
    have habs := abs_le.mp h
    by_contra hx
    push Not at hx
    rcases lt_abs.mp hx with hx1 | hx1
    · -- `x > 1`: the other root `tr − x = det/x` is positive, and `x ≤ det ≤ 1`
      have hb : P.det = x * (P.trace - x) := by linarith
      have hpos : 0 < P.trace - x := by
        by_contra hneg
        push Not at hneg
        nlinarith
      nlinarith
    · -- `x < −1`: symmetric
      have hb : P.det = x * (P.trace - x) := by linarith
      have hneg : P.trace - x < 0 := by
        by_contra hpos
        push Not at hpos
        nlinarith
      nlinarith
  · have hn := sq_norm_eq_det_of_im_ne_zero hμ him
    nlinarith [norm_nonneg μ]

/-- For `0 < det ≤ 1`: some multiplier lies strictly outside the unit circle iff
`1 + det < |tr|`. -/
@[tmio T, powerlib_foundation] theorem exists_one_lt_norm_iff (h0 : 0 < P.det) (h1 : P.det ≤ 1) :
    (∃ μ ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ)), 1 < ‖μ‖) ↔ 1 + P.det < |P.trace| := by
  constructor
  · rintro ⟨μ, hμ, hlt⟩
    by_contra hle
    push Not at hle
    exact absurd (norm_le_one_of_abs_trace_le h0 h1 hle hμ) (not_le.mpr hlt)
  · intro h
    obtain ⟨r, hr, hr1⟩ := exists_real_eig_of_lt h
    exact ⟨r, hr, by rwa [Complex.norm_real, Real.norm_eq_abs]⟩

/-- For `det < 1`: every multiplier is strictly inside the unit circle iff `|tr| < 1 + det`. -/
@[tmio T, powerlib_foundation] theorem schurStable_iff_abs_trace_lt (h1 : P.det < 1) :
    LTI.SchurStable P ↔ |P.trace| < 1 + P.det := by
  constructor
  · intro hS
    by_contra hle
    push Not at hle
    obtain ⟨r, hr, hr1⟩ := exists_real_eig_of_le hle
    obtain ⟨v, hv, hPv⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp hr
    have := hS _ v hv hPv
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    linarith
  · intro h
    have ha := abs_lt.mp h
    refine ParametricResonance.Averaging.schurStable_of_jury h1 ?_ ?_
    · have e : (1 - P).det = 1 - P.trace + P.det := by
        simp [Matrix.det_fin_two, Matrix.trace_fin_two]; ring
      linarith
    · have e : (1 + P).det = 1 + P.trace + P.det := by
        simp [Matrix.det_fin_two, Matrix.trace_fin_two]; ring
      linarith

/-- `−1` is a multiplier iff `tr = −(1 + det)` (period doubling). -/
@[tmio T, powerlib_foundation] theorem neg_one_mem_spectrum_iff :
    (-1 : ℂ) ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ)) ↔ P.trace = -(1 + P.det) := by
  rw [mem_spectrum_iff_root]
  constructor
  · intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  · intro h
    rw [h]
    push_cast
    ring

/-- `+1` is a multiplier iff `tr = 1 + det`. -/
@[tmio T, powerlib_foundation] theorem one_mem_spectrum_iff :
    (1 : ℂ) ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ)) ↔ P.trace = 1 + P.det := by
  rw [mem_spectrum_iff_root]
  constructor
  · intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  · intro h
    rw [h]
    push_cast
    ring

/-- For `det < 1` a multiplier on or outside the unit circle is real: complex multipliers have
`|μ|² = det < 1`. -/
@[tmio T, powerlib_foundation] theorem im_eq_zero_of_one_le_norm (h1 : P.det < 1) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ))) (hn : 1 ≤ ‖μ‖) : μ.im = 0 := by
  by_contra him
  have := sq_norm_eq_det_of_im_ne_zero hμ him
  nlinarith

/-- For `det < 1` a multiplier on the unit circle is `+1` or `−1`. -/
@[tmio T, powerlib_foundation] theorem eq_one_or_eq_neg_one_of_norm_eq_one (h1 : P.det < 1)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ))) (hn : ‖μ‖ = 1) :
    μ = 1 ∨ μ = -1 := by
  have him := im_eq_zero_of_one_le_norm h1 hμ hn.ge
  have hμr : μ = (μ.re : ℂ) := Complex.ext rfl (by simp [him])
  rw [hμr, Complex.norm_real, Real.norm_eq_abs] at hn
  rcases abs_eq (zero_le_one) |>.mp hn with h | h
  · left; rw [hμr, h]; simp
  · right; rw [hμr, h]; simp

end TwoByTwo

/-! ## Damped second-order periodic systems -/

/-- The state matrix `[[0, 1], [−k, −2c]]` of `ẍ + 2c ẋ + k x = 0` in the state `(x, ẋ)`. -/
def oscMatrix (c k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -k, -(2 * c)]

@[tmio T, powerlib_foundation] theorem trace_oscMatrix (c k : ℝ) :
    (oscMatrix c k).trace = -(2 * c) := by
  simp [oscMatrix, Matrix.trace_fin_two]

@[tmio T, powerlib_foundation] theorem det_oscMatrix (c k : ℝ) : (oscMatrix c k).det = k := by
  simp [oscMatrix, Matrix.det_fin_two]

/-- **Floquet instability of a damped second-order periodic system.** For
`ẍ + 2c ẋ + k(t) x = 0` (`c ≥ 0`, `k` continuous and `T`-periodic) the multipliers have the
product `det M = e^{−2cT}`, and some multiplier lies outside the unit circle iff
`1 + e^{−2cT} < |tr M|` (for `c = 0`: `2 < |tr M|`). -/
@[tmio T, powerlib_foundation] theorem damped_floquetUnstable_iff {c T : ℝ} {k : ℝ → ℝ}
    (hk : Continuous k) (hkP : Periodic k T) (hc : 0 ≤ c) (hT : 0 < T) :
    (monodromy (fun t => oscMatrix c (k t)) T 0).det = Real.exp (-(2 * c) * T) ∧
      (FloquetUnstable (fun t => oscMatrix c (k t)) T ↔
        1 + Real.exp (-(2 * c) * T) < |(monodromy (fun t => oscMatrix c (k t)) T 0).trace|) := by
  have hA : Continuous fun t => oscMatrix c (k t) := by
    unfold oscMatrix
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hP : Periodic (fun t => oscMatrix c (k t)) T := fun t => by simp only [hkP t]
  have hdet := det_monodromy_of_trace hA hP (fun t => trace_oscMatrix c (k t)) 0
  refine ⟨hdet, ?_⟩
  have h0 : 0 < (monodromy (fun t => oscMatrix c (k t)) T 0).det := by rw [hdet]; positivity
  have h1 : (monodromy (fun t => oscMatrix c (k t)) T 0).det ≤ 1 := by
    rw [hdet, Real.exp_le_one_iff]; nlinarith
  rw [FloquetUnstable, exists_one_lt_norm_iff h0 h1, hdet]

/-- **The exact two-state boundary under positive damping.** For `ẍ + 2c ẋ + k(t) x = 0` with
`c > 0` (`k` continuous and `T`-periodic): every multiplier lies strictly inside the unit circle
iff `|tr M| < 1 + e^{−2cT}`; every multiplier with `|μ| ≥ 1` is real; `−1` is a multiplier iff
`tr M = −(1 + e^{−2cT})` and `+1` iff `tr M = 1 + e^{−2cT}`. Instability can only arise through
a real multiplier crossing `±1`. -/
@[tmio T, powerlib_foundation] theorem damped_boundary {c T : ℝ} {k : ℝ → ℝ}
    (hk : Continuous k) (hkP : Periodic k T) (hc : 0 < c) (hT : 0 < T) :
    (LTI.SchurStable (monodromy (fun t => oscMatrix c (k t)) T 0) ↔
        |(monodromy (fun t => oscMatrix c (k t)) T 0).trace| < 1 + Real.exp (-(2 * c) * T)) ∧
      (∀ μ ∈ spectrum ℂ ((monodromy (fun t => oscMatrix c (k t)) T 0).map (algebraMap ℝ ℂ)),
        1 ≤ ‖μ‖ → μ.im = 0) ∧
      ((-1 : ℂ) ∈ spectrum ℂ ((monodromy (fun t => oscMatrix c (k t)) T 0).map (algebraMap ℝ ℂ)) ↔
        (monodromy (fun t => oscMatrix c (k t)) T 0).trace = -(1 + Real.exp (-(2 * c) * T))) ∧
      ((1 : ℂ) ∈ spectrum ℂ ((monodromy (fun t => oscMatrix c (k t)) T 0).map (algebraMap ℝ ℂ)) ↔
        (monodromy (fun t => oscMatrix c (k t)) T 0).trace = 1 + Real.exp (-(2 * c) * T)) := by
  obtain ⟨hdet, -⟩ := damped_floquetUnstable_iff hk hkP hc.le hT
  have h1 : (monodromy (fun t => oscMatrix c (k t)) T 0).det < 1 := by
    rw [hdet, Real.exp_lt_one_iff]; nlinarith
  refine ⟨?_, fun μ hμ hn => im_eq_zero_of_one_le_norm h1 hμ hn, ?_, ?_⟩
  · rw [schurStable_iff_abs_trace_lt h1, hdet]
  · rw [neg_one_mem_spectrum_iff, hdet]
  · rw [one_mem_spectrum_iff, hdet]

end powerlib.Periodic
