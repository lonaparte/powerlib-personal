import theorem.Attributes
import dependencies.Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! # Butterworth low-pass prototype and band-pass magnitude

The magnitude of the order-`n` Butterworth low-pass prototype and of the band-pass obtained by
the standard frequency transform: the `−3 dB` points, monotonicity, maximal flatness, the
asymptotic slope `−20 n` dB per decade and what "slopes of over −100 dB/decade" requires of the
order.

Scope.
* Magnitude functions of a real frequency (any unit; the transform is scale invariant): the
  prototype `G_n(ω)² = 1 / (1 + (ω/ω_c)^{2n})` and the band-pass
  `|H(ω)|² = G_n((ω² − ω₀²)/(ω B))²` with `ω₀² = ω_l ω_u`, `B = ω_u − ω_l`; decibels
  `L = 10 log₁₀ |·|²`. The prototype order `n` is the order of the low-pass prototype; the
  band-pass has denominator degree `2n`.
* Analog filters: the magnitude responses, and the realization of the prototype by its `n`
  left-half-plane poles `s_k = ω_c e^{jπ(2k+n+1)/(2n)}` (`ω_c > 0`, `n ≥ 1`). Phase, group delay,
  the pole realization of the band-pass and the discretization at the sampling rate (MATLAB's
  `butter` at 10 Hz) are outside this module; so are the detrending steps of §3.2.

Source: ENTSO-E/WindEurope Technical Group on Forced Oscillations Report (2 July 2026) §3.2 ("a
band-pass Butterworth filter … band of 0.10–2 Hz … A filter order of 6, with slopes of over
−100 dB/decade", Fig. 5), §5.2 ("sixth-order Butterworth bandpass filter").

Results.
* Prototype: `bwSq`, `bwDB`, `bwSq_cutoff` (`G_n(ω_c)² = 1/2`, `−3 dB`), `bwSq_strictAntiOn`
  (strictly decreasing on `ω ≥ 0`), `bwSq_flat` (`G_n² = 1 − (ω/ω_c)^{2n} + r`,
  `0 ≤ r ≤ (ω/ω_c)^{4n}`: maximal flatness).
* Slopes: `bwDB_drop_eq`, `bwDB_drop_lt` (the drop over any decade is less than `20 n` dB),
  `tendsto_drop`, `tendsto_bwDB_drop` (it tends to `20 n` dB), `exists_bwDB_drop_gt_iff` (a drop
  of more than `s ≥ 0` dB per decade occurs iff `s < 20 n`), `slope_over_hundred_iff` (more than
  `100` dB per decade iff `n ≥ 6`).
* Realization: `bwPole`, `bwTF` (`H(s) = ω_cⁿ / ∏_{k<n} (s − s_k)`), `bwPole_re_neg` (every pole
  in the open left half-plane), `conj_bwPole` (conjugate symmetry), `prod_sub_rootsNegOne`
  (`∏ (x − e^{jπ(2k+1)/n}) = xⁿ + 1`), `normSq_bwTF` (`|H(jω)|² = G_n(ω)²`).
* Band-pass: `bpArg`, `bpSq`, `bpDB`, `bpSq_edges` (`−3 dB` exactly at `ω_l` and `ω_u`),
  `bpSq_center` (unit gain at `ω₀ = √(ω_l ω_u)`), `bpSq_symm` (log-symmetry
  `|H(ω₀²/ω)| = |H(ω)|`), `bpDB_eq`, `tendsto_bpDB_drop_atTop`, `tendsto_bpDB_drop_zero`
  (`−20 n` dB per decade above and below the band), `bpSq_report_band` (`0.1–2 Hz`: edges at
  `−3 dB`, centre `√(1/5) Hz`).

Correction (§3.2, §5.2). "Order 6" must be the prototype order `n = 6` (asymptotic slopes
`±120` dB per decade): the drop per decade of the prototype never exceeds `20 n` dB
(`bwDB_drop_lt`), so `−100` dB per decade is reached only for `n ≥ 6`
(`slope_over_hundred_iff`), and the band-pass has the same asymptotic slopes `±20 n` dB per
decade (`tendsto_bpDB_drop_atTop`, `tendsto_bpDB_drop_zero`). A band-pass of total order 6
(prototype `n = 3`, e.g. MATLAB `butter(3, [f_l f_u])`) has only `±60` dB per decade.

Family and connection conclusions.
* None: this module defines no family; every result is a property of explicit magnitude
  functions.
-/

noncomputable section
namespace powerlib.Signal
open Real Set Filter Topology

/-! ## The low-pass prototype -/

/-- Squared magnitude `G_n(ω)² = 1 / (1 + (ω/ω_c)^{2n})` of the order-`n` Butterworth low-pass
prototype with cutoff `ω_c`. -/
def bwSq (n : ℕ) (ωc ω : ℝ) : ℝ := 1 / (1 + (ω / ωc) ^ (2 * n))

/-- Magnitude in decibels, `10 log₁₀ G²`. -/
def bwDB (n : ℕ) (ωc ω : ℝ) : ℝ := 10 * logb 10 (bwSq n ωc ω)

/-- `−3 dB` at the cutoff: `G_n(ω_c)² = 1/2`. -/
@[tmio T, powerlib_foundation] theorem bwSq_cutoff (n : ℕ) {ωc : ℝ} (hωc : ωc ≠ 0) :
    bwSq n ωc ωc = 1 / 2 := by
  rw [bwSq, div_self hωc, one_pow]
  norm_num

/-- The prototype magnitude decreases strictly on `ω ≥ 0` (`n ≥ 1`, `ω_c > 0`). -/
@[tmio T, powerlib_foundation] theorem bwSq_strictAntiOn {n : ℕ} (hn : 0 < n) {ωc : ℝ}
    (hωc : 0 < ωc) : StrictAntiOn (bwSq n ωc) (Ici 0) := by
  intro ω hω ω' hω' h
  simp only [bwSq]
  have h1 : (ω / ωc) ^ (2 * n) < (ω' / ωc) ^ (2 * n) :=
    pow_lt_pow_left₀ (div_lt_div_of_pos_right h hωc) (div_nonneg hω hωc.le) (by omega)
  have h0 := (even_two_mul n).pow_nonneg (ω / ωc)
  exact one_div_lt_one_div_of_lt (by linarith) (by linarith)

/-- Maximal flatness: `G_n² = 1 − (ω/ω_c)^{2n} + r` with `0 ≤ r ≤ (ω/ω_c)^{4n}`, i.e.
`G_n² = 1 − (ω/ω_c)^{2n} + O(ω^{4n})`: the first `2n − 1` derivatives of `G_n²` vanish at `0`. -/
@[tmio T, powerlib_foundation] theorem bwSq_flat (n : ℕ) (ωc ω : ℝ) :
    0 ≤ bwSq n ωc ω - (1 - (ω / ωc) ^ (2 * n)) ∧
      bwSq n ωc ω - (1 - (ω / ωc) ^ (2 * n)) ≤ (ω / ωc) ^ (4 * n) := by
  have key : ∀ u : ℝ, 0 ≤ u → 0 ≤ 1 / (1 + u) - (1 - u) ∧ 1 / (1 + u) - (1 - u) ≤ u ^ 2 :=
    fun u hu => by
      have he : 1 / (1 + u) - (1 - u) = u ^ 2 / (1 + u) := by field_simp; ring
      rw [he]
      exact ⟨by positivity, div_le_self (by positivity) (by linarith)⟩
  have h4 : (ω / ωc) ^ (4 * n) = ((ω / ωc) ^ (2 * n)) ^ 2 := by rw [← pow_mul]; ring_nf
  rw [h4]
  exact key _ ((even_two_mul n).pow_nonneg _)

/-- The drop of the prototype over one decade above `ω`:
`L(ω) − L(10 ω) = 10 log₁₀ ((1 + 10^{2n} u) / (1 + u))`, `u = (ω/ω_c)^{2n}`. -/
@[tmio T, powerlib_foundation] theorem bwDB_drop_eq (n : ℕ) (ωc ω : ℝ) :
    bwDB n ωc ω - bwDB n ωc (10 * ω) =
      10 * logb 10 ((1 + 10 ^ (2 * n) * (ω / ωc) ^ (2 * n)) / (1 + (ω / ωc) ^ (2 * n))) := by
  have hu := (even_two_mul n).pow_nonneg (ω / ωc)
  have h10 : (10 * ω / ωc) ^ (2 * n) = 10 ^ (2 * n) * (ω / ωc) ^ (2 * n) := by
    rw [mul_div_assoc, mul_pow]
  simp only [bwDB, bwSq, one_div, logb_inv, h10]
  rw [logb_div (by positivity) (by positivity)]
  ring

/-- The drop over a decade is less than `20 n` dB at every frequency (`n ≥ 1`). -/
@[tmio T, powerlib_foundation] theorem bwDB_drop_lt {n : ℕ} (hn : 0 < n) (ωc ω : ℝ) :
    bwDB n ωc ω - bwDB n ωc (10 * ω) < 20 * n := by
  rw [bwDB_drop_eq]
  set u := (ω / ωc) ^ (2 * n)
  have hu : 0 ≤ u := (even_two_mul n).pow_nonneg _
  have hK : (1 : ℝ) < 10 ^ (2 * n) := one_lt_pow₀ (by norm_num) (by omega)
  have hlt : (1 + 10 ^ (2 * n) * u) / (1 + u) < 10 ^ (2 * n) := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  have := logb_lt_logb (b := 10) (by norm_num) (by positivity) hlt
  rw [logb_pow, logb_self_eq_one (by norm_num)] at this
  push_cast at this
  linarith

/-- Limit of a per-decade drop: if `v → ∞` and `ρ → K > 0`, then
`10 log₁₀ ((1 + ρ v)/(1 + v)) → 10 log₁₀ K`. -/
@[tmio T, powerlib_foundation] theorem tendsto_drop {α : Type*} {l : Filter α} {v ρ : α → ℝ}
    {K : ℝ} (hK : 0 < K) (hv : Tendsto v l atTop) (hρ : Tendsto ρ l (𝓝 K)) :
    Tendsto (fun x => 10 * logb 10 ((1 + ρ x * v x) / (1 + v x))) l (𝓝 (10 * logb 10 K)) := by
  have h1 : Tendsto (fun x => 1 + v x) l atTop := tendsto_atTop_add_const_left l 1 hv
  have h2 : Tendsto (fun x => (ρ x - 1) / (1 + v x)) l (𝓝 0) :=
    (hρ.sub_const 1).div_atTop h1
  have h3 : Tendsto (fun x => ρ x - (ρ x - 1) / (1 + v x)) l (𝓝 K) := by
    simpa using hρ.sub h2
  have h4 : Tendsto (fun x => (1 + ρ x * v x) / (1 + v x)) l (𝓝 K) := by
    refine h3.congr' ?_
    filter_upwards [h1.eventually_gt_atTop 0] with x hx
    field_simp
    ring
  exact ((continuousAt_logb hK.ne').tendsto.comp h4).const_mul 10

/-- The asymptotic slope of the order-`n` prototype is `−20 n` dB per decade:
`L(ω) − L(10 ω) → 20 n` as `ω → ∞` (`n ≥ 1`, `ω_c > 0`). -/
@[tmio T, powerlib_foundation] theorem tendsto_bwDB_drop {n : ℕ} (hn : 0 < n) {ωc : ℝ}
    (hωc : 0 < ωc) :
    Tendsto (fun ω => bwDB n ωc ω - bwDB n ωc (10 * ω)) atTop (𝓝 (20 * n)) := by
  have hv : Tendsto (fun ω : ℝ => (ω / ωc) ^ (2 * n)) atTop atTop :=
    (tendsto_pow_atTop (by omega)).comp (tendsto_id.atTop_div_const hωc)
  have := tendsto_drop (K := 10 ^ (2 * n)) (by positivity) hv tendsto_const_nhds
  rw [logb_pow, logb_self_eq_one (by norm_num)] at this
  simp only [← bwDB_drop_eq] at this
  convert this using 2
  push_cast
  ring

/-- A drop of more than `s ≥ 0` dB over some decade occurs exactly when `s < 20 n`. -/
@[tmio T, powerlib_foundation] theorem exists_bwDB_drop_gt_iff (n : ℕ) {ωc s : ℝ} (hωc : 0 < ωc)
    (hs : 0 ≤ s) : (∃ ω, s < bwDB n ωc ω - bwDB n ωc (10 * ω)) ↔ s < 20 * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [bwDB, bwSq, mul_zero, pow_zero, sub_self, Nat.cast_zero]
    constructor
    · rintro ⟨_, h⟩; linarith
    · intro h; linarith
  constructor
  · rintro ⟨ω, h⟩
    exact h.trans (bwDB_drop_lt hn ωc ω)
  · intro h
    exact ((tendsto_bwDB_drop hn hωc).eventually (lt_mem_nhds h)).exists

/-- §3.2: "slopes of over −100 dB/decade" hold exactly for prototype order `n ≥ 6`; a filter of
total order `6` (prototype `n = 3`, `60 dB` per decade) never reaches them. -/
@[tmio T, powerlib_foundation] theorem slope_over_hundred_iff (n : ℕ) {ωc : ℝ} (hωc : 0 < ωc) :
    (∃ ω, 100 < bwDB n ωc ω - bwDB n ωc (10 * ω)) ↔ 6 ≤ n := by
  rw [exists_bwDB_drop_gt_iff n hωc (by norm_num)]
  constructor
  · intro h
    by_contra hlt
    have : (n : ℝ) ≤ 5 := by exact_mod_cast (show n ≤ 5 by omega)
    linarith
  · intro h
    have : (6 : ℝ) ≤ n := by exact_mod_cast h
    linarith

/-! ## Realization of the prototype by its poles -/

section Realization
open Finset Complex Polynomial

/-- The poles `s_k = ω_c e^{jπ(2k + n + 1)/(2n)}`, `k < n`. -/
def bwPole (n : ℕ) (ωc : ℝ) (k : ℕ) : ℂ :=
  ωc * Complex.exp (((π * (2 * k + n + 1) / (2 * n) : ℝ) : ℂ) * I)

/-- `H(s) = ω_cⁿ / ∏_{k<n} (s − s_k)`. -/
def bwTF (n : ℕ) (ωc : ℝ) (s : ℂ) : ℂ := (ωc : ℂ) ^ n / ∏ k ∈ range n, (s - bwPole n ωc k)

/-- Every pole lies in the open left half-plane: the realization is stable. -/
@[tmio T, powerlib_foundation] theorem bwPole_re_neg {n : ℕ} {ωc : ℝ} (hωc : 0 < ωc) {k : ℕ} (hk : k < n) :
    (bwPole n ωc k).re < 0 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
  rw [bwPole, re_ofReal_mul, exp_ofReal_mul_I_re]
  refine mul_neg_of_pos_of_neg hωc (Real.cos_neg_of_pi_div_two_lt_of_lt ?_ ?_)
  · rw [lt_div_iff₀ (by positivity)]; nlinarith [Real.pi_pos, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  · rw [div_lt_iff₀ (by positivity)]; nlinarith [Real.pi_pos]

/-- The poles are conjugate-symmetric: `conj s_k = s_{n−1−k}`. -/
@[tmio T, powerlib_foundation] theorem conj_bwPole {n : ℕ} {ωc : ℝ} {k : ℕ} (hk : k < n) :
    (starRingEnd ℂ) (bwPole n ωc k) = bwPole n ωc (n - 1 - k) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hcast : ((n - 1 - k : ℕ) : ℝ) = n - 1 - k := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
  rw [bwPole, bwPole, map_mul, conj_ofReal, ← Complex.exp_conj, map_mul, conj_ofReal, conj_I, hcast]
  congr 1
  have h2pi : Complex.exp (((π * (2 * (n - 1 - k : ℝ) + n + 1) / (2 * n) : ℝ) : ℂ) * I) =
      Complex.exp ((-(π * (2 * k + n + 1) / (2 * n)) : ℝ) * I + (1 : ℕ) * (2 * π * I)) := by
    congr 1
    push_cast
    field_simp
    ring
  rw [h2pi, Complex.exp_add, exp_nat_mul_two_pi_mul_I, mul_one]
  congr 1
  push_cast
  ring

/-- `∏_{k<n} (x − e^{jπ(2k+1)/n}) = xⁿ + 1` (Mathlib's `X_pow_sub_C_eq_prod` at the roots of
`−1`). -/
@[tmio T, powerlib_foundation] theorem prod_sub_rootsNegOne {n : ℕ} (hn : 0 < n) (x : ℂ) :
    ∏ k ∈ range n, (x - Complex.exp (((π * (2 * k + 1) / n : ℝ) : ℂ) * I)) = x ^ n + 1 := by
  have hn0 : n ≠ 0 := by omega
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hα : Complex.exp (π * I / n) ^ n = -1 := by
    rw [← Complex.exp_nat_mul, show (n : ℂ) * (π * I / n) = π * I by field_simp,
      Complex.exp_pi_mul_I]
  have h := X_pow_sub_C_eq_prod (Complex.isPrimitiveRoot_exp n hn0) hn hα
  have he := congrArg (Polynomial.eval x) h
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_prod] at he
  rw [sub_neg_eq_add] at he
  rw [he]
  refine prod_congr rfl fun k _ => ?_
  congr 1
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp

/-- The realization has the Butterworth magnitude: `|H(jω)|² = 1 / (1 + (ω/ω_c)^{2n})`. -/
@[tmio T, powerlib_foundation] theorem normSq_bwTF {n : ℕ} (hn : 0 < n) {ωc : ℝ} (hωc : 0 < ωc) (ω : ℝ) :
    ‖bwTF n ωc (ω * I)‖ ^ 2 = bwSq n ωc ω := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hωcC : (ωc : ℂ) ≠ 0 := by exact_mod_cast hωc.ne'
  -- reflection: `‖jω − s_{n−1−k}‖ = ‖jω + s_k‖`
  have hrefl : ∏ k ∈ range n, ‖(ω : ℂ) * I - bwPole n ωc k‖ =
      ∏ k ∈ range n, ‖(ω : ℂ) * I + bwPole n ωc k‖ := by
    rw [← prod_range_reflect (fun k => ‖(ω : ℂ) * I - bwPole n ωc k‖) n]
    refine prod_congr rfl fun k hk => ?_
    have hk' := mem_range.mp hk
    rw [← conj_bwPole hk']
    rw [show (ω : ℂ) * I - (starRingEnd ℂ) (bwPole n ωc k) =
        (starRingEnd ℂ) (-((ω : ℂ) * I + bwPole n ωc k)) by
      simp only [map_neg, map_add, map_mul, conj_ofReal, conj_I]; ring, Complex.norm_conj,
      norm_neg]
  -- the product of `(jω − s_k)(jω + s_k) = ω_c² (r_k − (ω/ω_c)²)`
  have hpair : ∀ k : ℕ, ((ω : ℂ) * I - bwPole n ωc k) * ((ω : ℂ) * I + bwPole n ωc k) =
      -((ωc : ℂ) ^ 2) * ((((ω / ωc) ^ 2 : ℝ) : ℂ) -
        Complex.exp (((π * (2 * k + 1) / n : ℝ) : ℂ) * I)) := fun k => by
    have hs : bwPole n ωc k ^ 2 = -((ωc : ℂ) ^ 2) * Complex.exp (((π * (2 * k + 1) / n : ℝ) : ℂ) * I) := by
      rw [bwPole, mul_pow, ← Complex.exp_nat_mul]
      have : Complex.exp (((2 : ℕ) : ℂ) * (((π * (2 * k + n + 1) / (2 * n) : ℝ) : ℂ) * I)) =
          Complex.exp (((π * (2 * k + 1) / n : ℝ) : ℂ) * I + π * I) := by
        congr 1; push_cast; field_simp; ring
      rw [this, Complex.exp_add, Complex.exp_pi_mul_I]
      ring
    have hx : (((ω / ωc) ^ 2 : ℝ) : ℂ) * (ωc : ℂ) ^ 2 = (ω : ℂ) ^ 2 := by
      push_cast; field_simp
    linear_combination (-1 : ℂ) * hs + hx + (ω : ℂ) ^ 2 * I_sq
  have hprod : ‖∏ k ∈ range n, (((ω : ℂ) * I - bwPole n ωc k) * ((ω : ℂ) * I + bwPole n ωc k))‖ =
      ωc ^ (2 * n) * (1 + (ω / ωc) ^ (2 * n)) := by
    rw [prod_congr rfl fun k _ => hpair k, prod_mul_distrib, prod_const, card_range,
      prod_sub_rootsNegOne hn, norm_mul, norm_pow, norm_neg, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hωc, ← pow_mul]
    have : ((((ω / ωc) ^ 2 : ℝ) : ℂ) ^ n + 1) = (((1 + (ω / ωc) ^ (2 * n)) : ℝ) : ℂ) := by
      push_cast; rw [pow_mul]; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by
      have := (even_two_mul n).pow_nonneg (ω / ωc); linarith)]
  have hden : ‖∏ k ∈ range n, ((ω : ℂ) * I - bwPole n ωc k)‖ ^ 2 =
      ωc ^ (2 * n) * (1 + (ω / ωc) ^ (2 * n)) := by
    rw [← hprod, prod_mul_distrib, norm_mul, sq]
    congr 1
    rw [norm_prod, norm_prod, hrefl]
  have h1 : 0 < 1 + (ω / ωc) ^ (2 * n) := by
    have := (even_two_mul n).pow_nonneg (ω / ωc); linarith
  have h2 : (0 : ℝ) < ωc ^ (2 * n) := by positivity
  rw [bwTF, norm_div, div_pow, hden, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hωc, ← pow_mul, bwSq, mul_comm n 2]
  field_simp

end Realization

/-! ## The band-pass transform -/

/-- The low-pass to band-pass transform `ω ↦ (ω² − ω_l ω_u) / (ω (ω_u − ω_l))`: centre
`ω₀ = √(ω_l ω_u)`, bandwidth `B = ω_u − ω_l`. -/
def bpArg (ωl ωu ω : ℝ) : ℝ := (ω ^ 2 - ωl * ωu) / (ω * (ωu - ωl))

/-- Squared magnitude of the order-`n` Butterworth band-pass on `[ω_l, ω_u]`:
`|H(ω)|² = 1 / (1 + ((ω² − ω₀²)/(ω B))^{2n})`. -/
def bpSq (n : ℕ) (ωl ωu ω : ℝ) : ℝ := bwSq n 1 (bpArg ωl ωu ω)

/-- Band-pass magnitude in decibels. -/
def bpDB (n : ℕ) (ωl ωu ω : ℝ) : ℝ := 10 * logb 10 (bpSq n ωl ωu ω)

/-- `−3 dB` exactly at both band edges. -/
@[tmio T, powerlib_foundation] theorem bpSq_edges (n : ℕ) {ωl ωu : ℝ} (hl : 0 < ωl)
    (hlu : ωl < ωu) : bpSq n ωl ωu ωl = 1 / 2 ∧ bpSq n ωl ωu ωu = 1 / 2 := by
  have hB : ωu - ωl ≠ 0 := sub_ne_zero.mpr hlu.ne'
  have hu : ωu ≠ 0 := (hl.trans hlu).ne'
  have h1 : bpArg ωl ωu ωl = -1 := by
    rw [bpArg, div_eq_iff (mul_ne_zero hl.ne' hB)]; ring
  have h2 : bpArg ωl ωu ωu = 1 := by
    rw [bpArg, div_eq_iff (mul_ne_zero hu hB)]; ring
  simp only [bpSq, bwSq, h1, h2, div_one, pow_mul, neg_one_sq, one_pow]
  norm_num

/-- Unit gain at the centre `ω₀ = √(ω_l ω_u)`. -/
@[tmio T, powerlib_foundation] theorem bpSq_center (n : ℕ) {ωl ωu : ℝ} (hn : 0 < n)
    (hl : 0 ≤ ωl * ωu) : bpSq n ωl ωu (√(ωl * ωu)) = 1 := by
  simp only [bpSq, bwSq, bpArg, sq_sqrt hl, sub_self, zero_div, div_one]
  rw [zero_pow (by omega)]
  norm_num

/-- Log-symmetry about the centre: `|H(ω₀²/ω)| = |H(ω)|`. -/
@[tmio T, powerlib_foundation] theorem bpSq_symm (n : ℕ) (ωl ωu : ℝ) {ω : ℝ} (hω : ω ≠ 0)
    (hlu : ωl * ωu ≠ 0) : bpSq n ωl ωu (ωl * ωu / ω) = bpSq n ωl ωu ω := by
  obtain ⟨hl', hu'⟩ := mul_ne_zero_iff.mp hlu
  have h : bpArg ωl ωu (ωl * ωu / ω) = -bpArg ωl ωu ω := by
    simp only [bpArg]
    rcases eq_or_ne (ωu - ωl) 0 with hB | hB
    · simp [hB]
    field_simp
    ring
  simp only [bpSq, bwSq, h, div_one, Even.neg_pow (even_two_mul n)]

/-- The band-pass in decibels as a function of the transform: `L = −10 log₁₀(1 + a^{2n})`. -/
@[tmio T, powerlib_foundation] theorem bpDB_eq (n : ℕ) (ωl ωu ω : ℝ) :
    bpDB n ωl ωu ω = -(10 * logb 10 (1 + bpArg ωl ωu ω ^ (2 * n))) := by
  simp only [bpDB, bpSq, bwSq, div_one, one_div, logb_inv]
  ring

/-- The band-pass falls off at `−20 n` dB per decade above the band: `L(ω) − L(10 ω) → 20 n` as
`ω → ∞`. -/
@[tmio T, powerlib_foundation] theorem tendsto_bpDB_drop_atTop {n : ℕ} (hn : 0 < n) {ωl ωu : ℝ}
    (hl : 0 < ωl) (hlu : ωl < ωu) :
    Tendsto (fun ω => bpDB n ωl ωu ω - bpDB n ωl ωu (10 * ω)) atTop (𝓝 (20 * n)) := by
  have hB : 0 < ωu - ωl := sub_pos.mpr hlu
  have hc : 0 < ωl * ωu := mul_pos hl (hl.trans hlu)
  have hinv : Tendsto (fun ω : ℝ => ω⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have ha : Tendsto (bpArg ωl ωu) atTop atTop := by
    have h1 : Tendsto (fun ω : ℝ => ω / (ωu - ωl) + (-(ωl * ωu / (ωu - ωl)) * ω⁻¹)) atTop atTop :=
      (tendsto_id.atTop_div_const hB).atTop_add (by simpa using hinv.const_mul (-(ωl * ωu / (ωu - ωl))))
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with ω hω
    simp only [bpArg]
    field_simp
    ring
  have hr : Tendsto (fun ω => bpArg ωl ωu (10 * ω) / bpArg ωl ωu ω) atTop (𝓝 10) := by
    have h2 : Tendsto (fun ω : ℝ => ωl * ωu * ω⁻¹ ^ 2) atTop (𝓝 0) := by
      simpa using (hinv.pow 2).const_mul (ωl * ωu)
    have h3 : Tendsto (fun ω : ℝ => (100 - ωl * ωu * ω⁻¹ ^ 2) / (10 * (1 - ωl * ωu * ω⁻¹ ^ 2)))
        atTop (𝓝 ((100 - 0) / (10 * (1 - 0)))) :=
      (tendsto_const_nhds.sub h2).div (tendsto_const_nhds.mul (tendsto_const_nhds.sub h2))
        (by norm_num)
    rw [show ((100 : ℝ) - 0) / (10 * (1 - 0)) = 10 by norm_num] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop (√(ωl * ωu))] with ω hω
    have hω0 : 0 < ω := (sqrt_nonneg _).trans_lt hω
    have hsq : ωl * ωu < ω ^ 2 := by
      have := mul_self_lt_mul_self (sqrt_nonneg _) hω
      rwa [mul_self_sqrt hc.le, ← sq] at this
    have hne : ω ^ 2 - ωl * ωu ≠ 0 := (sub_pos.mpr hsq).ne'
    simp only [bpArg]
    field_simp
    ring
  have hv : Tendsto (fun ω => bpArg ωl ωu ω ^ (2 * n)) atTop atTop :=
    (tendsto_pow_atTop (by omega)).comp ha
  have hρ := hr.pow (2 * n)
  have := tendsto_drop (K := 10 ^ (2 * n)) (by positivity) hv hρ
  rw [logb_pow, logb_self_eq_one (by norm_num)] at this
  push_cast at this
  convert this.congr' ?_ using 2
  · ring
  filter_upwards [ha.eventually_gt_atTop 0] with ω hω
  have h1 := (even_two_mul n).pow_nonneg (bpArg ωl ωu ω)
  have h2 := (even_two_mul n).pow_nonneg (bpArg ωl ωu (10 * ω))
  rw [bpDB_eq, bpDB_eq, div_pow, div_mul_cancel₀ _ (pow_pos hω _).ne',
    logb_div (by linarith) (by linarith)]
  ring

/-- By log-symmetry the band-pass also falls off at `−20 n` dB per decade below the band:
`L(ω) − L(ω/10) → 20 n` as `ω → 0⁺`. -/
@[tmio T, powerlib_foundation] theorem tendsto_bpDB_drop_zero {n : ℕ} (hn : 0 < n) {ωl ωu : ℝ}
    (hl : 0 < ωl) (hlu : ωl < ωu) :
    Tendsto (fun ω => bpDB n ωl ωu ω - bpDB n ωl ωu (ω / 10)) (𝓝[>] 0) (𝓝 (20 * n)) := by
  have hc : 0 < ωl * ωu := mul_pos hl (hl.trans hlu)
  have hinv : Tendsto (fun ω : ℝ => ωl * ωu / ω) (𝓝[>] 0) atTop := by
    simpa [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hc
  refine ((tendsto_bpDB_drop_atTop hn hl hlu).comp hinv).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ω (hω : 0 < ω)
  simp only [Function.comp, bpDB]
  rw [bpSq_symm n ωl ωu hω.ne' hc.ne', show 10 * (ωl * ωu / ω) = ωl * ωu / (ω / 10) by
    field_simp, bpSq_symm n ωl ωu (by positivity) hc.ne']

/-- The report's band `0.1–2 Hz` (in Hz; the transform is scale invariant): `−3 dB` at `0.1 Hz`
and `2 Hz`, unit gain at the centre `√(0.1 · 2) = √(1/5) Hz ≈ 0.447 Hz`. -/
@[tmio T, powerlib_foundation] theorem bpSq_report_band {n : ℕ} (hn : 0 < n) :
    bpSq n (1 / 10) 2 (1 / 10) = 1 / 2 ∧ bpSq n (1 / 10) 2 2 = 1 / 2 ∧
      bpSq n (1 / 10) 2 (√(1 / 5)) = 1 := by
  obtain ⟨h1, h2⟩ := bpSq_edges n (ωl := 1 / 10) (ωu := 2) (by norm_num) (by norm_num)
  refine ⟨h1, h2, ?_⟩
  rw [show (1 / 5 : ℝ) = 1 / 10 * 2 by norm_num]
  exact bpSq_center n hn (by norm_num)

end powerlib.Signal
