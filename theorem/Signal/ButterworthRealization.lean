import theorem.Signal.Butterworth
import theorem.Numerics.StabilityFunctions
import theorem.SpecialFunctions.Elementary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Butterworth band-pass realization, phase and group delay, bilinear discretization

The realization of the Butterworth band-pass of `theorem/Signal/Butterworth.lean` by the
low-pass to band-pass substitution `s ↦ (s² + ω₀²)/(sB)` of the stable prototype `bwTF`, the
phase and group delay of an all-pole filter with poles in the open left half plane (the
prototype in particular), and the bilinear (Tustin) discretization
`s = (2/T)(z − 1)/(z + 1)`, `z = (1 + sT/2)/(1 − sT/2)`: stability is preserved, the imaginary
axis is mapped onto the unit circle with the frequency warping `ω = (2/T) tan(θ/2)`, and
pre-warping the band edges puts the digital `−3 dB` points exactly at the prescribed edges.

Scope.
* Analog filters as explicit rational functions of `s ∈ ℂ`: the prototype `bwTF n 1` with poles
  `bwPole n 1 k` (`n ≥ 1`), the band-pass
  `H(s) = (sB)ⁿ / ∏_{k<n} (s² − s_k B s + ω₀²)`, `ω₀² = ω_l ω_u`, `B = ω_u − ω_l`,
  `0 < ω_l < ω_u`. An all-pole filter is `K / ∏_{k<n} (s − p_k)` with arbitrary complex poles
  `p_k`; phase and group delay are evaluated on `s = jω`.
* Discrete time: the digital filter is the analog one evaluated at `s = (2/T)(z − 1)/(z + 1)`,
  `T > 0` the sampling interval, `z ≠ −1`; its frequency response is read on `z = e^{jθ}`,
  `θ ∈ (0, π)` (rad/sample). The pole map `z = (1 + sT/2)/(1 − sT/2)` is the stability function
  `Numerics.stabTrap` of the trapezoidal rule at `sT`.
* Not formalized: the coefficient form of the digital filter (MATLAB `butter`), numerical
  roundoff, the detrending of §3.2, and forward–backward (zero-phase) filtering.

Source: ENTSO-E/WindEurope Technical Group on Forced Oscillations Report (2 July 2026) §3.2
("a band-pass Butterworth filter … band of 0.10–2 Hz", applied to 10 Hz data), §5.2
("sixth-order Butterworth bandpass filter"); the standard low-pass to band-pass transform and
bilinear transform with pre-warping (Oppenheim–Schafer, *Discrete-Time Signal Processing*, §7.1).

Results.
* Band-pass realization: `bpRoot_re_neg` (every root of `s² − pBs + c`, `Re p < 0`, `B, c > 0`,
  lies in the open left half plane), `bpTF`, `bpTF_eq` (`H(s) = bwTF n 1 ((s² + ω₀²)/(sB))`,
  `s ≠ 0`), `bpTF_den_re_neg` (stability: every root of the denominator has `Re s < 0`),
  `normSq_bpTF` (`|H(jω)|² = bpSq`, the magnitude of the wave-1 module), `normSq_bpTF_edges`
  (`−3 dB` at `ω_l`, `ω_u`).
* Phase and group delay: `phase`
  (`φ(ω) = −Σ_k arg(jω − p_k)`), `groupDelay` (`τ(ω) = Σ_k (−Re p_k)/|jω − p_k|²`),
  `allPole_jω_eq` (`H(jω) = |H(jω)| e^{jφ(ω)}`: `φ` is a phase of `H(jω)`), `hasDerivAt_phase`
  (`φ' = −τ`), `groupDelay_pos`, `phase_strictAnti` (left-half-plane poles); for the prototype
  `bwTF_jω_eq`, `bw_hasDerivAt_phase`, `bw_groupDelay_pos`, `bw_phase_strictAnti`.
* Bilinear transform: `tustin`, `tustin_stabTrap`, `stabTrap_tustin`, `tustin_eq_iff` (the two
  maps are inverse), `norm_lt_one_of_tustin_re_neg`, `norm_lt_one_of_prod_tustin` (a stable
  all-pole filter discretizes to poles inside the unit circle), `norm_stabTrap_eq_one_iff` (the
  imaginary axis goes to the unit circle), `tustin_exp` (`e^{jθ} ↦ j(2/T) tan(θ/2)`),
  `exp_ne_neg_one` (`e^{jθ} ≠ −1` for `cos(θ/2) ≠ 0`), `stabTrap_jω`
  (`jω ↦ e^{j 2 arctan(ωT/2)}`), `two_mul_arctan_half_lt` (warping compresses:
  `2 arctan(x/2) < x` for `x > 0`).
* Digital band-pass: `dbpTF`, `dbpTF_den_norm_lt_one` (stable), `normSq_dbpTF`
  (`|H_d(e^{jθ})|² = bpSq` at `ω = (2/T) tan(θ/2)`), `normSq_dbpTF_prewarp` (pre-warped edges
  `ω_{l,u} = (2/T) tan(θ_{l,u}/2)` give `−3 dB` exactly at `θ_l`, `θ_u`),
  `dbpTF_edges_unwarped` (without pre-warping the digital `−3 dB` points of the edges
  `ω_{l,u}` are at `θ = 2 arctan(ω_{l,u} T/2) < ω_{l,u} T`), `report_band_digital` (the report's
  `0.1–2 Hz` band at `10 Hz`: pre-warped edges exact; the unwarped `2 Hz` edge moves to
  `(10/π) arctan(π/5) Hz < 2 Hz`).

Sharpening (phase). The principal argument of `H(jω)` agrees with
`φ(ω) = −Σ_k arg(jω − s_k)` only modulo `2π` (each term lies in `(−π/2, π/2)`, so `φ` ranges over
`(−nπ/2, nπ/2)`); `φ` is the continuous phase of `H(jω)` (`allPole_jω_eq`), and it is this phase
that decreases strictly with group delay `τ = −φ' > 0`. The band-pass edges of §3.2 at `10 Hz`
are exact only after pre-warping (`report_band_digital`).

Family and connection conclusions.
* None: this module defines no family; every result is an identity or inequality of explicit
  rational functions.
-/

noncomputable section
namespace powerlib.Signal
open Complex Finset

/-! ## The low-pass to band-pass realization -/

/-- Every root of `s² − pBs + c` with `Re p < 0`, `B > 0`, `c > 0` lies in the open left half
plane: `Re s (|s|² + c) = B Re p |s|²`. -/
@[tmio T, powerlib_foundation] theorem bpRoot_re_neg {p s : ℂ} {B c : ℝ} (hp : p.re < 0)
    (hB : 0 < B) (hc : 0 < c) (hs : s ^ 2 - p * B * s + c = 0) : s.re < 0 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    have := congrArg Complex.re hs
    simp at this
    linarith
  have hre := congrArg Complex.re hs
  have him := congrArg Complex.im hs
  simp only [sub_re, add_re, mul_re, pow_two, ofReal_re, ofReal_im, zero_re, sub_im, add_im,
    mul_im, zero_im] at hre him
  have key : s.re * (s.re ^ 2 + s.im ^ 2 + c) = B * p.re * (s.re ^ 2 + s.im ^ 2) := by
    linear_combination s.re * hre + s.im * him
  have hpos : 0 < s.re ^ 2 + s.im ^ 2 := by
    have : s.re ≠ 0 ∨ s.im ≠ 0 := by
      by_contra h
      push Not at h
      exact hs0 (Complex.ext h.1 h.2)
    rcases this with h | h
    · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg s.im]
    · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg s.re]
  have hrhs : B * p.re * (s.re ^ 2 + s.im ^ 2) < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hB hp) hpos
  by_contra hnn
  push Not at hnn
  have : 0 ≤ s.re * (s.re ^ 2 + s.im ^ 2 + c) := mul_nonneg hnn (by positivity)
  linarith

/-- The Butterworth band-pass realized from the prototype `bwTF n 1`:
`H(s) = (sB)ⁿ / ∏_{k<n} (s² − s_k B s + ω₀²)`, `B = ω_u − ω_l`, `ω₀² = ω_l ω_u`. -/
def bpTF (n : ℕ) (ωl ωu : ℝ) (s : ℂ) : ℂ :=
  (s * ((ωu - ωl : ℝ) : ℂ)) ^ n /
    ∏ k ∈ range n, (s ^ 2 - bwPole n 1 k * ((ωu - ωl : ℝ) : ℂ) * s + ((ωl * ωu : ℝ) : ℂ))

/-- The realization is the prototype at the band-pass substitution `(s² + ω₀²)/(sB)`. -/
@[tmio T, powerlib_foundation] theorem bpTF_eq (n : ℕ) {ωl ωu : ℝ} (hlu : ωl ≠ ωu) {s : ℂ}
    (hs : s ≠ 0) :
    bpTF n ωl ωu s =
      bwTF n 1 ((s ^ 2 + ((ωl * ωu : ℝ) : ℂ)) / (s * ((ωu - ωl : ℝ) : ℂ))) := by
  have hB : ((ωu - ωl : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hlu.symm
  have hsB : s * ((ωu - ωl : ℝ) : ℂ) ≠ 0 := mul_ne_zero hs hB
  have hfac : ∀ k, (s ^ 2 + ((ωl * ωu : ℝ) : ℂ)) / (s * ((ωu - ωl : ℝ) : ℂ)) - bwPole n 1 k =
      (s ^ 2 - bwPole n 1 k * ((ωu - ωl : ℝ) : ℂ) * s + ((ωl * ωu : ℝ) : ℂ)) /
        (s * ((ωu - ωl : ℝ) : ℂ)) := fun k => by
    field_simp
    ring
  rw [bwTF, prod_congr rfl (fun k _ => hfac k), prod_div_distrib, prod_const, card_range,
    Complex.ofReal_one, one_pow, one_div_div, bpTF]

/-- **Stability of the band-pass realization.** Every root of its denominator lies in the open
left half plane (`0 < ω_l < ω_u`). -/
@[tmio T, powerlib_foundation] theorem bpTF_den_re_neg (n : ℕ) {ωl ωu : ℝ} (hl : 0 < ωl)
    (hlu : ωl < ωu) {s : ℂ}
    (h : ∏ k ∈ range n, (s ^ 2 - bwPole n 1 k * ((ωu - ωl : ℝ) : ℂ) * s + ((ωl * ωu : ℝ) : ℂ))
      = 0) : s.re < 0 := by
  obtain ⟨k, hk, hk0⟩ := prod_eq_zero_iff.mp h
  exact bpRoot_re_neg (bwPole_re_neg one_pos (mem_range.mp hk)) (sub_pos.mpr hlu)
    (mul_pos hl (hl.trans hlu)) hk0

/-- The realization has the band-pass magnitude of `Signal.Butterworth`:
`|H(jω)|² = bpSq n ω_l ω_u ω` for `ω ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem normSq_bpTF {n : ℕ} (hn : 0 < n) {ωl ωu : ℝ}
    (hlu : ωl ≠ ωu) {ω : ℝ} (hω : ω ≠ 0) : ‖bpTF n ωl ωu (ω * I)‖ ^ 2 = bpSq n ωl ωu ω := by
  have hωI : (ω : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hω) I_ne_zero
  have hB : (ωu - ωl : ℝ) ≠ 0 := sub_ne_zero.mpr hlu.symm
  have harg : (((ω : ℂ) * I) ^ 2 + ((ωl * ωu : ℝ) : ℂ)) / ((ω : ℂ) * I * ((ωu - ωl : ℝ) : ℂ)) =
      (bpArg ωl ωu ω : ℂ) * I := by
    have hω' : (ω : ℂ) ≠ 0 := by exact_mod_cast hω
    have hB' : ((ωu - ωl : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hB
    have hq : (bpArg ωl ωu ω : ℂ) * ((ω : ℂ) * ((ωu - ωl : ℝ) : ℂ)) =
        (ω : ℂ) ^ 2 - ((ωl * ωu : ℝ) : ℂ) := by
      rw [bpArg]
      push_cast
      have hB'' : (ωu : ℂ) - ωl ≠ 0 := by exact_mod_cast hB
      field_simp
    rw [div_eq_iff (mul_ne_zero hωI hB')]
    linear_combination (-I ^ 2) * hq + ((ωl * ωu : ℝ) : ℂ) * I_sq
  rw [bpTF_eq n hlu hωI, harg, normSq_bwTF hn one_pos, bpSq]

/-- The realization is `−3 dB` exactly at both band edges. -/
@[tmio T, powerlib_foundation] theorem normSq_bpTF_edges {n : ℕ} (hn : 0 < n) {ωl ωu : ℝ}
    (hl : 0 < ωl) (hlu : ωl < ωu) :
    ‖bpTF n ωl ωu (ωl * I)‖ ^ 2 = 1 / 2 ∧ ‖bpTF n ωl ωu (ωu * I)‖ ^ 2 = 1 / 2 := by
  rw [normSq_bpTF hn hlu.ne hl.ne', normSq_bpTF hn hlu.ne (hl.trans hlu).ne']
  exact bpSq_edges n hl hlu

/-! ## Phase and group delay of an all-pole filter -/

/-- The phase `φ(ω) = −Σ_{k<n} arg(jω − p_k)` of `K / ∏_{k<n} (s − p_k)` on `s = jω`. -/
def phase (p : ℕ → ℂ) (n : ℕ) (ω : ℝ) : ℝ := -∑ k ∈ range n, arg ((ω : ℂ) * I - p k)

/-- The group delay `τ(ω) = Σ_{k<n} (−Re p_k)/|jω − p_k|²`. -/
def groupDelay (p : ℕ → ℂ) (n : ℕ) (ω : ℝ) : ℝ :=
  ∑ k ∈ range n, -(p k).re / ‖(ω : ℂ) * I - p k‖ ^ 2

/-- `φ` is a phase of the frequency response: `K/∏(jω − p_k) = |K/∏(jω − p_k)| e^{jφ(ω)}`
(`K ≥ 0`). -/
@[tmio T, powerlib_foundation] theorem allPole_jω_eq {K : ℝ} (hK : 0 ≤ K) (p : ℕ → ℂ) (n : ℕ)
    (ω : ℝ) :
    (K : ℂ) / ∏ k ∈ range n, ((ω : ℂ) * I - p k) =
      ‖(K : ℂ) / ∏ k ∈ range n, ((ω : ℂ) * I - p k)‖ * cexp (phase p n ω * I) := by
  have hprod : ∏ k ∈ range n, ((ω : ℂ) * I - p k) =
      ((∏ k ∈ range n, ‖(ω : ℂ) * I - p k‖ : ℝ) : ℂ) *
        cexp ((∑ k ∈ range n, arg ((ω : ℂ) * I - p k) : ℝ) * I) := by
    push_cast
    rw [sum_mul, Complex.exp_sum, ← prod_mul_distrib]
    refine prod_congr rfl fun k _ => (norm_mul_exp_arg_mul_I _).symm
  rw [hprod, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one,
    abs_of_nonneg (prod_nonneg fun k _ => norm_nonneg _), phase]
  push_cast
  rw [neg_mul, Complex.exp_neg, div_mul_eq_div_div, div_eq_mul_inv]

/-- The phase of a filter with poles in the open left half plane has derivative `−τ(ω)`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_phase {p : ℕ → ℂ} {n : ℕ}
    (hp : ∀ k < n, (p k).re < 0) (ω : ℝ) : HasDerivAt (phase p n) (-groupDelay p n ω) ω := by
  have hφ : phase p n =
      fun ω => -∑ k ∈ range n, Real.arctan ((ω - (p k).im) / (-(p k).re)) := by
    funext ω
    rw [phase]
    congr 1
    refine sum_congr rfl fun k hk => ?_
    have hre : 0 < ((ω : ℂ) * I - p k).re := by
      simp only [sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
      linarith [hp k (mem_range.mp hk)]
    rw [SpecialFunctions.arg_eq_arctan hre]
    congr 1
    simp only [sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    ring_nf
  rw [hφ, groupDelay]
  refine HasDerivAt.neg (HasDerivAt.fun_sum
    (A := fun k ω => Real.arctan ((ω - (p k).im) / (-(p k).re))) fun k hk => ?_)
  have h1 : HasDerivAt (fun x : ℝ => (x - (p k).im) / (-(p k).re)) (1 / (-(p k).re)) ω :=
    ((hasDerivAt_id ω).sub_const ((p k).im)).div_const (-(p k).re)
  have h2 := (Real.hasDerivAt_arctan ((ω - (p k).im) / (-(p k).re))).comp ω h1
  refine h2.congr_deriv ?_
  have ha : (p k).re ≠ 0 := by linarith [hp k (mem_range.mp hk)]
  have hpos : 0 < (p k).re ^ 2 + (ω - (p k).im) ^ 2 := by
    have := sq_pos_of_ne_zero ha
    nlinarith [sq_nonneg (ω - (p k).im)]
  have hn : ‖(ω : ℂ) * I - p k‖ ^ 2 = (p k).re ^ 2 + (ω - (p k).im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    ring
  rw [hn]
  have ha' : -(p k).re ≠ 0 := neg_ne_zero.mpr ha
  field_simp

/-- With at least one pole, all in the open left half plane, the group delay is positive. -/
@[tmio T, powerlib_foundation] theorem groupDelay_pos {p : ℕ → ℂ} {n : ℕ} (hn : 0 < n)
    (hp : ∀ k < n, (p k).re < 0) (ω : ℝ) : 0 < groupDelay p n ω := by
  refine sum_pos (fun k hk => ?_) (nonempty_range_iff.mpr hn.ne')
  have hk := hp k (mem_range.mp hk)
  have hne : (ω : ℂ) * I - p k ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp only [sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, zero_re] at this
    linarith
  have := norm_pos_iff.mpr hne
  exact div_pos (by linarith) (by positivity)

/-- With at least one pole, all in the open left half plane, the phase decreases strictly. -/
@[tmio T, powerlib_foundation] theorem phase_strictAnti {p : ℕ → ℂ} {n : ℕ} (hn : 0 < n)
    (hp : ∀ k < n, (p k).re < 0) : StrictAnti (phase p n) :=
  strictAnti_of_deriv_neg fun ω => by
    rw [(hasDerivAt_phase hp ω).deriv, neg_lt_zero]
    exact groupDelay_pos hn hp ω

/-- The prototype on the imaginary axis: `H(jω) = |H(jω)| e^{jφ(ω)}`. -/
@[tmio T, powerlib_foundation] theorem bwTF_jω_eq (n : ℕ) {ωc : ℝ} (hωc : 0 ≤ ωc) (ω : ℝ) :
    bwTF n ωc (ω * I) = ‖bwTF n ωc (ω * I)‖ * cexp (phase (bwPole n ωc) n ω * I) := by
  have h := allPole_jω_eq (pow_nonneg hωc n) (bwPole n ωc) n ω
  push_cast at h
  exact h

@[tmio T, powerlib_foundation] theorem bw_hasDerivAt_phase (n : ℕ) {ωc : ℝ} (hωc : 0 < ωc)
    (ω : ℝ) : HasDerivAt (phase (bwPole n ωc) n) (-groupDelay (bwPole n ωc) n ω) ω :=
  hasDerivAt_phase (fun _ hk => bwPole_re_neg hωc hk) ω

/-- The group delay of the Butterworth prototype is positive at every frequency. -/
@[tmio T, powerlib_foundation] theorem bw_groupDelay_pos {n : ℕ} (hn : 0 < n) {ωc : ℝ}
    (hωc : 0 < ωc) (ω : ℝ) : 0 < groupDelay (bwPole n ωc) n ω :=
  groupDelay_pos hn (fun _ hk => bwPole_re_neg hωc hk) ω

/-- The phase of the Butterworth prototype decreases strictly. -/
@[tmio T, powerlib_foundation] theorem bw_phase_strictAnti {n : ℕ} (hn : 0 < n) {ωc : ℝ}
    (hωc : 0 < ωc) : StrictAnti (phase (bwPole n ωc) n) :=
  phase_strictAnti hn (fun _ hk => bwPole_re_neg hωc hk)

/-! ## The bilinear transform -/

open Numerics (stabTrap stabTrap_norm_lt_one_iff stabTrap_norm_le_one_iff)

/-- The bilinear (Tustin) substitution `s = (2/T)(z − 1)/(z + 1)`. -/
def tustin (T : ℝ) (z : ℂ) : ℂ := 2 / T * ((z - 1) / (z + 1))

/-- The pole map `z = (1 + sT/2)/(1 − sT/2)` inverts the substitution. -/
@[tmio T, powerlib_foundation] theorem tustin_stabTrap {T : ℝ} (hT : T ≠ 0) {s : ℂ}
    (hs : (T : ℂ) * s ≠ 2) : tustin T (stabTrap (T * s)) = s := by
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  have hd : 1 - (T : ℂ) * s / 2 ≠ 0 := fun h => hs (by linear_combination -2 * h)
  rw [tustin, stabTrap, div_add_one hd, div_sub_one hd, div_div_div_cancel_right₀ hd]
  field_simp
  ring

@[tmio T, powerlib_foundation] theorem stabTrap_tustin {T : ℝ} (hT : T ≠ 0) {z : ℂ}
    (hz : z ≠ -1) : stabTrap (T * tustin T z) = z := by
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  have hz' : z + 1 ≠ 0 := fun h => hz (by linear_combination h)
  rw [stabTrap, tustin]
  have hd : 1 - (T : ℂ) * (2 / T * ((z - 1) / (z + 1))) / 2 = 2 / (z + 1) := by
    field_simp; ring
  rw [hd, div_eq_iff (div_ne_zero two_ne_zero hz')]
  field_simp
  ring

@[tmio T, powerlib_foundation] theorem tustin_eq_iff {T : ℝ} (hT : T ≠ 0) {z p : ℂ}
    (hz : z ≠ -1) (hp : (T : ℂ) * p ≠ 2) : tustin T z = p ↔ z = stabTrap (T * p) := by
  constructor
  · rintro rfl; exact (stabTrap_tustin hT hz).symm
  · rintro rfl; exact tustin_stabTrap hT hp

/-- A point whose bilinear image lies in the open left half plane is inside the unit circle. -/
@[tmio T, powerlib_foundation] theorem norm_lt_one_of_tustin_re_neg {T : ℝ} (hT : 0 < T) {z : ℂ}
    (hz : z ≠ -1) (h : (tustin T z).re < 0) : ‖z‖ < 1 := by
  have hre : ((T : ℂ) * tustin T z).re < 0 := by
    rw [re_ofReal_mul]; exact mul_neg_of_pos_of_neg hT h
  have h2 : (T : ℂ) * tustin T z ≠ 2 := fun he => by
    rw [he] at hre; norm_num at hre
  rw [← stabTrap_tustin hT.ne' hz]
  exact (stabTrap_norm_lt_one_iff h2).mpr hre

/-- **Stability is preserved.** The bilinear discretization `K / ∏_{k<n} (s(z) − p_k)` of an
all-pole filter with poles in the open left half plane has all its poles (`z ≠ −1`) inside the
unit circle. -/
@[tmio T, powerlib_foundation] theorem norm_lt_one_of_prod_tustin {T : ℝ} (hT : 0 < T)
    {p : ℕ → ℂ} {n : ℕ} (hp : ∀ k < n, (p k).re < 0) {z : ℂ} (hz : z ≠ -1)
    (h : ∏ k ∈ range n, (tustin T z - p k) = 0) : ‖z‖ < 1 := by
  obtain ⟨k, hk, hk0⟩ := prod_eq_zero_iff.mp h
  refine norm_lt_one_of_tustin_re_neg hT hz ?_
  rw [sub_eq_zero.mp hk0]
  exact hp k (mem_range.mp hk)

/-- The imaginary axis is mapped onto the unit circle: `|z(s)| = 1 ↔ Re s = 0`. -/
@[tmio T, powerlib_foundation] theorem norm_stabTrap_eq_one_iff {T : ℝ} (hT : 0 < T) {s : ℂ}
    (hs : (T : ℂ) * s ≠ 2) : ‖stabTrap (T * s)‖ = 1 ↔ s.re = 0 := by
  have hre : ((T : ℂ) * s).re = T * s.re := re_ofReal_mul T s
  constructor
  · intro h
    have h1 := (stabTrap_norm_le_one_iff hs).mp h.le
    have h2 : ¬ ((T : ℂ) * s).re < 0 := fun hlt => by
      have := (stabTrap_norm_lt_one_iff hs).mpr hlt
      rw [h] at this
      exact lt_irrefl _ this
    rw [hre] at h1 h2
    push Not at h2
    exact (mul_eq_zero.mp (le_antisymm h1 h2)).resolve_left hT.ne'
  · intro h
    refine le_antisymm ((stabTrap_norm_le_one_iff hs).mpr (by rw [hre, h, mul_zero])) ?_
    by_contra hlt
    push Not at hlt
    have := (stabTrap_norm_lt_one_iff hs).mp hlt
    rw [hre, h, mul_zero] at this
    exact lt_irrefl _ this

/-- Half-angle factorizations: with `u = cos(θ/2) + j sin(θ/2) = e^{jθ/2}`,
`e^{jθ} = u²`, `e^{jθ} − 1 = 2j sin(θ/2) u` and `e^{jθ} + 1 = 2 cos(θ/2) u`. -/
@[tmio T, powerlib_foundation] private theorem exp_half_factor (θ : ℝ) :
    cexp (θ * I) - 1 =
        2 * (Real.sin (θ / 2) : ℂ) * I * ((Real.cos (θ / 2) : ℂ) + (Real.sin (θ / 2) : ℂ) * I) ∧
      cexp (θ * I) + 1 =
        2 * (Real.cos (θ / 2) : ℂ) * ((Real.cos (θ / 2) : ℂ) + (Real.sin (θ / 2) : ℂ) * I) ∧
      (Real.cos (θ / 2) : ℂ) + (Real.sin (θ / 2) : ℂ) * I ≠ 0 := by
  set c : ℂ := (Real.cos (θ / 2) : ℂ)
  set s : ℂ := (Real.sin (θ / 2) : ℂ)
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    simp only [c, s]; exact_mod_cast Real.cos_sq_add_sin_sq (θ / 2)
  have hu : c + s * I = cexp (((θ / 2 : ℝ) : ℂ) * I) := by
    simp only [c, s]; rw [← Complex.cos_add_sin_I]; push_cast; ring
  have he : cexp (θ * I) = (c + s * I) ^ 2 := by
    rw [hu, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  refine ⟨?_, ?_, by rw [hu]; exact Complex.exp_ne_zero _⟩
  · rw [he]; linear_combination hcs - s ^ 2 * I_sq
  · rw [he]; linear_combination (-1 : ℂ) * hcs + s ^ 2 * I_sq

/-- `e^{jθ} ≠ −1` when `cos(θ/2) ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem exp_ne_neg_one {θ : ℝ} (hc : Real.cos (θ / 2) ≠ 0) :
    cexp (θ * I) ≠ -1 := by
  obtain ⟨-, h, hu⟩ := exp_half_factor θ
  intro he
  rw [he, neg_add_cancel] at h
  exact mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast hc)) hu h.symm

/-- **Frequency warping.** The unit circle is mapped onto the imaginary axis:
`s(e^{jθ}) = j (2/T) tan(θ/2)` for `cos(θ/2) ≠ 0`. -/
@[tmio T, powerlib_foundation] theorem tustin_exp {T : ℝ} (hT : T ≠ 0) {θ : ℝ}
    (hc : Real.cos (θ / 2) ≠ 0) :
    tustin T (cexp (θ * I)) = ((2 / T * Real.tan (θ / 2) : ℝ) : ℂ) * I := by
  obtain ⟨h1, h2, hu⟩ := exp_half_factor θ
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  have hc' : (Real.cos (θ / 2) : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [tustin, h1, h2, Real.tan_eq_sin_div_cos]
  push_cast at hu hc' ⊢
  field_simp

/-- The imaginary axis goes to the unit circle with the inverse warping:
`z(jω) = e^{j 2 arctan(ωT/2)}`. -/
@[tmio T, powerlib_foundation] theorem stabTrap_jω {T : ℝ} (hT : T ≠ 0) (ω : ℝ) :
    stabTrap (T * (ω * I)) = cexp ((2 * Real.arctan (ω * T / 2) : ℝ) * I) := by
  have hc : Real.cos ((2 * Real.arctan (ω * T / 2)) / 2) ≠ 0 := by
    rw [mul_div_cancel_left₀ _ two_ne_zero]; exact (Real.cos_arctan_pos _).ne'
  have h := tustin_exp hT hc
  rw [mul_div_cancel_left₀ _ two_ne_zero, Real.tan_arctan,
    show 2 / T * (ω * T / 2) = ω by field_simp] at h
  rw [← h, stabTrap_tustin hT (exp_ne_neg_one hc)]

/-- Warping compresses: `2 arctan(x/2) < x` for `x > 0`, so an analog frequency `ω` lands at the
digital frequency `2 arctan(ωT/2) < ωT`. -/
@[tmio T, powerlib_foundation] theorem two_mul_arctan_half_lt {x : ℝ} (hx : 0 < x) :
    2 * Real.arctan (x / 2) < x := by
  have := Real.arctan_lt_self (half_pos hx)
  linarith

/-! ## The digital band-pass -/

/-- The digital Butterworth band-pass: the analog realization at `s = (2/T)(z − 1)/(z + 1)`. -/
def dbpTF (n : ℕ) (ωl ωu T : ℝ) (z : ℂ) : ℂ := bpTF n ωl ωu (tustin T z)

/-- **The digital band-pass is stable**: every pole (`z ≠ −1`, a root of the substituted
denominator) lies inside the unit circle. -/
@[tmio T, powerlib_foundation] theorem dbpTF_den_norm_lt_one (n : ℕ) {ωl ωu T : ℝ} (hl : 0 < ωl)
    (hlu : ωl < ωu) (hT : 0 < T) {z : ℂ} (hz : z ≠ -1)
    (h : ∏ k ∈ range n, (tustin T z ^ 2 - bwPole n 1 k * ((ωu - ωl : ℝ) : ℂ) * tustin T z +
      ((ωl * ωu : ℝ) : ℂ)) = 0) : ‖z‖ < 1 :=
  norm_lt_one_of_tustin_re_neg hT hz (bpTF_den_re_neg n hl hlu h)

/-- The digital magnitude on the unit circle is the analog one at the warped frequency:
`|H_d(e^{jθ})|² = bpSq n ω_l ω_u ((2/T) tan(θ/2))` for `θ ∈ (0, π)`. -/
@[tmio T, powerlib_foundation] theorem normSq_dbpTF {n : ℕ} (hn : 0 < n) {ωl ωu T : ℝ}
    (hlu : ωl ≠ ωu) (hT : 0 < T) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    ‖dbpTF n ωl ωu T (cexp (θ * I))‖ ^ 2 = bpSq n ωl ωu (2 / T * Real.tan (θ / 2)) := by
  have h0 : 0 < θ / 2 := half_pos hθ.1
  have h1 : θ / 2 < Real.pi / 2 := by linarith [hθ.2]
  have hc : Real.cos (θ / 2) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩).ne'
  have ht : 0 < 2 / T * Real.tan (θ / 2) :=
    mul_pos (div_pos two_pos hT) (Real.tan_pos_of_pos_of_lt_pi_div_two h0 h1)
  rw [dbpTF, tustin_exp hT.ne' hc, normSq_bpTF hn hlu ht.ne']

/-- **Pre-warping.** For prescribed digital band edges `0 < θ_l < θ_u < π` (rad/sample), the
analog edges `ω_{l,u} = (2/T) tan(θ_{l,u}/2)` make the digital band-pass `−3 dB` exactly at
`θ_l` and `θ_u`. -/
@[tmio T, powerlib_foundation] theorem normSq_dbpTF_prewarp {n : ℕ} (hn : 0 < n) {T θl θu : ℝ}
    (hT : 0 < T) (h0 : 0 < θl) (hlu : θl < θu) (hπ : θu < Real.pi) :
    ‖dbpTF n (2 / T * Real.tan (θl / 2)) (2 / T * Real.tan (θu / 2)) T (cexp (θl * I))‖ ^ 2 =
        1 / 2 ∧
      ‖dbpTF n (2 / T * Real.tan (θl / 2)) (2 / T * Real.tan (θu / 2)) T (cexp (θu * I))‖ ^ 2 =
        1 / 2 := by
  have hpi := Real.pi_pos
  have hl : 0 < 2 / T * Real.tan (θl / 2) :=
    mul_pos (div_pos two_pos hT) (Real.tan_pos_of_pos_of_lt_pi_div_two (half_pos h0)
      (by linarith))
  have hlt : 2 / T * Real.tan (θl / 2) < 2 / T * Real.tan (θu / 2) :=
    mul_lt_mul_of_pos_left (Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith) (by linarith)
      (by linarith)) (div_pos two_pos hT)
  rw [normSq_dbpTF hn hlt.ne hT ⟨h0, by linarith⟩, normSq_dbpTF hn hlt.ne hT ⟨by linarith, hπ⟩]
  exact bpSq_edges n hl hlt

/-- **Without pre-warping.** With the analog edges `ω_l < ω_u` used directly, the digital
`−3 dB` points are `θ = 2 arctan(ω_{l,u} T/2)`, strictly below the intended `ω_{l,u} T`. -/
@[tmio T, powerlib_foundation] theorem dbpTF_edges_unwarped {n : ℕ} (hn : 0 < n) {ωl ωu T : ℝ}
    (hl : 0 < ωl) (hlu : ωl < ωu) (hT : 0 < T) :
    (‖dbpTF n ωl ωu T (cexp ((2 * Real.arctan (ωl * T / 2) : ℝ) * I))‖ ^ 2 = 1 / 2 ∧
        2 * Real.arctan (ωl * T / 2) < ωl * T) ∧
      (‖dbpTF n ωl ωu T (cexp ((2 * Real.arctan (ωu * T / 2) : ℝ) * I))‖ ^ 2 = 1 / 2 ∧
        2 * Real.arctan (ωu * T / 2) < ωu * T) := by
  have hu : 0 < ωu := hl.trans hlu
  have key : ∀ ω : ℝ, 0 < ω →
      ‖dbpTF n ωl ωu T (cexp ((2 * Real.arctan (ω * T / 2) : ℝ) * I))‖ ^ 2 = bpSq n ωl ωu ω ∧
        2 * Real.arctan (ω * T / 2) < ω * T := fun ω hω => by
    have hx : 0 < ω * T / 2 := by positivity
    refine ⟨?_, two_mul_arctan_half_lt (mul_pos hω hT)⟩
    have hθ : 2 * Real.arctan (ω * T / 2) ∈ Set.Ioo 0 Real.pi :=
      ⟨by linarith [Real.arctan_pos.mpr hx], by linarith [Real.arctan_lt_pi_div_two (ω * T / 2)]⟩
    rw [normSq_dbpTF hn hlu.ne hT hθ, mul_div_cancel_left₀ _ two_ne_zero, Real.tan_arctan,
      show 2 / T * (ω * T / 2) = ω by field_simp]
  obtain ⟨hl1, hl2⟩ := key ωl hl
  obtain ⟨hu1, hu2⟩ := key ωu hu
  obtain ⟨e1, e2⟩ := bpSq_edges n hl hlu
  exact ⟨⟨hl1.trans e1, hl2⟩, ⟨hu1.trans e2, hu2⟩⟩

/-- §3.2 at `10 Hz` sampling (`T = 1/10 s`), band `0.1–2 Hz` (digital edges `θ = 2πf T`:
`π/50` and `2π/5` rad/sample). Pre-warped analog edges `20 tan(π/100)` and `20 tan(π/5)` rad/s
put the digital `−3 dB` points exactly at `0.1 Hz` and `2 Hz`; the unwarped edge `2 Hz`
(`4π` rad/s) lands at `θ = 2 arctan(π/5)`, i.e. at `(10/π) arctan(π/5) Hz < 2 Hz`. -/
@[tmio T, powerlib_foundation] theorem report_band_digital {n : ℕ} (hn : 0 < n) :
    ‖dbpTF n (20 * Real.tan (Real.pi / 100)) (20 * Real.tan (Real.pi / 5)) (1 / 10)
        (cexp ((Real.pi / 50 : ℝ) * I))‖ ^ 2 = 1 / 2 ∧
      ‖dbpTF n (20 * Real.tan (Real.pi / 100)) (20 * Real.tan (Real.pi / 5)) (1 / 10)
        (cexp ((2 * Real.pi / 5 : ℝ) * I))‖ ^ 2 = 1 / 2 ∧
      ‖dbpTF n (Real.pi / 5) (4 * Real.pi) (1 / 10)
        (cexp ((2 * Real.arctan (Real.pi / 5) : ℝ) * I))‖ ^ 2 = 1 / 2 ∧
      10 / Real.pi * Real.arctan (Real.pi / 5) < 2 := by
  have hpi := Real.pi_pos
  obtain ⟨h1, h2⟩ := normSq_dbpTF_prewarp hn (T := 1 / 10) (θl := Real.pi / 50)
    (θu := 2 * Real.pi / 5) (by norm_num) (by positivity) (by linarith) (by linarith)
  rw [show (2 : ℝ) / (1 / 10) = 20 by norm_num, show Real.pi / 50 / 2 = Real.pi / 100 by ring,
    show 2 * Real.pi / 5 / 2 = Real.pi / 5 by ring] at h1 h2
  obtain ⟨-, ⟨h3, h4⟩⟩ := dbpTF_edges_unwarped hn (ωl := Real.pi / 5) (ωu := 4 * Real.pi)
    (T := 1 / 10) (by positivity) (by linarith) (by norm_num)
  rw [show 4 * Real.pi * (1 / 10) / 2 = Real.pi / 5 by ring] at h3 h4
  refine ⟨h1, h2, h3, ?_⟩
  rw [div_mul_eq_mul_div, div_lt_iff₀ hpi]
  linarith

end powerlib.Signal
