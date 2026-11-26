import theorem.LTI.Oscillator2

/-! # Start-up envelopes of natural and forced oscillations

The start-up stage of a one-mode oscillation `m ẍ + c ẋ + k x = f(t)`: the exact natural and
forced start-up waveforms, the peak-to-peak values over successive periods, their increments and
the logarithmic slope `S = σT` that separates a natural start-up (growing free response) from a
forced one (a decaying free response under a resonant drive), with the least-squares slope and
the threshold classifier of the method.

Scope.
* A real scalar second-order equation `m ẍ + c ẋ + k x = f(t)` with constant `m ≠ 0`, `c`, `k`,
  underdamped: `σ = −c/(2m)`, `ω_d² = k/m − σ² > 0` (eigenvalues `σ ± j ω_d`). Solutions are
  global differentiable curves `x` with derivative `v` and second derivative `a` (written out in
  the statements); `c < 0` (growing natural start-up, `σ > 0`) is allowed.
* Natural start-up: `f = 0`. Forced start-up: a sinusoidal input at the damped frequency
  `ω = ω_d` (resonance) with steady state `A₃ sin(ωt + φ₃)`, started from rest.
* The envelope model `E(t) = A e^{σt} + B`, the least-squares slope of arbitrary finite data and
  a threshold classifier on the slope. The nonlinear amplitude saturation that ends the start-up
  stage, varying system conditions and measured records are excluded.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.2, eqs. (3-1)–(3-5),
Steps 1–3 and Fig. 3-1; §3.1 (intrinsic damping of natural and forced oscillations).

Corrections and sharpenings.
* (3-4)–(3-5): from `x(0) = ẋ(0) = 0` the report deduces `φ₂ = φ₃`, `A₂ = −A₃`, i.e. the free
  component `−A₃ e^{σt} sin(ωt + φ₃)`. This is exact only when `σ sin φ₃ = 0`; in general the exact
  solution is `x(t) = A₃(1 − e^{σt}) sin(ωt + φ₃) + (σ/ω) A₃ sin φ₃ e^{σt} sin ωt`
  (`forced_startUp`), so the envelope (3-5) holds up to the explicit remainder
  `|σ/ω| |A₃| e^{σt}` (`forced_startUp_error`).
* Step 2: the increment `Y_i = X_i − X_{i−1}` of the peak-to-peak values of a natural start-up is
  exactly `X₀ (e^{σT} − 1) e^{(i−1)σT}` with `X₀` the peak-to-peak value of the first period
  (`natural_increment`), the form `A(e^{σT} − 1)e^{(i−1)σT}` of the report.

Results.
* `peakToPeak`, `peakToPeak_shift`, `peakToPeak_period` — if `x(t + T) = q x(t)`, `q ≥ 0`, the
  peak-to-peak value over a window shifted by `T` is `q` times the original; over the `i`-th
  period it is `qⁱ X₀`.
* `natural_eq_dampedResp`, `natural_eq_amplitude_phase`, `natural_shift` — every natural
  solution is the damped response `LTI.dampedResp` (uniqueness of solutions of the 2×2 companion
  system, `LTI.hasDerivAt_osc2`), i.e. `A e^{σt} sin(ω_d t + φ)` (3-2), and satisfies the exact
  period law `x(t + T) = e^{σT} x(t)`, `T = 2π/ω_d` (`LTI.dampedResp_add_half_period` twice).
* `natural_peakToPeak_succ`, `natural_peakToPeak`, `natural_peakToPeak_pos`, `natural_increment`,
  `natural_increment_pos`, `natural_log_increment` — Step 1: `X_{i+1} = e^{σT} X_i` exactly, so
  `X_i = e^{iσT} X₀`; `X₀ > 0` for a nonzero solution;
  `Y_i = X₀(e^{σT} − 1)e^{(i−1)σT}`, and for `σ > 0`: `Y_i > 0`,
  `ln Y_i = ln(X₀(e^{σT} − 1)) + (i − 1)σT`.
* `exists_steadyState`, `forced_startUp`, `forced_startUp_of_sin`, `forced_startUp_error` — a
  sinusoidal input `μ sin(ωt + θ)` has a sinusoidal steady state `A₃ sin(ωt + φ₃)`
  (`k − mω² + jcω ≠ 0`); the exact start-up from rest at `ω = ω_d` (above), its special case
  `σ sin φ₃ = 0`, and the remainder bound.
* `envelope`, `envelope_increment`, `envelope_increment_pos`, `log_envelope_increment` — for
  `E(t) = A e^{σt} + B`: `E(iT) − E((i−1)T) = A(e^{σT} − 1)e^{(i−1)σT}`; positive, with logarithm
  affine in `i` of slope `σT`, both for the natural envelope (3-3) (`A > 0`, `B = 0`, `σ > 0`) and
  the forced envelope (3-5) (`A = −A₃ < 0`, `B = A₃`, `σ < 0`); `natural_peakToPeak_eq_envelope`.
* `olsSlope`, `olsSlope_affine`, `sum_sq_sub_expect_pos` — the least-squares slope
  `Σ(uᵢ − ū)(zᵢ − z̄)/Σ(uᵢ − ū)²` (means `Finset.expect`) of data `zᵢ = z₀ + S uᵢ` is `S`; the
  abscissae `1, …, N` (`N ≥ 2`) have positive spread.
* `slope_natural`, `slope_envelope` — Step 3: the slope of `(i, ln Y_i)`, `i = 1..N`, is `S = σT`
  for every nonzero natural start-up with `σ > 0` and for every envelope of either kind.
* `Verdict`, `classify`, `classify_ne_forced`, `classify_eq_natural_iff`,
  `classify_ne_natural`, `classify_eq_forced_iff`, `classify_natural`, `classify_forced` — the
  threshold rule (`S > ε` natural, `S < −ε` forced, `ε ≥ 0`) never calls a natural start-up
  (`σ > 0`) forced nor a forced one at positive intrinsic damping (`σ < 0`) natural, and decides
  each as soon as `|σT| > ε` (always for `ε = 0`).
-/

noncomputable section
namespace powerlib.LTI.StartUp
open Set Matrix
open scoped Pointwise

/-! ## Peak-to-peak values -/

/-- Peak-to-peak value of `x` over `[a, b]`: `sup x − inf x`. -/
def peakToPeak (x : ℝ → ℝ) (a b : ℝ) : ℝ := sSup (x '' Icc a b) - sInf (x '' Icc a b)

/-- A shift law `x(t + T) = q x(t)`, `q ≥ 0`, scales the peak-to-peak value of a shifted window
by `q`. -/
@[tmio T, powerlib_foundation] theorem peakToPeak_shift {x : ℝ → ℝ} {T q : ℝ} (hq : 0 ≤ q)
    (hx : ∀ t, x (t + T) = q * x t) (a b : ℝ) :
    peakToPeak x (a + T) (b + T) = q * peakToPeak x a b := by
  have himg : x '' Icc (a + T) (b + T) = q • (x '' Icc a b) := by
    ext y
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨x (t - T), ⟨t - T, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩, ?_⟩
      have := hx (t - T)
      rw [sub_add_cancel] at this
      rw [this, smul_eq_mul]
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t + T, ⟨by linarith [ht.1], by linarith [ht.2]⟩, by rw [hx t, smul_eq_mul]⟩
  rw [peakToPeak, peakToPeak, himg, Real.sSup_smul_of_nonneg hq, Real.sInf_smul_of_nonneg hq,
    smul_eq_mul, smul_eq_mul, mul_sub]

/-- Over the `i`-th period `[iT, (i+1)T]` the peak-to-peak value is `qⁱ X₀`. -/
@[tmio T, powerlib_foundation] theorem peakToPeak_period {x : ℝ → ℝ} {T q : ℝ} (hq : 0 ≤ q)
    (hx : ∀ t, x (t + T) = q * x t) (i : ℕ) :
    peakToPeak x (i * T) ((i + 1) * T) = q ^ i * peakToPeak x 0 T := by
  induction i with
  | zero => simp
  | succ n ih =>
    have h := peakToPeak_shift hq hx (n * T) ((n + 1) * T)
    rw [show (n : ℝ) * T + T = ((n + 1 : ℕ) : ℝ) * T by push_cast; ring,
      show ((n : ℝ) + 1) * T + T = (((n + 1 : ℕ) : ℝ) + 1) * T by push_cast; ring] at h
    rw [h, ih, pow_succ]
    ring

/-! ## Natural start-up -/

@[tmio T, powerlib_foundation] private theorem lipschitzWith_mulVec
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    LipschitzWith ‖LinearMap.toContinuousLinearMap (Matrix.toLin' A)‖₊
      (fun y : Fin 2 → ℝ => A *ᵥ y) := by
  have h := (LinearMap.toContinuousLinearMap (Matrix.toLin' A)).lipschitzWith
  have hf : (fun y : Fin 2 → ℝ => A *ᵥ y) =
      ⇑(LinearMap.toContinuousLinearMap (Matrix.toLin' A)) := by
    funext y; simp
  rw [hf]; exact h

section Oscillator

variable {m c k σ ωd : ℝ}

/-- Every solution of the unforced equation `m ẍ + c ẋ + k x = 0` (`σ = −c/(2m)`,
`ω_d² = k/m − σ²`, `ω_d ≠ 0`) is the damped response `dampedResp (−σ) ω_d x(0) ẋ(0)`,
`x(t) = e^{σt}(x(0) cos ω_d t + ((ẋ(0) − σ x(0))/ω_d) sin ω_d t)`. -/
@[tmio T, powerlib_foundation] theorem natural_eq_dampedResp (hm : m ≠ 0)
    (hσ : σ = -(c / (2 * m))) (hωd : ωd ^ 2 = k / m - σ ^ 2) (hωd0 : ωd ≠ 0)
    {x v a : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = 0) (t : ℝ) :
    x t = dampedResp (-σ) ωd (x 0) (v 0) t := by
  set A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -(k / m), -(c / m)] with hA
  have htr : A.trace = -2 * -σ := by
    rw [hA, Matrix.trace_fin_two_of, hσ]; field_simp; ring
  have hdet : A.det = (-σ) ^ 2 + ωd ^ 2 := by
    rw [hA, Matrix.det_fin_two_of, hωd]; ring
  have hy : ∀ s, HasDerivAt (fun s => ![x s, v s]) (A *ᵥ ![x s, v s]) s ∧
      ![x s, v s] ∈ (univ : Set (Fin 2 → ℝ)) := by
    intro s
    refine ⟨?_, trivial⟩
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa [hA, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hx s
    · have ha : a s = -(k / m) * x s + -(c / m) * v s := by
        have := heq s; field_simp; linear_combination this
      simpa [hA, Matrix.mulVec, dotProduct, Fin.sum_univ_two, ha] using hv s
  have hg : ∀ s, HasDerivAt (fun s => osc2 A (-σ) ωd ![x 0, v 0] s)
      (A *ᵥ osc2 A (-σ) ωd ![x 0, v 0] s) s ∧
      osc2 A (-σ) ωd ![x 0, v 0] s ∈ (univ : Set (Fin 2 → ℝ)) :=
    fun s => ⟨hasDerivAt_osc2 htr hdet hωd0 _ s, trivial⟩
  have heq' := ODE_solution_unique_univ (v := fun _ y => A *ᵥ y) (s := fun _ => univ) (t₀ := 0)
    (fun _ => (lipschitzWith_mulVec A).lipschitzOnWith) hy hg (by simp)
  have h0 := congrFun (congrFun heq' t) 0
  simp only [Matrix.cons_val_zero] at h0
  rw [h0]
  simp only [osc2, dampedResp, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, hA, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  simp
  ring

/-- (3-2): every natural solution is `A e^{σt} sin(ω_d t + φ)`, with `A = 0` exactly for the zero
solution. -/
@[tmio T, powerlib_foundation] theorem natural_eq_amplitude_phase (hm : m ≠ 0)
    (hσ : σ = -(c / (2 * m))) (hωd : ωd ^ 2 = k / m - σ ^ 2) (hωd0 : ωd ≠ 0)
    {x v a : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = 0) :
    ∃ A φ : ℝ, (A = 0 ↔ x 0 = 0 ∧ v 0 = 0) ∧
      ∀ t, x t = A * Real.exp (σ * t) * Real.sin (ωd * t + φ) := by
  set z : ℂ := ⟨(v 0 - σ * x 0) / ωd, x 0⟩
  refine ⟨‖z‖, Complex.arg z, ?_, fun t => ?_⟩
  · rw [norm_eq_zero, Complex.ext_iff]
    simp only [z, Complex.zero_re, Complex.zero_im, div_eq_zero_iff, hωd0, or_false]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, by rw [h2] at h1; linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by rw [h1, h2]; ring, h1⟩
  · rw [natural_eq_dampedResp hm hσ hωd hωd0 hx hv heq t, dampedResp, Real.sin_add]
    have hre := Complex.norm_mul_cos_arg z
    have him := Complex.norm_mul_sin_arg z
    simp only [z] at hre him
    rw [show -(-σ * t) = σ * t by ring]
    linear_combination (-(Real.exp (σ * t) * Real.sin (ωd * t))) * hre -
      (Real.exp (σ * t) * Real.cos (ωd * t)) * him

/-- The exact period law of a natural solution: `x(t + T) = e^{σT} x(t)`, `T = 2π/ω_d`. -/
@[tmio T, powerlib_foundation] theorem natural_shift (hm : m ≠ 0) (hσ : σ = -(c / (2 * m)))
    (hωd : ωd ^ 2 = k / m - σ ^ 2) (hωd0 : ωd ≠ 0)
    {x v a : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = 0) (t : ℝ) :
    x (t + 2 * Real.pi / ωd) = Real.exp (σ * (2 * Real.pi / ωd)) * x t := by
  have hcl := natural_eq_dampedResp hm hσ hωd hωd0 hx hv heq
  rw [hcl (t + 2 * Real.pi / ωd), hcl t,
    show t + 2 * Real.pi / ωd = (t + Real.pi / ωd) + Real.pi / ωd by ring,
    dampedResp_add_half_period hωd0, dampedResp_add_half_period hωd0]
  have : Real.exp (σ * (2 * Real.pi / ωd)) =
      Real.exp (-(-σ * (Real.pi / ωd))) * Real.exp (-(-σ * (Real.pi / ωd))) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]
  ring

/-- The peak-to-peak value of the `i`-th period of a natural start-up: `X_i = e^{iσT} X₀`. -/
@[tmio T, powerlib_foundation] theorem natural_peakToPeak (hm : m ≠ 0) (hσ : σ = -(c / (2 * m)))
    (hωd : ωd ^ 2 = k / m - σ ^ 2) (hωd0 : ωd ≠ 0)
    {x v a : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = 0) (i : ℕ) :
    peakToPeak x (i * (2 * Real.pi / ωd)) ((i + 1) * (2 * Real.pi / ωd)) =
      Real.exp (i * (σ * (2 * Real.pi / ωd))) * peakToPeak x 0 (2 * Real.pi / ωd) := by
  rw [peakToPeak_period (Real.exp_pos _).le (natural_shift hm hσ hωd hωd0 hx hv heq) i,
    ← Real.exp_nat_mul]

/-- Successive periods of a natural start-up: `X_{i+1} = e^{σT} X_i` exactly, `T = 2π/ω_d`. -/
@[tmio T, powerlib_foundation] theorem natural_peakToPeak_succ (hm : m ≠ 0)
    (hσ : σ = -(c / (2 * m))) (hωd : ωd ^ 2 = k / m - σ ^ 2) (hωd0 : ωd ≠ 0)
    {x v a : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = 0) (i : ℕ) :
    peakToPeak x ((i + 1) * (2 * Real.pi / ωd)) ((i + 2) * (2 * Real.pi / ωd)) =
      Real.exp (σ * (2 * Real.pi / ωd)) *
        peakToPeak x (i * (2 * Real.pi / ωd)) ((i + 1) * (2 * Real.pi / ωd)) := by
  have h := peakToPeak_shift (Real.exp_pos _).le (natural_shift hm hσ hωd hωd0 hx hv heq)
    (i * (2 * Real.pi / ωd)) ((i + 1) * (2 * Real.pi / ωd))
  rw [show (i : ℝ) * (2 * Real.pi / ωd) + 2 * Real.pi / ωd = (i + 1) * (2 * Real.pi / ωd) by ring,
    show ((i : ℝ) + 1) * (2 * Real.pi / ωd) + 2 * Real.pi / ωd = (i + 2) * (2 * Real.pi / ωd) by
      ring] at h
  exact h

/-- The first-period peak-to-peak value of a nonzero natural solution is positive. -/
@[tmio T, powerlib_foundation] theorem natural_peakToPeak_pos (hm : m ≠ 0)
    (hσ : σ = -(c / (2 * m))) (hωd : ωd ^ 2 = k / m - σ ^ 2) (hωd0 : 0 < ωd)
    {x v a : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = 0) (hne : x 0 ≠ 0 ∨ v 0 ≠ 0) :
    0 < peakToPeak x 0 (2 * Real.pi / ωd) := by
  have hcl := natural_eq_dampedResp hm hσ hωd hωd0.ne' hx hv heq
  have hpi := Real.pi_pos
  -- a time `s ∈ [0, π/(2ω_d)]` with `x s ≠ 0`
  obtain ⟨s, hs0, hs1, hxs⟩ : ∃ s, 0 ≤ s ∧ s ≤ Real.pi / (2 * ωd) ∧ x s ≠ 0 := by
    by_cases h0 : x 0 = 0
    · refine ⟨Real.pi / (2 * ωd), by positivity, le_rfl, ?_⟩
      have hv0 : v 0 ≠ 0 := hne.resolve_left (not_not.mpr h0)
      rw [hcl, dampedResp, h0,
        show ωd * (Real.pi / (2 * ωd)) = Real.pi / 2 by field_simp,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      simp only [mul_zero, zero_add, mul_one, add_zero]
      exact mul_ne_zero (Real.exp_pos _).ne' (div_ne_zero hv0 hωd0.ne')
    · exact ⟨0, le_rfl, by positivity, h0⟩
  have hhalf : x (s + Real.pi / ωd) = -Real.exp (-(-σ * (Real.pi / ωd))) * x s := by
    rw [hcl (s + Real.pi / ωd), hcl s, dampedResp_add_half_period hωd0.ne']
  have hcont : Continuous x := continuous_iff_continuousAt.mpr fun t => (hx t).continuousAt
  have hT : 0 < 2 * Real.pi / ωd := by positivity
  have hmem1 : s ∈ Icc 0 (2 * Real.pi / ωd) := ⟨hs0, by
    have : Real.pi / (2 * ωd) ≤ 2 * Real.pi / ωd := by
      rw [div_le_div_iff₀ (by positivity) hωd0]; nlinarith
    linarith⟩
  have hmem2 : s + Real.pi / ωd ∈ Icc 0 (2 * Real.pi / ωd) := ⟨by positivity, by
    have : Real.pi / (2 * ωd) + Real.pi / ωd ≤ 2 * Real.pi / ωd := by
      rw [show Real.pi / (2 * ωd) + Real.pi / ωd = (3 / 2) * (Real.pi / ωd) by field_simp; ring,
        show 2 * Real.pi / ωd = 2 * (Real.pi / ωd) by ring]
      have : 0 < Real.pi / ωd := by positivity
      linarith
    linarith⟩
  have hbddA : BddAbove (x '' Icc 0 (2 * Real.pi / ωd)) :=
    isCompact_Icc.bddAbove_image hcont.continuousOn
  have hbddB : BddBelow (x '' Icc 0 (2 * Real.pi / ωd)) :=
    isCompact_Icc.bddBelow_image hcont.continuousOn
  have h1 := le_csSup hbddA (mem_image_of_mem x hmem1)
  have h2 := le_csSup hbddA (mem_image_of_mem x hmem2)
  have h3 := csInf_le hbddB (mem_image_of_mem x hmem1)
  have h4 := csInf_le hbddB (mem_image_of_mem x hmem2)
  rw [hhalf] at h2 h4
  have he := Real.exp_pos (-(-σ * (Real.pi / ωd)))
  rw [peakToPeak]
  rcases lt_or_gt_of_ne hxs with hneg | hpos
  · nlinarith
  · nlinarith

/-- Step 2, natural start-up: `Y_i = X_i − X_{i−1} = X₀ (e^{σT} − 1) e^{(i−1)σT}`. -/
@[tmio T, powerlib_foundation] theorem natural_increment (hm : m ≠ 0) (hσ : σ = -(c / (2 * m)))
    (hωd : ωd ^ 2 = k / m - σ ^ 2) (hωd0 : ωd ≠ 0)
    {x v a : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = 0) (i : ℕ) :
    peakToPeak x (i * (2 * Real.pi / ωd)) ((i + 1) * (2 * Real.pi / ωd)) -
        peakToPeak x ((i - 1) * (2 * Real.pi / ωd)) (i * (2 * Real.pi / ωd)) =
      peakToPeak x 0 (2 * Real.pi / ωd) * (Real.exp (σ * (2 * Real.pi / ωd)) - 1) *
        Real.exp ((i - 1) * (σ * (2 * Real.pi / ωd))) := by
  set T := 2 * Real.pi / ωd
  have hsh := natural_shift hm hσ hωd hωd0 hx hv heq
  have hprev := peakToPeak_shift (Real.exp_pos (σ * T)).le hsh ((i - 1) * T) (i * T)
  rw [show (i - 1 : ℝ) * T + T = i * T by ring, show (i : ℝ) * T + T = (i + 1) * T by ring]
    at hprev
  have hcur := natural_peakToPeak hm hσ hωd hωd0 hx hv heq i
  have hq : Real.exp (σ * T) ≠ 0 := (Real.exp_pos _).ne'
  have hX : peakToPeak x ((i - 1) * T) (i * T) =
      Real.exp ((i - 1) * (σ * T)) * peakToPeak x 0 T := by
    have : Real.exp (i * (σ * T)) = Real.exp (σ * T) * Real.exp ((i - 1) * (σ * T)) := by
      rw [← Real.exp_add]; ring_nf
    rw [hcur, this, mul_assoc] at hprev
    exact (mul_left_cancel₀ hq hprev).symm
  rw [hcur, hX, show (i : ℝ) * (σ * T) = σ * T + (i - 1) * (σ * T) by ring, Real.exp_add]
  ring

/-- For `σ > 0` the increments of a nonzero natural start-up are positive. -/
@[tmio T, powerlib_foundation] theorem natural_increment_pos (hm : m ≠ 0)
    (hσ : σ = -(c / (2 * m))) (hωd : ωd ^ 2 = k / m - σ ^ 2) (hωd0 : 0 < ωd) (hσ0 : 0 < σ)
    {x v a : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = 0) (hne : x 0 ≠ 0 ∨ v 0 ≠ 0) (i : ℕ) :
    0 < peakToPeak x (i * (2 * Real.pi / ωd)) ((i + 1) * (2 * Real.pi / ωd)) -
        peakToPeak x ((i - 1) * (2 * Real.pi / ωd)) (i * (2 * Real.pi / ωd)) := by
  rw [natural_increment hm hσ hωd hωd0.ne' hx hv heq i]
  have hX := natural_peakToPeak_pos hm hσ hωd hωd0 hx hv heq hne
  have hT : 0 < σ * (2 * Real.pi / ωd) := mul_pos hσ0 (by positivity)
  have : 0 < Real.exp (σ * (2 * Real.pi / ωd)) - 1 := by
    have := Real.add_one_lt_exp hT.ne'; linarith
  positivity

/-- For `σ > 0`: `ln Y_i = ln(X₀ (e^{σT} − 1)) + (i − 1) σT`, affine in `i` with slope `σT`. -/
@[tmio T, powerlib_foundation] theorem natural_log_increment (hm : m ≠ 0)
    (hσ : σ = -(c / (2 * m))) (hωd : ωd ^ 2 = k / m - σ ^ 2) (hωd0 : 0 < ωd) (hσ0 : 0 < σ)
    {x v a : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = 0) (hne : x 0 ≠ 0 ∨ v 0 ≠ 0) (i : ℕ) :
    Real.log (peakToPeak x (i * (2 * Real.pi / ωd)) ((i + 1) * (2 * Real.pi / ωd)) -
        peakToPeak x ((i - 1) * (2 * Real.pi / ωd)) (i * (2 * Real.pi / ωd))) =
      Real.log (peakToPeak x 0 (2 * Real.pi / ωd) * (Real.exp (σ * (2 * Real.pi / ωd)) - 1)) +
        (i - 1) * (σ * (2 * Real.pi / ωd)) := by
  rw [natural_increment hm hσ hωd hωd0.ne' hx hv heq i]
  have hX := natural_peakToPeak_pos hm hσ hωd hωd0 hx hv heq hne
  have hT : 0 < σ * (2 * Real.pi / ωd) := mul_pos hσ0 (by positivity)
  have : 0 < Real.exp (σ * (2 * Real.pi / ωd)) - 1 := by
    have := Real.add_one_lt_exp hT.ne'; linarith
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]

/-! ## Forced start-up at resonance -/

/-- A sinusoidal input `μ sin(ωt + θ)` has a sinusoidal steady state `A₃ sin(ωt + φ₃)` whenever
`k − mω² + j c ω ≠ 0` (`A₃ e^{jφ₃} = μ e^{jθ}/(k − mω² + jcω)`). -/
@[tmio T, powerlib_foundation] theorem exists_steadyState {ω : ℝ}
    (hZ : k - m * ω ^ 2 ≠ 0 ∨ c * ω ≠ 0) (μ θ : ℝ) :
    ∃ A₃ φ₃ : ℝ, ∀ t, m * (-(ω ^ 2) * (A₃ * Real.sin (ω * t + φ₃))) +
        c * (ω * (A₃ * Real.cos (ω * t + φ₃))) + k * (A₃ * Real.sin (ω * t + φ₃)) =
      μ * Real.sin (ω * t + θ) := by
  set Z : ℂ := ⟨k - m * ω ^ 2, c * ω⟩
  have hZ0 : Z ≠ 0 := by
    intro h
    rcases hZ with h1 | h1
    · exact h1 (congrArg Complex.re h)
    · exact h1 (congrArg Complex.im h)
  set X : ℂ := (μ : ℂ) * ⟨Real.cos θ, Real.sin θ⟩ / Z
  have hZX : Z * X = (μ : ℂ) * ⟨Real.cos θ, Real.sin θ⟩ := mul_div_cancel₀ _ hZ0
  have hre := congrArg Complex.re hZX
  have him := congrArg Complex.im hZX
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, add_zero, Z] at hre him
  refine ⟨‖X‖, Complex.arg X, fun t => ?_⟩
  have hc := Complex.norm_mul_cos_arg X
  have hs := Complex.norm_mul_sin_arg X
  rw [Real.sin_add, Real.cos_add, Real.sin_add]
  linear_combination (Real.sin (ω * t)) * hre + (Real.cos (ω * t)) * him +
    ((k - m * ω ^ 2) * Real.sin (ω * t) + c * ω * Real.cos (ω * t)) * hc +
    ((k - m * ω ^ 2) * Real.cos (ω * t) - c * ω * Real.sin (ω * t)) * hs

/-- (3-4)–(3-5) exactly: started from rest, `x(0) = ẋ(0) = 0`, under an input with steady state
`A₃ sin(ωt + φ₃)` at the damped frequency `ω = ω_d`, the solution is
`x(t) = A₃(1 − e^{σt}) sin(ωt + φ₃) + (σ/ω) A₃ sin φ₃ e^{σt} sin ωt`. -/
@[tmio T, powerlib_foundation] theorem forced_startUp (hm : m ≠ 0) (hσ : σ = -(c / (2 * m)))
    {ω : ℝ} (hω : ω ^ 2 = k / m - σ ^ 2) (hω0 : ω ≠ 0) {A₃ φ₃ : ℝ} {f x v a : ℝ → ℝ}
    (hss : ∀ t, m * (-(ω ^ 2) * (A₃ * Real.sin (ω * t + φ₃))) +
        c * (ω * (A₃ * Real.cos (ω * t + φ₃))) + k * (A₃ * Real.sin (ω * t + φ₃)) = f t)
    (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = f t) (hx0 : x 0 = 0) (hv0 : v 0 = 0) (t : ℝ) :
    x t = A₃ * (1 - Real.exp (σ * t)) * Real.sin (ω * t + φ₃) +
      σ / ω * A₃ * Real.sin φ₃ * Real.exp (σ * t) * Real.sin (ω * t) := by
  have hs : ∀ s, HasDerivAt (fun s => A₃ * Real.sin (ω * s + φ₃))
      (ω * (A₃ * Real.cos (ω * s + φ₃))) s := fun s => by
    have := (((hasDerivAt_id' s).const_mul ω).add_const φ₃).sin.const_mul A₃
    convert this using 1; simp; ring
  have hc : ∀ s, HasDerivAt (fun s => ω * (A₃ * Real.cos (ω * s + φ₃)))
      (-(ω ^ 2) * (A₃ * Real.sin (ω * s + φ₃))) s := fun s => by
    have := ((((hasDerivAt_id' s).const_mul ω).add_const φ₃).cos.const_mul A₃).const_mul ω
    convert this using 1; simp; ring
  have he : ∀ s, HasDerivAt (fun s => x s - A₃ * Real.sin (ω * s + φ₃))
      (v s - ω * (A₃ * Real.cos (ω * s + φ₃))) s := fun s => (hx s).sub (hs s)
  have he' : ∀ s, HasDerivAt (fun s => v s - ω * (A₃ * Real.cos (ω * s + φ₃)))
      (a s - -(ω ^ 2) * (A₃ * Real.sin (ω * s + φ₃))) s := fun s => (hv s).sub (hc s)
  have hfree : ∀ s, m * (a s - -(ω ^ 2) * (A₃ * Real.sin (ω * s + φ₃))) +
      c * (v s - ω * (A₃ * Real.cos (ω * s + φ₃))) +
      k * (x s - A₃ * Real.sin (ω * s + φ₃)) = 0 := fun s => by
    have h1 := heq s; have h2 := hss s; linear_combination h1 - h2
  have h := natural_eq_dampedResp hm hσ hω hω0 he he' hfree t
  simp only [hx0, hv0, mul_zero, zero_add, zero_sub] at h
  rw [dampedResp] at h
  have hxt : x t = A₃ * Real.sin (ω * t + φ₃) + Real.exp (-(-σ * t)) *
      (-(A₃ * Real.sin φ₃) * Real.cos (ω * t) +
        (-(ω * (A₃ * Real.cos φ₃)) + -σ * -(A₃ * Real.sin φ₃)) / ω * Real.sin (ω * t)) := by
    linarith
  rw [hxt, show -(-σ * t) = σ * t by ring, Real.sin_add]
  field_simp
  ring

/-- When `σ sin φ₃ = 0` the report's deduction `φ₂ = φ₃`, `A₂ = −A₃` is exact:
`x(t) = A₃(1 − e^{σt}) sin(ωt + φ₃)`. -/
@[tmio T, powerlib_foundation] theorem forced_startUp_of_sin (hm : m ≠ 0)
    (hσ : σ = -(c / (2 * m))) {ω : ℝ} (hω : ω ^ 2 = k / m - σ ^ 2) (hω0 : ω ≠ 0) {A₃ φ₃ : ℝ}
    {f x v a : ℝ → ℝ}
    (hss : ∀ t, m * (-(ω ^ 2) * (A₃ * Real.sin (ω * t + φ₃))) +
        c * (ω * (A₃ * Real.cos (ω * t + φ₃))) + k * (A₃ * Real.sin (ω * t + φ₃)) = f t)
    (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = f t) (hx0 : x 0 = 0) (hv0 : v 0 = 0)
    (h0 : σ * Real.sin φ₃ = 0) (t : ℝ) :
    x t = A₃ * (1 - Real.exp (σ * t)) * Real.sin (ω * t + φ₃) := by
  rw [forced_startUp hm hσ hω hω0 hss hx hv heq hx0 hv0 t]
  have : σ / ω * A₃ * Real.sin φ₃ = (σ * Real.sin φ₃) * (A₃ / ω) := by ring
  rw [this, h0]
  ring

/-- The envelope (3-5) of the forced start-up up to the explicit remainder:
`|x(t) − A₃(1 − e^{σt}) sin(ωt + φ₃)| ≤ |σ/ω| |A₃| e^{σt}`. -/
@[tmio T, powerlib_foundation] theorem forced_startUp_error (hm : m ≠ 0)
    (hσ : σ = -(c / (2 * m))) {ω : ℝ} (hω : ω ^ 2 = k / m - σ ^ 2) (hω0 : ω ≠ 0) {A₃ φ₃ : ℝ}
    {f x v a : ℝ → ℝ}
    (hss : ∀ t, m * (-(ω ^ 2) * (A₃ * Real.sin (ω * t + φ₃))) +
        c * (ω * (A₃ * Real.cos (ω * t + φ₃))) + k * (A₃ * Real.sin (ω * t + φ₃)) = f t)
    (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = f t) (hx0 : x 0 = 0) (hv0 : v 0 = 0) (t : ℝ) :
    |x t - A₃ * (1 - Real.exp (σ * t)) * Real.sin (ω * t + φ₃)| ≤
      |σ / ω| * |A₃| * Real.exp (σ * t) := by
  rw [forced_startUp hm hσ hω hω0 hss hx hv heq hx0 hv0 t, add_sub_cancel_left]
  rw [show σ / ω * A₃ * Real.sin φ₃ * Real.exp (σ * t) * Real.sin (ω * t) =
      (σ / ω * A₃ * Real.exp (σ * t)) * (Real.sin φ₃ * Real.sin (ω * t)) by ring, abs_mul,
    abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : |Real.sin φ₃ * Real.sin (ω * t)| ≤ 1 := by
    rw [abs_mul]
    have := Real.abs_sin_le_one φ₃
    have := Real.abs_sin_le_one (ω * t)
    nlinarith [abs_nonneg (Real.sin φ₃), abs_nonneg (Real.sin (ω * t))]
  have h2 : 0 ≤ |σ / ω| * |A₃| * Real.exp (σ * t) := by positivity
  nlinarith

end Oscillator

/-! ## The envelope model -/

/-- The envelope model `E(t) = A e^{σt} + B` of Fig. 3-1. -/
def envelope (A B σ t : ℝ) : ℝ := A * Real.exp (σ * t) + B

/-- `E(iT) − E((i−1)T) = A (e^{σT} − 1) e^{(i−1)σT}`. -/
@[tmio T, powerlib_foundation] theorem envelope_increment (A B σ T : ℝ) (i : ℕ) :
    envelope A B σ (i * T) - envelope A B σ ((i - 1) * T) =
      A * (Real.exp (σ * T) - 1) * Real.exp ((i - 1) * (σ * T)) := by
  rw [envelope, envelope, show σ * (i * T) = σ * T + (i - 1) * (σ * T) by ring, Real.exp_add,
    show σ * ((i - 1) * T) = (i - 1) * (σ * T) by ring]
  ring

/-- The increments are positive for the natural envelope (`A > 0`, `σ > 0`) and for the forced
envelope (`A < 0`, `σ < 0`), whatever `B`. -/
@[tmio T, powerlib_foundation] theorem envelope_increment_pos {A B σ T : ℝ} (hT : 0 < T)
    (h : (0 < A ∧ 0 < σ) ∨ (A < 0 ∧ σ < 0)) (i : ℕ) :
    0 < envelope A B σ (i * T) - envelope A B σ ((i - 1) * T) := by
  rw [envelope_increment]
  have he := Real.exp_pos ((i - 1) * (σ * T))
  rcases h with ⟨hA, hσ⟩ | ⟨hA, hσ⟩
  · have : 0 < Real.exp (σ * T) - 1 := by
      have := Real.add_one_lt_exp (mul_pos hσ hT).ne'; have := mul_pos hσ hT; linarith
    positivity
  · have : Real.exp (σ * T) - 1 < 0 := by
      have := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos hσ hT); linarith
    have : 0 < A * (Real.exp (σ * T) - 1) := mul_pos_of_neg_of_neg hA this
    positivity

/-- `ln(E(iT) − E((i−1)T)) = ln(A(e^{σT} − 1)) + (i − 1)σT` for either kind of envelope. -/
@[tmio T, powerlib_foundation] theorem log_envelope_increment {A B σ T : ℝ} (hT : 0 < T)
    (h : (0 < A ∧ 0 < σ) ∨ (A < 0 ∧ σ < 0)) (i : ℕ) :
    Real.log (envelope A B σ (i * T) - envelope A B σ ((i - 1) * T)) =
      Real.log (A * (Real.exp (σ * T) - 1)) + (i - 1) * (σ * T) := by
  have hpos := envelope_increment_pos (B := B) hT h 1
  rw [envelope_increment] at hpos
  simp only [Nat.cast_one, sub_self, zero_mul, Real.exp_zero, mul_one] at hpos
  rw [envelope_increment, Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp]

/-- The peak-to-peak values of a natural start-up follow the natural envelope (3-3):
`X_i = E(iT)` with `A = X₀`, `B = 0`. -/
@[tmio T, powerlib_foundation] theorem natural_peakToPeak_eq_envelope {m c k σ ωd : ℝ}
    (hm : m ≠ 0) (hσ : σ = -(c / (2 * m))) (hωd : ωd ^ 2 = k / m - σ ^ 2) (hωd0 : ωd ≠ 0)
    {x v a : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = 0) (i : ℕ) :
    peakToPeak x (i * (2 * Real.pi / ωd)) ((i + 1) * (2 * Real.pi / ωd)) =
      envelope (peakToPeak x 0 (2 * Real.pi / ωd)) 0 σ (i * (2 * Real.pi / ωd)) := by
  rw [natural_peakToPeak hm hσ hωd hωd0 hx hv heq, envelope, add_zero,
    show σ * (i * (2 * Real.pi / ωd)) = i * (σ * (2 * Real.pi / ωd)) by ring]
  ring

/-! ## Least-squares slope -/

section Slope

variable {ι : Type*}

/-- Least-squares slope of the points `(uᵢ, zᵢ)`, `i ∈ s`:
`Σ (uᵢ − ū)(zᵢ − z̄) / Σ (uᵢ − ū)²` with the means `ū = 𝔼ᵢ uᵢ`, `z̄ = 𝔼ᵢ zᵢ`. -/
def olsSlope (s : Finset ι) (u z : ι → ℝ) : ℝ :=
  (∑ i ∈ s, (u i - Finset.expect s u) * (z i - Finset.expect s z)) /
    ∑ i ∈ s, (u i - Finset.expect s u) ^ 2

/-- Data on a line `zᵢ = z₀ + S uᵢ` (abscissae not all equal) have least-squares slope `S`. -/
@[tmio T, powerlib_foundation] theorem olsSlope_affine {s : Finset ι} {u : ι → ℝ}
    (h : ∑ i ∈ s, (u i - Finset.expect s u) ^ 2 ≠ 0) (z₀ S : ℝ) :
    olsSlope s u (fun i => z₀ + S * u i) = S := by
  have hs : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with h0 | h0
    · exact absurd (by rw [h0, Finset.sum_empty]) h
    · exact h0
  have hmean : Finset.expect s (fun i => z₀ + S * u i) = z₀ + S * Finset.expect s u := by
    rw [Finset.expect_add_distrib, Finset.expect_const hs, Finset.mul_expect]
  rw [olsSlope, hmean]
  have : ∀ i ∈ s, (u i - Finset.expect s u) * (z₀ + S * u i - (z₀ + S * Finset.expect s u)) =
      S * (u i - Finset.expect s u) ^ 2 := fun i _ => by ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, mul_div_assoc, div_self h, mul_one]

/-- Abscissae that are not all equal have positive spread `Σ (uᵢ − ū)² > 0`. -/
@[tmio T, powerlib_foundation] theorem sum_sq_sub_expect_pos {s : Finset ι} {u : ι → ℝ} {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (hij : u i ≠ u j) :
    0 < ∑ l ∈ s, (u l - Finset.expect s u) ^ 2 := by
  apply lt_of_le_of_ne (Finset.sum_nonneg fun l _ => sq_nonneg _)
  intro h0
  have h := (Finset.sum_eq_zero_iff_of_nonneg fun l _ => sq_nonneg (u l - Finset.expect s u)).mp
    h0.symm
  have h1 := h i hi
  have h2 := h j hj
  rw [sq_eq_zero_iff, sub_eq_zero] at h1 h2
  exact hij (h1.trans h2.symm)

@[tmio T, powerlib_foundation] private theorem spread_Icc_pos {N : ℕ} (hN : 2 ≤ N) :
    ∑ l ∈ Finset.Icc 1 N, ((l : ℝ) - Finset.expect (Finset.Icc 1 N) (fun l : ℕ => (l : ℝ))) ^ 2
      ≠ 0 :=
  (sum_sq_sub_expect_pos (u := fun l : ℕ => (l : ℝ)) (i := 1) (j := 2)
    (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) (Finset.mem_Icc.mpr ⟨by omega, hN⟩)
    (by norm_num)).ne'

end Slope

/-! ## Step 3: the slope index and the classifier -/

/-- Step 3 on a natural start-up: for a nonzero natural solution with `σ > 0`, the least-squares
slope of `(i, ln Y_i)`, `i = 1, …, N` (`N ≥ 2`), is `S = σT`. -/
@[tmio T, powerlib_foundation] theorem slope_natural {m c k σ ωd : ℝ} (hm : m ≠ 0)
    (hσ : σ = -(c / (2 * m))) (hωd : ωd ^ 2 = k / m - σ ^ 2) (hωd0 : 0 < ωd) (hσ0 : 0 < σ)
    {x v a : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, m * a t + c * v t + k * x t = 0) (hne : x 0 ≠ 0 ∨ v 0 ≠ 0) {N : ℕ}
    (hN : 2 ≤ N) :
    olsSlope (Finset.Icc 1 N) (fun i : ℕ => (i : ℝ)) (fun i : ℕ =>
      Real.log (peakToPeak x (i * (2 * Real.pi / ωd)) ((i + 1) * (2 * Real.pi / ωd)) -
        peakToPeak x ((i - 1) * (2 * Real.pi / ωd)) (i * (2 * Real.pi / ωd)))) =
      σ * (2 * Real.pi / ωd) := by
  have hlin : (fun i : ℕ =>
      Real.log (peakToPeak x (i * (2 * Real.pi / ωd)) ((i + 1) * (2 * Real.pi / ωd)) -
        peakToPeak x ((i - 1) * (2 * Real.pi / ωd)) (i * (2 * Real.pi / ωd)))) =
      fun i : ℕ => (Real.log (peakToPeak x 0 (2 * Real.pi / ωd) *
          (Real.exp (σ * (2 * Real.pi / ωd)) - 1)) - σ * (2 * Real.pi / ωd)) +
        σ * (2 * Real.pi / ωd) * (i : ℝ) := by
    funext i
    rw [natural_log_increment hm hσ hωd hωd0 hσ0 hx hv heq hne i]
    ring
  rw [hlin, olsSlope_affine (spread_Icc_pos hN)]

/-- Step 3 on the envelope model: for either kind of envelope the least-squares slope of the log
increments over `i = 1, …, N` (`N ≥ 2`) is `S = σT` (natural `σ > 0`, forced `σ < 0`). -/
@[tmio T, powerlib_foundation] theorem slope_envelope {A B σ T : ℝ} (hT : 0 < T)
    (h : (0 < A ∧ 0 < σ) ∨ (A < 0 ∧ σ < 0)) {N : ℕ} (hN : 2 ≤ N) :
    olsSlope (Finset.Icc 1 N) (fun i : ℕ => (i : ℝ))
      (fun i : ℕ => Real.log (envelope A B σ (i * T) - envelope A B σ ((i - 1) * T))) =
      σ * T := by
  have hlin : (fun i : ℕ => Real.log (envelope A B σ (i * T) - envelope A B σ ((i - 1) * T))) =
      fun i : ℕ => (Real.log (A * (Real.exp (σ * T) - 1)) - σ * T) + σ * T * (i : ℝ) := by
    funext i
    rw [log_envelope_increment hT h i]
    ring
  rw [hlin, olsSlope_affine (spread_Icc_pos hN)]

/-- The verdict of the slope test. -/
inductive Verdict
  | natural
  | forced
  | undecided
  deriving DecidableEq

/-- Step 3 with threshold `ε`: `S > ε` natural, `S < −ε` forced, otherwise undecided. -/
def classify (ε S : ℝ) : Verdict :=
  if ε < S then .natural else if S < -ε then .forced else .undecided

@[tmio T, powerlib_foundation] theorem classify_eq_natural_iff (ε S : ℝ) :
    classify ε S = .natural ↔ ε < S := by
  unfold classify
  split_ifs with h1 h2 <;> simp_all

@[tmio T, powerlib_foundation] theorem classify_eq_forced_iff {ε : ℝ} (hε : 0 ≤ ε) (S : ℝ) :
    classify ε S = .forced ↔ S < -ε := by
  unfold classify
  split_ifs with h1 h2 <;> simp_all
  linarith

/-- A positive slope is never classified forced (`ε ≥ 0`). -/
@[tmio T, powerlib_foundation] theorem classify_ne_forced {ε S : ℝ} (hε : 0 ≤ ε) (hS : 0 < S) :
    classify ε S ≠ .forced := by
  rw [Ne, classify_eq_forced_iff hε]; linarith

/-- A negative slope is never classified natural (`ε ≥ 0`). -/
@[tmio T, powerlib_foundation] theorem classify_ne_natural {ε S : ℝ} (hε : 0 ≤ ε) (hS : S < 0) :
    classify ε S ≠ .natural := by
  rw [Ne, classify_eq_natural_iff]; linarith

/-- Correctness on a natural start-up (`σ > 0`): the slope test never answers forced, and answers
natural exactly when `σT > ε`. -/
@[tmio T, powerlib_foundation] theorem classify_natural {m c k σ ωd ε : ℝ} (hm : m ≠ 0)
    (hσ : σ = -(c / (2 * m))) (hωd : ωd ^ 2 = k / m - σ ^ 2) (hωd0 : 0 < ωd) (hσ0 : 0 < σ)
    (hε : 0 ≤ ε) {x v a : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (v t) t)
    (hv : ∀ t, HasDerivAt v (a t) t) (heq : ∀ t, m * a t + c * v t + k * x t = 0)
    (hne : x 0 ≠ 0 ∨ v 0 ≠ 0) {N : ℕ} (hN : 2 ≤ N) :
    let S := olsSlope (Finset.Icc 1 N) (fun i : ℕ => (i : ℝ)) (fun i : ℕ =>
      Real.log (peakToPeak x (i * (2 * Real.pi / ωd)) ((i + 1) * (2 * Real.pi / ωd)) -
        peakToPeak x ((i - 1) * (2 * Real.pi / ωd)) (i * (2 * Real.pi / ωd))))
    classify ε S ≠ .forced ∧ (classify ε S = .natural ↔ ε < σ * (2 * Real.pi / ωd)) := by
  intro S
  have hS : S = σ * (2 * Real.pi / ωd) := slope_natural hm hσ hωd hωd0 hσ0 hx hv heq hne hN
  rw [hS]
  exact ⟨classify_ne_forced hε (mul_pos hσ0 (by positivity)), classify_eq_natural_iff ε _⟩

/-- Correctness on a forced start-up envelope (3-5) at positive intrinsic damping (`σ < 0`,
`E_F(t) = A₃ − A₃ e^{σt}`, `A₃ > 0`): the slope test never answers natural, and answers forced
exactly when `σT < −ε`. -/
@[tmio T, powerlib_foundation] theorem classify_forced {A₃ σ T ε : ℝ} (hT : 0 < T) (hA : 0 < A₃)
    (hσ0 : σ < 0) (hε : 0 ≤ ε) {N : ℕ} (hN : 2 ≤ N) :
    let S := olsSlope (Finset.Icc 1 N) (fun i : ℕ => (i : ℝ))
      (fun i : ℕ => Real.log (envelope (-A₃) A₃ σ (i * T) - envelope (-A₃) A₃ σ ((i - 1) * T)))
    classify ε S ≠ .natural ∧ (classify ε S = .forced ↔ σ * T < -ε) := by
  intro S
  have hS : S = σ * T := slope_envelope hT (Or.inr ⟨by linarith, hσ0⟩) hN
  rw [hS]
  exact ⟨classify_ne_natural hε (mul_neg_of_neg_of_pos hσ0 hT), classify_eq_forced_iff hε _⟩

end powerlib.LTI.StartUp
