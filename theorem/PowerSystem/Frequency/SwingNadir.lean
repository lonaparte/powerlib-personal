import theorem.PowerSystem.Frequency.SwingGovernor
import theorem.LTI.Oscillator2
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Frequency nadir of the swing + governor model (exact closed form)

The exact time and value of the frequency nadir of the underdamped swing + governor model after a
load step, without Laplace inversion; the nadir magnitude, which the note leaves to "Kundur
§11.1.6", is derived here.

Model boundary.
* Exactly the plant of `Frequency.SwingGovernor` (`SwingGovernor.plant`; state `(Δω, ΔP_m)`,
  continuous time, linear, Kundur per-unit, load step `ΔP_L` applied at `t = 0` to the system
  at rest `x(0) = 0`; no turbine/reheat, AGC, dead-band, rate limit, PLL, delay or PWM).
* Parameters: `0 < M`, `0 < T_g`, `0 ≤ D`, `0 < K_R + D`, a load *increase* `0 < ΔP_L`, and the
  underdamped case `ζ_n < 1`. The conclusions are trajectory-level (every trajectory of the
  model with `x(0) = 0`).
* Notation (`σ = ζ_n ω_n`, `ω_d = ω_n √(1 − ζ_n²)`, the §1.7 `ω_n`, `ζ_n`):
  `nadirTime = atan2(ω_d, σ − 1/T_g)/ω_d`, with `atan2(y, x) := Complex.arg (x + j y)`;
  `nadirValue = −ΔP_L/(K_R + D) · [1 + √(1 − 2σT_g + ω_n²T_g²) · e^{−σ t_nadir}]`.

Source: work-sync `theory/T-frequency-stability.md` §1.7 (boxed `t_nadir` with atan2 and the
step response `Δω(t) = −ΔP_L/(K_R + D)[1 − e^{−σt}(cos ω_d t − α sin ω_d t)]`).

Results.
* `decayRate_eq`, `decayRate_nonneg`, `dampedFreq_pos`, `dampingRatio_pos`,
  `decayRate_sq_add_dampedFreq_sq`, `trace_A`, `det_A` (domain): in the underdamped case the
  state matrix has the eigenvalues `−σ ± j ω_d` (`tr A = −2σ`, `det A = σ² + ω_d²`).
* `rest_deviation`, `rest_slope` (domain): from rest the deviation of `Δω` from the
  quasi-steady state starts at `ΔP_L/(K_R + D)` with the slope `−ΔP_L/M`.
* `dampedRespPhase_eq`, `nadirTime_eq_dampedRespCrit`, `nadirValue_eq` (domain): for a load
  increase the phase point of that damped response (`LTI.dampedRespPhase`) is
  `ΔP_L/(M ω_d) · (σ − 1/T_g + j ω_d)`, so `nadirTime` is its first critical time
  (`LTI.dampedRespCrit`) and `nadirValue` its value there (`LTI.trajectory_nadir_osc2`).
* `nadirValue_lt` (domain): the nadir lies strictly below the quasi-steady state
  `−ΔP_L/(K_R + D)` (overshoot is unavoidable in the underdamped case).
* `freq_nadir` (implementation evidence, private): `0 < t_nadir`; `Δω` is strictly decreasing on
  `[0, t_nadir]`; `Δω(t_nadir)` is the minimum of `Δω` over all `t ≥ 0`; and it equals
  `nadirValue`.
* `nadir_successive` (implementation evidence, private): at `t_nadir + kπ/ω_d` the derivative
  vanishes again and the deviation from the quasi-steady state is multiplied by
  `(−e^{−σπ/ω_d})^k`.

Family and connection conclusions.
* This module adds no family: the model is the swing + governor family of
  `Frequency.SwingGovernor`. The identities above are domain model identities.
* The nadir statements quantify over forward solutions and their extrema in time, which the
  sentence language does not express: `freq_nadir` and `nadir_successive` are private
  implementation evidence (Rules §3a). They instantiate the generic first extremum of a
  two-state plant (`LTI.trajectory_nadir_osc2`, `LTI.trajectory_apply_eq_dampedResp`,
  `LTI.hasDerivAt_dampedResp_crit_add`, `LTI.dampedResp_add_half_period`) with the static
  identities above; modules that need a nadir of a forward solution (`SFR`, `UFLS`,
  `UFLSLatched`) instantiate them the same way.

Proof outline (no Laplace inversion is assumed).
* Every coordinate of a forward solution of a two-state plant with eigenvalues `−σ ± j ω_d` is
  the equilibrium plus the damped response `LTI.dampedResp σ ω_d a r` with initial deviation `a`
  and initial slope `r` (`theorem/LTI/Oscillator2.lean`); its first critical time and value are
  `LTI.dampedRespCrit` and `LTI.dampedResp_crit`. Here `a = ΔP_L/(K_R + D)` and
  `r = −ΔP_L/M` (`rest_deviation`, `rest_slope`), and the phase point is a positive multiple of
  `σ − 1/T_g + j ω_d` (`dampedRespPhase_eq`, `Complex.arg_real_mul`).
-/

noncomputable section
namespace powerlib.Frequency.SwingGovernor
open Set Filter Matrix LinearSystems
open scoped Topology

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- `σ = ζ_n ω_n`. -/
def decayRate (M D K Tg : ℝ) : ℝ := dampingRatio M D K Tg * natFreq M D K Tg

/-- `ω_d = ω_n √(1 − ζ_n²)`. -/
def dampedFreq (M D K Tg : ℝ) : ℝ :=
  natFreq M D K Tg * Real.sqrt (1 - dampingRatio M D K Tg ^ 2)

/-- `t_nadir = atan2(ω_d, ζ_n ω_n − 1/T_g)/ω_d`, `atan2(y, x) = arg (x + j y)`. -/
def nadirTime (M D K Tg : ℝ) : ℝ :=
  Complex.arg ⟨decayRate M D K Tg - 1 / Tg, dampedFreq M D K Tg⟩ / dampedFreq M D K Tg

/-- `−ΔP_L/(K_R + D)·[1 + √(1 − 2σT_g + ω_n²T_g²) e^{−σ t_nadir}]`, `σ = ζ_n ω_n`. -/
def nadirValue (M D K Tg ΔPL : ℝ) : ℝ :=
  -ΔPL / (K + D) * (1 + Real.sqrt (1 - 2 * decayRate M D K Tg * Tg +
      natFreq M D K Tg ^ 2 * Tg ^ 2) * Real.exp (-(decayRate M D K Tg * nadirTime M D K Tg)))

variable {M D K Tg ΔPL : ℝ}

@[tmio M, powerlib_domain] theorem dampingRatio_pos (hM : 0 < M) (hTg : 0 < Tg) (hD : 0 ≤ D)
    (hKD : 0 < K + D) : 0 < dampingRatio M D K Tg := by
  rw [dampingRatio_eq hM hTg]
  have : 0 < M * Tg * (D + K) := mul_pos (mul_pos hM hTg) (by linarith)
  exact div_pos (by nlinarith) (by positivity)

@[tmio M, powerlib_domain] theorem decayRate_eq (hM : 0 < M) (hTg : 0 < Tg) (hKD : 0 < K + D) :
    decayRate M D K Tg = (M + D * Tg) / (2 * (M * Tg)) := by
  have h := two_mul_dampingRatio_mul_natFreq hM hTg (by linarith : 0 < D + K)
  unfold decayRate
  rw [show dampingRatio M D K Tg * natFreq M D K Tg =
    (2 * dampingRatio M D K Tg * natFreq M D K Tg) / 2 by ring, h]
  field_simp

@[tmio M, powerlib_domain] theorem decayRate_nonneg (hM : 0 < M) (hTg : 0 < Tg) (hD : 0 ≤ D)
    (hKD : 0 < K + D) : 0 ≤ decayRate M D K Tg := by
  rw [decayRate_eq hM hTg hKD]
  have : 0 ≤ D * Tg := mul_nonneg hD hTg.le
  positivity

@[tmio M, powerlib_domain] theorem dampedFreq_pos (hM : 0 < M) (hTg : 0 < Tg) (hD : 0 ≤ D)
    (hKD : 0 < K + D) (hζ : dampingRatio M D K Tg < 1) : 0 < dampedFreq M D K Tg := by
  have hz := dampingRatio_pos hM hTg hD hKD
  exact mul_pos (natFreq_pos hM hTg (by linarith))
    (Real.sqrt_pos.2 (by nlinarith))

@[tmio M, powerlib_domain] theorem decayRate_sq_add_dampedFreq_sq (hM : 0 < M) (hTg : 0 < Tg)
    (hD : 0 ≤ D) (hKD : 0 < K + D) (hζ : dampingRatio M D K Tg < 1) :
    decayRate M D K Tg ^ 2 + dampedFreq M D K Tg ^ 2 = natFreq M D K Tg ^ 2 := by
  have hz := dampingRatio_pos hM hTg hD hKD
  unfold decayRate dampedFreq
  rw [mul_pow, mul_pow, Real.sq_sqrt (by nlinarith)]
  ring

@[tmio M, powerlib_domain] theorem trace_A (hM : 0 < M) (hTg : 0 < Tg) (hKD : 0 < K + D) :
    (plant M D K Tg).A.trace = -2 * decayRate M D K Tg := by
  rw [decayRate_eq hM hTg hKD, trace_plant]
  field_simp
  ring

@[tmio M, powerlib_domain] theorem det_A (hM : 0 < M) (hTg : 0 < Tg) (hD : 0 ≤ D)
    (hKD : 0 < K + D) (hζ : dampingRatio M D K Tg < 1) :
    (plant M D K Tg).A.det = decayRate M D K Tg ^ 2 + dampedFreq M D K Tg ^ 2 := by
  rw [decayRate_sq_add_dampedFreq_sq hM hTg hD hKD hζ, natFreq_sq hM hTg (by linarith),
    det_plant hM.ne' hTg.ne']
  ring

/-- At rest the deviation from the quasi-steady state has the `Δω` component `ΔP_L/(K_R + D)`. -/
@[tmio M, powerlib_domain] theorem rest_deviation :
    WithLp.ofLp ((0 : ℝ²) - steadyState D K ΔPL) 0 = ΔPL / (K + D) := by
  simp [steadyState, neg_div]

/-- From rest the deviation from the quasi-steady state has the initial `Δω` slope `−ΔP_L/M`
(the initial RoCoF). -/
@[tmio M, powerlib_domain] theorem rest_slope (hKD : K + D ≠ 0) :
    ((plant M D K Tg).A *ᵥ WithLp.ofLp ((0 : ℝ²) - steadyState D K ΔPL)) 0 = -ΔPL / M := by
  simp [plant, steadyState, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  field_simp
  ring

/-- For a load increase the phase point of the response from rest is
`ΔP_L/(M ω_d) · (σ − 1/T_g + j ω_d)`. -/
@[tmio M, powerlib_domain] theorem dampedRespPhase_eq (hM : 0 < M) (hTg : 0 < Tg) (hD : 0 ≤ D)
    (hKD : 0 < K + D) (hζ : dampingRatio M D K Tg < 1) :
    LTI.dampedRespPhase (decayRate M D K Tg) (dampedFreq M D K Tg) (ΔPL / (K + D)) (-ΔPL / M) =
      ((ΔPL / (M * dampedFreq M D K Tg) : ℝ) : ℂ) *
        ⟨decayRate M D K Tg - 1 / Tg, dampedFreq M D K Tg⟩ := by
  have hsum := decayRate_sq_add_dampedFreq_sq hM hTg hD hKD hζ
  rw [natFreq_sq hM hTg (by linarith)] at hsum
  have hωd := (dampedFreq_pos hM hTg hD hKD hζ).ne'
  have hM' := hM.ne'
  have hTg' := hTg.ne'
  have hKD' := hKD.ne'
  apply Complex.ext
  · simp only [LTI.dampedRespPhase, Complex.re_ofReal_mul]
    rw [hsum]
    field_simp
    ring
  · simp only [LTI.dampedRespPhase, Complex.im_ofReal_mul]
    field_simp

/-- For a load increase the nadir time is the first critical time of the response from rest. -/
@[tmio M, powerlib_domain] theorem nadirTime_eq_dampedRespCrit (hM : 0 < M) (hTg : 0 < Tg)
    (hD : 0 ≤ D) (hKD : 0 < K + D) (hP : 0 < ΔPL) (hζ : dampingRatio M D K Tg < 1) :
    nadirTime M D K Tg = LTI.dampedRespCrit (decayRate M D K Tg) (dampedFreq M D K Tg)
      (ΔPL / (K + D)) (-ΔPL / M) := by
  rw [LTI.dampedRespCrit, dampedRespPhase_eq hM hTg hD hKD hζ, Complex.arg_real_mul _
    (div_pos hP (mul_pos hM (dampedFreq_pos hM hTg hD hKD hζ))), nadirTime]

/-- For a load increase the nadir value is the value of the response from rest at its first
critical time: `−ΔP_L/(K_R + D) − (ω_d ρ/(σ² + ω_d²)) e^{−σ t_nadir}`, `ρ` the norm of the phase
point. -/
@[tmio M, powerlib_domain] theorem nadirValue_eq (hM : 0 < M) (hTg : 0 < Tg) (hD : 0 ≤ D)
    (hKD : 0 < K + D) (hP : 0 < ΔPL) (hζ : dampingRatio M D K Tg < 1) :
    nadirValue M D K Tg ΔPL = -ΔPL / (K + D) - dampedFreq M D K Tg *
      ‖LTI.dampedRespPhase (decayRate M D K Tg) (dampedFreq M D K Tg) (ΔPL / (K + D))
        (-ΔPL / M)‖ / (decayRate M D K Tg ^ 2 + dampedFreq M D K Tg ^ 2) *
          Real.exp (-(decayRate M D K Tg * nadirTime M D K Tg)) := by
  have hωd := dampedFreq_pos hM hTg hD hKD hζ
  have hsum := decayRate_sq_add_dampedFreq_sq hM hTg hD hKD hζ
  have hn := natFreq_sq (D := D) (K := K) hM hTg (by linarith)
  have hsq : Real.sqrt (1 - 2 * decayRate M D K Tg * Tg + natFreq M D K Tg ^ 2 * Tg ^ 2) =
      Tg * ‖(⟨decayRate M D K Tg - 1 / Tg, dampedFreq M D K Tg⟩ : ℂ)‖ := by
    rw [← hsum, show 1 - 2 * decayRate M D K Tg * Tg +
        (decayRate M D K Tg ^ 2 + dampedFreq M D K Tg ^ 2) * Tg ^ 2 =
        (Tg * ‖(⟨decayRate M D K Tg - 1 / Tg, dampedFreq M D K Tg⟩ : ℂ)‖) ^ 2 by
      rw [mul_pow, Complex.sq_norm, Complex.normSq_mk]
      field_simp
      ring]
    exact Real.sqrt_sq (by positivity)
  have hM' := hM.ne'
  have hTg' := hTg.ne'
  have hKD' := hKD.ne'
  have hDK : D + K ≠ 0 := by linarith
  unfold nadirValue
  rw [dampedRespPhase_eq hM hTg hD hKD hζ, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (div_pos hP (mul_pos hM hωd)).le, hsq, hsum, hn]
  field_simp
  ring

/-- The nadir is strictly below the quasi-steady state `−ΔP_L/(K_R + D)`. -/
@[tmio M, powerlib_domain] theorem nadirValue_lt (hM : 0 < M) (hTg : 0 < Tg) (hD : 0 ≤ D)
    (hKD : 0 < K + D) (hP : 0 < ΔPL) (hζ : dampingRatio M D K Tg < 1) :
    nadirValue M D K Tg ΔPL < -ΔPL / (K + D) := by
  have hωd := dampedFreq_pos hM hTg hD hKD hζ
  have hR : 0 < Real.sqrt (1 - 2 * decayRate M D K Tg * Tg + natFreq M D K Tg ^ 2 * Tg ^ 2) := by
    rw [← decayRate_sq_add_dampedFreq_sq hM hTg hD hKD hζ]
    have h1 := sq_nonneg (1 - decayRate M D K Tg * Tg)
    have h2 := mul_pos (mul_pos hωd hωd) (mul_pos hTg hTg)
    exact Real.sqrt_pos.2 (by nlinarith)
  have hc : 0 < ΔPL / (K + D) := div_pos hP hKD
  unfold nadirValue
  have := mul_pos (mul_pos hc hR) (Real.exp_pos (-(decayRate M D K Tg * nadirTime M D K Tg)))
  rw [neg_div]
  nlinarith

/-! ## Implementation evidence (private, trajectory level) -/

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
§1.7 frequency nadir: from rest under a load increase, the frequency deviation of every forward
solution is strictly decreasing up to the nadir time `t_nadir > 0`, attains there its minimum
over all `t ≥ 0`, and that minimum is the closed-form `nadirValue` (the generic first extremum
`LTI.trajectory_nadir_osc2`). -/
@[tmio TM, powerlib_domain] private theorem freq_nadir (hM : 0 < M) (hTg : 0 < Tg) (hD : 0 ≤ D)
    (hKD : 0 < K + D) (hP : 0 < ΔPL) (hζ : dampingRatio M D K Tg < 1) {x : ℝ → ℝ²}
    (hx : IsIntegralCurveOn x (fun _ y => (plant M D K Tg).inputField (load ΔPL) y) (Ici 0))
    (h0 : x 0 = 0) :
    0 < nadirTime M D K Tg ∧ StrictAntiOn (fun t => x t 0) (Icc 0 (nadirTime M D K Tg)) ∧
      IsMinOn (fun t => x t 0) (Ici 0) (nadirTime M D K Tg) ∧
      x (nadirTime M D K Tg) 0 = nadirValue M D K Tg ΔPL := by
  have hr : -ΔPL / M < 0 := by rw [neg_div]; exact neg_neg_of_pos (div_pos hP hM)
  have h := LTI.trajectory_nadir_osc2 (plant M D K Tg)
    ((isEquilibrium_iff hM.ne' hTg.ne' hKD.ne' _).2 rfl) (trace_A hM hTg hKD)
    (det_A hM hTg hD hKD hζ) (dampedFreq_pos hM hTg hD hKD hζ) (decayRate_nonneg hM hTg hD hKD)
    hx 0 (a := ΔPL / (K + D)) (r := -ΔPL / M) (by rw [h0]; exact rest_deviation)
    (by rw [h0]; exact rest_slope hKD.ne') hr
  rwa [steadyState_zero, ← nadirTime_eq_dampedRespCrit hM hTg hD hKD hP hζ,
    ← nadirValue_eq hM hTg hD hKD hP hζ] at h

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
Successive extrema: at `t_nadir + kπ/ω_d` the frequency derivative vanishes and the deviation
from the quasi-steady state is multiplied by `(−e^{−σπ/ω_d})^k`. -/
@[tmio TM, powerlib_domain] private theorem nadir_successive (hM : 0 < M) (hTg : 0 < Tg)
    (hD : 0 ≤ D) (hKD : 0 < K + D) (hP : 0 < ΔPL) (hζ : dampingRatio M D K Tg < 1)
    {x : ℝ → ℝ²}
    (hx : IsIntegralCurveOn x (fun _ y => (plant M D K Tg).inputField (load ΔPL) y) (Ici 0))
    (h0 : x 0 = 0) (k : ℕ) :
    HasDerivWithinAt (fun t => x t 0) 0 (Ici 0)
        (nadirTime M D K Tg + k * (Real.pi / dampedFreq M D K Tg)) ∧
      x (nadirTime M D K Tg + k * (Real.pi / dampedFreq M D K Tg)) 0 + ΔPL / (K + D) =
        (-Real.exp (-(decayRate M D K Tg * (Real.pi / dampedFreq M D K Tg)))) ^ k *
          (x (nadirTime M D K Tg) 0 + ΔPL / (K + D)) := by
  have hωd := dampedFreq_pos hM hTg hD hKD hζ
  have hT := nadirTime_eq_dampedRespCrit hM hTg hD hKD hP hζ
  have hT0 : 0 < nadirTime M D K Tg := (freq_nadir hM hTg hD hKD hP hζ hx h0).1
  have hx' : ∀ {t : ℝ}, 0 ≤ t → x t 0 + ΔPL / (K + D) = LTI.dampedResp (decayRate M D K Tg)
      (dampedFreq M D K Tg) (ΔPL / (K + D)) (-ΔPL / M) t := fun ht => by
    rw [LTI.trajectory_apply_eq_dampedResp (plant M D K Tg)
      ((isEquilibrium_iff hM.ne' hTg.ne' hKD.ne' _).2 rfl) (trace_A hM hTg hKD)
      (det_A hM hTg hD hKD hζ) hωd.ne' hx 0 ht, h0, rest_deviation,
      rest_slope hKD.ne', steadyState_zero]
    ring
  have hpt : ∀ j : ℕ, 0 ≤ nadirTime M D K Tg + j * (Real.pi / dampedFreq M D K Tg) :=
    fun j => by have := Real.pi_pos; positivity
  refine ⟨?_, ?_⟩
  · have hd := (LTI.hasDerivAt_dampedResp_crit_add (σ := decayRate M D K Tg)
      (a := ΔPL / (K + D)) (r := -ΔPL / M) hωd.ne' k).hasDerivWithinAt (s := Ici 0)
    rw [← hT] at hd
    exact (hd.sub_const (ΔPL / (K + D))).congr (fun y hy => eq_sub_of_add_eq (hx' hy))
      (eq_sub_of_add_eq (hx' (hpt k)))
  · rw [hx' (hpt k), hx' hT0.le]
    induction k with
    | zero => simp
    | succ j ih =>
      rw [show nadirTime M D K Tg + ((j + 1 : ℕ) : ℝ) * (Real.pi / dampedFreq M D K Tg) =
        nadirTime M D K Tg + j * (Real.pi / dampedFreq M D K Tg) +
          Real.pi / dampedFreq M D K Tg by push_cast; ring,
        LTI.dampedResp_add_half_period hωd.ne', ih, pow_succ]
      ring

end powerlib.Frequency.SwingGovernor
