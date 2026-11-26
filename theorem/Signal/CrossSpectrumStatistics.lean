import dependencies.Mathlib
import theorem.Attributes
import theorem.Signal.CrossSpectrum
import Mathlib.Probability.Independence.Integration

/-! # Statistics of the cross-spectrum index

The second-order statistics behind the claims "`C_rg ≅ 1` for a natural oscillation, `C_rg < 1`
for a forced one" of the cross-spectrum index: for three independent windows the expectation
`E[S̄_r S_g]` of the cross-spectrum difference `S = Ȳ₁Y₂ − Ȳ₂Y₃` depends only on the first and
second moments of each window, and for the window model
`Y_{x,w} = c_x + β_x Z_w + N_{x,w}` (deterministic on-bin part, common random sinusoid, channel
noise) the expectations and the index have closed forms, from which the natural-case value close
to `1`, the forced-case value `0`, and the effect of partially common noise are read off exactly.

Scope.
* Probability model: a probability space `(Ω, P)`; the window values (the scaled single-bin DFTs
  (3-20) of the three windows of one data section) are complex random variables. The expectation
  of (3-22) is the expectation `∫ · ∂P` of this model (`momentIndex`); the empirical index over
  data sections (`CrossSpectrum.index`) estimates it, which is not formalized (no law of large
  numbers is applied, and overlapping sections are not independent).
* Window model (`modelDFT`): `Y_{x,w} = c_x + β_x Z_w + N_{x,w}`, `x ∈ {r, g}`, `w ∈ {1, 2, 3}`
  (`Fin 3`). Hypotheses, stated explicitly in each theorem: the window vectors
  `(Z_w, N_{r,w}, N_{g,w})` are independent across windows (`iIndepFun`) and square-integrable;
  in each window `Z_w`, `N_{x,w}` are centred, `Z_w` is independent of `(N_{r,w}, N_{g,w})`, the
  second moments are `E|Z_w|² = v`, `E|N_{x,w}|² = v_x`, `E[N_{r,w} N̄_{g,w}] = ρ` (the same in
  every window), and the variables are circular: `E Z_w² = 0`, `E N_{x,w}² = 0`,
  `E[N_{r,w} N_{g,w}] = 0`. Fourth moments are not needed: each product in `S̄_r S_g` contains
  at most two values of the same window.
* The natural case of (3-18) is `c_x = γβ_x`: the persisting "Transient" term and the "Noise 1"
  random sinusoid share the channel factor `𝐜_x u_n` of the undamped mode (TR-110's output row
  `𝐜_x`, `CrossSpectrum.residue_eq_mul`), the common factors `v_n x(0)` and `v_n b_{2l}` being
  absorbed in `γ` and `Z`; the forced case of (3-19) is `β_x = 0`; "Noise 2" / "Noise" is `N`.
  That the on-bin DFTs of the sampled responses have this structure (on-bin frequency, no
  leakage, vanishing image term as in `CrossSpectrum.dft_rankOne_of_modal`, independence of
  windows separated by `Δk ≥ N_T`) is the model boundary, not derived.
* Generic mathematics; no power-system model is selected.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.5, eqs. (3-18)–(3-22)
("Using extensive algebra, Xie and Trudnowski show that if the system is under a natural
oscillation condition, then `C_rg ≅ 1`. If the system is under a forced oscillation condition,
then `C_rg < 1`"; "the three windows are assumed to remain independent"); R. Xie and
D. J. Trudnowski, "Distinguishing between natural and forced oscillations using a cross-spectrum
index", IEEE PES GM 2017. The deterministic algebra is `theorem/Signal/CrossSpectrum.lean`.

Corrections and sharpenings.
* Natural case: `C_rg = 1/((1 + ρ_r)(1 + ρ_r')(1 + ρ_g)(1 + ρ_g'))` exactly, with the
  noise-to-signal ratios `ρ_x = v_x/(|β_x|² v)`, `ρ_x' = v_x/(|β_x|²(2|γ|² + v))`; so
  `1 − C_rg ≤ ρ_r + ρ_r' + ρ_g + ρ_g'` and `C_rg = 1` only without channel noise. "`≅ 1`" means
  "close to `1` when the random sinusoid dominates the channel noise".
* Forced case: `C_rg = 0` exactly when the channel noises are uncorrelated (`ρ = 0`). With
  partially common noise (`|ρ|² < v_r v_g`) still `C_rg < 1`, but `C_rg > 0` in general and not
  bounded away from `1`: equal forced parts and noise correlation `ρ = tw` give
  `C_rg = (t(2|c|² + tw)/(2|c|² + w))² → 1` as `t → 1` (`modelIndex_forced_common`), and for pure
  noise `C_rg = (|ρ|²/(v_r v_g))²` (`modelIndex_noise`). The
  separation of the two cases therefore requires channel noise that is not strongly correlated
  across channels, a condition the source does not state.

Results.
* `integral_conj_crossDiff_mul` — for independent windows,
  `E[S̄_r S_g] = K₁K̄₂ + K₂K̄₃ − m_{r,1}m_{g,3}J̄₂ − m̄_{g,1}m̄_{r,3}J₂` in the window moments;
  `integral_conj_crossDiff_mul_stationary` — with stationary moments and circular fluctuations
  `E[S̄_r S_g] = 2(|K|² − |a|²|b|²)`.
* `modelDFT`, `crossSpec`, `momentIndex`, `momentIndex_le_one` — the model, the difference
  function (3-21) of a channel, the index (3-22) with the model expectation, and `0 ≤ C ≤ 1`
  (Cauchy–Schwarz, `integral_mul_norm_le_Lp_mul_Lq`).
* `integral_window_moments` — `E[Y_r Ȳ_g] = c_r c̄_g + β_r β̄_g v + ρ`, `E[Y_r Y_g] = c_r c_g`;
  `integral_conj_crossSpec_model` — `E[S̄_r S_g] = 2(|c_r c̄_g + β_r β̄_g v + ρ|² − |c_r|²|c_g|²)`;
  `integral_norm_sq_crossSpec_model` — `E|S_r|² = 2((|c_r|² + |β_r|²v + v_r)² − |c_r|⁴)`.
* `modelIndex`, `momentIndex_model` — the index of the window model in closed form.
* Forced: `modelIndex_forced` (`β = 0`, `ρ = 0`: `C = 0`), `modelIndex_forced_eq`,
  `modelIndex_forced_lt_one` (`|ρ|² < v_r v_g`: `C < 1`), `modelIndex_forced_pos_iff`,
  `modelIndex_forced_common` (a forced index arbitrarily close to `1`), `modelIndex_noise`.
* Natural: `modelIndex_natural`, `one_sub_modelIndex_natural_le`, `modelIndex_natural_eq_one_iff`.
-/

noncomputable section
namespace powerlib.Signal.CrossSpectrumStatistics

open MeasureTheory ProbabilityTheory Complex
open CrossSpectrum (crossDiff)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ## Three independent windows -/

/-- Product of three functions of three independent windows: integrable, and its expectation is
the product of the expectations. -/
@[tmio T, powerlib_foundation] private theorem integral_triple [IsProbabilityMeasure P]
    {V : Fin 3 → Ω → ℂ × ℂ} (hind : iIndepFun V P) (hV : ∀ w, AEMeasurable (V w) P)
    (f₀ f₁ f₂ : ℂ × ℂ → ℂ) (hf₀ : Continuous f₀) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (h₀ : Integrable (fun ω => f₀ (V 0 ω)) P) (h₁ : Integrable (fun ω => f₁ (V 1 ω)) P)
    (h₂ : Integrable (fun ω => f₂ (V 2 ω)) P) :
    Integrable (fun ω => f₀ (V 0 ω) * f₁ (V 1 ω) * f₂ (V 2 ω)) P ∧
      ∫ ω, f₀ (V 0 ω) * f₁ (V 1 ω) * f₂ (V 2 ω) ∂P =
        (∫ ω, f₀ (V 0 ω) ∂P) * (∫ ω, f₁ (V 1 ω) ∂P) * ∫ ω, f₂ (V 2 ω) ∂P := by
  constructor
  · have i01 : IndepFun (fun ω => f₀ (V 0 ω)) (fun ω => f₁ (V 1 ω)) P :=
      (hind.indepFun (by decide : (0 : Fin 3) ≠ 1)).comp hf₀.measurable hf₁.measurable
    have hp : IndepFun (fun ω => (V 0 ω, V 1 ω)) (V 2) P :=
      hind.indepFun_prodMk₀ hV 0 1 2 (by decide) (by decide)
    have i2 : IndepFun (fun ω => f₀ (V 0 ω) * f₁ (V 1 ω)) (fun ω => f₂ (V 2 ω)) P :=
      hp.comp (φ := fun p : (ℂ × ℂ) × (ℂ × ℂ) => f₀ p.1 * f₁ p.2)
        (by fun_prop) hf₂.measurable
    exact i2.integrable_mul (i01.integrable_mul h₀ h₁) h₂
  · have h := hind.integral_fun_prod_comp (f := fun i => ![f₀, f₁, f₂] i) hV (fun i => by
      fin_cases i <;> simp <;> fun_prop)
    simpa [Fin.prod_univ_three] using h

/-- **Second moment of the cross-spectrum difference for independent windows.** If the window
value pairs `(Y_{r,w}, Y_{g,w})`, `w = 1, 2, 3`, are independent and square-integrable, then
`E[S̄_r S_g] = K₁K̄₂ + K₂K̄₃ − m_{r,1} m_{g,3} J̄₂ − m̄_{g,1} m̄_{r,3} J₂` with the window moments
`m_{x,w} = E Y_{x,w}`, `K_w = E[Y_{r,w} Ȳ_{g,w}]`, `J_w = E[Y_{r,w} Y_{g,w}]`. Only second moments
of each window enter. -/
@[tmio T, powerlib_foundation] theorem integral_conj_crossDiff_mul [IsProbabilityMeasure P]
    {Yr Yg : Fin 3 → Ω → ℂ} (hind : iIndepFun (fun w ω => (Yr w ω, Yg w ω)) P)
    (hr : ∀ w, MemLp (Yr w) 2 P) (hg : ∀ w, MemLp (Yg w) 2 P) :
    ∫ ω, (starRingEnd ℂ) (crossDiff (Yr 0 ω) (Yr 1 ω) (Yr 2 ω)) *
        crossDiff (Yg 0 ω) (Yg 1 ω) (Yg 2 ω) ∂P =
      (∫ ω, Yr 0 ω * (starRingEnd ℂ) (Yg 0 ω) ∂P) *
          (starRingEnd ℂ) (∫ ω, Yr 1 ω * (starRingEnd ℂ) (Yg 1 ω) ∂P) +
        (∫ ω, Yr 1 ω * (starRingEnd ℂ) (Yg 1 ω) ∂P) *
          (starRingEnd ℂ) (∫ ω, Yr 2 ω * (starRingEnd ℂ) (Yg 2 ω) ∂P) -
        (∫ ω, Yr 0 ω ∂P) * (∫ ω, Yg 2 ω ∂P) * (starRingEnd ℂ) (∫ ω, Yr 1 ω * Yg 1 ω ∂P) -
        (starRingEnd ℂ) (∫ ω, Yg 0 ω ∂P) * (starRingEnd ℂ) (∫ ω, Yr 2 ω ∂P) *
          (∫ ω, Yr 1 ω * Yg 1 ω ∂P) := by
  set V : Fin 3 → Ω → ℂ × ℂ := fun w ω => (Yr w ω, Yg w ω)
  have hV : ∀ w, AEMeasurable (V w) P := fun w =>
    (hr w).aestronglyMeasurable.aemeasurable.prodMk (hg w).aestronglyMeasurable.aemeasurable
  -- window factors
  have iY : ∀ (Y : Fin 3 → Ω → ℂ), (∀ w, MemLp (Y w) 2 P) → ∀ w, Integrable (Y w) P :=
    fun Y hY w => (hY w).integrable one_le_two
  have iYc : ∀ (Y : Fin 3 → Ω → ℂ), (∀ w, MemLp (Y w) 2 P) → ∀ w,
      Integrable (fun ω => (starRingEnd ℂ) (Y w ω)) P :=
    fun Y hY w => (hY w).star.integrable one_le_two
  have iRG : ∀ w, Integrable (fun ω => Yr w ω * (starRingEnd ℂ) (Yg w ω)) P :=
    fun w => (hr w).integrable_mul (hg w).star
  have iRGc : ∀ w, Integrable (fun ω => (starRingEnd ℂ) (Yr w ω) * Yg w ω) P :=
    fun w => (hr w).star.integrable_mul (hg w)
  have iRGp : ∀ w, Integrable (fun ω => Yr w ω * Yg w ω) P :=
    fun w => (hr w).integrable_mul (hg w)
  have iRGpc : ∀ w, Integrable (fun ω => (starRingEnd ℂ) (Yr w ω) * (starRingEnd ℂ) (Yg w ω)) P :=
    fun w => (hr w).star.integrable_mul (hg w).star
  have i1 := integral_triple hind hV (fun p => p.1 * (starRingEnd ℂ) p.2)
    (fun p => (starRingEnd ℂ) p.1 * p.2) (fun _ => 1) (by fun_prop) (by fun_prop) (by fun_prop)
    (iRG 0) (iRGc 1) (integrable_const _)
  have i2 := integral_triple hind hV (fun p => p.1) (fun p => (starRingEnd ℂ) p.1 * (starRingEnd ℂ) p.2)
    (fun p => p.2) (by fun_prop) (by fun_prop) (by fun_prop) (iY Yr hr 0) (iRGpc 1) (iY Yg hg 2)
  have i3 := integral_triple hind hV (fun p => (starRingEnd ℂ) p.2) (fun p => p.1 * p.2)
    (fun p => (starRingEnd ℂ) p.1) (by fun_prop) (by fun_prop) (by fun_prop) (iYc Yg hg 0) (iRGp 1)
    (iYc Yr hr 2)
  have i4 := integral_triple hind hV (fun _ => 1) (fun p => p.1 * (starRingEnd ℂ) p.2)
    (fun p => (starRingEnd ℂ) p.1 * p.2) (by fun_prop) (by fun_prop) (by fun_prop)
    (integrable_const _) (iRG 1) (iRGc 2)
  simp only [V] at i1 i2 i3 i4
  have e : ∀ ω, (starRingEnd ℂ) (crossDiff (Yr 0 ω) (Yr 1 ω) (Yr 2 ω)) *
      crossDiff (Yg 0 ω) (Yg 1 ω) (Yg 2 ω) =
      Yr 0 ω * (starRingEnd ℂ) (Yg 0 ω) * ((starRingEnd ℂ) (Yr 1 ω) * Yg 1 ω) * 1 -
        Yr 0 ω * ((starRingEnd ℂ) (Yr 1 ω) * (starRingEnd ℂ) (Yg 1 ω)) * Yg 2 ω -
        (starRingEnd ℂ) (Yg 0 ω) * (Yr 1 ω * Yg 1 ω) * (starRingEnd ℂ) (Yr 2 ω) +
        1 * (Yr 1 ω * (starRingEnd ℂ) (Yg 1 ω)) * ((starRingEnd ℂ) (Yr 2 ω) * Yg 2 ω) := by
    intro ω
    simp only [crossDiff, map_sub, map_mul, Complex.conj_conj]
    ring
  simp_rw [e]
  obtain ⟨j1, k1⟩ := i1
  obtain ⟨j2, k2⟩ := i2
  obtain ⟨j3, k3⟩ := i3
  obtain ⟨j4, k4⟩ := i4
  rw [integral_add ((j1.sub' j2).sub' j3) j4, integral_sub (j1.sub' j2) j3,
    integral_sub j1 j2, k1, k2, k3, k4]
  have c1 : ∀ w, ∫ ω, (starRingEnd ℂ) (Yr w ω) * Yg w ω ∂P =
      (starRingEnd ℂ) (∫ ω, Yr w ω * (starRingEnd ℂ) (Yg w ω) ∂P) := fun w => by
    rw [← integral_conj]; congr 1; ext ω; simp [mul_comm]
  have c2 : ∀ w, ∫ ω, (starRingEnd ℂ) (Yr w ω) * (starRingEnd ℂ) (Yg w ω) ∂P =
      (starRingEnd ℂ) (∫ ω, Yr w ω * Yg w ω ∂P) := fun w => by
    rw [← integral_conj]; congr 1; ext ω; simp
  have c3 : ∀ (Y : Fin 3 → Ω → ℂ) w, ∫ ω, (starRingEnd ℂ) (Y w ω) ∂P =
      (starRingEnd ℂ) (∫ ω, Y w ω ∂P) := fun Y w => integral_conj
  rw [c1, c1, c2, c3, c3]
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-- **Stationary windows.** If every window has the means `E Y_{r,w} = a`, `E Y_{g,w} = b`, the
cross moment `E[Y_{r,w} Ȳ_{g,w}] = K` and the pseudo-moment `E[Y_{r,w} Y_{g,w}] = ab` (circular
fluctuations), then `E[S̄_r S_g] = 2(|K|² − |a|²|b|²)`, a real number. -/
@[tmio T, powerlib_foundation] theorem integral_conj_crossDiff_mul_stationary
    [IsProbabilityMeasure P] {Yr Yg : Fin 3 → Ω → ℂ}
    (hind : iIndepFun (fun w ω => (Yr w ω, Yg w ω)) P)
    (hr : ∀ w, MemLp (Yr w) 2 P) (hg : ∀ w, MemLp (Yg w) 2 P) {a b K : ℂ}
    (ha : ∀ w, ∫ ω, Yr w ω ∂P = a) (hb : ∀ w, ∫ ω, Yg w ω ∂P = b)
    (hK : ∀ w, ∫ ω, Yr w ω * (starRingEnd ℂ) (Yg w ω) ∂P = K)
    (hJ : ∀ w, ∫ ω, Yr w ω * Yg w ω ∂P = a * b) :
    ∫ ω, (starRingEnd ℂ) (crossDiff (Yr 0 ω) (Yr 1 ω) (Yr 2 ω)) *
        crossDiff (Yg 0 ω) (Yg 1 ω) (Yg 2 ω) ∂P =
      ((2 * (‖K‖ ^ 2 - ‖a‖ ^ 2 * ‖b‖ ^ 2) : ℝ) : ℂ) := by
  rw [integral_conj_crossDiff_mul hind hr hg, hK, hK, hK, ha, ha, hb, hb, hJ, map_mul]
  have e1 : K * (starRingEnd ℂ) K = (‖K‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  have e2 : a * (starRingEnd ℂ) a = (‖a‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  have e3 : b * (starRingEnd ℂ) b = (‖b‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  push_cast
  linear_combination 2 * e1 - 2 * (a * (starRingEnd ℂ) a) * e3 - 2 * (‖b‖ : ℂ) ^ 2 * e2

/-! ## The window model: common random sinusoid, deterministic part, channel noise -/

/-- Expectation of a product of two affine window values `c + βZ + N` and `d + γW + M`. -/
@[tmio T, powerlib_foundation] private theorem integral_affine_mul [IsProbabilityMeasure P]
    {Z N W M : Ω → ℂ} (hZ : MemLp Z 2 P) (hN : MemLp N 2 P) (hW : MemLp W 2 P) (hM : MemLp M 2 P)
    (c β d γ : ℂ) :
    ∫ ω, (c + β * Z ω + N ω) * (d + γ * W ω + M ω) ∂P =
      c * d + c * γ * (∫ ω, W ω ∂P) + c * (∫ ω, M ω ∂P) + β * d * (∫ ω, Z ω ∂P) +
        β * γ * (∫ ω, Z ω * W ω ∂P) + β * (∫ ω, Z ω * M ω ∂P) + d * (∫ ω, N ω ∂P) +
        γ * (∫ ω, N ω * W ω ∂P) + (∫ ω, N ω * M ω ∂P) := by
  have iZ := hZ.integrable one_le_two
  have iN := hN.integrable one_le_two
  have iW := hW.integrable one_le_two
  have iM := hM.integrable one_le_two
  have iZW : Integrable (fun ω => Z ω * W ω) P := hZ.integrable_mul hW
  have iZM : Integrable (fun ω => Z ω * M ω) P := hZ.integrable_mul hM
  have iNW : Integrable (fun ω => N ω * W ω) P := hN.integrable_mul hW
  have iNM : Integrable (fun ω => N ω * M ω) P := hN.integrable_mul hM
  have e : ∀ ω, (c + β * Z ω + N ω) * (d + γ * W ω + M ω) =
      ((((((((c * d + c * γ * W ω) + c * M ω) + β * d * Z ω) + β * γ * (Z ω * W ω)) +
        β * (Z ω * M ω)) + d * N ω) + γ * (N ω * W ω)) + N ω * M ω) := fun ω => by ring
  simp_rw [e]
  rw [integral_add, integral_add, integral_add, integral_add, integral_add, integral_add,
    integral_add, integral_add, integral_const, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul]
  · simp
  all_goals first
    | exact integrable_const _
    | exact Integrable.const_mul ‹_› _
    | fun_prop

/-- The window values of one channel in the model: `Y_w = c + β Z_w + N_w` (deterministic
on-bin part `c`, modal factor `β` of the common random sinusoid `Z`, channel noise `N`). -/
def modelDFT (c β : ℂ) (Z N : Fin 3 → Ω → ℂ) : Fin 3 → Ω → ℂ := fun w ω => c + β * Z w ω + N w ω

/-- The cross-spectrum difference (3-21) of the three window values of a channel. -/
def crossSpec (Y : Fin 3 → Ω → ℂ) : Ω → ℂ := fun ω => crossDiff (Y 0 ω) (Y 1 ω) (Y 2 ω)

/-- The cross-spectrum index (3-22) with the expectation of the probability model:
`C = |E{S̄_r S_g}|² / (E{|S_r|²} E{|S_g|²})`. -/
def momentIndex (P : Measure Ω) (Sr Sg : Ω → ℂ) : ℝ :=
  ‖∫ ω, (starRingEnd ℂ) (Sr ω) * Sg ω ∂P‖ ^ 2 / ((∫ ω, ‖Sr ω‖ ^ 2 ∂P) * ∫ ω, ‖Sg ω‖ ^ 2 ∂P)

@[tmio T, powerlib_foundation] private theorem integral_mul_eq_zero_of_indep [IsProbabilityMeasure P]
    {X Y : Ω → ℂ} (hXY : IndepFun X Y P) (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hY0 : ∫ ω, Y ω ∂P = 0) : ∫ ω, X ω * Y ω ∂P = 0 := by
  have h := hXY.integral_fun_comp_mul_comp (f := fun z : ℂ => z) (g := fun z : ℂ => z) hX hY
    (by fun_prop) (by fun_prop)
  rw [h, hY0, mul_zero]

@[tmio T, powerlib_foundation] private theorem integral_mul_conj_eq_zero_of_indep
    [IsProbabilityMeasure P] {X Y : Ω → ℂ} (hXY : IndepFun X Y P) (hX : AEMeasurable X P)
    (hY : AEMeasurable Y P) (hY0 : ∫ ω, Y ω ∂P = 0) :
    ∫ ω, X ω * (starRingEnd ℂ) (Y ω) ∂P = 0 := by
  have h := hXY.integral_fun_comp_mul_comp (f := fun z : ℂ => z)
    (g := fun z : ℂ => (starRingEnd ℂ) z) hX hY (by fun_prop) (by fun_prop)
  rw [h, integral_conj, hY0, map_zero, mul_zero]

/-- **Window moments of the model.** For `Z`, `N_r`, `N_g` square-integrable and centred, `Z`
independent of `(N_r, N_g)`, `E|Z|² = v`, `E Z² = 0` (circular), `E[N_r N̄_g] = ρ`,
`E[N_r N_g] = 0` (circular): the window values `Y_x = c_x + β_x Z + N_x` have
`E[Y_r Ȳ_g] = c_r c̄_g + β_r β̄_g v + ρ` and `E[Y_r Y_g] = c_r c_g`. -/
@[tmio T, powerlib_foundation] theorem integral_window_moments [IsProbabilityMeasure P]
    {Z Nr Ng : Ω → ℂ} (hZ : MemLp Z 2 P) (hNr : MemLp Nr 2 P) (hNg : MemLp Ng 2 P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) (hNr0 : ∫ ω, Nr ω ∂P = 0) (hNg0 : ∫ ω, Ng ω ∂P = 0)
    (hind : IndepFun Z (fun ω => (Nr ω, Ng ω)) P) {v : ℝ}
    (hv : ∫ ω, Z ω * (starRingEnd ℂ) (Z ω) ∂P = v) (hZc : ∫ ω, Z ω * Z ω ∂P = 0) {ρ : ℂ}
    (hρ : ∫ ω, Nr ω * (starRingEnd ℂ) (Ng ω) ∂P = ρ) (hNc : ∫ ω, Nr ω * Ng ω ∂P = 0)
    (cr βr cg βg : ℂ) :
    (∫ ω, (cr + βr * Z ω + Nr ω) * (starRingEnd ℂ) (cg + βg * Z ω + Ng ω) ∂P =
        cr * (starRingEnd ℂ) cg + βr * (starRingEnd ℂ) βg * v + ρ) ∧
      ∫ ω, (cr + βr * Z ω + Nr ω) * (cg + βg * Z ω + Ng ω) ∂P = cr * cg := by
  have mZ := hZ.aestronglyMeasurable.aemeasurable
  have mNr := hNr.aestronglyMeasurable.aemeasurable
  have mNg := hNg.aestronglyMeasurable.aemeasurable
  have iZg : IndepFun Z Ng P := hind.comp measurable_id measurable_snd
  have iNrZ : IndepFun Nr Z P := (hind.comp measurable_id measurable_fst).symm
  have z1 := integral_mul_conj_eq_zero_of_indep iZg mZ mNg hNg0
  have z2 := integral_mul_conj_eq_zero_of_indep iNrZ mNr mZ hZ0
  have z3 := integral_mul_eq_zero_of_indep iZg mZ mNg hNg0
  have z4 := integral_mul_eq_zero_of_indep iNrZ mNr mZ hZ0
  constructor
  · have e : ∀ ω, (cr + βr * Z ω + Nr ω) * (starRingEnd ℂ) (cg + βg * Z ω + Ng ω) =
        (cr + βr * Z ω + Nr ω) * ((starRingEnd ℂ) cg + (starRingEnd ℂ) βg * (starRingEnd ℂ) (Z ω) +
          (starRingEnd ℂ) (Ng ω)) := fun ω => by simp [map_add, map_mul]
    simp_rw [e]
    rw [integral_affine_mul (W := fun ω => (starRingEnd ℂ) (Z ω)) (M := fun ω => (starRingEnd ℂ) (Ng ω))
      hZ hNr hZ.star hNg.star, hv, hρ, z1, z2, integral_conj, integral_conj, hZ0, hNg0, hNr0]
    simp
  · rw [integral_affine_mul hZ hNr hZ hNg, hZc, hNc, z3, z4, hZ0, hNg0, hNr0]
    simp

@[tmio T, powerlib_foundation] private theorem memLp_modelDFT [IsProbabilityMeasure P] {c β : ℂ}
    {Z N : Fin 3 → Ω → ℂ} (hZ : ∀ w, MemLp (Z w) 2 P) (hN : ∀ w, MemLp (N w) 2 P) (w : Fin 3) :
    MemLp (modelDFT c β Z N w) 2 P := by
  exact ((memLp_const c).add ((hZ w).const_mul β)).add (hN w)

@[tmio T, powerlib_foundation] private theorem integral_modelDFT [IsProbabilityMeasure P]
    {c β : ℂ} {Z N : Fin 3 → Ω → ℂ} (hZ : ∀ w, MemLp (Z w) 2 P) (hN : ∀ w, MemLp (N w) 2 P)
    (hZ0 : ∀ w, ∫ ω, Z w ω ∂P = 0) (hN0 : ∀ w, ∫ ω, N w ω ∂P = 0) (w : Fin 3) :
    ∫ ω, modelDFT c β Z N w ω ∂P = c := by
  have iZ := (hZ w).integrable one_le_two
  have iN := (hN w).integrable one_le_two
  simp only [modelDFT]
  rw [integral_add (by fun_prop) iN, integral_add (integrable_const _) (iZ.const_mul β),
    integral_const_mul, hZ0, hN0]
  simp

/-- **`E[S̄_r S_g]` in closed form for the window model.** Channels `Y_{x,w} = c_x + β_x Z_w +
N_{x,w}` (`x = r, g`) over three windows: the window vectors `(Z_w, N_{r,w}, N_{g,w})` are
independent across windows and square-integrable; in each window `Z_w`, `N_{r,w}`, `N_{g,w}` are
centred, `Z_w` is independent of `(N_{r,w}, N_{g,w})`, `E|Z_w|² = v`, `E Z_w² = 0`,
`E[N_{r,w} N̄_{g,w}] = ρ`, `E[N_{r,w} N_{g,w}] = 0`. Then
`E[S̄_r S_g] = 2(|K_{rg}|² − |c_r|²|c_g|²)` with `K_{rg} = c_r c̄_g + β_r β̄_g v + ρ`. -/
@[tmio T, powerlib_foundation] theorem integral_conj_crossSpec_model [IsProbabilityMeasure P]
    {Z Nr Ng : Fin 3 → Ω → ℂ} (hind : iIndepFun (fun w ω => (Z w ω, Nr w ω, Ng w ω)) P)
    (hZ : ∀ w, MemLp (Z w) 2 P) (hNr : ∀ w, MemLp (Nr w) 2 P) (hNg : ∀ w, MemLp (Ng w) 2 P)
    (hZ0 : ∀ w, ∫ ω, Z w ω ∂P = 0) (hNr0 : ∀ w, ∫ ω, Nr w ω ∂P = 0)
    (hNg0 : ∀ w, ∫ ω, Ng w ω ∂P = 0) (hZN : ∀ w, IndepFun (Z w) (fun ω => (Nr w ω, Ng w ω)) P)
    {v : ℝ} (hv : ∀ w, ∫ ω, Z w ω * (starRingEnd ℂ) (Z w ω) ∂P = v)
    (hZc : ∀ w, ∫ ω, Z w ω * Z w ω ∂P = 0) {ρ : ℂ}
    (hρ : ∀ w, ∫ ω, Nr w ω * (starRingEnd ℂ) (Ng w ω) ∂P = ρ)
    (hNc : ∀ w, ∫ ω, Nr w ω * Ng w ω ∂P = 0) (cr βr cg βg : ℂ) :
    ∫ ω, (starRingEnd ℂ) (crossSpec (modelDFT cr βr Z Nr) ω) * crossSpec (modelDFT cg βg Z Ng) ω ∂P =
      ((2 * (‖cr * (starRingEnd ℂ) cg + βr * (starRingEnd ℂ) βg * v + ρ‖ ^ 2 -
        ‖cr‖ ^ 2 * ‖cg‖ ^ 2) : ℝ) : ℂ) := by
  have hind' : iIndepFun (fun w ω => (modelDFT cr βr Z Nr w ω, modelDFT cg βg Z Ng w ω)) P := by
    have := hind.comp (fun _ t => (cr + βr * t.1 + t.2.1, cg + βg * t.1 + t.2.2))
      (fun _ => by fun_prop)
    exact this
  have hm := fun w => integral_window_moments (hZ w) (hNr w) (hNg w) (hZ0 w) (hNr0 w) (hNg0 w)
    (hZN w) (hv w) (hZc w) (hρ w) (hNc w) cr βr cg βg
  exact integral_conj_crossDiff_mul_stationary hind' (memLp_modelDFT hZ hNr) (memLp_modelDFT hZ hNg)
    (integral_modelDFT hZ hNr hZ0 hNr0) (integral_modelDFT hZ hNg hZ0 hNg0)
    (fun w => (hm w).1) (fun w => (hm w).2)

/-- `E|S|²` as the real integral of `‖S‖²`. -/
@[tmio T, powerlib_foundation] private theorem integral_norm_sq_eq {S : Ω → ℂ} {a : ℝ}
    (h : ∫ ω, (starRingEnd ℂ) (S ω) * S ω ∂P = (a : ℂ)) : ∫ ω, ‖S ω‖ ^ 2 ∂P = a := by
  have e : ∀ ω, (starRingEnd ℂ) (S ω) * S ω = ((‖S ω‖ ^ 2 : ℝ) : ℂ) := fun ω => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [e] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-- **`E|S_r|²` in closed form for the window model** (the case `g = r` of
`integral_conj_crossSpec_model`): with `E|N_{r,w}|² = v_r`, `E N_{r,w}² = 0`,
`E|S_r|² = 2((|c_r|² + |β_r|² v + v_r)² − |c_r|⁴) = 2 D_r (2|c_r|² + D_r)`,
`D_r = |β_r|² v + v_r`. -/
@[tmio T, powerlib_foundation] theorem integral_norm_sq_crossSpec_model [IsProbabilityMeasure P]
    {Z N : Fin 3 → Ω → ℂ} (hind : iIndepFun (fun w ω => (Z w ω, N w ω)) P)
    (hZ : ∀ w, MemLp (Z w) 2 P) (hN : ∀ w, MemLp (N w) 2 P)
    (hZ0 : ∀ w, ∫ ω, Z w ω ∂P = 0) (hN0 : ∀ w, ∫ ω, N w ω ∂P = 0)
    (hZN : ∀ w, IndepFun (Z w) (N w) P) {v : ℝ}
    (hv : ∀ w, ∫ ω, Z w ω * (starRingEnd ℂ) (Z w ω) ∂P = v)
    (hZc : ∀ w, ∫ ω, Z w ω * Z w ω ∂P = 0) {vN : ℝ}
    (hvN : ∀ w, ∫ ω, N w ω * (starRingEnd ℂ) (N w ω) ∂P = vN)
    (hNc : ∀ w, ∫ ω, N w ω * N w ω ∂P = 0) (c β : ℂ) :
    ∫ ω, ‖crossSpec (modelDFT c β Z N) ω‖ ^ 2 ∂P =
      2 * ((‖c‖ ^ 2 + ‖β‖ ^ 2 * v + vN) ^ 2 - ‖c‖ ^ 4) := by
  have hind3 : iIndepFun (fun w ω => (Z w ω, N w ω, N w ω)) P :=
    hind.comp (fun _ t => (t.1, t.2, t.2)) (fun _ => by fun_prop)
  have hZN' : ∀ w, IndepFun (Z w) (fun ω => (N w ω, N w ω)) P := fun w =>
    (hZN w).comp (φ := id) (ψ := fun z : ℂ => (z, z)) measurable_id (by fun_prop)
  have h := integral_conj_crossSpec_model hind3 hZ hN hN hZ0 hN0 hN0 hZN' hv hZc hvN hNc c β c β
  refine integral_norm_sq_eq (h.trans ?_)
  congr 1
  have e : c * (starRingEnd ℂ) c + β * (starRingEnd ℂ) β * v + vN =
      ((‖c‖ ^ 2 + ‖β‖ ^ 2 * v + vN : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/-- **Cauchy–Schwarz: `0 ≤ C ≤ 1`** for the moment index of any two square-integrable cross-spectrum
differences (`integral_mul_norm_le_Lp_mul_Lq` with `p = q = 2`). -/
@[tmio T, powerlib_foundation] theorem momentIndex_le_one {Sr Sg : Ω → ℂ} (hr : MemLp Sr 2 P)
    (hg : MemLp Sg 2 P) : 0 ≤ momentIndex P Sr Sg ∧ momentIndex P Sr Sg ≤ 1 := by
  have h0r : 0 ≤ ∫ ω, ‖Sr ω‖ ^ 2 ∂P := integral_nonneg fun _ => by positivity
  have h0g : 0 ≤ ∫ ω, ‖Sg ω‖ ^ 2 ∂P := integral_nonneg fun _ => by positivity
  refine ⟨by unfold momentIndex; positivity, ?_⟩
  have hH := integral_mul_norm_le_Lp_mul_Lq (μ := P) (f := Sr) (g := Sg) Real.HolderConjugate.two_two
    (by simpa using hr) (by simpa using hg)
  have hnorm : ‖∫ ω, (starRingEnd ℂ) (Sr ω) * Sg ω ∂P‖ ≤ ∫ ω, ‖Sr ω‖ * ‖Sg ω‖ ∂P := by
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    congr 1; ext ω; rw [norm_mul, Complex.norm_conj]
  simp only [Real.rpow_two] at hH
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hH
  have hsq : ‖∫ ω, (starRingEnd ℂ) (Sr ω) * Sg ω ∂P‖ ^ 2 ≤
      (∫ ω, ‖Sr ω‖ ^ 2 ∂P) * ∫ ω, ‖Sg ω‖ ^ 2 ∂P := by
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (hnorm.trans hH) 2
    rwa [mul_pow, Real.sq_sqrt h0r, Real.sq_sqrt h0g] at h2
  unfold momentIndex
  rcases (mul_nonneg h0r h0g).eq_or_lt with h | h
  · rw [← h, div_zero]; exact zero_le_one
  · exact (div_le_one h).mpr hsq

/-! ## The index of the window model -/

/-- The closed-form index of the window model:
`(|K_{rg}|² − |c_r|²|c_g|²)² / ((K_r² − |c_r|⁴)(K_g² − |c_g|⁴))` with
`K_{rg} = c_r c̄_g + β_r β̄_g v + ρ`, `K_x = |c_x|² + |β_x|² v + v_x`. -/
def modelIndex (cr βr cg βg ρ : ℂ) (v vr vg : ℝ) : ℝ :=
  (‖cr * (starRingEnd ℂ) cg + βr * (starRingEnd ℂ) βg * v + ρ‖ ^ 2 - ‖cr‖ ^ 2 * ‖cg‖ ^ 2) ^ 2 /
    (((‖cr‖ ^ 2 + ‖βr‖ ^ 2 * v + vr) ^ 2 - ‖cr‖ ^ 4) * ((‖cg‖ ^ 2 + ‖βg‖ ^ 2 * v + vg) ^ 2 - ‖cg‖ ^ 4))

/-- **The cross-spectrum index of the window model in closed form.** Under the moment model of
`integral_conj_crossSpec_model` (with `E|N_{x,w}|² = v_x`, `E N_{x,w}² = 0`, `E[N_{r,w}N_{g,w}] = 0`,
`E[N_{r,w} N̄_{g,w}] = ρ`): `C_{rg} = modelIndex c_r β_r c_g β_g ρ v v_r v_g`. -/
@[tmio T, powerlib_foundation] theorem momentIndex_model [IsProbabilityMeasure P]
    {Z Nr Ng : Fin 3 → Ω → ℂ} (hind : iIndepFun (fun w ω => (Z w ω, Nr w ω, Ng w ω)) P)
    (hZ : ∀ w, MemLp (Z w) 2 P) (hNr : ∀ w, MemLp (Nr w) 2 P) (hNg : ∀ w, MemLp (Ng w) 2 P)
    (hZ0 : ∀ w, ∫ ω, Z w ω ∂P = 0) (hNr0 : ∀ w, ∫ ω, Nr w ω ∂P = 0)
    (hNg0 : ∀ w, ∫ ω, Ng w ω ∂P = 0) (hZN : ∀ w, IndepFun (Z w) (fun ω => (Nr w ω, Ng w ω)) P)
    {v : ℝ} (hv : ∀ w, ∫ ω, Z w ω * (starRingEnd ℂ) (Z w ω) ∂P = v)
    (hZc : ∀ w, ∫ ω, Z w ω * Z w ω ∂P = 0) {vr vg : ℝ} {ρ : ℂ}
    (hvr : ∀ w, ∫ ω, Nr w ω * (starRingEnd ℂ) (Nr w ω) ∂P = vr)
    (hvg : ∀ w, ∫ ω, Ng w ω * (starRingEnd ℂ) (Ng w ω) ∂P = vg)
    (hρ : ∀ w, ∫ ω, Nr w ω * (starRingEnd ℂ) (Ng w ω) ∂P = ρ)
    (hNrc : ∀ w, ∫ ω, Nr w ω * Nr w ω ∂P = 0) (hNgc : ∀ w, ∫ ω, Ng w ω * Ng w ω ∂P = 0)
    (hNc : ∀ w, ∫ ω, Nr w ω * Ng w ω ∂P = 0) (cr βr cg βg : ℂ) :
    momentIndex P (crossSpec (modelDFT cr βr Z Nr)) (crossSpec (modelDFT cg βg Z Ng)) =
      modelIndex cr βr cg βg ρ v vr vg := by
  have hindr : iIndepFun (fun w ω => (Z w ω, Nr w ω)) P :=
    hind.comp (fun _ t => (t.1, t.2.1)) (fun _ => by fun_prop)
  have hindg : iIndepFun (fun w ω => (Z w ω, Ng w ω)) P :=
    hind.comp (fun _ t => (t.1, t.2.2)) (fun _ => by fun_prop)
  have hZNr : ∀ w, IndepFun (Z w) (Nr w) P := fun w =>
    (hZN w).comp (φ := id) (ψ := Prod.fst) measurable_id measurable_fst
  have hZNg : ∀ w, IndepFun (Z w) (Ng w) P := fun w =>
    (hZN w).comp (φ := id) (ψ := Prod.snd) measurable_id measurable_snd
  unfold momentIndex modelIndex
  rw [integral_conj_crossSpec_model hind hZ hNr hNg hZ0 hNr0 hNg0 hZN hv hZc hρ hNc,
    integral_norm_sq_crossSpec_model hindr hZ hNr hZ0 hNr0 hZNr hv hZc hvr hNrc,
    integral_norm_sq_crossSpec_model hindg hZ hNg hZ0 hNg0 hZNg hv hZc hvg hNgc,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [show ∀ x y z : ℝ, (2 * x) ^ 2 / (2 * y * (2 * z)) = x ^ 2 / (y * z) by
    intro x y z
    rw [show (2 * x) ^ 2 = 4 * x ^ 2 by ring, show 2 * y * (2 * z) = 4 * (y * z) by ring,
      mul_div_mul_left _ _ (by norm_num : (4 : ℝ) ≠ 0)]]

/-- `|z + ρ|² − |z|² = 2 Re(z ρ̄) + |ρ|²`. -/
@[tmio T, powerlib_foundation] private theorem norm_add_sq_sub (z ρ : ℂ) :
    ‖z + ρ‖ ^ 2 - ‖z‖ ^ 2 = 2 * (z * (starRingEnd ℂ) ρ).re + ‖ρ‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_add]
  ring

/-- **Forced oscillation, channel-independent noise: `C = 0`.** With no common random sinusoid
(`β_r = β_g = 0`) and uncorrelated channel noise (`ρ = 0`) the expected cross term vanishes:
`|c_r c̄_g|² = |c_r|²|c_g|²`. -/
@[tmio T, powerlib_foundation] theorem modelIndex_forced (cr cg : ℂ) (v vr vg : ℝ) :
    modelIndex cr 0 cg 0 0 v vr vg = 0 := by
  simp [modelIndex, mul_pow]

/-- Forced oscillation with partially common channel noise: the index is
`(2 Re(c_r c̄_g ρ̄) + |ρ|²)² / (v_r(2|c_r|² + v_r) v_g(2|c_g|² + v_g))`. -/
@[tmio T, powerlib_foundation] theorem modelIndex_forced_eq (cr cg ρ : ℂ) (v vr vg : ℝ) :
    modelIndex cr 0 cg 0 ρ v vr vg =
      (2 * (cr * (starRingEnd ℂ) cg * (starRingEnd ℂ) ρ).re + ‖ρ‖ ^ 2) ^ 2 /
        (vr * (2 * ‖cr‖ ^ 2 + vr) * (vg * (2 * ‖cg‖ ^ 2 + vg))) := by
  unfold modelIndex
  have h := norm_add_sq_sub (cr * (starRingEnd ℂ) cg) ρ
  rw [norm_mul, Complex.norm_conj, mul_pow] at h
  simp only [zero_mul, add_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow]
  rw [h]
  congr 1
  ring

/-- **Forced oscillation, partially common noise: `C < 1`.** If the channel noises are not
perfectly correlated, `|ρ|² < v_r v_g` (`v_r, v_g > 0`), the forced index is strictly below `1`. -/
@[tmio T, powerlib_foundation] theorem modelIndex_forced_lt_one (cr cg ρ : ℂ) (v : ℝ) {vr vg : ℝ}
    (hvr : 0 < vr) (hvg : 0 < vg) (hρ : ‖ρ‖ ^ 2 < vr * vg) :
    modelIndex cr 0 cg 0 ρ v vr vg < 1 := by
  rw [modelIndex_forced_eq]
  set a := ‖cr‖
  set b := ‖cg‖
  set p := ‖ρ‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hp : 0 ≤ p := norm_nonneg _
  have hre : |(cr * (starRingEnd ℂ) cg * (starRingEnd ℂ) ρ).re| ≤ a * b * p := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
  have hden : 0 < vr * (2 * a ^ 2 + vr) * (vg * (2 * b ^ 2 + vg)) := by positivity
  rw [div_lt_one hden]
  set x := (cr * (starRingEnd ℂ) cg * (starRingEnd ℂ) ρ).re
  have hX : (2 * x + p ^ 2) ^ 2 ≤ (2 * a * b * p + p ^ 2) ^ 2 := by
    have h1 : |2 * x + p ^ 2| ≤ 2 * a * b * p + p ^ 2 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_two, abs_of_nonneg (sq_nonneg p)]
      nlinarith
    exact sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
  -- AM–GM: `2a²v_g + 2b²v_r ≥ 4ab p`
  have hamgm : 4 * a * b * p ≤ 2 * a ^ 2 * vg + 2 * b ^ 2 * vr := by
    have hsq : (4 * a * b * p) ^ 2 ≤ (2 * a ^ 2 * vg + 2 * b ^ 2 * vr) ^ 2 := by
      nlinarith [sq_nonneg (2 * a ^ 2 * vg - 2 * b ^ 2 * vr),
        mul_le_mul_of_nonneg_left hρ.le (sq_nonneg (a * b))]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  have hs : p ^ 2 < vr * vg := hρ
  have k1 : p ^ 2 * (4 * a ^ 2 * b ^ 2) ≤ vr * vg * (4 * a ^ 2 * b ^ 2) :=
    mul_le_mul_of_nonneg_right hs.le (by positivity)
  have k2 : p ^ 2 * (4 * a * b * p) ≤ vr * vg * (2 * a ^ 2 * vg + 2 * b ^ 2 * vr) :=
    mul_le_mul hs.le hamgm (by positivity) (by positivity)
  have k3 : p ^ 2 * p ^ 2 < vr * vg * (vr * vg) :=
    mul_lt_mul'' hs hs (by positivity) (by positivity)
  calc (2 * x + p ^ 2) ^ 2 ≤ (2 * a * b * p + p ^ 2) ^ 2 := hX
    _ = p ^ 2 * (4 * a ^ 2 * b ^ 2) + p ^ 2 * (4 * a * b * p) + p ^ 2 * p ^ 2 := by ring
    _ < vr * vg * (4 * a ^ 2 * b ^ 2) + vr * vg * (2 * a ^ 2 * vg + 2 * b ^ 2 * vr) +
        vr * vg * (vr * vg) := by linarith
    _ = vr * (2 * a ^ 2 + vr) * (vg * (2 * b ^ 2 + vg)) := by ring

/-- Forced oscillation with partially common noise: `C > 0` exactly when the common-noise cross
term `2 Re(c_r c̄_g ρ̄) + |ρ|²` is nonzero (for instance `ρ ≠ 0` and `Re(c_r c̄_g ρ̄) ≥ 0`). -/
@[tmio T, powerlib_foundation] theorem modelIndex_forced_pos_iff (cr cg ρ : ℂ) (v : ℝ) {vr vg : ℝ}
    (hvr : 0 < vr) (hvg : 0 < vg) :
    0 < modelIndex cr 0 cg 0 ρ v vr vg ↔
      2 * (cr * (starRingEnd ℂ) cg * (starRingEnd ℂ) ρ).re + ‖ρ‖ ^ 2 ≠ 0 := by
  rw [modelIndex_forced_eq]
  have hden : 0 < vr * (2 * ‖cr‖ ^ 2 + vr) * (vg * (2 * ‖cg‖ ^ 2 + vg)) := by positivity
  rw [div_pos_iff_of_pos_right hden]
  exact ⟨fun h hx => by rw [hx] at h; simp at h, fun h => by positivity⟩

/-- **A forced index arbitrarily close to `1`.** Two channels with the same forced part `c`, the
same noise power `w > 0` and noise correlation `ρ = t w` (`0 ≤ t < 1`, partially common noise):
`C = (t(2|c|² + tw)/(2|c|² + w))²`, which tends to `1` as `t → 1`. -/
@[tmio T, powerlib_foundation] theorem modelIndex_forced_common (c : ℂ) (v : ℝ) {w : ℝ} (hw : 0 < w)
    (t : ℝ) :
    modelIndex c 0 c 0 ((t * w : ℝ) : ℂ) v w w =
      (t * (2 * ‖c‖ ^ 2 + t * w) / (2 * ‖c‖ ^ 2 + w)) ^ 2 := by
  rw [modelIndex_forced_eq]
  have hre : (c * (starRingEnd ℂ) c * (starRingEnd ℂ) ((t * w : ℝ) : ℂ)).re = ‖c‖ ^ 2 * (t * w) := by
    rw [Complex.mul_conj, Complex.conj_ofReal, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  rw [hre, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h1 : 0 < 2 * ‖c‖ ^ 2 + w := by positivity
  field_simp

/-- Only noise in both channels (`c = β = 0`): the index is the square of the noise coherence,
`C = (|ρ|²/(v_r v_g))²`, which is any value in `[0, 1)` for partially correlated noise. -/
@[tmio T, powerlib_foundation] theorem modelIndex_noise (ρ : ℂ) (v vr vg : ℝ) :
    modelIndex 0 0 0 0 ρ v vr vg = (‖ρ‖ ^ 2 / (vr * vg)) ^ 2 := by
  simp only [modelIndex, zero_mul, add_zero, zero_add, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, sub_zero, mul_zero]
  rw [div_pow, mul_pow]

/-- **Undamped natural mode, channel-independent noise.** The window values are
`Y_{x,w} = β_x(γ + Z_w) + N_{x,w}`: the modal factor `β_x` multiplies both the deterministic part
`γ` (the persisting transient) and the random sinusoid `Z_w` (so `c_x = γβ_x`), and the channel
noises are uncorrelated (`ρ = 0`). For `v > 0`, `β_r, β_g ≠ 0`, `v_r, v_g ≥ 0`:
`C = 1/((1 + ρ_r)(1 + ρ_r')(1 + ρ_g)(1 + ρ_g'))` with the noise-to-signal ratios
`ρ_x = v_x/(|β_x|² v)`, `ρ_x' = v_x/(|β_x|²(2|γ|² + v))`. -/
@[tmio T, powerlib_foundation] theorem modelIndex_natural {βr βg : ℂ} (hβr : βr ≠ 0) (hβg : βg ≠ 0)
    (γ : ℂ) {v : ℝ} (hv : 0 < v) {vr vg : ℝ} (hvr : 0 ≤ vr) (hvg : 0 ≤ vg) :
    modelIndex (γ * βr) βr (γ * βg) βg 0 v vr vg =
      1 / ((1 + vr / (‖βr‖ ^ 2 * v)) * (1 + vr / (‖βr‖ ^ 2 * (2 * ‖γ‖ ^ 2 + v))) *
        ((1 + vg / (‖βg‖ ^ 2 * v)) * (1 + vg / (‖βg‖ ^ 2 * (2 * ‖γ‖ ^ 2 + v))))) := by
  have hK : γ * βr * (starRingEnd ℂ) (γ * βg) + βr * (starRingEnd ℂ) βg * v + 0 =
      βr * (starRingEnd ℂ) βg * ((‖γ‖ ^ 2 + v : ℝ) : ℂ) := by
    rw [map_mul, add_zero]
    have : γ * (starRingEnd ℂ) γ = ((‖γ‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast at this ⊢
    linear_combination (βr * (starRingEnd ℂ) βg) * this
  have hn : ‖βr * (starRingEnd ℂ) βg * ((‖γ‖ ^ 2 + v : ℝ) : ℂ)‖ = ‖βr‖ * ‖βg‖ * (‖γ‖ ^ 2 + v) := by
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  unfold modelIndex
  rw [hK, hn, norm_mul, norm_mul]
  have hbr : 0 < ‖βr‖ := norm_pos_iff.mpr hβr
  have hbg : 0 < ‖βg‖ := norm_pos_iff.mpr hβg
  have hq : 0 < 2 * ‖γ‖ ^ 2 + v := by positivity
  have h1 : 0 < ‖βr‖ ^ 2 * v + vr := by positivity
  have h2 : 0 < ‖βr‖ ^ 2 * (2 * ‖γ‖ ^ 2 + v) + vr := by positivity
  have h3 : 0 < ‖βg‖ ^ 2 * v + vg := by positivity
  have h4 : 0 < ‖βg‖ ^ 2 * (2 * ‖γ‖ ^ 2 + v) + vg := by positivity
  rw [show ((‖γ‖ * ‖βr‖) ^ 2 + ‖βr‖ ^ 2 * v + vr) ^ 2 - (‖γ‖ * ‖βr‖) ^ 4 =
      (‖βr‖ ^ 2 * v + vr) * (‖βr‖ ^ 2 * (2 * ‖γ‖ ^ 2 + v) + vr) by ring,
    show ((‖γ‖ * ‖βg‖) ^ 2 + ‖βg‖ ^ 2 * v + vg) ^ 2 - (‖γ‖ * ‖βg‖) ^ 4 =
      (‖βg‖ ^ 2 * v + vg) * (‖βg‖ ^ 2 * (2 * ‖γ‖ ^ 2 + v) + vg) by ring]
  field_simp
  ring

/-- `1/∏(1 + x_i) ≥ 1 − Σ x_i` for four nonnegative `x_i` (via `1 + x ≤ eˣ`). -/
@[tmio T, powerlib_foundation] private theorem one_sub_le_inv_prod {x₁ x₂ x₃ x₄ : ℝ} (h₁ : 0 ≤ x₁)
    (h₂ : 0 ≤ x₂) (h₃ : 0 ≤ x₃) (h₄ : 0 ≤ x₄) :
    1 - (x₁ + x₂ + x₃ + x₄) ≤ 1 / ((1 + x₁) * (1 + x₂) * ((1 + x₃) * (1 + x₄))) := by
  have hP : (1 + x₁) * (1 + x₂) * ((1 + x₃) * (1 + x₄)) ≤ Real.exp (x₁ + x₂ + x₃ + x₄) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add]
    have e := fun x : ℝ => (Real.add_one_le_exp x)
    have k1 := e x₁; have k2 := e x₂; have k3 := e x₃; have k4 := e x₄
    rw [add_comm x₁] at k1; rw [add_comm x₂] at k2; rw [add_comm x₃] at k3; rw [add_comm x₄] at k4
    calc (1 + x₁) * (1 + x₂) * ((1 + x₃) * (1 + x₄))
        ≤ Real.exp x₁ * Real.exp x₂ * (Real.exp x₃ * Real.exp x₄) := by gcongr
      _ = _ := by ring
  have hpos : 0 < (1 + x₁) * (1 + x₂) * ((1 + x₃) * (1 + x₄)) := by positivity
  have hexp : 1 - (x₁ + x₂ + x₃ + x₄) ≤ Real.exp (-(x₁ + x₂ + x₃ + x₄)) := by
    linarith [Real.add_one_le_exp (-(x₁ + x₂ + x₃ + x₄))]
  refine hexp.trans ?_
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le hpos hP

/-- **"`C ≅ 1`" made quantitative.** For the undamped natural mode with channel-independent
noise, `1 − C ≤ ρ_r + ρ_r' + ρ_g + ρ_g'` (the noise-to-signal ratios of `modelIndex_natural`):
the index tends to `1` as the channel noise tends to `0`. -/
@[tmio T, powerlib_foundation] theorem one_sub_modelIndex_natural_le {βr βg : ℂ} (hβr : βr ≠ 0)
    (hβg : βg ≠ 0) (γ : ℂ) {v : ℝ} (hv : 0 < v) {vr vg : ℝ} (hvr : 0 ≤ vr) (hvg : 0 ≤ vg) :
    1 - modelIndex (γ * βr) βr (γ * βg) βg 0 v vr vg ≤
      vr / (‖βr‖ ^ 2 * v) + vr / (‖βr‖ ^ 2 * (2 * ‖γ‖ ^ 2 + v)) + vg / (‖βg‖ ^ 2 * v) +
        vg / (‖βg‖ ^ 2 * (2 * ‖γ‖ ^ 2 + v)) := by
  rw [modelIndex_natural hβr hβg γ hv hvr hvg]
  have := one_sub_le_inv_prod (x₁ := vr / (‖βr‖ ^ 2 * v))
    (x₂ := vr / (‖βr‖ ^ 2 * (2 * ‖γ‖ ^ 2 + v))) (x₃ := vg / (‖βg‖ ^ 2 * v))
    (x₄ := vg / (‖βg‖ ^ 2 * (2 * ‖γ‖ ^ 2 + v))) (by positivity) (by positivity) (by positivity)
    (by positivity)
  linarith

/-- For the undamped natural mode with channel-independent noise, `C = 1` exactly when both
channels are noise-free; any channel noise gives `C < 1`. -/
@[tmio T, powerlib_foundation] theorem modelIndex_natural_eq_one_iff {βr βg : ℂ} (hβr : βr ≠ 0)
    (hβg : βg ≠ 0) (γ : ℂ) {v : ℝ} (hv : 0 < v) {vr vg : ℝ} (hvr : 0 ≤ vr) (hvg : 0 ≤ vg) :
    modelIndex (γ * βr) βr (γ * βg) βg 0 v vr vg = 1 ↔ vr = 0 ∧ vg = 0 := by
  rw [modelIndex_natural hβr hβg γ hv hvr hvg]
  have hbr : 0 < ‖βr‖ := norm_pos_iff.mpr hβr
  have hbg : 0 < ‖βg‖ := norm_pos_iff.mpr hβg
  set x₁ := vr / (‖βr‖ ^ 2 * v)
  set x₂ := vr / (‖βr‖ ^ 2 * (2 * ‖γ‖ ^ 2 + v))
  set x₃ := vg / (‖βg‖ ^ 2 * v)
  set x₄ := vg / (‖βg‖ ^ 2 * (2 * ‖γ‖ ^ 2 + v))
  have k₁ : 0 ≤ x₁ := by positivity
  have k₂ : 0 ≤ x₂ := by positivity
  have k₃ : 0 ≤ x₃ := by positivity
  have k₄ : 0 ≤ x₄ := by positivity
  have hpos : 0 < (1 + x₁) * (1 + x₂) * ((1 + x₃) * (1 + x₄)) := by positivity
  rw [div_eq_one_iff_eq hpos.ne', eq_comm]
  constructor
  · intro h
    have hA : 0 ≤ x₂ + x₁ * x₂ := by positivity
    have hB : 0 ≤ x₄ + x₃ * x₄ := by positivity
    have hAB : 0 ≤ (x₁ + x₂ + x₁ * x₂) * (x₃ + x₄ + x₃ * x₄) := by positivity
    have hge : 1 + x₁ + x₃ ≤ (1 + x₁) * (1 + x₂) * ((1 + x₃) * (1 + x₄)) := by
      have e : (1 + x₁) * (1 + x₂) * ((1 + x₃) * (1 + x₄)) =
          1 + (x₁ + x₂ + x₁ * x₂) + (x₃ + x₄ + x₃ * x₄) +
            (x₁ + x₂ + x₁ * x₂) * (x₃ + x₄ + x₃ * x₄) := by ring
      rw [e]; linarith
    have hx1 : x₁ = 0 := by linarith
    have hx3 : x₃ = 0 := by linarith
    have hq : 0 < ‖βr‖ ^ 2 * v := by positivity
    have hq' : 0 < ‖βg‖ ^ 2 * v := by positivity
    exact ⟨by simpa [x₁, hq.ne'] using hx1, by simpa [x₃, hq'.ne'] using hx3⟩
  · rintro ⟨rfl, rfl⟩
    simp [x₁, x₂, x₃, x₄]

end powerlib.Signal.CrossSpectrumStatistics
