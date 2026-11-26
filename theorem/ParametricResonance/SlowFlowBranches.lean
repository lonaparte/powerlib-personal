import theorem.ParametricResonance.TwoToOneAveraging
import theorem.ParametricResonance.Kapitza

/-! # The two unstable branches of the 2:1 slow flow: small-signal and parametric

At the averaged level the principal (2:1) parametric resonance is the slow flow
`Ȧ = −(s + jΔ) A + g A*` (`theorem/ParametricResonance/SlowFlow.lean`): trace `−2s`, determinant
`s² + Δ² − |g|²`, exponents `−s ± √(|g|² − Δ²)`, with `s` the averaged damping (`α₀` of the slow
flow, `σ` of the normal form), `Δ` the detuning from `ω_p/2` and `g` the pump coefficient. Its
unstable set — an exponent with positive real part — is the disjoint union of two branches of a
different nature:

* the small-signal branch `s < 0`: unstable for every pump `g`, also `g = 0` — the instability of
  the unmodulated equilibrium, which no pump removes (the exponents sum to `−2s > 0`; the
  averaged mirror of the Liouville separation `det M = e^{−2sT} > 1`); for `|g| < |Δ|` both
  exponents are `−s ± j√(Δ² − |g|²)`, complex: in the original frame the growing oscillation has
  the frequencies `ω_p/2 ± √(Δ² − |g|²)`, not locked to the pump;
* the parametric branch `s ≥ 0`, `s² + Δ² < |g|²`: a saddle with one real positive exponent
  `−s + √(|g|² − Δ²)`, so the growing oscillation is locked at exactly `ω_p/2`; it requires
  `|g| > √(s² + Δ²)` and is empty at `g = 0`.

For the resonant normal form `ż = (−σ + jΩ) z + c e^{jωt} z̄` this picture is exact at the Floquet
level: the multipliers are exactly `e^{(λ + jω/2)T}` for the slow exponents `λ`, so Floquet
instability is the same disjoint union, the parametric branch has a single real multiplier
`< −1` outside the unit circle, and the weakly pumped small-signal branch has the two multipliers
`e^{(−σ + j(ω/2 ± w'))T}` of modulus `e^{−σT} > 1`. For a complete two-state system with
modulation `ε`, both verdicts of the slow flow hold for all small `ε`.

Scope.
* Slow flow: the real state matrix `slowFlowMatrix s Δ g` of
  `theorem/ParametricResonance/SlowFlow.lean` (real `s`, `Δ`, complex `g`); its exponents are the
  roots of `det(λI − M) = 0` (`Linear.characteristicMatrix`). The averaged model only; the
  averaging step itself is not repeated here.
* Normal form: `NormalForm.nfMatrix σ Ω ω c` of `theorem/ParametricResonance/ResonantNormalForm.lean`
  (state `(Re z, Im z)`, pump frequency `ω > 0`, period `T = 2π/ω`, monodromy
  `Periodic.monodromy … T 0`), with slow-flow parameters `s = σ`, `Δ = ω/2 − Ω`, `g = c`.
* Complete two-state system: `TwoToOne.full s d ω A ε` of
  `theorem/ParametricResonance/TwoToOneAveraging.lean` (`σ = εs`, `ω/2 − Ω = εd`, slow-flow
  pump `g/2` with `g = Element.pump A u r`), statements for all sufficiently small `ε > 0`.
* Generic mathematics; no model family.

Source: first-order averaging of the principal parametric resonance (Nayfeh–Mook, *Nonlinear
Oscillations*, parametrically excited systems: transition curves `s² + Δ² = |g|²`); the slow flow,
its threshold `ε_crit = 2√(α₀² + Δ²)/|𝒢|` and the multiplier `−e^{−α₀T}` of
`theorem/ParametricResonance/SlowFlow.lean` (work-sync
projects/vsc-parametric-oscillation/notes/theory-draft.md §2.2); the monodromy `Φ(T) = −e^{TM}`
of `NormalForm.monodromy_nf`; `TwoToOne.averaging_stable`, `TwoToOne.averaging_unstable`.

Sharpenings.
* The parametric branch includes the conservative limit `s = 0` (there `|g| > |Δ|` gives the real
  exponent `√(|g|² − Δ²) > 0`); with `s > 0` only, the two branches would not cover the unstable
  set.
* Frequency locking separates the branches only for weak pumps: in the small-signal branch with
  `|g| ≥ |Δ|` the unstable exponent `−s + √(|g|² − Δ²)` is real as well. What always separates
  them is the sign of the averaged damping `s`, i.e. of the sum of the exponents.

Results.
* `slowFlow_unstable_iff` — an exponent with `Re λ > 0` iff `Xor (s < 0) (0 ≤ s ∧ s² + Δ² < |g|²)`:
  the two branches are disjoint and their union is the unstable set.
* `smallSignal_complex_roots` — `|g|² < Δ²`: the exponents are exactly `−s ± j w'`,
  `w' = √(Δ² − |g|²) > 0`.
* `parametric_real_roots` — `s ≥ 0`, `s² + Δ² < |g|²`: the exponents are exactly the real
  `λ± = −s ± √(|g|² − Δ²)`, `λ₊ > 0 > λ₋`.
* `trace_exp_slowFlow` — `w² = |g|² − Δ²`: `tr e^{TM} = e^{(−s + w)T} + e^{(−s − w)T}`;
  `exp_add_half_pump` — `e^{(l + jω/2)T} = −e^{lT}` for `T = 2π/ω`.
* `nf_spectrum` — the Floquet multipliers of the normal form are exactly `e^{(λ + jω/2)T}`, `λ` a
  slow-flow exponent.
* `nf_floquetUnstable_iff` — the normal form is Floquet unstable iff
  `Xor (σ < 0) (0 ≤ σ ∧ σ² + (ω/2 − Ω)² < |c|²)`.
* `nf_parametric_locked` — parametric branch: `−e^{λ₊T} < −1` is a multiplier and the only one
  outside the unit circle.
* `nf_smallSignal_unlocked` — `σ < 0`, `|c|² < (ω/2 − Ω)²`: the multipliers are exactly
  `e^{(−σ + j(ω/2 ± w'))T}`, of modulus `e^{−σT} > 1`.
* `averaging_branches` — complete two-state system: an unstable slow exponent gives Floquet
  instability, a Hurwitz slow flow Schur stability, for all small `ε > 0`.
-/

noncomputable section
namespace powerlib.ParametricResonance.Branches

open Matrix Complex Set Filter Topology
open NormalForm (nfMatrix)

/-! ## The two unstable branches of the slow flow -/

section Slow

/-- **The unstable set of the 2:1 slow flow is the disjoint union of two branches.** The slow
flow `[[−s + Re g, Δ + Im g], [−Δ + Im g, −s − Re g]]` has a characteristic root with positive
real part iff exactly one of: the small-signal branch `s < 0` (any pump `g`, also `g = 0`), or
the parametric branch `s ≥ 0` and `s² + Δ² < |g|²`. -/
@[tmio T, powerlib_foundation] theorem slowFlow_unstable_iff (s Δ : ℝ) (g : ℂ) :
    (∃ μ : ℂ, (Linear.characteristicMatrix (slowFlowMatrix s Δ g) μ).det = 0 ∧ 0 < μ.re) ↔
      Xor (s < 0) (0 ≤ s ∧ s ^ 2 + Δ ^ 2 < ‖g‖ ^ 2) := by
  constructor
  · rintro ⟨μ, hμ, hre⟩
    rw [slowFlow_root_iff] at hμ
    by_cases hs : s < 0
    · exact Or.inl ⟨hs, fun h => absurd h.1 (not_le.mpr hs)⟩
    · push Not at hs
      refine Or.inr ⟨⟨hs, ?_⟩, not_lt.mpr hs⟩
      have hre' := congrArg Complex.re hμ
      have him' := congrArg Complex.im hμ
      simp [pow_two, Complex.mul_re, Complex.mul_im] at hre' him'
      have hpos : 0 < μ.re + s := by linarith
      have him0 : μ.im = 0 := by
        have : (μ.re + s) * μ.im = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hpos.ne'
      rw [him0] at hre'
      nlinarith
  · rintro (⟨hs, -⟩ | ⟨⟨hs, hD⟩, -⟩)
    · by_cases hD : Δ ^ 2 ≤ ‖g‖ ^ 2
      · refine ⟨_, (slowFlow_real_roots s Δ g hD).1, ?_⟩
        simp only [Complex.ofReal_re]
        have := Real.sqrt_nonneg (‖g‖ ^ 2 - Δ ^ 2)
        linarith
      · push Not at hD
        set w := √(Δ ^ 2 - ‖g‖ ^ 2)
        have hw : w ^ 2 = Δ ^ 2 - ‖g‖ ^ 2 := Real.sq_sqrt (by linarith)
        refine ⟨-(s : ℂ) + (w : ℂ) * I, ?_, by simp; linarith⟩
        rw [slowFlow_root_iff]
        have hw' : (w : ℂ) ^ 2 = ((Δ ^ 2 - ‖g‖ ^ 2 : ℝ) : ℂ) := by exact_mod_cast hw
        push_cast at hw' ⊢
        linear_combination (w : ℂ) ^ 2 * I_sq - hw'
    · have hD' : Δ ^ 2 ≤ ‖g‖ ^ 2 := by nlinarith
      refine ⟨_, (slowFlow_real_roots s Δ g hD').1, ?_⟩
      simp only [Complex.ofReal_re]
      have : s < √(‖g‖ ^ 2 - Δ ^ 2) := by
        rw [← Real.sqrt_sq hs]
        exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
      linarith

/-- **The small-signal branch with weak pump: complex roots, unlocked frequency.** For
`|g|² < Δ²` the characteristic roots are exactly `−s ± j w'`, `w' = √(Δ² − |g|²) > 0`; with
`s < 0` both are unstable and non-real, so in the frame of the original system (rotating back at
`ω_p/2`) the growing oscillation has the frequencies `ω_p/2 ± w'`, not locked to the pump. -/
@[tmio T, powerlib_foundation] theorem smallSignal_complex_roots (s Δ : ℝ) {g : ℂ}
    (hg : ‖g‖ ^ 2 < Δ ^ 2) :
    0 < √(Δ ^ 2 - ‖g‖ ^ 2) ∧ ∀ μ : ℂ,
      (Linear.characteristicMatrix (slowFlowMatrix s Δ g) μ).det = 0 ↔
        μ = -(s : ℂ) + (√(Δ ^ 2 - ‖g‖ ^ 2) : ℂ) * I ∨
          μ = -(s : ℂ) - (√(Δ ^ 2 - ‖g‖ ^ 2) : ℂ) * I := by
  set w := √(Δ ^ 2 - ‖g‖ ^ 2)
  have hw : w ^ 2 = Δ ^ 2 - ‖g‖ ^ 2 := Real.sq_sqrt (by linarith)
  refine ⟨Real.sqrt_pos.mpr (by linarith), fun μ => ?_⟩
  rw [slowFlow_root_iff]
  have hw' : ((‖g‖ ^ 2 - Δ ^ 2 : ℝ) : ℂ) = ((w : ℂ) * I) ^ 2 := by
    rw [mul_pow, I_sq]
    have : (w : ℂ) ^ 2 = ((Δ ^ 2 - ‖g‖ ^ 2 : ℝ) : ℂ) := by exact_mod_cast hw
    rw [this]; push_cast; ring
  rw [hw', sq_eq_sq_iff_eq_or_eq_neg]
  constructor <;> rintro (h | h)
  · left; linear_combination h
  · right; linear_combination h
  · left; linear_combination h
  · right; linear_combination h

/-- **The parametric branch: one real unstable root.** For `s ≥ 0` and `s² + Δ² < |g|²` the
characteristic roots are exactly the real numbers `λ± = −s ± √(|g|² − Δ²)`, with `λ₊ > 0 > λ₋`
(a saddle): the unstable slow mode does not rotate, so in the original frame it oscillates at
exactly `ω_p/2`, locked to the pump. The branch needs `|g| > √(s² + Δ²)`; it is empty at
`g = 0`. -/
@[tmio T, powerlib_foundation] theorem parametric_real_roots {s Δ : ℝ} {g : ℂ} (hs : 0 ≤ s)
    (hg : s ^ 2 + Δ ^ 2 < ‖g‖ ^ 2) :
    0 < -s + √(‖g‖ ^ 2 - Δ ^ 2) ∧ -s - √(‖g‖ ^ 2 - Δ ^ 2) < 0 ∧ ∀ μ : ℂ,
      (Linear.characteristicMatrix (slowFlowMatrix s Δ g) μ).det = 0 ↔
        μ = ((-s + √(‖g‖ ^ 2 - Δ ^ 2) : ℝ) : ℂ) ∨ μ = ((-s - √(‖g‖ ^ 2 - Δ ^ 2) : ℝ) : ℂ) := by
  set w := √(‖g‖ ^ 2 - Δ ^ 2)
  have hw : w ^ 2 = ‖g‖ ^ 2 - Δ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hsw : s < w := by
    rw [← Real.sqrt_sq hs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  refine ⟨by linarith, by linarith, fun μ => ?_⟩
  rw [slowFlow_root_iff]
  have hw' : ((‖g‖ ^ 2 - Δ ^ 2 : ℝ) : ℂ) = (w : ℂ) ^ 2 := by rw [← hw]; push_cast; ring
  rw [hw', sq_eq_sq_iff_eq_or_eq_neg]
  push_cast
  constructor <;> rintro (h | h)
  · left; linear_combination h
  · right; linear_combination h
  · left; linear_combination h
  · right; linear_combination h

end Slow

/-! ## The exact Floquet level of the resonant normal form -/

section NF

open scoped Matrix.Norms.Operator

/-- **The trace of the slow-flow exponential.** For any `w` with `w² = |c|² − Δ²`:
`tr e^{T M} = e^{(−σ + w)T} + e^{(−σ − w)T}`, `M = slowFlowMatrix σ Δ c` (closed forms
`LTI.exp_smul_of_sq_eq`, `Kapitza.exp_smul_of_sq_eq_sq`, `Averaging.exp_smul_sqZero_sub_smul_one`
for `|c|² − Δ²` negative, positive, zero: `(M + σI)² = (|c|² − Δ²) I`). -/
@[tmio T, powerlib_foundation] theorem trace_exp_slowFlow (σ Δ : ℝ) (c : ℂ) {w : ℂ}
    (hw : w ^ 2 = ((‖c‖ ^ 2 - Δ ^ 2 : ℝ) : ℂ)) (T : ℝ) :
    (((NormedSpace.exp (T • slowFlowMatrix σ Δ c)).trace : ℝ) : ℂ) =
      Complex.exp ((-(σ : ℂ) + w) * T) + Complex.exp ((-(σ : ℂ) - w) * T) := by
  set M := slowFlowMatrix σ Δ c with hM
  set D := ‖c‖ ^ 2 - Δ ^ 2 with hD
  have hN : (M + σ • 1) * (M + σ • 1) = D • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [hD, Complex.sq_norm, Complex.normSq_apply]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hM, slowFlowMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have htrN : (M + σ • (1 : Matrix (Fin 2) (Fin 2) ℝ)).trace = 0 := by
    simp [hM, slowFlowMatrix, Matrix.trace_fin_two]; ring
  -- the right side depends on `w` only through `w²`
  have hsymm : ∀ w₀ : ℂ, w₀ ^ 2 = (D : ℂ) →
      Complex.exp ((-(σ : ℂ) + w) * T) + Complex.exp ((-(σ : ℂ) - w) * T) =
        Complex.exp ((-(σ : ℂ) + w₀) * T) + Complex.exp ((-(σ : ℂ) - w₀) * T) := by
    intro w₀ hw₀
    have : w ^ 2 = w₀ ^ 2 := by rw [hw, hw₀]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with h | h
    · rw [h]
    · rw [h, show -(σ : ℂ) + -w₀ = -(σ : ℂ) - w₀ by ring,
        show -(σ : ℂ) - -w₀ = -(σ : ℂ) + w₀ by ring, add_comm]
  rcases lt_trichotomy D 0 with hneg | hzero | hpos
  · set v := √(-D) with hv
    have hv0 : v ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    have hvsq : v ^ 2 = -D := Real.sq_sqrt (by linarith)
    have hB : (M + σ • 1) * (M + σ • 1) = -(v ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [hN, hvsq, neg_neg]
    have hvc : (v : ℂ) ^ 2 = ((-D : ℝ) : ℂ) := by exact_mod_cast hvsq
    rw [hsymm ((v : ℂ) * I) (by rw [mul_pow, I_sq, hvc]; push_cast; ring),
      LTI.exp_smul_of_sq_eq hv0 hB T, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      htrN, Matrix.trace_one]
    simp only [Fintype.card_fin, smul_eq_mul, mul_zero, add_zero]
    rw [show (-(σ : ℂ) + (v : ℂ) * I) * T = ((-σ * T : ℝ) : ℂ) + ((v * T : ℝ) : ℂ) * I by
        push_cast; ring,
      show (-(σ : ℂ) - (v : ℂ) * I) * T = ((-σ * T : ℝ) : ℂ) + (-(v * T : ℝ) : ℂ) * I by
        push_cast; ring,
      Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I,
      Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  · have hw0 : w = 0 := by
      rw [hzero] at hw; push_cast at hw; exact pow_eq_zero_iff (two_ne_zero) |>.mp hw
    have hsq : (M + σ • 1) * (M + σ • 1) = 0 := by rw [hN, hzero, zero_smul]
    have hMeq : M = (M + σ • 1) - σ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by abel
    have hE : NormedSpace.exp (T • M) =
        Real.exp (-(σ * T)) • (1 + T • (M + σ • (1 : Matrix (Fin 2) (Fin 2) ℝ))) := by
      calc NormedSpace.exp (T • M)
          = NormedSpace.exp (T • ((M + σ • 1) - σ • (1 : Matrix (Fin 2) (Fin 2) ℝ))) := by
            rw [← hMeq]
        _ = _ := Averaging.exp_smul_sqZero_sub_smul_one hsq T σ
    rw [hw0, hE, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul, htrN, Matrix.trace_one]
    simp only [Fintype.card_fin, smul_eq_mul, mul_zero, add_zero, sub_zero]
    push_cast
    rw [show -(σ : ℂ) * T = -(σ * T) by ring]
    ring
  · set v := √D with hv
    have hv0 : v ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    have hvsq : v ^ 2 = D := Real.sq_sqrt hpos.le
    have hB : (M + σ • 1) * (M + σ • 1) = (v ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [hN, hvsq]
    rw [hsymm (v : ℂ) (by rw [← hvsq]; push_cast; ring),
      Kapitza.exp_smul_of_sq_eq_sq hv0 hB T, Matrix.trace_add, Matrix.trace_smul,
      Matrix.trace_smul, htrN, Matrix.trace_one]
    simp only [Fintype.card_fin, smul_eq_mul, mul_zero, add_zero]
    rw [Real.cosh_eq]
    push_cast
    rw [show (-(σ : ℂ) + v) * T = -σ * T + v * T by ring,
      show (-(σ : ℂ) - v) * T = -σ * T + -(v * T) by ring, Complex.exp_add, Complex.exp_add]
    ring

/-- Over one pump period `T = 2π/ω` the rotation at half the pump frequency contributes
`e^{jωT/2} = −1`: `e^{(l + jω/2)T} = −e^{lT}`. -/
@[tmio T, powerlib_foundation] theorem exp_add_half_pump (l : ℂ) {ω : ℝ} (hω : ω ≠ 0) :
    Complex.exp ((l + ((ω / 2 : ℝ) : ℂ) * I) * ((2 * Real.pi / ω : ℝ) : ℂ)) =
      -Complex.exp (l * ((2 * Real.pi / ω : ℝ) : ℂ)) := by
  have hω0 : (ω : ℂ) ≠ 0 := by exact_mod_cast hω
  have : ((ω / 2 : ℝ) : ℂ) * I * ((2 * Real.pi / ω : ℝ) : ℂ) = (Real.pi : ℂ) * I := by
    push_cast; field_simp
  rw [add_mul, Complex.exp_add, this, Complex.exp_pi_mul_I]
  ring

/-- **The Floquet multipliers of the normal form are the slow-flow exponents shifted by `jω/2`.**
For `ż = (−σ + jΩ) z + c e^{jωt} z̄` (`NormalForm.nfMatrix`, period `T = 2π/ω`) the Floquet
multipliers are exactly `e^{(λ + jω/2)T}` with `λ` a characteristic root of the slow flow
`slowFlowMatrix σ (ω/2 − Ω) c` (from `NormalForm.monodromy_nf`, `Φ(T) = −e^{TM}`, and
`trace_exp_slowFlow`): the Floquet exponents are `λ + jω/2`, growth rate `Re λ` and frequency
`ω/2 + Im λ`. -/
@[tmio T, powerlib_foundation] theorem nf_spectrum (σ Ω : ℝ) {ω : ℝ} (hω : 0 < ω) (c : ℂ)
    (μ : ℂ) :
    μ ∈ spectrum ℂ ((Periodic.monodromy (nfMatrix σ Ω ω c) (2 * Real.pi / ω) 0).map
        (algebraMap ℝ ℂ)) ↔
      ∃ l : ℂ, (Linear.characteristicMatrix (slowFlowMatrix σ (ω / 2 - Ω) c) l).det = 0 ∧
        μ = Complex.exp ((l + ((ω / 2 : ℝ) : ℂ) * I) * ((2 * Real.pi / ω : ℝ) : ℂ)) := by
  set T := 2 * Real.pi / ω with hT
  set Δ := ω / 2 - Ω with hΔ
  have hΦ : Periodic.monodromy (nfMatrix σ Ω ω c) T 0 =
      -NormedSpace.exp (T • slowFlowMatrix σ Δ c) := NormalForm.monodromy_nf σ Ω hω c
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (((‖c‖ ^ 2 - Δ ^ 2 : ℝ) : ℂ)) two_pos
  set e₁ := Complex.exp ((-(σ : ℂ) + w) * T) with he₁
  set e₂ := Complex.exp ((-(σ : ℂ) - w) * T) with he₂
  have htr : (((Periodic.monodromy (nfMatrix σ Ω ω c) T 0).trace : ℝ) : ℂ) = -(e₁ + e₂) := by
    rw [hΦ, Matrix.trace_neg, Complex.ofReal_neg, trace_exp_slowFlow σ Δ c hw T]
  have hdet : (((Periodic.monodromy (nfMatrix σ Ω ω c) T 0).det : ℝ) : ℂ) = e₁ * e₂ := by
    rw [hΦ, Matrix.det_neg, Fintype.card_fin, Periodic.det_exp_smul, trace_slowFlowMatrix,
      he₁, he₂, ← Complex.exp_add,
      show (-(σ : ℂ) + w) * T + (-(σ : ℂ) - w) * T = ((T * (-2 * σ) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp]
    push_cast
    ring
  have hshift : ∀ l : ℂ, Complex.exp ((l + ((ω / 2 : ℝ) : ℂ) * I) * T) =
      -Complex.exp (l * T) := fun l => exp_add_half_pump l hω.ne'
  have hroot : ∀ l : ℂ,
      (Linear.characteristicMatrix (slowFlowMatrix σ Δ c) l).det = 0 ↔
        l = -(σ : ℂ) + w ∨ l = -(σ : ℂ) - w := by
    intro l
    rw [slowFlow_root_iff, ← hw, sq_eq_sq_iff_eq_or_eq_neg]
    constructor <;> rintro (h | h)
    · left; linear_combination h
    · right; linear_combination h
    · left; linear_combination h
    · right; linear_combination h
  rw [Periodic.mem_spectrum_iff_root, htr, hdet]
  constructor
  · intro h
    have hf : (μ + e₁) * (μ + e₂) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hf with h1 | h1
    · exact ⟨-(σ : ℂ) + w, (hroot _).mpr (Or.inl rfl), by
        rw [hshift]; linear_combination h1⟩
    · exact ⟨-(σ : ℂ) - w, (hroot _).mpr (Or.inr rfl), by
        rw [hshift]; linear_combination h1⟩
  · rintro ⟨l, hl, rfl⟩
    rw [hshift]
    rcases (hroot l).mp hl with rfl | rfl
    · linear_combination (-Complex.exp ((-(σ : ℂ) + w) * T) + e₂) * he₁
    · linear_combination (-Complex.exp ((-(σ : ℂ) - w) * T) + e₁) * he₂

/-- **Exact Floquet instability of the normal form, by branch.** The normal form has a Floquet
multiplier outside the unit circle iff exactly one of: `σ < 0` (small-signal branch, for every
pump `c`), or `σ ≥ 0` and `σ² + (ω/2 − Ω)² < |c|²` (parametric branch): at the Floquet level the
2:1 slow flow of the normal form is exact (`nf_spectrum`, `slowFlow_unstable_iff`). -/
@[tmio T, powerlib_foundation] theorem nf_floquetUnstable_iff (σ Ω : ℝ) {ω : ℝ} (hω : 0 < ω)
    (c : ℂ) :
    Periodic.FloquetUnstable (nfMatrix σ Ω ω c) (2 * Real.pi / ω) ↔
      Xor (σ < 0) (0 ≤ σ ∧ σ ^ 2 + (ω / 2 - Ω) ^ 2 < ‖c‖ ^ 2) := by
  rw [← slowFlow_unstable_iff]
  have hT : 0 < 2 * Real.pi / ω := by positivity
  have hre : ∀ l : ℂ, ((l + ((ω / 2 : ℝ) : ℂ) * I) * ((2 * Real.pi / ω : ℝ) : ℂ)).re =
      l.re * (2 * Real.pi / ω) := by
    intro l; simp [Complex.mul_re]
  constructor
  · rintro ⟨μ, hμ, h1⟩
    obtain ⟨l, hl, rfl⟩ := (nf_spectrum σ Ω hω c μ).mp hμ
    rw [Complex.norm_exp, hre, Real.one_lt_exp_iff] at h1
    exact ⟨l, hl, pos_of_mul_pos_left h1 hT.le⟩
  · rintro ⟨l, hl, hpos⟩
    refine ⟨_, (nf_spectrum σ Ω hω c _).mpr ⟨l, hl, rfl⟩, ?_⟩
    rw [Complex.norm_exp, hre, Real.one_lt_exp_iff]
    positivity

/-- **The parametric branch at the Floquet level: a real negative multiplier, locked at `ω/2`.**
For `σ ≥ 0` and `σ² + Δ² < |c|²` (`Δ = ω/2 − Ω`) the real number `−e^{λ₊T}`,
`λ₊ = −σ + √(|c|² − Δ²) > 0`, is a Floquet multiplier of the normal form, it is `< −1`, and it is
the only multiplier outside the unit circle: the growing mode satisfies `x(t + T) = −e^{λ₊T} x(t)`
(period doubling, frequency exactly half the pump frequency). -/
@[tmio T, powerlib_foundation] theorem nf_parametric_locked {σ Ω ω : ℝ} (hω : 0 < ω) {c : ℂ}
    (hσ : 0 ≤ σ) (hc : σ ^ 2 + (ω / 2 - Ω) ^ 2 < ‖c‖ ^ 2) :
    (((-Real.exp ((-σ + √(‖c‖ ^ 2 - (ω / 2 - Ω) ^ 2)) * (2 * Real.pi / ω)) : ℝ) : ℂ) ∈
        spectrum ℂ ((Periodic.monodromy (nfMatrix σ Ω ω c) (2 * Real.pi / ω) 0).map
          (algebraMap ℝ ℂ))) ∧
      -Real.exp ((-σ + √(‖c‖ ^ 2 - (ω / 2 - Ω) ^ 2)) * (2 * Real.pi / ω)) < -1 ∧
      ∀ μ ∈ spectrum ℂ ((Periodic.monodromy (nfMatrix σ Ω ω c) (2 * Real.pi / ω) 0).map
          (algebraMap ℝ ℂ)), 1 < ‖μ‖ →
        μ = ((-Real.exp ((-σ + √(‖c‖ ^ 2 - (ω / 2 - Ω) ^ 2)) * (2 * Real.pi / ω)) : ℝ) : ℂ) := by
  set T := 2 * Real.pi / ω with hTdef
  have hT : 0 < T := by positivity
  obtain ⟨hp, hm, hroots⟩ := parametric_real_roots hσ hc
  set lp := -σ + √(‖c‖ ^ 2 - (ω / 2 - Ω) ^ 2) with hlp
  set lm := -σ - √(‖c‖ ^ 2 - (ω / 2 - Ω) ^ 2) with hlm
  have hval : ∀ l : ℝ, Complex.exp (((l : ℂ) + ((ω / 2 : ℝ) : ℂ) * I) * (T : ℂ)) =
      ((-Real.exp (l * T) : ℝ) : ℂ) := by
    intro l
    rw [exp_add_half_pump _ hω.ne', Complex.ofReal_neg, Complex.ofReal_exp, Complex.ofReal_mul]
  refine ⟨?_, ?_, fun μ hμ h1 => ?_⟩
  · rw [← hval]
    exact (nf_spectrum σ Ω hω c _).mpr ⟨lp, (hroots lp).mpr (Or.inl rfl), rfl⟩
  · have : 1 < Real.exp (lp * T) := Real.one_lt_exp_iff.mpr (by positivity)
    linarith
  · obtain ⟨l, hl, rfl⟩ := (nf_spectrum σ Ω hω c μ).mp hμ
    rcases (hroots l).mp hl with rfl | rfl
    · exact hval lp
    · exfalso
      rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (Real.exp_pos _),
        Real.one_lt_exp_iff] at h1
      nlinarith

/-- **The small-signal branch with weak pump at the Floquet level: unlocked frequencies.** For
`σ < 0` and `|c|² < Δ²` (`Δ = ω/2 − Ω`, `w' = √(Δ² − |c|²) > 0`) the Floquet multipliers of the
normal form are exactly `e^{(−σ + j(ω/2 ± w'))T}`, both of modulus `e^{−σT} > 1`: Floquet
exponents with growth rate `−σ` and frequencies `ω/2 ± w'`, shifted from half the pump frequency
by the residual detuning `w'`. -/
@[tmio T, powerlib_foundation] theorem nf_smallSignal_unlocked {σ Ω ω : ℝ} (hω : 0 < ω)
    {c : ℂ} (hσ : σ < 0) (hc : ‖c‖ ^ 2 < (ω / 2 - Ω) ^ 2) :
    0 < √((ω / 2 - Ω) ^ 2 - ‖c‖ ^ 2) ∧
      (∀ μ : ℂ, μ ∈ spectrum ℂ ((Periodic.monodromy (nfMatrix σ Ω ω c) (2 * Real.pi / ω) 0).map
          (algebraMap ℝ ℂ)) ↔
        μ = Complex.exp ((-(σ : ℂ) + ((ω / 2 + √((ω / 2 - Ω) ^ 2 - ‖c‖ ^ 2) : ℝ) : ℂ) * I) *
          ((2 * Real.pi / ω : ℝ) : ℂ)) ∨
        μ = Complex.exp ((-(σ : ℂ) + ((ω / 2 - √((ω / 2 - Ω) ^ 2 - ‖c‖ ^ 2) : ℝ) : ℂ) * I) *
          ((2 * Real.pi / ω : ℝ) : ℂ))) ∧
      ∀ μ ∈ spectrum ℂ ((Periodic.monodromy (nfMatrix σ Ω ω c) (2 * Real.pi / ω) 0).map
          (algebraMap ℝ ℂ)), ‖μ‖ = Real.exp (-σ * (2 * Real.pi / ω)) ∧ 1 < ‖μ‖ := by
  have hT : 0 < 2 * Real.pi / ω := by positivity
  obtain ⟨hw, hroots⟩ := smallSignal_complex_roots σ (ω / 2 - Ω) hc
  set w := √((ω / 2 - Ω) ^ 2 - ‖c‖ ^ 2) with hwdef
  have hspec : ∀ μ : ℂ, μ ∈ spectrum ℂ ((Periodic.monodromy (nfMatrix σ Ω ω c)
      (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ)) ↔
        μ = Complex.exp ((-(σ : ℂ) + ((ω / 2 + w : ℝ) : ℂ) * I) * ((2 * Real.pi / ω : ℝ) : ℂ)) ∨
        μ = Complex.exp ((-(σ : ℂ) + ((ω / 2 - w : ℝ) : ℂ) * I) *
          ((2 * Real.pi / ω : ℝ) : ℂ)) := by
    intro μ
    rw [nf_spectrum σ Ω hω c μ]
    constructor
    · rintro ⟨l, hl, rfl⟩
      rcases (hroots l).mp hl with rfl | rfl
      · left; congr 2; push_cast; ring
      · right; congr 2; push_cast; ring
    · rintro (rfl | rfl)
      · exact ⟨_, (hroots _).mpr (Or.inl rfl), by congr 2; push_cast; ring⟩
      · exact ⟨_, (hroots _).mpr (Or.inr rfl), by congr 2; push_cast; ring⟩
  refine ⟨hw, hspec, fun μ hμ => ?_⟩
  have hnorm : ‖μ‖ = Real.exp (-σ * (2 * Real.pi / ω)) := by
    rcases (hspec μ).mp hμ with rfl | rfl <;>
    · rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re]
  refine ⟨hnorm, ?_⟩
  rw [hnorm, Real.one_lt_exp_iff]
  nlinarith

end NF

/-! ## Validity of the averaged level for the complete two-state system -/

section Averaging

open TwoToOne (full left right)

/-- **The averaged verdicts transfer to the complete system for small modulation.** For the
two-state system `ẋ = (A₀ + ε Re{A₁ e^{jωt}}) x` with `σ = εs`, `ω/2 − Ω = εd`
(`TwoToOne.full`) and slow flow `M = slowFlowMatrix s d (g/2)`, `g = Element.pump A₁ u r`:
an unstable slow exponent (either branch, `slowFlow_unstable_iff`) gives Floquet instability,
and a Hurwitz slow flow gives Schur-stable monodromy, for all sufficiently small `ε > 0`
(`TwoToOne.averaging_unstable`, `TwoToOne.averaging_stable`). At finite `ε` the non-resonant
terms move the boundary; only the normal form (`nf_spectrum`) is exact. -/
@[tmio T, powerlib_foundation] theorem averaging_branches {s d ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ((∃ μ : ℂ, (Linear.characteristicMatrix
          (slowFlowMatrix s d (Element.pump A left right / 2)) μ).det = 0 ∧ 0 < μ.re) →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable (full s d ω A ε) (2 * Real.pi / ω)) ∧
      (LinearSystems.IsHurwitz (slowFlowMatrix s d (Element.pump A left right / 2)) →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          LTI.SchurStable (Periodic.monodromy (full s d ω A ε) (2 * Real.pi / ω) 0)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hx := (slowFlow_unstable_iff s d _).mp h
    refine TwoToOne.averaging_unstable hω A ?_
    rcases hx with ⟨hs, -⟩ | ⟨⟨-, hg⟩, -⟩
    · exact Or.inl hs
    · exact Or.inr hg
  · rw [Criteria.isHurwitz_fin_two_iff, trace_slowFlowMatrix, det_slowFlowMatrix] at h
    exact TwoToOne.averaging_stable hω A (by linarith [h.1]) (by linarith [h.2])

end Averaging

end powerlib.ParametricResonance.Branches
