import theorem.Signal.Sampling
import theorem.Modal.RealForm

/-! # Anti-aliasing pre-filters: the aliased contribution is bounded by the stop-band gain

An analog pre-filter with frequency response `H` acts on a sinusoidal input component
`Re(X e^{j2πft})` by multiplying its phasor: the steady-state output is `Re(H(f) X e^{j2πft})`,
whose samples at the rate `f_s` are the sampled sinusoid `sampledCos |H(f)X| f (arg(H(f)X)) f_s`
of `theorem/Signal/Sampling.lean`. If the pre-filter gain is at most `η` above `f_s/2`, every
input component above `f_s/2` reaches the sampled sequence only as an alias in `[0, f_s/2]` of
amplitude at most `η |X|`, each of its samples is at most `η |X|`, and a finite sum of such
components contributes at most `η Σ |X_i|` to every sample. A component at `f_s − f₀` produces
exactly the samples of an in-band component at `f₀` (a false in-band oscillation), of amplitude
`|H(f_s − f₀) X| ≤ η |X|`.

Scope.
* The pre-filter is represented by its frequency response `H : ℝ → ℂ` (any linear
  time-invariant filter, in steady state; transients are excluded), the input by finitely many
  sinusoidal components with phasors `X_i` and frequencies `f_i` (Hz), sampled ideally at the
  rate `f_s > 0` from `n = 0` on. The stop-band hypothesis is `|H(f)| ≤ η` for every `f > f_s/2`.
* No quantization, noise, PMU phasor estimation or reporting filter; the M-class requirement of
  IEC/IEEE 60255-118-1 is not encoded (only the mechanism by which a stop-band attenuation bounds
  aliasing).

Source: ENTSO-E/WindEurope Technical Group on Forced Oscillations Report (2 July 2026) §4.1
("The PMU would preferably be an M-class … to avoid aliasing"; sample rate, "several filtering
stages inside the PMU algorithm"); the aliasing identities of `theorem/Signal/Sampling.lean`.

Results.
* `filteredSample`, `filteredSample_eq` — the sample `Re(H X e^{j2πfn/f_s})` of the pre-filtered
  component is `sampledCos |HX| f (arg(HX)) f_s n` (`Modal.re_mul_exp`).
* `norm_mul_le_of_stopband` — above `f_s/2` the output phasor has `|H(f) X| ≤ η |X|`.
* `aliased_component` — every component above `f_s/2` appears in the samples as an alias at
  some `f₀ ∈ [0, f_s/2]` with the same or conjugate phase and amplitude `|H(f)X| ≤ η |X|`
  (`Signal.exists_alias`).
* `abs_filteredSample_le` — each of its samples is at most `η |X|` (`Signal.abs_sampledCos_le`).
* `abs_sum_filteredSample_le` — a finite sum of input components above `f_s/2` contributes at
  most `η Σ_i |X_i|` to every sample, whatever the in-band content.
* `false_inband_oscillation` — the component at `f_s − f₀` gives exactly the samples of the
  in-band sinusoid at `f₀` of amplitude `|H(f_s − f₀)X|` (`Signal.sampledCos_fs_sub`), so for
  `0 < f₀ < f_s/2` it cannot be told apart from a genuine oscillation at `f₀`
  (`Signal.sampledCos_eq_iff`), and its amplitude is at most `η|X|`.

Family and connection conclusions.
* None: this module defines no family; every result is an identity or inequality of sampled
  sinusoids and complex phasors.
-/

noncomputable section
namespace powerlib.Signal.AntiAliasing
open Complex Finset Set
open powerlib.Signal (sampledCos)

/-- The sample `n` (at the rate `f_s`) of the steady-state output `Re(H X e^{j2πft})` of a
pre-filter with gain `H` at the frequency `f` of the input component `Re(X e^{j2πft})`. -/
def filteredSample (H X : ℂ) (f fs : ℝ) (n : ℕ) : ℝ :=
  (H * X * cexp ((2 * Real.pi * f / fs : ℝ) * I * (n : ℝ))).re

/-- The pre-filtered component sampled is the sampled sinusoid of amplitude `|HX|` and phase
`arg(HX)`. -/
@[tmio T, powerlib_foundation] theorem filteredSample_eq (H X : ℂ) (f : ℝ) {fs : ℝ}
    (hfs : fs ≠ 0) (n : ℕ) :
    filteredSample H X f fs n = sampledCos ‖H * X‖ f (Complex.arg (H * X)) fs n := by
  rw [filteredSample, Modal.re_mul_exp, sampledCos]
  have hre : ((2 * Real.pi * f / fs : ℝ) * I : ℂ).re = 0 := by simp
  have him : ((2 * Real.pi * f / fs : ℝ) * I : ℂ).im = 2 * Real.pi * f / fs := by simp
  rw [hre, him, zero_mul, Real.exp_zero, mul_one]
  congr 2
  field_simp

/-- Above `f_s/2` the output phasor is bounded by the stop-band gain: `|H(f) X| ≤ η |X|`. -/
@[tmio T, powerlib_foundation] theorem norm_mul_le_of_stopband {H : ℝ → ℂ} {fs η : ℝ}
    (hH : ∀ f, fs / 2 < f → ‖H f‖ ≤ η) {f : ℝ} (hf : fs / 2 < f) (X : ℂ) :
    ‖H f * X‖ ≤ η * ‖X‖ := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hH f hf) (norm_nonneg X)

/-- **Aliased contribution.** An input component above `f_s/2` passed through a pre-filter of
stop-band gain `≤ η` appears in the samples as a sinusoid at an alias `f₀ ∈ [0, f_s/2]`, with
the same or the conjugate phase, of amplitude `|H(f) X| ≤ η |X|`. -/
@[tmio T, powerlib_foundation] theorem aliased_component {H : ℝ → ℂ} {fs η : ℝ} (hfs : 0 < fs)
    (hH : ∀ f, fs / 2 < f → ‖H f‖ ≤ η) {f : ℝ} (hf : fs / 2 < f) (X : ℂ) :
    ∃ f₀ ∈ Icc 0 (fs / 2), ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      (fun n => filteredSample (H f) X f fs n) =
        sampledCos ‖H f * X‖ f₀ (s * Complex.arg (H f * X)) fs ∧
      ‖H f * X‖ ≤ η * ‖X‖ := by
  obtain ⟨f₀, hf₀, s, hs, he⟩ := exists_alias hfs ‖H f * X‖ f (Complex.arg (H f * X))
  refine ⟨f₀, hf₀, s, hs, ?_, norm_mul_le_of_stopband hH hf X⟩
  funext n
  rw [filteredSample_eq _ _ _ hfs.ne', he]

/-- Every sample of a pre-filtered component above `f_s/2` is at most `η |X|`. -/
@[tmio T, powerlib_foundation] theorem abs_filteredSample_le {H : ℝ → ℂ} {fs η : ℝ}
    (hfs : fs ≠ 0) (hH : ∀ f, fs / 2 < f → ‖H f‖ ≤ η) {f : ℝ} (hf : fs / 2 < f) (X : ℂ)
    (n : ℕ) : |filteredSample (H f) X f fs n| ≤ η * ‖X‖ := by
  rw [filteredSample_eq _ _ _ hfs]
  refine (abs_sampledCos_le _ _ _ _ _).trans ?_
  rw [abs_of_nonneg (norm_nonneg _)]
  exact norm_mul_le_of_stopband hH hf X

/-- **Several out-of-band components.** Input components `(X_i, f_i)`, `i ∈ S`, all above
`f_s/2`, contribute at most `η Σ_i |X_i|` to every sample. -/
@[tmio T, powerlib_foundation] theorem abs_sum_filteredSample_le {ι : Type*} (S : Finset ι)
    {H : ℝ → ℂ} {fs η : ℝ} (hfs : fs ≠ 0) (hH : ∀ f, fs / 2 < f → ‖H f‖ ≤ η) {X : ι → ℂ}
    {f : ι → ℝ} (hf : ∀ i ∈ S, fs / 2 < f i) (n : ℕ) :
    |∑ i ∈ S, filteredSample (H (f i)) (X i) (f i) fs n| ≤ η * ∑ i ∈ S, ‖X i‖ := by
  rw [mul_sum]
  exact (abs_sum_le_sum_abs _ _).trans
    (sum_le_sum fun i hi => abs_filteredSample_le hfs hH (hf i hi) (X i) n)

/-- **False in-band oscillation.** The pre-filtered component at `f_s − f₀` has exactly the
samples of the in-band sinusoid at `f₀` with amplitude `|H(f_s − f₀)X|` and the conjugate phase;
for `0 < f₀ < f_s/2` no in-band sinusoid with other parameters has these samples, and the
amplitude is at most `η|X|`. -/
@[tmio T, powerlib_foundation] theorem false_inband_oscillation {H : ℝ → ℂ} {fs η f₀ : ℝ}
    (hfs : 0 < fs) (hH : ∀ f, fs / 2 < f → ‖H f‖ ≤ η) (hf₀ : f₀ ∈ Ioo 0 (fs / 2)) (X : ℂ)
    (hX : H (fs - f₀) * X ≠ 0) :
    (fun n => filteredSample (H (fs - f₀)) X (fs - f₀) fs n) =
        sampledCos ‖H (fs - f₀) * X‖ f₀ (-Complex.arg (H (fs - f₀) * X)) fs ∧
      (∀ A f φ, f ∈ Ioo 0 (fs / 2) →
        ((∀ n, filteredSample (H (fs - f₀)) X (fs - f₀) fs n = sampledCos A f φ fs n) ↔
          f = f₀ ∧ A * Real.cos φ = ‖H (fs - f₀) * X‖ * Real.cos (Complex.arg (H (fs - f₀) * X)) ∧
            A * Real.sin φ =
              -(‖H (fs - f₀) * X‖ * Real.sin (Complex.arg (H (fs - f₀) * X))))) ∧
      ‖H (fs - f₀) * X‖ ≤ η * ‖X‖ := by
  have he : (fun n => filteredSample (H (fs - f₀)) X (fs - f₀) fs n) =
      sampledCos ‖H (fs - f₀) * X‖ f₀ (-Complex.arg (H (fs - f₀) * X)) fs := by
    funext n
    rw [filteredSample_eq _ _ _ hfs.ne', sampledCos_fs_sub hfs.ne']
  refine ⟨he, fun A f φ hf => ?_, norm_mul_le_of_stopband hH (by linarith [hf₀.2]) X⟩
  have hA : ‖H (fs - f₀) * X‖ ≠ 0 := norm_ne_zero_iff.mpr hX
  have key := sampledCos_eq_iff hfs (A₂ := A) (f₂ := f) (φ₂ := φ) hf₀ hf hA
    (φ₁ := -Complex.arg (H (fs - f₀) * X))
  rw [Real.cos_neg, Real.sin_neg] at key
  have hn : ∀ n, filteredSample (H (fs - f₀)) X (fs - f₀) fs n =
      sampledCos ‖H (fs - f₀) * X‖ f₀ (-Complex.arg (H (fs - f₀) * X)) fs n := fun n =>
    congrFun he n
  simp only [hn]
  rw [key]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1.symm, h2.symm, by linarith⟩

end powerlib.Signal.AntiAliasing
