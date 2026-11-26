import theorem.SpecialFunctions.PeriodicWaves
import theorem.LTI.Decay
import theorem.Criteria.Hurwitz

/-! # Harmonics of periodic solutions of linear time-invariant systems

The Fourier coefficients of every periodic solution of `ẋ = A x + B u` are fixed, harmonic by
harmonic, by those of the input: `(j m ω₀ I − A) c_m(x) = B c_m(u)`. Hence a linear system creates
no harmonics: a harmonic of a periodic output is present only if the input has it, a sinusoidal
input gives a sinusoidal output on every channel (harmonic content index `0`), and a Hurwitz system
has no nonzero periodic free solution at all.

Scope.
* A real LTI plant `ẋ = A x + B u`, `y = C x + D u` with `A : Matrix (Fin n) (Fin n) ℝ`,
  `B : Matrix (Fin n) (Fin p) ℝ`, `C : Matrix (Fin p) (Fin n) ℝ`, `D : Matrix (Fin p) (Fin p) ℝ`
  (square `C`, `D` so that the transfer matrix is `Linear.transferOf A B C D`), continuous input
  `u : ℝ → Fin p → ℝ`, and a global solution `x : ℝ → Fin n → ℝ` (`HasDerivAt` at every `t`)
  closing over one period, `x(T) = x(0)` (in particular any `T`-periodic solution). The input
  need not be periodic for the coefficient identity.
* Fourier coefficients over `[0, T]`, componentwise: `coeffVec` from
  `SpecialFunctions.PeriodicWaves.coeff` (Mathlib's `fourierCoeffOn`), `ω₀ = 2π/T`.
* Generic linear-systems mathematics; no model family. Nonlinear systems (whose limit cycles carry
  harmonics of their own) and noise are excluded.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §3.1 ("Harmonics &
Non-sinusoid": the steady-state waveform of a forced oscillation is shaped by the forcing input;
the intrinsic damping of natural oscillations), §3.4 (harmonics of a steady-state waveform as an
indicator of forced oscillation) and §3.5, eq. (3-16)–(3-17) (Fourier-series input and the
forced response `c_r (jmω₀I − A)⁻¹ b₁ A_m` of each harmonic).

Results.
* `coeff_add`, `coeff_sum`, `coeffVec_mulVec_add` — linearity of the coefficients of continuous
  signals; for `y = P x + Q u`, `c_m(y) = P c_m(x) + Q c_m(u)`.
* `coeff_deriv` — integration by parts over a period (`fourierCoeffOn_of_hasDerivAt`): if
  `g(T) = g(0)`, then `c_m(ġ) = j m ω₀ c_m(g)`.
* `characteristicMatrix_mulVec_coeffVec` — every solution with `x(T) = x(0)` satisfies
  `(j m ω₀ I − A) c_m(x) = B c_m(u)` for every harmonic `m ∈ ℤ`.
* `coeffVec_eq`, `coeffVec_output` — if `j m ω₀` is not an eigenvalue of `A`:
  `c_m(x) = (j m ω₀ I − A)⁻¹ B c_m(u)` and `c_m(y) = G(j m ω₀) c_m(u)`,
  `G = Linear.transferOf A B C D`.
* `coeffVec_input_ne_zero` — a harmonic present in the output is present in the input.
* `coeffVec_output_of_cosine`, `harmonicContent_output_of_cosine` — for Hurwitz `A`
  (`Criteria.det_characteristicMatrix_ne_zero_of_isHurwitz`) and sinusoidal inputs at `ω₀`
  (`SpecialFunctions.PeriodicWaves.cosineWave`, any amplitudes and phases), `c_m(y) = 0` for
  `|m| ≠ 1` and every output channel has harmonic content index `h = 0`.
* `periodic_free_eq_zero`, `not_isHurwitz_of_periodic` — a Hurwitz matrix admits no nonzero
  periodic solution of `ẋ = A x` (`LTI.linear_decay_of_isHurwitz`): a sustained natural
  oscillation of an LTI system requires a non-Hurwitz `A`.
-/

noncomputable section
namespace powerlib.LTI.HarmonicTransfer
open Complex Matrix MeasureTheory
open powerlib.SpecialFunctions.PeriodicWaves

variable {T : ℝ}

/-- The componentwise Fourier coefficient vector `c_m(x)` of a vector signal over `[0, T]`. -/
def coeffVec (hT : 0 < T) {ι : Type*} (x : ℝ → ι → ℝ) (m : ℤ) : ι → ℂ :=
  fun i => coeff hT (fun t => x t i) m

/-! ## Linearity and integration by parts -/

@[tmio T, powerlib_foundation] theorem coeff_add (hT : 0 < T) {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (m : ℤ) :
    coeff hT (fun t => f t + g t) m = coeff hT f m + coeff hT g m := by
  rw [coeff_eq_integral, coeff_eq_integral, coeff_eq_integral, ← mul_add,
    ← intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  simp only
  push_cast
  ring

@[tmio T, powerlib_foundation] theorem coeff_sum (hT : 0 < T) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) {f : ι → ℝ → ℝ} (hf : ∀ j, Continuous (f j)) (m : ℤ) :
    coeff hT (fun t => ∑ j ∈ s, c j * f j t) m = ∑ j ∈ s, (c j : ℂ) * coeff hT (f j) m := by
  rw [coeff_eq_integral]
  have hpt : ∀ x : ℝ, cexp (kernelExp T m * x) * ((∑ j ∈ s, c j * f j x : ℝ) : ℂ) =
      ∑ j ∈ s, (c j : ℂ) * (cexp (kernelExp T m * x) * (f j x : ℂ)) := by
    intro x
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [intervalIntegral.integral_congr (fun x _ => hpt x),
    intervalIntegral.integral_finsetSum (fun j _ =>
      Continuous.intervalIntegrable (by have := hf j; fun_prop) _ _),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, coeff_eq_integral]
  ring

/-- For continuous `x`, `u` and real matrices `P`, `Q`: `c_m(P x + Q u) = P c_m(x) + Q c_m(u)`. -/
@[tmio T, powerlib_foundation] theorem coeffVec_mulVec_add (hT : 0 < T) {ι : Type*} [Fintype ι]
    {n p : ℕ} (P : Matrix ι (Fin n) ℝ) (Q : Matrix ι (Fin p) ℝ) {x : ℝ → Fin n → ℝ}
    {u : ℝ → Fin p → ℝ} (hx : Continuous x) (hu : Continuous u) (m : ℤ) :
    coeffVec hT (fun t => P *ᵥ x t + Q *ᵥ u t) m =
      Linear.complexify P *ᵥ coeffVec hT x m + Linear.complexify Q *ᵥ coeffVec hT u m := by
  funext i
  have hxj : ∀ j, Continuous fun t => x t j := fun j => (continuous_apply j).comp hx
  have huk : ∀ k, Continuous fun t => u t k := fun k => (continuous_apply k).comp hu
  simp only [coeffVec, Pi.add_apply, Matrix.mulVec, dotProduct, Linear.complexify,
    Matrix.map_apply, Complex.coe_algebraMap]
  rw [coeff_add hT (continuous_finsetSum _ fun j _ => (hxj j).const_mul _)
      (continuous_finsetSum _ fun k _ => (huk k).const_mul _),
    coeff_sum hT _ _ hxj, coeff_sum hT _ _ huk]

/-- Integration by parts over a period: if `g(T) = g(0)` then `c_m(ġ) = j m ω₀ c_m(g)`
(`−κ_m = j m (2π/T)`). -/
@[tmio T, powerlib_foundation] theorem coeff_deriv (hT : 0 < T) {g g' : ℝ → ℝ}
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : Continuous g') (hper : g T = g 0) (m : ℤ) :
    coeff hT g' m = -kernelExp T m * coeff hT g m := by
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  by_cases hm : m = 0
  · subst hm
    rw [coeff_eq_integral]
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hg x)
      (hg'.intervalIntegrable 0 T)
    simp only [kernelExp, Int.cast_zero, mul_zero, zero_div, neg_zero, zero_mul,
      Complex.exp_zero, one_mul]
    rw [intervalIntegral.integral_ofReal, hint, hper, sub_self, Complex.ofReal_zero, mul_zero]
  · have h := fourierCoeffOn_of_hasDerivAt hT hm (f := fun t => (g t : ℂ))
      (f' := fun t => (g' t : ℂ)) (fun x _ => (hg x).ofReal_comp)
      ((Complex.continuous_ofReal.comp hg').intervalIntegrable 0 T)
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    simp only [hper, sub_self, mul_zero, zero_sub, Complex.ofReal_zero, sub_zero] at h
    rw [coeff, coeff, h, kernelExp]
    have := Real.pi_pos.ne'
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast this
    field_simp

/-! ## The harmonic balance of a periodic solution -/

variable {n p : ℕ}

/-- `(j m ω₀ I − A) c_m(x) = B c_m(u)`, `ω₀ = 2π/T`, for every solution of `ẋ = A x + B u` with
`x(T) = x(0)` and every harmonic `m`. -/
@[tmio T, powerlib_foundation] theorem characteristicMatrix_mulVec_coeffVec (hT : 0 < T)
    {A : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin p) ℝ} {x : ℝ → Fin n → ℝ}
    {u : ℝ → Fin p → ℝ} (hu : Continuous u) (hx : ∀ t, HasDerivAt x (A *ᵥ x t + B *ᵥ u t) t)
    (hper : x T = x 0) (m : ℤ) :
    Linear.characteristicMatrix A ((m : ℂ) * (2 * Real.pi / T : ℝ) * I) *ᵥ coeffVec hT x m =
      Linear.complexify B *ᵥ coeffVec hT u m := by
  have hxc : Continuous x := continuous_iff_continuousAt.mpr fun t => (hx t).continuousAt
  have hlin := coeffVec_mulVec_add hT A B hxc hu m
  funext i
  have hgi : ∀ t, HasDerivAt (fun t => x t i) ((A *ᵥ x t + B *ᵥ u t) i) t :=
    fun t => hasDerivAt_pi.mp (hx t) i
  have hcont : Continuous fun t => (A *ᵥ x t + B *ᵥ u t) i :=
    (continuous_apply i).comp ((Continuous.matrix_mulVec continuous_const hxc).add
      (Continuous.matrix_mulVec continuous_const hu))
  have hd := coeff_deriv hT hgi hcont (congrFun hper i) m
  have hli := congrFun hlin i
  simp only [coeffVec] at hli
  rw [hd] at hli
  simp only [Linear.characteristicMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply] at hli ⊢
  have hk : ((m : ℂ) * (2 * Real.pi / T : ℝ) * I) = -kernelExp T m := by
    simp only [kernelExp]; push_cast; ring
  rw [hk]
  simp only [coeffVec] at hli ⊢
  linear_combination hli

/-- If `j m ω₀` is not an eigenvalue of `A`: `c_m(x) = (j m ω₀ I − A)⁻¹ B c_m(u)`. -/
@[tmio T, powerlib_foundation] theorem coeffVec_eq (hT : 0 < T)
    {A : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin p) ℝ} {x : ℝ → Fin n → ℝ}
    {u : ℝ → Fin p → ℝ} (hu : Continuous u) (hx : ∀ t, HasDerivAt x (A *ᵥ x t + B *ᵥ u t) t)
    (hper : x T = x 0) {m : ℤ}
    (hdet : (Linear.characteristicMatrix A ((m : ℂ) * (2 * Real.pi / T : ℝ) * I)).det ≠ 0) :
    coeffVec hT x m =
      (Linear.characteristicMatrix A ((m : ℂ) * (2 * Real.pi / T : ℝ) * I))⁻¹ *ᵥ
        (Linear.complexify B *ᵥ coeffVec hT u m) := by
  rw [← characteristicMatrix_mulVec_coeffVec hT hu hx hper m, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

/-- The `m`-th harmonic of the output `y = C x + D u` is `G(j m ω₀) c_m(u)`. -/
@[tmio T, powerlib_foundation] theorem coeffVec_output (hT : 0 < T)
    {A : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin p) ℝ} (C : Matrix (Fin p) (Fin n) ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ) {x : ℝ → Fin n → ℝ} {u : ℝ → Fin p → ℝ} (hu : Continuous u)
    (hx : ∀ t, HasDerivAt x (A *ᵥ x t + B *ᵥ u t) t) (hper : x T = x 0) {m : ℤ}
    (hdet : (Linear.characteristicMatrix A ((m : ℂ) * (2 * Real.pi / T : ℝ) * I)).det ≠ 0) :
    coeffVec hT (fun t => C *ᵥ x t + D *ᵥ u t) m =
      Linear.transferOf A B C D ((m : ℂ) * (2 * Real.pi / T : ℝ) * I) *ᵥ coeffVec hT u m := by
  have hxc : Continuous x := continuous_iff_continuousAt.mpr fun t => (hx t).continuousAt
  rw [coeffVec_mulVec_add hT C D hxc hu, coeffVec_eq hT hu hx hper hdet, Linear.transferOf,
    Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- A harmonic present in the output of a linear system is present in its input (when `j m ω₀`
is not an eigenvalue of `A`). -/
@[tmio T, powerlib_foundation] theorem coeffVec_input_ne_zero (hT : 0 < T)
    {A : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin p) ℝ} (C : Matrix (Fin p) (Fin n) ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ) {x : ℝ → Fin n → ℝ} {u : ℝ → Fin p → ℝ} (hu : Continuous u)
    (hx : ∀ t, HasDerivAt x (A *ᵥ x t + B *ᵥ u t) t) (hper : x T = x 0) {m : ℤ}
    (hdet : (Linear.characteristicMatrix A ((m : ℂ) * (2 * Real.pi / T : ℝ) * I)).det ≠ 0)
    (hy : coeffVec hT (fun t => C *ᵥ x t + D *ᵥ u t) m ≠ 0) : coeffVec hT u m ≠ 0 := by
  intro h0
  apply hy
  rw [coeffVec_output hT C D hu hx hper hdet, h0, Matrix.mulVec_zero]

/-! ## Sinusoidal inputs give sinusoidal outputs -/

/-- A Hurwitz system driven by sinusoids at `ω₀ = 2π/T` (any amplitudes `V_k`, phases `φ_k`):
every periodic solution has output harmonics `c_m(y) = 0` for `|m| ≠ 1`. -/
@[tmio T, powerlib_foundation] theorem coeffVec_output_of_cosine (hT : 0 < T)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : LinearSystems.IsHurwitz A) {B : Matrix (Fin n) (Fin p) ℝ}
    (C : Matrix (Fin p) (Fin n) ℝ) (D : Matrix (Fin p) (Fin p) ℝ) (V φ : Fin p → ℝ)
    {x : ℝ → Fin n → ℝ}
    (hx : ∀ t, HasDerivAt x (A *ᵥ x t + B *ᵥ (fun k => cosineWave (V k) T (φ k) t)) t)
    (hper : x T = x 0) {m : ℤ} (hm1 : m ≠ 1) (hm2 : m ≠ -1) :
    coeffVec hT (fun t => C *ᵥ x t + D *ᵥ (fun k => cosineWave (V k) T (φ k) t)) m = 0 := by
  have hu : Continuous fun t => fun k => cosineWave (V k) T (φ k) t :=
    continuous_pi fun k => by unfold cosineWave; fun_prop
  have hdet := Criteria.det_characteristicMatrix_ne_zero_of_isHurwitz hA
    (s := (m : ℂ) * (2 * Real.pi / T : ℝ) * I) (by simp)
  rw [coeffVec_output hT C D hu hx hper hdet]
  have h0 : coeffVec hT (fun t => fun k => cosineWave (V k) T (φ k) t) m = 0 := by
    funext k
    simp only [coeffVec, Pi.zero_apply]
    rw [show (fun t => cosineWave (V k) T (φ k) t) = cosineWave (V k) T (φ k) from rfl,
      coeff_cosineWave hT]
    simp only [hm1, hm2, ↓reduceIte, add_zero]
  rw [h0, Matrix.mulVec_zero]

/-- Under sinusoidal inputs at `ω₀`, every output channel of a Hurwitz system has harmonic
content index `h = 0` (`SpecialFunctions.PeriodicWaves.harmonicContent`). -/
@[tmio T, powerlib_foundation] theorem harmonicContent_output_of_cosine (hT : 0 < T)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : LinearSystems.IsHurwitz A) {B : Matrix (Fin n) (Fin p) ℝ}
    (C : Matrix (Fin p) (Fin n) ℝ) (D : Matrix (Fin p) (Fin p) ℝ) (V φ : Fin p → ℝ)
    {x : ℝ → Fin n → ℝ}
    (hx : ∀ t, HasDerivAt x (A *ᵥ x t + B *ᵥ (fun k => cosineWave (V k) T (φ k) t)) t)
    (hper : x T = x 0) (i : Fin p) :
    harmonicContent hT (fun t => (C *ᵥ x t + D *ᵥ (fun k => cosineWave (V k) T (φ k) t)) i) = 0 := by
  have h2 := congrFun (coeffVec_output_of_cosine hT hA C D V φ hx hper (m := 2) (by norm_num)
    (by norm_num)) i
  have h3 := congrFun (coeffVec_output_of_cosine hT hA C D V φ hx hper (m := 3) (by norm_num)
    (by norm_num)) i
  simp only [coeffVec, Pi.zero_apply] at h2 h3
  rw [harmonicContent, amp, amp]
  push_cast
  rw [h2, h3]
  simp

/-! ## No periodic free solution of a Hurwitz system -/

/-- A Hurwitz matrix admits no nonzero periodic solution of `ẋ = A x`. -/
@[tmio T, powerlib_foundation] theorem periodic_free_eq_zero {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : LinearSystems.IsHurwitz A) (hT : 0 < T) {x : ℝ → Fin n → ℝ}
    (hx : ∀ t, HasDerivAt x (A *ᵥ x t) t) (hper : Function.Periodic x T) : x = 0 := by
  obtain ⟨K, hK, r, hr, hb⟩ := linear_decay_of_isHurwitz hA
  have hxk : ∀ (k : ℕ) (t : ℝ), x (t + k * T) = x t := fun k t => by
    have := (hper.nat_mul k) t
    simpa [mul_comm] using this
  -- `x 0 = 0`: compare `x 0 = x (kT)` with the decay bound for a large `k`
  obtain ⟨k, hk⟩ := exists_nat_gt (K / (r * T))
  have hrT : 0 < r * T := mul_pos hr hT
  have hexp : K < Real.exp (r * (k * T)) := by
    have h1 : K < r * T * k := by rwa [div_lt_iff₀' hrT] at hk
    have h2 := Real.add_one_le_exp (r * (k * T))
    nlinarith
  have h0 : x 0 = 0 := by
    have hbk := hb x hx (k * T) (by positivity)
    rw [show (k : ℝ) * T = 0 + k * T by ring, hxk k 0] at hbk
    have hlt : K * Real.exp (-(r * (0 + k * T))) < 1 := by
      rw [zero_add, Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
      exact hexp
    have hn := norm_nonneg (WithLp.toLp 2 (x 0))
    have : ‖WithLp.toLp 2 (x 0)‖ = 0 := by nlinarith
    rw [norm_eq_zero] at this
    simpa using congrArg WithLp.ofLp this
  funext t
  obtain ⟨j, hj⟩ := exists_nat_gt (-t / T)
  have htj : 0 ≤ t + j * T := by
    have := (div_lt_iff₀ hT).mp hj
    linarith
  have hbt := hb x hx (t + j * T) htj
  rw [hxk j t, h0] at hbt
  simp only [WithLp.toLp_zero, norm_zero, mul_zero] at hbt
  simpa using congrArg WithLp.ofLp (norm_le_zero_iff.mp hbt)

/-- A sustained (nonzero periodic) natural oscillation `ẋ = A x` forces `A` to be non-Hurwitz. -/
@[tmio T, powerlib_foundation] theorem not_isHurwitz_of_periodic {A : Matrix (Fin n) (Fin n) ℝ}
    (hT : 0 < T) {x : ℝ → Fin n → ℝ} (hx : ∀ t, HasDerivAt x (A *ᵥ x t) t)
    (hper : Function.Periodic x T) (hne : x ≠ 0) : ¬ LinearSystems.IsHurwitz A :=
  fun hA => hne (periodic_free_eq_zero hA hT hx hper)

end powerlib.LTI.HarmonicTransfer
