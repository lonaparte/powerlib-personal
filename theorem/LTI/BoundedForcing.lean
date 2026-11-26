import theorem.ParametricResonance.ForcedResponse
import theorem.Modal.Spectral
import theorem.Averaging.StateSpaceAveraging
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.MeasureTheory.Integral.ExpDecay

/-! # Bounded forcing of a Hurwitz LTI system: steady state, superposition and decomposition

For a Hurwitz state matrix and a bounded continuous input, the convolution
`x_p(t) = ∫₀^∞ e^{τA} f(t − τ) dτ` is the unique bounded solution of `ẋ = A x + f` on the whole
time axis; it attracts every solution exponentially, it is periodic for a periodic input, it is
the forced orbit `Re(χ e^{jωt})` for a sinusoidal input, and it is the superposition of the forced
orbits of the harmonics of an absolutely summable Fourier series. Every solution splits into the
transient, ambient and forced convolution terms of the report, with the modal kernel.

Scope.
* Real LTI system `ẋ = A x + f(t)` on `ℝⁿ = EuclideanSpace ℝ (Fin n)` (Euclidean norm), constant
  real `A` acting as `Linear.op A`, operator exponential `e^{τA} = exp(τ • Linear.op A)`,
  continuous time, global solutions: `∀ t, HasDerivAt x (Linear.op A (x t) + f t) t`.
* Inputs are deterministic: continuous functions `f : ℝ → ℝⁿ` bounded on `ℝ` (for the steady
  state), or continuous on `ℝ` (for the decomposition (2-14)). The report's ambient input
  `e_k(t)` enters (2-14) through a convolution `⊛ e_k(t)`; here it is a continuous sample path.
  White-noise (Itô) inputs, whose sample paths are not functions of this kind, are outside this
  module.
* Sinusoidal inputs are `forcing b ω t = Re(b e^{jωt})` with complex phasor `b`, and their forced
  orbits `forcedOrbit A b ω` with `χ = (jωI − A)⁻¹ b`, as in
  `theorem/ParametricResonance/ForcedResponse.lean`. Phasors are measured in the sup norm of
  `Fin n → ℂ`.
* The modal kernel statements assume a `ModalBasis (Linear.complexify A)` (diagonalisable state
  matrix).
* No model family; foundation results.

Source: IEEE PES TR-110 "Forced Oscillations in Power Systems" (2023) §2.1.2, eqs. (2-12)–(2-14)
(the forced system `ẋ = Ax + Σ_k b_{e,k} e_k + b_f f`, the Fourier series
`f(t) = Σ_m A_m e^{jmω₀t}` of a periodic input, and the decomposition of the response into
transient, ambient and forced components with modal convolution kernels), and §2.2 (superposition
of the sinusoidal responses of the harmonics; restriction to the steady state).

Results.
* `norm_exp_le_of_isHurwitz` — `‖e^{τA}‖ ≤ K e^{−rτ}` for `τ ≥ 0`. Operator exponential:
  `exp_smul_add` (the semigroup law, read from the generic `Averaging.exp_add_smul`),
  `exp_zero_smul`, `exp_smul_mul_neg` (`e^{sA}e^{−sA} = 1`), `exp_smul_apply_comm`
  (`e^{sA}A = Ae^{sA}`), `hasDerivAt_exp_apply`, `continuous_exp_smul`;
  `setIntegral_Iic_zero_comp_add` (translation of a half-line integral).
* `boundedResponse` — `x_p(t) = ∫₀^∞ e^{τA} f(t − τ) dτ`; `integrableOn_boundedResponse`
  (the integral converges absolutely), `boundedResponse_eq` (`x_p(t) = e^{tA} ∫_{−∞}^t e^{−sA}
  f(s) ds`), `hasDerivAt_boundedResponse` (it solves `ẋ = A x + f`), `norm_boundedResponse_le`
  (`‖x_p(t)‖ ≤ (K/r) sup‖f‖`).
* `eq_boundedResponse_of_bounded` — it is the only solution bounded on `ℝ`;
  `norm_sub_boundedResponse_le` — every solution converges to it exponentially;
  `boundedResponse_periodic` — a `T`-periodic input gives a `T`-periodic steady state.
* `boundedResponse_forcing` — for `f = Re(b e^{jωt})`, `x_p = Re(χ e^{jωt})` (`forcedOrbit`);
  `norm_re_phasor_le`, `continuous_re_phasor` — `‖Re(c e^{jωt})‖ ≤ √n ‖c‖` and continuity;
  `norm_forcedOrbit_le` — `‖Re(χ e^{jωt})‖ ≤ (K/r)√n ‖b‖` uniformly in `ω`.
* `boundedResponse_tsum` — for `f = Σ_m Re(b_m e^{jω_m t})` with `Σ_m ‖b_m‖ < ∞` (in particular
  the Fourier series (2-13) of a periodic input with absolutely summable coefficients,
  `ω_m = mω₀`), `x_p = Σ_m Re(χ_m e^{jω_m t})`, `χ_m = (jω_mI − A)⁻¹ b_m`;
  `boundedResponse_sum` — the same for finitely many sinusoids (superposition).
* `variation_of_constants`, `three_components` — eq. (2-14): every solution of
  `ẋ = A x + B_e e(t) + b_f f(t)` is `e^{tA}x(0) + ∫₀ᵗ e^{(t−s)A}B_e e(s) ds +
  ∫₀ᵗ e^{(t−s)A} b_f f(s) ds` (transient + ambient + forced); `modal_kernel` — the kernel is
  modal, `e^{tA}x₀ = Σ_i e^{λ_i t}(ψ_iᵀx₀) v_i`, and `modal_kernel_residue` —
  `C e^{tA} B u = Σ_i e^{λ_i t} R^{(i)} u` with the modal residues `R^{(i)} = (C v_i)(ψ_iᵀB)`.
-/

noncomputable section
namespace powerlib.LTI
open Matrix Filter Topology Set MeasureTheory NormedSpace LinearSystems
open powerlib.ParametricResonance

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## The operator exponential -/

@[tmio T, powerlib_foundation] theorem exp_zero_smul (M : ℝⁿ →L[ℝ] ℝⁿ) : exp ((0 : ℝ) • M) = 1 := by
  rw [show (0 : ℝ) • M = 0 from zero_smul ℝ M, exp_zero]

/-- The semigroup law `e^{(s+u)A} = e^{sA} e^{uA}` on `ℝⁿ →L[ℝ] ℝⁿ`, read from the generic
`Averaging.exp_add_smul` (stated here with the operator smul so that it can be rewritten). -/
@[tmio T, powerlib_foundation] theorem exp_smul_add (M : ℝⁿ →L[ℝ] ℝⁿ) (s u : ℝ) :
    exp ((s + u) • M) = exp (s • M) * exp (u • M) :=
  Averaging.exp_add_smul M s u

@[tmio T, powerlib_foundation] theorem exp_smul_mul_neg (M : ℝⁿ →L[ℝ] ℝⁿ) (s : ℝ) :
    exp (s • M) * exp ((-s) • M) = 1 := by
  rw [← exp_smul_add, add_neg_cancel, exp_zero_smul]

/-- `e^{sA}` commutes with `A`. -/
@[tmio T, powerlib_foundation] theorem exp_smul_apply_comm (M : ℝⁿ →L[ℝ] ℝⁿ) (s : ℝ) (x : ℝⁿ) :
    exp (s • M) (M x) = M (exp (s • M) x) := by
  have hc : Commute (s • M) M := by
    refine ContinuousLinearMap.ext fun y => ?_
    change (s • M) (M y) = M ((s • M) y)
    simp only [FunLike.coe_smul, Pi.smul_apply, map_smul]
  change (exp (s • M) * M) x = (M * exp (s • M)) x
  rw [hc.exp_left.eq]

@[tmio T, powerlib_foundation] theorem hasDerivAt_exp_apply (A : Matrix (Fin n) (Fin n) ℝ) (x : ℝⁿ)
    (t : ℝ) :
    HasDerivAt (fun s => exp (s • Linear.op A) x) (Linear.op A (exp (t • Linear.op A) x)) t := by
  have h := (hasDerivAt_exp_smul_const' (Linear.op A) t).clm_apply (hasDerivAt_const t x)
  simpa using h

@[tmio T, powerlib_foundation] theorem continuous_exp_smul (A : Matrix (Fin n) (Fin n) ℝ) :
    Continuous fun s : ℝ => exp (s • Linear.op A) :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_exp_smul_const' (Linear.op A) t).continuousAt

/-- Hurwitz: `‖e^{τA}‖ ≤ K e^{−rτ}` for `τ ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem norm_exp_le_of_isHurwitz {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsHurwitz A) :
    ∃ K > 0, ∃ rate > 0, ∀ τ, 0 ≤ τ → ‖exp (τ • Linear.op A)‖ ≤ K * Real.exp (-(rate * τ)) := by
  obtain ⟨K, hK, r, hr, hb⟩ := exists_global_bound_of_isHurwitz hA
  refine ⟨K, hK, r, hr, fun τ hτ => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  have h := hb (fun s => exp (s • Linear.op A) x) (hasDerivAt_exp_apply A x) τ hτ
  rwa [exp_zero_smul, one_apply_eq_self] at h

/-! ## The bounded steady state -/

/-- The convolution steady state `x_p(t) = ∫₀^∞ e^{τA} f(t − τ) dτ`. -/
def boundedResponse (A : Matrix (Fin n) (Fin n) ℝ) (f : ℝ → ℝⁿ) (t : ℝ) : ℝⁿ :=
  ∫ τ in Ioi (0 : ℝ), exp (τ • Linear.op A) (f (t - τ))

variable {A : Matrix (Fin n) (Fin n) ℝ} {f : ℝ → EuclideanSpace ℝ (Fin n)}

/-- The convolution integral converges absolutely. -/
@[tmio T, powerlib_foundation] theorem integrableOn_boundedResponse (hA : IsHurwitz A)
    (hf : Continuous f) {B : ℝ} (hB : ∀ t, ‖f t‖ ≤ B) (t : ℝ) :
    IntegrableOn (fun τ => exp (τ • Linear.op A) (f (t - τ))) (Ioi 0) := by
  obtain ⟨K, hK, r, hr, hexp⟩ := norm_exp_le_of_isHurwitz hA
  have hcont : Continuous fun τ => exp (τ • Linear.op A) (f (t - τ)) :=
    (continuous_exp_smul A).clm_apply (hf.comp (continuous_const.sub continuous_id))
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hr).const_mul (K * B))
    hcont.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun τ hτ => ?_)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  calc ‖exp (τ • Linear.op A) (f (t - τ))‖ ≤ ‖exp (τ • Linear.op A)‖ * ‖f (t - τ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ K * Real.exp (-(r * τ)) * B :=
        mul_le_mul (hexp τ (le_of_lt hτ)) (hB _) (norm_nonneg _) (by positivity)
    _ = K * B * Real.exp (-r * τ) := by ring_nf

/-- `‖x_p(t)‖ ≤ (K/r) B` for every input bounded by `B`. -/
@[tmio T, powerlib_foundation] theorem norm_boundedResponse_le (hA : IsHurwitz A) :
    ∃ K > 0, ∃ rate > 0, ∀ f : ℝ → ℝⁿ, Continuous f → ∀ B, (∀ t, ‖f t‖ ≤ B) → ∀ t,
      ‖boundedResponse A f t‖ ≤ K / rate * B := by
  obtain ⟨K, hK, r, hr, hexp⟩ := norm_exp_le_of_isHurwitz hA
  refine ⟨K, hK, r, hr, fun f hf B hB t => ?_⟩
  have hint : IntegrableOn (fun τ : ℝ => K * B * Real.exp (-r * τ)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hr).const_mul (K * B)
  have hle := norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun τ (hτ : 0 < τ) => by
      calc ‖exp (τ • Linear.op A) (f (t - τ))‖ ≤ ‖exp (τ • Linear.op A)‖ * ‖f (t - τ)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ K * Real.exp (-(r * τ)) * B :=
            mul_le_mul (hexp τ hτ.le) (hB _) (norm_nonneg _) (by positivity)
        _ = K * B * Real.exp (-r * τ) := by ring_nf))
  have hval : ∫ τ in Ioi (0 : ℝ), K * B * Real.exp (-r * τ) = K / r * B := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
    field_simp
    simp
  rw [boundedResponse]
  linarith

/-- Translation of an integral over a half-line. -/
@[tmio T, powerlib_foundation] theorem setIntegral_Iic_zero_comp_add {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (G : ℝ → E) (t : ℝ) :
    ∫ x in Iic (0 : ℝ), G (t + x) = ∫ s in Iic t, G s := by
  rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic,
    ← integral_add_left_eq_self t (μ := volume) (f := (Iic t).indicator G)]
  congr 1
  funext x
  simp only [indicator, mem_Iic]
  by_cases hx : x ≤ 0
  · simp [hx, show t + x ≤ t by linarith]
  · simp [hx, show ¬ t + x ≤ t by intro h; exact hx (by linarith)]

/-- `x_p(t) = e^{tA} ∫_{−∞}^t e^{−sA} f(s) ds` (the integrand is integrable on `(−∞, t]`). -/
@[tmio T, powerlib_foundation] theorem boundedResponse_eq (hA : IsHurwitz A) (hf : Continuous f)
    {B : ℝ} (hB : ∀ t, ‖f t‖ ≤ B) (t : ℝ) :
    IntegrableOn (fun s => exp ((-s) • Linear.op A) (f s)) (Iic t) ∧
      boundedResponse A f t =
        exp (t • Linear.op A) (∫ s in Iic t, exp ((-s) • Linear.op A) (f s)) := by
  obtain ⟨K, hK, r, hr, hexp⟩ := norm_exp_le_of_isHurwitz hA
  set M := Linear.op A
  have hcont : Continuous fun s => exp ((-s) • M) (f s) :=
    ((continuous_exp_smul A).comp continuous_neg).clm_apply hf
  have hInt : IntegrableOn (fun s => exp ((-s) • M) (f s)) (Iic t) := by
    have hdom : IntegrableOn (fun s : ℝ => ‖exp ((-t) • M)‖ * K * B * Real.exp (-(r * t)) *
        Real.exp (r * s)) (Iic t) := (integrableOn_exp_mul_Iic hr t).const_mul _
    refine Integrable.mono' hdom hcont.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun s hs => ?_)
    have hsplit : exp ((-s) • M) = exp ((-t) • M) * exp ((t - s) • M) := by
      rw [← exp_smul_add]; congr 2; ring
    rw [hsplit, mul_apply_eq_comp]
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    calc ‖exp ((-t) • M) (exp ((t - s) • M) (f s))‖
        ≤ ‖exp ((-t) • M)‖ * (‖exp ((t - s) • M)‖ * ‖f s‖) :=
          (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
      _ ≤ ‖exp ((-t) • M)‖ * (K * Real.exp (-(r * (t - s))) * B) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hexp _ (by linarith [mem_Iic.mp hs])) (hB s)
            (norm_nonneg _) (by positivity)) (norm_nonneg _)
      _ = ‖exp ((-t) • M)‖ * K * B * Real.exp (-(r * t)) * Real.exp (r * s) := by
          rw [show -(r * (t - s)) = -(r * t) + r * s by ring, Real.exp_add]; ring
  refine ⟨hInt, ?_⟩
  set G : ℝ → ℝⁿ := fun s => exp ((t - s) • M) (f s)
  have h1 : boundedResponse A f t = ∫ τ in Ioi (0 : ℝ), G (t + -τ) := by
    rw [boundedResponse]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
    show exp (τ • M) (f (t - τ)) = exp ((t - (t + -τ)) • M) (f (t + -τ))
    rw [show t - (t + -τ) = τ by ring, show t + -τ = t - τ by ring]
  have h2 := integral_comp_neg_Ioi 0 (fun x => G (t + x))
  simp only [neg_zero] at h2
  rw [h1, h2, setIntegral_Iic_zero_comp_add G t]
  have h2 : ∀ s, G s = exp (t • M) (exp ((-s) • M) (f s)) := by
    intro s
    simp only [G]
    rw [← mul_apply_eq_comp, ← exp_smul_add, sub_eq_add_neg]
  simp_rw [h2]
  exact ContinuousLinearMap.integral_comp_comm _ hInt

/-- The steady state solves `ẋ = A x + f` on the whole time axis. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_boundedResponse (hA : IsHurwitz A)
    (hf : Continuous f) {B : ℝ} (hB : ∀ t, ‖f t‖ ≤ B) (t : ℝ) :
    HasDerivAt (boundedResponse A f) (Linear.op A (boundedResponse A f t) + f t) t := by
  set M := Linear.op A
  set φ : ℝ → ℝⁿ := fun s => exp ((-s) • M) (f s)
  have hφc : Continuous φ := ((continuous_exp_smul A).comp continuous_neg).clm_apply hf
  set H : ℝ → ℝⁿ := fun s => ∫ u in Iic s, φ u
  have hrep : boundedResponse A f = fun s => exp (s • M) (H s) := by
    funext s; exact (boundedResponse_eq hA hf hB s).2
  have hH : ∀ s, H s = H t + ∫ u in t..s, φ u := by
    intro s
    show (∫ u in Iic s, φ u) = (∫ u in Iic t, φ u) + ∫ u in t..s, φ u
    rw [← intervalIntegral.integral_Iic_sub_Iic (boundedResponse_eq hA hf hB t).1
      (boundedResponse_eq hA hf hB s).1]
    exact (add_sub_cancel _ _).symm
  have hHd : HasDerivAt H (φ t) t := by
    have h := ((hφc.integral_hasStrictDerivAt t t).hasDerivAt).const_add (H t)
    exact h.congr_of_eventuallyEq (Eventually.of_forall hH)
  have hprod := (hasDerivAt_exp_smul_const' M t).clm_apply hHd
  have hφt : exp (t • M) (φ t) = f t := by
    simp only [φ]
    rw [← mul_apply_eq_comp, exp_smul_mul_neg, one_apply_eq_self]
  have hxt : boundedResponse A f t = exp (t • M) (H t) := congrFun hrep t
  have hderiv : HasDerivAt (fun s => exp (s • M) (H s)) (M (boundedResponse A f t) + f t) t := by
    refine hprod.congr_deriv ?_
    rw [hφt, mul_apply_eq_comp, hxt]
  have hEq : boundedResponse A f =ᶠ[𝓝 t] fun s => exp (s • M) (H s) :=
    Eventually.of_forall fun s => congrFun hrep s
  exact hderiv.congr_of_eventuallyEq hEq

/-- Every solution converges exponentially to the steady state:
`‖x(t) − x_p(t)‖ ≤ K e^{−rt} ‖x(0) − x_p(0)‖` for `t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem norm_sub_boundedResponse_le (hA : IsHurwitz A) :
    ∃ K > 0, ∃ rate > 0, ∀ f : ℝ → ℝⁿ, Continuous f → ∀ B, (∀ t, ‖f t‖ ≤ B) →
      ∀ x : ℝ → ℝⁿ, (∀ t, HasDerivAt x (Linear.op A (x t) + f t) t) → ∀ t, 0 ≤ t →
        ‖x t - boundedResponse A f t‖ ≤
          K * Real.exp (-(rate * t)) * ‖x 0 - boundedResponse A f 0‖ := by
  obtain ⟨K, hK, r, hr, hb⟩ := exists_global_bound_of_isHurwitz hA
  refine ⟨K, hK, r, hr, fun f hf B hB x hx t ht =>
    hb (fun s => x s - boundedResponse A f s) (fun s => ?_) t ht⟩
  refine ((hx s).sub (hasDerivAt_boundedResponse hA hf hB s)).congr_deriv ?_
  simp only [map_sub]
  abel

/-- The steady state is the only solution bounded on the whole time axis. -/
@[tmio T, powerlib_foundation] theorem eq_boundedResponse_of_bounded (hA : IsHurwitz A)
    (hf : Continuous f) {B : ℝ} (hB : ∀ t, ‖f t‖ ≤ B) {y : ℝ → ℝⁿ}
    (hy : ∀ t, HasDerivAt y (Linear.op A (y t) + f t) t) {C : ℝ} (hC : ∀ t, ‖y t‖ ≤ C) :
    y = boundedResponse A f := by
  obtain ⟨K, hK, r, hr, hb⟩ := exists_global_bound_of_isHurwitz hA
  obtain ⟨K', hK', r', hr', hxp⟩ := norm_boundedResponse_le hA
  set D := C + K' / r' * B
  have hd : ∀ t, HasDerivAt (fun s => y s - boundedResponse A f s)
      (Linear.op A (y t - boundedResponse A f t)) t := by
    intro t
    refine ((hy t).sub (hasDerivAt_boundedResponse hA hf hB t)).congr_deriv ?_
    simp only [map_sub]
    abel
  have hdD : ∀ s, ‖y s - boundedResponse A f s‖ ≤ D :=
    fun s => (norm_sub_le _ _).trans (add_le_add (hC s) (hxp f hf B hB s))
  -- from any earlier time `t − L` the deviation has decayed by `K e^{−rL}`
  have hdec : ∀ t L, 0 ≤ L → ‖y t - boundedResponse A f t‖ ≤ K * Real.exp (-(r * L)) * D := by
    intro t L hL
    have hshift : ∀ u, HasDerivAt (fun u => y (u + (t - L)) - boundedResponse A f (u + (t - L)))
        (Linear.op A (y (u + (t - L)) - boundedResponse A f (u + (t - L)))) u := by
      intro u
      have h := (hd (u + (t - L))).comp_add_const u (t - L)
      exact h
    have h := hb _ hshift L hL
    simp only [zero_add, show L + (t - L) = t by ring] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hdD _) (by positivity))
  funext t
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  have hlim : Tendsto (fun L : ℝ => K * Real.exp (-(r * L)) * D) atTop (𝓝 0) := by
    have h1 : Tendsto (fun L : ℝ => r * L) atTop atTop := tendsto_id.const_mul_atTop hr
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul K
    simpa using h2.mul_const D
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop 0] with L hL
  exact hdec t L hL

/-- A `T`-periodic input gives a `T`-periodic steady state. -/
@[tmio T, powerlib_foundation] theorem boundedResponse_periodic {T : ℝ} (hper : ∀ t, f (t + T) = f t)
    (t : ℝ) : boundedResponse A f (t + T) = boundedResponse A f t := by
  simp only [boundedResponse]
  congr 1
  funext τ
  rw [show t + T - τ = t - τ + T by ring, hper]

/-! ## Sinusoidal inputs and superposition -/

/-- `‖Re(c e^{jωt})‖ ≤ √n ‖c‖` (Euclidean norm of the real vector, sup norm of the phasor). -/
@[tmio T, powerlib_foundation] theorem norm_re_phasor_le (c : Fin n → ℂ) (ω t : ℝ) :
    ‖(WithLp.toLp 2 fun i => (c i * Complex.exp ((ω : ℂ) * t * Complex.I)).re : ℝⁿ)‖ ≤
      Real.sqrt n * ‖c‖ := by
  rw [EuclideanSpace.norm_eq]
  have hle : ∀ i, ‖(c i * Complex.exp ((ω : ℂ) * t * Complex.I)).re‖ ^ 2 ≤ ‖c‖ ^ 2 := by
    intro i
    have h1 : ‖(c i * Complex.exp ((ω : ℂ) * t * Complex.I)).re‖ ≤ ‖c‖ := by
      rw [Real.norm_eq_abs]
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, show (ω : ℂ) * t * Complex.I = ((ω * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      exact norm_le_pi_norm c i
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc Real.sqrt (∑ i, ‖(WithLp.toLp 2 fun i => (c i * Complex.exp ((ω : ℂ) * t * Complex.I)).re :
        ℝⁿ) i‖ ^ 2) ≤ Real.sqrt (∑ _i : Fin n, ‖c‖ ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => hle i)
    _ = Real.sqrt n * ‖c‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Real.sqrt_mul
          (Nat.cast_nonneg n), Real.sqrt_sq (norm_nonneg _)]

@[tmio T, powerlib_foundation] theorem continuous_re_phasor (c : Fin n → ℂ) (ω : ℝ) :
    Continuous fun t : ℝ =>
      (WithLp.toLp 2 fun i => (c i * Complex.exp ((ω : ℂ) * t * Complex.I)).re : ℝⁿ) := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fun_prop

/-- For a sinusoidal input `f = Re(b e^{jωt})` the steady state is the forced orbit
`Re(χ e^{jωt})`, `χ = (jωI − A)⁻¹ b`. -/
@[tmio T, powerlib_foundation] theorem boundedResponse_forcing (hA : IsHurwitz A) (b : Fin n → ℂ)
    (ω : ℝ) : boundedResponse A (forcing b ω) = forcedOrbit A b ω :=
  (eq_boundedResponse_of_bounded hA (continuous_re_phasor b ω) (fun t => norm_re_phasor_le b ω t)
    (forcedOrbit_solves b (Criteria.det_characteristicMatrix_ne_zero_of_isHurwitz hA (by simp)))
    (fun t => norm_re_phasor_le (forcedAmplitude A b ω) ω t)).symm

/-- Uniform bound on the forced orbit: `‖Re(χ e^{jωt})‖ ≤ (K/r)√n ‖b‖` for all `ω, t`. -/
@[tmio T, powerlib_foundation] theorem norm_forcedOrbit_le (hA : IsHurwitz A) :
    ∃ C, 0 ≤ C ∧ ∀ (b : Fin n → ℂ) (ω t : ℝ), ‖forcedOrbit A b ω t‖ ≤ C * ‖b‖ := by
  obtain ⟨K, hK, r, hr, hxp⟩ := norm_boundedResponse_le hA
  refine ⟨K / r * Real.sqrt n, by positivity, fun b ω t => ?_⟩
  rw [← boundedResponse_forcing hA b ω, mul_assoc]
  exact hxp _ (continuous_re_phasor b ω) _ (fun t => norm_re_phasor_le b ω t) t

/-- Superposition for an absolutely summable family of sinusoids (in particular the Fourier
series (2-13) of a periodic input, `ω_m = mω₀`): the steady state of
`f = Σ_m Re(b_m e^{jω_m t})` is `Σ_m Re(χ_m e^{jω_m t})`, `χ_m = (jω_mI − A)⁻¹ b_m`. -/
@[tmio T, powerlib_foundation] theorem boundedResponse_tsum (hA : IsHurwitz A) {ι : Type*}
    (b : ι → Fin n → ℂ) (ω : ι → ℝ) (hb : Summable fun m => ‖b m‖) :
    boundedResponse A (fun t => ∑' m, forcing (b m) (ω m) t) =
      fun t => ∑' m, forcedOrbit A (b m) (ω m) t := by
  obtain ⟨C, hC0, hC⟩ := norm_forcedOrbit_le hA
  have hfb : ∀ m t, ‖forcing (b m) (ω m) t‖ ≤ Real.sqrt n * ‖b m‖ :=
    fun m t => norm_re_phasor_le (b m) (ω m) t
  have hsf : ∀ t, Summable fun m => forcing (b m) (ω m) t := fun t =>
    Summable.of_norm_bounded (hb.mul_left (Real.sqrt n)) (fun m => hfb m t)
  have hso : ∀ t, Summable fun m => forcedOrbit A (b m) (ω m) t := fun t =>
    Summable.of_norm_bounded (hb.mul_left C) (fun m => hC (b m) (ω m) t)
  have hdet : ∀ m, (Linear.characteristicMatrix A ((ω m : ℂ) * Complex.I)).det ≠ 0 :=
    fun m => Criteria.det_characteristicMatrix_ne_zero_of_isHurwitz hA (by simp)
  have hfc : Continuous fun t => ∑' m, forcing (b m) (ω m) t :=
    continuous_tsum (fun m => continuous_re_phasor (b m) (ω m)) (hb.mul_left (Real.sqrt n)) hfb
  have hfB : ∀ t, ‖∑' m, forcing (b m) (ω m) t‖ ≤ ∑' m, Real.sqrt n * ‖b m‖ := fun t =>
    tsum_of_norm_bounded (hb.mul_left (Real.sqrt n)).hasSum (fun m => hfb m t)
  have hyB : ∀ t, ‖∑' m, forcedOrbit A (b m) (ω m) t‖ ≤ ∑' m, C * ‖b m‖ := fun t =>
    tsum_of_norm_bounded (hb.mul_left C).hasSum (fun m => hC (b m) (ω m) t)
  have hderiv : ∀ t, HasDerivAt (fun s => ∑' m, forcedOrbit A (b m) (ω m) s)
      (Linear.op A (∑' m, forcedOrbit A (b m) (ω m) t) + ∑' m, forcing (b m) (ω m) t) t := by
    intro t
    have hu : Summable fun m => (‖Linear.op A‖ * C + Real.sqrt n) * ‖b m‖ := hb.mul_left _
    have h := hasDerivAt_tsum hu (fun m s => forcedOrbit_solves (b m) (hdet m) s)
      (fun m s => by
        calc ‖Linear.op A (forcedOrbit A (b m) (ω m) s) + forcing (b m) (ω m) s‖
            ≤ ‖Linear.op A‖ * ‖forcedOrbit A (b m) (ω m) s‖ + ‖forcing (b m) (ω m) s‖ :=
              (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.le_opNorm _ _) le_rfl)
          _ ≤ ‖Linear.op A‖ * (C * ‖b m‖) + Real.sqrt n * ‖b m‖ := by
              gcongr
              · exact hC _ _ _
              · exact hfb m s
          _ = (‖Linear.op A‖ * C + Real.sqrt n) * ‖b m‖ := by ring)
      (hso 0) t
    rw [Summable.tsum_add ((hso t).mapL (Linear.op A)) (hsf t),
      ← ContinuousLinearMap.map_tsum _ (hso t)] at h
    exact h
  exact (eq_boundedResponse_of_bounded hA hfc hfB hderiv hyB).symm

/-- Superposition for finitely many sinusoids. -/
@[tmio T, powerlib_foundation] theorem boundedResponse_sum (hA : IsHurwitz A) {ι : Type*} [Fintype ι]
    (b : ι → Fin n → ℂ) (ω : ι → ℝ) :
    boundedResponse A (fun t => ∑ m, forcing (b m) (ω m) t) =
      fun t => ∑ m, forcedOrbit A (b m) (ω m) t := by
  have h := boundedResponse_tsum hA b ω (Summable.of_finite)
  simp only [tsum_fintype] at h
  exact h

/-! ## The three components (2-14) and the modal kernel -/

/-- Variation of constants for `ẋ = A x + u(t)` with continuous `u`:
`x(t) = e^{tA}x(0) + ∫₀ᵗ e^{(t−s)A} u(s) ds` for every `t`. -/
@[tmio T, powerlib_foundation] theorem variation_of_constants {u : ℝ → ℝⁿ} (hu : Continuous u)
    {x : ℝ → ℝⁿ} (hx : ∀ t, HasDerivAt x (Linear.op A (x t) + u t) t) (t : ℝ) :
    x t = exp (t • Linear.op A) (x 0) + ∫ s in (0 : ℝ)..t, exp ((t - s) • Linear.op A) (u s) := by
  set M := Linear.op A
  set φ : ℝ → ℝⁿ := fun s => exp ((-s) • M) (u s)
  have hφc : Continuous φ := ((continuous_exp_smul A).comp continuous_neg).clm_apply hu
  -- `z(s) = e^{−sA} x(s) − ∫₀ˢ φ` has zero derivative
  have hz : ∀ s, HasDerivAt (fun s => exp ((-s) • M) (x s) - ∫ r in (0 : ℝ)..s, φ r) 0 s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => exp ((-s) • M)) (-(M * exp ((-s) • M))) s := by
      have h := (hasDerivAt_exp_smul_const' M (-s)).scomp s (hasDerivAt_neg s)
      exact h.congr_deriv (by rw [neg_one_smul])
    have h2 := h1.clm_apply (hx s)
    have h3 := (hφc.integral_hasStrictDerivAt 0 s).hasDerivAt
    refine (h2.sub h3).congr_deriv ?_
    show (-(M * exp ((-s) • M))) (x s) + exp ((-s) • M) (M (x s) + u s) -
      exp ((-s) • M) (u s) = 0
    rw [_root_.neg_apply, mul_apply_eq_comp, map_add, exp_smul_apply_comm]
    abel
  have hconst := is_const_of_deriv_eq_zero (fun s => (hz s).differentiableAt)
    (fun s => (hz s).deriv) t 0
  simp only [neg_zero, exp_zero_smul, one_apply_eq_self,
    intervalIntegral.integral_same, sub_zero] at hconst
  -- multiply by `e^{tA}`
  have hx' : x t = exp (t • M) (x 0 + ∫ r in (0 : ℝ)..t, φ r) := by
    rw [← hconst, sub_add_cancel, ← mul_apply_eq_comp, exp_smul_mul_neg,
      one_apply_eq_self]
  rw [hx', map_add, ← ContinuousLinearMap.intervalIntegral_comp_comm _
    (hφc.intervalIntegrable 0 t)]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [φ]
  rw [← mul_apply_eq_comp, ← exp_smul_add, sub_eq_add_neg]

/-- Eq. (2-14): the response of `ẋ = A x + Σ_k b_{e,k} e_k(t) + b_f f(t)` (eq. (2-12); continuous
ambient sample paths `e_k`, continuous deterministic input `f`) is the sum of the transient
`e^{tA}x(0)`, the ambient responses `∫₀ᵗ e_k(s) e^{(t−s)A} b_{e,k} ds` and the forced response
`∫₀ᵗ f(s) e^{(t−s)A} b_f ds`. -/
@[tmio T, powerlib_foundation] theorem three_components {K : ℕ} (be : Fin K → ℝⁿ)
    (e : Fin K → ℝ → ℝ) (he : ∀ k, Continuous (e k)) (bf : ℝⁿ) {g : ℝ → ℝ} (hg : Continuous g)
    {x : ℝ → ℝⁿ}
    (hx : ∀ t, HasDerivAt x (Linear.op A (x t) + ((∑ k, e k t • be k) + g t • bf)) t) (t : ℝ) :
    x t = exp (t • Linear.op A) (x 0) +
      (∑ k, ∫ s in (0 : ℝ)..t, e k s • exp ((t - s) • Linear.op A) (be k)) +
      ∫ s in (0 : ℝ)..t, g s • exp ((t - s) • Linear.op A) bf := by
  have hu : Continuous fun s => (∑ k, e k s • be k) + g s • bf :=
    (continuous_finsetSum _ fun k _ => (he k).smul continuous_const).add
      (hg.smul continuous_const)
  rw [variation_of_constants hu hx t, add_assoc]
  congr 1
  have hc : ∀ (c : ℝ → ℝ) (v : ℝⁿ), Continuous c →
      Continuous fun s => c s • exp ((t - s) • Linear.op A) v := fun c v hc =>
    hc.smul (((continuous_exp_smul A).comp (continuous_const.sub continuous_id)).clm_apply
      continuous_const)
  simp only [map_add, map_sum, map_smul]
  rw [intervalIntegral.integral_add
    ((continuous_finsetSum _ fun k _ => hc _ _ (he k)).intervalIntegrable 0 t)
    ((hc _ _ hg).intervalIntegrable 0 t),
    intervalIntegral.integral_finsetSum fun k _ => (hc _ _ (he k)).intervalIntegrable 0 t]

/-- The convolution kernel is modal: `e^{tA}x₀ = Σ_i e^{λ_i t}(ψ_iᵀx₀) v_i` (complexified), so
`C e^{tA} B = Σ_i e^{λ_i t} R^{(i)}` with the modal residues `R^{(i)} = (C v_i)(ψ_iᵀB)`. -/
@[tmio T, powerlib_foundation] theorem modal_kernel (mb : Modal.ModalBasis (Linear.complexify A))
    (x₀ : ℝⁿ) (t : ℝ) :
    (fun k => ((exp (t • Linear.op A) x₀) k : ℂ)) =
      ∑ i, (Complex.exp (mb.eig i * t) * (mb.ψ i ⬝ᵥ fun k => (x₀ k : ℂ))) • mb.v i := by
  have h := Modal.modal_free_response mb (x := fun s => exp (s • Linear.op A) x₀)
    (hasDerivAt_exp_apply A x₀) t
  simpa [exp_zero_smul] using h

/-- The input-output kernel is modal: for real `C`, `B` and an input vector `u`,
`C e^{tA} B u = Σ_i e^{λ_i t} R^{(i)} u` with the modal residues `R^{(i)} = (C v_i)(ψ_iᵀ B)`
(complexified; `Modal.ModalBasis.residue`). -/
@[tmio T, powerlib_foundation] theorem modal_kernel_residue
    (mb : Modal.ModalBasis (Linear.complexify A)) {p q : ℕ} (C : Matrix (Fin p) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin q) ℝ) (u : Fin q → ℝ) (t : ℝ) :
    Linear.complexify C *ᵥ (fun k => ((exp (t • Linear.op A) (WithLp.toLp 2 (B *ᵥ u))) k : ℂ)) =
      ∑ i, Complex.exp (mb.eig i * t) •
        (mb.residue (Linear.complexify C) (Linear.complexify B) i *ᵥ fun j => (u j : ℂ)) := by
  rw [modal_kernel mb, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcast : (fun k => (((WithLp.toLp 2 (B *ᵥ u) : ℝⁿ) k : ℝ) : ℂ)) =
      Linear.complexify B *ᵥ fun j => (u j : ℂ) := by
    funext k
    simp [Matrix.mulVec, dotProduct]
  have hres : mb.residue (Linear.complexify C) (Linear.complexify B) i *ᵥ (fun j => (u j : ℂ)) =
      (vecMul (mb.ψ i) (Linear.complexify B) ⬝ᵥ fun j => (u j : ℂ)) •
        (Linear.complexify C *ᵥ mb.v i) := by
    ext l
    simp only [Modal.ModalBasis.residue, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hcast, Matrix.mulVec_smul, Matrix.dotProduct_mulVec, hres, smul_smul]

end powerlib.LTI
