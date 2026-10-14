import theorem.Estimation.Conjugate

/-! # Gamma–Poisson conjugacy (i.i.d. counts)

A Gamma prior on a Poisson rate is updated to `Gamma(a + ∑ dᵢ, b + N)` by `N` i.i.d. counts.

Scope.
* General probability, not an engineering result.
* Rate `θ ∈ ℝ` with prior `gammaMeasure a b` (shape `a > 0`, rate `b > 0`, supported on
  `[0, ∞)`); data `d : Fin N → ℕ`, i.i.d. `Po(max θ 0)` given `θ` (`poissonIIDKernel N`).

Source: work-sync theory/T-bayesian-inference.md §1.4.2.

Results.
* `bayesPosterior_gamma_poisson` — the posterior is `Gamma(a + ∑ dᵢ, b + N)` at density level.
* `posterior_poissonIIDKernel_gammaMeasure` — the same for Mathlib's posterior kernel, a.e. in
  the data.
-/

noncomputable section
namespace powerlib.Estimation
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

/-- `N` i.i.d. Poisson counts with rate `max θ 0`. -/
def poissonIIDKernel (N : ℕ) : Kernel ℝ (Fin N → ℕ) where
  toFun θ := Measure.pi fun _ => poissonMeasure θ.toNNReal
  measurable' := by
    refine measurable_measure_of_singleton fun d => ?_
    simp_rw [← Set.univ_pi_singleton, Measure.pi_pi, poissonMeasure_singleton]
    refine Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp ?_
    have h : Measurable fun θ : ℝ => ((θ.toNNReal : ℝ≥0) : ℝ) :=
      measurable_coe_nnreal_real.comp measurable_real_toNNReal
    exact ((h.neg.exp).mul (h.pow_const _)).div_const _

instance (N : ℕ) : IsMarkovKernel (poissonIIDKernel N) :=
  ⟨fun θ => by simp only [poissonIIDKernel, Kernel.coe_mk]; infer_instance⟩

@[powerlib_foundation] theorem poissonIIDKernel_singleton (N : ℕ) {θ : ℝ} (hθ : 0 ≤ θ)
    (d : Fin N → ℕ) :
    poissonIIDKernel N θ {d} =
      ENNReal.ofReal (exp (-(N * θ)) * θ ^ (∑ i, d i) / ∏ i, ((d i).factorial : ℝ)) := by
  simp only [poissonIIDKernel, Kernel.coe_mk]
  rw [← Set.univ_pi_singleton, Measure.pi_pi]
  simp only [poissonMeasure_singleton, Real.coe_toNNReal _ hθ]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
  congr 1
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.prod_pow_eq_pow_sum, ← Real.exp_nat_mul]
  ring_nf

@[powerlib_foundation] private theorem measurable_gammaPDF (a r : ℝ) : Measurable (gammaPDF a r) :=
  ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal a r)

/-- Prior density × Poisson likelihood is a multiple of the updated Gamma density (`θ ≠ 0`). -/
@[powerlib_foundation] theorem gammaPDF_mul_poissonIID {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (N : ℕ) (d : Fin N → ℕ) {θ : ℝ} (hθ : θ ≠ 0) :
    gammaPDF a b θ * poissonIIDKernel N θ {d} =
      ENNReal.ofReal (b ^ a * Gamma (a + ∑ i, (d i : ℝ)) /
        (Gamma a * (∏ i, ((d i).factorial : ℝ)) * (b + N) ^ (a + ∑ i, (d i : ℝ)))) *
        gammaPDF (a + ∑ i, (d i : ℝ)) (b + N) θ := by
  rcases lt_or_gt_of_ne hθ with hneg | hpos
  · rw [gammaPDF_of_neg hneg, gammaPDF_of_neg hneg, zero_mul, mul_zero]
  · have hS : (0 : ℝ) ≤ ∑ i, (d i : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
    have hG : 0 < Gamma a := Gamma_pos_of_pos ha
    have hG' : 0 < Gamma (a + ∑ i, (d i : ℝ)) := Gamma_pos_of_pos (by linarith)
    have hF : (0 : ℝ) < ∏ i, ((d i).factorial : ℝ) :=
      Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _
    have hbN : 0 < b + N := by positivity
    rw [poissonIIDKernel_singleton N hpos.le, gammaPDF_of_nonneg hpos.le,
      gammaPDF_of_nonneg hpos.le, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have e1 : θ ^ (a + ∑ i, (d i : ℝ) - 1) = θ ^ (a - 1) * θ ^ (∑ i, d i) := by
      rw [show a + ∑ i, (d i : ℝ) - 1 = (a - 1) + ((∑ i, d i : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_add hpos, Real.rpow_natCast]
    have e2 : exp (-((b + N) * θ)) = exp (-(b * θ)) * exp (-(N * θ)) := by
      rw [← Real.exp_add]; ring_nf
    have e3 : (b + N) ^ (a + ∑ i, (d i : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hbN _).ne'
    rw [e1, e2]
    field_simp

/-- **Gamma–Poisson conjugacy** (density level). -/
@[powerlib_foundation] theorem bayesPosterior_gamma_poisson {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (N : ℕ) (d : Fin N → ℕ) :
    bayesPosterior (gammaMeasure a b) (fun θ => poissonIIDKernel N θ {d}) =
      gammaMeasure (a + ∑ i, (d i : ℝ)) (b + N) := by
  have hS : (0 : ℝ) ≤ ∑ i, (d i : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
  have hG' : 0 < Gamma (a + ∑ i, (d i : ℝ)) := Gamma_pos_of_pos (by linarith)
  have hG : 0 < Gamma a := Gamma_pos_of_pos ha
  have hF : (0 : ℝ) < ∏ i, ((d i).factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _
  have hbN : 0 < b + N := by positivity
  have hne : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 := by
    rw [ae_iff]; simp
  refine bayesPosterior_withDensity_eq (measurable_gammaPDF a b)
    (Kernel.measurable_coe _ (measurableSet_singleton d)) ?_ ENNReal.ofReal_ne_top
    (hne.mono fun θ hθ => gammaPDF_mul_poissonIID ha hb N d hθ)
    (lintegral_gammaPDF_eq_one (by linarith) hbN)
  exact (ENNReal.ofReal_pos.mpr (by
    have := Real.rpow_pos_of_pos hbN (a + ∑ i, (d i : ℝ))
    have := Real.rpow_pos_of_pos hb a
    positivity)).ne'

/-- **Gamma–Poisson conjugacy, Mathlib posterior kernel**:
`(poissonIIDKernel N)†Gamma(a, b) =ᵐ d ↦ Gamma(a + ∑ dᵢ, b + N)`. -/
@[powerlib_foundation] theorem posterior_poissonIIDKernel_gammaMeasure {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (N : ℕ) :
    have := isProbabilityMeasure_gammaMeasure ha hb
    (poissonIIDKernel N)†(gammaMeasure a b) =ᵐ[poissonIIDKernel N ∘ₘ gammaMeasure a b]
      fun d => gammaMeasure (a + ∑ i, (d i : ℝ)) (b + N) := by
  have := isProbabilityMeasure_gammaMeasure ha hb
  filter_upwards [posterior_ae_eq_bayesPosterior_of_countable (μ := gammaMeasure a b)
    (κ := poissonIIDKernel N)] with d hd
  rw [hd, bayesPosterior_gamma_poisson ha hb N d]

end powerlib.Estimation
