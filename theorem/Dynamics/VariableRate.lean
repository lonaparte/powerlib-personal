import dependencies.Mathlib
import theorem.Attributes

/-! # Scalar differential inequalities with a time-varying rate

Comparison laws for a real function of time whose derivative is bounded by a multiple of itself
with a time-varying coefficient, `g' ≤ λ(t) g` (or `≥`, or `=`): `g` stays below (above, equal
to) `g(0) e^{∫₀ᵗ λ}`. A Barbalat-type law: a nonnegative function `Ψ` with `Ψ' ≤ −k h`, `k > 0`,
`h ≥ 0` and `h'` bounded below forces `h → 0`.

Scope.
* Generic: real functions of time `g, Ψ, h : ℝ → ℝ`, derivatives at every `t ≥ 0`
  (`HasDerivAt`), a continuous rate `λ : ℝ → ℝ`; forward time `[0, ∞)`. No model, no family; the
  conclusions are about one function of time (implementation support for trajectory-level
  evidence).

Source: the integrating-factor form of Grönwall's inequality (P. Hartman, *Ordinary Differential
Equations*, Ch. III, Theorem 1.1 with the linear comparison equation); Barbalat's lemma in the
derivative form (H. K. Khalil, *Nonlinear Systems*, 3rd ed., Lemma 8.2, with the integral of `h`
bounded through `Ψ`).

Results.
* `le_mul_exp_integral`: `g' ≤ λ g` on `[0, ∞)` ⇒ `g(t) ≤ g(0) e^{∫₀ᵗ λ}`.
* `mul_exp_integral_le`: `λ g ≤ g'` on `[0, ∞)` ⇒ `g(0) e^{∫₀ᵗ λ} ≤ g(t)`; a positive start stays
  positive.
* `eq_mul_exp_integral`: `g' = λ g` on `[0, ∞)` ⇒ `g(t) = g(0) e^{∫₀ᵗ λ}`.
* `tendsto_zero_of_hasDerivAt_le`: `Ψ ≥ 0`, `Ψ' ≤ −k h`, `k > 0`, `h ≥ 0`, `h' ≥ −L` ⇒
  `h(t) → 0`.
-/

noncomputable section
namespace powerlib.Dynamics.VariableRate

open Set Filter Topology

@[powerlib_foundation] private theorem hasDerivAt_integral {lam : ℝ → ℝ} (hlam : Continuous lam)
    (u : ℝ) :
    HasDerivAt (fun v => ∫ s in (0 : ℝ)..v, lam s) (lam u) u :=
  (hlam.integral_hasStrictDerivAt 0 u).hasDerivAt

/-- **Comparison with a variable rate (upper).** If `g' ≤ λ g` on `[0, ∞)` with `λ` continuous,
then `g(t) ≤ g(0) e^{∫₀ᵗ λ}` for `t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem le_mul_exp_integral {g g' lam : ℝ → ℝ}
    (hlam : Continuous lam) (hg : ∀ t, 0 ≤ t → HasDerivAt g (g' t) t)
    (hle : ∀ t, 0 ≤ t → g' t ≤ lam t * g t) {t : ℝ} (ht : 0 ≤ t) :
    g t ≤ g 0 * Real.exp (∫ s in (0 : ℝ)..t, lam s) := by
  have hq : ∀ u, 0 ≤ u →
      HasDerivAt (fun v => g v * Real.exp (-∫ s in (0 : ℝ)..v, lam s))
        ((g' u - lam u * g u) * Real.exp (-∫ s in (0 : ℝ)..u, lam s)) u := by
    intro u hu
    have h := (hg u hu).fun_mul (hasDerivAt_integral hlam u).fun_neg.exp
    convert h using 1
    ring
  have hanti : AntitoneOn (fun v => g v * Real.exp (-∫ s in (0 : ℝ)..v, lam s)) (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun u hu => (hq u hu).continuousAt.continuousWithinAt) (fun u hu => ?_) (fun u hu => ?_)
    · rw [interior_Ici] at hu
      exact (hq u (le_of_lt hu)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici] at hu
      rw [(hq u (le_of_lt hu)).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hle u (le_of_lt hu)])
        (Real.exp_pos _).le
  have h := hanti self_mem_Ici ht ht
  simp only [intervalIntegral.integral_same, neg_zero, Real.exp_zero, mul_one] at h
  have h2 := mul_le_mul_of_nonneg_right h (Real.exp_pos (∫ s in (0 : ℝ)..t, lam s)).le
  rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at h2

/-- **Comparison with a variable rate (lower).** If `λ g ≤ g'` on `[0, ∞)` with `λ` continuous,
then `g(0) e^{∫₀ᵗ λ} ≤ g(t)` for `t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem mul_exp_integral_le {g g' lam : ℝ → ℝ}
    (hlam : Continuous lam) (hg : ∀ t, 0 ≤ t → HasDerivAt g (g' t) t)
    (hle : ∀ t, 0 ≤ t → lam t * g t ≤ g' t) {t : ℝ} (ht : 0 ≤ t) :
    g 0 * Real.exp (∫ s in (0 : ℝ)..t, lam s) ≤ g t := by
  have h := le_mul_exp_integral (g := fun v => -g v) (g' := fun v => -g' v) hlam
    (fun u hu => (hg u hu).fun_neg) (fun u hu => by nlinarith [hle u hu]) ht
  linarith

/-- **Linear equation with a variable rate.** If `g' = λ g` on `[0, ∞)` with `λ` continuous, then
`g(t) = g(0) e^{∫₀ᵗ λ}` for `t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem eq_mul_exp_integral {g g' lam : ℝ → ℝ}
    (hlam : Continuous lam) (hg : ∀ t, 0 ≤ t → HasDerivAt g (g' t) t)
    (heq : ∀ t, 0 ≤ t → g' t = lam t * g t) {t : ℝ} (ht : 0 ≤ t) :
    g t = g 0 * Real.exp (∫ s in (0 : ℝ)..t, lam s) :=
  le_antisymm (le_mul_exp_integral hlam hg (fun u hu => (heq u hu).le) ht)
    (mul_exp_integral_le hlam hg (fun u hu => (heq u hu).ge) ht)

/-- **Barbalat-type decay.** If `Ψ ≥ 0` with `Ψ' ≤ −k h` on `[0, ∞)` (`k > 0`), and `h ≥ 0` has
derivative bounded below, `h' ≥ −L`, then `h(t) → 0`: on `[t, t + δ]` the function `h` stays above
`h(t) − Lδ`, so `Ψ` drops by at least `kδ (h(t) − Lδ)`, while `Ψ` converges. -/
@[tmio T, powerlib_foundation] theorem tendsto_zero_of_hasDerivAt_le {Ψ Ψ' h h' : ℝ → ℝ}
    {k L : ℝ} (hk : 0 < k) (hΨ : ∀ t, 0 ≤ t → HasDerivAt Ψ (Ψ' t) t)
    (hle : ∀ t, 0 ≤ t → Ψ' t ≤ -(k * h t)) (hΨ0 : ∀ t, 0 ≤ t → 0 ≤ Ψ t)
    (hh : ∀ t, 0 ≤ t → HasDerivAt h (h' t) t) (hh0 : ∀ t, 0 ≤ t → 0 ≤ h t)
    (hL : ∀ t, 0 ≤ t → -L ≤ h' t) : Tendsto h atTop (𝓝 0) := by
  set L' := max L 1 with hL'
  have hL'0 : 0 < L' := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- `h` cannot drop faster than `L'`
  have hslow : ∀ t s, 0 ≤ t → t ≤ s → h t - L' * (s - t) ≤ h s := by
    intro t s ht hts
    have hd : ∀ u, t ≤ u → HasDerivAt (fun v => h v + L' * v) (h' u + L') u := fun u hu => by
      simpa using (hh u (ht.trans hu)).fun_add ((hasDerivAt_id u).const_mul L')
    have hmono : MonotoneOn (fun v => h v + L' * v) (Ici t) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici t)
        (fun u hu => (hd u hu).continuousAt.continuousWithinAt) (fun u hu => ?_) (fun u hu => ?_)
      · rw [interior_Ici] at hu
        exact (hd u hu.le).differentiableAt.differentiableWithinAt
      · rw [interior_Ici] at hu
        rw [(hd u hu.le).deriv]
        have := hL u (ht.trans hu.le)
        have : L ≤ L' := le_max_left _ _
        linarith
    have := hmono self_mem_Ici hts hts
    simp only at this
    linarith
  -- `Ψ` decreases by `kδ (h t − L'δ)` on `[t, t + δ]`
  have hdrop : ∀ t δ, 0 ≤ t → 0 ≤ δ → Ψ (t + δ) + k * δ * (h t - L' * δ) ≤ Ψ t := by
    intro t δ ht hδ
    have hanti : AntitoneOn (fun v => Ψ v + k * (h t - L' * δ) * (v - t)) (Icc t (t + δ)) := by
      have hd : ∀ u, t ≤ u → HasDerivAt (fun v => Ψ v + k * (h t - L' * δ) * (v - t))
          (Ψ' u + k * (h t - L' * δ)) u := fun u hu => by
        have := (hΨ u (ht.trans hu)).fun_add (((hasDerivAt_id u).sub_const t).const_mul
          (k * (h t - L' * δ)))
        simpa using this
      refine antitoneOn_of_deriv_nonpos (convex_Icc t (t + δ))
        (fun u hu => (hd u hu.1).continuousAt.continuousWithinAt) (fun u hu => ?_)
        (fun u hu => ?_)
      · rw [interior_Icc] at hu
        exact (hd u hu.1.le).differentiableAt.differentiableWithinAt
      · rw [interior_Icc] at hu
        rw [(hd u hu.1.le).deriv]
        have h1 := hle u (ht.trans hu.1.le)
        have h2 := hslow t u ht hu.1.le
        have h3 : L' * (u - t) ≤ L' * δ := mul_le_mul_of_nonneg_left (by linarith [hu.2]) hL'0.le
        nlinarith
    have := hanti ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
    simp only [sub_self, mul_zero, add_zero, add_sub_cancel_left] at this
    linarith
  -- convergence of `Ψ`
  set ℓ := ⨅ u : Ici (0 : ℝ), Ψ u with hℓ
  have hbdd : BddBelow (range fun u : Ici (0 : ℝ) => Ψ u) :=
    ⟨0, by rintro _ ⟨u, rfl⟩; exact hΨ0 u u.2⟩
  have hanti : AntitoneOn Ψ (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun u hu => (hΨ u hu).continuousAt.continuousWithinAt) (fun u hu => ?_) (fun u hu => ?_)
    · rw [interior_Ici] at hu
      exact (hΨ u hu.le).differentiableAt.differentiableWithinAt
    · rw [interior_Ici] at hu
      rw [(hΨ u hu.le).deriv]
      nlinarith [hle u hu.le, hh0 u hu.le]
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := ε / (2 * L') with hδ
  have hδ0 : 0 < δ := by positivity
  have hlt : ℓ < ℓ + k * δ * (ε / 2) := by linarith [show 0 < k * δ * (ε / 2) by positivity]
  obtain ⟨⟨T, hT0⟩, hT⟩ := exists_lt_of_ciInf_lt hlt
  refine ⟨T, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := (show (0 : ℝ) ≤ T from hT0).trans ht
  have h1 := hdrop t δ ht0 hδ0.le
  have h2 : ℓ ≤ Ψ (t + δ) := ciInf_le hbdd ⟨t + δ, by simp only [mem_Ici]; linarith⟩
  have h3 : Ψ t ≤ Ψ T := hanti hT0 (show t ∈ Ici 0 from ht0) ht
  have hLδ : L' * δ = ε / 2 := by rw [hδ]; field_simp
  rw [hLδ] at h1
  simp only at hT
  have h4 : k * δ * (h t - ε / 2) < k * δ * (ε / 2) := by linarith
  have h5 : h t - ε / 2 < ε / 2 := lt_of_mul_lt_mul_left h4 (by positivity)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hh0 t ht0)]
  linarith

end powerlib.Dynamics.VariableRate
