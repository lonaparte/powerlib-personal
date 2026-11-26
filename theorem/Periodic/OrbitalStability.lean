import theorem.Periodic.Floquet
import theorem.Dynamics.VariationOfConstants

/-! # Exponential stability of a solution from the Floquet multipliers of its linearization

A solution `x_*` of `ẋ = G(t, x)` whose linearization `J(t)` is continuous and `T`-periodic with
monodromy spectral radius below one attracts every solution that starts close enough, uniformly
in the initial time and exponentially: `‖x(t) − x_*(t)‖ ≤ K e^{−β(t − s)} ‖x(s) − x_*(s)‖`. The
proof combines variation of constants around `J`, the uniform exponential bound of the periodic
linear system, an integral Grönwall inequality and a first-exit argument.

Scope.
* Finite state space with the sup norm. `G` is continuous on the tube `‖x − x_*(t)‖ ≤ ρ` only,
  with the quadratic remainder `‖G(t, x_* + e) − G(t, x_*) − J(t) e‖ ≤ L‖e‖²` there; `x_*` is a
  differentiable solution; solutions `x` are integral curves on `[s, ∞)`.
* The statement is local: initial deviations `‖x(s) − x_*(s)‖ ≤ δ`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.2 (Floquet multipliers inside the unit circle as the stability criterion of the
forced trajectory); [8, 9] of that report (Floquet theory).

Results.
* `le_of_integral_gronwall` — `g(τ) ≤ a + b ∫ₛ^τ g` on `[s, t]` gives `g(t) ≤ a e^{b(t − s)}`.
* `deviation_estimate` — with `‖Φ(t, τ)‖ ≤ K₀ e^{−β₀(t − τ)}` and the deviation below `η` on
  `[s, t]`: `‖e(t)‖ ≤ K₀ ‖e(s)‖ e^{(K₀Lη − β₀)(t − s)}`.
* `exp_stable_of_floquet` — `ρ(Φ(T, 0)) < 1` gives `δ > 0`, `K`, `β > 0` with the exponential
  estimate for every solution starting within `δ`.

Corrections.
None: an extension (the report stops at the multipliers).

Family and connection conclusions.
None: static evidence on nonautonomous ODEs (local exponential stability).
-/

noncomputable section
namespace powerlib.Periodic
open Set Matrix Function Filter Topology
open scoped Matrix.Norms.Operator

/-- Integral Grönwall inequality: a continuous nonnegative `g` with
`g(τ) ≤ a + b ∫ₛ^τ g` on `[s, t]` (`a, b ≥ 0`) satisfies `g(t) ≤ a e^{b(t − s)}`. -/
@[tmio T, powerlib_foundation] theorem le_of_integral_gronwall {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ τ, 0 ≤ g τ) {a b s t : ℝ} (hb : 0 ≤ b) (hst : s ≤ t)
    (h : ∀ τ ∈ Icc s t, g τ ≤ a + b * ∫ σ in s..τ, g σ) :
    g t ≤ a * Real.exp (b * (t - s)) := by
  set H : ℝ → ℝ := fun τ => ∫ σ in s..τ, g σ with hH
  have hHd : ∀ τ, HasDerivAt H (g τ) τ := fun τ =>
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have hH0 : ∀ τ ∈ Icc s t, 0 ≤ H τ := fun τ hτ =>
    intervalIntegral.integral_nonneg hτ.1 fun σ _ => hg0 σ
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := H) (f' := g) (δ := 0) (K := b)
    (ε := a) (a := s) (b := t)
    (fun τ _ => (hHd τ).continuousAt.continuousWithinAt)
    (fun τ _ => (hHd τ).hasDerivWithinAt)
    (by simp [hH])
    (fun τ hτ => by
      rw [Real.norm_of_nonneg (hg0 τ), Real.norm_of_nonneg (hH0 τ (Ico_subset_Icc_self hτ))]
      have := h τ (Ico_subset_Icc_self hτ)
      linarith)
  have hHt := hgr t ⟨hst, le_rfl⟩
  rw [Real.norm_of_nonneg (hH0 t ⟨hst, le_rfl⟩)] at hHt
  have hgt := h t ⟨hst, le_rfl⟩
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · subst hb0; simpa using hgt
  · rw [gronwallBound_of_K_ne_0 hbpos.ne'] at hHt
    simp only [zero_mul, zero_add] at hHt
    have : b * H t ≤ a * (Real.exp (b * (t - s)) - 1) := by
      have := mul_le_mul_of_nonneg_left hHt hb
      rwa [show b * (a / b * (Real.exp (b * (t - s)) - 1)) = a * (Real.exp (b * (t - s)) - 1) by
        field_simp] at this
    linarith

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The variation-of-constants estimate for the deviation from a solution: with
`‖Φ(t, τ)‖ ≤ K₀ e^{−β₀(t − τ)}`, a remainder `‖R(τ, e)‖ ≤ L‖e‖²` and `‖e‖ ≤ η` on `[s, t]`,
`‖e(t)‖ ≤ K₀ ‖e(s)‖ e^{(K₀Lη − β₀)(t − s)}`. -/
@[tmio T, powerlib_foundation] theorem deviation_estimate {G : ℝ → (X → ℝ) → X → ℝ}
    {xs : ℝ → X → ℝ} {J : ℝ → Matrix X X ℝ} (hJc : Continuous J)
    (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) {ρ : ℝ}
    (hGc : ContinuousOn (fun p : ℝ × (X → ℝ) => G p.1 p.2) {p | ‖p.2 - xs p.1‖ ≤ ρ})
    {K0 β0 L η : ℝ} (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hη : 0 ≤ η) (hηρ : η ≤ ρ)
    (hΦ : ∀ s t, s ≤ t → ‖transition J t s‖ ≤ K0 * Real.exp (-(β0 * (t - s))))
    (hR : ∀ t e, ‖e‖ ≤ ρ → ‖G t (xs t + e) - G t (xs t) - J t *ᵥ e‖ ≤ L * ‖e‖ ^ 2)
    {s : ℝ} {x : ℝ → X → ℝ} (hx : IsIntegralCurveOn x G (Ici s)) {t : ℝ} (hst : s ≤ t)
    (hbd : ∀ τ ∈ Icc s t, ‖x τ - xs τ‖ ≤ η) :
    ‖x t - xs t‖ ≤ K0 * ‖x s - xs s‖ * Real.exp ((K0 * L * η - β0) * (t - s)) := by
  set e : ℝ → X → ℝ := fun τ => x τ - xs τ with he
  have hxsc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  have hxc : ContinuousOn x (Ici s) := hx.continuousOn
  set c : ℝ → ℝ := fun τ => max s (min τ t) with hcd
  have hmax : Continuous c := continuous_const.max (continuous_id.min continuous_const)
  have hcI : ∀ τ, c τ ∈ Icc s t := fun τ => ⟨le_max_left _ _, max_le hst (min_le_right _ _)⟩
  have hcid : ∀ τ ∈ Icc s t, c τ = τ := fun τ hτ => by
    simp only [hcd]; rw [min_eq_left hτ.2, max_eq_right hτ.1]
  have hxm : Continuous fun τ => x (c τ) :=
    hxc.comp_continuous hmax fun τ => (hcI τ).1
  set et : ℝ → X → ℝ := fun τ => e (c τ) with het
  have hetc : Continuous et := hxm.sub (hxsc.comp hmax)
  set u : ℝ → X → ℝ := fun τ => G (c τ) (x (c τ)) - G (c τ) (xs (c τ)) -
    J (c τ) *ᵥ et τ with hu
  have huc : Continuous u := by
    have h1 : Continuous fun τ => G (c τ) (x (c τ)) :=
      hGc.comp_continuous (hmax.prodMk hxm) fun τ => by
        show ‖x (c τ) - xs (c τ)‖ ≤ ρ
        exact (hbd _ (hcI τ)).trans hηρ
    have h2 : Continuous fun τ => G (c τ) (xs (c τ)) :=
      hGc.comp_continuous (hmax.prodMk (hxsc.comp hmax)) fun τ => by
        show ‖xs (c τ) - xs (c τ)‖ ≤ ρ
        rw [sub_self, norm_zero]; linarith [hη, hηρ]
    exact (h1.sub h2).sub ((hJc.comp hmax).matrix_mulVec hetc)
  -- the deviation solves the forced linear system on every `[s, t']`
  have hvc : ∀ t' ∈ Icc s t, e t' = transition J t' s *ᵥ e s +
      ∫ τ in s..t', transition J t' τ *ᵥ ((1 : Matrix X X ℝ) *ᵥ u τ) := by
    intro t' ht'
    have hcurve : IsIntegralCurveOn e (fun τ v => J τ *ᵥ v + (fun _ => (1 : Matrix X X ℝ)) τ *ᵥ u τ)
        (uIcc s t') := by
      intro τ hτ
      rw [uIcc_of_le ht'.1] at hτ ⊢
      have h1 : HasDerivWithinAt x (G τ (x τ)) (Icc s t') τ :=
        (hx τ hτ.1).mono Icc_subset_Ici_self
      have h2 := (hxs τ).hasDerivWithinAt (s := Icc s t')
      refine (h1.sub h2).congr_deriv ?_
      have hm : c τ = τ := hcid τ ⟨hτ.1, hτ.2.trans ht'.2⟩
      simp only [hu, het, he, hm, Matrix.one_mulVec]
      abel
    exact Dynamics.eq_forcedResponse_of_isIntegralCurveOn (B := fun _ => (1 : Matrix X X ℝ))
      hJc continuous_const huc hcurve rfl t' right_mem_uIcc
  -- the integrand bound
  have hint : ∀ t' ∈ Icc s t, ‖e t'‖ ≤ K0 * Real.exp (-(β0 * (t' - s))) * ‖e s‖ +
      ∫ τ in s..t', K0 * Real.exp (-(β0 * (t' - τ))) * (L * η) * ‖et τ‖ := by
    intro t' ht'
    rw [hvc t' ht']
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (linfty_opNorm_mulVec _ _).trans
        (mul_le_mul_of_nonneg_right (hΦ s t' ht'.1) (norm_nonneg _))
    · refine intervalIntegral.norm_integral_le_of_norm_le ht'.1 (Eventually.of_forall
        fun τ hτ => ?_) ?_
      · have hτt : τ ∈ Icc s t := ⟨hτ.1.le, hτ.2.trans ht'.2⟩
        have hm : c τ = τ := hcid τ hτt
        have heb := hbd τ hτt
        have hRτ := hR τ (e τ) (heb.trans hηρ)
        have hxe : xs τ + e τ = x τ := by simp [he]
        rw [hxe] at hRτ
        have hu' : (1 : Matrix X X ℝ) *ᵥ u τ = G τ (x τ) - G τ (xs τ) - J τ *ᵥ e τ := by
          simp [hu, het, hm]
        rw [hu']
        have het' : et τ = e τ := by simp [het, hm]
        rw [het']
        calc ‖transition J t' τ *ᵥ (G τ (x τ) - G τ (xs τ) - J τ *ᵥ e τ)‖ ≤
              ‖transition J t' τ‖ * (L * ‖e τ‖ ^ 2) :=
            (linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_left hRτ (norm_nonneg _))
          _ ≤ K0 * Real.exp (-(β0 * (t' - τ))) * (L * (η * ‖e τ‖)) := by
            refine mul_le_mul (hΦ τ t' hτ.2) ?_ (by positivity) (by positivity)
            rw [sq]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right heb (norm_nonneg _)) hL
          _ = K0 * Real.exp (-(β0 * (t' - τ))) * (L * η) * ‖e τ‖ := by ring
      · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  -- the weighted deviation and Grönwall
  set g : ℝ → ℝ := fun τ => Real.exp (β0 * (τ - s)) * ‖et τ‖ with hg
  have hgc : Continuous g := by fun_prop
  have hg0 : ∀ τ, 0 ≤ g τ := fun τ => by positivity
  have hgi : ∀ t' ∈ Icc s t, g t' ≤ K0 * ‖e s‖ + K0 * L * η * ∫ σ in s..t', g σ := by
    intro t' ht'
    have h := hint t' ht'
    have hm : c t' = t' := hcid t' ht'
    have het' : et t' = e t' := by simp [het, hm]
    have hpos : 0 < Real.exp (β0 * (t' - s)) := Real.exp_pos _
    have hI : Real.exp (β0 * (t' - s)) *
        ∫ τ in s..t', K0 * Real.exp (-(β0 * (t' - τ))) * (L * η) * ‖et τ‖ =
        K0 * L * η * ∫ σ in s..t', g σ := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
      congr 1
      funext τ
      simp only [hg]
      have : Real.exp (β0 * (t' - s)) * Real.exp (-(β0 * (t' - τ))) = Real.exp (β0 * (τ - s)) := by
        rw [← Real.exp_add]; congr 1; ring
      calc Real.exp (β0 * (t' - s)) * (K0 * Real.exp (-(β0 * (t' - τ))) * (L * η) * ‖et τ‖) =
            K0 * L * η * ((Real.exp (β0 * (t' - s)) * Real.exp (-(β0 * (t' - τ)))) * ‖et τ‖) := by
            ring
        _ = _ := by rw [this]
    have hE : Real.exp (β0 * (t' - s)) * (K0 * Real.exp (-(β0 * (t' - s))) * ‖e s‖) =
        K0 * ‖e s‖ := by
      rw [show Real.exp (β0 * (t' - s)) * (K0 * Real.exp (-(β0 * (t' - s))) * ‖e s‖) =
        K0 * ‖e s‖ * (Real.exp (β0 * (t' - s)) * Real.exp (-(β0 * (t' - s)))) by ring,
        ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    calc g t' = Real.exp (β0 * (t' - s)) * ‖e t'‖ := by simp only [hg, het']
      _ ≤ Real.exp (β0 * (t' - s)) * (K0 * Real.exp (-(β0 * (t' - s))) * ‖e s‖ +
          ∫ τ in s..t', K0 * Real.exp (-(β0 * (t' - τ))) * (L * η) * ‖et τ‖) :=
          mul_le_mul_of_nonneg_left h hpos.le
      _ = _ := by rw [mul_add, hE, hI]
  have hgt := le_of_integral_gronwall hgc hg0 (by positivity) hst hgi
  have hm : c t = t := hcid t ⟨hst, le_rfl⟩
  have het' : et t = e t := by simp [het, hm]
  have hgt' : Real.exp (β0 * (t - s)) * ‖e t‖ ≤
      K0 * ‖e s‖ * Real.exp (K0 * L * η * (t - s)) := by
    simpa [hg, het'] using hgt
  have hpos : 0 < Real.exp (β0 * (t - s)) := Real.exp_pos _
  rw [show (K0 * L * η - β0) * (t - s) = K0 * L * η * (t - s) + -(β0 * (t - s)) by ring,
    Real.exp_add, Real.exp_neg, ← mul_assoc, le_mul_inv_iff₀ hpos, mul_comm]
  exact hgt'

/-- **Floquet multipliers inside the unit circle make a periodic solution of a nonlinear periodic
system locally exponentially stable.** `xs` solves `ẋ = G(t, x)`, `J(t)` is continuous,
`T`-periodic, with spectral radius of its monodromy below one, and it linearizes `G` along `xs`
with a quadratic remainder on `‖e‖ ≤ ρ`. Then there are `δ > 0`, `K`, `β > 0` such that every
forward solution with `‖x(s) − xs(s)‖ ≤ δ` satisfies
`‖x(t) − xs(t)‖ ≤ K e^{−β(t − s)} ‖x(s) − xs(s)‖` for all `t ≥ s`. -/
@[tmio T, powerlib_foundation] theorem exp_stable_of_floquet {G : ℝ → (X → ℝ) → X → ℝ}
    {xs : ℝ → X → ℝ} {J : ℝ → Matrix X X ℝ} {T : ℝ} (hT : 0 < T) (hJc : Continuous J)
    (hJp : Periodic J T)
    (hsr : spectralRadius ℂ ((monodromy J T 0).map (algebraMap ℝ ℂ)) < 1)
    (hxs : ∀ t, HasDerivAt xs (G t (xs t)) t) {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hGc : ContinuousOn (fun p : ℝ × (X → ℝ) => G p.1 p.2) {p | ‖p.2 - xs p.1‖ ≤ ρ})
    (hR : ∀ t e, ‖e‖ ≤ ρ → ‖G t (xs t + e) - G t (xs t) - J t *ᵥ e‖ ≤ L * ‖e‖ ^ 2) :
    ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → X → ℝ), IsIntegralCurveOn x G (Ici s) →
      ‖x s - xs s‖ ≤ δ → ∀ t, s ≤ t → ‖x t - xs t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - xs s‖ := by
  obtain ⟨K0, β0, hβ0, hΦ⟩ := uniformlyExponentiallyStable_of_spectralRadius_lt_one hJc hJp hT hsr
  set K1 := |K0| + 1 with hK1
  have hK1p : 0 < K1 := by positivity
  have hΦ1 : ∀ s t, s ≤ t → ‖transition J t s‖ ≤ K1 * Real.exp (-(β0 * (t - s))) := fun s t h =>
    (hΦ s t h).trans (mul_le_mul_of_nonneg_right (by rw [hK1]; linarith [le_abs_self K0])
      (Real.exp_pos _).le)
  set η := min ρ (β0 / (2 * (K1 * L + 1))) with hηd
  have hη : 0 < η := lt_min hρ (by positivity)
  have hηρ : η ≤ ρ := min_le_left _ _
  have hKLη : K1 * L * η ≤ β0 / 2 := by
    have h1 : η ≤ β0 / (2 * (K1 * L + 1)) := min_le_right _ _
    have h2 : K1 * L * η ≤ (K1 * L + 1) * η := by nlinarith
    have h3 : (K1 * L + 1) * η ≤ β0 / 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (K1 * L + 1))] at h1
      nlinarith
    linarith
  refine ⟨η / (2 * K1), K1, β0 / 2, by positivity, by positivity, fun s x hx hδ => ?_⟩
  have hest : ∀ t, s ≤ t → (∀ τ ∈ Icc s t, ‖x τ - xs τ‖ ≤ η) →
      ‖x t - xs t‖ ≤ K1 * Real.exp (-(β0 / 2 * (t - s))) * ‖x s - xs s‖ := by
    intro t hst hbd
    have h := deviation_estimate hJc hxs hGc hK1p.le hL hη.le hηρ hΦ1 hR hx hst hbd
    refine h.trans ?_
    have hexp : Real.exp ((K1 * L * η - β0) * (t - s)) ≤ Real.exp (-(β0 / 2 * (t - s))) :=
      Real.exp_le_exp.2 (by nlinarith)
    calc K1 * ‖x s - xs s‖ * Real.exp ((K1 * L * η - β0) * (t - s)) ≤
          K1 * ‖x s - xs s‖ * Real.exp (-(β0 / 2 * (t - s))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  have hsmall : K1 * ‖x s - xs s‖ < η := by
    have : K1 * ‖x s - xs s‖ ≤ K1 * (η / (2 * K1)) := mul_le_mul_of_nonneg_left hδ hK1p.le
    rw [show K1 * (η / (2 * K1)) = η / 2 by field_simp] at this
    linarith
  have hxsc : Continuous xs := continuous_iff_continuousAt.2 fun t => (hxs t).continuousAt
  have hall : ∀ t, s ≤ t → ‖x t - xs t‖ ≤ η := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t1, hst1, ht1⟩ := hcon
    have hec : ContinuousOn (fun τ => ‖x τ - xs τ‖) (Icc s t1) :=
      ((hx.continuousOn.mono Icc_subset_Ici_self).sub hxsc.continuousOn).norm
    set A := Icc s t1 ∩ (fun τ => ‖x τ - xs τ‖) ⁻¹' Ici η with hA
    have hAc : IsClosed A := hec.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hAne : A.Nonempty := ⟨t1, ⟨hst1, le_rfl⟩, ht1.le⟩
    have hAb : BddBelow A := ⟨s, fun τ hτ => hτ.1.1⟩
    set τ0 := sInf A with hτ0
    have hτ0A : τ0 ∈ A := hAc.csInf_mem hAne hAb
    have hs0 : ‖x s - xs s‖ < η := by
      have : ‖x s - xs s‖ ≤ K1 * ‖x s - xs s‖ := le_mul_of_one_le_left (norm_nonneg _)
        (by rw [hK1]; linarith [abs_nonneg K0])
      linarith
    have hsτ0 : s < τ0 := by
      rcases eq_or_lt_of_le hτ0A.1.1 with h | h
      · exfalso; have := hτ0A.2; rw [← h] at this; simp at this; linarith
      · exact h
    have hbelow : ∀ τ ∈ Ico s τ0, ‖x τ - xs τ‖ ≤ η := by
      intro τ hτ
      by_contra hc
      push Not at hc
      have hτA : τ ∈ A := ⟨⟨hτ.1, hτ.2.le.trans hτ0A.1.2⟩, hc.le⟩
      have := csInf_le hAb hτA
      linarith [hτ.2]
    have hbd : ∀ τ ∈ Icc s τ0, ‖x τ - xs τ‖ ≤ η := by
      have hcl : IsClosed (Icc s τ0 ∩ (fun τ => ‖x τ - xs τ‖) ⁻¹' Iic η) :=
        (hec.mono (Icc_subset_Icc_right hτ0A.1.2)).preimage_isClosed_of_isClosed isClosed_Icc
          isClosed_Iic
      have hsub : Ico s τ0 ⊆ Icc s τ0 ∩ (fun τ => ‖x τ - xs τ‖) ⁻¹' Iic η := fun τ hτ =>
        ⟨Ico_subset_Icc_self hτ, hbelow τ hτ⟩
      have hcls := closure_minimal hsub hcl
      rw [closure_Ico hsτ0.ne] at hcls
      exact fun τ hτ => (hcls hτ).2
    have h1 := hest τ0 hτ0A.1.1 hbd
    have h2 : K1 * Real.exp (-(β0 / 2 * (τ0 - s))) * ‖x s - xs s‖ ≤ K1 * ‖x s - xs s‖ := by
      have hE : Real.exp (-(β0 / 2 * (τ0 - s))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      calc K1 * Real.exp (-(β0 / 2 * (τ0 - s))) * ‖x s - xs s‖ =
            K1 * ‖x s - xs s‖ * Real.exp (-(β0 / 2 * (τ0 - s))) := by ring
        _ ≤ K1 * ‖x s - xs s‖ * 1 := mul_le_mul_of_nonneg_left hE (by positivity)
        _ = K1 * ‖x s - xs s‖ := mul_one _
    have h3 := hτ0A.2
    simp only [mem_preimage, mem_Ici] at h3
    linarith
  exact fun t hst => hest t hst fun τ hτ => hall τ hτ.1

end powerlib.Periodic
