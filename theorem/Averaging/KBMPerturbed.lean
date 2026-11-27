import theorem.Averaging.KBM
import theorem.ParametricResonance.DuffingMathieu

/-! # First-order periodic averaging with a perturbation, on bounded sets

The first-order averaging theorem of `theorem/Averaging/KBM.lean` extended in two directions at
once: the system carries a perturbation of higher order, `ẋ = ε f(x, t) + q(t)` with
`‖q(t)‖ ≤ ε η` (in particular `q = ε² r(x, t)` or `q = ε^{1+κ} r(x, t)`), and the hypotheses on the
field are needed only on a set `U` that contains a tube of radius `ρ` around the averaged
solution. The error is `(C₁ ε + L η) e^{ℓL}` on `[0, L/ε]` with KBM's constant
`C₁ = 2ℓMLT + 2MT`: for `q = ε² r`, `‖r‖ ≤ M_r` on `U`, it is `(C₁ + L M_r) e^{ℓL} ε`, for
`q = ε^{1+κ} r` it is `(C₁ + L M_r) e^{ℓL} ε^{min(1, κ)}` (`0 < ε ≤ 1`). No engineering model is
fixed here.

Scope.
* `ẋ = ε f(x, t) + q(t)` on a real Banach space `E`, on the window `[0, L/ε]` (one-sided
  derivatives within the window), `ε > 0`, `L ≥ 0`. The perturbation `q` is an arbitrary function
  of time; a state-dependent `ε² r(x(t), t)` (possibly depending on `ε`) is the case
  `q(t) = ε² r(x(t), t)`.
* Global version (`kbm_perturbed`): `f` satisfies the hypotheses of `Averaging.kbm_first_order`
  (written out as the single hypothesis `hf`), the averaged solution `x̄̇ = ε f̄(x̄)` is a global
  solution, and `‖q‖ ≤ εη` on the window.
* Domain-restricted version (`kbm_perturbed_local`): the true field `f` agrees on a set `U` with a
  field `g` satisfying the global hypotheses (a cut-off of `f`, e.g.
  `ParametricResonance.DuffingMathieu.cutField`); the averaged solution of `f` is given on the
  window only and its closed `ρ`-tube lies in `U`; the perturbation is bounded only while the
  solution has stayed in `U` (`x(s) ∈ U` for `s ∈ [0, t]`, a bound that may use the history,
  e.g. of an implicitly defined state); and the error bound is smaller than `ρ`. Then the
  solution never leaves the tube (a first-exit-time argument) and the global estimate applies.
* Generic mathematics, no model family.

Source: work-sync theory/T-averaging-method.md §1.1–1.3 (standard form, averaged field, KBM
first-order theorem `‖x(t) − x̄(t)‖ ≤ Cε` on `[0, L/ε]`), §1.8 (validity on bounded sets);
Sanders–Verhulst–Murdock, *Averaging Methods in Nonlinear Dynamical Systems*, Ch. 2 (first-order
periodic averaging with an `O(ε²)` remainder, Grönwall's lemma); the KBM theorem
`Averaging.kbm_first_order` and the oscillation bound `Averaging.norm_integral_osc_le`.

Sharpenings.
* `theorem/Averaging/KBM.lean` lists the domain-restricted theorem as not formalized; it is
  proved here generically (`kbm_perturbed_local`), with the perturbation, for any cut-off `g`;
  `ParametricResonance.DuffingMathieu.averaging_valid` is the case of the van der Pol field
  without perturbation.
* The perturbation enters the error only through `L η e^{ℓL}`, with `η` the bound of `q/ε`:
  an `O(ε²)` perturbation keeps the `O(ε)` error, an `O(ε^{1+κ})` one gives `O(ε^{min(1, κ)})`.

Results.
* `kbm_perturbed` — global: `‖x(t) − x̄(t)‖ ≤ (C₁ ε + L η) e^{ℓL}` on `[0, L/ε]` for
  `ẋ = ε f(x, t) + q(t)`, `‖q‖ ≤ εη` (for `η = 0` the bound of `Averaging.kbm_first_order`).
* `kbm_perturbed_local` — the same bound when `f = g` only on `U`, the `ρ`-tube of `x̄` lies in
  `U`, `‖q(t)‖ ≤ εη` whenever `x` has stayed in `U` up to `t`, and the bound is `< ρ`.
* `kbm_perturbed_sq` — `ẋ = ε f(x, t) + ε² r(x, t)`, `‖r‖ ≤ M_r` on `U`:
  `‖x(t) − x̄(t)‖ ≤ (C₁ + L M_r) e^{ℓL} ε`.
* `kbm_perturbed_order` — `ẋ = ε f(x, t) + ε^{1+κ} r(x, t)`, `0 < ε ≤ 1` (any real `κ`):
  `‖x(t) − x̄(t)‖ ≤ (C₁ + L M_r) e^{ℓL} ε^{min(1, κ)}`.
-/

noncomputable section
namespace powerlib.Averaging

open Set Filter Topology intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {f g : E → ℝ → E} {T ℓ M : ℝ}

@[tmio T, powerlib_foundation] private theorem exp_sub_one_le_mul_exp (a : ℝ) :
    Real.exp a - 1 ≤ a * Real.exp a := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-a)) (Real.exp_pos a).le
  have h2 : Real.exp (-a) * Real.exp a = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  nlinarith

/-- **First-order averaging with a perturbation.** For `ẋ = ε f(x, t) + q(t)` on `[0, L/ε]` with
`‖q(t)‖ ≤ ε η` there, `f` as in `Averaging.kbm_first_order`, `x̄` the averaged solution and
`x(0) = x̄(0)`: `‖x(t) − x̄(t)‖ ≤ ((2ℓMLT + 2MT) ε + L η) e^{ℓL}` for every `t ∈ [0, L/ε]`.
(Grönwall applied to `x − x̄ − ε∫₀ᵗ g` as in KBM, with the extra source `εη`, and
`(e^{ℓL} − 1)/ℓ ≤ L e^{ℓL}`.) -/
@[tmio T, powerlib_foundation] theorem kbm_perturbed
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M) {ε L η : ℝ}
    (hε : 0 < ε) (hL : 0 ≤ L) {x xbar q : ℝ → E}
    (hx : ∀ t ∈ Icc 0 (L / ε), HasDerivWithinAt x (ε • f (x t) t + q t) (Icc 0 (L / ε)) t)
    (hq : ∀ t ∈ Icc 0 (L / ε), ‖q t‖ ≤ ε * η)
    (hxbar : ∀ t, HasDerivAt xbar (ε • fieldAverage f T (xbar t)) t) (h0 : x 0 = xbar 0) :
    ∀ t ∈ Icc 0 (L / ε),
      ‖x t - xbar t‖ ≤ ((2 * ℓ * M * L * T + 2 * M * T) * ε + L * η) * Real.exp (ℓ * L) := by
  have hcbar : Continuous xbar := continuous_iff_continuousAt.mpr fun t => (hxbar t).continuousAt
  have hg := oscPart_continuous hf hcbar
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 (xbar 0) 0)
  have hℓ := hf.2.1
  have hb : (0 : ℝ) ≤ L / ε := div_nonneg hL hε.le
  have hη : 0 ≤ η := by nlinarith [norm_nonneg (q 0), hq 0 ⟨le_rfl, hb⟩]
  set C₁ := 2 * ℓ * M * L * T + 2 * M * T with hC₁def
  have hC₁ : 0 ≤ C₁ := by have := hf.1; positivity
  set R : ℝ → E := fun t => ε • ∫ s in (0 : ℝ)..t, oscPart f T xbar s with hRdef
  have hR : ∀ t, HasDerivAt R (ε • oscPart f T xbar t) t :=
    fun t => (hg.integral_hasStrictDerivAt 0 t).hasDerivAt.const_smul ε
  have hRb : ∀ t ∈ Icc 0 (L / ε), ‖R t‖ ≤ ε * C₁ := by
    intro t ht
    have htL : ε * t ≤ L := by
      have := ht.2; rw [le_div_iff₀ hε] at this; linarith
    simp only [R, norm_smul, Real.norm_of_nonneg hε.le]
    exact mul_le_mul_of_nonneg_left (norm_integral_osc_le hf hε hxbar ht.1 htL) hε.le
  set w : ℝ → E := fun t => (x t - xbar t) - R t with hwdef
  have hw : ∀ t ∈ Icc 0 (L / ε),
      HasDerivWithinAt w (ε • (f (x t) t - f (xbar t) t) + q t) (Icc 0 (L / ε)) t := by
    intro t ht
    have h := ((hx t ht).sub (hxbar t).hasDerivWithinAt).sub (hR t).hasDerivWithinAt
    convert h using 1
    simp only [oscPart, smul_sub]; abel
  have hw0 : w 0 = 0 := by simp [w, R, h0]
  have hwc : ContinuousOn w (Icc 0 (L / ε)) := fun t ht => (hw t ht).continuousWithinAt
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := w)
    (f' := fun t => ε • (f (x t) t - f (xbar t) t) + q t) (δ := 0) (K := ε * ℓ)
    (ε := ε * ℓ * (ε * C₁) + ε * η) (a := 0) (b := L / ε) hwc
    (fun t ht => (hw t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (by simp [hw0])
    (fun t ht => by
      have ht' := Ico_subset_Icc_self ht
      have h1 := hf.2.2.2.2.1 (x t) (xbar t) t
      have h2 : ‖x t - xbar t‖ ≤ ‖w t‖ + ‖R t‖ := by
        have : x t - xbar t = w t + R t := by simp [w]
        rw [this]; exact norm_add_le _ _
      have h3 := hRb t ht'
      calc ‖ε • (f (x t) t - f (xbar t) t) + q t‖
          ≤ ‖ε • (f (x t) t - f (xbar t) t)‖ + ‖q t‖ := norm_add_le _ _
        _ ≤ ε * (ℓ * ‖x t - xbar t‖) + ε * η := by
            rw [norm_smul, Real.norm_of_nonneg hε.le]
            exact add_le_add (mul_le_mul_of_nonneg_left h1 hε.le) (hq t ht')
        _ ≤ ε * (ℓ * (‖w t‖ + ε * C₁)) + ε * η := by gcongr; linarith
        _ = ε * ℓ * ‖w t‖ + (ε * ℓ * (ε * C₁) + ε * η) := by ring)
  have hwb : ∀ t ∈ Icc 0 (L / ε),
      ‖w t‖ ≤ ε * C₁ * (Real.exp (ℓ * L) - 1) + L * η * Real.exp (ℓ * L) := by
    intro t ht
    have h := hgr t ht
    rw [sub_zero] at h
    have htL : ε * t ≤ L := by have := ht.2; rw [le_div_iff₀ hε] at this; linarith
    rcases eq_or_lt_of_le hℓ with hℓ0 | hℓpos
    · rw [← hℓ0] at h ⊢
      simp only [mul_zero, zero_mul, gronwallBound_K0, zero_add, Real.exp_zero, sub_self,
        mul_one] at h ⊢
      calc ‖w t‖ ≤ ε * η * t := h
        _ = η * (ε * t) := by ring
        _ ≤ η * L := mul_le_mul_of_nonneg_left htL hη
        _ = L * η := by ring
    · rw [gronwallBound_of_K_ne_0 (by positivity)] at h
      simp only [zero_mul, zero_add] at h
      have hratio : (ε * ℓ * (ε * C₁) + ε * η) / (ε * ℓ) = ε * C₁ + η / ℓ := by
        field_simp
      rw [hratio] at h
      have hexp : Real.exp (ε * ℓ * t) ≤ Real.exp (ℓ * L) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hkey : (Real.exp (ℓ * L) - 1) / ℓ ≤ L * Real.exp (ℓ * L) := by
        rw [div_le_iff₀ hℓpos]
        have := exp_sub_one_le_mul_exp (ℓ * L)
        linarith
      calc ‖w t‖ ≤ (ε * C₁ + η / ℓ) * (Real.exp (ε * ℓ * t) - 1) := h
        _ ≤ (ε * C₁ + η / ℓ) * (Real.exp (ℓ * L) - 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = ε * C₁ * (Real.exp (ℓ * L) - 1) + η * ((Real.exp (ℓ * L) - 1) / ℓ) := by ring
        _ ≤ ε * C₁ * (Real.exp (ℓ * L) - 1) + η * (L * Real.exp (ℓ * L)) := by gcongr
        _ = ε * C₁ * (Real.exp (ℓ * L) - 1) + L * η * Real.exp (ℓ * L) := by ring
  intro t ht
  have : x t - xbar t = w t + R t := by simp [w]
  rw [this]
  calc ‖w t + R t‖ ≤ ‖w t‖ + ‖R t‖ := norm_add_le _ _
    _ ≤ (ε * C₁ * (Real.exp (ℓ * L) - 1) + L * η * Real.exp (ℓ * L)) + ε * C₁ :=
        add_le_add (hwb t ht) (hRb t ht)
    _ = (C₁ * ε + L * η) * Real.exp (ℓ * L) := by ring

/-- **First-order averaging with a perturbation, on a bounded set.** Let `g` satisfy the
hypotheses of `Averaging.kbm_first_order` and agree with the field `f` on `U`. Let `x̄` solve the
averaged equation `x̄̇ = ε f̄(x̄)` of `f` on `[0, L/ε]` with its closed `ρ`-tube inside `U`, and
let `x` solve `ẋ = ε f(x, t) + q(t)` there with `x(0) = x̄(0)` and `‖q(t)‖ ≤ εη` whenever
`x(s) ∈ U` for all `s ∈ [0, t]`. If `B = ((2ℓMLT + 2MT) ε + L η) e^{ℓL} < ρ`, then
`‖x(t) − x̄(t)‖ ≤ B` on `[0, L/ε]` (in particular `x` stays in `U`). -/
@[tmio T, powerlib_foundation] theorem kbm_perturbed_local
    (hg : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry g) ∧ (∀ x t, g x (t + T) = g x t) ∧
      (∀ x y t, ‖g x t - g y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖g x t‖ ≤ M)
    {U : Set E} (hfg : ∀ y ∈ U, ∀ t, f y t = g y t) {ε L η ρ : ℝ} (hε : 0 < ε) (hL : 0 ≤ L)
    (hη : 0 ≤ η) {x xbar q : ℝ → E}
    (hx : ∀ t ∈ Icc 0 (L / ε), HasDerivWithinAt x (ε • f (x t) t + q t) (Icc 0 (L / ε)) t)
    (hq : ∀ t ∈ Icc 0 (L / ε), (∀ s ∈ Icc 0 t, x s ∈ U) → ‖q t‖ ≤ ε * η)
    (hxbar : ∀ t ∈ Icc 0 (L / ε),
      HasDerivWithinAt xbar (ε • fieldAverage f T (xbar t)) (Icc 0 (L / ε)) t)
    (hU : ∀ t ∈ Icc 0 (L / ε), ∀ y, ‖y - xbar t‖ ≤ ρ → y ∈ U) (h0 : x 0 = xbar 0)
    (hsmall : ((2 * ℓ * M * L * T + 2 * M * T) * ε + L * η) * Real.exp (ℓ * L) < ρ) :
    ∀ t ∈ Icc 0 (L / ε),
      ‖x t - xbar t‖ ≤ ((2 * ℓ * M * L * T + 2 * M * T) * ε + L * η) * Real.exp (ℓ * L) := by
  set b := L / ε with hbdef
  have hb : 0 ≤ b := div_nonneg hL hε.le
  have hℓ := hg.2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hg.2.2.2.2.2 (xbar 0) 0)
  set B := ((2 * ℓ * M * L * T + 2 * M * T) * ε + L * η) * Real.exp (ℓ * L) with hBdef
  have hB : 0 ≤ B := by have := hg.1; positivity
  have hρ : 0 < ρ := lt_of_le_of_lt hB hsmall
  -- the averaged solution lies in `U`, where the two averaged fields agree
  have hxbarU : ∀ t ∈ Icc 0 b, xbar t ∈ U := fun t ht =>
    hU t ht _ (by rw [sub_self, norm_zero]; exact hρ.le)
  have hav : ∀ y ∈ U, fieldAverage f T y = fieldAverage g T y := by
    intro y hy
    simp only [fieldAverage]
    congr 1
    exact intervalIntegral.integral_congr fun s _ => hfg y hy s
  -- a global solution of the averaged cut-off system agreeing with `x̄` on the window
  have hlipa : ∀ _t : ℝ, LipschitzWith (Real.toNNReal (ε * ℓ))
      fun y => ε • fieldAverage g T y := by
    intro _
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg hε.le,
      Real.coe_toNNReal _ (mul_nonneg hε.le hℓ), mul_assoc]
    exact mul_le_mul_of_nonneg_left (fieldAverage_lipschitz hg y z) hε.le
  have hconta : Continuous (Function.uncurry fun (_ : ℝ) (y : E) => ε • fieldAverage g T y) :=
    ((fieldAverage_continuous hg).comp continuous_snd).const_smul ε
  obtain ⟨xg, hxg0, hxg⟩ :=
    ParametricResonance.DuffingMathieu.exists_global_solution hconta hlipa (xbar 0)
  have hE : EqOn xbar xg (Icc 0 b) := by
    refine ODE_solution_unique_of_mem_Icc_right (v := fun _ y => ε • fieldAverage g T y)
      (s := fun _ => univ) (fun t _ => (hlipa t).lipschitzOnWith)
      (fun t ht => (hxbar t ht).continuousWithinAt) ?_ (fun _ _ => mem_univ _)
      (fun t _ => (hxg t).continuousAt.continuousWithinAt) (fun t _ => (hxg t).hasDerivWithinAt)
      (fun _ _ => mem_univ _) hxg0.symm
    intro t ht
    have h := (hxbar t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
    rw [hav _ (hxbarU t (Ico_subset_Icc_self ht))] at h
    exact h
  have hxc : ContinuousOn x (Icc 0 b) := fun t ht => (hx t ht).continuousWithinAt
  have hxbc : ContinuousOn xbar (Icc 0 b) := fun t ht => (hxbar t ht).continuousWithinAt
  have hφc : ContinuousOn (fun t => ‖x t - xbar t‖) (Icc 0 b) := (hxc.sub hxbc).norm
  -- while `x` stays in `U` up to time `u`, the global estimate holds up to `u`
  have key : ∀ u ∈ Icc 0 b, (∀ s ∈ Icc 0 u, x s ∈ U) →
      ∀ s ∈ Icc 0 u, ‖x s - xbar s‖ ≤ B := by
    intro u hu hUu s hs
    have hu' : ε * u / ε = u := by field_simp
    have hεu : 0 ≤ ε * u := mul_nonneg hε.le hu.1
    have hsub : Icc 0 u ⊆ Icc 0 b := Icc_subset_Icc le_rfl hu.2
    have hk := kbm_perturbed hg hε hεu (x := x) (xbar := xg) (q := q) (η := η)
      (fun t ht => by
        rw [hu'] at ht ⊢
        have h := (hx t (hsub ht)).mono hsub
        rw [hfg _ (hUu t ht)] at h
        exact h)
      (fun t ht => by
        rw [hu'] at ht
        exact hq t (hsub ht) fun s hs => hUu s ⟨hs.1, hs.2.trans ht.2⟩)
      hxg (by rw [h0, hxg0]) s (by rw [hu']; exact hs)
    rw [← hE (hsub hs)] at hk
    refine hk.trans ?_
    have hεuL : ε * u ≤ L := by
      have := hu.2; rw [hbdef, le_div_iff₀ hε] at this; linarith
    have := hg.1
    rw [hBdef]
    gcongr
  -- first exit from the open `ρ`-tube: there is none
  have hall : ∀ t ∈ Icc 0 b, ‖x t - xbar t‖ < ρ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t₀, ht₀, hρt₀⟩ := hcon
    set A := Icc 0 b ∩ (fun t => ‖x t - xbar t‖) ⁻¹' Ici ρ with hA
    have hAc : IsClosed A := hφc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hAne : A.Nonempty := ⟨t₀, ht₀, hρt₀⟩
    have hAbdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
    have hτA : sInf A ∈ A := hAc.csInf_mem hAne hAbdd
    have hbefore : ∀ s ∈ Icc 0 b, s < sInf A → ‖x s - xbar s‖ < ρ := by
      intro s hs hsτ
      by_contra h
      push Not at h
      exact absurd (csInf_le hAbdd ⟨hs, h⟩) (not_le.mpr hsτ)
    have hτ0 : 0 < sInf A := by
      rcases eq_or_lt_of_le hτA.1.1 with h | h
      · exfalso
        have h2 : ρ ≤ ‖x (sInf A) - xbar (sInf A)‖ := hτA.2
        rw [← h, h0, sub_self, norm_zero] at h2
        linarith
      · exact h
    have hle : ∀ u ∈ Ico 0 (sInf A), ‖x u - xbar u‖ ≤ B := by
      intro u hu
      have hub : u ∈ Icc 0 b := ⟨hu.1, hu.2.le.trans hτA.1.2⟩
      exact key u hub (fun s hs => hU s ⟨hs.1, hs.2.trans hub.2⟩ _
        (hbefore s ⟨hs.1, hs.2.trans hub.2⟩ (lt_of_le_of_lt hs.2 hu.2)).le) u ⟨hu.1, le_rfl⟩
    have hτle : ‖x (sInf A) - xbar (sInf A)‖ ≤ B := by
      have hcl : sInf A ∈ closure (Ico 0 (sInf A)) := by
        rw [closure_Ico hτ0.ne]; exact ⟨hτ0.le, le_rfl⟩
      have hcw : ContinuousWithinAt (fun t => ‖x t - xbar t‖) (Ico 0 (sInf A)) (sInf A) :=
        (hφc _ hτA.1).mono fun s hs => ⟨hs.1, hs.2.le.trans hτA.1.2⟩
      exact hcw.closure_le hcl continuousWithinAt_const hle
    have h2 : ρ ≤ ‖x (sInf A) - xbar (sInf A)‖ := hτA.2
    linarith
  intro t ht
  exact key b ⟨hb, le_rfl⟩ (fun s hs => hU s hs _ (hall s hs).le) t ht

/-- **An `O(ε²)` perturbation keeps the `O(ε)` error.** With `ẋ = ε f(x, t) + ε² r(x, t)` on
`[0, L/ε]` (`r` may depend on `ε`), `‖r(y, t)‖ ≤ M_r` for `y ∈ U`, and the other hypotheses of
`kbm_perturbed_local`: `‖x(t) − x̄(t)‖ ≤ ((2ℓMLT + 2MT) + L M_r) e^{ℓL} ε` on `[0, L/ε]`, whenever
this bound is `< ρ`. -/
@[tmio T, powerlib_foundation] theorem kbm_perturbed_sq
    (hg : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry g) ∧ (∀ x t, g x (t + T) = g x t) ∧
      (∀ x y t, ‖g x t - g y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖g x t‖ ≤ M)
    {U : Set E} (hfg : ∀ y ∈ U, ∀ t, f y t = g y t) {r : E → ℝ → E} {Mr : ℝ} (hMr : 0 ≤ Mr)
    (hr : ∀ y ∈ U, ∀ t, ‖r y t‖ ≤ Mr) {ε L ρ : ℝ} (hε : 0 < ε) (hL : 0 ≤ L) {x xbar : ℝ → E}
    (hx : ∀ t ∈ Icc 0 (L / ε),
      HasDerivWithinAt x (ε • f (x t) t + ε ^ 2 • r (x t) t) (Icc 0 (L / ε)) t)
    (hxbar : ∀ t ∈ Icc 0 (L / ε),
      HasDerivWithinAt xbar (ε • fieldAverage f T (xbar t)) (Icc 0 (L / ε)) t)
    (hU : ∀ t ∈ Icc 0 (L / ε), ∀ y, ‖y - xbar t‖ ≤ ρ → y ∈ U) (h0 : x 0 = xbar 0)
    (hsmall : ((2 * ℓ * M * L * T + 2 * M * T) + L * Mr) * Real.exp (ℓ * L) * ε < ρ) :
    ∀ t ∈ Icc 0 (L / ε),
      ‖x t - xbar t‖ ≤ ((2 * ℓ * M * L * T + 2 * M * T) + L * Mr) * Real.exp (ℓ * L) * ε := by
  have e : ((2 * ℓ * M * L * T + 2 * M * T) * ε + L * (ε * Mr)) * Real.exp (ℓ * L) =
      ((2 * ℓ * M * L * T + 2 * M * T) + L * Mr) * Real.exp (ℓ * L) * ε := by ring
  have h := kbm_perturbed_local hg hfg hε hL (mul_nonneg hε.le hMr)
    (q := fun t => ε ^ 2 • r (x t) t) hx (fun t ht hxt => by
      rw [norm_smul, Real.norm_of_nonneg (by positivity), sq, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hr _ (hxt t ⟨ht.1, le_rfl⟩) t) hε.le) hε.le)
    hxbar hU h0 (by rw [e]; exact hsmall)
  intro t ht
  rw [← e]
  exact h t ht

/-- **An `O(ε^{1+κ})` perturbation gives an `O(ε^{min(1, κ)})` error.** With
`ẋ = ε f(x, t) + ε^{1+κ} r(x, t)` on `[0, L/ε]`, `0 < ε ≤ 1` (any real `κ`; the case `κ > 0` is
the perturbation of higher order), `‖r(y, t)‖ ≤ M_r` for
`y ∈ U`, and the other hypotheses of `kbm_perturbed_local`:
`‖x(t) − x̄(t)‖ ≤ ((2ℓMLT + 2MT) + L M_r) e^{ℓL} ε^{min(1, κ)}` on `[0, L/ε]`, whenever this bound
is `< ρ`. -/
@[tmio T, powerlib_foundation] theorem kbm_perturbed_order
    (hg : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry g) ∧ (∀ x t, g x (t + T) = g x t) ∧
      (∀ x y t, ‖g x t - g y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖g x t‖ ≤ M)
    {U : Set E} (hfg : ∀ y ∈ U, ∀ t, f y t = g y t) {r : E → ℝ → E} {Mr : ℝ} (hMr : 0 ≤ Mr)
    (hr : ∀ y ∈ U, ∀ t, ‖r y t‖ ≤ Mr) {ε L ρ κ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hL : 0 ≤ L)
    {x xbar : ℝ → E}
    (hx : ∀ t ∈ Icc 0 (L / ε),
      HasDerivWithinAt x (ε • f (x t) t + ε ^ (1 + κ) • r (x t) t) (Icc 0 (L / ε)) t)
    (hxbar : ∀ t ∈ Icc 0 (L / ε),
      HasDerivWithinAt xbar (ε • fieldAverage f T (xbar t)) (Icc 0 (L / ε)) t)
    (hU : ∀ t ∈ Icc 0 (L / ε), ∀ y, ‖y - xbar t‖ ≤ ρ → y ∈ U) (h0 : x 0 = xbar 0)
    (hsmall : ((2 * ℓ * M * L * T + 2 * M * T) + L * Mr) * Real.exp (ℓ * L) * ε ^ min 1 κ < ρ) :
    ∀ t ∈ Icc 0 (L / ε), ‖x t - xbar t‖ ≤
      ((2 * ℓ * M * L * T + 2 * M * T) + L * Mr) * Real.exp (ℓ * L) * ε ^ min 1 κ := by
  have hℓ := hg.2.1
  have hT := hg.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hg.2.2.2.2.2 0 0)
  have h1 : ε ≤ ε ^ min 1 κ := by
    calc ε = ε ^ (1 : ℝ) := (Real.rpow_one ε).symm
      _ ≤ ε ^ min 1 κ := Real.rpow_le_rpow_of_exponent_ge hε hε1 (min_le_left _ _)
  have h2 : ε ^ κ ≤ ε ^ min 1 κ := Real.rpow_le_rpow_of_exponent_ge hε hε1 (min_le_right _ _)
  have hB : ((2 * ℓ * M * L * T + 2 * M * T) * ε + L * (ε ^ κ * Mr)) * Real.exp (ℓ * L) ≤
      ((2 * ℓ * M * L * T + 2 * M * T) + L * Mr) * Real.exp (ℓ * L) * ε ^ min 1 κ := by
    have hC : 0 ≤ 2 * ℓ * M * L * T + 2 * M * T := by positivity
    have hLM : 0 ≤ L * Mr := mul_nonneg hL hMr
    have e : ((2 * ℓ * M * L * T + 2 * M * T) * ε + L * (ε ^ κ * Mr)) =
        (2 * ℓ * M * L * T + 2 * M * T) * ε + L * Mr * ε ^ κ := by ring
    rw [e, mul_comm _ (ε ^ min 1 κ), ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_left h1 hC, mul_le_mul_of_nonneg_left h2 hLM]
  have h := kbm_perturbed_local hg hfg hε hL (mul_nonneg (Real.rpow_nonneg hε.le κ) hMr)
    (q := fun t => ε ^ (1 + κ) • r (x t) t) hx
    (fun t ht hxt => by
      rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hε.le _), Real.rpow_add hε,
        Real.rpow_one, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (hr _ (hxt t ⟨ht.1, le_rfl⟩) t) (Real.rpow_nonneg hε.le κ)) hε.le)
    hxbar hU h0 (lt_of_le_of_lt hB hsmall)
  intro t ht
  exact (h t ht).trans hB

end powerlib.Averaging
