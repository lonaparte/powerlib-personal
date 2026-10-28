import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import theorem.Dynamics.State

/-! # Scalar calculus for the stability toolbox

Real-variable calculus used by the Lyapunov, LaSalle and degenerate-equilibrium modules of
`theorem/Dynamics/` and by the equal-area (`theorem/Synchronous/EqualArea.lean`) and PLL
port-Hamiltonian (`theorem/PLL/PH.lean`) modules.

Scope.
* Foundation results only: no model is fixed here and no behavioural sentence is stated.

Source: library infrastructure (no work-sync note); standard real analysis (Grönwall, mean-value
theorem, Taylor bounds).

Results.
* Interval induction: `forall_mem_Icc_of_local_step` (continuous induction on `[t₀, t₁]` for a
  closed target set), `exists_Icc_mem_of_isOpen` (a continuous curve stays a little while in an
  open set), `pos_on_Icc_of_propagate` (positivity that propagates along `[a, b]`),
  `forall_Icc_of_forall_Ico` (a closed upper bound on `[a, b)` extends to `b`).
* Monotonicity and mean-value bounds: `monotoneOn_Icc_of_hasDerivAt`, `sub_ge_of_deriv_ge`,
  `sub_le_of_deriv_le`, `deriv_nonpos_of_isMinOn_right`, `exists_pos_of_hasDerivAt`,
  `eventually_pos_of_hasDerivAt`, `HasDerivWithinAt.eq_zero_of_eqOn_Icc`.
* Grönwall-type scalar inequalities: `le_exp_mul_of_hasDerivWithinAt` (linear Grönwall),
  `abs_le_of_sq_le_exp` (square-root-free decay bound), `abs_sub_le_of_abs_deriv_le_exp`
  (an exponentially decaying rate gives a bounded drift), `exists_tendsto_of_abs_deriv_le_exp`
  (and a convergent limit).
* Asymptotic bookkeeping: `eventually_neg_of_isLittleO` / `eventually_pos_of_isLittleO`
  (`g = ∓q + o(q)` with `q > 0` ⇒ `g` has the sign of `∓q`), `eventually_neg_of_le_of_isLittleO`
  (`g ≤ −q + o(q)`), `isBigO_pow_of_tendsto` / `isLittleO_pow_of_tendsto` (powers of a vanishing
  size function), `isBigO_monomial` (a monomial in two `O(s)` functions is `O(s^{i+j})`),
  `frequently_of_forall_smul` (states on a ray accumulate at the origin).
* Taylor remainders at `0`: `one_sub_cos_isBigO` (`1 − cos x = O(x²)`), `sin_sub_self_isBigO`
  (`sin x − x = O(x³)`), `one_sub_cos_sub_isBigO` (`1 − cos x − x²/2 = O(x⁴)`), from Mathlib's
  `Real.sin_bound`, `Real.cos_bound`, `Real.one_sub_sq_div_two_le_cos`.
* `hasDerivAt_mulVec`: a matrix (rectangular, any finite index types) maps a differentiable
  curve to a differentiable curve, `(M x)' = M x'`.
* `firstIntegral_const`: a differentiable `I` with `∇I · f ≡ 0` is constant along every solution
  segment of `f` (LeanForControl's `antitoneOn_V_comp_traj` applied to `±I`).
-/

noncomputable section
namespace powerlib.Dynamics

/-! ## Interval induction -/

section Induction

open Set Filter Topology Metric
open scoped Pointwise

variable {n : ℕ}
local notation "ℝⁿ" => State n

/-- Continuous induction on `[t₀, t₁]` for a closed target set. -/
@[tmio T, powerlib_foundation] theorem forall_mem_Icc_of_local_step {ψ : ℝ → ℝⁿ} {Ω : Set ℝⁿ}
    {t₀ t₁ : ℝ} (hψ : ContinuousOn ψ (Icc t₀ t₁)) (hΩ : IsClosed Ω) (h0 : ψ t₀ ∈ Ω)
    (hstep : ∀ x ∈ Ico t₀ t₁, ψ x ∈ Ω → ∃ y, x < y ∧ ∀ t ∈ Ioo x y, ψ t ∈ Ω) :
    ∀ t ∈ Icc t₀ t₁, ψ t ∈ Ω := by
  have hs : IsClosed ((ψ ⁻¹' Ω) ∩ Icc t₀ t₁) := by
    rw [inter_comm]
    exact hψ.preimage_isClosed_of_isClosed isClosed_Icc hΩ
  have hsub := hs.Icc_subset_of_forall_mem_nhdsWithin (s := ψ ⁻¹' Ω) h0 (by
    rintro x ⟨hx, hxI⟩
    obtain ⟨y, hxy, hy⟩ := hstep x hxI hx
    exact mem_of_superset (Ioo_mem_nhdsGT hxy) hy)
  exact fun t ht => hsub ht

/-- A curve continuous on `[t₀, t₁]` that is in an open set at `x ∈ [t₀, t₁)` stays in it on
some `[x, y]` with `x < y ≤ t₁`. -/
@[tmio T, powerlib_foundation] theorem exists_Icc_mem_of_isOpen {ψ : ℝ → ℝⁿ} {U : Set ℝⁿ}
    {t₀ t₁ x : ℝ} (hψ : ContinuousOn ψ (Icc t₀ t₁)) (hU : IsOpen U) (hx : x ∈ Ico t₀ t₁)
    (hxU : ψ x ∈ U) : ∃ y, x < y ∧ y ≤ t₁ ∧ ∀ t ∈ Icc x y, ψ t ∈ U := by
  have hIcc : Icc t₀ t₁ ∈ 𝓝[>] x :=
    mem_of_superset (Ioo_mem_nhdsGT hx.2) fun t ht => ⟨hx.1.trans ht.1.le, ht.2.le⟩
  have hpre : ψ ⁻¹' U ∈ 𝓝[>] x :=
    nhdsWithin_le_of_mem hIcc
      ((hψ x (Ico_subset_Icc_self hx)).preimage_mem_nhdsWithin (hU.mem_nhds hxU))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hpre
  have hxu : x < u := hu
  refine ⟨min ((x + u) / 2) t₁, lt_min (by linarith) hx.2, min_le_right _ _, ?_⟩
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | hlt
  · exact hxU
  · apply hsub
    exact ⟨hlt, lt_of_le_of_lt (ht.2.trans (min_le_left _ _)) (by linarith)⟩

end Induction

section Propagate

open Set Filter Topology

/-- If `g` is continuous on `[a, b]`, `g a > 0`, and positivity on `[a, t)` always propagates to
`t`, then `g > 0` on `[a, b]`. -/
@[tmio T, powerlib_foundation] theorem pos_on_Icc_of_propagate {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Icc a b)) (ha : 0 < g a)
    (h : ∀ t ∈ Ioc a b, (∀ s ∈ Ico a t, 0 < g s) → 0 < g t) :
    ∀ t ∈ Icc a b, 0 < g t := by
  by_contra hne
  push Not at hne
  obtain ⟨t₁, ht₁, hgt₁⟩ := hne
  set S := Icc a b ∩ g ⁻¹' Iic 0 with hSdef
  have hS : IsClosed S := hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := ⟨t₁, ht₁, hgt₁⟩
  have hbdd : BddBelow S := ⟨a, fun x hx => hx.1.1⟩
  have hmem : sInf S ∈ S := hS.csInf_mem hSne hbdd
  have hle : g (sInf S) ≤ 0 := hmem.2
  have hat : a ≤ sInf S := hmem.1.1
  have hne_a : sInf S ≠ a := by
    intro he; rw [he] at hle; linarith
  have hpos : 0 < g (sInf S) := by
    refine h _ ⟨lt_of_le_of_ne hat (Ne.symm hne_a), hmem.1.2⟩ fun s hs => ?_
    by_contra hs'
    push Not at hs'
    have : sInf S ≤ s := csInf_le hbdd ⟨⟨hs.1, hs.2.le.trans hmem.1.2⟩, hs'⟩
    linarith [hs.2]
  linarith

/-- A closed upper bound on `[a, b)` extends to `b`. -/
@[tmio T, powerlib_foundation] theorem forall_Icc_of_forall_Ico {F : ℝ → ℝ} {a b B : ℝ} (hab : a < b)
    (hF : ContinuousOn F (Icc a b)) (h : ∀ t ∈ Ico a b, F t ≤ B) : ∀ t ∈ Icc a b, F t ≤ B := by
  have hcl : IsClosed (Icc a b ∩ F ⁻¹' Iic B) :=
    hF.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hsub : Ico a b ⊆ Icc a b ∩ F ⁻¹' Iic B := fun t ht => ⟨Ico_subset_Icc_self ht, h t ht⟩
  have := hcl.closure_subset_iff.mpr hsub
  rw [closure_Ico hab.ne] at this
  exact fun t ht => (this ht).2

/-! ## Monotonicity and mean-value bounds -/

/-- Monotonicity on `[a, b]` from a nonnegative derivative on `(a, b)`. -/
@[tmio T, powerlib_foundation] theorem monotoneOn_Icc_of_hasDerivAt {h h' : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn h (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x)
    (hnn : ∀ x ∈ Ioo a b, 0 ≤ h' x) : MonotoneOn h (Icc a b) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hc
  · rw [interior_Icc]; exact fun x hx => (hd x hx).hasDerivWithinAt
  · rw [interior_Icc]; exact hnn

/-- Mean-value lower bound on a subinterval: a function with derivative at least `m` inside
`[c, d] ⊆ [a, b]` increases by at least `m (d − c)`. -/
@[tmio T, powerlib_foundation] theorem sub_ge_of_deriv_ge {u u' : ℝ → ℝ} {a b c d m : ℝ} (hcd : c ≤ d)
    (hca : a ≤ c) (hdb : d ≤ b) (hu : ∀ s ∈ Icc a b, HasDerivWithinAt u (u' s) (Icc a b) s)
    (hm : ∀ s ∈ Ioo c d, m ≤ u' s) : m * (d - c) ≤ u d - u c := by
  have hmono : MonotoneOn (fun s => u s - m * s) (Icc c d) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun s => u' s - m) (convex_Icc _ _)
      (fun s hs => ((hu s ⟨hca.trans hs.1, hs.2.trans hdb⟩).continuousWithinAt.mono
        (Icc_subset_Icc hca hdb)).sub (continuous_const.mul continuous_id).continuousWithinAt)
      (fun s hs => ?_) (fun s hs => ?_)
    · rw [interior_Icc] at hs
      have h1 := (hu s ⟨hca.trans hs.1.le, hs.2.le.trans hdb⟩).hasDerivAt
        (Icc_mem_nhds (lt_of_le_of_lt hca hs.1) (lt_of_lt_of_le hs.2 hdb))
      exact (h1.fun_sub ((hasDerivAt_id s).const_mul m)).hasDerivWithinAt.congr_deriv (by simp)
    · rw [interior_Icc] at hs
      linarith [hm s hs]
  have := hmono ⟨le_rfl, hcd⟩ ⟨hcd, le_rfl⟩ hcd
  simp only at this
  linarith

/-- Mean-value upper bound on a subinterval. -/
@[tmio T, powerlib_foundation] theorem sub_le_of_deriv_le {u u' : ℝ → ℝ} {a b c d m : ℝ} (hcd : c ≤ d)
    (hca : a ≤ c) (hdb : d ≤ b) (hu : ∀ s ∈ Icc a b, HasDerivWithinAt u (u' s) (Icc a b) s)
    (hm : ∀ s ∈ Ioo c d, u' s ≤ m) : u d - u c ≤ m * (d - c) := by
  have h := sub_ge_of_deriv_ge (u := fun s => -u s) (u' := fun s => -u' s) (m := -m) hcd hca hdb
    (fun s hs => (hu s hs).neg) (fun s hs => by linarith [hm s hs])
  linarith

/-- A function with derivative `d` within `[a, b]` at the right end `b`, where it is minimal on
`[a, b]`, has `d ≤ 0`. -/
@[tmio T, powerlib_foundation] theorem deriv_nonpos_of_isMinOn_right {φ : ℝ → ℝ} {d a b : ℝ} (hab : a < b)
    (hd : HasDerivWithinAt φ d (Icc a b) b) (hmin : ∀ u ∈ Icc a b, φ b ≤ φ u) : d ≤ 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Icc_sdiff_right, nhdsWithin_Ico_eq_nhdsLT hab] at hd
  refine le_of_tendsto hd ?_
  filter_upwards [Ioo_mem_nhdsLT hab] with u hu
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (by linarith [hmin u ⟨hu.1.le, hu.2.le⟩])
    (by linarith [hu.2])

/-- A function vanishing at `0` with positive derivative there is positive at some `t ∈ (0, ε)`. -/
@[tmio T, powerlib_foundation] theorem exists_pos_of_hasDerivAt {ψ : ℝ → ℝ} {d : ℝ} (hd : HasDerivAt ψ d 0)
    (h0 : ψ 0 = 0) (hpos : 0 < d) {ε : ℝ} (hε : 0 < ε) : ∃ t ∈ Ioo 0 ε, 0 < ψ t := by
  rw [hasDerivAt_iff_tendsto_slope] at hd
  have h1 : Tendsto (slope ψ 0) (𝓝[>] 0) (𝓝 d) :=
    hd.mono_left (nhdsWithin_mono _ fun t ht => ne_of_gt ht)
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < slope ψ 0 t ∧ t < ε :=
    (h1.eventually (lt_mem_nhds hpos)).and (Ioo_mem_nhdsGT hε |> fun h =>
      Filter.mem_of_superset h fun t ht => ht.2)
  obtain ⟨t, ht, ht0⟩ := (h2.and self_mem_nhdsWithin).exists
  refine ⟨t, ⟨ht0, ht.2⟩, ?_⟩
  have := ht.1
  rw [slope_def_field, h0, sub_zero, sub_zero] at this
  exact (div_pos_iff_of_pos_right ht0).mp this

/-- A function vanishing at `0` with positive derivative there is positive just to the right. -/
@[tmio T, powerlib_foundation] theorem eventually_pos_of_hasDerivAt {ψ : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt ψ d 0) (h0 : ψ 0 = 0) (hpos : 0 < d) : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < ψ t := by
  rw [hasDerivAt_iff_tendsto_slope] at hd
  have h1 : Tendsto (slope ψ 0) (𝓝[>] 0) (𝓝 d) :=
    hd.mono_left (nhdsWithin_mono _ fun t ht => ne_of_gt ht)
  filter_upwards [h1.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with t ht ht0
  rw [slope_def_field, h0, sub_zero, sub_zero] at ht
  exact (div_pos_iff_of_pos_right ht0).mp ht

end Propagate

/-! ## Grönwall-type scalar inequalities -/

section Gronwall

open Set Filter Topology Metric

/-- A function that is constant on a nontrivial interval `[a, b]` has derivative `0` there. -/
@[tmio T, powerlib_foundation] theorem HasDerivWithinAt.eq_zero_of_eqOn_Icc {F : ℝ → ℝ} {F' a b t c : ℝ}
    (hab : a < b) (ht : t ∈ Icc a b) (hF : HasDerivWithinAt F F' (Icc a b) t)
    (hc : ∀ τ ∈ Icc a b, F τ = c) : F' = 0 := by
  have h0 : HasDerivWithinAt F 0 (Icc a b) t :=
    (hasDerivWithinAt_const t (Icc a b) c).congr (fun τ hτ => hc τ hτ) (hc t ht)
  exact (uniqueDiffOn_Icc hab t ht).eq_deriv _ hF h0

@[tmio T] private theorem hasDerivAt_exp_lin (c t₀ t : ℝ) :
    HasDerivAt (fun τ => Real.exp (c * (τ - t₀))) (c * Real.exp (c * (t - t₀))) t := by
  have h := (Real.hasDerivAt_exp (c * (t - t₀))).comp t
    (((hasDerivAt_id t).sub_const t₀).const_mul c)
  rw [show (fun τ => Real.exp (c * (τ - t₀))) = Real.exp ∘ fun y => c * (id y - t₀) from rfl]
  convert h using 1
  ring

/-- **Grönwall's inequality, linear form.** If `g' ≤ −ρ g` on `[t₀, t₁]`, then
`g t ≤ e^{−ρ (t − t₀)} g t₀` there. -/
@[tmio T, powerlib_foundation] theorem le_exp_mul_of_hasDerivWithinAt {g g' : ℝ → ℝ} {ρ t₀ t₁ : ℝ}
    (hg : ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt g (g' t) (Icc t₀ t₁) t)
    (hle : ∀ t ∈ Icc t₀ t₁, g' t ≤ -ρ * g t) :
    ∀ t ∈ Icc t₀ t₁, g t ≤ Real.exp (-ρ * (t - t₀)) * g t₀ := by
  set h : ℝ → ℝ := fun t => Real.exp (ρ * (t - t₀)) * g t with hh
  have hd : ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt h
      (ρ * Real.exp (ρ * (t - t₀)) * g t + Real.exp (ρ * (t - t₀)) * g' t) (Icc t₀ t₁) t :=
    fun t ht => ((hasDerivAt_exp_lin ρ t₀ t).hasDerivWithinAt.mul (hg t ht))
  have hanti : AntitoneOn h (Icc t₀ t₁) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun t ht => (hd t ht).continuousWithinAt) (fun t ht =>
        (hd t (interior_subset ht)).mono interior_subset) (fun t ht => ?_)
    have h1 := hle t (interior_subset ht)
    have h2 := Real.exp_pos (ρ * (t - t₀))
    nlinarith
  intro t ht
  have h1 := hanti ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  simp only [hh, sub_self, mul_zero, Real.exp_zero, one_mul] at h1
  have h2 : Real.exp (-ρ * (t - t₀)) * Real.exp (ρ * (t - t₀)) = 1 := by
    rw [← Real.exp_add]
    simp
  have h3 := Real.exp_pos (-ρ * (t - t₀))
  calc g t = Real.exp (-ρ * (t - t₀)) * (Real.exp (ρ * (t - t₀)) * g t) := by
        rw [← mul_assoc, h2, one_mul]
    _ ≤ Real.exp (-ρ * (t - t₀)) * g t₀ := mul_le_mul_of_nonneg_left h1 h3.le

/-- `|x| ≤ (c/λ + λ)/2 · e^{−β s}` whenever `x² ≤ c e^{−2β s}` and `λ > 0` (arithmetic-geometric
mean with the weight `λ e^{−β s}`; no square roots). -/
@[tmio T, powerlib_foundation] theorem abs_le_of_sq_le_exp {x c l β s : ℝ} (hl : 0 < l)
    (hx : x ^ 2 ≤ c * Real.exp (-(2 * β) * s)) :
    |x| ≤ (c / l + l) / 2 * Real.exp (-β * s) := by
  set e := Real.exp (-β * s) with he
  have he0 : 0 < e := Real.exp_pos _
  have he2 : Real.exp (-(2 * β) * s) = e ^ 2 := by
    rw [he, sq, ← Real.exp_add]
    ring_nf
  rw [he2] at hx
  have hw : 0 < l * e := mul_pos hl he0
  have key : 2 * (l * e) * |x| ≤ x ^ 2 + (l * e) ^ 2 := by
    nlinarith [sq_nonneg (|x| - l * e), sq_abs x]
  have key2 : x ^ 2 + (l * e) ^ 2 ≤ (c + l ^ 2) * e ^ 2 := by nlinarith
  have : (c / l + l) / 2 * e = (c + l ^ 2) * e ^ 2 / (2 * (l * e)) := by
    field_simp
  rw [this, le_div_iff₀ (by positivity)]
  nlinarith

/-- **Bounded drift.** If `|θ'| ≤ A e^{−b (t − t₀)}` on `[t₀, t₁]` with `b > 0`, then
`|θ t − θ t₀| ≤ A / b` there. -/
@[tmio T, powerlib_foundation] theorem abs_sub_le_of_abs_deriv_le_exp {θ θ' : ℝ → ℝ} {A b t₀ t₁ : ℝ}
    (hb : 0 < b) (hθ : ∀ t ∈ Icc t₀ t₁, HasDerivWithinAt θ (θ' t) (Icc t₀ t₁) t)
    (hle : ∀ t ∈ Icc t₀ t₁, |θ' t| ≤ A * Real.exp (-b * (t - t₀))) :
    ∀ t ∈ Icc t₀ t₁, |θ t - θ t₀| ≤ A / b := by
  intro t ht
  have ht₀ : t₀ ∈ Icc t₀ t₁ := ⟨le_rfl, ht.1.trans ht.2⟩
  have hA : 0 ≤ A := by
    have := (abs_nonneg _).trans (hle t₀ ht₀)
    simpa using this
  -- `±θ + (A/b) e^{−b (t − t₀)}` is antitone
  have side : ∀ σ : ℝ, σ = 1 ∨ σ = -1 → σ * (θ t - θ t₀) ≤ A / b := by
    intro σ hσ
    set F : ℝ → ℝ := fun τ => σ * θ τ + A / b * Real.exp (-b * (τ - t₀)) with hF
    have hd : ∀ τ ∈ Icc t₀ t₁, HasDerivWithinAt F
        (σ * θ' τ + A / b * (-b * Real.exp (-b * (τ - t₀)))) (Icc t₀ t₁) τ :=
      fun τ hτ => ((hθ τ hτ).const_mul σ).add
        ((hasDerivAt_exp_lin (-b) t₀ τ).hasDerivWithinAt.const_mul (A / b))
    have hanti : AntitoneOn F (Icc t₀ t₁) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
        (fun τ hτ => (hd τ hτ).continuousWithinAt) (fun τ hτ =>
          (hd τ (interior_subset hτ)).mono interior_subset) (fun τ hτ => ?_)
      have h1 := hle τ (interior_subset hτ)
      have h2 : σ * θ' τ ≤ |θ' τ| := by
        rcases hσ with rfl | rfl
        · simpa using le_abs_self (θ' τ)
        · simpa using neg_le_abs (θ' τ)
      have h3 : A / b * (-b * Real.exp (-b * (τ - t₀))) = -(A * Real.exp (-b * (τ - t₀))) := by
        field_simp
      rw [h3]
      linarith
    have h1 := hanti ht₀ ht ht.1
    simp only [hF, sub_self, mul_zero, Real.exp_zero, mul_one] at h1
    have h2 : 0 ≤ A / b * Real.exp (-b * (t - t₀)) := by positivity
    linarith
  rw [abs_le]
  constructor
  · have := side (-1) (Or.inr rfl)
    linarith
  · have := side 1 (Or.inl rfl)
    linarith

/-- **Integrable drift converges.** If `|θ'| ≤ A e^{−b (t − t₀)}` on `[t₀, ∞)` with `b > 0`, then
`θ` converges. -/
@[tmio T, powerlib_foundation] theorem exists_tendsto_of_abs_deriv_le_exp {θ θ' : ℝ → ℝ} {A b t₀ : ℝ}
    (hb : 0 < b) (hθ : ∀ t, t₀ ≤ t → HasDerivWithinAt θ (θ' t) (Ici t₀) t)
    (hle : ∀ t, t₀ ≤ t → |θ' t| ≤ A * Real.exp (-b * (t - t₀))) :
    ∃ L : ℝ, Tendsto θ atTop (𝓝 L) := by
  have hbound : ∀ s, t₀ ≤ s → ∀ t, s ≤ t →
      |θ t - θ s| ≤ A * Real.exp (-b * (s - t₀)) / b := by
    intro s hs t hst
    refine abs_sub_le_of_abs_deriv_le_exp (θ' := θ') hb (t₁ := t)
      (fun τ hτ => (hθ τ (hs.trans hτ.1)).mono fun r hr => hs.trans hr.1) (fun τ hτ => ?_)
      t ⟨hst, le_rfl⟩
    have h := hle τ (hs.trans hτ.1)
    have e : Real.exp (-b * (τ - t₀)) =
        Real.exp (-b * (s - t₀)) * Real.exp (-b * (τ - s)) := by
      rw [← Real.exp_add]
      ring_nf
    rw [e] at h
    linarith [h]
  have hlim : Tendsto (fun s => A * Real.exp (-b * (s - t₀)) / b) atTop (𝓝 0) := by
    have hexp : Tendsto (fun s => Real.exp (-b * (s - t₀))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp ((tendsto_atTop_atTop.2 fun c =>
        ⟨c + t₀, fun s hs => by linarith⟩).const_mul_atTop_of_neg (by linarith))
    simpa using (hexp.const_mul A).div_const b
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hlim.eventually (gt_mem_nhds hε)).and
    (eventually_ge_atTop t₀))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  exact (hbound N (hN N le_rfl).2 n hn).trans_lt (hN N le_rfl).1

end Gronwall

/-! ## Asymptotic bookkeeping -/

section Asymptotic

open Set Filter Topology Metric Asymptotics

/-- `g = −q + o(q)` with `q > 0` eventually forces `g < 0` eventually. -/
@[tmio T, powerlib_foundation] theorem eventually_neg_of_isLittleO {α : Type*} {l : Filter α}
    {g q : α → ℝ} (hq : ∀ᶠ x in l, 0 < q x) (h : (fun x => g x + q x) =o[l] q) :
    ∀ᶠ x in l, g x < 0 := by
  filter_upwards [hq, h.def (by norm_num : (0 : ℝ) < 1 / 2)] with x hqx hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hqx] at hx
  have := le_abs_self (g x + q x)
  linarith

/-- `g = q + o(q)` with `q > 0` eventually forces `g > 0` eventually. -/
@[tmio T, powerlib_foundation] theorem eventually_pos_of_isLittleO {α : Type*} {l : Filter α}
    {g q : α → ℝ} (hq : ∀ᶠ x in l, 0 < q x) (h : (fun x => g x - q x) =o[l] q) :
    ∀ᶠ x in l, 0 < g x := by
  filter_upwards [hq, h.def (by norm_num : (0 : ℝ) < 1 / 2)] with x hqx hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hqx] at hx
  have := neg_abs_le (g x - q x)
  linarith

/-- Higher powers of a vanishing function are small: `s^k = o(s^m)` for `m < k`. -/
@[tmio T, powerlib_foundation] theorem isLittleO_pow_of_tendsto {α : Type*} {l : Filter α}
    {s : α → ℝ} (hs : Tendsto s l (𝓝 0)) {m k : ℕ} (h : m < k) :
    (fun x => s x ^ k) =o[l] fun x => s x ^ m :=
  (isLittleO_pow_pow h).comp_tendsto hs

/-- Higher powers of a vanishing function are bounded by lower ones: `s^k = O(s^m)` for `m ≤ k`. -/
@[tmio T, powerlib_foundation] theorem isBigO_pow_of_tendsto {α : Type*} {l : Filter α}
    {s : α → ℝ} (hs : Tendsto s l (𝓝 0)) {m k : ℕ} (h : m ≤ k) :
    (fun x => s x ^ k) =O[l] fun x => s x ^ m := by
  rcases h.lt_or_eq with h | h
  · exact (isLittleO_pow_of_tendsto hs h).isBigO
  · rw [h]

/-- A monomial in two functions that are `O(s)` is `O(s^{i+j})`. -/
@[tmio T, powerlib_foundation] theorem isBigO_monomial {α : Type*} {l : Filter α} {s u v : α → ℝ}
    (hu : u =O[l] s) (hv : v =O[l] s) (i j : ℕ) :
    (fun x => u x ^ i * v x ^ j) =O[l] fun x => s x ^ (i + j) := by
  have := (hu.pow i).mul (hv.pow j)
  refine this.congr_right fun x => ?_
  rw [pow_add]

/-- A sign estimate `g ≤ −q + R` with `R = o(q)` and `q > 0` forces `g < 0` eventually. -/
@[tmio T, powerlib_foundation] theorem eventually_neg_of_le_of_isLittleO {α : Type*} {l : Filter α}
    {g q R : α → ℝ} (hq : ∀ᶠ x in l, 0 < q x) (hle : ∀ᶠ x in l, g x ≤ -q x + R x)
    (hR : R =o[l] q) : ∀ᶠ x in l, g x < 0 := by
  filter_upwards [hq, hle, hR.def (by norm_num : (0 : ℝ) < 1 / 2)] with x hqx hgx hRx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hqx] at hRx
  have := le_abs_self (R x)
  linarith

/-- States along a ray `t • d`, `t > 0`, accumulate at the origin. -/
@[tmio T, powerlib_foundation] theorem frequently_of_forall_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (d : E) {P : E → Prop} (h : ∀ t : ℝ, 0 < t → P (t • d)) :
    ∃ᶠ z in 𝓝 (0 : E), P z := by
  rw [Filter.frequently_iff]
  intro U hU
  have hc : Tendsto (fun t : ℝ => t • d) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => t • d) (𝓝 0) (𝓝 ((0 : ℝ) • d)) :=
      (continuous_id.smul continuous_const).tendsto 0
    rw [zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨t, htU, ht⟩ := ((hc.eventually hU).and self_mem_nhdsWithin).exists
  exact ⟨t • d, htU, h t ht⟩

/-! ## Taylor remainders of `sin` and `cos` at `0` -/

/-- `1 − cos x = O(x²)`. -/
@[tmio T, powerlib_foundation] theorem one_sub_cos_isBigO :
    (fun x : ℝ => 1 - Real.cos x) =O[𝓝 0] fun x => x ^ 2 := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)
  have h1 := Real.one_sub_sq_div_two_le_cos (x := x)
  have h2 := Real.cos_le_one x
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
    abs_of_nonneg (sq_nonneg x)]
  nlinarith [sq_nonneg x]

/-- `sin x − x = O(x³)`. -/
@[tmio T, powerlib_foundation] theorem sin_sub_self_isBigO :
    (fun x : ℝ => Real.sin x - x) =O[𝓝 0] fun x => x ^ 3 := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with x hx
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
  have hb := Real.sin_bound hx.le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, one_mul]
  have h5 : |x| ^ 5 ≤ |x| ^ 3 := pow_le_pow_of_le_one (abs_nonneg _) hx.le (by norm_num)
  have h3 : |x ^ 3 / 6| = |x| ^ 3 / 6 := by rw [abs_div, abs_pow]; norm_num
  calc |Real.sin x - x| = |(Real.sin x - (x - x ^ 3 / 6)) - x ^ 3 / 6| := by ring_nf
    _ ≤ |Real.sin x - (x - x ^ 3 / 6)| + |x ^ 3 / 6| := abs_sub _ _
    _ ≤ |x| ^ 3 := by
        have h0 : 0 ≤ |x| ^ 3 := by positivity
        rw [h3]; linarith

/-- `1 − cos x − x²/2 = O(x⁴)`. -/
@[tmio T, powerlib_foundation] theorem one_sub_cos_sub_isBigO :
    (fun x : ℝ => 1 - Real.cos x - x ^ 2 / 2) =O[𝓝 0] fun x => x ^ 4 := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with x hx
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
  have hb := Real.cos_bound hx.le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, one_mul]
  have : |1 - Real.cos x - x ^ 2 / 2| = |Real.cos x - (1 - x ^ 2 / 2)| := by
    rw [← abs_neg]; ring_nf
  rw [this]
  have h4 : 0 ≤ |x| ^ 4 := by positivity
  linarith

end Asymptotic

/-! ## Curves through a matrix -/

open Matrix in
/-- A matrix maps a differentiable curve to a differentiable curve: `(M x)' = M x'` (rectangular
`M`, any finite index types). -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_mulVec {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) {x : ℝ → κ → ℝ} {x' : κ → ℝ} {t : ℝ} (hx : HasDerivAt x x' t) :
    HasDerivAt (fun s => M *ᵥ x s) (M *ᵥ x') t := by
  have h := (LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)).hasFDerivAt.comp_hasDerivAt t hx
  simpa [Function.comp_def] using h

/-! ## First integrals -/

/-- A differentiable `I` with `∇I · f ≡ 0` is constant along every solution segment of `f`
(generic: any field, any differentiable `I`). -/
@[tmio T, powerlib_foundation] theorem firstIntegral_const {n : ℕ} {f : State n → State n}
    {I : State n → ℝ} (hI : Differentiable ℝ I) (h0 : ∀ x, fderiv ℝ I x (f x) = 0)
    {φ : ℝ → State n} {a b : ℝ} (hφ : IsTrajectoryOn φ f a b) :
    ∀ t ∈ Set.Icc a b, I (φ t) = I (φ a) := by
  intro t ht
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have h1 := antitoneOn_V_comp_traj hI hI.continuous (convex_Icc a b) hφ
    (fun s _ => (h0 (φ s)).le) ha ht ht.1
  have hneg : Differentiable ℝ (fun x => -I x) := hI.neg
  have h2 := antitoneOn_V_comp_traj hneg hneg.continuous (convex_Icc a b) hφ
    (fun s _ => by rw [fderiv_fun_neg, _root_.neg_apply, h0, neg_zero]) ha ht ht.1
  simp only [Function.comp_apply] at h1 h2
  linarith

end powerlib.Dynamics
