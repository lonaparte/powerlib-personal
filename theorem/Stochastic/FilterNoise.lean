import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.MomentumNoise
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! # The quasi-potential of the rate for momentum noise behind a lagged sinusoidal output

The three-state system `q̇ = p`, `ṗ = f(q, p, z) + σ u`, `ż = κ (a₀ + A sin(q − α) − z)` (noise in
the momentum row only, `σ ≠ 0`; `z` a first-order lag of the sinusoidal output `a₀ + A sin(q − α)`).
As for the planar system (`theorem/Stochastic/MomentumNoise.lean`), the quasi-potential of the
Freidlin–Wentzell rate equals the controlled quasi-potential, for every pair of endpoints. The
endpoints `q(T)`, `p(T)` are kept by the two moments of `ṗ` (`exists_rc_approx`); the lag endpoint
`z(T) = e^{−κT}(z(0) + κ ∫₀ᵀ e^{κs}(a₀ + A sin(q(s) − α)) ds)` is a nonlinear functional of the
angle and is corrected by the intermediate value theorem along a bump perturbation `q + λβ`
placed where `cos(q − α) ≠ 0`. If `cos(q(t) − α) = 0` on all of `(0, T)`, the angle is constant,
`p = 0`, and the control is a.e. equal to a continuous one: no approximation is needed.

Scope.
* Generic: `b : ℝ³ → ℝ³` globally Lipschitz with `b(x)₀ = x₁`,
  `b(x)₂ = κ (a₀ + A sin(x₀ − α) − x₂)`, one noise column `(0, σ, 0)`, `σ ≠ 0`; deterministic
  statements on the rate.

Source: M. I. Freidlin, A. D. Wentzell, *Random Perturbations of Dynamical Systems* (1984),
Ch. 4 §1–3 (quasi-potential of the action functional; degenerate noise).

Results.
* `sin_add_sub_sin_eq` (mean value form), `exists_cos_sub_ne_zero`, `sq_add_sub_le_three`,
  `exists_bump`, `intervalIntegral_pi_apply`, `columnsCLM_filter`, `filter_components`,
  `leftInverse_filter`.
* `controlQuasiPotential_le_of_cos_eq_zero` (degenerate angle),
  `controlQuasiPotential_le_of_cos_ne_zero` (**bump correction of the lag endpoint**),
  `controlQuasiPotential_le_controlAction_filter`, `controlQuasiPotential_le_fwRate_filter`,
  `fwQP_eq_controlQuasiPotential_filter` (**the quasi-potential of the rate is the controlled
  quasi-potential**, every pair of endpoints).
-/

noncomputable section
namespace powerlib.Stochastic.LDP

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

variable {T : ℝ≥0}

/-! ## Elementary lemmas -/

/-- **Mean value form**: `sin(z + h) − sin z = h cos(z + ξ)` with `|ξ| ≤ |h|`. -/
@[tmio T, powerlib_foundation] theorem sin_add_sub_sin_eq (z h : ℝ) :
    ∃ ξ, |ξ| ≤ |h| ∧ Real.sin (z + h) - Real.sin z = h * Real.cos (z + ξ) := by
  rcases lt_trichotomy h 0 with hh | rfl | hh
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Real.sin Real.cos
      (show z + h < z by linarith) Real.continuous_sin.continuousOn
      (fun x _ => Real.hasDerivAt_sin x)
    refine ⟨c - z, ?_, ?_⟩
    · rw [abs_of_neg (by linarith [hc.2]), abs_of_neg hh]; linarith [hc.1]
    · have hh' : h ≠ 0 := hh.ne
      rw [show z + (c - z) = c by ring, hcd, show z - (z + h) = -h by ring]
      field_simp
      ring
  · exact ⟨0, by simp, by simp⟩
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Real.sin Real.cos
      (show z < z + h by linarith) Real.continuous_sin.continuousOn
      (fun x _ => Real.hasDerivAt_sin x)
    refine ⟨c - z, ?_, ?_⟩
    · rw [abs_of_pos (by linarith [hc.1]), abs_of_pos hh]; linarith [hc.2]
    · have hh' : h ≠ 0 := hh.ne'
      rw [show z + (c - z) = c by ring, hcd, show z + h - z = h by ring]
      field_simp

/-- `cos(· − α)` does not vanish identically on a nontrivial interval. -/
@[tmio T, powerlib_foundation] theorem exists_cos_sub_ne_zero (α : ℝ) {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Icc a b, Real.cos (y - α) ≠ 0 := by
  by_cases ha : Real.cos (a - α) = 0
  · have hh0 : 0 < min (b - a) 1 := lt_min (by linarith) one_pos
    have hh1 : min (b - a) 1 ≤ 1 := min_le_right _ _
    have hh2 : min (b - a) 1 ≤ b - a := min_le_left _ _
    refine ⟨a + min (b - a) 1, ⟨by linarith, by linarith⟩, ?_⟩
    have hs : Real.sin (a - α) ≠ 0 := by
      intro hs
      have := Real.sin_sq_add_cos_sq (a - α)
      rw [hs, ha] at this
      norm_num at this
    have hsh : 0 < Real.sin (min (b - a) 1) :=
      Real.sin_pos_of_pos_of_lt_pi hh0 (by linarith [Real.two_le_pi])
    rw [show a + min (b - a) 1 - α = (a - α) + min (b - a) 1 by ring, Real.cos_add, ha,
      zero_mul, zero_sub, neg_ne_zero]
    exact mul_ne_zero hs hsh.ne'
  · exact ⟨a, ⟨le_rfl, hab.le⟩, ha⟩

/-- `(a + b − c)² ≤ 3 (a² + b² + c²)`. -/
@[tmio T, powerlib_foundation] theorem sq_add_sub_le_three (a b c : ℝ) :
    (a + b - c) ^ 2 ≤ 3 * (a ^ 2 + (b ^ 2 + c ^ 2)) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + c), sq_nonneg (b + c)]

/-- **A smooth bump** `0 ≤ β ≤ 1` around `t₁`, vanishing with its derivative for
`|t − t₁| ≥ r`, with two continuous derivatives and positive integral. -/
@[tmio T, powerlib_foundation] theorem exists_bump {t₁ r : ℝ} (hr : 0 < r) :
    ∃ β β₁ β₂ : ℝ → ℝ, Continuous β ∧ Continuous β₁ ∧ Continuous β₂ ∧
      (∀ t, HasDerivAt β (β₁ t) t) ∧ (∀ t, HasDerivAt β₁ (β₂ t) t) ∧
      (∀ t, 0 ≤ β t ∧ β t ≤ 1) ∧ (∀ t, r ≤ |t - t₁| → β t = 0 ∧ β₁ t = 0) ∧
      0 < ∫ t, β t := by
  let f : ContDiffBump t₁ := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have h3 : ContDiff ℝ (2 + 1) f := f.contDiff
  have h2 : ContDiff ℝ (1 + 1) (deriv f) := h3.deriv'
  have h1 : ContDiff ℝ 1 (deriv (deriv f)) := h2.deriv'
  refine ⟨f, deriv f, deriv (deriv f), f.continuous, h2.continuous, h1.continuous,
    fun t => ((h3.differentiable (by norm_num)) t).hasDerivAt,
    fun t => ((h2.differentiable (by norm_num)) t).hasDerivAt,
    fun t => ⟨f.nonneg, f.le_one⟩, fun t ht => ?_, f.integral_pos⟩
  have hnot : t ∉ tsupport f := by
    rw [f.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, not_le]
    show r / 2 < |t - t₁|
    linarith
  refine ⟨image_eq_zero_of_notMem_tsupport hnot, ?_⟩
  by_contra h
  exact hnot (support_deriv_subset h)

/-- Components of an interval integral in `ℝⁿ`. -/
@[tmio T, powerlib_foundation] theorem intervalIntegral_pi_apply {n : ℕ} {F : ℝ → Fin n → ℝ}
    {a b : ℝ} (hF : IntervalIntegrable F volume a b) (i : Fin n) :
    (∫ s in a..b, F s) i = ∫ s in a..b, F s i := by
  have hc := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ)
    i).intervalIntegral_comp_comm hF
  simp only [ContinuousLinearMap.proj_apply] at hc
  exact hc.symm

/-- The noise map of the column `(0, σ, 0)`. -/
@[tmio T, powerlib_foundation] theorem columnsCLM_filter (σ : ℝ) (z : Fin 1 → ℝ) :
    columnsCLM (fun _ : Fin 1 => ![(0 : ℝ), σ, 0]) z = ![0, σ * z 0, 0] := by
  rw [columnsCLM_apply]
  ext i
  fin_cases i <;> simp [mul_comm]

/-- **Components of the integral equation** (three states, column `(0, σ, 0)`). -/
@[tmio T, powerlib_foundation] theorem filter_components {K : ℝ≥0}
    {b : (Fin 3 → ℝ) → Fin 3 → ℝ} (hb : LipschitzWith K b) (hb0 : ∀ y, b y 0 = y 1) (σ : ℝ)
    (xA : Fin 3 → ℝ) {u : ℝ → Fin 1 → ℝ} (hu : IntervalIntegrable u volume 0 T)
    {Φ : ℝ → Fin 3 → ℝ} (hΦc : Continuous Φ)
    (hint : ∀ t ∈ Icc (0 : ℝ) T, Φ t = xA + ∫ s in (0 : ℝ)..t,
      (columnsCLM (fun _ : Fin 1 => ![(0 : ℝ), σ, 0]) (u s) + b (Φ s))) :
    ∀ t ∈ Icc (0 : ℝ) T, Φ t 0 = xA 0 + ∫ s in (0 : ℝ)..t, Φ s 1 ∧
      Φ t 1 = xA 1 + ∫ s in (0 : ℝ)..t, (σ * u s 0 + b (Φ s) 1) ∧
      Φ t 2 = xA 2 + ∫ s in (0 : ℝ)..t, b (Φ s) 2 := by
  intro t ht
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 T := by
    rw [uIcc_of_le ht.1, uIcc_of_le T.coe_nonneg]; exact Icc_subset_Icc_right ht.2
  have hNu : IntervalIntegrable (fun r => columnsCLM (fun _ : Fin 1 => ![(0 : ℝ), σ, 0]) (u r))
      volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
      ((columnsCLM _).integrable_comp
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mp (hu.mono_set hsub)))
  have hF : IntervalIntegrable (fun s => columnsCLM (fun _ : Fin 1 => ![(0 : ℝ), σ, 0]) (u s) +
      b (Φ s)) volume 0 t := hNu.add ((hb.continuous.comp hΦc).intervalIntegrable 0 t)
  have hi : ∀ i, Φ t i = xA i + ∫ s in (0 : ℝ)..t,
      (columnsCLM (fun _ : Fin 1 => ![(0 : ℝ), σ, 0]) (u s) i + b (Φ s) i) := fun i => by
    rw [hint t ht, Pi.add_apply, intervalIntegral_pi_apply hF]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hi 0]; congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp [columnsCLM_filter, hb0]
  · rw [hi 1]; congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp [columnsCLM_filter]
  · rw [hi 2]; congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp [columnsCLM_filter]

/-! ## The degenerate angle -/

/-- **Degenerate angle**: if `cos(q(t) − α) = 0` on `(0, T)`, the angle is constant, `p = 0`, the
control is a.e. the continuous `−b(x)₁/σ`, and the path itself is admissible with it. -/
@[tmio T, powerlib_foundation] theorem controlQuasiPotential_le_of_cos_eq_zero {K : ℝ≥0}
    {b : (Fin 3 → ℝ) → Fin 3 → ℝ} (hb : LipschitzWith K b) (hb0 : ∀ y, b y 0 = y 1)
    {σ : ℝ} (hσ : σ ≠ 0) (α : ℝ) (xA : Fin 3 → ℝ) {u : ℝ → Fin 1 → ℝ}
    (hu : IntervalIntegrable u volume 0 T) (hT : 0 < (T : ℝ)) {Φ : ℝ → Fin 3 → ℝ}
    (hΦc : Continuous Φ)
    (hint : ∀ t ∈ Icc (0 : ℝ) T, Φ t = xA + ∫ s in (0 : ℝ)..t,
      (columnsCLM (fun _ : Fin 1 => ![(0 : ℝ), σ, 0]) (u s) + b (Φ s)))
    (hdeg : ∀ t ∈ Ioo (0 : ℝ) T, Real.cos (Φ t 0 - α) = 0) :
    controlQuasiPotential b (fun _ (_ : Fin 1) => ![0, σ, 0]) xA (Φ T) ≤
      ENNReal.ofReal (controlAction u T) := by
  have hT0 := T.coe_nonneg
  have hcomp := filter_components hb hb0 σ xA hu hΦc hint
  have hΦ0c : Continuous fun s => Φ s 0 := (continuous_apply 0).comp hΦc
  have hΦ1c : Continuous fun s => Φ s 1 := (continuous_apply 1).comp hΦc
  have hb1 : Continuous fun s => b (Φ s) 1 := (continuous_apply 1).comp (hb.continuous.comp hΦc)
  -- the angle is constant on `(0, T)`
  have hconst : ∀ t₁ ∈ Ioo (0 : ℝ) T, ∀ t₂ ∈ Ioo (0 : ℝ) T, Φ t₁ 0 = Φ t₂ 0 := by
    intro t₁ h₁ t₂ h₂
    by_contra hne
    obtain ⟨y, hy, hcy⟩ := exists_cos_sub_ne_zero α (min_lt_max.mpr hne)
    obtain ⟨t, ht, hty⟩ := intermediate_value_uIcc hΦ0c.continuousOn hy
    have htI : t ∈ Ioo (0 : ℝ) T := (ordConnected_Ioo.uIcc_subset h₁ h₂) ht
    exact hcy (by rw [← hty]; exact hdeg t htI)
  -- hence `p = 0` on `[0, T]`
  have h1zero : ∀ t ∈ Ioo (0 : ℝ) T, Φ t 1 = 0 := by
    intro t ht
    have hd1 : HasDerivAt (fun s => xA 0 + ∫ r in (0 : ℝ)..s, Φ r 1) (Φ t 1) t :=
      ((hΦ1c.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add _
    have hev : (fun s => Φ s 0) =ᶠ[𝓝 t] fun s => xA 0 + ∫ r in (0 : ℝ)..s, Φ r 1 := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact (hcomp s (Ioo_subset_Icc_self hs)).1
    have hev0 : (fun s => Φ s 0) =ᶠ[𝓝 t] fun _ => Φ t 0 := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact hconst s hs t ht
    exact (hd1.congr_of_eventuallyEq hev).unique
      ((hasDerivAt_const t (Φ t 0)).congr_of_eventuallyEq hev0)
  have h1zero' : ∀ t ∈ Icc (0 : ℝ) T, Φ t 1 = 0 := by
    have hcl : IsClosed {t : ℝ | Φ t 1 = 0} := isClosed_eq hΦ1c continuous_const
    have h := hcl.closure_subset_iff.mpr fun t ht => h1zero t ht
    rw [closure_Ioo hT.ne] at h
    exact fun t ht => h ht
  -- the momentum derivative vanishes a.e.
  obtain ⟨v, hv⟩ : ∃ v : ℝ → ℝ, ∀ s, v s = σ * u s 0 + b (Φ s) 1 := ⟨_, fun s => rfl⟩
  have hu0i : IntervalIntegrable (fun s => u s 0) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).mpr
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).integrable_comp
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).mp hu))
  have hvi : IntervalIntegrable v volume 0 T := by
    rw [funext hv]; exact (hu0i.const_mul σ).add (hb1.intervalIntegrable 0 T)
  have hT0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT0⟩
  have hxA1 : xA 1 = 0 := by
    have h := (hcomp 0 hT0mem).2.1
    simp only [intervalIntegral.integral_same, add_zero] at h
    rw [← h]; exact h1zero' 0 hT0mem
  have hprim : ∀ t ∈ Icc (0 : ℝ) T, ∫ s in (0 : ℝ)..t, v s = ∫ s in (0 : ℝ)..t, (0 : ℝ) := by
    intro t ht
    have h := (hcomp t ht).2.1
    rw [h1zero' t ht, hxA1, zero_add] at h
    rw [intervalIntegral.integral_zero]
    rw [show (fun s => v s) = fun s => σ * u s 0 + b (Φ s) 1 from funext hv]
    exact h.symm
  have hae := ae_eq_of_primitive_eq (T := T) hvi intervalIntegrable_const hprim
  -- the continuous control
  obtain ⟨ũ, hũ⟩ : ∃ ũ : ℝ → Fin 1 → ℝ, ∀ s, ũ s = fun _ => -b (Φ s) 1 / σ :=
    ⟨_, fun s => rfl⟩
  have hũc : Continuous ũ := by
    rw [funext hũ]; exact continuous_pi fun _ => (hb1.neg).div_const σ
  have hTne : ∀ᵐ s : ℝ, s ≠ (T : ℝ) := by simp [ae_iff, measure_singleton]
  have hũae : ∀ᵐ s, s ∈ Ioo (0 : ℝ) T → u s = ũ s := by
    filter_upwards [hae] with s hs hsI
    have h0 := hs hsI
    rw [hv] at h0
    rw [hũ]
    funext j
    fin_cases j
    simp only [Fin.zero_eta]
    field_simp
    linarith
  have hint' : ∀ t ∈ Icc (0 : ℝ) T, Φ t = xA + ∫ s in (0 : ℝ)..t,
      (columnsCLM (fun _ : Fin 1 => ![(0 : ℝ), σ, 0]) (ũ s) + b (Φ s)) := by
    intro t ht
    rw [hint t ht]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hũae, hTne] with s hs hsT hsI
    rw [uIoc_of_le ht.1] at hsI
    rw [hs ⟨hsI.1, lt_of_le_of_ne (hsI.2.trans ht.2) hsT⟩]
  -- admissibility of `(Φ, ũ)`
  have hFc : Continuous fun s => columnsCLM (fun _ : Fin 1 => ![(0 : ℝ), σ, 0]) (ũ s) + b (Φ s) :=
    ((columnsCLM _).continuous.comp hũc).add (hb.continuous.comp hΦc)
  have hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt Φ
      (controlField b (fun _ (_ : Fin 1) => ![0, σ, 0]) (Φ t) (ũ t)) (Ici t) t := by
    intro t ht
    have hFd := ((hFc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add xA).hasDerivWithinAt
      (s := Ici t)
    have hev : Φ =ᶠ[𝓝[≥] t] fun t => xA + ∫ s in (0 : ℝ)..t,
        (columnsCLM (fun _ : Fin 1 => ![(0 : ℝ), σ, 0]) (ũ s) + b (Φ s)) := by
      filter_upwards [Ico_mem_nhdsGE ht.2] with s hs
      exact hint' s ⟨ht.1.trans hs.1, hs.2.le⟩
    refine (hFd.congr_of_eventuallyEq hev (hint' t (Ico_subset_Icc_self ht))).congr_deriv ?_
    rw [controlField_const, add_comm]
  have hΦ0 : Φ 0 = xA := by rw [hint' 0 hT0mem]; simp
  have hũ2 : IntervalIntegrable (fun t => ∑ j, ũ t j ^ 2) volume 0 T :=
    (continuous_finsetSum _ fun j _ => ((continuous_apply j).comp hũc).pow 2).intervalIntegrable _ _
  have hact : controlAction ũ T = controlAction u T := by
    unfold controlAction
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hũae, hTne] with s hs hsT hsI
    rw [uIoc_of_le hT0] at hsI
    rw [hs ⟨hsI.1, lt_of_le_of_ne hsI.2 hsT⟩]
  rw [← hact]
  unfold controlQuasiPotential
  exact iInf_le_of_le (T : ℝ) (iInf_le_of_le Φ (iInf_le_of_le ũ (iInf_le_of_le
    ⟨hT0, hΦ0, rfl, hΦc.continuousOn, hderiv, hũ2⟩ le_rfl)))

/-! ## Correction of the lag endpoint -/

/-- **Bump correction of the lag endpoint**: if `cos(q(t₁) − α) ≠ 0` at some `t₁ ∈ (0, T)`, a
square-integrable control is replaced by a right-continuous one keeping all three endpoints, with
the action larger by at most any `η > 0`. The first two endpoints are kept by the two moments of
`ṗ`; the lag endpoint by the intermediate value theorem in `λ` along `q + λ c₁ β`
(`c₁ = cos(q(t₁) − α)`, `β` a bump near `t₁`). -/
@[tmio T, powerlib_foundation] theorem controlQuasiPotential_le_of_cos_ne_zero {K : ℝ≥0}
    {b : (Fin 3 → ℝ) → Fin 3 → ℝ} (hb : LipschitzWith K b) (hb0 : ∀ y, b y 0 = y 1)
    {κ a₀ A α : ℝ} (hb2 : ∀ y, b y 2 = κ * (a₀ + A * Real.sin (y 0 - α) - y 2))
    {σ : ℝ} (hσ : σ ≠ 0) (xA : Fin 3 → ℝ) {u : ℝ → Fin 1 → ℝ}
    (hu : IntervalIntegrable u volume 0 T)
    (hu2 : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) volume 0 T) (hT : 0 < (T : ℝ))
    {Φ : ℝ → Fin 3 → ℝ} (hΦc : Continuous Φ)
    (hint : ∀ t ∈ Icc (0 : ℝ) T, Φ t = xA + ∫ s in (0 : ℝ)..t,
      (columnsCLM (fun _ : Fin 1 => ![(0 : ℝ), σ, 0]) (u s) + b (Φ s)))
    {t₁ : ℝ} (ht₁ : t₁ ∈ Ioo (0 : ℝ) T) (hc₁ : Real.cos (Φ t₁ 0 - α) ≠ 0) :
    controlQuasiPotential b (fun _ (_ : Fin 1) => ![0, σ, 0]) xA (Φ T) ≤
      ENNReal.ofReal (controlAction u T) := by
  have hT0 := T.coe_nonneg
  have hIcc : uIcc (0 : ℝ) T = Icc (0 : ℝ) T := uIcc_of_le hT0
  have hTmem : (T : ℝ) ∈ Icc (0 : ℝ) T := right_mem_Icc.mpr hT0
  have hT0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := left_mem_Icc.mpr hT0
  have hcomp := filter_components hb hb0 σ xA hu hΦc hint
  have hΦ0c : Continuous fun s => Φ s 0 := (continuous_apply 0).comp hΦc
  have hΦ1c : Continuous fun s => Φ s 1 := (continuous_apply 1).comp hΦc
  have hbΦ : Continuous fun s => b (Φ s) := hb.continuous.comp hΦc
  have hb1 : Continuous fun s => b (Φ s) 1 := (continuous_apply 1).comp hbΦ
  have hb2c : Continuous fun s => b (Φ s) 2 := (continuous_apply 2).comp hbΦ
  have hsq1 : ∀ z : ℝ → Fin 1 → ℝ, (fun s => ∑ j, z s j ^ 2) = fun s => z s 0 ^ 2 :=
    fun z => by funext s; simp
  have hu0i : IntervalIntegrable (fun s => u s 0) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).mpr
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).integrable_comp
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).mp hu))
  have hu02 : IntervalIntegrable (fun s => u s 0 ^ 2) volume 0 T := by rw [← hsq1]; exact hu2
  obtain ⟨v, hv⟩ : ∃ v : ℝ → ℝ, ∀ s, v s = σ * u s 0 + b (Φ s) 1 := ⟨_, fun s => rfl⟩
  have hvi : IntervalIntegrable v volume 0 T := by
    rw [funext hv]; exact (hu0i.const_mul σ).add (hb1.intervalIntegrable 0 T)
  have hv2 : IntervalIntegrable (fun s => v s ^ 2) volume 0 T := by
    have e : (fun s => v s ^ 2) = fun s =>
        σ ^ 2 * u s 0 ^ 2 + 2 * σ * (u s 0 * b (Φ s) 1) + b (Φ s) 1 ^ 2 := by
      funext s; rw [hv]; ring
    rw [e]
    exact ((hu02.const_mul _).add ((hu0i.mul_continuousOn hb1.continuousOn).const_mul _)).add
      ((hb1.pow 2).intervalIntegrable 0 T)
  have h0t : ∀ t ∈ Icc (0 : ℝ) T, Φ t 0 = xA 0 + ∫ s in (0 : ℝ)..t, Φ s 1 :=
    fun t ht => (hcomp t ht).1
  have h1t : ∀ t ∈ Icc (0 : ℝ) T, Φ t 1 = xA 1 + ∫ s in (0 : ℝ)..t, v s := fun t ht => by
    rw [(hcomp t ht).2.1, funext hv]
  have h2t : ∀ t ∈ Icc (0 : ℝ) T, Φ t 2 = xA 2 + ∫ s in (0 : ℝ)..t, b (Φ s) 2 :=
    fun t ht => (hcomp t ht).2.2
  -- a neighbourhood of `t₁` where `c₁ cos(q − α) ≥ c₁²/2`
  obtain ⟨c₁, hc₁def⟩ : ∃ c₁, c₁ = Real.cos (Φ t₁ 0 - α) := ⟨_, rfl⟩
  rw [← hc₁def] at hc₁
  have hcosc : Continuous fun t => Real.cos (Φ t 0 - α) :=
    Real.continuous_cos.comp (hΦ0c.sub continuous_const)
  obtain ⟨δ₀, hδ₀, hδ₀c⟩ := Metric.continuous_iff.mp hcosc t₁ (|c₁| / 2)
    (by positivity)
  obtain ⟨r, hrdef⟩ : ∃ r, r = min δ₀ (min (t₁ / 2) ((T - t₁) / 2)) := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hrdef]; exact lt_min hδ₀ (lt_min (by linarith [ht₁.1])
    (by linarith [ht₁.2]))
  have hr1 : r ≤ t₁ / 2 := by rw [hrdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hr2 : r ≤ (T - t₁) / 2 := by rw [hrdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hr3 : r ≤ δ₀ := by rw [hrdef]; exact min_le_left _ _
  obtain ⟨β, β₁, β₂, hβc, hβ₁c, hβ₂c, hβd, hβ₁d, hβ01, hβout, hβint⟩ := exists_bump (t₁ := t₁) hr
  have hβ0 : β 0 = 0 ∧ β₁ 0 = 0 :=
    hβout 0 (by rw [zero_sub, abs_neg, abs_of_pos ht₁.1]; linarith)
  have hβT : β T = 0 ∧ β₁ T = 0 :=
    hβout T (by rw [abs_of_pos (by linarith [ht₁.2])]; linarith)
  have hsign : ∀ s, 0 ≤ β s * (c₁ * Real.cos (Φ s 0 - α) - c₁ ^ 2 / 2) := by
    intro s
    by_cases hs : |s - t₁| < r
    · have h := hδ₀c s (by rw [Real.dist_eq]; linarith)
      rw [Real.dist_eq, ← hc₁def] at h
      have h' : |c₁ * (Real.cos (Φ s 0 - α) - c₁)| ≤ |c₁| * (|c₁| / 2) := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left h.le (abs_nonneg _)
      have h'' := neg_abs_le (c₁ * (Real.cos (Φ s 0 - α) - c₁))
      have hsq : |c₁| * |c₁| = c₁ ^ 2 := by rw [← abs_mul, abs_mul_self, sq]
      refine mul_nonneg (hβ01 s).1 ?_
      nlinarith
    · rw [(hβout s (not_lt.mp hs)).1, zero_mul]
  have hc₁sq : 0 < c₁ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hc₁))
  have hc₁le : |c₁| ≤ 1 := by rw [hc₁def]; exact Real.abs_cos_le_one _
  -- bounds on `[0, T]`
  obtain ⟨B₁, hB₁⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := (T : ℝ))).exists_bound_of_continuousOn
    hβ₁c.continuousOn
  obtain ⟨B₂, hB₂⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := (T : ℝ))).exists_bound_of_continuousOn
    hβ₂c.continuousOn
  have hB₁0 : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ 0 hT0mem)
  have hB₂0 : 0 ≤ B₂ := (norm_nonneg _).trans (hB₂ 0 hT0mem)
  obtain ⟨E₁, hE₁def⟩ : ∃ E₁, E₁ = Real.exp (|κ| * T) := ⟨_, rfl⟩
  have hE₁1 : 1 ≤ E₁ := by rw [hE₁def]; exact Real.one_le_exp (by positivity)
  have hE : ∀ s ∈ Icc (0 : ℝ) T, Real.exp (κ * s) ≤ E₁ ∧ Real.exp (-(κ * s)) ≤ E₁ ∧
      E₁⁻¹ ≤ Real.exp (κ * s) := by
    intro s hs
    have h1 : |κ * s| ≤ |κ| * T := by
      rw [abs_mul, abs_of_nonneg hs.1]; exact mul_le_mul_of_nonneg_left hs.2 (abs_nonneg _)
    have h2 := abs_le.mp h1
    rw [hE₁def, ← Real.exp_neg]
    exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr (by linarith),
      Real.exp_le_exp.mpr (by linarith)⟩
  -- the weighted bump mass
  have hexpc : Continuous fun s : ℝ => Real.exp (κ * s) := by fun_prop
  obtain ⟨Iβ, hIβdef⟩ : ∃ Iβ, Iβ = ∫ s in (0 : ℝ)..T, Real.exp (κ * s) * β s := ⟨_, rfl⟩
  have hIβ : 0 < Iβ := by
    have h1 : ∫ s in (0 : ℝ)..T, β s = ∫ s, β s := by
      rw [intervalIntegral.integral_of_le hT0]
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_
      refine (hβout s ?_).1
      rcases not_and_or.mp hs with h | h
      · rw [not_lt] at h; rw [abs_of_nonpos (by linarith [ht₁.1])]; linarith
      · rw [not_le] at h; rw [abs_of_pos (by linarith [ht₁.2])]; linarith
    have h2 : E₁⁻¹ * ∫ s in (0 : ℝ)..T, β s ≤ Iβ := by
      rw [hIβdef, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on hT0 ((hβc.const_mul _).intervalIntegrable 0 T)
        ((hexpc.mul hβc).intervalIntegrable 0 T) fun s hs => ?_
      exact mul_le_mul_of_nonneg_right (hE s hs).2.2 (hβ01 s).1
    have h3 : 0 < E₁⁻¹ * ∫ s in (0 : ℝ)..T, β s := by
      rw [h1]; exact mul_pos (inv_pos.mpr (by linarith)) hβint
    linarith
  obtain ⟨μ, hμdef⟩ : ∃ μ, μ = c₁ ^ 2 / 4 * Iβ := ⟨_, rfl⟩
  have hμ : 0 < μ := by rw [hμdef]; positivity
  -- the tolerance and the constants
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = (ε : ℝ) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; exact hε
  obtain ⟨Au, hAu⟩ : ∃ Au, Au = ∫ s in (0 : ℝ)..T, u s 0 ^ 2 := ⟨_, rfl⟩
  have hAu0 : 0 ≤ Au := by
    rw [hAu]; exact intervalIntegral.integral_nonneg hT0 fun s _ => sq_nonneg _
  obtain ⟨Ce, hCe⟩ : ∃ Ce : ℝ, Ce = 3 + B₁ + 2 * E₁ ^ 2 * |κ * A| * T := ⟨_, rfl⟩
  have hCe0 : 0 ≤ Ce := by rw [hCe]; positivity
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = 3 * (1 + T * B₂ ^ 2 + T * ((K : ℝ) ^ 2 * Ce ^ 2)) / σ ^ 2 :=
    ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = η / (Au + 1) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  obtain ⟨C₂, hC₂⟩ : ∃ C₂, C₂ = (1 + 1 / θ) * C₁ := ⟨_, rfl⟩
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = min (c₁ ^ 2 / 8) (min 1 (η / (C₂ + 1))) := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by rw [hτ]; exact lt_min (by positivity) (lt_min one_pos (by positivity))
  have hτc : τ ≤ c₁ ^ 2 / 8 := by rw [hτ]; exact min_le_left _ _
  have hτ1 : τ ≤ 1 := by rw [hτ]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hτη : τ ≤ η / (C₂ + 1) := by rw [hτ]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hC₂τ : C₂ * τ ^ 2 ≤ η := by
    have h1 : τ ^ 2 ≤ η / (C₂ + 1) :=
      calc τ ^ 2 = τ * τ := sq τ
        _ ≤ 1 * τ := mul_le_mul_of_nonneg_right hτ1 hτ0.le
        _ = τ := one_mul _
        _ ≤ η / (C₂ + 1) := hτη
    have h2 : C₂ / (C₂ + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
    calc C₂ * τ ^ 2 ≤ C₂ * (η / (C₂ + 1)) := mul_le_mul_of_nonneg_left h1 hC₂0
      _ = η * (C₂ / (C₂ + 1)) := by ring
      _ ≤ η * 1 := mul_le_mul_of_nonneg_left h2 hη.le
      _ = η := mul_one η
  obtain ⟨d₀, hd₀⟩ : ∃ d₀, d₀ = min τ (τ * μ / (2 * E₁ * T + 1)) := ⟨_, rfl⟩
  have hd₀0 : 0 < d₀ := by rw [hd₀]; exact lt_min hτ0 (by positivity)
  have hd₀τ : d₀ ≤ τ := by rw [hd₀]; exact min_le_left _ _
  have hd₀μ : E₁ * T * d₀ < τ * μ := by
    have h1 : d₀ ≤ τ * μ / (2 * E₁ * T + 1) := by rw [hd₀]; exact min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    have h3 : 0 < d₀ * (E₁ * T + 1) := by positivity
    linarith
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀, ε₀ = min (τ ^ 2) (d₀ ^ 2) / (T ^ 3 + T + 1) := ⟨_, rfl⟩
  have hε₀0 : 0 < ε₀ := by
    rw [hε₀]
    exact div_pos (lt_min (by positivity) (by positivity)) (by positivity)
  have hε₀a : T * ε₀ ≤ τ ^ 2 ∧ T ^ 3 * ε₀ ≤ d₀ ^ 2 ∧ ε₀ ≤ τ ^ 2 := by
    have hm1 : min (τ ^ 2) (d₀ ^ 2) ≤ τ ^ 2 := min_le_left _ _
    have hm2 : min (τ ^ 2) (d₀ ^ 2) ≤ d₀ ^ 2 := min_le_right _ _
    have e : ε₀ * ((T : ℝ) ^ 3 + T + 1) = min (τ ^ 2) (d₀ ^ 2) := by
      rw [hε₀]; field_simp
    have h1 : 0 ≤ (T : ℝ) ^ 3 * ε₀ := by positivity
    have h2 : 0 ≤ (T : ℝ) * ε₀ := by positivity
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  -- the moment-preserving approximation of `ṗ`
  obtain ⟨g, hgm, hgrc, hgi, hg2, hm1, hm2, hgv2, hgv⟩ := exists_rc_approx hT hvi hv2 hε₀0
  obtain ⟨p, hp⟩ : ∃ p : ℝ → ℝ, ∀ t, p t = xA 1 + ∫ s in (0 : ℝ)..t, g s := ⟨_, fun t => rfl⟩
  have hpc : Continuous p := by
    rw [funext hp]; exact continuous_const.add (intervalIntegral.continuous_primitive hgi 0)
  obtain ⟨q, hq⟩ : ∃ q : ℝ → ℝ, ∀ t, q t = xA 0 + ∫ s in (0 : ℝ)..t, p s := ⟨_, fun t => rfl⟩
  have hqc : Continuous q := by
    rw [funext hq]; exact continuous_const.add (intervalIntegral.continuous_primitive
      (fun a b => hpc.intervalIntegrable a b) 0)
  have hpΦc : Continuous fun s => p s - Φ s 1 := hpc.sub hΦ1c
  have hpb : ∀ s ∈ Icc (0 : ℝ) T, |p s - Φ s 1| ≤ τ := by
    intro s hs
    refine abs_le_of_sq_le_sq ?_ hτ0.le
    rw [hp, h1t s hs, add_sub_add_left_eq_sub]
    exact (sq_integral_sub_le (hgi 0 T) hvi hgv2 hs).trans
      ((mul_le_mul_of_nonneg_left hgv hT0).trans hε₀a.1)
  have hint2 : ∫ s in (0 : ℝ)..T, (p s - Φ s 1) ^ 2 ≤ T * (T * ε₀) := by
    have hb' : ∀ s ∈ Icc (0 : ℝ) T, (p s - Φ s 1) ^ 2 ≤ T * ε₀ := by
      intro s hs
      rw [hp, h1t s hs, add_sub_add_left_eq_sub]
      exact (sq_integral_sub_le (hgi 0 T) hvi hgv2 hs).trans (mul_le_mul_of_nonneg_left hgv hT0)
    calc _ ≤ ∫ s in (0 : ℝ)..T, (T * ε₀) :=
          intervalIntegral.integral_mono_on hT0 ((hpΦc.pow 2).intervalIntegrable 0 T)
            intervalIntegrable_const hb'
      _ = T * (T * ε₀) := by simp
  have hqb : ∀ s ∈ Icc (0 : ℝ) T, |q s - Φ s 0| ≤ d₀ := by
    intro s hs
    refine abs_le_of_sq_le_sq ?_ hd₀0.le
    rw [hq, h0t s hs, add_sub_add_left_eq_sub]
    have h := sq_integral_sub_le (T := T) (f₁ := p) (f₂ := fun s => Φ s 1)
      (hpc.intervalIntegrable 0 T) (hΦ1c.intervalIntegrable 0 T)
      ((hpΦc.pow 2).intervalIntegrable 0 T) hs
    have e : (T : ℝ) * (T * (T * ε₀)) = T ^ 3 * ε₀ := by ring
    exact (h.trans (mul_le_mul_of_nonneg_left hint2 hT0)).trans (e ▸ hε₀a.2.1)
  -- the lag functional along `q + λ c₁ β`
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, ∀ l, G l =
      ∫ s in (0 : ℝ)..T, Real.exp (κ * s) * Real.sin (q s + l * (c₁ * β s) - α) :=
    ⟨_, fun l => rfl⟩
  have hGc : Continuous G := by
    rw [funext hG]
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 T
    exact (hexpc.comp continuous_snd).mul (Real.continuous_sin.comp (((hqc.comp continuous_snd).add
      (continuous_fst.mul (continuous_const.mul (hβc.comp continuous_snd)))).sub continuous_const))
  obtain ⟨Gs, hGs⟩ : ∃ Gs, Gs = ∫ s in (0 : ℝ)..T, Real.exp (κ * s) * Real.sin (Φ s 0 - α) :=
    ⟨_, rfl⟩
  have hsinc : ∀ l, Continuous fun s => Real.exp (κ * s) * Real.sin (q s + l * (c₁ * β s) - α) :=
    fun l => hexpc.mul (Real.continuous_sin.comp ((hqc.add (continuous_const.mul
      (continuous_const.mul hβc))).sub continuous_const))
  have hsinΦc : Continuous fun s => Real.exp (κ * s) * Real.sin (Φ s 0 - α) :=
    hexpc.mul (Real.continuous_sin.comp (hΦ0c.sub continuous_const))
  have hsinq : Continuous fun s => Real.exp (κ * s) * Real.sin (q s - α) :=
    hexpc.mul (Real.continuous_sin.comp (hqc.sub continuous_const))
  -- `λ (G(λ) − G(0)) ≥ λ² μ` for `|λ| ≤ τ`
  have hD : ∀ l, |l| ≤ τ → ∀ s ∈ Icc (0 : ℝ) T, l ^ 2 * (c₁ ^ 2 / 4) * β s ≤
      l * (Real.sin (q s + l * (c₁ * β s) - α) - Real.sin (q s - α)) := by
    intro l hl s hs
    obtain ⟨ξ, hξ, hξe⟩ := sin_add_sub_sin_eq (q s - α) (l * (c₁ * β s))
    have hlβ : |l * (c₁ * β s)| ≤ τ := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hβ01 s).1]
      calc |l| * (|c₁| * β s) ≤ τ * (1 * 1) :=
            mul_le_mul hl (mul_le_mul hc₁le (hβ01 s).2 (hβ01 s).1 zero_le_one)
              (mul_nonneg (abs_nonneg _) (hβ01 s).1) hτ0.le
        _ = τ := by ring
    rw [show q s + l * (c₁ * β s) - α = (q s - α) + l * (c₁ * β s) by ring, hξe]
    have hcos := Real.abs_cos_sub_cos_le (q s - α + ξ) (Φ s 0 - α)
    have hqs := hqb s hs
    have hcl : c₁ * Real.cos (Φ s 0 - α) - 2 * τ ≤ c₁ * Real.cos (q s - α + ξ) := by
      have h1 : |c₁ * (Real.cos (q s - α + ξ) - Real.cos (Φ s 0 - α))| ≤
          |q s - α + ξ - (Φ s 0 - α)| := by
        rw [abs_mul]
        calc |c₁| * |Real.cos (q s - α + ξ) - Real.cos (Φ s 0 - α)|
            ≤ 1 * |q s - α + ξ - (Φ s 0 - α)| := by gcongr
          _ = _ := one_mul _
      have h2 : |q s - α + ξ - (Φ s 0 - α)| ≤ 2 * τ := by
        calc |q s - α + ξ - (Φ s 0 - α)| = |(q s - Φ s 0) + ξ| := by ring_nf
          _ ≤ |q s - Φ s 0| + |ξ| := abs_add_le _ _
          _ ≤ d₀ + τ := add_le_add hqs (hξ.trans hlβ)
          _ ≤ 2 * τ := by linarith
      have h3 := neg_abs_le (c₁ * (Real.cos (q s - α + ξ) - Real.cos (Φ s 0 - α)))
      linarith
    have hβs := hsign s
    have hβ0' := (hβ01 s).1
    have hkey : β s * (c₁ ^ 2 / 4) ≤ β s * (c₁ * Real.cos (q s - α + ξ)) := by
      have k1 := mul_le_mul_of_nonneg_left hcl hβ0'
      have k2 := mul_le_mul_of_nonneg_left hτc hβ0'
      linarith
    have hl2 := sq_nonneg l
    calc l ^ 2 * (c₁ ^ 2 / 4) * β s = l ^ 2 * (β s * (c₁ ^ 2 / 4)) := by ring
      _ ≤ l ^ 2 * (β s * (c₁ * Real.cos (q s - α + ξ))) :=
          mul_le_mul_of_nonneg_left hkey hl2
      _ = l * (l * (c₁ * β s) * Real.cos (q s - α + ξ)) := by ring
  have hGdiff : ∀ l, |l| ≤ τ → l ^ 2 * μ ≤ l * (G l - G 0) := by
    intro l hl
    have hG0 : G 0 = ∫ s in (0 : ℝ)..T, Real.exp (κ * s) * Real.sin (q s - α) := by
      rw [hG]; simp
    rw [hG l, hG0, ← intervalIntegral.integral_sub ((hsinc l).intervalIntegrable 0 T)
      (hsinq.intervalIntegrable 0 T),
      ← intervalIntegral.integral_const_mul, hμdef, hIβdef, ← mul_assoc,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hT0 ((hexpc.mul hβc).intervalIntegrable 0 T
      |>.const_mul _) (((hsinc l).sub hsinq).intervalIntegrable 0 T |>.const_mul _)
      fun s hs => ?_
    have h1 := hD l hl s hs
    have h2 := Real.exp_pos (κ * s)
    calc l ^ 2 * (c₁ ^ 2 / 4) * (Real.exp (κ * s) * β s)
        = Real.exp (κ * s) * (l ^ 2 * (c₁ ^ 2 / 4) * β s) := by ring
      _ ≤ Real.exp (κ * s) * (l * (Real.sin (q s + l * (c₁ * β s) - α) -
            Real.sin (q s - α))) := mul_le_mul_of_nonneg_left h1 h2.le
      _ = _ := by ring
  have hG0s : |G 0 - Gs| < τ * μ := by
    have hG0 : G 0 = ∫ s in (0 : ℝ)..T, Real.exp (κ * s) * Real.sin (q s - α) := by
      rw [hG]; simp
    rw [hG0, hGs, ← intervalIntegral.integral_sub (hsinq.intervalIntegrable 0 T)
      (hsinΦc.intervalIntegrable 0 T)]
    have hb' : ∀ s ∈ uIoc (0 : ℝ) T, ‖Real.exp (κ * s) * Real.sin (q s - α) -
        Real.exp (κ * s) * Real.sin (Φ s 0 - α)‖ ≤ E₁ * d₀ := by
      intro s hs
      rw [uIoc_of_le hT0] at hs
      have hs' : s ∈ Icc (0 : ℝ) T := Ioc_subset_Icc_self hs
      rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have h1 := Real.abs_sin_sub_sin_le (q s - α) (Φ s 0 - α)
      rw [show q s - α - (Φ s 0 - α) = q s - Φ s 0 by ring] at h1
      exact mul_le_mul (hE s hs').1 (h1.trans (hqb s hs')) (abs_nonneg _) (by linarith)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hb'
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hT0] at h
    linarith
  -- the intermediate value theorem
  have hτabs : |τ| ≤ τ := (abs_of_pos hτ0).le
  have hτabs' : |-τ| ≤ τ := by rw [abs_neg]; exact hτabs
  have hGp : Gs < G τ := by
    have h := hGdiff τ hτabs
    have h' : τ * μ ≤ G τ - G 0 := by
      have : τ * (τ * μ) ≤ τ * (G τ - G 0) := by linarith
      exact le_of_mul_le_mul_left this hτ0
    have := (abs_lt.mp hG0s).1
    linarith
  have hGm : G (-τ) < Gs := by
    have h := hGdiff (-τ) hτabs'
    have h' : G (-τ) - G 0 ≤ -(τ * μ) := by
      have : τ * (G (-τ) - G 0) ≤ τ * (-(τ * μ)) := by linarith
      exact le_of_mul_le_mul_left this hτ0
    have := (abs_lt.mp hG0s).2
    linarith
  obtain ⟨l, hl, hGl⟩ := intermediate_value_Icc (by linarith : -τ ≤ τ) hGc.continuousOn
    ⟨hGm.le, hGp.le⟩
  have hlτ : |l| ≤ τ := abs_le.mpr hl
  -- the corrected path `(q + λ c₁ β, p + λ c₁ β', z̃)` and control
  obtain ⟨ωr, hωr⟩ : ∃ f : ℝ → ℝ, ∀ t, f t = p t + l * (c₁ * β₁ t) := ⟨_, fun t => rfl⟩
  obtain ⟨δr, hδr⟩ : ∃ f : ℝ → ℝ, ∀ t, f t = q t + l * (c₁ * β t) := ⟨_, fun t => rfl⟩
  have hωrc : Continuous ωr := by
    rw [funext hωr]; exact hpc.add (continuous_const.mul (continuous_const.mul hβ₁c))
  have hδrc : Continuous δr := by
    rw [funext hδr]; exact hqc.add (continuous_const.mul (continuous_const.mul hβc))
  obtain ⟨Δ, hΔ⟩ : ∃ f : ℝ → ℝ, ∀ r, f r =
      Real.exp (κ * r) * (Real.sin (δr r - α) - Real.sin (Φ r 0 - α)) := ⟨_, fun r => rfl⟩
  have hΔc : Continuous Δ := by
    rw [funext hΔ]
    exact hexpc.mul ((Real.continuous_sin.comp (hδrc.sub continuous_const)).sub
      (Real.continuous_sin.comp (hΦ0c.sub continuous_const)))
  obtain ⟨R, hR⟩ : ∃ f : ℝ → ℝ, ∀ t, f t =
      Real.exp (-(κ * t)) * (κ * A * ∫ r in (0 : ℝ)..t, Δ r) := ⟨_, fun t => rfl⟩
  have hΦ2c : Continuous fun s => Φ s 2 := (continuous_apply 2).comp hΦc
  have hRc : Continuous R := by
    rw [funext hR]
    exact (by fun_prop : Continuous fun t : ℝ => Real.exp (-(κ * t))).mul
      (continuous_const.mul (intervalIntegral.continuous_primitive
        (fun a b => hΔc.intervalIntegrable a b) 0))
  obtain ⟨P, hP⟩ : ∃ f : ℝ → ℝ, ∀ t, f t = Φ t 2 + R t := ⟨_, fun t => rfl⟩
  have hPc : Continuous P := by rw [funext hP]; exact hΦ2c.add hRc
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → Fin 3 → ℝ, ∀ t, φ t = ![δr t, ωr t, P t] := ⟨_, fun t => rfl⟩
  have hφc : Continuous φ := by
    rw [funext hφ]
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa using hδrc
    · simpa using hωrc
    · simpa using hPc
  have hbφ1 : Continuous fun s => b (φ s) 1 := (continuous_apply 1).comp (hb.continuous.comp hφc)
  obtain ⟨gr, hgr⟩ : ∃ f : ℝ → ℝ, ∀ t, f t = g t + l * (c₁ * β₂ t) := ⟨_, fun t => rfl⟩
  obtain ⟨ũ, hũ⟩ : ∃ ũ : ℝ → Fin 1 → ℝ, ∀ t, ũ t = fun _ => (gr t - b (φ t) 1) / σ :=
    ⟨_, fun t => rfl⟩
  have hũ0 : ∀ t, ũ t 0 = (gr t - b (φ t) 1) / σ := fun t => by rw [hũ]
  have hcf : ∀ t, controlField b (fun _ (_ : Fin 1) => ![0, σ, 0]) (φ t) (ũ t) =
      ![ωr t, gr t, b (φ t) 2] := by
    intro t
    ext i
    fin_cases i
    · simp [controlField, hb0, hφ]
    · simp [controlField, hũ0]
      field_simp
      ring
    · simp [controlField]
  -- the right derivatives
  have hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt φ
      (controlField b (fun _ (_ : Fin 1) => ![0, σ, 0]) (φ t) (ũ t)) (Ici t) t := by
    intro t ht
    rw [hcf]
    refine hasDerivWithinAt_pi.mpr fun i => ?_
    have hpd : HasDerivWithinAt p (g t) (Ici t) t := by
      rw [funext hp]
      exact (intervalIntegral.integral_hasDerivWithinAt_right (hgi 0 t)
        hgm.aestronglyMeasurable.stronglyMeasurableAtFilter (hgrc t)).const_add (xA 1)
    have hqd : HasDerivAt q (p t) t := by
      rw [funext hq]
      exact ((hpc.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add (xA 0)
    have hωrd : HasDerivWithinAt ωr (gr t) (Ici t) t := by
      rw [funext hωr, hgr]
      exact hpd.add (((hβ₁d t).const_mul c₁).const_mul l).hasDerivWithinAt
    have hδrd : HasDerivAt δr (ωr t) t := by
      rw [funext hδr, hωr]
      exact hqd.add (((hβd t).const_mul c₁).const_mul l)
    have hΦ2d : HasDerivWithinAt (fun s => Φ s 2) (b (Φ t) 2) (Ici t) t := by
      have h1 := ((hb2c.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add
        (xA 2)).hasDerivWithinAt (s := Ici t)
      have hev : (fun s => Φ s 2) =ᶠ[𝓝[≥] t] fun s => xA 2 + ∫ r in (0 : ℝ)..s, b (Φ r) 2 := by
        filter_upwards [Ico_mem_nhdsGE ht.2] with s hs
        exact h2t s ⟨ht.1.trans hs.1, hs.2.le⟩
      exact h1.congr_of_eventuallyEq hev (h2t t (Ico_subset_Icc_self ht))
    have hRd : HasDerivAt R (-κ * R t +
        κ * A * (Real.sin (δr t - α) - Real.sin (Φ t 0 - α))) t := by
      have h1 : HasDerivAt (fun s => Real.exp (-(κ * s))) (Real.exp (-(κ * t)) * (-κ)) t := by
        have h0 : HasDerivAt (fun s : ℝ => -(κ * s)) (-κ) t := by
          have := ((hasDerivAt_id' t).const_mul κ).neg
          rw [mul_one] at this
          exact this
        exact h0.exp
      have h2 : HasDerivAt (fun s => κ * A * ∫ r in (0 : ℝ)..s, Δ r) (κ * A * Δ t) t :=
        ((hΔc.integral_hasStrictDerivAt 0 t).hasDerivAt).const_mul _
      have he : Real.exp (-(κ * t)) * Real.exp (κ * t) = 1 := by
        rw [← Real.exp_add]; simp
      have hfun : HasDerivAt R (Real.exp (-(κ * t)) * (-κ) * (κ * A * ∫ r in (0 : ℝ)..t, Δ r) +
          Real.exp (-(κ * t)) * (κ * A * Δ t)) t := by
        rw [funext hR]; exact h1.mul h2
      convert hfun using 1
      rw [hR t, hΔ t]
      linear_combination (-(κ * A * (Real.sin (δr t - α) - Real.sin (Φ t 0 - α)))) * he
    have hPd : HasDerivWithinAt P (b (φ t) 2) (Ici t) t := by
      rw [funext hP]
      refine (hΦ2d.add hRd.hasDerivWithinAt).congr_deriv ?_
      rw [hb2, hb2, hφ t]
      simp only [Matrix.cons_val_zero, Matrix.cons_val, Fin.isValue]
      rw [hP t]
      ring
    fin_cases i
    · simpa [hφ] using hδrd.hasDerivWithinAt
    · simpa [hφ] using hωrd
    · simpa [hφ] using hPd
  -- the endpoints
  have hstart : φ 0 = xA := by
    have hR0 : R 0 = 0 := by rw [hR]; simp
    have hΦ02 : Φ 0 2 = xA 2 := by rw [h2t 0 hT0mem]; simp
    ext i
    fin_cases i
    · simp [hφ, hδr, hq, hβ0.1]
    · simp [hφ, hωr, hp, hβ0.2]
    · simp [hφ, hP, hR0, hΦ02]
  have hpint : ∫ s in (0 : ℝ)..T, p s = ∫ s in (0 : ℝ)..T, Φ s 1 := by
    have hVc : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, v s) (uIcc 0 T) :=
      intervalIntegral.continuousOn_primitive_interval' hvi left_mem_uIcc
    have e1 : ∫ s in (0 : ℝ)..T, Φ s 1 = ∫ s in (0 : ℝ)..T, (xA 1 + ∫ r in (0 : ℝ)..s, v r) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [hIcc] at hs
      exact h1t s hs
    rw [e1, funext hp, intervalIntegral.integral_add intervalIntegrable_const
        ((intervalIntegral.continuous_primitive hgi 0).intervalIntegrable 0 T),
      intervalIntegral.integral_add intervalIntegrable_const hVc.intervalIntegrable, hm2]
  have hRT : R T = 0 := by
    have hΔint : ∫ r in (0 : ℝ)..T, Δ r = G l - Gs := by
      rw [hG l, hGs, ← intervalIntegral.integral_sub ((hsinc l).intervalIntegrable 0 T)
        (hsinΦc.intervalIntegrable 0 T)]
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [hΔ, hδr]
      ring
    rw [hR, hΔint, hGl, sub_self, mul_zero, mul_zero]
  have hend : φ T = Φ T := by
    ext i
    fin_cases i
    · simp only [hφ, Fin.zero_eta, Matrix.cons_val_zero]
      rw [hδr, hβT.1, mul_zero, mul_zero, add_zero, hq, h0t T hTmem, hpint]
    · simp only [hφ, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [hωr, hβT.2, mul_zero, mul_zero, add_zero, hp, h1t T hTmem, hm1]
    · simp only [hφ, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
      rw [hP, hRT, add_zero]
  -- the control is square integrable
  have hβ₂' : Continuous fun t => l * (c₁ * β₂ t) :=
    continuous_const.mul (continuous_const.mul hβ₂c)
  have hFc : Continuous fun t => l * (c₁ * β₂ t) - b (φ t) 1 := hβ₂'.sub hbφ1
  have hũ02 : IntervalIntegrable (fun t => ũ t 0 ^ 2) volume 0 T := by
    have e : (fun t => ũ t 0 ^ 2) = fun t =>
        (g t ^ 2 + 2 * (g t * (l * (c₁ * β₂ t) - b (φ t) 1)) +
          (l * (c₁ * β₂ t) - b (φ t) 1) ^ 2) / σ ^ 2 := by
      funext t; rw [hũ0, hgr]; field_simp; ring
    rw [e]
    exact (((hg2 0 T).add (((hgi 0 T).mul_continuousOn hFc.continuousOn).const_mul 2)).add
      ((hFc.pow 2).intervalIntegrable 0 T)).div_const _
  have hũ2 : IntervalIntegrable (fun t => ∑ j, ũ t j ^ 2) volume 0 T := by
    rw [hsq1]; exact hũ02
  have hQP : controlQuasiPotential b (fun _ (_ : Fin 1) => ![0, σ, 0]) xA (Φ T) ≤
      ENNReal.ofReal (controlAction ũ T) := by
    unfold controlQuasiPotential
    exact iInf_le_of_le (T : ℝ) (iInf_le_of_le φ (iInf_le_of_le ũ (iInf_le_of_le
      ⟨hT0, hstart, hend, hφc.continuousOn, hderiv, hũ2⟩ le_rfl)))
  -- the action estimate
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → ℝ, ∀ s, ψ s = b (φ s) 1 - b (Φ s) 1 := ⟨_, fun s => rfl⟩
  have hψc : Continuous ψ := by rw [funext hψ]; exact hbφ1.sub hb1
  have hdiff : ∀ s, ũ s 0 - u s 0 = ((g s - v s) + l * (c₁ * β₂ s) - ψ s) / σ := by
    intro s; rw [hũ0, hψ, hv, hgr]; field_simp; ring
  have hlc : |l * c₁| ≤ τ := by
    rw [abs_mul]
    calc |l| * |c₁| ≤ τ * 1 := mul_le_mul hlτ hc₁le (abs_nonneg _) hτ0.le
      _ = τ := mul_one τ
  have hδb : ∀ s ∈ Icc (0 : ℝ) T, |δr s - Φ s 0| ≤ 2 * τ := by
    intro s hs
    rw [hδr, show q s + l * (c₁ * β s) - Φ s 0 = (q s - Φ s 0) + (l * c₁) * β s by ring]
    have h1 : |(l * c₁) * β s| ≤ τ := by
      rw [abs_mul, abs_of_nonneg (hβ01 s).1]
      calc |l * c₁| * β s ≤ τ * 1 := mul_le_mul hlc (hβ01 s).2 (hβ01 s).1 hτ0.le
        _ = τ := mul_one τ
    linarith [abs_add_le (q s - Φ s 0) ((l * c₁) * β s), hqb s hs]
  have hωb : ∀ s ∈ Icc (0 : ℝ) T, |ωr s - Φ s 1| ≤ τ * (1 + B₁) := by
    intro s hs
    rw [hωr, show p s + l * (c₁ * β₁ s) - Φ s 1 = (p s - Φ s 1) + (l * c₁) * β₁ s by ring]
    have h1 : |(l * c₁) * β₁ s| ≤ τ * B₁ := by
      rw [abs_mul]
      exact mul_le_mul hlc (by simpa [Real.norm_eq_abs] using hB₁ s hs) (abs_nonneg _) hτ0.le
    have e : τ * (1 + B₁) = τ + τ * B₁ := by ring
    linarith [abs_add_le (p s - Φ s 1) ((l * c₁) * β₁ s), hpb s hs]
  have hRb : ∀ s ∈ Icc (0 : ℝ) T, |R s| ≤ 2 * E₁ ^ 2 * |κ * A| * T * τ := by
    intro s hs
    have hΔb : ∀ r ∈ uIoc (0 : ℝ) s, ‖Δ r‖ ≤ E₁ * (2 * τ) := by
      intro r hr
      rw [uIoc_of_le hs.1] at hr
      have hr' : r ∈ Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.trans hs.2⟩
      rw [hΔ, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have h1 := Real.abs_sin_sub_sin_le (δr r - α) (Φ r 0 - α)
      rw [show δr r - α - (Φ r 0 - α) = δr r - Φ r 0 by ring] at h1
      exact mul_le_mul (hE r hr').1 (h1.trans (hδb r hr')) (abs_nonneg _) (by linarith)
    have hint3 := intervalIntegral.norm_integral_le_of_norm_le_const hΔb
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs.1] at hint3
    rw [hR, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
    have h4 : |∫ r in (0 : ℝ)..s, Δ r| ≤ E₁ * (2 * τ) * T :=
      hint3.trans (mul_le_mul_of_nonneg_left hs.2 (by positivity))
    calc Real.exp (-(κ * s)) * (|κ * A| * |∫ r in (0 : ℝ)..s, Δ r|)
        ≤ E₁ * (|κ * A| * (E₁ * (2 * τ) * T)) :=
          mul_le_mul (hE s hs).2.1 (mul_le_mul_of_nonneg_left h4 (abs_nonneg _))
            (by positivity) (by linarith)
      _ = 2 * E₁ ^ 2 * |κ * A| * T * τ := by ring
  have hψb : ∀ s ∈ Icc (0 : ℝ) T, |ψ s| ≤ K * (Ce * τ) := by
    intro s hs
    have h1 : |ψ s| ≤ K * ‖φ s - Φ s‖ := by
      rw [hψ]
      have h0 := hb.norm_sub_le (φ s) (Φ s)
      have h2 : ‖(b (φ s) - b (Φ s)) 1‖ ≤ ‖b (φ s) - b (Φ s)‖ := norm_le_pi_norm _ 1
      rw [Pi.sub_apply, Real.norm_eq_abs] at h2
      linarith
    have h3 : ‖φ s - Φ s‖ ≤ Ce * τ := by
      have hce : Ce * τ = 2 * τ + τ * (1 + B₁) + 2 * E₁ ^ 2 * |κ * A| * T * τ := by
        rw [hCe]; ring
      have hδ := hδb s hs
      have hω := hωb s hs
      have hRs := hRb s hs
      have hn0 : 0 ≤ 2 * τ := by positivity
      have hn1 : 0 ≤ τ * (1 + B₁) := by positivity
      have hn2 : 0 ≤ 2 * E₁ ^ 2 * |κ * A| * T * τ := by positivity
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
      fin_cases i
      · simp only [hφ, Pi.sub_apply, Fin.zero_eta, Matrix.cons_val_zero, Real.norm_eq_abs]
        linarith
      · simp only [hφ, Pi.sub_apply, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
          Real.norm_eq_abs]
        linarith
      · simp only [hφ, Pi.sub_apply, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue,
          Real.norm_eq_abs, hP, add_sub_cancel_left]
        linarith
    exact h1.trans (mul_le_mul_of_nonneg_left h3 K.coe_nonneg)
  have hFψ : Continuous fun s => l * (c₁ * β₂ s) - ψ s := hβ₂'.sub hψc
  have hd2 : IntervalIntegrable (fun s => (ũ s 0 - u s 0) ^ 2) volume 0 T := by
    have e : (fun s => (ũ s 0 - u s 0) ^ 2) = fun s =>
        ((g s - v s) ^ 2 + 2 * ((g s - v s) * (l * (c₁ * β₂ s) - ψ s)) +
          (l * (c₁ * β₂ s) - ψ s) ^ 2) / σ ^ 2 := by
      funext s; rw [hdiff]; field_simp; ring
    rw [e]
    exact ((hgv2.add ((((hgi 0 T).sub hvi).mul_continuousOn hFψ.continuousOn).const_mul 2)).add
      ((hFψ.pow 2).intervalIntegrable 0 T)).div_const _
  have hd : ∫ s in (0 : ℝ)..T, (ũ s 0 - u s 0) ^ 2 ≤ C₁ * τ ^ 2 := by
    calc ∫ s in (0 : ℝ)..T, (ũ s 0 - u s 0) ^ 2
        ≤ ∫ s in (0 : ℝ)..T, 3 / σ ^ 2 * ((g s - v s) ^ 2 +
            ((τ * B₂) ^ 2 + (K * (Ce * τ)) ^ 2)) := by
          refine intervalIntegral.integral_mono_on hT0 hd2
            ((hgv2.add intervalIntegrable_const).const_mul _) fun s hs => ?_
          have hb₂ : (l * (c₁ * β₂ s)) ^ 2 ≤ (τ * B₂) ^ 2 := by
            rw [← sq_abs, ← mul_assoc]
            refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
            rw [abs_mul]
            exact mul_le_mul hlc (by simpa [Real.norm_eq_abs] using hB₂ s hs) (abs_nonneg _)
              hτ0.le
          have hψ2 : ψ s ^ 2 ≤ (K * (Ce * τ)) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hψb s hs) 2
          have h3 := sq_add_sub_le_three (g s - v s) (l * (c₁ * β₂ s)) (ψ s)
          rw [hdiff, div_pow,
            show 3 / σ ^ 2 * ((g s - v s) ^ 2 + ((τ * B₂) ^ 2 + (K * (Ce * τ)) ^ 2)) =
              3 * ((g s - v s) ^ 2 + ((τ * B₂) ^ 2 + (K * (Ce * τ)) ^ 2)) / σ ^ 2 by ring]
          exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg σ)
      _ = 3 / σ ^ 2 * ((∫ s in (0 : ℝ)..T, (g s - v s) ^ 2) +
            T * ((τ * B₂) ^ 2 + (K * (Ce * τ)) ^ 2)) := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_add hgv2 intervalIntegrable_const,
            intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      _ ≤ 3 / σ ^ 2 * (τ ^ 2 + T * ((τ * B₂) ^ 2 + (K * (Ce * τ)) ^ 2)) := by
          gcongr
          exact hgv.trans hε₀a.2.2
      _ = C₁ * τ ^ 2 := by rw [hC₁]; ring
  have hY := integral_sq_le_add hT0 hũ02 hu02 hd2 hθ0
  rw [← hAu] at hY
  have hfin : ∫ s in (0 : ℝ)..T, ũ s 0 ^ 2 ≤ Au + 2 * η := by
    have h1 : θ * Au ≤ η := by
      have hA1 : Au / (Au + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
      calc θ * Au = η * (Au / (Au + 1)) := by rw [hθ]; ring
        _ ≤ η * 1 := mul_le_mul_of_nonneg_left hA1 hη.le
        _ = η := mul_one η
    have h2 : (1 + 1 / θ) * (∫ s in (0 : ℝ)..T, (ũ s 0 - u s 0) ^ 2) ≤ η := by
      calc _ ≤ (1 + 1 / θ) * (C₁ * τ ^ 2) := mul_le_mul_of_nonneg_left hd (by positivity)
        _ = C₂ * τ ^ 2 := by rw [hC₂]; ring
        _ ≤ η := hC₂τ
    linarith
  have hcaũ : controlAction ũ T = 1 / 2 * ∫ s in (0 : ℝ)..T, ũ s 0 ^ 2 := by
    unfold controlAction; rw [hsq1]
  have hcau : controlAction u T = 1 / 2 * Au := by
    unfold controlAction; rw [hsq1, hAu]
  calc _ ≤ ENNReal.ofReal (controlAction ũ T) := hQP
    _ ≤ ENNReal.ofReal (controlAction u T + η) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hcaũ, hcau]; linarith
    _ = ENNReal.ofReal (controlAction u T) + ε := by
        rw [ENNReal.ofReal_add (by rw [hcau]; positivity) hη.le, hηdef,
          ENNReal.ofReal_coe_nnreal]

/-! ## The quasi-potential of the rate -/

/-- **Regularisation keeping all three endpoints**: for `w = ∫ u` with `u` square integrable, the
controlled quasi-potential from `x_A` to the endpoint of `x = solMap w` is at most `½ ∫₀ᵀ u²`. -/
@[tmio T, powerlib_foundation] theorem controlQuasiPotential_le_controlAction_filter {K : ℝ≥0}
    {b : (Fin 3 → ℝ) → Fin 3 → ℝ} (hb : LipschitzWith K b) (hb0 : ∀ y, b y 0 = y 1)
    {κ a₀ A α : ℝ} (hb2 : ∀ y, b y 2 = κ * (a₀ + A * Real.sin (y 0 - α) - y 2))
    {σ : ℝ} (hσ : σ ≠ 0) (xA : Fin 3 → ℝ) {u : ℝ → Fin 1 → ℝ}
    (hu : IntervalIntegrable u volume 0 T)
    (hu2 : IntervalIntegrable (fun t => ∑ j, u t j ^ 2) volume 0 T)
    {w : C(Icc (0 : ℝ) T, Fin 1 → ℝ)} (hw : ∀ t : Icc (0 : ℝ) T, w t = ∫ s in (0 : ℝ)..t, u s) :
    controlQuasiPotential b (fun _ (_ : Fin 1) => ![0, σ, 0]) xA
        (solMap b (columnsCLM fun _ : Fin 1 => ![0, σ, 0]) xA w
          ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩) ≤
      ENNReal.ofReal (controlAction u T) := by
  have hT0 := T.coe_nonneg
  rcases eq_or_lt_of_le hT0 with hT | hT
  · have hend : solMap b (columnsCLM fun _ : Fin 1 => ![0, σ, 0]) xA w
        ⟨T, right_mem_Icc.mpr hT0⟩ = xA := by
      rw [solMap_spec hb, hw]
      simp [← hT]
    rw [hend]
    have h0 : controlQuasiPotential b (fun _ (_ : Fin 1) => ![0, σ, 0]) xA xA ≤ 0 := by
      unfold controlQuasiPotential
      refine iInf_le_of_le 0 (iInf_le_of_le (fun _ => xA) (iInf_le_of_le (fun _ _ => 0)
        (iInf_le_of_le ⟨le_rfl, rfl, rfl, continuousOn_const,
          fun t ht => absurd ht.2 (not_lt.mpr ht.1), by simp⟩ ?_)))
      simp [controlAction]
    exact h0.trans zero_le
  have hint : ∀ t ∈ Icc (0 : ℝ) T,
      pathExt (solMap b (columnsCLM fun _ : Fin 1 => ![0, σ, 0]) xA w) t =
        xA + ∫ s in (0 : ℝ)..t, (columnsCLM (fun _ : Fin 1 => ![(0 : ℝ), σ, 0]) (u s) +
          b (pathExt (solMap b (columnsCLM fun _ : Fin 1 => ![0, σ, 0]) xA w) s)) :=
    fun t ht => pathExt_solMap_of_primitive hb _ xA hu hw ht
  have hΦc := continuous_pathExt (solMap b (columnsCLM fun _ : Fin 1 => ![0, σ, 0]) xA w)
  rw [← pathExt_of_mem (solMap b (columnsCLM fun _ : Fin 1 => ![0, σ, 0]) xA w)
    (right_mem_Icc.mpr hT0)]
  generalize pathExt (solMap b (columnsCLM fun _ : Fin 1 => ![0, σ, 0]) xA w) = Φ at hint hΦc ⊢
  by_cases hdeg : ∀ t ∈ Ioo (0 : ℝ) T, Real.cos (Φ t 0 - α) = 0
  · exact controlQuasiPotential_le_of_cos_eq_zero hb hb0 hσ α xA hu hT hΦc hint hdeg
  · push Not at hdeg
    obtain ⟨t₁, ht₁, hc₁⟩ := hdeg
    exact controlQuasiPotential_le_of_cos_ne_zero hb hb0 hb2 hσ xA hu hu2 hT hΦc hint ht₁ hc₁

/-- The noise row is recovered from the column `(0, σ, 0)`: `L x = x₁/σ`. -/
@[tmio T, powerlib_foundation] theorem leftInverse_filter {σ : ℝ} (hσ : σ ≠ 0) :
    ∃ L : (Fin 3 → ℝ) →L[ℝ] Fin 1 → ℝ,
      ∀ v, L (columnsCLM (fun _ : Fin 1 => ![(0 : ℝ), σ, 0]) v) = v := by
  refine ⟨ContinuousLinearMap.pi fun _ => σ⁻¹ • ContinuousLinearMap.proj 1, fun v => ?_⟩
  ext j
  fin_cases j
  simp [columnsCLM_filter]
  field_simp

/-- **The controlled quasi-potential is below the rate** (three states):
`V(x_A, φ(T)) ≤ J_T(φ)` for every path `φ` on `[0, T]`. -/
@[tmio T, powerlib_foundation] theorem controlQuasiPotential_le_fwRate_filter {K : ℝ≥0}
    {b : (Fin 3 → ℝ) → Fin 3 → ℝ} (hb : LipschitzWith K b) (hb0 : ∀ y, b y 0 = y 1)
    {κ a₀ A α : ℝ} (hb2 : ∀ y, b y 2 = κ * (a₀ + A * Real.sin (y 0 - α) - y 2))
    {σ : ℝ} (hσ : σ ≠ 0) (xA : Fin 3 → ℝ) (φ : C(Icc (0 : ℝ) T, Fin 3 → ℝ)) :
    controlQuasiPotential b (fun _ (_ : Fin 1) => ![0, σ, 0]) xA
        (φ ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩) ≤
      fwRate b (fun _ : Fin 1 => ![0, σ, 0]) xA T φ := by
  unfold fwRate pushRate
  refine le_iInf₂ fun w hw => ?_
  subst hw
  unfold schilderRate
  refine le_iInf₂ fun u hu => ?_
  exact controlQuasiPotential_le_controlAction_filter hb hb0 hb2 hσ xA hu.1 hu.2.1 hu.2.2

/-- **The quasi-potential of the rate is the controlled quasi-potential** (three states):
`inf_T inf {J_T(φ) : φ(T) = x} = V(x_A, x)` for all endpoints. -/
@[tmio T, powerlib_foundation] theorem fwQP_eq_controlQuasiPotential_filter {K : ℝ≥0}
    {b : (Fin 3 → ℝ) → Fin 3 → ℝ} (hb : LipschitzWith K b) (hb0 : ∀ y, b y 0 = y 1)
    {κ a₀ A α : ℝ} (hb2 : ∀ y, b y 2 = κ * (a₀ + A * Real.sin (y 0 - α) - y 2))
    {σ : ℝ} (hσ : σ ≠ 0) (xA x : Fin 3 → ℝ) :
    ⨅ (T : ℝ≥0) (φ : C(Icc (0 : ℝ) T, Fin 3 → ℝ))
        (_ : φ ⟨T, right_mem_Icc.mpr T.coe_nonneg⟩ = x),
        fwRate b (fun _ : Fin 1 => ![0, σ, 0]) xA T φ =
      controlQuasiPotential b (fun _ (_ : Fin 1) => ![0, σ, 0]) xA x := by
  refine le_antisymm ?_ (le_iInf fun T => le_iInf fun φ => le_iInf fun hφ => by
    subst hφ; exact controlQuasiPotential_le_fwRate_filter hb hb0 hb2 hσ xA φ)
  obtain ⟨L, hL⟩ := leftInverse_filter hσ
  unfold controlQuasiPotential
  refine le_iInf fun T' => le_iInf fun φ => le_iInf fun u => le_iInf fun hadm => ?_
  obtain ⟨hT, h0, hTx, hc, hφ, hu⟩ := hadm
  let y : C(Icc (0 : ℝ) (⟨T', hT⟩ : ℝ≥0), Fin 3 → ℝ) := ⟨_, hc.domRestrict⟩
  refine iInf_le_of_le ⟨T', hT⟩ (iInf_le_of_le y (iInf_le_of_le hTx ?_))
  exact fwRate_le_controlAction (T := ⟨T', hT⟩) hb _ h0 hc hφ
    (intervalIntegrable_of_admissible hb _ hL hc hφ hu) hu fun t => rfl

end powerlib.Stochastic.LDP
