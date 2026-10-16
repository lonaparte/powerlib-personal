import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import theorem.Dynamics.Linearization
import theorem.Dynamics.State

/-! # Locality of stability and linearization (foundation)

Local exponential stability, Lyapunov stability, local asymptotic stability and instability of an
equilibrium depend only on the vector field near the equilibrium; the indirect method therefore
holds for fields that are `C¹` only near the point.

Scope.
* Generic facts about autonomous ODEs `ẋ = f x` on `Dynamics.State n = EuclideanSpace ℝ (Fin n)`
  (continuous time, no input; the library's segment semantics), not engineering conclusions.

Source: standard (Khalil, *Nonlinear Systems*, Thm 4.7 is stated for `C¹` on a domain);
needed by work-sync `theory/T-vsc-dc-voltage-control.md` §1.1, §1.4, and as infrastructure for
work-sync `projects/vsc-parametric-oscillation` and `projects/gfl-gfm-stability-tree` (ball form,
`invExt`, `regDen`).

Results.
* Curve transfer: `isIntegralCurveOn_of_eq_on_curve` (an integral curve of `g` along which
  `g = f` is one of `f`), `isTrajectoryOn_of_eqOn` (its solution-segment instance), and
  `eventuallyEq_of_eqOn_ball` (agreement on a ball is agreement near its centre).
* Neighbourhood (filter) form: `locallyExponentiallyStable_congr_nhds`, `lyapunovStable_congr_nhds`,
  `unstable_congr_nhds`, `localAsymptoticStable_congr_nhds`: if `f = g` on a neighbourhood of
  `x_eq` the properties transfer (first-exit argument with `exists_first_sphere_hit`).
* Ball form, the corollaries for `f = g` on `‖y − x‖ < ρ`:
  `locallyExponentiallyStable_of_eqOn_ball`, `lyapunovStable_of_eqOn_ball`,
  `unstable_of_eqOn_ball`, `localAsymptoticStable_of_eqOn_ball`.
* First-exit and bootstrap arguments on finite solution segments: `forall_lt_of_first_exit`,
  `forall_norm_sub_lt_of_bootstrap`, `exp_bound_of_local` (an exponential estimate transfers to a
  curve that solves `ẋ = G x` while it stays in a ball).
* Extensions: `exists_contDiff_eventuallyEq`, `exists_contDiff_ball` (a field that is `C¹` on an
  open set `U ∋ x` agrees near `x` with a globally `C¹` field: multiply by a smooth bump supported
  in `U`), `exists_contDiff_lipschitz_extension` (a `C¹` field agrees on a ball with a `C¹`,
  globally Lipschitz field).
* Lyapunov's indirect method for fields that are `C¹` only on an open neighbourhood of the
  equilibrium (`locallyExponentiallyStable_of_isHurwitz_jacobian_local`,
  `unstable_of_jacobian_eigenvalue_re_pos_local`), or that agree near it with a globally `C¹`
  field (`locallyExponentiallyStable_of_isHurwitz_jacobian_of_eqOn_ball`,
  `unstable_of_jacobian_eigenvalue_re_pos_of_eqOn_ball`), which the global-`ContDiff` wrappers of
  `theorem/Dynamics/Linearization.lean` do not cover. Typical use: power-balance fields with a
  `1/V_dc` factor, which are smooth only on `V_dc > 0`.
* Smooth regularizations of a denominator away from zero: `invDen`, `invExt` (a globally smooth
  function equal to `V⁻¹` for `V ≥ 1/2`) and `regDen V` (equal to `v` for `v ≥ 3V/4`, at least
  `V/2` everywhere).
-/

noncomputable section
namespace powerlib.Dynamics

/-! ## Curve transfer -/

section Transfer

open Set Filter Topology Metric

variable {n : ℕ}
local notation "ℝⁿ" => State n

/-- An integral curve of `g` along which `g` and `f` coincide is an integral curve of `f`. -/
@[powerlib_foundation] theorem isIntegralCurveOn_of_eq_on_curve {f g : ℝⁿ → ℝⁿ}
    {ψ : ℝ → ℝⁿ} {s : Set ℝ} (hψ : IsIntegralCurveOn ψ (fun _ x => g x) s)
    (h : ∀ t ∈ s, g (ψ t) = f (ψ t)) : IsIntegralCurveOn ψ (fun _ x => f x) s := by
  intro t ht
  show HasDerivWithinAt ψ (f (ψ t)) s t
  rw [← h t ht]
  exact hψ t ht

/-- A solution segment of `f` along which `f` and `g` coincide is a solution segment of `g`. -/
@[powerlib_foundation] theorem isTrajectoryOn_of_eqOn {f g : Dynamics.State n → Dynamics.State n}
    {φ : ℝ → Dynamics.State n} {a b : ℝ} (hφ : IsTrajectoryOn φ f a b)
    (h : ∀ t ∈ Icc a b, f (φ t) = g (φ t)) : IsTrajectoryOn φ g a b :=
  isIntegralCurveOn_of_eq_on_curve hφ h

/-- Agreement on the ball `‖y − x‖ < ρ` is agreement near `x`. -/
@[powerlib_foundation] theorem eventuallyEq_of_eqOn_ball {E F : Type*} [SeminormedAddCommGroup E]
    {f g : E → F} {x : E} {ρ : ℝ} (hρ : 0 < ρ) (hfg : ∀ y, ‖y - x‖ < ρ → f y = g y) :
    f =ᶠ[𝓝 x] g :=
  Filter.eventually_of_mem (Metric.ball_mem_nhds x hρ) fun y hy =>
    hfg y (by simpa [dist_eq_norm] using hy)

end Transfer

/-! ## Locality in a neighbourhood -/

section Nhds

open Set Filter Metric Matrix
open scoped Topology

variable {n : ℕ}
local notation "Sₙ" => Dynamics.State n

/-- Local exponential stability depends only on the field near the equilibrium. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_congr_nhds {f g : Sₙ → Sₙ}
    {x : Sₙ} (hfg : f =ᶠ[𝓝 x] g) (hg : LocallyExponentiallyStable g x) :
    LocallyExponentiallyStable f x := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hfg
  have hfg' : ∀ y, ‖y - x‖ < ρ → f y = g y := fun y hy => hball (by simpa [dist_eq_norm] using hy)
  obtain ⟨r, C, a, hr, hC, ha, hb⟩ := hg
  have hC0 : 0 < C := by linarith
  refine ⟨min r (ρ / (2 * C)), C, a, lt_min hr (by positivity), hC, ha, ?_⟩
  intro t₀ t₁ φ hφ h0 t ht
  have h0r : ‖φ t₀ - x‖ < r := h0.trans_le (min_le_left _ _)
  have h0ρ : ‖φ t₀ - x‖ < ρ / (2 * C) := h0.trans_le (min_le_right _ _)
  have hCρ : C * (ρ / (2 * C)) = ρ / 2 := by field_simp
  -- the solution never reaches the sphere of radius `ρ/2`
  have hstay : ∀ s ∈ Icc t₀ t₁, ‖φ s - x‖ < ρ / 2 := by
    intro s hs
    by_contra hfar0
    have hfar := not_lt.mp hfar0
    have hρ0 : ‖φ t₀ - x‖ < ρ / 2 := by
      have : ρ / (2 * C) ≤ ρ / 2 := div_le_div_of_nonneg_left hρ.le (by norm_num) (by linarith)
      linarith
    obtain ⟨τ, hτ, hτeq, hτin⟩ :=
      _root_.exists_first_sphere_hit hφ.continuousOn hρ0 hs hfar
    have hg' : IsTrajectoryOn φ g t₀ τ :=
      isTrajectoryOn_of_eqOn (hφ.mono (Icc_subset_Icc_right hτ.2)) fun s hs =>
        hfg' _ ((hτin s hs).trans_lt (by linarith))
    have hbound := hb t₀ τ φ hg' h0r τ ⟨hτ.1, le_rfl⟩
    have hexp : Real.exp (-a * (τ - t₀)) ≤ 1 := Real.exp_le_one_iff.mpr
      (by nlinarith [hτ.1])
    have : C * Real.exp (-a * (τ - t₀)) * ‖φ t₀ - x‖ < ρ / 2 := by
      calc C * Real.exp (-a * (τ - t₀)) * ‖φ t₀ - x‖ ≤ C * ‖φ t₀ - x‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            nlinarith [Real.exp_pos (-a * (τ - t₀))]
        _ < C * (ρ / (2 * C)) := mul_lt_mul_of_pos_left h0ρ hC0
        _ = ρ / 2 := hCρ
    linarith
  have hg' : IsTrajectoryOn φ g t₀ t₁ :=
    isTrajectoryOn_of_eqOn hφ fun s hs => hfg' _ ((hstay s hs).trans (by linarith))
  exact hb t₀ t₁ φ hg' h0r t ht

/-- Lyapunov stability depends only on the field near the equilibrium. -/
@[powerlib_foundation] theorem lyapunovStable_congr_nhds {f g : Sₙ → Sₙ}
    {x : Sₙ} (hfg : f =ᶠ[𝓝 x] g) (hg : LyapunovStable g x) : LyapunovStable f x := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hfg
  have hfg' : ∀ y, ‖y - x‖ < ρ → f y = g y := fun y hy => hball (by simpa [dist_eq_norm] using hy)
  intro ε hε
  set ε' := min ε (ρ / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by positivity)
  obtain ⟨δ, hδ, hb⟩ := hg ε' hε'0
  refine ⟨min δ ε', lt_min hδ hε'0, ?_⟩
  intro t₀ t₁ φ hφ h0 t ht
  have h0δ : ‖φ t₀ - x‖ < δ := h0.trans_le (min_le_left _ _)
  have h0ε : ‖φ t₀ - x‖ < ε' := h0.trans_le (min_le_right _ _)
  have hερ : ε' < ρ := (min_le_right _ _).trans_lt (by linarith)
  have hstay : ∀ s ∈ Icc t₀ t₁, ‖φ s - x‖ < ε' := by
    intro s hs
    by_contra hfar0
    have hfar := not_lt.mp hfar0
    obtain ⟨τ, hτ, hτeq, hτin⟩ := _root_.exists_first_sphere_hit hφ.continuousOn h0ε hs hfar
    have hg' : IsTrajectoryOn φ g t₀ τ :=
      isTrajectoryOn_of_eqOn (hφ.mono (Icc_subset_Icc_right hτ.2)) fun s hs =>
        hfg' _ ((hτin s hs).trans_lt hερ)
    have := hb t₀ τ φ hg' h0δ τ ⟨hτ.1, le_rfl⟩
    linarith
  exact (hstay t ht).trans_le (min_le_left _ _)

/-- Instability depends only on the field near the equilibrium. -/
@[powerlib_foundation] theorem unstable_congr_nhds {f g : Sₙ → Sₙ} {x : Sₙ}
    (hfg : f =ᶠ[𝓝 x] g) : Unstable f x ↔ Unstable g x :=
  ⟨fun hf hg => hf (lyapunovStable_congr_nhds hfg hg),
    fun hg hf => hg (lyapunovStable_congr_nhds hfg.symm hf)⟩

/-- A field that is `C¹` on an open neighbourhood of `x` agrees near `x` with a global `C¹`
field. -/
@[powerlib_foundation] theorem exists_contDiff_eventuallyEq {f : Sₙ → Sₙ}
    {U : Set (Sₙ)} (hU : IsOpen U) {x : Sₙ} (hx : x ∈ U)
    (hf : ContDiffOn ℝ 1 f U) :
    ∃ g : Sₙ → Sₙ, ContDiff ℝ 1 g ∧ g =ᶠ[𝓝 x] f := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hx
  let b : ContDiffBump x := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  refine ⟨fun y => b y • f y, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · exact b.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hy))
    · have hnot : y ∉ tsupport b := by
        rw [b.tsupport_eq]
        intro hyb
        apply hy
        apply hεU
        rw [mem_ball]
        exact (mem_closedBall.mp hyb).trans_lt (by simp [b]; linarith)
      have hzero : (fun y => b y • f y) =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with z hz
        simp [hz]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  · filter_upwards [Metric.ball_mem_nhds x (show (0 : ℝ) < ε / 4 by positivity)] with y hy
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), one_smul]

/-- Lyapunov indirect method for a field that is `C¹` only on an open neighbourhood. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_of_isHurwitz_jacobian_local
    {f : Sₙ → Sₙ} {x_eq : Sₙ} {U : Set (Sₙ)} (hU : IsOpen U)
    (hx : x_eq ∈ U) (A : Matrix (Fin n) (Fin n) ℝ) (hf : ContDiffOn ℝ 1 f U)
    (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hA : LinearSystems.IsHurwitz A) : LocallyExponentiallyStable f x_eq := by
  obtain ⟨g, hg, hgf⟩ := exists_contDiff_eventuallyEq hU hx hf
  refine locallyExponentiallyStable_congr_nhds hgf.symm ?_
  exact Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian A hg
    (by rw [hgf.eq_of_nhds, heq]) (by rw [hgf.fderiv_eq, hJac]) hA

/-- Instability from a Jacobian eigenvalue with positive real part, local `C¹` version. -/
@[powerlib_foundation] theorem unstable_of_jacobian_eigenvalue_re_pos_local
    {f : Sₙ → Sₙ} {x_eq : Sₙ} {U : Set (Sₙ)} (hU : IsOpen U)
    (hx : x_eq ∈ U) (A : Matrix (Fin n) (Fin n) ℝ) (hf : ContDiffOn ℝ 1 f U)
    (heq : f x_eq = 0)
    (hJac : fderiv ℝ f x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hunstable : ∃ (μ : ℂ) (v : Fin n → ℂ),
      v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re) :
    Unstable f x_eq := by
  obtain ⟨g, hg, hgf⟩ := exists_contDiff_eventuallyEq hU hx hf
  rw [unstable_congr_nhds hgf.symm]
  exact Dynamics.unstable_of_jacobian_eigenvalue_re_pos A hg
    (by rw [hgf.eq_of_nhds, heq]) (by rw [hgf.fderiv_eq, hJac]) hunstable

end Nhds

section NhdsLAS

open Set Filter Topology Metric

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- Local asymptotic stability depends only on the field near the point. -/
@[powerlib_foundation] theorem localAsymptoticStable_congr_nhds {f g : ℝⁿ → ℝⁿ} {x : ℝⁿ}
    (hfg : f =ᶠ[𝓝 x] g) (hg : LocalAsymptoticStable g x) : LocalAsymptoticStable f x := by
  obtain ⟨hgLS, c, hc, hconv⟩ := hg
  have hfLS : LyapunovStable f x := lyapunovStable_congr_nhds hfg hgLS
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hfg
  obtain ⟨δ, hδ, hb⟩ := hfLS ρ hρ
  refine ⟨hfLS, min c δ, lt_min hc hδ, fun t₀ φ hφ h0 => ?_⟩
  have hin : ∀ t, t₀ ≤ t → ‖φ t - x‖ < ρ := fun t ht =>
    hb t₀ t φ (hφ.mono Icc_subset_Ici_self) (h0.trans_le (min_le_right _ _)) t ⟨ht, le_rfl⟩
  exact hconv t₀ φ (isIntegralCurveOn_of_eq_on_curve hφ fun t ht =>
    hball (by rw [dist_eq_norm]; exact hin t ht)) (h0.trans_le (min_le_left _ _))

/-- A field that is `C¹` on an open neighbourhood `U` of `x` agrees near `x` with a globally `C¹`
field, on a ball contained in `U`. -/
@[powerlib_foundation] theorem exists_contDiff_ball {f : ℝⁿ → ℝⁿ} {U : Set ℝⁿ} (hU : IsOpen U)
    {x : ℝⁿ} (hx : x ∈ U) (hf : ContDiffOn ℝ 1 f U) :
    ∃ g : ℝⁿ → ℝⁿ, ContDiff ℝ 1 g ∧ g =ᶠ[𝓝 x] f ∧
      ∃ σ > 0, ∀ y, ‖y - x‖ < σ → g y = f y ∧ y ∈ U := by
  obtain ⟨g, hg, hgf⟩ := exists_contDiff_eventuallyEq hU hx hf
  obtain ⟨σ, hσ, hball⟩ := Metric.eventually_nhds_iff.mp (hgf.and (hU.mem_nhds hx))
  exact ⟨g, hg, hgf, σ, hσ, fun y hy => hball (by rw [dist_eq_norm]; exact hy)⟩

end NhdsLAS

/-! ## Globally Lipschitz cutoff -/

section Cutoff

open Set Filter Topology Metric
open scoped Pointwise

variable {n : ℕ}
local notation "ℝⁿ" => State n

/-- A `C¹` field agrees on `‖x‖ ≤ R` with a `C¹`, globally Lipschitz field. -/
@[powerlib_foundation] theorem exists_contDiff_lipschitz_extension {f : ℝⁿ → ℝⁿ}
    (hf : ContDiff ℝ 1 f) (R : ℝ) :
    ∃ g : ℝⁿ → ℝⁿ, ContDiff ℝ 1 g ∧ (∃ K, LipschitzWith K g) ∧
      ∀ x, ‖x‖ ≤ R → g x = f x := by
  let b : ContDiffBump (0 : ℝⁿ) :=
    ⟨max R 1, max R 1 + 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), by linarith⟩
  have hsmooth : ContDiff ℝ 1 (fun x => b x • f x) := b.contDiff.smul hf
  refine ⟨fun x => b x • f x, hsmooth, ?_, ?_⟩
  · exact ContDiff.lipschitzWith_of_hasCompactSupport b.hasCompactSupport.smul_right hsmooth
      (by norm_num)
  · intro x hx
    have hb : b x = 1 := by
      apply b.one_of_mem_closedBall
      rw [mem_closedBall, dist_zero_right]
      exact hx.trans (le_max_left _ _)
    simp only [hb, one_smul]

end Cutoff

/-! ## Locality on a ball -/

section Ball

open Set Filter Topology Matrix

variable {n : ℕ}

/-- First-exit argument for a continuous function of a curve: if `Φ ∘ φ` starts below `c` and is
below `c` at every `s` up to which it has stayed at most `c`, it stays below `c`. -/
@[powerlib_foundation] theorem forall_lt_of_first_exit {E : Type*} [TopologicalSpace E]
    {φ : ℝ → E} {Φ : E → ℝ} {t₀ t₁ c : ℝ} (hΦ : Continuous Φ) (hφ : ContinuousOn φ (Icc t₀ t₁))
    (h0 : Φ (φ t₀) < c)
    (hstep : ∀ s ∈ Icc t₀ t₁, (∀ u ∈ Icc t₀ s, Φ (φ u) ≤ c) → Φ (φ s) < c) :
    ∀ u ∈ Icc t₀ t₁, Φ (φ u) < c := by
  have hψ : ContinuousOn (fun t => Φ (φ t)) (Icc t₀ t₁) := hΦ.comp_continuousOn hφ
  by_contra hcon
  push Not at hcon
  obtain ⟨u, hu, hu'⟩ := hcon
  set A : Set ℝ := Icc t₀ t₁ ∩ (fun t => Φ (φ t)) ⁻¹' {y | c ≤ y} with hAdef
  have hAne : A.Nonempty := ⟨u, hu, hu'⟩
  have hAclosed : IsClosed A :=
    hψ.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_le continuous_const continuous_id)
  have hAbdd : BddBelow A := ⟨t₀, fun t ht => ht.1.1⟩
  have hτA : sInf A ∈ A := hAclosed.csInf_mem hAne hAbdd
  have hbelow : ∀ t ∈ Ico t₀ (sInf A), Φ (φ t) < c := by
    intro t ht
    by_contra h
    push Not at h
    have : sInf A ≤ t := csInf_le hAbdd ⟨⟨ht.1, ht.2.le.trans hτA.1.2⟩, h⟩
    linarith [ht.2]
  have hle : ∀ t ∈ Icc t₀ (sInf A), Φ (φ t) ≤ c := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · rcases eq_or_lt_of_le hτA.1.1 with h' | h'
      · rw [h, ← h']; exact h0.le
      · have hcl : IsClosed (Icc t₀ (sInf A) ∩ (fun t => Φ (φ t)) ⁻¹' {y | y ≤ c}) :=
          (hψ.mono (Icc_subset_Icc le_rfl hτA.1.2)).preimage_isClosed_of_isClosed isClosed_Icc
            (isClosed_le continuous_id continuous_const)
        have hsub : Ico t₀ (sInf A) ⊆ Icc t₀ (sInf A) ∩ (fun t => Φ (φ t)) ⁻¹' {y | y ≤ c} :=
          fun t' ht' => ⟨Ico_subset_Icc_self ht', (hbelow t' ht').le⟩
        have hcl' := hcl.closure_subset_iff.mpr hsub
        rw [closure_Ico h'.ne] at hcl'
        exact (hcl' ht).2
    · exact (hbelow t ⟨ht.1, h⟩).le
  exact absurd hτA.2 (not_le.mpr (hstep _ hτA.1 hle))

/-- First-exit (bootstrap) argument: a continuous curve that starts inside the open ball of
radius `R`, and that stays in the half-radius ball as long as it has stayed in the full ball,
never leaves the full ball. -/
@[powerlib_foundation] theorem forall_norm_sub_lt_of_bootstrap {E : Type*}
    [NormedAddCommGroup E] {φ : ℝ → E} {x : E} {t₀ t₁ R : ℝ}
    (hc : ContinuousOn φ (Icc t₀ t₁)) (h0 : ‖φ t₀ - x‖ < R)
    (hboot : ∀ s ∈ Icc t₀ t₁, (∀ u ∈ Icc t₀ s, ‖φ u - x‖ < R) → ‖φ s - x‖ ≤ R / 2) :
    ∀ t ∈ Icc t₀ t₁, ‖φ t - x‖ < R := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg _) h0
  have hcn : ContinuousOn (fun s => ‖φ s - x‖) (Icc t₀ t₁) := (hc.sub continuousOn_const).norm
  by_contra hcon
  push Not at hcon
  obtain ⟨t, ht, hRt⟩ := hcon
  set S : Set ℝ := Icc t₀ t₁ ∩ (fun s => ‖φ s - x‖) ⁻¹' Ici R with hSdef
  have hS_closed : IsClosed S := hcn.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hS_ne : S.Nonempty := ⟨t, ht, hRt⟩
  have hS_bdd : BddBelow S := ⟨t₀, fun s hs => hs.1.1⟩
  have hτ : sInf S ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
  set τ := sInf S with hτdef
  have hτR : R ≤ ‖φ τ - x‖ := hτ.2
  have hτ0 : t₀ < τ := by
    refine lt_of_le_of_ne hτ.1.1 fun h => ?_
    rw [← h] at hτR
    linarith
  have hbefore : ∀ s ∈ Ico t₀ τ, ‖φ s - x‖ ≤ R / 2 := by
    intro s hs
    apply hboot s ⟨hs.1, hs.2.le.trans hτ.1.2⟩
    intro u hu
    by_contra hu'
    push Not at hu'
    have hmem : u ∈ S := ⟨⟨hu.1, hu.2.trans (hs.2.le.trans hτ.1.2)⟩, hu'⟩
    have : τ ≤ u := csInf_le hS_bdd hmem
    linarith [hu.2, hs.2]
  have hT : IsClosed (Icc t₀ t₁ ∩ (fun s => ‖φ s - x‖) ⁻¹' Iic (R / 2)) :=
    hcn.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hsub : Ico t₀ τ ⊆ Icc t₀ t₁ ∩ (fun s => ‖φ s - x‖) ⁻¹' Iic (R / 2) :=
    fun s hs => ⟨⟨hs.1, hs.2.le.trans hτ.1.2⟩, hbefore s hs⟩
  have hcl := hT.closure_subset_iff.mpr hsub
  rw [closure_Ico hτ0.ne] at hcl
  have hle : ‖φ τ - x‖ ≤ R / 2 := (hcl ⟨hτ0.le, le_rfl⟩).2
  linarith

/-- Local exponential stability depends only on the field on a ball around the equilibrium. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_of_eqOn_ball
    {f g : Dynamics.State n → Dynamics.State n} {x : Dynamics.State n} {ρ : ℝ} (hρ : 0 < ρ)
    (hfg : ∀ y, ‖y - x‖ < ρ → f y = g y) (hg : LocallyExponentiallyStable g x) :
    LocallyExponentiallyStable f x :=
  locallyExponentiallyStable_congr_nhds (eventuallyEq_of_eqOn_ball hρ hfg) hg

/-- Lyapunov stability depends only on the field on a ball around the equilibrium. -/
@[powerlib_foundation] theorem lyapunovStable_of_eqOn_ball
    {f g : Dynamics.State n → Dynamics.State n} {x : Dynamics.State n} {ρ : ℝ} (hρ : 0 < ρ)
    (hfg : ∀ y, ‖y - x‖ < ρ → f y = g y) (hg : LyapunovStable g x) :
    LyapunovStable f x :=
  lyapunovStable_congr_nhds (eventuallyEq_of_eqOn_ball hρ hfg) hg

/-- Instability depends only on the field on a ball around the equilibrium. -/
@[powerlib_foundation] theorem unstable_of_eqOn_ball
    {f g : Dynamics.State n → Dynamics.State n} {x : Dynamics.State n} {ρ : ℝ} (hρ : 0 < ρ)
    (hfg : ∀ y, ‖y - x‖ < ρ → f y = g y) (hg : Unstable g x) :
    Unstable f x :=
  (unstable_congr_nhds (eventuallyEq_of_eqOn_ball hρ hfg)).mpr hg

/-- Linearization through a local `C¹` extension: if `f` agrees near `x_eq` with a globally
`C¹` field `g` whose Jacobian at `x_eq` is Hurwitz, then `f` is locally exponentially stable. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_of_isHurwitz_jacobian_of_eqOn_ball
    {f g : Dynamics.State n → Dynamics.State n} {x_eq : Dynamics.State n} {ρ : ℝ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hρ : 0 < ρ) (hfg : ∀ y, ‖y - x_eq‖ < ρ → f y = g y)
    (hg : ContDiff ℝ 1 g) (heq : g x_eq = 0)
    (hJac : fderiv ℝ g x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hA : LinearSystems.IsHurwitz A) : LocallyExponentiallyStable f x_eq :=
  locallyExponentiallyStable_of_eqOn_ball hρ hfg
    (Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian A hg heq hJac hA)

/-- Instability through a local `C¹` extension (eigenvalue with positive real part). -/
@[powerlib_foundation] theorem unstable_of_jacobian_eigenvalue_re_pos_of_eqOn_ball
    {f g : Dynamics.State n → Dynamics.State n} {x_eq : Dynamics.State n} {ρ : ℝ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hρ : 0 < ρ) (hfg : ∀ y, ‖y - x_eq‖ < ρ → f y = g y)
    (hg : ContDiff ℝ 1 g) (heq : g x_eq = 0)
    (hJac : fderiv ℝ g x_eq = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A)
    (hunstable : ∃ (μ : ℂ) (v : Fin n → ℂ),
      v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re) :
    Unstable f x_eq :=
  unstable_of_eqOn_ball hρ hfg
    (Dynamics.unstable_of_jacobian_eigenvalue_re_pos A hg heq hJac hunstable)

/-- Bootstrap: an exponential estimate for `G` transfers to every curve that solves
`ẋ = G x` while it stays in the ball of radius `R`. -/
@[powerlib_foundation] theorem exp_bound_of_local {G : State n → State n} {x₀ : State n}
    {r C a R : ℝ} (hC : 1 ≤ C) (ha : 0 < a)
    (hG : ∀ (t₀ t₁ : ℝ) (φ : ℝ → State n), IsTrajectoryOn φ G t₀ t₁ →
      ‖φ t₀ - x₀‖ < r → ∀ t ∈ Icc t₀ t₁,
        ‖φ t - x₀‖ ≤ C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - x₀‖)
    {φ : ℝ → State n} {t₀ t₁ : ℝ} (hcont : ContinuousOn φ (Icc t₀ t₁))
    (hder : ∀ t ∈ Icc t₀ t₁, ‖φ t - x₀‖ < R → HasDerivWithinAt φ (G (φ t)) (Icc t₀ t₁) t)
    (h0 : ‖φ t₀ - x₀‖ < min r (R / C)) :
    ∀ t ∈ Icc t₀ t₁, ‖φ t - x₀‖ ≤ C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - x₀‖ := by
  have hCpos : 0 < C := by linarith
  have h0r : ‖φ t₀ - x₀‖ < r := lt_of_lt_of_le h0 (min_le_left _ _)
  have hK : C * ‖φ t₀ - x₀‖ < R := by
    have := lt_of_lt_of_le h0 (min_le_right _ _)
    rw [lt_div_iff₀ hCpos] at this
    linarith
  have hn0 := norm_nonneg (φ t₀ - x₀)
  have hsub : ∀ s, s ≤ t₁ → (∀ τ ∈ Icc t₀ s, ‖φ τ - x₀‖ < R) →
      IsTrajectoryOn φ G t₀ s := by
    intro s hs hin τ hτ
    have hτ' : τ ∈ Icc t₀ t₁ := ⟨hτ.1, hτ.2.trans hs⟩
    exact (hder τ hτ' (hin τ hτ)).mono (Icc_subset_Icc le_rfl hs)
  have hcontN : ContinuousOn (fun s => ‖φ s - x₀‖) (Icc t₀ t₁) :=
    (hcont.sub continuousOn_const).norm
  have hstay : ∀ t ∈ Icc t₀ t₁, ‖φ t - x₀‖ < R := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t, ht, htR⟩ := hcon
    let S := Icc t₀ t₁ ∩ (fun s => ‖φ s - x₀‖) ⁻¹' Ici R
    have hSc : IsClosed S := hcontN.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hSne : S.Nonempty := ⟨t, ht, htR⟩
    have hSbdd : BddBelow S := ⟨t₀, fun y hy => hy.1.1⟩
    have hsS : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
    have hsR : R ≤ ‖φ (sInf S) - x₀‖ := hsS.2
    have hs0 : t₀ < sInf S := by
      rcases eq_or_lt_of_le hsS.1.1 with h | h
      · exfalso
        rw [← h] at hsR
        nlinarith
      · exact h
    have hbelow : ∀ τ ∈ Ico t₀ (sInf S), ‖φ τ - x₀‖ < R := by
      intro τ hτ
      by_contra hτR
      push Not at hτR
      have hmem : τ ∈ S := ⟨⟨hτ.1, hτ.2.le.trans hsS.1.2⟩, hτR⟩
      have := csInf_le hSbdd hmem
      linarith [hτ.2]
    have hbound : ∀ τ ∈ Ico t₀ (sInf S), ‖φ τ - x₀‖ ≤ C * ‖φ t₀ - x₀‖ := by
      intro τ hτ
      have htraj := hsub τ (hτ.2.le.trans hsS.1.2)
        (fun σ hσ => hbelow σ ⟨hσ.1, lt_of_le_of_lt hσ.2 hτ.2⟩)
      have hb := hG t₀ τ φ htraj h0r τ ⟨hτ.1, le_rfl⟩
      have hexp : Real.exp (-a * (τ - t₀)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [hτ.1])
      calc ‖φ τ - x₀‖ ≤ C * Real.exp (-a * (τ - t₀)) * ‖φ t₀ - x₀‖ := hb
        _ ≤ C * 1 * ‖φ t₀ - x₀‖ := by gcongr
        _ = C * ‖φ t₀ - x₀‖ := by ring
    let T := Icc t₀ t₁ ∩ (fun s => ‖φ s - x₀‖) ⁻¹' Iic (C * ‖φ t₀ - x₀‖)
    have hTc : IsClosed T := hcontN.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hsub2 : Ico t₀ (sInf S) ⊆ T := fun τ hτ =>
      ⟨⟨hτ.1, hτ.2.le.trans hsS.1.2⟩, hbound τ hτ⟩
    have hsT : sInf S ∈ T := by
      have := closure_minimal hsub2 hTc
      rw [closure_Ico hs0.ne] at this
      exact this ⟨hs0.le, le_rfl⟩
    have h2 : ‖φ (sInf S) - x₀‖ ≤ C * ‖φ t₀ - x₀‖ := hsT.2
    linarith
  exact hG t₀ t₁ φ (hsub t₁ le_rfl hstay) h0r

/-- Local asymptotic stability only depends on the field on a ball around the point. -/
@[powerlib_foundation] theorem localAsymptoticStable_of_eqOn_ball {f g : State n → State n}
    {x : State n} {R : ℝ} (hR : 0 < R) (hfg : ∀ y, ‖y - x‖ < R → f y = g y)
    (hg : LocalAsymptoticStable g x) : LocalAsymptoticStable f x :=
  localAsymptoticStable_congr_nhds (eventuallyEq_of_eqOn_ball hR hfg) hg

end Ball

/-! ## Smooth denominators away from zero -/

section Denominator

open Set Filter Topology

/-- The smooth denominator: equal to `V` for `V ≥ 1/2` and at least `1/4` everywhere. -/
def invDen (V : ℝ) : ℝ := 1 / 4 + (V - 1 / 4) * Real.smoothTransition (4 * V - 1)

/-- A globally smooth function equal to `V⁻¹` for `V ≥ 1/2`. -/
def invExt (V : ℝ) : ℝ := (invDen V)⁻¹

@[powerlib_foundation] theorem invDen_ge (V : ℝ) : 1 / 4 ≤ invDen V := by
  unfold invDen
  rcases le_or_gt V (1 / 4) with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
    simp
  · have := Real.smoothTransition.nonneg (4 * V - 1)
    have : 0 ≤ (V - 1 / 4) * Real.smoothTransition (4 * V - 1) :=
      mul_nonneg (by linarith) this
    linarith

@[powerlib_foundation] theorem invDen_pos (V : ℝ) : 0 < invDen V :=
  lt_of_lt_of_le (by norm_num) (invDen_ge V)

@[powerlib_foundation] theorem invDen_eq {V : ℝ} (h : 1 / 2 ≤ V) : invDen V = V := by
  unfold invDen
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  ring

@[powerlib_foundation] theorem invExt_eq {V : ℝ} (h : 1 / 2 ≤ V) : invExt V = V⁻¹ := by
  rw [invExt, invDen_eq h]

@[powerlib_foundation] theorem contDiff_invDen {k : ℕ∞} : ContDiff ℝ k invDen := by
  unfold invDen
  have hs : ContDiff ℝ k (fun V : ℝ => Real.smoothTransition (4 * V - 1)) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  fun_prop

@[powerlib_foundation] theorem contDiff_invExt {k : ℕ∞} : ContDiff ℝ k invExt := by
  unfold invExt
  exact contDiff_invDen.inv fun V => (invDen_pos V).ne'

/-- Smooth denominator: `regDen V v = v` for `v ≥ 3V/4` and `regDen V v ≥ V/2` (`V > 0`). -/
def regDen (V v : ℝ) : ℝ :=
  Real.smoothTransition (4 * v / V - 2) * v +
    (1 - Real.smoothTransition (4 * v / V - 2)) * (V / 2)

@[powerlib_foundation] theorem regDen_eq {V v : ℝ} (hV : 0 < V) (hv : 3 * V / 4 ≤ v) :
    regDen V v = v := by
  have h : 1 ≤ 4 * v / V - 2 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hV]
    linarith
  simp [regDen, Real.smoothTransition.one_of_one_le h]

@[powerlib_foundation] theorem half_le_regDen {V : ℝ} (hV : 0 < V) (v : ℝ) :
    V / 2 ≤ regDen V v := by
  unfold regDen
  have hs0 := Real.smoothTransition.nonneg (4 * v / V - 2)
  have hs1 := Real.smoothTransition.le_one (4 * v / V - 2)
  by_cases hv : V / 2 ≤ v
  · nlinarith
  · have h : 4 * v / V - 2 ≤ 0 := by
      rw [sub_nonpos, div_le_iff₀ hV]
      linarith
    rw [Real.smoothTransition.zero_of_nonpos h]
    simp

@[powerlib_foundation] theorem contDiff_regDen (V : ℝ) : ContDiff ℝ 1 (regDen V) := by
  have h : ContDiff ℝ 1 (fun v : ℝ => Real.smoothTransition (4 * v / V - 2)) :=
    (Real.smoothTransition.contDiff (n := 1)).comp (by fun_prop)
  unfold regDen
  exact (h.mul contDiff_id).add ((contDiff_const.sub h).mul contDiff_const)

end Denominator

end powerlib.Dynamics
