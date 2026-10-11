import theorem.Hurwitz
import theorem.Dynamics.Autonomous
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Locality of stability and linearization for locally C¹ fields (foundation)

Local exponential stability, Lyapunov stability and instability of an equilibrium depend only
on the vector field near the equilibrium:
* `locallyExponentiallyStable_congr_nhds`, `lyapunovStable_congr_nhds`, `unstable_congr_nhds`:
  if `f = g` on a neighbourhood of `x_eq` the properties transfer (first-exit argument with
  `exists_first_sphere_hit`).
* `exists_contDiff_eventuallyEq`: a field that is `C¹` on an open set `U ∋ x` agrees near `x`
  with a globally `C¹` field (multiply by a smooth bump supported in `U`).

Consequently the Lyapunov indirect method holds for fields that are only `C¹` on an open
neighbourhood of the equilibrium (`locallyExponentiallyStable_of_isHurwitz_jacobian_local`,
`unstable_of_jacobian_eigenvalue_re_pos_local`), which the global-`ContDiff` wrappers of
`theorem/Hurwitz.lean` do not cover. Typical use: power-balance fields with a `1/V_dc`
factor, which are smooth only on `V_dc > 0` (`theorem/DCLink/VoltageControl.lean`).

These are general facts about autonomous ODEs, not engineering conclusions.

Source: standard (Khalil, *Nonlinear Systems*, Thm 4.7 is stated for `C¹` on a domain);
needed by work-sync `theory/T-vsc-dc-voltage-control.md` §1.1, §1.4.
-/

noncomputable section
namespace powerlib.DCLink
open Set Filter Metric Matrix
open scoped Topology

variable {n : ℕ}
local notation "Sₙ" => Dynamics.State n

@[powerlib_foundation] private lemma isTrajectoryOn_of_eqOn {f g : Sₙ → Sₙ}
    {x : Sₙ} {ρ : ℝ} (hfg : ∀ y, ‖y - x‖ < ρ → f y = g y) {φ : ℝ → Sₙ}
    {t₀ t₁ τ : ℝ} (hφ : Dynamics.IsTrajectoryOn φ f t₀ t₁) (hτ : τ ≤ t₁)
    (hin : ∀ s ∈ Icc t₀ τ, ‖φ s - x‖ < ρ) : Dynamics.IsTrajectoryOn φ g t₀ τ := by
  intro s hs
  have h := (hφ s ⟨hs.1, hs.2.trans hτ⟩).mono (Icc_subset_Icc_right hτ)
  simpa [hfg _ (hin s hs)] using h

/-- Local exponential stability depends only on the field near the equilibrium. -/
@[powerlib_foundation] theorem locallyExponentiallyStable_congr_nhds {f g : Sₙ → Sₙ}
    {x : Sₙ} (hfg : f =ᶠ[𝓝 x] g) (hg : Dynamics.LocallyExponentiallyStable g x) :
    Dynamics.LocallyExponentiallyStable f x := by
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
      Dynamics.exists_first_sphere_hit hφ.continuousOn hρ0 hs hfar
    have hg' : Dynamics.IsTrajectoryOn φ g t₀ τ :=
      isTrajectoryOn_of_eqOn hfg' hφ hτ.2 fun s hs => (hτin s hs).trans_lt (by linarith)
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
  have hg' : Dynamics.IsTrajectoryOn φ g t₀ t₁ :=
    isTrajectoryOn_of_eqOn hfg' hφ le_rfl fun s hs => (hstay s hs).trans (by linarith)
  exact hb t₀ t₁ φ hg' h0r t ht

/-- Lyapunov stability depends only on the field near the equilibrium. -/
@[powerlib_foundation] theorem lyapunovStable_congr_nhds {f g : Sₙ → Sₙ}
    {x : Sₙ} (hfg : f =ᶠ[𝓝 x] g) (hg : Dynamics.LyapunovStable g x) : Dynamics.LyapunovStable f x := by
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
    obtain ⟨τ, hτ, hτeq, hτin⟩ := Dynamics.exists_first_sphere_hit hφ.continuousOn h0ε hs hfar
    have hg' : Dynamics.IsTrajectoryOn φ g t₀ τ :=
      isTrajectoryOn_of_eqOn hfg' hφ hτ.2 fun s hs => (hτin s hs).trans_lt hερ
    have := hb t₀ τ φ hg' h0δ τ ⟨hτ.1, le_rfl⟩
    linarith
  exact (hstay t ht).trans_le (min_le_left _ _)

/-- Instability depends only on the field near the equilibrium. -/
@[powerlib_foundation] theorem unstable_congr_nhds {f g : Sₙ → Sₙ} {x : Sₙ}
    (hfg : f =ᶠ[𝓝 x] g) : Dynamics.Unstable f x ↔ Dynamics.Unstable g x :=
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
    (hA : LinearSystems.IsHurwitz A) : Dynamics.LocallyExponentiallyStable f x_eq := by
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
    Dynamics.Unstable f x_eq := by
  obtain ⟨g, hg, hgf⟩ := exists_contDiff_eventuallyEq hU hx hf
  rw [unstable_congr_nhds hgf.symm]
  exact Dynamics.unstable_of_jacobian_eigenvalue_re_pos A hg
    (by rw [hgf.eq_of_nhds, heq]) (by rw [hgf.fderiv_eq, hJac]) hunstable

end powerlib.DCLink
