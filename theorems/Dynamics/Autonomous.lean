/-
Copyright 2026 Anand Gokhale and contributors
SPDX-License-Identifier: Apache-2.0
Adapted for PowerLib and mathlib 4.19. Original license:
licenses/LeanForControl-LICENSE.
Source: AnandGokhale/LeanForControl @ 7507ed04d94068fe3e7d4624b3383433a861bea7
LeanForControl/Stability/Autonomous.lean and LeanForControl/Analysis/Continuity.lean.
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
import theorems.Dynamics.LyapunovDefs

/-! Strict Lyapunov certificates imply asymptotic convergence of every existing
forward-complete trajectory. The original argument is adapted from LeanForControl's
Autonomous module without its blueprint annotations or custom axioms. -/

noncomputable section
namespace powerlib.Dynamics
open Set Filter Topology
variable {n : ℕ}
local notation "ℝⁿ" => State n

@[powerlib_foundation] theorem exists_first_sphere_hit
    {E : Type*} [NormedAddCommGroup E]
    {x_eq : E} {φ : ℝ → E} {ρ t₀ T t₁ : ℝ}
    (hφ : ContinuousOn φ (Icc t₀ T))
    (h₀ : ‖φ t₀ - x_eq‖ < ρ) (ht₁ : t₁ ∈ Icc t₀ T)
    (hfar : ρ ≤ ‖φ t₁ - x_eq‖) :
    ∃ τ ∈ Icc t₀ T, ‖φ τ - x_eq‖ = ρ ∧
      ∀ s ∈ Icc t₀ τ, ‖φ s - x_eq‖ ≤ ρ := by

  let d : ℝ → ℝ := fun t ↦ ‖φ t - x_eq‖
  have hd : ContinuousOn d (Icc t₀ T) :=
    continuous_norm.comp_continuousOn (hφ.sub continuousOn_const)
  have hd₁ : ContinuousOn d (Icc t₀ t₁) := hd.mono (Icc_subset_Icc_right ht₁.2)
  have hhit : ∃ s ∈ Icc t₀ T, d s = ρ := by
    have hρmem : ρ ∈ Icc (d t₀) (d t₁) := ⟨h₀.le, hfar⟩
    obtain ⟨s, hs, hsρ⟩ := (intermediate_value_Icc ht₁.1 hd₁) hρmem
    exact ⟨s, ⟨hs.1, hs.2.trans ht₁.2⟩, hsρ⟩
  let S : Set ℝ := Icc t₀ T ∩ d ⁻¹' {ρ}
  have hS_closed : IsClosed S :=
    hd.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hS_compact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hS_closed inter_subset_left
  have hS_nonempty : S.Nonempty := by
    obtain ⟨s, hs, hsρ⟩ := hhit
    exact ⟨s, hs, hsρ⟩
  obtain ⟨τ, hτS, hτmin⟩ := hS_compact.exists_isMinOn hS_nonempty continuousOn_id
  have hτIcc : τ ∈ Icc t₀ T := hτS.1
  have hτeq : d τ = ρ := hτS.2
  refine ⟨τ, hτIcc, hτeq, ?_⟩
  intro s hs
  by_contra hnot
  have hρs : ρ < d s := lt_of_not_ge hnot
  have hslt : s < τ :=
    hs.2.lt_of_ne (fun h ↦ by subst s; exact (ne_of_lt hρs) hτeq.symm)
  have hds : ContinuousOn d (Icc t₀ s) := by
    apply hd.mono
    intro q hq
    exact ⟨hq.1, hq.2.trans (hs.2.trans hτIcc.2)⟩
  have hρmem : ρ ∈ Icc (d t₀) (d s) := ⟨h₀.le, hρs.le⟩
  obtain ⟨q, hq, hqρ⟩ := (intermediate_value_Icc hs.1 hds) hρmem
  have hqS : q ∈ S := ⟨⟨hq.1, hq.2.trans (hs.2.trans hτIcc.2)⟩, hqρ⟩
  have hτq : τ ≤ q := hτmin hqS
  exact (not_lt_of_ge (hτq.trans hq.2)) hslt

private lemma sphere_nonempty
    (x_eq : ℝⁿ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    (Metric.sphere x_eq ε).Nonempty := by
  refine ⟨x_eq + EuclideanSpace.single (⟨0, hn⟩ : Fin n) ε, ?_⟩
  rw [Metric.mem_sphere, dist_eq_norm]
  simp [EuclideanSpace.norm_single, abs_of_pos hε]

private lemma lie_deriv_continuous
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    (hV_c1 : ContDiff ℝ 1 V) (hf_cont : Continuous f) :
    Continuous (fun x : ℝⁿ => fderiv ℝ V x (f x)) :=
  (hV_c1.continuous_fderiv (by norm_num)).clm_apply hf_cont

private lemma hasDerivAt_V_comp_integralCurveOn
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    (hV_diff : Differentiable ℝ V)
    {φ : ℝ → ℝⁿ} {s : Set ℝ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) s)
    {t : ℝ} (hs : s ∈ nhds t) :
    HasDerivAt (V ∘ φ) (fderiv ℝ V (φ t) (f (φ t))) t :=
  (hV_diff (φ t)).hasFDerivAt.comp_hasDerivAt t ((hφ t (mem_of_mem_nhds hs)).hasDerivAt hs)

@[powerlib_foundation] lemma hasDerivAt_V_comp_traj
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    (hV_diff : Differentiable ℝ V)
    {φ : ℝ → ℝⁿ} {t₀ t₁ : ℝ} (hφ : IsTrajectoryOn φ f t₀ t₁)
    {t : ℝ} (ht : t ∈ Set.Ioo t₀ t₁) :
    HasDerivAt (V ∘ φ) (fderiv ℝ V (φ t) (f (φ t))) t :=
  hasDerivAt_V_comp_integralCurveOn hV_diff hφ (Icc_mem_nhds ht.1 ht.2)

@[powerlib_foundation] lemma antitoneOn_V_add_linear
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    (hV_diff : Differentiable ℝ V) (hV_cont : Continuous V)
    {φ : ℝ → ℝⁿ} {s : Set ℝ} (hs : Convex ℝ s)
    (hφ : IsIntegralCurveOn φ (fun _ x => f x) s)
    {c : ℝ} (hLie : ∀ t ∈ interior s, fderiv ℝ V (φ t) (f (φ t)) ≤ -c) :
    AntitoneOn (fun t => V (φ t) + c * t) s := by
  have hd : ∀ t ∈ interior s, HasDerivAt (fun u => V (φ u) + c * u)
      (fderiv ℝ V (φ t) (f (φ t)) + c) t := fun t ht => by
    simpa using (hasDerivAt_V_comp_integralCurveOn hV_diff hφ
      (mem_interior_iff_mem_nhds.mp ht)).add ((hasDerivAt_id t).const_mul c)
  apply antitoneOn_of_deriv_nonpos hs
  · exact (hV_cont.comp_continuousOn hφ.continuousOn).add
      (continuous_const.mul continuous_id).continuousOn
  · exact fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
  · exact fun t ht => by rw [(hd t ht).deriv]; linarith [hLie t ht]

@[powerlib_foundation] lemma antitoneOn_V_comp_traj
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    (hV_diff : Differentiable ℝ V) (hV_cont : Continuous V)
    {φ : ℝ → ℝⁿ} {s : Set ℝ} (hs : Convex ℝ s)
    (hφ : IsIntegralCurveOn φ (fun _ x => f x) s)
    (hLie : ∀ t ∈ interior s, fderiv ℝ V (φ t) (f (φ t)) ≤ 0) :
    AntitoneOn (V ∘ φ) s := by
  simpa [Function.comp_def] using
    antitoneOn_V_add_linear hV_diff hV_cont hs hφ (c := 0) (by simpa using hLie)

@[powerlib_foundation] lemma V_nonincreasing_on
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsLocalLyapunovFunction f V x_eq D)
    {φ : ℝ → ℝⁿ} {t₀ t₁ : ℝ}
    (hφ : IsTrajectoryOn φ f t₀ t₁)
    (hle : t₀ ≤ t₁)
    (hstay : ∀ t ∈ Set.Icc t₀ t₁, φ t ∈ D) :
    V (φ t₁) ≤ V (φ t₀) := by
  have hanti : AntitoneOn (V ∘ φ) (Set.Icc t₀ t₁) :=
    antitoneOn_V_comp_traj hV.hV_diff hV.hcont (convex_Icc t₀ t₁) hφ fun t ht => by
      rw [interior_Icc] at ht
      exact hV.hLie_nonpos (φ t) (hstay t (Set.Ioo_subset_Icc_self ht))
  exact hanti (Set.left_mem_Icc.mpr hle) (Set.right_mem_Icc.mpr hle) hle

@[powerlib_foundation] lemma strict_implies_semidefinite
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsStrictLyapunovFunction f V x_eq) :
    IsLocalLyapunovFunction f V x_eq Set.univ where
  hD_open     := isOpen_univ
  hD_mem      := Set.mem_univ _
  hcont       := hV.hcont
  hV_diff     := hV.hV_c1.differentiable (by norm_num)
  hzero       := hV.hzero
  hpos        := fun x _ hx => hV.hpos x hx
  hLie_nonpos := fun x _ => by
    by_cases hx : x = x_eq
    · simp only [hx, hV.hequil, map_zero, le_refl]
    · exact le_of_lt (hV.hLie_neg x hx)

@[powerlib_foundation] lemma asymptotic_implies_strict
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsAsymptoticLyapunovFunction f V x_eq) :
    IsStrictLyapunovFunction f V x_eq where
  hcont             := hV.hcont
  hV_c1             := hV.hV_c1
  hzero             := hV.hzero
  hpos              := hV.hpos
  hequil            := hV.hequil
  hLie_neg          := hV.hLie_neg
  hbounded_sublevel := isCompact_sublevel_set V hV.hcont hV.hradial

@[powerlib_foundation] lemma strict_local_implies_semidefinite
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsStrictLocalLyapunovFunction f V x_eq D) :
    IsLocalLyapunovFunction f V x_eq D where
  hD_open     := hV.hD_open
  hD_mem      := hV.hD_mem
  hcont       := hV.hcont
  hV_diff     := hV.hV_c1.differentiable (by norm_num)
  hzero       := hV.hzero
  hpos        := hV.hpos
  hLie_nonpos := fun x hxD => by
    by_cases hx : x = x_eq
    · simp only [hx, hV.hequil, map_zero, le_refl]
    · exact le_of_lt (hV.hLie_neg x hxD hx)

@[powerlib_foundation] lemma sublevel_set_invariant
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsLocalLyapunovFunction f V x_eq D)
    {φ : ℝ → ℝⁿ} {t₀ t₁ : ℝ} (hφ : IsTrajectoryOn φ f t₀ t₁)
    {c : ℝ} (hΩ_sub_D : SublevelSet V c ⊆ D)
    (h0 : V (φ t₀) < c) :
    ∀ t ∈ Set.Icc t₀ t₁, V (φ t) < c := by
  have hcont : ContinuousOn (V ∘ φ) (Set.Icc t₀ t₁) :=
    hV.hcont.comp_continuousOn hφ.continuousOn
  intro t ht
  by_contra hge
  push_neg at hge
  set S := Set.Icc t₀ t₁ ∩ (V ∘ φ) ⁻¹' (Set.Ici c) with hS_def
  have hS_nonempty : S.Nonempty := ⟨t, ht, hge⟩
  have hS_bddBelow : BddBelow S := ⟨t₀, fun s hs => hs.1.1⟩
  have hS_closed : IsClosed S :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  set T := sInf S with hT_def
  have hT_mem : T ∈ S := hS_closed.csInf_mem hS_nonempty hS_bddBelow
  have hT_ge_c : c ≤ V (φ T) := hT_mem.2
  have hT_gt : t₀ < T := by
    rcases lt_or_eq_of_le hT_mem.1.1 with h | h
    · exact h
    · exact absurd hT_ge_c (by rw [← h] at hT_ge_c ⊢; linarith)
  have hlt_of_lt : ∀ s : ℝ, t₀ ≤ s → s < T → V (φ s) < c := by
    intro s hs_nonneg hs_lt
    by_contra h
    push_neg at h
    exact absurd (csInf_le hS_bddBelow
      ⟨⟨hs_nonneg, le_of_lt (lt_of_lt_of_le hs_lt hT_mem.1.2)⟩, h⟩) (not_le.mpr hs_lt)
  have hVs_le : ∀ s : ℝ, t₀ ≤ s → s < T → V (φ s) ≤ V (φ t₀) := by
    intro s hs_nonneg hs_lt
    have hsub : Set.Icc t₀ s ⊆ Set.Icc t₀ t₁ :=
      Set.Icc_subset_Icc_right (le_of_lt (lt_of_lt_of_le hs_lt hT_mem.1.2))
    exact V_nonincreasing_on hV (hφ.mono hsub) hs_nonneg fun r hr =>
      hΩ_sub_D (le_of_lt (hlt_of_lt r hr.1 (lt_of_le_of_lt hr.2 hs_lt)))
  haveI hNeBot : (nhdsWithin T (Set.Ico t₀ T)).NeBot := by
    rw [nhdsWithin_Ico_eq_nhdsLT hT_gt]
    infer_instance
  have hVs_bound : ∀ᶠ s in nhdsWithin T (Set.Ico t₀ T), (V ∘ φ) s ≤ V (φ t₀) :=
    eventually_nhdsWithin_of_forall (fun s hs => hVs_le s hs.1 hs.2)
  have hTwithin : ContinuousWithinAt (V ∘ φ) (Set.Ico t₀ T) T :=
    (hcont T hT_mem.1).mono (fun r hr => ⟨hr.1, le_of_lt (lt_of_lt_of_le hr.2 hT_mem.1.2)⟩)
  have hVT_le : V (φ T) ≤ V (φ t₀) := le_of_tendsto hTwithin hVs_bound
  linarith

open Set in

@[powerlib_domain] theorem lyapunov_stable
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsLocalLyapunovFunction f V x_eq D) :
    LyapunovStable f x_eq := by
  obtain ⟨r, hr_pos, hr_ball⟩ := Metric.isOpen_iff.mp hV.hD_open x_eq hV.hD_mem
  set ε₀ := r / 2
  have hε₀_pos : 0 < ε₀ := by dsimp [ε₀]; linarith
  have hcBall_sub_D : Metric.closedBall x_eq ε₀ ⊆ D := by
    intro x hx
    apply hr_ball
    rw [Metric.mem_ball, Metric.mem_closedBall] at *
    dsimp [ε₀] at *
    linarith
  intro ε hε
  set ε' := min ε ε₀
  have hε'_pos : 0 < ε' := lt_min hε hε₀_pos
  have hε'_le_ε : ε' ≤ ε := min_le_left _ _
  have hcBall'_sub_D : Metric.closedBall x_eq ε' ⊆ D :=
    (Metric.closedBall_subset_closedBall (min_le_right _ _)).trans hcBall_sub_D
  have hsphere'_sub_D : Metric.sphere x_eq ε' ⊆ D :=
    Metric.sphere_subset_closedBall.trans hcBall'_sub_D
  obtain ⟨x_min, hx_min_mem, hx_min_le⟩ :=
    (isCompact_sphere x_eq ε').exists_isMinOn
      (sphere_nonempty x_eq hn hε'_pos) hV.hcont.continuousOn
  set m := V x_min
  have hm_pos : 0 < m := by
    apply hV.hpos x_min (hsphere'_sub_D hx_min_mem)
    intro heq
    have hx := hx_min_mem
    rw [heq, Metric.mem_sphere, dist_self] at hx
    exact (ne_of_gt hε'_pos) hx.symm
  have hV_cont_at : ContinuousAt V x_eq := hV.hcont.continuousAt
  rw [Metric.continuousAt_iff] at hV_cont_at
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := hV_cont_at m hm_pos
  set δ := min δ₀ ε'
  refine ⟨δ, lt_min hδ₀_pos hε'_pos, ?_⟩
  intro t₀ t₁ φ hφ hφ0 t ht
  have hφ0ε' : ‖φ t₀ - x_eq‖ < ε' := hφ0.trans_le (min_le_right _ _)
  have hV0_lt_m : V (φ t₀) < m := by
    have hnear : dist (V (φ t₀)) (V x_eq) < m := hδ₀ (by
      rw [dist_eq_norm]
      exact hφ0.trans_le (min_le_left _ _))
    simp only [Real.dist_eq, hV.hzero, sub_zero] at hnear
    exact (abs_lt.mp hnear).2
  by_contra hnot
  push_neg at hnot
  have hge_ε' : ε' ≤ ‖φ t - x_eq‖ := hε'_le_ε.trans hnot

  obtain ⟨τ, hτ_mem, hτ_eq, hτ_stay⟩ :=
    exists_first_sphere_hit (hφ.continuousOn.mono (Icc_subset_Icc le_rfl ht.2))
      hφ0ε' ⟨ht.1, le_rfl⟩ hge_ε'
  have hstay : ∀ s ∈ Icc t₀ τ, φ s ∈ D := fun s hs =>
    hcBall'_sub_D (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hτ_stay s hs)

  have hVT_le : V (φ τ) ≤ V (φ t₀) :=
    V_nonincreasing_on hV (hφ.mono (Icc_subset_Icc_right (hτ_mem.2.trans ht.2)))
      hτ_mem.1 hstay
  have hVT_ge : m ≤ V (φ τ) :=
    hx_min_le (by rw [Metric.mem_sphere, dist_eq_norm]; exact hτ_eq)
  linarith

open Set in

@[powerlib_domain] theorem LocallyExponentiallyStable.lyapunovStable
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (h : LocallyExponentiallyStable f x_eq) :
    LyapunovStable f x_eq := by
  rcases h with ⟨r, C, a, hr, hC, ha, hdecay⟩
  intro ε hε
  refine ⟨min r (ε / C), ?_, ?_⟩
  · positivity
  intro t₀ t₁ φ hφ hφ0 t ht
  have ht0 : t₀ ≤ t := ht.1
  have hexp : Real.exp (-a * (t - t₀)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hinit : ‖φ t₀ - x_eq‖ < ε / C := lt_of_lt_of_le hφ0 (min_le_right _ _)
  calc
    ‖φ t - x_eq‖ ≤ C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - x_eq‖ :=
      hdecay t₀ t₁ φ hφ (lt_of_lt_of_le hφ0 (min_le_left _ _)) t ht
    _ ≤ C * 1 * ‖φ t₀ - x_eq‖ := by gcongr
    _ < ε := by
      rw [mul_one, ← lt_div_iff₀' hCpos]
      simpa [mul_comm] using hinit

open Set in

@[powerlib_domain] theorem unstable_of_fixed_escape
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {ε : ℝ} (hε : 0 < ε)
    (hescape : ∀ δ > 0, ∃ (T : ℝ) (φ : ℝ → ℝⁿ) (t : ℝ),
      IsTrajectoryOn φ f 0 T ∧ ‖φ 0 - x_eq‖ < δ ∧
        t ∈ Icc (0 : ℝ) T ∧ ε ≤ ‖φ t - x_eq‖) :
    Unstable f x_eq := by
  intro hstable
  obtain ⟨δ, hδ, hstay⟩ := hstable ε hε
  obtain ⟨T, φ, t, hφ, hφ0, ht, hfar⟩ := hescape δ hδ
  exact (not_lt_of_ge hfar) (hstay 0 T φ hφ hφ0 t ht)

open Set in

@[powerlib_foundation] lemma time_outside_ball_le
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsLocalLyapunovFunction f V x_eq D) (hV_c1 : ContDiff ℝ 1 V)
    (hLie_neg : ∀ x ∈ D, x ≠ x_eq → fderiv ℝ V x (f x) < 0) (hf_cont : Continuous f)
    {M : ℝ} (hM_sub : SublevelSet V M ⊆ D) (hM_compact : IsCompact (SublevelSet V M))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ τ ≥ 0, ∀ (t₀ t₁ : ℝ) (φ : ℝ → ℝⁿ), IsTrajectoryOn φ f t₀ t₁ → t₀ ≤ t₁ →
      V (φ t₀) ≤ M → (∀ t ∈ Icc t₀ t₁, φ t ∈ D) →
      (∀ t ∈ Icc t₀ t₁, δ ≤ ‖φ t - x_eq‖) → t₁ - t₀ ≤ τ := by
  have hout_closed : IsClosed {x : ℝⁿ | δ ≤ ‖x - x_eq‖} :=
    isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
  set K : Set ℝⁿ := SublevelSet V M ∩ {x : ℝⁿ | δ ≤ ‖x - x_eq‖} with hK_def
  have hK_compact : IsCompact K := hM_compact.inter_right hout_closed
  have hmem_K : ∀ x : ℝⁿ, V x ≤ M → δ ≤ ‖x - x_eq‖ → x ∈ K := fun x h₁ h₂ => ⟨h₁, h₂⟩
  have hK_sub_D : ∀ x ∈ K, x ∈ D := fun x hx => hM_sub hx.1
  have hK_ne_eq : ∀ x ∈ K, x ≠ x_eq := by
    intro x hx hxeq
    have h2 : δ ≤ ‖x - x_eq‖ := hx.2
    rw [hxeq, sub_self, norm_zero] at h2
    linarith
  rcases K.eq_empty_or_nonempty with hKempty | hKne
  · refine ⟨0, le_rfl, fun t₀ t₁ φ _ hle hM _ hout => ?_⟩
    have hmem : φ t₀ ∈ K := hmem_K (φ t₀) hM (hout t₀ ⟨le_rfl, hle⟩)
    rw [hKempty] at hmem
    simp at hmem
  · have hM_pos : 0 < M := by
      obtain ⟨x, hx⟩ := hKne
      exact lt_of_lt_of_le (hV.hpos x (hK_sub_D x hx) (hK_ne_eq x hx)) hx.1
    obtain ⟨x_max, hx_max_mem, hx_max⟩ :=
      hK_compact.exists_isMaxOn hKne (lie_deriv_continuous hV_c1 hf_cont).continuousOn
    set γ := -(fderiv ℝ V x_max (f x_max)) with hγ_def
    have hγ_pos : 0 < γ := by
      have h := hLie_neg x_max (hK_sub_D x_max hx_max_mem) (hK_ne_eq x_max hx_max_mem)
      rw [hγ_def]; linarith
    refine ⟨M / γ, le_of_lt (div_pos hM_pos hγ_pos), ?_⟩
    intro t₀ t₁ φ hφ hle hMle hstayD hout
    have hVle : ∀ t ∈ Icc t₀ t₁, V (φ t) ≤ M := by
      intro t ht
      refine le_trans ?_ hMle
      exact V_nonincreasing_on hV (hφ.mono (Icc_subset_Icc_right ht.2)) ht.1
        (fun r hr => hstayD r ⟨hr.1, hr.2.trans ht.2⟩)

    have hW_anti : AntitoneOn (fun t => V (φ t) + γ * t) (Icc t₀ t₁) :=
      antitoneOn_V_add_linear (hV_c1.differentiable (by norm_num)) hV.hcont
        (convex_Icc t₀ t₁) hφ fun t ht => by
          rw [interior_Icc] at ht
          have ht' : t ∈ Icc t₀ t₁ := Ioo_subset_Icc_self ht
          have hle_max : fderiv ℝ V (φ t) (f (φ t)) ≤ fderiv ℝ V x_max (f x_max) :=
            hx_max (hmem_K (φ t) (hVle t ht') (hout t ht'))
          rw [hγ_def]
          linarith
    have hstep : V (φ t₁) + γ * t₁ ≤ V (φ t₀) + γ * t₀ :=
      hW_anti (left_mem_Icc.mpr hle) (right_mem_Icc.mpr hle) hle
    have hV1_nonneg : 0 ≤ V (φ t₁) := by
      rcases eq_or_ne (φ t₁) x_eq with h | h
      · rw [h, hV.hzero]
      · exact (hV.hpos _ (hstayD t₁ (right_mem_Icc.mpr hle)) h).le
    have hbound : γ * (t₁ - t₀) ≤ M := by
      have hexp : γ * (t₁ - t₀) = γ * t₁ - γ * t₀ := by ring
      rw [hexp]
      linarith [hVle t₀ ⟨le_rfl, hle⟩]
    rw [le_div_iff₀ hγ_pos]
    linarith [hbound, mul_comm γ (t₁ - t₀)]

open Set in

/-- A strict coercive certificate gives stability and convergence of all existing global trajectories. -/
@[powerlib_domain] theorem lyapunov_asymptotic_stable
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsStrictLyapunovFunction f V x_eq)
    (hf_cont : Continuous f) :
    TrajectoryGloballyAsymptoticallyStable f x_eq := by
  have hstable : LyapunovStable f x_eq :=
    lyapunov_stable hn (strict_implies_semidefinite hV)
  refine ⟨hstable, ?_⟩
  intro t₀ φ hφ
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := hstable ε hε
  obtain ⟨τ₀, hτ₀_nonneg, hτ₀⟩ :=
    time_outside_ball_le (strict_implies_semidefinite hV) hV.hV_c1
      (fun x _ hx => hV.hLie_neg x hx) hf_cont (Set.subset_univ _)
      (hV.hbounded_sublevel (V (φ t₀))) hδ_pos
  refine ⟨t₀ + (τ₀ + 1), fun t ht => ?_⟩
  rw [dist_eq_norm]
  by_cases hex : ∃ s ∈ Icc t₀ (t₀ + (τ₀ + 1)), ‖φ s - x_eq‖ < δ
  · obtain ⟨s, hs_mem, hs⟩ := hex
    have hsub : Icc s t ⊆ Ici t₀ := fun r hr => le_trans hs_mem.1 hr.1
    exact hδ s t φ (hφ.mono hsub) hs t ⟨le_trans hs_mem.2 ht, le_rfl⟩
  · push_neg at hex
    have hsub : Icc t₀ (t₀ + (τ₀ + 1)) ⊆ Ici t₀ := fun r hr => hr.1
    have hdwell := hτ₀ t₀ (t₀ + (τ₀ + 1)) φ (hφ.mono hsub) (by linarith) le_rfl
      (fun _ _ => Set.mem_univ _) hex
    linarith

/-- Radial unboundedness supplies the compact sublevel sets of the strict certificate. -/
@[powerlib_domain] theorem lyapunov_global_asymptotic_stable
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsAsymptoticLyapunovFunction f V x_eq)
    (hf_cont : Continuous f) :
    TrajectoryGloballyAsymptoticallyStable f x_eq :=
  lyapunov_asymptotic_stable hn (asymptotic_implies_strict hV) hf_cont

open Set in

@[powerlib_domain] theorem lyapunov_local_asymptotic_stable
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsStrictLocalLyapunovFunction f V x_eq D)
    (hf_cont : Continuous f) :
    LocalAsymptoticStable f x_eq := by
  obtain ⟨c₀, hc₀_pos, hΩ_sub_D, hΩ_compact⟩ := hV.hcompact
  have hV_local := strict_local_implies_semidefinite hV
  have hstable : LyapunovStable f x_eq := lyapunov_stable hn hV_local
  refine ⟨hstable, ?_⟩
  have hVcont_at : ContinuousAt V x_eq := hV.hcont.continuousAt
  rw [Metric.continuousAt_iff] at hVcont_at
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := hVcont_at c₀ hc₀_pos
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  intro t₀ φ hφ hφ0
  have hV0_lt : V (φ t₀) < c₀ := by
    have h := hδ₀ (by rw [dist_eq_norm]; exact hφ0)
    rw [Real.dist_eq, hV.hzero, sub_zero] at h
    exact (abs_lt.mp h).2
  have hstayD : ∀ (t₁ : ℝ), ∀ s ∈ Icc t₀ t₁, φ s ∈ D := fun t₁ s hs =>
    hΩ_sub_D (le_of_lt (sublevel_set_invariant hV_local
      (hφ.mono (fun r hr => hr.1)) hΩ_sub_D hV0_lt s hs))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := hstable ε hε
  obtain ⟨τ₀, hτ₀_nonneg, hτ₀⟩ :=
    time_outside_ball_le hV_local hV.hV_c1 hV.hLie_neg hf_cont hΩ_sub_D hΩ_compact hδ_pos
  refine ⟨t₀ + (τ₀ + 1), fun t ht => ?_⟩
  rw [dist_eq_norm]
  by_cases hex : ∃ s ∈ Icc t₀ (t₀ + (τ₀ + 1)), ‖φ s - x_eq‖ < δ
  · obtain ⟨s, hs_mem, hs⟩ := hex
    have hsub : Icc s t ⊆ Ici t₀ := fun r hr => le_trans hs_mem.1 hr.1
    exact hδ s t φ (hφ.mono hsub) hs t ⟨le_trans hs_mem.2 ht, le_rfl⟩
  · push_neg at hex
    have hsub : Icc t₀ (t₀ + (τ₀ + 1)) ⊆ Ici t₀ := fun r hr => hr.1
    have hdwell := hτ₀ t₀ (t₀ + (τ₀ + 1)) φ (hφ.mono hsub) (by linarith)
      (le_of_lt hV0_lt) (fun s hs => hstayD _ s hs) hex
    linarith

end powerlib.Dynamics
