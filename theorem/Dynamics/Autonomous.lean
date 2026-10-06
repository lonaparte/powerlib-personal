import dependencies.LeanForControl
import theorem.Dynamics.LyapunovDefs

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
      ∀ s ∈ Icc t₀ τ, ‖φ s - x_eq‖ ≤ ρ :=
  _root_.exists_first_sphere_hit hφ h₀ ht₁ hfar

@[powerlib_foundation] lemma hasDerivAt_V_comp_traj
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    (hV_diff : Differentiable ℝ V)
    {φ : ℝ → ℝⁿ} {t₀ t₁ : ℝ} (hφ : IsTrajectoryOn φ f t₀ t₁)
    {t : ℝ} (ht : t ∈ Set.Ioo t₀ t₁) :
    HasDerivAt (V ∘ φ) (fderiv ℝ V (φ t) (f (φ t))) t :=
  _root_.hasDerivAt_V_comp_traj hV_diff hφ ht

@[powerlib_foundation] lemma antitoneOn_V_add_linear
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    (hV_diff : Differentiable ℝ V) (hV_cont : Continuous V)
    {φ : ℝ → ℝⁿ} {s : Set ℝ} (hs : Convex ℝ s)
    (hφ : IsIntegralCurveOn φ (fun _ x => f x) s)
    {c : ℝ} (hLie : ∀ t ∈ interior s, fderiv ℝ V (φ t) (f (φ t)) ≤ -c) :
    AntitoneOn (fun t => V (φ t) + c * t) s :=
  _root_.antitoneOn_V_add_linear hV_diff hV_cont hs hφ hLie

@[powerlib_foundation] lemma antitoneOn_V_comp_traj
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ}
    (hV_diff : Differentiable ℝ V) (hV_cont : Continuous V)
    {φ : ℝ → ℝⁿ} {s : Set ℝ} (hs : Convex ℝ s)
    (hφ : IsIntegralCurveOn φ (fun _ x => f x) s)
    (hLie : ∀ t ∈ interior s, fderiv ℝ V (φ t) (f (φ t)) ≤ 0) :
    AntitoneOn (V ∘ φ) s :=
  _root_.antitoneOn_V_comp_traj hV_diff hV_cont hs hφ hLie

@[powerlib_foundation] lemma V_nonincreasing_on
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsLocalLyapunovFunction f V x_eq D)
    {φ : ℝ → ℝⁿ} {t₀ t₁ : ℝ}
    (hφ : IsTrajectoryOn φ f t₀ t₁)
    (hle : t₀ ≤ t₁)
    (hstay : ∀ t ∈ Set.Icc t₀ t₁, φ t ∈ D) :
    V (φ t₁) ≤ V (φ t₀) :=
  _root_.V_nonincreasing_on hV hφ hle hstay

@[powerlib_foundation] lemma strict_implies_semidefinite
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsStrictLyapunovFunction f V x_eq) :
    IsLocalLyapunovFunction f V x_eq Set.univ :=
  _root_.strict_implies_semidefinite hV

@[powerlib_foundation] lemma asymptotic_implies_strict
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsAsymptoticLyapunovFunction f V x_eq) :
    IsStrictLyapunovFunction f V x_eq :=
  _root_.asymptotic_implies_strict hV

@[powerlib_foundation] lemma strict_local_implies_semidefinite
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsStrictLocalLyapunovFunction f V x_eq D) :
    IsLocalLyapunovFunction f V x_eq D :=
  _root_.strict_local_implies_semidefinite hV

@[powerlib_foundation] lemma sublevel_set_invariant
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsLocalLyapunovFunction f V x_eq D)
    {φ : ℝ → ℝⁿ} {t₀ t₁ : ℝ} (hφ : IsTrajectoryOn φ f t₀ t₁)
    {c : ℝ} (hΩ_sub_D : SublevelSet V c ⊆ D)
    (h0 : V (φ t₀) < c) :
    ∀ t ∈ Set.Icc t₀ t₁, V (φ t) < c :=
  _root_.sublevel_set_invariant hV hφ hΩ_sub_D h0

@[powerlib_domain] theorem lyapunov_stable
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsLocalLyapunovFunction f V x_eq D) :
    LyapunovStable f x_eq :=
  _root_.lyapunov_stable hn hV

@[powerlib_domain] theorem LocallyExponentiallyStable.lyapunovStable
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (h : LocallyExponentiallyStable f x_eq) :
    LyapunovStable f x_eq :=
  _root_.LocallyExponentiallyStable.lyapunovStable h

@[powerlib_domain] theorem unstable_of_fixed_escape
    {f : ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {ε : ℝ} (hε : 0 < ε)
    (hescape : ∀ δ > 0, ∃ (T : ℝ) (φ : ℝ → ℝⁿ) (t : ℝ),
      IsTrajectoryOn φ f 0 T ∧ ‖φ 0 - x_eq‖ < δ ∧
        t ∈ Icc (0 : ℝ) T ∧ ε ≤ ‖φ t - x_eq‖) :
    Unstable f x_eq :=
  _root_.unstable_of_fixed_escape hε hescape

@[powerlib_foundation] lemma time_outside_ball_le
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ}
    (hV : IsLocalLyapunovFunction f V x_eq D) (hV_c1 : ContDiff ℝ 1 V)
    (hLie_neg : ∀ x ∈ D, x ≠ x_eq → fderiv ℝ V x (f x) < 0) (hf_cont : Continuous f)
    {M : ℝ} (hM_sub : SublevelSet V M ⊆ D) (hM_compact : IsCompact (SublevelSet V M))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ τ ≥ 0, ∀ (t₀ t₁ : ℝ) (φ : ℝ → ℝⁿ), IsTrajectoryOn φ f t₀ t₁ → t₀ ≤ t₁ →
      V (φ t₀) ≤ M → (∀ t ∈ Icc t₀ t₁, φ t ∈ D) →
      (∀ t ∈ Icc t₀ t₁, δ ≤ ‖φ t - x_eq‖) → t₁ - t₀ ≤ τ :=
  _root_.time_outside_ball_le hV hV_c1 hLie_neg hf_cont hM_sub hM_compact hδ

@[powerlib_domain] theorem lyapunov_asymptotic_stable
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsStrictLyapunovFunction f V x_eq)
    (hf_cont : Continuous f) :
    TrajectoryGloballyAsymptoticallyStable f x_eq :=
  _root_.lyapunov_asymptotic_stable hn hV hf_cont

@[powerlib_domain] theorem lyapunov_global_asymptotic_stable
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsAsymptoticLyapunovFunction f V x_eq)
    (hf_cont : Continuous f) :
    TrajectoryGloballyAsymptoticallyStable f x_eq :=
  _root_.lyapunov_global_asymptotic_stable hn hV hf_cont

@[powerlib_domain] theorem lyapunov_local_asymptotic_stable
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV : IsStrictLocalLyapunovFunction f V x_eq D)
    (hf_cont : Continuous f) :
    LocalAsymptoticStable f x_eq :=
  _root_.lyapunov_local_asymptotic_stable hn hV hf_cont

end powerlib.Dynamics
