/-
Copyright 2026 Anand Gokhale and contributors
SPDX-License-Identifier: Apache-2.0
Adapted for PowerLib and mathlib 4.19. Original license:
licenses/LeanForControl-LICENSE.
Source: AnandGokhale/LeanForControl @ 7507ed04d94068fe3e7d4624b3383433a861bea7
LeanForControl/Stability/DefsAutonomous.lean.
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.MonotoneContinuity
import theorems.Dynamics.Defs
import theorems.Attributes

/-! Lyapunov certificates for finite-dimensional autonomous continuous-time systems.
Adapted from LeanForControl's DefsAutonomous module. These predicates quantify over
existing trajectories; forward completeness is a separate obligation. -/

noncomputable section
namespace powerlib.Dynamics
open Set Filter Topology
variable {n : ℕ}
local notation "ℝⁿ" => State n

def IsEquilibrium (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  f x_eq = 0

def LyapunovStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (t₀ t₁ : ℝ) (φ : ℝ → ℝⁿ),
    IsTrajectoryOn φ f t₀ t₁ → ‖φ t₀ - x_eq‖ < δ →
      ∀ t ∈ Icc t₀ t₁, ‖φ t - x_eq‖ < ε

def LocallyExponentiallyStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∃ r C a : ℝ, 0 < r ∧ 1 ≤ C ∧ 0 < a ∧
    ∀ (t₀ t₁ : ℝ) (φ : ℝ → ℝⁿ), IsTrajectoryOn φ f t₀ t₁ →
      ‖φ t₀ - x_eq‖ < r → ∀ t ∈ Icc t₀ t₁,
        ‖φ t - x_eq‖ ≤ C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - x_eq‖

def LocalAsymptoticStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  LyapunovStable f x_eq ∧
  ∃ c > 0, ∀ (t₀ : ℝ) (φ : ℝ → ℝⁿ), IsIntegralCurveOn φ (fun _ y => f y) (Ici t₀) →
    ‖φ t₀ - x_eq‖ < c → Tendsto φ atTop (𝓝 x_eq)

def TrajectoryGloballyAsymptoticallyStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  LyapunovStable f x_eq ∧
  ∀ (t₀ : ℝ) (φ : ℝ → ℝⁿ), IsIntegralCurveOn φ (fun _ y => f y) (Ici t₀) →
    Tendsto φ atTop (𝓝 x_eq)

def Unstable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ¬ LyapunovStable f x_eq

def SublevelSet (V : ℝⁿ → ℝ) (c : ℝ) : Set ℝⁿ := {x | V x ≤ c}

structure IsLocalLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) (D : Set ℝⁿ) : Prop where
  hD_open     : IsOpen D
  hD_mem      : x_eq ∈ D
  hcont       : Continuous V
  hV_diff     : Differentiable ℝ V
  hzero       : V x_eq = 0
  hpos        : ∀ x ∈ D, x ≠ x_eq → 0 < V x
  hLie_nonpos : ∀ x ∈ D, fderiv ℝ V x (f x) ≤ 0

structure IsStrictLocalLyapunovFunction
    (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) (D : Set ℝⁿ) : Prop where
  hD_open   : IsOpen D
  hD_mem    : x_eq ∈ D
  hcont     : Continuous V
  hV_c1     : ContDiff ℝ 1 V
  hzero     : V x_eq = 0
  hpos      : ∀ x ∈ D, x ≠ x_eq → 0 < V x
  hequil    : f x_eq = 0
  hLie_neg  : ∀ x ∈ D, x ≠ x_eq → fderiv ℝ V x (f x) < 0
  hcompact  : ∃ c > 0, SublevelSet V c ⊆ D ∧ IsCompact (SublevelSet V c)

structure IsStrictLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) : Prop where
  hcont             : Continuous V
  hV_c1             : ContDiff ℝ 1 V
  hzero             : V x_eq = 0
  hpos              : ∀ x : ℝⁿ, x ≠ x_eq → 0 < V x
  hequil            : f x_eq = 0
  hLie_neg          : ∀ x : ℝⁿ, x ≠ x_eq → fderiv ℝ V x (f x) < 0
  hbounded_sublevel : ∀ c : ℝ, IsCompact {x : ℝⁿ | V x ≤ c}

structure IsAsymptoticLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) : Prop where
  hcont    : Continuous V
  hV_c1    : ContDiff ℝ 1 V
  hzero    : V x_eq = 0
  hpos     : ∀ x : ℝⁿ, x ≠ x_eq → 0 < V x
  hequil   : f x_eq = 0
  hLie_neg : ∀ x : ℝⁿ, x ≠ x_eq → fderiv ℝ V x (f x) < 0
  hradial  : Filter.Tendsto V (Filter.comap norm Filter.atTop) Filter.atTop

def IsPositivelyInvariant (S : Set ℝⁿ) (f : ℝⁿ → ℝⁿ) : Prop :=
  ∀ (t₀ t₁ : ℝ) (φ : ℝ → ℝⁿ), IsTrajectoryOn φ f t₀ t₁ →
    φ t₀ ∈ S → ∀ t ∈ Icc t₀ t₁, φ t ∈ S

@[powerlib_foundation] lemma isCompact_sublevel_set
    (V : ℝⁿ → ℝ) (hcont : Continuous V)
    (hradial : Filter.Tendsto V (Filter.comap norm Filter.atTop) Filter.atTop)
    (c : ℝ) : IsCompact (SublevelSet V c) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_Iic.preimage hcont
  · rw [comap_norm_atTop, Metric.cobounded_eq_cocompact] at hradial
    have hev : {x : ℝⁿ | c < V x} ∈ Filter.cocompact ℝⁿ :=
      hradial (Filter.eventually_gt_atTop c)
    rw [Filter.mem_cocompact] at hev
    obtain ⟨K, hK_compact, hK⟩ := hev
    rw [Metric.isBounded_iff_subset_closedBall 0]
    obtain ⟨R, hR⟩ := hK_compact.isBounded.subset_closedBall 0
    refine ⟨R, fun x hx => hR ?_⟩
    by_contra hxK
    have hVx : c < V x := hK (Set.mem_compl hxK)
    exact absurd hVx (not_lt.mpr hx)

end powerlib.Dynamics
