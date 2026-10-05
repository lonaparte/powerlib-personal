import dependencies.LeanForControl
import theorem.Dynamics.Defs

noncomputable section
namespace powerlib.Dynamics

abbrev IsEquilibrium := @_root_.IsEquilibrium

abbrev LyapunovStable := @_root_.LyapunovStable

abbrev LocallyExponentiallyStable := @_root_.LocallyExponentiallyStable

abbrev LocalAsymptoticStable := @_root_.LocalAsymptoticStable

abbrev Unstable := @_root_.Unstable

abbrev SublevelSet := @_root_.SublevelSet

abbrev IsLocalLyapunovFunction := @_root_.IsLocalLyapunovFunction

abbrev IsStrictLocalLyapunovFunction := @_root_.IsStrictLocalLyapunovFunction

abbrev IsStrictLyapunovFunction := @_root_.IsStrictLyapunovFunction

abbrev IsAsymptoticLyapunovFunction := @_root_.IsAsymptoticLyapunovFunction

abbrev IsPositivelyInvariant := @_root_.IsPositivelyInvariant

abbrev TrajectoryGloballyAsymptoticallyStable := @_root_.GlobalAsymptoticStable

open Set Filter Topology
variable {n : ℕ}
local notation "ℝⁿ" => State n

@[powerlib_foundation] theorem isCompact_sublevel_set
    (V : ℝⁿ → ℝ) (hcont : Continuous V)
    (hradial : Filter.Tendsto V (Filter.comap norm Filter.atTop) Filter.atTop)
    (c : ℝ) : IsCompact (SublevelSet V c) :=
  _root_.isCompact_sublevel_set V hcont hradial c

@[powerlib_foundation] theorem isTrajectoryOn_upstream_iff
    {φ : ℝ → ℝⁿ} {f : ℝⁿ → ℝⁿ} {a b : ℝ} :
    IsTrajectoryOn φ f a b ↔ _root_.IsTrajectoryOn φ f a b := Iff.rfl

@[powerlib_foundation] theorem trajectoryStability_upstream_iff
    {f : ℝⁿ → ℝⁿ} {equilibrium : ℝⁿ} :
    TrajectoryGloballyAsymptoticallyStable f equilibrium ↔
      _root_.GlobalAsymptoticStable f equilibrium := Iff.rfl

end powerlib.Dynamics
