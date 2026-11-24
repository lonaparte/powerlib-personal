import dependencies.LeanForControl
import theorem.Dynamics.State
import theorem.Flow.Certificate

/-! # LaSalle invariance principle (LeanForControl interface)

The interface to the upstream module `LeanForControl.Stability.LaSalle` (LeanForControl rev
`7507ed04`, imported through `dependencies.LeanForControl`). The upstream theorems are used
directly under their `_root_` names; nothing is re-proved or re-exported.

Scope.
* An arbitrary autonomous continuous-time ODE `ẋ = f x` on
  `Dynamics.State n = EuclideanSpace ℝ (Fin n)`; no input, delay, switching, or
  time-variation. Solutions are `IsIntegralCurveOn` curves (one-sided derivatives at
  endpoints). `V̇ x` is `fderiv ℝ V x (f x)`.
* Every theorem here is a generic semantic implication about an arbitrary field `f` and function
  `V`; no model family is defined or fixed, so they are foundation results (Rules §3). The
  predicates are LeanForControl's (`IsPositivelyInvariant`, `IsLocalLyapunovFunction`,
  `SublevelSet`, `LocalAsymptoticStable`, `GlobalAsymptoticStable`, `Unstable`) used directly;
  likewise the ω-limit set of a forward trajectory `φ` is LeanForControl's
  `_root_.omegaLimitTraj φ` (the points `y` such that `φ t` is frequently in every neighbourhood
  of `y` as `t → ∞`; Khalil's positive limit set `L⁺`), written directly in the statements
  (behaviour is defined only in the semantic layer); `LocalAsymptoticStable` and `Unstable` are
  exactly the Flow sentences `.locallyAsymptoticallyStable` and `.unstable`. Model families that
  use these criteria publish their conclusions as connection statements.
* Hypotheses that differ from Khalil's textbook statements (inherited from upstream):
  LaSalle requires `f` globally `LipschitzWith` **and** `ContDiff ℝ 1`
  (`theorem/Dynamics/LaSalle/Basin.lean` removes the global Lipschitz requirement by a cutoff);
  the target set `M` must contain every *positively* invariant subset of
  `LieDerivZeroSet f V Ω = {x ∈ Ω | V̇ x = 0}` (stronger than "largest invariant subset");
  Barbashin needs the compact sublevel set to be positively invariant as a hypothesis.

Source: LeanForControl (Khalil, *Nonlinear Systems*, 3rd ed., Lemma 4.1, Theorem 4.4,
Corollaries 4.1–4.2; Hahn, *Stability of Motion*, Chetaev's method).

Results.
* `LieDerivZeroSet` (`lieDerivZeroSet_def`): `_root_.LieDerivZeroSet` under the powerlib name.
  The upstream results `_root_.mem_omegaLimitTraj_iff`,
  `_root_.isPositivelyInvariant_omegaLimitTraj` (Khalil, Lemma 4.1),
  `_root_.lieDeriv_eq_zero_on_omegaLimitTraj`, `_root_.lasalle_invariance_principle` (Theorem
  4.4), `_root_.lasalle_local_asymptotic_stable` (Barbashin, Corollary 4.1) and
  `_root_.lasalle_global_asymptotic_stable` (Krasovskii, Corollary 4.2) are used directly, as is
  `_root_.omegaLimitTraj`.
* `globallyAsymptoticallyStable_of_lasalle`: the upstream Krasovskii conclusion has no
  solution-existence clause; this wrapper adds the equilibrium and forward completeness (from the
  global Lipschitz bound, `Flow.forwardComplete_of_lipschitzWith`) to reach the Flow sentence
  `Flow.GloballyAsymptoticallyStable`.

LeanForControl's exponential Chetaev criterion
(`NonlinearInstability.unstable_of_exponential_chetaev`) is likewise used directly; the other
instability criteria are in `theorem/Dynamics/Instability.lean`.

The transitive LeanForControl imports of the upstream module are
`Analysis.{Continuity, IntegralCurves, Integrals}`,
`ODEs.{GronwallBellman, ODE_properties, PicardLindelof}`, `Stability.{Autonomous,
DefsAutonomous}`; none of the modules `LeanForControl.axioms`, `Comparison.*`,
`Stability.{LyapunovBounds, KLCharacterization*, ClassKDecay}` is involved, and `#print axioms`
of every upstream theorem used is `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section
namespace powerlib.Dynamics.LaSalle
open Set Filter Topology
variable {n : ℕ}
local notation "ℝⁿ" => State n

/-- `{x ∈ Ω | fderiv ℝ V x (f x) = 0}` (upstream `_root_.LieDerivZeroSet`). -/
abbrev LieDerivZeroSet := @_root_.LieDerivZeroSet

@[tmio T, powerlib_foundation] theorem lieDerivZeroSet_def (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (Ω : Set ℝⁿ) :
    LieDerivZeroSet f V Ω = {x ∈ Ω | fderiv ℝ V x (f x) = 0} := rfl

/-- Krasovskii's theorem in the Flow semantics: with an equilibrium at `x_eq`, the LaSalle
hypotheses give `Flow.GloballyAsymptoticallyStable` (equilibrium, a solution through every state
from the global Lipschitz bound, and the upstream trajectory predicate). -/
@[tmio T, powerlib_foundation] theorem globallyAsymptoticallyStable_of_lasalle
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n) (heq : IsEquilibrium f x_eq)
    (hV_c1 : ContDiff ℝ 1 V) (hzero : V x_eq = 0) (hpos : ∀ x : ℝⁿ, x ≠ x_eq → 0 < V x)
    (hLie : ∀ x : ℝⁿ, fderiv ℝ V x (f x) ≤ 0)
    (hradial : Tendsto V (comap norm atTop) atTop)
    {K : NNReal} (hf_lip : LipschitzWith K f) (hf_c1 : ContDiff ℝ 1 f)
    (hLasalle : ∀ c : ℝ, ∀ N ⊆ LieDerivZeroSet f V (SublevelSet V c),
      IsPositivelyInvariant N f → N ⊆ {x_eq}) :
    Flow.GloballyAsymptoticallyStable f x_eq :=
  ⟨heq, Flow.forwardComplete_of_lipschitzWith hf_lip,
    _root_.lasalle_global_asymptotic_stable hn hV_c1 hzero hpos hLie hradial hf_lip hf_c1
      hLasalle⟩

end powerlib.Dynamics.LaSalle
