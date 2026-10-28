import dependencies.LeanForControl
import theorem.Dynamics.State
import theorem.Flow.Certificate

/-! # LaSalle invariance principle (LeanForControl interface)

Thin powerlib-named wrappers. Every proof is a direct application of the upstream
declaration named in its docstring; nothing is re-proved. The upstream module is
`LeanForControl.Stability.LaSalle` (LeanForControl rev `7507ed04`, imported through
`dependencies.LeanForControl`).

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
* Wrappers of `LeanForControl.Stability.LaSalle` (`_root_.omegaLimitTraj`,
  `_root_.mem_omegaLimitTraj_iff`, `_root_.isPositivelyInvariant_omegaLimitTraj`,
  `_root_.lieDeriv_eq_zero_on_omegaLimitTraj`, `_root_.LieDerivZeroSet`,
  `_root_.lasalle_invariance_principle`, `_root_.lasalle_local_asymptotic_stable` (Barbashin),
  `_root_.lasalle_global_asymptotic_stable` (Krasovskii)), under the upstream names in
  `powerlib.Dynamics.LaSalle`: `LieDerivZeroSet` (`lieDerivZeroSet_def`),
  `mem_omegaLimitTraj_iff`, `isPositivelyInvariant_omegaLimitTraj`,
  `lieDeriv_eq_zero_on_omegaLimitTraj`, `lasalle_invariance_principle`,
  `lasalle_local_asymptotic_stable`, `lasalle_global_asymptotic_stable`; `_root_.omegaLimitTraj`
  itself is used directly.
* `globallyAsymptoticallyStable_of_lasalle`: the upstream Krasovskii conclusion has no
  solution-existence clause; this wrapper adds the equilibrium and forward completeness (from the
  global Lipschitz bound, `Flow.forwardComplete_of_lipschitzWith`) to reach the Flow sentence
  `Flow.GloballyAsymptoticallyStable`.

The wrapper of LeanForControl's exponential Chetaev criterion
(`NonlinearInstability.unstable_of_exponential_chetaev`) is
`Dynamics.unstable_of_exponential_chetaev` in `theorem/Dynamics/Instability.lean`, with the other
instability criteria.

The transitive LeanForControl imports of the upstream module are
`Analysis.{Continuity, IntegralCurves, Integrals}`,
`ODEs.{GronwallBellman, ODE_properties, PicardLindelof}`, `Stability.{Autonomous,
DefsAutonomous}`; none of `LeanForControl.axioms`, `Comparison.*`, `LyapunovBounds`,
`KLCharacterization*`, `ClassKDecay` is involved, and `#print axioms` of every wrapped
theorem is `[propext, Classical.choice, Quot.sound]`.
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

/-- Membership in the ω-limit set `_root_.omegaLimitTraj φ` of a forward trajectory `φ`
(Khalil's positive limit set `L⁺`): `φ` is frequently in every neighbourhood of `y`.
Upstream: `_root_.mem_omegaLimitTraj_iff`. -/
@[tmio T, powerlib_foundation] theorem mem_omegaLimitTraj_iff {φ : ℝ → ℝⁿ} {y : ℝⁿ} :
    y ∈ _root_.omegaLimitTraj φ ↔ ∀ U ∈ 𝓝 y, ∃ᶠ t in atTop, φ t ∈ U :=
  _root_.mem_omegaLimitTraj_iff

/-- The ω-limit set `_root_.omegaLimitTraj φ` of a forward trajectory is positively invariant
(Khalil, Lemma 4.1).
Upstream: `_root_.isPositivelyInvariant_omegaLimitTraj`. -/
@[tmio T, powerlib_foundation] theorem isPositivelyInvariant_omegaLimitTraj
    {f : ℝⁿ → ℝⁿ} {K : NNReal} (hf : LipschitzWith K f)
    {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) :
    IsPositivelyInvariant (_root_.omegaLimitTraj φ) f :=
  _root_.isPositivelyInvariant_omegaLimitTraj hf hφ

/-- `V̇` vanishes on the ω-limit set of a trajectory confined to a compact positively
invariant set where `V̇ ≤ 0`. Upstream: `_root_.lieDeriv_eq_zero_on_omegaLimitTraj`. -/
@[tmio T, powerlib_foundation] theorem lieDeriv_eq_zero_on_omegaLimitTraj
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {Ω : Set ℝⁿ} {K : NNReal}
    (hf_lip : LipschitzWith K f) (hf_c1 : ContDiff ℝ 1 f) (hV_c1 : ContDiff ℝ 1 V)
    (hΩ_compact : IsCompact Ω) (hΩ_inv : IsPositivelyInvariant Ω f)
    (hLie : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) (hφ0 : φ 0 ∈ Ω) :
    ∀ y ∈ _root_.omegaLimitTraj φ, fderiv ℝ V y (f y) = 0 :=
  _root_.lieDeriv_eq_zero_on_omegaLimitTraj hf_lip hf_c1 hV_c1 hΩ_compact hΩ_inv hLie hφ hφ0

/-- LaSalle's invariance principle (Khalil, Theorem 4.4; positively-invariant variant).
Upstream: `_root_.lasalle_invariance_principle`. -/
@[tmio T, powerlib_foundation] theorem lasalle_invariance_principle
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {Ω M : Set ℝⁿ} {K : NNReal}
    (hΩ_compact : IsCompact Ω) (hΩ_inv : IsPositivelyInvariant Ω f)
    (hf_lip : LipschitzWith K f) (hf_c1 : ContDiff ℝ 1 f) (hV_c1 : ContDiff ℝ 1 V)
    (hLie : ∀ x ∈ Ω, fderiv ℝ V x (f x) ≤ 0)
    {φ : ℝ → ℝⁿ} (hφ : IsIntegralCurveOn φ (fun _ x => f x) (Ici 0)) (hφ0 : φ 0 ∈ Ω)
    (hM : ∀ N ⊆ LieDerivZeroSet f V Ω, IsPositivelyInvariant N f → N ⊆ M) :
    Tendsto φ atTop (𝓝ˢ M) :=
  _root_.lasalle_invariance_principle hΩ_compact hΩ_inv hf_lip hf_c1 hV_c1 hLie hφ hφ0 hM

/-- Barbashin's theorem: local asymptotic stability via LaSalle (Khalil, Corollary 4.1).
Upstream: `_root_.lasalle_local_asymptotic_stable`. -/
@[tmio T, powerlib_foundation] theorem lasalle_local_asymptotic_stable
    {D : Set ℝⁿ} {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV_c1 : ContDiff ℝ 1 V) (hV_local : IsLocalLyapunovFunction f V x_eq D)
    {c : ℝ} (hc_pos : 0 < c) (hΩ_sub_D : SublevelSet V c ⊆ D)
    (hΩ_compact : IsCompact (SublevelSet V c))
    (hΩ_inv : IsPositivelyInvariant (SublevelSet V c) f)
    {K : NNReal} (hf_lip : LipschitzWith K f) (hf_c1 : ContDiff ℝ 1 f)
    (hLasalle : ∀ N ⊆ LieDerivZeroSet f V (SublevelSet V c),
      IsPositivelyInvariant N f → N ⊆ {x_eq}) :
    LocalAsymptoticStable f x_eq :=
  _root_.lasalle_local_asymptotic_stable hn hV_c1 hV_local hc_pos hΩ_sub_D hΩ_compact hΩ_inv
    hf_lip hf_c1 hLasalle

/-- Krasovskii's theorem: global asymptotic stability via LaSalle (Khalil, Corollary 4.2).
The conclusion is the upstream trajectory predicate (no solution-existence clause).
Upstream: `_root_.lasalle_global_asymptotic_stable`. -/
@[tmio T, powerlib_foundation] theorem lasalle_global_asymptotic_stable
    {f : ℝⁿ → ℝⁿ} {V : ℝⁿ → ℝ} {x_eq : ℝⁿ} (hn : 0 < n)
    (hV_c1 : ContDiff ℝ 1 V) (hzero : V x_eq = 0) (hpos : ∀ x : ℝⁿ, x ≠ x_eq → 0 < V x)
    (hLie : ∀ x : ℝⁿ, fderiv ℝ V x (f x) ≤ 0)
    (hradial : Tendsto V (comap norm atTop) atTop)
    {K : NNReal} (hf_lip : LipschitzWith K f) (hf_c1 : ContDiff ℝ 1 f)
    (hLasalle : ∀ c : ℝ, ∀ N ⊆ LieDerivZeroSet f V (SublevelSet V c),
      IsPositivelyInvariant N f → N ⊆ {x_eq}) :
    GlobalAsymptoticStable f x_eq :=
  _root_.lasalle_global_asymptotic_stable hn hV_c1 hzero hpos hLie hradial hf_lip hf_c1
    hLasalle

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
    lasalle_global_asymptotic_stable hn hV_c1 hzero hpos hLie hradial hf_lip hf_c1 hLasalle⟩

end powerlib.Dynamics.LaSalle
