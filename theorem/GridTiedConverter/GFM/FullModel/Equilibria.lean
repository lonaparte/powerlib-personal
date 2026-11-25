import theorem.GridTiedConverter.GFM.FullModel.Saddle
import theorem.GridTiedConverter.GFM.Equilibria
import theorem.SpecialFunctions.PolynomialSigns

/-! # The 13-state grid-forming converter: equilibrium count per period

Model boundary.
* The 13-state model of `theorem/GridTiedConverter/GFM/FullModel/Basic.lean` (state order
  `(i, v_c, i_g, ξ, ζ, δ, Δω, Q_f)` in dq components, `x 10 = δ`, system frame for the plant,
  controller frame for the integrators, currents out of the converter positive, export-positive
  per-unit power), continuous time, autonomous, no input.
* Range of the statements: no virtual impedance (`Z_v = 0`), nondegenerate fast block
  (`L_f, C_f, L_g, K_ic, K_iv ≠ 0`, `Z_g ≠ 0`), `M, ω_q ≠ 0`; every other gain is free. Without
  Q–V droop (`n_q = 0`, internal EMF `E = E₀`): `E₀ V > 0`. With droop: the physical range of
  `theorem/GridTiedConverter/GFM/QVDroop.lean`, `n_q > 0`, `ω₀L_g > 0`, `V > 0`,
  `E₀ + n_q Q_ref > 0`; an equilibrium is physical when its droop EMF
  `E = E₀ − n_q (Q_f − Q_ref)` is positive (equilibria of the formal model with `E < 0` are
  counted by `Params.ncard_equilibria_window_droop` with `T = (−∞, 0)`). Virtual impedance with
  droop (`Z_v ≠ 0`, `n_q ≠ 0`) is not counted here.
* Level: the equilibrium set of the field with angle in a period window `[a, a + 2π)` and its
  cardinality; no stability statement (the saddle branch is unstable by
  `theorem/GridTiedConverter/GFM/FullModel/Saddle.lean`).

Scaffold of the reading of the reduced model:
`theorem/GridTiedConverter/GFM/FullModel/FullModelSwing.agda`.

Source: GFM counterpart study, full-order model note (t5 (b): "n_q = 0: two angles iff
|P_ref − c₀| ≤ A") and equilibria note (t6 (a): "count per window: 2 if |P_ref − c₀| < A, 1 double
zero if =, 0 if >"; t6 (b): the droop quartic; t6 (c): the full-order equilibria with `(c₀, A, α)`
from `Z_g` only), checked numerically there; the counting laws of the reduced models
`theorem/GridTiedConverter/GFM/Equilibria.lean` and `theorem/GridTiedConverter/GFM/QVDroop.lean`
(elimination, droop quartic, Descartes bound, parity); the intermediate value theorem and the
factorization `f = (X − r₁)(X − r₂) Q` over two positive roots for the droop count.

Results.
* `Params.lift`: a reduced swing state `(δ, Δω)` read as the full-order quasi-steady state
  `qssState δ Δω Q(δ, E₀)` (reactive-power filter at the quasi-steady reactive power); injective
  (`Params.lift_injective`).
* `Params.equilibria_window`: the equilibria of the 13-state field with angle in a window are the
  lifts of the equilibria of the reduced swing machine `Params.swingParams` with angle in the same
  window (`Params.field_eq_zero_iff`, `Params.Pq_eq_swing`); `Params.ncard_equilibria_window`: they
  are as many.
* The count per window, read from the reduced laws `Reduced.two_equilibria_per_period` and
  `Reduced.fold_equilibrium_per_period`: `Params.two_equilibria_per_period`
  (`|P_ref − E₀²R_g/|Z_g|²| < E₀V/|Z_g|`: exactly two equilibria, the lifts of `δ_s` and `δ_u`
  reduced into the window) and `Params.fold_equilibrium_per_period` (equality: exactly one, the
  double zero `δ_s = δ_u`). Beyond the bound there is no equilibrium at all
  (`Params.exists_equilibrium_iff`).
* With Q–V droop (`Z_v = 0`, any droop gain): `Params.equilibria_window_droop` — the equilibria
  with angle in a window and droop EMF in a set `T` are the quasi-steady lifts `Params.graph`
  (injective, `Params.graph_injective`) of the equilibria of the reduced droop model
  `Params.qvDroop` in the same window with EMF in `T`; `Params.ncard_equilibria_window_droop`
  (`0 ∉ T`): as many as the roots of the droop quartic `f(E) = u(E)² + w(E)² − V²E²` in `T`
  (`QVDroop.ncard_equilibriaWindow`).
* The exact count of physical equilibria per window with droop, in the physical range, for every
  controller gain — `0`, `1` or `2` (at most two: Descartes, `QVDroop.countP_pos_roots_le_two`),
  decided by the balance point `(u(E), w(E))` (`QVDroop.u = E² + βE − γ`,
  `QVDroop.w = ρE + κ`, `β = ω₀L_g/n_q`, `ρ = R_g/n_q`, `q₀ = E₀/n_q + Q_ref`,
  `γ = R_g P_ref + ω₀L_g q₀`, `κ = ω₀L_g P_ref − R_g q₀`) against the circle of radius `V E`:
  `Params.two_physical_equilibria_iff` (exactly two iff `u(E)² + w(E)² < V²E²` for some `E > 0`),
  `Params.fold_physical_equilibrium_iff` (exactly one iff `u(E)² + w(E)² ≥ V²E²` for every
  `E > 0` with equality at some `E > 0`: the fold, a positive double root of `f`,
  `QVDroop.rootMultiplicity_eq_two_of_ncard_eq_one`), `Params.no_physical_equilibrium_iff`
  (none iff `u(E)² + w(E)² > V²E²` for every `E > 0`) — the droop counterparts of
  `Params.two_equilibria_per_period`, `Params.fold_equilibrium_per_period` and
  `Params.exists_equilibrium_iff`. The polynomial step (private): a real polynomial with
  `f(0) > 0`, positive leading coefficient and at most two positive roots counted with
  multiplicity has two distinct positive roots iff it is negative somewhere on `(0, ∞)`, and none
  iff it is positive there.

Family and connection conclusions.
The module defines no Family and states no behaviour: the equilibrium sets and their counts are
static evidence on the model.
-/

noncomputable section
namespace powerlib.GFM.FullModel
open Real Set
open powerlib.Dynamics (State)
open powerlib.Synchronous (SwingParams)

namespace Params

variable (p : Params)

/-- A reduced swing state `(δ, Δω)` read as the full-order quasi-steady state
`qssState δ Δω Q(δ, E₀)`, with the reactive-power filter at the quasi-steady reactive power. -/
def lift (y : State 2) : State 13 := p.qssState (y 0) (y 1) (p.Qq (y 0) p.E0)

@[tmio M, powerlib_domain] theorem lift_injective : Function.Injective p.lift := by
  intro y y' h
  have h0 : y 0 = y' 0 := by simpa [lift] using congrArg (· 10) h
  have h1 : y 1 = y' 1 := by simpa [lift] using congrArg (· 11) h
  exact PhasePlane.ext_iff'.mpr ⟨h0, h1⟩

@[tmio M, powerlib_domain] private theorem lift_mk (δ : ℝ) :
    p.lift (PhasePlane.mk δ 0) = p.qssState δ 0 (p.Qq δ p.E0) := rfl

/-- The equilibria of the 13-state field with angle in a window `[a, a + 2π)` are the lifts of the
equilibria of the reduced swing machine `swingParams` with angle in the same window (no droop, no
virtual impedance). Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem equilibria_window (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0) (hZg : p.Zg ≠ 0) (hM : p.M ≠ 0)
    (hωq : p.ωq ≠ 0) (hnq : p.nq = 0) (hZv : p.Zv = 0) (a : ℝ) :
    {x : State 13 | p.field x = 0 ∧ x 10 ∈ Ico a (a + 2 * π)} =
      p.lift '' {y : State 2 | p.swingParams.field y = 0 ∧ y 0 ∈ Ico a (a + 2 * π)} := by
  have hZt : p.Zt ≠ 0 := by rwa [Zt, hZv, add_zero]
  have hE : ∀ Qf, p.emf Qf = p.E0 := fun Qf => by simp [emf, hnq]
  have hiff := p.field_eq_zero_iff hLf hCf hLg hKic hKiv hZt hM hωq
  ext x
  simp only [mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨hx, hw⟩
    obtain ⟨δ, Qf, rfl, hP, hQ⟩ := (hiff x).mp hx
    refine ⟨PhasePlane.mk δ 0, ⟨(p.swingParams.field_eq_zero_iff hM _).mpr ⟨rfl, ?_⟩, ?_⟩, ?_⟩
    · rw [PhasePlane.mk_apply_zero, ← p.Pq_eq_swing hZv hZg, ← hE Qf, hP]; rfl
    · simpa using hw
    · rw [lift_mk, ← hE Qf, hQ]
  · rintro ⟨y, ⟨hy, hw⟩, rfl⟩
    obtain ⟨h1, hP⟩ := (p.swingParams.field_eq_zero_iff hM y).mp hy
    refine ⟨(hiff _).mpr ⟨y 0, p.Qq (y 0) p.E0, by rw [lift, h1], ?_, by rw [hE]⟩, ?_⟩
    · rw [hE, p.Pq_eq_swing hZv hZg, hP]; rfl
    · simpa [lift] using hw

/-- Counting law: the equilibria of the 13-state field with angle in a window `[a, a + 2π)` are as
many as those of the reduced swing machine `swingParams` (`lift` is injective).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem ncard_equilibria_window (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0) (hZg : p.Zg ≠ 0) (hM : p.M ≠ 0)
    (hωq : p.ωq ≠ 0) (hnq : p.nq = 0) (hZv : p.Zv = 0) (a : ℝ) :
    {x : State 13 | p.field x = 0 ∧ x 10 ∈ Ico a (a + 2 * π)}.ncard =
      {y : State 2 | p.swingParams.field y = 0 ∧ y 0 ∈ Ico a (a + 2 * π)}.ncard := by
  rw [p.equilibria_window hLf hCf hLg hKic hKiv hZg hM hωq hnq hZv,
    Set.ncard_image_of_injective _ p.lift_injective]

/-- `|P_ref − E₀²R_g/|Z_g|²| < E₀V/|Z_g|` (no droop, no virtual impedance): in every window
`[a, a + 2π)` the 13-state field has exactly two equilibria, the quasi-steady states at the stable
and saddle angles `δ_s`, `δ_u` of `swingParams` reduced into the window, for every choice of the
controller gains (`Reduced.two_equilibria_per_period`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem two_equilibria_per_period (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0) (hZg : p.Zg ≠ 0) (hM : p.M ≠ 0)
    (hωq : p.ωq ≠ 0) (hnq : p.nq = 0) (hZv : p.Zv = 0) (hEV : 0 < p.E0 * p.V)
    (h : |p.Pref - p.Rg / ‖p.Zg‖ ^ 2 * p.E0 ^ 2| < p.E0 * p.V / ‖p.Zg‖) (a : ℝ) :
    {x : State 13 | p.field x = 0 ∧ x 10 ∈ Ico a (a + 2 * π)}.ncard = 2 ∧
      {x : State 13 | p.field x = 0 ∧ x 10 ∈ Ico a (a + 2 * π)} =
        {p.qssState (toIcoMod two_pi_pos a p.swingParams.deltaS) 0
            (p.Qq (toIcoMod two_pi_pos a p.swingParams.deltaS) p.E0),
          p.qssState (toIcoMod two_pi_pos a p.swingParams.deltaU) 0
            (p.Qq (toIcoMod two_pi_pos a p.swingParams.deltaU) p.E0)} := by
  have hk : 0 < p.swingParams.k₂ := div_pos hEV (norm_pos_iff.mpr hZg)
  obtain ⟨hn, hs⟩ := Reduced.two_equilibria_per_period p.swingParams hM hk h a
  refine ⟨?_, ?_⟩
  · rw [p.ncard_equilibria_window hLf hCf hLg hKic hKiv hZg hM hωq hnq hZv, hn]
  · rw [p.equilibria_window hLf hCf hLg hKic hKiv hZg hM hωq hnq hZv, hs, Set.image_pair,
      lift_mk, lift_mk]

/-- `|P_ref − E₀²R_g/|Z_g|²| = E₀V/|Z_g|` (fold of the power–angle curve, no droop, no virtual
impedance): in every window the 13-state field has exactly one equilibrium, the quasi-steady state
at the double zero `δ_s = δ_u` (`Reduced.fold_equilibrium_per_period`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem fold_equilibrium_per_period (hLf : p.Lf ≠ 0)
    (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0) (hZg : p.Zg ≠ 0)
    (hM : p.M ≠ 0) (hωq : p.ωq ≠ 0) (hnq : p.nq = 0) (hZv : p.Zv = 0) (hEV : 0 < p.E0 * p.V)
    (h : |p.Pref - p.Rg / ‖p.Zg‖ ^ 2 * p.E0 ^ 2| = p.E0 * p.V / ‖p.Zg‖) (a : ℝ) :
    {x : State 13 | p.field x = 0 ∧ x 10 ∈ Ico a (a + 2 * π)}.ncard = 1 ∧
      {x : State 13 | p.field x = 0 ∧ x 10 ∈ Ico a (a + 2 * π)} =
        {p.qssState (toIcoMod two_pi_pos a p.swingParams.deltaS) 0
            (p.Qq (toIcoMod two_pi_pos a p.swingParams.deltaS) p.E0)} := by
  have hk : 0 < p.swingParams.k₂ := div_pos hEV (norm_pos_iff.mpr hZg)
  obtain ⟨hn, hs⟩ := Reduced.fold_equilibrium_per_period p.swingParams hM hk h a
  refine ⟨?_, ?_⟩
  · rw [p.ncard_equilibria_window hLf hCf hLg hKic hKiv hZg hM hωq hnq hZv, hn]
  · rw [p.equilibria_window hLf hCf hLg hKic hKiv hZg hM hωq hnq hZv, hs, Set.image_singleton,
      lift_mk]

/-! ### With Q–V droop -/

/-- With Q–V droop and without virtual impedance, the equilibria of the 13-state field with
angle in a window `[a, a + 2π)` and droop EMF in a set `T` are the quasi-steady lifts `graph` of
the equilibria of the reduced Q–V droop model `qvDroop` with angle in the window and EMF in `T`,
for every gain. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem equilibria_window_droop (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0) (hZg : p.Zg ≠ 0) (hM : p.M ≠ 0)
    (hωq : p.ωq ≠ 0) (hZv : p.Zv = 0) (T : Set ℝ) (a : ℝ) :
    {x : State 13 | p.field x = 0 ∧ x 10 ∈ Ico a (a + 2 * π) ∧ p.emf (x 12) ∈ T} =
      p.graph '' p.qvDroop.equilibriaWindow T a := by
  have hZt : p.Zt ≠ 0 := by rwa [Zt, hZv, add_zero]
  have hiff := p.field_eq_zero_iff hLf hCf hLg hKic hKiv hZt hM hωq
  have hq := p.qvDroop.field_eq_zero_iff hM hωq
  have hE : ∀ Qf, p.qvDroop.emf Qf = p.emf Qf := fun _ => rfl
  ext x
  simp only [mem_ofPred_eq, mem_image, QVDroop.equilibriaWindow]
  constructor
  · rintro ⟨hx, hw, hT⟩
    obtain ⟨δ, Qf, rfl, hP, hQ⟩ := (hiff x).mp hx
    refine ⟨Dynamics.mk3 δ 0 Qf, ⟨(hq _).mpr ⟨Dynamics.mk3_one _ _ _, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · rw [Dynamics.mk3_zero, Dynamics.mk3_two, hE, ← p.Pq_eq_qvDroop hZv hZg, hP]; rfl
    · rw [Dynamics.mk3_zero, Dynamics.mk3_two, hE, ← p.Qq_eq_qvDroop hZv hZg, hQ]
    · simpa using hw
    · simpa [hE] using hT
    · simp [graph]
  · rintro ⟨y, ⟨hy, hw, hT⟩, rfl⟩
    obtain ⟨h1, hP, hQ⟩ := (hq y).mp hy
    refine ⟨(hiff _).mpr ⟨y 0, y 2, by rw [graph, h1], ?_, ?_⟩, by simpa [graph] using hw,
      by simpa [graph, hE] using hT⟩
    · rw [p.Pq_eq_qvDroop hZv hZg, ← hE, hP]; rfl
    · rw [p.Qq_eq_qvDroop hZv hZg, ← hE, hQ]

@[tmio M, powerlib_domain] theorem graph_injective : Function.Injective p.graph := by
  intro y y' h
  have h0 : y 0 = y' 0 := by simpa [graph] using congrArg (· 10) h
  have h1 : y 1 = y' 1 := by simpa [graph] using congrArg (· 11) h
  have h2 : y 2 = y' 2 := by simpa [graph] using congrArg (· 12) h
  exact Dynamics.state3_ext h0 h1 h2

/-- Counting law with droop (`Z_v = 0`): in every window `[a, a + 2π)` the equilibria of the
13-state field whose droop EMF lies in a set `T ∌ 0` are as many as the roots of the droop quartic
`qvDroop.quartic` in `T` (`QVDroop.ncard_equilibriaWindow`; `lift` by `graph` is injective).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem ncard_equilibria_window_droop (hLf : p.Lf ≠ 0)
    (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0) (hM : p.M ≠ 0)
    (hωq : p.ωq ≠ 0) (hZv : p.Zv = 0) (hnq : p.nq ≠ 0) (hX : p.ω0 * p.Lg ≠ 0) (hV : p.V ≠ 0)
    {T : Set ℝ} (hT : (0 : ℝ) ∉ T) (a : ℝ) :
    {x : State 13 | p.field x = 0 ∧ x 10 ∈ Ico a (a + 2 * π) ∧ p.emf (x 12) ∈ T}.ncard =
      {E | E ∈ T ∧ p.qvDroop.quartic.IsRoot E}.ncard := by
  have hZg : p.Zg ≠ 0 := fun h => hX (by simpa [Zg_eq] using congrArg Complex.im h)
  rw [p.equilibria_window_droop hLf hCf hLg hKic hKiv hZg hM hωq hZv,
    Set.ncard_image_of_injective _ p.graph_injective]
  exact p.qvDroop.ncard_equilibriaWindow hM hωq hnq (p.qvDroop.zsq_pos hX).ne' hV hT a

end Params

/-! ### Positive roots of a polynomial with `P(0) > 0` (support for the droop count) -/

open Polynomial in
/-- The positive roots of a nonzero real polynomial form a finite set. -/
@[tmio T, powerlib_foundation] private theorem finite_pos_isRoot {P : ℝ[X]} (hP : P ≠ 0) :
    {x : ℝ | 0 < x ∧ P.IsRoot x}.Finite :=
  P.roots.toFinset.finite_toSet.subset fun x hx => by
    simpa [Multiset.mem_toFinset, mem_roots hP] using hx.2

open Polynomial in
/-- `P(0) > 0` and a nonpositive value at `x > 0` give a positive root in `(0, x]`. -/
@[tmio T, powerlib_foundation] private theorem exists_pos_isRoot_of_nonpos {P : ℝ[X]}
    (h0 : 0 < P.eval 0) {x : ℝ} (hx : 0 < x) (hle : P.eval x ≤ 0) :
    ∃ r, 0 < r ∧ P.IsRoot r := by
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' hx.le P.continuous.continuousOn
    (show (0 : ℝ) ∈ Icc (P.eval x) (P.eval 0) from ⟨hle, h0.le⟩)
  refine ⟨r, lt_of_le_of_ne hr.1 ?_, hr0⟩
  rintro rfl
  exact h0.ne' hr0

open Polynomial in
/-- **No positive root.** A real polynomial with `P(0) > 0` has no positive root iff it is
positive on `(0, ∞)`. -/
@[tmio T, powerlib_foundation] private theorem ncard_pos_isRoot_eq_zero_iff {P : ℝ[X]}
    (h0 : 0 < P.eval 0) :
    {x : ℝ | 0 < x ∧ P.IsRoot x}.ncard = 0 ↔ ∀ x, 0 < x → 0 < P.eval x := by
  have hP : P ≠ 0 := by rintro rfl; simp at h0
  rw [Set.ncard_eq_zero (finite_pos_isRoot hP)]
  constructor
  · intro h x hx
    by_contra hn
    obtain ⟨r, hr, hr0⟩ := exists_pos_isRoot_of_nonpos h0 hx (not_lt.mp hn)
    exact (Set.eq_empty_iff_forall_notMem.mp h) r ⟨hr, hr0⟩
  · intro h
    exact Set.eq_empty_iff_forall_notMem.mpr fun r hr => (h r hr.1).ne' hr.2

open Polynomial in
/-- **Two positive roots.** A real polynomial with `P(0) > 0`, positive leading coefficient and
at most two positive roots counted with multiplicity has two distinct positive roots iff it takes
a negative value on `(0, ∞)`: a negative value gives a root on each side (intermediate value
theorem, `P → +∞`); two distinct positive roots are then simple, `P = (X − r₁)(X − r₂) Q` with `Q`
positive on `[0, ∞)`, and `P < 0` between them. -/
@[tmio T, powerlib_foundation] private theorem ncard_pos_isRoot_eq_two_iff {P : ℝ[X]}
    (h0 : 0 < P.eval 0) (hl : 0 < P.leadingCoeff) (h2 : P.roots.countP (0 < ·) ≤ 2) :
    {x : ℝ | 0 < x ∧ P.IsRoot x}.ncard = 2 ↔ ∃ x, 0 < x ∧ P.eval x < 0 := by
  classical
  have hP : P ≠ 0 := by rintro rfl; simp at h0
  have hup : {x : ℝ | 0 < x ∧ P.IsRoot x}.ncard ≤ 2 :=
    (SpecialFunctions.ncard_pos_isRoot_le_countP hP).trans h2
  have key : ∀ r₁ r₂, r₁ < r₂ → 0 < r₁ → P.IsRoot r₁ → P.IsRoot r₂ →
      P.eval ((r₁ + r₂) / 2) < 0 := by
    intro r₁ r₂ hlt hr₁ hroot₁ hroot₂
    have hr₂ : 0 < r₂ := hr₁.trans hlt
    set s : Multiset ℝ := {r₁, r₂} with hs
    have hsle : s ≤ P.roots := by
      rw [Multiset.le_iff_subset (by simp [hs, hlt.ne])]
      intro x hx
      simp only [hs, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (mem_roots hP).mpr hroot₁
      · exact (mem_roots hP).mpr hroot₂
    obtain ⟨Q, hQ⟩ := (Multiset.prod_X_sub_C_dvd_iff_le_roots hP s).mpr hsle
    have hQ0 : Q ≠ 0 := by rintro rfl; rw [mul_zero] at hQ; exact hP hQ
    have hroots : P.roots = s + Q.roots := by
      rw [hQ, roots_mul (hQ ▸ hP), roots_multiset_prod_X_sub_C]
    have hQpos : ∀ x, 0 < x → ¬ Q.IsRoot x := by
      intro x hx hr
      have hlt' : 0 < Q.roots.countP (0 < ·) :=
        Multiset.countP_pos.mpr ⟨x, (mem_roots hQ0).mpr hr, hx⟩
      have hs2 : s.countP (0 < ·) = 2 := by
        rw [Multiset.countP_eq_card.mpr fun a ha => ?_]
        · simp [hs]
        · simp only [hs, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha
          rcases ha with rfl | rfl
          · exact hr₁
          · exact hr₂
      rw [hroots, Multiset.countP_add, hs2] at h2
      omega
    have heval : ∀ y, P.eval y = (y - r₁) * (y - r₂) * Q.eval y := by
      intro y
      rw [hQ]
      simp [hs, Multiset.insert_eq_cons, eval_mul]
    have hQe : 0 < Q.eval 0 := by
      have h := heval 0
      have hrr : 0 < (0 - r₁) * (0 - r₂) := by nlinarith
      by_contra hn
      have : (0 - r₁) * (0 - r₂) * Q.eval 0 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hrr.le (not_lt.mp hn)
      linarith
    have hQm : 0 < Q.eval ((r₁ + r₂) / 2) := by
      by_contra hn
      obtain ⟨r, hr, hr0⟩ := exists_pos_isRoot_of_nonpos hQe (by linarith) (not_lt.mp hn)
      exact hQpos r hr hr0
    rw [heval]
    have ha : 0 < (r₁ + r₂) / 2 - r₁ := by linarith
    have hb : (r₁ + r₂) / 2 - r₂ < 0 := by linarith
    have hab : ((r₁ + r₂) / 2 - r₁) * ((r₁ + r₂) / 2 - r₂) < 0 := mul_neg_of_pos_of_neg ha hb
    exact mul_neg_of_neg_of_pos hab hQm
  constructor
  · intro hn
    obtain ⟨r₁, r₂, hne, hS⟩ := Set.ncard_eq_two.mp hn
    have hm₁ : r₁ ∈ {x : ℝ | 0 < x ∧ P.IsRoot x} := by rw [hS]; simp
    have hm₂ : r₂ ∈ {x : ℝ | 0 < x ∧ P.IsRoot x} := by rw [hS]; simp
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨(r₁ + r₂) / 2, by linarith [hm₁.1, hm₂.1], key r₁ r₂ hlt hm₁.1 hm₁.2 hm₂.2⟩
    · exact ⟨(r₂ + r₁) / 2, by linarith [hm₁.1, hm₂.1], key r₂ r₁ hlt hm₂.1 hm₂.2 hm₁.2⟩
  · rintro ⟨x₁, hx₁, hneg⟩
    have hdeg : 0 < P.degree := by
      by_contra h
      rw [not_lt] at h
      rw [eq_C_of_degree_le_zero h] at h0 hneg
      simp only [eval_C] at h0 hneg
      linarith
    have ht := tendsto_atTop_of_leadingCoeff_nonneg P hdeg hl.le
    obtain ⟨x₂, hx₂, hx₂'⟩ :=
      ((ht.eventually (Filter.eventually_gt_atTop 0)).and (Filter.eventually_gt_atTop x₁)).exists
    obtain ⟨r₁, hr₁, hr₁0⟩ := intermediate_value_Ioo' hx₁.le P.continuous.continuousOn
      (show (0 : ℝ) ∈ Ioo (P.eval x₁) (P.eval 0) from ⟨hneg, h0⟩)
    obtain ⟨r₂, hr₂, hr₂0⟩ := intermediate_value_Ioo hx₂'.le P.continuous.continuousOn
      (show (0 : ℝ) ∈ Ioo (P.eval x₁) (P.eval x₂) from ⟨hneg, hx₂⟩)
    have hsub : ({r₁, r₂} : Set ℝ) ⊆ {x : ℝ | 0 < x ∧ P.IsRoot x} := by
      intro r hr
      rcases hr with rfl | hr
      · exact ⟨hr₁.1, hr₁0⟩
      · rw [Set.mem_singleton_iff] at hr
        subst hr
        exact ⟨hx₁.trans hr₂.1, hr₂0⟩
    have hle := Set.ncard_le_ncard hsub (finite_pos_isRoot hP)
    rw [Set.ncard_pair (hr₁.2.trans hr₂.1).ne] at hle
    omega

namespace Params

variable (p : Params)

/-- The physical equilibria of the full model with droop: the equilibria with angle in the window
and positive droop EMF are as many as the positive roots of the droop quartic
(`ncard_equilibria_window_droop` with `T = (0, ∞)`). -/
@[tmio M, powerlib_domain] private theorem ncard_physical_eq (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0) (hM : p.M ≠ 0) (hωq : p.ωq ≠ 0)
    (hZv : p.Zv = 0) (hnq : p.nq ≠ 0) (hX : p.ω0 * p.Lg ≠ 0) (hV : p.V ≠ 0) (a : ℝ) :
    {x : State 13 | p.field x = 0 ∧ x 10 ∈ Ico a (a + 2 * π) ∧ 0 < p.emf (x 12)}.ncard =
      {E : ℝ | 0 < E ∧ p.qvDroop.quartic.IsRoot E}.ncard :=
  p.ncard_equilibria_window_droop hLf hCf hLg hKic hKiv hM hωq hZv hnq hX hV
    (T := Ioi 0) (by simp) a

/-- **Two physical equilibria with droop.** Q–V droop in its physical range (`n_q > 0`,
`ω₀L_g > 0`, `V > 0`, `E₀ + n_q Q_ref > 0`), no virtual impedance: in every window `[a, a + 2π)`
the 13-state field has exactly two equilibria with positive droop EMF iff some positive EMF `E`
puts the balance point `(u(E), w(E))` strictly inside the circle of radius `V E`,
`u(E)² + w(E)² < V² E²` (`QVDroop.u`, `QVDroop.w`: `u = E² + βE − γ`, `w = ρE + κ`), i.e. the
droop quartic takes a negative value on `(0, ∞)`; for every controller gain. The droop
counterpart of `two_equilibria_per_period`. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem two_physical_equilibria_iff (hLf : p.Lf ≠ 0)
    (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0) (hM : p.M ≠ 0)
    (hωq : p.ωq ≠ 0) (hZv : p.Zv = 0) (hnq : 0 < p.nq) (hX : 0 < p.ω0 * p.Lg) (hV : 0 < p.V)
    (hc : 0 < p.E0 + p.nq * p.Qref) (a : ℝ) :
    {x : State 13 | p.field x = 0 ∧ x 10 ∈ Ico a (a + 2 * π) ∧ 0 < p.emf (x 12)}.ncard = 2 ↔
      ∃ E, 0 < E ∧ p.qvDroop.u E ^ 2 + p.qvDroop.w E ^ 2 < (p.V * E) ^ 2 := by
  rw [p.ncard_physical_eq hLf hCf hLg hKic hKiv hM hωq hZv hnq.ne' hX.ne' hV.ne' a,
    ncard_pos_isRoot_eq_two_iff (p.qvDroop.eval_zero_quartic_pos hnq hX hc)
      (by rw [QVDroop.leadingCoeff_quartic]; exact one_pos)
      (p.qvDroop.countP_pos_roots_le_two hnq hX)]
  refine exists_congr fun E => and_congr_right fun _ => ?_
  rw [QVDroop.eval_quartic, mul_pow, sub_neg]
  rfl

/-- **No physical equilibrium with droop.** In the physical range, without virtual impedance:
no window holds an equilibrium with positive droop EMF iff `u(E)² + w(E)² > V² E²` for every
`E > 0` (the droop quartic is positive on `(0, ∞)`). Static evidence on the model, not a
connection conclusion. -/
@[tmio M, powerlib_domain] theorem no_physical_equilibrium_iff (hLf : p.Lf ≠ 0)
    (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0) (hM : p.M ≠ 0)
    (hωq : p.ωq ≠ 0) (hZv : p.Zv = 0) (hnq : 0 < p.nq) (hX : 0 < p.ω0 * p.Lg) (hV : 0 < p.V)
    (hc : 0 < p.E0 + p.nq * p.Qref) (a : ℝ) :
    {x : State 13 | p.field x = 0 ∧ x 10 ∈ Ico a (a + 2 * π) ∧ 0 < p.emf (x 12)}.ncard = 0 ↔
      ∀ E, 0 < E → (p.V * E) ^ 2 < p.qvDroop.u E ^ 2 + p.qvDroop.w E ^ 2 := by
  rw [p.ncard_physical_eq hLf hCf hLg hKic hKiv hM hωq hZv hnq.ne' hX.ne' hV.ne' a,
    ncard_pos_isRoot_eq_zero_iff (p.qvDroop.eval_zero_quartic_pos hnq hX hc)]
  refine forall_congr' fun E => imp_congr_right fun _ => ?_
  rw [QVDroop.eval_quartic, mul_pow, sub_pos]
  rfl

/-- **The fold with droop.** In the physical range, without virtual impedance: a window holds
exactly one equilibrium with positive droop EMF iff `u(E)² + w(E)² ≥ V² E²` for every `E > 0`
with equality at some `E > 0` (the balance point touches the circle without entering it: a
positive double root of the droop quartic, `QVDroop.rootMultiplicity_eq_two_of_ncard_eq_one`);
otherwise the count is `0` or `2` (`no_physical_equilibrium_iff`, `two_physical_equilibria_iff`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem fold_physical_equilibrium_iff (hLf : p.Lf ≠ 0)
    (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0) (hM : p.M ≠ 0)
    (hωq : p.ωq ≠ 0) (hZv : p.Zv = 0) (hnq : 0 < p.nq) (hX : 0 < p.ω0 * p.Lg) (hV : 0 < p.V)
    (hc : 0 < p.E0 + p.nq * p.Qref) (a : ℝ) :
    {x : State 13 | p.field x = 0 ∧ x 10 ∈ Ico a (a + 2 * π) ∧ 0 < p.emf (x 12)}.ncard = 1 ↔
      (∀ E, 0 < E → (p.V * E) ^ 2 ≤ p.qvDroop.u E ^ 2 + p.qvDroop.w E ^ 2) ∧
        ∃ E, 0 < E ∧ p.qvDroop.u E ^ 2 + p.qvDroop.w E ^ 2 = (p.V * E) ^ 2 := by
  have h2 := p.two_physical_equilibria_iff hLf hCf hLg hKic hKiv hM hωq hZv hnq hX hV hc a
  have h0 := p.no_physical_equilibrium_iff hLf hCf hLg hKic hKiv hM hωq hZv hnq hX hV hc a
  have hle : {x : State 13 | p.field x = 0 ∧ x 10 ∈ Ico a (a + 2 * π) ∧
      0 < p.emf (x 12)}.ncard ≤ 2 := by
    rw [p.ncard_physical_eq hLf hCf hLg hKic hKiv hM hωq hZv hnq.ne' hX.ne' hV.ne' a]
    exact (SpecialFunctions.ncard_pos_isRoot_le_countP p.qvDroop.quartic_ne_zero).trans
      (p.qvDroop.countP_pos_roots_le_two hnq hX)
  constructor
  · intro h1
    have hn2 : ¬ ∃ E, 0 < E ∧ p.qvDroop.u E ^ 2 + p.qvDroop.w E ^ 2 < (p.V * E) ^ 2 :=
      fun h => by have := h2.mpr h; omega
    have hn0 : ¬ ∀ E, 0 < E → (p.V * E) ^ 2 < p.qvDroop.u E ^ 2 + p.qvDroop.w E ^ 2 :=
      fun h => by have := h0.mpr h; omega
    push Not at hn2 hn0
    obtain ⟨E, hE, hEle⟩ := hn0
    exact ⟨hn2, E, hE, le_antisymm hEle (hn2 E hE)⟩
  · rintro ⟨hge, E, hE, hEq⟩
    have hn2 : ¬ _ = 2 := fun h => by
      obtain ⟨E', hE', hlt⟩ := h2.mp h
      linarith [hge E' hE']
    have hn0 : ¬ _ = 0 := fun h => by
      have := h0.mp h E hE
      linarith
    omega

end Params

end powerlib.GFM.FullModel
