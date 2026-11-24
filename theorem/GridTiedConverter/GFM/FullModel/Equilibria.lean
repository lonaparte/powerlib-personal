import theorem.GridTiedConverter.GFM.FullModel.Basic
import theorem.GridTiedConverter.GFM.Equilibria

/-! # The 13-state grid-forming converter: equilibrium count per period

Model boundary.
* The 13-state model of `theorem/GridTiedConverter/GFM/FullModel/Basic.lean` (state order
  `(i, v_c, i_g, ξ, ζ, δ, Δω, Q_f)` in dq components, `x 10 = δ`, system frame for the plant,
  controller frame for the integrators, currents out of the converter positive, export-positive
  per-unit power), continuous time, autonomous, no input.
* Range of the statements: no Q–V droop (`n_q = 0`, internal EMF `E = E₀`) and no virtual impedance
  (`Z_v = 0`), nondegenerate fast block (`L_f, C_f, L_g, K_ic, K_iv ≠ 0`, `Z_g ≠ 0`), `M, ω_q ≠ 0`,
  `E₀ V > 0`; every other gain is free. With droop the equilibrium count is not established here.
* Level: the equilibrium set of the field with angle in a period window `[a, a + 2π)` and its
  cardinality; no stability statement (the saddle branch is unstable by
  `theorem/GridTiedConverter/GFM/FullModel/Saddle.lean`).

Scaffold of the reading of the reduced model:
`theorem/GridTiedConverter/GFM/FullModel/FullModelSwing.agda`.

Source: GFM counterpart study, full-order model note (t5 (b): "n_q = 0: two angles iff
|P_ref − c₀| ≤ A") and equilibria note (t6 (a): "count per window: 2 if |P_ref − c₀| < A, 1 double
zero if =, 0 if >"; t6 (c): the full-order equilibria with `(c₀, A, α)` from `Z_g` only), checked
numerically there; the counting laws of the reduced model
`theorem/GridTiedConverter/GFM/Equilibria.lean`.

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

end Params

end powerlib.GFM.FullModel
