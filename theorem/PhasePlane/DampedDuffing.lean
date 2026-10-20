import theorem.PhasePlane.Duffing
import theorem.Dynamics.LaSalle.Basin

/-! # Damped Duffing: every solution converges to the equilibrium set (LaSalle)

The "bounded orbits converge to the set of equilibria" statement of the phase-plane note for the
damped double well (all orbits are bounded there since the energy is coercive).

Model boundary.
* The Duffing field `PhasePlane.Duffing.field δ` (`ẋ = y`, `ẏ = x − x³ − δy`, state
  `(x, y) ∈ State 2`) with damping `δ > 0`, continuous time, no input.
* A canonical textbook system, not a power-system model: no model family; foundation results.

Source: work-sync theory/T-nonlinear-phase-plane.md §1.7 (damped systems: trajectories shrink to
the equilibria; stretch item "有界轨道收敛到平衡点集").

Results.
* `tendsto_equilibria`: every forward solution converges to the equilibrium set
  `{(0, 0), (1, 0), (−1, 0)}` (`equilibria`, in the sense of `𝓝ˢ`). Proof: LaSalle's invariance
  principle in the `C¹` form of `theorem/Dynamics/LaSalle/Basin.lean`
  (`lasalle_invariance_principle_of_contDiff`) on the compact, positively invariant energy
  sublevel set through the initial state (`sublevel_positivelyInvariant`); on
  `{Ė = 0} = {y = 0}` an invariant set must have `ẏ = −(x³ − x) = 0`, i.e. consist of equilibria.
-/

noncomputable section
namespace powerlib.PhasePlane.Duffing
open Set Filter Topology
open powerlib.Dynamics (State)
open powerlib.PhasePlane

/-- The equilibrium set `{(0, 0), (1, 0), (−1, 0)}`. -/
def equilibria : Set (State 2) := {mk 0 0, mk 1 0, mk (-1) 0}

@[powerlib_foundation] theorem mem_equilibria_iff (δ : ℝ) (y : State 2) :
    y ∈ equilibria ↔ field δ y = 0 := by
  rw [field_eq_zero_iff]
  simp only [equilibria, mem_insert_iff, mem_singleton_iff, ext_iff', mk_apply_zero,
    mk_apply_one]
  tauto

@[powerlib_foundation] theorem energy_contDiff : ContDiff ℝ 1 energy := by
  have h : energy = fun y : State 2 => 1 * y 1 ^ 2 / 2 + potential (y 0) := rfl
  rw [h]
  have h0 : ContDiff ℝ 1 (fun y : State 2 => y 0) := Dynamics.contDiff_coord 0
  have h1 : ContDiff ℝ 1 (fun y : State 2 => y 1) := Dynamics.contDiff_coord 1
  unfold potential
  fun_prop

/-- Energy sublevel sets are positively invariant for `δ ≥ 0`. -/
@[powerlib_foundation] theorem sublevel_positivelyInvariant {δ : ℝ} (hδ : 0 ≤ δ) (c : ℝ) :
    IsPositivelyInvariant {y : State 2 | energy y ≤ c} (field δ) := by
  intro t₀ t₁ φ hφ h0 t ht
  have hanti := Conservative.energy_antitone one_ne_zero hδ hasDerivAt_potential hφ
  have := hanti ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  exact le_trans this h0

/-- Damped Duffing: every forward solution converges to the equilibrium set. -/
@[powerlib_foundation] theorem tendsto_equilibria {δ : ℝ} (hδ : 0 < δ) {φ : ℝ → State 2}
    (hφ : IsIntegralCurveOn φ (fun _ y => field δ y) (Ici 0)) :
    Tendsto φ atTop (𝓝ˢ equilibria) := by
  refine Dynamics.LaSalle.lasalle_invariance_principle_of_contDiff (V := energy)
    (Ω := {y | energy y ≤ energy (φ 0)}) (energy_sublevel_compact _)
    (sublevel_positivelyInvariant hδ.le _) (field_contDiff δ) energy_contDiff
    (fun x _ => energy_lie_nonpos hδ.le x) hφ (by simp) ?_
  intro N hN hNinv x hx
  -- on `N` the Lie derivative vanishes, so `y = 0` there
  have hzero : ∀ z ∈ N, z 1 = 0 := by
    intro z hz
    have h := (hN hz).2
    rw [energy, field, Conservative.energy_lie one_ne_zero hasDerivAt_potential] at h
    have : δ * z 1 ^ 2 = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hδ.ne'
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  -- a local solution from `x` stays in `N`, so its `y`-coordinate vanishes identically
  obtain ⟨T, ψ, hT, hψ0, hψ⟩ :=
    ((field_contDiff δ (k := 1)).contDiffAt (x := x)).exists_isIntegralCurveOn_Icc
  have hstay : ∀ t ∈ Icc 0 T, ψ t ∈ N := hNinv 0 T ψ hψ (hψ0 ▸ hx)
  have hmem0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hchain : HasDerivWithinAt (fun t => ψ t 1) (field δ (ψ 0) 1) (Icc 0 T) 0 :=
    (Dynamics.coord 1).hasFDerivAt.comp_hasDerivWithinAt 0 (hψ 0 hmem0)
  have hconst : HasDerivWithinAt (fun t => ψ t 1) 0 (Icc 0 T) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) _ (0 : ℝ)).congr (fun s hs => hzero _ (hstay s hs))
      (hzero _ (hstay 0 hmem0))
  have hder : field δ (ψ 0) 1 = 0 := (uniqueDiffOn_Icc hT 0 hmem0).eq_deriv _ hchain hconst
  rw [hψ0] at hder
  have hx1 : x 1 = 0 := hzero x hx
  rw [mem_equilibria_iff δ, field, Conservative.field_eq_zero_iff one_ne_zero]
  refine ⟨hx1, ?_⟩
  simp only [field, Conservative.field_apply_one, hx1, mul_zero, zero_sub, div_one,
    neg_eq_zero] at hder
  exact hder

end powerlib.PhasePlane.Duffing
