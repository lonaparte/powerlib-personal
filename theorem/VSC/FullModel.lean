import theorem.VSC.Reduction
import theorem.Dynamics.LyapunovDefs

/-! # The 10-state GFL-VSC model, its quasi-steady set, and its equilibria

Domain module (`vsc-stochastic-stability`, rigid-DC baseline "M1").

Model boundary.
* State `x : State 10`, coordinates in this order:
  `x 0 = i_d`, `x 1 = i_q` (converter current, system dq frame),
  `x 2 = v_cd`, `x 3 = v_cq` (filter-capacitor voltage, system frame),
  `x 4 = i_gd`, `x 5 = i_gq` (line current, system frame),
  `x 6 = ξ_d`, `x 7 = ξ_q` (current-loop PI integrators, controller frame),
  `x 8 = η` (PLL integrator), `x 9 = θ_e` (PLL angle error).
* Frames: system dq aligned with the grid EMF `(V_g, 0)`; controller frame obtained with the
  Park matrix `T(θ_e)` (`conventions.md` §D4; `decisions.md` §D1.2), `θ_e = θ̂_g − θ_g`
  (§D1.1, text convention).
* Direction: converter current OUT-positive (from the bridge into the filter), as in the
  project frame `decisions.md` §D1.6 (opposite to the workspace default `conventions.md` §D1).
* Continuous time, autonomous (no grid-frequency drift: `δω_g ≡ 0`), no noise.
  Plant: `L_f i̇ = u − v_c − R_f i + ω_g L_f J i`, `C_f v̇_c = i − i_g − ω_g C_f J v_c`,
  `L_g i̇_g = v_c − (V_g, 0) − R_g i_g − ω_g L_g J i_g` written component-wise as in
  `reduction-pipeline.md` §1. Current loop (controller frame):
  `ξ̇ = i* − i^c`, `u^c = K_p^cc (i* − i^c) + K_i^cc ξ + ω_g L_f J i^c + v_c^c`, `u = T(−θ_e) u^c`.
  The decoupling term uses the nominal `ω_g` (as in the project code `models.py::full_dynamics`);
  the note's `ω_p` coincides with `ω_g` at every equilibrium.
  PLL (SRF, `decisions.md` §D1.3): `η̇ = v_cq^c`, `θ̇_e = K_p v_cq^c + K_i η`.
* Included: rigid (ideal) DC source, frozen references `i_d*, i_q*`. Excluded: DC-link dynamics
  (see `theorem/VSC/DCLink.lean`), outer P/Q loops, saturation / limiters, modulation limits,
  PWM, sampling delay, measurement filters, harmonics and unbalance.
* Level: algebraic quasi-steady set and equilibrium set of the full 10-state field. No claim is
  made here about time-scale separation or about how well the reduced model approximates
  trajectories (the project notes show the LC/line step is averaging, not a slow manifold).

Main results.
* `fast_eq_zero_iff` : the eight fast rows (current, capacitor, line, current-loop integrators)
  vanish iff the state lies on the explicit quasi-steady set `qssState θ_e η`
  (`i = T(−θ_e) i*`, capacitor and corrected line solution, `ξ = R_f i*/K_i^cc`).
* `field10_eq_zero_iff` (A3, `validity-boundary.md` §2 D1 / §8(a)): for `K_i ≠ 0`,
  `x` is an equilibrium of the 10-state field iff `x = qssState θ* 0` with `h(θ*) = 0`.
* `reducedField` is *defined* as the slow rows `(θ̇_e, η̇)` of the 10-state field evaluated on the
  quasi-steady set; `reducedField_apply` shows it equals `(K_p h(θ) + K_i η, h(θ))` with the
  closed-form `h` of `theorem/VSC/Reduction.lean`.

Nondegeneracy hypotheses: `L_f, C_f, L_g ≠ 0`, `ω_g C_f ≠ 0`, `Δ ≠ 0`, `K_i^cc ≠ 0`
(and `K_i ≠ 0` for the equilibrium statement).

Sources: work-sync `projects/vsc-stochastic-stability/notes/concepts/reduction-pipeline.md`
§1–§5; `validity-boundary.md` §2 (D1: "10D equilibrium equations ⇔ `h(θ*) = 0`") and §8(a);
`equilibria-and-bifurcation.md` §1.
-/

noncomputable section
namespace powerlib.VSC
open Real Matrix
open powerlib.Dynamics (State)

/-- Ten-state vectors are equal iff all ten coordinates agree. -/
@[powerlib_foundation] theorem state10_ext_iff {x y : State 10} : x = y ↔ ∀ i, x i = y i := by
  constructor
  · rintro rfl i; rfl
  · intro h; ext i; exact h i

/-! ### The 10-state vector field -/

/-- Controller-frame converter current, d-axis. -/
def icD (x : State 10) : ℝ := parkD (x 9) (x 0) (x 1)
/-- Controller-frame converter current, q-axis. -/
def icQ (x : State 10) : ℝ := parkQ (x 9) (x 0) (x 1)
/-- Controller-frame capacitor voltage, d-axis. -/
def vccD (x : State 10) : ℝ := parkD (x 9) (x 2) (x 3)
/-- Controller-frame capacitor voltage, q-axis (the PLL input `v_cq^c`). -/
def vccQ (x : State 10) : ℝ := parkQ (x 9) (x 2) (x 3)

namespace Params

variable (p : Params)

/-- Current-loop output, controller frame, d-axis. -/
def ucD (x : State 10) : ℝ :=
  p.Kpcc * (p.idRef - icD x) + p.Kicc * x 6 - p.ωg * p.Lf * icQ x + vccD x
/-- Current-loop output, controller frame, q-axis. -/
def ucQ (x : State 10) : ℝ :=
  p.Kpcc * (p.iqRef - icQ x) + p.Kicc * x 7 + p.ωg * p.Lf * icD x + vccQ x

/-- Bridge voltage in the system frame, `u = T(−θ_e) u^c`, d-axis. -/
def uD (x : State 10) : ℝ := iparkD (x 9) (p.ucD x) (p.ucQ x)
/-- Bridge voltage in the system frame, `u = T(−θ_e) u^c`, q-axis. -/
def uQ (x : State 10) : ℝ := iparkQ (x 9) (p.ucD x) (p.ucQ x)

/-- The complete 10-state field (`reduction-pipeline.md` §1, `δω_g = 0`). -/
def field10 (x : State 10) : State 10 :=
  WithLp.toLp 2 ![
    (p.uD x - x 2 - p.Rf * x 0 + p.ωg * p.Lf * x 1) / p.Lf,
    (p.uQ x - x 3 - p.Rf * x 1 - p.ωg * p.Lf * x 0) / p.Lf,
    (x 0 - x 4 + p.ωg * p.Cf * x 3) / p.Cf,
    (x 1 - x 5 - p.ωg * p.Cf * x 2) / p.Cf,
    (x 2 - p.Vg - p.Rg * x 4 + p.ωg * p.Lg * x 5) / p.Lg,
    (x 3 - p.Rg * x 5 - p.ωg * p.Lg * x 4) / p.Lg,
    p.idRef - icD x,
    p.iqRef - icQ x,
    vccQ x,
    p.Kp * vccQ x + p.Ki * x 8]

@[simp, powerlib_foundation] theorem field10_0 (x : State 10) :
    p.field10 x 0 = (p.uD x - x 2 - p.Rf * x 0 + p.ωg * p.Lf * x 1) / p.Lf := rfl
@[simp, powerlib_foundation] theorem field10_1 (x : State 10) :
    p.field10 x 1 = (p.uQ x - x 3 - p.Rf * x 1 - p.ωg * p.Lf * x 0) / p.Lf := rfl
@[simp, powerlib_foundation] theorem field10_2 (x : State 10) :
    p.field10 x 2 = (x 0 - x 4 + p.ωg * p.Cf * x 3) / p.Cf := rfl
@[simp, powerlib_foundation] theorem field10_3 (x : State 10) :
    p.field10 x 3 = (x 1 - x 5 - p.ωg * p.Cf * x 2) / p.Cf := rfl
@[simp, powerlib_foundation] theorem field10_4 (x : State 10) :
    p.field10 x 4 = (x 2 - p.Vg - p.Rg * x 4 + p.ωg * p.Lg * x 5) / p.Lg := rfl
@[simp, powerlib_foundation] theorem field10_5 (x : State 10) :
    p.field10 x 5 = (x 3 - p.Rg * x 5 - p.ωg * p.Lg * x 4) / p.Lg := rfl
@[simp, powerlib_foundation] theorem field10_6 (x : State 10) :
    p.field10 x 6 = p.idRef - icD x := rfl
@[simp, powerlib_foundation] theorem field10_7 (x : State 10) :
    p.field10 x 7 = p.iqRef - icQ x := rfl
@[simp, powerlib_foundation] theorem field10_8 (x : State 10) :
    p.field10 x 8 = vccQ x := rfl
@[simp, powerlib_foundation] theorem field10_9 (x : State 10) :
    p.field10 x 9 = p.Kp * vccQ x + p.Ki * x 8 := rfl

/-! ### The quasi-steady set -/

/-- The explicit quasi-steady state with PLL coordinates `(θ, η)`:
`i = T(−θ) i*`, `v_c`, `i_g` from the capacitor and corrected line equations, `ξ = R_f i*/K_i^cc`. -/
def qssState (θ η : ℝ) : State 10 :=
  WithLp.toLp 2 ![p.iD θ, p.iQ θ, p.vcD θ p.Vg 0, p.vcQ θ p.Vg 0, p.igD θ p.Vg 0,
    p.igQ θ p.Vg 0, p.Rf * p.idRef / p.Kicc, p.Rf * p.iqRef / p.Kicc, η, θ]

@[simp, powerlib_foundation] theorem qssState_8 (θ η : ℝ) : p.qssState θ η 8 = η := rfl
@[simp, powerlib_foundation] theorem qssState_9 (θ η : ℝ) : p.qssState θ η 9 = θ := rfl

/-- On the quasi-steady set the PLL input is exactly `h(θ)`. -/
@[powerlib_foundation] theorem vccQ_qssState (θ η : ℝ) : vccQ (p.qssState θ η) = p.h θ := rfl

/-- The fast rows `0 … 7` (current, capacitor, line, current-loop integrators). -/
def FastAtRest (x : State 10) : Prop := ∀ i : Fin 10, i.val < 8 → p.field10 x i = 0

/-- `reduction-pipeline.md` §2–§4 as an exact algebraic statement: the eight fast rows of the
10-state field vanish iff the state is on the explicit quasi-steady set. -/
@[powerlib_foundation] theorem fastAtRest_iff (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0)
    (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hKicc : p.Kicc ≠ 0) (x : State 10) :
    p.FastAtRest x ↔ x = p.qssState (x 9) (x 8) := by
  set θ := x 9 with hθ
  have hwC' : p.ωg * p.Cf = p.wC := rfl
  constructor
  · intro hx
    have f0 : (p.uD x - x 2 - p.Rf * x 0 + p.ωg * p.Lf * x 1) / p.Lf = 0 := hx 0 (by decide)
    have f1 : (p.uQ x - x 3 - p.Rf * x 1 - p.ωg * p.Lf * x 0) / p.Lf = 0 := hx 1 (by decide)
    have f2 : (x 0 - x 4 + p.ωg * p.Cf * x 3) / p.Cf = 0 := hx 2 (by decide)
    have f3 : (x 1 - x 5 - p.ωg * p.Cf * x 2) / p.Cf = 0 := hx 3 (by decide)
    have f4 : (x 2 - p.Vg - p.Rg * x 4 + p.ωg * p.Lg * x 5) / p.Lg = 0 := hx 4 (by decide)
    have f5 : (x 3 - p.Rg * x 5 - p.ωg * p.Lg * x 4) / p.Lg = 0 := hx 5 (by decide)
    have f6 : p.idRef - icD x = 0 := hx 6 (by decide)
    have f7 : p.iqRef - icQ x = 0 := hx 7 (by decide)
    rw [div_eq_zero_iff, or_iff_left hLf] at f0 f1
    rw [div_eq_zero_iff, or_iff_left hCf] at f2 f3
    rw [div_eq_zero_iff, or_iff_left hLg] at f4 f5
    rw [hwC'] at f2 f3
    obtain ⟨hi0, hi1⟩ := (p.current_qss_iff θ (x 0) (x 1)).mp ⟨f6, f7⟩
    have f5' : x 3 - 0 - p.Rg * x 5 - p.ωg * p.Lg * x 4 = 0 := by linarith
    obtain ⟨hM, hv2, hv3⟩ :=
      (p.lc_line_qss_iff hwC p.Vg 0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)).mp ⟨f2, f3, f4, f5'⟩
    obtain ⟨hg4, hg5⟩ := (p.lineMatrix_mulVec_iff hΔ (x 0) (x 1) p.Vg 0 (x 4) (x 5)).mp hM
    -- the current-loop integrators from the inductor rows
    have hic0 : icD x = p.idRef := by linarith
    have hic1 : icQ x = p.iqRef := by linarith
    have key_d : p.Kicc * x 6 = p.Rf * p.idRef := by
      have hu : parkD θ (p.uD x) (p.uQ x) = p.ucD x := by simp [uD, uQ, hθ]
      have : parkD θ (p.uD x - x 2 - p.Rf * x 0 + p.ωg * p.Lf * x 1)
          (p.uQ x - x 3 - p.Rf * x 1 - p.ωg * p.Lf * x 0) =
          p.ucD x - vccD x - p.Rf * icD x + p.ωg * p.Lf * icQ x := by
        rw [← hu]; simp only [parkD, vccD, icD, icQ, parkQ]; ring
      rw [f0, f1] at this
      simp only [parkD, mul_zero, add_zero] at this
      simp only [ucD] at this
      rw [hic0, hic1] at this
      linarith
    have key_q : p.Kicc * x 7 = p.Rf * p.iqRef := by
      have hu : parkQ θ (p.uD x) (p.uQ x) = p.ucQ x := by simp [uD, uQ, hθ]
      have : parkQ θ (p.uD x - x 2 - p.Rf * x 0 + p.ωg * p.Lf * x 1)
          (p.uQ x - x 3 - p.Rf * x 1 - p.ωg * p.Lf * x 0) =
          p.ucQ x - vccQ x - p.Rf * icQ x - p.ωg * p.Lf * icD x := by
        rw [← hu]; simp only [parkD, vccQ, icD, icQ, parkQ]; ring
      rw [f0, f1] at this
      simp only [parkQ, mul_zero, add_zero] at this
      simp only [ucQ] at this
      rw [hic0, hic1] at this
      linarith
    rw [state10_ext_iff]
    intro i
    fin_cases i
    · exact hi0
    · exact hi1
    · show x 2 = p.vcD θ p.Vg 0
      rw [hv2, vcD, igQ, ← hi0, ← hi1, ← hg5]
    · show x 3 = p.vcQ θ p.Vg 0
      rw [hv3, vcQ, igD, ← hi0, ← hi1, ← hg4]
    · show x 4 = p.igD θ p.Vg 0
      rw [igD, ← hi0, ← hi1]; exact hg4
    · show x 5 = p.igQ θ p.Vg 0
      rw [igQ, ← hi0, ← hi1]; exact hg5
    · show x 6 = p.Rf * p.idRef / p.Kicc
      field_simp; linarith
    · show x 7 = p.Rf * p.iqRef / p.Kicc
      field_simp; linarith
    · rfl
    · rfl
  · intro hx
    -- evaluate everything on the explicit quasi-steady state
    set q := p.qssState θ (x 8)
    rw [hx]
    have q0 : q 0 = p.iD θ := rfl
    have q1 : q 1 = p.iQ θ := rfl
    have q2 : q 2 = p.vcD θ p.Vg 0 := rfl
    have q3 : q 3 = p.vcQ θ p.Vg 0 := rfl
    have q4 : q 4 = p.igD θ p.Vg 0 := rfl
    have q5 : q 5 = p.igQ θ p.Vg 0 := rfl
    have q6 : q 6 = p.Rf * p.idRef / p.Kicc := rfl
    have q7 : q 7 = p.Rf * p.iqRef / p.Kicc := rfl
    have q9 : q 9 = θ := rfl
    have hic0 : icD q = p.idRef := by simp [icD, q0, q1, q9, iD, iQ]
    have hic1 : icQ q = p.iqRef := by simp [icQ, q0, q1, q9, iD, iQ]
    have hlin := (p.lc_line_qss_iff hwC p.Vg 0 (p.iD θ) (p.iQ θ) (p.vcD θ p.Vg 0)
      (p.vcQ θ p.Vg 0) (p.igD θ p.Vg 0) (p.igQ θ p.Vg 0)).mpr
      ⟨(p.lineMatrix_mulVec_iff hΔ _ _ _ _ _ _).mpr ⟨rfl, rfl⟩, rfl, rfl⟩
    obtain ⟨l2, l3, l4, l5⟩ := hlin
    have hK6 : p.Kicc * q 6 = p.Rf * p.idRef := by rw [q6]; field_simp
    have hK7 : p.Kicc * q 7 = p.Rf * p.iqRef := by rw [q7]; field_simp
    -- controller-frame inductor balance
    have huc : p.ucD q = vccD q + p.Rf * icD q - p.ωg * p.Lf * icQ q := by
      simp only [ucD]; rw [hK6, hic0]; ring
    have huq : p.ucQ q = vccQ q + p.Rf * icQ q + p.ωg * p.Lf * icD q := by
      simp only [ucQ]; rw [hK7, hic1]; ring
    have hud : p.uD q = q 2 + p.Rf * q 0 - p.ωg * p.Lf * q 1 := by
      simp only [uD, huc, huq, vccD, vccQ, icD, icQ, iparkD, parkD, parkQ]
      linear_combination (q 2 + p.Rf * q 0 - p.ωg * p.Lf * q 1) * sin_sq_add_cos_sq (q 9)
    have huq' : p.uQ q = q 3 + p.Rf * q 1 + p.ωg * p.Lf * q 0 := by
      simp only [uQ, huc, huq, vccD, vccQ, icD, icQ, iparkQ, parkD, parkQ]
      linear_combination (q 3 + p.Rf * q 1 + p.ωg * p.Lf * q 0) * sin_sq_add_cos_sq (q 9)
    intro i hi
    fin_cases i
    · show (p.uD q - q 2 - p.Rf * q 0 + p.ωg * p.Lf * q 1) / p.Lf = 0
      rw [hud, div_eq_zero_iff]; left; ring
    · show (p.uQ q - q 3 - p.Rf * q 1 - p.ωg * p.Lf * q 0) / p.Lf = 0
      rw [huq', div_eq_zero_iff]; left; ring
    · show (q 0 - q 4 + p.ωg * p.Cf * q 3) / p.Cf = 0
      rw [q0, q3, q4, hwC', l2, zero_div]
    · show (q 1 - q 5 - p.ωg * p.Cf * q 2) / p.Cf = 0
      rw [q1, q2, q5, hwC', l3, zero_div]
    · show (q 2 - p.Vg - p.Rg * q 4 + p.ωg * p.Lg * q 5) / p.Lg = 0
      rw [q2, q4, q5, l4, zero_div]
    · show (q 3 - p.Rg * q 5 - p.ωg * p.Lg * q 4) / p.Lg = 0
      rw [q3, q4, q5, div_eq_zero_iff]; left; linarith
    · show p.idRef - icD q = 0
      rw [hic0, sub_self]
    · show p.iqRef - icQ q = 0
      rw [hic1, sub_self]
    all_goals simp at hi

/-! ### Equilibria of the 10-state field (A3) -/

/-- `validity-boundary.md` §2 (D1) / §8(a): the equilibria of the complete 10-state field are
exactly the quasi-steady states `qssState θ* 0` with `h(θ*) = 0`. This is an exact statement;
it does not depend on any time-scale separation. -/
@[powerlib_domain] theorem field10_eq_zero_iff (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hKicc : p.Kicc ≠ 0) (hKi : p.Ki ≠ 0)
    (x : State 10) :
    p.field10 x = 0 ↔ ∃ θ, p.h θ = 0 ∧ x = p.qssState θ 0 := by
  constructor
  · intro hx
    have hfast : p.FastAtRest x := fun i _ => by rw [hx]; rfl
    have hq := (p.fastAtRest_iff hLf hCf hLg hwC hΔ hKicc x).mp hfast
    have h8 : vccQ x = 0 := by
      have := congrArg (fun y : State 10 => y 8) hx; simpa using this
    have h9 : p.Kp * vccQ x + p.Ki * x 8 = 0 := by
      have := congrArg (fun y : State 10 => y 9) hx; simpa using this
    rw [h8, mul_zero, zero_add, mul_eq_zero, or_iff_right hKi] at h9
    refine ⟨x 9, ?_, ?_⟩
    · rw [← p.vccQ_qssState (x 9) (x 8), ← hq]; exact h8
    · rw [hq, h9]; congr 1
  · rintro ⟨θ, hθ, rfl⟩
    have hfast := (p.fastAtRest_iff hLf hCf hLg hwC hΔ hKicc (p.qssState θ 0)).mpr rfl
    rw [state10_ext_iff]
    intro i
    fin_cases i
    iterate 8 · exact hfast _ (by decide)
    · show vccQ (p.qssState θ 0) = 0
      rw [p.vccQ_qssState]; exact hθ
    · show p.Kp * vccQ (p.qssState θ 0) + p.Ki * p.qssState θ 0 8 = 0
      rw [p.vccQ_qssState, hθ, p.qssState_8]; ring

/-- The equilibrium set of the 10-state field as an image of the zero set of `h`. -/
@[powerlib_domain] theorem field10_equilibria_eq (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (hwC : p.wC ≠ 0) (hΔ : p.Δ ≠ 0) (hKicc : p.Kicc ≠ 0) (hKi : p.Ki ≠ 0) :
    {x : State 10 | p.field10 x = 0} = (fun θ => p.qssState θ 0) '' {θ | p.h θ = 0} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  rw [p.field10_eq_zero_iff hLf hCf hLg hwC hΔ hKicc hKi]
  constructor
  · rintro ⟨θ, hθ, rfl⟩; exact ⟨θ, hθ, rfl⟩
  · rintro ⟨θ, hθ, rfl⟩; exact ⟨θ, hθ, rfl⟩

/-! ### The reduced field, derived from the 10-state field -/

/-- The reduced `(θ_e, η)` field, *defined* as the slow rows `(θ̇_e, η̇)` of the 10-state field
evaluated on the quasi-steady set (`reduction-pipeline.md` §5). Coordinates `y 0 = θ_e`,
`y 1 = η`. -/
def reducedField (y : State 2) : State 2 :=
  WithLp.toLp 2 ![p.field10 (p.qssState (y 0) (y 1)) 9, p.field10 (p.qssState (y 0) (y 1)) 8]

/-- The reduced field is `θ̇_e = K_p h(θ_e) + K_i η`, `η̇ = h(θ_e)`. -/
@[powerlib_foundation] theorem reducedField_apply (y : State 2) :
    p.reducedField y = WithLp.toLp 2 ![p.Kp * p.h (y 0) + p.Ki * y 1, p.h (y 0)] := rfl

end Params

end powerlib.VSC
