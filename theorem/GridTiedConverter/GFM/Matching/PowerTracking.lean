import theorem.GridTiedConverter.GFM.Matching.LaSalle
import theorem.Linear.Transfer

/-! # Matching control on a stiff grid with power set-point tracking

The PQ set-point tracking variant of the stiff-grid matching closed loop: the modulation amplitude
is fixed at the set-point value `μ*` and the synchronizing term of the DC current control is
shifted to the target angle, `−η ∇S(θ_dq − θ*_dq)` (source eq. (28)). This module formalizes the
closed loop, its equilibria and energy balance, the set-point, the local stability conclusions,
and (private, trajectory level) the LaSalle convergence the source claims for it.

Model boundary.
* Exactly the converter, filter, grid and frame of
  `theorem.GridTiedConverter.GFM.Matching.StiffGrid` (averaged converter, DC capacitor `C_dc`
  and conductance `G_dc`, L filter `L_s`, `R_s`, stiff grid `v₀`, `ω₀ = η u*_dc`, grid `dq`
  frame, `i_s` from the grid into the converter; no PWM, delay, PLL, current or modulation
  limits), whose parameters are the field `base` with `base.μ = μ*`; a second parameter, the
  target angle error `θ*_dq = θ* − θ_g` (`θs`, constant in the grid frame). State
  `(θ_dq, u_dc, i_d, i_q) ∈ ℝ⁴`, continuous time, autonomous:
  `θ_dq' = η u_dc − ω₀`, `C_dc u_dc' = −G_dc u_dc + i_dc + μ* (−sin θ_dq, cos θ_dq)ᵀ i_dq`,
  `L_s i_dq' = −Z_s i_dq + v₀ e₂ − μ* (−sin θ_dq, cos θ_dq) u_dc` with
  `i_dc = −K_p ũ_dc + G_dc u*_dc + î_x(θ_dq) − κ sin(θ_dq − θ*_dq)` (`Model.field`; the internal
  model `î_x` at the actual angle, as in (18), `κ = η k`).
* Operating point `(θ*_dq, u*_dc, î_dq(θ*_dq))` (`Model.point`). Parameter ranges as stated in each
  result (`C_dc, L_s, R_s > 0` throughout the stability results).
* Excluded: the time-scale-separated pendulum, current tracking of `i*_s` by inner loops, and any
  saturation of `μ*`.

Source: C. Arghir, F. Dörfler, "The electronic realization of synchronous machines: model
matching, angle tracking, and energy shaping techniques", IEEE Trans. Power Electron. 35(4)
(2020) 4398–4410, author version (ETH Research Collection, `bare_jrnl.pdf`, text layer read):
§III-E "PQ set-point tracking", eqs. (25)–(29) — `P_g = −i_sᵀ v_g`, `Q_g = −i_sᵀ J v_g` (25),
`i*_s = [P*_g Q*_g; −Q*_g P*_g] v_g/‖v_g‖` (26), `μ* = ‖v_g − Z_s i*_s‖/u*_dc` (27a),
`μ* u*_dc (−sin θ*, cos θ*) = v_g − Z_s i*_s` (27b), the control (28) with `μ = μ*`,
`η ∇S(θ_dq − θ*_dq) = (μ* v₀ ω₀ L_s/‖Z_s‖²) sin(θ − θ*)` (29), and the statement that the
appendix stability analysis "pertains" with `S(θ_dq)` replaced by `S(θ_dq − θ*_dq)` in (22);
work-sync `theory/papers/@arghir2020matching.md`, `theory/T-gfm-control.md` §1.6.

Results.
* Static: `field_eq_base` (the loop is the stiff-grid loop plus the shift of the synchronizing
  term), `energy_eq_base`, `fderiv_energy`, `energy_lie` (**the shift leaves the dissipation
  unchanged**: the Lie derivative of the shifted energy
  `C_dc ũ²/2 + k(1 − cos(θ_dq − θ*_dq)) + L_s‖ĩ‖²/2` along the tracking loop equals the stiff-grid
  one, `MatchingStiffGrid.energy_lie`), `energy_lie_le` (`dH/dt ≤ −margin ũ²`, the same margin),
  `field_eq_zero_of_kappa_mul_sin_eq_zero`, `field_point`, `field_add_two_pi`, `energy_point`.
* Set-point: `iHat_eq_of_setpoint` (with (27b) the equilibrium current is the target `i*`),
  `setpoint_power_printed` (**correction**: the current (26), as it reads in the text layer of the
  author version, delivers
  `(P_g, Q_g) = −‖v_g‖ (P*_g, Q*_g)` under (25)), `setpoint_power` (the current
  `−[P* Q*; −Q* P*] v_g/‖v_g‖²` delivers `(P*_g, Q*_g)`).
* Linearization: `hasFDerivAt_field_point`, `jac_eq_conj` (the Jacobian at `θ*_dq` is the
  stiff-grid Jacobian at `0` in current coordinates rotated by `θ*_dq`), `jac_isHurwitz` (through
  `Linear.isHurwitz_conj` and `MatchingStiffGrid.jac_isHurwitz`).
* Trajectory level (private implementation evidence, Rules §3a): on the cylinder of
  `MatchingStiffGrid.cyl` (`fderiv_cyl_field`, `energy_eq_cylEnergy`, `cylLie_cyl`,
  `cylLie_eq_base`, `fderiv_circle_cylField`, `isCompact_cylSublevel`, `cylField_two_of_mem`,
  public static support), `tendsto_equilibrium` (**the source's claim, PROVED**: with
  `margin > 0`, `C_dc, L_s, R_s > 0`, `η ≠ 0`, `μ* u* v₀ ≠ 0`, every forward solution converges to
  one equilibrium `(θ*_dq + j π, u*, î(θ*_dq + j π))`), `exists_solution` (forward solutions exist
  on `[0, ∞)` for `margin ≥ 0`).

Family and connection conclusions.
* `family : Family Model MatchingStiffGrid.Requirement 4 0`: the translated loops, with the
  stiff-grid requirements read on `base` (`Meets`) and the stiff-grid translation
  (`family_isAutonomous`, `realize_univ`). Connection results: `mem_den_lyapunovStable`
  (`margin ≥ 0`, `μ* u* v₀ > 0`: the shifted energy is a local Lyapunov function on
  `|θ_dq − θ*_dq| < 2π`),
  `mem_den_locallyExponentiallyStable` (`margin > 0`, `η ≠ 0`, for every target angle),
  `chain_le_semantics`, `not_mem_den_globallyAsymptoticallyStable`,
  `not_mem_den_globallyExponentiallyStable`, `exact_globallyAsymptoticallyStable`,
  `exact_globallyExponentiallyStable` (`2π`-periodicity: no global asymptotic stability on `ℝ⁴`).
-/

noncomputable section
namespace powerlib.GFM.Matching.PowerTracking
open powerlib.Dynamics (State)
open Set Filter Topology

/-- Power set-point tracking on a stiff grid. -/
structure Model where
  /-- The stiff-grid closed loop; its modulation amplitude is the set-point `μ*` of (27a). -/
  base : MatchingStiffGrid.Model
  /-- The target angle error `θ*_dq = θ* − θ_g` of (27b). -/
  θs : ℝ

namespace Model
variable (m : Model)

/-- The DC current control (28). -/
def idc (x : State 4) : ℝ :=
  -m.base.Kp * (x 1 - m.base.ustar) + m.base.Gdc * m.base.ustar + m.base.ixHat (x 0) -
    m.base.κ * Real.sin (x 0 - m.θs)

/-- The closed loop in the grid `dq` frame, state `(θ_dq, u_dc, i_d, i_q)`. -/
def field (x : State 4) : State 4 :=
  WithLp.toLp 2 ![
    m.base.η * x 1 - m.base.ω0,
    (-m.base.Gdc * x 1 + m.idc x +
      m.base.μ * (-Real.sin (x 0) * x 2 + Real.cos (x 0) * x 3)) / m.base.Cdc,
    (-(m.base.Rs * x 2 - m.base.ω0 * m.base.Ls * x 3) - m.base.μ * (-Real.sin (x 0)) * x 1) /
      m.base.Ls,
    (-(m.base.ω0 * m.base.Ls * x 2 + m.base.Rs * x 3) + m.base.v0 -
      m.base.μ * Real.cos (x 0) * x 1) / m.base.Ls]

/-- The operating point `(θ*_dq, u*_dc, î_dq(θ*_dq))`. -/
def point : State 4 :=
  WithLp.toLp 2 ![m.θs, m.base.ustar, m.base.iHatD m.θs, m.base.iHatQ m.θs]

/-- The shifted energy `C_dc ũ²/2 + k (1 − cos(θ − θ*)) + L_s ‖i − î(θ)‖²/2`. -/
def energy (x : State 4) : ℝ :=
  m.base.Cdc / 2 * (x 1 - m.base.ustar) ^ 2 + m.base.k * (1 - Real.cos (x 0 - m.θs)) +
    m.base.Ls / 2 * ((x 2 - m.base.iHatD (x 0)) ^ 2 + (x 3 - m.base.iHatQ (x 0)) ^ 2)

end Model

/-- The tracking loop is the stiff-grid loop plus the shift of the synchronizing term in the DC
row. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_eq_base (m : Model) (x : State 4) :
    m.field x = m.base.field x + WithLp.toLp 2 ![0,
      m.base.κ * (Real.sin (x 0) - Real.sin (x 0 - m.θs)) / m.base.Cdc, 0, 0] := by
  ext i
  fin_cases i <;>
    simp [Model.field, Model.idc, MatchingStiffGrid.Model.field, MatchingStiffGrid.Model.idc]
  ring

/-- The shifted energy differs from the stiff-grid energy by `k (cos θ − cos(θ − θ*))`. Static
evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem energy_eq_base (m : Model) (x : State 4) :
    m.energy x = m.base.energy x + m.base.k * (Real.cos (x 0) - Real.cos (x 0 - m.θs)) := by
  simp only [Model.energy, MatchingStiffGrid.Model.energy]
  ring

/-- The derivative of the shifted energy. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem fderiv_energy (m : Model) (x v : State 4) :
    fderiv ℝ m.energy x v = fderiv ℝ m.base.energy x v +
      m.base.k * (Real.sin (x 0 - m.θs) - Real.sin (x 0)) * v 0 := by
  have p0 : HasFDerivAt (fun y : State 4 => y 0)
      (PiLp.proj 2 (fun _ : Fin 4 => ℝ) 0 : State 4 →L[ℝ] ℝ) x :=
    (PiLp.proj 2 (fun _ : Fin 4 => ℝ) 0 : State 4 →L[ℝ] ℝ).hasFDerivAt
  have hg := ((p0.cos).sub ((p0.sub_const m.θs).cos)).const_mul m.base.k
  have hb := (MatchingStiffGrid.energy_differentiable m.base x).hasFDerivAt
  have e : m.energy = fun y => m.base.energy y +
      m.base.k * (Real.cos (y 0) - Real.cos (y 0 - m.θs)) := funext (energy_eq_base m)
  have h : HasFDerivAt m.energy (fderiv ℝ m.base.energy x + m.base.k •
      (-Real.sin (x 0) • (PiLp.proj 2 (fun _ : Fin 4 => ℝ) 0 : State 4 →L[ℝ] ℝ) -
        -Real.sin (x 0 - m.θs) • (PiLp.proj 2 (fun _ : Fin 4 => ℝ) 0 : State 4 →L[ℝ] ℝ))) x := by
    rw [e]
    exact hb.add hg
  rw [h.fderiv]
  simp
  ring

/-- **The shift leaves the dissipation unchanged**: the Lie derivative of the shifted energy
along the tracking loop is that of the stiff-grid energy along the stiff-grid loop (the
appendix balance `MatchingStiffGrid.energy_lie`). Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem energy_lie (m : Model) (hC : m.base.Cdc ≠ 0) (x : State 4) :
    fderiv ℝ m.energy x (m.field x) = fderiv ℝ m.base.energy x (m.base.field x) := by
  rw [fderiv_energy, field_eq_base, map_add, MatchingStiffGrid.fderiv_energy m.base x
    (WithLp.toLp 2 ![0, _, 0, 0])]
  have hk := MatchingStiffGrid.eta_mul_k m.base
  simp [MatchingStiffGrid.Model.field, MatchingStiffGrid.Model.ω0]
  field_simp
  linear_combination (-(x 1 - m.base.ustar) * (Real.sin (x 0) - Real.sin (x 0 - m.θs))) * hk


/-- With `R_s > 0`, `dH/dt ≤ −margin ũ²` along the tracking loop. Static evidence on the model,
not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem energy_lie_le (m : Model) (hR : 0 < m.base.Rs)
    (hL : m.base.Ls ≠ 0) (hC : m.base.Cdc ≠ 0) (x : State 4) :
    fderiv ℝ m.energy x (m.field x) ≤ -m.base.margin * (x 1 - m.base.ustar) ^ 2 := by
  rw [energy_lie m hC]
  exact MatchingStiffGrid.energy_lie_le m.base hR hL hC x

/-- Every `θ_dq` with `κ sin(θ_dq − θ*_dq) = 0` gives an equilibrium `(θ_dq, u*, î(θ_dq))`.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_eq_zero_of_kappa_mul_sin_eq_zero (m : Model)
    (hN : m.base.N ≠ 0) {θ : ℝ} (h : m.base.κ * Real.sin (θ - m.θs) = 0) :
    m.field (WithLp.toLp 2 ![θ, m.base.ustar, m.base.iHatD θ, m.base.iHatQ θ]) = 0 := by
  ext i
  fin_cases i
  · simp [Model.field, MatchingStiffGrid.Model.ω0]
  · simp only [Model.field, Model.idc, MatchingStiffGrid.Model.ixHat, Transform.parkQ,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, PiLp.zero_apply, Fin.isValue,
      Fin.mk_one]
    linear_combination (-1 / m.base.Cdc) * h
  · simp only [Model.field, MatchingStiffGrid.Model.cD, MatchingStiffGrid.Model.cQ,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, PiLp.zero_apply, Fin.isValue,
      Fin.reduceFinMk]
    field_simp
    simp only [MatchingStiffGrid.Model.N]
    ring
  · simp only [Model.field, MatchingStiffGrid.Model.cD, MatchingStiffGrid.Model.cQ,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, PiLp.zero_apply, Fin.isValue,
      Fin.reduceFinMk]
    field_simp
    simp only [MatchingStiffGrid.Model.N]
    ring

/-- The operating point is an equilibrium. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem field_point (m : Model) (hN : m.base.N ≠ 0) :
    m.field m.point = 0 := by
  simpa [Model.point] using
    field_eq_zero_of_kappa_mul_sin_eq_zero m hN (θ := m.θs) (by simp)

/-- The tracking loop is `2π`-periodic in `θ_dq`. Static evidence on the model, not a
connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_add_two_pi (m : Model) (θ u id iq : ℝ) :
    m.field (WithLp.toLp 2 ![θ + 2 * Real.pi, u, id, iq]) =
      m.field (WithLp.toLp 2 ![θ, u, id, iq]) := by
  have h : Real.sin (θ + 2 * Real.pi - m.θs) = Real.sin (θ - m.θs) := by
    rw [show θ + 2 * Real.pi - m.θs = θ - m.θs + 2 * Real.pi by ring, Real.sin_add_two_pi]
  simp [Model.field, Model.idc, MatchingStiffGrid.Model.ixHat, Transform.parkQ,
    MatchingStiffGrid.Model.cD, MatchingStiffGrid.Model.cQ, h]


/-- Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem energy_point (m : Model) : m.energy m.point = 0 := by
  simp [Model.energy, Model.point]

@[tmio M, powerlib_domain] private theorem energy_pos (m : Model) (hC : 0 < m.base.Cdc)
    (hL : 0 < m.base.Ls) (hk : 0 < m.base.k) {x : State 4} (hx : |x 0 - m.θs| < 2 * Real.pi)
    (hne : x ≠ m.point) : 0 < m.energy x := by
  unfold Model.energy
  by_contra hle
  push Not at hle
  have a0 : 0 ≤ m.base.Cdc / 2 * (x 1 - m.base.ustar) ^ 2 := by positivity
  have a1 : 0 ≤ m.base.k * (1 - Real.cos (x 0 - m.θs)) :=
    mul_nonneg hk.le (by linarith [Real.cos_le_one (x 0 - m.θs)])
  have a2 : 0 ≤ m.base.Ls / 2 *
      ((x 2 - m.base.iHatD (x 0)) ^ 2 + (x 3 - m.base.iHatQ (x 0)) ^ 2) := by positivity
  have e0 : m.base.Cdc / 2 * (x 1 - m.base.ustar) ^ 2 = 0 := by linarith
  have e1 : m.base.k * (1 - Real.cos (x 0 - m.θs)) = 0 := by linarith
  have e2 : m.base.Ls / 2 *
      ((x 2 - m.base.iHatD (x 0)) ^ 2 + (x 3 - m.base.iHatQ (x 0)) ^ 2) = 0 := by linarith
  have u1 : x 1 = m.base.ustar := by
    have := (mul_eq_zero.mp e0).resolve_left (by positivity)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  have c1 : Real.cos (x 0 - m.θs) = 1 := by
    have := (mul_eq_zero.mp e1).resolve_left hk.ne'
    linarith
  have t0 : x 0 = m.θs := by
    rw [abs_lt] at hx
    have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) hx.2).mp c1
    linarith
  have e2' := (mul_eq_zero.mp e2).resolve_left (by positivity)
  have i2 : x 2 = m.base.iHatD (x 0) := by
    nlinarith [sq_nonneg (x 2 - m.base.iHatD (x 0)), sq_nonneg (x 3 - m.base.iHatQ (x 0))]
  have i3 : x 3 = m.base.iHatQ (x 0) := by
    nlinarith [sq_nonneg (x 2 - m.base.iHatD (x 0)), sq_nonneg (x 3 - m.base.iHatQ (x 0))]
  apply hne
  ext i
  fin_cases i <;> simp [Model.point, t0, u1, i2, i3]

/-! ## The set-point -/

/-- **The operating point carries the target current.** If the set-point modulation satisfies
(27b), `μ* u* (−sin θ*_dq, cos θ*_dq) = v₀ e₂ − Z_s i*` (grid `dq` frame, `v_g = v₀ e₂`), the
internal model at `θ*_dq` is `i*`: the equilibrium current of the tracking loop is the target.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem iHat_eq_of_setpoint (m : Model) (hN : m.base.N ≠ 0)
    {id iq : ℝ}
    (h27 : m.base.μ * m.base.ustar * -Real.sin m.θs =
        -(m.base.Rs * id - m.base.ω0 * m.base.Ls * iq) ∧
      m.base.μ * m.base.ustar * Real.cos m.θs =
        m.base.v0 - (m.base.ω0 * m.base.Ls * id + m.base.Rs * iq)) :
    m.base.iHatD m.θs = id ∧ m.base.iHatQ m.θs = iq := by
  obtain ⟨h1, h2⟩ := h27
  have hs : m.base.μ * m.base.ustar * Real.sin m.θs =
      m.base.Rs * id - m.base.ω0 * m.base.Ls * iq := by linarith
  have hc : m.base.v0 - m.base.μ * m.base.ustar * Real.cos m.θs =
      m.base.ω0 * m.base.Ls * id + m.base.Rs * iq := by linarith
  simp only [MatchingStiffGrid.Model.cD, MatchingStiffGrid.Model.cQ, hs, hc]
  constructor <;> field_simp <;> simp only [MatchingStiffGrid.Model.N] <;> ring

/-- **The set-point current (26) as printed.** For a grid voltage `v ≠ 0`, set-points
`(P*, Q*)` and `P_g = −iᵀ v`, `Q_g = −iᵀ J v`, `J = [0 1; −1 0]` (25), the current
`i = [P* Q*; −Q* P*] v / ‖v‖` delivers `(P_g, Q_g) = −‖v‖ (P*, Q*)`, not `(P*, Q*)`. Static
evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem setpoint_power_printed (P Q v1 v2 : ℝ)
    (hv : v1 ^ 2 + v2 ^ 2 ≠ 0) :
    -((P * v1 + Q * v2) / Real.sqrt (v1 ^ 2 + v2 ^ 2) * v1 +
        (-Q * v1 + P * v2) / Real.sqrt (v1 ^ 2 + v2 ^ 2) * v2) =
      -Real.sqrt (v1 ^ 2 + v2 ^ 2) * P ∧
    -((P * v1 + Q * v2) / Real.sqrt (v1 ^ 2 + v2 ^ 2) * v2 +
        (-Q * v1 + P * v2) / Real.sqrt (v1 ^ 2 + v2 ^ 2) * -v1) =
      -Real.sqrt (v1 ^ 2 + v2 ^ 2) * Q := by
  have hpos : 0 < v1 ^ 2 + v2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hv)
  have hn : Real.sqrt (v1 ^ 2 + v2 ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hsq := Real.sq_sqrt hpos.le
  constructor
  · field_simp
    linear_combination P * hsq
  · field_simp
    linear_combination Q * hsq

/-- **The set-point current, corrected.** With the same conventions, the current
`i = −[P* Q*; −Q* P*] v / ‖v‖²` delivers `(P_g, Q_g) = (P*, Q*)`. Static evidence on the model,
not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem setpoint_power (P Q v1 v2 : ℝ) (hv : v1 ^ 2 + v2 ^ 2 ≠ 0) :
    -(-(P * v1 + Q * v2) / (v1 ^ 2 + v2 ^ 2) * v1 +
        -(-Q * v1 + P * v2) / (v1 ^ 2 + v2 ^ 2) * v2) = P ∧
    -(-(P * v1 + Q * v2) / (v1 ^ 2 + v2 ^ 2) * v2 +
        -(-Q * v1 + P * v2) / (v1 ^ 2 + v2 ^ 2) * -v1) = Q := by
  constructor <;> field_simp <;> ring


/-! ## Linearization at the operating point -/

namespace Model
variable (m : Model)

/-- The Jacobian of the tracking loop at the operating point (`hasFDerivAt_field_point`). -/
def jac : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, m.base.η, 0, 0;
     m.base.μ * m.base.ω0 * m.base.Ls * (m.base.μ * m.base.ustar - m.base.v0) /
        (m.base.N * m.base.Cdc), -(m.base.Gdc + m.base.Kp) / m.base.Cdc,
       -(m.base.μ * Real.sin m.θs) / m.base.Cdc, m.base.μ * Real.cos m.θs / m.base.Cdc;
     m.base.μ * m.base.ustar * Real.cos m.θs / m.base.Ls,
       m.base.μ * Real.sin m.θs / m.base.Ls, -m.base.Rs / m.base.Ls, m.base.ω0;
     m.base.μ * m.base.ustar * Real.sin m.θs / m.base.Ls,
       -(m.base.μ * Real.cos m.θs) / m.base.Ls, -m.base.ω0, -m.base.Rs / m.base.Ls]

/-- The rotation of the current coordinates by `θ*_dq`. -/
def rot : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, Real.cos m.θs, -Real.sin m.θs;
     0, 0, Real.sin m.θs, Real.cos m.θs]

/-- The inverse rotation. -/
def rotInv : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, Real.cos m.θs, Real.sin m.θs;
     0, 0, -Real.sin m.θs, Real.cos m.θs]

end Model

@[tmio M, powerlib_domain] private theorem rot_mul_rotInv (m : Model) : m.rot * m.rotInv = 1 := by
  have h := Real.sin_sq_add_cos_sq m.θs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Model.rot, Model.rotInv, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | ring1 | linear_combination h

@[tmio M, powerlib_domain] private theorem rotInv_mul_rot (m : Model) : m.rotInv * m.rot = 1 := by
  have h := Real.sin_sq_add_cos_sq m.θs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Model.rot, Model.rotInv, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | ring1 | linear_combination h

/-- **The linearization at `θ*_dq` is the stiff-grid linearization at `0` in rotated current
coordinates**: `jac = R jac₀ R⁻¹`, `R = diag(1, 1, R(θ*_dq))`. Static evidence on the model, not
a connection conclusion. -/
@[tmio M, powerlib_domain] theorem jac_eq_conj (m : Model) :
    m.jac = m.rot * m.base.jac * m.rotInv := by
  have h := Real.sin_sq_add_cos_sq m.θs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Model.jac, Model.rot, Model.rotInv, MatchingStiffGrid.Model.jac, Matrix.mul_apply,
      Fin.sum_univ_four] <;>
    ring_nf <;> (try simp only [Real.cos_sq']) <;> ring_nf


/-- **The linearization at the operating point is Hurwitz** under the source's strict condition
(`margin > 0`), `C_dc, L_s, R_s > 0`, `μ* u* v₀ > 0` and `η ≠ 0`, for every target angle: it is
conjugate to the stiff-grid linearization (`jac_eq_conj`, `Linear.isHurwitz_conj`,
`MatchingStiffGrid.jac_isHurwitz`). Static evidence on the model, not a connection conclusion. -/
@[tmio TM, powerlib_domain] theorem jac_isHurwitz (m : Model) (hC : 0 < m.base.Cdc)
    (hL : 0 < m.base.Ls) (hR : 0 < m.base.Rs) (hs : 0 < m.base.μ * m.base.ustar * m.base.v0)
    (hη : m.base.η ≠ 0) (hδ : 0 < m.base.margin) : LinearSystems.IsHurwitz m.jac := by
  rw [jac_eq_conj]
  exact (Linear.isHurwitz_conj (rot_mul_rotInv m) (rotInv_mul_rot m) _).2
    (MatchingStiffGrid.jac_isHurwitz m.base hC hL hR hs hη hδ)

/-- Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_contDiff (m : Model) : ContDiff ℝ 1 m.field := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i <;>
    simp [Model.field, Model.idc, MatchingStiffGrid.Model.ixHat, Transform.parkQ,
      MatchingStiffGrid.Model.cD, MatchingStiffGrid.Model.cQ] <;> fun_prop

/-- Entries of the Jacobian applied to a vector. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem jac_apply (m : Model) (v : State 4) :
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.jac v) 0 = m.base.η * v 1 ∧
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.jac v) 1 =
      m.base.μ * m.base.ω0 * m.base.Ls * (m.base.μ * m.base.ustar - m.base.v0) /
          (m.base.N * m.base.Cdc) * v 0 - (m.base.Gdc + m.base.Kp) / m.base.Cdc * v 1 -
        m.base.μ * Real.sin m.θs / m.base.Cdc * v 2 +
        m.base.μ * Real.cos m.θs / m.base.Cdc * v 3 ∧
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.jac v) 2 =
      m.base.μ * m.base.ustar * Real.cos m.θs / m.base.Ls * v 0 +
        m.base.μ * Real.sin m.θs / m.base.Ls * v 1 - m.base.Rs / m.base.Ls * v 2 +
        m.base.ω0 * v 3 ∧
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.jac v) 3 =
      m.base.μ * m.base.ustar * Real.sin m.θs / m.base.Ls * v 0 -
        m.base.μ * Real.cos m.θs / m.base.Ls * v 1 - m.base.ω0 * v 2 -
        m.base.Rs / m.base.Ls * v 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four] <;>
    simp only [Model.jac, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;> ring

/-- The derivative of the tracking loop at the operating point is `jac`. Static evidence on the
model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_field_point (m : Model) (hN : m.base.N ≠ 0)
    (hL : m.base.Ls ≠ 0) :
    HasFDerivAt m.field (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.jac) m.point := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have hp : ∀ k : Fin 4, HasFDerivAt (fun x : State 4 => x k)
      (PiLp.proj 2 (fun _ : Fin 4 => ℝ) k : State 4 →L[ℝ] ℝ) m.point :=
    fun k => (PiLp.proj 2 (fun _ : Fin 4 => ℝ) k : State 4 →L[ℝ] ℝ).hasFDerivAt
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  have hs := h0.sin
  have hc := h0.cos
  have hsh := (h0.sub_const m.θs).sin
  have hD := (MatchingStiffGrid.hasDerivAt_iHatD m.base (m.point 0)).comp_hasFDerivAt m.point h0
  have hQ := (MatchingStiffGrid.hasDerivAt_iHatQ m.base (m.point 0)).comp_hasFDerivAt m.point h0
  have p0 : m.point 0 = m.θs := by simp [Model.point]
  have p1 : m.point 1 = m.base.ustar := by simp [Model.point]
  have p2 : m.point 2 = m.base.iHatD m.θs := by simp [Model.point]
  have p3 : m.point 3 = m.base.iHatQ m.θs := by simp [Model.point]
  have j := jac_apply m
  have hsc := Real.sin_sq_add_cos_sq m.θs
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · have h := (h1.const_mul m.base.η).sub_const m.base.ω0
    convert h using 1
    · funext y; simp [Model.field]
    · apply ContinuousLinearMap.ext; intro v
      simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply]
      rw [(j v).1]
      simp
  · have hix := ((hs.neg.mul hD).add (hc.mul hQ)).const_mul m.base.μ |>.neg
    have hidc :=
      ((((h1.sub_const m.base.ustar).const_mul (-m.base.Kp)).add_const
        (m.base.Gdc * m.base.ustar)).add hix).sub (hsh.const_mul m.base.κ)
    have h := (((h1.const_mul (-m.base.Gdc)).add hidc).add
      (((hs.neg.mul h2).add (hc.mul h3)).const_mul m.base.μ)).mul_const m.base.Cdc⁻¹
    convert h using 1
    · funext y
      simp only [Model.field, Model.idc, MatchingStiffGrid.Model.ixHat, Transform.parkQ,
        PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply,
        Pi.sub_apply, Pi.neg_apply, Pi.mul_apply, Function.comp_apply, div_eq_mul_inv]
    · apply ContinuousLinearMap.ext; intro v
      simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply]
      rw [(j v).2.1]
      simp [p0, p2, p3, MatchingStiffGrid.Model.κ, MatchingStiffGrid.Model.cD,
        MatchingStiffGrid.Model.cQ]
      field_simp
      linear_combination (-(m.base.μ ^ 2 * m.base.ustar * m.base.ω0 * m.base.Ls * v 0 /
        m.base.Cdc)) * hsc
  · have h := ((((h2.const_mul m.base.Rs).sub ((h3.const_mul m.base.ω0).const_mul
      m.base.Ls)).neg).sub ((hs.neg.const_mul m.base.μ).mul h1)).mul_const m.base.Ls⁻¹
    convert h using 1
    · funext y
      simp only [Model.field, PiLp.toLp_apply, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, Pi.sub_apply, Pi.neg_apply, Pi.mul_apply, div_eq_mul_inv]
      ring
    · apply ContinuousLinearMap.ext; intro v
      simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply]
      rw [(j v).2.2.1]
      simp [p0, p1]
      field_simp
      ring
  · have h :=
      (((((h2.const_mul m.base.ω0).const_mul m.base.Ls).add (h3.const_mul m.base.Rs)).neg.add_const
        m.base.v0).sub ((hc.const_mul m.base.μ).mul h1)).mul_const m.base.Ls⁻¹
    convert h using 1
    · funext y
      simp only [Model.field, PiLp.toLp_apply, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.mul_apply,
        div_eq_mul_inv]
      ring
    · apply ContinuousLinearMap.ext; intro v
      simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply]
      rw [(j v).2.2.2]
      simp [p0, p1]
      field_simp
      ring


/-! ## Family -/

/-- Satisfaction of a stiff-grid requirement by the base loop of a tracking model (the
requirements do not involve the target angle). -/
def Meets (m : Model) (r : MatchingStiffGrid.Requirement) : Prop :=
  MatchingStiffGrid.Meets m.base r

/-- The tracking loop translated to its operating point. -/
def Model.translated (m : Model) (z : State 4) : State 4 := m.field (z + m.point)

/-- The power-tracking family: the translated loops, read with the stiff-grid requirement
language and translation (`MatchingStiffGrid.translate`). -/
def family : Family Model MatchingStiffGrid.Requirement 4 0 :=
  ⟨fun m => Port.System.autonomous m.translated, Meets, MatchingStiffGrid.translate⟩

/-- The power-tracking family is the family of the translated autonomous fields. -/
@[tmio M, powerlib_domain] theorem family_isAutonomous : family.IsAutonomous Model.translated :=
  fun _ => rfl

@[tmio TM, powerlib_domain] private theorem mem_den_flow {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.field m.point :=
  Spectral.mem_den_flow_iff_shift (f := Model.field) (pt := Model.point) family_isAutonomous

/-- The whole requirement language is inconsistent. -/
@[tmio M, powerlib_domain] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of .synchronizing .antiSynchronizing fun m h1 h2 => ?_
  have h1 : 0 < m.base.μ * m.base.ustar * m.base.v0 := h1
  have h2 : m.base.μ * m.base.ustar * m.base.v0 < 0 := h2
  linarith

/-- **Local exponential stability of the tracking operating point** `(θ*_dq, u*, î(θ*_dq))`
under the source's strict condition `margin > 0`, with `C_dc, L_s, R_s > 0`, `μ* u* v₀ > 0` and
`η ≠ 0`, for every target angle `θ*_dq`. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable (m : Model)
    (hC : 0 < m.base.Cdc) (hL : 0 < m.base.Ls) (hR : 0 < m.base.Rs)
    (hs : 0 < m.base.μ * m.base.ustar * m.base.v0) (hη : m.base.η ≠ 0)
    (hδ : 0 < m.base.margin) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% mem_den_flow)]
  change LocallyExponentiallyStable m.field m.point
  have hN : 0 < m.base.N := MatchingStiffGrid.N_pos m.base hR.ne'
  exact hurwitz_linearization_locally_exponentially_stable m.jac (field_contDiff m)
    (field_point m hN.ne') (hasFDerivAt_field_point m hN.ne' hL.ne').fderiv
    (jac_isHurwitz m hC hL hR hs hη hδ)

/-- **Lyapunov stability of the tracking operating point** under the non-strict condition
`margin ≥ 0`, `C_dc, L_s, R_s > 0` and `μ* u* v₀ > 0`: the shifted energy is a local Lyapunov
function on `|θ_dq − θ*_dq| < 2π` (the appendix argument with `S(θ_dq − θ*_dq)`). -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable (m : Model) (hC : 0 < m.base.Cdc)
    (hL : 0 < m.base.Ls) (hR : 0 < m.base.Rs) (hs : 0 < m.base.μ * m.base.ustar * m.base.v0)
    (hδ : 0 ≤ m.base.margin) :
    connection% (m ∈ family.den (.flow .lyapunovStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% mem_den_flow)]
  change LyapunovStable m.field m.point
  have hk := MatchingStiffGrid.k_pos m.base hL hR hs
  have hcont : Continuous fun x : State 4 => x 0 - m.θs :=
    ((PiLp.proj 2 (fun _ : Fin 4 => ℝ) 0 : State 4 →L[ℝ] ℝ).continuous).sub continuous_const
  have hdiff : Differentiable ℝ m.energy := by
    intro x
    exact (MatchingStiffGrid.energy_differentiable m.base x).add (by fun_prop)
      |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => energy_eq_base m y)
  apply lyapunov_stable (D := {x : State 4 | |x 0 - m.θs| < 2 * Real.pi}) (by norm_num)
  exact
    { hD_open := isOpen_lt (continuous_abs.comp hcont) continuous_const
      hD_mem := by simp [Model.point, Real.pi_pos]
      hcont := hdiff.continuous
      hV_diff := hdiff
      hzero := energy_point m
      hpos := fun x hx hne => energy_pos m hC hL hk hx hne
      hLie_nonpos := fun x _ => (energy_lie_le m hR hL.ne' hC.ne' x).trans
        (by nlinarith [sq_nonneg (x 1 - m.base.ustar)]) }

/-- Every translation of the power-tracking family is sound. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_localTable (Rl := {.physical, .synchronizing, .dissipative})
    (Rs := {.physical, .synchronizing, .damped, .matching}) (Ru := Set.univ) (Rp := ∅)
    (fun s => ?_) realize_univ (fun m hm => ?_) (fun m hm => ?_) (fun m hm => ?_) (fun m _ => ?_)
  · rcases s with P | _ | _
    · cases P <;> rfl
    · rfl
    · rfl
  · rw [(connection_proof% TMIO.mem_realize)] at hm
    obtain ⟨hC, hL, hR⟩ : Meets m .physical := hm .physical (by simp)
    exact mem_den_lyapunovStable m hC hL hR (hm .synchronizing (by simp))
      (hm .dissipative (by simp))
  · rw [(connection_proof% TMIO.mem_realize)] at hm
    obtain ⟨hC, hL, hR⟩ : Meets m .physical := hm .physical (by simp)
    exact mem_den_locallyExponentiallyStable m hC hL hR (hm .synchronizing (by simp))
      (hm .matching (by simp)) (hm .damped (by simp))
  · exact Spectral.realize_univ_subset_of_eq_empty realize_univ _ hm
  · rw [family_isAutonomous.den_passive]
    trivial

/-- **Boundary**: no tracking loop is globally asymptotically stable on `ℝ⁴` (`2π`-periodicity
gives a second equilibrium whenever the operating point is one). -/
@[tmio TM, powerlib_domain] theorem not_mem_den_globallyAsymptoticallyStable (m : Model) :
    connection% (m ∉ family.den (.flow .globallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% mem_den_flow)]
  intro h
  change Flow.GloballyAsymptoticallyStable _ _ at h
  refine Dynamics.not_globallyAsymptoticallyStable_of_equilibrium_ne
    (y := WithLp.toLp 2 ![m.θs + 2 * Real.pi, m.base.ustar, m.base.iHatD m.θs,
      m.base.iHatQ m.θs]) ?_ ?_ h
  · rw [field_add_two_pi]
    exact h.1
  · intro he
    have h0 := congrArg (fun z : State 4 => z 0) he
    simp [Model.point, Real.pi_ne_zero] at h0

/-- The same boundary for global exponential stability. -/
@[tmio TM, powerlib_domain] theorem not_mem_den_globallyExponentiallyStable (m : Model) :
    connection% (m ∉ family.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact fun h => not_mem_den_globallyAsymptoticallyStable m
    (Spectral.den_globallyExponentiallyStable_subset_gas h)

/-- The global asymptotic translation is exact: both its denotation and its space are empty. -/
@[tmio TM, powerlib_domain] theorem exact_globallyAsymptoticallyStable :
    connection% (family.Exact (.flow .globallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_univ (F := family) realize_univ rfl
    (Set.eq_empty_iff_forall_notMem.mpr not_mem_den_globallyAsymptoticallyStable)

/-- The global exponential translation is exact: both its denotation and its space are empty. -/
@[tmio TM, powerlib_domain] theorem exact_globallyExponentiallyStable :
    connection% (family.Exact (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_univ (F := family) realize_univ rfl
    (Set.eq_empty_iff_forall_notMem.mpr not_mem_den_globallyExponentiallyStable)


/-! ## LaSalle on the cylinder (trajectory level, private implementation evidence) -/

namespace Model
variable (m : Model)

/-- The tracking loop on the cylinder `(cos θ, sin θ, u, i_d, i_q)` of
`MatchingStiffGrid.cyl`: the stiff-grid cylinder field plus the shift of the synchronizing term,
`sin(θ − θ*) = s cos θ* − c sin θ*`. -/
def cylField (y : State 5) : State 5 :=
  m.base.cylField y + WithLp.toLp 2 ![0, 0,
    m.base.κ * (y 1 - (y 1 * Real.cos m.θs - y 0 * Real.sin m.θs)) / m.base.Cdc, 0, 0]

/-- The shifted energy on the cylinder, `cos(θ − θ*) = c cos θ* + s sin θ*`. -/
def cylEnergy (y : State 5) : ℝ :=
  m.base.cylEnergy y + m.base.k * (y 0 - (y 0 * Real.cos m.θs + y 1 * Real.sin m.θs))

end Model

/-- The cylinder map is a semiconjugacy for the tracking loop. Static evidence on the model, not
a connection conclusion. -/
@[tmio M, powerlib_domain] theorem fderiv_cyl_field (m : Model) (x : State 4) :
    fderiv ℝ MatchingStiffGrid.cyl x (m.field x) = m.cylField (MatchingStiffGrid.cyl x) := by
  rw [Dynamics.fderiv_apply_eq_of_hasDerivAt_line
    ((MatchingStiffGrid.cyl_contDiff.differentiable (by norm_num)) x)
    (MatchingStiffGrid.hasDerivAt_cyl_line x _), Model.cylField, field_eq_base]
  rw [← MatchingStiffGrid.fderiv_cyl_field, Dynamics.fderiv_apply_eq_of_hasDerivAt_line
    ((MatchingStiffGrid.cyl_contDiff.differentiable (by norm_num)) x)
    (MatchingStiffGrid.hasDerivAt_cyl_line x _)]
  ext i
  fin_cases i <;> simp [MatchingStiffGrid.cyl, Real.sin_sub]

/-- Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem energy_eq_cylEnergy (m : Model) :
    m.energy = fun x => m.cylEnergy (MatchingStiffGrid.cyl x) := by
  funext x
  rw [energy_eq_base, Model.cylEnergy, MatchingStiffGrid.energy_eq_cylEnergy]
  simp [MatchingStiffGrid.cyl, Real.cos_sub]

@[tmio T, powerlib_foundation] private theorem circle_contDiff' :
    ContDiff ℝ 1 (fun y : State 5 => y 0 ^ 2 + y 1 ^ 2) := by
  have h0 := Dynamics.contDiff_coord (k := 1) (n := 5) 0
  have h1 := Dynamics.contDiff_coord (k := 1) (n := 5) 1
  fun_prop

/-- Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem cylEnergy_contDiff (m : Model) : ContDiff ℝ 1 m.cylEnergy := by
  have h0 := Dynamics.contDiff_coord (k := 1) (n := 5) 0
  have h1 := Dynamics.contDiff_coord (k := 1) (n := 5) 1
  exact (MatchingStiffGrid.cylEnergy_contDiff m.base).add (by fun_prop)

/-- Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem cylField_contDiff (m : Model) : ContDiff ℝ 1 m.cylField := by
  have h0 := Dynamics.contDiff_coord (k := 1) (n := 5) 0
  have h1 := Dynamics.contDiff_coord (k := 1) (n := 5) 1
  refine (MatchingStiffGrid.cylField_contDiff m.base).add ?_
  rw [contDiff_euclidean]
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- The Lie derivative of the cylinder energy at the image of a state is that of the shifted
energy, hence that of the stiff-grid energy (`energy_lie`). Static evidence on the model, not a
connection conclusion. -/
@[tmio M, powerlib_domain] theorem cylLie_cyl (m : Model) (x : State 4) :
    fderiv ℝ m.cylEnergy (MatchingStiffGrid.cyl x) (m.cylField (MatchingStiffGrid.cyl x)) =
      fderiv ℝ m.energy x (m.field x) := by
  have e : m.energy = m.cylEnergy ∘ MatchingStiffGrid.cyl := energy_eq_cylEnergy m
  rw [e, fderiv_comp x ((cylEnergy_contDiff m).differentiable (by norm_num) _)
    ((MatchingStiffGrid.cyl_contDiff.differentiable (by norm_num)) x),
    ContinuousLinearMap.comp_apply, fderiv_cyl_field]

/-- On the circle the tracking Lie derivative is the stiff-grid one. Static evidence on the
model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem cylLie_eq_base (m : Model) (hC : m.base.Cdc ≠ 0) {y : State 5}
    (hy : y 0 ^ 2 + y 1 ^ 2 = 1) :
    fderiv ℝ m.cylEnergy y (m.cylField y) = fderiv ℝ m.base.cylEnergy y (m.base.cylField y) := by
  obtain ⟨x, rfl⟩ := MatchingStiffGrid.exists_cyl_eq hy
  rw [cylLie_cyl, MatchingStiffGrid.cylLie_cyl, energy_lie m hC]

/-- The circle is a first integral of the tracking cylinder field. Static evidence on the model,
not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem fderiv_circle_cylField (m : Model) (y : State 5) :
    fderiv ℝ (fun y : State 5 => y 0 ^ 2 + y 1 ^ 2) y (m.cylField y) = 0 := by
  let p : Fin 5 → State 5 →L[ℝ] ℝ := fun j => PiLp.proj 2 (fun _ : Fin 5 => ℝ) j
  have hp : ∀ j, HasFDerivAt (fun x : State 5 => x j) (p j) y := fun j => (p j).hasFDerivAt
  have h : HasFDerivAt (fun y : State 5 => y 0 ^ 2 + y 1 ^ 2) _ y :=
    ((hp 0).pow 2).add ((hp 1).pow 2)
  rw [h.fderiv]
  simp [p, Model.cylField, MatchingStiffGrid.Model.cylField]
  ring

/-- The sublevel sets of the tracking energy on the cylinder are compact (they lie in stiff-grid
sublevel sets, the two energies differing by at most `2|k|` on the circle). Static evidence on
the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem isCompact_cylSublevel (m : Model) (hC : 0 < m.base.Cdc)
    (hL : 0 < m.base.Ls) (hR : 0 < m.base.Rs) (c : ℝ) :
    IsCompact {y : State 5 | y 0 ^ 2 + y 1 ^ 2 = 1 ∧ m.cylEnergy y ≤ c} := by
  refine (MatchingStiffGrid.isCompact_cylSublevel m.base hC hL hR
    (c + 2 * |m.base.k|)).of_isClosed_subset
    ((isClosed_eq circle_contDiff'.continuous continuous_const).inter
      (isClosed_le (cylEnergy_contDiff m).continuous continuous_const)) ?_
  rintro y ⟨hy, hV⟩
  refine ⟨hy, ?_⟩
  have hy0 : |y 0| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (y 1), sq_nonneg (y 0 + 1), sq_nonneg (y 0 - 1)]
  have hcs : |y 0 * Real.cos m.θs + y 1 * Real.sin m.θs| ≤ 1 := by
    rw [abs_le]
    have := Real.sin_sq_add_cos_sq m.θs
    constructor <;> nlinarith [sq_nonneg (y 0 * Real.sin m.θs - y 1 * Real.cos m.θs),
      sq_nonneg (y 0 * Real.cos m.θs + y 1 * Real.sin m.θs + 1),
      sq_nonneg (y 0 * Real.cos m.θs + y 1 * Real.sin m.θs - 1)]
  have hd : |m.base.k * (y 0 - (y 0 * Real.cos m.θs + y 1 * Real.sin m.θs))| ≤ 2 * |m.base.k| := by
    rw [abs_mul]
    have : |y 0 - (y 0 * Real.cos m.θs + y 1 * Real.sin m.θs)| ≤ 2 :=
      (abs_sub _ _).trans (by linarith)
    nlinarith [abs_nonneg m.base.k]
  unfold Model.cylEnergy at hV
  linarith [neg_abs_le (m.base.k * (y 0 - (y 0 * Real.cos m.θs + y 1 * Real.sin m.θs)))]

/-- On the set `ũ = 0`, `ĩ = 0` the DC row of the tracking cylinder field is
`−κ sin(θ − θ*)/C_dc`. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem cylField_two_of_mem (m : Model) {y : State 5}
    (h2 : y 2 = m.base.ustar) (h3 : y 3 = m.base.cD (y 0) (y 1))
    (h4 : y 4 = m.base.cQ (y 0) (y 1)) :
    m.cylField y 2 = -(m.base.κ * (y 1 * Real.cos m.θs - y 0 * Real.sin m.θs)) / m.base.Cdc := by
  have hb := MatchingStiffGrid.cylField_two_of_mem m.base h2 h3 h4
  simp only [Model.cylField, PiLp.add_apply, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, hb]
  ring


@[tmio M, powerlib_domain] private theorem iHatD_continuous (m : Model) :
    Continuous m.base.iHatD :=
  continuous_iff_continuousAt.2 fun θ => (MatchingStiffGrid.hasDerivAt_iHatD m.base θ).continuousAt

@[tmio M, powerlib_domain] private theorem iHatQ_continuous (m : Model) :
    Continuous m.base.iHatQ :=
  continuous_iff_continuousAt.2 fun θ => (MatchingStiffGrid.hasDerivAt_iHatQ m.base θ).continuousAt

/-- The image of every forward solution on the cylinder converges to the set
`{sin(θ − θ*) = 0, u = u*, i = î(c, s)}` (strict condition `margin > 0`). -/
@[tmio TM, powerlib_domain] private theorem tendsto_cyl (m : Model) (hC : 0 < m.base.Cdc)
    (hL : 0 < m.base.Ls) (hR : 0 < m.base.Rs) (hη : m.base.η ≠ 0)
    (hs : m.base.μ * m.base.ustar * m.base.v0 ≠ 0) (hδ : 0 < m.base.margin) {φ : ℝ → State 4}
    (hφ : IsIntegralCurveOn φ (fun _ x => m.field x) (Ici 0)) :
    Tendsto (fun t => MatchingStiffGrid.cyl (φ t)) atTop
      (𝓝ˢ {y : State 5 | y 1 * Real.cos m.θs - y 0 * Real.sin m.θs = 0 ∧ y 2 = m.base.ustar ∧
        y 3 = m.base.cD (y 0) (y 1) ∧ y 4 = m.base.cQ (y 0) (y 1)}) := by
  have hk : m.base.k ≠ 0 := by
    unfold MatchingStiffGrid.Model.k
    have : m.base.Ls * m.base.μ * m.base.ustar * m.base.v0 =
        m.base.Ls * (m.base.μ * m.base.ustar * m.base.v0) := by ring
    rw [this]
    exact div_ne_zero (mul_ne_zero hL.ne' hs) (MatchingStiffGrid.N_pos m.base hR.ne').ne'
  have hκ : m.base.κ ≠ 0 := by
    rw [← MatchingStiffGrid.eta_mul_k]
    exact mul_ne_zero hη hk
  have h2 : ContDiff ℝ 1 (fun y : State 5 => y 2 - m.base.ustar) :=
    (Dynamics.contDiff_coord (k := 1) 2).sub contDiff_const
  have hle : ∀ y : State 5, y 0 ^ 2 + y 1 ^ 2 = 1 → fderiv ℝ m.cylEnergy y (m.cylField y) ≤ 0 :=
    fun y hy => by
      rw [cylLie_eq_base m hC.ne' hy]
      exact (MatchingStiffGrid.cylLie_le m.base hR hL.ne' hC.ne' hy).trans
        (by nlinarith [sq_nonneg (y 2 - m.base.ustar)])
  refine Dynamics.LaSalle.lasalle_levelSet (h := fun y : State 5 => y 0 ^ 2 + y 1 ^ 2) (c₀ := 1)
    (c := m.cylEnergy (MatchingStiffGrid.cyl (φ 0))) (cylField_contDiff m)
    (circle_contDiff'.differentiable (by norm_num)) (cylEnergy_contDiff m)
    (fderiv_circle_cylField m) hle (isCompact_cylSublevel m hC hL hR _) ?_
    (Dynamics.LaSalle.isIntegralCurveOn_comp_of_fderiv
      (MatchingStiffGrid.cyl_contDiff.differentiable (by norm_num)) (fderiv_cyl_field m) hφ)
    (by simp) le_rfl
  refine Dynamics.LaSalle.lasalle_condition_of_lieDeriv_mem (cylField_contDiff m) h2 ?_ ?_
  · rintro y ⟨⟨hy, -⟩, h0⟩
    rw [cylLie_eq_base m hC.ne' hy] at h0
    exact sub_eq_zero.mpr (MatchingStiffGrid.cylLie_eq_zero m.base hR hL hC hδ hy h0).1
  · rintro y ⟨⟨hy, -⟩, h0⟩ hd
    rw [cylLie_eq_base m hC.ne' hy] at h0
    obtain ⟨e2, e3, e4⟩ := MatchingStiffGrid.cylLie_eq_zero m.base hR hL hC hδ hy h0
    have hf : HasFDerivAt (fun y : State 5 => y 2 - m.base.ustar)
        (PiLp.proj 2 (fun _ : Fin 5 => ℝ) 2 : State 5 →L[ℝ] ℝ) y :=
      (PiLp.proj 2 (fun _ : Fin 5 => ℝ) 2 : State 5 →L[ℝ] ℝ).hasFDerivAt.sub_const _
    rw [hf.fderiv] at hd
    have hd' : m.cylField y 2 = 0 := by simpa using hd
    rw [cylField_two_of_mem m e2 e3 e4, neg_div, neg_eq_zero,
      div_eq_zero_iff, or_iff_left hC.ne'] at hd'
    exact ⟨(mul_eq_zero.mp hd').resolve_left hκ, e2, e3, e4⟩

/-- **LaSalle convergence of power tracking (the source's claim that the appendix analysis
"pertains" with `S(θ_dq − θ*_dq)`, made precise).** Under the strict condition `margin > 0`, with
`C_dc, L_s, R_s > 0`, `η ≠ 0` and `μ* u* v₀ ≠ 0`, every forward solution converges to **one**
equilibrium `(θ*_dq + j π, u*, î(θ*_dq + j π))`, `j ∈ ℤ`. -/
@[tmio TM, powerlib_domain] private theorem tendsto_equilibrium (m : Model) (hC : 0 < m.base.Cdc)
    (hL : 0 < m.base.Ls) (hR : 0 < m.base.Rs) (hη : m.base.η ≠ 0)
    (hs : m.base.μ * m.base.ustar * m.base.v0 ≠ 0) (hδ : 0 < m.base.margin) {φ : ℝ → State 4}
    (hφ : IsIntegralCurveOn φ (fun _ x => m.field x) (Ici 0)) :
    ∃ j : ℤ, Tendsto φ atTop (𝓝 (WithLp.toLp 2 ![m.θs + j * Real.pi, m.base.ustar,
      m.base.iHatD (m.θs + j * Real.pi), m.base.iHatQ (m.θs + j * Real.pi)])) := by
  have hT := tendsto_cyl m hC hL hR hη hs hδ hφ
  have c5 : ∀ j : Fin 5, Continuous (fun y : State 5 => y j) := fun j =>
    (Dynamics.contDiff_coord (k := 1) j).continuous
  have hsin : Tendsto (fun t => Real.sin (φ t 0 - m.θs)) atTop (𝓝 0) := by
    have := Dynamics.LaSalle.tendsto_zero_of_tendsto_nhdsSet hT
      (((c5 1).mul continuous_const).sub ((c5 0).mul continuous_const)) (fun y hy => hy.1)
    simpa [MatchingStiffGrid.cyl, Real.sin_sub] using this
  have hcD : Continuous (fun y : State 5 => y 3 - m.base.cD (y 0) (y 1)) := by
    have h0 := c5 0
    have h1 := c5 1
    have h3 := c5 3
    unfold MatchingStiffGrid.Model.cD
    fun_prop
  have hcQ : Continuous (fun y : State 5 => y 4 - m.base.cQ (y 0) (y 1)) := by
    have h0 := c5 0
    have h1 := c5 1
    have h4 := c5 4
    unfold MatchingStiffGrid.Model.cQ
    fun_prop
  have hu : Tendsto (fun t => φ t 1 - m.base.ustar) atTop (𝓝 0) := by
    have := Dynamics.LaSalle.tendsto_zero_of_tendsto_nhdsSet hT ((c5 2).sub continuous_const)
      (fun y hy => sub_eq_zero.mpr hy.2.1)
    simpa using this
  have hd : Tendsto (fun t => φ t 2 - m.base.iHatD (φ t 0)) atTop (𝓝 0) := by
    have := Dynamics.LaSalle.tendsto_zero_of_tendsto_nhdsSet hT hcD
      (fun y hy => sub_eq_zero.mpr hy.2.2.1)
    simpa using this
  have hq : Tendsto (fun t => φ t 3 - m.base.iHatQ (φ t 0)) atTop (𝓝 0) := by
    have := Dynamics.LaSalle.tendsto_zero_of_tendsto_nhdsSet hT hcQ
      (fun y hy => sub_eq_zero.mpr hy.2.2.2)
    simpa using this
  have hθc : ContinuousOn (fun t => φ t 0 - m.θs) (Ici 0) :=
    ((Dynamics.contDiff_coord (k := 1) (n := 4) 0).continuous.comp_continuousOn
      hφ.continuousOn).sub continuousOn_const
  obtain ⟨j, hj⟩ := Dynamics.LaSalle.exists_int_tendsto_of_tendsto_sin hθc hsin
  have hj' : Tendsto (fun t => φ t 0) atTop (𝓝 (m.θs + j * Real.pi)) := by
    have := hj.add_const m.θs
    simpa [add_comm] using this
  refine ⟨j, Dynamics.tendsto_euclidean_of_coord fun i => ?_⟩
  fin_cases i
  · simpa using hj'
  · simpa using hu.add_const m.base.ustar
  · simpa using hd.add (((iHatD_continuous m).tendsto _).comp hj')
  · simpa using hq.add (((iHatQ_continuous m).tendsto _).comp hj')


/-- A forward solution on `[0, ∞)` from every state (with `margin ≥ 0`): the cylinder solution
stays in a compact energy sublevel set, and its angle is lifted back. -/
@[tmio TM, powerlib_domain] private theorem exists_solution (m : Model) (hC : 0 < m.base.Cdc)
    (hL : 0 < m.base.Ls) (hR : 0 < m.base.Rs) (hδ : 0 ≤ m.base.margin) (x₀ : State 4) :
    ∃ φ : ℝ → State 4, φ 0 = x₀ ∧ IsIntegralCurveOn φ (fun _ x => m.field x) (Ici 0) := by
  set c := m.cylEnergy (MatchingStiffGrid.cyl x₀)
  have hinv : IsPositivelyInvariant {y : State 5 | y 0 ^ 2 + y 1 ^ 2 = 1 ∧ m.cylEnergy y ≤ c}
      m.cylField :=
    Dynamics.LaSalle.isPositivelyInvariant_levelSet_sublevel
      (h := fun y : State 5 => y 0 ^ 2 + y 1 ^ 2)
      (circle_contDiff'.differentiable (by norm_num))
      ((cylEnergy_contDiff m).differentiable (by norm_num)) (fderiv_circle_cylField m)
      (fun y hy => by
        rw [cylLie_eq_base m hC.ne' hy]
        exact (MatchingStiffGrid.cylLie_le m.base hR hL.ne' hC.ne' hy).trans
          (by nlinarith [sq_nonneg (y 2 - m.base.ustar)]))
  obtain ⟨ψ, hψ0, hψ, -⟩ :=
    Dynamics.LaSalle.exists_isIntegralCurveOn_of_isCompact (cylField_contDiff m)
      (isCompact_cylSublevel m hC hL hR c) hinv (y₀ := MatchingStiffGrid.cyl x₀) ⟨by simp, le_rfl⟩
  have hco : ∀ t, 0 ≤ t → ∀ i,
      HasDerivWithinAt (fun τ => ψ τ i) (m.cylField (ψ t) i) (Ici 0) t :=
    fun t ht i => Dynamics.HasDerivWithinAt.euclidean_coord (hψ t ht) i
  have hw : ContinuousOn (fun t => m.base.η * ψ t 2 - m.base.ω0) (Ici 0) :=
    (continuousOn_const.mul
      ((Dynamics.contDiff_coord (k := 1) (n := 5) 2).continuous.comp_continuousOn
        hψ.continuousOn)).sub continuousOn_const
  obtain ⟨θ, hθ0, hθd, hθcs⟩ := Dynamics.LaSalle.exists_angle_lift (c := fun t => ψ t 0)
    (s := fun t => ψ t 1) (θ₀ := x₀ 0) hw
    (fun t ht => by
      simpa [Model.cylField, MatchingStiffGrid.Model.cylField] using hco t ht 0)
    (fun t ht => by
      simpa [Model.cylField, MatchingStiffGrid.Model.cylField] using hco t ht 1)
    (by simp [hψ0]) (by simp [hψ0])
  refine ⟨fun t => WithLp.toLp 2 ![θ t, ψ t 2, ψ t 3, ψ t 4], ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [hθ0, hψ0]
  · intro t ht
    have ht' : (0 : ℝ) ≤ t := ht
    have hψt : ψ t = MatchingStiffGrid.cyl (WithLp.toLp 2 ![θ t, ψ t 2, ψ t 3, ψ t 4]) := by
      ext i
      fin_cases i <;> simp [MatchingStiffGrid.cyl, (hθcs t ht').1, (hθcs t ht').2]
    have hF := fderiv_cyl_field m (WithLp.toLp 2 ![θ t, ψ t 2, ψ t 3, ψ t 4])
    rw [← hψt, Dynamics.fderiv_apply_eq_of_hasDerivAt_line
      ((MatchingStiffGrid.cyl_contDiff.differentiable (by norm_num)) _)
      (MatchingStiffGrid.hasDerivAt_cyl_line _ _)] at hF
    apply Dynamics.hasDerivWithinAt_euclidean_of_coord
    intro i
    fin_cases i
    · simpa [Model.field] using hθd t ht'
    · have h := hco t ht' 2
      rw [← hF] at h
      simpa using h
    · have h := hco t ht' 3
      rw [← hF] at h
      simpa using h
    · have h := hco t ht' 4
      rw [← hF] at h
      simpa using h

end powerlib.GFM.Matching.PowerTracking
