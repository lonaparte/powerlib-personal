import theorem.Spectral.Global
import theorem.Passive.Series
import theorem.Passive.Parallel
import theorem.Criteria.Lyapunov
import theorem.Dynamics.Coordinates
import theorem.Transform.Park
import theorem.Dynamics.Instability

/-! # Matching control on a weak grid: energy shaping with the Bregman potential

The weak-grid closed loop of the source's §IV: the converter with L filter feeds an AC bus with
capacitor `C_f` and shunt conductance `G_f` that carries a measurable load current of constant
amplitude `i₀` rotating at `ω₀`; the synchronizing term of the DC current control is the gradient
of the Bregman divergence `W` of the internal-model reactive power `Q̂_f/ω₀`, which is the
active-power droop. This module formalizes the closed loop, the source's identities (33), (35),
(38)–(39), the equilibria, the energy balance and the local stability conclusions.

Model boundary.
* Averaged converter (no PWM or delay), DC capacitor `C_dc`, DC conductance `G_dc`, L filter
  `L_s`, `R_s`, bus capacitor `C_f` with conductance `G_f` (local load and grid admittance,
  (30d)), load current `i_g` of amplitude `i₀` at the frequency `ω₀ = η u*_dc`; no current or
  modulation limits, no PLL. Analysis frame: the `dq` frame of the load-current angle `θ_g`
  (`θ_g' = ω₀`), with its origin chosen so that `i_g = i₀ (−sin θ_g, cos θ_g)`, i.e.
  `i_g,dq = (0, i₀)` (any other phase of `i_g` is a constant rotation of this frame). State
  `(θ_dq, u_dc, i_d, i_q, v_d, v_q) ∈ ℝ⁶` (`Model.field`): `θ_dq' = η u_dc − ω₀`,
  `C_dc u_dc' = −G_dc u_dc + i_dc + μ (−sin θ_dq, cos θ_dq)ᵀ i_dq`,
  `L_s i_dq' = −Z_s i_dq + v_dq − μ (−sin θ_dq, cos θ_dq) u_dc`,
  `C_f v_dq' = −Y_f v_dq − i_dq − i_g,dq` (`Z_s = R_s + ω₀L_s J₀`, `Y_f = G_f + ω₀C_f J₀`), with
  the control (36) `i_dc = −K_p ũ_dc + G_dc u*_dc + î_x(θ_dq) − η ∇W(θ_dq)`. Continuous time,
  autonomous. The modulation amplitude `μ` is a constant parameter: the voltage controller
  `μ = μ̂_f(θ, i_g)` of §IV-A (a state-dependent amplitude) is excluded, since (33) and the
  energy argument hold for constant `μ` only.
* Operating point `(θ*_dq, u*, î(θ*_dq), v̂(θ*_dq))` (`Model.point`, `θs` a parameter;
  `P*_f = P̂_f(θ*_dq)`). Parameter ranges as stated in each result
  (`C_dc, L_s, R_s, C_f, G_f > 0` for the stability results).
* Excluded: the voltage controller of §IV-A, the droop variant (40)
  (`θ' = η u_dc − κ (P̂_f − P*_f)`), the path-following augmentation (41), the two-unit
  experiment of §V, and global results (the source proves none for the weak grid, and `W` is
  tilted, unbounded below in general).

Source: C. Arghir, F. Dörfler, "The electronic realization of synchronous machines: model
matching, angle tracking, and energy shaping techniques", IEEE Trans. Power Electron. 35(4)
(2020) 4398–4410, author version (ETH Research Collection, `bare_jrnl.pdf`, text layer read):
§IV, the model (30a)–(30d) with Fig. 8 (`θ_g' = ω₀`, `i_g` of constant magnitude `i₀`), the
internal models (31a) `î_s = −(Y_f⁻¹ + Z_s)⁻¹ (μ u* (−sin θ, cos θ) + Y_f⁻¹ i_g)`, (31b)
`v̂_f = (Z_s Y_f + I)⁻¹ (μ u* (−sin θ, cos θ) − Z_s i_g)`, the powers (32)
`P̂_f = i_gᵀ v̂_f`, `Q̂_f = i_gᵀ [0 1; −1 0] v̂_f`, (33)–(36), (37)
`P̂_loss = ½ î_sᵀ R_s î_s + ½ v̂_fᵀ G_f v̂_f`, (38) `î_x = (P̂_loss + P̂_f)/u*`, (39); work-sync
`theory/papers/@arghir2020matching.md` ("weak grid 用基于 Q̂_f 的 Bregman 散度").

Results.
* Static (source identities): `steady_d`, `steady_q` (the internal models are the steady state at
  `u_dc = u*`), `Phat_sub_dQhat` (**(33) is exact**: `P̂_f − ∇Q̂_f` is the constant
  `−i₀²(R_s + G_f N)/|1 + Z_sY_f|²`), `eta_mul_gradW` (**(35)**: `η ∇W = (P̂_f − P*_f)/u*`, the
  synchronizing torque is the active-power droop), `ustar_mul_ixHat` (**correction of (37)**: the
  power balance is `u* î_x = R_s‖î‖² + G_f‖v̂‖² + P̂_f`, so (38) holds with twice the loss (37) as
  printed), `idc_eq_injection` (with that loss, (36) is (39)).
* Static (internal-model calculus): `D_pos`, `hasDerivAt_vHatD`, `hasDerivAt_vHatQ`,
  `hasDerivAt_iHatD`, `hasDerivAt_iHatQ`, `hasDerivAt_W` (`W' = ∇W`), `hasDerivAt_gradW`,
  `dv_sq`, `dj_sq` (`|v̂'|² = μ²u*²/|1+Z_sY_f|²`, `|î'|² = |Y_f|² |v̂'|²`), `steady_d'`,
  `steady_q'`.
* Static (equilibria and energy): `field_eq_zero_of_gradW_eq_zero` (every angle with
  `P̂_f(θ_dq) = P*_f` gives an equilibrium `(θ_dq, u*, î(θ_dq), v̂(θ_dq))`), `field_point`,
  `field_add_two_pi`, `energy_differentiable`, `fderiv_energy`, `energy_lie` (**the energy
  balance**: with `H = C_dc ũ²/2 + W(θ) + L_s‖ĩ‖²/2 + C_f‖ṽ‖²/2`,
  `dH/dt = −(G_dc+K_p) ũ² − R_s‖ĩ‖² − G_f‖ṽ‖² − η ũ (L_s ĩᵀ î' + C_f ṽᵀ v̂')`), `energy_lie_le`
  (`dH/dt ≤ −margin ũ²`, `margin = G_dc + K_p − η²μ²u*² (L_s²|Y_f|²/(4R_s) + C_f²/(4G_f))/
  |1 + Z_sY_f|²`).
* Linearization: `jac`, `hasFDerivAt_field_point`, `field_contDiff`, `jac_apply`, the quadratic
  energy `lyap` (`lyap_form`) and its dissipation (`lyap_jac`, `lyap_jac_le`), `jac_isHurwitz`
  (`margin > 0`, `W''(θ*_dq) = kW > 0`, `η ≠ 0`).

Family and connection conclusions.
* `family : Family Model Requirement 6 0`: the translated loops (`family_isAutonomous`).
  Requirements `physical` (`C_dc, L_s, R_s, C_f, G_f > 0`), `convex` (`kW > 0`), `concave`
  (`kW < 0`), `damped` (`margin > 0`), `matching` (`η ≠ 0`); translation `Spectral.localTable`:
  Lyapunov, local asymptotic and local exponential stability into
  `{physical, convex, damped, matching}`, passivity into nothing, every other sentence into the
  whole, inconsistent, language (`realize_univ`). Connection results:
  `mem_den_locallyExponentiallyStable`, `chain_le_semantics`,
  `not_mem_den_globallyAsymptoticallyStable`, `not_mem_den_globallyExponentiallyStable`,
  `exact_globallyAsymptoticallyStable`, `exact_globallyExponentiallyStable` (the field is
  `2π`-periodic in `θ_dq` although `W` is not).
* Not proved: the source's "the set-point is achieved asymptotically" beyond the local
  statement (no basin estimate; a LaSalle argument fails as stated because `H` is unbounded
  below when `W` is tilted), and the closed loop with the voltage controller `μ̂_f`.
-/

noncomputable section
namespace powerlib.GFM.Matching.WeakGrid
open powerlib.Dynamics (State)
open Matrix

/-- Parameters of matching control on a weak grid. -/
structure Model where
  /-- The DC link: capacitance `C_dc`, conductance `G_dc`. -/
  dcLink : Passive.ParallelRLC
  /-- The DC P-gain `K_p`. -/
  Kp : ℝ
  /-- The matching gain `η`. -/
  η : ℝ
  /-- The (constant) modulation amplitude. -/
  μ : ℝ
  /-- The DC voltage reference `u*_dc`. -/
  ustar : ℝ
  /-- The L filter: series inductor `L_s` with resistance `R_s`. -/
  filter : Passive.SeriesRLC
  /-- The AC bus: capacitance `C_f`, shunt conductance `G_f` (load and grid admittance). -/
  bus : Passive.ParallelRLC
  /-- The amplitude `i₀` of the measurable load current `i_g`. -/
  i0 : ℝ
  /-- The operating angle error `θ*_dq`. -/
  θs : ℝ
  /-- The DC link has no shunt inductor. -/
  dcLink_noInd : dcLink.Γ = 0
  /-- The filter has no series capacitor. -/
  filter_noCap : filter.S = 0
  /-- The bus has no shunt inductor. -/
  bus_noInd : bus.Γ = 0

namespace Model
variable (m : Model)

/-- The DC-link capacitance. -/
abbrev Cdc : ℝ := m.dcLink.C
/-- The DC-link conductance. -/
abbrev Gdc : ℝ := m.dcLink.G
/-- The filter resistance `R_s`. -/
abbrev Rs : ℝ := m.filter.R
/-- The filter inductance `L_s`. -/
abbrev Ls : ℝ := m.filter.L
/-- The bus capacitance `C_f`. -/
abbrev Cf : ℝ := m.bus.C
/-- The bus conductance `G_f`. -/
abbrev Gf : ℝ := m.bus.G

/-- The frequency `ω₀ = η u*_dc` of the load current. -/
def ω0 : ℝ := m.η * m.ustar

/-- `Re (1 + Z_s Y_f)`. -/
def a : ℝ := 1 + m.Rs * m.Gf - m.ω0 ^ 2 * m.Ls * m.Cf
/-- `Im (1 + Z_s Y_f)`. -/
def b : ℝ := m.ω0 * (m.Rs * m.Cf + m.Ls * m.Gf)
/-- `|1 + Z_s Y_f|²`. -/
def D : ℝ := m.a ^ 2 + m.b ^ 2

/-- The internal model of the bus voltage (31b), `d` component, at `(c, s) = (cos θ, sin θ)`:
`v̂ = (Z_s Y_f + I)⁻¹ (μ u* (−s, c) − Z_s i_g)`, `i_g = (0, i₀)`. -/
def vD (c s : ℝ) : ℝ :=
  (m.a * (-(m.μ * m.ustar * s) + m.ω0 * m.Ls * m.i0) +
    m.b * (m.μ * m.ustar * c - m.Rs * m.i0)) / m.D
/-- The internal model of the bus voltage, `q` component. -/
def vQ (c s : ℝ) : ℝ :=
  (m.a * (m.μ * m.ustar * c - m.Rs * m.i0) -
    m.b * (-(m.μ * m.ustar * s) + m.ω0 * m.Ls * m.i0)) / m.D
/-- The internal model of the switch current (31a), `d` component: `î = −Y_f v̂ − i_g`. -/
def jD (c s : ℝ) : ℝ := -(m.Gf * m.vD c s - m.ω0 * m.Cf * m.vQ c s)
/-- The internal model of the switch current, `q` component. -/
def jQ (c s : ℝ) : ℝ := -(m.ω0 * m.Cf * m.vD c s + m.Gf * m.vQ c s) - m.i0

/-- `v̂_d(θ)`. -/
abbrev vHatD (θ : ℝ) : ℝ := m.vD (Real.cos θ) (Real.sin θ)
/-- `v̂_q(θ)`. -/
abbrev vHatQ (θ : ℝ) : ℝ := m.vQ (Real.cos θ) (Real.sin θ)
/-- `î_d(θ)`. -/
abbrev iHatD (θ : ℝ) : ℝ := m.jD (Real.cos θ) (Real.sin θ)
/-- `î_q(θ)`. -/
abbrev iHatQ (θ : ℝ) : ℝ := m.jQ (Real.cos θ) (Real.sin θ)

/-- `d v̂_d / dθ` at `(c, s)`. -/
def dvD (c s : ℝ) : ℝ := (-(m.a * m.μ * m.ustar * c) - m.b * m.μ * m.ustar * s) / m.D
/-- `d v̂_q / dθ` at `(c, s)`. -/
def dvQ (c s : ℝ) : ℝ := (-(m.a * m.μ * m.ustar * s) + m.b * m.μ * m.ustar * c) / m.D
/-- `d î_d / dθ` at `(c, s)`. -/
def djD (c s : ℝ) : ℝ := -(m.Gf * m.dvD c s - m.ω0 * m.Cf * m.dvQ c s)
/-- `d î_q / dθ` at `(c, s)`. -/
def djQ (c s : ℝ) : ℝ := -(m.ω0 * m.Cf * m.dvD c s + m.Gf * m.dvQ c s)

/-- The internal-model active power `P̂_f = i_gᵀ v̂` (32). -/
def Phat (θ : ℝ) : ℝ := m.i0 * m.vHatQ θ
/-- The internal-model reactive power `Q̂_f = i_gᵀ J v̂` (32). -/
def Qhat (θ : ℝ) : ℝ := -(m.i0 * m.vHatD θ)
/-- `∇Q̂_f`. -/
def dQhat (θ : ℝ) : ℝ := -(m.i0 * m.dvD (Real.cos θ) (Real.sin θ))
/-- `∇²Q̂_f`. -/
def ddQhat (θ : ℝ) : ℝ :=
  -(m.i0 * ((m.a * m.μ * m.ustar * Real.sin θ - m.b * m.μ * m.ustar * Real.cos θ) / m.D))

/-- The synchronization potential (34), the Bregman divergence of `Q̂_f/ω₀` at `θ*_dq`. -/
def W (θ : ℝ) : ℝ := (m.Qhat θ - m.Qhat m.θs - m.dQhat m.θs * (θ - m.θs)) / m.ω0
/-- `∇W` (34). -/
def gradW (θ : ℝ) : ℝ := (m.dQhat θ - m.dQhat m.θs) / m.ω0
/-- The curvature `W''(θ*_dq) = ∇²Q̂_f(θ*_dq)/ω₀`. -/
def kW : ℝ := m.ddQhat m.θs / m.ω0

/-- The internal model of the DC current, `î_x = −μ (−sin θ, cos θ)ᵀ î(θ)`. -/
def ixHat (θ : ℝ) : ℝ := -(m.μ * Transform.parkQ θ (m.iHatD θ) (m.iHatQ θ))

/-- The DC current control (36). -/
def idc (x : State 6) : ℝ :=
  -m.Kp * (x 1 - m.ustar) + m.Gdc * m.ustar + m.ixHat (x 0) - m.η * m.gradW (x 0)

/-- The closed loop (30), (36) in the load-current `dq` frame, state
`(θ_dq, u_dc, i_d, i_q, v_d, v_q)`. -/
def field (x : State 6) : State 6 :=
  WithLp.toLp 2 ![
    m.η * x 1 - m.ω0,
    (-m.Gdc * x 1 + m.idc x + m.μ * (-Real.sin (x 0) * x 2 + Real.cos (x 0) * x 3)) / m.Cdc,
    (-(m.Rs * x 2 - m.ω0 * m.Ls * x 3) + x 4 - m.μ * (-Real.sin (x 0)) * x 1) / m.Ls,
    (-(m.ω0 * m.Ls * x 2 + m.Rs * x 3) + x 5 - m.μ * Real.cos (x 0) * x 1) / m.Ls,
    (-(m.Gf * x 4 - m.ω0 * m.Cf * x 5) - x 2) / m.Cf,
    (-(m.ω0 * m.Cf * x 4 + m.Gf * x 5) - x 3 - m.i0) / m.Cf]

/-- The operating point `(θ*_dq, u*, î(θ*_dq), v̂(θ*_dq))`. -/
def point : State 6 :=
  WithLp.toLp 2 ![m.θs, m.ustar, m.iHatD m.θs, m.iHatQ m.θs, m.vHatD m.θs, m.vHatQ m.θs]

/-- The energy `C_dc ũ²/2 + W(θ) + L_s ‖i − î(θ)‖²/2 + C_f ‖v − v̂(θ)‖²/2`. -/
def energy (x : State 6) : ℝ :=
  m.Cdc / 2 * (x 1 - m.ustar) ^ 2 + m.W (x 0) +
    m.Ls / 2 * ((x 2 - m.iHatD (x 0)) ^ 2 + (x 3 - m.iHatQ (x 0)) ^ 2) +
    m.Cf / 2 * ((x 4 - m.vHatD (x 0)) ^ 2 + (x 5 - m.vHatQ (x 0)) ^ 2)

/-- The damping margin
`G_dc + K_p − η² μ² u*² (L_s² |Y_f|²/(4R_s) + C_f²/(4G_f))/|1 + Z_s Y_f|²`. -/
def margin : ℝ :=
  m.Gdc + m.Kp - m.η ^ 2 * m.μ ^ 2 * m.ustar ^ 2 *
    (m.Ls ^ 2 * (m.Gf ^ 2 + m.ω0 ^ 2 * m.Cf ^ 2) / (4 * m.Rs) + m.Cf ^ 2 / (4 * m.Gf)) / m.D

end Model

/-- `|1 + Z_s Y_f|² > 0` for a physical filter and bus. Static evidence on the model, not a
connection conclusion. -/
@[tmio M, powerlib_domain] theorem D_pos (m : Model) (hR : 0 < m.Rs) (hL : 0 < m.Ls)
    (hCf : 0 < m.Cf) (hGf : 0 < m.Gf) : 0 < m.D := by
  unfold Model.D
  by_cases hω : m.ω0 = 0
  · have : m.a = 1 + m.Rs * m.Gf := by simp [Model.a, hω]
    rw [this]
    positivity
  · have hb : m.b ≠ 0 := mul_ne_zero hω (by positivity)
    have := sq_pos_of_ne_zero hb
    positivity

/-- The internal models solve the inductor rows at `u_dc = u*`. Static evidence on the model,
not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem steady_d (m : Model) (hD : m.D ≠ 0) (c s : ℝ) :
    -(m.Rs * m.jD c s - m.ω0 * m.Ls * m.jQ c s) + m.vD c s + m.μ * s * m.ustar = 0 := by
  simp only [Model.jD, Model.jQ, Model.vD, Model.vQ]
  field_simp
  simp only [Model.D, Model.a, Model.b]
  ring

/-- Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem steady_q (m : Model) (hD : m.D ≠ 0) (c s : ℝ) :
    -(m.ω0 * m.Ls * m.jD c s + m.Rs * m.jQ c s) + m.vQ c s - m.μ * c * m.ustar = 0 := by
  simp only [Model.jD, Model.jQ, Model.vD, Model.vQ]
  field_simp
  simp only [Model.D, Model.a, Model.b]
  ring

/-- **(33) is exact**: `P̂_f − ∇Q̂_f` is the constant `−i₀² (R_s + G_f N)/|1 + Z_s Y_f|²`,
`N = R_s² + ω₀² L_s²`. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem Phat_sub_dQhat (m : Model) (θ : ℝ) :
    m.Phat θ - m.dQhat θ =
      -(m.i0 ^ 2 * (m.Rs + m.Gf * (m.Rs ^ 2 + m.ω0 ^ 2 * m.Ls ^ 2)) / m.D) := by
  simp only [Model.Phat, Model.dQhat, Model.vQ, Model.dvD, Model.a, Model.b]
  ring

/-- **The synchronizing torque is the active-power droop (35)**:
`η ∇W(θ) = (P̂_f(θ) − P̂_f(θ*_dq))/u*_dc`. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem eta_mul_gradW (m : Model) (hη : m.η ≠ 0) (hu : m.ustar ≠ 0)
    (θ : ℝ) : m.η * m.gradW θ = (m.Phat θ - m.Phat m.θs) / m.ustar := by
  have h1 := Phat_sub_dQhat m θ
  have h2 := Phat_sub_dQhat m m.θs
  simp only [Model.gradW, Model.ω0]
  field_simp
  linear_combination (-1 : ℝ) * h1 + h2


/-- **Steady-state power balance of the internal model (38), corrected**:
`u* î_x(θ) = R_s ‖î(θ)‖² + G_f ‖v̂(θ)‖² + P̂_f(θ)`, so (38) holds with
`P̂_loss = î_sᵀ R_s î_s + v̂_fᵀ G_f v̂_f`, twice the loss (37) as it reads in the text layer of the
author version. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem ustar_mul_ixHat (m : Model) (hD : m.D ≠ 0) (θ : ℝ) :
    m.ustar * m.ixHat θ = m.Rs * (m.iHatD θ ^ 2 + m.iHatQ θ ^ 2) +
      m.Gf * (m.vHatD θ ^ 2 + m.vHatQ θ ^ 2) + m.Phat θ := by
  have hd := steady_d m hD (Real.cos θ) (Real.sin θ)
  have hq := steady_q m hD (Real.cos θ) (Real.sin θ)
  have hJd : m.iHatD θ = -(m.Gf * m.vHatD θ - m.ω0 * m.Cf * m.vHatQ θ) := rfl
  have hJq : m.iHatQ θ = -(m.ω0 * m.Cf * m.vHatD θ + m.Gf * m.vHatQ θ) - m.i0 := rfl
  simp only [Model.ixHat, Transform.parkQ, Model.Phat]
  linear_combination m.iHatD θ * hd + m.iHatQ θ * hq - m.vHatD θ * hJd - m.vHatQ θ * hJq

/-- **(36) is the active-power injection (39)** with the corrected loss: for `η, u* ≠ 0`,
`i_dc = −K_p ũ + (G_dc u*² + P̂_loss(θ) + P*_f)/u*`, `P*_f = P̂_f(θ*_dq)`. Static evidence on the
model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem idc_eq_injection (m : Model) (hD : m.D ≠ 0) (hη : m.η ≠ 0)
    (hu : m.ustar ≠ 0) (x : State 6) :
    m.idc x = -m.Kp * (x 1 - m.ustar) + (m.Gdc * m.ustar ^ 2 +
      (m.Rs * (m.iHatD (x 0) ^ 2 + m.iHatQ (x 0) ^ 2) +
        m.Gf * (m.vHatD (x 0) ^ 2 + m.vHatQ (x 0) ^ 2)) + m.Phat m.θs) / m.ustar := by
  have h1 := ustar_mul_ixHat m hD (x 0)
  have h2 := eta_mul_gradW m hη hu (x 0)
  simp only [Model.idc]
  rw [h2]
  field_simp
  linear_combination h1

/-! ## Derivatives of the internal models -/

/-- Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_vHatD (m : Model) (θ : ℝ) :
    HasDerivAt m.vHatD (m.dvD (Real.cos θ) (Real.sin θ)) θ := by
  have h := ((((Real.hasDerivAt_sin θ).const_mul (m.μ * m.ustar)).neg.add_const
    (m.ω0 * m.Ls * m.i0)).const_mul m.a).add
    ((((Real.hasDerivAt_cos θ).const_mul (m.μ * m.ustar)).sub_const (m.Rs * m.i0)).const_mul m.b)
  convert h.div_const m.D using 1
  · funext θ
    simp [Model.vD]
  · simp only [Model.dvD]
    ring

/-- Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_vHatQ (m : Model) (θ : ℝ) :
    HasDerivAt m.vHatQ (m.dvQ (Real.cos θ) (Real.sin θ)) θ := by
  have h := ((((Real.hasDerivAt_cos θ).const_mul (m.μ * m.ustar)).sub_const
    (m.Rs * m.i0)).const_mul m.a).sub
    ((((Real.hasDerivAt_sin θ).const_mul (m.μ * m.ustar)).neg.add_const
      (m.ω0 * m.Ls * m.i0)).const_mul m.b)
  convert h.div_const m.D using 1
  · funext θ
    simp [Model.vQ]
  · simp only [Model.dvQ]
    ring

/-- Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_iHatD (m : Model) (θ : ℝ) :
    HasDerivAt m.iHatD (m.djD (Real.cos θ) (Real.sin θ)) θ := by
  have h := (((hasDerivAt_vHatD m θ).const_mul m.Gf).sub
    ((hasDerivAt_vHatQ m θ).const_mul (m.ω0 * m.Cf))).neg
  convert h using 1
  · funext θ
    simp [Model.jD]
  · simp only [Model.djD]

/-- Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_iHatQ (m : Model) (θ : ℝ) :
    HasDerivAt m.iHatQ (m.djQ (Real.cos θ) (Real.sin θ)) θ := by
  have h := ((((hasDerivAt_vHatD m θ).const_mul (m.ω0 * m.Cf)).add
    ((hasDerivAt_vHatQ m θ).const_mul m.Gf)).neg).sub_const m.i0
  convert h using 1
  · funext θ
    simp [Model.jQ]
  · simp only [Model.djQ]

/-- `∇W` is the derivative of `W`. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_W (m : Model) (θ : ℝ) :
    HasDerivAt m.W (m.gradW θ) θ := by
  have h := ((((hasDerivAt_vHatD m θ).const_mul m.i0).neg.sub_const (m.Qhat m.θs)).sub
    (((hasDerivAt_id θ).sub_const m.θs).const_mul (m.dQhat m.θs))).div_const m.ω0
  convert h using 1
  · funext θ
    simp [Model.W, Model.Qhat]
  · simp only [Model.gradW, Model.dQhat]
    ring

/-- `∇²W(θ) = ∇²Q̂_f(θ)/ω₀`. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_gradW (m : Model) (θ : ℝ) :
    HasDerivAt m.gradW (m.ddQhat θ / m.ω0) θ := by
  have h := ((((((Real.hasDerivAt_cos θ).const_mul (m.a * m.μ * m.ustar)).neg.sub
    ((Real.hasDerivAt_sin θ).const_mul (m.b * m.μ * m.ustar))).div_const m.D).const_mul
      m.i0).neg.sub_const (m.dQhat m.θs)).div_const m.ω0
  convert h using 1
  · funext θ
    simp [Model.gradW, Model.dQhat, Model.dvD]
  · simp only [Model.ddQhat]
    ring

/-- `|dv̂/dθ|² = μ² u*²/|1 + Z_s Y_f|²`. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem dv_sq (m : Model) (hD : m.D ≠ 0) (θ : ℝ) :
    m.dvD (Real.cos θ) (Real.sin θ) ^ 2 + m.dvQ (Real.cos θ) (Real.sin θ) ^ 2 =
      m.μ ^ 2 * m.ustar ^ 2 / m.D := by
  have h := Real.sin_sq_add_cos_sq θ
  simp only [Model.dvD, Model.dvQ]
  field_simp
  simp only [Model.D]
  linear_combination (m.μ ^ 2 * m.ustar ^ 2 * (m.a ^ 2 + m.b ^ 2)) * h

/-- `|dî/dθ|² = μ² u*² |Y_f|²/|1 + Z_s Y_f|²`. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem dj_sq (m : Model) (hD : m.D ≠ 0) (θ : ℝ) :
    m.djD (Real.cos θ) (Real.sin θ) ^ 2 + m.djQ (Real.cos θ) (Real.sin θ) ^ 2 =
      m.μ ^ 2 * m.ustar ^ 2 * (m.Gf ^ 2 + m.ω0 ^ 2 * m.Cf ^ 2) / m.D := by
  have h := dv_sq m hD θ
  simp only [Model.djD, Model.djQ]
  have e : m.μ ^ 2 * m.ustar ^ 2 * (m.Gf ^ 2 + m.ω0 ^ 2 * m.Cf ^ 2) / m.D =
      (m.Gf ^ 2 + m.ω0 ^ 2 * m.Cf ^ 2) * (m.μ ^ 2 * m.ustar ^ 2 / m.D) := by ring
  rw [e, ← h]
  ring


/-! ## Equilibria and energy balance -/

/-- Every `θ_dq` with `η ∇W(θ_dq) = 0` (equivalently `P̂_f(θ_dq) = P̂_f(θ*_dq)`, by
`eta_mul_gradW`) gives an equilibrium `(θ_dq, u*, î(θ_dq), v̂(θ_dq))`. Static evidence on the
model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_eq_zero_of_gradW_eq_zero (m : Model) (hD : m.D ≠ 0)
    {θ : ℝ} (h : m.η * m.gradW θ = 0) :
    m.field (WithLp.toLp 2 ![θ, m.ustar, m.iHatD θ, m.iHatQ θ, m.vHatD θ, m.vHatQ θ]) = 0 := by
  have hd := steady_d m hD (Real.cos θ) (Real.sin θ)
  have hq := steady_q m hD (Real.cos θ) (Real.sin θ)
  ext i
  fin_cases i
  · simp [Model.field, Model.ω0]
  · simp only [Model.field, Model.idc, Model.ixHat, Transform.parkQ, PiLp.toLp_apply,
      PiLp.zero_apply, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linear_combination (-1 / m.Cdc) * h
  · simp [Model.field]
    left
    linear_combination hd
  · simp [Model.field]
    left
    linear_combination hq
  · simp [Model.field, Model.jD]
  · simp [Model.field, Model.jQ]

/-- The operating point is an equilibrium. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem field_point (m : Model) (hD : m.D ≠ 0) :
    m.field m.point = 0 :=
  field_eq_zero_of_gradW_eq_zero m hD (by simp [Model.gradW])

/-- Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem energy_differentiable (m : Model) :
    Differentiable ℝ m.energy := by
  have h := fun j : Fin 6 => (PiLp.proj 2 (fun _ : Fin 6 => ℝ) j : State 6 →L[ℝ] ℝ).differentiable
  have h0 : Differentiable ℝ (fun x : State 6 => x 0) := h 0
  have h1 : Differentiable ℝ (fun x : State 6 => x 1) := h 1
  have h2 : Differentiable ℝ (fun x : State 6 => x 2) := h 2
  have h3 : Differentiable ℝ (fun x : State 6 => x 3) := h 3
  have h4 : Differentiable ℝ (fun x : State 6 => x 4) := h 4
  have h5 : Differentiable ℝ (fun x : State 6 => x 5) := h 5
  unfold Model.energy Model.W Model.Qhat
  simp only [Model.iHatD, Model.iHatQ, Model.vHatD, Model.vHatQ, Model.jD, Model.jQ, Model.vD,
    Model.vQ]
  fun_prop

/-- The derivative of the energy. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem fderiv_energy (m : Model) (x v : State 6) :
    fderiv ℝ m.energy x v =
      m.Cdc * (x 1 - m.ustar) * v 1 + m.gradW (x 0) * v 0 +
        m.Ls * ((x 2 - m.iHatD (x 0)) * (v 2 - m.djD (Real.cos (x 0)) (Real.sin (x 0)) * v 0) +
          (x 3 - m.iHatQ (x 0)) * (v 3 - m.djQ (Real.cos (x 0)) (Real.sin (x 0)) * v 0)) +
        m.Cf * ((x 4 - m.vHatD (x 0)) * (v 4 - m.dvD (Real.cos (x 0)) (Real.sin (x 0)) * v 0) +
          (x 5 - m.vHatQ (x 0)) * (v 5 - m.dvQ (Real.cos (x 0)) (Real.sin (x 0)) * v 0)) := by
  apply Dynamics.fderiv_apply_eq_of_hasDerivAt_line ((energy_differentiable m) x)
  have hlin : ∀ j : Fin 6, HasDerivAt (fun t : ℝ => x j + t * v j) (v j) 0 := fun j => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v j)).const_add (x j)
  have hθ := hlin 0
  have hW := (hasDerivAt_W m (x 0)).comp_of_eq (0 : ℝ) hθ (by simp)
  have hjD := (hasDerivAt_iHatD m (x 0)).comp_of_eq (0 : ℝ) hθ (by simp)
  have hjQ := (hasDerivAt_iHatQ m (x 0)).comp_of_eq (0 : ℝ) hθ (by simp)
  have hvD := (hasDerivAt_vHatD m (x 0)).comp_of_eq (0 : ℝ) hθ (by simp)
  have hvQ := (hasDerivAt_vHatQ m (x 0)).comp_of_eq (0 : ℝ) hθ (by simp)
  have h1 := ((hlin 1).sub_const m.ustar).pow 2 |>.const_mul (m.Cdc / 2)
  have h3 := ((((hlin 2).sub hjD).pow 2).add (((hlin 3).sub hjQ).pow 2)).const_mul (m.Ls / 2)
  have h4 := ((((hlin 4).sub hvD).pow 2).add (((hlin 5).sub hvQ).pow 2)).const_mul (m.Cf / 2)
  have h := ((h1.add hW).add h3).add h4
  have e : (fun t : ℝ => m.energy (x + t • v)) = fun t =>
      m.Cdc / 2 * (x 1 + t * v 1 - m.ustar) ^ 2 + m.W (x 0 + t * v 0) +
        m.Ls / 2 * ((x 2 + t * v 2 - m.iHatD (x 0 + t * v 0)) ^ 2 +
          (x 3 + t * v 3 - m.iHatQ (x 0 + t * v 0)) ^ 2) +
        m.Cf / 2 * ((x 4 + t * v 4 - m.vHatD (x 0 + t * v 0)) ^ 2 +
          (x 5 + t * v 5 - m.vHatQ (x 0 + t * v 0)) ^ 2) := by
    funext t
    simp [Model.energy]
  rw [e]
  convert h using 1
  · funext t
    simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Function.comp_apply]
  · simp
    ring

/-- **The energy balance of the weak-grid loop** (the stiff-grid appendix balance with the bus
capacitor): `dH/dt = −(G_dc+K_p) ũ² − R_s ‖ĩ‖² − G_f ‖ṽ‖² − η ũ (L_s ĩᵀ î' + C_f ṽᵀ v̂')`,
`ĩ = i − î(θ)`, `ṽ = v − v̂(θ)`. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem energy_lie (m : Model) (hD : m.D ≠ 0) (hL : m.Ls ≠ 0)
    (hC : m.Cdc ≠ 0) (hCf : m.Cf ≠ 0) (x : State 6) :
    fderiv ℝ m.energy x (m.field x) =
      -(m.Gdc + m.Kp) * (x 1 - m.ustar) ^ 2 -
        m.Rs * ((x 2 - m.iHatD (x 0)) ^ 2 + (x 3 - m.iHatQ (x 0)) ^ 2) -
        m.Gf * ((x 4 - m.vHatD (x 0)) ^ 2 + (x 5 - m.vHatQ (x 0)) ^ 2) -
        m.η * (x 1 - m.ustar) *
          (m.Ls * ((x 2 - m.iHatD (x 0)) * m.djD (Real.cos (x 0)) (Real.sin (x 0)) +
              (x 3 - m.iHatQ (x 0)) * m.djQ (Real.cos (x 0)) (Real.sin (x 0))) +
            m.Cf * ((x 4 - m.vHatD (x 0)) * m.dvD (Real.cos (x 0)) (Real.sin (x 0)) +
              (x 5 - m.vHatQ (x 0)) * m.dvQ (Real.cos (x 0)) (Real.sin (x 0)))) := by
  rw [fderiv_energy]
  have hd := steady_d m hD (Real.cos (x 0)) (Real.sin (x 0))
  have hq := steady_q m hD (Real.cos (x 0)) (Real.sin (x 0))
  have hJd : m.iHatD (x 0) + (m.Gf * m.vHatD (x 0) - m.ω0 * m.Cf * m.vHatQ (x 0)) = 0 := by
    simp only [Model.iHatD, Model.jD]
    ring
  have hJq : m.iHatQ (x 0) + (m.ω0 * m.Cf * m.vHatD (x 0) + m.Gf * m.vHatQ (x 0)) + m.i0 = 0 := by
    simp only [Model.iHatQ, Model.jQ]
    ring
  have hF0 : m.field x 0 = m.η * x 1 - m.ω0 := rfl
  have hF1 : m.Cdc * m.field x 1 = -m.Gdc * x 1 + m.idc x +
      m.μ * (-Real.sin (x 0) * x 2 + Real.cos (x 0) * x 3) := by
    rw [show m.field x 1 = (-m.Gdc * x 1 + m.idc x +
      m.μ * (-Real.sin (x 0) * x 2 + Real.cos (x 0) * x 3)) / m.Cdc from rfl]
    field_simp
  have hF2 : m.Ls * m.field x 2 = -(m.Rs * x 2 - m.ω0 * m.Ls * x 3) + x 4 -
      m.μ * (-Real.sin (x 0)) * x 1 := by
    rw [show m.field x 2 = (-(m.Rs * x 2 - m.ω0 * m.Ls * x 3) + x 4 -
      m.μ * (-Real.sin (x 0)) * x 1) / m.Ls from rfl]
    field_simp
  have hF3 : m.Ls * m.field x 3 = -(m.ω0 * m.Ls * x 2 + m.Rs * x 3) + x 5 -
      m.μ * Real.cos (x 0) * x 1 := by
    rw [show m.field x 3 = (-(m.ω0 * m.Ls * x 2 + m.Rs * x 3) + x 5 -
      m.μ * Real.cos (x 0) * x 1) / m.Ls from rfl]
    field_simp
  have hF4 : m.Cf * m.field x 4 = -(m.Gf * x 4 - m.ω0 * m.Cf * x 5) - x 2 := by
    rw [show m.field x 4 = (-(m.Gf * x 4 - m.ω0 * m.Cf * x 5) - x 2) / m.Cf from rfl]
    field_simp
  have hF5 : m.Cf * m.field x 5 = -(m.ω0 * m.Cf * x 4 + m.Gf * x 5) - x 3 - m.i0 := by
    rw [show m.field x 5 = (-(m.ω0 * m.Cf * x 4 + m.Gf * x 5) - x 3 - m.i0) / m.Cf from rfl]
    field_simp
  simp only [Model.idc, Model.ixHat, Transform.parkQ] at hF1
  simp only [Model.ω0] at hF0 hF2 hF3 hF4 hF5 hd hq hJd hJq ⊢
  linear_combination
    (m.gradW (x 0) - m.Ls * ((x 2 - m.iHatD (x 0)) * m.djD (Real.cos (x 0)) (Real.sin (x 0)) +
        (x 3 - m.iHatQ (x 0)) * m.djQ (Real.cos (x 0)) (Real.sin (x 0))) -
      m.Cf * ((x 4 - m.vHatD (x 0)) * m.dvD (Real.cos (x 0)) (Real.sin (x 0)) +
        (x 5 - m.vHatQ (x 0)) * m.dvQ (Real.cos (x 0)) (Real.sin (x 0)))) * hF0 +
    (x 1 - m.ustar) * hF1 + (x 2 - m.iHatD (x 0)) * hF2 + (x 3 - m.iHatQ (x 0)) * hF3 +
    (x 4 - m.vHatD (x 0)) * hF4 + (x 5 - m.vHatQ (x 0)) * hF5 +
    (x 2 - m.iHatD (x 0)) * hd + (x 3 - m.iHatQ (x 0)) * hq -
    (x 4 - m.vHatD (x 0)) * hJd - (x 5 - m.vHatQ (x 0)) * hJq


@[tmio T, powerlib_foundation] private theorem quad_le {R B e1 e2 p1 p2 : ℝ} (hR : 0 < R) :
    -R * (e1 ^ 2 + e2 ^ 2) - B * (e1 * p1 + e2 * p2) ≤ B ^ 2 * (p1 ^ 2 + p2 ^ 2) / (4 * R) := by
  have key : B ^ 2 * (p1 ^ 2 + p2 ^ 2) / (4 * R) - (-R * (e1 ^ 2 + e2 ^ 2) -
      B * (e1 * p1 + e2 * p2)) = ((2 * R * e1 + B * p1) ^ 2 + (2 * R * e2 + B * p2) ^ 2) /
        (4 * R) := by
    field_simp
    ring
  have : 0 ≤ ((2 * R * e1 + B * p1) ^ 2 + (2 * R * e2 + B * p2) ^ 2) / (4 * R) := by positivity
  linarith

/-- With `R_s, G_f > 0`, `dH/dt ≤ −margin ũ²`. An equivalent form of the damping requirement. -/
@[tmio M, powerlib_domain] theorem energy_lie_le (m : Model) (hR : 0 < m.Rs) (hL : 0 < m.Ls)
    (hC : m.Cdc ≠ 0) (hCf : 0 < m.Cf) (hGf : 0 < m.Gf) (x : State 6) :
    fderiv ℝ m.energy x (m.field x) ≤ -m.margin * (x 1 - m.ustar) ^ 2 := by
  have hD := D_pos m hR hL hCf hGf
  rw [energy_lie m hD.ne' hL.ne' hC hCf.ne']
  have h1 := quad_le (R := m.Rs) (B := m.η * (x 1 - m.ustar) * m.Ls) (e1 := x 2 - m.iHatD (x 0))
    (e2 := x 3 - m.iHatQ (x 0)) (p1 := m.djD (Real.cos (x 0)) (Real.sin (x 0)))
    (p2 := m.djQ (Real.cos (x 0)) (Real.sin (x 0))) hR
  have h2 := quad_le (R := m.Gf) (B := m.η * (x 1 - m.ustar) * m.Cf)
    (e1 := x 4 - m.vHatD (x 0)) (e2 := x 5 - m.vHatQ (x 0))
    (p1 := m.dvD (Real.cos (x 0)) (Real.sin (x 0)))
    (p2 := m.dvQ (Real.cos (x 0)) (Real.sin (x 0))) hGf
  rw [dj_sq m hD.ne'] at h1
  rw [dv_sq m hD.ne'] at h2
  have e : -(m.Gdc + m.Kp) * (x 1 - m.ustar) ^ 2 +
      (m.η * (x 1 - m.ustar) * m.Ls) ^ 2 *
        (m.μ ^ 2 * m.ustar ^ 2 * (m.Gf ^ 2 + m.ω0 ^ 2 * m.Cf ^ 2) / m.D) / (4 * m.Rs) +
      (m.η * (x 1 - m.ustar) * m.Cf) ^ 2 * (m.μ ^ 2 * m.ustar ^ 2 / m.D) / (4 * m.Gf) =
      -m.margin * (x 1 - m.ustar) ^ 2 := by
    unfold Model.margin
    field_simp
    ring
  nlinarith


/-- The derivatives of the internal models solve the differentiated inductor rows. Static
evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem steady_d' (m : Model) (hD : m.D ≠ 0) (c s : ℝ) :
    -(m.Rs * m.djD c s - m.ω0 * m.Ls * m.djQ c s) + m.dvD c s + m.μ * c * m.ustar = 0 := by
  simp only [Model.djD, Model.djQ, Model.dvD, Model.dvQ]
  field_simp
  simp only [Model.D, Model.a, Model.b]
  ring

/-- Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem steady_q' (m : Model) (hD : m.D ≠ 0) (c s : ℝ) :
    -(m.ω0 * m.Ls * m.djD c s + m.Rs * m.djQ c s) + m.dvQ c s + m.μ * s * m.ustar = 0 := by
  simp only [Model.djD, Model.djQ, Model.dvD, Model.dvQ]
  field_simp
  simp only [Model.D, Model.a, Model.b]
  ring

/-! ## Linearization at the operating point -/

namespace Model
variable (m : Model)

/-- `î_d'(θ*_dq)`. -/
abbrev pD : ℝ := m.djD (Real.cos m.θs) (Real.sin m.θs)
/-- `î_q'(θ*_dq)`. -/
abbrev pQ : ℝ := m.djQ (Real.cos m.θs) (Real.sin m.θs)
/-- `v̂_d'(θ*_dq)`. -/
abbrev qD : ℝ := m.dvD (Real.cos m.θs) (Real.sin m.θs)
/-- `v̂_q'(θ*_dq)`. -/
abbrev qQ : ℝ := m.dvQ (Real.cos m.θs) (Real.sin m.θs)

/-- The Jacobian at the operating point (`hasFDerivAt_field_point`). -/
def jac : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, m.η, 0, 0, 0, 0;
     (-(m.μ * (-Real.sin m.θs * m.pD + Real.cos m.θs * m.pQ)) - m.η * m.kW) / m.Cdc,
       -(m.Gdc + m.Kp) / m.Cdc, -(m.μ * Real.sin m.θs) / m.Cdc, m.μ * Real.cos m.θs / m.Cdc,
       0, 0;
     m.μ * m.ustar * Real.cos m.θs / m.Ls, m.μ * Real.sin m.θs / m.Ls, -m.Rs / m.Ls, m.ω0,
       1 / m.Ls, 0;
     m.μ * m.ustar * Real.sin m.θs / m.Ls, -(m.μ * Real.cos m.θs) / m.Ls, -m.ω0,
       -m.Rs / m.Ls, 0, 1 / m.Ls;
     0, 0, -1 / m.Cf, 0, -m.Gf / m.Cf, m.ω0;
     0, 0, 0, -1 / m.Cf, -m.ω0, -m.Gf / m.Cf]

/-- The quadratic part of the energy at the operating point as a matrix:
`W'' δθ² + C_dc δu² + L_s ‖δi − î' δθ‖² + C_f ‖δv − v̂' δθ‖²`. -/
def lyap : Matrix (Fin 6) (Fin 6) ℝ :=
  !![m.kW + m.Ls * (m.pD ^ 2 + m.pQ ^ 2) + m.Cf * (m.qD ^ 2 + m.qQ ^ 2), 0,
       -(m.Ls * m.pD), -(m.Ls * m.pQ), -(m.Cf * m.qD), -(m.Cf * m.qQ);
     0, m.Cdc, 0, 0, 0, 0;
     -(m.Ls * m.pD), 0, m.Ls, 0, 0, 0;
     -(m.Ls * m.pQ), 0, 0, m.Ls, 0, 0;
     -(m.Cf * m.qD), 0, 0, 0, m.Cf, 0;
     -(m.Cf * m.qQ), 0, 0, 0, 0, m.Cf]

end Model

@[tmio M, powerlib_domain] private theorem lyap_symm (m : Model) : m.lyapᵀ = m.lyap := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Model.lyap]

/-- The Lyapunov form. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem lyap_form (m : Model) (w : Fin 6 → ℝ) :
    w ⬝ᵥ (m.lyap *ᵥ w) = m.kW * w 0 ^ 2 + m.Cdc * w 1 ^ 2 +
      m.Ls * ((w 2 - m.pD * w 0) ^ 2 + (w 3 - m.pQ * w 0) ^ 2) +
      m.Cf * ((w 4 - m.qD * w 0) ^ 2 + (w 5 - m.qQ * w 0) ^ 2) := by
  simp [Model.lyap, Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  ring

/-- **Dissipation of the linearization**: `wᵀ P J w = −(g δu² + R_s ‖ẽ_i‖² + G_f ‖ẽ_v‖² +
η δu (L_s ẽ_iᵀ î' + C_f ẽ_vᵀ v̂'))`, `ẽ_i = δi − î' δθ`, `ẽ_v = δv − v̂' δθ`. Static evidence on
the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem lyap_jac (m : Model) (hD : m.D ≠ 0) (hL : m.Ls ≠ 0)
    (hC : m.Cdc ≠ 0) (hCf : m.Cf ≠ 0) (w : Fin 6 → ℝ) :
    w ⬝ᵥ (m.lyap *ᵥ (m.jac *ᵥ w)) =
      -((m.Gdc + m.Kp) * w 1 ^ 2 +
        m.Rs * ((w 2 - m.pD * w 0) ^ 2 + (w 3 - m.pQ * w 0) ^ 2) +
        m.Gf * ((w 4 - m.qD * w 0) ^ 2 + (w 5 - m.qQ * w 0) ^ 2) +
        m.η * w 1 * (m.Ls * ((w 2 - m.pD * w 0) * m.pD + (w 3 - m.pQ * w 0) * m.pQ) +
          m.Cf * ((w 4 - m.qD * w 0) * m.qD + (w 5 - m.qQ * w 0) * m.qQ))) := by
  have r0 := steady_d' m hD (Real.cos m.θs) (Real.sin m.θs)
  have r1 := steady_q' m hD (Real.cos m.θs) (Real.sin m.θs)
  have r2 : -(m.Gf * m.qD - m.ω0 * m.Cf * m.qQ) - m.pD = 0 := by
    simp only [Model.pD, Model.djD]
    ring
  have r3 : -(m.ω0 * m.Cf * m.qD + m.Gf * m.qQ) - m.pQ = 0 := by
    simp only [Model.pQ, Model.djQ]
    ring
  simp only [Model.pD, Model.pQ, Model.qD, Model.qQ] at r2 r3
  simp [Model.lyap, Model.jac, Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  field_simp
  linear_combination (w 0 * (w 2 - m.pD * w 0)) * r0 + (w 0 * (w 3 - m.pQ * w 0)) * r1 +
    (w 0 * (w 4 - m.qD * w 0)) * r2 + (w 0 * (w 5 - m.qQ * w 0)) * r3


/-- With `R_s, G_f > 0`, the dissipation of the linearization is `≤ −margin δu²`. Static
evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem lyap_jac_le (m : Model) (hR : 0 < m.Rs) (hL : 0 < m.Ls)
    (hC : m.Cdc ≠ 0) (hCf : 0 < m.Cf) (hGf : 0 < m.Gf) (w : Fin 6 → ℝ) :
    w ⬝ᵥ (m.lyap *ᵥ (m.jac *ᵥ w)) ≤ -m.margin * w 1 ^ 2 := by
  have hD := D_pos m hR hL hCf hGf
  rw [lyap_jac m hD.ne' hL.ne' hC hCf.ne']
  have h1 := quad_le (R := m.Rs) (B := m.η * w 1 * m.Ls) (e1 := w 2 - m.pD * w 0)
    (e2 := w 3 - m.pQ * w 0) (p1 := m.pD) (p2 := m.pQ) hR
  have h2 := quad_le (R := m.Gf) (B := m.η * w 1 * m.Cf) (e1 := w 4 - m.qD * w 0)
    (e2 := w 5 - m.qQ * w 0) (p1 := m.qD) (p2 := m.qQ) hGf
  rw [dj_sq m hD.ne'] at h1
  rw [dv_sq m hD.ne'] at h2
  have e : -(m.Gdc + m.Kp) * w 1 ^ 2 +
      (m.η * w 1 * m.Ls) ^ 2 *
        (m.μ ^ 2 * m.ustar ^ 2 * (m.Gf ^ 2 + m.ω0 ^ 2 * m.Cf ^ 2) / m.D) / (4 * m.Rs) +
      (m.η * w 1 * m.Cf) ^ 2 * (m.μ ^ 2 * m.ustar ^ 2 / m.D) / (4 * m.Gf) =
      -m.margin * w 1 ^ 2 := by
    unfold Model.margin
    field_simp
    ring
  nlinarith

@[tmio T, powerlib_foundation] private theorem sq_add_sq_eq_zero' {x y : ℝ}
    (h : x ^ 2 + y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  have hx : x ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx,
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy⟩

/-- **The linearization is Hurwitz** under the weak-grid damping condition `margin > 0`, a
strictly convex potential at the operating angle (`W''(θ*_dq) > 0`), `η ≠ 0` and
`C_dc, L_s, R_s, C_f, G_f > 0`: the energy-eigenvector argument
(`Criteria.re_neg_of_lyapunov_observable` with `lyap`); at `Re λ ≥ 0` the dissipation forces
`δu = 0`, `δi = î' δθ`, `δv = v̂' δθ`, and the DC row then forces `η W'' δθ = 0`. Static evidence
on the model, not a connection conclusion. -/
@[tmio TM, powerlib_domain] theorem jac_isHurwitz (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls)
    (hR : 0 < m.Rs) (hCf : 0 < m.Cf) (hGf : 0 < m.Gf) (hη : m.η ≠ 0) (hk : 0 < m.kW)
    (hδ : 0 < m.margin) : LinearSystems.IsHurwitz m.jac := by
  have hD := D_pos m hR hL hCf hGf
  -- zero dissipation forces `δu = 0`, `δi = î' δθ`, `δv = v̂' δθ`
  have hzero : ∀ w : Fin 6 → ℝ, w ⬝ᵥ (m.lyap *ᵥ (m.jac *ᵥ w)) = 0 →
      w 1 = 0 ∧ w 2 = m.pD * w 0 ∧ w 3 = m.pQ * w 0 ∧ w 4 = m.qD * w 0 ∧ w 5 = m.qQ * w 0 := by
    intro w hw
    have hle := lyap_jac_le m hR hL hC.ne' hCf hGf w
    rw [hw] at hle
    have h1 : w 1 = 0 := by
      have h2 : w 1 ^ 2 ≤ 0 := by
        by_contra hc
        push Not at hc
        have := mul_pos hδ hc
        linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h2 (sq_nonneg _))
    have hl := hw
    rw [lyap_jac m hD.ne' hL.ne' hC.ne' hCf.ne' w, h1] at hl
    have a1 : 0 ≤ m.Rs * ((w 2 - m.pD * w 0) ^ 2 + (w 3 - m.pQ * w 0) ^ 2) := by positivity
    have a2 : 0 ≤ m.Gf * ((w 4 - m.qD * w 0) ^ 2 + (w 5 - m.qQ * w 0) ^ 2) := by positivity
    have s1 : (w 2 - m.pD * w 0) ^ 2 + (w 3 - m.pQ * w 0) ^ 2 = 0 := by
      have : m.Rs * ((w 2 - m.pD * w 0) ^ 2 + (w 3 - m.pQ * w 0) ^ 2) = 0 := by
        simp only [mul_zero, zero_mul, zero_add, pow_two] at hl
        nlinarith
      exact (mul_eq_zero.mp this).resolve_left hR.ne'
    have s2 : (w 4 - m.qD * w 0) ^ 2 + (w 5 - m.qQ * w 0) ^ 2 = 0 := by
      have : m.Gf * ((w 4 - m.qD * w 0) ^ 2 + (w 5 - m.qQ * w 0) ^ 2) = 0 := by
        simp only [mul_zero, zero_mul, zero_add, pow_two] at hl
        nlinarith
      exact (mul_eq_zero.mp this).resolve_left hGf.ne'
    obtain ⟨e2, e3⟩ := sq_add_sq_eq_zero' s1
    obtain ⟨e4, e5⟩ := sq_add_sq_eq_zero' s2
    exact ⟨h1, by linarith, by linarith, by linarith, by linarith⟩
  -- on that set the DC row is `−η W'' δθ / C_dc`
  have hrow : ∀ w : Fin 6 → ℝ, w 1 = 0 → w 2 = m.pD * w 0 → w 3 = m.pQ * w 0 →
      (m.jac *ᵥ w) 1 = -(m.η * m.kW * w 0) / m.Cdc := by
    intro w h1 h2 h3
    simp only [Model.jac, Matrix.mulVec, dotProduct, Fin.sum_univ_six, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    simp [h1, h2, h3]
    field_simp
    ring
  have hkη : m.η * m.kW ≠ 0 := mul_ne_zero hη hk.ne'
  intro lam v hv hev
  rw [neg_zero]
  refine Criteria.re_neg_of_lyapunov_observable (lyap_symm m) (fun w => ?_) (fun w => ?_)
    (fun x y a b ha hb _ hda hdb => ?_) hv hev
  · rw [lyap_form]
    positivity
  · exact (lyap_jac_le m hR hL hC.ne' hCf hGf w).trans (by nlinarith [sq_nonneg (w 1)])
  · obtain ⟨a1, a2, a3, a4, a5⟩ := hzero a hda
    obtain ⟨b1, b2, b3, b4, b5⟩ := hzero b hdb
    have ra := congrFun ha 1
    have rb := congrFun hb 1
    rw [hrow a a1 a2 a3] at ra
    rw [hrow b b1 b2 b3] at rb
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, a1, b1, mul_zero,
      sub_zero, add_zero] at ra rb
    have a0 : a 0 = 0 := by
      rw [div_eq_zero_iff, or_iff_left hC.ne', neg_eq_zero] at ra
      exact (mul_eq_zero.mp ra).resolve_left hkη
    have b0 : b 0 = 0 := by
      rw [div_eq_zero_iff, or_iff_left hC.ne', neg_eq_zero] at rb
      exact (mul_eq_zero.mp rb).resolve_left hkη
    constructor
    · funext j
      fin_cases j <;> simp [a0, a1, a2, a3, a4, a5]
    · funext j
      fin_cases j <;> simp [b0, b1, b2, b3, b4, b5]


/-- Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_contDiff (m : Model) : ContDiff ℝ 1 m.field := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i <;>
    simp [Model.field, Model.idc, Model.ixHat, Transform.parkQ, Model.gradW, Model.dQhat,
      Model.dvD, Model.jD, Model.jQ, Model.vD, Model.vQ] <;> fun_prop

/-- Entries of the Jacobian applied to a vector. Static evidence on the model, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem jac_apply (m : Model) (v : State 6) :
    (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℝ) m.jac v) 0 = m.η * v 1 ∧
    (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℝ) m.jac v) 1 =
      (-(m.μ * (-Real.sin m.θs * m.pD + Real.cos m.θs * m.pQ)) - m.η * m.kW) / m.Cdc * v 0 -
        (m.Gdc + m.Kp) / m.Cdc * v 1 - m.μ * Real.sin m.θs / m.Cdc * v 2 +
        m.μ * Real.cos m.θs / m.Cdc * v 3 ∧
    (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℝ) m.jac v) 2 =
      m.μ * m.ustar * Real.cos m.θs / m.Ls * v 0 + m.μ * Real.sin m.θs / m.Ls * v 1 -
        m.Rs / m.Ls * v 2 + m.ω0 * v 3 + 1 / m.Ls * v 4 ∧
    (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℝ) m.jac v) 3 =
      m.μ * m.ustar * Real.sin m.θs / m.Ls * v 0 - m.μ * Real.cos m.θs / m.Ls * v 1 -
        m.ω0 * v 2 - m.Rs / m.Ls * v 3 + 1 / m.Ls * v 5 ∧
    (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℝ) m.jac v) 4 =
      -1 / m.Cf * v 2 - m.Gf / m.Cf * v 4 + m.ω0 * v 5 ∧
    (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℝ) m.jac v) 5 =
      -1 / m.Cf * v 3 - m.ω0 * v 4 - m.Gf / m.Cf * v 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_six] <;>
    simp [Model.jac] <;> ring


/-- The derivative of the loop at the operating point is `jac`. Static evidence on the model,
not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_field_point (m : Model) (hL : m.Ls ≠ 0)
    (hC : m.Cdc ≠ 0) (hCf : m.Cf ≠ 0) :
    HasFDerivAt m.field (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℝ) m.jac) m.point := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have hp : ∀ k : Fin 6, HasFDerivAt (fun x : State 6 => x k)
      (PiLp.proj 2 (fun _ : Fin 6 => ℝ) k : State 6 →L[ℝ] ℝ) m.point :=
    fun k => (PiLp.proj 2 (fun _ : Fin 6 => ℝ) k : State 6 →L[ℝ] ℝ).hasFDerivAt
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  have h4 := hp 4
  have h5 := hp 5
  have hs := h0.sin
  have hc := h0.cos
  have hD := (hasDerivAt_iHatD m (m.point 0)).comp_hasFDerivAt m.point h0
  have hQ := (hasDerivAt_iHatQ m (m.point 0)).comp_hasFDerivAt m.point h0
  have hgW := (hasDerivAt_gradW m (m.point 0)).comp_hasFDerivAt m.point h0
  have p0 : m.point 0 = m.θs := by simp [Model.point]
  have p1 : m.point 1 = m.ustar := by simp [Model.point]
  have p2 : m.point 2 = m.iHatD m.θs := by simp [Model.point]
  have p3 : m.point 3 = m.iHatQ m.θs := by simp [Model.point]
  have j := jac_apply m
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
  · have h := (h1.const_mul m.η).sub_const m.ω0
    convert h using 1
    · funext y; simp [Model.field]
    · apply ContinuousLinearMap.ext; intro v
      simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply]
      rw [(j v).1]
      simp
  · have hix := ((hs.neg.mul hD).add (hc.mul hQ)).const_mul m.μ |>.neg
    have hidc :=
      ((((h1.sub_const m.ustar).const_mul (-m.Kp)).add_const
        (m.Gdc * m.ustar)).add hix).sub (hgW.const_mul m.η)
    have h := (((h1.const_mul (-m.Gdc)).add hidc).add
      (((hs.neg.mul h2).add (hc.mul h3)).const_mul m.μ)).mul_const m.Cdc⁻¹
    convert h using 1
    · funext y
      simp only [Model.field, Model.idc, Model.ixHat, Transform.parkQ, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply, Pi.neg_apply,
        Pi.mul_apply, Function.comp_apply, div_eq_mul_inv]
    · apply ContinuousLinearMap.ext; intro v
      simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply]
      rw [(j v).2.1]
      simp [p0, p2, p3, Model.kW]
      field_simp
      ring
  · have h := (((((h2.const_mul m.Rs).sub ((h3.const_mul m.ω0).const_mul m.Ls)).neg).add h4).sub
      ((hs.neg.const_mul m.μ).mul h1)).mul_const m.Ls⁻¹
    convert h using 1
    · funext y
      simp only [Model.field, PiLp.toLp_apply, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.mul_apply,
        div_eq_mul_inv]
      ring
    · apply ContinuousLinearMap.ext; intro v
      simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply]
      rw [(j v).2.2.1]
      simp [p0, p1]
      field_simp
      ring
  · have h := ((((((h2.const_mul m.ω0).const_mul m.Ls).add (h3.const_mul m.Rs)).neg).add h5).sub
      ((hc.const_mul m.μ).mul h1)).mul_const m.Ls⁻¹
    convert h using 1
    · funext y
      simp only [Model.field, PiLp.toLp_apply, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.mul_apply,
        div_eq_mul_inv]
      ring
    · apply ContinuousLinearMap.ext; intro v
      simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply]
      rw [(j v).2.2.2.1]
      simp [p0, p1]
      field_simp
      ring
  · have h := ((((h4.const_mul m.Gf).sub ((h5.const_mul m.ω0).const_mul m.Cf)).neg).sub
      h2).mul_const m.Cf⁻¹
    convert h using 1
    · funext y
      simp [Model.field, div_eq_mul_inv]
      exact Or.inl (by ring)
    · apply ContinuousLinearMap.ext; intro v
      simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply]
      rw [(j v).2.2.2.2.1]
      simp
      field_simp
      ring
  · have h := (((((h4.const_mul m.ω0).const_mul m.Cf).add (h5.const_mul m.Gf)).neg.sub
      h3).sub_const m.i0).mul_const m.Cf⁻¹
    convert h using 1
    · funext y
      simp [Model.field, div_eq_mul_inv]
      exact Or.inl (by ring)
    · apply ContinuousLinearMap.ext; intro v
      simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply]
      rw [(j v).2.2.2.2.2]
      simp
      field_simp
      ring


/-- The loop is `2π`-periodic in `θ_dq` (the field contains `∇W`, which is periodic, not the
tilted potential `W`). Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_add_two_pi (m : Model) (θ u id iq vd vq : ℝ) :
    m.field (WithLp.toLp 2 ![θ + 2 * Real.pi, u, id, iq, vd, vq]) =
      m.field (WithLp.toLp 2 ![θ, u, id, iq, vd, vq]) := by
  simp [Model.field, Model.idc, Model.ixHat, Transform.parkQ, Model.gradW, Model.dQhat,
    Model.iHatD, Model.iHatQ]

/-! ## Family -/

/-- Static requirements on weak-grid matching models. -/
inductive Requirement
  | physical
  | convex
  | concave
  | damped
  | matching

/-- Satisfaction of a requirement. -/
def Meets (m : Model) : Requirement → Prop
  | .physical => 0 < m.Cdc ∧ 0 < m.Ls ∧ 0 < m.Rs ∧ 0 < m.Cf ∧ 0 < m.Gf
  | .convex => 0 < m.kW
  | .concave => m.kW < 0
  | .damped => 0 < m.margin
  | .matching => m.η ≠ 0

/-- The translation (`Spectral.localTable`): Lyapunov, local asymptotic and local exponential
stability into `{physical, convex, damped, matching}`; passivity into nothing; every other
sentence into the whole, inconsistent, language. -/
abbrev translate : Sentence → Set Requirement :=
  Spectral.localTable {.physical, .convex, .damped, .matching}
    {.physical, .convex, .damped, .matching} Set.univ ∅

/-- The loop translated to the operating point. -/
def Model.translated (m : Model) (z : State 6) : State 6 := m.field (z + m.point)

/-- The weak-grid matching family. -/
def family : Family Model Requirement 6 0 :=
  ⟨fun m => Port.System.autonomous m.translated, Meets, translate⟩

/-- The weak-grid family is the family of the translated autonomous fields. -/
@[tmio M, powerlib_domain] theorem family_isAutonomous : family.IsAutonomous Model.translated :=
  fun _ => rfl

@[tmio TM, powerlib_domain] private theorem mem_den_flow {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.field m.point :=
  Spectral.mem_den_flow_iff_shift (f := Model.field) (pt := Model.point) family_isAutonomous

/-- **Local exponential stability of the weak-grid operating point** under `margin > 0`, a
strictly convex potential `W''(θ*_dq) > 0`, `η ≠ 0` and `C_dc, L_s, R_s, C_f, G_f > 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable (m : Model)
    (hC : 0 < m.Cdc) (hL : 0 < m.Ls) (hR : 0 < m.Rs) (hCf : 0 < m.Cf) (hGf : 0 < m.Gf)
    (hη : m.η ≠ 0) (hk : 0 < m.kW) (hδ : 0 < m.margin) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% mem_den_flow)]
  change LocallyExponentiallyStable m.field m.point
  have hD := D_pos m hR hL hCf hGf
  exact hurwitz_linearization_locally_exponentially_stable m.jac (field_contDiff m)
    (field_point m hD.ne') (hasFDerivAt_field_point m hL.ne' hC.ne' hCf.ne').fderiv
    (jac_isHurwitz m hC hL hR hCf hGf hη hk hδ)

/-- The whole requirement language is inconsistent. -/
@[tmio M, powerlib_domain] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of .convex .concave fun m h1 h2 => ?_
  have h1 : 0 < m.kW := h1
  have h2 : m.kW < 0 := h2
  linarith

/-- Every translation of the weak-grid family is sound. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.chain_le_semantics_of_localTable_same (fun _ => rfl) realize_univ
    (fun m hm => ?_) (fun m hm => Spectral.realize_univ_subset_of_eq_empty realize_univ _ hm)
    family_isAutonomous.den_passive
  rw [(connection_proof% TMIO.mem_realize)] at hm
  obtain ⟨hC, hL, hR, hCf, hGf⟩ : Meets m .physical := hm .physical (by simp)
  exact mem_den_locallyExponentiallyStable m hC hL hR hCf hGf (hm .matching (by simp))
    (hm .convex (by simp)) (hm .damped (by simp))

/-- **Boundary**: no weak-grid loop is globally asymptotically stable on `ℝ⁶`
(`2π`-periodicity gives a second equilibrium whenever the operating point is one). -/
@[tmio TM, powerlib_domain] theorem not_mem_den_globallyAsymptoticallyStable (m : Model) :
    connection% (m ∉ family.den (.flow .globallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% mem_den_flow)]
  intro h
  change Flow.GloballyAsymptoticallyStable _ _ at h
  refine Dynamics.not_globallyAsymptoticallyStable_of_equilibrium_ne
    (y := WithLp.toLp 2 ![m.θs + 2 * Real.pi, m.ustar, m.iHatD m.θs, m.iHatQ m.θs,
      m.vHatD m.θs, m.vHatQ m.θs]) ?_ ?_ h
  · rw [field_add_two_pi]
    exact h.1
  · intro he
    have h0 := congrArg (fun z : State 6 => z 0) he
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

end powerlib.GFM.Matching.WeakGrid
