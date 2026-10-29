import theorem.GFM.Matching.Matching
import theorem.Spectral.Global
import theorem.Criteria.Lyapunov
import theorem.Dynamics.Coordinates

/-! # Energy-shaping matching control on a stiff grid: what the "global stability condition" proves

The work-sync notes quote, as the global stability condition of matching control,
`(G_dc + K_p)/η² > L_s² μ² v*²/(4 R_s ‖Z_s‖²)`. This module formalizes the closed loop that
condition belongs to, its energy balance, and the stability conclusions that can be stated in
the sentence language, and records what the source's LaSalle argument does and does not give.

Model boundary.
* Averaged converter (no PWM or delay), DC capacitor `C_dc`, DC conductance `G_dc`, switching
  inductor `L_s` with resistance `R_s` (L filter, no LCL), connected to a stiff grid of amplitude
  `v₀` and frequency `ω₀ = η u*_dc`; no current or modulation limits, no PLL, constant `μ`.
  Directions as in the source: `i_s` flows from the grid into the converter, `i_dc` into the DC
  node.
* Analysis frame of the source: grid `dq` frame, `θ_dq = θ − θ_g`, `i_dq = R_{θ_g}ᵀ i_s`
  (`Z_s = R_s I + ω₀ L_s J`, `‖Z_s‖² = N = R_s² + ω₀² L_s²`). The stationary-frame model is
  non-autonomous (`θ_g = ω₀ t`) and is not formalized; the grid-frame model is the source's.
  State, in this order: `x = (θ_dq, u_dc, i_d, i_q) ∈ ℝ⁴` (`Model.field`):
  `θ_dq' = η u_dc − ω₀`, `C_dc u_dc' = −G_dc u_dc + i_dc(x) + μ (−sin θ_dq, cos θ_dq)ᵀ i_dq`,
  `L_s i_dq' = −Z_s i_dq + v₀ e₂ − μ (−sin θ_dq, cos θ_dq) u_dc`, with `i_dc` given by (18).
  Continuous time, autonomous. The operating point is `x* = (0, u*_dc, î_dq(0))`
  (`Model.point`, an equilibrium when `N ≠ 0`, `field_point`). Excluded: the power-tracking
  variant `S(θ_dq − θ*_dq)` with `μ = μ*`, direct angle control (24), the weak-grid controllers
  of §IV and the time-scale-separated pendulum (21).
* Parameter ranges: `C_dc, L_s, R_s > 0`; `G_dc`, `K_p`, `η`, `μ`, `u*_dc`, `v₀` real.

Source: work-sync `theory/T-dc-voltage-gfm.md` §1.2, `theory/T-gfm-control.md` §1.6,
`theory/papers/@arghir2020matching.md`; equations from the TPEL author version as listed above.

Provenance. Equations from C. Arghir, F. Dörfler, author version "Direct angle control and
energy-shaping techniques for grid-connected converters" of "The electronic realization of
synchronous machines: model matching, angle tracking, and energy shaping techniques", IEEE Trans.
Power Electron. 35(4) (2020) 4398–4410 (ETH Research Collection, `bare_jrnl.pdf`, text read):
the converter model (4), modulation `m_αβ = μ (−sin θ, cos θ)` (11), matching `θ' = η u_dc` (12),
the stiff grid `v_g = v₀ (−sin θ_g, cos θ_g)`, `θ_g' = ω₀` (Fig. 5), the internal model
`î_s = Z_s⁻¹ (v_g − μ u*_dc (−sin θ, cos θ))` (14), `î_x = −m_αβᵀ î_s` (15), the synchronization
potential `S = î_sᵀ L_s î_s / 2` (16)–(17), the control
`i_dc = −K_p (u_dc − u*_dc) + G_dc u*_dc + î_x(θ_dq) − η ∇S(θ_dq)` (18), `η∇S = (μ v₀ ω₀ L_s/‖Z_s‖²)
sin θ_dq` (20), the energy `H = C_dc ũ_dc²/2 + S(θ_dq) + ĩ_dqᵀ L_s ĩ_dq/2` (22) and the appendix
("Energy-based stabilization of the eSM"): error system (42),
`dH/dt = −(G_dc+K_p) ũ_dc² − ĩᵀR_s ĩ − ĩᵀ T(θ_dq) ũ_dc`, `T = μ ω₀ L_s Z_s⁻¹ (cos θ_dq, sin θ_dq)`,
and the condition `(G_dc+K_p)/η² > L_s²μ²u*_dc²/(4R_s‖Z_s‖²)`, from which the source concludes by
LaSalle that all trajectories converge to the set `{ũ_dc = 0, ∇S(θ_dq) = 0, ĩ_dq = 0}`. None of
these equations is written in the work-sync notes, which contain only the condition.

Results.
* Static (source link): `potential_eq` (the potential is (16)), `potential_sub_potential_zero`
  (`S(θ) − S(0) = k (1 − cos θ)`, `k = L_s μ u* v₀/N`), `eta_mul_k` (`η ∇S` is the
  synchronizing term `κ sin θ` of (18), (20)), `field_point`, `field_add_two_pi`,
  `field_eq_zero_of_sin_eq_zero` (every `θ_dq ∈ πℤ` gives an equilibrium `(θ_dq, u*, î(θ_dq))`).
* Static (energy balance): `energy_lie` (the appendix formula for `dH/dt`, as a Lie derivative of
  `H − S(0)` along the closed-loop field), `energy_lie_le` (`dH/dt ≤ −margin ũ_dc²`, by completing
  the square with `‖T‖² = μ²ω₀²L_s²/N`), `margin_pos_iff` (for `η ≠ 0`, `margin > 0` is exactly the
  source's (and the note's) condition).

Family and connection conclusions.
* Family `family : Family Model Requirement 4 0`: the closed loop about `x*`, the family of the
  translated fields (`family_isAutonomous`). Requirements
  `physical` (`C_dc, L_s, R_s > 0`), `synchronizing` (`μ u* v₀ > 0`, so that `θ_dq = 0` is the
  minimum of `S`), `dissipative` (`margin ≥ 0`), `antiSynchronizing` (`μ u* v₀ < 0`), `damped`
  (`margin > 0`), `matching` (`η ≠ 0`). Lyapunov stability translates into
  `{physical, synchronizing, dissipative}`; local asymptotic and exponential stability into
  `{physical, synchronizing, damped, matching}`; passivity into nothing (exact); every other
  flow sentence into the whole, inconsistent, language (unavailable coverage). Connection
  results: `chain_le_semantics`, `exact_passive`,
  `mem_den_lyapunovStable` (the operating point is Lyapunov stable: `H − S(0)` is a local
  Lyapunov function on `|θ_dq| < 2π`), `not_mem_den_globallyAsymptoticallyStable`,
  `not_mem_den_globallyExponentiallyStable` (no model is globally asymptotically stable on `ℝ⁴`:
  `2π`-periodicity), hence `exact_globallyAsymptoticallyStable`,
  `exact_globallyExponentiallyStable` (both denotations are empty, as is the space of their
  translation).
* Linearization: `hasFDerivAt_field_point` (the Jacobian `jac` at `x*`), `jac_isHurwitz` (under
  `margin > 0`, `μ u* v₀ > 0`, `η ≠ 0`; eigenvector form of the energy argument), giving the
  connection results `mem_den_locallyExponentiallyStable` and
  `mem_den_locallyAsymptoticallyStable`.
* Trajectory level, in `theorem.GFM.Matching.LaSalle` (private implementation evidence: set
  attraction and regions of attraction are outside the sentence language; the generic tools are
  the foundation results of `theorem.Dynamics.LaSalle.Periodic`, LaSalle on the invariant cylinder
  `(cos θ_dq, sin θ_dq, u_dc, i_dq)` with the `C¹` LaSalle of `theorem.Dynamics.LaSalle.Basin`):
  `tendsto_equilibrium` (the source's LaSalle conclusion, also for the non-strict condition: with
  `margin ≥ 0`, `η ≠ 0`, `μ u* v₀ ≠ 0` every forward solution converges to one equilibrium
  `(j π, u*, î(j π))`, hence to `{ũ_dc = 0, ∇S = 0, ĩ_dq = 0}`, `tendsto_critical`),
  `exists_solution` (forward solutions exist on `[0, ∞)`), `basin` (with `μ u* v₀ > 0` the window
  `{|θ_dq| < π, H − S(0) < 2k}` below the saddle energy lies in the region of attraction of `x*`)
  and the boundary `not_tendsto_critical_of_eta_eq_zero` (`η ≠ 0` is necessary). Connection
  conclusions there: `mem_den_locallyAsymptoticallyStable_of_dissipative` (`margin ≥ 0` already
  gives local asymptotic stability) and `not_exact_locallyAsymptoticallyStable` (the local
  asymptotic translation of this family is sound but not exact: a `margin = 0` model).
  Without synchronizing torque (`μ u* v₀ = 0`, outside the source): with `margin > 0` every
  solution converges to one point of the circle of equilibria `(θ, u*, î(θ))` and the operating
  point is Lyapunov stable but not locally asymptotically stable
  (`mem_den_lyapunovStable_of_no_sync`, `not_mem_den_locallyAsymptoticallyStable_of_no_sync`;
  hence `not_exact_lyapunovStable`); with `margin = 0` and `μ ≠ 0` every solution still converges
  to an equilibrium; with `margin = 0` and `μ = 0` the DC error is conserved and the angle drifts
  (`mem_den_unstable_of_mu_eq_zero` for `η ≠ 0`). Decided: for `μ u* v₀ = 0` and `margin ≥ 0` the
  operating point is Lyapunov stable iff `margin > 0 ∨ μ ≠ 0 ∨ η = 0`
  (`mem_den_lyapunovStable_iff_of_no_sync`), and never locally asymptotically stable.

Corrections.
* The note's condition is the source's condition (`margin_pos_iff`), but it is not a global
  stability condition of the operating point: it makes `H` nonincreasing (dissipation in
  `(ũ_dc, ĩ_dq)` only), which gives Lyapunov stability of `θ_dq = 0` (with `μ u* v₀ > 0`),
  local exponential stability (with `η ≠ 0`, `mem_den_locallyExponentiallyStable`) and LaSalle
  convergence to `{ũ_dc = 0, ∇S = 0, ĩ_dq = 0}` (`theorem.GFM.Matching.LaSalle`). That set
  contains the saddle equilibria `θ_dq = π` (`field_eq_zero_of_sin_eq_zero`), and no point is
  globally asymptotically stable on `ℝ⁴` (`exact_globallyAsymptoticallyStable`).
* The note attributes the condition to "[[@arghir2020matching]] Theorem 3" inside a section
  headed "Arghir-Jouini-Dörfler 2018 Automatica"; in the author version it is an unnumbered
  appendix argument of the 2020 TPEL paper, and the Automatica closed-loop condition is a
  different inequality (`theorem.GFM.Matching.ClosedLoop`, `margin_pos_iff` there).
* Source typo (not in the notes): the caption of Fig. 7 writes the pendulum damping as
  `(C_dc + K_p)/η²`; from (21b) it is `(G_dc + K_p)/η²`.
-/

noncomputable section
namespace powerlib.GFM.Matching.MatchingStiffGrid
open powerlib.Dynamics (State)

/-- Parameters of the stiff-grid matching closed loop: DC capacitance and conductance, DC P-gain,
matching gain `η`, modulation amplitude `μ`, DC voltage reference `u*_dc`, grid amplitude `v₀`,
switching-inductor resistance `R_s` and inductance `L_s`. -/
structure Model where
  Cdc : ℝ
  Gdc : ℝ
  Kp : ℝ
  η : ℝ
  μ : ℝ
  ustar : ℝ
  v0 : ℝ
  Rs : ℝ
  Ls : ℝ

namespace Model

variable (m : Model)

/-- The nominal grid frequency `ω₀ = η u*_dc`. -/
def ω0 : ℝ := m.η * m.ustar

/-- `‖Z_s‖² = R_s² + ω₀² L_s²`. -/
def N : ℝ := m.Rs ^ 2 + m.ω0 ^ 2 * m.Ls ^ 2

/-- The internal model `î_dq(θ) = Z_s⁻¹ (v₀ e₂ − μ u* (−sin θ, cos θ))`, `d` component. -/
def iHatD (θ : ℝ) : ℝ :=
  (m.Rs * (m.μ * m.ustar * Real.sin θ) + m.ω0 * m.Ls * (m.v0 - m.μ * m.ustar * Real.cos θ)) / m.N

/-- The internal model, `q` component. -/
def iHatQ (θ : ℝ) : ℝ :=
  (-(m.ω0 * m.Ls) * (m.μ * m.ustar * Real.sin θ) + m.Rs * (m.v0 - m.μ * m.ustar * Real.cos θ)) /
    m.N

/-- The synchronization potential `S(θ) = î(θ)ᵀ L_s î(θ)/2` of the source. -/
def potential (θ : ℝ) : ℝ := m.Ls / 2 * (m.iHatD θ ^ 2 + m.iHatQ θ ^ 2)

/-- The internal model of the switch current, `î_x = −μ (−sin θ, cos θ)ᵀ î(θ)`. -/
def ixHat (θ : ℝ) : ℝ := -(m.μ * (-Real.sin θ * m.iHatD θ + Real.cos θ * m.iHatQ θ))

/-- The synchronizing-torque gain: `η ∇S(θ) = κ sin θ`. -/
def κ : ℝ := m.μ * m.v0 * m.ω0 * m.Ls / m.N

/-- The potential stiffness: `S(θ) − S(0) = k (1 − cos θ)`. -/
def k : ℝ := m.Ls * m.μ * m.ustar * m.v0 / m.N

/-- The DC current control (18). -/
def idc (x : State 4) : ℝ :=
  -m.Kp * (x 1 - m.ustar) + m.Gdc * m.ustar + m.ixHat (x 0) - m.κ * Real.sin (x 0)

/-- The closed loop in the grid `dq` frame, state `(θ_dq, u_dc, i_d, i_q)`. -/
def field (x : State 4) : State 4 :=
  WithLp.toLp 2 ![
    m.η * x 1 - m.ω0,
    (-m.Gdc * x 1 + m.idc x + m.μ * (-Real.sin (x 0) * x 2 + Real.cos (x 0) * x 3)) / m.Cdc,
    (-(m.Rs * x 2 - m.ω0 * m.Ls * x 3) - m.μ * (-Real.sin (x 0)) * x 1) / m.Ls,
    (-(m.ω0 * m.Ls * x 2 + m.Rs * x 3) + m.v0 - m.μ * Real.cos (x 0) * x 1) / m.Ls]

/-- The operating point `(0, u*_dc, î_dq(0))`. -/
def point : State 4 := WithLp.toLp 2 ![0, m.ustar, m.iHatD 0, m.iHatQ 0]

/-- The energy `H − S(0) = C_dc ũ²/2 + k (1 − cos θ) + L_s ‖i − î(θ)‖²/2`. -/
def energy (x : State 4) : ℝ :=
  m.Cdc / 2 * (x 1 - m.ustar) ^ 2 + m.k * (1 - Real.cos (x 0)) +
    m.Ls / 2 * ((x 2 - m.iHatD (x 0)) ^ 2 + (x 3 - m.iHatQ (x 0)) ^ 2)

/-- The damping margin `G_dc + K_p − μ²ω₀²L_s²/(4R_s N)`. -/
def margin : ℝ := m.Gdc + m.Kp - m.μ ^ 2 * m.ω0 ^ 2 * m.Ls ^ 2 / (4 * m.Rs * m.N)

end Model

/-- Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_foundation] theorem hasDerivAt_iHatD (m : Model) (θ : ℝ) :
    HasDerivAt m.iHatD
      (m.μ * m.ustar * (m.Rs * Real.cos θ + m.ω0 * m.Ls * Real.sin θ) / m.N) θ := by
  have h := (((Real.hasDerivAt_sin θ).const_mul (m.μ * m.ustar)).const_mul m.Rs).add
    ((((Real.hasDerivAt_cos θ).const_mul (m.μ * m.ustar)).const_sub m.v0).const_mul
      (m.ω0 * m.Ls))
  convert h.div_const m.N using 1
  · funext θ
    simp [Model.iHatD]
  · ring

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem hasDerivAt_iHatQ (m : Model) (θ : ℝ) :
    HasDerivAt m.iHatQ
      (m.μ * m.ustar * (m.Rs * Real.sin θ - m.ω0 * m.Ls * Real.cos θ) / m.N) θ := by
  have h := (((Real.hasDerivAt_sin θ).const_mul (m.μ * m.ustar)).const_mul (-(m.ω0 * m.Ls))).add
    ((((Real.hasDerivAt_cos θ).const_mul (m.μ * m.ustar)).const_sub m.v0).const_mul m.Rs)
  convert h.div_const m.N using 1
  · funext θ
    simp [Model.iHatQ]
  · ring

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem energy_differentiable (m : Model) : Differentiable ℝ m.energy := by
  have h := fun j : Fin 4 => (PiLp.proj 2 (fun _ : Fin 4 => ℝ) j : State 4 →L[ℝ] ℝ).differentiable
  have h0 : Differentiable ℝ (fun x : State 4 => x 0) := h 0
  have h1 : Differentiable ℝ (fun x : State 4 => x 1) := h 1
  have h2 : Differentiable ℝ (fun x : State 4 => x 2) := h 2
  have h3 : Differentiable ℝ (fun x : State 4 => x 3) := h 3
  have hd : Differentiable ℝ m.iHatD := fun θ => (hasDerivAt_iHatD m θ).differentiableAt
  have hq : Differentiable ℝ m.iHatQ := fun θ => (hasDerivAt_iHatQ m θ).differentiableAt
  unfold Model.energy
  fun_prop

/-- The derivative of the energy. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem fderiv_energy (m : Model) (x v : State 4) :
    fderiv ℝ m.energy x v =
      m.Cdc * (x 1 - m.ustar) * v 1 + m.k * Real.sin (x 0) * v 0 +
        m.Ls * ((x 2 - m.iHatD (x 0)) *
            (v 2 - m.μ * m.ustar * (m.Rs * Real.cos (x 0) + m.ω0 * m.Ls * Real.sin (x 0)) / m.N *
              v 0) +
          (x 3 - m.iHatQ (x 0)) *
            (v 3 - m.μ * m.ustar * (m.Rs * Real.sin (x 0) - m.ω0 * m.Ls * Real.cos (x 0)) / m.N *
              v 0)) := by
  apply Dynamics.fderiv_apply_eq_of_hasDerivAt_line ((energy_differentiable m) x)
  have hlin : ∀ j : Fin 4, HasDerivAt (fun t : ℝ => x j + t * v j) (v j) 0 := fun j => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v j)).const_add (x j)
  have hθ := hlin 0
  have hD : HasDerivAt (fun t : ℝ => m.iHatD (x 0 + t * v 0))
      (m.μ * m.ustar * (m.Rs * Real.cos (x 0) + m.ω0 * m.Ls * Real.sin (x 0)) / m.N * v 0) 0 := by
    exact (hasDerivAt_iHatD m (x 0)).comp_of_eq (0 : ℝ) hθ (by simp)
  have hQ : HasDerivAt (fun t : ℝ => m.iHatQ (x 0 + t * v 0))
      (m.μ * m.ustar * (m.Rs * Real.sin (x 0) - m.ω0 * m.Ls * Real.cos (x 0)) / m.N * v 0) 0 := by
    exact (hasDerivAt_iHatQ m (x 0)).comp_of_eq (0 : ℝ) hθ (by simp)
  have hc : HasDerivAt (fun t : ℝ => Real.cos (x 0 + t * v 0)) (-Real.sin (x 0) * v 0) 0 := by
    exact (Real.hasDerivAt_cos (x 0)).comp_of_eq (0 : ℝ) hθ (by simp)
  have h1 := ((hlin 1).sub_const m.ustar).pow 2 |>.const_mul (m.Cdc / 2)
  have h2 := (hc.const_sub 1).const_mul m.k
  have h3 := ((((hlin 2).sub hD).pow 2).add (((hlin 3).sub hQ).pow 2)).const_mul (m.Ls / 2)
  have h := (h1.add h2).add h3
  have e : (fun t : ℝ => m.energy (x + t • v)) = fun t =>
      m.Cdc / 2 * (x 1 + t * v 1 - m.ustar) ^ 2 + m.k * (1 - Real.cos (x 0 + t * v 0)) +
        m.Ls / 2 * ((x 2 + t * v 2 - m.iHatD (x 0 + t * v 0)) ^ 2 +
          (x 3 + t * v 3 - m.iHatQ (x 0 + t * v 0)) ^ 2) := by
    funext t
    simp [Model.energy]
  rw [e]
  convert h using 1
  simp
  ring

/-- The energy balance of the source's appendix:
`dH/dt = −(G_dc+K_p) ũ² − R_s ‖ĩ‖² − ũ ĩᵀ T(θ)`, `T(θ) = (μ ω₀ L_s/N) Z_sᵀ (cos θ, sin θ)`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem energy_lie (m : Model) (hN : m.N ≠ 0) (hL : m.Ls ≠ 0)
    (hC : m.Cdc ≠ 0) (x : State 4) :
    fderiv ℝ m.energy x (m.field x) =
      -(m.Gdc + m.Kp) * (x 1 - m.ustar) ^ 2 -
        m.Rs * ((x 2 - m.iHatD (x 0)) ^ 2 + (x 3 - m.iHatQ (x 0)) ^ 2) -
        m.μ * m.ω0 * m.Ls / m.N * (x 1 - m.ustar) *
          ((x 2 - m.iHatD (x 0)) * (m.Rs * Real.cos (x 0) + m.ω0 * m.Ls * Real.sin (x 0)) +
            (x 3 - m.iHatQ (x 0)) * (m.Rs * Real.sin (x 0) - m.ω0 * m.Ls * Real.cos (x 0))) := by
  rw [fderiv_energy]
  simp only [Model.field, Model.idc, Model.ixHat, Model.iHatD, Model.iHatQ, Model.κ, Model.k,
    PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  field_simp
  simp only [Model.N, Model.ω0]
  ring

private theorem sos_aux {R N B G u e1 e2 z1 z2 : ℝ} (hR : 0 < R) (hN : 0 < N)
    (hz : z1 ^ 2 + z2 ^ 2 = N) :
    -G * u ^ 2 - R * (e1 ^ 2 + e2 ^ 2) - B / N * u * (e1 * z1 + e2 * z2) ≤
      -(G - B ^ 2 / (4 * R * N)) * u ^ 2 := by
  have h1 : 0 ≤ (2 * R * N * e1 + B * u * z1) ^ 2 + (2 * R * N * e2 + B * u * z2) ^ 2 := by
    positivity
  have h2 : (2 * R * N * e1 + B * u * z1) ^ 2 + (2 * R * N * e2 + B * u * z2) ^ 2 =
      4 * R ^ 2 * N ^ 2 * (e1 ^ 2 + e2 ^ 2) + 4 * R * N * B * u * (e1 * z1 + e2 * z2) +
        B ^ 2 * u ^ 2 * N := by
    linear_combination (B ^ 2 * u ^ 2) * hz
  have h3 : 4 * R * N ^ 2 * (R * (e1 ^ 2 + e2 ^ 2) + B / N * u * (e1 * z1 + e2 * z2) +
      B ^ 2 * u ^ 2 / (4 * R * N)) = 4 * R ^ 2 * N ^ 2 * (e1 ^ 2 + e2 ^ 2) +
        4 * R * N * B * u * (e1 * z1 + e2 * z2) + B ^ 2 * u ^ 2 * N := by
    field_simp
  have h4 : 0 ≤ R * (e1 ^ 2 + e2 ^ 2) + B / N * u * (e1 * z1 + e2 * z2) +
      B ^ 2 * u ^ 2 / (4 * R * N) := by
    have h5 : 0 ≤ 4 * R * N ^ 2 * (R * (e1 ^ 2 + e2 ^ 2) + B / N * u * (e1 * z1 + e2 * z2) +
        B ^ 2 * u ^ 2 / (4 * R * N)) := by rw [h3, ← h2]; exact h1
    have h6 : 0 < 4 * R * N ^ 2 := by positivity
    exact (mul_nonneg_iff_of_pos_left h6).mp h5
  have h7 : -G * u ^ 2 - R * (e1 ^ 2 + e2 ^ 2) - B / N * u * (e1 * z1 + e2 * z2) -
      (-(G - B ^ 2 / (4 * R * N)) * u ^ 2) = -(R * (e1 ^ 2 + e2 ^ 2) +
        B / N * u * (e1 * z1 + e2 * z2) + B ^ 2 * u ^ 2 / (4 * R * N)) := by ring
  linarith

/-- With `R_s > 0`, `dH/dt ≤ −margin ũ²`. An equivalent form of the damping requirement. -/
@[powerlib_foundation] theorem energy_lie_le (m : Model) (hR : 0 < m.Rs) (hL : m.Ls ≠ 0)
    (hC : m.Cdc ≠ 0) (x : State 4) :
    fderiv ℝ m.energy x (m.field x) ≤ -m.margin * (x 1 - m.ustar) ^ 2 := by
  have hN : 0 < m.N := by
    unfold Model.N
    have := sq_nonneg (m.ω0)
    positivity
  rw [energy_lie m hN.ne' hL hC]
  have hz : (m.Rs * Real.cos (x 0) + m.ω0 * m.Ls * Real.sin (x 0)) ^ 2 +
      (m.Rs * Real.sin (x 0) - m.ω0 * m.Ls * Real.cos (x 0)) ^ 2 = m.N := by
    unfold Model.N
    linear_combination (m.Rs ^ 2 + m.ω0 ^ 2 * m.Ls ^ 2) * Real.sin_sq_add_cos_sq (x 0)
  have h := sos_aux (G := m.Gdc + m.Kp) (B := m.μ * m.ω0 * m.Ls) (u := x 1 - m.ustar)
    (e1 := x 2 - m.iHatD (x 0)) (e2 := x 3 - m.iHatQ (x 0)) hR hN hz
  have hm : m.margin = m.Gdc + m.Kp - (m.μ * m.ω0 * m.Ls) ^ 2 / (4 * m.Rs * m.N) := by
    unfold Model.margin
    ring
  rw [hm]
  linarith

/-- Every `θ_dq` with `sin θ_dq = 0` gives an equilibrium `(θ_dq, u*, î(θ_dq))`; for
`θ_dq = π` it is the saddle of `S` contained in the source's LaSalle set. Static evidence on the
model, not a connection conclusion. -/
@[powerlib_foundation] theorem field_eq_zero_of_sin_eq_zero (m : Model) (hN : m.N ≠ 0) {θ : ℝ}
    (hθ : Real.sin θ = 0) :
    m.field (WithLp.toLp 2 ![θ, m.ustar, m.iHatD θ, m.iHatQ θ]) = 0 := by
  ext i
  fin_cases i
  · simp [Model.field, Model.ω0]
  · simp only [Model.field, Model.idc, Model.ixHat, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, PiLp.zero_apply, Fin.isValue, Fin.mk_one, hθ]
    ring
  · simp only [Model.field, Model.iHatD, Model.iHatQ, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, PiLp.zero_apply, Fin.isValue, Fin.reduceFinMk, hθ]
    ring
  · simp only [Model.field, Model.iHatD, Model.iHatQ, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, PiLp.zero_apply, Fin.isValue, Fin.reduceFinMk, hθ]
    field_simp
    simp only [Model.N]
    ring

/-- The operating point is an equilibrium. An equivalent form of the damping requirement. -/
@[powerlib_foundation] theorem field_point (m : Model) (hN : m.N ≠ 0) : m.field m.point = 0 := by
  simpa [Model.point] using field_eq_zero_of_sin_eq_zero m hN (θ := 0) Real.sin_zero

/-- The closed loop is `2π`-periodic in `θ_dq`. An equivalent form of the damping requirement. -/
@[powerlib_foundation] theorem field_add_two_pi (m : Model) (θ u id iq : ℝ) :
    m.field (WithLp.toLp 2 ![θ + 2 * Real.pi, u, id, iq]) =
      m.field (WithLp.toLp 2 ![θ, u, id, iq]) := by
  simp [Model.field, Model.idc, Model.ixHat, Model.iHatD, Model.iHatQ]

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem energy_point (m : Model) : m.energy m.point = 0 := by
  simp [Model.energy, Model.point]

private theorem energy_pos (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls) (hk : 0 < m.k)
    {x : State 4} (hx : |x 0| < 2 * Real.pi) (hne : x ≠ m.point) : 0 < m.energy x := by
  unfold Model.energy
  by_contra hle
  push Not at hle
  have a0 : 0 ≤ m.Cdc / 2 * (x 1 - m.ustar) ^ 2 := by positivity
  have a1 : 0 ≤ m.k * (1 - Real.cos (x 0)) :=
    mul_nonneg hk.le (by linarith [Real.cos_le_one (x 0)])
  have a2 : 0 ≤ m.Ls / 2 * ((x 2 - m.iHatD (x 0)) ^ 2 + (x 3 - m.iHatQ (x 0)) ^ 2) := by
    positivity
  have e0 : m.Cdc / 2 * (x 1 - m.ustar) ^ 2 = 0 := by linarith
  have e1 : m.k * (1 - Real.cos (x 0)) = 0 := by linarith
  have e2 : m.Ls / 2 * ((x 2 - m.iHatD (x 0)) ^ 2 + (x 3 - m.iHatQ (x 0)) ^ 2) = 0 := by linarith
  have u1 : x 1 = m.ustar := by
    have := (mul_eq_zero.mp e0).resolve_left (by positivity)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  have c1 : Real.cos (x 0) = 1 := by
    have := (mul_eq_zero.mp e1).resolve_left hk.ne'
    linarith
  have t0 : x 0 = 0 := by
    rw [abs_lt] at hx
    exact (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) hx.2).mp c1
  have e2' := (mul_eq_zero.mp e2).resolve_left (by positivity)
  have i2 : x 2 = m.iHatD (x 0) := by
    nlinarith [sq_nonneg (x 2 - m.iHatD (x 0)), sq_nonneg (x 3 - m.iHatQ (x 0))]
  have i3 : x 3 = m.iHatQ (x 0) := by
    nlinarith [sq_nonneg (x 2 - m.iHatD (x 0)), sq_nonneg (x 3 - m.iHatQ (x 0))]
  apply hne
  ext i
  fin_cases i <;> simp [Model.point, t0, u1, i2, i3]

/-- The source's potential (16): `S(θ) = L_s (μ²u*² − 2μu*v₀ cos θ + v₀²)/(2N)`. Static evidence
on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem potential_eq (m : Model) (hN : m.N ≠ 0) (θ : ℝ) :
    m.potential θ = m.Ls / (2 * m.N) *
      (m.μ ^ 2 * m.ustar ^ 2 - 2 * m.μ * m.ustar * m.v0 * Real.cos θ + m.v0 ^ 2) := by
  have hw : (m.μ * m.ustar * Real.sin θ) ^ 2 + (m.v0 - m.μ * m.ustar * Real.cos θ) ^ 2 =
      m.μ ^ 2 * m.ustar ^ 2 - 2 * m.μ * m.ustar * m.v0 * Real.cos θ + m.v0 ^ 2 := by
    linear_combination (m.μ ^ 2 * m.ustar ^ 2) * Real.sin_sq_add_cos_sq θ
  have hZ :
      (m.Rs * (m.μ * m.ustar * Real.sin θ) +
          m.ω0 * m.Ls * (m.v0 - m.μ * m.ustar * Real.cos θ)) ^ 2
      + (-(m.ω0 * m.Ls) * (m.μ * m.ustar * Real.sin θ) +
          m.Rs * (m.v0 - m.μ * m.ustar * Real.cos θ)) ^ 2
      = m.N * ((m.μ * m.ustar * Real.sin θ) ^ 2 + (m.v0 - m.μ * m.ustar * Real.cos θ) ^ 2) := by
    simp only [Model.N]
    ring
  rw [Model.potential, Model.iHatD, Model.iHatQ, div_pow, div_pow, ← add_div, hZ, hw]
  field_simp

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem potential_sub_potential_zero (m : Model) (hN : m.N ≠ 0) (θ : ℝ) :
    m.potential θ - m.potential 0 = m.k * (1 - Real.cos θ) := by
  rw [potential_eq m hN, potential_eq m hN, Real.cos_zero, Model.k]
  field_simp
  ring

/-- `η ∇S = κ sin θ`: the synchronizing term of the control (18) is the gradient of the
potential. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem eta_mul_k (m : Model) : m.η * m.k = m.κ := by
  simp only [Model.k, Model.κ, Model.ω0]
  ring

/-! ## Linearization at the operating point -/

namespace Model
variable (m : Model)

/-- The Jacobian of the closed loop at the operating point (`hasFDerivAt_field_point`). -/
def jac : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, m.η, 0, 0;
     m.μ * m.ω0 * m.Ls * (m.μ * m.ustar - m.v0) / (m.N * m.Cdc), -(m.Gdc + m.Kp) / m.Cdc, 0,
       m.μ / m.Cdc;
     m.μ * m.ustar / m.Ls, 0, -m.Rs / m.Ls, m.ω0;
     0, -m.μ / m.Ls, -m.ω0, -m.Rs / m.Ls]

/-- The slope `î_d'(0)` of the internal model. -/
def p : ℝ := m.μ * m.ustar * m.Rs / m.N
/-- The slope `î_q'(0)` of the internal model. -/
def q : ℝ := -(m.μ * m.ustar * m.ω0 * m.Ls) / m.N

/-- The quadratic part of the energy at the operating point, in the deviations
`(δθ, δu, δi_d, δi_q)` (twice the Hessian form of `H − S(0)`). -/
def linE (a b c d : ℝ) : ℝ :=
  m.k * a ^ 2 + m.Cdc * b ^ 2 + m.Ls * ((c - m.p * a) ^ 2 + (d - m.q * a) ^ 2)

/-- The polarization `B(x, y)` of `linE`: `B(x, x) = 2 linE x`. -/
def linB (a b c d y0 y1 y2 y3 : ℝ) : ℝ :=
  2 * m.k * a * y0 + 2 * m.Cdc * b * y1 +
    2 * m.Ls * ((c - m.p * a) * (y2 - m.p * y0) + (d - m.q * a) * (y3 - m.q * y0))

/-- The derivative `B(x, J x)` of `linE` along the linearization `J = jac`. -/
def linDot (a b c d : ℝ) : ℝ :=
  m.linB a b c d
    (m.η * b)
    (m.μ * m.ω0 * m.Ls * (m.μ * m.ustar - m.v0) / (m.N * m.Cdc) * a - (m.Gdc + m.Kp) / m.Cdc * b +
      m.μ / m.Cdc * d)
    (m.μ * m.ustar / m.Ls * a - m.Rs / m.Ls * c + m.ω0 * d)
    (-m.μ / m.Ls * b - m.ω0 * c - m.Rs / m.Ls * d)

end Model

/-- Energy balance of the linearization:
`B(x, J x) = −2 (g δu² + R_s ‖δĩ‖² + (μω₀L_s/N) δu δĩᵀ Z_sᵀ e₁)`,
`δĩ = δi − î'(0) δθ`. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem linDot_eq (m : Model) (hN : m.N ≠ 0) (hL : m.Ls ≠ 0)
    (hC : m.Cdc ≠ 0) (a b c d : ℝ) :
    m.linDot a b c d = -2 * ((m.Gdc + m.Kp) * b ^ 2 +
      m.Rs * ((c - m.p * a) ^ 2 + (d - m.q * a) ^ 2) +
      m.μ * m.ω0 * m.Ls / m.N * b * ((c - m.p * a) * m.Rs + (d - m.q * a) * (-(m.ω0 * m.Ls)))) := by
  simp only [Model.linDot, Model.linB, Model.p, Model.q, Model.k]
  field_simp
  simp only [Model.N, Model.ω0]
  ring

private theorem jac_coef (m : Model) (hN : m.N ≠ 0) (hC : m.Cdc ≠ 0) :
    m.μ * m.ω0 * m.Ls * (m.μ * m.ustar - m.v0) / (m.N * m.Cdc) + m.μ / m.Cdc * m.q =
      -(m.μ * m.v0 * m.ω0 * m.Ls) / (m.N * m.Cdc) := by
  unfold Model.q
  field_simp
  ring

private theorem sq_add_sq_eq_zero {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  have hx : x ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx,
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy⟩

private theorem eigen_re_im {A : Matrix (Fin 4) (Fin 4) ℝ} {lam : ℂ} {v : Fin 4 → ℂ}
    (h : Matrix.mulVec (A.map (algebraMap ℝ ℂ)) v = lam • v) (i : Fin 4) :
    A i 0 * (v 0).re + A i 1 * (v 1).re + A i 2 * (v 2).re + A i 3 * (v 3).re =
        lam.re * (v i).re - lam.im * (v i).im ∧
      A i 0 * (v 0).im + A i 1 * (v 1).im + A i 2 * (v 2).im + A i 3 * (v 3).im =
        lam.im * (v i).re + lam.re * (v i).im := by
  obtain ⟨hr, hi⟩ := Criteria.mulVec_re_im_of_eigenpair h
  have hr := congrFun hr i
  have hi := congrFun hi i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul] at hr hi
  exact ⟨hr, hi⟩

/-- **The linearization at the operating point is Hurwitz** under the source's strict condition
(`margin > 0`), `C_dc, L_s, R_s > 0`, `μ u* v₀ > 0` and `η ≠ 0`. Proof: along a complex eigenvector
the quadratic energy gives `2 Re λ (E(v_r) + E(v_i)) = B(v_r, J v_r) + B(v_i, J v_i) ≤ 0`; on the
boundary `Re λ = 0` the dissipation forces `δu = 0`, `δĩ = 0`, and the DC row then forces
`κ δθ = 0`. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem jac_isHurwitz (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls)
    (hR : 0 < m.Rs) (hs : 0 < m.μ * m.ustar * m.v0) (hη : m.η ≠ 0) (hδ : 0 < m.margin) :
    LinearSystems.IsHurwitz m.jac := by
  intro lam v hv hev
  have hN : 0 < m.N := by
    unfold Model.N
    have := sq_nonneg m.ω0
    positivity
  have hk : 0 < m.k := by
    unfold Model.k
    have : m.Ls * m.μ * m.ustar * m.v0 = m.Ls * (m.μ * m.ustar * m.v0) := by ring
    rw [this]
    positivity
  obtain ⟨r0, i0⟩ := eigen_re_im hev 0
  obtain ⟨r1, i1⟩ := eigen_re_im hev 1
  obtain ⟨r2, i2⟩ := eigen_re_im hev 2
  obtain ⟨r3, i3⟩ := eigen_re_im hev 3
  simp only [Model.jac, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons] at r0 i0 r1 i1 r2 i2 r3 i3
  set σ := lam.re
  set ω := lam.im
  set ar := (v 0).re
  set br := (v 1).re
  set cr := (v 2).re
  set dr := (v 3).re
  set ai := (v 0).im
  set bi := (v 1).im
  set ci := (v 2).im
  set di := (v 3).im
  -- the energy identity along the eigenvector
  have key : m.linDot ar br cr dr + m.linDot ai bi ci di =
      2 * σ * (m.linE ar br cr dr + m.linE ai bi ci di) := by
    simp only [Model.linDot, Model.linB, Model.linE]
    linear_combination
      (2 * m.k * ar - 2 * m.Ls * m.p * (cr - m.p * ar) - 2 * m.Ls * m.q * (dr - m.q * ar)) * r0 +
      (2 * m.Cdc * br) * r1 + (2 * m.Ls * (cr - m.p * ar)) * r2 +
      (2 * m.Ls * (dr - m.q * ar)) * r3 +
      (2 * m.k * ai - 2 * m.Ls * m.p * (ci - m.p * ai) - 2 * m.Ls * m.q * (di - m.q * ai)) * i0 +
      (2 * m.Cdc * bi) * i1 + (2 * m.Ls * (ci - m.p * ai)) * i2 + (2 * m.Ls * (di - m.q * ai)) * i3
  -- dissipation
  have hm : m.margin = m.Gdc + m.Kp - (m.μ * m.ω0 * m.Ls) ^ 2 / (4 * m.Rs * m.N) := by
    unfold Model.margin
    ring
  have hz : m.Rs ^ 2 + (-(m.ω0 * m.Ls)) ^ 2 = m.N := by
    unfold Model.N
    ring
  have hdot : ∀ a b c d : ℝ, m.linDot a b c d ≤ -2 * m.margin * b ^ 2 := by
    intro a b c d
    rw [linDot_eq m hN.ne' hL.ne' hC.ne', hm]
    have := sos_aux (G := m.Gdc + m.Kp) (B := m.μ * m.ω0 * m.Ls) (u := b)
      (e1 := c - m.p * a) (e2 := d - m.q * a) hR hN hz
    nlinarith [this]
  have hE : ∀ a b c d : ℝ, 0 ≤ m.linE a b c d := by
    intro a b c d
    unfold Model.linE
    positivity
  by_contra hσ
  push Not at hσ
  have hsum : 0 ≤ m.linDot ar br cr dr + m.linDot ai bi ci di := by
    rw [key]
    have := hE ar br cr dr
    have := hE ai bi ci di
    positivity
  have h1 := hdot ar br cr dr
  have h2 := hdot ai bi ci di
  have p1 : 0 ≤ m.margin * br ^ 2 := mul_nonneg hδ.le (sq_nonneg _)
  have p2 : 0 ≤ m.margin * bi ^ 2 := mul_nonneg hδ.le (sq_nonneg _)
  have hbr : br = 0 := by
    have : m.margin * br ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp this).resolve_left hδ.ne')
  have hbi : bi = 0 := by
    have : m.margin * bi ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp this).resolve_left hδ.ne')
  have hDr := linDot_eq m hN.ne' hL.ne' hC.ne' ar br cr dr
  have hDi := linDot_eq m hN.ne' hL.ne' hC.ne' ai bi ci di
  rw [hbr] at hDr
  rw [hbi] at hDi
  have hSr : m.linDot ar 0 cr dr = -2 * (m.Rs * ((cr - m.p * ar) ^ 2 + (dr - m.q * ar) ^ 2)) := by
    rw [hDr]; ring
  have hSi : m.linDot ai 0 ci di = -2 * (m.Rs * ((ci - m.p * ai) ^ 2 + (di - m.q * ai) ^ 2)) := by
    rw [hDi]; ring
  rw [hbr, hbi, hSr, hSi] at hsum
  have q1 : 0 ≤ m.Rs * ((cr - m.p * ar) ^ 2 + (dr - m.q * ar) ^ 2) := by positivity
  have q2 : 0 ≤ m.Rs * ((ci - m.p * ai) ^ 2 + (di - m.q * ai) ^ 2) := by positivity
  have er : (cr - m.p * ar) ^ 2 + (dr - m.q * ar) ^ 2 = 0 := by
    have : m.Rs * ((cr - m.p * ar) ^ 2 + (dr - m.q * ar) ^ 2) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hR.ne'
  have ei : (ci - m.p * ai) ^ 2 + (di - m.q * ai) ^ 2 = 0 := by
    have : m.Rs * ((ci - m.p * ai) ^ 2 + (di - m.q * ai) ^ 2) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hR.ne'
  obtain ⟨hcr, hdr⟩ := sq_add_sq_eq_zero er
  obtain ⟨hci, hdi⟩ := sq_add_sq_eq_zero ei
  rw [sub_eq_zero] at hcr hdr hci hdi
  -- the DC row forces the angle component to vanish
  have hus : m.ustar ≠ 0 := by
    rintro h
    rw [h] at hs
    simp at hs
  have hμ : m.μ ≠ 0 := by
    rintro h
    rw [h] at hs
    simp at hs
  have hv0 : m.v0 ≠ 0 := by
    rintro h
    rw [h] at hs
    simp at hs
  have hω : m.ω0 ≠ 0 := mul_ne_zero hη hus
  have hcoef := jac_coef m hN.ne' hC.ne'
  have hcoef0 : -(m.μ * m.v0 * m.ω0 * m.Ls) / (m.N * m.Cdc) ≠ 0 := by
    have : m.μ * m.v0 * m.ω0 * m.Ls ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero hμ hv0) hω) hL.ne'
    exact div_ne_zero (neg_ne_zero.mpr this) (mul_ne_zero hN.ne' hC.ne')
  have har : ar = 0 := by
    rw [hbr, hdr] at r1
    rw [hbi] at r1
    have : (m.μ * m.ω0 * m.Ls * (m.μ * m.ustar - m.v0) / (m.N * m.Cdc) + m.μ / m.Cdc * m.q) *
        ar = 0 := by linear_combination r1
    rw [hcoef] at this
    exact (mul_eq_zero.mp this).resolve_left hcoef0
  have hai : ai = 0 := by
    rw [hbi, hdi, hbr] at i1
    have : (m.μ * m.ω0 * m.Ls * (m.μ * m.ustar - m.v0) / (m.N * m.Cdc) + m.μ / m.Cdc * m.q) *
        ai = 0 := by linear_combination i1
    rw [hcoef] at this
    exact (mul_eq_zero.mp this).resolve_left hcoef0
  apply hv
  funext j
  fin_cases j
  · exact Complex.ext har hai
  · exact Complex.ext hbr hbi
  · refine Complex.ext ?_ ?_
    · show cr = 0
      rw [hcr, har, mul_zero]
    · show ci = 0
      rw [hci, hai, mul_zero]
  · refine Complex.ext ?_ ?_
    · show dr = 0
      rw [hdr, har, mul_zero]
    · show di = 0
      rw [hdi, hai, mul_zero]

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field_contDiff (m : Model) : ContDiff ℝ 1 m.field := by
  have hd : ContDiff ℝ 1 m.iHatD := by
    unfold Model.iHatD
    fun_prop
  have hq : ContDiff ℝ 1 m.iHatQ := by
    unfold Model.iHatQ
    fun_prop
  rw [contDiff_euclidean]
  intro i
  fin_cases i <;> simp [Model.field, Model.idc, Model.ixHat] <;> fun_prop

/-- Entries of the Jacobian applied to a vector. An equivalent form of the damping requirement. -/
@[powerlib_foundation] theorem jac_apply (m : Model) (v : State 4) :
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.jac v) 0 = m.η * v 1 ∧
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.jac v) 1 =
      m.μ * m.ω0 * m.Ls * (m.μ * m.ustar - m.v0) / (m.N * m.Cdc) * v 0 -
        (m.Gdc + m.Kp) / m.Cdc * v 1 + m.μ / m.Cdc * v 3 ∧
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.jac v) 2 =
      m.μ * m.ustar / m.Ls * v 0 - m.Rs / m.Ls * v 2 + m.ω0 * v 3 ∧
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.jac v) 3 =
      -m.μ / m.Ls * v 1 - m.ω0 * v 2 - m.Rs / m.Ls * v 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four] <;>
    simp only [Model.jac, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;> ring

/-- The derivative of the closed loop at the operating point is `jac`. Static evidence on the
model, not a connection conclusion. -/
@[powerlib_foundation] theorem hasFDerivAt_field_point (m : Model) (hL : m.Ls ≠ 0) :
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
  have hD := (hasDerivAt_iHatD m (m.point 0)).comp_hasFDerivAt m.point h0
  have hQ := (hasDerivAt_iHatQ m (m.point 0)).comp_hasFDerivAt m.point h0
  have p0 : m.point 0 = 0 := by simp [Model.point]
  have p1 : m.point 1 = m.ustar := by simp [Model.point]
  have p2 : m.point 2 = m.iHatD 0 := by simp [Model.point]
  have p3 : m.point 3 = m.iHatQ 0 := by simp [Model.point]
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
      ((((h1.sub_const m.ustar).const_mul (-m.Kp)).add_const (m.Gdc * m.ustar)).add hix).sub
        (hs.const_mul m.κ)
    have h := (((h1.const_mul (-m.Gdc)).add hidc).add (((hs.neg.mul h2).add (hc.mul h3)).const_mul
      m.μ)).mul_const m.Cdc⁻¹
    convert h using 1
    · funext y
      simp only [Model.field, Model.idc, Model.ixHat, PiLp.toLp_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.mul_apply,
        Function.comp_apply, div_eq_mul_inv]
    · apply ContinuousLinearMap.ext; intro v
      simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply]
      rw [(j v).2.1]
      simp [p0, p2, p3, Model.κ]
      field_simp
      ring
  · have h := ((((h2.const_mul m.Rs).sub ((h3.const_mul m.ω0).const_mul m.Ls)).neg).sub
      ((hs.neg.const_mul m.μ).mul h1)).mul_const m.Ls⁻¹
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
      (((((h2.const_mul m.ω0).const_mul m.Ls).add (h3.const_mul m.Rs)).neg.add_const m.v0).sub
        ((hc.const_mul m.μ).mul h1)).mul_const m.Ls⁻¹
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

/-- Static requirements on stiff-grid matching models. -/
inductive Requirement
  | physical
  | synchronizing
  | dissipative
  | antiSynchronizing
  | damped
  | matching

/-- Satisfaction of a requirement. -/
def Meets (m : Model) : Requirement → Prop
  | .physical => 0 < m.Cdc ∧ 0 < m.Ls ∧ 0 < m.Rs
  | .synchronizing => 0 < m.μ * m.ustar * m.v0
  | .dissipative => 0 ≤ m.margin
  | .antiSynchronizing => m.μ * m.ustar * m.v0 < 0
  | .damped => 0 < m.margin
  | .matching => m.η ≠ 0

/-- For `η ≠ 0`, `margin > 0` is the source's (and the note's) condition
`(G_dc+K_p)/η² > L_s²μ²u*²/(4R_s‖Z_s‖²)`. An equivalent form of the damping requirement. -/
@[tmio M, powerlib_foundation] theorem margin_pos_iff (m : Model) (hη : m.η ≠ 0) :
    connection% (m ∈ TMIO.realize Meets {.damped} ↔ m.Ls ^ 2 * m.μ ^ 2 * m.ustar ^ 2 / (4 * m.Rs * m.N) <
      (m.Gdc + m.Kp) / m.η ^ 2) := by
  simp only [TMIO.Statement, TMIO.mem_realize, Set.mem_singleton_iff, forall_eq, Meets]
  change 0 < m.margin ↔ m.Ls ^ 2 * m.μ ^ 2 * m.ustar ^ 2 / (4 * m.Rs * m.N) <
      (m.Gdc + m.Kp) / m.η ^ 2
  have hη2 : 0 < m.η ^ 2 := by positivity
  rw [lt_div_iff₀ hη2, Model.margin, Model.ω0, sub_pos]
  constructor <;> intro h <;> convert h using 1 <;> ring

/-- The translation: Lyapunov stability into the physical, synchronizing and dissipative
requirements; local asymptotic and exponential stability into the physical, synchronizing,
damped (`margin > 0`) and matching (`η ≠ 0`) requirements; passivity into nothing; every other
flow sentence into the whole, inconsistent, language (unavailable coverage, exact for the global
sentences). -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable => {.physical, .synchronizing, .dissipative}
  | .flow .locallyAsymptoticallyStable | .flow .locallyExponentiallyStable =>
      {.physical, .synchronizing, .damped, .matching}
  | .flow _ => Set.univ
  | .passive => ∅
  | .envelope _ => Set.univ

/-- The closed loop translated to the operating point. -/
def Model.translated (m : Model) (z : State 4) : State 4 := m.field (z + m.point)

/-- The stiff-grid matching family. -/
def family : Family Model Requirement 4 0 :=
  ⟨fun m => Port.System.autonomous m.translated, Meets, translate⟩

/-- The stiff-grid family is the family of the translated autonomous fields. -/
@[powerlib_foundation] theorem family_isAutonomous : family.IsAutonomous Model.translated :=
  fun _ => rfl

private theorem mem_den_flow {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.field m.point :=
  Spectral.mem_den_flow_iff_shift (f := Model.field) (pt := Model.point) family_isAutonomous

private theorem lyapunovStable (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls) (hR : 0 < m.Rs)
    (hk : 0 < m.k) (hδ : 0 ≤ m.margin) :
    connection% (m ∈ family.den (.flow .lyapunovStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% mem_den_flow)]
  change LyapunovStable m.field m.point
  apply lyapunov_stable (D := {x : State 4 | |x 0| < 2 * Real.pi}) (by norm_num)
  exact
    { hD_open := isOpen_lt (continuous_abs.comp ((PiLp.proj 2 (fun _ : Fin 4 => ℝ) 0 :
          State 4 →L[ℝ] ℝ).continuous)) continuous_const
      hD_mem := by simp [Model.point, Real.pi_pos]
      hcont := (energy_differentiable m).continuous
      hV_diff := energy_differentiable m
      hzero := energy_point m
      hpos := fun x hx hne => energy_pos m hC hL hk hx hne
      hLie_nonpos := fun x _ => (energy_lie_le m hR hL.ne' hC.ne' x).trans
        (by nlinarith [sq_nonneg (x 1 - m.ustar)]) }

private theorem les (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls) (hR : 0 < m.Rs)
    (hs : 0 < m.μ * m.ustar * m.v0) (hη : m.η ≠ 0) (hδ : 0 < m.margin) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% mem_den_flow)]
  change LocallyExponentiallyStable m.field m.point
  have hN : 0 < m.N := by
    unfold Model.N
    have := sq_nonneg m.ω0
    positivity
  exact Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian m.jac (field_contDiff m)
    (field_point m hN.ne') (hasFDerivAt_field_point m hL.ne').fderiv
    (jac_isHurwitz m hC hL hR hs hη hδ)


/-- The whole requirement language is inconsistent. -/
@[tmio M, powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.realize_univ_eq_empty_of .synchronizing .antiSynchronizing fun m h1 h2 => ?_
  have h1 : 0 < m.μ * m.ustar * m.v0 := h1
  have h2 : m.μ * m.ustar * m.v0 < 0 := h2
  linarith

/-- The synchronizing coefficient is positive (`L_s, R_s > 0`, `μ u* v₀ > 0`).
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem k_pos (m : Model) (hL : 0 < m.Ls) (hR : 0 < m.Rs)
    (hs : 0 < m.μ * m.ustar * m.v0) : 0 < m.k := by
  have hN : 0 < m.N := by
    unfold Model.N
    have := sq_nonneg m.ω0
    positivity
  unfold Model.k
  have : m.Ls * m.μ * m.ustar * m.v0 = m.Ls * (m.μ * m.ustar * m.v0) := by ring
  rw [this]
  positivity

/-- Every translation of the stiff-grid matching family is sound. -/
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
    exact mem_den_flow.mpr ((mem_den_flow.mp (lyapunovStable m hC hL hR (k_pos m hL hR (hm .synchronizing (by simp)))
      (hm .dissipative (by simp)))))
  · rw [(connection_proof% TMIO.mem_realize)] at hm
    obtain ⟨hC, hL, hR⟩ : Meets m .physical := hm .physical (by simp)
    exact mem_den_flow.mpr ((mem_den_flow.mp (les m hC hL hR (hm .synchronizing (by simp)) (hm .matching (by simp))
      (hm .damped (by simp)))))
  · exact Spectral.realize_univ_subset_of_eq_empty realize_univ _ hm
  · rw [family_isAutonomous.den_passive]
    trivial

/-- Passivity is translated exactly: the closed loop has no ports. -/
@[tmio TM, powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_empty rfl family_isAutonomous.den_passive

/-- **Boundary**: no stiff-grid matching closed loop is globally asymptotically stable on `ℝ⁴`
(`2π`-periodicity gives a second equilibrium whenever the operating point is one). -/
@[tmio TM, powerlib_domain] theorem not_mem_den_globallyAsymptoticallyStable (m : Model) :
    connection% (m ∉ family.den (.flow .globallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% mem_den_flow)]
  intro h
  change Flow.GloballyAsymptoticallyStable _ _ at h
  refine Dynamics.not_globallyAsymptoticallyStable_of_equilibrium_ne
    (y := WithLp.toLp 2 ![0 + 2 * Real.pi, m.ustar, m.iHatD 0, m.iHatQ 0]) ?_ ?_ h
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

/-- **Lyapunov stability of the operating point** under the note's condition in its non-strict
form (`margin ≥ 0`), `C_dc, L_s, R_s > 0` and `μ u* v₀ > 0`: the energy `H − S(0)` is a local
Lyapunov function on `|θ_dq| < 2π`. -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls)
    (hR : 0 < m.Rs) (hs : 0 < m.μ * m.ustar * m.v0) (hδ : 0 ≤ m.margin) :
    connection% (m ∈ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% mem_den_flow)]
  exact (mem_den_flow.mp (lyapunovStable m hC hL hR (k_pos m hL hR hs) hδ))


/-- **Local exponential stability of the operating point** under the source's (and the note's)
strict condition `margin > 0`, with `C_dc, L_s, R_s > 0`, `μ u* v₀ > 0` and `η ≠ 0`: the
linearization is Hurwitz (`jac_isHurwitz`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable (m : Model) (hC : 0 < m.Cdc)
    (hL : 0 < m.Ls) (hR : 0 < m.Rs) (hs : 0 < m.μ * m.ustar * m.v0) (hη : m.η ≠ 0)
    (hδ : 0 < m.margin) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% mem_den_flow)]
  exact (mem_den_flow.mp (les m hC hL hR hs hη hδ))

/-- Local asymptotic stability of the operating point under the same requirements. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable (m : Model) (hC : 0 < m.Cdc)
    (hL : 0 < m.Ls) (hR : 0 < m.Rs) (hs : 0 < m.μ * m.ustar * m.v0) (hη : m.η ≠ 0)
    (hδ : 0 < m.margin) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.den_locallyExponentiallyStable_subset_las
    (mem_den_locallyExponentiallyStable m hC hL hR hs hη hδ)

end powerlib.GFM.Matching.MatchingStiffGrid
