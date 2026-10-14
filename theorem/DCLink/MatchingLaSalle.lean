import theorem.DCLink.MatchingStiffGrid
import theorem.Dynamics.LaSalle.Periodic
import theorem.Criteria.Routh3
import theorem.Dynamics.Lyapunov
import theorem.Dynamics.Instability

/-! # Stiff-grid matching control: LaSalle convergence and a basin estimate

This module completes the trajectory-level part of the energy-shaping argument for the
stiff-grid matching closed loop of `theorem.DCLink.MatchingStiffGrid`: the source's LaSalle
conclusion (convergence of every trajectory to the critical set of the synchronization potential)
and an estimate of the region of attraction of the operating point.

Provenance. C. Arghir, F. Dörfler, author version "Direct angle control and energy-shaping
techniques for grid-connected converters" of IEEE Trans. Power Electron. 35(4) (2020) 4398–4410
(ETH Research Collection, `bare_jrnl.pdf`), appendix "Energy-based stabilization of the eSM": under
`(G_dc+K_p)/η² > L_s²μ²u*_dc²/(4R_s‖Z_s‖²)` (`margin > 0`, `margin_pos_iff`) the energy `H` (22) is
nonincreasing and, "by LaSalle", every trajectory converges to `{ũ_dc = 0, ∇S(θ_dq) = 0,
ĩ_dq = 0}`. The work-sync notes (`theory/T-dc-voltage-gfm.md` §1.2, `theory/T-gfm-control.md`
§1.6, `theory/papers/@arghir2020matching.md`) contain only the condition.

Model boundary. Exactly the closed loop `MatchingStiffGrid.Model.field` (averaged converter,
L filter, stiff grid, grid `dq` frame; state `(θ_dq, u_dc, i_d, i_q) ∈ ℝ⁴`, continuous time,
autonomous; no PWM, delay, PLL, limits). Solutions are `IsIntegralCurveOn` curves on `[0, ∞)`.
Parameter ranges as stated in each result (`C_dc, L_s, R_s > 0` throughout).

Method (Rules §15: Mathlib/LeanForControl have no LaSalle principle for non-compact sublevel sets
or modulo a period; the generic pieces are the foundation results of
`theorem.Dynamics.LaSalle.Periodic`). The field is `2π`-periodic in `θ_dq`, so sublevel sets of `H`
are unbounded in `ℝ⁴`. The cylinder map `cyl x = (cos θ, sin θ, u, i_d, i_q)` carries the closed
loop to the polynomial field `cylField` on `ℝ⁵` (`fderiv_cyl_field`: a semiconjugacy), for which
`c² + s²` is a first integral (`fderiv_circle_cylField`) and the energy `cylEnergy` (with
`energy = cylEnergy ∘ cyl`, `energy_eq_cylEnergy`) has compact sublevel sets on the cylinder
`c² + s² = 1` (`isCompact_cylSublevel`) and Lie derivative `≤ −margin ũ²` there (`cylLie_le`, from
the appendix balance `energy_lie_le` through `cylLie_cyl`). LaSalle on the invariant cylinder
(`Dynamics.LaSalle.lasalle_levelSet`, the `C¹` LaSalle of `theorem.Dynamics.LaSalle.Basin`, no global Lipschitz
bound) with the LaSalle set `dH/dt = 0 ⇒ ũ = 0, ĩ = 0` (`cylLie_eq_zero`) and the DC row
`ũ' = −κ sin θ / C_dc` there (`cylField_two_of_mem`, `κ = η k ≠ 0`) gives convergence of the
cylinder image to `{sin θ = 0, ũ = 0, ĩ = 0}`; `Dynamics.LaSalle.exists_int_tendsto_of_tendsto_sin` (no
drift between the zeros of `sin`) lifts it back to `ℝ⁴`.

At the boundary `margin = 0` the dissipation `dH/dt = −margin ũ² − ‖2R_sN ĩ + μω₀L_s ũ z(θ)‖²/(4R_sN²)`
(`cylLie_eq_zero_of_margin_eq_zero`) vanishes on the three-dimensional set
`ĩ = −c ũ z(θ)`, `c = μω₀L_s/(2R_sN)`; there the energy is the pendulum energy
`a ũ²/2 + k(1 − cos θ)`, `a = C_dc + L_s c²N` (`cylEnergy_of_rel`), and the DC row is a negatively
damped pendulum `C_dc ũ' = g ũ − κ sin θ`, `g = (μω₀L_s)²/(4R_sN)` (`cylField_two_of_rel`). A
solution segment staying in that set has `ũ ≡ 0` (where `ũ ≠ 0`, constant energy forces
`a g ũ = (a − C_dc) κ sin θ`, its derivative then fixes `cos θ`, contradicting `θ' = η ũ ≠ 0`) and
therefore starts at `{sin θ = 0, ũ = 0, ĩ = 0}` (`margin_zero_segment`, through
`Dynamics.LaSalle.lasalle_condition_of_trajectories_mem`).

Results.
* Static (public foundation, about the model's maps, not connection conclusions): `cylField_cyl`,
  `hasDerivAt_cyl_line`, `fderiv_cyl_field`, `cyl_contDiff`, `cylField_contDiff`,
  `cylEnergy_contDiff`, `energy_eq_cylEnergy`, `cylLie_cyl`, `cyl_apply`, `cD_cos_sin`,
  `cQ_cos_sin`, `fderiv_circle_cylField`, `exists_cyl_eq`, `cylLie_le`, `cylLie_eq_zero`,
  `cylField_two_of_mem`, `cD_sq_add_cQ_sq`, `isCompact_cylSublevel`,
  `cylLie_eq_zero_of_margin_eq_zero`, `cylEnergy_of_rel`, `cylField_two_of_rel`,
  `hasDerivAt_potential` (`∇S(θ) = k sin θ`), `boundaryModel_margin`.
* Trajectory level (private implementation evidence, Rules §3a: set attraction and regions of
  attraction are not sentences of the library, so they are not published as Family conclusions):
  - `tendsto_equilibrium` (**the source's LaSalle conclusion, PROVED in a sharper form and for
    the non-strict condition**): with `margin ≥ 0`, `C_dc, L_s, R_s > 0`, `η ≠ 0` and
    `μ u* v₀ ≠ 0`, every forward solution converges to a single equilibrium
    `(j π, u*_dc, î_dq(j π))`, `j ∈ ℤ`;
  - `tendsto_critical`: hence every forward solution converges (in the neighbourhood-filter sense
    `𝓝ˢ`) to the source's set `{ũ_dc = 0, ∇S(θ_dq) = 0, ĩ_dq = 0}` (`∇S = deriv potential`);
  - `exists_solution`: with `margin ≥ 0` a forward solution on `[0, ∞)` exists from every state
    (the cylinder solution stays in a compact sublevel set; its angle is lifted back with
    `Dynamics.LaSalle.exists_angle_lift`);
  - `basin` (**basin estimate, PROVED**): with `margin ≥ 0`, `C_dc, L_s, R_s > 0`, `η ≠ 0` and
    `μ u* v₀ > 0`, the window `{|θ_dq| < π, H − S(0) < 2k}` below the saddle energy
    `H(±π, u*, î(±π)) − S(0) = 2k` lies in the region of attraction of the operating point
    (a forward solution exists from each such state, and every forward solution converges to
    `x*`); the angle cannot cross `±π` without energy `2k`, and the limit equilibrium must have
    energy below `2k`, hence `j = 0`;
  - `not_tendsto_critical_of_eta_eq_zero` (boundary): the hypothesis `η ≠ 0` cannot be dropped —
    for `η = 0` and `μ u* v₀ ≠ 0` the equilibrium `(π/2, u*, î(π/2))` is a constant solution that
    does not converge to the source's set (the source assumes `η > 0`).
* Connection conclusions on `MatchingStiffGrid.family` (the sentence-level shadow of the basin):
  `mem_den_locallyAsymptoticallyStable_of_dissipative` (with `margin ≥ 0`, `C_dc, L_s, R_s > 0`,
  `μ u* v₀ > 0`, `η ≠ 0` the operating point is locally asymptotically stable: Lyapunov stable,
  and a ball around it lies in the basin window), `boundaryModel_mem_den_locallyAsymptoticallyStable`
  (a concrete model with `margin = 0`), and the boundary `not_exact_locallyAsymptoticallyStable`
  (**REFUTED exactness**: the local asymptotic translation `{physical, synchronizing, damped,
  matching}` is sound but not exact; `boundaryModel` violates `damped`).

No synchronizing torque, `μ u* v₀ = 0` (outside the source's hypotheses; then `k = κ = 0`, `S` is
constant, every `(θ, u*, î(θ))` is an equilibrium, `field_eq_zero_of_kappa_eq_zero`, and
`H − S(0) = C_dc ũ²/2 + L_s ‖ĩ‖²/2`, `energy_eq_of_no_sync`). All with `C_dc, L_s, R_s > 0`.
* (a) `margin > 0`: the dissipation is uniformly definite, `dH/dt ≤ −ε(ũ² + ‖ĩ‖²)`
  (`energy_lie_le_sq`, any `μ u* v₀`), so `H` decays exponentially at `noSyncRate`
  (`energy_lie_le_noSyncRate`); `θ' = η ũ` is integrable and the angle settles.
  Private: `tendsto_equilibrium_of_no_sync` (every forward solution converges to one equilibrium
  `(θ∞, u*, î(θ∞))` — no drift), `lyapunovStable_of_no_sync`. Connection:
  `mem_den_lyapunovStable_of_no_sync` (Lyapunov stable), `noSyncModel_mem_den_lyapunovStable`,
  and the boundary `not_exact_lyapunovStable` (**REFUTED exactness**: the Lyapunov translation
  `{physical, synchronizing, dissipative}` is sound but not exact, `noSyncModel` has `v₀ = 0`).
* Any margin: `not_mem_den_locallyAsymptoticallyStable_of_no_sync`,
  `not_mem_den_locallyExponentiallyStable_of_no_sync` (with `R_s > 0` the equilibria accumulate at
  `x*`).
* (b) `margin = 0`, `μ = 0` (no modulation): `C_dc ũ' = 0`, the DC error is conserved
  (`utilde_const_of_mu_eq_zero`, private); `(θ₀ + η a t, u* + a, î(θ₀))` is a solution
  (`drift_isIntegralCurveOn`), so `not_tendsto_critical_of_mu_eq_zero` (private counterexample: no
  convergence to the source's set) and, for `η ≠ 0`, the connection `mem_den_unstable_of_mu_eq_zero`
  (the angle drifts away linearly from arbitrarily small DC offsets). With `η = 0` (frozen angle;
  any `margin ≥ 0`) the deviation dynamics is `z' = (0, −margin z₁/C_dc, −R_s z₂/L_s, −R_s z₃/L_s)`,
  so `⟨z, z'⟩ ≤ 0`: Lyapunov stable (private `lyapunovStable_of_frozen`, connection
  `mem_den_lyapunovStable_of_frozen`), not asymptotically.
* (c) `margin = 0`, `μ ≠ 0` (so `u* v₀ = 0`): `tendsto_error_of_no_sync_margin_zero` (private, LaSalle
  on the cylinder with the LaSalle-set argument `no_sync_margin_zero_segment`: `ũ_dc, ĩ_dq → 0`) and
  `tendsto_equilibrium_of_no_sync_margin_zero` (private: every forward solution converges to one
  equilibrium, for every `η`). Method: the rotation-reduced error `red x = (ũ, R_θᵀ ĩ)` solves the
  autonomous field `redField` (`red_field_identity`), whose Jacobian `redJac` is Hurwitz
  (`redJac_isHurwitz`, Routh–Hurwitz of `theorem.Criteria.Routh3`); local exponential stability
  then bounds `ũ` exponentially after the solution enters the ball, and
  `Dynamics.exists_tendsto_of_abs_deriv_le_exp` makes the angle converge. Lyapunov stability
  (private `lyapunovStable_of_no_sync_of_mu_ne_zero`, connection
  `mem_den_lyapunovStable_of_no_sync_of_mu_ne_zero`, for every `margin ≥ 0`): starting near `x*`
  the reduced error starts in the ball of local exponential stability (`red_bounds`), stays
  exponentially small, and the angle moves by at most `|η| C K₁ ‖x₀ − x*‖ / a`
  (`Dynamics.abs_sub_le_of_abs_deriv_le_exp`).
* Decision (connection `mem_den_lyapunovStable_iff_of_no_sync`): with `C_dc, L_s, R_s > 0`,
  `μ u* v₀ = 0` and `margin ≥ 0`, the operating point is Lyapunov stable iff
  `margin > 0 ∨ μ ≠ 0 ∨ η = 0`; it is never locally asymptotically stable (continuum of
  equilibria), and in the remaining case `margin = 0, μ = 0, η ≠ 0` it is unstable.

Source: work-sync `theory/T-dc-voltage-gfm.md` §1.2, `theory/T-gfm-control.md` §1.6,
`theory/papers/@arghir2020matching.md`; equations from the TPEL author version as listed in
`theorem.DCLink.MatchingStiffGrid`.
-/

noncomputable section
namespace powerlib.DCLink.MatchingStiffGrid
open powerlib.Dynamics (State)
open Set Filter Topology

namespace Model
variable (m : Model)

/-- The internal model `î_d` as a function of `(cos θ, sin θ) = (c, s)`. -/
def cD (c s : ℝ) : ℝ :=
  (m.Rs * (m.μ * m.ustar * s) + m.ω0 * m.Ls * (m.v0 - m.μ * m.ustar * c)) / m.N

/-- The internal model `î_q` as a function of `(cos θ, sin θ) = (c, s)`. -/
def cQ (c s : ℝ) : ℝ :=
  (-(m.ω0 * m.Ls) * (m.μ * m.ustar * s) + m.Rs * (m.v0 - m.μ * m.ustar * c)) / m.N

/-- The closed loop on the cylinder, state `(c, s, u_dc, i_d, i_q)` with `(c, s)` standing for
`(cos θ_dq, sin θ_dq)`: `c' = −s θ'`, `s' = c θ'`, `θ' = η u_dc − ω₀`, and the DC and current rows
of `field` with `sin θ_dq, cos θ_dq` replaced by `s, c`. -/
def cylField (y : State 5) : State 5 :=
  WithLp.toLp 2 ![
    -(y 1) * (m.η * y 2 - m.ω0),
    y 0 * (m.η * y 2 - m.ω0),
    (-m.Gdc * y 2 + (-m.Kp * (y 2 - m.ustar) + m.Gdc * m.ustar +
        -(m.μ * (-(y 1) * m.cD (y 0) (y 1) + y 0 * m.cQ (y 0) (y 1))) - m.κ * y 1) +
      m.μ * (-(y 1) * y 3 + y 0 * y 4)) / m.Cdc,
    (-(m.Rs * y 3 - m.ω0 * m.Ls * y 4) - m.μ * (-(y 1)) * y 2) / m.Ls,
    (-(m.ω0 * m.Ls * y 3 + m.Rs * y 4) + m.v0 - m.μ * y 0 * y 2) / m.Ls]

/-- The energy `H − S(0)` on the cylinder. -/
def cylEnergy (y : State 5) : ℝ :=
  m.Cdc / 2 * (y 2 - m.ustar) ^ 2 + m.k * (1 - y 0) +
    m.Ls / 2 * ((y 3 - m.cD (y 0) (y 1)) ^ 2 + (y 4 - m.cQ (y 0) (y 1)) ^ 2)

end Model

/-- The cylinder map `(θ, u, i_d, i_q) ↦ (cos θ, sin θ, u, i_d, i_q)`. -/
def cyl (x : State 4) : State 5 :=
  WithLp.toLp 2 ![Real.cos (x 0), Real.sin (x 0), x 1, x 2, x 3]

private theorem proj_contDiff {n : ℕ} (j : Fin n) : ContDiff ℝ 1 (fun x : State n => x j) :=
  (PiLp.proj 2 (fun _ : Fin n => ℝ) j : State n →L[ℝ] ℝ).contDiff

/-- The cylinder field at the image of a state is the cylinder image of the closed loop.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem cylField_cyl (m : Model) (x : State 4) :
    m.cylField (cyl x) = WithLp.toLp 2 ![-Real.sin (x 0) * m.field x 0,
      Real.cos (x 0) * m.field x 0, m.field x 1, m.field x 2, m.field x 3] := by
  ext i
  fin_cases i <;>
    simp [Model.cylField, cyl, Model.field, Model.idc, Model.ixHat, Model.iHatD, Model.iHatQ,
      Model.cD, Model.cQ]

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem cyl_contDiff : ContDiff ℝ 1 cyl := by
  have h0 := proj_contDiff (n := 4) 0
  have h1 := proj_contDiff (n := 4) 1
  have h2 := proj_contDiff (n := 4) 2
  have h3 := proj_contDiff (n := 4) 3
  rw [contDiff_euclidean]
  intro i
  fin_cases i <;> simp [cyl] <;> fun_prop

/-- The derivative of the cylinder map along a line. Static evidence, not a connection conclusion. -/
@[powerlib_foundation] theorem hasDerivAt_cyl_line (x v : State 4) :
    HasDerivAt (fun t : ℝ => cyl (x + t • v))
      (WithLp.toLp 2 ![-Real.sin (x 0) * v 0, Real.cos (x 0) * v 0, v 1, v 2, v 3]) 0 := by
  rw [← hasDerivWithinAt_univ]
  apply Dynamics.hasDerivWithinAt_euclidean_of_coord
  intro i
  rw [hasDerivWithinAt_univ]
  have hlin : ∀ j : Fin 4, HasDerivAt (fun t : ℝ => x j + t * v j) (v j) 0 := fun j => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v j)).const_add (x j)
  fin_cases i
  · have h := (Real.hasDerivAt_cos (x 0)).comp_of_eq (0 : ℝ) (hlin 0) (by simp)
    convert h using 1
    · funext t; simp [cyl]
    · simp
  · have h := (Real.hasDerivAt_sin (x 0)).comp_of_eq (0 : ℝ) (hlin 0) (by simp)
    convert h using 1
    · funext t; simp [cyl]
    · simp
  · convert hlin 1 using 1
    · funext t; simp [cyl]
    · simp
  · convert hlin 2 using 1
    · funext t; simp [cyl]
    · simp
  · convert hlin 3 using 1
    · funext t; simp [cyl]
    · simp

/-- `D cyl x (field x) = cylField (cyl x)`: the cylinder map is a semiconjugacy.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem fderiv_cyl_field (m : Model) (x : State 4) :
    fderiv ℝ cyl x (m.field x) = m.cylField (cyl x) := by
  rw [Dynamics.fderiv_apply_eq_of_hasDerivAt_line
    ((cyl_contDiff.differentiable (by norm_num)) x) (hasDerivAt_cyl_line x _), cylField_cyl]

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem energy_eq_cylEnergy (m : Model) :
    m.energy = fun x => m.cylEnergy (cyl x) := by
  funext x
  simp [Model.energy, Model.cylEnergy, cyl, Model.iHatD, Model.iHatQ, Model.cD, Model.cQ]

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem cylEnergy_contDiff (m : Model) : ContDiff ℝ 1 m.cylEnergy := by
  have h0 := proj_contDiff (n := 5) 0
  have h1 := proj_contDiff (n := 5) 1
  have h2 := proj_contDiff (n := 5) 2
  have h3 := proj_contDiff (n := 5) 3
  have h4 := proj_contDiff (n := 5) 4
  unfold Model.cylEnergy Model.cD Model.cQ
  fun_prop

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem cylField_contDiff (m : Model) : ContDiff ℝ 1 m.cylField := by
  have h0 := proj_contDiff (n := 5) 0
  have h1 := proj_contDiff (n := 5) 1
  have h2 := proj_contDiff (n := 5) 2
  have h3 := proj_contDiff (n := 5) 3
  have h4 := proj_contDiff (n := 5) 4
  rw [contDiff_euclidean]
  intro i
  fin_cases i <;> simp [Model.cylField, Model.cD, Model.cQ] <;> fun_prop

/-- The Lie derivative of the cylinder energy at the image of a state is that of `H − S(0)`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem cylLie_cyl (m : Model) (x : State 4) :
    fderiv ℝ m.cylEnergy (cyl x) (m.cylField (cyl x)) = fderiv ℝ m.energy x (m.field x) := by
  have e : m.energy = m.cylEnergy ∘ cyl := energy_eq_cylEnergy m
  rw [e, fderiv_comp x ((cylEnergy_contDiff m).differentiable (by norm_num) _)
    ((cyl_contDiff.differentiable (by norm_num)) x), ContinuousLinearMap.comp_apply,
    fderiv_cyl_field]

/-! ## The cylinder -/

/-- Coordinates of the cylinder map. Static evidence on the model, not a connection conclusion. -/
@[simp, powerlib_foundation] theorem cyl_apply (x : State 4) :
    cyl x 0 = Real.cos (x 0) ∧ cyl x 1 = Real.sin (x 0) ∧ cyl x 2 = x 1 ∧ cyl x 3 = x 2 ∧
      cyl x 4 = x 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [cyl]

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem cD_cos_sin (m : Model) (θ : ℝ) :
    m.cD (Real.cos θ) (Real.sin θ) = m.iHatD θ := rfl

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem cQ_cos_sin (m : Model) (θ : ℝ) :
    m.cQ (Real.cos θ) (Real.sin θ) = m.iHatQ θ := rfl

private theorem circle_contDiff : ContDiff ℝ 1 (fun y : State 5 => y 0 ^ 2 + y 1 ^ 2) := by
  have h0 := proj_contDiff (n := 5) 0
  have h1 := proj_contDiff (n := 5) 1
  fun_prop

/-- The circle `c² + s² = 1` is a first integral of the cylinder field.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem fderiv_circle_cylField (m : Model) (y : State 5) :
    fderiv ℝ (fun y : State 5 => y 0 ^ 2 + y 1 ^ 2) y (m.cylField y) = 0 := by
  let p : Fin 5 → State 5 →L[ℝ] ℝ := fun j => PiLp.proj 2 (fun _ : Fin 5 => ℝ) j
  have hp : ∀ j, HasFDerivAt (fun x : State 5 => x j) (p j) y := fun j => (p j).hasFDerivAt
  have h : HasFDerivAt (fun y : State 5 => y 0 ^ 2 + y 1 ^ 2) _ y :=
    ((hp 0).pow 2).add ((hp 1).pow 2)
  rw [h.fderiv]
  simp [p, Model.cylField]
  ring

/-- Every point of the cylinder `c² + s² = 1` is the image of a state.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem exists_cyl_eq {y : State 5} (hy : y 0 ^ 2 + y 1 ^ 2 = 1) :
    ∃ x : State 4, cyl x = y := by
  obtain ⟨θ, hc, hs⟩ := Dynamics.LaSalle.exists_cos_sin hy
  refine ⟨WithLp.toLp 2 ![θ, y 2, y 3, y 4], ?_⟩
  ext i
  fin_cases i <;> simp [cyl, hc, hs]

/-- On the cylinder `dH/dt ≤ −margin ũ²`. Static evidence on the model, not a connection
conclusion. -/
@[powerlib_foundation] theorem cylLie_le (m : Model) (hR : 0 < m.Rs) (hL : m.Ls ≠ 0)
    (hC : m.Cdc ≠ 0) {y : State 5} (hy : y 0 ^ 2 + y 1 ^ 2 = 1) :
    fderiv ℝ m.cylEnergy y (m.cylField y) ≤ -m.margin * (y 2 - m.ustar) ^ 2 := by
  obtain ⟨x, rfl⟩ := exists_cyl_eq hy
  rw [cylLie_cyl]
  simpa using energy_lie_le m hR hL hC x

private theorem N_pos (m : Model) (hR : 0 < m.Rs) : 0 < m.N := by
  unfold Model.N
  have := sq_nonneg m.ω0
  positivity

/-- On the cylinder, with `margin > 0`, `dH/dt = 0` only where `ũ_dc = 0` and `ĩ_dq = 0`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem cylLie_eq_zero (m : Model) (hR : 0 < m.Rs) (hL : 0 < m.Ls)
    (hC : 0 < m.Cdc) (hδ : 0 < m.margin) {y : State 5} (hy : y 0 ^ 2 + y 1 ^ 2 = 1)
    (h0 : fderiv ℝ m.cylEnergy y (m.cylField y) = 0) :
    y 2 = m.ustar ∧ y 3 = m.cD (y 0) (y 1) ∧ y 4 = m.cQ (y 0) (y 1) := by
  obtain ⟨x, rfl⟩ := exists_cyl_eq hy
  rw [cylLie_cyl] at h0
  have hle := energy_lie_le m hR hL.ne' hC.ne' x
  have hu : x 1 = m.ustar := by
    have h1 : m.margin * (x 1 - m.ustar) ^ 2 ≤ 0 := by linarith
    have h2 : (x 1 - m.ustar) ^ 2 = 0 :=
      le_antisymm ((mul_nonpos_iff_pos_imp_nonpos.mp h1).1 hδ |> fun h => by
        nlinarith [sq_nonneg (x 1 - m.ustar)]) (sq_nonneg _)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    linarith
  have hl := energy_lie m (N_pos m hR).ne' hL.ne' hC.ne' x
  rw [h0, hu, sub_self] at hl
  have hsum : m.Rs * ((x 2 - m.iHatD (x 0)) ^ 2 + (x 3 - m.iHatQ (x 0)) ^ 2) = 0 := by
    linarith
  have hsum' := (mul_eq_zero.mp hsum).resolve_left hR.ne'
  have e1 : (x 2 - m.iHatD (x 0)) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x 2 - m.iHatD (x 0)), sq_nonneg (x 3 - m.iHatQ (x 0))]
  have e2 : (x 3 - m.iHatQ (x 0)) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x 2 - m.iHatD (x 0)), sq_nonneg (x 3 - m.iHatQ (x 0))]
  have e1' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e1
  have e2' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e2
  simp only [cyl_apply, cD_cos_sin, cQ_cos_sin]
  exact ⟨hu, by linarith, by linarith⟩

/-- On the set `ũ_dc = 0`, `ĩ_dq = 0` the DC row of the cylinder field is `−κ s / C_dc`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem cylField_two_of_mem (m : Model) {y : State 5}
    (h2 : y 2 = m.ustar) (h3 : y 3 = m.cD (y 0) (y 1)) (h4 : y 4 = m.cQ (y 0) (y 1)) :
    m.cylField y 2 = -(m.κ * y 1) / m.Cdc := by
  simp only [Model.cylField, PiLp.toLp_apply, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [h2, h3, h4]
  ring

/-- `î_d² + î_q² = ‖μ u* (−s, c) − v₀ e₂‖² / N` on the cylinder coordinates.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem cD_sq_add_cQ_sq (m : Model) (hN : m.N ≠ 0) (c s : ℝ) :
    m.cD c s ^ 2 + m.cQ c s ^ 2 =
      ((m.μ * m.ustar * s) ^ 2 + (m.v0 - m.μ * m.ustar * c) ^ 2) / m.N := by
  have hZ : (m.Rs * (m.μ * m.ustar * s) + m.ω0 * m.Ls * (m.v0 - m.μ * m.ustar * c)) ^ 2 +
      (-(m.ω0 * m.Ls) * (m.μ * m.ustar * s) + m.Rs * (m.v0 - m.μ * m.ustar * c)) ^ 2 =
      m.N * ((m.μ * m.ustar * s) ^ 2 + (m.v0 - m.μ * m.ustar * c) ^ 2) := by
    simp only [Model.N]
    ring
  rw [Model.cD, Model.cQ, div_pow, div_pow, ← add_div, hZ]
  field_simp

/-- The sublevel sets of the energy on the cylinder are compact.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem isCompact_cylSublevel (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls)
    (hR : 0 < m.Rs) (c : ℝ) :
    IsCompact {y : State 5 | y 0 ^ 2 + y 1 ^ 2 = 1 ∧ m.cylEnergy y ≤ c} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_eq circle_contDiff.continuous continuous_const).inter
      (isClosed_le (cylEnergy_contDiff m).continuous continuous_const)
  · rw [isBounded_iff_forall_norm_le]
    have hN := N_pos m hR
    set K := |m.k|
    set Q := m.μ ^ 2 * m.ustar ^ 2 + m.v0 ^ 2 with hQ
    refine ⟨Real.sqrt (1 + 4 * (c + 2 * K) / m.Cdc + 2 * m.ustar ^ 2 + 4 * (c + 2 * K) / m.Ls +
      4 * Q / m.N), ?_⟩
    rintro y ⟨hy, hV⟩
    rw [EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_five]
    have hy0 : |y 0| ≤ 1 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (y 1), sq_nonneg (y 0 + 1), sq_nonneg (y 0 - 1)]
    have hk : -(2 * K) ≤ m.k * (1 - y 0) := by
      have h1 : |1 - y 0| ≤ 2 := by
        rw [abs_le] at hy0 ⊢
        constructor <;> linarith
      have : |m.k * (1 - y 0)| ≤ 2 * K := by
        rw [abs_mul]
        nlinarith [abs_nonneg m.k, abs_nonneg (1 - y 0)]
      linarith [neg_abs_le (m.k * (1 - y 0))]
    unfold Model.cylEnergy at hV
    set e1 := y 3 - m.cD (y 0) (y 1) with he1
    set e2 := y 4 - m.cQ (y 0) (y 1) with he2
    have hu : (y 2 - m.ustar) ^ 2 ≤ 2 * (c + 2 * K) / m.Cdc := by
      rw [le_div_iff₀ hC]
      nlinarith [sq_nonneg e1, sq_nonneg e2, sq_nonneg (y 2 - m.ustar)]
    have he : e1 ^ 2 + e2 ^ 2 ≤ 2 * (c + 2 * K) / m.Ls := by
      rw [le_div_iff₀ hL]
      nlinarith [sq_nonneg e1, sq_nonneg e2, sq_nonneg (y 2 - m.ustar)]
    have hab : (m.μ * m.ustar * y 1) ^ 2 + (m.v0 - m.μ * m.ustar * y 0) ^ 2 ≤ 2 * Q := by
      have e : (m.μ * m.ustar * y 1) ^ 2 + (m.v0 - m.μ * m.ustar * y 0) ^ 2 =
          (m.μ * m.ustar) ^ 2 * (y 0 ^ 2 + y 1 ^ 2) - 2 * m.v0 * (m.μ * m.ustar) * y 0 +
            m.v0 ^ 2 := by ring
      rw [e, hy, hQ]
      have h1 : 0 ≤ 1 - y 0 ^ 2 := by nlinarith [sq_nonneg (y 1)]
      nlinarith [sq_nonneg (m.μ * m.ustar * y 0 + m.v0), mul_nonneg (sq_nonneg (m.μ * m.ustar)) h1]
    have hcd : m.cD (y 0) (y 1) ^ 2 + m.cQ (y 0) (y 1) ^ 2 ≤ 2 * Q / m.N := by
      rw [cD_sq_add_cQ_sq m hN.ne']
      exact div_le_div_of_nonneg_right hab hN.le
    have h3 : y 3 = e1 + m.cD (y 0) (y 1) := by linarith [he1]
    have h4 : y 4 = e2 + m.cQ (y 0) (y 1) := by linarith [he2]
    have h34 : y 3 ^ 2 + y 4 ^ 2 ≤ 2 * (e1 ^ 2 + e2 ^ 2) +
        2 * (m.cD (y 0) (y 1) ^ 2 + m.cQ (y 0) (y 1) ^ 2) := by
      rw [h3, h4]
      linarith [sq_nonneg (e1 - m.cD (y 0) (y 1)), sq_nonneg (e2 - m.cQ (y 0) (y 1))]
    have h2 : y 2 ^ 2 ≤ 2 * (y 2 - m.ustar) ^ 2 + 2 * m.ustar ^ 2 := by
      linarith [sq_nonneg (y 2 - 2 * m.ustar)]
    have e4 : 4 * (c + 2 * K) / m.Cdc = 2 * (2 * (c + 2 * K) / m.Cdc) := by ring
    have e5 : 4 * (c + 2 * K) / m.Ls = 2 * (2 * (c + 2 * K) / m.Ls) := by ring
    have e6 : 4 * Q / m.N = 2 * (2 * Q / m.N) := by ring
    rw [e4, e5, e6]
    linarith

/-- On the cylinder, with `margin = 0`, `dH/dt = 0` only where
`2 R_s N ĩ + μ ω₀ L_s ũ z(θ) = 0`. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem cylLie_eq_zero_of_margin_eq_zero (m : Model) (hR : 0 < m.Rs) (hL : 0 < m.Ls)
    (hC : 0 < m.Cdc) (hm : m.margin = 0) {y : State 5} (hy : y 0 ^ 2 + y 1 ^ 2 = 1)
    (h0 : fderiv ℝ m.cylEnergy y (m.cylField y) = 0) :
    y 3 - m.cD (y 0) (y 1) = -(m.μ * m.ω0 * m.Ls / (2 * m.Rs * m.N)) * (y 2 - m.ustar) *
        (m.Rs * y 0 + m.ω0 * m.Ls * y 1) ∧
      y 4 - m.cQ (y 0) (y 1) = -(m.μ * m.ω0 * m.Ls / (2 * m.Rs * m.N)) * (y 2 - m.ustar) *
        (m.Rs * y 1 - m.ω0 * m.Ls * y 0) := by
  have hN := N_pos m hR
  obtain ⟨x, rfl⟩ := exists_cyl_eq hy
  rw [cylLie_cyl, energy_lie m hN.ne' hL.ne' hC.ne' x] at h0
  simp only [cyl_apply, cD_cos_sin, cQ_cos_sin]
  set u := x 1 - m.ustar
  set e1 := x 2 - m.iHatD (x 0)
  set e2 := x 3 - m.iHatQ (x 0)
  set z1 := m.Rs * Real.cos (x 0) + m.ω0 * m.Ls * Real.sin (x 0)
  set z2 := m.Rs * Real.sin (x 0) - m.ω0 * m.Ls * Real.cos (x 0)
  set B := m.μ * m.ω0 * m.Ls
  have hz : z1 ^ 2 + z2 ^ 2 = m.N := by
    simp only [z1, z2, Model.N]
    linear_combination (m.Rs ^ 2 + m.ω0 ^ 2 * m.Ls ^ 2) * Real.sin_sq_add_cos_sq (x 0)
  set β := B / m.N with hβdef
  have hβ : β * m.N = B := div_mul_cancel₀ _ hN.ne'
  set γ := B ^ 2 / (4 * m.Rs * m.N) with hγdef
  have hγ : γ * (4 * m.Rs * m.N) = B ^ 2 := div_mul_cancel₀ _ (by positivity)
  have hGK : m.Gdc + m.Kp = γ := by
    have : m.margin = m.Gdc + m.Kp - γ := by
      simp only [Model.margin, γ, B]
      ring
    linarith
  clear_value u e1 e2 z1 z2 β γ
  have key : (2 * m.Rs * m.N * e1 + B * u * z1) ^ 2 + (2 * m.Rs * m.N * e2 + B * u * z2) ^ 2 = 0 := by
    linear_combination (-4 * m.Rs * m.N ^ 2) * h0 - 4 * m.Rs * m.N ^ 2 * u ^ 2 * hGK
      - m.N * u ^ 2 * hγ - 4 * m.Rs * m.N * u * (e1 * z1 + e2 * z2) * hβ + B ^ 2 * u ^ 2 * hz
  have k1 : 2 * m.Rs * m.N * e1 + B * u * z1 = 0 := by
    nlinarith [sq_nonneg (2 * m.Rs * m.N * e1 + B * u * z1), sq_nonneg (2 * m.Rs * m.N * e2 + B * u * z2)]
  have k2 : 2 * m.Rs * m.N * e2 + B * u * z2 = 0 := by
    nlinarith [sq_nonneg (2 * m.Rs * m.N * e1 + B * u * z1), sq_nonneg (2 * m.Rs * m.N * e2 + B * u * z2)]
  have h2RN : 2 * m.Rs * m.N ≠ 0 := by positivity
  constructor
  · field_simp
    linear_combination k1
  · field_simp
    linear_combination k2

/-- On the set `ĩ = −c ũ z(θ)` of the cylinder (`c = μω₀L_s/(2R_sN)`), the energy is a pendulum
energy `a ũ²/2 + k(1 − cos θ)` with `a = C_dc + L_s c² N`. Static evidence on the model, not a
connection conclusion. -/
@[powerlib_foundation] theorem cylEnergy_of_rel (m : Model) {y : State 5} (hy : y 0 ^ 2 + y 1 ^ 2 = 1)
    (h3 : y 3 - m.cD (y 0) (y 1) = -(m.μ * m.ω0 * m.Ls / (2 * m.Rs * m.N)) * (y 2 - m.ustar) *
        (m.Rs * y 0 + m.ω0 * m.Ls * y 1))
    (h4 : y 4 - m.cQ (y 0) (y 1) = -(m.μ * m.ω0 * m.Ls / (2 * m.Rs * m.N)) * (y 2 - m.ustar) *
        (m.Rs * y 1 - m.ω0 * m.Ls * y 0)) :
    m.cylEnergy y = (m.Cdc + m.Ls * (m.μ * m.ω0 * m.Ls / (2 * m.Rs * m.N)) ^ 2 * m.N) / 2 *
      (y 2 - m.ustar) ^ 2 + m.k * (1 - y 0) := by
  unfold Model.cylEnergy
  rw [h3, h4]
  have hz : (m.Rs * y 0 + m.ω0 * m.Ls * y 1) ^ 2 + (m.Rs * y 1 - m.ω0 * m.Ls * y 0) ^ 2 = m.N := by
    simp only [Model.N]
    linear_combination (m.Rs ^ 2 + m.ω0 ^ 2 * m.Ls ^ 2) * hy
  linear_combination (m.Ls / 2 * (m.μ * m.ω0 * m.Ls / (2 * m.Rs * m.N)) ^ 2 *
    (y 2 - m.ustar) ^ 2) * hz

/-- On the same set, with `margin = 0`, the DC row is `C_dc ũ' = g ũ − κ s`,
`g = (μω₀L_s)²/(4R_sN)`: a pendulum with negative damping. Static evidence on the model, not a
connection conclusion. -/
@[powerlib_foundation] theorem cylField_two_of_rel (m : Model) (hC : m.Cdc ≠ 0) (hm : m.margin = 0) {y : State 5}
    (hy : y 0 ^ 2 + y 1 ^ 2 = 1)
    (h3 : y 3 - m.cD (y 0) (y 1) = -(m.μ * m.ω0 * m.Ls / (2 * m.Rs * m.N)) * (y 2 - m.ustar) *
        (m.Rs * y 0 + m.ω0 * m.Ls * y 1))
    (h4 : y 4 - m.cQ (y 0) (y 1) = -(m.μ * m.ω0 * m.Ls / (2 * m.Rs * m.N)) * (y 2 - m.ustar) *
        (m.Rs * y 1 - m.ω0 * m.Ls * y 0)) :
    m.Cdc * m.cylField y 2 =
      (m.μ * m.ω0 * m.Ls) ^ 2 / (4 * m.Rs * m.N) * (y 2 - m.ustar) - m.κ * y 1 := by
  have hGK : m.Gdc + m.Kp = (m.μ * m.ω0 * m.Ls) ^ 2 / (4 * m.Rs * m.N) := by
    have : m.margin = m.Gdc + m.Kp - (m.μ * m.ω0 * m.Ls) ^ 2 / (4 * m.Rs * m.N) := by
      simp only [Model.margin]
      ring
    linarith
  have h3' : y 3 = m.cD (y 0) (y 1) + -(m.μ * m.ω0 * m.Ls / (2 * m.Rs * m.N)) * (y 2 - m.ustar) *
      (m.Rs * y 0 + m.ω0 * m.Ls * y 1) := by linarith
  have h4' : y 4 = m.cQ (y 0) (y 1) + -(m.μ * m.ω0 * m.Ls / (2 * m.Rs * m.N)) * (y 2 - m.ustar) *
      (m.Rs * y 1 - m.ω0 * m.Ls * y 0) := by linarith
  have e : m.cylField y 2 = (-m.Gdc * y 2 + (-m.Kp * (y 2 - m.ustar) + m.Gdc * m.ustar +
        -(m.μ * (-(y 1) * m.cD (y 0) (y 1) + y 0 * m.cQ (y 0) (y 1))) - m.κ * y 1) +
      m.μ * (-(y 1) * y 3 + y 0 * y 4)) / m.Cdc := by
    simp [Model.cylField]
  rw [e, mul_div_cancel₀ _ hC, h3', h4']
  linear_combination (-(y 2 - m.ustar)) * hGK +
    (2 * ((m.μ * m.ω0 * m.Ls) ^ 2 / (4 * m.Rs * m.N)) * (y 2 - m.ustar)) * hy

/-- `∇S(θ) = k sin θ`. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem hasDerivAt_potential (m : Model) (hN : m.N ≠ 0) (θ : ℝ) :
    HasDerivAt m.potential (m.k * Real.sin θ) θ := by
  have e : m.potential = fun θ => m.potential 0 + m.k * (1 - Real.cos θ) := by
    funext θ
    rw [← potential_sub_potential_zero m hN θ]
    ring
  rw [e]
  convert (((Real.hasDerivAt_cos θ).const_sub 1).const_mul m.k).const_add (m.potential 0) using 1
  ring

private theorem k_ne_zero (m : Model) (hL : 0 < m.Ls) (hR : 0 < m.Rs)
    (hs : m.μ * m.ustar * m.v0 ≠ 0) : m.k ≠ 0 := by
  unfold Model.k
  have : m.Ls * m.μ * m.ustar * m.v0 = m.Ls * (m.μ * m.ustar * m.v0) := by ring
  rw [this]
  exact div_ne_zero (mul_ne_zero hL.ne' hs) (N_pos m hR).ne'

private theorem iHatD_continuous (m : Model) : Continuous m.iHatD :=
  continuous_iff_continuousAt.2 fun θ => (hasDerivAt_iHatD m θ).continuousAt

private theorem iHatQ_continuous (m : Model) : Continuous m.iHatQ :=
  continuous_iff_continuousAt.2 fun θ => (hasDerivAt_iHatQ m θ).continuousAt

/-- **LaSalle set at `margin = 0`.** A solution segment of positive length of the cylinder field
that stays on the cylinder where `dH/dt = 0` starts at `{s = 0, ũ = 0, ĩ = 0}`: on that set the
motion is a negatively damped pendulum `C_dc ũ' = g ũ − κ s`, `θ' = η ũ` of constant energy
`a ũ²/2 + k(1 − cos θ)`; where `ũ ≠ 0` the two force `a g ũ = (a − C_dc) κ s` and then
`cos θ = const`, contradicting `θ' = η ũ ≠ 0`. -/
private theorem margin_zero_segment (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls) (hR : 0 < m.Rs)
    (hη : m.η ≠ 0) (hs : m.μ * m.ustar * m.v0 ≠ 0) (hm : m.margin = 0) {T : ℝ}
    {ψ : ℝ → State 5} (hT : 0 < T) (hψ : IsTrajectoryOn ψ m.cylField 0 T)
    (hE : ∀ t ∈ Icc 0 T, ψ t 0 ^ 2 + ψ t 1 ^ 2 = 1 ∧
      fderiv ℝ m.cylEnergy (ψ t) (m.cylField (ψ t)) = 0) :
    ψ 0 1 = 0 ∧ ψ 0 2 = m.ustar ∧ ψ 0 3 = m.cD (ψ 0 0) (ψ 0 1) ∧
      ψ 0 4 = m.cQ (ψ 0 0) (ψ 0 1) := by
  have hN := N_pos m hR
  have hμ : m.μ ≠ 0 := fun h => hs (by rw [h]; ring)
  have hu : m.ustar ≠ 0 := fun h => hs (by rw [h]; ring)
  have hω : m.ω0 ≠ 0 := mul_ne_zero hη hu
  have hB : m.μ * m.ω0 * m.Ls ≠ 0 := mul_ne_zero (mul_ne_zero hμ hω) hL.ne'
  have hκ : m.κ ≠ 0 := by
    rw [← eta_mul_k]
    exact mul_ne_zero hη (k_ne_zero m hL hR hs)
  have hrel := fun t (ht : t ∈ Icc 0 T) =>
    cylLie_eq_zero_of_margin_eq_zero m hR hL hC hm (hE t ht).1 (hE t ht).2
  have hEn := fun t (ht : t ∈ Icc 0 T) =>
    cylEnergy_of_rel m (hE t ht).1 (hrel t ht).1 (hrel t ht).2
  have hDC := fun t (ht : t ∈ Icc 0 T) =>
    cylField_two_of_rel m hC.ne' hm (hE t ht).1 (hrel t ht).1 (hrel t ht).2
  set cc := m.μ * m.ω0 * m.Ls / (2 * m.Rs * m.N) with hccdef
  set g := (m.μ * m.ω0 * m.Ls) ^ 2 / (4 * m.Rs * m.N) with hgdef
  set a := m.Cdc + m.Ls * cc ^ 2 * m.N with hadef
  have hcc : cc ≠ 0 := div_ne_zero hB (by positivity)
  have hg : 0 < g := div_pos (by positivity) (by positivity)
  have haC : 0 < a - m.Cdc := by
    have : a - m.Cdc = m.Ls * cc ^ 2 * m.N := by rw [hadef]; ring
    rw [this]
    positivity
  have ha : 0 < a := by linarith
  clear_value cc g a
  have hF0 : ∀ y : State 5, m.cylField y 0 = -(y 1) * (m.η * (y 2 - m.ustar)) := fun y => by
    simp only [Model.cylField, Model.ω0, PiLp.toLp_apply, Matrix.cons_val_zero]
    ring
  have hF1 : ∀ y : State 5, m.cylField y 1 = y 0 * (m.η * (y 2 - m.ustar)) := fun y => by
    simp only [Model.cylField, Model.ω0, PiLp.toLp_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    ring
  have hco : ∀ {I : Set ℝ}, I ⊆ Icc 0 T → ∀ t ∈ I, ∀ i,
      HasDerivWithinAt (fun τ => ψ τ i) (m.cylField (ψ t) i) I t :=
    fun hI t ht i => Dynamics.HasDerivWithinAt.euclidean_coord ((hψ t (hI ht)).mono hI) i
  have hcont2 : Continuous (fun y : State 5 => y 2) := (proj_contDiff 2).continuous
  -- `ũ` vanishes on `[0, T)`
  have hA : ∀ t₀ ∈ Ico 0 T, ψ t₀ 2 = m.ustar := by
    intro t₀ ht₀
    by_contra hne
    obtain ⟨t₁, h01, h1T, hU⟩ := Dynamics.exists_Icc_mem_of_isOpen hψ.continuousOn
      (U := {y : State 5 | y 2 ≠ m.ustar}) (isOpen_ne_fun hcont2 continuous_const) ht₀ hne
    have hsub : Icc t₀ t₁ ⊆ Icc 0 T := Icc_subset_Icc ht₀.1 h1T
    have hR1 : ∀ t ∈ Icc t₀ t₁, a * g * (ψ t 2 - m.ustar) = (a - m.Cdc) * m.κ * ψ t 1 := by
      intro t ht
      have d1 : HasDerivWithinAt (fun τ => m.cylEnergy (ψ τ))
          (fderiv ℝ m.cylEnergy (ψ t) (m.cylField (ψ t))) (Icc t₀ t₁) t :=
        ((cylEnergy_contDiff m).differentiable (by norm_num) (ψ t)).hasFDerivAt.comp_hasDerivWithinAt
          t ((hψ t (hsub ht)).mono hsub)
      rw [(hE t (hsub ht)).2] at d1
      have d1' : HasDerivWithinAt (fun τ => a / 2 * (ψ τ 2 - m.ustar) ^ 2 + m.k * (1 - ψ τ 0)) 0
          (Icc t₀ t₁) t :=
        d1.congr (fun τ hτ => (hEn τ (hsub hτ)).symm) (hEn t (hsub ht)).symm
      have d2 : HasDerivWithinAt (fun τ => a / 2 * (ψ τ 2 - m.ustar) ^ 2 + m.k * (1 - ψ τ 0))
          (a / 2 * (2 * (ψ t 2 - m.ustar) * m.cylField (ψ t) 2) +
            m.k * (-(m.cylField (ψ t) 0))) (Icc t₀ t₁) t := by
        have h2 := hco hsub t ht 2
        have h0 := hco hsub t ht 0
        convert (((h2.sub_const m.ustar).pow 2).const_mul (a / 2)).add
          ((h0.const_sub 1).const_mul m.k) using 1
        simp only [Nat.cast_ofNat]
        ring
      have heq := (uniqueDiffOn_Icc h01 t ht).eq_deriv _ d2 d1'
      rw [hF0] at heq
      have hut : ψ t 2 - m.ustar ≠ 0 := sub_ne_zero.mpr (hU t ht)
      have h1 : a * m.cylField (ψ t) 2 + m.κ * ψ t 1 = 0 := by
        have : (ψ t 2 - m.ustar) * (a * m.cylField (ψ t) 2 + m.κ * ψ t 1) = 0 := by
          rw [← eta_mul_k]
          linear_combination heq
        exact (mul_eq_zero.mp this).resolve_left hut
      linear_combination m.Cdc * h1 - a * hDC t (hsub ht)
    have hR2 : ∀ t ∈ Icc t₀ t₁,
        a * g * m.cylField (ψ t) 2 = (a - m.Cdc) * m.κ * m.cylField (ψ t) 1 := by
      intro t ht
      have dG : HasDerivWithinAt (fun τ => a * g * (ψ τ 2 - m.ustar) - (a - m.Cdc) * m.κ * ψ τ 1)
          (a * g * m.cylField (ψ t) 2 - (a - m.Cdc) * m.κ * m.cylField (ψ t) 1) (Icc t₀ t₁) t :=
        (((hco hsub t ht 2).sub_const m.ustar).const_mul (a * g)).sub
          ((hco hsub t ht 1).const_mul ((a - m.Cdc) * m.κ))
      have := Dynamics.HasDerivWithinAt.eq_zero_of_eqOn_Icc h01 ht dG (c := 0)
        (fun τ hτ => by rw [hR1 τ hτ]; ring)
      linarith
    have hc : ∀ t ∈ Icc t₀ t₁,
        ψ t 0 = -(a * g ^ 2) / ((a - m.Cdc) ^ 2 * m.κ * m.η) := by
      intro t ht
      have r1 := hR1 t ht
      have r2 := hR2 t ht
      rw [hF1] at r2
      have hDCt := hDC t (hsub ht)
      have hut : ψ t 2 - m.ustar ≠ 0 := sub_ne_zero.mpr (hU t ht)
      have key : ψ t 0 * ((a - m.Cdc) ^ 2 * m.κ * m.η) * (m.Cdc * (ψ t 2 - m.ustar)) =
          -(a * g ^ 2) * (m.Cdc * (ψ t 2 - m.ustar)) := by
        linear_combination (-(a - m.Cdc) * m.Cdc) * r2 + ((a - m.Cdc) * a * g) * hDCt +
          (a * g) * r1
      have key' := mul_right_cancel₀ (mul_ne_zero hC.ne' hut) key
      rw [eq_div_iff (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 haC.ne') hκ) hη)]
      exact key'
    have ht₀I : t₀ ∈ Icc t₀ t₁ := ⟨le_rfl, h01.le⟩
    have hd0 := Dynamics.HasDerivWithinAt.eq_zero_of_eqOn_Icc h01 ht₀I (hco hsub t₀ ht₀I 0) hc
    rw [hF0] at hd0
    have hut₀ : ψ t₀ 2 - m.ustar ≠ 0 := sub_ne_zero.mpr hne
    have hs₀ : ψ t₀ 1 = 0 := by
      have : ψ t₀ 1 * (m.η * (ψ t₀ 2 - m.ustar)) = 0 := by linear_combination -hd0
      exact (mul_eq_zero.mp this).resolve_right (mul_ne_zero hη hut₀)
    have r1 := hR1 t₀ ht₀I
    rw [hs₀, mul_zero] at r1
    exact hut₀ ((mul_eq_zero.mp r1).resolve_left (mul_ne_zero ha.ne' hg.ne'))
  -- at the initial time
  have hT2 : (0 : ℝ) < T / 2 := by linarith
  have hsub2 : Icc 0 (T / 2) ⊆ Icc 0 T := Icc_subset_Icc le_rfl (by linarith)
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hu0 : ψ 0 2 = m.ustar := hA 0 ⟨le_rfl, hT⟩
  have hg2 : m.cylField (ψ 0) 2 = 0 :=
    Dynamics.HasDerivWithinAt.eq_zero_of_eqOn_Icc hT2 ⟨le_rfl, hT2.le⟩
      (hco hsub2 0 ⟨le_rfl, hT2.le⟩ 2) (fun τ hτ => hA τ ⟨hτ.1, by linarith [hτ.2]⟩)
  have hDC0 := hDC 0 h0T
  rw [hg2, mul_zero, hu0, sub_self, mul_zero, zero_sub] at hDC0
  have hs0 : ψ 0 1 = 0 := by
    have : m.κ * ψ 0 1 = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hκ
  obtain ⟨r3, r4⟩ := hrel 0 h0T
  rw [hu0, sub_self, mul_zero, zero_mul] at r3 r4
  exact ⟨hs0, hu0, by linarith, by linarith⟩
/-! ## LaSalle on the cylinder (implementation evidence)

The conclusions below are trajectory-level statements (convergence to a set, to one of several
equilibria, region-of-attraction estimates), outside the sentence language of the library;
they are private implementation evidence about the concrete model (Rules §3a). The generic tools
they instantiate are the public foundation results of `theorem.Dynamics.LaSalle.Periodic`. -/

/-- The image of every forward solution on the cylinder converges to the set
`{s = 0, u = u*, i = î(c, s)}`. -/
private theorem tendsto_cyl (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls) (hR : 0 < m.Rs)
    (hη : m.η ≠ 0) (hs : m.μ * m.ustar * m.v0 ≠ 0) (hδ : 0 ≤ m.margin) {φ : ℝ → State 4}
    (hφ : IsIntegralCurveOn φ (fun _ x => m.field x) (Ici 0)) :
    Tendsto (fun t => cyl (φ t)) atTop (𝓝ˢ {y : State 5 | y 1 = 0 ∧ y 2 = m.ustar ∧
      y 3 = m.cD (y 0) (y 1) ∧ y 4 = m.cQ (y 0) (y 1)}) := by
  have hψ := Dynamics.LaSalle.isIntegralCurveOn_comp_of_fderiv (cyl_contDiff.differentiable (by norm_num))
    (fderiv_cyl_field m) hφ
  have hκ : m.κ ≠ 0 := by
    rw [← eta_mul_k]
    exact mul_ne_zero hη (k_ne_zero m hL hR hs)
  have h2 : ContDiff ℝ 1 (fun y : State 5 => y 2 - m.ustar) :=
    (proj_contDiff 2).sub contDiff_const
  refine Dynamics.LaSalle.lasalle_levelSet (h := fun y : State 5 => y 0 ^ 2 + y 1 ^ 2) (c₀ := 1)
    (c := m.cylEnergy (cyl (φ 0))) (cylField_contDiff m)
    (circle_contDiff.differentiable (by norm_num)) (cylEnergy_contDiff m)
    (fderiv_circle_cylField m)
    (fun y hy => (cylLie_le m hR hL.ne' hC.ne' hy).trans
      (by nlinarith [sq_nonneg (y 2 - m.ustar)]))
    (isCompact_cylSublevel m hC hL hR _) ?_ hψ (by simp) le_rfl
  rcases hδ.lt_or_eq with hδ | hδ
  · refine Dynamics.LaSalle.lasalle_condition_of_lieDeriv_mem (cylField_contDiff m) h2 ?_ ?_
    · rintro y ⟨⟨hy, -⟩, h0⟩
      exact sub_eq_zero.mpr (cylLie_eq_zero m hR hL hC hδ hy h0).1
    · rintro y ⟨⟨hy, -⟩, h0⟩ hd
      obtain ⟨e2, e3, e4⟩ := cylLie_eq_zero m hR hL hC hδ hy h0
      have hf : HasFDerivAt (fun y : State 5 => y 2 - m.ustar)
          (PiLp.proj 2 (fun _ : Fin 5 => ℝ) 2 : State 5 →L[ℝ] ℝ) y :=
        (PiLp.proj 2 (fun _ : Fin 5 => ℝ) 2 : State 5 →L[ℝ] ℝ).hasFDerivAt.sub_const _
      rw [hf.fderiv] at hd
      have hd' : m.cylField y 2 = 0 := by simpa using hd
      rw [cylField_two_of_mem m e2 e3 e4, neg_div, neg_eq_zero,
        div_eq_zero_iff, or_iff_left hC.ne'] at hd'
      exact ⟨(mul_eq_zero.mp hd').resolve_left hκ, e2, e3, e4⟩
  · refine Dynamics.LaSalle.lasalle_condition_of_trajectories_mem (cylField_contDiff m) ?_
    intro T ψ hT hψ hstay
    exact margin_zero_segment m hC hL hR hη hs hδ.symm hT hψ fun t ht =>
      ⟨(hstay t ht).1.1, (hstay t ht).2⟩

/-- **Item: LaSalle convergence (the source's appendix argument, made precise).** Under the
source's strict condition `margin > 0`, with `C_dc, L_s, R_s > 0`, `η ≠ 0` and `μ u* v₀ ≠ 0`,
every forward solution of the stiff-grid closed loop converges to **one** equilibrium
`(j π, u*_dc, î_dq(j π))`, `j ∈ ℤ`. -/
private theorem tendsto_equilibrium (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls) (hR : 0 < m.Rs)
    (hη : m.η ≠ 0) (hs : m.μ * m.ustar * m.v0 ≠ 0) (hδ : 0 ≤ m.margin) {φ : ℝ → State 4}
    (hφ : IsIntegralCurveOn φ (fun _ x => m.field x) (Ici 0)) :
    ∃ j : ℤ, Tendsto φ atTop (𝓝 (WithLp.toLp 2 ![j * Real.pi, m.ustar,
      m.iHatD (j * Real.pi), m.iHatQ (j * Real.pi)])) := by
  have hT := tendsto_cyl m hC hL hR hη hs hδ hφ
  have c5 : ∀ j : Fin 5, Continuous (fun y : State 5 => y j) := fun j =>
    (proj_contDiff j).continuous
  have hsin : Tendsto (fun t => Real.sin (φ t 0)) atTop (𝓝 0) := by
    have := Dynamics.LaSalle.tendsto_zero_of_tendsto_nhdsSet hT (c5 1) (fun y hy => hy.1)
    simpa using this
  have hu : Tendsto (fun t => φ t 1 - m.ustar) atTop (𝓝 0) := by
    have := Dynamics.LaSalle.tendsto_zero_of_tendsto_nhdsSet hT ((c5 2).sub continuous_const)
      (fun y hy => sub_eq_zero.mpr hy.2.1)
    simpa using this
  have hcD : Continuous (fun y : State 5 => y 3 - m.cD (y 0) (y 1)) := by
    have h0 := c5 0
    have h1 := c5 1
    have h3 := c5 3
    unfold Model.cD
    fun_prop
  have hcQ : Continuous (fun y : State 5 => y 4 - m.cQ (y 0) (y 1)) := by
    have h0 := c5 0
    have h1 := c5 1
    have h4 := c5 4
    unfold Model.cQ
    fun_prop
  have hd : Tendsto (fun t => φ t 2 - m.iHatD (φ t 0)) atTop (𝓝 0) := by
    have := Dynamics.LaSalle.tendsto_zero_of_tendsto_nhdsSet hT hcD
      (fun y hy => sub_eq_zero.mpr hy.2.2.1)
    simpa [cD_cos_sin] using this
  have hq : Tendsto (fun t => φ t 3 - m.iHatQ (φ t 0)) atTop (𝓝 0) := by
    have := Dynamics.LaSalle.tendsto_zero_of_tendsto_nhdsSet hT hcQ
      (fun y hy => sub_eq_zero.mpr hy.2.2.2)
    simpa [cQ_cos_sin] using this
  have hθc : ContinuousOn (fun t => φ t 0) (Ici 0) :=
    ((proj_contDiff (n := 4) 0).continuous.comp_continuousOn hφ.continuousOn)
  obtain ⟨j, hj⟩ := Dynamics.LaSalle.exists_int_tendsto_of_tendsto_sin hθc hsin
  refine ⟨j, Dynamics.tendsto_euclidean_of_coord fun i => ?_⟩
  fin_cases i
  · simpa using hj
  · simpa using hu.add_const m.ustar
  · simpa using hd.add (((iHatD_continuous m).tendsto _).comp hj)
  · simpa using hq.add (((iHatQ_continuous m).tendsto _).comp hj)

/-- The source's statement: every forward solution converges to the set
`{ũ_dc = 0, ∇S(θ_dq) = 0, ĩ_dq = 0}` (with `∇S = deriv potential`). -/
private theorem tendsto_critical (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls) (hR : 0 < m.Rs)
    (hη : m.η ≠ 0) (hs : m.μ * m.ustar * m.v0 ≠ 0) (hδ : 0 ≤ m.margin) {φ : ℝ → State 4}
    (hφ : IsIntegralCurveOn φ (fun _ x => m.field x) (Ici 0)) :
    Tendsto φ atTop (𝓝ˢ {x : State 4 | x 1 = m.ustar ∧ deriv m.potential (x 0) = 0 ∧
      x 2 = m.iHatD (x 0) ∧ x 3 = m.iHatQ (x 0)}) := by
  obtain ⟨j, hj⟩ := tendsto_equilibrium m hC hL hR hη hs hδ hφ
  refine hj.mono_right (nhds_le_nhdsSet ?_)
  have hN := (N_pos m hR).ne'
  simp [(hasDerivAt_potential m hN _).deriv, Real.sin_int_mul_pi]

/-- A forward solution on `[0, ∞)` from every state (with `margin ≥ 0`): the cylinder solution
from `cyl x₀` stays in a compact energy sublevel set, and its angle is lifted back. -/
private theorem exists_solution (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls) (hR : 0 < m.Rs)
    (hδ : 0 ≤ m.margin) (x₀ : State 4) :
    ∃ φ : ℝ → State 4, φ 0 = x₀ ∧ IsIntegralCurveOn φ (fun _ x => m.field x) (Ici 0) := by
  set c := m.cylEnergy (cyl x₀)
  have hinv : IsPositivelyInvariant {y : State 5 | y 0 ^ 2 + y 1 ^ 2 = 1 ∧ m.cylEnergy y ≤ c}
      m.cylField :=
    Dynamics.LaSalle.isPositivelyInvariant_levelSet_sublevel (h := fun y : State 5 => y 0 ^ 2 + y 1 ^ 2)
      (circle_contDiff.differentiable (by norm_num))
      ((cylEnergy_contDiff m).differentiable (by norm_num)) (fderiv_circle_cylField m)
      (fun y hy => (cylLie_le m hR hL.ne' hC.ne' hy).trans
        (by nlinarith [sq_nonneg (y 2 - m.ustar)]))
  obtain ⟨ψ, hψ0, hψ, -⟩ := Dynamics.LaSalle.exists_isIntegralCurveOn_of_isCompact (cylField_contDiff m)
    (isCompact_cylSublevel m hC hL hR c) hinv (y₀ := cyl x₀) ⟨by simp, le_rfl⟩
  have hco : ∀ t, 0 ≤ t → ∀ i,
      HasDerivWithinAt (fun τ => ψ τ i) (m.cylField (ψ t) i) (Ici 0) t :=
    fun t ht i => Dynamics.HasDerivWithinAt.euclidean_coord (hψ t ht) i
  have hw : ContinuousOn (fun t => m.η * ψ t 2 - m.ω0) (Ici 0) :=
    (continuousOn_const.mul ((proj_contDiff (n := 5) 2).continuous.comp_continuousOn
      hψ.continuousOn)).sub continuousOn_const
  obtain ⟨θ, hθ0, hθd, hθcs⟩ := Dynamics.LaSalle.exists_angle_lift (c := fun t => ψ t 0)
    (s := fun t => ψ t 1) (θ₀ := x₀ 0) hw
    (fun t ht => by simpa [Model.cylField] using hco t ht 0)
    (fun t ht => by simpa [Model.cylField] using hco t ht 1)
    (by simp [hψ0]) (by simp [hψ0])
  refine ⟨fun t => WithLp.toLp 2 ![θ t, ψ t 2, ψ t 3, ψ t 4], ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [hθ0, hψ0]
  · intro t ht
    have ht' : (0 : ℝ) ≤ t := ht
    have hψt : ψ t = cyl (WithLp.toLp 2 ![θ t, ψ t 2, ψ t 3, ψ t 4]) := by
      ext i
      fin_cases i <;> simp [cyl, (hθcs t ht').1, (hθcs t ht').2]
    have hF := cylField_cyl m (WithLp.toLp 2 ![θ t, ψ t 2, ψ t 3, ψ t 4])
    rw [← hψt] at hF
    apply Dynamics.hasDerivWithinAt_euclidean_of_coord
    intro i
    fin_cases i
    · simpa [Model.field] using hθd t ht'
    · have h := hco t ht' 2
      rw [hF] at h
      simpa using h
    · have h := hco t ht' 3
      rw [hF] at h
      simpa using h
    · have h := hco t ht' 4
      rw [hF] at h
      simpa using h

private theorem k_pos' (m : Model) (hL : 0 < m.Ls) (hR : 0 < m.Rs)
    (hs : 0 < m.μ * m.ustar * m.v0) : 0 < m.k := by
  unfold Model.k
  have : m.Ls * m.μ * m.ustar * m.v0 = m.Ls * (m.μ * m.ustar * m.v0) := by ring
  rw [this]
  exact div_pos (mul_pos hL hs) (N_pos m hR)

private theorem energy_ge (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls) (x : State 4) :
    m.k * (1 - Real.cos (x 0)) ≤ m.energy x := by
  unfold Model.energy
  have h1 : 0 ≤ m.Cdc / 2 * (x 1 - m.ustar) ^ 2 := by positivity
  have h2 : 0 ≤ m.Ls / 2 * ((x 2 - m.iHatD (x 0)) ^ 2 + (x 3 - m.iHatQ (x 0)) ^ 2) := by
    positivity
  linarith

/-- **Item: basin estimate.** Under `margin > 0`, `C_dc, L_s, R_s > 0`, `η ≠ 0` and
`μ u* v₀ > 0` (so that `θ_dq = 0` is the minimum of `S` and `θ_dq = ±π` the saddles, at energy
`H − S(0) = 2k`), the window `{|θ_dq| < π, H − S(0) < 2k}` — the part below the saddle level of
the energy well around the operating point — lies in its region of attraction: from every such
initial state a forward solution exists, and every forward solution converges to `x*`. -/
private theorem basin (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls) (hR : 0 < m.Rs)
    (hη : m.η ≠ 0) (hs : 0 < m.μ * m.ustar * m.v0) (hδ : 0 ≤ m.margin) :
    ∀ x₀ ∈ {x : State 4 | |x 0| < Real.pi ∧ m.energy x < 2 * m.k},
      (∃ φ : ℝ → State 4, φ 0 = x₀ ∧ IsIntegralCurveOn φ (fun _ x => m.field x) (Ici 0)) ∧
      ∀ φ : ℝ → State 4, φ 0 = x₀ → IsIntegralCurveOn φ (fun _ x => m.field x) (Ici 0) →
        Tendsto φ atTop (𝓝 m.point) := by
  rintro x₀ ⟨hθ0, hE0⟩
  refine ⟨exists_solution m hC hL hR hδ x₀, fun φ hφ0 hφ => ?_⟩
  have hπ := Real.pi_pos
  have hk := k_pos' m hL hR hs
  -- the energy is nonincreasing along the solution
  have hanti : AntitoneOn (m.energy ∘ φ) (Ici 0) :=
    antitoneOn_V_comp_traj (energy_differentiable m) (energy_differentiable m).continuous
      (convex_Ici 0) hφ (fun t _ => (energy_lie_le m hR hL.ne' hC.ne' _).trans
        (by nlinarith [sq_nonneg (φ t 1 - m.ustar)]))
  have hEt : ∀ t, 0 ≤ t → m.energy (φ t) ≤ m.energy x₀ := fun t ht => by
    have := hanti (show (0 : ℝ) ∈ Ici 0 from Set.mem_Ici.mpr le_rfl) (show t ∈ Ici 0 from ht) ht
    simpa [hφ0] using this
  have hθc : ContinuousOn (fun t => φ t 0) (Ici 0) :=
    ((proj_contDiff (n := 4) 0).continuous.comp_continuousOn hφ.continuousOn)
  -- the angle stays in `(−π, π)`: crossing `±π` would need energy `≥ 2k`
  have hwin : ∀ t, 0 ≤ t → |φ t 0| < Real.pi := by
    intro t ht
    by_contra hc
    rw [not_lt] at hc
    have hcont : ContinuousOn (fun t => φ t 0) (Icc 0 t) := hθc.mono Icc_subset_Ici_self
    have h00 : φ 0 0 = x₀ 0 := by rw [hφ0]
    rw [abs_lt] at hθ0
    have hsad : ∃ s ∈ Icc 0 t, Real.cos (φ s 0) = -1 := by
      rcases le_abs'.mp hc with hc | hc
      · obtain ⟨s, hs, hse⟩ := intermediate_value_Icc' ht hcont
          (show -Real.pi ∈ Icc (φ t 0) (φ 0 0) by constructor <;> linarith)
        exact ⟨s, hs, by simp only at hse; rw [hse, Real.cos_neg, Real.cos_pi]⟩
      · obtain ⟨s, hs, hse⟩ := intermediate_value_Icc ht hcont
          (show Real.pi ∈ Icc (φ 0 0) (φ t 0) by constructor <;> linarith)
        exact ⟨s, hs, by simp only at hse; rw [hse, Real.cos_pi]⟩
    obtain ⟨s, hs, hcs⟩ := hsad
    have h1 := energy_ge m hC hL (φ s)
    rw [hcs] at h1
    linarith [hEt s hs.1]
  obtain ⟨j, hj⟩ := tendsto_equilibrium m hC hL hR hη hs.ne' hδ hφ
  set p : State 4 := WithLp.toLp 2 ![j * Real.pi, m.ustar, m.iHatD (j * Real.pi),
    m.iHatQ (j * Real.pi)] with hp
  have hθj : Tendsto (fun t => φ t 0) atTop (𝓝 (j * Real.pi)) := by
    have := ((proj_contDiff (n := 4) 0).continuous.tendsto p).comp hj
    simpa [hp, Function.comp_def] using this
  have hjle : |(j : ℝ) * Real.pi| ≤ Real.pi :=
    le_of_tendsto hθj.abs (eventually_atTop.mpr ⟨0, fun t ht => (hwin t ht).le⟩)
  have hEj : m.energy p ≤ m.energy x₀ :=
    le_of_tendsto (((energy_differentiable m).continuous.tendsto p).comp hj)
      (eventually_atTop.mpr ⟨0, fun t ht => hEt t ht⟩)
  have hEp : m.energy p = m.k * (1 - Real.cos (j * Real.pi)) := by
    simp [Model.energy, hp]
  have hj1 : |(j : ℝ)| ≤ 1 := by
    rw [abs_mul, abs_of_pos hπ] at hjle
    nlinarith
  have hj0 : j = 0 := by
    have hj1' : |j| ≤ 1 := by exact_mod_cast hj1
    rw [abs_le] at hj1'
    have hcos : j ≠ 0 → Real.cos (j * Real.pi) = -1 := by
      intro hne
      have : j = -1 ∨ j = 1 := by omega
      rcases this with rfl | rfl <;> simp
    by_contra hne
    rw [hEp, hcos hne] at hEj
    linarith
  rw [hp, hj0] at hj
  convert hj using 2
  ext i
  fin_cases i <;> simp [Model.point]

/-- **Boundary: `η ≠ 0` is necessary.** Without matching gain (`η = 0`, so `ω₀ = 0` and no
synchronizing torque `κ = η k`), every `(θ, u*, î(θ))` is an equilibrium; for `μ u* v₀ ≠ 0` the one
at `θ = π/2` has `∇S ≠ 0`, so the constant solution there does not converge to the source's set. -/
private theorem not_tendsto_critical_of_eta_eq_zero (m : Model) (hL : 0 < m.Ls) (hR : 0 < m.Rs)
    (hη : m.η = 0) (hs : m.μ * m.ustar * m.v0 ≠ 0) :
    ∃ φ : ℝ → State 4, IsIntegralCurveOn φ (fun _ x => m.field x) (Ici 0) ∧
      ¬ Tendsto φ atTop (𝓝ˢ {x : State 4 | x 1 = m.ustar ∧ deriv m.potential (x 0) = 0 ∧
        x 2 = m.iHatD (x 0) ∧ x 3 = m.iHatQ (x 0)}) := by
  have hN := (N_pos m hR).ne'
  set p : State 4 := WithLp.toLp 2 ![Real.pi / 2, m.ustar, m.iHatD (Real.pi / 2),
    m.iHatQ (Real.pi / 2)] with hp
  have hω : m.ω0 = 0 := by simp [Model.ω0, hη]
  have hκ : m.κ = 0 := by simp [Model.κ, hω]
  have hfp : m.field p = 0 := by
    ext i
    fin_cases i
    · simp [hp, Model.field, hη, hω]
    · simp only [hp, Model.field, Model.idc, Model.ixHat, hκ, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons, PiLp.zero_apply, Fin.isValue, Fin.mk_one]
      ring
    · simp only [hp, Model.field, Model.iHatD, Model.iHatQ, hω, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons, PiLp.zero_apply, Fin.isValue, Fin.reduceFinMk]
      field_simp
      simp only [Model.N, hω]
      ring
    · simp only [hp, Model.field, Model.iHatD, Model.iHatQ, hω, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons, PiLp.zero_apply, Fin.isValue, Fin.reduceFinMk]
      field_simp
      simp only [Model.N, hω]
      ring
  refine ⟨fun _ => p, fun t _ => ?_, fun h => ?_⟩
  · show HasDerivWithinAt (fun _ => p) (m.field p) (Ici 0) t
    rw [hfp]
    exact hasDerivWithinAt_const t _ p
  · have hnot : p ∉ {x : State 4 | x 1 = m.ustar ∧ deriv m.potential (x 0) = 0 ∧
        x 2 = m.iHatD (x 0) ∧ x 3 = m.iHatQ (x 0)} := by
      rintro ⟨-, hd, -, -⟩
      rw [show p 0 = Real.pi / 2 by simp [hp], (hasDerivAt_potential m hN _).deriv,
        Real.sin_pi_div_two, mul_one] at hd
      exact k_ne_zero m hL hR hs hd
    have hU : ({p}ᶜ : Set (State 4)) ∈ 𝓝ˢ {x : State 4 | x 1 = m.ustar ∧
        deriv m.potential (x 0) = 0 ∧ x 2 = m.iHatD (x 0) ∧ x 3 = m.iHatQ (x 0)} :=
      isOpen_compl_singleton.mem_nhdsSet.mpr fun x hx hxp => hnot (by
        rw [Set.mem_singleton_iff] at hxp
        rwa [← hxp])
    obtain ⟨T, hT⟩ := eventually_atTop.mp (h hU)
    exact hT T le_rfl rfl

/-! ## Connection conclusions -/

private theorem mem_den_flow' {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.field m.point :=
  ((show family.IsAutonomous Model.translated from fun _ => rfl).mem_den_flow).trans
    (Flow.Property.holds_shift_iff P)

/-- **Local asymptotic stability under the non-strict condition** `margin ≥ 0` (the note's
condition with equality allowed), with `C_dc, L_s, R_s > 0`, `μ u* v₀ > 0` and `η ≠ 0`: the operating
point is Lyapunov stable (`mem_den_lyapunovStable`) and a ball around it lies in the LaSalle basin
window (`basin`). At `margin = 0` the linearization is not used (the dissipation is only
semidefinite); the LaSalle set argument on the cylinder covers it. -/
@[powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_of_dissipative (m : Model)
    (hC : 0 < m.Cdc) (hL : 0 < m.Ls) (hR : 0 < m.Rs) (hs : 0 < m.μ * m.ustar * m.v0)
    (hη : m.η ≠ 0) (hδ : 0 ≤ m.margin) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow']
  have hLS : LyapunovStable m.field m.point := by
    have h := mem_den_lyapunovStable m hC hL hR hs hδ
    unfold powerlib.TMIO.Statement at h
    exact mem_den_flow'.mp h
  refine ⟨hLS, ?_⟩
  have hk := k_pos' m hL hR hs
  have hW : IsOpen {x : State 4 | |x 0| < Real.pi ∧ m.energy x < 2 * m.k} :=
    (isOpen_lt (continuous_abs.comp (proj_contDiff (n := 4) 0).continuous) continuous_const).inter
      (isOpen_lt (energy_differentiable m).continuous continuous_const)
  have hp : m.point ∈ {x : State 4 | |x 0| < Real.pi ∧ m.energy x < 2 * m.k} := by
    refine ⟨by simp [Model.point, Real.pi_pos], ?_⟩
    rw [energy_point]
    linarith
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW m.point hp
  refine ⟨r, hr, fun t₀ φ hφ hφ0 => ?_⟩
  have hmem : φ t₀ ∈ {x : State 4 | |x 0| < Real.pi ∧ m.energy x < 2 * m.k} :=
    hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hφ0)
  exact Dynamics.LaSalle.RegionOfAttraction.tendsto (basin m hC hL hR hη hs hδ) hφ hmem

/-- A stiff-grid model at the boundary `margin = 0`: `C_dc = L_s = R_s = η = μ = u*_dc = v₀ = 1`,
`G_dc = 1/8`, `K_p = 0` (`ω₀ = 1`, `N = 2`, `μ²ω₀²L_s²/(4R_sN) = 1/8`). -/
def boundaryModel : Model :=
  { Cdc := 1, Gdc := 1 / 8, Kp := 0, η := 1, μ := 1, ustar := 1, v0 := 1, Rs := 1, Ls := 1 }

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem boundaryModel_margin : boundaryModel.margin = 0 := by
  simp [Model.margin, Model.N, Model.ω0, boundaryModel]
  norm_num

/-- The boundary model is locally asymptotically stable. -/
@[powerlib_domain] theorem boundaryModel_mem_den_locallyAsymptoticallyStable :
    connection% (boundaryModel ∈ family.den (.flow .locallyAsymptoticallyStable)) :=
  mem_den_locallyAsymptoticallyStable_of_dissipative boundaryModel (by norm_num [boundaryModel])
    (by norm_num [boundaryModel]) (by norm_num [boundaryModel]) (by norm_num [boundaryModel])
    (by norm_num [boundaryModel]) boundaryModel_margin.ge

/-- **Boundary**: the local asymptotic translation `{physical, synchronizing, damped, matching}` of
`MatchingStiffGrid.family` is sound but **not exact** — the boundary model with `margin = 0`
violates `damped` and is locally asymptotically stable. -/
@[powerlib_domain] theorem not_exact_locallyAsymptoticallyStable :
    connection% (¬ family.Exact (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := boundaryModel_mem_den_locallyAsymptoticallyStable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hd : Meets boundaryModel .damped := hmem .damped (by
    show Requirement.damped ∈ translate (.flow .locallyAsymptoticallyStable)
    simp [translate])
  have : (0 : ℝ) < 0 := by
    have hd' : 0 < boundaryModel.margin := hd
    rwa [boundaryModel_margin] at hd'
  exact lt_irrefl _ this


/-! ## No synchronizing torque: `μ u* v₀ = 0`

Then `k = κ = 0`: the potential `S` is constant, every `(θ, u*, î(θ))` is an equilibrium
(`field_eq_zero_of_kappa_eq_zero`), and `H − S(0) = C_dc ũ²/2 + L_s ‖ĩ‖²/2`. -/

/-- Without synchronizing torque (`μ u* v₀ = 0`) the potential stiffness vanishes. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem k_eq_zero_of_no_sync (m : Model) (hs : m.μ * m.ustar * m.v0 = 0) : m.k = 0 := by
  unfold Model.k
  rw [show m.Ls * m.μ * m.ustar * m.v0 = m.Ls * (m.μ * m.ustar * m.v0) by ring, hs, mul_zero,
    zero_div]

/-- Without synchronizing torque the synchronizing-torque gain vanishes. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem kappa_eq_zero_of_no_sync (m : Model) (hs : m.μ * m.ustar * m.v0 = 0) : m.κ = 0 := by
  rw [← eta_mul_k, k_eq_zero_of_no_sync m hs, mul_zero]

/-- With `κ = 0` every `(θ, u*, î(θ))` is an equilibrium (a circle of equilibria). Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field_eq_zero_of_kappa_eq_zero (m : Model) (hN : m.N ≠ 0) (hκ : m.κ = 0) (θ : ℝ) :
    m.field (WithLp.toLp 2 ![θ, m.ustar, m.iHatD θ, m.iHatQ θ]) = 0 := by
  ext i
  fin_cases i
  · simp [Model.field, Model.ω0]
  · simp only [Model.field, Model.idc, Model.ixHat, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, PiLp.zero_apply, Fin.isValue, Fin.mk_one, hκ]
    ring
  · simp only [Model.field, Model.iHatD, Model.iHatQ, PiLp.toLp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, PiLp.zero_apply, Fin.isValue, Fin.reduceFinMk]
    field_simp
    simp only [Model.N]
    ring
  · simp only [Model.field, Model.iHatD, Model.iHatQ, PiLp.toLp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, PiLp.zero_apply, Fin.isValue, Fin.reduceFinMk]
    field_simp
    simp only [Model.N]
    ring

/-- The internal model is Lipschitz in the angle. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem abs_iHatD_sub_le (m : Model) (hN : 0 < m.N) (θ : ℝ) :
    |m.iHatD θ - m.iHatD 0| ≤
      (|m.Rs * (m.μ * m.ustar)| + |m.ω0 * m.Ls * (m.μ * m.ustar)|) / m.N * |θ| := by
  have e : m.iHatD θ - m.iHatD 0 = (m.Rs * (m.μ * m.ustar) * Real.sin θ +
      m.ω0 * m.Ls * (m.μ * m.ustar) * (1 - Real.cos θ)) / m.N := by
    simp only [Model.iHatD, Real.sin_zero, Real.cos_zero]
    field_simp
    ring
  have hs : |Real.sin θ| ≤ |θ| := by simpa using Real.abs_sin_sub_sin_le θ 0
  have hc : |1 - Real.cos θ| ≤ |θ| := by simpa using Real.abs_cos_sub_cos_le 0 θ
  rw [e, abs_div, abs_of_pos hN, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hN]
  calc |m.Rs * (m.μ * m.ustar) * Real.sin θ + m.ω0 * m.Ls * (m.μ * m.ustar) * (1 - Real.cos θ)|
      ≤ |m.Rs * (m.μ * m.ustar)| * |Real.sin θ| +
        |m.ω0 * m.Ls * (m.μ * m.ustar)| * |1 - Real.cos θ| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |m.Rs * (m.μ * m.ustar)| * |θ| + |m.ω0 * m.Ls * (m.μ * m.ustar)| * |θ| := by
        gcongr
    _ = _ := by ring

/-- The internal model is Lipschitz in the angle. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem abs_iHatQ_sub_le (m : Model) (hN : 0 < m.N) (θ : ℝ) :
    |m.iHatQ θ - m.iHatQ 0| ≤
      (|m.Rs * (m.μ * m.ustar)| + |m.ω0 * m.Ls * (m.μ * m.ustar)|) / m.N * |θ| := by
  have e : m.iHatQ θ - m.iHatQ 0 = (-(m.ω0 * m.Ls * (m.μ * m.ustar)) * Real.sin θ +
      m.Rs * (m.μ * m.ustar) * (1 - Real.cos θ)) / m.N := by
    simp only [Model.iHatQ, Real.sin_zero, Real.cos_zero]
    field_simp
    ring
  have hs : |Real.sin θ| ≤ |θ| := by simpa using Real.abs_sin_sub_sin_le θ 0
  have hc : |1 - Real.cos θ| ≤ |θ| := by simpa using Real.abs_cos_sub_cos_le 0 θ
  rw [e, abs_div, abs_of_pos hN, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hN]
  calc |-(m.ω0 * m.Ls * (m.μ * m.ustar)) * Real.sin θ + m.Rs * (m.μ * m.ustar) * (1 - Real.cos θ)|
      ≤ |m.ω0 * m.Ls * (m.μ * m.ustar)| * |Real.sin θ| +
        |m.Rs * (m.μ * m.ustar)| * |1 - Real.cos θ| := by
        rw [← abs_neg (m.ω0 * m.Ls * (m.μ * m.ustar)), ← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |m.ω0 * m.Ls * (m.μ * m.ustar)| * |θ| + |m.Rs * (m.μ * m.ustar)| * |θ| := by
        gcongr
    _ = _ := by ring

private theorem quad_nonneg {a b u e1 e2 w1 w2 : ℝ} (ha : 0 < a) (hab : w1 ^ 2 + w2 ^ 2 ≤ a * b) :
    0 ≤ a * u ^ 2 + b * (e1 ^ 2 + e2 ^ 2) + 2 * u * (e1 * w1 + e2 * w2) := by
  have h : a * (a * u ^ 2 + b * (e1 ^ 2 + e2 ^ 2) + 2 * u * (e1 * w1 + e2 * w2)) =
      (a * u + (e1 * w1 + e2 * w2)) ^ 2 + (a * b - (w1 ^ 2 + w2 ^ 2)) * (e1 ^ 2 + e2 ^ 2) +
        (e1 * w2 - e2 * w1) ^ 2 := by ring
  have h2 : 0 ≤ a * (a * u ^ 2 + b * (e1 ^ 2 + e2 ^ 2) + 2 * u * (e1 * w1 + e2 * w2)) := by
    rw [h]
    have := sub_nonneg.mpr hab
    positivity
  exact (mul_nonneg_iff_of_pos_left ha).mp h2

/-- With `margin > 0` the dissipation is uniformly positive definite in `(ũ_dc, ĩ_dq)`:
`dH/dt ≤ −ε (ũ² + ‖ĩ‖²)`, `ε = R_s margin/(G_dc + K_p + R_s)` (for every `μ u* v₀`). Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem energy_lie_le_sq (m : Model) (hR : 0 < m.Rs) (hL : m.Ls ≠ 0) (hC : m.Cdc ≠ 0)
    (hδ : 0 < m.margin) (x : State 4) :
    fderiv ℝ m.energy x (m.field x) ≤ -(m.Rs * m.margin / (m.Gdc + m.Kp + m.Rs)) *
      ((x 1 - m.ustar) ^ 2 + ((x 2 - m.iHatD (x 0)) ^ 2 + (x 3 - m.iHatQ (x 0)) ^ 2)) := by
  have hN := N_pos m hR
  rw [energy_lie m hN.ne' hL hC]
  have hz : (m.Rs * Real.cos (x 0) + m.ω0 * m.Ls * Real.sin (x 0)) ^ 2 +
      (m.Rs * Real.sin (x 0) - m.ω0 * m.Ls * Real.cos (x 0)) ^ 2 = m.N := by
    simp only [Model.N]
    linear_combination (m.Rs ^ 2 + m.ω0 ^ 2 * m.Ls ^ 2) * Real.sin_sq_add_cos_sq (x 0)
  have hBm : (m.μ * m.ω0 * m.Ls) ^ 2 / (4 * m.N) = m.Rs * (m.Gdc + m.Kp - m.margin) := by
    simp only [Model.margin]
    field_simp
    ring
  have hP : m.margin ≤ m.Gdc + m.Kp := by
    have : 0 ≤ m.μ ^ 2 * m.ω0 ^ 2 * m.Ls ^ 2 / (4 * m.Rs * m.N) := by positivity
    simp only [Model.margin]
    linarith
  set u := x 1 - m.ustar
  set e1 := x 2 - m.iHatD (x 0)
  set e2 := x 3 - m.iHatQ (x 0)
  set z1 := m.Rs * Real.cos (x 0) + m.ω0 * m.Ls * Real.sin (x 0)
  set z2 := m.Rs * Real.sin (x 0) - m.ω0 * m.Ls * Real.cos (x 0)
  set B := m.μ * m.ω0 * m.Ls
  set P := m.Gdc + m.Kp
  have hPR : 0 < P + m.Rs := by linarith
  set ε := m.Rs * m.margin / (P + m.Rs) with hεdef
  have hε : ε * (P + m.Rs) = m.Rs * m.margin := div_mul_cancel₀ _ hPR.ne'
  have hε0 : 0 < ε := div_pos (mul_pos hR hδ) hPR
  have hεP : ε < P := by nlinarith
  have hεR : ε < m.Rs := by nlinarith
  have hw : (B / (2 * m.N) * z1) ^ 2 + (B / (2 * m.N) * z2) ^ 2 ≤ (P - ε) * (m.Rs - ε) := by
    have e : (B / (2 * m.N) * z1) ^ 2 + (B / (2 * m.N) * z2) ^ 2 = B ^ 2 / (4 * m.N) := by
      rw [mul_pow, mul_pow, ← mul_add, hz]
      field_simp
      ring
    rw [e, hBm]
    nlinarith [sq_nonneg ε]
  have q := quad_nonneg (u := u) (e1 := e1) (e2 := e2) (by linarith : 0 < P - ε) hw
  have e2' : 2 * u * (e1 * (B / (2 * m.N) * z1) + e2 * (B / (2 * m.N) * z2)) =
      B / m.N * u * (e1 * z1 + e2 * z2) := by
    field_simp
  nlinarith [q, e2']

/-- The exponential decay rate `2 ε/(C_dc + L_s)` of the energy without synchronizing torque,
`ε = R_s margin/(G_dc + K_p + R_s)`. -/
def Model.noSyncRate (m : Model) : ℝ :=
  2 * (m.Rs * m.margin / (m.Gdc + m.Kp + m.Rs)) / (m.Cdc + m.Ls)

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem noSyncRate_pos (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls) (hR : 0 < m.Rs)
    (hδ : 0 < m.margin) : 0 < m.noSyncRate := by
  have hP : m.margin ≤ m.Gdc + m.Kp := by
    have : 0 ≤ m.μ ^ 2 * m.ω0 ^ 2 * m.Ls ^ 2 / (4 * m.Rs * m.N) := by
      have := N_pos m hR
      positivity
    simp only [Model.margin]
    linarith
  have hPR : 0 < m.Gdc + m.Kp + m.Rs := by linarith
  unfold Model.noSyncRate
  positivity

/-- Without synchronizing torque the energy is the quadratic `C_dc ũ²/2 + L_s ‖ĩ‖²/2`. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem energy_eq_of_no_sync (m : Model) (hs : m.μ * m.ustar * m.v0 = 0) (x : State 4) :
    m.energy x = m.Cdc / 2 * (x 1 - m.ustar) ^ 2 +
      m.Ls / 2 * ((x 2 - m.iHatD (x 0)) ^ 2 + (x 3 - m.iHatQ (x 0)) ^ 2) := by
  simp [Model.energy, k_eq_zero_of_no_sync m hs]

/-- Without synchronizing torque and with `margin > 0`, `dH/dt ≤ −noSyncRate · H`. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem energy_lie_le_noSyncRate (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls) (hR : 0 < m.Rs)
    (hs : m.μ * m.ustar * m.v0 = 0) (hδ : 0 < m.margin) (x : State 4) :
    fderiv ℝ m.energy x (m.field x) ≤ -m.noSyncRate * m.energy x := by
  have h := energy_lie_le_sq m hR hL.ne' hC.ne' hδ x
  rw [energy_eq_of_no_sync m hs]
  have hε : 0 ≤ m.Rs * m.margin / (m.Gdc + m.Kp + m.Rs) := by
    have := (noSyncRate_pos m hC hL hR hδ).le
    unfold Model.noSyncRate at this
    have hCL : 0 < m.Cdc + m.Ls := by linarith
    have h2 := mul_nonneg this hCL.le
    rw [div_mul_cancel₀ _ hCL.ne'] at h2
    linarith
  set ε := m.Rs * m.margin / (m.Gdc + m.Kp + m.Rs)
  have hCL : 0 < m.Cdc + m.Ls := by linarith
  have e : -m.noSyncRate * (m.Cdc / 2 * (x 1 - m.ustar) ^ 2 +
      m.Ls / 2 * ((x 2 - m.iHatD (x 0)) ^ 2 + (x 3 - m.iHatQ (x 0)) ^ 2)) =
      -ε * (m.Cdc / (m.Cdc + m.Ls) * (x 1 - m.ustar) ^ 2 +
        m.Ls / (m.Cdc + m.Ls) * ((x 2 - m.iHatD (x 0)) ^ 2 + (x 3 - m.iHatQ (x 0)) ^ 2)) := by
    simp only [Model.noSyncRate, ε]
    field_simp
  rw [e]
  have h1 : m.Cdc / (m.Cdc + m.Ls) ≤ 1 := by rw [div_le_one hCL]; linarith
  have h2 : m.Ls / (m.Cdc + m.Ls) ≤ 1 := by rw [div_le_one hCL]; linarith
  have a1 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (x 1 - m.ustar))
  have a2 := mul_le_mul_of_nonneg_right h2
    (add_nonneg (sq_nonneg (x 2 - m.iHatD (x 0))) (sq_nonneg (x 3 - m.iHatQ (x 0))))
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add a1 a2) hε]

/-- Without synchronizing torque each error coordinate is bounded by the energy. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem sq_le_energy_of_no_sync (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls)
    (hs : m.μ * m.ustar * m.v0 = 0) (x : State 4) :
    (x 1 - m.ustar) ^ 2 ≤ 2 / m.Cdc * m.energy x ∧
      (x 2 - m.iHatD (x 0)) ^ 2 ≤ 2 / m.Ls * m.energy x ∧
      (x 3 - m.iHatQ (x 0)) ^ 2 ≤ 2 / m.Ls * m.energy x := by
  rw [energy_eq_of_no_sync m hs]
  have a := sq_nonneg (x 1 - m.ustar)
  have b := sq_nonneg (x 2 - m.iHatD (x 0))
  have c := sq_nonneg (x 3 - m.iHatQ (x 0))
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_add, ← mul_assoc, show 2 / m.Cdc * (m.Cdc / 2) = 1 by field_simp, one_mul]
    nlinarith [mul_nonneg (div_pos two_pos hC).le (mul_nonneg (div_pos hL two_pos).le (add_nonneg b c))]
  · rw [mul_add, show 2 / m.Ls * (m.Ls / 2 * ((x 2 - m.iHatD (x 0)) ^ 2 + (x 3 - m.iHatQ (x 0)) ^ 2)) =
      (x 2 - m.iHatD (x 0)) ^ 2 + (x 3 - m.iHatQ (x 0)) ^ 2 by field_simp]
    nlinarith [mul_nonneg (div_pos two_pos hL).le (mul_nonneg (div_pos hC two_pos).le a)]
  · rw [mul_add, show 2 / m.Ls * (m.Ls / 2 * ((x 2 - m.iHatD (x 0)) ^ 2 + (x 3 - m.iHatQ (x 0)) ^ 2)) =
      (x 2 - m.iHatD (x 0)) ^ 2 + (x 3 - m.iHatQ (x 0)) ^ 2 by field_simp]
    nlinarith [mul_nonneg (div_pos two_pos hL).le (mul_nonneg (div_pos hC two_pos).le a)]

/-- Exponential decay of the energy along every solution segment (no synchronizing torque,
`margin > 0`). Implementation evidence. -/
private theorem energy_decay (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls) (hR : 0 < m.Rs)
    (hs : m.μ * m.ustar * m.v0 = 0) (hδ : 0 < m.margin) {t₀ t₁ : ℝ} {φ : ℝ → State 4}
    (hφ : IsTrajectoryOn φ m.field t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, m.energy (φ t) ≤ Real.exp (-m.noSyncRate * (t - t₀)) * m.energy (φ t₀) :=
  Dynamics.le_exp_mul_of_hasDerivWithinAt (g := fun t => m.energy (φ t))
    (fun t ht => ((energy_differentiable m) (φ t)).hasFDerivAt.comp_hasDerivWithinAt t (hφ t ht))
    (fun t _ => energy_lie_le_noSyncRate m hC hL hR hs hδ (φ t))

/-- The coordinates `ũ, ĩ_d, ĩ_q` decay like `e^{−(rate/2)(t − t₀)}` along every segment. -/
private theorem coord_decay (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls) (hR : 0 < m.Rs)
    (hs : m.μ * m.ustar * m.v0 = 0) (hδ : 0 < m.margin) {t₀ t₁ : ℝ} {φ : ℝ → State 4}
    (hφ : IsTrajectoryOn φ m.field t₀ t₁) {l E : ℝ} (hl : 0 < l) (hE : m.energy (φ t₀) ≤ E) :
    ∀ t ∈ Icc t₀ t₁,
      |φ t 1 - m.ustar| ≤ (2 / m.Cdc * E / l + l) / 2 * Real.exp (-(m.noSyncRate / 2) * (t - t₀)) ∧
      |φ t 2 - m.iHatD (φ t 0)| ≤ (2 / m.Ls * E / l + l) / 2 *
        Real.exp (-(m.noSyncRate / 2) * (t - t₀)) ∧
      |φ t 3 - m.iHatQ (φ t 0)| ≤ (2 / m.Ls * E / l + l) / 2 *
        Real.exp (-(m.noSyncRate / 2) * (t - t₀)) := by
  intro t ht
  have hd := energy_decay m hC hL hR hs hδ hφ t ht
  have hd' : m.energy (φ t) ≤ E * Real.exp (-(2 * (m.noSyncRate / 2)) * (t - t₀)) := by
    rw [show 2 * (m.noSyncRate / 2) = m.noSyncRate by ring]
    nlinarith [Real.exp_pos (-m.noSyncRate * (t - t₀))]
  obtain ⟨a, b, c⟩ := sq_le_energy_of_no_sync m hC hL hs (φ t)
  have hCp : 0 ≤ 2 / m.Cdc := by positivity
  have hLp : 0 ≤ 2 / m.Ls := by positivity
  refine ⟨Dynamics.abs_le_of_sq_le_exp hl ?_, Dynamics.abs_le_of_sq_le_exp hl ?_,
    Dynamics.abs_le_of_sq_le_exp hl ?_⟩
  · calc (φ t 1 - m.ustar) ^ 2 ≤ 2 / m.Cdc * m.energy (φ t) := a
      _ ≤ 2 / m.Cdc * (E * Real.exp (-(2 * (m.noSyncRate / 2)) * (t - t₀))) :=
          mul_le_mul_of_nonneg_left hd' hCp
      _ = _ := by ring
  · calc (φ t 2 - m.iHatD (φ t 0)) ^ 2 ≤ 2 / m.Ls * m.energy (φ t) := b
      _ ≤ 2 / m.Ls * (E * Real.exp (-(2 * (m.noSyncRate / 2)) * (t - t₀))) :=
          mul_le_mul_of_nonneg_left hd' hLp
      _ = _ := by ring
  · calc (φ t 3 - m.iHatQ (φ t 0)) ^ 2 ≤ 2 / m.Ls * m.energy (φ t) := c
      _ ≤ 2 / m.Ls * (E * Real.exp (-(2 * (m.noSyncRate / 2)) * (t - t₀))) :=
          mul_le_mul_of_nonneg_left hd' hLp
      _ = _ := by ring

private theorem hasDerivWithinAt_angle (m : Model) {φ : ℝ → State 4} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt φ (m.field (φ t)) s t) :
    HasDerivWithinAt (fun τ => φ τ 0) (m.η * (φ t 1 - m.ustar)) s t := by
  have h0 := Dynamics.HasDerivWithinAt.euclidean_coord h 0
  convert h0 using 1
  simp only [Model.field, Model.ω0, PiLp.toLp_apply, Matrix.cons_val_zero]
  ring

/-- **No synchronizing torque, `margin > 0`: every forward solution converges to an equilibrium**
`(θ∞, u*, î(θ∞))` of the continuum `{(θ, u*, î(θ))}`: `ũ_dc, ĩ_dq → 0` exponentially and the angle
settles (`θ' = η ũ` is integrable), it does not drift. -/
private theorem tendsto_equilibrium_of_no_sync (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls)
    (hR : 0 < m.Rs) (hs : m.μ * m.ustar * m.v0 = 0) (hδ : 0 < m.margin) {φ : ℝ → State 4}
    (hφ : IsIntegralCurveOn φ (fun _ x => m.field x) (Ici 0)) :
    ∃ θ : ℝ, Tendsto φ atTop (𝓝 (WithLp.toLp 2 ![θ, m.ustar, m.iHatD θ, m.iHatQ θ])) := by
  have hρ := noSyncRate_pos m hC hL hR hδ
  set E₀ := m.energy (φ 0)
  have hb : ∀ t, 0 ≤ t →
      |φ t 1 - m.ustar| ≤ (2 / m.Cdc * E₀ / 1 + 1) / 2 * Real.exp (-(m.noSyncRate / 2) * t) ∧
      |φ t 2 - m.iHatD (φ t 0)| ≤ (2 / m.Ls * E₀ / 1 + 1) / 2 * Real.exp (-(m.noSyncRate / 2) * t) ∧
      |φ t 3 - m.iHatQ (φ t 0)| ≤ (2 / m.Ls * E₀ / 1 + 1) / 2 * Real.exp (-(m.noSyncRate / 2) * t) :=
    fun t ht => by
      have := coord_decay m hC hL hR hs hδ (hφ.mono Icc_subset_Ici_self : IsTrajectoryOn φ m.field 0 t)
        one_pos le_rfl t ⟨ht, le_rfl⟩
      simpa using this
  have hexp : Tendsto (fun t => Real.exp (-(m.noSyncRate / 2) * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  have sq0 : ∀ (g : ℝ → ℝ) (A : ℝ), (∀ t, 0 ≤ t → |g t| ≤ A * Real.exp (-(m.noSyncRate / 2) * t)) →
      Tendsto g atTop (𝓝 0) := fun g A h => by
    have hA : Tendsto (fun t => A * Real.exp (-(m.noSyncRate / 2) * t)) atTop (𝓝 0) := by
      have := hexp.const_mul A
      rwa [mul_zero] at this
    refine squeeze_zero_norm' ?_ hA
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [Real.norm_eq_abs]
    exact h t ht
  obtain ⟨θ, hθ⟩ := Dynamics.exists_tendsto_of_abs_deriv_le_exp (θ := fun t => φ t 0)
    (θ' := fun t => m.η * (φ t 1 - m.ustar)) (A := |m.η| * ((2 / m.Cdc * E₀ / 1 + 1) / 2))
    (t₀ := 0) (half_pos hρ) (fun t ht => hasDerivWithinAt_angle m (hφ t ht))
    (fun t ht => by
      rw [abs_mul, sub_zero, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hb t ht).1 (abs_nonneg _))
  refine ⟨θ, Dynamics.tendsto_euclidean_of_coord fun i => ?_⟩
  have hu := sq0 _ _ fun t ht => (hb t ht).1
  have hd := sq0 _ _ fun t ht => (hb t ht).2.1
  have hq := sq0 _ _ fun t ht => (hb t ht).2.2
  fin_cases i
  · simpa using hθ
  · simpa using hu.add_const m.ustar
  · simpa using hd.add (((iHatD_continuous m).tendsto _).comp hθ)
  · simpa using hq.add (((iHatQ_continuous m).tendsto _).comp hθ)

/-- Lyapunov stability without synchronizing torque (`margin > 0`): the angle moves by at most a
multiple of the initial deviation. -/
private theorem lyapunovStable_of_no_sync (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls)
    (hR : 0 < m.Rs) (hs : m.μ * m.ustar * m.v0 = 0) (hδ : 0 < m.margin) :
    LyapunovStable m.field m.point := by
  have hN := N_pos m hR
  have hρ := noSyncRate_pos m hC hL hR hδ
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ, Λ = (|m.Rs * (m.μ * m.ustar)| + |m.ω0 * m.Ls * (m.μ * m.ustar)|) /
      m.N := ⟨_, rfl⟩
  have hΛ : 0 ≤ Λ := by rw [hΛdef]; positivity
  obtain ⟨κ₀, hκ₀⟩ : ∃ κ₀, κ₀ = m.Cdc / 2 + m.Ls * (1 + Λ) ^ 2 := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ₀ := by rw [hκ₀]; positivity
  obtain ⟨cu, hcu⟩ : ∃ cu, cu = 2 / m.Cdc * κ₀ := ⟨_, rfl⟩
  obtain ⟨ce, hce⟩ : ∃ ce, ce = 2 / m.Ls * κ₀ := ⟨_, rfl⟩
  have hcu0 : 0 ≤ cu := by rw [hcu]; positivity
  have hce0 : 0 ≤ ce := by rw [hce]; positivity
  obtain ⟨Kθ, hKθ⟩ : ∃ Kθ, Kθ = 1 + |m.η| * (cu + 1) / m.noSyncRate := ⟨_, rfl⟩
  have hKθ0 : 0 ≤ Kθ := by rw [hKθ]; positivity
  obtain ⟨K, hK⟩ : ∃ K, K = (1 + 2 * Λ) * Kθ + (cu + 1) / 2 + (ce + 1) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  intro ε hε
  refine ⟨ε / (K + 1), by positivity, fun t₀ t₁ φ hφ h0 t ht => ?_⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = ε / (K + 1) := ⟨_, rfl⟩
  rw [← hδdef] at h0
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hKδ : K * δ < ε := by
    rw [hδdef, mul_div_assoc', div_lt_iff₀ (by linarith)]
    linarith
  have hr : ‖φ t₀ - m.point‖ < δ := h0
  have hc : ∀ i, |(φ t₀ - m.point) i| ≤ ‖φ t₀ - m.point‖ := fun i => by
    simpa using PiLp.norm_apply_le (φ t₀ - m.point) i
  have p0 : m.point 0 = 0 := by simp [Model.point]
  have p1 : m.point 1 = m.ustar := by simp [Model.point]
  have p2 : m.point 2 = m.iHatD 0 := by simp [Model.point]
  have p3 : m.point 3 = m.iHatQ 0 := by simp [Model.point]
  have hθ0 : |φ t₀ 0| ≤ δ := by
    have := hc 0
    rw [PiLp.sub_apply, p0, sub_zero] at this
    linarith
  have hu0 : |φ t₀ 1 - m.ustar| ≤ δ := by
    have := hc 1
    rw [PiLp.sub_apply, p1] at this
    linarith
  have hd0 : |φ t₀ 2 - m.iHatD 0| ≤ δ := by
    have := hc 2
    rw [PiLp.sub_apply, p2] at this
    linarith
  have hq0 : |φ t₀ 3 - m.iHatQ 0| ≤ δ := by
    have := hc 3
    rw [PiLp.sub_apply, p3] at this
    linarith
  have hD := abs_iHatD_sub_le m hN (φ t₀ 0)
  have hQ := abs_iHatQ_sub_le m hN (φ t₀ 0)
  rw [← hΛdef] at hD hQ
  have hΛθ0 := mul_le_mul_of_nonneg_left hθ0 hΛ
  have he1 : |φ t₀ 2 - m.iHatD (φ t₀ 0)| ≤ (1 + Λ) * δ := by
    have := abs_sub_le (φ t₀ 2) (m.iHatD 0) (m.iHatD (φ t₀ 0))
    rw [abs_sub_comm (m.iHatD 0)] at this
    linarith
  have he2 : |φ t₀ 3 - m.iHatQ (φ t₀ 0)| ≤ (1 + Λ) * δ := by
    have := abs_sub_le (φ t₀ 3) (m.iHatQ 0) (m.iHatQ (φ t₀ 0))
    rw [abs_sub_comm (m.iHatQ 0)] at this
    linarith
  have hE0 : m.energy (φ t₀) ≤ κ₀ * δ ^ 2 := by
    rw [energy_eq_of_no_sync m hs, hκ₀]
    have a : (φ t₀ 1 - m.ustar) ^ 2 ≤ δ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hu0 2
    have b : (φ t₀ 2 - m.iHatD (φ t₀ 0)) ^ 2 ≤ ((1 + Λ) * δ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) he1 2
    have c : (φ t₀ 3 - m.iHatQ (φ t₀ 0)) ^ 2 ≤ ((1 + Λ) * δ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) he2 2
    have hC2 : 0 ≤ m.Cdc / 2 := by positivity
    have hL2 : 0 ≤ m.Ls / 2 := by positivity
    have i1 := mul_le_mul_of_nonneg_left a hC2
    have i2 := mul_le_mul_of_nonneg_left (add_le_add b c) hL2
    have e : m.Ls / 2 * (((1 + Λ) * δ) ^ 2 + ((1 + Λ) * δ) ^ 2) = m.Ls * (1 + Λ) ^ 2 * δ ^ 2 := by
      ring
    linarith
  have hcd := coord_decay m hC hL hR hs hδ hφ hδ0 hE0
  have hsimp_u : (2 / m.Cdc * (κ₀ * δ ^ 2) / δ + δ) / 2 = (cu + 1) * δ / 2 := by
    rw [hcu]; field_simp
  have hsimp_e : (2 / m.Ls * (κ₀ * δ ^ 2) / δ + δ) / 2 = (ce + 1) * δ / 2 := by
    rw [hce]; field_simp
  -- the angle moves little
  have hθ : |φ t 0 - φ t₀ 0| ≤ |m.η| * ((cu + 1) * δ / 2) / (m.noSyncRate / 2) :=
    Dynamics.abs_sub_le_of_abs_deriv_le_exp (θ := fun τ => φ τ 0)
      (θ' := fun τ => m.η * (φ τ 1 - m.ustar)) (half_pos hρ)
      (fun τ hτ => hasDerivWithinAt_angle m (hφ τ hτ))
      (fun τ hτ => by
        rw [abs_mul, mul_assoc, ← hsimp_u]
        exact mul_le_mul_of_nonneg_left (hcd τ hτ).1 (abs_nonneg _)) t ht
  have hθt : |φ t 0| ≤ δ * Kθ := by
    have h1 := abs_sub_abs_le_abs_sub (φ t 0) (φ t₀ 0)
    have h2 : |m.η| * ((cu + 1) * δ / 2) / (m.noSyncRate / 2) = δ * (Kθ - 1) := by
      rw [hKθ]
      field_simp
      ring
    rw [h2] at hθ
    linarith
  obtain ⟨hut, hdt, hqt⟩ := hcd t ht
  rw [hsimp_u] at hut
  rw [hsimp_e] at hdt hqt
  have hx : Real.exp (-(m.noSyncRate / 2) * (t - t₀)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := mul_nonneg (half_pos hρ).le (sub_nonneg.mpr ht.1)
    linarith
  have hp1 : (0 : ℝ) ≤ (cu + 1) * δ / 2 := by positivity
  have hp2 : (0 : ℝ) ≤ (ce + 1) * δ / 2 := by positivity
  have hut' : |φ t 1 - m.ustar| ≤ (cu + 1) * δ / 2 := by
    have := mul_le_mul_of_nonneg_left hx hp1
    linarith
  have hdt' : |φ t 2 - m.iHatD (φ t 0)| ≤ (ce + 1) * δ / 2 := by
    have := mul_le_mul_of_nonneg_left hx hp2
    linarith
  have hqt' : |φ t 3 - m.iHatQ (φ t 0)| ≤ (ce + 1) * δ / 2 := by
    have := mul_le_mul_of_nonneg_left hx hp2
    linarith
  have hDt := abs_iHatD_sub_le m hN (φ t 0)
  have hQt := abs_iHatQ_sub_le m hN (φ t 0)
  rw [← hΛdef] at hDt hQt
  have h2 : |φ t 2 - m.iHatD 0| ≤ (ce + 1) * δ / 2 + Λ * |φ t 0| := by
    have := abs_sub_le (φ t 2) (m.iHatD (φ t 0)) (m.iHatD 0)
    linarith
  have h3 : |φ t 3 - m.iHatQ 0| ≤ (ce + 1) * δ / 2 + Λ * |φ t 0| := by
    have := abs_sub_le (φ t 3) (m.iHatQ (φ t 0)) (m.iHatQ 0)
    linarith
  have hn := Dynamics.norm_le_sum_abs (φ t - m.point)
  rw [Fin.sum_univ_four, PiLp.sub_apply, PiLp.sub_apply, PiLp.sub_apply, PiLp.sub_apply, p0, p1,
    p2, p3, sub_zero] at hn
  have hΛθ := mul_le_mul_of_nonneg_left hθt hΛ
  have hfin : |φ t 0| + |φ t 1 - m.ustar| + |φ t 2 - m.iHatD 0| + |φ t 3 - m.iHatQ 0| ≤ K * δ := by
    have e : K * δ = δ * Kθ + 2 * (Λ * (δ * Kθ)) + (cu + 1) * δ / 2 + 2 * ((ce + 1) * δ / 2) := by
      rw [hK]; ring
    rw [e]
    linarith
  linarith

/-! ### Family conclusions without synchronizing torque -/

private theorem point_apply (m : Model) :
    m.point 0 = 0 ∧ m.point 1 = m.ustar ∧ m.point 2 = m.iHatD 0 ∧ m.point 3 = m.iHatQ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Model.point]

/-- **Lyapunov stability without synchronizing torque**: with `C_dc, L_s, R_s > 0`,
`μ u* v₀ = 0` and `margin > 0` the operating point is Lyapunov stable. -/
@[powerlib_domain] theorem mem_den_lyapunovStable_of_no_sync (m : Model) (hC : 0 < m.Cdc)
    (hL : 0 < m.Ls) (hR : 0 < m.Rs) (hs : m.μ * m.ustar * m.v0 = 0) (hδ : 0 < m.margin) :
    connection% (m ∈ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow']
  exact lyapunovStable_of_no_sync m hC hL hR hs hδ

/-- **Boundary: no local asymptotic stability without synchronizing torque.** With `R_s > 0` and
`μ u* v₀ = 0` every `(θ, u*, î(θ))` is an equilibrium, so equilibria accumulate at the operating
point. -/
@[powerlib_domain] theorem not_mem_den_locallyAsymptoticallyStable_of_no_sync (m : Model)
    (hR : 0 < m.Rs) (hs : m.μ * m.ustar * m.v0 = 0) :
    connection% (m ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow']
  have hN := N_pos m hR
  have hκ := kappa_eq_zero_of_no_sync m hs
  set Λ := (|m.Rs * (m.μ * m.ustar)| + |m.ω0 * m.Ls * (m.μ * m.ustar)|) / m.N
  have hΛ : 0 ≤ Λ := by positivity
  apply Dynamics.not_localAsymptoticStable_of_equilibria
  intro ε hε
  set θ := ε / (2 * (1 + 2 * Λ)) with hθ
  have hθ0 : 0 < θ := by positivity
  refine ⟨WithLp.toLp 2 ![θ, m.ustar, m.iHatD θ, m.iHatQ θ], fun h => ?_, ?_,
    field_eq_zero_of_kappa_eq_zero m hN.ne' hκ θ⟩
  · have := congrArg (fun x : State 4 => x 0) h
    simp [Model.point] at this
    exact hθ0.ne' this
  · obtain ⟨p0, p1, p2, p3⟩ := point_apply m
    have hn := Dynamics.norm_le_sum_abs (WithLp.toLp 2 ![θ, m.ustar, m.iHatD θ, m.iHatQ θ] - m.point)
    simp only [Fin.sum_univ_four, PiLp.sub_apply, p0, p1, p2, p3,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, sub_zero, sub_self, abs_zero, add_zero] at hn
    have hD := abs_iHatD_sub_le m hN θ
    have hQ := abs_iHatQ_sub_le m hN θ
    rw [abs_of_pos hθ0] at hD hQ hn
    have e : (1 + 2 * Λ) * θ = ε / 2 := by
      rw [hθ]
      field_simp
    linarith

/-- The local exponential sentence fails as well. -/
@[powerlib_domain] theorem not_mem_den_locallyExponentiallyStable_of_no_sync (m : Model)
    (hR : 0 < m.Rs) (hs : m.μ * m.ustar * m.v0 = 0) :
    connection% (m ∉ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have h2 := not_mem_den_locallyAsymptoticallyStable_of_no_sync m hR hs
  unfold powerlib.TMIO.Statement at h2
  rw [mem_den_flow'] at h h2
  exact h2 (Flow.locallyExponentiallyStable_localAsymptoticStable h)

/-- A stiff-grid model without grid voltage (`v₀ = 0`, so no synchronizing torque) and with
`margin = 7/8 > 0`: `C_dc = L_s = R_s = η = μ = u*_dc = 1`, `G_dc = 1`, `K_p = 0`. -/
def noSyncModel : Model :=
  { Cdc := 1, Gdc := 1, Kp := 0, η := 1, μ := 1, ustar := 1, v0 := 0, Rs := 1, Ls := 1 }

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem noSyncModel_margin : noSyncModel.margin = 7 / 8 := by
  simp [Model.margin, Model.N, Model.ω0, noSyncModel]
  norm_num

/-- The model without synchronizing torque is Lyapunov stable. -/
@[powerlib_domain] theorem noSyncModel_mem_den_lyapunovStable :
    connection% (noSyncModel ∈ family.den (.flow .lyapunovStable)) :=
  mem_den_lyapunovStable_of_no_sync noSyncModel (by norm_num [noSyncModel])
    (by norm_num [noSyncModel]) (by norm_num [noSyncModel]) (by norm_num [noSyncModel])
    (by rw [noSyncModel_margin]; norm_num)

/-- **Boundary**: the Lyapunov translation `{physical, synchronizing, dissipative}` of
`MatchingStiffGrid.family` is sound but **not exact** — `noSyncModel` violates `synchronizing`
(`μ u* v₀ = 0`) and is Lyapunov stable. -/
@[powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := noSyncModel_mem_den_lyapunovStable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have hd : Meets noSyncModel .synchronizing := hmem .synchronizing (by
    show Requirement.synchronizing ∈ translate (.flow .lyapunovStable)
    simp [translate])
  have : (0 : ℝ) < 0 := by
    have hd' : 0 < noSyncModel.μ * noSyncModel.ustar * noSyncModel.v0 := hd
    simp [noSyncModel] at hd'
  exact lt_irrefl _ this

/-! ### No modulation and no damping: `μ = 0`, `margin = 0` -/

/-- With `μ = 0` and `margin = 0` the DC error is conserved along every forward solution:
`C_dc ũ' = −(G_dc + K_p) ũ = 0`. -/
private theorem utilde_const_of_mu_eq_zero (m : Model) (hμ : m.μ = 0) (hm : m.margin = 0)
    {φ : ℝ → State 4} (hφ : IsIntegralCurveOn φ (fun _ x => m.field x) (Ici 0)) :
    ∀ t, 0 ≤ t → φ t 1 = φ 0 1 := by
  have hGK : m.Gdc + m.Kp = 0 := by
    have : m.margin = m.Gdc + m.Kp := by simp [Model.margin, hμ]
    linarith
  have hG : m.Gdc = -m.Kp := by linarith
  have hF : ∀ x : State 4, m.field x 1 = 0 := fun x => by
    simp only [Model.field, Model.idc, Model.ixHat, Model.κ, hμ, hG, PiLp.toLp_apply,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    ring
  intro t ht
  have hc : ContinuousOn (fun τ => φ τ 1) (Icc 0 t) :=
    ((proj_contDiff (n := 4) 1).continuous.comp_continuousOn hφ.continuousOn).mono
      Icc_subset_Ici_self
  have hd : ∀ τ ∈ Ico 0 t, HasDerivWithinAt (fun τ => φ τ 1) 0 (Ici τ) τ := fun τ hτ => by
    have h := Dynamics.HasDerivWithinAt.euclidean_coord (hφ τ hτ.1) 1
    rw [hF] at h
    exact h.mono (Ici_subset_Ici.mpr hτ.1)
  exact constant_of_has_deriv_right_zero hc hd t ⟨ht, le_rfl⟩

/-- With `μ = 0`, `margin = 0` and `R_s > 0`, for every `a` and `θ₀` the drifting motion
`(θ₀ + η a t, u* + a, î(θ₀))` is a solution: the angle drifts linearly whenever `η a ≠ 0`. -/
private theorem drift_isIntegralCurveOn (m : Model) (hR : 0 < m.Rs) (hμ : m.μ = 0)
    (hm : m.margin = 0) (a θ₀ : ℝ) :
    IsIntegralCurveOn (fun t => WithLp.toLp 2 ![θ₀ + m.η * a * t, m.ustar + a, m.iHatD θ₀,
      m.iHatQ θ₀]) (fun _ x => m.field x) univ := by
  have hN := (N_pos m hR).ne'
  have hG : m.Gdc = -m.Kp := by
    have : m.margin = m.Gdc + m.Kp := by simp [Model.margin, hμ]
    linarith
  have hfield : ∀ θ : ℝ, m.field (WithLp.toLp 2 ![θ, m.ustar + a, m.iHatD θ₀, m.iHatQ θ₀]) =
      WithLp.toLp 2 ![m.η * a, 0, 0, 0] := by
    intro θ
    ext i
    fin_cases i
    · simp only [Model.field, Model.ω0, PiLp.toLp_apply, Matrix.cons_val_zero, Fin.zero_eta,
        Fin.isValue, Matrix.cons_val_one]
      ring
    · simp only [Model.field, Model.idc, Model.ixHat, Model.κ, hμ, hG, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, Fin.mk_one]
      ring
    · simp only [Model.field, Model.iHatD, Model.iHatQ, hμ, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons, Fin.isValue, Fin.reduceFinMk]
      field_simp
      simp only [Model.N]
      ring
    · simp only [Model.field, Model.iHatD, Model.iHatQ, hμ, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons, Fin.isValue, Fin.reduceFinMk]
      field_simp
      simp only [Model.N]
      ring
  intro t _
  show HasDerivWithinAt _ (m.field (WithLp.toLp 2 ![θ₀ + m.η * a * t, m.ustar + a, m.iHatD θ₀,
    m.iHatQ θ₀])) univ t
  rw [hfield]
  apply Dynamics.hasDerivWithinAt_euclidean_of_coord
  intro i
  apply HasDerivAt.hasDerivWithinAt
  fin_cases i
  · have h := ((hasDerivAt_id t).const_mul (m.η * a)).const_add θ₀
    simp only [id, mul_one] at h
    simpa using h
  · simpa using hasDerivAt_const t (m.ustar + a)
  · simpa using hasDerivAt_const t (m.iHatD θ₀)
  · simpa using hasDerivAt_const t (m.iHatQ θ₀)

/-- **Counterexample (no modulation, `margin = 0`).** The drifting solution with `ũ_dc ≡ 1` never
approaches the source's set `{ũ_dc = 0, ∇S = 0, ĩ_dq = 0}`. -/
private theorem not_tendsto_critical_of_mu_eq_zero (m : Model) (hR : 0 < m.Rs) (hμ : m.μ = 0)
    (hm : m.margin = 0) :
    ∃ φ : ℝ → State 4, IsIntegralCurveOn φ (fun _ x => m.field x) (Ici 0) ∧
      (∀ t, φ t 1 = m.ustar + 1) ∧
      ¬ Tendsto φ atTop (𝓝ˢ {x : State 4 | x 1 = m.ustar ∧ deriv m.potential (x 0) = 0 ∧
        x 2 = m.iHatD (x 0) ∧ x 3 = m.iHatQ (x 0)}) := by
  refine ⟨fun t => WithLp.toLp 2 ![0 + m.η * 1 * t, m.ustar + 1, m.iHatD 0, m.iHatQ 0],
    (drift_isIntegralCurveOn m hR hμ hm 1 0).mono (subset_univ _), fun t => by simp,
    fun h => ?_⟩
  have hU : {x : State 4 | x 1 ≠ m.ustar + 1} ∈ 𝓝ˢ {x : State 4 | x 1 = m.ustar ∧
      deriv m.potential (x 0) = 0 ∧ x 2 = m.iHatD (x 0) ∧ x 3 = m.iHatQ (x 0)} := by
    refine (isOpen_ne_fun (proj_contDiff (n := 4) 1).continuous continuous_const).mem_nhdsSet.mpr ?_
    rintro x ⟨hx, -⟩
    show x 1 ≠ m.ustar + 1
    rw [hx]
    intro h'
    linarith
  obtain ⟨T, hT⟩ := eventually_atTop.mp (h hU)
  exact hT T le_rfl (by simp)

/-- **Instability (no modulation, `margin = 0`, `η ≠ 0`)**: an arbitrarily small DC offset makes the
angle drift away linearly. -/
@[powerlib_domain] theorem mem_den_unstable_of_mu_eq_zero (m : Model) (hR : 0 < m.Rs)
    (hμ : m.μ = 0) (hm : m.margin = 0) (hη : m.η ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow']
  intro hLS
  obtain ⟨δ, hδ, hb⟩ := hLS 1 one_pos
  set a := δ / 2 with ha
  have ha0 : 0 < a := by positivity
  set T := 2 / (|m.η| * a) with hT
  have hηa : 0 < |m.η| * a := mul_pos (abs_pos.mpr hη) ha0
  have hT0 : 0 < T := by positivity
  set φ := fun t => WithLp.toLp 2 ![0 + m.η * a * t, m.ustar + a, m.iHatD 0, m.iHatQ 0]
  have hφ : IsTrajectoryOn φ m.field 0 T :=
    (drift_isIntegralCurveOn m hR hμ hm a 0).mono (subset_univ _)
  obtain ⟨p0, p1, p2, p3⟩ := point_apply m
  have hv : φ 0 = WithLp.toLp 2 ![(0 : ℝ), m.ustar + a, m.iHatD 0, m.iHatQ 0] := by
    simp [φ]
  have h0 : ‖φ 0 - m.point‖ < δ := by
    rw [hv]
    have hn := Dynamics.norm_le_sum_abs
      (WithLp.toLp 2 ![(0 : ℝ), m.ustar + a, m.iHatD 0, m.iHatQ 0] - m.point)
    simp only [Fin.sum_univ_four, PiLp.sub_apply, p0, p1, p2, p3,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, sub_self, abs_zero, add_zero,
      add_sub_cancel_left, zero_add] at hn
    rw [abs_of_pos ha0] at hn
    linarith
  have hfar := hb 0 T φ hφ h0 T ⟨hT0.le, le_rfl⟩
  have hc := PiLp.norm_apply_le (φ T - m.point) 0
  have hφT : φ T 0 = m.η * a * T := by simp [φ]
  rw [PiLp.sub_apply, p0, sub_zero, hφT, Real.norm_eq_abs] at hc
  have : |m.η * a * T| = 2 := by
    rw [abs_mul, abs_mul, abs_of_pos ha0, abs_of_pos hT0, hT]
    field_simp
  linarith

/-! ### Modulation without synchronizing torque at `margin = 0`: `μ ≠ 0`, `u* v₀ = 0` -/

/-- **LaSalle set at `margin = 0` without synchronizing torque** (`μ ≠ 0`, `μ u* v₀ = 0`): a solution
segment of positive length staying on the cylinder where `dH/dt = 0` starts at `ũ = 0, ĩ = 0`. If
`μ ω₀ L_s ≠ 0` the energy is `a ũ²/2` there and `C_dc ũ' = g ũ` (`g > 0`), so `ũ ≠ 0` cannot keep the
energy constant; if `ω₀ = 0` the set is `ĩ = 0` and keeping `ĩ_d, ĩ_q ≡ 0` forces
`μ ũ (s/L_s − u*η c/R_s) = 0 = μ ũ (c/L_s + u*η s/R_s)`, hence `μ ũ (c² + s²)/L_s = 0`. -/
private theorem no_sync_margin_zero_segment (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls)
    (hR : 0 < m.Rs) (hμ : m.μ ≠ 0) (hs : m.μ * m.ustar * m.v0 = 0) (hm : m.margin = 0) {T : ℝ}
    {ψ : ℝ → State 5} (hT : 0 < T) (hψ : IsTrajectoryOn ψ m.cylField 0 T)
    (hE : ∀ t ∈ Icc 0 T, ψ t 0 ^ 2 + ψ t 1 ^ 2 = 1 ∧
      fderiv ℝ m.cylEnergy (ψ t) (m.cylField (ψ t)) = 0) :
    ψ 0 2 = m.ustar ∧ ψ 0 3 = m.cD (ψ 0 0) (ψ 0 1) ∧ ψ 0 4 = m.cQ (ψ 0 0) (ψ 0 1) := by
  have hN := N_pos m hR
  have hκ := kappa_eq_zero_of_no_sync m hs
  have hk := k_eq_zero_of_no_sync m hs
  have hrel := fun t (ht : t ∈ Icc 0 T) =>
    cylLie_eq_zero_of_margin_eq_zero m hR hL hC hm (hE t ht).1 (hE t ht).2
  have hco : ∀ {I : Set ℝ}, I ⊆ Icc 0 T → ∀ t ∈ I, ∀ i,
      HasDerivWithinAt (fun τ => ψ τ i) (m.cylField (ψ t) i) I t :=
    fun hI t ht i => Dynamics.HasDerivWithinAt.euclidean_coord ((hψ t (hI ht)).mono hI) i
  have hF0 : ∀ y : State 5, m.cylField y 0 = -(y 1) * (m.η * (y 2 - m.ustar)) := fun y => by
    simp only [Model.cylField, Model.ω0, PiLp.toLp_apply, Matrix.cons_val_zero]
    ring
  have hF1 : ∀ y : State 5, m.cylField y 1 = y 0 * (m.η * (y 2 - m.ustar)) := fun y => by
    simp only [Model.cylField, Model.ω0, PiLp.toLp_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    ring
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hu0 : ψ 0 2 = m.ustar := by
    by_cases hB : m.μ * m.ω0 * m.Ls = 0
    · -- `ω₀ = 0`: the LaSalle set is `ĩ = 0`
      have hω : m.ω0 = 0 := by
        rcases mul_eq_zero.mp hB with h | h
        · exact (mul_eq_zero.mp h).resolve_left hμ
        · exact absurd h hL.ne'
      have hNR : m.N = m.Rs ^ 2 := by simp [Model.N, hω]
      have hcD : ∀ c s : ℝ, m.cD c s = m.μ * m.ustar * s / m.Rs := fun c s => by
        simp only [Model.cD, hNR, hω]
        field_simp
        ring
      have hcQ : ∀ c s : ℝ, m.cQ c s = (m.v0 - m.μ * m.ustar * c) / m.Rs := fun c s => by
        simp only [Model.cQ, hNR, hω]
        field_simp
        ring
      have he3 : ∀ t ∈ Icc 0 T, ψ t 3 = m.μ * m.ustar * ψ t 1 / m.Rs := fun t ht => by
        have := (hrel t ht).1
        rw [hB, zero_div, neg_zero, zero_mul, zero_mul, hcD] at this
        linarith
      have he4 : ∀ t ∈ Icc 0 T, ψ t 4 = (m.v0 - m.μ * m.ustar * ψ t 0) / m.Rs := fun t ht => by
        have := (hrel t ht).2
        rw [hB, zero_div, neg_zero, zero_mul, zero_mul, hcQ] at this
        linarith
      have d3 : HasDerivWithinAt (fun τ => ψ τ 3 - m.μ * m.ustar * ψ τ 1 / m.Rs)
          (m.cylField (ψ 0) 3 - m.μ * m.ustar * m.cylField (ψ 0) 1 / m.Rs) (Icc 0 T) 0 :=
        (hco subset_rfl 0 h0T 3).sub (((hco subset_rfl 0 h0T 1).const_mul (m.μ * m.ustar)).div_const
          m.Rs)
      have d4 : HasDerivWithinAt (fun τ => ψ τ 4 - (m.v0 - m.μ * m.ustar * ψ τ 0) / m.Rs)
          (m.cylField (ψ 0) 4 - (-(m.μ * m.ustar * m.cylField (ψ 0) 0)) / m.Rs) (Icc 0 T) 0 :=
        (hco subset_rfl 0 h0T 4).sub ((((hco subset_rfl 0 h0T 0).const_mul
          (m.μ * m.ustar)).const_sub m.v0).div_const m.Rs)
      have z3 := Dynamics.HasDerivWithinAt.eq_zero_of_eqOn_Icc hT h0T d3 (c := 0)
        (fun τ hτ => by rw [he3 τ hτ]; ring)
      have z4 := Dynamics.HasDerivWithinAt.eq_zero_of_eqOn_Icc hT h0T d4 (c := 0)
        (fun τ hτ => by rw [he4 τ hτ]; ring)
      have g3 : m.cylField (ψ 0) 3 = m.μ * ψ 0 1 * (ψ 0 2 - m.ustar) / m.Ls := by
        simp only [Model.cylField, PiLp.toLp_apply, Matrix.cons_val_three, Matrix.head_cons,
          Matrix.tail_cons, hω]
        rw [he3 0 h0T]
        field_simp
        ring
      have g4 : m.cylField (ψ 0) 4 = -(m.μ * ψ 0 0 * (ψ 0 2 - m.ustar)) / m.Ls := by
        simp only [Model.cylField, PiLp.toLp_apply, Matrix.cons_val_four, Matrix.head_cons,
          Matrix.tail_cons, hω]
        rw [he4 0 h0T]
        field_simp
        ring
      rw [g3, hF1] at z3
      rw [g4, hF0] at z4
      have hy := (hE 0 h0T).1
      have key : m.μ * (ψ 0 2 - m.ustar) / m.Ls = 0 := by
        linear_combination ψ 0 1 * z3 - ψ 0 0 * z4 - (m.μ * (ψ 0 2 - m.ustar) / m.Ls) * hy
      rw [div_eq_zero_iff, or_iff_left hL.ne'] at key
      have := (mul_eq_zero.mp key).resolve_left hμ
      linarith
    · -- `μ ω₀ L_s ≠ 0`: negatively damped DC row on a set of constant energy
      by_contra hne
      have hcont2 : Continuous (fun y : State 5 => y 2) := (proj_contDiff 2).continuous
      obtain ⟨t₁, h01, h1T, hU⟩ := Dynamics.exists_Icc_mem_of_isOpen hψ.continuousOn
        (U := {y : State 5 | y 2 ≠ m.ustar}) (isOpen_ne_fun hcont2 continuous_const)
        (show (0 : ℝ) ∈ Ico 0 T from ⟨le_rfl, hT⟩) hne
      have hsub : Icc 0 t₁ ⊆ Icc 0 T := Icc_subset_Icc le_rfl h1T
      have hEn := fun t (ht : t ∈ Icc 0 T) =>
        cylEnergy_of_rel m (hE t ht).1 (hrel t ht).1 (hrel t ht).2
      set a := m.Cdc + m.Ls * (m.μ * m.ω0 * m.Ls / (2 * m.Rs * m.N)) ^ 2 * m.N
      have ha : 0 < a := by positivity
      have h0I : (0 : ℝ) ∈ Icc 0 t₁ := ⟨le_rfl, h01.le⟩
      have d1 : HasDerivWithinAt (fun τ => m.cylEnergy (ψ τ))
          (fderiv ℝ m.cylEnergy (ψ 0) (m.cylField (ψ 0))) (Icc 0 t₁) 0 :=
        ((cylEnergy_contDiff m).differentiable (by norm_num) (ψ 0)).hasFDerivAt.comp_hasDerivWithinAt
          0 ((hψ 0 h0T).mono hsub)
      rw [(hE 0 h0T).2] at d1
      have d1' : HasDerivWithinAt (fun τ => a / 2 * (ψ τ 2 - m.ustar) ^ 2 + m.k * (1 - ψ τ 0)) 0
          (Icc 0 t₁) 0 :=
        d1.congr (fun τ hτ => (hEn τ (hsub hτ)).symm) (hEn 0 h0T).symm
      have d2 : HasDerivWithinAt (fun τ => a / 2 * (ψ τ 2 - m.ustar) ^ 2 + m.k * (1 - ψ τ 0))
          (a / 2 * (2 * (ψ 0 2 - m.ustar) * m.cylField (ψ 0) 2) +
            m.k * (-(m.cylField (ψ 0) 0))) (Icc 0 t₁) 0 := by
        have h2 := hco hsub 0 h0I 2
        have h0 := hco hsub 0 h0I 0
        convert (((h2.sub_const m.ustar).pow 2).const_mul (a / 2)).add
          ((h0.const_sub 1).const_mul m.k) using 1
        simp only [Nat.cast_ofNat]
        ring
      have heq := (uniqueDiffOn_Icc h01 0 h0I).eq_deriv _ d2 d1'
      rw [hk, zero_mul, add_zero] at heq
      have hut : ψ 0 2 - m.ustar ≠ 0 := sub_ne_zero.mpr hne
      have hg2 : m.cylField (ψ 0) 2 = 0 := by
        have : a * (ψ 0 2 - m.ustar) * m.cylField (ψ 0) 2 = 0 := by linear_combination heq
        exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero ha.ne' hut)
      have hDC := cylField_two_of_rel m hC.ne' hm (hE 0 h0T).1 (hrel 0 h0T).1 (hrel 0 h0T).2
      rw [hg2, mul_zero, hκ, zero_mul, sub_zero] at hDC
      have hg : 0 < (m.μ * m.ω0 * m.Ls) ^ 2 / (4 * m.Rs * m.N) := by positivity
      exact hut ((mul_eq_zero.mp hDC.symm).resolve_left hg.ne')
  obtain ⟨r3, r4⟩ := hrel 0 h0T
  rw [hu0, sub_self, mul_zero, zero_mul] at r3 r4
  exact ⟨hu0, by linarith, by linarith⟩

/-- **Modulation without synchronizing torque at `margin = 0`** (`μ ≠ 0`, `u* v₀ = 0`): every forward
solution has `ũ_dc → 0` and `ĩ_dq → 0` (uniformly in the angle), by LaSalle on the cylinder. -/
private theorem tendsto_error_of_no_sync_margin_zero (m : Model) (hC : 0 < m.Cdc)
    (hL : 0 < m.Ls) (hR : 0 < m.Rs) (hμ : m.μ ≠ 0) (hs : m.μ * m.ustar * m.v0 = 0)
    (hm : m.margin = 0) {φ : ℝ → State 4}
    (hφ : IsIntegralCurveOn φ (fun _ x => m.field x) (Ici 0)) :
    Tendsto (fun t => φ t 1 - m.ustar) atTop (𝓝 0) ∧
      Tendsto (fun t => φ t 2 - m.iHatD (φ t 0)) atTop (𝓝 0) ∧
      Tendsto (fun t => φ t 3 - m.iHatQ (φ t 0)) atTop (𝓝 0) := by
  have hψ := Dynamics.LaSalle.isIntegralCurveOn_comp_of_fderiv (cyl_contDiff.differentiable (by norm_num))
    (fderiv_cyl_field m) hφ
  have hT : Tendsto (fun t => cyl (φ t)) atTop (𝓝ˢ {y : State 5 | y 2 = m.ustar ∧
      y 3 = m.cD (y 0) (y 1) ∧ y 4 = m.cQ (y 0) (y 1)}) := by
    refine Dynamics.LaSalle.lasalle_levelSet (h := fun y : State 5 => y 0 ^ 2 + y 1 ^ 2) (c₀ := 1)
      (c := m.cylEnergy (cyl (φ 0))) (cylField_contDiff m)
      (circle_contDiff.differentiable (by norm_num)) (cylEnergy_contDiff m)
      (fderiv_circle_cylField m)
      (fun y hy => (cylLie_le m hR hL.ne' hC.ne' hy).trans
        (by rw [hm]; simp))
      (isCompact_cylSublevel m hC hL hR _) ?_ hψ (by simp) le_rfl
    refine Dynamics.LaSalle.lasalle_condition_of_trajectories_mem (cylField_contDiff m) ?_
    intro T ψ hT hψ hstay
    exact no_sync_margin_zero_segment m hC hL hR hμ hs hm hT hψ fun t ht =>
      ⟨(hstay t ht).1.1, (hstay t ht).2⟩
  have c5 : ∀ j : Fin 5, Continuous (fun y : State 5 => y j) := fun j =>
    (proj_contDiff j).continuous
  have hcD : Continuous (fun y : State 5 => y 3 - m.cD (y 0) (y 1)) := by
    have h0 := c5 0
    have h1 := c5 1
    have h3 := c5 3
    unfold Model.cD
    fun_prop
  have hcQ : Continuous (fun y : State 5 => y 4 - m.cQ (y 0) (y 1)) := by
    have h0 := c5 0
    have h1 := c5 1
    have h4 := c5 4
    unfold Model.cQ
    fun_prop
  refine ⟨?_, ?_, ?_⟩
  · have := Dynamics.LaSalle.tendsto_zero_of_tendsto_nhdsSet hT ((c5 2).sub continuous_const)
      (fun y hy => sub_eq_zero.mpr hy.1)
    simpa using this
  · have := Dynamics.LaSalle.tendsto_zero_of_tendsto_nhdsSet hT hcD
      (fun y hy => sub_eq_zero.mpr hy.2.1)
    simpa [cD_cos_sin] using this
  · have := Dynamics.LaSalle.tendsto_zero_of_tendsto_nhdsSet hT hcQ
      (fun y hy => sub_eq_zero.mpr hy.2.2)
    simpa [cQ_cos_sin] using this

namespace Model
variable (m : Model)

/-- The rotation-reduced error dynamics without synchronizing torque, state
`(ũ_dc, w_d, w_q)`, `w = R_θᵀ ĩ_dq` (`red`): `C_dc ũ' = −(G_dc+K_p) ũ + μ w_q`,
`L_s w' = −Z_s w − ũ (μω₀L_sR_s/N, μR_s²/N) − L_s η ũ J w`. -/
def redField (z : State 3) : State 3 :=
  WithLp.toLp 2 ![
    (-(m.Gdc + m.Kp) * z 0 + m.μ * z 2) / m.Cdc,
    (-(m.Rs * z 1 - m.ω0 * m.Ls * z 2)) / m.Ls - m.μ * m.ω0 * m.Rs / m.N * z 0 +
      m.η * z 0 * z 2,
    (-(m.ω0 * m.Ls * z 1 + m.Rs * z 2)) / m.Ls - m.μ * m.Rs ^ 2 / (m.N * m.Ls) * z 0 -
      m.η * z 0 * z 1]

/-- The reduction `x ↦ (ũ_dc, R_θᵀ (i_dq − î_dq(θ)))`. -/
def red (x : State 4) : State 3 :=
  WithLp.toLp 2 ![x 1 - m.ustar,
    Real.cos (x 0) * (x 2 - m.iHatD (x 0)) + Real.sin (x 0) * (x 3 - m.iHatQ (x 0)),
    -Real.sin (x 0) * (x 2 - m.iHatD (x 0)) + Real.cos (x 0) * (x 3 - m.iHatQ (x 0))]

end Model

/-- Rotated internal model and its slope. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem red_identity_aux (m : Model) (hN : m.N ≠ 0) (θ : ℝ) :
    Real.cos θ * m.iHatD θ + Real.sin θ * m.iHatQ θ =
        (m.ω0 * m.Ls * m.v0 * Real.cos θ + m.Rs * m.v0 * Real.sin θ - m.ω0 * m.Ls * (m.μ * m.ustar)) /
          m.N ∧
      -Real.sin θ * m.iHatD θ + Real.cos θ * m.iHatQ θ =
        (-(m.ω0 * m.Ls * m.v0 * Real.sin θ) + m.Rs * m.v0 * Real.cos θ - m.Rs * (m.μ * m.ustar)) /
          m.N ∧
      Real.cos θ * (m.μ * m.ustar * (m.Rs * Real.cos θ + m.ω0 * m.Ls * Real.sin θ) / m.N) +
        Real.sin θ * (m.μ * m.ustar * (m.Rs * Real.sin θ - m.ω0 * m.Ls * Real.cos θ) / m.N) =
        m.μ * m.ustar * m.Rs / m.N ∧
      -Real.sin θ * (m.μ * m.ustar * (m.Rs * Real.cos θ + m.ω0 * m.Ls * Real.sin θ) / m.N) +
        Real.cos θ * (m.μ * m.ustar * (m.Rs * Real.sin θ - m.ω0 * m.Ls * Real.cos θ) / m.N) =
        -(m.μ * m.ustar * m.ω0 * m.Ls) / m.N := by
  have hsc := Real.sin_sq_add_cos_sq θ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Model.iHatD, Model.iHatQ]
    field_simp
    linear_combination (-(m.ω0 * m.Ls * (m.μ * m.ustar))) * hsc
  · simp only [Model.iHatD, Model.iHatQ]
    field_simp
    linear_combination (-(m.Rs * (m.μ * m.ustar))) * hsc
  · field_simp
    linear_combination (m.μ * m.ustar * m.Rs) * hsc
  · field_simp
    linear_combination (-(m.μ * m.ustar * m.ω0 * m.Ls)) * hsc

/-- The chain rule for `red` along the closed loop equals the reduced field (with `κ = 0`). Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem red_field_identity (m : Model) (hN : m.N ≠ 0) (hL : m.Ls ≠ 0) (hκ : m.κ = 0)
    (x : State 4) :
    m.field x 1 = m.redField (m.red x) 0 ∧
    -Real.sin (x 0) * m.field x 0 * (x 2 - m.iHatD (x 0)) +
        Real.cos (x 0) * (m.field x 2 - m.μ * m.ustar *
          (m.Rs * Real.cos (x 0) + m.ω0 * m.Ls * Real.sin (x 0)) / m.N * m.field x 0) +
        (Real.cos (x 0) * m.field x 0 * (x 3 - m.iHatQ (x 0)) +
          Real.sin (x 0) * (m.field x 3 - m.μ * m.ustar *
            (m.Rs * Real.sin (x 0) - m.ω0 * m.Ls * Real.cos (x 0)) / m.N * m.field x 0)) =
      m.redField (m.red x) 1 ∧
    -Real.cos (x 0) * m.field x 0 * (x 2 - m.iHatD (x 0)) +
        -Real.sin (x 0) * (m.field x 2 - m.μ * m.ustar *
          (m.Rs * Real.cos (x 0) + m.ω0 * m.Ls * Real.sin (x 0)) / m.N * m.field x 0) +
        (-Real.sin (x 0) * m.field x 0 * (x 3 - m.iHatQ (x 0)) +
          Real.cos (x 0) * (m.field x 3 - m.μ * m.ustar *
            (m.Rs * Real.sin (x 0) - m.ω0 * m.Ls * Real.cos (x 0)) / m.N * m.field x 0)) =
      m.redField (m.red x) 2 := by
  obtain ⟨hY, hZ, hX, hW⟩ := red_identity_aux m hN (x 0)
  have hsc := Real.sin_sq_add_cos_sq (x 0)
  have hN1 : (m.Rs ^ 2 + m.ω0 ^ 2 * m.Ls ^ 2) / m.N = 1 := by
    rw [div_eq_one_iff_eq hN]
    simp [Model.N]
  have hc2 : m.μ / m.Ls - m.μ * m.ω0 ^ 2 * m.Ls / m.N = m.μ * m.Rs ^ 2 / (m.N * m.Ls) := by
    field_simp
    simp only [Model.N]
    ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [Model.field, Model.redField, Model.red, Model.idc, Model.ixHat, hκ,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  · simp only [Model.field, Model.redField, Model.red, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, Model.ω0] at hY hZ hX hW hN1 ⊢
    linear_combination (-(m.η * x 1 - m.η * m.ustar)) * hX + (-m.Rs / m.Ls) * hY +
      (m.η * m.ustar * m.Ls / m.Ls) * hZ + (-(Real.sin (x 0) * m.v0) / m.Ls) * hN1
  · simp only [Model.field, Model.redField, Model.red, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, Model.ω0] at hY hZ hX hW hc2 hN1 ⊢
    linear_combination (-(m.η * x 1 - m.η * m.ustar)) * hW + (-(m.η * m.ustar * m.Ls) / m.Ls) * hY +
      (-m.Rs / m.Ls) * hZ + (-(m.μ * x 1) / m.Ls) * hsc +
      ((m.μ * m.ustar - m.v0 * Real.cos (x 0)) / m.Ls) * hN1 + (-(x 1 - m.ustar)) * hc2

/-- The reduction carries solutions to solutions of the reduced field (`κ = 0`). Implementation
evidence. -/
private theorem red_isIntegralCurveOn (m : Model) (hN : m.N ≠ 0) (hL : m.Ls ≠ 0) (hκ : m.κ = 0)
    {φ : ℝ → State 4} {s : Set ℝ} (hφ : IsIntegralCurveOn φ (fun _ x => m.field x) s) :
    IsIntegralCurveOn (fun t => m.red (φ t)) (fun _ z => m.redField z) s := by
  intro t ht
  have hc : ∀ i, HasDerivWithinAt (fun τ => φ τ i) (m.field (φ t) i) s t := fun i =>
    Dynamics.HasDerivWithinAt.euclidean_coord (hφ t ht) i
  obtain ⟨e0, e1, e2⟩ := red_field_identity m hN hL hκ (φ t)
  have hθ := hc 0
  have hcos := hθ.cos
  have hsin := hθ.sin
  have hD := (hasDerivAt_iHatD m (φ t 0)).comp_hasDerivWithinAt t hθ
  have hQ := (hasDerivAt_iHatQ m (φ t 0)).comp_hasDerivWithinAt t hθ
  apply Dynamics.hasDerivWithinAt_euclidean_of_coord
  intro i
  fin_cases i
  · have h := (hc 1).sub_const m.ustar
    convert h using 1
    · funext τ
      simp [Model.red]
    · show m.redField (m.red (φ t)) 0 = _
      rw [← e0]
  · have h := (hcos.mul ((hc 2).sub hD)).add (hsin.mul ((hc 3).sub hQ))
    convert h using 1
    · funext τ
      simp [Model.red]
    · show m.redField (m.red (φ t)) 1 = _
      rw [← e1]
      simp only [Function.comp_apply, Pi.sub_apply]
  · have h := ((hsin.neg).mul ((hc 2).sub hD)).add (hcos.mul ((hc 3).sub hQ))
    convert h using 1
    · funext τ
      simp [Model.red]
    · show m.redField (m.red (φ t)) 2 = _
      rw [← e2]
      simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply]
      ring

/-- The Jacobian of the reduced field at the origin. -/
def Model.redJac (m : Model) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-(m.Gdc + m.Kp) / m.Cdc, 0, m.μ / m.Cdc;
     -(m.μ * m.ω0 * m.Rs / m.N), -m.Rs / m.Ls, m.ω0;
     -(m.μ * m.Rs ^ 2 / (m.N * m.Ls)), -m.ω0, -m.Rs / m.Ls]

private theorem toEuclideanCLM_apply3 (A : Matrix (Fin 3) (Fin 3) ℝ) (v : State 3) (i : Fin 3) :
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) A v) i =
      A i 0 * v 0 + A i 1 * v 1 + A i 2 * v 2 := by
  simp [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem redField_contDiff (m : Model) : ContDiff ℝ 1 m.redField := by
  have h0 := proj_contDiff (n := 3) 0
  have h1 := proj_contDiff (n := 3) 1
  have h2 := proj_contDiff (n := 3) 2
  rw [contDiff_euclidean]
  intro i
  fin_cases i <;> simp [Model.redField] <;> fun_prop

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem redField_zero (m : Model) : m.redField 0 = 0 := by
  ext i
  fin_cases i <;> simp [Model.redField]

/-- The Jacobian of the reduced field at the origin. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem hasFDerivAt_redField_zero (m : Model) (hL : m.Ls ≠ 0) :
    HasFDerivAt m.redField (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.redJac) 0 := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have hp : ∀ k : Fin 3, HasFDerivAt (fun x : State 3 => x k)
      (PiLp.proj 2 (fun _ : Fin 3 => ℝ) k : State 3 →L[ℝ] ℝ) (0 : State 3) :=
    fun k => (PiLp.proj 2 (fun _ : Fin 3 => ℝ) k : State 3 →L[ℝ] ℝ).hasFDerivAt
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  fin_cases i
  · have h := ((h0.const_mul (-(m.Gdc + m.Kp))).add (h2.const_mul m.μ)).mul_const m.Cdc⁻¹
    convert h using 1
    · funext z
      simp [Model.redField, div_eq_mul_inv]
    · apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply]
      rw [toEuclideanCLM_apply3]
      simp [Model.redJac]
      ring
  · have h := (((h1.const_mul m.Rs).sub (h2.const_mul (m.ω0 * m.Ls))).neg.mul_const m.Ls⁻¹).sub
      (h0.const_mul (m.μ * m.ω0 * m.Rs / m.N)) |>.add ((h0.const_mul m.η).mul h2)
    convert h using 1
    · funext z
      simp [Model.redField, div_eq_mul_inv]
    · apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply]
      rw [toEuclideanCLM_apply3]
      simp [Model.redJac]
      field_simp
      ring
  · have h := (((h1.const_mul (m.ω0 * m.Ls)).add (h2.const_mul m.Rs)).neg.mul_const m.Ls⁻¹).sub
      (h0.const_mul (m.μ * m.Rs ^ 2 / (m.N * m.Ls))) |>.sub ((h0.const_mul m.η).mul h1)
    convert h using 1
    · funext z
      simp [Model.redField, div_eq_mul_inv]
    · apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.comp_apply, PiLp.proj_apply]
      rw [toEuclideanCLM_apply3]
      simp [Model.redJac]
      field_simp
      ring

private theorem isHurwitz_aux {a b c1 c2 e f : ℝ} (ha : a ≤ 0) (he : e < 0) (hbc2 : b * c2 < 0)
    (hbc1 : b * c1 * f ≤ 0) (hdet : a * (e ^ 2 + f ^ 2) - b * c1 * f - b * e * c2 < 0) :
    LinearSystems.IsHurwitz !![a, 0, b; c1, e, f; c2, -f, e] := by
  rw [Criteria.isHurwitz_fin_three_iff]
  simp only [Matrix.trace_fin_three, Matrix.det_fin_three, Criteria.principalMinorSum,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const]
  have h1 : a ^ 2 * e ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) he.le
  have h2 : 0 ≤ a * (b * c2) := mul_nonneg_of_nonpos_of_nonpos ha hbc2.le
  have h3 : a * e ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha (sq_nonneg e)
  have h4 : 0 < b * c2 * e := mul_pos_of_neg_of_neg hbc2 he
  have h5 : e ^ 3 < 0 := by
    have : e ^ 3 = e * e ^ 2 := by ring
    rw [this]
    exact mul_neg_of_neg_of_pos he (by rw [sq]; exact mul_pos_of_neg_of_neg he he)
  have h6 : e * f ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg he.le (sq_nonneg f)
  refine ⟨by linarith, by linarith, by nlinarith⟩

/-- With `C_dc, L_s, R_s > 0`, `μ ≠ 0` and `margin ≥ 0` the reduced Jacobian is Hurwitz (Routh–Hurwitz: `tr < 0`, `det < 0`, `tr · Σ minors < det`; at `margin = 0` the determinant is `−μ²(X² − 3R_s²X + 4R_s⁴)/(4R_s C_dc L_s² N) < 0`, `X = ω₀²L_s²`). Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem redJac_isHurwitz (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls) (hR : 0 < m.Rs)
    (hμ : m.μ ≠ 0) (hδ : 0 ≤ m.margin) : LinearSystems.IsHurwitz m.redJac := by
  have hN := N_pos m hR
  have hP : m.μ ^ 2 * m.ω0 ^ 2 * m.Ls ^ 2 ≤ 4 * m.Rs * m.N * (m.Gdc + m.Kp) := by
    have h := hδ
    simp only [Model.margin] at h
    have h4 : 0 < 4 * m.Rs * m.N := by positivity
    have := (div_le_iff₀ h4).mp (by linarith : m.μ ^ 2 * m.ω0 ^ 2 * m.Ls ^ 2 / (4 * m.Rs * m.N) ≤
      m.Gdc + m.Kp)
    linarith
  have hP0 : 0 ≤ m.Gdc + m.Kp := by
    have : 0 ≤ m.μ ^ 2 * m.ω0 ^ 2 * m.Ls ^ 2 := by positivity
    have h4 : 0 < 4 * m.Rs * m.N := by positivity
    nlinarith
  have e : m.redJac = !![-(m.Gdc + m.Kp) / m.Cdc, 0, m.μ / m.Cdc;
      -(m.μ * m.ω0 * m.Rs / m.N), -m.Rs / m.Ls, m.ω0;
      -(m.μ * m.Rs ^ 2 / (m.N * m.Ls)), -m.ω0, -m.Rs / m.Ls] := rfl
  rw [e]
  have hμ2 : 0 < m.μ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hμ))
  apply isHurwitz_aux
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith) hC.le
  · exact div_neg_of_neg_of_pos (by linarith) hL
  · have : m.μ / m.Cdc * -(m.μ * m.Rs ^ 2 / (m.N * m.Ls)) =
        -(m.μ ^ 2 * m.Rs ^ 2 / (m.Cdc * m.N * m.Ls)) := by
      field_simp
    rw [this]
    have : 0 < m.μ ^ 2 * m.Rs ^ 2 / (m.Cdc * m.N * m.Ls) := by positivity
    linarith
  · have : m.μ / m.Cdc * -(m.μ * m.ω0 * m.Rs / m.N) * m.ω0 =
        -(m.μ ^ 2 * m.ω0 ^ 2 * m.Rs / (m.Cdc * m.N)) := by
      field_simp
    rw [this]
    have : 0 ≤ m.μ ^ 2 * m.ω0 ^ 2 * m.Rs / (m.Cdc * m.N) := by positivity
    linarith
  · -- the determinant: `C L² N det = −P N² + μ² R_s (ω₀²L² − R_s²) < 0`
    have hdet : (-(m.Gdc + m.Kp) / m.Cdc * ((-m.Rs / m.Ls) ^ 2 + m.ω0 ^ 2) -
        m.μ / m.Cdc * -(m.μ * m.ω0 * m.Rs / m.N) * m.ω0 -
        m.μ / m.Cdc * (-m.Rs / m.Ls) * -(m.μ * m.Rs ^ 2 / (m.N * m.Ls))) *
        (m.Cdc * m.Ls ^ 2 * m.N) =
        -(m.Gdc + m.Kp) * m.N ^ 2 + m.μ ^ 2 * m.Rs * (m.ω0 ^ 2 * m.Ls ^ 2 - m.Rs ^ 2) := by
      field_simp
      simp only [Model.N]
      ring
    have hX : 0 ≤ m.ω0 ^ 2 * m.Ls ^ 2 := by positivity
    have hNdef : m.N = m.Rs ^ 2 + m.ω0 ^ 2 * m.Ls ^ 2 := rfl
    have hq : 0 < (m.ω0 ^ 2 * m.Ls ^ 2) ^ 2 - 3 * m.Rs ^ 2 * (m.ω0 ^ 2 * m.Ls ^ 2) + 4 * m.Rs ^ 4 := by
      nlinarith [sq_nonneg (m.ω0 ^ 2 * m.Ls ^ 2 - 3 / 2 * m.Rs ^ 2), pow_pos hR 4]
    have hneg : -(m.Gdc + m.Kp) * m.N ^ 2 + m.μ ^ 2 * m.Rs * (m.ω0 ^ 2 * m.Ls ^ 2 - m.Rs ^ 2) < 0 := by
      -- `4 R_s × (…) ≤ −μ² (X² − 3R_s²X + 4R_s⁴) < 0`
      have h1 : 4 * m.Rs * ((m.Gdc + m.Kp) * m.N ^ 2) ≥ m.μ ^ 2 * m.ω0 ^ 2 * m.Ls ^ 2 * m.N := by
        nlinarith [mul_le_mul_of_nonneg_right hP hN.le]
      have h2 : m.μ ^ 2 * ((m.ω0 ^ 2 * m.Ls ^ 2) ^ 2 - 3 * m.Rs ^ 2 * (m.ω0 ^ 2 * m.Ls ^ 2) +
          4 * m.Rs ^ 4) > 0 := mul_pos hμ2 hq
      have h4R : 0 < 4 * m.Rs := by positivity
      have key : 4 * m.Rs * (-(m.Gdc + m.Kp) * m.N ^ 2 + m.μ ^ 2 * m.Rs *
          (m.ω0 ^ 2 * m.Ls ^ 2 - m.Rs ^ 2)) < 0 := by
        rw [hNdef] at h1 ⊢
        nlinarith
      by_contra hc
      push Not at hc
      have := mul_nonneg h4R.le hc
      linarith
    have hpos : 0 < m.Cdc * m.Ls ^ 2 * m.N := by positivity
    by_contra hc
    push Not at hc
    have := mul_nonneg hc hpos.le
    rw [hdet] at this
    linarith

/-- **No synchronizing torque at `margin = 0` with modulation (`μ ≠ 0`): every forward solution
converges to one equilibrium** `(θ∞, u*, î(θ∞))`. LaSalle on the cylinder gives `ũ_dc, ĩ_dq → 0`;
the rotation-reduced error `(ũ, R_θᵀ ĩ)` solves an autonomous system whose linearization is Hurwitz
(`redJac_isHurwitz`), so once it is small it decays exponentially and `θ' = η ũ` is integrable.
Implementation evidence (Rules §3a). -/
private theorem tendsto_equilibrium_of_no_sync_margin_zero (m : Model) (hC : 0 < m.Cdc)
    (hL : 0 < m.Ls) (hR : 0 < m.Rs) (hμ : m.μ ≠ 0) (hs : m.μ * m.ustar * m.v0 = 0)
    (hm : m.margin = 0) {φ : ℝ → State 4}
    (hφ : IsIntegralCurveOn φ (fun _ x => m.field x) (Ici 0)) :
    ∃ θ : ℝ, Tendsto φ atTop (𝓝 (WithLp.toLp 2 ![θ, m.ustar, m.iHatD θ, m.iHatQ θ])) := by
  have hN := N_pos m hR
  have hκ := kappa_eq_zero_of_no_sync m hs
  obtain ⟨hu, hd, hq⟩ := tendsto_error_of_no_sync_margin_zero m hC hL hR hμ hs hm hφ
  have hρ : IsIntegralCurveOn (fun t => m.red (φ t)) (fun _ z => m.redField z) (Ici 0) :=
    red_isIntegralCurveOn m hN.ne' hL.ne' hκ hφ
  have hb : Tendsto (fun t => |φ t 2 - m.iHatD (φ t 0)| + |φ t 3 - m.iHatQ (φ t 0)|) atTop
      (𝓝 0) := by
    simpa using hd.abs.add hq.abs
  have hrot : ∀ θ a b : ℝ, |Real.cos θ * a + Real.sin θ * b| ≤ |a| + |b| ∧
      |-Real.sin θ * a + Real.cos θ * b| ≤ |a| + |b| := fun θ a b => by
    have hc := Real.abs_cos_le_one θ
    have hs := Real.abs_sin_le_one θ
    constructor
    · calc |Real.cos θ * a + Real.sin θ * b| ≤ |Real.cos θ| * |a| + |Real.sin θ| * |b| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ 1 * |a| + 1 * |b| := by gcongr
        _ = |a| + |b| := by ring
    · calc |-Real.sin θ * a + Real.cos θ * b| ≤ |Real.sin θ| * |a| + |Real.cos θ| * |b| := by
            rw [← abs_neg (Real.sin θ), ← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ 1 * |a| + 1 * |b| := by gcongr
        _ = |a| + |b| := by ring
  have hρ0 : Tendsto (fun t => m.red (φ t)) atTop (𝓝 0) := by
    apply Dynamics.tendsto_euclidean_of_coord
    intro i
    fin_cases i
    · simpa [Model.red] using hu
    · simp only [PiLp.zero_apply]
      refine squeeze_zero_norm' (Eventually.of_forall fun t => ?_) hb
      simpa [Model.red] using (hrot (φ t 0) _ _).1
    · simp only [PiLp.zero_apply]
      refine squeeze_zero_norm' (Eventually.of_forall fun t => ?_) hb
      simpa [Model.red] using (hrot (φ t 0) _ _).2
  obtain ⟨r, Cc, a, hr, hC1, ha, hles⟩ := Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian
    m.redJac (redField_contDiff m) (redField_zero m) (hasFDerivAt_redField_zero m hL.ne').fderiv
    (redJac_isHurwitz m hC hL hR hμ hm.ge)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    ((hρ0.eventually (Metric.ball_mem_nhds 0 hr)).and (eventually_ge_atTop 0))
  have hin : ‖m.red (φ T₀) - 0‖ < r := by
    have := (hT₀ T₀ le_rfl).1
    rwa [dist_eq_norm] at this
  have hT0 : 0 ≤ T₀ := (hT₀ T₀ le_rfl).2
  have hbound : ∀ t, T₀ ≤ t → |φ t 1 - m.ustar| ≤ Cc * r * Real.exp (-a * (t - T₀)) := by
    intro t ht
    have hseg : IsTrajectoryOn (fun t => m.red (φ t)) m.redField T₀ t :=
      hρ.mono fun τ hτ => hT0.trans hτ.1
    have h := hles T₀ t _ hseg hin t ⟨ht, le_rfl⟩
    have hc := PiLp.norm_apply_le (m.red (φ t) - 0) 0
    simp only [sub_zero] at hc h hin
    have e : (m.red (φ t)) 0 = φ t 1 - m.ustar := by simp [Model.red]
    rw [e, Real.norm_eq_abs] at hc
    have hp : 0 ≤ Cc * Real.exp (-a * (t - T₀)) := by
      have := Real.exp_pos (-a * (t - T₀))
      positivity
    calc |φ t 1 - m.ustar| ≤ ‖m.red (φ t)‖ := hc
      _ ≤ Cc * Real.exp (-a * (t - T₀)) * ‖m.red (φ T₀)‖ := h
      _ ≤ Cc * Real.exp (-a * (t - T₀)) * r := mul_le_mul_of_nonneg_left hin.le hp
      _ = Cc * r * Real.exp (-a * (t - T₀)) := by ring
  obtain ⟨θ, hθ⟩ := Dynamics.exists_tendsto_of_abs_deriv_le_exp (θ := fun t => φ t 0)
    (θ' := fun t => m.η * (φ t 1 - m.ustar)) (A := |m.η| * (Cc * r)) (t₀ := T₀) ha
    (fun t ht => (hasDerivWithinAt_angle m (hφ t (hT0.trans ht))).mono
      (Ici_subset_Ici.mpr hT0))
    (fun t ht => by
      rw [abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hbound t ht) (abs_nonneg _))
  refine ⟨θ, Dynamics.tendsto_euclidean_of_coord fun i => ?_⟩
  fin_cases i
  · simpa using hθ
  · simpa using hu.add_const m.ustar
  · simpa using hd.add (((iHatD_continuous m).tendsto _).comp hθ)
  · simpa using hq.add (((iHatQ_continuous m).tendsto _).comp hθ)


/-! ### Lyapunov stability without synchronizing torque at the boundary -/

/-- **Frozen angle without modulation** (`μ = 0`, `η = 0`, `margin ≥ 0`): in deviation coordinates
the closed loop is `z' = (0, −margin z₁/C_dc, −R_s z₂/L_s, −R_s z₃/L_s)` (the angle and, at
`margin = 0`, the DC error are conserved, the current error decays), so `⟨z, z'⟩ ≤ 0` and the
operating point is Lyapunov stable (`Dynamics.lyapunovStable_of_inner_nonpos`). Implementation
evidence. -/
private theorem lyapunovStable_of_frozen (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls)
    (hR : 0 < m.Rs) (hμ : m.μ = 0) (hη : m.η = 0) (hδ : 0 ≤ m.margin) :
    LyapunovStable m.translated 0 := by
  have hω : m.ω0 = 0 := by simp [Model.ω0, hη]
  have hNR : m.N = m.Rs ^ 2 := by simp [Model.N, hω]
  have hGK : m.Gdc + m.Kp = m.margin := by simp [Model.margin, hμ]
  have hf : ∀ z : State 4, m.translated z = WithLp.toLp 2 ![0, -(m.margin * z 1) / m.Cdc,
      -(m.Rs * z 2) / m.Ls, -(m.Rs * z 3) / m.Ls] := by
    intro z
    ext i
    fin_cases i
    · simp [Model.translated, Model.field, Model.point, hη, hω]
    · simp only [Model.translated, Model.field, Model.idc, Model.ixHat, Model.κ, Model.point,
        hμ, PiLp.toLp_apply, PiLp.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Fin.isValue, Fin.mk_one, ← hGK]
      ring
    · simp only [Model.translated, Model.field, Model.point, Model.iHatD, hμ, hω,
        PiLp.toLp_apply, PiLp.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, Fin.reduceFinMk]
      ring
    · simp only [Model.translated, Model.field, Model.point, Model.iHatQ, hμ, hω, hNR,
        PiLp.toLp_apply, PiLp.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
        Fin.isValue, Fin.reduceFinMk]
      field_simp
      ring
  refine powerlib.Dynamics.lyapunovStable_of_inner_nonpos (by norm_num)
    (ContinuousLinearMap.id ℝ (State 4)) Function.injective_id fun z => ?_
  simp only [ContinuousLinearMap.id_apply, hf, PiLp.inner_apply, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, RCLike.inner_apply, conj_trivial]
  have h1 : 0 ≤ m.margin * z 1 ^ 2 / m.Cdc := by positivity
  have h2 : 0 ≤ m.Rs * z 2 ^ 2 / m.Ls := by positivity
  have h3 : 0 ≤ m.Rs * z 3 ^ 2 / m.Ls := by positivity
  have e : z 0 * 0 + z 1 * (-(m.margin * z 1) / m.Cdc) + z 2 * (-(m.Rs * z 2) / m.Ls) +
      z 3 * (-(m.Rs * z 3) / m.Ls) = -(m.margin * z 1 ^ 2 / m.Cdc) - m.Rs * z 2 ^ 2 / m.Ls -
        m.Rs * z 3 ^ 2 / m.Ls := by ring
  nlinarith [e]

/-- The reduced error `red x = (ũ, R_θᵀ ĩ)` and the errors `(ũ, ĩ)` control each other.
Implementation evidence (it names the model's reduction only; kept private with its users). -/
private theorem red_bounds (m : Model) (x : State 4) :
    |x 1 - m.ustar| ≤ ‖m.red x‖ ∧ |x 2 - m.iHatD (x 0)| ≤ 2 * ‖m.red x‖ ∧
      |x 3 - m.iHatQ (x 0)| ≤ 2 * ‖m.red x‖ ∧
      ‖m.red x‖ ≤ |x 1 - m.ustar| + 2 * (|x 2 - m.iHatD (x 0)| + |x 3 - m.iHatQ (x 0)|) := by
  have r0 : m.red x 0 = x 1 - m.ustar := by simp [Model.red]
  have r1 : m.red x 1 = Real.cos (x 0) * (x 2 - m.iHatD (x 0)) +
      Real.sin (x 0) * (x 3 - m.iHatQ (x 0)) := by simp [Model.red]
  have r2 : m.red x 2 = -Real.sin (x 0) * (x 2 - m.iHatD (x 0)) +
      Real.cos (x 0) * (x 3 - m.iHatQ (x 0)) := by simp [Model.red]
  have n0 := PiLp.norm_apply_le (m.red x) 0
  have n1 := PiLp.norm_apply_le (m.red x) 1
  have n2 := PiLp.norm_apply_le (m.red x) 2
  have hn := Dynamics.norm_le_sum_abs (m.red x)
  rw [Fin.sum_univ_three, r0, r1, r2] at hn
  rw [r0, Real.norm_eq_abs] at n0
  rw [r1, Real.norm_eq_abs] at n1
  rw [r2, Real.norm_eq_abs] at n2
  set c := Real.cos (x 0)
  set s := Real.sin (x 0)
  set e1 := x 2 - m.iHatD (x 0)
  set e2 := x 3 - m.iHatQ (x 0)
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hc := Real.abs_cos_le_one (x 0)
  have hs := Real.abs_sin_le_one (x 0)
  have i1 : e1 = c * (c * e1 + s * e2) - s * (-s * e1 + c * e2) := by
    linear_combination (-e1) * hsc
  have i2 : e2 = s * (c * e1 + s * e2) + c * (-s * e1 + c * e2) := by
    linear_combination (-e2) * hsc
  have bnd : ∀ a b p q : ℝ, |a| ≤ 1 → |b| ≤ 1 → |a * p + b * q| ≤ |p| + |q| := fun a b p q ha hb => by
    calc |a * p + b * q| ≤ |a| * |p| + |b| * |q| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * |p| + 1 * |q| := by gcongr
      _ = |p| + |q| := by ring
  refine ⟨n0, ?_, ?_, ?_⟩
  · rw [i1, sub_eq_add_neg, ← neg_mul]
    have := bnd c (-s) (c * e1 + s * e2) (-s * e1 + c * e2) hc (by rwa [abs_neg])
    linarith
  · rw [i2]
    have := bnd s c (c * e1 + s * e2) (-s * e1 + c * e2) hs hc
    linarith
  · have b1 := bnd c s e1 e2 hc hs
    have b2 := bnd (-s) c e1 e2 (by rwa [abs_neg]) hc
    linarith

/-- **Lyapunov stability without synchronizing torque, with modulation** (`μ ≠ 0`, `margin ≥ 0`):
the rotation-reduced error is locally exponentially stable and the angle moves by at most a
multiple of the initial error. Implementation evidence. -/
private theorem lyapunovStable_of_no_sync_of_mu_ne_zero (m : Model) (hC : 0 < m.Cdc)
    (hL : 0 < m.Ls) (hR : 0 < m.Rs) (hμ : m.μ ≠ 0) (hs : m.μ * m.ustar * m.v0 = 0)
    (hδ : 0 ≤ m.margin) : LyapunovStable m.field m.point := by
  have hN := N_pos m hR
  have hκ := kappa_eq_zero_of_no_sync m hs
  obtain ⟨r, Cc, a, hr, hC1, ha, hles⟩ := Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian
    m.redJac (redField_contDiff m) (redField_zero m) (hasFDerivAt_redField_zero m hL.ne').fderiv
    (redJac_isHurwitz m hC hL hR hμ hδ)
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ, Λ = (|m.Rs * (m.μ * m.ustar)| + |m.ω0 * m.Ls * (m.μ * m.ustar)|) /
      m.N := ⟨_, rfl⟩
  have hΛ : 0 ≤ Λ := by rw [hΛdef]; positivity
  obtain ⟨K₁, hK₁⟩ : ∃ K₁, K₁ = 1 + 4 * (1 + Λ) := ⟨_, rfl⟩
  have hK₁0 : 0 < K₁ := by rw [hK₁]; positivity
  obtain ⟨K, hK⟩ : ∃ K, K = (1 + 2 * Λ) * (1 + |m.η| * Cc * K₁ / a) + 5 * Cc * K₁ := ⟨_, rfl⟩
  have hCc : 0 ≤ Cc := by linarith
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨p0, p1, p2, p3⟩ := point_apply m
  intro ε hε
  refine ⟨min (r / (K₁ + 1)) (ε / (K + 1)), lt_min (by positivity) (by positivity),
    fun t₀ t₁ φ hφ h0 t ht => ?_⟩
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀, ρ₀ = ‖φ t₀ - m.point‖ := ⟨_, rfl⟩
  rw [← hρ₀] at h0
  have hρ₁ : ρ₀ < r / (K₁ + 1) := h0.trans_le (min_le_left _ _)
  have hρ₂ : ρ₀ < ε / (K + 1) := h0.trans_le (min_le_right _ _)
  have hρ0 : 0 ≤ ρ₀ := hρ₀ ▸ norm_nonneg _
  have hc : ∀ i, |(φ t₀ - m.point) i| ≤ ρ₀ := fun i => by
    rw [hρ₀]
    simpa using PiLp.norm_apply_le (φ t₀ - m.point) i
  have hθ0 : |φ t₀ 0| ≤ ρ₀ := by
    have := hc 0; rw [PiLp.sub_apply, p0, sub_zero] at this; exact this
  have hu0 : |φ t₀ 1 - m.ustar| ≤ ρ₀ := by
    have := hc 1; rw [PiLp.sub_apply, p1] at this; exact this
  have hd0 : |φ t₀ 2 - m.iHatD 0| ≤ ρ₀ := by
    have := hc 2; rw [PiLp.sub_apply, p2] at this; exact this
  have hq0 : |φ t₀ 3 - m.iHatQ 0| ≤ ρ₀ := by
    have := hc 3; rw [PiLp.sub_apply, p3] at this; exact this
  have hD := abs_iHatD_sub_le m hN (φ t₀ 0)
  have hQ := abs_iHatQ_sub_le m hN (φ t₀ 0)
  rw [← hΛdef] at hD hQ
  have hΛθ0 := mul_le_mul_of_nonneg_left hθ0 hΛ
  have he1 : |φ t₀ 2 - m.iHatD (φ t₀ 0)| ≤ (1 + Λ) * ρ₀ := by
    have := abs_sub_le (φ t₀ 2) (m.iHatD 0) (m.iHatD (φ t₀ 0))
    rw [abs_sub_comm (m.iHatD 0)] at this
    linarith
  have he2 : |φ t₀ 3 - m.iHatQ (φ t₀ 0)| ≤ (1 + Λ) * ρ₀ := by
    have := abs_sub_le (φ t₀ 3) (m.iHatQ 0) (m.iHatQ (φ t₀ 0))
    rw [abs_sub_comm (m.iHatQ 0)] at this
    linarith
  have hred0 : ‖m.red (φ t₀)‖ ≤ K₁ * ρ₀ := by
    have := (red_bounds m (φ t₀)).2.2.2
    rw [hK₁]
    linarith
  have hin : ‖m.red (φ t₀) - 0‖ < r := by
    rw [sub_zero]
    have h1 : K₁ * ρ₀ < r := by
      have := (lt_div_iff₀ (by linarith : (0 : ℝ) < K₁ + 1)).mp hρ₁
      linarith
    linarith
  have hseg : IsTrajectoryOn (fun t => m.red (φ t)) m.redField t₀ t₁ :=
    red_isIntegralCurveOn m hN.ne' hL.ne' hκ hφ
  have hdec : ∀ τ ∈ Icc t₀ t₁, ‖m.red (φ τ)‖ ≤ Cc * K₁ * ρ₀ * Real.exp (-a * (τ - t₀)) := by
    intro τ hτ
    have h := hles t₀ t₁ _ hseg hin τ hτ
    simp only [sub_zero] at h
    have hp : 0 ≤ Cc * Real.exp (-a * (τ - t₀)) := by
      have := Real.exp_pos (-a * (τ - t₀)); positivity
    calc ‖m.red (φ τ)‖ ≤ Cc * Real.exp (-a * (τ - t₀)) * ‖m.red (φ t₀)‖ := h
      _ ≤ Cc * Real.exp (-a * (τ - t₀)) * (K₁ * ρ₀) := mul_le_mul_of_nonneg_left hred0 hp
      _ = Cc * K₁ * ρ₀ * Real.exp (-a * (τ - t₀)) := by ring
  have hθ : |φ t 0 - φ t₀ 0| ≤ |m.η| * (Cc * K₁ * ρ₀) / a :=
    Dynamics.abs_sub_le_of_abs_deriv_le_exp (θ := fun τ => φ τ 0)
      (θ' := fun τ => m.η * (φ τ 1 - m.ustar)) ha
      (fun τ hτ => hasDerivWithinAt_angle m (hφ τ hτ))
      (fun τ hτ => by
        rw [abs_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (((red_bounds m (φ τ)).1).trans (hdec τ hτ))
          (abs_nonneg _)) t ht
  have hx : Real.exp (-a * (t - t₀)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := mul_nonneg ha.le (sub_nonneg.mpr ht.1)
    linarith
  have hRt : ‖m.red (φ t)‖ ≤ Cc * K₁ * ρ₀ := by
    have := hdec t ht
    have hp : 0 ≤ Cc * K₁ * ρ₀ := by positivity
    have := mul_le_mul_of_nonneg_left hx hp
    linarith
  obtain ⟨b0, b1, b2, -⟩ := red_bounds m (φ t)
  have hθt : |φ t 0| ≤ ρ₀ * (1 + |m.η| * Cc * K₁ / a) := by
    have h1 := abs_sub_abs_le_abs_sub (φ t 0) (φ t₀ 0)
    have h2 : |m.η| * (Cc * K₁ * ρ₀) / a = ρ₀ * (|m.η| * Cc * K₁ / a) := by ring
    rw [h2] at hθ
    linarith
  have hDt := abs_iHatD_sub_le m hN (φ t 0)
  have hQt := abs_iHatQ_sub_le m hN (φ t 0)
  rw [← hΛdef] at hDt hQt
  have h2 : |φ t 2 - m.iHatD 0| ≤ 2 * (Cc * K₁ * ρ₀) + Λ * |φ t 0| := by
    have := abs_sub_le (φ t 2) (m.iHatD (φ t 0)) (m.iHatD 0)
    linarith
  have h3 : |φ t 3 - m.iHatQ 0| ≤ 2 * (Cc * K₁ * ρ₀) + Λ * |φ t 0| := by
    have := abs_sub_le (φ t 3) (m.iHatQ (φ t 0)) (m.iHatQ 0)
    linarith
  have hn := Dynamics.norm_le_sum_abs (φ t - m.point)
  rw [Fin.sum_univ_four, PiLp.sub_apply, PiLp.sub_apply, PiLp.sub_apply, PiLp.sub_apply, p0, p1,
    p2, p3, sub_zero] at hn
  have hΛθ := mul_le_mul_of_nonneg_left hθt hΛ
  have hfin : ‖φ t - m.point‖ ≤ K * ρ₀ := by
    have e : K * ρ₀ = ρ₀ * (1 + |m.η| * Cc * K₁ / a) +
        2 * (Λ * (ρ₀ * (1 + |m.η| * Cc * K₁ / a))) + Cc * K₁ * ρ₀ + 2 * (2 * (Cc * K₁ * ρ₀)) := by
      rw [hK]; ring
    rw [e]
    linarith
  have hKε : K * ρ₀ < ε := by
    have := (lt_div_iff₀ (by linarith : (0 : ℝ) < K + 1)).mp hρ₂
    linarith
  linarith

/-- **Lyapunov stability with a frozen angle and no modulation**: with `C_dc, L_s, R_s > 0`,
`μ = 0`, `η = 0` and `margin ≥ 0` the operating point is Lyapunov stable. -/
@[powerlib_domain] theorem mem_den_lyapunovStable_of_frozen (m : Model) (hC : 0 < m.Cdc)
    (hL : 0 < m.Ls) (hR : 0 < m.Rs) (hμ : m.μ = 0) (hη : m.η = 0) (hδ : 0 ≤ m.margin) :
    connection% (m ∈ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  rw [(show family.IsAutonomous Model.translated from fun _ => rfl).mem_den_flow]
  exact lyapunovStable_of_frozen m hC hL hR hμ hη hδ

/-- **Lyapunov stability without synchronizing torque, with modulation**: with
`C_dc, L_s, R_s > 0`, `μ ≠ 0`, `μ u* v₀ = 0` and `margin ≥ 0` (in particular at `margin = 0`) the
operating point is Lyapunov stable. -/
@[powerlib_domain] theorem mem_den_lyapunovStable_of_no_sync_of_mu_ne_zero (m : Model)
    (hC : 0 < m.Cdc) (hL : 0 < m.Ls) (hR : 0 < m.Rs) (hμ : m.μ ≠ 0)
    (hs : m.μ * m.ustar * m.v0 = 0) (hδ : 0 ≤ m.margin) :
    connection% (m ∈ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  rw [mem_den_flow']
  exact lyapunovStable_of_no_sync_of_mu_ne_zero m hC hL hR hμ hs hδ

/-- **Lyapunov stability without synchronizing torque, decided** (`C_dc, L_s, R_s > 0`,
`μ u* v₀ = 0`, `margin ≥ 0`): the operating point is Lyapunov stable exactly when
`margin > 0`, or `μ ≠ 0`, or `η = 0`; the remaining case `margin = 0`, `μ = 0`, `η ≠ 0` is
unstable (`mem_den_unstable_of_mu_eq_zero`). -/
@[powerlib_domain] theorem mem_den_lyapunovStable_iff_of_no_sync (m : Model) (hC : 0 < m.Cdc)
    (hL : 0 < m.Ls) (hR : 0 < m.Rs) (hs : m.μ * m.ustar * m.v0 = 0) (hδ : 0 ≤ m.margin) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      m ∈ {m : Model | 0 < m.margin ∨ m.μ ≠ 0 ∨ m.η = 0}) := by
  unfold powerlib.TMIO.Statement
  rw [Set.mem_ofPred_eq]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2, h3⟩ := hc
    have hm : m.margin = 0 := le_antisymm h1 hδ
    have hu := mem_den_unstable_of_mu_eq_zero m hR h2 hm h3
    unfold powerlib.TMIO.Statement at hu
    rw [mem_den_flow'] at h hu
    exact hu h
  · rintro (h | h | h)
    · have := mem_den_lyapunovStable_of_no_sync m hC hL hR hs h
      unfold powerlib.TMIO.Statement at this
      exact this
    · have := mem_den_lyapunovStable_of_no_sync_of_mu_ne_zero m hC hL hR h hs hδ
      unfold powerlib.TMIO.Statement at this
      exact this
    · by_cases hμ : m.μ = 0
      · have := mem_den_lyapunovStable_of_frozen m hC hL hR hμ h hδ
        unfold powerlib.TMIO.Statement at this
        exact this
      · have := mem_den_lyapunovStable_of_no_sync_of_mu_ne_zero m hC hL hR hμ hs hδ
        unfold powerlib.TMIO.Statement at this
        exact this

end powerlib.DCLink.MatchingStiffGrid
