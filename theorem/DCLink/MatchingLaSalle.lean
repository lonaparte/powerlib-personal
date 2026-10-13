import theorem.DCLink.MatchingStiffGrid
import theorem.Dynamics.PeriodicLaSalle

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
`theorem.Dynamics.PeriodicLaSalle`). The field is `2π`-periodic in `θ_dq`, so sublevel sets of `H`
are unbounded in `ℝ⁴`. The cylinder map `cyl x = (cos θ, sin θ, u, i_d, i_q)` carries the closed
loop to the polynomial field `cylField` on `ℝ⁵` (`fderiv_cyl_field`: a semiconjugacy), for which
`c² + s²` is a first integral (`fderiv_circle_cylField`) and the energy `cylEnergy` (with
`energy = cylEnergy ∘ cyl`, `energy_eq_cylEnergy`) has compact sublevel sets on the cylinder
`c² + s² = 1` (`isCompact_cylSublevel`) and Lie derivative `≤ −margin ũ²` there (`cylLie_le`, from
the appendix balance `energy_lie_le` through `cylLie_cyl`). LaSalle on the invariant cylinder
(`Dynamics.lasalle_levelSet`, the `C¹` LaSalle of `theorem.Dynamics.Basin`, no global Lipschitz
bound) with the LaSalle set `dH/dt = 0 ⇒ ũ = 0, ĩ = 0` (`cylLie_eq_zero`) and the DC row
`ũ' = −κ sin θ / C_dc` there (`cylField_two_of_mem`, `κ = η k ≠ 0`) gives convergence of the
cylinder image to `{sin θ = 0, ũ = 0, ĩ = 0}`; `Dynamics.exists_int_tendsto_of_tendsto_sin` (no
drift between the zeros of `sin`) lifts it back to `ℝ⁴`.

At the boundary `margin = 0` the dissipation `dH/dt = −margin ũ² − ‖2R_sN ĩ + μω₀L_s ũ z(θ)‖²/(4R_sN²)`
(`cylLie_eq_zero_of_margin_eq_zero`) vanishes on the three-dimensional set
`ĩ = −c ũ z(θ)`, `c = μω₀L_s/(2R_sN)`; there the energy is the pendulum energy
`a ũ²/2 + k(1 − cos θ)`, `a = C_dc + L_s c²N` (`cylEnergy_of_rel`), and the DC row is a negatively
damped pendulum `C_dc ũ' = g ũ − κ sin θ`, `g = (μω₀L_s)²/(4R_sN)` (`cylField_two_of_rel`). A
solution segment staying in that set has `ũ ≡ 0` (where `ũ ≠ 0`, constant energy forces
`a g ũ = (a − C_dc) κ sin θ`, its derivative then fixes `cos θ`, contradicting `θ' = η ũ ≠ 0`) and
therefore starts at `{sin θ = 0, ũ = 0, ĩ = 0}` (`margin_zero_segment`, through
`Dynamics.lasalle_condition_of_trajectories_mem`).

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
    `Dynamics.exists_angle_lift`);
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

Not covered: `μ u* v₀ = 0` (no synchronizing torque, `S` constant; outside the source's
hypotheses), where the LaSalle set argument still gives `ũ_dc, ĩ_dq → 0` on the cylinder but the
drift of `θ_dq` along the resulting circle of equilibria is not analysed.

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
  obtain ⟨θ, hc, hs⟩ := Dynamics.exists_cos_sin hy
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
they instantiate are the public foundation results of `theorem.Dynamics.PeriodicLaSalle`. -/

/-- The image of every forward solution on the cylinder converges to the set
`{s = 0, u = u*, i = î(c, s)}`. -/
private theorem tendsto_cyl (m : Model) (hC : 0 < m.Cdc) (hL : 0 < m.Ls) (hR : 0 < m.Rs)
    (hη : m.η ≠ 0) (hs : m.μ * m.ustar * m.v0 ≠ 0) (hδ : 0 ≤ m.margin) {φ : ℝ → State 4}
    (hφ : IsIntegralCurveOn φ (fun _ x => m.field x) (Ici 0)) :
    Tendsto (fun t => cyl (φ t)) atTop (𝓝ˢ {y : State 5 | y 1 = 0 ∧ y 2 = m.ustar ∧
      y 3 = m.cD (y 0) (y 1) ∧ y 4 = m.cQ (y 0) (y 1)}) := by
  have hψ := Dynamics.isIntegralCurveOn_comp_of_fderiv (cyl_contDiff.differentiable (by norm_num))
    (fderiv_cyl_field m) hφ
  have hκ : m.κ ≠ 0 := by
    rw [← eta_mul_k]
    exact mul_ne_zero hη (k_ne_zero m hL hR hs)
  have h2 : ContDiff ℝ 1 (fun y : State 5 => y 2 - m.ustar) :=
    (proj_contDiff 2).sub contDiff_const
  refine Dynamics.lasalle_levelSet (h := fun y : State 5 => y 0 ^ 2 + y 1 ^ 2) (c₀ := 1)
    (c := m.cylEnergy (cyl (φ 0))) (cylField_contDiff m)
    (circle_contDiff.differentiable (by norm_num)) (cylEnergy_contDiff m)
    (fderiv_circle_cylField m)
    (fun y hy => (cylLie_le m hR hL.ne' hC.ne' hy).trans
      (by nlinarith [sq_nonneg (y 2 - m.ustar)]))
    (isCompact_cylSublevel m hC hL hR _) ?_ hψ (by simp) le_rfl
  rcases hδ.lt_or_eq with hδ | hδ
  · refine Dynamics.lasalle_condition_of_lieDeriv_mem (cylField_contDiff m) h2 ?_ ?_
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
  · refine Dynamics.lasalle_condition_of_trajectories_mem (cylField_contDiff m) ?_
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
    have := Dynamics.tendsto_zero_of_tendsto_nhdsSet hT (c5 1) (fun y hy => hy.1)
    simpa using this
  have hu : Tendsto (fun t => φ t 1 - m.ustar) atTop (𝓝 0) := by
    have := Dynamics.tendsto_zero_of_tendsto_nhdsSet hT ((c5 2).sub continuous_const)
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
    have := Dynamics.tendsto_zero_of_tendsto_nhdsSet hT hcD
      (fun y hy => sub_eq_zero.mpr hy.2.2.1)
    simpa [cD_cos_sin] using this
  have hq : Tendsto (fun t => φ t 3 - m.iHatQ (φ t 0)) atTop (𝓝 0) := by
    have := Dynamics.tendsto_zero_of_tendsto_nhdsSet hT hcQ
      (fun y hy => sub_eq_zero.mpr hy.2.2.2)
    simpa [cQ_cos_sin] using this
  have hθc : ContinuousOn (fun t => φ t 0) (Ici 0) :=
    ((proj_contDiff (n := 4) 0).continuous.comp_continuousOn hφ.continuousOn)
  obtain ⟨j, hj⟩ := Dynamics.exists_int_tendsto_of_tendsto_sin hθc hsin
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
    Dynamics.isPositivelyInvariant_levelSet_sublevel (h := fun y : State 5 => y 0 ^ 2 + y 1 ^ 2)
      (circle_contDiff.differentiable (by norm_num))
      ((cylEnergy_contDiff m).differentiable (by norm_num)) (fderiv_circle_cylField m)
      (fun y hy => (cylLie_le m hR hL.ne' hC.ne' hy).trans
        (by nlinarith [sq_nonneg (y 2 - m.ustar)]))
  obtain ⟨ψ, hψ0, hψ, -⟩ := Dynamics.exists_isIntegralCurveOn_of_isCompact (cylField_contDiff m)
    (isCompact_cylSublevel m hC hL hR c) hinv (y₀ := cyl x₀) ⟨by simp, le_rfl⟩
  have hco : ∀ t, 0 ≤ t → ∀ i,
      HasDerivWithinAt (fun τ => ψ τ i) (m.cylField (ψ t) i) (Ici 0) t :=
    fun t ht i => Dynamics.HasDerivWithinAt.euclidean_coord (hψ t ht) i
  have hw : ContinuousOn (fun t => m.η * ψ t 2 - m.ω0) (Ici 0) :=
    (continuousOn_const.mul ((proj_contDiff (n := 5) 2).continuous.comp_continuousOn
      hψ.continuousOn)).sub continuousOn_const
  obtain ⟨θ, hθ0, hθd, hθcs⟩ := Dynamics.exists_angle_lift (c := fun t => ψ t 0)
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
  exact Dynamics.RegionOfAttraction.tendsto (basin m hC hL hR hη hs hδ) hφ hmem

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

end powerlib.DCLink.MatchingStiffGrid
