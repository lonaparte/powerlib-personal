import theorem.GridTiedConverter.GFM.Matching.StiffGrid
import theorem.Dynamics.LaSalle.Periodic

/-! # Matching control on a stiff grid in the stationary frame: the operating orbit

The stiff-grid matching closed loop of `theorem.GridTiedConverter.GFM.Matching.StiffGrid` written
in the stationary `αβ` frame, the frame in which the source states the converter model. With the
grid angle adjoined as a state the loop is autonomous but has no equilibrium; its operating state
is a periodic orbit. This module states what the library can state about it: the exact
correspondence with the grid frame, the absence of equilibria, and (private, trajectory level)
the existence of the orbit and its transversal exponential stability.

Model boundary.
* Exactly the converter, filter, grid and control (18) of
  `theorem.GridTiedConverter.GFM.Matching.StiffGrid` (parameters `MatchingStiffGrid.Model`), in the
  stationary frame: state `(θ_g, θ, u_dc, i_α, i_β) ∈ ℝ⁵` (`stationaryField`): `θ_g' = ω₀`,
  `θ' = η u_dc`, `C_dc u_dc' = −G_dc u_dc + i_dc + μ (−sin θ, cos θ)ᵀ i_αβ` with
  `i_dc = −K_p ũ_dc + G_dc u*_dc + î_x(θ − θ_g) − κ sin(θ − θ_g)` (the control reads the
  measured angle difference), `L_s i_αβ' = −R_s i_αβ + v₀ (−sin θ_g, cos θ_g) −
  μ (−sin θ, cos θ) u_dc` (stiff grid `v_g = v₀ (−sin θ_g, cos θ_g)`, Fig. 5 of the source).
  Continuous time, autonomous. Non-autonomous stationary models (`θ_g = ω₀ t` as an input) are
  not formalized: the families read autonomous fields at points, and with `θ_g` adjoined the
  model is autonomous.
* The frame map `frame (θ_g, θ, u, i_αβ) = (θ − θ_g, u, R_{θ_g}ᵀ i_αβ)` and the orbit points
  `orbitPoint m φ = (φ, φ, u*_dc, R_φ î_dq(0))`.

Source: C. Arghir, F. Dörfler, "The electronic realization of synchronous machines: model
matching, angle tracking, and energy shaping techniques", IEEE Trans. Power Electron. 35(4)
(2020) 4398–4410, author version (ETH Research Collection, `bare_jrnl.pdf`, text layer read): the
stationary-frame model (4), (11)–(13), the stiff grid of Fig. 5 (`θ_g' = ω₀`), and the transform
to the grid frame of §III-B (`θ_dq = θ − θ_g`, `i_dq = R_{θ_g}ᵀ i_s`); Khalil, *Nonlinear
Systems*, 3rd ed., §8.4 (orbital stability), for the reading of the result.

Results.
* Static: `frame_contDiff`, `hasDerivAt_frame_line`, `fderiv_frame_field` (**the frame map is a
  semiconjugacy** from the stationary-frame loop to the grid-frame loop
  `MatchingStiffGrid.Model.field`; with `θ_g` kept, `(θ_g, frame)` conjugates it to the skew
  product `(ω₀, field)`), `stationaryField_ne_zero` (**no equilibrium** for `ω₀ ≠ 0`, so no flow
  sentence about a point of this model holds: the decision is that the stationary frame is read
  through the grid frame), `frame_orbitPoint` (the orbit lies over the grid-frame operating
  point), `norm_sub_orbitPoint` (the distance to the orbit point of the same grid phase is the
  grid-frame distance to the operating point).
* Trajectory level (private implementation evidence, Rules §3a: periodic orbits and orbital
  stability are not sentences of the library): `orbit_hasDerivAt` (**existence**: for every grid
  phase `φ₀`, `t ↦ orbitPoint m (φ₀ + ω₀ t)` is a solution, periodic of period `2π/ω₀` modulo
  `2π` in the angles), `orbit_exponentiallyStable` (**transversal exponential stability** under
  the source's strict condition: every solution starting within `r` of the orbit point of its
  grid phase stays within `C e^{−a(t − t₀)}` times the initial distance of the orbit point of its
  current grid phase; the phase is the grid angle itself).
* Not proved: orbital stability as a library sentence (no such sentence exists), and the global
  (LaSalle) picture in the stationary frame beyond its grid-frame reading in
  `theorem.GridTiedConverter.GFM.Matching.LaSalle`.
-/

noncomputable section
namespace powerlib.GFM.Matching.StationaryFrame
open powerlib.Dynamics (State)
open powerlib.GFM.Matching.MatchingStiffGrid (Model)
open Set Filter Topology

/-- The stiff-grid closed loop in the stationary frame with the grid angle adjoined, state
`(θ_g, θ, u_dc, i_α, i_β)`: `θ_g' = ω₀`, `θ' = η u_dc`, the DC row with the control (18) computed
from `θ − θ_g`, and `L_s i_αβ' = −R_s i_αβ + v₀ (−sin θ_g, cos θ_g) − μ (−sin θ, cos θ) u_dc`. -/
def stationaryField (m : Model) (y : State 5) : State 5 :=
  WithLp.toLp 2 ![
    m.ω0,
    m.η * y 2,
    (-m.Gdc * y 2 + (-m.Kp * (y 2 - m.ustar) + m.Gdc * m.ustar + m.ixHat (y 1 - y 0) -
        m.κ * Real.sin (y 1 - y 0)) + m.μ * (-Real.sin (y 1) * y 3 + Real.cos (y 1) * y 4)) /
      m.Cdc,
    (-m.Rs * y 3 + m.v0 * -Real.sin (y 0) - m.μ * (-Real.sin (y 1)) * y 2) / m.Ls,
    (-m.Rs * y 4 + m.v0 * Real.cos (y 0) - m.μ * Real.cos (y 1) * y 2) / m.Ls]

/-- The point of the operating orbit with grid phase `φ`:
`(φ, φ, u*_dc, R_φ î_dq(0))`. -/
def orbitPoint (m : Model) (φ : ℝ) : State 5 :=
  WithLp.toLp 2 ![φ, φ, m.ustar,
    Transform.iparkD φ (m.iHatD 0) (m.iHatQ 0), Transform.iparkQ φ (m.iHatD 0) (m.iHatQ 0)]

/-- The grid frame: `(θ_g, θ, u, i_αβ) ↦ (θ − θ_g, u, R_{θ_g}ᵀ i_αβ)`. -/
def frame (y : State 5) : State 4 :=
  WithLp.toLp 2 ![y 1 - y 0, y 2, Transform.parkD (y 0) (y 3) (y 4),
    Transform.parkQ (y 0) (y 3) (y 4)]


/-- Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem frame_contDiff : ContDiff ℝ 1 frame := by
  have h0 := Dynamics.contDiff_coord (k := 1) (n := 5) 0
  have h1 := Dynamics.contDiff_coord (k := 1) (n := 5) 1
  have h2 := Dynamics.contDiff_coord (k := 1) (n := 5) 2
  have h3 := Dynamics.contDiff_coord (k := 1) (n := 5) 3
  have h4 := Dynamics.contDiff_coord (k := 1) (n := 5) 4
  rw [contDiff_euclidean]
  intro i
  fin_cases i <;> simp [frame, Transform.parkD, Transform.parkQ] <;> fun_prop

/-- The derivative of the frame map along a line. Static evidence, not a connection
conclusion. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_frame_line (y v : State 5) :
    HasDerivAt (fun t : ℝ => frame (y + t • v))
      (WithLp.toLp 2 ![v 1 - v 0, v 2,
        Transform.parkQ (y 0) (y 3) (y 4) * v 0 + Real.cos (y 0) * v 3 + Real.sin (y 0) * v 4,
        -Transform.parkD (y 0) (y 3) (y 4) * v 0 - Real.sin (y 0) * v 3 +
          Real.cos (y 0) * v 4]) 0 := by
  rw [← hasDerivWithinAt_univ]
  apply Dynamics.hasDerivWithinAt_euclidean_of_coord
  intro i
  rw [hasDerivWithinAt_univ]
  have hlin : ∀ j : Fin 5, HasDerivAt (fun t : ℝ => y j + t * v j) (v j) 0 := fun j => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v j)).const_add (y j)
  have hc := (Real.hasDerivAt_cos (y 0)).comp_of_eq (0 : ℝ) (hlin 0) (by simp)
  have hs := (Real.hasDerivAt_sin (y 0)).comp_of_eq (0 : ℝ) (hlin 0) (by simp)
  fin_cases i
  · convert (hlin 1).sub (hlin 0) using 1
    · funext t; simp [frame]
    · simp
  · convert hlin 2 using 1
    · funext t; simp [frame]
    · simp
  · convert (hc.mul (hlin 3)).add (hs.mul (hlin 4)) using 1
    · funext t; simp [frame, Transform.parkD]
    · simp [Transform.parkQ]
      ring
  · convert (hs.neg.mul (hlin 3)).add (hc.mul (hlin 4)) using 1
    · funext t; simp [frame, Transform.parkQ]
    · simp [Transform.parkD]
      ring

/-- **The stationary frame is the grid frame with the grid angle adjoined**: the frame map is a
semiconjugacy from the stationary-frame loop to the grid-frame loop
`MatchingStiffGrid.Model.field`. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem fderiv_frame_field (m : Model) (hL : m.Ls ≠ 0) (y : State 5) :
    fderiv ℝ frame y (stationaryField m y) = m.field (frame y) := by
  rw [Dynamics.fderiv_apply_eq_of_hasDerivAt_line ((frame_contDiff.differentiable (by norm_num)) y)
    (hasDerivAt_frame_line y _)]
  have hsc := Real.sin_sq_add_cos_sq (y 0)
  ext i
  fin_cases i <;>
    simp [stationaryField, MatchingStiffGrid.Model.field, MatchingStiffGrid.Model.idc,
      frame, Transform.parkD, Transform.parkQ, MatchingStiffGrid.Model.ω0, Real.sin_sub,
      Real.cos_sub]
  · linear_combination (-(m.μ * (-(Real.sin (y 1) * y 3) + Real.cos (y 1) * y 4)) / m.Cdc) * hsc
  · field_simp
    ring
  · field_simp
    linear_combination m.v0 * hsc


/-- **No equilibrium in the stationary frame**: for `ω₀ ≠ 0` the stationary-frame loop has no
zero, so no point is an equilibrium and the operating state is not a point. Static evidence on
the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem stationaryField_ne_zero (m : Model) (hω : m.ω0 ≠ 0)
    (y : State 5) : stationaryField m y ≠ 0 := by
  intro h
  have := congrArg (fun z : State 5 => z 0) h
  simp [stationaryField, hω] at this

/-- The orbit points lie over the grid-frame operating point. Static evidence on the model, not
a connection conclusion. -/
@[tmio M, powerlib_domain] theorem frame_orbitPoint (m : Model) (φ : ℝ) :
    frame (orbitPoint m φ) = m.point := by
  have h := Real.sin_sq_add_cos_sq φ
  ext i
  fin_cases i <;>
    simp [frame, orbitPoint, MatchingStiffGrid.Model.point, Transform.parkD, Transform.parkQ,
      Transform.iparkD, Transform.iparkQ]
  · linear_combination (m.iHatD 0) * h
  · linear_combination (m.iHatQ 0) * h

/-- **The distance to the orbit point of the same grid phase is the grid-frame distance to the
operating point** (the rotation `R_{θ_g}` is an isometry). Static evidence on the model, not a
connection conclusion. -/
@[tmio M, powerlib_domain] theorem norm_sub_orbitPoint (m : Model) (y : State 5) :
    ‖y - orbitPoint m (y 0)‖ = ‖frame y - m.point‖ := by
  have h := Real.sin_sq_add_cos_sq (y 0)
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [Fin.sum_univ_five, Fin.sum_univ_four, Real.norm_eq_abs, sq_abs, PiLp.sub_apply]
  simp [frame, orbitPoint, MatchingStiffGrid.Model.point, Transform.parkD, Transform.parkQ,
    Transform.iparkD, Transform.iparkQ]
  linear_combination ((m.iHatD 0) ^ 2 + (m.iHatQ 0) ^ 2 - (y 3) ^ 2 - (y 4) ^ 2) * h

/-! ## The operating orbit (trajectory level, private implementation evidence) -/

/-- **Existence of the operating orbit**: for every grid phase `φ₀`, the curve
`t ↦ (φ₀ + ω₀ t, φ₀ + ω₀ t, u*, R_{φ₀ + ω₀ t} î_dq(0))` solves the stationary-frame loop (it is
periodic modulo `2π` in the angles, of period `2π/ω₀`). -/
@[tmio TM, powerlib_domain] private theorem orbit_hasDerivAt (m : Model) (hN : m.N ≠ 0)
    (hL : m.Ls ≠ 0) (φ₀ t : ℝ) :
    HasDerivAt (fun t => orbitPoint m (φ₀ + m.ω0 * t))
      (stationaryField m (orbitPoint m (φ₀ + m.ω0 * t))) t := by
  have h0 := MatchingStiffGrid.field_point m hN
  have r2 := congrArg (fun z : State 4 => z 2) h0
  have r3 := congrArg (fun z : State 4 => z 3) h0
  simp [MatchingStiffGrid.Model.field, MatchingStiffGrid.Model.point, hL] at r2 r3
  rw [← hasDerivWithinAt_univ]
  apply Dynamics.hasDerivWithinAt_euclidean_of_coord
  intro i
  rw [hasDerivWithinAt_univ]
  have hφ : HasDerivAt (fun t : ℝ => φ₀ + m.ω0 * t) m.ω0 t := by
    simpa using ((hasDerivAt_id t).const_mul m.ω0).const_add φ₀
  have hc := (Real.hasDerivAt_cos (φ₀ + m.ω0 * t)).comp t hφ
  have hs := (Real.hasDerivAt_sin (φ₀ + m.ω0 * t)).comp t hφ
  fin_cases i
  · convert hφ using 1
    · funext t; simp [orbitPoint]
    · simp [stationaryField]
  · convert hφ using 1
    · funext t; simp [orbitPoint]
    · simp [stationaryField, orbitPoint, MatchingStiffGrid.Model.ω0]
  · convert hasDerivAt_const t m.ustar using 1
    · funext t; simp [orbitPoint]
    · have hsc := Real.sin_sq_add_cos_sq (φ₀ + m.ω0 * t)
      simp [stationaryField, orbitPoint, MatchingStiffGrid.Model.ixHat, Transform.parkQ,
        Transform.iparkD, Transform.iparkQ]
      left
      linear_combination (m.μ * m.iHatQ 0) * hsc
  · convert (hc.mul_const (m.iHatD 0)).sub (hs.mul_const (m.iHatQ 0)) using 1
    · funext t; simp [orbitPoint, Transform.iparkD]
    · simp [stationaryField, orbitPoint, Transform.iparkD]
      field_simp
      linear_combination Real.cos (φ₀ + m.ω0 * t) * r2 - Real.sin (φ₀ + m.ω0 * t) * r3
  · convert (hs.mul_const (m.iHatD 0)).add (hc.mul_const (m.iHatQ 0)) using 1
    · funext t; simp [orbitPoint, Transform.iparkQ]
    · simp [stationaryField, orbitPoint, Transform.iparkQ]
      field_simp
      linear_combination Real.sin (φ₀ + m.ω0 * t) * r2 + Real.cos (φ₀ + m.ω0 * t) * r3


/-- **Transversal exponential stability of the operating orbit** under the source's strict
condition (`margin > 0`, `C_dc, L_s, R_s > 0`, `μ u* v₀ > 0`, `η ≠ 0`): every solution of the
stationary-frame loop that starts near the orbit point of its own grid phase approaches the
orbit point of its current grid phase exponentially. This is the grid-frame local exponential
stability (`MatchingStiffGrid.jac_isHurwitz`) carried through the semiconjugacy
`fderiv_frame_field` and the isometry `norm_sub_orbitPoint`. -/
@[tmio TM, powerlib_domain] private theorem orbit_exponentiallyStable (m : Model)
    (hC : 0 < m.Cdc) (hL : 0 < m.Ls) (hR : 0 < m.Rs) (hs : 0 < m.μ * m.ustar * m.v0)
    (hη : m.η ≠ 0) (hδ : 0 < m.margin) :
    ∃ r C a : ℝ, 0 < r ∧ 1 ≤ C ∧ 0 < a ∧ ∀ (t₀ t₁ : ℝ) (y : ℝ → State 5),
      IsIntegralCurveOn y (fun _ z => stationaryField m z) (Icc t₀ t₁) →
      ‖y t₀ - orbitPoint m (y t₀ 0)‖ < r → ∀ t ∈ Icc t₀ t₁,
        ‖y t - orbitPoint m (y t 0)‖ ≤
          C * Real.exp (-a * (t - t₀)) * ‖y t₀ - orbitPoint m (y t₀ 0)‖ := by
  have hN : 0 < m.N := MatchingStiffGrid.N_pos m hR.ne'
  have hLES : LocallyExponentiallyStable m.field m.point :=
    hurwitz_linearization_locally_exponentially_stable m.jac
      (MatchingStiffGrid.field_contDiff m) (MatchingStiffGrid.field_point m hN.ne')
      (MatchingStiffGrid.hasFDerivAt_field_point m hL.ne').fderiv
      (MatchingStiffGrid.jac_isHurwitz m hC hL hR hs hη hδ)
  obtain ⟨r, C, a, hr, hC1, ha, hb⟩ := hLES
  refine ⟨r, C, a, hr, hC1, ha, fun t₀ t₁ y hy h0 t ht => ?_⟩
  rw [norm_sub_orbitPoint] at h0 ⊢
  rw [norm_sub_orbitPoint]
  exact hb t₀ t₁ (fun t => frame (y t))
    (Dynamics.LaSalle.isIntegralCurveOn_comp_of_fderiv
      (frame_contDiff.differentiable (by norm_num)) (fderiv_frame_field m hL.ne') hy) h0 t ht

end powerlib.GFM.Matching.StationaryFrame
