import theorem.GFM.Matching.Matching
import theorem.Flow.Certificate
import theorem.Dynamics.LaSalle.Periodic

/-! # Matching control in closed loop: global exponential stability in the rotating frame

This module formalizes the closed loop of the grid-forming *matching control* of Arghir, Jouini
and Dörfler, together with the model reduction behind its global stability claim, and proves that
claim (strengthened from asymptotic to exponential) in the reduced coordinates.

Provenance. The equations are taken from C. Arghir, T. Jouini, F. Dörfler, "Grid-forming control
for power converters based on matching of synchronous machines", *Automatica* 95 (2018) 273–282,
arXiv:1706.09495v3 (source read): the averaged converter model (§2.2), the matching modulation
`m_αβ = μ (−sin θ, cos θ)`, `θ' = η v_dc` (§3), the `dq` model in the frame of `θ` (§3.1), the
theorem "Strict passivity in dq-frame" and its storage `V₁ = C_dc ṽ_dc²/2 + L ‖ĩ_dq‖²/2 +
C ‖ṽ_dq‖²/2`, the DC-side P-control `i_dc = i_dc,ref − K_p (v_dc − v_dc,ref)` and the load of
Assumption 1, `i_l = (G_l I + B_l J) v_αβ + s_l`, `s_l' = ω J s_l`, `ω = η v_dc` (§3.2), and the
corollary "Closed-loop stability with DC-side P-control":
`C²‖v_dq*‖²/(4(G+G_l)) + L²‖i_dq*‖²/(4R) < (G_dc+K_p)/η²` ⇒ the steady state `x*` is unique and
globally asymptotically stable "for stationary loads `s_l,dq = s*`". The work-sync notes
(`theory/T-dc-voltage-gfm.md` §1.0–§1.2, `theory/T-gfm-control.md` §1.6,
`theory/papers/@arghir2020matching.md`) contain only the matching law, the swing analogy and a
stability *condition*; none of the equations below comes from the notes.

Model boundary.
* Averaged two-level three-phase converter (no PWM, switching ripple, dead time or delay), with a
  controllable DC current source, DC capacitor `C_dc`, DC conductance `G_dc`, AC inductor `L`
  with resistance `R`, AC shunt capacitor `C` with conductance `G`; balanced three phases with the
  zero-sequence (`γ`) subsystem omitted (it is a decoupled, asymptotically stable linear system,
  Remark "Zero sequence" of the source). Continuous time. No current or modulation limits
  (`|μ| ≤ 1` is not used), no PLL, no inner current loops, no outer loops of the source's §4,
  no multi-converter network.
* Controller: matching `θ' = η v_dc` with constant modulation amplitude `μ`; DC-side P-control
  `i_dc = i_dc,ref − K_p (v_dc − v_dc,ref)`. Load: constant shunt admittance `G_l I + B_l J` in
  parallel with a current source rotating at the converter frequency `ω = η v_dc`
  (Assumption 1); in the frame of `θ` it is a constant `s_dq = (s_d, s_q)`.
* Directions as in the source: `i_dc` is injected into the DC node, `i_x = m_αβᵀ i_αβ/2` is drawn
  from it by the switches, `i_αβ` flows from the switch node through the inductor to the AC
  capacitor, `i_l` is drawn from the capacitor node by the load (AC export positive);
  `J = [[0, −1], [1, 0]]`, `R_θ` the rotation by `θ`, `z_dq = R_θᵀ z_αβ`.
* Reduced (`dq`, `θ`-free) state, in this order: `x = (v_dc, i_d, i_q, v_d, v_q) ∈ ℝ⁵`
  (`Model.field`):
  `C_dc v_dc' = −G_dc v_dc + i_dc,ref − K_p (v_dc − v_dc,ref) − (μ/2) i_q + w₀`,
  `L i_dq' = −R i_dq − η v_dc L J i_dq + (μ/2) e₂ v_dc − v_dq`,
  `C v_dq' = −(G + G_l) v_dq − B_l J v_dq − η v_dc C J v_dq − s_dq + i_dq + (w₁, w₂)`,
  where `w = (ĩ_dc, −ĩ_l,d, −ĩ_l,q)` are port perturbations of the DC current and of the load
  current (the input `u = (i_dc, −i_l,dq)` of the source's passivity theorem, relative to the
  steady state). The rotation terms are written `η v_dc J i_dq` after division by `L` (and `C`),
  which equals the source form for `L, C ≠ 0`.
* Stationary-frame state, in this order: `X = (θ, v_dc, i_α, i_β, v_α, v_β, s_α, s_β) ∈ ℝ⁸`
  (`Model.abField`), the load source being a state of its own oscillator.
* Parameter ranges for the conclusions: `C_dc, L, C, R > 0`, `G + G_l > 0`; `G_dc`, `K_p`, `η`,
  `μ`, `B_l`, set points and `s_dq` are arbitrary reals (the source assumes `G_dc, G, G_l, B_l,
  K_p, η > 0`, `μ ∈ [0, 1]`). The selected point `x* = (v*, i_d*, i_q*, v_d*, v_q*)` is part of the
  model; its being an equilibrium is a static requirement.

Reduction (static and generic results; Rules §5).
* `hasDerivWithinAt_rot` (generic): the rotating-frame chain rule
  `(R_θᵀ z)' = R_θᵀ z' − θ' J R_θᵀ z`, for arbitrary differentiable `θ`, `z`.
* `field_reduce` (static): the reduced field at `reduce X = (v_dc, R_θᵀ i_αβ, R_θᵀ v_αβ)`, with
  load `s_dq = R_θᵀ s_αβ`, equals the stationary field `F = abField X` transformed by that chain
  rule; and `R_θᵀ s_αβ` has zero rotating-frame derivative. Together they give the private
  trajectory statement `reduce_isTrajectoryOn` (implementation evidence: every stationary-frame
  solution segment is mapped by `reduce` to a solution segment of the reduced model with the
  constant load `s_dq` it starts with).

Family and connection conclusions.
* `family : Family Model Requirement 5 3`: a model is read as the port system of its reduced field
  translated to the selected point (input `w`, conjugate output `(ṽ_dc, ṽ_d, ṽ_q)`, supply
  `w ⬝ y = ĩ_dc ṽ_dc − ĩ_l,dqᵀ ṽ_dq`). Requirements: `physical` (`C_dc, L, C, R, G + G_l > 0`),
  `equilibrium` (the selected point is an equilibrium at zero perturbation), `damping`
  (`0 < margin`, `margin = G_dc + K_p − η²(L²‖i*‖²/(4R) + C²‖v*‖²/(4(G+G_l)))`), `slowRate r`
  (`r ≤ 0`). Translation: every attractive sentence, Lyapunov stability, sampled contraction and
  passivity into `{physical, equilibrium, damping}`; a decay rate `r` into those and `r ≤ 0`;
  instability and conservation into the whole (inconsistent, `realize_univ`) language.
  `chain_le_semantics` proves every translation sound. No exactness is claimed.
* `mem_den_globallyExponentiallyStable`, `mem_den_globallyAsymptoticallyStable` (the source's
  corollary, strengthened to exponential), `mem_den_attractive`, `mem_den_passive` (the
  passivity theorem of the source relative to the steady state, with the P-control and the load
  admittance absorbed): under the static requirements, for every reduced model. Proof: the
  storage `V₁` has Lie derivative `−W(x̃) + w ⬝ y` (`energy_lie`), where the dissipation
  `W = margin ṽ_dc² + R‖·‖² + (G+G_l)‖·‖²` is a sum of squares (`dissipation_eq`), positive
  definite when `margin > 0`; a quadratic-decay certificate (`Flow.QuadraticDecay`) then gives
  global exponential stability, and `Port.System.passiveWith_of_rate` passivity.
* `example1_mem_den`: a concrete model with nonzero currents meets all requirements
  (nonvacuity).
* Boundary in the stationary frame, `fullFamily : Family FullModel Spectral.Requirement 8 0`
  (the stationary closed loop about a selected point; no requirement language, every flow
  translation is unavailable coverage): `full_not_mem_den_globallyAsymptoticallyStable` and
  `full_not_mem_den_globallyExponentiallyStable` (the field is `2π`-periodic in `θ`, so no point
  is globally attractive on `ℝ⁸`, whatever the gains), and `full_mem_den_unstable` (a point with
  frequency `η v* ≠ 0` is not an equilibrium, hence not Lyapunov stable — the steady state is a
  rotating orbit). The global result as a sentence therefore lives only on the reduced space;
  set attraction of the steady-state orbit in `ℝ⁸` is not a sentence of the library and is proved
  below as implementation evidence.
* Stationary-frame orbit attraction (Rules §3a: set attraction is outside the sentence language,
  so these are private implementation evidence; the generic transfer is the public foundation
  `Dynamics.LaSalle.infDist_le_of_reduction'` of `theorem.Dynamics.LaSalle.Periodic`). The steady-state
  orbit is `O = range orbitPoint`, `orbitPoint θ = (θ, v*, R_θ i*_dq, R_θ v*_dq, R_θ s_dq)`;
  static: `reduce_orbitPoint` (`O` reduces to `x*`), `orbitPoint_load`, `rotD_rot`, `rotQ_rot`,
  `rot_dist_sq`, `rot_sub_rot_sq`, `norm_sub_orbitPoint` (with the model's load phasor,
  `‖X − orbitPoint (X θ)‖ = ‖reduce X − x*‖`), `norm_orbitPoint_sub_le` (`O` is Lipschitz in `θ`).
  Private: `norm_reduce_sub_le` (`‖reduce X − x*‖ ≤ (1 + Λ) dist(X, O)`), `load_const` (the load
  phasor `R_θᵀ s_αβ` is constant along stationary solutions), `orbit_exponentiallyAttractive`
  (**PROVED**: under `physical`, `equilibrium`, `damping` there are `K ≥ 0`, `a > 0` with
  `dist(X t, O) ≤ K e^{−a (t − t₀)} dist(X t₀, O)` for every stationary-frame solution segment
  whose load phasor is the model's `s_dq` — the source's stationary loads), `tendsto_infDist_orbit`
  (forward solutions converge to `O`) and `orbit_invariant` (`O` is invariant).
* Static evidence: `margin_pos_iff` (for `η ≠ 0` the damping requirement is exactly the source's
  inequality), `eq_point_of_field_eq_zero` (uniqueness of the steady state, as in the source),
  `abField_eq_zero` (every stationary-frame equilibrium has `η v_dc = 0`),
  `abField_add_two_pi`, `dissipation_eq`, `energy_lie`.

Corrections (to the work-sync notes).
* T-dc-voltage-gfm §1.2 (headed "Arghir-Jouini-Dörfler 2018 Automatica") and T-gfm-control §1.6
  quote the "global stability condition" `(G_dc + K_p)/η² > L_s²μ²v*²/(4R_s‖Z_s‖²)` as
  [[@arghir2020matching]] Theorem 3. The closed-loop condition of the 2018 Automatica paper is
  different: `C²‖v_dq*‖²/(4(G+G_l)) + L²‖i_dq*‖²/(4R) < (G_dc+K_p)/η²`, depending on the
  steady-state currents and voltages (formalized here). The quoted `L_s, R_s, Z_s` condition is
  the one of the appendix of the TPEL paper (Arghir–Dörfler 2020; author version "Direct angle
  control and energy-shaping techniques for grid-connected converters", ETH Research
  Collection), for a different closed loop (stiff grid behind `R_s + jω₀L_s`, steady-state
  feedforward and synchronizing torque `−η∇S`); its conclusion there is LaSalle convergence to the
  set `{ũ_dc = 0, ∇S = 0, ĩ_dq = 0}`, which contains the saddle points `θ_dq = π`, not global
  stability of the operating point (see `theorem.GFM.Matching.StiffGrid`).
* "Global" stability of matching control holds only in the `θ`-free reduced coordinates
  (`full_not_mem_den_globallyAsymptoticallyStable`, `full_mem_den_unstable`; for the
  two-state abstraction also `matching_not_mem_den_globallyAsymptoticallyStable` in
  `theorem.GFM.Matching.Matching`).

Source: work-sync `theory/T-dc-voltage-gfm.md` §1.0–§1.2; `theory/T-gfm-control.md` §1.6;
`theory/papers/@arghir2020matching.md`; equations from arXiv:1706.09495v3 as listed above.
-/

noncomputable section
namespace powerlib.GFM.Matching.MatchingClosedLoop
open powerlib.Dynamics (State)

/-- Parameters of the reduced matching closed loop and a selected point
`x* = (v*, i_d*, i_q*, v_d*, v_q*)`: DC capacitance, DC conductance, DC P-gain, DC current and
voltage set points, matching gain `η`, modulation amplitude `μ`, AC inductance and resistance, AC
capacitance and conductance, load conductance and susceptance, and the load source `s_dq`. -/
structure Model where
  Cdc : ℝ
  Gdc : ℝ
  Kp : ℝ
  idcRef : ℝ
  vdcRef : ℝ
  η : ℝ
  μ : ℝ
  L : ℝ
  R : ℝ
  C : ℝ
  G : ℝ
  Gl : ℝ
  Bl : ℝ
  sd : ℝ
  sq : ℝ
  vStar : ℝ
  idStar : ℝ
  iqStar : ℝ
  vdStar : ℝ
  vqStar : ℝ

namespace Model

variable (m : Model)

/-- The selected point `x*`. -/
def point : State 5 := WithLp.toLp 2 ![m.vStar, m.idStar, m.iqStar, m.vdStar, m.vqStar]

/-- The reduced closed-loop field in the frame of `θ`, state `(v_dc, i_d, i_q, v_d, v_q)`, under the
port perturbation `w = (ĩ_dc, −ĩ_l,d, −ĩ_l,q)`. -/
def field (x : State 5) (w : Fin 3 → ℝ) : State 5 :=
  WithLp.toLp 2 ![
    (-m.Gdc * x 0 + m.idcRef - m.Kp * (x 0 - m.vdcRef) - m.μ / 2 * x 2 + w 0) / m.Cdc,
    (-m.R * x 1 - x 3) / m.L + m.η * x 0 * x 2,
    (-m.R * x 2 + m.μ / 2 * x 0 - x 4) / m.L - m.η * x 0 * x 1,
    (-(m.G + m.Gl) * x 3 + m.Bl * x 4 - m.sd + x 1 + w 1) / m.C + m.η * x 0 * x 4,
    (-(m.G + m.Gl) * x 4 - m.Bl * x 3 - m.sq + x 2 + w 2) / m.C - m.η * x 0 * x 3]

/-- The port system of the model: the reduced field translated to the selected point, input `w`,
conjugate output `(ṽ_dc, ṽ_d, ṽ_q)`. -/
def system : Port.System 5 3 :=
  ⟨fun z w => m.field (z + m.point) w, fun z _ => ![z 0, z 3, z 4]⟩

/-- The storage `V₁ = (C_dc ṽ_dc² + L ‖ĩ_dq‖² + C ‖ṽ_dq‖²)/2` of the source, in deviation
coordinates. -/
def energy (z : State 5) : ℝ :=
  (m.Cdc * z 0 ^ 2 + m.L * z 1 ^ 2 + m.L * z 2 ^ 2 + m.C * z 3 ^ 2 + m.C * z 4 ^ 2) / 2

/-- The dissipation `W`: minus the Lie derivative of the storage at zero perturbation. -/
def dissipation (z : State 5) : ℝ :=
  (m.Gdc + m.Kp) * z 0 ^ 2 + m.R * (z 1 ^ 2 + z 2 ^ 2) + (m.G + m.Gl) * (z 3 ^ 2 + z 4 ^ 2)
    - m.η * m.L * z 0 * (z 1 * m.iqStar - z 2 * m.idStar)
    - m.η * m.C * z 0 * (z 3 * m.vqStar - z 4 * m.vdStar)

end Model

private theorem coord_smooth' {n : ℕ} (j : Fin n) : ContDiff ℝ 1 (fun x : State n => x j) :=
  (PiLp.proj 2 (fun _ : Fin n => ℝ) j : State n →L[ℝ] ℝ).contDiff

private theorem coord_smooth (j : Fin 5) : ContDiff ℝ 1 (fun x : State 5 => x j) :=
  coord_smooth' j

/-- Components of the reduced field. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field_apply (m : Model) (x : State 5) (w : Fin 3 → ℝ) :
    m.field x w 0 = (-m.Gdc * x 0 + m.idcRef - m.Kp * (x 0 - m.vdcRef) - m.μ / 2 * x 2 + w 0) / m.Cdc ∧
    m.field x w 1 = (-m.R * x 1 - x 3) / m.L + m.η * x 0 * x 2 ∧
    m.field x w 2 = (-m.R * x 2 + m.μ / 2 * x 0 - x 4) / m.L - m.η * x 0 * x 1 ∧
    m.field x w 3 = (-(m.G + m.Gl) * x 3 + m.Bl * x 4 - m.sd + x 1 + w 1) / m.C + m.η * x 0 * x 4 ∧
    m.field x w 4 = (-(m.G + m.Gl) * x 4 - m.Bl * x 3 - m.sq + x 2 + w 2) / m.C - m.η * x 0 * x 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Model.field]

/-- Components of the selected point. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem point_apply (m : Model) :
    m.point 0 = m.vStar ∧ m.point 1 = m.idStar ∧ m.point 2 = m.iqStar ∧ m.point 3 = m.vdStar ∧
      m.point 4 = m.vqStar := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Model.point]

/-- The reduced field is `C¹`. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field_smooth (m : Model) (w : Fin 3 → ℝ) : ContDiff ℝ 1 (fun x => m.field x w) := by
  have h0 := coord_smooth 0
  have h1 := coord_smooth 1
  have h2 := coord_smooth 2
  have h3 := coord_smooth 3
  have h4 := coord_smooth 4
  have hs : ContDiff ℝ 1 (fun x : State 5 => ![
    (-m.Gdc * x 0 + m.idcRef - m.Kp * (x 0 - m.vdcRef) - m.μ / 2 * x 2 + w 0) / m.Cdc,
    (-m.R * x 1 - x 3) / m.L + m.η * x 0 * x 2,
    (-m.R * x 2 + m.μ / 2 * x 0 - x 4) / m.L - m.η * x 0 * x 1,
    (-(m.G + m.Gl) * x 3 + m.Bl * x 4 - m.sd + x 1 + w 1) / m.C + m.η * x 0 * x 4,
    (-(m.G + m.Gl) * x 4 - m.Bl * x 3 - m.sq + x 2 + w 2) / m.C - m.η * x 0 * x 3]) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j <;> simp <;> fun_prop
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 5 => ℝ)).symm.contDiff.comp hs

/-- The derivative of the storage. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem energy_hasFDerivAt (m : Model) (z : State 5) :
    ∃ D : State 5 →L[ℝ] ℝ, HasFDerivAt m.energy D z ∧ ∀ v : State 5,
      D v = m.Cdc * z 0 * v 0 + m.L * z 1 * v 1 + m.L * z 2 * v 2 + m.C * z 3 * v 3 +
        m.C * z 4 * v 4 := by
  let p : Fin 5 → State 5 →L[ℝ] ℝ := fun j => PiLp.proj 2 (fun _ : Fin 5 => ℝ) j
  have hp : ∀ j, HasFDerivAt (fun x : State 5 => x j) (p j) z := fun j => (p j).hasFDerivAt
  have h := ((((((hp 0).pow 2).const_mul m.Cdc).add (((hp 1).pow 2).const_mul m.L)).add
    (((hp 2).pow 2).const_mul m.L) |>.add (((hp 3).pow 2).const_mul m.C) |>.add
    (((hp 4).pow 2).const_mul m.C)).const_mul (1 / 2 : ℝ))
  have he : m.energy = fun y : State 5 => (1 / 2 : ℝ) * (m.Cdc * y 0 ^ 2 + m.L * y 1 ^ 2 +
      m.L * y 2 ^ 2 + m.C * y 3 ^ 2 + m.C * y 4 ^ 2) := by
    funext y
    simp only [Model.energy]
    ring
  refine ⟨_, he ▸ h, fun v => ?_⟩
  simp [p]
  ring

/-- The reduced field multiplied by the storage weights. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field_scaled (m : Model) (hCdc : m.Cdc ≠ 0) (hL : m.L ≠ 0) (hC : m.C ≠ 0)
    (x : State 5) (w : Fin 3 → ℝ) :
    m.Cdc * m.field x w 0 = -m.Gdc * x 0 + m.idcRef - m.Kp * (x 0 - m.vdcRef) - m.μ / 2 * x 2 + w 0 ∧
    m.L * m.field x w 1 = -m.R * x 1 - x 3 + m.L * (m.η * x 0 * x 2) ∧
    m.L * m.field x w 2 = -m.R * x 2 + m.μ / 2 * x 0 - x 4 - m.L * (m.η * x 0 * x 1) ∧
    m.C * m.field x w 3 = -(m.G + m.Gl) * x 3 + m.Bl * x 4 - m.sd + x 1 + w 1 + m.C * (m.η * x 0 * x 4) ∧
    m.C * m.field x w 4 = -(m.G + m.Gl) * x 4 - m.Bl * x 3 - m.sq + x 2 + w 2 - m.C * (m.η * x 0 * x 3) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := field_apply m x w
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h0]; field_simp
  · rw [h1]; field_simp
  · rw [h2]; field_simp
  · rw [h3]; field_simp
  · rw [h4]; field_simp

/-- Energy balance: along the port system the storage changes at the rate `−W + w ⬝ y`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem energy_lie (m : Model) (hCdc : m.Cdc ≠ 0) (hL : m.L ≠ 0) (hC : m.C ≠ 0)
    (he : m.field m.point 0 = 0) (z : State 5) (u : Fin 3 → ℝ) :
    fderiv ℝ m.energy z (m.system.field z u) =
      -m.dissipation z + (u 0 * z 0 + u 1 * z 3 + u 2 * z 4) := by
  obtain ⟨D, hD, hDv⟩ := energy_hasFDerivAt m z
  rw [hD.fderiv, hDv]
  change m.Cdc * z 0 * m.field (z + m.point) u 0 + m.L * z 1 * m.field (z + m.point) u 1 +
    m.L * z 2 * m.field (z + m.point) u 2 + m.C * z 3 * m.field (z + m.point) u 3 +
    m.C * z 4 * m.field (z + m.point) u 4 = _
  obtain ⟨f0, f1, f2, f3, f4⟩ := field_scaled m hCdc hL hC (z + m.point) u
  obtain ⟨n0, n1, n2, n3, n4⟩ := field_scaled m hCdc hL hC m.point 0
  obtain ⟨p0, p1, p2, p3, p4⟩ := point_apply m
  simp only [he, PiLp.zero_apply, mul_zero, Pi.zero_apply, PiLp.add_apply, p0, p1, p2, p3, p4]
    at f0 f1 f2 f3 f4 n0 n1 n2 n3 n4
  simp only [Model.dissipation]
  linear_combination z 0 * f0 + z 1 * f1 + z 2 * f2 + z 3 * f3 + z 4 * f4
    - z 0 * n0 - z 1 * n1 - z 2 * n2 - z 3 * n3 - z 4 * n4

/-- Damping margin `δ = G_dc + K_p − η²L²‖i*‖²/(4R) − η²C²‖v*‖²/(4(G+G_l))`. -/
def Model.margin (m : Model) : ℝ :=
  m.Gdc + m.Kp - m.η ^ 2 * (m.L ^ 2 * (m.idStar ^ 2 + m.iqStar ^ 2) / (4 * m.R) +
    m.C ^ 2 * (m.vdStar ^ 2 + m.vqStar ^ 2) / (4 * (m.G + m.Gl)))

/-- Completing the squares: `W = margin ṽ_dc² + R ‖ĩ_dq − …‖² + (G+G_l) ‖ṽ_dq − …‖²`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem dissipation_eq (m : Model) (hR : m.R ≠ 0) (hG : m.G + m.Gl ≠ 0) (z : State 5) :
    m.dissipation z = m.margin * z 0 ^ 2 +
      m.R * ((z 1 - m.η * m.L / (2 * m.R) * z 0 * m.iqStar) ^ 2 +
        (z 2 + m.η * m.L / (2 * m.R) * z 0 * m.idStar) ^ 2) +
      (m.G + m.Gl) * ((z 3 - m.η * m.C / (2 * (m.G + m.Gl)) * z 0 * m.vqStar) ^ 2 +
        (z 4 + m.η * m.C / (2 * (m.G + m.Gl)) * z 0 * m.vdStar) ^ 2) := by
  simp only [Model.dissipation, Model.margin]
  field_simp
  ring

/-- With a positive margin the dissipation is nonnegative. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem dissipation_nonneg (m : Model) (hR : 0 < m.R) (hG : 0 < m.G + m.Gl)
    (hδ : 0 < m.margin) (z : State 5) : 0 ≤ m.dissipation z := by
  rw [dissipation_eq m hR.ne' hG.ne']
  positivity

/-- With a positive margin the dissipation is positive definite. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem dissipation_pos (m : Model) (hR : 0 < m.R) (hG : 0 < m.G + m.Gl)
    (hδ : 0 < m.margin) (z : State 5) (hz : z ≠ 0) : 0 < m.dissipation z := by
  rw [dissipation_eq m hR.ne' hG.ne']
  by_contra hle
  push Not at hle
  set a := m.η * m.L / (2 * m.R)
  set b := m.η * m.C / (2 * (m.G + m.Gl))
  have h1 : 0 ≤ m.margin * z 0 ^ 2 := by positivity
  have h2 : 0 ≤ m.R * ((z 1 - a * z 0 * m.iqStar) ^ 2 + (z 2 + a * z 0 * m.idStar) ^ 2) := by
    positivity
  have h3 : 0 ≤ (m.G + m.Gl) * ((z 3 - b * z 0 * m.vqStar) ^ 2 + (z 4 + b * z 0 * m.vdStar) ^ 2) := by
    positivity
  have e1 : m.margin * z 0 ^ 2 = 0 := by linarith
  have e2 : m.R * ((z 1 - a * z 0 * m.iqStar) ^ 2 + (z 2 + a * z 0 * m.idStar) ^ 2) = 0 := by
    linarith
  have e3 : (m.G + m.Gl) * ((z 3 - b * z 0 * m.vqStar) ^ 2 + (z 4 + b * z 0 * m.vdStar) ^ 2) = 0 := by
    linarith
  have z0 : z 0 = 0 := by
    rcases mul_eq_zero.mp e1 with h | h
    · exact absurd h hδ.ne'
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  rw [z0] at e2 e3
  simp only [mul_zero, zero_mul, sub_zero, add_zero] at e2 e3
  have e2' := (mul_eq_zero.mp e2).resolve_left hR.ne'
  have e3' := (mul_eq_zero.mp e3).resolve_left hG.ne'
  have z1 : z 1 = 0 := by nlinarith [sq_nonneg (z 1), sq_nonneg (z 2)]
  have z2 : z 2 = 0 := by nlinarith [sq_nonneg (z 1), sq_nonneg (z 2)]
  have z3 : z 3 = 0 := by nlinarith [sq_nonneg (z 3), sq_nonneg (z 4)]
  have z4 : z 4 = 0 := by nlinarith [sq_nonneg (z 3), sq_nonneg (z 4)]
  apply hz
  ext i
  fin_cases i <;> simp [z0, z1, z2, z3, z4]

private theorem dissipation_continuous (m : Model) : Continuous m.dissipation := by
  have h := fun j => (coord_smooth j).continuous
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  unfold Model.dissipation
  fun_prop

private theorem energy_smooth (m : Model) : ContDiff ℝ 1 m.energy := by
  have h0 := coord_smooth 0
  have h1 := coord_smooth 1
  have h2 := coord_smooth 2
  have h3 := coord_smooth 3
  have h4 := coord_smooth 4
  unfold Model.energy
  fun_prop

private theorem eq_zero_of_mul_sq {c x : ℝ} (hc : 0 < c) (h : c * x ^ 2 = 0) : x = 0 :=
  pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp h).resolve_left hc.ne')

/-- The storage is positive definite. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem energy_pos (m : Model) (hCdc : 0 < m.Cdc) (hL : 0 < m.L) (hC : 0 < m.C) (z : State 5)
    (hz : z ≠ 0) : 0 < m.energy z := by
  unfold Model.energy
  by_contra hle
  push Not at hle
  have a0 := mul_nonneg hCdc.le (sq_nonneg (z 0))
  have a1 := mul_nonneg hL.le (sq_nonneg (z 1))
  have a2 := mul_nonneg hL.le (sq_nonneg (z 2))
  have a3 := mul_nonneg hC.le (sq_nonneg (z 3))
  have a4 := mul_nonneg hC.le (sq_nonneg (z 4))
  have z0 : z 0 = 0 := eq_zero_of_mul_sq hCdc (by linarith)
  have z1 : z 1 = 0 := eq_zero_of_mul_sq hL (by linarith)
  have z2 : z 2 = 0 := eq_zero_of_mul_sq hL (by linarith)
  have z3 : z 3 = 0 := eq_zero_of_mul_sq hC (by linarith)
  have z4 : z 4 = 0 := eq_zero_of_mul_sq hC (by linarith)
  apply hz
  ext i
  fin_cases i <;> simp [z0, z1, z2, z3, z4]

private theorem energy_nonneg (m : Model) (hCdc : 0 < m.Cdc) (hL : 0 < m.L) (hC : 0 < m.C)
    (z : State 5) : 0 ≤ m.energy z := by
  unfold Model.energy
  have := sq_nonneg (z 0)
  positivity

private theorem energy_homogeneous (m : Model) (a : ℝ) (z : State 5) :
    m.energy (a • z) = a ^ 2 * m.energy z := by
  simp only [Model.energy, PiLp.smul_apply, smul_eq_mul]
  ring

private theorem dissipation_homogeneous (m : Model) (a : ℝ) (z : State 5) :
    m.dissipation (a • z) = a ^ 2 * m.dissipation z := by
  simp only [Model.dissipation, PiLp.smul_apply, smul_eq_mul]
  ring

private theorem zeroInput_smooth (m : Model) : ContDiff ℝ 1 m.system.zeroInput :=
  (field_smooth m 0).comp (contDiff_id.add contDiff_const)

private theorem ges (m : Model) (hCdc : 0 < m.Cdc) (hL : 0 < m.L) (hC : 0 < m.C)
    (hR : 0 < m.R) (hG : 0 < m.G + m.Gl) (he : m.field m.point 0 = 0) (hδ : 0 < m.margin) :
    Flow.GloballyExponentiallyStable m.system.zeroInput 0 := by
  obtain ⟨aW, haW, bW, -, hW⟩ := Flow.quadratic_bounds m.dissipation (dissipation_continuous m)
    (dissipation_homogeneous m) (fun z hz => dissipation_pos m hR hG hδ z hz)
  obtain ⟨aV, haV, bV, hbV, hV⟩ := Flow.quadratic_bounds m.energy (energy_smooth m).continuous
    (energy_homogeneous m) (fun z hz => energy_pos m hCdc hL hC z hz)
  have hbVpos : 0 < bV := lt_of_lt_of_le haV hbV
  let c : Flow.QuadraticDecay m.system.zeroInput m.energy 0 :=
    { lower := aV
      upper := bV
      rate := aW / bV
      lower_pos := haV
      upper_pos := hbVpos
      rate_pos := div_pos haW hbVpos
      smooth := energy_smooth m
      equilibrium := by
        show m.field (0 + m.point) 0 = 0
        rw [zero_add]
        exact he
      lower_bound := fun x => by rw [sub_zero]; exact (hV x).1
      upper_bound := fun x => by rw [sub_zero]; exact (hV x).2
      dissipation := fun x => by
        show fderiv ℝ m.energy x (m.system.field x 0) ≤ _
        rw [energy_lie m hCdc.ne' hL.ne' hC.ne' he x 0]
        simp only [Pi.zero_apply, zero_mul, add_zero]
        have h1 := (hW x).1
        have h2 : aW / bV * m.energy x ≤ aW * ‖x‖ ^ 2 :=
          calc aW / bV * m.energy x ≤ aW / bV * (bV * ‖x‖ ^ 2) :=
                mul_le_mul_of_nonneg_left (hV x).2 (div_nonneg haW.le hbVpos.le)
            _ = aW * ‖x‖ ^ 2 := by field_simp
        linarith }
  exact c.globallyExponentiallyStable (zeroInput_smooth m)

private theorem passive (m : Model) (hCdc : 0 < m.Cdc) (hL : 0 < m.L) (hC : 0 < m.C)
    (hR : 0 < m.R) (hG : 0 < m.G + m.Gl) (he : m.field m.point 0 = 0) (hδ : 0 < m.margin) :
    m.system.PassiveWith m.energy := by
  refine Port.System.passiveWith_of_rate m.system m.energy (energy_nonneg m hCdc hL hC)
    (fun z u => fderiv ℝ m.energy z (m.system.field z u))
    (fun u x t₀ t₁ t hx ht =>
      ((energy_smooth m).differentiable (by norm_num) (x t)).hasFDerivAt.comp_hasDerivWithinAt t
        (hx t ht)) (fun z u => ?_)
  rw [energy_lie m hCdc.ne' hL.ne' hC.ne' he z u]
  have h := dissipation_nonneg m hR hG hδ z
  simp only [Port.System.supply, Model.system, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linarith

/-- Static requirements on reduced matching models. -/
inductive Requirement
  | physical
  | equilibrium
  | damping
  | slowRate (r : ℝ)

/-- Satisfaction of a requirement. -/
def Meets (m : Model) : Requirement → Prop
  | .physical => 0 < m.Cdc ∧ 0 < m.L ∧ 0 < m.C ∧ 0 < m.R ∧ 0 < m.G + m.Gl
  | .equilibrium => m.field m.point 0 = 0
  | .damping => 0 < m.margin
  | .slowRate r => r ≤ 0

/-- The translation: stability sentences, sampled contraction and passivity into the physical,
equilibrium and damping requirements; a decay rate `r` additionally into `r ≤ 0`; instability
and conservation into the whole, inconsistent, language (unavailable coverage). -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable | .flow .globallyAsymptoticallyStable
  | .flow .globallyExponentiallyStable | .flow .contractive => {.physical, .equilibrium, .damping}
  | .flow (.decay r) => {.physical, .equilibrium, .damping, .slowRate r}
  | .flow .unstable | .flow .conservative => Set.univ
  | .passive => {.physical, .equilibrium, .damping}

/-- The reduced matching closed-loop family. -/
def family : Family Model Requirement 5 3 := ⟨Model.system, Meets, translate⟩

/-- The whole requirement language is inconsistent (`r ≤ 0` fails at `r = 1`). -/
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext m
  simp only [TMIO.mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro h
  have : (1 : ℝ) ≤ 0 := h (.slowRate 1)
  norm_num at this

/-- Every translation of the reduced matching family is sound. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s m hm => ?_
  rw [TMIO.mem_realize] at hm
  change ∀ q ∈ translate s, Meets m q at hm
  rw [Family.mem_den]
  have key : (∀ q ∈ ({.physical, .equilibrium, .damping} : Set Requirement), Meets m q) →
      Flow.GloballyExponentiallyStable m.system.zeroInput 0 ∧ m.system.Passive := by
    intro h
    obtain ⟨hCdc, hL, hC, hR, hG⟩ : Meets m .physical := h _ (by simp)
    have he : Meets m .equilibrium := h _ (by simp)
    have hδ : Meets m .damping := h _ (by simp)
    exact ⟨ges m hCdc hL hC hR hG he hδ, _, passive m hCdc hL hC hR hG he hδ⟩
  rcases s with P | _
  · simp only [Sentence.holds]
    cases P
    case lyapunovStable => exact (key hm).1.lyapunovStable
    case locallyAsymptoticallyStable =>
      exact (key hm).1.holds Flow.Property.attractive_locallyAsymptoticallyStable
    case locallyExponentiallyStable => exact (key hm).1.locallyExponentiallyStable
    case globallyAsymptoticallyStable => exact (key hm).1.globallyAsymptoticallyStable
    case globallyExponentiallyStable => exact (key hm).1
    case contractive => exact (key hm).1.sampledContraction
    case decay r =>
      have hk := key fun q hq => hm q (by
        simp only [translate, Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
        tauto)
      have hr : r ≤ 0 := hm (.slowRate r) (by simp [translate])
      obtain ⟨a, ha, hd⟩ := hk.1.exists_decay
      exact hd.mono (by linarith)
    case unstable =>
      have : (1 : ℝ) ≤ 0 := hm (.slowRate 1) trivial
      norm_num at this
    case conservative =>
      have : (1 : ℝ) ≤ 0 := hm (.slowRate 1) trivial
      norm_num at this
  · exact (key hm).2

/-- **Global exponential stability of the matching closed loop in the rotating frame**: with
`C_dc, L, C, R, G + G_l > 0`, the selected point an equilibrium and a positive damping margin,
the steady state of the reduced model is globally exponentially stable (the source proves global
asymptotic stability). -/
@[powerlib_domain] theorem mem_den_globallyExponentiallyStable (m : Model) (hCdc : 0 < m.Cdc)
    (hL : 0 < m.L) (hC : 0 < m.C) (hR : 0 < m.R) (hG : 0 < m.G + m.Gl)
    (he : m.field m.point 0 = 0) (hδ : 0 < m.margin) :
    connection% (m ∈ family.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [Family.mem_den]
  exact ges m hCdc hL hC hR hG he hδ

/-- The source's corollary "Closed-loop stability with DC-side P-control": global asymptotic
stability of the steady state of the reduced model. -/
@[powerlib_domain] theorem mem_den_globallyAsymptoticallyStable (m : Model) (hCdc : 0 < m.Cdc)
    (hL : 0 < m.L) (hC : 0 < m.C) (hR : 0 < m.R) (hG : 0 < m.G + m.Gl)
    (he : m.field m.point 0 = 0) (hδ : 0 < m.margin) :
    connection% (m ∈ family.den (.flow .globallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [Family.mem_den]
  exact (ges m hCdc hL hC hR hG he hδ).globallyAsymptoticallyStable

/-- Every attractive sentence and sampled contraction. -/
@[powerlib_domain] theorem mem_den_attractive (m : Model) (hCdc : 0 < m.Cdc)
    (hL : 0 < m.L) (hC : 0 < m.C) (hR : 0 < m.R) (hG : 0 < m.G + m.Gl)
    (he : m.field m.point 0 = 0) (hδ : 0 < m.margin) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (m ∈ family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  rw [Family.mem_den]
  rcases hP with hP | rfl
  · exact (ges m hCdc hL hC hR hG he hδ).holds hP
  · exact (ges m hCdc hL hC hR hG he hδ).sampledContraction

/-- Passivity relative to the steady state, from the port perturbations `(ĩ_dc, −ĩ_l,dq)` to
`(ṽ_dc, ṽ_dq)` (the source's passivity theorem, with the P-control and load admittance
absorbed into the damping). -/
@[powerlib_domain] theorem mem_den_passive (m : Model) (hCdc : 0 < m.Cdc)
    (hL : 0 < m.L) (hC : 0 < m.C) (hR : 0 < m.R) (hG : 0 < m.G + m.Gl)
    (he : m.field m.point 0 = 0) (hδ : 0 < m.margin) :
    connection% (m ∈ family.den .passive) := by
  unfold powerlib.TMIO.Statement
  rw [Family.mem_den]
  exact ⟨_, passive m hCdc hL hC hR hG he hδ⟩

/-- For `η ≠ 0` the damping requirement is the source's inequality
`C²‖v*‖²/(4(G+G_l)) + L²‖i*‖²/(4R) < (G_dc+K_p)/η²`. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem margin_pos_iff (m : Model) (hη : m.η ≠ 0) :
    0 < m.margin ↔ m.C ^ 2 * (m.vdStar ^ 2 + m.vqStar ^ 2) / (4 * (m.G + m.Gl)) +
      m.L ^ 2 * (m.idStar ^ 2 + m.iqStar ^ 2) / (4 * m.R) < (m.Gdc + m.Kp) / m.η ^ 2 := by
  have hη2 : 0 < m.η ^ 2 := by positivity
  rw [lt_div_iff₀ hη2, Model.margin, sub_pos]
  constructor <;> intro h <;> linarith

/-- Uniqueness of the steady state: under the requirements every equilibrium of the reduced field
is the selected point. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem eq_point_of_field_eq_zero (m : Model) (hCdc : 0 < m.Cdc)
    (hL : 0 < m.L) (hC : 0 < m.C) (hR : 0 < m.R) (hG : 0 < m.G + m.Gl)
    (he : m.field m.point 0 = 0) (hδ : 0 < m.margin) {x : State 5} (hx : m.field x 0 = 0) :
    x = m.point := by
  by_contra hne
  have hz : x - m.point ≠ 0 := sub_ne_zero.mpr hne
  have hl := energy_lie m hCdc.ne' hL.ne' hC.ne' he (x - m.point) 0
  have hf : m.system.field (x - m.point) 0 = 0 := by
    show m.field (x - m.point + m.point) 0 = 0
    rw [sub_add_cancel]
    exact hx
  rw [hf, map_zero] at hl
  simp only [Pi.zero_apply, zero_mul, add_zero] at hl
  have := dissipation_pos m hR hG hδ _ hz
  linarith

/-- A model with nonzero currents meeting every requirement: `C_dc = G_dc = K_p = η = μ = L = R =
C = G = 1`, `G_l = B_l = 0`, `i_dc,ref = 9/8`, `v_dc,ref = 1`, `s_dq = (0, −1/4)`, selected point
`v* = 1`, `i* = (0, 1/4)`, `v_dq* = (1/4, 1/4)`. -/
def example1 : Model :=
  { Cdc := 1, Gdc := 1, Kp := 1, idcRef := 9 / 8, vdcRef := 1, η := 1, μ := 1, L := 1, R := 1,
    C := 1, G := 1, Gl := 0, Bl := 0, sd := 0, sq := -1 / 4, vStar := 1, idStar := 0,
    iqStar := 1 / 4, vdStar := 1 / 4, vqStar := 1 / 4 }

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem example1_equilibrium : example1.field example1.point 0 = 0 := by
  ext i
  fin_cases i <;> simp [Model.field, Model.point, example1] <;> norm_num

/-- Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem example1_margin : example1.margin = 125 / 64 := by
  simp [Model.margin, example1]
  norm_num

/-- Nonvacuity: the example is globally exponentially stable. -/
@[powerlib_domain] theorem example1_mem_den :
    connection% (example1 ∈ family.den (.flow .globallyExponentiallyStable)) :=
  mem_den_globallyExponentiallyStable example1 (by norm_num [example1]) (by norm_num [example1])
    (by norm_num [example1]) (by norm_num [example1]) (by norm_num [example1])
    example1_equilibrium (by rw [example1_margin]; norm_num)

/-! ## Stationary frame -/

/-- The `d` component `cos θ a + sin θ b` of `R_θᵀ (a, b)`. -/
def rotD (θ a b : ℝ) : ℝ := Real.cos θ * a + Real.sin θ * b

/-- The `q` component `−sin θ a + cos θ b` of `R_θᵀ (a, b)`. -/
def rotQ (θ a b : ℝ) : ℝ := -Real.sin θ * a + Real.cos θ * b

/-- The rotating-frame chain rule `(R_θᵀ z)' = R_θᵀ z' − θ' J R_θᵀ z`, for arbitrary functions. -/
@[powerlib_foundation] theorem hasDerivWithinAt_rot {θ a b : ℝ → ℝ} {θ' a' b' t : ℝ}
    {s : Set ℝ} (hθ : HasDerivWithinAt θ θ' s t) (ha : HasDerivWithinAt a a' s t)
    (hb : HasDerivWithinAt b b' s t) :
    HasDerivWithinAt (fun τ => rotD (θ τ) (a τ) (b τ))
        (rotD (θ t) a' b' + θ' * rotQ (θ t) (a t) (b t)) s t ∧
      HasDerivWithinAt (fun τ => rotQ (θ τ) (a τ) (b τ))
        (rotQ (θ t) a' b' - θ' * rotD (θ t) (a t) (b t)) s t := by
  have hc := hθ.cos
  have hs := hθ.sin
  constructor
  · convert (hc.mul ha).add (hs.mul hb) using 1
    · funext τ
      simp [rotD]
    · simp only [rotD, rotQ]
      ring
  · convert (hs.neg.mul ha).add (hc.mul hb) using 1
    · funext τ
      simp [rotQ]
    · simp only [rotD, rotQ, Pi.neg_apply]
      ring

/-- The stationary-frame closed loop, state `(θ, v_dc, i_α, i_β, v_α, v_β, s_α, s_β)`: matching
`θ' = η v_dc`, DC node with P-control, inductor, capacitor with load `(G_l I + B_l J) v_αβ + s_αβ`,
and the load oscillator `s' = η v_dc J s`. -/
def Model.abField (m : Model) (X : State 8) : State 8 :=
  WithLp.toLp 2 ![
    m.η * X 1,
    (-m.Gdc * X 1 + m.idcRef - m.Kp * (X 1 - m.vdcRef)
      - m.μ / 2 * (-Real.sin (X 0) * X 2 + Real.cos (X 0) * X 3)) / m.Cdc,
    (-m.R * X 2 - X 4 + m.μ / 2 * (-Real.sin (X 0)) * X 1) / m.L,
    (-m.R * X 3 - X 5 + m.μ / 2 * Real.cos (X 0) * X 1) / m.L,
    (-(m.G + m.Gl) * X 4 + m.Bl * X 5 - X 6 + X 2) / m.C,
    (-(m.G + m.Gl) * X 5 - m.Bl * X 4 - X 7 + X 3) / m.C,
    -(m.η * X 1) * X 7,
    m.η * X 1 * X 6]

/-- The reduction `(θ, v_dc, i_αβ, v_αβ, s_αβ) ↦ (v_dc, R_θᵀ i_αβ, R_θᵀ v_αβ)`. -/
def reduce (X : State 8) : State 5 :=
  WithLp.toLp 2 ![X 1, rotD (X 0) (X 2) (X 3), rotQ (X 0) (X 2) (X 3), rotD (X 0) (X 4) (X 5),
    rotQ (X 0) (X 4) (X 5)]

/-- The parameters with the load source `s_dq` replaced. -/
def Model.withLoad (m : Model) (sd sq : ℝ) : Model := { m with sd := sd, sq := sq }

/-- The reduced field is the stationary field in the coordinates of `θ`: each reduced component
equals the rotating-frame chain rule applied to the stationary field, with the load source
`s_dq = R_θᵀ s_αβ`, whose own rotating-frame derivative vanishes. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem field_reduce (m : Model) (X : State 8) :
    let F := m.abField X
    let m' := m.withLoad (rotD (X 0) (X 6) (X 7)) (rotQ (X 0) (X 6) (X 7))
    m'.field (reduce X) 0 0 = F 1 ∧
    m'.field (reduce X) 0 1 = rotD (X 0) (F 2) (F 3) + F 0 * rotQ (X 0) (X 2) (X 3) ∧
    m'.field (reduce X) 0 2 = rotQ (X 0) (F 2) (F 3) - F 0 * rotD (X 0) (X 2) (X 3) ∧
    m'.field (reduce X) 0 3 = rotD (X 0) (F 4) (F 5) + F 0 * rotQ (X 0) (X 4) (X 5) ∧
    m'.field (reduce X) 0 4 = rotQ (X 0) (F 4) (F 5) - F 0 * rotD (X 0) (X 4) (X 5) ∧
    rotD (X 0) (F 6) (F 7) + F 0 * rotQ (X 0) (X 6) (X 7) = 0 ∧
    rotQ (X 0) (F 6) (F 7) - F 0 * rotD (X 0) (X 6) (X 7) = 0 := by
  intro F m'
  have hsc := Real.sin_sq_add_cos_sq (X 0)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [F, m', Model.field, Model.abField, Model.withLoad, reduce, rotD, rotQ,
      div_eq_mul_inv, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val,
      Pi.zero_apply, Matrix.head_cons, Matrix.tail_cons]
  · ring
  · ring
  · linear_combination (-(m.μ / 2) * X 1 * m.L⁻¹) * hsc
  · ring
  · ring
  · ring
  · ring

private theorem coord_hasDerivWithinAt {n : ℕ} {φ : ℝ → State n} {φ' : State n} {s : Set ℝ}
    {t : ℝ} (h : HasDerivWithinAt φ φ' s t) (i : Fin n) :
    HasDerivWithinAt (fun τ => φ τ i) (φ' i) s t :=
  (PiLp.proj 2 (fun _ : Fin n => ℝ) i : State n →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t h

private theorem hasDerivWithinAt_of_coord {n : ℕ} {φ : ℝ → State n} {φ' : State n}
    {s : Set ℝ} {t : ℝ} (h : ∀ i, HasDerivWithinAt (fun τ => φ τ i) (φ' i) s t) :
    HasDerivWithinAt φ φ' s t := by
  have h1 : HasDerivWithinAt (fun τ => (φ τ).ofLp) φ'.ofLp s t := hasDerivWithinAt_pi.mpr h
  have h2 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.hasFDerivAt.comp_hasDerivWithinAt
    t h1
  have e : (⇑(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm ∘ fun τ => (φ τ).ofLp) = φ := by
    funext τ
    simp
  rw [e] at h2
  simpa using h2

private theorem abField_smooth (m : Model) : ContDiff ℝ 1 m.abField := by
  have h0 : ContDiff ℝ 1 (fun x : State 8 => x 0) := coord_smooth' 0
  have h1 : ContDiff ℝ 1 (fun x : State 8 => x 1) := coord_smooth' 1
  have h2 : ContDiff ℝ 1 (fun x : State 8 => x 2) := coord_smooth' 2
  have h3 : ContDiff ℝ 1 (fun x : State 8 => x 3) := coord_smooth' 3
  have h4 : ContDiff ℝ 1 (fun x : State 8 => x 4) := coord_smooth' 4
  have h5 : ContDiff ℝ 1 (fun x : State 8 => x 5) := coord_smooth' 5
  have h6 : ContDiff ℝ 1 (fun x : State 8 => x 6) := coord_smooth' 6
  have h7 : ContDiff ℝ 1 (fun x : State 8 => x 7) := coord_smooth' 7
  have hs : ContDiff ℝ 1 (fun X : State 8 => ![
    m.η * X 1,
    (-m.Gdc * X 1 + m.idcRef - m.Kp * (X 1 - m.vdcRef)
      - m.μ / 2 * (-Real.sin (X 0) * X 2 + Real.cos (X 0) * X 3)) / m.Cdc,
    (-m.R * X 2 - X 4 + m.μ / 2 * (-Real.sin (X 0)) * X 1) / m.L,
    (-m.R * X 3 - X 5 + m.μ / 2 * Real.cos (X 0) * X 1) / m.L,
    (-(m.G + m.Gl) * X 4 + m.Bl * X 5 - X 6 + X 2) / m.C,
    (-(m.G + m.Gl) * X 5 - m.Bl * X 4 - X 7 + X 3) / m.C,
    -(m.η * X 1) * X 7,
    m.η * X 1 * X 6]) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j <;> simp <;> fun_prop
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 8 => ℝ)).symm.contDiff.comp hs

/-- Along every stationary-frame solution segment the load phasor `R_θᵀ s_αβ` is constant.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem load_const (m : Model) {X : ℝ → State 8} {a b : ℝ}
    (hX : IsTrajectoryOn X m.abField a b) :
    ∀ t ∈ Set.Icc a b, rotD (X t 0) (X t 6) (X t 7) = rotD (X a 0) (X a 6) (X a 7) ∧
      rotQ (X t 0) (X t 6) (X t 7) = rotQ (X a 0) (X a 6) (X a 7) := by
  have hc : ∀ t ∈ Set.Icc a b, ∀ k : Fin 8,
      HasDerivWithinAt (fun τ => X τ k) (m.abField (X t) k) (Set.Icc a b) t :=
    fun t ht k => coord_hasDerivWithinAt (hX t ht) k
  have hrot : ∀ t ∈ Set.Icc a b, ∀ j k : Fin 8,
      HasDerivWithinAt (fun τ => rotD (X τ 0) (X τ j) (X τ k))
          (rotD (X t 0) (m.abField (X t) j) (m.abField (X t) k) +
            m.abField (X t) 0 * rotQ (X t 0) (X t j) (X t k)) (Set.Icc a b) t ∧
        HasDerivWithinAt (fun τ => rotQ (X τ 0) (X τ j) (X τ k))
          (rotQ (X t 0) (m.abField (X t) j) (m.abField (X t) k) -
            m.abField (X t) 0 * rotD (X t 0) (X t j) (X t k)) (Set.Icc a b) t :=
    fun t ht j k => hasDerivWithinAt_rot (hc t ht 0) (hc t ht j) (hc t ht k)
  have hcontD : ContinuousOn (fun τ => rotD (X τ 0) (X τ 6) (X τ 7)) (Set.Icc a b) :=
    fun t ht => ((hrot t ht 6 7).1).continuousWithinAt
  have hcontQ : ContinuousOn (fun τ => rotQ (X τ 0) (X τ 6) (X τ 7)) (Set.Icc a b) :=
    fun t ht => ((hrot t ht 6 7).2).continuousWithinAt
  have hzD : ∀ t ∈ Set.Ico a b,
      HasDerivWithinAt (fun τ => rotD (X τ 0) (X τ 6) (X τ 7)) 0 (Set.Ici t) t := by
    intro t ht
    have h := (hrot t (Set.mem_Icc_of_Ico ht) 6 7).1
    rw [(field_reduce m (X t)).2.2.2.2.2.1] at h
    exact h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  have hzQ : ∀ t ∈ Set.Ico a b,
      HasDerivWithinAt (fun τ => rotQ (X τ 0) (X τ 6) (X τ 7)) 0 (Set.Ici t) t := by
    intro t ht
    have h := (hrot t (Set.mem_Icc_of_Ico ht) 6 7).2
    rw [(field_reduce m (X t)).2.2.2.2.2.2] at h
    exact h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  intro t ht
  exact ⟨constant_of_has_deriv_right_zero hcontD hzD t ht,
    constant_of_has_deriv_right_zero hcontQ hzQ t ht⟩

/-- Every stationary-frame solution segment is mapped by `reduce` to a solution segment of the
reduced model whose load is the initial `R_θᵀ s_αβ`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem reduce_isTrajectoryOn (m : Model) {X : ℝ → State 8} {a b : ℝ}
    (hX : IsTrajectoryOn X m.abField a b) :
    IsTrajectoryOn (fun t => reduce (X t))
      (fun y => (m.withLoad (rotD (X a 0) (X a 6) (X a 7)) (rotQ (X a 0) (X a 6) (X a 7))).field
        y 0) a b := by
  have hc : ∀ t ∈ Set.Icc a b, ∀ k : Fin 8,
      HasDerivWithinAt (fun τ => X τ k) (m.abField (X t) k) (Set.Icc a b) t :=
    fun t ht k => coord_hasDerivWithinAt (hX t ht) k
  have hrot : ∀ t ∈ Set.Icc a b, ∀ j k : Fin 8,
      HasDerivWithinAt (fun τ => rotD (X τ 0) (X τ j) (X τ k))
          (rotD (X t 0) (m.abField (X t) j) (m.abField (X t) k) +
            m.abField (X t) 0 * rotQ (X t 0) (X t j) (X t k)) (Set.Icc a b) t ∧
        HasDerivWithinAt (fun τ => rotQ (X τ 0) (X τ j) (X τ k))
          (rotQ (X t 0) (m.abField (X t) j) (m.abField (X t) k) -
            m.abField (X t) 0 * rotD (X t 0) (X t j) (X t k)) (Set.Icc a b) t :=
    fun t ht j k => hasDerivWithinAt_rot (hc t ht 0) (hc t ht j) (hc t ht k)
  -- the load source is constant in the rotating frame
  have hconst := load_const m hX
  intro t ht
  obtain ⟨hD, hQ⟩ := hconst t ht
  obtain ⟨f0, f1, f2, f3, f4, -, -⟩ := field_reduce m (X t)
  simp only [hD, hQ] at f0 f1 f2 f3 f4
  have d0 : HasDerivWithinAt (fun τ => reduce (X τ) 0)
      ((m.withLoad (rotD (X a 0) (X a 6) (X a 7)) (rotQ (X a 0) (X a 6) (X a 7))).field
        (reduce (X t)) 0 0) (Set.Icc a b) t := by
    rw [f0]; simpa [reduce] using hc t ht 1
  have d1 : HasDerivWithinAt (fun τ => reduce (X τ) 1)
      ((m.withLoad (rotD (X a 0) (X a 6) (X a 7)) (rotQ (X a 0) (X a 6) (X a 7))).field
        (reduce (X t)) 0 1) (Set.Icc a b) t := by
    rw [f1]; simpa [reduce] using (hrot t ht 2 3).1
  have d2 : HasDerivWithinAt (fun τ => reduce (X τ) 2)
      ((m.withLoad (rotD (X a 0) (X a 6) (X a 7)) (rotQ (X a 0) (X a 6) (X a 7))).field
        (reduce (X t)) 0 2) (Set.Icc a b) t := by
    rw [f2]; simpa [reduce] using (hrot t ht 2 3).2
  have d3 : HasDerivWithinAt (fun τ => reduce (X τ) 3)
      ((m.withLoad (rotD (X a 0) (X a 6) (X a 7)) (rotQ (X a 0) (X a 6) (X a 7))).field
        (reduce (X t)) 0 3) (Set.Icc a b) t := by
    rw [f3]; simpa [reduce] using (hrot t ht 4 5).1
  have d4 : HasDerivWithinAt (fun τ => reduce (X τ) 4)
      ((m.withLoad (rotD (X a 0) (X a 6) (X a 7)) (rotQ (X a 0) (X a 6) (X a 7))).field
        (reduce (X t)) 0 4) (Set.Icc a b) t := by
    rw [f4]; simpa [reduce] using (hrot t ht 4 5).2
  apply hasDerivWithinAt_of_coord
  intro i
  fin_cases i
  exacts [d0, d1, d2, d3, d4]

/-! ## The stationary-frame family -/

/-- A stationary-frame matching model: parameters and a selected point
`(θ*, v*, i_α*, i_β*, v_α*, v_β*, s_α*, s_β*)`. -/
structure FullModel where
  p : Model
  θ : ℝ
  v : ℝ
  iα : ℝ
  iβ : ℝ
  uα : ℝ
  uβ : ℝ
  sα : ℝ
  sβ : ℝ

/-- The selected point. -/
def FullModel.point (M : FullModel) : State 8 :=
  WithLp.toLp 2 ![M.θ, M.v, M.iα, M.iβ, M.uα, M.uβ, M.sα, M.sβ]

/-- The stationary field translated to the selected point. -/
def FullModel.field (M : FullModel) (z : State 8) : State 8 := M.p.abField (z + M.point)

/-- The stationary-frame family: no requirement language of its own (every flow translation is
unavailable coverage); its content is its semantics. -/
def fullFamily : Family FullModel Spectral.Requirement 8 0 :=
  Spectral.localFamily FullModel.field (fun _ => False) (fun _ => False)

/-- Every translation of the stationary-frame family is sound. -/
@[powerlib_domain] theorem fullChain_le_semantics :
    connection% (∀ P, fullFamily.chain P ≤ fullFamily.semantics P) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.local_chain_le_semantics (fun _ h => h.elim) (fun _ h => h.elim)

private theorem full_mem_den_flow {M : FullModel} {P : Flow.Property} :
    M ∈ fullFamily.den (.flow P) ↔ P.holds M.p.abField M.point :=
  (Spectral.localFamily_isAutonomous _ _ _).mem_den_flow.trans (Flow.Property.holds_shift_iff P)

/-- The stationary field is `2π`-periodic in `θ`. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem abField_add_two_pi (m : Model) (θ v iα iβ uα uβ sα sβ : ℝ) :
    m.abField (WithLp.toLp 2 ![θ + 2 * Real.pi, v, iα, iβ, uα, uβ, sα, sβ]) =
      m.abField (WithLp.toLp 2 ![θ, v, iα, iβ, uα, uβ, sα, sβ]) := by
  simp [Model.abField, Real.sin_add_two_pi, Real.cos_add_two_pi]

/-- Every stationary-frame equilibrium has zero frequency `η v_dc`. Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem abField_eq_zero (m : Model) {X : State 8} (h : m.abField X = 0) :
    m.η * X 1 = 0 := by
  have := congrArg (fun Y : State 8 => Y 0) h
  simpa [Model.abField] using this

/-- **Boundary**: in the stationary frame no selected point of the matching closed loop is globally
asymptotically stable on `ℝ⁸` (`2π`-periodicity gives a second equilibrium whenever the point is
one). -/
@[powerlib_domain] theorem full_not_mem_den_globallyAsymptoticallyStable (M : FullModel) :
    connection% (M ∉ fullFamily.den (.flow .globallyAsymptoticallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [full_mem_den_flow]
  intro h
  change Flow.GloballyAsymptoticallyStable _ _ at h
  refine Dynamics.not_globallyAsymptoticallyStable_of_equilibrium_ne
    (y := WithLp.toLp 2 ![M.θ + 2 * Real.pi, M.v, M.iα, M.iβ, M.uα, M.uβ, M.sα, M.sβ]) ?_ ?_ h
  · rw [abField_add_two_pi]
    exact h.1
  · intro he
    have h0 := congrArg (fun z : State 8 => z 0) he
    simp [FullModel.point, Real.pi_ne_zero] at h0

/-- The same boundary for global exponential stability. -/
@[powerlib_domain] theorem full_not_mem_den_globallyExponentiallyStable (M : FullModel) :
    connection% (M ∉ fullFamily.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  rw [full_mem_den_flow] at h
  have := full_not_mem_den_globallyAsymptoticallyStable M
  unfold powerlib.TMIO.Statement at this
  rw [full_mem_den_flow] at this
  exact this (Flow.GloballyExponentiallyStable.globallyAsymptoticallyStable h)

/-- A selected point with nonzero frequency `η v* ≠ 0` is not an equilibrium of the stationary
closed loop, hence not Lyapunov stable: the steady state is a rotating orbit. -/
@[powerlib_domain] theorem full_mem_den_unstable (M : FullModel) (h : M.p.η * M.v ≠ 0) :
    connection% (M ∈ fullFamily.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  rw [full_mem_den_flow]
  intro hs
  have he := Dynamics.isEquilibrium_of_lyapunovStable (abField_smooth M.p) hs
  have := abField_eq_zero M.p he
  simp only [FullModel.point, PiLp.toLp_apply, Matrix.cons_val_one] at this
  exact h this

/-! ## Attraction of the steady-state orbit in the stationary frame -/

/-- The steady state rotated by `θ`: `(θ, v*, R_θ i*_dq, R_θ v*_dq, R_θ s_dq)`. Its range is the
steady-state rotating orbit in the stationary frame. -/
def Model.orbitPoint (m : Model) (θ : ℝ) : State 8 :=
  WithLp.toLp 2 ![θ, m.vStar,
    Real.cos θ * m.idStar - Real.sin θ * m.iqStar, Real.sin θ * m.idStar + Real.cos θ * m.iqStar,
    Real.cos θ * m.vdStar - Real.sin θ * m.vqStar, Real.sin θ * m.vdStar + Real.cos θ * m.vqStar,
    Real.cos θ * m.sd - Real.sin θ * m.sq, Real.sin θ * m.sd + Real.cos θ * m.sq]

/-- `R_θᵀ R_θ = 1`, `d` component. Static evidence, not a connection conclusion. -/
@[powerlib_foundation] theorem rotD_rot (θ d q : ℝ) :
    rotD θ (Real.cos θ * d - Real.sin θ * q) (Real.sin θ * d + Real.cos θ * q) = d := by
  simp only [rotD]
  linear_combination d * Real.sin_sq_add_cos_sq θ

/-- `R_θᵀ R_θ = 1`, `q` component. Static evidence, not a connection conclusion. -/
@[powerlib_foundation] theorem rotQ_rot (θ d q : ℝ) :
    rotQ θ (Real.cos θ * d - Real.sin θ * q) (Real.sin θ * d + Real.cos θ * q) = q := by
  simp only [rotQ]
  linear_combination q * Real.sin_sq_add_cos_sq θ

/-- `‖z − R_θ w‖ = ‖R_θᵀ z − w‖`. Static evidence, not a connection conclusion. -/
@[powerlib_foundation] theorem rot_dist_sq (θ a b d q : ℝ) :
    (a - (Real.cos θ * d - Real.sin θ * q)) ^ 2 + (b - (Real.sin θ * d + Real.cos θ * q)) ^ 2 =
      (rotD θ a b - d) ^ 2 + (rotQ θ a b - q) ^ 2 := by
  simp only [rotD, rotQ]
  linear_combination (d ^ 2 + q ^ 2 - a ^ 2 - b ^ 2) * Real.sin_sq_add_cos_sq θ

/-- `‖R_a w − R_b w‖² = 2 ‖w‖² (1 − cos (a − b))`. Static evidence, not a connection conclusion. -/
@[powerlib_foundation] theorem rot_sub_rot_sq (a b d q : ℝ) :
    (Real.cos a * d - Real.sin a * q - (Real.cos b * d - Real.sin b * q)) ^ 2 +
      (Real.sin a * d + Real.cos a * q - (Real.sin b * d + Real.cos b * q)) ^ 2 =
      2 * (d ^ 2 + q ^ 2) * (1 - Real.cos (a - b)) := by
  rw [Real.cos_sub]
  linear_combination (d ^ 2 + q ^ 2) * Real.sin_sq_add_cos_sq a +
    (d ^ 2 + q ^ 2) * Real.sin_sq_add_cos_sq b

/-- The orbit reduces to the selected point. Static evidence, not a connection conclusion. -/
@[powerlib_foundation] theorem reduce_orbitPoint (m : Model) (θ : ℝ) :
    reduce (m.orbitPoint θ) = m.point := by
  ext i
  fin_cases i <;> simp [reduce, Model.orbitPoint, Model.point, rotD_rot, rotQ_rot]

/-- The orbit carries the model's load phasor. Static evidence, not a connection conclusion. -/
@[powerlib_foundation] theorem orbitPoint_load (m : Model) (θ : ℝ) :
    rotD (m.orbitPoint θ 0) (m.orbitPoint θ 6) (m.orbitPoint θ 7) = m.sd ∧
      rotQ (m.orbitPoint θ 0) (m.orbitPoint θ 6) (m.orbitPoint θ 7) = m.sq := by
  simp [Model.orbitPoint, rotD_rot, rotQ_rot]

/-- With the model's load phasor, the distance to the orbit point of the same angle is the
rotating-frame deviation. Static evidence, not a connection conclusion. -/
@[powerlib_foundation] theorem norm_sub_orbitPoint (m : Model) (X : State 8)
    (hD : rotD (X 0) (X 6) (X 7) = m.sd) (hQ : rotQ (X 0) (X 6) (X 7) = m.sq) :
    ‖X - m.orbitPoint (X 0)‖ = ‖reduce X - m.point‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  have h1 := rot_dist_sq (X 0) (X 2) (X 3) m.idStar m.iqStar
  have h2 := rot_dist_sq (X 0) (X 4) (X 5) m.vdStar m.vqStar
  have h3 := rot_dist_sq (X 0) (X 6) (X 7) m.sd m.sq
  rw [hD, hQ, sub_self, sub_self] at h3
  simp [Fin.sum_univ_eight, Fin.sum_univ_five, Model.orbitPoint, reduce, Model.point]
  linarith

/-- The orbit is Lipschitz in its angle. Static evidence, not a connection conclusion. -/
@[powerlib_foundation] theorem norm_orbitPoint_sub_le (m : Model) (a b : ℝ) :
    ‖m.orbitPoint a - m.orbitPoint b‖ ≤ Real.sqrt (1 + (m.idStar ^ 2 + m.iqStar ^ 2) +
      (m.vdStar ^ 2 + m.vqStar ^ 2) + (m.sd ^ 2 + m.sq ^ 2)) * |a - b| := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have hc : 2 * (1 - Real.cos (a - b)) ≤ (a - b) ^ 2 := by
    have := Real.one_sub_sq_div_two_le_cos (x := a - b)
    linarith
  have h1 := rot_sub_rot_sq a b m.idStar m.iqStar
  have h2 := rot_sub_rot_sq a b m.vdStar m.vqStar
  have h3 := rot_sub_rot_sq a b m.sd m.sq
  have k1 := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ m.idStar ^ 2 + m.iqStar ^ 2)
  have k2 := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ m.vdStar ^ 2 + m.vqStar ^ 2)
  have k3 := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ m.sd ^ 2 + m.sq ^ 2)
  simp [Fin.sum_univ_eight, Model.orbitPoint]
  linarith

/-- On the load-matched set the rotating-frame deviation is at most `(1 + Λ)` times the distance
to the orbit (`Λ` the Lipschitz constant of the orbit). Implementation evidence (it names the
orbit `range orbitPoint` of the model, Rules §3a). -/
private theorem norm_reduce_sub_le (m : Model) (X : State 8)
    (hD : rotD (X 0) (X 6) (X 7) = m.sd) (hQ : rotQ (X 0) (X 6) (X 7) = m.sq) :
    ‖reduce X - m.point‖ ≤ (1 + Real.sqrt (1 + (m.idStar ^ 2 + m.iqStar ^ 2) +
      (m.vdStar ^ 2 + m.vqStar ^ 2) + (m.sd ^ 2 + m.sq ^ 2))) *
      Metric.infDist X (Set.range m.orbitPoint) := by
  set Λ := Real.sqrt (1 + (m.idStar ^ 2 + m.iqStar ^ 2) + (m.vdStar ^ 2 + m.vqStar ^ 2) +
    (m.sd ^ 2 + m.sq ^ 2))
  have hΛ : 0 ≤ Λ := Real.sqrt_nonneg _
  have hB : 0 < 1 + Λ := by linarith
  by_contra hlt
  rw [not_le] at hlt
  have hlt' : Metric.infDist X (Set.range m.orbitPoint) < ‖reduce X - m.point‖ / (1 + Λ) := by
    rw [lt_div_iff₀ hB]
    linarith
  obtain ⟨Y, ⟨φ, rfl⟩, hY⟩ := (Metric.infDist_lt_iff (Set.range_nonempty m.orbitPoint)).mp hlt'
  rw [dist_eq_norm, lt_div_iff₀ hB] at hY
  have h1 := norm_sub_orbitPoint m X hD hQ
  have h2 : ‖X - m.orbitPoint (X 0)‖ ≤
      ‖X - m.orbitPoint φ‖ + ‖m.orbitPoint φ - m.orbitPoint (X 0)‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  have h3 := norm_orbitPoint_sub_le m φ (X 0)
  have h4 : |φ - X 0| ≤ ‖X - m.orbitPoint φ‖ := by
    have := PiLp.norm_apply_le (X - m.orbitPoint φ) 0
    simp only [PiLp.sub_apply, Real.norm_eq_abs] at this
    rw [abs_sub_comm]
    simpa [Model.orbitPoint] using this
  have h5 : Λ * |φ - X 0| ≤ Λ * ‖X - m.orbitPoint φ‖ := mul_le_mul_of_nonneg_left h4 hΛ
  nlinarith

private theorem orbitPoint_continuous (m : Model) : Continuous m.orbitPoint := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 8 => ℝ)).comp
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp <;> fun_prop

private theorem isClosed_orbit (m : Model) : IsClosed (Set.range m.orbitPoint) := by
  have e : Set.range m.orbitPoint = {X : State 8 | X = m.orbitPoint (X 0)} := by
    ext X
    constructor
    · rintro ⟨φ, rfl⟩
      show m.orbitPoint φ = m.orbitPoint (m.orbitPoint φ 0)
      simp [Model.orbitPoint]
    · intro h
      exact ⟨X 0, h.symm⟩
  rw [e]
  exact isClosed_eq continuous_id ((orbitPoint_continuous m).comp
    (PiLp.proj 2 (fun _ : Fin 8 => ℝ) 0 : State 8 →L[ℝ] ℝ).continuous)

/-- **Exponential attraction of the steady-state orbit in the stationary frame.** Under the static
requirements (`C_dc, L, C, R, G + G_l > 0`, the selected point an equilibrium, `margin > 0`),
there are `K ≥ 0`, `a > 0` such that every stationary-frame solution segment whose load phasor
`R_θᵀ s_αβ` is the model's `s_dq` (a stationary load in the source's sense) satisfies
`dist(X t, O) ≤ K e^{−a (t − t₀)} dist(X t₀, O)`, `O = range orbitPoint` the steady-state orbit.
Proof: global exponential stability in the reduced coordinates (`ges`), the reduction of solutions
(`reduce_isTrajectoryOn`, `load_const`), and the two-sided comparison `norm_sub_orbitPoint`,
`norm_reduce_sub_le` through `Dynamics.LaSalle.infDist_le_of_reduction'`.
Implementation evidence: set attraction is outside the sentence language (Rules §3a). -/
private theorem orbit_exponentiallyAttractive (m : Model) (hCdc : 0 < m.Cdc) (hL : 0 < m.L)
    (hC : 0 < m.C) (hR : 0 < m.R) (hG : 0 < m.G + m.Gl) (he : m.field m.point 0 = 0)
    (hδ : 0 < m.margin) :
    ∃ K a : ℝ, 0 ≤ K ∧ 0 < a ∧ ∀ (t₀ t₁ : ℝ) (X : ℝ → State 8), IsTrajectoryOn X m.abField t₀ t₁ →
      rotD (X t₀ 0) (X t₀ 6) (X t₀ 7) = m.sd → rotQ (X t₀ 0) (X t₀ 6) (X t₀ 7) = m.sq →
      ∀ t ∈ Set.Icc t₀ t₁, Metric.infDist (X t) (Set.range m.orbitPoint) ≤
        K * Real.exp (-a * (t - t₀)) * Metric.infDist (X t₀) (Set.range m.orbitPoint) := by
  have hges : Flow.GloballyExponentiallyStable (fun y => m.field y 0) m.point :=
    Dynamics.globallyExponentiallyStable_shift_iff.mp (ges m hCdc hL hC hR hG he hδ)
  have hwl : m.withLoad m.sd m.sq = m := by cases m; rfl
  have hB : 0 ≤ 1 + Real.sqrt (1 + (m.idStar ^ 2 + m.iqStar ^ 2) +
      (m.vdStar ^ 2 + m.vqStar ^ 2) + (m.sd ^ 2 + m.sq ^ 2)) := by
    have := Real.sqrt_nonneg (1 + (m.idStar ^ 2 + m.iqStar ^ 2) +
      (m.vdStar ^ 2 + m.vqStar ^ 2) + (m.sd ^ 2 + m.sq ^ 2))
    linarith
  have hred : ∀ (t₀ t₁ : ℝ) (X : ℝ → State 8), IsTrajectoryOn X m.abField t₀ t₁ →
      X t₀ ∈ {X : State 8 | rotD (X 0) (X 6) (X 7) = m.sd ∧ rotQ (X 0) (X 6) (X 7) = m.sq} →
      IsTrajectoryOn (fun t => reduce (X t)) (fun y => m.field y 0) t₀ t₁ ∧
        ∀ t ∈ Set.Icc t₀ t₁,
          X t ∈ {X : State 8 | rotD (X 0) (X 6) (X 7) = m.sd ∧ rotQ (X 0) (X 6) (X 7) = m.sq} := by
    rintro t₀ t₁ X hX ⟨hD, hQ⟩
    have hr := reduce_isTrajectoryOn m hX
    rw [hD, hQ, hwl] at hr
    refine ⟨hr, fun t ht => ?_⟩
    obtain ⟨h1, h2⟩ := load_const m hX t ht
    exact ⟨h1.trans hD, h2.trans hQ⟩
  have hO : ∀ X ∈ {X : State 8 | rotD (X 0) (X 6) (X 7) = m.sd ∧ rotQ (X 0) (X 6) (X 7) = m.sq},
      Metric.infDist X (Set.range m.orbitPoint) ≤ 1 * ‖reduce X - m.point‖ := by
    rintro X ⟨hD, hQ⟩
    rw [one_mul, ← norm_sub_orbitPoint m X hD hQ, ← dist_eq_norm]
    exact Metric.infDist_le_dist_of_mem (Set.mem_range_self (X 0))
  have hO' : ∀ X ∈ {X : State 8 | rotD (X 0) (X 6) (X 7) = m.sd ∧ rotQ (X 0) (X 6) (X 7) = m.sq},
      ‖reduce X - m.point‖ ≤ (1 + Real.sqrt (1 + (m.idStar ^ 2 + m.iqStar ^ 2) +
        (m.vdStar ^ 2 + m.vqStar ^ 2) + (m.sd ^ 2 + m.sq ^ 2))) *
        Metric.infDist X (Set.range m.orbitPoint) := by
    rintro X ⟨hD, hQ⟩
    exact norm_reduce_sub_le m X hD hQ
  obtain ⟨K, a, hK, ha, h⟩ :=
    Dynamics.LaSalle.infDist_le_of_reduction' zero_le_one hB hges hred hO hO'
  exact ⟨K, a, hK, ha, fun t₀ t₁ X hX hD hQ => h t₀ t₁ X hX ⟨hD, hQ⟩⟩

/-- Every forward solution with the model's load phasor converges to the steady-state orbit.
Implementation evidence (Rules §3a). -/
private theorem tendsto_infDist_orbit (m : Model) (hCdc : 0 < m.Cdc) (hL : 0 < m.L)
    (hC : 0 < m.C) (hR : 0 < m.R) (hG : 0 < m.G + m.Gl) (he : m.field m.point 0 = 0)
    (hδ : 0 < m.margin) {X : ℝ → State 8} {t₀ : ℝ}
    (hX : IsIntegralCurveOn X (fun _ x => m.abField x) (Set.Ici t₀))
    (hD : rotD (X t₀ 0) (X t₀ 6) (X t₀ 7) = m.sd) (hQ : rotQ (X t₀ 0) (X t₀ 6) (X t₀ 7) = m.sq) :
    Filter.Tendsto (fun t => Metric.infDist (X t) (Set.range m.orbitPoint)) Filter.atTop
      (nhds 0) := by
  obtain ⟨K, a, hK, ha, h⟩ := orbit_exponentiallyAttractive m hCdc hL hC hR hG he hδ
  have hexp : Filter.Tendsto (fun t => Real.exp (-a * (t - t₀))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp ((Filter.tendsto_atTop_atTop.2 fun b =>
      ⟨b + t₀, fun t ht => by linarith⟩).const_mul_atTop_of_neg (by linarith))
  have hlim : Filter.Tendsto (fun t => K * Real.exp (-a * (t - t₀)) *
      Metric.infDist (X t₀) (Set.range m.orbitPoint)) Filter.atTop (nhds 0) := by
    simpa using (hexp.const_mul K).mul_const (Metric.infDist (X t₀) (Set.range m.orbitPoint))
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => Metric.infDist_nonneg) ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop t₀] with t ht
  exact h t₀ t X (hX.mono Set.Icc_subset_Ici_self) hD hQ t ⟨ht, le_rfl⟩

/-- The steady-state orbit is invariant: a solution segment starting on it stays on it.
Implementation evidence (Rules §3a). -/
private theorem orbit_invariant (m : Model) (hCdc : 0 < m.Cdc) (hL : 0 < m.L)
    (hC : 0 < m.C) (hR : 0 < m.R) (hG : 0 < m.G + m.Gl) (he : m.field m.point 0 = 0)
    (hδ : 0 < m.margin) {t₀ t₁ : ℝ} {X : ℝ → State 8} (hX : IsTrajectoryOn X m.abField t₀ t₁)
    (h0 : X t₀ ∈ Set.range m.orbitPoint) : ∀ t ∈ Set.Icc t₀ t₁, X t ∈ Set.range m.orbitPoint := by
  obtain ⟨K, a, -, -, h⟩ := orbit_exponentiallyAttractive m hCdc hL hC hR hG he hδ
  obtain ⟨φ, hφ⟩ := h0
  have hl := orbitPoint_load m φ
  rw [hφ] at hl
  intro t ht
  have hle := h t₀ t₁ X hX hl.1 hl.2 t ht
  have hmem : X t₀ ∈ Set.range m.orbitPoint := ⟨φ, hφ⟩
  rw [Metric.infDist_zero_of_mem hmem, mul_zero] at hle
  have h0' : Metric.infDist (X t) (Set.range m.orbitPoint) = 0 :=
    le_antisymm hle Metric.infDist_nonneg
  exact ((isClosed_orbit m).mem_iff_infDist_zero (Set.range_nonempty m.orbitPoint)).mpr h0'

end powerlib.GFM.Matching.MatchingClosedLoop
