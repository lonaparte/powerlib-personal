import theorem.Dynamics.Locality
import theorem.Passive.Series
import theorem.Passive.Parallel
import theorem.Criteria.Routh4
import theorem.Dynamics.ConverseLinearization
import theorem.Family.Basic
import theorem.Dynamics.Shift
import theorem.TMIO.ClaimElab
import theorem.Dynamics.Coordinates
import theorem.Spectral.Local
import theorem.SpecialFunctions.Sinusoid
import theorem.GridTiedConverter.PLL.Linear
import theorem.GridTiedConverter.GFL.DCLink.VoltageControl
import theorem.Dynamics.Transport
import theorem.GridTiedConverter.GFL.DCLink.PLLDC.Stability

/-! # Four-state GFL with PLL and dc-bus voltage loop: a parameterization of the PLL–DC model

Model boundary.
Single grid-following VSC on an infinite ac source of amplitude `V₀`
behind a lossless reactance `X_g`; three-phase balanced averaged dq model in the PLL frame,
algebraic network, quasi-steady (ideal) current loop, continuous time.
* States, in order: `θ` (PLL error angle `θ̂_g − θ_g`), `x` (PLL integrator), `V` (dc-bus
  voltage, per unit, nominal `1`), `η` (dc-voltage PI integrator).
* Port current IN-positive (absorbed), power written as absorbed power
  `P_abs = (3/2)(v_d i_d + v_q i_q)`, `i_q = 0`; an exporting converter has `i_{d0} < 0`.
* `i_dc = i_{d0} − k_pv (V − 1) − k_iv η`, `v_d = V₀ cos θ`, `v_q = −V₀ sin θ − X_g i_dc`;
  `θ̇ = k_p v_q + k_i x`, `ẋ = v_q`, `C V̇ = I_dc0 + P_abs / V` (constant-current dc source),
  `η̇ = V − 1`.  With `γ = 3/(2C)` this is `V̇ = γ v_d i_dc / V + I_dc0 / C`.
* The grid angle is held constant in `field` (autonomous model).  `fieldAngle` adds the
  grid-angle input of the error-angle coordinates, which enters only as `−θ̇_g` in `θ̇`.
* No PWM, delay, limiter, line resistance, `L_f`, or current-loop dynamics.  Results are at
  the equilibrium (linearization) level for the full nonlinear four-state field.

Reading into the PLL–DC model. The four-state model is a parameterization of the library's single
four-state DC-link model, the PLL–DC model (`PLLDC.Params`, `PLLDC.family`,
`theorem/GridTiedConverter/GFL/DCLink/PLLDC/Stability.lean`); it has no family of its own.
`Params.toPLLDC` sends every parameter set to the PLL–DC model with `ω_s = ω_g = 1`, `V_dc* = 1`,
`i_q0 = 0`, `V_g = V₀`, the same lossless line (`R_g = 0`, `X_g` at `ω = 1`), the reference
offset `i_d0`, `I₀ = I_dc0` and the same gains and DC link. The note's state `(θ, x, V, η)` is
the PLL–DC model's `(Δθ, x_pll, V_dc, ξ_v)` with the DC-voltage integrator sign flipped
(`integratorFlip`, `ξ_v = −η`: the PLL–DC model integrates `V_dc* − V_dc`, the note `V − 1`), which
fixes the operating point (`field_eq_transport`). A complete system (`Model`) is a parameter set
with a selected angle `θ₀`; its PLL–DC image `Model.toPLLDC` is the PLL–DC system of `toPLLDC` about
`(θ₀, 0, 1, 0)`, and its behaviour is that of the image: every behavioural statement below is a
membership of the image in a denotation of `PLLDC.family`. Smoothness and the Jacobian are the
PLL–DC model's read through the flip (`field_contDiffOn`, `hasFDerivAt_field`, `jacGen_eq_jacobian`,
`A0_eq_jacobian`). Scaffold: `theorem/GridTiedConverter/GFL/DCLink/FourStatePLLDC.agda`.

The `1/V` term. The physical field contains `P_abs / V`; read with Lean's `x / 0 = 0` it is `C¹`
on `V ≠ 0` (the PLL–DC model, `PLLDC.Params.field_contDiffOn`), an open set containing every
operating point, where the PLL–DC model's local linearization laws apply without a separate
regularization.

Source: work-sync `projects/vsc-parametric-oscillation/notes/theory-draft.md` §1.2, §2.3;
`.../references/gfm-driven-gfl-parametric-resonance/notes/concepts/
gfl-four-state-parametric-resonance.md` (功率方向与工作点, 四态周期线性化, 特征多项式检查);
`.../references/gfl-gfm-contrast/gfl-gfm-parametric-contrast.md` §14.

Results.
* Equilibrium `(θ₀, 0, 1, 0)` iff `V₀ sin θ₀ = −X_g i_{d0}` and `I_dc0 = −(3/2) V₀ cos θ₀ i_{d0}`;
  `θ₀ = arcsin(−X_g i_{d0}/V₀)` with `|X_g i_{d0}| < V₀` gives the principal branch
  (`cos θ₀ > 0`).
* The closed-form Jacobian `jacGen` at every state with `V ≠ 0` is the PLL–DC model's Jacobian
  conjugated by the flip (`jacGen_eq_jacobian`, `hasFDerivAt_field`); `A₀ = jacGen` at the
  operating point (`jacGen_opPoint`, `fderiv_field_opPoint`, `A0_eq_jacobian`). `A₁`, `b₁` of the
  amplitude modulation `V₀ ↦ V₀(1 + ε)` are exact: `J(z₀; ε) = A₀ + ε A₁` and `f_ε(z₀) = ε b₁`.
* Characteristic polynomial
  `det(λI − A₀) = L_PLL(λ)(λ² + 2α_cl λ + ω_cl²) − Γ(k_p λ + k_i)(k_pv λ + k_iv)` with
  `L_PLL = λ² + k_p v_{d0} λ + k_i v_{d0}` (`PLL.loopPoly` at `v_{d0}`),
  `2α_cl = γ v_{d0}(i_{d0} + k_pv)`,
  `ω_cl² = γ v_{d0} k_iv`, `Γ = γ X_g² i_{d0}²`; exact decoupling when `Γ = 0`;
  the `(V, η)` block of `A₀` is the Jacobian of the closed DC-voltage loop
  (`theorem/GridTiedConverter/GFL/DCLink/VoltageControl.lean`) with `V_d = (3/2) V₀ cos θ₀`,
  `V_dc* = 1`, `K_p = k_pv`, `K_i = k_iv`, `I_d0 = i_d0` (`dcLoop`, `A0_dcBlock`), whose negated
  trace and determinant are `2α_cl` and `ω_cl²` (`twoAlphaCl`, `omegaClSq`; closed forms
  `twoAlphaCl_eq`, `omegaClSq_eq`);
  `det A₀ = γ k_i k_iv V₀² cos 2θ₀`. The PLL–DC model's Jacobian at the image has the same quartic
  (`det_characteristicMatrix_jacobian`).
* Angle input: in error-angle coordinates `θ_g` enters only additively through `−θ̇_g`, so
  the state Jacobian does not depend on the input (`A₁^GFL = 0`, `b(jω_p) = −jω_p e_θ`).

Connection conclusions (readings into the PLL–DC model).
The four-state closed forms read the PLL–DC model's requirements at the image: the equilibrium
requirement is `IsEq` when `C ≠ 0` (`meets_equilibrium_iff`); at a point with `v_q = 0` the 4×4
Routh conditions are the quartic Routh conditions on `det(λI − A₀)` (`meets_routh_iff`, through
`Criteria.routhFin4_iff_of_det_characteristicMatrix_quartic`), a negative determinant is
`a₀ < 0` (`meets_detNeg_iff`) and the Routh boundary is the quartic's (`meets_offBoundary_iff`).
Every image has positive reference, and the Routh conditions or `det < 0` force `C ≠ 0`, so the
PLL–DC model's translation read through `toPLLDC` is the note's (equilibrium and Routh conditions
for the local sentences, equilibrium and `a₀ < 0` for instability).
* Domain: the quartic Routh–Hurwitz conditions ⇒ local exponential stability
  (`mem_den_locallyExponentiallyStable_of_routh`, from `PLLDC.mem_den_locallyExponentiallyStable`);
  `a₀ < 0` ⇒ instability (`mem_den_unstable_of_a0_neg`, from `PLLDC.mem_den_unstable_of_det_neg`);
  `cos 2θ₀ < 0` ⇒ `a₀ < 0` ⇒ unstable (`mem_den_unstable_of_cos_two_mul_neg`), hence not
  Lyapunov stable (`not_mem_den_lyapunovStable_of_cos_two_mul_neg`) and the necessary condition
  `cos 2θ₀ ≥ 0` for local exponential stability in contrapositive form
  (`not_mem_den_locallyExponentiallyStable_of_cos_two_mul_neg`, `|θ₀| ≤ 45°` on the branch).
* Characterization: a four-state model is locally exponentially stable exactly when it is an
  equilibrium (`IsEq`, `C ≠ 0`) whose quartic meets the Routh conditions
  (`mem_den_locallyExponentiallyStable_iff`: the PLL–DC model's converse linearization off the
  singular plane, `PLLDC.mem_den_locallyExponentiallyStable_iff`; with `C = 0` the determinant
  vanishes).
* Instability off equilibrium: the unbalanced model `offEquilibrium` (no ac source, constant dc
  source current) is unstable without being an equilibrium (`offEquilibrium_mem_den_unstable`,
  `PLLDC.mem_den_unstable_of_field_ne_zero`), so the PLL–DC model's instability translation is not
  exact even within positive reference (`PLLDC.not_exactUnder_positiveReference_unstable`,
  `theorem/GridTiedConverter/GFL/DCLink/PLLDC/FourStateSlice.lean`).
* The necessary closed Routh conditions of the four-state models are
  `GFL.DCLink.FourStateBoundary`; the inexpressibility of Lyapunov stability, local asymptotic
  stability and instability in the PLL–DC model's language is proved on the PLL–DC model's own
  boundary witnesses (`PLLDC.realize_ne_den_lyapunovStable` and companions,
  `theorem/GridTiedConverter/GFL/DCLink/PLLDC/Boundary.lean`).

Correction: theory-draft §1.2 gives the equilibrium `θ₀ = arcsin(−X_g i_{d0}/V₀)` without
any stability restriction; the formal statements show that local exponential stability
requires `cos 2θ₀ ≥ 0` (`θ₀ ≤ 45°` on the branch) and that `cos 2θ₀ < 0` is unstable for all
positive `k_i, k_iv, C`.  Also `|X_g i_{d0}| < V₀` is required for the principal branch.
-/

noncomputable section

namespace powerlib.GFL.DCLink

/-- The sign change of the DC-voltage integrator, `diag(1, 1, 1, −1)`: the PLL–DC model and the
carrier integrate `1 − V_dc`, the four-state GFL model `V − 1`. -/
abbrev integratorFlipMatrix : Matrix (Fin 4) (Fin 4) ℝ := Dynamics.signMatrix ![1, 1, 1, -1]

/-- `(θ, x, V, η) ↦ (θ, x, V, −η)` as a coordinate change. -/
abbrev integratorFlip : Dynamics.State 4 ≃L[ℝ] Dynamics.State 4 :=
  Dynamics.signCoord ![1, 1, 1, -1]

end powerlib.GFL.DCLink

namespace powerlib.GFL.DCLink.FourState
open Matrix

/-- Parameters of the four-state GFL model. -/
structure Params where
  /-- ac source amplitude -/
  V0 : ℝ
  /-- Grid line, a series RLC branch; its phasor impedance `R + jX` is taken at the per-unit grid
  frequency `ω = 1`; lossless. -/
  line : Passive.SeriesRLC
  /-- d-axis current reference (IN-positive) -/
  id0 : ℝ
  /-- PLL proportional gain -/
  kp : ℝ
  /-- PLL integral gain -/
  ki : ℝ
  /-- dc-voltage loop proportional gain -/
  kpv : ℝ
  /-- dc-voltage loop integral gain -/
  kiv : ℝ
  /-- dc-bus capacitance (lossless shunt). -/
  dcLink : Passive.ParallelRLC
  /-- dc source current -/
  Idc0 : ℝ
  /-- The DC link is lossless. -/
  dcLink_lossless : dcLink.G = 0
  /-- The grid line is lossless. -/
  line_lossless : line.R = 0
  /-- The DC link has no shunt inductor. -/
  dcLink_noInd : dcLink.Γ = 0

/-- The DC-link capacitance. -/
abbrev Params.C (p : Params) : ℝ := p.dcLink.C

/-- The grid reactance `X_g`. -/
abbrev Params.Xg (p : Params) : ℝ := p.line.reactance 1

namespace Params
variable (p : Params)
/-- `γ = 3/(2C)` -/
def γ : ℝ := 3 / (2 * p.C)
end Params

variable (p : Params)

/-- d-axis current command `i_dc = i_{d0} − k_pv (V − 1) − k_iv η` -/
def idc (V η : ℝ) : ℝ := p.id0 - p.kpv * (V - 1) - p.kiv * η

/-- q-axis port voltage -/
def vq (θ V η : ℝ) : ℝ := -p.V0 * Real.sin θ - p.Xg * idc p V η

/-- absorbed active power, `i_q = 0` -/
def Pabs (θ V η : ℝ) : ℝ := 3 / 2 * (p.V0 * Real.cos θ) * idc p V η

/-- Physical coordinate field, state `(θ, x, V, η)`. -/
def coordField (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![p.kp * vq p (y 0) (y 2) (y 3) + p.ki * y 1, vq p (y 0) (y 2) (y 3),
    p.Idc0 / p.C + p.γ * (p.V0 * Real.cos (y 0) * idc p (y 2) (y 3)) / y 2, y 2 - 1]

/-- The physical (nonlinear) four-state field. -/
def field : Dynamics.State 4 → Dynamics.State 4 := Dynamics.lift (coordField p)

/-- The operating point `(θ₀, 0, 1, 0)`. -/
def opPoint (θ0 : ℝ) : Dynamics.State 4 := WithLp.toLp 2 ![θ0, 0, 1, 0]

/-- Equilibrium relations of the source. -/
def IsEq (θ0 : ℝ) : Prop :=
  p.V0 * Real.sin θ0 = -(p.Xg * p.id0) ∧ p.Idc0 = -(3 / 2 * (p.V0 * Real.cos θ0) * p.id0)

/-- `v_{d0} = V₀ cos θ₀` -/
def vd0 (θ0 : ℝ) : ℝ := p.V0 * Real.cos θ0

/-- The PLL–DC parameters of the four-state model (`PLLDC.Params`,
`theorem/GridTiedConverter/GFL/DCLink/PLLDC/Basic.lean`): `ω_s = ω_g = 1` (per-unit grid
frequency), `V_dc* = 1`, `i_q0 = 0`, `V_g = V₀`, the same lossless line, the reference offset
`i_d0`, `I₀ = I_dc0`, the same gains and DC link. -/
def Params.toPLLDC : PLLDC.Params where
  ωs := 1
  ωg := 1
  kp := p.kp
  ki := p.ki
  dcLink := p.dcLink
  I0 := p.Idc0
  VdcRef := 1
  kpv := p.kpv
  kiv := p.kiv
  Vg := p.V0
  line := p.line
  iq0 := 0
  id0 := p.id0
  dcLink_lossless := p.dcLink_lossless
  dcLink_noInd := p.dcLink_noInd

/-- **The four-state model is the PLL–DC model.** For every parameter set the note's field is the
PLL–DC field of `toPLLDC` in the coordinates `(θ, x, V, η) = (Δθ, x_pll, V_dc, −ξ_v)`: the PLL–DC
model transported by the integrator flip, which fixes the operating point.
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem field_eq_transport :
    field p = Dynamics.transportField integratorFlip 0 p.toPLLDC.field := by
  funext y
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;>
    simp [Dynamics.transportField, field, Dynamics.lift, coordField, vq, idc, Params.γ,
      Params.toPLLDC, PLLDC.Params.field, PLLDC.Params.vgq, PLLDC.Params.vgd, PLLDC.Params.idRef,
      PLLDC.Params.Rg, PLLDC.Params.Xg, PLLDC.Params.Cdc, p.line_lossless,
      -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

/-- The integrator flip fixes the operating point. -/
@[tmio M, powerlib_domain] private theorem affineCoord_opPoint (θ0 : ℝ) :
    Dynamics.affineCoord integratorFlip 0 (opPoint θ0) = opPoint θ0 := by
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;> simp [Dynamics.affineCoord, opPoint]

/-- The operating point is an equilibrium of the note's field exactly when it is one of the PLL–DC
model. -/
@[tmio M, powerlib_domain] private theorem field_opPoint_eq_zero_iff (θ0 : ℝ) :
    field p (opPoint θ0) = 0 ↔ p.toPLLDC.field (opPoint θ0) = 0 := by
  rw [field_eq_transport]
  conv_lhs => rw [← affineCoord_opPoint θ0]
  exact Dynamics.transportField_affineCoord_eq_zero_iff integratorFlip 0 _ _

@[tmio M, powerlib_domain] theorem isEq_iff (hC : p.C ≠ 0) (θ0 : ℝ) :
    field p (opPoint θ0) = 0 ↔ IsEq p θ0 := by
  constructor
  · intro h
    have hc : ∀ i, coordField p ![θ0, 0, 1, 0] i = 0 := by
      intro i
      have := congrArg (fun w : Dynamics.State 4 => w i) h
      simpa [field, Dynamics.lift, opPoint] using this
    have h1 := hc 1
    have h2 := hc 2
    simp [coordField, vq, idc, Params.γ] at h1 h2
    refine ⟨by linarith, ?_⟩
    field_simp at h2
    linarith
  · rintro ⟨h1, h2⟩
    have hq : vq p θ0 1 0 = 0 := by simp [vq, idc]; linarith
    apply Dynamics.lift_toLp_eq_zero
    ext i
    fin_cases i
    · simp [coordField, hq]
    · simp [coordField, hq]
    · simp [coordField, idc, Params.γ, h2]; field_simp; ring
    · simp [coordField]

/-- Principal equilibrium branch: `θ₀ = arcsin(−X_g i_{d0}/V₀)`, `|X_g i_{d0}| < V₀`. -/
@[tmio M, powerlib_domain] theorem principal_branch (hV0 : 0 < p.V0)
    (hlt : |p.Xg * p.id0| < p.V0) :
    p.V0 * Real.sin (Real.arcsin (-(p.Xg * p.id0) / p.V0)) = -(p.Xg * p.id0) ∧
      0 < Real.cos (Real.arcsin (-(p.Xg * p.id0) / p.V0)) := by
  have hc : |-(p.Xg * p.id0)| < p.V0 := by rwa [abs_neg]
  exact ⟨SpecialFunctions.mul_sin_arcsin_div hc.le hV0, SpecialFunctions.cos_arcsin_div_pos hc hV0⟩

/-- The note's field is `C¹` off the plane `V = 0` (the PLL–DC model,
`PLLDC.Params.field_contDiffOn`, read through the integrator flip); every operating point lies
there. -/
@[tmio M, powerlib_domain] theorem field_contDiffOn :
    ContDiffOn ℝ 1 (field p) PLLDC.Params.nonzeroVdc := by
  rw [field_eq_transport]
  have hin : ContDiff ℝ 1 (fun y : Dynamics.State 4 => integratorFlip.symm (y - 0)) :=
    integratorFlip.symm.contDiff.comp (contDiff_id.sub contDiff_const)
  have hmaps : Set.MapsTo (fun y : Dynamics.State 4 => integratorFlip.symm (y - 0))
      PLLDC.Params.nonzeroVdc PLLDC.Params.nonzeroVdc := fun y hy => by
    simpa [PLLDC.Params.nonzeroVdc] using hy
  exact integratorFlip.contDiff.comp_contDiffOn
    (p.toPLLDC.field_contDiffOn.comp hin.contDiffOn hmaps)

/-! ## Jacobian -/

/-- Closed-form Jacobian at the state `(θ, x, V, η)` (`V ≠ 0`). -/
def jacGen (θ V η : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-p.kp * p.V0 * Real.cos θ, p.ki, p.kp * p.Xg * p.kpv, p.kp * p.Xg * p.kiv;
     -p.V0 * Real.cos θ, 0, p.Xg * p.kpv, p.Xg * p.kiv;
     -p.γ * p.V0 * Real.sin θ * idc p V η / V, 0,
       p.γ * p.V0 * Real.cos θ * (-p.kpv / V - idc p V η / V ^ 2),
       -p.γ * p.V0 * Real.cos θ * p.kiv / V;
     0, 0, 1, 0]

/-- The source matrix `A₀` (Jacobian at `(θ₀, 0, 1, 0)`). -/
def A0 (θ0 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-p.kp * vd0 p θ0, p.ki, p.kp * p.Xg * p.kpv, p.kp * p.Xg * p.kiv;
     -vd0 p θ0, 0, p.Xg * p.kpv, p.Xg * p.kiv;
     -p.γ * p.V0 * Real.sin θ0 * p.id0, 0, -p.γ * vd0 p θ0 * (p.id0 + p.kpv),
       -p.γ * vd0 p θ0 * p.kiv;
     0, 0, 1, 0]

@[tmio M, powerlib_domain] theorem jacGen_opPoint (θ0 : ℝ) : jacGen p θ0 1 0 = A0 p θ0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jacGen, A0, vd0, idc] <;> first | ring1 | (left; ring1)

/-- The closed-form Jacobian is the PLL–DC model's Jacobian conjugated by the integrator flip, at
every state with `V ≠ 0` (the PLL–DC state `(θ, x, V, −η)`). -/
@[tmio M, powerlib_domain] theorem jacGen_eq_jacobian (y : Dynamics.State 4) (hy : y 2 ≠ 0) :
    jacGen p (y 0) (y 2) (y 3) =
      integratorFlipMatrix * p.toPLLDC.jacobian (integratorFlip y) * integratorFlipMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jacGen, PLLDC.Params.jacobian, Dynamics.signMatrix, Params.toPLLDC, PLLDC.Params.idRef,
      PLLDC.Params.vgd, PLLDC.Params.vgq, PLLDC.Params.pccP, idc, Params.γ, PLLDC.Params.Rg,
      PLLDC.Params.Xg, PLLDC.Params.Cdc, p.line_lossless, -mul_eq_mul_left_iff,
      -mul_eq_mul_right_iff] <;>
    field_simp <;> ring

/-- **The Jacobian of the note's field** at every state with `V ≠ 0` is `jacGen`: the PLL–DC model's
derivative (`PLLDC.Params.hasFDerivAt_field`) read through the integrator flip
(`Dynamics.hasFDerivAt_transportField`, `jacGen_eq_jacobian`). -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_field {y : Dynamics.State 4} (hy : y 2 ≠ 0) :
    HasFDerivAt (field p)
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (jacGen p (y 0) (y 2) (y 3))) y := by
  have hx : integratorFlip y 2 ≠ 0 := by simpa using hy
  have h := Dynamics.hasFDerivAt_transportField integratorFlip 0
    (p.toPLLDC.hasFDerivAt_field hx)
  have hxy : Dynamics.affineCoord integratorFlip 0 (integratorFlip y) = y := by
    apply WithLp.ofLp_injective
    ext i
    fin_cases i <;> simp [Dynamics.affineCoord]
  rw [hxy, ← field_eq_transport] at h
  refine h.congr_fderiv ?_
  rw [jacGen_eq_jacobian p y hy, map_mul, map_mul, Dynamics.signCoord_symm]
  rfl

/-- `A₀` is the PLL–DC model's Jacobian at the operating point conjugated by the integrator flip. -/
@[tmio M, powerlib_domain] theorem A0_eq_jacobian (θ0 : ℝ) :
    A0 p θ0 = integratorFlipMatrix * p.toPLLDC.jacobian (opPoint θ0) * integratorFlipMatrix := by
  have h := jacGen_eq_jacobian p (opPoint θ0) (by simp [opPoint])
  have hflip : integratorFlip (opPoint θ0) = opPoint θ0 := by
    simpa [Dynamics.affineCoord] using affineCoord_opPoint θ0
  rw [hflip] at h
  rw [← jacGen_opPoint, ← h]
  simp [opPoint]

/-- The physical field has the Jacobian `A₀` at the operating point (`hasFDerivAt_field`). -/
@[tmio M, powerlib_domain] theorem fderiv_field_opPoint (θ0 : ℝ) :
    fderiv ℝ (field p) (opPoint θ0) =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (A0 p θ0) := by
  rw [(hasFDerivAt_field p (by simp [opPoint] : (opPoint θ0) 2 ≠ 0)).fderiv, ← jacGen_opPoint]
  simp [opPoint]

/-! ## Amplitude modulation: `A₁` and `b₁` -/

/-- The same model with the ac amplitude scaled by `1 + ε`. -/
def modulated (ε : ℝ) : Params := { p with V0 := p.V0 * (1 + ε) }

/-- `A₁ = ∂A/∂ε` for `V₀ ↦ V₀(1 + ε)`. -/
def A1 (θ0 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-p.kp * vd0 p θ0, 0, 0, 0;
     -vd0 p θ0, 0, 0, 0;
     -p.γ * p.V0 * Real.sin θ0 * p.id0, 0, -p.γ * vd0 p θ0 * (p.id0 + p.kpv),
       -p.γ * vd0 p θ0 * p.kiv;
     0, 0, 0, 0]

/-- `b₁ = ∂f/∂ε` at the operating point. -/
def b1 (θ0 : ℝ) : Fin 4 → ℝ :=
  ![-p.kp * p.V0 * Real.sin θ0, -p.V0 * Real.sin θ0, Pabs p θ0 1 0 / p.C, 0]

/-- The Jacobian at `z₀` is exactly affine in the modulation depth: `A₀ + ε A₁`. -/
@[tmio M, powerlib_domain] theorem jac_modulated (θ0 ε : ℝ) :
    jacGen (modulated p ε) θ0 1 0 = A0 p θ0 + ε • A1 p θ0 := by
  rw [jacGen_opPoint]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A0, A1, modulated, vd0, Params.γ] <;> ring

@[tmio M, powerlib_domain] theorem hasDerivAt_jac_modulated (θ0 : ℝ) (i j : Fin 4) :
    HasDerivAt (fun ε => jacGen (modulated p ε) θ0 1 0 i j) (A1 p θ0 i j) 0 := by
  simp only [jac_modulated, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (A1 p θ0 i j)).const_add (A0 p θ0 i j)

/-- At an equilibrium, the modulated field at `z₀` is exactly `ε b₁`. -/
@[tmio M, powerlib_domain] theorem coordField_modulated (hC : p.C ≠ 0) {θ0 : ℝ} (h : IsEq p θ0)
    (ε : ℝ) : coordField (modulated p ε) ![θ0, 0, 1, 0] = ε • b1 p θ0 := by
  obtain ⟨h1, h2⟩ := h
  ext i
  fin_cases i
  · simp [coordField, modulated, vq, idc, b1]; linear_combination (-p.kp) * h1
  · simp [coordField, modulated, vq, idc, b1]; linear_combination (-1 : ℝ) * h1
  · simp [coordField, modulated, idc, b1, Pabs, Params.γ, h2]; field_simp; ring
  · simp [coordField, b1]

/-! ## Characteristic polynomial -/

/-- `L_PLL(λ) = λ² + k_p v_{d0} λ + k_i v_{d0}`: the PLL loop polynomial `PLL.loopPoly` at the
amplitude `v_{d0}`. -/
abbrev LPLL (θ0 : ℝ) (s : ℂ) : ℂ := PLL.loopPoly (vd0 p θ0) p.kp p.ki s

/-- The DC-voltage outer loop of the model at `θ₀` (`DCParams`,
`theorem/GridTiedConverter/GFL/DCLink/VoltageControl.lean`): `V_d = (3/2) v_{d0}`, `V_dc* = 1`,
gains `(k_pv, k_iv)`, operating current `I_d0 = i_{d0}` with feedforward `i_ff = i_{d0}`, the
model's DC link. -/
def dcLoop (θ0 : ℝ) : DCParams :=
  ⟨p.dcLink, 3 / 2 * vd0 p θ0, 1, p.kpv, p.kiv, p.id0, p.id0, p.dcLink_lossless, p.dcLink_noInd⟩

/-- `2α_cl`: the negated trace `a K_p + b` of the closed DC loop `dcLoop`
(`DCParams.jacobian_trace`); `2α_cl = γ v_{d0}(i_{d0} + k_pv)` (`twoAlphaCl_eq`). -/
def twoAlphaCl (θ0 : ℝ) : ℝ := (dcLoop p θ0).a * (dcLoop p θ0).Kp + (dcLoop p θ0).b

/-- `ω_cl²`: the determinant `a K_i` of the closed DC loop `dcLoop` (`DCParams.jacobian_det`);
`ω_cl² = γ v_{d0} k_iv` (`omegaClSq_eq`). -/
def omegaClSq (θ0 : ℝ) : ℝ := (dcLoop p θ0).a * (dcLoop p θ0).Ki

@[tmio M, powerlib_domain] theorem twoAlphaCl_eq (θ0 : ℝ) :
    twoAlphaCl p θ0 = p.γ * vd0 p θ0 * (p.id0 + p.kpv) := by
  simp only [twoAlphaCl, dcLoop, DCParams.a, DCParams.b, DCParams.Idc0, DCParams.C, Params.γ,
    Params.C]
  ring

@[tmio M, powerlib_domain] theorem omegaClSq_eq (θ0 : ℝ) :
    omegaClSq p θ0 = p.γ * vd0 p θ0 * p.kiv := by
  simp only [omegaClSq, dcLoop, DCParams.a, DCParams.C, Params.γ, Params.C]
  ring

/-- `L_dc(λ) = λ² + 2α_cl λ + ω_cl²` -/
def Ldc (θ0 : ℝ) (s : ℂ) : ℂ := s ^ 2 + (twoAlphaCl p θ0 : ℂ) * s + (omegaClSq p θ0 : ℂ)

/-- Coupling `Γ = γ X_g² i_{d0}²` -/
def Γc : ℝ := p.γ * p.Xg ^ 2 * p.id0 ^ 2

/-- **The DC block of `A₀` is the closed DC-voltage loop.** The `(V, η)` block of `A₀` is the
Jacobian `[[−(a K_p + b), −a K_i], [1, 0]]` of `dcLoop θ₀` (`DCParams.jacobian`), so
`2α_cl = −A₀[2,2]` and `ω_cl² = −A₀[2,3]`. -/
@[tmio M, powerlib_domain] theorem A0_dcBlock (θ0 : ℝ) :
    (A0 p θ0).submatrix (Fin.addNat · 2) (Fin.addNat · 2) = (dcLoop p θ0).jacobian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A0, DCParams.jacobian, dcLoop, DCParams.a, DCParams.b, DCParams.Idc0, Params.γ,
      -mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring

/-- Characteristic equation of the source:
`det(λI − A₀) = L_PLL(λ) L_dc(λ) − Γ (k_p λ + k_i)(k_pv λ + k_iv)`. -/
@[tmio M, powerlib_domain] theorem det_characteristicMatrix_A0 {θ0 : ℝ}
    (h : p.V0 * Real.sin θ0 = -(p.Xg * p.id0)) (s : ℂ) :
    (Linear.characteristicMatrix (A0 p θ0) s).det =
      LPLL p θ0 s * Ldc p θ0 s -
        (Γc p : ℂ) * ((p.kp : ℂ) * s + p.ki) * ((p.kpv : ℂ) * s + p.kiv) := by
  rw [Criteria.det_characteristicMatrix_fin_four]
  have hA : A0 p θ0 2 0 = p.γ * p.Xg * p.id0 ^ 2 := by
    simp [A0]
    have : p.γ * p.V0 * Real.sin θ0 * p.id0 = p.γ * p.id0 * (p.V0 * Real.sin θ0) := by ring
    rw [this, h]; ring
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_four, Criteria.principalMinorSum2Fin4,
    Criteria.principalMinorSum3Fin4, Criteria.det_fin_four, hA]
  simp [A0, PLL.loopPoly, Ldc, twoAlphaCl_eq, omegaClSq_eq, Γc]
  ring

/-- Exact decoupling at `Γ = 0`: the characteristic polynomial factors as `L_PLL · L_dc`. -/
@[tmio M, powerlib_domain] theorem decoupled_of_Gamma_zero {θ0 : ℝ}
    (h : p.V0 * Real.sin θ0 = -(p.Xg * p.id0)) (hΓ : Γc p = 0) (s : ℂ) :
    (Linear.characteristicMatrix (A0 p θ0) s).det = LPLL p θ0 s * Ldc p θ0 s := by
  rw [det_characteristicMatrix_A0 p h, hΓ]
  push_cast
  ring

/-- Quartic coefficients `a₃, a₂, a₁, a₀` of `det(λI − A₀)`. -/
def a3 (θ0 : ℝ) : ℝ := p.kp * vd0 p θ0 + twoAlphaCl p θ0
/-- `a₂` -/
def a2 (θ0 : ℝ) : ℝ := p.ki * vd0 p θ0 + twoAlphaCl p θ0 * (p.kp * vd0 p θ0) +
  omegaClSq p θ0 - Γc p * p.kp * p.kpv
/-- `a₁` -/
def a1 (θ0 : ℝ) : ℝ := twoAlphaCl p θ0 * (p.ki * vd0 p θ0) + omegaClSq p θ0 * (p.kp * vd0 p θ0) -
  Γc p * (p.kp * p.kiv + p.ki * p.kpv)
/-- `a₀` -/
def a0 (θ0 : ℝ) : ℝ := p.ki * vd0 p θ0 * omegaClSq p θ0 - Γc p * p.ki * p.kiv

@[tmio M, powerlib_domain] theorem det_characteristicMatrix_A0_quartic {θ0 : ℝ}
    (h : p.V0 * Real.sin θ0 = -(p.Xg * p.id0)) (s : ℂ) :
    (Linear.characteristicMatrix (A0 p θ0) s).det =
      s ^ 4 + (a3 p θ0 : ℂ) * s ^ 3 + (a2 p θ0 : ℂ) * s ^ 2 + (a1 p θ0 : ℂ) * s +
        (a0 p θ0 : ℂ) := by
  rw [det_characteristicMatrix_A0 p h]
  simp only [LPLL, PLL.loopPoly, Ldc, a3, a2, a1, a0]
  push_cast
  ring

/-- `a₀ = det A₀ = γ k_i k_iv V₀² cos 2θ₀`. -/
@[tmio M, powerlib_domain] theorem a0_eq {θ0 : ℝ} (h : p.V0 * Real.sin θ0 = -(p.Xg * p.id0)) :
    a0 p θ0 = p.γ * p.ki * p.kiv * p.V0 ^ 2 * Real.cos (2 * θ0) := by
  have hc : Real.cos (2 * θ0) = Real.cos θ0 ^ 2 - Real.sin θ0 ^ 2 := by
    rw [Real.cos_two_mul]; have := Real.sin_sq_add_cos_sq θ0; linarith
  have hs : (p.Xg * p.id0) ^ 2 = (p.V0 * Real.sin θ0) ^ 2 := by rw [h]; ring
  simp only [a0, omegaClSq_eq, Γc, vd0, hc]
  linear_combination (-(p.γ * p.ki * p.kiv)) * hs

@[tmio M, powerlib_domain] theorem det_A0 {θ0 : ℝ} (h : p.V0 * Real.sin θ0 = -(p.Xg * p.id0)) :
    (A0 p θ0).det = p.γ * p.ki * p.kiv * p.V0 ^ 2 * Real.cos (2 * θ0) := by
  have h1 := det_characteristicMatrix_A0_quartic p h 0
  rw [Criteria.det_characteristicMatrix_fin_four] at h1
  simp at h1
  rw [← a0_eq p h]
  exact_mod_cast h1

/-- The Routh condition `a₀ > 0` already encodes `cos 2θ₀ > 0`. -/
@[tmio M, powerlib_domain] theorem cos_two_mul_pos_of_a0_pos (hC : 0 < p.C) (hki : 0 < p.ki)
    (hkiv : 0 < p.kiv) {θ0 : ℝ} (h : p.V0 * Real.sin θ0 = -(p.Xg * p.id0))
    (h0 : 0 < a0 p θ0) : 0 < Real.cos (2 * θ0) := by
  rw [a0_eq p h] at h0
  have hγ : 0 < p.γ := by unfold Params.γ; positivity
  by_contra hc
  push Not at hc
  have : p.γ * p.ki * p.kiv * p.V0 ^ 2 * Real.cos (2 * θ0) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
  linarith


/-- The PLL–DC model's Jacobian at the image of the operating point has the quartic of `A₀` (it is
`A₀` conjugated by the involution `integratorFlipMatrix`, `A0_eq_jacobian`). -/
@[tmio M, powerlib_domain] theorem det_characteristicMatrix_jacobian {θ0 : ℝ}
    (h : p.V0 * Real.sin θ0 = -(p.Xg * p.id0)) (s : ℂ) :
    (Linear.characteristicMatrix (p.toPLLDC.jacobian (opPoint θ0)) s).det =
      s ^ 4 + (a3 p θ0 : ℂ) * s ^ 3 + (a2 p θ0 : ℂ) * s ^ 2 + (a1 p θ0 : ℂ) * s +
        (a0 p θ0 : ℂ) := by
  have hF : integratorFlipMatrix * integratorFlipMatrix = 1 := Dynamics.signMatrix_mul_self _
  have hJ : p.toPLLDC.jacobian (opPoint θ0) =
      integratorFlipMatrix * A0 p θ0 * integratorFlipMatrix := by
    rw [A0_eq_jacobian, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hF, Matrix.one_mul,
      Matrix.mul_assoc, hF, Matrix.mul_one]
  rw [hJ, Linear.characteristicMatrix_conj hF, Matrix.det_conj_of_mul_eq_one
    (Linear.complexify_mul_eq_one hF) (Linear.complexify_mul_eq_one hF)]
  exact det_characteristicMatrix_A0_quartic p h s

/-! ## The four-state models read as the PLL–DC model -/

/-- A four-state GFL model read about a selected angle `θ₀`: the operating point is
`(θ₀, 0, 1, 0)`. -/
structure Model where
  /-- The parameters. -/
  params : Params
  /-- The selected angle `θ₀`. -/
  θ : ℝ

/-- The PLL–DC reading of a four-state model: the PLL–DC system of `toPLLDC` about the
operating point `(θ₀, 0, 1, 0)` (fixed by the integrator flip). The behaviour of a four-state
model is that of its image. -/
def Model.toPLLDC (m : Model) : PLLDC.Model := ⟨m.params.toPLLDC, opPoint m.θ⟩

/-- A flow sentence of the image is the sentence of the note's field at the operating point
(`field_eq_transport`, `Dynamics.holds_transport_iff`). -/
@[tmio TM, powerlib_domain] private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m.toPLLDC ∈ PLLDC.family.den (.flow P) ↔
      P.holds (FourState.field m.params) (opPoint m.θ) := by
  have h : m.toPLLDC ∈ PLLDC.family.den (.flow P) ↔
      P.holds m.params.toPLLDC.field (opPoint m.θ) :=
    Spectral.mem_den_flow_iff_shift (f := fun m : PLLDC.Model => m.p.field)
      (pt := PLLDC.Model.x) PLLDC.family_isAutonomous
  rw [h, field_eq_transport]
  conv_rhs => rw [← affineCoord_opPoint m.θ]
  exact (Dynamics.holds_transport_iff integratorFlip 0 P).symm

/-! ### The PLL–DC model's requirements at the image -/

/-- With `C ≠ 0` the image meets the PLL–DC model's equilibrium requirement exactly when `IsEq`
holds. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem meets_equilibrium_iff (m : Model) (hC : m.params.C ≠ 0) :
    PLLDC.Meets m.toPLLDC .equilibrium ↔ IsEq m.params m.θ := by
  change m.params.toPLLDC.field (opPoint m.θ) = 0 ↔ _
  rw [← field_opPoint_eq_zero_iff, isEq_iff m.params hC]

/-- At a point with `v_q = 0` the image meets the PLL–DC model's 4×4 Routh conditions exactly when
the quartic coefficients of `det(λI − A₀)` meet the quartic Routh conditions
(`det_characteristicMatrix_jacobian`, `Criteria.routhFin4_iff_of_det_characteristicMatrix_quartic`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem meets_routh_iff (m : Model)
    (h : m.params.V0 * Real.sin m.θ = -(m.params.Xg * m.params.id0)) :
    PLLDC.Meets m.toPLLDC .routh ↔ 0 < a3 m.params m.θ ∧ 0 < a1 m.params m.θ ∧
      0 < a0 m.params m.θ ∧ a1 m.params m.θ ^ 2 + a3 m.params m.θ ^ 2 * a0 m.params m.θ <
        a3 m.params m.θ * a2 m.params m.θ * a1 m.params m.θ :=
  Criteria.routhFin4_iff_of_det_characteristicMatrix_quartic _
    (det_characteristicMatrix_jacobian m.params h)

/-- At a point with `v_q = 0` the image meets the PLL–DC model's negative-determinant requirement
exactly when `a₀ < 0`. Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem meets_detNeg_iff (m : Model)
    (h : m.params.V0 * Real.sin m.θ = -(m.params.Xg * m.params.id0)) :
    PLLDC.Meets m.toPLLDC .detNeg ↔ a0 m.params m.θ < 0 := by
  obtain ⟨-, -, -, hd⟩ := Criteria.coeffs_of_det_characteristicMatrix_quartic _
    (det_characteristicMatrix_jacobian m.params h)
  change (m.params.toPLLDC.jacobian (opPoint m.θ)).det < 0 ↔ _
  rw [hd]

/-- At a point with `v_q = 0` the image is off the PLL–DC model's Routh boundary exactly when the
quartic of `A₀` meets the quartic Routh conditions or violates them strictly
(`Criteria.routhViolationFin4_iff_of_det_characteristicMatrix_quartic`).
Static evidence on the model, not a connection conclusion. -/
@[tmio M, powerlib_domain] theorem meets_offBoundary_iff (m : Model)
    (h : m.params.V0 * Real.sin m.θ = -(m.params.Xg * m.params.id0)) :
    PLLDC.Meets m.toPLLDC .offBoundary ↔
      (0 < a3 m.params m.θ ∧ 0 < a1 m.params m.θ ∧ 0 < a0 m.params m.θ ∧
        a1 m.params m.θ ^ 2 + a3 m.params m.θ ^ 2 * a0 m.params m.θ <
          a3 m.params m.θ * a2 m.params m.θ * a1 m.params m.θ) ∨
      (a3 m.params m.θ < 0 ∨ a2 m.params m.θ < 0 ∨ a1 m.params m.θ < 0 ∨ a0 m.params m.θ < 0 ∨
        a3 m.params m.θ * a2 m.params m.θ * a1 m.params m.θ <
          a1 m.params m.θ ^ 2 + a3 m.params m.θ ^ 2 * a0 m.params m.θ) :=
  Iff.or (meets_routh_iff m h)
    (Criteria.routhViolationFin4_iff_of_det_characteristicMatrix_quartic _
      (det_characteristicMatrix_jacobian m.params h))

/-- Without capacitance the DC row of the PLL–DC model's Jacobian at the image vanishes
(`x / 0 = 0`), so its determinant is zero. -/
@[tmio M, powerlib_domain] private theorem det_jacobian_eq_zero_of_C_eq_zero {m : Model}
    (hC : m.params.C = 0) : (m.params.toPLLDC.jacobian (opPoint m.θ)).det = 0 := by
  have hC' : m.params.dcLink.C = 0 := hC
  refine Matrix.det_eq_zero_of_row_eq_zero 2 fun j => ?_
  fin_cases j <;> simp [PLLDC.Params.jacobian, Params.toPLLDC, PLLDC.Params.Cdc, hC']

/-! ### Local exponential stability of the operating point -/

/-- Four-state GFL (PLL + dc-voltage loop): the quartic Routh–Hurwitz conditions on the
coefficients of `det(λI − A₀)` at an equilibrium place the PLL–DC image in local exponential
stability (`PLLDC.mem_den_locallyExponentiallyStable_iff`, `meets_routh_iff`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_of_routh (p : Params)
    (hC : p.C ≠ 0) {θ0 : ℝ} (heq : IsEq p θ0) (h3 : 0 < a3 p θ0) (h1 : 0 < a1 p θ0)
    (h0 : 0 < a0 p θ0) (hg : a1 p θ0 ^ 2 + a3 p θ0 ^ 2 * a0 p θ0 < a3 p θ0 * a2 p θ0 * a1 p θ0) :
    connection% ((Model.mk p θ0).toPLLDC ∈
      PLLDC.family.den (.flow .locallyExponentiallyStable)) := by
  have h := PLLDC.mem_den_locallyExponentiallyStable_iff (Model.mk p θ0).toPLLDC
    (by simp [Model.toPLLDC, opPoint])
  unfold powerlib.TMIO.Statement at h ⊢
  rw [h]
  exact ⟨(meets_equilibrium_iff ⟨p, θ0⟩ hC).mpr heq,
    (meets_routh_iff ⟨p, θ0⟩ heq.1).mpr ⟨h3, h1, h0, hg⟩⟩

/-- **Local exponential stability of a four-state model.** The PLL–DC image is locally
exponentially stable exactly when the operating point is an equilibrium (`IsEq`, `C ≠ 0`) whose
quartic `det(λI − A₀)` meets the Routh conditions: the PLL–DC model's converse linearization off the
singular plane (`PLLDC.mem_den_locallyExponentiallyStable_iff`) read through
`meets_equilibrium_iff` and `meets_routh_iff`; with `C = 0` the determinant vanishes, which the
Routh conditions exclude. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff (m : Model) :
    connection% (m.toPLLDC ∈ PLLDC.family.den (.flow .locallyExponentiallyStable) ↔
      m ∈ {m : Model | IsEq m.params m.θ ∧ m.params.C ≠ 0 ∧ 0 < a3 m.params m.θ ∧
        0 < a1 m.params m.θ ∧ 0 < a0 m.params m.θ ∧
        a1 m.params m.θ ^ 2 + a3 m.params m.θ ^ 2 * a0 m.params m.θ <
          a3 m.params m.θ * a2 m.params m.θ * a1 m.params m.θ}) := by
  have h := PLLDC.mem_den_locallyExponentiallyStable_iff m.toPLLDC
    (by simp [Model.toPLLDC, opPoint])
  unfold powerlib.TMIO.Statement at h ⊢
  rw [h]
  constructor
  · rintro ⟨he, hr⟩
    have hC : m.params.C ≠ 0 := fun hC => by
      obtain ⟨-, -, hdet, -⟩ := hr
      have h0 := det_jacobian_eq_zero_of_C_eq_zero hC
      change 0 < (m.params.toPLLDC.jacobian (opPoint m.θ)).det at hdet
      rw [h0] at hdet
      exact lt_irrefl _ hdet
    have heq : IsEq m.params m.θ := (meets_equilibrium_iff m hC).mp he
    exact ⟨heq, hC, (meets_routh_iff m heq.1).mp hr⟩
  · rintro ⟨heq, hC, hr⟩
    exact ⟨(meets_equilibrium_iff m hC).mpr heq, (meets_routh_iff m heq.1).mpr hr⟩

/-! ### Instability of the operating point -/

/-- `a₀ < 0` at an equilibrium gives a positive real eigenvalue and instability of the PLL–DC
image (`PLLDC.mem_den_unstable_of_det_neg`, `meets_detNeg_iff`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_a0_neg (p : Params) (hC : p.C ≠ 0)
    {θ0 : ℝ} (heq : IsEq p θ0) (h0 : a0 p θ0 < 0) :
    connection% ((Model.mk p θ0).toPLLDC ∈ PLLDC.family.den (.flow .unstable)) :=
  PLLDC.mem_den_unstable_of_det_neg _ (by norm_num [Model.toPLLDC, Params.toPLLDC])
    ((meets_equilibrium_iff ⟨p, θ0⟩ hC).mpr heq) ((meets_detNeg_iff ⟨p, θ0⟩ heq.1).mpr h0)

/-- Four-state GFL: `cos 2θ₀ < 0` (operating angle beyond 45°) gives `a₀ = det A₀ < 0`, a
positive real eigenvalue, and instability, for all positive `C, k_i, k_iv`. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_cos_two_mul_neg (p : Params)
    (hC : 0 < p.C) (hki : 0 < p.ki) (hkiv : 0 < p.kiv) (hV0 : p.V0 ≠ 0) {θ0 : ℝ}
    (heq : IsEq p θ0) (hcos : Real.cos (2 * θ0) < 0) :
    connection% ((Model.mk p θ0).toPLLDC ∈ PLLDC.family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  have hγ : 0 < p.γ := by unfold Params.γ; positivity
  refine mem_den_unstable_of_a0_neg p hC.ne' heq ?_
  rw [a0_eq p heq.1]
  have : 0 < p.γ * p.ki * p.kiv * p.V0 ^ 2 := by positivity
  nlinarith

/-- Beyond 45° (`cos 2θ₀ < 0`) the operating point is not Lyapunov stable. -/
@[tmio TM, powerlib_domain] theorem not_mem_den_lyapunovStable_of_cos_two_mul_neg (p : Params)
    (hC : 0 < p.C) (hki : 0 < p.ki) (hkiv : 0 < p.kiv) (hV0 : p.V0 ≠ 0) {θ0 : ℝ}
    (heq : IsEq p θ0) (hcos : Real.cos (2 * θ0) < 0) :
    connection% ((Model.mk p θ0).toPLLDC ∉ PLLDC.family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.not_mem_den_lyapunovStable_of_unstable
    (mem_den_unstable_of_cos_two_mul_neg p hC hki hkiv hV0 heq hcos)

/-- Necessary condition (`cos 2θ₀ ≥ 0`, in contrapositive form): if `cos 2θ₀ < 0` the operating
point is not locally exponentially stable, i.e. local exponential stability forces
`cos 2θ₀ ≥ 0` (`|θ₀| ≤ 45°` on the principal branch). -/
@[tmio TM, powerlib_domain] theorem not_mem_den_locallyExponentiallyStable_of_cos_two_mul_neg
    (p : Params) (hC : 0 < p.C) (hki : 0 < p.ki) (hkiv : 0 < p.kiv) (hV0 : p.V0 ≠ 0) {θ0 : ℝ}
    (heq : IsEq p θ0) (hcos : Real.cos (2 * θ0) < 0) :
    connection% ((Model.mk p θ0).toPLLDC ∉
      PLLDC.family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have h := not_mem_den_lyapunovStable_of_cos_two_mul_neg p hC hki hkiv hV0 heq hcos
  unfold powerlib.TMIO.Statement at h
  exact fun hs => h (Spectral.den_locallyExponentiallyStable_subset_lyapunovStable hs)

/-! ## Grid-angle input in error-angle coordinates -/

/-- Field with the grid angle `u = θ_g` and its rate `u̇` as inputs; in error-angle
coordinates `u` itself does not appear and `u̇` enters only `θ̇`. -/
def fieldAngle (_u ud : ℝ) (z : Dynamics.State 4) : Dynamics.State 4 :=
  field p z - ud • WithLp.toLp 2 ![1, 0, 0, 0]

/-- `f_u = 0`, `f_{u̇} = −e_θ`: the input is purely additive. -/
@[tmio M, powerlib_domain] theorem fieldAngle_indep_angle (u u' ud : ℝ) :
    fieldAngle p u ud = fieldAngle p u' ud := rfl

/-- `A₁^GFL = 0`: the state Jacobian does not depend on the grid-angle input. -/
@[tmio M, powerlib_domain] theorem fderiv_fieldAngle (u ud : ℝ) (z : Dynamics.State 4) :
    fderiv ℝ (fieldAngle p u ud) z = fderiv ℝ (field p) z := by
  unfold fieldAngle
  exact fderiv_sub_const _

/-- The derivative of the state Jacobian with respect to the grid angle is zero. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_jacobian_angle (ud : ℝ) (z : Dynamics.State 4)
    (u : ℝ) : HasDerivAt (fun u => fderiv ℝ (fieldAngle p u ud) z) 0 u := by
  show HasDerivAt (fun _ : ℝ => fderiv ℝ (fieldAngle p 0 ud) z) 0 u
  exact hasDerivAt_const u _

/-! ### Instability away from equilibrium -/

/-- An unbalanced model: no ac source (`V₀ = 0`), unit capacitance and dc source current, all
gains and references zero, at `θ₀ = 0`; the dc-bus voltage ramps, `V̇ = I_dc0 / C = 1`. -/
def offEquilibrium : Model := ⟨⟨0, ⟨0, 0, 0⟩, 0, 0, 0, 0, 0, ⟨0, 1, 0⟩, 1, rfl, rfl, rfl⟩, 0⟩

/-- The image of `offEquilibrium` is not an equilibrium: its DC-link component is `1`. -/
@[tmio M, powerlib_domain] private theorem offEquilibrium_field_ne_zero :
    offEquilibrium.toPLLDC.p.field offEquilibrium.toPLLDC.x ≠ 0 := fun h => by
  have := congrArg (fun y : Dynamics.State 4 => y 2) h
  simp [Model.toPLLDC, offEquilibrium, opPoint, Params.toPLLDC, PLLDC.Params.field,
    PLLDC.Params.Cdc, PLLDC.Params.idRef, PLLDC.Params.vgd, PLLDC.Params.vgq] at this

/-- A point that is not an equilibrium is unstable: the PLL–DC image of `offEquilibrium`
(`V_dc* = 1`, off the singular plane) leaves its point
(`PLLDC.mem_den_unstable_of_field_ne_zero`). -/
@[tmio TM, powerlib_domain] theorem offEquilibrium_mem_den_unstable :
    connection% (offEquilibrium.toPLLDC ∈ PLLDC.family.den (.flow .unstable)) :=
  PLLDC.mem_den_unstable_of_field_ne_zero _ (by simp [Model.toPLLDC, opPoint])
    offEquilibrium_field_ne_zero

end powerlib.GFL.DCLink.FourState
