import theorem.GridTiedConverter.GFM.DCLink.OpenLoop
import theorem.GridTiedConverter.GFM.Line.VSM

/-! # The DC-voltage plant `ΔV/ΔP_ref` of the VSM with a DC link: quasi-static and dynamic line

The small-signal plant from the power reference of the VSM to the DC-link voltage, DC-voltage loop
open, for two line models: the quasi-static line of
`theorem/GridTiedConverter/GFM/DCLink/OpenLoop.lean` (no finite zero) and the dynamic R–L line of
`theorem/GridTiedConverter/GFM/Line/Model.lean` (a right-half-plane zero exactly when the operating
point exports reactive power below `E² X/|Z|²`).

Model boundary.
* Quasi-static line: the open-loop plant `Plant` of `OpenLoop.lean` (state `(δ, ω, V)`,
  `P_e(δ) = c₀ + A sin(δ − α)`, DC node `C V̇ = (P_s + I_s V − P_e(δ))/V`) with the power
  reference `P_ff` read as the input; small-signal plant `Plant.refPlant δ V` at `(δ, 0, V)`.
* Dynamic line: `DynamicLine`, the line VSM `Line.VSM` of `Line/Model.lean` (dq frame rotating at
  `ω₀` aligned with the stiff grid `V_g ∠ 0`; line `L i̇ = E e^{jδ} − V_g − (R + jX) i`,
  `X = ω₀ L`; export current, `P_e + j Q_e = E e^{jδ} conj i`; constant EMF magnitude `E`) with
  the DC link of `OpenLoop.lean` (`C V̇ = (P_s + I_s V − P_e)/V`, the DC-node law
  `GFL.DCLink.nodeRate`). State `(δ, ω, i_d, i_q, V) : Dynamics.State 5`, in this order; input
  the power reference `r` (`δ̇ = ω`, `M ω̇ = r − P_e − D ω`); output `V`. Small-signal plant
  `DynamicLine.model δ V` at the operating point `(δ*, 0, i_s(δ*), V*)`, an equilibrium when
  balanced (`DynamicLine.field_point_of_balance`).
* Signs: active and reactive power export-positive (the GFM convention of
  `theorem/GridTiedConverter/GFM/VSMLPF.lean`); source power positive into the DC node.
* Continuous time, constant parameters, constant input at the operating point. Excluded: the
  DC-voltage loop (`theorem/GridTiedConverter/GFM/DCLink/VSMDC.lean`), reactive-power and amplitude
  loops, inner voltage and current loops, LC filter, limits, PLL, delay, PWM, DC-link losses.
* Level: linearization (Jacobian by `fderiv`, input column by `HasDerivAt`), the transfer
  `C (sI − A)⁻¹ B + D` (`Linear.transfer`) and its zeros. No behavioural conclusion is drawn.

Source: GFM counterpart study, note T7 part (b) (`t7-dcside`: the dynamic-line transfer and the
zero criterion, checked numerically there; notes outside the repository); the GFL counterpart is
the rectifier zero `GFL.DCLink.bridgeZero_pos_iff` (`theorem/GridTiedConverter/GFL/DCLink/`
`PowerBalance.lean`, transfer in `Cascade.lean`); the line-VSM characteristic polynomial
`Line.VSM.characteristic_polynomial` (`theorem/GridTiedConverter/GFM/Line/VSM.lean`); the
quadratic root facts `Criteria.quadratic_root_re`, `Criteria.quadratic_root_im`,
`Criteria.exists_quadratic_root_pos_of_const_neg` (`theorem/Criteria/Hurwitz2.lean`).

Results.
* Quasi-static line: `Plant.hasDerivAt_openField_Pff` (input column);
  `Plant.transfer_refPlant`: `ΔV/ΔP_ff = −(k/(C V)) / ((M s² + D s + k)(s − j))`,
  `k = P_e'(δ)`, `j = Plant.nodeSlope δ V`; `Plant.transfer_refPlant_ne_zero`: for `k ≠ 0` it has
  no finite zero.
* Dynamic line, angle to power: `DynamicLine.anglePlant`, whose matrices are the derivatives of
  the line rates and of `P_e` (`DynamicLine.hasFDerivAt_line`);
  `DynamicLine.transfer_anglePlant`: `ΔP_e/Δδ = G(s) = −Q_e + E² X/((R + L s)² + X²)`
  (`DynamicLine.angleGain`; numerator `DynamicLine.zeroPoly`, `DynamicLine.angleGain_eq_div`);
  `DynamicLine.angleGain_zero`: `G(0) = K(δ)`, the quasi-steady synchronizing coefficient.
* Dynamic line, the plant: `DynamicLine.hasFDerivAt_field`, `DynamicLine.fderiv_point`,
  `DynamicLine.hasDerivAt_field_ref`; `DynamicLine.det_characteristicMatrix_jacobian` (block
  triangular), `DynamicLine.det_characteristicMatrix_model` and
  `DynamicLine.det_characteristicMatrix_model_eq_mul`:
  `M L² det(sI − A) = ((R + L s)² + X²)(M s² + D s + G(s))(s − j)`, `j = DynamicLine.dcPole`
  (`I_s/(C V*)` at balance, `DynamicLine.dcPole_of_balance`).
* `DynamicLine.transfer_model`: `ΔV/ΔP_ref = −G(s) / (C V* (s − j)(M s² + D s + G(s)))`;
  `DynamicLine.transfer_model_eq_zero_iff`: off the poles it vanishes exactly at the roots of
  `E² X − Q ((R + L s)² + X²)`, `Q = Q(δ*)`.
* `DynamicLine.exists_zeroPoly_eq_zero_re_pos_iff`: that numerator has a root with `Re s > 0`
  iff `0 < Q < κ = E² X/|Z|²` (`E ≠ 0`, `X > 0`, `R ≥ 0`, `L > 0`; `zeroPoly_eq_neg_mul`,
  `lineDen_ne_zero_of_re_pos`). `DynamicLine.exists_transfer_model_eq_zero_re_pos_iff`: for a
  physical network, `M > 0`, `D ≥ 0`, `C, V* ≠ 0`, and no cancellation by a DC pole `j > 0` at
  the zero, `ΔV/ΔP_ref` has a zero with `Re s > 0` that is not a pole iff `0 < Q(δ*) < κ`,
  whatever the sign of the active power (the GFL rectifier zero needs `I_d0 > 0`); on the stable
  branch `K(δ*) > 0` iff `Q(δ*) > 0`
  (`DynamicLine.exists_transfer_model_eq_zero_re_pos_iff_of_syncCoeff_pos`).

Family and connection conclusions.
The module defines no family and states no behaviour: every result is static evidence on the
two small-signal plants. The two line models are not related here (no reduction statement);
`DynamicLine.angleGain_zero` compares two quantities of the same dynamic line.
-/

noncomputable section
namespace powerlib.GFM.DCLink
open Matrix Filter
open powerlib.Dynamics (State coord hasFDerivAt_coord hasFDerivAt_toEuclideanCLM_of_components)

/-! ## The quasi-static line: no finite zero -/

namespace Plant

variable (q : Plant)

/-- The small-signal plant of the open loop from the power reference `ΔP_ff` to the DC voltage
`ΔV`, at the angle `δ` and the DC voltage `V`: state `(Δδ, Δω, ΔV)`, state matrix the Jacobian
`openJacobian δ V` (`Plant.hasFDerivAt_openField`), input column `∂f/∂P_ff = (0, 1/M, 0)`
(`Plant.hasDerivAt_openField_Pff`), output `ΔV`. -/
def refPlant (δ V : ℝ) : Linear.Plant 3 1 :=
  ⟨q.openJacobian δ V, !![0; 1 / q.M; 0], !![0, 0, 1], !![0]⟩

/-- The input column of `refPlant` is the derivative of the open-loop field in the power
reference `P_ff`. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_openField_Pff (x : State 3) (k : Fin 3) :
    HasDerivAt (fun r => ({ q with Pff := r } : Plant).openField x k)
      ((q.refPlant (x 0) (x 2)).B k 0) q.Pff := by
  fin_cases k
  · simpa [openField, refPlant] using hasDerivAt_const q.Pff (x 1)
  · have h := (((hasDerivAt_id q.Pff).sub_const (q.Pe (x 0))).sub_const (q.D * x 1)).div_const q.M
    convert h using 1
    · funext r
      simp [openField, swingRate, Pe]
    · simp [refPlant]
  · simpa [openField, refPlant, nodeRate, Pe] using
      hasDerivAt_const q.Pff (q.nodeRate (x 0) (x 2))

/-- **Quasi-static line, the transfer `ΔV/ΔP_ff`.** Off the poles,
`ΔV/ΔP_ff = −(k/(C V)) / ((M s² + D s + k)(s − j))`, `k = k(δ)`, `j = nodeSlope δ V`; the
denominator is `M det(sI − J)` (`Plant.det_characteristicMatrix_openJacobian`) and the numerator
is a constant. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem transfer_refPlant (hM : q.M ≠ 0) (hC : q.C ≠ 0) {δ V : ℝ}
    (hV : V ≠ 0) {s : ℂ} (hs : (Linear.characteristicMatrix (q.openJacobian δ V) s).det ≠ 0) :
    Linear.transfer (q.refPlant δ V) s 0 0 =
      -((q.k δ / (q.C * V) : ℝ) : ℂ) /
        (((q.M : ℂ) * s ^ 2 + q.D * s + q.k δ) * (s - q.nodeSlope δ V)) := by
  have hfac := q.det_characteristicMatrix_openJacobian δ V s
  have hM' : (q.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hC' : (q.C : ℂ) ≠ 0 := by exact_mod_cast hC
  have hV' : (V : ℂ) ≠ 0 := by exact_mod_cast hV
  obtain ⟨P, hP⟩ : ∃ P : ℂ, P = (q.M : ℂ) * s ^ 2 + q.D * s + q.k δ := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℂ, e = s - q.nodeSlope δ V := ⟨_, rfl⟩
  have hsw : (Linear.characteristicMatrix (q.swingJacobian δ) s).det = P / q.M := by
    simp [Linear.characteristicMatrix, swingJacobian, Matrix.det_fin_two, hP]
    field_simp
    ring
  have hfac' : (Linear.characteristicMatrix (q.openJacobian δ V) s).det = P / q.M * e := by
    rw [hfac, hsw, he]
    push_cast
    ring
  have hP0 : P ≠ 0 := fun h => hs (by rw [hfac', h, zero_div, zero_mul])
  have he0 : e ≠ 0 := fun h => hs (by rw [hfac', h, mul_zero])
  set Mx := Linear.characteristicMatrix (q.refPlant δ V).A s with hMx
  set X : Matrix (Fin 3) (Fin 1) ℂ :=
    !![1 / P; s / P; -((q.k δ : ℂ) / (q.C * V)) / (P * e)] with hX
  have hdet : Mx.det ≠ 0 := hs
  have hMX : Mx * X = Linear.complexify (q.refPlant δ V).B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hMx, hX, Linear.characteristicMatrix, refPlant, openJacobian, Matrix.mul_apply,
        Fin.sum_univ_three] <;>
      field_simp <;> (try simp only [hP, he]) <;> ring
  have hsol : Mx⁻¹ * Linear.complexify (q.refPlant δ V).B = X := by
    rw [← hMX, Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.mpr hdet)]
  rw [Linear.transfer, ← hMx, Matrix.mul_assoc, hsol, ← hP, ← he]
  simp [hX, refPlant, Matrix.mul_apply, Fin.sum_univ_three]

/-- **The quasi-static line has no finite zero.** With `k(δ) ≠ 0` (`M, C, V ≠ 0`) the transfer
`ΔV/ΔP_ff` vanishes at no `s` that is not a pole. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem transfer_refPlant_ne_zero (hM : q.M ≠ 0) (hC : q.C ≠ 0)
    {δ V : ℝ} (hk : q.k δ ≠ 0) (hV : V ≠ 0) {s : ℂ}
    (hs : (Linear.characteristicMatrix (q.openJacobian δ V) s).det ≠ 0) :
    Linear.transfer (q.refPlant δ V) s 0 0 ≠ 0 := by
  rw [q.transfer_refPlant hM hC hV hs]
  refine div_ne_zero (neg_ne_zero.mpr (by exact_mod_cast div_ne_zero hk (mul_ne_zero hC hV)))
    fun h => hs ?_
  rw [q.det_characteristicMatrix_openJacobian δ V s]
  have hsw : (Linear.characteristicMatrix (q.swingJacobian δ) s).det =
      ((q.M : ℂ) * s ^ 2 + q.D * s + q.k δ) / q.M := by
    have hM' : (q.M : ℂ) ≠ 0 := by exact_mod_cast hM
    simp [Linear.characteristicMatrix, swingJacobian, Matrix.det_fin_two]
    field_simp
    ring
  rw [hsw, show s + ((-q.nodeSlope δ V : ℝ) : ℂ) = s - q.nodeSlope δ V by push_cast; ring,
    div_mul_eq_mul_div, h, zero_div]

end Plant

/-! ## The dynamic line -/

/-- The VSM with a DC link on the dynamic R–L line: the line VSM (`Line.VSM`: network
`E, V_g, R, L, ω₀`, inertia `M`, damping `D`, set-point `P_ref`) and the DC link (capacitance
`C`, affine source `P_src(V) = P_s + I_s V`). -/
structure DynamicLine extends Line.VSM where
  /-- DC-link capacitance `C`. -/
  C : ℝ
  /-- Constant part `P_s` of the DC source. -/
  Ps : ℝ
  /-- Current part `I_s` of the DC source. -/
  Is : ℝ

namespace DynamicLine

variable (g : DynamicLine)

/-! ### The line from the angle to the exported power -/

/-- The small-signal line from the angle `Δδ` to the exported power `ΔP_e`, at the angle `δ` and
the line current `(i_d, i_q)`: state `(Δi_d, Δi_q)`, `A = [[−R/L, X/L], [−X/L, −R/L]]`,
`B = (−E sin δ, E cos δ)/L`, `C = (E cos δ, E sin δ)`, `D = −Q_e`. Its matrices are the partial
derivatives of the line rates and of `P_e` (`DynamicLine.hasFDerivAt_line`). -/
def anglePlant (δ id iq : ℝ) : Linear.Plant 2 1 :=
  ⟨!![-g.R / g.L, g.X / g.L; -g.X / g.L, -g.R / g.L],
    !![-(g.E * Real.sin δ) / g.L; g.E * Real.cos δ / g.L],
    !![g.E * Real.cos δ, g.E * Real.sin δ], !![-g.reactive δ id iq]⟩

/-- The angle plant is the linearization of the line: on the coordinates `(δ, i_d, i_q)`, the
derivatives of the line rates `i̇_d, i̇_q` have the entries of `B` (on `δ`) and `A` (on the
current), and that of `P_e` has `D` (on `δ`, `∂P_e/∂δ = −Q_e`) and `C` (on the current). -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_line (x : State 3) :
    HasFDerivAt (fun y : State 3 => g.rateD (y 0) (y 1) (y 2))
        ((g.anglePlant (x 0) (x 1) (x 2)).B 0 0 • coord 0 +
          (g.anglePlant (x 0) (x 1) (x 2)).A 0 0 • coord 1 +
          (g.anglePlant (x 0) (x 1) (x 2)).A 0 1 • coord 2) x ∧
      HasFDerivAt (fun y : State 3 => g.rateQ (y 0) (y 1) (y 2))
        ((g.anglePlant (x 0) (x 1) (x 2)).B 1 0 • coord 0 +
          (g.anglePlant (x 0) (x 1) (x 2)).A 1 0 • coord 1 +
          (g.anglePlant (x 0) (x 1) (x 2)).A 1 1 • coord 2) x ∧
      HasFDerivAt (fun y : State 3 => g.power (y 0) (y 1) (y 2))
        ((g.anglePlant (x 0) (x 1) (x 2)).D 0 0 • coord 0 +
          (g.anglePlant (x 0) (x 1) (x 2)).C 0 0 • coord 1 +
          (g.anglePlant (x 0) (x 1) (x 2)).C 0 1 • coord 2) x :=
  ⟨by simpa [anglePlant] using g.hasFDerivAt_rateD 0 1 2 x,
    by simpa [anglePlant] using g.hasFDerivAt_rateQ 0 1 2 x,
    by simpa [anglePlant] using g.hasFDerivAt_power 0 1 2 x⟩

/-- `(R + L s)² + X²`, the line factor (`L² det(sI − A)` of the angle plant). -/
def lineDen (s : ℂ) : ℂ := ((g.R : ℂ) + g.L * s) ^ 2 + (g.X : ℂ) ^ 2

/-- The angle-to-power gain `−Q + E² X / ((R + L s)² + X²)` at the reactive power `Q`. -/
def angleGain (Q : ℝ) (s : ℂ) : ℂ := -(Q : ℂ) + (g.E : ℂ) ^ 2 * g.X / g.lineDen s

/-- Its numerator `E² X − Q ((R + L s)² + X²)`. -/
def zeroPoly (Q : ℝ) (s : ℂ) : ℂ := (g.E : ℂ) ^ 2 * g.X - Q * g.lineDen s

@[tmio M, powerlib_domain] theorem angleGain_eq_div {Q : ℝ} {s : ℂ} (hs : g.lineDen s ≠ 0) :
    g.angleGain Q s = g.zeroPoly Q s / g.lineDen s := by
  rw [angleGain, zeroPoly]
  field_simp
  ring

/-- **`ΔP_e/Δδ` of the dynamic line.** Off the line poles (`(R + L s)² + X² ≠ 0`, `L ≠ 0`),
the transfer of the angle plant is `−Q_e + E² X / ((R + L s)² + X²)`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem transfer_anglePlant (hL : g.L ≠ 0) (δ id iq : ℝ) {s : ℂ}
    (hs : g.lineDen s ≠ 0) :
    Linear.transfer (g.anglePlant δ id iq) s 0 0 = g.angleGain (g.reactive δ id iq) s := by
  have hL' : (g.L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hcs : Complex.cos (δ : ℂ) ^ 2 + Complex.sin (δ : ℂ) ^ 2 = 1 := Complex.cos_sq_add_sin_sq _
  set u : ℂ := g.E * (g.X * Complex.cos δ - (g.R + g.L * s) * Complex.sin δ) / g.lineDen s
    with hu
  set w : ℂ := g.E * ((g.R + g.L * s) * Complex.cos δ + g.X * Complex.sin δ) / g.lineDen s
    with hw
  set Mx := Linear.characteristicMatrix (g.anglePlant δ id iq).A s with hMx
  set X : Matrix (Fin 2) (Fin 1) ℂ := !![u; w] with hX
  have hdet : Mx.det ≠ 0 := by
    have h : Mx.det = g.lineDen s / (g.L : ℂ) ^ 2 := by
      simp [hMx, Linear.characteristicMatrix, anglePlant, Matrix.det_fin_two, lineDen]
      field_simp
      ring
    rw [h]
    exact div_ne_zero hs (pow_ne_zero 2 hL')
  have hMX : Mx * X = Linear.complexify (g.anglePlant δ id iq).B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hMx, hX, Linear.characteristicMatrix, anglePlant, Matrix.mul_apply,
        Fin.sum_univ_two, hu, hw] <;>
      field_simp <;> simp only [lineDen] <;> ring
  have hsol : Mx⁻¹ * Linear.complexify (g.anglePlant δ id iq).B = X := by
    rw [← hMX, Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.mpr hdet)]
  rw [Linear.transfer, ← hMx, Matrix.mul_assoc, hsol]
  simp [hX, anglePlant, Matrix.mul_apply, Fin.sum_univ_two, angleGain, hu, hw]
  field_simp
  linear_combination (g.E : ℂ) ^ 2 * g.X * hcs


/-! ### The five-state model -/

/-- The field on `(δ, ω, i_d, i_q, V)` at the power reference `r`: the line VSM
(`Line.VSM.field` with `P_ref = r`) and the DC node `V̇ = (I_s + (P_s − P_e)/V)/C`
(`GFL.DCLink.nodeRate`, node power `P_s − P_e`, `P_e = Line.Network.power`). -/
def field (r : ℝ) (x : State 5) : State 5 :=
  WithLp.toLp 2 ![x 1, (r - g.power (x 0) (x 2) (x 3) - g.D * x 1) / g.M,
    g.rateD (x 0) (x 2) (x 3), g.rateQ (x 0) (x 2) (x 3),
    GFL.DCLink.nodeRate g.C g.Is (g.Ps - g.power (x 0) (x 2) (x 3)) (x 4)]

/-- The DC-node slope `∂V̇/∂V = (P_e − P_s)/(C V²)` at the exported power `P_e`. -/
def nodeSlope (Pe Vdc : ℝ) : ℝ := (Pe - g.Ps) / (g.C * Vdc ^ 2)

/-- The Jacobian at the angle `δ`, the line current `(i_d, i_q)` and the DC voltage `V`: the
line-VSM Jacobian `Line.VSM.jacobian` bordered by the DC row (`DynamicLine.hasFDerivAt_field`). -/
def jacobian (δ id iq Vdc : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 1, 0, 0, 0;
    g.reactive δ id iq / g.M, -g.D / g.M, -(g.E * Real.cos δ) / g.M,
      -(g.E * Real.sin δ) / g.M, 0;
    -(g.E * Real.sin δ) / g.L, 0, -g.R / g.L, g.X / g.L, 0;
    g.E * Real.cos δ / g.L, 0, -g.X / g.L, -g.R / g.L, 0;
    g.reactive δ id iq / (g.C * Vdc), 0, -(g.E * Real.cos δ) / (g.C * Vdc),
      -(g.E * Real.sin δ) / (g.C * Vdc), g.nodeSlope (g.power δ id iq) Vdc]

/-- The Jacobian of the five-state field, computed from the field, wherever `V ≠ 0`. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_field (r : ℝ) {x : State 5} (hx : x 4 ≠ 0) :
    HasFDerivAt (g.field r)
      (Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (g.jacobian (x 0) (x 2) (x 3) (x 4))) x := by
  have hP := g.hasFDerivAt_power 0 2 3 x
  refine hasFDerivAt_toEuclideanCLM_of_components _
    ![coord 1, g.M⁻¹ • (-((-g.reactive (x 0) (x 2) (x 3)) • coord 0 +
        (g.E * Real.cos (x 0)) • coord 2 + (g.E * Real.sin (x 0)) • coord 3) - g.D • coord 1),
      (-(g.E * Real.sin (x 0)) / g.L) • coord 0 + (-g.R / g.L) • coord 2 + (g.X / g.L) • coord 3,
      (g.E * Real.cos (x 0) / g.L) • coord 0 + (-g.X / g.L) • coord 2 + (-g.R / g.L) • coord 3,
      g.C⁻¹ • (0 + (x 4)⁻¹ • -((-g.reactive (x 0) (x 2) (x 3)) • coord 0 +
          (g.E * Real.cos (x 0)) • coord 2 + (g.E * Real.sin (x 0)) • coord 3) -
        ((g.Ps - g.power (x 0) (x 2) (x 3)) / x 4 ^ 2) • coord 4)]
    (fun i => ?_) (fun i v => ?_)
  · fin_cases i
    · exact hasFDerivAt_coord 1 x
    · have h := (((hasFDerivAt_const r x).sub hP).sub
        ((hasFDerivAt_coord 1 x).const_smul g.D)).const_smul g.M⁻¹
      convert h using 1
      · funext y; simp [field, div_eq_inv_mul]
      · simp
    · exact g.hasFDerivAt_rateD 0 2 3 x
    · exact g.hasFDerivAt_rateQ 0 2 3 x
    · exact GFL.DCLink.hasFDerivAt_nodeRate g.C (hasFDerivAt_const g.Is x) (hP.const_sub g.Ps)
        (hasFDerivAt_coord 4 x) hx
  · fin_cases i <;> (simp [jacobian, nodeSlope, Fin.sum_univ_five]; try ring)

/-- The input column `(0, 1/M, 0, 0, 0)`. -/
def inputB : Matrix (Fin 5) (Fin 1) ℝ := !![0; 1 / g.M; 0; 0; 0]

/-- The input column is the derivative of the field in the power reference. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_field_ref (r : ℝ) (x : State 5) (k : Fin 5) :
    HasDerivAt (fun r => g.field r x k) (g.inputB k 0) r := by
  fin_cases k
  · simpa [field, inputB] using hasDerivAt_const r (x 1)
  · have h := (((hasDerivAt_id r).sub_const (g.power (x 0) (x 2) (x 3))).sub_const
      (g.D * x 1)).div_const g.M
    convert h using 1
    · funext r; simp [field]
    · simp [inputB]
  · simpa [field, inputB] using hasDerivAt_const r (g.rateD (x 0) (x 2) (x 3))
  · simpa [field, inputB] using hasDerivAt_const r (g.rateQ (x 0) (x 2) (x 3))
  · simpa [field, inputB] using
      hasDerivAt_const r (GFL.DCLink.nodeRate g.C g.Is (g.Ps - g.power (x 0) (x 2) (x 3)) (x 4))

/-- The operating point `(δ*, 0, i_s(δ*), V*)` (line current at its quasi-steady value). -/
def point (δ Vdc : ℝ) : State 5 := WithLp.toLp 2 ![δ, 0, (g.is δ).re, (g.is δ).im, Vdc]

/-- The small-signal plant from `ΔP_ref` to `ΔV` at the operating point: the Jacobian there
(`DynamicLine.fderiv_point`), the input column (`DynamicLine.hasDerivAt_field_ref`), the output
`ΔV`. -/
def model (δ Vdc : ℝ) : Linear.Plant 5 1 :=
  ⟨g.jacobian δ (g.is δ).re (g.is δ).im Vdc, g.inputB, !![0, 0, 0, 0, 1], !![0]⟩

/-- The DC-node pole `j = (P(δ*) − P_s)/(C V*²)` at the operating point
(`I_s/(C V*)` at balance, `DynamicLine.dcPole_of_balance`). -/
def dcPole (δ Vdc : ℝ) : ℝ := g.nodeSlope (g.qssPower δ) Vdc

@[tmio M, powerlib_domain] theorem dcPole_of_balance {δ Vdc : ℝ} (hV : Vdc ≠ 0)
    (h : g.Ps + g.Is * Vdc = g.qssPower δ) : g.dcPole δ Vdc = g.Is / (g.C * Vdc) := by
  rw [dcPole, nodeSlope, ← h, show g.Ps + g.Is * Vdc - g.Ps = g.Is * Vdc by ring, sq,
    ← mul_assoc]
  exact mul_div_mul_right _ _ hV

@[tmio M, powerlib_domain] theorem fderiv_point (r : ℝ) {δ Vdc : ℝ} (hV : Vdc ≠ 0) :
    fderiv ℝ (g.field r) (g.point δ Vdc) =
      Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (g.model δ Vdc).A := by
  rw [(g.hasFDerivAt_field r (x := g.point δ Vdc) (by simpa [point] using hV)).fderiv]
  simp [point, model]

/-- At a balanced operating point (`P(δ*) = P_ref`, `P_s + I_s V* = P(δ*)`) the field vanishes:
the plant is the linearization at an equilibrium. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem field_point_of_balance (hL : g.L ≠ 0) (hZ : g.absSq ≠ 0)
    {δ Vdc : ℝ} (hV : Vdc ≠ 0) (h1 : g.qssPower δ = g.Pref)
    (h2 : g.Ps + g.Is * Vdc = g.qssPower δ) : g.field g.Pref (g.point δ Vdc) = 0 := by
  have hr := (g.rate_eq_zero_iff hL hZ δ (g.is δ).re (g.is δ).im).mpr ⟨rfl, rfl⟩
  have hP : g.Ps - g.qssPower δ = -(g.Is * Vdc) := by linarith
  simp only [Line.Network.qssPower] at h1 hP
  ext i
  fin_cases i
  · simp [field, point]
  · simp [field, point, h1]
  · simpa [field, point] using hr.1
  · simpa [field, point] using hr.2
  · simp only [field, point, GFL.DCLink.nodeRate]
    simp [hP, neg_div, mul_div_cancel_right₀ _ hV]

/-- The characteristic polynomial is block triangular: `det(sI − J) = det(sI − J_VSM)(s − j)`,
`J_VSM` the line-VSM Jacobian. -/
@[tmio M, powerlib_domain] theorem det_characteristicMatrix_jacobian (δ id iq Vdc : ℝ) (s : ℂ) :
    (Linear.characteristicMatrix (g.jacobian δ id iq Vdc) s).det =
      (Linear.characteristicMatrix (g.toVSM.jacobian δ id iq) s).det *
        (s - g.nodeSlope (g.power δ id iq) Vdc) := by
  rw [Matrix.det_succ_column _ (Fin.last 4), Fin.sum_univ_castSucc]
  have h0 : ∀ i : Fin 4, Linear.characteristicMatrix (g.jacobian δ id iq Vdc) s i.castSucc
      (Fin.last 4) = 0 := by
    intro i; fin_cases i <;> simp [Linear.characteristicMatrix, jacobian]
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Fin.succAbove_last]
  have hsub : (Linear.characteristicMatrix (g.jacobian δ id iq Vdc) s).submatrix Fin.castSucc
      Fin.castSucc = Linear.characteristicMatrix (g.toVSM.jacobian δ id iq) s := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Linear.characteristicMatrix, jacobian, Line.VSM.jacobian]
  rw [hsub]
  simp [Linear.characteristicMatrix, jacobian]
  ring

/-- **Characteristic polynomial at the operating point**:
`M L² det(sI − A) = ((M s² + D s)((R + L s)² + X²) + E² X − Q ((R + L s)² + X²))(s − j)`,
`Q = Q(δ*)` (from the line-VSM polynomial `Line.VSM.characteristic_polynomial`). -/
@[tmio M, powerlib_domain] theorem det_characteristicMatrix_model (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    (δ Vdc : ℝ) (s : ℂ) :
    (g.M : ℂ) * (g.L : ℂ) ^ 2 * (Linear.characteristicMatrix (g.model δ Vdc).A s).det =
      ((g.M * s ^ 2 + g.D * s) * g.lineDen s + g.zeroPoly (g.qssReactive δ) s) *
        (s - g.dcPole δ Vdc) := by
  have h := g.toVSM.characteristic_polynomial hM δ (g.is δ).re (g.is δ).im s
  have hL' : (g.L : ℂ) ≠ 0 := by exact_mod_cast hL
  rw [show (g.model δ Vdc).A = g.jacobian δ (g.is δ).re (g.is δ).im Vdc from rfl,
    g.det_characteristicMatrix_jacobian]
  simp only [Line.Network.σ, Line.Network.ρ] at h
  push_cast at h
  simp only [lineDen, zeroPoly, dcPole, Line.Network.qssReactive, Line.Network.qssPower]
  field_simp at h
  linear_combination (s - ((g.nodeSlope (g.power δ (g.is δ).re (g.is δ).im) Vdc : ℝ) : ℂ)) * h

/-- Off the line poles the characteristic polynomial factors through the swing loop closed by
the angle gain: `M L² det(sI − A) = ((R + L s)² + X²)(M s² + D s + G(s))(s − j)`. -/
@[tmio M, powerlib_domain] theorem det_characteristicMatrix_model_eq_mul (hM : g.M ≠ 0)
    (hL : g.L ≠ 0) (δ Vdc : ℝ) {s : ℂ} (hl : g.lineDen s ≠ 0) :
    (g.M : ℂ) * (g.L : ℂ) ^ 2 * (Linear.characteristicMatrix (g.model δ Vdc).A s).det =
      g.lineDen s * (g.M * s ^ 2 + g.D * s + g.angleGain (g.qssReactive δ) s) *
        (s - g.dcPole δ Vdc) := by
  rw [g.det_characteristicMatrix_model hM hL, g.angleGain_eq_div hl]
  field_simp

/-- Off the poles: `s − j ≠ 0` and `M s² + D s + G(s) ≠ 0`. -/
@[tmio M, powerlib_domain] private theorem ne_zero_of_det (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    {δ Vdc : ℝ} {s : ℂ} (hs : (Linear.characteristicMatrix (g.model δ Vdc).A s).det ≠ 0)
    (hl : g.lineDen s ≠ 0) :
    s - g.dcPole δ Vdc ≠ 0 ∧ g.M * s ^ 2 + g.D * s + g.angleGain (g.qssReactive δ) s ≠ 0 := by
  have h := g.det_characteristicMatrix_model_eq_mul hM hL δ Vdc hl
  have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hL' : (g.L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hne : (g.M : ℂ) * (g.L : ℂ) ^ 2 *
      (Linear.characteristicMatrix (g.model δ Vdc).A s).det ≠ 0 :=
    mul_ne_zero (mul_ne_zero hM' (pow_ne_zero 2 hL')) hs
  rw [h] at hne
  exact ⟨right_ne_zero_of_mul hne, right_ne_zero_of_mul (left_ne_zero_of_mul hne)⟩

/-- **The transfer `ΔV/ΔP_ref` on the dynamic line.** Off the poles,
`ΔV/ΔP_ref = −G(s) / (C V* (s − j)(M s² + D s + G(s)))`, `G(s) = −Q + E² X/((R + L s)² + X²)`
the angle gain (`DynamicLine.transfer_anglePlant`), `Q = Q(δ*)`, `j` the DC-node pole. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem transfer_model (hM : g.M ≠ 0) (hL : g.L ≠ 0) (hC : g.C ≠ 0)
    {δ Vdc : ℝ} (hV : Vdc ≠ 0) {s : ℂ}
    (hs : (Linear.characteristicMatrix (g.model δ Vdc).A s).det ≠ 0) (hl : g.lineDen s ≠ 0) :
    Linear.transfer (g.model δ Vdc) s 0 0 =
      -g.angleGain (g.qssReactive δ) s / (g.C * Vdc * (s - g.dcPole δ Vdc) *
        (g.M * s ^ 2 + g.D * s + g.angleGain (g.qssReactive δ) s)) := by
  have hM' : (g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hL' : (g.L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hC' : (g.C : ℂ) ≠ 0 := by exact_mod_cast hC
  have hV' : (Vdc : ℂ) ≠ 0 := by exact_mod_cast hV
  obtain ⟨he0, hP0⟩ := g.ne_zero_of_det hM hL hs hl
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = g.reactive δ (g.is δ).re (g.is δ).im := ⟨_, rfl⟩
  have hQq : g.qssReactive δ = Q := hQ.symm
  rw [hQq] at hP0 ⊢
  obtain ⟨G, hG⟩ : ∃ G, G = g.angleGain Q s := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℂ, P = g.M * s ^ 2 + g.D * s + G := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℂ, e = s - g.dcPole δ Vdc := ⟨_, rfl⟩
  rw [← hG, ← hP] at hP0
  rw [← he] at he0
  rw [← hG, ← hP, ← he]
  -- the line response to the angle
  have hcs : Complex.cos (δ : ℂ) ^ 2 + Complex.sin (δ : ℂ) ^ 2 = 1 := Complex.cos_sq_add_sin_sq _
  obtain ⟨u, hu⟩ : ∃ u : ℂ,
      u = g.E * (g.X * Complex.cos δ - (g.R + g.L * s) * Complex.sin δ) / g.lineDen s :=
    ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℂ,
      w = g.E * ((g.R + g.L * s) * Complex.cos δ + g.X * Complex.sin δ) / g.lineDen s :=
    ⟨_, rfl⟩
  have h2 : g.E * Complex.sin δ + (g.R + g.L * s) * u - g.X * w = 0 := by
    rw [hu, hw]; field_simp; simp only [lineDen]; ring
  have h3 : -(g.E * Complex.cos δ) + g.X * u + (g.R + g.L * s) * w = 0 := by
    rw [hu, hw]; field_simp; simp only [lineDen]; ring
  have hGu : -(Q : ℂ) + g.E * Complex.cos δ * u + g.E * Complex.sin δ * w = G := by
    rw [hu, hw, hG, angleGain]; field_simp; linear_combination (g.E : ℂ) ^ 2 * g.X * hcs
  set Mx := Linear.characteristicMatrix (g.model δ Vdc).A s with hMx
  set X : Matrix (Fin 5) (Fin 1) ℂ :=
    !![1 / P; s / P; u / P; w / P; -G / (g.C * Vdc * e * P)] with hX
  have hMX : Mx * X = Linear.complexify (g.model δ Vdc).B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hMx, hX, Linear.characteristicMatrix, model, jacobian, inputB, Matrix.mul_apply,
        Fin.sum_univ_five, ← hQ] <;> field_simp
    · ring
    · linear_combination hGu - hP
    · linear_combination h2
    · linear_combination h3
    · have he' : e = s - ((g.nodeSlope (g.power δ (g.is δ).re (g.is δ).im) Vdc : ℝ) : ℂ) := he
      linear_combination e * hGu + G * he'
  have hsol : Mx⁻¹ * Linear.complexify (g.model δ Vdc).B = X := by
    rw [← hMX, Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.mpr hs)]
  rw [Linear.transfer, ← hMx, Matrix.mul_assoc, hsol]
  simp [hX, model, Matrix.mul_apply, Fin.sum_univ_five]

/-- Off the poles the transfer `ΔV/ΔP_ref` vanishes exactly at the zeros of the angle-gain
numerator `E² X − Q ((R + L s)² + X²)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem transfer_model_eq_zero_iff (hM : g.M ≠ 0) (hL : g.L ≠ 0)
    (hC : g.C ≠ 0) {δ Vdc : ℝ} (hV : Vdc ≠ 0) {s : ℂ}
    (hs : (Linear.characteristicMatrix (g.model δ Vdc).A s).det ≠ 0) (hl : g.lineDen s ≠ 0) :
    Linear.transfer (g.model δ Vdc) s 0 0 = 0 ↔ g.zeroPoly (g.qssReactive δ) s = 0 := by
  obtain ⟨he0, hP0⟩ := g.ne_zero_of_det hM hL hs hl
  have hC' : (g.C : ℂ) ≠ 0 := by exact_mod_cast hC
  have hV' : (Vdc : ℂ) ≠ 0 := by exact_mod_cast hV
  rw [g.transfer_model hM hL hC hV hs hl, div_eq_zero_iff, neg_eq_zero,
    or_iff_left (mul_ne_zero (mul_ne_zero (mul_ne_zero hC' hV') he0) hP0),
    g.angleGain_eq_div hl, div_eq_zero_iff, or_iff_left hl]

/-! ### The right-half-plane zero -/

/-- In the open right half plane the line factor does not vanish (`R ≥ 0`, `L > 0`):
`(R + L s)² + X² = (R + L s + jX)(R + L s − jX)` and both factors have real part
`R + L Re s > 0`. -/
@[tmio M, powerlib_domain] theorem lineDen_ne_zero_of_re_pos (hR : 0 ≤ g.R) (hL : 0 < g.L)
    {s : ℂ} (hs : 0 < s.re) : g.lineDen s ≠ 0 := by
  have hfac : g.lineDen s = ((g.R : ℂ) + g.L * s + g.X * Complex.I) *
      ((g.R : ℂ) + g.L * s - g.X * Complex.I) := by
    simp only [lineDen]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hpos : 0 < g.R + g.L * s.re := by nlinarith [mul_pos hL hs]
  rw [hfac]
  refine mul_ne_zero (fun h => ?_) (fun h => ?_) <;>
    · have := congrArg Complex.re h
      simp at this
      linarith

/-- For `Q ≠ 0` the numerator is `−Q L²` times the monic quadratic
`s² + (2R/L) s + (|Z|² − E² X/Q)/L²`. -/
@[tmio M, powerlib_domain] theorem zeroPoly_eq_neg_mul (hL : g.L ≠ 0) {Q : ℝ} (hQ : Q ≠ 0)
    (s : ℂ) :
    g.zeroPoly Q s = -((Q * g.L ^ 2 : ℝ) : ℂ) * (s ^ 2 + ((2 * g.R / g.L : ℝ) : ℂ) * s +
      (((g.absSq - g.E ^ 2 * g.X / Q) / g.L ^ 2 : ℝ) : ℂ)) := by
  have hL' : (g.L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hQ' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ
  simp only [zeroPoly, lineDen, Line.Network.absSq]
  push_cast
  field_simp
  ring

@[tmio M, powerlib_domain] private theorem const_neg_iff (hE : g.E ≠ 0) (hX : 0 < g.X)
    (hL : 0 < g.L) {Q : ℝ} :
    (g.absSq - g.E ^ 2 * g.X / Q) / g.L ^ 2 < 0 ↔ 0 < Q ∧ Q < g.κ := by
  have hZ : 0 < g.absSq := by unfold Line.Network.absSq; positivity
  have hEX : 0 < g.E ^ 2 * g.X := by positivity
  rw [div_lt_iff₀ (by positivity), zero_mul, sub_neg, Line.Network.κ]
  constructor
  · intro h
    have hQ0 : 0 < Q := by
      by_contra hq
      push Not at hq
      have : g.E ^ 2 * g.X / Q ≤ 0 := div_nonpos_of_nonneg_of_nonpos hEX.le hq
      linarith
    refine ⟨hQ0, ?_⟩
    rw [lt_div_iff₀ hQ0] at h
    rw [lt_div_iff₀ hZ]
    linarith
  · rintro ⟨hQ0, hQk⟩
    rw [lt_div_iff₀ hZ] at hQk
    rw [lt_div_iff₀ hQ0]
    linarith

/-- For `0 < Q < κ` the numerator has a positive real root: `E² X = Q ((R + L r)² + X²)`. -/
@[tmio M, powerlib_domain] private theorem exists_zeroPoly_pos_root (hE : g.E ≠ 0) (hX : 0 < g.X)
    (hL : 0 < g.L) {Q : ℝ} (hQk : 0 < Q ∧ Q < g.κ) :
    ∃ r : ℝ, 0 < r ∧ g.zeroPoly Q r = 0 := by
  obtain ⟨r, hr, hroot⟩ := Criteria.exists_quadratic_root_pos_of_const_neg (a1 := 2 * g.R / g.L)
    ((g.const_neg_iff hE hX hL).mpr hQk)
  exact ⟨r, hr, by rw [g.zeroPoly_eq_neg_mul hL.ne' hQk.1.ne',
    Criteria.quadratic_real_root_complex hroot, mul_zero]⟩

/-- **The right-half-plane zero criterion.** With `E ≠ 0`, `X > 0`, `R ≥ 0`, `L > 0`, the
numerator `E² X − Q ((R + L s)² + X²)` of the angle gain has a root in the open right half
plane iff `0 < Q < E² X/|Z|² = κ`. The sum of the roots is `−2R/L ≤ 0`, so a right-half-plane root
is real and the product `(|Z|² − E² X/Q)/L²` is negative. -/
@[tmio M, powerlib_domain] theorem exists_zeroPoly_eq_zero_re_pos_iff (hE : g.E ≠ 0)
    (hX : 0 < g.X) (hR : 0 ≤ g.R) (hL : 0 < g.L) (Q : ℝ) :
    (∃ s : ℂ, 0 < s.re ∧ g.zeroPoly Q s = 0) ↔ 0 < Q ∧ Q < g.κ := by
  have ha1 : 0 ≤ 2 * g.R / g.L := by positivity
  have hL2 : (0 : ℝ) < g.L ^ 2 := by positivity
  constructor
  · rintro ⟨s, hs, h0⟩
    have hQ : Q ≠ 0 := by
      rintro rfl
      have hEX : ((g.E ^ 2 * g.X : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (by positivity : (0 : ℝ) < g.E ^ 2 * g.X).ne'
      apply hEX
      simpa [zeroPoly] using h0
    rw [g.zeroPoly_eq_neg_mul hL.ne' hQ, mul_eq_zero, neg_eq_zero] at h0
    have hq : ((Q * g.L ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero hQ hL2.ne'
    have hroot := h0.resolve_left hq
    have him := Criteria.quadratic_root_im hroot
    have hre := Criteria.quadratic_root_re hroot
    have hs0 : s.im = 0 := (mul_eq_zero.mp him).resolve_right (by linarith)
    rw [hs0] at hre
    refine (g.const_neg_iff hE hX hL).mp ?_
    nlinarith [mul_nonneg ha1 hs.le]
  · intro hQk
    obtain ⟨r, hr, hroot⟩ := g.exists_zeroPoly_pos_root hE hX hL hQk
    exact ⟨r, by simpa using hr, hroot⟩

/-- **The transfer `ΔV/ΔP_ref` has a right-half-plane zero iff `0 < Q(δ*) < E² X/|Z|²`.** For
a physical network (`E, V_g > 0`, `R ≥ 0`, `L, ω₀ > 0`), `M > 0`, `D ≥ 0`, `C, V* ≠ 0`, the
transfer vanishes at some `s` with `Re s > 0` that is not a pole of the plant exactly when the
operating point exports reactive power below `κ = E² X/|Z|²` (on the stable branch
`K(δ*) = κ − Q(δ*) > 0`, `Line.Network.syncCoeff_add_qssReactive`: whenever `Q(δ*) > 0`),
whatever the sign of the active power. The proviso `hb` excludes the cancellation of the zero
by a DC-node pole `j > 0` at the same place. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem exists_transfer_model_eq_zero_re_pos_iff (hN : g.Physical)
    (hM : 0 < g.M) (hD : 0 ≤ g.D) (hC : g.C ≠ 0) {δ Vdc : ℝ} (hV : Vdc ≠ 0)
    (hb : 0 < g.dcPole δ Vdc → g.zeroPoly (g.qssReactive δ) (g.dcPole δ Vdc) ≠ 0) :
    (∃ s : ℂ, 0 < s.re ∧ (Linear.characteristicMatrix (g.model δ Vdc).A s).det ≠ 0 ∧
        Linear.transfer (g.model δ Vdc) s 0 0 = 0) ↔
      0 < g.qssReactive δ ∧ g.qssReactive δ < g.κ := by
  have hX := hN.X_pos
  have hE := hN.E.ne'
  constructor
  · rintro ⟨s, hs, hdet, h0⟩
    have hl := g.lineDen_ne_zero_of_re_pos hN.R hN.L hs
    rw [g.transfer_model_eq_zero_iff hM.ne' hN.L.ne' hC hV hdet hl] at h0
    exact (g.exists_zeroPoly_eq_zero_re_pos_iff hE hX hN.R hN.L _).mp ⟨s, hs, h0⟩
  · intro hQk
    obtain ⟨r, hr, hroot⟩ := g.exists_zeroPoly_pos_root hE hX hN.L hQk
    have hre : 0 < (r : ℂ).re := by simpa using hr
    have hl := g.lineDen_ne_zero_of_re_pos hN.R hN.L hre
    have hG : g.angleGain (g.qssReactive δ) r = 0 := by
      rw [g.angleGain_eq_div hl, hroot, zero_div]
    have hdet : (Linear.characteristicMatrix (g.model δ Vdc).A r).det ≠ 0 := by
      intro h
      have h' := g.det_characteristicMatrix_model_eq_mul hM.ne' hN.L.ne' δ Vdc hl
      rw [h, mul_zero, hG, add_zero] at h'
      have hsw : (g.M : ℂ) * (r : ℂ) ^ 2 + g.D * r ≠ 0 := by
        have : (0 : ℝ) < g.M * r ^ 2 + g.D * r := by positivity
        exact_mod_cast this.ne'
      have hrj : (r : ℂ) - g.dcPole δ Vdc ≠ 0 := by
        intro hj
        have hj' : r = g.dcPole δ Vdc := by exact_mod_cast sub_eq_zero.mp hj
        exact hb (hj' ▸ hr) (by rw [← hj']; exact hroot)
      exact mul_ne_zero (mul_ne_zero hl hsw) hrj h'.symm
    exact ⟨r, hre, hdet,
      (g.transfer_model_eq_zero_iff hM.ne' hN.L.ne' hC hV hdet hl).mpr hroot⟩

/-- **On the stable branch the zero is set by the sign of the reactive power.** With a positive
synchronizing coefficient `K(δ*) = κ − Q(δ*) > 0` (`Line.Network.syncCoeff_add_qssReactive`),
`ΔV/ΔP_ref` has a right-half-plane zero (not a pole) iff the operating point exports reactive
power, `Q(δ*) > 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem exists_transfer_model_eq_zero_re_pos_iff_of_syncCoeff_pos
    (hN : g.Physical) (hM : 0 < g.M) (hD : 0 ≤ g.D) (hC : g.C ≠ 0) {δ Vdc : ℝ} (hV : Vdc ≠ 0)
    (hb : 0 < g.dcPole δ Vdc → g.zeroPoly (g.qssReactive δ) (g.dcPole δ Vdc) ≠ 0)
    (hK : 0 < g.syncCoeff δ) :
    (∃ s : ℂ, 0 < s.re ∧ (Linear.characteristicMatrix (g.model δ Vdc).A s).det ≠ 0 ∧
        Linear.transfer (g.model δ Vdc) s 0 0 = 0) ↔ 0 < g.qssReactive δ := by
  rw [g.exists_transfer_model_eq_zero_re_pos_iff hN hM hD hC hV hb]
  have h := g.syncCoeff_add_qssReactive hN.absSq_pos δ
  exact ⟨fun h' => h'.1, fun h' => ⟨h', by linarith⟩⟩

/-- The static gain of the angle gain is the quasi-static synchronizing coefficient:
`G(0) = κ − Q(δ) = K(δ) = P'(δ)` (`Line.Network.syncCoeff_add_qssReactive`), the slope `k` of
the quasi-static plant `Plant.refPlant`. -/
@[tmio M, powerlib_domain] theorem angleGain_zero (hZ : 0 < g.absSq) (δ : ℝ) :
    g.angleGain (g.qssReactive δ) 0 = (g.syncCoeff δ : ℂ) := by
  have h := g.syncCoeff_add_qssReactive hZ δ
  have hl : g.lineDen 0 = (g.absSq : ℂ) := by
    simp [lineDen, Line.Network.absSq]
  rw [angleGain, hl, show g.syncCoeff δ = g.κ - g.qssReactive δ by linarith, Line.Network.κ]
  push_cast
  ring

end DynamicLine

end powerlib.GFM.DCLink
