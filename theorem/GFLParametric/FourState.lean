import theorem.GFLParametric.Basic
import theorem.Dynamics.Autonomous

/-! # Four-state GFL with PLL and dc-bus voltage loop

**Model boundary.** Single grid-following VSC on an infinite ac source of amplitude `V₀`
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

**The `1/V` term.** The physical field contains `P_abs / V`, so it is not globally `C¹`
(Lean's `x / 0 = 0` makes it discontinuous at `V = 0`).  The powerlib linearization theorems
need a globally `C¹` field, so they are applied to `regField`, where `V⁻¹` is replaced by the
smooth `invExt V` (equal to `V⁻¹` for `V ≥ 1/2`); `regField` coincides with `field` on the
ball of radius `1/2` around the operating point, and the locality lemmas of
`GFLParametric.Basic` transport local exponential stability / instability back to `field`.

**Results.**
* Equilibrium `(θ₀, 0, 1, 0)` iff `V₀ sin θ₀ = −X_g i_{d0}` and `I_dc0 = −(3/2) V₀ cos θ₀ i_{d0}`;
  `θ₀ = arcsin(−X_g i_{d0}/V₀)` with `|X_g i_{d0}| < V₀` gives the principal branch
  (`cos θ₀ > 0`).
* `A₀` derived with `fderiv`; `A₁`, `b₁` of the amplitude modulation `V₀ ↦ V₀(1 + ε)` are exact:
  `J(z₀; ε) = A₀ + ε A₁` and `f_ε(z₀) = ε b₁`.
* Characteristic polynomial
  `det(λI − A₀) = L_PLL(λ)(λ² + 2α_cl λ + ω_cl²) − Γ(k_p λ + k_i)(k_pv λ + k_iv)` with
  `L_PLL = λ² + k_p v_{d0} λ + k_i v_{d0}`, `2α_cl = γ v_{d0}(i_{d0} + k_pv)`,
  `ω_cl² = γ v_{d0} k_iv`, `Γ = γ X_g² i_{d0}²`; exact decoupling when `Γ = 0`;
  `det A₀ = γ k_i k_iv V₀² cos 2θ₀`.
* Domain: quartic Routh–Hurwitz conditions ⇒ local exponential stability;
  `cos 2θ₀ < 0` ⇒ positive real eigenvalue ⇒ unstable; hence local exponential stability
  forces `cos 2θ₀ ≥ 0` (necessary condition `|θ₀| ≤ 45°`).
* Angle input: in error-angle coordinates `θ_g` enters only additively through `−θ̇_g`, so
  the state Jacobian does not depend on the input (`A₁^GFL = 0`, `b(jω_p) = −jω_p e_θ`).

Source: work-sync `projects/vsc-parametric-oscillation/notes/theory-draft.md` §1.2, §2.3;
`.../references/gfm-driven-gfl-parametric-resonance/notes/concepts/
gfl-four-state-parametric-resonance.md` (功率方向与工作点, 四态周期线性化, 特征多项式检查);
`.../references/gfl-gfm-contrast/gfl-gfm-parametric-contrast.md` §14.
Correction: theory-draft §1.2 gives the equilibrium `θ₀ = arcsin(−X_g i_{d0}/V₀)` without
any stability restriction; the formal statements show that local exponential stability
requires `cos 2θ₀ ≥ 0` (`θ₀ ≤ 45°` on the branch) and that `cos 2θ₀ < 0` is unstable for all
positive `k_i, k_iv, C`.  Also `|X_g i_{d0}| < V₀` is required for the principal branch.
-/

noncomputable section
namespace powerlib.GFLParametric.FourState
open Matrix

/-- Parameters of the four-state GFL model. -/
structure Params where
  /-- ac source amplitude -/
  V0 : ℝ
  /-- grid reactance -/
  Xg : ℝ
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
  /-- dc-bus capacitance -/
  C : ℝ
  /-- dc source current -/
  Idc0 : ℝ

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
def field : Dynamics.State 4 → Dynamics.State 4 := lift (coordField p)

/-- Coordinate field with `V⁻¹` replaced by the smooth `invExt V`. -/
def regCoordField (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![p.kp * vq p (y 0) (y 2) (y 3) + p.ki * y 1, vq p (y 0) (y 2) (y 3),
    p.Idc0 / p.C + p.γ * (p.V0 * Real.cos (y 0) * idc p (y 2) (y 3)) * invExt (y 2), y 2 - 1]

/-- Globally smooth field agreeing with `field` for `V ≥ 1/2`. -/
def regField : Dynamics.State 4 → Dynamics.State 4 := lift (regCoordField p)

/-- The operating point `(θ₀, 0, 1, 0)`. -/
def opPoint (θ0 : ℝ) : Dynamics.State 4 := WithLp.toLp 2 ![θ0, 0, 1, 0]

/-- Equilibrium relations of the source. -/
def IsEq (θ0 : ℝ) : Prop :=
  p.V0 * Real.sin θ0 = -(p.Xg * p.id0) ∧ p.Idc0 = -(3 / 2 * (p.V0 * Real.cos θ0) * p.id0)

/-- `v_{d0} = V₀ cos θ₀` -/
def vd0 (θ0 : ℝ) : ℝ := p.V0 * Real.cos θ0

@[powerlib_foundation] theorem field_eq_regField {y : Dynamics.State 4}
    (hy : 1 / 2 ≤ WithLp.ofLp y 2) : field p y = regField p y := by
  simp only [field, regField, lift]
  congr 1
  ext i
  fin_cases i <;> simp [coordField, regCoordField, invExt_eq hy, div_eq_mul_inv]

@[powerlib_foundation] theorem field_eq_regField_of_near {θ0 : ℝ} {y : Dynamics.State 4}
    (hy : ‖y - opPoint θ0‖ < 1 / 2) : field p y = regField p y := by
  apply field_eq_regField
  have h := abs_coord_sub_le (opPoint θ0) y 2
  have h2 : (opPoint θ0) 2 = 1 := rfl
  rw [h2] at h
  have := (abs_lt.mp (lt_of_le_of_lt h hy)).1
  show 1 / 2 ≤ y 2
  linarith

@[powerlib_foundation] theorem isEq_iff (hC : p.C ≠ 0) (θ0 : ℝ) :
    field p (opPoint θ0) = 0 ↔ IsEq p θ0 := by
  constructor
  · intro h
    have hc : ∀ i, coordField p ![θ0, 0, 1, 0] i = 0 := by
      intro i
      have := congrArg (fun w : Dynamics.State 4 => w i) h
      simpa [field, lift, opPoint] using this
    have h1 := hc 1
    have h2 := hc 2
    simp [coordField, vq, idc, Params.γ] at h1 h2
    refine ⟨by linarith, ?_⟩
    field_simp at h2
    linarith
  · rintro ⟨h1, h2⟩
    have hq : vq p θ0 1 0 = 0 := by simp [vq, idc]; linarith
    apply lift_toLp_eq_zero
    ext i
    fin_cases i
    · simp [coordField, hq]
    · simp [coordField, hq]
    · simp [coordField, idc, Params.γ, h2]; field_simp; ring
    · simp [coordField]

@[powerlib_foundation] theorem regField_opPoint {θ0 : ℝ} (hC : p.C ≠ 0) (h : IsEq p θ0) :
    regField p (opPoint θ0) = 0 := by
  rw [← field_eq_regField p (by simp [opPoint]; norm_num)]
  exact (isEq_iff p hC θ0).2 h

/-- Principal equilibrium branch: `θ₀ = arcsin(−X_g i_{d0}/V₀)`, `|X_g i_{d0}| < V₀`. -/
@[powerlib_foundation] theorem principal_branch (hV0 : 0 < p.V0)
    (hlt : |p.Xg * p.id0| < p.V0) :
    p.V0 * Real.sin (Real.arcsin (-(p.Xg * p.id0) / p.V0)) = -(p.Xg * p.id0) ∧
      0 < Real.cos (Real.arcsin (-(p.Xg * p.id0) / p.V0)) := by
  have hr : |-(p.Xg * p.id0) / p.V0| < 1 := by
    rw [abs_div, abs_neg, abs_of_pos hV0, div_lt_one hV0]; exact hlt
  obtain ⟨h1, h2⟩ := abs_lt.mp hr
  refine ⟨?_, ?_⟩
  · rw [Real.sin_arcsin h1.le h2.le]; field_simp
  · rw [Real.cos_arcsin]
    apply Real.sqrt_pos.2
    nlinarith

@[powerlib_foundation] theorem contDiff_regField : ContDiff ℝ 1 (regField p) := by
  have hinv : ContDiff ℝ 1 invExt := contDiff_invExt
  apply contDiff_lift
  apply contDiff_pi.2
  intro i
  fin_cases i
  · simp [regCoordField, vq, idc]; fun_prop
  · simp [regCoordField, vq, idc]; fun_prop
  · simp only [regCoordField]
    simp
    have h2 : ContDiff ℝ 1 (fun y : Fin 4 → ℝ => invExt (y 2)) :=
      hinv.comp (contDiff_apply ℝ ℝ (2 : Fin 4))
    have h1 : ContDiff ℝ 1 (fun y : Fin 4 → ℝ =>
        p.γ * (p.V0 * Real.cos (y 0) * idc p (y 2) (y 3))) := by
      simp [idc]; fun_prop
    exact contDiff_const.add (h1.mul h2)
  · simp [regCoordField]; fun_prop

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

@[powerlib_foundation] theorem jacGen_opPoint (θ0 : ℝ) : jacGen p θ0 1 0 = A0 p θ0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jacGen, A0, vd0, idc] <;> first | ring1 | (left; ring1)

@[powerlib_foundation] theorem hasFDerivAt_regCoordField {y : Fin 4 → ℝ} (hy : 1 / 2 < y 2) :
    HasFDerivAt (regCoordField p)
      (Matrix.toLin' (jacGen p (y 0) (y 2) (y 3))).toContinuousLinearMap y := by
  have h0 := hasFDerivAt_coord (0 : Fin 4) y
  have h1 := hasFDerivAt_coord (1 : Fin 4) y
  have h2 := hasFDerivAt_coord (2 : Fin 4) y
  have h3 := hasFDerivAt_coord (3 : Fin 4) y
  have hy0 : y 2 ≠ 0 := by linarith
  have hidc := ((h2.sub_const 1).const_mul p.kpv).const_sub p.id0 |>.sub (h3.const_mul p.kiv)
  have hq := (h0.sin.const_mul (-p.V0)).sub (hidc.const_mul p.Xg)
  have hinvd : HasDerivAt invExt (-(y 2 ^ 2)⁻¹) (y 2) := by
    have hev : invExt =ᶠ[nhds (y 2)] fun V => V⁻¹ := by
      filter_upwards [Ioi_mem_nhds hy] with V hV
      exact invExt_eq (le_of_lt hV)
    exact (hasDerivAt_inv hy0).congr_of_eventuallyEq hev
  have hinv := hinvd.comp_hasFDerivAt y h2
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · refine hasFDerivAt_of_eq ((hq.const_mul p.kp).add (h1.const_mul p.ki))
      (fun z => by simp [regCoordField, vq, idc]) ?_
    ext v
    simp [jacGen, dotProduct, Fin.sum_univ_four]
    ring
  · refine hasFDerivAt_of_eq hq (fun z => by simp [regCoordField, vq, idc]) ?_
    ext v
    simp [jacGen, dotProduct, Fin.sum_univ_four]
    ring
  · have hP := ((h0.cos.const_mul p.V0).mul hidc).const_mul p.γ
    refine hasFDerivAt_of_eq ((hP.mul hinv).const_add (p.Idc0 / p.C))
      (fun z => by simp [regCoordField, idc]) ?_
    ext v
    simp [jacGen, dotProduct, Fin.sum_univ_four, idc,
      invExt_eq (le_of_lt hy)]
    field_simp
    ring
  · refine hasFDerivAt_of_eq (h2.sub_const 1) (fun z => by simp [regCoordField]) ?_
    ext v
    simp [jacGen, dotProduct, Fin.sum_univ_four]

/-- `A₀` is the Jacobian of the (regularized) field at the operating point. -/
@[powerlib_foundation] theorem fderiv_regField_opPoint (θ0 : ℝ) :
    fderiv ℝ (regField p) (opPoint θ0) =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (A0 p θ0) := by
  have := hasFDerivAt_regCoordField p (y := ![θ0, 0, 1, 0]) (by simp; norm_num)
  rw [← jacGen_opPoint]
  exact fderiv_lift (by simpa [opPoint] using this)

/-- The physical field has the same Jacobian `A₀` at the operating point. -/
@[powerlib_foundation] theorem fderiv_field_opPoint (θ0 : ℝ) :
    fderiv ℝ (field p) (opPoint θ0) =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (A0 p θ0) := by
  rw [← fderiv_regField_opPoint]
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [Metric.ball_mem_nhds (opPoint θ0) (by norm_num : (0 : ℝ) < 1 / 2)] with y hy
  exact field_eq_regField_of_near p (by simpa [dist_eq_norm] using hy)

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
@[powerlib_foundation] theorem jac_modulated (θ0 ε : ℝ) :
    jacGen (modulated p ε) θ0 1 0 = A0 p θ0 + ε • A1 p θ0 := by
  rw [jacGen_opPoint]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A0, A1, modulated, vd0, Params.γ] <;> ring

@[powerlib_foundation] theorem hasDerivAt_jac_modulated (θ0 : ℝ) (i j : Fin 4) :
    HasDerivAt (fun ε => jacGen (modulated p ε) θ0 1 0 i j) (A1 p θ0 i j) 0 := by
  simp only [jac_modulated, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (A1 p θ0 i j)).const_add (A0 p θ0 i j)

/-- At an equilibrium, the modulated field at `z₀` is exactly `ε b₁`. -/
@[powerlib_foundation] theorem coordField_modulated (hC : p.C ≠ 0) {θ0 : ℝ} (h : IsEq p θ0)
    (ε : ℝ) : coordField (modulated p ε) ![θ0, 0, 1, 0] = ε • b1 p θ0 := by
  obtain ⟨h1, h2⟩ := h
  ext i
  fin_cases i
  · simp [coordField, modulated, vq, idc, b1]; linear_combination (-p.kp) * h1
  · simp [coordField, modulated, vq, idc, b1]; linear_combination (-1 : ℝ) * h1
  · simp [coordField, modulated, idc, b1, Pabs, Params.γ, h2]; field_simp; ring
  · simp [coordField, b1]

/-! ## Characteristic polynomial -/

/-- `L_PLL(λ) = λ² + k_p v_{d0} λ + k_i v_{d0}` -/
def LPLL (θ0 : ℝ) (s : ℂ) : ℂ := s ^ 2 + (p.kp * vd0 p θ0 : ℝ) * s + (p.ki * vd0 p θ0 : ℝ)

/-- `2α_cl = γ v_{d0}(i_{d0} + k_pv)` -/
def twoAlphaCl (θ0 : ℝ) : ℝ := p.γ * vd0 p θ0 * (p.id0 + p.kpv)

/-- `ω_cl² = γ v_{d0} k_iv` -/
def omegaClSq (θ0 : ℝ) : ℝ := p.γ * vd0 p θ0 * p.kiv

/-- `L_dc(λ) = λ² + 2α_cl λ + ω_cl²` -/
def Ldc (θ0 : ℝ) (s : ℂ) : ℂ := s ^ 2 + (twoAlphaCl p θ0 : ℂ) * s + (omegaClSq p θ0 : ℂ)

/-- Coupling `Γ = γ X_g² i_{d0}²` -/
def Γc : ℝ := p.γ * p.Xg ^ 2 * p.id0 ^ 2

/-- `2α_cl` and `ω_cl²` are the negated dc-block entries of `A₀`. -/
@[powerlib_foundation] theorem dcBlock_closed_forms (θ0 : ℝ) :
    twoAlphaCl p θ0 = -A0 p θ0 2 2 ∧ omegaClSq p θ0 = -A0 p θ0 2 3 := by
  simp [twoAlphaCl, omegaClSq, A0]

/-- Characteristic equation of the source:
`det(λI − A₀) = L_PLL(λ) L_dc(λ) − Γ (k_p λ + k_i)(k_pv λ + k_iv)`. -/
@[powerlib_foundation] theorem det_characteristicMatrix_A0 {θ0 : ℝ}
    (h : p.V0 * Real.sin θ0 = -(p.Xg * p.id0)) (s : ℂ) :
    (LTI.characteristicMatrix (A0 p θ0) s).det =
      LPLL p θ0 s * Ldc p θ0 s -
        (Γc p : ℂ) * ((p.kp : ℂ) * s + p.ki) * ((p.kpv : ℂ) * s + p.kiv) := by
  rw [Criteria.det_characteristicMatrix_fin_four]
  have hA : A0 p θ0 2 0 = p.γ * p.Xg * p.id0 ^ 2 := by
    simp [A0]
    have : p.γ * p.V0 * Real.sin θ0 * p.id0 = p.γ * p.id0 * (p.V0 * Real.sin θ0) := by ring
    rw [this, h]; ring
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_four, Criteria.principalMinorSum2Fin4,
    Criteria.principalMinorSum3Fin4, Criteria.det_fin_four, hA]
  simp [A0, LPLL, Ldc, twoAlphaCl, omegaClSq, Γc]
  ring

/-- Same, with `L_dc` written through the closed forms (`charpoly(A₀)` form of the source). -/
@[powerlib_foundation] theorem det_characteristicMatrix_A0_closed {θ0 : ℝ}
    (h : p.V0 * Real.sin θ0 = -(p.Xg * p.id0)) (s : ℂ) :
    (LTI.characteristicMatrix (A0 p θ0) s).det =
      LPLL p θ0 s * (s ^ 2 + (twoAlphaCl p θ0 : ℂ) * s + (omegaClSq p θ0 : ℂ)) -
        (Γc p : ℂ) * ((p.kp : ℂ) * s + p.ki) * ((p.kpv : ℂ) * s + p.kiv) :=
  det_characteristicMatrix_A0 p h s

/-- Exact decoupling at `Γ = 0`: the characteristic polynomial factors as `L_PLL · L_dc`. -/
@[powerlib_foundation] theorem decoupled_of_Gamma_zero {θ0 : ℝ}
    (h : p.V0 * Real.sin θ0 = -(p.Xg * p.id0)) (hΓ : Γc p = 0) (s : ℂ) :
    (LTI.characteristicMatrix (A0 p θ0) s).det = LPLL p θ0 s * Ldc p θ0 s := by
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

@[powerlib_foundation] theorem det_characteristicMatrix_A0_quartic {θ0 : ℝ}
    (h : p.V0 * Real.sin θ0 = -(p.Xg * p.id0)) (s : ℂ) :
    (LTI.characteristicMatrix (A0 p θ0) s).det =
      s ^ 4 + (a3 p θ0 : ℂ) * s ^ 3 + (a2 p θ0 : ℂ) * s ^ 2 + (a1 p θ0 : ℂ) * s +
        (a0 p θ0 : ℂ) := by
  rw [det_characteristicMatrix_A0 p h]
  simp only [LPLL, Ldc, a3, a2, a1, a0]
  push_cast
  ring

/-- `a₀ = det A₀ = γ k_i k_iv V₀² cos 2θ₀`. -/
@[powerlib_foundation] theorem a0_eq {θ0 : ℝ} (h : p.V0 * Real.sin θ0 = -(p.Xg * p.id0)) :
    a0 p θ0 = p.γ * p.ki * p.kiv * p.V0 ^ 2 * Real.cos (2 * θ0) := by
  have hc : Real.cos (2 * θ0) = Real.cos θ0 ^ 2 - Real.sin θ0 ^ 2 := by
    rw [Real.cos_two_mul]; have := Real.sin_sq_add_cos_sq θ0; linarith
  have hs : (p.Xg * p.id0) ^ 2 = (p.V0 * Real.sin θ0) ^ 2 := by rw [h]; ring
  simp only [a0, omegaClSq, Γc, vd0, hc]
  linear_combination (-(p.γ * p.ki * p.kiv)) * hs

@[powerlib_foundation] theorem det_A0 {θ0 : ℝ} (h : p.V0 * Real.sin θ0 = -(p.Xg * p.id0)) :
    (A0 p θ0).det = p.γ * p.ki * p.kiv * p.V0 ^ 2 * Real.cos (2 * θ0) := by
  have h1 := det_characteristicMatrix_A0_quartic p h 0
  rw [Criteria.det_characteristicMatrix_fin_four] at h1
  simp at h1
  rw [← a0_eq p h]
  exact_mod_cast h1

/-! ## Stability of the operating point -/

/-- Four-state GFL (PLL + dc-voltage loop): the quartic Routh–Hurwitz conditions on the
coefficients of `det(λI − A₀)` give local exponential stability of the physical field. -/
@[powerlib_domain] theorem locallyExponentiallyStable_of_routh (hC : p.C ≠ 0) {θ0 : ℝ}
    (heq : IsEq p θ0) (h3 : 0 < a3 p θ0) (h1 : 0 < a1 p θ0) (h0 : 0 < a0 p θ0)
    (hg : a1 p θ0 ^ 2 + a3 p θ0 ^ 2 * a0 p θ0 < a3 p θ0 * a2 p θ0 * a1 p θ0) :
    Dynamics.LocallyExponentiallyStable (field p) (opPoint θ0) :=
  locallyExponentiallyStable_of_eqOn_ball (by norm_num : (0 : ℝ) < 1 / 2)
    (fun y hy => field_eq_regField_of_near p hy)
    (Criteria.locallyExponentiallyStable_of_jacobian_quartic (A0 p θ0) (contDiff_regField p)
      (regField_opPoint p hC heq) (fderiv_regField_opPoint p θ0)
      (det_characteristicMatrix_A0_quartic p heq.1) h3 h1 h0 hg)

/-- Four-state GFL: `cos 2θ₀ < 0` (operating angle beyond 45°) gives `det A₀ < 0`, a positive
real eigenvalue, and instability of the physical field, for all positive `C, k_i, k_iv`. -/
@[powerlib_domain] theorem unstable_of_cos_two_mul_neg (hC : 0 < p.C) (hki : 0 < p.ki)
    (hkiv : 0 < p.kiv) (hV0 : p.V0 ≠ 0) {θ0 : ℝ} (heq : IsEq p θ0)
    (hcos : Real.cos (2 * θ0) < 0) :
    Dynamics.Unstable (field p) (opPoint θ0) := by
  have hγ : 0 < p.γ := by unfold Params.γ; positivity
  have hdet : (A0 p θ0).det < 0 := by
    rw [det_A0 p heq.1]
    have : 0 < p.γ * p.ki * p.kiv * p.V0 ^ 2 := by positivity
    nlinarith
  exact unstable_of_eqOn_ball (by norm_num : (0 : ℝ) < 1 / 2)
    (fun y hy => field_eq_regField_of_near p hy)
    (Criteria.unstable_of_jacobian_det_neg_fin_four (A0 p θ0) (contDiff_regField p)
      (regField_opPoint p hC.ne' heq) (fderiv_regField_opPoint p θ0) hdet)

/-- Necessary condition: if the operating point is locally exponentially stable then
`cos 2θ₀ ≥ 0` (`|θ₀| ≤ 45°` on the principal branch). -/
@[powerlib_domain] theorem cos_two_mul_nonneg_of_locallyExponentiallyStable (hC : 0 < p.C)
    (hki : 0 < p.ki) (hkiv : 0 < p.kiv) (hV0 : p.V0 ≠ 0) {θ0 : ℝ} (heq : IsEq p θ0)
    (hs : Dynamics.LocallyExponentiallyStable (field p) (opPoint θ0)) :
    0 ≤ Real.cos (2 * θ0) := by
  by_contra hneg
  push Not at hneg
  exact unstable_of_cos_two_mul_neg p hC hki hkiv hV0 heq hneg
    (Dynamics.LocallyExponentiallyStable.lyapunovStable hs)

/-- The Routh condition `a₀ > 0` already encodes `cos 2θ₀ > 0`. -/
@[powerlib_foundation] theorem cos_two_mul_pos_of_a0_pos (hC : 0 < p.C) (hki : 0 < p.ki)
    (hkiv : 0 < p.kiv) {θ0 : ℝ} (h : p.V0 * Real.sin θ0 = -(p.Xg * p.id0))
    (h0 : 0 < a0 p θ0) : 0 < Real.cos (2 * θ0) := by
  rw [a0_eq p h] at h0
  have hγ : 0 < p.γ := by unfold Params.γ; positivity
  by_contra hc
  push Not at hc
  have : p.γ * p.ki * p.kiv * p.V0 ^ 2 * Real.cos (2 * θ0) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
  linarith

/-! ## Grid-angle input in error-angle coordinates -/

/-- Field with the grid angle `u = θ_g` and its rate `u̇` as inputs; in error-angle
coordinates `u` itself does not appear and `u̇` enters only `θ̇`. -/
def fieldAngle (_u ud : ℝ) (z : Dynamics.State 4) : Dynamics.State 4 :=
  field p z - ud • WithLp.toLp 2 ![1, 0, 0, 0]

/-- `f_u = 0`, `f_{u̇} = −e_θ`: the input is purely additive. -/
@[powerlib_foundation] theorem fieldAngle_indep_angle (u u' ud : ℝ) :
    fieldAngle p u ud = fieldAngle p u' ud := rfl

/-- `A₁^GFL = 0`: the state Jacobian does not depend on the grid-angle input. -/
@[powerlib_foundation] theorem fderiv_fieldAngle (u ud : ℝ) (z : Dynamics.State 4) :
    fderiv ℝ (fieldAngle p u ud) z = fderiv ℝ (field p) z := by
  unfold fieldAngle
  exact fderiv_sub_const _

/-- The derivative of the state Jacobian with respect to the grid angle is zero. -/
@[powerlib_foundation] theorem hasDerivAt_jacobian_angle (ud : ℝ) (z : Dynamics.State 4)
    (u : ℝ) : HasDerivAt (fun u => fderiv ℝ (fieldAngle p u ud) z) 0 u := by
  show HasDerivAt (fun _ : ℝ => fderiv ℝ (fieldAngle p 0 ud) z) 0 u
  exact hasDerivAt_const u _

end powerlib.GFLParametric.FourState
