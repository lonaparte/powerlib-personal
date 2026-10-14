import theorem.Dynamics.Locality
import theorem.Criteria.Routh4
import theorem.Dynamics.ConverseLinearization
import theorem.Family.Basic
import theorem.Dynamics.Shift
import theorem.TMIO.ClaimElab
import theorem.Dynamics.Coordinates

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
smooth `Dynamics.invExt V` (equal to `V⁻¹` for `V ≥ 1/2`); `regField` coincides with `field` on the
ball of radius `1/2` around the operating point, and the locality lemmas of
`Dynamics.Locality` transport local exponential stability / instability back to `field`.

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

**Family and connection conclusions.** A complete system (`Model`) is a parameter set with a
selected angle `θ₀`; the system map reads it as the physical field (with its `1/V` term)
translated so that the operating point `(θ₀, 0, 1, 0)` is the origin,
`z ↦ field p (z + opPoint θ₀)` (every flow sentence is invariant under this translation,
`Flow.Property.holds_shift_iff`). The requirement language is static: the operating point is an
equilibrium (`IsEq p θ₀`, `C ≠ 0`); the quartic coefficients of `det(λI − A₀)` satisfy the Routh
conditions; or `a₀ < 0`. The local sentences translate into the first two, instability into the
first and the third, passivity into nothing, and the global sentences, decay rates, sampled
contraction and conservation into the whole (inconsistent) language: unavailable translation
coverage. `chain_le_semantics` proves every translation sound (linearization of the smooth
`regField`, transported back through the locality lemmas of `Dynamics.Locality`, then moved to
the origin); `exact_passive` proves the passivity translation exact. The former domain theorems
are connection conclusions: `mem_den_locallyExponentiallyStable_of_routh`,
`mem_den_unstable_of_cos_two_mul_neg`, and — the former necessary condition
`cos_two_mul_nonneg_of_locallyExponentiallyStable`, which had a behavioural premise — its
contrapositive `not_mem_den_locallyExponentiallyStable_of_cos_two_mul_neg` (with the stronger
`not_mem_den_lyapunovStable_of_cos_two_mul_neg`). The local exponential translation is exact
(`exact_locallyExponentiallyStable`): the physical field agrees with `regField` on a ball around
the operating point, and by the converse linearization theorem
(`Dynamics.isHurwitz_of_locallyExponentiallyStable`) local exponential stability forces an
equilibrium (`IsEq`) with `A₀` Hurwitz, i.e. the quartic Routh conditions
(`Criteria.isHurwitz_iff_of_det_characteristicMatrix_quartic`); with `C = 0` the dc-bus voltage
is a linear first integral and excludes it. The instability translation is not exact
(`not_exact_unstable`): instability is the failure of Lyapunov stability, so a model whose
selected point is not an equilibrium (`offEquilibrium`, no ac source and a constant dc source
current) is unstable (`offEquilibrium_mem_den_unstable`). The Lyapunov translation is not exact
(`not_exact_lyapunovStable`): the undamped PLL (`k_p = 0`, `X_g = 0`) driving a damped dc loop
`undampedPLL` is Lyapunov stable (`undampedPLL_mem_den_lyapunovStable`) through the sum of the
conserved pendulum energy `1 − cos θ + x²/2` and the dc quadratic `u² + u η + (3/2) η²`, which
does not increase while the loop gain `cos θ / V` stays in `[3/4, 5/4]`; its quartic
`(λ² + 1)(λ² + λ + 1)` fails the strict Routh inequality. The local asymptotic translation is
not exact either (`GFLParametric.FourStateBoundary.not_exact_locallyAsymptoticallyStable`): the
weak focus `FourStateBoundary.weakFocus` on the Hopf boundary of the undamped dc loop is locally
asymptotically stable. `GFLParametric.FourStateBoundary` also proves the necessary closed Routh
conditions for Lyapunov stability and that no translation into this requirement language is exact
for Lyapunov stability, local asymptotic stability or instability (`realize_ne_den_*`): models
with the same requirement profile on the Routh boundary fall on both sides. The angle-input field
`fieldAngle` and its Jacobian identities are static.

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
def field : Dynamics.State 4 → Dynamics.State 4 := Dynamics.lift (coordField p)

/-- Coordinate field with `V⁻¹` replaced by the smooth `invExt V`. -/
def regCoordField (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![p.kp * vq p (y 0) (y 2) (y 3) + p.ki * y 1, vq p (y 0) (y 2) (y 3),
    p.Idc0 / p.C + p.γ * (p.V0 * Real.cos (y 0) * idc p (y 2) (y 3)) * Dynamics.invExt (y 2), y 2 - 1]

/-- Globally smooth field agreeing with `field` for `V ≥ 1/2`. -/
def regField : Dynamics.State 4 → Dynamics.State 4 := Dynamics.lift (regCoordField p)

/-- The operating point `(θ₀, 0, 1, 0)`. -/
def opPoint (θ0 : ℝ) : Dynamics.State 4 := WithLp.toLp 2 ![θ0, 0, 1, 0]

/-- Equilibrium relations of the source. -/
def IsEq (θ0 : ℝ) : Prop :=
  p.V0 * Real.sin θ0 = -(p.Xg * p.id0) ∧ p.Idc0 = -(3 / 2 * (p.V0 * Real.cos θ0) * p.id0)

/-- `v_{d0} = V₀ cos θ₀` -/
def vd0 (θ0 : ℝ) : ℝ := p.V0 * Real.cos θ0

@[powerlib_foundation] theorem field_eq_regField {y : Dynamics.State 4}
    (hy : 1 / 2 ≤ WithLp.ofLp y 2) : field p y = regField p y := by
  simp only [field, regField, Dynamics.lift]
  congr 1
  ext i
  fin_cases i <;> simp [coordField, regCoordField, Dynamics.invExt_eq hy, div_eq_mul_inv]

@[powerlib_foundation] theorem field_eq_regField_of_near {θ0 : ℝ} {y : Dynamics.State 4}
    (hy : ‖y - opPoint θ0‖ < 1 / 2) : field p y = regField p y := by
  apply field_eq_regField
  have h := Dynamics.abs_coord_sub_le (opPoint θ0) y 2
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
  have hinv : ContDiff ℝ 1 Dynamics.invExt := Dynamics.contDiff_invExt
  apply Dynamics.contDiff_lift
  apply contDiff_pi.2
  intro i
  fin_cases i
  · simp [regCoordField, vq, idc]; fun_prop
  · simp [regCoordField, vq, idc]; fun_prop
  · simp only [regCoordField]
    simp
    have h2 : ContDiff ℝ 1 (fun y : Fin 4 → ℝ => Dynamics.invExt (y 2)) :=
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
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) y
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) y
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) y
  have h3 := hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) y
  have hy0 : y 2 ≠ 0 := by linarith
  have hidc := ((h2.sub_const 1).const_mul p.kpv).const_sub p.id0 |>.sub (h3.const_mul p.kiv)
  have hq := (h0.sin.const_mul (-p.V0)).sub (hidc.const_mul p.Xg)
  have hinvd : HasDerivAt Dynamics.invExt (-(y 2 ^ 2)⁻¹) (y 2) := by
    have hev : Dynamics.invExt =ᶠ[nhds (y 2)] fun V => V⁻¹ := by
      filter_upwards [Ioi_mem_nhds hy] with V hV
      exact Dynamics.invExt_eq (le_of_lt hV)
    exact (hasDerivAt_inv hy0).congr_of_eventuallyEq hev
  have hinv := hinvd.comp_hasFDerivAt y h2
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · refine Dynamics.hasFDerivAt_of_eq ((hq.const_mul p.kp).add (h1.const_mul p.ki))
      (fun z => by simp [regCoordField, vq, idc]) ?_
    ext v
    simp [jacGen, dotProduct, Fin.sum_univ_four]
    ring
  · refine Dynamics.hasFDerivAt_of_eq hq (fun z => by simp [regCoordField, vq, idc]) ?_
    ext v
    simp [jacGen, dotProduct, Fin.sum_univ_four]
    ring
  · have hP := ((h0.cos.const_mul p.V0).mul hidc).const_mul p.γ
    refine Dynamics.hasFDerivAt_of_eq ((hP.mul hinv).const_add (p.Idc0 / p.C))
      (fun z => by simp [regCoordField, idc]) ?_
    ext v
    simp [jacGen, dotProduct, Fin.sum_univ_four, idc,
      Dynamics.invExt_eq (le_of_lt hy)]
    field_simp
    ring
  · refine Dynamics.hasFDerivAt_of_eq (h2.sub_const 1) (fun z => by simp [regCoordField]) ?_
    ext v
    simp [jacGen, dotProduct, Fin.sum_univ_four]

/-- `A₀` is the Jacobian of the (regularized) field at the operating point. -/
@[powerlib_foundation] theorem fderiv_regField_opPoint (θ0 : ℝ) :
    fderiv ℝ (regField p) (opPoint θ0) =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (A0 p θ0) := by
  have := hasFDerivAt_regCoordField p (y := ![θ0, 0, 1, 0]) (by simp; norm_num)
  rw [← jacGen_opPoint]
  exact Dynamics.fderiv_lift (by simpa [opPoint] using this)

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
  simp [A0, LPLL, Ldc, twoAlphaCl, omegaClSq, Γc]
  ring

/-- Same, with `L_dc` written through the closed forms (`charpoly(A₀)` form of the source). -/
@[powerlib_foundation] theorem det_characteristicMatrix_A0_closed {θ0 : ℝ}
    (h : p.V0 * Real.sin θ0 = -(p.Xg * p.id0)) (s : ℂ) :
    (Linear.characteristicMatrix (A0 p θ0) s).det =
      LPLL p θ0 s * (s ^ 2 + (twoAlphaCl p θ0 : ℂ) * s + (omegaClSq p θ0 : ℂ)) -
        (Γc p : ℂ) * ((p.kp : ℂ) * s + p.ki) * ((p.kpv : ℂ) * s + p.kiv) :=
  det_characteristicMatrix_A0 p h s

/-- Exact decoupling at `Γ = 0`: the characteristic polynomial factors as `L_PLL · L_dc`. -/
@[powerlib_foundation] theorem decoupled_of_Gamma_zero {θ0 : ℝ}
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

@[powerlib_foundation] theorem det_characteristicMatrix_A0_quartic {θ0 : ℝ}
    (h : p.V0 * Real.sin θ0 = -(p.Xg * p.id0)) (s : ℂ) :
    (Linear.characteristicMatrix (A0 p θ0) s).det =
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


/-! ## The four-state GFL family -/

/-- A four-state GFL model read about a selected angle `θ₀`: the operating point is
`(θ₀, 0, 1, 0)`. -/
structure Model where
  /-- The parameters. -/
  params : Params
  /-- The selected angle `θ₀`. -/
  θ : ℝ

/-- The physical field translated so that the selected operating point is the origin. -/
def Model.field (m : Model) (z : Dynamics.State 4) : Dynamics.State 4 :=
  FourState.field m.params (z + opPoint m.θ)

/-- Requirements on the four-state GFL models, all static. -/
inductive Requirement
  /-- `(θ₀, 0, 1, 0)` is an equilibrium (`IsEq p θ₀`) and `C ≠ 0`. -/
  | equilibrium
  /-- The quartic coefficients of `det(λI − A₀)` satisfy the Routh conditions
  `a₃, a₁, a₀ > 0`, `a₁² + a₃² a₀ < a₃ a₂ a₁`. -/
  | routh
  /-- The constant coefficient is negative, `a₀ < 0`. -/
  | constNeg

/-- Satisfaction of a requirement by a model. -/
def Meets (m : Model) : Requirement → Prop
  | .equilibrium => IsEq m.params m.θ ∧ m.params.C ≠ 0
  | .routh => 0 < a3 m.params m.θ ∧ 0 < a1 m.params m.θ ∧ 0 < a0 m.params m.θ ∧
      a1 m.params m.θ ^ 2 + a3 m.params m.θ ^ 2 * a0 m.params m.θ <
        a3 m.params m.θ * a2 m.params m.θ * a1 m.params m.θ
  | .constNeg => a0 m.params m.θ < 0

/-- The translation of the sentences: the local ones into an equilibrium meeting the Routh
conditions, instability into an equilibrium with `a₀ < 0`, passivity into nothing. The global
sentences, decay rates, sampled contraction and conservation are not decided by the
linearization and are translated into the whole language, which no model meets (unavailable
translation coverage). -/
def translate : Sentence → Set Requirement
  | .flow .lyapunovStable | .flow .locallyAsymptoticallyStable
  | .flow .locallyExponentiallyStable => {.equilibrium, .routh}
  | .flow .unstable => {.equilibrium, .constNeg}
  | .flow _ => Set.univ
  | .passive => ∅

/-- The four-state GFL family: every model read as its physical field translated to the
selected operating point. -/
def family : Family Model Requirement 4 0 :=
  ⟨fun m => Port.System.autonomous m.field, Meets, translate⟩

@[powerlib_foundation] theorem family_isAutonomous : family.IsAutonomous Model.field :=
  fun _ => rfl

/-! ### Implementation evidence (private) -/

/-- A flow sentence of a model is the sentence of the untranslated field at `(θ₀, 0, 1, 0)`. -/
private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds (FourState.field m.params) (opPoint m.θ) :=
  family_isAutonomous.mem_den_flow.trans (Flow.Property.holds_shift_iff P)

/-- The quartic Routh conditions give local exponential stability of the physical field (the
proof of the former public `locallyExponentiallyStable_of_routh`). -/
private theorem les_of_meets {m : Model} (he : Meets m .equilibrium) (hr : Meets m .routh) :
    m ∈ family.den (.flow .locallyExponentiallyStable) := by
  obtain ⟨heq, hC⟩ := he
  obtain ⟨h3, h1, h0, hg⟩ := hr
  exact mem_den_flow_iff.mpr (Dynamics.locallyExponentiallyStable_of_eqOn_ball
    (by norm_num : (0 : ℝ) < 1 / 2) (fun y hy => field_eq_regField_of_near m.params hy)
    (Criteria.locallyExponentiallyStable_of_jacobian_quartic (A0 m.params m.θ)
      (contDiff_regField m.params) (regField_opPoint m.params hC heq)
      (fderiv_regField_opPoint m.params m.θ) (det_characteristicMatrix_A0_quartic m.params heq.1)
      h3 h1 h0 hg))

/-- `a₀ < 0` gives a positive real eigenvalue and instability of the physical field (the proof
of the former public `unstable_of_cos_two_mul_neg`). -/
private theorem unstable_of_meets {m : Model} (he : Meets m .equilibrium)
    (hn : Meets m .constNeg) : m ∈ family.den (.flow .unstable) := by
  obtain ⟨heq, hC⟩ := he
  exact mem_den_flow_iff.mpr (Dynamics.unstable_of_eqOn_ball (by norm_num : (0 : ℝ) < 1 / 2)
    (fun y hy => field_eq_regField_of_near m.params hy)
    (Criteria.unstable_of_jacobian_quartic_const_neg (A0 m.params m.θ)
      (contDiff_regField m.params) (regField_opPoint m.params hC heq)
      (fderiv_regField_opPoint m.params m.θ) (det_characteristicMatrix_A0_quartic m.params heq.1)
      hn))

/-! ### Soundness of the translation -/

/-- No model has `a₀ > 0` and `a₀ < 0`: the whole requirement language is inconsistent. -/
@[powerlib_foundation] theorem realize_univ :
    connection% (TMIO.realize Meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  ext m
  simp only [TMIO.mem_realize, Set.mem_univ, true_implies, Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨-, -, h0, -⟩ : Meets m .routh := h .routh
  have : Meets m .constNeg := h .constNeg
  exact lt_asymm h0 this

/-- Every translation of the four-state GFL family is sound: its translation chain lies below
its semantics connection. The Routh conditions at an equilibrium prove the local sentences,
`a₀ < 0` proves instability (LeanForControl's linearization theorems for the smooth `regField`,
transported to the physical field by locality and moved to the origin), and passivity holds
without requirement. -/
@[powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Family.chain_le_semantics_iff.mpr fun s m hm => ?_
  rw [TMIO.mem_realize] at hm
  change ∀ q ∈ translate s, Meets m q at hm
  have hnone : (∀ q, Meets m q) → False := fun h => by
    have hm' : m ∈ TMIO.realize Meets Set.univ := (TMIO.mem_realize _ _ _).mpr fun q _ => h q
    rw [realize_univ] at hm'
    exact hm'
  rcases s with P | _
  · have hles : Meets m .equilibrium → Meets m .routh →
        LocallyExponentiallyStable m.field 0 := fun he hr =>
      family_isAutonomous.mem_den_flow.mp (les_of_meets he hr)
    rw [family_isAutonomous.mem_den_flow]
    cases P
    case lyapunovStable =>
      exact (hles (hm .equilibrium (by simp [translate]))
        (hm .routh (by simp [translate]))).lyapunovStable
    case locallyAsymptoticallyStable =>
      exact Flow.locallyExponentiallyStable_localAsymptoticStable
        (hles (hm .equilibrium (by simp [translate])) (hm .routh (by simp [translate])))
    case locallyExponentiallyStable =>
      exact hles (hm .equilibrium (by simp [translate])) (hm .routh (by simp [translate]))
    case unstable =>
      exact family_isAutonomous.mem_den_flow.mp (unstable_of_meets
        (hm .equilibrium (by simp [translate])) (hm .constNeg (by simp [translate])))
    all_goals exact (hnone fun q => hm q trivial).elim
  · rw [family_isAutonomous.den_passive]
    trivial

/-- Passivity is translated exactly: a system without ports is passive. -/
@[powerlib_domain] theorem exact_passive : connection% (family.Exact .passive) := by
  unfold powerlib.TMIO.Statement
  exact Family.exact_of_translate_eq_empty rfl family_isAutonomous.den_passive

/-! ### Stability of the operating point -/

/-- Four-state GFL (PLL + dc-voltage loop): the quartic Routh–Hurwitz conditions on the
coefficients of `det(λI − A₀)` place the operating point in local exponential stability. -/
@[powerlib_domain] theorem mem_den_locallyExponentiallyStable_of_routh (p : Params)
    (hC : p.C ≠ 0) {θ0 : ℝ} (heq : IsEq p θ0) (h3 : 0 < a3 p θ0) (h1 : 0 < a1 p θ0)
    (h0 : 0 < a0 p θ0) (hg : a1 p θ0 ^ 2 + a3 p θ0 ^ 2 * a0 p θ0 < a3 p θ0 * a2 p θ0 * a1 p θ0) :
    connection% (Model.mk p θ0 ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact les_of_meets ⟨heq, hC⟩ ⟨h3, h1, h0, hg⟩

/-- Four-state GFL: `cos 2θ₀ < 0` (operating angle beyond 45°) gives `a₀ = det A₀ < 0`, a
positive real eigenvalue, and instability of the physical field, for all positive `C, k_i, k_iv`. -/
@[powerlib_domain] theorem mem_den_unstable_of_cos_two_mul_neg (p : Params) (hC : 0 < p.C)
    (hki : 0 < p.ki) (hkiv : 0 < p.kiv) (hV0 : p.V0 ≠ 0) {θ0 : ℝ} (heq : IsEq p θ0)
    (hcos : Real.cos (2 * θ0) < 0) :
    connection% (Model.mk p θ0 ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  have hγ : 0 < p.γ := by unfold Params.γ; positivity
  refine unstable_of_meets ⟨heq, hC.ne'⟩ ?_
  show a0 p θ0 < 0
  rw [a0_eq p heq.1]
  have : 0 < p.γ * p.ki * p.kiv * p.V0 ^ 2 := by positivity
  nlinarith

/-- Beyond 45° (`cos 2θ₀ < 0`) the operating point is not Lyapunov stable. -/
@[powerlib_domain] theorem not_mem_den_lyapunovStable_of_cos_two_mul_neg (p : Params)
    (hC : 0 < p.C) (hki : 0 < p.ki) (hkiv : 0 < p.kiv) (hV0 : p.V0 ≠ 0) {θ0 : ℝ}
    (heq : IsEq p θ0) (hcos : Real.cos (2 * θ0) < 0) :
    connection% (Model.mk p θ0 ∉ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  have h := mem_den_unstable_of_cos_two_mul_neg p hC hki hkiv hV0 heq hcos
  unfold powerlib.TMIO.Statement at h
  rw [family_isAutonomous.mem_den_flow] at h ⊢
  exact h

/-- Necessary condition (the former `cos_two_mul_nonneg_of_locallyExponentiallyStable`, in
contrapositive form): if `cos 2θ₀ < 0` the operating point is not locally exponentially stable,
i.e. local exponential stability forces `cos 2θ₀ ≥ 0` (`|θ₀| ≤ 45°` on the principal branch). -/
@[powerlib_domain] theorem not_mem_den_locallyExponentiallyStable_of_cos_two_mul_neg (p : Params)
    (hC : 0 < p.C) (hki : 0 < p.ki) (hkiv : 0 < p.kiv) (hV0 : p.V0 ≠ 0) {θ0 : ℝ}
    (heq : IsEq p θ0) (hcos : Real.cos (2 * θ0) < 0) :
    connection% (Model.mk p θ0 ∉ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have h := not_mem_den_lyapunovStable_of_cos_two_mul_neg p hC hki hkiv hV0 heq hcos
  unfold powerlib.TMIO.Statement at h
  rw [family_isAutonomous.mem_den_flow] at h ⊢
  exact fun hs => h hs.lyapunovStable

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

/-! ### Exactness of the local exponential translation -/

/-- Without capacitance (`C = 0`) the dc-bus voltage is frozen: `V` is a linear first integral
of the regularized field, so it has no locally exponentially stable point. -/
private theorem not_les_regField_of_C_eq_zero {p : Params} (hC : p.C = 0) (x : Dynamics.State 4) :
    ¬ LocallyExponentiallyStable (regField p) x := by
  refine Dynamics.not_locallyExponentiallyStable_of_firstIntegral (contDiff_regField p)
    (PiLp.proj 2 (fun _ : Fin 4 => ℝ) 2) ?_ fun y => ?_
  · intro h
    have := congrArg (fun L : Dynamics.State 4 →L[ℝ] ℝ => L (EuclideanSpace.single 2 1)) h
    simp at this
  · simp [regField, Dynamics.lift, regCoordField, Params.γ, hC]

/-- Local exponential stability of the physical field at `(θ₀, 0, 1, 0)` is that of the
regularized field. -/
private theorem les_field_iff_regField {p : Params} {θ0 : ℝ} :
    LocallyExponentiallyStable (FourState.field p) (opPoint θ0) ↔
      LocallyExponentiallyStable (regField p) (opPoint θ0) :=
  ⟨Dynamics.locallyExponentiallyStable_of_eqOn_ball (by norm_num : (0 : ℝ) < 1 / 2)
      (fun y hy => (field_eq_regField_of_near p hy).symm),
    Dynamics.locallyExponentiallyStable_of_eqOn_ball (by norm_num : (0 : ℝ) < 1 / 2)
      (fun y hy => field_eq_regField_of_near p hy)⟩

/-- The local exponential translation is exact: a model is locally exponentially stable at
`(θ₀, 0, 1, 0)` exactly when the point is an equilibrium (`IsEq`, `C ≠ 0`) whose quartic
`det(λI − A₀)` meets the Routh conditions. Converse linearization of the regularized field
(which is the physical field on a ball around the point) and the quartic Routh–Hurwitz
criterion; with `C = 0` the frozen dc-bus voltage excludes local exponential stability. -/
@[powerlib_domain] theorem exact_locallyExponentiallyStable :
    connection% (family.Exact (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  ext m
  rw [TMIO.mem_realize]
  simp only [family, translate, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq]
  constructor
  · rintro ⟨he, hr⟩
    exact les_of_meets he hr
  · intro h
    have hles : LocallyExponentiallyStable (regField m.params) (opPoint m.θ) :=
      les_field_iff_regField.mp (mem_den_flow_iff.mp h)
    by_cases hC : m.params.C = 0
    · exact absurd hles (not_les_regField_of_C_eq_zero hC _)
    have h0 := Dynamics.isEquilibrium_of_locallyExponentiallyStable (contDiff_regField m.params)
      hles
    have heq : IsEq m.params m.θ := by
      rw [← isEq_iff m.params hC]
      rw [field_eq_regField_of_near m.params (by simp : ‖opPoint m.θ - opPoint m.θ‖ < 1 / 2)]
      exact h0
    have hA := Dynamics.isHurwitz_of_locallyExponentiallyStable _ (contDiff_regField m.params)
      (fderiv_regField_opPoint m.params m.θ) hles
    rw [Criteria.isHurwitz_iff_of_det_characteristicMatrix_quartic _
      (det_characteristicMatrix_A0_quartic m.params heq.1)] at hA
    exact ⟨⟨heq, hC⟩, hA⟩

/-! ### Instability away from equilibrium -/

/-- An unbalanced model: no ac source (`V₀ = 0`), unit capacitance and dc source current, all
gains and references zero, at `θ₀ = 0`; the dc-bus voltage ramps, `V̇ = I_dc0 / C = 1`. -/
def offEquilibrium : Model := ⟨⟨0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0⟩

/-- A point that is not an equilibrium is unstable: the solution through it leaves it (the field
is the smooth `regField` near the point). -/
@[powerlib_domain] theorem offEquilibrium_mem_den_unstable :
    connection% (offEquilibrium ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  refine mem_den_flow_iff.mpr (Dynamics.unstable_of_eqOn_ball (by norm_num : (0 : ℝ) < 1 / 2)
    (fun y hy => field_eq_regField_of_near _ hy)
    (Dynamics.unstable_of_ne_zero (contDiff_regField _) fun h => ?_))
  rw [← field_eq_regField _ (by simp [opPoint]; norm_num)] at h
  have := congrArg (fun y : Dynamics.State 4 => y 2) h
  simp [offEquilibrium, FourState.field, Dynamics.lift, coordField, opPoint, Params.γ] at this

/-- The instability translation is sound but not exact: instability is the failure of Lyapunov
stability, so the non-equilibrium point `offEquilibrium` is unstable, while the translation asks
for an equilibrium. -/
@[powerlib_domain] theorem not_exact_unstable :
    connection% (¬ family.Exact (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := offEquilibrium_mem_den_unstable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  have he : Meets offEquilibrium .equilibrium := hmem .equilibrium (by simp [family, translate])
  simp [Meets, IsEq, offEquilibrium] at he

/-! ### The Lyapunov translation -/

/-- Undamped PLL with a damped dc loop: `V₀ = k_i = 1`, `X_g = i_{d0} = k_p = I_dc0 = 0`,
`k_pv = k_iv = 1`, `C = 3/2` (so `γ = 1`), at `θ₀ = 0`. The field is the pendulum `θ̇ = x`,
`ẋ = −sin θ` driving the dc loop `V̇ = cos θ (−(V − 1) − η) / V`, `η̇ = V − 1`. -/
def undampedPLL : Model := ⟨⟨1, 0, 0, 0, 1, 1, 1, 3 / 2, 0⟩, 0⟩

private theorem undampedPLL_field (y : Dynamics.State 4) :
    FourState.field undampedPLL.params y = WithLp.toLp 2 ![y 1, -Real.sin (y 0),
      Real.cos (y 0) * (-(y 2 - 1) - y 3) / y 2, y 2 - 1] := by
  ext i
  fin_cases i <;> simp [FourState.field, Dynamics.lift, coordField, undampedPLL, vq, idc, Params.γ]
  ring

/-- The Lyapunov function `1 − cos θ + x²/2 + u² + u η + (3/2) η²`, `u = V − 1`. -/
private def lsEnergy (y : Dynamics.State 4) : ℝ :=
  1 - Real.cos (y 0) + 1 / 2 * y 1 ^ 2 + ((y 2 - 1) ^ 2 + (y 2 - 1) * y 3 + 3 / 2 * y 3 ^ 2)

private theorem lsEnergy_hasFDerivAt (z : Dynamics.State 4) :
    HasFDerivAt lsEnergy
      (Real.sin (z 0) • (PiLp.proj 2 (fun _ : Fin 4 => ℝ) 0 : Dynamics.State 4 →L[ℝ] ℝ) +
        z 1 • (PiLp.proj 2 (fun _ : Fin 4 => ℝ) 1 : Dynamics.State 4 →L[ℝ] ℝ) +
        (2 * (z 2 - 1) + z 3) • (PiLp.proj 2 (fun _ : Fin 4 => ℝ) 2 : Dynamics.State 4 →L[ℝ] ℝ) +
        ((z 2 - 1) + 3 * z 3) • (PiLp.proj 2 (fun _ : Fin 4 => ℝ) 3 :
          Dynamics.State 4 →L[ℝ] ℝ)) z := by
  have h0 := (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (0 : Fin 4) :
    Dynamics.State 4 →L[ℝ] ℝ).hasFDerivAt (x := z)
  have h1 := (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (1 : Fin 4) :
    Dynamics.State 4 →L[ℝ] ℝ).hasFDerivAt (x := z)
  have h2 := (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (2 : Fin 4) :
    Dynamics.State 4 →L[ℝ] ℝ).hasFDerivAt (x := z)
  have h3 := (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (3 : Fin 4) :
    Dynamics.State 4 →L[ℝ] ℝ).hasFDerivAt (x := z)
  have hc := (Real.hasDerivAt_cos (z 0)).comp_hasFDerivAt z h0
  have hu := h2.sub_const 1
  have h := (((hc.const_sub 1).add ((h1.pow 2).const_mul (1 / 2 : ℝ))).add
    (((hu.pow 2).add (hu.mul h3)).add ((h3.pow 2).const_mul (3 / 2 : ℝ))))
  refine h.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  simp
  ring

/-- The undamped PLL with a damped dc loop is Lyapunov stable at `(0, 0, 1, 0)`: the pendulum
energy `1 − cos θ + x²/2` of the PLL is conserved, and the dc quadratic `u² + u η + (3/2) η²`
(`u = V − 1`) does not increase while the loop gain `cos θ / V` stays in `[3/4, 5/4]`
(`|θ| < 1/2`, `|V − 1| < 1/10`). The cascade coupling `cos θ` therefore needs no separate
input-to-state argument: the sum is a local Lyapunov function. -/
@[powerlib_domain] theorem undampedPLL_mem_den_lyapunovStable :
    connection% (undampedPLL ∈ family.den (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  refine mem_den_flow_iff.mpr ?_
  change LyapunovStable _ _
  have hc0 : Continuous fun y : Dynamics.State 4 => y 0 :=
    (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (0 : Fin 4) : Dynamics.State 4 →L[ℝ] ℝ).continuous
  have hc2 : Continuous fun y : Dynamics.State 4 => y 2 :=
    (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (2 : Fin 4) : Dynamics.State 4 →L[ℝ] ℝ).continuous
  refine lyapunov_stable (V := lsEnergy)
    (D := {y | |y 0| < 1 / 2 ∧ |y 2 - 1| < 1 / 10}) (by norm_num)
    ⟨(isOpen_lt (continuous_abs.comp hc0) continuous_const).inter
        (isOpen_lt (continuous_abs.comp (hc2.sub continuous_const)) continuous_const),
      by simp [opPoint, undampedPLL],
      continuous_iff_continuousAt.mpr fun y => (lsEnergy_hasFDerivAt y).continuousAt,
      fun y => (lsEnergy_hasFDerivAt y).differentiableAt,
      by simp [lsEnergy, opPoint, undampedPLL], fun y hy hne => ?_, fun y hy => ?_⟩
  · obtain ⟨hy0, hy2⟩ := hy
    have hq : 0 ≤ (y 2 - 1) ^ 2 + (y 2 - 1) * y 3 + 3 / 2 * y 3 ^ 2 := by
      nlinarith [sq_nonneg (y 2 - 1 + y 3 / 2), sq_nonneg (y 3)]
    have hcos : Real.cos (y 0) ≤ 1 := Real.cos_le_one _
    have h1 : 0 ≤ 1 / 2 * y 1 ^ 2 := by positivity
    unfold lsEnergy
    by_cases h0 : y 0 = 0
    · by_cases h1' : y 1 = 0
      · have h23 : y 2 - 1 ≠ 0 ∨ y 3 ≠ 0 := by
          by_contra h
          push Not at h
          apply hne
          ext i
          fin_cases i
          · simp [opPoint, undampedPLL, h0]
          · simp [opPoint, undampedPLL, h1']
          · simp [opPoint, undampedPLL]; linarith [h.1]
          · simp [opPoint, undampedPLL, h.2]
        have hq' : 0 < (y 2 - 1) ^ 2 + (y 2 - 1) * y 3 + 3 / 2 * y 3 ^ 2 := by
          rcases h23 with h | h
          · have : 0 < (y 2 - 1) ^ 2 := by positivity
            nlinarith [sq_nonneg (y 2 - 1 + y 3 / 2), sq_nonneg (y 3)]
          · have : 0 < y 3 ^ 2 := by positivity
            nlinarith [sq_nonneg (y 2 - 1 + y 3 / 2), sq_nonneg (y 3)]
        linarith
      · have : 0 < 1 / 2 * y 1 ^ 2 := by positivity
        linarith
    · have hlt : Real.cos (y 0) < 1 := by
        have := Real.one_sub_sq_div_two_lt_cos h0
        refine lt_of_le_of_ne hcos fun h => h0 ?_
        refine (Real.cos_eq_one_iff_of_lt_of_lt ?_ ?_).mp h
        · linarith [neg_abs_le (y 0), Real.two_le_pi]
        · linarith [le_abs_self (y 0), Real.two_le_pi]
      linarith
  · obtain ⟨hy0, hy2⟩ := hy
    rw [(lsEnergy_hasFDerivAt y).fderiv, undampedPLL_field]
    simp
    have hθ := abs_lt.mp hy0
    have hV := abs_lt.mp hy2
    have hVpos : 0 < y 2 := by linarith
    have hcl : 7 / 8 ≤ Real.cos (y 0) := by
      have := Real.one_sub_sq_div_two_le_cos (x := y 0)
      nlinarith
    have hcu : Real.cos (y 0) ≤ 1 := Real.cos_le_one _
    set c := Real.cos (y 0)
    set u := y 2 - 1 with hu
    set e := y 3
    have hkey : 0 ≤ c * (2 * u ^ 2 + 3 * u * e + e ^ 2) - y 2 * (u ^ 2 + 3 * u * e) := by
      have hV' : y 2 = u + 1 := by rw [hu]; ring
      rw [hV']
      nlinarith [sq_nonneg (u - e), sq_nonneg (u + e), mul_nonneg (sub_nonneg.2 hcl)
        (sq_nonneg u), mul_nonneg (sub_nonneg.2 hcl) (sq_nonneg e),
        mul_nonneg (sub_nonneg.2 hcu) (sq_nonneg u), mul_nonneg (sub_nonneg.2 hcu) (sq_nonneg e),
        mul_nonneg (sub_nonneg.2 hcl) (sq_nonneg (u + e)), mul_nonneg (sub_nonneg.2 hcu)
        (sq_nonneg (u + e)), mul_nonneg (sub_nonneg.2 hcl) (sq_nonneg (u - e)),
        mul_nonneg (sub_nonneg.2 hcu) (sq_nonneg (u - e))]
    have hgoal : Real.sin (y 0) * y 1 + -(y 1 * Real.sin (y 0)) +
        (2 * u + e) * (c * (1 - y 2 - e) / y 2) + (u + 3 * e) * u =
        -(c * (2 * u ^ 2 + 3 * u * e + e ^ 2) - y 2 * (u ^ 2 + 3 * u * e)) / y 2 := by
      rw [hu]
      field_simp
      ring
    rw [hgoal]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hVpos.le

/-- The Lyapunov translation is sound but not exact: `undampedPLL` is Lyapunov stable, but its
quartic `(λ² + 1)(λ² + λ + 1)` has the imaginary pair `±i`, so the Routh inequality
`a₁² + a₃² a₀ < a₃ a₂ a₁` fails with equality (`2 = 2`). -/
@[powerlib_domain] theorem not_exact_lyapunovStable :
    connection% (¬ family.Exact (.flow .lyapunovStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  have hmem := undampedPLL_mem_den_lyapunovStable
  unfold powerlib.TMIO.Statement at hmem
  rw [← h, TMIO.mem_realize] at hmem
  obtain ⟨-, -, -, hg⟩ : Meets undampedPLL .routh := hmem .routh (by simp [family, translate])
  norm_num [a1, a2, a3, a0, twoAlphaCl, omegaClSq, Γc, vd0, undampedPLL, Params.γ] at hg


end powerlib.GFLParametric.FourState
