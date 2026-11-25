import theorem.GridTiedConverter.GFM.PSCVoltage
import theorem.ParametricResonance.SmoothForcedOrbit

/-! # PSC with active damping under grid-voltage modulation: the real model, its forced orbit and Floquet multipliers

End-to-end statement for the four-state PSC of `PSCFull` driven through the grid-voltage
magnitude. The real field in the states `(δ, p_f, ℓ_d, ℓ_q)` is defined from the model functions
(`rfield`); its partial Jacobian, its second derivatives along a state direction and in the
voltage, and its voltage input are derived from the complexified model of `PSCFull` and
`PSCVoltage` through `x ↦ R x = (δ, p_f, ℓ, ℓ̄)` (`rfield_lift`). Hence `SmoothForcedOrbit`
applies: at the Hopf point of the core the forced orbit exists for small `ε`, and its Floquet
multipliers are inside or outside the unit circle according to `|g_V/2| ≶ |λ₁|`, with the exact
voltage pump `g_V = u_{p_f} ω_f V̂ G_V(2jΩ, −jΩ, jΩ)` of `PSCVoltage`.

Model boundary.
* `PSCFull.Model` with the grid-voltage magnitude `V` as input (`withV`), no grid-frequency input,
  PCC power `Re(u ī)`, quasi-static network, constant `E` (`rfield`); `E`, `V`, impedances real;
  `Z ≠ 0`, `Z₀ ≠ 0`.
* Operating point `x₀ = (δ₀, p*, Re ℓ₀, Im ℓ₀)` with `p* = Re(u ī)` at `(δ₀, ℓ₀)` (`xeq`, `Peq`);
  drive `V = V + ε V̂ cos 2Ωt`; state perturbation `ε A₀'` with any real `A₀'`; the core at a Hopf
  point `D(jΩ) = 0` (`D`, `D'` and the branch denominators nonzero at `jΩ`, and `D(2jΩ) ≠ 0`).
* The stable two-dimensional subspace of `Jreal` is given by a real basis `W` with
  `Jreal W = W A_s`, a left inverse `W'` annihilating the critical pair, and
  `‖e^{T A_s}‖ < 1` (`∞`-operator norm, `T = π/Ω`): these are hypotheses, not computed in closed
  form. Orbital stability of the nonlinear solutions is not derived.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1–§2.2 (first-order averaging along the forced trajectory), §3 (PSC
core), `verification/check_psc.py`; the voltage excitation is new.

Results.
* `realifyInv_conj`, `realify_ofv`, `realify_mul_realifyInv`, `realify_ofv_line` — the coordinates.
* `rfield`, `rfield_lift` — `rfield(x, V) = R⁻¹ f_V(R x)`; `contDiff_rfield` — the field is smooth.
* `Jgen`, `Jgen_eq`, `line_pw`, `hasDerivAt_real0`, `field_line`, `matX_rfield` —
  `∂ₓ rfield(x, V) = R⁻¹ J_V(R x) R` at every state.
* `Jgen_line`, `withV_consts`, `Jgen_lineV`, `field_lineV` — `A₁`, `G_V`, `B_V` as derivatives of
  the general Jacobian and of the field.
* `Peq`, `xeq`, `re_add_I_im`, `realify_xeq`, `rfield_eq_zero`, `Jreal`, `matX_rfield_eq`,
  `matX_eq_Jreal`, `smDx_rfield`, `smM1_rfield`, `fderivW_rfield` — the equilibrium and the data
  of the forced system.
* `Coeffs.A1lin`, `rmode`, `umode`, `shift`, `pumpV`, `zorb`, `modes`, `zorb_eq`, `smA1_rfield`,
  `pump_rfield` — eigen-data, first-order orbit and `u A₁ r̄ = g_V`; `modal_rfield` — real modal
  coordinates.
* `orbit_voltage_stable`, `orbit_voltage_unstable` — the end-to-end Floquet statements.

Corrections.
None: an extension. The relation between the real Jacobian and the Jacobian in the coordinates
`(δ, p_f, ℓ, ℓ̄)`, used in `PSCFull` as the definition of those coordinates, is derived here from
the real field (`matX_rfield_eq`).

Family and connection conclusions.
None: static evidence on the voltage-modulated PSC (forced orbit, Floquet multipliers).
-/

noncomputable section

namespace powerlib.GFM
namespace PSCFull
open Complex ComplexConjugate Matrix
open powerlib.ParametricResonance.ForcedOrbit (ofv)
open Filter Topology
open scoped Matrix.Norms.Operator

/-- `R⁻¹ (a, b, c, c̄) = (a, b, Re c, Im c)`. -/
@[tmio T, powerlib_foundation] theorem realifyInv_conj (a b c : ℂ) :
    realifyInv *ᵥ ![a, b, c, conj c] = ![a, b, (c.re : ℂ), (c.im : ℂ)] := by
  funext i
  fin_cases i <;> simp [realifyInv, mulVec, dotProduct, Fin.sum_univ_four]
  · apply Complex.ext <;> simp; ring
  · apply Complex.ext <;> simp <;> ring

/-- `R (x₀, x₁, x₂, x₃) = (x₀, x₁, x₂ + j x₃, x₂ − j x₃)` on real vectors. -/
@[tmio T, powerlib_foundation] theorem realify_ofv (x : Fin 4 → ℝ) :
    realify *ᵥ ofv x = ![(x 0 : ℂ), (x 1 : ℂ), (x 2 : ℂ) + I * (x 3 : ℂ),
      conj ((x 2 : ℂ) + I * (x 3 : ℂ))] := by
  funext i
  fin_cases i <;> simp [realify, ofv, mulVec, dotProduct, Fin.sum_univ_four]

@[tmio T, powerlib_foundation] theorem realify_mul_realifyInv : realify * realifyInv = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 realifyInv_mul

namespace Coeffs

/-- `A₁` is complex-linear in the direction. -/
def A1lin (q : Coeffs) : (Fin 4 → ℂ) →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ where
  toFun := q.A1
  map_add' a b := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [A1] <;> ring
  map_smul' c a := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [A1] <;> ring

end Coeffs

namespace Model

variable (p : Model)

/-- The real field of the PSC with active damping in the states `x = (δ, p_f, ℓ_d, ℓ_q)` with the
grid-voltage magnitude `V` as input: `δ̇ = k(p* − p_f)`, `ṗ_f = ω_f(Re(u ī) − p_f)`,
`ℓ̇ = α_d(i − ℓ)`, `ℓ = ℓ_d + jℓ_q`, with `i`, `u` of the model with grid voltage `V`. -/
def rfield (Pref : ℝ) (q : (Fin 4 → ℝ) × ℝ) : Fin 4 → ℝ :=
  ![p.k * (Pref - q.1 1),
    p.ωf * (((p.withV q.2).volt (q.1 0) ((q.1 2 : ℂ) + I * (q.1 3 : ℂ)) *
      conj ((p.withV q.2).cur (q.1 0) ((q.1 2 : ℂ) + I * (q.1 3 : ℂ)))).re - q.1 1),
    p.αd * (((p.withV q.2).cur (q.1 0) ((q.1 2 : ℂ) + I * (q.1 3 : ℂ))).re - q.1 2),
    p.αd * (((p.withV q.2).cur (q.1 0) ((q.1 2 : ℂ) + I * (q.1 3 : ℂ))).im - q.1 3)]

/-- The real field is the complexified field in the coordinates `(δ, p_f, ℓ, ℓ̄)`:
`rfield(x, V) = R⁻¹ f_V(R x)` (without grid-frequency input). -/
@[tmio M, powerlib_domain] theorem rfield_lift (Pref : ℝ) (x : Fin 4 → ℝ) (V : ℝ) :
    ofv (p.rfield Pref (x, V)) = realifyInv *ᵥ (p.withV V).field 0 Pref (realify *ᵥ ofv x) := by
  rw [realify_ofv]
  set ℓ : ℂ := (x 2 : ℂ) + I * (x 3 : ℂ) with hℓ
  have hf : (p.withV V).field 0 Pref ![(x 0 : ℂ), (x 1 : ℂ), ℓ, conj ℓ] =
      ![(p.k : ℂ) * (Pref - x 1), p.ωf * (((p.withV V).volt (x 0) ℓ *
          conj ((p.withV V).cur (x 0) ℓ)).re - x 1),
        p.αd * ((p.withV V).cur (x 0) ℓ - ℓ), conj (p.αd * ((p.withV V).cur (x 0) ℓ - ℓ))] := by
    funext i
    fin_cases i
    · simp [field, withV]
    · simp only [field, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      rw [(p.withV V).pw_real]; rfl
    · simp [field, withV]
    · show ((p.withV V).αd : ℂ) * ((p.withV V).curt (x 0 : ℂ) (conj ℓ) - conj ℓ) =
        conj (p.αd * ((p.withV V).cur (x 0) ℓ - ℓ))
      rw [(p.withV V).curt_real, map_mul, map_sub, conj_ofReal]; rfl
  rw [hf, realifyInv_conj]
  funext i
  fin_cases i <;> simp [rfield, ofv, hℓ]

/-- The real field is smooth. -/
@[tmio M, powerlib_domain] theorem contDiff_rfield (Pref : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (p.rfield Pref) := by
  have hc : ∀ q : (Fin 4 → ℝ) × ℝ, (p.withV q.2).cur (q.1 0) ((q.1 2 : ℂ) + I * (q.1 3 : ℂ)) =
      (p.E + p.ra * ((q.1 2 : ℂ) + I * (q.1 3 : ℂ)) - (q.2 : ℂ) * exp (-((q.1 0 : ℂ) * I))) /
        p.Z := fun q => rfl
  have hv : ∀ q : (Fin 4 → ℝ) × ℝ, (p.withV q.2).volt (q.1 0) ((q.1 2 : ℂ) + I * (q.1 3 : ℂ)) =
      (q.2 : ℂ) * exp (-((q.1 0 : ℂ) * I)) + p.Zg *
        ((p.E + p.ra * ((q.1 2 : ℂ) + I * (q.1 3 : ℂ)) - (q.2 : ℂ) * exp (-((q.1 0 : ℂ) * I))) /
          p.Z) := fun q => rfl
  have hC : ContDiff ℝ n fun q : (Fin 4 → ℝ) × ℝ =>
      (p.E + p.ra * ((q.1 2 : ℂ) + I * (q.1 3 : ℂ)) - (q.2 : ℂ) * exp (-((q.1 0 : ℂ) * I))) /
        p.Z := by
    have h0 : ContDiff ℝ n fun q : (Fin 4 → ℝ) × ℝ => ((q.1 0 : ℝ) : ℂ) :=
      ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ 0).comp contDiff_fst)
    have h2 : ContDiff ℝ n fun q : (Fin 4 → ℝ) × ℝ => ((q.1 2 : ℝ) : ℂ) :=
      ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ 2).comp contDiff_fst)
    have h3 : ContDiff ℝ n fun q : (Fin 4 → ℝ) × ℝ => ((q.1 3 : ℝ) : ℂ) :=
      ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ 3).comp contDiff_fst)
    have hV : ContDiff ℝ n fun q : (Fin 4 → ℝ) × ℝ => ((q.2 : ℝ) : ℂ) :=
      ofRealCLM.contDiff.comp contDiff_snd
    have he : ContDiff ℝ n fun q : (Fin 4 → ℝ) × ℝ => exp (-((q.1 0 : ℂ) * I)) :=
      Complex.contDiff_exp.comp (h0.mul contDiff_const).neg
    exact ((contDiff_const.add (contDiff_const.mul (h2.add (contDiff_const.mul h3)))).sub
      (hV.mul he)).div_const _
  have hV' : ContDiff ℝ n fun q : (Fin 4 → ℝ) × ℝ =>
      (q.2 : ℂ) * exp (-((q.1 0 : ℂ) * I)) + p.Zg *
        ((p.E + p.ra * ((q.1 2 : ℂ) + I * (q.1 3 : ℂ)) - (q.2 : ℂ) * exp (-((q.1 0 : ℂ) * I))) /
          p.Z) := by
    have h0 : ContDiff ℝ n fun q : (Fin 4 → ℝ) × ℝ => ((q.1 0 : ℝ) : ℂ) :=
      ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ 0).comp contDiff_fst)
    have hV : ContDiff ℝ n fun q : (Fin 4 → ℝ) × ℝ => ((q.2 : ℝ) : ℂ) :=
      ofRealCLM.contDiff.comp contDiff_snd
    exact (hV.mul (Complex.contDiff_exp.comp (h0.mul contDiff_const).neg)).add
      (contDiff_const.mul hC)
  have hre := reCLM.contDiff.comp ((hV').mul (conjCLE.contDiff.comp hC))
  have hcr := reCLM.contDiff.comp hC
  have hci := imCLM.contDiff.comp hC
  have hx : ∀ i : Fin 4, ContDiff ℝ n fun q : (Fin 4 → ℝ) × ℝ => q.1 i := fun i =>
    (contDiff_apply ℝ ℝ i).comp contDiff_fst
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact contDiff_const.mul (contDiff_const.sub (hx 1))
  · simp only [rfield, hc, hv]
    exact contDiff_const.mul (hre.sub (hx 1))
  · simp only [rfield, hc]
    exact contDiff_const.mul (hcr.sub (hx 2))
  · simp only [rfield, hc]
    exact contDiff_const.mul (hci.sub (hx 3))

/-- The Jacobian of the complexified field at an arbitrary state `z = (δ, p_f, ℓ, ℓ̄)`. -/
def Jgen (z : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, -p.k, 0, 0;
    p.ωf * p.pwδ (z 0) (z 2) (z 3), -p.ωf, p.ωf * p.pwℓ (z 0) (z 3), p.ωf * p.pwm (z 0) (z 2);
    p.αd * p.curδ (z 0), 0, p.αd * (p.ra / p.Z - 1), 0;
    p.αd * p.curtδ (z 0), 0, 0, p.αd * (p.ra / p.Zc - 1)]

/-- At the equilibrium state the general Jacobian is the core Jacobian `J` of `coeffs`. -/
@[tmio M, powerlib_domain] theorem Jgen_eq (δ0 pf : ℂ) :
    p.Jgen ![δ0, pf, p.ell0 δ0, p.m0 δ0] = (p.coeffs δ0).J := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Jgen, Coeffs.J, coeffs]

/-- The power along a line: `d/dt p(δ + t z_δ, ℓ + t z_ℓ, ℓ̄ + t z_ℓ̄) = P_δ z_δ + P_ℓ z_ℓ + P_ℓ̄ z_ℓ̄`. -/
@[tmio M, powerlib_domain] theorem line_pw (δ ℓ m zδ zℓ zm : ℂ) :
    HasDerivAt (fun t => p.pw (δ + t * zδ) (ℓ + t * zℓ) (m + t * zm))
      (p.pwδ δ ℓ m * zδ + p.pwℓ δ m * zℓ + p.pwm δ ℓ * zm) 0 := by
  have hφ := p.line_φ δ zδ 0
  have hφt := p.line_φt δ zδ 0
  have hc := p.line_cur δ ℓ zδ zℓ 0
  have hct := p.line_curt δ m zδ zm 0
  simp only [zero_mul, add_zero] at hφ hφt hc hct
  have h := (((hφ.mul hct).add (hφt.mul hc)).div_const 2).add
    ((hc.mul hct).const_mul (p.Rg : ℂ))
  convert h using 1
  · funext t; simp only [Pi.add_apply, Pi.mul_apply]; rw [pw_eq]; ring
  · simp only [pwδ, pwℓ, pwm]; ring_nf

/-- Real-parameter restriction of a complex line derivative at `0`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_real0 {e : ℂ → ℂ} {e' : ℂ}
    (h : HasDerivAt e e' 0) : HasDerivAt (fun t : ℝ => e t) e' 0 :=
  HasDerivAt.comp_ofReal (by simpa using h)

/-- The complexified field along a real line: `d/ds f(z + s w) = J(z) w`. -/
@[tmio M, powerlib_domain] theorem field_line (Pref : ℝ) (z w : Fin 4 → ℂ) :
    HasDerivAt (fun s : ℝ => p.field 0 Pref (z + (s : ℂ) • w)) (p.Jgen z *ᵥ w) 0 := by
  have hl : ∀ a b : ℂ, HasDerivAt (fun t : ℂ => a + t * b) b 0 := fun a b => by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const b).const_add a
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · have h := hasDerivAt_real0 (((hl (z 1) (w 1)).const_sub (Pref : ℂ)).const_mul (p.k : ℂ))
    convert h.sub_const ((0 : ℝ) : ℂ) using 1
    · funext s; simp [field]
    · simp [Jgen, mulVec, dotProduct, Fin.sum_univ_four]
  · have h := hasDerivAt_real0 (((p.line_pw (z 0) (z 2) (z 3) (w 0) (w 2) (w 3)).sub
      (hl (z 1) (w 1))).const_mul (p.ωf : ℂ))
    convert h using 1
    · funext s; simp [field]
    · simp [Jgen, mulVec, dotProduct, Fin.sum_univ_four]; ring
  · have h := hasDerivAt_real0 (((p.line_cur (z 0) (z 2) (w 0) (w 2) 0).sub
      (hl (z 2) (w 2))).const_mul (p.αd : ℂ))
    convert h using 1
    · funext s; simp [field]
    · simp [Jgen, mulVec, dotProduct, Fin.sum_univ_four]; ring
  · have h := hasDerivAt_real0 (((p.line_curt (z 0) (z 3) (w 0) (w 3) 0).sub
      (hl (z 3) (w 3))).const_mul (p.αd : ℂ))
    convert h using 1
    · funext s; simp [field]
    · simp [Jgen, mulVec, dotProduct, Fin.sum_univ_four]; ring

@[tmio T, powerlib_foundation] theorem realify_ofv_line (x y : Fin 4 → ℝ) (s : ℝ) :
    realify *ᵥ ofv (x + s • y) = realify *ᵥ ofv x + (s : ℂ) • (realify *ᵥ ofv y) := by
  have : ofv (x + s • y) = ofv x + (s : ℂ) • ofv y := by
    funext i; simp [ofv]
  rw [this, Matrix.mulVec_add, Matrix.mulVec_smul]

/-- The Jacobian of the real field: `∂ₓ rfield(x, V) = R⁻¹ J_V(R x) R`. -/
@[tmio M, powerlib_domain] theorem matX_rfield (Pref : ℝ) (x : Fin 4 → ℝ) (V : ℝ) :
    (ParametricResonance.ForcedOrbit.matX (p.rfield Pref) (x, V)).map (algebraMap ℝ ℂ) =
      realifyInv * (p.withV V).Jgen (realify *ᵥ ofv x) * realify := by
  refine ParametricResonance.ForcedOrbit.matX_of_lift
    ((p.contDiff_rfield Pref (n := 1)).differentiable one_ne_zero _) fun y => ?_
  have e : (fun s : ℝ => ofv (p.rfield Pref ((x, V).1 + s • y, (x, V).2))) =
      fun s : ℝ => realifyInv *ᵥ (p.withV V).field 0 Pref
        (realify *ᵥ ofv x + (s : ℂ) • (realify *ᵥ ofv y)) := by
    funext s; rw [p.rfield_lift, realify_ofv_line]
  rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact ParametricResonance.ForcedOrbit.hasDerivAt_mulVec_c realifyInv
    ((p.withV V).field_line Pref _ _)

/-- The modulation `A₁ = DJ[w]` is the derivative of the Jacobian along `z₀ + t w` at the
equilibrium state. -/
@[tmio M, powerlib_domain] theorem Jgen_line (δ0 pf : ℂ) (w : Fin 4 → ℂ) (i j : Fin 4) :
    HasDerivAt (fun t : ℝ => p.Jgen (![δ0, pf, p.ell0 δ0, p.m0 δ0] + (t : ℂ) • w) i j)
      ((p.coeffs δ0).A1 w i j) 0 := by
  fin_cases i <;> fin_cases j <;> simp [Jgen, Coeffs.A1, coeffs]
  all_goals (try exact hasDerivAt_const _ _)
  · exact (hasDerivAt_real0 (p.line_pwδ _ _ _ _ _ _)).const_mul _
  · exact (hasDerivAt_real0 (p.line_pwℓ _ _ _ _)).const_mul _
  · exact (hasDerivAt_real0 (p.line_pwm _ _ _ _)).const_mul _
  · convert (hasDerivAt_real0 (p.line_curδ0 δ0 (w 0))).const_mul (p.αd : ℂ) using 1; ring
  · convert (hasDerivAt_real0 (p.line_curtδ0 δ0 (w 0))).const_mul (p.αd : ℂ) using 1; ring

@[tmio M, powerlib_domain] theorem withV_consts (V' : ℝ) :
    (p.withV V').k = p.k ∧ (p.withV V').ωf = p.ωf ∧ (p.withV V').αd = p.αd ∧
      (p.withV V').ra = p.ra ∧ (p.withV V').Z = p.Z ∧ (p.withV V').Zc = p.Zc :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The direct voltage modulation `G_V = ∂J/∂V` is the derivative of the Jacobian in the grid
voltage at the equilibrium state. -/
@[tmio M, powerlib_domain] theorem Jgen_lineV (δ0 pf : ℂ) (i j : Fin 4) :
    HasDerivAt (fun t : ℝ => (p.withV (p.V + t)).Jgen ![δ0, pf, p.ell0 δ0, p.m0 δ0] i j)
      ((p.coeffs δ0).GV (p.vin δ0) i j) 0 := by
  have sh : ∀ {f : ℝ → ℂ} {f' : ℂ}, HasDerivAt f f' p.V →
      HasDerivAt (fun t : ℝ => f (p.V + t)) f' 0 := fun h =>
    HasDerivAt.comp_const_add p.V 0 (by simpa using h)
  have hk : ∀ V', (p.withV V').k = p.k := fun V' => (p.withV_consts V').1
  have hω : ∀ V', (p.withV V').ωf = p.ωf := fun V' => (p.withV_consts V').2.1
  have hα : ∀ V', (p.withV V').αd = p.αd := fun V' => (p.withV_consts V').2.2.1
  have hra : ∀ V', (p.withV V').ra = p.ra := fun V' => (p.withV_consts V').2.2.2.1
  have hZ : ∀ V', (p.withV V').Z = p.Z := fun V' => (p.withV_consts V').2.2.2.2.1
  have hZc : ∀ V', (p.withV V').Zc = p.Zc := fun V' => (p.withV_consts V').2.2.2.2.2
  fin_cases i <;> fin_cases j <;> simp [Jgen, Coeffs.GV, vin, coeffs, hk, hω, hα, hra, hZ, hZc]
  all_goals (try exact hasDerivAt_const _ _)
  · exact (sh (p.hasDerivAt_pwδ_V δ0 (p.ell0 δ0) (p.m0 δ0))).const_mul _
  · exact (sh (p.hasDerivAt_pwℓ_V (δ := δ0) (m := p.m0 δ0) (V0 := p.V))).const_mul _
  · exact (sh (p.hasDerivAt_pwm_V (δ := δ0) (ℓ := p.ell0 δ0) (V0 := p.V))).const_mul _
  · exact (sh (p.hasDerivAt_curδ_V (δ := δ0) (V0 := p.V))).const_mul _
  · exact (sh (p.hasDerivAt_curtδ_V (δ := δ0) (V0 := p.V))).const_mul _

/-- The voltage input `B_V = ∂f/∂V` is the derivative of the field in the grid voltage at the
equilibrium state. -/
@[tmio M, powerlib_domain] theorem field_lineV (Pref : ℝ) (δ0 pf : ℂ) :
    HasDerivAt (fun t : ℝ => (p.withV (p.V + t)).field 0 Pref ![δ0, pf, p.ell0 δ0, p.m0 δ0])
      ((p.coeffs δ0).Bv (p.vin δ0)) 0 := by
  have sh : ∀ {f : ℝ → ℂ} {f' : ℂ}, HasDerivAt f f' p.V →
      HasDerivAt (fun t : ℝ => f (p.V + t)) f' 0 := fun h =>
    HasDerivAt.comp_const_add p.V 0 (by simpa using h)
  obtain ⟨d1, d2, d3⟩ := p.hasDerivAt_field_V 0 Pref ![δ0, pf, p.ell0 δ0, p.m0 δ0]
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · exact hasDerivAt_const (0 : ℝ) ((p.k : ℂ) * (Pref - pf) - ((0 : ℝ) : ℂ))
  · exact sh d1
  · exact sh d2
  · exact sh d3

/-- The equilibrium power `p* = Re(u ī)` at `(δ₀, ℓ₀)`. -/
def Peq (δ0 : ℝ) : ℝ := (p.volt δ0 (p.ell0 δ0) * conj (p.cur δ0 (p.ell0 δ0))).re

/-- The equilibrium state `x₀ = (δ₀, p*, Re ℓ₀, Im ℓ₀)`. -/
def xeq (δ0 : ℝ) : Fin 4 → ℝ := ![δ0, p.Peq δ0, (p.ell0 δ0).re, (p.ell0 δ0).im]

omit p in
@[tmio T, powerlib_foundation] theorem re_add_I_im (z : ℂ) : (z.re : ℂ) + I * (z.im : ℂ) = z := by
  rw [mul_comm]; exact re_add_im z

@[tmio M, powerlib_domain] theorem realify_xeq (δ0 : ℝ) :
    realify *ᵥ ofv (p.xeq δ0) = ![(δ0 : ℂ), (p.Peq δ0 : ℂ), p.ell0 δ0, p.m0 δ0] := by
  rw [realify_ofv]
  funext i
  fin_cases i <;> simp [xeq, re_add_I_im, p.m0_real]

/-- `x₀` is an equilibrium of the real field with `p* = Peq δ₀` and the nominal grid voltage. -/
@[tmio M, powerlib_domain] theorem rfield_eq_zero (δ0 : ℝ) (hZ : p.Z ≠ 0) (hZ0 : p.Z0 ≠ 0) :
    p.rfield (p.Peq δ0) (p.xeq δ0, p.V) = 0 := by
  have hc := p.cur_ell0 δ0 hZ hZ0
  funext i
  fin_cases i <;> simp [rfield, xeq, re_add_I_im, withV_self, hc, Peq]

/-- The real Jacobian of the core: `R⁻¹ J R`, a real matrix. -/
def Jreal (δ0 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (realifyInv * (p.coeffs δ0).J * realify).map Complex.re

@[tmio M, powerlib_domain] theorem matX_rfield_eq (Pref δ0 : ℝ) :
    (ParametricResonance.ForcedOrbit.matX (p.rfield Pref) (p.xeq δ0, p.V)).map
      (algebraMap ℝ ℂ) = realifyInv * (p.coeffs δ0).J * realify := by
  rw [p.matX_rfield, withV_self, realify_xeq, Jgen_eq]

/-- The partial Jacobian of the real field at the equilibrium is `Jreal`. -/
@[tmio M, powerlib_domain] theorem matX_eq_Jreal (Pref δ0 : ℝ) :
    ParametricResonance.ForcedOrbit.matX (p.rfield Pref) (p.xeq δ0, p.V) = p.Jreal δ0 := by
  ext i j
  have h := congrFun (congrFun (p.matX_rfield_eq Pref δ0) i) j
  simp only [Matrix.map_apply] at h
  simp [Jreal, ← h]

/-- The second derivative of the real field along `y` is the core modulation in the coordinates
`(δ, p_f, ℓ, ℓ̄)`: `D_x(∂ₓ rfield)(x₀) y = R⁻¹ A₁(R y) R`. -/
@[tmio M, powerlib_domain] theorem smDx_rfield (Pref δ0 : ℝ) (y : Fin 4 → ℝ) :
    (ParametricResonance.ForcedOrbit.smDx (p.rfield Pref) (p.xeq δ0, p.V) y).map
      (algebraMap ℝ ℂ) = realifyInv * (p.coeffs δ0).A1 (realify *ᵥ ofv y) * realify := by
  refine ParametricResonance.ForcedOrbit.smDx_of_lift (p.contDiff_rfield Pref).contDiffAt y
    (Jc := fun t => realifyInv * p.Jgen (![(δ0 : ℂ), (p.Peq δ0 : ℂ), p.ell0 δ0, p.m0 δ0] +
      (t : ℂ) • (realify *ᵥ ofv y)) * realify)
    (Filter.Eventually.of_forall fun t => ?_)
    (fun i j => ParametricResonance.ForcedOrbit.hasDerivAt_conj_entries
      (fun i j => p.Jgen_line _ _ _ i j) _ _ i j)
  dsimp only
  rw [p.matX_rfield, withV_self, realify_ofv_line, realify_xeq]

/-- The mixed second derivative in the grid voltage is the direct voltage modulation:
`D_V(∂ₓ rfield)(x₀) = R⁻¹ G_V R`. -/
@[tmio M, powerlib_domain] theorem smM1_rfield (Pref δ0 : ℝ) :
    (ParametricResonance.ForcedOrbit.smM1 (p.rfield Pref) (p.xeq δ0, p.V)).map
      (algebraMap ℝ ℂ) = realifyInv * (p.coeffs δ0).GV (p.vin δ0) * realify := by
  refine ParametricResonance.ForcedOrbit.smM1_of_lift (p.contDiff_rfield Pref).contDiffAt
    (Jc := fun t => realifyInv * (p.withV (p.V + t)).Jgen
      ![(δ0 : ℂ), (p.Peq δ0 : ℂ), p.ell0 δ0, p.m0 δ0] * realify)
    (Filter.Eventually.of_forall fun t => ?_)
    (fun i j => ParametricResonance.ForcedOrbit.hasDerivAt_conj_entries
      (fun i j => p.Jgen_lineV _ _ i j) _ _ i j)
  dsimp only
  rw [p.matX_rfield, realify_xeq]

/-- The voltage input of the real field: `∂_V rfield(x₀) = R⁻¹ B_V`. -/
@[tmio M, powerlib_domain] theorem fderivW_rfield (Pref δ0 : ℝ) :
    ofv (fderiv ℝ (p.rfield Pref) (p.xeq δ0, p.V) (0, 1)) =
      realifyInv *ᵥ (p.coeffs δ0).Bv (p.vin δ0) := by
  refine ParametricResonance.ForcedOrbit.fderivW_of_lift
    ((p.contDiff_rfield Pref (n := 1)).differentiable one_ne_zero _) ?_
  have e : (fun s : ℝ => ofv (p.rfield Pref ((p.xeq δ0, p.V).1, (p.xeq δ0, p.V).2 + s))) =
      fun s => realifyInv *ᵥ (p.withV (p.V + s)).field 0 Pref
        ![(δ0 : ℂ), (p.Peq δ0 : ℂ), p.ell0 δ0, p.m0 δ0] := by
    funext s; dsimp only; rw [p.rfield_lift, realify_xeq]
  rw [e]
  exact ParametricResonance.ForcedOrbit.hasDerivAt_mulVec_c _ (p.field_lineV Pref _ _)

/-- The pair `±jΩ` in the real coordinates: right eigenvector `r = R⁻¹ r_c(jΩ)`. -/
def rmode (δ0 Ω : ℝ) : Fin 4 → ℂ := realifyInv *ᵥ (p.coeffs δ0).right ((Ω : ℂ) * I)

/-- Left eigenvector `u = u_c(jΩ) R`. -/
def umode (δ0 Ω : ℝ) : Fin 4 → ℂ := (p.coeffs δ0).left ((Ω : ℂ) * I) ᵥ* realify

/-- The shift `λ₁ = u A₀' r` of the pair by the state-matrix perturbation `A₀'`. -/
def shift (δ0 Ω : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ) : ℂ :=
  p.umode δ0 Ω ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ p.rmode δ0 Ω)

/-- The closed-form voltage pump `g_V = u_{p_f} ω_f V̂ G_V(2jΩ, −jΩ, jΩ)` (`PSCVoltage`). -/
def pumpV (δ0 Ω Vh : ℝ) : ℂ :=
  (-(p.k : ℂ) / (p.coeffs δ0).Dd ((Ω : ℂ) * I)) * p.ωf * Vh *
    (p.coeffs δ0).GVb (p.vin δ0) (((2 * Ω : ℝ) : ℂ) * I) (conj ((Ω : ℂ) * I)) ((Ω : ℂ) * I)

/-- The first-order orbit `z = R⁻¹ V̂ z_V(2jΩ)`. -/
def zorb (δ0 Ω Vh : ℝ) : Fin 4 → ℂ :=
  realifyInv *ᵥ ((Vh : ℂ) • (p.coeffs δ0).forcedV (p.vin δ0) (((2 * Ω : ℝ) : ℂ) * I))

/-- The eigen-data of the critical pair in the real coordinates. -/
@[tmio M, powerlib_domain] theorem modes (Pref δ0 Ω : ℝ) (hk : p.k ≠ 0)
    (h1 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h2 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0)
    (hD : (p.coeffs δ0).D ((Ω : ℂ) * I) = 0) (hDd : (p.coeffs δ0).Dd ((Ω : ℂ) * I) ≠ 0) :
    (ParametricResonance.ForcedOrbit.matX (p.rfield Pref) (p.xeq δ0, p.V)).map
        (algebraMap ℝ ℂ) *ᵥ p.rmode δ0 Ω = ((Ω : ℂ) * I) • p.rmode δ0 Ω ∧
      p.umode δ0 Ω ᵥ* (ParametricResonance.ForcedOrbit.matX (p.rfield Pref)
        (p.xeq δ0, p.V)).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • p.umode δ0 Ω ∧
      p.umode δ0 Ω ⬝ᵥ p.rmode δ0 Ω = 1 := by
  have hkc : (p.coeffs δ0).k ≠ 0 := by simp [coeffs, hk]
  have hr := Coeffs.right_eig hkc h1 h2 hD
  have hu := Coeffs.left_eig hkc h1 h2 hD
  have hur := Coeffs.left_right hkc h1 h2 hDd
  rw [p.matX_rfield_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [rmode, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, realify_mul_realifyInv,
      Matrix.mul_one, ← Matrix.mulVec_mulVec, hr, Matrix.mulVec_smul]
  · rw [umode, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      realify_mul_realifyInv, Matrix.one_mul, ← Matrix.vecMul_vecMul, hu, Matrix.smul_vecMul]
  · rw [umode, rmode, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, realify_mul_realifyInv,
      Matrix.one_mulVec, hur]

/-- The first-order orbit solves the linearization: `(jω − ∂ₓF) z = V̂ ∂_V F`, `ω = 2Ω`. -/
@[tmio M, powerlib_domain] theorem zorb_eq (Pref δ0 Ω Vh : ℝ) (hk : p.k ≠ 0)
    (hD2 : (p.coeffs δ0).D (((2 * Ω : ℝ) : ℂ) * I) ≠ 0)
    (h12 : ((2 * Ω : ℝ) : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h22 : ((2 * Ω : ℝ) : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0) :
    (((2 * Ω : ℝ) : ℂ) * I) • p.zorb δ0 Ω Vh -
        (ParametricResonance.ForcedOrbit.matX (p.rfield Pref) (p.xeq δ0, p.V)).map
          (algebraMap ℝ ℂ) *ᵥ p.zorb δ0 Ω Vh =
      (Vh : ℂ) • fun i => ((fderiv ℝ (p.rfield Pref) (p.xeq δ0, p.V) (0, 1) i : ℝ) : ℂ) := by
  have hkc : (p.coeffs δ0).k ≠ 0 := by simp [coeffs, hk]
  have hf := Coeffs.forcedV_eq (w := p.vin δ0) hkc hD2 h12 h22
  have hb : (fun i => ((fderiv ℝ (p.rfield Pref) (p.xeq δ0, p.V) (0, 1) i : ℝ) : ℂ)) =
      realifyInv *ᵥ (p.coeffs δ0).Bv (p.vin δ0) := p.fderivW_rfield Pref δ0
  rw [hb, p.matX_rfield_eq, zorb, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
    realify_mul_realifyInv, Matrix.mul_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul,
    ← Matrix.mulVec_sub, ← hf, ← Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul]
  conv_rhs => rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four]
  ring

/-- The modulation of the real field along the orbit is the core modulation in the coordinates
`(δ, p_f, ℓ, ℓ̄)`: `A₁ = R⁻¹ (A₁(V̂ z_V) + V̂ G_V) R`. -/
@[tmio M, powerlib_domain] theorem smA1_rfield (Pref δ0 Ω Vh : ℝ) :
    ParametricResonance.ForcedOrbit.smA1 (p.rfield Pref) (p.xeq δ0, p.V) Vh (p.zorb δ0 Ω Vh) =
      realifyInv * ((p.coeffs δ0).A1 ((Vh : ℂ) • (p.coeffs δ0).forcedV (p.vin δ0)
        (((2 * Ω : ℝ) : ℂ) * I)) + (Vh : ℂ) • (p.coeffs δ0).GV (p.vin δ0)) * realify := by
  have hD := ParametricResonance.ForcedOrbit.DxC_of_lift
    (ParametricResonance.ForcedOrbit.smDx (p.rfield Pref) (p.xeq δ0, p.V))
    ({ toFun := fun w => realifyInv * (p.coeffs δ0).A1lin (realify *ᵥ w) * realify
       map_add' := fun a b => by
         simp only [Matrix.mulVec_add, map_add, Matrix.mul_add, Matrix.add_mul]
       map_smul' := fun c a => by
         simp only [Matrix.mulVec_smul, map_smul, Matrix.mul_smul, Matrix.smul_mul,
           RingHom.id_apply] } : (Fin 4 → ℂ) →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ)
    (fun y => p.smDx_rfield Pref δ0 y) (p.zorb δ0 Ω Vh)
  rw [ParametricResonance.ForcedOrbit.smA1, hD, p.smM1_rfield]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Coeffs.A1lin, zorb, Matrix.mulVec_mulVec,
    realify_mul_realifyInv, Matrix.one_mulVec, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul]

/-- The pump of the real field along the orbit is the closed-form voltage pump `pumpV`. -/
@[tmio M, powerlib_domain] theorem pump_rfield (Pref δ0 Ω Vh : ℝ) :
    p.umode δ0 Ω ⬝ᵥ (ParametricResonance.ForcedOrbit.smA1 (p.rfield Pref) (p.xeq δ0, p.V) Vh
      (p.zorb δ0 Ω Vh) *ᵥ star (p.rmode δ0 Ω)) = p.pumpV δ0 Ω Vh := by
  have h := pump_realify (ParametricResonance.ForcedOrbit.smA1 (p.rfield Pref) (p.xeq δ0, p.V)
    Vh (p.zorb δ0 Ω Vh)) (p.umode δ0 Ω) (p.rmode δ0 Ω)
  simp only [ParametricResonance.Element.pump] at h
  rw [h, p.smA1_rfield, umode, rmode, Matrix.mulVec_mulVec, realify_mul_realifyInv,
    Matrix.one_mulVec, Matrix.vecMul_vecMul, realify_mul_realifyInv, Matrix.vecMul_one,
    p.swapConj_right, ← Matrix.mul_assoc, ← Matrix.mul_assoc, realify_mul_realifyInv,
    Matrix.one_mul, Matrix.mul_assoc, realify_mul_realifyInv, Matrix.mul_one, Coeffs.pumpV_eq,
    pumpV]
  rfl

/-- The real modal coordinates of the PSC core at its Hopf point from the critical eigenvectors
and a real basis `W` of the stable subspace of `Jreal`. -/
@[tmio M, powerlib_domain] theorem modal_rfield (Pref δ0 : ℝ) {Ω : ℝ} (hΩ : 0 < Ω) (hk : p.k ≠ 0)
    (h1 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h2 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0)
    (hD : (p.coeffs δ0).D ((Ω : ℂ) * I) = 0) (hDd : (p.coeffs δ0).Dd ((Ω : ℂ) * I) ≠ 0)
    {W : Matrix (Fin 4) (Fin 2) ℝ} {W' : Matrix (Fin 2) (Fin 4) ℝ} {As : Matrix (Fin 2) (Fin 2) ℝ}
    (hW : p.Jreal δ0 * W = W * As) (hWW : W' * W = 1)
    (huW : p.umode δ0 Ω ᵥ* W.map (algebraMap ℝ ℂ) = 0)
    (hWr : W'.map (algebraMap ℝ ℂ) *ᵥ p.rmode δ0 Ω = 0) :
    ∃ (P : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) ℝ) (Q : Matrix (Fin 2 ⊕ Fin 2) (Fin 4) ℝ),
      P * Q = 1 ∧ Q * P = 1 ∧
      Q * ParametricResonance.ForcedOrbit.matX (p.rfield Pref) (p.xeq δ0, p.V) * P =
        Matrix.fromBlocks (ParametricResonance.TwoToOne.base 0 (2 * Ω / 2)) 0 0 As ∧
      ParametricResonance.BlockAveraging.physLeft Q = p.umode δ0 Ω ∧
      ParametricResonance.BlockAveraging.physRight P = p.rmode δ0 Ω := by
  obtain ⟨hr, hu, hur⟩ := p.modes Pref δ0 Ω hk h1 h2 hD hDd
  have hW2 : ParametricResonance.ForcedOrbit.matX (p.rfield Pref) (p.xeq δ0, p.V) * W =
      W * As := by rw [p.matX_eq_Jreal]; exact hW
  obtain ⟨hQP, hPQ, hA0, hL, hR⟩ := ParametricResonance.ForcedOrbit.modal_of_basis
    finSumFinEquiv.symm hΩ.ne' hr hu hur hW2 hWW huW hWr
  refine ⟨_, _, hPQ, hQP, ?_, hL, hR⟩
  rw [hA0, mul_div_cancel_left₀ Ω two_ne_zero]

/-- PSC with active damping, grid-voltage modulation, end-to-end, stability. The real four-state
model `rfield` at the equilibrium `x₀ = xeq δ₀` (`p* = Peq δ₀`), with the core at its Hopf point
(`D(jΩ) = 0`), is driven by `V = V₀ + ε V̂ cos 2Ωt` and perturbed by `ε A₀'`. With a real basis
`W` of the stable subspace of `Jreal` (`Jreal W = W A_s`, `W' W = I`, `u W = 0`, `W' r = 0`,
`‖e^{T A_s}‖ < 1`): if `Re λ₁ < 0` and `|g_V/2| < |λ₁|` (`λ₁ = shift`, `g_V = pumpV`, the exact
closed form of `PSCVoltage`), then for all small `ε > 0` the forced periodic orbit exists (unique
in the ball of radius `cε`) and all its Floquet multipliers lie inside the unit circle. -/
@[tmio M, powerlib_domain] theorem orbit_voltage_stable (δ0 : ℝ) (hZ : p.Z ≠ 0) (hZ0 : p.Z0 ≠ 0)
    {Ω : ℝ} (hΩ : 0 < Ω) (hk : p.k ≠ 0)
    (h1 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h2 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0)
    (hD : (p.coeffs δ0).D ((Ω : ℂ) * I) = 0) (hDd : (p.coeffs δ0).Dd ((Ω : ℂ) * I) ≠ 0)
    (hD2 : (p.coeffs δ0).D (((2 * Ω : ℝ) : ℂ) * I) ≠ 0)
    (h12 : ((2 * Ω : ℝ) : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h22 : ((2 * Ω : ℝ) : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0)
    {W : Matrix (Fin 4) (Fin 2) ℝ} {W' : Matrix (Fin 2) (Fin 4) ℝ} {As : Matrix (Fin 2) (Fin 2) ℝ}
    (hW : p.Jreal δ0 * W = W * As) (hWW : W' * W = 1)
    (huW : p.umode δ0 Ω ᵥ* W.map (algebraMap ℝ ℂ) = 0)
    (hWr : W'.map (algebraMap ℝ ℂ) *ᵥ p.rmode δ0 Ω = 0)
    (hq : ‖ParametricResonance.BlockAveraging.expS As (2 * Real.pi / (2 * Ω))‖ < 1)
    (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ) (hs : (p.shift δ0 Ω A0').re < 0)
    (hg : ‖p.pumpV δ0 Ω Vh / 2‖ ^ 2 < ‖p.shift δ0 Ω A0'‖ ^ 2) :
    ∃ c, 0 ≤ c ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y (p.rfield (p.Peq δ0)
          (p.xeq δ0 + y t, p.V + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y (p.rfield (p.Peq δ0)
          (p.xeq δ0 + y t, p.V + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 4 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => ParametricResonance.ForcedOrbit.smJ (p.rfield (p.Peq δ0))
            (p.xeq δ0, p.V) Vh (2 * Ω) A0' ε t (y t)) (2 * Real.pi / (2 * Ω)) 0).map
            (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  obtain ⟨P, Q, hPQ, hQP, hA0, hL, hR⟩ :=
    p.modal_rfield (p.Peq δ0) δ0 hΩ hk h1 h2 hD hDd hW hWW huW hWr
  have hz := p.zorb_eq (p.Peq δ0) δ0 Ω Vh hk hD2 h12 h22
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_stable
    (p.contDiff_rfield (p.Peq δ0)).contDiffAt (p.rfield_eq_zero δ0 hZ hZ0)
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0 hq hz A0' ?_ ?_
  · rw [hL, hR]; exact hs
  · rw [hL, hR, p.pump_rfield]; exact hg

/-- PSC with active damping, grid-voltage modulation, end-to-end, parametric instability: with
`|λ₁| < |g_V/2|` the forced periodic orbit exists for all small `ε > 0` and its variational
equation is Floquet unstable. -/
@[tmio M, powerlib_domain] theorem orbit_voltage_unstable (δ0 : ℝ) (hZ : p.Z ≠ 0) (hZ0 : p.Z0 ≠ 0)
    {Ω : ℝ} (hΩ : 0 < Ω) (hk : p.k ≠ 0)
    (h1 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h2 : (Ω : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0)
    (hD : (p.coeffs δ0).D ((Ω : ℂ) * I) = 0) (hDd : (p.coeffs δ0).Dd ((Ω : ℂ) * I) ≠ 0)
    (hD2 : (p.coeffs δ0).D (((2 * Ω : ℝ) : ℂ) * I) ≠ 0)
    (h12 : ((2 * Ω : ℝ) : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).b) ≠ 0)
    (h22 : ((2 * Ω : ℝ) : ℂ) * I + (p.coeffs δ0).αd * (1 - (p.coeffs δ0).bb) ≠ 0)
    {W : Matrix (Fin 4) (Fin 2) ℝ} {W' : Matrix (Fin 2) (Fin 4) ℝ} {As : Matrix (Fin 2) (Fin 2) ℝ}
    (hW : p.Jreal δ0 * W = W * As) (hWW : W' * W = 1)
    (huW : p.umode δ0 Ω ᵥ* W.map (algebraMap ℝ ℂ) = 0)
    (hWr : W'.map (algebraMap ℝ ℂ) *ᵥ p.rmode δ0 Ω = 0)
    (hq : ‖ParametricResonance.BlockAveraging.expS As (2 * Real.pi / (2 * Ω))‖ < 1)
    (Vh : ℝ) (A0' : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ‖p.shift δ0 Ω A0'‖ ^ 2 < ‖p.pumpV δ0 Ω Vh / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 4 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y (p.rfield (p.Peq δ0)
          (p.xeq δ0 + y t, p.V + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 4 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y (p.rfield (p.Peq δ0)
          (p.xeq δ0 + y t, p.V + ε * (Vh * Real.cos (2 * Ω * t))) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => ParametricResonance.ForcedOrbit.smJ
          (p.rfield (p.Peq δ0)) (p.xeq δ0, p.V) Vh (2 * Ω) A0' ε t (y t))
          (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨P, Q, hPQ, hQP, hA0, hL, hR⟩ :=
    p.modal_rfield (p.Peq δ0) δ0 hΩ hk h1 h2 hD hDd hW hWW huW hWr
  have hz := p.zorb_eq (p.Peq δ0) δ0 Ω Vh hk hD2 h12 h22
  refine ParametricResonance.ForcedOrbit.smooth_orbit_floquet_unstable
    (p.contDiff_rfield (p.Peq δ0)).contDiffAt (p.rfield_eq_zero δ0 hZ hZ0)
    (by positivity : (0 : ℝ) < 2 * Ω) hPQ hQP As hA0 hq hz A0' ?_
  rw [hL, hR, p.pump_rfield]; exact hg

end Model

end PSCFull
end powerlib.GFM
