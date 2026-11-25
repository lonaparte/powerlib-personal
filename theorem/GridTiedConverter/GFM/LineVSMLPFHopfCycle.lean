import theorem.GridTiedConverter.GFM.HopfLineLPFSlice
import theorem.Dynamics.HopfCycle

/-! # The VSM with a power filter on a dynamic R–L line: Hopf cycles along damping and inertia

Domain module.

Model boundary.
* The five-state VSM + power filter `Line.VSMLPF` of
  `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged: state `(δ, ω, P_f, i_d, i_q)`, grid
  dq frame at `ω₀`, export-positive power, constant `E`, `M ω̇ = P_ref − P_f − D ω`,
  `Ṗ_f = ω_c (P_e − P_f)`, `L i̇ = E e^{jδ} − V − (R + jX) i`; no voltage loop, inner loops, PLL,
  delay or PWM. Read about a selected angle (`Line.VSMLPF.Model`) at a Hopf point of its quintic
  (`Line.VSMLPF.Model.HopfAt`).
* Two unfolding parameters, each keeping the operating point `(δ*, 0, P_ref, i_s(δ*))` and the
  balance (they depend only on the network and the set-point): the damping, `D ↦ D + μ`
  (`Line.VSMLPF.dampShift`, family `Line.VSMLPF.Model.dampFamily`), and the inverse inertia,
  `1/M ↦ 1/M + μ` (`Line.VSMLPF.inertShift`, `M ↦ (M⁻¹ + μ)⁻¹`, physical for `μ > −1/M`, family
  `Line.VSMLPF.Model.inertFamily`).
* The transversality coefficients in closed form on the zero-current slice `δ* = 0`, `V = E`
  (`Line.VSMLPF.Model.OnSlice`, the setting of
  `theorem/GridTiedConverter/GFM/HopfLineLPFSlice.lean`; on the boundary `Δ₄ = 0`, `Δ₂, Δ₃ > 0`
  the Hopf frequency is `Line.VSMLPF.Model.sliceOmega`, `Line.VSMLPF.Model.hopfAt_sliceOmega`) and
  exactly at the two witnesses of `theorem/GridTiedConverter/GFM/HopfLineLPF.lean`. Off the slice
  neither `ℓ₁` nor `τ` is stated in closed form (the size obstruction of the slice module).
* Level: exact identities and signs, and, as private evidence, the cycles of the generic Hopf
  theorem `Dynamics.HopfCycle.exists_hopfCycle`. Periodic orbits are not sentences of
  `Line.VSMLPF.family`: no new family, no connection conclusion. Not proved: uniqueness and
  orbital stability of the cycles, the cycles at the Bautin points `𝔅 = 0`.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.4–3.5 (Theorem 3.3,
the transversality coefficient `Re λ'(0) = Re ⟨p, A'(0) q⟩`); the templates
`theorem/GridTiedConverter/GFM/VSMLPFHopfCycle.lean` and
`theorem/GridTiedConverter/GFM/LineVSMHopfCycle.lean` (four states, damping and inertia); the
critical pairs, `ℓ₁` and the slice pattern of `theorem/GridTiedConverter/GFM/HopfLineLPF.lean`
and `theorem/GridTiedConverter/GFM/HopfLineLPFSlice.lean`. The slice forms `𝔗`, `𝔍` and the
witness were found with SymPy in exact rational arithmetic (untrusted) and are checked by the
kernel (`linear_combination`, `ring`, `norm_num`).

Results.
* The damping family: `Line.VSMLPF.dampShift`, `Line.VSMLPF.Model.dampFamily`,
  `Line.VSMLPF.dampJac` (`∂J/∂D = −(1/M) e₁e₁ᵀ`); `Line.VSMLPF.dampShift_field`,
  `Line.VSMLPF.Model.dampFamily_zero_param`, `Line.VSMLPF.Model.dampFamily_origin`,
  `Line.VSMLPF.dampShift_jacobian`, `Line.VSMLPF.Model.fderiv_dampFamily`,
  `Line.VSMLPF.Model.hasDerivAt_fderiv_dampFamily`.
* `Line.VSMLPF.paramTrace_dampJac` (`τ_D = −(2/M) Re(conj p₁ q₁)` for every pair);
  `Line.VSMLPF.Model.paramTrace_dampJac_slice` (on the slice:
  `τ_D = −4 w² ω⁴ ((σ² + w² − ω²)² + 4σ²ω²) 𝔗 / (M (Re² Ĉ + Im² Ĉ))`,
  `𝔗 = Line.VSMLPF.sliceTransversality (D/M) (R/L) ω₀ ω`) and
  `Line.VSMLPF.Model.sign_paramTrace_dampJac_slice` (`sign τ_D = −sign 𝔗`).
* At the witnesses: `Line.VSMLPF.hopfWitnessSup_paramTrace` (`τ_D = −46/25`) and
  `Line.VSMLPF.hopfWitness_paramTrace` (`τ_D = −581472978503/190454141400`).
* **`𝔗` has no fixed sign on the slice**: the slice witness `Line.VSMLPF.sliceNegWitness`
  (`E = V = L = 1`, `R = 1/20`, `ω₀ = 27/20`, `M = 27/17`, `D = 27/85`, `ω_c = 13`; physical,
  balanced, on the slice, a Hopf point at `ω = 1`: `sliceNegWitness_physical`,
  `sliceNegWitness_balanced`, `sliceNegWitness_onSlice`, `sliceNegWitness_hopfAt`) has
  `𝔗 = −19513/200000` (`Line.VSMLPF.sliceNegWitness_sliceTransversality`), hence `τ_D > 0`
  (`Line.VSMLPF.sliceNegWitness_paramTrace_pos`: there more damping destabilizes).
* The inverse-inertia family: `Line.VSMLPF.inertShift`, `Line.VSMLPF.Model.inertFamily`,
  `Line.VSMLPF.inertJac` (`∂J/∂μ`: the single row `(0, −D, −1, 0, 0)`);
  `Line.VSMLPF.inertShift_field`, `Line.VSMLPF.Model.inertFamily_zero_param`,
  `Line.VSMLPF.Model.inertFamily_origin`, `Line.VSMLPF.inertShift_jacobian`,
  `Line.VSMLPF.Model.fderiv_inertFamily`, `Line.VSMLPF.Model.hasDerivAt_fderiv_inertFamily`.
* `Line.VSMLPF.paramTrace_inertJac` (`τ_M = 2 Re(conj p₁ (−D q₁ − q₂))` for every pair);
  `Line.VSMLPF.Model.paramTrace_inertJac_slice` (on the slice the row maps the critical vector
  to `−M ω² q₀` and `τ_M = 2 M w² ω⁴ ((σ² + w² − ω²)² + 4σ²ω²) 𝔍 / (Re² Ĉ + Im² Ĉ)`,
  `𝔍 = Line.VSMLPF.sliceInertia (D/M) (R/L) ω₀ ω`) and
  `Line.VSMLPF.Model.sign_paramTrace_inertJac_slice` (`sign τ_M = sign 𝔍`).
* **`τ_D` and `τ_M` never vanish together on the slice**: the identity
  `ω² w² (4ω² 𝔗² + 𝔍²) = (d² + ω²)(Re² Ĉ + Im² Ĉ)`
  (`Line.VSMLPF.sliceTransversality_sq_add_sliceInertia_sq`) with `Re Ĉ > 0`;
  `Line.VSMLPF.Model.paramTrace_inert_ne_zero_of_paramTrace_eq_zero_slice`.
* Private evidence: `Line.VSMLPF.Model.exists_hopfCycle_slice_of_family` (the cycles of
  `Dynamics.HopfCycle.exists_hopfCycle` for any family through a slice Hopf point with a given
  sign of `τ`), `Line.VSMLPF.Model.exists_hopfCycle_slice_damping` (`𝔅 ≠ 0`, `𝔗 ≠ 0`, small
  `μ` with `μ 𝔗 𝔅 < 0`), `Line.VSMLPF.Model.exists_hopfCycle_slice_inertia` (`𝔅 ≠ 0`, `𝔍 ≠ 0`,
  `μ 𝔍 𝔅 > 0`) and **`Line.VSMLPF.Model.exists_hopfCycle_slice_of_sliceBautin_ne`**: at every
  balanced physical slice Hopf point with `𝔅 ≠ 0` a nonconstant periodic orbit of period at
  most `4π/ω` with `c|μ|/8 ≤ ‖critπ p z(t)‖² ≤ 8c|μ|` exists, along the damping if `𝔗 ≠ 0` and
  along the inverse inertia if `𝔗 = 0`; at the witnesses
  `Line.VSMLPF.hopfWitnessSup_exists_hopfCycle` (supercritical, `μ < 0`) and
  `Line.VSMLPF.hopfWitness_exists_hopfCycle` (subcritical, `μ > 0`); with them
  `Line.VSMLPF.Model.contDiff_augField_dampFamily`,
  `Line.VSMLPF.Model.contDiff_augField_inertFamily`.
-/

noncomputable section
namespace powerlib.GFM.Line
namespace VSMLPF
open Polynomial Complex
open powerlib.Dynamics (State)
open powerlib.Dynamics.HopfCycle (augField xpart mpart xin)
open powerlib.NormalForm.LyapunovCoefficient
open powerlib.Dynamics.CenterManifold (critπ critι critι_apply critπ_apply0 critπ_apply1 reV_apply
  imV_apply)
open powerlib.Dynamics.Degenerate.PlanarFocus (e0 e1 e0_apply0 e0_apply1 e1_apply0 e1_apply1)

/-! ## The damping family -/

/-- The parameters with the damping shifted by `μ`: `D ↦ D + μ`. -/
def dampShift (g : VSMLPF) (μ : ℝ) : VSMLPF := { g with D := g.D + μ }

/-- The translated field of the model with the damping `D + μ`, as a family in `μ`
(`z = x − (δ*, 0, P_ref, i_s(δ*))`; the operating point does not depend on the damping). -/
def Model.dampFamily (m : Model) (z : State 5) (μ : ℝ) : State 5 :=
  (m.g.dampShift μ).field (z + m.point)

/-- The parameter derivative of the Jacobian: `∂J/∂D = −(1/M) e₁ e₁ᵀ`. -/
def dampJac (M : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 0, 0, 0, 0; 0, -(1 / M), 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0]

@[tmio M, simp, powerlib_domain] theorem dampShift_zero (g : VSMLPF) : g.dampShift 0 = g := by
  rcases g with ⟨⟨N, M, D, Pref⟩, ωc⟩
  simp [dampShift]

/-- **The shifted field** differs from the model field only in the `ω` row:
`F_{D+μ}(x) = F_D(x) − (μ x₁/M) e₁`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem dampShift_field (g : VSMLPF) (μ : ℝ) (x : State 5) :
    (g.dampShift μ).field x = g.field x - (μ * x 1 / g.M) • EuclideanSpace.single 1 1 := by
  ext i
  fin_cases i <;> simp [field, dampShift, Network.power_eq, Network.rateD, Network.rateQ]
  ring

@[tmio M, powerlib_domain] theorem Model.dampFamily_zero_param (m : Model) :
    (fun z => m.dampFamily z 0) = m.field := by
  funext z; simp [Model.dampFamily, Model.field]

@[tmio M, powerlib_domain] theorem Model.dampFamily_origin (m : Model) (hp : Meets m .physical)
    (hb : Meets m .balanced) (μ : ℝ) : m.dampFamily 0 μ = 0 := by
  have h0 : m.g.field m.point = 0 :=
    (m.field_point_eq_zero_iff hp.2.1.ne' hp.2.2.2.ne' hp.1.L.ne' hp.1.absSq_pos.ne').mpr hb
  have h1 : m.point 1 = 0 := rfl
  rw [Model.dampFamily, zero_add, dampShift_field, h0, h1]
  simp

@[tmio M, powerlib_domain] private theorem Model.contDiff_augField_dampFamily (m : Model)
    {k : WithTop ℕ∞} : ContDiff ℝ k (augField m.dampFamily) := by
  have hx : ContDiff ℝ k fun w : State (5 + 1) => xpart w + m.point :=
    xpart.contDiff.add contDiff_const
  have h : ContDiff ℝ k (fun w : State (5 + 1) => m.g.field (xpart w + m.point) -
      (mpart w * (xpart w + m.point) 1 / m.g.M) • EuclideanSpace.single (1 : Fin 5) (1 : ℝ)) := by
    refine (m.g.contDiff_field.comp hx).sub (ContDiff.smul_const ?_ _)
    exact (mpart.contDiff.mul ((PiLp.proj 2 (fun _ : Fin 5 => ℝ) 1).contDiff.comp hx)).div_const _
  have e : augField m.dampFamily = fun w : State (5 + 1) => xin (m.g.field (xpart w + m.point) -
      (mpart w * (xpart w + m.point) 1 / m.g.M) • EuclideanSpace.single (1 : Fin 5) (1 : ℝ)) := by
    funext w
    simp only [augField, Model.dampFamily, dampShift_field]
  rw [e]
  exact xin.contDiff.comp h

@[tmio M, powerlib_domain] theorem dampShift_jacobian (g : VSMLPF) (μ δ id iq : ℝ) :
    (g.dampShift μ).jacobian δ id iq = g.jacobian δ id iq + μ • dampJac g.M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jacobian, dampShift, dampJac, Network.reactive_eq]
  ring

@[tmio M, powerlib_domain] theorem Model.fderiv_dampFamily (m : Model) (μ : ℝ) :
    fderiv ℝ (fun z => m.dampFamily z μ) 0 =
      Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) m.jac +
        μ • Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (dampJac m.g.M) := by
  rw [show (fun z => m.dampFamily z μ) = fun z => (m.g.dampShift μ).field (z + m.point) from rfl,
    fderiv_comp_add_right, zero_add, fderiv_field, dampShift_jacobian]
  simp [Model.point, qss, Model.jac, Dynamics.mk3, map_add, map_smul]

/-- **Transversality data**: `μ ↦ D_z F(0, μ)` is affine with slope `toEuclideanCLM (∂J/∂D)`. -/
@[tmio M, powerlib_domain] theorem Model.hasDerivAt_fderiv_dampFamily (m : Model) :
    HasDerivAt (fun μ => fderiv ℝ (fun z => m.dampFamily z μ) 0)
      (Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (dampJac m.g.M)) 0 := by
  simp only [Model.fderiv_dampFamily]
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
    (Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (dampJac m.g.M))).const_add
    (Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) m.jac)

/-! ## The transversality coefficient -/

/-- **The transversality coefficient along the damping, for every pair**:
`τ = tr (critπ p ∘ ∂J/∂D ∘ critι q) = −(2/M) Re(conj p₁ q₁)` (`= 2 Re ⟨p, (∂J/∂D) q⟩`). -/
@[tmio M, powerlib_domain] theorem paramTrace_dampJac (M : ℝ) (p q : Fin 5 → ℂ) :
    Dynamics.PlanarHopf.paramTrace ((critπ p).comp
        ((Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (dampJac M)).comp (critι q))) =
      -(2 / M) * (starRingEnd ℂ (p 1) * q 1).re := by
  have hB : ∀ v : State 5, Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (dampJac M) v =
      WithLp.toLp 2 ![0, -(v 1 / M), 0, 0, 0] := by
    intro v
    ext i
    fin_cases i <;> simp [Dynamics.toEuclideanCLM_apply, dampJac, Fin.sum_univ_five]
    ring
  simp only [Dynamics.PlanarHopf.paramTrace, Dynamics.PlanarHopf.m00, Dynamics.PlanarHopf.m11,
    ContinuousLinearMap.comp_apply, critι_apply, critπ_apply0, critπ_apply1, e0_apply0,
    e0_apply1, e1_apply0, e1_apply1, one_smul, zero_smul, add_zero, zero_add, hB]
  simp [PiLp.inner_apply, Fin.sum_univ_five, reV_apply, imV_apply, Complex.mul_re,
    RCLike.inner_apply, conj_trivial]
  ring

/-- **The transversality coefficient on the zero-current slice in closed form**: at a Hopf point
`ω` of a physical slice model (`δ* = 0`, `V = E`), along the damping and at
(`Model.sliceQ`, `Model.sliceP`),
`τ = −4 w² ω⁴ ((σ² + w² − ω²)² + 4σ²ω²) 𝔗 / (M (Re² Ĉ + Im² Ĉ))`, `d = D/M`, `σ = R/L`,
`w = ω₀`, `𝔗 = Line.VSMLPF.sliceTransversality d σ w ω`, `Ĉ = slicePairRe + i slicePairIm`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.paramTrace_dampJac_slice {m : Model}
    (hp : Meets m .physical) (hs : m.OnSlice) {ω : ℝ} (hH : m.HopfAt ω) :
    Dynamics.PlanarHopf.paramTrace ((critπ (m.sliceP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (dampJac m.g.M)).comp
          (critι (m.sliceQ ω)))) =
      -(4 * m.g.ω0 ^ 2 * ω ^ 4 *
          (((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2) ^ 2 + 4 * (m.g.R / m.g.L) ^ 2 * ω ^ 2) *
          sliceTransversality (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω /
        (m.g.M * (slicePairRe (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 +
          slicePairIm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2))) := by
  rw [paramTrace_dampJac, m.re_sliceP_one_mul_sliceQ_one hp hs hH, ← div_div]
  ring

/-- **The sign of the transversality coefficient on the slice**: `sign τ = −sign 𝔗`
(`Line.VSMLPF.sliceTransversality`): more damping moves the critical pair to the left exactly
where `𝔗 > 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.sign_paramTrace_dampJac_slice {m : Model}
    (hp : Meets m .physical) (hs : m.OnSlice) {ω : ℝ} (hH : m.HopfAt ω) :
    SignType.sign (Dynamics.PlanarHopf.paramTrace ((critπ (m.sliceP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (dampJac m.g.M)).comp
          (critι (m.sliceQ ω))))) =
      -SignType.sign (sliceTransversality (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω) := by
  have hM : -(2 / m.g.M) < 0 := neg_neg_of_pos (div_pos two_pos hp.2.1)
  rw [paramTrace_dampJac, sign_mul, sign_neg hM, neg_one_mul,
    m.sign_re_sliceP_one_mul_sliceQ_one hp hs hH]

/-- **The transversality coefficient of `hopfWitnessSup`**: `τ = −46/25`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem hopfWitnessSup_paramTrace :
    Dynamics.PlanarHopf.paramTrace ((critπ hopfWitnessSupP).comp
        ((Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (dampJac hopfWitnessSup.g.M)).comp
          (critι hopfWitnessSupQ))) = -46 / 25 := by
  rw [paramTrace_dampJac]
  simp [hopfWitnessSupP, hopfWitnessSupQ, hopfWitnessSup, Complex.mul_re,
    -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
    -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
  norm_num

/-- **The transversality coefficient of `hopfWitness`**: `τ = −581472978503/190454141400`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem hopfWitness_paramTrace :
    Dynamics.PlanarHopf.paramTrace ((critπ hopfWitnessP).comp
        ((Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (dampJac hopfWitness.g.M)).comp
          (critι hopfWitnessQ))) = -581472978503 / 190454141400 := by
  rw [paramTrace_dampJac]
  simp [hopfWitnessP, hopfWitnessQ, hopfWitness, Complex.mul_re,
    -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
    -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
  norm_num

/-! ## A slice Hopf point where more damping destabilizes -/

/-- The slice witness `E = V = L = 1`, `R = 1/20`, `ω₀ = 27/20`, `M = 27/17`, `D = 27/85`,
`ω_c = 13`, `P_ref = 0`, `δ* = 0` (`d = 1/5`, `σ = 1/20`, `w = 27/20`; a Hopf point at
`ω = 1`). -/
def sliceNegWitness : Model := ⟨⟨⟨⟨1, 1, 1 / 20, 1, 27 / 20⟩, 27 / 17, 27 / 85, 0⟩, 13⟩, 0⟩

/-- `sliceNegWitness` is physical. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem sliceNegWitness_physical : Meets sliceNegWitness .physical := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> norm_num [sliceNegWitness]

/-- `sliceNegWitness` is balanced. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem sliceNegWitness_balanced : Meets sliceNegWitness .balanced := by
  change sliceNegWitness.g.qssPower sliceNegWitness.δ = sliceNegWitness.g.Pref
  norm_num [Network.qssPower, sliceNegWitness, Network.is, Network.power_eq]

/-- `sliceNegWitness` lies on the zero-current slice. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem sliceNegWitness_onSlice : sliceNegWitness.OnSlice :=
  ⟨rfl, rfl⟩

@[tmio M, powerlib_domain] private theorem sliceNegWitness_Q : sliceNegWitness.Q = 0 := by
  norm_num [Model.Q, Network.qssReactive, sliceNegWitness, Network.is, Network.reactive_eq]

/-- The quintic of `sliceNegWitness` has a Hopf point at `ω = 1`
(`a₄ = 133/10`, `a₃ = 1149/200`, `a₂ = 487/20`, `a₁ = 949/200`, `a₀ = 221/20`). Static evidence
on the model. -/
@[tmio M, powerlib_domain] theorem sliceNegWitness_hopfAt : sliceNegWitness.HopfAt 1 := by
  have h : sliceNegWitness.g.coeff4 = 133 / 10 ∧ sliceNegWitness.g.coeff3 = 1149 / 200 ∧
      sliceNegWitness.g.coeff2 sliceNegWitness.Q = 487 / 20 ∧
      sliceNegWitness.g.coeff1 sliceNegWitness.Q = 949 / 200 ∧
      sliceNegWitness.g.coeff0 sliceNegWitness.Q = 221 / 20 := by
    rw [sliceNegWitness_Q]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [coeff4, coeff3, coeff2, coeff1, coeff0, VSM.coeff1, VSM.coeff0, sliceNegWitness,
        Network.ρ, Network.σ, Network.X]
  obtain ⟨h4, h3, h2, h1, h0⟩ := h
  refine ⟨one_pos, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [h4, h3, h2, h1, h0] <;> norm_num

/-- The transversality form of `sliceNegWitness` is negative: `𝔗(1/5, 1/20, 27/20, 1) =
−19513/200000`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem sliceNegWitness_sliceTransversality :
    sliceTransversality (sliceNegWitness.g.D / sliceNegWitness.g.M)
      (sliceNegWitness.g.R / sliceNegWitness.g.L) sliceNegWitness.g.ω0 1 = -19513 / 200000 := by
  norm_num [sliceTransversality, sliceNegWitness]

/-- **More damping destabilizes at `sliceNegWitness`**: at its slice Hopf point the transversality
coefficient along the damping is positive (`sign τ = −sign 𝔗`, `𝔗 < 0`): `𝔗` has no fixed sign on
the slice Hopf set. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem sliceNegWitness_paramTrace_pos :
    0 < Dynamics.PlanarHopf.paramTrace ((critπ (sliceNegWitness.sliceP 1)).comp
        ((Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (dampJac sliceNegWitness.g.M)).comp
          (critι (sliceNegWitness.sliceQ 1)))) := by
  have h := sliceNegWitness.sign_paramTrace_dampJac_slice sliceNegWitness_physical
    sliceNegWitness_onSlice sliceNegWitness_hopfAt
  rw [sliceNegWitness_sliceTransversality,
    sign_neg (show (-19513 / 200000 : ℝ) < 0 by norm_num), neg_neg] at h
  exact sign_eq_one_iff.mp h

/-! ## The family along the inverse inertia -/

/-- The parameters with the inverse inertia shifted by `μ`: `1/M ↦ 1/M + μ`, i.e.
`M ↦ (M⁻¹ + μ)⁻¹` (network, damping, set-point and filter unchanged). -/
def inertShift (g : VSMLPF) (μ : ℝ) : VSMLPF := { g with M := (g.M⁻¹ + μ)⁻¹ }

/-- The translated field of the model with the inverse inertia `1/M + μ`, as a family in `μ`
(the operating point does not depend on the inertia). -/
def Model.inertFamily (m : Model) (z : State 5) (μ : ℝ) : State 5 :=
  (m.g.inertShift μ).field (z + m.point)

/-- The parameter derivative of the Jacobian along the inverse inertia: the single row
`(0, −D, −1, 0, 0)` (`M` times the `ω` row of `J`). -/
def inertJac (D : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 0, 0, 0, 0; 0, -D, -1, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0]

@[tmio M, simp, powerlib_domain] theorem inertShift_zero (g : VSMLPF) : g.inertShift 0 = g := by
  rcases g with ⟨⟨N, M, D, Pref⟩, ωc⟩
  simp [inertShift]

/-- The inertia enters only the `ω` row: `F_μ(x) = F(x) + μ (P_ref − x₂ − D x₁) e₁`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem inertShift_field (g : VSMLPF) (μ : ℝ) (x : State 5) :
    (g.inertShift μ).field x =
      g.field x + (μ * (g.Pref - x 2 - g.D * x 1)) • EuclideanSpace.single 1 1 := by
  ext i
  fin_cases i <;> simp [field, inertShift, Network.power_eq, Network.rateD, Network.rateQ]
  ring

@[tmio M, powerlib_domain] theorem Model.inertFamily_zero_param (m : Model) :
    (fun z => m.inertFamily z 0) = m.field := by
  funext z; simp [Model.inertFamily, Model.field]

@[tmio M, powerlib_domain] theorem Model.inertFamily_origin (m : Model) (hp : Meets m .physical)
    (hb : Meets m .balanced) (μ : ℝ) : m.inertFamily 0 μ = 0 := by
  have h0 : m.g.field m.point = 0 :=
    (m.field_point_eq_zero_iff hp.2.1.ne' hp.2.2.2.ne' hp.1.L.ne' hp.1.absSq_pos.ne').mpr hb
  have h1 : m.point 1 = 0 := rfl
  have h2 : m.point 2 = m.g.Pref := rfl
  rw [Model.inertFamily, zero_add, inertShift_field, h0, h1, h2]
  simp

@[tmio M, powerlib_domain] private theorem Model.contDiff_augField_inertFamily (m : Model)
    {k : WithTop ℕ∞} : ContDiff ℝ k (augField m.inertFamily) := by
  have hx : ContDiff ℝ k fun w : State (5 + 1) => xpart w + m.point :=
    xpart.contDiff.add contDiff_const
  have hj : ∀ j : Fin 5, ContDiff ℝ k fun w : State (5 + 1) => (xpart w + m.point) j :=
    contDiff_euclidean.mp hx
  have h : ContDiff ℝ k (fun w : State (5 + 1) => m.g.field (xpart w + m.point) +
      (mpart w * (m.g.Pref - (xpart w + m.point) 2 - m.g.D * (xpart w + m.point) 1)) •
        EuclideanSpace.single (1 : Fin 5) (1 : ℝ)) := by
    refine (m.g.contDiff_field.comp hx).add (ContDiff.smul_const ?_ _)
    exact mpart.contDiff.mul ((contDiff_const.sub (hj 2)).sub (contDiff_const.mul (hj 1)))
  have e : augField m.inertFamily = fun w : State (5 + 1) => xin (m.g.field (xpart w + m.point) +
      (mpart w * (m.g.Pref - (xpart w + m.point) 2 - m.g.D * (xpart w + m.point) 1)) •
        EuclideanSpace.single (1 : Fin 5) (1 : ℝ)) := by
    funext w
    simp only [augField, Model.inertFamily, inertShift_field]
  rw [e]
  exact xin.contDiff.comp h

@[tmio M, powerlib_domain] theorem inertShift_jacobian (g : VSMLPF) (μ δ id iq : ℝ) :
    (g.inertShift μ).jacobian δ id iq = g.jacobian δ id iq + μ • inertJac g.D := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jacobian, inertShift, inertJac, Network.reactive_eq]
  all_goals ring

@[tmio M, powerlib_domain] theorem Model.fderiv_inertFamily (m : Model) (μ : ℝ) :
    fderiv ℝ (fun z => m.inertFamily z μ) 0 =
      Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) m.jac +
        μ • Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (inertJac m.g.D) := by
  rw [show (fun z => m.inertFamily z μ) = fun z => (m.g.inertShift μ).field (z + m.point) from
    rfl, fderiv_comp_add_right, zero_add, fderiv_field, inertShift_jacobian]
  simp [Model.point, qss, Model.jac, Dynamics.mk3, map_add, map_smul]

/-- **Transversality data along the inverse inertia**: `μ ↦ D_z F(0, μ)` is affine with slope
`toEuclideanCLM (inertJac D)`. -/
@[tmio M, powerlib_domain] theorem Model.hasDerivAt_fderiv_inertFamily (m : Model) :
    HasDerivAt (fun μ => fderiv ℝ (fun z => m.inertFamily z μ) 0)
      (Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (inertJac m.g.D)) 0 := by
  simp only [Model.fderiv_inertFamily]
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
    (Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (inertJac m.g.D))).const_add
    (Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) m.jac)

/-- **The transversality coefficient along the inverse inertia, for every pair**:
`τ_M = 2 Re(conj p₁ (−D q₁ − q₂))`. -/
@[tmio M, powerlib_domain] theorem paramTrace_inertJac (D : ℝ) (p q : Fin 5 → ℂ) :
    Dynamics.PlanarHopf.paramTrace ((critπ p).comp
        ((Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (inertJac D)).comp (critι q))) =
      2 * (starRingEnd ℂ (p 1) * (-(D : ℂ) * q 1 - q 2)).re := by
  have hB : ∀ v : State 5, Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (inertJac D) v =
      WithLp.toLp 2 ![0, -(D * v 1) - v 2, 0, 0, 0] := by
    intro v
    ext i
    fin_cases i <;> simp [Dynamics.toEuclideanCLM_apply, inertJac, Fin.sum_univ_five]
    ring
  simp only [Dynamics.PlanarHopf.paramTrace, Dynamics.PlanarHopf.m00, Dynamics.PlanarHopf.m11,
    ContinuousLinearMap.comp_apply, critι_apply, critπ_apply0, critπ_apply1, e0_apply0,
    e0_apply1, e1_apply0, e1_apply1, one_smul, zero_smul, add_zero, zero_add, hB]
  simp [PiLp.inner_apply, Fin.sum_univ_five, reV_apply, imV_apply, Complex.mul_re,
    RCLike.inner_apply, conj_trivial]
  ring

@[tmio M, powerlib_domain] private theorem sliceQ_inertRow {m : Model} (hM : m.g.M ≠ 0)
    (hL : m.g.L ≠ 0) (ω : ℝ) : -(m.g.D : ℂ) * m.sliceQ ω 1 - m.sliceQ ω 2 =
      -((m.g.M * ω ^ 2 : ℝ) : ℂ) * m.sliceQ ω 0 := by
  have hMc : (m.g.M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hLc : (m.g.L : ℂ) ≠ 0 := by exact_mod_cast hL
  simp [Model.sliceQ, sliceScale, sliceVecQ]
  field_simp
  ring

/-- **The inverse-inertia transversality coefficient on the zero-current slice in closed form**:
at a Hopf point `ω` of a physical slice model, at (`Model.sliceQ`, `Model.sliceP`), the row of
`∂J/∂μ` maps the critical vector to `−M ω² q₀` and
`τ_M = 2 M w² ω⁴ ((σ² + w² − ω²)² + 4σ²ω²) 𝔍 / (Re² Ĉ + Im² Ĉ)`,
`𝔍 = Line.VSMLPF.sliceInertia (D/M) (R/L) ω₀ ω`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.paramTrace_inertJac_slice {m : Model}
    (hp : Meets m .physical) (hs : m.OnSlice) {ω : ℝ} (hH : m.HopfAt ω) :
    Dynamics.PlanarHopf.paramTrace ((critπ (m.sliceP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (inertJac m.g.D)).comp
          (critι (m.sliceQ ω)))) =
      2 * m.g.M * m.g.ω0 ^ 2 * ω ^ 4 *
          (((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2 - ω ^ 2) ^ 2 + 4 * (m.g.R / m.g.L) ^ 2 * ω ^ 2) *
          sliceInertia (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω /
        (slicePairRe (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2 +
          slicePairIm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ^ 2) := by
  rw [paramTrace_inertJac, sliceQ_inertRow hp.2.1.ne' hp.1.L.ne',
    show starRingEnd ℂ (m.sliceP ω 1) * (-((m.g.M * ω ^ 2 : ℝ) : ℂ) * m.sliceQ ω 0) =
      ((-(m.g.M * ω ^ 2) : ℝ) : ℂ) * (starRingEnd ℂ (m.sliceP ω 1) * m.sliceQ ω 0) by
        push_cast; ring,
    Complex.re_ofReal_mul, m.re_sliceP_one_mul_sliceQ_zero hp hs hH]
  ring

/-- **The sign of the inverse-inertia transversality coefficient on the slice**:
`sign τ_M = sign 𝔍` (`Line.VSMLPF.sliceInertia`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.sign_paramTrace_inertJac_slice {m : Model}
    (hp : Meets m .physical) (hs : m.OnSlice) {ω : ℝ} (hH : m.HopfAt ω) :
    SignType.sign (Dynamics.PlanarHopf.paramTrace ((critπ (m.sliceP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (inertJac m.g.D)).comp
          (critι (m.sliceQ ω))))) =
      SignType.sign (sliceInertia (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω) := by
  have hM : -(2 * m.g.M * ω ^ 2) < 0 := by
    have h1 := hp.2.1
    have h2 := hH.1
    have : 0 < 2 * m.g.M * ω ^ 2 := by positivity
    linarith
  rw [paramTrace_inertJac, sliceQ_inertRow hp.2.1.ne' hp.1.L.ne',
    show starRingEnd ℂ (m.sliceP ω 1) * (-((m.g.M * ω ^ 2 : ℝ) : ℂ) * m.sliceQ ω 0) =
      ((-(m.g.M * ω ^ 2) : ℝ) : ℂ) * (starRingEnd ℂ (m.sliceP ω 1) * m.sliceQ ω 0) by
        push_cast; ring,
    Complex.re_ofReal_mul, ← mul_assoc, show 2 * -(m.g.M * ω ^ 2) = -(2 * m.g.M * ω ^ 2) by ring,
    sign_mul, sign_neg hM, m.sign_re_sliceP_one_mul_sliceQ_zero hp hs hH, neg_one_mul, neg_neg]

/-- **Damping and inertia are never both non-transversal on the slice**: at a slice Hopf point,
`τ_D = 0` (`𝔗 = 0`) forces `τ_M ≠ 0` (`𝔍 ≠ 0`,
`Line.VSMLPF.Model.sliceInertia_ne_zero_of_sliceTransversality_eq_zero`). Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem Model.paramTrace_inert_ne_zero_of_paramTrace_eq_zero_slice
    {m : Model} (hp : Meets m .physical) (hs : m.OnSlice) {ω : ℝ} (hH : m.HopfAt ω)
    (h0 : Dynamics.PlanarHopf.paramTrace ((critπ (m.sliceP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (dampJac m.g.M)).comp
          (critι (m.sliceQ ω)))) = 0) :
    Dynamics.PlanarHopf.paramTrace ((critπ (m.sliceP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) (inertJac m.g.D)).comp
          (critι (m.sliceQ ω)))) ≠ 0 := by
  have hT : sliceTransversality (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω = 0 := by
    have e := m.sign_paramTrace_dampJac_slice hp hs hH
    rw [h0, sign_zero] at e
    have e' : SignType.sign (sliceTransversality (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω) =
        -0 := by rw [e, neg_neg]
    exact sign_eq_zero_iff.mp e'
  intro hτ
  have e := m.sign_paramTrace_inertJac_slice hp hs hH
  rw [hτ, sign_zero, eq_comm, sign_eq_zero_iff] at e
  exact m.sliceInertia_ne_zero_of_sliceTransversality_eq_zero hp hs hH hT e

/-! ## The Hopf cycles (private evidence) -/

/-- **Hopf cycles of a one-parameter family through a slice Hopf point.** For a family `F` of a
balanced physical slice model at a Hopf point `ω` with `𝔅 ≠ 0`, whose augmented field is
smooth, which keeps the origin fixed, equals the model field at `μ = 0` and whose transversality
coefficient at (`sliceQ`, `sliceP`) has the sign of `s ≠ 0`: for every small `μ` with
`μ s 𝔅 > 0` there is a nonconstant periodic orbit of period at most `4π/ω` with
`c|μ|/8 ≤ ‖critπ p z(t)‖² ≤ 8c|μ|`, `c = |τ|/(ω|ℓ₁|)` (`HopfCycle.exists_hopfCycle`). Private
evidence. -/
@[tmio TM, powerlib_domain] private theorem Model.exists_hopfCycle_slice_of_family (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hs : m.OnSlice) {ω : ℝ}
    (hH : m.HopfAt ω) (hB : sliceBautin (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ≠ 0)
    {F : State 5 → ℝ → State 5} {B : State 5 →L[ℝ] State 5}
    (hF : ∀ k : WithTop ℕ∞, ContDiff ℝ k (augField F)) (hF0 : ∀ μ, F 0 μ = 0)
    (hFm : (fun z => F z 0) = m.field)
    (hFB : HasDerivAt (fun μ => fderiv ℝ (fun z => F z μ) 0) B 0) {s : ℝ} (hs0 : s ≠ 0)
    (hsg : SignType.sign (Dynamics.PlanarHopf.paramTrace ((critπ (m.sliceP ω)).comp
        (B.comp (critι (m.sliceQ ω))))) = SignType.sign s) :
    ∃ δ > 0, ∃ c > 0, ∀ μ, |μ| < δ →
      0 < μ * s * sliceBautin (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω →
      ∃ z : ℝ → State 5, ∃ T, 0 < T ∧ T ≤ 4 * Real.pi / ω ∧
        (∀ t, HasDerivAt z (F (z t) μ) t) ∧ (∀ t, z (t + T) = z t) ∧ (∃ t, z t ≠ z 0) ∧
        ∀ t, c * |μ| / 8 ≤ ‖critπ (m.sliceP ω) (z t)‖ ^ 2 ∧
          ‖critπ (m.sliceP ω) (z t)‖ ^ 2 ≤ 8 * (c * |μ|) := by
  have hω := hH.1
  have hcp0 := m.isCriticalPair_slice hp hb hs hH
  have hcp : IsCriticalPair (fun z => F z 0) 0 ω (m.sliceQ ω) (m.sliceP ω) := by
    rw [hFm]; exact hcp0
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_hopfAt hH
  have hchar' : (jacobianC (fun z => F z 0) 0).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r := by
    rw [hFm]; exact hchar
  have hsℓ := m.sign_firstLyapunov_slice hp hb hs hH hcp0
  set τ := Dynamics.PlanarHopf.paramTrace ((critπ (m.sliceP ω)).comp
      (B.comp (critι (m.sliceQ ω)))) with hτdef
  set ℓ := firstLyapunov (fun z => F z 0) 0 ω (m.sliceQ ω) (m.sliceP ω) with hℓdef
  have hℓe : ℓ = firstLyapunov m.field 0 ω (m.sliceQ ω) (m.sliceP ω) := by
    rw [hℓdef, hFm]
  rw [← hℓe] at hsℓ
  have hτ0 : τ ≠ 0 := by
    intro h
    rw [h, sign_zero, eq_comm, sign_eq_zero_iff] at hsg
    exact hs0 hsg
  have hℓ0 : ℓ ≠ 0 := by
    intro h
    have e : SignType.sign (sliceBautin (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω) =
        -SignType.sign ℓ := by rw [hsℓ, neg_neg]
    rw [h, sign_zero] at e
    exact hB (sign_eq_zero_iff.mp e)
  obtain ⟨δ, hδ, hcyc⟩ := Dynamics.HopfCycle.exists_hopfCycle (hF 1) (hF ⊤).contDiffAt.analyticAt
    hF0 hcp hchar' hr hFB hτ0 hℓ0
  have hκ : 0 < |τ| / (ω * |ℓ|) := div_pos (abs_pos.mpr hτ0) (mul_pos hω (abs_pos.mpr hℓ0))
  refine ⟨δ, hδ, |τ| / (ω * |ℓ|), hκ, fun μ hμ hpos => ?_⟩
  have hs' : μ * τ * ℓ < 0 := by
    have e : SignType.sign (μ * τ * ℓ) = -SignType.sign (μ * s *
        sliceBautin (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω) := by
      rw [sign_mul, sign_mul, hsg, hsℓ, sign_mul, sign_mul]
      simp only [mul_neg]
    rw [sign_pos hpos] at e
    exact sign_eq_neg_one_iff.mp e
  obtain ⟨z, T, hT0, hT4, hz, hzT, hznc, hamp⟩ := hcyc μ hμ hs'
  have hν : -(μ * τ) / (ω * ℓ) = |τ| / (ω * |ℓ|) * |μ| := by
    have habs : |μ| * |τ| * |ℓ| = -(μ * τ * ℓ) := by
      rw [← abs_mul, ← abs_mul]; exact abs_of_neg hs'
    have hl2 : ℓ ^ 2 = |ℓ| ^ 2 := (sq_abs ℓ).symm
    have hla : |ℓ| ≠ 0 := abs_ne_zero.mpr hℓ0
    rw [div_mul_eq_mul_div, div_eq_div_iff (mul_ne_zero hω.ne' hℓ0) (mul_ne_zero hω.ne' hla)]
    apply mul_right_cancel₀ hℓ0
    linear_combination (-(ω * |ℓ|)) * habs - (ω * |μ| * |τ|) * hl2
  refine ⟨z, T, hT0, hT4, hz, hzT, hznc, fun t => ?_⟩
  have := hamp t
  rw [hν] at this
  constructor
  · linarith [this.1]
  · linarith [this.2]

/-- **Hopf cycles on the zero-current slice along the damping.** At a Hopf point `ω` of a
balanced physical slice model with `𝔅 ≠ 0` (`ℓ₁ ≠ 0`) and `𝔗 ≠ 0` (`τ_D ≠ 0`): for every small
`μ` with `μ 𝔗 𝔅 < 0` the model with the damping `D + μ` has a nonconstant periodic orbit of
period at most `4π/ω` with `c|μ|/8 ≤ ‖critπ p z(t)‖² ≤ 8c|μ|`, `c > 0`. Private evidence. -/
@[tmio TM, powerlib_domain] private theorem Model.exists_hopfCycle_slice_damping (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hs : m.OnSlice) {ω : ℝ}
    (hH : m.HopfAt ω) (hB : sliceBautin (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ≠ 0)
    (hT : sliceTransversality (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ≠ 0) :
    ∃ δ > 0, ∃ c > 0, ∀ μ, |μ| < δ →
      μ * sliceTransversality (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω *
          sliceBautin (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω < 0 →
      ∃ z : ℝ → State 5, ∃ T, 0 < T ∧ T ≤ 4 * Real.pi / ω ∧
        (∀ t, HasDerivAt z (m.dampFamily (z t) μ) t) ∧ (∀ t, z (t + T) = z t) ∧
        (∃ t, z t ≠ z 0) ∧ ∀ t, c * |μ| / 8 ≤ ‖critπ (m.sliceP ω) (z t)‖ ^ 2 ∧
          ‖critπ (m.sliceP ω) (z t)‖ ^ 2 ≤ 8 * (c * |μ|) := by
  have hsg := m.sign_paramTrace_dampJac_slice hp hs hH
  rw [← Left.sign_neg] at hsg
  obtain ⟨δ, hδ, c, hc, h⟩ := m.exists_hopfCycle_slice_of_family hp hb hs hH hB
    (fun _ => m.contDiff_augField_dampFamily) (m.dampFamily_origin hp hb)
    m.dampFamily_zero_param m.hasDerivAt_fderiv_dampFamily (neg_ne_zero.mpr hT) hsg
  refine ⟨δ, hδ, c, hc, fun μ hμ hneg => h μ hμ ?_⟩
  linarith [show μ * -sliceTransversality (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω *
      sliceBautin (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω =
    -(μ * sliceTransversality (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω *
      sliceBautin (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω) by ring]

/-- **Hopf cycles on the zero-current slice along the inverse inertia.** At a Hopf point `ω` of a
balanced physical slice model with `𝔅 ≠ 0` and `𝔍 ≠ 0` (`τ_M ≠ 0`): for every small `μ` with
`μ 𝔍 𝔅 > 0` the model with the inverse inertia `1/M + μ` has a nonconstant periodic orbit of
period at most `4π/ω` with `c|μ|/8 ≤ ‖critπ p z(t)‖² ≤ 8c|μ|`, `c > 0`. Private evidence. -/
@[tmio TM, powerlib_domain] private theorem Model.exists_hopfCycle_slice_inertia (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hs : m.OnSlice) {ω : ℝ}
    (hH : m.HopfAt ω) (hB : sliceBautin (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ≠ 0)
    (hJ : sliceInertia (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ≠ 0) :
    ∃ δ > 0, ∃ c > 0, ∀ μ, |μ| < δ →
      0 < μ * sliceInertia (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω *
          sliceBautin (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω →
      ∃ z : ℝ → State 5, ∃ T, 0 < T ∧ T ≤ 4 * Real.pi / ω ∧
        (∀ t, HasDerivAt z (m.inertFamily (z t) μ) t) ∧ (∀ t, z (t + T) = z t) ∧
        (∃ t, z t ≠ z 0) ∧ ∀ t, c * |μ| / 8 ≤ ‖critπ (m.sliceP ω) (z t)‖ ^ 2 ∧
          ‖critπ (m.sliceP ω) (z t)‖ ^ 2 ≤ 8 * (c * |μ|) :=
  m.exists_hopfCycle_slice_of_family hp hb hs hH hB (fun _ => m.contDiff_augField_inertFamily)
    (m.inertFamily_origin hp hb) m.inertFamily_zero_param m.hasDerivAt_fderiv_inertFamily hJ
    (m.sign_paramTrace_inertJac_slice hp hs hH)

/-- **Hopf cycles at every slice Hopf point with `𝔅 ≠ 0`.** At every Hopf point `ω` of a
balanced physical slice model with `𝔅 ≠ 0`: either `𝔗 ≠ 0` and the damping unfolds the cycles
(`Model.exists_hopfCycle_slice_damping`), or `𝔗 = 0`, then `𝔍 ≠ 0`
(`Line.VSMLPF.Model.sliceInertia_ne_zero_of_sliceTransversality_eq_zero`) and the inverse inertia
unfolds them (`Model.exists_hopfCycle_slice_inertia`). Private evidence. -/
@[tmio TM, powerlib_domain] private theorem Model.exists_hopfCycle_slice_of_sliceBautin_ne
    (m : Model) (hp : Meets m .physical) (hb : Meets m .balanced) (hs : m.OnSlice) {ω : ℝ}
    (hH : m.HopfAt ω) (hB : sliceBautin (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ≠ 0) :
    (sliceTransversality (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ≠ 0 ∧
      ∃ δ > 0, ∃ c > 0, ∀ μ, |μ| < δ →
        μ * sliceTransversality (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω *
          sliceBautin (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω < 0 →
        ∃ z : ℝ → State 5, ∃ T, 0 < T ∧ T ≤ 4 * Real.pi / ω ∧
          (∀ t, HasDerivAt z (m.dampFamily (z t) μ) t) ∧ (∀ t, z (t + T) = z t) ∧
          (∃ t, z t ≠ z 0) ∧ ∀ t, c * |μ| / 8 ≤ ‖critπ (m.sliceP ω) (z t)‖ ^ 2 ∧
            ‖critπ (m.sliceP ω) (z t)‖ ^ 2 ≤ 8 * (c * |μ|)) ∨
    (sliceInertia (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω ≠ 0 ∧
      ∃ δ > 0, ∃ c > 0, ∀ μ, |μ| < δ →
        0 < μ * sliceInertia (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω *
          sliceBautin (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω →
        ∃ z : ℝ → State 5, ∃ T, 0 < T ∧ T ≤ 4 * Real.pi / ω ∧
          (∀ t, HasDerivAt z (m.inertFamily (z t) μ) t) ∧ (∀ t, z (t + T) = z t) ∧
          (∃ t, z t ≠ z 0) ∧ ∀ t, c * |μ| / 8 ≤ ‖critπ (m.sliceP ω) (z t)‖ ^ 2 ∧
            ‖critπ (m.sliceP ω) (z t)‖ ^ 2 ≤ 8 * (c * |μ|)) := by
  by_cases hT : sliceTransversality (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 ω = 0
  · have hJ := m.sliceInertia_ne_zero_of_sliceTransversality_eq_zero hp hs hH hT
    exact Or.inr ⟨hJ, m.exists_hopfCycle_slice_inertia hp hb hs hH hB hJ⟩
  · exact Or.inl ⟨hT, m.exists_hopfCycle_slice_damping hp hb hs hH hB hT⟩

/-- **Supercritical cycles at `hopfWitnessSup`**: `ℓ₁ = −14341/14450 < 0` and `τ = −46/25 < 0`, so
for every small `μ < 0` (damping just below the Hopf value, where the operating point is
unstable) the model with the damping `D + μ` has a nonconstant periodic orbit with
`κ|μ|/8 ≤ ‖critπ p z(t)‖² ≤ 8κ|μ|`, `κ > 0`. Private evidence. -/
@[tmio TM, powerlib_domain] private theorem hopfWitnessSup_exists_hopfCycle :
    ∃ δ > 0, ∃ κ > 0, ∀ μ, -δ < μ → μ < 0 →
      ∃ z : ℝ → State 5, ∃ T, 0 < T ∧ (∀ t, HasDerivAt z (hopfWitnessSup.dampFamily (z t) μ) t) ∧
        (∀ t, z (t + T) = z t) ∧ (∃ t, z t ≠ z 0) ∧
        ∀ t, κ * |μ| / 8 ≤ ‖critπ hopfWitnessSupP (z t)‖ ^ 2 ∧
          ‖critπ hopfWitnessSupP (z t)‖ ^ 2 ≤ 8 * (κ * |μ|) := by
  have hcp : IsCriticalPair (fun z => hopfWitnessSup.dampFamily z 0) 0 1 hopfWitnessSupQ
      hopfWitnessSupP := by
    rw [hopfWitnessSup.dampFamily_zero_param]; exact hopfWitnessSup_isCriticalPair
  obtain ⟨r, hchar, hr⟩ := hopfWitnessSup.exists_charpoly_factor_of_hopfAt hopfWitnessSup_hopfAt
  rw [← hopfWitnessSup.dampFamily_zero_param] at hchar
  have hl : firstLyapunov (fun z => hopfWitnessSup.dampFamily z 0) 0 1 hopfWitnessSupQ
      hopfWitnessSupP = -14341 / 14450 := by
    rw [hopfWitnessSup.dampFamily_zero_param]; exact hopfWitnessSup_firstLyapunov
  obtain ⟨δ, hδ, hcyc⟩ := Dynamics.HopfCycle.exists_hopfCycle
    hopfWitnessSup.contDiff_augField_dampFamily
    (hopfWitnessSup.contDiff_augField_dampFamily (k := ⊤)).contDiffAt.analyticAt
    (hopfWitnessSup.dampFamily_origin hopfWitnessSup_physical hopfWitnessSup_balanced) hcp hchar
    hr hopfWitnessSup.hasDerivAt_fderiv_dampFamily (by rw [hopfWitnessSup_paramTrace]; norm_num)
    (by rw [hl]; norm_num)
  refine ⟨δ, hδ, 26588 / 14341, by norm_num, fun μ h1 h2 => ?_⟩
  have hμ : |μ| < δ := by rw [abs_of_neg h2]; linarith
  obtain ⟨z, T, hT0, -, hz, hzT, hznc, hamp⟩ :=
    hcyc μ hμ (by rw [hopfWitnessSup_paramTrace, hl]; nlinarith)
  refine ⟨z, T, hT0, hz, hzT, hznc, fun t => ?_⟩
  have := hamp t
  rw [hopfWitnessSup_paramTrace, hl,
    show -(μ * (-46 / 25 : ℝ)) / (1 * (-14341 / 14450)) = 26588 / 14341 * -μ by ring] at this
  rw [abs_of_neg h2]
  exact this

/-- **Subcritical cycles at `hopfWitness`**: `ℓ₁ > 0` and `τ < 0`, so for every small `μ > 0`
(damping just above the Hopf value, around a stable operating point) the model with the damping
`D + μ` has a nonconstant periodic orbit with `κμ/8 ≤ ‖critπ p z(t)‖² ≤ 8κμ`, `κ > 0`. Private
evidence. -/
@[tmio TM, powerlib_domain] private theorem hopfWitness_exists_hopfCycle :
    ∃ δ > 0, ∃ κ > 0, ∀ μ, 0 < μ → μ < δ →
      ∃ z : ℝ → State 5, ∃ T, 0 < T ∧ (∀ t, HasDerivAt z (hopfWitness.dampFamily (z t) μ) t) ∧
        (∀ t, z (t + T) = z t) ∧ (∃ t, z t ≠ z 0) ∧
        ∀ t, κ * μ / 8 ≤ ‖critπ hopfWitnessP (z t)‖ ^ 2 ∧
          ‖critπ hopfWitnessP (z t)‖ ^ 2 ≤ 8 * (κ * μ) := by
  have hcp : IsCriticalPair (fun z => hopfWitness.dampFamily z 0) 0 1 hopfWitnessQ
      hopfWitnessP := by
    rw [hopfWitness.dampFamily_zero_param]; exact hopfWitness_isCriticalPair
  obtain ⟨r, hchar, hr⟩ := hopfWitness.exists_charpoly_factor_of_hopfAt hopfWitness_hopfAt
  rw [← hopfWitness.dampFamily_zero_param] at hchar
  have hl : firstLyapunov (fun z => hopfWitness.dampFamily z 0) 0 1 hopfWitnessQ
      hopfWitnessP = 795686360348046533 / 264278927960175000 := by
    rw [hopfWitness.dampFamily_zero_param]; exact hopfWitness_firstLyapunov
  obtain ⟨δ, hδ, hcyc⟩ := Dynamics.HopfCycle.exists_hopfCycle
    hopfWitness.contDiff_augField_dampFamily
    (hopfWitness.contDiff_augField_dampFamily (k := ⊤)).contDiffAt.analyticAt
    (hopfWitness.dampFamily_origin hopfWitness_physical hopfWitness_balanced) hcp hchar
    hr hopfWitness.hasDerivAt_fderiv_dampFamily (by rw [hopfWitness_paramTrace]; norm_num)
    (by rw [hl]; norm_num)
  refine ⟨δ, hδ, 19922136287875 / 19646091710033, by norm_num, fun μ h1 h2 => ?_⟩
  have hμ : |μ| < δ := by rw [abs_of_pos h1]; exact h2
  obtain ⟨z, T, hT0, -, hz, hzT, hznc, hamp⟩ :=
    hcyc μ hμ (by rw [hopfWitness_paramTrace, hl]; nlinarith)
  refine ⟨z, T, hT0, hz, hzT, hznc, fun t => ?_⟩
  have := hamp t
  rw [hopfWitness_paramTrace, hl,
    show -(μ * (-581472978503 / 190454141400 : ℝ)) / (1 * (795686360348046533 /
      264278927960175000)) = 19922136287875 / 19646091710033 * μ by ring] at this
  exact this

end VSMLPF
end powerlib.GFM.Line
