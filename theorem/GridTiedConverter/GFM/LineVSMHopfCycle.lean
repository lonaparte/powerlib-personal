import theorem.GridTiedConverter.GFM.HopfLyapunovSymbolic
import theorem.GridTiedConverter.GFM.HopfBautinLine
import theorem.Dynamics.HopfCycleAmplitude

/-! # The VSM on a dynamic line: transversality along the damping and the inertia, Hopf cycles

Domain module.

Model boundary.
* The four-state VSM `Line.VSM` of `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged:
  state `(δ, ω, i_d, i_q) : State 4`, grid dq frame at `ω₀`, export-positive power, constant `E`,
  `M ω̇ = P_ref − P_e − D ω`, `L i̇ = E e^{jδ} − V − (R + jX) i`; no power filter, voltage loop,
  inner loops, PLL, delay or PWM. Read about a selected angle (`Line.VSM.Model`), translated so
  that the operating point is the origin.
* The Hopf points of `theorem/GridTiedConverter/GFM/HopfLyapunovCurrent.lean`: every balanced
  physical model (`E, V, L, ω₀, M, D > 0`, `R ≥ 0`, any angle `δ*`) on the Hopf boundary
  `a₃a₂a₁ = a₁² + a₃²a₀` with `a₁, a₀ > 0`, its frequency `ω = √(a₁/a₃)` and its critical pair
  (`Line.VSM.Model.critQ`, `Line.VSM.Model.critP`); the zero-current slice
  (`Line.VSM.zeroCurrent`, `V = E`, `P_ref = 0`, `δ* = 0`) of
  `theorem/GridTiedConverter/GFM/HopfLyapunovSymbolic.lean` with the pair `angleZeroQ`,
  `angleZeroP` at `κ = 0`.
* The unfolding parameter is the damping: `μ` replaces `D` by `D + μ` (`Line.VSM.dampShift`). The
  operating point `(δ*, 0, i_s(δ*))` and the balance `P(δ*) = P_ref` depend only on the network,
  so the translated family `Line.VSM.Model.dampFamily` keeps the origin as an equilibrium. The
  second unfolding parameter is the inverse inertia: `μ` replaces `1/M` by `1/M + μ`
  (`Line.VSM.inertShift`, `M ↦ (M⁻¹ + μ)⁻¹`, physical for `μ > −1/M`); the operating point and
  the balance do not depend on `M` either (`Line.VSM.Model.inertFamily`).
* Notation: `d = D/M`, `σ = R/L`, `w = ω₀`, `κ = Q/M`, `ρ = σ² + w²`; `a₃ = 2σ + d`,
  `a₂ = ρ + 2σd − κ`, `a₁ = dρ − 2σκ` (`Line.VSM.Model.coeff_atoms`).
* Level: exact identities and signs for all parameters of the region (the transversality
  coefficient `τ = tr (critπ p ∘ ∂J/∂D ∘ critι q) = 2 Re ⟨p, (∂J/∂D) q⟩`, twice the crossing speed
  of the critical eigenvalues), and, as private evidence, the cycles of the generic Hopf theorem
  `Dynamics.HopfCycle.exists_hopfCycle` for this family. Periodic orbits are not sentences of
  `Line.VSM.family`: no new family, no connection conclusion. Every small cycle
  (`Dynamics.HopfCycle.periodic_amplitude`): no small cycle on the other side; amplitude
  `(1 ± η) ν`. Not proved: uniqueness and orbital stability of the cycles, the cycles at the
  degenerate points `𝔅_δ = 0` (Bautin).

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.4–3.5 (Theorem 3.3, the
transversality coefficient `Re λ'(0) = Re ⟨p, A'(0) q⟩`); Hassard–Kazarinoff–Wan, *Theory and
Applications of Hopf Bifurcation* (1981), Ch. 1; the critical pair and `ℓ₁` of
`theorem/GridTiedConverter/GFM/HopfLyapunovCurrent.lean`; the template
`theorem/GridTiedConverter/GFM/VSMLPFHopfCycle.lean`. The closed forms were derived with SymPy in
exact rational arithmetic (exact division modulo the frequency relation, factorisation over `ℚ`;
untrusted discovery) and are checked by the kernel (`field_simp`, `linear_combination`).

Results.
* The family: `Line.VSM.dampShift`, `Line.VSM.Model.dampFamily`, `Line.VSM.dampJac`
  (`∂J/∂D = −(1/M) e₁e₁ᵀ`); `dampShift_zero`, `dampShift_field`, `Model.dampFamily_zero_param`,
  `Model.dampFamily_origin`, `dampShift_jacobian`, `Model.fderiv_dampFamily`,
  `Model.hasDerivAt_fderiv_dampFamily` (the Jacobian is affine in `μ` with slope `∂J/∂D`).
* `paramTrace_dampJac_apply` (`τ = −(2/M) Re(p̄₁ q₁)` for every pair) and the closed form at the
  pair of every angle, `paramTrace_dampJac`:
  `τ = −N(d, σ, w, κ, ω)/(M |r(iω)|²)`, `N = transNum = 2σω²(2σ + d) + (ρ − ω²)(a₂ − 2ω²)`,
  `|r(iω)|² = angleZeroR1` (`r` the stable factor; the rotation `rotC δ*` does not enter).
* **`τ` at every Hopf boundary point** (`Line.VSM.Model.paramTrace_crit`): at the critical pair of
  every balanced physical boundary model,
  `τ = −2σ 𝔗(d, σ, ω₀, κ)/(M (a₁a₃³ + (a₂a₃ − 2a₁)²))`, the transversality form
  `𝔗 = transForm` (degree 5, 16 terms, `(2σ + d)² N = 2σ 𝔗` on `a₃ω² = a₁`).
* **Its sign** (`Line.VSM.Model.sign_paramTrace_crit`): `sign τ = −sign 𝔗(D/M, R/L, ω₀, Q/M)`; `τ`
  vanishes exactly on `𝔗 = 0`. At the critical frequency
  `2σ N = 4σ²(2σω² + dρ) + (2σ − d)(ρ − ω²)²`, so `τ < 0` whenever `D/M ≤ 2R/L`
  (`Line.VSM.Model.paramTrace_crit_neg_of_le`: more damping stabilizes).
* The zero-current slice (`κ = 0`): `transForm_zero` (`𝔗 = ρ 𝔖`,
  `𝔖 = sliceTrans = (d + σ)(d² + 5dσ + 2σ²) − (d − 2σ)w²`), `zeroCurrent_sign_paramTrace`
  (`sign τ = −sign 𝔖(D/M, R/L, ω₀)`: `τ < 0` for `d ≤ 2σ`, `τ = 0` on the curve
  `(d − 2σ)ω₀² = (d + σ)(d² + 5dσ + 2σ²)`, `τ > 0` beyond it), and the witness
  `zeroCurrentHopf_paramTrace_pos` (`zeroCurrentHopf 1 1 1 10 4`: `𝔖 = −10`, `τ > 0`, more
  damping destabilizes): `τ` has no fixed sign on the boundary.
* The Bautin path of `theorem/GridTiedConverter/GFM/HopfBautinLine.lean`:
  `bautinPath_paramTrace_neg` (`τ < 0` at every point).
* The family along the inverse inertia: `Line.VSM.inertShift`, `Line.VSM.Model.inertFamily`,
  `Line.VSM.inertJac`, `Line.VSM.Model.inertJac` (`∂J/∂μ`: the single row
  `(Q_e, −D, −E cos δ, −E sin δ)`); `inertShift_zero`, `inertShift_field`,
  `Model.inertFamily_zero_param`, `Model.inertFamily_origin`, `inertShift_jacobian`,
  `Model.fderiv_inertFamily`, `Model.hasDerivAt_fderiv_inertFamily`.
* **`τ_M` in closed form** (`Line.VSM.Model.paramTrace_inertJac`): at (`critQ ω`, `critP ω`), every
  angle and every `ω > 0`, the row of `∂J/∂μ` maps the critical vector to `−E ω₀ ω²` and
  `τ_M = M ω² N_M/|r(iω)|²`, `N_M = inertNum = (ρ − ω²)(2σ + d) − 2σ(a₂ − 2ω²)`. At every Hopf
  boundary point (`Line.VSM.Model.paramTrace_inert_crit`) `N_M = 2d(ω₀² − σ² − ω²)` and
  `τ_M = 4Dσ a₁ 𝔍/(a₁a₃³ + (a₂a₃ − 2a₁)²)`, `𝔍 = inertForm = ω₀² − σ² − σd + κ`; its sign
  (`Line.VSM.Model.sign_paramTrace_inert_crit`): `sign τ_M = sign 𝔍`.
* **`τ_D` and `τ_M` never vanish together**: `transForm_eq_inertForm`
  (`𝔗 = ω₀²(d + 2σ)³ + 𝔍 (2σκ − dκ − d²σ − 5dσ² − dω₀² − 2σ³ + 2σω₀²)`, so `𝔍 = 0` forces
  `𝔗 > 0`), `Line.VSM.Model.paramTrace_inert_ne_zero_of_paramTrace_eq_zero` (`τ_D = 0 ⇒ τ_M ≠ 0`
  at every boundary point).
* Private evidence `Line.VSM.Model.hopfData_of_family` (the shared Hopf data),
  `Line.VSM.Model.periodic_amplitude_of_family`, `Model.periodic_amplitude_damping`,
  `Model.periodic_amplitude_inertia` (every small cycle is on the cycle side, with amplitude
  `(1 ± η) c|μ|`).
* Private evidence: `Line.VSM.Model.exists_hopfCycle_of_family` (the cycles of
  `Dynamics.HopfCycle.exists_hopfCycle` for any family through a boundary point with a given
  sign of `τ`), `Line.VSM.Model.exists_hopfCycle_damping` (`𝔅_δ ≠ 0`, `𝔗 ≠ 0`: for every small
  `μ` with `μ 𝔗 𝔅_δ < 0` the model with the damping `D + μ` has a nonconstant periodic orbit
  around the operating point with `c|μ|/8 ≤ ‖critπ p z(t)‖² ≤ 8c|μ|`, `c = |τ|/(ω|ℓ₁|) > 0`),
  `Line.VSM.Model.exists_hopfCycle_inertia` (`𝔅_δ ≠ 0`, `𝔍 ≠ 0`, `μ 𝔍 𝔅_δ > 0`, inverse inertia
  `1/M + μ`), and `Line.VSM.Model.exists_hopfCycle_of_bautinFormAngle_ne`: **at every balanced
  physical boundary point (every angle) with `𝔅_δ ≠ 0`** the cycles exist, along the damping
  if `𝔗 ≠ 0` and along the inverse inertia if `𝔗 = 0`; with them
  `Model.contDiff_augField_dampFamily`, `Model.contDiff_augField_inertFamily`.
-/

noncomputable section
namespace powerlib.GFM.Line
namespace VSM
open Polynomial Complex
open powerlib.Dynamics (State)
open powerlib.Dynamics.HopfCycle (augField xpart mpart xin)
open powerlib.NormalForm.LyapunovCoefficient
open powerlib.Dynamics.CenterManifold (critπ critι critι_apply critπ_apply0 critπ_apply1 reV_apply
  imV_apply)
open powerlib.Dynamics.Degenerate.PlanarFocus (e0 e1 e0_apply0 e0_apply1 e1_apply0 e1_apply1)

/-! ## The family along the damping -/

/-- The parameters with the damping shifted by `μ`: `D ↦ D + μ` (network, inertia and set-point
unchanged). -/
def dampShift (g : VSM) (μ : ℝ) : VSM := ⟨g.toNetwork, g.M, g.D + μ, g.Pref⟩

/-- The translated field of the model with the damping `D + μ`, as a family in `μ`
(`z = x − (δ*, 0, i_s(δ*))`; the operating point does not depend on the damping). -/
def Model.dampFamily (m : Model) (z : State 4) (μ : ℝ) : State 4 :=
  (m.g.dampShift μ).field (z + m.point)

/-- The parameter derivative of the Jacobian: `∂J/∂D = −(1/M) e₁ e₁ᵀ`. -/
def dampJac (M : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0; 0, -(1 / M), 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

@[tmio M, simp, powerlib_domain] theorem dampShift_zero (g : VSM) : g.dampShift 0 = g := by
  cases g; simp [dampShift]

/-- The damping enters only the rate row: `F_{D+μ}(x) = F_D(x) − (μ x₁/M) e₁`. -/
@[tmio M, powerlib_domain] theorem dampShift_field (g : VSM) (μ : ℝ) (x : State 4) :
    (g.dampShift μ).field x = g.field x - (μ * x 1 / g.M) • EuclideanSpace.single 1 1 := by
  ext i
  fin_cases i <;> simp [field, dampShift]
  ring

@[tmio M, powerlib_domain] theorem Model.dampFamily_zero_param (m : Model) :
    (fun z => m.dampFamily z 0) = m.field := by
  funext z; simp [Model.dampFamily, Model.field]

@[tmio M, powerlib_domain] theorem Model.dampFamily_origin (m : Model) (hp : Meets m .physical)
    (hb : Meets m .balanced) (μ : ℝ) : m.dampFamily 0 μ = 0 := by
  have h := (m.field_point_eq_zero_iff hp.2.1.ne' hp.1.L.ne' hp.1.absSq_pos.ne').mpr hb
  rw [Model.dampFamily, zero_add, dampShift_field, h]
  simp [Model.point, qss]

@[tmio M, powerlib_domain] private theorem Model.contDiff_augField_dampFamily (m : Model)
    {k : WithTop ℕ∞} : ContDiff ℝ k (augField m.dampFamily) := by
  have hx : ContDiff ℝ k fun w : State (4 + 1) => xpart w + m.point :=
    xpart.contDiff.add contDiff_const
  have h : ContDiff ℝ k (fun w : State (4 + 1) => m.dampFamily (xpart w) (mpart w)) := by
    have hc : ContDiff ℝ k fun w : State (4 + 1) => mpart w * (xpart w + m.point) 1 / m.g.M :=
      (mpart.contDiff.mul ((PiLp.proj 2 (fun _ : Fin 4 => ℝ) 1).contDiff.comp hx)).div_const _
    simp only [Model.dampFamily, dampShift_field]
    exact (m.g.contDiff_field.comp hx).sub (hc.smul contDiff_const)
  exact xin.contDiff.comp h

@[tmio M, powerlib_domain] theorem dampShift_jacobian (g : VSM) (μ δ id iq : ℝ) :
    (g.dampShift μ).jacobian δ id iq = g.jacobian δ id iq + μ • dampJac g.M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jacobian, dampShift, dampJac]
  ring

@[tmio M, powerlib_domain] theorem Model.fderiv_dampFamily (m : Model) (μ : ℝ) :
    fderiv ℝ (fun z => m.dampFamily z μ) 0 =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.jac +
        μ • Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (dampJac m.g.M) := by
  rw [show (fun z => m.dampFamily z μ) = fun z => (m.g.dampShift μ).field (z + m.point) from rfl,
    fderiv_comp_add_right, zero_add, fderiv_field, dampShift_jacobian]
  simp [Model.point, qss, Model.jac, map_add, map_smul]

/-- **Transversality data**: `μ ↦ D_z F(0, μ)` is affine with slope `toEuclideanCLM (∂J/∂D)`. -/
@[tmio M, powerlib_domain] theorem Model.hasDerivAt_fderiv_dampFamily (m : Model) :
    HasDerivAt (fun μ => fderiv ℝ (fun z => m.dampFamily z μ) 0)
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (dampJac m.g.M)) 0 := by
  simp only [Model.fderiv_dampFamily]
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (dampJac m.g.M))).const_add
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.jac)

/-! ## The transversality coefficient -/

/-- The numerator of the transversality coefficient at the frequency `ω`:
`N = 2σω²(2σ + d) + (σ² + w² − ω²)(σ² + w² − 2ω² + 2σd − κ)`. -/
def transNum (d σ w κ ω : ℝ) : ℝ :=
  2 * σ * ω ^ 2 * (2 * σ + d) +
    (σ ^ 2 + w ^ 2 - ω ^ 2) * (σ ^ 2 + w ^ 2 - 2 * ω ^ 2 + 2 * σ * d - κ)

/-- **The transversality form** in the model parameters `d = D/M`, `σ = R/L`, `w = ω₀`,
`κ = Q/M` (`ρ = σ² + w²`): `𝔗 = d³ρ + 6d²σρ + d(7σ⁴ + 6σ²w² − w⁴ − κ² − 6κσ² − 2κw²) +
2σ(κ² − 2κσ² + 2κw² + ρ²)`; `2σ 𝔗 = 2σa₁a₃² + (ρa₃ − a₁)(a₂a₃ − 2a₁)`. -/
def transForm (d σ w κ : ℝ) : ℝ :=
  d ^ 3 * (σ ^ 2 + w ^ 2) + 6 * d ^ 2 * σ * (σ ^ 2 + w ^ 2) +
    d * (7 * σ ^ 4 + 6 * σ ^ 2 * w ^ 2 - w ^ 4 - κ ^ 2 - 6 * κ * σ ^ 2 - 2 * κ * w ^ 2) +
    2 * σ * (κ ^ 2 - 2 * κ * σ ^ 2 + 2 * κ * w ^ 2 + (σ ^ 2 + w ^ 2) ^ 2)

/-- **The transversality form of the zero-current slice**:
`𝔖 = (d + σ)(d² + 5dσ + 2σ²) − (d − 2σ)w²`. -/
def sliceTrans (d σ w : ℝ) : ℝ := (d + σ) * (d ^ 2 + 5 * d * σ + 2 * σ ^ 2) - (d - 2 * σ) * w ^ 2

/-- **The transversality coefficient along the damping, for every pair**:
`τ = tr (critπ p ∘ ∂J/∂D ∘ critι q) = −(2/M) Re(p̄₁ q₁)`. -/
@[tmio M, powerlib_domain] theorem paramTrace_dampJac_apply (M : ℝ) (p q : Fin 4 → ℂ) :
    Dynamics.PlanarHopf.paramTrace ((critπ p).comp
        ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (dampJac M)).comp (critι q))) =
      -(2 / M) * ((p 1).re * (q 1).re + (p 1).im * (q 1).im) := by
  have hB : ∀ v : State 4, Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (dampJac M) v =
      (-(v 1 / M)) • EuclideanSpace.single 1 1 := by
    intro v
    ext i
    fin_cases i <;> simp [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four, dampJac]
    ring
  simp only [Dynamics.PlanarHopf.paramTrace, Dynamics.PlanarHopf.m00, Dynamics.PlanarHopf.m11,
    ContinuousLinearMap.comp_apply, critι_apply, critπ_apply0, critπ_apply1, e0_apply0,
    e0_apply1, e1_apply0, e1_apply1, one_smul, zero_smul, add_zero, zero_add, hB]
  simp only [inner_smul_right, EuclideanSpace.inner_single_right, PiLp.add_apply, PiLp.sub_apply,
    reV_apply, imV_apply, conj_trivial, one_mul]
  ring

/-- **The transversality coefficient at the critical pair of every angle, in closed form**:
for the pair (`rotC θ (angleZeroQ a d κ σ w ω)`, `rotC θ (angleZeroP a d κ σ w ω)`) of
`HopfLyapunovCurrent` (`a, w, ω ≠ 0`), `τ = −N/(M |r(iω)|²)`, `N = transNum d σ w κ ω`,
`|r(iω)|² = angleZeroR1 d σ w κ ω`; the rotation angle does not enter. -/
@[tmio M, powerlib_domain] theorem paramTrace_dampJac {M a d κ σ w ω : ℝ} (θ : ℝ) (ha : a ≠ 0)
    (hw : w ≠ 0) (hω : ω ≠ 0) (hR : angleZeroR1 d σ w κ ω ≠ 0) :
    Dynamics.PlanarHopf.paramTrace ((critπ (rotC θ (angleZeroP a d κ σ w ω))).comp
        ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (dampJac M)).comp
          (critι (rotC θ (angleZeroQ a d κ σ w ω))))) =
      -(transNum d σ w κ ω / (M * angleZeroR1 d σ w κ ω)) := by
  rw [paramTrace_dampJac_apply]
  have hq : (rotC θ (angleZeroQ a d κ σ w ω) 1).re = 0 ∧
      (rotC θ (angleZeroQ a d κ σ w ω) 1).im = ω * a * w := by
    simp [rotC, angleZeroQ]
  have hpair : (angleZeroPairing a d κ σ w ω).re = 2 * a * ω * w * (ω * (2 * σ + d)) ∧
      (angleZeroPairing a d κ σ w ω).im =
        -(2 * a * ω * w * (σ ^ 2 + w ^ 2 - 2 * ω ^ 2 + 2 * σ * d - κ)) := by
    have e : angleZeroPairing a d κ σ w ω = ((2 * a * ω * w * (ω * (2 * σ + d)) : ℝ) : ℂ) +
        ((-(2 * a * ω * w * (σ ^ 2 + w ^ 2 - 2 * ω ^ 2 + 2 * σ * d - κ)) : ℝ) : ℂ) * I := by
      unfold angleZeroPairing; push_cast; ring
    rw [e]
    constructor <;> simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;> ring
  have hN : (angleZeroPairing a d κ σ w ω).re ^ 2 + (angleZeroPairing a d κ σ w ω).im ^ 2 =
      4 * a ^ 2 * ω ^ 2 * w ^ 2 * angleZeroR1 d σ w κ ω := by
    rw [hpair.1, hpair.2]; unfold angleZeroR1; ring
  have hp : (rotC θ (angleZeroP a d κ σ w ω) 1).im =
      transNum d σ w κ ω / (2 * a * ω * w * angleZeroR1 d σ w κ ω) := by
    have hN0 : (angleZeroPairing a d κ σ w ω).re ^ 2 + (angleZeroPairing a d κ σ w ω).im ^ 2 ≠
        0 := by
      rw [hN]; exact mul_ne_zero (by positivity) hR
    simp only [rotC, angleZeroP, angleZeroLeft, Matrix.cons_val_one, Matrix.cons_val_zero,
      Pi.smul_apply, smul_eq_mul, Complex.mul_im, Complex.inv_re, Complex.inv_im,
      Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    rw [show ∀ x : ℝ, x * x = x ^ 2 from fun x => (sq x).symm,
      show ∀ x : ℝ, -x * -x = x ^ 2 from fun x => by ring]
    rw [hN]
    simp only [Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, sq, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, hpair.1, hpair.2]
    unfold transNum
    field_simp
    ring
  rw [hq.1, hq.2, hp]
  field_simp
  ring

/-! ## The transversality coefficient at every Hopf boundary point -/

@[tmio M, powerlib_domain] private theorem model_coeff3_pos' {m : Model}
    (hp : Meets m .physical) : 0 < m.g.coeff3 := by
  obtain ⟨hN, hM, hD⟩ := hp
  have hR : 0 ≤ m.g.R := hN.R
  have hL : 0 < m.g.L := hN.L
  rw [(m.coeff_atoms hL.ne').1]
  positivity

/-- The frequency relation `a₃ ω² = a₁` in the atoms. -/
@[tmio M, powerlib_domain] private theorem freq_atoms {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hω2 : ω ^ 2 = m.g.coeff1 m.Q / m.g.coeff3) :
    (2 * (m.g.R / m.g.L) + m.g.D / m.g.M) * ω ^ 2 =
      m.g.D / m.g.M * ((m.g.R / m.g.L) ^ 2 + m.g.ω0 ^ 2) - 2 * (m.g.R / m.g.L) * (m.Q / m.g.M) := by
  have h3 := model_coeff3_pos' hp
  obtain ⟨e3, -, e1, -⟩ := m.coeff_atoms hp.1.L.ne'
  have h3' := h3.ne'
  rw [hω2, ← e1, ← e3]
  field_simp

/-- The closed form of `paramTrace_dampJac` at the critical pair of a physical model. -/
@[tmio M, powerlib_domain] private theorem model_paramTrace {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hω : 0 < ω) :
    Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (dampJac m.g.M)).comp
          (critι (m.critQ ω)))) =
      -(transNum (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ω /
        (m.g.M * angleZeroR1 (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ω)) := by
  obtain ⟨hN, hM, hD⟩ := hp
  have hE := hN.E
  have hR : 0 ≤ m.g.R := hN.R
  have hL := hN.L
  have hR1 : 0 < angleZeroR1 (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ω := by
    unfold angleZeroR1; positivity
  exact paramTrace_dampJac m.δ (by positivity) hN.ω0.ne' hω.ne' hR1.ne'

/-- **The transversality coefficient at every Hopf boundary point**: for every physical model and
the frequency `ω² = a₁/a₃` (on the Hopf boundary: its critical frequency, and
(`Model.critQ`, `Model.critP`) its critical pair, `Model.isCriticalPair_crit`), at every angle,
`τ = −2σ 𝔗(D/M, R/L, ω₀, Q/M)/(M (a₁a₃³ + (a₂a₃ − 2a₁)²))` (`transForm`). Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem Model.paramTrace_crit {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hω : 0 < ω) (hω2 : ω ^ 2 = m.g.coeff1 m.Q / m.g.coeff3) :
    Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (dampJac m.g.M)).comp
          (critι (m.critQ ω)))) =
      -(2 * (m.g.R / m.g.L) * transForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) /
        (m.g.M * (m.g.coeff1 m.Q * m.g.coeff3 ^ 3 +
          (m.g.coeff2 m.Q * m.g.coeff3 - 2 * m.g.coeff1 m.Q) ^ 2))) := by
  have hf := freq_atoms hp hω2
  have h3 := model_coeff3_pos' hp
  rw [model_paramTrace hp hω]
  obtain ⟨hN, hM, hD⟩ := hp
  have hR : 0 ≤ m.g.R := hN.R
  have hL := hN.L
  obtain ⟨e3, e2, e1, -⟩ := m.coeff_atoms hL.ne'
  have hR1 : 0 < angleZeroR1 (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ω := by
    unfold angleZeroR1; positivity
  rw [e3, e2, e1]
  rw [e3] at h3
  set d := m.g.D / m.g.M
  set σ := m.g.R / m.g.L
  set w := m.g.ω0
  set κ := m.Q / m.g.M
  have k1 : (2 * σ + d) ^ 2 * transNum d σ w κ ω = 2 * σ * transForm d σ w κ := by
    unfold transNum transForm
    linear_combination (d * κ + 2 * d * ω ^ 2 + 3 * d * σ ^ 2 - d * w ^ 2 - 2 * κ * σ +
      4 * ω ^ 2 * σ + 2 * σ ^ 3 - 6 * σ * w ^ 2) * hf
  have k2 : (2 * σ + d) ^ 2 * angleZeroR1 d σ w κ ω =
      (d * (σ ^ 2 + w ^ 2) - 2 * σ * κ) * (2 * σ + d) ^ 3 +
        ((σ ^ 2 + w ^ 2 + 2 * σ * d - κ) * (2 * σ + d) - 2 * (d * (σ ^ 2 + w ^ 2) -
          2 * σ * κ)) ^ 2 := by
    unfold angleZeroR1
    linear_combination ((2 * σ + d) ^ 3 - 4 * (σ ^ 2 + w ^ 2 + 2 * σ * d - κ) * (2 * σ + d) +
      4 * ω ^ 2 * (2 * σ + d) + 4 * (d * (σ ^ 2 + w ^ 2) - 2 * σ * κ)) * hf
  have hden : 0 < (d * (σ ^ 2 + w ^ 2) - 2 * σ * κ) * (2 * σ + d) ^ 3 +
      ((σ ^ 2 + w ^ 2 + 2 * σ * d - κ) * (2 * σ + d) - 2 * (d * (σ ^ 2 + w ^ 2) -
        2 * σ * κ)) ^ 2 := by
    rw [← k2]; exact mul_pos (by positivity) hR1
  congr 1
  rw [div_eq_div_iff (mul_pos hM hR1).ne' (mul_pos hM hden).ne']
  linear_combination (-(transNum d σ w κ ω * m.g.M)) * k2 + (m.g.M * angleZeroR1 d σ w κ ω) * k1

/-- **The sign of the transversality coefficient at every Hopf boundary point**:
`sign τ = −sign 𝔗(D/M, R/L, ω₀, Q/M)` (`transForm`) at the critical pair of every balanced
physical boundary model; `τ = 0` exactly on `𝔗 = 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.sign_paramTrace_crit {m : Model} {ω : ℝ}
    (hp : Meets m .physical)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q) (hω : 0 < ω)
    (hω2 : ω ^ 2 = m.g.coeff1 m.Q / m.g.coeff3) :
    SignType.sign (Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (dampJac m.g.M)).comp
          (critι (m.critQ ω))))) =
      -SignType.sign (transForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)) := by
  have hR := Model.R_pos_of_boundary hp hH
  have h3 := model_coeff3_pos' hp
  have hM := hp.2.1
  have hL := hp.1.L
  have hden : 0 < m.g.coeff1 m.Q * m.g.coeff3 ^ 3 +
      (m.g.coeff2 m.Q * m.g.coeff3 - 2 * m.g.coeff1 m.Q) ^ 2 := by
    have h1 : 0 < m.g.coeff1 m.Q := by
      have h := pow_pos hω 2
      rw [hω2, lt_div_iff₀ h3, zero_mul] at h
      exact h
    positivity
  rw [Model.paramTrace_crit hp hω hω2,
    show ∀ x : ℝ, -(2 * (m.g.R / m.g.L) * x / (m.g.M * (m.g.coeff1 m.Q * m.g.coeff3 ^ 3 +
        (m.g.coeff2 m.Q * m.g.coeff3 - 2 * m.g.coeff1 m.Q) ^ 2))) =
      -((2 * (m.g.R / m.g.L) / (m.g.M * (m.g.coeff1 m.Q * m.g.coeff3 ^ 3 +
        (m.g.coeff2 m.Q * m.g.coeff3 - 2 * m.g.coeff1 m.Q) ^ 2))) * x) from fun x => by ring,
    Left.sign_neg, sign_mul, sign_pos (div_pos (by positivity) (mul_pos hM hden)), one_mul]

/-- **More damping stabilizes when `D/M ≤ 2R/L`**: at the critical frequency
`2σ N = 4σ²(2σω² + dρ) + (2σ − d)(ρ − ω²)²` (the frequency relation
`d(ρ − ω²) = 2σ(κ + ω²)`), so `τ < 0` at every balanced physical boundary point with
`D/M ≤ 2R/L`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.paramTrace_crit_neg_of_le {m : Model} {ω : ℝ}
    (hp : Meets m .physical)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q) (hω : 0 < ω)
    (hω2 : ω ^ 2 = m.g.coeff1 m.Q / m.g.coeff3) (hd : m.g.D / m.g.M ≤ 2 * (m.g.R / m.g.L)) :
    Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (dampJac m.g.M)).comp
          (critι (m.critQ ω)))) < 0 := by
  have hR := Model.R_pos_of_boundary hp hH
  have h1 := (Model.freq_relations_of_boundary hp hH hω2).1
  rw [model_paramTrace hp hω]
  obtain ⟨hN, hM, hD⟩ := hp
  have hL := hN.L
  have hR1 : 0 < angleZeroR1 (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ω := by
    unfold angleZeroR1; positivity
  set d := m.g.D / m.g.M
  set σ := m.g.R / m.g.L
  set w := m.g.ω0
  set κ := m.Q / m.g.M
  have hσ : 0 < σ := by positivity
  have hd0 : 0 < d := by positivity
  have key : 2 * σ * transNum d σ w κ ω = 4 * σ ^ 2 * (2 * σ * ω ^ 2 + d * (σ ^ 2 + w ^ 2)) +
      (2 * σ - d) * (σ ^ 2 + w ^ 2 - ω ^ 2) ^ 2 := by
    unfold transNum
    linear_combination (σ ^ 2 + w ^ 2 - ω ^ 2) * h1
  have hpos : 0 < transNum d σ w κ ω := by
    have h2 : 0 ≤ (2 * σ - d) * (σ ^ 2 + w ^ 2 - ω ^ 2) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    have h4 : 0 < 4 * σ ^ 2 * (2 * σ * ω ^ 2 + d * (σ ^ 2 + w ^ 2)) := by positivity
    have : 0 < 2 * σ * transNum d σ w κ ω := by rw [key]; linarith
    exact pos_of_mul_pos_right this (by positivity)
  exact neg_neg_of_pos (div_pos hpos (mul_pos hM hR1))

/-! ## The zero-current slice -/

/-- **The transversality form on the slice `κ = 0`**: `𝔗(d, σ, w, 0) = (σ² + w²) 𝔖(d, σ, w)`. -/
@[tmio M, powerlib_domain] theorem transForm_zero (d σ w : ℝ) :
    transForm d σ w 0 = (σ ^ 2 + w ^ 2) * sliceTrans d σ w := by
  unfold transForm sliceTrans; ring

/-- **The sign of the transversality coefficient on the zero-current boundary**: at the critical
pair (`angleZeroQ`, `angleZeroP`, `κ = 0`) of every physical zero-current model on the Hopf
boundary, `sign τ = −sign 𝔖(D/M, R/L, ω₀)`, `𝔖 = (d + σ)(d² + 5dσ + 2σ²) − (d − 2σ)ω₀²`
(`sliceTrans`): `τ < 0` for `D/M ≤ 2R/L`, and for `D/M > 2R/L` it changes sign on the curve
`(d − 2σ)ω₀² = (d + σ)(d² + 5dσ + 2σ²)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem zeroCurrent_sign_paramTrace {E R L w M D ω : ℝ}
    (hp : Meets (zeroCurrent E R L w M D) .physical)
    (hH : (zeroCurrent E R L w M D).g.coeff3 * (zeroCurrent E R L w M D).g.coeff2
          (zeroCurrent E R L w M D).Q * (zeroCurrent E R L w M D).g.coeff1
          (zeroCurrent E R L w M D).Q =
        (zeroCurrent E R L w M D).g.coeff1 (zeroCurrent E R L w M D).Q ^ 2 +
          (zeroCurrent E R L w M D).g.coeff3 ^ 2 * (zeroCurrent E R L w M D).g.coeff0
            (zeroCurrent E R L w M D).Q) (hω : 0 < ω)
    (hω2 : ω ^ 2 = (zeroCurrent E R L w M D).g.coeff1 (zeroCurrent E R L w M D).Q /
      (zeroCurrent E R L w M D).g.coeff3) :
    SignType.sign (Dynamics.PlanarHopf.paramTrace
        ((critπ (angleZeroP (E / M) (D / M) 0 (R / L) w ω)).comp
          ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (dampJac M)).comp
            (critι (angleZeroQ (E / M) (D / M) 0 (R / L) w ω))))) =
      -SignType.sign (sliceTrans (D / M) (R / L) w) := by
  have h := Model.sign_paramTrace_crit hp hH hω hω2
  have hQ : (zeroCurrent E R L w M D).Q / M = 0 := by rw [zeroCurrent_Q, zero_div]
  have eq : (zeroCurrent E R L w M D).critQ ω = angleZeroQ (E / M) (D / M) 0 (R / L) w ω := by
    rw [Model.critQ, show (zeroCurrent E R L w M D).g.M = M from rfl, hQ]; exact rotC_zero _
  have ep : (zeroCurrent E R L w M D).critP ω = angleZeroP (E / M) (D / M) 0 (R / L) w ω := by
    rw [Model.critP, show (zeroCurrent E R L w M D).g.M = M from rfl, hQ]; exact rotC_zero _
  rw [eq, ep, show (zeroCurrent E R L w M D).g.M = M from rfl, hQ] at h
  rw [h]
  change -SignType.sign (transForm (D / M) (R / L) w 0) = _
  have hw : 0 < w := hp.1.ω0
  rw [transForm_zero, sign_mul, sign_pos (by positivity : (0 : ℝ) < (R / L) ^ 2 + w ^ 2), one_mul]

/-- **More damping can destabilize**: at the zero-current boundary point
`zeroCurrentHopf 1 1 1 10 4` (`E = R = L = 1`, `ω₀ = 10`, `D/M = 4`; `𝔖 = −10`) the
transversality coefficient is positive at every critical frequency: the critical eigenvalues
cross into the right half-plane as `D` increases. With `Line.VSM.Model.paramTrace_crit_neg_of_le`,
`τ` has no fixed sign on the Hopf boundary. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem zeroCurrentHopf_paramTrace_pos {ω : ℝ} (hω : 0 < ω)
    (hω2 : ω ^ 2 = (zeroCurrentHopf 1 1 1 10 4).g.coeff1 (zeroCurrentHopf 1 1 1 10 4).Q /
      (zeroCurrentHopf 1 1 1 10 4).g.coeff3) :
    0 < Dynamics.PlanarHopf.paramTrace ((critπ ((zeroCurrentHopf 1 1 1 10 4).critP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
          (dampJac (zeroCurrentHopf 1 1 1 10 4).g.M)).comp
          (critι ((zeroCurrentHopf 1 1 1 10 4).critQ ω)))) := by
  obtain ⟨hp, hdM, hH⟩ := zeroCurrentHopf_meets (E := 1) (R := 1) (L := 1) (w := 10) (d := 4)
    one_pos one_pos one_pos (by norm_num) (by norm_num)
  have h := Model.sign_paramTrace_crit hp hH hω hω2
  have hQ : (zeroCurrentHopf 1 1 1 10 4).Q / (zeroCurrentHopf 1 1 1 10 4).g.M = 0 := by
    rw [show (zeroCurrentHopf 1 1 1 10 4).Q = 0 from zeroCurrent_Q _ _ _ _ _ _, zero_div]
  have hT : transForm ((zeroCurrentHopf 1 1 1 10 4).g.D / (zeroCurrentHopf 1 1 1 10 4).g.M)
      ((zeroCurrentHopf 1 1 1 10 4).g.R / (zeroCurrentHopf 1 1 1 10 4).g.L)
      (zeroCurrentHopf 1 1 1 10 4).g.ω0
      ((zeroCurrentHopf 1 1 1 10 4).Q / (zeroCurrentHopf 1 1 1 10 4).g.M) < 0 := by
    rw [hQ, show (zeroCurrentHopf 1 1 1 10 4).g.D / (zeroCurrentHopf 1 1 1 10 4).g.M = 4 from hdM,
      transForm_zero]
    norm_num [sliceTrans, zeroCurrentHopf, zeroCurrent]
  rw [sign_neg hT, neg_neg] at h
  exact sign_eq_one_iff.mp h

/-- **Along the Bautin path the damping crosses transversally**: at every point of
`bautinPath s` (`s > 0`, frequency `1`, `D/M = 2/s`, `R/L = s`, `ω₀ = 1`, `Q = 0`) the
transversality coefficient is `τ = −(4s² + 4 + s²(s² + 3))/(M |r(i)|²) < 0`. Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem bautinPath_paramTrace_neg {s : ℝ} (hs : 0 < s) :
    Dynamics.PlanarHopf.paramTrace ((critπ ((bautinPath s).critP 1)).comp
        ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (dampJac (bautinPath s).g.M)).comp
          (critι ((bautinPath s).critQ 1)))) < 0 := by
  obtain ⟨-, hp⟩ := bautinPath_meets hs
  rw [model_paramTrace hp one_pos]
  have hQ : (bautinPath s).Q = 0 := by
    norm_num [Model.Q, Network.qssReactive, bautinPath, Network.is, Network.reactive_eq]
  have hd : (bautinPath s).g.D / (bautinPath s).g.M = 2 / s := by
    simp only [bautinPath]; field_simp
  have hσ : (bautinPath s).g.R / (bautinPath s).g.L = s := by simp [bautinPath]
  have hw : (bautinPath s).g.ω0 = 1 := rfl
  have hM : (bautinPath s).g.M = 1 / (4 + s ^ 2) := rfl
  rw [hQ, zero_div, hd, hσ, hw, hM]
  have hN : transNum (2 / s) s 1 0 1 = 4 * s ^ 2 + 4 + s ^ 2 * (s ^ 2 + 3) := by
    unfold transNum; field_simp; ring
  rw [hN]
  have hR1 : 0 < angleZeroR1 (2 / s) s 1 0 1 := by unfold angleZeroR1; positivity
  exact neg_neg_of_pos (div_pos (by positivity) (mul_pos (by positivity) hR1))

/-! ## The family along the inverse inertia -/

/-- The parameters with the inverse inertia shifted by `μ`: `1/M ↦ 1/M + μ`, i.e.
`M ↦ (M⁻¹ + μ)⁻¹` (network, damping and set-point unchanged). -/
def inertShift (g : VSM) (μ : ℝ) : VSM := ⟨g.toNetwork, (g.M⁻¹ + μ)⁻¹, g.D, g.Pref⟩

/-- The translated field of the model with the inverse inertia `1/M + μ`, as a family in `μ`
(the operating point does not depend on the inertia). -/
def Model.inertFamily (m : Model) (z : State 4) (μ : ℝ) : State 4 :=
  (m.g.inertShift μ).field (z + m.point)

/-- The parameter derivative of the Jacobian along the inverse inertia at angle `δ` and current
`(i_d, i_q)`: the single row `(Q_e, −D, −E cos δ, −E sin δ)` (`M` times the rate row of `J`). -/
def inertJac (g : VSM) (δ id iq : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0; g.reactive δ id iq, -g.D, -(g.E * Real.cos δ), -(g.E * Real.sin δ);
    0, 0, 0, 0; 0, 0, 0, 0]

/-- `∂J/∂μ` along the inverse inertia at the operating point. -/
def Model.inertJac (m : Model) : Matrix (Fin 4) (Fin 4) ℝ :=
  m.g.inertJac m.δ (m.g.is m.δ).re (m.g.is m.δ).im

/-- The numerator of the inverse-inertia transversality coefficient at the frequency `ω`:
`N_M = (σ² + w² − ω²)(2σ + d) − 2σ(σ² + w² − 2ω² + 2σd − κ)`. -/
def inertNum (d σ w κ ω : ℝ) : ℝ :=
  (σ ^ 2 + w ^ 2 - ω ^ 2) * (2 * σ + d) - 2 * σ * (σ ^ 2 + w ^ 2 - 2 * ω ^ 2 + 2 * σ * d - κ)

/-- **The inertia transversality form** `𝔍 = w² − σ² − σd + κ` (`d = D/M`, `σ = R/L`, `w = ω₀`,
`κ = Q/M`). -/
def inertForm (d σ w κ : ℝ) : ℝ := w ^ 2 - σ ^ 2 - σ * d + κ

@[tmio M, simp, powerlib_domain] theorem inertShift_zero (g : VSM) : g.inertShift 0 = g := by
  cases g; simp [inertShift]

/-- The inertia enters only the rate row: `F_μ(x) = F(x) + μ (P_ref − P_e − D x₁) e₁`. -/
@[tmio M, powerlib_domain] theorem inertShift_field (g : VSM) (μ : ℝ) (x : State 4) :
    (g.inertShift μ).field x = g.field x +
      (μ * (g.Pref - g.power (x 0) (x 2) (x 3) - g.D * x 1)) • EuclideanSpace.single 1 1 := by
  ext i
  fin_cases i <;> simp [field, inertShift]
  ring

@[tmio M, powerlib_domain] theorem Model.inertFamily_zero_param (m : Model) :
    (fun z => m.inertFamily z 0) = m.field := by
  funext z; simp [Model.inertFamily, Model.field]

@[tmio M, powerlib_domain] theorem Model.inertFamily_origin (m : Model) (hp : Meets m .physical)
    (hb : Meets m .balanced) (μ : ℝ) : m.inertFamily 0 μ = 0 := by
  have h := (m.field_point_eq_zero_iff hp.2.1.ne' hp.1.L.ne' hp.1.absSq_pos.ne').mpr hb
  have hb' : m.g.power m.δ (m.g.is m.δ).re (m.g.is m.δ).im = m.g.Pref := hb
  rw [Model.inertFamily, zero_add, inertShift_field, h]
  simp [Model.point, qss, hb']

@[tmio M, powerlib_domain] private theorem Model.contDiff_augField_inertFamily (m : Model)
    {k : WithTop ℕ∞} : ContDiff ℝ k (augField m.inertFamily) := by
  have hx : ContDiff ℝ k fun w : State (4 + 1) => xpart w + m.point :=
    xpart.contDiff.add contDiff_const
  have h1 := (PiLp.proj 2 (fun _ : Fin 4 => ℝ) 1).contDiff.comp
    ((VSM.contDiff_field (k := k) (⟨m.g.toNetwork, 1, m.g.D, m.g.Pref⟩ : VSM)).comp hx)
  have hc : ContDiff ℝ k fun w : State (4 + 1) => mpart w *
      (m.g.Pref - m.g.power ((xpart w + m.point) 0) ((xpart w + m.point) 2)
        ((xpart w + m.point) 3) - m.g.D * (xpart w + m.point) 1) := by
    refine mpart.contDiff.mul ?_
    convert h1 using 1
    funext w
    simp [Function.comp_def]
  have h : ContDiff ℝ k (fun w : State (4 + 1) => m.inertFamily (xpart w) (mpart w)) := by
    simp only [Model.inertFamily, inertShift_field]
    exact (m.g.contDiff_field.comp hx).add (hc.smul contDiff_const)
  exact xin.contDiff.comp h

@[tmio M, powerlib_domain] theorem inertShift_jacobian (g : VSM) (μ δ id iq : ℝ) :
    (g.inertShift μ).jacobian δ id iq = g.jacobian δ id iq + μ • g.inertJac δ id iq := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jacobian, inertShift, inertJac] <;> ring

@[tmio M, powerlib_domain] theorem Model.fderiv_inertFamily (m : Model) (μ : ℝ) :
    fderiv ℝ (fun z => m.inertFamily z μ) 0 =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.jac +
        μ • Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.inertJac := by
  rw [show (fun z => m.inertFamily z μ) = fun z => (m.g.inertShift μ).field (z + m.point) from
    rfl, fderiv_comp_add_right, zero_add, fderiv_field, inertShift_jacobian]
  simp [Model.point, qss, Model.jac, Model.inertJac, map_add, map_smul]

/-- **Transversality data along the inverse inertia**: `μ ↦ D_z F(0, μ)` is affine with slope
`toEuclideanCLM m.inertJac`. -/
@[tmio M, powerlib_domain] theorem Model.hasDerivAt_fderiv_inertFamily (m : Model) :
    HasDerivAt (fun μ => fderiv ℝ (fun z => m.inertFamily z μ) 0)
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.inertJac) 0 := by
  simp only [Model.fderiv_inertFamily]
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.inertJac)).const_add
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.jac)

/-- `τ` of a parameter derivative with a single nonzero row `r` (row `1`):
`τ = 2 Re(p̄₁ Σ rⱼ qⱼ)`. -/
@[tmio M, powerlib_domain] private theorem paramTrace_row_apply (r₀ r₁ r₂ r₃ : ℝ)
    (p q : Fin 4 → ℂ) :
    Dynamics.PlanarHopf.paramTrace ((critπ p).comp
        ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
          !![0, 0, 0, 0; r₀, r₁, r₂, r₃; 0, 0, 0, 0; 0, 0, 0, 0]).comp (critι q))) =
      2 * ((p 1).re * (r₀ * (q 0).re + r₁ * (q 1).re + r₂ * (q 2).re + r₃ * (q 3).re) +
        (p 1).im * (r₀ * (q 0).im + r₁ * (q 1).im + r₂ * (q 2).im + r₃ * (q 3).im)) := by
  have hB : ∀ v : State 4, Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
      !![0, 0, 0, 0; r₀, r₁, r₂, r₃; 0, 0, 0, 0; 0, 0, 0, 0] v =
      (r₀ * v 0 + r₁ * v 1 + r₂ * v 2 + r₃ * v 3) • EuclideanSpace.single 1 1 := by
    intro v
    ext i
    fin_cases i <;> simp [Dynamics.toEuclideanCLM_apply, Fin.sum_univ_four]
  simp only [Dynamics.PlanarHopf.paramTrace, Dynamics.PlanarHopf.m00, Dynamics.PlanarHopf.m11,
    ContinuousLinearMap.comp_apply, critι_apply, critπ_apply0, critπ_apply1, e0_apply0,
    e0_apply1, e1_apply0, e1_apply1, one_smul, zero_smul, add_zero, zero_add, hB]
  simp only [inner_smul_right, EuclideanSpace.inner_single_right, PiLp.add_apply, PiLp.sub_apply,
    reV_apply, imV_apply, conj_trivial, one_mul]
  ring

/-- The real part of the rate component of the critical left vector:
`Re p₁ = −N_M/(2aw|r(iω)|²)` (`a, w, ω ≠ 0`; the rotation does not enter). -/
@[tmio M, powerlib_domain] private theorem angleZeroP_one_re {a d κ σ w ω : ℝ} (θ : ℝ)
    (ha : a ≠ 0) (hw : w ≠ 0) (hω : ω ≠ 0) (hR : angleZeroR1 d σ w κ ω ≠ 0) :
    (rotC θ (angleZeroP a d κ σ w ω) 1).re =
      -(inertNum d σ w κ ω / (2 * a * w * angleZeroR1 d σ w κ ω)) := by
  have hpair : (angleZeroPairing a d κ σ w ω).re = 2 * a * ω * w * (ω * (2 * σ + d)) ∧
      (angleZeroPairing a d κ σ w ω).im =
        -(2 * a * ω * w * (σ ^ 2 + w ^ 2 - 2 * ω ^ 2 + 2 * σ * d - κ)) := by
    have e : angleZeroPairing a d κ σ w ω = ((2 * a * ω * w * (ω * (2 * σ + d)) : ℝ) : ℂ) +
        ((-(2 * a * ω * w * (σ ^ 2 + w ^ 2 - 2 * ω ^ 2 + 2 * σ * d - κ)) : ℝ) : ℂ) * I := by
      unfold angleZeroPairing; push_cast; ring
    rw [e]
    constructor <;> simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;> ring
  have hN : (angleZeroPairing a d κ σ w ω).re ^ 2 + (angleZeroPairing a d κ σ w ω).im ^ 2 =
      4 * a ^ 2 * ω ^ 2 * w ^ 2 * angleZeroR1 d σ w κ ω := by
    rw [hpair.1, hpair.2]; unfold angleZeroR1; ring
  simp only [rotC, angleZeroP, angleZeroLeft, Matrix.cons_val_one, Matrix.cons_val_zero,
    Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.inv_re, Complex.inv_im,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  rw [show ∀ x : ℝ, x * x = x ^ 2 from fun x => (sq x).symm,
    show ∀ x : ℝ, -x * -x = x ^ 2 from fun x => by ring]
  rw [hN]
  simp only [Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, sq, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, hpair.1, hpair.2]
  unfold inertNum
  field_simp
  ring

/-- **The inverse-inertia transversality coefficient at the critical pair of every angle**: for
every physical model and every `ω > 0`, at (`Model.critQ ω`, `Model.critP ω`),
`τ_M = M ω² N_M(D/M, R/L, ω₀, Q/M, ω)/|r(iω)|²` (`inertNum`, `angleZeroR1`): the row of
`∂J/∂μ` applied to the critical vector is `−E ω₀ ω²` exactly. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.paramTrace_inertJac {m : Model} {ω : ℝ}
    (hp : Meets m .physical) (hω : 0 < ω) :
    Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.inertJac).comp
          (critι (m.critQ ω)))) =
      m.g.M * ω ^ 2 * inertNum (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ω /
        angleZeroR1 (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ω := by
  obtain ⟨hN, hM, hD⟩ := hp
  have hE := hN.E
  have hR : 0 ≤ m.g.R := hN.R
  have hL := hN.L
  have hw := hN.ω0
  have hR1 : 0 < angleZeroR1 (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ω := by
    unfold angleZeroR1; positivity
  unfold Model.inertJac VSM.inertJac
  rw [paramTrace_row_apply]
  have hcs := Real.sin_sq_add_cos_sq m.δ
  have hQ : m.g.reactive m.δ (m.g.is m.δ).re (m.g.is m.δ).im = m.Q := rfl
  have hre : m.g.reactive m.δ (m.g.is m.δ).re (m.g.is m.δ).im * (m.critQ ω 0).re +
      -m.g.D * (m.critQ ω 1).re + -(m.g.E * Real.cos m.δ) * (m.critQ ω 2).re +
      -(m.g.E * Real.sin m.δ) * (m.critQ ω 3).re = -(m.g.E * m.g.ω0 * ω ^ 2) := by
    simp only [Model.critQ, rotC, angleZeroQ, Matrix.cons_val, Complex.add_re, Complex.sub_re,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.add_im, Complex.sub_im, sq, hQ]
    linear_combination (-(m.g.E * m.g.ω0 * (m.Q / m.g.M + ω * ω))) * hcs
  have him : m.g.reactive m.δ (m.g.is m.δ).re (m.g.is m.δ).im * (m.critQ ω 0).im +
      -m.g.D * (m.critQ ω 1).im + -(m.g.E * Real.cos m.δ) * (m.critQ ω 2).im +
      -(m.g.E * Real.sin m.δ) * (m.critQ ω 3).im = 0 := by
    simp only [Model.critQ, rotC, angleZeroQ, Matrix.cons_val, Complex.add_re, Complex.sub_re,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.add_im, Complex.sub_im, sq, hQ]
    linear_combination (m.g.E * ω * m.g.ω0 * (m.g.D / m.g.M)) * hcs
  rw [hre, him]
  have hpre : (m.critP ω 1).re = -(inertNum (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ω /
      (2 * (m.g.E / m.g.M) * m.g.ω0 *
        angleZeroR1 (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ω)) :=
    angleZeroP_one_re m.δ (by positivity) hw.ne' hω.ne' hR1.ne'
  rw [hpre]
  have hE0 := hE.ne'
  have hM0 := hM.ne'
  have hw0 := hw.ne'
  have hR10 := hR1.ne'
  field_simp
  ring

/-- **The inverse-inertia transversality coefficient at every Hopf boundary point**: at the
critical frequency (`ω² = a₁/a₃`) and pair of a physical boundary model,
`N_M = 2d(ω₀² − σ² − ω²) = 4dσ 𝔍/a₃` and
`τ_M = 4 D σ a₁ 𝔍(D/M, R/L, ω₀, Q/M)/(a₁a₃³ + (a₂a₃ − 2a₁)²)` (`inertForm`). Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem Model.paramTrace_inert_crit {m : Model} {ω : ℝ}
    (hp : Meets m .physical)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q) (hω : 0 < ω)
    (hω2 : ω ^ 2 = m.g.coeff1 m.Q / m.g.coeff3) :
    Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.inertJac).comp
          (critι (m.critQ ω)))) =
      4 * m.g.D * (m.g.R / m.g.L) * m.g.coeff1 m.Q *
          inertForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) /
        (m.g.coeff1 m.Q * m.g.coeff3 ^ 3 +
          (m.g.coeff2 m.Q * m.g.coeff3 - 2 * m.g.coeff1 m.Q) ^ 2) := by
  have hf := freq_atoms hp hω2
  have h3 := model_coeff3_pos' hp
  have h1 := (Model.freq_relations_of_boundary hp hH hω2).1
  rw [Model.paramTrace_inertJac hp hω]
  obtain ⟨hN, hM, hD⟩ := hp
  have hR : 0 ≤ m.g.R := hN.R
  have hL := hN.L
  obtain ⟨e3, e2, e1, -⟩ := m.coeff_atoms hL.ne'
  have hR1 : 0 < angleZeroR1 (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ω := by
    unfold angleZeroR1; positivity
  have hDM : m.g.D = m.g.D / m.g.M * m.g.M := by field_simp
  rw [e3, e2, e1]
  rw [e3] at h3
  set d := m.g.D / m.g.M
  set σ := m.g.R / m.g.L
  set w := m.g.ω0
  set κ := m.Q / m.g.M
  have k2 : (2 * σ + d) ^ 2 * angleZeroR1 d σ w κ ω =
      (d * (σ ^ 2 + w ^ 2) - 2 * σ * κ) * (2 * σ + d) ^ 3 +
        ((σ ^ 2 + w ^ 2 + 2 * σ * d - κ) * (2 * σ + d) - 2 * (d * (σ ^ 2 + w ^ 2) -
          2 * σ * κ)) ^ 2 := by
    unfold angleZeroR1
    linear_combination ((2 * σ + d) ^ 3 - 4 * (σ ^ 2 + w ^ 2 + 2 * σ * d - κ) * (2 * σ + d) +
      4 * ω ^ 2 * (2 * σ + d) + 4 * (d * (σ ^ 2 + w ^ 2) - 2 * σ * κ)) * hf
  have hden : 0 < (d * (σ ^ 2 + w ^ 2) - 2 * σ * κ) * (2 * σ + d) ^ 3 +
      ((σ ^ 2 + w ^ 2 + 2 * σ * d - κ) * (2 * σ + d) - 2 * (d * (σ ^ 2 + w ^ 2) -
        2 * σ * κ)) ^ 2 := by
    rw [← k2]; exact mul_pos (by positivity) hR1
  have i1 : inertNum d σ w κ ω = 2 * d * (w ^ 2 - σ ^ 2 - ω ^ 2) := by
    unfold inertNum; linear_combination (-1 : ℝ) * h1
  have i2 : (2 * σ + d) * (w ^ 2 - σ ^ 2 - ω ^ 2) = 2 * σ * inertForm d σ w κ := by
    unfold inertForm; linear_combination (-1 : ℝ) * hf
  rw [div_eq_div_iff hR1.ne' hden.ne', i1]
  linear_combination (-(2 * m.g.M * d * ω ^ 2 * (w ^ 2 - σ ^ 2 - ω ^ 2))) * k2 +
    (2 * m.g.M * d * angleZeroR1 d σ w κ ω * (2 * σ + d) * (w ^ 2 - σ ^ 2 - ω ^ 2)) * hf +
    (2 * m.g.M * d * angleZeroR1 d σ w κ ω * (d * (σ ^ 2 + w ^ 2) - 2 * σ * κ)) * i2 -
    (4 * σ * (d * (σ ^ 2 + w ^ 2) - 2 * σ * κ) * inertForm d σ w κ *
      angleZeroR1 d σ w κ ω) * hDM

/-- **The sign of the inverse-inertia transversality coefficient**: at every critical frequency
and pair of a physical boundary model, `sign τ_M = sign 𝔍(D/M, R/L, ω₀, Q/M)`,
`𝔍 = ω₀² − σ² − σd + κ` (`inertForm`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.sign_paramTrace_inert_crit {m : Model} {ω : ℝ}
    (hp : Meets m .physical)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q) (hω : 0 < ω)
    (hω2 : ω ^ 2 = m.g.coeff1 m.Q / m.g.coeff3) :
    SignType.sign (Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.inertJac).comp
          (critι (m.critQ ω))))) =
      SignType.sign (inertForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)) := by
  have hR := Model.R_pos_of_boundary hp hH
  have h3 := model_coeff3_pos' hp
  have hM := hp.2.1
  have hD := hp.2.2
  have hL := hp.1.L
  have h1 : 0 < m.g.coeff1 m.Q := by
    have h := pow_pos hω 2
    rw [hω2, lt_div_iff₀ h3, zero_mul] at h
    exact h
  have hden : 0 < m.g.coeff1 m.Q * m.g.coeff3 ^ 3 +
      (m.g.coeff2 m.Q * m.g.coeff3 - 2 * m.g.coeff1 m.Q) ^ 2 := by positivity
  rw [Model.paramTrace_inert_crit hp hH hω hω2,
    show ∀ x : ℝ, 4 * m.g.D * (m.g.R / m.g.L) * m.g.coeff1 m.Q * x /
        (m.g.coeff1 m.Q * m.g.coeff3 ^ 3 +
          (m.g.coeff2 m.Q * m.g.coeff3 - 2 * m.g.coeff1 m.Q) ^ 2) =
      (4 * m.g.D * (m.g.R / m.g.L) * m.g.coeff1 m.Q / (m.g.coeff1 m.Q * m.g.coeff3 ^ 3 +
        (m.g.coeff2 m.Q * m.g.coeff3 - 2 * m.g.coeff1 m.Q) ^ 2)) * x from fun x => by ring,
    sign_mul, sign_pos (div_pos (by positivity) hden), one_mul]

/-- **The two transversality forms never vanish together**:
`𝔗 = ω₀²(d + 2σ)³ + 𝔍 (2σκ − dκ − d²σ − 5dσ² − dω₀² − 2σ³ + 2σω₀²)`, so `𝔍 = 0` forces
`𝔗 = ω₀²(d + 2σ)³`. -/
@[tmio M, powerlib_domain] theorem transForm_eq_inertForm (d σ w κ : ℝ) :
    transForm d σ w κ = w ^ 2 * (d + 2 * σ) ^ 3 + inertForm d σ w κ *
      (2 * σ * κ - d * κ - d ^ 2 * σ - 5 * d * σ ^ 2 - d * w ^ 2 - 2 * σ ^ 3 + 2 * σ * w ^ 2) := by
  unfold transForm inertForm; ring

/-- **Damping and inertia are never both non-transversal**: at every critical frequency and
pair of a physical boundary model, `τ_D = 0` (`𝔗 = 0`) forces `𝔍 ≠ 0`, hence `τ_M ≠ 0`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.paramTrace_inert_ne_zero_of_paramTrace_eq_zero
    {m : Model} {ω : ℝ} (hp : Meets m .physical)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q) (hω : 0 < ω)
    (hω2 : ω ^ 2 = m.g.coeff1 m.Q / m.g.coeff3)
    (h0 : Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (dampJac m.g.M)).comp
          (critι (m.critQ ω)))) = 0) :
    Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
        ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.inertJac).comp
          (critι (m.critQ ω)))) ≠ 0 := by
  have hT : transForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) = 0 := by
    have e := Model.sign_paramTrace_crit hp hH hω hω2
    rw [h0, sign_zero] at e
    have e' : SignType.sign (transForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)) =
        -0 := by rw [e, neg_neg]
    exact sign_eq_zero_iff.mp e'
  intro hτ
  have e := Model.sign_paramTrace_inert_crit hp hH hω hω2
  rw [hτ, sign_zero, eq_comm, sign_eq_zero_iff] at e
  obtain ⟨hN, hM, hD⟩ := hp
  have hw := hN.ω0
  have hR : 0 ≤ m.g.R := hN.R
  have hL := hN.L
  rw [transForm_eq_inertForm, e, zero_mul, add_zero] at hT
  have : 0 < m.g.ω0 ^ 2 * (m.g.D / m.g.M + 2 * (m.g.R / m.g.L)) ^ 3 := by positivity
  linarith

/-! ## The Hopf cycles -/

/-- The Hopf data of a family through a boundary point (shared by the cycle and amplitude
laws): the critical pair, the factorized characteristic polynomial, `τ ≠ 0`, `ℓ₁ ≠ 0` and
`sign(μ τ ℓ₁) = −sign(μ s 𝔅_δ)`. -/
@[tmio TM, powerlib_domain] private theorem Model.hopfData_of_family (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hB : bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)
      m.angleShift ≠ 0)
    {F : State 4 → ℝ → State 4} {B : State 4 →L[ℝ] State 4}
    (hFm : (fun z => F z 0) = m.field) {s : ℝ} (hs0 : s ≠ 0)
    (hs : SignType.sign (Dynamics.PlanarHopf.paramTrace ((critπ (m.critP
        √(m.g.coeff1 m.Q / m.g.coeff3))).comp (B.comp (critι (m.critQ
          √(m.g.coeff1 m.Q / m.g.coeff3)))))) = SignType.sign s) :
    ∃ r : ℂ[X], IsCriticalPair (fun z => F z 0) 0 √(m.g.coeff1 m.Q / m.g.coeff3)
        (m.critQ √(m.g.coeff1 m.Q / m.g.coeff3)) (m.critP √(m.g.coeff1 m.Q / m.g.coeff3)) ∧
      (jacobianC (fun z => F z 0) 0).charpoly =
        (X ^ 2 + C ((√(m.g.coeff1 m.Q / m.g.coeff3) : ℂ) ^ 2)) * r ∧
      (∀ s : ℂ, r.eval s = 0 → s.re < 0) ∧
      Dynamics.PlanarHopf.paramTrace ((critπ (m.critP √(m.g.coeff1 m.Q / m.g.coeff3))).comp
        (B.comp (critι (m.critQ √(m.g.coeff1 m.Q / m.g.coeff3))))) ≠ 0 ∧
      firstLyapunov (fun z => F z 0) 0 √(m.g.coeff1 m.Q / m.g.coeff3)
        (m.critQ √(m.g.coeff1 m.Q / m.g.coeff3)) (m.critP √(m.g.coeff1 m.Q / m.g.coeff3)) ≠ 0 ∧
      ∀ μ : ℝ, SignType.sign (μ * Dynamics.PlanarHopf.paramTrace ((critπ (m.critP
          √(m.g.coeff1 m.Q / m.g.coeff3))).comp (B.comp (critι (m.critQ
            √(m.g.coeff1 m.Q / m.g.coeff3))))) *
        firstLyapunov (fun z => F z 0) 0 √(m.g.coeff1 m.Q / m.g.coeff3)
          (m.critQ √(m.g.coeff1 m.Q / m.g.coeff3)) (m.critP √(m.g.coeff1 m.Q / m.g.coeff3))) =
        -SignType.sign (μ * s * bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)
      m.angleShift) := by
  have h3 := model_coeff3_pos' hp
  set ω := √(m.g.coeff1 m.Q / m.g.coeff3) with hωdef
  have hω : 0 < ω := Real.sqrt_pos.mpr (div_pos h1 h3)
  have hω2 : ω ^ 2 = m.g.coeff1 m.Q / m.g.coeff3 := Real.sq_sqrt (div_pos h1 h3).le
  have hcp0 := Model.isCriticalPair_crit hp hb hH hω hω2
  have hcp : IsCriticalPair (fun z => F z 0) 0 ω (m.critQ ω) (m.critP ω) := by
    rw [hFm]; exact hcp0
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_boundary h3 h1 h0 hH hω2
  have hchar' : (jacobianC (fun z => F z 0) 0).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r := by
    rw [hFm]; exact hchar
  have hsℓ := Model.sign_firstLyapunov_crit hp hb hH h1 h0 hcp0
  set τ := Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
      (B.comp (critι (m.critQ ω)))) with hτdef
  set ℓ := firstLyapunov (fun z => F z 0) 0 ω (m.critQ ω) (m.critP ω) with hℓdef
  have hℓe : ℓ = firstLyapunov m.field 0 ω (m.critQ ω) (m.critP ω) := by
    rw [hℓdef, hFm]
  rw [← hℓe] at hsℓ
  have hτ0 : τ ≠ 0 := by
    intro h
    rw [h, sign_zero, eq_comm, sign_eq_zero_iff] at hs
    exact hs0 hs
  have hℓ0 : ℓ ≠ 0 := by
    intro h
    have e : SignType.sign (bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)
        m.angleShift) = -SignType.sign ℓ := by rw [hsℓ, neg_neg]
    rw [h, sign_zero] at e
    exact hB (sign_eq_zero_iff.mp e)
  refine ⟨r, hcp, hchar', hr, hτ0, hℓ0, fun μ => ?_⟩
  rw [sign_mul, sign_mul, hs, hsℓ, sign_mul, sign_mul]
  simp only [mul_neg]

/-- **Hopf cycles of a one-parameter family through a boundary point.** For a family `F` of the
model at a balanced physical boundary point (`a₁, a₀ > 0`) whose augmented field is smooth,
which keeps the origin fixed, equals the model field at `μ = 0`, and whose transversality
coefficient at (`critQ`, `critP`) has the sign of `s ≠ 0`, with `𝔅_δ ≠ 0`: for every small `μ`
with `μ s 𝔅_δ > 0` there is a nonconstant periodic orbit with
`c|μ|/8 ≤ ‖critπ p z(t)‖² ≤ 8c|μ|` (`HopfCycle.exists_hopfCycle`). Private evidence. -/
@[tmio TM, powerlib_domain] private theorem Model.exists_hopfCycle_of_family (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hB : bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)
      m.angleShift ≠ 0)
    {F : State 4 → ℝ → State 4} {B : State 4 →L[ℝ] State 4}
    (hF : ∀ k : WithTop ℕ∞, ContDiff ℝ k (augField F)) (hF0 : ∀ μ, F 0 μ = 0)
    (hFm : (fun z => F z 0) = m.field)
    (hFB : HasDerivAt (fun μ => fderiv ℝ (fun z => F z μ) 0) B 0) {s : ℝ} (hs0 : s ≠ 0)
    (hs : SignType.sign (Dynamics.PlanarHopf.paramTrace ((critπ (m.critP
        √(m.g.coeff1 m.Q / m.g.coeff3))).comp (B.comp (critι (m.critQ
          √(m.g.coeff1 m.Q / m.g.coeff3)))))) = SignType.sign s) :
    ∃ δ > 0, ∃ c > 0, ∀ μ, |μ| < δ →
      0 < μ * s * bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)
        m.angleShift →
      ∃ z : ℝ → State 4, ∃ T, 0 < T ∧ (∀ t, HasDerivAt z (F (z t) μ) t) ∧
        (∀ t, z (t + T) = z t) ∧ (∃ t, z t ≠ z 0) ∧
        ∀ t, c * |μ| / 8 ≤ ‖critπ (m.critP √(m.g.coeff1 m.Q / m.g.coeff3)) (z t)‖ ^ 2 ∧
          ‖critπ (m.critP √(m.g.coeff1 m.Q / m.g.coeff3)) (z t)‖ ^ 2 ≤ 8 * (c * |μ|) := by
  obtain ⟨r, hcp, hchar', hr, hτ0, hℓ0, hsgn⟩ := m.hopfData_of_family hp hb hH h1 h0 hB hFm hs0 hs
  have h3 := model_coeff3_pos' hp
  set ω := √(m.g.coeff1 m.Q / m.g.coeff3) with hωdef
  have hω : 0 < ω := Real.sqrt_pos.mpr (div_pos h1 h3)
  set τ := Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
      (B.comp (critι (m.critQ ω)))) with hτdef
  set ℓ := firstLyapunov (fun z => F z 0) 0 ω (m.critQ ω) (m.critP ω) with hℓdef
  obtain ⟨δ, hδ, hcyc⟩ := Dynamics.HopfCycle.exists_hopfCycle (hF 1) (hF ⊤).contDiffAt.analyticAt
    hF0 hcp hchar' hr hFB hτ0 hℓ0
  have hκ : 0 < |τ| / (ω * |ℓ|) := div_pos (abs_pos.mpr hτ0) (mul_pos hω (abs_pos.mpr hℓ0))
  refine ⟨δ, hδ, |τ| / (ω * |ℓ|), hκ, fun μ hμ hpos => ?_⟩
  have hs' : μ * τ * ℓ < 0 := by
    have e := hsgn μ
    rw [sign_pos hpos] at e
    exact sign_eq_neg_one_iff.mp e
  obtain ⟨z, T, hT0, -, hz, hzT, hznc, hamp⟩ := hcyc μ hμ hs'
  have hν := Dynamics.HopfCycle.hopfAmplitude_eq_abs hω hs'
  refine ⟨z, T, hT0, hz, hzT, hznc, fun t => ?_⟩
  have := hamp t
  rw [hν] at this
  constructor
  · linarith [this.1]
  · linarith [this.2]

/-- **Hopf cycles along the damping at every angle.** At a balanced physical model on the Hopf
boundary (`a₁, a₀ > 0`) with `𝔅_δ ≠ 0` (`ℓ₁ ≠ 0`, `Line.VSM.Model.sign_firstLyapunov_crit`) and
`𝔗 ≠ 0` (`τ ≠ 0`, `Line.VSM.Model.sign_paramTrace_crit`), so that `sign(τ ℓ₁) = sign(𝔗 𝔅_δ)`:
for every small `μ` with `μ 𝔗 𝔅_δ < 0` the translated model field with the damping `D + μ` has a
nonconstant periodic orbit around the operating point whose critical coordinates satisfy
`c|μ|/8 ≤ ‖critπ p z(t)‖² ≤ 8c|μ|`, `c = |τ|/(ω|ℓ₁|) > 0`, `ω = √(a₁/a₃)`
(`HopfCycle.exists_hopfCycle`). Private evidence: periodic orbits are not sentences of the
family. -/
@[tmio TM, powerlib_domain] private theorem Model.exists_hopfCycle_damping (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hB : bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)
      m.angleShift ≠ 0)
    (hT : transForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ≠ 0) :
    ∃ δ > 0, ∃ c > 0, ∀ μ, |μ| < δ →
      μ * transForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) *
          bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) m.angleShift < 0 →
      ∃ z : ℝ → State 4, ∃ T, 0 < T ∧ (∀ t, HasDerivAt z (m.dampFamily (z t) μ) t) ∧
        (∀ t, z (t + T) = z t) ∧ (∃ t, z t ≠ z 0) ∧
        ∀ t, c * |μ| / 8 ≤ ‖critπ (m.critP √(m.g.coeff1 m.Q / m.g.coeff3)) (z t)‖ ^ 2 ∧
          ‖critπ (m.critP √(m.g.coeff1 m.Q / m.g.coeff3)) (z t)‖ ^ 2 ≤ 8 * (c * |μ|) := by
  have h3 := model_coeff3_pos' hp
  have hs := Model.sign_paramTrace_crit hp hH (Real.sqrt_pos.mpr (div_pos h1 h3))
    (Real.sq_sqrt (div_pos h1 h3).le)
  rw [← Left.sign_neg] at hs
  obtain ⟨δ, hδ, c, hc, h⟩ := m.exists_hopfCycle_of_family hp hb hH h1 h0 hB
    (fun _ => m.contDiff_augField_dampFamily) (m.dampFamily_origin hp hb)
    m.dampFamily_zero_param m.hasDerivAt_fderiv_dampFamily (neg_ne_zero.mpr hT) hs
  refine ⟨δ, hδ, c, hc, fun μ hμ hneg => h μ hμ ?_⟩
  linarith [show μ * -transForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) *
      bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) m.angleShift =
    -(μ * transForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) *
      bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) m.angleShift) by ring]

/-- **Hopf cycles along the inverse inertia at every angle.** At a balanced physical boundary
point with `𝔅_δ ≠ 0` and `𝔍 ≠ 0` (`τ_M ≠ 0`, `Line.VSM.Model.sign_paramTrace_inert_crit`): for
every small `μ` with `μ 𝔍 𝔅_δ > 0` the model with the inverse inertia `1/M + μ` has a
nonconstant periodic orbit around the operating point with `c|μ|/8 ≤ ‖critπ p z(t)‖² ≤ 8c|μ|`.
Private evidence. -/
@[tmio TM, powerlib_domain] private theorem Model.exists_hopfCycle_inertia (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hB : bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)
      m.angleShift ≠ 0)
    (hJ : inertForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ≠ 0) :
    ∃ δ > 0, ∃ c > 0, ∀ μ, |μ| < δ →
      0 < μ * inertForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) *
          bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) m.angleShift →
      ∃ z : ℝ → State 4, ∃ T, 0 < T ∧ (∀ t, HasDerivAt z (m.inertFamily (z t) μ) t) ∧
        (∀ t, z (t + T) = z t) ∧ (∃ t, z t ≠ z 0) ∧
        ∀ t, c * |μ| / 8 ≤ ‖critπ (m.critP √(m.g.coeff1 m.Q / m.g.coeff3)) (z t)‖ ^ 2 ∧
          ‖critπ (m.critP √(m.g.coeff1 m.Q / m.g.coeff3)) (z t)‖ ^ 2 ≤ 8 * (c * |μ|) := by
  have h3 := model_coeff3_pos' hp
  exact m.exists_hopfCycle_of_family hp hb hH h1 h0 hB
    (fun _ => m.contDiff_augField_inertFamily) (m.inertFamily_origin hp hb)
    m.inertFamily_zero_param m.hasDerivAt_fderiv_inertFamily hJ
    (Model.sign_paramTrace_inert_crit hp hH (Real.sqrt_pos.mpr (div_pos h1 h3))
      (Real.sq_sqrt (div_pos h1 h3).le))

/-- **Hopf cycles at every boundary point with `𝔅_δ ≠ 0`.** At every balanced physical model on
the Hopf boundary (`a₁, a₀ > 0`, every angle) with `𝔅_δ ≠ 0`: either `𝔗 ≠ 0` and the damping
unfolds the cycles (`Model.exists_hopfCycle_damping`), or `𝔗 = 0`, then `𝔍 ≠ 0`
(`transForm_eq_inertForm`) and the inverse inertia unfolds them
(`Model.exists_hopfCycle_inertia`). Private evidence. -/
@[tmio TM, powerlib_domain] private theorem Model.exists_hopfCycle_of_bautinFormAngle_ne (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hB : bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)
      m.angleShift ≠ 0) :
    (transForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ≠ 0 ∧
      ∃ δ > 0, ∃ c > 0, ∀ μ, |μ| < δ →
        μ * transForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) *
          bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) m.angleShift < 0 →
        ∃ z : ℝ → State 4, ∃ T, 0 < T ∧ (∀ t, HasDerivAt z (m.dampFamily (z t) μ) t) ∧
          (∀ t, z (t + T) = z t) ∧ (∃ t, z t ≠ z 0) ∧
          ∀ t, c * |μ| / 8 ≤ ‖critπ (m.critP √(m.g.coeff1 m.Q / m.g.coeff3)) (z t)‖ ^ 2 ∧
            ‖critπ (m.critP √(m.g.coeff1 m.Q / m.g.coeff3)) (z t)‖ ^ 2 ≤ 8 * (c * |μ|)) ∨
    (inertForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ≠ 0 ∧
      ∃ δ > 0, ∃ c > 0, ∀ μ, |μ| < δ →
        0 < μ * inertForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) *
          bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) m.angleShift →
        ∃ z : ℝ → State 4, ∃ T, 0 < T ∧ (∀ t, HasDerivAt z (m.inertFamily (z t) μ) t) ∧
          (∀ t, z (t + T) = z t) ∧ (∃ t, z t ≠ z 0) ∧
          ∀ t, c * |μ| / 8 ≤ ‖critπ (m.critP √(m.g.coeff1 m.Q / m.g.coeff3)) (z t)‖ ^ 2 ∧
            ‖critπ (m.critP √(m.g.coeff1 m.Q / m.g.coeff3)) (z t)‖ ^ 2 ≤ 8 * (c * |μ|)) := by
  by_cases hT : transForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) = 0
  · right
    have hJ : inertForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ≠ 0 := by
      intro hJ
      obtain ⟨hN, hM, hD⟩ := hp
      have hw := hN.ω0
      have hR : 0 ≤ m.g.R := hN.R
      have hL := hN.L
      rw [transForm_eq_inertForm, hJ, zero_mul, add_zero] at hT
      have : 0 < m.g.ω0 ^ 2 * (m.g.D / m.g.M + 2 * (m.g.R / m.g.L)) ^ 3 := by positivity
      linarith
    exact ⟨hJ, m.exists_hopfCycle_inertia hp hb hH h1 h0 hB hJ⟩
  · exact Or.inl ⟨hT, m.exists_hopfCycle_damping hp hb hH h1 h0 hB hT⟩


/-- **Every small cycle of a family through a boundary point.** With the hypotheses of
`Model.exists_hopfCycle_of_family`: for every `η > 0` there are `δ, c > 0` such that every
nonconstant periodic orbit of `F(·, μ)`, `|μ| < δ`, in the ball of radius `δ` has `μ s 𝔅_δ > 0`
(none on the other side) and `(1 − η) c|μ| ≤ ‖critπ p z(t)‖² ≤ (1 + η) c|μ|`
(`HopfCycle.periodic_amplitude`). Private evidence. -/
@[tmio TM, powerlib_domain] private theorem Model.periodic_amplitude_of_family (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hB : bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)
      m.angleShift ≠ 0)
    {F : State 4 → ℝ → State 4} {B : State 4 →L[ℝ] State 4}
    (hF : ∀ k : WithTop ℕ∞, ContDiff ℝ k (augField F)) (hF0 : ∀ μ, F 0 μ = 0)
    (hFm : (fun z => F z 0) = m.field)
    (hFB : HasDerivAt (fun μ => fderiv ℝ (fun z => F z μ) 0) B 0) {s : ℝ} (hs0 : s ≠ 0)
    (hs : SignType.sign (Dynamics.PlanarHopf.paramTrace ((critπ (m.critP
        √(m.g.coeff1 m.Q / m.g.coeff3))).comp (B.comp (critι (m.critQ
          √(m.g.coeff1 m.Q / m.g.coeff3)))))) = SignType.sign s) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ c > 0, ∀ μ, |μ| < δ → ∀ (z : ℝ → State 4) (T : ℝ), 0 < T →
      (∀ t, HasDerivAt z (F (z t) μ) t) → (∀ t, z (t + T) = z t) → (∃ t, z t ≠ z 0) →
      (∀ t, ‖z t‖ < δ) →
      0 < μ * s * bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)
      m.angleShift ∧
        ∀ t, (1 - η) * (c * |μ|) ≤ ‖critπ (m.critP √(m.g.coeff1 m.Q / m.g.coeff3)) (z t)‖ ^ 2 ∧
          ‖critπ (m.critP √(m.g.coeff1 m.Q / m.g.coeff3)) (z t)‖ ^ 2 ≤ (1 + η) * (c * |μ|) := by
  obtain ⟨r, hcp, hchar', hr, hτ0, hℓ0, hsgn⟩ := m.hopfData_of_family hp hb hH h1 h0 hB hFm hs0 hs
  have h3 := model_coeff3_pos' hp
  set ω := √(m.g.coeff1 m.Q / m.g.coeff3) with hωdef
  have hω : 0 < ω := Real.sqrt_pos.mpr (div_pos h1 h3)
  obtain ⟨δ, hδ, hamp⟩ := Dynamics.HopfCycle.periodic_amplitude (hF 1)
    (hF ⊤).contDiffAt.analyticAt hF0 hcp hchar' hr hFB hτ0 hℓ0 hη
  set τ := Dynamics.PlanarHopf.paramTrace ((critπ (m.critP ω)).comp
      (B.comp (critι (m.critQ ω)))) with hτdef
  set ℓ := firstLyapunov (fun z => F z 0) 0 ω (m.critQ ω) (m.critP ω) with hℓdef
  refine ⟨δ, hδ, |τ| / (ω * |ℓ|), div_pos (abs_pos.mpr hτ0) (mul_pos hω (abs_pos.mpr hℓ0)),
    fun μ hμ z T hT hz hzT hnc hzδ => ?_⟩
  obtain ⟨hs', hbd⟩ := hamp μ hμ z T hT hz hzT hnc hzδ
  have e := hsgn μ
  rw [sign_neg hs'] at e
  refine ⟨sign_eq_one_iff.mp (neg_inj.mp e).symm, fun t => ?_⟩
  rw [Dynamics.HopfCycle.hopfAmplitude_eq_abs hω hs'] at hbd
  exact hbd t

/-- **Every small cycle along the damping.** With the hypotheses of
`Model.exists_hopfCycle_damping`: every small nonconstant cycle has `μ 𝔗 𝔅_δ < 0` and the
amplitude `(1 ± η) c|μ|`. Private evidence. -/
@[tmio TM, powerlib_domain] private theorem Model.periodic_amplitude_damping (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hB : bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)
      m.angleShift ≠ 0)
    (hT : transForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ≠ 0) {η : ℝ}
    (hη : 0 < η) :
    ∃ δ > 0, ∃ c > 0, ∀ μ, |μ| < δ → ∀ (z : ℝ → State 4) (T : ℝ), 0 < T →
      (∀ t, HasDerivAt z (m.dampFamily (z t) μ) t) → (∀ t, z (t + T) = z t) →
      (∃ t, z t ≠ z 0) → (∀ t, ‖z t‖ < δ) →
      μ * transForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) *
          bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)
      m.angleShift < 0 ∧
        ∀ t, (1 - η) * (c * |μ|) ≤ ‖critπ (m.critP √(m.g.coeff1 m.Q / m.g.coeff3)) (z t)‖ ^ 2 ∧
          ‖critπ (m.critP √(m.g.coeff1 m.Q / m.g.coeff3)) (z t)‖ ^ 2 ≤ (1 + η) * (c * |μ|) := by
  have h3 := model_coeff3_pos' hp
  have hs := Model.sign_paramTrace_crit hp hH (Real.sqrt_pos.mpr (div_pos h1 h3))
    (Real.sq_sqrt (div_pos h1 h3).le)
  rw [← Left.sign_neg] at hs
  obtain ⟨δ, hδ, c, hc, h⟩ := m.periodic_amplitude_of_family hp hb hH h1 h0 hB
    (fun _ => m.contDiff_augField_dampFamily) (m.dampFamily_origin hp hb)
    m.dampFamily_zero_param m.hasDerivAt_fderiv_dampFamily (neg_ne_zero.mpr hT) hs hη
  refine ⟨δ, hδ, c, hc, fun μ hμ z T hT0 hz hzT hnc hzδ => ?_⟩
  obtain ⟨hpos, hbd⟩ := h μ hμ z T hT0 hz hzT hnc hzδ
  refine ⟨?_, hbd⟩
  linarith [show μ * -transForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) *
      bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) m.angleShift =
    -(μ * transForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) *
      bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) m.angleShift) by ring]

/-- **Every small cycle along the inverse inertia.** With the hypotheses of
`Model.exists_hopfCycle_inertia`: every small nonconstant cycle has `μ 𝔍 𝔅_δ > 0` and the
amplitude `(1 ± η) c|μ|`. Private evidence. -/
@[tmio TM, powerlib_domain] private theorem Model.periodic_amplitude_inertia (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hB : bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)
      m.angleShift ≠ 0)
    (hJ : inertForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) ≠ 0) {η : ℝ}
    (hη : 0 < η) :
    ∃ δ > 0, ∃ c > 0, ∀ μ, |μ| < δ → ∀ (z : ℝ → State 4) (T : ℝ), 0 < T →
      (∀ t, HasDerivAt z (m.inertFamily (z t) μ) t) → (∀ t, z (t + T) = z t) →
      (∃ t, z t ≠ z 0) → (∀ t, ‖z t‖ < δ) →
      0 < μ * inertForm (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M) *
          bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)
      m.angleShift ∧
        ∀ t, (1 - η) * (c * |μ|) ≤ ‖critπ (m.critP √(m.g.coeff1 m.Q / m.g.coeff3)) (z t)‖ ^ 2 ∧
          ‖critπ (m.critP √(m.g.coeff1 m.Q / m.g.coeff3)) (z t)‖ ^ 2 ≤ (1 + η) * (c * |μ|) := by
  have h3 := model_coeff3_pos' hp
  exact m.periodic_amplitude_of_family hp hb hH h1 h0 hB
    (fun _ => m.contDiff_augField_inertFamily) (m.inertFamily_origin hp hb)
    m.inertFamily_zero_param m.hasDerivAt_fderiv_inertFamily hJ
    (Model.sign_paramTrace_inert_crit hp hH (Real.sqrt_pos.mpr (div_pos h1 h3))
      (Real.sq_sqrt (div_pos h1 h3).le)) hη

end VSM
end powerlib.GFM.Line
