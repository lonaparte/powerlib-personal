import theorem.GridTiedConverter.GFM.QVDroopHopf
import theorem.GridTiedConverter.GFM.VSMLPFHopfCycle
import theorem.Dynamics.HopfCycleAmplitude

/-! # Grid-forming converter with Q–V droop: Hopf cycles along the damping

Domain module.

Model boundary.
* The model of `theorem/GridTiedConverter/GFM/QVDroop.lean`, unchanged (state `(δ, Δω, Q_f)`,
  quasi-static line, export-positive powers, `E = E₀ − n_q (Q_f − Q_ref)`; excluded as there),
  read about a selected point on the Hopf surface of
  `theorem/GridTiedConverter/GFM/QVDroopHopf.lean` (an equilibrium with `A > 0`, `C > 0`,
  `G = 0`; `M, D, ω_q > 0`, `E* ≠ 0`), and unfolded in the damping: the parameter `μ` replaces
  `D` by `D + μ` (`QVDroop.dampShift`). The equilibrium conditions `Δω = 0`, `P = P_ref`,
  `Q = Q_f` do not contain `D`, so the translated family `QVDroop.Model.dampFamily` keeps the
  origin as an equilibrium for every `μ`.
* Level: the transversality coefficient `τ` of the critical pair of `QVDroopHopf` along the
  damping, in closed form on the whole Hopf surface, with its sign; and the cycles of the generic
  Hopf theorem `Dynamics.HopfCycle.exists_hopfCycle` for this family wherever `ℓ₁ ≠ 0` and
  `τ ≠ 0`. Periodic orbits are not sentences of `QVDroop.family`, so the cycles are private
  evidence; no new family, no connection conclusion. Every small cycle
  (`Dynamics.HopfCycle.periodic_amplitude`): no small cycle on the other side; amplitude
  `(1 ± η) ν`. Not proved: uniqueness and orbital stability of the cycles; cycles at the Bautin
  set (`hopfNum = 0`) or where `τ = 0`.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.4–3.5 (Theorem 3.3,
the transversality coefficient `Re λ'(0) = Re ⟨p, A'(0) q⟩`); the critical pair and `ℓ₁` of
`theorem/GridTiedConverter/GFM/QVDroopHopf.lean`; the parameter derivative `VSMLPF.dampJac` of
`theorem/GridTiedConverter/GFM/VSMLPFHopfCycle.lean` (the damping enters both Jacobians only
through the entry `−D/M`). The transversality coefficient was derived with SymPy (exact
rational-function arithmetic, cross-checked against `2 Re λ'(D)` from the characteristic
polynomial; untrusted) and is checked here by the kernel (`field_simp`, `ring`).

Results.
* `QVDroop.dampShift`, `QVDroop.Model.dampFamily`; `dampShift_field` (the field with the damping
  `D + μ` is `F(x) + μ (∂J/∂D) x`, `∂J/∂D = VSMLPF.dampJac M = −(1/M) e₁e₁ᵀ`),
  `dampShift_jacobian`, `Model.dampFamily_zero_param` (at `μ = 0` the family is the model
  field), `Model.dampFamily_origin`, `Model.fderiv_dampFamily`,
  `Model.hasDerivAt_fderiv_dampFamily` (the Jacobian is affine in `μ` with slope `∂J/∂D`).
* `paramTrace_dampJac` (every datum of the Hopf surface): at the critical pair
  `(hopfQ, hopfP)`, `τ = −(M ω² + ω_q k L)/(L² + M² ω²)`, `L = D + M ω_q k`.
* On the model (`Model.hopfQAt`, `Model.hopfPAt`: the critical pair at the data of the point):
  `Model.paramTrace_damping`, `τ = −T/(A² + M² ω²)` with the transversality numerator
  `T = P_δ + 2 D ω_q K + M ω_q² K²` (`Model.dampTransNum`); the sign law
  `Model.sign_paramTrace_damping` (`sign τ = −sign T`, so `τ = 0` exactly on `T = 0`);
  `Model.dampTransNum_pos_of_gain_nonneg` (`K ≥ 0 ⇒ T > 0`: `τ` can vanish only where `K < 0`)
  and `Model.dampTransNum_pos_of_physical` (physical range, `E* > 0`: `K = √disc > 0`, so
  `τ < 0`; more damping moves the critical eigenvalues to the left).
* The sign is not universal: the witness `hopfTransPos` (physical parameter range, `E* = −5`,
  `K = −3`, `T = −1/7`: `hopfTransPos_dampTransNum`) has `τ > 0`
  (`hopfTransPos_paramTrace_pos`), so the hypothesis `E* > 0` cannot be dropped
  (`not_forall_paramTrace_damping_neg`).
* Private evidence `Model.hopfData_damping` (the shared Hopf data) and
  `Model.periodic_amplitude_damping` (every small cycle has `κμ > 0`, amplitude `(1 ± η) κμ`).
* Private evidence `Model.exists_hopfCycle_damping`: for `hopfNum ≠ 0` and `T ≠ 0` there are
  `δ > 0` and `κ` with `sign κ = sign (T · hopfNum)` such that for every `μ` with `|μ| < δ` and
  `κ μ > 0` the model with the damping `D + μ` has a nonconstant periodic orbit around the
  operating point, of period at most `4π/ω`, with `κμ/8 ≤ ‖critπ p z(t)‖² ≤ 8κμ`. On the
  physical branch (`T > 0`; private evidence `Model.exists_hopfCycle_damping_of_physical`:
  physical range, `E* > 0`, wherever `hopfNum ≠ 0`, `sign κ = sign hopfNum`) a supercritical
  point (`hopfNum < 0`) has its cycles for damping just below the Hopf value, a subcritical one
  (`hopfNum > 0`) just above it. With it the private evidence
  `Model.contDiff_augField_dampFamily` (the augmented field is smooth, hence analytic).
-/

noncomputable section
namespace powerlib.GFM.QVDroop
open Complex Matrix Polynomial
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two state3_ext toEuclideanCLM_apply3)
open powerlib.Dynamics.HopfCycle (augField xpart mpart xin)
open powerlib.NormalForm.LyapunovCoefficient
open powerlib.Dynamics.CenterManifold (critπ critι critι_apply critπ_apply0 critπ_apply1 reV_apply
  imV_apply)
open powerlib.Dynamics.Degenerate.PlanarFocus (e0 e1 e0_apply0 e0_apply1 e1_apply0 e1_apply1)

/-! ## The damping family -/

/-- The parameters with the damping shifted by `μ`: `D ↦ D + μ`. -/
def dampShift (q : QVDroop) (μ : ℝ) : QVDroop :=
  ⟨q.M, q.D + μ, q.ωq, q.nq, q.E0, q.Qref, q.Pref, q.V, q.R, q.X⟩

/-- The translated field of the model with the damping `D + μ`, as a family in `μ`
(`z = x − (δ*, 0, Q_f*)`; the equilibrium conditions do not contain the damping). -/
def Model.dampFamily (m : Model) (z : State 3) (μ : ℝ) : State 3 :=
  (m.q.dampShift μ).field (z + m.point)

@[tmio M, simp, powerlib_domain] theorem dampShift_zero (q : QVDroop) : q.dampShift 0 = q := by
  cases q; simp [dampShift]

/-- The damping enters the field only through `−D Δω/M`: the field with the damping `D + μ` is
`F(x) + μ (∂J/∂D) x`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem dampShift_field (q : QVDroop) (μ : ℝ) (x : State 3) :
    (q.dampShift μ).field x =
      q.field x + μ • Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac q.M) x := by
  have hP : (q.dampShift μ).P = q.P := rfl
  have hQ : (q.dampShift μ).Q = q.Q := rfl
  have hE : (q.dampShift μ).emf = q.emf := rfl
  apply state3_ext
  · simp [toEuclideanCLM_apply3, VSMLPF.dampJac]
  · rw [field_apply_one, hP, hE]
    simp [toEuclideanCLM_apply3, VSMLPF.dampJac, dampShift]
    ring
  · rw [field_apply_two, hQ, hE]
    simp [toEuclideanCLM_apply3, VSMLPF.dampJac, dampShift]

/-- The parameter derivative of the Jacobian: `∂J/∂D = −(1/M) e₁ e₁ᵀ` (`VSMLPF.dampJac`). -/
@[tmio M, powerlib_domain] theorem dampShift_jacobian (q : QVDroop) (μ δ E : ℝ) :
    (q.dampShift μ).jacobian δ E = q.jacobian δ E + μ • VSMLPF.dampJac q.M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jacobian, dampShift, VSMLPF.dampJac, Pδ, PE, Qδ, QE, zsq]
  ring

@[tmio M, powerlib_domain] theorem Model.dampFamily_zero_param (m : Model) :
    (fun z => m.dampFamily z 0) = m.field := by
  funext z; simp [Model.dampFamily, Model.field]

@[tmio M, powerlib_domain] theorem Model.dampFamily_origin (m : Model)
    (heq : m.q.field m.point = 0) (μ : ℝ) : m.dampFamily 0 μ = 0 := by
  have hB : Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M) m.point = 0 := by
    apply state3_ext <;> simp [toEuclideanCLM_apply3, VSMLPF.dampJac, Model.point]
  rw [Model.dampFamily, zero_add, dampShift_field, heq, hB, smul_zero, add_zero]

@[tmio M, powerlib_domain] private theorem Model.contDiff_augField_dampFamily (m : Model)
    {k : WithTop ℕ∞} : ContDiff ℝ k (augField m.dampFamily) := by
  have e : augField m.dampFamily = fun w => xin (m.q.field (xpart w + m.point) +
      mpart w • Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M)
        (xpart w + m.point)) := by
    funext w
    simp only [augField, Model.dampFamily, dampShift_field]
  rw [e]
  have hx : ContDiff ℝ k fun w : State (3 + 1) => xpart w + m.point :=
    xpart.contDiff.add contDiff_const
  exact xin.contDiff.comp ((m.q.contDiff_field.comp hx).add (mpart.contDiff.smul
    ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M)).contDiff.comp hx)))

@[tmio M, powerlib_domain] theorem Model.fderiv_dampFamily (m : Model) (μ : ℝ) :
    fderiv ℝ (fun z => m.dampFamily z μ) 0 =
      Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.jacobian +
        μ • Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M) := by
  have hE : (m.q.dampShift μ).emf = m.q.emf := rfl
  rw [show (fun z => m.dampFamily z μ) = fun z => (m.q.dampShift μ).field (z + m.point) from rfl,
    fderiv_comp_add_right, zero_add, QVDroop.fderiv_field, dampShift_jacobian, hE]
  simp [Model.point, Model.jacobian, map_add, map_smul]

/-- **Transversality data**: `μ ↦ D_z F(0, μ)` is affine with slope `toEuclideanCLM (∂J/∂D)`. -/
@[tmio M, powerlib_domain] theorem Model.hasDerivAt_fderiv_dampFamily (m : Model) :
    HasDerivAt (fun μ => fderiv ℝ (fun z => m.dampFamily z μ) 0)
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M)) 0 := by
  simp only [Model.fderiv_dampFamily]
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M))).const_add
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.jacobian)

/-! ## The transversality coefficient on the Hopf surface -/

/-- **The transversality coefficient along the damping, on the whole Hopf surface**: for the
critical pair `(hopfQ, hopfP)` of `QVDroopHopf` (`M ≠ 0`, `ω ≠ 0`),
`τ = tr (critπ p ∘ ∂J/∂D ∘ critι q) = −(M ω² + ω_q k L)/(L² + M² ω²)`, `L = D + M ω_q k`
(`= 2 Re ⟨p, (∂J/∂D) q⟩ = 2 Re λ'(D)`). -/
@[tmio M, powerlib_domain] theorem paramTrace_dampJac {M D ω w k c : ℝ} (hM : M ≠ 0)
    (hw : w ≠ 0) :
    Dynamics.PlanarHopf.paramTrace ((critπ (hopfP M D ω w k c)).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac M)).comp
          (critι (hopfQ ω w k c)))) =
      -(M * w ^ 2 + ω * k * hopfL M D ω k) / hopfQ1 M D ω w k := by
  have hw2 : 0 < w ^ 2 := sq_pos_of_ne_zero hw
  have hQ1 : 0 < hopfQ1 M D ω w k := by
    have := mul_pos (sq_pos_of_ne_zero hM) hw2
    unfold hopfQ1
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) this
  have hn : Complex.normSq (hopfN0 M D ω w k) =
      4 * w ^ 2 * (w ^ 2 + ω ^ 2 * k ^ 2) * hopfQ1 M D ω w k := by
    simp [Complex.normSq_apply, hopfN0, hopfQ1, hopfL, -Complex.ofReal_mul, -Complex.ofReal_pow,
      -Complex.ofReal_add, -Complex.ofReal_neg, -Complex.ofReal_sub]
    ring
  have hN0 : starRingEnd ℂ (hopfN0 M D ω w k) ≠ 0 := by
    rw [_root_.map_ne_zero]
    intro h0
    have h1 : Complex.normSq (hopfN0 M D ω w k) = 0 := by rw [h0, map_zero]
    have h2 : 0 < 4 * w ^ 2 * (w ^ 2 + ω ^ 2 * k ^ 2) * hopfQ1 M D ω w k :=
      mul_pos (mul_pos (mul_pos four_pos hw2) (add_pos_of_pos_of_nonneg hw2 (by positivity))) hQ1
    linarith [hn ▸ h1]
  have hp : hopfP M D ω w k c 1 =
      ((-(M ^ 2) / (2 * hopfQ1 M D ω w k) : ℝ) : ℂ) +
        ((M * hopfL M D ω k / (2 * w * hopfQ1 M D ω w k) : ℝ) : ℂ) * I := by
    simp only [hopfP]
    rw [div_eq_iff hN0]
    apply Complex.ext <;>
      simp [hopfY, hopfN0, hopfQ1, hopfL, -Complex.ofReal_mul, -Complex.ofReal_div,
        -Complex.ofReal_pow, -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add] <;>
      field_simp <;> ring
  have hpr : (hopfP M D ω w k c 1).re = -(M ^ 2) / (2 * hopfQ1 M D ω w k) := by
    rw [hp]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hpi : (hopfP M D ω w k c 1).im = M * hopfL M D ω k / (2 * w * hopfQ1 M D ω w k) := by
    rw [hp]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hq1 : (hopfQ ω w k c 1).re = -w ^ 2 ∧ (hopfQ ω w k c 1).im = w * ω * k := by
    simp only [hopfQ, Matrix.cons_val_one, Matrix.cons_val_zero]
    constructor <;> simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  have hB : ∀ v : State 3, Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac M) v =
      mk3 0 (-(v 1 / M)) 0 := by
    intro v
    apply state3_ext <;> simp [toEuclideanCLM_apply3, VSMLPF.dampJac]
    ring
  simp only [Dynamics.PlanarHopf.paramTrace, Dynamics.PlanarHopf.m00, Dynamics.PlanarHopf.m11,
    ContinuousLinearMap.comp_apply, critι_apply, critπ_apply0, critπ_apply1, e0_apply0,
    e0_apply1, e1_apply0, e1_apply1, one_smul, zero_smul, add_zero, zero_add, hB]
  simp only [PiLp.inner_apply, Fin.sum_univ_three, mk3_zero, mk3_one, mk3_two, PiLp.add_apply,
    PiLp.sub_apply, reV_apply, imV_apply, hq1.1, hq1.2, hpr, hpi, RCLike.inner_apply,
    conj_trivial]
  field_simp
  ring

/-- The critical right eigenvector `hopfQ` at the data of the selected point
(`ω = hopfFreq`, `k = K`, `c = Q_δ`). -/
def Model.hopfQAt (m : Model) : Fin 3 → ℂ :=
  hopfQ m.q.ωq m.hopfFreq (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))

/-- The normalised left eigenvector `hopfP` at the data of the selected point. -/
def Model.hopfPAt (m : Model) : Fin 3 → ℂ :=
  hopfP m.q.M m.q.D m.q.ωq m.hopfFreq (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qδ m.δ (m.q.emf m.Qf))

/-- The transversality numerator `T = P_δ + 2 D ω_q K + M ω_q² K²` at the selected point. -/
def Model.dampTransNum (m : Model) : ℝ :=
  m.q.Pδ m.δ (m.q.emf m.Qf) + 2 * m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) +
    m.q.M * m.q.ωq ^ 2 * m.q.gain m.δ (m.q.emf m.Qf) ^ 2

/-- **The transversality coefficient of the model.** At a Hopf point (`A > 0`, `C > 0`, `G = 0`)
with `M, D, ω_q > 0`: `τ = −T/(A² + M² ω²)`, `T = P_δ + 2 D ω_q K + M ω_q² K²`,
`ω = hopfFreq`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.paramTrace_damping (m : Model) (hM : 0 < m.q.M)
    (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (h : m.IsHopf) :
    Dynamics.PlanarHopf.paramTrace ((critπ m.hopfPAt).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M)).comp
          (critι m.hopfQAt))) =
      -m.dampTransNum /
        (m.q.routhTrace m.δ (m.q.emf m.Qf) ^ 2 + m.q.M ^ 2 * m.hopfFreq ^ 2) := by
  obtain ⟨hw, ha, -, -⟩ := m.hopf_relations hM hD hω h
  rw [Model.hopfPAt, Model.hopfQAt, paramTrace_dampJac hM.ne' hw.ne', Model.dampTransNum, ha]
  simp only [hopfQ1, hopfL, hopfA, routhTrace]
  congr 1 <;> ring

/-- **The sign law of the transversality coefficient.** At a Hopf point with `M, D, ω_q > 0`,
`sign τ = −sign T`; in particular `τ = 0` exactly on `T = 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.sign_paramTrace_damping (m : Model) (hM : 0 < m.q.M)
    (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (h : m.IsHopf) :
    SignType.sign (Dynamics.PlanarHopf.paramTrace ((critπ m.hopfPAt).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M)).comp
          (critι m.hopfQAt)))) = -SignType.sign m.dampTransNum := by
  rw [m.paramTrace_damping hM hD hω h]
  have hA := h.2.1
  have hd : 0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ^ 2 + m.q.M ^ 2 * m.hopfFreq ^ 2 := by
    positivity
  rcases lt_trichotomy m.dampTransNum 0 with h0 | h0 | h0
  · rw [sign_neg h0, sign_pos (div_pos (neg_pos.mpr h0) hd)]
    rfl
  · rw [h0, neg_zero, zero_div, sign_zero, neg_zero]
  · rw [sign_pos h0, sign_neg (div_neg_of_neg_of_pos (neg_neg_of_pos h0) hd)]

/-- **`T > 0` for a nonnegative voltage-loop gain.** At a Hopf point with `M, D, ω_q > 0` and
`K ≥ 0`, `T = M ω² + ω_q K A > 0`, so `τ < 0`; `τ` can vanish only where `K < 0`. Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.dampTransNum_pos_of_gain_nonneg (m : Model)
    (hM : 0 < m.q.M) (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (h : m.IsHopf)
    (hK : 0 ≤ m.q.gain m.δ (m.q.emf m.Qf)) : 0 < m.dampTransNum := by
  obtain ⟨hw, ha, -, -⟩ := m.hopf_relations hM hD hω h
  have hA := h.2.1
  have e : m.dampTransNum = m.q.M * m.hopfFreq ^ 2 +
      m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) * m.q.routhTrace m.δ (m.q.emf m.Qf) := by
    rw [Model.dampTransNum, ha, hopfA, routhTrace]; ring
  rw [e]
  have h1 : 0 < m.q.M * m.hopfFreq ^ 2 := by positivity
  have h2 := mul_nonneg (mul_nonneg hω.le hK) hA.le
  linarith

/-- **The physical branch.** In the physical range (`M, D, ω_q, n_q, X > 0`,
`E₀ + n_q Q_ref > 0`) a Hopf point with a positive EMF has `K = √disc > 0`
(`QVDroop.one_add_nq_QE_Eplus`), hence `T > 0` and `τ < 0`: more damping moves the critical
eigenvalues to the left. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.dampTransNum_pos_of_physical (m : Model)
    (hM : 0 < m.q.M) (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq) (hX : 0 < m.q.X)
    (hc : 0 < m.q.E0 + m.q.nq * m.q.Qref) (h : m.IsHopf) (hE : 0 < m.q.emf m.Qf) :
    0 < m.dampTransNum := by
  refine m.dampTransNum_pos_of_gain_nonneg hM hD hω h ?_
  have h2 := m.q.a2_pos hnq hX
  have h0 := m.q.a0_neg hc
  have hEq : m.q.emf m.Qf = m.q.Eplus m.δ := by
    simpa [Model.point] using m.q.emf_eq_Eplus hM.ne' hω.ne' h2 h0 h.1 (by simpa [Model.point])
  rw [gain, hEq]
  exact (m.q.one_add_nq_QE_Eplus h2 h0 m.δ).2.le

/-! ## A Hopf point with `τ > 0` -/

/-- A Hopf point in the physical parameter range with a negative EMF:
`M = 2/21`, `D = ω_q = n_q = R = X = 1`, `V = 2`, `E₀ = 5/2`, `Q_ref = 0`, `P_ref = 35/2`, at
`δ* = −π/2`, `Q_f* = 15/2` (`E* = −5`, `K = −3`, `A = 5/7`, `C = 15`, `G = 0`, `T = −1/7`). -/
def hopfTransPos : Model :=
  ⟨⟨2 / 21, 1, 1, 1, 5 / 2, 0, 35 / 2, 2, 1, 1⟩, -(Real.pi / 2), 15 / 2⟩

@[tmio M, powerlib_domain] private theorem hopfTransPos_trig :
    Real.cos hopfTransPos.δ = 0 ∧ Real.sin hopfTransPos.δ = -1 := by
  rw [show hopfTransPos.δ = -(Real.pi / 2) from rfl, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  exact ⟨rfl, rfl⟩

@[tmio M, powerlib_domain] private theorem hopfTransPos_isHopf : hopfTransPos.IsHopf := by
  obtain ⟨hc, hs⟩ := hopfTransPos_trig
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply state3_ext <;>
      simp [Model.point, field, P_eq, Q_eq, emf, zsq, hc, hs] <;> norm_num [hopfTransPos]
  all_goals simp only [routhTrace, routhFold, routhHopf, gain, coupling, Pδ, PE, Qδ, QE, zsq,
    emf, hc, hs]
  all_goals norm_num [hopfTransPos]

/-- The witness has `T = −1/7`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem hopfTransPos_dampTransNum :
    hopfTransPos.dampTransNum = -1 / 7 := by
  obtain ⟨hc, hs⟩ := hopfTransPos_trig
  simp only [Model.dampTransNum, gain, Pδ, QE, zsq, emf, hc, hs]
  norm_num [hopfTransPos]

/-- **`τ > 0` occurs on the Hopf surface.** At the witness `hopfTransPos` (`E* = −5`, `K = −3`)
more damping moves the critical eigenvalues to the right. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem hopfTransPos_paramTrace_pos :
    0 < Dynamics.PlanarHopf.paramTrace ((critπ hopfTransPos.hopfPAt).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac hopfTransPos.q.M)).comp
          (critι hopfTransPos.hopfQAt))) := by
  have h := hopfTransPos.sign_paramTrace_damping (by norm_num [hopfTransPos])
    (by norm_num [hopfTransPos]) (by norm_num [hopfTransPos]) hopfTransPos_isHopf
  rw [hopfTransPos_dampTransNum, sign_neg (by norm_num : (-1 / 7 : ℝ) < 0)] at h
  exact sign_eq_one_iff.mp (h.trans rfl)

/-- **Refutation: `τ < 0` needs the physical branch.** In the physical parameter range
(`M, D, ω_q, n_q, X, V > 0`, `E₀ + n_q Q_ref > 0`) not every Hopf point has `τ < 0`: the
witness `hopfTransPos` has `E* = −5 < 0` and `τ > 0`; the hypothesis `E* > 0` of
`Model.dampTransNum_pos_of_physical` cannot be dropped. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem not_forall_paramTrace_damping_neg :
    ¬ ∀ m : Model, 0 < m.q.M → 0 < m.q.D → 0 < m.q.ωq → 0 < m.q.nq → 0 < m.q.X →
      0 < m.q.V → 0 < m.q.E0 + m.q.nq * m.q.Qref → m.IsHopf →
      Dynamics.PlanarHopf.paramTrace ((critπ m.hopfPAt).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M)).comp
          (critι m.hopfQAt))) < 0 := by
  intro h
  have := h hopfTransPos (by norm_num [hopfTransPos]) (by norm_num [hopfTransPos])
    (by norm_num [hopfTransPos]) (by norm_num [hopfTransPos]) (by norm_num [hopfTransPos])
    (by norm_num [hopfTransPos]) (by norm_num [hopfTransPos]) hopfTransPos_isHopf
  linarith [hopfTransPos_paramTrace_pos]

/-! ## The Hopf cycles -/

/-- The Hopf data of the damping family at a Hopf point (shared by the cycle and amplitude
laws): the critical pair, the factorized characteristic polynomial, `τ ≠ 0`, `ℓ₁ ≠ 0`, and
`sign(−τ/(ω ℓ₁)) = sign(T · hopfNum)`. -/
@[tmio TM, powerlib_domain] private theorem Model.hopfData_damping (m : Model)
    (hM : 0 < m.q.M) (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (hE : m.q.emf m.Qf ≠ 0)
    (h : m.IsHopf) (hN : m.hopfNumAt ≠ 0) (hT : m.dampTransNum ≠ 0) :
    IsCriticalPair (fun z => m.dampFamily z 0) 0 m.hopfFreq m.hopfQAt m.hopfPAt ∧
      (jacobianC (fun z => m.dampFamily z 0) 0).charpoly =
        (Polynomial.X ^ 2 + Polynomial.C ((m.hopfFreq : ℂ) ^ 2)) *
          (Polynomial.X +
            Polynomial.C (((m.q.routhTrace m.δ (m.q.emf m.Qf)) / m.q.M : ℝ) : ℂ)) ∧
      Dynamics.PlanarHopf.paramTrace ((critπ m.hopfPAt).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M)).comp
          (critι m.hopfQAt))) ≠ 0 ∧
      firstLyapunov (fun z => m.dampFamily z 0) 0 m.hopfFreq m.hopfQAt m.hopfPAt ≠ 0 ∧
      SignType.sign (-(Dynamics.PlanarHopf.paramTrace ((critπ m.hopfPAt).comp
        ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M)).comp
          (critι m.hopfQAt)))) / (m.hopfFreq *
        firstLyapunov (fun z => m.dampFamily z 0) 0 m.hopfFreq m.hopfQAt m.hopfPAt)) =
        SignType.sign (m.dampTransNum * m.hopfNumAt) := by
  obtain ⟨hcp0, -, hchar0⟩ := m.hopf_data hM hD hω hE h
  have hw : 0 < m.hopfFreq := (m.hopf_relations hM hD hω h).1
  have hz := m.dampFamily_zero_param
  have hcp : IsCriticalPair (fun z => m.dampFamily z 0) 0 m.hopfFreq m.hopfQAt m.hopfPAt := by
    rw [hz]; exact hcp0
  have hchar : (jacobianC (fun z => m.dampFamily z 0) 0).charpoly =
      (Polynomial.X ^ 2 + Polynomial.C ((m.hopfFreq : ℂ) ^ 2)) *
        (Polynomial.X +
          Polynomial.C (((m.q.routhTrace m.δ (m.q.emf m.Qf)) / m.q.M : ℝ) : ℂ)) := by
    rw [hz]; exact hchar0
  have hls : SignType.sign (firstLyapunov (fun z => m.dampFamily z 0) 0 m.hopfFreq m.hopfQAt
      m.hopfPAt) = SignType.sign m.hopfNumAt := by
    rw [hz]; exact m.sign_firstLyapunov_hopf hM hD hω hE h hcp0
  have hl : firstLyapunov (fun z => m.dampFamily z 0) 0 m.hopfFreq m.hopfQAt m.hopfPAt ≠ 0 := by
    intro h0
    rw [h0, sign_zero] at hls
    exact hN (sign_eq_zero_iff.mp hls.symm)
  have hτs := m.sign_paramTrace_damping hM hD hω h
  have hτ : Dynamics.PlanarHopf.paramTrace ((critπ m.hopfPAt).comp
      ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M)).comp
        (critι m.hopfQAt))) ≠ 0 := by
    rw [m.paramTrace_damping hM hD hω h]
    have hA := h.2.1
    have hd : 0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ^ 2 + m.q.M ^ 2 * m.hopfFreq ^ 2 := by
      positivity
    exact div_ne_zero (neg_ne_zero.mpr hT) hd.ne'
  set τ := Dynamics.PlanarHopf.paramTrace ((critπ m.hopfPAt).comp
      ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M)).comp
        (critι m.hopfQAt))) with hτdef
  set ℓ := firstLyapunov (fun z => m.dampFamily z 0) 0 m.hopfFreq m.hopfQAt m.hopfPAt
    with hℓdef
  have hc : 0 < m.hopfFreq * ℓ ^ 2 := mul_pos hw (sq_pos_of_ne_zero hl)
  have key : -τ / (m.hopfFreq * ℓ) * (m.hopfFreq * ℓ ^ 2) = -(τ * ℓ) := by
    field_simp
  refine ⟨hcp, hchar, hτ, hl, ?_⟩
  calc SignType.sign (-τ / (m.hopfFreq * ℓ))
      = SignType.sign (-τ / (m.hopfFreq * ℓ)) * SignType.sign (m.hopfFreq * ℓ ^ 2) := by
        rw [sign_pos hc, mul_one]
    _ = SignType.sign (-τ / (m.hopfFreq * ℓ) * (m.hopfFreq * ℓ ^ 2)) := (sign_mul _ _).symm
    _ = -(SignType.sign τ * SignType.sign ℓ) := by rw [key, Left.sign_neg, sign_mul]
    _ = SignType.sign m.dampTransNum * SignType.sign m.hopfNumAt := by
        rw [hτs, hls, neg_mul, neg_neg]
    _ = SignType.sign (m.dampTransNum * m.hopfNumAt) := (sign_mul _ _).symm

/-- **Hopf cycles along the damping.** At a Hopf point (`A > 0`, `C > 0`, `G = 0`) with
`M, D, ω_q > 0`, `E* ≠ 0`, `hopfNum ≠ 0` (`ℓ₁ ≠ 0`, `Model.sign_firstLyapunov_hopf`) and `T ≠ 0`
(`τ ≠ 0`, `Model.sign_paramTrace_damping`), there are `δ > 0` and `κ` with
`sign κ = sign (T · hopfNum)` such that for every `μ` with `|μ| < δ` and `κ μ > 0` the translated
model field with the damping `D + μ` has a nonconstant periodic orbit around the operating point,
of period at most `4π/ω`, whose critical coordinates satisfy `κμ/8 ≤ ‖critπ p z(t)‖² ≤ 8κμ`
(`HopfCycle.exists_hopfCycle`, `κ = −τ/(ω ℓ₁)`). Private evidence: periodic orbits are not
sentences of the family. -/
@[tmio TM, powerlib_domain] private theorem Model.exists_hopfCycle_damping (m : Model)
    (hM : 0 < m.q.M) (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (hE : m.q.emf m.Qf ≠ 0)
    (h : m.IsHopf) (hN : m.hopfNumAt ≠ 0) (hT : m.dampTransNum ≠ 0) :
    ∃ δ > 0, ∃ κ : ℝ, SignType.sign κ = SignType.sign (m.dampTransNum * m.hopfNumAt) ∧
      ∀ μ, |μ| < δ → 0 < κ * μ →
        ∃ z : ℝ → State 3, ∃ T, 0 < T ∧ T ≤ 4 * Real.pi / m.hopfFreq ∧
          (∀ t, HasDerivAt z (m.dampFamily (z t) μ) t) ∧ (∀ t, z (t + T) = z t) ∧
          (∃ t, z t ≠ z 0) ∧
          ∀ t, κ * μ / 8 ≤ ‖critπ m.hopfPAt (z t)‖ ^ 2 ∧
            ‖critπ m.hopfPAt (z t)‖ ^ 2 ≤ 8 * (κ * μ) := by
  obtain ⟨hcp, hchar, hτ, hl, hκs⟩ := m.hopfData_damping hM hD hω hE h hN hT
  have hw : 0 < m.hopfFreq := (m.hopf_relations hM hD hω h).1
  obtain ⟨δ, hδ, hcyc⟩ := Dynamics.HopfCycle.exists_hopfCycle m.contDiff_augField_dampFamily
    (m.contDiff_augField_dampFamily (k := ⊤)).contDiffAt.analyticAt (m.dampFamily_origin h.1)
    hcp hchar (re_neg_of_eval_X_add_C (div_pos h.2.1 hM)) m.hasDerivAt_fderiv_dampFamily hτ hl
  set τ := Dynamics.PlanarHopf.paramTrace ((critπ m.hopfPAt).comp
      ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M)).comp
        (critι m.hopfQAt))) with hτdef
  set ℓ := firstLyapunov (fun z => m.dampFamily z 0) 0 m.hopfFreq m.hopfQAt m.hopfPAt
    with hℓdef
  have hc : 0 < m.hopfFreq * ℓ ^ 2 := mul_pos hw (sq_pos_of_ne_zero hl)
  have key : -τ / (m.hopfFreq * ℓ) * (m.hopfFreq * ℓ ^ 2) = -(τ * ℓ) := by
    field_simp
  refine ⟨δ, hδ, -τ / (m.hopfFreq * ℓ), ?_, fun μ hμ hκμ => ?_⟩
  · exact hκs
  · have e : μ * τ * ℓ = -((-τ / (m.hopfFreq * ℓ) * μ) * (m.hopfFreq * ℓ ^ 2)) := by
      linear_combination μ * key
    have hs : μ * τ * ℓ < 0 := by
      rw [e]; exact neg_neg_of_pos (mul_pos hκμ hc)
    obtain ⟨z, T, hT0, hTle, hz', hzT, hznc, hamp⟩ := hcyc μ hμ hs
    refine ⟨z, T, hT0, hTle, hz', hzT, hznc, fun t => ?_⟩
    have hν : -(μ * τ) / (m.hopfFreq * ℓ) = -τ / (m.hopfFreq * ℓ) * μ := by ring
    have ht := hamp t
    rw [hν] at ht
    exact ht

/-- **Every small cycle along the damping.** With the hypotheses of
`Model.exists_hopfCycle_damping`, for every `η > 0` there are `δ > 0` and `κ` with
`sign κ = sign (T · hopfNum)` such that every nonconstant periodic orbit of the model with the
damping `D + μ`, `|μ| < δ`, in the ball of radius `δ` has `κ μ > 0` (no small cycle on the other
side) and `(1 − η) κμ ≤ ‖critπ p z(t)‖² ≤ (1 + η) κμ` (`HopfCycle.periodic_amplitude`). Private
evidence. -/
@[tmio TM, powerlib_domain] private theorem Model.periodic_amplitude_damping (m : Model)
    (hM : 0 < m.q.M) (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (hE : m.q.emf m.Qf ≠ 0)
    (h : m.IsHopf) (hN : m.hopfNumAt ≠ 0) (hT : m.dampTransNum ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ κ : ℝ, SignType.sign κ = SignType.sign (m.dampTransNum * m.hopfNumAt) ∧
      ∀ μ, |μ| < δ → ∀ (z : ℝ → State 3) (T : ℝ), 0 < T →
        (∀ t, HasDerivAt z (m.dampFamily (z t) μ) t) → (∀ t, z (t + T) = z t) →
        (∃ t, z t ≠ z 0) → (∀ t, ‖z t‖ < δ) →
        0 < κ * μ ∧ ∀ t, (1 - η) * (κ * μ) ≤ ‖critπ m.hopfPAt (z t)‖ ^ 2 ∧
          ‖critπ m.hopfPAt (z t)‖ ^ 2 ≤ (1 + η) * (κ * μ) := by
  obtain ⟨hcp, hchar, hτ, hl, hκs⟩ := m.hopfData_damping hM hD hω hE h hN hT
  have hw : 0 < m.hopfFreq := (m.hopf_relations hM hD hω h).1
  obtain ⟨δ, hδ, hamp⟩ := Dynamics.HopfCycle.periodic_amplitude m.contDiff_augField_dampFamily
    (m.contDiff_augField_dampFamily (k := ⊤)).contDiffAt.analyticAt (m.dampFamily_origin h.1)
    hcp hchar (re_neg_of_eval_X_add_C (div_pos h.2.1 hM)) m.hasDerivAt_fderiv_dampFamily hτ hl hη
  set τ := Dynamics.PlanarHopf.paramTrace ((critπ m.hopfPAt).comp
      ((Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (VSMLPF.dampJac m.q.M)).comp
        (critι m.hopfQAt))) with hτdef
  set ℓ := firstLyapunov (fun z => m.dampFamily z 0) 0 m.hopfFreq m.hopfQAt m.hopfPAt
    with hℓdef
  have hc : 0 < m.hopfFreq * ℓ ^ 2 := mul_pos hw (sq_pos_of_ne_zero hl)
  have key : -τ / (m.hopfFreq * ℓ) * (m.hopfFreq * ℓ ^ 2) = -(τ * ℓ) := by
    field_simp
  refine ⟨δ, hδ, -τ / (m.hopfFreq * ℓ), hκs, fun μ hμ z T hT0 hz hzT hnc hzδ => ?_⟩
  obtain ⟨hs, hbd⟩ := hamp μ hμ z T hT0 hz hzT hnc hzδ
  have e : μ * τ * ℓ = -((-τ / (m.hopfFreq * ℓ) * μ) * (m.hopfFreq * ℓ ^ 2)) := by
    linear_combination μ * key
  have hpos : 0 < -τ / (m.hopfFreq * ℓ) * μ := by
    rw [e] at hs
    exact pos_of_mul_pos_left (neg_neg_iff_pos.mp hs) hc.le
  have hν : -(μ * τ) / (m.hopfFreq * ℓ) = -τ / (m.hopfFreq * ℓ) * μ := by ring
  refine ⟨hpos, fun t => ?_⟩
  rw [hν] at hbd
  exact hbd t

/-- **Hopf cycles on the physical branch.** In the physical range (`M, D, ω_q, n_q, X > 0`,
`E₀ + n_q Q_ref > 0`) at a Hopf point with `E* > 0` and `hopfNum ≠ 0` (`T > 0` there,
`Model.dampTransNum_pos_of_physical`) the cycles of `Model.exists_hopfCycle_damping` exist with
`sign κ = sign hopfNum`: for damping just below the Hopf value at a supercritical point, just
above it at a subcritical one. Private evidence. -/
@[tmio TM, powerlib_domain] private theorem Model.exists_hopfCycle_damping_of_physical
    (m : Model) (hM : 0 < m.q.M) (hD : 0 < m.q.D) (hω : 0 < m.q.ωq) (hnq : 0 < m.q.nq)
    (hX : 0 < m.q.X) (hc : 0 < m.q.E0 + m.q.nq * m.q.Qref) (h : m.IsHopf)
    (hE : 0 < m.q.emf m.Qf) (hN : m.hopfNumAt ≠ 0) :
    ∃ δ > 0, ∃ κ : ℝ, SignType.sign κ = SignType.sign m.hopfNumAt ∧
      ∀ μ, |μ| < δ → 0 < κ * μ →
        ∃ z : ℝ → State 3, ∃ T, 0 < T ∧ T ≤ 4 * Real.pi / m.hopfFreq ∧
          (∀ t, HasDerivAt z (m.dampFamily (z t) μ) t) ∧ (∀ t, z (t + T) = z t) ∧
          (∃ t, z t ≠ z 0) ∧
          ∀ t, κ * μ / 8 ≤ ‖critπ m.hopfPAt (z t)‖ ^ 2 ∧
            ‖critπ m.hopfPAt (z t)‖ ^ 2 ≤ 8 * (κ * μ) := by
  have hT := m.dampTransNum_pos_of_physical hM hD hω hnq hX hc h hE
  obtain ⟨δ, hδ, κ, hs, hcyc⟩ := m.exists_hopfCycle_damping hM hD hω hE.ne' h hN hT.ne'
  refine ⟨δ, hδ, κ, ?_, hcyc⟩
  rw [hs, sign_mul, sign_pos hT, one_mul]

end QVDroop

end powerlib.GFM
