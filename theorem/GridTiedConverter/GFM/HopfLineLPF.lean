import theorem.GridTiedConverter.GFM.Line.VSMLPF
import theorem.Dynamics.HopfDichotomy

/-! # Hopf points of the VSM with a power filter on a dynamic R–L line

Model boundary.
* The five-state VSM + power filter (droop + LPF) `Line.VSMLPF` of
  `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged: state
  `(δ, ω, P_f, i_d, i_q) : State 5`, grid dq frame at `ω₀`, export-positive power, constant `E`,
  `M ω̇ = P_ref − P_f − D ω`, `Ṗ_f = ω_c (P_e − P_f)`, `L i̇ = E e^{jδ} − V − (R + jX) i`; no
  voltage loop, inner loops, PLL, delay or PWM. Read about a selected angle
  (`Line.VSMLPF.Model`), translated so that the operating point is the origin.
* A Hopf point of the quintic at the frequency `ω` (`Line.VSMLPF.Model.HopfAt`): `±iω` are roots
  of the monic characteristic quintic `s⁵ + a₄ s⁴ + … + a₀` at the operating point
  (`ω⁴ − a₃ ω² + a₁ = 0`, `a₄ ω⁴ − a₂ ω² + a₀ = 0`) and the complementary cubic
  `s³ + a₄ s² + (a₃ − ω²) s + (a₂ − a₄ ω²)` is Hurwitz; this is the boundary `Δ₄ = 0` of the
  quintic Routh region of `Line.VSMLPF.family` with a simple pair `±iω`.
* Level: Lyapunov instability and local asymptotic stability (LeanForControl's `Unstable`,
  `LocalAsymptoticStable`) of the operating point. Not stated: the bifurcating cycles (their
  existence is the generic `Dynamics.HopfCycle.exists_hopfCycle`, given `ℓ₁ ≠ 0` and the
  transversality `τ ≠ 0`, instantiated only for `VSMLPF` in `VSMLPFHopfCycle`; for this model the
  transversality computation and the instance are missing, and uniqueness and orbital stability
  are not proved); a closed
  form of `ℓ₁` for all parameters (the exact real-part numerator in the frame rotated with `δ*`
  has thousands of terms before the reduction modulo the two frequency relations; open), hence
  no sign law and no complete local asymptotic membership for this model off the zero-current
  slice; on the slice `δ* = 0`, `V = E` they are in
  `theorem/GridTiedConverter/GFM/HopfLineLPFSlice.lean`.

Source: the four-state laws `theorem/GridTiedConverter/GFM/HopfLineInstability.lean` (same
method); Carr, *Applications of Centre Manifold Theory* (1981), §2.4; Kuznetsov, *Elements of
Applied Bifurcation Theory* (3rd ed.), §3.5 and §5.4
(`NormalForm.LyapunovCoefficient.firstLyapunov`); the witnesses were found and their critical
data computed in exact rational arithmetic with SymPy (untrusted discovery; every value is
checked here by `norm_num`). The generic laws are
`theorem/Dynamics/HopfDichotomy.lean`.

Results.
* The field in pieces (`Line.VSMLPF.field_eq_pieces`, `Line.VSMLPF.affinePart`,
  `Line.VSMLPF.constPart`); the derivatives at any state `Line.VSMLPF.bilinC_field_eq`,
  `Line.VSMLPF.trilinC_field_eq`; `Line.VSMLPF.Model.jacobianC_field`,
  `Line.VSMLPF.Model.analyticAt_field`.
* `Line.VSMLPF.Model.exists_charpoly_factor_of_hopfAt` (the factorization
  `(s² + ω²)(s³ + a₄ s² + (a₃ − ω²) s + (a₂ − a₄ ω²))`),
  `Line.VSMLPF.Model.freq_eqs_of_isCriticalPair` (a critical pair puts `iω` on the quintic),
  `Line.VSMLPF.Model.exists_isCriticalPair_of_hopfAt` (`ℓ₁` is defined at every Hopf point),
  `Line.VSMLPF.Model.sign_firstLyapunov_eq_of_hopfAt` (its sign does not depend on the pair).
* Witnesses at zero load: `Line.VSMLPF.hopfWitnessSup` (`E = V = R = L = ω₀ = 1`, `M = 7/50`,
  `D = 21/50`, `ω_c = 7`; `Line.VSMLPF.hopfWitnessSup_isCriticalPair`,
  `Line.VSMLPF.hopfWitnessSup_firstLyapunov`: `ℓ₁ = −14341/14450`) and `Line.VSMLPF.hopfWitness`
  (`R = 1/5`, `ω₀ = 3`, `M = 15000/40501`, `D = 1500/40501`, `ω_c = 20`;
  `Line.VSMLPF.hopfWitness_isCriticalPair`, `Line.VSMLPF.hopfWitness_firstLyapunov`: `ℓ₁ > 0`).

Family and connection conclusions.
No new family: connection conclusions on `Line.VSMLPF.family`.
* `Line.VSMLPF.mem_den_unstable_of_firstLyapunov_pos`,
  `Line.VSMLPF.mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg`: at a Hopf point of the
  quintic, `ℓ₁ > 0` gives instability and `ℓ₁ < 0` local asymptotic stability.
* `Line.VSMLPF.hopfWitnessSup_mem_den_locallyAsymptoticallyStable` (supercritical) and
  `Line.VSMLPF.hopfWitness_mem_den_unstable` (subcritical); hence neither the local asymptotic
  nor the instability translation of `Line.VSMLPF.family` is exact within physical models
  (`Line.VSMLPF.not_exactUnder_locallyAsymptoticallyStable`,
  `Line.VSMLPF.not_exactUnder_unstable`).
-/

noncomputable section
namespace powerlib.GFM.Line
namespace VSMLPF
open Complex Matrix Polynomial
open powerlib.Dynamics (State coord)
open powerlib.NormalForm.LyapunovCoefficient

/-! ## The field in pieces and its derivatives at any state -/

section Pieces

variable (g : VSMLPF)

/-- The affine part of the field. -/
def affinePart : State 5 →L[ℝ] State 5 :=
  Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ)
    !![0, 1, 0, 0, 0; 0, -g.D / g.M, -1 / g.M, 0, 0; 0, 0, -g.ωc, 0, 0;
      0, 0, 0, -g.R / g.L, g.X / g.L; 0, 0, 0, -g.X / g.L, -g.R / g.L]

/-- The constant part of the field. -/
def constPart : State 5 := WithLp.toLp 2 ![0, g.Pref / g.M, 0, -g.V / g.L, 0]

/-- The field as an affine field plus four one-nonlinearity terms. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem field_eq_pieces :
    g.field =
      ridge g.affinePart g.constPart (coord 0) (fun t => g.E / g.L * Real.cos t)
          (EuclideanSpace.single 3 1) +
        ridge 0 0 (coord 0) (fun t => g.E / g.L * Real.sin t) (EuclideanSpace.single 4 1) +
        prodRidge (coord 0) (coord 3) Real.cos ((g.ωc * g.E) • EuclideanSpace.single 2 1) +
        prodRidge (coord 0) (coord 4) Real.sin ((g.ωc * g.E) • EuclideanSpace.single 2 1) := by
  funext x
  ext i
  fin_cases i <;>
    simp [field, ridge, prodRidge, affinePart, constPart, Dynamics.toEuclideanCLM_apply,
      Fin.sum_univ_five, Network.power_eq, Network.rateD, Network.rateQ] <;>
    ring

@[tmio M, powerlib_domain] private theorem lpf_cos_chain (c : ℝ) :
    (∀ t, HasDerivAt (fun t => c * Real.cos t) (-(c * Real.sin t)) t) ∧
    (∀ t, HasDerivAt (fun t => -(c * Real.sin t)) (-(c * Real.cos t)) t) ∧
    (∀ t, HasDerivAt (fun t => -(c * Real.cos t)) (c * Real.sin t) t) :=
  ⟨fun t => ((Real.hasDerivAt_cos t).const_mul c).congr_deriv (by ring),
    fun t => ((Real.hasDerivAt_sin t).const_mul c).neg,
    fun t => ((Real.hasDerivAt_cos t).const_mul c).neg.congr_deriv (by ring)⟩

@[tmio M, powerlib_domain] private theorem lpf_sin_chain (c : ℝ) :
    (∀ t, HasDerivAt (fun t => c * Real.sin t) (c * Real.cos t) t) ∧
    (∀ t, HasDerivAt (fun t => c * Real.cos t) (-(c * Real.sin t)) t) ∧
    (∀ t, HasDerivAt (fun t => -(c * Real.sin t)) (-(c * Real.cos t)) t) :=
  ⟨fun t => (Real.hasDerivAt_sin t).const_mul c,
    fun t => ((Real.hasDerivAt_cos t).const_mul c).congr_deriv (by ring),
    fun t => ((Real.hasDerivAt_sin t).const_mul c).neg⟩

@[tmio M, powerlib_domain] private theorem lpf_contDiff_pieces :
    ContDiff ℝ 3 (ridge g.affinePart g.constPart (coord (n := 5) 0)
        (fun t => g.E / g.L * Real.cos t) (EuclideanSpace.single 3 1)) ∧
    ContDiff ℝ 3 (ridge 0 0 (coord (n := 5) 0) (fun t => g.E / g.L * Real.sin t)
        (EuclideanSpace.single 4 1)) ∧
    ContDiff ℝ 3 (prodRidge (coord (n := 5) 0) (coord (n := 5) 3) Real.cos
        ((g.ωc * g.E) • EuclideanSpace.single 2 1)) ∧
    ContDiff ℝ 3 (prodRidge (coord (n := 5) 0) (coord (n := 5) 4) Real.sin
        ((g.ωc * g.E) • EuclideanSpace.single 2 1)) :=
  ⟨contDiff_ridge _ _ _ _ (by fun_prop), contDiff_ridge _ _ _ _ (by fun_prop),
    contDiff_prodRidge _ _ _ Real.contDiff_cos, contDiff_prodRidge _ _ _ Real.contDiff_sin⟩

/-- **The second derivative at any state** `x₀` (angle `δ = x₀ 0`):
`B(u, w) = (0, 0, −ω_c P_e u₀w₀ − ω_c E (sin δ (u₀w₃ + u₃w₀) − cos δ (u₀w₄ + u₄w₀)),
−(E/L) cos δ u₀w₀, −(E/L) sin δ u₀w₀)`, `P_e` the exported power at `x₀`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem bilinC_field_eq (x₀ : State 5) (u w : Fin 5 → ℂ) :
    bilinC g.field x₀ u w =
      ![0, 0, -((g.ωc * g.power (x₀ 0) (x₀ 3) (x₀ 4) : ℝ) : ℂ) * (u 0 * w 0) -
          ((g.ωc * g.E * Real.sin (x₀ 0) : ℝ) : ℂ) * (u 0 * w 3 + u 3 * w 0) +
          ((g.ωc * g.E * Real.cos (x₀ 0) : ℝ) : ℂ) * (u 0 * w 4 + u 4 * w 0),
        -((g.E / g.L * Real.cos (x₀ 0) : ℝ) : ℂ) * (u 0 * w 0),
        -((g.E / g.L * Real.sin (x₀ 0) : ℝ) : ℂ) * (u 0 * w 0)] := by
  obtain ⟨c1, c2, c3, c4⟩ := lpf_contDiff_pieces g
  have k2 : (2 : WithTop ℕ∞) ≤ 3 := by norm_num
  rw [field_eq_pieces, bilinC_add, bilinC_add, bilinC_add,
    bilinC_ridge _ _ _ _ (by fun_prop), bilinC_ridge _ _ _ _ (by fun_prop),
    bilinC_prodRidge _ _ _ Real.contDiff_cos Real.hasDerivAt_cos
      (fun t => (Real.hasDerivAt_sin t).neg),
    bilinC_prodRidge _ _ _ Real.contDiff_sin Real.hasDerivAt_sin Real.hasDerivAt_cos,
    (iteratedDeriv_of_hasDerivAt (lpf_cos_chain _).1 (lpf_cos_chain _).2.1
      (lpf_cos_chain _).2.2 _).2.1,
    (iteratedDeriv_of_hasDerivAt (lpf_sin_chain _).1 (lpf_sin_chain _).2.1
      (lpf_sin_chain _).2.2 _).2.1]
  · ext i
    fin_cases i <;> simp [toC, Network.power_eq] <;> ring
  all_goals first | exact c1.of_le k2 | exact c2.of_le k2 | exact c3.of_le k2 |
    exact c4.of_le k2 | exact (c1.add c2).of_le k2 | exact ((c1.add c2).add c3).of_le k2

/-- **The third derivative at any state** `x₀` (angle `δ = x₀ 0`):
`C(u, w, z) = (0, 0, ω_c Q_e u₀w₀z₀ − ω_c E (cos δ Σ₃ + sin δ Σ₄), (E/L) sin δ u₀w₀z₀,
−(E/L) cos δ u₀w₀z₀)`, `Σₖ = u₀w₀zₖ + u₀wₖz₀ + uₖw₀z₀`, `Q_e` the reactive power at `x₀`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem trilinC_field_eq (x₀ : State 5) (u w z : Fin 5 → ℂ) :
    trilinC g.field x₀ u w z =
      ![0, 0, ((g.ωc * g.reactive (x₀ 0) (x₀ 3) (x₀ 4) : ℝ) : ℂ) * (u 0 * w 0 * z 0) -
          ((g.ωc * g.E * Real.cos (x₀ 0) : ℝ) : ℂ) *
            (u 0 * w 0 * z 3 + u 0 * w 3 * z 0 + u 3 * w 0 * z 0) -
          ((g.ωc * g.E * Real.sin (x₀ 0) : ℝ) : ℂ) *
            (u 0 * w 0 * z 4 + u 0 * w 4 * z 0 + u 4 * w 0 * z 0),
        ((g.E / g.L * Real.sin (x₀ 0) : ℝ) : ℂ) * (u 0 * w 0 * z 0),
        -((g.E / g.L * Real.cos (x₀ 0) : ℝ) : ℂ) * (u 0 * w 0 * z 0)] := by
  obtain ⟨c1, c2, c3, c4⟩ := lpf_contDiff_pieces g
  rw [field_eq_pieces, trilinC_add, trilinC_add, trilinC_add,
    trilinC_ridge _ _ _ _ (by fun_prop), trilinC_ridge _ _ _ _ (by fun_prop),
    trilinC_prodRidge _ _ _ Real.contDiff_cos (Real.hasDerivAt_cos)
      (fun t => (Real.hasDerivAt_sin t).neg)
      (fun t => (Real.hasDerivAt_cos t).neg.congr_deriv (neg_neg _)),
    trilinC_prodRidge _ _ _ Real.contDiff_sin Real.hasDerivAt_sin Real.hasDerivAt_cos
      (fun t => (Real.hasDerivAt_sin t).neg),
    (iteratedDeriv_of_hasDerivAt (lpf_cos_chain _).1 (lpf_cos_chain _).2.1
      (lpf_cos_chain _).2.2 _).2.2,
    (iteratedDeriv_of_hasDerivAt (lpf_sin_chain _).1 (lpf_sin_chain _).2.1
      (lpf_sin_chain _).2.2 _).2.2]
  · ext i
    fin_cases i <;> simp [toC, Network.reactive_eq] <;> ring
  all_goals first | exact c1 | exact c2 | exact c3 | exact c4 | exact c1.add c2 |
    exact (c1.add c2).add c3

end Pieces

/-! ## The model at its operating point -/

/-- The complexified Jacobian of the model field at the operating point is that of `Model.jac`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.jacobianC_field (m : Model) :
    jacobianC m.field 0 = Linear.complexify m.jac := by
  have h : fderiv ℝ m.field 0 = Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) m.jac := by
    rw [show m.field = fun z => m.g.field (z + m.point) from rfl, fderiv_comp_add_right,
      zero_add, m.fderiv_point]
  rw [jacobianC, h, cmat_toEuclideanCLM]
  rfl

/-- The model field is analytic at the operating point (`sin`, `cos` and polynomials). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.analyticAt_field (m : Model) :
    AnalyticAt ℝ m.field 0 := by
  have h : ContDiff ℝ (⊤ : WithTop ℕ∞) m.field :=
    (m.g.contDiff_field (k := ⊤)).comp (contDiff_id.add contDiff_const)
  exact h.contDiffAt.analyticAt

/-! ## The quintic on its Hopf boundary -/

/-- **A Hopf point of the quintic at the frequency `ω`**: `±iω` are roots
(`ω⁴ − a₃ ω² + a₁ = 0`, `a₄ ω⁴ − a₂ ω² + a₀ = 0`) and the complementary cubic
`s³ + a₄ s² + (a₃ − ω²) s + (a₂ − a₄ ω²)` meets the cubic Routh conditions. -/
def Model.HopfAt (m : Model) (ω : ℝ) : Prop :=
  0 < ω ∧ ω ^ 4 - m.g.coeff3 * ω ^ 2 + m.g.coeff1 m.Q = 0 ∧
    m.g.coeff4 * ω ^ 4 - m.g.coeff2 m.Q * ω ^ 2 + m.g.coeff0 m.Q = 0 ∧ 0 < m.g.coeff4 ∧
    0 < m.g.coeff2 m.Q - m.g.coeff4 * ω ^ 2 ∧
    m.g.coeff2 m.Q - m.g.coeff4 * ω ^ 2 < m.g.coeff4 * (m.g.coeff3 - ω ^ 2)

/-- **The quintic factors at a Hopf point**: `det(sI − J) = (s² + ω²)(s³ + a₄ s² +
(a₃ − ω²) s + (a₂ − a₄ ω²))`, the cubic factor Hurwitz. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.exists_charpoly_factor_of_hopfAt (m : Model) {ω : ℝ}
    (h : m.HopfAt ω) :
    ∃ r : ℂ[X], (jacobianC m.field 0).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r ∧
      ∀ s : ℂ, r.eval s = 0 → s.re < 0 := by
  obtain ⟨-, h1, h2, h4, h0, hg⟩ := h
  refine ⟨X ^ 3 + C ((m.g.coeff4 : ℝ) : ℂ) * X ^ 2 + C (((m.g.coeff3 - ω ^ 2 : ℝ)) : ℂ) * X +
    C (((m.g.coeff2 m.Q - m.g.coeff4 * ω ^ 2 : ℝ)) : ℂ), ?_, fun s hs => ?_⟩
  · refine Polynomial.funext fun s => ?_
    rw [m.jacobianC_field, ← Linear.det_characteristicMatrix_eq_eval, m.det_characteristicMatrix]
    have e1 : ((m.g.coeff1 m.Q : ℝ) : ℂ) = ((m.g.coeff3 * ω ^ 2 - ω ^ 4 : ℝ) : ℂ) := by
      congr 1; linarith
    have e0 : ((m.g.coeff0 m.Q : ℝ) : ℂ) =
        ((ω ^ 2 * (m.g.coeff2 m.Q - m.g.coeff4 * ω ^ 2) : ℝ) : ℂ) := by
      congr 1; linarith
    simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C]
    rw [e1, e0]
    push_cast
    ring
  · refine (Criteria.cubic_roots_re_neg_iff _ _ _).mpr ⟨h4, h0, hg⟩ s ?_
    simpa using hs

/-- **The frequency of a critical pair**: a critical pair at `ω` makes `iω` a root of the quintic,
`ω⁴ − a₃ ω² + a₁ = 0` and `a₄ ω⁴ − a₂ ω² + a₀ = 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.freq_eqs_of_isCriticalPair (m : Model) {ω : ℝ}
    {q p : Fin 5 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p) :
    ω ^ 4 - m.g.coeff3 * ω ^ 2 + m.g.coeff1 m.Q = 0 ∧
      m.g.coeff4 * ω ^ 4 - m.g.coeff2 m.Q * ω ^ 2 + m.g.coeff0 m.Q = 0 := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    have h := hcp.normalized
    simp at h
  have hdet := (Linear.det_characteristicMatrix_eq_zero_iff_exists_eigenpair m.jac
    ((ω : ℂ) * I)).mpr ⟨q, hq0, by rw [← m.jacobianC_field]; exact hcp.right⟩
  rw [m.det_characteristicMatrix] at hdet
  have him := congrArg Complex.im hdet
  have hre := congrArg Complex.re hdet
  simp [pow_succ, Complex.mul_im, Complex.mul_re] at him hre
  have hω := hcp.freq_pos
  constructor
  · have h : ω * (ω ^ 4 - m.g.coeff3 * ω ^ 2 + m.g.coeff1 m.Q) = 0 := by
      linear_combination him
    exact (mul_eq_zero.mp h).resolve_left hω.ne'
  · linear_combination hre

/-- **`ℓ₁` is defined at every Hopf point**: a balanced physical model with a Hopf point of its
quintic at `ω` has a critical pair at `ω`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.exists_isCriticalPair_of_hopfAt (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) {ω : ℝ} (h : m.HopfAt ω) :
    ∃ q p : Fin 5 → ℂ, IsCriticalPair m.field 0 ω q p := by
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_hopfAt h
  obtain ⟨q, p, hc⟩ := Dynamics.CenterManifold.exists_isCritical_of_charpoly h.1 hchar hr
  have heq : m.field 0 = 0 := by
    have h' := (m.field_point_eq_zero_iff hp.2.1.ne' hp.2.2.2.ne' hp.1.L.ne'
      hp.1.absSq_pos.ne').mpr hb
    simpa [Model.field] using h'
  exact ⟨q, p, heq, h.1, hc.right, hc.left, hc.normalized⟩

/-- **The sign of `ℓ₁` is a property of the model**: at a Hopf point of the quintic all critical
pairs at `ω` give first Lyapunov coefficients of the same sign. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.sign_firstLyapunov_eq_of_hopfAt (m : Model) {ω : ℝ}
    (h : m.HopfAt ω) {q p q' p' : Fin 5 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p)
    (hcp' : IsCriticalPair m.field 0 ω q' p') :
    SignType.sign (firstLyapunov m.field 0 ω q' p') =
      SignType.sign (firstLyapunov m.field 0 ω q p) := by
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_hopfAt h
  exact Dynamics.CenterManifold.sign_firstLyapunov_eq_of_charpoly hchar hr hcp hcp'

/-! ## The family laws at a Hopf point -/

/-- **Subcritical Hopf points are unstable**: a model with a Hopf point of its quintic at `ω`
(`Line.VSMLPF.Model.HopfAt`) and a critical pair at `ω` with `ℓ₁ > 0` is unstable
(`Dynamics.CenterManifold.unstable_of_firstLyapunov_pos_of_charpoly`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_firstLyapunov_pos (m : Model) {ω : ℝ}
    (h : m.HopfAt ω) {q p : Fin 5 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p)
    (hl : 0 < firstLyapunov m.field 0 ω q p) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Unstable m.field 0
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_hopfAt h
  exact Dynamics.CenterManifold.unstable_of_firstLyapunov_pos_of_charpoly m.contDiff_field
    m.analyticAt_field hcp hchar hr hl

/-- **Supercritical Hopf points are locally asymptotically stable**: a model with a Hopf point of
its quintic at `ω` and a critical pair at `ω` with `ℓ₁ < 0` is locally asymptotically stable
(`Dynamics.CenterManifold.localAsymptoticStable_of_firstLyapunov_neg_of_charpoly`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg
    (m : Model) {ω : ℝ} (h : m.HopfAt ω) {q p : Fin 5 → ℂ}
    (hcp : IsCriticalPair m.field 0 ω q p) (hl : firstLyapunov m.field 0 ω q p < 0) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change LocalAsymptoticStable m.field 0
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_hopfAt h
  exact Dynamics.CenterManifold.localAsymptoticStable_of_firstLyapunov_neg_of_charpoly
    m.contDiff_field m.analyticAt_field hcp hchar hr hl

/-! ## Witnesses: a supercritical and a subcritical Hopf point

Two balanced physical models at zero load (`V = E`, `P_ref = 0`, `δ* = 0`, so the operating point
is the origin and `Q = 0`) whose quintic has the roots `±i`; their first Lyapunov coefficients are
exact rationals (critical pair, resolvent solutions and pairings checked by `norm_num`). -/

@[tmio M, powerlib_domain] private theorem field_eq_of_point {m : Model} (h : m.point = 0) :
    m.field = m.g.field := by
  funext z
  simp [Model.field, h]

/-- The witness `E = V = R = L = ω₀ = 1`, `M = 7/50`, `D = 21/50`, `ω_c = 7`, `P_ref = 0`,
    `δ* = 0`. -/
def hopfWitnessSup : Model := ⟨⟨⟨⟨1, 1, 1, 1, 1⟩, 7 / 50, 21 / 50, 0⟩, 7⟩, 0⟩

@[tmio M, powerlib_domain] private theorem hopfWitnessSup_point : hopfWitnessSup.point = 0 := by
  ext i
  fin_cases i <;> simp [Model.point, qss, hopfWitnessSup, Network.is, Dynamics.mk3]

@[tmio M, powerlib_domain] private theorem hopfWitnessSup_physical : Meets hopfWitnessSup
    .physical := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> norm_num [hopfWitnessSup]

@[tmio M, powerlib_domain] private theorem hopfWitnessSup_balanced : Meets hopfWitnessSup
    .balanced := by
  change hopfWitnessSup.g.qssPower hopfWitnessSup.δ = hopfWitnessSup.g.Pref
  norm_num [Network.qssPower, hopfWitnessSup, Network.is, Network.power_eq]

@[tmio M, powerlib_domain] private theorem hopfWitnessSup_Q : hopfWitnessSup.Q = 0 := by
  norm_num [Model.Q, Network.qssReactive, hopfWitnessSup, Network.is, Network.reactive_eq]

@[tmio M, powerlib_domain] private theorem hopfWitnessSup_coeffs :
    hopfWitnessSup.g.coeff4 = 12 ∧ hopfWitnessSup.g.coeff3 = 43
        ∧ hopfWitnessSup.g.coeff2 hopfWitnessSup.Q = 62 ∧
      hopfWitnessSup.g.coeff1 hopfWitnessSup.Q = 42
          ∧ hopfWitnessSup.g.coeff0 hopfWitnessSup.Q = 50 := by
  rw [hopfWitnessSup_Q]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [coeff4, coeff3, coeff2, coeff1, coeff0, VSM.coeff1, VSM.coeff0, hopfWitnessSup,
        Network.ρ,
      Network.σ, Network.X]

@[tmio M, powerlib_domain] private theorem hopfWitnessSup_hopfAt : hopfWitnessSup.HopfAt 1 := by
  obtain ⟨h4, h3, h2, h1, h0⟩ := hopfWitnessSup_coeffs
  refine ⟨one_pos, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [h4, h3, h2, h1, h0] <;> norm_num

@[tmio M, powerlib_domain] private theorem hopfWitnessSup_jacobianC :
    jacobianC hopfWitnessSup.field 0 =
      (!![0, 1, 0, 0, 0; 0, -3, -50 / 7, 0, 0; 0, 0, -7, 7, 0; 0, 0, 0, -1, 1; 1, 0, 0, -1, -1] :
        Matrix (Fin 5) (Fin 5) ℝ).map (fun x => (x : ℂ)) := by
  rw [Model.jacobianC_field]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Model.jac, jacobian, hopfWitnessSup, Network.is, Network.reactive_eq, Network.X]

@[tmio M, powerlib_domain] private theorem hopfWitnessSup_bilinC (u w : Fin 5 → ℂ) :
    bilinC hopfWitnessSup.field 0 u w =
      ![0, 0, 7 * (u 0 * w 4 + u 4 * w 0), -(u 0 * w 0), 0] := by
  rw [field_eq_of_point hopfWitnessSup_point, bilinC_field_eq]
  ext i
  fin_cases i <;> norm_num [hopfWitnessSup, Network.power_eq]

@[tmio M, powerlib_domain] private theorem hopfWitnessSup_trilinC (u w z : Fin 5 → ℂ) :
    trilinC hopfWitnessSup.field 0 u w z =
      ![0, 0, -(7 * (u 0 * w 0 * z 3 + u 0 * w 3 * z 0 + u 3 * w 0 * z 0)), 0,
        -(u 0 * w 0 * z 0)] := by
  rw [field_eq_of_point hopfWitnessSup_point, trilinC_field_eq]
  ext i
  fin_cases i <;> norm_num [hopfWitnessSup, Network.reactive_eq]

/-- The critical right eigenvector of `hopfWitnessSup` at `ω = 1`. -/
def hopfWitnessSupQ : Fin 5 → ℂ :=
  ![((1 : ℝ) : ℂ) + ((2 : ℝ) : ℂ) * I, ((-2 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * I,
    ((49 / 50 : ℝ) : ℂ) + ((-7 / 50 : ℝ) : ℂ) * I, ((1 : ℝ) : ℂ),
    ((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * I]

/-- The critical left eigenvector of `hopfWitnessSup` at `ω = 1` (`⟨p, q⟩ = 1`). -/
def hopfWitnessSupP : Fin 5 → ℂ :=
  ![((-44 / 625 : ℝ) : ℂ) + ((117 / 625 : ℝ) : ℂ) * I,
    ((-249 / 6250 : ℝ) : ℂ) + ((307 / 6250 : ℝ) : ℂ) * I,
    ((41 / 875 : ℝ) : ℂ) + ((-38 / 875 : ℝ) : ℂ) * I,
    ((161 / 625 : ℝ) : ℂ) + ((-73 / 625 : ℝ) : ℂ) * I,
    ((117 / 625 : ℝ) : ℂ) + ((44 / 625 : ℝ) : ℂ) * I]

/-- **The critical pair** of `hopfWitnessSup` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem hopfWitnessSup_isCriticalPair :
    IsCriticalPair hopfWitnessSup.field 0 1 hopfWitnessSupQ hopfWitnessSupP := by
  refine ⟨?_, one_pos, ?_, ?_, ?_⟩
  · rw [field_eq_of_point hopfWitnessSup_point]
    ext i
    fin_cases i <;> norm_num [field, hopfWitnessSup, Network.power_eq, Network.rateD, Network.rateQ,
      Network.X]
  · rw [hopfWitnessSup_jacobianC]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_five, hopfWitnessSupQ,
        Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num
  · rw [hopfWitnessSup_jacobianC]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_five, hopfWitnessSupP,
        Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num
  · simp [dotProduct, Fin.sum_univ_five, hopfWitnessSupP, hopfWitnessSupQ, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num

/-- **The first Lyapunov coefficient of `hopfWitnessSup`**: `ℓ₁
    = -14341 / 14450`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem hopfWitnessSup_firstLyapunov :
    firstLyapunov hopfWitnessSup.field 0 1 hopfWitnessSupQ hopfWitnessSupP = -14341 / 14450 := by
  set r : Fin 5 → ℂ :=
    ![((7 : ℝ) : ℂ), ((0 : ℝ) : ℂ), ((0 : ℝ) : ℂ), ((6 : ℝ) : ℂ), ((1 : ℝ) : ℂ)]
  set s : Fin 5 → ℂ :=
    ![((-1155 / 289 : ℝ) : ℂ) + ((540 / 289 : ℝ) : ℂ) * I,
      ((-1080 / 289 : ℝ) : ℂ) + ((-2310 / 289 : ℝ) : ℂ) * I,
      ((-966 / 1445 : ℝ) : ℂ) + ((6363 / 1445 : ℝ) : ℂ) * I,
      ((106 / 1445 : ℝ) : ℂ) + ((-2583 / 1445 : ℝ) : ℂ) * I,
      ((937 / 1445 : ℝ) : ℂ) + ((3409 / 1445 : ℝ) : ℂ) * I]
  obtain ⟨r0, hchar, hr0⟩ := hopfWitnessSup.exists_charpoly_factor_of_hopfAt hopfWitnessSup_hopfAt
  obtain ⟨hA, h2⟩ := Dynamics.CenterManifold.isUnit_det_of_charpoly one_ne_zero hchar hr0
  have hr : jacobianC hopfWitnessSup.field 0 *ᵥ r
      = bilinC hopfWitnessSup.field 0 hopfWitnessSupQ (star hopfWitnessSupQ) := by
    rw [hopfWitnessSup_jacobianC, hopfWitnessSup_bilinC]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_five, hopfWitnessSupQ, r,
        Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num
  have hs : shift2 (jacobianC hopfWitnessSup.field 0) 1 *ᵥ s
      = bilinC hopfWitnessSup.field 0 hopfWitnessSupQ hopfWitnessSupQ := by
    rw [hopfWitnessSup_jacobianC, hopfWitnessSup_bilinC, shift2]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_five, hopfWitnessSupQ, s,
        Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num
  rw [firstLyapunov_eq_of_solve hA h2 hr hs, hopfWitnessSup_trilinC, hopfWitnessSup_bilinC,
      hopfWitnessSup_bilinC]
  simp [pairing_apply, Fin.sum_univ_five, hopfWitnessSupP, hopfWitnessSupQ, r, s, Complex.mul_re,
      Complex.mul_im,
    -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
    -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
  norm_num

/-- The witness `E = V = L = 1`, `R = 1/5`, `ω₀ = 3`, `M = 15000/40501`, `D = 1500/40501`,
    `ω_c = 20`, `P_ref = 0`, `δ* = 0`. -/
def hopfWitness : Model := ⟨⟨⟨⟨1, 1, 1 / 5, 1, 3⟩, 15000 / 40501, 1500 / 40501, 0⟩, 20⟩, 0⟩

@[tmio M, powerlib_domain] private theorem hopfWitness_point : hopfWitness.point = 0 := by
  ext i
  fin_cases i <;> simp [Model.point, qss, hopfWitness, Network.is, Dynamics.mk3]

@[tmio M, powerlib_domain] private theorem hopfWitness_physical : Meets hopfWitness .physical := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> norm_num [hopfWitness]

@[tmio M, powerlib_domain] private theorem hopfWitness_balanced : Meets hopfWitness .balanced := by
  change hopfWitness.g.qssPower hopfWitness.δ = hopfWitness.g.Pref
  norm_num [Network.qssPower, hopfWitness, Network.is, Network.power_eq]

@[tmio M, powerlib_domain] private theorem hopfWitness_Q : hopfWitness.Q = 0 := by
  norm_num [Model.Q, Network.qssReactive, hopfWitness, Network.is, Network.reactive_eq]

@[tmio M, powerlib_domain] private theorem hopfWitness_coeffs :
    hopfWitness.g.coeff4 = 41 / 2 ∧ hopfWitness.g.coeff3 = 477 / 25
        ∧ hopfWitness.g.coeff2 hopfWitness.Q = 22813 / 125 ∧
      hopfWitness.g.coeff1 hopfWitness.Q = 452 / 25
          ∧ hopfWitness.g.coeff0 hopfWitness.Q = 40501 / 250 := by
  rw [hopfWitness_Q]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [coeff4, coeff3, coeff2, coeff1, coeff0, VSM.coeff1, VSM.coeff0, hopfWitness,
        Network.ρ,
      Network.σ, Network.X]

@[tmio M, powerlib_domain] private theorem hopfWitness_hopfAt : hopfWitness.HopfAt 1 := by
  obtain ⟨h4, h3, h2, h1, h0⟩ := hopfWitness_coeffs
  refine ⟨one_pos, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [h4, h3, h2, h1, h0] <;> norm_num

@[tmio M, powerlib_domain] private theorem hopfWitness_jacobianC :
    jacobianC hopfWitness.field 0 =
      (!![0, 1, 0, 0, 0; 0, -1 / 10, -40501 / 15000, 0, 0; 0, 0, -20, 20, 0; 0, 0, 0, -1 / 5,
          3; 1, 0, 0, -3, -1 / 5] :
        Matrix (Fin 5) (Fin 5) ℝ).map (fun x => (x : ℂ)) := by
  rw [Model.jacobianC_field]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Model.jac, jacobian, hopfWitness, Network.is, Network.reactive_eq, Network.X]

@[tmio M, powerlib_domain] private theorem hopfWitness_bilinC (u w : Fin 5 → ℂ) :
    bilinC hopfWitness.field 0 u w =
      ![0, 0, 20 * (u 0 * w 4 + u 4 * w 0), -(u 0 * w 0), 0] := by
  rw [field_eq_of_point hopfWitness_point, bilinC_field_eq]
  ext i
  fin_cases i <;> norm_num [hopfWitness, Network.power_eq]

@[tmio M, powerlib_domain] private theorem hopfWitness_trilinC (u w z : Fin 5 → ℂ) :
    trilinC hopfWitness.field 0 u w z =
      ![0, 0, -(20 * (u 0 * w 0 * z 3 + u 0 * w 3 * z 0 + u 3 * w 0 * z 0)), 0,
        -(u 0 * w 0 * z 0)] := by
  rw [field_eq_of_point hopfWitness_point, trilinC_field_eq]
  ext i
  fin_cases i <;> norm_num [hopfWitness, Network.reactive_eq]

/-- The critical right eigenvector of `hopfWitness` at `ω = 1`. -/
def hopfWitnessQ : Fin 5 → ℂ :=
  ![((201 / 25 : ℝ) : ℂ) + ((2 / 5 : ℝ) : ℂ) * I, ((-2 / 5 : ℝ) : ℂ) + ((201 / 25 : ℝ) : ℂ) * I,
    ((1200 / 401 : ℝ) : ℂ) + ((-60 / 401 : ℝ) : ℂ) * I, ((3 : ℝ) : ℂ),
    ((1 / 5 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * I]

/-- The critical left eigenvector of `hopfWitness` at `ω = 1` (`⟨p, q⟩ = 1`). -/
def hopfWitnessP : Fin 5 → ℂ :=
  ![((44174225 / 634847138 : ℝ) : ℂ) + ((15150375 / 1269694276 : ℝ) : ℂ) * I,
    ((-1563250 / 317423569 : ℝ) : ℂ) + ((44486875 / 634847138 : ℝ) : ℂ) * I,
    ((17293927 / 15236331312 : ℝ) : ℂ) + ((-29849237 / 3174235690 : ℝ) : ℂ) * I,
    ((-85318375 / 3809082828 : ℝ) : ℂ) + ((-32820065 / 3809082828 : ℝ) : ℂ) * I,
    ((15150375 / 1269694276 : ℝ) : ℂ) + ((-44174225 / 634847138 : ℝ) : ℂ) * I]

/-- **The critical pair** of `hopfWitness` at `ω = 1`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem hopfWitness_isCriticalPair :
    IsCriticalPair hopfWitness.field 0 1 hopfWitnessQ hopfWitnessP := by
  refine ⟨?_, one_pos, ?_, ?_, ?_⟩
  · rw [field_eq_of_point hopfWitness_point]
    ext i
    fin_cases i <;> norm_num [field, hopfWitness, Network.power_eq, Network.rateD, Network.rateQ,
      Network.X]
  · rw [hopfWitness_jacobianC]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_five, hopfWitnessQ, Complex.ext_iff,
        -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num
  · rw [hopfWitness_jacobianC]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_five, hopfWitnessP, Complex.ext_iff,
        -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num
  · simp [dotProduct, Fin.sum_univ_five, hopfWitnessP, hopfWitnessQ, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num

/-- **The first Lyapunov coefficient of `hopfWitness`**: `ℓ₁
    = 795686360348046533 / 264278927960175000`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem hopfWitness_firstLyapunov :
    firstLyapunov hopfWitness.field 0 1 hopfWitnessQ hopfWitnessP
        = 795686360348046533 / 264278927960175000 := by
  set r : Fin 5 → ℂ :=
    ![((24317 / 3125 : ℝ) : ℂ), ((0 : ℝ) : ℂ), ((0 : ℝ) : ℂ), ((502 / 125 : ℝ) : ℂ),
      ((-13333 / 625 : ℝ) : ℂ)]
  set s : Fin 5 → ℂ :=
    ![((-1075261049 / 312215625 : ℝ) : ℂ) + ((-1539038 / 166515 : ℝ) : ℂ) * I,
      ((3078076 / 166515 : ℝ) : ℂ) + ((-2150522098 / 312215625 : ℝ) : ℂ) * I,
      ((-963568 / 166515 : ℝ) : ℂ) + ((-11187608 / 832575 : ℝ) : ℂ) * I,
      ((-9517634 / 1387625 : ℝ) : ℂ) + ((-5038082 / 166515 : ℝ) : ℂ) * I,
      ((2573111801 / 62443125 : ℝ) : ℂ) + ((-55520602 / 12488625 : ℝ) : ℂ) * I]
  obtain ⟨r0, hchar, hr0⟩ := hopfWitness.exists_charpoly_factor_of_hopfAt hopfWitness_hopfAt
  obtain ⟨hA, h2⟩ := Dynamics.CenterManifold.isUnit_det_of_charpoly one_ne_zero hchar hr0
  have hr : jacobianC hopfWitness.field 0 *ᵥ r
      = bilinC hopfWitness.field 0 hopfWitnessQ (star hopfWitnessQ) := by
    rw [hopfWitness_jacobianC, hopfWitness_bilinC]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_five, hopfWitnessQ, r,
        Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num
  have hs : shift2 (jacobianC hopfWitness.field 0) 1 *ᵥ s
      = bilinC hopfWitness.field 0 hopfWitnessQ hopfWitnessQ := by
    rw [hopfWitness_jacobianC, hopfWitness_bilinC, shift2]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_five, hopfWitnessQ, s,
        Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals norm_num
  rw [firstLyapunov_eq_of_solve hA h2 hr hs, hopfWitness_trilinC, hopfWitness_bilinC,
      hopfWitness_bilinC]
  simp [pairing_apply, Fin.sum_univ_five, hopfWitnessP, hopfWitnessQ, r, s, Complex.mul_re,
      Complex.mul_im,
    -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
    -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
  norm_num

/-! ## Connection conclusions at the witnesses -/

/-- **A supercritical Hopf point of the VSM with power filter on the line**: `hopfWitnessSup`
(balanced, physical, `(s² + 1)(s³ + 12 s² + 42 s + 50)`) has `ℓ₁ = −14341/14450 < 0` and is
locally asymptotically stable, although its linearization has the eigenvalues `±i`
(`mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg`). -/
@[tmio TM, powerlib_domain] theorem hopfWitnessSup_mem_den_locallyAsymptoticallyStable :
    connection% (hopfWitnessSup ∈ family.den (.flow .locallyAsymptoticallyStable)) :=
  mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg _ hopfWitnessSup_hopfAt
    hopfWitnessSup_isCriticalPair (by rw [hopfWitnessSup_firstLyapunov]; norm_num)

/-- **A subcritical Hopf point of the VSM with power filter on the line**: `hopfWitness`
(balanced, physical, the roots `±i` and a Hurwitz cubic) has `ℓ₁ > 0` and is unstable
(`mem_den_unstable_of_firstLyapunov_pos`). -/
@[tmio TM, powerlib_domain] theorem hopfWitness_mem_den_unstable :
    connection% (hopfWitness ∈ family.den (.flow .unstable)) :=
  mem_den_unstable_of_firstLyapunov_pos _ hopfWitness_hopfAt hopfWitness_isCriticalPair
    (by rw [hopfWitness_firstLyapunov]; norm_num)

@[tmio M, powerlib_domain] private theorem hopfWitness_not_routhViolation :
    ¬ hopfWitness.RouthViolation := by
  obtain ⟨h4, h3, h2, h1, h0⟩ := hopfWitness_coeffs
  rw [Model.RouthViolation, h4, h3, h2, h1, h0]
  norm_num [Criteria.quinticHurwitzDet4, Criteria.quinticHurwitzDet3, Criteria.quinticHurwitzDet2]

@[tmio M, powerlib_domain] private theorem hopfWitnessSup_not_routh :
    ¬ hopfWitnessSup.Routh := by
  obtain ⟨h4, h3, h2, h1, h0⟩ := hopfWitnessSup_coeffs
  rw [Model.Routh, h4, h3, h2, h1, h0]
  norm_num [Criteria.quinticHurwitzDet5, Criteria.quinticHurwitzDet4, Criteria.quinticHurwitzDet3,
    Criteria.quinticHurwitzDet2]

/-- **The instability translation is not exact within physical models**: it asks for a strict
violation of the quintic Routh–Hurwitz conditions, but the subcritical witness lies on the
boundary (`Δ₄ = 0`) and is unstable (`hopfWitness_mem_den_unstable`). -/
@[tmio TM, powerlib_domain] theorem not_exactUnder_unstable :
    connection% (¬ family.ExactUnder {.physical} (.flow .unstable)) := by
  have hmem := hopfWitness_mem_den_unstable
  unfold powerlib.TMIO.Statement at hmem ⊢
  refine Spectral.not_exactUnder_of_witness ?_ hmem (q := .destabilizing) ?_ ?_
  · rw [(connection_proof% TMIO.mem_realize)]
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact hopfWitness_physical
  · simp [family, translate, Spectral.localTable, Spectral.table]
  · exact hopfWitness_not_routhViolation

/-- **The local asymptotic translation is not exact within physical models**: it asks for the
strict quintic Routh–Hurwitz conditions, but the supercritical witness lies on the boundary and
is locally asymptotically stable (`hopfWitnessSup_mem_den_locallyAsymptoticallyStable`). -/
@[tmio TM, powerlib_domain] theorem not_exactUnder_locallyAsymptoticallyStable :
    connection% (¬ family.ExactUnder {.physical} (.flow .locallyAsymptoticallyStable)) := by
  have hmem := hopfWitnessSup_mem_den_locallyAsymptoticallyStable
  unfold powerlib.TMIO.Statement at hmem ⊢
  refine Spectral.not_exactUnder_of_witness ?_ hmem (q := .routh) ?_ ?_
  · rw [(connection_proof% TMIO.mem_realize)]
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact hopfWitnessSup_physical
  · simp [family, translate, Spectral.localTable, Spectral.table]
  · exact hopfWitnessSup_not_routh

end VSMLPF
end powerlib.GFM.Line
