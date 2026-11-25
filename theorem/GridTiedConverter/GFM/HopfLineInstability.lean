import theorem.GridTiedConverter.GFM.HopfCoefficientLine
import theorem.Dynamics.HopfDichotomy

/-! # Hopf points of the VSM on a dynamic R–L line: `ℓ₁ > 0` unstable, `ℓ₁ < 0` stable

Model boundary.
* The four-state VSM `Line.VSM` of `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged:
  state `(δ, ω, i_d, i_q) : State 4`, grid dq frame at `ω₀`, export-positive power, constant `E`,
  `M ω̇ = P_ref − P_e − D ω`, `L i̇ = E e^{jδ} − V − (R + jX) i`; no power filter, voltage loop,
  inner loops, PLL, delay or PWM. Read about a selected angle (`Line.VSM.Model`), the field
  translated so that the operating point is the origin.
* Parameter range: the Hopf boundary of the monic characteristic quartic
  `s⁴ + a₃ s³ + a₂ s² + a₁ s + a₀` at the operating point (`Line.VSM.coeff3` … `coeff0`):
  `a₃, a₁, a₀ > 0` and `a₃ a₂ a₁ = a₁² + a₃² a₀`, where it factors as
  `(s² + a₁/a₃)(s² + a₃ s + a₀ a₃/a₁)`: eigenvalues `±iω`, `ω² = a₁/a₃`, and a stable pair. The
  operating point is an equilibrium (a balanced angle) with a critical pair `(q, p)` of the field
  there (`NormalForm.LyapunovCoefficient.IsCriticalPair`), and `ℓ₁` is Kuznetsov's first Lyapunov
  coefficient `firstLyapunov` of the model field with that pair.
* Level: Lyapunov instability and local asymptotic stability (LeanForControl's `Unstable`,
  `LocalAsymptoticStable`) of the operating point. The bifurcating cycles (the transversality
  coefficients along the damping and the inverse inertia at every boundary point, never both
  zero, and the cycles of `Dynamics.HopfCycle.exists_hopfCycle` at every boundary point with
  `ℓ₁ ≠ 0`, private evidence) are `theorem/GridTiedConverter/GFM/LineVSMHopfCycle.lean`. Not
  stated: uniqueness and orbital stability of the cycles, the degenerate points `ℓ₁ = 0`
  (`theorem/GridTiedConverter/GFM/HopfBautinLine.lean`, `HopfBautinPoint.lean`). The
  `ε = 1/ω_b` law of the source note — on every line of time scale `ε < ε₀` the Hopf boundary is
  nonempty and every boundary point is unstable if `(X² − R²)(5K² − P''²) > 0`, locally
  asymptotically stable if it is negative — is `theorem/GridTiedConverter/GFM/HopfLineScale.lean`
  (`Line.VSM.Model.atScale_mem_den_unstable`,
  `Line.VSM.Model.atScale_mem_den_locallyAsymptoticallyStable`), through the family laws below.

Source: study note `gfm/t3-bifurcation/REPORT-coord.md` (c, "Subcritical EXISTS: VSM without
filter on dynamic RL line"); Carr, *Applications of Centre Manifold Theory* (1981), §2.4 (the
reduction principle); Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.5 and §5.4
(the projection formula). The generic laws are `theorem/Dynamics/HopfDichotomy.lean` (the
dichotomy of a Hopf point from the factorized characteristic polynomial, analytic fields),
`theorem/Dynamics/CenterReduction.lean` and `theorem/Dynamics/CenterReductionStability.lean`
(centre-manifold reduction).

Results.
* `Line.VSM.Model.analyticAt_field` (the field is analytic: `sin`, `cos` and polynomials, so its
  second and third derivatives at the operating point are symmetric and give the cubic Taylor
  expansion), `Line.VSM.Model.charpoly_eq_of_boundary` (the factorization on the boundary,
  through `Line.VSM.Model.jacobianC_field` of
  `theorem/GridTiedConverter/GFM/HopfCoefficientLine.lean`),
  `Line.VSM.Model.sq_freq_of_isCriticalPair` (a critical pair has `ω² = a₁/a₃`),
  `Line.VSM.Model.exists_charpoly_factor_of_boundary` (at `ω² = a₁/a₃` the characteristic
  polynomial is `(s² + ω²) r(s)` with `r` Hurwitz).
* `ℓ₁` is a property of the model: `Line.VSM.Model.exists_isCriticalPair_of_boundary` (every
  balanced physical boundary model has a critical pair, at `ω = √(a₁/a₃)`),
  `Line.VSM.Model.sign_firstLyapunov_eq_of_boundary` (all critical pairs give the same sign).

Family and connection conclusions.
No new family: connection conclusions on `Line.VSM.family`.
* `Line.VSM.mem_den_unstable_of_firstLyapunov_pos`: every model on the Hopf boundary of the
  quartic (`a₃, a₁, a₀ > 0`) with a critical pair whose `ℓ₁` is positive is unstable — the
  subcritical Hopf points of the family (centre-manifold reduction,
  `Dynamics.CenterManifold.unstable_of_firstLyapunov_pos_of_charpoly`).
* `Line.VSM.mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg`: with `ℓ₁ < 0` instead the
  model is locally asymptotically stable — the supercritical Hopf points
  (`Dynamics.CenterManifold.localAsymptoticStable_of_firstLyapunov_neg_of_charpoly`).
* `Line.VSM.hopfWitness_mem_den_unstable`: the witness `Line.VSM.hopfWitness` (`E = V = 1`,
  `R = 1/5`, `L = 1/10`, `ω₀ = 5`, `M = 7/4`, `D = 1/4`, `P_ref = 0`, `δ* = 0`;
  `ℓ₁ = 1478182/156873665`, `Line.VSM.hopfWitness_firstLyapunov`) is unstable: a subcritical Hopf
  point of a balanced physical model, where the linearization (eigenvalues `±i` and a stable pair)
  decides nothing.
* `Line.VSM.not_exactUnder_unstable`: the instability translation of `Line.VSM.family` (a strict
  violation of the quartic Routh conditions, `Line.VSM.mem_den_unstable`) is **not** exact within
  physical models: the witness lies on the Routh boundary (`a₃ a₂ a₁ = a₁² + a₃² a₀`) and is
  unstable.
* `Line.VSM.hopfWitnessSup_mem_den_locallyAsymptoticallyStable`: the boundary point
  `Line.VSM.hopfWitnessSup` (`E = V = 1`, `R = L = 1/5`, `ω₀ = 1`, `M = 1`, `D = 2`, `P_ref = 0`,
  `δ* = 0`; `ℓ₁ = −73/416`, `Line.VSM.hopfWitnessSup_firstLyapunov`) is locally asymptotically
  stable: a supercritical Hopf point of a balanced physical model.
* `Line.VSM.not_exactUnder_locallyAsymptoticallyStable`: the local asymptotic translation (the
  strict quartic Routh conditions) is **not** exact within physical models: the supercritical
  witness lies on the Routh boundary and is locally asymptotically stable.
-/

noncomputable section
namespace powerlib.GFM.Line
namespace VSM
open Complex Polynomial
open powerlib.Dynamics (State)
open powerlib.NormalForm.LyapunovCoefficient

/-! ## The field at a Hopf point of the quartic -/

/-- The model field is analytic at the operating point (`sin`, `cos` and polynomials). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.analyticAt_field (m : Model) :
    AnalyticAt ℝ m.field 0 := by
  have h : ContDiff ℝ (⊤ : WithTop ℕ∞) m.field :=
    (m.g.contDiff_field (k := ⊤)).comp (contDiff_id.add contDiff_const)
  exact h.contDiffAt.analyticAt

/-- **The quartic factors on its Hopf boundary**: if `a₃ a₂ a₁ = a₁² + a₃² a₀` (`a₃, a₁ ≠ 0`),
`det(sI − J) = (s² + a₁/a₃)(s² + a₃ s + a₀ a₃/a₁)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.charpoly_eq_of_boundary (m : Model)
    (h3 : m.g.coeff3 ≠ 0) (h1 : m.g.coeff1 m.Q ≠ 0)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q) :
    (jacobianC m.field 0).charpoly =
      (X ^ 2 + C (((m.g.coeff1 m.Q / m.g.coeff3 : ℝ)) : ℂ)) *
        (X ^ 2 + C (m.g.coeff3 : ℂ) * X +
          C (((m.g.coeff0 m.Q * m.g.coeff3 / m.g.coeff1 m.Q : ℝ)) : ℂ)) := by
  refine Polynomial.funext fun s => ?_
  rw [m.jacobianC_field, ← Linear.det_characteristicMatrix_eq_eval, m.det_characteristicMatrix]
  set a3 := m.g.coeff3
  set a2 := m.g.coeff2 m.Q
  set a1 := m.g.coeff1 m.Q
  set a0 := m.g.coeff0 m.Q
  have key : a2 = a0 * a3 / a1 + a1 / a3 := by
    field_simp
    linear_combination hH
  have hk : (a2 : ℂ) = ((a0 * a3 / a1 + a1 / a3 : ℝ) : ℂ) := by rw [key]
  have h3' : (a3 : ℂ) ≠ 0 := by exact_mod_cast h3
  have h1' : (a1 : ℂ) ≠ 0 := by exact_mod_cast h1
  simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C]
  rw [hk]
  push_cast
  field_simp
  ring

/-- **The frequency of a critical pair**: `iω` is a root of the quartic, so its imaginary part
`ω (a₁ − a₃ ω²)` vanishes and `ω² = a₁/a₃`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.sq_freq_of_isCriticalPair (m : Model)
    (h3 : m.g.coeff3 ≠ 0) {ω : ℝ} {q p : Fin 4 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p) :
    ω ^ 2 = m.g.coeff1 m.Q / m.g.coeff3 := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    have h := hcp.normalized
    simp at h
  have hdet := (Linear.det_characteristicMatrix_eq_zero_iff_exists_eigenpair m.jac
    ((ω : ℂ) * I)).mpr ⟨q, hq0, by rw [← m.jacobianC_field]; exact hcp.right⟩
  rw [m.det_characteristicMatrix] at hdet
  have him := congrArg Complex.im hdet
  simp [pow_succ, Complex.mul_im, Complex.mul_re] at him
  have hω := hcp.freq_pos
  field_simp
  nlinarith [him]

/-- On the Hopf boundary, at a frequency with `ω² = a₁/a₃`, the characteristic polynomial is
`(s² + ω²) r(s)` with `r(s) = s² + a₃ s + a₀ a₃/a₁` Hurwitz. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.exists_charpoly_factor_of_boundary (m : Model)
    (h3 : 0 < m.g.coeff3)
    (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q)
    {ω : ℝ} (hω2 : ω ^ 2 = m.g.coeff1 m.Q / m.g.coeff3) :
    ∃ r : ℂ[X], (jacobianC m.field 0).charpoly = (X ^ 2 + C ((ω : ℂ) ^ 2)) * r ∧
      ∀ s : ℂ, r.eval s = 0 → s.re < 0 := by
  have hchar := m.charpoly_eq_of_boundary h3.ne' h1.ne' hH
  rw [← hω2, Complex.ofReal_pow] at hchar
  refine ⟨_, hchar, fun s hs => ?_⟩
  exact (Criteria.quadratic_roots_re_neg_iff m.g.coeff3
    (m.g.coeff0 m.Q * m.g.coeff3 / m.g.coeff1 m.Q)).mpr ⟨h3, by positivity⟩ s (by simpa using hs)

/-- **`ℓ₁` is defined at every boundary point**: a balanced physical model on the Hopf boundary
(`a₁, a₀ > 0`, `a₃ a₂ a₁ = a₁² + a₃² a₀`) has a critical pair at the frequency
`ω = √(a₁/a₃)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.exists_isCriticalPair_of_boundary (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (h1 : 0 < m.g.coeff1 m.Q)
    (h0 : 0 < m.g.coeff0 m.Q)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q) :
    ∃ q p : Fin 4 → ℂ,
      IsCriticalPair m.field 0 (Real.sqrt (m.g.coeff1 m.Q / m.g.coeff3)) q p := by
  obtain ⟨hN, hM, hD⟩ := hp
  have h3 : 0 < m.g.coeff3 := by
    have : 0 ≤ m.g.σ := div_nonneg hN.R hN.L.le
    unfold coeff3; positivity
  set ω := Real.sqrt (m.g.coeff1 m.Q / m.g.coeff3) with hω
  have hω0 : 0 < ω := Real.sqrt_pos.mpr (div_pos h1 h3)
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_boundary h3 h1 h0 hH
    (Real.sq_sqrt (div_pos h1 h3).le)
  obtain ⟨q, p, hc⟩ := Dynamics.CenterManifold.exists_isCritical_of_charpoly hω0 hchar hr
  have heq : m.field 0 = 0 := by
    have h := (m.field_point_eq_zero_iff hM.ne' hN.L.ne' hN.absSq_pos.ne').mpr hb
    simpa [Model.field] using h
  exact ⟨q, p, heq, hω0, hc.right, hc.left, hc.normalized⟩

/-- **The sign of `ℓ₁` is a property of the model**: on the Hopf boundary (`a₃, a₁, a₀ > 0`) all
critical pairs of the model field at the operating point give first Lyapunov coefficients of the
same sign. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.sign_firstLyapunov_eq_of_boundary (m : Model)
    (h3 : 0 < m.g.coeff3) (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q)
    {ω : ℝ} {q p q' p' : Fin 4 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p)
    (hcp' : IsCriticalPair m.field 0 ω q' p') :
    SignType.sign (firstLyapunov m.field 0 ω q' p') =
      SignType.sign (firstLyapunov m.field 0 ω q p) := by
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_boundary h3 h1 h0 hH
    (m.sq_freq_of_isCriticalPair h3.ne' hcp)
  exact Dynamics.CenterManifold.sign_firstLyapunov_eq_of_charpoly hchar hr hcp hcp'

/-! ## Connection conclusions -/

/-- **Subcritical Hopf points are unstable**: a model on the Hopf boundary of the quartic
(`a₃, a₁, a₀ > 0`, `a₃ a₂ a₁ = a₁² + a₃² a₀`) with a critical pair `(q, p)` of its field at the
operating point and `ℓ₁ = firstLyapunov > 0` is unstable (centre-manifold reduction:
`Dynamics.CenterManifold.unstable_of_firstLyapunov_pos_of_charpoly`, the stable factor
`s² + a₃ s + a₀ a₃/a₁` Hurwitz by `Criteria.quadratic_roots_re_neg_iff`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_firstLyapunov_pos (m : Model)
    (h3 : 0 < m.g.coeff3) (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q)
    {ω : ℝ} {q p : Fin 4 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p)
    (hl : 0 < firstLyapunov m.field 0 ω q p) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Unstable m.field 0
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_boundary h3 h1 h0 hH
    (m.sq_freq_of_isCriticalPair h3.ne' hcp)
  exact Dynamics.CenterManifold.unstable_of_firstLyapunov_pos_of_charpoly m.contDiff_field
    m.analyticAt_field hcp hchar hr hl

/-- **Supercritical Hopf points are locally asymptotically stable**: a model on the Hopf boundary
of the quartic (`a₃, a₁, a₀ > 0`, `a₃ a₂ a₁ = a₁² + a₃² a₀`) with a critical pair `(q, p)` of its
field at the operating point and `ℓ₁ = firstLyapunov < 0` is locally asymptotically stable
(centre-manifold reduction,
`Dynamics.CenterManifold.localAsymptoticStable_of_firstLyapunov_neg_of_charpoly`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg
    (m : Model) (h3 : 0 < m.g.coeff3) (h1 : 0 < m.g.coeff1 m.Q) (h0 : 0 < m.g.coeff0 m.Q)
    (hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q)
    {ω : ℝ} {q p : Fin 4 → ℂ} (hcp : IsCriticalPair m.field 0 ω q p)
    (hl : firstLyapunov m.field 0 ω q p < 0) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change LocalAsymptoticStable m.field 0
  obtain ⟨r, hchar, hr⟩ := m.exists_charpoly_factor_of_boundary h3 h1 h0 hH
    (m.sq_freq_of_isCriticalPair h3.ne' hcp)
  exact Dynamics.CenterManifold.localAsymptoticStable_of_firstLyapunov_neg_of_charpoly
    m.contDiff_field m.analyticAt_field hcp hchar hr hl

/-- The coefficients of the quartic at the witness: `a₃ = 29/7`, `a₂ = 207/7`, `a₁ = 29/7`,
`a₀ = 200/7`. Static evidence on the model. -/
@[tmio M, powerlib_domain] private theorem hopfWitness_coeffs :
    hopfWitness.g.coeff3 = 29 / 7 ∧ hopfWitness.g.coeff2 hopfWitness.Q = 207 / 7 ∧
      hopfWitness.g.coeff1 hopfWitness.Q = 29 / 7 ∧
      hopfWitness.g.coeff0 hopfWitness.Q = 200 / 7 := by
  have hQ : hopfWitness.Q = 0 := by
    norm_num [Model.Q, Network.qssReactive, hopfWitness, Network.is, Network.reactive_eq]
  rw [hQ]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [coeff3, coeff2, coeff1, coeff0, hopfWitness, Network.ρ, Network.σ, Network.X]

/-- **The subcritical Hopf witness is unstable**: the witness (`E = V = 1`, `R = 1/5`,
`L = 1/10`, `ω₀ = 5`, `M = 7/4`, `D = 1/4`, `P_ref = 0`) lies on the Hopf boundary
(`(s² + 1)(s² + 29s/7 + 200/7)`), and its first Lyapunov coefficient
`ℓ₁ = 1478182/156873665` is positive (`mem_den_unstable_of_firstLyapunov_pos`). -/
@[tmio TM, powerlib_domain] theorem hopfWitness_mem_den_unstable :
    connection% (hopfWitness ∈ family.den (.flow .unstable)) := by
  obtain ⟨h3, h2, h1, h0⟩ := hopfWitness_coeffs
  refine mem_den_unstable_of_firstLyapunov_pos hopfWitness (by rw [h3]; norm_num)
    (by rw [h1]; norm_num) (by rw [h0]; norm_num) (by rw [h3, h2, h1, h0]; norm_num)
    hopfWitness_isCriticalPair hopfWitness_firstLyapunov_pos

@[tmio M, powerlib_domain] private theorem hopfWitness_not_routhViolation :
    ¬ hopfWitness.RouthViolation := by
  obtain ⟨h3, h2, h1, h0⟩ := hopfWitness_coeffs
  rw [Model.RouthViolation, h3, h2, h1, h0]
  norm_num

/-- **The instability translation is not exact within physical models**: it asks for a strict
violation of the quartic Routh conditions, but the witness lies on the Routh boundary
(`a₃ a₂ a₁ = a₁² + a₃² a₀`) and is unstable (`hopfWitness_mem_den_unstable`). -/
@[tmio TM, powerlib_domain] theorem not_exactUnder_unstable :
    connection% (¬ family.ExactUnder {.physical} (.flow .unstable)) := by
  have hmem := hopfWitness_mem_den_unstable
  unfold powerlib.TMIO.Statement at hmem ⊢
  refine Spectral.not_exactUnder_of_witness ?_ hmem (q := .destabilizing) ?_ ?_
  · rw [(connection_proof% TMIO.mem_realize)]
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact hopfWitness_meets.2
  · simp [family, translate, Spectral.localTable, Spectral.table]
  · exact hopfWitness_not_routhViolation


/-- **The supercritical Hopf witness is locally asymptotically stable**: the boundary point
`hopfWitnessSup` (`E = V = 1`, `R = L = 1/5`, `ω₀ = 1`, `M = 1`, `D = 2`, `P_ref = 0`;
`(s² + 1)(s² + 4s + 5)`) has `ℓ₁ = −73/416 < 0`
(`mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg`). -/
@[tmio TM, powerlib_domain] theorem hopfWitnessSup_mem_den_locallyAsymptoticallyStable :
    connection% (hopfWitnessSup ∈ family.den (.flow .locallyAsymptoticallyStable)) := by
  obtain ⟨h3, h2, h1, h0⟩ := hopfWitnessSup_coeffs
  refine mem_den_locallyAsymptoticallyStable_of_firstLyapunov_neg hopfWitnessSup
    (by rw [h3]; norm_num) (by rw [h1]; norm_num) (by rw [h0]; norm_num)
    (by rw [h3, h2, h1, h0]; norm_num) hopfWitnessSup_isCriticalPair
    hopfWitnessSup_firstLyapunov_neg

@[tmio M, powerlib_domain] private theorem hopfWitnessSup_not_routh :
    ¬ hopfWitnessSup.Routh := by
  obtain ⟨h3, h2, h1, h0⟩ := hopfWitnessSup_coeffs
  rw [Model.Routh, h3, h2, h1, h0]
  norm_num

/-- **The local asymptotic translation is not exact within physical models**: it asks for the
strict quartic Routh conditions, but the supercritical witness lies on the Routh boundary
(`a₃ a₂ a₁ = a₁² + a₃² a₀`) and is locally asymptotically stable
(`hopfWitnessSup_mem_den_locallyAsymptoticallyStable`). -/
@[tmio TM, powerlib_domain] theorem not_exactUnder_locallyAsymptoticallyStable :
    connection% (¬ family.ExactUnder {.physical} (.flow .locallyAsymptoticallyStable)) := by
  have hmem := hopfWitnessSup_mem_den_locallyAsymptoticallyStable
  unfold powerlib.TMIO.Statement at hmem ⊢
  refine Spectral.not_exactUnder_of_witness ?_ hmem (q := .routh) ?_ ?_
  · rw [(connection_proof% TMIO.mem_realize)]
    intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact hopfWitnessSup_meets.2
  · simp [family, translate, Spectral.localTable, Spectral.table]
  · exact hopfWitnessSup_not_routh

end VSM
end powerlib.GFM.Line
