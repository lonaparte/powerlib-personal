import theorem.GridTiedConverter.GFM.HopfLyapunovCurrent
import theorem.GridTiedConverter.GFM.BTCoefficientLine
import theorem.Dynamics.SaddleNodeReduction

/-! # Complete local asymptotic membership of the VSM on a dynamic R–L line

Model boundary.
* The four-state VSM `Line.VSM` of `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged:
  state `(δ, ω, i_d, i_q) : State 4`, grid dq frame at `ω₀`, export-positive power, constant `E`,
  `M ω̇ = P_ref − P_e − D ω`, `L i̇ = E e^{jδ} − V − (R + jX) i`; no power filter, voltage loop,
  inner loops, PLL, delay or PWM. Read about a selected angle (`Line.VSM.Model`), translated so
  that the operating point `(δ*, 0, i_s(δ*))` is the origin.
* Every physical model (`Network.Physical`, `M, D > 0`), every operating angle, balanced or not.
  The degenerate set (`Line.VSM.Model.Degenerate`): the balanced zero–Hopf fold points `K = 0`,
  `a₃ a₂ = a₁` (the cubic cofactor has a pair `±i√a₂`, or the triple zero `a₁ = a₂ = 0`) and the
  Bautin-type points of the Hopf boundary (`a₃ a₂ a₁ = a₁² + a₃² a₀`, `a₁, a₀ > 0`, `𝔅_δ = 0`,
  `Line.VSM.bautinFormAngle`); it is excluded, not decided. The Bogdanov–Takens fold points
  (`a₁ = 0`, i.e. `D = D_line`, with `a₂ ≠ 0`) are decided and are not in it.
* Level: local asymptotic stability and instability (LeanForControl's `LocalAsymptoticStable`,
  `Unstable`) of the operating point, through `Line.VSM.family`.

Source: the closure of the quartic Routh region (the boundary of the stable coefficients of a
monic quartic with `a₃ > 0` is `a₀ = 0` or the Hopf boundary `a₃ a₂ a₁ = a₁² + a₃² a₀`,
`a₁, a₀ > 0`); the Hopf laws of `theorem/GridTiedConverter/GFM/HopfLyapunovCurrent.lean`; the
saddle-node law `Dynamics.CenterManifold.unstable_of_foldCoeff_ne_zero_of_charpoly`
(`theorem/Dynamics/SaddleNodeReduction.lean`; Kuznetsov, *Elements of Applied Bifurcation
Theory* (3rd ed.), §3.2 and §5.4, the fold coefficient `a = ½⟨p, B(q, q)⟩`); the tangent and the
second derivative of `theorem/GridTiedConverter/GFM/BifurcationLine.lean`
(`Line.VSM.Model.tangent`) and `theorem/GridTiedConverter/GFM/BTCoefficientLine.lean`
(`Line.VSM.fderiv_fderiv_field`); the pattern of the rate-coupled GFL PLL
(`GFL.RatePLL.mem_den_locallyAsymptoticallyStable_iff`,
`theorem/GridTiedConverter/GFL/RatePLLHopf.lean`); the Bogdanov–Takens law
`Line.VSM.mem_den_unstable_of_bt` (`theorem/GridTiedConverter/GFM/BTCoefficientLine.lean`,
`theorem/Dynamics/BTInstability.lean`). The left null vector and the fold coefficient
were derived with exact computer algebra (SymPy, untrusted) and are proved here by
`linear_combination`.

Results.
* The fold location `Line.VSM.Model.det_jac_eq_zero_iff`: the Jacobian at the operating point is
  singular (a zero eigenvalue) exactly at `K = 0` (`det J = ρ K/M`); with
  `Line.VSM.Model.two_le_rootMultiplicity_zero_iff`
  (`theorem/GridTiedConverter/GFM/BifurcationLine.lean`) the zero eigenvalue is simple off the
  Bogdanov–Takens damping `D = D_line`.
* The fold data: at `K = 0`, `D ≠ D_line` the tangent `q = (1, 0, i_s'(δ*))` and
  `p = (D, M, E L (X sin δ* − R cos δ*)/|Z|², −E L (X cos δ* + R sin δ*)/|Z|²)/(D − D_line)`
  (`Line.VSM.Model.foldP`) are a normalised null pair (`Line.VSM.Model.isNullPair_fold`); the fold
  coefficient is `a = (P(δ*) − c₀)/(2 (D − D_line))`, `c₀ = E² R/|Z|²`
  (`Line.VSM.Model.foldCoeff_fold`), with `P(δ*) − c₀ = ± A ≠ 0` at a fold, so `a ≠ 0` off
  `D = D_line`; `det(sI − J) = s (s³ + a₃ s² + a₂ s + a₁)` (`Line.VSM.Model.charpoly_fold`).
* `Line.VSM.Model.Degenerate`: the degenerate balanced points still undecided (the zero–Hopf
  fold points and the Bautin-type points).

Family and connection conclusions.
No new family: connection conclusions on `Line.VSM.family`.
* **`Line.VSM.mem_den_unstable_of_fold`** (the fold is a saddle-node): a balanced physical model
  at `K = 0` with `0 < a₁ < a₃ a₂` is unstable.
* **`Line.VSM.mem_den_unstable_of_fold_of_ne`** (the fold decided): a balanced physical model at
  `K = 0` with `a₁ ≠ 0` and `a₃ a₂ ≠ a₁` is unstable (a strict Routh violation, or the
  saddle-node law).
* **`Line.VSM.mem_den_unstable_of_fold_of_ne_zeroHopf`** (the fold decided off the zero–Hopf
  points): a balanced physical model at `K = 0` with `a₃ a₂ ≠ a₁` is unstable (the saddle-node
  law off `D = D_line`; at it a strict Routh violation `a₂ < 0` or the Bogdanov–Takens cusp
  `Line.VSM.mem_den_unstable_of_bt`).
* **`Line.VSM.mem_den_locallyAsymptoticallyStable_iff`**, **`Line.VSM.mem_den_lyapunovStable_iff`**
  (complete membership off the degenerate set): a physical model is locally asymptotically
  stable, equivalently Lyapunov stable, iff it is balanced and either meets the strict quartic
  Routh conditions or lies on the Hopf boundary with `a₁, a₀ > 0` and
  `𝔅_δ(D/M, R/L, ω₀, Q/M, t) > 0`. The excluded cases are unstable: not balanced (the operating
  point is not an equilibrium), a strict Routh violation (`Line.VSM.mem_den_unstable`), the fold
  off the zero–Hopf points (`Line.VSM.mem_den_unstable_of_fold_of_ne_zeroHopf`), the Hopf
  boundary with `𝔅_δ < 0` (`Line.VSM.mem_den_unstable_of_bautinFormAngle_neg`). The zero–Hopf
  points are decided in `theorem/GridTiedConverter/GFM/LineVSMZeroHopf.lean`; the membership with
  only the Bautin-type points and the triple zero left is
  `theorem/GridTiedConverter/GFM/LineVSMMembership.lean`.
-/

noncomputable section
namespace powerlib.GFM.Line
namespace VSM

/-- **The fold location**: for `M, L ≠ 0` and `|Z|² > 0` the Jacobian at the operating point is
singular, a zero eigenvalue, exactly at the fold `K = 0` (product rule `Line.VSM.Model.det_jac`:
`det J = (K/M) ρ`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.det_jac_eq_zero_iff (m : Model) (hM : m.g.M ≠ 0)
    (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) : m.jac.det = 0 ↔ m.K = 0 := by
  have hρ : m.g.ρ ≠ 0 := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
    rw [this]; exact div_ne_zero hZ.ne' (pow_ne_zero 2 hL)
  rw [m.det_jac hL hZ, Synchronous.SwingParams.det_jacobian, Network.det_lineJacobian,
    show m.g.swingParams.syncCoeff m.δ = m.K from rfl, show m.g.swingParams.M = m.g.M from rfl]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases div_eq_zero_iff.mp h with h | h
      · exact h
      · exact absurd h hM
    · exact absurd h hρ
  · intro h
    rw [h, zero_div, zero_mul]

/-! ## The fold: a saddle-node point -/

section Fold

open Polynomial Matrix
open scoped RealInnerProductSpace
open powerlib.NormalForm.LyapunovCoefficient (jacobianC)
open powerlib.NormalForm.BogdanovTakens (IsNullPair foldCoeff isNullPair_toEuclideanCLM_iff)

/-- The left null vector of the Jacobian at a fold, normalised against the tangent
`Line.VSM.Model.tangent` by `D − D_line`:
`p = (D, M, E L (X sin δ* − R cos δ*)/|Z|², −E L (X cos δ* + R sin δ*)/|Z|²)/(D − D_line)`. -/
def Model.foldP (m : Model) : Fin 4 → ℝ :=
  (m.g.D - m.g.Dline)⁻¹ • ![m.g.D, m.g.M,
    m.g.E * m.g.L * (m.g.X * Real.sin m.δ - m.g.R * Real.cos m.δ) / m.g.absSq,
    -(m.g.E * m.g.L * (m.g.X * Real.cos m.δ + m.g.R * Real.sin m.δ) / m.g.absSq)]

@[tmio M, powerlib_domain] private theorem fold_fderiv (m : Model) :
    fderiv ℝ m.field 0 = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) m.jac := by
  rw [show m.field = fun z => m.g.field (z + m.point) from rfl, fderiv_comp_add_right,
    zero_add, m.fderiv_point]

@[tmio M, powerlib_domain] private theorem fold_fderiv2 (m : Model) :
    fderiv ℝ (fderiv ℝ m.field) 0 = fderiv ℝ (fderiv ℝ m.g.field) m.point := by
  have h : fderiv ℝ m.field = fun z => fderiv ℝ m.g.field (z + m.point) := by
    funext z
    show fderiv ℝ (fun z => m.g.field (z + m.point)) z = _
    rw [fderiv_comp_add_right]
  rw [h, fderiv_comp_add_right, zero_add]

/-- **The null pair of a fold**: at a physical model with `K = 0` and `D ≠ D_line`, the tangent
`q = (1, 0, i_s'(δ*))` (`Line.VSM.Model.tangent`) and `p = Line.VSM.Model.foldP` are a
normalised null pair of the Jacobian at the operating point (`J q = 0`, `pᵀ J = 0`,
`⟨p, q⟩ = 1`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.isNullPair_fold {m : Model} (hp : Meets m .physical)
    (hK : m.K = 0) (hD : m.g.D ≠ m.g.Dline) :
    IsNullPair (fderiv ℝ m.field 0) (WithLp.toLp 2 m.tangent) (WithLp.toLp 2 m.foldP) := by
  obtain ⟨hN, hM, -⟩ := hp
  have hL := hN.L.ne'
  have hZ := hN.absSq_pos
  have hQ : m.Q = m.g.E ^ 2 * m.g.X / m.g.absSq := by
    have h := m.g.syncCoeff_add_qssReactive hZ m.δ
    rw [show m.g.syncCoeff m.δ = m.K from rfl, hK, zero_add] at h
    rw [Model.Q, h, Network.κ]
  have hX : m.g.X = m.g.ω0 * m.g.L := rfl
  have hcs := Real.cos_sq_add_sin_sq m.δ
  have hDD : m.g.D - m.g.Dline ≠ 0 := sub_ne_zero.mpr hD
  have hA : m.g.absSq = m.g.R ^ 2 + (m.g.ω0 * m.g.L) ^ 2 := by rw [Network.absSq, hX]
  have hZ' : m.g.R ^ 2 + (m.g.ω0 * m.g.L) ^ 2 ≠ 0 := hA ▸ hZ.ne'
  have hM' := hM.ne'
  have hZ1 : m.g.R ^ 2 + m.g.ω0 ^ 2 * m.g.L ^ 2 ≠ 0 := by rw [← mul_pow]; exact hZ'
  have hZ2 : m.g.R ^ 2 + m.g.L ^ 2 * m.g.ω0 ^ 2 ≠ 0 := by rw [← mul_pow, mul_comm]; exact hZ'
  have hDl : m.g.Dline * (m.g.R ^ 2 + m.g.L ^ 2 * m.g.ω0 ^ 2) ^ 2 =
      2 * m.g.E ^ 2 * m.g.R * m.g.ω0 * m.g.L ^ 2 := by
    rw [Network.Dline, hA, hX]; field_simp
  have ha : m.g.E ^ 2 * (m.g.ω0 * m.g.L) * (Real.cos m.δ ^ 2 + Real.sin m.δ ^ 2 - 1) = 0 := by
    rw [hcs, sub_self, mul_zero]
  rw [fold_fderiv, isNullPair_toEuclideanCLM_iff, m.jac_eq hL]
  refine ⟨?_, ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Model.tangent, hQ, hX] <;>
      rw [hA] <;> field_simp
    · linear_combination -ha
    · ring
    · ring
  · ext j
    fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_four, Model.foldP, hQ, hX] <;>
      (try rw [hA]) <;> field_simp
    · linear_combination -ha
    · ring
    · ring
    · ring
  · simp only [dotProduct, Fin.sum_univ_four, Model.foldP, Model.tangent, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons, hX]
    rw [hA]; field_simp
    linear_combination hDl - 2 * m.g.E ^ 2 * m.g.L ^ 2 * m.g.ω0 * m.g.R * hcs

/-- **The fold coefficient**: for `M, L ≠ 0`, `|Z|² > 0` and `D ≠ D_line`, Kuznetsov's quadratic
coefficient `a = ½ ⟨p, B(q, q)⟩` of the tangent `q` and `p = Line.VSM.Model.foldP` is
`a = (P(δ*) − c₀)/(2 (D − D_line))`, `c₀ = E² R/|Z|²` (at every angle; at a fold `K = 0` it is
the coefficient of the saddle-node). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.foldCoeff_fold (m : Model) (hM : m.g.M ≠ 0)
    (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) (hD : m.g.D ≠ m.g.Dline) :
    foldCoeff m.field 0 (WithLp.toLp 2 m.tangent) (WithLp.toLp 2 m.foldP) =
      (m.g.qssPower m.δ - m.g.c0) / (2 * (m.g.D - m.g.Dline)) := by
  have hpt : ∀ i, m.point i = ![m.δ, 0, (m.g.is m.δ).re, (m.g.is m.δ).im] i := fun i => by
    fin_cases i <;> rfl
  have hP : m.g.power m.δ (m.g.is m.δ).re (m.g.is m.δ).im = m.g.qssPower m.δ := rfl
  have hcs := Real.cos_sq_add_sin_sq m.δ
  have hDD : m.g.D - m.g.Dline ≠ 0 := sub_ne_zero.mpr hD
  have hZ' := hZ.ne'
  rw [foldCoeff, fold_fderiv2, fderiv_fderiv_field, hpt 0, hpt 2, hpt 3]
  simp [PiLp.inner_apply, Fin.sum_univ_four, Model.tangent, Model.foldP, Network.c0]
  field_simp
  rw [hP]
  linear_combination (-(m.g.E ^ 2 * m.g.R)) * hcs

/-- **The characteristic polynomial at a fold**: for `L ≠ 0`, `|Z|² > 0` and `K = 0` (`a₀ = 0`),
`det(sI − J) = s (s³ + a₃ s² + a₂ s + a₁)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.charpoly_fold (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) (hK : m.K = 0) :
    (jacobianC m.field 0).charpoly = X * (X ^ 3 + C ((m.g.coeff3 : ℝ) : ℂ) * X ^ 2 +
      C ((m.g.coeff2 m.Q : ℝ) : ℂ) * X + C ((m.g.coeff1 m.Q : ℝ) : ℂ)) := by
  have h0 : m.g.coeff0 m.Q = 0 := by rw [m.coeff0_eq hL hZ, hK]; simp
  rw [Model.jacobianC_field, Linear.complexify, Matrix.charpoly_map, m.charpoly_jac, h0]
  simp
  ring

/-- **The fold is a saddle-node**
(`Dynamics.CenterManifold.unstable_of_foldCoeff_ne_zero_of_charpoly`): a balanced physical
model at a fold `K = 0` whose other three eigenvalues are stable (`a₁ > 0`, `a₁ < a₃ a₂`) is
unstable. Its fold coefficient
`a = (P_ref − c₀)/(2 (D − D_line))` (`Line.VSM.Model.foldCoeff_fold`) never vanishes there:
`P_ref − c₀ = ± A ≠ 0` at a fold, and `a₁ = ρ (D − D_line)/M > 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold (m : Model) (hp : Meets m .physical)
    (hb : Meets m .balanced) (hK : m.K = 0) (h1 : 0 < m.g.coeff1 m.Q)
    (h31 : m.g.coeff1 m.Q < m.g.coeff3 * m.g.coeff2 m.Q) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Unstable m.field 0
  obtain ⟨hN, hM, hD0⟩ := hp
  have hL := hN.L.ne'
  have hZ := hN.absSq_pos
  have hD : m.g.D ≠ m.g.Dline := by
    intro hD
    rw [m.coeff1_eq hL hZ, hK, hD, sub_self] at h1
    simp at h1
  have h3 : 0 < m.g.coeff3 := by
    have : 0 ≤ m.g.σ := div_nonneg hN.R hN.L.le
    unfold coeff3; positivity
  have h2 : 0 < m.g.coeff2 m.Q := by
    by_contra h2
    push Not at h2
    nlinarith
  have hF : ContDiff ℝ 2 m.field := (m.g.contDiff_field (k := 2)).comp
    (contDiff_id.add contDiff_const)
  have hF0 : m.field 0 = 0 := by
    show m.g.field (0 + m.point) = 0
    rw [zero_add]
    exact (m.field_point_eq_zero_iff hM.ne' hL hZ.ne').mpr hb
  refine Dynamics.CenterManifold.unstable_of_foldCoeff_ne_zero_of_charpoly hF hF0
    (m.isNullPair_fold ⟨hN, hM, hD0⟩ hK hD) (m.charpoly_fold hL hZ hK) ?_ ?_
  · intro s hs
    simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C] at hs
    exact Criteria.cubic_roots_re_neg_of h3 h1 h31 s hs
  · rw [m.foldCoeff_fold hM.ne' hL hZ hD]
    exact div_ne_zero (m.qssPower_sub_c0_ne_zero_of_fold ⟨hN, hM, hD0⟩ hK)
      (mul_ne_zero two_ne_zero (sub_ne_zero.mpr hD))

/-- **The fold decided off its degenerate set**: a balanced physical model at a fold `K = 0`
with `a₁ ≠ 0` (off the Bogdanov–Takens damping `D = D_line`) and `a₃ a₂ ≠ a₁` (off the
zero–Hopf points) is unstable: a strict Routh violation (`Line.VSM.mem_den_unstable`), or the
saddle-node law (`Line.VSM.mem_den_unstable_of_fold`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold_of_ne (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hK : m.K = 0)
    (h1 : m.g.coeff1 m.Q ≠ 0) (h31 : m.g.coeff3 * m.g.coeff2 m.Q ≠ m.g.coeff1 m.Q) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  by_cases hv : m.RouthViolation
  · exact mem_den_unstable m hp hb hv
  have h0 : m.g.coeff0 m.Q = 0 := by
    rw [m.coeff0_eq hp.1.L.ne' hp.1.absSq_pos, hK]; simp
  unfold Model.RouthViolation at hv
  push Not at hv
  obtain ⟨-, -, v1, -, v4⟩ := hv
  rw [h0, mul_zero, add_zero] at v4
  have h1' : 0 < m.g.coeff1 m.Q := lt_of_le_of_ne v1 (Ne.symm h1)
  have h31' : m.g.coeff1 m.Q ≤ m.g.coeff3 * m.g.coeff2 m.Q := by nlinarith
  exact mem_den_unstable_of_fold m hp hb hK h1' (lt_of_le_of_ne h31' (Ne.symm h31))

/-- **The fold decided off the zero–Hopf points**: a balanced physical model at a fold `K = 0`
with `a₃ a₂ ≠ a₁` is unstable. Off the Bogdanov–Takens damping (`a₁ ≠ 0`) this is
`Line.VSM.mem_den_unstable_of_fold_of_ne`; at it (`a₁ = 0`, `D = D_line`) `a₂ = |Z|² n/(L² M) ≠ 0`
(`Line.VSM.Model.coeff2_of_bt`): `a₂ < 0` is a strict Routh violation (`Line.VSM.mem_den_unstable`)
and `a₂ > 0` the Bogdanov–Takens cusp (`Line.VSM.mem_den_unstable_of_bt`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold_of_ne_zeroHopf (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hK : m.K = 0)
    (h31 : m.g.coeff3 * m.g.coeff2 m.Q ≠ m.g.coeff1 m.Q) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  by_cases h1 : m.g.coeff1 m.Q = 0
  swap
  · exact mem_den_unstable_of_fold_of_ne m hp hb hK h1 h31
  obtain ⟨hN, hM, hD0⟩ := hp
  have hL := hN.L.ne'
  have hZ := hN.absSq_pos
  have hρ : 0 < m.g.ρ := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
    rw [this]; exact div_pos hZ (pow_pos hN.L 2)
  have hD : m.g.D = m.g.Dline := by
    rw [m.coeff1_eq hL hZ, hK, mul_zero, add_zero, div_eq_zero_iff] at h1
    rcases h1 with h1 | h1
    · exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hρ.ne')
    · exact absurd h1 hM.ne'
  have h2 := m.coeff2_of_bt ⟨hN, hM, hD0⟩ hK hD
  have h2ne : m.g.coeff2 m.Q ≠ 0 := by
    intro h0; rw [h0, mul_zero, h1] at h31; exact h31 rfl
  rcases lt_or_gt_of_ne h2ne with hneg | hpos
  · exact mem_den_unstable m ⟨hN, hM, hD0⟩ hb (Or.inr (Or.inl hneg))
  · have hn : 0 < m.g.btInertia := by
      rw [h2] at hpos
      have hd : 0 < m.g.L ^ 2 * m.g.M := by positivity
      have := (div_pos_iff_of_pos_right hd).mp hpos
      exact (pos_iff_pos_of_mul_pos this).mp hZ
    exact mem_den_unstable_of_bt m ⟨hN, hM, hD0⟩ hb hK hD hn

end Fold

/-- The degenerate balanced points of the VSM on the line, still undecided: the zero–Hopf fold
points (`K = 0`, `a₃ a₂ = a₁`: the cubic cofactor has a pair `±i√a₂`, or the triple zero
`a₁ = a₂ = 0`) and the Bautin-type points of the Hopf boundary (`a₃ a₂ a₁ = a₁² + a₃² a₀`,
`a₁, a₀ > 0`, `𝔅_δ = 0`). The other fold points, the Bogdanov–Takens damping `a₁ = 0` included,
are decided (`Line.VSM.mem_den_unstable_of_fold_of_ne_zeroHopf`). -/
def Model.Degenerate (m : Model) : Prop :=
  Meets m .balanced ∧ ((m.K = 0 ∧ m.g.coeff3 * m.g.coeff2 m.Q = m.g.coeff1 m.Q) ∨
    (m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
    m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q ∧ 0 < m.g.coeff1 m.Q ∧
    0 < m.g.coeff0 m.Q ∧ bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)
      m.angleShift = 0))

/-- Off the degenerate set, a Lyapunov stable physical model is balanced and either meets the
strict quartic Routh conditions or lies on the Hopf boundary with `𝔅_δ > 0`: every other case
is unstable (not balanced, a strict Routh violation, the fold off the zero–Hopf points, the
subcritical Hopf boundary). -/
@[tmio TM, powerlib_domain] private theorem rhs_of_lyapunovStable (m : Model)
    (hp : Meets m .physical) (hd : ¬ m.Degenerate)
    (hl : m ∈ family.den (.flow .lyapunovStable)) :
    Meets m .balanced ∧ (m.Routh ∨ (m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q ∧ 0 < m.g.coeff1 m.Q ∧
      0 < m.g.coeff0 m.Q ∧ 0 < bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0
        (m.Q / m.g.M) m.angleShift)) := by
  have hunst : m ∈ family.den (.flow .unstable) →
      m ∉ family.den (.flow .lyapunovStable) := fun hu => by
    have h := Spectral.not_mem_den_lyapunovStable_of_unstable hu
    unfold powerlib.TMIO.Statement at h
    exact h
  obtain ⟨hN, hM, hD⟩ := hp
  have hZ := hN.absSq_pos
  have hρ : 0 < m.g.ρ := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp [hN.L.ne']
    rw [this]; exact div_pos hZ (pow_pos hN.L 2)
  have h3 : 0 < m.g.coeff3 := by
    have : 0 ≤ m.g.σ := div_nonneg hN.R hN.L.le
    unfold coeff3; positivity
  have hb : Meets m .balanced := by
    by_contra hb
    have hne : m.field 0 ≠ 0 := by
      intro h0
      apply hb
      have h' : m.g.field m.point = 0 := by simpa [Model.field] using h0
      exact (m.field_point_eq_zero_iff hM.ne' hN.L.ne' hZ.ne').mp h'
    rw [(connection_proof% family_isAutonomous.mem_den_flow)] at hl
    change LyapunovStable m.field 0 at hl
    exact Dynamics.unstable_of_ne_zero m.contDiff_field hne hl
  refine ⟨hb, ?_⟩
  by_cases hv : m.RouthViolation
  · exact absurd hl (hunst (mem_den_unstable m ⟨hN, hM, hD⟩ hb hv))
  by_cases hr : m.Routh
  · exact Or.inl hr
  right
  unfold Model.RouthViolation at hv
  unfold Model.Routh at hr
  push Not at hv hr
  obtain ⟨-, -, v1, v0, v4⟩ := hv
  have h0 : 0 < m.g.coeff0 m.Q := by
    rcases v0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [m.coeff0_eq hN.L.ne' hZ] at h
      have h' : m.g.ρ * m.K = 0 := by
        rcases div_eq_zero_iff.mp h.symm with h'' | h''
        · exact h''
        · exact absurd h'' hM.ne'
      have hK : m.K = 0 := (mul_eq_zero.mp h').resolve_left hρ.ne'
      by_cases hd1 : m.g.coeff3 * m.g.coeff2 m.Q = m.g.coeff1 m.Q
      · exact hd ⟨hb, Or.inl ⟨hK, hd1⟩⟩
      · exact hunst (mem_den_unstable_of_fold_of_ne_zeroHopf m ⟨hN, hM, hD⟩ hb hK hd1) hl
  have h1 : 0 < m.g.coeff1 m.Q := by
    rcases v1.lt_or_eq with h | h
    · exact h
    · rw [← h] at v4
      have : 0 < m.g.coeff3 ^ 2 * m.g.coeff0 m.Q := by positivity
      nlinarith
  have hH : m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q :=
    le_antisymm (hr h3 h1 h0) v4
  refine ⟨hH, h1, h0, ?_⟩
  rcases lt_trichotomy (bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0 (m.Q / m.g.M)
    m.angleShift) 0 with hB | hB | hB
  · exact absurd hl (hunst
      (mem_den_unstable_of_bautinFormAngle_neg m ⟨hN, hM, hD⟩ hb hH h1 h0 hB))
  · exact absurd ⟨hb, Or.inr ⟨hH, h1, h0, hB⟩⟩ hd
  · exact hB

/-- The strict Routh conditions and the supercritical Hopf boundary give local asymptotic
stability (the family translation and
`Line.VSM.mem_den_locallyAsymptoticallyStable_of_bautinFormAngle_pos`). -/
@[tmio TM, powerlib_domain] private theorem las_of_rhs (m : Model) (hp : Meets m .physical)
    (h : Meets m .balanced ∧ (m.Routh ∨ (m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
      m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q ∧ 0 < m.g.coeff1 m.Q ∧
      0 < m.g.coeff0 m.Q ∧ 0 < bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0
        (m.Q / m.g.M) m.angleShift))) :
    m ∈ family.den (.flow .locallyAsymptoticallyStable) := by
  have hs := chain_le_semantics
  unfold powerlib.TMIO.Statement at hs
  obtain ⟨hN, hM, hD⟩ := hp
  revert h
  rintro ⟨hb, hr | ⟨hH, h1, h0, hB⟩⟩
  · refine (Family.chain_le_semantics_iff.mp hs _) ((TMIO.mem_realize _ _ _).mpr ?_)
    intro q hq
    simp only [family, translate, Spectral.localTable, Spectral.table, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · exact hb
    · exact ⟨hN, hM, hD⟩
    · exact hr
  · exact mem_den_locallyAsymptoticallyStable_of_bautinFormAngle_pos m ⟨hN, hM, hD⟩ hb hH h1
      h0 hB

/-- **Complete local asymptotic membership** (the counterpart of the rate-coupled GFL PLL's
`GFL.RatePLL.mem_den_locallyAsymptoticallyStable_iff`): a physical model off the degenerate set
(`Line.VSM.Model.Degenerate`: the zero–Hopf fold points and the Bautin-type points) is locally
asymptotically stable iff it is balanced and either meets the strict quartic Routh conditions or
lies on the Hopf boundary (`a₃ a₂ a₁ = a₁² + a₃² a₀`, `a₁, a₀ > 0`) with `𝔅_δ > 0`
(supercritical). The Bogdanov–Takens fold points are unstable
(`Line.VSM.mem_den_unstable_of_fold_of_ne_zeroHopf`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff (m : Model)
    (hp : Meets m .physical) (hd : ¬ m.Degenerate) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      Meets m .balanced ∧ (m.Routh ∨ (m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
        m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q ∧ 0 < m.g.coeff1 m.Q ∧
        0 < m.g.coeff0 m.Q ∧ 0 < bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0
          (m.Q / m.g.M) m.angleShift))) := by
  unfold TMIO.Statement
  refine ⟨fun hl => rhs_of_lyapunovStable m hp hd ?_, las_of_rhs m hp⟩
  have h := Spectral.den_las_subset_lyapunovStable (F := family)
  unfold powerlib.TMIO.Statement at h
  exact h hl

/-- **Complete Lyapunov membership**: off the degenerate set (`Line.VSM.Model.Degenerate`) a
physical model is Lyapunov stable iff it is locally asymptotically stable, i.e. iff it is balanced
and either meets the strict quartic Routh conditions or lies on the Hopf boundary with `𝔅_δ > 0`
(`Line.VSM.mem_den_locallyAsymptoticallyStable_iff`). -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff (m : Model)
    (hp : Meets m .physical) (hd : ¬ m.Degenerate) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      Meets m .balanced ∧ (m.Routh ∨ (m.g.coeff3 * m.g.coeff2 m.Q * m.g.coeff1 m.Q =
        m.g.coeff1 m.Q ^ 2 + m.g.coeff3 ^ 2 * m.g.coeff0 m.Q ∧ 0 < m.g.coeff1 m.Q ∧
        0 < m.g.coeff0 m.Q ∧ 0 < bautinFormAngle (m.g.D / m.g.M) (m.g.R / m.g.L) m.g.ω0
          (m.Q / m.g.M) m.angleShift))) := by
  unfold TMIO.Statement
  refine ⟨rhs_of_lyapunovStable m hp hd, fun h => ?_⟩
  have hs := Spectral.den_las_subset_lyapunovStable (F := family)
  unfold powerlib.TMIO.Statement at hs
  exact hs (las_of_rhs m hp h)

end VSM
end powerlib.GFM.Line
