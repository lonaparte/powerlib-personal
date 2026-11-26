import theorem.GridTiedConverter.GFM.HopfLineLPF
import theorem.GridTiedConverter.GFM.BTCoefficientLineLPF
import theorem.Dynamics.SaddleNodeReduction
import theorem.Dynamics.BTInstability

/-! # The VSM with a power filter on a dynamic R–L line: the fold

Domain module.

Model boundary.
* The five-state VSM + power filter `Line.VSMLPF` of
  `theorem/GridTiedConverter/GFM/Line/Model.lean`, unchanged: state `(δ, ω, P_f, i_d, i_q)`, grid
  dq frame at `ω₀`, export-positive power, constant `E`, `M ω̇ = P_ref − P_f − D ω`,
  `Ṗ_f = ω_c (P_e − P_f)`, `L i̇ = E e^{jδ} − V − (R + jX) i`; no voltage loop, inner loops, PLL,
  delay or PWM. Read about a selected angle (`Line.VSMLPF.Model`), translated so that the
  operating point `(δ*, 0, P_ref, i_s(δ*))` is the origin.
* The fold: a balanced physical model (`Network.Physical`, `M, D, ω_c > 0`) at `K = P'(δ*) = 0`,
  where the constant coefficient `a₀ = ω_c ρ K/M` of the characteristic quintic vanishes (a zero
  eigenvalue). The degenerate fold points (`Line.VSMLPF.Model.FoldDegenerate`) are located, not
  decided: the zero–Hopf points `Δ₃ = 0` (the quartic cofactor has a pair `±iΩ`; at the
  Bogdanov–Takens damping `D = D_line` this is `a₂ (a₄ a₃ − a₂) = 0`, with the triple zero
  `a₂ = 0`). The Bogdanov–Takens points `a₁ = 0` with `Δ₃ ≠ 0` are decided.
* Level: Lyapunov instability (LeanForControl's `Unstable`) of the operating point, through
  `Line.VSMLPF.family`; the null pair and the fold coefficient are static evidence.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.2 and §5.4 (the fold
coefficient `a = ½⟨p, B(q, q)⟩`); the saddle-node law
`Dynamics.CenterManifold.unstable_of_foldCoeff_ne_zero_of_charpoly`
(`theorem/Dynamics/SaddleNodeReduction.lean`); the tangent `Line.VSMLPF.Model.btTangent` and the
null-vector law `Line.VSMLPF.Model.jac_mulVec_btTangent`
(`theorem/GridTiedConverter/GFM/BifurcationLineLPF.lean`), the second derivative
`Line.VSMLPF.fderiv_fderiv_field` (`theorem/GridTiedConverter/GFM/BTCoefficientLineLPF.lean`); the
four-state counterpart `Line.VSM.mem_den_unstable_of_fold_of_ne`
(`theorem/GridTiedConverter/GFM/HopfLineMembership.lean`) and the Q–V droop fold
(`theorem/GridTiedConverter/GFM/QVDroopFold.lean`); the Bogdanov–Takens law
`NormalForm.BogdanovTakens.IsBTChain.unstable_of_coeffA_ne_zero`
(`theorem/Dynamics/BTInstability.lean`) with the chain `Line.VSMLPF.Model.exists_isBTChain_of_bt`
and the coefficients `Line.VSMLPF.Model.coeff_of_bt`, `Line.VSMLPF.Model.coeff2_of_bt`
(`theorem/GridTiedConverter/GFM/BTCoefficientLineLPF.lean`). The left null vector and the fold
coefficient were derived with exact computer algebra (SymPy, untrusted) and are proved here by
`field_simp` and `linear_combination`.

Results.
* The left null vector `Line.VSMLPF.Model.foldP`, `p = (D, M, −1/ω_c,
  E L (X sin δ* − R cos δ*)/|Z|², −E L (X cos δ* + R sin δ*)/|Z|²)/(D − D_line)`; at a fold with
  `D ≠ D_line` the tangent `q = (1, 0, 0, i_s'(δ*))` and `p` are a normalised null pair
  (`Line.VSMLPF.Model.isNullPair_fold`).
* `Line.VSMLPF.Model.foldCoeff_fold`: the fold coefficient is `a = (P(δ*) − c₀)/(2 (D − D_line))`,
  `c₀ = E² R/|Z|²`, at every angle (the power filter does not change the four-state value);
  `Line.VSMLPF.Model.foldCoeff_fold_ne_zero`: `a ≠ 0` at every fold off `D = D_line`
  (`P(δ*) − c₀ = ± A`), so the fold has no cusp points.
* `Line.VSMLPF.Model.charpoly_fold`: at a fold `det(sI − J) = s (s⁴ + a₄ s³ + a₃ s² + a₂ s + a₁)`;
  `Line.VSMLPF.Model.coeff1_fold`: there `a₁ = ω_c ρ (D − D_line)/M`, so `a₁ = 0` exactly at the
  Bogdanov–Takens damping; `Line.VSMLPF.Model.charpoly_fold_eval_zeroHopf`: at a fold with
  `Δ₃ = 0` and `a₄, a₂ > 0` the eigenvalues include `±i √(a₂/a₄)` (zero–Hopf).
* `Line.VSMLPF.Model.FoldDegenerate`: the degenerate balanced fold points still undecided
  (`K = 0`, `Δ₃ = 0`).

Family and connection conclusions.
No new family: connection conclusions on `Line.VSMLPF.family`.
* **`Line.VSMLPF.mem_den_unstable_of_fold`** (the fold is a saddle-node): a balanced physical
  model at `K = 0` with `a₁ > 0` and `Δ₃ > 0` (the quartic cofactor is Hurwitz) is unstable.
* **`Line.VSMLPF.mem_den_unstable_of_fold_of_ne`** (the fold decided): a balanced physical model
  at `K = 0` with `a₁ ≠ 0` and `Δ₃ ≠ 0` is unstable (a strict quintic Routh violation,
  `Line.VSMLPF.mem_den_unstable`, or the saddle-node law).
* **`Line.VSMLPF.mem_den_unstable_of_bt`** (the Bogdanov–Takens point is a cusp): a balanced
  physical model at `K = 0` with `D = D_line`, `n₅ > 0` and `a₂ < a₄ a₃` (the cubic cofactor
  `s³ + a₄ s² + a₃ s + a₂` Hurwitz) is unstable; `a = (P(δ*) − c₀)/(2 n₅)` never vanishes there.
* **`Line.VSMLPF.mem_den_unstable_of_fold_of_det3_ne`** (the fold decided off the zero–Hopf
  points): at `K = 0` with `Δ₃ ≠ 0` the model is unstable; hence at a fold the operating point is
  never locally asymptotically stable off `Line.VSMLPF.Model.FoldDegenerate`.
-/

noncomputable section
namespace powerlib.GFM.Line
namespace VSMLPF

open Polynomial Matrix Complex
open scoped RealInnerProductSpace
open powerlib.Dynamics (State)
open powerlib.NormalForm.LyapunovCoefficient (jacobianC)
open powerlib.NormalForm.BogdanovTakens (IsNullPair foldCoeff isNullPair_toEuclideanCLM_iff
  IsBTChain coeffA)

/-- The left null vector of the Jacobian at a fold, normalised against the tangent
`Line.VSMLPF.Model.btTangent` by `D − D_line`:
`p = (D, M, −1/ω_c, E L (X sin δ* − R cos δ*)/|Z|², −E L (X cos δ* + R sin δ*)/|Z|²)/
(D − D_line)`.
-/
def Model.foldP (m : Model) : Fin 5 → ℝ :=
  (m.g.D - m.g.Dline)⁻¹ • ![m.g.D, m.g.M, -(1 / m.g.ωc),
    m.g.E * m.g.L * (m.g.X * Real.sin m.δ - m.g.R * Real.cos m.δ) / m.g.absSq,
    -(m.g.E * m.g.L * (m.g.X * Real.cos m.δ + m.g.R * Real.sin m.δ) / m.g.absSq)]

@[tmio M, powerlib_domain] private theorem lf_fderiv (m : Model) :
    fderiv ℝ m.field 0 = Matrix.toEuclideanCLM (n := Fin 5) (𝕜 := ℝ) m.jac := by
  rw [show m.field = fun z => m.g.field (z + m.point) from rfl, fderiv_comp_add_right,
    zero_add, m.fderiv_point]

@[tmio M, powerlib_domain] private theorem lf_fderiv2 (m : Model) :
    fderiv ℝ (fderiv ℝ m.field) 0 = fderiv ℝ (fderiv ℝ m.g.field) m.point := by
  have h : fderiv ℝ m.field = fun z => fderiv ℝ m.g.field (z + m.point) := by
    funext z
    show fderiv ℝ (fun z => m.g.field (z + m.point)) z = _
    rw [fderiv_comp_add_right]
  rw [h, fderiv_comp_add_right, zero_add]

@[tmio M, powerlib_domain] private theorem lf_tangent (m : Model) :
    m.btTangent = ![1, 0, 0, m.g.E * (m.g.X * Real.cos m.δ - m.g.R * Real.sin m.δ) / m.g.absSq,
      m.g.E * (m.g.X * Real.sin m.δ + m.g.R * Real.cos m.δ) / m.g.absSq] := by
  funext i; fin_cases i <;> rfl

/-- **The null pair of a fold**: at a physical model with `K = 0` and `D ≠ D_line`, the tangent
`q = (1, 0, 0, i_s'(δ*))` (`Line.VSMLPF.Model.btTangent`) and `p = Line.VSMLPF.Model.foldP` are a
normalised null pair of the Jacobian at the operating point (`J q = 0`, `pᵀ J = 0`,
`⟨p, q⟩ = 1`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.isNullPair_fold {m : Model} (hp : Meets m .physical)
    (hK : m.K = 0) (hD : m.g.D ≠ m.g.Dline) :
    IsNullPair (fderiv ℝ m.field 0) (WithLp.toLp 2 m.btTangent) (WithLp.toLp 2 m.foldP) := by
  obtain ⟨hN, hM, -, hω⟩ := hp
  have hL := hN.L.ne'
  have hZ := hN.absSq_pos
  have hV : m.g.E * m.g.V ≠ 0 := (mul_pos hN.E hN.V).ne'
  obtain ⟨k, hc, hs, hk⟩ := (⟨m.g.toVSM, m.δ⟩ : VSM.Model).fold_coords hZ hV hK
  have hc' : Real.cos m.δ = -(m.g.R * k) / (m.g.R ^ 2 + m.g.X ^ 2) := hc
  have hs' : Real.sin m.δ = m.g.X * k / (m.g.R ^ 2 + m.g.X ^ 2) := hs
  have hk' : k ^ 2 = m.g.R ^ 2 + m.g.X ^ 2 := hk
  have hQ : m.g.reactive m.δ (m.g.is m.δ).re (m.g.is m.δ).im =
      m.g.E ^ 2 * m.g.X / (m.g.R ^ 2 + m.g.X ^ 2) := by
    have h1 := m.g.syncCoeff_add_qssReactive hZ m.δ
    rw [show m.g.syncCoeff m.δ = 0 from hK, zero_add] at h1
    exact h1
  have hZ' : m.g.R ^ 2 + m.g.X ^ 2 ≠ 0 := hZ.ne'
  have habs : m.g.absSq = m.g.R ^ 2 + m.g.X ^ 2 := rfl
  have hDD : m.g.D - m.g.Dline ≠ 0 := sub_ne_zero.mpr hD
  have hcs := Real.cos_sq_add_sin_sq m.δ
  have hDl : m.g.Dline * (m.g.R ^ 2 + m.g.X ^ 2) ^ 2 =
      2 * m.g.E ^ 2 * m.g.R * m.g.X * m.g.L := by
    rw [Network.Dline, habs]; field_simp
  rw [lf_fderiv, isNullPair_toEuclideanCLM_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [m.jac_mulVec_btTangent hL hZ, show m.g.syncCoeff m.δ = 0 from hK, mul_zero]
    funext i; fin_cases i <;> rfl
  · ext j
    fin_cases j <;>
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_five, Model.foldP, Model.jac, jacobian, hQ,
        habs, hc', hs'] <;>
      field_simp <;>
      first
        | ring1
        | linear_combination (-(m.g.E ^ 2 * m.g.X * (m.g.R ^ 2 + m.g.X ^ 2))) * hk'
  · simp only [dotProduct, Fin.sum_univ_five, Model.foldP, lf_tangent, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons, habs]
    field_simp
    linear_combination m.g.ωc * hDl - 2 * m.g.ωc * m.g.E ^ 2 * m.g.L * m.g.R * m.g.X * hcs

/-- **The fold coefficient**: for `ω_c, L ≠ 0`, `|Z|² > 0` and `D ≠ D_line`, Kuznetsov's
quadratic coefficient `a = ½ ⟨p, B(q, q)⟩` of the tangent `q = Line.VSMLPF.Model.btTangent` and
`p = Line.VSMLPF.Model.foldP` is `a = (P(δ*) − c₀)/(2 (D − D_line))`, `c₀ = E² R/|Z|²`, at every
angle (the four-state value: the power filter does not change it). Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem Model.foldCoeff_fold (m : Model) (hω : m.g.ωc ≠ 0)
    (hL : m.g.L ≠ 0) (hZ : 0 < m.g.absSq) (hD : m.g.D ≠ m.g.Dline) :
    foldCoeff m.field 0 (WithLp.toLp 2 m.btTangent) (WithLp.toLp 2 m.foldP) =
      (m.g.qssPower m.δ - m.g.c0) / (2 * (m.g.D - m.g.Dline)) := by
  have hpt : ∀ i, m.point i =
      ![m.δ, 0, m.g.Pref, (m.g.is m.δ).re, (m.g.is m.δ).im] i := fun i => by
    fin_cases i <;> rfl
  have hP : m.g.power m.δ (m.g.is m.δ).re (m.g.is m.δ).im = m.g.qssPower m.δ := rfl
  have hcs := Real.cos_sq_add_sin_sq m.δ
  have hDD : m.g.D - m.g.Dline ≠ 0 := sub_ne_zero.mpr hD
  have hZ' := hZ.ne'
  rw [foldCoeff, lf_fderiv2, fderiv_fderiv_field, hpt 0, hpt 3, hpt 4, lf_tangent]
  simp [PiLp.inner_apply, Fin.sum_univ_five, Model.foldP, Network.c0]
  field_simp
  rw [hP]
  linear_combination (-(m.g.E ^ 2 * m.g.R)) * hcs

@[tmio M, powerlib_domain] private theorem lf_P_sub_c0_ne {m : Model} (hp : Meets m .physical)
    (hK : m.K = 0) : m.g.qssPower m.δ - m.g.c0 ≠ 0 := by
  have hZ := hp.1.absSq_pos
  have hA : m.g.A ≠ 0 :=
    div_ne_zero (mul_pos hp.1.E hp.1.V).ne' (Real.sqrt_pos.mpr hZ).ne'
  have hcos : Real.cos (m.δ - m.g.α) = 0 :=
    (mul_eq_zero.mp (show m.g.A * Real.cos (m.δ - m.g.α) = 0 from hK)).resolve_left hA
  have h : 0 < (m.g.qssPower m.δ - m.g.c0) ^ 2 := by
    rw [m.g.qssPower_eq_polar hZ, add_sub_cancel_left, mul_pow,
      show Real.sin (m.δ - m.g.α) ^ 2 = 1 by
        nlinarith [Real.sin_sq_add_cos_sq (m.δ - m.g.α)], mul_one]
    positivity
  intro h0
  rw [h0] at h
  simp at h

/-- **The fold has no cusp points**: at a fold `K = 0` of a physical model with `D ≠ D_line` the
fold coefficient does not vanish (`P(δ*) − c₀ = ± A ≠ 0` there). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.foldCoeff_fold_ne_zero {m : Model}
    (hp : Meets m .physical) (hK : m.K = 0) (hD : m.g.D ≠ m.g.Dline) :
    foldCoeff m.field 0 (WithLp.toLp 2 m.btTangent) (WithLp.toLp 2 m.foldP) ≠ 0 := by
  rw [m.foldCoeff_fold hp.2.2.2.ne' hp.1.L.ne' hp.1.absSq_pos hD]
  exact div_ne_zero (lf_P_sub_c0_ne hp hK) (mul_ne_zero two_ne_zero (sub_ne_zero.mpr hD))

/-- **The characteristic polynomial at a fold**: for `K = 0` (`a₀ = 0`),
`det(sI − J) = s (s⁴ + a₄ s³ + a₃ s² + a₂ s + a₁)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.charpoly_fold (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) (hK : m.K = 0) :
    (jacobianC m.field 0).charpoly = X * (X ^ 4 + C ((m.g.coeff4 : ℝ) : ℂ) * X ^ 3 +
      C ((m.g.coeff3 : ℝ) : ℂ) * X ^ 2 + C ((m.g.coeff2 m.Q : ℝ) : ℂ) * X +
        C ((m.g.coeff1 m.Q : ℝ) : ℂ)) := by
  have h0 : m.g.coeff0 m.Q = 0 := by rw [m.coeff0_eq hL hZ, hK]; simp
  refine Polynomial.funext fun s => ?_
  rw [m.jacobianC_field, ← Linear.det_characteristicMatrix_eq_eval, m.det_characteristicMatrix, h0]
  simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C]
  push_cast
  ring

/-- **The linear coefficient at a fold**: for `L ≠ 0`, `|Z|² > 0` and `K = 0`,
`a₁ = ω_c ρ (D − D_line)/M`; it vanishes exactly at the Bogdanov–Takens damping `D = D_line`
(`Line.VSMLPF.Model.two_le_rootMultiplicity_zero_iff`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.coeff1_fold (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) (hK : m.K = 0) :
    m.g.coeff1 m.Q = m.g.ωc * (m.g.ρ * (m.g.D - m.g.Dline) / m.g.M) := by
  have h := VSM.Model.coeff1_eq ⟨m.g.toVSM, m.δ⟩ hL hZ
  rw [show (⟨m.g.toVSM, m.δ⟩ : VSM.Model).K = 0 from hK, mul_zero, add_zero] at h
  rw [coeff1]
  exact congrArg (m.g.ωc * ·) h

/-- **The zero–Hopf points of the fold**: at a fold `K = 0` with `Δ₃ = 0` (the third Hurwitz
determinant of the quintic) and `a₄, a₂ > 0`, `i Ω`, `Ω = √(a₂/a₄)`, is an eigenvalue: the quartic
cofactor of `Line.VSMLPF.Model.charpoly_fold` has the pair `±iΩ`. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem Model.charpoly_fold_eval_zeroHopf (m : Model) (hL : m.g.L ≠ 0)
    (hZ : 0 < m.g.absSq) (hK : m.K = 0) (h4 : 0 < m.g.coeff4) (h2 : 0 < m.g.coeff2 m.Q)
    (h3 : Criteria.quinticHurwitzDet3 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q) (m.g.coeff1 m.Q)
      (m.g.coeff0 m.Q) = 0) :
    (jacobianC m.field 0).charpoly.eval
      (((Real.sqrt (m.g.coeff2 m.Q / m.g.coeff4) : ℝ) : ℂ) * I) = 0 := by
  have h0 : m.g.coeff0 m.Q = 0 := by rw [m.coeff0_eq hL hZ, hK]; simp
  rw [h0] at h3
  unfold Criteria.quinticHurwitzDet3 Criteria.quinticHurwitzDet2 at h3
  set Ω := Real.sqrt (m.g.coeff2 m.Q / m.g.coeff4) with hΩ
  have hΩ2 : Ω ^ 2 = m.g.coeff2 m.Q / m.g.coeff4 := Real.sq_sqrt (by positivity)
  have e2 : m.g.coeff4 * Ω ^ 2 = m.g.coeff2 m.Q := by rw [hΩ2]; field_simp
  have e4 : Ω ^ 4 - m.g.coeff3 * Ω ^ 2 + m.g.coeff1 m.Q = 0 := by
    have : m.g.coeff4 ^ 2 * (Ω ^ 4 - m.g.coeff3 * Ω ^ 2 + m.g.coeff1 m.Q) = 0 := by
      have e : m.g.coeff4 ^ 2 * Ω ^ 4 = m.g.coeff2 m.Q ^ 2 := by rw [← e2]; ring
      linear_combination e - m.g.coeff4 * m.g.coeff3 * e2 - h3
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 h4.ne')
  rw [m.charpoly_fold hL hZ hK]
  simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C]
  set z : ℂ := (Ω : ℂ) * I with hz
  have hz2 : z ^ 2 = -(Ω : ℂ) ^ 2 := by rw [hz, mul_pow, I_sq]; ring
  have e2c : ((m.g.coeff4 : ℝ) : ℂ) * (Ω : ℂ) ^ 2 = ((m.g.coeff2 m.Q : ℝ) : ℂ) := by
    exact_mod_cast e2
  have e4c : (Ω : ℂ) ^ 4 - ((m.g.coeff3 : ℝ) : ℂ) * (Ω : ℂ) ^ 2 + ((m.g.coeff1 m.Q : ℝ) : ℂ) = 0 :=
    by exact_mod_cast e4
  linear_combination z * e4c - z ^ 2 * e2c + (z * (z ^ 2 - (Ω : ℂ) ^ 2) +
    ((m.g.coeff4 : ℝ) : ℂ) * z ^ 2 + ((m.g.coeff3 : ℝ) : ℂ) * z) * hz2

/-- The degenerate balanced fold points still undecided: `K = 0` (`a₀ = 0`, a zero eigenvalue)
at a zero–Hopf point (`Δ₃ = 0`, `Line.VSMLPF.Model.charpoly_fold_eval_zeroHopf`; at the
Bogdanov–Takens damping `a₁ = 0` this is `a₂ (a₄ a₃ − a₂) = 0`: a triple zero `a₂ = 0` or a
zero–Hopf pair). The Bogdanov–Takens points with `Δ₃ ≠ 0` are decided
(`Line.VSMLPF.mem_den_unstable_of_fold_of_det3_ne`). -/
def Model.FoldDegenerate (m : Model) : Prop :=
  Meets m .balanced ∧ m.K = 0 ∧
    Criteria.quinticHurwitzDet3 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q) (m.g.coeff1 m.Q)
      (m.g.coeff0 m.Q) = 0

/-- **The fold is a saddle-node**
(`Dynamics.CenterManifold.unstable_of_foldCoeff_ne_zero_of_charpoly`): a balanced physical model
at a fold `K = 0` whose other four eigenvalues are stable (`a₁ > 0`, `Δ₃ > 0`: the quartic
cofactor `s⁴ + a₄ s³ + a₃ s² + a₂ s + a₁` is Hurwitz) is unstable. Its fold coefficient
`a = (P_ref − c₀)/(2 (D − D_line))` (`Line.VSMLPF.Model.foldCoeff_fold`) does not vanish there
(`Line.VSMLPF.Model.foldCoeff_fold_ne_zero`; `a₁ > 0` gives `D ≠ D_line`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold (m : Model) (hp : Meets m .physical)
    (hb : Meets m .balanced) (hK : m.K = 0) (h1 : 0 < m.g.coeff1 m.Q)
    (h3 : 0 < Criteria.quinticHurwitzDet3 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q)
      (m.g.coeff1 m.Q) (m.g.coeff0 m.Q)) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Unstable m.field 0
  obtain ⟨hN, hM, hD0, hω⟩ := hp
  have hL := hN.L.ne'
  have hZ := hN.absSq_pos
  have hD : m.g.D ≠ m.g.Dline := by
    intro hD
    rw [m.coeff1_fold hL hZ hK, hD, sub_self] at h1
    simp at h1
  have h0 : m.g.coeff0 m.Q = 0 := by rw [m.coeff0_eq hL hZ, hK]; simp
  rw [h0] at h3
  unfold Criteria.quinticHurwitzDet3 Criteria.quinticHurwitzDet2 at h3
  have hρ : 0 < m.g.ρ := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
    rw [this]; exact div_pos hZ (pow_pos hN.L 2)
  have hσ : 0 ≤ m.g.σ := div_nonneg hN.R hN.L.le
  have h4 : 0 < m.g.coeff4 := by unfold coeff4; positivity
  have h3' : 0 < m.g.coeff3 := by unfold coeff3; positivity
  have h2 : 0 < m.g.coeff2 m.Q := by
    by_contra h2
    push Not at h2
    nlinarith [mul_pos h4 h3', mul_pos (pow_pos h4 2) h1]
  have hF : ContDiff ℝ 2 m.field := (m.g.contDiff_field (k := 2)).comp
    (contDiff_id.add contDiff_const)
  have hF0 : m.field 0 = 0 := by
    show m.g.field (0 + m.point) = 0
    rw [zero_add]
    exact (m.field_point_eq_zero_iff hM.ne' hω.ne' hL hZ.ne').mpr hb
  refine Dynamics.CenterManifold.unstable_of_foldCoeff_ne_zero_of_charpoly hF hF0
    (m.isNullPair_fold ⟨hN, hM, hD0, hω⟩ hK hD) (m.charpoly_fold hL hZ hK) ?_
    (m.foldCoeff_fold_ne_zero ⟨hN, hM, hD0, hω⟩ hK hD)
  intro s hs
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C] at hs
  exact Criteria.quartic_roots_re_neg_of h4 h2 h1 (by nlinarith) s hs

/-- **The fold decided off its degenerate set**: a balanced physical model at a fold `K = 0` with
`a₁ ≠ 0` (off the Bogdanov–Takens damping `D = D_line`) and `Δ₃ ≠ 0` (off the zero–Hopf points)
is unstable: a strict quintic Routh violation (`Line.VSMLPF.mem_den_unstable`), or the
saddle-node law (`Line.VSMLPF.mem_den_unstable_of_fold`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold_of_ne (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hK : m.K = 0)
    (h1 : m.g.coeff1 m.Q ≠ 0)
    (h3 : Criteria.quinticHurwitzDet3 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q) (m.g.coeff1 m.Q)
      (m.g.coeff0 m.Q) ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  by_cases hv : m.RouthViolation
  · exact mem_den_unstable m hp hb hv
  unfold Model.RouthViolation Criteria.QuinticRouthViolation at hv
  push Not at hv
  obtain ⟨-, -, -, v1, -, -, v3, -⟩ := hv
  exact mem_den_unstable_of_fold m hp hb hK (lt_of_le_of_ne v1 (Ne.symm h1))
    (lt_of_le_of_ne v3 (Ne.symm h3))

/-! ## The Bogdanov–Takens point -/

/-- **The Bogdanov–Takens point with a power filter is unstable** (the cusp,
`NormalForm.BogdanovTakens.IsBTChain.unstable_of_coeffA_ne_zero`): a balanced physical model at a
fold `K = 0` with `D = D_line`, `n₅ = btInertia > 0` and `a₂ < a₄ a₃` (the cofactor
`s³ + a₄ s² + a₃ s + a₂` of `det(sI − J) = s² (s³ + a₄ s² + a₃ s + a₂)` is Hurwitz:
`a₂ = ω_c ρ n₅/M > 0`, `Line.VSMLPF.Model.coeff2_of_bt`) is unstable. Its coefficient
`a = (P(δ*) − c₀)/(2 n₅)` (`Line.VSMLPF.Model.coeff_of_bt`) never vanishes there
(`P(δ*) − c₀ = ± A`): no codimension-three point `a = 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_bt (m : Model) (hp : Meets m .physical)
    (hb : Meets m .balanced) (hK : m.K = 0) (hD : m.g.D = m.g.Dline)
    (hn : 0 < m.g.btInertia) (h42 : m.g.coeff2 m.Q < m.g.coeff4 * m.g.coeff3) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  change Unstable m.field 0
  obtain ⟨hN, hM, hD0, hω⟩ := hp
  have hL := hN.L.ne'
  have hZ := hN.absSq_pos
  have hV : m.g.E * m.g.V ≠ 0 := (mul_pos hN.E hN.V).ne'
  obtain ⟨p₀, p₁, hch'⟩ := m.exists_isBTChain_of_bt hM.ne' hω.ne' hL hZ hV hK hD hn.ne'
  have hch : IsBTChain (fderiv ℝ m.field 0) (WithLp.toLp 2 m.btTangent)
      (WithLp.toLp 2 m.btChain) p₀ p₁ := by rw [lf_fderiv, ← m.fderiv_point]; exact hch'
  have hF : ContDiff ℝ 2 m.field := (m.g.contDiff_field (k := 2)).comp
    (contDiff_id.add contDiff_const)
  have hF0 : m.field 0 = 0 := by
    show m.g.field (0 + m.point) = 0
    rw [zero_add]
    exact (m.field_point_eq_zero_iff hM.ne' hω.ne' hL hZ.ne').mpr hb
  have hker : ∀ v, fderiv ℝ m.field 0 v = 0 → ∃ s : ℝ, v = s • WithLp.toLp 2 m.btTangent := by
    intro v hv
    rw [lf_fderiv] at hv
    have hv' : m.jac *ᵥ (WithLp.ofLp v) = 0 := by
      have := congrArg WithLp.ofLp hv
      simpa [Matrix.ofLp_toEuclideanCLM] using this
    have he := m.eq_smul_btTangent_of_mulVec_eq_zero hM.ne' hL hZ hv'
    refine ⟨v 0, ?_⟩
    ext i
    have := congrFun he i
    simpa using this
  have h1 : m.g.coeff1 m.Q = 0 := by rw [m.coeff1_fold hL hZ hK, hD, sub_self]; simp
  have hchar : (NormalForm.LyapunovCoefficient.cmat (fderiv ℝ m.field 0)).charpoly =
      X ^ 2 * (X ^ 3 + C ((m.g.coeff4 : ℝ) : ℂ) * X ^ 2 + C ((m.g.coeff3 : ℝ) : ℂ) * X +
        C ((m.g.coeff2 m.Q : ℝ) : ℂ)) := by
    have h := m.charpoly_fold hL hZ hK
    rw [h1] at h
    rw [show NormalForm.LyapunovCoefficient.cmat (fderiv ℝ m.field 0) = jacobianC m.field 0
      from rfl, h]
    simp
    ring
  have hσ : 0 ≤ m.g.σ := div_nonneg hN.R hN.L.le
  have h4 : 0 < m.g.coeff4 := by unfold coeff4; positivity
  have hρ : 0 < m.g.ρ := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
    rw [this]; exact div_pos hZ (pow_pos hN.L 2)
  have h2 : 0 < m.g.coeff2 m.Q := by
    rw [m.coeff2_of_bt ⟨hN, hM, hD0, hω⟩ hK hD]; positivity
  have hr : ∀ s : ℂ, (X ^ 3 + C ((m.g.coeff4 : ℝ) : ℂ) * X ^ 2 + C ((m.g.coeff3 : ℝ) : ℂ) * X +
      C ((m.g.coeff2 m.Q : ℝ) : ℂ)).eval s = 0 → s.re < 0 := by
    intro s hs
    simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C] at hs
    exact Criteria.cubic_roots_re_neg_of h4 h2 h42 s hs
  refine hch.unstable_of_coeffA_ne_zero hF hF0 hker hchar hr ?_
  obtain ⟨ha, -⟩ := m.coeff_of_bt hM.ne' hω.ne' hL hZ hV hK hD hn.ne' hch'
  rw [coeffA, lf_fderiv2, ← coeffA, ha]
  exact div_ne_zero (lf_P_sub_c0_ne ⟨hN, hM, hD0, hω⟩ hK) (mul_ne_zero two_ne_zero hn.ne')

/-- **The fold decided off the zero–Hopf points**: a balanced physical model at a fold `K = 0`
with `Δ₃ ≠ 0` is unstable; hence at a fold the operating point is never locally asymptotically
stable off `Line.VSMLPF.Model.FoldDegenerate`. Off the Bogdanov–Takens damping (`a₁ ≠ 0`) this
is `Line.VSMLPF.mem_den_unstable_of_fold_of_ne`; at it (`a₁ = 0`, `D = D_line`)
`Δ₃ = a₂ (a₄ a₃ − a₂)`: a strict quintic Routh violation (`Line.VSMLPF.mem_den_unstable`), or
`a₂ > 0`, `a₄ a₃ > a₂` and the Bogdanov–Takens cusp (`Line.VSMLPF.mem_den_unstable_of_bt`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold_of_det3_ne (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced) (hK : m.K = 0)
    (h3 : Criteria.quinticHurwitzDet3 m.g.coeff4 m.g.coeff3 (m.g.coeff2 m.Q) (m.g.coeff1 m.Q)
      (m.g.coeff0 m.Q) ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  by_cases h1 : m.g.coeff1 m.Q = 0
  swap
  · exact mem_den_unstable_of_fold_of_ne m hp hb hK h1 h3
  by_cases hv : m.RouthViolation
  · exact mem_den_unstable m hp hb hv
  obtain ⟨hN, hM, hD0, hω⟩ := hp
  have hL := hN.L.ne'
  have hZ := hN.absSq_pos
  have hρ : 0 < m.g.ρ := by
    have : m.g.ρ = m.g.absSq / m.g.L ^ 2 := by
      simp only [Network.ρ, Network.σ, Network.absSq]; field_simp
    rw [this]; exact div_pos hZ (pow_pos hN.L 2)
  have hD : m.g.D = m.g.Dline := by
    rw [m.coeff1_fold hL hZ hK] at h1
    have h' : m.g.ρ * (m.g.D - m.g.Dline) / m.g.M = 0 :=
      (mul_eq_zero.mp h1).resolve_left hω.ne'
    rw [div_eq_zero_iff, or_iff_left hM.ne'] at h'
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hρ.ne')
  have h0 : m.g.coeff0 m.Q = 0 := by rw [m.coeff0_eq hL hZ, hK]; simp
  unfold Model.RouthViolation Criteria.QuinticRouthViolation at hv
  push Not at hv
  obtain ⟨-, -, v2, -, -, vd2, -, -⟩ := hv
  rw [h0, h1] at h3
  unfold Criteria.quinticHurwitzDet3 at h3
  unfold Criteria.quinticHurwitzDet2 at vd2 h3
  have h3' : m.g.coeff2 m.Q * (m.g.coeff4 * m.g.coeff3 - m.g.coeff2 m.Q) ≠ 0 := by
    intro h; apply h3; rw [h]; ring
  have h2 : 0 < m.g.coeff2 m.Q :=
    lt_of_le_of_ne v2 (fun h => h3' (by rw [← h, zero_mul]))
  have h42 : m.g.coeff2 m.Q < m.g.coeff4 * m.g.coeff3 :=
    lt_of_le_of_ne (sub_nonneg.mp vd2) (fun h => h3' (by rw [h, sub_self, mul_zero]))
  have hn : 0 < m.g.btInertia := by
    rw [m.coeff2_of_bt ⟨hN, hM, hD0, hω⟩ hK hD] at h2
    have hc : 0 < m.g.ωc * m.g.ρ := mul_pos hω hρ
    have := (div_pos_iff_of_pos_right hM).mp h2
    exact (pos_iff_pos_of_mul_pos this).mp hc
  exact mem_den_unstable_of_bt m ⟨hN, hM, hD0, hω⟩ hb hK hD hn h42

end VSMLPF
end powerlib.GFM.Line
