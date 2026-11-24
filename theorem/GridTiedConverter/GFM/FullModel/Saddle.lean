import theorem.GridTiedConverter.GFM.FullModel.Basic
import theorem.LinearAlgebra.SchurDeterminant
import theorem.Criteria.Hurwitz
import theorem.Spectral.Family
import theorem.GridTiedConverter.GFM.QVDroop
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-! # The 13-state grid-forming converter: fast block, Schur identity and the saddle branch

Model boundary.
The 13-state model of `theorem/GridTiedConverter/GFM/FullModel/Basic.lean` (state order
`(i, v_c, i_g, ξ, ζ, δ, Δω, Q_f)` in dq components, system frame for the plant, controller frame
for the integrators, currents out of the converter positive, export-positive per-unit power).
Continuous time, autonomous, no input. Level: the Jacobian of the field at an equilibrium and
local instability of the equilibrium; no statement about the stable branch, about time-scale
separation or about trajectories of the reduced model.

Scaffolds of the readings of the reduced models: the swing machine,
`theorem/GridTiedConverter/GFM/FullModel/FullModelSwing.agda`; the reduced Q–V droop model,
`theorem/GridTiedConverter/GFM/FullModel/FullModelQVDroop.agda`.

Source: GFM counterpart study, full-order model note (t5: "det of the fast block =
K_ic²K_iv²|Z_g+Z_v|²/(L_fC_fL_g)² > 0"; "reduced Jacobian = Schur complement; det J = det J_ff ·
det J_red, det J_ff > 0 ⇒ reduced saddle branch unstable in full model for any gains") and
equilibria note (t6 §b, Q–V droop: "det J = −(ω_q/M)(1 + n_q Q_E) P̃′, P̃′ < 0 ⇒ unstable", and
§c); the reduced Q–V droop model and its descending branch,
`theorem/GridTiedConverter/GFM/QVDroop.lean`; Schur determinant identity (Horn–Johnson,
*Matrix Analysis*, §0.8.5); determinant of a complex matrix read over `ℝ` (Silvester,
"Determinants of block matrices", Math. Gazette 84 (2000)).

Results.
* `fastRows_add`: the ten fast rows are affine in the fast states, with the complex `5 × 5`
  coefficient matrix `fastMatrix δ` (rows and columns `i, v_c, i_g, ξ, ζ`) that depends on the
  angle only; `hasDerivAt_fast`: the fast–fast partial derivatives of the field are the real
  `10 × 10` block `fastBlock δ`, the realification of `fastMatrix δ`.
* `det_fastMatrix`: `det fastMatrix δ = −K_ic K_iv Z_t/(L_f C_f L_g)`, `Z_t = Z_g + Z_v`;
  `det_fastBlock`: `det fastBlock δ = K_ic² K_iv² |Z_t|²/(L_f C_f L_g)²` (`Matrix.det_det`), so
  `det_fastBlock_pos`: it is positive under the nondegeneracy hypotheses, for every gain — no
  LC–line resonance condition enters.
* `det_jacobian_qssState`: at every quasi-steady point, with or without droop, the Jacobian of the
  13-state field has `det J = det fastBlock · det J_red` — the generic law
  `LinearAlgebra.det_eq_det_fast_mul_det_reduced` — where `J_red = reducedJacobian δ Q_f` is the
  Jacobian of the reduced field (`hasFDerivAt_reducedField`; its `Q_f` column carries the
  `E`-partials `powerSlopeE`, `reactiveSlopeE` of the quasi-steady powers through
  `∂E/∂Q_f = −n_q`); `det_reducedJacobian`: `det J_red = −ω_q droopSlope/M`, with the
  droop-corrected slope `droopSlope = P_δ (1 + n_q Q_E) − n_q P_E Q_δ` (minus the Jacobian
  determinant of the static balance in `(δ, Q_f)`; `droopSlope_eq_powerSlope`: `P_δ` without
  droop).
* `powerSlope_eq_syncCoeff` (`Z_v = 0`): the slope `∂P/∂δ` of the quasi-steady power–angle curve
  is the synchronizing coefficient of the reduced swing machine `Params.swingParams`;
  `reducedField_eq_qvDroop` (`Z_v = 0`, any droop): the reduced field is the field of the reduced
  Q–V droop model `Params.qvDroop` (`theorem/GridTiedConverter/GFM/QVDroop.lean`).
* `contDiff_field`, `contDiff_graph`: the field and the quasi-steady graph `graph` are `C¹`.

Family and connection conclusions.
* `family : Family Model Spectral.Requirement 13 0`: a complete system is a parameter set with a
  selected quasi-steady point `qssState δ* 0 Q*` (`Model`), read as the field translated so that
  the point is the origin (`Spectral.localFamily`). Requirements: `stable` — none is claimed
  (`False`: stability of the full model at the stable branch of the reduction is not established
  here; the determinant identity decides only the sign of `det J`); `unstable` — `Model.Saddle`:
  nondegenerate fast block, `M, ω_q > 0`, a balanced point at the droop EMF and a negative
  droop-corrected slope (without droop: a negative slope of the power–angle curve). Local
  sentences translate into `stable` (no model meets it: unavailable coverage), instability into
  `unstable`, passivity into nothing, the rest into the whole (inconsistent) language.
  `chain_le_semantics` proves every translation sound.
* `mem_den_unstable` (connection): an equilibrium on the saddle branch, `droopSlope < 0`, is
  unstable in the full 13-state model for every choice of the controller gains and of the Q–V
  droop gain (`det J = det fastBlock · (−ω_q droopSlope/M) > 0` in dimension 13,
  `Criteria.unstable_of_jacobian_det`); `mem_den_unstable_of_swing` (connection, `Z_v = 0`,
  `n_q = 0`): a balanced angle with negative synchronizing coefficient of the reduced swing
  reading `Params.swingParams` is unstable in the full model, for every gain;
  `mem_den_unstable_of_qvDroop` (connection, `Z_v = 0`, droop in its physical range): a physical
  equilibrium on the descending branch `P̃′ < 0` of the reduced Q–V droop model
  `Params.qvDroop` is unstable in the full model, for every gain.
-/

noncomputable section
namespace powerlib.GFM.FullModel
open Complex ComplexConjugate Matrix
open powerlib.Dynamics (State)

/-- The real or imaginary part (`c = 0`, `1`) of a complex number. -/
def component (c : Fin 2) (z : ℂ) : ℝ := ![z.re, z.im] c

/-- The complex unit of the `c`-th real coordinate of a phasor: `1` for `d`, `j` for `q`. -/
def axisUnit (c : Fin 2) : ℂ := ![1, I] c

/-- The splitting of the 13 coordinates into the fast phasor coordinates (phasor `a`, component
`c`, coordinate `2a + c`) and the slow ones `(δ, Δω, Q_f)` (coordinates `10, 11, 12`). -/
def split : Fin 13 ≃ (Fin 5 × Fin 2) ⊕ Fin 3 :=
  (finSumFinEquiv (m := 10) (n := 3)).symm.trans
    (Equiv.sumCongr (finProdFinEquiv (m := 5) (n := 2)).symm (Equiv.refl (Fin 3)))

/-- The five fast phasors of a state. -/
def fastPart (y : State 13) : Fin 5 → ℂ :=
  ![phasor y 0 1, phasor y 2 3, phasor y 4 5, phasor y 6 7, phasor y 8 9]

namespace Params

variable (p : Params)

/-- The five complex fast rows `(i̇, v̇_c, i̇_g, ξ̇, ζ̇)`. -/
def fastRows (x : State 13) : Fin 5 → ℂ :=
  ![p.convRow x, p.capRow x, p.lineRow x, p.currentIntRow x, p.voltageIntRow x]

/-- The complex coefficient matrix of the fast rows in the fast phasors `(i, v_c, i_g, ξ, ζ)` at
the angle `δ` (`a_v = −K_pv + k_dv jω₀C_f`, `a_g = k_ff − K_pv Z_v`). -/
def fastMatrix (δ : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  let av : ℂ := -p.Kpv + p.kdv * (p.Bf * I)
  let ag : ℂ := p.kff - p.Kpv * p.Zv
  !![-(p.Kpc + p.Rf) / p.Lf, p.Kpc * av / p.Lf, p.Kpc * ag / p.Lf, p.Kic * ej δ / p.Lf,
      p.Kpc * p.Kiv * ej δ / p.Lf;
    1 / p.Cf, -(p.Bf * I) / p.Cf, -1 / p.Cf, 0, 0;
    0, 1 / p.Lg, -p.Zg / p.Lg, 0, 0;
    -ej (-δ), av * ej (-δ), ag * ej (-δ), 0, p.Kiv;
    0, -ej (-δ), -(p.Zv * ej (-δ)), 0, 0]

/-- The fast rows are affine in the fast states: a perturbation `y` of the fast coordinates only
changes them by `fastMatrix δ` applied to its phasors. -/
@[tmio M, powerlib_domain] theorem fastRows_add (x y : State 13) (h10 : y 10 = 0)
    (h12 : y 12 = 0) :
    p.fastRows (x + y) = p.fastRows x + p.fastMatrix (x 10) *ᵥ fastPart y := by
  have hne : ej (x 10) ≠ 0 := Complex.exp_ne_zero _
  have he' : ej (-x 10) = (ej (x 10))⁻¹ := by simp [ej, Complex.exp_neg]
  funext a
  fin_cases a <;>
    simp [fastRows, fastMatrix, fastPart, convRow, capRow, lineRow, currentIntRow,
      voltageIntRow, uBridge, uCtrl, iRef, vRef, emf, phasor, h10, h12, Zf_eq] <;>
    (try rw [he']) <;> field_simp <;> ring

/-- The real `10 × 10` fast block: the realification of `fastMatrix δ`, each complex entry
`z = a + jb` read as `[[a, −b], [b, a]]` (`Algebra.leftMulMatrix Complex.basisOneI`), indexed by
(phasor, component). -/
def fastBlock (δ : ℝ) : Matrix (Fin 5 × Fin 2) (Fin 5 × Fin 2) ℝ :=
  Matrix.comp (Fin 5) (Fin 5) (Fin 2) (Fin 2) ℝ
    ((p.fastMatrix δ).map (Algebra.leftMulMatrix Complex.basisOneI))

/-- The complex determinant of the fast rows, `det fastMatrix δ = −K_ic K_iv Z_t/(L_f C_f L_g)`,
independent of the angle and of `K_pv, K_pc, k_ff, k_dv`. -/
@[tmio M, powerlib_domain] theorem det_fastMatrix (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (δ : ℝ) :
    (p.fastMatrix δ).det = -(p.Kic * p.Kiv * p.Zt / (p.Lf * p.Cf * p.Lg)) := by
  have he : ej (-δ) * ej δ = 1 := by simp [ej, Complex.exp_neg]
  have hLf' : (p.Lf : ℂ) ≠ 0 := by exact_mod_cast hLf
  have hCf' : (p.Cf : ℂ) ≠ 0 := by exact_mod_cast hCf
  have hLg' : (p.Lg : ℂ) ≠ 0 := by exact_mod_cast hLg
  simp only [fastMatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_unique,
    Fin.sum_univ_zero]
  simp [Matrix.submatrix, Fin.succAbove, Fin.lt_def, Zt]
  field_simp
  linear_combination (-(p.Kic * p.Kiv * (p.Zg + p.Zv))) * he

/-- The determinant of the real fast block, `K_ic² K_iv² |Z_g + Z_v|²/(L_f C_f L_g)²`: the
determinant of a complex matrix read over `ℝ` is the squared modulus of its complex determinant
(`Matrix.det_det`, Silvester). -/
@[tmio M, powerlib_domain] theorem det_fastBlock (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (δ : ℝ) :
    (p.fastBlock δ).det =
      p.Kic ^ 2 * p.Kiv ^ 2 * Complex.normSq p.Zt / (p.Lf * p.Cf * p.Lg) ^ 2 := by
  have h : ((Algebra.leftMulMatrix Complex.basisOneI) (p.fastMatrix δ).det).det =
      (Matrix.comp (Fin 5) (Fin 5) (Fin 2) (Fin 2) ℝ
        ((p.fastMatrix δ).map (Algebra.leftMulMatrix Complex.basisOneI))).det :=
    Matrix.det_det (p.fastMatrix δ) (Algebra.leftMulMatrix Complex.basisOneI).toRingHom
  rw [fastBlock, ← h, Algebra.leftMulMatrix_complex, Matrix.det_fin_two_of,
    p.det_fastMatrix hLf hCf hLg]
  have hn : ∀ z : ℂ, z.re * z.re - -z.im * z.im = Complex.normSq z := fun z => by
    rw [Complex.normSq_apply]; ring
  rw [hn, Complex.normSq_neg, Complex.normSq_div, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_mul, Complex.normSq_mul]
  simp only [Complex.normSq_ofReal]
  ring

/-- The fast block is nonsingular — its determinant is positive — whenever `L_f, C_f, L_g, K_ic,
K_iv ≠ 0` and `Z_g + Z_v ≠ 0`, for every value of the other gains and of the angle. -/
@[tmio M, powerlib_domain] theorem det_fastBlock_pos (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0) (hZt : p.Zt ≠ 0) (δ : ℝ) :
    0 < (p.fastBlock δ).det := by
  rw [p.det_fastBlock hLf hCf hLg]
  have := Complex.normSq_pos.mpr hZt
  have : p.Lf * p.Cf * p.Lg ≠ 0 := mul_ne_zero (mul_ne_zero hLf hCf) hLg
  positivity

end Params

/-- Component `c` of the fast phasor `a` is the coordinate `2a + c`. -/
@[tmio M, powerlib_domain] theorem split_symm_inl (a : Fin 5) (c : Fin 2) :
    split.symm (.inl (a, c)) = ⟨2 * a.val + c.val, by omega⟩ := by
  fin_cases a <;> fin_cases c <;> rfl

namespace Params

variable (p : Params)

/-- The fast coordinates of the field are the real and imaginary parts of the fast rows. -/
@[tmio M, powerlib_domain] theorem field_split_inl (x : State 13) (a : Fin 5) (c : Fin 2) :
    p.field x (split.symm (.inl (a, c))) = component c (p.fastRows x a) := by
  rw [split_symm_inl]; fin_cases a <;> fin_cases c <;> rfl

/-- The phasors of a perturbation along one fast coordinate. -/
@[tmio M, powerlib_domain] private theorem fastPart_single (t : ℝ) (b : Fin 5) (c : Fin 2) :
    fastPart (t • EuclideanSpace.single (split.symm (.inl (b, c))) (1 : ℝ)) =
      Pi.single b ((t : ℂ) * axisUnit c) := by
  rw [split_symm_inl]
  funext a
  fin_cases b <;> fin_cases c <;> fin_cases a <;> simp [fastPart, phasor, axisUnit]

/-- The fast–fast partial derivatives of the 13-state field at any state are the entries of the
fast block at its angle. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_fast (x : State 13) (i j : Fin 5 × Fin 2) :
    HasDerivAt (fun t : ℝ => p.field (x + t • EuclideanSpace.single (split.symm (.inl j)) 1)
      (split.symm (.inl i))) (p.fastBlock (x 10) i j) 0 := by
  obtain ⟨a, c'⟩ := i
  obtain ⟨b, c⟩ := j
  have hne : ∀ k : Fin 13, 10 ≤ k.val → (split.symm (.inl (b, c))) ≠ k := by
    intro k hk h
    rw [split_symm_inl] at h
    have := congrArg Fin.val h
    simp at this
    omega
  have hy : ∀ (t : ℝ) (k : Fin 13), 10 ≤ k.val →
      (t • EuclideanSpace.single (split.symm (.inl (b, c))) (1 : ℝ)) k = 0 := by
    intro t k hk
    simp [(hne k hk).symm]
  have key : ∀ t : ℝ, p.field (x + t • EuclideanSpace.single (split.symm (.inl (b, c))) 1)
      (split.symm (.inl (a, c'))) =
        component c' (p.fastRows x a) +
          t * component c' (p.fastMatrix (x 10) a b * axisUnit c) := by
    intro t
    rw [p.field_split_inl, p.fastRows_add x _ (hy t 10 (by norm_num)) (hy t 12 (by norm_num)),
      fastPart_single, Matrix.mulVec_single]
    fin_cases c' <;> simp [component] <;> ring
  have hblock : p.fastBlock (x 10) (a, c') (b, c) =
      component c' (p.fastMatrix (x 10) a b * axisUnit c) := by
    simp only [fastBlock, Matrix.comp_apply, Matrix.map_apply, Algebra.leftMulMatrix_complex]
    fin_cases c' <;> fin_cases c <;> simp [component, axisUnit]
  rw [funext key, hblock]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const
    (component c' (p.fastMatrix (x 10) a b * axisUnit c))).const_add (component c' (p.fastRows x a))

/-! ### Smoothness of the field and of the quasi-steady graph -/

@[tmio T, powerlib_foundation] private theorem contDiff_ofReal {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun x : ℝ => (x : ℂ)) :=
  Complex.ofRealCLM.contDiff

attribute [local fun_prop] contDiff_ofReal

@[tmio T, powerlib_foundation] private theorem contDiff_re {f : State 13 → ℂ}
    (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 fun x => (f x).re :=
  Complex.reCLM.contDiff.comp hf

@[tmio T, powerlib_foundation] private theorem contDiff_im {f : State 13 → ℂ}
    (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 fun x => (f x).im :=
  Complex.imCLM.contDiff.comp hf

/-- The 13-state field is `C¹`. -/
@[tmio M, powerlib_domain] theorem contDiff_field : ContDiff ℝ 1 p.field := by
  have h0 : ContDiff ℝ 1 p.convRow := by
    unfold convRow uBridge uCtrl iRef vRef emf ej
    simp only [convCurrent, capVoltage, lineCurrent, currentInt, voltageInt, phasor]; fun_prop
  have h1 : ContDiff ℝ 1 p.capRow := by
    unfold capRow; simp only [capVoltage, lineCurrent, phasor]; fun_prop
  have h2 : ContDiff ℝ 1 p.lineRow := by
    unfold lineRow; simp only [capVoltage, lineCurrent, phasor]; fun_prop
  have h3 : ContDiff ℝ 1 p.currentIntRow := by
    unfold currentIntRow iRef vRef emf ej
    simp only [convCurrent, capVoltage, lineCurrent, voltageInt, phasor]; fun_prop
  have h4 : ContDiff ℝ 1 p.voltageIntRow := by
    unfold voltageIntRow vRef emf ej
    simp only [capVoltage, lineCurrent, phasor]; fun_prop
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · exact contDiff_re h0
  · exact contDiff_im h0
  · exact contDiff_re h1
  · exact contDiff_im h1
  · exact contDiff_re h2
  · exact contDiff_im h2
  · exact contDiff_re h3
  · exact contDiff_im h3
  · exact contDiff_re h4
  · exact contDiff_im h4
  · exact Dynamics.contDiff_coord 11
  · show ContDiff ℝ 1 fun x : State 13 => (p.Pref - Pe x - p.D * x 11) / p.M
    simp only [Pe, Transform.pq, Matrix.cons_val_zero, Matrix.cons_val_one]; fun_prop
  · show ContDiff ℝ 1 fun x : State 13 => p.ωq * (Qe x - x 12)
    simp only [Qe, Transform.pq, Matrix.cons_val_zero, Matrix.cons_val_one]; fun_prop

/-- The quasi-steady graph `(δ, Δω, Q_f) ↦ qssState δ Δω Q_f`. -/
def graph (s : State 3) : State 13 := p.qssState (s 0) (s 1) (s 2)

@[tmio T, powerlib_foundation] private theorem contDiff_re3 {f : State 3 → ℂ}
    (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 fun x => (f x).re :=
  Complex.reCLM.contDiff.comp hf

@[tmio T, powerlib_foundation] private theorem contDiff_im3 {f : State 3 → ℂ}
    (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 fun x => (f x).im :=
  Complex.imCLM.contDiff.comp hf

/-- The quasi-steady graph is `C¹`. -/
@[tmio M, powerlib_domain] theorem contDiff_graph : ContDiff ℝ 1 p.graph := by
  have hg : ContDiff ℝ 1 fun s : State 3 => p.igQ (s 0) (p.emf (s 2)) := by
    unfold igQ emf ej; fun_prop
  have hv : ContDiff ℝ 1 fun s : State 3 => p.vcQ (s 0) (p.emf (s 2)) := by
    unfold vcQ igQ emf ej; fun_prop
  have hi : ContDiff ℝ 1 fun s : State 3 => p.iQ (s 0) (p.emf (s 2)) := by
    unfold iQ vcQ igQ emf ej; fun_prop
  have hξ : ContDiff ℝ 1 fun s : State 3 => p.xiQ (s 0) (p.emf (s 2)) := by
    unfold xiQ iQ vcQ igQ emf ej; fun_prop
  have hζ : ContDiff ℝ 1 fun s : State 3 => p.zeQ (s 0) (p.emf (s 2)) := by
    unfold zeQ vcQ igQ emf ej; fun_prop
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · exact contDiff_re3 hi
  · exact contDiff_im3 hi
  · exact contDiff_re3 hv
  · exact contDiff_im3 hv
  · exact contDiff_re3 hg
  · exact contDiff_im3 hg
  · exact contDiff_re3 hξ
  · exact contDiff_im3 hξ
  · exact contDiff_re3 hζ
  · exact contDiff_im3 hζ
  · exact Dynamics.contDiff_coord 0
  · exact Dynamics.contDiff_coord 1
  · exact Dynamics.contDiff_coord 2

/-! ### The reduced Jacobian and the Schur identity -/

/-- The slope `∂P/∂E` of the quasi-steady power in the internal EMF,
`(2E R_g + V((R_v − R_g) cos δ + X_t sin δ))/|Z_t|²`. -/
def powerSlopeE (δ E : ℝ) : ℝ :=
  (2 * E * p.Rg + p.V * ((p.Rv - p.Rg) * Real.cos δ + p.Xt * Real.sin δ)) / (p.Rt ^ 2 + p.Xt ^ 2)

/-- The slope `∂Q/∂E` of the quasi-steady reactive power in the internal EMF,
`(2E X_g + V((X_v − X_g) cos δ − R_t sin δ))/|Z_t|²`, `X_g = ω₀L_g`. -/
def reactiveSlopeE (δ E : ℝ) : ℝ :=
  (2 * E * (p.ω0 * p.Lg) + p.V * ((p.Xv - p.ω0 * p.Lg) * Real.cos δ - p.Rt * Real.sin δ)) /
    (p.Rt ^ 2 + p.Xt ^ 2)

/-- The quasi-steady power along two `C¹` coordinates `δ = u`, `E = w` of the reduced state: its
derivative has the partials `∂P/∂δ = powerSlope`, `∂P/∂E = powerSlopeE`. -/
@[tmio M, powerlib_domain] private theorem hasFDerivAt_Pq_comp (hZt : p.Zt ≠ 0)
    {u w : State 3 → ℝ} {u' w' : State 3 →L[ℝ] ℝ} {y : State 3} (hu : HasFDerivAt u u' y)
    (hw : HasFDerivAt w w' y) :
    HasFDerivAt (fun z => p.Pq (u z) (w z))
      (p.powerSlope (u y) (w y) • u' + p.powerSlopeE (u y) (w y) • w') y := by
  have hf : (fun z => p.Pq (u z) (w z)) = fun z => (w z * w z * p.Rg + -(p.Rv * p.V ^ 2) +
      w z * p.V * ((p.Rv - p.Rg) * Real.cos (u z) + p.Xt * Real.sin (u z))) *
        (p.Rt ^ 2 + p.Xt ^ 2)⁻¹ := by
    funext z; rw [p.Pq_eq hZt]; ring
  rw [hf]
  have hc := (Real.hasDerivAt_cos (u y)).comp_hasFDerivAt y hu
  have hs := (Real.hasDerivAt_sin (u y)).comp_hasFDerivAt y hu
  have h := ((((hw.fun_mul hw).mul_const p.Rg).add_const (-(p.Rv * p.V ^ 2))).add
    ((hw.mul_const p.V).fun_mul ((hc.const_mul (p.Rv - p.Rg)).add
      (hs.const_mul p.Xt)))).mul_const (p.Rt ^ 2 + p.Xt ^ 2)⁻¹
  refine h.congr_fderiv ?_
  ext v
  simp [powerSlope, powerSlopeE]
  ring

/-- The quasi-steady reactive power along two `C¹` coordinates `δ = u`, `E = w`: partials
`∂Q/∂δ = reactiveSlope`, `∂Q/∂E = reactiveSlopeE`. -/
@[tmio M, powerlib_domain] private theorem hasFDerivAt_Qq_comp (hZt : p.Zt ≠ 0)
    {u w : State 3 → ℝ} {u' w' : State 3 →L[ℝ] ℝ} {y : State 3} (hu : HasFDerivAt u u' y)
    (hw : HasFDerivAt w w' y) :
    HasFDerivAt (fun z => p.Qq (u z) (w z))
      (p.reactiveSlope (u y) (w y) • u' + p.reactiveSlopeE (u y) (w y) • w') y := by
  have hf : (fun z => p.Qq (u z) (w z)) = fun z => (w z * w z * (p.ω0 * p.Lg) +
      -(p.Xv * p.V ^ 2) + w z * p.V * ((p.Xv - p.ω0 * p.Lg) * Real.cos (u z) +
        -p.Rt * Real.sin (u z))) * (p.Rt ^ 2 + p.Xt ^ 2)⁻¹ := by
    funext z; rw [p.Qq_eq hZt]; ring
  rw [hf]
  have hc := (Real.hasDerivAt_cos (u y)).comp_hasFDerivAt y hu
  have hs := (Real.hasDerivAt_sin (u y)).comp_hasFDerivAt y hu
  have h := ((((hw.fun_mul hw).mul_const (p.ω0 * p.Lg)).add_const (-(p.Xv * p.V ^ 2))).add
    ((hw.mul_const p.V).fun_mul ((hc.const_mul (p.Xv - p.ω0 * p.Lg)).add
      (hs.const_mul (-p.Rt))))).mul_const (p.Rt ^ 2 + p.Xt ^ 2)⁻¹
  refine h.congr_fderiv ?_
  ext v
  simp [reactiveSlope, reactiveSlopeE]
  ring

/-- The Jacobian of the reduced field at `(δ, ·, Q_f)`, with the Q–V droop `E = E₀ − n_q (Q_f −
Q_ref)` (all slopes at `(δ, E)`):
`[[0, 1, 0], [−P_δ/M, −D/M, n_q P_E/M], [ω_q Q_δ, 0, −ω_q (1 + n_q Q_E)]]`. -/
def reducedJacobian (δ Qf : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0;
    -p.powerSlope δ (p.emf Qf) / p.M, -p.D / p.M, p.nq * p.powerSlopeE δ (p.emf Qf) / p.M;
    p.ωq * p.reactiveSlope δ (p.emf Qf), 0, -(p.ωq * (1 + p.nq * p.reactiveSlopeE δ (p.emf Qf)))]

/-- The droop-corrected slope `P_δ (1 + n_q Q_E) − n_q P_E Q_δ` at `(δ, E(Q_f))`: minus the
Jacobian determinant of the static balance `(δ, Q_f) ↦ (P(δ, E) − P_ref, Q(δ, E) − Q_f)`; without
droop it is the slope `∂P/∂δ` (`droopSlope_eq_powerSlope`). -/
def droopSlope (δ Qf : ℝ) : ℝ :=
  p.powerSlope δ (p.emf Qf) * (1 + p.nq * p.reactiveSlopeE δ (p.emf Qf)) -
    p.nq * p.powerSlopeE δ (p.emf Qf) * p.reactiveSlope δ (p.emf Qf)

@[tmio M, powerlib_domain] theorem det_reducedJacobian (δ Qf : ℝ) :
    (p.reducedJacobian δ Qf).det = -(p.ωq * p.droopSlope δ Qf / p.M) := by
  simp [reducedJacobian, droopSlope, Matrix.det_fin_three]; ring

@[tmio M, powerlib_domain] theorem droopSlope_eq_powerSlope (hnq : p.nq = 0) (δ Qf : ℝ) :
    p.droopSlope δ Qf = p.powerSlope δ p.E0 := by
  simp [droopSlope, emf, hnq]

/-- The reduced field has the Jacobian `reducedJacobian` (Fréchet derivative), with or without
droop: the `Q_f` column carries the `E`-partials of the quasi-steady powers through
`∂E/∂Q_f = −n_q`. -/
@[tmio M, powerlib_domain] theorem hasFDerivAt_reducedField (hZt : p.Zt ≠ 0) (y : State 3) :
    HasFDerivAt p.reducedField
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (p.reducedJacobian (y 0) (y 2))) y := by
  have hf : p.reducedField = fun z => Dynamics.mk3 (z 1)
      ((p.Pref - p.Pq (z 0) (p.emf (z 2)) - p.D * z 1) / p.M)
        (p.ωq * (p.Qq (z 0) (p.emf (z 2)) - z 2)) :=
    funext p.reducedField_apply
  rw [hf, ← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
  intro i
  rw [hasFDerivWithinAt_univ]
  have h0 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := y)
  have h1 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := y)
  have h2 := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3) : State 3 →L[ℝ] ℝ).hasFDerivAt (x := y)
  have he : HasFDerivAt (fun z : State 3 => p.emf (z 2))
      (-(p.nq • (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3) : State 3 →L[ℝ] ℝ))) y :=
    ((h2.add_const (-p.Qref)).const_mul p.nq).const_sub p.E0 |>.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => by simp [emf, sub_eq_add_neg])
  have hP := p.hasFDerivAt_Pq_comp hZt h0 he
  have hQ := p.hasFDerivAt_Qq_comp hZt h0 he
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Dynamics.mk3_zero]
    convert h1 using 1
    · rfl
    · apply ContinuousLinearMap.ext; intro v
      simp [reducedJacobian, Dynamics.toEuclideanCLM_apply3]
  · simp only [Fin.mk_one, Fin.isValue, Dynamics.mk3_one]
    have h := (((hasFDerivAt_const p.Pref y).sub hP).sub (h1.const_mul p.D)).const_mul p.M⁻¹
    convert h using 1
    · funext z; simp [div_eq_inv_mul]
    · apply ContinuousLinearMap.ext; intro v
      simp [reducedJacobian, Dynamics.toEuclideanCLM_apply3]
      ring
  · simp only [Fin.reduceFinMk, Fin.isValue, Dynamics.mk3_two]
    have h := (hQ.sub h2).const_mul p.ωq
    convert h using 1
    · funext z; simp
    · apply ContinuousLinearMap.ext; intro v
      simp [reducedJacobian, Dynamics.toEuclideanCLM_apply3]
      ring

/-- The Schur identity at a quasi-steady point, with or without droop: if `J` is the Jacobian of
the 13-state field at `qssState δ Δω Q_f`, then
`det J = det fastBlock δ · det reducedJacobian δ Q_f` (the generic law
`LinearAlgebra.det_eq_det_fast_mul_det_reduced`: the Jacobian of the reduced field,
`hasFDerivAt_reducedField`, is the Schur complement of the fast block). -/
@[tmio M, powerlib_domain] theorem det_jacobian_qssState (hLf : p.Lf ≠ 0) (hCf : p.Cf ≠ 0)
    (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0) (hZt : p.Zt ≠ 0)
    (δ ω Qf : ℝ) {J : Matrix (Fin 13) (Fin 13) ℝ}
    (hJ : HasFDerivAt p.field (Matrix.toEuclideanCLM (𝕜 := ℝ) J) (p.qssState δ ω Qf)) :
    J.det = (p.fastBlock δ).det * (p.reducedJacobian δ Qf).det := by
  have hRed : HasFDerivAt p.reducedField
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (p.reducedJacobian δ Qf)) (Dynamics.mk3 δ ω Qf) := by
    simpa using p.hasFDerivAt_reducedField hZt (Dynamics.mk3 δ ω Qf)
  have hs : p.qssState δ ω Qf = p.graph (Dynamics.mk3 δ ω Qf) := by simp [graph]
  rw [hs] at hJ
  have hR : HasFDerivAt
      (fun s => (WithLp.toLp 2 fun k => p.field (p.graph s) (split.symm (.inr k)) : State 3))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (p.reducedJacobian δ Qf)) (Dynamics.mk3 δ ω Qf) := by
    have he : (fun s => (WithLp.toLp 2 fun k => p.field (p.graph s) (split.symm (.inr k)) :
        State 3)) = p.reducedField := by
      funext s
      ext k
      fin_cases k <;> rfl
    rw [he]
    exact hRed
  have hA : ∀ i j, HasDerivAt (fun t : ℝ => p.field (p.graph (Dynamics.mk3 δ ω Qf) +
      t • EuclideanSpace.single (split.symm (.inl j)) 1) (split.symm (.inl i)))
      (p.fastBlock δ i j) 0 := by
    intro i j
    simpa [graph] using p.hasDerivAt_fast (p.graph (Dynamics.mk3 δ ω Qf)) i j
  refine LinearAlgebra.det_eq_det_fast_mul_det_reduced split hJ
    (p.contDiff_graph.differentiable (by norm_num) _) (fun s k => ?_) (fun s i => ?_) hA hR
  · fin_cases k <;> rfl
  · have hfast := (p.fastAtRest_iff hLf hCf hLg hKic hKiv hZt (p.graph s)).mpr rfl
    obtain ⟨a, c⟩ := i
    exact hfast _ (by rw [split_symm_inl]; simp only; omega)

/-- On the saddle branch the full-order model is unstable, for every choice of the controller
gains and with or without droop: at an equilibrium `qssState δ* 0 Q*` (`P(δ*, E*) = P_ref`,
`Q(δ*, E*) = Q*`, `E* = E₀ − n_q (Q* − Q_ref)`) with a negative droop-corrected slope
`droopSlope δ* Q* < 0` and `M, ω_q > 0`, the Jacobian has
`det J = det fastBlock · (−ω_q droopSlope/M) > 0` in dimension 13, hence a positive real
eigenvalue (`Criteria.unstable_of_jacobian_det`). -/
@[tmio TM, powerlib_domain] private theorem unstable_of_droopSlope_neg (hLf : p.Lf ≠ 0)
    (hCf : p.Cf ≠ 0) (hLg : p.Lg ≠ 0) (hKic : p.Kic ≠ 0) (hKiv : p.Kiv ≠ 0) (hZt : p.Zt ≠ 0)
    (hM : 0 < p.M) (hωq : 0 < p.ωq) {δ Qf : ℝ} (hP : p.Pq δ (p.emf Qf) = p.Pref)
    (hQ : p.Qq δ (p.emf Qf) = Qf) (hs : p.droopSlope δ Qf < 0) :
    Unstable p.field (p.qssState δ 0 Qf) := by
  have heq : p.field (p.qssState δ 0 Qf) = 0 :=
    (p.field_eq_zero_iff hLf hCf hLg hKic hKiv hZt hM.ne' hωq.ne' _).mpr ⟨δ, Qf, rfl, hP, hQ⟩
  set J := (Matrix.toEuclideanCLM (n := Fin 13) (𝕜 := ℝ)).symm
    (fderiv ℝ p.field (p.qssState δ 0 Qf))
  have hJac : fderiv ℝ p.field (p.qssState δ 0 Qf) =
      Matrix.toEuclideanCLM (n := Fin 13) (𝕜 := ℝ) J := by simp [J]
  have hJ : HasFDerivAt p.field (Matrix.toEuclideanCLM (𝕜 := ℝ) J) (p.qssState δ 0 Qf) := by
    rw [← hJac]
    exact (p.contDiff_field.differentiable (by norm_num) _).hasFDerivAt
  refine Criteria.unstable_of_jacobian_det J p.contDiff_field heq hJac ?_
  rw [p.det_jacobian_qssState hLf hCf hLg hKic hKiv hZt δ 0 Qf hJ, p.det_reducedJacobian]
  have h1 := p.det_fastBlock_pos hLf hCf hLg hKic hKiv hZt δ
  have h2 : 0 < -(p.ωq * p.droopSlope δ Qf / p.M) := by
    rw [neg_pos]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hωq hs) hM
  have h3 := mul_pos h1 h2
  norm_num
  linarith

/-- Without virtual impedance the slope of the quasi-steady power–angle curve is the
synchronizing coefficient of the reduced swing machine `swingParams`. -/
@[tmio M, powerlib_domain] theorem powerSlope_eq_syncCoeff (hZv : p.Zv = 0) (hZg : p.Zg ≠ 0)
    (δ : ℝ) : p.powerSlope δ p.E0 = p.swingParams.syncCoeff δ := by
  have hZt : p.Zt ≠ 0 := by rwa [Zt, hZv, add_zero]
  have hf : (fun d => p.Pq d p.E0) = p.swingParams.Pe := funext (p.Pq_eq_swing hZv hZg)
  have h := p.hasDerivAt_Pq hZt δ p.E0
  rw [hf] at h
  exact h.unique (p.swingParams.hasDerivAt_Pe δ)

/-! ### The reading as the reduced Q–V droop model -/

/-- The reduced Q–V droop model of the quasi-steady set (`Z_v = 0`): the VSM, droop and filter
parameters with the line `R = R_g`, `X = ω₀L_g` (`theorem/GridTiedConverter/GFM/QVDroop.lean`). -/
def qvDroop : QVDroop := ⟨p.M, p.D, p.ωq, p.nq, p.E0, p.Qref, p.Pref, p.V, p.Rg, p.ω0 * p.Lg⟩

@[tmio M, powerlib_domain] private theorem Rv_Xv_of_Zv (hZv : p.Zv = 0) :
    p.Rv = 0 ∧ p.Xv = 0 := by
  have h := Complex.ext_iff.mp hZv
  simpa [Zv] using h

@[tmio M, powerlib_domain] private theorem Pq_eq_qvDroop (hZv : p.Zv = 0) (hZg : p.Zg ≠ 0)
    (δ E : ℝ) : p.Pq δ E = p.qvDroop.P δ E := by
  have hZt : p.Zt ≠ 0 := by rwa [Zt, hZv, add_zero]
  obtain ⟨hR, hX⟩ := p.Rv_Xv_of_Zv hZv
  rw [p.Pq_eq hZt, QVDroop.P_eq]
  simp only [qvDroop, QVDroop.zsq, Rt, Xt, hR, hX]
  ring

@[tmio M, powerlib_domain] private theorem Qq_eq_qvDroop (hZv : p.Zv = 0) (hZg : p.Zg ≠ 0)
    (δ E : ℝ) : p.Qq δ E = p.qvDroop.Q δ E := by
  have hZt : p.Zt ≠ 0 := by rwa [Zt, hZv, add_zero]
  obtain ⟨hR, hX⟩ := p.Rv_Xv_of_Zv hZv
  rw [p.Qq_eq hZt, QVDroop.Q_eq]
  simp only [qvDroop, QVDroop.zsq, Rt, Xt, hR, hX]
  ring

/-- Without virtual impedance the reduced field — the slow rows of the 13-state field on its
quasi-steady set — is the field of the reduced Q–V droop model `qvDroop`, for every droop gain
and every controller gain. -/
@[tmio M, powerlib_domain] theorem reducedField_eq_qvDroop (hZv : p.Zv = 0) (hZg : p.Zg ≠ 0) :
    p.reducedField = p.qvDroop.field := by
  funext y
  rw [reducedField_apply, QVDroop.field, p.Pq_eq_qvDroop hZv hZg, p.Qq_eq_qvDroop hZv hZg]
  rfl

end Params

/-! ## The family of the full-order model -/

/-- A full-order model read about a selected quasi-steady point `qssState δ* 0 Q*`. -/
structure Model where
  /-- The parameters. -/
  p : Params
  /-- The selected angle `δ*`. -/
  δ : ℝ
  /-- The selected filtered reactive power `Q*`. -/
  Qf : ℝ

/-- The selected point `qssState δ* 0 Q*`. -/
def Model.point (m : Model) : State 13 := m.p.qssState m.δ 0 m.Qf

/-- The 13-state field translated so that the selected point is the origin. -/
def Model.field (m : Model) (z : State 13) : State 13 := m.p.field (z + m.point)

/-- The saddle condition (instability requirement): nondegenerate fast block
(`L_f, C_f, L_g, K_ic, K_iv ≠ 0`, `Z_g + Z_v ≠ 0`), `M, ω_q > 0`, a balanced point at the droop
EMF `E* = E₀ − n_q (Q* − Q_ref)` (`P(δ*, E*) = P_ref`, `Q(δ*, E*) = Q*`) and a negative
droop-corrected slope `Params.droopSlope δ* Q* < 0` (without droop: `∂P/∂δ (δ*, E₀) < 0`). -/
def Model.Saddle (m : Model) : Prop :=
  m.p.Lf ≠ 0 ∧ m.p.Cf ≠ 0 ∧ m.p.Lg ≠ 0 ∧ m.p.Kic ≠ 0 ∧ m.p.Kiv ≠ 0 ∧ m.p.Zt ≠ 0 ∧
    0 < m.p.M ∧ 0 < m.p.ωq ∧ m.p.Pq m.δ (m.p.emf m.Qf) = m.p.Pref ∧
      m.p.Qq m.δ (m.p.emf m.Qf) = m.Qf ∧ m.p.droopSlope m.δ m.Qf < 0

/-- The full-order family: no stability requirement (`False`), instability through the saddle
condition. -/
def family : Family Model Spectral.Requirement 13 0 :=
  Spectral.localFamily Model.field (fun _ => False) Model.Saddle

@[tmio TM, powerlib_domain] private theorem mem_den_flow {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.p.field m.point :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.p.field) (pt := Model.point)
    (Spectral.localFamily_isAutonomous _ _ _)

/-- The saddle condition places a model in instability (the Schur identity and the fast-block
determinant, `Params.det_jacobian_qssState`, `Params.det_fastBlock_pos`). Implementation evidence
for the family's soundness. -/
@[tmio TM, powerlib_domain] private theorem unstable_of_saddle {m : Model} (h : m.Saddle) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  obtain ⟨hLf, hCf, hLg, hKic, hKiv, hZt, hM, hωq, hP, hQ, hs⟩ := h
  exact mem_den_flow.mpr
    (m.p.unstable_of_droopSlope_neg hLf hCf hLg hKic hKiv hZt hM hωq hP hQ hs)

/-- Every translation of the full-order family is sound: no model meets the (absent) stability
requirement, and the saddle condition proves instability. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  refine Spectral.local_chain_le_semantics (fun m h => h.elim) (fun m h => ?_)
  exact (Flow.Property.holds_shift_iff .unstable).mpr (mem_den_flow.mp (unstable_of_saddle h))

/-- The reduced saddle branch is unstable in the full-order model, for every choice of the
controller gains `K_pv, K_iv, K_pc, K_ic, k_ff, k_dv`, of the virtual impedance and of the Q–V
droop gain `n_q`: a balanced quasi-steady point `qssState δ* 0 Q*` at the droop EMF
`E* = E₀ − n_q (Q* − Q_ref)` with a negative droop-corrected slope
`Params.droopSlope δ* Q* = P_δ (1 + n_q Q_E) − n_q P_E Q_δ < 0` is unstable (the Jacobian
determinant is `det fastBlock · (−ω_q droopSlope/M) > 0` in dimension 13). Without droop the
condition is `∂P/∂δ < 0` (`Params.droopSlope_eq_powerSlope`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable (m : Model) (hLf : m.p.Lf ≠ 0)
    (hCf : m.p.Cf ≠ 0) (hLg : m.p.Lg ≠ 0) (hKic : m.p.Kic ≠ 0) (hKiv : m.p.Kiv ≠ 0)
    (hZt : m.p.Zt ≠ 0) (hM : 0 < m.p.M) (hωq : 0 < m.p.ωq)
    (hP : m.p.Pq m.δ (m.p.emf m.Qf) = m.p.Pref) (hQ : m.p.Qq m.δ (m.p.emf m.Qf) = m.Qf)
    (hs : m.p.droopSlope m.δ m.Qf < 0) :
    connection% (m ∈ family.den (.flow .unstable)) :=
  unstable_of_saddle ⟨hLf, hCf, hLg, hKic, hKiv, hZt, hM, hωq, hP, hQ, hs⟩

/-- Read through the reduced swing machine (`Z_v = 0`, no droop): a balanced angle of
`Params.swingParams` (`P_e(δ*) = P_ref`) with a negative synchronizing coefficient — the saddle
equilibrium `δ_u` of the reduced model — is an unstable equilibrium of the full 13-state model, for
every choice of the controller gains (scaffold
`theorem/GridTiedConverter/GFM/FullModel/FullModelSwing.agda`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_swing (m : Model) (hLf : m.p.Lf ≠ 0)
    (hCf : m.p.Cf ≠ 0) (hLg : m.p.Lg ≠ 0) (hKic : m.p.Kic ≠ 0) (hKiv : m.p.Kiv ≠ 0)
    (hZg : m.p.Zg ≠ 0) (hZv : m.p.Zv = 0) (hnq : m.p.nq = 0) (hM : 0 < m.p.M)
    (hωq : 0 < m.p.ωq) (hb : m.p.swingParams.Pe m.δ = m.p.Pref)
    (hQ : m.p.Qq m.δ m.p.E0 = m.Qf) (hK : m.p.swingParams.syncCoeff m.δ < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  have hE : m.p.emf m.Qf = m.p.E0 := by simp [Params.emf, hnq]
  exact mem_den_unstable m hLf hCf hLg hKic hKiv (by rwa [Params.Zt, hZv, add_zero]) hM hωq
    (by rw [hE, m.p.Pq_eq_swing hZv hZg]; exact hb) (by rw [hE]; exact hQ)
    (by rw [m.p.droopSlope_eq_powerSlope hnq, m.p.powerSlope_eq_syncCoeff hZv hZg]; exact hK)

/-- Read through the reduced Q–V droop model (`Z_v = 0`, droop in its physical range
`M, ω_q, n_q, ω₀L_g > 0`, `E₀ + n_q Q_ref > 0`): an equilibrium `(δ*, 0, Q*)` of
`Params.qvDroop` with positive EMF on the descending branch of its quasi-static characteristic,
`P̃'(δ*) < 0` (`QVDroop.mem_den_unstable_of_slope_neg`), is an unstable equilibrium
`qssState δ* 0 Q*` of the full 13-state model, for every choice of the controller gains
(scaffold `theorem/GridTiedConverter/GFM/FullModel/FullModelQVDroop.agda`): the two reduced
Jacobians agree (`Params.reducedField_eq_qvDroop`), so `det J_red > 0` and
`Params.droopSlope δ* Q* < 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_qvDroop (m : Model) (hLf : m.p.Lf ≠ 0)
    (hCf : m.p.Cf ≠ 0) (hLg : m.p.Lg ≠ 0) (hKic : m.p.Kic ≠ 0) (hKiv : m.p.Kiv ≠ 0)
    (hZv : m.p.Zv = 0) (hM : 0 < m.p.M) (hωq : 0 < m.p.ωq) (hnq : 0 < m.p.nq)
    (hX : 0 < m.p.ω0 * m.p.Lg) (hc : 0 < m.p.E0 + m.p.nq * m.p.Qref)
    (heq : m.p.qvDroop.field (Dynamics.mk3 m.δ 0 m.Qf) = 0) (hE : 0 < m.p.emf m.Qf)
    (hs : deriv m.p.qvDroop.Ptilde m.δ < 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  set q := m.p.qvDroop
  have hZg : m.p.Zg ≠ 0 := by
    intro h
    have him : m.p.Zg.im = m.p.ω0 * m.p.Lg := by rw [Params.Zg_eq]; simp
    rw [h, Complex.zero_im] at him
    exact hX.ne' him.symm
  have hZt : m.p.Zt ≠ 0 := by rwa [Params.Zt, hZv, add_zero]
  have h2 : 0 < q.a2 := q.a2_pos hnq hX
  have h0 : q.a0 < 0 := q.a0_neg hc
  have hEq : q.emf m.Qf = q.Eplus m.δ := by
    simpa using q.emf_eq_Eplus hM.ne' hωq.ne' h2 h0 heq (by exact hE)
  have hK := (q.one_add_nq_QE_Eplus h2 h0 m.δ).2
  have hdet : 0 < (q.jacobian m.δ (q.emf m.Qf)).det := by
    rw [hEq, q.det_jacobian_eq_slope h2 h0 m.δ]
    have hωM : 0 < q.ωq / q.M := div_pos hωq hM
    nlinarith [mul_pos hωM hK, mul_pos (mul_pos hωM hK) (neg_pos.mpr hs)]
  have hJ : m.p.reducedJacobian m.δ m.Qf = q.jacobian m.δ (q.emf m.Qf) := by
    have h1 := m.p.hasFDerivAt_reducedField hZt (Dynamics.mk3 m.δ 0 m.Qf)
    rw [m.p.reducedField_eq_qvDroop hZv hZg] at h1
    have h3 := h1.unique (q.hasFDerivAt_field (Dynamics.mk3 m.δ 0 m.Qf))
    simpa using Matrix.toEuclideanCLM.injective h3
  obtain ⟨-, hP, hQ⟩ := (q.field_eq_zero_iff hM.ne' hωq.ne' _).mp heq
  refine mem_den_unstable m hLf hCf hLg hKic hKiv hZt hM hωq ?_ ?_ ?_
  · rw [m.p.Pq_eq_qvDroop hZv hZg]; exact hP
  · rw [m.p.Qq_eq_qvDroop hZv hZg]; exact hQ
  · rw [← hJ, m.p.det_reducedJacobian] at hdet
    by_contra hn
    have : 0 ≤ m.p.ωq * m.p.droopSlope m.δ m.Qf / m.p.M :=
      div_nonneg (mul_nonneg hωq.le (not_lt.mp hn)) hM.le
    linarith

end powerlib.GFM.FullModel
