import theorem.GridTiedConverter.GFM.FullModel.TimeScale
import theorem.Linear.Synthesis

/-! # The 13-state grid-forming converter: a stable reduction with an unstable full model

Model boundary.
The 13-state model of `theorem/GridTiedConverter/GFM/FullModel/Basic.lean` (state order
`(i, v_c, i_g, ξ, ζ, δ, Δω, Q_f)` in dq components, system frame for the plant, controller frame
for the integrators, currents out of the converter positive, export-positive per-unit power) at
one explicit rational parameter point `witness` (per-unit frame frequency `ω₀ = 1`, lossless filter
and line, no virtual impedance, no droop, full capacitor decoupling, no line-current
feed-forward), at its quasi-steady equilibrium `δ* = 0`, `Q* = 2`. Continuous time, autonomous,
no input; fixed parameters (no time-scale separation). Level: the Jacobian of the field at the
equilibrium and local (in)stability.

Scaffold of the comparison with the reduced Q–V droop model (stable reduction, unstable full
model): `theorem/GridTiedConverter/GFM/FullModel/FullModelTimeScale.agda`.

Source: GFM counterpart study, equilibria note (t6 §c: "δs stability does NOT carry over: 14/20
full unstable where reduced stable", numerical), full-order model note (t5: "UNPROVED: stability of
δ+ in full model"); the witness was found by a parameter scan and is certified here exactly
(rational arithmetic in the kernel); Schur determinant identity (Horn–Johnson, *Matrix Analysis*,
§0.8.5).

Results.
* `Params.convRow_eq_ej`, `Params.currentIntRow_eq_ej`, `Params.voltageIntRow_eq_ej`: the fast
  rows are affine in `e^{jδ}` (filter row) and `e^{−jδ}` (integrator rows);
  `Params.hasDerivAt_fast_delta`: the angle derivative of the fast rows is `Params.deltaRows`;
  `Params.hasDerivAt_slow`: the slow rows along any direction (`Params.slowJac`);
  `Params.fastRows_shift_eq`: the fast rows do not depend on `Δω`, nor on `Q_f` without droop;
  `Params.phasors_qssState`: the phasors of the quasi-steady state.
* `Params.sum_fastBlock_mul`, `Params.smul_one_sub_fastBlock`: `fastBlock δ` and
  `r • 1 − fastBlock δ` are the realifications of `fastMatrix δ` and `r • 1 − fastMatrix δ`;
  `Params.det_smul_one_sub_fastBlock_nonneg`: `det (r • 1 − fastBlock δ) ≥ 0` (a squared modulus).
* `witness`: `L_f = C_f = 1/10`, `L_g = 1`, `R_f = R_g = 0`, `V = 1`, `E₀ = 2`, `K_pv = K_pc = 2`,
  `K_iv = K_ic = 1`, `k_ff = 0`, `k_dv = 1`, `M = D = 1/10`, `P_ref = 0`, `ω_q = 1`, `n_q = 0`,
  `Z_v = 0`; `witness_balance`: `P(0, E₀) = P_ref`, `Q(0, E₀) = 2`.
* `witness_isHurwitz_reducedJacobian`: the reduced Jacobian at the equilibrium is Hurwitz
  (synchronizing coefficient `2 > 0`, `M, D, ω_q > 0`).
* `witness_jacobian_blocks`: the Jacobian `J` of the 13-state field at the equilibrium in block
  form, `[[fastBlock 0, witnessBblock], [witnessC, witnessD]]` (angle column `witnessB`).
* `witness_det_sub_jacobian_nonpos`: `det (2 • 1 − J) ≤ 0`: the Schur factorization with the
  explicit solution `witnessH` (`witnessHblock`) of `(2 − A) H = B` gives
  `det (2 − A) · 3 (6 + 10 κ)`, `det (2 − A) = |det_ℂ (2 − fastMatrix)|² ≥ 0`,
  `κ = −492650/622073` (the dynamic synchronizing coefficient at `s = 2`, negative while the
  static one is `2`). Hence `witness_exists_real_eigenvalue`
  (`SingularPerturbation.exists_real_eigenvalue_ge_of_det_sub_nonpos`): `J` has a real eigenvalue
  `μ ≥ 2`.
* `witness_fastBlock_spectrallyStable`: the boundary layer of the witness is stable. Its fast
  block, relabelled by `finProdFinEquiv`, is the real image of the rational matrix `witnessA10`
  (`witness_fastBlock_reindex`, from `witnessRe`, `witnessIm`), and `witnessFastCertificate` is a
  rational Lyapunov certificate of it produced by the verified synthesizer
  `lyapunov_certificate%` of `theorem/Linear/Synthesis.lean` and checked by the kernel
  (`Linear.Certificate.isHurwitz`).

Family and connection conclusions.
* `witness_reduced_mem_den_LES` (connection, `QVDroop.family`): the reduced Q–V droop model of the
  witness (`Params.qvDroop`) is locally exponentially stable at `(0, 0, 2)`.
* `witness_mem_den_unstable` (connection, `FullModel.family`): the full 13-state model of the
  witness is unstable at the same equilibrium. So stability does not transfer from the reduced
  model to the full model at fixed parameters: the transfer of
  `theorem/GridTiedConverter/GFM/FullModel/TimeScale.lean` needs the time-scale separation
  (`ε` small), not only a stable boundary layer.
* `not_forall_mem_den_LES_of_reduced` (connection, both families): the refutation as one
  statement — every hypothesis of the time-scale transfer `exists_epsStar_mem_den_LES_of_qvDroop`
  (nondegenerate fast block, no virtual impedance, a locally exponentially stable reduction, a
  spectrally stable boundary layer) holds at the witness, and the full model at `ε = 1` is not
  locally exponentially stable.
-/

noncomputable section
namespace powerlib.GFM.FullModel
open Complex ComplexConjugate Matrix
open powerlib.Dynamics (State)

/-! ### Directional derivatives of the 13-state field -/

@[tmio T, powerlib_foundation] private theorem hasDerivAt_ej_add (δ : ℝ) :
    HasDerivAt (fun t : ℝ => ej (δ + t)) (I * ej δ) 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).const_add δ).ofReal_comp).mul_const I
  have h2 := h.cexp
  simp only [ej, id] at h2 ⊢
  convert h2 using 1
  simp; ring

@[tmio T, powerlib_foundation] private theorem hasDerivAt_ej_neg_add (δ : ℝ) :
    HasDerivAt (fun t : ℝ => ej (-(δ + t))) (-(I * ej (-δ))) 0 := by
  have h := ((((hasDerivAt_id (0 : ℝ)).const_add δ).neg).ofReal_comp).mul_const I
  have h2 := h.cexp
  simp only [ej, id] at h2 ⊢
  convert h2 using 1
  simp [Pi.neg_apply]; ring

@[tmio T, powerlib_foundation] private theorem hasDerivAt_component {f : ℝ → ℂ} {f' : ℂ}
    (hf : HasDerivAt f f' 0) (c : Fin 2) :
    HasDerivAt (fun t => component c (f t)) (component c f') 0 := by
  fin_cases c
  · exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hf
  · exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hf

@[tmio T, powerlib_foundation] private theorem add_smul_single_apply (x : State 13) (t : ℝ)
    (j i : Fin 13) :
    (x + t • EuclideanSpace.single j (1 : ℝ)) i = x i + t * (if i = j then 1 else 0) := by
  simp [PiLp.single_apply]

namespace Params

variable (p : Params)

/-- The filter row is affine in `e^{jδ}`:
`L_f i̇ = e^{jδ}(K_pc K_pv E + K_pc K_iv ζ + K_ic ξ) + K_pc (a_g i_g + a_v v_c) − (K_pc + R_f) i`,
`a_g = k_ff − K_pv Z_v`, `a_v = −K_pv + k_dv jω₀C_f`. -/
@[tmio M, powerlib_domain] theorem convRow_eq_ej (y : State 13) :
    p.convRow y = (ej (y 10) * (p.Kpc * (p.Kpv * (p.emf (y 12) : ℂ) + p.Kiv * voltageInt y) +
      p.Kic * currentInt y) + p.Kpc * ((p.kff - p.Kpv * p.Zv) * lineCurrent y +
        (-p.Kpv + p.kdv * (p.Bf * I)) * capVoltage y) - (p.Kpc + p.Rf) * convCurrent y) / p.Lf := by
  have hne : ej (y 10) ≠ 0 := Complex.exp_ne_zero _
  have he' : ej (-y 10) = (ej (y 10))⁻¹ := by simp [ej, Complex.exp_neg]
  simp only [convRow, uBridge, uCtrl, iRef, vRef, Zf_eq, he']
  field_simp
  ring

/-- The current-integrator row is affine in `e^{−jδ}`. -/
@[tmio M, powerlib_domain] theorem currentIntRow_eq_ej (y : State 13) :
    p.currentIntRow y = p.Kpv * (p.emf (y 12) : ℂ) + p.Kiv * voltageInt y +
      ej (-y 10) * ((p.kff - p.Kpv * p.Zv) * lineCurrent y +
        (-p.Kpv + p.kdv * (p.Bf * I)) * capVoltage y - convCurrent y) := by
  simp only [currentIntRow, iRef, vRef]
  ring

/-- The voltage-integrator row is affine in `e^{−jδ}`. -/
@[tmio M, powerlib_domain] theorem voltageIntRow_eq_ej (y : State 13) :
    p.voltageIntRow y =
      (p.emf (y 12) : ℂ) - ej (-y 10) * (p.Zv * lineCurrent y + capVoltage y) := by
  simp only [voltageIntRow, vRef]
  ring

/-- The angle derivatives of the five complex fast rows. -/
def deltaRows (x : State 13) : Fin 5 → ℂ :=
  ![I * ej (x 10) * (p.Kpc * (p.Kpv * (p.emf (x 12) : ℂ) + p.Kiv * voltageInt x) +
      p.Kic * currentInt x) / p.Lf, 0, 0,
    -(I * ej (-x 10)) * ((p.kff - p.Kpv * p.Zv) * lineCurrent x +
      (-p.Kpv + p.kdv * (p.Bf * I)) * capVoltage x - convCurrent x),
    I * ej (-x 10) * (p.Zv * lineCurrent x + capVoltage x)]

@[tmio M, powerlib_domain] private theorem phasors_shift (x : State 13) (t : ℝ) {j : Fin 13}
    (hj : 10 ≤ j.val) :
    convCurrent (x + t • EuclideanSpace.single j 1) = convCurrent x ∧
      capVoltage (x + t • EuclideanSpace.single j 1) = capVoltage x ∧
      lineCurrent (x + t • EuclideanSpace.single j 1) = lineCurrent x ∧
      currentInt (x + t • EuclideanSpace.single j 1) = currentInt x ∧
      voltageInt (x + t • EuclideanSpace.single j 1) = voltageInt x := by
  have h : ∀ i : Fin 13, i.val < 10 → (x + t • EuclideanSpace.single j (1 : ℝ)) i = x i := by
    intro i hi
    rw [add_smul_single_apply, ite_eq_right_iff.mpr (fun h => by rw [h] at hi; omega), mul_zero,
      add_zero]
  simp only [convCurrent, capVoltage, lineCurrent, currentInt, voltageInt, phasor]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [h _ (by decide), h _ (by decide)]

/-- The angle derivative of the fast rows of the 13-state field. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_fast_delta (x : State 13) (a : Fin 5) :
    HasDerivAt (fun t : ℝ => p.fastRows (x + t • EuclideanSpace.single 10 1) a)
      (p.deltaRows x a) 0 := by
  have hi := fun t => (phasors_shift x t (j := 10) (by decide)).1
  have hv := fun t => (phasors_shift x t (j := 10) (by decide)).2.1
  have hg := fun t => (phasors_shift x t (j := 10) (by decide)).2.2.1
  have hξ := fun t => (phasors_shift x t (j := 10) (by decide)).2.2.2.1
  have hζ := fun t => (phasors_shift x t (j := 10) (by decide)).2.2.2.2
  have h10 : ∀ t : ℝ, (x + t • EuclideanSpace.single (10 : Fin 13) (1 : ℝ)) 10 = x 10 + t := by
    intro t; rw [add_smul_single_apply]; simp
  have h12 : ∀ t : ℝ, (x + t • EuclideanSpace.single (10 : Fin 13) (1 : ℝ)) 12 = x 12 := by
    intro t; rw [add_smul_single_apply]; simp
  fin_cases a
  · simp only [fastRows, Fin.zero_eta, Matrix.cons_val_zero, convRow_eq_ej, hi, hv, hg, hξ, hζ,
      h10, h12, deltaRows]
    have h := (((hasDerivAt_ej_add (x 10)).mul_const (p.Kpc * (p.Kpv * (p.emf (x 12) : ℂ) +
      p.Kiv * voltageInt x) + p.Kic * currentInt x)).add_const (p.Kpc * ((p.kff - p.Kpv * p.Zv) *
        lineCurrent x + (-p.Kpv + p.kdv * (p.Bf * I)) * capVoltage x) -
          (p.Kpc + p.Rf) * convCurrent x)).div_const (p.Lf : ℂ)
    convert h using 1
    · funext t; ring
  · simp only [fastRows, deltaRows]
    have : ∀ t : ℝ, p.capRow (x + t • EuclideanSpace.single 10 1) = p.capRow x := fun t => by
      simp only [capRow, (hi t), (hv t), (hg t)]
    simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, this]
    exact hasDerivAt_const _ _
  · simp only [fastRows, deltaRows]
    have : ∀ t : ℝ, p.lineRow (x + t • EuclideanSpace.single 10 1) = p.lineRow x := fun t => by
      simp only [lineRow, (hv t), (hg t)]
    simp only [Fin.reduceFinMk, Matrix.cons_val, this]
    exact hasDerivAt_const _ _
  · simp only [fastRows, Fin.reduceFinMk, Matrix.cons_val, currentIntRow_eq_ej, hi, hv, hg, hζ,
      h10, h12, deltaRows]
    have h := ((hasDerivAt_ej_neg_add (x 10)).mul_const ((p.kff - p.Kpv * p.Zv) * lineCurrent x +
      (-p.Kpv + p.kdv * (p.Bf * I)) * capVoltage x - convCurrent x)).const_add
        (p.Kpv * (p.emf (x 12) : ℂ) + p.Kiv * voltageInt x)
    convert h using 1
  · simp only [fastRows, Fin.reduceFinMk, Matrix.cons_val, voltageIntRow_eq_ej, hv, hg, h10, h12,
      deltaRows]
    have h := ((hasDerivAt_ej_neg_add (x 10)).mul_const (p.Zv * lineCurrent x +
      capVoltage x)).const_sub (p.emf (x 12) : ℂ)
    convert h using 1
    ring

/-- The fast rows of the 13-state field do not depend on `Δω`, nor on `Q_f` without droop. -/
@[tmio M, powerlib_domain] theorem fastRows_shift_eq (x : State 13) (t : ℝ) {j : Fin 13}
    (hj : j = 11 ∨ (j = 12 ∧ p.nq = 0)) :
    p.fastRows (x + t • EuclideanSpace.single j 1) = p.fastRows x := by
  have hj' : 10 ≤ j.val := by rcases hj with rfl | ⟨rfl, -⟩ <;> decide
  obtain ⟨hi, hv, hg, hξ, hζ⟩ := phasors_shift x t hj'
  have h10 : (x + t • EuclideanSpace.single j (1 : ℝ)) 10 = x 10 := by
    rw [add_smul_single_apply]; rcases hj with rfl | ⟨rfl, -⟩ <;> simp
  have h12 : p.emf ((x + t • EuclideanSpace.single j (1 : ℝ)) 12) = p.emf (x 12) := by
    rw [add_smul_single_apply]
    rcases hj with rfl | ⟨rfl, hnq⟩
    · simp
    · simp [emf, hnq]
  funext a
  fin_cases a <;> simp only [fastRows, convRow, uBridge, uCtrl, iRef, vRef, capRow, lineRow,
    currentIntRow, voltageIntRow, hi, hv, hg, hξ, hζ, h10, h12]

/-- The Jacobian rows of the slow coordinates `(δ, Δω, Q_f)` at `x` (`k = 0, 1, 2`), against
every coordinate `j`: `δ̇ = Δω`, `Δω̇ = (P_ref − P_e − D Δω)/M`, `Q̇_f = ω_q (Q_e − Q_f)` with
`P_e = v_d i_d + v_q i_q`, `Q_e = v_q i_d − v_d i_q`. -/
def slowJac (x : State 13) : Matrix (Fin 3) (Fin 13) ℝ := fun k j =>
  let s : Fin 13 → ℝ := fun i => if i = j then 1 else 0
  ![s 11, -(s 2 * x 4 + x 2 * s 4 + s 3 * x 5 + x 3 * s 5 + p.D * s 11) / p.M,
    p.ωq * (s 3 * x 4 + x 3 * s 4 - s 2 * x 5 - x 2 * s 5 - s 12)] k

@[tmio M, powerlib_domain] private theorem Pe_apply (x : State 13) :
    Pe x = x 2 * x 4 + x 3 * x 5 := by
  simp [Pe, Transform.pq]

@[tmio M, powerlib_domain] private theorem Qe_apply (x : State 13) :
    Qe x = x 3 * x 4 - x 2 * x 5 := by
  simp [Qe, Transform.pq]

@[tmio T, powerlib_foundation] private theorem hasDerivAt_lin_mul (a b c d : ℝ) :
    HasDerivAt (fun t : ℝ => (a + t * b) * (c + t * d)) (a * d + b * c) 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a).fun_mul
    (((hasDerivAt_id (0 : ℝ)).mul_const d).const_add c)
  simp only [id, one_mul, zero_mul, add_zero] at h
  convert h using 1
  ring

/-- The slow rows of the 13-state field along any coordinate direction. -/
@[tmio M, powerlib_domain] theorem hasDerivAt_slow (x : State 13) (k : Fin 3) (j : Fin 13) :
    HasDerivAt (fun t : ℝ => p.field (x + t • EuclideanSpace.single j 1) (split.symm (.inr k)))
      (p.slowJac x k j) 0 := by
  have hc : ∀ i : Fin 13, HasDerivAt (fun t : ℝ => (x + t • EuclideanSpace.single j (1 : ℝ)) i)
      (if i = j then 1 else 0) 0 := by
    intro i
    simp only [add_smul_single_apply]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (if i = j then (1 : ℝ) else 0)).const_add (x i)
  fin_cases k
  · simp only [split_symm_inr, slowJac, Fin.zero_eta, Matrix.cons_val_zero]
    exact hc 11
  · simp only [split_symm_inr, slowJac, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    change HasDerivAt (fun t : ℝ => (p.Pref - Pe (x + t • EuclideanSpace.single j (1 : ℝ)) -
      p.D * (x + t • EuclideanSpace.single j (1 : ℝ) : State 13) 11) / p.M) _ 0
    simp only [Pe_apply, add_smul_single_apply]
    have h := ((((hasDerivAt_const (0 : ℝ) p.Pref).sub
      ((hasDerivAt_lin_mul (x 2) (if (2 : Fin 13) = j then 1 else 0) (x 4)
        (if (4 : Fin 13) = j then 1 else 0)).add
      (hasDerivAt_lin_mul (x 3) (if (3 : Fin 13) = j then 1 else 0) (x 5)
        (if (5 : Fin 13) = j then 1 else 0)))).sub
      ((((hasDerivAt_id (0 : ℝ)).mul_const (if (11 : Fin 13) = j then (1 : ℝ) else 0)).const_add
        (x 11)).const_mul p.D)).div_const p.M)
    convert h using 1
    · funext t; simp only [Pi.add_apply, Pi.sub_apply, id]
    · ring
  · simp only [split_symm_inr, slowJac, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    change HasDerivAt (fun t : ℝ => p.ωq * (Qe (x + t • EuclideanSpace.single j (1 : ℝ)) -
      (x + t • EuclideanSpace.single j (1 : ℝ) : State 13) 12)) _ 0
    simp only [Qe_apply, add_smul_single_apply]
    have h := (((hasDerivAt_lin_mul (x 3) (if (3 : Fin 13) = j then 1 else 0) (x 4)
        (if (4 : Fin 13) = j then 1 else 0)).sub
      (hasDerivAt_lin_mul (x 2) (if (2 : Fin 13) = j then 1 else 0) (x 5)
        (if (5 : Fin 13) = j then 1 else 0))).sub
      (((hasDerivAt_id (0 : ℝ)).mul_const (if (12 : Fin 13) = j then (1 : ℝ) else 0)).const_add
        (x 12))).const_mul p.ωq
    convert h using 1
    · funext t; simp only [Pi.sub_apply, id]
    · ring

end Params

/-! ### Realification of the fast block -/

namespace Params

variable (p : Params)

/-- The real fast block acting on a realified complex vector is the realification of the complex
fast matrix acting on it. -/
@[tmio M, powerlib_domain] theorem sum_fastBlock_mul (δ : ℝ) (a : Fin 5) (c' : Fin 2)
    (w : Fin 5 → ℂ) :
    ∑ j : Fin 5 × Fin 2, p.fastBlock δ (a, c') j * component j.2 (w j.1) =
      component c' (∑ b, p.fastMatrix δ a b * w b) := by
  rw [Fintype.sum_prod_type]
  simp only [fastBlock_apply, Fin.sum_univ_two]
  have hc : ∀ b, component c' (p.fastMatrix δ a b * axisUnit 0) * component 0 (w b) +
      component c' (p.fastMatrix δ a b * axisUnit 1) * component 1 (w b) =
        component c' (p.fastMatrix δ a b * w b) := by
    intro b
    fin_cases c' <;> simp [component, axisUnit, Complex.mul_re, Complex.mul_im] <;> ring
  simp only [hc]
  fin_cases c'
  · simp [component, Complex.re_sum]
  · simp [component, Complex.im_sum]

/-- `r • 1 − fastBlock δ` is the realification of `r • 1 − fastMatrix δ`. -/
@[tmio M, powerlib_domain] theorem smul_one_sub_fastBlock (r δ : ℝ) :
    r • (1 : Matrix (Fin 5 × Fin 2) (Fin 5 × Fin 2) ℝ) - p.fastBlock δ =
      Matrix.comp (Fin 5) (Fin 5) (Fin 2) (Fin 2) ℝ
        ((r • (1 : Matrix (Fin 5) (Fin 5) ℂ) - p.fastMatrix δ).map
          (Algebra.leftMulMatrix Complex.basisOneI)) := by
  ext ⟨a, c⟩ ⟨b, d⟩
  rw [Matrix.sub_apply, fastBlock_apply]
  simp only [Matrix.comp_apply, Matrix.map_apply, Algebra.leftMulMatrix_complex, Matrix.smul_apply,
    Matrix.one_apply, Prod.mk.injEq]
  by_cases hab : a = b <;> fin_cases c <;> fin_cases d <;>
    simp [hab, component, axisUnit, Matrix.sub_apply, Matrix.smul_apply]

/-- The determinant of `r • 1 − fastBlock δ` is a squared modulus, hence nonnegative. -/
@[tmio M, powerlib_domain] theorem det_smul_one_sub_fastBlock_nonneg (r δ : ℝ) :
    0 ≤ (r • (1 : Matrix (Fin 5 × Fin 2) (Fin 5 × Fin 2) ℝ) - p.fastBlock δ).det := by
  set N := r • (1 : Matrix (Fin 5) (Fin 5) ℂ) - p.fastMatrix δ
  have h : ((Algebra.leftMulMatrix Complex.basisOneI) N.det).det =
      (Matrix.comp (Fin 5) (Fin 5) (Fin 2) (Fin 2) ℝ
        (N.map (Algebra.leftMulMatrix Complex.basisOneI))).det :=
    Matrix.det_det N (Algebra.leftMulMatrix Complex.basisOneI).toRingHom
  rw [p.smul_one_sub_fastBlock, ← h, Algebra.leftMulMatrix_complex, Matrix.det_fin_two_of]
  nlinarith [sq_nonneg N.det.re, sq_nonneg N.det.im]

@[tmio M, powerlib_domain] theorem phasors_qssState (δ ω Qf : ℝ) :
    convCurrent (p.qssState δ ω Qf) = p.iQ δ (p.emf Qf) ∧
      capVoltage (p.qssState δ ω Qf) = p.vcQ δ (p.emf Qf) ∧
      lineCurrent (p.qssState δ ω Qf) = p.igQ δ (p.emf Qf) ∧
      currentInt (p.qssState δ ω Qf) = p.xiQ δ (p.emf Qf) ∧
      voltageInt (p.qssState δ ω Qf) = p.zeQ δ (p.emf Qf) := by
  simp [convCurrent, capVoltage, lineCurrent, currentInt, voltageInt, phasor, qssState,
    Complex.re_add_im]

end Params

/-! ### The witness -/

/-- The witness: per-unit frame frequency `ω₀ = 1`, `L_f = C_f = 1/10`, `L_g = 1`, lossless filter
and line, stiff grid `V = 1`, no virtual impedance, `K_pv = K_pc = 2`, `K_iv = K_ic = 1`, no
line-current feed-forward, full capacitor decoupling, `M = D = 1/10`, `P_ref = 0`, `E₀ = 2`, no
droop, `ω_q = 1`. -/
def witness : Params where
  ω0 := 1
  Lf := 1 / 10
  Rf := 0
  Cf := 1 / 10
  Lg := 1
  Rg := 0
  V := 1
  Rv := 0
  Xv := 0
  Kpv := 2
  Kiv := 1
  Kpc := 2
  Kic := 1
  kff := 0
  kdv := 1
  M := 1 / 10
  D := 1 / 10
  Pref := 0
  E0 := 2
  nq := 0
  Qref := 0
  ωq := 1

/-- The witness read about its equilibrium `δ* = 0`, `Q* = 2`. -/
def witnessModel : Model := ⟨witness, 0, 2⟩

@[tmio M, powerlib_domain] theorem witness_Zg : witness.Zg = I := by
  rw [Params.Zg_eq]; simp [witness]

@[tmio M, powerlib_domain] theorem witness_Zv : witness.Zv = 0 := by
  simp [Params.Zv, witness]

@[tmio M, powerlib_domain] theorem witness_Zt : witness.Zt = I := by
  rw [Params.Zt, witness_Zg, witness_Zv, add_zero]

@[tmio M, powerlib_domain] theorem witness_emf (Qf : ℝ) : witness.emf Qf = 2 := by
  simp [Params.emf, witness]

@[tmio M, powerlib_domain] theorem witness_Bf : witness.Bf = 1 / 10 := by
  simp [Params.Bf, witness]

/-- The witness is balanced at `δ* = 0`, `Q* = 2`: `P(0, E₀) = P_ref = 0`, `Q(0, E₀) = 2`. -/
@[tmio M, powerlib_domain] theorem witness_balance :
    witness.Pq 0 (witness.emf 2) = witness.Pref ∧ witness.Qq 0 (witness.emf 2) = 2 := by
  have hZt : witness.Zt ≠ 0 := by rw [witness_Zt]; exact Complex.I_ne_zero
  rw [witness.Pq_eq hZt, witness.Qq_eq hZt, witness_emf]
  simp [Params.Rt, Params.Xt, witness]
  norm_num

@[tmio M, powerlib_domain] private theorem witness_eq_phasors :
    witness.igQ 0 2 = -I ∧ witness.vcQ 0 2 = 2 ∧ witness.iQ 0 2 = -(4 / 5) * I ∧
      witness.xiQ 0 2 = 0 ∧ witness.zeQ 0 2 = -I := by
  have hg : witness.igQ 0 2 = -I := by
    rw [Params.igQ, witness_Zt]; simp [ej, witness]; field_simp; norm_num [Complex.ext_iff]
  have hv : witness.vcQ 0 2 = 2 := by
    rw [Params.vcQ, hg, witness_Zg]; simp [witness]; norm_num [Complex.ext_iff]
  have hi : witness.iQ 0 2 = -(4 / 5) * I := by
    rw [Params.iQ, hg, hv, witness_Bf]; push_cast; norm_num [Complex.ext_iff]
  refine ⟨hg, hv, hi, ?_, ?_⟩
  · simp [Params.xiQ, witness]
  · rw [Params.zeQ, hg, hv]; simp [ej, witness]

/-- The equilibrium of the witness. -/
def witnessPoint : State 13 := witness.qssState 0 0 2

@[tmio M, powerlib_domain] private theorem witnessPoint_phasors :
    convCurrent witnessPoint = -(4 / 5) * I ∧ capVoltage witnessPoint = 2 ∧
      lineCurrent witnessPoint = -I ∧ currentInt witnessPoint = 0 ∧
      voltageInt witnessPoint = -I := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := witness.phasors_qssState 0 0 2
  obtain ⟨hg, hv, hi, hξ, hζ⟩ := witness_eq_phasors
  rw [witness_emf] at h1 h2 h3 h4 h5
  exact ⟨h1.trans hi, h2.trans hv, h3.trans hg, h4.trans hξ, h5.trans hζ⟩

@[tmio M, powerlib_domain] private theorem witnessPoint_coords :
    witnessPoint 2 = 2 ∧ witnessPoint 3 = 0 ∧ witnessPoint 4 = 0 ∧ witnessPoint 5 = -1 ∧
      witnessPoint 10 = 0 ∧ witnessPoint 11 = 0 ∧ witnessPoint 12 = 2 := by
  obtain ⟨-, hv, hg, -, -⟩ := witnessPoint_phasors
  simp only [capVoltage, lineCurrent, phasor, Complex.ext_iff] at hv hg
  simp at hv hg
  exact ⟨hv.1, hv.2, hg.1, hg.2, rfl, rfl, rfl⟩

/-- The angle derivatives of the fast rows at the witness equilibrium. -/
def witnessB : Fin 5 → ℂ := ![20 + 80 * I, 0, 0, 1 + 4 * I, 2 * I]

/-- The solution of `(2 − fastMatrix) h = witnessB` at the witness equilibrium. -/
def witnessH : Fin 5 → ℂ :=
  ![(178725 + 584875 * I) / 622073, (131750 + 996750 * I) / 622073,
    (252050 + 372350 * I) / 622073, (7149 + 23395 * I) / 622073, (-65875 + 123698 * I) / 622073]

@[tmio M, powerlib_domain] private theorem witness_deltaRows :
    witness.deltaRows witnessPoint = witnessB := by
  obtain ⟨hi, hv, hg, hξ, hζ⟩ := witnessPoint_phasors
  obtain ⟨-, -, -, -, h10, -, h12⟩ := witnessPoint_coords
  funext a
  fin_cases a <;>
    simp [Params.deltaRows, witnessB, hi, hv, hg, hξ, hζ, h10, h12, ej, witness_emf, witness_Zv,
      witness_Bf] <;> (try simp [witness]) <;> norm_num [Complex.ext_iff]

@[tmio M, powerlib_domain] private theorem witness_solve (a : Fin 5) :
    2 * witnessH a - ∑ b, witness.fastMatrix 0 a b * witnessH b = witnessB a := by
  fin_cases a <;>
    simp [Fin.sum_univ_five, Params.fastMatrix, witnessH, witnessB, ej, witness_Zg, witness_Zv,
      witness_Bf] <;> (try simp [witness]) <;> norm_num [Complex.ext_iff]

/-- The fast–slow block of the witness Jacobian: only the angle column is nonzero. -/
def witnessBblock : Matrix (Fin 5 × Fin 2) (Fin 3) ℝ := fun i l =>
  if l = 0 then component i.2 (witnessB i.1) else 0

/-- The realified solution `H` of `(2 − A) H = B`. -/
def witnessHblock : Matrix (Fin 5 × Fin 2) (Fin 3) ℝ := fun i l =>
  if l = 0 then component i.2 (witnessH i.1) else 0

/-- The slow–fast block of the witness Jacobian. -/
def witnessC : Matrix (Fin 3) (Fin 5 × Fin 2) ℝ := fun k i =>
  witness.slowJac witnessPoint k (split.symm (.inl i))

/-- The slow–slow block of the witness Jacobian. -/
def witnessD : Matrix (Fin 3) (Fin 3) ℝ := fun k l =>
  witness.slowJac witnessPoint k (split.symm (.inr l))

/-- The Jacobian of the witness field at its equilibrium, in block form (fast first): the fast
block `fastBlock 0`, the angle column `witnessB`, and the slow rows `slowJac`. -/
@[tmio M, powerlib_domain] theorem witness_jacobian_blocks {J : Matrix (Fin 13) (Fin 13) ℝ}
    (hJ : HasFDerivAt witness.field (Matrix.toEuclideanCLM (𝕜 := ℝ) J) witnessPoint) :
    J.reindex split split =
      fromBlocks (witness.fastBlock 0) witnessBblock witnessC witnessD := by
  obtain ⟨-, -, -, -, h10, -, -⟩ := witnessPoint_coords
  ext (⟨a, c⟩ | k) (⟨b, d⟩ | l)
  · have h1 := LinearAlgebra.hasDerivAt_line_apply hJ (split.symm (.inl (a, c)))
      (split.symm (.inl (b, d)))
    have h2 := witness.hasDerivAt_fast witnessPoint (a, c) (b, d)
    rw [h10] at h2
    exact h1.unique h2
  · have h1 := LinearAlgebra.hasDerivAt_line_apply hJ (split.symm (.inl (a, c)))
      (split.symm (.inr l))
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂,
      witnessBblock]
    refine h1.unique ?_
    simp only [witness.field_split_inl]
    fin_cases l
    · have h := hasDerivAt_component (witness.hasDerivAt_fast_delta witnessPoint a) c
      rw [witness_deltaRows] at h
      exact h
    · simp only [Fin.mk_one, show split.symm (.inr 1) = (11 : Fin 13) from rfl,
        witness.fastRows_shift_eq witnessPoint _ (Or.inl rfl)]
      exact hasDerivAt_const _ _
    · simp only [Fin.reduceFinMk, show split.symm (.inr 2) = (12 : Fin 13) from rfl,
        witness.fastRows_shift_eq witnessPoint _ (Or.inr ⟨rfl, rfl⟩)]
      exact hasDerivAt_const _ _
  · exact (LinearAlgebra.hasDerivAt_line_apply hJ (split.symm (.inr k))
      (split.symm (.inl (b, d)))).unique (witness.hasDerivAt_slow witnessPoint k _)
  · exact (LinearAlgebra.hasDerivAt_line_apply hJ (split.symm (.inr k))
      (split.symm (.inr l))).unique (witness.hasDerivAt_slow witnessPoint k _)

@[tmio M, powerlib_domain] private theorem witness_schur :
    ((2 : ℝ) • (1 : Matrix (Fin 5 × Fin 2) (Fin 5 × Fin 2) ℝ) - witness.fastBlock 0) *
      witnessHblock + -witnessBblock = 0 := by
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
  ext ⟨a, c⟩ l
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
    Matrix.zero_apply, Matrix.mul_apply, smul_eq_mul]
  by_cases hl : l = 0
  · subst hl
    simp only [witnessHblock, witnessBblock, ↓reduceIte]
    rw [witness.sum_fastBlock_mul 0 a c witnessH, ← witness_solve a]
    fin_cases c <;> simp [component]
  · simp [witnessHblock, witnessBblock, hl]

@[tmio M, powerlib_domain] private theorem witness_det_small :
    (-witnessC * witnessHblock +
      ((2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - witnessD)).det < 0 := by
  obtain ⟨h2, h3, h4, h5, -, -, -⟩ := witnessPoint_coords
  rw [Matrix.det_fin_three]
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_five, Fin.sum_univ_two, witnessC,
    witnessD, witnessHblock, Params.slowJac, split_symm_inl, split_symm_inr, h2, h3, h4, h5,
    component, witnessH, Fin.ext_iff, witness]
  norm_num

/-- **The frequency test at the witness.** The Jacobian `J` of the 13-state field of the witness
at its equilibrium has `det (2 • 1 − J) ≤ 0`: in block form the Schur factorization with
`witnessHblock` gives `det (2 − fastBlock) · 3 (6 + 10 κ)`, `κ = −492650/622073`, and the first
factor is a squared modulus. -/
@[tmio M, powerlib_domain] theorem witness_det_sub_jacobian_nonpos
    {J : Matrix (Fin 13) (Fin 13) ℝ}
    (hJ : HasFDerivAt witness.field (Matrix.toEuclideanCLM (𝕜 := ℝ) J) witnessPoint) :
    ((2 : ℝ) • (1 : Matrix (Fin 13) (Fin 13) ℝ) - J).det ≤ 0 := by
  have hre : ((2 : ℝ) • (1 : Matrix (Fin 13) (Fin 13) ℝ) - J).reindex split split =
      fromBlocks ((2 : ℝ) • 1 - witness.fastBlock 0) (-witnessBblock) (-witnessC)
        ((2 : ℝ) • 1 - witnessD) := by
    have hb := witness_jacobian_blocks hJ
    ext i j
    have := congrFun (congrFun hb i) j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply] at this ⊢
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, this,
        split.symm.injective.eq_iff]
  rw [← Matrix.det_reindex_self split, hre,
    LinearAlgebra.det_fromBlocks_of_mul_add_eq_zero _ _ _ _ witnessHblock witness_schur]
  exact mul_nonpos_of_nonneg_of_nonpos (witness.det_smul_one_sub_fastBlock_nonneg 2 0)
    witness_det_small.le

@[tmio M, powerlib_domain] private theorem witness_nondeg :
    witness.Lf ≠ 0 ∧ witness.Cf ≠ 0 ∧ witness.Lg ≠ 0 ∧ witness.Kic ≠ 0 ∧ witness.Kiv ≠ 0 ∧
      witness.Zt ≠ 0 ∧ witness.M ≠ 0 ∧ witness.ωq ≠ 0 := by
  refine ⟨by norm_num [witness], by norm_num [witness], by norm_num [witness],
    by norm_num [witness], by norm_num [witness], by rw [witness_Zt]; exact Complex.I_ne_zero,
    by norm_num [witness], by norm_num [witness]⟩

@[tmio M, powerlib_domain] private theorem witness_field_eq_zero :
    witness.field witnessPoint = 0 := by
  obtain ⟨hLf, hCf, hLg, hKic, hKiv, hZt, hM, hωq⟩ := witness_nondeg
  exact (witness.field_eq_zero_iff hLf hCf hLg hKic hKiv hZt hM hωq _).mpr
    ⟨0, 2, rfl, witness_balance.1, witness_balance.2⟩

/-- The Jacobian of the 13-state field of the witness at its equilibrium has a real eigenvalue
`μ ≥ 2` (`witness_det_sub_jacobian_nonpos`, the frequency test
`SingularPerturbation.exists_real_eigenvalue_ge_of_det_sub_nonpos`). -/
@[tmio M, powerlib_domain] theorem witness_exists_real_eigenvalue :
    ∃ μ : ℝ, 2 ≤ μ ∧ ∃ v : Fin 13 → ℂ, v ≠ 0 ∧
      ((Matrix.toEuclideanCLM (n := Fin 13) (𝕜 := ℝ)).symm
        (fderiv ℝ witness.field witnessPoint)).map (algebraMap ℝ ℂ) *ᵥ v = (μ : ℂ) • v := by
  set J := (Matrix.toEuclideanCLM (n := Fin 13) (𝕜 := ℝ)).symm
    (fderiv ℝ witness.field witnessPoint)
  have hJac : fderiv ℝ witness.field witnessPoint =
      Matrix.toEuclideanCLM (n := Fin 13) (𝕜 := ℝ) J := by simp [J]
  have hJ : HasFDerivAt witness.field (Matrix.toEuclideanCLM (𝕜 := ℝ) J) witnessPoint := by
    rw [← hJac]; exact (witness.contDiff_field.differentiable (by norm_num) _).hasFDerivAt
  exact SingularPerturbation.exists_real_eigenvalue_ge_of_det_sub_nonpos J
    (witness_det_sub_jacobian_nonpos hJ)

/-- The 13-state model of the witness is unstable at its equilibrium. -/
@[tmio TM, powerlib_domain] private theorem witness_unstable :
    Unstable witness.field witnessPoint := by
  set J := (Matrix.toEuclideanCLM (n := Fin 13) (𝕜 := ℝ)).symm
    (fderiv ℝ witness.field witnessPoint)
  have hJac : fderiv ℝ witness.field witnessPoint =
      Matrix.toEuclideanCLM (n := Fin 13) (𝕜 := ℝ) J := by simp [J]
  have hJ : HasFDerivAt witness.field (Matrix.toEuclideanCLM (𝕜 := ℝ) J) witnessPoint := by
    rw [← hJac]; exact (witness.contDiff_field.differentiable (by norm_num) _).hasFDerivAt
  exact SingularPerturbation.unstable_of_det_sub_nonpos J witness.contDiff_field
    witness_field_eq_zero hJac two_pos (witness_det_sub_jacobian_nonpos hJ)

/-- The reduced Jacobian of the witness at its equilibrium is Hurwitz: synchronizing coefficient
`2 > 0`, `M = D = 1/10`, `ω_q = 1`. -/
@[tmio M, powerlib_domain] theorem witness_isHurwitz_reducedJacobian :
    LinearSystems.IsHurwitz (witness.reducedJacobian 0 2) := by
  have hZg : witness.Zg ≠ 0 := by rw [witness_Zg]; exact Complex.I_ne_zero
  refine witness.isHurwitz_reducedJacobian_of_swing witness_Zv hZg (by simp [witness])
    (by norm_num [witness]) (by norm_num [witness]) (by norm_num [witness]) 2 ?_
  rw [← witness.powerSlope_eq_syncCoeff witness_Zv hZg]
  simp [Params.powerSlope, Params.Rt, Params.Xt, witness]

/-- **The reduced model of the witness is stable (connection).** The reduced Q–V droop model
`Params.qvDroop` of the witness is locally exponentially stable at `(δ, Δω, Q_f) = (0, 0, 2)`. -/
@[tmio TM, powerlib_domain] theorem witness_reduced_mem_den_LES :
    connection% ((⟨witness.qvDroop, 0, 2⟩ : QVDroop.Model) ∈
      QVDroop.family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  have hZg : witness.Zg ≠ 0 := by rw [witness_Zg]; exact Complex.I_ne_zero
  have hZt : witness.Zt ≠ 0 := by rw [witness_Zt]; exact Complex.I_ne_zero
  set q := witness.qvDroop
  have hJ : witness.reducedJacobian 0 2 = q.jacobian 0 (q.emf 2) := by
    have h1 := witness.hasFDerivAt_reducedField hZt (Dynamics.mk3 0 0 2)
    rw [witness.reducedField_eq_qvDroop witness_Zv hZg] at h1
    have h3 := h1.unique (q.hasFDerivAt_field (Dynamics.mk3 0 0 2))
    simpa using Matrix.toEuclideanCLM.injective h3
  have heq : q.field (Dynamics.mk3 0 0 2) = 0 := by
    rw [← witness.reducedField_eq_qvDroop witness_Zv hZg, witness.reducedField_apply]
    obtain ⟨hP, hQ⟩ := witness_balance
    apply Dynamics.state3_ext <;> simp [hP, hQ]
  refine (Spectral.mem_den_flow_iff_shift (f := fun r : QVDroop.Model => r.q.field)
    (pt := QVDroop.Model.point) QVDroop.family_isAutonomous).mpr ?_
  refine (Dynamics.locallyExponentiallyStable_iff_isHurwitz_jacobian _ q.contDiff_field
    (q.fderiv_field _)).mpr ⟨heq, ?_⟩
  have h := witness_isHurwitz_reducedJacobian
  rw [hJ] at h
  simpa [QVDroop.Model.point] using h

/-- **The full model of the witness is unstable (connection).** The 13-state model of the witness
at the same equilibrium is unstable: the Jacobian has a real eigenvalue `μ ≥ 2`
(`witness_exists_real_eigenvalue`, the frequency test `witness_det_sub_jacobian_nonpos`). -/
@[tmio TM, powerlib_domain] theorem witness_mem_den_unstable :
    connection% (witnessModel ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact (Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.p.field) (pt := Model.point)
    (Spectral.localFamily_isAutonomous _ _ _)).mpr witness_unstable

/-! ### The boundary layer of the witness is stable -/

/-- The real part of the complex fast matrix of the witness at `δ = 0`. -/
def witnessRe : Matrix (Fin 5) (Fin 5) ℚ :=
  !![-20, -40, 0, 10, 20; 10, 0, -10, 0, 0; 0, 1, 0, 0, 0; -1, -2, 0, 0, 1; 0, -1, 0, 0, 0]

/-- The imaginary part of the complex fast matrix of the witness at `δ = 0`. -/
def witnessIm : Matrix (Fin 5) (Fin 5) ℚ :=
  !![0, 2, 0, 0, 0; 0, -1, 0, 0, 0; 0, 0, -1, 0, 0; 0, 1 / 10, 0, 0, 0; 0, 0, 0, 0, 0]

/-- The rational `10 × 10` fast block of the witness, coordinates `2a + c` (`finProdFinEquiv`). -/
def witnessA10 : Matrix (Fin 10) (Fin 10) ℚ := Matrix.of fun i j =>
  let a := finProdFinEquiv.symm i
  let b := finProdFinEquiv.symm j
  !![witnessRe a.1 b.1, -witnessIm a.1 b.1; witnessIm a.1 b.1, witnessRe a.1 b.1] a.2 b.2

@[tmio M, powerlib_domain] private theorem witness_fastMatrix_apply (a b : Fin 5) :
    witness.fastMatrix 0 a b = ((witnessRe a b : ℝ) : ℂ) + ((witnessIm a b : ℝ) : ℂ) * I := by
  fin_cases a <;> fin_cases b <;>
    simp [Params.fastMatrix, witnessRe, witnessIm, ej, witness_Zg, witness_Zv, witness_Bf] <;>
    (try simp [witness]) <;> norm_num [Complex.ext_iff]

/-- The fast block of the witness, relabelled by `finProdFinEquiv`, is the real image of the
rational matrix `witnessA10`. -/
@[tmio M, powerlib_domain] theorem witness_fastBlock_reindex :
    (witness.fastBlock 0).reindex finProdFinEquiv finProdFinEquiv =
      Linear.Positive.real witnessA10 := by
  ext i j
  obtain ⟨⟨a, c'⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨b, c⟩, rfl⟩ := finProdFinEquiv.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Linear.Positive.real, Matrix.map_apply, witnessA10, Matrix.of_apply, witness.fastBlock_apply,
    witness_fastMatrix_apply]
  fin_cases c' <;> fin_cases c <;> simp [component, axisUnit]

/-- A rational Lyapunov certificate of the witness's fast block, produced by the verified
synthesizer of `theorem/Linear/Synthesis.lean` and checked by the kernel. -/
def witnessFastCertificate : Linear.Certificate (Linear.Positive.real witnessA10) :=
  lyapunov_certificate% witnessA10

/-- **The boundary layer of the witness is stable**: its fast block is spectrally stable (the
rational Lyapunov certificate `witnessFastCertificate`, `Linear.Certificate.isHurwitz`). -/
@[tmio M, powerlib_domain] theorem witness_fastBlock_spectrallyStable :
    Linear.SpectrallyStable (witness.fastBlock 0) := by
  rw [← Linear.spectrallyStable_reindex finProdFinEquiv, witness_fastBlock_reindex,
    Linear.spectrallyStable_iff_isHurwitz]
  exact witnessFastCertificate.isHurwitz

/-- **No stability transfer at fixed parameters.** The hypotheses of the time-scale transfer
`exists_epsStar_mem_den_LES_of_qvDroop` — nondegenerate fast block, no virtual impedance, a reduced
Q–V droop model locally exponentially stable at the selected point, and a spectrally stable fast
block (boundary layer) — do not make the full-order model itself locally exponentially stable
there: the witness meets all of them (`witness_reduced_mem_den_LES`,
`witness_fastBlock_spectrallyStable`) and is unstable (`witness_mem_den_unstable`). -/
@[tmio TM, powerlib_domain] theorem not_forall_mem_den_LES_of_reduced :
    connection% (¬ ∀ m : Model, m.p.Lf ≠ 0 → m.p.Cf ≠ 0 → m.p.Lg ≠ 0 → m.p.Kic ≠ 0 →
      m.p.Kiv ≠ 0 → m.p.Zv = 0 → m.p.Zg ≠ 0 → m.p.M ≠ 0 → m.p.ωq ≠ 0 →
      (⟨m.p.qvDroop, m.δ, m.Qf⟩ : QVDroop.Model) ∈
        QVDroop.family.den (.flow .locallyExponentiallyStable) →
      Linear.SpectrallyStable (m.p.fastBlock m.δ) →
      m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  intro h
  obtain ⟨hLf, hCf, hLg, hKic, hKiv, -, hM, hωq⟩ := witness_nondeg
  have hZg : witness.Zg ≠ 0 := by rw [witness_Zg]; exact Complex.I_ne_zero
  have hLES := h witnessModel hLf hCf hLg hKic hKiv witness_Zv hZg hM hωq
    witness_reduced_mem_den_LES witness_fastBlock_spectrallyStable
  have hflow := (Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.p.field)
    (pt := Model.point) (Spectral.localFamily_isAutonomous _ _ _)).mp hLES
  exact witness_unstable (LocallyExponentiallyStable.lyapunovStable hflow)

end powerlib.GFM.FullModel
