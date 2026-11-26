import theorem.GridTiedConverter.GFM.QVDroopVirtualImpedance
import theorem.GridTiedConverter.GFM.QVDroopFold
import theorem.NormalForm.LyapunovCoefficient
import theorem.NormalForm.CoefficientLemmas
import theorem.Dynamics.SaddleNodeReduction

/-! # Grid-forming converter with Q–V droop and a virtual impedance: higher derivatives and the fold

Domain module.

Model boundary.
* The model of `theorem/GridTiedConverter/GFM/QVDroopVirtualImpedance.lean`, unchanged: state
  `x = (δ, Δω, Q_f)`, `δ̇ = Δω`, `M Δω̇ = P_ref − P_t(δ, E) − D Δω`, `Q̇_f = ω_q (Q_t(δ, E) − Q_f)`,
  `E = E₀ − n_q (Q_f − Q_ref)`, the powers measured at the converter terminal behind the virtual
  impedance `Z_v = R_v + jX_v`, the grid branch `Z_g = R_g + jX_g` to a stiff grid `V ∠ 0`,
  export-positive, continuous time, autonomous. Read about a selected point
  (`QVDroopVirtual.Model`) on `QVDroopVirtual.family`. Excluded as there.
* Level: the second and third derivatives of the field (static), and Lyapunov instability
  (LeanForControl's `Unstable`) at a fold `C = 0` of the Routh region of the virtual-impedance
  model.

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.2 and §5.4 (the fold
coefficient `a = ½⟨p, B(q, q)⟩`); the saddle-node reduction
`Dynamics.CenterManifold.unstable_of_foldCoeff_ne_zero_of_charpoly`
(`theorem/Dynamics/SaddleNodeReduction.lean`); the derivative laws of one-nonlinearity fields
(`NormalForm.LyapunovCoefficient.hess_ridge`, `third_ridge`, `hess_prodRidge`, `third_prodRidge`)
and the auxiliary laws of `theorem/NormalForm/CoefficientLemmas.lean`;
the null pair of the droop Jacobian at a fold (`Criteria.droopJacobian_null`, the vectors
`QVDroop.foldQ`, `QVDroop.foldP` of `theorem/GridTiedConverter/GFM/QVDroopFold.lean`). The
derivative forms and the fold coefficient were derived with exact computer algebra (sympy:
symbolic partial derivatives of the field, factorisation over `ℚ` after the fold relation
`b c = k a`) and are proved here by `ring`.

Results.
* `field_eq_pieces`: the field is an affine field plus five one-nonlinearity terms (`E²` along
  `vE`, `cos δ`, `sin δ` along `vC`, `vS`, and `Q_f cos δ`, `Q_f sin δ`); the virtual impedance
  enters the directions and the constant part (`−R_v V²`, `−X_v V²`).
* Unlike the model without virtual impedance, the angle curvatures `ρ = ∂²P_t/∂δ²`,
  `τ = ∂²Q_t/∂δ²` (`Ptδδ`, `Qtδδ`) are not `−∂Q_t/∂δ`, `∂P_t/∂δ`: with the Jacobian data
  `a = ∂P_t/∂δ`, `b = n_q ∂P_t/∂E`, `c = ∂Q_t/∂δ`, `k = K_t = 1 + n_q ∂Q_t/∂E` and `m = n_q/E`
  (`E ≠ 0`), the complexified second and third derivatives at every state are
  `bilinC_field`: `B(u, w) = (0, −(ρ/M) u₀w₀ + (ma/M)(u₀w₂ + u₂w₀) − (m(b + mρ)/M) u₂w₂,
  ω_q τ u₀w₀ − ω_q m c (u₀w₂ + u₂w₀) + ω_q m (k − 1 + m τ) u₂w₂)` (`bForm`) and
  `trilinC_field`: `C(u, w, z) = (0, (a/M) u₀w₀z₀ + (mρ/M) σ, −ω_q c u₀w₀z₀ − ω_q m τ σ)`,
  `σ = u₀w₀z₂ + u₀w₂z₀ + u₂w₀z₀` (`cForm`). For `Z_v = 0`, `ρ = −c`, `τ = a`
  (`curvatures_of_zero_virtual`), the forms of `theorem/GridTiedConverter/GFM/QVDroopFold.lean`.
* `jacobianC_field`, `Model.jacobianC_field`, `Model.contDiff_field`, `Model.analyticAt_field`,
  `Model.fderiv_field`, `Model.bilinC_field`, `Model.trilinC_field`;
  `Model.fderiv_fderiv_apply_eq_bForm`, `Model.iteratedFDeriv_three_apply_eq_cForm` (the second
  and third derivatives of the model field at the origin, at any real arguments).
* The fold: at `C = k a − b c = 0` the pair `q = (k, 0, c)`,
  `p = (D ω_q k, M ω_q k, b)/(D ω_q k² + b c)` is a normalised null pair (`Model.isNullPair_fold`),
  `det(sI − J) = s (s² + (A/M) s + (a + D ω_q k)/M)` (`Model.charpoly_fold`), and the fold
  coefficient satisfies `2 c (D ω_q k² + b c) foldCoeff = k ω_q 𝔉` with the cusp quantity
  `𝔉 = (k² + m² c²)(a τ − c ρ) − m a c²` (`foldQuad`, `Model.foldCoeff_fold`); for `Z_v = 0` it
  is `QVDroop.foldQuad` (`curvatures_of_zero_virtual`, `foldQuad_neg_self`).

Family and connection conclusions.
No new family: connection conclusions on `QVDroopVirtual.family`.
* **`mem_den_unstable_of_fold`**: for `M, ω_q > 0`, an equilibrium at a fold (`C = 0`) with
  `A > 0`, `a + D ω_q k > 0`, `k ≠ 0`, `E* ≠ 0` and `𝔉 ≠ 0` is unstable (a saddle-node,
  `Dynamics.CenterManifold.unstable_of_foldCoeff_ne_zero_of_charpoly`).
* **`mem_den_unstable_of_fold_of_hopf_ne`**: every fold equilibrium off the Hopf surface
  (`C = 0`, `G ≠ 0`) with `k, E* ≠ 0` and `𝔉 ≠ 0` is unstable (with `C = 0`,
  `G = A (a + D ω_q k)`, `routhHopf_eq`: a violation, or the saddle-node law).
* **`mem_den_lyapunovStable_iff_of_hopf_ne`**,
  **`mem_den_locallyAsymptoticallyStable_iff_of_hopf_ne`**: for `M, ω_q > 0` off the Hopf
  surface (`G ≠ 0`) and, at a fold, off the cusp set (`C = 0 → k ≠ 0 ∧ E* ≠ 0 ∧ 𝔉 ≠ 0`),
  Lyapunov stability and local asymptotic stability hold iff the point is an equilibrium with
  `A, C, G > 0`.

Degenerate points. The cusp set `C = 0`, `𝔉 = 0` with `c ≠ 0` (the fold coefficient vanishes) is
decided in `theorem/GridTiedConverter/GFM/QVDroopVirtualCusp.lean` (the cubic coefficient
`−ω_q k m c ρ/(2 (a + D ω_q k))`) except where `ρ = 0`; it does not meet the physical range
(`QVDroopVirtual.foldQuad_ne_zero_of_physical`; there `dz 𝔉 > 0`). The folds with `c = 0` (where
`𝔉 = 0` but the fold coefficient is `(b τ − k ρ)/(2 D)`) are decided there off `b τ = k ρ`, and
the double-zero set `C = 0`, `G = 0` (`A (a + D ω_q k) = 0`) off `A = 0`, `k = 0`, `𝔉 = 0` in
`theorem/GridTiedConverter/GFM/QVDroopVirtualBT.lean`. Located, not decided: the cusp points with
`ρ = 0`, the fold points with `k = 0`, the folds with `c = 0`, `b τ = k ρ`, and the triple zero
`A = 0` at a fold. The Hopf surface `G = 0`, `C > 0` is decided in
`theorem/GridTiedConverter/GFM/QVDroopVirtualHopf.lean`; the complete physical-range membership
is `theorem/GridTiedConverter/GFM/QVDroopVirtualMembership.lean`.
-/

noncomputable section
namespace powerlib.GFM.QVDroopVirtual
open Complex Matrix Polynomial
open powerlib.Dynamics (State coord mk3 mk3_zero mk3_one mk3_two state3_ext)
open powerlib.NormalForm.LyapunovCoefficient
open powerlib.Criteria (droopJacobian)

variable (q : QVDroopVirtual)

/-! ## The field in pieces -/

/-- The droop level `c = E₀ + n_q Q_ref`, so that `E = c − n_q Q_f`. -/
def level : ℝ := q.E0 + q.nq * q.Qref

/-- The linear part `(Δω, −D Δω/M, −ω_q Q_f)`. -/
def linPart : State 3 →L[ℝ] State 3 :=
  Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) !![0, 1, 0; 0, -q.D / q.M, 0; 0, 0, -q.ωq]

/-- The constant part `(0, (P_ref + R_v V²/|Z_t|²)/M, −ω_q X_v V²/|Z_t|²)`. -/
def constPart : State 3 :=
  mk3 0 (q.Pref / q.M + q.Rv * q.V ^ 2 / (q.M * q.ztsq)) (-(q.ωq * q.Xv * q.V ^ 2 / q.ztsq))

/-- The direction of the `E²` terms. -/
def vE : State 3 := mk3 0 (-(q.Rg / (q.M * q.ztsq))) (q.ωq * q.Xg / q.ztsq)

/-- The direction of the `E cos δ` terms. -/
def vC : State 3 :=
  mk3 0 (-((q.Rv - q.Rg) * q.V / (q.M * q.ztsq))) (q.ωq * (q.Xv - q.Xg) * q.V / q.ztsq)

/-- The direction of the `E sin δ` terms. -/
def vS : State 3 :=
  mk3 0 (-((q.Xg + q.Xv) * q.V / (q.M * q.ztsq))) (-(q.ωq * (q.Rg + q.Rv) * q.V / q.ztsq))

/-- The `E²` piece `(c − n_q Q_f)² vE` (with the affine part). -/
def pieceE : State 3 → State 3 :=
  ridge q.linPart q.constPart (coord 2) (fun t => (q.level - q.nq * t) ^ 2) q.vE

/-- The `cos δ` piece. -/
def pieceC : State 3 → State 3 := ridge 0 0 (coord 0) (fun t => q.level * Real.cos t) q.vC

/-- The `sin δ` piece. -/
def pieceS : State 3 → State 3 := ridge 0 0 (coord 0) (fun t => q.level * Real.sin t) q.vS

/-- The `Q_f cos δ` piece. -/
def pieceQC : State 3 → State 3 := prodRidge (coord 0) (coord 2) Real.cos ((-q.nq) • q.vC)

/-- The `Q_f sin δ` piece. -/
def pieceQS : State 3 → State 3 := prodRidge (coord 0) (coord 2) Real.sin ((-q.nq) • q.vS)

/-- The field as an affine field plus five one-nonlinearity terms. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem field_eq_pieces :
    q.field = q.pieceE + q.pieceC + q.pieceS + q.pieceQC + q.pieceQS := by
  funext x
  apply state3_ext <;>
    simp [field, pieceE, pieceC, pieceS, pieceQC, pieceQS, ridge, prodRidge, linPart, constPart,
      vE, vC, vS, Pt_eq, Qt_eq, emf, level, Dynamics.toEuclideanCLM_apply3] <;>
    ring

@[tmio M, powerlib_domain] private theorem contDiff_pieces :
    ContDiff ℝ 3 q.pieceE ∧ ContDiff ℝ 3 q.pieceC ∧ ContDiff ℝ 3 q.pieceS ∧
      ContDiff ℝ 3 q.pieceQC ∧ ContDiff ℝ 3 q.pieceQS :=
  ⟨contDiff_ridge _ _ _ _ (by fun_prop), contDiff_ridge _ _ _ _ (by fun_prop),
    contDiff_ridge _ _ _ _ (by fun_prop), contDiff_prodRidge _ _ _ Real.contDiff_cos,
    contDiff_prodRidge _ _ _ Real.contDiff_sin⟩

/-! ## Second and third derivatives in the Jacobian data -/

/-- `ρ = ∂²P_t/∂δ²` at `(δ, E)`. -/
def Ptδδ (δ E : ℝ) : ℝ :=
  -((q.Rv - q.Rg) * (E * q.V * Real.cos δ) + (q.Xg + q.Xv) * (E * q.V * Real.sin δ)) / q.ztsq

/-- `τ = ∂²Q_t/∂δ²` at `(δ, E)`. -/
def Qtδδ (δ E : ℝ) : ℝ :=
  ((q.Rg + q.Rv) * (E * q.V * Real.sin δ) - (q.Xv - q.Xg) * (E * q.V * Real.cos δ)) / q.ztsq

/-- Without virtual impedance (`R_v = X_v = 0`) the angle curvatures are the slopes of the other
power: `∂²P_t/∂δ² = −∂Q_t/∂δ`, `∂²Q_t/∂δ² = ∂P_t/∂δ`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem curvatures_of_zero_virtual (hRv : q.Rv = 0) (hXv : q.Xv = 0)
    (δ E : ℝ) : q.Ptδδ δ E = -q.Qtδ δ E ∧ q.Qtδδ δ E = q.Ptδ δ E := by
  constructor <;> simp only [Ptδδ, Qtδδ, Qtδ, Ptδ, hRv, hXv] <;> ring

/-- The second-derivative form in the Jacobian data `a, b, c, k`, `m = n_q/E` and the angle
curvatures `ρ, τ`. -/
def bForm (M ω a b c k m ρ τ : ℝ) (u w : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![0, -((ρ / M : ℝ) : ℂ) * (u 0 * w 0) + ((m * a / M : ℝ) : ℂ) * (u 0 * w 2 + u 2 * w 0) -
      ((m * (b + m * ρ) / M : ℝ) : ℂ) * (u 2 * w 2),
    ((ω * τ : ℝ) : ℂ) * (u 0 * w 0) - ((ω * m * c : ℝ) : ℂ) * (u 0 * w 2 + u 2 * w 0) +
      ((ω * m * (k - 1 + m * τ) : ℝ) : ℂ) * (u 2 * w 2)]

/-- The third-derivative form in the Jacobian data. -/
def cForm (M ω a c m ρ τ : ℝ) (u w z : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![0, ((a / M : ℝ) : ℂ) * (u 0 * w 0 * z 0) +
      ((m * ρ / M : ℝ) : ℂ) * (u 0 * w 0 * z 2 + u 0 * w 2 * z 0 + u 2 * w 0 * z 0),
    -((ω * c : ℝ) : ℂ) * (u 0 * w 0 * z 0) -
      ((ω * m * τ : ℝ) : ℂ) * (u 0 * w 0 * z 2 + u 0 * w 2 * z 0 + u 2 * w 0 * z 0)]

/-- The second-derivative coefficients `b_{rij}` in the Jacobian data. -/
def bTab (M ω a b c k m ρ τ : ℝ) (r i j : Fin 3) : ℝ :=
  ![0, -(ρ / M), ω * τ] r * coord 0 (basisVec i) * coord 0 (basisVec j) +
    ![0, m * a / M, -(ω * m * c)] r *
      (coord 0 (basisVec i) * coord 2 (basisVec j) + coord 2 (basisVec i) * coord 0 (basisVec j)) +
    ![0, -(m * (b + m * ρ) / M), ω * m * (k - 1 + m * τ)] r * coord 2 (basisVec i) *
      coord 2 (basisVec j)

/-- The third-derivative coefficients `c_{rijl}` in the Jacobian data. -/
def cTab (M ω a c m ρ τ : ℝ) (r i j l : Fin 3) : ℝ :=
  ![0, a / M, -(ω * c)] r * coord 0 (basisVec i) * coord 0 (basisVec j) * coord 0 (basisVec l) +
    ![0, m * ρ / M, -(ω * m * τ)] r *
      (coord 0 (basisVec i) * coord 0 (basisVec j) * coord 2 (basisVec l) +
        coord 0 (basisVec i) * coord 2 (basisVec j) * coord 0 (basisVec l) +
        coord 2 (basisVec i) * coord 0 (basisVec j) * coord 0 (basisVec l))

/-- **The second derivative** at a state `x₀` with EMF `E ≠ 0`, in the Jacobian data at
`(x₀ 0, E)`, `m = n_q/E` and the angle curvatures. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem hess_field (x₀ : State 3) (hE : q.emf (x₀ 2) ≠ 0)
    (r i j : Fin 3) :
    hess q.field x₀ r i j =
      bTab q.M q.ωq (q.Ptδ (x₀ 0) (q.emf (x₀ 2))) (q.nq * q.PtE (x₀ 0) (q.emf (x₀ 2)))
        (q.Qtδ (x₀ 0) (q.emf (x₀ 2))) (q.gain (x₀ 0) (q.emf (x₀ 2))) (q.nq / q.emf (x₀ 2))
        (q.Ptδδ (x₀ 0) (q.emf (x₀ 2))) (q.Qtδδ (x₀ 0) (q.emf (x₀ 2))) r i j := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := q.contDiff_pieces
  have k2 : (2 : WithTop ℕ∞) ≤ 3 := by norm_num
  have c12 : ContDiff ℝ 3 (q.pieceE + q.pieceC) := c1.add c2
  have c123 : ContDiff ℝ 3 (q.pieceE + q.pieceC + q.pieceS) := c12.add c3
  have c1234 : ContDiff ℝ 3 (q.pieceE + q.pieceC + q.pieceS + q.pieceQC) := c123.add c4
  rw [field_eq_pieces, hess_add (c1234.of_le k2) (c5.of_le k2),
    hess_add (c123.of_le k2) (c4.of_le k2), hess_add (c12.of_le k2) (c3.of_le k2),
    hess_add (c1.of_le k2) (c2.of_le k2)]
  rw [pieceE, pieceC, pieceS, pieceQC, pieceQS, hess_ridge _ _ _ _ (by fun_prop),
    hess_ridge _ _ _ _ (by fun_prop), hess_ridge _ _ _ _ (by fun_prop),
    hess_prodRidge _ _ _ Real.contDiff_cos (fun t => Real.hasDerivAt_cos t)
      (fun t => (Real.hasDerivAt_sin t).neg),
    hess_prodRidge _ _ _ Real.contDiff_sin (fun t => Real.hasDerivAt_sin t)
      (fun t => Real.hasDerivAt_cos t)]
  rw [(iteratedDeriv_affine_sq q.level q.nq _).1, (iteratedDeriv_const_mul_cos q.level _).1,
    (iteratedDeriv_const_mul_sin q.level _).1]
  have hE' : q.E0 - q.nq * (x₀ 2 - q.Qref) ≠ 0 := hE
  fin_cases r <;>
    simp [bTab, vE, vC, vS, Dynamics.coord_apply, gain, Ptδ, PtE, Qtδ, QtE, Ptδδ, Qtδδ, level,
      emf] <;>
    field_simp <;> ring

/-- **The third derivative** at a state `x₀` with EMF `E ≠ 0`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem third_field (x₀ : State 3) (hE : q.emf (x₀ 2) ≠ 0)
    (r i j l : Fin 3) :
    third q.field x₀ r i j l =
      cTab q.M q.ωq (q.Ptδ (x₀ 0) (q.emf (x₀ 2))) (q.Qtδ (x₀ 0) (q.emf (x₀ 2)))
        (q.nq / q.emf (x₀ 2)) (q.Ptδδ (x₀ 0) (q.emf (x₀ 2))) (q.Qtδδ (x₀ 0) (q.emf (x₀ 2)))
        r i j l := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := q.contDiff_pieces
  have c12 : ContDiff ℝ 3 (q.pieceE + q.pieceC) := c1.add c2
  have c123 : ContDiff ℝ 3 (q.pieceE + q.pieceC + q.pieceS) := c12.add c3
  have c1234 : ContDiff ℝ 3 (q.pieceE + q.pieceC + q.pieceS + q.pieceQC) := c123.add c4
  rw [field_eq_pieces, third_add c1234 c5, third_add c123 c4, third_add c12 c3, third_add c1 c2]
  rw [pieceE, pieceC, pieceS, pieceQC, pieceQS, third_ridge _ _ _ _ (by fun_prop),
    third_ridge _ _ _ _ (by fun_prop), third_ridge _ _ _ _ (by fun_prop),
    third_prodRidge _ _ _ Real.contDiff_cos (fun t => Real.hasDerivAt_cos t)
      (fun t => (Real.hasDerivAt_sin t).neg)
      (fun t => ((Real.hasDerivAt_cos t).neg).congr_deriv (neg_neg _)),
    third_prodRidge _ _ _ Real.contDiff_sin (fun t => Real.hasDerivAt_sin t)
      (fun t => Real.hasDerivAt_cos t) (fun t => (Real.hasDerivAt_sin t).neg)]
  rw [(iteratedDeriv_affine_sq q.level q.nq _).2, (iteratedDeriv_const_mul_cos q.level _).2,
    (iteratedDeriv_const_mul_sin q.level _).2]
  have hE' : q.E0 - q.nq * (x₀ 2 - q.Qref) ≠ 0 := hE
  fin_cases r <;>
    simp [cTab, vE, vC, vS, Dynamics.coord_apply, Ptδ, Qtδ, Ptδδ, Qtδδ, level, emf] <;>
    field_simp <;> ring

/-- **The second-derivative form** at a state with EMF `E ≠ 0` (`bForm`). Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem bilinC_field (x₀ : State 3) (hE : q.emf (x₀ 2) ≠ 0)
    (u w : Fin 3 → ℂ) :
    bilinC q.field x₀ u w =
      bForm q.M q.ωq (q.Ptδ (x₀ 0) (q.emf (x₀ 2))) (q.nq * q.PtE (x₀ 0) (q.emf (x₀ 2)))
        (q.Qtδ (x₀ 0) (q.emf (x₀ 2))) (q.gain (x₀ 0) (q.emf (x₀ 2))) (q.nq / q.emf (x₀ 2))
        (q.Ptδδ (x₀ 0) (q.emf (x₀ 2))) (q.Qtδδ (x₀ 0) (q.emf (x₀ 2))) u w := by
  ext r
  rw [bilinC_apply]
  simp only [q.hess_field x₀ hE, bTab, coord_basisVec, Fin.sum_univ_three]
  fin_cases r <;> simp [bForm] <;> ring

/-- **The third-derivative form** at a state with EMF `E ≠ 0` (`cForm`). Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem trilinC_field (x₀ : State 3) (hE : q.emf (x₀ 2) ≠ 0)
    (u w z : Fin 3 → ℂ) :
    trilinC q.field x₀ u w z =
      cForm q.M q.ωq (q.Ptδ (x₀ 0) (q.emf (x₀ 2))) (q.Qtδ (x₀ 0) (q.emf (x₀ 2)))
        (q.nq / q.emf (x₀ 2)) (q.Ptδδ (x₀ 0) (q.emf (x₀ 2))) (q.Qtδδ (x₀ 0) (q.emf (x₀ 2)))
        u w z := by
  ext r
  rw [trilinC_apply]
  simp only [q.third_field x₀ hE, cTab, coord_basisVec, Fin.sum_univ_three]
  fin_cases r <;> simp [cForm] <;> ring

/-- The complexified Jacobian at a state. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem jacobianC_field (x₀ : State 3) :
    jacobianC q.field x₀ = (q.jacobian (x₀ 0) (q.emf (x₀ 2))).map (fun x => (x : ℂ)) := by
  rw [jacobianC, q.fderiv_field, cmat_toEuclideanCLM]

/-! ## The translated field of a model -/

@[tmio M, powerlib_domain] theorem Model.contDiff_field (m : Model) {k : WithTop ℕ∞} :
    ContDiff ℝ k m.field :=
  m.q.contDiff_field.comp (contDiff_id.add contDiff_const)

/-- The model field is analytic at the selected point (`sin`, `cos` and polynomials). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.analyticAt_field (m : Model) :
    AnalyticAt ℝ m.field 0 :=
  (m.contDiff_field (k := ⊤)).contDiffAt.analyticAt

@[tmio M, powerlib_domain] theorem Model.fderiv_field (m : Model) :
    fderiv ℝ m.field 0 = Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) m.jacobian := by
  rw [show m.field = fun z => m.q.field (z + m.point) from rfl, fderiv_comp_add_right,
    zero_add, m.q.fderiv_field]
  simp [Model.point, Model.jacobian]

@[tmio M, powerlib_domain] theorem Model.jacobianC_field (m : Model) :
    jacobianC m.field 0 = Linear.complexify m.jacobian := by
  rw [jacobianC, m.fderiv_field, cmat_toEuclideanCLM]
  rfl

/-- The second-derivative form of the model field at the origin. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem Model.bilinC_field (m : Model) (hE : m.q.emf m.Qf ≠ 0)
    (u w : Fin 3 → ℂ) :
    bilinC m.field 0 u w =
      bForm m.q.M m.q.ωq (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf))
        (m.q.Qtδ m.δ (m.q.emf m.Qf)) (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf)
        (m.q.Ptδδ m.δ (m.q.emf m.Qf)) (m.q.Qtδδ m.δ (m.q.emf m.Qf)) u w := by
  have h := m.q.bilinC_field m.point (by simpa [Model.point] using hE) u w
  simp only [Model.point, mk3_zero, mk3_two] at h
  rw [show m.field = fun z => m.q.field (z + m.point) from rfl, bilinC_comp_add, Model.point, h]

/-- The third-derivative form of the model field at the origin. Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem Model.trilinC_field (m : Model) (hE : m.q.emf m.Qf ≠ 0)
    (u w z : Fin 3 → ℂ) :
    trilinC m.field 0 u w z =
      cForm m.q.M m.q.ωq (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
        (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf)) (m.q.Qtδδ m.δ (m.q.emf m.Qf))
        u w z := by
  have h := m.q.trilinC_field m.point (by simpa [Model.point] using hE) u w z
  simp only [Model.point, mk3_zero, mk3_two] at h
  rw [show m.field = fun z => m.q.field (z + m.point) from rfl, trilinC_comp_add, Model.point, h]

/-! ## The fold -/

/-- The cusp quantity `𝔉 = (k² + m² c²)(a τ − c ρ) − m a c²` of the fold coefficient (for
`ρ = −c`, `τ = a` it is `QVDroop.foldQuad`). -/
def foldQuad (a c k m ρ τ : ℝ) : ℝ := (k ^ 2 + m ^ 2 * c ^ 2) * (a * τ - c * ρ) - m * a * c ^ 2

/-- At the curvatures of the model without virtual impedance (`ρ = −c`, `τ = a`,
`curvatures_of_zero_virtual`) the cusp quantity is `QVDroop.foldQuad`. -/
@[tmio M, powerlib_domain] theorem foldQuad_neg_self (a c k m : ℝ) :
    foldQuad a c k m (-c) a = QVDroop.foldQuad a c k m := by
  simp only [foldQuad, QVDroop.foldQuad]
  ring

/-- `G = A (P_tδ + D ω_q K_t) − M ω_q C` (both sides of the Routh gap). -/
@[tmio M, powerlib_domain] theorem routhHopf_eq (δ E : ℝ) :
    q.routhHopf δ E = q.routhTrace δ E * (q.Ptδ δ E + q.D * q.ωq * q.gain δ E) -
      q.M * q.ωq * q.routhFold δ E := by
  simp only [routhHopf, routhTrace, routhFold]
  ring

/-- **The characteristic polynomial at a fold** (`C = 0`, `M ≠ 0`):
`det(sI − J) = s (s² + (A/M) s + (P_tδ + D ω_q K_t)/M)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.charpoly_fold (m : Model) (hM : m.q.M ≠ 0)
    (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0) :
    (jacobianC m.field 0).charpoly =
      Polynomial.X * (Polynomial.X ^ 2 +
        Polynomial.C (((m.q.routhTrace m.δ (m.q.emf m.Qf)) / m.q.M : ℝ) : ℂ) * Polynomial.X +
        Polynomial.C (((m.q.Ptδ m.δ (m.q.emf m.Qf) +
          m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf)) / m.q.M : ℝ) : ℂ)) := by
  refine Polynomial.funext fun s => ?_
  rw [m.jacobianC_field, ← Linear.det_characteristicMatrix_eq_eval, Model.jacobian,
    jacobian_eq_droopJacobian, Criteria.det_characteristicMatrix_droopJacobian hM]
  have h0 : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Ptδ m.δ (m.q.emf m.Qf) -
      m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) = 0 := hC
  rw [h0, mul_zero, zero_div]
  simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C, routhTrace]
  push_cast
  ring

/-- **The null pair at a fold**: with `C = k a − b c = 0`, `M ≠ 0` and `D ω_q k² + b c ≠ 0`,
`(QVDroop.foldQ k c, QVDroop.foldP M D ω_q b c k)` is a normalised null pair of the Jacobian.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.isNullPair_fold (m : Model) (hM : m.q.M ≠ 0)
    (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0)
    (hN : m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2 +
      m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) ≠ 0) :
    NormalForm.BogdanovTakens.IsNullPair (fderiv ℝ m.field 0)
      (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)))
      (QVDroop.foldP m.q.M m.q.D m.q.ωq (m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf))
        (m.q.Qtδ m.δ (m.q.emf m.Qf)) (m.q.gain m.δ (m.q.emf m.Qf))) := by
  rw [m.fderiv_field, QVDroop.foldQ, QVDroop.foldP,
    NormalForm.BogdanovTakens.isNullPair_toEuclideanCLM_iff, Model.jacobian,
    jacobian_eq_droopJacobian]
  have h0 : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Ptδ m.δ (m.q.emf m.Qf) -
      m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) = 0 := hC
  obtain ⟨hr, hl⟩ := Criteria.droopJacobian_null (M := m.q.M) (D := m.q.D) (ω := m.q.ωq) h0
  generalize m.q.Ptδ m.δ (m.q.emf m.Qf) = a at hr hl ⊢
  generalize m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) = b at hr hl hN ⊢
  generalize m.q.Qtδ m.δ (m.q.emf m.Qf) = c at hr hl hN ⊢
  generalize m.q.gain m.δ (m.q.emf m.Qf) = k at hr hl hN ⊢
  refine ⟨hr, by rw [Matrix.smul_vecMul, hl, smul_zero], ?_⟩
  simp only [dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  field_simp
  ring

/-- **The second derivative of the model field at the origin**, read through the form `bForm` at
any real arguments. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.fderiv_fderiv_apply_eq_bForm (m : Model)
    (hE : m.q.emf m.Qf ≠ 0) (u v : State 3) (r : Fin 3) :
    (fderiv ℝ (fderiv ℝ m.field) 0 u v r : ℂ) =
      bForm m.q.M m.q.ωq (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf))
        (m.q.Qtδ m.δ (m.q.emf m.Qf)) (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf)
        (m.q.Ptδδ m.δ (m.q.emf m.Qf)) (m.q.Qtδδ m.δ (m.q.emf m.Qf)) (toC u) (toC v) r := by
  have h := congrFun (bilinC_toC m.field 0 u v) r
  rw [m.bilinC_field hE, iteratedFDeriv_two_apply] at h
  rw [h]
  simp

/-- **The third derivative of the model field at the origin**, read through the form `cForm` at
any real arguments. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.iteratedFDeriv_three_apply_eq_cForm (m : Model)
    (hE : m.q.emf m.Qf ≠ 0) (u v z : State 3) (r : Fin 3) :
    (iteratedFDeriv ℝ 3 m.field 0 ![u, v, z] r : ℂ) =
      cForm m.q.M m.q.ωq (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
        (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf)) (m.q.Qtδδ m.δ (m.q.emf m.Qf))
        (toC u) (toC v) (toC z) r := by
  have h := congrFun (trilinC_toC m.field 0 u v z) r
  rw [m.trilinC_field hE] at h
  rw [h]
  simp [toC]

/-- **The fold coefficient.** At a fold (`C = k a − b c = 0`, `M ≠ 0`, `E* ≠ 0`,
`N = D ω_q k² + b c ≠ 0`): `2 c N foldCoeff = k ω_q 𝔉(a, c, k, n_q/E*, ρ, τ)`, `𝔉 = foldQuad`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Model.foldCoeff_fold (m : Model) (hM : m.q.M ≠ 0)
    (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0) (hE : m.q.emf m.Qf ≠ 0)
    (hN : m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2 +
      m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) ≠ 0) :
    2 * m.q.Qtδ m.δ (m.q.emf m.Qf) * (m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2 +
        m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf)) *
      NormalForm.BogdanovTakens.foldCoeff m.field 0
        (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)))
        (QVDroop.foldP m.q.M m.q.D m.q.ωq (m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf))
          (m.q.Qtδ m.δ (m.q.emf m.Qf)) (m.q.gain m.δ (m.q.emf m.Qf))) =
      m.q.gain m.δ (m.q.emf m.Qf) * m.q.ωq *
        foldQuad (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
          (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf))
          (m.q.Qtδδ m.δ (m.q.emf m.Qf)) := by
  have h0 : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Ptδ m.δ (m.q.emf m.Qf) -
      m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) = 0 := hC
  have v1 := m.fderiv_fderiv_apply_eq_bForm hE
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)))
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))) 1
  have v2 := m.fderiv_fderiv_apply_eq_bForm hE
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)))
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))) 2
  have v0 := m.fderiv_fderiv_apply_eq_bForm hE
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)))
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))) 0
  rw [NormalForm.BogdanovTakens.foldCoeff]
  generalize fderiv ℝ (fderiv ℝ m.field) 0
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf)))
    (QVDroop.foldQ (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))) = v at v0 v1 v2 ⊢
  generalize m.q.Ptδ m.δ (m.q.emf m.Qf) = a at h0 v1 v2 v0 ⊢
  generalize m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) = b at h0 hN v1 v2 v0 ⊢
  generalize m.q.Qtδ m.δ (m.q.emf m.Qf) = c at h0 hN v1 v2 v0 ⊢
  generalize m.q.gain m.δ (m.q.emf m.Qf) = k at h0 hN v1 v2 v0 ⊢
  generalize m.q.nq / m.q.emf m.Qf = μ at v1 v2 v0 ⊢
  generalize m.q.Ptδδ m.δ (m.q.emf m.Qf) = ρ at v1 v2 v0 ⊢
  generalize m.q.Qtδδ m.δ (m.q.emf m.Qf) = τ at v1 v2 v0 ⊢
  simp only [bForm, toC, QVDroop.foldQ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, WithLp.ofLp_toLp] at v0 v1 v2
  have e1 : v 1 = -(ρ / m.q.M) * (k * k) + μ * a / m.q.M * (k * c + c * k) -
      μ * (b + μ * ρ) / m.q.M * (c * c) := by
    apply Complex.ofReal_injective; rw [v1]; push_cast; ring
  have e2 : v 2 = m.q.ωq * τ * (k * k) - m.q.ωq * μ * c * (k * c + c * k) +
      m.q.ωq * μ * (k - 1 + μ * τ) * (c * c) := by
    apply Complex.ofReal_injective; rw [v2]; push_cast; ring
  have hv0 : v 0 = 0 := by apply Complex.ofReal_injective; rw [v0]; simp
  have hM1 : m.q.M * v 1 = -(ρ * k ^ 2) + 2 * μ * a * k * c - μ * (b + μ * ρ) * c ^ 2 := by
    rw [e1]; field_simp; ring
  have key : c * (m.q.ωq * k * (m.q.M * v 1) + b * v 2) = k * m.q.ωq * foldQuad a c k μ ρ τ := by
    rw [hM1, e2]
    unfold foldQuad
    linear_combination (-(m.q.ωq * (c ^ 2 * μ ^ 2 * τ + k ^ 2 * τ - 2 * c ^ 2 * k * μ -
      c ^ 2 * μ))) * h0
  rw [← key]
  simp only [QVDroop.foldP, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
    conj_trivial, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hv0]
  have hN2 : c * b + m.q.D * m.q.ωq * k ^ 2 ≠ 0 := by
    rwa [add_comm, mul_comm c b]
  have hX := inv_mul_cancel₀ hN2
  field_simp
  linear_combination (c * (m.q.ωq * k * m.q.M * v 1 + b * v 2)) * hX

/-- **The fold is unstable** (a saddle-node). For `M, ω_q > 0`, an equilibrium at a fold of the
Routh region (`C = 0`) with `A > 0`, `P_tδ + D ω_q K_t > 0` (the other two eigenvalues in the
open left half plane), `K_t ≠ 0`, `E* ≠ 0` and a nonzero cusp quantity
`𝔉 = (k² + m² c²)(a τ − c ρ) − m a c² ≠ 0` (`a = P_tδ`, `c = Q_tδ`, `k = K_t`, `m = n_q/E*`,
`ρ = P_tδδ`, `τ = Q_tδδ`) is unstable: the fold coefficient is `k ω_q 𝔉/(2 c (D ω_q k² + b c))`
(`Dynamics.CenterManifold.unstable_of_foldCoeff_ne_zero_of_charpoly`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold (m : Model) (hM : 0 < m.q.M)
    (hω : 0 < m.q.ωq) (heq : m.q.field m.point = 0)
    (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0) (hA : 0 < m.q.routhTrace m.δ (m.q.emf m.Qf))
    (ha1 : 0 < m.q.Ptδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf))
    (hk : m.q.gain m.δ (m.q.emf m.Qf) ≠ 0) (hE : m.q.emf m.Qf ≠ 0)
    (hQ : foldQuad (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
      (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf))
      (m.q.Qtδδ m.δ (m.q.emf m.Qf)) ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  rw [(connection_proof% family_isAutonomous.mem_den_flow)]
  have h0 : m.q.gain m.δ (m.q.emf m.Qf) * m.q.Ptδ m.δ (m.q.emf m.Qf) -
      m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) = 0 := hC
  -- `N = D ω_q k² + b c = k (P_tδ + D ω_q K_t) ≠ 0` at the fold
  have hN : m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2 +
      m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) ≠ 0 := by
    have e : m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf) ^ 2 +
        m.q.nq * m.q.PtE m.δ (m.q.emf m.Qf) * m.q.Qtδ m.δ (m.q.emf m.Qf) =
        m.q.gain m.δ (m.q.emf m.Qf) *
          (m.q.Ptδ m.δ (m.q.emf m.Qf) + m.q.D * m.q.ωq * m.q.gain m.δ (m.q.emf m.Qf)) := by
      linear_combination (-1 : ℝ) * h0
    rw [e]
    exact mul_ne_zero hk ha1.ne'
  have hc : m.q.Qtδ m.δ (m.q.emf m.Qf) ≠ 0 := by
    intro hc0
    apply hQ
    have ha0 : m.q.Ptδ m.δ (m.q.emf m.Qf) = 0 := by
      rw [hc0, mul_zero, sub_zero] at h0
      exact (mul_eq_zero.mp h0).resolve_left hk
    simp [foldQuad, hc0, ha0]
  have heq0 : m.field 0 = 0 := by simpa [Model.field] using heq
  refine Dynamics.CenterManifold.unstable_of_foldCoeff_ne_zero_of_charpoly
    (m.contDiff_field (k := 2)) heq0 (m.isNullPair_fold hM.ne' hC hN)
    (m.charpoly_fold hM.ne' hC) (fun s hs => (Criteria.quadratic_roots_re_neg_iff _ _).mpr
      ⟨div_pos hA hM, div_pos ha1 hM⟩ s (by simpa using hs)) ?_
  intro h
  have key := m.foldCoeff_fold hM.ne' hC hE hN
  rw [h, mul_zero] at key
  exact mul_ne_zero (mul_ne_zero hk hω.ne') hQ key.symm

/-- **Every nondegenerate fold off the Hopf surface is unstable.** For `M, ω_q > 0`, an
equilibrium with `C = 0`, `G ≠ 0`, `K_t ≠ 0`, `E* ≠ 0` and `𝔉 ≠ 0` is unstable: at a fold
`G = A (P_tδ + D ω_q K_t)` (`routhHopf_eq`), so either a Routh quantity is strictly negative
(`mem_den_unstable_of_violation`) or both factors are positive (`mem_den_unstable_of_fold`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_fold_of_hopf_ne (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (heq : m.q.field m.point = 0)
    (hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0) (hG : m.q.routhHopf m.δ (m.q.emf m.Qf) ≠ 0)
    (hk : m.q.gain m.δ (m.q.emf m.Qf) ≠ 0) (hE : m.q.emf m.Qf ≠ 0)
    (hQ : foldQuad (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
      (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf))
      (m.q.Qtδδ m.δ (m.q.emf m.Qf)) ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  have hGe := m.q.routhHopf_eq m.δ (m.q.emf m.Qf)
  rw [hC, mul_zero, sub_zero] at hGe
  rcases (left_ne_zero_of_mul (hGe ▸ hG)).lt_or_gt with hA | hA
  · exact mem_den_unstable_of_violation m hM hω heq (Or.inl hA)
  rcases (right_ne_zero_of_mul (hGe ▸ hG)).lt_or_gt with ha1 | ha1
  · refine mem_den_unstable_of_violation m hM hω heq (Or.inr (Or.inr ?_))
    rw [hGe]
    exact mul_neg_of_pos_of_neg hA ha1
  · exact mem_den_unstable_of_fold m hM hω heq hC hA ha1 hk hE hQ

/-- **Lyapunov stability off the Hopf surface.** For `M, ω_q > 0`, `G ≠ 0` at the selected point,
and at a fold (`C = 0`) `K_t ≠ 0`, `E* ≠ 0`, `𝔉 ≠ 0`: the model is Lyapunov stable iff the point
is an equilibrium with `A, C, G > 0` (`mem_den_lyapunovStable_iff_of_ne` off the fold, the
saddle-node law on it). -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff_of_hopf_ne (m : Model)
    (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hG : m.q.routhHopf m.δ (m.q.emf m.Qf) ≠ 0)
    (hfold : m.q.routhFold m.δ (m.q.emf m.Qf) = 0 → m.q.gain m.δ (m.q.emf m.Qf) ≠ 0 ∧
      m.q.emf m.Qf ≠ 0 ∧ foldQuad (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
        (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf))
        (m.q.Qtδδ m.δ (m.q.emf m.Qf)) ≠ 0) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      m ∈ {m : Model | m.q.field m.point = 0 ∧ 0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
        0 < m.q.routhFold m.δ (m.q.emf m.Qf) ∧ 0 < m.q.routhHopf m.δ (m.q.emf m.Qf)}) := by
  by_cases hC : m.q.routhFold m.δ (m.q.emf m.Qf) = 0
  · have hles := mem_den_locallyExponentiallyStable_iff m hM hω
    unfold powerlib.TMIO.Statement at hles ⊢
    constructor
    · intro hl
      have heq : m.q.field m.point = 0 :=
        Dynamics.isEquilibrium_of_lyapunovStable m.q.contDiff_field
          ((Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.q.field)
            (pt := Model.point) family_isAutonomous).mp hl)
      obtain ⟨hk, hE, hQ⟩ := hfold hC
      exact absurd hl (Spectral.not_mem_den_lyapunovStable_of_unstable
        (mem_den_unstable_of_fold_of_hopf_ne m hM hω heq hC hG hk hE hQ))
    · intro h
      exact Spectral.den_locallyExponentiallyStable_subset_lyapunovStable (hles.mpr h)
  · exact mem_den_lyapunovStable_iff_of_ne m hM hω hC hG

/-- **Local asymptotic stability off the Hopf surface**, under the hypotheses of
`mem_den_lyapunovStable_iff_of_hopf_ne`: iff an equilibrium with `A, C, G > 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff_of_hopf_ne
    (m : Model) (hM : 0 < m.q.M) (hω : 0 < m.q.ωq) (hG : m.q.routhHopf m.δ (m.q.emf m.Qf) ≠ 0)
    (hfold : m.q.routhFold m.δ (m.q.emf m.Qf) = 0 → m.q.gain m.δ (m.q.emf m.Qf) ≠ 0 ∧
      m.q.emf m.Qf ≠ 0 ∧ foldQuad (m.q.Ptδ m.δ (m.q.emf m.Qf)) (m.q.Qtδ m.δ (m.q.emf m.Qf))
        (m.q.gain m.δ (m.q.emf m.Qf)) (m.q.nq / m.q.emf m.Qf) (m.q.Ptδδ m.δ (m.q.emf m.Qf))
        (m.q.Qtδδ m.δ (m.q.emf m.Qf)) ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      m ∈ {m : Model | m.q.field m.point = 0 ∧ 0 < m.q.routhTrace m.δ (m.q.emf m.Qf) ∧
        0 < m.q.routhFold m.δ (m.q.emf m.Qf) ∧ 0 < m.q.routhHopf m.δ (m.q.emf m.Qf)}) := by
  have hles := mem_den_locallyExponentiallyStable_iff m hM hω
  have hly := mem_den_lyapunovStable_iff_of_hopf_ne m hM hω hG hfold
  unfold powerlib.TMIO.Statement at hles hly ⊢
  exact ⟨fun h => hly.mp (Spectral.den_las_subset_lyapunovStable h),
    fun h => Spectral.den_locallyExponentiallyStable_subset_las (hles.mpr h)⟩

end QVDroopVirtual

end powerlib.GFM
