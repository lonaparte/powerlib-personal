import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Calculus
import theorem.PH.Nonlinear
import theorem.PortHamiltonian

/-! Quadratic Hamiltonians and constant-coefficient port-Hamiltonian systems as instances of
`powerlib.PH.NonlinearModel`, and the bridge to `powerlib.PortHamiltonian.Model`.

Model boundary.
* State `x : State n = EuclideanSpace ℝ (Fin n)`, input `u : Fin m → ℝ`, continuous time.
* Constant matrices: `J` skew-symmetric, `R` symmetric positive semidefinite, `g` arbitrary,
  `Q` symmetric (not necessarily definite unless stated). Hamiltonian `H(x) = ½ xᵀ Q x`,
  gradient `Q x`.
* Field `ẋ = (J − R) Q x + g u`, output `y = gᵀ Q x`; state matrix `A = (J − R) Q`.
  Lyapunov identity `Aᵀ Q + Q A = −2 Q R Q ⪯ 0`.
* With `Q ≻ 0`, the model is an `LTI.Model` carrying a
  `StateSpacePassivity.CollocatedCertificate` with storage matrix `Q`.
* `PortHamiltonian.Model (Fin n) (Fin m)` (constant `J`, diagonal damping `d ≥ 0`, diagonal
  weights `w > 0`, `H = Σ wᵢ xᵢ²/2`) is the special case `R = diag d`, `Q = diag w`; the two
  vector fields, outputs, energies, damping powers and trajectory notions coincide under the
  coordinate identification `WithLp.ofLp : State n → (Fin n → ℝ)`.
* Excluded: state-dependent matrices (see `NonlinearModel`), linearization of a nonlinear
  pH system (the Hessian bridge of T-ph §1.10), transfer functions and positive realness,
  delay, PWM, PLL, saturation.

Source: work-sync `theory/T-ph.md` §1.10 (linear pH form (1.15), `A_ph = (J − R) Q` and its
Lyapunov inequality), §1.6 (RLC instance of constant-coefficient pH).
-/

noncomputable section
namespace powerlib.PH
open Matrix Set Filter
open powerlib.Dynamics (State)

variable {n m : ℕ}

/-! ### Quadratic Hamiltonian -/

/-- The quadratic Hamiltonian `½ xᵀ Q x`. -/
def quadraticEnergy (Q : Matrix (Fin n) (Fin n) ℝ) (x : State n) : ℝ :=
  (1 / 2 : ℝ) * (WithLp.ofLp x ⬝ᵥ (Q *ᵥ WithLp.ofLp x))

@[powerlib_foundation] theorem quadraticEnergy_eq_stateSpace (Q : Matrix (Fin n) (Fin n) ℝ)
    (x : State n) :
    quadraticEnergy Q x = StateSpacePassivity.energy Q (WithLp.ofLp x) := by
  simp only [quadraticEnergy, StateSpacePassivity.energy, LTI.energy]
  ring

/-- For symmetric `Q`, the gradient of `½ xᵀ Q x` is `Q x`. -/
@[powerlib_foundation] theorem hasGradientAt_quadraticEnergy {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Qᵀ = Q) (x : State n) :
    HasGradientAt (quadraticEnergy Q) (WithLp.toLp 2 (Q *ᵥ WithLp.ofLp x)) x := by
  let A := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Q
  have hin := ((hasFDerivAt_id x).inner ℝ A.hasFDerivAt).const_mul (1 / 2 : ℝ)
  have hfun : quadraticEnergy Q = fun y => (1 / 2 : ℝ) * inner ℝ (id y) (A y) := by
    funext y
    simp [quadraticEnergy, inner_eq_dotProduct, A]
  rw [hfun]
  refine hasGradientAt_of_hasFDerivAt hin fun v => ?_
  have hsym : WithLp.ofLp x ⬝ᵥ (Q *ᵥ WithLp.ofLp v) = (Q *ᵥ WithLp.ofLp x) ⬝ᵥ WithLp.ofLp v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hQ]
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, id_eq, ContinuousLinearMap.id_apply,
    inner_eq_dotProduct, smul_eq_mul, A, Matrix.ofLp_toEuclideanCLM]
  rw [hsym, dotProduct_comm (WithLp.ofLp v)]
  ring

/-! ### Constant-coefficient port-Hamiltonian systems -/

/-- The constant-coefficient pH system `ẋ = (J − R) Q x + g u`, `y = gᵀ Q x`,
`H = ½ xᵀ Q x`. -/
def linear (J R : Matrix (Fin n) (Fin n) ℝ) (g : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hJ : Jᵀ = -J) (hR : R.PosSemidef) (hQ : Qᵀ = Q) :
    NonlinearModel n m where
  J _ := J
  R _ := R
  g _ := g
  H := quadraticEnergy Q
  dH x := WithLp.toLp 2 (Q *ᵥ WithLp.ofLp x)
  skew _ := hJ
  dissipation_posSemidef _ := hR
  hasGradient := hasGradientAt_quadraticEnergy hQ

/-- The state matrix `A = (J − R) Q`. -/
def linearStateMatrix (J R Q : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (J - R) * Q

section Linear

variable {J R : Matrix (Fin n) (Fin n) ℝ} {g : Matrix (Fin n) (Fin m) ℝ}
  {Q : Matrix (Fin n) (Fin n) ℝ} (hJ : Jᵀ = -J) (hR : R.PosSemidef) (hQ : Qᵀ = Q)

include hJ hR hQ in
@[simp, powerlib_foundation] theorem linear_H (x : State n) :
    (linear J R g Q hJ hR hQ).H x = quadraticEnergy Q x := rfl

include hJ hR hQ in
@[simp, powerlib_foundation] theorem ofLp_linear_dH (x : State n) :
    WithLp.ofLp ((linear J R g Q hJ hR hQ).dH x) = Q *ᵥ WithLp.ofLp x := rfl

include hJ hR hQ in
/-- The field of the quadratic pH system is `(J − R) Q x + g u`. -/
@[powerlib_foundation] theorem linear_field (x : State n) (u : Fin m → ℝ) :
    (linear J R g Q hJ hR hQ).field x u =
      WithLp.toLp 2 (linearStateMatrix J R Q *ᵥ WithLp.ofLp x + g *ᵥ u) := by
  simp only [NonlinearModel.field, linear, linearStateMatrix, WithLp.ofLp_toLp, mulVec_mulVec]

include hJ hR hQ in
@[powerlib_foundation] theorem linear_output (x : State n) :
    (linear J R g Q hJ hR hQ).output x = (gᵀ * Q) *ᵥ WithLp.ofLp x := by
  simp only [NonlinearModel.output, linear, WithLp.ofLp_toLp, mulVec_mulVec]

include hJ hR hQ in
/-- The zero-input field is the linear map `x ↦ A x`. -/
@[powerlib_foundation] theorem linear_zeroInputField :
    (linear J R g Q hJ hR hQ).zeroInputField =
      ⇑(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (linearStateMatrix J R Q)) := by
  funext x
  apply WithLp.ofLp_injective
  simp [NonlinearModel.zeroInputField, linear_field]

include hJ hR hQ in
/-- The Jacobian of the zero-input field is `A = (J − R) Q` at every point. -/
@[powerlib_foundation] theorem fderiv_linear_zeroInputField (x : State n) :
    fderiv ℝ (linear J R g Q hJ hR hQ).zeroInputField x =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (linearStateMatrix J R Q) := by
  rw [linear_zeroInputField]
  exact ContinuousLinearMap.fderiv _

include hJ hQ in
/-- Lyapunov identity of the linear pH system: `Aᵀ Q + Q A = −2 Q R Q` for symmetric `R`. -/
@[powerlib_foundation] theorem linearStateMatrix_lyapunov (hRt : Rᵀ = R) :
    (linearStateMatrix J R Q)ᵀ * Q + Q * linearStateMatrix J R Q = -(2 : ℝ) • (Q * R * Q) := by
  rw [linearStateMatrix, transpose_mul, transpose_sub, hJ, hRt, hQ, neg_smul, two_smul]
  noncomm_ring

include hJ hR hQ in
/-- `Aᵀ Q + Q A ⪯ 0`: its negation `2 Q R Q` is positive semidefinite. -/
@[powerlib_foundation] theorem linearStateMatrix_lyapunov_negSemidef :
    (-((linearStateMatrix J R Q)ᵀ * Q + Q * linearStateMatrix J R Q)).PosSemidef := by
  have hRt : Rᵀ = R := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
  rw [linearStateMatrix_lyapunov hJ hQ hRt, neg_smul, neg_neg]
  have h := hR.conjTranspose_mul_mul_same Q
  rw [conjTranspose_eq_transpose_of_trivial, hQ] at h
  exact h.smul (by norm_num)

include hJ hR hQ in
/-- With `Q ≻ 0`, the origin is a strict minimum of `H = ½ xᵀ Q x`. -/
@[powerlib_foundation] theorem linear_isStrictLocalMin_zero (hQd : Q.PosDef) :
    (linear J R g Q hJ hR hQ).IsStrictLocalMin 0 := by
  refine eventually_nhdsWithin_of_forall fun x hx => ?_
  have hx0 : WithLp.ofLp x ≠ 0 := fun h => hx (WithLp.ofLp_injective 2 (by simpa using h))
  have hpos := hQd.dotProduct_mulVec_pos hx0
  rw [star_trivial] at hpos
  simp only [linear_H, quadraticEnergy, WithLp.ofLp_zero, mulVec_zero, dotProduct_zero, mul_zero]
  positivity

include hJ hR hQ in
/-- Lyapunov stability of the origin for the zero-input constant-coefficient pH system with
`Q ≻ 0`, `R ⪰ 0` (the semantic form of T-ph §1.10 "`Re λ(A_ph) ≤ 0`"). -/
@[powerlib_domain] theorem linear_lyapunovStable (hQd : Q.PosDef) :
    Dynamics.LyapunovStable (linear J R g Q hJ hR hQ).zeroInputField 0 :=
  (linear_isStrictLocalMin_zero hJ hR hQ hQd).lyapunovStable

end Linear

/-- The constant-coefficient pH system as an `LTI.Model`: `A = (J − R) Q`, `B = g`,
`C = gᵀ Q`, `D = 0`. -/
def linearLTIModel (J R : Matrix (Fin n) (Fin n) ℝ) (g : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) : LTI.Model (Fin n) (Fin m) where
  A := linearStateMatrix J R Q
  B := g
  C := gᵀ * Q
  D := 0

section LinearLTI

variable {J R : Matrix (Fin n) (Fin n) ℝ} {g : Matrix (Fin n) (Fin m) ℝ}
  {Q : Matrix (Fin n) (Fin n) ℝ} (hJ : Jᵀ = -J) (hR : R.PosSemidef) (hQ : Qᵀ = Q)

include hJ hR hQ in
@[powerlib_foundation] theorem linearLTIModel_field (x : State n) (u : Fin m → ℝ) :
    LTI.Model.field (linearLTIModel J R g Q) (WithLp.ofLp x) u =
      WithLp.ofLp ((linear J R g Q hJ hR hQ).field x u) := by
  rw [linear_field]
  rfl

include hJ hR hQ in
@[powerlib_foundation] theorem linearLTIModel_output (x : State n) (u : Fin m → ℝ) :
    LTI.Model.output (linearLTIModel J R g Q) (WithLp.ofLp x) u =
      (linear J R g Q hJ hR hQ).output x := by
  rw [linear_output]
  simp [LTI.Model.output, linearLTIModel]

end LinearLTI

/-- For `Q ≻ 0`, the linear pH system carries a collocated passivity certificate with
storage matrix `Q` (so the `StateSpacePassivity` theorems apply). -/
def linearCollocatedCertificate {J R : Matrix (Fin n) (Fin n) ℝ} (g : Matrix (Fin n) (Fin m) ℝ)
    {Q : Matrix (Fin n) (Fin n) ℝ} (hJ : Jᵀ = -J) (hR : R.PosSemidef) (hQ : Q.PosDef) :
    StateSpacePassivity.CollocatedCertificate (linearLTIModel J R g Q) where
  P := Q
  positive := hQ
  dissipation := by
    have h := linearStateMatrix_lyapunov_negSemidef hJ hR
      (StateSpacePassivity.symmetric_of_posDef hQ)
    change (-(Q * linearStateMatrix J R Q + (linearStateMatrix J R Q)ᵀ * Q)).PosSemidef
    rwa [add_comm]
  collocated := by
    simp only [linearLTIModel, transpose_mul, transpose_transpose,
      StateSpacePassivity.symmetric_of_posDef hQ]
  feedthrough := PosSemidef.zero

/-! ### Bridge to `powerlib.PortHamiltonian.Model` -/

/-- A diagonal-quadratic `PortHamiltonian.Model` viewed as a `NonlinearModel`. -/
def ofPortHamiltonian (pm : PortHamiltonian.Model (Fin n) (Fin m)) : NonlinearModel n m :=
  linear pm.J (diagonal pm.d) pm.B (diagonal pm.w) pm.skew
    (PosSemidef.diagonal fun i => pm.damping_nonneg i) (diagonal_transpose pm.w)

section Bridge

variable (pm : PortHamiltonian.Model (Fin n) (Fin m))

@[simp, powerlib_foundation] theorem ofLp_ofPortHamiltonian_dH (x : State n) :
    WithLp.ofLp ((ofPortHamiltonian pm).dH x) = PortHamiltonian.gradient pm (WithLp.ofLp x) := by
  simp [ofPortHamiltonian]

/-- The two vector fields coincide. -/
@[powerlib_foundation] theorem ofPortHamiltonian_field (x : State n) (u : Fin m → ℝ) :
    (ofPortHamiltonian pm).field x u =
      WithLp.toLp 2 (PortHamiltonian.field pm (WithLp.ofLp x) u) := by
  apply WithLp.ofLp_injective
  rw [NonlinearModel.ofLp_field, ofLp_ofPortHamiltonian_dH]
  rfl

@[powerlib_foundation] theorem ofLp_ofPortHamiltonian_field (x : State n) (u : Fin m → ℝ) :
    WithLp.ofLp ((ofPortHamiltonian pm).field x u) =
      PortHamiltonian.field pm (WithLp.ofLp x) u := by
  rw [ofPortHamiltonian_field]

@[powerlib_foundation] theorem ofPortHamiltonian_output (x : State n) :
    (ofPortHamiltonian pm).output x = PortHamiltonian.output pm (WithLp.ofLp x) := by
  simp only [NonlinearModel.output, ofLp_ofPortHamiltonian_dH]
  rfl

@[powerlib_foundation] theorem ofPortHamiltonian_H (x : State n) :
    (ofPortHamiltonian pm).H x = PortHamiltonian.energy pm (WithLp.ofLp x) := by
  change quadraticEnergy (diagonal pm.w) x = _
  rw [quadraticEnergy_eq_stateSpace, PortHamiltonian.energy_eq]

@[powerlib_foundation] theorem ofPortHamiltonian_dampingPower (x : State n) :
    (ofPortHamiltonian pm).dampingPower x =
      PortHamiltonian.dampingPower pm (WithLp.ofLp x) := by
  simp only [NonlinearModel.dampingPower, ofLp_ofPortHamiltonian_dH]
  simp only [ofPortHamiltonian, linear, dotProduct, mulVec_diagonal, PortHamiltonian.dampingPower]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[powerlib_foundation] theorem ofPortHamiltonian_supply (x : State n) (u : Fin m → ℝ) :
    (ofPortHamiltonian pm).supply x u =
      Passivity.supply (PortHamiltonian.system pm) (WithLp.ofLp x) u := by
  change u ⬝ᵥ (ofPortHamiltonian pm).output x = ∑ i, u i * PortHamiltonian.output pm _ i
  rw [ofPortHamiltonian_output]
  rfl

/-- Input/state trajectories of the two models correspond under `WithLp.ofLp`. -/
@[powerlib_foundation] theorem ofPortHamiltonian_isTrajectory_iff
    {u : ℝ → (Fin m → ℝ)} {x : ℝ → State n} :
    Passivity.IsTrajectory (ofPortHamiltonian pm).toSystem u x ↔
      Passivity.IsTrajectory (PortHamiltonian.system pm) u (fun t => WithLp.ofLp (x t)) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  constructor
  · intro hx t ht
    have h := e.hasFDerivAt.comp_hasDerivWithinAt t (hx t ht)
    have hfield : e ((ofPortHamiltonian pm).toSystem.field (x t) (u t)) =
        (PortHamiltonian.system pm).field (WithLp.ofLp (x t)) (u t) :=
      ofLp_ofPortHamiltonian_field pm (x t) (u t)
    convert h using 1
    · rfl
    · exact hfield.symm
  · intro hx t ht
    have h := e.symm.hasFDerivAt.comp_hasDerivWithinAt t (hx t ht)
    have hfield : (ofPortHamiltonian pm).toSystem.field (x t) (u t) =
        e.symm ((PortHamiltonian.system pm).field (WithLp.ofLp (x t)) (u t)) := by
      rw [NonlinearModel.toSystem_field, ofPortHamiltonian_field]
      rfl
    rw [hfield]
    exact h

end Bridge

end powerlib.PH
