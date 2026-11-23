import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Calculus
import theorem.PH.Nonlinear
import theorem.PH.Composition

/-! # Constant-coefficient port-Hamiltonian systems

Quadratic Hamiltonians and constant-coefficient port-Hamiltonian systems as instances of
`powerlib.PH.NonlinearModel`, and the bridge to linear port-Hamiltonian plants.

Model boundary.
* State `x : State n = EuclideanSpace ℝ (Fin n)`, input `u : Fin m → ℝ`, continuous time.
* Constant matrices: `J` skew-symmetric, `R` symmetric positive semidefinite, `g` arbitrary,
  `Q` symmetric (not necessarily definite unless stated). Hamiltonian `H(x) = ½ xᵀ Q x`,
  gradient `Q x`.
* Field `ẋ = (J − R) Q x + g u`, output `y = gᵀ Q x`; state matrix `A = (J − R) Q`.
  Lyapunov identity `Aᵀ Q + Q A = −2 Q R Q ⪯ 0`.
* Excluded: state-dependent matrices (see `NonlinearModel`), linearization of a nonlinear
  pH system (the Hessian bridge of T-ph §1.10), transfer functions and positive realness,
  delay, PWM, PLL, saturation.

Source: work-sync `theory/T-ph.md` §1.10 (linear pH form (1.15), `A_ph = (J − R) Q` and its
Lyapunov inequality), §1.6 (RLC instance of constant-coefficient pH).

Results.
* `linearStateMatrix_lyapunov` (the Lyapunov identity above, `Port.PortHamiltonian.lyapunov`),
  `linearStateMatrix_lyapunov_negSemidef`; `linear_lyapunovStable` — every constant-coefficient
  pH system with `Q ≻ 0` is Lyapunov stable (generic, public foundation).
* The linear plant of the system is `linearLTIModel J R g Q : Linear.Plant n m`
  (`A = (J − R) Q`, `B = g`, `C = gᵀ Q`, `D = 0`), and the port system of the pH model **is**
  the port system of that plant (`linear_system_eq`).
* The Hamiltonian is the quadratic energy `Linear.quadraticEnergy Q`
  (`theorem/Linear/Certificate.lean`), with gradient `Q x` (`hasGradientAt_quadraticEnergy`).
* With `Q ≻ 0` the model is the linear port-Hamiltonian plant `toPortHamiltonian J R g Q`
  (`theorem/Port/PortHamiltonian.lean`; its passivity certificate is the plant's KYP
  certificate `Q`, whose storage is the same quadratic energy by definition).
* Diagonal data (`DiagonalPH (Fin n) (Fin m)`, `theorem/PH/Composition.lean`: constant `J`,
  diagonal damping `d ≥ 0`, diagonal weights `w > 0`, `H = Σ wᵢ xᵢ²/2`) are the special case
  `R = diag d`, `Q = diag w` (`ofDiagonal`); the two vector fields, outputs, energies, damping
  powers and port systems coincide under the coordinate identification
  `WithLp.ofLp : State n → (Fin n → ℝ)` (`ofDiagonal_field`, `ofDiagonal_system`).

Family and connection conclusions.
* No new family. `NonlinearModel` is the generic framework (no family takes it as model type),
  so the generic Lyapunov-stability theorem `linear_lyapunovStable` is a public foundation
  result.
* The connection conclusions are memberships of `toPortHamiltonian J R g Q` in the existing
  linear port-Hamiltonian family `Port.PortHamiltonian.family`: passivity and Lyapunov stability
  are `Port.PortHamiltonian.mem_den_passive` and `Port.PortHamiltonian.mem_den_lyapunovStable`
  applied to it, reached through `linear_system_eq` and `toPortHamiltonian_plant`. Solutions of
  the diagonal data and of the plant correspond through the equality of port systems
  `ofDiagonal_system` (every solution notion of the Port semantics transfers by rewriting).
-/

noncomputable section
namespace powerlib.PH
open Matrix Set Filter
open powerlib.Dynamics (State)

variable {n m : ℕ}

/-! ### Quadratic Hamiltonian -/

/-- For symmetric `Q`, the gradient of the quadratic energy `½ xᵀ Q x` (`Linear.quadraticEnergy`)
is `Q x`. -/
@[tmio T, powerlib_foundation] theorem hasGradientAt_quadraticEnergy
    {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Qᵀ = Q) (x : State n) :
    HasGradientAt (Linear.quadraticEnergy Q) (WithLp.toLp 2 (Q *ᵥ WithLp.ofLp x)) x := by
  refine hasGradientAt_of_hasFDerivAt
    ((Linear.contDiff_quadraticEnergy Q).differentiable (by norm_num) x).hasFDerivAt fun v => ?_
  rw [Linear.fderiv_quadraticEnergy_apply hQ, WithLp.ofLp_toLp,
    dotProduct_mulVec, ← mulVec_transpose, hQ]

/-! ### Constant-coefficient port-Hamiltonian systems -/

/-- The constant-coefficient pH system `ẋ = (J − R) Q x + g u`, `y = gᵀ Q x`,
`H = ½ xᵀ Q x`. -/
def linear (J R : Matrix (Fin n) (Fin n) ℝ) (g : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hJ : Jᵀ = -J) (hR : R.PosSemidef) (hQ : Qᵀ = Q) :
    NonlinearModel n m where
  J _ := J
  R _ := R
  g _ := g
  H := Linear.quadraticEnergy Q
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
@[tmio M, simp, powerlib_foundation] theorem linear_H (x : State n) :
    (linear J R g Q hJ hR hQ).H x = Linear.quadraticEnergy Q x := rfl

include hJ hR hQ in
@[tmio M, simp, powerlib_foundation] theorem ofLp_linear_dH (x : State n) :
    WithLp.ofLp ((linear J R g Q hJ hR hQ).dH x) = Q *ᵥ WithLp.ofLp x := rfl

include hJ hR hQ in
/-- The field of the quadratic pH system is `(J − R) Q x + g u`. -/
@[tmio M, powerlib_foundation] theorem linear_field (x : State n) (u : Fin m → ℝ) :
    (linear J R g Q hJ hR hQ).field x u =
      WithLp.toLp 2 (linearStateMatrix J R Q *ᵥ WithLp.ofLp x + g *ᵥ u) := by
  simp only [NonlinearModel.field, linear, linearStateMatrix, WithLp.ofLp_toLp, mulVec_mulVec]

include hJ hR hQ in
@[tmio M, powerlib_foundation] theorem linear_output (x : State n) :
    (linear J R g Q hJ hR hQ).output x = (gᵀ * Q) *ᵥ WithLp.ofLp x := by
  simp only [NonlinearModel.output, linear, WithLp.ofLp_toLp, mulVec_mulVec]

include hJ hR hQ in
/-- The zero-input field is the linear map `x ↦ A x`. -/
@[tmio M, powerlib_foundation] theorem linear_zeroInputField :
    (linear J R g Q hJ hR hQ).zeroInputField =
      ⇑(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (linearStateMatrix J R Q)) := by
  funext x
  apply WithLp.ofLp_injective
  simp [NonlinearModel.zeroInputField, linear_field]

include hJ hR hQ in
/-- The Jacobian of the zero-input field is `A = (J − R) Q` at every point. -/
@[tmio M, powerlib_foundation] theorem fderiv_linear_zeroInputField (x : State n) :
    fderiv ℝ (linear J R g Q hJ hR hQ).zeroInputField x =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (linearStateMatrix J R Q) := by
  rw [linear_zeroInputField]
  exact ContinuousLinearMap.fderiv _

include hJ hQ in
/-- Lyapunov identity of the linear pH system: `Aᵀ Q + Q A = −2 Q R Q` for symmetric `R`. -/
@[tmio T, powerlib_foundation] theorem linearStateMatrix_lyapunov (hRt : Rᵀ = R) :
    (linearStateMatrix J R Q)ᵀ * Q + Q * linearStateMatrix J R Q = -(2 : ℝ) • (Q * R * Q) :=
  Port.PortHamiltonian.lyapunov hJ hRt hQ

include hJ hR hQ in
/-- `Aᵀ Q + Q A ⪯ 0`: its negation `2 Q R Q` is positive semidefinite. -/
@[tmio T, powerlib_foundation] theorem linearStateMatrix_lyapunov_negSemidef :
    (-((linearStateMatrix J R Q)ᵀ * Q + Q * linearStateMatrix J R Q)).PosSemidef := by
  have hRt : Rᵀ = R := hR.isHermitian.isSymm
  rw [linearStateMatrix_lyapunov hJ hQ hRt, neg_smul, neg_neg]
  have h := hR.conjTranspose_mul_mul_same Q
  rw [conjTranspose_eq_transpose_of_trivial, hQ] at h
  exact h.smul (by norm_num)

include hJ hR hQ in
/-- With `Q ≻ 0`, the origin is a strict minimum of `H = ½ xᵀ Q x`. -/
@[tmio T, powerlib_foundation] theorem linear_isStrictLocalMin_zero (hQd : Q.PosDef) :
    (linear J R g Q hJ hR hQ).IsStrictLocalMin 0 := by
  refine eventually_nhdsWithin_of_forall fun x hx => ?_
  have hx0 : WithLp.ofLp x ≠ 0 := fun h => hx (WithLp.ofLp_injective 2 (by simpa using h))
  have hpos := hQd.dotProduct_mulVec_pos hx0
  rw [star_trivial] at hpos
  simp only [linear_H, Linear.quadraticEnergy, WithLp.ofLp_zero, mulVec_zero, dotProduct_zero,
    mul_zero]
  positivity

include hJ hR hQ in
/-- Lyapunov stability of the origin for the zero-input constant-coefficient pH system with
`Q ≻ 0`, `R ⪰ 0` (the semantic form of T-ph §1.10 "`Re λ(A_ph) ≤ 0`"). Generic: for every
constant-coefficient pH system. -/
@[tmio T, powerlib_foundation] theorem linear_lyapunovStable (hQd : Q.PosDef) :
    LyapunovStable (linear J R g Q hJ hR hQ).zeroInputField 0 :=
  (linear_isStrictLocalMin_zero hJ hR hQ hQd).lyapunovStable

end Linear

/-- Two port systems with the same field and output are equal. -/
@[tmio T, powerlib_foundation] theorem system_ext {p : ℕ} {s t : Port.System n p}
    (hf : ∀ x u, s.field x u = t.field x u) (ho : ∀ x u, s.output x u = t.output x u) :
    s = t := by
  cases s
  cases t
  simp only [Port.System.mk.injEq]
  exact ⟨funext fun x => funext (hf x), funext fun x => funext (ho x)⟩

/-- The linear plant of the constant-coefficient pH system: `A = (J − R) Q`, `B = g`,
`C = gᵀ Q`, `D = 0`. -/
def linearLTIModel (J R : Matrix (Fin n) (Fin n) ℝ) (g : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) : Linear.Plant n m :=
  ⟨linearStateMatrix J R Q, g, gᵀ * Q, 0⟩

section LinearLTI

variable {J R : Matrix (Fin n) (Fin n) ℝ} {g : Matrix (Fin n) (Fin m) ℝ}
  {Q : Matrix (Fin n) (Fin n) ℝ} (hJ : Jᵀ = -J) (hR : R.PosSemidef) (hQ : Qᵀ = Q)

include hJ hR hQ in
/-- The port system of the pH model is the port system of its linear plant. -/
@[tmio M, powerlib_foundation] theorem linear_system_eq :
    (linear J R g Q hJ hR hQ).system = (linearLTIModel J R g Q).system := by
  refine system_ext (fun x u => ?_) (fun x u => ?_)
  · apply WithLp.ofLp_injective
    rw [NonlinearModel.system_field, linear_field]
    simp [Linear.Plant.system, linearLTIModel, Linear.op, Matrix.ofLp_toEuclideanCLM]
  · rw [NonlinearModel.system_output, linear_output]
    simp [Linear.Plant.system, linearLTIModel]

end LinearLTI

/-! ### The linear port-Hamiltonian plant -/

/-- With `Q ≻ 0` the constant-coefficient pH system is a linear port-Hamiltonian plant. -/
def toPortHamiltonian (J R : Matrix (Fin n) (Fin n) ℝ) (g : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hJ : Jᵀ = -J) (hR : R.PosSemidef) (hQ : Q.PosDef) :
    Port.PortHamiltonian n m where
  J := J
  R := R
  Q := Q
  B := g
  skew := hJ
  dissipation_symmetric := hR.isHermitian.isSymm
  dissipation_nonneg x := by simpa [star_trivial] using hR.dotProduct_mulVec_nonneg x
  energy_symmetric := hQ.isHermitian.isSymm
  energy_pos x hx := by simpa [star_trivial] using hQ.dotProduct_mulVec_pos hx

@[tmio M, powerlib_foundation] theorem toPortHamiltonian_plant {J R : Matrix (Fin n) (Fin n) ℝ}
    {g : Matrix (Fin n) (Fin m) ℝ} {Q : Matrix (Fin n) (Fin n) ℝ} (hJ : Jᵀ = -J)
    (hR : R.PosSemidef) (hQ : Q.PosDef) :
    (toPortHamiltonian J R g Q hJ hR hQ).plant = linearLTIModel J R g Q := rfl

/-! ### Bridge to diagonal data -/

/-- Diagonal port-Hamiltonian data numbered by `Fin` viewed as a `NonlinearModel`. -/
def ofDiagonal (pm : DiagonalPH (Fin n) (Fin m)) : NonlinearModel n m :=
  linear pm.J (diagonal pm.d) pm.B (diagonal pm.w) pm.skew
    (PosSemidef.diagonal fun i => pm.damping_nonneg i) (diagonal_transpose pm.w)

section Bridge

variable (pm : DiagonalPH (Fin n) (Fin m))

@[tmio M, simp, powerlib_foundation] theorem ofLp_ofDiagonal_dH (x : State n) :
    WithLp.ofLp ((ofDiagonal pm).dH x) = pm.gradient (WithLp.ofLp x) := by
  simp [ofDiagonal]

/-- The two vector fields coincide. -/
@[tmio M, powerlib_foundation] theorem ofDiagonal_field (x : State n) (u : Fin m → ℝ) :
    (ofDiagonal pm).field x u = WithLp.toLp 2 (pm.field (WithLp.ofLp x) u) := by
  apply WithLp.ofLp_injective
  rw [NonlinearModel.ofLp_field, ofLp_ofDiagonal_dH]
  rfl

@[tmio M, powerlib_foundation] theorem ofDiagonal_output (x : State n) :
    (ofDiagonal pm).output x = pm.output (WithLp.ofLp x) := by
  simp only [NonlinearModel.output, ofLp_ofDiagonal_dH]
  rfl

@[tmio M, powerlib_foundation] theorem ofDiagonal_H (x : State n) :
    (ofDiagonal pm).H x = pm.energy (WithLp.ofLp x) := by
  change Linear.quadraticEnergy (diagonal pm.w) x = _
  simp only [Linear.quadraticEnergy, DiagonalPH.energy, dotProduct, mulVec_diagonal, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

@[tmio M, powerlib_foundation] theorem ofDiagonal_dampingPower (x : State n) :
    (ofDiagonal pm).dampingPower x = pm.dampingPower (WithLp.ofLp x) := by
  simp only [NonlinearModel.dampingPower, ofLp_ofDiagonal_dH]
  simp only [ofDiagonal, linear, dotProduct, mulVec_diagonal, DiagonalPH.dampingPower]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[tmio M, powerlib_foundation] theorem ofDiagonal_supply (x : State n) (u : Fin m → ℝ) :
    (ofDiagonal pm).supply x u = pm.supply (WithLp.ofLp x) u := by
  rw [NonlinearModel.supply, ofDiagonal_output]
  rfl

/-- The port system of the pH model is the port system of the numbered diagonal plant; every
solution notion of the Port semantics transfers by rewriting. -/
@[tmio M, powerlib_foundation] theorem ofDiagonal_system :
    (ofDiagonal pm).system = (pm.toPH (Equiv.refl _) (Equiv.refl _)).plant.system := by
  refine system_ext (fun x u => ?_) (fun x u => ?_)
  · apply WithLp.ofLp_injective
    rw [DiagonalPH.toPH_field, NonlinearModel.system_field]
    exact congrArg WithLp.ofLp (ofDiagonal_field pm x u)
  · rw [DiagonalPH.toPH_output, NonlinearModel.system_output]
    exact ofDiagonal_output pm x

end Bridge

end powerlib.PH
