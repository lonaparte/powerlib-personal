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
* `linearStateMatrix_lyapunov`, `linearStateMatrix_lyapunov_negSemidef` — the Lyapunov identity
  above; `linear_lyapunovStable` — every constant-coefficient pH system with `Q ≻ 0` is Lyapunov
  stable (generic, public foundation).
* The linear plant of the system is `linearLTIModel J R g Q : Linear.Plant n m`
  (`A = (J − R) Q`, `B = g`, `C = gᵀ Q`, `D = 0`), and the port system of the pH model **is**
  the port system of that plant (`linear_system_eq`).
* With `Q ≻ 0` the model is the linear port-Hamiltonian plant `toPortHamiltonian J R g Q`
  (`theorem/Port/PortHamiltonian.lean`; its passivity certificate is the plant's KYP
  certificate `Q`); `quadraticEnergy_eq_storage` — the quadratic Hamiltonian is its stored
  energy.
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
  (`toPortHamiltonian_mem_den_passive`, `toPortHamiltonian_mem_den_lyapunovStable`), reached
  through `linear_system_eq` and `toPortHamiltonian_plant`. Solutions of the diagonal data and
  of the plant correspond through the equality of port systems `ofDiagonal_system` (every
  solution notion of the Port semantics transfers by rewriting).
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
`Q ≻ 0`, `R ⪰ 0` (the semantic form of T-ph §1.10 "`Re λ(A_ph) ≤ 0`"). Generic: for every
constant-coefficient pH system. -/
@[powerlib_foundation] theorem linear_lyapunovStable (hQd : Q.PosDef) :
    LyapunovStable (linear J R g Q hJ hR hQ).zeroInputField 0 :=
  (linear_isStrictLocalMin_zero hJ hR hQ hQd).lyapunovStable

end Linear

/-- Two port systems with the same field and output are equal. -/
@[powerlib_foundation] theorem system_ext {p : ℕ} {s t : Port.System n p}
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
@[powerlib_foundation] theorem linear_system_eq :
    (linear J R g Q hJ hR hQ).system = (linearLTIModel J R g Q).system := by
  refine system_ext (fun x u => ?_) (fun x u => ?_)
  · apply WithLp.ofLp_injective
    rw [NonlinearModel.system_field, linear_field]
    simp [Linear.Plant.system, linearLTIModel, Linear.op, Matrix.ofLp_toEuclideanCLM]
  · rw [NonlinearModel.system_output, linear_output]
    simp [Linear.Plant.system, linearLTIModel]

include hJ hR hQ in
@[powerlib_foundation] theorem linearLTIModel_field (x : State n) (u : Fin m → ℝ) :
    (linearLTIModel J R g Q).system.field x u = (linear J R g Q hJ hR hQ).field x u := by
  rw [← linear_system_eq hJ hR hQ]
  rfl

include hJ hR hQ in
@[powerlib_foundation] theorem linearLTIModel_output (x : State n) (u : Fin m → ℝ) :
    (linearLTIModel J R g Q).system.output x u = (linear J R g Q hJ hR hQ).output x := by
  rw [← linear_system_eq hJ hR hQ]
  rfl

end LinearLTI

/-! ### The linear port-Hamiltonian plant -/

@[powerlib_foundation] theorem symmetric_of_posSemidef {R : Matrix (Fin n) (Fin n) ℝ}
    (hR : R.PosSemidef) : Rᵀ = R := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq

@[powerlib_foundation] theorem symmetric_of_posDef {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.PosDef) : Qᵀ = Q :=
  symmetric_of_posSemidef hQ.posSemidef

/-- With `Q ≻ 0` the constant-coefficient pH system is a linear port-Hamiltonian plant. -/
def toPortHamiltonian (J R : Matrix (Fin n) (Fin n) ℝ) (g : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hJ : Jᵀ = -J) (hR : R.PosSemidef) (hQ : Q.PosDef) :
    Port.PortHamiltonian n m where
  J := J
  R := R
  Q := Q
  B := g
  skew := hJ
  dissipation_symmetric := symmetric_of_posSemidef hR
  dissipation_nonneg x := by simpa [star_trivial] using hR.dotProduct_mulVec_nonneg x
  energy_symmetric := symmetric_of_posDef hQ
  energy_pos x hx := by simpa [star_trivial] using hQ.dotProduct_mulVec_pos hx

@[powerlib_foundation] theorem toPortHamiltonian_plant {J R : Matrix (Fin n) (Fin n) ℝ}
    {g : Matrix (Fin n) (Fin m) ℝ} {Q : Matrix (Fin n) (Fin n) ℝ} (hJ : Jᵀ = -J)
    (hR : R.PosSemidef) (hQ : Q.PosDef) :
    (toPortHamiltonian J R g Q hJ hR hQ).plant = linearLTIModel J R g Q := rfl

/-- The port system of the pH model is the port system of the linear port-Hamiltonian plant. -/
@[powerlib_foundation] theorem linear_system_eq_toPortHamiltonian {J R : Matrix (Fin n) (Fin n) ℝ}
    {g : Matrix (Fin n) (Fin m) ℝ} {Q : Matrix (Fin n) (Fin n) ℝ} (hJ : Jᵀ = -J)
    (hR : R.PosSemidef) (hQ : Q.PosDef) :
    (linear J R g Q hJ hR (symmetric_of_posDef hQ)).system =
      (toPortHamiltonian J R g Q hJ hR hQ).plant.system := by
  rw [toPortHamiltonian_plant, linear_system_eq]

/-- The quadratic Hamiltonian is the stored energy of the linear port-Hamiltonian plant. -/
@[powerlib_foundation] theorem quadraticEnergy_eq_storage {J R : Matrix (Fin n) (Fin n) ℝ}
    {g : Matrix (Fin n) (Fin m) ℝ} {Q : Matrix (Fin n) (Fin n) ℝ} (hJ : Jᵀ = -J)
    (hR : R.PosSemidef) (hQ : Q.PosDef) (x : State n) :
    quadraticEnergy Q x = (toPortHamiltonian J R g Q hJ hR hQ).kyp.storage x := by
  simp only [quadraticEnergy, Linear.KYP.storage, Port.PortHamiltonian.kyp, toPortHamiltonian]
  ring

/-- Every constant-coefficient pH system with `Q ≻ 0`, `R ⪰ 0` is passive (storage
`½ xᵀ Q x`). -/
@[powerlib_domain] theorem toPortHamiltonian_mem_den_passive {J R : Matrix (Fin n) (Fin n) ℝ}
    (g : Matrix (Fin n) (Fin m) ℝ) {Q : Matrix (Fin n) (Fin n) ℝ} (hJ : Jᵀ = -J)
    (hR : R.PosSemidef) (hQ : Q.PosDef) :
    connection% (toPortHamiltonian J R g Q hJ hR hQ ∈ Port.PortHamiltonian.family.den .passive) :=
  Port.PortHamiltonian.mem_den_passive _

/-- Every unforced constant-coefficient pH system with `Q ≻ 0`, `R ⪰ 0` is Lyapunov stable at
the origin. -/
@[powerlib_domain] theorem toPortHamiltonian_mem_den_lyapunovStable
    {J R : Matrix (Fin n) (Fin n) ℝ} (g : Matrix (Fin n) (Fin m) ℝ)
    {Q : Matrix (Fin n) (Fin n) ℝ} (hJ : Jᵀ = -J) (hR : R.PosSemidef) (hQ : Q.PosDef) :
    connection% (toPortHamiltonian J R g Q hJ hR hQ ∈
      Port.PortHamiltonian.family.den (.flow .lyapunovStable)) :=
  Port.PortHamiltonian.mem_den_lyapunovStable _

/-! ### Bridge to diagonal data -/

/-- Diagonal port-Hamiltonian data numbered by `Fin` viewed as a `NonlinearModel`. -/
def ofDiagonal (pm : DiagonalPH (Fin n) (Fin m)) : NonlinearModel n m :=
  linear pm.J (diagonal pm.d) pm.B (diagonal pm.w) pm.skew
    (PosSemidef.diagonal fun i => pm.damping_nonneg i) (diagonal_transpose pm.w)

section Bridge

variable (pm : DiagonalPH (Fin n) (Fin m))

@[simp, powerlib_foundation] theorem ofLp_ofDiagonal_dH (x : State n) :
    WithLp.ofLp ((ofDiagonal pm).dH x) = pm.gradient (WithLp.ofLp x) := by
  simp [ofDiagonal]

/-- The two vector fields coincide. -/
@[powerlib_foundation] theorem ofDiagonal_field (x : State n) (u : Fin m → ℝ) :
    (ofDiagonal pm).field x u = WithLp.toLp 2 (pm.field (WithLp.ofLp x) u) := by
  apply WithLp.ofLp_injective
  rw [NonlinearModel.ofLp_field, ofLp_ofDiagonal_dH]
  rfl

@[powerlib_foundation] theorem ofLp_ofDiagonal_field (x : State n) (u : Fin m → ℝ) :
    WithLp.ofLp ((ofDiagonal pm).field x u) = pm.field (WithLp.ofLp x) u := by
  rw [ofDiagonal_field]

@[powerlib_foundation] theorem ofDiagonal_output (x : State n) :
    (ofDiagonal pm).output x = pm.output (WithLp.ofLp x) := by
  simp only [NonlinearModel.output, ofLp_ofDiagonal_dH]
  rfl

@[powerlib_foundation] theorem ofDiagonal_H (x : State n) :
    (ofDiagonal pm).H x = pm.energy (WithLp.ofLp x) := by
  change quadraticEnergy (diagonal pm.w) x = _
  simp only [quadraticEnergy, DiagonalPH.energy, dotProduct, mulVec_diagonal, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

@[powerlib_foundation] theorem ofDiagonal_dampingPower (x : State n) :
    (ofDiagonal pm).dampingPower x = pm.dampingPower (WithLp.ofLp x) := by
  simp only [NonlinearModel.dampingPower, ofLp_ofDiagonal_dH]
  simp only [ofDiagonal, linear, dotProduct, mulVec_diagonal, DiagonalPH.dampingPower]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[powerlib_foundation] theorem ofDiagonal_supply (x : State n) (u : Fin m → ℝ) :
    (ofDiagonal pm).supply x u = pm.supply (WithLp.ofLp x) u := by
  rw [NonlinearModel.supply, ofDiagonal_output]
  rfl

/-- The port system of the pH model is the port system of the numbered diagonal plant; every
solution notion of the Port semantics transfers by rewriting. -/
@[powerlib_foundation] theorem ofDiagonal_system :
    (ofDiagonal pm).system = (pm.toPH (Equiv.refl _) (Equiv.refl _)).plant.system := by
  refine system_ext (fun x u => ?_) (fun x u => ?_)
  · apply WithLp.ofLp_injective
    rw [DiagonalPH.toPH_field, NonlinearModel.system_field]
    exact ofLp_ofDiagonal_field pm x u
  · rw [DiagonalPH.toPH_output, NonlinearModel.system_output]
    exact ofDiagonal_output pm x

end Bridge

end powerlib.PH
