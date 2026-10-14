import theorem.Port.PortHamiltonian
import theorem.Linear.Coordinates
import theorem.Criteria.Lyapunov

/-! # Composition of port-Hamiltonian systems (foundation layer)

* Diagonal linear port-Hamiltonian data (`DiagonalPH ι κ`): a constant skew interconnection
  `J`, diagonal damping `R = diag d ≥ 0`, diagonal energy weights `Q = diag w > 0`
  (`H = Σ wᵢ xᵢ² / 2`) and an input matrix `B`, on arbitrary finite state and port index types;
  field `ẋ = (J − R) ∇H + B u`, collocated output `y = Bᵀ ∇H`, incoming-positive port power
  `uᵀ y`. Continuous time, constant matrices; no switching, delay, saturation or controller.
  The data are static: their behaviour is the behaviour of the linear port-Hamiltonian plant
  `toPH e e' : Port.PortHamiltonian n p` obtained by numbering the states by `e : ι ≃ Fin n` and
  the ports by `e' : κ ≃ Fin p`. Its field, output, supplied power and stored energy are those
  of the data read through the numbering (`toPH_field`, `toPH_output`, `toPH_supply`,
  `toPH_storage`), and data related by a coordinate change give similar plants (`toPH_similar`).
* Power-preserving interconnection (T-ph §1.5, (1.9)–(1.10)). Two diagonal models
  `m₁ : DiagonalPH ι₁ κ₁`, `m₂ : DiagonalPH ι₂ κ₂` are coupled by
  `u₁ = −Mᵀ y₂ + g₁ u`, `u₂ = M y₁ + g₂ u` (`M : κ₂ × κ₁`, external input `u : κ → ℝ`).
  The composite is again a `DiagonalPH (ι₁ ⊕ ι₂) κ` with
  `J = [[J₁, −B₁ Mᵀ B₂ᵀ], [B₂ M B₁ᵀ, J₂]]`, `R = blkdiag(R₁, R₂)`, `H = H₁ + H₂`,
  `B = [B₁ g₁; B₂ g₂]`; its field restricts to the two subsystem fields under the coupling law,
  and it is passive (compositionality).
* Block structure (T-power-system-ph §1.4–§1.5.2): block-diagonal PSD dissipation, adding
  skew pairs keeps `J` skew, adding a nonnegative diagonal (constant-impedance loads) keeps
  `R ⪰ 0`.
* Frame rotation (T-power-system-ph §1.2, `v·i` is frame invariant):
  `Transform.frameRotation_power_invariant` in `theorem/Transform/Park.lean`.
* Kron reduction (T-power-system-ph §1.7): `Network.kron_current`, `Network.kron_power`,
  `Network.kron_posSemidef` in `theorem/Network/WeightedLaplacian.lean`.
* Strictly damped diagonal models: the energy `H = Σ wᵢ xᵢ² / 2` is `C¹` with derivative
  `∇H · v` (`energy_hasFDerivAt`, `fderiv_energy_apply`, `energy_contDiff`), the unforced
  field is `C¹` (`zeroInput_contDiff`), and a model whose every state is damped is globally
  exponentially stable in every numbering (`toPH_mem_den_globallyExponentiallyStable`).
* State dimension (T-power-system-ph §1.8, `7N + ℓ + n_C`): `Synchronous.powerSystem_state_dim`
  in `theorem/Synchronous/SMIB11PH.lean`.

Family and connection conclusions. No new family is introduced: every numbered model is a
member of the linear port-Hamiltonian family `Port.PortHamiltonian.family`
(`theorem/Port/PortHamiltonian.lean`), whose system map reads a plant as its port system and
whose sentences are interpreted at the origin. The connection conclusions here are memberships
in its denotations, valid for every linear port-Hamiltonian plant: strictly positive dissipation
places a plant in every attractive sentence and in sampled contraction
(`mem_den_of_dissipation_pos`, `mem_den_globallyExponentiallyStable_of_dissipation_pos`, through
the strict Lyapunov inequality `xᵀ Q A x = −(Q x)ᵀ R (Q x)`, `Criteria.isHurwitz_of_lyapunov`); no
dissipation places it in conservation (`mem_den_conservative_of_lossless`); strict dissipation
excludes conservation (`not_mem_den_conservative_of_dissipation_pos`); similar plants share every
sentence (`mem_den_iff_of_similar`); and every numbering of an interconnection is passive and
Lyapunov stable (`interconnect_mem_den_passive`, `interconnect_mem_den_lyapunovStable`). The
former public trajectory projections `interconnect_trajectory_inl`/`_inr` are private
implementation evidence (trajectory-level, outside the sentence language). All other results
are static algebra.

Source: work-sync `theory/T-ph.md` §1.5 (1.9)–(1.10);
`theory/T-power-system-ph.md` §1.2, §1.4, §1.5, §1.5.2, §1.7, §1.8.
-/

noncomputable section
namespace powerlib.PH
open Matrix Set LinearSystems

/-! ## Diagonal port-Hamiltonian data -/

/-- Diagonal linear port-Hamiltonian data on finite index types: skew `J`, damping `diag d ≥ 0`,
energy weights `diag w > 0`, input matrix `B`. -/
structure DiagonalPH (ι κ : Type*) where
  J : Matrix ι ι ℝ
  d : ι → ℝ
  w : ι → ℝ
  B : Matrix ι κ ℝ
  skew : Jᵀ = -J
  damping_nonneg : ∀ i, 0 ≤ d i
  weights_pos : ∀ i, 0 < w i

namespace DiagonalPH

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- The co-energy `∇H = Q x`. -/
def gradient (m : DiagonalPH ι κ) (x : ι → ℝ) : ι → ℝ := fun i => m.w i * x i

/-- The state field `(J − R) ∇H + B u`. -/
def field (m : DiagonalPH ι κ) (x : ι → ℝ) (u : κ → ℝ) : ι → ℝ :=
  (m.J - diagonal m.d) *ᵥ m.gradient x + m.B *ᵥ u

/-- The collocated output `Bᵀ ∇H`. -/
def output (m : DiagonalPH ι κ) (x : ι → ℝ) : κ → ℝ := m.Bᵀ *ᵥ m.gradient x

/-- The supplied power `uᵀ y`. -/
def supply (m : DiagonalPH ι κ) (x : ι → ℝ) (u : κ → ℝ) : ℝ := u ⬝ᵥ m.output x

/-- The stored energy `H = Σ wᵢ xᵢ² / 2`. -/
def energy (m : DiagonalPH ι κ) (x : ι → ℝ) : ℝ := ∑ i, m.w i * x i ^ 2 / 2

/-- The dissipated power `∇Hᵀ R ∇H`. -/
def dampingPower (m : DiagonalPH ι κ) (x : ι → ℝ) : ℝ := ∑ i, m.d i * m.gradient x i ^ 2

/-- The state matrix `(J − R) Q`. -/
def stateMatrix (m : DiagonalPH ι κ) : Matrix ι ι ℝ := (m.J - diagonal m.d) * diagonal m.w

omit [Fintype κ] in
@[simp, powerlib_foundation] theorem diagonal_mulVec_gradient (m : DiagonalPH ι κ)
    (x : ι → ℝ) : diagonal m.w *ᵥ x = m.gradient x := by
  ext i
  exact mulVec_diagonal m.w x i

@[powerlib_foundation] theorem field_eq_stateMatrix (m : DiagonalPH ι κ) (x : ι → ℝ)
    (u : κ → ℝ) : m.field x u = m.stateMatrix *ᵥ x + m.B *ᵥ u := by
  rw [field, stateMatrix, ← mulVec_mulVec, diagonal_mulVec_gradient]

omit [Fintype κ] [DecidableEq ι] in
@[powerlib_foundation] theorem dampingPower_nonneg (m : DiagonalPH ι κ) (x : ι → ℝ) :
    0 ≤ m.dampingPower x :=
  Finset.sum_nonneg fun i _ => mul_nonneg (m.damping_nonneg i) (sq_nonneg _)

/-- Power balance: `∇Hᵀ ẋ = uᵀ y − Σ dᵢ (∇H)ᵢ²`. -/
@[powerlib_foundation] theorem power_balance (m : DiagonalPH ι κ) (x : ι → ℝ) (u : κ → ℝ) :
    m.gradient x ⬝ᵥ m.field x u = m.supply x u - m.dampingPower x := by
  have hskew : m.gradient x ⬝ᵥ (m.J *ᵥ m.gradient x) = 0 := by
    have h : m.gradient x ⬝ᵥ (m.J *ᵥ m.gradient x) =
        -(m.gradient x ⬝ᵥ (m.J *ᵥ m.gradient x)) := by
      calc
        _ = (m.Jᵀ *ᵥ m.gradient x) ⬝ᵥ m.gradient x := by
          rw [dotProduct_mulVec, mulVec_transpose]
        _ = _ := by rw [m.skew, neg_mulVec, neg_dotProduct, dotProduct_comm]
    linarith
  have hport : m.gradient x ⬝ᵥ (m.B *ᵥ u) = m.supply x u := by
    rw [supply, output, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]
  have hdamping : m.gradient x ⬝ᵥ (diagonal m.d *ᵥ m.gradient x) = m.dampingPower x := by
    simp only [dotProduct, mulVec_diagonal, dampingPower]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [field, sub_mulVec, dotProduct_add, dotProduct_sub, hskew, hport, hdamping]
  ring

/-! ### Numbering the indices: the `Port.PortHamiltonian` plant -/

variable {n p : ℕ}

omit [DecidableEq ι] in
@[powerlib_foundation] theorem reindex_mulVec (e : ι ≃ Fin n) (M : Matrix ι ι ℝ)
    (x : Fin n → ℝ) : reindex e e M *ᵥ x = (M *ᵥ (x ∘ e)) ∘ e.symm := by
  rw [reindex_apply, submatrix_mulVec_equiv, Equiv.symm_symm]

omit [Fintype ι] [DecidableEq ι] in
@[powerlib_foundation] theorem reindex_mulVec' (e : ι ≃ Fin n) (e' : κ ≃ Fin p)
    (M : Matrix ι κ ℝ) (u : Fin p → ℝ) : reindex e e' M *ᵥ u = (M *ᵥ (u ∘ e')) ∘ e.symm := by
  rw [reindex_apply, submatrix_mulVec_equiv, Equiv.symm_symm]

omit [DecidableEq ι] in
@[powerlib_foundation] theorem dotProduct_reindex_mulVec (e : ι ≃ Fin n) (M : Matrix ι ι ℝ)
    (x : Fin n → ℝ) : x ⬝ᵥ (reindex e e M *ᵥ x) = (x ∘ e) ⬝ᵥ (M *ᵥ (x ∘ e)) := by
  rw [reindex_mulVec, dotProduct_comp_equiv_symm]

omit [Fintype ι] in
@[powerlib_foundation] theorem diagonal_quadratic (d y : ι → ℝ) [Fintype ι] :
    y ⬝ᵥ (diagonal d *ᵥ y) = ∑ i, d i * y i ^ 2 := by
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The `Port.PortHamiltonian` plant of the data, with states numbered by `e` and ports by
`e'`: `J`, `R = diag d`, `Q = diag w`, `B` read on `Fin n`, `Fin p`. -/
def toPH (m : DiagonalPH ι κ) (e : ι ≃ Fin n) (e' : κ ≃ Fin p) : Port.PortHamiltonian n p where
  J := reindex e e m.J
  R := reindex e e (diagonal m.d)
  Q := reindex e e (diagonal m.w)
  B := reindex e e' m.B
  skew := by
    rw [transpose_reindex, m.skew]
    ext i j
    simp
  dissipation_symmetric := by rw [transpose_reindex, diagonal_transpose]
  dissipation_nonneg x := by
    rw [dotProduct_reindex_mulVec, diagonal_quadratic]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (m.damping_nonneg i) (sq_nonneg _)
  energy_symmetric := by rw [transpose_reindex, diagonal_transpose]
  energy_pos x hx := by
    rw [dotProduct_reindex_mulVec, diagonal_quadratic]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
    refine Finset.sum_pos' (fun i _ => mul_nonneg (m.weights_pos i).le (sq_nonneg _))
      ⟨e.symm j, Finset.mem_univ _, mul_pos (m.weights_pos _) ?_⟩
    have : (x ∘ e) (e.symm j) ≠ 0 := by simpa using hj
    positivity

omit [Fintype κ] in
@[powerlib_foundation] theorem toPH_plant (m : DiagonalPH ι κ) (e : ι ≃ Fin n)
    (e' : κ ≃ Fin p) :
    (m.toPH e e').plant = ⟨reindex e e m.stateMatrix, reindex e e' m.B,
      reindex e' e (m.Bᵀ * diagonal m.w), 0⟩ := by
  simp only [Port.PortHamiltonian.plant, toPH, stateMatrix, reindex_apply, transpose_submatrix]
  have h : m.J.submatrix e.symm e.symm - (diagonal m.d).submatrix e.symm e.symm =
      (m.J - diagonal m.d).submatrix e.symm e.symm := rfl
  rw [h, submatrix_mul_equiv, submatrix_mul_equiv]

/-- The state field of the numbered plant is the field of the data, read through the
numbering. -/
@[powerlib_foundation] theorem toPH_field (m : DiagonalPH ι κ) (e : ι ≃ Fin n) (e' : κ ≃ Fin p)
    (x : EuclideanSpace ℝ (Fin n)) (u : Fin p → ℝ) :
    WithLp.ofLp ((m.toPH e e').plant.system.field x u) =
      m.field (WithLp.ofLp x ∘ e) (u ∘ e') ∘ e.symm := by
  rw [toPH_plant, field_eq_stateMatrix]
  simp only [Linear.Plant.system, Linear.op, Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_add,
    reindex_apply, submatrix_mulVec_equiv, Equiv.symm_symm]
  rfl

/-- The port output of the numbered plant is the output of the data. -/
@[powerlib_foundation] theorem toPH_output (m : DiagonalPH ι κ) (e : ι ≃ Fin n)
    (e' : κ ≃ Fin p) (x : EuclideanSpace ℝ (Fin n)) (u : Fin p → ℝ) :
    (m.toPH e e').plant.system.output x u = m.output (WithLp.ofLp x ∘ e) ∘ e'.symm := by
  rw [toPH_plant]
  simp only [Linear.Plant.system, zero_mulVec, add_zero, reindex_apply, submatrix_mulVec_equiv,
    Equiv.symm_symm, output, ← mulVec_mulVec, diagonal_mulVec_gradient]

/-- The supplied power of the numbered plant is the supplied power of the data. -/
@[powerlib_foundation] theorem toPH_supply (m : DiagonalPH ι κ) (e : ι ≃ Fin n)
    (e' : κ ≃ Fin p) (x : EuclideanSpace ℝ (Fin n)) (u : Fin p → ℝ) :
    (m.toPH e e').plant.system.supply x u = m.supply (WithLp.ofLp x ∘ e) (u ∘ e') := by
  rw [Port.System.supply, toPH_output, dotProduct_comp_equiv_symm, supply]

omit [Fintype κ] in
/-- The stored energy `xᵀ Q x / 2` of the numbered plant is the energy of the data. -/
@[powerlib_foundation] theorem toPH_storage (m : DiagonalPH ι κ) (e : ι ≃ Fin n)
    (e' : κ ≃ Fin p) (x : EuclideanSpace ℝ (Fin n)) :
    (m.toPH e e').kyp.storage x = m.energy (WithLp.ofLp x ∘ e) := by
  simp only [Linear.KYP.storage, Port.PortHamiltonian.kyp, toPH]
  rw [dotProduct_reindex_mulVec, diagonal_quadratic, energy, Finset.sum_div]

omit [Fintype κ] in
/-- Strictly positive damping on every state gives a strictly positive dissipation matrix. -/
@[powerlib_foundation] theorem toPH_dissipation_pos (m : DiagonalPH ι κ) (e : ι ≃ Fin n)
    (e' : κ ≃ Fin p) (hd : ∀ i, 0 < m.d i) :
    ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ ((m.toPH e e').R *ᵥ x) := by
  intro x hx
  change 0 < x ⬝ᵥ (reindex e e (diagonal m.d) *ᵥ x)
  rw [dotProduct_reindex_mulVec, diagonal_quadratic]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
  refine Finset.sum_pos' (fun i _ => mul_nonneg (m.damping_nonneg i) (sq_nonneg _))
    ⟨e.symm j, Finset.mem_univ _, mul_pos (hd _) ?_⟩
  have : (x ∘ e) (e.symm j) ≠ 0 := by simpa using hj
  positivity

omit [Fintype κ] in
/-- Zero damping gives a zero dissipation matrix. -/
@[powerlib_foundation] theorem toPH_R_eq_zero (m : DiagonalPH ι κ) (e : ι ≃ Fin n)
    (e' : κ ≃ Fin p) (hd : m.d = 0) : (m.toPH e e').R = 0 := by
  change reindex e e (diagonal m.d) = 0
  rw [hd]
  ext i j
  simp

omit [Fintype κ] in
/-- Data related by a coordinate change `T`, `S = T⁻¹` (state matrix `T A S`, input `T B`,
output `C S`) give similar numbered plants. -/
@[powerlib_foundation] theorem toPH_similar (m m' : DiagonalPH ι κ) (e : ι ≃ Fin n)
    (e' : κ ≃ Fin p) {T S : Matrix ι ι ℝ} (hTS : T * S = 1) (hST : S * T = 1)
    (hA : m'.stateMatrix = T * m.stateMatrix * S) (hB : m'.B = T * m.B)
    (hC : m'.Bᵀ * diagonal m'.w = m.Bᵀ * diagonal m.w * S) :
    Linear.Similar (m.toPH e e').plant (m'.toPH e e').plant := by
  have hmul : ∀ (X : Matrix ι ι ℝ) (Y : Matrix ι κ ℝ),
      reindex e e X * reindex e e' Y = reindex e e' (X * Y) := by
    intro X Y
    simp only [reindex_apply, submatrix_mul_equiv]
  have hmul' : ∀ (X : Matrix κ ι ℝ) (Y : Matrix ι ι ℝ),
      reindex e' e X * reindex e e Y = reindex e' e (X * Y) := by
    intro X Y
    simp only [reindex_apply, submatrix_mul_equiv]
  have hsq : ∀ X Y : Matrix ι ι ℝ, reindex e e X * reindex e e Y = reindex e e (X * Y) := by
    intro X Y
    simp only [reindex_apply, submatrix_mul_equiv]
  have hone : reindex e e (1 : Matrix ι ι ℝ) = 1 := by
    simp only [reindex_apply, submatrix_one_equiv]
  refine ⟨reindex e e T, reindex e e S, by rw [hsq, hTS, hone], by rw [hsq, hST, hone], ?_⟩
  rw [toPH_plant, toPH_plant, hC, hA, hB]
  simp only [Linear.Plant.changeCoordinates, hsq, hmul, hmul']

end DiagonalPH

/-! ## Linear port-Hamiltonian plants: damping and conservation -/

section Linear

variable {n p : ℕ}

/-- In a linear port-Hamiltonian plant the energy matrix turns the state matrix into the
dissipation: `xᵀ Q A x = −(Q x)ᵀ R (Q x)`. -/
@[powerlib_foundation] theorem energy_rate (h : Port.PortHamiltonian n p) (x : Fin n → ℝ) :
    x ⬝ᵥ (h.Q *ᵥ (h.plant.A *ᵥ x)) = -((h.Q *ᵥ x) ⬝ᵥ (h.R *ᵥ (h.Q *ᵥ x))) := by
  have hsym : x ⬝ᵥ (h.Q *ᵥ (((h.J - h.R) * h.Q) *ᵥ x)) =
      (h.Q *ᵥ x) ⬝ᵥ ((h.J - h.R) *ᵥ (h.Q *ᵥ x)) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec]
    congr 1
    conv_lhs => rw [← h.energy_symmetric]
    rw [Matrix.vecMul_transpose]
  have hJ : (h.Q *ᵥ x) ⬝ᵥ (h.J *ᵥ (h.Q *ᵥ x)) = 0 := by
    set z := h.Q *ᵥ x
    have h1 : z ⬝ᵥ (h.J *ᵥ z) = -(z ⬝ᵥ (h.J *ᵥ z)) := by
      calc z ⬝ᵥ (h.J *ᵥ z) = (h.Jᵀ *ᵥ z) ⬝ᵥ z := by rw [dotProduct_mulVec, mulVec_transpose]
        _ = -(z ⬝ᵥ (h.J *ᵥ z)) := by rw [h.skew, neg_mulVec, neg_dotProduct, dotProduct_comm]
    linarith
  change x ⬝ᵥ (h.Q *ᵥ (((h.J - h.R) * h.Q) *ᵥ x)) = _
  rw [hsym, sub_mulVec, dotProduct_sub, hJ, zero_sub]

/-- Strictly positive dissipation makes the state matrix of a linear port-Hamiltonian plant
Hurwitz. -/
@[powerlib_foundation] theorem isHurwitz_of_dissipation_pos (h : Port.PortHamiltonian n p)
    (hR : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (h.R *ᵥ x)) : IsHurwitz h.plant.A := by
  refine Criteria.isHurwitz_of_lyapunov h.energy_symmetric h.energy_pos fun x hx => ?_
  rw [energy_rate]
  have hQx : h.Q *ᵥ x ≠ 0 := by
    intro h0
    have := h.energy_pos x hx
    rw [h0, dotProduct_zero] at this
    exact lt_irrefl 0 this
  linarith [hR _ hQx]

/-- Without dissipation the stored energy is conserved: `Aᵀ Q + Q A = 0`. -/
@[powerlib_foundation] theorem lossless_lyapunov (h : Port.PortHamiltonian n p) (hR : h.R = 0) :
    h.plant.Aᵀ * h.Q + h.Q * h.plant.A = 0 := by
  simp only [Port.PortHamiltonian.plant, hR, sub_zero, Matrix.transpose_mul, h.skew,
    h.energy_symmetric]
  noncomm_ring

/-- The stored energy `xᵀ Q x / 2` as an inner product. -/
@[powerlib_foundation] theorem storage_eq_inner (h : Port.PortHamiltonian n p) :
    h.kyp.storage = fun x => inner ℝ x (Linear.op h.Q x) / 2 := by
  funext x
  rw [Linear.inner_op]
  rfl

@[powerlib_foundation] theorem storage_contDiff (h : Port.PortHamiltonian n p) :
    ContDiff ℝ 1 h.kyp.storage := by
  rw [storage_eq_inner]
  exact (contDiff_id.inner ℝ (Linear.op h.Q).contDiff).div_const 2

/-- The derivative of the stored energy in the direction `v` is `xᵀ Q v`. -/
@[powerlib_foundation] theorem fderiv_storage_apply (h : Port.PortHamiltonian n p)
    (x v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ h.kyp.storage x v = WithLp.ofLp x ⬝ᵥ (h.Q *ᵥ WithLp.ofLp v) := by
  have hd : HasFDerivAt h.kyp.storage
      ((1 / 2 : ℝ) • (fderivInnerCLM ℝ (x, Linear.op h.Q x)).comp
        ((ContinuousLinearMap.id ℝ _).prod (Linear.op h.Q))) x := by
    rw [storage_eq_inner]
    have := ((hasFDerivAt_id x).inner ℝ (Linear.op h.Q).hasFDerivAt).const_mul (1 / 2 : ℝ)
    simpa only [div_eq_inv_mul, one_div, id, mul_one] using this
  rw [hd.fderiv]
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, ContinuousLinearMap.id_apply,
    Linear.inner_op, smul_eq_mul]
  have hsym : WithLp.ofLp v ⬝ᵥ (h.Q *ᵥ WithLp.ofLp x) =
      WithLp.ofLp x ⬝ᵥ (h.Q *ᵥ WithLp.ofLp v) := by
    rw [Matrix.dotProduct_mulVec, dotProduct_comm]
    congr 1
    conv_lhs => rw [← h.energy_symmetric]
    rw [Matrix.vecMul_transpose]
  rw [hsym]
  ring

/-- Power balance of a linear port-Hamiltonian plant: in the direction of the field, the stored
energy changes at the supplied power minus the dissipated power `(Q x)ᵀ R (Q x)`. -/
@[powerlib_foundation] theorem fderiv_storage_field (h : Port.PortHamiltonian n p)
    (x : EuclideanSpace ℝ (Fin n)) (u : Fin p → ℝ) :
    fderiv ℝ h.kyp.storage x (h.plant.system.field x u) =
      h.plant.system.supply x u -
        (h.Q *ᵥ WithLp.ofLp x) ⬝ᵥ (h.R *ᵥ (h.Q *ᵥ WithLp.ofLp x)) := by
  rw [fderiv_storage_apply]
  have hf : WithLp.ofLp (h.plant.system.field x u) =
      h.plant.A *ᵥ WithLp.ofLp x + h.B *ᵥ u := by
    simp [Linear.Plant.system, Port.PortHamiltonian.plant, Linear.op,
      Matrix.ofLp_toEuclideanCLM, Matrix.sub_mul, Matrix.sub_mulVec]
  have hs : h.plant.system.supply x u = WithLp.ofLp x ⬝ᵥ (h.Q *ᵥ (h.B *ᵥ u)) := by
    simp only [Port.System.supply, Linear.Plant.system, Port.PortHamiltonian.plant,
      zero_mulVec, add_zero]
    have hsym : WithLp.ofLp x ⬝ᵥ (h.Q *ᵥ (h.B *ᵥ u)) =
        (h.Q *ᵥ WithLp.ofLp x) ⬝ᵥ (h.B *ᵥ u) := by
      rw [dotProduct_mulVec]
      congr 1
      conv_lhs => rw [← h.energy_symmetric]
      rw [vecMul_transpose]
    rw [hsym, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  rw [hf, mulVec_add, dotProduct_add, energy_rate, hs]
  ring

/-- Strictly positive dissipation gives a quadratic-decay certificate whose energy is the stored
energy itself. -/
@[powerlib_foundation] theorem exists_quadraticDecay (h : Port.PortHamiltonian n p)
    (hR : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (h.R *ᵥ x)) :
    Nonempty (Flow.QuadraticDecay h.plant.system.zeroInput h.kyp.storage 0) := by
  have hpos : ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 → 0 < h.kyp.storage x := fun x hx =>
    div_pos (h.energy_pos _ (by simpa using hx)) two_pos
  have hhom : ∀ (a : ℝ) (x : EuclideanSpace ℝ (Fin n)),
      h.kyp.storage (a • x) = a ^ 2 * h.kyp.storage x := fun a x => by
    simp only [Linear.KYP.storage, WithLp.ofLp_smul, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    ring
  obtain ⟨a, ha, b, hab, hb⟩ := Flow.quadratic_bounds h.kyp.storage
    (storage_contDiff h).continuous hhom hpos
  let W : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    (h.Q *ᵥ WithLp.ofLp x) ⬝ᵥ (h.R *ᵥ (h.Q *ᵥ WithLp.ofLp x))
  have hWc : Continuous W := by
    simp only [W]
    fun_prop
  have hWh : ∀ (a : ℝ) (x : EuclideanSpace ℝ (Fin n)), W (a • x) = a ^ 2 * W x := fun a x => by
    simp only [W, WithLp.ofLp_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
      smul_eq_mul]
    ring
  have hWp : ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 → 0 < W x := fun x hx => by
    apply hR
    intro h0
    have := h.energy_pos (WithLp.ofLp x) (by simpa using hx)
    rw [h0, dotProduct_zero] at this
    exact lt_irrefl 0 this
  obtain ⟨α, hα, β, -, hW⟩ := Flow.quadratic_bounds W hWc hWh hWp
  have hb0 : 0 < b := ha.trans_le hab
  refine ⟨⟨a, b, α / b, ha, hb0, div_pos hα hb0, storage_contDiff h, ?_, ?_, ?_, ?_⟩⟩
  · simp [Linear.Plant.system, Port.System.zeroInput]
  · intro x
    simpa using (hb x).1
  · intro x
    simpa using (hb x).2
  · intro x
    have hz : WithLp.ofLp (h.plant.system.zeroInput x) = h.plant.A *ᵥ WithLp.ofLp x := by
      simp [Linear.Plant.system, Port.System.zeroInput]
    rw [fderiv_storage_apply, hz, energy_rate]
    have h1 := (hW x).1
    have h2 := (hb x).2
    change -W x ≤ -(α / b) * h.kyp.storage x
    have h3 : α / b * h.kyp.storage x ≤ α * ‖x‖ ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hb0]
      nlinarith [sq_nonneg ‖x‖]
    linarith

/-- Strictly damped linear port-Hamiltonian plants satisfy every attractive sentence and sampled
contraction. -/
@[powerlib_domain] theorem mem_den_of_dissipation_pos (h : Port.PortHamiltonian n p)
    (hR : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (h.R *ᵥ x)) {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (h ∈ Port.PortHamiltonian.family.den (.flow P)) := by
  unfold powerlib.TMIO.Statement
  rw [Port.PortHamiltonian.family_isLinear.den_hurwitz hP]
  exact isHurwitz_of_dissipation_pos h hR

/-- Strict damping: the zero-input plant is globally exponentially stable. -/
@[powerlib_domain] theorem mem_den_globallyExponentiallyStable_of_dissipation_pos
    (h : Port.PortHamiltonian n p) (hR : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (h.R *ᵥ x)) :
    connection% (h ∈ Port.PortHamiltonian.family.den (.flow .globallyExponentiallyStable)) :=
  mem_den_of_dissipation_pos h hR (Or.inl trivial)

/-- Without dissipation the zero-input plant conserves its positive definite stored energy. -/
@[powerlib_domain] theorem mem_den_conservative_of_lossless (h : Port.PortHamiltonian n p)
    (hR : h.R = 0) :
    connection% (h ∈ Port.PortHamiltonian.family.den (.flow .conservative)) :=
  Port.PortHamiltonian.family_isLinear.mem_den_conservative h.energy_symmetric h.energy_pos
    (lossless_lyapunov h hR)

/-- A strictly damped plant with a state conserves no energy. -/
@[powerlib_domain] theorem not_mem_den_conservative_of_dissipation_pos
    (h : Port.PortHamiltonian n p) (hn : 0 < n)
    (hR : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (h.R *ᵥ x)) :
    connection% (h ∉ Port.PortHamiltonian.family.den (.flow .conservative)) := fun hc =>
  Port.PortHamiltonian.family_isLinear.not_isHurwitz_of_mem_den_conservative hn hc
    (isHurwitz_of_dissipation_pos h hR)

/-- Similar plants of port-Hamiltonian models satisfy the same sentences. -/
@[powerlib_domain] theorem mem_den_iff_of_similar {h h' : Port.PortHamiltonian n p}
    (hs : Linear.Similar h.plant h'.plant) :
    connection% (∀ s : Sentence, h' ∈ Port.PortHamiltonian.family.den s ↔
      h ∈ Port.PortHamiltonian.family.den s) := by
  unfold powerlib.TMIO.Statement
  intro s
  simp only [Family.mem_den]
  exact hs.sentence_iff s

end Linear

/-! ## Power-preserving interconnection -/

section Interconnection

variable {ι₁ ι₂ κ₁ κ₂ κ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
  [Fintype κ₁] [Fintype κ₂] [Fintype κ]

/-- The power-preserving interconnection (1.9) of two diagonal pH models, written as one diagonal
pH model (1.10). -/
def interconnect (m₁ : DiagonalPH ι₁ κ₁) (m₂ : DiagonalPH ι₂ κ₂)
    (Mc : Matrix κ₂ κ₁ ℝ) (g₁ : Matrix κ₁ κ ℝ) (g₂ : Matrix κ₂ κ ℝ) :
    DiagonalPH (ι₁ ⊕ ι₂) κ where
  J := fromBlocks m₁.J (-(m₁.B * Mcᵀ * m₂.Bᵀ)) (m₂.B * Mc * m₁.Bᵀ) m₂.J
  d := Sum.elim m₁.d m₂.d
  w := Sum.elim m₁.w m₂.w
  B := fromRows (m₁.B * g₁) (m₂.B * g₂)
  skew := by
    rw [fromBlocks_transpose, fromBlocks_neg, m₁.skew, m₂.skew]
    congr 1 <;> simp [transpose_mul, Matrix.mul_assoc]
  damping_nonneg := by
    rintro (i | i)
    · exact m₁.damping_nonneg i
    · exact m₂.damping_nonneg i
  weights_pos := by
    rintro (i | i)
    · exact m₁.weights_pos i
    · exact m₂.weights_pos i

variable (m₁ : DiagonalPH ι₁ κ₁) (m₂ : DiagonalPH ι₂ κ₂)
  (Mc : Matrix κ₂ κ₁ ℝ) (g₁ : Matrix κ₁ κ ℝ) (g₂ : Matrix κ₂ κ ℝ)

omit [DecidableEq ι₁] [DecidableEq ι₂] [Fintype ι₁] [Fintype ι₂] [Fintype κ] in
@[powerlib_foundation] theorem interconnect_gradient (x : ι₁ ⊕ ι₂ → ℝ) :
    (interconnect m₁ m₂ Mc g₁ g₂).gradient x =
      Sum.elim (m₁.gradient (x ∘ Sum.inl)) (m₂.gradient (x ∘ Sum.inr)) := by
  ext (i | i) <;> rfl

omit [Fintype ι₁] [Fintype ι₂] [Fintype κ] in
@[powerlib_foundation] theorem interconnect_stateMatrix_sub :
    (interconnect m₁ m₂ Mc g₁ g₂).J - diagonal (interconnect m₁ m₂ Mc g₁ g₂).d =
      fromBlocks (m₁.J - diagonal m₁.d) (-(m₁.B * Mcᵀ * m₂.Bᵀ)) (m₂.B * Mc * m₁.Bᵀ)
        (m₂.J - diagonal m₂.d) := by
  ext (i | i) (j | j) <;> simp [interconnect, diagonal_apply]

/-- (1.10) restricted to the first block is the first subsystem driven by
`u₁ = −Mᵀ y₂ + g₁ u`. -/
@[powerlib_foundation] theorem interconnect_field_inl (x : ι₁ ⊕ ι₂ → ℝ) (u : κ → ℝ) :
    (interconnect m₁ m₂ Mc g₁ g₂).field x u ∘ Sum.inl =
      m₁.field (x ∘ Sum.inl) (-(Mcᵀ *ᵥ m₂.output (x ∘ Sum.inr)) + g₁ *ᵥ u) := by
  have hB : (interconnect m₁ m₂ Mc g₁ g₂).B = fromRows (m₁.B * g₁) (m₂.B * g₂) := rfl
  rw [DiagonalPH.field, interconnect_stateMatrix_sub, interconnect_gradient, hB,
    fromBlocks_mulVec, fromRows_mulVec]
  simp only [Function.comp_def, Pi.add_apply, Sum.elim_inl, Sum.elim_inr, DiagonalPH.field,
    DiagonalPH.output]
  ext i
  simp only [Pi.add_apply, neg_mulVec, mulVec_add, mulVec_neg, ← mulVec_mulVec]
  abel

/-- (1.10) restricted to the second block is the second subsystem driven by
`u₂ = M y₁ + g₂ u`. -/
@[powerlib_foundation] theorem interconnect_field_inr (x : ι₁ ⊕ ι₂ → ℝ) (u : κ → ℝ) :
    (interconnect m₁ m₂ Mc g₁ g₂).field x u ∘ Sum.inr =
      m₂.field (x ∘ Sum.inr) (Mc *ᵥ m₁.output (x ∘ Sum.inl) + g₂ *ᵥ u) := by
  have hB : (interconnect m₁ m₂ Mc g₁ g₂).B = fromRows (m₁.B * g₁) (m₂.B * g₂) := rfl
  rw [DiagonalPH.field, interconnect_stateMatrix_sub, interconnect_gradient, hB,
    fromBlocks_mulVec, fromRows_mulVec]
  simp only [Function.comp_def, Pi.add_apply, Sum.elim_inl, Sum.elim_inr, DiagonalPH.field,
    DiagonalPH.output]
  ext i
  simp only [Pi.add_apply, mulVec_add, ← mulVec_mulVec]
  abel

omit [DecidableEq ι₁] [DecidableEq ι₂] [Fintype κ] in
/-- `H^tot = H₁ + H₂`. -/
@[powerlib_foundation] theorem interconnect_energy (x : ι₁ ⊕ ι₂ → ℝ) :
    (interconnect m₁ m₂ Mc g₁ g₂).energy x =
      m₁.energy (x ∘ Sum.inl) + m₂.energy (x ∘ Sum.inr) := by
  simp [DiagonalPH.energy, interconnect, Fintype.sum_sum_type]

omit [DecidableEq ι₁] [DecidableEq ι₂] [Fintype κ] in
/-- The external output is `g₁ᵀ y₁ + g₂ᵀ y₂`. -/
@[powerlib_foundation] theorem interconnect_output (x : ι₁ ⊕ ι₂ → ℝ) :
    (interconnect m₁ m₂ Mc g₁ g₂).output x =
      g₁ᵀ *ᵥ m₁.output (x ∘ Sum.inl) + g₂ᵀ *ᵥ m₂.output (x ∘ Sum.inr) := by
  have hB : (interconnect m₁ m₂ Mc g₁ g₂).B = fromRows (m₁.B * g₁) (m₂.B * g₂) := rfl
  rw [DiagonalPH.output, hB, interconnect_gradient, transpose_fromRows, fromCols_mulVec]
  simp [DiagonalPH.output, transpose_mul, mulVec_mulVec, Function.comp_def]

variable {n p : ℕ}

/-! ### Trajectories of the composite (implementation evidence) -/

/-- A continuous linear map intertwining two port fields carries solution segments. Generic: for
any two port systems. -/
@[powerlib_foundation] theorem isTrajectoryOn_map {n' p' : ℕ} (s : Port.System n p) (s' : Port.System n' p')
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n'))
    (v : EuclideanSpace ℝ (Fin n) → (Fin p → ℝ) → (Fin p' → ℝ))
    (hL : ∀ y u, L (s.field y u) = s'.field (L y) (v y u)) {u : ℝ → Fin p → ℝ}
    {x : ℝ → EuclideanSpace ℝ (Fin n)} {t₀ t₁ : ℝ} (hx : s.IsTrajectoryOn u x t₀ t₁) :
    s'.IsTrajectoryOn (fun t => v (x t) (u t)) (fun t => L (x t)) t₀ t₁ := by
  intro t ht
  have h := L.hasFDerivAt.comp_hasDerivWithinAt t (hx t ht)
  simpa [Function.comp_def, hL] using h

/-- Reading a numbered state through an index map. -/
private def restrict {α β : Type*} {n' : ℕ} (f : α → β) (e : β ≃ Fin n) (e₁ : α ≃ Fin n') :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n') :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n' => ℝ)).symm.toContinuousLinearMap.comp
    ((LinearMap.funLeft ℝ ℝ (e.symm.symm ∘ f ∘ e₁.symm)).toContinuousLinearMap.comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).toContinuousLinearMap)

private theorem ofLp_restrict {α β : Type*} {n' : ℕ} (f : α → β) (e : β ≃ Fin n)
    (e₁ : α ≃ Fin n') (x : EuclideanSpace ℝ (Fin n)) :
    WithLp.ofLp (restrict f e e₁ x) = (WithLp.ofLp x ∘ e ∘ f) ∘ e₁.symm := rfl

/-- Formerly the public `interconnect_trajectory_inl`: solutions of the composite project to
solutions of the first subsystem under the coupling input `u₁ = −Mᵀ y₂ + g₁ u`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem interconnect_trajectory_inl {n₁ p₁ : ℕ} (e : ι₁ ⊕ ι₂ ≃ Fin n) (e' : κ ≃ Fin p)
    (e₁ : ι₁ ≃ Fin n₁) (e₁' : κ₁ ≃ Fin p₁) {u : ℝ → Fin p → ℝ}
    {x : ℝ → EuclideanSpace ℝ (Fin n)} {t₀ t₁ : ℝ}
    (hx : ((interconnect m₁ m₂ Mc g₁ g₂).toPH e e').plant.system.IsTrajectoryOn u x t₀ t₁) :
    (m₁.toPH e₁ e₁').plant.system.IsTrajectoryOn
      (fun t => (-(Mcᵀ *ᵥ m₂.output (WithLp.ofLp (x t) ∘ e ∘ Sum.inr)) +
        g₁ *ᵥ (u t ∘ e')) ∘ e₁'.symm)
      (fun t => restrict Sum.inl e e₁ (x t)) t₀ t₁ := by
  refine isTrajectoryOn_map _ _ (restrict Sum.inl e e₁)
    (fun y w => (-(Mcᵀ *ᵥ m₂.output (WithLp.ofLp y ∘ e ∘ Sum.inr)) + g₁ *ᵥ (w ∘ e')) ∘ e₁'.symm)
    (fun y w => ?_) hx
  apply WithLp.ofLp_injective
  funext i
  have h := congrFun (interconnect_field_inl m₁ m₂ Mc g₁ g₂ (WithLp.ofLp y ∘ e) (w ∘ e'))
    (e₁.symm i)
  rw [ofLp_restrict, DiagonalPH.toPH_field, DiagonalPH.toPH_field, ofLp_restrict]
  simp only [Function.comp_apply, Equiv.symm_apply_apply] at h ⊢
  rw [h]
  congr 1 <;> funext j <;> simp [Function.comp_assoc]

/-- Formerly the public `interconnect_trajectory_inr`: solutions of the composite project to
solutions of the second subsystem under the coupling input `u₂ = M y₁ + g₂ u`.
Implementation evidence: trajectory-level result outside the sentence language (Rules §3a). -/
private theorem interconnect_trajectory_inr {n₂ p₂ : ℕ} (e : ι₁ ⊕ ι₂ ≃ Fin n) (e' : κ ≃ Fin p)
    (e₂ : ι₂ ≃ Fin n₂) (e₂' : κ₂ ≃ Fin p₂) {u : ℝ → Fin p → ℝ}
    {x : ℝ → EuclideanSpace ℝ (Fin n)} {t₀ t₁ : ℝ}
    (hx : ((interconnect m₁ m₂ Mc g₁ g₂).toPH e e').plant.system.IsTrajectoryOn u x t₀ t₁) :
    (m₂.toPH e₂ e₂').plant.system.IsTrajectoryOn
      (fun t => (Mc *ᵥ m₁.output (WithLp.ofLp (x t) ∘ e ∘ Sum.inl) +
        g₂ *ᵥ (u t ∘ e')) ∘ e₂'.symm)
      (fun t => restrict Sum.inr e e₂ (x t)) t₀ t₁ := by
  refine isTrajectoryOn_map _ _ (restrict Sum.inr e e₂)
    (fun y w => (Mc *ᵥ m₁.output (WithLp.ofLp y ∘ e ∘ Sum.inl) + g₂ *ᵥ (w ∘ e')) ∘ e₂'.symm)
    (fun y w => ?_) hx
  apply WithLp.ofLp_injective
  funext i
  have h := congrFun (interconnect_field_inr m₁ m₂ Mc g₁ g₂ (WithLp.ofLp y ∘ e) (w ∘ e'))
    (e₂.symm i)
  rw [ofLp_restrict, DiagonalPH.toPH_field, DiagonalPH.toPH_field, ofLp_restrict]
  simp only [Function.comp_apply, Equiv.symm_apply_apply] at h ⊢
  rw [h]
  congr 1 <;> funext j <;> simp [Function.comp_assoc]

end Interconnection

/-- Compositionality (T-ph §1.5), for numbered components (connection statements quantify only
over values, so the index types are `Fin`): every numbering of the interconnected model is
passive, with no new Lyapunov analysis; its stored energy is `H₁ + H₂` (`toPH_storage`, `interconnect_energy`). -/
@[powerlib_domain] theorem interconnect_mem_den_passive {a₁ a₂ b₁ b₂ b n p : ℕ}
    (m₁ : DiagonalPH (Fin a₁) (Fin b₁)) (m₂ : DiagonalPH (Fin a₂) (Fin b₂))
    (Mc : Matrix (Fin b₂) (Fin b₁) ℝ) (g₁ : Matrix (Fin b₁) (Fin b) ℝ)
    (g₂ : Matrix (Fin b₂) (Fin b) ℝ) (e : Fin a₁ ⊕ Fin a₂ ≃ Fin n) (e' : Fin b ≃ Fin p) :
    connection% ((interconnect m₁ m₂ Mc g₁ g₂).toPH e e' ∈
      Port.PortHamiltonian.family.den .passive) :=
  Port.PortHamiltonian.mem_den_passive _

/-- The zero-input interconnection is Lyapunov stable. -/
@[powerlib_domain] theorem interconnect_mem_den_lyapunovStable {a₁ a₂ b₁ b₂ b n p : ℕ}
    (m₁ : DiagonalPH (Fin a₁) (Fin b₁)) (m₂ : DiagonalPH (Fin a₂) (Fin b₂))
    (Mc : Matrix (Fin b₂) (Fin b₁) ℝ) (g₁ : Matrix (Fin b₁) (Fin b) ℝ)
    (g₂ : Matrix (Fin b₂) (Fin b) ℝ) (e : Fin a₁ ⊕ Fin a₂ ≃ Fin n) (e' : Fin b ≃ Fin p) :
    connection% ((interconnect m₁ m₂ Mc g₁ g₂).toPH e e' ∈
      Port.PortHamiltonian.family.den (.flow .lyapunovStable)) :=
  Port.PortHamiltonian.mem_den_lyapunovStable _

/-! ## Block structure of `J^tot` and `R^tot` -/

section Blocks

variable {ι ι₁ ι₂ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι₁] [Fintype ι₂]

/-- Block-diagonal dissipation of independent components is positive semidefinite. -/
@[powerlib_foundation] theorem blockDiag_posSemidef {R₁ : Matrix ι₁ ι₁ ℝ} {R₂ : Matrix ι₂ ι₂ ℝ}
    (h₁ : R₁.PosSemidef) (h₂ : R₂.PosSemidef) : (fromBlocks R₁ 0 0 R₂).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec] at h₁ h₂ ⊢
  refine ⟨h₁.1.fromBlocks (by simp) h₂.1, fun x => ?_⟩
  rw [fromBlocks_mulVec]
  simp only [zero_mulVec, add_zero, zero_add, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Pi.star_apply]
  have a := h₁.2 (x ∘ Sum.inl)
  have b := h₂.2 (x ∘ Sum.inr)
  simp only [dotProduct, Pi.star_apply, Function.comp_apply] at a b
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- §1.5.2: adding skew-symmetric interconnection blocks keeps `J` skew. -/
@[powerlib_foundation] theorem skew_add {J K : Matrix ι ι ℝ} (hJ : Jᵀ = -J) (hK : Kᵀ = -K) :
    (J + K)ᵀ = -(J + K) := by
  rw [transpose_add, hJ, hK, neg_add]

/-- An elementary interconnection pair `a (eᵢ eⱼᵀ − eⱼ eᵢᵀ)` is skew-symmetric. -/
def skewPair (i j : ι) (a : ℝ) : Matrix ι ι ℝ :=
  a • (single i j 1 - single j i 1)

omit [Fintype ι] in
@[powerlib_foundation] theorem skewPair_skew (i j : ι) (a : ℝ) :
    (skewPair i j a)ᵀ = -skewPair i j a := by
  simp [skewPair, transpose_sub, transpose_single, smul_sub, neg_sub]

omit [Fintype ι] in
/-- §1.5.2 recursion: any finite sum of elementary pairs added to a skew `J` stays skew. -/
@[powerlib_foundation] theorem skew_add_sum_skewPair {J : Matrix ι ι ℝ} (hJ : Jᵀ = -J)
    (s : Finset (ι × ι × ℝ)) :
    (J + ∑ p ∈ s, skewPair p.1 p.2.1 p.2.2)ᵀ = -(J + ∑ p ∈ s, skewPair p.1 p.2.1 p.2.2) := by
  apply skew_add hJ
  rw [transpose_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun p _ => skewPair_skew _ _ _

omit [Fintype ι] in
/-- §1.7: a constant-impedance load adds a nonnegative diagonal term to `R`, keeping `R ⪰ 0`. -/
@[powerlib_foundation] theorem posSemidef_add_diagonal {R : Matrix ι ι ℝ} (hR : R.PosSemidef)
    {G : ι → ℝ} (hG : ∀ i, 0 ≤ G i) : (R + diagonal G).PosSemidef :=
  hR.add (PosSemidef.diagonal hG)

end Blocks

/-! ## Strictly damped diagonal port-Hamiltonian models -/

section Strict

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

@[powerlib_foundation] theorem exists_pos_lower {ι : Type*} [Finite ι] (f : ι → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ c > 0, ∀ i, c ≤ f i := by
  rcases isEmpty_or_nonempty ι with h | h
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min f
    exact ⟨f i₀, hf i₀, hi₀⟩

omit [DecidableEq ι] [Fintype κ] in
@[powerlib_foundation] theorem energy_hasFDerivAt (m : DiagonalPH ι κ) (x : ι → ℝ) :
    HasFDerivAt m.energy
      (∑ i, (m.w i * x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i) x := by
  have h : ∀ i ∈ (Finset.univ : Finset ι), HasFDerivAt (fun y : ι → ℝ => m.w i * y i ^ 2 / 2)
      ((m.w i * x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i) x := by
    intro i _
    have hp := ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : ι => ℝ) i x).pow 2).const_mul
      (m.w i / 2)
    convert hp using 1
    · funext y; ring
    · ext v
      simp
      ring
  exact HasFDerivAt.fun_sum h

omit [DecidableEq ι] [Fintype κ] in
@[powerlib_foundation] theorem fderiv_energy_apply (m : DiagonalPH ι κ) (x v : ι → ℝ) :
    fderiv ℝ m.energy x v = m.gradient x ⬝ᵥ v := by
  rw [(energy_hasFDerivAt m x).fderiv]
  simp [dotProduct, DiagonalPH.gradient]

omit [DecidableEq ι] [Fintype κ] in
@[powerlib_foundation] theorem energy_contDiff (m : DiagonalPH ι κ) :
    ContDiff ℝ 1 m.energy := by
  unfold DiagonalPH.energy
  apply ContDiff.sum
  intro i _
  exact ((contDiff_const.mul ((contDiff_apply ℝ ℝ i).pow 2)).div_const 2)

@[powerlib_foundation] theorem zeroInput_contDiff (m : DiagonalPH ι κ) :
    ContDiff ℝ 1 (fun x => m.field x 0) := by
  have h : (fun x => m.field x 0) = fun x => m.stateMatrix *ᵥ x := by
    funext x
    rw [DiagonalPH.field_eq_stateMatrix, mulVec_zero, add_zero]
  rw [h]
  exact (Matrix.mulVecLin m.stateMatrix).toContinuousLinearMap.contDiff

/-- A diagonal port-Hamiltonian model whose every state is damped is globally exponentially
stable with zero input, in every numbering: equilibrium, global existence, and a uniform
exponential bound on every solution segment. -/
@[powerlib_domain] theorem toPH_mem_den_globallyExponentiallyStable {a b n p : ℕ}
    (m : DiagonalPH (Fin a) (Fin b)) (e : Fin a ≃ Fin n) (e' : Fin b ≃ Fin p)
    (hd : ∀ i, 0 < m.d i) :
    connection% (m.toPH e e' ∈
      Port.PortHamiltonian.family.den (.flow .globallyExponentiallyStable)) :=
  mem_den_globallyExponentiallyStable_of_dissipation_pos _ (m.toPH_dissipation_pos e e' hd)

end Strict

end powerlib.PH
