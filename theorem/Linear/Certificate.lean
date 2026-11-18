import theorem.Linear.Stability
import theorem.Flow.Certificate
import theorem.Criteria.Lyapunov

/-! # Lyapunov certificates

A certificate is the evidence a synthesizer returns for a state matrix `A`: a symmetric matrix
`P`, positive on every nonzero state, solving `Aᵀ P + P A = -1`. It is proof-relevant data,
indexed by the exact matrix it was produced for. It introduces no meaning of its own: its energy
`⟪x - e, P (x - e)⟫` is a quadratic-decay certificate of the affine linear field
(`Certificate.toQuadraticDecay`), so what it proves is what the generic certificate theory of
`Flow` proves. A certificate exists exactly when `A` is Hurwitz. Families supply synthesizers that
construct certificates; they do not restate what a certificate proves.

Scope.
* Generic: an arbitrary real square matrix `A` and its affine linear field centred at any point;
  quadratic energies only. No model.

Source: the quadratic-decay certificates of `theorem/Flow/Certificate.lean`; LeanForControl's
continuous Lyapunov equation (`IsHurwitz.exists_posDef_unique_solution_continuous_lyapunov`) for
the converse.

Results.
* `Certificate` (`P`, `symmetric`, `positive`, `lyapunov`); `quadratic_sym`, `quadratic_lyapunov`.
* `Certificate.isHurwitz` (the Lyapunov-inequality criterion `Criteria.re_neg_of_lyapunov` of
  `theorem/Criteria/Lyapunov.lean`, the dissipation being `-wᵀw/2`) and
  `nonempty_certificate_iff` (a certificate exists exactly when `A` is Hurwitz).
* The energy: `inner_op`, `Certificate.energy`, `Certificate.hasFDerivAt_energy`,
  `Certificate.lie_energy_matrix`, `Certificate.lie_energy`, `Certificate.energy_contDiff`,
  `Certificate.exists_energy_bounds`; `Certificate.toQuadraticDecay`, and `Certificate.holds`
  (every attractive sentence at every centre).
* The quadratic energy `quadraticEnergy P` (`xᵀ P x / 2`, the stored energy of KYP certificates
  and pH plants): `contDiff_quadraticEnergy`, `fderiv_quadraticEnergy_apply` (for symmetric `P`
  its derivative in the direction `v` is `xᵀ P v`), `quadraticDecay_of_lyapunov` (a symmetric
  positive definite `P` with `xᵀ P A x < 0` off the origin is a quadratic-decay certificate of
  the linear field).
* Conserved quadratic energies: `dotProduct_hasDerivWithinAt`, `quadratic_conserved` (a symmetric
  `P` with `Aᵀ P + P A = 0` is constant along every solution segment), `conservative_of_quadratic`
  (with `P` positive definite the linear field is conservative).
-/

noncomputable section

namespace powerlib.Linear

open Matrix LinearSystems
open scoped RealInnerProductSpace

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- A quadratic Lyapunov certificate for the state matrix `A`. -/
structure Certificate (A : Matrix (Fin n) (Fin n) ℝ) where
  /-- The quadratic form. -/
  P : Matrix (Fin n) (Fin n) ℝ
  symmetric : Pᵀ = P
  positive : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (P *ᵥ x)
  lyapunov : Aᵀ * P + P * A = -1

attribute [powerlib_foundation]
  Certificate.symmetric Certificate.positive Certificate.lyapunov

/-- For a symmetric `P`, the quadratic form of `Aᵀ P + P A` is twice that of `P A`. -/
@[tmio T, powerlib_foundation] theorem quadratic_sym {A P : Matrix (Fin n) (Fin n) ℝ} (hP : Pᵀ = P)
    (z : Fin n → ℝ) : z ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ z) = 2 * (z ⬝ᵥ (P *ᵥ (A *ᵥ z))) := by
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, dotProduct_add]
  have h1 : z ⬝ᵥ (Aᵀ *ᵥ (P *ᵥ z)) = (A *ᵥ z) ⬝ᵥ (P *ᵥ z) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have h2 : z ⬝ᵥ (P *ᵥ (A *ᵥ z)) = (P *ᵥ z) ⬝ᵥ (A *ᵥ z) := by
    rw [Matrix.dotProduct_mulVec]
    congr 1
    conv_lhs => rw [← hP]
    rw [Matrix.vecMul_transpose]
  rw [h1, h2, dotProduct_comm (A *ᵥ z)]
  ring

@[tmio T, powerlib_foundation] theorem quadratic_lyapunov {A P : Matrix (Fin n) (Fin n) ℝ}
    (hP : Pᵀ = P) (hL : Aᵀ * P + P * A = -1) (z : Fin n → ℝ) :
    2 * (z ⬝ᵥ (P *ᵥ (A *ᵥ z))) = -(z ⬝ᵥ z) := by
  rw [← quadratic_sym hP, hL, Matrix.neg_mulVec, Matrix.one_mulVec, dotProduct_neg]

/-- A certificate proves the matrix Hurwitz. -/
@[tmio T, powerlib_foundation, aesop safe forward]
theorem Certificate.isHurwitz {A : Matrix (Fin n) (Fin n) ℝ}
    (c : Certificate A) : IsHurwitz A := by
  intro μ v hv heig
  have hdiss : ∀ w : Fin n → ℝ, w ≠ 0 → w ⬝ᵥ (c.P *ᵥ (A *ᵥ w)) < 0 := fun w hw => by
    have hw2 : 0 < w ⬝ᵥ w := lt_of_le_of_ne
      (Finset.sum_nonneg fun j _ => mul_self_nonneg (w j))
      (Ne.symm (mt dotProduct_self_eq_zero.mp hw))
    linarith [quadratic_lyapunov c.symmetric c.lyapunov w]
  simpa using Criteria.re_neg_of_lyapunov c.symmetric c.positive hdiss hv heig

/-- A certificate exists exactly when the matrix is Hurwitz (LeanForControl's Lyapunov
equation for the converse). -/
@[tmio T, powerlib_foundation] theorem nonempty_certificate_iff (A : Matrix (Fin n) (Fin n) ℝ) :
    Nonempty (Certificate A) ↔ IsHurwitz A := by
  refine ⟨fun ⟨c⟩ => c.isHurwitz, fun hA => ?_⟩
  obtain ⟨P, hP, hL, -⟩ := hA.exists_posDef_unique_solution_continuous_lyapunov 1 PosDef.one
  refine ⟨⟨P, ?_, fun x hx => ?_, ?_⟩⟩
  · simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hP.isHermitian.eq
  · simpa using hP.dotProduct_mulVec_pos hx
  · have h : P * A + Aᵀ * P = -1 := hL
    rw [add_comm]
    exact h

/-! ## A certificate is a quadratic-decay certificate -/

@[tmio T, powerlib_foundation] theorem inner_op (P : Matrix (Fin n) (Fin n) ℝ) (x y : ℝⁿ) :
    ⟪x, op P y⟫ = WithLp.ofLp x ⬝ᵥ (P *ᵥ WithLp.ofLp y) :=
  Matrix.inner_toEuclideanCLM P x y

/-- The energy `⟪x - e, P (x - e)⟫` of a certificate about the centre `e`. -/
def Certificate.energy {A : Matrix (Fin n) (Fin n) ℝ} (c : Certificate A) (e x : ℝⁿ) : ℝ :=
  ⟪x - e, op c.P (x - e)⟫

@[tmio T, powerlib_foundation] theorem Certificate.hasFDerivAt_energy {A : Matrix (Fin n) (Fin n) ℝ}
    (c : Certificate A) (e x : ℝⁿ) :
    HasFDerivAt (c.energy e) ((fderivInnerCLM ℝ (x - e, op c.P (x - e))).comp
      ((ContinuousLinearMap.id ℝ ℝⁿ).prod (op c.P))) x := by
  have h1 : HasFDerivAt (fun y : ℝⁿ => y - e) (ContinuousLinearMap.id ℝ ℝⁿ) x :=
    (hasFDerivAt_id x).sub_const e
  have h2 : HasFDerivAt (fun y : ℝⁿ => op c.P (y - e)) (op c.P) x := by
    have h := (op c.P).hasFDerivAt.comp x h1
    rwa [ContinuousLinearMap.comp_id] at h
  exact h1.inner ℝ h2

/-- The derivative of a quadratic certificate energy along any linear field. -/
@[tmio T, powerlib_foundation] theorem Certificate.lie_energy_matrix
    {A B : Matrix (Fin n) (Fin n) ℝ} (c : Certificate B) (e x : ℝⁿ) :
    fderiv ℝ (c.energy e) x (affineLinearVectorField A e x) =
      WithLp.ofLp (x - e) ⬝ᵥ ((Aᵀ * c.P + c.P * A) *ᵥ WithLp.ofLp (x - e)) := by
  rw [(c.hasFDerivAt_energy e x).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.id_apply, affine_apply]
  rw [← op_mul_apply, inner_op, inner_op]
  simp only [op, Matrix.ofLp_toEuclideanCLM, ← Matrix.mulVec_mulVec]
  set y := WithLp.ofLp (x - e)
  have hsym : (A *ᵥ y) ⬝ᵥ (c.P *ᵥ y) = y ⬝ᵥ (c.P *ᵥ (A *ᵥ y)) := by
    rw [Matrix.dotProduct_mulVec, dotProduct_comm]
    congr 1
    conv_lhs => rw [← c.symmetric]
    rw [Matrix.vecMul_transpose]
  rw [hsym, quadratic_sym c.symmetric]
  ring

/-- Along its own field, the energy decreases at the rate `‖x - e‖²`. -/
@[tmio T, powerlib_foundation] theorem Certificate.lie_energy {A : Matrix (Fin n) (Fin n) ℝ}
    (c : Certificate A) (e x : ℝⁿ) :
    fderiv ℝ (c.energy e) x (affineLinearVectorField A e x) = -‖x - e‖ ^ 2 := by
  rw [c.lie_energy_matrix, c.lyapunov, Matrix.neg_mulVec, Matrix.one_mulVec, dotProduct_neg]
  congr 1
  rw [EuclideanSpace.norm_sq_eq]
  simp [dotProduct, sq]

@[tmio T, powerlib_foundation] theorem Certificate.energy_contDiff {A : Matrix (Fin n) (Fin n) ℝ}
    (c : Certificate A) (e : ℝⁿ) : ContDiff ℝ 1 (c.energy e) :=
  (contDiff_id.sub contDiff_const).inner ℝ ((op c.P).contDiff.comp (contDiff_id.sub contDiff_const))

@[tmio T, powerlib_foundation] theorem Certificate.exists_energy_bounds {A : Matrix (Fin n) (Fin n) ℝ}
    (c : Certificate A) :
    ∃ α > 0, ∃ β ≥ α, ∀ z : ℝⁿ, α * ‖z‖ ^ 2 ≤ ⟪z, op c.P z⟫ ∧ ⟪z, op c.P z⟫ ≤ β * ‖z‖ ^ 2 := by
  have hc : Continuous fun z : ℝⁿ => ⟪z, op c.P z⟫ := continuous_id.inner (op c.P).continuous
  have hh : ∀ (a : ℝ) (z : ℝⁿ), ⟪a • z, op c.P (a • z)⟫ = a ^ 2 * ⟪z, op c.P z⟫ := fun a z => by
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
  have hp : ∀ z : ℝⁿ, z ≠ 0 → 0 < ⟪z, op c.P z⟫ := fun z hz => by
    rw [inner_op]
    exact c.positive _ (by simpa using hz)
  obtain ⟨α, hα, hlo⟩ := Flow.quadratic_lower_bound _ hc hh hp
  obtain ⟨β, -, hhi⟩ := Flow.quadratic_upper_bound _ hc hh hp
  exact ⟨α, hα, max α β, le_max_left α β, fun z => ⟨hlo z, (hhi z).trans
    (mul_le_mul_of_nonneg_right (le_max_right α β) (sq_nonneg ‖z‖))⟩⟩

/-- A Lyapunov certificate is a quadratic-decay certificate of the affine linear field: its energy
lies between two multiples of `‖x - e‖²` and decays at the rate `1 / β` of the upper one. -/
def Certificate.toQuadraticDecay {A : Matrix (Fin n) (Fin n) ℝ} (c : Certificate A) (e : ℝⁿ) :
    Flow.QuadraticDecay (affineLinearVectorField A e) (c.energy e) e where
  lower := c.exists_energy_bounds.choose
  upper := c.exists_energy_bounds.choose_spec.2.choose
  rate := 1 / c.exists_energy_bounds.choose_spec.2.choose
  lower_pos := c.exists_energy_bounds.choose_spec.1
  upper_pos := c.exists_energy_bounds.choose_spec.1.trans_le
    c.exists_energy_bounds.choose_spec.2.choose_spec.1
  rate_pos := one_div_pos.mpr (c.exists_energy_bounds.choose_spec.1.trans_le
    c.exists_energy_bounds.choose_spec.2.choose_spec.1)
  smooth := c.energy_contDiff e
  equilibrium := affine_isEquilibrium A e
  lower_bound x := (c.exists_energy_bounds.choose_spec.2.choose_spec.2 (x - e)).1
  upper_bound x := (c.exists_energy_bounds.choose_spec.2.choose_spec.2 (x - e)).2
  dissipation x := by
    have hβ := c.exists_energy_bounds.choose_spec.1.trans_le
      c.exists_energy_bounds.choose_spec.2.choose_spec.1
    have hb := (c.exists_energy_bounds.choose_spec.2.choose_spec.2 (x - e)).2
    rw [c.lie_energy]
    change -‖x - e‖ ^ 2 ≤ -(1 / c.exists_energy_bounds.choose_spec.2.choose) * c.energy e x
    have : 1 / c.exists_energy_bounds.choose_spec.2.choose * c.energy e x ≤ ‖x - e‖ ^ 2 := by
      rw [one_div, inv_mul_le_iff₀ hβ]
      exact hb
    linarith

/-- A certificate proves every attractive sentence at every centre: the generic quadratic-decay
theory applied to its energy. -/
@[tmio T, powerlib_foundation] theorem Certificate.holds {A : Matrix (Fin n) (Fin n) ℝ}
    (c : Certificate A) (e : ℝⁿ) {P : Flow.Property} (hP : P.Attractive) :
    P.holds (affineLinearVectorField A e) e :=
  ((c.toQuadraticDecay e).globallyExponentiallyStable (affine_contDiff A e)).holds hP

/-! ## The quadratic energy -/

/-- The quadratic energy `xᵀ P x / 2`: the stored energy of KYP certificates and of
port-Hamiltonian plants, and the Hamiltonian of quadratic pH systems. -/
def quadraticEnergy (P : Matrix (Fin n) (Fin n) ℝ) (x : ℝⁿ) : ℝ :=
  (1 / 2 : ℝ) * (WithLp.ofLp x ⬝ᵥ (P *ᵥ WithLp.ofLp x))

@[powerlib_foundation] private theorem quadraticEnergy_eq_inner (P : Matrix (Fin n) (Fin n) ℝ) :
    quadraticEnergy P = fun x => (1 / 2 : ℝ) * ⟪x, op P x⟫ := by
  funext x
  rw [inner_op]
  rfl

@[tmio T, powerlib_foundation] theorem contDiff_quadraticEnergy (P : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ 1 (quadraticEnergy P) := by
  rw [quadraticEnergy_eq_inner]
  exact contDiff_const.mul (contDiff_id.inner ℝ (op P).contDiff)

/-- For symmetric `P`, the derivative of `xᵀ P x / 2` in the direction `v` is `xᵀ P v`. -/
@[tmio T, powerlib_foundation] theorem fderiv_quadraticEnergy_apply
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : Pᵀ = P) (x v : ℝⁿ) :
    fderiv ℝ (quadraticEnergy P) x v = WithLp.ofLp x ⬝ᵥ (P *ᵥ WithLp.ofLp v) := by
  have hd : HasFDerivAt (quadraticEnergy P)
      ((1 / 2 : ℝ) • (fderivInnerCLM ℝ (x, op P x)).comp
        ((ContinuousLinearMap.id ℝ ℝⁿ).prod (op P))) x := by
    rw [quadraticEnergy_eq_inner]
    exact ((hasFDerivAt_id x).inner ℝ (op P).hasFDerivAt).const_mul (1 / 2 : ℝ)
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, ContinuousLinearMap.id_apply, inner_op,
    smul_eq_mul]
  have hsym : WithLp.ofLp v ⬝ᵥ (P *ᵥ WithLp.ofLp x) = WithLp.ofLp x ⬝ᵥ (P *ᵥ WithLp.ofLp v) := by
    rw [Matrix.dotProduct_mulVec, dotProduct_comm]
    congr 1
    conv_lhs => rw [← hP]
    rw [Matrix.vecMul_transpose]
  rw [hsym]
  ring

/-- A symmetric positive definite `P` along which the linear field strictly loses energy,
`xᵀ P A x < 0` for every `x ≠ 0`, gives a quadratic-decay certificate of the linear field with
the energy `xᵀ P x / 2`. -/
@[tmio T, powerlib_foundation] theorem quadraticDecay_of_lyapunov {A P : Matrix (Fin n) (Fin n) ℝ}
    (hP : Pᵀ = P) (hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (P *ᵥ x))
    (hneg : ∀ x : Fin n → ℝ, x ≠ 0 → x ⬝ᵥ (P *ᵥ (A *ᵥ x)) < 0) :
    Nonempty (Flow.QuadraticDecay (affineLinearVectorField A 0) (quadraticEnergy P) 0) := by
  have hhom : ∀ (a : ℝ) (x : ℝⁿ), quadraticEnergy P (a • x) = a ^ 2 * quadraticEnergy P x :=
    fun a x => by
      simp only [quadraticEnergy, WithLp.ofLp_smul, Matrix.mulVec_smul, dotProduct_smul,
        smul_dotProduct, smul_eq_mul]
      ring
  have hE : ∀ x : ℝⁿ, x ≠ 0 → 0 < quadraticEnergy P x := fun x hx =>
    mul_pos (by norm_num) (hpos _ (by simpa using hx))
  have hc := (contDiff_quadraticEnergy P).continuous
  obtain ⟨a, ha, hlo⟩ := Flow.quadratic_lower_bound _ hc hhom hE
  obtain ⟨b, hb0, hhi⟩ := Flow.quadratic_upper_bound _ hc hhom hE
  let W : ℝⁿ → ℝ := fun x => -(WithLp.ofLp x ⬝ᵥ (P *ᵥ (A *ᵥ WithLp.ofLp x)))
  have hWc : Continuous W := by
    simp only [W]
    fun_prop
  have hWh : ∀ (c : ℝ) (x : ℝⁿ), W (c • x) = c ^ 2 * W x := fun c x => by
    simp only [W, WithLp.ofLp_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
      smul_eq_mul]
    ring
  have hWp : ∀ x : ℝⁿ, x ≠ 0 → 0 < W x := fun x hx => neg_pos.mpr (hneg _ (by simpa using hx))
  obtain ⟨α, hα, hW⟩ := Flow.quadratic_lower_bound W hWc hWh hWp
  refine ⟨⟨a, b, α / b, ha, hb0, div_pos hα hb0, contDiff_quadraticEnergy P,
    affine_isEquilibrium A 0, fun x => by simpa using hlo x, fun x => by simpa using hhi x,
    fun x => ?_⟩⟩
  have hz : WithLp.ofLp (affineLinearVectorField A 0 x) = A *ᵥ WithLp.ofLp x := by
    simp [affine_apply, op, Matrix.ofLp_toEuclideanCLM]
  rw [fderiv_quadraticEnergy_apply hP, hz, show WithLp.ofLp x ⬝ᵥ (P *ᵥ (A *ᵥ WithLp.ofLp x)) =
    -W x from (neg_neg _).symm]
  have h1 := hW x
  have h2 := hhi x
  have h3 : α / b * quadraticEnergy P x ≤ α * ‖x‖ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hb0]
    nlinarith [sq_nonneg ‖x‖]
  linarith

/-! ## Conserved quadratic energies -/

@[tmio T, powerlib_foundation] theorem dotProduct_hasDerivWithinAt {X Y : ℝ → (Fin n → ℝ)}
    {dX dY : Fin n → ℝ} {s : Set ℝ} {t : ℝ} (hX : HasDerivWithinAt X dX s t)
    (hY : HasDerivWithinAt Y dY s t) :
    HasDerivWithinAt (fun τ => X τ ⬝ᵥ Y τ) (dX ⬝ᵥ Y t + X t ⬝ᵥ dY) s t := by
  have hd (i : Fin n) :=
    ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t hX).mul
      ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t hY)
  simpa [dotProduct, Finset.sum_add_distrib, Pi.mul_apply, Function.comp_def] using!
    HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ => hd i)

/-- A symmetric `P` with `Aᵀ P + P A = 0` gives a quadratic energy constant along every solution
segment of the linear field. -/
@[tmio T, powerlib_foundation] theorem quadratic_conserved {A P : Matrix (Fin n) (Fin n) ℝ}
    (hP : Pᵀ = P) (hl : Aᵀ * P + P * A = 0) {x : ℝ → ℝⁿ} {t₀ t₁ : ℝ}
    (hx : IsTrajectoryOn x (affineLinearVectorField A 0) t₀ t₁) :
    ∀ t ∈ Set.Icc t₀ t₁, WithLp.ofLp (x t) ⬝ᵥ (P *ᵥ WithLp.ofLp (x t)) =
      WithLp.ofLp (x t₀) ⬝ᵥ (P *ᵥ WithLp.ofLp (x t₀)) := by
  have hcont : ContinuousOn (fun t => WithLp.ofLp (x t) ⬝ᵥ (P *ᵥ WithLp.ofLp (x t)))
      (Set.Icc t₀ t₁) :=
    (by fun_prop : Continuous fun y : ℝⁿ => WithLp.ofLp y ⬝ᵥ (P *ᵥ WithLp.ofLp y)).comp_continuousOn
      hx.continuousOn
  refine constant_of_has_deriv_right_zero hcont fun t ht => ?_
  have hxt := hasDerivWithinAt_Ici_of_isIntegralCurveOn hx t ht
  have hX : HasDerivWithinAt (fun τ => WithLp.ofLp (x τ))
      (WithLp.ofLp (affineLinearVectorField A 0 (x t))) (Set.Ici t) t :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).hasFDerivAt.comp_hasDerivWithinAt t hxt
  have hfield : WithLp.ofLp (affineLinearVectorField A 0 (x t)) = A *ᵥ WithLp.ofLp (x t) := by
    simp [affine_apply]
  rw [hfield] at hX
  have hPX : HasDerivWithinAt (fun τ => P *ᵥ WithLp.ofLp (x τ))
      (P *ᵥ (A *ᵥ WithLp.ofLp (x t))) (Set.Ici t) t :=
    (P.mulVecLin.toContinuousLinearMap).hasFDerivAt.comp_hasDerivWithinAt t hX
  have h0 := quadratic_sym (A := A) hP (WithLp.ofLp (x t))
  rw [hl, Matrix.zero_mulVec, dotProduct_zero] at h0
  have hsym : (A *ᵥ WithLp.ofLp (x t)) ⬝ᵥ (P *ᵥ WithLp.ofLp (x t)) =
      WithLp.ofLp (x t) ⬝ᵥ (P *ᵥ (A *ᵥ WithLp.ofLp (x t))) := by
    rw [Matrix.dotProduct_mulVec, dotProduct_comm]
    congr 1
    conv_lhs => rw [← hP]
    rw [Matrix.vecMul_transpose]
  convert dotProduct_hasDerivWithinAt hX hPX using 1
  rw [hsym]
  linarith

/-- A positive definite `P` with `Aᵀ P + P A = 0` proves the linear field conservative: its
quadratic energy has a strict minimum at the origin and is constant along every solution. -/
@[tmio T, powerlib_foundation] theorem conservative_of_quadratic {A P : Matrix (Fin n) (Fin n) ℝ}
    (hP : Pᵀ = P) (hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (P *ᵥ x))
    (hl : Aᵀ * P + P * A = 0) : Flow.Conservative (affineLinearVectorField A 0) 0 := by
  refine ⟨fun y => WithLp.ofLp y ⬝ᵥ (P *ᵥ WithLp.ofLp y), by fun_prop, fun y hy => ?_,
    fun t₀ t₁ φ hφ t ht => quadratic_conserved hP hl hφ t ht⟩
  have hy' : WithLp.ofLp y ≠ 0 := fun h => hy (by rw [← WithLp.toLp_ofLp 2 y, h]; rfl)
  simpa using hpos _ hy'

end powerlib.Linear
