import theorem.Linear.Stability
import theorem.Flow.Certificate

/-! # Lyapunov certificates

A certificate is the evidence a synthesizer returns for a state matrix `A`: a symmetric matrix
`P`, positive on every nonzero state, solving `Aᵀ P + P A = -1`. It is proof-relevant data,
indexed by the exact matrix it was produced for. It introduces no meaning of its own: its energy
`⟪x - e, P (x - e)⟫` is a quadratic-decay certificate of the affine linear field
(`Certificate.toQuadraticDecay`), so what it proves is what the generic certificate theory of
`Flow` proves. A certificate exists exactly when `A` is Hurwitz. Families supply synthesizers that
construct certificates; they do not restate what a certificate proves. -/

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

/-- For a symmetric `P`, the quadratic form of `Aᵀ P + P A` is twice that of `P A`. -/
@[powerlib_foundation] theorem quadratic_sym {A P : Matrix (Fin n) (Fin n) ℝ} (hP : Pᵀ = P)
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

@[powerlib_foundation] theorem quadratic_lyapunov {A P : Matrix (Fin n) (Fin n) ℝ}
    (hP : Pᵀ = P) (hL : Aᵀ * P + P * A = -1) (z : Fin n → ℝ) :
    2 * (z ⬝ᵥ (P *ᵥ (A *ᵥ z))) = -(z ⬝ᵥ z) := by
  rw [← quadratic_sym hP, hL, Matrix.neg_mulVec, Matrix.one_mulVec, dotProduct_neg]

/-- A certificate proves the matrix Hurwitz. -/
@[powerlib_foundation, aesop safe forward]
theorem Certificate.isHurwitz {A : Matrix (Fin n) (Fin n) ℝ}
    (c : Certificate A) : IsHurwitz A := by
  intro μ v hv heig
  let x : Fin n → ℝ := fun j => (v j).re
  let y : Fin n → ℝ := fun j => (v j).im
  have hcomp (j : Fin n) : ∑ k, (A j k : ℂ) * v k = μ * v j := by
    have hj := congrFun heig j
    simpa [Matrix.mulVec, dotProduct, Matrix.map_apply] using hj
  have hAx : A *ᵥ x = μ.re • x - μ.im • y := by
    funext j
    have h := congrArg Complex.re (hcomp j)
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] at h
    simp only [Matrix.mulVec, dotProduct, x, y, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hAy : A *ᵥ y = μ.im • x + μ.re • y := by
    funext j
    have h := congrArg Complex.im (hcomp j)
    simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero] at h
    simp only [Matrix.mulVec, dotProduct, x, y, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hx := quadratic_lyapunov c.symmetric c.lyapunov x
  have hy := quadratic_lyapunov c.symmetric c.lyapunov y
  rw [hAx, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_sub,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hx
  rw [hAy, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_add,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hy
  have hcross : y ⬝ᵥ (c.P *ᵥ x) = x ⬝ᵥ (c.P *ᵥ y) := by
    rw [Matrix.dotProduct_mulVec, dotProduct_comm]
    congr 1
    conv_lhs => rw [← c.symmetric]
    rw [Matrix.vecMul_transpose]
  rw [hcross] at hy
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext j
    apply Complex.ext
    · exact congrFun h.1 j
    · exact congrFun h.2 j
  have hq : 0 < x ⬝ᵥ (c.P *ᵥ x) + y ⬝ᵥ (c.P *ᵥ y) := by
    have hqx : 0 ≤ x ⬝ᵥ (c.P *ᵥ x) := by
      by_cases h0 : x = 0
      · simp [h0]
      · exact (c.positive x h0).le
    have hqy : 0 ≤ y ⬝ᵥ (c.P *ᵥ y) := by
      by_cases h0 : y = 0
      · simp [h0]
      · exact (c.positive y h0).le
    rcases hxy with h | h
    · linarith [c.positive x h]
    · linarith [c.positive y h]
  have hnn : 0 ≤ x ⬝ᵥ x + y ⬝ᵥ y := by
    have h1 : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun j _ => mul_self_nonneg (x j)
    have h2 : 0 ≤ y ⬝ᵥ y := Finset.sum_nonneg fun j _ => mul_self_nonneg (y j)
    linarith
  have hsum : 2 * μ.re * (x ⬝ᵥ (c.P *ᵥ x) + y ⬝ᵥ (c.P *ᵥ y)) = -(x ⬝ᵥ x + y ⬝ᵥ y) := by
    linarith
  have : μ.re < 0 := by
    by_contra hμ
    push Not at hμ
    have : 0 ≤ 2 * μ.re * (x ⬝ᵥ (c.P *ᵥ x) + y ⬝ᵥ (c.P *ᵥ y)) := by positivity
    have hpos : 0 < x ⬝ᵥ x + y ⬝ᵥ y := by
      rcases hxy with h | h
      · have : 0 < x ⬝ᵥ x := by
          obtain ⟨j, hj⟩ := Function.ne_iff.mp h
          exact Finset.sum_pos' (fun k _ => mul_self_nonneg (x k))
            ⟨j, Finset.mem_univ _, mul_self_pos.mpr hj⟩
        have : 0 ≤ y ⬝ᵥ y := Finset.sum_nonneg fun j _ => mul_self_nonneg (y j)
        linarith
      · have : 0 < y ⬝ᵥ y := by
          obtain ⟨j, hj⟩ := Function.ne_iff.mp h
          exact Finset.sum_pos' (fun k _ => mul_self_nonneg (y k))
            ⟨j, Finset.mem_univ _, mul_self_pos.mpr hj⟩
        have : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun j _ => mul_self_nonneg (x j)
        linarith
    linarith
  simpa using this

/-- A certificate exists exactly when the matrix is Hurwitz (LeanForControl's Lyapunov
equation for the converse). -/
@[powerlib_foundation] theorem nonempty_certificate_iff (A : Matrix (Fin n) (Fin n) ℝ) :
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

@[powerlib_foundation] theorem inner_op (P : Matrix (Fin n) (Fin n) ℝ) (x y : ℝⁿ) :
    ⟪x, op P y⟫ = WithLp.ofLp x ⬝ᵥ (P *ᵥ WithLp.ofLp y) :=
  Matrix.inner_toEuclideanCLM P x y

/-- The energy `⟪x - e, P (x - e)⟫` of a certificate about the centre `e`. -/
def Certificate.energy {A : Matrix (Fin n) (Fin n) ℝ} (c : Certificate A) (e x : ℝⁿ) : ℝ :=
  ⟪x - e, op c.P (x - e)⟫

@[powerlib_foundation] theorem Certificate.hasFDerivAt_energy {A : Matrix (Fin n) (Fin n) ℝ}
    (c : Certificate A) (e x : ℝⁿ) :
    HasFDerivAt (c.energy e) ((fderivInnerCLM ℝ (x - e, op c.P (x - e))).comp
      ((ContinuousLinearMap.id ℝ ℝⁿ).prod (op c.P))) x := by
  have h1 : HasFDerivAt (fun y : ℝⁿ => y - e) (ContinuousLinearMap.id ℝ ℝⁿ) x :=
    (hasFDerivAt_id x).sub_const e
  have h2 : HasFDerivAt (fun y : ℝⁿ => op c.P (y - e)) (op c.P) x := by
    have h := (op c.P).hasFDerivAt.comp x h1
    rwa [ContinuousLinearMap.comp_id] at h
  exact h1.inner ℝ h2

/-- Along the field, the energy decreases at the rate `‖x - e‖²`. -/
@[powerlib_foundation] theorem Certificate.lie_energy {A : Matrix (Fin n) (Fin n) ℝ}
    (c : Certificate A) (e x : ℝⁿ) :
    fderiv ℝ (c.energy e) x (affineLinearVectorField A e x) = -‖x - e‖ ^ 2 := by
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
  have hL := quadratic_lyapunov c.symmetric c.lyapunov y
  have hn : ‖x - e‖ ^ 2 = y ⬝ᵥ y := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [y, dotProduct, sq]
  rw [hsym, hn]
  linarith

@[powerlib_foundation] theorem Certificate.energy_contDiff {A : Matrix (Fin n) (Fin n) ℝ}
    (c : Certificate A) (e : ℝⁿ) : ContDiff ℝ 1 (c.energy e) :=
  (contDiff_id.sub contDiff_const).inner ℝ ((op c.P).contDiff.comp (contDiff_id.sub contDiff_const))

@[powerlib_foundation] theorem Certificate.exists_energy_bounds {A : Matrix (Fin n) (Fin n) ℝ}
    (c : Certificate A) :
    ∃ α > 0, ∃ β ≥ α, ∀ z : ℝⁿ, α * ‖z‖ ^ 2 ≤ ⟪z, op c.P z⟫ ∧ ⟪z, op c.P z⟫ ≤ β * ‖z‖ ^ 2 :=
  Flow.quadratic_bounds (fun z => ⟪z, op c.P z⟫)
    (continuous_id.inner (op c.P).continuous)
    (fun a z => by simp only [map_smul, real_inner_smul_left, real_inner_smul_right]; ring)
    (fun z hz => by
      rw [inner_op]
      exact c.positive _ (by simpa using hz))

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
@[powerlib_foundation] theorem Certificate.holds {A : Matrix (Fin n) (Fin n) ℝ}
    (c : Certificate A) (e : ℝⁿ) {P : Flow.Property} (hP : P.Attractive) :
    P.holds (affineLinearVectorField A e) e :=
  (c.toQuadraticDecay e).holds (affine_contDiff A e) hP

/-! ## Conserved quadratic energies -/

@[powerlib_foundation] theorem dotProduct_hasDerivWithinAt {X Y : ℝ → (Fin n → ℝ)}
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
@[powerlib_foundation] theorem quadratic_conserved {A P : Matrix (Fin n) (Fin n) ℝ}
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
@[powerlib_foundation] theorem conservative_of_quadratic {A P : Matrix (Fin n) (Fin n) ℝ}
    (hP : Pᵀ = P) (hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (P *ᵥ x))
    (hl : Aᵀ * P + P * A = 0) : Flow.Conservative (affineLinearVectorField A 0) 0 := by
  refine ⟨fun y => WithLp.ofLp y ⬝ᵥ (P *ᵥ WithLp.ofLp y), by fun_prop, fun y hy => ?_,
    fun t₀ t₁ φ hφ t ht => quadratic_conserved hP hl hφ t ht⟩
  have hy' : WithLp.ofLp y ≠ 0 := fun h => hy (by rw [← WithLp.toLp_ofLp 2 y, h]; rfl)
  simpa using hpos _ hy'

end powerlib.Linear
