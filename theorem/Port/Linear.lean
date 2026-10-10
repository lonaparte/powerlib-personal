import theorem.Port.Basic
import theorem.Linear.Certificate

/-! # Linear plants as port systems

The port system of a linear plant has input `u` and output `y = C x + D u`. Its zero-input field is
the hub's affine linear field, so its stability is the hub's. A KYP certificate — a nonnegative
symmetric storage matrix for which the plant dissipates and whose output is the storage gradient
read through `B` — proves passivity with the quadratic storage `xᵀ P x / 2`. -/

noncomputable section

namespace powerlib.Linear

open Matrix Set LinearSystems

variable {n p : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- The port system of a plant. -/
def Plant.system (M : Plant n p) : Port.System n p :=
  ⟨fun x u => op M.A x + WithLp.toLp 2 (M.B *ᵥ u), fun x u => M.C *ᵥ WithLp.ofLp x + M.D *ᵥ u⟩

/-- With the ports at zero, the plant is the hub's linear field. -/
@[powerlib_foundation] theorem Plant.system_zeroInput (M : Plant n p) :
    M.system.zeroInput = affineLinearVectorField M.A 0 := by
  funext x
  simp [Port.System.zeroInput, Plant.system, affine_apply]

/-- A KYP certificate for passivity. -/
structure KYP (M : Plant n p) where
  /-- The storage matrix. -/
  P : Matrix (Fin n) (Fin n) ℝ
  symmetric : Pᵀ = P
  nonneg : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (P *ᵥ x)
  dissipation : ∀ x : Fin n → ℝ, x ⬝ᵥ ((M.Aᵀ * P + P * M.A) *ᵥ x) ≤ 0
  output : M.Bᵀ * P = M.C
  feedthrough : ∀ u : Fin p → ℝ, 0 ≤ u ⬝ᵥ (M.D *ᵥ u)

/-- The quadratic storage `xᵀ P x / 2`. -/
def KYP.storage {M : Plant n p} (c : KYP M) (x : ℝⁿ) : ℝ :=
  WithLp.ofLp x ⬝ᵥ (c.P *ᵥ WithLp.ofLp x) / 2

@[powerlib_foundation] theorem dotProduct_hasDerivWithinAt {X Y : ℝ → (Fin n → ℝ)}
    {dX dY : Fin n → ℝ} {s : Set ℝ} {t : ℝ} (hX : HasDerivWithinAt X dX s t)
    (hY : HasDerivWithinAt Y dY s t) :
    HasDerivWithinAt (fun τ => X τ ⬝ᵥ Y τ) (dX ⬝ᵥ Y t + X t ⬝ᵥ dY) s t := by
  have hd (i : Fin n) :=
    ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t hX).mul
      ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t hY)
  simpa [dotProduct, Finset.sum_add_distrib, Pi.mul_apply, Function.comp_def] using!
    HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ => hd i)

@[powerlib_foundation] theorem KYP.output_dot {M : Plant n p} (c : KYP M) (X : Fin n → ℝ)
    (u : Fin p → ℝ) : X ⬝ᵥ (c.P *ᵥ (M.B *ᵥ u)) = (M.C *ᵥ X) ⬝ᵥ u := by
  rw [← c.output, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.transpose_mul, Matrix.transpose_transpose, c.symmetric]

/-- A KYP certificate proves passivity with its quadratic storage. -/
@[powerlib_foundation] theorem KYP.passiveWith {M : Plant n p} (c : KYP M) :
    M.system.PassiveWith c.storage := by
  apply Port.System.passiveWith_of_rate _ _ (fun x => div_nonneg (c.nonneg _) two_pos.le)
    (fun x u => WithLp.ofLp x ⬝ᵥ (c.P *ᵥ WithLp.ofLp (M.system.field x u)))
  · intro u x t₀ t₁ t hx ht
    have hX : HasDerivWithinAt (fun τ => WithLp.ofLp (x τ))
        (WithLp.ofLp (M.system.field (x t) (u t))) (Icc t₀ t₁) t :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).hasFDerivAt.comp_hasDerivWithinAt t
        (hx t ht)
    have hPX : HasDerivWithinAt (fun τ => c.P *ᵥ WithLp.ofLp (x τ))
        (c.P *ᵥ WithLp.ofLp (M.system.field (x t) (u t))) (Icc t₀ t₁) t :=
      (c.P.mulVecLin.toContinuousLinearMap).hasFDerivAt.comp_hasDerivWithinAt t hX
    convert (dotProduct_hasDerivWithinAt hX hPX).div_const 2 using 1
    have hsym : WithLp.ofLp (M.system.field (x t) (u t)) ⬝ᵥ (c.P *ᵥ WithLp.ofLp (x t)) =
        WithLp.ofLp (x t) ⬝ᵥ (c.P *ᵥ WithLp.ofLp (M.system.field (x t) (u t))) := by
      rw [Matrix.dotProduct_mulVec, dotProduct_comm]
      congr 1
      conv_lhs => rw [← c.symmetric]
      rw [Matrix.vecMul_transpose]
    rw [hsym]
    ring
  · intro x u
    have hfield : WithLp.ofLp (M.system.field x u) =
        M.A *ᵥ WithLp.ofLp x + M.B *ᵥ u := by
      simp [Plant.system]
    rw [hfield, Matrix.mulVec_add, dotProduct_add, c.output_dot]
    have hdiss := c.dissipation (WithLp.ofLp x)
    rw [quadratic_sym c.symmetric] at hdiss
    have hD := c.feedthrough u
    simp only [Port.System.supply, Plant.system, dotProduct_add]
    rw [dotProduct_comm (M.C *ᵥ WithLp.ofLp x) u]
    linarith

/-- With a lossless certificate, `Aᵀ P + P A = 0`, the storage is conserved along every zero-input
solution segment. -/
@[powerlib_foundation] theorem KYP.storage_conserved {M : Plant n p} (c : KYP M)
    (hl : M.Aᵀ * c.P + c.P * M.A = 0) {x : ℝ → ℝⁿ} {t₀ t₁ : ℝ}
    (hx : IsTrajectoryOn x (affineLinearVectorField M.A 0) t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, c.storage (x t) = c.storage (x t₀) := by
  have hcont : ContinuousOn (fun t => c.storage (x t)) (Icc t₀ t₁) :=
    (by unfold KYP.storage; fun_prop : Continuous c.storage).comp_continuousOn hx.continuousOn
  refine constant_of_has_deriv_right_zero hcont fun t ht => ?_
  have hxt := hasDerivWithinAt_Ici_of_isIntegralCurveOn hx t ht
  have hX : HasDerivWithinAt (fun τ => WithLp.ofLp (x τ))
      (WithLp.ofLp (affineLinearVectorField M.A 0 (x t))) (Ici t) t :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).hasFDerivAt.comp_hasDerivWithinAt t hxt
  have hfield : WithLp.ofLp (affineLinearVectorField M.A 0 (x t)) = M.A *ᵥ WithLp.ofLp (x t) := by
    simp [affine_apply]
  rw [hfield] at hX
  have hPX : HasDerivWithinAt (fun τ => c.P *ᵥ WithLp.ofLp (x τ))
      (c.P *ᵥ (M.A *ᵥ WithLp.ofLp (x t))) (Ici t) t :=
    (c.P.mulVecLin.toContinuousLinearMap).hasFDerivAt.comp_hasDerivWithinAt t hX
  have h0 := quadratic_sym (A := M.A) c.symmetric (WithLp.ofLp (x t))
  rw [hl, Matrix.zero_mulVec, dotProduct_zero] at h0
  have hsym : (M.A *ᵥ WithLp.ofLp (x t)) ⬝ᵥ (c.P *ᵥ WithLp.ofLp (x t)) =
      WithLp.ofLp (x t) ⬝ᵥ (c.P *ᵥ (M.A *ᵥ WithLp.ofLp (x t))) := by
    rw [Matrix.dotProduct_mulVec, dotProduct_comm]
    congr 1
    conv_lhs => rw [← c.symmetric]
    rw [Matrix.vecMul_transpose]
  show HasDerivWithinAt (fun τ => WithLp.ofLp (x τ) ⬝ᵥ (c.P *ᵥ WithLp.ofLp (x τ)) / 2) 0 (Ici t) t
  convert (dotProduct_hasDerivWithinAt hX hPX).div_const 2 using 1
  rw [hsym]
  linarith

/-- With quadratic bounds on the storage, a KYP certificate proves Lyapunov stability of the
zero-input plant in the Flow semantics. -/
@[powerlib_foundation] theorem KYP.lyapunovStable {M : Plant n p} (c : KYP M) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x, a * ‖x‖ ^ 2 ≤ c.storage x ∧ c.storage x ≤ b * ‖x‖ ^ 2) :
    LyapunovStable (affineLinearVectorField M.A 0) 0 := by
  rw [← M.system_zeroInput]
  exact c.passiveWith.lyapunovStable ha hab hbounds

/-- A KYP certificate with a positive definite storage matrix proves Lyapunov stability of the
zero-input plant in the Flow semantics. -/
@[powerlib_foundation] theorem KYP.lyapunovStable_of_pos {M : Plant n p} (c : KYP M)
    (hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (c.P *ᵥ x)) :
    LyapunovStable (affineLinearVectorField M.A 0) 0 := by
  obtain ⟨a, ha, b, hab, hb⟩ := Flow.quadratic_bounds c.storage
    (by unfold KYP.storage; fun_prop)
    (fun r x => by
      simp only [KYP.storage, WithLp.ofLp_smul, Matrix.mulVec_smul, dotProduct_smul,
        smul_dotProduct, smul_eq_mul]
      ring)
    (fun x hx => div_pos (hpos _ (by simpa using hx)) two_pos)
  exact c.lyapunovStable ha hab hb

end powerlib.Linear
