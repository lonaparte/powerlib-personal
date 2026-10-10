import theorem.Linear.Certificate

/-! # Frequency domain: poles, transfer functions and coordinate changes

The transfer function `C (sI - A)⁻¹ B + D` of a plant is an observation of the plant, not a
representation of it: plants with hidden modes share a transfer function with plants of
different stability (`transfer_not_determines_stability`). A coordinate change of the state is
a representation change: it preserves the transfer function and the spectrum, hence every
behavioural sentence. Pole stability is read through the characteristic matrix and agrees with
LeanForControl's Hurwitz predicate. -/

noncomputable section

namespace powerlib.Linear

open Matrix LinearSystems

variable {n p : ℕ}

/-- Entrywise complexification of a real matrix. -/
abbrev complexify {a b : Type*} (M : Matrix a b ℝ) : Matrix a b ℂ := M.map (algebraMap ℝ ℂ)

/-- The characteristic matrix `s I - A`. -/
def characteristicMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (s : ℂ) :
    Matrix ι ι ℂ :=
  s • (1 : Matrix ι ι ℂ) - complexify A

/-- All roots of the characteristic polynomial lie in the open left half plane. -/
def SpectrallyStable {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) : Prop :=
  ∀ s : ℂ, (characteristicMatrix A s).det = 0 → s.re < 0

/-- Pole stability does not depend on the labelling of the states. -/
@[powerlib_foundation] theorem spectrallyStable_reindex {ι ι' : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι') (A : Matrix ι ι ℝ) :
    SpectrallyStable (A.reindex e e) ↔ SpectrallyStable A := by
  have h (s : ℂ) :
      characteristicMatrix (A.reindex e e) s = (characteristicMatrix A s).reindex e e := by
    ext i j
    simp [characteristicMatrix, Matrix.one_apply]
  simp only [SpectrallyStable, h, Matrix.det_reindex_self]

/-- Pole stability is LeanForControl's Hurwitz predicate. -/
@[powerlib_foundation] theorem spectrallyStable_iff_isHurwitz (A : Matrix (Fin n) (Fin n) ℝ) :
    SpectrallyStable A ↔ IsHurwitz A := by
  constructor
  · intro h μ v hv heigen
    simpa only [neg_zero] using (show μ.re < 0 by
      apply h μ
      apply Matrix.exists_mulVec_eq_zero_iff.mp
      refine ⟨v, hv, ?_⟩
      rw [characteristicMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, heigen]
      exact sub_self _)
  · intro h μ hdet
    obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    simpa only [neg_zero] using (show μ.re < -0 by
      apply h μ v hv
      rw [characteristicMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hzero
      exact (sub_eq_zero.mp hzero).symm)

/-- The transfer function from port input to port output. -/
def transfer (M : Plant n p) (s : ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  complexify M.C * (characteristicMatrix M.A s)⁻¹ * complexify M.B + complexify M.D

/-- The same formula for state-space matrices on an arbitrary finite state index, as produced by
block constructions. -/
def transferOf {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (B : Matrix ι (Fin p) ℝ) (C : Matrix (Fin p) ι ℝ) (D : Matrix (Fin p) (Fin p) ℝ) (s : ℂ) :
    Matrix (Fin p) (Fin p) ℂ :=
  complexify C * (characteristicMatrix A s)⁻¹ * complexify B + complexify D

@[powerlib_foundation] theorem transfer_eq_transferOf (M : Plant n p) (s : ℂ) :
    transfer M s = transferOf M.A M.B M.C M.D s := rfl

@[powerlib_foundation] theorem characteristicMatrix_reindex {ι ι' : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι') (A : Matrix ι ι ℝ) (s : ℂ) :
    characteristicMatrix (A.reindex e e) s = (characteristicMatrix A s).reindex e e := by
  ext i j
  simp [characteristicMatrix, Matrix.one_apply]

/-- Relabelling the states does not change the transfer function. -/
@[powerlib_foundation] theorem transferOf_reindex {ι ι' : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι') (A : Matrix ι ι ℝ) (B : Matrix ι (Fin p) ℝ)
    (C : Matrix (Fin p) ι ℝ) (D : Matrix (Fin p) (Fin p) ℝ) (s : ℂ) :
    transferOf (A.reindex e e) (B.reindex e (Equiv.refl _)) (C.reindex (Equiv.refl _) e) D s =
      transferOf A B C D s := by
  unfold transferOf
  rw [characteristicMatrix_reindex, Matrix.inv_reindex]
  simp only [Matrix.reindex_apply, complexify, ← Matrix.submatrix_map]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  simp

/-! ## Coordinate changes -/

@[powerlib_foundation] theorem complexify_mul {a b c : Type*} [Fintype b] (M : Matrix a b ℝ)
    (N : Matrix b c ℝ) : complexify (M * N) = complexify M * complexify N :=
  Matrix.map_mul

@[powerlib_foundation] theorem complexify_neg {a b : Type*} (M : Matrix a b ℝ) :
    complexify (-M) = -complexify M :=
  Matrix.map_neg _ (fun x => map_neg _ x) M

@[powerlib_foundation] theorem complexify_sub {a b : Type*} (M N : Matrix a b ℝ) :
    complexify (M - N) = complexify M - complexify N :=
  Matrix.map_sub _ (fun x y => map_sub _ x y) M N

@[simp, powerlib_foundation] theorem complexify_zero {a b : Type*} :
    complexify (0 : Matrix a b ℝ) = 0 :=
  Matrix.map_zero _ (map_zero _)

@[powerlib_foundation] theorem complexify_fromRows {a b c : Type*} (M₁ : Matrix a c ℝ)
    (M₂ : Matrix b c ℝ) : complexify (fromRows M₁ M₂) = fromRows (complexify M₁) (complexify M₂) :=
  fromRows_map _ _ _

@[powerlib_foundation] theorem complexify_fromCols {a b c : Type*} (M₁ : Matrix c a ℝ)
    (M₂ : Matrix c b ℝ) : complexify (fromCols M₁ M₂) = fromCols (complexify M₁) (complexify M₂) :=
  fromCols_map _ _ _

@[powerlib_foundation] theorem complexify_fromBlocks {a b c d : Type*} (A : Matrix c a ℝ)
    (B : Matrix c b ℝ) (C : Matrix d a ℝ) (D : Matrix d b ℝ) :
    complexify (fromBlocks A B C D) =
      fromBlocks (complexify A) (complexify B) (complexify C) (complexify D) :=
  Matrix.fromBlocks_map _ _ _ _ _

@[powerlib_foundation] theorem complexify_mul_eq_one {a b : Type*} [Fintype b] [DecidableEq a]
    {T : Matrix a b ℝ} {S : Matrix b a ℝ} (h : T * S = 1) : complexify T * complexify S = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]

@[powerlib_foundation] theorem inv_conj {n' : ℕ} {T : Matrix (Fin n') (Fin n) ℂ}
    {S : Matrix (Fin n) (Fin n') ℂ} (hTS : T * S = 1) (hST : S * T = 1)
    (N : Matrix (Fin n) (Fin n) ℂ) : (T * N * S)⁻¹ = T * N⁻¹ * S := by
  by_cases h : IsUnit N.det
  · apply Matrix.inv_eq_right_inv
    calc T * N * S * (T * N⁻¹ * S) = T * (N * (S * T) * N⁻¹) * S := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hST, Matrix.mul_one, Matrix.mul_nonsing_inv _ h, Matrix.mul_one, hTS]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ (by rwa [Matrix.det_conj_of_mul_eq_one hTS hST]),
      Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.mul_zero, Matrix.zero_mul]

@[powerlib_foundation] theorem characteristicMatrix_conj {n' : ℕ} {T : Matrix (Fin n') (Fin n) ℝ}
    {S : Matrix (Fin n) (Fin n') ℝ} (hTS : T * S = 1) (A : Matrix (Fin n) (Fin n) ℝ) (s : ℂ) :
    characteristicMatrix (T * A * S) s =
      complexify T * characteristicMatrix A s * complexify S := by
  simp only [characteristicMatrix, Matrix.map_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, complexify_mul_eq_one hTS]

/-- The state coordinate change `x' = T x`, with inverse `x = S x'`. -/
def Plant.changeCoordinates {n' : ℕ} (T : Matrix (Fin n') (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n') ℝ) (M : Plant n p) : Plant n' p :=
  ⟨T * M.A * S, T * M.B, M.C * S, M.D⟩

/-- A coordinate change preserves the spectrum. -/
@[powerlib_foundation] theorem isHurwitz_conj {n' : ℕ} {T : Matrix (Fin n') (Fin n) ℝ}
    {S : Matrix (Fin n) (Fin n') ℝ} (hTS : T * S = 1) (hST : S * T = 1)
    (A : Matrix (Fin n) (Fin n) ℝ) : IsHurwitz (T * A * S) ↔ IsHurwitz A := by
  rw [← spectrallyStable_iff_isHurwitz, ← spectrallyStable_iff_isHurwitz]
  simp only [SpectrallyStable, characteristicMatrix_conj hTS,
    Matrix.det_conj_of_mul_eq_one (complexify_mul_eq_one hTS) (complexify_mul_eq_one hST)]

/-- A coordinate change preserves the transfer function. -/
@[powerlib_foundation] theorem transfer_changeCoordinates {n' : ℕ}
    {T : Matrix (Fin n') (Fin n) ℝ} {S : Matrix (Fin n) (Fin n') ℝ} (hTS : T * S = 1)
    (hST : S * T = 1) (M : Plant n p) (s : ℂ) :
    transfer (M.changeCoordinates T S) s = transfer M s := by
  simp only [transfer, Plant.changeCoordinates]
  rw [characteristicMatrix_conj hTS,
    inv_conj (complexify_mul_eq_one hTS) (complexify_mul_eq_one hST), complexify_mul,
    complexify_mul]
  congr 1
  calc complexify M.C * complexify S * (complexify T * (characteristicMatrix M.A s)⁻¹ *
        complexify S) * (complexify T * complexify M.B)
      = complexify M.C * (complexify S * complexify T) * (characteristicMatrix M.A s)⁻¹ *
          (complexify S * complexify T) * complexify M.B := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [complexify_mul_eq_one hST, Matrix.mul_one, Matrix.mul_one]

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- Lyapunov stability of the origin survives a linear change of coordinates. -/
@[powerlib_foundation] theorem lyapunovStable_conj {f : ℝⁿ → ℝⁿ} (L K : ℝⁿ →L[ℝ] ℝⁿ)
    (hKL : ∀ x, K (L x) = x) (hLK : ∀ x, L (K x) = x) (hf : LyapunovStable f 0) :
    LyapunovStable (fun x => L (f (K x))) 0 := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hf (ε / (‖L‖ + 1)) (by positivity)
  refine ⟨δ / (‖K‖ + 1), by positivity, fun t₀ t₁ φ hφ h0 t ht => ?_⟩
  have hψ : IsTrajectoryOn (fun t => K (φ t)) f t₀ t₁ := fun s hs => by
    have := K.hasFDerivAt.comp_hasDerivWithinAt s (hφ s hs)
    simpa [Function.comp_def, hKL] using this
  have hK0 : ‖K (φ t₀) - 0‖ < δ := by
    rw [sub_zero] at h0 ⊢
    calc ‖K (φ t₀)‖ ≤ ‖K‖ * ‖φ t₀‖ := K.le_opNorm _
      _ ≤ (‖K‖ + 1) * ‖φ t₀‖ := by gcongr; linarith
      _ < (‖K‖ + 1) * (δ / (‖K‖ + 1)) := by gcongr
      _ = δ := by field_simp
  have hb := h t₀ t₁ _ hψ hK0 t ht
  rw [sub_zero] at hb ⊢
  calc ‖φ t‖ = ‖L (K (φ t))‖ := by rw [hLK]
    _ ≤ ‖L‖ * ‖K (φ t)‖ := L.le_opNorm _
    _ ≤ (‖L‖ + 1) * ‖K (φ t)‖ := by gcongr; linarith
    _ < (‖L‖ + 1) * (ε / (‖L‖ + 1)) := by gcongr
    _ = ε := by field_simp

@[powerlib_foundation] theorem lyapunovStable_conj_iff {T S : Matrix (Fin n) (Fin n) ℝ}
    (hTS : T * S = 1) (hST : S * T = 1) (A : Matrix (Fin n) (Fin n) ℝ) :
    LyapunovStable (affineLinearVectorField (T * A * S) 0) 0 ↔
      LyapunovStable (affineLinearVectorField A 0) 0 := by
  have h₁ : affineLinearVectorField (T * A * S) 0 =
      fun x => op T (affineLinearVectorField A 0 (op S x)) := by
    funext x
    simp only [affine_apply, sub_zero, op_mul_apply]
  have h₂ : affineLinearVectorField A 0 =
      fun x => op S (affineLinearVectorField (T * A * S) 0 (op T x)) := by
    funext x
    simp only [affine_apply, sub_zero, op_mul_apply, op_cancel hST]
  constructor
  · intro h
    rw [h₂]
    exact lyapunovStable_conj (op S) (op T) (op_cancel hTS) (op_cancel hST) h
  · intro h
    rw [h₁]
    exact lyapunovStable_conj (op T) (op S) (op_cancel hST) (op_cancel hTS) h

/-- A coordinate change preserves every behavioural sentence at the origin. -/
@[powerlib_foundation] theorem holds_conj (P : Flow.Property) {T S : Matrix (Fin n) (Fin n) ℝ}
    (hTS : T * S = 1) (hST : S * T = 1) (A : Matrix (Fin n) (Fin n) ℝ) :
    P.holds (affineLinearVectorField (T * A * S) 0) 0 ↔
      P.holds (affineLinearVectorField A 0) 0 := by
  by_cases hP : P.Attractive
  · rw [holds_iff_isHurwitz 0 hP, holds_iff_isHurwitz 0 hP, isHurwitz_conj hTS hST]
  · cases P with
    | lyapunovStable => exact lyapunovStable_conj_iff hTS hST A
    | unstable => exact not_congr (lyapunovStable_conj_iff hTS hST A)
    | _ => exact absurd trivial hP

/-! ## Similar plants -/

/-- Two plants are similar when a state coordinate change carries one into the other. -/
def Similar {n' : ℕ} (m : Plant n p) (m' : Plant n' p) : Prop :=
  ∃ (T : Matrix (Fin n') (Fin n) ℝ) (S : Matrix (Fin n) (Fin n') ℝ), T * S = 1 ∧ S * T = 1 ∧
    m' = m.changeCoordinates T S

@[powerlib_foundation] theorem Plant.changeCoordinates_changeCoordinates {n' n'' : ℕ}
    (M : Plant n p) (T : Matrix (Fin n') (Fin n) ℝ) (S : Matrix (Fin n) (Fin n') ℝ)
    (T' : Matrix (Fin n'') (Fin n') ℝ) (S' : Matrix (Fin n') (Fin n'') ℝ) :
    (M.changeCoordinates T S).changeCoordinates T' S' = M.changeCoordinates (T' * T) (S * S') := by
  ext : 1 <;> simp only [Plant.changeCoordinates, Matrix.mul_assoc]

@[powerlib_foundation] theorem Plant.changeCoordinates_one (M : Plant n p) :
    M.changeCoordinates 1 1 = M := by
  ext : 1 <;> simp [Plant.changeCoordinates]

@[powerlib_foundation] theorem Similar.refl (m : Plant n p) : Similar m m :=
  ⟨1, 1, Matrix.mul_one 1, Matrix.mul_one 1, m.changeCoordinates_one.symm⟩

@[powerlib_foundation] theorem Similar.symm {n' : ℕ} {m : Plant n p} {m' : Plant n' p}
    (h : Similar m m') : Similar m' m := by
  obtain ⟨T, S, hTS, hST, rfl⟩ := h
  exact ⟨S, T, hST, hTS, by rw [Plant.changeCoordinates_changeCoordinates, hST,
    Plant.changeCoordinates_one]⟩

@[powerlib_foundation] theorem Similar.trans {n' n'' : ℕ} {m : Plant n p} {m' : Plant n' p}
    {m'' : Plant n'' p} (h : Similar m m') (h' : Similar m' m'') : Similar m m'' := by
  obtain ⟨T, S, hTS, hST, rfl⟩ := h
  obtain ⟨T', S', hTS', hST', rfl⟩ := h'
  refine ⟨T' * T, S * S', ?_, ?_, Plant.changeCoordinates_changeCoordinates _ _ _ _ _⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc T, hTS, Matrix.one_mul, hTS']
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc S', hST', Matrix.one_mul, hST]

@[powerlib_foundation] theorem Similar.transfer_eq {n' : ℕ} {m : Plant n p} {m' : Plant n' p}
    (h : Similar m m') (s : ℂ) : transfer m' s = transfer m s := by
  obtain ⟨T, S, hTS, hST, rfl⟩ := h
  exact transfer_changeCoordinates hTS hST m s

/-- Similar plants have the same spectrum. -/
@[powerlib_foundation] theorem Similar.isHurwitz_iff {n' : ℕ} {m : Plant n p} {m' : Plant n' p}
    (h : Similar m m') : IsHurwitz m'.A ↔ IsHurwitz m.A := by
  obtain ⟨T, S, hTS, hST, rfl⟩ := h
  exact isHurwitz_conj hTS hST m.A

/-- Similar plants of the same dimension satisfy the same behavioural sentences. -/
@[powerlib_foundation] theorem Similar.holds_iff {m m' : Plant n p} (h : Similar m m')
    (P : Flow.Property) :
    P.holds (affineLinearVectorField m'.A 0) 0 ↔ P.holds (affineLinearVectorField m.A 0) 0 := by
  obtain ⟨T, S, hTS, hST, rfl⟩ := h
  exact holds_conj P hTS hST m.A

/-- A coordinate change, as an equivalence of plants. -/
def Plant.similarity (T S : Matrix (Fin n) (Fin n) ℝ) (hTS : T * S = 1) (hST : S * T = 1) :
    Plant n p ≃ Plant n p where
  toFun := Plant.changeCoordinates T S
  invFun := Plant.changeCoordinates S T
  left_inv M := by
    ext : 1
    · show S * (T * M.A * S) * T = M.A
      calc S * (T * M.A * S) * T = (S * T) * M.A * (S * T) := by simp only [Matrix.mul_assoc]
        _ = M.A := by rw [hST, Matrix.one_mul, Matrix.mul_one]
    · show S * (T * M.B) = M.B
      rw [← Matrix.mul_assoc, hST, Matrix.one_mul]
    · show M.C * S * T = M.C
      rw [Matrix.mul_assoc, hST, Matrix.mul_one]
    · rfl
  right_inv M := by
    ext : 1
    · show T * (S * M.A * T) * S = M.A
      calc T * (S * M.A * T) * S = (T * S) * M.A * (T * S) := by simp only [Matrix.mul_assoc]
        _ = M.A := by rw [hTS, Matrix.one_mul, Matrix.mul_one]
    · show T * (S * M.B) = M.B
      rw [← Matrix.mul_assoc, hTS, Matrix.one_mul]
    · show M.C * T * S = M.C
      rw [Matrix.mul_assoc, hTS, Matrix.mul_one]
    · rfl

/-! ## The transfer function is an observation -/

/-- An unstable hidden mode. -/
def hiddenMode : Plant 1 1 := ⟨!![1], 0, 0, 0⟩

/-- A stable mode with the same (zero) transfer function. -/
def quietMode : Plant 1 1 := ⟨!![-1], 0, 0, 0⟩

/-- The transfer function does not determine stability. -/
@[powerlib_foundation] theorem transfer_not_determines_stability :
    transfer hiddenMode = transfer quietMode ∧ IsHurwitz quietMode.A ∧
      ¬ IsHurwitz hiddenMode.A := by
  refine ⟨by funext s; simp [transfer, hiddenMode, quietMode], ?_, ?_⟩
  · rw [← spectrallyStable_iff_isHurwitz]
    intro s hs
    simp [characteristicMatrix, quietMode, Matrix.det_unique] at hs
    have : s = -1 := by linear_combination hs
    rw [this]
    norm_num
  · rw [← spectrallyStable_iff_isHurwitz]
    intro h
    have := h 1 (by simp [characteristicMatrix, hiddenMode, Matrix.det_unique])
    norm_num at this

end powerlib.Linear
