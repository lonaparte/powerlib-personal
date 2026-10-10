import theorem.Linear.Certificate

/-! # Synthesis of Lyapunov certificates over the rationals

Only a rational state matrix `A` is submitted. The synthesizer solves the Lyapunov equation
`Aᵀ P + P A = -1` for `P` by Gauss–Jordan elimination over `ℚ` and factors `P = L D Lᵀ`. It is
ordinary code and is not trusted: its proposal is accepted only through a decidable check of exact
rational identities — the Lyapunov equation, the factorization, the unit lower-triangular shape of
`L` and the positivity of `D` — whose soundness is a theorem (`Witness.certificate`). The kernel
runs both the synthesizer and the check (`decide +kernel`), so no witness is supplied by hand and
an arbitrarily wrong proposal can only be rejected. An accepted matrix receives a `Certificate` of
its real image, hence every attractive sentence. -/

namespace powerlib.Linear.Synthesis

open Matrix

variable {n : ℕ}

/-! ## The untrusted synthesizer -/

/-- One Gauss–Jordan step on column `c` of an augmented system. -/
def eliminate (rows : List (List ℚ)) (c : ℕ) : Option (List (List ℚ)) :=
  match (rows.drop c).findIdx? (fun r => r.getD c 0 != 0) with
  | none => none
  | some k =>
    let rc := rows.getD c []
    let rp := rows.getD (c + k) []
    let pivot := rp.map (· / rp.getD c 0)
    some (((rows.set c rp).set (c + k) rc).mapIdx fun i r =>
      if i = c then pivot else List.zipWith (fun a b => a - r.getD c 0 * b) r pivot)

/-- Solve a square linear system given as augmented rows. -/
def solve (aug : List (List ℚ)) : Option (List ℚ) :=
  ((List.range aug.length).foldlM eliminate aug).map fun rows =>
    rows.map fun r => r.getD aug.length 0

/-- The Lyapunov equation `Aᵀ P + P A = -1` for the entries of `P`, row-major. -/
def lyapunovSystem (A : Matrix (Fin n) (Fin n) ℚ) : List (List ℚ) :=
  (List.finRange n).flatMap fun i => (List.finRange n).map fun j =>
    ((List.finRange n).flatMap fun k => (List.finRange n).map fun l =>
      (if l = j then A k i else 0) + (if k = i then A l j else 0)) ++ [if i = j then -1 else 0]

/-- One column of the factorization `P = L D Lᵀ`. -/
def ldlStep (P : List (List ℚ)) (acc : List (List ℚ) × List ℚ) (j : ℕ) :
    List (List ℚ) × List ℚ :=
  let get (i k : ℕ) : ℚ := (acc.1.getD i []).getD k 0
  let dj := (P.getD j []).getD j 0 -
    ((List.range j).map fun k => get j k * get j k * acc.2.getD k 0).sum
  (acc.1.mapIdx fun i row =>
    if i = j then row.set j 1
    else if j < i then row.set j (((P.getD i []).getD j 0 -
      ((List.range j).map fun k => get i k * get j k * acc.2.getD k 0).sum) / dj)
    else row, acc.2 ++ [dj])

/-- The factorization `P = L D Lᵀ`, as the rows of `L` and the diagonal of `D`. -/
def ldl (P : List (List ℚ)) : List (List ℚ) × List ℚ :=
  (List.range P.length).foldl (ldlStep P)
    (List.replicate P.length (List.replicate P.length 0), [])

/-- A list of rows read as a square matrix. -/
def ofRows (rows : List (List ℚ)) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => (rows.getD i []).getD j 0

/-- The rational data proposed by the synthesizer. -/
structure Witness (n : ℕ) where
  P : Matrix (Fin n) (Fin n) ℚ
  L : Matrix (Fin n) (Fin n) ℚ
  D : Fin n → ℚ

/-- The synthesizer: solve the Lyapunov equation and factor the solution. -/
def synth (A : Matrix (Fin n) (Fin n) ℚ) : Option (Witness n) :=
  (solve (lyapunovSystem A)).map fun sol =>
    let rows := (List.range n).map fun i => (List.range n).map fun j => sol.getD (i * n + j) 0
    let f := ldl rows
    ⟨ofRows rows, ofRows f.1, fun i => f.2.getD i 0⟩

/-! ## The check -/

/-- The exact rational conditions an accepted witness satisfies. -/
def Witness.Valid (A : Matrix (Fin n) (Fin n) ℚ) (w : Witness n) : Prop :=
  (∀ q : Fin n × Fin n, (Aᵀ * w.P + w.P * A) q.1 q.2 = (-1 : Matrix (Fin n) (Fin n) ℚ) q.1 q.2) ∧
    (∀ q : Fin n × Fin n, w.P q.1 q.2 = (w.L * diagonal w.D * w.Lᵀ) q.1 q.2) ∧
    (∀ q : Fin n × Fin n, q.1 < q.2 → w.L q.1 q.2 = 0) ∧ (∀ i, w.L i i = 1) ∧ ∀ i, 0 < w.D i

instance (A : Matrix (Fin n) (Fin n) ℚ) (w : Witness n) : Decidable (w.Valid A) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Run the synthesizer on `A` and check its proposal. -/
def accepts (A : Matrix (Fin n) (Fin n) ℚ) : Bool :=
  match synth A with
  | some w => decide (w.Valid A)
  | none => false

/-! ## Soundness of the check -/

noncomputable section

/-- The real matrix of a rational one. -/
abbrev real (M : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ := M.map (Rat.cast : ℚ → ℝ)

@[powerlib_foundation] theorem real_eq_mapMatrix (M : Matrix (Fin n) (Fin n) ℚ) :
    real M = (Rat.castHom ℝ).mapMatrix M := rfl

@[powerlib_foundation]
theorem Witness.lyapunov_eq {A : Matrix (Fin n) (Fin n) ℚ} {w : Witness n} (h : w.Valid A) :
    Aᵀ * w.P + w.P * A = -1 := by
  ext i j
  exact h.1 (i, j)

@[powerlib_foundation]
theorem Witness.factor_eq {A : Matrix (Fin n) (Fin n) ℚ} {w : Witness n} (h : w.Valid A) :
    w.P = w.L * diagonal w.D * w.Lᵀ := by
  ext i j
  exact h.2.1 (i, j)

/-- An accepted witness is a Lyapunov certificate of the real matrix. -/
def Witness.certificate {A : Matrix (Fin n) (Fin n) ℚ} (w : Witness n)
    (h : w.Valid A) : Certificate (real A) where
  P := real w.P
  symmetric := by
    have hQ : w.Pᵀ = w.P := by
      rw [w.factor_eq h, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.diagonal_transpose, Matrix.mul_assoc]
    rw [real, ← Matrix.transpose_map, hQ]
  positive x hx := by
    have hP : real w.P = real w.L * diagonal (fun i => (w.D i : ℝ)) * (real w.L)ᵀ := by
      rw [real_eq_mapMatrix, w.factor_eq h, map_mul, map_mul, RingHom.mapMatrix_apply,
        RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _),
        Matrix.transpose_map]
      rfl
    set L' := real w.L
    have hlow : L'.IsLowerTriangular := fun i j hij => by
      simp [L', h.2.2.1 (i, j) hij]
    have hdet : L'ᵀ.det = 1 := by
      rw [Matrix.det_transpose, Matrix.det_of_isLowerTriangular L' hlow]
      simp [L', h.2.2.2.1]
    set y := L'ᵀ *ᵥ x
    have hy : y ≠ 0 := by
      intro hy0
      have : ∃ v ≠ 0, L'ᵀ *ᵥ v = 0 := ⟨x, hx, hy0⟩
      rw [Matrix.exists_mulVec_eq_zero_iff, hdet] at this
      exact one_ne_zero this
    have hquad : x ⬝ᵥ (real w.P *ᵥ x) = ∑ i, (w.D i : ℝ) * y i ^ 2 := by
      rw [hP, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose]
      simp only [dotProduct, Matrix.mulVec_diagonal]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hquad]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    exact Finset.sum_pos' (fun j _ => mul_nonneg (by exact_mod_cast (h.2.2.2.2 j).le)
      (sq_nonneg _)) ⟨i, Finset.mem_univ _, mul_pos (by exact_mod_cast h.2.2.2.2 i)
        (by simpa using pow_pos (abs_pos.mpr hi) 2)⟩
  lyapunov := by
    have h1 := congrArg (Rat.castHom ℝ).mapMatrix (w.lyapunov_eq h)
    rw [map_add, map_mul, map_mul, map_neg, map_one] at h1
    simpa [RingHom.mapMatrix_apply, Matrix.transpose_map] using h1

/-- The certificate synthesized for an accepted matrix. -/
def certificateOf (A : Matrix (Fin n) (Fin n) ℚ) (h : accepts A = true) :
    Certificate (real A) :=
  match hs : synth A with
  | some w => w.certificate (by
      have h' : accepts A = decide (w.Valid A) := by
        unfold accepts
        rw [hs]
      rw [h'] at h
      exact of_decide_eq_true h)
  | none => absurd h (by
      unfold accepts
      rw [hs]
      exact Bool.false_ne_true)

/-- A rational matrix accepted by the synthesizer satisfies every attractive sentence. -/
@[powerlib_foundation] theorem holds_of_accepts {A : Matrix (Fin n) (Fin n) ℚ}
    (h : accepts A = true) (e : EuclideanSpace ℝ (Fin n)) {P : Flow.Property}
    (hP : P.Attractive) : P.holds (LinearSystems.affineLinearVectorField (real A) e) e :=
  (certificateOf A h).holds e hP

end

end powerlib.Linear.Synthesis
