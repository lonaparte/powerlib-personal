import theorem.Linear.VerifiedSynthesis

/-! # Synthesis of Lyapunov certificates over the rationals

Only a rational state matrix `A` is submitted. The fast proposal solves the Lyapunov equation
`Aᵀ P + P A = -1` for a symmetric `P` by Gauss–Jordan elimination over `ℚ` and factors
`P = L D Lᵀ`. Its legacy witness checker remains available: `Witness.valid_of_check` and
`Witness.certificate` prove the soundness of the exact equation, factorization, triangularity and
positive-pivot checks. Proposal execution is untrusted; an accepted matrix receives a checked
`Certificate` of its real image, hence every attractive sentence.

Acceptance uses a checked fast solution when available and otherwise a complete rational
full-operator backend, with positive definiteness decided by verified Schur elimination.
`accepts_iff_isHurwitz` proves both directions for every dimension. The LDL proposal remains a
fast candidate; both entry points use the complete backend when it supplies no checked solution.

Scope.
* Generic: square rational matrices of every dimension, read in `ℝ` through `real`; no model.
* There are two ways to run it. `certificateOf A (by decide +kernel)` lets the kernel run both
  the synthesizer and the check. `lyapunov_certificate% A` evaluates the synthesizer during
  elaboration, outside the kernel, writes its proposal out as rational literals, and leaves only
  the check to the kernel; this is the way for larger matrices.

Source: the certificates of `theorem/Linear/Certificate.lean`; the complete verified backend of
`theorem/Linear/VerifiedSynthesis.lean` (`VerifiedSynthesis.check`, `candidate`,
`solutionCheck`); LeanForControl's `IsHurwitz`.

Results.
* The untrusted synthesizer: `eliminate`, `solve`, `pairs`, `lyapunovSystem`, `ldlStep`, `ldl`,
  `ofRows`, `Witness`, `synth`.
* The legacy witness check: `Witness.Valid`, `Witness.check`, `Witness.valid_of_check`,
  `real`, `real_eq_mapMatrix`, `Witness.lyapunov_eq`, `Witness.factor_eq`,
  `Witness.certificate`.
* Acceptance: `selectedMatrix`, `accepts`, `certificateOf`, `accepts_of_isHurwitz` (no Hurwitz
  matrix is lost), `accepts_iff_isHurwitz` (the synthesizer decides the Hurwitz property of every
  finite rational matrix).
* Synthesis during elaboration: `rows`, `ofList`, `synthRows`, `selectedRows`, and the term
  elaborator `lyapunov_certificate%` (a `Certificate (real A)`).
-/

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
      if i = c then pivot else
        let f := r.getD c 0
        if f == 0 then r else List.zipWith (fun a b => a - f * b) r pivot)

/-- Solve a square linear system given as augmented rows. -/
def solve (aug : List (List ℚ)) : Option (List ℚ) :=
  ((List.range aug.length).foldlM eliminate aug).map fun rows =>
    rows.map fun r => r.getD aug.length 0

/-- The upper-triangular index pairs `(i, j)`, `i ≤ j`: the unknowns of a symmetric matrix. -/
def pairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun i => (List.range (n - i)).map fun d => (i, i + d)

/-- The Lyapunov equation `Aᵀ P + P A = -1` for the upper-triangular entries of a symmetric `P`. -/
def lyapunovSystem (A : Matrix (Fin n) (Fin n) ℚ) : List (List ℚ) :=
  let a (k i : ℕ) : ℚ := if h : k < n ∧ i < n then A ⟨k, h.1⟩ ⟨i, h.2⟩ else 0
  let u := pairs n
  u.map fun (i, j) =>
    (u.map fun (p, q) => (List.range n).foldl (fun s k =>
      s + (if (min k j, max k j) = (p, q) then a k i else 0) +
        (if (min i k, max i k) = (p, q) then a k j else 0)) 0) ++ [if i = j then -1 else 0]

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
    let entry (i j : ℕ) : ℚ := (((pairs n).zip sol).lookup (min i j, max i j)).getD 0
    let rows := (List.range n).map fun i => (List.range n).map fun j => entry i j
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

/-- The check as one boolean computation over lists, entry by entry. -/
def Witness.check (A : Matrix (Fin n) (Fin n) ℚ) (w : Witness n) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    ((List.ofFn fun k => A k i * w.P k j + w.P i k * A k j).sum == if i = j then -1 else 0) &&
    (w.P i j == (List.ofFn fun k => w.L i k * w.D k * w.L j k).sum) &&
    (!decide (i < j) || w.L i j == 0) && (!decide (i = j) || (w.L i j == 1 && decide (0 < w.D i)))

/-- Use a fast proposal only when its rational Lyapunov equation is checked. Otherwise the
verified full-operator backend supplies the candidate. Positivity is checked independently of
whether the fast LDL proposal succeeded. -/
def selectedMatrix (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  match synth A with
  | some w => if VerifiedSynthesis.solutionCheck A w.P then w.P else VerifiedSynthesis.candidate A
  | none => VerifiedSynthesis.candidate A

/-- Total verified synthesis. The untrusted proposal accelerates the common case; the complete
backend and exact positivity check determine acceptance. -/
def accepts (A : Matrix (Fin n) (Fin n) ℚ) : Bool :=
  VerifiedSynthesis.check A (selectedMatrix A)

/-! ## Soundness of the check -/

/-- The boolean check establishes the conditions. -/
@[powerlib_foundation] theorem Witness.valid_of_check {A : Matrix (Fin n) (Fin n) ℚ}
    {w : Witness n} (h : w.check A = true) : w.Valid A := by
  simp only [Witness.check, List.all_eq_true, List.mem_finRange, forall_const, Bool.and_eq_true,
    beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    List.sum_ofFn] at h
  refine ⟨fun q => ?_, fun q => ?_, fun q hq => ?_, fun i => ?_, fun i => ?_⟩
  · rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib,
      Matrix.neg_apply, Matrix.one_apply]
    simpa [apply_ite] using (h q.1 q.2).1.1.1
  · rw [Matrix.mul_apply]
    simpa [Matrix.mul_diagonal] using (h q.1 q.2).1.1.2
  · exact ((h q.1 q.2).1.2).resolve_left (not_not.mpr hq)
  · exact (((h i i).2).resolve_left (not_not.mpr rfl)).1
  · exact (((h i i).2).resolve_left (not_not.mpr rfl)).2

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
    Certificate (real A) := VerifiedSynthesis.certificate A (selectedMatrix A) h

/-- Acceptance is complete: an untrusted proposal can affect running time but cannot lose a
Hurwitz matrix, because a checked solution is uniquely the positive upstream solution. -/
@[powerlib_foundation] theorem accepts_of_isHurwitz {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : LinearSystems.IsHurwitz (real A)) : accepts A = true := by
  unfold accepts selectedMatrix
  cases hs : synth A with
  | none => exact VerifiedSynthesis.candidate_checked hA
  | some w =>
    by_cases h : VerifiedSynthesis.solutionCheck A w.P = true
    · simp only [h, ↓reduceIte]
      exact VerifiedSynthesis.check_of_solution hA
        (by simpa [VerifiedSynthesis.solutionCheck] using h)
    · have hf : VerifiedSynthesis.solutionCheck A w.P = false := Bool.eq_false_iff.mpr h
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
      exact VerifiedSynthesis.candidate_checked hA

/-- The executable synthesizer decides the Hurwitz property of every finite rational matrix. -/
@[powerlib_foundation] theorem accepts_iff_isHurwitz (A : Matrix (Fin n) (Fin n) ℚ) :
    accepts A = true ↔ LinearSystems.IsHurwitz (real A) :=
  ⟨fun h => (certificateOf A h).isHurwitz, accepts_of_isHurwitz⟩

/-- A rational matrix accepted by the synthesizer satisfies every attractive sentence. -/
@[powerlib_foundation] private theorem holds_of_accepts {A : Matrix (Fin n) (Fin n) ℚ}
    (h : accepts A = true) (e : EuclideanSpace ℝ (Fin n)) {P : Flow.Property}
    (hP : P.Attractive) : P.holds (LinearSystems.affineLinearVectorField (real A) e) e :=
  (certificateOf A h).holds e hP

end

/-! ## Synthesis during elaboration -/

/-- The rows of a square matrix. -/
def rows (M : Matrix (Fin n) (Fin n) ℚ) : List (List ℚ) :=
  (List.finRange n).map fun i => (List.finRange n).map fun j => M i j

/-- A list read as a vector. -/
def ofList (l : List ℚ) : Fin n → ℚ := fun i => l.getD i 0

/-- The synthesizer's proposal as lists of rationals. -/
def synthRows (A : Matrix (Fin n) (Fin n) ℚ) :
    Option (List (List ℚ) × List (List ℚ) × List ℚ) :=
  (synth A).map fun w => (rows w.P, rows w.L, (List.finRange n).map w.D)

/-- The selected complete-backend candidate serialized for kernel verification. -/
def selectedRows (A : Matrix (Fin n) (Fin n) ℚ) : List (List ℚ) := rows (selectedMatrix A)

open Lean Elab Term Meta in
/-- `lyapunov_certificate% A` evaluates the synthesizer on the rational matrix `A` during
elaboration, outside the kernel, writes its proposal out as rational literals, and leaves the check
of the proposal to the kernel alone (`decide +kernel`). It elaborates to a `Certificate (real A)`.
-/
elab "lyapunov_certificate% " a:term:max : term => do
  let A ← instantiateMVars (← elabTerm a none)
  synthesizeSyntheticMVarsNoPostponing
  let ty ← whnfR (← inferType A)
  let_expr Matrix fin _ _ := ty | throwError "expected a square rational matrix, got {ty}"
  let_expr Fin dim := fin | throwError "expected a square rational matrix, got {ty}"
  let P ← unsafe evalExpr (List (List ℚ)) (toTypeExpr (List (List ℚ)))
    (mkApp2 (.const ``selectedRows []) dim A)
  let p := mkApp2 (.const ``ofRows []) dim (toExpr P)
  let h ← elabTermEnsuringType (← `(by decide +kernel))
    (← mkEq (mkApp3 (.const ``VerifiedSynthesis.check []) dim A p) (toExpr true))
  synthesizeSyntheticMVarsNoPostponing
  return mkApp4 (.const ``VerifiedSynthesis.certificate []) dim A p (← instantiateMVars h)

end powerlib.Linear.Synthesis
