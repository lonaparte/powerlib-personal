import theorem.Criteria.RouthHurwitz

/-! # The Routh–Hurwitz criterion in table form, every degree (foundation)

The first column of the Routh table, computed from the coefficient list of a polynomial, decides
whether every complex root has negative real part: for a real polynomial with positive leading
coefficient, the polynomial is Hurwitz iff every entry of the first column is positive. The table
is defined over any field, so at rational data it is a finite computation checked by the kernel
(`decide +kernel` after `hurwitz_ofList_rat_iff`).

Scope.
* Static algebra of one real polynomial `p : ℝ[X]`, of a coefficient list `[a_n, …, a_0]`
  (leading coefficient first) and of a real square matrix through its characteristic
  polynomial. No model family is defined; every degree.

Source: E. J. Routh, *A Treatise on the Stability of a Given State of Motion* (1877), the table;
F. R. Gantmacher, *The Theory of Matrices*, vol. 2, Ch. XV §§6–7; the reduction step is
`theorem/Criteria/RouthHurwitz.lean` (shared criteria interface for the work-sync formalization).

Results.
* Coefficients of the Routh step: `coeff_comp_neg_X`, `coeff_altPart` (the coefficients of parity
  `n − 1`), `coeff_routhStep_zero`, `coeff_routhStep_succ`; for `deg p = n + 1` and
  `a_n ≠ 0`, `natDegree_routhStep` (`= n`) and `leadingCoeff_routhStep` (`= a_n`).
* The table over a field `K`: `coeffList p = [a_n, …, a_0]`; `routhListStep` (one row of the
  table, `bⱼ = a_{j+1} − (a₀/a₁)·[j odd]·a_{j+2}` in list positions); `routhColumn m l`, the first
  column `[l₀, (routhListStep l)₀, …]` (`m + 1` entries); `coeffList_routhStep`: the coefficient
  list of `routhStep p` is `routhListStep (coeffList p)`.
* **Criterion** (`hurwitz_iff_routhColumn`): for `p : ℝ[X]` with `a_n > 0`, every complex root has
  negative real part iff every entry of `routhColumn n (coeffList p)` is positive.
* Lists as polynomials: `ofList [a_n, …, a_0] = ∑ aᵢ X^{n−i}` (`coeff_ofList`,
  `natDegree_ofList`, `leadingCoeff_ofList`, `coeffList_ofList`); `hurwitz_ofList_iff`.
* Rational data: `routhListStep_map`, `routhColumn_map` (the table commutes with field
  homomorphisms) and `hurwitz_ofList_rat_iff`: for a rational list the criterion is the rational
  table, a decidable statement.
* Matrices: `spectrallyStable_iff_routhColumn` (any finite index: spectral stability iff the
  table of `A.charpoly` is positive), `isHurwitz_iff_routhColumn` (`Fin n`, `IsHurwitz`) and
  `isHurwitz_iff_routhColumn_of_det` (through any coefficient list whose polynomial evaluates to
  the characteristic determinant).
* Checks: `routhColumn_example_stable` (`s³ + 2 s² + 3 s + 1`, the table `[1, 2, 5/2, 1]`),
  `routhColumn_example_unstable` (`s³ + s² + s + 2`).

Family and connection conclusions.
* None: static algebra. Model families read the criterion through their characteristic
  polynomials.
-/

noncomputable section
namespace powerlib.Criteria
open Polynomial

/-! ## Coefficients of the Routh step -/

section Coefficients

@[tmio T, powerlib_foundation] theorem coeff_comp_neg_X {R : Type*} [CommRing R] (p : R[X])
    (k : ℕ) : (p.comp (-X)).coeff k = (-1) ^ k * p.coeff k := by
  rw [show (-X : R[X]) = C (-1) * X by simp, comp_C_mul_X_coeff, mul_comm]

/-- The coefficients of `altPart p` are those of `p` of parity `n − 1`. -/
@[tmio T, powerlib_foundation] theorem coeff_altPart (p : ℝ[X]) (k : ℕ) :
    (altPart p).coeff k = if (p.natDegree + k) % 2 = 1 then p.coeff k else 0 := by
  rw [altPart, coeff_C_mul, coeff_sub, coeff_C_mul, coeff_comp_neg_X, ← mul_assoc, ← pow_add]
  rcases Nat.even_or_odd (p.natDegree + k) with h | h
  · rw [h.neg_one_pow, ite_eq_right (by rw [Nat.even_iff.mp h]; norm_num)]; ring
  · rw [h.neg_one_pow, ite_eq_left (Nat.odd_iff.mp h)]; ring

@[tmio T, powerlib_foundation] theorem coeff_routhStep_zero (p : ℝ[X]) :
    (routhStep p).coeff 0 = p.coeff 0 := by
  rw [routhStep, coeff_sub, mul_assoc, coeff_C_mul, coeff_X_mul_zero, mul_zero, sub_zero]

@[tmio T, powerlib_foundation] theorem coeff_routhStep_succ (p : ℝ[X]) (k : ℕ) :
    (routhStep p).coeff (k + 1) = p.coeff (k + 1) - p.leadingCoeff / p.nextCoeff *
      (if (p.natDegree + k) % 2 = 1 then p.coeff k else 0) := by
  rw [routhStep, coeff_sub, mul_assoc, coeff_C_mul, coeff_X_mul, coeff_altPart]

variable {p : ℝ[X]} {n : ℕ}

@[tmio T, powerlib_foundation] private theorem coeff_routhStep_of_lt (hn : p.natDegree = n + 1)
    (hb : p.nextCoeff ≠ 0) {k : ℕ} (hk : n < k) : (routhStep p).coeff k = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [coeff_routhStep_succ]
  rcases Nat.lt_or_ge j (n + 1) with hj | hj
  · have hjn : j = n := by omega
    subst hjn
    have hnc : p.nextCoeff = p.coeff j := by
      rw [nextCoeff_of_natDegree_pos (by omega), hn, Nat.add_sub_cancel]
    rw [hn, ite_eq_left (by omega), ← hnc, leadingCoeff, hn]
    field_simp
    ring
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < j + 1)]
    by_cases hj' : j = n + 1
    · subst hj'
      rw [hn, ite_eq_right (by omega)]; ring
    · rw [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < j)]; simp

@[tmio T, powerlib_foundation] private theorem coeff_routhStep_self (hn : p.natDegree = n + 1) :
    (routhStep p).coeff n = p.coeff n := by
  rcases n with _ | m
  · exact coeff_routhStep_zero p
  · rw [coeff_routhStep_succ, hn, ite_eq_right (by omega), mul_zero, sub_zero]

@[tmio T, powerlib_foundation] theorem natDegree_routhStep (hn : p.natDegree = n + 1)
    (hb : p.nextCoeff ≠ 0) : (routhStep p).natDegree = n := by
  have hnc : p.nextCoeff = p.coeff n := by
    rw [nextCoeff_of_natDegree_pos (by omega), hn, Nat.add_sub_cancel]
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ (by rw [coeff_routhStep_self hn, ← hnc]; exact hb)
  exact natDegree_le_iff_coeff_eq_zero.mpr fun k hk =>
    coeff_routhStep_of_lt hn hb (by exact_mod_cast hk)

@[tmio T, powerlib_foundation] theorem leadingCoeff_routhStep (hn : p.natDegree = n + 1)
    (hb : p.nextCoeff ≠ 0) : (routhStep p).leadingCoeff = p.nextCoeff := by
  rw [leadingCoeff, natDegree_routhStep hn hb, coeff_routhStep_self hn,
    nextCoeff_of_natDegree_pos (by omega), hn, Nat.add_sub_cancel]

end Coefficients

/-! ## The Routh table -/

section Table

variable {K : Type*} [Field K]

/-- The coefficient list `[a_n, a_{n−1}, …, a_0]` of `p`, leading coefficient first. -/
def coeffList {R : Type*} [Semiring R] (p : R[X]) : List R :=
  (List.range (p.natDegree + 1)).map fun j => p.coeff (p.natDegree - j)

/-- One Routh step on a coefficient list `[a₀', a₁', …]` (leading first): the list of length one
less with entries `a_{j+1}' − (a₀'/a₁')·[j odd]·a_{j+2}'`. -/
def routhListStep (l : List K) : List K :=
  (List.range (l.length - 1)).map fun j =>
    l.getD (j + 1) 0 - l.getD 0 0 / l.getD 1 0 * if j % 2 = 1 then l.getD (j + 2) 0 else 0

/-- The first column of the Routh table of a coefficient list of length `m + 1`. -/
def routhColumn : ℕ → List K → List K
  | 0, l => [l.getD 0 0]
  | m + 1, l => l.getD 0 0 :: routhColumn m (routhListStep l)

@[tmio T, powerlib_foundation] private theorem getD_eq_getElem' {α : Type*} (l : List α) {i : ℕ}
    (h : i < l.length) (d : α) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

@[tmio T, powerlib_foundation] private theorem getD_map' {α β : Type*} (l : List α) (f : α → β)
    (i : ℕ) (d : α) : (l.map f).getD i (f d) = f (l.getD i d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map]

@[tmio T, powerlib_foundation] private theorem getD_map_range {α : Type*} (N i : ℕ) (f : ℕ → α)
    (d : α) : ((List.range N).map f).getD i d = if i < N then f i else d := by
  by_cases h : i < N
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

@[tmio T, powerlib_foundation] theorem length_coeffList {R : Type*} [Semiring R] (p : R[X]) :
    (coeffList p).length = p.natDegree + 1 := by
  simp [coeffList]

@[tmio T, powerlib_foundation] theorem length_routhListStep (l : List K) :
    (routhListStep l).length = l.length - 1 := by
  simp [routhListStep]

@[tmio T, powerlib_foundation] theorem routhColumn_cons (m : ℕ) (l : List K) :
    ∃ t, routhColumn m l = l.getD 0 0 :: t := by
  cases m <;> exact ⟨_, rfl⟩

@[tmio T, powerlib_foundation] theorem routhListStep_getD_zero {l : List K}
    (hl : 2 ≤ l.length) : (routhListStep l).getD 0 0 = l.getD 1 0 := by
  rw [routhListStep, getD_map_range, ite_eq_left (by omega)]
  simp

/-- **The table is the Routh step**: the coefficient list of `routhStep p` is one row step of the
coefficient list of `p` (`deg p = n + 1`, `a_n ≠ 0`). -/
@[tmio T, powerlib_foundation] theorem coeffList_routhStep {p : ℝ[X]} {n : ℕ}
    (hn : p.natDegree = n + 1) (hb : p.nextCoeff ≠ 0) :
    coeffList (routhStep p) = routhListStep (coeffList p) := by
  have hq := natDegree_routhStep hn hb
  have hnc : p.nextCoeff = p.coeff n := by
    rw [nextCoeff_of_natDegree_pos (by omega), hn, Nat.add_sub_cancel]
  have hlc : p.leadingCoeff = p.coeff (n + 1) := by rw [leadingCoeff, hn]
  apply List.ext_getElem
  · rw [length_routhListStep, length_coeffList, length_coeffList, hq, hn]; rfl
  · intro j h1 h2
    rw [length_coeffList, hq] at h1
    have hg : ∀ i, (coeffList p).getD i 0 = if i < n + 2 then p.coeff (n + 1 - i) else 0 := by
      intro i; rw [coeffList, getD_map_range, hn]
    rw [← getD_eq_getElem' _ _ (0 : ℝ), ← getD_eq_getElem' _ _ (0 : ℝ), routhListStep,
      getD_map_range, ite_eq_left (by rw [length_coeffList, hn]; omega), hg, hg, hg, hg,
      ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega), coeffList,
      getD_map_range, ite_eq_left (by omega), hq]
    simp only [Nat.sub_zero, show n + 1 - 1 = n by omega, show n + 1 - (j + 1) = n - j by omega]
    rcases Nat.lt_or_ge j n with hj | hj
    · obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by omega⟩
      rw [hk, coeff_routhStep_succ, hn, hlc, hnc]
      by_cases hpar : j % 2 = 1
      · rw [ite_eq_left (by omega), ite_eq_left hpar, ite_eq_left (by omega),
          show n + 1 - (j + 2) = k by omega]
      · rw [ite_eq_right (by omega), ite_eq_right hpar]
    · have hjn : j = n := by omega
      subst hjn
      rw [Nat.sub_self, coeff_routhStep_zero]
      split_ifs <;> first | (exfalso; omega) | simp

/-- **Routh–Hurwitz criterion, every degree.** For `p : ℝ[X]` with positive leading
coefficient, every complex root has negative real part iff every entry of the first column of the
Routh table of its coefficient list is positive. -/
@[tmio T, powerlib_foundation] theorem hurwitz_iff_routhColumn {p : ℝ[X]}
    (hp : 0 < p.leadingCoeff) :
    (∀ s : ℂ, aeval s p = 0 → s.re < 0) ↔ ∀ c ∈ routhColumn p.natDegree (coeffList p), 0 < c := by
  induction hn : p.natDegree generalizing p with
  | zero =>
    have hpC : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hn
    have hc0 : p.coeff 0 = p.leadingCoeff := by rw [leadingCoeff, hn]
    have hl : (coeffList p).getD 0 0 = p.leadingCoeff := by
      rw [coeffList, getD_map_range, ite_eq_left (by omega), hn, hc0]
    simp only [routhColumn, hl, List.mem_singleton, forall_eq, hp, iff_true]
    intro s hs
    rw [hpC, aeval_C, hc0] at hs
    exact absurd (by simpa using hs : p.leadingCoeff = 0) hp.ne'
  | succ n ih =>
    rw [hurwitz_iff_routhStep (by omega) hp, routhColumn]
    have hl0 : (coeffList p).getD 0 0 = p.leadingCoeff := by
      rw [coeffList, getD_map_range, ite_eq_left (by omega), hn, Nat.sub_zero, leadingCoeff, hn]
    simp only [List.mem_cons, forall_eq_or_imp, hl0, hp, true_and]
    by_cases hb : 0 < p.nextCoeff
    · have hq := natDegree_routhStep hn hb.ne'
      have hlq := leadingCoeff_routhStep hn hb.ne'
      rw [← coeffList_routhStep hn hb.ne', ← ih (by rw [hlq]; exact hb) hq]
      simp [hb]
    · simp only [hb, false_and, false_iff]
      intro h
      obtain ⟨t, ht⟩ := routhColumn_cons n (routhListStep (coeffList p))
      have h0 := h _ (by rw [ht]; exact List.mem_cons_self)
      rw [routhListStep_getD_zero (by rw [length_coeffList]; omega),
        coeffList, getD_map_range, ite_eq_left (by omega), hn,
        show n + 1 - 1 = n by omega] at h0
      rw [nextCoeff_of_natDegree_pos (by omega), hn, show n + 1 - 1 = n by omega] at hb
      exact hb h0

end Table

/-! ## Lists as polynomials, rational data -/

section Lists

/-- The polynomial `a_n Xⁿ + … + a_0` of the coefficient list `[a_n, …, a_0]`. -/
def ofList {R : Type*} [Semiring R] : List R → R[X]
  | [] => 0
  | a :: l => C a * X ^ l.length + ofList l

@[tmio T, powerlib_foundation] theorem coeff_ofList {R : Type*} [Semiring R] (l : List R)
    (k : ℕ) : (ofList l).coeff k = if k < l.length then l.getD (l.length - 1 - k) 0 else 0 := by
  induction l with
  | nil => simp [ofList]
  | cons a l ih =>
    rw [ofList, coeff_add, coeff_C_mul_X_pow, ih, List.length_cons]
    by_cases hk : k = l.length
    · subst hk; simp
    · rcases Nat.lt_or_ge k l.length with h | h
      · rw [ite_eq_right hk, ite_eq_left h, ite_eq_left (by omega), zero_add,
          show l.length + 1 - 1 - k = (l.length - 1 - k) + 1 by omega, List.getD_cons_succ]
      · rw [ite_eq_right hk, ite_eq_right (by omega), ite_eq_right (by omega)]; simp

@[tmio T, powerlib_foundation] theorem natDegree_ofList {R : Type*} [Semiring R] {a : R}
    (ha : a ≠ 0) (l : List R) : (ofList (a :: l)).natDegree = l.length := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ (by simp [coeff_ofList, ha])
  refine natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
  rw [coeff_ofList, ite_eq_right (by simp; exact_mod_cast hk)]

@[tmio T, powerlib_foundation] theorem leadingCoeff_ofList {R : Type*} [Semiring R] {a : R}
    (ha : a ≠ 0) (l : List R) : (ofList (a :: l)).leadingCoeff = a := by
  rw [leadingCoeff, natDegree_ofList ha, coeff_ofList]
  simp

@[tmio T, powerlib_foundation] theorem coeffList_ofList {R : Type*} [Semiring R] {a : R}
    (ha : a ≠ 0) (l : List R) : coeffList (ofList (a :: l)) = a :: l := by
  apply List.ext_getElem
  · rw [length_coeffList, natDegree_ofList ha]; rfl
  · intro j h1 h2
    have h1' := h1
    rw [length_coeffList, natDegree_ofList ha] at h1'
    rw [← getD_eq_getElem' _ h1 (0 : R), ← getD_eq_getElem' _ h2 (0 : R), coeffList,
      natDegree_ofList ha, getD_map_range, ite_eq_left h1', coeff_ofList,
      ite_eq_left (by simp only [List.length_cons]; omega), List.length_cons,
      show l.length + 1 - 1 - (l.length - j) = j by omega]

/-- **Criterion for a coefficient list.** For `a > 0`, `ofList (a :: l)` is Hurwitz iff the first
column of the Routh table of `a :: l` is positive. -/
@[tmio T, powerlib_foundation] theorem hurwitz_ofList_iff {a : ℝ} (ha : 0 < a) (l : List ℝ) :
    (∀ s : ℂ, aeval s (ofList (a :: l)) = 0 → s.re < 0) ↔
      ∀ c ∈ routhColumn l.length (a :: l), 0 < c := by
  rw [hurwitz_iff_routhColumn (by rw [leadingCoeff_ofList ha.ne']; exact ha),
    natDegree_ofList ha.ne', coeffList_ofList ha.ne']

variable {K L : Type*} [Field K] [Field L]

@[tmio T, powerlib_foundation] theorem routhListStep_map (φ : K →+* L) (l : List K) :
    routhListStep (l.map φ) = (routhListStep l).map φ := by
  simp only [routhListStep, List.length_map, List.map_map]
  congr 1
  funext j
  have hg : ∀ i, (l.map φ).getD i 0 = φ (l.getD i 0) := fun i => by
    rw [← map_zero φ, getD_map']
  simp only [Function.comp_apply, hg, map_sub, map_mul, map_div₀, apply_ite φ, map_zero]

@[tmio T, powerlib_foundation] theorem routhColumn_map (φ : K →+* L) (m : ℕ) (l : List K) :
    routhColumn m (l.map φ) = (routhColumn m l).map φ := by
  induction m generalizing l with
  | zero => rw [routhColumn, routhColumn, ← map_zero φ, getD_map']; rfl
  | succ m ih =>
    rw [routhColumn, routhColumn, routhListStep_map, ih, List.map_cons, ← map_zero φ,
      getD_map']

/-- **Rational data.** For a rational coefficient list with positive leading coefficient, the
real polynomial is Hurwitz iff the rational Routh table is positive (a decidable statement). -/
@[tmio T, powerlib_foundation] theorem hurwitz_ofList_rat_iff {a : ℚ} (ha : 0 < a) (l : List ℚ) :
    (∀ s : ℂ, aeval s (ofList (((a :: l).map (Rat.castHom ℝ)))) = 0 → s.re < 0) ↔
      ∀ c ∈ routhColumn l.length (a :: l), 0 < c := by
  rw [List.map_cons, hurwitz_ofList_iff (by simpa using ha), ← List.map_cons, List.length_map,
    routhColumn_map]
  simp

end Lists

/-! ## Matrices -/

section Matrix

variable {n : ℕ}

/-- **Routh–Hurwitz for matrices, any finite index.** A real square matrix is spectrally stable
iff the first column of the Routh table of its characteristic polynomial is positive. -/
@[tmio T, powerlib_foundation] theorem spectrallyStable_iff_routhColumn {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι ℝ) :
    Linear.SpectrallyStable A ↔
      ∀ c ∈ routhColumn (Fintype.card ι) (coeffList A.charpoly), 0 < c := by
  have h : ∀ s, (Linear.characteristicMatrix A s).det = aeval s A.charpoly := fun s => by
    rw [Linear.det_characteristicMatrix_eq_eval, Linear.complexify, Matrix.charpoly_map,
      eval_map_algebraMap]
  unfold Linear.SpectrallyStable
  simp only [h]
  rw [hurwitz_iff_routhColumn (by rw [A.charpoly_monic.leadingCoeff]; exact one_pos),
    Matrix.charpoly_natDegree_eq_dim]

/-- **Routh–Hurwitz for matrices, any dimension.** A real square matrix is Hurwitz iff the first
column of the Routh table of its characteristic polynomial is positive. -/
@[tmio T, powerlib_foundation] theorem isHurwitz_iff_routhColumn (A : Matrix (Fin n) (Fin n) ℝ) :
    LinearSystems.IsHurwitz A ↔ ∀ c ∈ routhColumn n (coeffList A.charpoly), 0 < c := by
  rw [← Linear.spectrallyStable_iff_isHurwitz, spectrallyStable_iff_routhColumn, Fintype.card_fin]

/-- The same through a coefficient list whose polynomial is the characteristic determinant. -/
@[tmio T, powerlib_foundation] theorem isHurwitz_iff_routhColumn_of_det
    (A : Matrix (Fin n) (Fin n) ℝ) {a : ℝ} (ha : 0 < a) (l : List ℝ)
    (h : ∀ s : ℂ, (Linear.characteristicMatrix A s).det = aeval s (ofList (a :: l))) :
    LinearSystems.IsHurwitz A ↔ ∀ c ∈ routhColumn l.length (a :: l), 0 < c := by
  rw [isHurwitz_iff_of_det_characteristicMatrix A (q := fun s => aeval s (ofList (a :: l)))
    (fun s => by rw [h]), hurwitz_ofList_iff ha]

end Matrix

/-! ## Checks -/

/-- `s³ + 2 s² + 3 s + 1` is Hurwitz: its Routh column is `[1, 2, 5/2, 1]`. -/
@[tmio T, powerlib_foundation] theorem routhColumn_example_stable :
    ∀ s : ℂ, s ^ 3 + 2 * s ^ 2 + 3 * s + 1 = 0 → s.re < 0 := by
  have h := (hurwitz_ofList_rat_iff (a := 1) (by norm_num) [2, 3, 1]).mpr (by decide +kernel)
  intro s hs
  exact h s (by simp [ofList]; linear_combination hs)

/-- `s³ + s² + s + 2` is not Hurwitz: its Routh column is `[1, 1, −1, 2]`. -/
@[tmio T, powerlib_foundation] theorem routhColumn_example_unstable :
    ¬ ∀ s : ℂ, s ^ 3 + s ^ 2 + s + 2 = 0 → s.re < 0 := by
  have h := (hurwitz_ofList_rat_iff (a := 1) (by norm_num) [1, 1, 2]).not.mpr (by decide +kernel)
  intro hs
  exact h fun s h0 => hs s (by simp [ofList] at h0; linear_combination h0)

end powerlib.Criteria
