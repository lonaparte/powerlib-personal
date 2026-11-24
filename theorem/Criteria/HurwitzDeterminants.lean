import theorem.Criteria.RouthTable

/-! # The Hurwitz determinants in every degree (foundation)

The Routh step is a row elimination of the Hurwitz matrix: subtracting `a_n/a_{n−1}` times each
odd-numbered row from the row below it leaves the first column `(a_{n−1}, 0, …, 0)` and, below
and to the right, the Hurwitz matrix of the Routh-reduced polynomial. So the leading principal
minors satisfy `Δ_{k+1}(p) = a_{n−1} Δ_k(routhStep p)`, the Routh column entries are
`c_k = Δ_k/Δ_{k−1}`, and a real polynomial with positive leading coefficient is Hurwitz iff
`Δ₁, …, Δ_n > 0`.

Scope.
* Static algebra of one real polynomial `p : ℝ[X]` of degree `n` and of real square matrices
  through their characteristic polynomials; every degree. No model family is defined.

Source: A. Hurwitz, *Math. Ann.* 46 (1895) 273–284 (the determinant criterion); F. R.
Gantmacher, *The Theory of Matrices*, vol. 2, Ch. XV §6 (the Routh column as ratios of Hurwitz
determinants, by Gauss elimination of the Hurwitz matrix); the Routh step
`theorem/Criteria/RouthHurwitz.lean` (shared criteria interface for the work-sync
formalization).

Results.
* `hurwitzCoeff p m` (`a_m` at an integer index, `0` for `m < 0`), `hurwitzMinor p k` (the
  leading `k × k` block of the Hurwitz matrix, entry `(i, j) = a_{n + i − 2j − 1}`, rows
  `a_{n−1}, a_{n−3}, …` / `a_n, a_{n−2}, …` / `0, a_{n−1}, …`) and `hurwitzDet p k = Δ_k`;
  `hurwitzDet_zero` (`Δ₀ = 1`), `hurwitzDet_one` (`Δ₁ = a_{n−1}`).
* `hurwitzCoeff_routhStep`: the coefficients of the Routh step at integer indices.
* **The elimination** (`hurwitzDet_succ_routhStep`): for `deg p = n + 1` and `a_n ≠ 0`,
  `Δ_{k+1}(p) = a_n Δ_k(routhStep p)` for every `k`.
* `hurwitzDet_eq_prod`: `Δ_k = c_1 c_2 ⋯ c_k` with `c_{j+1}` the next coefficient of the `j`-th
  Routh iterate (when the earlier ones do not vanish); `nextCoeff_iterate_routhStep_eq_div`:
  `c_{k+1} = Δ_{k+1}/Δ_k`.
* **Criterion** (`hurwitz_iff_hurwitzDet`): for `a_n > 0`, every complex root has negative real
  part iff `Δ_k > 0` for `1 ≤ k ≤ n`. Matrices: `spectrallyStable_iff_hurwitzDet` (any finite
  index) and `isHurwitz_iff_hurwitzDet` (`Fin n`).

Family and connection conclusions.
* None: static algebra.
-/

noncomputable section
namespace powerlib.Criteria
open Polynomial

/-! ## The Hurwitz matrix -/

section Minors

/-- The coefficient `a_m` of `p` at an integer index (`0` for `m < 0`). -/
def hurwitzCoeff (p : ℝ[X]) (m : ℤ) : ℝ := if 0 ≤ m then p.coeff m.toNat else 0

/-- The leading `k × k` block of the Hurwitz matrix of `p` (`n = natDegree p`): entry `(i, j)` is
`a_{n + i − 2j − 1}`. -/
def hurwitzMinor (p : ℝ[X]) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => hurwitzCoeff p ((p.natDegree : ℤ) + (i : ℕ) - 2 * (j : ℕ) - 1)

/-- The Hurwitz determinant `Δ_k`: the leading `k × k` principal minor of the Hurwitz matrix. -/
def hurwitzDet (p : ℝ[X]) (k : ℕ) : ℝ := (hurwitzMinor p k).det

variable {p : ℝ[X]}

@[tmio T, powerlib_foundation] private theorem hurwitzCoeff_of_eq {m : ℤ} {k : ℕ}
    (h : m = k) : hurwitzCoeff p m = p.coeff k := by
  rw [hurwitzCoeff, ite_eq_left (by omega)]
  congr 1
  omega

@[tmio T, powerlib_foundation] private theorem hurwitzCoeff_of_neg {m : ℤ} (h : m < 0) :
    hurwitzCoeff p m = 0 := by
  rw [hurwitzCoeff, ite_eq_right (by omega)]

@[tmio T, powerlib_foundation] theorem hurwitzDet_zero (p : ℝ[X]) : hurwitzDet p 0 = 1 :=
  Matrix.det_isEmpty

@[tmio T, powerlib_foundation] theorem hurwitzDet_one (hn : 0 < p.natDegree) :
    hurwitzDet p 1 = p.nextCoeff := by
  rw [hurwitzDet, Matrix.det_unique, nextCoeff_of_natDegree_pos hn]
  exact hurwitzCoeff_of_eq (by simp; omega)

/-- The coefficients of the Routh step at integer indices:
`b_m = a_m − (a_n/a_{n−1}) [m ≡ n (mod 2)] a_{m−1}`. -/
@[tmio T, powerlib_foundation] theorem hurwitzCoeff_routhStep (p : ℝ[X]) (m : ℤ) :
    hurwitzCoeff (routhStep p) m = hurwitzCoeff p m - p.leadingCoeff / p.nextCoeff *
      (if (m - p.natDegree) % 2 = 0 then hurwitzCoeff p (m - 1) else 0) := by
  rcases lt_or_ge m 0 with hm | hm
  · rw [hurwitzCoeff_of_neg hm, hurwitzCoeff_of_neg hm, hurwitzCoeff_of_neg (by omega)]
    simp
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rcases k with _ | k
    · rw [hurwitzCoeff_of_eq rfl, hurwitzCoeff_of_eq rfl, hurwitzCoeff_of_neg (by omega),
        coeff_routhStep_zero]
      simp
    · rw [hurwitzCoeff_of_eq rfl, hurwitzCoeff_of_eq rfl, coeff_routhStep_succ,
        hurwitzCoeff_of_eq (k := k) (by push_cast; ring)]
      by_cases h : (p.natDegree + k) % 2 = 1
      · rw [ite_eq_left h, ite_eq_left (by push_cast; omega)]
      · rw [ite_eq_right h, ite_eq_right (by push_cast; omega)]

end Minors

/-! ## The Routh step as a row elimination -/

section Elimination

variable {p : ℝ[X]} {n : ℕ}

/-- **The Routh step is a row elimination of the Hurwitz matrix**: for `deg p = n + 1` and
`a_n ≠ 0`, `Δ_{k+1}(p) = a_n Δ_k(routhStep p)` for every `k`. -/
@[tmio T, powerlib_foundation] theorem hurwitzDet_succ_routhStep (hn : p.natDegree = n + 1)
    (hb : p.nextCoeff ≠ 0) (k : ℕ) :
    hurwitzDet p (k + 1) = p.nextCoeff * hurwitzDet (routhStep p) k := by
  set μ := p.leadingCoeff / p.nextCoeff with hμ
  have hq := natDegree_routhStep hn hb
  have hnc : p.nextCoeff = p.coeff n := by
    rw [nextCoeff_of_natDegree_pos (by omega), hn, Nat.add_sub_cancel]
  have hlc : p.leadingCoeff = p.coeff (n + 1) := by rw [leadingCoeff, hn]
  -- the elimination matrix: unit lower bidiagonal, `−μ` below each odd-numbered row
  set L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ := Matrix.of fun i c =>
    if i = c then 1 else if (c : ℕ) + 1 = i ∧ (i : ℕ) % 2 = 1 then -μ else 0 with hLdef
  have hL : L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular L]
    · simp [hLdef]
    · intro i j hij
      have hij' : i < j := hij
      simp only [hLdef, Matrix.of_apply]
      rw [ite_eq_right (ne_of_lt hij'), ite_eq_right]
      intro h
      have := Fin.lt_def.mp hij'
      omega
  set E := L * hurwitzMinor p (k + 1) with hEdef
  have hE : ∀ i j, E i j = hurwitzCoeff p ((p.natDegree : ℤ) + (i : ℕ) - 2 * (j : ℕ) - 1) -
      (if (i : ℕ) % 2 = 1 then
        μ * hurwitzCoeff p ((p.natDegree : ℤ) + (i : ℕ) - 2 * (j : ℕ) - 2) else 0) := by
    intro i j
    have hsplit : ∀ c, L i c = (if i = c then 1 else 0) +
        (if (c : ℕ) + 1 = i ∧ (i : ℕ) % 2 = 1 then -μ else 0) := by
      intro c
      simp only [hLdef, Matrix.of_apply]
      by_cases hic : i = c
      · subst hic; simp
      · simp [hic]
    rw [hEdef, Matrix.mul_apply]
    simp only [hsplit, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [hurwitzMinor, Matrix.of_apply]
    by_cases hodd : (i : ℕ) % 2 = 1
    · have hi1 : 1 ≤ (i : ℕ) := by omega
      set c0 : Fin (k + 1) := ⟨(i : ℕ) - 1, by omega⟩
      rw [Finset.sum_eq_single c0]
      · rw [ite_eq_left ⟨by simp [c0]; omega, hodd⟩, ite_eq_left hodd]
        have e : (p.natDegree : ℤ) + ((c0 : ℕ) : ℤ) - 2 * (j : ℕ) - 1 =
            (p.natDegree : ℤ) + (i : ℕ) - 2 * (j : ℕ) - 2 := by simp [c0]; omega
        rw [e]; ring
      · intro c _ hc
        rw [ite_eq_right]
        rintro ⟨h1, -⟩
        exact hc (Fin.ext (by simp [c0]; omega))
      · simp
    · rw [Finset.sum_eq_zero (fun c _ => by rw [ite_eq_right (fun h => hodd h.2)]),
        ite_eq_right hodd]
      ring
  have hdet : hurwitzDet p (k + 1) = E.det := by
    rw [hurwitzDet, hEdef, Matrix.det_mul, hL, one_mul]
  have hcol : ∀ i : Fin k, E i.succ 0 = 0 := by
    intro i
    rw [hE]
    simp only [Fin.val_succ, Fin.val_zero, hn]
    rcases Nat.eq_zero_or_pos (i : ℕ) with hi | hi
    · rw [hi, ite_eq_left (by norm_num), hurwitzCoeff_of_eq (k := n + 1) (by push_cast; ring),
        hurwitzCoeff_of_eq (k := n) (by push_cast; ring), hμ, hlc, hnc]
      field_simp [hnc ▸ hb]
      ring
    · rw [hurwitzCoeff_of_eq (k := n + 1 + (i : ℕ)) (by push_cast; ring),
        coeff_eq_zero_of_natDegree_lt (by omega)]
      split_ifs with hpar
      · rw [hurwitzCoeff_of_eq (k := n + (i : ℕ)) (by push_cast; ring),
          coeff_eq_zero_of_natDegree_lt (by omega)]
        ring
      · ring
  have h00 : E 0 0 = p.nextCoeff := by
    rw [hE]
    simp only [Fin.val_zero, Nat.zero_mod, zero_ne_one, ↓reduceIte, sub_zero]
    rw [hurwitzCoeff_of_eq (k := n) (by rw [hn]; push_cast; ring), hnc]
  have hsub : E.submatrix Fin.succ Fin.succ = hurwitzMinor (routhStep p) k := by
    ext i j
    rw [Matrix.submatrix_apply, hE, hurwitzMinor, Matrix.of_apply, hurwitzCoeff_routhStep, hq]
    simp only [Fin.val_succ]
    have e1 : (p.natDegree : ℤ) + ((i : ℕ) + 1 : ℕ) - 2 * ((j : ℕ) + 1 : ℕ) - 1 =
        (n : ℤ) + (i : ℕ) - 2 * (j : ℕ) - 1 := by rw [hn]; push_cast; ring
    have e2 : (p.natDegree : ℤ) + ((i : ℕ) + 1 : ℕ) - 2 * ((j : ℕ) + 1 : ℕ) - 2 =
        (n : ℤ) + (i : ℕ) - 2 * (j : ℕ) - 1 - 1 := by rw [hn]; push_cast; ring
    rw [e1, e2]
    by_cases hpar : (i : ℕ) % 2 = 0
    · rw [ite_eq_left (by omega), ite_eq_left (by rw [hn]; push_cast; omega)]
    · rw [ite_eq_right (by omega), ite_eq_right (by rw [hn]; push_cast; omega)]
      ring
  rw [hdet, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [hcol, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
    one_mul, Fin.succAbove_zero, h00, hsub]
  rfl

/-- **The Hurwitz determinants are the products of the Routh column**: `Δ_k = c_1 ⋯ c_k` with
`c_{j+1} = nextCoeff (routhStep^[j] p)`, when `c_1, …, c_{k−1}` do not vanish. -/
@[tmio T, powerlib_foundation] theorem hurwitzDet_eq_prod {k : ℕ} (hk : k ≤ p.natDegree)
    (hb : ∀ j, j + 1 < k → (routhStep^[j] p).nextCoeff ≠ 0) :
    hurwitzDet p k = ∏ j ∈ Finset.range k, (routhStep^[j] p).nextCoeff := by
  induction k generalizing p with
  | zero => simp [hurwitzDet_zero]
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      rw [hurwitzDet_one (p := p) (by omega)]
      simp
    obtain ⟨m, hm⟩ : ∃ m, p.natDegree = m + 1 := ⟨p.natDegree - 1, by omega⟩
    have hb0 : p.nextCoeff ≠ 0 := hb 0 (by omega)
    rw [hurwitzDet_succ_routhStep hm hb0, Finset.prod_range_succ',
      ih (p := routhStep p) (by rw [natDegree_routhStep hm hb0]; omega)
        fun j hj => hb (j + 1) (by omega)]
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
    ring

/-- **The Routh column entries are ratios of Hurwitz determinants**: `c_{k+1} = Δ_{k+1}/Δ_k`
when `c_1, …, c_k` do not vanish (`k < n`). -/
@[tmio T, powerlib_foundation] theorem nextCoeff_iterate_routhStep_eq_div {k : ℕ}
    (hk : k + 1 ≤ p.natDegree) (hb : ∀ j < k, (routhStep^[j] p).nextCoeff ≠ 0) :
    (routhStep^[k] p).nextCoeff = hurwitzDet p (k + 1) / hurwitzDet p k := by
  have h1 := hurwitzDet_eq_prod hk fun j hj => hb j (by omega)
  have h0 := hurwitzDet_eq_prod (k := k) (by omega) fun j hj => hb j (by omega)
  have hne : hurwitzDet p k ≠ 0 := by
    rw [h0, Finset.prod_ne_zero_iff]
    exact fun j hj => hb j (Finset.mem_range.mp hj)
  rw [eq_div_iff hne, h1, Finset.prod_range_succ, h0, mul_comm]

end Elimination

/-! ## The determinant criterion -/

section Criterion

/-- **Hurwitz's criterion, every degree.** For `p : ℝ[X]` with positive leading coefficient,
every complex root has negative real part iff the Hurwitz determinants `Δ₁, …, Δ_n` are
positive. -/
@[tmio T, powerlib_foundation] theorem hurwitz_iff_hurwitzDet {p : ℝ[X]}
    (hp : 0 < p.leadingCoeff) :
    (∀ s : ℂ, aeval s p = 0 → s.re < 0) ↔
      ∀ k, 1 ≤ k → k ≤ p.natDegree → 0 < hurwitzDet p k := by
  induction hn : p.natDegree generalizing p with
  | zero =>
    have hpC : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hn
    have hc0 : p.coeff 0 = p.leadingCoeff := by rw [leadingCoeff, hn]
    refine ⟨fun _ k h1 h2 => absurd h2 (by omega), fun _ s hs => ?_⟩
    rw [hpC, aeval_C, hc0] at hs
    exact absurd (by simpa using hs : p.leadingCoeff = 0) hp.ne'
  | succ n ih =>
    rw [hurwitz_iff_routhStep (by omega) hp]
    by_cases hb : 0 < p.nextCoeff
    · have hq := natDegree_routhStep hn hb.ne'
      have hlq := leadingCoeff_routhStep hn hb.ne'
      rw [ih (by rw [hlq]; exact hb) hq]
      constructor
      · rintro ⟨-, h⟩ k hk1 hk2
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [hurwitzDet_succ_routhStep hn hb.ne']
        rcases Nat.eq_zero_or_pos j with hj | hj
        · rw [hj, hurwitzDet_zero, mul_one]; exact hb
        · exact mul_pos hb (h j hj (by omega))
      · intro h
        refine ⟨hb, fun k hk1 hk2 => ?_⟩
        have := h (k + 1) (by omega) (by omega)
        rw [hurwitzDet_succ_routhStep hn hb.ne'] at this
        exact pos_of_mul_pos_right this hb.le
    · simp only [hb, false_and, false_iff]
      intro h
      have := h 1 le_rfl (by omega)
      rw [hurwitzDet_one (by omega)] at this
      exact hb this

/-- **Hurwitz's criterion for matrices, any finite index**: a real square matrix is spectrally
stable iff the Hurwitz determinants of its characteristic polynomial are positive. -/
@[tmio T, powerlib_foundation] theorem spectrallyStable_iff_hurwitzDet {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι ℝ) :
    Linear.SpectrallyStable A ↔
      ∀ k, 1 ≤ k → k ≤ Fintype.card ι → 0 < hurwitzDet A.charpoly k := by
  have h : ∀ s, (Linear.characteristicMatrix A s).det = aeval s A.charpoly := fun s => by
    rw [Linear.det_characteristicMatrix_eq_eval, Linear.complexify, Matrix.charpoly_map,
      eval_map_algebraMap]
  unfold Linear.SpectrallyStable
  simp only [h]
  rw [hurwitz_iff_hurwitzDet (by rw [A.charpoly_monic.leadingCoeff]; exact one_pos),
    Matrix.charpoly_natDegree_eq_dim]

/-- **Hurwitz's criterion for matrices, any dimension**: `IsHurwitz A` iff the Hurwitz
determinants `Δ₁, …, Δ_n` of `A.charpoly` are positive. -/
@[tmio T, powerlib_foundation] theorem isHurwitz_iff_hurwitzDet {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    LinearSystems.IsHurwitz A ↔ ∀ k, 1 ≤ k → k ≤ n → 0 < hurwitzDet A.charpoly k := by
  rw [← Linear.spectrallyStable_iff_isHurwitz, spectrallyStable_iff_hurwitzDet, Fintype.card_fin]

end Criterion

end powerlib.Criteria
