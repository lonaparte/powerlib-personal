import theorem.Linear.Transfer

/-! # Hurwitz polynomials and Hurwitz matrices in every degree (foundation)

The parts of the Routh–Hurwitz theory that do not depend on the degree: a monic real polynomial
splits into real factors of degree one and two, so its coefficients are positive when its roots
lie in the open left half plane (Stodola), a negative constant coefficient gives a positive real
root, and a matrix is Hurwitz exactly when the roots of its characteristic polynomial are. The
degree-specific Routh conditions (`theorem/Criteria/Hurwitz2.lean`, `Routh3.lean`, `Routh4.lean`)
are instances of these statements plus their own algebra.

Scope.
* Static algebra of one monic real polynomial `p : ℝ[X]`, whose complex roots are read through
  `aeval s p`, and of one real square matrix `A : Matrix (Fin n) (Fin n) ℝ` with the
  LeanForControl eigenpair predicate `LinearSystems.IsHurwitz` and the characteristic matrix
  `Linear.characteristicMatrix A s = s • 1 - A`. Nothing here describes a physical system and no
  model family is defined.

Source: the standard necessary condition of Stodola and the factorization of real polynomials
into real linear and quadratic factors (shared criteria interface for the work-sync
formalization; stability from the real parts of the eigenvalues,
`theory/T-small-signal-stability.md` §1.6).

Results.
* Polynomials (any degree): Stodola's necessary condition, every coefficient up to the degree is
  positive when every root has negative real part (`coeff_pos_of_roots_re_neg`), and nonnegative
  when every root has nonpositive real part (`coeff_nonneg_of_roots_re_nonpos`); its witness form,
  a negative coefficient gives a root with positive real part (`exists_root_re_pos_of_coeff_neg`);
  a negative constant coefficient gives a positive real root (`exists_pos_root_of_coeff_zero_neg`)
  and an odd degree a real root (`exists_root_of_odd_natDegree`). All follow from one
  factorization step: a complex root `z` of `p` splits off `X - z` (real `z`) or
  `X² - 2 Re z X + |z|²` (non-real `z`) with a monic real cofactor.
* Matrices (any dimension): `det (s • 1 - A) = aeval s A.charpoly`
  (`det_characteristicMatrix_eq_aeval`); the interface `IsHurwitz A ↔ ∀ s, q s = 0 → s.re < 0`
  for every `q` with the zeros of the characteristic determinant
  (`isHurwitz_iff_of_det_characteristicMatrix`; for a polynomial equal to `A.charpoly`,
  `isHurwitz_iff_of_charpoly`); Stodola for a Hurwitz matrix (`charpoly_coeff_pos_of_isHurwitz`).
* Witnesses (any dimension): `0 < tr A` gives a characteristic root with positive real part
  (`exists_root_re_pos_of_trace_pos`, eigenpair form
  `exists_eigenpair_re_pos_of_trace_pos`; `tr A = -coeff (n - 1)`), and `(-1)ⁿ det A < 0` a positive
  real eigenvalue (real eigenvector: `exists_pos_real_eigenvector_of_det`; complex eigenvector:
  `exists_pos_real_eigenvalue_of_det`; `det A = (-1)ⁿ coeff 0`).
* No characteristic root to the right of the spectrum: if every eigenvalue has real part below
  `Re s`, `s` is not a characteristic root (`det_characteristicMatrix_ne_zero_of_re_lt`); for a
  Hurwitz matrix every `s` with `0 ≤ Re s` (`det_characteristicMatrix_ne_zero_of_isHurwitz`), and
  every real `r ≥ 0` in the real determinant (`det_smul_sub_ne_zero_of_isHurwitz`).

Family and connection conclusions.
* None: static algebra of polynomials and matrices. Model families publish their conclusions as
  connection statements through the linear hub.
-/

noncomputable section
namespace powerlib.Criteria
open Matrix Polynomial
open scoped ComplexConjugate

/-! ## Monic real polynomials -/

section Polynomial

variable {p : ℝ[X]}

/-- The real quadratic factor `X² - 2 Re z X + |z|²` whose roots are `z` and `z̄`. -/
private def quadFactor (z : ℂ) : ℝ[X] := X ^ 2 - C (2 * z.re) * X + C (z.re ^ 2 + z.im ^ 2)

@[tmio T, powerlib_foundation] private theorem quadFactor_monic (z : ℂ) : (quadFactor z).Monic := by
  unfold quadFactor
  monicity!

@[tmio T, powerlib_foundation] private theorem quadFactor_natDegree (z : ℂ) :
    (quadFactor z).natDegree = 2 := by
  unfold quadFactor
  compute_degree!

@[tmio T, powerlib_foundation] private theorem aeval_quadFactor (z : ℂ) : aeval z (quadFactor z) = 0 := by
  simp only [quadFactor, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    Complex.coe_algebraMap]
  apply Complex.ext <;> simp [pow_two] <;> ring

@[tmio T, powerlib_foundation] private theorem coeff_quadFactor (z : ℂ) (k : ℕ) :
    (quadFactor z).coeff k =
      if k = 0 then z.re ^ 2 + z.im ^ 2 else if k = 1 then -(2 * z.re) else if k = 2 then 1
        else 0 := by
  simp only [quadFactor, coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul_X, coeff_C]
  rcases k with _ | _ | _ | k <;> simp

/-- A complex root of a monic real polynomial of positive degree splits off a monic real factor of
degree one or two: `X - r` at a real root `r`, `X² - 2 Re z X + |z|²` at a non-real root `z`. -/
@[tmio T, powerlib_foundation] private theorem exists_factor (hp : p.Monic) (hd : 0 < p.natDegree) :
    ∃ q : ℝ[X], q.Monic ∧
      ((∃ r : ℝ, p = (X - C r) * q) ∨ ∃ z : ℂ, z.im ≠ 0 ∧ p = quadFactor z * q) := by
  obtain ⟨z, hz⟩ := Complex.exists_root (f := p.map (algebraMap ℝ ℂ))
    (by rw [degree_map]; exact natDegree_pos_iff_degree_pos.mp hd)
  rw [IsRoot, eval_map_algebraMap] at hz
  by_cases him : z.im = 0
  · have hr : p.IsRoot z.re := by
      have hzr : z = algebraMap ℝ ℂ z.re := Complex.ext (by simp) (by simp [him])
      rw [hzr, aeval_algebraMap_apply, coe_aeval_eq_eval] at hz
      exact (algebraMap ℝ ℂ).injective (hz.trans (map_zero _).symm)
    obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hr
    exact ⟨q, (monic_X_sub_C _).of_mul_monic_left (hq ▸ hp), Or.inl ⟨z.re, hq⟩⟩
  · have hmap : (quadFactor z).map (algebraMap ℝ ℂ) = (X - C z) * (X - C (conj z)) := by
      have h1 : z + conj z = ((2 * z.re : ℝ) : ℂ) := Complex.add_conj z
      have h2 : z * conj z = ((z.re ^ 2 + z.im ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_apply]; push_cast; ring
      have e : (X - C z) * (X - C (conj z)) = X ^ 2 - C (z + conj z) * X + C (z * conj z) := by
        simp only [C_add, C_mul]
        ring
      rw [e, h1, h2]
      simp only [quadFactor, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
        Polynomial.map_pow, map_X, map_C, Complex.coe_algebraMap]
    have hdvd : (quadFactor z).map (algebraMap ℝ ℂ) ∣ p.map (algebraMap ℝ ℂ) := by
      obtain ⟨g, hg⟩ := dvd_iff_isRoot.mpr
        (show (p.map (algebraMap ℝ ℂ)).IsRoot z by rw [IsRoot, eval_map_algebraMap]; exact hz)
      have hconj : (p.map (algebraMap ℝ ℂ)).IsRoot (conj z) := by
        rw [IsRoot, eval_map_algebraMap, aeval_conj, hz, map_zero]
      have hne : conj z - z ≠ 0 := fun h => him (by
        have := congrArg Complex.im h
        simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
        linarith)
      rw [hg, IsRoot, eval_mul, eval_sub, eval_X, eval_C] at hconj
      obtain ⟨h, hh⟩ := dvd_iff_isRoot.mpr ((mul_eq_zero.mp hconj).resolve_left hne)
      exact ⟨h, by rw [hmap, hg, hh, mul_assoc]⟩
    obtain ⟨q, hq⟩ := (map_dvd_map (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective
      (quadFactor_monic z)).mp hdvd
    exact ⟨q, (quadFactor_monic z).of_mul_monic_left (hq ▸ hp), Or.inr ⟨z, him, hq⟩⟩

/-- Induction over the real factorization of monic real polynomials. -/
@[tmio T, powerlib_foundation] private theorem monic_induction {P : ℝ[X] → Prop} (h1 : P 1)
    (hlin : ∀ (r : ℝ) (q : ℝ[X]), q.Monic → P q → P ((X - C r) * q))
    (hquad : ∀ (z : ℂ) (q : ℝ[X]), z.im ≠ 0 → q.Monic → P q → P (quadFactor z * q))
    (hp : p.Monic) : P p := by
  induction h : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ d ih =>
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [eq_one_of_monic_natDegree_zero hp h]
      exact h1
    obtain ⟨q, hq, ⟨r, rfl⟩ | ⟨z, hz, rfl⟩⟩ := exists_factor hp (h ▸ hd)
    · refine hlin r q hq (ih q.natDegree ?_ hq rfl)
      rw [← h, (monic_X_sub_C r).natDegree_mul hq, natDegree_X_sub_C]
      omega
    · refine hquad z q hz hq (ih q.natDegree ?_ hq rfl)
      rw [← h, (quadFactor_monic z).natDegree_mul hq, quadFactor_natDegree]
      omega

@[tmio T, powerlib_foundation] private theorem coeff_nonneg_mul {f q : ℝ[X]} (hf : ∀ k, 0 ≤ f.coeff k)
    (hq : ∀ k, 0 ≤ q.coeff k) (k : ℕ) : 0 ≤ (f * q).coeff k := by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hf _) (hq _)

@[tmio T, powerlib_foundation] private theorem coeff_nonneg_of_pos {f : ℝ[X]}
    (hf : ∀ k ≤ f.natDegree, 0 < f.coeff k) (k : ℕ) : 0 ≤ f.coeff k := by
  by_cases hk : k ≤ f.natDegree
  · exact (hf k hk).le
  · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hk)]

/-- Positive coefficients up to the degree are preserved by products of monic polynomials. -/
@[tmio T, powerlib_foundation] private theorem coeff_pos_mul {f q : ℝ[X]} (hfm : f.Monic) (hqm : q.Monic)
    (hf : ∀ k ≤ f.natDegree, 0 < f.coeff k) (hq : ∀ k ≤ q.natDegree, 0 < q.coeff k) :
    ∀ k ≤ (f * q).natDegree, 0 < (f * q).coeff k := by
  intro k hk
  rw [hfm.natDegree_mul hqm] at hk
  rw [coeff_mul]
  refine Finset.sum_pos' (fun x _ => mul_nonneg (coeff_nonneg_of_pos hf _)
    (coeff_nonneg_of_pos hq _)) ⟨(min k f.natDegree, k - min k f.natDegree), ?_, ?_⟩
  · rw [Finset.mem_antidiagonal]
    omega
  · exact mul_pos (hf _ (min_le_right _ _)) (hq _ (by omega))

@[tmio T, powerlib_foundation] private theorem coeff_X_sub_C_pos {r : ℝ} (hr : r < 0) :
    ∀ k ≤ (X - C r).natDegree, 0 < (X - C r).coeff k := by
  intro k hk
  rw [natDegree_X_sub_C] at hk
  interval_cases k <;> simp [coeff_X, coeff_C, hr]

@[tmio T, powerlib_foundation] private theorem coeff_quadFactor_pos {z : ℂ} (hz : z.re < 0) :
    ∀ k ≤ (quadFactor z).natDegree, 0 < (quadFactor z).coeff k := by
  intro k hk
  rw [quadFactor_natDegree] at hk
  interval_cases k <;> simp [coeff_quadFactor] <;> nlinarith [sq_nonneg z.im]

/-- **Stodola.** Every coefficient of a monic real polynomial whose complex roots all have
negative real part is positive, up to the degree. -/
@[tmio T, powerlib_foundation] theorem coeff_pos_of_roots_re_neg (hp : p.Monic)
    (H : ∀ s : ℂ, aeval s p = 0 → s.re < 0) : ∀ k ≤ p.natDegree, 0 < p.coeff k := by
  refine monic_induction (P := fun p => (∀ s : ℂ, aeval s p = 0 → s.re < 0) →
    ∀ k ≤ p.natDegree, 0 < p.coeff k) ?_ ?_ ?_ hp H
  · intro _ k hk
    rw [natDegree_one, Nat.le_zero] at hk
    rw [hk, coeff_one_zero]
    exact one_pos
  · intro r q hq ih H
    have hr : r < 0 := by simpa using H r (by simp)
    exact coeff_pos_mul (monic_X_sub_C r) hq (coeff_X_sub_C_pos hr)
      (ih fun s hs => H s (by simp [hs]))
  · intro z q _ hq ih H
    exact coeff_pos_mul (quadFactor_monic z) hq
      (coeff_quadFactor_pos (H z (by rw [map_mul, aeval_quadFactor, zero_mul])))
      (ih fun s hs => H s (by simp [hs]))

/-- Closed half plane: every coefficient of a monic real polynomial whose complex roots all have
nonpositive real part is nonnegative. -/
@[tmio T, powerlib_foundation] theorem coeff_nonneg_of_roots_re_nonpos (hp : p.Monic)
    (H : ∀ s : ℂ, aeval s p = 0 → s.re ≤ 0) (k : ℕ) : 0 ≤ p.coeff k := by
  refine monic_induction (P := fun p => (∀ s : ℂ, aeval s p = 0 → s.re ≤ 0) →
    ∀ k, 0 ≤ p.coeff k) ?_ ?_ ?_ hp H k
  · intro _ k
    rw [coeff_one]
    split_ifs <;> norm_num
  · intro r q _ ih H
    have hr : r ≤ 0 := by simpa using H r (by simp)
    refine coeff_nonneg_mul (fun k => ?_) (ih fun s hs => H s (by simp [hs]))
    rcases k with _ | _ | k <;> simp [coeff_X, coeff_C, hr]
  · intro z q _ _ ih H
    have hz : z.re ≤ 0 := H z (by rw [map_mul, aeval_quadFactor, zero_mul])
    refine coeff_nonneg_mul (fun k => ?_) (ih fun s hs => H s (by simp [hs]))
    rw [coeff_quadFactor]
    split_ifs <;> nlinarith [sq_nonneg z.re, sq_nonneg z.im]

/-- A negative coefficient of a monic real polynomial gives a root with positive real part. -/
@[tmio T, powerlib_foundation] theorem exists_root_re_pos_of_coeff_neg (hp : p.Monic) {k : ℕ}
    (hk : p.coeff k < 0) : ∃ s : ℂ, aeval s p = 0 ∧ 0 < s.re := by
  by_contra h
  push Not at h
  exact absurd (coeff_nonneg_of_roots_re_nonpos hp h k) (not_le.mpr hk)

/-- A monic real polynomial with a negative constant coefficient has a positive real root. -/
@[tmio T, powerlib_foundation] theorem exists_pos_root_of_coeff_zero_neg (hp : p.Monic)
    (h0 : p.coeff 0 < 0) : ∃ r : ℝ, 0 < r ∧ p.eval r = 0 := by
  refine monic_induction (P := fun p => p.coeff 0 < 0 → ∃ r : ℝ, 0 < r ∧ p.eval r = 0)
    ?_ ?_ ?_ hp h0
  · intro h
    rw [coeff_one_zero] at h
    exact absurd h (by norm_num)
  · intro r q _ ih h
    rw [mul_coeff_zero] at h
    by_cases hr : 0 < r
    · exact ⟨r, hr, by simp⟩
    obtain ⟨r', hr', hroot⟩ := ih (by simp at h; nlinarith)
    exact ⟨r', hr', by simp [hroot]⟩
  · intro z q hz _ ih h
    rw [mul_coeff_zero] at h
    have hf : 0 < (quadFactor z).coeff 0 := by
      simp only [coeff_quadFactor, ↓reduceIte]
      positivity
    obtain ⟨r', hr', hroot⟩ := ih (by nlinarith)
    exact ⟨r', hr', by simp [hroot]⟩

/-- A monic real polynomial of odd degree has a real root. -/
@[tmio T, powerlib_foundation] theorem exists_root_of_odd_natDegree (hp : p.Monic)
    (h : Odd p.natDegree) : ∃ r : ℝ, p.eval r = 0 := by
  refine monic_induction (P := fun p => Odd p.natDegree → ∃ r : ℝ, p.eval r = 0) ?_ ?_ ?_ hp h
  · intro h
    simp at h
  · intro r _ _ _ _
    exact ⟨r, by simp⟩
  · intro z q _ hq ih h
    rw [(quadFactor_monic z).natDegree_mul hq, quadFactor_natDegree] at h
    obtain ⟨r, hr⟩ := ih (by obtain ⟨m, hm⟩ := h; exact ⟨m - 1, by omega⟩)
    exact ⟨r, by simp [hr]⟩

end Polynomial

/-! ## Matrices and their characteristic polynomials -/

section Matrix

variable {n : ℕ}

/-- The characteristic determinant is the complex evaluation of the real characteristic
polynomial (`Linear.det_characteristicMatrix_eq_eval`). -/
@[tmio T, powerlib_foundation] theorem det_characteristicMatrix_eq_aeval (A : Matrix (Fin n) (Fin n) ℝ)
    (s : ℂ) : (Linear.characteristicMatrix A s).det = aeval s A.charpoly := by
  rw [Linear.det_characteristicMatrix_eq_eval, Linear.complexify, charpoly_map,
    eval_map_algebraMap]

/-- **The Hurwitz interface.** `A` is Hurwitz exactly when every zero of a function with the zeros
of its characteristic determinant lies in the open left half plane. -/
@[tmio T, powerlib_foundation] theorem isHurwitz_iff_of_det_characteristicMatrix
    (A : Matrix (Fin n) (Fin n) ℝ) {q : ℂ → ℂ}
    (h : ∀ s, (Linear.characteristicMatrix A s).det = 0 ↔ q s = 0) :
    LinearSystems.IsHurwitz A ↔ ∀ s, q s = 0 → s.re < 0 := by
  rw [← Linear.spectrallyStable_iff_isHurwitz]
  simp only [Linear.SpectrallyStable, h]

/-- `A` is Hurwitz exactly when every complex root of its characteristic polynomial lies in the
open left half plane. -/
@[tmio T, powerlib_foundation] theorem isHurwitz_iff_of_charpoly (A : Matrix (Fin n) (Fin n) ℝ)
    {p : ℝ[X]} (h : A.charpoly = p) :
    LinearSystems.IsHurwitz A ↔ ∀ s : ℂ, aeval s p = 0 → s.re < 0 :=
  isHurwitz_iff_of_det_characteristicMatrix A fun s => by rw [det_characteristicMatrix_eq_aeval, h]

/-- Stodola for matrices: the characteristic polynomial of a Hurwitz matrix has positive
coefficients. -/
@[tmio T, powerlib_foundation] theorem charpoly_coeff_pos_of_isHurwitz {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : LinearSystems.IsHurwitz A) {k : ℕ} (hk : k ≤ n) : 0 < A.charpoly.coeff k :=
  coeff_pos_of_roots_re_neg A.charpoly_monic ((isHurwitz_iff_of_charpoly A rfl).mp hA) k
    (by rwa [charpoly_natDegree_eq_dim, Fintype.card_fin])

/-- `0 < tr A`: a characteristic root with positive real part (`tr A = -coeff (n - 1)`). -/
@[tmio T, powerlib_foundation] theorem exists_root_re_pos_of_trace_pos
    (A : Matrix (Fin n) (Fin n) ℝ) (h : 0 < A.trace) :
    ∃ s : ℂ, (Linear.characteristicMatrix A s).det = 0 ∧ 0 < s.re := by
  have : Nonempty (Fin n) := by
    rcases n with _ | n
    · simp at h
    · exact ⟨0⟩
  rw [trace_eq_neg_charpoly_coeff] at h
  obtain ⟨s, hs, hre⟩ := exists_root_re_pos_of_coeff_neg A.charpoly_monic (neg_pos.mp h)
  exact ⟨s, by rw [det_characteristicMatrix_eq_aeval]; exact hs, hre⟩

/-- `0 < tr A`: an eigenpair with positive real part, in the shape of LeanForControl's
`unstable_of_exists_complex_eigenvalue_re_pos`. -/
@[tmio T, powerlib_foundation] theorem exists_eigenpair_re_pos_of_trace_pos
    (A : Matrix (Fin n) (Fin n) ℝ) (h : 0 < A.trace) :
    ∃ (μ : ℂ) (v : Fin n → ℂ), v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v ∧ 0 < μ.re := by
  obtain ⟨s, hs, hre⟩ := exists_root_re_pos_of_trace_pos A h
  obtain ⟨v, hv, heig⟩ := Linear.exists_eigenvector_of_root hs
  exact ⟨s, v, hv, heig, hre⟩

@[tmio T, powerlib_foundation] private theorem charpoly_coeff_zero_neg {A : Matrix (Fin n) (Fin n) ℝ}
    (h : (-1) ^ n * A.det < 0) : A.charpoly.coeff 0 < 0 := by
  rwa [det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc, ← pow_add, ← two_mul, pow_mul,
    neg_one_sq, one_pow, one_mul] at h

/-- `(-1)ⁿ det A < 0`: a positive real eigenvalue with a real eigenvector
(`det A = (-1)ⁿ coeff 0`). -/
@[tmio T, powerlib_foundation] theorem exists_pos_real_eigenvector_of_det (A : Matrix (Fin n) (Fin n) ℝ)
    (h : (-1) ^ n * A.det < 0) : ∃ r : ℝ, 0 < r ∧ ∃ v : Fin n → ℝ, v ≠ 0 ∧ A *ᵥ v = r • v := by
  obtain ⟨r, hr, hroot⟩ := exists_pos_root_of_coeff_zero_neg A.charpoly_monic
    (charpoly_coeff_zero_neg h)
  rw [eval_charpoly] at hroot
  obtain ⟨v, hv, hz⟩ := exists_mulVec_eq_zero_iff.mpr hroot
  refine ⟨r, hr, v, hv, ?_⟩
  rw [sub_mulVec, scalar_apply, sub_eq_zero] at hz
  rw [← hz]
  ext i
  simp [mulVec_diagonal]

/-- `(-1)ⁿ det A < 0`: a positive real eigenvalue with a complex eigenvector, in the shape of
LeanForControl's `unstable_of_exists_complex_eigenvalue_re_pos`. -/
@[tmio T, powerlib_foundation] theorem exists_pos_real_eigenvalue_of_det (A : Matrix (Fin n) (Fin n) ℝ)
    (h : (-1) ^ n * A.det < 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : Fin n → ℂ, v ≠ 0 ∧ A.map (algebraMap ℝ ℂ) *ᵥ v = (r : ℂ) • v := by
  obtain ⟨r, hr, hroot⟩ := exists_pos_root_of_coeff_zero_neg A.charpoly_monic
    (charpoly_coeff_zero_neg h)
  refine ⟨r, hr, Linear.exists_eigenvector_of_root ?_⟩
  rw [det_characteristicMatrix_eq_aeval, ← Complex.coe_algebraMap, aeval_algebraMap_apply,
    coe_aeval_eq_eval, hroot, map_zero]

/-- No characteristic root to the right of the spectrum: if every eigenvalue of `A` has real part
below `Re s`, then `s` is not a root of `det (s • 1 - A)`. -/
@[tmio T, powerlib_foundation] theorem det_characteristicMatrix_ne_zero_of_re_lt
    (A : Matrix (Fin n) (Fin n) ℝ) {s : ℂ}
    (h : ∀ (μ : ℂ) (v : Fin n → ℂ), v ≠ 0 → A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v → μ.re < s.re) :
    (Linear.characteristicMatrix A s).det ≠ 0 := fun h0 => by
  obtain ⟨v, hv, heig⟩ := Linear.exists_eigenvector_of_root h0
  exact lt_irrefl _ (h s v hv heig)

/-- A Hurwitz matrix has no characteristic root in the closed right half plane. -/
@[tmio T, powerlib_foundation] theorem det_characteristicMatrix_ne_zero_of_isHurwitz
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : LinearSystems.IsHurwitz A) {s : ℂ} (hs : 0 ≤ s.re) :
    (Linear.characteristicMatrix A s).det ≠ 0 :=
  det_characteristicMatrix_ne_zero_of_re_lt A fun μ v hv heig => by
    have := hA μ v hv heig
    rw [neg_zero] at this
    linarith

/-- A Hurwitz matrix has no real characteristic root `r ≥ 0`: `r • 1 - A` is invertible. -/
@[tmio T, powerlib_foundation] theorem det_smul_sub_ne_zero_of_isHurwitz
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : LinearSystems.IsHurwitz A) {r : ℝ} (hr : 0 ≤ r) :
    (r • (1 : Matrix (Fin n) (Fin n) ℝ) - A).det ≠ 0 := by
  intro h0
  apply det_characteristicMatrix_ne_zero_of_isHurwitz hA (s := r) (by simpa using hr)
  rw [det_characteristicMatrix_eq_aeval, ← Complex.coe_algebraMap, aeval_algebraMap_apply,
    coe_aeval_eq_eval, eval_charpoly, scalar_apply, ← smul_one_eq_diagonal, h0, map_zero]

end Matrix

end powerlib.Criteria
