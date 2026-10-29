import theorem.Linear.Transfer
import theorem.TMIO.Relation

/-! # Realization theory

The transfer function observes a plant; a coordinate change re-represents it. On minimal plants,
those that are controllable and observable, the observation is exactly the representation
change: two minimal plants have the same transfer function if and only if they are similar
(`similar_iff_transfer_eq`), and stability is then a function of the transfer function
(`isHurwitz_iff_of_transfer_eq`). Every plant has a minimal plant with the same transfer function
and no more states (`exists_minimal_realization`), and controllability together with
observability is exactly minimality (`controllable_observable_iff_minimal`). The modes removed by
a minimal realization are the hidden modes that the observation cannot see.

Scope.
* Generic: arbitrary linear plants `Plant n p` (`theorem/Linear/Plant.lean`), continuous time,
  of any state dimension; no model.
* Controllability and observability are LeanForControl's predicates, used through their rank
  characterizations. Transfer functions are compared where both are defined; equality there is
  equality of the Markov parameters `C Aᵏ B` and of the feedthrough.

Source: LeanForControl's controllability and observability (`IsControllable`, `IsObservable`,
`reachableSubspace`); the transfer functions and similarity of `theorem/Linear/Transfer.lean`;
certification by an observation (`TMIO.certify`, `theorem/TMIO/Relation.lean`).

Results.
* Transfer functions and Markov parameters: `det_characteristicMatrix`, `transfer_eq_adjugate`,
  `markov`, `exists_det_characteristicMatrix_ne_zero`, `markov_eq_of_transfer_eventually_eq`,
  `transfer_eventually_eq_of_markov_eq`, `transfer_eq_of_eventually_eq`,
  `transfer_eq_iff_markov_eq`.
* Minimal plants: `obsv`, `ctrb`, `ctrb_eq`, `obsv_eq`, `similar_of_markov_eq`,
  `similar_iff_transfer_eq`, `basisMatrix`, `reduce_uncontrollable`, `Plant.dual`, `markov_dual`,
  `isObservable_iff_isControllable_transpose`, `exists_minimal_markov`,
  `exists_minimal_realization`, `controllable_observable_iff_minimal`, `Plant.Minimal`.
* What the observation decides: `isHurwitz_iff_of_transfer_eq`, `transfer_certified` (on minimal
  plants the transfer function certifies every behavioural sentence), `hiddenMode_not_minimal`
  (the observation misses exactly such modes).
-/

noncomputable section

namespace powerlib.Linear

open Matrix LinearSystems

variable {n n' p : ℕ}

@[tmio T, powerlib_foundation] theorem det_characteristicMatrix (A : Matrix (Fin n) (Fin n) ℝ) (s : ℂ) :
    (characteristicMatrix A s).det = (complexify A).charpoly.eval s :=
  det_characteristicMatrix_eq_eval A s

@[powerlib_foundation] theorem transfer_eq_adjugate (m : Plant n p) (s : ℂ) :
    transfer m s = ((characteristicMatrix m.A s).det)⁻¹ •
      (complexify m.C * (characteristicMatrix m.A s).adjugate * complexify m.B) +
      complexify m.D := by
  rw [transfer, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.mul_smul, Matrix.smul_mul]

/-- The Markov parameters `C Aᵏ B`. -/
def markov (m : Plant n p) (k : ℕ) : Matrix (Fin p) (Fin p) ℝ := m.C * m.A ^ k * m.B

section Expansion

variable (m : Plant n p)

@[powerlib_foundation] private lemma smul_resolvent {s : ℂ}
    (h : (characteristicMatrix m.A s).det ≠ 0) :
    s • (characteristicMatrix m.A s)⁻¹ = 1 + complexify m.A * (characteristicMatrix m.A s)⁻¹ := by
  have hinv := Matrix.mul_nonsing_inv (characteristicMatrix m.A s) (isUnit_iff_ne_zero.mpr h)
  generalize (characteristicMatrix m.A s)⁻¹ = R at hinv ⊢
  rw [show characteristicMatrix m.A s = s • 1 - complexify m.A from rfl, Matrix.sub_mul,
    Matrix.smul_mul, Matrix.one_mul] at hinv
  rw [← hinv]
  abel

@[powerlib_foundation] private lemma resolvent_expansion {s : ℂ} (hs : s ≠ 0)
    (h : (characteristicMatrix m.A s).det ≠ 0) (N : ℕ) :
    (characteristicMatrix m.A s)⁻¹ =
      ∑ j ∈ Finset.range N, (s ^ (j + 1))⁻¹ • complexify m.A ^ j +
        (s ^ N)⁻¹ • (complexify m.A ^ N * (characteristicMatrix m.A s)⁻¹) := by
  have hR := smul_resolvent m h
  generalize (characteristicMatrix m.A s)⁻¹ = R at hR ⊢
  have hR' : R = s⁻¹ • (1 + complexify m.A * R) := by
    rw [← hR, smul_smul, inv_mul_cancel₀ hs, one_smul]
  induction N with
  | zero => simp
  | succ N ih =>
    have step : (s ^ N)⁻¹ • (complexify m.A ^ N * R) =
        (s ^ (N + 1))⁻¹ • complexify m.A ^ N +
          (s ^ (N + 1))⁻¹ • (complexify m.A ^ (N + 1) * R) := by
      conv_lhs => rw [hR']
      rw [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, smul_smul, ← Matrix.mul_assoc,
        ← mul_inv, ← pow_succ, ← pow_succ, smul_add]
    rw [Finset.sum_range_succ, add_assoc, ← step]
    exact ih

@[powerlib_foundation] private lemma transfer_expansion {s : ℂ} (hs : s ≠ 0)
    (h : (characteristicMatrix m.A s).det ≠ 0) (N : ℕ) :
    transfer m s = complexify m.D +
      ∑ j ∈ Finset.range N, (s ^ (j + 1))⁻¹ • complexify (markov m j) +
        (s ^ N)⁻¹ • (complexify m.C * complexify m.A ^ N * (characteristicMatrix m.A s)⁻¹ *
          complexify m.B) := by
  rw [transfer]
  conv_lhs => rw [resolvent_expansion m hs h N]
  simp only [markov, complexify_mul, Matrix.map_pow, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  abel

open scoped Matrix.Norms.Operator in
@[powerlib_foundation] private lemma resolvent_bound :
    ∃ s₀ > 0, ∀ x : ℝ, s₀ ≤ x → (characteristicMatrix m.A (x : ℂ)).det ≠ 0 ∧
      ‖(characteristicMatrix m.A (x : ℂ))⁻¹‖ ≤ 2 * ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ / x := by
  refine ⟨2 * ‖complexify m.A‖ + 1, by positivity, fun x hx => ?_⟩
  have ha := norm_nonneg (complexify m.A)
  have hx0 : 0 < x := by linarith
  have hxn : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real, Real.norm_of_nonneg hx0.le]
  have hdet : (characteristicMatrix m.A (x : ℂ)).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hAv : complexify m.A *ᵥ v = (x : ℂ) • v := by
      rw [show characteristicMatrix m.A (x : ℂ) = (x : ℂ) • 1 - complexify m.A from rfl,
        Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hzero
      exact hzero.symm
    have hle : x * ‖v‖ ≤ ‖complexify m.A‖ * ‖v‖ := by
      rw [← hxn, ← norm_smul, ← hAv]
      exact Matrix.linfty_opNorm_mulVec _ _
    have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
    nlinarith
  refine ⟨hdet, ?_⟩
  have hR := smul_resolvent m hdet
  generalize (characteristicMatrix m.A (x : ℂ))⁻¹ = R at hR ⊢
  have h1 : x * ‖R‖ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ + ‖complexify m.A‖ * ‖R‖ := by
    rw [← hxn, ← norm_smul, hR]
    exact (norm_add_le _ _).trans (by gcongr; exact Matrix.linfty_opNorm_mul _ _)
  rw [le_div_iff₀ hx0]
  nlinarith [norm_nonneg R, mul_nonneg (show (0 : ℝ) ≤ x - 2 * ‖complexify m.A‖ by linarith)
    (norm_nonneg R)]

end Expansion

@[powerlib_foundation] theorem exists_det_characteristicMatrix_ne_zero (m : Plant n p) :
    ∃ s₀ : ℝ, ∀ x : ℝ, s₀ ≤ x → (characteristicMatrix m.A (x : ℂ)).det ≠ 0 := by
  obtain ⟨s₀, -, h⟩ := resolvent_bound m
  exact ⟨s₀, fun x hx => (h x hx).1⟩

@[powerlib_foundation] private lemma eq_zero_of_norm_le_div {E : Type*} [NormedAddCommGroup E]
    (X : E) (K s₀ : ℝ) (h : ∀ x : ℝ, s₀ ≤ x → ‖X‖ ≤ K / x) : X = 0 := by
  have ht : Filter.Tendsto (fun x : ℝ => K / x) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  exact norm_le_zero_iff.mp (ge_of_tendsto ht (Filter.eventually_atTop.2 ⟨s₀, h⟩))

open scoped Matrix.Norms.Operator in
@[powerlib_foundation] private lemma remainder_bound (m : Plant n p) (N : ℕ) :
    ∃ s₀ > 0, ∃ K, ∀ x : ℝ, s₀ ≤ x → (characteristicMatrix m.A (x : ℂ)).det ≠ 0 ∧
      ‖complexify m.C * complexify m.A ^ N * (characteristicMatrix m.A (x : ℂ))⁻¹ *
        complexify m.B‖ ≤ K / x := by
  obtain ⟨s₀, hs₀, hb⟩ := resolvent_bound m
  refine ⟨s₀, hs₀, ‖complexify m.C * complexify m.A ^ N‖ * (2 * ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖) *
    ‖complexify m.B‖, fun x hx => ⟨(hb x hx).1, ?_⟩⟩
  have hx0 : 0 < x := hs₀.trans_le hx
  calc _ ≤ ‖complexify m.C * complexify m.A ^ N‖ * ‖(characteristicMatrix m.A (x : ℂ))⁻¹‖ *
        ‖complexify m.B‖ :=
        (Matrix.linfty_opNorm_mul _ _).trans
          (by gcongr; exact Matrix.linfty_opNorm_mul _ _)
    _ ≤ ‖complexify m.C * complexify m.A ^ N‖ * (2 * ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ / x) *
        ‖complexify m.B‖ := by gcongr; exact (hb x hx).2
    _ = _ := by field_simp

open scoped Matrix.Norms.Operator in
@[powerlib_foundation] theorem markov_eq_of_transfer_eventually_eq {m : Plant n p}
    {m' : Plant n' p} (h : ∃ s₁ : ℝ, ∀ x : ℝ, s₁ ≤ x → transfer m x = transfer m' x) :
    m.D = m'.D ∧ ∀ k, markov m k = markov m' k := by
  obtain ⟨s₁, hs₁⟩ := h
  have hinj : Function.Injective fun M : Matrix (Fin p) (Fin p) ℝ => complexify M :=
    Matrix.map_injective (algebraMap ℝ ℂ).injective
  have key : ∀ N, ∃ s₀ > 0, ∃ K, ∀ x : ℝ, s₀ ≤ x →
      complexify m.D + ∑ j ∈ Finset.range N, ((x : ℂ) ^ (j + 1))⁻¹ • complexify (markov m j) +
          ((x : ℂ) ^ N)⁻¹ • (complexify m.C * complexify m.A ^ N *
            (characteristicMatrix m.A (x : ℂ))⁻¹ * complexify m.B) =
        complexify m'.D +
          ∑ j ∈ Finset.range N, ((x : ℂ) ^ (j + 1))⁻¹ • complexify (markov m' j) +
          ((x : ℂ) ^ N)⁻¹ • (complexify m'.C * complexify m'.A ^ N *
            (characteristicMatrix m'.A (x : ℂ))⁻¹ * complexify m'.B) ∧
      ‖complexify m.C * complexify m.A ^ N * (characteristicMatrix m.A (x : ℂ))⁻¹ *
          complexify m.B - complexify m'.C * complexify m'.A ^ N *
          (characteristicMatrix m'.A (x : ℂ))⁻¹ * complexify m'.B‖ ≤ K / x := by
    intro N
    obtain ⟨a, ha, K, hK⟩ := remainder_bound m N
    obtain ⟨a', ha', K', hK'⟩ := remainder_bound m' N
    refine ⟨max (max a a') s₁, lt_max_of_lt_left (lt_max_of_lt_left ha), K + K',
      fun x hx => ?_⟩
    have hxa : a ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    have hxa' : a' ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have hx₁ : s₁ ≤ x := le_trans (le_max_right _ _) hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ha.trans_le hxa).ne'
    refine ⟨?_, ?_⟩
    · rw [← transfer_expansion m hx0 (hK x hxa).1 N, ← transfer_expansion m' hx0 (hK' x hxa').1 N]
      exact hs₁ x hx₁
    · rw [add_div]
      exact (norm_sub_le _ _).trans (add_le_add (hK x hxa).2 (hK' x hxa').2)
  have hD : complexify m.D = complexify m'.D := by
    obtain ⟨s₀, -, K, hK⟩ := key 0
    refine sub_eq_zero.mp (eq_zero_of_norm_le_div _ K s₀ fun x hx => ?_)
    obtain ⟨e, hb⟩ := hK x hx
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, pow_zero, inv_one, one_smul,
      Matrix.mul_one] at e hb
    rw [norm_sub_rev] at hb
    have hdiff : complexify m.D - complexify m'.D =
        complexify m'.C * (characteristicMatrix m'.A (x : ℂ))⁻¹ * complexify m'.B -
          complexify m.C * (characteristicMatrix m.A (x : ℂ))⁻¹ * complexify m.B := by
      rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
    rw [hdiff]
    exact hb
  have hM : ∀ k, complexify (markov m k) = complexify (markov m' k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      obtain ⟨s₀, hs₀, K, hK⟩ := key (k + 1)
      refine sub_eq_zero.mp (eq_zero_of_norm_le_div _ K s₀ fun x hx => ?_)
      obtain ⟨e, hb⟩ := hK x hx
      have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hs₀.trans_le hx).ne'
      rw [Finset.sum_range_succ, Finset.sum_range_succ, hD,
        Finset.sum_congr rfl fun j hj => by rw [ih j (Finset.mem_range.mp hj)]] at e
      set c : ℂ := ((x : ℂ) ^ (k + 1))⁻¹
      have hc : c ≠ 0 := inv_ne_zero (pow_ne_zero _ hx0)
      have hsc : c • (complexify (markov m k) - complexify (markov m' k)) =
          c • ((complexify m'.C * complexify m'.A ^ (k + 1) *
            (characteristicMatrix m'.A (x : ℂ))⁻¹ * complexify m'.B) -
          (complexify m.C * complexify m.A ^ (k + 1) * (characteristicMatrix m.A (x : ℂ))⁻¹ *
            complexify m.B)) := by
        rw [smul_sub, smul_sub]
        rw [← sub_eq_zero] at e ⊢
        rw [← e]
        abel
      rw [smul_right_injective _ hc hsc, norm_sub_rev]
      exact hb
  exact ⟨hinj hD, fun k => hinj (hM k)⟩

open scoped Matrix.Norms.Operator in
@[powerlib_foundation] private lemma norm_mul_pow_le {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] (C : Matrix β α ℂ) (A : Matrix α α ℂ) (N : ℕ) : ‖C * A ^ N‖ ≤ ‖C‖ * ‖A‖ ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, ← Matrix.mul_assoc]
    calc ‖C * A ^ N * A‖ ≤ ‖C * A ^ N‖ * ‖A‖ := Matrix.linfty_opNorm_mul _ _
      _ ≤ ‖C‖ * ‖A‖ ^ N * ‖A‖ := by gcongr
      _ = ‖C‖ * ‖A‖ ^ (N + 1) := by ring

open scoped Matrix.Norms.Operator in
@[powerlib_foundation] private lemma norm_remainder_le (m : Plant n p) (N : ℕ) (s : ℂ) :
    ‖complexify m.C * complexify m.A ^ N * (characteristicMatrix m.A s)⁻¹ * complexify m.B‖ ≤
      ‖complexify m.A‖ ^ N * (‖complexify m.C‖ * ‖(characteristicMatrix m.A s)⁻¹‖ *
        ‖complexify m.B‖) := by
  calc _ ≤ ‖complexify m.C * complexify m.A ^ N * (characteristicMatrix m.A s)⁻¹‖ *
        ‖complexify m.B‖ := Matrix.linfty_opNorm_mul _ _
    _ ≤ ‖complexify m.C * complexify m.A ^ N‖ * ‖(characteristicMatrix m.A s)⁻¹‖ *
        ‖complexify m.B‖ := by gcongr; exact Matrix.linfty_opNorm_mul _ _
    _ ≤ ‖complexify m.C‖ * ‖complexify m.A‖ ^ N * ‖(characteristicMatrix m.A s)⁻¹‖ *
        ‖complexify m.B‖ := by gcongr; exact norm_mul_pow_le _ _ _
    _ = _ := by ring

open scoped Matrix.Norms.Operator in
@[powerlib_foundation] theorem transfer_eventually_eq_of_markov_eq {m : Plant n p}
    {m' : Plant n' p} (hD : m.D = m'.D) (hM : ∀ k, markov m k = markov m' k) :
    ∃ s₁ : ℝ, ∀ x : ℝ, s₁ ≤ x → transfer m x = transfer m' x := by
  obtain ⟨a, ha, hb⟩ := resolvent_bound m
  obtain ⟨a', ha', hb'⟩ := resolvent_bound m'
  refine ⟨max (max a a') (‖complexify m.A‖ + ‖complexify m'.A‖ + 1), fun x hx => ?_⟩
  obtain ⟨hxa₁, hxn⟩ := max_le_iff.mp hx
  obtain ⟨hxa, hxa'⟩ := max_le_iff.mp hxa₁
  have hx0 : 0 < x := ha.trans_le hxa
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  have hn := norm_nonneg (complexify m.A)
  have hn' := norm_nonneg (complexify m'.A)
  have hdiff : ∀ N, transfer m x - transfer m' x = ((x : ℂ) ^ N)⁻¹ •
      (complexify m.C * complexify m.A ^ N * (characteristicMatrix m.A (x : ℂ))⁻¹ *
        complexify m.B - complexify m'.C * complexify m'.A ^ N *
        (characteristicMatrix m'.A (x : ℂ))⁻¹ * complexify m'.B) := by
    intro N
    rw [transfer_expansion m hxc (hb x hxa).1 N, transfer_expansion m' hxc (hb' x hxa').1 N, hD]
    simp only [hM, smul_sub]
    abel
  set K := ‖complexify m.C‖ * ‖(characteristicMatrix m.A (x : ℂ))⁻¹‖ * ‖complexify m.B‖
  set K' := ‖complexify m'.C‖ * ‖(characteristicMatrix m'.A (x : ℂ))⁻¹‖ * ‖complexify m'.B‖
  have hlim : Filter.Tendsto (fun N : ℕ => (‖complexify m.A‖ / x) ^ N * K +
      (‖complexify m'.A‖ / x) ^ N * K') Filter.atTop (nhds 0) := by
    have h₁ := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hn hx0.le)
      ((div_lt_one hx0).mpr (by linarith))
    have h₂ := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hn' hx0.le)
      ((div_lt_one hx0).mpr (by linarith))
    simpa using (h₁.mul_const K).add (h₂.mul_const K')
  refine sub_eq_zero.mp (norm_le_zero_iff.mp (ge_of_tendsto' hlim fun N => ?_))
  have hxN : ‖((x : ℂ) ^ N)⁻¹‖ = (x ^ N)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx0.le]
  rw [hdiff N, norm_smul, hxN]
  calc (x ^ N)⁻¹ * ‖_ - _‖ ≤
      (x ^ N)⁻¹ * (‖complexify m.A‖ ^ N * K + ‖complexify m'.A‖ ^ N * K') := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add (norm_remainder_le m N _)
          (norm_remainder_le m' N _))
    _ = _ := by
        rw [div_pow, div_pow]
        field_simp

@[powerlib_foundation] private lemma transfer_eq_numerator (m : Plant n p) (s : ℂ) :
    transfer m s = ((complexify m.A).charpoly.eval s)⁻¹ •
      ((complexify m.C).map Polynomial.C * (charmatrix (complexify m.A)).adjugate *
        (complexify m.B).map Polynomial.C).map (Polynomial.eval s) + complexify m.D := by
  have hchar : (Polynomial.evalRingHom s).mapMatrix (charmatrix (complexify m.A)) =
      characteristicMatrix m.A s := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [characteristicMatrix, charmatrix_apply_eq]
    · simp [characteristicMatrix, charmatrix_apply_ne _ _ _ h, Matrix.one_apply_ne h]
  have hadj : (charmatrix (complexify m.A)).adjugate.map (Polynomial.evalRingHom s) =
      (characteristicMatrix m.A s).adjugate := by
    rw [← hchar, ← RingHom.map_adjugate]
    rfl
  rw [transfer_eq_adjugate, det_characteristicMatrix]
  congr 2
  rw [show (Polynomial.eval s : Polynomial ℂ → ℂ) = Polynomial.evalRingHom s from rfl,
    Matrix.map_mul, Matrix.map_mul, hadj]
  congr 2 <;> ext <;> simp

@[powerlib_foundation] theorem transfer_eq_of_eventually_eq {m : Plant n p}
    {m' : Plant n' p} (h : ∃ s₁ : ℝ, ∀ x : ℝ, s₁ ≤ x → transfer m x = transfer m' x)
    (s : ℂ) (hs : (characteristicMatrix m.A s).det ≠ 0)
    (hs' : (characteristicMatrix m'.A s).det ≠ 0) : transfer m s = transfer m' s := by
  obtain ⟨s₁, hs₁⟩ := h
  obtain ⟨a, -, ha⟩ := resolvent_bound m
  obtain ⟨a', -, ha'⟩ := resolvent_bound m'
  have hnum := transfer_eq_numerator m
  have hnum' := transfer_eq_numerator m'
  have hdet := det_characteristicMatrix m.A
  have hdet' := det_characteristicMatrix m'.A
  generalize (complexify m.A).charpoly = χ at hnum hdet
  generalize (complexify m'.A).charpoly = χ' at hnum' hdet'
  generalize (complexify m.C).map Polynomial.C * (charmatrix (complexify m.A)).adjugate *
    (complexify m.B).map Polynomial.C = N at hnum
  generalize (complexify m'.C).map Polynomial.C * (charmatrix (complexify m'.A)).adjugate *
    (complexify m'.B).map Polynomial.C = N' at hnum'
  have key : ∀ z, χ.eval z ≠ 0 → χ'.eval z ≠ 0 → ∀ i j,
      (χ' * N i j + χ * χ' * Polynomial.C (complexify m.D i j) -
        (χ * N' i j + χ * χ' * Polynomial.C (complexify m'.D i j))).eval z =
      χ.eval z * χ'.eval z * (transfer m z i j - transfer m' z i j) := by
    intro z hz hz' i j
    rw [hnum z, hnum' z]
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    field_simp
  have hzero : ∀ i j, χ' * N i j + χ * χ' * Polynomial.C (complexify m.D i j) -
      (χ * N' i j + χ * χ' * Polynomial.C (complexify m'.D i j)) = 0 := by
    intro i j
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ ((Set.Ici_infinite (max (max a a') s₁)).image
      Complex.ofReal_injective.injOn)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxa₁, hx₁⟩ := max_le_iff.mp (Set.mem_Ici.mp hx)
    obtain ⟨hxa, hxa'⟩ := max_le_iff.mp hxa₁
    have hz := (ha x hxa).1
    have hz' := (ha' x hxa').1
    rw [hdet] at hz
    rw [hdet'] at hz'
    show Polynomial.IsRoot _ _
    rw [Polynomial.IsRoot, key x hz hz' i j, hs₁ x hx₁, sub_self, mul_zero]
  rw [hdet] at hs
  rw [hdet'] at hs'
  ext i j
  have e := key s hs hs' i j
  rw [hzero i j, Polynomial.eval_zero] at e
  exact sub_eq_zero.mp ((mul_eq_zero.mp e.symm).resolve_left (mul_ne_zero hs hs'))

@[powerlib_foundation] theorem transfer_eq_iff_markov_eq {m : Plant n p}
    {m' : Plant n' p} :
    (∀ s : ℂ, (characteristicMatrix m.A s).det ≠ 0 → (characteristicMatrix m'.A s).det ≠ 0 →
      transfer m s = transfer m' s) ↔ m.D = m'.D ∧ ∀ k, markov m k = markov m' k := by
  refine ⟨fun h => ?_, fun ⟨hD, hM⟩ =>
    transfer_eq_of_eventually_eq (transfer_eventually_eq_of_markov_eq hD hM)⟩
  obtain ⟨a, -, ha⟩ := resolvent_bound m
  obtain ⟨a', -, ha'⟩ := resolvent_bound m'
  exact markov_eq_of_transfer_eventually_eq ⟨max a a', fun x hx =>
    h x (ha x (le_of_max_le_left hx)).1 (ha' x (le_of_max_le_right hx)).1⟩

section Minimal

def obsv (A : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin p) (Fin n) ℝ) (N : ℕ) :
    Matrix (Fin N × Fin p) (Fin n) ℝ :=
  Matrix.of fun ki j => (C * A ^ (ki.1 : ℕ)) ki.2 j

def ctrb (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ) (N : ℕ) :
    Matrix (Fin n) (Fin N × Fin p) ℝ :=
  Matrix.of fun i kj => (A ^ (kj.1 : ℕ) * B) i kj.2

@[powerlib_foundation] private lemma obsv_mul {β : Type*} (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (N : ℕ) (X : Matrix (Fin n) β ℝ) :
    obsv A C N * X = Matrix.of fun ki j => (C * A ^ (ki.1 : ℕ) * X) ki.2 j := by
  ext ⟨k, i⟩ j
  simp [obsv, Matrix.mul_apply]

@[powerlib_foundation] private lemma mul_ctrb {β : Type*} [Fintype β]
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ) (N : ℕ)
    (X : Matrix β (Fin n) ℝ) :
    X * ctrb A B N = Matrix.of fun i kj => (X * A ^ (kj.1 : ℕ) * B) i kj.2 := by
  ext i ⟨k, j⟩
  simp only [Matrix.of_apply]
  rw [Matrix.mul_assoc]
  simp [ctrb, Matrix.mul_apply]

@[powerlib_foundation] private lemma hankel (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) (C : Matrix (Fin p) (Fin n) ℝ) (N₁ N₂ r : ℕ) :
    obsv A C N₁ * A ^ r * ctrb A B N₂ =
      Matrix.of fun ki lj => (C * A ^ ((ki.1 : ℕ) + r + lj.1) * B) ki.2 lj.2 := by
  rw [mul_ctrb]
  ext ⟨k, i⟩ ⟨l, j⟩
  simp only [Matrix.of_apply, Matrix.mul_assoc]
  rw [obsv_mul]
  simp only [Matrix.of_apply, pow_add, Matrix.mul_assoc]

@[powerlib_foundation] theorem ctrb_eq (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) : ctrb A B n = controllabilityMatrix A B := rfl

@[powerlib_foundation] theorem obsv_eq (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) : obsv A C n = observabilityMatrix A C := rfl

@[powerlib_foundation] private lemma ctrb_right_inverse {A : Matrix (Fin n) (Fin n) ℝ}
    {B : Matrix (Fin n) (Fin p) ℝ} (h : IsControllable A B) :
    ∃ R : Matrix (Fin n × Fin p) (Fin n) ℝ, ctrb A B n * R = 1 := by
  rw [ctrb_eq]
  exact Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    ((MatrixAlgebra.mulVec_range_top_iff_rank_eq_card_rows _).mpr (by
      rw [Fintype.card_fin]
      exact (isControllable_iff_controllabilityMatrix_rank_eq A B).mp h))

@[powerlib_foundation] private lemma obsv_left_inverse {A : Matrix (Fin n) (Fin n) ℝ}
    {C : Matrix (Fin p) (Fin n) ℝ} (h : IsObservable A C) :
    ∃ L : Matrix (Fin n) (Fin n × Fin p) ℝ, L * obsv A C n = 1 := by
  have hr : (observabilityMatrix A C)ᵀ.rank = Fintype.card (Fin n) := by
    rw [Matrix.rank_transpose, Fintype.card_fin]
    exact (isObservable_iff_observabilityMatrix_rank_eq A C).mp h
  rw [obsv_eq]
  refine Matrix.vecMul_surjective_iff_exists_left_inverse.mp fun y => ?_
  obtain ⟨x, hx⟩ := (MatrixAlgebra.mulVec_range_top_iff_rank_eq_card_rows _).mpr hr y
  exact ⟨x, by simpa only [Matrix.mulVec_transpose] using hx⟩

@[powerlib_foundation] theorem similar_of_markov_eq {m : Plant n p}
    {m' : Plant n' p}
    (hc : IsControllable m.A m.B) (ho : IsObservable m.A m.C)
    (hc' : IsControllable m'.A m'.B) (ho' : IsObservable m'.A m'.C)
    (hD : m.D = m'.D) (hM : ∀ k, markov m k = markov m' k) : Similar m m' := by
  obtain ⟨R, hR⟩ := ctrb_right_inverse hc
  obtain ⟨R', hR'⟩ := ctrb_right_inverse hc'
  obtain ⟨L, hL⟩ := obsv_left_inverse ho
  obtain ⟨L', hL'⟩ := obsv_left_inverse ho'
  have hH : ∀ N₁ N₂ r, obsv m.A m.C N₁ * m.A ^ r * ctrb m.A m.B N₂ =
      obsv m'.A m'.C N₁ * m'.A ^ r * ctrb m'.A m'.B N₂ := by
    intro N₁ N₂ r
    rw [hankel, hankel]
    ext ⟨k, i⟩ ⟨l, j⟩
    exact congrFun (congrFun (hM _) i) j
  have hH0 : ∀ N₁ N₂, obsv m.A m.C N₁ * ctrb m.A m.B N₂ =
      obsv m'.A m'.C N₁ * ctrb m'.A m'.B N₂ := by
    intro N₁ N₂
    simpa only [pow_zero, Matrix.mul_one] using hH N₁ N₂ 0
  set T := L' * obsv m.A m.C n' with hT
  set S := L * obsv m'.A m'.C n with hS
  have hTK : ∀ N, T * ctrb m.A m.B N = ctrb m'.A m'.B N := by
    intro N
    rw [hT, Matrix.mul_assoc, hH0, ← Matrix.mul_assoc, hL', Matrix.one_mul]
  have hSK : ∀ N, S * ctrb m'.A m'.B N = ctrb m.A m.B N := by
    intro N
    rw [hS, Matrix.mul_assoc, ← hH0, ← Matrix.mul_assoc, hL, Matrix.one_mul]
  have hTS : T * S = 1 := by
    calc T * S = T * S * (ctrb m'.A m'.B n' * R') := by rw [hR', Matrix.mul_one]
      _ = T * (S * ctrb m'.A m'.B n') * R' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hSK, hTK, hR']
  have hST : S * T = 1 := by
    calc S * T = S * T * (ctrb m.A m.B n * R) := by rw [hR, Matrix.mul_one]
      _ = S * (T * ctrb m.A m.B n) * R := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hTK, hSK, hR]
  have hB : T * m.B = m'.B := by
    have hOB : obsv m.A m.C n' * m.B = obsv m'.A m'.C n' * m'.B := by
      rw [obsv_mul, obsv_mul]
      ext ⟨k, i⟩ j
      exact congrFun (congrFun (hM k) i) j
    rw [hT, Matrix.mul_assoc, hOB, ← Matrix.mul_assoc, hL', Matrix.one_mul]
  have hC : m'.C * T = m.C := by
    have hCK : m'.C * ctrb m'.A m'.B n = m.C * ctrb m.A m.B n := by
      rw [mul_ctrb, mul_ctrb]
      ext i ⟨l, j⟩
      exact (congrFun (congrFun (hM l) i) j).symm
    calc m'.C * T = m'.C * T * (ctrb m.A m.B n * R) := by rw [hR, Matrix.mul_one]
      _ = m'.C * (T * ctrb m.A m.B n) * R := by simp only [Matrix.mul_assoc]
      _ = m.C := by rw [hTK, hCK, Matrix.mul_assoc, hR, Matrix.mul_one]
  have hA : T * m.A = m'.A * T := by
    have hshift : T * (m.A * ctrb m.A m.B n) = m'.A * ctrb m'.A m'.B n := by
      calc T * (m.A * ctrb m.A m.B n) = L' * (obsv m.A m.C n' * m.A ^ 1 * ctrb m.A m.B n) := by
            rw [hT, pow_one]
            simp only [Matrix.mul_assoc]
        _ = L' * (obsv m'.A m'.C n' * m'.A ^ 1 * ctrb m'.A m'.B n) := by rw [hH]
        _ = m'.A * ctrb m'.A m'.B n := by
            rw [pow_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hL', Matrix.one_mul]
    calc T * m.A = T * m.A * (ctrb m.A m.B n * R) := by rw [hR, Matrix.mul_one]
      _ = T * (m.A * ctrb m.A m.B n) * R := by simp only [Matrix.mul_assoc]
      _ = m'.A * (T * ctrb m.A m.B n) * R := by rw [hshift, hTK]
      _ = m'.A * T := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hR, Matrix.mul_one]
  refine ⟨T, S, hTS, hST, Plant.ext ?_ hB.symm ?_ hD.symm⟩
  · show m'.A = T * m.A * S
    rw [hA, Matrix.mul_assoc, hTS, Matrix.mul_one]
  · show m'.C = m.C * S
    rw [← hC, Matrix.mul_assoc, hTS, Matrix.mul_one]

@[powerlib_foundation] theorem similar_iff_transfer_eq {m : Plant n p}
    {m' : Plant n' p}
    (hc : IsControllable m.A m.B) (ho : IsObservable m.A m.C)
    (hc' : IsControllable m'.A m'.B) (ho' : IsObservable m'.A m'.C) :
    Similar m m' ↔ ∀ s : ℂ, (characteristicMatrix m.A s).det ≠ 0 →
      (characteristicMatrix m'.A s).det ≠ 0 → transfer m s = transfer m' s := by
  refine ⟨fun h s _ _ => (h.transfer_eq s).symm, fun h => ?_⟩
  obtain ⟨a, -, ha⟩ := resolvent_bound m
  obtain ⟨a', -, ha'⟩ := resolvent_bound m'
  obtain ⟨hD, hM⟩ := markov_eq_of_transfer_eventually_eq ⟨max a a', fun x hx =>
    h x (ha x (le_of_max_le_left hx)).1 (ha' x (le_of_max_le_right hx)).1⟩
  exact similar_of_markov_eq hc ho hc' ho' hD hM

def basisMatrix {r : ℕ} {V : Submodule ℝ (Fin n → ℝ)} (b : Module.Basis (Fin r) ℝ V) :
    Matrix (Fin n) (Fin r) ℝ :=
  Matrix.of fun i j => (b j : Fin n → ℝ) i

@[powerlib_foundation] private lemma exists_coords {r : ℕ} {β : Type*}
    {V : Submodule ℝ (Fin n → ℝ)} (b : Module.Basis (Fin r) ℝ V) (M : Matrix (Fin n) β ℝ)
    (hM : ∀ j, (fun i => M i j) ∈ V) : ∃ M' : Matrix (Fin r) β ℝ, basisMatrix b * M' = M := by
  refine ⟨Matrix.of fun l j => b.repr ⟨fun i => M i j, hM j⟩ l, ?_⟩
  ext i j
  have h := congrArg (fun y : V => (y : Fin n → ℝ) i) (b.sum_repr ⟨fun i => M i j, hM j⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  rw [← h]
  simp only [basisMatrix, Matrix.mul_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

@[powerlib_foundation] theorem reduce_uncontrollable {m : Plant n p}
    (h : ¬ IsControllable m.A m.B) :
    ∃ (r : ℕ) (m' : Plant r p), r < n ∧ m'.D = m.D ∧
      ∀ k, markov m' k = markov m k := by
  set V := reachableSubspace m.A m.B
  let b := Module.finBasis ℝ V
  have hinv := (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp
    (reachableSubspace_invariant m.A m.B)
  obtain ⟨Ar, hAr⟩ := exists_coords b (m.A * basisMatrix b) fun j => by
    have hcol : (fun i => (m.A * basisMatrix b) i j) = m.A *ᵥ (b j : Fin n → ℝ) := by
      funext i
      simp [basisMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [hcol]
    exact hinv _ (b j).2
  obtain ⟨Br, hBr⟩ := exists_coords b m.B fun j => by
    have hcol : (fun i => m.B i j) = m.B *ᵥ Pi.single j 1 := by
      funext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hcol]
    exact range_B_le_reachableSubspace m.A m.B ⟨Pi.single j 1, rfl⟩
  refine ⟨Module.finrank ℝ V, ⟨Ar, Br, m.C * basisMatrix b, m.D⟩, ?_, rfl, fun k => ?_⟩
  · have hV : V ≠ ⊤ := fun hV =>
      h ((reachableSubspace_eq_top_iff_isControllable m.A m.B).mp hV)
    simpa using Submodule.finrank_lt hV
  · have hpow : ∀ k, m.A ^ k * basisMatrix b = basisMatrix b * Ar ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, ← hAr, Matrix.mul_assoc,
          ← pow_succ']
    calc m.C * basisMatrix b * Ar ^ k * Br = m.C * (basisMatrix b * Ar ^ k) * Br := by
          simp only [Matrix.mul_assoc]
      _ = m.C * (m.A ^ k * basisMatrix b) * Br := by rw [hpow]
      _ = m.C * m.A ^ k * (basisMatrix b * Br) := by simp only [Matrix.mul_assoc]
      _ = markov m k := by rw [hBr, markov]

def Plant.dual (m : Plant n p) : Plant n p := ⟨m.Aᵀ, m.Cᵀ, m.Bᵀ, m.Dᵀ⟩

@[powerlib_foundation] theorem markov_dual (m : Plant n p) (k : ℕ) :
    markov (Plant.dual m) k = (markov m k)ᵀ := by
  simp [markov, Plant.dual, Matrix.transpose_mul, Matrix.transpose_pow, Matrix.mul_assoc]

@[powerlib_foundation] theorem isObservable_iff_isControllable_transpose
    (A : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin p) (Fin n) ℝ) :
    IsObservable A C ↔ IsControllable Aᵀ Cᵀ := by
  have hO : observabilityMatrix A C =
      (controllabilityMatrix Aᵀ Cᵀ)ᵀ := by
    ext ⟨k, i⟩ j
    simp [observabilityMatrix, controllabilityMatrix,
      ← Matrix.transpose_pow, ← Matrix.transpose_mul]
  rw [isObservable_iff_observabilityMatrix_rank_eq,
    isControllable_iff_controllabilityMatrix_rank_eq, hO, Matrix.rank_transpose]

@[powerlib_foundation] private lemma reduce_unobservable {m : Plant n p}
    (h : ¬ IsObservable m.A m.C) :
    ∃ (r : ℕ) (m' : Plant r p), r < n ∧ m'.D = m.D ∧
      ∀ k, markov m' k = markov m k := by
  have hd : ¬ IsControllable (Plant.dual m).A (Plant.dual m).B := by
    show ¬ IsControllable m.Aᵀ m.Cᵀ
    rwa [← isObservable_iff_isControllable_transpose]
  obtain ⟨r, m₁, hr, hD, hM⟩ := reduce_uncontrollable hd
  refine ⟨r, Plant.dual m₁, hr, ?_, fun k => ?_⟩
  · simp [Plant.dual, hD]
  · rw [markov_dual, hM, markov_dual, Matrix.transpose_transpose]

@[powerlib_foundation] theorem exists_minimal_markov (m : Plant n p) :
    ∃ (n' : ℕ) (m' : Plant n' p), n' ≤ n ∧
      IsControllable m'.A m'.B ∧ IsObservable m'.A m'.C ∧
        m'.D = m.D ∧ ∀ k, markov m' k = markov m k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hc : IsControllable m.A m.B
    · by_cases ho : IsObservable m.A m.C
      · exact ⟨n, m, le_rfl, hc, ho, rfl, fun _ => rfl⟩
      · obtain ⟨r, m₁, hr, hD, hM⟩ := reduce_unobservable ho
        obtain ⟨n', m', hn', hc', ho', hD', hM'⟩ := ih r hr m₁
        exact ⟨n', m', hn'.trans hr.le, hc', ho', hD'.trans hD, fun k => (hM' k).trans (hM k)⟩
    · obtain ⟨r, m₁, hr, hD, hM⟩ := reduce_uncontrollable hc
      obtain ⟨n', m', hn', hc', ho', hD', hM'⟩ := ih r hr m₁
      exact ⟨n', m', hn'.trans hr.le, hc', ho', hD'.trans hD, fun k => (hM' k).trans (hM k)⟩

@[powerlib_foundation] theorem exists_minimal_realization (m : Plant n p) :
    ∃ (n' : ℕ) (m' : Plant n' p), n' ≤ n ∧
      IsControllable m'.A m'.B ∧ IsObservable m'.A m'.C ∧
        ∀ s : ℂ, (characteristicMatrix m'.A s).det ≠ 0 → (characteristicMatrix m.A s).det ≠ 0 →
          transfer m' s = transfer m s := by
  obtain ⟨n', m', hn, hc, ho, hD, hM⟩ := exists_minimal_markov m
  exact ⟨n', m', hn, hc, ho, transfer_eq_iff_markov_eq.mpr ⟨hD, hM⟩⟩

@[powerlib_foundation] theorem controllable_observable_iff_minimal
    {m : Plant n p} :
    (IsControllable m.A m.B ∧ IsObservable m.A m.C) ↔
      ∀ (n₂ : ℕ) (m₂ : Plant n₂ p),
        (∀ s : ℂ, (characteristicMatrix m.A s).det ≠ 0 → (characteristicMatrix m₂.A s).det ≠ 0 →
          transfer m s = transfer m₂ s) → n ≤ n₂ := by
  constructor
  · rintro ⟨hc, ho⟩ n₂ m₂ h
    obtain ⟨hD, hM⟩ := transfer_eq_iff_markov_eq.mp h
    obtain ⟨n₃, m₃, hn₃, hc₃, ho₃, hD₃, hM₃⟩ := exists_minimal_markov m₂
    obtain ⟨T, S, hTS, hST, -⟩ := similar_of_markov_eq hc ho hc₃ ho₃ (hD.trans hD₃.symm)
      fun k => (hM k).trans (hM₃ k).symm
    have hcard := Fintype.card_congr (Matrix.indexEquivOfInv hST hTS)
    simp only [Fintype.card_fin] at hcard
    omega
  · intro h
    by_contra hco
    rcases not_and_or.mp hco with hc | ho
    · obtain ⟨r, m', hr, hD, hM⟩ := reduce_uncontrollable hc
      exact absurd (h r m' (transfer_eq_iff_markov_eq.mpr ⟨hD.symm, fun k => (hM k).symm⟩))
        (by omega)
    · obtain ⟨r, m', hr, hD, hM⟩ := reduce_unobservable ho
      exact absurd (h r m' (transfer_eq_iff_markov_eq.mpr ⟨hD.symm, fun k => (hM k).symm⟩))
        (by omega)
end Minimal

/-- A plant is minimal when it is controllable and observable. -/
def Plant.Minimal (m : Plant n p) : Prop := IsControllable m.A m.B ∧ IsObservable m.A m.C

/-- On minimal plants, equal transfer functions decide stability: the observation sees every
mode. -/
@[powerlib_foundation] theorem isHurwitz_iff_of_transfer_eq {m : Plant n p} {m' : Plant n' p}
    (hm : m.Minimal) (hm' : m'.Minimal)
    (h : ∀ s : ℂ, (characteristicMatrix m.A s).det ≠ 0 → (characteristicMatrix m'.A s).det ≠ 0 →
      transfer m s = transfer m' s) : IsHurwitz m.A ↔ IsHurwitz m'.A :=
  ((similar_iff_transfer_eq hm.1 hm.2 hm'.1 hm'.2).mpr h).isHurwitz_iff.symm

/-- On minimal plants, the transfer function certifies every behavioural sentence: every minimal
plant with the same transfer function is similar, hence satisfies the same sentences. -/
@[powerlib_foundation] theorem transfer_certified {m : Plant n p} (hm : m.Minimal)
    {P : Flow.Property} (h : P.holds (affineLinearVectorField m.A 0) 0) :
    transfer m ∈ TMIO.certify (Function.graph fun m : {m : Plant n p // m.Minimal} => transfer m.1)
      {m | P.holds (affineLinearVectorField m.1.A 0) 0} := by
  rw [(connection_proof% TMIO.mem_certify)]
  rintro ⟨m', hm'⟩ heq
  have heq' : transfer m' = transfer m := heq
  have hs : Similar m m' :=
    (similar_iff_transfer_eq hm.1 hm.2 hm'.1 hm'.2).mpr fun s _ _ => congrFun heq'.symm s
  exact (hs.holds_iff P).mpr h

/-- The hidden mode is not minimal: the observation misses exactly such modes. -/
@[powerlib_foundation] theorem hiddenMode_not_minimal : ¬ hiddenMode.Minimal := by
  rintro ⟨hc, -⟩
  have h := (isControllable_iff_controllabilityMatrix_rank_eq hiddenMode.A hiddenMode.B).mp hc
  have h0 : controllabilityMatrix hiddenMode.A hiddenMode.B = 0 := by
    ext i ⟨k, j⟩
    simp [controllabilityMatrix, hiddenMode]
  rw [h0, Matrix.rank_zero] at h
  exact absurd h (by norm_num)

end powerlib.Linear
