import theorem.ParametricResonance.SaturatedAmplitude

/-! # The zeros of the cubic amplitude equation: the trivial state and the pairs `±w*`

`theorem/ParametricResonance/SaturatedAmplitude.lean` derives the amplitudes `|z|² = A` of the
phase-locked states of the cubic 2:1 amplitude equation
`ż = −(σ + jΔ) z + c z̄ + (−η + jβ)|z|² z` (`Saturation.exists_norm_sq_eq_iff`,
`Saturation.shift_states`) and their stability. Here the zero set itself is described. The field
is odd, `F(−z) = −F(z)`, and for `c ≠ 0` each admissible amplitude carries exactly the two locked
states `w*` and `−w*`: from `c z̄ = K z` with `K = (σ + ηA) + j(Δ − βA)` one gets `cA = Kz²`, so
`z²` is fixed by `A` (`zero_pair_iff`). In the oscillator the pair `±w*` is one oscillation shifted
by half its period. Under a pure frequency shift (`η = 0`, `β ≠ 0`, the Duffing and swing case)
the zeros are `0` and the pairs on the two amplitudes `A± = (Δ ± s)/β`, `s = √(|c|² − σ²)`
(`shift_zeros`); off the fold `|c| = σ` the number of zeros in the disc `|z| ≤ R` is `1 + 2N`,
`N` the number of the roots `A±` in `(0, R²]` (`shift_zeros_ncard`). A zero is degenerate (zero
Jacobian determinant) exactly when it is the trivial state on the first-order (linear) boundary
`σ² + Δ² = |c|²` or a locked state at the fold (`shift_det_eq_zero_iff`); off these parameter
sets all zeros are nondegenerate and the periodic-orbit theorems
(`Averaging.periodic_orbit_classification_compact`) apply to them.

Scope.
* The complex amplitude field `Saturation.ampField σ Δ c η β` (real `σ, Δ, η, β`, complex `c`)
  and its Jacobian `Saturation.ampJacobian` in the real coordinates `(Re z, Im z)`; static
  algebra of the zero set, no dynamics. The pair and counting statements need `c ≠ 0` (for
  `c = 0` a nonzero zero comes with its whole circle `|z| = |w*|` of zeros).
* Generic mathematics, no model family.

Source: first-order averaging of parametrically excited oscillators with cubic nonlinearity
(Nayfeh–Mook, *Nonlinear Oscillations*, Ch. 5: the frequency–response curves, the trivial and the
two nontrivial branches, the two phases `φ` and `φ + π` of each nontrivial branch); the amplitude
condition `Saturation.exists_norm_sq_eq_iff`, `Saturation.shift_states`, the Jacobian
determinants `Saturation.det_ampJacobian`, `Saturation.ampJacobian_zero`,
`ParametricResonance.det_slowFlowMatrix`.

Results.
* `ampField_zero`, `ampField_neg` — `F(0) = 0`, `F(−z) = −F(z)`.
* `zero_pair_iff` — for `c ≠ 0` and a zero `w ≠ 0`, the zeros of norm `|w|` are exactly `±w`.
* `exists_pair` — an admissible amplitude `A > 0` carries a pair: some `w` with `|w|² = A` and
  `{z : |z|² = A, F(z) = 0} = {w, −w}`, `w ≠ −w`.
* `shift_zeros` — `η = 0`, `β ≠ 0`, `c ≠ 0`: every zero is `0` or has `|z|² = A±` (with
  `σ² ≤ |c|²`), and each positive `A±` carries exactly a pair `±w`.
* `shift_zeros_finite` — the zero set is finite.
* `shift_zeros_ncard` — off the fold (`σ² < |c|²`) the disc `|z| ≤ R` contains `1 + 2N` zeros.
* `shift_det_eq_zero_iff`, `shift_det_ne_zero`, `zero_det_ne_zero` — a zero is degenerate exactly
  at the first-order boundary `σ² + Δ² = |c|²` (the trivial zero) or at the fold `σ² = |c|²`
  (the nontrivial zeros).
-/

noncomputable section
namespace powerlib.ParametricResonance.Saturation

open Complex

variable {σ Δ η β : ℝ} {c : ℂ}

/-- The trivial state is a zero of the amplitude field. -/
@[tmio M, powerlib_foundation] theorem ampField_zero (σ Δ : ℝ) (c : ℂ) (η β : ℝ) :
    ampField σ Δ c η β 0 = 0 := by
  simp [ampField, slowFlowField]

/-- **The amplitude field is odd**: `F(−z) = −F(z)`. -/
@[tmio M, powerlib_foundation] theorem ampField_neg (σ Δ : ℝ) (c : ℂ) (η β : ℝ) (z : ℂ) :
    ampField σ Δ c η β (-z) = -ampField σ Δ c η β z := by
  simp only [ampField, slowFlowField, norm_neg, map_neg]
  ring

/-- **Locked states come in pairs `±w`.** For `c ≠ 0` and a zero `w ≠ 0` of the amplitude field,
a point `z` with `|z| = |w|` is a zero iff `z = w` or `z = −w`: from `c w̄ = K w`,
`K = (σ + η|w|²) + j(Δ − β|w|²)`, follows `c|w|² = K w²`, so `z² = w²`. -/
@[tmio M, powerlib_foundation] theorem zero_pair_iff (hc : c ≠ 0) {w z : ℂ}
    (hw : ampField σ Δ c η β w = 0) (hw0 : w ≠ 0) (hn : ‖z‖ = ‖w‖) :
    ampField σ Δ c η β z = 0 ↔ z = w ∨ z = -w := by
  constructor
  · intro hz
    rw [ampField_eq, sub_eq_zero] at hw hz
    rw [hn] at hz
    set K : ℂ := ((σ + η * ‖w‖ ^ 2 : ℝ) : ℂ) + ((Δ - β * ‖w‖ ^ 2 : ℝ) : ℂ) * I with hK
    have hconj : ∀ u : ℂ, (starRingEnd ℂ) u * u = ((‖u‖ ^ 2 : ℝ) : ℂ) := fun u => by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have h1 : c * ((‖w‖ ^ 2 : ℝ) : ℂ) = K * w ^ 2 := by
      rw [← hconj, ← mul_assoc, hw]; ring
    have h2 : c * ((‖w‖ ^ 2 : ℝ) : ℂ) = K * z ^ 2 := by
      rw [← hn, ← hconj, ← mul_assoc, hz]; ring
    have hK0 : K ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hw
      have := (mul_eq_zero.mp hw).resolve_left hc
      exact hw0 (by simpa using this)
    have h3 : z ^ 2 = w ^ 2 := mul_left_cancel₀ hK0 (h2.symm.trans h1)
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h3
  · rintro (rfl | rfl)
    · exact hw
    · rw [ampField_neg, hw, neg_zero]

/-- **An admissible amplitude carries exactly one pair of locked states.** For `c ≠ 0` and
`A > 0` with `(σ + ηA)² + (Δ − βA)² = |c|²` there is `w` with `|w|² = A`, `w ≠ −w`, such that the
zeros of the amplitude field with `|z|² = A` are exactly `w` and `−w`. -/
@[tmio M, powerlib_foundation] theorem exists_pair (hc : c ≠ 0) {A : ℝ} (hA : 0 < A)
    (h : (σ + η * A) ^ 2 + (Δ - β * A) ^ 2 = ‖c‖ ^ 2) :
    ∃ w : ℂ, ‖w‖ ^ 2 = A ∧ w ≠ -w ∧
      ∀ z : ℂ, (‖z‖ ^ 2 = A ∧ ampField σ Δ c η β z = 0) ↔ (z = w ∨ z = -w) := by
  obtain ⟨w, hwA, hw⟩ := (exists_norm_sq_eq_iff hA).mpr h
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hwA
    linarith [hwA ▸ hA]
  refine ⟨w, hwA, fun h' => hw0 (by linear_combination h' / 2), fun z => ?_⟩
  constructor
  · rintro ⟨hzA, hz⟩
    have hn : ‖z‖ = ‖w‖ := by
      have := hzA.trans hwA.symm
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this
    exact (zero_pair_iff hc hw hw0 hn).mp hz
  · intro hz
    have hn : ‖z‖ = ‖w‖ := by rcases hz with rfl | rfl <;> simp
    exact ⟨by rw [hn, hwA], (zero_pair_iff hc hw hw0 hn).mpr hz⟩

/-- **The zeros under a pure frequency shift** (`η = 0`, `β ≠ 0`, `c ≠ 0`,
`s = √(|c|² − σ²)`). Every zero is the trivial state or has `|z|² = (Δ + s)/β` or
`|z|² = (Δ − s)/β`, with `σ² ≤ |c|²`; conversely each of these amplitudes that is positive (for
`σ² ≤ |c|²`) carries exactly two zeros `w`, `−w` (`Saturation.shift_states`, `exists_pair`). -/
@[tmio M, powerlib_foundation] theorem shift_zeros (hc : c ≠ 0) (hβ : β ≠ 0) :
    (∀ z : ℂ, ampField σ Δ c 0 β z = 0 → z = 0 ∨ (σ ^ 2 ≤ ‖c‖ ^ 2 ∧
      (‖z‖ ^ 2 = (Δ + √(‖c‖ ^ 2 - σ ^ 2)) / β ∨ ‖z‖ ^ 2 = (Δ - √(‖c‖ ^ 2 - σ ^ 2)) / β))) ∧
    ∀ A : ℝ, 0 < A → σ ^ 2 ≤ ‖c‖ ^ 2 →
      (A = (Δ + √(‖c‖ ^ 2 - σ ^ 2)) / β ∨ A = (Δ - √(‖c‖ ^ 2 - σ ^ 2)) / β) →
      ∃ w : ℂ, ‖w‖ ^ 2 = A ∧ w ≠ -w ∧
        ∀ z : ℂ, (‖z‖ ^ 2 = A ∧ ampField σ Δ c 0 β z = 0) ↔ (z = w ∨ z = -w) := by
  refine ⟨fun z hz => ?_, fun A hA hD hAe => ?_⟩
  · by_cases hz0 : z = 0
    · exact Or.inl hz0
    · exact Or.inr ((shift_states hβ (pow_pos (norm_pos_iff.mpr hz0) 2)).mp ⟨z, rfl, hz⟩)
  · obtain ⟨z, hzA, hz⟩ := (shift_states hβ hA).mpr ⟨hD, hAe⟩
    have h := (exists_norm_sq_eq_iff (η := 0) hA).mp ⟨z, hzA, hz⟩
    exact exists_pair hc hA h

/-- The zero set of the amplitude field under a pure frequency shift is finite (`c ≠ 0`,
`β ≠ 0`). -/
@[tmio M, powerlib_foundation] theorem shift_zeros_finite (hc : c ≠ 0) (hβ : β ≠ 0) :
    {z : ℂ | ampField σ Δ c 0 β z = 0}.Finite := by
  set s := √(‖c‖ ^ 2 - σ ^ 2)
  have hP : ∀ A : ℝ, {z : ℂ | ‖z‖ ^ 2 = A ∧ ampField σ Δ c 0 β z = 0}.Finite := by
    intro A
    rcases Set.eq_empty_or_nonempty {z : ℂ | ‖z‖ ^ 2 = A ∧ ampField σ Δ c 0 β z = 0} with
      he | ⟨w, hwA, hw⟩
    · rw [he]; exact Set.finite_empty
    · by_cases hw0 : w = 0
      · subst hw0
        refine (Set.finite_singleton (0 : ℂ)).subset fun z hz => ?_
        have : ‖z‖ ^ 2 = 0 := by rw [hz.1, ← hwA, norm_zero]; ring
        simpa using this
      · refine (Set.toFinite ({w, -w} : Set ℂ)).subset fun z hz => ?_
        have hn : ‖z‖ = ‖w‖ :=
          (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hz.1.trans hwA.symm)
        exact (zero_pair_iff hc hw hw0 hn).mp hz.2
  refine (((Set.finite_singleton (0 : ℂ)).union (hP ((Δ + s) / β))).union
    (hP ((Δ - s) / β))).subset fun z hz => ?_
  rcases (shift_zeros hc hβ).1 z hz with h0 | ⟨-, h1 | h1⟩
  · exact Or.inl (Or.inl h0)
  · exact Or.inl (Or.inr ⟨h1, hz⟩)
  · exact Or.inr ⟨h1, hz⟩

@[tmio M, powerlib_foundation] private theorem pair_ncard (hc : c ≠ 0) (hβ : β ≠ 0) {A R : ℝ}
    (hD : σ ^ 2 ≤ ‖c‖ ^ 2)
    (hAe : A = (Δ + √(‖c‖ ^ 2 - σ ^ 2)) / β ∨ A = (Δ - √(‖c‖ ^ 2 - σ ^ 2)) / β) (hR : 0 ≤ R) :
    {z : ℂ | z ≠ 0 ∧ ‖z‖ ^ 2 = A ∧ ampField σ Δ c 0 β z = 0 ∧ ‖z‖ ≤ R}.ncard =
      if 0 < A ∧ A ≤ R ^ 2 then 2 else 0 := by
  split_ifs with h
  · obtain ⟨w, hwA, hww, hw⟩ := (shift_zeros (σ := σ) (Δ := Δ) hc hβ).2 A h.1 hD hAe
    have e : {z : ℂ | z ≠ 0 ∧ ‖z‖ ^ 2 = A ∧ ampField σ Δ c 0 β z = 0 ∧ ‖z‖ ≤ R} = {w, -w} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨-, hzA, hz, -⟩
        exact (hw z).mp ⟨hzA, hz⟩
      · intro hz'
        obtain ⟨hzA, hz⟩ := (hw z).mpr hz'
        refine ⟨fun h0 => ?_, hzA, hz, ?_⟩
        · rw [h0, norm_zero] at hzA; linarith [h.1]
        · have : ‖z‖ ^ 2 ≤ R ^ 2 := hzA ▸ h.2
          exact (sq_le_sq₀ (norm_nonneg _) hR).mp this
    rw [e, Set.ncard_pair hww]
  · have e : {z : ℂ | z ≠ 0 ∧ ‖z‖ ^ 2 = A ∧ ampField σ Δ c 0 β z = 0 ∧ ‖z‖ ≤ R} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hz0, hzA, -, hzR⟩
      refine h ⟨hzA ▸ pow_pos (norm_pos_iff.mpr hz0) 2, ?_⟩
      rw [← hzA]
      exact pow_le_pow_left₀ (norm_nonneg _) hzR 2
    rw [e, Set.ncard_empty]

/-- **The number of zeros in a disc.** Under a pure frequency shift (`η = 0`, `β ≠ 0`, `c ≠ 0`)
and off the fold (`σ² < |c|²`, so that the two amplitudes `A± = (Δ ± s)/β`,
`s = √(|c|² − σ²) > 0`, differ), the disc `|z| ≤ R` (`R ≥ 0`) contains exactly `1 + 2N` zeros of
the amplitude field: the trivial state and a pair `±w` for each of the `N` roots `A±` in
`(0, R²]`. (For `|c|² < σ²` the trivial state is the only zero, `Saturation.shift_exists_iff`.) -/
@[tmio M, powerlib_foundation] theorem shift_zeros_ncard (hc : c ≠ 0) (hβ : β ≠ 0)
    (hcs : σ ^ 2 < ‖c‖ ^ 2) {R : ℝ} (hR : 0 ≤ R) :
    {z : ℂ | ampField σ Δ c 0 β z = 0 ∧ ‖z‖ ≤ R}.ncard =
      1 + 2 * ((if 0 < (Δ + √(‖c‖ ^ 2 - σ ^ 2)) / β ∧ (Δ + √(‖c‖ ^ 2 - σ ^ 2)) / β ≤ R ^ 2
          then 1 else 0) +
        (if 0 < (Δ - √(‖c‖ ^ 2 - σ ^ 2)) / β ∧ (Δ - √(‖c‖ ^ 2 - σ ^ 2)) / β ≤ R ^ 2
          then 1 else 0)) := by
  set s := √(‖c‖ ^ 2 - σ ^ 2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  set Ap := (Δ + s) / β with hAp
  set Am := (Δ - s) / β with hAm
  have hApm : Ap ≠ Am := by
    rw [hAp, hAm]
    intro h
    have := (div_left_inj' hβ).mp h
    linarith
  set P : ℝ → Set ℂ := fun A => {z : ℂ | z ≠ 0 ∧ ‖z‖ ^ 2 = A ∧ ampField σ Δ c 0 β z = 0 ∧
    ‖z‖ ≤ R} with hP
  have hPf : ∀ A, (P A).Finite := fun A => (shift_zeros_finite hc hβ).subset fun z hz => hz.2.2.1
  have e : {z : ℂ | ampField σ Δ c 0 β z = 0 ∧ ‖z‖ ≤ R} = ({0} ∪ P Ap) ∪ P Am := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff, hP]
    constructor
    · rintro ⟨hz, hzR⟩
      rcases (shift_zeros hc hβ).1 z hz with h0 | ⟨-, h1 | h1⟩
      · exact Or.inl (Or.inl h0)
      · by_cases h0 : z = 0
        · exact Or.inl (Or.inl h0)
        · exact Or.inl (Or.inr ⟨h0, h1, hz, hzR⟩)
      · by_cases h0 : z = 0
        · exact Or.inl (Or.inl h0)
        · exact Or.inr ⟨h0, h1, hz, hzR⟩
    · rintro ((rfl | ⟨-, -, hz, hzR⟩) | ⟨-, -, hz, hzR⟩)
      · exact ⟨ampField_zero _ _ _ _ _, by rw [norm_zero]; exact hR⟩
      · exact ⟨hz, hzR⟩
      · exact ⟨hz, hzR⟩
  have hd1 : Disjoint ({0} : Set ℂ) (P Ap) :=
    Set.disjoint_left.mpr fun z hz hz' => hz'.1 hz
  have hd2 : Disjoint ({0} ∪ P Ap) (P Am) := by
    refine Set.disjoint_left.mpr fun z hz hz' => ?_
    rcases hz with hz | hz
    · exact hz'.1 hz
    · exact hApm (hz.2.1.symm.trans hz'.2.1)
  rw [e, Set.ncard_union_eq hd2 ((Set.finite_singleton _).union (hPf _)) (hPf _),
    Set.ncard_union_eq hd1 (Set.finite_singleton _) (hPf _), Set.ncard_singleton,
    pair_ncard hc hβ hcs.le (Or.inl rfl) hR, pair_ncard hc hβ hcs.le (Or.inr rfl) hR]
  split_ifs <;> norm_num

/-- **The degenerate zeros under a pure frequency shift.** For `β ≠ 0` a zero `z` of the amplitude
field has a singular Jacobian exactly at the first-order boundary (`z = 0`, `σ² + Δ² = |c|²`:
the determinant at `0` is `σ² + Δ² − |c|²`, `Saturation.ampJacobian_zero`) or at the fold
(`z ≠ 0`, `σ² = |c|²`: the determinant is `4|z|²β(β|z|² − Δ)`, `Saturation.det_ampJacobian`, and
the amplitude condition reads `σ² + (Δ − β|z|²)² = |c|²`). -/
@[tmio M, powerlib_foundation] theorem shift_det_eq_zero_iff (hβ : β ≠ 0) {z : ℂ}
    (hz : ampField σ Δ c 0 β z = 0) :
    (ampJacobian σ Δ c 0 β (toReal z)).det = 0 ↔
      (z = 0 ∧ σ ^ 2 + Δ ^ 2 = ‖c‖ ^ 2) ∨ (z ≠ 0 ∧ σ ^ 2 = ‖c‖ ^ 2) := by
  by_cases hz0 : z = 0
  · subst hz0
    rw [map_zero, ampJacobian_zero, det_slowFlowMatrix, sub_eq_zero]
    exact ⟨fun h => Or.inl ⟨rfl, h⟩, fun h => h.elim (fun h => h.2) fun h => (h.1 rfl).elim⟩
  · have hx : ampSystem σ Δ c 0 β (toReal z) = 0 := by rw [toReal_ampField, hz, map_zero]
    have hx0 : toReal z ≠ 0 := by rwa [Ne, ContinuousLinearEquiv.map_eq_zero_iff]
    rw [det_ampJacobian hx hx0, norm_toReal]
    have hA := (exists_norm_sq_eq_iff (η := 0) (pow_pos (norm_pos_iff.mpr hz0) 2)).mp
      ⟨z, rfl, hz⟩
    have hn : 0 < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz0) 2
    have e : 0 * σ - β * Δ + (0 ^ 2 + β ^ 2) * ‖z‖ ^ 2 = β * (β * ‖z‖ ^ 2 - Δ) := by ring
    rw [e]
    constructor
    · intro h
      refine Or.inr ⟨hz0, ?_⟩
      have h1 : β * ‖z‖ ^ 2 - Δ = 0 := by
        rcases mul_eq_zero.mp h with h2 | h2
        · exact absurd h2 (mul_ne_zero (by norm_num) hn.ne')
        · exact (mul_eq_zero.mp h2).resolve_left hβ
      have : Δ - β * ‖z‖ ^ 2 = 0 := by linarith
      rw [this] at hA
      linarith
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact (hz0 h).elim
      · have h1 : (Δ - β * ‖z‖ ^ 2) ^ 2 = 0 := by simp only [zero_mul, add_zero] at hA; linarith
        have h2 : β * ‖z‖ ^ 2 - Δ = 0 := by
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
          linarith
        rw [h2, mul_zero, mul_zero]

/-- **Off the fold, every nontrivial zero is nondegenerate**: under a pure frequency shift
(`η = 0`, `β ≠ 0`) with `σ² ≠ |c|²`, the Jacobian of a zero `z ≠ 0` is invertible
(`shift_det_eq_zero_iff`). -/
@[tmio M, powerlib_foundation] theorem shift_det_ne_zero (hβ : β ≠ 0) (hcs : σ ^ 2 ≠ ‖c‖ ^ 2)
    {z : ℂ} (hz : ampField σ Δ c 0 β z = 0) (hz0 : z ≠ 0) :
    (ampJacobian σ Δ c 0 β (toReal z)).det ≠ 0 := fun h =>
  ((shift_det_eq_zero_iff hβ hz).mp h).elim (fun h => hz0 h.1) fun h => hcs h.2

/-- **Off the first-order boundary, the trivial zero is nondegenerate** (`η = 0`, `β ≠ 0`,
`σ² + Δ² ≠ |c|²`, `shift_det_eq_zero_iff`). -/
@[tmio M, powerlib_foundation] theorem zero_det_ne_zero (hβ : β ≠ 0)
    (h : σ ^ 2 + Δ ^ 2 ≠ ‖c‖ ^ 2) : (ampJacobian σ Δ c 0 β (toReal 0)).det ≠ 0 := fun h' =>
  ((shift_det_eq_zero_iff hβ (ampField_zero σ Δ c 0 β)).mp h').elim (fun h'' => h h''.2)
    fun h'' => h''.1 rfl

end powerlib.ParametricResonance.Saturation
