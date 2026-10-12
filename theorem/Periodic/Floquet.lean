import theorem.Periodic.Transition

/-! # Floquet sufficient criterion for periodic linear time-varying systems

Foundation layer. System: `ẋ = A(t) x`, `x ∈ ℝ^X` (sup norm), with a continuous real
`T`-periodic state matrix `A` (`T > 0`), continuous time, forward solutions only. The
monodromy matrix is `monodromy A T 0 = Φ(T, 0)` of `theorem/Periodic/Transition.lean`; its
complex spectrum is the set of Floquet multipliers.

Main results:
* `uniformlyExponentiallyStable_of_spectralRadius_lt_one`: if the spectral radius of the
  complexified monodromy matrix is `< 1`, then there are `K` and `β > 0` with
  `‖Φ(t, s)‖ ≤ K e^{-β (t - s)}` for **all** `s ≤ t` (uniform in the initial time).
* `trajectory_decay_of_spectralRadius_lt_one`: the same bound for every forward solution,
  `‖x(t)‖ ≤ K e^{-β (t - s)} ‖x(s)‖`.

Only the sufficient direction is proved (no converse, no instability statement). The
contractive power `‖M^m‖ < 1` is LeanForControl's
`exists_pow_norm_lt_one_of_spectralRadius_lt_one` (Gelfand's formula), applied to the
complexified monodromy matrix with the `L∞` operator norm.

Source: work-sync theory/T-harmonic-linearization.md §1.6 (`|ρ_i| < 1` stability criterion);
projects/basin-guard/notes/concepts/guard-object.md §3 (`max |μ_i| = 1` as the threshold).
-/

noncomputable section
namespace powerlib.Periodic

open Set Matrix Function
open scoped Matrix.Norms.Operator

variable {X : Type*} [Fintype X] [DecidableEq X]

@[powerlib_foundation] theorem norm_map_algebraMap (P : Matrix X X ℝ) :
    ‖P.map (algebraMap ℝ ℂ)‖ = ‖P‖ := by
  rw [Matrix.linfty_opNorm_def, Matrix.linfty_opNorm_def]
  simp [Complex.nnnorm_real]

@[powerlib_foundation] theorem norm_pow_le_norm_one_mul {Q : Matrix X X ℝ} (k : ℕ) :
    ‖Q ^ k‖ ≤ ‖(1 : Matrix X X ℝ)‖ * ‖Q‖ ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    calc ‖Q ^ k * Q‖ ≤ ‖Q ^ k‖ * ‖Q‖ := norm_mul_le _ _
      _ ≤ ‖(1 : Matrix X X ℝ)‖ * ‖Q‖ ^ k * ‖Q‖ :=
        mul_le_mul_of_nonneg_right ih (norm_nonneg _)
      _ = _ := by ring

/-- Spectral radius `< 1` gives a contractive power (wraps LeanForControl
`exists_pow_norm_lt_one_of_spectralRadius_lt_one` on the complexification). -/
@[powerlib_foundation] theorem exists_pow_norm_lt_one (P : Matrix X X ℝ)
    (hρ : spectralRadius ℂ (P.map (algebraMap ℝ ℂ)) < 1) : ∃ m : ℕ, 0 < m ∧ ‖P ^ m‖ < 1 := by
  rcases isEmpty_or_nonempty X with hX | hX
  · refine ⟨1, one_pos, ?_⟩
    rw [Subsingleton.elim (P ^ 1) 0, norm_zero]
    norm_num
  · obtain ⟨m, hm, hlt⟩ := exists_pow_norm_lt_one_of_spectralRadius_lt_one
      (P.map (algebraMap ℝ ℂ)) hρ
    refine ⟨m, hm, ?_⟩
    have hmap : (P ^ m).map (algebraMap ℝ ℂ) = (P.map (algebraMap ℝ ℂ)) ^ m := by
      have h := map_pow ((algebraMap ℝ ℂ).mapMatrix (m := X)) P m
      simpa [RingHom.mapMatrix_apply] using h
    rw [← norm_map_algebraMap, hmap]
    exact hlt

/-- A contractive power gives geometric decay of all powers. -/
@[powerlib_foundation] theorem exists_pow_norm_le_exp {P : Matrix X X ℝ} {m : ℕ} (hm : 0 < m)
    (hq : ‖P ^ m‖ < 1) :
    ∃ C γ : ℝ, 0 ≤ C ∧ 0 < γ ∧ ∀ n : ℕ, ‖P ^ n‖ ≤ C * Real.exp (-(γ * n)) := by
  set q : ℝ := max ‖P ^ m‖ (1 / 2) with hq_def
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hq1 : q < 1 := max_lt hq (by norm_num)
  set γ₀ : ℝ := -Real.log q with hγ₀
  have hγ₀pos : 0 < γ₀ := by
    have := Real.log_neg hq0 hq1
    linarith
  set C₀ : ℝ := ∑ r ∈ Finset.range m, ‖P ^ r‖ with hC₀
  have hC₀nn : 0 ≤ C₀ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  refine ⟨‖(1 : Matrix X X ℝ)‖ * C₀ * Real.exp γ₀, γ₀ / m, by positivity,
    div_pos hγ₀pos hmR, fun n => ?_⟩
  set k := n / m
  set r := n % m
  have hn : n = m * k + r := (Nat.div_add_mod n m).symm
  have hr : r < m := Nat.mod_lt n hm
  have hPn : P ^ n = (P ^ m) ^ k * P ^ r := by rw [hn, pow_add, pow_mul]
  have hPr : ‖P ^ r‖ ≤ C₀ :=
    Finset.single_le_sum (f := fun r => ‖P ^ r‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_range.mpr hr)
  have hqk : ‖P ^ m‖ ^ k ≤ q ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) k
  have hqexp : q ^ k = Real.exp (-(γ₀ * k)) := by
    rw [hγ₀, neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hq0]
  have hkge : (n : ℝ) / m - 1 ≤ k := by
    have h1 : (n : ℝ) < m * (k + 1) := by
      have : n < m * (k + 1) := by rw [hn]; nlinarith
      exact_mod_cast this
    rw [div_sub_one hmR.ne', div_le_iff₀ hmR]
    linarith
  have hexp : Real.exp (-(γ₀ * k)) ≤ Real.exp γ₀ * Real.exp (-(γ₀ / m * n)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : γ₀ * ((n : ℝ) / m - 1) ≤ γ₀ * k := mul_le_mul_of_nonneg_left hkge hγ₀pos.le
    have e : γ₀ / m * n = γ₀ * ((n : ℝ) / m) := by ring
    rw [e]
    linarith
  calc ‖P ^ n‖ = ‖(P ^ m) ^ k * P ^ r‖ := by rw [hPn]
    _ ≤ ‖(P ^ m) ^ k‖ * ‖P ^ r‖ := norm_mul_le _ _
    _ ≤ (‖(1 : Matrix X X ℝ)‖ * ‖P ^ m‖ ^ k) * C₀ :=
        mul_le_mul (norm_pow_le_norm_one_mul k) hPr (norm_nonneg _) (by positivity)
    _ ≤ (‖(1 : Matrix X X ℝ)‖ * Real.exp (-(γ₀ * k))) * C₀ := by
        rw [← hqexp]; gcongr
    _ ≤ (‖(1 : Matrix X X ℝ)‖ * (Real.exp γ₀ * Real.exp (-(γ₀ / m * n)))) * C₀ := by
        gcongr
    _ = ‖(1 : Matrix X X ℝ)‖ * C₀ * Real.exp γ₀ * Real.exp (-(γ₀ / m * n)) := by ring

variable {A : ℝ → Matrix X X ℝ} {T : ℝ}

/-- **Floquet sufficient criterion.** For a continuous `T`-periodic state matrix, Floquet
multipliers strictly inside the unit disk give uniform exponential stability of `ẋ = A(t) x`,
stated on the transition matrix: `‖Φ(t, s)‖ ≤ K e^{-β (t - s)}` for all `s ≤ t`, with `β > 0`. -/
@[powerlib_foundation] theorem uniformlyExponentiallyStable_of_spectralRadius_lt_one
    (hA : Continuous A) (hP : Periodic A T) (hT : 0 < T)
    (hρ : spectralRadius ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ)) < 1) :
    ∃ K β : ℝ, 0 < β ∧ ∀ s t, s ≤ t → ‖transition A t s‖ ≤ K * Real.exp (-(β * (t - s))) := by
  obtain ⟨M, hM⟩ := exists_bound_of_periodic hA hP hT
  obtain ⟨m, hm, hlt⟩ := exists_pow_norm_lt_one _ hρ
  obtain ⟨C, γ, hC, hγ, hpow⟩ := exists_pow_norm_le_exp hm hlt
  set E : ℝ := ‖(1 : Matrix X X ℝ)‖ * Real.exp (Real.toNNReal M * T) with hE
  have hE0 : 0 ≤ E := by positivity
  have hwin : ∀ s t, s ≤ t → t - s ≤ T → ‖transition A t s‖ ≤ E := by
    intro s t hst hts
    refine (norm_transition_le hA hM hst).trans ?_
    rw [hE]
    gcongr
  set β : ℝ := γ / T with hβ
  have hβpos : 0 < β := div_pos hγ hT
  refine ⟨E * E * C * Real.exp (2 * γ) + E * Real.exp (β * T), β, hβpos, fun s t hst => ?_⟩
  set k₀ : ℤ := ⌈s / T⌉ with hk₀
  set a : ℝ := k₀ * T with ha
  have hsa : s ≤ a := by
    have := Int.le_ceil (s / T)
    calc s = s / T * T := by field_simp
      _ ≤ a := mul_le_mul_of_nonneg_right this hT.le
  have has : a < s + T := by
    have := Int.ceil_lt_add_one (s / T)
    calc a = (k₀ : ℝ) * T := rfl
      _ < (s / T + 1) * T := mul_lt_mul_of_pos_right this hT
      _ = s + T := by field_simp
  have hexp_nn : 0 ≤ Real.exp (-(β * (t - s))) := (Real.exp_pos _).le
  rcases lt_or_ge t a with hta | hat
  · -- `t` and `s` lie within one period window.
    have hw := hwin s t hst (by linarith)
    have hb : 1 ≤ Real.exp (β * T) * Real.exp (-(β * (t - s))) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    calc ‖transition A t s‖ ≤ E := hw
      _ ≤ E * (Real.exp (β * T) * Real.exp (-(β * (t - s)))) := le_mul_of_one_le_right hE0 hb
      _ ≤ (E * E * C * Real.exp (2 * γ) + E * Real.exp (β * T)) * Real.exp (-(β * (t - s))) := by
        have : 0 ≤ E * E * C * Real.exp (2 * γ) * Real.exp (-(β * (t - s))) := by positivity
        nlinarith
  · set n : ℕ := ⌊(t - a) / T⌋₊ with hn
    set b : ℝ := a + n * T with hb
    have hnT : (n : ℝ) * T ≤ t - a := by
      have := Nat.floor_le (div_nonneg (sub_nonneg.mpr hat) hT.le)
      calc (n : ℝ) * T ≤ (t - a) / T * T := mul_le_mul_of_nonneg_right this hT.le
        _ = t - a := by field_simp
    have hnT' : t - a < (n + 1) * T := by
      have := Nat.lt_floor_add_one ((t - a) / T)
      calc t - a = (t - a) / T * T := by field_simp
        _ < (n + 1) * T := mul_lt_mul_of_pos_right this hT
    have hab : a ≤ b := by
      have : (0 : ℝ) ≤ n * T := mul_nonneg (Nat.cast_nonneg n) hT.le
      simp only [hb]; linarith
    have hbt : b ≤ t := by simp only [hb]; linarith
    have hsplit : transition A t s =
        transition A t b * (transition A b a * transition A a s) := by
      rw [transition_trans hA hM hsa hab, transition_trans hA hM (hsa.trans hab) hbt]
    have hmono : transition A b a = monodromy A T 0 ^ n := by
      rw [hb, transition_add_nat_mul_period hA hM hT.le hP a n, ha,
        show (k₀ : ℝ) * T = 0 + k₀ * T by ring, monodromy_add_int_mul hA hM hT.le hP 0 k₀]
    have h1 : ‖transition A t b‖ ≤ E := hwin b t hbt (by simp only [hb]; nlinarith)
    have h3 : ‖transition A a s‖ ≤ E := hwin s a hsa (by linarith)
    have h2 : ‖transition A b a‖ ≤ C * Real.exp (-(γ * n)) := by rw [hmono]; exact hpow n
    have hdecay : Real.exp (-(γ * n)) ≤ Real.exp (2 * γ) * Real.exp (-(β * (t - s))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hts : t - s < (n + 2) * T := by nlinarith
      have : β * (t - s) ≤ γ * (n + 2) := by
        rw [hβ, div_mul_eq_mul_div, div_le_iff₀ hT]
        nlinarith
      nlinarith
    calc ‖transition A t s‖ = ‖transition A t b * (transition A b a * transition A a s)‖ := by
          rw [hsplit]
      _ ≤ ‖transition A t b‖ * (‖transition A b a‖ * ‖transition A a s‖) :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ E * ((C * Real.exp (-(γ * n))) * E) := by gcongr
      _ ≤ E * ((C * (Real.exp (2 * γ) * Real.exp (-(β * (t - s))))) * E) := by gcongr
      _ = E * E * C * Real.exp (2 * γ) * Real.exp (-(β * (t - s))) := by ring
      _ ≤ (E * E * C * Real.exp (2 * γ) + E * Real.exp (β * T)) *
            Real.exp (-(β * (t - s))) := by
          have : 0 ≤ E * Real.exp (β * T) * Real.exp (-(β * (t - s))) := by positivity
          nlinarith

/-- Trajectory form of the Floquet criterion: every forward solution of `ẋ = A(t) x` decays
exponentially, uniformly in the initial time. -/
@[powerlib_foundation] theorem trajectory_decay_of_spectralRadius_lt_one
    (hA : Continuous A) (hP : Periodic A T) (hT : 0 < T)
    (hρ : spectralRadius ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ)) < 1) :
    ∃ K β : ℝ, 0 < β ∧ ∀ (s : ℝ) (x : ℝ → X → ℝ),
      IsIntegralCurveOn x (vecField A) (Ici s) →
        ∀ t, s ≤ t → ‖x t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s‖ := by
  obtain ⟨M, hM⟩ := exists_bound_of_periodic hA hP hT
  obtain ⟨K, β, hβ, hK⟩ := uniformlyExponentiallyStable_of_spectralRadius_lt_one hA hP hT hρ
  refine ⟨K, β, hβ, fun s x hx t hst => ?_⟩
  rw [trajectory_eq hA hM hx t hst]
  exact (Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul_of_nonneg_right (hK s t hst) (norm_nonneg _))

end powerlib.Periodic
