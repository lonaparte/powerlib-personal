import theorem.Periodic.Transition
import theorem.LTI.Discrete

/-! # Floquet sufficient criterion for periodic linear time-varying systems

A monodromy matrix with spectral radius below one makes a periodic linear time-varying system
uniformly exponentially stable.

Scope.
* System `ẋ = A(t) x`, `x ∈ ℝ^X` (sup norm), with a continuous real `T`-periodic state matrix `A`
  (`T > 0`), continuous time, forward solutions only.
* The monodromy matrix is `monodromy A T 0 = Φ(T, 0)` of `theorem/Periodic/Transition.lean`; its
  complex spectrum is the set of Floquet multipliers.
* Only the sufficient direction is proved (no converse, no instability statement);
  `FloquetUnstable A T` names the opposite situation (some Floquet multiplier strictly outside
  the unit circle).

Source: work-sync theory/T-harmonic-linearization.md §1.6 (`|ρ_i| < 1` stability criterion);
projects/basin-guard/notes/concepts/guard-object.md §3 (`max |μ_i| = 1` as the threshold).

Results.
* `uniformlyExponentiallyStable_of_spectralRadius_lt_one` — if the spectral radius of the
  complexified monodromy matrix is `< 1`, then there are `K` and `β > 0` with
  `‖Φ(t, s)‖ ≤ K e^{-β (t - s)}` for **all** `s ≤ t` (uniform in the initial time).
* `trajectory_decay_of_spectralRadius_lt_one` — the same bound for every forward solution,
  `‖x(t)‖ ≤ K e^{-β (t - s)} ‖x(s)‖`.

The contractive power `‖M^m‖ < 1` is LeanForControl's
`exists_pow_norm_lt_one_of_spectralRadius_lt_one` (Gelfand's formula), applied to the
complexified monodromy matrix with the `L∞` operator norm; the matrix-power lemmas
(`LTI.exists_pow_norm_lt_one`, `LTI.exists_pow_norm_le_exp`) are in `theorem/LTI/Discrete.lean`.
-/

noncomputable section
namespace powerlib.Periodic

open Set Matrix Function
open scoped Matrix.Norms.Operator

variable {X : Type*} [Fintype X] [DecidableEq X]

variable {A : ℝ → Matrix X X ℝ} {T : ℝ}

/-- **Floquet sufficient criterion.** For a continuous `T`-periodic state matrix, Floquet
multipliers strictly inside the unit disk give uniform exponential stability of `ẋ = A(t) x`,
stated on the transition matrix: `‖Φ(t, s)‖ ≤ K e^{-β (t - s)}` for all `s ≤ t`, with `β > 0`. -/
@[tmio T, powerlib_foundation] theorem uniformlyExponentiallyStable_of_spectralRadius_lt_one
    (hA : Continuous A) (hP : Periodic A T) (hT : 0 < T)
    (hρ : spectralRadius ℂ ((monodromy A T 0).map (algebraMap ℝ ℂ)) < 1) :
    ∃ K β : ℝ, 0 < β ∧ ∀ s t, s ≤ t → ‖transition A t s‖ ≤ K * Real.exp (-(β * (t - s))) := by
  obtain ⟨M, hM⟩ := exists_bound_of_periodic hA hP hT
  obtain ⟨m, hm, hlt⟩ := LTI.exists_pow_norm_lt_one _ hρ
  obtain ⟨C, γ, hC, hγ, hpow⟩ := LTI.exists_pow_norm_le_exp hm hlt
  set E : ℝ := ‖(1 : Matrix X X ℝ)‖ * Real.exp (Real.toNNReal M * T) with hE
  have hE0 : 0 ≤ E := by positivity
  have hwin : ∀ s t, s ≤ t → t - s ≤ T → ‖transition A t s‖ ≤ E := by
    intro s t hst hts
    refine (norm_transition_le hM hst).trans ?_
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
  · -- from the first period point `a` on, the period samples decay (`LTI.le_exp_of_sampled_decay`)
    have hwin : ∀ (n : ℕ) (r : ℝ), a + n * T ≤ r → r < a + (n + 1) * T →
        ‖transition A r s‖ ≤ E * (‖transition A (a + n * T) a‖ * E) := by
      intro n r h1 h2
      have hab : a ≤ a + n * T := le_add_of_nonneg_right (by positivity)
      have hsplit : transition A r s =
          transition A r (a + n * T) * (transition A (a + n * T) a * transition A a s) := by
        rw [LinearSystems.stateTransitionMatrix_comp hA (fun r _ => hM r) (mem_uIcc_of_le hsa hab),
          LinearSystems.stateTransitionMatrix_comp hA (fun r _ => hM r)
            (mem_uIcc_of_le (hsa.trans hab) h1)]
      rw [hsplit]
      refine (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left (norm_mul_le _ _)
        (norm_nonneg _)).trans ?_)
      gcongr
      · exact hwin _ r h1 (by linarith)
      · exact hwin s a hsa (by linarith)
    have hβT : β * T = γ := by rw [hβ]; exact div_mul_cancel₀ γ hT.ne'
    have hg : ∀ n : ℕ, ‖transition A (a + n * T) a‖ * E ≤
        C * E * Real.exp (-(β * (n * T))) := by
      intro n
      rw [transition_add_nat_mul_period hA hM hT.le hP a n, ha,
        show (k₀ : ℝ) * T = 0 + k₀ * T by ring, monodromy_add_int_mul hA hM hT.le hP 0 k₀,
        show β * (n * T) = γ * n by rw [← hβT]; ring]
      calc ‖monodromy A T 0 ^ n‖ * E ≤ C * Real.exp (-(γ * n)) * E := by gcongr; exact hpow n
        _ = C * E * Real.exp (-(γ * n)) := by ring
    have h := LTI.le_exp_of_sampled_decay hT hE0 (mul_nonneg hC hE0) hwin hg hat
    rw [abs_of_pos hβpos, hβT] at h
    have hsh : Real.exp (-(β * (t - a))) ≤ Real.exp γ * Real.exp (-(β * (t - s))) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have : β * (a - s) ≤ β * T := mul_le_mul_of_nonneg_left (by linarith) hβpos.le
      nlinarith
    calc ‖transition A t s‖ ≤ E * (C * E) * Real.exp γ * Real.exp (-(β * (t - a))) := h
      _ ≤ E * (C * E) * Real.exp γ * (Real.exp γ * Real.exp (-(β * (t - s)))) := by gcongr
      _ = E * E * C * Real.exp (2 * γ) * Real.exp (-(β * (t - s))) := by
          rw [two_mul, Real.exp_add]; ring
      _ ≤ (E * E * C * Real.exp (2 * γ) + E * Real.exp (β * T)) *
            Real.exp (-(β * (t - s))) := by
          have : 0 ≤ E * Real.exp (β * T) * Real.exp (-(β * (t - s))) := by positivity
          nlinarith

/-- Trajectory form of the Floquet criterion: every forward solution of `ẋ = A(t) x` decays
exponentially, uniformly in the initial time. -/
@[tmio T, powerlib_foundation] theorem trajectory_decay_of_spectralRadius_lt_one
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

/-! ## Floquet instability -/

/-- Some Floquet multiplier lies strictly outside the unit circle. -/
def FloquetUnstable {X : Type*} [Fintype X] [DecidableEq X] (A : ℝ → Matrix X X ℝ) (T : ℝ) :
    Prop :=
  ∃ ρ ∈ spectrum ℂ ((Periodic.monodromy A T 0).map (algebraMap ℝ ℂ)), 1 < ‖ρ‖

end powerlib.Periodic
