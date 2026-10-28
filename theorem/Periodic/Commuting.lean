import theorem.Periodic.Transition

/-! # Commuting state matrices: the transition matrix is an ordinary exponential

When the state matrices at different times commute, the transition matrix of `ẋ = A(t) x` is the
exponential of the integrated state matrix.

Scope.
* `ẋ = A(t) x` with continuous, uniformly bounded `A : ℝ → Matrix X X ℝ` (`L∞` operator norm),
  as in `Periodic/Transition.lean`.

Source: work-sync theory/T-harmonic-linearization.md §1.6.

Results.
* `commute_intervalIntegral` — an interval integral of a family commuting with `N` commutes with
  `N` (the integral is pushed through left and right multiplication, Mathlib
  `ContinuousLinearMap.intervalIntegral_comp_comm`).
* `transition_eq_exp_integral` — if `A(t₁) A(t₂) = A(t₂) A(t₁)` for all `t₁, t₂`, then
  `Φ(t, s) = exp(∫ₛᵗ A)` for `s ≤ t`; in particular the monodromy matrix is `exp(∫₀ᵀ A)`.
* `transition_smul` — the special case `A(t) = a(t) N` gives `Φ(t, s) = exp((∫ₛᵗ a) N)`.

Corrections.
* T-harmonic-linearization.md §1.6 says the ordinary exponential formula holds "仅当 (only if)
  `[A(t₁), A(t₂)] = 0` for all `t₁, t₂`". Pairwise commutation is a **sufficient** condition
  (proved here); it is not shown, and not claimed here, to be necessary.
-/

noncomputable section
namespace powerlib.Periodic

open Set Matrix Function intervalIntegral
open scoped Matrix.Norms.Operator

variable {X : Type*} [Fintype X] [DecidableEq X] {A : ℝ → Matrix X X ℝ} {M : ℝ}

/-- An interval integral of a family commuting with `N` commutes with `N`. -/
@[tmio T, powerlib_foundation] theorem commute_intervalIntegral (hA : Continuous A)
    {N : Matrix X X ℝ} (h : ∀ r, Commute (A r) N) (a b : ℝ) :
    Commute (∫ r in a..b, A r) N := by
  have h1 := ((ContinuousLinearMap.mul ℝ (Matrix X X ℝ)).flip N).intervalIntegral_comp_comm
    (hA.intervalIntegrable (μ := MeasureTheory.volume) a b)
  have h2 := (ContinuousLinearMap.mul ℝ (Matrix X X ℝ) N).intervalIntegral_comp_comm
    (hA.intervalIntegrable (μ := MeasureTheory.volume) a b)
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] at h1 h2
  show (∫ r in a..b, A r) * N = N * ∫ r in a..b, A r
  rw [← h1, ← h2]
  congr 1
  funext r
  exact h r

/-- Pairwise commuting state matrices: `Φ(t, s) = exp(∫ₛᵗ A)` (`s ≤ t`). -/
@[powerlib_foundation] theorem transition_eq_exp_integral (hA : Continuous A)
    (hM : ∀ t, ‖A t‖ ≤ M) (hcomm : ∀ t r, Commute (A t) (A r)) {s t : ℝ} (hst : s ≤ t) :
    transition A t s = NormedSpace.exp (∫ r in s..t, A r) := by
  set Y : ℝ → Matrix X X ℝ := fun u => NormedSpace.exp (∫ r in s..u, A r) with hYdef
  have hcI : ∀ a b x, Commute (A x) (∫ r in a..b, A r) := fun a b x =>
    (commute_intervalIntegral hA (fun y => hcomm y x) a b).symm
  have hY : IsIntegralCurveOn Y (matField A) (Ici s) := by
    intro u _
    apply HasDerivAt.hasDerivWithinAt
    have hsplit : ∀ r, Y r = Y u * NormedSpace.exp (∫ x in u..r, A x) := by
      intro r
      simp only [hYdef]
      rw [← integral_add_adjacent_intervals (hA.intervalIntegrable (μ := MeasureTheory.volume) s u)
        (hA.intervalIntegrable (μ := MeasureTheory.volume) u r)]
      exact NormedSpace.exp_add_of_commute
        (commute_intervalIntegral hA (fun x => hcI u r x) s u)
    have hG : HasDerivAt (fun r => ∫ x in u..r, A x) (A u) u :=
      (hA.integral_hasStrictDerivAt u u).hasDerivAt
    have hF : HasDerivAt (fun r => NormedSpace.exp (∫ x in u..r, A x)) (A u) u := by
      have hE := hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix X X ℝ)
      have := hE.comp_hasDerivAt_of_eq u hG (by simp)
      simp only [one_apply_eq_self] at this
      exact this
    have hYfun : Y = fun r => Y u * NormedSpace.exp (∫ x in u..r, A x) := funext hsplit
    rw [hYfun]
    have h := hF.const_mul (Y u)
    convert h using 1
    · simp only [matField]
      rw [← hsplit u]
      exact ((hcI s u u).exp_right).eq
  have h := transition_unique hA hM hY t hst
  have hs : Y s = 1 := by simp [hYdef]
  rw [hs, mul_one] at h
  exact h.symm

/-- Scalar modulation of a constant matrix, `A(t) = a(t) N`: `Φ(t, s) = exp((∫ₛᵗ a) N)`. -/
@[powerlib_foundation] theorem transition_smul {a : ℝ → ℝ} (ha : Continuous a)
    (N : Matrix X X ℝ) {M : ℝ} (hM : ∀ t, ‖a t • N‖ ≤ M) {s t : ℝ} (hst : s ≤ t) :
    transition (fun r => a r • N) t s = NormedSpace.exp ((∫ r in s..t, a r) • N) := by
  rw [transition_eq_exp_integral (A := fun r => a r • N) (ha.smul continuous_const) hM
    (fun t r => (Commute.refl N).smul_left (a t) |>.smul_right (a r)) hst,
    intervalIntegral.integral_smul_const]

end powerlib.Periodic
