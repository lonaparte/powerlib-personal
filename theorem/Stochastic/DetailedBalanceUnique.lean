import dependencies.Mathlib
import theorem.Attributes
import theorem.Stochastic.DetailedBalance

/-! # Uniqueness of the generalized detailed-balance density of a Klein–Kramers system

For the Klein–Kramers drift `q̇ = p/M`, `ṗ = −V'(q) − D p/M` (`DetailedBalance.kkDrift`) with a
diagonal diffusion matrix `diag(s, a(q))` (a constant position diffusion `s`, a momentum
diffusion `a` depending on the position), generalized detailed balance under the momentum flip
`(q, p) ↦ (q, −p)` with a positive differentiable density `ρ` forces the fluctuation–dissipation
structure and the Gibbs form: `a` is a nonzero constant `a₀`, `s = 0` unless `V' ≡ 0`, and
`ρ = ρ(0, 0) e^{V(0)/T} e^{−H/T}` with `H = p²/(2M) + V(q)`, `T = a₀/(2D)`. The converse is
`DetailedBalance.kk_genDetailedBalance`. Hence a Klein–Kramers system whose Gibbs function
violates a constraint on the density (normalizability, periodicity in a cyclic coordinate) has no
density in generalized detailed balance: a stationary density, if any, carries an irreversible
probability current.

Scope.
* Foundation (calculus on `Fin 2 → ℝ`), for arbitrary `M ≠ 0`, `D ≠ 0`, differentiable `V`,
  arbitrary `a`, `s`. Partial derivatives are `DetailedBalance.pd`; the density is assumed
  differentiable on `Fin 2 → ℝ` (no second derivatives are used: stationarity enters through
  `DetailedBalance.fpOp_eq_of_drift`). Statements about laws or paths are not made.

Source: C. W. Gardiner, *Handbook of Stochastic Methods* (3rd ed., 2004), §5.3.5 (the drift
condition determines the potential `−log ρ` of the irreversible drift); H. Risken, *The
Fokker–Planck Equation* (2nd ed., 1989), §6.4 and §10.1 (Kramers equation, detailed balance with
the Maxwell–Boltzmann density).

Results.
* `update_vec2_zero`, `update_vec2_one`, `pd_vec2_zero`, `pd_vec2_one`: coordinate lines of
  `Fin 2 → ℝ`.
* `eq_gibbs_of_kk_genDetailedBalance` (**uniqueness**): under generalized detailed balance with
  the momentum flip, `s = 0 ∨ V' ≡ 0`, `a ≡ a(0) ≠ 0` and
  `ρ(q, p) = ρ(0, 0) e^{V(0)/T} gibbs(q, p)`, `T = a(0)/(2D)`.
-/

noncomputable section
namespace powerlib.Stochastic.DetailedBalance

open Real Matrix
open powerlib.Stochastic.KleinKramers (gibbs)

/-! ## Coordinate lines of `Fin 2 → ℝ` -/

@[tmio T, powerlib_foundation] theorem update_vec2_zero (a b t : ℝ) :
    Function.update ![a, b] 0 t = ![t, b] := by
  funext i; fin_cases i <;> simp

@[tmio T, powerlib_foundation] theorem update_vec2_one (a b t : ℝ) :
    Function.update ![a, b] 1 t = ![a, t] := by
  funext i; fin_cases i <;> simp

@[tmio T, powerlib_foundation] theorem pd_vec2_zero (g : (Fin 2 → ℝ) → ℝ) (a b : ℝ) :
    pd g 0 ![a, b] = deriv (fun t => g ![t, b]) a := by
  simp [pd, update_vec2_zero]

@[tmio T, powerlib_foundation] theorem pd_vec2_one (g : (Fin 2 → ℝ) → ℝ) (a b : ℝ) :
    pd g 1 ![a, b] = deriv (fun t => g ![a, t]) b := by
  simp [pd, update_vec2_one]

/-! ## The two rows and stationarity -/

variable {M D s : ℝ} {V V' a : ℝ → ℝ} {ρ : (Fin 2 → ℝ) → ℝ}

/-- The two rows of the drift condition and stationarity, in coordinates:
`s ∂_q ρ = 0`, `a(q) ∂_p ρ = −2D (p/M) ρ`, `(p/M) ∂_q ρ = V'(q) ∂_p ρ`. -/
@[tmio T, powerlib_foundation] private theorem kk_rows
    (h : GenDetailedBalance (kkDrift M D V') (fun x => !![s, 0; 0, a (x 0)]) kkFlip ρ)
    (q p : ℝ) :
    s * deriv (fun t => ρ ![t, p]) q = 0 ∧
      a q * deriv (fun t => ρ ![q, t]) p = -(2 * D * (p / M)) * ρ ![q, p] ∧
      p / M * deriv (fun t => ρ ![t, p]) q = V' q * deriv (fun t => ρ ![q, t]) p := by
  have hc : ∀ (x : Fin 2 → ℝ) (i j : Fin 2),
      pd (fun y => (!![s, 0; 0, a (y 0)] : Matrix (Fin 2) (Fin 2) ℝ) i j * ρ y) j x =
        (!![s, 0; 0, a (x 0)] : Matrix (Fin 2) (Fin 2) ℝ) i j * pd ρ j x := by
    intro x i j
    refine pd_mul_of_update (a := fun y => (!![s, 0; 0, a (y 0)] : Matrix (Fin 2) (Fin 2) ℝ) i j)
      fun t => ?_
    fin_cases i <;> fin_cases j <;> simp
  have h0 := h.drift ![q, p] 0
  have h1 := h.drift ![q, p] 1
  simp only [hc, Fin.sum_univ_two, pd_vec2_zero, pd_vec2_one] at h0 h1
  simp [kkDrift, kkFlip, reversal] at h0 h1
  have hst := h.stationary ![q, p]
  rw [fpOp_eq_of_drift h.drift] at hst
  have hr : ∀ y : Fin 2 → ℝ, ∀ i,
      revDrift (kkDrift M D V') kkFlip y i = ![y 1 / M, -V' (y 0)] i :=
    fun y i => by fin_cases i <;> simp [revDrift, kkDrift, kkFlip, reversal] <;> ring
  simp only [hr, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hst
  rw [pd_mul_of_update (a := fun y => y 1 / M) (fun t => by simp),
    pd_mul_of_update (a := fun y => -V' (y 0)) (fun t => by simp), pd_vec2_zero,
    pd_vec2_one] at hst
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hst
  exact ⟨by linear_combination -h0, by linear_combination -h1, by linear_combination -hst⟩

/-- **Uniqueness of the generalized detailed-balance density** of a Klein–Kramers system with
diffusion `diag(s, a(q))`: under the momentum flip, with `ρ` positive and differentiable, `M ≠ 0`
and `D ≠ 0`, either `s = 0` or `V' ≡ 0`; the momentum diffusion is a nonzero constant `a(0)`;
and `ρ` is the Gibbs function at the temperature `T = a(0)/(2D)`, up to the factor
`ρ(0, 0) e^{V(0)/T}`. -/
@[tmio T, powerlib_foundation] theorem eq_gibbs_of_kk_genDetailedBalance
    (hV : ∀ q, HasDerivAt V (V' q) q) (hM : M ≠ 0) (hD : D ≠ 0) (hρ : Differentiable ℝ ρ)
    (h : GenDetailedBalance (kkDrift M D V') (fun x => !![s, 0; 0, a (x 0)]) kkFlip ρ) :
    (s = 0 ∨ ∀ q, V' q = 0) ∧ (∀ q, a q = a 0) ∧ a 0 ≠ 0 ∧
      ∀ q p, ρ ![q, p] = ρ ![0, 0] * exp (V 0 / (a 0 / (2 * D))) *
        gibbs V M (a 0 / (2 * D)) q p := by
  have hpos := h.pos
  have hdq : ∀ q p, HasDerivAt (fun t => ρ ![t, p]) (deriv (fun t => ρ ![t, p]) q) q := by
    intro q p
    have := differentiable_comp_update hρ ![0, p] 0 q
    simp only [update_vec2_zero] at this
    exact this.hasDerivAt
  have hdp : ∀ q p, HasDerivAt (fun t => ρ ![q, t]) (deriv (fun t => ρ ![q, t]) p) p := by
    intro q p
    have := differentiable_comp_update hρ ![q, 0] 1 p
    simp only [update_vec2_one] at this
    exact this.hasDerivAt
  -- the momentum diffusion never vanishes
  have ha : ∀ q, a q ≠ 0 := by
    intro q haq
    have h1 := (kk_rows h q 1).2.1
    rw [haq, zero_mul] at h1
    have : 2 * D * (1 / M) * ρ ![q, 1] = 0 := by linarith
    have hρ1 := hpos ![q, 1]
    simp only [mul_eq_zero, div_eq_zero_iff, one_ne_zero, false_or, OfNat.ofNat_ne_zero,
      hD, hM] at this
    linarith
  -- momentum slices: `∂_p ρ = −(2D p/(M a(q))) ρ`
  have hP : ∀ q p, deriv (fun t => ρ ![q, t]) p = -(2 * D * p / (M * a q)) * ρ ![q, p] := by
    intro q p
    have h1 := (kk_rows h q p).2.1
    field_simp [ha q] at h1 ⊢
    linarith
  have hslice : ∀ q p, ρ ![q, p] = ρ ![q, 0] * exp (-(D * p ^ 2 / (M * a q))) := by
    intro q p
    have e := eq_mul_exp_of_hasDerivAt (f := fun t => ρ ![q, t])
      (c := fun t => -(2 * D * t / (M * a q))) (C := fun t => -(D * t ^ 2 / (M * a q)))
      (fun t => by rw [← hP q t]; exact hdp q t)
      (fun t => (((hasDerivAt_pow 2 t).const_mul D).div_const (M * a q)).neg.congr_deriv
        (by push_cast; ring)) 0 p
    simpa using e
  -- position slices at `p ≠ 0`: `∂_q ρ = −(2D V'(q)/a(q)) ρ`
  have hQ : ∀ q p, p ≠ 0 →
      deriv (fun t => ρ ![t, p]) q = -(2 * D * V' q / a q) * ρ ![q, p] := by
    intro q p hp
    have h3 := (kk_rows h q p).2.2
    rw [hP] at h3
    have e : deriv (fun t => ρ ![t, p]) q = M / p * (p / M * deriv (fun t => ρ ![t, p]) q) := by
      field_simp
    rw [e, h3]
    field_simp [ha q]
  -- `a` is constant: `log ρ(q, 1) − log ρ(q, 2)` has zero derivative
  have hconst : ∀ q, a q = a 0 := by
    have hL : ∀ (p : ℝ), p ≠ 0 → ∀ q, HasDerivAt (fun t => Real.log (ρ ![t, p]))
        (-(2 * D * V' q / a q)) q := by
      intro p hp q
      have := (hdq q p).log (hpos _).ne'
      convert this using 1
      rw [hQ q p hp]
      field_simp [(hpos ![q, p]).ne']
    have hz : ∀ q, HasDerivAt (fun t => Real.log (ρ ![t, 1]) - Real.log (ρ ![t, 2])) 0 q :=
      fun q => by
        have := (hL 1 one_ne_zero q).sub (hL 2 two_ne_zero q)
        rwa [sub_self] at this
    intro q
    have hc := is_const_of_deriv_eq_zero (fun t => (hz t).differentiableAt)
      (fun t => (hz t).deriv) q 0
    have e : ∀ t, Real.log (ρ ![t, 1]) - Real.log (ρ ![t, 2]) = 3 * D / (M * a t) := by
      intro t
      rw [hslice t 1, hslice t 2, Real.log_mul (hpos _).ne' (exp_pos _).ne',
        Real.log_mul (hpos _).ne' (exp_pos _).ne', Real.log_exp, Real.log_exp]
      ring
    rw [e, e] at hc
    have h3 : (3 * D) / (M * a q) = (3 * D) / (M * a 0) := hc
    have hD3 : 3 * D ≠ 0 := mul_ne_zero three_ne_zero hD
    rw [div_eq_div_iff (mul_ne_zero hM (ha q)) (mul_ne_zero hM (ha 0))] at h3
    have := mul_left_cancel₀ hD3 h3
    exact (mul_left_cancel₀ hM this).symm
  refine ⟨?_, hconst, ha 0, ?_⟩
  · -- position diffusion: `s ∂_q ρ = 0` forces `V' ≡ 0` unless `s = 0`
    by_cases hs : s = 0
    · exact Or.inl hs
    refine Or.inr fun q => ?_
    have h0 : deriv (fun t => ρ ![t, 1]) q = 0 := by
      have := (kk_rows h q 1).1
      exact (mul_eq_zero.mp this).resolve_left hs
    rw [hQ q 1 one_ne_zero] at h0
    have hρ1 := (hpos ![q, 1]).ne'
    have := (mul_eq_zero.mp h0).resolve_right hρ1
    rw [neg_eq_zero, div_eq_zero_iff] at this
    rcases mul_eq_zero.mp (this.resolve_right (ha q)) with h' | h'
    · exact absurd h' (mul_ne_zero two_ne_zero hD)
    · exact h'
  · -- integrate along `p = 1`, then along the momentum
    intro q p
    set T := a 0 / (2 * D) with hT
    have hT0 : T ≠ 0 := div_ne_zero (ha 0) (mul_ne_zero two_ne_zero hD)
    have hq1 : ρ ![q, 1] = ρ ![0, 1] * exp (-(V q / T) - -(V 0 / T)) := by
      refine eq_mul_exp_of_hasDerivAt (f := fun t => ρ ![t, 1])
        (c := fun t => -(2 * D * V' t / a t)) (C := fun t => -(V t / T))
        (fun t => by rw [← hQ t 1 one_ne_zero]; exact hdq t 1)
        (fun t => ((hV t).div_const T).neg.congr_deriv (by rw [hconst t, hT]; field_simp)) 0 q
    have h00 := hslice 0 1
    have hq0 := hslice q 1
    rw [hconst q] at hq0
    rw [hslice q p, hconst q]
    have hρq0 : ρ ![q, 0] = ρ ![q, 1] * exp (D * 1 ^ 2 / (M * a 0)) := by
      rw [hq0, mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
    have hρ00 : ρ ![0, 0] = ρ ![0, 1] * exp (D * 1 ^ 2 / (M * a 0)) := by
      rw [h00, mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
    rw [hρq0, hq1, hρ00]
    simp only [gibbs, mul_assoc, ← exp_add]
    congr 2
    rw [hT]
    field_simp
    ring

end powerlib.Stochastic.DetailedBalance
