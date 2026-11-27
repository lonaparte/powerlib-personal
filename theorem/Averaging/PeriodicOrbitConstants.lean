import theorem.Averaging.PerturbedPeriodicOrbits
import theorem.Averaging.PeriodicOrbitStability

/-! # Explicit constants for the stability of averaging periodic orbits

`theorem/Averaging/PeriodicOrbitStability.lean` decides the stability of the periodic orbits of
`theorem/Averaging/PeriodicOrbits.lean` by the averaged Jacobian `J = Df̄(y*)`, with constants
`ε₀, δ₀, K, β` that exist because a Lyapunov matrix (`PJ + JᵀP = −I`) or an instability
certificate exists. Here the certificate is a hypothesis, and every constant is a closed-form
expression in the bounds `p₁ ≤ λ_min(P)`, `p₂ ≥ λ_max(P)`, `q₁ ≤ λ_min(Q)` of a Lyapunov pair
`PJ + JᵀP = −Q`, or in the constants `α`, `q₁ ≤ λ_min(HJ + JᵀH − 2αH)`, `η_H ≥ ‖H‖` of a
Chetaev form `H`, in a bound `a ≥ ‖J‖`, and in the constants `T, ℓ, M, ρ, L₂` of the field and
`ℓ_q, M_q` of the perturbation (`C_S`, `L_S` of `Averaging.stroboConst`,
`Averaging.stroboLip`). The statements are made for the perturbed curves of
`theorem/Averaging/PerturbedPeriodicOrbits.lean` (`ẋ = ε f(x, t) + q(t)`, `‖q‖ ≤ ηM_q`,
`ε² ≤ η ≤ ε`), which covers both `ẋ = ε f + ε² r` (`exp_stable_of_lyapunov`,
`unstable_of_chetaev`) and transformed coordinates with fractional-order remainders.

Scope.
* `f` as in `Averaging.exp_stable_of_hurwitz` on `ℝⁿ = EuclideanSpace ℝ (Fin n)`, `n > 0`,
  `Df̄(y*)` the operator of a real matrix `J`.
* Lyapunov certificate: `P ≻ 0`, `PJ + JᵀP = −Q`, `p₁‖e‖² ≤ eᵀPe ≤ p₂‖e‖²`,
  `q₁‖e‖² ≤ eᵀQe` (`q₁ > 0`; e.g. `p₁ = λ_min(P)`, `p₂ = λ_max(P)`, `q₁ = λ_min(Q)`).
  The rate is `c = q₁/(8p₂)` per slow time, the attraction radius `δ₀ = r₁p₁/(2p₂)`, the
  constant `K = √(e^{2(ℓ+ℓ_q)T}(p₂/p₁)e^{cT})`, the decay `e^{−(c/2)ε(t − τ)}`.
* Chetaev certificate: a symmetric `H` with `wᵀHw > 0` for some `w`, `α > 0`,
  `q₁‖e‖² ≤ eᵀ(HJ + JᵀH − 2αH)e`, `‖H‖ ≤ η_H`; the escape radius is `r₁/2`.
* Smallness is stated by explicit inequalities: for a radius `r₁` (`2r₁ ≤ ρ`) and a perturbation
  level `κ` (`2L₂r₁ ≤ κ`, `96p₂³κ² ≤ q₁²p₁` resp. `κ ≤ 1`, `16η_Hκ ≤ q₁`), the depth satisfies
  `2εTp₂a² ≤ q₁`, `εTq₁ ≤ p₂` (resp. `εTa ≤ 1`, `4εTη_H(a² + 1) ≤ q₁`),
  `2ε(M + M_q)T ≤ ρ` and `2ηL_S ≤ κεT`. For `η = ε²` the last reads `2εL_S ≤ κT`; the
  admissible depths are then exactly `ε ≤ ε₀` with `ε₀` the minimum of the five closed-form
  bounds.
* The stability properties are written out (exponential attraction uniform in the initial
  time; escape from a ball), as in `Averaging.exp_stable_of_hurwitz`. Generic mathematics, no
  model family.

Source: Bogoliubov–Mitropolsky, *Asymptotic Methods in the Theory of Non-Linear Oscillations*
(stability of the periodic solutions of the second theorem of Bogoliubov); Hale, *Ordinary
Differential Equations*, Ch. V; Khalil, *Nonlinear Systems*, Ch. 4 and 10 (quadratic Lyapunov
functions with `λ_min`/`λ_max` bounds, Chetaev's theorem, averaging); the Euler-step identity
`Averaging.quadraticForm_euler`, the splitting `Averaging.quadraticForm_add_le`, and LeanForControl
`MatrixAlgebra.quadraticForm`; the one-period estimate `Averaging.perturbed_period_step_sub_le`.

Results.
* `lyapunov_step_le` — `V(e + hJe) ≤ (1 − (q₁/(2p₂))h) V(e)` for `2hp₂a² ≤ q₁`.
* `lyapunov_perturbed_step_le` — `V(e + hJe + p) ≤ (1 − (q₁/(8p₂))h)V(e) + (12p₂²/q₁)σ²/h` for
  `‖p‖ ≤ hκ‖e‖ + σ`, `96p₂³κ² ≤ q₁²p₁`, `hq₁ ≤ p₂`.
* `chetaev_perturbed_step_ge` — `W(e + hJe + p) ≥ (1 + 2αh)W(e)` for `‖p‖ ≤ hκ‖e‖`.
* `perturbed_difference_step` — one period of the difference of two perturbed curves is a
  perturbed Euler step of `A = Df̄(y*)`.
* `exp_stable_perturbed` — the explicit exponential attraction estimate for perturbed curves.
* `unstable_perturbed` — the explicit escape for a perturbed family.
* `exp_stable_of_lyapunov`, `unstable_of_chetaev` — the same for `ẋ = ε f(x, t) + ε² r(x, t)`:
  `Averaging.exp_stable_of_hurwitz` and `Averaging.unstable_of_root` with explicit constants.
-/

noncomputable section
namespace powerlib.Averaging

open Set Filter Topology intervalIntegral
open scoped Interval

/-! ## Euler steps with an explicit certificate -/

section Certificates

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

local notation "op" A:max => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A

open MatrixAlgebra Matrix

open scoped RealInnerProductSpace

/-- **The linear Euler step contracts the Lyapunov function of a certificate.** If
`PJ + JᵀP = −Q`, `V = eᵀPe ≤ p₂‖e‖²`, `q₁‖e‖² ≤ eᵀQe`, `‖J‖ ≤ a` and `2hp₂a² ≤ q₁`, `h ≥ 0`,
then `V(e + hJe) ≤ (1 − (q₁/(2p₂))h) V(e)`. -/
@[tmio T, powerlib_foundation] theorem lyapunov_step_le {P Q J : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.IsHermitian) (hLyap : P * J + Jᵀ * P = -Q) {p₂ q₁ a h : ℝ} (hp₂ : 0 < p₂)
    (hq₁ : 0 ≤ q₁) (hup : ∀ x : ℝⁿ, quadraticForm P x ≤ p₂ * ‖x‖ ^ 2)
    (hQ : ∀ x : ℝⁿ, q₁ * ‖x‖ ^ 2 ≤ quadraticForm Q x) (ha : ‖op J‖ ≤ a) (hh : 0 ≤ h)
    (hha : 2 * h * p₂ * a ^ 2 ≤ q₁) (e : ℝⁿ) :
    quadraticForm P (e + h • (op J) e) ≤ (1 - q₁ / (2 * p₂) * h) * quadraticForm P e := by
  rw [quadraticForm_euler hP, hLyap]
  have hneg : quadraticForm (-Q) e = -quadraticForm Q e := by
    rw [show -Q = (-1 : ℝ) • Q by simp, quadraticForm_matrix_smul]; ring
  rw [hneg]
  have ha0 : 0 ≤ a := (norm_nonneg _).trans ha
  have hJe : quadraticForm P ((op J) e) ≤ p₂ * (a ^ 2 * ‖e‖ ^ 2) := by
    refine (hup _).trans ?_
    gcongr
    calc ‖(op J) e‖ ^ 2 ≤ (‖op J‖ * ‖e‖) ^ 2 := by gcongr; exact (op J).le_opNorm e
      _ ≤ (a * ‖e‖) ^ 2 := by gcongr
      _ = a ^ 2 * ‖e‖ ^ 2 := by ring
  have h1 : h ^ 2 * quadraticForm P ((op J) e) ≤ h * (q₁ * ‖e‖ ^ 2) / 2 := by
    calc h ^ 2 * quadraticForm P ((op J) e) ≤ h ^ 2 * (p₂ * (a ^ 2 * ‖e‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hJe (sq_nonneg _)
      _ = h * ‖e‖ ^ 2 * (2 * h * p₂ * a ^ 2) / 2 := by ring
      _ ≤ h * ‖e‖ ^ 2 * q₁ / 2 := by gcongr
      _ = h * (q₁ * ‖e‖ ^ 2) / 2 := by ring
  have h2 : q₁ / (2 * p₂) * h * quadraticForm P e ≤ h * (q₁ * ‖e‖ ^ 2) / 2 := by
    calc q₁ / (2 * p₂) * h * quadraticForm P e ≤ q₁ / (2 * p₂) * h * (p₂ * ‖e‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hup e) (by positivity)
      _ = h * (q₁ * ‖e‖ ^ 2) / 2 := by field_simp
  have h3 : h * (q₁ * ‖e‖ ^ 2) ≤ h * quadraticForm Q e := mul_le_mul_of_nonneg_left (hQ e) hh
  have e4 : (1 - q₁ / (2 * p₂) * h) * quadraticForm P e =
      quadraticForm P e - q₁ / (2 * p₂) * h * quadraticForm P e := by ring
  rw [e4]
  linarith

/-- The arithmetic of a perturbed contraction step. -/
@[tmio T, powerlib_foundation] private theorem contraction_arith {Ve Vu Vp Vup nE c₁ h κ σ p₁
    p₂ : ℝ} (hc₁ : 0 < c₁) (hh : 0 < h) (hc₁h : c₁ * h ≤ 2⁻¹) (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hVe : 0 ≤ Ve) (hVp0 : 0 ≤ Vp) (hnE0 : 0 ≤ nE) (hnE : p₁ * nE ≤ Ve)
    (hVu : Vu ≤ (1 - c₁ * h) * Ve)
    (hup : Vup ≤ (1 + c₁ * h / 2) * Vu + (1 + 1 / (c₁ * h / 2)) * Vp)
    (hVp : Vp ≤ 2 * p₂ * (h ^ 2 * κ ^ 2 * nE + σ ^ 2)) (hκ2 : κ ^ 2 ≤ c₁ ^ 2 * p₁ / (24 * p₂)) :
    Vup ≤ (1 - c₁ / 4 * h) * Ve + 6 * p₂ / c₁ * σ ^ 2 / h := by
  have hch : 0 < c₁ * h := mul_pos hc₁ hh
  have hθinv : 1 + 1 / (c₁ * h / 2) ≤ 3 / (c₁ * h) := by
    rw [div_div_eq_mul_div, one_mul, show 3 / (c₁ * h) = 1 / (c₁ * h) + 2 / (c₁ * h) by ring]
    have : 1 ≤ 1 / (c₁ * h) := by rw [le_div_iff₀ hch]; linarith
    linarith
  have hB : (1 + c₁ * h / 2) * Vu ≤ (1 - c₁ * h / 2) * Ve := by
    have h1 : (1 + c₁ * h / 2) * Vu ≤ (1 + c₁ * h / 2) * ((1 - c₁ * h) * Ve) :=
      mul_le_mul_of_nonneg_left hVu (by positivity)
    have h2 : (1 + c₁ * h / 2) * (1 - c₁ * h) ≤ 1 - c₁ * h / 2 := by nlinarith
    calc (1 + c₁ * h / 2) * Vu ≤ (1 + c₁ * h / 2) * (1 - c₁ * h) * Ve := by linarith
      _ ≤ (1 - c₁ * h / 2) * Ve := mul_le_mul_of_nonneg_right h2 hVe
  have hC1 : (1 + 1 / (c₁ * h / 2)) * Vp ≤ 3 / (c₁ * h) * (2 * p₂ * (h ^ 2 * κ ^ 2 * nE + σ ^ 2)) :=
    mul_le_mul hθinv hVp hVp0 (by positivity)
  have hC2 : 3 / (c₁ * h) * (2 * p₂ * (h ^ 2 * κ ^ 2 * nE + σ ^ 2)) =
      h * nE * (6 * p₂ * κ ^ 2 / c₁) + 6 * p₂ / c₁ * σ ^ 2 / h := by
    field_simp; ring
  have hk : 6 * p₂ * κ ^ 2 / c₁ ≤ c₁ * p₁ / 4 := by
    rw [div_le_iff₀ hc₁]
    calc 6 * p₂ * κ ^ 2 ≤ 6 * p₂ * (c₁ ^ 2 * p₁ / (24 * p₂)) :=
          mul_le_mul_of_nonneg_left hκ2 (by positivity)
      _ = c₁ * p₁ / 4 * c₁ := by field_simp; ring
  have hC3 : h * nE * (6 * p₂ * κ ^ 2 / c₁) ≤ c₁ * h / 4 * Ve := by
    calc h * nE * (6 * p₂ * κ ^ 2 / c₁) ≤ h * nE * (c₁ * p₁ / 4) :=
          mul_le_mul_of_nonneg_left hk (by positivity)
      _ = c₁ * h / 4 * (p₁ * nE) := by ring
      _ ≤ c₁ * h / 4 * Ve := mul_le_mul_of_nonneg_left hnE (by positivity)
  have : (1 - c₁ / 4 * h) * Ve = (1 - c₁ * h / 2) * Ve + c₁ * h / 4 * Ve := by ring
  rw [this]
  linarith

/-- **A Lyapunov certificate makes perturbed Euler steps contract, with explicit constants.**
For `P ≻ 0`, `PJ + JᵀP = −Q`, `p₁‖e‖² ≤ eᵀPe ≤ p₂‖e‖²`, `q₁‖e‖² ≤ eᵀQe` (`q₁ > 0`), `‖J‖ ≤ a`,
a step `0 < h` with `2hp₂a² ≤ q₁` and `hq₁ ≤ p₂`, and `96p₂³κ² ≤ q₁²p₁`: every perturbed Euler
step with `‖p‖ ≤ hκ‖e‖ + σ` has
`V(e + hJe + p) ≤ (1 − (q₁/(8p₂))h) V(e) + (12p₂²/q₁) σ²/h`. -/
@[tmio T, powerlib_foundation] theorem lyapunov_perturbed_step_le
    {P Q J : Matrix (Fin n) (Fin n) ℝ} (hPd : P.PosDef) (hLyap : P * J + Jᵀ * P = -Q)
    {p₁ p₂ q₁ a h κ σ : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hq₁ : 0 < q₁)
    (hbd : ∀ x : ℝⁿ, p₁ * ‖x‖ ^ 2 ≤ quadraticForm P x ∧ quadraticForm P x ≤ p₂ * ‖x‖ ^ 2)
    (hQ : ∀ x : ℝⁿ, q₁ * ‖x‖ ^ 2 ≤ quadraticForm Q x) (ha : ‖op J‖ ≤ a) (hh : 0 < h)
    (hha : 2 * h * p₂ * a ^ 2 ≤ q₁) (hhq : h * q₁ ≤ p₂) (hκ : 96 * p₂ ^ 3 * κ ^ 2 ≤ q₁ ^ 2 * p₁)
    (e p : ℝⁿ) (hp : ‖p‖ ≤ h * κ * ‖e‖ + σ) :
    quadraticForm P (e + h • (op J) e + p) ≤
      (1 - q₁ / (8 * p₂) * h) * quadraticForm P e + 12 * p₂ ^ 2 / q₁ * σ ^ 2 / h := by
  set c₁ := q₁ / (2 * p₂) with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  have hV0 : ∀ x : ℝⁿ, 0 ≤ quadraticForm P x := fun x =>
    (mul_nonneg hp₁.le (sq_nonneg _)).trans (hbd x).1
  have hVu := lyapunov_step_le hPd.1 hLyap hp₂ hq₁.le (fun x => (hbd x).2) hQ ha hh.le hha e
  have hsplit := quadraticForm_add_le hPd (θ := c₁ * h / 2) (by positivity) (e + h • (op J) e) p
  have hVp : quadraticForm P p ≤ 2 * p₂ * (h ^ 2 * κ ^ 2 * ‖e‖ ^ 2 + σ ^ 2) := by
    refine (hbd p).2.trans ?_
    have hp0 : 0 ≤ ‖p‖ := norm_nonneg _
    have h1 : ‖p‖ ^ 2 ≤ (h * κ * ‖e‖ + σ) ^ 2 := pow_le_pow_left₀ hp0 hp 2
    have h2 : (h * κ * ‖e‖ + σ) ^ 2 ≤ 2 * (h ^ 2 * κ ^ 2 * ‖e‖ ^ 2 + σ ^ 2) := by
      nlinarith [sq_nonneg (h * κ * ‖e‖ - σ)]
    nlinarith
  have hc₁h : c₁ * h ≤ 2⁻¹ := by
    rw [hc₁, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; linarith
  have hκ2 : κ ^ 2 ≤ c₁ ^ 2 * p₁ / (24 * p₂) := by
    rw [hc₁, le_div_iff₀ (by positivity), div_pow]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have h := contraction_arith hc₁0 hh hc₁h hp₁ hp₂ (hV0 e) (hV0 p) (sq_nonneg _) (hbd e).1
    hVu hsplit hVp hκ2
  have e1 : c₁ / 4 = q₁ / (8 * p₂) := by rw [hc₁]; field_simp; ring
  have e2 : 6 * p₂ / c₁ = 12 * p₂ ^ 2 / q₁ := by rw [hc₁]; field_simp; ring
  rw [e1, e2] at h
  exact h

/-- The arithmetic of a perturbed expansion step. -/
@[tmio T, powerlib_foundation] private theorem expansion_arith' {We Wu Wup nE nU nP α h κ q₁ η
    a : ℝ} (hh : 0 < h) (hη : 0 ≤ η) (hq₁ : 0 ≤ q₁) (hnE : 0 ≤ nE) (hnP : 0 ≤ nP)
    (hWu : We + h * (q₁ * nE ^ 2 + 2 * α * We) - h ^ 2 * (η * (a ^ 2 * nE ^ 2)) ≤ Wu)
    (hWup : Wu - 2 * (nU * (η * nP)) - η * nP ^ 2 ≤ Wup) (hU : nU ≤ 2 * nE)
    (hP : nP ≤ h * κ * nE) (h1 : h * (η * a ^ 2) ≤ q₁ / 4) (h2 : 4 * η * κ ≤ q₁ / 4)
    (h3 : η * h * κ ^ 2 ≤ q₁ / 4) :
    (1 + 2 * α * h) * We ≤ Wup := by
  have hP2 : nP ^ 2 ≤ (h * κ * nE) ^ 2 := pow_le_pow_left₀ hnP hP 2
  have hUP : nU * nP ≤ 2 * nE * (h * κ * nE) := by
    have hnU : 0 ≤ nU ∨ nU < 0 := le_or_gt 0 nU
    rcases hnU with hnU | hnU
    · exact mul_le_mul hU hP hnP (by positivity)
    · nlinarith [mul_nonneg hnP hnE]
  have hA : 2 * (nU * (η * nP)) ≤ h * nE ^ 2 * (4 * η * κ) := by
    nlinarith [mul_le_mul_of_nonneg_left hUP hη]
  have hB : η * nP ^ 2 ≤ h * nE ^ 2 * (η * h * κ ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hP2 hη]
  have hC : h ^ 2 * (η * (a ^ 2 * nE ^ 2)) = h * nE ^ 2 * (h * (η * a ^ 2)) := by ring
  have hD : 0 ≤ h * nE ^ 2 * (q₁ - h * (η * a ^ 2) - 4 * η * κ - η * h * κ ^ 2) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith

/-- **A Chetaev certificate makes perturbed Euler steps expand, with explicit constants.** For a
symmetric `H`, `α`, `q₁` with `q₁‖e‖² ≤ eᵀ(HJ + JᵀH − 2αH)e`, `‖J‖ ≤ a`, `‖H‖ ≤ η_H`, a step
`0 < h` with `ha ≤ 1` and `4hη_H(a² + 1) ≤ q₁`, and `0 ≤ κ ≤ 1`, `16η_Hκ ≤ q₁`: every perturbed
Euler step with `‖p‖ ≤ hκ‖e‖` has `W(e + hJe + p) ≥ (1 + 2αh) W(e)`, `W(e) = eᵀHe`. -/
@[tmio T, powerlib_foundation] theorem chetaev_perturbed_step_ge
    {H J : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian) {α q₁ a ηH h κ : ℝ}
    (hQ : ∀ x : ℝⁿ, q₁ * ‖x‖ ^ 2 ≤ quadraticForm (H * J + Jᵀ * H - (2 * α) • H) x)
    (ha : ‖op J‖ ≤ a) (hηH : ‖op H‖ ≤ ηH) (hh : 0 < h) (hha : h * a ≤ 1)
    (hhq : 4 * h * ηH * (a ^ 2 + 1) ≤ q₁) (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hκq : 16 * ηH * κ ≤ q₁)
    (e p : ℝⁿ) (hp : ‖p‖ ≤ h * κ * ‖e‖) :
    (1 + 2 * α * h) * quadraticForm H e ≤ quadraticForm H (e + h • (op J) e + p) := by
  have hη : 0 ≤ ηH := (norm_nonneg _).trans hηH
  have ha0 : 0 ≤ a := (norm_nonneg _).trans ha
  have hq₁ : 0 ≤ q₁ := le_trans (by positivity) hκq
  have c1 : h * (ηH * a ^ 2) ≤ q₁ / 4 := by nlinarith [mul_nonneg hh.le hη]
  have c2 : 4 * ηH * κ ≤ q₁ / 4 := by linarith
  have c3 : ηH * h * κ ^ 2 ≤ q₁ / 4 := by
    have hk2 : κ ^ 2 ≤ 1 := by nlinarith
    have : ηH * h * κ ^ 2 ≤ ηH * h * 1 := mul_le_mul_of_nonneg_left hk2 (by positivity)
    nlinarith [mul_nonneg (mul_nonneg hh.le hη) (sq_nonneg a)]
  have habsH : ∀ x : ℝⁿ, |quadraticForm H x| ≤ ηH * ‖x‖ ^ 2 := fun x =>
    (abs_quadraticForm_le H x).trans (mul_le_mul_of_nonneg_right hηH (sq_nonneg _))
  -- the linear Euler step
  set u := e + h • (op J) e with hu
  have hWu : quadraticForm H e + h * (q₁ * ‖e‖ ^ 2 + 2 * α * quadraticForm H e) -
      h ^ 2 * (ηH * (a ^ 2 * ‖e‖ ^ 2)) ≤ quadraticForm H u := by
    rw [hu, quadraticForm_euler hH]
    have hsplitQ : quadraticForm (H * J + Jᵀ * H) e =
        quadraticForm (H * J + Jᵀ * H - (2 * α) • H) e + 2 * α * quadraticForm H e := by
      rw [← quadraticForm_matrix_smul, ← quadraticForm_matrix_add, sub_add_cancel]
    rw [hsplitQ]
    have hJe : -(ηH * (a ^ 2 * ‖e‖ ^ 2)) ≤ quadraticForm H ((op J) e) := by
      have h1 := habsH ((op J) e)
      have h2 : ‖(op J) e‖ ^ 2 ≤ a ^ 2 * ‖e‖ ^ 2 := by
        calc ‖(op J) e‖ ^ 2 ≤ (‖op J‖ * ‖e‖) ^ 2 := by
              gcongr; exact (op J).le_opNorm e
          _ ≤ (a * ‖e‖) ^ 2 := by gcongr
          _ = a ^ 2 * ‖e‖ ^ 2 := by ring
      have h3 := neg_abs_le (quadraticForm H ((op J) e))
      have h4 := mul_le_mul_of_nonneg_left h2 hη
      linarith
    have k1 := mul_le_mul_of_nonneg_left (hQ e) hh.le
    have k2 := mul_le_mul_of_nonneg_left hJe (sq_nonneg h)
    have e1 : quadraticForm H e + h * (quadraticForm (H * J + Jᵀ * H - (2 * α) • H) e +
        2 * α * quadraticForm H e) + h ^ 2 * quadraticForm H ((op J) e) =
        quadraticForm H e + h * (2 * α * quadraticForm H e) +
          h * quadraticForm (H * J + Jᵀ * H - (2 * α) • H) e +
          h ^ 2 * quadraticForm H ((op J) e) := by ring
    have e2 : quadraticForm H e + h * (q₁ * ‖e‖ ^ 2 + 2 * α * quadraticForm H e) -
        h ^ 2 * (ηH * (a ^ 2 * ‖e‖ ^ 2)) = quadraticForm H e + h * (2 * α * quadraticForm H e) +
          h * (q₁ * ‖e‖ ^ 2) + h ^ 2 * -(ηH * (a ^ 2 * ‖e‖ ^ 2)) := by ring
    rw [e1, e2]
    linarith
  -- the perturbation
  have hWup : quadraticForm H u - 2 * (‖u‖ * (ηH * ‖p‖)) - ηH * ‖p‖ ^ 2 ≤
      quadraticForm H (u + p) := by
    rw [quadraticForm_add hH u p]
    have h1 : |⟪u, (op H) p⟫| ≤ ‖u‖ * (ηH * ‖p‖) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
        (((op H).le_opNorm p).trans (mul_le_mul_of_nonneg_right hηH (norm_nonneg _)))
        (norm_nonneg _))
    have h2 := habsH p
    have h3 := neg_abs_le ⟪u, (op H) p⟫
    have h4 := neg_abs_le (quadraticForm H p)
    linarith
  have hU : ‖u‖ ≤ 2 * ‖e‖ := by
    calc ‖u‖ ≤ ‖e‖ + ‖h • (op J) e‖ := norm_add_le _ _
      _ = ‖e‖ + h * ‖(op J) e‖ := by rw [norm_smul, Real.norm_of_nonneg hh.le]
      _ ≤ ‖e‖ + h * (a * ‖e‖) := by
          gcongr; exact ((op J).le_opNorm e).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
      _ ≤ 2 * ‖e‖ := by nlinarith [norm_nonneg e]
  exact expansion_arith' hh hη hq₁ (norm_nonneg e) (norm_nonneg p) hWu hWup hU hp c1 c2 c3

end Certificates

/-! ## One period of the difference of two perturbed curves -/

section Difference

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ → E} {T ℓ M ρ L₂ : ℝ} {Df : E → ℝ → E →L[ℝ] E} {ystar : E}

/-- **One period of the difference of two perturbed curves near `y*` is a perturbed Euler step of
the linearized averaged field**: `x(s + T) − z(s + T) = e + εT A e + p`, `e = x(s) − z(s)`,
`A = Df̄(y*)`, `‖p‖ ≤ εT (L₂ r₁ + ηL_S/(εT)) ‖e‖`, while `x(s)`, `z(s)` lie in the ball of radius
`r₁` (`r₁ + ε(M + M_q)T ≤ ρ`) (`perturbed_period_step_sub_le`,
`Averaging.fieldAverage_sub_linear_le`). -/
@[tmio T, powerlib_foundation] theorem perturbed_difference_step [CompleteSpace E]
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hρ : 0 < ρ) (hL₂ : 0 ≤ L₂)
    (hD : ∀ x, ‖x - ystar‖ ≤ ρ → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ x y, ‖x - ystar‖ ≤ ρ → ‖y - ystar‖ ≤ ρ → ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    (hDc : Continuous (Df ystar)) {A : E →L[ℝ] E} (hA : HasFDerivAt (fieldAverage f T) A ystar)
    {ε η ℓq Mq : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hηε : η ≤ ε) (hεη : ε ^ 2 ≤ η) (hℓq : 0 ≤ ℓq)
    (hMq : 0 ≤ Mq) {x z qx qz : ℝ → E} {s r₁ : ℝ}
    (hx : ∀ t ∈ Icc s (s + T), HasDerivAt x (ε • f (x t) t + qx t) t)
    (hz : ∀ t ∈ Icc s (s + T), HasDerivAt z (ε • f (z t) t + qz t) t)
    (hqx : ∀ t ∈ Icc s (s + T), ‖qx t‖ ≤ η * Mq) (hqz : ∀ t ∈ Icc s (s + T), ‖qz t‖ ≤ η * Mq)
    (hqxz : ∀ t ∈ Icc s (s + T), ‖qx t - qz t‖ ≤ η * ℓq * ‖x t - z t‖)
    (hxs : ‖x s - ystar‖ ≤ r₁) (hzs : ‖z s - ystar‖ ≤ r₁) (hr₁ : r₁ + ε * (M + Mq) * T ≤ ρ) :
    ∃ p : E, x (s + T) - z (s + T) = (x s - z s) + (ε * T) • A (x s - z s) + p ∧
      ‖p‖ ≤ ε * T * (L₂ * r₁ + η * stroboLip ℓ ℓq L₂ M Mq T / (ε * T)) * ‖x s - z s‖ := by
  have hT := hf.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 ystar 0)
  have hr₁ρ : r₁ ≤ ρ := by nlinarith [mul_nonneg (mul_nonneg hε.le (add_nonneg hM hMq)) hT.le]
  refine ⟨(ε * T) • (fieldAverage f T (x s) - fieldAverage f T (z s) - A (x s - z s)) +
    ((x (s + T) - x s - (ε * T) • fieldAverage f T (x s)) -
      (z (s + T) - z s - (ε * T) • fieldAverage f T (z s))), ?_, ?_⟩
  · simp only [smul_sub]; abel
  have h1 := fieldAverage_sub_linear_le hf hρ hL₂ hD hDl hDc hA hr₁ρ hxs hzs
  have h2 := perturbed_period_step_sub_le hf hL₂ hD hDl hε.le hε1 hηε hεη hℓq hMq hx hz hqx hqz
    hqxz hxs hzs hr₁
  calc _ ≤ ε * T * (L₂ * r₁ * ‖x s - z s‖) +
        η * stroboLip ℓ ℓq L₂ M Mq T * ‖x s - z s‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ h2)
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ε * T * (L₂ * r₁ + η * stroboLip ℓ ℓq L₂ M Mq T / (ε * T)) * ‖x s - z s‖ := by
        field_simp

end Difference

/-! ## Stability and instability with explicit constants -/

section StabilityRn

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

local notation "op" A:max => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A

open MatrixAlgebra Matrix

/-- The arithmetic of the final exponential estimate: from `a ≤ G b`,
`p₁ b² ≤ (1 − ch)^k p₂ d²` and `t − τ − kT ≤ T`, `h = εT`, `ε ≤ 1`:
`a ≤ √(G²(p₂/p₁)e^{cT}) e^{−(c/2)ε(t − τ)} d`. -/
@[tmio T, powerlib_foundation] private theorem decay_arith' {a b d G p₁ p₂ c ε T t τ : ℝ}
    {k : ℕ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hc : 0 < c) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hT : 0 < T) (hch : c * (ε * T) ≤ 1) (hd : 0 ≤ d) (ha : 0 ≤ a) (hab : a ≤ G * b)
    (hb : p₁ * b ^ 2 ≤ (1 - c * (ε * T)) ^ k * (p₂ * d ^ 2))
    (hkT' : t - τ - k * T ≤ T) :
    a ≤ Real.sqrt (G ^ 2 * (p₂ / p₁) * Real.exp (c * T)) * Real.exp (-(c / 2 * ε * (t - τ))) *
      d := by
  have hch0 : 0 ≤ c * (ε * T) := by positivity
  have hpowexp : (1 - c * (ε * T)) ^ k ≤ Real.exp (c * T) * Real.exp (-(c * ε * (t - τ))) := by
    have h1 : (1 - c * (ε * T)) ^ k ≤ Real.exp (-(c * (ε * T))) ^ k :=
      pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-(c * (ε * T)))]) k
    rw [← Real.exp_nat_mul] at h1
    rw [← Real.exp_add]
    refine h1.trans (Real.exp_le_exp.mpr ?_)
    have h2 : ε * (t - τ - k * T) ≤ ε * T := mul_le_mul_of_nonneg_left hkT' hε.le
    have h3 : ε * T ≤ T := by nlinarith
    nlinarith
  have hb2 : b ^ 2 ≤ Real.exp (c * T) * Real.exp (-(c * ε * (t - τ))) * (p₂ * d ^ 2) / p₁ := by
    rw [le_div_iff₀ hp₁]
    have := mul_le_mul_of_nonneg_right hpowexp (by positivity : 0 ≤ p₂ * d ^ 2)
    linarith
  have hexp2 : Real.exp (-(c / 2 * ε * (t - τ))) ^ 2 = Real.exp (-(c * ε * (t - τ))) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hK2 : Real.sqrt (G ^ 2 * (p₂ / p₁) * Real.exp (c * T)) ^ 2 =
      G ^ 2 * (p₂ / p₁) * Real.exp (c * T) := Real.sq_sqrt (by positivity)
  have hfin : a ^ 2 ≤ (Real.sqrt (G ^ 2 * (p₂ / p₁) * Real.exp (c * T)) *
      Real.exp (-(c / 2 * ε * (t - τ))) * d) ^ 2 := by
    have h1 : a ^ 2 ≤ G ^ 2 * b ^ 2 := by
      calc a ^ 2 ≤ (G * b) ^ 2 := pow_le_pow_left₀ ha hab 2
        _ = G ^ 2 * b ^ 2 := by ring
    calc a ^ 2 ≤ G ^ 2 * b ^ 2 := h1
      _ ≤ G ^ 2 * (Real.exp (c * T) * Real.exp (-(c * ε * (t - τ))) * (p₂ * d ^ 2) / p₁) :=
          mul_le_mul_of_nonneg_left hb2 (sq_nonneg _)
      _ = _ := by rw [mul_pow, mul_pow, hK2, hexp2]; field_simp
  exact (pow_le_pow_iff_left₀ ha (by positivity) two_ne_zero).mp hfin

/-- `p₁ ≤ p₂` for the bounds of a quadratic form on `ℝⁿ`, `n > 0`. -/
@[tmio T, powerlib_foundation] private theorem le_of_quadratic_bounds [NeZero n]
    {P : Matrix (Fin n) (Fin n) ℝ} {p₁ p₂ : ℝ}
    (hbd : ∀ e : ℝⁿ, p₁ * ‖e‖ ^ 2 ≤ quadraticForm P e ∧ quadraticForm P e ≤ p₂ * ‖e‖ ^ 2) :
    p₁ ≤ p₂ := by
  have hn : ‖(EuclideanSpace.single (0 : Fin n) (1 : ℝ) : ℝⁿ)‖ = 1 := by simp
  have h := hbd (EuclideanSpace.single 0 1)
  rw [hn, one_pow, mul_one, mul_one] at h
  exact h.1.trans h.2

/-- **Exponential stability of perturbed curves near a Hurwitz equilibrium, explicit constants.**
Let `f` be as in `Averaging.exp_stable_of_hurwitz` on `ℝⁿ` (`Df̄(y*) = J`) and let
`(P, Q)` be a Lyapunov certificate of `J`: `P ≻ 0`, `PJ + JᵀP = −Q`,
`p₁‖e‖² ≤ eᵀPe ≤ p₂‖e‖²`, `q₁‖e‖² ≤ eᵀQe`, `q₁ > 0`, `‖J‖ ≤ a`. Take `r₁ > 0` with `2r₁ ≤ ρ`,
`κ` with `2L₂r₁ ≤ κ` and `96p₂³κ² ≤ q₁²p₁`, and `0 < ε ≤ 1`, `ε² ≤ η ≤ ε` with
`2εTp₂a² ≤ q₁`, `εTq₁ ≤ p₂`, `2ε(M + M_q)T ≤ ρ`, `2ηL_S ≤ κεT`. Let `x`, `z` be curves that
solve `ẋ = ε f(x, t) + q_x`, `ż = ε f(z, t) + q_z` with the perturbation bounds over every period
that starts with both in the ball of radius `r₁`. If `z` stays within `δ₀ = r₁p₁/(2p₂)` of `y*`
and `‖x(τ) − z(τ)‖ ≤ δ₀`, then for all `t ≥ τ`
`‖x(t) − z(t)‖ ≤ √(e^{2(ℓ+ℓ_q)T}(p₂/p₁)e^{q₁T/(8p₂)}) e^{−(q₁/(16p₂))ε(t − τ)} ‖x(τ) − z(τ)‖`
(`lyapunov_perturbed_step_le`, `perturbed_difference_step`). -/
@[tmio T, powerlib_foundation] theorem exp_stable_perturbed [NeZero n] {f : ℝⁿ → ℝ → ℝⁿ}
    {T ℓ M ρ L₂ : ℝ} {Df : ℝⁿ → ℝ → ℝⁿ →L[ℝ] ℝⁿ} {ystar : ℝⁿ}
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hρ : 0 < ρ) (hL₂ : 0 ≤ L₂)
    (hD : ∀ x, ‖x - ystar‖ ≤ ρ → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ x y, ‖x - ystar‖ ≤ ρ → ‖y - ystar‖ ≤ ρ → ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    (hDc : Continuous (Df ystar)) {J : Matrix (Fin n) (Fin n) ℝ}
    (hA : HasFDerivAt (fieldAverage f T) (op J) ystar)
    {P Q : Matrix (Fin n) (Fin n) ℝ} (hPd : P.PosDef) (hLyap : P * J + Jᵀ * P = -Q)
    {p₁ p₂ q₁ a : ℝ} (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hbd : ∀ e : ℝⁿ, p₁ * ‖e‖ ^ 2 ≤ quadraticForm P e ∧ quadraticForm P e ≤ p₂ * ‖e‖ ^ 2)
    (hQ : ∀ e : ℝⁿ, q₁ * ‖e‖ ^ 2 ≤ quadraticForm Q e) (ha : ‖op J‖ ≤ a)
    {r₁ κ ε η ℓq Mq : ℝ} (hr₁ : 0 < r₁) (hr₁ρ : 2 * r₁ ≤ ρ)
    (hκ : 96 * p₂ ^ 3 * κ ^ 2 ≤ q₁ ^ 2 * p₁) (hr₁κ : 2 * L₂ * r₁ ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hηε : η ≤ ε) (hεη : ε ^ 2 ≤ η) (hℓq : 0 ≤ ℓq) (hMq : 0 ≤ Mq)
    (hεa : 2 * (ε * T) * p₂ * a ^ 2 ≤ q₁) (hεq : ε * T * q₁ ≤ p₂)
    (hερ : 2 * ε * (M + Mq) * T ≤ ρ) (hηκ : 2 * η * stroboLip ℓ ℓq L₂ M Mq T ≤ κ * (ε * T))
    {x z qx qz : ℝ → ℝⁿ}
    (hxz : ∀ s, ‖x s - ystar‖ ≤ r₁ → ‖z s - ystar‖ ≤ r₁ → ∀ t ∈ Icc s (s + T),
      HasDerivAt x (ε • f (x t) t + qx t) t ∧ HasDerivAt z (ε • f (z t) t + qz t) t ∧
      ‖qx t‖ ≤ η * Mq ∧ ‖qz t‖ ≤ η * Mq ∧ ‖qx t - qz t‖ ≤ η * ℓq * ‖x t - z t‖)
    (hzb : ∀ t, ‖z t - ystar‖ ≤ r₁ * p₁ / (2 * p₂)) {τ : ℝ}
    (hxτ : ‖x τ - z τ‖ ≤ r₁ * p₁ / (2 * p₂)) :
    ∀ t, τ ≤ t → ‖x t - z t‖ ≤ Real.sqrt (Real.exp ((ℓ + ℓq) * T) ^ 2 * (p₂ / p₁) *
      Real.exp (q₁ / (8 * p₂) * T)) * Real.exp (-(q₁ / (16 * p₂) * ε * (t - τ))) *
        ‖x τ - z τ‖ := by
  have hT := hf.1
  have hℓ := hf.2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 ystar 0)
  have hp₁₂ : p₁ ≤ p₂ := le_of_quadratic_bounds hbd
  have hp₂ : 0 < p₂ := hp₁.trans_le hp₁₂
  set LS := stroboLip ℓ ℓq L₂ M Mq T with hLS
  set c := q₁ / (8 * p₂) with hcdef
  have hc : 0 < c := by positivity
  set h := ε * T with hh
  have hh0 : 0 < h := mul_pos hε hT
  have hch : c * h ≤ 1 := by
    rw [hcdef, div_mul_eq_mul_div, div_le_one (by positivity)]; nlinarith
  set δ₀ := r₁ * p₁ / (2 * p₂) with hδ₀
  have hδ₀r : δ₀ ≤ r₁ / 2 := by
    rw [hδ₀, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hδ₀sq : p₂ / p₁ * δ₀ ^ 2 ≤ (r₁ / 2) ^ 2 := by
    rw [hδ₀, div_pow, mul_pow]
    rw [show p₂ / p₁ * (r₁ ^ 2 * p₁ ^ 2 / (2 * p₂) ^ 2) = (r₁ / 2) ^ 2 * (p₁ / p₂) by
      field_simp]
    exact mul_le_of_le_one_right (sq_nonneg _) ((div_le_one hp₂).mpr hp₁₂)
  have hερ' : r₁ + ε * (M + Mq) * T ≤ ρ := by linarith
  have hκ' : L₂ * r₁ + η * LS / (ε * T) ≤ κ := by
    have : η * LS / (ε * T) ≤ κ / 2 := by
      rw [div_le_iff₀ (mul_pos hε hT)]; linarith
    linarith
  have hκ'0 : 0 ≤ L₂ * r₁ + η * LS / (ε * T) := by
    have hη0 : 0 ≤ η := (sq_nonneg ε).trans hεη
    have : 0 ≤ LS := by rw [hLS, stroboLip]; positivity
    positivity
  have hzr : ∀ s, ‖z s - ystar‖ ≤ r₁ := fun s => (hzb s).trans (by linarith)
  have hstep : ∀ e p : ℝⁿ, ‖p‖ ≤ h * κ * ‖e‖ →
      quadraticForm P (e + h • (op J) e + p) ≤ (1 - c * h) * quadraticForm P e := by
    intro e p hp
    have := lyapunov_perturbed_step_le hPd hLyap hp₁ hp₂ hq₁ hbd hQ ha hh0 hεa hεq hκ e p
      (by rw [add_zero]; exact hp)
    simpa using this
  -- the sampled deviation decreases the Lyapunov function
  set e : ℕ → ℝⁿ := fun k => x (τ + k * T) - z (τ + k * T) with he
  have hind : ∀ k : ℕ, quadraticForm P (e k) ≤ (1 - c * h) ^ k * quadraticForm P (e 0) ∧
      ‖x (τ + k * T) - ystar‖ ≤ r₁ := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, one_mul, Nat.cast_zero, zero_mul, add_zero, le_refl, true_and]
      calc ‖x τ - ystar‖ = ‖(x τ - z τ) + (z τ - ystar)‖ := by congr 1; abel
        _ ≤ δ₀ + δ₀ := (norm_add_le _ _).trans (add_le_add hxτ (hzb τ))
        _ ≤ r₁ := by linarith
    | succ k ih =>
      obtain ⟨hVk, hxk⟩ := ih
      have hp := hxz _ hxk (hzr _)
      obtain ⟨p, hpe, hpn⟩ := perturbed_difference_step hf hρ hL₂ hD hDl hDc hA hε hε1 hηε hεη
        hℓq hMq (fun t ht => (hp t ht).1) (fun t ht => (hp t ht).2.1)
        (fun t ht => (hp t ht).2.2.1) (fun t ht => (hp t ht).2.2.2.1)
        (fun t ht => (hp t ht).2.2.2.2) hxk (hzr _) hερ'
      have hek : e (k + 1) = e k + h • (op J) (e k) + p := by
        simp only [he]
        rw [show τ + ((k + 1 : ℕ) : ℝ) * T = τ + k * T + T by push_cast; ring, hpe]
      have hpn' : ‖p‖ ≤ h * κ * ‖e k‖ := by
        refine hpn.trans ?_
        simp only [he, hh]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκ' (by positivity))
          (norm_nonneg _)
      have hs := hstep (e k) p hpn'
      rw [← hek] at hs
      have hVk1 : quadraticForm P (e (k + 1)) ≤ (1 - c * h) ^ (k + 1) * quadraticForm P (e 0) := by
        calc quadraticForm P (e (k + 1)) ≤ (1 - c * h) * quadraticForm P (e k) := hs
          _ ≤ (1 - c * h) * ((1 - c * h) ^ k * quadraticForm P (e 0)) :=
              mul_le_mul_of_nonneg_left hVk (by linarith)
          _ = (1 - c * h) ^ (k + 1) * quadraticForm P (e 0) := by ring
      refine ⟨hVk1, ?_⟩
      have hch0 : 0 ≤ c * h := mul_nonneg hc.le hh0.le
      have hpow : (1 - c * h) ^ (k + 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      have hV0 : 0 ≤ quadraticForm P (e 0) := (mul_nonneg hp₁.le (sq_nonneg _)).trans (hbd _).1
      have hsq : ‖e (k + 1)‖ ^ 2 ≤ (r₁ / 2) ^ 2 := by
        have h1 : p₁ * ‖e (k + 1)‖ ^ 2 ≤ quadraticForm P (e 0) := by
          calc p₁ * ‖e (k + 1)‖ ^ 2 ≤ quadraticForm P (e (k + 1)) := (hbd _).1
            _ ≤ (1 - c * h) ^ (k + 1) * quadraticForm P (e 0) := hVk1
            _ ≤ 1 * quadraticForm P (e 0) := mul_le_mul_of_nonneg_right hpow hV0
            _ = quadraticForm P (e 0) := one_mul _
        have h2 : quadraticForm P (e 0) ≤ p₂ * δ₀ ^ 2 := by
          refine (hbd _).2.trans (mul_le_mul_of_nonneg_left ?_ hp₂.le)
          have : e 0 = x τ - z τ := by simp [he]
          rw [this]
          exact pow_le_pow_left₀ (norm_nonneg _) hxτ 2
        have h3 : ‖e (k + 1)‖ ^ 2 ≤ p₂ / p₁ * δ₀ ^ 2 := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hp₁, mul_comm]; exact h1.trans h2
        exact h3.trans hδ₀sq
      have hn : ‖e (k + 1)‖ ≤ r₁ / 2 :=
        (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
      calc ‖x (τ + ((k + 1 : ℕ) : ℝ) * T) - ystar‖ =
          ‖e (k + 1) + (z (τ + ((k + 1 : ℕ) : ℝ) * T) - ystar)‖ := by
            simp only [he]; congr 1; abel
        _ ≤ r₁ / 2 + δ₀ := (norm_add_le _ _).trans (add_le_add hn (hzb _))
        _ ≤ r₁ := by linarith only [hδ₀r]
  -- between the sampling times
  intro t hτt
  set k := ⌊(t - τ) / T⌋₊ with hk
  have hkT : (k : ℝ) * T ≤ t - τ := by
    have := Nat.floor_le (div_nonneg (sub_nonneg.mpr hτt) hT.le)
    calc (k : ℝ) * T ≤ (t - τ) / T * T := mul_le_mul_of_nonneg_right this hT.le
      _ = t - τ := by field_simp
  have hkT' : t - τ - k * T ≤ T := by
    have := Nat.lt_floor_add_one ((t - τ) / T)
    have : t - τ < ((k : ℝ) + 1) * T := by
      calc t - τ = (t - τ) / T * T := by field_simp
        _ < ((k : ℝ) + 1) * T := mul_lt_mul_of_pos_right this hT
    linarith
  have hp := hxz _ (hind k).2 (hzr _)
  have hη0 : 0 ≤ η := (sq_nonneg ε).trans hεη
  have hgr := perturbed_sub_le_exp hf.2.2.2.2.1 hℓ hε.le hε1 hη0 (hηε.trans hε1) hℓq
    (fun t ht => (hp t ht).1) (fun t ht => (hp t ht).2.1) (fun t ht => (hp t ht).2.2.2.2) t
    ⟨by linarith, by linarith⟩
  have hVk := (hind k).1
  have hV0 : quadraticForm P (e 0) ≤ p₂ * ‖x τ - z τ‖ ^ 2 := by
    have : e 0 = x τ - z τ := by simp [he]
    rw [this]; exact (hbd _).2
  have hb : p₁ * ‖e k‖ ^ 2 ≤ (1 - c * (ε * T)) ^ k * (p₂ * ‖x τ - z τ‖ ^ 2) :=
    (hbd _).1.trans (hVk.trans (mul_le_mul_of_nonneg_left hV0 (pow_nonneg (by linarith) _)))
  have hfin := decay_arith' hp₁ hp₂ hc hε hε1 hT hch (norm_nonneg _) (norm_nonneg _) hgr hb hkT'
  rw [show c / 2 = q₁ / (16 * p₂) by rw [hcdef]; field_simp; ring] at hfin
  exact hfin

/-- **Instability of perturbed curves near an equilibrium with a Chetaev certificate, explicit
constants.** Let `f` be as in `exp_stable_perturbed` and let `H` be a Chetaev form of `J`:
symmetric, `wᵀHw > 0` for some `w`, `q₁‖e‖² ≤ eᵀ(HJ + JᵀH − 2αH)e` with `α > 0`, `‖H‖ ≤ η_H`,
`‖J‖ ≤ a`. Take `r₁ > 0` with `2r₁ ≤ ρ`, `0 ≤ κ ≤ 1` with `16η_Hκ ≤ q₁`, `2L₂r₁ ≤ κ`, and
`0 < ε ≤ 1`, `ε² ≤ η ≤ ε` with `εTa ≤ 1`, `4εTη_H(a² + 1) ≤ q₁`, `2ε(M + M_q)T ≤ ρ`,
`2ηL_S ≤ κεT`. Let `X y` (`X y 0 = y`) be a family of perturbed curves and `z` a perturbed curve,
with the perturbation bounds for the pairs `(X y, z)` over every period that starts with both in
the ball of radius `r₁`, and let `z` stay within `r₁/2` of `y*`. Then arbitrarily close to `z(0)`
start curves of the family that reach the distance `r₁/2` from `z` (`chetaev_perturbed_step_ge`,
`perturbed_difference_step`). -/
@[tmio T, powerlib_foundation] theorem unstable_perturbed [NeZero n] {f : ℝⁿ → ℝ → ℝⁿ}
    {T ℓ M ρ L₂ : ℝ} {Df : ℝⁿ → ℝ → ℝⁿ →L[ℝ] ℝⁿ} {ystar : ℝⁿ}
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hρ : 0 < ρ) (hL₂ : 0 ≤ L₂)
    (hD : ∀ x, ‖x - ystar‖ ≤ ρ → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ x y, ‖x - ystar‖ ≤ ρ → ‖y - ystar‖ ≤ ρ → ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    (hDc : Continuous (Df ystar)) {J : Matrix (Fin n) (Fin n) ℝ}
    (hA : HasFDerivAt (fieldAverage f T) (op J) ystar)
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian) {w : ℝⁿ} (hHw : 0 < quadraticForm H w)
    {α q₁ a ηH : ℝ} (hα : 0 < α)
    (hQ : ∀ e : ℝⁿ, q₁ * ‖e‖ ^ 2 ≤ quadraticForm (H * J + Jᵀ * H - (2 * α) • H) e)
    (ha : ‖op J‖ ≤ a) (hηH : ‖op H‖ ≤ ηH)
    {r₁ κ ε η ℓq Mq : ℝ} (hr₁ : 0 < r₁) (hr₁ρ : 2 * r₁ ≤ ρ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hκq : 16 * ηH * κ ≤ q₁) (hr₁κ : 2 * L₂ * r₁ ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hηε : η ≤ ε) (hεη : ε ^ 2 ≤ η) (hℓq : 0 ≤ ℓq) (hMq : 0 ≤ Mq)
    (hεa : ε * T * a ≤ 1) (hεH : 4 * (ε * T) * ηH * (a ^ 2 + 1) ≤ q₁)
    (hερ : 2 * ε * (M + Mq) * T ≤ ρ) (hηκ : 2 * η * stroboLip ℓ ℓq L₂ M Mq T ≤ κ * (ε * T))
    {X Q : ℝⁿ → ℝ → ℝⁿ} (hX0 : ∀ y, X y 0 = y) {z qz : ℝ → ℝⁿ}
    (hXz : ∀ y s, ‖X y s - ystar‖ ≤ r₁ → ‖z s - ystar‖ ≤ r₁ → ∀ t ∈ Icc s (s + T),
      HasDerivAt (X y) (ε • f (X y t) t + Q y t) t ∧ HasDerivAt z (ε • f (z t) t + qz t) t ∧
      ‖Q y t‖ ≤ η * Mq ∧ ‖qz t‖ ≤ η * Mq ∧ ‖Q y t - qz t‖ ≤ η * ℓq * ‖X y t - z t‖)
    (hzb : ∀ t, ‖z t - ystar‖ ≤ r₁ / 2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ y, ‖y - z 0‖ ≤ δ ∧ ∃ t, 0 ≤ t ∧ r₁ / 2 ≤ ‖X y t - z t‖ := by
  have hT := hf.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 ystar 0)
  set LS := stroboLip ℓ ℓq L₂ M Mq T with hLS
  set h := ε * T with hh
  have hh0 : 0 < h := mul_pos hε hT
  have hη0 : 0 ≤ η := (sq_nonneg ε).trans hεη
  have hερ' : r₁ + ε * (M + Mq) * T ≤ ρ := by linarith
  have hκ' : L₂ * r₁ + η * LS / (ε * T) ≤ κ := by
    have : η * LS / (ε * T) ≤ κ / 2 := by
      rw [div_le_iff₀ (mul_pos hε hT)]; linarith
    linarith
  have hstep : ∀ e p : ℝⁿ, ‖p‖ ≤ h * κ * ‖e‖ →
      (1 + 2 * α * h) * quadraticForm H e ≤ quadraticForm H (e + h • (op J) e + p) :=
    fun e p hp => chetaev_perturbed_step_ge hH hQ ha hηH hh0 hεa hεH hκ0 hκ1 hκq e p hp
  have hηH0 : 0 < ηH := by
    have h1 := (le_abs_self _).trans (abs_quadraticForm_le H w)
    have h2 : ‖op H‖ * ‖w‖ ^ 2 ≤ ηH * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_right hηH (sq_nonneg _)
    by_contra hneg
    push Not at hneg
    nlinarith [sq_nonneg ‖w‖]
  have hw0 : w ≠ 0 := by
    rintro rfl; simp [quadraticForm] at hHw
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  set s := min δ (r₁ / 2) / (2 * ‖w‖) with hs
  have hs0 : 0 < s := div_pos (lt_min hδ (by positivity)) (by positivity)
  have hsw : ‖s • w‖ ≤ min δ (r₁ / 2) / 2 := by
    rw [norm_smul, Real.norm_of_nonneg hs0.le, hs]; field_simp; rfl
  set y := z 0 + s • w with hy
  refine ⟨y, ?_, ?_⟩
  · rw [hy, add_sub_cancel_left]
    exact hsw.trans (by linarith [min_le_left δ (r₁ / 2), le_min hδ.le (by positivity :
      (0 : ℝ) ≤ r₁ / 2)])
  by_contra hcon
  push Not at hcon
  set e : ℕ → ℝⁿ := fun k => X y (k * T) - z (k * T) with he
  have hzr : ∀ t, ‖z t - ystar‖ ≤ r₁ := fun t => (hzb t).trans (by linarith)
  have hgrow : ∀ k : ℕ, (1 + 2 * α * h) ^ k * quadraticForm H (e 0) ≤ quadraticForm H (e k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hek : ‖e k‖ < r₁ / 2 := hcon _ (by positivity)
      have hxk : ‖X y (k * T) - ystar‖ ≤ r₁ := by
        calc ‖X y (k * T) - ystar‖ = ‖e k + (z (k * T) - ystar)‖ := by
              simp only [he]; congr 1; abel
          _ ≤ r₁ / 2 + r₁ / 2 := (norm_add_le _ _).trans (add_le_add hek.le (hzb _))
          _ = r₁ := by ring
      have hp := hXz y _ hxk (hzr _)
      obtain ⟨p, hpe, hpn⟩ := perturbed_difference_step hf hρ hL₂ hD hDl hDc hA hε hε1 hηε hεη
        hℓq hMq (fun t ht => (hp t ht).1) (fun t ht => (hp t ht).2.1)
        (fun t ht => (hp t ht).2.2.1) (fun t ht => (hp t ht).2.2.2.1)
        (fun t ht => (hp t ht).2.2.2.2) hxk (hzr _) hερ'
      have hek1 : e (k + 1) = e k + h • (op J) (e k) + p := by
        simp only [he]
        rw [show ((k + 1 : ℕ) : ℝ) * T = k * T + T by push_cast; ring, hpe]
      have hpn' : ‖p‖ ≤ h * κ * ‖e k‖ := by
        refine hpn.trans ?_
        simp only [he, hh]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκ' (by positivity))
          (norm_nonneg _)
      have hs := hstep (e k) p hpn'
      rw [← hek1] at hs
      calc (1 + 2 * α * h) ^ (k + 1) * quadraticForm H (e 0) =
          (1 + 2 * α * h) * ((1 + 2 * α * h) ^ k * quadraticForm H (e 0)) := by ring
        _ ≤ (1 + 2 * α * h) * quadraticForm H (e k) :=
            mul_le_mul_of_nonneg_left ih (by positivity)
        _ ≤ quadraticForm H (e (k + 1)) := hs
  have he0 : e 0 = s • w := by simp [he, hX0, hy]
  have hW0 : 0 < quadraticForm H (e 0) := by
    rw [he0, quadraticForm_smul]; positivity
  have hHup : ∀ x : ℝⁿ, quadraticForm H x ≤ ηH * ‖x‖ ^ 2 := fun x =>
    (quadraticForm_le_opNorm_mul_norm_sq H x).trans (mul_le_mul_of_nonneg_right hηH (sq_nonneg _))
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (ηH * (r₁ / 2) ^ 2 / quadraticForm H (e 0))
    (by linarith [mul_pos (mul_pos two_pos hα) hh0] : (1 : ℝ) < 1 + 2 * α * h)
  have hupk : quadraticForm H (e k) ≤ ηH * (r₁ / 2) ^ 2 := by
    refine (hHup _).trans (mul_le_mul_of_nonneg_left ?_ hηH0.le)
    exact pow_le_pow_left₀ (norm_nonneg _) (hcon _ (by positivity)).le 2
  have := hgrow k
  rw [div_lt_iff₀ hW0] at hk
  linarith

/-- **`Averaging.exp_stable_of_hurwitz` with explicit constants** (`ẋ = ε f(x, t) + ε² r(x, t)`).
With a Lyapunov certificate `(P, Q)` of `J = Df̄(y*)` as in `exp_stable_perturbed` and a remainder
`r` with the constants `ℓ_r`, `M_r`: for `r₁ > 0`, `2r₁ ≤ ρ`, `2L₂r₁ ≤ κ`,
`96p₂³κ² ≤ q₁²p₁`, and every depth `0 < ε ≤ 1` with `2εTp₂a² ≤ q₁`, `εTq₁ ≤ p₂`,
`2ε(M + M_r)T ≤ ρ` and `2εL_S ≤ κT`, every solution `z` staying within `δ₀ = r₁p₁/(2p₂)` of `y*`
attracts every solution `x` with `‖x(τ) − z(τ)‖ ≤ δ₀`:
`‖x(t) − z(t)‖ ≤ √(e^{2(ℓ+ℓ_r)T}(p₂/p₁)e^{q₁T/(8p₂)}) e^{−(q₁/(16p₂))ε(t − τ)} ‖x(τ) − z(τ)‖`. -/
@[tmio T, powerlib_foundation] theorem exp_stable_of_lyapunov [NeZero n] {f r : ℝⁿ → ℝ → ℝⁿ}
    {T ℓ M ℓr Mr ρ L₂ : ℝ} {Df : ℝⁿ → ℝ → ℝⁿ →L[ℝ] ℝⁿ} {ystar : ℝⁿ}
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hr : 0 < T ∧ 0 ≤ ℓr ∧ Continuous (Function.uncurry r) ∧ (∀ x t, r x (t + T) = r x t) ∧
      (∀ x y t, ‖r x t - r y t‖ ≤ ℓr * ‖x - y‖) ∧ ∀ x t, ‖r x t‖ ≤ Mr)
    (hρ : 0 < ρ) (hL₂ : 0 ≤ L₂)
    (hD : ∀ x, ‖x - ystar‖ ≤ ρ → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ x y, ‖x - ystar‖ ≤ ρ → ‖y - ystar‖ ≤ ρ → ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    (hDc : Continuous (Df ystar)) {J : Matrix (Fin n) (Fin n) ℝ}
    (hA : HasFDerivAt (fieldAverage f T) (op J) ystar)
    {P Q : Matrix (Fin n) (Fin n) ℝ} (hPd : P.PosDef) (hLyap : P * J + Jᵀ * P = -Q)
    {p₁ p₂ q₁ a : ℝ} (hp₁ : 0 < p₁) (hq₁ : 0 < q₁)
    (hbd : ∀ e : ℝⁿ, p₁ * ‖e‖ ^ 2 ≤ quadraticForm P e ∧ quadraticForm P e ≤ p₂ * ‖e‖ ^ 2)
    (hQ : ∀ e : ℝⁿ, q₁ * ‖e‖ ^ 2 ≤ quadraticForm Q e) (ha : ‖op J‖ ≤ a)
    {r₁ κ ε : ℝ} (hr₁ : 0 < r₁) (hr₁ρ : 2 * r₁ ≤ ρ)
    (hκ : 96 * p₂ ^ 3 * κ ^ 2 ≤ q₁ ^ 2 * p₁) (hr₁κ : 2 * L₂ * r₁ ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεa : 2 * (ε * T) * p₂ * a ^ 2 ≤ q₁) (hεq : ε * T * q₁ ≤ p₂)
    (hερ : 2 * ε * (M + Mr) * T ≤ ρ) (hεL : 2 * ε * stroboLip ℓ ℓr L₂ M Mr T ≤ κ * T)
    {x z : ℝ → ℝⁿ} (hx : ∀ t, HasDerivAt x (ε • f (x t) t + ε ^ 2 • r (x t) t) t)
    (hz : ∀ t, HasDerivAt z (ε • f (z t) t + ε ^ 2 • r (z t) t) t)
    (hzb : ∀ t, ‖z t - ystar‖ ≤ r₁ * p₁ / (2 * p₂)) {τ : ℝ}
    (hxτ : ‖x τ - z τ‖ ≤ r₁ * p₁ / (2 * p₂)) :
    ∀ t, τ ≤ t → ‖x t - z t‖ ≤ Real.sqrt (Real.exp ((ℓ + ℓr) * T) ^ 2 * (p₂ / p₁) *
      Real.exp (q₁ / (8 * p₂) * T)) * Real.exp (-(q₁ / (16 * p₂) * ε * (t - τ))) *
        ‖x τ - z τ‖ := by
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  have hMr : 0 ≤ Mr := (norm_nonneg _).trans (hr.2.2.2.2.2 ystar 0)
  refine exp_stable_perturbed hf hρ hL₂ hD hDl hDc hA hPd hLyap hp₁ hq₁ hbd hQ ha hr₁ hr₁ρ hκ
    hr₁κ hε hε1 hε2 le_rfl hr.2.1 hMr hεa hεq hερ ?_ (qx := fun t => ε ^ 2 • r (x t) t)
    (qz := fun t => ε ^ 2 • r (z t) t) (fun s _ _ t _ => ⟨hx t, hz t, ?_, ?_, ?_⟩) hzb hxτ
  · have := mul_le_mul_of_nonneg_left hεL hε.le
    nlinarith
  · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hr.2.2.2.2.2 _ _) (by positivity)
  · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hr.2.2.2.2.2 _ _) (by positivity)
  · rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity), mul_assoc]
    exact mul_le_mul_of_nonneg_left (hr.2.2.2.2.1 _ _ _) (by positivity)

/-- **`Averaging.unstable_of_root` with explicit constants** (`ẋ = ε f(x, t) + ε² r(x, t)`). With a
Chetaev certificate `H` of `J = Df̄(y*)` as in `unstable_perturbed` and a remainder `r` with the
constants `ℓ_r`, `M_r`: for `r₁ > 0`, `2r₁ ≤ ρ`, `0 ≤ κ ≤ 1`, `16η_Hκ ≤ q₁`, `2L₂r₁ ≤ κ`, and
every depth `0 < ε ≤ 1` with `εTa ≤ 1`, `4εTη_H(a² + 1) ≤ q₁`, `2ε(M + M_r)T ≤ ρ`,
`2εL_S ≤ κT`, every solution `z` staying within `r₁/2` of `y*` is unstable: within any `δ > 0`
of `z(0)` starts a solution that reaches the distance `r₁/2` from `z`. -/
@[tmio T, powerlib_foundation] theorem unstable_of_chetaev [NeZero n] {f r : ℝⁿ → ℝ → ℝⁿ}
    {T ℓ M ℓr Mr ρ L₂ : ℝ} {Df : ℝⁿ → ℝ → ℝⁿ →L[ℝ] ℝⁿ} {ystar : ℝⁿ}
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hr : 0 < T ∧ 0 ≤ ℓr ∧ Continuous (Function.uncurry r) ∧ (∀ x t, r x (t + T) = r x t) ∧
      (∀ x y t, ‖r x t - r y t‖ ≤ ℓr * ‖x - y‖) ∧ ∀ x t, ‖r x t‖ ≤ Mr)
    (hρ : 0 < ρ) (hL₂ : 0 ≤ L₂)
    (hD : ∀ x, ‖x - ystar‖ ≤ ρ → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ x y, ‖x - ystar‖ ≤ ρ → ‖y - ystar‖ ≤ ρ → ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    (hDc : Continuous (Df ystar)) {J : Matrix (Fin n) (Fin n) ℝ}
    (hA : HasFDerivAt (fieldAverage f T) (op J) ystar)
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian) {w : ℝⁿ} (hHw : 0 < quadraticForm H w)
    {α q₁ a ηH : ℝ} (hα : 0 < α)
    (hQ : ∀ e : ℝⁿ, q₁ * ‖e‖ ^ 2 ≤ quadraticForm (H * J + Jᵀ * H - (2 * α) • H) e)
    (ha : ‖op J‖ ≤ a) (hηH : ‖op H‖ ≤ ηH)
    {r₁ κ ε : ℝ} (hr₁ : 0 < r₁) (hr₁ρ : 2 * r₁ ≤ ρ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hκq : 16 * ηH * κ ≤ q₁) (hr₁κ : 2 * L₂ * r₁ ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεa : ε * T * a ≤ 1) (hεH : 4 * (ε * T) * ηH * (a ^ 2 + 1) ≤ q₁)
    (hερ : 2 * ε * (M + Mr) * T ≤ ρ) (hεL : 2 * ε * stroboLip ℓ ℓr L₂ M Mr T ≤ κ * T)
    {z : ℝ → ℝⁿ} (hz : ∀ t, HasDerivAt z (ε • f (z t) t + ε ^ 2 • r (z t) t) t)
    (hzb : ∀ t, ‖z t - ystar‖ ≤ r₁ / 2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x : ℝ → ℝⁿ, (∀ t, HasDerivAt x (ε • f (x t) t + ε ^ 2 • r (x t) t) t) ∧
      ‖x 0 - z 0‖ ≤ δ ∧ ∃ t, 0 ≤ t ∧ r₁ / 2 ≤ ‖x t - z t‖ := by
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  have hMr : 0 ≤ Mr := (norm_nonneg _).trans (hr.2.2.2.2.2 ystar 0)
  have hsol : ∀ y : ℝⁿ, ∃ x : ℝ → ℝⁿ, x 0 = y ∧
      ∀ t, HasDerivAt x (ε • f (x t) t + ε ^ 2 • r (x t) t) t := fun y =>
    ParametricResonance.DuffingMathieu.exists_global_solution
      (full_field_continuous hf.2.2.1 hr.2.2.1 ε)
      (fun t => field_lipschitzWith hf.2.2.2.2.1 hr.2.2.2.2.1 hf.2.1 hr.2.1 hε.le t) y
  choose X hX0 hX using hsol
  have hηκ : 2 * ε ^ 2 * stroboLip ℓ ℓr L₂ M Mr T ≤ κ * (ε * T) := by
    have := mul_le_mul_of_nonneg_left hεL hε.le
    nlinarith
  have hbund : ∀ y s, ‖X y s - ystar‖ ≤ r₁ → ‖z s - ystar‖ ≤ r₁ → ∀ t ∈ Icc s (s + T),
      HasDerivAt (X y) (ε • f (X y t) t + ε ^ 2 • r (X y t) t) t ∧
      HasDerivAt z (ε • f (z t) t + ε ^ 2 • r (z t) t) t ∧
      ‖ε ^ 2 • r (X y t) t‖ ≤ ε ^ 2 * Mr ∧ ‖ε ^ 2 • r (z t) t‖ ≤ ε ^ 2 * Mr ∧
      ‖ε ^ 2 • r (X y t) t - ε ^ 2 • r (z t) t‖ ≤ ε ^ 2 * ℓr * ‖X y t - z t‖ := by
    intro y s _ _ t _
    refine ⟨hX y t, hz t, ?_, ?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hr.2.2.2.2.2 _ _) (by positivity)
    · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hr.2.2.2.2.2 _ _) (by positivity)
    · rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity), mul_assoc]
      exact mul_le_mul_of_nonneg_left (hr.2.2.2.2.1 _ _ _) (by positivity)
  obtain ⟨y, hy, t, ht, hesc⟩ := unstable_perturbed hf hρ hL₂ hD hDl hDc hA hH hHw hα hQ ha hηH
    hr₁ hr₁ρ hκ0 hκ1 hκq hr₁κ hε hε1 hε2 le_rfl hr.2.1 hMr hεa hεH hερ hηκ hX0 hbund hzb hδ
  exact ⟨X y, hX y, by rw [hX0]; exact hy, t, ht, hesc⟩

end StabilityRn

end powerlib.Averaging
