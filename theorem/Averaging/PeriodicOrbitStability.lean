import theorem.Averaging.PeriodicOrbits
import theorem.Linear.Transfer
import dependencies.LeanForControl

/-! # Stability of the averaging periodic orbits; averaging on `[0, ∞)` in the attraction case

`theorem/Averaging/PeriodicOrbits.lean` turns a hyperbolic equilibrium `y*` of the averaged field
into a periodic solution of `ẋ = ε f(x, t) + ε² r(x, t)`. Here the averaged Jacobian decides its
stability, and the KBM estimate on `[0, L/ε]` is extended to all `t ≥ 0` when the averaged
solution is attracted to a hyperbolic sink. Again no differentiability of the flow is used: one
period of the difference of two nearby solutions is a perturbed Euler step
`e ↦ e + εT J e + p` of the linearized averaged field `J = Df̄(y*)`, with `‖p‖ ≤ εT κ ‖e‖ (+ O(ε²))`
and `κ` small near `y*` (`period_difference_step`, `averaged_difference_step`), and such steps
contract the Lyapunov function of a Hurwitz `J` (`exists_lyapunov_euler`) or expand the indefinite
Chetaev form of a `J` with an eigenvalue `Re μ > 0` (`exists_chetaev_euler`).

Scope.
* `ẋ = ε f(x, t) + ε² r(x, t)` with the hypotheses of `Averaging.exists_periodic_orbit` (the
  Banach-space lemmas `solution_sub_le_exp`, `period_difference_step`, `averaged_period_step_le`,
  `averaged_difference_step`); for the stability statements the state space is
  `ℝⁿ = EuclideanSpace ℝ (Fin n)`, `n > 0`, and `Df̄(y*)` is the operator of a real matrix `J`.
* The stability properties are written out in the statements (an exponential attraction
  estimate, uniform in the initial time; escape from a ball), not as predicates of the semantic
  layer. They hold for every solution that stays in a small ball around `y*`, in particular for
  the periodic solution of `Averaging.exists_periodic_orbit` once `ε (2‖B‖C_S/T + (M + M_r)T)` is
  below the radius `δ₀`.
* The constants `ε₀, δ₀, K, β, κ₁` are existential: they come from the Lyapunov matrix
  `PJ + JᵀP = −I` (LeanForControl `IsHurwitz.exists_posDef_unique_solution_continuous_lyapunov`)
  or from the instability certificate
  (`LinearSystems.exists_instability_quadratic_certificate_of_complex_eigenvalue_re_pos`) and
  depend only on `T, ℓ, M, ℓ_r, M_r, ρ, L₂` and `J` — not on `ε`, not on the remainder `r`.
  Explicit constants from a given Lyapunov or Chetaev certificate (stability and instability):
  `theorem/Averaging/PeriodicOrbitConstants.lean` (`exp_stable_of_lyapunov`,
  `unstable_of_chetaev`); for the validity on `[0, ∞)` (`κ₁`):
  `theorem/Averaging/ValidForeverConstants.lean` (`averaging_valid_forever_of_lyapunov`).
* Generic mathematics, no model family.

Source: Bogoliubov–Mitropolsky, *Asymptotic Methods in the Theory of Non-Linear Oscillations*
(the second theorem of Bogoliubov: stability of its periodic solutions); Hale, *Ordinary
Differential Equations*, Ch. V (periodic solutions of averaged systems and their stability);
Sanders–Verhulst–Murdock, *Averaging Methods in Nonlinear Dynamical Systems*, Ch. 5 (attraction:
validity of averaging on `[0, ∞)` near an attracting hyperbolic equilibrium, the
Eckhaus/Sanchez-Palencia theorem); the Lyapunov equation and Chetaev's indefinite quadratic form
(LeanForControl `MatrixAlgebra.quadraticForm`); KBM with a perturbation
`Averaging.kbm_perturbed` on the initial segment.

Results.
* `quadraticForm_add`, `quadraticForm_add_le`, `quadraticForm_euler` — `V(u + v)`,
  `V(u + p) ≤ (1 + θ)V(u) + (1 + 1/θ)V(p)` and `V(e + hJe) = V(e) + h V_{PJ + JᵀP}(e) + h²V(Je)`.
* `exists_lyapunov_euler` — a Hurwitz `J`: `V(e + hJe + p) ≤ (1 − ch)V(e) + Dσ²/h` whenever
  `‖p‖ ≤ hκ‖e‖ + σ`, `0 < h ≤ h₀`, `κ ≤ κ₀`.
* `exists_chetaev_euler` — a characteristic root `Re μ > 0`: an indefinite `W` with a positive
  direction and `W(e + hJe + p) ≥ (1 + 2αh)W(e)` whenever `‖p‖ ≤ hκ‖e‖`.
* `solution_sub_le_exp` — Grönwall over one period, factor `e^{(ℓ + ℓ_r)T}`.
* `period_difference_step`, `averaged_period_step_le`, `averaged_difference_step` — one period of
  the difference of two solutions (or of a solution and an averaged solution) near `y*` is a
  perturbed Euler step of `J`.
* `exp_stable_of_hurwitz` — `J` Hurwitz: every solution staying within `δ₀` of `y*` (the
  periodic one) attracts the solutions starting within `δ₀` of it,
  `‖x(t) − z(t)‖ ≤ K e^{−βε(t − τ)} ‖x(τ) − z(τ)‖` for all `t ≥ τ`.
* `unstable_of_root` — `J` with a characteristic root `Re μ > 0`: every solution staying within
  `δ₀` of `y*` is unstable (nearby solutions reach the distance `δ₀`).
* `averaging_valid_forever` — `J` Hurwitz, the averaged solution in the `δ₀`-ball from the slow
  time `L` on: `‖x(t) − x̄(t)‖ ≤ (κ₁(C_K + C₂) + 2(M + M_r)T) ε` for ALL `t ≥ 0`.
-/

noncomputable section
namespace powerlib.Averaging

open Set Filter Topology intervalIntegral
open scoped Interval

/-! ## Quadratic forms along Euler steps of a linear field -/

section Quadratic

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

open MatrixAlgebra Matrix

/-- The operator `x ↦ A x` of a matrix on `ℝⁿ`. -/
local notation "op" A:max => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A

open scoped RealInnerProductSpace

@[tmio T, powerlib_foundation] private theorem inner_op_comm {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.IsHermitian) (u v : ℝⁿ) : ⟪v, (op P) u⟫ = ⟪u, (op P) v⟫ := by
  have hPt : Pᵀ = P := by
    have := hP.eq; rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  rw [Matrix.inner_toEuclideanCLM, Matrix.inner_toEuclideanCLM, Matrix.dotProduct_mulVec,
    ← hPt, Matrix.vecMul_transpose, hPt, dotProduct_comm]

/-- `V(u + v) = V(u) + 2⟨u, P v⟩ + V(v)` for a symmetric `P`. -/
@[tmio T, powerlib_foundation] theorem quadraticForm_add {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.IsHermitian) (u v : ℝⁿ) :
    quadraticForm P (u + v) = quadraticForm P u + 2 * ⟪u, (op P) v⟫ + quadraticForm P v := by
  simp only [quadraticForm, map_add, inner_add_left, inner_add_right]
  rw [inner_op_comm hP u v]; ring

/-- `2⟨u, P p⟩ ≤ θ V(u) + V(p)/θ` for `P ⪰ 0` (`V(θu − p) ≥ 0`), `θ > 0`. -/
@[tmio T, powerlib_foundation] private theorem two_inner_le {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.PosDef) {θ : ℝ} (hθ : 0 < θ) (u p : ℝⁿ) :
    2 * ⟪u, (op P) p⟫ ≤ θ * quadraticForm P u + quadraticForm P p / θ := by
  have h0 : 0 ≤ quadraticForm P (θ • u - p) := by
    by_cases hz : θ • u - p = 0
    · rw [hz]; simp [quadraticForm]
    · exact (quadraticForm_pos P hP hz).le
  rw [sub_eq_add_neg, quadraticForm_add hP.1, quadraticForm_smul, ← neg_one_smul ℝ p,
    quadraticForm_smul, map_smul, inner_smul_left, inner_smul_right] at h0
  simp only [conj_trivial] at h0
  have key : 2 * ⟪u, (op P) p⟫ ≤ (θ ^ 2 * quadraticForm P u + quadraticForm P p) / θ := by
    rw [le_div_iff₀ hθ]; nlinarith [h0]
  refine key.trans (le_of_eq ?_)
  field_simp

/-- The Euler step of `ẏ = J y`: `V(e + hJe) = V(e) + h V_{PJ + JᵀP}(e) + h² V(Je)`. -/
@[tmio T, powerlib_foundation] theorem quadraticForm_euler {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.IsHermitian) (J : Matrix (Fin n) (Fin n) ℝ) (h : ℝ) (e : ℝⁿ) :
    quadraticForm P (e + h • (op J) e) =
      quadraticForm P e + h * quadraticForm (P * J + Jᵀ * P) e +
        h ^ 2 * quadraticForm P ((op J) e) := by
  have hd := MatrixAlgebra.fderiv_centeredQuadraticForm_apply_matrix J P 0 e
  rw [fderiv_centeredQuadraticForm_apply] at hd
  simp only [sub_zero] at hd
  rw [quadraticForm_add hP, quadraticForm_smul, map_smul, inner_smul_right, ← hd,
    inner_op_comm hP e ((op J) e)]
  ring

/-- `V(u + p) ≤ (1 + θ) V(u) + (1 + 1/θ) V(p)` for `P ≻ 0`, `θ > 0`. -/
@[tmio T, powerlib_foundation] theorem quadraticForm_add_le {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.PosDef) {θ : ℝ} (hθ : 0 < θ) (u p : ℝⁿ) :
    quadraticForm P (u + p) ≤ (1 + θ) * quadraticForm P u + (1 + 1 / θ) * quadraticForm P p := by
  rw [quadraticForm_add hP.1]
  have h := two_inner_le hP hθ u p
  have : quadraticForm P p / θ = 1 / θ * quadraticForm P p := by ring
  linarith

/-- The linear Euler step decreases `V`: with `PJ + JᵀP = −I`, `V ≤ p₂ ‖·‖²` and
`h p₂ ‖J‖² ≤ 1/2`, `V(e + hJe) ≤ (1 − h/(2p₂)) V(e)`. -/
@[tmio T, powerlib_foundation] private theorem lyapunov_euler_decrease
    {P J : Matrix (Fin n) (Fin n) ℝ} (hP : P.IsHermitian) (hLyap : P * J + Jᵀ * P = -1) {p₂ : ℝ}
    (hp₂ : 0 < p₂) (hup : ∀ x : ℝⁿ, quadraticForm P x ≤ p₂ * ‖x‖ ^ 2) {h : ℝ} (hh : 0 ≤ h)
    (hha : h * (p₂ * ‖op J‖ ^ 2) ≤ 2⁻¹) (e : ℝⁿ) :
    quadraticForm P (e + h • (op J) e) ≤ (1 - h / (2 * p₂)) * quadraticForm P e := by
  rw [quadraticForm_euler hP, hLyap]
  have hneg : quadraticForm (-1 : Matrix (Fin n) (Fin n) ℝ) e = -‖e‖ ^ 2 := by
    simp [quadraticForm]
  rw [hneg]
  have hJe : quadraticForm P ((op J) e) ≤ p₂ * (‖op J‖ ^ 2 * ‖e‖ ^ 2) := by
    refine (hup _).trans ?_
    gcongr
    calc ‖(op J) e‖ ^ 2 ≤ (‖op J‖ * ‖e‖) ^ 2 := by
          gcongr; exact (op J).le_opNorm e
      _ = ‖op J‖ ^ 2 * ‖e‖ ^ 2 := by ring
  have h1 : h ^ 2 * quadraticForm P ((op J) e) ≤ h * ‖e‖ ^ 2 / 2 := by
    calc h ^ 2 * quadraticForm P ((op J) e) ≤ h ^ 2 * (p₂ * (‖op J‖ ^ 2 * ‖e‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hJe (sq_nonneg _)
      _ = h * ‖e‖ ^ 2 * (h * (p₂ * ‖op J‖ ^ 2)) := by ring
      _ ≤ h * ‖e‖ ^ 2 * 2⁻¹ := mul_le_mul_of_nonneg_left hha (by positivity)
      _ = h * ‖e‖ ^ 2 / 2 := by ring
  have h2 : h / (2 * p₂) * quadraticForm P e ≤ h * ‖e‖ ^ 2 / 2 := by
    have hee : quadraticForm P e / p₂ ≤ ‖e‖ ^ 2 := by
      rw [div_le_iff₀ hp₂]; linarith [hup e]
    calc h / (2 * p₂) * quadraticForm P e = h / 2 * (quadraticForm P e / p₂) := by
          field_simp
      _ ≤ h / 2 * ‖e‖ ^ 2 := mul_le_mul_of_nonneg_left hee (by positivity)
      _ = h * ‖e‖ ^ 2 / 2 := by ring
  have e3 : quadraticForm P e + h * -‖e‖ ^ 2 + h ^ 2 * quadraticForm P ((op J) e) =
      quadraticForm P e - h * ‖e‖ ^ 2 + h ^ 2 * quadraticForm P ((op J) e) := by ring
  rw [e3]
  have e4 : (1 - h / (2 * p₂)) * quadraticForm P e =
      quadraticForm P e - h / (2 * p₂) * quadraticForm P e := by ring
  rw [e4]
  linarith

/-- The arithmetic of a perturbed contraction step. -/
@[tmio T, powerlib_foundation] private theorem perturbed_step_arith {Ve Vu Vp Vup nE c₁ h κ σ p₁
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

/-- **A Hurwitz matrix makes perturbed Euler steps contract a quadratic Lyapunov function.** For
`J` Hurwitz there are a positive definite `P` (the Lyapunov matrix `PJ + JᵀP = −I`), constants
`0 < p₁ ≤ V(e)/‖e‖² ≤ p₂`, a rate `c > 0`, a step bound `h₀ > 0` (`c h₀ ≤ 1`), a perturbation
bound `κ₀ > 0` and `D ≥ 0` such that every perturbed Euler step `e ↦ e + hJe + p` with
`0 < h ≤ h₀` and `‖p‖ ≤ hκ‖e‖ + σ`, `κ ≤ κ₀`, satisfies `V(e + hJe + p) ≤ (1 − ch)V(e) + Dσ²/h`. -/
@[tmio T, powerlib_foundation] theorem exists_lyapunov_euler [NeZero n]
    {J : Matrix (Fin n) (Fin n) ℝ} (hJ : LinearSystems.IsHurwitz J) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, ∃ p₁ p₂ c h₀ κ₀ D : ℝ, 0 < p₁ ∧ 0 < p₂ ∧ 0 < c ∧ 0 < h₀ ∧
      c * h₀ ≤ 1 ∧ 0 < κ₀ ∧ 0 ≤ D ∧
      (∀ e : ℝⁿ, p₁ * ‖e‖ ^ 2 ≤ quadraticForm P e ∧ quadraticForm P e ≤ p₂ * ‖e‖ ^ 2) ∧
      ∀ h, 0 < h → h ≤ h₀ → ∀ κ σ : ℝ, 0 ≤ κ → κ ≤ κ₀ → 0 ≤ σ → ∀ e p : ℝⁿ,
        ‖p‖ ≤ h * κ * ‖e‖ + σ →
        quadraticForm P (e + h • (op J) e + p) ≤
          (1 - c * h) * quadraticForm P e + D * σ ^ 2 / h := by
  obtain ⟨P, hPd, hEq, -⟩ :=
    hJ.exists_posDef_unique_solution_continuous_lyapunov 1 Matrix.PosDef.one
  obtain ⟨p₁, hp₁, hlow⟩ := exists_pos_mul_norm_sq_le_quadraticForm P hPd
  set p₂ := ‖op P‖ + 1 with hp₂def
  have hp₂ : 0 < p₂ := by positivity
  have hup : ∀ x : ℝⁿ, quadraticForm P x ≤ p₂ * ‖x‖ ^ 2 := fun x =>
    (quadraticForm_le_opNorm_mul_norm_sq P x).trans
      (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
  have hV0 : ∀ x : ℝⁿ, 0 ≤ quadraticForm P x := fun x =>
    (mul_nonneg hp₁.le (sq_nonneg _)).trans (hlow x)
  set c₁ := 1 / (2 * p₂) with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  set h₀ := min (1 / (2 * (p₂ * ‖op J‖ ^ 2 + 1))) p₂ with hh₀
  set κ₀ := min 1 (c₁ ^ 2 * p₁ / (24 * p₂)) with hκ₀
  refine ⟨P, p₁, p₂, c₁ / 4, h₀, κ₀, 6 * p₂ / c₁, hp₁, hp₂, by positivity, by positivity, ?_,
    by positivity, by positivity, fun e => ⟨hlow e, hup e⟩, ?_⟩
  · have : h₀ ≤ p₂ := min_le_right _ _
    calc c₁ / 4 * h₀ ≤ c₁ / 4 * p₂ := by gcongr
      _ ≤ 1 := by rw [hc₁]; field_simp; linarith
  intro h hh hh₀' κ σ hκ hκ₀' hσ e p hp
  have hc₁h : c₁ * h ≤ 2⁻¹ := by
    have : h ≤ p₂ := hh₀'.trans (min_le_right _ _)
    calc c₁ * h ≤ c₁ * p₂ := by gcongr
      _ = 2⁻¹ := by rw [hc₁]; field_simp
  have hha : h * (p₂ * ‖op J‖ ^ 2) ≤ 2⁻¹ := by
    have h1 : h ≤ 1 / (2 * (p₂ * ‖op J‖ ^ 2 + 1)) := hh₀'.trans (min_le_left _ _)
    calc h * (p₂ * ‖op J‖ ^ 2) ≤ 1 / (2 * (p₂ * ‖op J‖ ^ 2 + 1)) * (p₂ * ‖op J‖ ^ 2 + 1) :=
          mul_le_mul h1 (by linarith) (by positivity) (by positivity)
      _ = 2⁻¹ := by field_simp
  have hVu := lyapunov_euler_decrease hPd.1 hEq hp₂ hup hh.le hha e
  rw [show h / (2 * p₂) = c₁ * h by rw [hc₁]; field_simp] at hVu
  have hsplit := quadraticForm_add_le hPd (θ := c₁ * h / 2) (by positivity)
    (e + h • (op J) e) p
  have hVp : quadraticForm P p ≤ 2 * p₂ * (h ^ 2 * κ ^ 2 * ‖e‖ ^ 2 + σ ^ 2) := by
    refine (hup p).trans ?_
    have hp0 : 0 ≤ ‖p‖ := norm_nonneg _
    have h1 : ‖p‖ ^ 2 ≤ (h * κ * ‖e‖ + σ) ^ 2 := pow_le_pow_left₀ hp0 hp 2
    have h2 : (h * κ * ‖e‖ + σ) ^ 2 ≤ 2 * (h ^ 2 * κ ^ 2 * ‖e‖ ^ 2 + σ ^ 2) := by
      nlinarith [sq_nonneg (h * κ * ‖e‖ - σ)]
    nlinarith
  have hκ2 : κ ^ 2 ≤ c₁ ^ 2 * p₁ / (24 * p₂) := by
    have h1 : κ ≤ 1 := hκ₀'.trans (min_le_left _ _)
    have h2 : κ ≤ c₁ ^ 2 * p₁ / (24 * p₂) := hκ₀'.trans (min_le_right _ _)
    nlinarith
  exact perturbed_step_arith hc₁0 hh hc₁h hp₁ hp₂ (hV0 e) (hV0 p) (sq_nonneg _) (hlow e)
    hVu hsplit hVp hκ2

/-- The arithmetic of a perturbed expansion step. -/
@[tmio T, powerlib_foundation] private theorem expansion_arith {We Wu Wup nE nU nP α h κ q₁ η a
    : ℝ} (hh : 0 < h) (hη : 0 ≤ η) (hq₁ : 0 ≤ q₁) (hnE : 0 ≤ nE) (hnP : 0 ≤ nP)
    (hWu : We + h * (q₁ * nE ^ 2 + 2 * α * We) - h ^ 2 * (η * (a ^ 2 * nE ^ 2)) ≤ Wu)
    (hWup : Wu - 2 * (nU * (η * nP)) - η * nP ^ 2 ≤ Wup) (hU : nU ≤ 2 * nE)
    (hP : nP ≤ h * κ * nE) (h1 : h * (η * a ^ 2) ≤ q₁ / 4) (h2 : 4 * η * κ ≤ q₁ / 4)
    (h3 : η * h * κ ^ 2 ≤ q₁ / 4) :
    (1 + 2 * α * h) * We ≤ Wup := by
  have hP2 : nP ^ 2 ≤ (h * κ * nE) ^ 2 := pow_le_pow_left₀ hnP hP 2
  have hUP : nU * nP ≤ 2 * nE * (h * κ * nE) := mul_le_mul hU hP hnP (by positivity)
  have hA : 2 * (nU * (η * nP)) ≤ h * nE ^ 2 * (4 * η * κ) := by
    nlinarith [mul_le_mul_of_nonneg_left hUP hη]
  have hB : η * nP ^ 2 ≤ h * nE ^ 2 * (η * h * κ ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hP2 hη]
  have hC : h ^ 2 * (η * (a ^ 2 * nE ^ 2)) = h * nE ^ 2 * (h * (η * a ^ 2)) := by ring
  have hD : 0 ≤ h * nE ^ 2 * (q₁ - h * (η * a ^ 2) - 4 * η * κ - η * h * κ ^ 2) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith

/-- **An eigenvalue with positive real part makes perturbed Euler steps expand an indefinite
quadratic form** (discrete Chetaev certificate). If `J` has a characteristic root `μ` with
`Re μ > 0`, there are a symmetric `H`, a direction `w` with `W(w) = wᵀHw > 0`, `α > 0`,
`h₀ > 0`, `κ₀ > 0` and `η` with `W ≤ η ‖·‖²` such that every perturbed Euler step with
`0 < h ≤ h₀`, `‖p‖ ≤ hκ‖e‖`, `κ ≤ κ₀` has `W(e + hJe + p) ≥ (1 + 2αh) W(e)` (LeanForControl's
certificate `HJ + JᵀH − 2αH ≻ 0`). -/
@[tmio T, powerlib_foundation] theorem exists_chetaev_euler [NeZero n]
    {J : Matrix (Fin n) (Fin n) ℝ} {μ : ℂ} (hroot : (Linear.characteristicMatrix J μ).det = 0)
    (hμ : 0 < μ.re) :
    ∃ H : Matrix (Fin n) (Fin n) ℝ, ∃ w : ℝⁿ, ∃ α h₀ κ₀ η : ℝ, 0 < α ∧ 0 < h₀ ∧ 0 < κ₀ ∧
      0 < quadraticForm H w ∧ (∀ x : ℝⁿ, quadraticForm H x ≤ η * ‖x‖ ^ 2) ∧
      ∀ h, 0 < h → h ≤ h₀ → ∀ κ : ℝ, 0 ≤ κ → κ ≤ κ₀ → ∀ e p : ℝⁿ, ‖p‖ ≤ h * κ * ‖e‖ →
        (1 + 2 * α * h) * quadraticForm H e ≤ quadraticForm H (e + h • (op J) e + p) := by
  obtain ⟨v, hv, heig⟩ := Linear.exists_eigenvector_of_root hroot
  obtain ⟨α, H, w, hα, hH, -, hHw, hQ⟩ :=
    LinearSystems.exists_instability_quadratic_certificate_of_complex_eigenvalue_re_pos J hv heig hμ
  obtain ⟨q₁, hq₁, hqlow⟩ := exists_pos_mul_norm_sq_le_quadraticForm _ hQ
  set η := ‖op H‖ with hηdef
  set a := ‖op J‖ with hadef
  have hη : 0 ≤ η := norm_nonneg _
  have ha : 0 ≤ a := norm_nonneg _
  set h₀ := min (min (1 / (a + 1)) (q₁ / (4 * (η * a ^ 2 + 1)))) (min 1 (q₁ / (4 * (η + 1))))
    with hh₀
  set κ₀ := min 1 (q₁ / (16 * (η + 1))) with hκ₀
  refine ⟨H, w, α, h₀, κ₀, η, hα, by positivity, by positivity, hHw,
    fun x => quadraticForm_le_opNorm_mul_norm_sq H x, ?_⟩
  intro h hh hh₀' κ hκ hκ₀' e p hp
  have hha : h * a ≤ 1 := by
    have h1 : h ≤ 1 / (a + 1) := hh₀'.trans ((min_le_left _ _).trans (min_le_left _ _))
    calc h * a ≤ 1 / (a + 1) * (a + 1) := mul_le_mul h1 (by linarith) ha (by positivity)
      _ = 1 := by field_simp
  have hh1 : h ≤ 1 := hh₀'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hκ1 : κ ≤ 1 := hκ₀'.trans (min_le_left _ _)
  have c1 : h * (η * a ^ 2) ≤ q₁ / 4 := by
    have h1 : h ≤ q₁ / (4 * (η * a ^ 2 + 1)) :=
      hh₀'.trans ((min_le_left _ _).trans (min_le_right _ _))
    calc h * (η * a ^ 2) ≤ q₁ / (4 * (η * a ^ 2 + 1)) * (η * a ^ 2 + 1) :=
          mul_le_mul h1 (by linarith) (by positivity) (by positivity)
      _ = q₁ / 4 := by field_simp
  have c2 : 4 * η * κ ≤ q₁ / 4 := by
    have h1 : κ ≤ q₁ / (16 * (η + 1)) := hκ₀'.trans (min_le_right _ _)
    calc 4 * η * κ ≤ 4 * (η + 1) * (q₁ / (16 * (η + 1))) :=
          mul_le_mul (by linarith) h1 hκ (by positivity)
      _ = q₁ / 4 := by field_simp; ring
  have c3 : η * h * κ ^ 2 ≤ q₁ / 4 := by
    have h1 : h ≤ q₁ / (4 * (η + 1)) := hh₀'.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hk2 : κ ^ 2 ≤ 1 := by nlinarith
    calc η * h * κ ^ 2 ≤ (η + 1) * (q₁ / (4 * (η + 1))) * 1 := by
          gcongr
          · linarith
      _ = q₁ / 4 := by field_simp
  -- the linear Euler step
  set u := e + h • (op J) e with hu
  have hWu : quadraticForm H e + h * (q₁ * ‖e‖ ^ 2 + 2 * α * quadraticForm H e) -
      h ^ 2 * (η * (a ^ 2 * ‖e‖ ^ 2)) ≤ quadraticForm H u := by
    rw [hu, quadraticForm_euler hH]
    have hsplitQ : quadraticForm (H * J + Jᵀ * H) e =
        quadraticForm (H * J + Jᵀ * H - (2 * α) • H) e + 2 * α * quadraticForm H e := by
      rw [← quadraticForm_matrix_smul, ← quadraticForm_matrix_add, sub_add_cancel]
    rw [hsplitQ]
    have hJe : -(η * (a ^ 2 * ‖e‖ ^ 2)) ≤ quadraticForm H ((op J) e) := by
      have h1 := abs_quadraticForm_le H ((op J) e)
      have h2 : ‖(op J) e‖ ^ 2 ≤ a ^ 2 * ‖e‖ ^ 2 := by
        calc ‖(op J) e‖ ^ 2 ≤ (a * ‖e‖) ^ 2 := by
              gcongr; exact (op J).le_opNorm e
          _ = a ^ 2 * ‖e‖ ^ 2 := by ring
      have h3 := neg_abs_le (quadraticForm H ((op J) e))
      have h4 := mul_le_mul_of_nonneg_left h2 hη
      linarith
    have k1 := mul_le_mul_of_nonneg_left (hqlow e) hh.le
    have k2 := mul_le_mul_of_nonneg_left hJe (sq_nonneg h)
    have e1 : quadraticForm H e + h * (quadraticForm (H * J + Jᵀ * H - (2 * α) • H) e +
        2 * α * quadraticForm H e) + h ^ 2 * quadraticForm H ((op J) e) =
        quadraticForm H e + h * (2 * α * quadraticForm H e) +
          h * quadraticForm (H * J + Jᵀ * H - (2 * α) • H) e +
          h ^ 2 * quadraticForm H ((op J) e) := by ring
    have e2 : quadraticForm H e + h * (q₁ * ‖e‖ ^ 2 + 2 * α * quadraticForm H e) -
        h ^ 2 * (η * (a ^ 2 * ‖e‖ ^ 2)) = quadraticForm H e + h * (2 * α * quadraticForm H e) +
          h * (q₁ * ‖e‖ ^ 2) + h ^ 2 * -(η * (a ^ 2 * ‖e‖ ^ 2)) := by ring
    rw [e1, e2]
    linarith
  -- the perturbation
  have hWup : quadraticForm H u - 2 * (‖u‖ * (η * ‖p‖)) - η * ‖p‖ ^ 2 ≤
      quadraticForm H (u + p) := by
    rw [quadraticForm_add hH u p]
    have h1 : |⟪u, (op H) p⟫| ≤ ‖u‖ * (η * ‖p‖) :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left ((op H).le_opNorm p) (norm_nonneg _))
    have h2 := abs_quadraticForm_le H p
    have h3 := neg_abs_le ⟪u, (op H) p⟫
    have h4 := neg_abs_le (quadraticForm H p)
    linarith
  have hU : ‖u‖ ≤ 2 * ‖e‖ := by
    calc ‖u‖ ≤ ‖e‖ + ‖h • (op J) e‖ := norm_add_le _ _
      _ = ‖e‖ + h * ‖(op J) e‖ := by rw [norm_smul, Real.norm_of_nonneg hh.le]
      _ ≤ ‖e‖ + h * (a * ‖e‖) := by gcongr; exact (op J).le_opNorm e
      _ ≤ 2 * ‖e‖ := by nlinarith [norm_nonneg e]
  exact expansion_arith hh hη hq₁.le (norm_nonneg e) (norm_nonneg p) hWu hWup hU hp
    c1 c2 c3

end Quadratic

/-! ## Exponential stability -/

section Stability

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

local notation "op" A:max => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f r : E → ℝ → E} {T ℓ M ℓr Mr ρ L₂ : ℝ} {Df : E → ℝ → E →L[ℝ] E} {ystar : E}

/-- **Grönwall over one period**: two solutions of `ẋ = ε f(x, t) + ε² r(x, t)` (`0 ≤ ε ≤ 1`)
separate at most by the factor `e^{(ℓ + ℓ_r)T}` over a time `t − s ≤ T`. -/
@[tmio T, powerlib_foundation] theorem solution_sub_le_exp
    (hfl : ∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖)
    (hrl : ∀ x y t, ‖r x t - r y t‖ ≤ ℓr * ‖x - y‖) (hℓ : 0 ≤ ℓ) (hℓr : 0 ≤ ℓr) {ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {x z : ℝ → E}
    (hx : ∀ t, HasDerivAt x (ε • f (x t) t + ε ^ 2 • r (x t) t) t)
    (hz : ∀ t, HasDerivAt z (ε • f (z t) t + ε ^ 2 • r (z t) t) t) {s t : ℝ} (hst : s ≤ t)
    (htT : t - s ≤ T) : ‖x t - z t‖ ≤ Real.exp ((ℓ + ℓr) * T) * ‖x s - z s‖ := by
  have hK0 : 0 ≤ ε * ℓ + ε ^ 2 * ℓr := by positivity
  have hxc : Continuous x := continuous_iff_continuousAt.mpr fun t => (hx t).continuousAt
  have hzc : Continuous z := continuous_iff_continuousAt.mpr fun t => (hz t).continuousAt
  have h := dist_le_of_trajectories_ODE (v := fun t y => ε • f y t + ε ^ 2 • r y t)
    (fun t => field_lipschitzWith hfl hrl hℓ hℓr hε t) hxc.continuousOn
    (fun t _ => (hx t).hasDerivWithinAt) hzc.continuousOn
    (fun t _ => (hz t).hasDerivWithinAt) (le_of_eq rfl) t ⟨hst, le_rfl⟩
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hK0] at h
  refine h.trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have h1 : ε * ℓ + ε ^ 2 * ℓr ≤ ℓ + ℓr := by
    have : ε ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this hℓr]
  exact mul_le_mul h1 htT (by linarith) (by positivity)

/-- **One period of the difference of two solutions near `y*` is a perturbed Euler step of the
linearized averaged field**: `x(s + T) − z(s + T) = e + εT A e + p` with `e = x(s) − z(s)`,
`A = Df̄(y*)` and `‖p‖ ≤ εT (L₂ r₁ + ε L_S/T) ‖e‖`, while `x(s)`, `z(s)` lie in the ball of
radius `r₁` (`r₁ ≤ ρ`, `r₁ + ε(M + M_r)T ≤ ρ`). -/
@[tmio T, powerlib_foundation] theorem period_difference_step [CompleteSpace E]
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hr : 0 < T ∧ 0 ≤ ℓr ∧ Continuous (Function.uncurry r) ∧ (∀ x t, r x (t + T) = r x t) ∧
      (∀ x y t, ‖r x t - r y t‖ ≤ ℓr * ‖x - y‖) ∧ ∀ x t, ‖r x t‖ ≤ Mr)
    (hρ : 0 < ρ) (hL₂ : 0 ≤ L₂)
    (hD : ∀ x, ‖x - ystar‖ ≤ ρ → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ x y, ‖x - ystar‖ ≤ ρ → ‖y - ystar‖ ≤ ρ → ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    (hDc : Continuous (Df ystar)) {A : E →L[ℝ] E} (hA : HasFDerivAt (fieldAverage f T) A ystar)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {x z : ℝ → E}
    (hx : ∀ t, HasDerivAt x (ε • f (x t) t + ε ^ 2 • r (x t) t) t)
    (hz : ∀ t, HasDerivAt z (ε • f (z t) t + ε ^ 2 • r (z t) t) t) {s r₁ : ℝ}
    (hxs : ‖x s - ystar‖ ≤ r₁) (hzs : ‖z s - ystar‖ ≤ r₁) (hr₁ : r₁ + ε * (M + Mr) * T ≤ ρ) :
    ∃ p : E, x (s + T) - z (s + T) = (x s - z s) + (ε * T) • A (x s - z s) + p ∧
      ‖p‖ ≤ ε * T * (L₂ * r₁ + ε * stroboLip ℓ ℓr L₂ M Mr T / T) * ‖x s - z s‖ := by
  have hT := hf.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 ystar 0)
  have hMr : 0 ≤ Mr := (norm_nonneg _).trans (hr.2.2.2.2.2 ystar 0)
  have hr₁ρ : r₁ ≤ ρ := by nlinarith [mul_nonneg (mul_nonneg hε.le (add_nonneg hM hMr)) hT.le]
  refine ⟨(ε * T) • (fieldAverage f T (x s) - fieldAverage f T (z s) - A (x s - z s)) +
    ((x (s + T) - x s - (ε * T) • fieldAverage f T (x s)) -
      (z (s + T) - z s - (ε * T) • fieldAverage f T (z s))), ?_, ?_⟩
  · simp only [smul_sub]; abel
  have h1 := fieldAverage_sub_linear_le hf hρ hL₂ hD hDl hDc hA hr₁ρ hxs hzs
  have h2 := period_step_sub_le hf hr hL₂ hD hDl hε.le hε1 hx hz hxs hzs hr₁
  calc _ ≤ ε * T * (L₂ * r₁ * ‖x s - z s‖) +
        ε ^ 2 * stroboLip ℓ ℓr L₂ M Mr T * ‖x s - z s‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ h2)
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ε * T * (L₂ * r₁ + ε * stroboLip ℓ ℓr L₂ M Mr T / T) * ‖x s - z s‖ := by
        field_simp

/-- **One period of the averaged equation**: a solution of `x̄̇ = ε f̄(x̄)` (`0 ≤ ε`) has
`‖x̄(s + T) − x̄(s) − εT f̄(x̄(s))‖ ≤ ε² ℓ M T²`. -/
@[tmio T, powerlib_foundation] theorem averaged_period_step_le
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    {ε : ℝ} (hε : 0 ≤ ε) {xbar : ℝ → E}
    (hxbar : ∀ t, HasDerivAt xbar (ε • fieldAverage f T (xbar t)) t) (s : ℝ) :
    ‖xbar (s + T) - xbar s - (ε * T) • fieldAverage f T (xbar s)‖ ≤ ε ^ 2 * (ℓ * M * T ^ 2) := by
  have hT := hf.1
  have hℓ := hf.2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 (xbar s) 0)
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun u => xbar u - (ε * (u - s)) • fieldAverage f T (xbar s))
    (f' := fun u => ε • fieldAverage f T (xbar u) - ε • fieldAverage f T (xbar s))
    (C := ε * (ℓ * (ε * M * T))) (a := s) (b := s + T)
    (fun u _ => by
      have h1 : HasDerivAt (fun u => (ε * (u - s)) • fieldAverage f T (xbar s))
          (ε • fieldAverage f T (xbar s)) u := by
        have := (((hasDerivAt_id u).sub_const s).const_mul ε).smul_const
          (fieldAverage f T (xbar s))
        simpa using this
      exact ((hxbar u).sub h1).hasDerivWithinAt)
    (fun u hu => by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg hε]
      refine mul_le_mul_of_nonneg_left ((fieldAverage_lipschitz hf _ _).trans
        (mul_le_mul_of_nonneg_left ?_ hℓ)) hε
      refine (averaged_drift hf hε hxbar hu.1).trans ?_
      exact mul_le_mul_of_nonneg_left (by linarith [hu.2]) (by positivity))
    (s + T) ⟨by linarith, le_rfl⟩
  have e : xbar (s + T) - (ε * (s + T - s)) • fieldAverage f T (xbar s) -
      (xbar s - (ε * (s - s)) • fieldAverage f T (xbar s)) =
      xbar (s + T) - xbar s - (ε * T) • fieldAverage f T (xbar s) := by
    rw [show s + T - s = T by ring, sub_self, mul_zero, zero_smul, sub_zero]; abel
  rw [e] at h
  calc _ ≤ ε * (ℓ * (ε * M * T)) * (s + T - s) := h
    _ = ε ^ 2 * (ℓ * M * T ^ 2) := by ring

/-- **One period of the difference between a solution and an averaged solution near `y*`**:
`x(s + T) − x̄(s + T) = e + εT A e + p` with `e = x(s) − x̄(s)`, `A = Df̄(y*)` and
`‖p‖ ≤ εT L₂ r₁ ‖e‖ + ε²(C_S + ℓMT²)`, while `x(s)`, `x̄(s)` lie in the ball of radius `r₁ ≤ ρ`. -/
@[tmio T, powerlib_foundation] theorem averaged_difference_step [CompleteSpace E]
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hrc : Continuous (Function.uncurry r)) (hrM : ∀ x t, ‖r x t‖ ≤ Mr)
    (hρ : 0 < ρ) (hL₂ : 0 ≤ L₂)
    (hD : ∀ x, ‖x - ystar‖ ≤ ρ → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ x y, ‖x - ystar‖ ≤ ρ → ‖y - ystar‖ ≤ ρ → ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    (hDc : Continuous (Df ystar)) {A : E →L[ℝ] E} (hA : HasFDerivAt (fieldAverage f T) A ystar)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {x xbar : ℝ → E}
    (hx : ∀ t, HasDerivAt x (ε • f (x t) t + ε ^ 2 • r (x t) t) t)
    (hxbar : ∀ t, HasDerivAt xbar (ε • fieldAverage f T (xbar t)) t) {s r₁ : ℝ}
    (hxs : ‖x s - ystar‖ ≤ r₁) (hxbs : ‖xbar s - ystar‖ ≤ r₁) (hr₁ : r₁ ≤ ρ) :
    ∃ p : E, x (s + T) - xbar (s + T) = (x s - xbar s) + (ε * T) • A (x s - xbar s) + p ∧
      ‖p‖ ≤ ε * T * (L₂ * r₁) * ‖x s - xbar s‖ +
        ε ^ 2 * (stroboConst ℓ M Mr T + ℓ * M * T ^ 2) := by
  have hT := hf.1
  refine ⟨(ε * T) • (fieldAverage f T (x s) - fieldAverage f T (xbar s) - A (x s - xbar s)) +
    ((x (s + T) - x s - (ε * T) • fieldAverage f T (x s)) -
      (xbar (s + T) - xbar s - (ε * T) • fieldAverage f T (xbar s))), ?_, ?_⟩
  · simp only [smul_sub]; abel
  have h1 := fieldAverage_sub_linear_le hf hρ hL₂ hD hDl hDc hA hr₁ hxs hxbs
  have h2 := period_step_le hf hrc hrM hε.le hε1 hx s
  have h3 := averaged_period_step_le hf hε.le hxbar s
  calc _ ≤ ε * T * (L₂ * r₁ * ‖x s - xbar s‖) +
        (ε ^ 2 * (ℓ * (M + Mr) * T ^ 2 + Mr * T) + ε ^ 2 * (ℓ * M * T ^ 2)) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ((norm_sub_le _ _).trans (add_le_add h2 h3)))
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ε * T * (L₂ * r₁) * ‖x s - xbar s‖ + ε ^ 2 * (stroboConst ℓ M Mr T + ℓ * M * T ^ 2) := by
        rw [stroboConst]; ring

end Stability

section StabilityRn

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

local notation "op" A:max => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A

open MatrixAlgebra

/-- `min(1, x)² ≤ x` for `x > 0`. -/
@[tmio T, powerlib_foundation] private theorem min_one_sq_le {x : ℝ} (hx : 0 < x) :
    min 1 x ^ 2 ≤ x := by
  rcases le_total x 1 with h | h
  · rw [min_eq_right h]; nlinarith
  · rw [min_eq_left h]; linarith

/-- The arithmetic of the final exponential estimate: from `a ≤ G b`,
`p₁ b² ≤ (1 − ch)^k p₂ d²` and `kT ≤ t − τ < (k + 1)T`, `h = εT`, `ε ≤ 1`:
`a ≤ √(G²(p₂/p₁)e^{cT}) e^{−(c/2)ε(t − τ)} d`. -/
@[tmio T, powerlib_foundation] private theorem decay_arith {a b d G p₁ p₂ c ε T t τ : ℝ} {k : ℕ}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hc : 0 < c) (hε : 0 < ε) (hε1 : ε ≤ 1)
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

/-- **Exponential stability near a Hurwitz equilibrium of the averaged field.** Let `f` be as in
`Averaging.exists_periodic_orbit` on `ℝⁿ` and let `Df̄(y*) = J` be Hurwitz. There are `ε₀ > 0`,
`δ₀ > 0`, `K > 0` and `β > 0` such that for every `0 < ε ≤ ε₀` and every remainder `r` with the
constants `ℓ_r`, `M_r`: every solution `z` of `ẋ = ε f(x, t) + ε² r(x, t)` that stays in the
ball `‖z(t) − y*‖ ≤ δ₀` (in particular the periodic solution of `exists_periodic_orbit` for small
`ε`) attracts every solution `x` starting within `δ₀` of it, at the slow rate `βε`:
`‖x(t) − z(t)‖ ≤ K e^{−βε(t − τ)} ‖x(τ) − z(τ)‖` for `t ≥ τ`, uniformly in the initial time `τ`.
(The period map contracts the Lyapunov function of `J` by `1 − cεT`, `exists_lyapunov_euler`,
`period_difference_step`.) -/
@[tmio T, powerlib_foundation] theorem exp_stable_of_hurwitz [NeZero n] {f : ℝⁿ → ℝ → ℝⁿ}
    {T ℓ M ℓr Mr ρ L₂ : ℝ} {Df : ℝⁿ → ℝ → ℝⁿ →L[ℝ] ℝⁿ} {ystar : ℝⁿ}
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hρ : 0 < ρ) (hL₂ : 0 ≤ L₂)
    (hD : ∀ x, ‖x - ystar‖ ≤ ρ → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ x y, ‖x - ystar‖ ≤ ρ → ‖y - ystar‖ ≤ ρ → ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    (hDc : Continuous (Df ystar)) {J : Matrix (Fin n) (Fin n) ℝ}
    (hA : HasFDerivAt (fieldAverage f T) (op J) ystar) (hJ : LinearSystems.IsHurwitz J)
    (hℓr : 0 ≤ ℓr) (hMr : 0 ≤ Mr) :
    ∃ ε₀ δ₀ K β : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧ 0 < K ∧ 0 < β ∧
      ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ r : ℝⁿ → ℝ → ℝⁿ,
      (0 < T ∧ 0 ≤ ℓr ∧ Continuous (Function.uncurry r) ∧ (∀ x t, r x (t + T) = r x t) ∧
        (∀ x y t, ‖r x t - r y t‖ ≤ ℓr * ‖x - y‖) ∧ ∀ x t, ‖r x t‖ ≤ Mr) →
      ∀ x z : ℝ → ℝⁿ, (∀ t, HasDerivAt x (ε • f (x t) t + ε ^ 2 • r (x t) t) t) →
        (∀ t, HasDerivAt z (ε • f (z t) t + ε ^ 2 • r (z t) t) t) →
        (∀ t, ‖z t - ystar‖ ≤ δ₀) → ∀ τ, ‖x τ - z τ‖ ≤ δ₀ →
        ∀ t, τ ≤ t → ‖x t - z t‖ ≤ K * Real.exp (-(β * ε * (t - τ))) * ‖x τ - z τ‖ := by
  obtain ⟨P, p₁, p₂, c, h₀, κ₀, D, hp₁, hp₂, hc, hh₀, hch₀, hκ₀, hD0, hbd, hstep⟩ :=
    exists_lyapunov_euler hJ
  have hT := hf.1
  have hℓ := hf.2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 ystar 0)
  set LS := stroboLip ℓ ℓr L₂ M Mr T with hLS
  have hLS0 : 0 ≤ LS := by rw [hLS, stroboLip]; positivity
  set r₁ := min (ρ / 2) (κ₀ / (2 * (L₂ + 1))) with hr₁
  have hr₁0 : 0 < r₁ := lt_min (by positivity) (by positivity)
  have hr₁ρ : r₁ ≤ ρ / 2 := min_le_left _ _
  have hr₁κ : L₂ * r₁ ≤ κ₀ / 2 := by
    have h1 : r₁ ≤ κ₀ / (2 * (L₂ + 1)) := min_le_right _ _
    calc L₂ * r₁ ≤ (L₂ + 1) * (κ₀ / (2 * (L₂ + 1))) :=
          mul_le_mul (by linarith) h1 hr₁0.le (by positivity)
      _ = κ₀ / 2 := by field_simp
  set δ₀ := r₁ / 2 * min 1 (p₁ / p₂) with hδ₀
  have hδ₀0 : 0 < δ₀ := mul_pos (by positivity) (lt_min one_pos (by positivity))
  have hδ₀r : δ₀ ≤ r₁ / 2 := by
    rw [hδ₀]; exact mul_le_of_le_one_right (by positivity) (min_le_left _ _)
  have hδ₀sq : p₂ / p₁ * δ₀ ^ 2 ≤ (r₁ / 2) ^ 2 := by
    rw [hδ₀, mul_pow]
    have h1 := min_one_sq_le (div_pos hp₁ hp₂)
    calc p₂ / p₁ * ((r₁ / 2) ^ 2 * min 1 (p₁ / p₂) ^ 2) ≤ p₂ / p₁ * ((r₁ / 2) ^ 2 * (p₁ / p₂)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (sq_nonneg _)) (by positivity)
      _ = (r₁ / 2) ^ 2 := by field_simp
  set ε₀ := min (min 1 (h₀ / T)) (min (κ₀ * T / (2 * (LS + 1))) (ρ / (2 * ((M + Mr) * T + 1))))
    with hε₀
  set G := Real.exp ((ℓ + ℓr) * T) with hG
  have hG1 : 1 ≤ G := Real.one_le_exp (by positivity)
  set K := Real.sqrt (G ^ 2 * (p₂ / p₁) * Real.exp (c * T)) with hK
  refine ⟨ε₀, δ₀, K, c / 2, by positivity, hδ₀0, Real.sqrt_pos.mpr (by positivity), by positivity,
    ?_⟩
  intro ε hε hεε₀ r hr x z hx hz hzb τ hxτ t hτt
  have hε1 : ε ≤ 1 := hεε₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεh : ε * T ≤ h₀ := by
    have : ε ≤ h₀ / T := hεε₀.trans ((min_le_left _ _).trans (min_le_right _ _))
    rwa [le_div_iff₀ hT] at this
  have hεL : ε * LS / T ≤ κ₀ / 2 := by
    have h1 : ε ≤ κ₀ * T / (2 * (LS + 1)) := hεε₀.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [div_le_iff₀ hT]
    calc ε * LS ≤ κ₀ * T / (2 * (LS + 1)) * (LS + 1) :=
          mul_le_mul h1 (by linarith) hLS0 (by positivity)
      _ = κ₀ / 2 * T := by field_simp
  have hερ : r₁ + ε * (M + Mr) * T ≤ ρ := by
    have h1 : ε ≤ ρ / (2 * ((M + Mr) * T + 1)) :=
      hεε₀.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h2 : ε * (M + Mr) * T ≤ ρ / 2 := by
      calc ε * (M + Mr) * T = ε * ((M + Mr) * T) := by ring
        _ ≤ ρ / (2 * ((M + Mr) * T + 1)) * ((M + Mr) * T + 1) :=
            mul_le_mul h1 (by linarith) (by positivity) (by positivity)
        _ = ρ / 2 := by field_simp
    linarith
  set h := ε * T with hh
  have hh0 : 0 < h := mul_pos hε hT
  have hch : c * h ≤ 1 := (mul_le_mul_of_nonneg_left hεh hc.le).trans hch₀
  have hzr : ∀ s, ‖z s - ystar‖ ≤ r₁ := fun s => (hzb s).trans (by linarith)
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
      obtain ⟨p, hpe, hpn⟩ := period_difference_step hf hr hρ hL₂ hD hDl hDc hA hε hε1 hx hz
        hxk (hzr _) hερ
      have hκ : L₂ * r₁ + ε * LS / T ≤ κ₀ := by linarith
      have hκ0 : 0 ≤ L₂ * r₁ + ε * LS / T := by positivity
      have hek : e (k + 1) = e k + h • (op J) (e k) + p := by
        simp only [he]
        rw [show τ + ((k + 1 : ℕ) : ℝ) * T = τ + k * T + T by push_cast; ring, hpe]
      have hs := hstep h hh0 hεh _ 0 hκ0 hκ le_rfl (e k) p (by simpa [he, hh] using hpn)
      rw [← hek] at hs
      simp only [sq, mul_zero, zero_div, add_zero] at hs
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
          rw [div_mul_eq_mul_div, le_div_iff₀ hp₁]; nlinarith
        linarith
      have hn : ‖e (k + 1)‖ ≤ r₁ / 2 :=
        (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
      calc ‖x (τ + ((k + 1 : ℕ) : ℝ) * T) - ystar‖ =
          ‖e (k + 1) + (z (τ + ((k + 1 : ℕ) : ℝ) * T) - ystar)‖ := by
            simp only [he]; congr 1; abel
        _ ≤ r₁ / 2 + δ₀ := (norm_add_le _ _).trans (add_le_add hn (hzb _))
        _ ≤ r₁ := by linarith
  -- between the sampling times
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
  have hgr := solution_sub_le_exp hf.2.2.2.2.1 hr.2.2.2.2.1 hℓ hℓr hε.le hε1 hx hz
    (T := T) (s := τ + k * T) (t := t) (by linarith) (by linarith)
  have hVk := (hind k).1
  have hV0 : quadraticForm P (e 0) ≤ p₂ * ‖x τ - z τ‖ ^ 2 := by
    have : e 0 = x τ - z τ := by simp [he]
    rw [this]; exact (hbd _).2
  have hb : p₁ * ‖e k‖ ^ 2 ≤ (1 - c * (ε * T)) ^ k * (p₂ * ‖x τ - z τ‖ ^ 2) :=
    (hbd _).1.trans (hVk.trans (mul_le_mul_of_nonneg_left hV0 (pow_nonneg (by linarith) _)))
  exact decay_arith hp₁ hp₂ hc hε hε1 hT hch (norm_nonneg _) (norm_nonneg _) hgr hb hkT'

/-- **Instability near an equilibrium of the averaged field with an unstable eigenvalue.** Let `f`
be as in `exp_stable_of_hurwitz` and let `Df̄(y*) = J` have a characteristic root `μ` with
`Re μ > 0`. There are `ε₀ > 0` and `δ₀ > 0` such that for every `0 < ε ≤ ε₀` and every remainder
`r` with the constants `ℓ_r`, `M_r`, every solution `z` of `ẋ = ε f(x, t) + ε² r(x, t)` that stays
in the ball `‖z(t) − y*‖ ≤ δ₀` (in particular the periodic solution of `exists_periodic_orbit`)
is unstable: arbitrarily close to `z(0)` start solutions that reach the distance `δ₀` from `z`.
(Discrete Chetaev argument on the period map with the indefinite quadratic form of
`exists_chetaev_euler`.) -/
@[tmio T, powerlib_foundation] theorem unstable_of_root [NeZero n] {f : ℝⁿ → ℝ → ℝⁿ}
    {T ℓ M ℓr Mr ρ L₂ : ℝ} {Df : ℝⁿ → ℝ → ℝⁿ →L[ℝ] ℝⁿ} {ystar : ℝⁿ}
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hρ : 0 < ρ) (hL₂ : 0 ≤ L₂)
    (hD : ∀ x, ‖x - ystar‖ ≤ ρ → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ x y, ‖x - ystar‖ ≤ ρ → ‖y - ystar‖ ≤ ρ → ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    (hDc : Continuous (Df ystar)) {J : Matrix (Fin n) (Fin n) ℝ}
    (hA : HasFDerivAt (fieldAverage f T) (op J) ystar) {μ : ℂ}
    (hroot : (Linear.characteristicMatrix J μ).det = 0) (hμ : 0 < μ.re) (hℓr : 0 ≤ ℓr)
    (hMr : 0 ≤ Mr) :
    ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ r : ℝⁿ → ℝ → ℝⁿ,
      (0 < T ∧ 0 ≤ ℓr ∧ Continuous (Function.uncurry r) ∧ (∀ x t, r x (t + T) = r x t) ∧
        (∀ x y t, ‖r x t - r y t‖ ≤ ℓr * ‖x - y‖) ∧ ∀ x t, ‖r x t‖ ≤ Mr) →
      ∀ z : ℝ → ℝⁿ, (∀ t, HasDerivAt z (ε • f (z t) t + ε ^ 2 • r (z t) t) t) →
        (∀ t, ‖z t - ystar‖ ≤ δ₀) → ∀ δ, 0 < δ →
        ∃ x : ℝ → ℝⁿ, (∀ t, HasDerivAt x (ε • f (x t) t + ε ^ 2 • r (x t) t) t) ∧
          ‖x 0 - z 0‖ ≤ δ ∧ ∃ t, 0 ≤ t ∧ δ₀ ≤ ‖x t - z t‖ := by
  obtain ⟨H, w, α, h₀, κ₀, η, hα, hh₀, hκ₀, hHw, hHup, hstep⟩ := exists_chetaev_euler hroot hμ
  have hT := hf.1
  have hℓ := hf.2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 ystar 0)
  set LS := stroboLip ℓ ℓr L₂ M Mr T with hLS
  have hLS0 : 0 ≤ LS := by rw [hLS, stroboLip]; positivity
  set r₁ := min (ρ / 2) (κ₀ / (2 * (L₂ + 1))) with hr₁
  have hr₁0 : 0 < r₁ := lt_min (by positivity) (by positivity)
  have hr₁ρ : r₁ ≤ ρ / 2 := min_le_left _ _
  have hr₁κ : L₂ * r₁ ≤ κ₀ / 2 := by
    have h1 : r₁ ≤ κ₀ / (2 * (L₂ + 1)) := min_le_right _ _
    calc L₂ * r₁ ≤ (L₂ + 1) * (κ₀ / (2 * (L₂ + 1))) :=
          mul_le_mul (by linarith) h1 hr₁0.le (by positivity)
      _ = κ₀ / 2 := by field_simp
  set ε₀ := min (min 1 (h₀ / T)) (min (κ₀ * T / (2 * (LS + 1))) (ρ / (2 * ((M + Mr) * T + 1))))
    with hε₀
  refine ⟨ε₀, r₁ / 2, by positivity, by positivity, ?_⟩
  intro ε hε hεε₀ r hr z hz hzb δ hδ
  have hε1 : ε ≤ 1 := hεε₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεh : ε * T ≤ h₀ := by
    have : ε ≤ h₀ / T := hεε₀.trans ((min_le_left _ _).trans (min_le_right _ _))
    rwa [le_div_iff₀ hT] at this
  have hεL : ε * LS / T ≤ κ₀ / 2 := by
    have h1 : ε ≤ κ₀ * T / (2 * (LS + 1)) := hεε₀.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [div_le_iff₀ hT]
    calc ε * LS ≤ κ₀ * T / (2 * (LS + 1)) * (LS + 1) :=
          mul_le_mul h1 (by linarith) hLS0 (by positivity)
      _ = κ₀ / 2 * T := by field_simp
  have hερ : r₁ + ε * (M + Mr) * T ≤ ρ := by
    have h1 : ε ≤ ρ / (2 * ((M + Mr) * T + 1)) :=
      hεε₀.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h2 : ε * (M + Mr) * T ≤ ρ / 2 := by
      calc ε * (M + Mr) * T = ε * ((M + Mr) * T) := by ring
        _ ≤ ρ / (2 * ((M + Mr) * T + 1)) * ((M + Mr) * T + 1) :=
            mul_le_mul h1 (by linarith) (by positivity) (by positivity)
        _ = ρ / 2 := by field_simp
    linarith
  set h := ε * T with hh
  have hh0 : 0 < h := mul_pos hε hT
  -- the escaping solution
  have hw0 : w ≠ 0 := by
    rintro rfl; simp [quadraticForm] at hHw
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  set s := min δ (r₁ / 2) / (2 * ‖w‖) with hs
  have hs0 : 0 < s := div_pos (lt_min hδ (by positivity)) (by positivity)
  have hsw : ‖s • w‖ ≤ min δ (r₁ / 2) / 2 := by
    rw [norm_smul, Real.norm_of_nonneg hs0.le, hs]; field_simp; rfl
  obtain ⟨x, hx0, hx⟩ := ParametricResonance.DuffingMathieu.exists_global_solution
    (full_field_continuous hf.2.2.1 hr.2.2.1 ε)
    (fun t => field_lipschitzWith hf.2.2.2.2.1 hr.2.2.2.2.1 hℓ hℓr hε.le t) (z 0 + s • w)
  refine ⟨x, hx, ?_, ?_⟩
  · rw [hx0, add_sub_cancel_left]
    exact hsw.trans (by linarith [min_le_left δ (r₁ / 2), le_min hδ.le (by positivity :
      (0 : ℝ) ≤ r₁ / 2)])
  by_contra hcon
  push Not at hcon
  set e : ℕ → ℝⁿ := fun k => x (k * T) - z (k * T) with he
  have hzr : ∀ t, ‖z t - ystar‖ ≤ r₁ := fun t => (hzb t).trans (by linarith)
  have hgrow : ∀ k : ℕ, (1 + 2 * α * h) ^ k * quadraticForm H (e 0) ≤ quadraticForm H (e k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hek : ‖e k‖ < r₁ / 2 := hcon _ (by positivity)
      have hxk : ‖x (k * T) - ystar‖ ≤ r₁ := by
        calc ‖x (k * T) - ystar‖ = ‖e k + (z (k * T) - ystar)‖ := by simp only [he]; congr 1; abel
          _ ≤ r₁ / 2 + r₁ / 2 := (norm_add_le _ _).trans (add_le_add hek.le (hzb _))
          _ = r₁ := by ring
      obtain ⟨p, hpe, hpn⟩ := period_difference_step hf hr hρ hL₂ hD hDl hDc hA hε hε1 hx hz
        hxk (hzr _) hερ
      have hκ : L₂ * r₁ + ε * LS / T ≤ κ₀ := by linarith
      have hκ0 : 0 ≤ L₂ * r₁ + ε * LS / T := by positivity
      have hek1 : e (k + 1) = e k + h • (op J) (e k) + p := by
        simp only [he]
        rw [show ((k + 1 : ℕ) : ℝ) * T = k * T + T by push_cast; ring, hpe]
      have hs := hstep h hh0 hεh _ hκ0 hκ (e k) p (by simpa [he, hh] using hpn)
      rw [← hek1] at hs
      calc (1 + 2 * α * h) ^ (k + 1) * quadraticForm H (e 0) =
          (1 + 2 * α * h) * ((1 + 2 * α * h) ^ k * quadraticForm H (e 0)) := by ring
        _ ≤ (1 + 2 * α * h) * quadraticForm H (e k) :=
            mul_le_mul_of_nonneg_left ih (by positivity)
        _ ≤ quadraticForm H (e (k + 1)) := hs
  have he0 : e 0 = s • w := by simp [he, hx0]
  have hW0 : 0 < quadraticForm H (e 0) := by
    rw [he0, quadraticForm_smul]; positivity
  have hη : 0 < η := by
    have := hHup w
    by_contra hneg
    push Not at hneg
    nlinarith [sq_nonneg ‖w‖]
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (η * (r₁ / 2) ^ 2 / quadraticForm H (e 0))
    (by linarith [mul_pos (mul_pos two_pos hα) hh0] : (1 : ℝ) < 1 + 2 * α * h)
  have hupk : quadraticForm H (e k) ≤ η * (r₁ / 2) ^ 2 := by
    refine (hHup _).trans (mul_le_mul_of_nonneg_left ?_ hη.le)
    exact pow_le_pow_left₀ (norm_nonneg _) (hcon _ (by positivity)).le 2
  have := hgrow k
  rw [div_lt_iff₀ hW0] at hk
  linarith

/-- The arithmetic of the error bound from the Lyapunov bound. -/
@[tmio T, powerlib_foundation] private theorem norm_le_of_lyapunov_bound {nrm p₁ p₂ c D T ε CK C₂ :
    ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hc : 0 < c) (hD : 0 ≤ D) (hT : 0 < T) (hε : 0 < ε)
    (hCK : 0 ≤ CK) (hC₂ : 0 ≤ C₂) (hn : 0 ≤ nrm)
    (hV : p₁ * nrm ^ 2 ≤ ε ^ 2 * (p₂ * CK ^ 2 + D * C₂ ^ 2 / (c * T ^ 2))) :
    nrm ≤ (Real.sqrt (p₂ / p₁) + Real.sqrt (D / (c * p₁)) / T + 1) * (CK + C₂) * ε := by
  set a := Real.sqrt (p₂ / p₁) with ha
  set b := Real.sqrt (D / (c * p₁)) / T with hb
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := by positivity
  have ha2 : a ^ 2 = p₂ / p₁ := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = D / (c * p₁) / T ^ 2 := by
    rw [hb, div_pow, Real.sq_sqrt (by positivity)]
  have h1 : nrm ^ 2 ≤ (ε * (a * CK + b * C₂)) ^ 2 := by
    have h2 : nrm ^ 2 ≤ ε ^ 2 * (a ^ 2 * CK ^ 2 + b ^ 2 * C₂ ^ 2) := by
      rw [ha2, hb2]
      have e : ε ^ 2 * (p₂ / p₁ * CK ^ 2 + D / (c * p₁) / T ^ 2 * C₂ ^ 2) =
          ε ^ 2 * (p₂ * CK ^ 2 + D * C₂ ^ 2 / (c * T ^ 2)) / p₁ := by
        field_simp
      rw [e, le_div_iff₀ hp₁]; linarith
    refine h2.trans ?_
    have : 0 ≤ 2 * (a * CK) * (b * C₂) := by positivity
    nlinarith
  have h3 : nrm ≤ ε * (a * CK + b * C₂) :=
    (pow_le_pow_iff_left₀ hn (by positivity) two_ne_zero).mp h1
  refine h3.trans ?_
  have h4 : a * CK + b * C₂ ≤ (a + b + 1) * (CK + C₂) := by nlinarith
  nlinarith

/-- **First-order averaging is valid on `[0, ∞)` in the attraction case (Sanders–Verhulst).**
Let `f` be as in `exp_stable_of_hurwitz` with `Df̄(y*) = J` Hurwitz. There are `ε₀ > 0`, `δ₀ > 0`
and `κ₁ ≥ 1` such that for every `0 < ε ≤ ε₀`, every remainder `r` with the constants `ℓ_r`,
`M_r`, every slow time `L ≥ 0` with `κ₁ (C_K + C₂) ε ≤ δ₀`, where
`C_K = (2ℓMLT + 2MT + LM_r) e^{ℓL}` is the KBM constant of `Averaging.kbm_perturbed` and
`C₂ = C_S + ℓMT²`: if a solution `x̄` of the averaged equation `x̄̇ = ε f̄(x̄)` has entered the ball
`‖x̄ − y*‖ ≤ δ₀` by the time `L/ε` and stays there, then the solution `x` of
`ẋ = ε f(x, t) + ε² r(x, t)` with `x(0) = x̄(0)` satisfies, for ALL `t ≥ 0`,
`‖x(t) − x̄(t)‖ ≤ (κ₁ (C_K + C₂) + 2(M + M_r)T) ε` — the `O(ε)` error of KBM on `[0, L/ε]`
(`Averaging.kbm_perturbed`) does not grow afterwards, because the period map contracts the
Lyapunov function of `J` (`exists_lyapunov_euler`, `averaged_difference_step`). -/
@[tmio T, powerlib_foundation] theorem averaging_valid_forever [NeZero n] {f : ℝⁿ → ℝ → ℝⁿ}
    {T ℓ M ℓr Mr ρ L₂ : ℝ} {Df : ℝⁿ → ℝ → ℝⁿ →L[ℝ] ℝⁿ} {ystar : ℝⁿ}
    (hf : 0 < T ∧ 0 ≤ ℓ ∧ Continuous (Function.uncurry f) ∧ (∀ x t, f x (t + T) = f x t) ∧
      (∀ x y t, ‖f x t - f y t‖ ≤ ℓ * ‖x - y‖) ∧ ∀ x t, ‖f x t‖ ≤ M)
    (hρ : 0 < ρ) (hL₂ : 0 ≤ L₂)
    (hD : ∀ x, ‖x - ystar‖ ≤ ρ → ∀ t, HasFDerivAt (fun y => f y t) (Df x t) x)
    (hDl : ∀ x y, ‖x - ystar‖ ≤ ρ → ‖y - ystar‖ ≤ ρ → ∀ t, ‖Df x t - Df y t‖ ≤ L₂ * ‖x - y‖)
    (hDc : Continuous (Df ystar)) {J : Matrix (Fin n) (Fin n) ℝ}
    (hA : HasFDerivAt (fieldAverage f T) (op J) ystar) (hJ : LinearSystems.IsHurwitz J)
    (hMr : 0 ≤ Mr) :
    ∃ ε₀ δ₀ κ₁ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧ 1 ≤ κ₁ ∧
      ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ r : ℝⁿ → ℝ → ℝⁿ,
      (0 < T ∧ 0 ≤ ℓr ∧ Continuous (Function.uncurry r) ∧ (∀ x t, r x (t + T) = r x t) ∧
        (∀ x y t, ‖r x t - r y t‖ ≤ ℓr * ‖x - y‖) ∧ ∀ x t, ‖r x t‖ ≤ Mr) →
      ∀ L, 0 ≤ L →
      κ₁ * ((2 * ℓ * M * L * T + 2 * M * T + L * Mr) * Real.exp (ℓ * L) +
        (stroboConst ℓ M Mr T + ℓ * M * T ^ 2)) * ε ≤ δ₀ →
      ∀ x xbar : ℝ → ℝⁿ, (∀ t, HasDerivAt x (ε • f (x t) t + ε ^ 2 • r (x t) t) t) →
        (∀ t, HasDerivAt xbar (ε • fieldAverage f T (xbar t)) t) → x 0 = xbar 0 →
        (∀ t, L / ε ≤ t → ‖xbar t - ystar‖ ≤ δ₀) →
        ∀ t, 0 ≤ t → ‖x t - xbar t‖ ≤
          (κ₁ * ((2 * ℓ * M * L * T + 2 * M * T + L * Mr) * Real.exp (ℓ * L) +
            (stroboConst ℓ M Mr T + ℓ * M * T ^ 2)) + 2 * (M + Mr) * T) * ε := by
  obtain ⟨P, p₁, p₂, c, h₀, κ₀, D, hp₁, hp₂, hc, hh₀, hch₀, hκ₀, hD0, hbd, hstep⟩ :=
    exists_lyapunov_euler hJ
  have hT := hf.1
  have hℓ := hf.2.1
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf.2.2.2.2.2 ystar 0)
  set r₁ := min (ρ / 2) (κ₀ / (L₂ + 1)) with hr₁
  have hr₁0 : 0 < r₁ := lt_min (by positivity) (by positivity)
  have hr₁ρ : r₁ ≤ ρ / 2 := min_le_left _ _
  have hr₁κ : L₂ * r₁ ≤ κ₀ := by
    have h1 : r₁ ≤ κ₀ / (L₂ + 1) := min_le_right _ _
    calc L₂ * r₁ ≤ (L₂ + 1) * (κ₀ / (L₂ + 1)) :=
          mul_le_mul (by linarith) h1 hr₁0.le (by positivity)
      _ = κ₀ := by field_simp
  set κ₁ := Real.sqrt (p₂ / p₁) + Real.sqrt (D / (c * p₁)) / T + 1 with hκ₁
  have hκ₁ : 1 ≤ κ₁ := by
    have : 0 ≤ Real.sqrt (p₂ / p₁) + Real.sqrt (D / (c * p₁)) / T := by positivity
    linarith
  set ε₀ := min (min 1 (h₀ / T)) (ρ / (2 * ((M + Mr) * T + 1))) with hε₀
  refine ⟨ε₀, r₁ / 2, κ₁, by positivity, by positivity, hκ₁, ?_⟩
  intro ε hε hεε₀ r hr L hL hsmall x xbar hx hxbar h0 hin t ht
  have hε1 : ε ≤ 1 := hεε₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεh : ε * T ≤ h₀ := by
    have : ε ≤ h₀ / T := hεε₀.trans ((min_le_left _ _).trans (min_le_right _ _))
    rwa [le_div_iff₀ hT] at this
  have hεd : ε * (M + Mr) * T ≤ ρ / 2 := by
    have h1 : ε ≤ ρ / (2 * ((M + Mr) * T + 1)) := hεε₀.trans (min_le_right _ _)
    calc ε * (M + Mr) * T = ε * ((M + Mr) * T) := by ring
      _ ≤ ρ / (2 * ((M + Mr) * T + 1)) * ((M + Mr) * T + 1) :=
          mul_le_mul h1 (by linarith) (by positivity) (by positivity)
      _ = ρ / 2 := by field_simp
  set CK := (2 * ℓ * M * L * T + 2 * M * T + L * Mr) * Real.exp (ℓ * L) with hCK
  set C₂ := stroboConst ℓ M Mr T + ℓ * M * T ^ 2 with hC₂
  have hCK0 : 0 ≤ CK := by positivity
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂, stroboConst]; positivity
  set B := κ₁ * (CK + C₂) * ε with hB
  have hB0 : 0 ≤ B := by positivity
  have hBδ : B ≤ r₁ / 2 := by rw [hB]; linarith [hsmall]
  have hCKB : CK * ε ≤ B := by
    rw [hB]
    have : CK ≤ κ₁ * (CK + C₂) := by nlinarith
    exact mul_le_mul_of_nonneg_right this hε.le
  -- KBM on `[0, L/ε]`
  have hkbm : ∀ s ∈ Icc 0 (L / ε), ‖x s - xbar s‖ ≤ CK * ε := by
    intro s hs
    have h := kbm_perturbed hf hε hL (η := ε * Mr) (x := x) (xbar := xbar)
      (q := fun t => ε ^ 2 • r (x t) t) (fun t _ => (hx t).hasDerivWithinAt)
      (fun t _ => by
        rw [norm_smul, Real.norm_of_nonneg (by positivity), sq, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hr.2.2.2.2.2 _ _) hε.le)
          hε.le) hxbar h0 s hs
    calc ‖x s - xbar s‖ ≤ ((2 * ℓ * M * L * T + 2 * M * T) * ε + L * (ε * Mr)) *
          Real.exp (ℓ * L) := h
      _ = CK * ε := by rw [hCK]; ring
  -- the sampled deviation after `L/ε`
  set t₁ := L / ε with ht₁
  have ht₁0 : 0 ≤ t₁ := div_nonneg hL hε.le
  set h := ε * T with hh
  have hh0 : 0 < h := mul_pos hε hT
  have hch : c * h ≤ 1 := (mul_le_mul_of_nonneg_left hεh hc.le).trans hch₀
  set Λ := ε ^ 2 * (p₂ * CK ^ 2 + D * C₂ ^ 2 / (c * T ^ 2)) with hΛ
  set e : ℕ → ℝⁿ := fun k => x (t₁ + k * T) - xbar (t₁ + k * T) with he
  have hbarr : ∀ k : ℕ, ‖xbar (t₁ + k * T) - ystar‖ ≤ r₁ / 2 := fun k =>
    hin _ (by have : (0 : ℝ) ≤ k * T := by positivity
              linarith)
  have hind : ∀ k : ℕ, quadraticForm P (e k) ≤ Λ := by
    intro k
    induction k with
    | zero =>
      have h1 : ‖e 0‖ ≤ CK * ε := by
        simp only [he, Nat.cast_zero, zero_mul, add_zero]
        exact hkbm t₁ ⟨ht₁0, le_rfl⟩
      calc quadraticForm P (e 0) ≤ p₂ * ‖e 0‖ ^ 2 := (hbd _).2
        _ ≤ p₂ * (CK * ε) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2) hp₂.le
        _ ≤ Λ := by
            rw [hΛ]
            have : 0 ≤ D * C₂ ^ 2 / (c * T ^ 2) := by positivity
            rw [show p₂ * (CK * ε) ^ 2 = ε ^ 2 * (p₂ * CK ^ 2) by ring]
            exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    | succ k ih =>
      have hek : ‖e k‖ ≤ B := norm_le_of_lyapunov_bound hp₁ hp₂ hc hD0 hT hε hCK0 hC₂0
        (norm_nonneg _) ((hbd _).1.trans ih)
      have hxk : ‖x (t₁ + k * T) - ystar‖ ≤ r₁ := by
        calc ‖x (t₁ + k * T) - ystar‖ = ‖e k + (xbar (t₁ + k * T) - ystar)‖ := by
              simp only [he]; congr 1; abel
          _ ≤ B + r₁ / 2 := (norm_add_le _ _).trans (add_le_add hek (hbarr k))
          _ ≤ r₁ := by linarith
      obtain ⟨p, hpe, hpn⟩ := averaged_difference_step hf hr.2.2.1 hr.2.2.2.2.2 hρ hL₂ hD hDl hDc
        hA hε hε1 hx hxbar hxk ((hbarr k).trans (by linarith)) (by linarith)
      have hek1 : e (k + 1) = e k + h • (op J) (e k) + p := by
        simp only [he]
        rw [show t₁ + ((k + 1 : ℕ) : ℝ) * T = t₁ + k * T + T by push_cast; ring, hpe]
      have hs := hstep h hh0 hεh (L₂ * r₁) (ε ^ 2 * C₂) (by positivity) hr₁κ (by positivity)
        (e k) p (by simpa [he, hh, hC₂] using hpn)
      rw [← hek1] at hs
      refine hs.trans ?_
      have hkey : D * (ε ^ 2 * C₂) ^ 2 / h ≤ c * h * Λ := by
        rw [hh, hΛ, div_le_iff₀ hh0]
        have : 0 ≤ c * (ε * T) * (ε ^ 2 * (p₂ * CK ^ 2)) * (ε * T) := by positivity
        have e2 : c * (ε * T) * (ε ^ 2 * (p₂ * CK ^ 2 + D * C₂ ^ 2 / (c * T ^ 2))) * (ε * T) =
            c * (ε * T) * (ε ^ 2 * (p₂ * CK ^ 2)) * (ε * T) + D * (ε ^ 2 * C₂) ^ 2 := by
          field_simp
        linarith
      have := mul_le_mul_of_nonneg_left ih (by linarith : 0 ≤ 1 - c * h)
      linarith
  -- every time `t ≥ 0`
  rcases le_or_gt t t₁ with htt | htt
  · refine (hkbm t ⟨ht, htt⟩).trans ?_
    have : 0 ≤ 2 * (M + Mr) * T * ε := by positivity
    have e : (κ₁ * (CK + C₂) + 2 * (M + Mr) * T) * ε = B + 2 * (M + Mr) * T * ε := by
      rw [hB]; ring
    rw [e]; linarith
  set k := ⌊(t - t₁) / T⌋₊ with hk
  have hkT : (k : ℝ) * T ≤ t - t₁ := by
    have := Nat.floor_le (div_nonneg (sub_nonneg.mpr htt.le) hT.le)
    calc (k : ℝ) * T ≤ (t - t₁) / T * T := mul_le_mul_of_nonneg_right this hT.le
      _ = t - t₁ := by field_simp
  have hkT' : t - t₁ - k * T ≤ T := by
    have := Nat.lt_floor_add_one ((t - t₁) / T)
    have : t - t₁ < ((k : ℝ) + 1) * T := by
      calc t - t₁ = (t - t₁) / T * T := by field_simp
        _ < ((k : ℝ) + 1) * T := mul_lt_mul_of_pos_right this hT
    linarith
  have hek : ‖e k‖ ≤ B := norm_le_of_lyapunov_bound hp₁ hp₂ hc hD0 hT hε hCK0 hC₂0
    (norm_nonneg _) ((hbd _).1.trans (hind k))
  have hdx := solution_drift_le hf.2.2.2.2.2 hr.2.2.2.2.2 hε.le hε1 hx
    (a := t₁ + k * T) (b := t) (by linarith)
  have hdxb := averaged_drift hf hε.le hxbar (r := t₁ + k * T) (s := t) (by linarith)
  have e1 : x t - xbar t = e k + (x t - x (t₁ + k * T)) - (xbar t - xbar (t₁ + k * T)) := by
    simp only [he]; abel
  rw [e1]
  have hMMr : ε * M * (t - (t₁ + k * T)) ≤ ε * (M + Mr) * T := by
    have h1 : t - (t₁ + k * T) ≤ T := by linarith
    calc ε * M * (t - (t₁ + k * T)) ≤ ε * M * T := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ ε * (M + Mr) * T := by
          have : ε * M ≤ ε * (M + Mr) := mul_le_mul_of_nonneg_left (by linarith) hε.le
          exact mul_le_mul_of_nonneg_right this hT.le
  have hMMr' : ε * (M + Mr) * (t - (t₁ + k * T)) ≤ ε * (M + Mr) * T := by
    have : t - (t₁ + k * T) ≤ T := by linarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  calc ‖e k + (x t - x (t₁ + k * T)) - (xbar t - xbar (t₁ + k * T))‖
      ≤ ‖e k‖ + ‖x t - x (t₁ + k * T)‖ + ‖xbar t - xbar (t₁ + k * T)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ B + ε * (M + Mr) * T + ε * (M + Mr) * T := by linarith
    _ = _ := by rw [hB]; ring

end StabilityRn

end powerlib.Averaging
