import theorem.PH.Nonlinear

/-! # Discrete gradient method for port-Hamiltonian energies

A discrete-gradient step reproduces the port-Hamiltonian energy balance exactly: conservation
without dissipation and inputs, and a discrete dissipation inequality otherwise.

Scope.
* Statements about arbitrary matrices and energies; the continuous-time port-Hamiltonian
  framework is `theorem/PH/Nonlinear.lean`.

Source: work-sync theory/T-ph.md §2.5.

Results.
* `DiscreteGradient` — a discrete gradient of `H : (Fin n → ℝ) → ℝ` is a map `∇̄H(x, y)` with
  `H y − H x = ∇̄H(x, y) · (y − x)`.
* `discreteGradient_energy_step` — any discrete gradient makes the implicit step
  `x⁺ − x = h((J − R) ∇̄H + g u)` (`J` skew) satisfy
  `H(x⁺) − H(x) = h(uᵀ gᵀ∇̄H − ∇̄Hᵀ R ∇̄H)`; in particular `H` is conserved **exactly** when
  `R = 0, u = 0` (`discreteGradient_conserves`), and with `h ≥ 0`, `R ⪰ 0` the discrete
  dissipation inequality holds (`discreteGradient_dissipation`).
* `midpointDiscreteGradient` — the midpoint (average-vector-field) discrete gradient of a
  quadratic `H = ½ xᵀ Q x`, `Q` symmetric, is `Q (x + y) / 2`.
* `separableDiscreteGradient` — the discrete gradient of a planar separable energy
  `H(x) = U(x₀) + (k/2) x₁²`: the slope of `U` (a supplied `U'` on the diagonal) and the mean
  `k (x₁ + y₁)/2`, for any `U`; consistent on the diagonal
  (`separableDiscreteGradient_dg_self`).
-/

noncomputable section
namespace powerlib.Numerics
open Matrix
open powerlib.PH (dotProduct_phField)

variable {n m : ℕ}

/-- A discrete gradient of `H : (Fin n → ℝ) → ℝ`: `H y − H x = ∇̄H(x, y) · (y − x)`. -/
structure DiscreteGradient (H : (Fin n → ℝ) → ℝ) where
  dg : (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ)
  mean_value : ∀ x y, H y - H x = dg x y ⬝ᵥ (y - x)

/-- One implicit discrete-gradient step `x⁺ − x = h((J − R)∇̄H + g u)` changes the energy by
exactly `h (uᵀ gᵀ ∇̄H − ∇̄Hᵀ R ∇̄H)`. -/
@[tmio T, powerlib_foundation] theorem discreteGradient_energy_step {H : (Fin n → ℝ) → ℝ}
    (G : DiscreteGradient H) {J R : Matrix (Fin n) (Fin n) ℝ} (g : Matrix (Fin n) (Fin m) ℝ)
    (hJ : Jᵀ = -J) (h : ℝ) (u : Fin m → ℝ) {x y : Fin n → ℝ}
    (hstep : y - x = h • ((J - R) *ᵥ G.dg x y + g *ᵥ u)) :
    H y - H x = h * (u ⬝ᵥ (gᵀ *ᵥ G.dg x y) - G.dg x y ⬝ᵥ (R *ᵥ G.dg x y)) := by
  rw [G.mean_value, hstep, dotProduct_smul, dotProduct_phField hJ, smul_eq_mul]

/-- Exact energy conservation of the discrete gradient method for lossless unforced pH
systems (`R = 0`, `u = 0`). -/
@[tmio T, powerlib_foundation] theorem discreteGradient_conserves {H : (Fin n → ℝ) → ℝ}
    (G : DiscreteGradient H) {J : Matrix (Fin n) (Fin n) ℝ} (hJ : Jᵀ = -J) (h : ℝ)
    {x y : Fin n → ℝ} (hstep : y - x = h • (J *ᵥ G.dg x y)) : H y = H x := by
  have := discreteGradient_energy_step G (R := 0) (0 : Matrix (Fin n) (Fin 0) ℝ) hJ h 0
    (x := x) (y := y) (by simpa using hstep)
  simp at this
  linarith

/-- Discrete dissipation inequality: with `h ≥ 0` and `R ⪰ 0`,
`H(x⁺) − H(x) ≤ h uᵀ gᵀ ∇̄H`. -/
@[tmio T, powerlib_foundation] theorem discreteGradient_dissipation {H : (Fin n → ℝ) → ℝ}
    (G : DiscreteGradient H) {J R : Matrix (Fin n) (Fin n) ℝ} (g : Matrix (Fin n) (Fin m) ℝ)
    (hJ : Jᵀ = -J) (hR : R.PosSemidef) {h : ℝ} (hh : 0 ≤ h) (u : Fin m → ℝ) {x y : Fin n → ℝ}
    (hstep : y - x = h • ((J - R) *ᵥ G.dg x y + g *ᵥ u)) :
    H y - H x ≤ h * (u ⬝ᵥ (gᵀ *ᵥ G.dg x y)) := by
  rw [discreteGradient_energy_step G g hJ h u hstep]
  have hd := hR.dotProduct_mulVec_nonneg (G.dg x y)
  rw [star_trivial] at hd
  nlinarith

/-- The midpoint (average-vector-field) discrete gradient of `H(x) = ½ xᵀ Q x`, `Q` symmetric:
`∇̄H(x, y) = Q (x + y) / 2`. -/
def midpointDiscreteGradient {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Qᵀ = Q) :
    DiscreteGradient (fun x : Fin n → ℝ => (1 / 2 : ℝ) * (x ⬝ᵥ (Q *ᵥ x))) where
  dg x y := (1 / 2 : ℝ) • (Q *ᵥ (x + y))
  mean_value x y := by
    have hsym : x ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ (Q *ᵥ x) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hQ, dotProduct_comm]
    simp only [smul_dotProduct, mulVec_add, add_dotProduct, dotProduct_sub, smul_eq_mul]
    rw [dotProduct_comm (Q *ᵥ x) y, dotProduct_comm (Q *ᵥ x) x, dotProduct_comm (Q *ᵥ y) y,
      dotProduct_comm (Q *ᵥ y) x, hsym]
    ring

/-- The separable discrete gradient of `H(x) = U(x₀) + (k/2) x₁²` on the plane: the slope of `U`
between the two first coordinates (the supplied derivative `U'` when they agree) and the mean
`k (x₁ + y₁)/2` of the gradients of the quadratic part. No smoothness of `U` is needed for the
mean-value identity; with `U'` the derivative of `U` it is consistent
(`separableDiscreteGradient_dg_self`). -/
def separableDiscreteGradient (U U' : ℝ → ℝ) (k : ℝ) :
    DiscreteGradient (fun x : Fin 2 → ℝ => U (x 0) + k / 2 * x 1 ^ 2) where
  dg x y := ![if x 0 = y 0 then U' (x 0) else slope U (x 0) (y 0), k * (x 1 + y 1) / 2]
  mean_value x y := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.sub_apply]
    split_ifs with hxy
    · rw [hxy]
      ring
    · have h := sub_smul_slope U (x 0) (y 0)
      rw [smul_eq_mul, vsub_eq_sub] at h
      linear_combination -h

/-- On the diagonal the separable discrete gradient is `(U'(x₀), k x₁)`, the gradient of `H` when
`U'` is the derivative of `U`. -/
@[tmio T, powerlib_foundation] theorem separableDiscreteGradient_dg_self (U U' : ℝ → ℝ) (k : ℝ)
    (x : Fin 2 → ℝ) : (separableDiscreteGradient U U' k).dg x x = ![U' (x 0), k * x 1] := by
  simp only [separableDiscreteGradient, ite_true]
  congr 2
  ring

end powerlib.Numerics
