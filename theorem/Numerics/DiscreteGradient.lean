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
-/

noncomputable section
namespace powerlib.Numerics
open Matrix
open powerlib.PH (dotProduct_mulVec_self_eq_zero_of_skew)

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
  rw [G.mean_value, hstep, dotProduct_smul, sub_mulVec, dotProduct_add, dotProduct_sub,
    dotProduct_mulVec_self_eq_zero_of_skew hJ, dotProduct_mulVec (G.dg x y) g,
    ← mulVec_transpose, dotProduct_comm (gᵀ *ᵥ G.dg x y), smul_eq_mul]
  ring

/-- Exact energy conservation of the discrete gradient method for lossless unforced pH
systems (`R = 0`, `u = 0`). -/
@[powerlib_foundation] theorem discreteGradient_conserves {H : (Fin n → ℝ) → ℝ}
    (G : DiscreteGradient H) {J : Matrix (Fin n) (Fin n) ℝ} (hJ : Jᵀ = -J) (h : ℝ)
    {x y : Fin n → ℝ} (hstep : y - x = h • (J *ᵥ G.dg x y)) : H y = H x := by
  have := discreteGradient_energy_step G (R := 0) (0 : Matrix (Fin n) (Fin 0) ℝ) hJ h 0
    (x := x) (y := y) (by simpa using hstep)
  simp at this
  linarith

/-- Discrete dissipation inequality: with `h ≥ 0` and `R ⪰ 0`,
`H(x⁺) − H(x) ≤ h uᵀ gᵀ ∇̄H`. -/
@[powerlib_foundation] theorem discreteGradient_dissipation {H : (Fin n → ℝ) → ℝ}
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

end powerlib.Numerics
