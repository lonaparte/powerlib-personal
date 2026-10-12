import theorem.DAE.Linear

/-! # Linear SDAE with additive noise: Schur-complement reduction keeps the diffusion

Foundation layer (category B).

System (pathwise integral form, `q` noise channels, additive noise only in the differential
equations — the standing assumption of the source note):
```
X(t) = X(0) + ∫₀ᵗ (Axx X + Axy Y + Bx u) ds + G (W(t) - W(0)),
0    = Ayx X(t) + Ayy Y(t) + By u(t)          for all t.
```
`W` is an arbitrary driving path (e.g. a Brownian sample path; for additive constant `G` the
Itô integral `∫₀ᵗ G dW` equals `G (W(t) - W(0))` pathwise, so no stochastic calculus is
needed). The drift integrals are interval integrals of `Fin n → ℝ`-valued functions.

Result (index 1, `Ayy` invertible): `(X, Y)` is a path of the SDAE iff
`X(t) = X(0) + ∫₀ᵗ (A_red X + B_red u) ds + G (W(t) - W(0))` and
`Y(t) = -Ayy⁻¹ (Ayx X(t) + By u(t))`: the drift is reduced by the Schur complement
(`LinearDAE.schurA`, `LinearDAE.schurB`) and the diffusion is unchanged, `G_red = G`.

Model boundary: linear, additive noise entering only the differential equations, noise not
in the algebraic constraint, index 1. State-dependent diffusion or noisy constraints (the
exceptions listed in the note) are not covered; covariance (Lyapunov) results are elsewhere.

Source: work-sync theory/T-sdae-systems.md §1.0–§1.1 (Schur complement `A_red` and
`G_red = G`).
-/

noncomputable section
namespace powerlib.DAE
open Matrix

variable {n m p q : ℕ}

namespace LinearDAE

variable (d : LinearDAE n m p)

/-- Pathwise integral form of the linear SDAE with additive noise `G dW`. -/
def IsSDAEPath (G : Matrix (Fin n) (Fin q) ℝ) (u : ℝ → Fin p → ℝ) (W : ℝ → Fin q → ℝ)
    (X : ℝ → Fin n → ℝ) (Y : ℝ → Fin m → ℝ) : Prop :=
  (∀ t, X t = X 0 + (∫ s in (0 : ℝ)..t, (d.Axx *ᵥ X s + d.Axy *ᵥ Y s + d.Bx *ᵥ u s)) +
    G *ᵥ (W t - W 0)) ∧
  ∀ t, d.Ayx *ᵥ X t + d.Ayy *ᵥ Y t + d.By *ᵥ u t = 0

/-- Index-1 reduction of the SDAE: Schur-complement drift, unchanged diffusion `G`. -/
@[powerlib_foundation] theorem isSDAEPath_iff (hA : IsUnit d.Ayy.det)
    (G : Matrix (Fin n) (Fin q) ℝ) (u : ℝ → Fin p → ℝ) (W : ℝ → Fin q → ℝ)
    (X : ℝ → Fin n → ℝ) (Y : ℝ → Fin m → ℝ) :
    d.IsSDAEPath G u W X Y ↔
      (∀ t, X t = X 0 + (∫ s in (0 : ℝ)..t, (d.schurA *ᵥ X s + d.schurB *ᵥ u s)) +
        G *ᵥ (W t - W 0)) ∧
      ∀ t, Y t = d.algebraic (X t) (u t) := by
  have key : ∀ (Y : ℝ → Fin m → ℝ), (∀ t, Y t = d.algebraic (X t) (u t)) →
      (fun s => d.Axx *ᵥ X s + d.Axy *ᵥ Y s + d.Bx *ᵥ u s) =
        fun s => d.schurA *ᵥ X s + d.schurB *ᵥ u s := by
    intro Y hY
    funext s
    rw [hY s, field_on_constraint]
  constructor
  · rintro ⟨hX, hc⟩
    have hY : ∀ t, Y t = d.algebraic (X t) (u t) := fun t => (d.constraint_iff hA _ _ _).mp (hc t)
    refine ⟨fun t => ?_, hY⟩
    rw [hX t, key Y hY]
  · rintro ⟨hX, hY⟩
    refine ⟨fun t => ?_, fun t => (d.constraint_iff hA _ _ _).mpr (hY t)⟩
    rw [key Y hY]
    exact hX t

end LinearDAE

end powerlib.DAE
