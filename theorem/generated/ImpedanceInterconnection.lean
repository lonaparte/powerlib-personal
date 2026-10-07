-- Generated from the Agda-normalized executable conversion.
-- Agda source SHA-256: f72f18e8490867016a395a48dbd8c4967435c3bdbb12375d29b70d4d2a4a6502
-- Wire 20261006 v1: [0, 0, 1, 0, 1, 0, 6, 2, 1, 0, 5, 0, 2, 3, 0, 4, 1, 1, 0, 5, 0, 3, 0, 6]
import dependencies.Mathlib
import theorem.Attributes

namespace powerlib.generated

def closedLoopBlocks {ι₁ ι₂ κ : Type*} [Fintype κ]
    (A₁ : Matrix ι₁ ι₁ ℝ) (B₁ : Matrix ι₁ κ ℝ) (C₁ : Matrix κ ι₁ ℝ) (D₁ : Matrix κ κ ℝ)
    (A₂ : Matrix ι₂ ι₂ ℝ) (B₂ : Matrix ι₂ κ ℝ) (C₂ : Matrix κ ι₂ ℝ) :
    Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℝ :=
  Matrix.fromBlocks A₁ (B₁ * C₂)
    (-(B₂ * C₁)) (A₂ - ((B₂ * D₁) * C₂))

@[simp, powerlib_foundation] theorem closedLoopBlocks_spec {ι₁ ι₂ κ : Type*} [Fintype κ]
    (A₁ : Matrix ι₁ ι₁ ℝ) (B₁ : Matrix ι₁ κ ℝ) (C₁ : Matrix κ ι₁ ℝ) (D₁ : Matrix κ κ ℝ)
    (A₂ : Matrix ι₂ ι₂ ℝ) (B₂ : Matrix ι₂ κ ℝ) (C₂ : Matrix κ ι₂ ℝ) :
    closedLoopBlocks A₁ B₁ C₁ D₁ A₂ B₂ C₂ =
      Matrix.fromBlocks A₁ (B₁ * C₂) (-(B₂ * C₁)) (A₂ - B₂ * D₁ * C₂) := rfl

end powerlib.generated
