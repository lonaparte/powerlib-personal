-- Generated from the Agda-normalized executable conversion.
-- Agda source SHA-256: 6a28dab84351bde71a4d784ea16265f35dd2e4ce89199157e7b5cac2bf5dce1d
-- Wire 20261006 v2: [0, 0, 1, 0, 1, 0, 6, 2, 1, 0, 5, 0, 2, 3, 0, 4, 1, 1, 0, 5, 0, 3, 0, 6, 2, 0, 1, 1, 0, 5, 0, 3, 2, 0, 2, 2, 1, 0, 3, 0, 6, 0, 3]
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

def closedLoopInput {ι₁ ι₂ κ : Type*} [Fintype κ]
    (B₁ : Matrix ι₁ κ ℝ) (D₁ : Matrix κ κ ℝ) (B₂ : Matrix ι₂ κ ℝ) :
    Matrix (ι₁ ⊕ ι₂) κ ℝ :=
  Matrix.fromRows (-B₁) (B₂ * D₁)

@[simp, powerlib_foundation] theorem closedLoopInput_spec {ι₁ ι₂ κ : Type*} [Fintype κ]
    (B₁ : Matrix ι₁ κ ℝ) (D₁ : Matrix κ κ ℝ) (B₂ : Matrix ι₂ κ ℝ) :
    closedLoopInput B₁ D₁ B₂ =
      Matrix.fromRows (-B₁) (B₂ * D₁) := rfl

def closedLoopOutput {ι₁ ι₂ κ : Type*} [Fintype κ]
    (C₁ : Matrix κ ι₁ ℝ) (D₁ : Matrix κ κ ℝ) (C₂ : Matrix κ ι₂ ℝ) :
    Matrix κ (ι₁ ⊕ ι₂) ℝ :=
  Matrix.fromCols (-C₁) (-(D₁ * C₂))

@[simp, powerlib_foundation] theorem closedLoopOutput_spec {ι₁ ι₂ κ : Type*} [Fintype κ]
    (C₁ : Matrix κ ι₁ ℝ) (D₁ : Matrix κ κ ℝ) (C₂ : Matrix κ ι₂ ℝ) :
    closedLoopOutput C₁ D₁ C₂ =
      Matrix.fromCols (-C₁) (-(D₁ * C₂)) := rfl

def closedLoopFeedthrough {κ : Type*}
    (D₁ : Matrix κ κ ℝ) :
    Matrix κ κ ℝ :=
  D₁

@[simp, powerlib_foundation] theorem closedLoopFeedthrough_spec {κ : Type*}
    (D₁ : Matrix κ κ ℝ) :
    closedLoopFeedthrough D₁ =
      D₁ := rfl

end powerlib.generated
