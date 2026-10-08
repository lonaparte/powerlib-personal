import theorem.Hurwitz
import theorem.StateSpacePassivity

noncomputable section
namespace powerlib.Realization
open Matrix
open powerlib.LTI (characteristicMatrix)

abbrev PortModel := StateSpacePassivity.Model

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

abbrev complexify {m n : Type*} (M : Matrix m n ℝ) : Matrix m n ℂ := M.map (algebraMap ℝ ℂ)

def transfer (m : PortModel ι κ) (s : ℂ) : Matrix κ κ ℂ :=
  complexify m.C * (characteristicMatrix m.A s)⁻¹ * complexify m.B + complexify m.D

@[powerlib_foundation] theorem complexify_mul {m n p : Type*} [Fintype n]
    (M : Matrix m n ℝ) (N : Matrix n p ℝ) : complexify (M * N) = complexify M * complexify N :=
  Matrix.map_mul

@[powerlib_foundation] theorem complexify_neg {m n : Type*} (M : Matrix m n ℝ) :
    complexify (-M) = -complexify M :=
  Matrix.map_neg _ (fun a => map_neg _ a) M

@[powerlib_foundation] theorem complexify_sub {m n : Type*} (M N : Matrix m n ℝ) :
    complexify (M - N) = complexify M - complexify N :=
  Matrix.map_sub _ (fun a b => map_sub _ a b) M N

@[powerlib_foundation] theorem complexify_zero {m n : Type*} :
    complexify (0 : Matrix m n ℝ) = 0 :=
  Matrix.map_zero _ (map_zero _)

@[powerlib_foundation] theorem complexify_fromRows {m₁ m₂ n : Type*}
    (A₁ : Matrix m₁ n ℝ) (A₂ : Matrix m₂ n ℝ) :
    complexify (fromRows A₁ A₂) = fromRows (complexify A₁) (complexify A₂) :=
  fromRows_map _ _ _

@[powerlib_foundation] theorem complexify_fromCols {m n₁ n₂ : Type*}
    (A₁ : Matrix m n₁ ℝ) (A₂ : Matrix m n₂ ℝ) :
    complexify (fromCols A₁ A₂) = fromCols (complexify A₁) (complexify A₂) :=
  fromCols_map _ _ _

@[powerlib_foundation] theorem complexify_fromBlocks {l m n o : Type*}
    (A : Matrix n l ℝ) (B : Matrix n m ℝ) (C : Matrix o l ℝ) (D : Matrix o m ℝ) :
    complexify (fromBlocks A B C D) =
      fromBlocks (complexify A) (complexify B) (complexify C) (complexify D) :=
  Matrix.fromBlocks_map _ _ _ _ _

@[powerlib_foundation] theorem transfer_eq_adjugate (m : PortModel ι κ) (s : ℂ) :
    transfer m s = ((characteristicMatrix m.A s).det)⁻¹ •
      (complexify m.C * (characteristicMatrix m.A s).adjugate * complexify m.B) +
      complexify m.D := by
  rw [transfer, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.mul_smul, Matrix.smul_mul]

end powerlib.Realization
