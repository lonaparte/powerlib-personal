import theorem.GridTiedConverter.GFM.HopfLineLPFAngleKey
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

/-! # The rotated pattern of the VSM with a power filter on a dynamic line

Model boundary.
* Static algebra of patterns, no model and no behaviour: the Jacobian, the second and the third
  derivative of the five-state VSM with a power filter on a dynamic R–L line (`Line.VSMLPF`) at
  its operating point, in the coordinates `(δ, ω, P_f/M, (L/E) e^{−jδ*} i)` (the frame rotated
  with the operating angle `δ*`), as matrices and multilinear maps in complex atoms `c = ω_c`,
  `d = D/M`, `K = Q/M`, `g = E²/(M L)`, `N = P_ref/M`, `σ = R/L`, `w = ω₀` (the reading of a
  model in this frame is in `theorem/GridTiedConverter/GFM/HopfLineLPFAngle.lean`), a frequency
  `O` and a square root `j` of `−1`; the critical eigenvectors, the solutions of the two linear
  systems of the projection
  formula, and the reduction of the four pairings modulo the two Hopf relations at `O` (`σ > 0`)
  and on the lossless line (`σ = 0`, `c d = O²`).

Source: Kuznetsov, *Elements of Applied Bifurcation Theory* (3rd ed.), §3.5 and §5.4; the
eigenvectors are the adjugate rows/columns of `λ − J`, the solutions follow the sparsity of
`J`; the reductions were found with exact polynomial arithmetic (python-flint, untrusted) and
every identity is proved here by `ring` / `linear_combination` with its certificate.

Results.
* The pattern `AnglePattern.jac`, `AnglePattern.bilin`, `AnglePattern.trilin`; the critical
  vectors `Line.VSMLPF.angleVecQ`, `Line.VSMLPF.angleVecP`; `AnglePattern.right`,
  `AnglePattern.left` (eigenvector relations under the Hopf relations, every `σ`).
* The linear systems: `AnglePattern.solveJ` (`AnglePattern.jac_solveJ`), `AnglePattern.solveShift`,
  `AnglePattern.shiftDet` (`AnglePattern.shift_solveShift`); no relation is used.
* The reductions (`σ > 0`): `AnglePattern.trilin_pairing`, `AnglePattern.bilin_pairing`,
  `AnglePattern.shift_pairing`, `AnglePattern.pairing_eq`, `AnglePattern.shiftDet_eq`,
  `AnglePattern.det_eq`; lossless: `AnglePattern.loss_trilin_pairing`,
  `AnglePattern.loss_bilin_pairing`, `AnglePattern.loss_shift_pairing`,
  `AnglePattern.loss_pairing_eq`, `AnglePattern.loss_shiftDet_eq`, `AnglePattern.loss_det_eq`.
-/

noncomputable section
namespace powerlib.GFM.Line
namespace VSMLPF
open Complex Matrix

/-! ## The pattern of the rotated frame

Polynomial vectors in complex atoms and a square root `j` of `−1`: the Jacobian, the second and
the third derivative of the model at its operating point, in the coordinates
`(δ, ω, P_f/M, (L/E) e^{−jδ*} i)` (`d = D/M`, `c = ω_c`, `K = Q/M`, `g = E²/(M L)`,
`N = P_ref/M`, `σ = R/L`, `w = ω₀`), under the two Hopf relations at the frequency `O`. -/

/-- The Jacobian pattern in the rotated frame. -/
def AnglePattern.jac (c d K g σ w : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0, 1, 0, 0, 0; 0, -d, -1, 0, 0; -(c * K), 0, -c, c * g, 0; 0, 0, 0, -σ, w; 1, 0, 0, -w, -σ]

/-- The second-derivative pattern in the rotated frame. -/
def AnglePattern.bilin (c g N : ℂ) (u v : Fin 5 → ℂ) : Fin 5 → ℂ :=
  ![0, 0, c * (g * (u 0 * v 4 + u 4 * v 0) - N * (u 0 * v 0)), -(u 0 * v 0), 0]

/-- The third-derivative pattern in the rotated frame. -/
def AnglePattern.trilin (c g K : ℂ) (u v z : Fin 5 → ℂ) : Fin 5 → ℂ :=
  ![0, 0, c * (K * (u 0 * v 0 * z 0) - g * (u 0 * v 0 * z 3 + u 0 * v 3 * z 0 +
    u 3 * v 0 * z 0)), 0, -(u 0 * v 0 * z 0)]

/-- **The critical right eigenvector of the rotated pattern** at the frequency `O` (`j² = −1`,
`d = D/M`, `σ = R/L`, `w = ω₀`): `q = (L, λL, −(λ + d) λ L, w, σ + λ)`, `λ = jO`,
`L = (σ + λ)² + w²`. -/
def angleVecQ (d σ w O j : ℂ) : Fin 5 → ℂ :=
  ![(σ + O * j) ^ 2 + w ^ 2, O * j * ((σ + O * j) ^ 2 + w ^ 2),
    -((O * j + d) * (O * j) * ((σ + O * j) ^ 2 + w ^ 2)), w, σ + O * j]

/-- **The unnormalised critical left eigenvector of the rotated pattern** (`μ = −jO`,
`c = ω_c`, `g = E²/(M L)`): `p̃ = (−(c + μ)(d + μ) L_μ, −(c + μ) L_μ, L_μ, c g (σ + μ), c g w)`,
`L_μ = (σ + μ)² + w²`. -/
def angleVecP (c d g σ w O j : ℂ) : Fin 5 → ℂ :=
  ![-((c - O * j) * (d - O * j) * ((σ - O * j) ^ 2 + w ^ 2)),
    -((c - O * j) * ((σ - O * j) ^ 2 + w ^ 2)), (σ - O * j) ^ 2 + w ^ 2, c * g * (σ - O * j),
    c * g * w]

/-- `c (g w − K ρ)` times the solution of `J r = b` for a right-hand side `b = B(u, v)`. -/
def AnglePattern.solveJ (c K g σ w : ℂ) (b : Fin 5 → ℂ) : Fin 5 → ℂ :=
  ![(σ ^ 2 + w ^ 2) * b 2 + σ * c * g * b 3, 0, 0, w * b 2 + c * K * σ * b 3,
    σ * b 2 + c * (g - K * w) * b 3]

/-- `χ(2jO) = det(2jO − J)` of the pattern. -/
def AnglePattern.shiftDet (c d K g σ w O j : ℂ) : ℂ :=
  2 * O * j * (2 * O * j + d) * (2 * O * j + c) * ((2 * O * j + σ) ^ 2 + w ^ 2) -
    c * K * ((2 * O * j + σ) ^ 2 + w ^ 2) + c * g * w

/-- `χ(2jO)` times the solution of `(2jO − J) s = b` for a right-hand side `b = B(u, v)`. -/
def AnglePattern.solveShift (c d K g σ w O j : ℂ) (b : Fin 5 → ℂ) : Fin 5 → ℂ :=
  ![-(((2 * O * j + σ) ^ 2 + w ^ 2) * b 2 + c * g * (2 * O * j + σ) * b 3),
    -(2 * O * j * (((2 * O * j + σ) ^ 2 + w ^ 2) * b 2 + c * g * (2 * O * j + σ) * b 3)),
    (2 * O * j + d) * (2 * O * j) * (((2 * O * j + σ) ^ 2 + w ^ 2) * b 2 +
      c * g * (2 * O * j + σ) * b 3),
    (2 * O * j * (2 * O * j + c) * (2 * O * j + d) - c * K) * (2 * O * j + σ) * b 3 - w * b 2,
    -((2 * O * j + σ) * b 2) - ((2 * O * j * (2 * O * j + c) * (2 * O * j + d) - c * K) * w +
      c * g) * b 3]

/-- **The right critical eigenvector of the rotated pattern** under the two Hopf relations. Static
    algebra. -/
@[tmio M, powerlib_domain] theorem AnglePattern.right {c d K g σ w O j : ℂ}
    (hj : j ^ 2 = -1)
    (hK : 2 * σ * c * K = (d * c - O ^ 2) * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * (d + c) * O ^ 2)
    (hR : c * g * w = c * K * (σ ^ 2 + w ^ 2 - O ^ 2) +
      O ^ 2 * ((d + c) * (σ ^ 2 + w ^ 2 - O ^ 2) + 2 * σ * (d * c - O ^ 2))) :
    (AnglePattern.jac c d K g σ w) *ᵥ angleVecQ d σ w O j = (O * j) • angleVecQ d σ w O j := by
  ext k
  fin_cases k <;> simp only [AnglePattern.jac, angleVecQ, Matrix.mulVec, dotProduct,
      Fin.sum_univ_five,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · ring
  · ring
  · linear_combination (1) * hR + (-O * j) * hK + (O ^ (5:ℕ) * j ^ (3:ℕ) + c * O ^ (4:ℕ) * j ^ (2:ℕ)
    + d * O ^ (4:ℕ) * j ^ (2:ℕ) + 2 * σ * O ^ (4:ℕ) * j ^ (2:ℕ) + c * d * O ^ (3:ℕ) * j +
    2 * c * σ * O ^ (3:ℕ) * j + 2 * d * σ * O ^ (3:ℕ) * j + σ ^ (2:ℕ) * O ^ (3:ℕ) * j +
    w ^ (2:ℕ) * O ^ (3:ℕ) * j - O ^ (5:ℕ) * j + 2 * c * d * σ * O ^ (2:ℕ) +
    c * σ ^ (2:ℕ) * O ^ (2:ℕ) + d * σ ^ (2:ℕ) * O ^ (2:ℕ) + c * w ^ (2:ℕ) * O ^ (2:ℕ) +
    d * w ^ (2:ℕ) * O ^ (2:ℕ) - c * O ^ (4:ℕ) - d * O ^ (4:ℕ) - 2 * σ * O ^ (4:ℕ) -
    c * K * O ^ (2:ℕ)) * hj
  · ring
  · ring

/-- **The left critical eigenvector of the rotated pattern** under the two Hopf relations. Static
    algebra. -/
@[tmio M, powerlib_domain] theorem AnglePattern.left {c d K g σ w O j : ℂ}
    (hj : j ^ 2 = -1)
    (hK : 2 * σ * c * K = (d * c - O ^ 2) * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * (d + c) * O ^ 2)
    (hR : c * g * w = c * K * (σ ^ 2 + w ^ 2 - O ^ 2) +
      O ^ 2 * ((d + c) * (σ ^ 2 + w ^ 2 - O ^ 2) + 2 * σ * (d * c - O ^ 2))) :
    (AnglePattern.jac c d K g σ w)ᵀ *ᵥ angleVecP c d g σ w O j = (-(O
        * j)) • angleVecP c d g σ w O j := by
  ext k
  fin_cases k <;> simp only [AnglePattern.jac, angleVecP, Matrix.mulVec, dotProduct,
      Fin.sum_univ_five,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk]
  · linear_combination (1) * hR + (O * j) * hK + (-O ^ (5:ℕ) * j ^ (3:ℕ) + c * O ^ (4:ℕ) * j ^ (2:ℕ)
    + d * O ^ (4:ℕ) * j ^ (2:ℕ) + 2 * σ * O ^ (4:ℕ) * j ^ (2:ℕ) - c * d * O ^ (3:ℕ) * j -
    2 * c * σ * O ^ (3:ℕ) * j - 2 * d * σ * O ^ (3:ℕ) * j - σ ^ (2:ℕ) * O ^ (3:ℕ) * j -
    w ^ (2:ℕ) * O ^ (3:ℕ) * j + O ^ (5:ℕ) * j + 2 * c * d * σ * O ^ (2:ℕ) +
    c * σ ^ (2:ℕ) * O ^ (2:ℕ) + d * σ ^ (2:ℕ) * O ^ (2:ℕ) + c * w ^ (2:ℕ) * O ^ (2:ℕ) +
    d * w ^ (2:ℕ) * O ^ (2:ℕ) - c * O ^ (4:ℕ) - d * O ^ (4:ℕ) - 2 * σ * O ^ (4:ℕ) -
    c * K * O ^ (2:ℕ)) * hj
  · ring
  · ring
  · ring
  · ring

/-- The solution of `J r = B(u, v)` (times `c (g w − K ρ)`). Static algebra. -/
@[tmio M, powerlib_domain] theorem AnglePattern.jac_solveJ (c d K g N σ w : ℂ) (u v : Fin 5 → ℂ) :
    AnglePattern.jac c d K g σ w *ᵥ AnglePattern.solveJ c K g σ w (AnglePattern.bilin c g N u v) =
      (c * (g * w - K * (σ ^ 2 + w ^ 2))) • AnglePattern.bilin c g N u v := by
  ext k
  fin_cases k <;> simp only [AnglePattern.jac, AnglePattern.solveJ, AnglePattern.bilin,
      Matrix.mulVec, dotProduct, Fin.sum_univ_five,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    ring

/-- The solution of `(2jO − J) s = B(u, v)` (times `χ(2jO)`). Static algebra. -/
@[tmio M, powerlib_domain] theorem AnglePattern.shift_solveShift (c d K g N σ w O j : ℂ) (u v : Fin
    5 → ℂ) :
    ((2 * O * j) • (1 : Matrix (Fin 5) (Fin 5) ℂ) - AnglePattern.jac c d K g σ w) *ᵥ
        AnglePattern.solveShift c d K g σ w O j (AnglePattern.bilin c g N u v) =
      AnglePattern.shiftDet c d K g σ w O j • AnglePattern.bilin c g N u v := by
  ext k
  fin_cases k <;> simp only [AnglePattern.jac, AnglePattern.solveShift, AnglePattern.shiftDet,
      AnglePattern.bilin, Matrix.mulVec, dotProduct,
      Fin.sum_univ_five, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq,
      ↓reduceIte] <;>
    ring


/-- The pairing Y1 expanded (no relation used). -/
private def agY1raw {R : Type*} [CommRing R] (c K g σ w O j : R) : R :=
  (((c * K * O ^ (8:ℕ) * j ^ (8:ℕ) + 4 * c * K * σ * O ^ (7:ℕ) * j ^ (7:ℕ) +
    4 * c * K * σ ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ) + 4 * c * K * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ) -
    4 * c * K * σ ^ (3:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ)) +
    (12 * c * K * σ * w ^ (2:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ) - 4 * c * g * w * O ^ (6:ℕ) * j ^ (6:ℕ) -
    10 * c * K * σ ^ (4:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    12 * c * K * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    6 * c * K * w ^ (4:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ))) + ((-12 * c * g * σ * w * O ^ (5:ℕ) * j ^ (5:ℕ)
    - 4 * c * K * σ ^ (5:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
    8 * c * K * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
    12 * c * K * σ * w ^ (4:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) -
    12 * c * g * σ ^ (2:ℕ) * w * O ^ (4:ℕ) * j ^ (4:ℕ)) +
    (-12 * c * g * w ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) + 4 * c * K * σ ^ (6:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ)
    + 12 * c * K * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    12 * c * K * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    4 * c * K * w ^ (6:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ)))) +
    (((-8 * c * g * σ ^ (3:ℕ) * w * O ^ (3:ℕ) * j ^ (3:ℕ) -
    24 * c * g * σ * w ^ (3:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) + 4 * c * K * σ ^ (7:ℕ) * O * j +
    12 * c * K * σ ^ (5:ℕ) * w ^ (2:ℕ) * O * j + 12 * c * K * σ ^ (3:ℕ) * w ^ (4:ℕ) * O * j) +
    (4 * c * K * σ * w ^ (6:ℕ) * O * j - 12 * c * g * σ ^ (4:ℕ) * w * O ^ (2:ℕ) * j ^ (2:ℕ) -
    24 * c * g * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
    12 * c * g * w ^ (5:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) + c * K * σ ^ (8:ℕ))) +
    ((4 * c * K * σ ^ (6:ℕ) * w ^ (2:ℕ) + 6 * c * K * σ ^ (4:ℕ) * w ^ (4:ℕ) +
    4 * c * K * σ ^ (2:ℕ) * w ^ (6:ℕ) + c * K * w ^ (8:ℕ) - 12 * c * g * σ ^ (5:ℕ) * w * O * j) +
    (-24 * c * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O * j - 12 * c * g * σ * w ^ (5:ℕ) * O * j -
    4 * c * g * σ ^ (6:ℕ) * w - 12 * c * g * σ ^ (4:ℕ) * w ^ (3:ℕ) -
    12 * c * g * σ ^ (2:ℕ) * w ^ (5:ℕ) - 4 * c * g * w ^ (7:ℕ))))

@[tmio M, powerlib_domain] private theorem ag_Y1raw (c d K g σ w O j : ℂ) :
    angleVecP c d g σ w (-O) j ⬝ᵥ AnglePattern.trilin c g K (angleVecQ d σ w O j)
        (angleVecQ d σ w O j) (angleVecQ d σ w (-O) j) =
      agY1raw c K g σ w O j := by
  simp only [angleVecP, angleVecQ, AnglePattern.trilin, agY1raw, dotProduct, Fin.sum_univ_five,
      Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- `⟨p̃, C(q, q, q̄)⟩` reduced modulo the Hopf relations. Static algebra. -/
@[tmio M, powerlib_domain] theorem AnglePattern.trilin_pairing {c d K g σ w O j : ℂ}
    (hj : j ^ 2 = -1)
    (hK : 2 * σ * c * K = (d * c - O ^ 2) * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * (d + c) * O ^ 2)
    (hg : 2 * σ * c * w * g =
      (d * c - O ^ 2) * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2)) :
    (2 * σ * c) * (2 * σ * c * w)
        * (angleVecP c d g σ w (-O) j ⬝ᵥ AnglePattern.trilin c g K (angleVecQ d σ w O j)
        (angleVecQ d σ w O j) (angleVecQ d σ w (-O) j)) =
      2 * w * σ * c ^ 2 * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2) * ((σ ^ 2 + w ^ 2
          - O ^ 2) + 2 * σ * O * j) * (AngleKey.trilinRe c d σ w O + AngleKey.trilinIm c d σ w O
              * j) := by
  rw [ag_Y1raw]
  simp only [agY1raw, AngleKey.trilinRe, AngleKey.trilinIm]
  linear_combination (((8 * c ^ (2:ℕ) * σ ^ (8:ℕ) * w * O * j +
    24 * c ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * O * j + 24 * c ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) * O * j
    + 8 * c ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (7:ℕ) * O * j + 8 * c ^ (2:ℕ) * σ ^ (6:ℕ) * w * O ^ (3:ℕ) * j
    - 16 * c ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j) +
    (-24 * c ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j -
    8 * c ^ (2:ℕ) * σ ^ (4:ℕ) * w * O ^ (5:ℕ) * j +
    24 * c ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j -
    8 * c ^ (2:ℕ) * σ ^ (2:ℕ) * w * O ^ (7:ℕ) * j + 2 * c ^ (2:ℕ) * σ ^ (9:ℕ) * w +
    8 * c ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ))) + ((12 * c ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (5:ℕ) +
    8 * c ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (7:ℕ) + 2 * c ^ (2:ℕ) * σ * w ^ (9:ℕ) -
    8 * c ^ (2:ℕ) * σ ^ (7:ℕ) * w * O ^ (2:ℕ) - 24 * c ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) -
    24 * c ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ)) +
    (-8 * c ^ (2:ℕ) * σ * w ^ (7:ℕ) * O ^ (2:ℕ) - 20 * c ^ (2:ℕ) * σ ^ (5:ℕ) * w * O ^ (4:ℕ) +
    24 * c ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) + 12 * c ^ (2:ℕ) * σ * w ^ (5:ℕ) * O ^ (4:ℕ)
    - 8 * c ^ (2:ℕ) * σ ^ (3:ℕ) * w * O ^ (6:ℕ) - 8 * c ^ (2:ℕ) * σ * w ^ (3:ℕ) * O ^ (6:ℕ) +
    2 * c ^ (2:ℕ) * σ * w * O ^ (8:ℕ)))) * hK + (-24 * c ^ (2:ℕ) * σ ^ (6:ℕ) * w * O * j -
    48 * c ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * O * j - 24 * c ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (5:ℕ) * O * j
    + 16 * c ^ (2:ℕ) * σ ^ (4:ℕ) * w * O ^ (3:ℕ) * j +
    48 * c ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j -
    24 * c ^ (2:ℕ) * σ ^ (2:ℕ) * w * O ^ (5:ℕ) * j - 8 * c ^ (2:ℕ) * σ ^ (7:ℕ) * w -
    24 * c ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) - 24 * c ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) -
    8 * c ^ (2:ℕ) * σ * w ^ (7:ℕ) + 24 * c ^ (2:ℕ) * σ ^ (5:ℕ) * w * O ^ (2:ℕ) +
    48 * c ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) + 24 * c ^ (2:ℕ) * σ * w ^ (5:ℕ) * O ^ (2:ℕ)
    - 24 * c ^ (2:ℕ) * σ ^ (3:ℕ) * w * O ^ (4:ℕ) - 24 * c ^ (2:ℕ) * σ * w ^ (3:ℕ) * O ^ (4:ℕ) +
    8 * c ^ (2:ℕ) * σ * w * O ^ (6:ℕ)) * hg +
    (((((4 * c ^ (3:ℕ) * K * σ ^ (2:ℕ) * w * O ^ (8:ℕ) * j ^ (6:ℕ) +
    16 * c ^ (3:ℕ) * K * σ ^ (3:ℕ) * w * O ^ (7:ℕ) * j ^ (5:ℕ) +
    16 * c ^ (3:ℕ) * K * σ ^ (4:ℕ) * w * O ^ (6:ℕ) * j ^ (4:ℕ) +
    16 * c ^ (3:ℕ) * K * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ)) +
    (-4 * c ^ (3:ℕ) * K * σ ^ (2:ℕ) * w * O ^ (8:ℕ) * j ^ (4:ℕ) -
    16 * c ^ (3:ℕ) * K * σ ^ (5:ℕ) * w * O ^ (5:ℕ) * j ^ (3:ℕ) +
    48 * c ^ (3:ℕ) * K * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) -
    16 * c ^ (3:ℕ) * K * σ ^ (3:ℕ) * w * O ^ (7:ℕ) * j ^ (3:ℕ) -
    16 * c ^ (3:ℕ) * g * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ))) +
    ((-40 * c ^ (3:ℕ) * K * σ ^ (6:ℕ) * w * O ^ (4:ℕ) * j ^ (2:ℕ) +
    48 * c ^ (3:ℕ) * K * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    24 * c ^ (3:ℕ) * K * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) -
    16 * c ^ (3:ℕ) * K * σ ^ (4:ℕ) * w * O ^ (6:ℕ) * j ^ (2:ℕ) -
    16 * c ^ (3:ℕ) * K * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ)) +
    (4 * c ^ (3:ℕ) * K * σ ^ (2:ℕ) * w * O ^ (8:ℕ) * j ^ (2:ℕ) -
    48 * c ^ (3:ℕ) * g * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) +
    8 * c ^ (3:ℕ) * d * σ ^ (9:ℕ) * w * O ^ (2:ℕ) +
    24 * c ^ (3:ℕ) * d * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) +
    24 * c ^ (3:ℕ) * d * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ)))) +
    (((8 * c ^ (3:ℕ) * d * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ) +
    8 * c ^ (3:ℕ) * d * σ ^ (7:ℕ) * w * O ^ (4:ℕ) + 16 * c ^ (3:ℕ) * σ ^ (8:ℕ) * w * O ^ (4:ℕ) +
    16 * c ^ (2:ℕ) * d * σ ^ (8:ℕ) * w * O ^ (4:ℕ)) + (-8 * c ^ (2:ℕ) * σ ^ (9:ℕ) * w * O ^ (4:ℕ) -
    16 * c ^ (3:ℕ) * d * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) +
    32 * c ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) +
    32 * c ^ (2:ℕ) * d * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) -
    24 * c ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ))) +
    ((-24 * c ^ (3:ℕ) * d * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) +
    16 * c ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) +
    16 * c ^ (2:ℕ) * d * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) -
    24 * c ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) -
    8 * c ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ)) +
    (-8 * c ^ (3:ℕ) * d * σ ^ (5:ℕ) * w * O ^ (6:ℕ) + 32 * c ^ (3:ℕ) * σ ^ (6:ℕ) * w * O ^ (6:ℕ) +
    32 * c ^ (2:ℕ) * d * σ ^ (6:ℕ) * w * O ^ (6:ℕ) - 8 * c ^ (2:ℕ) * σ ^ (7:ℕ) * w * O ^ (6:ℕ) +
    24 * c ^ (3:ℕ) * d * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ))))) +
    ((((-32 * c ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) -
    32 * c ^ (2:ℕ) * d * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) +
    16 * c ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) +
    24 * c ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ)) +
    (-8 * c ^ (3:ℕ) * d * σ ^ (3:ℕ) * w * O ^ (8:ℕ) + 16 * c ^ (3:ℕ) * σ ^ (4:ℕ) * w * O ^ (8:ℕ) +
    16 * c ^ (2:ℕ) * d * σ ^ (4:ℕ) * w * O ^ (8:ℕ) + 8 * c ^ (2:ℕ) * σ ^ (5:ℕ) * w * O ^ (8:ℕ) -
    24 * c ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ))) +
    ((8 * c ^ (2:ℕ) * σ ^ (3:ℕ) * w * O ^ (10:ℕ) -
    16 * c ^ (3:ℕ) * K * σ ^ (7:ℕ) * w * O ^ (3:ℕ) * j +
    32 * c ^ (3:ℕ) * K * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j +
    48 * c ^ (3:ℕ) * K * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j +
    16 * c ^ (3:ℕ) * K * σ ^ (5:ℕ) * w * O ^ (5:ℕ) * j) +
    (-48 * c ^ (3:ℕ) * K * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j +
    16 * c ^ (3:ℕ) * K * σ ^ (3:ℕ) * w * O ^ (7:ℕ) * j -
    48 * c ^ (3:ℕ) * g * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) -
    48 * c ^ (3:ℕ) * g * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    16 * c ^ (3:ℕ) * g * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ)))) +
    (((16 * c ^ (3:ℕ) * K * σ ^ (8:ℕ) * w * O ^ (2:ℕ) +
    48 * c ^ (3:ℕ) * K * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) +
    48 * c ^ (3:ℕ) * K * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) +
    16 * c ^ (3:ℕ) * K * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ)) +
    (40 * c ^ (3:ℕ) * K * σ ^ (6:ℕ) * w * O ^ (4:ℕ) -
    48 * c ^ (3:ℕ) * K * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) -
    24 * c ^ (3:ℕ) * K * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) +
    16 * c ^ (3:ℕ) * K * σ ^ (4:ℕ) * w * O ^ (6:ℕ) +
    16 * c ^ (3:ℕ) * K * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ))) +
    ((-4 * c ^ (3:ℕ) * K * σ ^ (2:ℕ) * w * O ^ (8:ℕ) -
    32 * c ^ (3:ℕ) * g * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j -
    96 * c ^ (3:ℕ) * g * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j +
    48 * c ^ (3:ℕ) * g * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j -
    48 * c ^ (3:ℕ) * g * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ)) +
    (-96 * c ^ (3:ℕ) * g * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) -
    48 * c ^ (3:ℕ) * g * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ) +
    48 * c ^ (3:ℕ) * g * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) +
    48 * c ^ (3:ℕ) * g * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) -
    16 * c ^ (3:ℕ) * g * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ)))))) * hj

/-- The pairing Y2 expanded (no relation used). -/
private def agY2raw {R : Type*} [CommRing R] (c K g N σ w O j : R) : R :=
  ((((c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (8:ℕ) +
    c ^ (2:ℕ) * N ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (8:ℕ) +
    4 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * O ^ (7:ℕ) * j ^ (7:ℕ) +
    4 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ * w ^ (2:ℕ) * O ^ (7:ℕ) * j ^ (7:ℕ) +
    c ^ (2:ℕ) * K * g * w * O ^ (8:ℕ) * j ^ (8:ℕ) +
    4 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ)) +
    (8 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ) +
    4 * c ^ (2:ℕ) * N ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ) +
    4 * c ^ (2:ℕ) * K * g * σ * w * O ^ (7:ℕ) * j ^ (7:ℕ) -
    c ^ (2:ℕ) * g ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (8:ℕ) -
    4 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ) +
    8 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ))) +
    ((12 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ * w ^ (4:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ) +
    2 * c ^ (2:ℕ) * g * N * σ ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ) +
    4 * c ^ (2:ℕ) * K * g * σ ^ (2:ℕ) * w * O ^ (6:ℕ) * j ^ (6:ℕ) +
    2 * c ^ (2:ℕ) * g * N * σ * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ) +
    4 * c ^ (2:ℕ) * K * g * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ) -
    4 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ * O ^ (7:ℕ) * j ^ (7:ℕ)) +
    (-10 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (6:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    2 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    18 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    6 * c ^ (2:ℕ) * N ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    8 * c ^ (2:ℕ) * g * N * σ ^ (4:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ) -
    4 * c ^ (2:ℕ) * K * g * σ ^ (3:ℕ) * w * O ^ (5:ℕ) * j ^ (5:ℕ) +
    8 * c ^ (2:ℕ) * g * N * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ)))) +
    (((12 * c ^ (2:ℕ) * K * g * σ * w ^ (3:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ) -
    6 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ) -
    4 * c ^ (2:ℕ) * g ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ) -
    4 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (7:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
    4 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
    20 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ)) +
    (12 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ * w ^ (6:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
    10 * c ^ (2:ℕ) * g * N * σ ^ (5:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) -
    10 * c ^ (2:ℕ) * K * g * σ ^ (4:ℕ) * w * O ^ (4:ℕ) * j ^ (4:ℕ) +
    12 * c ^ (2:ℕ) * g * N * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    12 * c ^ (2:ℕ) * K * g * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    2 * c ^ (2:ℕ) * g * N * σ * w ^ (4:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ))) +
    ((6 * c ^ (2:ℕ) * K * g * w ^ (5:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) -
    4 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ) -
    12 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ * w ^ (2:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ) +
    4 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (8:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    16 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    24 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ)) +
    (16 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    4 * c ^ (2:ℕ) * N ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
    4 * c ^ (2:ℕ) * K * g * σ ^ (5:ℕ) * w * O ^ (3:ℕ) * j ^ (3:ℕ) +
    8 * c ^ (2:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
    12 * c ^ (2:ℕ) * K * g * σ * w ^ (5:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) -
    14 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) -
    6 * c ^ (2:ℕ) * g ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ))))) +
    ((((4 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (9:ℕ) * O * j +
    16 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * O * j +
    24 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * O * j +
    16 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * O * j +
    4 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ * w ^ (8:ℕ) * O * j -
    10 * c ^ (2:ℕ) * g * N * σ ^ (7:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ)) +
    (4 * c ^ (2:ℕ) * K * g * σ ^ (6:ℕ) * w * O ^ (2:ℕ) * j ^ (2:ℕ) -
    22 * c ^ (2:ℕ) * g * N * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    12 * c ^ (2:ℕ) * K * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
    14 * c ^ (2:ℕ) * g * N * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    12 * c ^ (2:ℕ) * K * g * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
    2 * c ^ (2:ℕ) * g * N * σ * w ^ (6:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ))) +
    ((4 * c ^ (2:ℕ) * K * g * w ^ (7:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    4 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (5:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) -
    8 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) -
    12 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ * w ^ (4:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
    c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (10:ℕ) + 5 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ)) +
    (10 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) +
    10 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) +
    5 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) + c ^ (2:ℕ) * N ^ (2:ℕ) * w ^ (10:ℕ) -
    8 * c ^ (2:ℕ) * g * N * σ ^ (8:ℕ) * O * j + 4 * c ^ (2:ℕ) * K * g * σ ^ (7:ℕ) * w * O * j -
    24 * c ^ (2:ℕ) * g * N * σ ^ (6:ℕ) * w ^ (2:ℕ) * O * j))) +
    (((12 * c ^ (2:ℕ) * K * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O * j -
    24 * c ^ (2:ℕ) * g * N * σ ^ (4:ℕ) * w ^ (4:ℕ) * O * j +
    12 * c ^ (2:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O * j -
    8 * c ^ (2:ℕ) * g * N * σ ^ (2:ℕ) * w ^ (6:ℕ) * O * j +
    4 * c ^ (2:ℕ) * K * g * σ * w ^ (7:ℕ) * O * j +
    6 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (6:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ)) +
    (-10 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
    4 * c ^ (2:ℕ) * g ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
    2 * c ^ (2:ℕ) * g * N * σ ^ (9:ℕ) + c ^ (2:ℕ) * K * g * σ ^ (8:ℕ) * w -
    8 * c ^ (2:ℕ) * g * N * σ ^ (7:ℕ) * w ^ (2:ℕ) + 4 * c ^ (2:ℕ) * K * g * σ ^ (6:ℕ) * w ^ (3:ℕ) -
    12 * c ^ (2:ℕ) * g * N * σ ^ (5:ℕ) * w ^ (4:ℕ))) +
    ((6 * c ^ (2:ℕ) * K * g * σ ^ (4:ℕ) * w ^ (5:ℕ) - 8 * c ^ (2:ℕ) * g * N * σ ^ (3:ℕ) * w ^ (6:ℕ)
    + 4 * c ^ (2:ℕ) * K * g * σ ^ (2:ℕ) * w ^ (7:ℕ) - 2 * c ^ (2:ℕ) * g * N * σ * w ^ (8:ℕ) +
    c ^ (2:ℕ) * K * g * w ^ (9:ℕ) + 4 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (7:ℕ) * O * j) +
    (4 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O * j -
    4 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O * j -
    4 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ * w ^ (6:ℕ) * O * j + c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (8:ℕ) +
    2 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) -
    2 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) - c ^ (2:ℕ) * g ^ (2:ℕ) * w ^ (8:ℕ)))))

@[tmio M, powerlib_domain] private theorem ag_Y2raw (c d K g N σ w O j : ℂ) :
    angleVecP c d g σ w (-O) j ⬝ᵥ AnglePattern.bilin c g N (angleVecQ d σ w O j)
        (AnglePattern.solveJ c K g σ w (AnglePattern.bilin c g N (angleVecQ d σ w O j) (angleVecQ d
            σ w (-O) j))) =
      agY2raw c K g N σ w O j := by
  simp only [angleVecP, angleVecQ, AnglePattern.bilin, AnglePattern.solveJ, agY2raw, dotProduct,
      Fin.sum_univ_five, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- `⟨p̃, B(q, r̄)⟩` reduced modulo the Hopf relations. Static algebra. -/
@[tmio M, powerlib_domain] theorem AnglePattern.bilin_pairing {c d K g N σ w O j : ℂ}
    (hj : j ^ 2 = -1)
    (hK : 2 * σ * c * K = (d * c - O ^ 2) * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * (d + c) * O ^ 2)
    (hg : 2 * σ * c * w * g =
      (d * c - O ^ 2) * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2)) :
    (2 * σ * c) * (2 * σ * c * w) ^ 2
        * (angleVecP c d g σ w (-O) j ⬝ᵥ AnglePattern.bilin c g N (angleVecQ d σ w O j)
        (AnglePattern.solveJ c K g σ w (AnglePattern.bilin c g N (angleVecQ d σ w O j) (angleVecQ d
            σ w (-O) j)))) =
      2 * σ * c ^ 3 * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2)
          * AngleKey.bilinRed c d N σ w O * ((σ ^ 2 + w ^ 2 - O ^ 2) + 2 * σ * O * j) ^ 2 := by
  rw [ag_Y2raw]
  simp only [agY2raw, AngleKey.bilinRed]
  linear_combination (((16 * c ^ (4:ℕ) * g * σ ^ (9:ℕ) * w ^ (3:ℕ) * O * j +
    48 * c ^ (4:ℕ) * g * σ ^ (7:ℕ) * w ^ (5:ℕ) * O * j +
    48 * c ^ (4:ℕ) * g * σ ^ (5:ℕ) * w ^ (7:ℕ) * O * j +
    16 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (9:ℕ) * O * j +
    16 * c ^ (4:ℕ) * g * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j -
    32 * c ^ (4:ℕ) * g * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j) +
    (-48 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (3:ℕ) * j -
    16 * c ^ (4:ℕ) * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j +
    48 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j -
    16 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j +
    4 * c ^ (4:ℕ) * g * σ ^ (10:ℕ) * w ^ (3:ℕ) + 16 * c ^ (4:ℕ) * g * σ ^ (8:ℕ) * w ^ (5:ℕ))) +
    ((24 * c ^ (4:ℕ) * g * σ ^ (6:ℕ) * w ^ (7:ℕ) + 16 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (9:ℕ) +
    4 * c ^ (4:ℕ) * g * σ ^ (2:ℕ) * w ^ (11:ℕ) -
    16 * c ^ (4:ℕ) * g * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) -
    48 * c ^ (4:ℕ) * g * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) -
    48 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ)) +
    (-16 * c ^ (4:ℕ) * g * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (2:ℕ) -
    40 * c ^ (4:ℕ) * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) +
    48 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) +
    24 * c ^ (4:ℕ) * g * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) -
    16 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) -
    16 * c ^ (4:ℕ) * g * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) +
    4 * c ^ (4:ℕ) * g * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ)))) * hK +
    ((((((8 * c ^ (4:ℕ) * d * σ ^ (12:ℕ) * O * j +
    32 * c ^ (4:ℕ) * d * σ ^ (10:ℕ) * w ^ (2:ℕ) * O * j +
    48 * c ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (4:ℕ) * O * j +
    32 * c ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (6:ℕ) * O * j +
    8 * c ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (8:ℕ) * O * j) +
    (8 * c ^ (4:ℕ) * d * σ ^ (10:ℕ) * O ^ (3:ℕ) * j - 8 * c ^ (3:ℕ) * σ ^ (12:ℕ) * O ^ (3:ℕ) * j -
    16 * c ^ (4:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j -
    16 * c ^ (3:ℕ) * d * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j -
    32 * c ^ (3:ℕ) * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j)) +
    ((-16 * c ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j -
    48 * c ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j -
    48 * c ^ (3:ℕ) * d * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j -
    48 * c ^ (3:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j -
    48 * c ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (3:ℕ) * j) +
    (-48 * c ^ (3:ℕ) * d * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (3:ℕ) * j -
    32 * c ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (3:ℕ) * j +
    8 * c ^ (4:ℕ) * d * σ ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (3:ℕ) * j -
    16 * c ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (3:ℕ) * j -
    16 * c ^ (3:ℕ) * d * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (3:ℕ) * j -
    8 * c ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (3:ℕ) * j))) +
    (((-16 * c ^ (4:ℕ) * d * σ ^ (8:ℕ) * O ^ (5:ℕ) * j - 8 * c ^ (3:ℕ) * σ ^ (10:ℕ) * O ^ (5:ℕ) * j
    - 16 * c ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j -
    16 * c ^ (3:ℕ) * d * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j -
    16 * c ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j) +
    (32 * c ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j +
    32 * c ^ (3:ℕ) * d * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j +
    16 * c ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j -
    32 * c ^ (4:ℕ) * d * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (5:ℕ) * j +
    48 * c ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (5:ℕ) * j +
    48 * c ^ (3:ℕ) * d * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (5:ℕ) * j)) +
    ((-8 * c ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (5:ℕ) * j -
    16 * c ^ (4:ℕ) * d * σ ^ (6:ℕ) * O ^ (7:ℕ) * j + 16 * c ^ (3:ℕ) * σ ^ (8:ℕ) * O ^ (7:ℕ) * j +
    16 * c ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j +
    16 * c ^ (3:ℕ) * d * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j) +
    (48 * c ^ (4:ℕ) * d * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j -
    48 * c ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j -
    48 * c ^ (3:ℕ) * d * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j +
    16 * c ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j +
    32 * c ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (7:ℕ) * j +
    8 * c ^ (4:ℕ) * d * σ ^ (4:ℕ) * O ^ (9:ℕ) * j)))) +
    ((((16 * c ^ (3:ℕ) * σ ^ (6:ℕ) * O ^ (9:ℕ) * j -
    32 * c ^ (4:ℕ) * d * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j +
    16 * c ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j +
    16 * c ^ (3:ℕ) * d * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j -
    48 * c ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (9:ℕ) * j) +
    (8 * c ^ (4:ℕ) * d * σ ^ (2:ℕ) * O ^ (11:ℕ) * j - 8 * c ^ (3:ℕ) * σ ^ (4:ℕ) * O ^ (11:ℕ) * j +
    32 * c ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (11:ℕ) * j -
    8 * c ^ (3:ℕ) * σ ^ (2:ℕ) * O ^ (13:ℕ) * j + 2 * c ^ (4:ℕ) * d * σ ^ (13:ℕ))) +
    ((10 * c ^ (4:ℕ) * d * σ ^ (11:ℕ) * w ^ (2:ℕ) + 20 * c ^ (4:ℕ) * d * σ ^ (9:ℕ) * w ^ (4:ℕ) +
    20 * c ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (6:ℕ) + 10 * c ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (8:ℕ) +
    2 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (10:ℕ)) + (-8 * c ^ (4:ℕ) * d * σ ^ (11:ℕ) * O ^ (2:ℕ) -
    2 * c ^ (3:ℕ) * σ ^ (13:ℕ) * O ^ (2:ℕ) - 30 * c ^ (4:ℕ) * d * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ)
    - 4 * c ^ (4:ℕ) * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) -
    4 * c ^ (3:ℕ) * d * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) -
    10 * c ^ (3:ℕ) * σ ^ (11:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ)))) +
    (((-40 * c ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) -
    16 * c ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) -
    16 * c ^ (3:ℕ) * d * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) -
    20 * c ^ (3:ℕ) * σ ^ (9:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) -
    20 * c ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ)) +
    (-24 * c ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ) -
    24 * c ^ (3:ℕ) * d * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ) -
    20 * c ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ) -
    16 * c ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (2:ℕ) -
    16 * c ^ (3:ℕ) * d * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (2:ℕ) -
    10 * c ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (8:ℕ) * O ^ (2:ℕ))) +
    ((2 * c ^ (4:ℕ) * d * σ * w ^ (10:ℕ) * O ^ (2:ℕ) -
    4 * c ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (10:ℕ) * O ^ (2:ℕ) -
    4 * c ^ (3:ℕ) * d * σ ^ (2:ℕ) * w ^ (10:ℕ) * O ^ (2:ℕ) -
    2 * c ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (10:ℕ) * O ^ (2:ℕ) - 22 * c ^ (4:ℕ) * d * σ ^ (9:ℕ) * O ^ (4:ℕ))
    + (8 * c ^ (3:ℕ) * σ ^ (11:ℕ) * O ^ (4:ℕ) -
    12 * c ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) +
    16 * c ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) +
    16 * c ^ (3:ℕ) * d * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) +
    30 * c ^ (3:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) +
    48 * c ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ)))))) +
    (((((48 * c ^ (3:ℕ) * d * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) +
    40 * c ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) -
    20 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) +
    48 * c ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) +
    48 * c ^ (3:ℕ) * d * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ)) +
    (20 * c ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) -
    10 * c ^ (4:ℕ) * d * σ * w ^ (8:ℕ) * O ^ (4:ℕ) +
    16 * c ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) +
    16 * c ^ (3:ℕ) * d * σ ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) -
    2 * c ^ (3:ℕ) * σ * w ^ (10:ℕ) * O ^ (4:ℕ))) + ((22 * c ^ (3:ℕ) * σ ^ (9:ℕ) * O ^ (6:ℕ) -
    12 * c ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) +
    40 * c ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) +
    40 * c ^ (3:ℕ) * d * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) +
    12 * c ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ)) +
    (40 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) -
    48 * c ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) -
    48 * c ^ (3:ℕ) * d * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) +
    20 * c ^ (4:ℕ) * d * σ * w ^ (6:ℕ) * O ^ (6:ℕ) -
    24 * c ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) -
    24 * c ^ (3:ℕ) * d * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ)))) +
    (((20 * c ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) +
    10 * c ^ (3:ℕ) * σ * w ^ (8:ℕ) * O ^ (6:ℕ) + 22 * c ^ (4:ℕ) * d * σ ^ (5:ℕ) * O ^ (8:ℕ) -
    30 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) +
    16 * c ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ)) +
    (16 * c ^ (3:ℕ) * d * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) +
    12 * c ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) -
    20 * c ^ (4:ℕ) * d * σ * w ^ (4:ℕ) * O ^ (8:ℕ) +
    16 * c ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) +
    16 * c ^ (3:ℕ) * d * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) -
    40 * c ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ))) +
    ((-20 * c ^ (3:ℕ) * σ * w ^ (6:ℕ) * O ^ (8:ℕ) + 8 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * O ^ (10:ℕ) -
    22 * c ^ (3:ℕ) * σ ^ (5:ℕ) * O ^ (10:ℕ) + 10 * c ^ (4:ℕ) * d * σ * w ^ (2:ℕ) * O ^ (10:ℕ) -
    4 * c ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ)) +
    (-4 * c ^ (3:ℕ) * d * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) +
    30 * c ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) +
    20 * c ^ (3:ℕ) * σ * w ^ (4:ℕ) * O ^ (10:ℕ) - 2 * c ^ (4:ℕ) * d * σ * O ^ (12:ℕ) -
    8 * c ^ (3:ℕ) * σ ^ (3:ℕ) * O ^ (12:ℕ) - 10 * c ^ (3:ℕ) * σ * w ^ (2:ℕ) * O ^ (12:ℕ))))) +
    ((((2 * c ^ (3:ℕ) * σ * O ^ (14:ℕ) - 32 * c ^ (4:ℕ) * N * σ ^ (10:ℕ) * w * O * j -
    96 * c ^ (4:ℕ) * N * σ ^ (8:ℕ) * w ^ (3:ℕ) * O * j -
    96 * c ^ (4:ℕ) * N * σ ^ (6:ℕ) * w ^ (5:ℕ) * O * j -
    32 * c ^ (4:ℕ) * N * σ ^ (4:ℕ) * w ^ (7:ℕ) * O * j) +
    (32 * c ^ (4:ℕ) * N * σ ^ (6:ℕ) * w * O ^ (5:ℕ) * j +
    32 * c ^ (4:ℕ) * N * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j - 8 * c ^ (4:ℕ) * N * σ ^ (11:ℕ) * w
    - 32 * c ^ (4:ℕ) * N * σ ^ (9:ℕ) * w ^ (3:ℕ) - 48 * c ^ (4:ℕ) * N * σ ^ (7:ℕ) * w ^ (5:ℕ))) +
    ((-32 * c ^ (4:ℕ) * N * σ ^ (5:ℕ) * w ^ (7:ℕ) - 8 * c ^ (4:ℕ) * N * σ ^ (3:ℕ) * w ^ (9:ℕ) +
    40 * c ^ (4:ℕ) * N * σ ^ (9:ℕ) * w * O ^ (2:ℕ) +
    88 * c ^ (4:ℕ) * N * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) +
    56 * c ^ (4:ℕ) * N * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ)) +
    (8 * c ^ (4:ℕ) * N * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ) +
    40 * c ^ (4:ℕ) * N * σ ^ (7:ℕ) * w * O ^ (4:ℕ) +
    48 * c ^ (4:ℕ) * N * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) +
    8 * c ^ (4:ℕ) * N * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) -
    8 * c ^ (4:ℕ) * N * σ ^ (5:ℕ) * w * O ^ (6:ℕ) -
    8 * c ^ (4:ℕ) * N * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ)))) +
    (((16 * c ^ (4:ℕ) * g * σ ^ (9:ℕ) * w * O * j +
    16 * c ^ (4:ℕ) * g * σ ^ (7:ℕ) * w ^ (3:ℕ) * O * j -
    16 * c ^ (4:ℕ) * g * σ ^ (5:ℕ) * w ^ (5:ℕ) * O * j -
    16 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (7:ℕ) * O * j -
    16 * c ^ (4:ℕ) * g * σ ^ (7:ℕ) * w * O ^ (3:ℕ) * j) +
    (32 * c ^ (4:ℕ) * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j +
    48 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j -
    16 * c ^ (4:ℕ) * g * σ ^ (5:ℕ) * w * O ^ (5:ℕ) * j -
    48 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j +
    16 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w * O ^ (7:ℕ) * j + 4 * c ^ (4:ℕ) * g * σ ^ (10:ℕ) * w)) +
    ((8 * c ^ (4:ℕ) * g * σ ^ (8:ℕ) * w ^ (3:ℕ) - 8 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (7:ℕ) -
    4 * c ^ (4:ℕ) * g * σ ^ (2:ℕ) * w ^ (9:ℕ) - 24 * c ^ (4:ℕ) * g * σ ^ (8:ℕ) * w * O ^ (2:ℕ) +
    40 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ)) +
    (16 * c ^ (4:ℕ) * g * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ) -
    56 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) -
    24 * c ^ (4:ℕ) * g * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) +
    24 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w * O ^ (6:ℕ) +
    16 * c ^ (4:ℕ) * g * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) -
    4 * c ^ (4:ℕ) * g * σ ^ (2:ℕ) * w * O ^ (8:ℕ))))))) * hg +
    ((((((8 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) +
    8 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) +
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j ^ (5:ℕ) +
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j ^ (5:ℕ) +
    8 * c ^ (5:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) +
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) +
    64 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) +
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ)) +
    ((-8 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ) -
    8 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ) +
    32 * c ^ (5:ℕ) * K * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j ^ (5:ℕ) -
    8 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ)) +
    (-32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) +
    64 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) +
    96 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) -
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ) -
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ)))) +
    (((16 * c ^ (5:ℕ) * g * N * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) +
    32 * c ^ (5:ℕ) * K * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) +
    16 * c ^ (5:ℕ) * g * N * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) +
    32 * c ^ (5:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ)) +
    (-8 * c ^ (5:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ) -
    32 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j ^ (5:ℕ) -
    8 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (15:ℕ) * O ^ (2:ℕ) -
    40 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (13:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) -
    80 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (11:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ))) +
    ((-80 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ) -
    40 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (8:ℕ) * O ^ (2:ℕ) -
    8 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (10:ℕ) * O ^ (2:ℕ) -
    32 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (13:ℕ) * O ^ (4:ℕ)) +
    (16 * c ^ (4:ℕ) * d * σ ^ (15:ℕ) * O ^ (4:ℕ) -
    72 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (11:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) +
    16 * c ^ (5:ℕ) * d * σ ^ (12:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) +
    16 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (12:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) +
    80 * c ^ (4:ℕ) * d * σ ^ (13:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ))))) +
    (((-32 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) +
    64 * c ^ (5:ℕ) * d * σ ^ (10:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) +
    64 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (10:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) +
    160 * c ^ (4:ℕ) * d * σ ^ (11:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) +
    16 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) +
    96 * c ^ (5:ℕ) * d * σ ^ (8:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) +
    96 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) +
    160 * c ^ (4:ℕ) * d * σ ^ (9:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ)) +
    ((64 * c ^ (5:ℕ) * d * σ ^ (6:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) +
    64 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) +
    80 * c ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) -
    8 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (10:ℕ) * O ^ (4:ℕ)) +
    (16 * c ^ (5:ℕ) * d * σ ^ (4:ℕ) * w ^ (10:ℕ) * O ^ (4:ℕ) +
    16 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (10:ℕ) * O ^ (4:ℕ) +
    16 * c ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (10:ℕ) * O ^ (4:ℕ) -
    40 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (11:ℕ) * O ^ (6:ℕ) +
    64 * c ^ (4:ℕ) * d * σ ^ (13:ℕ) * O ^ (6:ℕ)))) + (((-8 * c ^ (3:ℕ) * σ ^ (15:ℕ) * O ^ (6:ℕ) -
    16 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) +
    64 * c ^ (5:ℕ) * d * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) +
    64 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ)) +
    (144 * c ^ (4:ℕ) * d * σ ^ (11:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) -
    16 * c ^ (4:ℕ) * σ ^ (12:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) -
    16 * c ^ (3:ℕ) * d * σ ^ (12:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) -
    40 * c ^ (3:ℕ) * σ ^ (13:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) +
    64 * c ^ (5:ℕ) * d * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ))) +
    ((64 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) +
    64 * c ^ (4:ℕ) * d * σ ^ (9:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) -
    64 * c ^ (4:ℕ) * σ ^ (10:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) -
    64 * c ^ (3:ℕ) * d * σ ^ (10:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ)) +
    (-80 * c ^ (3:ℕ) * σ ^ (11:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) +
    16 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) -
    64 * c ^ (5:ℕ) * d * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) -
    64 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) -
    32 * c ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ)))))) +
    ((((-96 * c ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) -
    96 * c ^ (3:ℕ) * d * σ ^ (8:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) -
    80 * c ^ (3:ℕ) * σ ^ (9:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) +
    40 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (6:ℕ) -
    64 * c ^ (5:ℕ) * d * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (6:ℕ) -
    64 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (6:ℕ) -
    64 * c ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (8:ℕ) * O ^ (6:ℕ) -
    64 * c ^ (3:ℕ) * d * σ ^ (6:ℕ) * w ^ (8:ℕ) * O ^ (6:ℕ)) +
    ((-40 * c ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (8:ℕ) * O ^ (6:ℕ) +
    16 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (10:ℕ) * O ^ (6:ℕ) -
    16 * c ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (10:ℕ) * O ^ (6:ℕ) -
    16 * c ^ (3:ℕ) * d * σ ^ (4:ℕ) * w ^ (10:ℕ) * O ^ (6:ℕ)) +
    (-8 * c ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (10:ℕ) * O ^ (6:ℕ) +
    80 * c ^ (4:ℕ) * d * σ ^ (11:ℕ) * O ^ (8:ℕ) - 32 * c ^ (3:ℕ) * σ ^ (13:ℕ) * O ^ (8:ℕ) -
    16 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) +
    96 * c ^ (5:ℕ) * d * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ)))) +
    (((96 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) +
    32 * c ^ (4:ℕ) * d * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) -
    64 * c ^ (4:ℕ) * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) -
    64 * c ^ (3:ℕ) * d * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ)) +
    (-72 * c ^ (3:ℕ) * σ ^ (11:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) +
    32 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) -
    64 * c ^ (5:ℕ) * d * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) -
    64 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) -
    64 * c ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ))) +
    ((-64 * c ^ (3:ℕ) * d * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) -
    32 * c ^ (3:ℕ) * σ ^ (9:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) -
    80 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ) +
    96 * c ^ (5:ℕ) * d * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ)) +
    (96 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ) -
    32 * c ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ) +
    64 * c ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ) +
    64 * c ^ (3:ℕ) * d * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ) +
    16 * c ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ))))) +
    (((-80 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (8:ℕ) +
    64 * c ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (8:ℕ) +
    64 * c ^ (3:ℕ) * d * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (8:ℕ) -
    8 * c ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (10:ℕ) * O ^ (8:ℕ) +
    40 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * O ^ (10:ℕ) - 40 * c ^ (3:ℕ) * σ ^ (11:ℕ) * O ^ (10:ℕ) -
    72 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) +
    64 * c ^ (5:ℕ) * d * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ)) +
    ((64 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) +
    32 * c ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) -
    96 * c ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) -
    96 * c ^ (3:ℕ) * d * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ)) +
    (-16 * c ^ (3:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) +
    80 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ) -
    64 * c ^ (5:ℕ) * d * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ) -
    64 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ) -
    64 * c ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ)))) +
    (((64 * c ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ) +
    64 * c ^ (3:ℕ) * d * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ) +
    160 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (10:ℕ) -
    96 * c ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (10:ℕ)) +
    (-96 * c ^ (3:ℕ) * d * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (10:ℕ) +
    16 * c ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (10:ℕ) +
    40 * c ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (10:ℕ) +
    32 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * O ^ (12:ℕ) -
    80 * c ^ (4:ℕ) * d * σ ^ (7:ℕ) * O ^ (12:ℕ))) +
    ((-40 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ) +
    16 * c ^ (5:ℕ) * d * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ) +
    16 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ) +
    144 * c ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ)) +
    (-64 * c ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ) -
    64 * c ^ (3:ℕ) * d * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ) -
    16 * c ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ) -
    160 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (12:ℕ) +
    64 * c ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (12:ℕ))))))) +
    (((((64 * c ^ (3:ℕ) * d * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (12:ℕ) +
    32 * c ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (12:ℕ) -
    80 * c ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (12:ℕ) +
    8 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * O ^ (14:ℕ) - 64 * c ^ (4:ℕ) * d * σ ^ (5:ℕ) * O ^ (14:ℕ)
    + 40 * c ^ (3:ℕ) * σ ^ (7:ℕ) * O ^ (14:ℕ) +
    80 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (14:ℕ) -
    16 * c ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (14:ℕ)) +
    ((-16 * c ^ (3:ℕ) * d * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (14:ℕ) -
    72 * c ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (14:ℕ) +
    80 * c ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (14:ℕ) -
    16 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * O ^ (16:ℕ)) + (32 * c ^ (3:ℕ) * σ ^ (5:ℕ) * O ^ (16:ℕ) -
    40 * c ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (16:ℕ) + 8 * c ^ (3:ℕ) * σ ^ (3:ℕ) * O ^ (18:ℕ) -
    80 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    16 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ)))) +
    (((144 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    48 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) -
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) -
    64 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ)) +
    (-32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) +
    8 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ) +
    8 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ) +
    64 * c ^ (5:ℕ) * g * N * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) -
    32 * c ^ (5:ℕ) * K * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ))) +
    ((64 * c ^ (5:ℕ) * g * N * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) +
    96 * c ^ (5:ℕ) * K * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) -
    32 * c ^ (5:ℕ) * K * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ) -
    48 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ)) +
    (-32 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) +
    8 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ) +
    32 * c ^ (5:ℕ) * d * N * σ ^ (13:ℕ) * w * O ^ (2:ℕ) +
    128 * c ^ (5:ℕ) * d * N * σ ^ (11:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) +
    192 * c ^ (5:ℕ) * d * N * σ ^ (9:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ))))) +
    (((128 * c ^ (5:ℕ) * d * N * σ ^ (7:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ) +
    32 * c ^ (5:ℕ) * d * N * σ ^ (5:ℕ) * w ^ (9:ℕ) * O ^ (2:ℕ) +
    96 * c ^ (5:ℕ) * d * N * σ ^ (11:ℕ) * w * O ^ (4:ℕ) -
    32 * c ^ (4:ℕ) * N * σ ^ (13:ℕ) * w * O ^ (4:ℕ) +
    160 * c ^ (5:ℕ) * d * N * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) -
    128 * c ^ (4:ℕ) * N * σ ^ (11:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) +
    32 * c ^ (5:ℕ) * d * N * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) -
    192 * c ^ (4:ℕ) * N * σ ^ (9:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ)) +
    ((-32 * c ^ (5:ℕ) * d * N * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) -
    128 * c ^ (4:ℕ) * N * σ ^ (7:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) -
    32 * c ^ (4:ℕ) * N * σ ^ (5:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ) +
    96 * c ^ (5:ℕ) * d * N * σ ^ (9:ℕ) * w * O ^ (6:ℕ)) +
    (-96 * c ^ (4:ℕ) * N * σ ^ (11:ℕ) * w * O ^ (6:ℕ) +
    64 * c ^ (5:ℕ) * d * N * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) -
    160 * c ^ (4:ℕ) * N * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) -
    32 * c ^ (5:ℕ) * d * N * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) -
    32 * c ^ (4:ℕ) * N * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ)))) +
    (((32 * c ^ (4:ℕ) * N * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) +
    32 * c ^ (5:ℕ) * d * N * σ ^ (7:ℕ) * w * O ^ (8:ℕ) -
    96 * c ^ (4:ℕ) * N * σ ^ (9:ℕ) * w * O ^ (8:ℕ) +
    32 * c ^ (5:ℕ) * d * N * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ)) +
    (-64 * c ^ (4:ℕ) * N * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) +
    32 * c ^ (4:ℕ) * N * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) -
    32 * c ^ (4:ℕ) * N * σ ^ (7:ℕ) * w * O ^ (10:ℕ) -
    32 * c ^ (4:ℕ) * N * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) -
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j)) +
    ((32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j +
    160 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (3:ℕ) * j +
    96 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (3:ℕ) * j +
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j) +
    (-64 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j -
    96 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (5:ℕ) * j +
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j +
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j +
    80 * c ^ (5:ℕ) * g * N * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ)))))) +
    ((((-80 * c ^ (5:ℕ) * K * g * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    96 * c ^ (5:ℕ) * g * N * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    96 * c ^ (5:ℕ) * K * g * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    16 * c ^ (5:ℕ) * g * N * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    48 * c ^ (5:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) -
    16 * c ^ (5:ℕ) * g * N * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) -
    32 * c ^ (5:ℕ) * K * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) -
    16 * c ^ (5:ℕ) * g * N * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ)) +
    ((-32 * c ^ (5:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) +
    8 * c ^ (5:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ) -
    32 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) -
    96 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ)) +
    (32 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ) +
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) +
    96 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ) +
    96 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (8:ℕ) * O ^ (2:ℕ) +
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (10:ℕ) * O ^ (2:ℕ)))) +
    (((16 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) -
    16 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) -
    80 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) -
    48 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ)) +
    (32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) +
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) -
    8 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) -
    8 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) -
    32 * c ^ (5:ℕ) * K * g * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j)) +
    ((64 * c ^ (5:ℕ) * K * g * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j +
    96 * c ^ (5:ℕ) * K * g * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (3:ℕ) * j -
    64 * c ^ (5:ℕ) * g * N * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j +
    32 * c ^ (5:ℕ) * K * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j) +
    (-64 * c ^ (5:ℕ) * g * N * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j -
    96 * c ^ (5:ℕ) * K * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j +
    32 * c ^ (5:ℕ) * K * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j -
    112 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) -
    48 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ))))) +
    ((((48 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) +
    32 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) -
    8 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ) -
    80 * c ^ (5:ℕ) * g * N * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ)) +
    (32 * c ^ (5:ℕ) * K * g * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) -
    176 * c ^ (5:ℕ) * g * N * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) +
    96 * c ^ (5:ℕ) * K * g * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) -
    112 * c ^ (5:ℕ) * g * N * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ) +
    96 * c ^ (5:ℕ) * K * g * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ))) +
    ((-16 * c ^ (5:ℕ) * g * N * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (2:ℕ) +
    32 * c ^ (5:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (2:ℕ) -
    80 * c ^ (5:ℕ) * g * N * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) +
    80 * c ^ (5:ℕ) * K * g * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ)) +
    (-96 * c ^ (5:ℕ) * g * N * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) -
    96 * c ^ (5:ℕ) * K * g * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) -
    16 * c ^ (5:ℕ) * g * N * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) -
    48 * c ^ (5:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) +
    16 * c ^ (5:ℕ) * g * N * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ)))) +
    (((32 * c ^ (5:ℕ) * K * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) +
    16 * c ^ (5:ℕ) * g * N * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) +
    32 * c ^ (5:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) -
    8 * c ^ (5:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ)) +
    (32 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j -
    64 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j -
    96 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (3:ℕ) * j +
    32 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j +
    96 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j)) +
    ((-32 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j +
    48 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) -
    80 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ) -
    32 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (2:ℕ)) +
    (112 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) +
    48 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) -
    48 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) -
    32 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) +
    8 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ)))))))) * hj

/-- The pairing Y3 expanded (no relation used). -/
private def agY3raw {R : Type*} [CommRing R] (c d K g N σ w O j : R) : R :=
  (((((8 * c * g * w * O ^ (11:ℕ) * j ^ (11:ℕ) - 4 * c ^ (2:ℕ) * N ^ (2:ℕ) * O ^ (10:ℕ) * j ^ (10:ℕ)
    + 4 * c ^ (2:ℕ) * g * w * O ^ (10:ℕ) * j ^ (10:ℕ) + 4 * c * d * g * w * O ^ (10:ℕ) * j ^ (10:ℕ)
    + 32 * c * g * σ * w * O ^ (10:ℕ) * j ^ (10:ℕ) -
    20 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ * O ^ (9:ℕ) * j ^ (9:ℕ)) +
    (2 * c ^ (2:ℕ) * d * g * w * O ^ (9:ℕ) * j ^ (9:ℕ) +
    16 * c ^ (2:ℕ) * g * σ * w * O ^ (9:ℕ) * j ^ (9:ℕ) +
    16 * c * d * g * σ * w * O ^ (9:ℕ) * j ^ (9:ℕ) +
    32 * c * g * σ ^ (2:ℕ) * w * O ^ (9:ℕ) * j ^ (9:ℕ) +
    32 * c * g * w ^ (3:ℕ) * O ^ (9:ℕ) * j ^ (9:ℕ) -
    33 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (8:ℕ))) +
    ((8 * c ^ (2:ℕ) * d * g * σ * w * O ^ (8:ℕ) * j ^ (8:ℕ) +
    16 * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w * O ^ (8:ℕ) * j ^ (8:ℕ) +
    16 * c * d * g * σ ^ (2:ℕ) * w * O ^ (8:ℕ) * j ^ (8:ℕ) -
    32 * c * g * σ ^ (3:ℕ) * w * O ^ (8:ℕ) * j ^ (8:ℕ) -
    17 * c ^ (2:ℕ) * N ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (8:ℕ) +
    16 * c ^ (2:ℕ) * g * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (8:ℕ)) +
    (16 * c * d * g * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (8:ℕ) +
    96 * c * g * σ * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (8:ℕ) -
    4 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * O ^ (7:ℕ) * j ^ (7:ℕ) +
    8 * c ^ (2:ℕ) * d * g * σ ^ (2:ℕ) * w * O ^ (7:ℕ) * j ^ (7:ℕ) -
    16 * c ^ (2:ℕ) * g * σ ^ (3:ℕ) * w * O ^ (7:ℕ) * j ^ (7:ℕ) -
    16 * c * d * g * σ ^ (3:ℕ) * w * O ^ (7:ℕ) * j ^ (7:ℕ) -
    80 * c * g * σ ^ (4:ℕ) * w * O ^ (7:ℕ) * j ^ (7:ℕ)))) +
    (((-68 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ * w ^ (2:ℕ) * O ^ (7:ℕ) * j ^ (7:ℕ) +
    8 * c ^ (2:ℕ) * d * g * w ^ (3:ℕ) * O ^ (7:ℕ) * j ^ (7:ℕ) +
    48 * c ^ (2:ℕ) * g * σ * w ^ (3:ℕ) * O ^ (7:ℕ) * j ^ (7:ℕ) +
    48 * c * d * g * σ * w ^ (3:ℕ) * O ^ (7:ℕ) * j ^ (7:ℕ) +
    96 * c * g * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j ^ (7:ℕ) +
    48 * c * g * w ^ (5:ℕ) * O ^ (7:ℕ) * j ^ (7:ℕ)) +
    (-8 * c ^ (2:ℕ) * g * N * σ * O ^ (8:ℕ) * j ^ (8:ℕ) -
    c ^ (2:ℕ) * K * g * w * O ^ (8:ℕ) * j ^ (8:ℕ) +
    52 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ) -
    8 * c ^ (2:ℕ) * d * g * σ ^ (3:ℕ) * w * O ^ (6:ℕ) * j ^ (6:ℕ) -
    40 * c ^ (2:ℕ) * g * σ ^ (4:ℕ) * w * O ^ (6:ℕ) * j ^ (6:ℕ) -
    40 * c * d * g * σ ^ (4:ℕ) * w * O ^ (6:ℕ) * j ^ (6:ℕ) -
    32 * c * g * σ ^ (5:ℕ) * w * O ^ (6:ℕ) * j ^ (6:ℕ))) +
    ((-104 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ) +
    24 * c ^ (2:ℕ) * d * g * σ * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ) +
    48 * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ) +
    48 * c * d * g * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ) +
    64 * c * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ) -
    28 * c ^ (2:ℕ) * N ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ)) +
    (24 * c ^ (2:ℕ) * g * w ^ (5:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ) +
    24 * c * d * g * w ^ (5:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ) +
    96 * c * g * σ * w ^ (5:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ) -
    40 * c ^ (2:ℕ) * g * N * σ ^ (2:ℕ) * O ^ (7:ℕ) * j ^ (7:ℕ) -
    4 * c ^ (2:ℕ) * K * g * σ * w * O ^ (7:ℕ) * j ^ (7:ℕ) +
    9 * c ^ (2:ℕ) * g ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (8:ℕ) +
    60 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ))))) +
    ((((-20 * c ^ (2:ℕ) * d * g * σ ^ (4:ℕ) * w * O ^ (5:ℕ) * j ^ (5:ℕ) -
    16 * c ^ (2:ℕ) * g * σ ^ (5:ℕ) * w * O ^ (5:ℕ) * j ^ (5:ℕ) -
    16 * c * d * g * σ ^ (5:ℕ) * w * O ^ (5:ℕ) * j ^ (5:ℕ) +
    32 * c * g * σ ^ (6:ℕ) * w * O ^ (5:ℕ) * j ^ (5:ℕ) -
    88 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ) +
    24 * c ^ (2:ℕ) * d * g * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ)) +
    (32 * c ^ (2:ℕ) * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ) +
    32 * c * d * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ) +
    96 * c * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ) -
    84 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ * w ^ (4:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ) +
    12 * c ^ (2:ℕ) * d * g * w ^ (5:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ) +
    48 * c ^ (2:ℕ) * g * σ * w ^ (5:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ) +
    48 * c * d * g * σ * w ^ (5:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ))) +
    ((96 * c * g * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ) +
    32 * c * g * w ^ (7:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ) -
    74 * c ^ (2:ℕ) * g * N * σ ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ) -
    4 * c ^ (2:ℕ) * K * g * σ ^ (2:ℕ) * w * O ^ (6:ℕ) * j ^ (6:ℕ) -
    10 * c ^ (2:ℕ) * g * N * σ * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ) -
    4 * c ^ (2:ℕ) * K * g * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ)) +
    (36 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ * O ^ (7:ℕ) * j ^ (7:ℕ) +
    10 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (6:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) -
    8 * c ^ (2:ℕ) * d * g * σ ^ (5:ℕ) * w * O ^ (4:ℕ) * j ^ (4:ℕ) +
    16 * c ^ (2:ℕ) * g * σ ^ (6:ℕ) * w * O ^ (4:ℕ) * j ^ (4:ℕ) +
    16 * c * d * g * σ ^ (6:ℕ) * w * O ^ (4:ℕ) * j ^ (4:ℕ) +
    32 * c * g * σ ^ (7:ℕ) * w * O ^ (4:ℕ) * j ^ (4:ℕ) -
    82 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ)))) +
    (((16 * c ^ (2:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    48 * c ^ (2:ℕ) * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    48 * c * d * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    96 * c * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) -
    114 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    24 * c ^ (2:ℕ) * d * g * σ * w ^ (5:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ)) +
    (48 * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    48 * c * d * g * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    96 * c * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) -
    22 * c ^ (2:ℕ) * N ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    16 * c ^ (2:ℕ) * g * w ^ (7:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    16 * c * d * g * w ^ (7:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    32 * c * g * σ * w ^ (7:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ))) +
    ((-48 * c ^ (2:ℕ) * g * N * σ ^ (4:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ) +
    4 * c ^ (2:ℕ) * K * g * σ ^ (3:ℕ) * w * O ^ (5:ℕ) * j ^ (5:ℕ) -
    16 * c ^ (2:ℕ) * g * N * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ) -
    12 * c ^ (2:ℕ) * K * g * σ * w ^ (3:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ) +
    50 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ) +
    16 * c ^ (2:ℕ) * g ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (6:ℕ)) +
    (-28 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (7:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
    8 * c ^ (2:ℕ) * d * g * σ ^ (6:ℕ) * w * O ^ (3:ℕ) * j ^ (3:ℕ) +
    16 * c ^ (2:ℕ) * g * σ ^ (7:ℕ) * w * O ^ (3:ℕ) * j ^ (3:ℕ) +
    16 * c * d * g * σ ^ (7:ℕ) * w * O ^ (3:ℕ) * j ^ (3:ℕ) +
    8 * c * g * σ ^ (8:ℕ) * w * O ^ (3:ℕ) * j ^ (3:ℕ) -
    100 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
    24 * c ^ (2:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ)))))) +
    (((((48 * c ^ (2:ℕ) * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
    48 * c * d * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
    32 * c * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) -
    116 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
    24 * c ^ (2:ℕ) * d * g * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
    48 * c ^ (2:ℕ) * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ)) +
    (48 * c * d * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
    48 * c * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) -
    44 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ * w ^ (6:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
    8 * c ^ (2:ℕ) * d * g * w ^ (7:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
    16 * c ^ (2:ℕ) * g * σ * w ^ (7:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
    16 * c * d * g * σ * w ^ (7:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
    32 * c * g * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ))) +
    ((8 * c * g * w ^ (9:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
    30 * c ^ (2:ℕ) * g * N * σ ^ (5:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    10 * c ^ (2:ℕ) * K * g * σ ^ (4:ℕ) * w * O ^ (4:ℕ) * j ^ (4:ℕ) +
    36 * c ^ (2:ℕ) * g * N * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) -
    12 * c ^ (2:ℕ) * K * g * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    6 * c ^ (2:ℕ) * g * N * σ * w ^ (4:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ)) +
    (-6 * c ^ (2:ℕ) * K * g * w ^ (5:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    16 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ) +
    48 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ * w ^ (2:ℕ) * O ^ (5:ℕ) * j ^ (5:ℕ) -
    24 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (8:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    8 * c ^ (2:ℕ) * d * g * σ ^ (7:ℕ) * w * O ^ (2:ℕ) * j ^ (2:ℕ) +
    4 * c ^ (2:ℕ) * g * σ ^ (8:ℕ) * w * O ^ (2:ℕ) * j ^ (2:ℕ) +
    4 * c * d * g * σ ^ (8:ℕ) * w * O ^ (2:ℕ) * j ^ (2:ℕ)))) +
    (((-80 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    24 * c ^ (2:ℕ) * d * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    16 * c ^ (2:ℕ) * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    16 * c * d * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
    96 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    24 * c ^ (2:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ)) +
    (24 * c ^ (2:ℕ) * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    24 * c * d * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
    48 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    8 * c ^ (2:ℕ) * d * g * σ * w ^ (7:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    16 * c ^ (2:ℕ) * g * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    16 * c * d * g * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
    8 * c ^ (2:ℕ) * N ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ))) +
    ((4 * c ^ (2:ℕ) * g * w ^ (9:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    4 * c * d * g * w ^ (9:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    72 * c ^ (2:ℕ) * g * N * σ ^ (6:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
    4 * c ^ (2:ℕ) * K * g * σ ^ (5:ℕ) * w * O ^ (3:ℕ) * j ^ (3:ℕ) +
    112 * c ^ (2:ℕ) * g * N * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) -
    8 * c ^ (2:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ)) +
    (40 * c ^ (2:ℕ) * g * N * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) -
    12 * c ^ (2:ℕ) * K * g * σ * w ^ (5:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) -
    32 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (4:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    46 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) +
    6 * c ^ (2:ℕ) * g ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) * j ^ (4:ℕ) -
    8 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (9:ℕ) * O * j +
    2 * c ^ (2:ℕ) * d * g * σ ^ (8:ℕ) * w * O * j)))) +
    ((((-32 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * O * j +
    8 * c ^ (2:ℕ) * d * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O * j -
    48 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * O * j +
    12 * c ^ (2:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O * j -
    32 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * O * j +
    8 * c ^ (2:ℕ) * d * g * σ ^ (2:ℕ) * w ^ (7:ℕ) * O * j) +
    (-8 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ * w ^ (8:ℕ) * O * j + 2 * c ^ (2:ℕ) * d * g * w ^ (9:ℕ) * O * j
    + 50 * c ^ (2:ℕ) * g * N * σ ^ (7:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
    4 * c ^ (2:ℕ) * K * g * σ ^ (6:ℕ) * w * O ^ (2:ℕ) * j ^ (2:ℕ) +
    110 * c ^ (2:ℕ) * g * N * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
    12 * c ^ (2:ℕ) * K * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    70 * c ^ (2:ℕ) * g * N * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ))) +
    ((-12 * c ^ (2:ℕ) * K * g * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    10 * c ^ (2:ℕ) * g * N * σ * w ^ (6:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
    4 * c ^ (2:ℕ) * K * g * w ^ (7:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
    44 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (5:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) +
    12 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ * w ^ (4:ℕ) * O ^ (3:ℕ) * j ^ (3:ℕ) -
    c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (10:ℕ)) + (-5 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) -
    10 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) -
    10 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) -
    5 * c ^ (2:ℕ) * N ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) - c ^ (2:ℕ) * N ^ (2:ℕ) * w ^ (10:ℕ) +
    16 * c ^ (2:ℕ) * g * N * σ ^ (8:ℕ) * O * j - 4 * c ^ (2:ℕ) * K * g * σ ^ (7:ℕ) * w * O * j))) +
    (((48 * c ^ (2:ℕ) * g * N * σ ^ (6:ℕ) * w ^ (2:ℕ) * O * j -
    12 * c ^ (2:ℕ) * K * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O * j +
    48 * c ^ (2:ℕ) * g * N * σ ^ (4:ℕ) * w ^ (4:ℕ) * O * j -
    12 * c ^ (2:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O * j +
    16 * c ^ (2:ℕ) * g * N * σ ^ (2:ℕ) * w ^ (6:ℕ) * O * j -
    4 * c ^ (2:ℕ) * K * g * σ * w ^ (7:ℕ) * O * j) +
    (-26 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (6:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
    28 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) -
    2 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) * j ^ (2:ℕ) +
    2 * c ^ (2:ℕ) * g * N * σ ^ (9:ℕ) - c ^ (2:ℕ) * K * g * σ ^ (8:ℕ) * w +
    8 * c ^ (2:ℕ) * g * N * σ ^ (7:ℕ) * w ^ (2:ℕ) - 4 * c ^ (2:ℕ) * K * g * σ ^ (6:ℕ) * w ^ (3:ℕ)))
    + ((12 * c ^ (2:ℕ) * g * N * σ ^ (5:ℕ) * w ^ (4:ℕ) -
    6 * c ^ (2:ℕ) * K * g * σ ^ (4:ℕ) * w ^ (5:ℕ) + 8 * c ^ (2:ℕ) * g * N * σ ^ (3:ℕ) * w ^ (6:ℕ) -
    4 * c ^ (2:ℕ) * K * g * σ ^ (2:ℕ) * w ^ (7:ℕ) + 2 * c ^ (2:ℕ) * g * N * σ * w ^ (8:ℕ) -
    c ^ (2:ℕ) * K * g * w ^ (9:ℕ)) + (-8 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (7:ℕ) * O * j -
    16 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O * j -
    8 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O * j - c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (8:ℕ) -
    2 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) +
    2 * c ^ (2:ℕ) * g ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) + c ^ (2:ℕ) * g ^ (2:ℕ) * w ^ (8:ℕ))))))

@[tmio M, powerlib_domain] private theorem ag_Y3raw (c d K g N σ w O j : ℂ) :
    angleVecP c d g σ w (-O) j ⬝ᵥ AnglePattern.bilin c g N (angleVecQ d σ w (-O) j)
        (AnglePattern.solveShift c d K g σ w O j (AnglePattern.bilin c g N (angleVecQ d σ w O j)
            (angleVecQ d σ w O j))) =
      agY3raw c d K g N σ w O j := by
  simp only [angleVecP, angleVecQ, AnglePattern.bilin, AnglePattern.solveShift, agY3raw,
      dotProduct, Fin.sum_univ_five, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- `⟨p̃, B(q̄, s̄)⟩` reduced modulo the Hopf relations. Static algebra. -/
@[tmio M, powerlib_domain] theorem AnglePattern.shift_pairing {c d K g N σ w O j : ℂ}
    (hj : j ^ 2 = -1)
    (hK : 2 * σ * c * K = (d * c - O ^ 2) * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * (d + c) * O ^ 2)
    (hg : 2 * σ * c * w * g =
      (d * c - O ^ 2) * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2)) :
    (2 * σ * c) * (2 * σ * c * w) ^ 2
        * (angleVecP c d g σ w (-O) j ⬝ᵥ AnglePattern.bilin c g N (angleVecQ d σ w (-O) j)
        (AnglePattern.solveShift c d K g σ w O j (AnglePattern.bilin c g N (angleVecQ d σ w O j)
            (angleVecQ d σ w O j)))) =
      2 * σ * c ^ 3 * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2) * ((σ ^ 2 + w ^ 2 - O ^ 2)
          + 2 * σ * O * j) * (AngleKey.shiftRe c d N σ w O + AngleKey.shiftIm c d N σ w O * j) := by
  rw [ag_Y3raw]
  simp only [agY3raw, AngleKey.shiftRe, AngleKey.shiftIm]
  linear_combination (((-16 * c ^ (4:ℕ) * g * σ ^ (9:ℕ) * w ^ (3:ℕ) * O * j -
    48 * c ^ (4:ℕ) * g * σ ^ (7:ℕ) * w ^ (5:ℕ) * O * j -
    48 * c ^ (4:ℕ) * g * σ ^ (5:ℕ) * w ^ (7:ℕ) * O * j -
    16 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (9:ℕ) * O * j -
    16 * c ^ (4:ℕ) * g * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j +
    32 * c ^ (4:ℕ) * g * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j) +
    (48 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (3:ℕ) * j +
    16 * c ^ (4:ℕ) * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j -
    48 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j +
    16 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j -
    4 * c ^ (4:ℕ) * g * σ ^ (10:ℕ) * w ^ (3:ℕ) - 16 * c ^ (4:ℕ) * g * σ ^ (8:ℕ) * w ^ (5:ℕ))) +
    ((-24 * c ^ (4:ℕ) * g * σ ^ (6:ℕ) * w ^ (7:ℕ) - 16 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (9:ℕ) -
    4 * c ^ (4:ℕ) * g * σ ^ (2:ℕ) * w ^ (11:ℕ) +
    16 * c ^ (4:ℕ) * g * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) +
    48 * c ^ (4:ℕ) * g * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) +
    48 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ)) +
    (16 * c ^ (4:ℕ) * g * σ ^ (2:ℕ) * w ^ (9:ℕ) * O ^ (2:ℕ) +
    40 * c ^ (4:ℕ) * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) -
    48 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) -
    24 * c ^ (4:ℕ) * g * σ ^ (2:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) +
    16 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) +
    16 * c ^ (4:ℕ) * g * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) -
    4 * c ^ (4:ℕ) * g * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ)))) * hK +
    ((((((-16 * c ^ (4:ℕ) * d * σ ^ (12:ℕ) * O * j -
    64 * c ^ (4:ℕ) * d * σ ^ (10:ℕ) * w ^ (2:ℕ) * O * j -
    96 * c ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (4:ℕ) * O * j -
    64 * c ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (6:ℕ) * O * j -
    16 * c ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (8:ℕ) * O * j) +
    (56 * c ^ (4:ℕ) * d * σ ^ (10:ℕ) * O ^ (3:ℕ) * j + 16 * c ^ (3:ℕ) * σ ^ (12:ℕ) * O ^ (3:ℕ) * j +
    112 * c ^ (4:ℕ) * d * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j -
    48 * c ^ (4:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j -
    48 * c ^ (3:ℕ) * d * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j +
    40 * c ^ (3:ℕ) * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j)) +
    ((32 * c ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j -
    144 * c ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j -
    144 * c ^ (3:ℕ) * d * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j -
    48 * c ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (3:ℕ) * j -
    144 * c ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (3:ℕ) * j -
    144 * c ^ (3:ℕ) * d * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (3:ℕ) * j) +
    (-80 * c ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (3:ℕ) * j -
    24 * c ^ (4:ℕ) * d * σ ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (3:ℕ) * j -
    48 * c ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (3:ℕ) * j -
    48 * c ^ (3:ℕ) * d * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (3:ℕ) * j -
    80 * c ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (3:ℕ) * j -
    24 * c ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (10:ℕ) * O ^ (3:ℕ) * j))) +
    (((192 * c ^ (4:ℕ) * d * σ ^ (8:ℕ) * O ^ (5:ℕ) * j - 56 * c ^ (3:ℕ) * σ ^ (10:ℕ) * O ^ (5:ℕ) * j
    - 112 * c ^ (4:ℕ) * d * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j -
    48 * c ^ (4:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j -
    48 * c ^ (3:ℕ) * d * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j -
    16 * c ^ (3:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j) +
    (224 * c ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j +
    96 * c ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j +
    96 * c ^ (3:ℕ) * d * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j +
    256 * c ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j +
    144 * c ^ (4:ℕ) * d * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (5:ℕ) * j +
    144 * c ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (5:ℕ) * j)) +
    ((144 * c ^ (3:ℕ) * d * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (5:ℕ) * j +
    336 * c ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (5:ℕ) * j +
    120 * c ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (5:ℕ) * j +
    80 * c ^ (4:ℕ) * d * σ ^ (6:ℕ) * O ^ (7:ℕ) * j - 192 * c ^ (3:ℕ) * σ ^ (8:ℕ) * O ^ (7:ℕ) * j -
    48 * c ^ (4:ℕ) * d * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j) +
    (48 * c ^ (4:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j +
    48 * c ^ (3:ℕ) * d * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j +
    352 * c ^ (3:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j -
    288 * c ^ (4:ℕ) * d * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j -
    144 * c ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j -
    144 * c ^ (3:ℕ) * d * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j)))) +
    ((((-512 * c ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j -
    288 * c ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (7:ℕ) * j -
    112 * c ^ (4:ℕ) * d * σ ^ (4:ℕ) * O ^ (9:ℕ) * j - 80 * c ^ (3:ℕ) * σ ^ (6:ℕ) * O ^ (9:ℕ) * j +
    240 * c ^ (4:ℕ) * d * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j +
    48 * c ^ (4:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j) +
    (48 * c ^ (3:ℕ) * d * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j +
    144 * c ^ (3:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j +
    384 * c ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (9:ℕ) * j -
    72 * c ^ (4:ℕ) * d * σ ^ (2:ℕ) * O ^ (11:ℕ) * j + 112 * c ^ (3:ℕ) * σ ^ (4:ℕ) * O ^ (11:ℕ) * j -
    264 * c ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (11:ℕ) * j)) +
    ((72 * c ^ (3:ℕ) * σ ^ (2:ℕ) * O ^ (13:ℕ) * j - 2 * c ^ (4:ℕ) * d * σ ^ (13:ℕ) -
    10 * c ^ (4:ℕ) * d * σ ^ (11:ℕ) * w ^ (2:ℕ) - 20 * c ^ (4:ℕ) * d * σ ^ (9:ℕ) * w ^ (4:ℕ) -
    20 * c ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (6:ℕ) - 10 * c ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (8:ℕ)) +
    (-2 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (10:ℕ) + 48 * c ^ (4:ℕ) * d * σ ^ (11:ℕ) * O ^ (2:ℕ) +
    2 * c ^ (3:ℕ) * σ ^ (13:ℕ) * O ^ (2:ℕ) + 134 * c ^ (4:ℕ) * d * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ)
    - 12 * c ^ (4:ℕ) * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) -
    12 * c ^ (3:ℕ) * d * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ)))) +
    (((10 * c ^ (3:ℕ) * σ ^ (11:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) +
    120 * c ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) -
    48 * c ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) -
    48 * c ^ (3:ℕ) * d * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) +
    20 * c ^ (3:ℕ) * σ ^ (9:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) +
    36 * c ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ)) +
    (-72 * c ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ) -
    72 * c ^ (3:ℕ) * d * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ) +
    20 * c ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ) +
    8 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (2:ℕ) -
    48 * c ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (2:ℕ) -
    48 * c ^ (3:ℕ) * d * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (2:ℕ))) +
    ((10 * c ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (8:ℕ) * O ^ (2:ℕ) +
    6 * c ^ (4:ℕ) * d * σ * w ^ (10:ℕ) * O ^ (2:ℕ) -
    12 * c ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (10:ℕ) * O ^ (2:ℕ) -
    12 * c ^ (3:ℕ) * d * σ ^ (2:ℕ) * w ^ (10:ℕ) * O ^ (2:ℕ) +
    2 * c ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (10:ℕ) * O ^ (2:ℕ) + 38 * c ^ (4:ℕ) * d * σ ^ (9:ℕ) * O ^ (4:ℕ))
    + (-48 * c ^ (3:ℕ) * σ ^ (11:ℕ) * O ^ (4:ℕ) -
    52 * c ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) +
    48 * c ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) +
    48 * c ^ (3:ℕ) * d * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) -
    38 * c ^ (3:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) +
    64 * c ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ)))))) +
    (((((144 * c ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) +
    144 * c ^ (3:ℕ) * d * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) +
    168 * c ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) +
    148 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) +
    144 * c ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ)) +
    (144 * c ^ (3:ℕ) * d * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) +
    252 * c ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) -
    6 * c ^ (4:ℕ) * d * σ * w ^ (8:ℕ) * O ^ (4:ℕ) +
    48 * c ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) +
    48 * c ^ (3:ℕ) * d * σ ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) +
    88 * c ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ))) +
    ((-6 * c ^ (3:ℕ) * σ * w ^ (10:ℕ) * O ^ (4:ℕ) - 176 * c ^ (4:ℕ) * d * σ ^ (7:ℕ) * O ^ (6:ℕ) -
    38 * c ^ (3:ℕ) * σ ^ (9:ℕ) * O ^ (6:ℕ) + 156 * c ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ)
    + 120 * c ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) +
    120 * c ^ (3:ℕ) * d * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ)) +
    (148 * c ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) -
    376 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) -
    144 * c ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) -
    144 * c ^ (3:ℕ) * d * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) -
    256 * c ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) -
    36 * c ^ (4:ℕ) * d * σ * w ^ (6:ℕ) * O ^ (6:ℕ)))) +
    (((-72 * c ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) -
    72 * c ^ (3:ℕ) * d * σ ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) -
    436 * c ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) + 6 * c ^ (3:ℕ) * σ * w ^ (8:ℕ) * O ^ (6:ℕ)
    - 246 * c ^ (4:ℕ) * d * σ ^ (5:ℕ) * O ^ (8:ℕ) + 176 * c ^ (3:ℕ) * σ ^ (7:ℕ) * O ^ (8:ℕ)) +
    (286 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) +
    48 * c ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) +
    48 * c ^ (3:ℕ) * d * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) -
    252 * c ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) +
    84 * c ^ (4:ℕ) * d * σ * w ^ (4:ℕ) * O ^ (8:ℕ) +
    48 * c ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ))) +
    ((48 * c ^ (3:ℕ) * d * σ ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) +
    664 * c ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) + 36 * c ^ (3:ℕ) * σ * w ^ (6:ℕ) * O ^ (8:ℕ)
    - 64 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * O ^ (10:ℕ) + 246 * c ^ (3:ℕ) * σ ^ (5:ℕ) * O ^ (10:ℕ) -
    66 * c ^ (4:ℕ) * d * σ * w ^ (2:ℕ) * O ^ (10:ℕ)) +
    (-12 * c ^ (4:ℕ) * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) -
    12 * c ^ (3:ℕ) * d * σ ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) -
    382 * c ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) -
    84 * c ^ (3:ℕ) * σ * w ^ (4:ℕ) * O ^ (10:ℕ) + 18 * c ^ (4:ℕ) * d * σ * O ^ (12:ℕ) +
    64 * c ^ (3:ℕ) * σ ^ (3:ℕ) * O ^ (12:ℕ))))) + ((((66 * c ^ (3:ℕ) * σ * w ^ (2:ℕ) * O ^ (12:ℕ) -
    18 * c ^ (3:ℕ) * σ * O ^ (14:ℕ) + 64 * c ^ (4:ℕ) * N * σ ^ (10:ℕ) * w * O * j +
    192 * c ^ (4:ℕ) * N * σ ^ (8:ℕ) * w ^ (3:ℕ) * O * j +
    192 * c ^ (4:ℕ) * N * σ ^ (6:ℕ) * w ^ (5:ℕ) * O * j +
    64 * c ^ (4:ℕ) * N * σ ^ (4:ℕ) * w ^ (7:ℕ) * O * j) +
    (-288 * c ^ (4:ℕ) * N * σ ^ (8:ℕ) * w * O ^ (3:ℕ) * j -
    448 * c ^ (4:ℕ) * N * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j -
    160 * c ^ (4:ℕ) * N * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j -
    192 * c ^ (4:ℕ) * N * σ ^ (6:ℕ) * w * O ^ (5:ℕ) * j -
    64 * c ^ (4:ℕ) * N * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j +
    160 * c ^ (4:ℕ) * N * σ ^ (4:ℕ) * w * O ^ (7:ℕ) * j)) + ((8 * c ^ (4:ℕ) * N * σ ^ (11:ℕ) * w +
    32 * c ^ (4:ℕ) * N * σ ^ (9:ℕ) * w ^ (3:ℕ) + 48 * c ^ (4:ℕ) * N * σ ^ (7:ℕ) * w ^ (5:ℕ) +
    32 * c ^ (4:ℕ) * N * σ ^ (5:ℕ) * w ^ (7:ℕ) + 8 * c ^ (4:ℕ) * N * σ ^ (3:ℕ) * w ^ (9:ℕ) -
    200 * c ^ (4:ℕ) * N * σ ^ (9:ℕ) * w * O ^ (2:ℕ)) +
    (-440 * c ^ (4:ℕ) * N * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) -
    280 * c ^ (4:ℕ) * N * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) -
    40 * c ^ (4:ℕ) * N * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ) +
    120 * c ^ (4:ℕ) * N * σ ^ (7:ℕ) * w * O ^ (4:ℕ) +
    144 * c ^ (4:ℕ) * N * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) +
    24 * c ^ (4:ℕ) * N * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ)))) +
    (((296 * c ^ (4:ℕ) * N * σ ^ (5:ℕ) * w * O ^ (6:ℕ) +
    40 * c ^ (4:ℕ) * N * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) -
    32 * c ^ (4:ℕ) * N * σ ^ (3:ℕ) * w * O ^ (8:ℕ) - 32 * c ^ (4:ℕ) * g * σ ^ (9:ℕ) * w * O * j -
    64 * c ^ (4:ℕ) * g * σ ^ (7:ℕ) * w ^ (3:ℕ) * O * j -
    32 * c ^ (4:ℕ) * g * σ ^ (5:ℕ) * w ^ (5:ℕ) * O * j) +
    (176 * c ^ (4:ℕ) * g * σ ^ (7:ℕ) * w * O ^ (3:ℕ) * j -
    48 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j +
    64 * c ^ (4:ℕ) * g * σ ^ (5:ℕ) * w * O ^ (5:ℕ) * j +
    192 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j -
    144 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w * O ^ (7:ℕ) * j - 4 * c ^ (4:ℕ) * g * σ ^ (10:ℕ) * w)) +
    ((-8 * c ^ (4:ℕ) * g * σ ^ (8:ℕ) * w ^ (3:ℕ) + 8 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (7:ℕ) +
    4 * c ^ (4:ℕ) * g * σ ^ (2:ℕ) * w ^ (9:ℕ) + 104 * c ^ (4:ℕ) * g * σ ^ (8:ℕ) * w * O ^ (2:ℕ) +
    112 * c ^ (4:ℕ) * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) +
    8 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ)) +
    (-128 * c ^ (4:ℕ) * g * σ ^ (6:ℕ) * w * O ^ (4:ℕ) +
    184 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) +
    24 * c ^ (4:ℕ) * g * σ ^ (2:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) -
    200 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w * O ^ (6:ℕ) -
    64 * c ^ (4:ℕ) * g * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) +
    36 * c ^ (4:ℕ) * g * σ ^ (2:ℕ) * w * O ^ (8:ℕ))))))) * hg +
    (((((((64 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) * j ^ (9:ℕ) -
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) * j ^ (8:ℕ) +
    32 * c ^ (5:ℕ) * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) * j ^ (8:ℕ) +
    32 * c ^ (4:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) * j ^ (8:ℕ) +
    256 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) * j ^ (8:ℕ) -
    160 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j ^ (7:ℕ) +
    16 * c ^ (5:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j ^ (7:ℕ) +
    128 * c ^ (5:ℕ) * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j ^ (7:ℕ)) +
    (128 * c ^ (4:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j ^ (7:ℕ) +
    256 * c ^ (4:ℕ) * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j ^ (7:ℕ) +
    256 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) * j ^ (7:ℕ) -
    64 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) * j ^ (7:ℕ) -
    264 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) +
    64 * c ^ (5:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) +
    128 * c ^ (5:ℕ) * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) +
    128 * c ^ (4:ℕ) * d * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ))) +
    ((-256 * c ^ (4:ℕ) * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) -
    136 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) +
    128 * c ^ (5:ℕ) * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) +
    128 * c ^ (4:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) +
    768 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) +
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) * j ^ (6:ℕ) -
    32 * c ^ (5:ℕ) * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) * j ^ (6:ℕ) -
    32 * c ^ (4:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) * j ^ (6:ℕ)) +
    (-256 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) * j ^ (6:ℕ) -
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j ^ (5:ℕ) +
    64 * c ^ (5:ℕ) * d * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j ^ (5:ℕ) -
    128 * c ^ (5:ℕ) * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j ^ (5:ℕ) -
    128 * c ^ (4:ℕ) * d * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j ^ (5:ℕ) -
    640 * c ^ (4:ℕ) * g * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j ^ (5:ℕ) -
    544 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j ^ (5:ℕ) +
    64 * c ^ (5:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j ^ (5:ℕ)))) +
    (((384 * c ^ (5:ℕ) * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j ^ (5:ℕ) +
    384 * c ^ (4:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j ^ (5:ℕ) +
    768 * c ^ (4:ℕ) * g * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j ^ (5:ℕ) +
    384 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ) * j ^ (5:ℕ) +
    160 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j ^ (5:ℕ) -
    16 * c ^ (5:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j ^ (5:ℕ) -
    128 * c ^ (5:ℕ) * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j ^ (5:ℕ) -
    128 * c ^ (4:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j ^ (5:ℕ)) +
    (-256 * c ^ (4:ℕ) * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j ^ (5:ℕ) -
    256 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) * j ^ (5:ℕ) +
    64 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) * j ^ (5:ℕ) -
    64 * c ^ (5:ℕ) * g * N * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) -
    8 * c ^ (5:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) +
    416 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) -
    64 * c ^ (5:ℕ) * d * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) -
    320 * c ^ (5:ℕ) * g * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ))) +
    ((-320 * c ^ (4:ℕ) * d * g * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) -
    256 * c ^ (4:ℕ) * g * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) -
    832 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) +
    192 * c ^ (5:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) +
    384 * c ^ (5:ℕ) * g * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) +
    384 * c ^ (4:ℕ) * d * g * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) +
    512 * c ^ (4:ℕ) * g * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) -
    224 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ)) +
    ((192 * c ^ (5:ℕ) * g * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) +
    192 * c ^ (4:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) +
    768 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) +
    264 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ)) +
    (-64 * c ^ (5:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ) -
    128 * c ^ (5:ℕ) * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ) -
    128 * c ^ (4:ℕ) * d * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ) +
    256 * c ^ (4:ℕ) * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ) +
    136 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ)))))) +
    ((((-128 * c ^ (5:ℕ) * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ) -
    128 * c ^ (4:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ) -
    768 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ) -
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) * j ^ (4:ℕ) +
    32 * c ^ (5:ℕ) * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) * j ^ (4:ℕ) +
    32 * c ^ (4:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) * j ^ (4:ℕ) +
    256 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) * j ^ (4:ℕ) -
    320 * c ^ (5:ℕ) * g * N * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j ^ (5:ℕ)) +
    (-32 * c ^ (5:ℕ) * K * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j ^ (5:ℕ) +
    72 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) +
    480 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) -
    160 * c ^ (5:ℕ) * d * g * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) -
    128 * c ^ (5:ℕ) * g * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) -
    128 * c ^ (4:ℕ) * d * g * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) +
    256 * c ^ (4:ℕ) * g * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) -
    704 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ))) +
    ((192 * c ^ (5:ℕ) * d * g * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) +
    256 * c ^ (5:ℕ) * g * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) +
    256 * c ^ (4:ℕ) * d * g * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) +
    768 * c ^ (4:ℕ) * g * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) -
    672 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) +
    96 * c ^ (5:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) +
    384 * c ^ (5:ℕ) * g * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) +
    384 * c ^ (4:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ)) +
    ((768 * c ^ (4:ℕ) * g * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) +
    256 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) +
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ) -
    64 * c ^ (5:ℕ) * d * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ)) +
    (128 * c ^ (5:ℕ) * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ) +
    128 * c ^ (4:ℕ) * d * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ) +
    640 * c ^ (4:ℕ) * g * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ) +
    544 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ) -
    64 * c ^ (5:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ))))) +
    (((-384 * c ^ (5:ℕ) * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ) -
    384 * c ^ (4:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ) -
    768 * c ^ (4:ℕ) * g * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ) -
    384 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ) -
    160 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j ^ (3:ℕ) +
    16 * c ^ (5:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j ^ (3:ℕ) +
    128 * c ^ (5:ℕ) * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j ^ (3:ℕ) +
    128 * c ^ (4:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j ^ (3:ℕ)) +
    (256 * c ^ (4:ℕ) * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j ^ (3:ℕ) +
    256 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) * j ^ (3:ℕ) -
    64 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) * j ^ (3:ℕ) -
    592 * c ^ (5:ℕ) * g * N * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) -
    32 * c ^ (5:ℕ) * K * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) -
    80 * c ^ (5:ℕ) * g * N * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) -
    32 * c ^ (5:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) +
    64 * c ^ (5:ℕ) * g * N * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ))) +
    ((8 * c ^ (5:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ) +
    288 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j ^ (5:ℕ) +
    24 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (15:ℕ) * O ^ (2:ℕ) +
    120 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (13:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) +
    240 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (11:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) +
    240 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ) +
    120 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (8:ℕ) * O ^ (2:ℕ) +
    24 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (10:ℕ) * O ^ (2:ℕ)) +
    ((48 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (13:ℕ) * O ^ (4:ℕ) -
    48 * c ^ (4:ℕ) * d * σ ^ (15:ℕ) * O ^ (4:ℕ) +
    72 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (11:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) +
    48 * c ^ (5:ℕ) * d * σ ^ (12:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ)) +
    (48 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (12:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) -
    192 * c ^ (4:ℕ) * d * σ ^ (13:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) +
    192 * c ^ (5:ℕ) * d * σ ^ (10:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) +
    192 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (10:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) -
    240 * c ^ (4:ℕ) * d * σ ^ (11:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ))))))) +
    (((((48 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) +
    288 * c ^ (5:ℕ) * d * σ ^ (8:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) +
    288 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) +
    144 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) +
    192 * c ^ (5:ℕ) * d * σ ^ (6:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) +
    192 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) +
    240 * c ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) +
    72 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (10:ℕ) * O ^ (4:ℕ)) +
    (48 * c ^ (5:ℕ) * d * σ ^ (4:ℕ) * w ^ (10:ℕ) * O ^ (4:ℕ) +
    48 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (10:ℕ) * O ^ (4:ℕ) +
    192 * c ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (10:ℕ) * O ^ (4:ℕ) +
    48 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (12:ℕ) * O ^ (4:ℕ) -
    120 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (11:ℕ) * O ^ (6:ℕ) -
    96 * c ^ (4:ℕ) * d * σ ^ (13:ℕ) * O ^ (6:ℕ) + 24 * c ^ (3:ℕ) * σ ^ (15:ℕ) * O ^ (6:ℕ) -
    144 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ))) +
    ((192 * c ^ (5:ℕ) * d * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) +
    192 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) -
    48 * c ^ (4:ℕ) * σ ^ (12:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) -
    48 * c ^ (3:ℕ) * d * σ ^ (12:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) +
    72 * c ^ (3:ℕ) * σ ^ (13:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) +
    96 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) +
    192 * c ^ (5:ℕ) * d * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) +
    192 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ)) +
    ((192 * c ^ (4:ℕ) * d * σ ^ (9:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) -
    192 * c ^ (4:ℕ) * σ ^ (10:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) -
    192 * c ^ (3:ℕ) * d * σ ^ (10:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) -
    240 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ)) +
    (-192 * c ^ (5:ℕ) * d * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) -
    192 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) -
    384 * c ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) -
    288 * c ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) -
    288 * c ^ (3:ℕ) * d * σ ^ (8:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ))))) +
    (((-240 * c ^ (3:ℕ) * σ ^ (9:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) -
    360 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (6:ℕ) -
    192 * c ^ (5:ℕ) * d * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (6:ℕ) -
    192 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (6:ℕ) -
    864 * c ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (8:ℕ) * O ^ (6:ℕ) -
    192 * c ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (8:ℕ) * O ^ (6:ℕ) -
    192 * c ^ (3:ℕ) * d * σ ^ (6:ℕ) * w ^ (8:ℕ) * O ^ (6:ℕ) -
    360 * c ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (8:ℕ) * O ^ (6:ℕ)) +
    (-384 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (10:ℕ) * O ^ (6:ℕ) -
    48 * c ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (10:ℕ) * O ^ (6:ℕ) -
    48 * c ^ (3:ℕ) * d * σ ^ (4:ℕ) * w ^ (10:ℕ) * O ^ (6:ℕ) -
    216 * c ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (10:ℕ) * O ^ (6:ℕ) -
    48 * c ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (12:ℕ) * O ^ (6:ℕ) -
    480 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (9:ℕ) * O ^ (8:ℕ) +
    240 * c ^ (4:ℕ) * d * σ ^ (11:ℕ) * O ^ (8:ℕ) + 48 * c ^ (3:ℕ) * σ ^ (13:ℕ) * O ^ (8:ℕ))) +
    ((336 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) +
    288 * c ^ (5:ℕ) * d * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) +
    288 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) +
    384 * c ^ (4:ℕ) * d * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) -
    192 * c ^ (4:ℕ) * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) -
    192 * c ^ (3:ℕ) * d * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) -
    72 * c ^ (3:ℕ) * σ ^ (11:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) -
    384 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ)) +
    ((-192 * c ^ (5:ℕ) * d * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) -
    192 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) -
    288 * c ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) -
    192 * c ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ)) +
    (-192 * c ^ (3:ℕ) * d * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) -
    192 * c ^ (3:ℕ) * σ ^ (9:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) +
    720 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ) +
    288 * c ^ (5:ℕ) * d * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ) +
    288 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ)))))) +
    ((((768 * c ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ) +
    192 * c ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ) +
    192 * c ^ (3:ℕ) * d * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ) +
    336 * c ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ) +
    1200 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (8:ℕ) +
    192 * c ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (8:ℕ) +
    192 * c ^ (3:ℕ) * d * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (8:ℕ) +
    720 * c ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (8:ℕ) * O ^ (8:ℕ)) +
    (312 * c ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (10:ℕ) * O ^ (8:ℕ) -
    600 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (7:ℕ) * O ^ (10:ℕ) +
    960 * c ^ (4:ℕ) * d * σ ^ (9:ℕ) * O ^ (10:ℕ) - 120 * c ^ (3:ℕ) * σ ^ (11:ℕ) * O ^ (10:ℕ) +
    792 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) +
    192 * c ^ (5:ℕ) * d * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) +
    192 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) -
    768 * c ^ (4:ℕ) * d * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ))) +
    ((-288 * c ^ (4:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) -
    288 * c ^ (3:ℕ) * d * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) -
    240 * c ^ (3:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) -
    720 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ) -
    192 * c ^ (5:ℕ) * d * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ) -
    192 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ) +
    960 * c ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ) +
    192 * c ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ)) +
    ((192 * c ^ (3:ℕ) * d * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ) +
    192 * c ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ) -
    1920 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (10:ℕ) -
    288 * c ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (10:ℕ)) +
    (-288 * c ^ (3:ℕ) * d * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (10:ℕ) -
    528 * c ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (10:ℕ) -
    840 * c ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (10:ℕ) -
    336 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (5:ℕ) * O ^ (12:ℕ) +
    1200 * c ^ (4:ℕ) * d * σ ^ (7:ℕ) * O ^ (12:ℕ))))) + (((-480 * c ^ (3:ℕ) * σ ^ (9:ℕ) * O ^ (12:ℕ)
    + 360 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ) +
    48 * c ^ (5:ℕ) * d * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ) +
    48 * c ^ (4:ℕ) * d ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ) -
    1728 * c ^ (4:ℕ) * d * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ) -
    192 * c ^ (4:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ) -
    192 * c ^ (3:ℕ) * d * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ) +
    432 * c ^ (3:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ)) +
    (1680 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (12:ℕ) +
    192 * c ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (12:ℕ) +
    192 * c ^ (3:ℕ) * d * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (12:ℕ) -
    576 * c ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (12:ℕ) +
    1200 * c ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (12:ℕ) -
    72 * c ^ (5:ℕ) * d ^ (2:ℕ) * σ ^ (3:ℕ) * O ^ (14:ℕ) +
    672 * c ^ (4:ℕ) * d * σ ^ (5:ℕ) * O ^ (14:ℕ) - 600 * c ^ (3:ℕ) * σ ^ (7:ℕ) * O ^ (14:ℕ))) +
    ((-768 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (14:ℕ) -
    48 * c ^ (4:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (14:ℕ) -
    48 * c ^ (3:ℕ) * d * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (14:ℕ) +
    936 * c ^ (3:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (14:ℕ) -
    960 * c ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (14:ℕ) +
    144 * c ^ (4:ℕ) * d * σ ^ (3:ℕ) * O ^ (16:ℕ) - 336 * c ^ (3:ℕ) * σ ^ (5:ℕ) * O ^ (16:ℕ) +
    408 * c ^ (3:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (16:ℕ)) +
    ((-72 * c ^ (3:ℕ) * σ ^ (3:ℕ) * O ^ (18:ℕ) +
    80 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) -
    64 * c ^ (5:ℕ) * d * g * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    128 * c ^ (5:ℕ) * g * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ)) +
    (128 * c ^ (4:ℕ) * d * g * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    256 * c ^ (4:ℕ) * g * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) -
    656 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    128 * c ^ (5:ℕ) * d * g * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    384 * c ^ (5:ℕ) * g * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ)))))))) +
    ((((((384 * c ^ (4:ℕ) * d * g * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    768 * c ^ (4:ℕ) * g * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) -
    912 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    192 * c ^ (5:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    384 * c ^ (5:ℕ) * g * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    384 * c ^ (4:ℕ) * d * g * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    768 * c ^ (4:ℕ) * g * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) -
    176 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ)) +
    (128 * c ^ (5:ℕ) * g * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    128 * c ^ (4:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    256 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) -
    416 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) +
    64 * c ^ (5:ℕ) * d * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) +
    320 * c ^ (5:ℕ) * g * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) +
    320 * c ^ (4:ℕ) * d * g * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) +
    256 * c ^ (4:ℕ) * g * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ))) +
    ((832 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) -
    192 * c ^ (5:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) -
    384 * c ^ (5:ℕ) * g * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) -
    384 * c ^ (4:ℕ) * d * g * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) -
    512 * c ^ (4:ℕ) * g * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) +
    224 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) -
    192 * c ^ (5:ℕ) * g * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) -
    192 * c ^ (4:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ)) +
    ((-768 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) -
    264 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ) +
    64 * c ^ (5:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ) +
    128 * c ^ (5:ℕ) * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ)) +
    (128 * c ^ (4:ℕ) * d * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ) -
    256 * c ^ (4:ℕ) * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ) -
    136 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ) +
    128 * c ^ (5:ℕ) * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ) +
    128 * c ^ (4:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ))))) +
    (((768 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ) +
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) * j ^ (2:ℕ) -
    32 * c ^ (5:ℕ) * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) * j ^ (2:ℕ) -
    32 * c ^ (4:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) * j ^ (2:ℕ) -
    256 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) * j ^ (2:ℕ) -
    384 * c ^ (5:ℕ) * g * N * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) +
    32 * c ^ (5:ℕ) * K * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) -
    128 * c ^ (5:ℕ) * g * N * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ)) +
    (-96 * c ^ (5:ℕ) * K * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) +
    320 * c ^ (5:ℕ) * g * N * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ) +
    32 * c ^ (5:ℕ) * K * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ) +
    400 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) +
    128 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) -
    72 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ) -
    96 * c ^ (5:ℕ) * d * N * σ ^ (13:ℕ) * w * O ^ (2:ℕ) -
    384 * c ^ (5:ℕ) * d * N * σ ^ (11:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ))) +
    ((-576 * c ^ (5:ℕ) * d * N * σ ^ (9:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) -
    384 * c ^ (5:ℕ) * d * N * σ ^ (7:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ) -
    96 * c ^ (5:ℕ) * d * N * σ ^ (5:ℕ) * w ^ (9:ℕ) * O ^ (2:ℕ) -
    96 * c ^ (5:ℕ) * d * N * σ ^ (11:ℕ) * w * O ^ (4:ℕ) +
    96 * c ^ (4:ℕ) * N * σ ^ (13:ℕ) * w * O ^ (4:ℕ) +
    96 * c ^ (5:ℕ) * d * N * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) +
    384 * c ^ (4:ℕ) * N * σ ^ (11:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) +
    480 * c ^ (5:ℕ) * d * N * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ)) +
    ((576 * c ^ (4:ℕ) * N * σ ^ (9:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) +
    288 * c ^ (5:ℕ) * d * N * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) +
    384 * c ^ (4:ℕ) * N * σ ^ (7:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) +
    96 * c ^ (4:ℕ) * N * σ ^ (5:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ)) +
    (288 * c ^ (5:ℕ) * d * N * σ ^ (9:ℕ) * w * O ^ (6:ℕ) +
    96 * c ^ (4:ℕ) * N * σ ^ (11:ℕ) * w * O ^ (6:ℕ) +
    192 * c ^ (5:ℕ) * d * N * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) -
    96 * c ^ (4:ℕ) * N * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) -
    96 * c ^ (5:ℕ) * d * N * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ)))))) +
    ((((-480 * c ^ (4:ℕ) * N * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) -
    288 * c ^ (4:ℕ) * N * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) +
    480 * c ^ (5:ℕ) * d * N * σ ^ (7:ℕ) * w * O ^ (8:ℕ) -
    288 * c ^ (4:ℕ) * N * σ ^ (9:ℕ) * w * O ^ (8:ℕ) -
    288 * c ^ (5:ℕ) * d * N * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) -
    192 * c ^ (4:ℕ) * N * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) +
    96 * c ^ (4:ℕ) * N * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) +
    192 * c ^ (5:ℕ) * d * N * σ ^ (5:ℕ) * w * O ^ (10:ℕ)) +
    (-480 * c ^ (4:ℕ) * N * σ ^ (7:ℕ) * w * O ^ (10:ℕ) +
    288 * c ^ (4:ℕ) * N * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) -
    192 * c ^ (4:ℕ) * N * σ ^ (5:ℕ) * w * O ^ (12:ℕ) -
    224 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j +
    64 * c ^ (5:ℕ) * d * g * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j +
    128 * c ^ (5:ℕ) * g * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j +
    128 * c ^ (4:ℕ) * d * g * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j +
    64 * c ^ (4:ℕ) * g * σ ^ (11:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j)) +
    ((-800 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j +
    192 * c ^ (5:ℕ) * d * g * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j +
    384 * c ^ (5:ℕ) * g * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j +
    384 * c ^ (4:ℕ) * d * g * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j +
    256 * c ^ (4:ℕ) * g * σ ^ (9:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j -
    928 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (3:ℕ) * j +
    192 * c ^ (5:ℕ) * d * g * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (3:ℕ) * j +
    384 * c ^ (5:ℕ) * g * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (3:ℕ) * j) +
    ((384 * c ^ (4:ℕ) * d * g * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (3:ℕ) * j +
    384 * c ^ (4:ℕ) * g * σ ^ (7:ℕ) * w ^ (7:ℕ) * O ^ (3:ℕ) * j -
    352 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (3:ℕ) * j +
    64 * c ^ (5:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (3:ℕ) * j) +
    (128 * c ^ (5:ℕ) * g * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (3:ℕ) * j +
    128 * c ^ (4:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (3:ℕ) * j +
    256 * c ^ (4:ℕ) * g * σ ^ (5:ℕ) * w ^ (9:ℕ) * O ^ (3:ℕ) * j +
    64 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (11:ℕ) * O ^ (3:ℕ) * j -
    480 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j)))) +
    (((160 * c ^ (5:ℕ) * d * g * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j +
    128 * c ^ (5:ℕ) * g * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j +
    128 * c ^ (4:ℕ) * d * g * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j -
    256 * c ^ (4:ℕ) * g * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j +
    704 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j -
    192 * c ^ (5:ℕ) * d * g * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j -
    256 * c ^ (5:ℕ) * g * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j -
    256 * c ^ (4:ℕ) * d * g * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j) +
    (-768 * c ^ (4:ℕ) * g * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j +
    672 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (5:ℕ) * j -
    96 * c ^ (5:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) * j -
    384 * c ^ (5:ℕ) * g * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) * j -
    384 * c ^ (4:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) * j -
    768 * c ^ (4:ℕ) * g * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (5:ℕ) * j -
    256 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (5:ℕ) * j -
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j)) +
    ((64 * c ^ (5:ℕ) * d * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j -
    128 * c ^ (5:ℕ) * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j -
    128 * c ^ (4:ℕ) * d * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j -
    640 * c ^ (4:ℕ) * g * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j -
    544 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (7:ℕ) * j +
    64 * c ^ (5:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j +
    384 * c ^ (5:ℕ) * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j +
    384 * c ^ (4:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j) +
    ((768 * c ^ (4:ℕ) * g * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (7:ℕ) * j +
    384 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (7:ℕ) * j +
    160 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (9:ℕ) * j -
    16 * c ^ (5:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j) +
    (-128 * c ^ (5:ℕ) * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j -
    128 * c ^ (4:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j -
    256 * c ^ (4:ℕ) * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (9:ℕ) * j -
    256 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (9:ℕ) * j +
    64 * c ^ (4:ℕ) * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (11:ℕ) * j)))))) +
    (((((240 * c ^ (5:ℕ) * g * N * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    80 * c ^ (5:ℕ) * K * g * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    288 * c ^ (5:ℕ) * g * N * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) -
    96 * c ^ (5:ℕ) * K * g * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    48 * c ^ (5:ℕ) * g * N * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) -
    48 * c ^ (5:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    592 * c ^ (5:ℕ) * g * N * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) +
    32 * c ^ (5:ℕ) * K * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ)) +
    (80 * c ^ (5:ℕ) * g * N * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) +
    32 * c ^ (5:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) -
    64 * c ^ (5:ℕ) * g * N * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ) -
    8 * c ^ (5:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ) +
    128 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) +
    384 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) -
    288 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ) -
    96 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (11:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ))) +
    ((64 * c ^ (5:ℕ) * d * g * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) +
    32 * c ^ (5:ℕ) * g * σ ^ (11:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) +
    32 * c ^ (4:ℕ) * d * g * σ ^ (11:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) -
    352 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) +
    192 * c ^ (5:ℕ) * d * g * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) +
    128 * c ^ (5:ℕ) * g * σ ^ (9:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) +
    128 * c ^ (4:ℕ) * d * g * σ ^ (9:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) -
    480 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ)) +
    ((192 * c ^ (5:ℕ) * d * g * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ) +
    192 * c ^ (5:ℕ) * g * σ ^ (7:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ) +
    192 * c ^ (4:ℕ) * d * g * σ ^ (7:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ) -
    288 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (8:ℕ) * O ^ (2:ℕ)) +
    (64 * c ^ (5:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (2:ℕ) +
    128 * c ^ (5:ℕ) * g * σ ^ (5:ℕ) * w ^ (9:ℕ) * O ^ (2:ℕ) +
    128 * c ^ (4:ℕ) * d * g * σ ^ (5:ℕ) * w ^ (9:ℕ) * O ^ (2:ℕ) -
    64 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (10:ℕ) * O ^ (2:ℕ) +
    32 * c ^ (5:ℕ) * g * σ ^ (3:ℕ) * w ^ (11:ℕ) * O ^ (2:ℕ))))) +
    (((32 * c ^ (4:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (11:ℕ) * O ^ (2:ℕ) -
    80 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) +
    64 * c ^ (5:ℕ) * d * g * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) -
    128 * c ^ (5:ℕ) * g * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) -
    128 * c ^ (4:ℕ) * d * g * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) -
    256 * c ^ (4:ℕ) * g * σ ^ (10:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) +
    272 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) -
    128 * c ^ (5:ℕ) * d * g * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ)) +
    (-384 * c ^ (5:ℕ) * g * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) -
    384 * c ^ (4:ℕ) * d * g * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) -
    768 * c ^ (4:ℕ) * g * σ ^ (8:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) +
    528 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) -
    192 * c ^ (5:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) -
    384 * c ^ (5:ℕ) * g * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) -
    384 * c ^ (4:ℕ) * d * g * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) -
    768 * c ^ (4:ℕ) * g * σ ^ (6:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ))) +
    ((176 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) -
    128 * c ^ (5:ℕ) * g * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ) -
    128 * c ^ (4:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ) -
    256 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (9:ℕ) * O ^ (4:ℕ) +
    128 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) -
    64 * c ^ (5:ℕ) * d * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) -
    320 * c ^ (5:ℕ) * g * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) -
    320 * c ^ (4:ℕ) * d * g * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ)) +
    ((-256 * c ^ (4:ℕ) * g * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) -
    352 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) +
    192 * c ^ (5:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) +
    384 * c ^ (5:ℕ) * g * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ)) +
    (384 * c ^ (4:ℕ) * d * g * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) +
    512 * c ^ (4:ℕ) * g * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) -
    224 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) +
    192 * c ^ (5:ℕ) * g * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) +
    192 * c ^ (4:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ)))))) +
    ((((768 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (6:ℕ) +
    72 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) -
    64 * c ^ (5:ℕ) * d * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) -
    128 * c ^ (5:ℕ) * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) -
    128 * c ^ (4:ℕ) * d * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) +
    256 * c ^ (4:ℕ) * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) +
    136 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) -
    128 * c ^ (5:ℕ) * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ)) +
    (-128 * c ^ (4:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) -
    768 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (8:ℕ) -
    32 * c ^ (5:ℕ) * N ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) +
    32 * c ^ (5:ℕ) * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) +
    32 * c ^ (4:ℕ) * d * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) +
    256 * c ^ (4:ℕ) * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (10:ℕ) +
    576 * c ^ (5:ℕ) * g * N * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j +
    32 * c ^ (5:ℕ) * K * g * σ ^ (8:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j)) +
    ((896 * c ^ (5:ℕ) * g * N * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (3:ℕ) * j -
    64 * c ^ (5:ℕ) * K * g * σ ^ (6:ℕ) * w ^ (5:ℕ) * O ^ (3:ℕ) * j +
    320 * c ^ (5:ℕ) * g * N * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (3:ℕ) * j -
    96 * c ^ (5:ℕ) * K * g * σ ^ (4:ℕ) * w ^ (7:ℕ) * O ^ (3:ℕ) * j +
    384 * c ^ (5:ℕ) * g * N * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j -
    32 * c ^ (5:ℕ) * K * g * σ ^ (6:ℕ) * w ^ (3:ℕ) * O ^ (5:ℕ) * j +
    128 * c ^ (5:ℕ) * g * N * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j +
    96 * c ^ (5:ℕ) * K * g * σ ^ (4:ℕ) * w ^ (5:ℕ) * O ^ (5:ℕ) * j) +
    ((-320 * c ^ (5:ℕ) * g * N * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j -
    32 * c ^ (5:ℕ) * K * g * σ ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (7:ℕ) * j -
    256 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    368 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ)) +
    (48 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) -
    400 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) -
    128 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) +
    72 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ) +
    400 * c ^ (5:ℕ) * g * N * σ ^ (10:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ))))) +
    (((-32 * c ^ (5:ℕ) * K * g * σ ^ (9:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) +
    880 * c ^ (5:ℕ) * g * N * σ ^ (8:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) -
    96 * c ^ (5:ℕ) * K * g * σ ^ (7:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) +
    560 * c ^ (5:ℕ) * g * N * σ ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ) -
    96 * c ^ (5:ℕ) * K * g * σ ^ (5:ℕ) * w ^ (7:ℕ) * O ^ (2:ℕ) +
    80 * c ^ (5:ℕ) * g * N * σ ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (2:ℕ) -
    32 * c ^ (5:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (9:ℕ) * O ^ (2:ℕ) -
    240 * c ^ (5:ℕ) * g * N * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ)) +
    (-80 * c ^ (5:ℕ) * K * g * σ ^ (7:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) -
    288 * c ^ (5:ℕ) * g * N * σ ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) +
    96 * c ^ (5:ℕ) * K * g * σ ^ (5:ℕ) * w ^ (5:ℕ) * O ^ (4:ℕ) -
    48 * c ^ (5:ℕ) * g * N * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) +
    48 * c ^ (5:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (7:ℕ) * O ^ (4:ℕ) -
    592 * c ^ (5:ℕ) * g * N * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) -
    32 * c ^ (5:ℕ) * K * g * σ ^ (5:ℕ) * w ^ (3:ℕ) * O ^ (6:ℕ) -
    80 * c ^ (5:ℕ) * g * N * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ))) +
    ((-32 * c ^ (5:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (6:ℕ) +
    64 * c ^ (5:ℕ) * g * N * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) +
    8 * c ^ (5:ℕ) * K * g * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (8:ℕ) -
    352 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (8:ℕ) * w ^ (2:ℕ) * O ^ (3:ℕ) * j +
    96 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (3:ℕ) * j -
    128 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (5:ℕ) * j -
    384 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (5:ℕ) * j +
    288 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (7:ℕ) * j) +
    ((-208 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (9:ℕ) * w ^ (2:ℕ) * O ^ (2:ℕ) -
    224 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (4:ℕ) * O ^ (2:ℕ) -
    16 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (2:ℕ) +
    256 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (7:ℕ) * w ^ (2:ℕ) * O ^ (4:ℕ)) +
    (-368 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (4:ℕ) -
    48 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) +
    400 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (6:ℕ) +
    128 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) -
    72 * c ^ (5:ℕ) * g ^ (2:ℕ) * σ ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ))))))))) * hj

/-- The pairing `⟨p̃, q⟩` reduced: `c w (−2jO) ĉ(jO) L`. Static algebra. -/
@[tmio M, powerlib_domain] theorem AnglePattern.pairing_eq {c d g σ w O j : ℂ}
    (hj : j ^ 2 = -1)
    (hg : 2 * σ * c * w * g =
      (d * c - O ^ 2) * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2)) :
    (2 * σ * c * w) * (angleVecP c d g σ w (-O) j ⬝ᵥ angleVecQ d σ w O j) =
      c * w * (-2 * O * j) * (AngleKey.cubRe c d σ w O + AngleKey.cubIm c d σ w O * j) * ((σ ^ 2
          + w ^ 2 - O ^ 2) + 2 * σ * O * j) := by
  simp only [angleVecP, angleVecQ, AngleKey.cubRe, AngleKey.cubIm, dotProduct, Fin.sum_univ_five,
      Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (2 * c * w * O * j + 2 * c * σ * w) * hg +
    (((-6 * c * σ * w * O ^ (6:ℕ) * j ^ (4:ℕ) - 4 * c ^ (2:ℕ) * σ * w * O ^ (5:ℕ) * j ^ (3:ℕ) -
    4 * c * d * σ * w * O ^ (5:ℕ) * j ^ (3:ℕ) - 24 * c * σ ^ (2:ℕ) * w * O ^ (5:ℕ) * j ^ (3:ℕ) -
    2 * c ^ (2:ℕ) * d * σ * w * O ^ (4:ℕ) * j ^ (2:ℕ) -
    16 * c ^ (2:ℕ) * σ ^ (2:ℕ) * w * O ^ (4:ℕ) * j ^ (2:ℕ) -
    16 * c * d * σ ^ (2:ℕ) * w * O ^ (4:ℕ) * j ^ (2:ℕ)) +
    (-36 * c * σ ^ (3:ℕ) * w * O ^ (4:ℕ) * j ^ (2:ℕ) -
    12 * c * σ * w ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) + 6 * c * σ * w * O ^ (6:ℕ) * j ^ (2:ℕ) -
    8 * c ^ (2:ℕ) * σ ^ (3:ℕ) * w * O ^ (3:ℕ) * j - 8 * c * d * σ ^ (3:ℕ) * w * O ^ (3:ℕ) * j -
    16 * c * σ ^ (4:ℕ) * w * O ^ (3:ℕ) * j - 8 * c ^ (2:ℕ) * σ * w ^ (3:ℕ) * O ^ (3:ℕ) * j)) +
    ((-8 * c * d * σ * w ^ (3:ℕ) * O ^ (3:ℕ) * j - 16 * c * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j +
    4 * c ^ (2:ℕ) * σ * w * O ^ (5:ℕ) * j + 4 * c * d * σ * w * O ^ (5:ℕ) * j +
    8 * c * σ ^ (2:ℕ) * w * O ^ (5:ℕ) * j + 4 * c ^ (2:ℕ) * d * σ ^ (3:ℕ) * w * O ^ (2:ℕ) -
    2 * c * σ ^ (5:ℕ) * w * O ^ (2:ℕ)) + (-4 * c ^ (2:ℕ) * d * σ * w ^ (3:ℕ) * O ^ (2:ℕ) -
    4 * c * σ ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) - 2 * c * σ * w ^ (5:ℕ) * O ^ (2:ℕ) +
    2 * c ^ (2:ℕ) * d * σ * w * O ^ (4:ℕ) - 4 * c * σ ^ (3:ℕ) * w * O ^ (4:ℕ) +
    4 * c * σ * w ^ (3:ℕ) * O ^ (4:ℕ) - 2 * c * σ * w * O ^ (6:ℕ)))) * hj

/-- `χ(2jO)` reduced: `−6 c² σ w O² ĉ(2jO)` (cubic values times `2σ`). Static algebra. -/
@[tmio M, powerlib_domain] theorem AnglePattern.shiftDet_eq {c d K g σ w O j : ℂ}
    (hj : j ^ 2 = -1)
    (hK : 2 * σ * c * K = (d * c - O ^ 2) * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * (d + c) * O ^ 2)
    (hg : 2 * σ * c * w * g =
      (d * c - O ^ 2) * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2)) :
    (2 * σ * c) * (2 * σ * c * w) * (AnglePattern.shiftDet c d K g σ w O j) =
      2 * c ^ 2 * σ * w * (-3 * O ^ 2) * (AngleKey.cub2Re c d σ w O + AngleKey.cub2Im c d σ w O
          * j) := by
  simp only [AnglePattern.shiftDet, AngleKey.cub2Re, AngleKey.cub2Im]
  linear_combination (-8 * c ^ (2:ℕ) * σ ^ (2:ℕ) * w * O * j - 2 * c ^ (2:ℕ) * σ ^ (3:ℕ) * w -
    2 * c ^ (2:ℕ) * σ * w ^ (3:ℕ) + 8 * c ^ (2:ℕ) * σ * w * O ^ (2:ℕ)) * hK +
    (2 * c ^ (2:ℕ) * σ * w) * hg + (128 * c ^ (2:ℕ) * σ ^ (2:ℕ) * w * O ^ (5:ℕ) * j ^ (3:ℕ) +
    64 * c ^ (3:ℕ) * σ ^ (2:ℕ) * w * O ^ (4:ℕ) * j ^ (2:ℕ) +
    64 * c ^ (2:ℕ) * d * σ ^ (2:ℕ) * w * O ^ (4:ℕ) * j ^ (2:ℕ) +
    128 * c ^ (2:ℕ) * σ ^ (3:ℕ) * w * O ^ (4:ℕ) * j ^ (2:ℕ) +
    32 * c ^ (3:ℕ) * d * σ ^ (2:ℕ) * w * O ^ (3:ℕ) * j +
    64 * c ^ (3:ℕ) * σ ^ (3:ℕ) * w * O ^ (3:ℕ) * j +
    64 * c ^ (2:ℕ) * d * σ ^ (3:ℕ) * w * O ^ (3:ℕ) * j +
    32 * c ^ (2:ℕ) * σ ^ (4:ℕ) * w * O ^ (3:ℕ) * j +
    32 * c ^ (2:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j -
    128 * c ^ (2:ℕ) * σ ^ (2:ℕ) * w * O ^ (5:ℕ) * j + 32 * c ^ (3:ℕ) * d * σ ^ (3:ℕ) * w * O ^ (2:ℕ)
    + 16 * c ^ (3:ℕ) * σ ^ (4:ℕ) * w * O ^ (2:ℕ) + 16 * c ^ (2:ℕ) * d * σ ^ (4:ℕ) * w * O ^ (2:ℕ) +
    16 * c ^ (3:ℕ) * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) +
    16 * c ^ (2:ℕ) * d * σ ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) -
    64 * c ^ (3:ℕ) * σ ^ (2:ℕ) * w * O ^ (4:ℕ) - 64 * c ^ (2:ℕ) * d * σ ^ (2:ℕ) * w * O ^ (4:ℕ) -
    128 * c ^ (2:ℕ) * σ ^ (3:ℕ) * w * O ^ (4:ℕ) -
    16 * c ^ (3:ℕ) * K * σ ^ (2:ℕ) * w * O ^ (2:ℕ)) * hj

/-- `a₀ = c (g w − K ρ)` reduced. Static algebra. -/
@[tmio M, powerlib_domain] theorem AnglePattern.det_eq {c d K g σ w O : ℂ}
    (hK : 2 * σ * c * K = (d * c - O ^ 2) * (σ ^ 2 + w ^ 2 - O ^ 2) - 2 * σ * (d + c) * O ^ 2)
    (hg : 2 * σ * c * w * g =
      (d * c - O ^ 2) * ((σ ^ 2 + w ^ 2 - O ^ 2) ^ 2 + 4 * σ ^ 2 * O ^ 2)) :
    (2 * σ * c) * (2 * σ * c * w) * (c * (g * w - K * (σ ^ 2 + w ^ 2))) =
      2 * w * σ * O ^ 2 * c ^ 2 * AngleKey.constRed c d σ w O := by
  simp only [AngleKey.constRed]
  linear_combination (-2 * c ^ (2:ℕ) * σ ^ (3:ℕ) * w - 2 * c ^ (2:ℕ) * σ * w ^ (3:ℕ)) * hK +
    (2 * c ^ (2:ℕ) * σ * w) * hg

/-- Lossless `⟨p̃, C(q, q, q̄)⟩` reduced. Static algebra. -/
@[tmio M, powerlib_domain] theorem AnglePattern.loss_trilin_pairing {c d K g w O j : ℂ}
    (hj : j ^ 2 = -1)
    (hg0 : c ^ 2 * w * g = (w ^ 2 - O ^ 2) * (c ^ 2 * K + O ^ 4 + c ^ 2 * O ^ 2)) :
    (c ^ 2 * w) * (angleVecP c d g 0 w (-O) j ⬝ᵥ AnglePattern.trilin c g K (angleVecQ d 0 w O j)
        (angleVecQ d 0 w O j) (angleVecQ d 0 w (-O) j)) =
      -(w * c * (w ^ 2 - O ^ 2) ^ 4 * AngleKey.lossTrilin c K O) := by
  simp only [angleVecP, angleVecQ, AnglePattern.trilin, AngleKey.lossTrilin, dotProduct,
      Fin.sum_univ_five, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (-4 * c * w ^ (7:ℕ) + 12 * c * w ^ (5:ℕ) * O ^ (2:ℕ) -
    12 * c * w ^ (3:ℕ) * O ^ (4:ℕ) + 4 * c * w * O ^ (6:ℕ)) * hg0 +
    (c ^ (3:ℕ) * K * w * O ^ (8:ℕ) * j ^ (6:ℕ) +
    4 * c ^ (3:ℕ) * K * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) -
    c ^ (3:ℕ) * K * w * O ^ (8:ℕ) * j ^ (4:ℕ) -
    4 * c ^ (3:ℕ) * g * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) +
    6 * c ^ (3:ℕ) * K * w ^ (5:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) -
    4 * c ^ (3:ℕ) * K * w ^ (3:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) +
    c ^ (3:ℕ) * K * w * O ^ (8:ℕ) * j ^ (2:ℕ) -
    12 * c ^ (3:ℕ) * g * w ^ (4:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    4 * c ^ (3:ℕ) * g * w ^ (2:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) +
    4 * c ^ (3:ℕ) * K * w ^ (7:ℕ) * O ^ (2:ℕ) - 6 * c ^ (3:ℕ) * K * w ^ (5:ℕ) * O ^ (4:ℕ) +
    4 * c ^ (3:ℕ) * K * w ^ (3:ℕ) * O ^ (6:ℕ) - c ^ (3:ℕ) * K * w * O ^ (8:ℕ) -
    12 * c ^ (3:ℕ) * g * w ^ (6:ℕ) * O ^ (2:ℕ) + 12 * c ^ (3:ℕ) * g * w ^ (4:ℕ) * O ^ (4:ℕ) -
    4 * c ^ (3:ℕ) * g * w ^ (2:ℕ) * O ^ (6:ℕ)) * hj

/-- Lossless `⟨p̃, B(q, r̄)⟩` reduced. Static algebra. -/
@[tmio M, powerlib_domain] theorem AnglePattern.loss_bilin_pairing {c d K g N w O j : ℂ}
    (hj : j ^ 2 = -1)
    (hg0 : c ^ 2 * w * g = (w ^ 2 - O ^ 2) * (c ^ 2 * K + O ^ 4 + c ^ 2 * O ^ 2)) :
    (c ^ 4 * w ^ 2) * (angleVecP c d g 0 w (-O) j ⬝ᵥ AnglePattern.bilin c g N (angleVecQ d 0 w O j)
        (AnglePattern.solveJ c K g 0 w (AnglePattern.bilin c g N (angleVecQ d 0 w O j) (angleVecQ d
            0 w (-O) j)))) =
      -(c ^ 2 * (w ^ 2 - O ^ 2) ^ 4 * AngleKey.lossBilinRed c K N w O) := by
  simp only [angleVecP, angleVecQ, AnglePattern.bilin, AnglePattern.solveJ, AngleKey.lossBilinRed,
      dotProduct, Fin.sum_univ_five, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (-c ^ (4:ℕ) * w ^ (10:ℕ) * O ^ (2:ℕ) + 5 * c ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) -
    c ^ (2:ℕ) * w ^ (10:ℕ) * O ^ (4:ℕ) - 10 * c ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) +
    5 * c ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (6:ℕ) + 10 * c ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) -
    10 * c ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ) - 5 * c ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) +
    10 * c ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ) + c ^ (4:ℕ) * O ^ (12:ℕ) -
    5 * c ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ) + c ^ (2:ℕ) * O ^ (14:ℕ) +
    c ^ (4:ℕ) * K * w ^ (8:ℕ) * O ^ (2:ℕ) - 4 * c ^ (4:ℕ) * K * w ^ (6:ℕ) * O ^ (4:ℕ) +
    6 * c ^ (4:ℕ) * K * w ^ (4:ℕ) * O ^ (6:ℕ) - 4 * c ^ (4:ℕ) * K * w ^ (2:ℕ) * O ^ (8:ℕ) +
    c ^ (4:ℕ) * K * O ^ (10:ℕ) - c ^ (4:ℕ) * g * w ^ (9:ℕ) +
    4 * c ^ (4:ℕ) * g * w ^ (7:ℕ) * O ^ (2:ℕ) - 6 * c ^ (4:ℕ) * g * w ^ (5:ℕ) * O ^ (4:ℕ) +
    4 * c ^ (4:ℕ) * g * w ^ (3:ℕ) * O ^ (6:ℕ) - c ^ (4:ℕ) * g * w * O ^ (8:ℕ)) * hg0 +
    (((c ^ (6:ℕ) * N ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) +
    c ^ (6:ℕ) * K * g * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) +
    4 * c ^ (6:ℕ) * N ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) -
    c ^ (6:ℕ) * N ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ) -
    c ^ (6:ℕ) * g ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) +
    4 * c ^ (6:ℕ) * K * g * w ^ (5:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) -
    c ^ (6:ℕ) * K * g * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ)) +
    (6 * c ^ (6:ℕ) * N ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) -
    4 * c ^ (6:ℕ) * N ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) +
    c ^ (6:ℕ) * N ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ) -
    4 * c ^ (6:ℕ) * g ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) +
    c ^ (6:ℕ) * g ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ) +
    6 * c ^ (6:ℕ) * K * g * w ^ (7:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) -
    4 * c ^ (6:ℕ) * K * g * w ^ (5:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) +
    c ^ (6:ℕ) * K * g * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ))) +
    ((4 * c ^ (6:ℕ) * N ^ (2:ℕ) * w ^ (10:ℕ) * O ^ (2:ℕ) -
    6 * c ^ (6:ℕ) * N ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) +
    4 * c ^ (6:ℕ) * N ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) -
    c ^ (6:ℕ) * N ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) -
    6 * c ^ (6:ℕ) * g ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    4 * c ^ (6:ℕ) * g ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) -
    c ^ (6:ℕ) * g ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ)) +
    (4 * c ^ (6:ℕ) * K * g * w ^ (9:ℕ) * O ^ (2:ℕ) - 6 * c ^ (6:ℕ) * K * g * w ^ (7:ℕ) * O ^ (4:ℕ) +
    4 * c ^ (6:ℕ) * K * g * w ^ (5:ℕ) * O ^ (6:ℕ) - c ^ (6:ℕ) * K * g * w ^ (3:ℕ) * O ^ (8:ℕ) -
    4 * c ^ (6:ℕ) * g ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (2:ℕ) +
    6 * c ^ (6:ℕ) * g ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) -
    4 * c ^ (6:ℕ) * g ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) +
    c ^ (6:ℕ) * g ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ)))) * hj

/-- Lossless `⟨p̃, B(q̄, s̄)⟩` reduced. Static algebra. -/
@[tmio M, powerlib_domain] theorem AnglePattern.loss_shift_pairing {c d K g N w O j : ℂ}
    (hj : j ^ 2 = -1)
    (hd : c * d = O ^ 2)
    (hg0 : c ^ 2 * w * g = (w ^ 2 - O ^ 2) * (c ^ 2 * K + O ^ 4 + c ^ 2 * O ^ 2)) :
    (c ^ 5 * w ^ 2) * (angleVecP c d g 0 w (-O) j ⬝ᵥ AnglePattern.bilin c g N (angleVecQ d 0 w (-O)
        j)
        (AnglePattern.solveShift c d K g 0 w O j (AnglePattern.bilin c g N (angleVecQ d 0 w O j)
            (angleVecQ d 0 w O j)))) =
      (w ^ 2 - O ^ 2) ^ 4 * (AngleKey.lossShiftRe c K N w O + AngleKey.lossShiftIm c K N w O
          * j) := by
  simp only [angleVecP, angleVecQ, AnglePattern.bilin, AnglePattern.solveShift,
      AngleKey.lossShiftRe, AngleKey.lossShiftIm, dotProduct, Fin.sum_univ_five,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (((2 * c ^ (5:ℕ) * d * w ^ (10:ℕ) * O * j -
    8 * c ^ (5:ℕ) * d * w ^ (8:ℕ) * O ^ (3:ℕ) * j - 8 * c ^ (4:ℕ) * w ^ (10:ℕ) * O ^ (3:ℕ) * j +
    12 * c ^ (5:ℕ) * d * w ^ (6:ℕ) * O ^ (5:ℕ) * j + 32 * c ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (5:ℕ) * j -
    8 * c ^ (5:ℕ) * d * w ^ (4:ℕ) * O ^ (7:ℕ) * j - 48 * c ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (7:ℕ) * j +
    2 * c ^ (5:ℕ) * d * w ^ (2:ℕ) * O ^ (9:ℕ) * j) + ((32 * c ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (9:ℕ) * j -
    8 * c ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (11:ℕ) * j - 3 * c ^ (5:ℕ) * w ^ (10:ℕ) * O ^ (2:ℕ) -
    4 * c ^ (4:ℕ) * d * w ^ (10:ℕ) * O ^ (2:ℕ)) + (15 * c ^ (5:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) +
    16 * c ^ (4:ℕ) * d * w ^ (8:ℕ) * O ^ (4:ℕ) + c ^ (3:ℕ) * w ^ (10:ℕ) * O ^ (4:ℕ) -
    18 * c ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) - 24 * c ^ (4:ℕ) * d * w ^ (6:ℕ) * O ^ (6:ℕ)))) +
    (((-c ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (6:ℕ) - 6 * c ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) +
    16 * c ^ (4:ℕ) * d * w ^ (4:ℕ) * O ^ (8:ℕ) + 6 * c ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (8:ℕ)) +
    (21 * c ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) - 4 * c ^ (4:ℕ) * d * w ^ (2:ℕ) * O ^ (10:ℕ) -
    22 * c ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (10:ℕ) - 9 * c ^ (5:ℕ) * O ^ (12:ℕ) +
    25 * c ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (12:ℕ))) + ((-9 * c ^ (3:ℕ) * O ^ (14:ℕ) +
    3 * c ^ (5:ℕ) * K * w ^ (8:ℕ) * O ^ (2:ℕ) - 18 * c ^ (5:ℕ) * K * w ^ (4:ℕ) * O ^ (6:ℕ) +
    24 * c ^ (5:ℕ) * K * w ^ (2:ℕ) * O ^ (8:ℕ)) + (-9 * c ^ (5:ℕ) * K * O ^ (10:ℕ) +
    c ^ (5:ℕ) * g * w ^ (9:ℕ) + 6 * c ^ (5:ℕ) * g * w ^ (5:ℕ) * O ^ (4:ℕ) -
    16 * c ^ (5:ℕ) * g * w ^ (3:ℕ) * O ^ (6:ℕ) + 9 * c ^ (5:ℕ) * g * w * O ^ (8:ℕ))))) * hg0 +
    ((((2 * c ^ (6:ℕ) * w ^ (12:ℕ) * O ^ (3:ℕ) * j - 10 * c ^ (6:ℕ) * w ^ (10:ℕ) * O ^ (5:ℕ) * j +
    2 * c ^ (4:ℕ) * w ^ (12:ℕ) * O ^ (5:ℕ) * j + 20 * c ^ (6:ℕ) * w ^ (8:ℕ) * O ^ (7:ℕ) * j) +
    (-10 * c ^ (4:ℕ) * w ^ (10:ℕ) * O ^ (7:ℕ) * j - 20 * c ^ (6:ℕ) * w ^ (6:ℕ) * O ^ (9:ℕ) * j +
    20 * c ^ (4:ℕ) * w ^ (8:ℕ) * O ^ (9:ℕ) * j + 10 * c ^ (6:ℕ) * w ^ (4:ℕ) * O ^ (11:ℕ) * j -
    20 * c ^ (4:ℕ) * w ^ (6:ℕ) * O ^ (11:ℕ) * j)) + ((-2 * c ^ (6:ℕ) * w ^ (2:ℕ) * O ^ (13:ℕ) * j +
    10 * c ^ (4:ℕ) * w ^ (4:ℕ) * O ^ (13:ℕ) * j - 2 * c ^ (4:ℕ) * w ^ (2:ℕ) * O ^ (15:ℕ) * j -
    4 * c ^ (5:ℕ) * w ^ (12:ℕ) * O ^ (4:ℕ)) + (20 * c ^ (5:ℕ) * w ^ (10:ℕ) * O ^ (6:ℕ) -
    4 * c ^ (3:ℕ) * w ^ (12:ℕ) * O ^ (6:ℕ) - 40 * c ^ (5:ℕ) * w ^ (8:ℕ) * O ^ (8:ℕ) +
    20 * c ^ (3:ℕ) * w ^ (10:ℕ) * O ^ (8:ℕ) + 40 * c ^ (5:ℕ) * w ^ (6:ℕ) * O ^ (10:ℕ)))) +
    (((-40 * c ^ (3:ℕ) * w ^ (8:ℕ) * O ^ (10:ℕ) - 20 * c ^ (5:ℕ) * w ^ (4:ℕ) * O ^ (12:ℕ) +
    40 * c ^ (3:ℕ) * w ^ (6:ℕ) * O ^ (12:ℕ) + 4 * c ^ (5:ℕ) * w ^ (2:ℕ) * O ^ (14:ℕ)) +
    (-20 * c ^ (3:ℕ) * w ^ (4:ℕ) * O ^ (14:ℕ) + 4 * c ^ (3:ℕ) * w ^ (2:ℕ) * O ^ (16:ℕ) +
    2 * c ^ (6:ℕ) * K * w ^ (12:ℕ) * O * j - 10 * c ^ (6:ℕ) * K * w ^ (10:ℕ) * O ^ (3:ℕ) * j +
    20 * c ^ (6:ℕ) * K * w ^ (8:ℕ) * O ^ (5:ℕ) * j)) +
    ((-20 * c ^ (6:ℕ) * K * w ^ (6:ℕ) * O ^ (7:ℕ) * j +
    10 * c ^ (6:ℕ) * K * w ^ (4:ℕ) * O ^ (9:ℕ) * j - 2 * c ^ (6:ℕ) * K * w ^ (2:ℕ) * O ^ (11:ℕ) * j
    - 4 * c ^ (5:ℕ) * K * w ^ (12:ℕ) * O ^ (2:ℕ)) + (20 * c ^ (5:ℕ) * K * w ^ (10:ℕ) * O ^ (4:ℕ) -
    40 * c ^ (5:ℕ) * K * w ^ (8:ℕ) * O ^ (6:ℕ) + 40 * c ^ (5:ℕ) * K * w ^ (6:ℕ) * O ^ (8:ℕ) -
    20 * c ^ (5:ℕ) * K * w ^ (4:ℕ) * O ^ (10:ℕ) +
    4 * c ^ (5:ℕ) * K * w ^ (2:ℕ) * O ^ (12:ℕ))))) * hd +
    (((((8 * c ^ (6:ℕ) * g * w ^ (3:ℕ) * O ^ (11:ℕ) * j ^ (9:ℕ) -
    4 * c ^ (7:ℕ) * N ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) * j ^ (8:ℕ) +
    4 * c ^ (7:ℕ) * g * w ^ (3:ℕ) * O ^ (10:ℕ) * j ^ (8:ℕ) +
    4 * c ^ (6:ℕ) * d * g * w ^ (3:ℕ) * O ^ (10:ℕ) * j ^ (8:ℕ) +
    2 * c ^ (7:ℕ) * d * g * w ^ (3:ℕ) * O ^ (9:ℕ) * j ^ (7:ℕ)) +
    (32 * c ^ (6:ℕ) * g * w ^ (5:ℕ) * O ^ (9:ℕ) * j ^ (7:ℕ) -
    8 * c ^ (6:ℕ) * g * w ^ (3:ℕ) * O ^ (11:ℕ) * j ^ (7:ℕ) -
    17 * c ^ (7:ℕ) * N ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) +
    16 * c ^ (7:ℕ) * g * w ^ (5:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) +
    16 * c ^ (6:ℕ) * d * g * w ^ (5:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) +
    4 * c ^ (7:ℕ) * N ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) * j ^ (6:ℕ))) +
    ((-4 * c ^ (7:ℕ) * g * w ^ (3:ℕ) * O ^ (10:ℕ) * j ^ (6:ℕ) -
    4 * c ^ (6:ℕ) * d * g * w ^ (3:ℕ) * O ^ (10:ℕ) * j ^ (6:ℕ) +
    8 * c ^ (7:ℕ) * d * g * w ^ (5:ℕ) * O ^ (7:ℕ) * j ^ (5:ℕ) +
    48 * c ^ (6:ℕ) * g * w ^ (7:ℕ) * O ^ (7:ℕ) * j ^ (5:ℕ) -
    2 * c ^ (7:ℕ) * d * g * w ^ (3:ℕ) * O ^ (9:ℕ) * j ^ (5:ℕ)) +
    (-32 * c ^ (6:ℕ) * g * w ^ (5:ℕ) * O ^ (9:ℕ) * j ^ (5:ℕ) +
    8 * c ^ (6:ℕ) * g * w ^ (3:ℕ) * O ^ (11:ℕ) * j ^ (5:ℕ) -
    c ^ (7:ℕ) * K * g * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) -
    28 * c ^ (7:ℕ) * N ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) +
    24 * c ^ (7:ℕ) * g * w ^ (7:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) +
    24 * c ^ (6:ℕ) * d * g * w ^ (7:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ)))) +
    (((17 * c ^ (7:ℕ) * N ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ) -
    16 * c ^ (7:ℕ) * g * w ^ (5:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ) -
    16 * c ^ (6:ℕ) * d * g * w ^ (5:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ) -
    4 * c ^ (7:ℕ) * N ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) * j ^ (4:ℕ) +
    4 * c ^ (7:ℕ) * g * w ^ (3:ℕ) * O ^ (10:ℕ) * j ^ (4:ℕ)) +
    (4 * c ^ (6:ℕ) * d * g * w ^ (3:ℕ) * O ^ (10:ℕ) * j ^ (4:ℕ) +
    9 * c ^ (7:ℕ) * g ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (6:ℕ) +
    12 * c ^ (7:ℕ) * d * g * w ^ (7:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) +
    32 * c ^ (6:ℕ) * g * w ^ (9:ℕ) * O ^ (5:ℕ) * j ^ (3:ℕ) -
    8 * c ^ (7:ℕ) * d * g * w ^ (5:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ) -
    48 * c ^ (6:ℕ) * g * w ^ (7:ℕ) * O ^ (7:ℕ) * j ^ (3:ℕ))) +
    ((2 * c ^ (7:ℕ) * d * g * w ^ (3:ℕ) * O ^ (9:ℕ) * j ^ (3:ℕ) +
    32 * c ^ (6:ℕ) * g * w ^ (5:ℕ) * O ^ (9:ℕ) * j ^ (3:ℕ) -
    8 * c ^ (6:ℕ) * g * w ^ (3:ℕ) * O ^ (11:ℕ) * j ^ (3:ℕ) -
    4 * c ^ (7:ℕ) * K * g * w ^ (5:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) +
    c ^ (7:ℕ) * K * g * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ)) +
    (-22 * c ^ (7:ℕ) * N ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    16 * c ^ (7:ℕ) * g * w ^ (9:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    16 * c ^ (6:ℕ) * d * g * w ^ (9:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    28 * c ^ (7:ℕ) * N ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) -
    24 * c ^ (7:ℕ) * g * w ^ (7:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) -
    24 * c ^ (6:ℕ) * d * g * w ^ (7:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ))))) +
    ((((-17 * c ^ (7:ℕ) * N ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ) +
    16 * c ^ (7:ℕ) * g * w ^ (5:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ) +
    16 * c ^ (6:ℕ) * d * g * w ^ (5:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ) +
    4 * c ^ (7:ℕ) * N ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ) * j ^ (2:ℕ) -
    4 * c ^ (7:ℕ) * g * w ^ (3:ℕ) * O ^ (10:ℕ) * j ^ (2:ℕ)) +
    (-4 * c ^ (6:ℕ) * d * g * w ^ (3:ℕ) * O ^ (10:ℕ) * j ^ (2:ℕ) +
    16 * c ^ (7:ℕ) * g ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) * j ^ (4:ℕ) -
    9 * c ^ (7:ℕ) * g ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (4:ℕ) +
    8 * c ^ (7:ℕ) * d * g * w ^ (9:ℕ) * O ^ (3:ℕ) * j +
    8 * c ^ (6:ℕ) * g * w ^ (11:ℕ) * O ^ (3:ℕ) * j -
    12 * c ^ (7:ℕ) * d * g * w ^ (7:ℕ) * O ^ (5:ℕ) * j)) +
    ((-32 * c ^ (6:ℕ) * g * w ^ (9:ℕ) * O ^ (5:ℕ) * j +
    8 * c ^ (7:ℕ) * d * g * w ^ (5:ℕ) * O ^ (7:ℕ) * j +
    48 * c ^ (6:ℕ) * g * w ^ (7:ℕ) * O ^ (7:ℕ) * j -
    2 * c ^ (7:ℕ) * d * g * w ^ (3:ℕ) * O ^ (9:ℕ) * j -
    32 * c ^ (6:ℕ) * g * w ^ (5:ℕ) * O ^ (9:ℕ) * j) +
    (8 * c ^ (6:ℕ) * g * w ^ (3:ℕ) * O ^ (11:ℕ) * j -
    6 * c ^ (7:ℕ) * K * g * w ^ (7:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) +
    4 * c ^ (7:ℕ) * K * g * w ^ (5:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) -
    c ^ (7:ℕ) * K * g * w ^ (3:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ) -
    8 * c ^ (7:ℕ) * N ^ (2:ℕ) * w ^ (10:ℕ) * O ^ (2:ℕ) +
    4 * c ^ (7:ℕ) * g * w ^ (11:ℕ) * O ^ (2:ℕ)))) +
    (((4 * c ^ (6:ℕ) * d * g * w ^ (11:ℕ) * O ^ (2:ℕ) +
    22 * c ^ (7:ℕ) * N ^ (2:ℕ) * w ^ (8:ℕ) * O ^ (4:ℕ) - 16 * c ^ (7:ℕ) * g * w ^ (9:ℕ) * O ^ (4:ℕ)
    - 16 * c ^ (6:ℕ) * d * g * w ^ (9:ℕ) * O ^ (4:ℕ) -
    28 * c ^ (7:ℕ) * N ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (6:ℕ)) +
    (24 * c ^ (7:ℕ) * g * w ^ (7:ℕ) * O ^ (6:ℕ) + 24 * c ^ (6:ℕ) * d * g * w ^ (7:ℕ) * O ^ (6:ℕ) +
    17 * c ^ (7:ℕ) * N ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (8:ℕ) - 16 * c ^ (7:ℕ) * g * w ^ (5:ℕ) * O ^ (8:ℕ)
    - 16 * c ^ (6:ℕ) * d * g * w ^ (5:ℕ) * O ^ (8:ℕ) -
    4 * c ^ (7:ℕ) * N ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (10:ℕ))) +
    ((4 * c ^ (7:ℕ) * g * w ^ (3:ℕ) * O ^ (10:ℕ) + 4 * c ^ (6:ℕ) * d * g * w ^ (3:ℕ) * O ^ (10:ℕ) +
    6 * c ^ (7:ℕ) * g ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) -
    16 * c ^ (7:ℕ) * g ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) * j ^ (2:ℕ) +
    9 * c ^ (7:ℕ) * g ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ) * j ^ (2:ℕ) -
    4 * c ^ (7:ℕ) * K * g * w ^ (9:ℕ) * O ^ (2:ℕ)) + (6 * c ^ (7:ℕ) * K * g * w ^ (7:ℕ) * O ^ (4:ℕ)
    - 4 * c ^ (7:ℕ) * K * g * w ^ (5:ℕ) * O ^ (6:ℕ) + c ^ (7:ℕ) * K * g * w ^ (3:ℕ) * O ^ (8:ℕ) -
    6 * c ^ (7:ℕ) * g ^ (2:ℕ) * w ^ (6:ℕ) * O ^ (4:ℕ) +
    16 * c ^ (7:ℕ) * g ^ (2:ℕ) * w ^ (4:ℕ) * O ^ (6:ℕ) -
    9 * c ^ (7:ℕ) * g ^ (2:ℕ) * w ^ (2:ℕ) * O ^ (8:ℕ)))))) * hj

/-- Lossless pairing `⟨p̃, q⟩` reduced. Static algebra. -/
@[tmio M, powerlib_domain] theorem AnglePattern.loss_pairing_eq {c d K g w O j : ℂ}
    (hj : j ^ 2 = -1)
    (hd : c * d = O ^ 2)
    (hg0 : c ^ 2 * w * g = (w ^ 2 - O ^ 2) * (c ^ 2 * K + O ^ 4 + c ^ 2 * O ^ 2)) :
    (c ^ 3 * w) * (angleVecP c d g 0 w (-O) j ⬝ᵥ angleVecQ d 0 w O j) =
      -2 * O * j * w * c ^ 2 * (w ^ 2 - O ^ 2) * (AngleKey.lossCubRe c K w O
          + AngleKey.lossCubIm c w O * j) := by
  simp only [angleVecP, angleVecQ, AngleKey.lossCubRe, AngleKey.lossCubIm, dotProduct,
      Fin.sum_univ_five, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (2 * c ^ (2:ℕ) * w * O * j) * hg0 + (-2 * c ^ (2:ℕ) * w ^ (5:ℕ) * O * j +
    4 * c ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j - 2 * c ^ (2:ℕ) * w * O ^ (5:ℕ) * j -
    c ^ (3:ℕ) * w ^ (5:ℕ) + 2 * c ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) - c ^ (3:ℕ) * w * O ^ (4:ℕ)) * hd
    + (-3 * c ^ (3:ℕ) * w * O ^ (6:ℕ) * j ^ (4:ℕ) - 2 * c ^ (4:ℕ) * w * O ^ (5:ℕ) * j ^ (3:ℕ) -
    2 * c ^ (3:ℕ) * d * w * O ^ (5:ℕ) * j ^ (3:ℕ) - c ^ (4:ℕ) * d * w * O ^ (4:ℕ) * j ^ (2:ℕ) -
    6 * c ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) * j ^ (2:ℕ) + 3 * c ^ (3:ℕ) * w * O ^ (6:ℕ) * j ^ (2:ℕ) -
    4 * c ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j - 4 * c ^ (3:ℕ) * d * w ^ (3:ℕ) * O ^ (3:ℕ) * j +
    2 * c ^ (4:ℕ) * w * O ^ (5:ℕ) * j + 2 * c ^ (3:ℕ) * d * w * O ^ (5:ℕ) * j -
    2 * c ^ (4:ℕ) * d * w ^ (3:ℕ) * O ^ (2:ℕ) - c ^ (3:ℕ) * w ^ (5:ℕ) * O ^ (2:ℕ) +
    c ^ (4:ℕ) * d * w * O ^ (4:ℕ) + 2 * c ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (4:ℕ) -
    c ^ (3:ℕ) * w * O ^ (6:ℕ)) * hj

/-- Lossless `χ(2jO)` reduced. Static algebra. -/
@[tmio M, powerlib_domain] theorem AnglePattern.loss_shiftDet_eq {c d K g w O j : ℂ}
    (hj : j ^ 2 = -1)
    (hd : c * d = O ^ 2)
    (hg0 : c ^ 2 * w * g = (w ^ 2 - O ^ 2) * (c ^ 2 * K + O ^ 4 + c ^ 2 * O ^ 2)) :
    (c ^ 3 * w) * (AnglePattern.shiftDet c d K g 0 w O j) =
      -3 * O ^ 2 * w * c ^ 2 * (AngleKey.lossCub2Re c K w O + AngleKey.lossCub2Im c w O * j) := by
  simp only [AnglePattern.shiftDet, AngleKey.lossCub2Re, AngleKey.lossCub2Im]
  linear_combination (c ^ (2:ℕ) * w) * hg0 + (2 * c ^ (3:ℕ) * w ^ (3:ℕ) * O * j -
    8 * c ^ (3:ℕ) * w * O ^ (3:ℕ) * j - 4 * c ^ (2:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) +
    16 * c ^ (2:ℕ) * w * O ^ (4:ℕ)) * hd + (32 * c ^ (3:ℕ) * w * O ^ (5:ℕ) * j ^ (3:ℕ) +
    16 * c ^ (4:ℕ) * w * O ^ (4:ℕ) * j ^ (2:ℕ) + 16 * c ^ (3:ℕ) * d * w * O ^ (4:ℕ) * j ^ (2:ℕ) +
    8 * c ^ (4:ℕ) * d * w * O ^ (3:ℕ) * j + 8 * c ^ (3:ℕ) * w ^ (3:ℕ) * O ^ (3:ℕ) * j -
    32 * c ^ (3:ℕ) * w * O ^ (5:ℕ) * j + 4 * c ^ (4:ℕ) * w ^ (3:ℕ) * O ^ (2:ℕ) +
    4 * c ^ (3:ℕ) * d * w ^ (3:ℕ) * O ^ (2:ℕ) - 16 * c ^ (4:ℕ) * w * O ^ (4:ℕ) -
    16 * c ^ (3:ℕ) * d * w * O ^ (4:ℕ) - 4 * c ^ (4:ℕ) * K * w * O ^ (2:ℕ)) * hj

/-- Lossless `a₀` reduced. Static algebra. -/
@[tmio M, powerlib_domain] theorem AnglePattern.loss_det_eq {c K g w O : ℂ}
    (hg0 : c ^ 2 * w * g = (w ^ 2 - O ^ 2) * (c ^ 2 * K + O ^ 4 + c ^ 2 * O ^ 2)) :
    (c ^ 2 * w) * (c * (g * w - K * (0 ^ 2 + w ^ 2))) =
      w * c * O ^ 2 * AngleKey.lossConstRed c K w O := by
  simp only [AngleKey.lossConstRed]
  linear_combination (c * w) * hg0


end VSMLPF
end powerlib.GFM.Line
