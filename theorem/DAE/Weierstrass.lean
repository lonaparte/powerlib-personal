import theorem.Attributes
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Algebra.Polynomial.Roots

/-! # Weierstrass canonical form of a regular matrix pencil

Every regular square matrix pencil over an infinite field has a Weierstrass canonical form, and
regularity is necessary.

Model boundary.
* Object: a square matrix pencil `s E - A` with `E A : Matrix ι ι K` over a field `K` (any
  finite index type `ι`), i.e. the coefficient pair of the constant-coefficient linear DAE
  `E x' = A x + f`. The pencil is *regular* when its determinant polynomial
  `det (X E - A) ∈ K[X]` (`pencilPoly`) is not the zero polynomial (`Regular`). Over an
  infinite field this is equivalent to `det (c E - A) ≠ 0` for some `c ∈ K`
  (`regular_iff_exists_det_ne_zero`).
* A *Weierstrass form* (`WeierstrassForm E A`) consists of a split `k + l` of the coordinates,
  matrices `P : Matrix (Fin k ⊕ Fin l) ι K`, `Q : Matrix ι (Fin k ⊕ Fin l) K` with two-sided
  inverses `P'`, `Q'`, a matrix `J` (size `k`) and a nilpotent `N` (size `l`) with
```
P E Q = diag(I, N),     P A Q = diag(J, I),   hence   P (s E - A) Q = diag(s I - J, s N - I).
```
  `P`, `Q` are indexed by `Fin k ⊕ Fin l` on the canonical side, so that the block structure is
  literal (`Matrix.fromBlocks`); their inverses make them invertible changes of equations and of
  variables.
* Constant coefficients; square pencils. Existence is proved over every infinite field (in
  particular `ℝ`, `ℂ`), and over any field once a point `c` with `det (c E - A) ≠ 0` is given;
  no claim about singular (rectangular or non-regular) pencils beyond the counterexample, and no
  Jordan form of `J` (only that `J` is some matrix). Static linear algebra: no solution notion
  is involved.
* The Kronecker index (nilpotency class of `N`) and its equality with the differentiation index
  are in `theorem/DAE/KroneckerIndex.lean`.

Source: work-sync theory/T-pantelides-index-reduction.md §1.1, §1.6 (Weierstrass form and
Kronecker index); theory/T-dae-systems.md §1.6.2 ("Kronecker 正则形式（仅线性 DAE）").

Results.
* `fitting_matrix` — Fitting decomposition in matrix form, from Mathlib's
  `LinearMap.eventually_isCompl_ker_pow_range_pow`: every square matrix is similar, by an
  explicit invertible change of basis, to `diag(M₁, M₀)` with `M₁` invertible and `M₀`
  nilpotent.
* `exists_weierstrassForm_of_det_ne_zero` — if `det (c E - A) ≠ 0` for one `c`, a Weierstrass
  form exists. Construction: `R = (c E - A)⁻¹`, Fitting decomposition of `R E = diag(M₁, M₀)`,
  then `R A = c R E - I`, `J = c I - M₁⁻¹`, `N = (c M₀ - I)⁻¹ M₀` (nilpotent because the two
  factors commute), `P = diag(M₁⁻¹, (c M₀ - I)⁻¹) P₀ R`, `Q = Q₀`.
* `weierstrass` — every regular pencil over an infinite field has a Weierstrass form.
* `WeierstrassForm.pencil_eq` — `P (s E - A) Q = diag(s I - J, s N - I)` for every `s`.
* `WeierstrassForm.det_eq_zero_iff` — the finite generalized eigenvalues of the pencil are
  exactly the eigenvalues of `J` (`det (s N - I)` is a unit because `s N` is nilpotent).
* `regular_iff_nonempty_weierstrassForm` — over an infinite field a pencil has a Weierstrass
  form iff it is regular.

Corrections.
* T-pantelides-index-reduction §1.1, T-dae-systems §1.6.2: the note asserts the Weierstrass form
  for every linear DAE `E ż = A z` with singular `E` and omits the regularity premise.
  Regularity is necessary (`regular_of_weierstrassForm`); the zero pencil `E = A = 0` of size
  one is a singular DAE with no Weierstrass form (`zero_pencil_no_weierstrassForm`). The note
  also names the pencil `E - λ A` while writing the normal form of `s E - A`; the formal
  statement uses `s E - A`, consistent with the displayed blocks.
-/

noncomputable section
namespace powerlib.DAE
open Matrix Polynomial

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Fitting decomposition in matrix form -/

/-- Fitting decomposition: every square matrix is, after an invertible change of basis `P`, `Q`
(`P Q = 1`, `Q P = 1`), block diagonal `diag(M₁, M₀)` with `M₁` invertible and `M₀` nilpotent. -/
@[tmio T, powerlib_foundation] theorem fitting_matrix (M : Matrix ι ι K) :
    ∃ (k l : ℕ) (P : Matrix (Fin k ⊕ Fin l) ι K) (Q : Matrix ι (Fin k ⊕ Fin l) K)
      (M₁ : Matrix (Fin k) (Fin k) K) (M₀ : Matrix (Fin l) (Fin l) K),
      P * Q = 1 ∧ Q * P = 1 ∧ P * M * Q = fromBlocks M₁ 0 0 M₀ ∧ IsUnit M₁ ∧
        IsNilpotent M₀ := by
  set f : Module.End K (ι → K) := Matrix.toLin' M with hf
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp f.eventually_isCompl_ker_pow_range_pow
  set r := N + 1 with hr
  have hc : IsCompl (LinearMap.range (f ^ r)) (LinearMap.ker (f ^ r)) :=
    (hN r (by omega)).symm
  have hcomm : ∀ x, (f ^ r) (f x) = f ((f ^ r) x) := fun x => by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_succ, ← pow_succ']
  have h₁ : ∀ x ∈ LinearMap.range (f ^ r), f x ∈ LinearMap.range (f ^ r) := by
    rintro _ ⟨u, rfl⟩
    exact ⟨f u, hcomm u⟩
  have h₀ : ∀ x ∈ LinearMap.ker (f ^ r), f x ∈ LinearMap.ker (f ^ r) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hcomm, hx, map_zero]
  set V₁ := LinearMap.range (f ^ r)
  set V₀ := LinearMap.ker (f ^ r)
  set f₁ : Module.End K V₁ := f.restrict h₁
  set f₀ : Module.End K V₀ := f.restrict h₀
  set b₁ := Module.finBasis K V₁
  set b₀ := Module.finBasis K V₀
  set e := Submodule.prodEquivOfIsCompl V₁ V₀ hc
  set b := (b₁.prod b₀).map e
  set std := Pi.basisFun K ι
  have hconj : ∀ y, f (e y) = e (f₁.prodMap f₀ y) := by
    rintro ⟨x, y⟩
    simp [e, f₁, f₀, LinearMap.restrict_apply, map_add]
  have hmat : LinearMap.toMatrix b b f =
      LinearMap.toMatrix (b₁.prod b₀) (b₁.prod b₀) (f₁.prodMap f₀) := by
    ext i j
    simp only [LinearMap.toMatrix_apply, b, Module.Basis.map_apply, Module.Basis.map_repr, hconj,
      LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  refine ⟨_, _, b.toMatrix std, std.toMatrix b, LinearMap.toMatrix b₁ b₁ f₁,
    LinearMap.toMatrix b₀ b₀ f₀, Module.Basis.toMatrix_mul_toMatrix_flip _ _,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, ?_, ?_, ?_⟩
  · have key := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b std b std f
    rw [LinearMap.toMatrix_eq_toMatrix', hf, LinearMap.toMatrix'_toLin'] at key
    rw [key, ← hf, hmat, LinearMap.toMatrix_prodMap]
  · change IsUnit (LinearMap.toMatrixAlgEquiv b₁ f₁)
    refine (isUnit_map_iff _ _).mpr ?_
    rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx' : f x = 0 := by
      have := congrArg Subtype.val hx
      simpa [f₁, LinearMap.restrict_apply] using this
    have hker : (x : ι → K) ∈ V₀ := by
      rw [LinearMap.mem_ker, hr, pow_succ, Module.End.mul_apply, hx', map_zero]
    have := hc.disjoint.le_bot ⟨x.2, hker⟩
    exact Subtype.ext (by simpa using this)
  · change IsNilpotent (LinearMap.toMatrixAlgEquiv b₀ f₀)
    refine IsNilpotent.map ?_ _
    refine ⟨r, LinearMap.ext fun x => ?_⟩
    rw [Module.End.pow_restrict]
    exact Subtype.ext (by simp [LinearMap.restrict_apply])

/-! ## Regular pencils and Weierstrass forms -/

/-- The determinant polynomial `det (X E - A) ∈ K[X]` of the pencil `s E - A`. -/
def pencilPoly (E A : Matrix ι ι K) : K[X] := ((X : K[X]) • E.map C - A.map C).det

/-- The pencil `s E - A` is regular: its determinant polynomial is not identically zero. -/
def Regular (E A : Matrix ι ι K) : Prop := pencilPoly E A ≠ 0

@[powerlib_foundation] theorem eval_pencilPoly (E A : Matrix ι ι K) (s : K) :
    (pencilPoly E A).eval s = (s • E - A).det := by
  rw [pencilPoly, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
    coe_evalRingHom, eval_sub, smul_eq_mul, eval_mul, eval_X, eval_C]

/-- Over an infinite field, regularity means that `det (c E - A) ≠ 0` for some `c`. -/
@[powerlib_foundation] theorem regular_iff_exists_det_ne_zero [Infinite K] (E A : Matrix ι ι K) :
    Regular E A ↔ ∃ c : K, (c • E - A).det ≠ 0 := by
  constructor
  · intro h
    have hfin : {x | IsRoot (pencilPoly E A) x}.Finite := by
      by_contra hinf
      exact h (eq_zero_of_infinite_isRoot _ hinf)
    obtain ⟨c, -, hc⟩ := (Set.infinite_univ.sdiff hfin).nonempty
    exact ⟨c, by simpa [eval_pencilPoly] using hc⟩
  · rintro ⟨c, hc⟩ h
    apply hc
    rw [← eval_pencilPoly, h, eval_zero]

/-- A Weierstrass form of the pencil `s E - A`: invertible `P`, `Q` with `P E Q = diag(I, N)` and
`P A Q = diag(J, I)`, `N` nilpotent. -/
structure WeierstrassForm (E A : Matrix ι ι K) where
  /-- Size of the finite (slow) block. -/
  k : ℕ
  /-- Size of the nilpotent (infinite-eigenvalue) block. -/
  l : ℕ
  P : Matrix (Fin k ⊕ Fin l) ι K
  P' : Matrix ι (Fin k ⊕ Fin l) K
  Q : Matrix ι (Fin k ⊕ Fin l) K
  Q' : Matrix (Fin k ⊕ Fin l) ι K
  J : Matrix (Fin k) (Fin k) K
  N : Matrix (Fin l) (Fin l) K
  P_mul_P' : P * P' = 1
  P'_mul_P : P' * P = 1
  Q_mul_Q' : Q * Q' = 1
  Q'_mul_Q : Q' * Q = 1
  nilpotent : IsNilpotent N
  E_eq : P * E * Q = fromBlocks 1 0 0 N
  A_eq : P * A * Q = fromBlocks J 0 0 1

/-- Existence of a Weierstrass form from one point `c` with `det (c E - A) ≠ 0`. -/
@[powerlib_foundation] theorem exists_weierstrassForm_of_det_ne_zero (E A : Matrix ι ι K) {c : K}
    (hc : (c • E - A).det ≠ 0) : Nonempty (WeierstrassForm E A) := by
  set G := c • E - A with hG
  have hGu : IsUnit G.det := isUnit_iff_ne_zero.mpr hc
  set R := G⁻¹
  have hRG : R * G = 1 := nonsing_inv_mul G hGu
  have hGR : G * R = 1 := mul_nonsing_inv G hGu
  have hRA : R * A = c • (R * E) - 1 := by
    rw [← hRG, hG, Matrix.mul_sub, Matrix.mul_smul]; abel
  obtain ⟨k, l, P₀, Q₀, M₁, M₀, h₁, h₂, h₃, hu, hn⟩ := fitting_matrix (R * E)
  have hU : IsUnit (c • M₀ - 1) := (hn.smul c).isUnit_sub_one
  have hUd : IsUnit (c • M₀ - 1).det := (Matrix.isUnit_iff_isUnit_det _).mp hU
  have hMd : IsUnit M₁.det := (Matrix.isUnit_iff_isUnit_det _).mp hu
  set D := fromBlocks M₁⁻¹ 0 0 (c • M₀ - 1)⁻¹ with hD
  set D' := fromBlocks M₁ 0 0 (c • M₀ - 1) with hD'
  have hDD' : D * D' = 1 := by
    rw [hD, hD', fromBlocks_multiply]
    simp [nonsing_inv_mul _ hMd, nonsing_inv_mul _ hUd, fromBlocks_one]
  have hD'D : D' * D = 1 := by
    rw [hD, hD', fromBlocks_multiply]
    simp [mul_nonsing_inv _ hMd, mul_nonsing_inv _ hUd, fromBlocks_one]
  have hcomm : Commute (c • M₀ - 1)⁻¹ M₀ := by
    have h : (c • M₀ - 1) * M₀ = M₀ * (c • M₀ - 1) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one]
    calc (c • M₀ - 1)⁻¹ * M₀ = (c • M₀ - 1)⁻¹ * (M₀ * (c • M₀ - 1)) * (c • M₀ - 1)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hUd, Matrix.mul_one]
      _ = (c • M₀ - 1)⁻¹ * ((c • M₀ - 1) * M₀) * (c • M₀ - 1)⁻¹ := by rw [h]
      _ = M₀ * (c • M₀ - 1)⁻¹ := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ hUd, Matrix.one_mul]
  refine ⟨⟨k, l, D * P₀ * R, G * Q₀ * D', Q₀, P₀, c • 1 - M₁⁻¹, (c • M₀ - 1)⁻¹ * M₀,
    ?_, ?_, h₂, h₁, hcomm.isNilpotent_mul_left hn, ?_, ?_⟩⟩
  · calc D * P₀ * R * (G * Q₀ * D') = D * (P₀ * (R * G) * Q₀) * D' := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hRG, Matrix.mul_one, h₁, Matrix.mul_one, hDD']
  · calc G * Q₀ * D' * (D * P₀ * R) = G * (Q₀ * (D' * D) * P₀) * R := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hD'D, Matrix.mul_one, h₂, Matrix.mul_one, hGR]
  · calc D * P₀ * R * E * Q₀ = D * (P₀ * (R * E) * Q₀) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [h₃, hD, fromBlocks_multiply]
        simp [nonsing_inv_mul _ hMd]
  · calc D * P₀ * R * A * Q₀ = D * (c • (P₀ * (R * E) * Q₀) - P₀ * Q₀) := by
          rw [Matrix.mul_assoc (D * P₀) R A, hRA]
          simp only [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
            Matrix.smul_mul, Matrix.mul_one]
      _ = _ := by
        have hsub : c • fromBlocks M₁ 0 0 M₀ - (1 : Matrix (Fin k ⊕ Fin l) (Fin k ⊕ Fin l) K) =
            fromBlocks (c • M₁ - 1) 0 0 (c • M₀ - 1) := by
          ext (i | i) (j | j) <;> simp [Matrix.one_apply]
        rw [h₃, h₁, hsub, hD, fromBlocks_multiply]
        simp [Matrix.mul_sub, nonsing_inv_mul _ hMd, nonsing_inv_mul _ hUd]

/-- **Weierstrass canonical form.** Every regular pencil `s E - A` over an infinite field has a
Weierstrass form: `P (s E - A) Q = diag(s I - J, s N - I)` with `N` nilpotent. -/
@[powerlib_foundation] theorem weierstrass [Infinite K] {E A : Matrix ι ι K} (h : Regular E A) :
    Nonempty (WeierstrassForm E A) := by
  obtain ⟨c, hc⟩ := (regular_iff_exists_det_ne_zero E A).mp h
  exact exists_weierstrassForm_of_det_ne_zero E A hc

namespace WeierstrassForm

variable {E A : Matrix ι ι K} (W : WeierstrassForm E A)

/-- The transformed pencil is `diag(s I - J, s N - I)`. -/
@[powerlib_foundation] theorem pencil_eq (s : K) :
    W.P * (s • E - A) * W.Q = fromBlocks (s • 1 - W.J) 0 0 (s • W.N - 1) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, W.E_eq, W.A_eq]
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

/-- Finite generalized eigenvalues: `det (s E - A) = 0` iff `s` is an eigenvalue of `J`. -/
@[powerlib_foundation] theorem det_eq_zero_iff (s : K) :
    (s • E - A).det = 0 ↔ (s • 1 - W.J).det = 0 := by
  set X := s • E - A
  set B := W.P * X * W.Q
  have hB : B = fromBlocks (s • 1 - W.J) 0 0 (s • W.N - 1) := W.pencil_eq s
  have hNd : IsUnit (s • W.N - 1).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (W.nilpotent.smul s).isUnit_sub_one
  have hdet : B.det = (s • 1 - W.J).det * (s • W.N - 1).det := by
    rw [hB, det_fromBlocks_zero₂₁]
  have hiff : IsUnit X.det ↔ IsUnit B.det := by
    constructor
    · intro hX
      refine isUnit_det_of_right_inverse (B := W.Q' * X⁻¹ * W.P') ?_
      calc B * (W.Q' * X⁻¹ * W.P') = W.P * (X * (W.Q * W.Q') * X⁻¹) * W.P' := by
            simp only [B, Matrix.mul_assoc]
        _ = 1 := by rw [W.Q_mul_Q', Matrix.mul_one, mul_nonsing_inv _ hX, Matrix.mul_one,
              W.P_mul_P']
    · intro hBu
      have hX : X = W.P' * B * W.Q' := by
        calc X = (W.P' * W.P) * X * (W.Q * W.Q') := by
              rw [W.P'_mul_P, W.Q_mul_Q', Matrix.one_mul, Matrix.mul_one]
          _ = W.P' * B * W.Q' := by simp only [B, Matrix.mul_assoc]
      refine isUnit_det_of_right_inverse (B := W.Q * B⁻¹ * W.P) ?_
      calc X * (W.Q * B⁻¹ * W.P) = W.P' * (B * (W.Q' * W.Q) * B⁻¹) * W.P := by
            rw [hX]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [W.Q'_mul_Q, Matrix.mul_one, mul_nonsing_inv _ hBu, Matrix.mul_one,
              W.P'_mul_P]
  rw [← not_iff_not, ← Ne, ← Ne, ← isUnit_iff_ne_zero, ← isUnit_iff_ne_zero, hiff, hdet,
    IsUnit.mul_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, hNd⟩⟩

end WeierstrassForm

/-- Regularity is necessary: over an infinite field a pencil with a Weierstrass form is regular
(`det (s E - A) ≠ 0` wherever `s` is not an eigenvalue of `J`). -/
@[powerlib_foundation] theorem regular_of_weierstrassForm [Infinite K] {E A : Matrix ι ι K}
    (W : WeierstrassForm E A) : Regular E A := by
  have hfin : {x | IsRoot W.J.charpoly x}.Finite := by
    by_contra hinf
    exact W.J.charpoly_monic.ne_zero (eq_zero_of_infinite_isRoot _ hinf)
  obtain ⟨s, -, hs⟩ := (Set.infinite_univ.sdiff hfin).nonempty
  refine (regular_iff_exists_det_ne_zero E A).mpr ⟨s, fun h => hs ?_⟩
  have h' := (W.det_eq_zero_iff s).mp h
  show W.J.charpoly.eval s = 0
  rw [eval_charpoly, ← h']
  congr 1
  ext i j
  simp [Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal_apply]

/-- Over an infinite field: a Weierstrass form exists iff the pencil is regular. -/
@[powerlib_foundation] theorem regular_iff_nonempty_weierstrassForm [Infinite K]
    (E A : Matrix ι ι K) : Regular E A ↔ Nonempty (WeierstrassForm E A) :=
  ⟨weierstrass, fun ⟨W⟩ => regular_of_weierstrassForm W⟩

/-- Correction (missing regularity premise): the singular pencil `s·0 - 0` of size one (the DAE
`0 · x' = 0 · x`) has no Weierstrass form. -/
@[powerlib_foundation] theorem zero_pencil_no_weierstrassForm [Infinite K] :
    IsEmpty (WeierstrassForm (0 : Matrix (Fin 1) (Fin 1) K) 0) := by
  refine ⟨fun W => ?_⟩
  have h := regular_of_weierstrassForm W
  apply h
  simp [pencilPoly]

end powerlib.DAE
