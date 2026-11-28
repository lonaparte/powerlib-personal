import theorem.ParametricResonance.BlockCriticalExponent
import theorem.ParametricResonance.ThirdOrderBoundary

/-! # Exact decoupling of a block monodromy: the critical block to third order

The boundary results for `n`-state cores (`BlockBoundary.block_boundary_stable`,
`BlockCritical.block_boundary_multipliers`) reduce a block monodromy `Φ = [[P, Q], [R, S]]` on
`Fin 2 ⊕ Y` to its critical block through the Schur complement `P + Q(μI − S)⁻¹R`, a function of
`μ`. This file replaces that reduction by an exact similarity. With `P = −I + ΔP`, `I + S`
invertible, `‖(I + S)⁻¹‖ ≤ κ` and `κ‖ΔP‖ + 4κ²‖Q‖‖R‖ ≤ 1/2`, the Riccati equation
`S X − X P = R − X Q X` has exactly one solution in the ball `‖X‖ ≤ 2κ‖R‖`, the fixed point of the
contraction `X ↦ (I + S)⁻¹ (R + X ΔP − X Q X)` (`riccati_small_solution`), and
`T = [[I, 0], [X, I]]` gives `T Φ T⁻¹ = [[P − Q X, Q], [0, S + X Q]]`
(`fromBlocks_conj_triangular`). Hence `charpoly Φ = charpoly (P − Q X) · charpoly (S + X Q)`, for
the real and the complexified matrices (`charpoly_decoupled`, `charpoly_decoupled_complex`), and
`σ(Φ) = σ(P − Q X) ∪ σ(S + X Q)` (`spectrum_decoupled`).

For the expansions of the boundary theorems (`ρ(E) < 1`, all small `ε > 0`, uniform constants):
* second order (`P = −(I + εT M + ε² N) + O(ε³)`, `Q = εQ₁ + O(ε²)`, `R = εR₁ + O(ε²)`,
  `S = E + O(ε)`): `X = O(ε)`, `S + X Q = E + O(ε)` and
  `P − Q X = −(I + εT M + ε² N_eff) + O(ε³)`, `N_eff = N + Q₁ (I + E)⁻¹ R₁`
  (`decoupled_block_second`): the effective matrix of the Schur complement is, to this order, an
  exact diagonal block of a matrix similar to `Φ`;
* third order (`P = −(I + εT M + ε² N + ε³ N₃) + O(ε⁴)`, `Q = εQ₁ + ε²Q₂ + O(ε³)`,
  `R = εR₁ + ε²R₂ + O(ε³)`, `S = E + εS₁ + O(ε²)`): with `G = (I + E)⁻¹`,
  `X = εG R₁ + ε² G (R₂ − S₁ G R₁ − T G R₁ M) + O(ε³)` and
  `P − Q X = −(I + εT M + ε² N_eff + ε³ N_eff3) + O(ε⁴)`,
  `N_eff3 = N₃ + Q₁ G R₂ + Q₂ G R₁ − Q₁ G S₁ G R₁ − T Q₁ G² R₁ M` (`effThird`, `effThird_eq`,
  `decoupled_block_third`);
* the decision of the boundary at third order (`block_boundary_third`): on `det M = 0 > tr M` and
  `mixedDet(M, N_eff) = 0` (the second-order test of `BlockBoundary` void) the sign of
  `K_eff = det N_eff + T mixedDet(M, N_eff3)` decides — `K_eff > 0`: every multiplier inside the
  unit circle, `K_eff < 0`: a multiplier of modulus `> 1` — by `ThirdOrder.critical_jury_three`
  applied to `−(P − Q X)`, while `S + X Q` keeps its spectrum in a disk of radius `c < 1`
  (`lower_block_inside`). For two states (`Y` empty) `N_eff = N`, `N_eff3 = N₃` and this is
  `ThirdOrder.critical_jury_three` itself.

The multiplicity of the multipliers near `−1` (one simple multiplier in each cluster of
`BlockCritical.block_critical_localization`) follows from the same decoupling:
`theorem/ParametricResonance/ClusterMultiplicity.lean`.

Scope.
* Generic: real block matrices on `Z ⊕ Y` (`Z`, `Y` finite; `Z = Fin 2` for the decision) with the
  operator `L∞` norm; `ρ(E) < 1` for the complexified `E`; the stated expansions with constants
  `C` uniform in `ε`; statements for all sufficiently small `ε > 0`, constants existential; the
  eigenvalues of the complexified block matrix (eigenvector form for stability, spectrum for
  instability).
* The `ε`-expansions of the blocks of a particular monodromy (frames, cores, forced orbits) at
  third order are not derived here; this file takes them as hypotheses.
* Generic mathematics; no model family.

Source: the open item of `theorem/ParametricResonance/BlockCriticalExponent.lean` and
`theorem/ParametricResonance/ForcedOrbitCriticalMultipliers.lean` (the multiplicity inside each
cluster) and the third-order boundary of a block monodromy (`mixedDet(M, N_eff) = 0`); the
decoupling of a block operator matrix by a Riccati equation (Stewart–Sun, *Matrix Perturbation
Theory*, Ch. V, §2, invariant subspaces as graphs of solutions of `S X − X P = R − X Q X`; Kato,
*Perturbation Theory for Linear Operators*, Ch. II, the reduction process); the Banach fixed point
theorem (Mathlib `ContractingWith.exists_fixedPoint'`); `ThirdOrder.critical_jury_three`,
`BlockBoundary.stable_block_resolvent`, `BlockCritical.stable_block_lower_inner`.

Results.
* Decoupling: `fromBlocks_conj_triangular`, `charpoly_decoupled`, `charpoly_decoupled_complex`,
  `riccati_small_solution`, `spectrum_decoupled`.
* Expansions: `effThird`, `riccati_eventually`, `effThird_eq`, `decoupled_block_second`,
  `decoupled_block_third`.
* Decision: `lower_block_inside`, `block_boundary_third`.

Corrections.
None: an extension (the case `mixedDet(M, N_eff) = 0` left open by
`BlockBoundary.block_boundary_stable` / `block_boundary_unstable`).

Family and connection conclusions.
None: static evidence on linear periodic systems (Floquet multipliers).
-/

noncomputable section
namespace powerlib.ParametricResonance.BlockDecoupling

open Matrix Complex Set Filter Topology Polynomial
open scoped Matrix.Norms.Operator
open Boundary (mixedDet)

/-! ## The Riccati decoupling -/

section Riccati

variable {Z Y : Type*} [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

/-- **Block triangularization.** If `X` solves the Riccati equation `S X − X P = R − X Q X`, then
`T = [[I, 0], [X, I]]` (inverse `[[I, 0], [−X, I]]`) conjugates `[[P, Q], [R, S]]` to the block
upper triangular `[[P − Q X, Q], [0, S + X Q]]`. -/
@[tmio T, powerlib_foundation] theorem fromBlocks_conj_triangular (P : Matrix Z Z ℝ)
    (Q : Matrix Z Y ℝ) (R : Matrix Y Z ℝ) (S : Matrix Y Y ℝ) {X : Matrix Y Z ℝ}
    (hX : S * X - X * P = R - X * Q * X) :
    fromBlocks 1 0 X 1 * fromBlocks P Q R S * fromBlocks 1 0 (-X) 1 =
      fromBlocks (P - Q * X) Q 0 (S + X * Q) := by
  have hR : R = S * X - X * P + X * Q * X := by rw [hX]; abel
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_one, add_zero,
    zero_add, Matrix.mul_neg]
  rw [hR]
  congr 1 <;> (try simp only [Matrix.add_mul, Matrix.mul_assoc]) <;> abel

/-- **The characteristic polynomial splits.** If `S X − X P = R − X Q X`, then
`charpoly [[P, Q], [R, S]] = charpoly (P − Q X) · charpoly (S + X Q)`. -/
@[tmio T, powerlib_foundation] theorem charpoly_decoupled (P : Matrix Z Z ℝ) (Q : Matrix Z Y ℝ)
    (R : Matrix Y Z ℝ) (S : Matrix Y Y ℝ) {X : Matrix Y Z ℝ}
    (hX : S * X - X * P = R - X * Q * X) :
    (fromBlocks P Q R S).charpoly = (P - Q * X).charpoly * (S + X * Q).charpoly := by
  have h1 : fromBlocks 1 0 X 1 * fromBlocks (1 : Matrix Z Z ℝ) 0 (-X) (1 : Matrix Y Y ℝ) = 1 := by
    rw [fromBlocks_multiply]; simp
  have h2 : fromBlocks 1 0 (-X) 1 * fromBlocks (1 : Matrix Z Z ℝ) 0 X (1 : Matrix Y Y ℝ) = 1 := by
    rw [fromBlocks_multiply]; simp
  let U : (Matrix (Z ⊕ Y) (Z ⊕ Y) ℝ)ˣ := ⟨fromBlocks 1 0 X 1, fromBlocks 1 0 (-X) 1, h1, h2⟩
  have hinv : (U : Matrix (Z ⊕ Y) (Z ⊕ Y) ℝ)⁻¹ = fromBlocks 1 0 (-X) 1 := Matrix.inv_eq_right_inv h1
  have hU : (U : Matrix (Z ⊕ Y) (Z ⊕ Y) ℝ) * fromBlocks P Q R S *
      (U : Matrix (Z ⊕ Y) (Z ⊕ Y) ℝ)⁻¹ = fromBlocks (P - Q * X) Q 0 (S + X * Q) := by
    rw [hinv]; exact fromBlocks_conj_triangular P Q R S hX
  rw [← Matrix.charpoly_units_conj U (fromBlocks P Q R S), hU, charpoly_fromBlocks_zero₂₁]

/-- The complexified form of `charpoly_decoupled`. -/
@[tmio T, powerlib_foundation] theorem charpoly_decoupled_complex (P : Matrix Z Z ℝ)
    (Q : Matrix Z Y ℝ) (R : Matrix Y Z ℝ) (S : Matrix Y Y ℝ) {X : Matrix Y Z ℝ}
    (hX : S * X - X * P = R - X * Q * X) :
    ((fromBlocks P Q R S).map (algebraMap ℝ ℂ)).charpoly =
      ((P - Q * X).map (algebraMap ℝ ℂ)).charpoly *
        ((S + X * Q).map (algebraMap ℝ ℂ)).charpoly := by
  rw [Matrix.charpoly_map, Matrix.charpoly_map, Matrix.charpoly_map, charpoly_decoupled P Q R S hX,
    Polynomial.map_mul]

/-- **The small solution of the Riccati equation (Banach fixed point).** Let `I + S` be invertible
with `‖(I + S)⁻¹‖ ≤ κ`, and `κ ‖P + I‖ + 4 κ² ‖Q‖ ‖R‖ ≤ 1/2`. Then `S X − X P = R − X Q X` has a
solution `X` with `‖X‖ ≤ 2κ‖R‖`, and it is the only solution in that ball: `X` is the fixed point
of the contraction `X ↦ (I + S)⁻¹ (R + X (P + I) − X Q X)` (constant `1/2`) of the closed ball of
radius `2κ‖R‖`. -/
@[tmio T, powerlib_foundation] theorem riccati_small_solution {P : Matrix Z Z ℝ}
    {Q : Matrix Z Y ℝ} {R : Matrix Y Z ℝ} {S : Matrix Y Y ℝ} {κ : ℝ}
    (hS : IsUnit (1 + S).det) (hκ : ‖(1 + S)⁻¹‖ ≤ κ)
    (hsmall : κ * ‖P + 1‖ + 4 * κ ^ 2 * (‖Q‖ * ‖R‖) ≤ 1 / 2) :
    ∃ X : Matrix Y Z ℝ, ‖X‖ ≤ 2 * κ * ‖R‖ ∧ S * X - X * P = R - X * Q * X ∧
      ∀ X' : Matrix Y Z ℝ, ‖X'‖ ≤ 2 * κ * ‖R‖ → S * X' - X' * P = R - X' * Q * X' → X' = X := by
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans hκ
  set G := (1 + S)⁻¹ with hG
  set ρ := 2 * κ * ‖R‖ with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  set f : Matrix Y Z ℝ → Matrix Y Z ℝ := fun X => G * (R + X * (P + 1) - X * Q * X) with hf
  -- fixed points of `f` are the solutions
  have hfix : ∀ X, f X = X ↔ S * X - X * P = R - X * Q * X := by
    intro X
    constructor
    · intro h
      have e : (1 + S) * f X = R + X * (P + 1) - X * Q * X := by
        rw [hf]; dsimp only
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hS, Matrix.one_mul]
      rw [h, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one] at e
      have : S * X - X * P = (X + S * X) - (X * P + X) := by abel
      rw [this, e]; abel
    · intro h
      have e : R + X * (P + 1) - X * Q * X = (1 + S) * X := by
        rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one]
        have : R = S * X - X * P + X * Q * X := by rw [h]; abel
        rw [this]; abel
      rw [hf]; dsimp only
      rw [e, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hS, Matrix.one_mul]
  -- the contraction estimate on the ball
  have hlip : ∀ X X', ‖X‖ ≤ ρ → ‖X'‖ ≤ ρ → ‖f X - f X'‖ ≤ 2⁻¹ * ‖X - X'‖ := by
    intro X X' hX hX'
    have e : f X - f X' = G * ((X - X') * (P + 1) - ((X - X') * Q * X + X' * Q * (X - X'))) := by
      rw [hf]; dsimp only
      rw [← Matrix.mul_sub]
      congr 1
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      abel
    rw [e]
    have hQX : ‖(X - X') * Q * X + X' * Q * (X - X')‖ ≤ 2 * ρ * ‖Q‖ * ‖X - X'‖ := by
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖(X - X') * Q * X‖ ≤ ‖X - X'‖ * ‖Q‖ * ρ :=
        (linfty_opNorm_mul _ _).trans (mul_le_mul ((linfty_opNorm_mul _ _)) hX (norm_nonneg _)
          (by positivity))
      have h2 : ‖X' * Q * (X - X')‖ ≤ ρ * ‖Q‖ * ‖X - X'‖ :=
        (linfty_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right ((linfty_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right hX' (norm_nonneg _))) (norm_nonneg _))
      nlinarith [h1, h2]
    calc ‖G * ((X - X') * (P + 1) - ((X - X') * Q * X + X' * Q * (X - X')))‖
        ≤ κ * (‖X - X'‖ * ‖P + 1‖ + 2 * ρ * ‖Q‖ * ‖X - X'‖) := by
          refine (linfty_opNorm_mul _ _).trans (mul_le_mul hκ ?_ (norm_nonneg _) hκ0)
          exact (norm_sub_le _ _).trans (add_le_add (linfty_opNorm_mul _ _) hQX)
      _ = (κ * ‖P + 1‖ + 4 * κ ^ 2 * (‖Q‖ * ‖R‖)) * ‖X - X'‖ := by rw [hρ]; ring
      _ ≤ 2⁻¹ * ‖X - X'‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _); norm_num; linarith
  -- `f` maps the ball into itself
  have hball : ∀ X, ‖X‖ ≤ ρ → ‖f X‖ ≤ ρ := by
    intro X hX
    have h0 : f 0 = G * R := by rw [hf]; simp
    have hf0 : ‖f 0‖ ≤ κ * ‖R‖ := by
      rw [h0]; exact (linfty_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right hκ (norm_nonneg _))
    have hl := hlip X 0 hX (by rw [norm_zero]; exact hρ0)
    rw [sub_zero] at hl
    calc ‖f X‖ = ‖(f X - f 0) + f 0‖ := by rw [sub_add_cancel]
      _ ≤ 2⁻¹ * ‖X‖ + κ * ‖R‖ := (norm_add_le _ _).trans (add_le_add hl hf0)
      _ ≤ 2⁻¹ * ρ + κ * ‖R‖ := by gcongr
      _ = ρ := by rw [hρ]; ring
  have hmaps : MapsTo f (Metric.closedBall 0 ρ) (Metric.closedBall 0 ρ) := by
    intro X hX
    rw [Metric.mem_closedBall, dist_zero_right] at hX ⊢
    exact hball X hX
  have hcontr : ContractingWith 2⁻¹ (hmaps.restrict f _ _) := by
    refine ⟨by rw [inv_lt_one₀ (by norm_num)]; norm_num, ?_⟩
    apply LipschitzOnWith.mapsToRestrict
    refine LipschitzOnWith.of_dist_le_mul fun X hX X' hX' => ?_
    rw [Metric.mem_closedBall, dist_zero_right] at hX hX'
    rw [dist_eq_norm, dist_eq_norm]
    have : ((2⁻¹ : NNReal) : ℝ) = 2⁻¹ := by norm_num
    rw [this]
    exact hlip X X' hX hX'
  obtain ⟨X, hXb, hXfix, -, -⟩ := hcontr.exists_fixedPoint' Metric.isClosed_closedBall.isComplete
    hmaps (Metric.mem_closedBall_self hρ0) (edist_ne_top _ _)
  rw [Metric.mem_closedBall, dist_zero_right] at hXb
  have hX : f X = X := hXfix
  refine ⟨X, hXb, (hfix X).mp hX, fun X' hX'b hX' => ?_⟩
  have h1 : f X' = X' := (hfix X').mpr hX'
  have h2 := hlip X' X hX'b hXb
  rw [h1, hX] at h2
  have : ‖X' - X‖ ≤ 0 := by linarith [norm_nonneg (X' - X)]
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

/-- The complex spectrum of a decoupled block matrix is the union of the spectra of its diagonal
blocks after the decoupling: `σ([[P, Q], [R, S]]) = σ(P − Q X) ∪ σ(S + X Q)` for a solution `X` of
`S X − X P = R − X Q X`. -/
@[tmio T, powerlib_foundation] theorem spectrum_decoupled (P : Matrix Z Z ℝ) (Q : Matrix Z Y ℝ)
    (R : Matrix Y Z ℝ) (S : Matrix Y Y ℝ) {X : Matrix Y Z ℝ}
    (hX : S * X - X * P = R - X * Q * X) :
    spectrum ℂ ((fromBlocks P Q R S).map (algebraMap ℝ ℂ)) =
      spectrum ℂ ((P - Q * X).map (algebraMap ℝ ℂ)) ∪
        spectrum ℂ ((S + X * Q).map (algebraMap ℝ ℂ)) := by
  ext μ
  rw [Set.mem_union, Matrix.mem_spectrum_iff_isRoot_charpoly,
    Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.mem_spectrum_iff_isRoot_charpoly,
    charpoly_decoupled_complex P Q R S hX, Polynomial.root_mul]

end Riccati

/-! ## The decoupled blocks of a perturbed monodromy -/

section Expansion

variable {Z Y : Type*} [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

/-- **The third-order effective matrix of the critical block.** With `G = (I + E)⁻¹`,
`N_eff3 = N₃ + Q₁ G R₂ + Q₂ G R₁ − Q₁ G S₁ G R₁ − T Q₁ G² R₁ M`: the `ε³` coefficient of the
decoupled critical block `−(P − Q X)` for `P = −(I + εT M + ε² N + ε³ N₃) + O(ε⁴)`,
`Q = εQ₁ + ε²Q₂ + O(ε³)`, `R = εR₁ + ε²R₂ + O(ε³)`, `S = E + εS₁ + O(ε²)`
(`decoupled_block_third`). -/
def effThird (T : ℝ) (M N₃ : Matrix Z Z ℝ) (Q₁ Q₂ : Matrix Z Y ℝ) (R₁ R₂ : Matrix Y Z ℝ)
    (E S₁ : Matrix Y Y ℝ) : Matrix Z Z ℝ :=
  N₃ + Q₁ * (1 + E)⁻¹ * R₂ + Q₂ * (1 + E)⁻¹ * R₁ - Q₁ * (1 + E)⁻¹ * S₁ * (1 + E)⁻¹ * R₁ -
    T • (Q₁ * (1 + E)⁻¹ * (1 + E)⁻¹ * R₁ * M)

/-- `I + S` is uniformly invertible near a stable `E`. -/
@[tmio T, powerlib_foundation] private theorem one_add_resolvent {E : Matrix Y Y ℝ}
    (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1) :
    ∃ κ η : ℝ, 0 ≤ κ ∧ 0 < η ∧ ∀ S : Matrix Y Y ℝ, ‖S - E‖ ≤ η →
      IsUnit (1 + S).det ∧ ‖(1 + S)⁻¹‖ ≤ κ := by
  obtain ⟨K, η, hK, hη, hres⟩ := BlockBoundary.stable_block_resolvent hρ
  refine ⟨K, η, hK, hη, fun S hS => ?_⟩
  obtain ⟨hU, hB⟩ := (hres S hS).1 (-1) (by norm_num)
  have e : (-1 : ℝ) • (1 : Matrix Y Y ℝ) - S = -(1 + S) := by rw [neg_one_smul]; abel
  have hinv := BlockBoundary.neg_one_sub_inv hU
  refine ⟨?_, ?_⟩
  · rw [e, Matrix.det_neg] at hU
    exact (IsUnit.mul_iff.mp hU).2
  · rw [hinv, norm_neg] at hB
    exact hB

/-- **The Riccati solution for small `ε`.** If `ρ(E) < 1`, then for all small `ε > 0` every block
matrix with `‖P + I‖ ≤ aε`, `‖Q‖ ≤ qε`, `‖R‖ ≤ bε`, `‖S − E‖ ≤ sε` has `I + S` invertible with
`‖(I + S)⁻¹‖ ≤ κ` and a solution `X` of `S X − X P = R − X Q X` with `‖X‖ ≤ 2κbε`
(`riccati_small_solution`); `I + E` is invertible. -/
@[tmio T, powerlib_foundation] theorem riccati_eventually {E : Matrix Y Y ℝ}
    (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1) {a q b s : ℝ} (ha : 0 ≤ a)
    (hq : 0 ≤ q) (hb : 0 ≤ b) (hs : 0 ≤ s) :
    ∃ κ ε₀ : ℝ, 0 ≤ κ ∧ 0 < ε₀ ∧ IsUnit (1 + E).det ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ (P : Matrix Z Z ℝ) (Q : Matrix Z Y ℝ) (R : Matrix Y Z ℝ) (S : Matrix Y Y ℝ),
      ‖P + 1‖ ≤ a * ε → ‖Q‖ ≤ q * ε → ‖R‖ ≤ b * ε → ‖S - E‖ ≤ s * ε →
      IsUnit (1 + S).det ∧ ‖(1 + S)⁻¹‖ ≤ κ ∧
        ∃ X : Matrix Y Z ℝ, S * X - X * P = R - X * Q * X ∧ ‖X‖ ≤ 2 * κ * b * ε := by
  obtain ⟨κ, η, hκ, hη, hres⟩ := one_add_resolvent hρ
  set L := κ * a + 4 * κ ^ 2 * (q * b) with hL
  have hL0 : 0 ≤ L := by positivity
  refine ⟨κ, min 1 (min (η / (s + 1)) (1 / (2 * L + 1))), hκ,
    lt_min one_pos (lt_min (by positivity) (by positivity)),
    (hres E (by rw [sub_self, norm_zero]; exact hη.le)).1,
    fun ε hε hε₀ P Q R S hP hQ hR hS => ?_⟩
  have hε1 : ε ≤ 1 := hε₀.trans (min_le_left _ _)
  have hεη : ε ≤ η / (s + 1) := hε₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεL : ε ≤ 1 / (2 * L + 1) := hε₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hSE : ‖S - E‖ ≤ η := by
    refine hS.trans ?_
    rw [le_div_iff₀ (by positivity)] at hεη
    nlinarith
  obtain ⟨hU, hB⟩ := hres S hSE
  refine ⟨hU, hB, ?_⟩
  have hsmall : κ * ‖P + 1‖ + 4 * κ ^ 2 * (‖Q‖ * ‖R‖) ≤ 1 / 2 := by
    have h1 : κ * ‖P + 1‖ ≤ κ * a * ε := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hP hκ
    have h2 : ‖Q‖ * ‖R‖ ≤ q * b * ε := by
      calc ‖Q‖ * ‖R‖ ≤ (q * ε) * (b * ε) := mul_le_mul hQ hR (norm_nonneg _) (by positivity)
        _ = q * b * ε * ε := by ring
        _ ≤ q * b * ε * 1 := by gcongr
        _ = q * b * ε := by ring
    have h3 : 4 * κ ^ 2 * (‖Q‖ * ‖R‖) ≤ 4 * κ ^ 2 * (q * b) * ε := by
      rw [mul_assoc (4 * κ ^ 2) (q * b)]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h4 : L * ε ≤ 1 / 2 := by
      rw [le_div_iff₀ (by positivity)] at hεL
      nlinarith
    rw [hL] at h4
    nlinarith
  obtain ⟨X, hXb, hX, -⟩ := riccati_small_solution hU hB hsmall
  refine ⟨X, hX, hXb.trans ?_⟩
  calc 2 * κ * ‖R‖ ≤ 2 * κ * (b * ε) := mul_le_mul_of_nonneg_left hR (by positivity)
    _ = 2 * κ * b * ε := by ring

/-- The residual estimate of the Riccati equation: `‖X − W‖ ≤ κ ‖R + X(P + I) − X Q X − (I + S) W‖`
for a solution `X` and any `W`. -/
@[tmio T, powerlib_foundation] private theorem riccati_residual {P : Matrix Z Z ℝ}
    {Q : Matrix Z Y ℝ} {R : Matrix Y Z ℝ} {S : Matrix Y Y ℝ} {X : Matrix Y Z ℝ} {κ : ℝ}
    (hS : IsUnit (1 + S).det) (hκ : ‖(1 + S)⁻¹‖ ≤ κ) (hX : S * X - X * P = R - X * Q * X)
    (W : Matrix Y Z ℝ) :
    ‖X - W‖ ≤ κ * ‖R + X * (P + 1) - X * Q * X - (1 + S) * W‖ := by
  have e1 : R + X * (P + 1) - X * Q * X = (1 + S) * X := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one]
    have : R = S * X - X * P + X * Q * X := by rw [hX]; abel
    rw [this]; abel
  have e2 : X - W = (1 + S)⁻¹ * (R + X * (P + 1) - X * Q * X - (1 + S) * W) := by
    rw [e1, ← Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hS, Matrix.one_mul]
  rw [e2]
  exact (linfty_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right hκ (norm_nonneg _))

@[tmio T, powerlib_foundation] private theorem norm_smul_of_nonneg' {a b : Type*} [Fintype a]
    [Fintype b] {c : ℝ} (hc : 0 ≤ c) (A : Matrix a b ℝ) : ‖c • A‖ = c * ‖A‖ := by
  rw [norm_smul, Real.norm_of_nonneg hc]

/-- The first-order term of the Riccati solution: `X = ε (I + E)⁻¹ R₁ + O(ε²)`. -/
@[tmio T, powerlib_foundation] private theorem riccati_first {P : Matrix Z Z ℝ}
    {Q : Matrix Z Y ℝ} {R R₁ : Matrix Y Z ℝ} {S E : Matrix Y Y ℝ} {X : Matrix Y Z ℝ}
    {ε κ a q b s x : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hκ0 : 0 ≤ κ) (hq : 0 ≤ q) (hx : 0 ≤ x)
    (hS : IsUnit (1 + S).det) (hκ : ‖(1 + S)⁻¹‖ ≤ κ)
    (hE : IsUnit (1 + E).det) (hX : S * X - X * P = R - X * Q * X) (hXb : ‖X‖ ≤ x * ε)
    (hP : ‖P + 1‖ ≤ a * ε) (hQ : ‖Q‖ ≤ q * ε) (hR : ‖R - ε • R₁‖ ≤ b * ε ^ 2)
    (hSE : ‖S - E‖ ≤ s * ε) :
    ‖X - ε • ((1 + E)⁻¹ * R₁)‖ ≤
      κ * (b + x * a + x ^ 2 * q + s * ‖(1 + E)⁻¹ * R₁‖) * ε ^ 2 := by
  set X₁ := (1 + E)⁻¹ * R₁ with hX₁
  have hEX : (1 + E) * X₁ = R₁ := by
    rw [hX₁, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hE, Matrix.one_mul]
  have e : R + X * (P + 1) - X * Q * X - (1 + S) * (ε • X₁) =
      (R - ε • R₁) + X * (P + 1) - X * Q * X - ε • ((S - E) * X₁) := by
    have h1 : (1 + S) * (ε • X₁) = ε • ((1 + E) * X₁) + ε • ((S - E) * X₁) := by
      rw [Matrix.mul_smul, ← smul_add, ← Matrix.add_mul]; congr 2; abel
    rw [h1, hEX]; abel
  refine (riccati_residual hS hκ hX _).trans ?_
  rw [e, mul_assoc κ, mul_comm _ (ε ^ 2)]
  refine mul_le_mul_of_nonneg_left ?_ hκ0
  have h1 : ‖X * (P + 1)‖ ≤ x * a * ε ^ 2 := by
    calc ‖X * (P + 1)‖ ≤ (x * ε) * (a * ε) :=
          (linfty_opNorm_mul _ _).trans (mul_le_mul hXb hP (norm_nonneg _) (by positivity))
      _ = x * a * ε ^ 2 := by ring
  have h2 : ‖X * Q * X‖ ≤ x ^ 2 * q * ε ^ 2 := by
    calc ‖X * Q * X‖ ≤ (x * ε) * (q * ε) * (x * ε) :=
          (linfty_opNorm_mul _ _).trans (mul_le_mul ((linfty_opNorm_mul _ _).trans
            (mul_le_mul hXb hQ (norm_nonneg _) (by positivity))) hXb (norm_nonneg _)
            (by positivity))
      _ = x ^ 2 * q * ε ^ 2 * ε := by ring
      _ ≤ x ^ 2 * q * ε ^ 2 * 1 := by gcongr
      _ = x ^ 2 * q * ε ^ 2 := by ring
  have h3 : ‖ε • ((S - E) * X₁)‖ ≤ s * ‖X₁‖ * ε ^ 2 := by
    rw [norm_smul_of_nonneg' hε.le]
    calc ε * ‖(S - E) * X₁‖ ≤ ε * (s * ε * ‖X₁‖) :=
          mul_le_mul_of_nonneg_left ((linfty_opNorm_mul _ _).trans
            (mul_le_mul_of_nonneg_right hSE (norm_nonneg _))) hε.le
      _ = s * ‖X₁‖ * ε ^ 2 := by ring
  calc ‖(R - ε • R₁) + X * (P + 1) - X * Q * X - ε • ((S - E) * X₁)‖
      ≤ ‖R - ε • R₁‖ + ‖X * (P + 1)‖ + ‖X * Q * X‖ + ‖ε • ((S - E) * X₁)‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ b * ε ^ 2 + x * a * ε ^ 2 + x ^ 2 * q * ε ^ 2 + s * ‖X₁‖ * ε ^ 2 := by
        gcongr
    _ = ε ^ 2 * (b + x * a + x ^ 2 * q + s * ‖X₁‖) := by ring

/-- The second-order term of the Riccati solution:
`X = ε X₁ + ε² X₂ + O(ε³)`, `X₁ = (I + E)⁻¹ R₁`, `X₂ = (I + E)⁻¹ (R₂ − S₁ X₁ − T X₁ M)`. -/
@[tmio T, powerlib_foundation] private theorem riccati_second {P M : Matrix Z Z ℝ}
    {Q : Matrix Z Y ℝ} {R R₁ R₂ : Matrix Y Z ℝ} {S E S₁ : Matrix Y Y ℝ} {X : Matrix Y Z ℝ}
    {ε T κ C a₂ q x x₁ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hκ0 : 0 ≤ κ) (hC : 0 ≤ C)
    (hq : 0 ≤ q) (hx : 0 ≤ x) (hS : IsUnit (1 + S).det) (hκ : ‖(1 + S)⁻¹‖ ≤ κ)
    (hE : IsUnit (1 + E).det) (hX : S * X - X * P = R - X * Q * X) (hXb : ‖X‖ ≤ x * ε)
    (hX1 : ‖X - ε • ((1 + E)⁻¹ * R₁)‖ ≤ x₁ * ε ^ 2) (hP : ‖P + 1 + (ε * T) • M‖ ≤ a₂ * ε ^ 2)
    (hQ : ‖Q‖ ≤ q * ε) (hR : ‖R - ε • R₁ - ε ^ 2 • R₂‖ ≤ C * ε ^ 3)
    (hSE : ‖S - E - ε • S₁‖ ≤ C * ε ^ 2) :
    ‖X - ε • ((1 + E)⁻¹ * R₁) -
        ε ^ 2 • ((1 + E)⁻¹ * (R₂ - S₁ * ((1 + E)⁻¹ * R₁) - T • ((1 + E)⁻¹ * R₁ * M)))‖ ≤
      κ * (C + x * a₂ + |T| * ‖M‖ * x₁ + x ^ 2 * q +
        ‖S₁‖ * ‖(1 + E)⁻¹ * (R₂ - S₁ * ((1 + E)⁻¹ * R₁) - T • ((1 + E)⁻¹ * R₁ * M))‖ +
        C * (‖(1 + E)⁻¹ * R₁‖ +
          ‖(1 + E)⁻¹ * (R₂ - S₁ * ((1 + E)⁻¹ * R₁) - T • ((1 + E)⁻¹ * R₁ * M))‖)) * ε ^ 3 := by
  set X₁ := (1 + E)⁻¹ * R₁ with hX₁
  set X₂ := (1 + E)⁻¹ * (R₂ - S₁ * X₁ - T • (X₁ * M)) with hX₂
  have hEX₁ : (1 + E) * X₁ = R₁ := by
    rw [hX₁, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hE, Matrix.one_mul]
  have hEX₂ : (1 + E) * X₂ = R₂ - S₁ * X₁ - T • (X₁ * M) := by
    rw [hX₂, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hE, Matrix.one_mul]
  set D := S - E - ε • S₁ with hD
  have h1S : 1 + S = (1 + E) + ε • S₁ + D := by rw [hD]; abel
  have e : R + X * (P + 1) - X * Q * X - (1 + S) * (ε • X₁ + ε ^ 2 • X₂) =
      (R - ε • R₁ - ε ^ 2 • R₂) + X * (P + 1 + (ε * T) • M) - (ε * T) • ((X - ε • X₁) * M) -
        X * Q * X - ε ^ 3 • (S₁ * X₂) - D * (ε • X₁ + ε ^ 2 • X₂) := by
    rw [h1S, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add (1 + E), Matrix.mul_smul,
      Matrix.mul_smul, hEX₁, hEX₂]
    simp only [Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, smul_sub,
      smul_smul]
    module
  have e2 : X - ε • X₁ - ε ^ 2 • X₂ = X - (ε • X₁ + ε ^ 2 • X₂) := by abel
  rw [e2]
  refine (riccati_residual hS hκ hX _).trans ?_
  rw [e, mul_assoc κ]
  refine mul_le_mul_of_nonneg_left ?_ hκ0
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  have h1 : ‖X * (P + 1 + (ε * T) • M)‖ ≤ x * a₂ * ε ^ 3 := by
    calc _ ≤ (x * ε) * (a₂ * ε ^ 2) :=
          (linfty_opNorm_mul _ _).trans (mul_le_mul hXb hP (norm_nonneg _) (by positivity))
      _ = x * a₂ * ε ^ 3 := by ring
  have h2 : ‖(ε * T) • ((X - ε • X₁) * M)‖ ≤ |T| * ‖M‖ * x₁ * ε ^ 3 := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hε]
    calc ε * |T| * ‖(X - ε • X₁) * M‖ ≤ ε * |T| * (x₁ * ε ^ 2 * ‖M‖) :=
          mul_le_mul_of_nonneg_left ((linfty_opNorm_mul _ _).trans
            (mul_le_mul_of_nonneg_right hX1 (norm_nonneg _))) (by positivity)
      _ = |T| * ‖M‖ * x₁ * ε ^ 3 := by ring
  have h3 : ‖X * Q * X‖ ≤ x ^ 2 * q * ε ^ 3 := by
    calc ‖X * Q * X‖ ≤ (x * ε) * (q * ε) * (x * ε) :=
          (linfty_opNorm_mul _ _).trans (mul_le_mul ((linfty_opNorm_mul _ _).trans
            (mul_le_mul hXb hQ (norm_nonneg _) (by positivity))) hXb (norm_nonneg _)
            (by positivity))
      _ = x ^ 2 * q * ε ^ 3 := by ring
  have h4 : ‖ε ^ 3 • (S₁ * X₂)‖ ≤ ‖S₁‖ * ‖X₂‖ * ε ^ 3 := by
    rw [norm_smul_of_nonneg' (by positivity)]
    calc ε ^ 3 * ‖S₁ * X₂‖ ≤ ε ^ 3 * (‖S₁‖ * ‖X₂‖) :=
          mul_le_mul_of_nonneg_left (linfty_opNorm_mul _ _) (by positivity)
      _ = _ := by ring
  have h5 : ‖D * (ε • X₁ + ε ^ 2 • X₂)‖ ≤ C * (‖X₁‖ + ‖X₂‖) * ε ^ 3 := by
    have hw : ‖ε • X₁ + ε ^ 2 • X₂‖ ≤ (‖X₁‖ + ‖X₂‖) * ε := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul_of_nonneg' hε.le, norm_smul_of_nonneg' (by positivity)]
      nlinarith [norm_nonneg X₁, norm_nonneg X₂]
    calc ‖D * (ε • X₁ + ε ^ 2 • X₂)‖ ≤ (C * ε ^ 2) * ((‖X₁‖ + ‖X₂‖) * ε) :=
          (linfty_opNorm_mul _ _).trans (mul_le_mul hSE hw (norm_nonneg _) (by positivity))
      _ = C * (‖X₁‖ + ‖X₂‖) * ε ^ 3 := by ring
  calc ‖(R - ε • R₁ - ε ^ 2 • R₂) + X * (P + 1 + (ε * T) • M) - (ε * T) • ((X - ε • X₁) * M) -
        X * Q * X - ε ^ 3 • (S₁ * X₂) - D * (ε • X₁ + ε ^ 2 • X₂)‖
      ≤ ‖R - ε • R₁ - ε ^ 2 • R₂‖ + ‖X * (P + 1 + (ε * T) • M)‖ +
          ‖(ε * T) • ((X - ε • X₁) * M)‖ + ‖X * Q * X‖ + ‖ε ^ 3 • (S₁ * X₂)‖ +
          ‖D * (ε • X₁ + ε ^ 2 • X₂)‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_add_le _ _
    _ ≤ C * ε ^ 3 + x * a₂ * ε ^ 3 + |T| * ‖M‖ * x₁ * ε ^ 3 + x ^ 2 * q * ε ^ 3 +
          ‖S₁‖ * ‖X₂‖ * ε ^ 3 + C * (‖X₁‖ + ‖X₂‖) * ε ^ 3 := by gcongr
    _ = (C + x * a₂ + |T| * ‖M‖ * x₁ + x ^ 2 * q + ‖S₁‖ * ‖X₂‖ +
          C * (‖X₁‖ + ‖X₂‖)) * ε ^ 3 := by ring

omit [DecidableEq Z] in
/-- `effThird` in terms of the Riccati coefficients `X₁ = (I + E)⁻¹ R₁`,
`X₂ = (I + E)⁻¹ (R₂ − S₁ X₁ − T X₁ M)`: `N_eff3 = N₃ + Q₁ X₂ + Q₂ X₁`. -/
@[tmio T, powerlib_foundation] theorem effThird_eq (T : ℝ) (M N₃ : Matrix Z Z ℝ)
    (Q₁ Q₂ : Matrix Z Y ℝ) (R₁ R₂ : Matrix Y Z ℝ) (E S₁ : Matrix Y Y ℝ) :
    effThird T M N₃ Q₁ Q₂ R₁ R₂ E S₁ =
      N₃ + Q₁ * ((1 + E)⁻¹ * (R₂ - S₁ * ((1 + E)⁻¹ * R₁) - T • ((1 + E)⁻¹ * R₁ * M))) +
        Q₂ * ((1 + E)⁻¹ * R₁) := by
  simp only [effThird, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_assoc]
  abel

omit [DecidableEq Y] in
/-- The critical block to second order from the first-order Riccati coefficient. -/
@[tmio T, powerlib_foundation] private theorem crit_second {P M N : Matrix Z Z ℝ}
    {Q Q₁ : Matrix Z Y ℝ} {X X₁ : Matrix Y Z ℝ} {ε T C x x₁ : ℝ} (hε : 0 < ε)
    (hC : 0 ≤ C) (hP : ‖P + 1 + (ε * T) • M + ε ^ 2 • N‖ ≤ C * ε ^ 3)
    (hQ : ‖Q - ε • Q₁‖ ≤ C * ε ^ 2) (hXb : ‖X‖ ≤ x * ε) (hX1 : ‖X - ε • X₁‖ ≤ x₁ * ε ^ 2) :
    ‖P - Q * X + 1 + (ε * T) • M + ε ^ 2 • (N + Q₁ * X₁)‖ ≤
      (C + C * x + ‖Q₁‖ * x₁) * ε ^ 3 := by
  have e : P - Q * X + 1 + (ε * T) • M + ε ^ 2 • (N + Q₁ * X₁) =
      (P + 1 + (ε * T) • M + ε ^ 2 • N) - (Q - ε • Q₁) * X - ε • (Q₁ * (X - ε • X₁)) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      smul_sub, smul_smul]
    module
  rw [e]
  have h1 : ‖(Q - ε • Q₁) * X‖ ≤ C * x * ε ^ 3 := by
    calc _ ≤ (C * ε ^ 2) * (x * ε) :=
          (linfty_opNorm_mul _ _).trans (mul_le_mul hQ hXb (norm_nonneg _) (by positivity))
      _ = C * x * ε ^ 3 := by ring
  have h2 : ‖ε • (Q₁ * (X - ε • X₁))‖ ≤ ‖Q₁‖ * x₁ * ε ^ 3 := by
    rw [norm_smul_of_nonneg' hε.le]
    calc ε * ‖Q₁ * (X - ε • X₁)‖ ≤ ε * (‖Q₁‖ * (x₁ * ε ^ 2)) :=
          mul_le_mul_of_nonneg_left ((linfty_opNorm_mul _ _).trans
            (mul_le_mul_of_nonneg_left hX1 (norm_nonneg _))) hε.le
      _ = ‖Q₁‖ * x₁ * ε ^ 3 := by ring
  calc _ ≤ ‖P + 1 + (ε * T) • M + ε ^ 2 • N‖ + ‖(Q - ε • Q₁) * X‖ +
        ‖ε • (Q₁ * (X - ε • X₁))‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ C * ε ^ 3 + C * x * ε ^ 3 + ‖Q₁‖ * x₁ * ε ^ 3 := by gcongr
    _ = (C + C * x + ‖Q₁‖ * x₁) * ε ^ 3 := by ring

omit [DecidableEq Y] in
/-- The critical block to third order from the second-order Riccati coefficients. -/
@[tmio T, powerlib_foundation] private theorem crit_third {P M N N₃ : Matrix Z Z ℝ}
    {Q Q₁ Q₂ : Matrix Z Y ℝ} {X X₁ X₂ : Matrix Y Z ℝ} {ε T C x x₂ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hC : 0 ≤ C)
    (hP : ‖P + 1 + (ε * T) • M + ε ^ 2 • N + ε ^ 3 • N₃‖ ≤ C * ε ^ 4)
    (hQ : ‖Q - ε • Q₁ - ε ^ 2 • Q₂‖ ≤ C * ε ^ 3) (hXb : ‖X‖ ≤ x * ε)
    (hX2 : ‖X - ε • X₁ - ε ^ 2 • X₂‖ ≤ x₂ * ε ^ 3) :
    ‖P - Q * X + 1 + (ε * T) • M + ε ^ 2 • (N + Q₁ * X₁) + ε ^ 3 • (N₃ + Q₁ * X₂ + Q₂ * X₁)‖ ≤
      (C + C * x + (‖Q₁‖ + ‖Q₂‖) * x₂ + ‖Q₂‖ * ‖X₂‖) * ε ^ 4 := by
  have e : P - Q * X + 1 + (ε * T) • M + ε ^ 2 • (N + Q₁ * X₁) +
      ε ^ 3 • (N₃ + Q₁ * X₂ + Q₂ * X₁) =
      (P + 1 + (ε * T) • M + ε ^ 2 • N + ε ^ 3 • N₃) - (Q - ε • Q₁ - ε ^ 2 • Q₂) * X -
        (ε • Q₁ + ε ^ 2 • Q₂) * (X - ε • X₁ - ε ^ 2 • X₂) - ε ^ 4 • (Q₂ * X₂) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_add, smul_smul]
    module
  rw [e]
  have h1 : ‖(Q - ε • Q₁ - ε ^ 2 • Q₂) * X‖ ≤ C * x * ε ^ 4 := by
    calc _ ≤ (C * ε ^ 3) * (x * ε) :=
          (linfty_opNorm_mul _ _).trans (mul_le_mul hQ hXb (norm_nonneg _) (by positivity))
      _ = C * x * ε ^ 4 := by ring
  have h2 : ‖(ε • Q₁ + ε ^ 2 • Q₂) * (X - ε • X₁ - ε ^ 2 • X₂)‖ ≤
      (‖Q₁‖ + ‖Q₂‖) * x₂ * ε ^ 4 := by
    have hw : ‖ε • Q₁ + ε ^ 2 • Q₂‖ ≤ (‖Q₁‖ + ‖Q₂‖) * ε := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul_of_nonneg' hε.le, norm_smul_of_nonneg' (by positivity)]
      have hε2 : ε ^ 2 ≤ ε := by nlinarith
      nlinarith [norm_nonneg Q₁, norm_nonneg Q₂]
    calc _ ≤ ((‖Q₁‖ + ‖Q₂‖) * ε) * (x₂ * ε ^ 3) :=
          (linfty_opNorm_mul _ _).trans (mul_le_mul hw hX2 (norm_nonneg _) (by positivity))
      _ = (‖Q₁‖ + ‖Q₂‖) * x₂ * ε ^ 4 := by ring
  have h3 : ‖ε ^ 4 • (Q₂ * X₂)‖ ≤ ‖Q₂‖ * ‖X₂‖ * ε ^ 4 := by
    rw [norm_smul_of_nonneg' (by positivity)]
    calc ε ^ 4 * ‖Q₂ * X₂‖ ≤ ε ^ 4 * (‖Q₂‖ * ‖X₂‖) :=
          mul_le_mul_of_nonneg_left (linfty_opNorm_mul _ _) (by positivity)
      _ = _ := by ring
  calc _ ≤ ‖P + 1 + (ε * T) • M + ε ^ 2 • N + ε ^ 3 • N₃‖ + ‖(Q - ε • Q₁ - ε ^ 2 • Q₂) * X‖ +
        ‖(ε • Q₁ + ε ^ 2 • Q₂) * (X - ε • X₁ - ε ^ 2 • X₂)‖ + ‖ε ^ 4 • (Q₂ * X₂)‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ C * ε ^ 4 + C * x * ε ^ 4 + (‖Q₁‖ + ‖Q₂‖) * x₂ * ε ^ 4 + ‖Q₂‖ * ‖X₂‖ * ε ^ 4 := by
        gcongr
    _ = (C + C * x + (‖Q₁‖ + ‖Q₂‖) * x₂ + ‖Q₂‖ * ‖X₂‖) * ε ^ 4 := by ring

/-- `ε^k ≤ ε^j` for `j ≤ k` and `0 ≤ ε ≤ 1`. -/
@[tmio T, powerlib_foundation] private theorem pow_le_pow' {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    {j k : ℕ} (hjk : j ≤ k) : ε ^ k ≤ ε ^ j :=
  pow_le_pow_of_le_one h0 h1 hjk

set_option maxHeartbeats 1000000 in
/-- **The exactly decoupled critical block to second order.** Let `ρ(E) < 1` and
`P = −(I + εT M + ε² N) + O(ε³)`, `Q = εQ₁ + O(ε²)`, `R = εR₁ + O(ε²)`, `S = E + O(ε)` (constant
`C`). There is `K` such that for all small `ε > 0` the Riccati equation `S X − X P = R − X Q X`
has a solution with `‖X‖ ≤ Kε` (so that `[[P, Q], [R, S]]` is similar to
`[[P − Q X, Q], [0, S + X Q]]`, `fromBlocks_conj_triangular`), `‖S + X Q − E‖ ≤ Kε`, and the
decoupled critical block is
`P − Q X = −(I + εT M + ε² N_eff) + O(ε³)`, `N_eff = N + Q₁ (I + E)⁻¹ R₁` (error `≤ Kε³`): the
Schur-complement matrix of `BlockBoundary.block_boundary_stable` is, to this order, an exact
diagonal block of a matrix similar to the monodromy. -/
@[tmio T, powerlib_foundation] theorem decoupled_block_second {T : ℝ} {M N : Matrix Z Z ℝ}
    {Q₁ : Matrix Z Y ℝ} {R₁ : Matrix Y Z ℝ} {E : Matrix Y Y ℝ}
    (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1) {C : ℝ} (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (P : Matrix Z Z ℝ) (Q : Matrix Z Y ℝ)
      (R : Matrix Y Z ℝ) (S : Matrix Y Y ℝ),
      ‖P + 1 + (ε * T) • M + ε ^ 2 • N‖ ≤ C * ε ^ 3 → ‖Q - ε • Q₁‖ ≤ C * ε ^ 2 →
      ‖R - ε • R₁‖ ≤ C * ε ^ 2 → ‖S - E‖ ≤ C * ε →
      ∃ X : Matrix Y Z ℝ, S * X - X * P = R - X * Q * X ∧ ‖X‖ ≤ K * ε ∧
        ‖S + X * Q - E‖ ≤ K * ε ∧
        ‖P - Q * X + 1 + (ε * T) • M + ε ^ 2 • (N + Q₁ * (1 + E)⁻¹ * R₁)‖ ≤ K * ε ^ 3 := by
  set a := C + |T| * ‖M‖ + ‖N‖ with ha
  set q := C + ‖Q₁‖ with hq
  set b := C + ‖R₁‖ with hb
  have ha0 : 0 ≤ a := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hb0 : 0 ≤ b := by positivity
  obtain ⟨κ, ε₀, hκ, hε₀, hE, hric⟩ := riccati_eventually (Z := Z) hρ ha0 hq0 hb0 hC
  set x := 2 * κ * b with hx
  have hx0 : 0 ≤ x := by positivity
  set X₁ := (1 + E)⁻¹ * R₁ with hX₁
  set x₁ := κ * (C + x * a + x ^ 2 * q + C * ‖X₁‖) with hx₁
  have hx₁0 : 0 ≤ x₁ := by positivity
  set Kc := C + C * x + ‖Q₁‖ * x₁ with hKc
  set Ks := C + x * q with hKs
  have hKc0 : 0 ≤ Kc := by positivity
  have hKs0 : 0 ≤ Ks := by positivity
  refine ⟨x + Ks + Kc, by positivity, ?_⟩
  filter_upwards [BlockAveraging.eventually_lt_nhdsGT (lt_min hε₀ one_pos)] with ε ⟨hε, hεlt⟩
  intro P Q R S hP hQ hR hS
  have hεe : ε ≤ ε₀ := (hεlt.trans_le (min_le_left _ _)).le
  have hε1 : ε ≤ 1 := (hεlt.trans_le (min_le_right _ _)).le
  have p21 := pow_le_pow' hε.le hε1 (show 1 ≤ 2 by norm_num)
  have p32 := pow_le_pow' hε.le hε1 (show 2 ≤ 3 by norm_num)
  have p31 := pow_le_pow' hε.le hε1 (show 1 ≤ 3 by norm_num)
  rw [pow_one] at p21 p31
  -- first-order bounds
  have hP1 : ‖P + 1‖ ≤ a * ε := by
    have e : P + 1 = (P + 1 + (ε * T) • M + ε ^ 2 • N) - (ε * T) • M - ε ^ 2 • N := by abel
    rw [e]
    calc _ ≤ ‖P + 1 + (ε * T) • M + ε ^ 2 • N‖ + ‖(ε * T) • M‖ + ‖ε ^ 2 • N‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ = ‖P + 1 + (ε * T) • M + ε ^ 2 • N‖ + ε * |T| * ‖M‖ + ε ^ 2 * ‖N‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hε,
            norm_smul_of_nonneg' (by positivity)]
      _ ≤ C * ε + ε * |T| * ‖M‖ + ε * ‖N‖ := by
          gcongr
          · exact hP.trans (mul_le_mul_of_nonneg_left p31 hC)
      _ = a * ε := by rw [ha]; ring
  have hQ1 : ‖Q‖ ≤ q * ε := by
    have e : Q = (Q - ε • Q₁) + ε • Q₁ := by abel
    rw [e]
    calc _ ≤ ‖Q - ε • Q₁‖ + ‖ε • Q₁‖ := norm_add_le _ _
      _ ≤ C * ε + ε * ‖Q₁‖ := by
          rw [norm_smul_of_nonneg' hε.le]
          gcongr
          exact hQ.trans (mul_le_mul_of_nonneg_left p21 hC)
      _ = q * ε := by rw [hq]; ring
  have hR1 : ‖R‖ ≤ b * ε := by
    have e : R = (R - ε • R₁) + ε • R₁ := by abel
    rw [e]
    calc _ ≤ ‖R - ε • R₁‖ + ‖ε • R₁‖ := norm_add_le _ _
      _ ≤ C * ε + ε * ‖R₁‖ := by
          rw [norm_smul_of_nonneg' hε.le]
          gcongr
          exact hR.trans (mul_le_mul_of_nonneg_left p21 hC)
      _ = b * ε := by rw [hb]; ring
  obtain ⟨hU, hκS, X, hX, hXb⟩ := hric ε hε hεe P Q R S hP1 hQ1 hR1 hS
  have hXb' : ‖X‖ ≤ x * ε := by rw [hx]; exact hXb
  have h1 := riccati_first hε hε1 hκ hq0 hx0 hU hκS hE hX hXb' hP1 hQ1 hR hS
  rw [← hX₁, ← hx₁] at h1
  have h2 := crit_second hε hC hP hQ hXb' h1
  rw [← hKc] at h2
  refine ⟨X, hX, hXb'.trans (mul_le_mul_of_nonneg_right (by linarith) hε.le), ?_, ?_⟩
  · have e : S + X * Q - E = (S - E) + X * Q := by abel
    rw [e]
    calc _ ≤ ‖S - E‖ + ‖X‖ * ‖Q‖ := (norm_add_le _ _).trans (add_le_add le_rfl
          (linfty_opNorm_mul _ _))
      _ ≤ C * ε + (x * ε) * (q * ε) := by
          gcongr
      _ = (C + x * q * ε) * ε := by ring
      _ ≤ (C + x * q * 1) * ε := by gcongr
      _ = Ks * ε := by rw [hKs]; ring
      _ ≤ (x + Ks + Kc) * ε := mul_le_mul_of_nonneg_right (by linarith) hε.le
  · have e : N + Q₁ * (1 + E)⁻¹ * R₁ = N + Q₁ * X₁ := by rw [hX₁, Matrix.mul_assoc]
    rw [e]
    exact h2.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

set_option maxHeartbeats 2000000 in
/-- **The exactly decoupled critical block to third order.** Let `ρ(E) < 1` and
`P = −(I + εT M + ε² N + ε³ N₃) + O(ε⁴)`, `Q = εQ₁ + ε²Q₂ + O(ε³)`, `R = εR₁ + ε²R₂ + O(ε³)`,
`S = E + εS₁ + O(ε²)` (constant `C`). There is `K` such that for all small `ε > 0` the Riccati
equation `S X − X P = R − X Q X` has a solution with `‖X‖ ≤ Kε`, `‖S + X Q − E‖ ≤ Kε`, and the
decoupled critical block is
`P − Q X = −(I + εT M + ε² N_eff + ε³ N_eff3) + O(ε⁴)` (error `≤ Kε⁴`), with
`N_eff = N + Q₁ G R₁` and `N_eff3 = effThird T M N₃ Q₁ Q₂ R₁ R₂ E S₁
= N₃ + Q₁ G R₂ + Q₂ G R₁ − Q₁ G S₁ G R₁ − T Q₁ G² R₁ M`, `G = (I + E)⁻¹`. (The solution is
`X = εG R₁ + ε² G (R₂ − S₁ G R₁ − T G R₁ M) + O(ε³)`, from the Riccati residual.) -/
@[tmio T, powerlib_foundation] theorem decoupled_block_third {T : ℝ} {M N N₃ : Matrix Z Z ℝ}
    {Q₁ Q₂ : Matrix Z Y ℝ} {R₁ R₂ : Matrix Y Z ℝ} {E S₁ : Matrix Y Y ℝ}
    (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1) {C : ℝ} (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (P : Matrix Z Z ℝ) (Q : Matrix Z Y ℝ)
      (R : Matrix Y Z ℝ) (S : Matrix Y Y ℝ),
      ‖P + 1 + (ε * T) • M + ε ^ 2 • N + ε ^ 3 • N₃‖ ≤ C * ε ^ 4 →
      ‖Q - ε • Q₁ - ε ^ 2 • Q₂‖ ≤ C * ε ^ 3 → ‖R - ε • R₁ - ε ^ 2 • R₂‖ ≤ C * ε ^ 3 →
      ‖S - E - ε • S₁‖ ≤ C * ε ^ 2 →
      ∃ X : Matrix Y Z ℝ, S * X - X * P = R - X * Q * X ∧ ‖X‖ ≤ K * ε ∧
        ‖S + X * Q - E‖ ≤ K * ε ∧
        ‖P - Q * X + 1 + (ε * T) • M + ε ^ 2 • (N + Q₁ * (1 + E)⁻¹ * R₁) +
          ε ^ 3 • effThird T M N₃ Q₁ Q₂ R₁ R₂ E S₁‖ ≤ K * ε ^ 4 := by
  set a₂ := C + ‖N‖ + ‖N₃‖ with ha₂
  set a := a₂ + |T| * ‖M‖ with ha
  set q := C + ‖Q₁‖ + ‖Q₂‖ with hq
  set b₂ := C + ‖R₂‖ with hb₂
  set b := b₂ + ‖R₁‖ with hb
  set s := C + ‖S₁‖ with hs
  have ha₂0 : 0 ≤ a₂ := by positivity
  have ha0 : 0 ≤ a := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hb₂0 : 0 ≤ b₂ := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hs0 : 0 ≤ s := by positivity
  obtain ⟨κ, ε₀, hκ, hε₀, hE, hric⟩ := riccati_eventually (Z := Z) hρ ha0 hq0 hb0 hs0
  set x := 2 * κ * b with hx
  have hx0 : 0 ≤ x := by positivity
  set X₁ := (1 + E)⁻¹ * R₁ with hX₁
  set X₂ := (1 + E)⁻¹ * (R₂ - S₁ * X₁ - T • (X₁ * M)) with hX₂
  set x₁ := κ * (b₂ + x * a + x ^ 2 * q + s * ‖X₁‖) with hx₁
  have hx₁0 : 0 ≤ x₁ := by positivity
  set x₂ := κ * (C + x * a₂ + |T| * ‖M‖ * x₁ + x ^ 2 * q + ‖S₁‖ * ‖X₂‖ +
    C * (‖X₁‖ + ‖X₂‖)) with hx₂
  have hx₂0 : 0 ≤ x₂ := by positivity
  set Kc := C + C * x + (‖Q₁‖ + ‖Q₂‖) * x₂ + ‖Q₂‖ * ‖X₂‖ with hKc
  set Ks := s + x * q with hKs
  have hKc0 : 0 ≤ Kc := by positivity
  have hKs0 : 0 ≤ Ks := by positivity
  refine ⟨x + Ks + Kc, by positivity, ?_⟩
  filter_upwards [BlockAveraging.eventually_lt_nhdsGT (lt_min hε₀ one_pos)] with ε ⟨hε, hεlt⟩
  intro P Q R S hP hQ hR hS
  have hεe : ε ≤ ε₀ := (hεlt.trans_le (min_le_left _ _)).le
  have hε1 : ε ≤ 1 := (hεlt.trans_le (min_le_right _ _)).le
  have p21 := pow_le_pow' hε.le hε1 (show 1 ≤ 2 by norm_num)
  have p32 := pow_le_pow' hε.le hε1 (show 2 ≤ 3 by norm_num)
  have p42 := pow_le_pow' hε.le hε1 (show 2 ≤ 4 by norm_num)
  rw [pow_one] at p21
  -- the bounds used by the Riccati estimates
  have hP2 : ‖P + 1 + (ε * T) • M‖ ≤ a₂ * ε ^ 2 := by
    have e : P + 1 + (ε * T) • M =
        (P + 1 + (ε * T) • M + ε ^ 2 • N + ε ^ 3 • N₃) - ε ^ 2 • N - ε ^ 3 • N₃ := by abel
    rw [e]
    calc _ ≤ ‖P + 1 + (ε * T) • M + ε ^ 2 • N + ε ^ 3 • N₃‖ + ‖ε ^ 2 • N‖ + ‖ε ^ 3 • N₃‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ = ‖P + 1 + (ε * T) • M + ε ^ 2 • N + ε ^ 3 • N₃‖ + ε ^ 2 * ‖N‖ + ε ^ 3 * ‖N₃‖ := by
          rw [norm_smul_of_nonneg' (by positivity), norm_smul_of_nonneg' (by positivity)]
      _ ≤ C * ε ^ 2 + ε ^ 2 * ‖N‖ + ε ^ 2 * ‖N₃‖ := by
          gcongr
          exact hP.trans (mul_le_mul_of_nonneg_left p42 hC)
      _ = a₂ * ε ^ 2 := by rw [ha₂]; ring
  have hP1 : ‖P + 1‖ ≤ a * ε := by
    have e : P + 1 = (P + 1 + (ε * T) • M) - (ε * T) • M := by abel
    rw [e]
    calc _ ≤ ‖P + 1 + (ε * T) • M‖ + ‖(ε * T) • M‖ := norm_sub_le _ _
      _ = ‖P + 1 + (ε * T) • M‖ + ε * |T| * ‖M‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hε]
      _ ≤ a₂ * ε + ε * |T| * ‖M‖ := by
          gcongr
          exact hP2.trans (mul_le_mul_of_nonneg_left p21 ha₂0)
      _ = a * ε := by rw [ha]; ring
  have hQ1 : ‖Q‖ ≤ q * ε := by
    have e : Q = (Q - ε • Q₁ - ε ^ 2 • Q₂) + ε • Q₁ + ε ^ 2 • Q₂ := by abel
    rw [e]
    calc _ ≤ ‖Q - ε • Q₁ - ε ^ 2 • Q₂‖ + ‖ε • Q₁‖ + ‖ε ^ 2 • Q₂‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ C * ε + ε * ‖Q₁‖ + ε * ‖Q₂‖ := by
          rw [norm_smul_of_nonneg' hε.le, norm_smul_of_nonneg' (by positivity)]
          gcongr
          · exact hQ.trans (mul_le_mul_of_nonneg_left
              ((pow_le_pow' hε.le hε1 (show 1 ≤ 3 by norm_num)).trans_eq (pow_one ε)) hC)
      _ = q * ε := by rw [hq]; ring
  have hR2 : ‖R - ε • R₁‖ ≤ b₂ * ε ^ 2 := by
    have e : R - ε • R₁ = (R - ε • R₁ - ε ^ 2 • R₂) + ε ^ 2 • R₂ := by abel
    rw [e]
    calc _ ≤ ‖R - ε • R₁ - ε ^ 2 • R₂‖ + ‖ε ^ 2 • R₂‖ := norm_add_le _ _
      _ ≤ C * ε ^ 2 + ε ^ 2 * ‖R₂‖ := by
          rw [norm_smul_of_nonneg' (by positivity)]
          gcongr
          exact hR.trans (mul_le_mul_of_nonneg_left p32 hC)
      _ = b₂ * ε ^ 2 := by rw [hb₂]; ring
  have hR1 : ‖R‖ ≤ b * ε := by
    have e : R = (R - ε • R₁) + ε • R₁ := by abel
    rw [e]
    calc _ ≤ ‖R - ε • R₁‖ + ‖ε • R₁‖ := norm_add_le _ _
      _ ≤ b₂ * ε + ε * ‖R₁‖ := by
          rw [norm_smul_of_nonneg' hε.le]
          gcongr
          exact hR2.trans (mul_le_mul_of_nonneg_left p21 hb₂0)
      _ = b * ε := by rw [hb]; ring
  have hS1 : ‖S - E‖ ≤ s * ε := by
    have e : S - E = (S - E - ε • S₁) + ε • S₁ := by abel
    rw [e]
    calc _ ≤ ‖S - E - ε • S₁‖ + ‖ε • S₁‖ := norm_add_le _ _
      _ ≤ C * ε + ε * ‖S₁‖ := by
          rw [norm_smul_of_nonneg' hε.le]
          gcongr
          exact hS.trans (mul_le_mul_of_nonneg_left p21 hC)
      _ = s * ε := by rw [hs]; ring
  obtain ⟨hU, hκS, X, hX, hXb⟩ := hric ε hε hεe P Q R S hP1 hQ1 hR1 hS1
  have hXb' : ‖X‖ ≤ x * ε := by rw [hx]; exact hXb
  have h1 := riccati_first hε hε1 hκ hq0 hx0 hU hκS hE hX hXb' hP1 hQ1 hR2 hS1
  rw [← hX₁, ← hx₁] at h1
  have h2 := riccati_second hε hε1 hκ hC hq0 hx0 hU hκS hE hX hXb' h1 hP2 hQ1 hR hS
  rw [← hX₁, ← hX₂, ← hx₂] at h2
  have h3 := crit_third (N := N) (N₃ := N₃) (Q₁ := Q₁) (Q₂ := Q₂) (X₁ := X₁) hε hε1 hC hP hQ
    hXb' h2
  rw [← hKc] at h3
  refine ⟨X, hX, hXb'.trans (mul_le_mul_of_nonneg_right (by linarith) hε.le), ?_, ?_⟩
  · have e : S + X * Q - E = (S - E) + X * Q := by abel
    rw [e]
    calc _ ≤ ‖S - E‖ + ‖X‖ * ‖Q‖ := (norm_add_le _ _).trans (add_le_add le_rfl
          (linfty_opNorm_mul _ _))
      _ ≤ s * ε + (x * ε) * (q * ε) := by
          gcongr
      _ = (s + x * q * ε) * ε := by ring
      _ ≤ (s + x * q * 1) * ε := by gcongr
      _ = Ks * ε := by rw [hKs]; ring
      _ ≤ (x + Ks + Kc) * ε := mul_le_mul_of_nonneg_right (by linarith) hε.le
  · have e1 : N + Q₁ * (1 + E)⁻¹ * R₁ = N + Q₁ * X₁ := by rw [hX₁, Matrix.mul_assoc]
    have e2 : effThird T M N₃ Q₁ Q₂ R₁ R₂ E S₁ = N₃ + Q₁ * X₂ + Q₂ * X₁ := by
      rw [effThird_eq, hX₂, hX₁]
    rw [e1, e2]
    exact h3.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

end Expansion

/-! ## The third-order decision of the boundary of a block monodromy -/

section Verdict

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- A statement for every family on `(0, 1]` (the form of `ThirdOrder.critical_jury_three`) gives
the uniform statement: for all small `ε` and every admissible datum. -/
@[tmio T, powerlib_foundation] private theorem eventually_forall_of_families {α : Type*}
    [Nonempty α] {B G : ℝ → α → Prop} (hB : ∀ ε, 0 < ε → ε ≤ 1 → ∃ a, B ε a)
    (h : ∀ F : ℝ → α, (∀ ε, 0 < ε → ε ≤ 1 → B ε (F ε)) → ∀ᶠ ε in 𝓝[>] (0 : ℝ), G ε (F ε)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a, B ε a → G ε a := by
  classical
  by_contra hne
  rw [Filter.not_eventually] at hne
  let F : ℝ → α := fun ε => if h1 : ∃ a, B ε a ∧ ¬ G ε a then h1.choose
    else if h2 : ∃ a, B ε a then h2.choose else Classical.arbitrary α
  have hF : ∀ ε, 0 < ε → ε ≤ 1 → B ε (F ε) := by
    intro ε h0 h1
    simp only [F]
    split_ifs with h1' h2'
    · exact h1'.choose_spec.1
    · exact h2'.choose_spec
    · exact absurd (hB ε h0 h1) h2'
  obtain ⟨ε, hε1, hε2⟩ := (hne.and_eventually (h F hF)).exists
  have h1' : ∃ a, B ε a ∧ ¬ G ε a := by
    push Not at hε1
    obtain ⟨a, ha, hna⟩ := hε1
    exact ⟨a, ha, hna⟩
  have e : F ε = h1'.choose := by simp only [F]; rw [dite_eq_left h1']
  rw [e] at hε2
  exact h1'.choose_spec.2 hε2

/-- The spectrum of a perturbed stable block stays in a disk of radius `c < 1`. -/
@[tmio T, powerlib_foundation] theorem lower_block_inside {E : Matrix Y Y ℝ}
    (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1) :
    ∃ c η : ℝ, 0 < c ∧ c < 1 ∧ 0 < η ∧ ∀ S : Matrix Y Y ℝ, ‖S - E‖ ≤ η →
      ∀ μ ∈ spectrum ℂ (S.map (algebraMap ℝ ℂ)), ‖μ‖ < c := by
  obtain ⟨c, K, η, hc0, hc1, hK, hη, hlow⟩ := BlockCritical.stable_block_lower_inner hρ
  refine ⟨c, η, hc0, hc1, hη, fun S hS μ hμ => ?_⟩
  obtain ⟨y, hy, hSy⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp hμ
  by_contra hcon
  have h := hlow S hS μ (not_lt.mp hcon) y
  rw [hSy, sub_self, norm_zero, mul_zero] at h
  exact hy (norm_le_zero_iff.mp h)

@[tmio T, powerlib_foundation] private theorem neg_mem_spectrum_neg {Z : Type*} [Fintype Z]
    [DecidableEq Z] (A : Matrix Z Z ℝ) (μ : ℂ) :
    -μ ∈ spectrum ℂ ((-A).map (algebraMap ℝ ℂ)) ↔ μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) := by
  have hneg : (-A).map (algebraMap ℝ ℂ) = -(A.map (algebraMap ℝ ℂ)) := by ext i j; simp
  rw [hneg, ← spectrum.neg_eq, Set.mem_neg, neg_neg]

set_option maxHeartbeats 2000000 in
/-- **The boundary of a block monodromy at third order.** Let `Φ = [[P, Q], [R, S]]` on
`Fin 2 ⊕ Y` with `P = −(I + εT M + ε² N + ε³ N₃) + O(ε⁴)`, `Q = εQ₁ + ε²Q₂ + O(ε³)`,
`R = εR₁ + ε²R₂ + O(ε³)`, `S = E + εS₁ + O(ε²)` (`T > 0`, constant `C`), `ρ(E) < 1`, the critical
block on the first-order boundary `det M = 0 > tr M`, and the second-order test void:
`mixedDet(M, N_eff) = 0`, `N_eff = N + Q₁(I + E)⁻¹R₁`. With
`N_eff3 = effThird T M N₃ Q₁ Q₂ R₁ R₂ E S₁` the sign of
`K_eff = det N_eff + T mixedDet(M, N_eff3)` decides for all small `ε > 0`: `K_eff > 0` gives every
eigenvalue of the complexified `Φ` inside the unit circle, `K_eff < 0` an eigenvalue of modulus
`> 1`. (The exact decoupling `decoupled_block_third`: `−(P − Q X) = I + εT M + ε² N_eff +
ε³ N_eff3 + O(ε⁴)` is decided by `ThirdOrder.critical_jury_three`, and `S + X Q` keeps its
spectrum inside the circle, `lower_block_inside`; `spectrum_decoupled`.) -/
@[tmio T, powerlib_foundation] theorem block_boundary_third {T : ℝ} (hT : 0 < T)
    {M N N₃ : Matrix (Fin 2) (Fin 2) ℝ} {Q₁ Q₂ : Matrix (Fin 2) Y ℝ}
    {R₁ R₂ : Matrix Y (Fin 2) ℝ} {E S₁ : Matrix Y Y ℝ}
    (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1) (hdet : M.det = 0)
    (htr : M.trace < 0) (hmix : mixedDet M (N + Q₁ * (1 + E)⁻¹ * R₁) = 0) {C : ℝ} (hC : 0 ≤ C) :
    (0 < (N + Q₁ * (1 + E)⁻¹ * R₁).det + T * mixedDet M (effThird T M N₃ Q₁ Q₂ R₁ R₂ E S₁) →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (P : Matrix (Fin 2) (Fin 2) ℝ) (Q : Matrix (Fin 2) Y ℝ)
        (R : Matrix Y (Fin 2) ℝ) (S : Matrix Y Y ℝ),
        ‖P + 1 + (ε * T) • M + ε ^ 2 • N + ε ^ 3 • N₃‖ ≤ C * ε ^ 4 →
        ‖Q - ε • Q₁ - ε ^ 2 • Q₂‖ ≤ C * ε ^ 3 → ‖R - ε • R₁ - ε ^ 2 • R₂‖ ≤ C * ε ^ 3 →
        ‖S - E - ε • S₁‖ ≤ C * ε ^ 2 →
        ∀ (μ : ℂ) (v : Fin 2 ⊕ Y → ℂ), v ≠ 0 →
          (fromBlocks P Q R S).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1) ∧
    ((N + Q₁ * (1 + E)⁻¹ * R₁).det + T * mixedDet M (effThird T M N₃ Q₁ Q₂ R₁ R₂ E S₁) < 0 →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (P : Matrix (Fin 2) (Fin 2) ℝ) (Q : Matrix (Fin 2) Y ℝ)
        (R : Matrix Y (Fin 2) ℝ) (S : Matrix Y Y ℝ),
        ‖P + 1 + (ε * T) • M + ε ^ 2 • N + ε ^ 3 • N₃‖ ≤ C * ε ^ 4 →
        ‖Q - ε • Q₁ - ε ^ 2 • Q₂‖ ≤ C * ε ^ 3 → ‖R - ε • R₁ - ε ^ 2 • R₂‖ ≤ C * ε ^ 3 →
        ‖S - E - ε • S₁‖ ≤ C * ε ^ 2 →
        ∃ μ ∈ spectrum ℂ ((fromBlocks P Q R S).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) := by
  classical
  obtain ⟨K, hK, hdec⟩ := decoupled_block_third (Z := Fin 2) (T := T) (M := M) (N := N)
    (N₃ := N₃) (Q₁ := Q₁) (Q₂ := Q₂) (R₁ := R₁) (R₂ := R₂) (S₁ := S₁) hρ hC
  obtain ⟨c, η, hc0, hc1, hη, hin⟩ := lower_block_inside hρ
  set Neff := N + Q₁ * (1 + E)⁻¹ * R₁ with hNeff
  set N3 := effThird T M N₃ Q₁ Q₂ R₁ R₂ E S₁ with hN3
  -- the admissible data and the decoupling property
  let B : ℝ → Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) Y ℝ × Matrix Y (Fin 2) ℝ ×
      Matrix Y Y ℝ → Prop := fun ε a =>
    ‖a.1 + 1 + (ε * T) • M + ε ^ 2 • N + ε ^ 3 • N₃‖ ≤ C * ε ^ 4 ∧
    ‖a.2.1 - ε • Q₁ - ε ^ 2 • Q₂‖ ≤ C * ε ^ 3 ∧ ‖a.2.2.1 - ε • R₁ - ε ^ 2 • R₂‖ ≤ C * ε ^ 3 ∧
    ‖a.2.2.2 - E - ε • S₁‖ ≤ C * ε ^ 2
  let D : ℝ → Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) Y ℝ × Matrix Y (Fin 2) ℝ ×
      Matrix Y Y ℝ → Matrix Y (Fin 2) ℝ → Prop := fun ε a X =>
    a.2.2.2 * X - X * a.1 = a.2.2.1 - X * a.2.1 * X ∧ ‖a.2.2.2 + X * a.2.1 - E‖ ≤ K * ε ∧
    ‖a.1 - a.2.1 * X + 1 + (ε * T) • M + ε ^ 2 • Neff + ε ^ 3 • N3‖ ≤ K * ε ^ 4
  have hBdef : ∀ ε, 0 < ε → ε ≤ 1 → ∃ a, B ε a := fun ε hε _ =>
    ⟨(-(1 + (ε * T) • M + ε ^ 2 • N + ε ^ 3 • N₃), ε • Q₁ + ε ^ 2 • Q₂, ε • R₁ + ε ^ 2 • R₂,
      E + ε • S₁), by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only
      · rw [show -(1 + (ε * T) • M + ε ^ 2 • N + ε ^ 3 • N₃) + 1 + (ε * T) • M + ε ^ 2 • N +
          ε ^ 3 • N₃ = 0 by abel, norm_zero]; positivity
      · rw [show ε • Q₁ + ε ^ 2 • Q₂ - ε • Q₁ - ε ^ 2 • Q₂ = 0 by abel, norm_zero]; positivity
      · rw [show ε • R₁ + ε ^ 2 • R₂ - ε • R₁ - ε ^ 2 • R₂ = 0 by abel, norm_zero]; positivity
      · rw [show E + ε • S₁ - E - ε • S₁ = 0 by abel, norm_zero]; positivity⟩
  have hdecF : ∀ F : ℝ → Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) Y ℝ × Matrix Y (Fin 2) ℝ ×
      Matrix Y Y ℝ, (∀ ε, 0 < ε → ε ≤ 1 → B ε (F ε)) →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ X, D ε (F ε) X := by
    intro F hF
    filter_upwards [hdec, BlockAveraging.eventually_lt_nhdsGT one_pos] with ε h ⟨h0, h1⟩
    obtain ⟨b1, b2, b3, b4⟩ := hF ε h0 h1.le
    obtain ⟨X, hX, -, hS', hc⟩ := h _ _ _ _ b1 b2 b3 b4
    exact ⟨X, hX, hS', hc⟩
  -- the critical blocks as a family on `(0, 1]`
  have hfam : ∀ F : ℝ → Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) Y ℝ × Matrix Y (Fin 2) ℝ ×
      Matrix Y Y ℝ, ∃ Pc : ℝ → Matrix (Fin 2) (Fin 2) ℝ,
      (∀ ε, 0 < ε → ε ≤ 1 →
        ‖Pc ε - 1 - (ε * T) • M - ε ^ 2 • Neff - ε ^ 3 • N3‖ ≤ K * ε ^ 4) ∧
      ∀ ε, (∃ X, D ε (F ε) X) → ∃ X, D ε (F ε) X ∧ Pc ε = -((F ε).1 - (F ε).2.1 * X) := by
    intro F
    refine ⟨fun ε => if h : ∃ X, D ε (F ε) X then -((F ε).1 - (F ε).2.1 * h.choose)
      else 1 + (ε * T) • M + ε ^ 2 • Neff + ε ^ 3 • N3, fun ε h0 _ => ?_, fun ε h => ?_⟩
    · dsimp only
      split_ifs with h
      · have hb := h.choose_spec.2.2
        rw [show -((F ε).1 - (F ε).2.1 * h.choose) - 1 - (ε * T) • M - ε ^ 2 • Neff -
            ε ^ 3 • N3 = -((F ε).1 - (F ε).2.1 * h.choose + 1 + (ε * T) • M + ε ^ 2 • Neff +
            ε ^ 3 • N3) by abel, norm_neg]
        exact hb
      · rw [show 1 + (ε * T) • M + ε ^ 2 • Neff + ε ^ 3 • N3 - 1 - (ε * T) • M - ε ^ 2 • Neff -
            ε ^ 3 • N3 = 0 by abel, norm_zero]; positivity
    · exact ⟨h.choose, h.choose_spec, by dsimp only; rw [dite_eq_left h]⟩
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), K * ε ≤ η := by
    filter_upwards [BlockAveraging.eventually_lt_nhdsGT (show 0 < η / (K + 1) by positivity)]
      with ε ⟨h0, h1⟩
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith
  refine ⟨fun hKp => ?_, fun hKn => ?_⟩
  · have main : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a, B ε a →
        ∀ (μ : ℂ) (v : Fin 2 ⊕ Y → ℂ), v ≠ 0 →
          (fromBlocks a.1 a.2.1 a.2.2.1 a.2.2.2).map (algebraMap ℝ ℂ) *ᵥ v = μ • v →
            ‖μ‖ < 1 := by
      refine eventually_forall_of_families hBdef fun F hF => ?_
      obtain ⟨Pc, hPc, hPcF⟩ := hfam F
      have hj := (ThirdOrder.critical_jury_three hT hK hPc hdet htr hmix).1 hKp
      filter_upwards [hj, hdecF F hF, hsmall] with ε hstab hX hKε
      obtain ⟨X, ⟨hRic, hS', -⟩, hPcX⟩ := hPcF ε hX
      intro μ v hv hΦv
      have hμ := LTI.mem_spectrum_iff_exists_eigvec.mpr ⟨v, hv, hΦv⟩
      rw [spectrum_decoupled _ _ _ _ hRic] at hμ
      rcases hμ with hμ | hμ
      · rw [← neg_mem_spectrum_neg, ← hPcX] at hμ
        obtain ⟨w, hw, hPw⟩ := LTI.mem_spectrum_iff_exists_eigvec.mp hμ
        have := hstab (-μ) w hw hPw
        rwa [norm_neg] at this
      · exact (hin _ (hS'.trans hKε) μ hμ).trans hc1
    filter_upwards [main] with ε h P Q R S h1 h2 h3 h4
    exact h (P, Q, R, S) ⟨h1, h2, h3, h4⟩
  · have main : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a, B ε a →
        ∃ μ ∈ spectrum ℂ ((fromBlocks a.1 a.2.1 a.2.2.1 a.2.2.2).map (algebraMap ℝ ℂ)),
          1 < ‖μ‖ := by
      refine eventually_forall_of_families hBdef fun F hF => ?_
      obtain ⟨Pc, hPc, hPcF⟩ := hfam F
      have hj := (ThirdOrder.critical_jury_three hT hK hPc hdet htr hmix).2 hKn
      filter_upwards [hj, hdecF F hF] with ε hun hX
      obtain ⟨X, ⟨hRic, -, -⟩, hPcX⟩ := hPcF ε hX
      obtain ⟨μ, hμ, hμ1⟩ := hun
      rw [hPcX, ← neg_neg μ, neg_mem_spectrum_neg] at hμ
      refine ⟨-μ, ?_, by rwa [norm_neg]⟩
      rw [spectrum_decoupled _ _ _ _ hRic]
      exact Or.inl hμ
    filter_upwards [main] with ε h P Q R S h1 h2 h3 h4
    exact h (P, Q, R, S) ⟨h1, h2, h3, h4⟩

end Verdict

end powerlib.ParametricResonance.BlockDecoupling
