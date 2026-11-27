import theorem.ParametricResonance.ThreeStateCore

/-! # Block cores on the first-order boundary: the effective matrix for every stable block

`BlockBoundary.averagingB_boundary` decides the first-order boundary of the `n`-state 2:1 core
`BlockAveraging.fullB s d ω A_s A B ε` by the sign of `mixedDet(M, N_eff)`,
`N_eff = BlockBoundary.effSecond F_z T E`; `ThreeStateCore.effSecond_core` evaluates `N_eff` for
one stable real mode, constant coupling and no modulated coupling. This file evaluates it for
every core: any finite stable block `A_s` (only `ρ(e^{TA_s}) < 1`, `T = 2π/ω`), the modulation
`ε Re{A e^{jωt}}` and the constant perturbation `εB` on all four blocks.

* Reduction (`effSecond_eq_sub`). Let `W(u) = (A(u) + B)₂₁ R(ωu/2)` be the coupling out of the
  critical pair seen from the rotating frame, and `Γ` a solution of `A_s Γ − Γ' = W` with
  `Γ(T) = −Γ(0)`. Then `∫₀ʳ F₂₁ = Γ(0) − e^{−rA_s} Γ(r)`, the Schur-complement correction
  `−T² F̄₁₂ (I + E)⁻¹ E F̄₂₁ = −T F̄₁₂ Γ(0)` cancels the `E`-dependent part of the excursion through
  the stable block, and `N_eff = N₂(F₁₁) − ∫₀ᵀ R(−ωr/2) (A(r) + B)₁₂ Γ(r) dr`: the stable block
  acts only through the antiperiodic solution `Γ` (adiabatic elimination), never through `e^{TA_s}`.
* Harmonics. In the rotating frame the coupling into the pair is
  `R(−ωt/2)B₁₂ + R(ωt/2)X₊ + R(−3ωt/2)X₋` and the coupling out of it
  `B₂₁R(ωt/2) + Z₋R(−ωt/2) + Z₃R(3ωt/2)` (`rot_mul_coupling₁₂`, `coupling₂₁_mul_rot`;
  `X± = (Re A₁₂ ± J Im A₁₂)/2`, `Z₋ = (Re A₂₁ − Im A₂₁ J)/2`, `Z₃ = (Re A₂₁ + Im A₂₁ J)/2`). Each
  harmonic `Z R(μu)` has the rotating solution `G R(μu)`, `A_s G − μ G J = Z`,
  `G = sylv A_s μ Z = (A_s² + μ²)⁻¹ (A_s Z + μ Z J)`; at `μ = ±ω/2, 3ω/2` it exists because
  `ρ(e^{TA_s}) < 1` (`isUnit_sylv_of_spectralRadius`: otherwise `e^{TA_s}` has the eigenvalue `−1`).
* Closed form (`effSecond_closed_form`). With `R(a) M R(b) = P(M) R(a + b) + N(M) R(b − a)`
  (`P`, `N` the parts commuting and anticommuting with `J`) the rotating average of the nine
  products leaves `N_eff = N₂(F₁₁) − T (P(βΓ_a + X₊Γ_b + X₋Γ_c) + N(βΓ_b + X₊Γ_a))`,
  `β = B₁₂`, `Γ_a = sylv A_s (ω/2) B₂₁`, `Γ_b = sylv A_s (−ω/2) Z₋`, `Γ_c = sylv A_s (3ω/2) Z₃`.
  Through the complex resolvents of the stable block (`projC_couplingP`, `antiShift_couplingN`;
  `u = (1, j)/2`, `r = (1, −j)`, `γ = B₂₁`):
  `p + jq = (uβ)(A_s − jω/2)⁻¹(γr) + ¼(uA₁₂)(A_s + jω/2)⁻¹(Ā₂₁r) + ¼(uĀ₁₂)(A_s − 3jω/2)⁻¹(A₂₁r)`,
  `x + jy = ½(uβ)(A_s − jω/2)⁻¹(A₂₁r̄) + ½(uA₁₂)(A_s + jω/2)⁻¹(γr̄)`.
* Critical block (`mixedDet_secondTerm_crit`). The constant `B₁₁` shifts `(s, d)` by its commuting
  part and adds, through its anticommuting part `n = u B₁₁ r̄` (`antiShift`), a fundamental
  component of the rotating-frame matrix:
  `mixedDet(M, N₂(F₁₁)) = −s'T²(s'² + d'² − |g/2|²) + T critMixed`,
  `critMixed = d'|g'|²/(4ω) + (2/ω)(Re(κ (g/2) n̄) + d'|n|²)`, `κ = fundSkew A₁₁`.
* Verdict (`mixedDet_effSecond`, `block_boundary`). On the first-order boundary
  `s'² + d'² = |g/2|²`, `s' > 0` (`s' = s − shiftRe B`, `d' = d − shiftIm B`, `g = u A₁₁ r̄`), the
  sign of `blockMixed = critMixed + 2 Re((s' − jd')(p + jq)) + 2 Re((g/2)(x − jy))` decides:
  positive gives every Floquet multiplier inside the unit circle, negative Floquet instability,
  for all small `ε > 0`.

Scope.
* Generic: real block matrices on `Fin 2 ⊕ Y` (`Y` finite) with the operator `L∞` norm, the
  rotation `R(θ)` and quarter turn `J` of `NormalForm`, `T = 2π/ω`, `ω > 0`; the stable block
  enters only through `ρ(e^{TA_s}) < 1` (no norm condition, no diagonalizability); statements for
  all sufficiently small `ε > 0`.
* Cores: `BlockAveraging.fullB s d ω A_s A B ε` with arbitrary complex `A` and real `B` on all four
  blocks; `A₂₂`, `B₂₂` drop out at this order; `sylv_fin_one` reduces `sylv` for one real mode to
  `ThreeStateCore.lamInv`, the case of `ThreeStateCore.effSecond_core`.
* Not covered: `blockMixed = 0` (next order); remainders `ε² R_ε(t)` of a physical orbit
  (`theorem/ParametricResonance/BlockRemainderSecond.lean`).
* Generic mathematics; no model family. The flux-decay machine instance is
  `theorem/PowerSystem/Synchronous/FluxDecayParametric.lean`.

Source: the wave-7 question of this library (the effective matrix of a block core for any stable
block and modulated coupling, left open in `theorem/ParametricResonance/ThreeStateCore.lean`);
`BlockBoundary.averagingB_boundary`, `BlockBoundary.effSecond`,
`ThreeStateCore.secondTerm_toBlocks₁₁`, `SecondOrder.mixedDet_secondTerm_trigPoly`,
`BlockAveraging.rot_conj` (`theorem/ParametricResonance/BlockBoundary.lean`,
`theorem/ParametricResonance/SecondOrderClosedForm.lean`,
`theorem/ParametricResonance/BlockAveragingDetuned.lean`); adiabatic elimination of stable modes
and the second-order reduction of a critical eigenvalue (Kato, *Perturbation Theory for Linear
Operators*, the reduction process; Yakubovich–Starzhinskii, *Linear Differential Equations with
Periodic Coefficients*).

Results.
* `antiJ`, `rot_mul_mul_rot`, `integral_rot_int_mul`, `integral_rot_mul_mul_rot` — the rotating
  average of `R(ar) M R(br)`.
* `sylv`, `sylv_spec`, `hasDerivAt_mul_rot`, `mul_rot_spec`, `sylv_fin_one` — the rotating
  Sylvester equation and its harmonic solutions.
* `mulBil`, `hasDerivAt_expS_neg_mul`, `FzB_toBlocks₁₂`, `FzB_toBlocks₂₁`, `effSecond_eq_sub` —
  the reduction of `N_eff` to the critical block.
* `isUnit_one_add_of_spectralRadius`, `isUnit_sylv_of_spectralRadius` — the stable block.
* `upPlus`, `upMinus`, `lowMinus`, `lowThree`, `rot_mul_coupling₁₂`, `coupling₂₁_mul_rot`,
  `integral_harmonic_product` — the harmonics of the coupling blocks.
* `couplingP`, `couplingN`, `effSecond_closed_form` — `N_eff` in closed form.
* `antiShift`, `fundSkew`, `critMixed`, `mixedDet_secondTerm_crit` — the critical block with a
  constant perturbation.
* `projC`, `blockMixed`, `mixedDet_effSecond`, `block_boundary` — the boundary verdict.
* `stableRes`, `sylv_mulVec_right`, `sylv_mulVec_star_right`, `projC_couplingP`,
  `antiShift_couplingN` — the couplings through the complex resolvents `(A_s ∓ jω/2)⁻¹`,
  `(A_s − 3jω/2)⁻¹`.
* `sameRow_blockMixed` — a core perturbed and pumped through one equation: the resolvent terms
  are proportional to `s'² + d'² − |g/2|²` and cancel on the boundary.

Corrections.
* Of the resolvents at `∓3jω/2` only `(A_s − 3jω/2)⁻¹` occurs (its conjugate through the real
  part): the harmonic `3ω/2` of the coupling into the pair meets only the harmonic `3ω/2` of the
  coupling out of it, and only in the commuting part.
* The constant and the modulated couplings interact at second order (`βΓ_b`, `X₊Γ_a` in the
  anticommuting part, weighted by the pump phase `g/2`); a constant anticommuting perturbation of
  the pair itself (`n ≠ 0`) also changes the verdict, through `Re(κ (g/2) n̄) + d'|n|²`.

Family and connection conclusions.
None: static evidence on linear periodic systems (Floquet multipliers).
-/

noncomputable section
namespace powerlib.ParametricResonance.BlockCoreClosedForm

open Matrix Complex Set Filter Topology
open scoped Matrix.Norms.Operator Interval
open Boundary (mixedDet secondTerm)
open _root_.powerlib.ParametricResonance.NormalForm (rot quarter)
open TwoToOne (left right stdForm refl1 refl2)
open BlockAveraging (fullB FzB FzcB Fz expS Psi PsiInv modN clampT shiftRe shiftIm)
open BlockBoundary (effSecond)
open ThreeStateCore (projJ blk12 blk21 mulLeftL mulRightL)

/-! ## Rotations in the rotating frame -/

section Rot

@[tmio T, powerlib_foundation] private theorem quarter_mul_self :
    quarter * quarter = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [quarter, Matrix.mul_apply, Fin.sum_univ_two]

@[tmio T, powerlib_foundation] private theorem rot_comm_quarter (θ : ℝ) :
    rot θ * quarter = quarter * rot θ := by
  simp only [rot, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]

@[tmio T, powerlib_foundation] private theorem rot_add' (a b : ℝ) :
    rot (a + b) = rot a * rot b := by
  simp only [rot, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, quarter_mul_self, Real.cos_add, Real.sin_add, smul_neg, sub_smul, add_smul]
  module

@[tmio T, powerlib_foundation] private theorem rot_zero' : rot 0 = 1 := by simp [rot]

@[tmio T, powerlib_foundation] private theorem rot_eq_of (θ : ℝ) :
    rot θ = !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot, quarter]

@[tmio T, powerlib_foundation] private theorem projJ_eq_of (M : Matrix (Fin 2) (Fin 2) ℝ) :
    projJ M = !![(M 0 0 + M 1 1) / 2, -((M 1 0 - M 0 1) / 2); (M 1 0 - M 0 1) / 2,
      (M 0 0 + M 1 1) / 2] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [projJ, quarter]

/-- The part of a real `2 × 2` matrix anticommuting with the quarter turn `J`:
`N(M) = ((M₀₀ − M₁₁)/2) E₁ + ((M₀₁ + M₁₀)/2) E₂`, so that `M = P(M) + N(M)`. -/
def antiJ (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ((M 0 0 - M 1 1) / 2) • refl1 + ((M 0 1 + M 1 0) / 2) • refl2

/-- `R(a) M R(b) = P(M) R(a + b) + N(M) R(b − a)`: the commuting part of `M` rotates with the sum
of the two angles, the anticommuting part with their difference. -/
@[tmio T, powerlib_foundation] theorem rot_mul_mul_rot (M : Matrix (Fin 2) (Fin 2) ℝ) (a b : ℝ) :
    rot a * M * rot b = projJ M * rot (a + b) + antiJ M * rot (b - a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply] <;>
    simp [rot, quarter, projJ, antiJ, refl1, refl2, Real.cos_add, Real.sin_add, Real.cos_sub,
      Real.sin_sub] <;> ring

/-- `∫₀ᵀ R(mωr) dr` is `T I` for `m = 0` and `0` for every other integer `m` (`T = 2π/ω`). -/
@[tmio T, powerlib_foundation] theorem integral_rot_int_mul {ω : ℝ} (hω : 0 < ω) (m : ℤ) :
    ∫ r in (0 : ℝ)..(2 * Real.pi / ω), rot (m * (ω * r)) =
      if m = 0 then (2 * Real.pi / ω) • (1 : Matrix (Fin 2) (Fin 2) ℝ) else 0 := by
  have hc : Continuous fun r : ℝ => Real.cos (m * (ω * r)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
    (by fun_prop : Continuous fun r : ℝ => Real.cos (m * (ω * r))).smul continuous_const
  have hs : Continuous fun r : ℝ => Real.sin (m * (ω * r)) • quarter :=
    (by fun_prop : Continuous fun r : ℝ => Real.sin (m * (ω * r))).smul continuous_const
  simp only [rot]
  rw [intervalIntegral.integral_add (hc.intervalIntegrable _ _) (hs.intervalIntegrable _ _),
    intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const,
    SecondOrder.integral_cos_int_mul hω, SecondOrder.integral_sin_int_mul hω, zero_smul, add_zero]
  split_ifs <;> simp

@[tmio T, powerlib_foundation] private theorem integral_mul_left₂ {m n p : Type*} [Fintype m]
    [Fintype n] [Fintype p] {f : ℝ → Matrix n p ℝ} (hf : Continuous f) (B : Matrix m n ℝ)
    (a b : ℝ) : ∫ t in a..b, B * f t = B * ∫ t in a..b, f t :=
  (mulLeftL B).intervalIntegral_comp_comm (hf.intervalIntegrable a b)

@[tmio T, powerlib_foundation] private theorem integral_mul_right₂ {m n p : Type*} [Fintype m]
    [Fintype n] [Fintype p] {f : ℝ → Matrix m n ℝ} (hf : Continuous f) (B : Matrix n p ℝ)
    (a b : ℝ) : ∫ t in a..b, f t * B = (∫ t in a..b, f t) * B :=
  (mulRightL B).intervalIntegral_comp_comm (hf.intervalIntegrable a b)

/-- **The rotating average of a product of two harmonics.** For frequencies `a`, `b` whose sum
and difference are integer multiples `mω`, `nω` of the pump frequency (`T = 2π/ω`):
`∫₀ᵀ R(ar) M R(br) dr = T ([m = 0] P(M) + [n = 0] N(M))`. -/
@[tmio T, powerlib_foundation] theorem integral_rot_mul_mul_rot {ω : ℝ} (hω : 0 < ω)
    (M : Matrix (Fin 2) (Fin 2) ℝ) {a b : ℝ} {m n : ℤ} (hm : a + b = m * ω) (hn : b - a = n * ω) :
    ∫ r in (0 : ℝ)..(2 * Real.pi / ω), rot (a * r) * M * rot (b * r) =
      (2 * Real.pi / ω) • ((if m = 0 then projJ M else 0) + (if n = 0 then antiJ M else 0)) := by
  have e : ∀ r : ℝ, rot (a * r) * M * rot (b * r) =
      projJ M * rot (m * (ω * r)) + antiJ M * rot (n * (ω * r)) := fun r => by
    rw [rot_mul_mul_rot, show a * r + b * r = m * (ω * r) by rw [← add_mul, hm]; ring,
      show b * r - a * r = n * (ω * r) by rw [← sub_mul, hn]; ring]
  have hrc : ∀ k : ℤ, Continuous fun r : ℝ => rot (k * (ω * r)) := fun k => by
    unfold rot; fun_prop
  simp_rw [e]
  rw [intervalIntegral.integral_add ((continuous_const.matrix_mul (hrc m)).intervalIntegrable _ _)
      ((continuous_const.matrix_mul (hrc n)).intervalIntegrable _ _),
    integral_mul_left₂ (hrc m), integral_mul_left₂ (hrc n), integral_rot_int_mul hω,
    integral_rot_int_mul hω]
  split_ifs <;> simp [smul_add]

end Rot

/-! ## The rotating Sylvester equation: the real form of the resolvent `(A_s − jμ)⁻¹` -/

section Sylvester

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The solution of the rotating Sylvester equation `A_s Γ − μ Γ J = Z` (`Γ, Z : Y × 2`):
`Γ = (A_s² + μ² I)⁻¹ (A_s Z + μ Z J)`. With `r = (1, −j)` it is `Γ r = (A_s − jμ)⁻¹ Z r` and
`Γ r̄ = (A_s + jμ)⁻¹ Z r̄` (`sylv_mulVec_right`, `sylv_mulVec_star_right`): the real form of the
resolvent of the stable block at `±jμ`. -/
def sylv (As : Matrix Y Y ℝ) (μ : ℝ) (Z : Matrix Y (Fin 2) ℝ) : Matrix Y (Fin 2) ℝ :=
  (As * As + μ ^ 2 • (1 : Matrix Y Y ℝ))⁻¹ * (As * Z + μ • (Z * quarter))

/-- `Γ = sylv A_s μ Z` solves `A_s Γ − μ Γ J = Z` when `A_s² + μ²` is invertible. -/
@[tmio T, powerlib_foundation] theorem sylv_spec {As : Matrix Y Y ℝ} {μ : ℝ}
    (h : IsUnit (As * As + μ ^ 2 • (1 : Matrix Y Y ℝ)).det) (Z : Matrix Y (Fin 2) ℝ) :
    As * sylv As μ Z - μ • (sylv As μ Z * quarter) = Z := by
  set S := As * As + μ ^ 2 • (1 : Matrix Y Y ℝ) with hS
  have hAS : As * S = S * As := by
    rw [hS, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc]
  have hc : As * S⁻¹ = S⁻¹ * As := by
    calc As * S⁻¹ = S⁻¹ * (S * As) * S⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.one_mul]
      _ = S⁻¹ * (As * S) * S⁻¹ := by rw [hAS]
      _ = S⁻¹ * As := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h, Matrix.mul_one]
  have hW : As * (As * Z + μ • (Z * quarter)) - μ • ((As * Z + μ • (Z * quarter)) * quarter) =
      S * Z := by
    rw [hS]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_assoc, quarter_mul_self, Matrix.mul_neg, Matrix.mul_one]
    module
  have e1 : As * sylv As μ Z = S⁻¹ * (As * (As * Z + μ • (Z * quarter))) := by
    rw [sylv, ← hS, ← Matrix.mul_assoc, hc, Matrix.mul_assoc]
  have e2 : sylv As μ Z * quarter = S⁻¹ * ((As * Z + μ • (Z * quarter)) * quarter) := by
    rw [sylv, ← hS, Matrix.mul_assoc]
  rw [e1, e2, ← Matrix.mul_smul S⁻¹, ← Matrix.mul_sub, hW, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ h, Matrix.one_mul]

omit [DecidableEq Y] in
/-- The rotating solution `Γ(u) = G R(μu)` has `Γ' = μ Γ J`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_mul_rot (G : Matrix Y (Fin 2) ℝ) (μ u : ℝ) :
    HasDerivAt (fun u => G * rot (μ * u)) (μ • (G * rot (μ * u) * quarter)) u := by
  have h := NormalForm.hasDerivAt_rot (2 * μ) u
  have e : (fun t => rot (2 * μ * t / 2)) = fun t => rot (μ * t) := by
    funext t; congr 1; ring
  rw [e, show 2 * μ * u / 2 = μ * u by ring, show 2 * μ / 2 = μ by ring] at h
  have h2 := (mulLeftL G).hasFDerivAt.comp_hasDerivAt u h
  refine h2.congr_deriv ?_
  show G * (μ • (rot (μ * u) * quarter)) = _
  rw [Matrix.mul_smul, Matrix.mul_assoc]

omit [DecidableEq Y] in
/-- If `A_s G − μ G J = Z`, the rotating solution `Γ(u) = G R(μu)` solves
`A_s Γ − Γ' = Z R(μu)`. -/
@[tmio T, powerlib_foundation] theorem mul_rot_spec {As : Matrix Y Y ℝ} {μ : ℝ}
    {G Z : Matrix Y (Fin 2) ℝ} (hG : As * G - μ • (G * quarter) = Z) (u : ℝ) :
    As * (G * rot (μ * u)) - μ • (G * rot (μ * u) * quarter) = Z * rot (μ * u) := by
  rw [← hG, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc G quarter, ← rot_comm_quarter,
    Matrix.mul_assoc, Matrix.mul_assoc]

/-- For one real stable mode `a` the rotating Sylvester solution is `sylv [a] μ Z = Z (aI − μJ)⁻¹`
(`ThreeStateCore.lamInv`). -/
@[tmio T, powerlib_foundation] theorem sylv_fin_one {a μ : ℝ} (h : a ^ 2 + μ ^ 2 ≠ 0)
    (Z : Matrix (Fin 1) (Fin 2) ℝ) : sylv !![a] μ Z = Z * ThreeStateCore.lamInv a μ := by
  have hS : (!![a] * !![a] + μ ^ 2 • (1 : Matrix (Fin 1) (Fin 1) ℝ)) = !![a ^ 2 + μ ^ 2] := by
    ext i j; fin_cases i; fin_cases j; simp; ring
  have hinv : (!![a ^ 2 + μ ^ 2] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = !![(a ^ 2 + μ ^ 2)⁻¹] := by
    refine Matrix.inv_eq_left_inv ?_
    ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply, h]
  have hrow : ∀ (c : ℝ) (X : Matrix (Fin 1) (Fin 2) ℝ), !![c] * X = c • X := fun c X => by
    ext i j; fin_cases i; simp [Matrix.mul_apply]
  rw [sylv, hS, hinv, hrow, hrow, ThreeStateCore.lamInv, Matrix.mul_smul, Matrix.mul_add,
    Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]

end Sylvester

/-! ## The reduction of the effective matrix to the critical block -/

section Reduction

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- Multiplication `(Y × Y) × (Y × 2) → Y × 2` as a continuous bilinear map. -/
def mulBil : Matrix Y Y ℝ →L[ℝ] Matrix Y (Fin 2) ℝ →L[ℝ] Matrix Y (Fin 2) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => mulLeftL M
      map_add' := fun M N => ContinuousLinearMap.ext fun X => Matrix.add_mul M N X
      map_smul' := fun c M => ContinuousLinearMap.ext fun X => Matrix.smul_mul c M X }

/-- `d/du (e^{−uA_s} Γ(u)) = e^{−uA_s} (Γ'(u) − A_s Γ(u))`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_expS_neg_mul (As : Matrix Y Y ℝ)
    {Γ : ℝ → Matrix Y (Fin 2) ℝ} {Γ' : Matrix Y (Fin 2) ℝ} {u : ℝ} (hΓ : HasDerivAt Γ Γ' u) :
    HasDerivAt (fun u => expS As (-u) * Γ u) (expS As (-u) * (Γ' - As * Γ u)) u := by
  have he : HasDerivAt (fun u => expS As (-u)) (-(expS As (-u) * As)) u := by
    have h := (BlockAveraging.hasDerivAt_expS As (-u)).scomp u (hasDerivAt_neg u)
    rw [neg_one_smul] at h
    exact h
  have h := ContinuousLinearMap.hasDerivAt_of_bilinear (B := mulBil) (fun _ => he) (fun _ => hΓ)
  refine h.congr_deriv ?_
  show expS As (-u) * Γ' + -(expS As (-u) * As) * Γ u = _
  rw [Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_assoc]
  abel

@[tmio T, powerlib_foundation] private theorem FzB_eq (s d ω : ℝ) (As : Matrix Y Y ℝ)
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (t : ℝ) :
    FzB s d ω As A B t = fromBlocks (slowFlowMatrix s d 0) 0 0 0 +
      fromBlocks (rot (-(ω * t / 2))) 0 0 (expS As (-t)) *
        fromBlocks (modN A ω t + B).toBlocks₁₁ (modN A ω t + B).toBlocks₁₂
          (modN A ω t + B).toBlocks₂₁ (modN A ω t + B).toBlocks₂₂ *
        fromBlocks (rot (ω * t / 2)) 0 0 (expS As t) := by
  rw [fromBlocks_toBlocks, FzB, Fz, add_assoc, ← Matrix.add_mul, ← Matrix.mul_add, PsiInv, Psi]

/-- The coupling block into the critical pair: `F₁₂(t) = R(−ωt/2) (A(t) + B)₁₂ e^{tA_s}`. -/
@[tmio T, powerlib_foundation] theorem FzB_toBlocks₁₂ (s d ω : ℝ) (As : Matrix Y Y ℝ)
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (t : ℝ) :
    (FzB s d ω As A B t).toBlocks₁₂ =
      rot (-(ω * t / 2)) * (modN A ω t + B).toBlocks₁₂ * expS As t := by
  rw [FzB_eq, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_add]
  simp

/-- The coupling block out of the critical pair: `F₂₁(t) = e^{−tA_s} (A(t) + B)₂₁ R(ωt/2)`. -/
@[tmio T, powerlib_foundation] theorem FzB_toBlocks₂₁ (s d ω : ℝ) (As : Matrix Y Y ℝ)
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (t : ℝ) :
    (FzB s d ω As A B t).toBlocks₂₁ =
      expS As (-t) * (modN A ω t + B).toBlocks₂₁ * rot (ω * t / 2) := by
  rw [FzB_eq, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_add]
  simp

set_option maxHeartbeats 2000000 in
/-- **The effective matrix of a block core, reduced to the critical block.** For the block
standard form of `BlockAveraging.fullB s d ω A_s A B` (any finite `Y`, any stable block `A_s`, any
modulation `A` and constant perturbation `B`, coupling blocks included), let `Γ` be a
differentiable solution of `A_s Γ(u) − Γ'(u) = W(u)`, `W(u) = (A(u) + B)₂₁ R(ωu/2)`, with
`Γ(T) = −Γ(0)`, and let `1 + e^{TA_s}` be invertible. Then
`N_eff = N₂(F₁₁) − ∫₀ᵀ R(−ωr/2) (A(r) + B)₁₂ Γ(r) dr`, with `F₁₁` the critical block of the
standard form. The primitive `∫₀ʳ F₂₁ = Γ(0) − e^{−rA_s} Γ(r)` makes `T F̄₂₁ = (1 + E⁻¹) Γ(0)`;
the Schur-complement correction `−T² F̄₁₂ (I + E)⁻¹ E F̄₂₁ = −T F̄₁₂ Γ(0)` cancels the part
`T F̄₁₂ Γ(0)` of the excursion through the stable block, and `E = e^{TA_s}` drops out. -/
@[tmio T, powerlib_foundation] theorem effSecond_eq_sub {s d ω T : ℝ} (hT : 0 < T)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) {Γ Γ' : ℝ → Matrix Y (Fin 2) ℝ}
    (hΓ : ∀ u, HasDerivAt Γ (Γ' u) u)
    (heq : ∀ u, As * Γ u - Γ' u = (modN A ω u + B).toBlocks₂₁ * rot (ω * u / 2))
    (hper : Γ T = -Γ 0) (hE : IsUnit (1 + expS As T).det) :
    effSecond (FzcB s d ω T As A B) T (expS As T) =
      secondTerm (fun t => stdForm s d ω A.toBlocks₁₁ t +
          rot (-(ω * t / 2)) * B.toBlocks₁₁ * rot (ω * t / 2)) T -
        ∫ r in (0 : ℝ)..T, rot (-(ω * r / 2)) * (modN A ω r + B).toBlocks₁₂ * Γ r := by
  set G := FzB s d ω As A B with hG
  set F := FzcB s d ω T As A B with hF
  have hGc : Continuous G := BlockAveraging.continuous_FzB s d ω _ _ _
  have hFG : ∀ t ∈ Icc (0 : ℝ) T, F t = G t := fun t ht => by
    rw [hF, BlockAveraging.FzcB, BlockAveraging.clampT_of_mem ht]
  have hint : ∀ r ∈ Icc (0 : ℝ) T, ∫ u in (0 : ℝ)..r, F u = ∫ u in (0 : ℝ)..r, G u := by
    intro r hr
    refine intervalIntegral.integral_congr fun u hu => hFG u ?_
    rw [uIcc_of_le hr.1] at hu
    exact ⟨hu.1, hu.2.trans hr.2⟩
  have hsecFG : secondTerm F T = secondTerm G T := by
    unfold secondTerm
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hT.le] at hr
    rw [hFG r hr, hint r hr]
  have hmeanFG : ∫ t in (0 : ℝ)..T, F t = ∫ t in (0 : ℝ)..T, G t := hint T ⟨hT.le, le_rfl⟩
  have hΓc : Continuous Γ := continuous_iff_continuousAt.2 fun u => (hΓ u).continuousAt
  have h12c : Continuous fun t => (G t).toBlocks₁₂ := blk12.continuous.comp hGc
  have h21c : Continuous fun t => (G t).toBlocks₂₁ := blk21.continuous.comp hGc
  -- the primitive of the lower coupling block
  have hderiv : ∀ u, HasDerivAt (fun u => -(expS As (-u) * Γ u)) ((G u).toBlocks₂₁) u := by
    intro u
    refine (hasDerivAt_expS_neg_mul As (hΓ u)).neg.congr_deriv ?_
    rw [hG, FzB_toBlocks₂₁, Matrix.mul_assoc, ← heq u, Matrix.mul_sub, Matrix.mul_sub]
    abel
  have hprim : ∀ r, ∫ u in (0 : ℝ)..r, (G u).toBlocks₂₁ = Γ 0 - expS As (-r) * Γ r := by
    intro r
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
      (h21c.intervalIntegrable 0 r)]
    have h0 : expS As (-0) = 1 := by simp [BlockAveraging.expS]
    rw [h0, Matrix.one_mul]
    abel
  have hE1 : expS As T * expS As (-T) = 1 := (BlockAveraging.expS_mul_neg As T).1
  have hI21 : (∫ t in (0 : ℝ)..T, G t).toBlocks₂₁ = Γ 0 + expS As (-T) * Γ 0 := by
    have h := (blk21 (Y := Y)).intervalIntegral_comp_comm
      (hGc.intervalIntegrable (μ := MeasureTheory.volume) 0 T)
    have h' : (∫ t in (0 : ℝ)..T, G t).toBlocks₂₁ = blk21 (∫ t in (0 : ℝ)..T, G t) := rfl
    rw [h']
    refine h.symm.trans ?_
    show (∫ t in (0 : ℝ)..T, (G t).toBlocks₂₁) = _
    rw [hprim, hper, Matrix.mul_neg, sub_neg_eq_add]
  have hI12 : (∫ t in (0 : ℝ)..T, G t).toBlocks₁₂ = ∫ t in (0 : ℝ)..T, (G t).toBlocks₁₂ :=
    ((blk12 (Y := Y)).intervalIntegral_comp_comm
      (hGc.intervalIntegrable (μ := MeasureTheory.volume) 0 T)).symm
  -- the excursion through the stable block
  have hexc : ∀ r, (G r).toBlocks₁₂ * ∫ u in (0 : ℝ)..r, (G u).toBlocks₂₁ =
      (G r).toBlocks₁₂ * Γ 0 - rot (-(ω * r / 2)) * (modN A ω r + B).toBlocks₁₂ * Γ r := by
    intro r
    rw [hprim, Matrix.mul_sub]
    congr 1
    rw [hG, FzB_toBlocks₁₂, ← Matrix.mul_assoc, Matrix.mul_assoc _ (expS As r),
      (BlockAveraging.expS_mul_neg As r).1, Matrix.mul_one]
  have hcR : Continuous fun r => rot (-(ω * r / 2)) * (modN A ω r + B).toBlocks₁₂ * Γ r := by
    have h1 : Continuous fun r : ℝ => rot (-(ω * r / 2)) := by unfold rot; fun_prop
    have h2 : Continuous fun r => (modN A ω r + B).toBlocks₁₂ :=
      blk12.continuous.comp ((BlockAveraging.continuous_modN A ω).add continuous_const)
    exact (h1.matrix_mul h2).matrix_mul hΓc
  have hIexc : ∫ r in (0 : ℝ)..T, (G r).toBlocks₁₂ * ∫ u in (0 : ℝ)..r, (G u).toBlocks₂₁ =
      (∫ r in (0 : ℝ)..T, (G r).toBlocks₁₂) * Γ 0 -
        ∫ r in (0 : ℝ)..T, rot (-(ω * r / 2)) * (modN A ω r + B).toBlocks₁₂ * Γ r := by
    simp_rw [hexc]
    rw [intervalIntegral.integral_sub ((h12c.matrix_mul continuous_const).intervalIntegrable 0 T)
      (hcR.intervalIntegrable 0 T), integral_mul_right₂ h12c]
  have hsec11 := ThreeStateCore.secondTerm_toBlocks₁₁ hGc T
  have hG11 : (fun t => (G t).toBlocks₁₁) = fun t => stdForm s d ω A.toBlocks₁₁ t +
      rot (-(ω * t / 2)) * B.toBlocks₁₁ * rot (ω * t / 2) :=
    funext fun t => BlockAveraging.FzB_toBlocks₁₁ s d ω As A B t
  rw [hG11] at hsec11
  rw [effSecond, hsecFG, hmeanFG, hsec11, hIexc]
  have hs12 : (T • (T⁻¹ • ∫ t in (0 : ℝ)..T, G t).toBlocks₁₂) =
      (∫ t in (0 : ℝ)..T, G t).toBlocks₁₂ := by
    show T • (T⁻¹ • (∫ t in (0 : ℝ)..T, G t).toBlocks₁₂) = _
    rw [smul_smul, mul_inv_cancel₀ hT.ne', one_smul]
  have hs21 : (T • (expS As T * (T⁻¹ • ∫ t in (0 : ℝ)..T, G t).toBlocks₂₁)) =
      expS As T * (∫ t in (0 : ℝ)..T, G t).toBlocks₂₁ := by
    show T • (expS As T * (T⁻¹ • (∫ t in (0 : ℝ)..T, G t).toBlocks₂₁)) = _
    rw [Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hT.ne', one_smul]
  rw [hs12, hs21, hI21, hI12]
  have hEΓ : expS As T * (Γ 0 + expS As (-T) * Γ 0) = (1 + expS As T) * Γ 0 := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hE1, Matrix.one_mul, Matrix.add_mul, Matrix.one_mul,
      add_comm]
  rw [hEΓ, Matrix.mul_assoc _ (1 + expS As T)⁻¹, ← Matrix.mul_assoc (1 + expS As T)⁻¹,
    Matrix.nonsing_inv_mul _ hE, Matrix.one_mul, Matrix.neg_mul]
  abel

end Reduction

/-! ## The stable block: invertibility from `ρ(e^{TA_s}) < 1` -/

section Stable

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- `ρ(E) < 1` makes `1 + E` invertible. -/
@[tmio T, powerlib_foundation] theorem isUnit_one_add_of_spectralRadius {E : Matrix Y Y ℝ}
    (hρ : spectralRadius ℂ (E.map (algebraMap ℝ ℂ)) < 1) : IsUnit (1 + E).det := by
  obtain ⟨K, η, _, hη, h⟩ := BlockBoundary.stable_block_resolvent hρ
  have h1 := ((h E (by rw [sub_self, norm_zero]; exact hη.le)).1 (-1) (by norm_num)).1
  have e : (-1 : ℝ) • (1 : Matrix Y Y ℝ) - E = -(1 + E) := by rw [neg_one_smul]; abel
  rw [e, Matrix.det_neg] at h1
  exact (IsUnit.mul_iff.mp h1).2

/-- A homogeneous solution `A_s X = μ X J` with `R(μT) = −I` is reversed by one period:
`(1 + e^{TA_s}) X = 0`. -/
@[tmio T, powerlib_foundation] private theorem one_add_expS_mul_eq_zero {As : Matrix Y Y ℝ}
    {μ T : ℝ} {X : Matrix Y (Fin 2) ℝ} (hX : As * X - μ • (X * quarter) = 0)
    (hπ : rot (μ * T) = -1) : (1 + expS As T) * X = 0 := by
  set f : ℝ → Matrix Y (Fin 2) ℝ := fun u => expS As (-u) * (X * rot (μ * u)) with hf
  have hd : ∀ u, HasDerivAt f 0 u := fun u => by
    refine (hasDerivAt_expS_neg_mul As (hasDerivAt_mul_rot X μ u)).congr_deriv ?_
    rw [← neg_sub, mul_rot_spec hX u, Matrix.zero_mul, neg_zero, Matrix.mul_zero]
  have hc := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) T 0
  have h0 : f 0 = X := by simp [hf, BlockAveraging.expS, rot_zero']
  rw [h0] at hc
  have hT : f T = -(expS As (-T) * X) := by
    rw [hf]; simp only; rw [hπ, Matrix.mul_neg, Matrix.mul_one, Matrix.mul_neg]
  rw [hT] at hc
  have hE := (BlockAveraging.expS_mul_neg As T).1
  have : expS As T * X = -X :=
    calc expS As T * X = expS As T * (-(expS As (-T) * X)) := by rw [hc]
      _ = -X := by rw [Matrix.mul_neg, ← Matrix.mul_assoc, hE, Matrix.one_mul]
  rw [Matrix.add_mul, Matrix.one_mul, this, add_neg_cancel]

/-- **`ρ(e^{TA_s}) < 1` makes the rotating Sylvester equation solvable** at every frequency `μ`
with `R(μT) = −I` (an odd multiple of `π/T`): `A_s² + μ²` is invertible, i.e. `±jμ` is not an
eigenvalue of `A_s` (else `e^{TA_s}` would have the eigenvalue `−1`). -/
@[tmio T, powerlib_foundation] theorem isUnit_sylv_of_spectralRadius {As : Matrix Y Y ℝ}
    {μ T : ℝ} (hρ : spectralRadius ℂ ((expS As T).map (algebraMap ℝ ℂ)) < 1)
    (hπ : rot (μ * T) = -1) : IsUnit (As * As + μ ^ 2 • (1 : Matrix Y Y ℝ)).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hSv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hμ : μ ≠ 0 := by
    rintro rfl
    have h := congrFun (congrFun hπ 0) 0
    simp [rot] at h
    norm_num at h
  have hAAv : As *ᵥ (As *ᵥ v) = -(μ ^ 2 • v) := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at hSv
    exact eq_neg_of_add_eq_zero_left hSv
  set X : Matrix Y (Fin 2) ℝ := Matrix.of fun i j => ![v i, (As *ᵥ v) i / μ] j with hXd
  have hX : As * X - μ • (X * quarter) = 0 := by
    ext i j
    fin_cases j
    · simp [hXd, Matrix.mul_apply, Fin.sum_univ_two, quarter, Matrix.mulVec, dotProduct]
      field_simp
      ring
    · have hi := congrFun hAAv i
      simp only [Matrix.mulVec, dotProduct, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at hi
      simp [hXd, Matrix.mul_apply, Fin.sum_univ_two, quarter, Matrix.mulVec, dotProduct,
        ← Finset.sum_div, mul_div_assoc']
      rw [hi]
      field_simp
      ring
  have hπ' := one_add_expS_mul_eq_zero hX hπ
  have hE := isUnit_one_add_of_spectralRadius hρ
  have hX0 : X = 0 := by
    rw [← Matrix.one_mul X, ← Matrix.nonsing_inv_mul _ hE, Matrix.mul_assoc, hπ',
      Matrix.mul_zero]
  apply hv
  funext i
  have := congrFun (congrFun hX0 i) 0
  simpa [hXd] using this

end Stable

/-! ## The harmonics of the coupling blocks in the rotating frame -/

section Harmonics

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The coefficient `X₊ = (Re A₁₂ + J Im A₁₂)/2` of `R(ωt/2)` in `R(−ωt/2) Re{A₁₂ e^{jωt}}`. -/
def upPlus (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) : Matrix (Fin 2) Y ℝ :=
  (1 / 2 : ℝ) • (A.toBlocks₁₂.map Complex.re + quarter * A.toBlocks₁₂.map Complex.im)

/-- The coefficient `X₋ = (Re A₁₂ − J Im A₁₂)/2` of `R(−3ωt/2)` in `R(−ωt/2) Re{A₁₂ e^{jωt}}`. -/
def upMinus (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) : Matrix (Fin 2) Y ℝ :=
  (1 / 2 : ℝ) • (A.toBlocks₁₂.map Complex.re - quarter * A.toBlocks₁₂.map Complex.im)

/-- The coefficient `Z₋ = (Re A₂₁ − Im A₂₁ J)/2` of `R(−ωt/2)` in `Re{A₂₁ e^{jωt}} R(ωt/2)`. -/
def lowMinus (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) : Matrix Y (Fin 2) ℝ :=
  (1 / 2 : ℝ) • (A.toBlocks₂₁.map Complex.re - A.toBlocks₂₁.map Complex.im * quarter)

/-- The coefficient `Z₃ = (Re A₂₁ + Im A₂₁ J)/2` of `R(3ωt/2)` in `Re{A₂₁ e^{jωt}} R(ωt/2)`. -/
def lowThree (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) : Matrix Y (Fin 2) ℝ :=
  (1 / 2 : ℝ) • (A.toBlocks₂₁.map Complex.re + A.toBlocks₂₁.map Complex.im * quarter)

@[tmio T, powerlib_foundation] private theorem cos_two_smul_rot_neg (φ : ℝ) :
    Real.cos (2 * φ) • rot (-φ) = (1 / 2 : ℝ) • (rot φ + rot (-(3 * φ))) := by
  have hsc := Real.cos_sq_add_sin_sq φ
  have h3 : 3 * φ = 2 * φ + φ := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, quarter, h3, Real.cos_add, Real.sin_add, Real.cos_two_mul, Real.sin_two_mul] <;>
    first
      | ring1
      | linear_combination (Real.cos φ / 2) * hsc
      | linear_combination (-Real.cos φ / 2) * hsc
      | linear_combination (Real.sin φ / 2) * hsc
      | linear_combination (-Real.sin φ / 2) * hsc
      | linear_combination (Real.cos φ) * hsc

@[tmio T, powerlib_foundation] private theorem sin_two_smul_rot_neg (φ : ℝ) :
    Real.sin (2 * φ) • rot (-φ) = (1 / 2 : ℝ) • (quarter * (rot (-(3 * φ)) - rot φ)) := by
  have hsc := Real.cos_sq_add_sin_sq φ
  have h3 : 3 * φ = 2 * φ + φ := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply] <;>
    simp [rot, quarter, h3, Real.cos_add, Real.sin_add, Real.cos_two_mul, Real.sin_two_mul] <;>
    first
      | ring1
      | linear_combination (Real.cos φ / 2) * hsc
      | linear_combination (-Real.cos φ / 2) * hsc
      | linear_combination (Real.sin φ / 2) * hsc
      | linear_combination (-Real.sin φ / 2) * hsc
      | linear_combination (Real.cos φ) * hsc
      | linear_combination (-Real.cos φ) * hsc

@[tmio T, powerlib_foundation] private theorem cos_two_smul_rot (φ : ℝ) :
    Real.cos (2 * φ) • rot φ = (1 / 2 : ℝ) • (rot (3 * φ) + rot (-φ)) := by
  have hsc := Real.cos_sq_add_sin_sq φ
  have h3 : 3 * φ = 2 * φ + φ := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, quarter, h3, Real.cos_add, Real.sin_add, Real.cos_two_mul, Real.sin_two_mul] <;>
    first
      | ring1
      | linear_combination (Real.cos φ / 2) * hsc
      | linear_combination (-Real.cos φ / 2) * hsc
      | linear_combination (Real.sin φ / 2) * hsc
      | linear_combination (-Real.sin φ / 2) * hsc
      | linear_combination (Real.cos φ) * hsc

@[tmio T, powerlib_foundation] private theorem sin_two_smul_rot (φ : ℝ) :
    Real.sin (2 * φ) • rot φ = (1 / 2 : ℝ) • (quarter * (rot (-φ) - rot (3 * φ))) := by
  have hsc := Real.cos_sq_add_sin_sq φ
  have h3 : 3 * φ = 2 * φ + φ := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply] <;>
    simp [rot, quarter, h3, Real.cos_add, Real.sin_add, Real.cos_two_mul, Real.sin_two_mul] <;>
    first
      | ring1
      | linear_combination (Real.cos φ / 2) * hsc
      | linear_combination (-Real.cos φ / 2) * hsc
      | linear_combination (Real.sin φ / 2) * hsc
      | linear_combination (-Real.sin φ / 2) * hsc
      | linear_combination (Real.cos φ) * hsc
      | linear_combination (-Real.cos φ) * hsc

omit [DecidableEq Y] in
@[tmio T, powerlib_foundation] private theorem quarter_mul_rot_mul (ψ : ℝ) {Z : Type*} [Fintype Z]
    (M : Matrix (Fin 2) Z ℝ) : quarter * (rot ψ * M) = rot ψ * (quarter * M) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, rot_comm_quarter]

omit [DecidableEq Y] in
/-- **The coupling into the critical pair in the rotating frame**: three harmonics,
`R(−ωt/2) (A(t) + B)₁₂ = R(−ωt/2) B₁₂ + R(ωt/2) X₊ + R(−3ωt/2) X₋` (`upPlus`, `upMinus`). -/
@[tmio T, powerlib_foundation] theorem rot_mul_coupling₁₂ (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (ω t : ℝ) :
    rot (-(ω * t / 2)) * (modN A ω t + B).toBlocks₁₂ =
      rot (-(ω / 2) * t) * B.toBlocks₁₂ + rot (ω / 2 * t) * upPlus A +
        rot (-(3 * ω / 2) * t) * upMinus A := by
  set φ := ω * t / 2 with hφ
  have h2 : ω * t = 2 * φ := by rw [hφ]; ring
  have e1 : -(ω / 2) * t = -φ := by rw [hφ]; ring
  have e2 : ω / 2 * t = φ := by rw [hφ]; ring
  have e3 : -(3 * ω / 2) * t = -(3 * φ) := by rw [hφ]; ring
  have hm : (modN A ω t + B).toBlocks₁₂ = Real.cos (2 * φ) • A.toBlocks₁₂.map Complex.re -
      Real.sin (2 * φ) • A.toBlocks₁₂.map Complex.im + B.toBlocks₁₂ := by
    rw [← h2]; ext i j; simp [modN, Matrix.toBlocks₁₂]; ring
  rw [e1, e2, e3, hm, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul,
    ← Matrix.smul_mul, ← Matrix.smul_mul, cos_two_smul_rot_neg, sin_two_smul_rot_neg, upPlus,
    upMinus]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add,
    Matrix.mul_sub, Matrix.mul_assoc, quarter_mul_rot_mul]
  module

omit [Fintype Y] [DecidableEq Y] in
/-- **The coupling out of the critical pair in the rotating frame**:
`(A(t) + B)₂₁ R(ωt/2) = B₂₁ R(ωt/2) + Z₋ R(−ωt/2) + Z₃ R(3ωt/2)` (`lowMinus`, `lowThree`). -/
@[tmio T, powerlib_foundation] theorem coupling₂₁_mul_rot (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (ω t : ℝ) :
    (modN A ω t + B).toBlocks₂₁ * rot (ω * t / 2) =
      B.toBlocks₂₁ * rot (ω / 2 * t) + lowMinus A * rot (-(ω / 2) * t) +
        lowThree A * rot (3 * ω / 2 * t) := by
  set φ := ω * t / 2 with hφ
  have h2 : ω * t = 2 * φ := by rw [hφ]; ring
  have e1 : -(ω / 2) * t = -φ := by rw [hφ]; ring
  have e2 : ω / 2 * t = φ := by rw [hφ]; ring
  have e3 : 3 * ω / 2 * t = 3 * φ := by rw [hφ]; ring
  have hm : (modN A ω t + B).toBlocks₂₁ = Real.cos (2 * φ) • A.toBlocks₂₁.map Complex.re -
      Real.sin (2 * φ) • A.toBlocks₂₁.map Complex.im + B.toBlocks₂₁ := by
    rw [← h2]; ext i j; simp [modN, Matrix.toBlocks₂₁]; ring
  rw [e1, e2, e3, hm, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul,
    ← Matrix.mul_smul, ← Matrix.mul_smul, cos_two_smul_rot, sin_two_smul_rot, lowMinus, lowThree]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add,
    Matrix.mul_sub, Matrix.mul_assoc]
  module

omit [DecidableEq Y] in
/-- **The rotating average of a product of harmonic sums.** If every pair of frequencies has sum
`m_{ij} ω` and difference `n_{ij} ω` (`T = 2π/ω`), then
`∫₀ᵀ (∑ᵢ R(aᵢr) Xᵢ)(∑ⱼ Gⱼ R(bⱼr)) dr = T ∑ᵢⱼ ([m_{ij} = 0] P(XᵢGⱼ) + [n_{ij} = 0] N(XᵢGⱼ))`. -/
@[tmio T, powerlib_foundation] theorem integral_harmonic_product {ω : ℝ} (hω : 0 < ω)
    {ι κ : Type*} [Fintype ι] [Fintype κ] (a : ι → ℝ) (b : κ → ℝ)
    (X : ι → Matrix (Fin 2) Y ℝ) (G : κ → Matrix Y (Fin 2) ℝ) (m n : ι → κ → ℤ)
    (hm : ∀ i j, a i + b j = m i j * ω) (hn : ∀ i j, b j - a i = n i j * ω) :
    ∫ r in (0 : ℝ)..(2 * Real.pi / ω),
        (∑ i, rot (a i * r) * X i) * (∑ j, G j * rot (b j * r)) =
      (2 * Real.pi / ω) • ∑ i, ∑ j, ((if m i j = 0 then projJ (X i * G j) else 0) +
        (if n i j = 0 then antiJ (X i * G j) else 0)) := by
  have hc : ∀ i j, Continuous fun r : ℝ => rot (a i * r) * (X i * G j) * rot (b j * r) :=
    fun i j => by unfold rot; fun_prop
  have e : ∀ r : ℝ, (∑ i, rot (a i * r) * X i) * (∑ j, G j * rot (b j * r)) =
      ∑ i, ∑ j, rot (a i * r) * (X i * G j) * rot (b j * r) := by
    intro r
    rw [Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mul_assoc]
  simp_rw [e]
  rw [intervalIntegral.integral_finsetSum fun i _ =>
      (continuous_finsetSum _ fun j _ => hc i j).intervalIntegrable _ _, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum fun j _ => (hc i j).intervalIntegrable _ _,
    Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => integral_rot_mul_mul_rot hω _ (hm i j) (hn i j)

end Harmonics

/-! ## The closed form of the effective matrix -/

section ClosedForm

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The coupling that survives with the rotation-commuting part:
`βΓ_a + X₊Γ_b + X₋Γ_c`, `Γ_a = sylv A_s (ω/2) γ`, `Γ_b = sylv A_s (−ω/2) Z₋`,
`Γ_c = sylv A_s (3ω/2) Z₃` (`β = B₁₂`, `γ = B₂₁`). -/
def couplingP (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  B.toBlocks₁₂ * sylv As (ω / 2) B.toBlocks₂₁ + upPlus A * sylv As (-(ω / 2)) (lowMinus A) +
    upMinus A * sylv As (3 * ω / 2) (lowThree A)

/-- The coupling that survives with the anticommuting part: `βΓ_b + X₊Γ_a`. -/
def couplingN (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) (ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  B.toBlocks₁₂ * sylv As (-(ω / 2)) (lowMinus A) + upPlus A * sylv As (ω / 2) B.toBlocks₂₁

@[tmio T, powerlib_foundation] private theorem projJ_add (M N : Matrix (Fin 2) (Fin 2) ℝ) :
    projJ (M + N) = projJ M + projJ N := by
  simp only [projJ, Matrix.add_apply]; module

@[tmio T, powerlib_foundation] private theorem antiJ_add (M N : Matrix (Fin 2) (Fin 2) ℝ) :
    antiJ (M + N) = antiJ M + antiJ N := by
  simp only [antiJ, Matrix.add_apply]; module

@[tmio T, powerlib_foundation] private theorem rot_odd_pi {ω : ℝ} (hω : 0 < ω) :
    rot (ω / 2 * (2 * Real.pi / ω)) = -1 ∧ rot (-(ω / 2) * (2 * Real.pi / ω)) = -1 ∧
      rot (3 * ω / 2 * (2 * Real.pi / ω)) = -1 := by
  have h1 : ω / 2 * (2 * Real.pi / ω) = Real.pi := by field_simp
  have h2 : -(ω / 2) * (2 * Real.pi / ω) = -Real.pi := by field_simp
  have h3 : 3 * ω / 2 * (2 * Real.pi / ω) = Real.pi + 2 * Real.pi := by field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; simp [rot]
  · rw [h2]; simp [rot]
  · rw [h3]; simp [rot, Real.cos_add_two_pi, Real.sin_add_two_pi]

set_option maxHeartbeats 2000000 in
/-- **The effective second-order matrix of a block core in closed form.** For the core
`BlockAveraging.fullB s d ω A_s A B` with any finite stable block (`ρ(e^{TA_s}) < 1`,
`T = 2π/ω`), any modulation `A` (coupling blocks `A₁₂`, `A₂₁` included) and any constant `B`:
`N_eff = N₂(F₁₁) − T (P(βΓ_a + X₊Γ_b + X₋Γ_c) + N(βΓ_b + X₊Γ_a))`, where `F₁₁` is the critical
block of the standard form, `P`, `N` the parts commuting and anticommuting with `J`, and
`Γ_a = sylv A_s (ω/2) B₂₁`, `Γ_b = sylv A_s (−ω/2) Z₋`, `Γ_c = sylv A_s (3ω/2) Z₃` solve the
rotating Sylvester equations of the three harmonics of the coupling out of the pair. The constant
coupling acts through the resolvent at `jω/2`; the modulated couplings meet each other through
`−jω/2` and `3jω/2` and the constant ones through the anticommuting part. -/
@[tmio T, powerlib_foundation] theorem effSecond_closed_form (s d : ℝ) {ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    effSecond (FzcB s d ω (2 * Real.pi / ω) As A B) (2 * Real.pi / ω)
        (expS As (2 * Real.pi / ω)) =
      secondTerm (fun t => stdForm s d ω A.toBlocks₁₁ t +
          rot (-(ω * t / 2)) * B.toBlocks₁₁ * rot (ω * t / 2)) (2 * Real.pi / ω) -
        (2 * Real.pi / ω) • (projJ (couplingP As A B ω) + antiJ (couplingN As A B ω)) := by
  set T := 2 * Real.pi / ω with hTdef
  have hT : 0 < T := by positivity
  obtain ⟨hπ1, hπ2, hπ3⟩ := rot_odd_pi hω
  rw [← hTdef] at hπ1 hπ2 hπ3
  set Ga := sylv As (ω / 2) B.toBlocks₂₁ with hGa
  set Gb := sylv As (-(ω / 2)) (lowMinus A) with hGb
  set Gc := sylv As (3 * ω / 2) (lowThree A) with hGc
  have sa := sylv_spec (isUnit_sylv_of_spectralRadius hρ hπ1) B.toBlocks₂₁
  have sb := sylv_spec (isUnit_sylv_of_spectralRadius hρ hπ2) (lowMinus A)
  have sc := sylv_spec (isUnit_sylv_of_spectralRadius hρ hπ3) (lowThree A)
  rw [← hGa] at sa
  rw [← hGb] at sb
  rw [← hGc] at sc
  set Γ : ℝ → Matrix Y (Fin 2) ℝ := fun u => Ga * rot (ω / 2 * u) + Gb * rot (-(ω / 2) * u) +
    Gc * rot (3 * ω / 2 * u) with hΓd
  set Γ' : ℝ → Matrix Y (Fin 2) ℝ := fun u => (ω / 2) • (Ga * rot (ω / 2 * u) * quarter) +
    (-(ω / 2)) • (Gb * rot (-(ω / 2) * u) * quarter) +
      (3 * ω / 2) • (Gc * rot (3 * ω / 2 * u) * quarter) with hΓ'd
  have hΓ : ∀ u, HasDerivAt Γ (Γ' u) u := fun u =>
    ((hasDerivAt_mul_rot Ga _ u).add (hasDerivAt_mul_rot Gb _ u)).add (hasDerivAt_mul_rot Gc _ u)
  have heq : ∀ u, As * Γ u - Γ' u = (modN A ω u + B).toBlocks₂₁ * rot (ω * u / 2) := by
    intro u
    rw [coupling₂₁_mul_rot, ← mul_rot_spec sa u, ← mul_rot_spec sb u, ← mul_rot_spec sc u]
    simp only [hΓd, hΓ'd, Matrix.mul_add]
    abel
  have hper : Γ T = -Γ 0 := by
    simp only [hΓd, mul_zero, rot_zero', hπ1, hπ2, hπ3, Matrix.mul_one, Matrix.mul_neg]
    abel
  rw [effSecond_eq_sub hT As A B hΓ heq hper (isUnit_one_add_of_spectralRadius hρ)]
  congr 1
  have hint : ∀ r, rot (-(ω * r / 2)) * (modN A ω r + B).toBlocks₁₂ * Γ r =
      (∑ i : Fin 3, rot (![-(ω / 2), ω / 2, -(3 * ω / 2)] i * r) *
          ![B.toBlocks₁₂, upPlus A, upMinus A] i) *
        (∑ j : Fin 3, ![Ga, Gb, Gc] j * rot (![ω / 2, -(ω / 2), 3 * ω / 2] j * r)) := by
    intro r
    rw [rot_mul_coupling₁₂, Fin.sum_univ_three, Fin.sum_univ_three]
    rfl
  rw [intervalIntegral.integral_congr fun r _ => hint r,
    integral_harmonic_product hω _ _ _ _ ![![0, -1, 1], ![1, 0, 2], ![-1, -2, 0] ]
      ![![1, 0, 2], ![0, -1, 1], ![2, 1, 3] ]
      (by intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring)]
  congr 1
  simp only [Fin.sum_univ_three]
  simp [couplingP, couplingN, projJ_add, antiJ_add]
  abel

end ClosedForm

/-! ## The critical block with a constant perturbation -/

section Critical

open SecondOrder (trigPoly stdCos stdSin antiPump)

/-- The anti-shift `n = u B r̄ = ((B₀₀ − B₁₁) + j(B₀₁ + B₁₀))/2` of a constant perturbation of the
pair (`u = (1, j)/2`, `r = (1, −j)`): the coefficient of `z̄` in `ż` that `B` adds, rotating at
`−ω` relative to `z`. It is the complex form of the anticommuting part, `N(B) ≅ n`. -/
def antiShift (B : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := ⟨(B 0 0 - B 1 1) / 2, (B 0 1 + B 1 0) / 2⟩

/-- `κ = conj(A₁₀ − A₀₁)/2`: the coefficient pair `(κ₁, σ₁)` of `J` in the cosine and sine
fundamentals `stdCos A 1`, `stdSin A 1` of the rotating-frame matrix, `κ = κ₁ + jσ₁`. -/
def fundSkew (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := star (A 1 0 - A 0 1) / 2

/-- **The decisive second-order quantity of a pumped pair with a constant perturbation** `B`:
`d|g'|²/(4ω) + (2/ω)(Re(κ (g/2) n̄) + d|n|²)` with the anti-resonant pump `g' = antiPump A`, the
pump `g = u A r̄`, `κ = fundSkew A` and the anti-shift `n = antiShift B` (`d` the shifted
detuning). For `B` commuting with `J` (`n = 0`) it is `d|g'|²/(4ω)`
(`SecondOrder.mixedDet_secondTerm_stdForm`). -/
def critMixed (d ω : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  d * ‖antiPump A‖ ^ 2 / (4 * ω) +
    2 / ω * ((fundSkew A * (Element.pump A left right / 2) * star (antiShift B)).re +
      d * ‖antiShift B‖ ^ 2)

@[tmio T, powerlib_foundation] private theorem crit_eq_trigPoly (s d ω : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    (fun t => stdForm s d ω A t + rot (-(ω * t / 2)) * B * rot (ω * t / 2)) =
      trigPoly (slowFlowMatrix (s - (B 0 0 + B 1 1) / 2) (d - (B 1 0 - B 0 1) / 2)
          (Element.pump A left right / 2))
        (fun k => stdCos A k + if k = 1 then B - BlockAveraging.commPart B else 0)
        (fun k => stdSin A k + if k = 1 then (B - BlockAveraging.commPart B) * quarter else 0)
        {1, 2} ω := by
  funext t
  rw [SecondOrder.stdForm_eq_trigPoly, BlockAveraging.rot_conj, SecondOrder.trigPoly,
    SecondOrder.trigPoly, Finset.sum_pair (by norm_num), Finset.sum_pair (by norm_num)]
  have hθ : 2 * (ω * t / 2) = ((1 : ℕ) : ℝ) * (ω * t) := by push_cast; ring
  have hM : slowFlowMatrix (s - (B 0 0 + B 1 1) / 2) (d - (B 1 0 - B 0 1) / 2)
      (Element.pump A left right / 2) = slowFlowMatrix s d (Element.pump A left right / 2) +
        BlockAveraging.commPart B := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [slowFlowMatrix, BlockAveraging.commPart] <;> ring
  rw [hθ, hM]
  simp only [↓reduceIte, OfNat.ofNat_ne_one, add_zero, smul_add]
  abel

@[tmio T, powerlib_foundation] private theorem mixed_one (s d : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℝ) :
    mixedDet (slowFlowMatrix s d (Element.pump A left right / 2))
        ((stdSin A 1 + (B - BlockAveraging.commPart B) * quarter) *
            (stdCos A 1 + (B - BlockAveraging.commPart B)) -
          (stdCos A 1 + (B - BlockAveraging.commPart B)) *
            (stdSin A 1 + (B - BlockAveraging.commPart B) * quarter)) =
      4 * ((fundSkew A * (Element.pump A left right / 2) * star (antiShift B)).re +
        d * ‖antiShift B‖ ^ 2) := by
  rw [Complex.sq_norm, Complex.normSq_apply, TwoToOne.pump_base]
  simp only [mixedDet, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply,
    Matrix.add_apply]
  simp [stdCos, stdSin, BlockAveraging.commPart, slowFlowMatrix, quarter, fundSkew, antiShift,
    Complex.mul_re, Complex.mul_im]
  ring

@[tmio T, powerlib_foundation] private theorem mixed_two (s d : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    mixedDet (slowFlowMatrix s d (Element.pump A left right / 2))
        (stdSin A 2 * stdCos A 2 - stdCos A 2 * stdSin A 2) = d * ‖antiPump A‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, SecondOrder.antiPump_eq, TwoToOne.pump_base]
  simp only [mixedDet, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply]
  simp [stdCos, stdSin, slowFlowMatrix, refl1, refl2]
  ring

/-- **The critical block with a constant perturbation, at second order.** For the critical block
`F₁₁(t) = stdForm s d ω A t + R(−ωt/2) B R(ωt/2)` of a block standard form (`T = 2π/ω`), with the
shifted damping and detuning `s' = s − (B₀₀ + B₁₁)/2`, `d' = d − (B₁₀ − B₀₁)/2` and
`M = slowFlowMatrix s' d' (g/2)`:
`mixedDet(M, N₂(F₁₁)) = −s'T²(s'² + d'² − |g/2|²) + T · critMixed d' ω A B`. The commuting part
of `B` only shifts `(s, d)`; its anticommuting part `n` adds a fundamental (`ω`) component that
meets the pump fundamental `κ` and itself: `(2T/ω)(Re(κ (g/2) n̄) + d'|n|²)`. -/
@[tmio T, powerlib_foundation] theorem mixedDet_secondTerm_crit (s d : ℝ) {ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    mixedDet (slowFlowMatrix (s - (B 0 0 + B 1 1) / 2) (d - (B 1 0 - B 0 1) / 2)
        (Element.pump A left right / 2))
      (secondTerm (fun t => stdForm s d ω A t + rot (-(ω * t / 2)) * B * rot (ω * t / 2))
        (2 * Real.pi / ω)) =
      -((s - (B 0 0 + B 1 1) / 2) * (2 * Real.pi / ω) ^ 2 *
          ((s - (B 0 0 + B 1 1) / 2) ^ 2 + (d - (B 1 0 - B 0 1) / 2) ^ 2 -
            ‖Element.pump A left right / 2‖ ^ 2)) +
        2 * Real.pi / ω * critMixed (d - (B 1 0 - B 0 1) / 2) ω A B := by
  rw [crit_eq_trigPoly, SecondOrder.mixedDet_secondTerm_trigPoly hω (by simp),
    Finset.sum_pair (by norm_num), trace_slowFlowMatrix, det_slowFlowMatrix]
  simp only [↓reduceIte, OfNat.ofNat_ne_one, add_zero, Nat.cast_one, Nat.cast_ofNat]
  rw [mixed_one, mixed_two, critMixed]
  have hω0 : ω ≠ 0 := hω.ne'
  field_simp
  ring

end Critical

/-! ## The block core on its first-order boundary -/

section Boundary

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The complex form `p + jq` of the commuting part `pI + qJ` of a real `2 × 2` matrix
(`= u M r`). -/
def projC (M : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := ⟨(M 0 0 + M 1 1) / 2, (M 1 0 - M 0 1) / 2⟩

/-- **The decisive quantity of a block core** on its first-order boundary:
`critMixed d' ω A₁₁ B₁₁ + 2 Re((s' − jd') c_P) + 2 Re((g/2) c̄_N)` with `c_P = projC(couplingP)`,
`c_N = antiShift(couplingN)` (the complex forms of the commuting and anticommuting parts of the
two coupling sums), `s' = s − shiftRe B`, `d' = d − shiftIm B`, `g = u A₁₁ r̄`. -/
def blockMixed (s d ω : ℝ) (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ) : ℝ :=
  critMixed (d - shiftIm B) ω A.toBlocks₁₁ B.toBlocks₁₁ +
    2 * ((((s - shiftRe B : ℝ) : ℂ) - ((d - shiftIm B : ℝ) : ℂ) * I) *
      projC (couplingP As A B ω)).re +
    2 * ((Element.pump A.toBlocks₁₁ left right / 2) * star (antiShift (couplingN As A B ω))).re

set_option maxHeartbeats 1000000 in
/-- `mixedDet(M, N_eff) = −s'T²(s'² + d'² − |g/2|²) + T · blockMixed` for every block core. -/
@[tmio T, powerlib_foundation] theorem mixedDet_effSecond (s d : ℝ) {ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    mixedDet (slowFlowMatrix (s - shiftRe B) (d - shiftIm B)
        (Element.pump A.toBlocks₁₁ left right / 2))
      (effSecond (FzcB s d ω (2 * Real.pi / ω) As A B) (2 * Real.pi / ω)
        (expS As (2 * Real.pi / ω))) =
      -((s - shiftRe B) * (2 * Real.pi / ω) ^ 2 * ((s - shiftRe B) ^ 2 + (d - shiftIm B) ^ 2 -
          ‖Element.pump A.toBlocks₁₁ left right / 2‖ ^ 2)) +
        2 * Real.pi / ω * blockMixed s d ω As A B := by
  rw [effSecond_closed_form s d hω As A B hρ]
  set M := slowFlowMatrix (s - shiftRe B) (d - shiftIm B)
    (Element.pump A.toBlocks₁₁ left right / 2) with hM
  have hsub : ∀ X Z : Matrix (Fin 2) (Fin 2) ℝ, mixedDet M (X - Z) = mixedDet M X - mixedDet M Z :=
    fun X Z => by simp only [mixedDet, Matrix.trace_sub, Matrix.mul_sub]; ring
  have hadd : ∀ X Z : Matrix (Fin 2) (Fin 2) ℝ, mixedDet M (X + Z) = mixedDet M X + mixedDet M Z :=
    fun X Z => by simp only [mixedDet, Matrix.trace_add, Matrix.mul_add]; ring
  have hsm : ∀ (c : ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ), mixedDet M (c • X) = c * mixedDet M X :=
    fun c X => by simp only [mixedDet, Matrix.trace_smul, Matrix.mul_smul, smul_eq_mul]; ring
  have hcrit := mixedDet_secondTerm_crit s d hω A.toBlocks₁₁ B.toBlocks₁₁
  have hP : ∀ X : Matrix (Fin 2) (Fin 2) ℝ, mixedDet M (projJ X) =
      -(2 * ((((s - shiftRe B : ℝ) : ℂ) - ((d - shiftIm B : ℝ) : ℂ) * I) * projC X).re) := by
    intro X
    simp only [hM, mixedDet, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp [projJ, projC, slowFlowMatrix, quarter]
    ring
  have hN : ∀ X : Matrix (Fin 2) (Fin 2) ℝ, mixedDet M (antiJ X) =
      -(2 * ((Element.pump A.toBlocks₁₁ left right / 2) * star (antiShift X)).re) := by
    intro X
    simp only [hM, mixedDet, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp [antiJ, antiShift, slowFlowMatrix, refl1, refl2]
    ring
  rw [hsub, hsm, hadd, hP, hN]
  have hre : shiftRe B = (B.toBlocks₁₁ 0 0 + B.toBlocks₁₁ 1 1) / 2 := rfl
  have him : shiftIm B = (B.toBlocks₁₁ 1 0 - B.toBlocks₁₁ 0 1) / 2 := rfl
  rw [hM, hre, him, hcrit, blockMixed, hre, him]
  ring

/-- **A block core on its first-order boundary, decided in closed form.** For
`BlockAveraging.fullB s d ω A_s A B ε` — the critical pair `−εs ± j(ω/2 − εd)`, any finite stable
block `A_s` (`ρ(e^{TA_s}) < 1`, `T = 2π/ω`), the modulation `ε Re{A e^{jωt}}` on every block and
the constant `εB` on every block — on the first-order boundary `s'² + d'² = |g/2|²`, `s' > 0`
(`s' = s − shiftRe B`, `d' = d − shiftIm B`, `g = u A₁₁ r̄`): for all small `ε > 0`,
`blockMixed > 0` puts every Floquet multiplier inside the unit circle and `blockMixed < 0` gives
Floquet instability. -/
@[tmio T, powerlib_foundation] theorem block_boundary {s d ω : ℝ} (hω : 0 < ω) (As : Matrix Y Y ℝ)
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)
    (hs : 0 < s - shiftRe B)
    (hb : (s - shiftRe B) ^ 2 + (d - shiftIm B) ^ 2 =
      ‖Element.pump A.toBlocks₁₁ left right / 2‖ ^ 2)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    (0 < blockMixed s d ω As A B →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : Fin 2 ⊕ Y → ℂ), v ≠ 0 →
        (Periodic.monodromy (fullB s d ω As A B ε) (2 * Real.pi / ω) 0).map (algebraMap ℝ ℂ) *ᵥ
          v = μ • v → ‖μ‖ < 1) ∧
      (blockMixed s d ω As A B < 0 →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          Periodic.FloquetUnstable (fullB s d ω As A B ε) (2 * Real.pi / ω)) := by
  have hT : 0 < 2 * Real.pi / ω := by positivity
  have h := BlockBoundary.averagingB_boundary hω As A B hs hb hρ
  rw [mixedDet_effSecond s d hω As A B hρ, ← hb, sub_self, mul_zero, neg_zero, zero_add] at h
  exact ⟨fun hpos => h.1 (mul_pos hT hpos), fun hneg => h.2 (mul_neg_of_pos_of_neg hT hneg)⟩

end Boundary

/-! ## The coupling terms through the complex resolvents of the stable block -/

section Resolvent

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The resolvent `(A_s − z)⁻¹` of the complexified stable block. -/
def stableRes (As : Matrix Y Y ℝ) (z : ℂ) : Matrix Y Y ℂ :=
  (As.map (algebraMap ℝ ℂ) - z • (1 : Matrix Y Y ℂ))⁻¹

omit [DecidableEq Y] in
@[tmio T, powerlib_foundation] private theorem map_mulVec_right {Z : Type*} [Fintype Z]
    (X : Matrix Z (Fin 2) ℝ) :
    X.map (algebraMap ℝ ℂ) *ᵥ right = fun i => (X i 0 : ℂ) - I * X i 1 := by
  funext i; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, right]; ring

omit [DecidableEq Y] in
@[tmio T, powerlib_foundation] private theorem map_mulVec_star_right {Z : Type*} [Fintype Z]
    (X : Matrix Z (Fin 2) ℝ) :
    X.map (algebraMap ℝ ℂ) *ᵥ star right = fun i => (X i 0 : ℂ) + I * X i 1 := by
  funext i; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, right]; ring

@[tmio T, powerlib_foundation] private theorem isUnit_sub_of_sylv {As : Matrix Y Y ℝ} {μ : ℝ}
    (h : IsUnit (As * As + μ ^ 2 • (1 : Matrix Y Y ℝ)).det) (σ : ℝ) (hσ : σ ^ 2 = 1) :
    IsUnit (As.map (algebraMap ℝ ℂ) - ((σ * μ : ℝ) * I) • (1 : Matrix Y Y ℂ)).det := by
  set Ac := As.map (algebraMap ℝ ℂ)
  have hprod : (Ac - ((σ * μ : ℝ) * I) • (1 : Matrix Y Y ℂ)) *
      (Ac + ((σ * μ : ℝ) * I) • (1 : Matrix Y Y ℂ)) =
      (As * As + μ ^ 2 • (1 : Matrix Y Y ℝ)).map (algebraMap ℝ ℂ) := by
    have hI : ((σ * μ : ℝ) * I) * ((σ * μ : ℝ) * I) = -((μ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rw [show ((σ : ℂ) * μ * I) * ((σ : ℂ) * μ * I) = ((σ ^ 2 : ℝ) : ℂ) * μ ^ 2 * (I * I) by
        push_cast; ring, hσ, I_mul_I]
      push_cast; ring
    rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_smul' _ _ _ (fun _ => by simp),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_smul, Matrix.mul_one, smul_smul, hI]
    simp only [neg_smul]
    rw [show ((μ ^ 2 : ℝ) : ℂ) = (algebraMap ℝ ℂ) (μ ^ 2) from rfl]
    abel
  have hdet := congrArg Matrix.det hprod
  rw [Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hdet
  have hu : IsUnit ((algebraMap ℝ ℂ) (As * As + μ ^ 2 • (1 : Matrix Y Y ℝ)).det) := h.map _
  rw [← hdet] at hu
  exact (IsUnit.mul_iff.mp hu).1

/-- **The rotating Sylvester solution through the complex resolvent**: with `r = (1, −j)`,
`Γ r = (A_s − jμ)⁻¹ Z r` for `Γ = sylv A_s μ Z`. -/
@[tmio T, powerlib_foundation] theorem sylv_mulVec_right {As : Matrix Y Y ℝ} {μ : ℝ}
    (h : IsUnit (As * As + μ ^ 2 • (1 : Matrix Y Y ℝ)).det) (Z : Matrix Y (Fin 2) ℝ) :
    (sylv As μ Z).map (algebraMap ℝ ℂ) *ᵥ right =
      stableRes As ((μ : ℂ) * I) *ᵥ (Z.map (algebraMap ℝ ℂ) *ᵥ right) := by
  have hs := sylv_spec h Z
  have hu := isUnit_sub_of_sylv h 1 (one_pow 2)
  rw [one_mul] at hu
  set M := As.map (algebraMap ℝ ℂ) - ((μ : ℝ) * I) • (1 : Matrix Y Y ℂ) with hM
  have key : M *ᵥ ((sylv As μ Z).map (algebraMap ℝ ℂ) *ᵥ right) =
      Z.map (algebraMap ℝ ℂ) *ᵥ right := by
    have hA : As.map (algebraMap ℝ ℂ) *ᵥ ((sylv As μ Z).map (algebraMap ℝ ℂ) *ᵥ right) =
        (As * sylv As μ Z).map (algebraMap ℝ ℂ) *ᵥ right := by
      rw [Matrix.mulVec_mulVec, Matrix.map_mul]
    rw [hM, Matrix.sub_mulVec, hA, Matrix.smul_mulVec, Matrix.one_mulVec, map_mulVec_right,
      map_mulVec_right, map_mulVec_right]
    funext i
    have h0 := congrFun (congrFun hs i) 0
    have h1 := congrFun (congrFun hs i) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, quarter] at h0 h1
    apply Complex.ext <;> simp [Matrix.mul_apply] <;> linarith
  rw [← key, stableRes, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

/-- With `r̄ = (1, j)`: `Γ r̄ = (A_s + jμ)⁻¹ Z r̄` for `Γ = sylv A_s μ Z`. -/
@[tmio T, powerlib_foundation] theorem sylv_mulVec_star_right {As : Matrix Y Y ℝ} {μ : ℝ}
    (h : IsUnit (As * As + μ ^ 2 • (1 : Matrix Y Y ℝ)).det) (Z : Matrix Y (Fin 2) ℝ) :
    (sylv As μ Z).map (algebraMap ℝ ℂ) *ᵥ star right =
      stableRes As (-((μ : ℂ) * I)) *ᵥ (Z.map (algebraMap ℝ ℂ) *ᵥ star right) := by
  have hs := sylv_spec h Z
  have hu := isUnit_sub_of_sylv h (-1) (by norm_num)
  set M := As.map (algebraMap ℝ ℂ) - ((-1 * μ : ℝ) * I) • (1 : Matrix Y Y ℂ) with hM
  have key : M *ᵥ ((sylv As μ Z).map (algebraMap ℝ ℂ) *ᵥ star right) =
      Z.map (algebraMap ℝ ℂ) *ᵥ star right := by
    have hA : As.map (algebraMap ℝ ℂ) *ᵥ ((sylv As μ Z).map (algebraMap ℝ ℂ) *ᵥ star right) =
        (As * sylv As μ Z).map (algebraMap ℝ ℂ) *ᵥ star right := by
      rw [Matrix.mulVec_mulVec, Matrix.map_mul]
    rw [hM, Matrix.sub_mulVec, hA, Matrix.smul_mulVec, Matrix.one_mulVec, map_mulVec_star_right,
      map_mulVec_star_right, map_mulVec_star_right]
    funext i
    have h0 := congrFun (congrFun hs i) 0
    have h1 := congrFun (congrFun hs i) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, quarter] at h0 h1
    apply Complex.ext <;> simp [Matrix.mul_apply] <;> linarith
  have hz : -((μ : ℂ) * I) = ((-1 * μ : ℝ) : ℂ) * I := by push_cast; ring
  rw [← key, stableRes, hz, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

@[tmio T, powerlib_foundation] private theorem projC_eq (M : Matrix (Fin 2) (Fin 2) ℝ) :
    projC M = left ⬝ᵥ (M.map (algebraMap ℝ ℂ) *ᵥ right) := by
  apply Complex.ext <;>
    simp [projC, left, right, dotProduct, Matrix.mulVec, Fin.sum_univ_two] <;> ring

@[tmio T, powerlib_foundation] private theorem antiShift_eq (M : Matrix (Fin 2) (Fin 2) ℝ) :
    antiShift M = left ⬝ᵥ (M.map (algebraMap ℝ ℂ) *ᵥ star right) := by
  apply Complex.ext <;>
    simp [antiShift, left, right, dotProduct, Matrix.mulVec, Fin.sum_univ_two] <;> ring

omit [DecidableEq Y] in
@[tmio T, powerlib_foundation] private theorem dot_map_mul (X : Matrix (Fin 2) Y ℝ)
    (G : Matrix Y (Fin 2) ℝ) (w : Fin 2 → ℂ) :
    left ⬝ᵥ ((X * G).map (algebraMap ℝ ℂ) *ᵥ w) =
      (left ᵥ* X.map (algebraMap ℝ ℂ)) ⬝ᵥ (G.map (algebraMap ℝ ℂ) *ᵥ w) := by
  rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]

omit [Fintype Y] [DecidableEq Y] in
@[tmio T, powerlib_foundation] private theorem left_upPlus (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) :
    left ᵥ* (upPlus A).map (algebraMap ℝ ℂ) = (1 / 2 : ℂ) • (left ᵥ* A.toBlocks₁₂) := by
  funext k
  simp only [upPlus, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul,
    Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply]
  apply Complex.ext <;> simp [left, quarter, Matrix.toBlocks₁₂] <;> ring

omit [Fintype Y] [DecidableEq Y] in
@[tmio T, powerlib_foundation] private theorem left_upMinus (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) :
    left ᵥ* (upMinus A).map (algebraMap ℝ ℂ) =
      (1 / 2 : ℂ) • (left ᵥ* A.toBlocks₁₂.map star) := by
  funext k
  simp only [upMinus, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul,
    Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_apply]
  apply Complex.ext <;> simp [left, quarter, Matrix.toBlocks₁₂] <;> ring

omit [Fintype Y] [DecidableEq Y] in
@[tmio T, powerlib_foundation] private theorem lowMinus_right
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) :
    (lowMinus A).map (algebraMap ℝ ℂ) *ᵥ right =
      (1 / 2 : ℂ) • (A.toBlocks₂₁.map star *ᵥ right) := by
  funext k
  simp only [lowMinus, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul,
    Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_apply]
  apply Complex.ext <;> simp [right, quarter, Matrix.toBlocks₂₁] <;> ring

omit [Fintype Y] [DecidableEq Y] in
@[tmio T, powerlib_foundation] private theorem lowMinus_star_right
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) :
    (lowMinus A).map (algebraMap ℝ ℂ) *ᵥ star right =
      (1 / 2 : ℂ) • (A.toBlocks₂₁ *ᵥ star right) := by
  funext k
  simp only [lowMinus, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul,
    Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_apply]
  apply Complex.ext <;> simp [right, quarter, Matrix.toBlocks₂₁] <;> ring

omit [Fintype Y] [DecidableEq Y] in
@[tmio T, powerlib_foundation] private theorem lowThree_right
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) :
    (lowThree A).map (algebraMap ℝ ℂ) *ᵥ right = (1 / 2 : ℂ) • (A.toBlocks₂₁ *ᵥ right) := by
  funext k
  simp only [lowThree, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul,
    Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply]
  apply Complex.ext <;> simp [right, quarter, Matrix.toBlocks₂₁]
  ring

/-- **The commuting coupling through the resolvents of the stable block.** With `u = (1, j)/2`,
`r = (1, −j)`, `β = B₁₂`, `γ = B₂₁` and `ρ(e^{TA_s}) < 1`:
`projC(couplingP) = (uβ)(A_s − jω/2)⁻¹(γr) + ¼(uA₁₂)(A_s + jω/2)⁻¹(Ā₂₁r)
  + ¼(uĀ₁₂)(A_s − 3jω/2)⁻¹(A₂₁r)`. -/
@[tmio T, powerlib_foundation] theorem projC_couplingP {ω : ℝ} (hω : 0 < ω) (As : Matrix Y Y ℝ)
    (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ) (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    projC (couplingP As A B ω) =
      (left ᵥ* B.toBlocks₁₂.map (algebraMap ℝ ℂ)) ⬝ᵥ
          (stableRes As (((ω / 2 : ℝ) : ℂ) * I) *ᵥ (B.toBlocks₂₁.map (algebraMap ℝ ℂ) *ᵥ right)) +
        1 / 4 * ((left ᵥ* A.toBlocks₁₂) ⬝ᵥ
          (stableRes As (-(((ω / 2 : ℝ) : ℂ) * I)) *ᵥ (A.toBlocks₂₁.map star *ᵥ right))) +
        1 / 4 * ((left ᵥ* A.toBlocks₁₂.map star) ⬝ᵥ
          (stableRes As (((3 * ω / 2 : ℝ) : ℂ) * I) *ᵥ (A.toBlocks₂₁ *ᵥ right))) := by
  obtain ⟨hπ1, hπ2, hπ3⟩ := rot_odd_pi hω
  have h1 := isUnit_sylv_of_spectralRadius hρ hπ1
  have h2 := isUnit_sylv_of_spectralRadius hρ hπ2
  have h3 := isUnit_sylv_of_spectralRadius hρ hπ3
  have hneg : ((-(ω / 2) : ℝ) : ℂ) * I = -(((ω / 2 : ℝ) : ℂ) * I) := by push_cast; ring
  rw [projC_eq, couplingP, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _),
    Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add, dot_map_mul,
    dot_map_mul, dot_map_mul, sylv_mulVec_right h1, sylv_mulVec_right h2, sylv_mulVec_right h3,
    hneg, left_upPlus, left_upMinus, lowMinus_right, lowThree_right, Matrix.mulVec_smul,
    Matrix.mulVec_smul, smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

/-- **The anticommuting coupling through the resolvents of the stable block.** With
`r̄ = (1, j)`: `antiShift(couplingN) = ½(uβ)(A_s − jω/2)⁻¹(A₂₁r̄) + ½(uA₁₂)(A_s + jω/2)⁻¹(γr̄)`. -/
@[tmio T, powerlib_foundation] theorem antiShift_couplingN {ω : ℝ} (hω : 0 < ω)
    (As : Matrix Y Y ℝ) (A : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℂ)
    (B : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ)
    (hρ : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    antiShift (couplingN As A B ω) =
      1 / 2 * ((left ᵥ* B.toBlocks₁₂.map (algebraMap ℝ ℂ)) ⬝ᵥ
          (stableRes As (((ω / 2 : ℝ) : ℂ) * I) *ᵥ (A.toBlocks₂₁ *ᵥ star right))) +
        1 / 2 * ((left ᵥ* A.toBlocks₁₂) ⬝ᵥ (stableRes As (-(((ω / 2 : ℝ) : ℂ) * I)) *ᵥ
          (B.toBlocks₂₁.map (algebraMap ℝ ℂ) *ᵥ star right))) := by
  obtain ⟨hπ1, hπ2, -⟩ := rot_odd_pi hω
  have h1 := isUnit_sylv_of_spectralRadius hρ hπ1
  have h2 := isUnit_sylv_of_spectralRadius hρ hπ2
  have hneg : -(((-(ω / 2) : ℝ) : ℂ) * I) = ((ω / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [antiShift_eq, couplingN, Matrix.map_add _ (map_add _), Matrix.add_mulVec, dotProduct_add,
    dot_map_mul, dot_map_mul, sylv_mulVec_star_right h1, sylv_mulVec_star_right h2, hneg,
    left_upPlus, lowMinus_star_right, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]

end Resolvent

/-! ## Cores perturbed through one equation -/

section SameRow

@[tmio T, powerlib_foundation] private theorem sr_norm_sq_half (c : ℝ) :
    ‖(c : ℂ) * I / 2‖ ^ 2 = c ^ 2 / 4 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

@[tmio T, powerlib_foundation] private theorem sr_re_mul_mk (a b p q : ℝ) :
    (((a : ℂ) - (b : ℂ) * I) * (⟨p, q⟩ : ℂ)).re = a * p + b * q := by
  simp [Complex.mul_re]

@[tmio T, powerlib_foundation] private theorem sr_re_crit (a c x y : ℝ) :
    ((a : ℂ) * ((c : ℂ) * I / 2 / 2) * star (⟨x, y⟩ : ℂ)).re = a * c * y / 4 := by
  simp [Complex.mul_re, Complex.mul_im]; ring

@[tmio T, powerlib_foundation] private theorem sr_norm_sq_mk (x y : ℝ) :
    ‖(⟨x, y⟩ : ℂ)‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_mk]; ring

@[tmio T, powerlib_foundation] private theorem sr_re_quarter_star (c x y : ℝ) :
    ((c : ℂ) * I / 2 / 2 * star (⟨x, y⟩ : ℂ)).re = c * y / 4 := by
  simp [Complex.mul_re, Complex.mul_im]; ring

set_option maxHeartbeats 1000000 in
/-- **A core whose perturbation and modulation act through one equation.** When the constant
perturbation and the modulation of a three-state core both enter one physical equation (rank one
with the same row, e.g. the torque equation of a machine) and the stable mode is driven by the
pair, the modal blocks take the form `B₁₁ = [[0, 0], [−2d, −2s]]` (first-order damping `s`,
detuning `d`), `β = (0, b)ᵀ`, `γ = ρ(−2d, −2s)`, `B₂₂ = ρb`, `A₁₁ = [[0, 0], [a, 0]]`
(`g = ja`), `A₂₁ = ρ(a, 0)`, `A₁₂ = 0`, with one real stable mode `l`. Then
`blockMixed = d(s² + d² − 3a²/32)/ν − 2bρl(s² + d² − a²/16)/(l² + ν²)`: the constant and the
modulated coupling terms through the resolvent `(l − jν)⁻¹` add up to a multiple of
`s² + d² − |g/2|²` and vanish on the first-order boundary, where the verdict is the sign of
`−d`. -/
@[tmio T, powerlib_foundation] theorem sameRow_blockMixed (s d a b ρ l ν : ℝ)
    (hν : 0 < ν) :
    blockMixed 0 0 (2 * ν) !![l]
        (fromBlocks !![0, 0; (a : ℂ), 0] 0 !![((ρ * a : ℝ) : ℂ), 0] 0)
        (fromBlocks !![0, 0; -(2 * d), -(2 * s)] !![0; b] !![-(2 * ρ * d), -(2 * ρ * s)]
          !![ρ * b]) =
      d * (s ^ 2 + d ^ 2 - 3 * a ^ 2 / 32) / ν -
        2 * b * ρ * l * (s ^ 2 + d ^ 2 - a ^ 2 / 16) / (l ^ 2 + ν ^ 2) := by
  set A : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℂ :=
    fromBlocks !![0, 0; (a : ℂ), 0] 0 !![((ρ * a : ℝ) : ℂ), 0] 0 with hA
  set B : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ :=
    fromBlocks !![0, 0; -(2 * d), -(2 * s)] !![0; b] !![-(2 * ρ * d), -(2 * ρ * s)] !![ρ * b]
    with hB
  have hA12 : A.toBlocks₁₂ = 0 := toBlocks_fromBlocks₁₂ _ _ _ _
  have hup : upPlus A = 0 := by simp [upPlus, hA12]
  have hum : upMinus A = 0 := by simp [upMinus, hA12]
  have hre : A.toBlocks₂₁.map Complex.re = !![ρ * a, 0] := by
    ext i j; fin_cases i; fin_cases j <;> simp [hA]
  have him : A.toBlocks₂₁.map Complex.im = 0 := by
    ext i j; fin_cases i; fin_cases j <;> simp [hA]
  have hlm : lowMinus A = !![ρ * a / 2, 0] := by
    rw [lowMinus, hre, him, Matrix.zero_mul, sub_zero]
    ext i j; fin_cases i; fin_cases j <;> simp; ring
  have hD : l ^ 2 + ν ^ 2 ≠ 0 := by
    have : 0 < ν ^ 2 := by positivity
    positivity
  have hD' : l ^ 2 + (-ν) ^ 2 ≠ 0 := by rw [neg_sq]; exact hD
  have h2 : 2 * ν / 2 = ν := by ring
  have hP : couplingP !![l] A B (2 * ν) =
      B.toBlocks₁₂ * (B.toBlocks₂₁ * ThreeStateCore.lamInv l ν) := by
    rw [couplingP, hup, hum, h2, sylv_fin_one hD]
    simp
  have hN : couplingN !![l] A B (2 * ν) =
      B.toBlocks₁₂ * (!![ρ * a / 2, 0] * ThreeStateCore.lamInv l (-ν)) := by
    rw [couplingN, hup, hlm, h2, sylv_fin_one hD']
    simp
  have hpump : Element.pump A.toBlocks₁₁ TwoToOne.left TwoToOne.right = (a : ℂ) * I / 2 := by
    rw [TwoToOne.pump_base]; simp [hA]; ring
  have hanti : ‖SecondOrder.antiPump A.toBlocks₁₁‖ ^ 2 = a ^ 2 / 4 := by
    have h : SecondOrder.antiPump A.toBlocks₁₁ = -((a : ℂ) * I / 2) := by
      rw [SecondOrder.antiPump_eq]; simp [hA]; ring
    rw [h, norm_neg, sr_norm_sq_half]
  have hκ : fundSkew A.toBlocks₁₁ = ((a / 2 : ℝ) : ℂ) := by simp [fundSkew, hA]
  have hn : antiShift B.toBlocks₁₁ = ⟨s, -d⟩ := by
    apply Complex.ext <;> simp [antiShift, hB] <;> ring
  have hsr : shiftRe B = -s := by simp [shiftRe, hB]; ring
  have hsi : shiftIm B = -d := by simp [shiftIm, hB]; ring
  have hpc : projC (B.toBlocks₁₂ * (B.toBlocks₂₁ * ThreeStateCore.lamInv l ν)) =
      ⟨b * ρ * (d * ν - s * l) / (l ^ 2 + ν ^ 2),
        -(b * ρ * (d * l + s * ν) / (l ^ 2 + ν ^ 2))⟩ := by
    apply Complex.ext <;> simp only [projC] <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one] <;>
      simp [hB, ThreeStateCore.lamInv, quarter] <;>
      field_simp <;> ring
  have hac : antiShift (B.toBlocks₁₂ * (!![ρ * a / 2, 0] * ThreeStateCore.lamInv l (-ν))) =
      ⟨-(b * ρ * a * ν / (4 * (l ^ 2 + ν ^ 2))), b * ρ * a * l / (4 * (l ^ 2 + ν ^ 2))⟩ := by
    apply Complex.ext <;> simp only [antiShift] <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one] <;>
      simp [hB, ThreeStateCore.lamInv, quarter] <;>
      field_simp <;> ring
  rw [blockMixed, hP, hN, critMixed, hpc, sr_re_mul_mk, hac, hpump, sr_re_quarter_star, hanti,
    hκ, hn,
    sr_re_crit, sr_norm_sq_mk, hsr, hsi]
  field_simp
  ring

end SameRow

end powerlib.ParametricResonance.BlockCoreClosedForm
