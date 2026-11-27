import theorem.ParametricResonance.BlockBoundary
import theorem.ParametricResonance.SecondOrderClosedForm

/-! # A three-state core on its first-order boundary: the effective matrix in closed form

`BlockBoundary.averagingB_boundary` decides the first-order boundary of an `n`-state 2:1 core by
the sign of `mixedDet(M, N_eff)`, `N_eff = effSecond F_z T E = (N₂)₁₁ − T² F̄₁₂ (I + E)⁻¹ E F̄₂₁`,
but leaves `N_eff` as an integral expression. This file computes it for the simplest core with a
stable block: the critical pair `−εs ± j(ω/2 − εd)` pumped by `ε Re{A₁₁ e^{jωt}}`, one stable real
mode `a` (`Y = Fin 1`, `E = e^{Ta}`, `T = 2π/ω`), coupled to the pair by a constant `O(ε)` column
`β` (stable mode → pair) and row `γ` (pair → stable mode); the stable mode may carry its own
modulation `c` and shift `b`, which do not enter at this order.

In the rotating frame the coupling blocks are `F₁₂(t) = e^{ta} R(−ωt/2) β`,
`F₂₁(t) = e^{−ta} γ R(ωt/2)` (`FzB_core₁₂`, `FzB_core₂₁`), i.e. `e^{tΛ}β` and `γ e^{−tΛ}` with
`Λ = aI − (ω/2)J`, and every integral is elementary (`L = Λ⁻¹ = lamInv a (ω/2)`, `R(π) = −I`):
* `T F̄₁₂ = −(1 + E) L β`, `T F̄₂₁ = (1 + E⁻¹) γ L`, so the Schur-complement correction is
  `−T² F̄₁₂ (1 + E)⁻¹ E F̄₂₁ = (1 + E) L βγ L`;
* the excursion through the stable mode in the critical block of the second Picard term
  (`secondTerm_toBlocks₁₁`) is `∫₀ᵀ F₁₂ ∫₀ʳ F₂₁ = −(1 + E) L βγ L − T P(βγ) L`, with `P` the
  rotating average (the part commuting with `J`, `integral_rot_conj`).
The `E`-dependent parts cancel: `N_eff = N₂(stdForm s d ω A₁₁) − T P(βγ) L` (`effSecond_core`).
The one-period gain `e^{Ta}` of the stable mode drops out; the stable mode acts through the
rotating resolvent `(a − jω/2)⁻¹` alone — the second-order eigenvalue shift of the critical pair by
adiabatic elimination of the stable mode. With the closed form of the two-state part
(`SecondOrder.mixedDet_secondTerm_stdForm`) the decisive quantity on the boundary
`s² + d² = |g/2|²` is `T · coreMixed`,
`coreMixed = d|g'|²/(4ω) + 2 Re{(s − jd)(p + jq)/(a − jω/2)}`,
`p + jq = ((β₀γ₀ + β₁γ₁) + j(β₁γ₀ − β₀γ₁))/2`, `g' = SecondOrder.antiPump A₁₁`, and the verdict is
an explicit inequality in the entries of the core (`three_state_boundary`).

Scope.
* Generic: real `2 × 2` matrices, the rotation `R(θ)` and quarter turn `J` of
  `NormalForm`; integrals over one pump period `T = 2π/ω`, `ω > 0`; the block identity for the
  second Picard term on `Fin 2 ⊕ Y`.
* Core: `BlockAveraging.fullB s d ω [a] (coreA A₁₁ c) (coreB β γ b) ε` — pump only on the critical
  block (`A₁₂ = A₂₁ = 0`), constant coupling `β`, `γ`, no first-order shift of the pair
  (`B₁₁ = 0`, so `shiftRe = shiftIm = 0`); `a < 0` for `ρ(E) < 1`; the boundary
  `s² + d² = |g/2|²`, `s > 0`; statements for all small `ε > 0`.
* Not covered: modulated coupling `A₁₂`, `A₂₁` (harmonics `3ω/2` enter the same integrals), a
  first-order shift `B₁₁ ≠ 0` of the pair, larger stable blocks; `coreMixed = 0` (next order).
* Generic mathematics; no model family. No engineering instance is given: the library has no
  model of the swing pair with a first-order governor or AVR lag in this modal form.

Source: the wave-6 question of this library (a closed form of `BlockBoundary.effSecond` for a
concrete core); `BlockBoundary.averagingB_boundary`, `SecondOrder.mixedDet_secondTerm_stdForm`
(`theorem/ParametricResonance/BlockBoundary.lean`,
`theorem/ParametricResonance/SecondOrderClosedForm.lean`); second-order perturbation of a critical
eigenvalue by a coupled stable mode (Kato, *Perturbation Theory for Linear Operators*, the
reduction process).

Results.
* `lamInv`, `projJ`, `lam_mul_lamInv`, `lamInv_comm_quarter`, `integral_exp_rot_neg`,
  `integral_exp_neg_rot`, `integral_rot_conj` — the rotating-frame integrals.
* `blk12`, `blk21`, `secondTerm_toBlocks₁₁` — the critical block of the second Picard term.
* `coreA`, `coreB`, `expS_fin_one`, `modN_coreA`, `FzB_core₁₁`, `FzB_core₁₂`, `FzB_core₂₁` — the
  core and its standard form; `mulRightL`, `mulLeftL`.
* `effSecond_core` — `N_eff = N₂(stdForm) − T P(βγ) (aI − (ω/2)J)⁻¹`.
* `coreMixed`, `mixedDet_effSecond_core`, `three_state_boundary` — the boundary verdict by the sign
  of `coreMixed`.

Corrections.
The expected form `N_eff = (N₂)_crit + T² F̄₁₂F̄₂₁ e^{Ta}/(1 + e^{Ta})` (with the critical block of
the second Picard term taken alone) is not what the computation gives: the Schur term
`(1 + E) L βγ L` is cancelled by the `E`-dependent part of the excursion term contained in
`(N₂)₁₁`, and `N_eff` does not depend on `e^{Ta}`.

Family and connection conclusions.
None: static evidence on linear periodic systems (Floquet multipliers).
-/

noncomputable section
namespace powerlib.ParametricResonance.ThreeStateCore

open Matrix Complex Set Filter Topology
open scoped Matrix.Norms.Operator Interval
open Boundary (mixedDet secondTerm)
open _root_.powerlib.ParametricResonance.NormalForm (rot quarter)
open TwoToOne (left right stdForm)
open BlockAveraging (fullB FzB FzcB Fz expS Psi PsiInv modN clampT)
open BlockBoundary (effSecond)

/-! ## Rotating-frame integrals with one real exponent -/

section Integrals

/-- `(aI − νJ)⁻¹ = (aI + νJ)/(a² + ν²)`, the resolvent of the stable exponent `a` seen from the
rotating frame of frequency `ν`. -/
def lamInv (a ν : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := (a ^ 2 + ν ^ 2)⁻¹ • (a • 1 + ν • quarter)

/-- The part of a `2 × 2` matrix commuting with the quarter turn:
`P(M) = ((M₀₀ + M₁₁)/2) I + ((M₁₀ − M₀₁)/2) J`. -/
def projJ (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ((M 0 0 + M 1 1) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + ((M 1 0 - M 0 1) / 2) • quarter

@[tmio T, powerlib_foundation] theorem lam_mul_lamInv {a ν : ℝ} (h : a ^ 2 + ν ^ 2 ≠ 0) :
    (a • (1 : Matrix (Fin 2) (Fin 2) ℝ) - ν • quarter) * lamInv a ν = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lamInv, quarter, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    field_simp <;> ring

@[tmio T, powerlib_foundation] theorem lamInv_comm_quarter (a ν : ℝ) :
    lamInv a ν * quarter = quarter * lamInv a ν := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lamInv, quarter, Matrix.mul_apply, Fin.sum_univ_two]

/-- `∫₀ᵀ e^{ta} R(−ωt/2) dt = −(1 + e^{Ta}) (aI − (ω/2)J)⁻¹`, `T = 2π/ω`. -/
@[tmio T, powerlib_foundation] theorem integral_exp_rot_neg {ω : ℝ} (hω : 0 < ω) (a : ℝ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi / ω), Real.exp (t * a) • rot (-(ω * t / 2)) =
      -(1 + Real.exp (2 * Real.pi / ω * a)) • lamInv a (ω / 2) := by
  set L := lamInv a (ω / 2) with hL
  have hne : a ^ 2 + (ω / 2) ^ 2 ≠ 0 := by positivity
  have hrot : ∀ t : ℝ, HasDerivAt (fun t => rot (-(ω * t / 2)))
      ((-(ω / 2)) • (rot (-(ω * t / 2)) * quarter)) t := fun t => by
    have h := NormalForm.hasDerivAt_rot (-ω) t
    have e : (fun t => rot (-ω * t / 2)) = fun t => rot (-(ω * t / 2)) := by
      funext s; congr 1; ring
    rw [e] at h
    convert h using 2
    · ring
    · congr 2; ring
  have hder : ∀ t ∈ uIcc (0 : ℝ) (2 * Real.pi / ω),
      HasDerivAt (fun t => Real.exp (t * a) • (rot (-(ω * t / 2)) * L))
        (Real.exp (t * a) • rot (-(ω * t / 2))) t := by
    intro t _
    have he : HasDerivAt (fun t => Real.exp (t * a)) (Real.exp (t * a) * a) t := by
      simpa using ((hasDerivAt_id t).mul_const a).exp
    have h : HasDerivAt (fun t => Real.exp (t * a) • (rot (-(ω * t / 2)) * L)) _ t :=
      he.smul ((hrot t).mul_const L)
    refine h.congr_deriv ?_
    have hlam : (a • (1 : Matrix (Fin 2) (Fin 2) ℝ) - (ω / 2) • quarter) * L = 1 := by
      rw [hL]; exact lam_mul_lamInv hne
    rw [show Real.exp (t * a) • rot (-(ω * t / 2)) = Real.exp (t * a) • (rot (-(ω * t / 2)) *
      ((a • (1 : Matrix (Fin 2) (Fin 2) ℝ) - (ω / 2) • quarter) * L)) from by rw [hlam, Matrix.mul_one] ]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      ← Matrix.mul_assoc, smul_sub, smul_smul]
    module
  have hcont : Continuous fun t => Real.exp (t * a) • rot (-(ω * t / 2)) := by
    unfold rot; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hcont.intervalIntegrable _ _)]
  have hpi : -(ω * (2 * Real.pi / ω) / 2) = -Real.pi := by field_simp
  have hr : rot (-Real.pi) = -1 := by simp [rot]
  simp only [hpi, hr, mul_zero, zero_div, neg_zero, Real.exp_zero, one_smul, zero_mul]
  have h0 : rot 0 = 1 := by simp [rot]
  rw [h0, Matrix.one_mul, Matrix.neg_mul, Matrix.one_mul, smul_neg, neg_smul, add_smul, one_smul]
  abel

/-- `∫₀ʳ e^{−ua} R(ωu/2) du = (I − e^{−ra} R(ωr/2)) (aI − (ω/2)J)⁻¹`. -/
@[tmio T, powerlib_foundation] theorem integral_exp_neg_rot (ω a r : ℝ) (hne : a ^ 2 + (ω / 2) ^ 2 ≠ 0) :
    ∫ u in (0 : ℝ)..r, Real.exp (-(u * a)) • rot (ω * u / 2) =
      (1 - Real.exp (-(r * a)) • rot (ω * r / 2)) * lamInv a (ω / 2) := by
  set L := lamInv a (ω / 2) with hL
  have hder : ∀ u ∈ uIcc (0 : ℝ) r,
      HasDerivAt (fun u => -(Real.exp (-(u * a)) • (rot (ω * u / 2) * L)))
        (Real.exp (-(u * a)) • rot (ω * u / 2)) u := by
    intro u _
    have he : HasDerivAt (fun u => Real.exp (-(u * a))) (Real.exp (-(u * a)) * (-a)) u := by
      simpa using (((hasDerivAt_id u).mul_const a).neg).exp
    have h : HasDerivAt (fun u => -(Real.exp (-(u * a)) • (rot (ω * u / 2) * L))) _ u :=
      (he.smul ((NormalForm.hasDerivAt_rot ω u).mul_const L)).neg
    refine h.congr_deriv ?_
    have hlam : (a • (1 : Matrix (Fin 2) (Fin 2) ℝ) - (ω / 2) • quarter) * L = 1 := by
      rw [hL]; exact lam_mul_lamInv hne
    rw [show Real.exp (-(u * a)) • rot (ω * u / 2) = Real.exp (-(u * a)) • (rot (ω * u / 2) *
      ((a • (1 : Matrix (Fin 2) (Fin 2) ℝ) - (ω / 2) • quarter) * L)) from by rw [hlam, Matrix.mul_one] ]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      ← Matrix.mul_assoc, smul_sub, smul_smul]
    module
  have hcont : Continuous fun u => Real.exp (-(u * a)) • rot (ω * u / 2) := by
    unfold rot; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hcont.intervalIntegrable _ _)]
  have h0 : rot (ω * 0 / 2) = 1 := by simp [rot]
  simp only [h0, zero_mul, neg_zero, Real.exp_zero, one_smul, Matrix.one_mul, Matrix.sub_mul,
    Matrix.smul_mul]
  abel

/-- `∫₀ᵀ R(−ωr/2) M R(ωr/2) dr = T P(M)`, `T = 2π/ω`: the rotating average keeps the part of `M`
commuting with `J`. -/
@[tmio T, powerlib_foundation] theorem integral_rot_conj {ω : ℝ} (hω : 0 < ω)
    (M : Matrix (Fin 2) (Fin 2) ℝ) :
    ∫ r in (0 : ℝ)..(2 * Real.pi / ω), rot (-(ω * r / 2)) * M * rot (ω * r / 2) =
      (2 * Real.pi / ω) • projJ M := by
  have hc : ∫ r in (0 : ℝ)..(2 * Real.pi / ω), Real.cos (ω * r) = 0 := by
    have h := SecondOrder.integral_cos_int_mul hω 1
    simpa using h
  have hs : ∫ r in (0 : ℝ)..(2 * Real.pi / ω), Real.sin (ω * r) = 0 := by
    have h := SecondOrder.integral_sin_int_mul hω 1
    simpa using h
  set C1 : Matrix (Fin 2) (Fin 2) ℝ := ((M 0 0 - M 1 1) / 2) • TwoToOne.refl1 +
    ((M 0 1 + M 1 0) / 2) • TwoToOne.refl2 with hC1
  set C2 : Matrix (Fin 2) (Fin 2) ℝ := ((M 0 1 + M 1 0) / 2) • TwoToOne.refl1 -
    ((M 0 0 - M 1 1) / 2) • TwoToOne.refl2 with hC2
  have e : ∀ r : ℝ, rot (-(ω * r / 2)) * M * rot (ω * r / 2) = projJ M +
      Real.cos (ω * r) • C1 + Real.sin (ω * r) • C2 := fun r => by
    rw [TwoToOne.rot_conj M (ω * r), projJ, hC1, hC2]
    module
  simp_rw [e]
  have hcos : Continuous fun r : ℝ => Real.cos (ω * r) • C1 :=
    (by fun_prop : Continuous fun r : ℝ => Real.cos (ω * r)).smul continuous_const
  have hsin : Continuous fun r : ℝ => Real.sin (ω * r) • C2 :=
    (by fun_prop : Continuous fun r : ℝ => Real.sin (ω * r)).smul continuous_const
  rw [intervalIntegral.integral_add (f := fun r => projJ M + Real.cos (ω * r) • C1)
      (g := fun r => Real.sin (ω * r) • C2) ((continuous_const.add hcos).intervalIntegrable _ _)
      (hsin.intervalIntegrable _ _),
    intervalIntegral.integral_add (f := fun _ => projJ M) (g := fun r => Real.cos (ω * r) • C1)
      (continuous_const.intervalIntegrable _ _)
      (hcos.intervalIntegrable _ _), intervalIntegral.integral_const,
    intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const, hc, hs, zero_smul,
    zero_smul, add_zero, add_zero, sub_zero]

end Integrals

/-! ## The critical block of the second Picard term -/

section Blocks

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The `(1,2)` block as a continuous linear map. -/
def blk12 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ →L[ℝ] Matrix (Fin 2) Y ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M.toBlocks₁₂
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The `(2,1)` block as a continuous linear map. -/
def blk21 : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ →L[ℝ] Matrix Y (Fin 2) ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M.toBlocks₂₁
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- **The critical block of the second Picard term.**
`(N₂(F))₁₁ = N₂(F₁₁) + ∫₀ᵀ F₁₂(r) ∫₀ʳ F₂₁(u) du dr`: the critical block of the second-order
monodromy term is the second Picard term of the critical block plus the excursion through the
stable block. -/
@[tmio T, powerlib_foundation] theorem secondTerm_toBlocks₁₁
    {F : ℝ → Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ} (hF : Continuous F) (T : ℝ) :
    (secondTerm F T).toBlocks₁₁ = secondTerm (fun t => (F t).toBlocks₁₁) T +
      ∫ r in (0 : ℝ)..T, (F r).toBlocks₁₂ * ∫ u in (0 : ℝ)..r, (F u).toBlocks₂₁ := by
  have hc : Continuous fun r => F r * ∫ u in (0 : ℝ)..r, F u :=
    hF.mul (intervalIntegral.continuous_primitive (fun a b => hF.intervalIntegrable a b) 0)
  have h11c : Continuous fun t => (F t).toBlocks₁₁ := BlockAveraging.blk11.continuous.comp hF
  have h12c : Continuous fun t => (F t).toBlocks₁₂ := blk12.continuous.comp hF
  have h21c : Continuous fun t => (F t).toBlocks₂₁ := blk21.continuous.comp hF
  have hp11 : Continuous fun r => ∫ u in (0 : ℝ)..r, (F u).toBlocks₁₁ :=
    intervalIntegral.continuous_primitive (fun a b => h11c.intervalIntegrable a b) 0
  have hp21 : Continuous fun r => ∫ u in (0 : ℝ)..r, (F u).toBlocks₂₁ :=
    intervalIntegral.continuous_primitive (fun a b => h21c.intervalIntegrable a b) 0
  have e : ∀ r, BlockAveraging.blk11 (F r * ∫ u in (0 : ℝ)..r, F u) =
      (F r).toBlocks₁₁ * (∫ u in (0 : ℝ)..r, (F u).toBlocks₁₁) +
        (F r).toBlocks₁₂ * ∫ u in (0 : ℝ)..r, (F u).toBlocks₂₁ := by
    intro r
    show (F r * ∫ u in (0 : ℝ)..r, F u).toBlocks₁₁ = _
    have h11 : (∫ u in (0 : ℝ)..r, F u).toBlocks₁₁ = ∫ u in (0 : ℝ)..r, (F u).toBlocks₁₁ :=
      (BlockAveraging.blk11.intervalIntegral_comp_comm (hF.intervalIntegrable 0 r)).symm
    have h21 : (∫ u in (0 : ℝ)..r, F u).toBlocks₂₁ = ∫ u in (0 : ℝ)..r, (F u).toBlocks₂₁ :=
      (blk21.intervalIntegral_comp_comm (hF.intervalIntegrable 0 r)).symm
    rw [← h11, ← h21]
    conv_lhs => rw [← fromBlocks_toBlocks (F r), ← fromBlocks_toBlocks (∫ u in (0 : ℝ)..r, F u)]
    rw [fromBlocks_multiply, toBlocks_fromBlocks₁₁]
  have h := BlockAveraging.blk11.intervalIntegral_comp_comm
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 T)
  show (∫ r in (0 : ℝ)..T, F r * ∫ u in (0 : ℝ)..r, F u).toBlocks₁₁ = _
  have h' : (∫ r in (0 : ℝ)..T, F r * ∫ u in (0 : ℝ)..r, F u).toBlocks₁₁ =
      BlockAveraging.blk11 (∫ r in (0 : ℝ)..T, F r * ∫ u in (0 : ℝ)..r, F u) := rfl
  rw [h']
  refine h.symm.trans ((intervalIntegral.integral_congr (fun r _ => e r)).trans ?_)
  rw [intervalIntegral.integral_add
    (f := fun r => (F r).toBlocks₁₁ * ∫ u in (0 : ℝ)..r, (F u).toBlocks₁₁)
    (g := fun r => (F r).toBlocks₁₂ * ∫ u in (0 : ℝ)..r, (F u).toBlocks₂₁)
    ((h11c.mul hp11).intervalIntegrable 0 T) ((h12c.matrix_mul hp21).intervalIntegrable 0 T)]
  rfl

end Blocks

/-! ## The three-state core: a pumped pair coupled to one stable real mode -/

section Core

/-- The modulation of the core: the pump `A₁₁` on the critical pair and a modulation `c` of the
stable mode; no modulated coupling between them. -/
def coreA (A₁₁ : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℂ :=
  fromBlocks A₁₁ 0 0 !![c]

/-- The constant `O(ε)` part of the core: the pair is fed by the stable mode through the column
`β` and feeds it through the row `γ`; `b` shifts the stable mode. -/
def coreB (β : Matrix (Fin 2) (Fin 1) ℝ) (γ : Matrix (Fin 1) (Fin 2) ℝ) (b : ℝ) :
    Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ :=
  fromBlocks 0 β γ !![b]

@[tmio T, powerlib_foundation] theorem expS_fin_one (a t : ℝ) :
    expS (!![a] : Matrix (Fin 1) (Fin 1) ℝ) t = !![Real.exp (t * a)] := by
  have hd : (t • !![a] : Matrix (Fin 1) (Fin 1) ℝ) = diagonal fun _ => t * a := by
    ext i j; fin_cases i; fin_cases j; simp
  have he : (NormedSpace.exp fun _ : Fin 1 => t * a) = fun _ => Real.exp (t * a) := by
    funext i; rw [Pi.exp_def, Real.exp_eq_exp_ℝ]
  rw [expS, hd, Matrix.exp_diagonal, he]
  ext i j; fin_cases i; fin_cases j; simp

@[tmio T, powerlib_foundation] theorem modN_coreA (A₁₁ : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ)
    (ω t : ℝ) :
    modN (coreA A₁₁ c) ω t = fromBlocks (TwoToOne.modReal A₁₁ ω t) 0 0
      !![c.re * Real.cos (ω * t) - c.im * Real.sin (ω * t)] := by
  ext (i | i) (j | j) <;> simp [modN, coreA, TwoToOne.modReal]

@[tmio T, powerlib_foundation] private theorem FzB_core_blocks (s d ω a : ℝ)
    (A₁₁ : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) (β : Matrix (Fin 2) (Fin 1) ℝ)
    (γ : Matrix (Fin 1) (Fin 2) ℝ) (b t : ℝ) :
    (FzB s d ω !![a] (coreA A₁₁ c) (coreB β γ b) t).toBlocks₁₁ = stdForm s d ω A₁₁ t ∧
      (FzB s d ω !![a] (coreA A₁₁ c) (coreB β γ b) t).toBlocks₁₂ =
        Real.exp (t * a) • (rot (-(ω * t / 2)) * β) ∧
      (FzB s d ω !![a] (coreA A₁₁ c) (coreB β γ b) t).toBlocks₂₁ =
        Real.exp (-t * a) • (γ * rot (ω * t / 2)) := by
  have h1 : ∀ x : ℝ, rot (-(ω * t / 2)) * β * !![x] = x • (rot (-(ω * t / 2)) * β) := fun x => by
    ext i j; fin_cases j; simp [Matrix.mul_apply, mul_comm]
  have h2 : ∀ x : ℝ, !![x] * γ * rot (ω * t / 2) = x • (γ * rot (ω * t / 2)) := fun x => by
    rw [Matrix.mul_assoc]
    ext i j; fin_cases i; simp [Matrix.mul_apply]
  rw [FzB, Fz, PsiInv, Psi, modN_coreA, coreB, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_multiply, fromBlocks_multiply, fromBlocks_add, fromBlocks_add, expS_fin_one,
    expS_fin_one, stdForm]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add]
  exact ⟨trivial, h1 _, h2 _⟩

/-- The critical block of the standard form of the core is the two-state standard form. -/
@[tmio T, powerlib_foundation] theorem FzB_core₁₁ (s d ω a : ℝ) (A₁₁ : Matrix (Fin 2) (Fin 2) ℂ)
    (c : ℂ) (β : Matrix (Fin 2) (Fin 1) ℝ) (γ : Matrix (Fin 1) (Fin 2) ℝ) (b t : ℝ) :
    (FzB s d ω !![a] (coreA A₁₁ c) (coreB β γ b) t).toBlocks₁₁ = stdForm s d ω A₁₁ t :=
  (FzB_core_blocks s d ω a A₁₁ c β γ b t).1

/-- The coupling block from the stable mode: `F₁₂(t) = e^{ta} R(−ωt/2) β`. -/
@[tmio T, powerlib_foundation] theorem FzB_core₁₂ (s d ω a : ℝ) (A₁₁ : Matrix (Fin 2) (Fin 2) ℂ)
    (c : ℂ) (β : Matrix (Fin 2) (Fin 1) ℝ) (γ : Matrix (Fin 1) (Fin 2) ℝ) (b t : ℝ) :
    (FzB s d ω !![a] (coreA A₁₁ c) (coreB β γ b) t).toBlocks₁₂ =
      Real.exp (t * a) • (rot (-(ω * t / 2)) * β) :=
  (FzB_core_blocks s d ω a A₁₁ c β γ b t).2.1

/-- The coupling block into the stable mode: `F₂₁(t) = e^{−ta} γ R(ωt/2)`. -/
@[tmio T, powerlib_foundation] theorem FzB_core₂₁ (s d ω a : ℝ) (A₁₁ : Matrix (Fin 2) (Fin 2) ℂ)
    (c : ℂ) (β : Matrix (Fin 2) (Fin 1) ℝ) (γ : Matrix (Fin 1) (Fin 2) ℝ) (b t : ℝ) :
    (FzB s d ω !![a] (coreA A₁₁ c) (coreB β γ b) t).toBlocks₂₁ =
      Real.exp (-t * a) • (γ * rot (ω * t / 2)) :=
  (FzB_core_blocks s d ω a A₁₁ c β γ b t).2.2

/-- Right multiplication by a fixed matrix as a continuous linear map. -/
def mulRightL {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] (B : Matrix n p ℝ) :
    Matrix m n ℝ →L[ℝ] Matrix m p ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => X * B
      map_add' := fun X Y => Matrix.add_mul X Y B
      map_smul' := fun c X => Matrix.smul_mul c X B }

/-- Left multiplication by a fixed matrix as a continuous linear map. -/
def mulLeftL {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] (B : Matrix m n ℝ) :
    Matrix n p ℝ →L[ℝ] Matrix m p ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => B * X
      map_add' := fun X Y => Matrix.mul_add B X Y
      map_smul' := fun c X => Matrix.mul_smul B c X }

@[tmio T, powerlib_foundation] private theorem integral_mul_right' {m n p : Type*} [Fintype m]
    [Fintype n] [Fintype p] {f : ℝ → Matrix m n ℝ} (hf : Continuous f) (B : Matrix n p ℝ)
    (a b : ℝ) : ∫ t in a..b, f t * B = (∫ t in a..b, f t) * B :=
  (mulRightL B).intervalIntegral_comp_comm (hf.intervalIntegrable a b)

@[tmio T, powerlib_foundation] private theorem integral_mul_left' {m n p : Type*} [Fintype m]
    [Fintype n] [Fintype p] {f : ℝ → Matrix n p ℝ} (hf : Continuous f) (B : Matrix m n ℝ)
    (a b : ℝ) : ∫ t in a..b, B * f t = B * ∫ t in a..b, f t :=
  (mulLeftL B).intervalIntegral_comp_comm (hf.intervalIntegrable a b)

set_option maxHeartbeats 4000000 in
/-- **The effective second-order matrix of the three-state core in closed form.** For the core
`fullB s d ω [a] (coreA A₁₁ c) (coreB β γ b)` (critical pair with pump `A₁₁`, one stable real mode
`a`, constant coupling `β`, `γ`), `T = 2π/ω`, `E = e^{Ta}`:
`N_eff = N₂(stdForm s d ω A₁₁) − T P(βγ) (aI − (ω/2)J)⁻¹`.
The excursion through the stable mode in the second Picard term,
`∫₀ᵀ F₁₂ ∫₀ʳ F₂₁ = −(1 + E) L βγ L − T P(βγ) L` (`L = (aI − (ω/2)J)⁻¹`), and the Schur-complement
correction `−T² F̄₁₂ (I + E)⁻¹ E F̄₂₁ = (1 + E) L βγ L` cancel in their `E`-dependent parts: the
stable mode enters only through the rotating resolvent `L`, not through `e^{Ta}`. -/
@[tmio T, powerlib_foundation] theorem effSecond_core (s d : ℝ) {ω : ℝ} (hω : 0 < ω) (a : ℝ)
    (A₁₁ : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) (β : Matrix (Fin 2) (Fin 1) ℝ)
    (γ : Matrix (Fin 1) (Fin 2) ℝ) (b : ℝ) :
    effSecond (FzcB s d ω (2 * Real.pi / ω) !![a] (coreA A₁₁ c) (coreB β γ b)) (2 * Real.pi / ω)
        (expS !![a] (2 * Real.pi / ω)) =
      secondTerm (stdForm s d ω A₁₁) (2 * Real.pi / ω) -
        (2 * Real.pi / ω) • (projJ (β * γ) * lamInv a (ω / 2)) := by
  set T := 2 * Real.pi / ω with hTdef
  have hT : 0 < T := by positivity
  have hne : a ^ 2 + (ω / 2) ^ 2 ≠ 0 := by positivity
  set L := lamInv a (ω / 2) with hL
  set e := Real.exp (T * a) with he
  have he0 : 0 < e := Real.exp_pos _
  set G := FzB s d ω !![a] (coreA A₁₁ c) (coreB β γ b) with hG
  set F := FzcB s d ω T !![a] (coreA A₁₁ c) (coreB β γ b) with hF
  have hGc : Continuous G := BlockAveraging.continuous_FzB s d ω _ _ _
  have hFG : ∀ t ∈ Icc (0 : ℝ) T, F t = G t := fun t ht => by
    rw [hF, FzcB, BlockAveraging.clampT_of_mem ht]
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
  have hmeanFG : ∫ t in (0 : ℝ)..T, F t = ∫ t in (0 : ℝ)..T, G t :=
    hint T ⟨hT.le, le_rfl⟩
  -- the blocks of `G`
  have hG11 : ∀ t, (G t).toBlocks₁₁ = stdForm s d ω A₁₁ t := fun t => by
    rw [hG, FzB_core₁₁]
  have hG12 : ∀ t, (G t).toBlocks₁₂ = Real.exp (t * a) • rot (-(ω * t / 2)) * β := fun t => by
    rw [hG, FzB_core₁₂, Matrix.smul_mul]
  have hG21 : ∀ t, (G t).toBlocks₂₁ = γ * (Real.exp (-(t * a)) • rot (ω * t / 2)) := fun t => by
    rw [hG, FzB_core₂₁, Matrix.mul_smul, neg_mul]
  have hc1 : Continuous fun t : ℝ => Real.exp (t * a) • rot (-(ω * t / 2)) := by
    unfold rot; fun_prop
  have hc2 : Continuous fun t : ℝ => Real.exp (-(t * a)) • rot (ω * t / 2) := by
    unfold rot; fun_prop
  have hrotpi : rot (ω * T / 2) = -1 := by
    have h : ω * T / 2 = Real.pi := by rw [hTdef]; field_simp
    rw [h]; simp [rot]
  -- the integrals of the coupling blocks
  have hI12 : (∫ t in (0 : ℝ)..T, G t).toBlocks₁₂ = (-(1 + e) • L) * β := by
    have h := (blk12 (Y := Fin 1)).intervalIntegral_comp_comm (hGc.intervalIntegrable (μ := MeasureTheory.volume) 0 T)
    refine h.symm.trans ((intervalIntegral.integral_congr (g := fun t =>
      Real.exp (t * a) • rot (-(ω * t / 2)) * β) (fun t _ => ?_)).trans ?_)
    · show (G t).toBlocks₁₂ = _
      exact hG12 t
    rw [integral_mul_right' hc1, hTdef, integral_exp_rot_neg hω]
  have hI21 : (∫ t in (0 : ℝ)..T, G t).toBlocks₂₁ = γ * ((1 + e⁻¹) • L) := by
    have h := (blk21 (Y := Fin 1)).intervalIntegral_comp_comm (hGc.intervalIntegrable (μ := MeasureTheory.volume) 0 T)
    refine h.symm.trans ((intervalIntegral.integral_congr (g := fun t =>
      γ * (Real.exp (-(t * a)) • rot (ω * t / 2))) (fun t _ => ?_)).trans ?_)
    · show (G t).toBlocks₂₁ = _
      exact hG21 t
    rw [integral_mul_left' hc2, integral_exp_neg_rot ω a T hne, hrotpi]
    congr 1
    rw [smul_neg, sub_neg_eq_add, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.one_mul,
      add_smul, one_smul, Real.exp_neg, ← he]
  -- the excursion through the stable mode
  have hprim : ∀ r, ∫ u in (0 : ℝ)..r, (G u).toBlocks₂₁ =
      γ * ((1 - Real.exp (-(r * a)) • rot (ω * r / 2)) * L) := fun r => by
    rw [intervalIntegral.integral_congr (g := fun u =>
      γ * (Real.exp (-(u * a)) • rot (ω * u / 2))) (fun u _ => hG21 u),
      integral_mul_left' hc2, integral_exp_neg_rot ω a r hne]
  have hexc : ∀ r, (G r).toBlocks₁₂ * ∫ u in (0 : ℝ)..r, (G u).toBlocks₂₁ =
      Real.exp (r * a) • rot (-(ω * r / 2)) * (β * γ * L) -
        rot (-(ω * r / 2)) * (β * γ) * rot (ω * r / 2) * L := fun r => by
    rw [hG12, hprim]
    have hee : Real.exp (-(r * a)) * Real.exp (r * a) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hee, one_smul, Matrix.mul_assoc]
  have hcE : Continuous fun r : ℝ => Real.exp (r * a) • rot (-(ω * r / 2)) * (β * γ * L) :=
    hc1.mul continuous_const
  have hcR : Continuous fun r : ℝ => rot (-(ω * r / 2)) * (β * γ) * rot (ω * r / 2) * L := by
    unfold rot; fun_prop
  have hIexc : ∫ r in (0 : ℝ)..T, (G r).toBlocks₁₂ * ∫ u in (0 : ℝ)..r, (G u).toBlocks₂₁ =
      (-(1 + e) • L) * (β * γ * L) - (T • projJ (β * γ)) * L := by
    simp_rw [hexc]
    rw [intervalIntegral.integral_sub (hcE.intervalIntegrable 0 T) (hcR.intervalIntegrable 0 T),
      integral_mul_right' hc1, hTdef, integral_exp_rot_neg hω,
      integral_mul_right' (by unfold rot; fun_prop) L, integral_rot_conj hω]
  have hsec11 := secondTerm_toBlocks₁₁ hGc T
  simp_rw [hG11] at hsec11
  -- the stable block
  have hE : expS (!![a] : Matrix (Fin 1) (Fin 1) ℝ) T = !![e] := by rw [expS_fin_one, he, mul_comm]
  have hinv : (1 + (!![e] : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ = !![(1 + e)⁻¹] := by
    have h1 : (1 + (!![e] : Matrix (Fin 1) (Fin 1) ℝ)) = !![1 + e] := by
      ext i j; fin_cases i; fin_cases j; simp
    rw [h1]
    refine Matrix.inv_eq_left_inv ?_
    ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]; field_simp
  have hcol : ∀ (X : Matrix (Fin 2) (Fin 1) ℝ) (c : ℝ), X * !![c] = c • X := fun X c => by
    ext i j; fin_cases j; simp [Matrix.mul_apply, mul_comm]
  have hrow : ∀ (X : Matrix (Fin 1) (Fin 2) ℝ) (c : ℝ), !![c] * X = c • X := fun X c => by
    ext i j; fin_cases i; simp [Matrix.mul_apply]
  rw [effSecond, hsecFG, hmeanFG, hE, hinv]
  have hs12 : (T • (T⁻¹ • ∫ t in (0 : ℝ)..T, G t).toBlocks₁₂) =
      (∫ t in (0 : ℝ)..T, G t).toBlocks₁₂ := by
    show T • (T⁻¹ • (∫ t in (0 : ℝ)..T, G t).toBlocks₁₂) = _
    rw [smul_smul, mul_inv_cancel₀ hT.ne', one_smul]
  have hs21 : (T • (!![e] * (T⁻¹ • ∫ t in (0 : ℝ)..T, G t).toBlocks₂₁)) =
      !![e] * (∫ t in (0 : ℝ)..T, G t).toBlocks₂₁ := by
    show T • (!![e] * (T⁻¹ • (∫ t in (0 : ℝ)..T, G t).toBlocks₂₁)) = _
    rw [Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hT.ne', one_smul]
  rw [hs12, hs21, hsec11, hIexc, hI12, hI21]
  have hschur : (-((-(1 + e) • L) * β)) * !![(1 + e)⁻¹] * (!![e] * (γ * ((1 + e⁻¹) • L))) =
      (1 + e) • (L * (β * γ * L)) := by
    rw [hrow, hcol]
    simp only [Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul, neg_neg, neg_smul, smul_smul,
      Matrix.mul_assoc]
    congr 1
    have h1e : (1 + e) ≠ 0 := by positivity
    field_simp
    ring
  rw [hschur]
  simp only [Matrix.smul_mul, Matrix.neg_mul, neg_smul]
  abel

/-- **The decisive quantity of the three-state core** on its first-order boundary:
`d|g'|²/(4ω) + 2(s(pa − qν) + d(pν + qa))/(a² + ν²)`, `ν = ω/2`, with the anti-resonant pump
`g' = SecondOrder.antiPump A₁₁` and the rotation-invariant part `p I + q J` of the coupling
`βγ`: `p = (β₀γ₀ + β₁γ₁)/2`, `q = (β₁γ₀ − β₀γ₁)/2`. -/
def coreMixed (s d ω a : ℝ) (A₁₁ : Matrix (Fin 2) (Fin 2) ℂ) (β : Matrix (Fin 2) (Fin 1) ℝ)
    (γ : Matrix (Fin 1) (Fin 2) ℝ) : ℝ :=
  d * ‖SecondOrder.antiPump A₁₁‖ ^ 2 / (4 * ω) +
    2 * (s * ((β 0 0 * γ 0 0 + β 1 0 * γ 0 1) / 2 * a - (β 1 0 * γ 0 0 - β 0 0 * γ 0 1) / 2 *
        (ω / 2)) +
      d * ((β 0 0 * γ 0 0 + β 1 0 * γ 0 1) / 2 * (ω / 2) +
        (β 1 0 * γ 0 0 - β 0 0 * γ 0 1) / 2 * a)) / (a ^ 2 + (ω / 2) ^ 2)

/-- `mixedDet(M, N_eff) = −sT²(s² + d² − |g/2|²) + T · coreMixed` for the three-state core. -/
@[tmio T, powerlib_foundation] theorem mixedDet_effSecond_core (s d : ℝ) {ω : ℝ} (hω : 0 < ω)
    (a : ℝ) (A₁₁ : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) (β : Matrix (Fin 2) (Fin 1) ℝ)
    (γ : Matrix (Fin 1) (Fin 2) ℝ) (b : ℝ) :
    mixedDet (slowFlowMatrix s d (Element.pump A₁₁ left right / 2))
        (effSecond (FzcB s d ω (2 * Real.pi / ω) !![a] (coreA A₁₁ c) (coreB β γ b)) (2 * Real.pi / ω)
          (expS !![a] (2 * Real.pi / ω))) =
      -(s * (2 * Real.pi / ω) ^ 2 * (s ^ 2 + d ^ 2 - ‖Element.pump A₁₁ left right / 2‖ ^ 2)) +
        2 * Real.pi / ω * coreMixed s d ω a A₁₁ β γ := by
  have hne : a ^ 2 + (ω / 2) ^ 2 ≠ 0 := by positivity
  rw [effSecond_core s d hω a A₁₁ c β γ b]
  set M := slowFlowMatrix s d (Element.pump A₁₁ left right / 2) with hM
  have hsub : ∀ X Z : Matrix (Fin 2) (Fin 2) ℝ, mixedDet M (X - Z) = mixedDet M X - mixedDet M Z :=
    fun X Z => by simp only [mixedDet, Matrix.trace_sub, Matrix.mul_sub]; ring
  have hsm : ∀ (c : ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ), mixedDet M (c • X) = c * mixedDet M X :=
    fun c X => by simp only [mixedDet, Matrix.trace_smul, Matrix.mul_smul, smul_eq_mul]; ring
  have hcoup : mixedDet M (projJ (β * γ) * lamInv a (ω / 2)) =
      -(2 * (s * ((β 0 0 * γ 0 0 + β 1 0 * γ 0 1) / 2 * a - (β 1 0 * γ 0 0 - β 0 0 * γ 0 1) / 2 *
        (ω / 2)) + d * ((β 0 0 * γ 0 0 + β 1 0 * γ 0 1) / 2 * (ω / 2) +
          (β 1 0 * γ 0 0 - β 0 0 * γ 0 1) / 2 * a)) / (a ^ 2 + (ω / 2) ^ 2)) := by
    set p := (β 0 0 * γ 0 0 + β 1 0 * γ 0 1) / 2 with hp
    set q := (β 1 0 * γ 0 0 - β 0 0 * γ 0 1) / 2 with hq
    have hprod : projJ (β * γ) * lamInv a (ω / 2) = (a ^ 2 + (ω / 2) ^ 2)⁻¹ •
        ((p * a - q * (ω / 2)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          (p * (ω / 2) + q * a) • quarter) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [projJ, lamInv, quarter, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, hp, hq] <;>
        ring
    have hadd : ∀ X Z : Matrix (Fin 2) (Fin 2) ℝ, mixedDet M (X + Z) = mixedDet M X + mixedDet M Z :=
      fun X Z => by simp only [mixedDet, Matrix.trace_add, Matrix.mul_add]; ring
    have h1 : mixedDet M 1 = -2 * s := by
      rw [Boundary.mixedDet_one_right, hM, trace_slowFlowMatrix]
    have hJ : mixedDet M quarter = -(2 * d) := by
      rw [hM]; simp [mixedDet, slowFlowMatrix, quarter, Matrix.trace_fin_two]; ring
    rw [hprod, hsm, hadd, hsm, hsm, h1, hJ]
    field_simp
    ring
  rw [hsub, hsm, hcoup, SecondOrder.mixedDet_secondTerm_stdForm s d hω A₁₁, coreMixed]
  ring

/-- **The three-state core on its first-order boundary, decided in closed form.** For the core
`BlockAveraging.fullB s d ω [a] (coreA A₁₁ c) (coreB β γ b) ε` — the critical pair
`−εs ± j(ω/2 − εd)` pumped by `ε Re{A₁₁ e^{jωt}}`, one stable real mode `a < 0`, and the constant
coupling `ε(β, γ)` between them — on the first-order boundary `s² + d² = |g/2|²`, `s > 0`
(`g = u A₁₁ r̄`): for all small `ε > 0`, `coreMixed > 0` puts every Floquet multiplier inside the
unit circle and `coreMixed < 0` gives Floquet instability, where
`coreMixed = d|g'|²/(4ω) + 2(s(pa − qω/2) + d(pω/2 + qa))/(a² + ω²/4)`
`= d|g'|²/(4ω) + 2 Re{(s − jd)(p + jq)/(a − jω/2)}`. The stable mode shifts the second-order
verdict through the rotating resolvent `(a − jω/2)⁻¹`; its one-period gain `e^{Ta}`, its own
modulation `c` and shift `b` drop out. -/
@[tmio T, powerlib_foundation] theorem three_state_boundary {s d ω a : ℝ} (hω : 0 < ω)
    (ha : a < 0) (A₁₁ : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) (β : Matrix (Fin 2) (Fin 1) ℝ)
    (γ : Matrix (Fin 1) (Fin 2) ℝ) (b : ℝ) (hs : 0 < s)
    (hb : s ^ 2 + d ^ 2 = ‖Element.pump A₁₁ left right / 2‖ ^ 2) :
    (0 < coreMixed s d ω a A₁₁ β γ →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (μ : ℂ) (v : Fin 2 ⊕ Fin 1 → ℂ), v ≠ 0 →
        (Periodic.monodromy (fullB s d ω !![a] (coreA A₁₁ c) (coreB β γ b) ε) (2 * Real.pi / ω)
          0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1) ∧
      (coreMixed s d ω a A₁₁ β γ < 0 →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), Periodic.FloquetUnstable
          (fullB s d ω !![a] (coreA A₁₁ c) (coreB β γ b) ε) (2 * Real.pi / ω)) := by
  have hT : 0 < 2 * Real.pi / ω := by positivity
  have hsr : spectralRadius ℂ ((expS (!![a] : Matrix (Fin 1) (Fin 1) ℝ) (2 * Real.pi / ω)).map
      (algebraMap ℝ ℂ)) < 1 := by
    have hq : ‖expS (!![a] : Matrix (Fin 1) (Fin 1) ℝ) (2 * Real.pi / ω)‖ < 1 := by
      rw [BlockAveraging.norm_expS_one, Real.exp_lt_one_iff]
      exact mul_neg_of_pos_of_neg hT ha
    exact BlockAveraging.spectralRadius_lt_one_of_norm _ hq
  have hA : (coreA A₁₁ c).toBlocks₁₁ = A₁₁ := toBlocks_fromBlocks₁₁ _ _ _ _
  have hre : BlockAveraging.shiftRe (coreB β γ b) = 0 := by
    simp [BlockAveraging.shiftRe, coreB]
  have him : BlockAveraging.shiftIm (coreB β γ b) = 0 := by
    simp [BlockAveraging.shiftIm, coreB]
  have h := BlockBoundary.averagingB_boundary (s := s) (d := d) hω !![a] (coreA A₁₁ c) (coreB β γ b)
    (by rw [hre, sub_zero]; exact hs) (by rw [hre, him, sub_zero, sub_zero, hA]; exact hb) hsr
  rw [hre, him, sub_zero, sub_zero, hA, mixedDet_effSecond_core s d hω a A₁₁ c β γ b, ← hb, sub_self,
    mul_zero, neg_zero, zero_add] at h
  refine ⟨fun hpos => h.1 (mul_pos hT hpos), fun hneg => h.2 (mul_neg_of_pos_of_neg hT hneg)⟩

end Core

end powerlib.ParametricResonance.ThreeStateCore
