import theorem.ParametricResonance.ForcedOrbit
import theorem.ParametricResonance.BlockAveragingRemainder

/-! # Floquet multipliers of the variational equation along the forced orbit

Composition of `ForcedOrbit` with `BlockAveragingRemainder`. For a forced system whose Jacobian
satisfies `J_ε(t, y) = A + D_x y + ε D_u(t) + O(‖y‖² + ε²)`, the variational matrix along the forced
orbit is `A + ε(D_x y_p + D_u) + ε² R_ε(t)` with `R_ε` continuous and uniformly bounded; with the
first-order orbit `y_p = Re{z e^{jωt}}` and `D_u = A₀' + Re{G e^{jωt}}` this is
`A + ε(A₀' + Re{A₁ e^{jωt}}) + ε² R_ε`, `A₁ = D_x z + G`. Hence the Floquet multipliers of the
variational equation of the actual forced orbit obey the first-order criterion `|g/2| ≶ |λ₁|`,
`λ₁ = u A₀' r`, `g = u A₁ r̄`.

Scope.
* The forced system `ẏ = A y + ε b(t) + N_ε(t, y)` with the hypotheses of
  `ForcedOrbit.forced_orbit`, and a matrix field `J_ε(t, y)` (the Jacobian of the vector field for a
  concrete model), continuous on `ℝ × {‖y‖ ≤ ρ}`, with its first-order Taylor bound, on any
  finite state space; the variational
  matrix along a solution is `t ↦ J_ε(t, y(t))`. The solution conditions are written out in the
  statements.
* The Floquet statements need real modal coordinates of `A` with the pair `±jω/2` and a stable
  block with one-period spectral radius `ρ(e^{TA_s}) < 1` (general `X`), or the eigen-data of a
  three-state core.
* The statements here concern the Floquet multipliers; the exponential stability of the nonlinear
  solutions near the orbit that follows from them is `Periodic.OrbitalStability` and
  `SmoothOrbitStability`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1–§2.2 (`J_p = A₀ + ε Re{A₁ e^{jω_p t}}` along the forced
trajectory, `g_m = l_mᴴ A₁ r_m*`, first-order averaging), [8, 9] of that report.

Results.
* `jacRem`, `jacRem_eq`, `jacRem_bound`, `continuous_jacRem` — the remainder of the variational
  matrix along an orbit and its bound `K_J(c² + 1) + K_D C`.
* `harm`, `continuous_harm`, `harm_periodic`, `harm_hasDerivAt` (`Re{z e^{jωt}}` solves
  `ẏ = A y + Re{β e^{jωt}}` when `(jωI − A) z = β`), `DxC`, `Dx_harm`, `modX_add`.
* `eq_expS_of_hasDerivAt`, `expS_block`, `conjHom`, `exists_minv_of_modal` — the modal coordinates
  give `(I − e^{TA})⁻¹`.
* `orbit_variational` — for small `ε` the variational matrix along the (unique small)
  forced orbit is `physJR A A₀' A₁ R ω ε`.
* `orbit_floquet_stable`, `orbit_floquet_unstable` — end-to-end criterion for the
  forced orbit; `orbit_floquet_three_stable`, `orbit_floquet_three_unstable` — for three-state
  cores from their eigen-data.

Corrections.
None: with the forced orbit and the `O(ε²)` terms included, the first-order 2:1 criterion of §2.2
holds for the variational equation of the actual forced orbit.

Family and connection conclusions.
None: static evidence on periodically forced ODEs (Floquet multipliers along the forced orbit).
-/

noncomputable section
namespace powerlib.ParametricResonance.ForcedOrbit
open Complex Matrix Set Filter Topology
open scoped Matrix.Norms.Operator
open TwoToOne (base)
open NormalForm (rot quarter)
open BlockAveraging (expS modX physJ physJR physLeft physRight physical_stable_R
  physical_unstable_R eventually_lt_nhdsGT modalP modalQ modal_three norm_expS_one hasDerivAt_expS
  expS_comm expS_mul_neg)

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### The variational matrix along the orbit -/

/-- The remainder of the variational matrix along an orbit `y`:
`R_ε(t) = ε⁻² (J_ε(t, y(t)) − A − ε(D_x y_p(t) + D_u(t)))`. -/
def jacRem (Jf : ℝ → ℝ → (X → ℝ) → Matrix X X ℝ) (A : Matrix X X ℝ)
    (Dx : (X → ℝ) →ₗ[ℝ] Matrix X X ℝ) (Du : ℝ → Matrix X X ℝ) (y yp : ℝ → X → ℝ) (ε t : ℝ) :
    Matrix X X ℝ :=
  (ε ^ 2)⁻¹ • (Jf ε t (y t) - A - ε • (Dx (yp t) + Du t))

omit [Fintype X] [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem jacRem_eq (Jf : ℝ → ℝ → (X → ℝ) → Matrix X X ℝ)
    (A : Matrix X X ℝ) (Dx : (X → ℝ) →ₗ[ℝ] Matrix X X ℝ) (Du : ℝ → Matrix X X ℝ)
    (y yp : ℝ → X → ℝ) {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    Jf ε t (y t) = A + ε • (Dx (yp t) + Du t) + ε ^ 2 • jacRem Jf A Dx Du y yp ε t := by
  rw [jacRem, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hε), one_smul]
  abel

/-- `‖R_ε(t)‖ ≤ K_J(c² + 1) + K_D C` from the Taylor bound of the Jacobian and the expansion
`‖y − ε y_p‖ ≤ C ε²` of the orbit. -/
@[tmio T, powerlib_foundation] theorem jacRem_bound {Jf : ℝ → ℝ → (X → ℝ) → Matrix X X ℝ}
    {A : Matrix X X ℝ} {Dx : (X → ℝ) →ₗ[ℝ] Matrix X X ℝ} {Du : ℝ → Matrix X X ℝ}
    {KJ KD ρ ε c C : ℝ} (hε : 0 < ε) (hKJ : 0 ≤ KJ)
    (hKD : 0 ≤ KD) (hDx : ∀ v, ‖Dx v‖ ≤ KD * ‖v‖)
    (hJ : ∀ t y, ‖y‖ ≤ ρ → ‖Jf ε t y - A - Dx y - ε • Du t‖ ≤ KJ * (‖y‖ ^ 2 + ε ^ 2))
    {y yp : ℝ → X → ℝ} (hyb : ∀ t, ‖y t‖ ≤ c * ε) (hcρ : c * ε ≤ ρ)
    (hexp : ∀ t, ‖y t - ε • yp t‖ ≤ C * ε ^ 2) (t : ℝ) :
    ‖jacRem Jf A Dx Du y yp ε t‖ ≤ KJ * (c ^ 2 + 1) + KD * C := by
  have e : Jf ε t (y t) - A - ε • (Dx (yp t) + Du t) =
      (Jf ε t (y t) - A - Dx (y t) - ε • Du t) + Dx (y t - ε • yp t) := by
    rw [map_sub, map_smul, smul_add]; abel
  have hy2 : ‖y t‖ ^ 2 ≤ (c * ε) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hyb t) 2
  have h1 := hJ t (y t) ((hyb t).trans hcρ)
  have h2 : ‖Dx (y t - ε • yp t)‖ ≤ KD * (C * ε ^ 2) :=
    (hDx _).trans (mul_le_mul_of_nonneg_left (hexp t) hKD)
  have hε2 : 0 < ε ^ 2 := by positivity
  rw [jacRem, norm_smul, e, Real.norm_of_nonneg (inv_nonneg.2 hε2.le)]
  rw [inv_mul_le_iff₀ hε2]
  calc ‖Jf ε t (y t) - A - Dx (y t) - ε • Du t + Dx (y t - ε • yp t)‖
      ≤ KJ * (‖y t‖ ^ 2 + ε ^ 2) + KD * (C * ε ^ 2) := (norm_add_le _ _).trans (add_le_add h1 h2)
    _ ≤ KJ * ((c * ε) ^ 2 + ε ^ 2) + KD * (C * ε ^ 2) := by gcongr
    _ = ε ^ 2 * (KJ * (c ^ 2 + 1) + KD * C) := by ring

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem continuous_jacRem {Jf : ℝ → ℝ → (X → ℝ) → Matrix X X ℝ}
    (A : Matrix X X ℝ) (Dx : (X → ℝ) →ₗ[ℝ] Matrix X X ℝ) {Du : ℝ → Matrix X X ℝ}
    {y yp : ℝ → X → ℝ} (ε : ℝ) {ρ : ℝ}
    (hJc : ContinuousOn (fun p : ℝ × (X → ℝ) => Jf ε p.1 p.2) (Set.univ ×ˢ Metric.closedBall 0 ρ))
    (hy : Continuous y) (hyb : ∀ t, ‖y t‖ ≤ ρ) (hyp : Continuous yp) (hDu : Continuous Du) :
    Continuous (jacRem Jf A Dx Du y yp ε) := by
  have h1 : Continuous fun t => Jf ε t (y t) := hJc.comp_continuous (continuous_id.prodMk hy)
    (fun s => Set.mk_mem_prod (Set.mem_univ _) (mem_closedBall_zero_iff.2 (hyb s)))
  have h2 : Continuous fun t => Dx (yp t) := (LinearMap.continuous_of_finiteDimensional Dx).comp hyp
  show Continuous fun t => (ε ^ 2)⁻¹ • (Jf ε t (y t) - A - ε • (Dx (yp t) + Du t))
  exact ((h1.sub continuous_const).sub ((h2.add hDu).const_smul ε)).const_smul ((ε ^ 2)⁻¹ : ℝ)

/-! ### The harmonic first-order orbit -/

/-- `Re{z e^{jωt}}` as a real vector. -/
def harm (z : X → ℂ) (ω t : ℝ) : X → ℝ :=
  fun i => (z i).re * Real.cos (ω * t) - (z i).im * Real.sin (ω * t)

omit [Fintype X] [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem continuous_harm (z : X → ℂ) (ω : ℝ) :
    Continuous (harm z ω) := by
  unfold harm; fun_prop

omit [Fintype X] [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem harm_periodic (z : X → ℂ) {ω : ℝ} (hω : ω ≠ 0) (t : ℝ) :
    harm z ω (t + 2 * Real.pi / ω) = harm z ω t := by
  have e : ω * (t + 2 * Real.pi / ω) = ω * t + 2 * Real.pi := by field_simp
  funext i
  simp only [harm, e, Real.cos_add_two_pi, Real.sin_add_two_pi]

omit [DecidableEq X] in
/-- `y_p = Re{z e^{jωt}}` solves `ẏ = A y + Re{β e^{jωt}}` when `(jωI − A) z = β`. -/
@[tmio T, powerlib_foundation] theorem harm_hasDerivAt {A : Matrix X X ℝ} {z β : X → ℂ} {ω : ℝ}
    (hz : ((ω : ℂ) * I) • z - A.map (algebraMap ℝ ℂ) *ᵥ z = β) (t : ℝ) :
    HasDerivAt (harm z ω) (A *ᵥ harm z ω t + harm β ω t) t := by
  rw [hasDerivAt_pi]
  intro i
  have hl : HasDerivAt (fun t : ℝ => ω * t) ω t := by simpa using (hasDerivAt_id t).const_mul ω
  have hcos := (Real.hasDerivAt_cos (ω * t)).comp t hl
  have hsin := (Real.hasDerivAt_sin (ω * t)).comp t hl
  have h := (hcos.const_mul (z i).re).sub (hsin.const_mul (z i).im)
  refine h.congr_deriv ?_
  have hi := congrFun hz i
  have hre := congrArg Complex.re hi
  have him := congrArg Complex.im hi
  simp [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.im_sum] at hre him
  have hs : ∀ j, A i j * ((z j).re * Real.cos (ω * t) - (z j).im * Real.sin (ω * t)) =
      A i j * (z j).re * Real.cos (ω * t) - A i j * (z j).im * Real.sin (ω * t) := fun j => by ring
  simp only [Pi.add_apply, harm, Matrix.mulVec, dotProduct, hs, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  linear_combination Real.cos (ω * t) * hre - Real.sin (ω * t) * him

/-- The complexified `D_x` applied to a complex vector. -/
def DxC (Dx : (X → ℝ) →ₗ[ℝ] Matrix X X ℝ) (z : X → ℂ) : Matrix X X ℂ :=
  fun i j => ⟨Dx (fun k => (z k).re) i j, Dx (fun k => (z k).im) i j⟩

omit [Fintype X] [DecidableEq X] in
/-- `D_x Re{z e^{jωt}} = Re{(D_x z) e^{jωt}}`. -/
@[tmio T, powerlib_foundation] theorem Dx_harm (Dx : (X → ℝ) →ₗ[ℝ] Matrix X X ℝ) (z : X → ℂ)
    (ω t : ℝ) : Dx (harm z ω t) = modX (DxC Dx z) ω t := by
  have e : harm z ω t = Real.cos (ω * t) • (fun k => (z k).re) -
      Real.sin (ω * t) • (fun k => (z k).im) := by
    funext k; simp [harm]; ring
  rw [e, map_sub, map_smul, map_smul]
  ext i j
  simp [modX, DxC]
  ring

omit [Fintype X] [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem modX_add (A B : Matrix X X ℂ) (ω t : ℝ) :
    modX (A + B) ω t = modX A ω t + modX B ω t := by
  ext i j; simp [modX]; ring

/-! ### `(I − e^{TA})⁻¹` from the modal coordinates -/

section Modal

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- A matrix solution of `Ẏ = Y B`, `Y(0) = I`, is `e^{tB}`. -/
@[tmio T, powerlib_foundation] theorem eq_expS_of_hasDerivAt {Z : Type*} [Fintype Z] [DecidableEq Z]
    {B : Matrix Z Z ℝ} {Yf : ℝ → Matrix Z Z ℝ} (hY : ∀ t, HasDerivAt Yf (Yf t * B) t)
    (h0 : Yf 0 = 1) (t : ℝ) : Yf t = expS B t := by
  have hZ : ∀ t, HasDerivAt (fun t => Yf t * expS B (-t)) 0 t := by
    intro t
    have hE := (hasDerivAt_expS B (-t)).scomp t (hasDerivAt_neg t)
    have h := (hY t).mul hE
    refine h.congr_deriv ?_
    simp only [Function.comp_apply, neg_one_smul, Matrix.mul_neg]
    rw [expS_comm B (-t), ← Matrix.mul_assoc, add_neg_cancel]
  have hc : ∀ t, Yf t * expS B (-t) = 1 := by
    intro t
    have := is_const_of_deriv_eq_zero (f := fun t => Yf t * expS B (-t))
      (fun t => (hZ t).differentiableAt) (fun t => (hZ t).deriv) t 0
    rw [this]; simp [h0, BlockAveraging.expS]
  calc Yf t = Yf t * (expS B (-t) * expS B t) := by rw [(expS_mul_neg B t).2, Matrix.mul_one]
    _ = expS B t := by rw [← Matrix.mul_assoc, hc t, Matrix.one_mul]

/-- `e^{t diag(base(0, ω/2), A_s)} = Ψ(t) = diag(R(ωt/2), e^{tA_s})`. -/
@[tmio T, powerlib_foundation] theorem expS_block (ω : ℝ) (As : Matrix Y Y ℝ) (t : ℝ) :
    expS (fromBlocks (base 0 (ω / 2)) 0 0 As) t = BlockAveraging.Psi ω As t := by
  refine (eq_expS_of_hasDerivAt (fun t => ?_) ?_ t).symm
  · refine (BlockAveraging.hasDerivAt_psi ω As t).congr_deriv ?_
    rw [BlockAveraging.Psi, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [base, quarter, rot, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · simp [BlockAveraging.Psi, BlockAveraging.expS, rot]

/-- The conjugation `M ↦ P M Q` as a ring homomorphism (`P Q = I`, `Q P = I`). -/
def conjHom {X : Type*} [Fintype X] [DecidableEq X] (P : Matrix X (Fin 2 ⊕ Y) ℝ)
    (Q : Matrix (Fin 2 ⊕ Y) X ℝ) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ →+* Matrix X X ℝ where
  toFun M := P * M * Q
  map_one' := by rw [Matrix.mul_one, hPQ]
  map_mul' M N := by
    rw [show P * M * Q * (P * N * Q) = P * M * (Q * P) * N * Q by simp only [Matrix.mul_assoc],
      hQP, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' M N := by rw [Matrix.mul_add, Matrix.add_mul]

/-- With real modal coordinates `Q A P = diag(base(0, ω/2), A_s)` and `ρ(e^{TA_s}) < 1`
(`T = 2π/ω`), `I − e^{TA}` is invertible: the monodromy of the linear part has no multiplier `1`. -/
@[tmio T, powerlib_foundation] theorem exists_minv_of_modal {X : Type*} [Fintype X] [DecidableEq X]
    {ω : ℝ} (hω : 0 < ω) {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) {A : Matrix X X ℝ} (As : Matrix Y Y ℝ)
    (hA0 : Q * A * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) :
    ∃ Minv : Matrix X X ℝ, Minv * (1 - expS A (2 * Real.pi / ω)) = 1 ∧
      (1 - expS A (2 * Real.pi / ω)) * Minv = 1 := by
  set T := 2 * Real.pi / ω with hT
  set B := fromBlocks (base 0 (ω / 2)) 0 0 As with hB
  set φ := conjHom P Q hPQ hQP
  have hφ : ∀ M, φ M = P * M * Q := fun M => rfl
  have hA : A = P * B * Q := by
    rw [← hA0, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ, Matrix.one_mul, Matrix.mul_assoc,
      hPQ, Matrix.mul_one]
  have hφc : Continuous φ := by
    show Continuous fun M => P * M * Q
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hexpA : expS A T = P * expS B T * Q := by
    have e : NormedSpace.exp (T • A) = φ (NormedSpace.exp (T • B)) := by
      have h := NormedSpace.map_exp φ hφc (T • B)
      convert h.symm using 2
      all_goals first | rfl | rw [hφ, hA, Matrix.mul_smul, Matrix.smul_mul]
    rw [BlockAveraging.expS, BlockAveraging.expS, e, hφ]
  have hpsiT : expS B T = fromBlocks (-1) 0 0 (expS As T) := by
    rw [hB, expS_block, BlockAveraging.Psi]
    have h : ω * T / 2 = Real.pi := by rw [hT]; field_simp
    rw [h]
    congr 1
    simp [rot]
  have hunit : IsUnit (1 - expS As T) := by
    have h1 : (1 : ℂ) ∉ spectrum ℂ ((expS As T).map (algebraMap ℝ ℂ)) := by
      intro hmem
      have hle : ((‖(1 : ℂ)‖₊ : NNReal) : ENNReal) ≤
          spectralRadius ℂ ((expS As T).map (algebraMap ℝ ℂ)) := by
        rw [spectralRadius_eq_of_unital]
        exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ ((expS As T).map (algebraMap ℝ ℂ))) =>
          ((‖k‖₊ : NNReal) : ENNReal)) 1 hmem
      rw [nnnorm_one, ENNReal.coe_one] at hle
      exact absurd hsr (not_lt.2 hle)
    rw [spectrum.notMem_iff, Algebra.algebraMap_eq_smul_one, one_smul,
      Matrix.isUnit_iff_isUnit_det] at h1
    have hmap : (1 : Matrix Y Y ℂ) - (expS As T).map (algebraMap ℝ ℂ) =
        (1 - expS As T).map (algebraMap ℝ ℂ) := by
      ext i j; simp [Matrix.one_apply]; split_ifs <;> simp
    rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, isUnit_iff_ne_zero,
      map_ne_zero] at h1
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact h1
  set U := hunit.unit
  set W : Matrix (Fin 2 ⊕ Y) (Fin 2 ⊕ Y) ℝ := fromBlocks ((1 / 2 : ℝ) • 1) 0 0 ↑U⁻¹ with hW
  have hsub : 1 - expS B T = fromBlocks ((2 : ℝ) • 1) 0 0 ↑U := by
    rw [hpsiT, IsUnit.unit_spec, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
    congr 1 <;> simp [two_smul]
  have hWl : W * (1 - expS B T) = 1 := by
    rw [hsub, hW, fromBlocks_multiply, ← fromBlocks_one]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, smul_mul_smul_comm,
      Matrix.one_mul, Units.inv_mul]
    norm_num
  have hWr : (1 - expS B T) * W = 1 := by
    rw [hsub, hW, fromBlocks_multiply, ← fromBlocks_one]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, smul_mul_smul_comm,
      Matrix.one_mul, Units.mul_inv]
    norm_num
  have hdiff : 1 - expS A T = P * (1 - expS B T) * Q := by
    rw [hexpA, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ]
  refine ⟨P * W * Q, ?_, ?_⟩
  · rw [hdiff, show P * W * Q * (P * (1 - expS B T) * Q) = P * W * (Q * P) * (1 - expS B T) * Q by
      simp only [Matrix.mul_assoc], hQP, Matrix.mul_one, Matrix.mul_assoc P W, hWl,
      Matrix.mul_one, hPQ]
  · rw [hdiff, show P * (1 - expS B T) * Q * (P * W * Q) = P * (1 - expS B T) * (Q * P) * W * Q by
      simp only [Matrix.mul_assoc], hQP, Matrix.mul_one, Matrix.mul_assoc P, hWr,
      Matrix.mul_one, hPQ]

end Modal

/-! ### The variational equation of the forced orbit

The forced system is `ẏ = A y + ε b(t) + N_ε(t, y)` near the equilibrium (`y = x − x₀`), with the
hypotheses of `ForcedOrbit.forced_orbit`; its variational matrix along a solution `y` is
`J_ε(t, y(t))` with `J_ε(t, y) = A + D_x y + ε D_u(t) + O(‖y‖² + ε²)` (for a concrete model, `J_ε` is
the Jacobian of the vector field, see `VoltageModulation.Model.orbJ_hasFDerivAt`). -/

section Orbit

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- For small `ε` the variational matrix `t ↦ J_ε(t, y(t))` along the (unique small) forced orbit
is `A + ε(A₀' + Re{A₁ e^{jωt}}) + ε² R_ε(t)` with `R_ε` continuous and uniformly bounded, whenever
`D_x y_p + D_u = A₀' + Re{A₁ e^{jωt}}` for the first-order orbit `y_p`. -/
@[tmio T, powerlib_foundation] theorem orbit_variational {A Minv : Matrix X X ℝ} {T : ℝ} (hT : 0 < T)
    (hL : Minv * (1 - expS A T) = 1) (hR : (1 - expS A T) * Minv = 1)
    {b : ℝ → X → ℝ} (hb : Continuous b) (hbp : ∀ t, b (t + T) = b t)
    {N : ℝ → ℝ → (X → ℝ) → X → ℝ} {K ρ ε0 : ℝ} (hK : 0 ≤ K) (hρ : 0 < ρ) (hε0 : 0 < ε0)
    (hNc : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × (X → ℝ) => N ε p.1 p.2)
      (Set.univ ×ˢ Metric.closedBall 0 ρ))
    (hNp : ∀ ε t y, N ε (t + T) y = N ε t y)
    (hN0 : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t, ‖N ε t 0‖ ≤ K * ε ^ 2)
    (hNL : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y1 y2, ‖y1‖ ≤ ρ → ‖y2‖ ≤ ρ →
      ‖N ε t y1 - N ε t y2‖ ≤ K * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖)
    {Jf : ℝ → ℝ → (X → ℝ) → Matrix X X ℝ} {Dx : (X → ℝ) →ₗ[ℝ] Matrix X X ℝ}
    {Du : ℝ → Matrix X X ℝ} {KJ KD : ℝ} (hKJ : 0 ≤ KJ) (hKD : 0 ≤ KD)
    (hDx : ∀ v, ‖Dx v‖ ≤ KD * ‖v‖) (hDu : Continuous Du)
    (hJc : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × (X → ℝ) => Jf ε p.1 p.2)
      (Set.univ ×ˢ Metric.closedBall 0 ρ))
    (hJ : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y, ‖y‖ ≤ ρ →
      ‖Jf ε t y - A - Dx y - ε • Du t‖ ≤ KJ * (‖y‖ ^ 2 + ε ^ 2))
    {yp : ℝ → X → ℝ} (hpp : ∀ t, yp (t + T) = yp t)
    (hpd : ∀ t, HasDerivAt yp (A *ᵥ yp t + b t) t)
    {ω : ℝ} (A0' : Matrix X X ℝ) (A1 : Matrix X X ℂ)
    (hlink : ∀ t, Dx (yp t) + Du t = A0' + modX A1 ω t) :
    ∃ c ε1 CR, 0 ≤ c ∧ 0 < ε1 ∧ ∃ Rm : ℝ → ℝ → Matrix X X ℝ,
      (∀ ε, 0 < ε → ε ≤ ε1 → Continuous (Rm ε)) ∧
      (∀ ε, 0 < ε → ε ≤ ε1 → ∀ t, ‖Rm ε t‖ ≤ CR) ∧
      ∀ ε, 0 < ε → ε ≤ ε1 → (∃ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) ∧
        ∀ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) → (fun t => Jf ε t (y t)) = physJR A A0' A1 Rm ω ε := by
  obtain ⟨c, C, ε1, hc, hC, hε1, hε1e, hcρ, hmain⟩ := forced_orbit hT hL hR hb hbp hK hρ hε0
    hNc hNp hN0 hNL
  have hex : ∀ ε, 0 < ε → ε ≤ ε1 → ∃ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t := fun ε h0 h1 => (hmain ε h0 h1).1
  set orb : ℝ → ℝ → X → ℝ := fun ε =>
    if h : 0 < ε ∧ ε ≤ ε1 then Classical.choose (hex ε h.1 h.2) else 0 with horb
  have horbS : ∀ ε, 0 < ε → ε ≤ ε1 → (∀ t, orb ε (t + T) = orb ε t) ∧
      (∀ t, ‖orb ε t‖ ≤ c * ε) ∧
      ∀ t, HasDerivAt (orb ε) (A *ᵥ orb ε t + (ε • b t + N ε t (orb ε t))) t := by
    intro ε h0 h1
    simp only [horb, h0, h1, and_self, ↓reduceDIte]
    exact Classical.choose_spec (hex ε h0 h1)
  have hypc : Continuous yp := continuous_iff_continuousAt.2 fun t => (hpd t).continuousAt
  set Rm : ℝ → ℝ → Matrix X X ℝ := fun ε => jacRem Jf A Dx Du (orb ε) yp ε with hRm
  refine ⟨c, ε1, KJ * (c ^ 2 + 1) + KD * C, hc, hε1, Rm, ?_, ?_, ?_⟩
  · intro ε h0 h1
    have hy := horbS ε h0 h1
    have hcρε : c * ε ≤ ρ := (mul_le_mul_of_nonneg_left h1 hc).trans hcρ
    exact continuous_jacRem A Dx ε (hJc ε h0.le (h1.trans hε1e))
      (continuous_iff_continuousAt.2 fun t => (hy.2.2 t).continuousAt)
      (fun t => (hy.2.1 t).trans hcρε) hypc hDu
  · intro ε h0 h1 t
    have hy := horbS ε h0 h1
    have hcρε : c * ε ≤ ρ := (mul_le_mul_of_nonneg_left h1 hc).trans hcρ
    exact jacRem_bound h0 hKJ hKD hDx (hJ ε h0.le (h1.trans hε1e)) hy.2.1 hcρε
      ((hmain ε h0 h1).2.2 _ hy.1 hy.2.1 hy.2.2 yp hpp hpd) t
  · intro ε h0 h1
    refine ⟨hex ε h0 h1, fun y hy1 hy2 hy3 => ?_⟩
    have hyo : y = orb ε := (hmain ε h0 h1).2.1 y (orb ε) hy1 hy2 hy3
      (horbS ε h0 h1).1 (horbS ε h0 h1).2.1 (horbS ε h0 h1).2.2
    funext t
    rw [hyo, jacRem_eq Jf A Dx Du (orb ε) yp h0.ne' t, hlink, physJR, physJ]

/-- End-to-end, stability: for all small `ε > 0` the forced orbit exists (unique in the ball of
radius `cε`), and when `A` has real modal coordinates with the pair `±jω/2`, `Re λ₁ < 0` and
`|g/2| < |λ₁|` (`λ₁ = u A₀' r`, `g = u A₁ r̄`), every Floquet multiplier of the variational
equation `ξ̇ = J_ε(t, y(t)) ξ` lies inside the unit circle. -/
@[tmio T, powerlib_foundation] theorem orbit_floquet_stable {A Minv : Matrix X X ℝ} {T : ℝ} (hT : 0 < T)
    (hL : Minv * (1 - expS A T) = 1) (hR : (1 - expS A T) * Minv = 1)
    {b : ℝ → X → ℝ} (hb : Continuous b) (hbp : ∀ t, b (t + T) = b t)
    {N : ℝ → ℝ → (X → ℝ) → X → ℝ} {K ρ ε0 : ℝ} (hK : 0 ≤ K) (hρ : 0 < ρ) (hε0 : 0 < ε0)
    (hNc : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × (X → ℝ) => N ε p.1 p.2)
      (Set.univ ×ˢ Metric.closedBall 0 ρ))
    (hNp : ∀ ε t y, N ε (t + T) y = N ε t y)
    (hN0 : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t, ‖N ε t 0‖ ≤ K * ε ^ 2)
    (hNL : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y1 y2, ‖y1‖ ≤ ρ → ‖y2‖ ≤ ρ →
      ‖N ε t y1 - N ε t y2‖ ≤ K * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖)
    {Jf : ℝ → ℝ → (X → ℝ) → Matrix X X ℝ} {Dx : (X → ℝ) →ₗ[ℝ] Matrix X X ℝ}
    {Du : ℝ → Matrix X X ℝ} {KJ KD : ℝ} (hKJ : 0 ≤ KJ) (hKD : 0 ≤ KD)
    (hDx : ∀ v, ‖Dx v‖ ≤ KD * ‖v‖) (hDu : Continuous Du)
    (hJc : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × (X → ℝ) => Jf ε p.1 p.2)
      (Set.univ ×ˢ Metric.closedBall 0 ρ))
    (hJ : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y, ‖y‖ ≤ ρ →
      ‖Jf ε t y - A - Dx y - ε • Du t‖ ≤ KJ * (‖y‖ ^ 2 + ε ^ 2))
    {yp : ℝ → X → ℝ} (hpp : ∀ t, yp (t + T) = yp t)
    (hpd : ∀ t, HasDerivAt yp (A *ᵥ yp t + b t) t)
    {ω : ℝ} (hω : 0 < ω) (hTω : T = 2 * Real.pi / ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (As : Matrix Y Y ℝ)
    (hA0 : Q * A * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1)
    (A0' : Matrix X X ℝ) (A1 : Matrix X X ℂ)
    (hlink : ∀ t, Dx (yp t) + Du t = A0' + modX A1 ω t)
    (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hg : ‖physLeft Q ⬝ᵥ (A1 *ᵥ star (physRight P)) / 2‖ ^ 2 <
      ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) →
        ∀ (μ : ℂ) (v : X → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => Jf ε t (y t)) T 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v →
            ‖μ‖ < 1 := by
  obtain ⟨c, ε1, CR, hc, hε1, Rm, hRc, hRb, hmain⟩ :=
    orbit_variational hT hL hR hb hbp hK hρ hε0 hNc hNp hN0 hNL hKJ hKD hDx hDu hJc hJ hpp hpd A0' A1 hlink
  have h := physical_stable_R hω hPQ hQP As hA0 A0' A1 Rm hε1 hRc hRb hs hg hsr
  refine ⟨c, hc, ?_, ?_⟩
  · filter_upwards [eventually_lt_nhdsGT hε1] with ε ⟨h0, h1⟩
    exact (hmain ε h0 h1.le).1
  · filter_upwards [h, eventually_lt_nhdsGT hε1] with ε hε ⟨h0, h1⟩
    intro y hy1 hy2 hy3 μ v hv hμ
    rw [(hmain ε h0 h1.le).2 y hy1 hy2 hy3, hTω] at hμ
    exact hε μ v hv hμ

/-- End-to-end, parametric instability: with `|λ₁| < |g/2|` the variational equation of the
forced orbit is Floquet unstable for all small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem orbit_floquet_unstable {A Minv : Matrix X X ℝ} {T : ℝ} (hT : 0 < T)
    (hL : Minv * (1 - expS A T) = 1) (hR : (1 - expS A T) * Minv = 1)
    {b : ℝ → X → ℝ} (hb : Continuous b) (hbp : ∀ t, b (t + T) = b t)
    {N : ℝ → ℝ → (X → ℝ) → X → ℝ} {K ρ ε0 : ℝ} (hK : 0 ≤ K) (hρ : 0 < ρ) (hε0 : 0 < ε0)
    (hNc : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × (X → ℝ) => N ε p.1 p.2)
      (Set.univ ×ˢ Metric.closedBall 0 ρ))
    (hNp : ∀ ε t y, N ε (t + T) y = N ε t y)
    (hN0 : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t, ‖N ε t 0‖ ≤ K * ε ^ 2)
    (hNL : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y1 y2, ‖y1‖ ≤ ρ → ‖y2‖ ≤ ρ →
      ‖N ε t y1 - N ε t y2‖ ≤ K * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖)
    {Jf : ℝ → ℝ → (X → ℝ) → Matrix X X ℝ} {Dx : (X → ℝ) →ₗ[ℝ] Matrix X X ℝ}
    {Du : ℝ → Matrix X X ℝ} {KJ KD : ℝ} (hKJ : 0 ≤ KJ) (hKD : 0 ≤ KD)
    (hDx : ∀ v, ‖Dx v‖ ≤ KD * ‖v‖) (hDu : Continuous Du)
    (hJc : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × (X → ℝ) => Jf ε p.1 p.2)
      (Set.univ ×ˢ Metric.closedBall 0 ρ))
    (hJ : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y, ‖y‖ ≤ ρ →
      ‖Jf ε t y - A - Dx y - ε • Du t‖ ≤ KJ * (‖y‖ ^ 2 + ε ^ 2))
    {yp : ℝ → X → ℝ} (hpp : ∀ t, yp (t + T) = yp t)
    (hpd : ∀ t, HasDerivAt yp (A *ᵥ yp t + b t) t)
    {ω : ℝ} (hω : 0 < ω) (hTω : T = 2 * Real.pi / ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (As : Matrix Y Y ℝ)
    (hA0 : Q * A * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1)
    (A0' : Matrix X X ℝ) (A1 : Matrix X X ℂ)
    (hlink : ∀ t, Dx (yp t) + Du t = A0' + modX A1 ω t)
    (hg : ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2 <
      ‖physLeft Q ⬝ᵥ (A1 *ᵥ star (physRight P)) / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) →
        Periodic.FloquetUnstable (fun t => Jf ε t (y t)) T := by
  obtain ⟨c, ε1, CR, hc, hε1, Rm, hRc, hRb, hmain⟩ :=
    orbit_variational hT hL hR hb hbp hK hρ hε0 hNc hNp hN0 hNL hKJ hKD hDx hDu hJc hJ hpp hpd A0' A1 hlink
  have h := physical_unstable_R hω hPQ hQP As hA0 A0' A1 Rm hε1 hRc hRb hg hsr
  refine ⟨c, hc, ?_, ?_⟩
  · filter_upwards [eventually_lt_nhdsGT hε1] with ε ⟨h0, h1⟩
    exact (hmain ε h0 h1.le).1
  · filter_upwards [h, eventually_lt_nhdsGT hε1] with ε hε ⟨h0, h1⟩
    intro y hy1 hy2 hy3
    rw [(hmain ε h0 h1.le).2 y hy1 hy2 hy3, hTω]
    exact hε

/-- Three-state cores, end-to-end stability: `A` has the pair `±jΩ` (eigenvectors `r`, `u`,
`u r = 1`) and a real pole `λ₃ < 0` (`r₃`, `u₃`, `u₃ r₃ = 1`), drive at `ω = 2Ω`. With
`λ₁ = u A₀' r` and `g = u A₁ r̄`, `Re λ₁ < 0` and `|g/2| < |λ₁|`: the forced orbit exists, is unique
in the ball of radius `cε`, and its variational equation has all Floquet multipliers inside the unit
circle for all small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem orbit_floquet_three_stable {A Minv : Matrix (Fin 3) (Fin 3) ℝ} {T : ℝ} (hT : 0 < T)
    (hL : Minv * (1 - expS A T) = 1) (hR : (1 - expS A T) * Minv = 1)
    {b : ℝ → (Fin 3) → ℝ} (hb : Continuous b) (hbp : ∀ t, b (t + T) = b t)
    {N : ℝ → ℝ → ((Fin 3) → ℝ) → (Fin 3) → ℝ} {K ρ ε0 : ℝ} (hK : 0 ≤ K) (hρ : 0 < ρ) (hε0 : 0 < ε0)
    (hNc : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × ((Fin 3) → ℝ) => N ε p.1 p.2)
      (Set.univ ×ˢ Metric.closedBall 0 ρ))
    (hNp : ∀ ε t y, N ε (t + T) y = N ε t y)
    (hN0 : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t, ‖N ε t 0‖ ≤ K * ε ^ 2)
    (hNL : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y1 y2, ‖y1‖ ≤ ρ → ‖y2‖ ≤ ρ →
      ‖N ε t y1 - N ε t y2‖ ≤ K * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖)
    {Jf : ℝ → ℝ → ((Fin 3) → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {Dx : ((Fin 3) → ℝ) →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ}
    {Du : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {KJ KD : ℝ} (hKJ : 0 ≤ KJ) (hKD : 0 ≤ KD)
    (hDx : ∀ v, ‖Dx v‖ ≤ KD * ‖v‖) (hDu : Continuous Du)
    (hJc : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × ((Fin 3) → ℝ) => Jf ε p.1 p.2)
      (Set.univ ×ˢ Metric.closedBall 0 ρ))
    (hJ : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y, ‖y‖ ≤ ρ →
      ‖Jf ε t y - A - Dx y - ε • Du t‖ ≤ KJ * (‖y‖ ^ 2 + ε ^ 2))
    {yp : ℝ → (Fin 3) → ℝ} (hpp : ∀ t, yp (t + T) = yp t)
    (hpd : ∀ t, HasDerivAt yp (A *ᵥ yp t + b t) t)
    {Ω l3 : ℝ} (hΩ : 0 < Ω) (hl3 : l3 < 0) (hTΩ : T = 2 * Real.pi / (2 * Ω))
    {r u : Fin 3 → ℂ} {r3 u3 : Fin 3 → ℝ}
    (hr : A.map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* A.map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : A *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* A = l3 • u3) (hur3 : u3 ⬝ᵥ r3 = 1)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ) (A1 : Matrix (Fin 3) (Fin 3) ℂ)
    (hlink : ∀ t, Dx (yp t) + Du t = A0' + modX A1 (2 * Ω) t)
    (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ (A1 *ᵥ star r) / 2‖ ^ 2 < ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → (Fin 3) → ℝ, (∀ t, y (t + T) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → (Fin 3) → ℝ, (∀ t, y (t + T) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) →
        ∀ (μ : ℂ) (v : Fin 3 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => Jf ε t (y t)) T 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v →
            ‖μ‖ < 1 := by
  obtain ⟨hQP, hPQ, hQAP, hLu, hRr⟩ := modal_three hΩ.ne' hr hu hur hr3 hu3 hur3
  have hω : 0 < 2 * Ω := by linarith
  have hA0 : modalQ u u3 * A * modalP r r3 = fromBlocks (base 0 (2 * Ω / 2)) 0 0 !![l3] := by
    rw [hQAP, mul_div_cancel_left₀ _ two_ne_zero]
  have hq : ‖expS (!![l3] : Matrix (Fin 1) (Fin 1) ℝ) (2 * Real.pi / (2 * Ω))‖ < 1 := by
    rw [norm_expS_one, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (by positivity) hl3
  exact orbit_floquet_stable hT hL hR hb hbp hK hρ hε0 hNc hNp hN0 hNL hKJ hKD hDx hDu hJc hJ hpp hpd hω hTΩ hPQ hQP _ hA0 (BlockAveraging.spectralRadius_lt_one_of_norm _ hq) A0' A1 hlink
    (by rw [hLu, hRr]; exact hs) (by rw [hLu, hRr]; exact hg)

/-- Three-state cores, end-to-end parametric instability: `|λ₁| < |g/2|`. -/
@[tmio T, powerlib_foundation] theorem orbit_floquet_three_unstable {A Minv : Matrix (Fin 3) (Fin 3) ℝ} {T : ℝ} (hT : 0 < T)
    (hL : Minv * (1 - expS A T) = 1) (hR : (1 - expS A T) * Minv = 1)
    {b : ℝ → (Fin 3) → ℝ} (hb : Continuous b) (hbp : ∀ t, b (t + T) = b t)
    {N : ℝ → ℝ → ((Fin 3) → ℝ) → (Fin 3) → ℝ} {K ρ ε0 : ℝ} (hK : 0 ≤ K) (hρ : 0 < ρ) (hε0 : 0 < ε0)
    (hNc : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × ((Fin 3) → ℝ) => N ε p.1 p.2)
      (Set.univ ×ˢ Metric.closedBall 0 ρ))
    (hNp : ∀ ε t y, N ε (t + T) y = N ε t y)
    (hN0 : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t, ‖N ε t 0‖ ≤ K * ε ^ 2)
    (hNL : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y1 y2, ‖y1‖ ≤ ρ → ‖y2‖ ≤ ρ →
      ‖N ε t y1 - N ε t y2‖ ≤ K * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖)
    {Jf : ℝ → ℝ → ((Fin 3) → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {Dx : ((Fin 3) → ℝ) →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ}
    {Du : ℝ → Matrix (Fin 3) (Fin 3) ℝ} {KJ KD : ℝ} (hKJ : 0 ≤ KJ) (hKD : 0 ≤ KD)
    (hDx : ∀ v, ‖Dx v‖ ≤ KD * ‖v‖) (hDu : Continuous Du)
    (hJc : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × ((Fin 3) → ℝ) => Jf ε p.1 p.2)
      (Set.univ ×ˢ Metric.closedBall 0 ρ))
    (hJ : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y, ‖y‖ ≤ ρ →
      ‖Jf ε t y - A - Dx y - ε • Du t‖ ≤ KJ * (‖y‖ ^ 2 + ε ^ 2))
    {yp : ℝ → (Fin 3) → ℝ} (hpp : ∀ t, yp (t + T) = yp t)
    (hpd : ∀ t, HasDerivAt yp (A *ᵥ yp t + b t) t)
    {Ω l3 : ℝ} (hΩ : 0 < Ω) (hl3 : l3 < 0) (hTΩ : T = 2 * Real.pi / (2 * Ω))
    {r u : Fin 3 → ℂ} {r3 u3 : Fin 3 → ℝ}
    (hr : A.map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* A.map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : A *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* A = l3 • u3) (hur3 : u3 ⬝ᵥ r3 = 1)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ) (A1 : Matrix (Fin 3) (Fin 3) ℂ)
    (hlink : ∀ t, Dx (yp t) + Du t = A0' + modX A1 (2 * Ω) t)
    (hg : ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2 < ‖u ⬝ᵥ (A1 *ᵥ star r) / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → (Fin 3) → ℝ, (∀ t, y (t + T) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → (Fin 3) → ℝ, (∀ t, y (t + T) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) →
        Periodic.FloquetUnstable (fun t => Jf ε t (y t)) T := by
  obtain ⟨hQP, hPQ, hQAP, hLu, hRr⟩ := modal_three hΩ.ne' hr hu hur hr3 hu3 hur3
  have hω : 0 < 2 * Ω := by linarith
  have hA0 : modalQ u u3 * A * modalP r r3 = fromBlocks (base 0 (2 * Ω / 2)) 0 0 !![l3] := by
    rw [hQAP, mul_div_cancel_left₀ _ two_ne_zero]
  have hq : ‖expS (!![l3] : Matrix (Fin 1) (Fin 1) ℝ) (2 * Real.pi / (2 * Ω))‖ < 1 := by
    rw [norm_expS_one, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (by positivity) hl3
  exact orbit_floquet_unstable hT hL hR hb hbp hK hρ hε0 hNc hNp hN0 hNL hKJ hKD hDx hDu hJc hJ hpp hpd hω hTΩ hPQ hQP _ hA0 (BlockAveraging.spectralRadius_lt_one_of_norm _ hq) A0' A1 hlink
    (by rw [hLu, hRr]; exact hg)

end Orbit

end powerlib.ParametricResonance.ForcedOrbit
