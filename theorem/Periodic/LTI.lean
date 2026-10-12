import theorem.Periodic.Transition

/-! # The LTI special case of the monodromy matrix

Foundation layer. For a constant state matrix `A` (the unforced case `ε = 0` of a periodically
forced orbit, whose variational matrix is the constant Jacobian at the equilibrium):
* `transition_const`: `Φ(t, s) = exp ((t - s) • A)` for `t ≥ s` (uniqueness of the matrix
  solution, Mathlib `hasDerivAt_exp_smul_const'`);
* `monodromy_const`: `monodromy (fun _ => A) T s = exp (T • A)`;
* `exp_mulVec_of_eigen`, `monodromy_const_mulVec_eigen`: an eigenpair `(μ, v)` of the
  complexified `A` gives the Floquet multiplier `e^{μ T}` with the same eigenvector;
* `norm_exp_mul_eq`, `log_norm_exp_div`: `|e^{μ T}| = e^{Re μ · T}`, so the Floquet rate
  `σ = ln |ρ| / T` of the unforced orbit equals `Re μ` (`= -α` for the victim mode
  `μ = -α ± jω`).

Source: work-sync projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/archive/
notes/concepts/forced-orbit-and-bandwidth.md, block B (`σ_fp(ε = 0) = -α`; at `ε = 0` both
multipliers are `e^{-αT}`); theory/T-harmonic-linearization.md §1.6 (LTI check
`A(t) = A₀`).
-/

noncomputable section
namespace powerlib.Periodic

open Set Matrix Function
open scoped Matrix.Norms.Operator

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- For a constant state matrix, `Φ(t, s) = exp ((t - s) • A)` (`t ≥ s`). -/
@[powerlib_foundation] theorem transition_const (A : Matrix X X ℝ) {s t : ℝ} (hst : s ≤ t) :
    transition (fun _ => A) t s = NormedSpace.exp ((t - s) • A) := by
  have hM : ∀ r, ‖(fun _ : ℝ => A) r‖ ≤ ‖A‖ := fun _ => le_rfl
  have hY : IsIntegralCurveOn (fun r => NormedSpace.exp ((r - s) • A))
      (matField (fun _ => A)) (Ici s) := by
    intro r _
    have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A (r - s)).scomp r
      ((hasDerivAt_id' r).sub_const s)
    simp only [matField, Function.comp_def, one_smul] at h ⊢
    exact h.hasDerivWithinAt
  have h := transition_unique continuous_const hM hY t hst
  simpa using h.symm

/-- LTI monodromy: `monodromy (fun _ => A) T s = exp (T • A)` (`T ≥ 0`). -/
@[powerlib_foundation] theorem monodromy_const (A : Matrix X X ℝ) {T : ℝ} (hT : 0 ≤ T)
    (s : ℝ) : monodromy (fun _ => A) T s = NormedSpace.exp (T • A) := by
  rw [monodromy, transition_const A (by linarith), add_sub_cancel_left]

/-- A complex matrix exponential acts on an eigenvector by the exponential of the eigenvalue. -/
@[powerlib_foundation] theorem exp_mulVec_of_eigen (B : Matrix X X ℂ) {μ : ℂ} {v : X → ℂ}
    (hv : B *ᵥ v = μ • v) : NormedSpace.exp B *ᵥ v = Complex.exp μ • v := by
  have hpow : ∀ k : ℕ, (B ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hv, smul_smul, pow_succ',
        mul_comm]
  let L : Matrix X X ℂ →L[ℂ] (X → ℂ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun N => N *ᵥ v
        map_add' := fun N N' => Matrix.add_mulVec N N' v
        map_smul' := fun c N => Matrix.smul_mulVec c N v }
  have hL : ∀ N, L N = N *ᵥ v := fun _ => rfl
  rw [congrFun (NormedSpace.exp_eq_tsum ℂ) B, ← hL,
    L.map_tsum (NormedSpace.expSeries_summable' B)]
  simp_rw [map_smul, hL, hpow, smul_smul]
  have hs : Summable (fun n : ℕ => (n.factorial : ℂ)⁻¹ * μ ^ n) := by
    simpa [smul_eq_mul] using NormedSpace.expSeries_summable' (𝕂 := ℂ) μ
  rw [hs.tsum_smul_const, Complex.exp_eq_exp_ℂ, congrFun (NormedSpace.exp_eq_tsum ℂ) μ]
  simp [smul_eq_mul]

/-- LTI Floquet multiplier: an eigenpair `(μ, v)` of the complexified constant matrix gives
`M v = e^{μ T} v` for the monodromy matrix `M = exp (T • A)`. -/
@[powerlib_foundation] theorem monodromy_const_mulVec_eigen (A : Matrix X X ℝ) {T : ℝ}
    (hT : 0 ≤ T) (s : ℝ) {μ : ℂ} {v : X → ℂ} (hv : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) :
    (monodromy (fun _ => A) T s).map (algebraMap ℝ ℂ) *ᵥ v = Complex.exp (μ * T) • v := by
  rw [monodromy_const A hT]
  have hcont : Continuous fun N : Matrix X X ℝ => N.map (algebraMap ℝ ℂ) :=
    continuous_id.matrix_map (continuous_algebraMap ℝ ℂ)
  have h := NormedSpace.map_exp ((algebraMap ℝ ℂ).mapMatrix (m := X)) hcont (T • A)
  have hmap : (NormedSpace.exp (T • A)).map (algebraMap ℝ ℂ) =
      NormedSpace.exp ((T : ℂ) • A.map (algebraMap ℝ ℂ)) := by
    rw [RingHom.mapMatrix_apply] at h
    refine h.trans ?_
    congr 1
    ext i j
    simp [Matrix.map_apply]
  rw [hmap]
  apply exp_mulVec_of_eigen
  rw [Matrix.smul_mulVec, hv, smul_smul, mul_comm]

/-- `|e^{μ T}| = e^{(Re μ) T}`. -/
@[powerlib_foundation] theorem norm_exp_mul_eq (μ : ℂ) (T : ℝ) :
    ‖Complex.exp (μ * T)‖ = Real.exp (μ.re * T) := by
  rw [Complex.norm_exp]
  simp

/-- The Floquet rate `ln |ρ| / T` of the multiplier `ρ = e^{μ T}` is `Re μ`. -/
@[powerlib_foundation] theorem log_norm_exp_div (μ : ℂ) {T : ℝ} (hT : T ≠ 0) :
    Real.log ‖Complex.exp (μ * T)‖ / T = μ.re := by
  rw [norm_exp_mul_eq, Real.log_exp]
  field_simp

end powerlib.Periodic
