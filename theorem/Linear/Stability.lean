import theorem.Linear.Plant

/-! # The linear stability hub

For the affine linear field of `A` centred at `e`, every attractive sentence of the Flow
semantics — local or global, asymptotic or exponential — holds at `e` exactly when `A` is
Hurwitz. This is the one place where linear stability is decided; every linear family inherits
it through its plant map.

Sampled contraction is decided by the same test: Hurwitz gives a contracting integer horizon
(LeanForControl's spectral-radius argument), and a non-decaying eigenmode does not contract. A
conserved energy excludes Hurwitz on a nontrivial state space, and a one-state plant decays exactly
at the rates up to its pole.

Scope.
* Generic: the affine linear field `affineLinearVectorField A e` of an arbitrary real square
  matrix `A` centred at an arbitrary point `e`, read by the flow semantics; no model.

Source: LeanForControl: the linearization theorem
(`hurwitz_linearization_locally_exponentially_stable`), instability from an eigenvalue in the
open right half plane (`unstable_affineLinear_of_eigenvalue_re_pos`), uniqueness of solutions of
Lipschitz fields (`eqOn_of_isIntegralCurveOn_Icc`) and the contracting horizon of a Hurwitz
matrix (`IsHurwitz.exists_norm_exp_nat_smul_lt_one`); Mathlib's matrix exponential.

Results.
* Hurwitz ⇒ local exponential stability: LeanForControl's linearization theorem, applied to the
  field itself (`locallyExponentiallyStable_of_isHurwitz`, with `affine_isEquilibrium`,
  `affine_hasFDerivAt`, `affine_contDiff`).
* Forward completeness: the matrix exponential (`solution`, `solution_initial`,
  `solution_hasDerivAt`, `forwardComplete`, `affine_lipschitzWith`, `trajectory_eq_solution`,
  `trajectory_unique`).
* Local ⇒ global exponential stability: the field is linear about `e`, so solution segments scale
  (`isTrajectoryOn_scale`, `globallyExponentiallyStable_of_locallyExponentiallyStable`,
  `globallyExponentiallyStable_of_isHurwitz`).
* Local asymptotic stability ⇒ Hurwitz: a real eigenmode with `Re μ ≥ 0` does not decay
  (`eigenmode`, `eigen_component_hasDerivAt`, `eigenmode_hasDerivAt`, `eigenmode_norm_sq`,
  `isHurwitz_of_localAsymptoticStable`).
* The hub: `holds_iff_isHurwitz` (every attractive sentence), `holds_of_isHurwitz`,
  `globallyAsymptoticallyStable_of_isHurwitz`, `localAsymptoticStable_of_isHurwitz`,
  `lyapunovStable_of_isHurwitz`; `unstable_of_eigenvalue`.
* Sampled contraction: `contractive_block`, `norm_op_apply_le`, `op_exp`,
  `sampledContraction_of_isHurwitz`, `isHurwitz_of_sampledContraction`,
  `sampledContraction_iff_isHurwitz`.
* Conservation and one-state plants: `not_isHurwitz_of_conservative`, `decay_scalar_iff` (a
  one-state plant `x' = -b x` decays exactly at the rates up to `b`; with `op_one_apply`,
  `scalar_solution_hasDerivAt`, `trajectory_eq_scalar`).
-/

noncomputable section

namespace powerlib.Linear

open Matrix LinearSystems Set Filter Topology NormedSpace

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

@[powerlib_foundation] theorem affine_isEquilibrium (A : Matrix (Fin n) (Fin n) ℝ) (e : ℝⁿ) :
    IsEquilibrium (affineLinearVectorField A e) e := by
  simp [IsEquilibrium, affine_apply]

@[powerlib_foundation] theorem affine_hasFDerivAt (A : Matrix (Fin n) (Fin n) ℝ) (e x : ℝⁿ) :
    HasFDerivAt (affineLinearVectorField A e) (op A) x := by
  have h : HasFDerivAt (fun y : ℝⁿ => op A (y - e))
      ((op A).comp (ContinuousLinearMap.id ℝ ℝⁿ)) x :=
    (op A).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const e)
  rw [ContinuousLinearMap.comp_id] at h
  exact h

@[powerlib_foundation] theorem affine_contDiff (A : Matrix (Fin n) (Fin n) ℝ) (e : ℝⁿ) :
    ContDiff ℝ 1 (affineLinearVectorField A e) :=
  (op A).contDiff.comp (contDiff_id.sub contDiff_const)

/-- Hurwitz gives local exponential stability (LeanForControl's linearization theorem). -/
@[powerlib_foundation, aesop safe apply] theorem locallyExponentiallyStable_of_isHurwitz
    {A : Matrix (Fin n) (Fin n) ℝ} (e : ℝⁿ) (hA : IsHurwitz A) :
    LocallyExponentiallyStable (affineLinearVectorField A e) e :=
  hurwitz_linearization_locally_exponentially_stable A (affine_contDiff A e)
    (affine_isEquilibrium A e) (affine_hasFDerivAt A e e).fderiv hA

/-! ## Solutions -/

/-- The solution through `x₀` at time `t₀`. -/
def solution (A : Matrix (Fin n) (Fin n) ℝ) (e : ℝⁿ) (t₀ : ℝ) (x₀ : ℝⁿ) (t : ℝ) : ℝⁿ :=
  e + exp ((t - t₀) • op A) (x₀ - e)

@[simp, powerlib_foundation] theorem solution_initial (A : Matrix (Fin n) (Fin n) ℝ) (e : ℝⁿ)
    (t₀ : ℝ) (x₀ : ℝⁿ) : solution A e t₀ x₀ t₀ = x₀ := by
  have h : (t₀ - t₀) • op A = 0 := by rw [sub_self]; exact zero_smul ℝ (op A)
  show e + exp ((t₀ - t₀) • op A) (x₀ - e) = x₀
  rw [h, exp_zero]
  exact add_sub_cancel e x₀

@[powerlib_foundation] theorem solution_hasDerivAt (A : Matrix (Fin n) (Fin n) ℝ) (e : ℝⁿ)
    (t₀ : ℝ) (x₀ : ℝⁿ) (t : ℝ) :
    HasDerivAt (solution A e t₀ x₀) (affineLinearVectorField A e (solution A e t₀ x₀ t)) t := by
  have hexp : HasDerivAt (fun s : ℝ => exp ((s - t₀) • op A))
      (op A * exp ((t - t₀) • op A)) t := by
    have h := (hasDerivAt_exp_smul_const' (op A) (t - t₀)).scomp t
      ((hasDerivAt_id' t).sub_const t₀)
    rw [one_smul] at h
    exact h
  have happ := (hexp.clm_apply (hasDerivAt_const t (x₀ - e))).const_add e
  have hfun : solution A e t₀ x₀ = fun s => e + exp ((s - t₀) • op A) (x₀ - e) := rfl
  rw [hfun]
  convert happ using 1
  simp [affine_apply]

/-- The affine linear field has a solution through every state. -/
@[powerlib_foundation] theorem forwardComplete (A : Matrix (Fin n) (Fin n) ℝ) (e : ℝⁿ) :
    Flow.ForwardComplete (affineLinearVectorField A e) :=
  fun t₀ x₀ => ⟨solution A e t₀ x₀, solution_initial A e t₀ x₀,
    fun t _ => (solution_hasDerivAt A e t₀ x₀ t).hasDerivWithinAt⟩

/-- The affine linear field is globally Lipschitz. -/
@[powerlib_foundation] theorem affine_lipschitzWith (A : Matrix (Fin n) (Fin n) ℝ) (e : ℝⁿ) :
    LipschitzWith ‖op A‖₊ (affineLinearVectorField A e) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simp only [affine_apply, dist_eq_norm, ← map_sub, sub_sub_sub_cancel_right, coe_nnnorm]
    exact (op A).le_opNorm _

/-- Every solution segment of the affine linear field is the matrix-exponential solution
(LeanForControl's uniqueness for Lipschitz fields). -/
@[powerlib_foundation] theorem trajectory_eq_solution {A : Matrix (Fin n) (Fin n) ℝ} {e : ℝⁿ}
    {φ : ℝ → ℝⁿ} {t₀ t₁ : ℝ} (hφ : IsTrajectoryOn φ (affineLinearVectorField A e) t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, φ t = solution A e t₀ (φ t₀) t :=
  eqOn_of_isIntegralCurveOn_Icc (fun _ => affine_lipschitzWith A e) hφ
    (fun t _ => (solution_hasDerivAt A e t₀ (φ t₀) t).hasDerivWithinAt)
    (solution_initial A e t₀ (φ t₀)).symm

/-- Two solution segments with the same initial state coincide. -/
@[powerlib_foundation] theorem trajectory_unique {A : Matrix (Fin n) (Fin n) ℝ} {e : ℝⁿ}
    {φ ψ : ℝ → ℝⁿ} {t₀ t₁ : ℝ} (hφ : IsTrajectoryOn φ (affineLinearVectorField A e) t₀ t₁)
    (hψ : IsTrajectoryOn ψ (affineLinearVectorField A e) t₀ t₁) (h₀ : φ t₀ = ψ t₀) :
    ∀ t ∈ Icc t₀ t₁, φ t = ψ t :=
  eqOn_of_isIntegralCurveOn_Icc (fun _ => affine_lipschitzWith A e) hφ hψ h₀

/-! ## One-state plants -/

@[powerlib_foundation] theorem op_one_apply (c : ℝ) (y : EuclideanSpace ℝ (Fin 1)) :
    op !![c] y = c • y := by
  ext i
  fin_cases i
  simp [Matrix.mulVec, dotProduct]

/-- The explicit solution of the one-state field `x' = -a (x - e)`. -/
@[powerlib_foundation] theorem scalar_solution_hasDerivAt (a : ℝ) (e x₀ : EuclideanSpace ℝ (Fin 1))
    (t₀ t : ℝ) :
    HasDerivAt (fun t => e + Real.exp (-a * (t - t₀)) • (x₀ - e))
      (affineLinearVectorField !![-a] e (e + Real.exp (-a * (t - t₀)) • (x₀ - e))) t := by
  have hexp : HasDerivAt (fun t => Real.exp (-a * (t - t₀))) (Real.exp (-a * (t - t₀)) * -a) t := by
    simpa using (((hasDerivAt_id t).sub_const t₀).const_mul (-a)).exp
  have h := (hexp.smul_const (x₀ - e)).const_add e
  convert h using 1
  rw [affine_apply, add_sub_cancel_left, op_one_apply, smul_smul, mul_comm]

/-- Every solution segment of a one-state plant decays or grows exponentially. -/
@[powerlib_foundation] theorem trajectory_eq_scalar {a : ℝ} {e : EuclideanSpace ℝ (Fin 1)}
    {φ : ℝ → EuclideanSpace ℝ (Fin 1)} {t₀ t₁ : ℝ}
    (hφ : IsTrajectoryOn φ (affineLinearVectorField !![-a] e) t₀ t₁) :
    ∀ t ∈ Icc t₀ t₁, φ t = e + Real.exp (-a * (t - t₀)) • (φ t₀ - e) :=
  trajectory_unique hφ (fun t _ => (scalar_solution_hasDerivAt a e (φ t₀) t₀ t).hasDerivWithinAt)
    (by simp)

/-- A one-state plant `x' = -b x` decays exactly at the rates up to `b`: its solutions are the
exponentials `e^{-b t}`. -/
@[powerlib_foundation] theorem decay_scalar_iff (b a : ℝ) :
    Flow.Decay (affineLinearVectorField !![-b] 0) 0 a ↔ a ≤ b := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hab
    push Not at hab
    set x₀ : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1 with hx₀_def
    have hx₀ : ‖x₀‖ = 1 := by simp [hx₀_def]
    set T : ℝ := |C| / (a - b) with hT_def
    have hT0 : 0 ≤ T := div_nonneg (abs_nonneg C) (by linarith)
    have hsol : IsTrajectoryOn (fun t => 0 + Real.exp (-b * (t - 0)) • (x₀ - 0))
        (affineLinearVectorField !![-b] 0) 0 T :=
      fun t _ => (scalar_solution_hasDerivAt b 0 x₀ 0 t).hasDerivWithinAt
    have hbound := hC 0 T _ hsol T ⟨hT0, le_rfl⟩
    simp only [zero_add, sub_zero, mul_zero, Real.exp_zero, one_smul, norm_smul,
      Real.norm_of_nonneg (Real.exp_pos _).le, hx₀, mul_one] at hbound
    have hprod : (a - b) * T = |C| := by
      rw [hT_def]
      field_simp
    have hgap : Real.exp ((a - b) * T) ≤ C := by
      have h := mul_le_mul_of_nonneg_left hbound (Real.exp_pos (a * T)).le
      have e₁ : Real.exp (a * T) * Real.exp (-b * T) = Real.exp ((a - b) * T) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have e₂ : Real.exp (a * T) * (C * Real.exp (-a * T)) = C := by
        rw [mul_left_comm, ← Real.exp_add, show a * T + -a * T = 0 by ring, Real.exp_zero,
          mul_one]
      linarith
    have hlarge : |C| + 1 ≤ Real.exp ((a - b) * T) := by
      rw [hprod]
      exact Real.add_one_le_exp |C|
    linarith [le_abs_self C]
  · intro hab
    refine ⟨1, fun t₀ t₁ φ hφ t ht => ?_⟩
    rw [trajectory_eq_scalar hφ t ht]
    simp only [zero_add, sub_zero, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]
    gcongr
    nlinarith [ht.1]

/-- Solution segments scale about the centre. -/
@[powerlib_foundation] theorem isTrajectoryOn_scale {A : Matrix (Fin n) (Fin n) ℝ} {e : ℝⁿ}
    {φ : ℝ → ℝⁿ} {t₀ t₁ : ℝ} (hφ : IsTrajectoryOn φ (affineLinearVectorField A e) t₀ t₁)
    (c : ℝ) :
    IsTrajectoryOn (fun t => e + c • (φ t - e)) (affineLinearVectorField A e) t₀ t₁ := by
  intro t ht
  have h := (((hφ t ht).sub_const e).const_smul c).const_add e
  convert h using 1
  simp [affine_apply, map_smul]

/-- Local exponential stability of the affine linear field is global. -/
@[powerlib_foundation] theorem globallyExponentiallyStable_of_locallyExponentiallyStable
    {A : Matrix (Fin n) (Fin n) ℝ} {e : ℝⁿ}
    (h : LocallyExponentiallyStable (affineLinearVectorField A e) e) :
    Flow.GloballyExponentiallyStable (affineLinearVectorField A e) e := by
  obtain ⟨r, C, a, hr, hC, ha, hb⟩ := h
  refine ⟨affine_isEquilibrium A e, forwardComplete A e, C, a, hC, ha,
    fun t₀ t₁ φ hφ t ht => ?_⟩
  have hd : 0 ≤ ‖φ t₀ - e‖ := norm_nonneg _
  have hc : 0 < r / (2 * (‖φ t₀ - e‖ + 1)) := by positivity
  have hstart : ‖(e + (r / (2 * (‖φ t₀ - e‖ + 1))) • (φ t₀ - e)) - e‖ < r := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hc.le, div_mul_eq_mul_div,
      div_lt_iff₀ (by positivity)]
    nlinarith
  have hbound := hb t₀ t₁ _ (isTrajectoryOn_scale hφ _) hstart t ht
  rw [add_sub_cancel_left, add_sub_cancel_left, norm_smul, norm_smul,
    Real.norm_of_nonneg hc.le] at hbound
  have : r / (2 * (‖φ t₀ - e‖ + 1)) * ‖φ t - e‖ ≤
      r / (2 * (‖φ t₀ - e‖ + 1)) * (C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - e‖) := by
    linarith
  exact le_of_mul_le_mul_left this hc

/-- Hurwitz gives global exponential stability. -/
@[powerlib_foundation, aesop safe apply] theorem globallyExponentiallyStable_of_isHurwitz
    {A : Matrix (Fin n) (Fin n) ℝ} (e : ℝⁿ) (hA : IsHurwitz A) :
    Flow.GloballyExponentiallyStable (affineLinearVectorField A e) e :=
  globallyExponentiallyStable_of_locallyExponentiallyStable
    (locallyExponentiallyStable_of_isHurwitz e hA)

/-! ## Non-decaying eigenmodes -/

/-- One real component (`part = re` or `im`) of the complex eigenmode `t ↦ e^{μ t} v`. -/
def eigenmode (part : ℂ →L[ℝ] ℝ) (μ : ℂ) (v : Fin n → ℂ) (t : ℝ) : ℝⁿ :=
  WithLp.toLp 2 fun j => part (Complex.exp (μ * t) * v j)

@[powerlib_foundation] theorem eigen_component_hasDerivAt (A : Matrix (Fin n) (Fin n) ℝ)
    {μ : ℂ} {v : Fin n → ℂ} (heig : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) (t : ℝ) (j : Fin n) :
    HasDerivAt (fun s : ℝ => Complex.exp (μ * s) * v j)
      (∑ k, (A j k : ℂ) * (Complex.exp (μ * t) * v k)) t := by
  have hcoe : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have hexp := ((hcoe.const_mul μ).cexp).mul_const (v j)
  convert hexp using 1
  have hj := congrFun heig j
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.coe_algebraMap,
    Pi.smul_apply, smul_eq_mul] at hj
  calc ∑ k, (A j k : ℂ) * (Complex.exp (μ * t) * v k)
      = Complex.exp (μ * t) * ∑ k, (A j k : ℂ) * v k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by rw [hj]; ring

@[powerlib_foundation] theorem eigenmode_hasDerivAt (A : Matrix (Fin n) (Fin n) ℝ) {μ : ℂ}
    {v : Fin n → ℂ} (heig : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v) (part : ℂ →L[ℝ] ℝ)
    (hpart : ∀ (a : ℝ) (z : ℂ), part ((a : ℂ) * z) = a * part z) (t : ℝ) :
    HasDerivAt (eigenmode part μ v) (op A (eigenmode part μ v t)) t := by
  have hcomp : HasDerivAt (fun s : ℝ => fun j => part (Complex.exp (μ * s) * v j))
      (A *ᵥ fun j => part (Complex.exp (μ * t) * v j)) t := by
    refine hasDerivAt_pi.2 fun j => ?_
    have h := part.hasFDerivAt.comp_hasDerivAt t (eigen_component_hasDerivAt A heig t j)
    convert h using 1 <;> first | rfl | simp [Matrix.mulVec, dotProduct, map_sum, hpart]
  have h := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.hasFDerivAt.comp_hasDerivAt
    t hcomp
  convert h using 1 <;> rfl

@[powerlib_foundation] theorem eigenmode_norm_sq (μ : ℂ) (v : Fin n → ℂ) (t : ℝ) :
    ‖eigenmode Complex.reCLM μ v t‖ ^ 2 + ‖eigenmode Complex.imCLM μ v t‖ ^ 2 =
      Real.exp (μ.re * t) ^ 2 * ∑ j, Complex.normSq (v j) := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hexp : Complex.normSq (Complex.exp (μ * t)) = Real.exp (μ.re * t) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    simp [Complex.mul_re]
  simp only [eigenmode, PiLp.toLp_apply, Complex.reCLM_apply, Complex.imCLM_apply]
  rw [← hexp, ← Complex.normSq_mul, Complex.normSq_apply]
  ring

/-- A non-decaying eigenmode rules out local asymptotic stability: local asymptotic stability of
the affine linear field forces Hurwitz. -/
@[powerlib_foundation] theorem isHurwitz_of_localAsymptoticStable
    {A : Matrix (Fin n) (Fin n) ℝ} {e : ℝⁿ}
    (h : LocalAsymptoticStable (affineLinearVectorField A e) e) : IsHurwitz A := by
  obtain ⟨-, c, hc, hconv⟩ := h
  intro μ v hv heig
  by_contra hμ
  have hre : 0 ≤ μ.re := by simpa using not_lt.mp hμ
  have hN : 0 < ∑ j, Complex.normSq (v j) := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
    exact Finset.sum_pos' (fun k _ => Complex.normSq_nonneg _)
      ⟨j, Finset.mem_univ _, Complex.normSq_pos.mpr hj⟩
  set N := ∑ j, Complex.normSq (v j)
  set ε : ℝ := c / (2 * (N + 1)) with hε_def
  have hε : 0 < ε := by positivity
  have hεeq : ε * (2 * (N + 1)) = c := by
    rw [hε_def]
    field_simp
  have hcurve : ∀ part : ℂ →L[ℝ] ℝ, (∀ (a : ℝ) (z : ℂ), part ((a : ℂ) * z) = a * part z) →
      IsIntegralCurveOn (fun t => e + ε • eigenmode part μ v t)
        (fun _ y => affineLinearVectorField A e y) (Ici 0) := by
    intro part hpart t _
    have h := ((eigenmode_hasDerivAt A heig part hpart t).const_smul ε).const_add e
    convert h.hasDerivWithinAt using 1
    simp [affine_apply, map_smul]
  have hsq : ∀ t, ‖(e + ε • eigenmode Complex.reCLM μ v t) - e‖ ^ 2 +
      ‖(e + ε • eigenmode Complex.imCLM μ v t) - e‖ ^ 2 =
        ε ^ 2 * (Real.exp (μ.re * t) ^ 2 * N) := by
    intro t
    rw [add_sub_cancel_left, add_sub_cancel_left, norm_smul, norm_smul,
      Real.norm_of_nonneg hε.le, mul_pow, mul_pow, ← mul_add, eigenmode_norm_sq]
  have hstart : ∀ part ∈ ({Complex.reCLM, Complex.imCLM} : Set (ℂ →L[ℝ] ℝ)),
      ‖(e + ε • eigenmode part μ v 0) - e‖ < c := by
    have h0 := hsq 0
    simp only [mul_zero, Real.exp_zero, one_pow, one_mul] at h0
    have hlt : ε ^ 2 * N < c ^ 2 := by
      rw [← hεeq]
      have hε2 : 0 < ε ^ 2 := by positivity
      nlinarith [mul_pos hε2 hN, mul_pos hε2 (mul_pos hN hN)]
    intro part hpart
    apply lt_of_pow_lt_pow_left₀ 2 hc.le
    rcases hpart with rfl | rfl
    · nlinarith [sq_nonneg ‖(e + ε • eigenmode Complex.imCLM μ v 0) - e‖]
    · nlinarith [sq_nonneg ‖(e + ε • eigenmode Complex.reCLM μ v 0) - e‖]
  have hre_t := hconv 0 _ (hcurve Complex.reCLM (by simp)) (hstart _ (by simp))
  have him_t := hconv 0 _ (hcurve Complex.imCLM (by simp)) (hstart _ (by simp))
  have hlim : Tendsto (fun t => ‖(e + ε • eigenmode Complex.reCLM μ v t) - e‖ ^ 2 +
      ‖(e + ε • eigenmode Complex.imCLM μ v t) - e‖ ^ 2) atTop (𝓝 0) := by
    have h1 := (tendsto_iff_norm_sub_tendsto_zero.mp hre_t).pow 2
    have h2 := (tendsto_iff_norm_sub_tendsto_zero.mp him_t).pow 2
    simpa using h1.add h2
  have hpos : 0 < ε ^ 2 * N := by positivity
  obtain ⟨t, ht, hsmall⟩ :=
    ((eventually_ge_atTop (0 : ℝ)).and (hlim.eventually (gt_mem_nhds hpos))).exists
  rw [hsq] at hsmall
  have hgrow : 1 ≤ Real.exp (μ.re * t) ^ 2 :=
    one_le_pow₀ (Real.one_le_exp_iff.mpr (mul_nonneg hre ht))
  nlinarith

/-! ## The hub -/

/-- For the affine linear field of `A`, every attractive sentence holds at the centre exactly
when `A` is Hurwitz. -/
@[powerlib_foundation] theorem holds_iff_isHurwitz {A : Matrix (Fin n) (Fin n) ℝ} (e : ℝⁿ)
    {P : Flow.Property} (hP : P.Attractive) :
    P.holds (affineLinearVectorField A e) e ↔ IsHurwitz A :=
  ⟨fun h => isHurwitz_of_localAsymptoticStable (Flow.Property.localAsymptoticStable hP h),
    fun hA => (globallyExponentiallyStable_of_isHurwitz e hA).holds hP⟩

/-- Hurwitz gives every attractive sentence. -/
@[powerlib_foundation, aesop unsafe 80% apply] theorem holds_of_isHurwitz
    {A : Matrix (Fin n) (Fin n) ℝ} (e : ℝⁿ) {P : Flow.Property} (hP : P.Attractive)
    (hA : IsHurwitz A) : P.holds (affineLinearVectorField A e) e :=
  (holds_iff_isHurwitz e hP).mpr hA

/-- Hurwitz gives global asymptotic stability, with a solution through every state. -/
@[powerlib_foundation, aesop safe apply] theorem globallyAsymptoticallyStable_of_isHurwitz
    {A : Matrix (Fin n) (Fin n) ℝ} (e : ℝⁿ) (hA : IsHurwitz A) :
    Flow.GloballyAsymptoticallyStable (affineLinearVectorField A e) e :=
  (globallyExponentiallyStable_of_isHurwitz e hA).globallyAsymptoticallyStable

/-- Hurwitz gives local asymptotic stability. -/
@[powerlib_foundation, aesop safe apply] theorem localAsymptoticStable_of_isHurwitz
    {A : Matrix (Fin n) (Fin n) ℝ} (e : ℝⁿ) (hA : IsHurwitz A) :
    LocalAsymptoticStable (affineLinearVectorField A e) e :=
  Flow.locallyExponentiallyStable_localAsymptoticStable
    (locallyExponentiallyStable_of_isHurwitz e hA)

/-- Hurwitz gives Lyapunov stability. -/
@[powerlib_foundation, aesop unsafe 50% apply]
theorem lyapunovStable_of_isHurwitz {A : Matrix (Fin n) (Fin n) ℝ}
    (e : ℝⁿ) (hA : IsHurwitz A) : LyapunovStable (affineLinearVectorField A e) e :=
  (globallyExponentiallyStable_of_isHurwitz e hA).lyapunovStable

/-- An eigenvalue in the open right half plane gives instability (LeanForControl). -/
@[powerlib_foundation] theorem unstable_of_eigenvalue {A : Matrix (Fin n) (Fin n) ℝ} (e : ℝⁿ)
    {μ : ℂ} {v : Fin n → ℂ} (hv : v ≠ 0) (heig : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v)
    (hμ : 0 < μ.re) : Unstable (affineLinearVectorField A e) e :=
  unstable_affineLinear_of_eigenvalue_re_pos A e μ v hv heig hμ

/-! ## Sampling

At integer multiples of a horizon the solutions of a Hurwitz field contract by a fixed factor
(LeanForControl's spectral-radius argument, measured in the Frobenius norm). -/

section Sampling

open scoped Matrix.Norms.Frobenius

/-- Hurwitz gives a positive integer horizon whose transition matrix has Frobenius norm below one
(LeanForControl). -/
@[powerlib_foundation] theorem contractive_block {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsHurwitz A) :
    ∃ k : ℕ, 0 < k ∧ ‖exp ((k : ℝ) • A)‖ < 1 :=
  hA.exists_norm_exp_nat_smul_lt_one

/-- The Frobenius norm bounds the action on states. -/
@[powerlib_foundation] theorem norm_op_apply_le (M : Matrix (Fin n) (Fin n) ℝ) (x : ℝⁿ) :
    ‖op M x‖ ≤ ‖M‖ * ‖x‖ :=
  calc ‖op M x‖ = ‖replicateCol (Fin 1) (M *ᵥ x.ofLp)‖ :=
        (frobenius_norm_replicateCol (ι := Fin 1) (M *ᵥ x.ofLp)).symm
    _ = ‖M * replicateCol (Fin 1) x.ofLp‖ := by rw [replicateCol_mulVec]
    _ ≤ ‖M‖ * ‖replicateCol (Fin 1) x.ofLp‖ := frobenius_norm_mul _ _
    _ = ‖M‖ * ‖x‖ := congrArg (‖M‖ * ·) (frobenius_norm_replicateCol (ι := Fin 1) x.ofLp)

/-- The exponential of a matrix acts on states as the exponential of its operator. -/
@[powerlib_foundation] theorem op_exp (M : Matrix (Fin n) (Fin n) ℝ) : op (exp M) = exp (op M) :=
  map_exp (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ))
    ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap
      |>.continuous_of_finiteDimensional) M

/-- Hurwitz gives sampled contraction of the affine linear field: over an integer horizon the
transition matrix has Frobenius norm below one. -/
@[powerlib_foundation] theorem sampledContraction_of_isHurwitz {A : Matrix (Fin n) (Fin n) ℝ}
    (e : ℝⁿ) (hA : IsHurwitz A) : Flow.SampledContraction (affineLinearVectorField A e) e := by
  obtain ⟨k, hk, hlt⟩ := contractive_block hA
  refine ⟨k, hk, _, hlt, fun t₀ φ hφ => ?_⟩
  have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [trajectory_eq_solution hφ (t₀ + k) ⟨by linarith, le_rfl⟩, solution,
    add_sub_cancel_left, add_sub_cancel_left, show (k : ℝ) • op A = op ((k : ℝ) • A) from
      (map_smul _ _ _).symm, ← op_exp]
  exact norm_op_apply_le _ _

end Sampling

/-- A non-decaying eigenmode does not contract: sampled contraction of the affine linear field
forces Hurwitz. -/
@[powerlib_foundation] theorem isHurwitz_of_sampledContraction {A : Matrix (Fin n) (Fin n) ℝ}
    {e : ℝⁿ} (h : Flow.SampledContraction (affineLinearVectorField A e) e) : IsHurwitz A := by
  obtain ⟨k, hk, c, hc, hcon⟩ := h
  intro μ v hv heig
  by_contra hμ
  have hre : 0 ≤ μ.re := by simpa using not_lt.mp hμ
  have hN : 0 < ∑ j, Complex.normSq (v j) := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
    exact Finset.sum_pos' (fun k _ => Complex.normSq_nonneg _)
      ⟨j, Finset.mem_univ _, Complex.normSq_pos.mpr hj⟩
  set N := ∑ j, Complex.normSq (v j)
  have hcurve : ∀ part : ℂ →L[ℝ] ℝ, (∀ (a : ℝ) (z : ℂ), part ((a : ℂ) * z) = a * part z) →
      IsTrajectoryOn (fun t => e + eigenmode part μ v t) (affineLinearVectorField A e) 0
        (0 + k) := by
    intro part hpart t _
    have h := (eigenmode_hasDerivAt A heig part hpart t).const_add e
    convert h.hasDerivWithinAt using 1
    simp [affine_apply]
  have h₁ := hcon 0 _ (hcurve Complex.reCLM (by simp))
  have h₂ := hcon 0 _ (hcurve Complex.imCLM (by simp))
  simp only [add_sub_cancel_left, zero_add] at h₁ h₂
  have hk₀ := eigenmode_norm_sq μ v 0
  have hkk := eigenmode_norm_sq μ v k
  simp only [mul_zero, Real.exp_zero, one_pow, one_mul] at hk₀
  have hgrow : 1 ≤ Real.exp (μ.re * k) ^ 2 :=
    one_le_pow₀ (Real.one_le_exp_iff.mpr (mul_nonneg hre (Nat.cast_nonneg k)))
  have a0 := norm_nonneg (eigenmode Complex.reCLM μ v 0)
  have b0 := norm_nonneg (eigenmode Complex.imCLM μ v 0)
  have ak := norm_nonneg (eigenmode Complex.reCLM μ v k)
  have bk := norm_nonneg (eigenmode Complex.imCLM μ v k)
  rcases lt_or_ge c 0 with hc0 | hc0
  · have hz₁ : ‖eigenmode Complex.reCLM μ v k‖ = 0 :=
      le_antisymm (h₁.trans (mul_nonpos_of_nonpos_of_nonneg hc0.le a0)) ak
    have hz₂ : ‖eigenmode Complex.imCLM μ v k‖ = 0 :=
      le_antisymm (h₂.trans (mul_nonpos_of_nonpos_of_nonneg hc0.le b0)) bk
    rw [hz₁, hz₂] at hkk
    nlinarith
  · have hs₁ := pow_le_pow_left₀ ak h₁ 2
    have hs₂ := pow_le_pow_left₀ bk h₂ 2
    have hc2 : c ^ 2 < 1 := by nlinarith
    nlinarith

/-- For the affine linear field, sampled contraction holds at the centre exactly when the matrix
is Hurwitz. -/
@[powerlib_foundation] theorem sampledContraction_iff_isHurwitz {A : Matrix (Fin n) (Fin n) ℝ}
    (e : ℝⁿ) : Flow.SampledContraction (affineLinearVectorField A e) e ↔ IsHurwitz A :=
  ⟨isHurwitz_of_sampledContraction, sampledContraction_of_isHurwitz e⟩

/-- A conserved energy excludes Hurwitz on a nontrivial state space: every solution of a Hurwitz
field converges. -/
@[powerlib_foundation] theorem not_isHurwitz_of_conservative (hn : 0 < n)
    {A : Matrix (Fin n) (Fin n) ℝ} {e : ℝⁿ}
    (h : Flow.Conservative (affineLinearVectorField A e) e) : ¬ IsHurwitz A :=
  fun hA => h.not_localAsymptoticStable hn (forwardComplete A e)
    (localAsymptoticStable_of_isHurwitz e hA)

end powerlib.Linear
