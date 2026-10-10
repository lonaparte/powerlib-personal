import theorem.Linear.Plant

/-! # The linear stability hub

For the affine linear field of `A` centred at `e`, every attractive sentence of the Flow
semantics — local or global, asymptotic or exponential — holds at `e` exactly when `A` is
Hurwitz. This is the one place where linear stability is decided; every linear family inherits
it through its plant map.

* Hurwitz ⇒ local exponential stability: LeanForControl's linearization theorem, applied to the
  field itself.
* Local ⇒ global exponential stability: the field is linear about `e`, so solution segments scale.
* Forward completeness: the matrix exponential.
* Local asymptotic stability ⇒ Hurwitz: a real eigenmode with `Re μ ≥ 0` does not decay. -/

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
@[powerlib_foundation] theorem locallyExponentiallyStable_of_isHurwitz
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
@[powerlib_foundation] theorem globallyExponentiallyStable_of_isHurwitz
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

/-- Hurwitz gives Lyapunov stability. -/
@[powerlib_foundation] theorem lyapunovStable_of_isHurwitz {A : Matrix (Fin n) (Fin n) ℝ}
    (e : ℝⁿ) (hA : IsHurwitz A) : LyapunovStable (affineLinearVectorField A e) e :=
  (globallyExponentiallyStable_of_isHurwitz e hA).lyapunovStable

/-- An eigenvalue in the open right half plane gives instability (LeanForControl). -/
@[powerlib_foundation] theorem unstable_of_eigenvalue {A : Matrix (Fin n) (Fin n) ℝ} (e : ℝⁿ)
    {μ : ℂ} {v : Fin n → ℂ} (hv : v ≠ 0) (heig : A.map (algebraMap ℝ ℂ) *ᵥ v = μ • v)
    (hμ : 0 < μ.re) : Unstable (affineLinearVectorField A e) e :=
  unstable_affineLinear_of_eigenvalue_re_pos A e μ v hv heig hμ

end powerlib.Linear
