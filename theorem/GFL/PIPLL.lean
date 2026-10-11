import theorem.Criteria.Hurwitz2

/-! # PI phase-locked loop with a general phase-detector characteristic

Model boundary (domain module).
* State `x : State 2 = EuclideanSpace ℝ (Fin 2)`, coordinates in this order:
  `x 0 = θ` (phase offset `θ_e = θ̂_g − θ_g`, PLL estimate minus grid angle, swing-style sign of
  work-sync `conventions.md` §D5), `x 1 = η` (state of the PI integrator, `η̇ = h(θ)`).
* Continuous-time autonomous vector field
  `θ̇ = K_p h(θ) + K_i η − δω`, `η̇ = h(θ)` (`piPLLField h Kp Ki δω`).
  `h : ℝ → ℝ` is an arbitrary phase-detector characteristic (the PLL input `v_q^c` written as a
  function of `θ` after all faster dynamics have been eliminated); `K_p`, `K_i` are the PI gains
  (any real numbers unless a theorem says otherwise); `δω = ω_g − ω_s` is a constant grid-frequency
  offset (constant input; no time-varying forcing).
* Direction convention: none is needed at this level — `h` already contains the sign of the
  measured `q`-axis voltage. The standard GFL derivation (`T-gfl-dynamics` §1.7) uses the
  IN-positive current convention to build `h`.
* Excluded: the derivation of `h` (time-scale reduction, Tikhonov error), current loop, LC filter,
  line dynamics, outer loops, saturation, delay, PWM, measurement filters, noise. The stochastic
  extension is not modelled.
* Level: equilibrium set (all `δω`), and local behaviour at an equilibrium through the
  linearization theorems of `theorem/Hurwitz.lean` (Jacobian computed with `fderiv` from the
  field itself). Local results need `h` to be `C¹` on all of `ℝ` (global `ContDiff ℝ 1`), because
  the powerlib linearization wrappers require a globally `C¹` field.

Results.
* Equilibria (`K_i ≠ 0`): exactly `{(θ*, δω / K_i) : h(θ*) = 0}`, for **every** constant `δω`.
  Hence existence of an equilibrium does not depend on `δω`.
* Jacobian at any point: `[[K_p g, K_i], [g, 0]]` with `g = h'(θ)`; trace `K_p g`, determinant
  `−K_i g` (so `K_i · tr + K_p · det = 0`).
* `K_p, K_i > 0`: `h'(θ*) < 0` ⇒ local exponential stability; `h'(θ*) > 0` ⇒ instability
  (saddle); `h'(θ*) = 0` ⇒ the Jacobian is a nonzero nilpotent matrix (loss of hyperbolicity;
  linearization decides nothing).

Source: work-sync `theory/T-gfl-dynamics.md` §1.7 (boxed 2D ODE), §1.9 (equilibria), §1.10
(Jacobian and local stability), §1.12 (`Σ_FD`); `theory/T-bogdanov-takens-bifurcation.md` §1.6;
`theory/T-gfl-ph.md` (1.1); `projects/vsc-stochastic-stability/notes/concepts/
equilibria-and-bifurcation.md` §1, §3 (written with `δω = 0`).

Sign conventions of the sources. `T-gfl-dynamics` §1.7, `T-gfl-ph` (1.1) and this module use
`θ̇ = K_p h + K_i η − δω`. The vsc note and `T-bogdanov-takens` §1.6 drop `δω` (take `δω = 0`).
`T-gfl-dynamics` §1.12 writes `θ̇ = −K_p h − K_i η − δω`; with `η̇ = h` that field is this one with
`h` replaced by `−h` and `η` by `−η` (so its stability condition would read `h' > 0`); §1.12 is
inconsistent with §1.7–§1.10 and this module follows §1.7.

Correction (`T-gfl-dynamics` §1.12, `Σ_FD`, and §1.14 region D): the note claims that when
`|δω| > K_p max |h|` "the system loses all equilibria". This is false for the reduced model of
§1.7: the PI integrator absorbs any constant frequency offset, the equilibria are
`(θ*, δω / K_i)` with the same `θ*` for every `δω`, and their local stability does not depend on
`δω`. `piPLLField_eq_zero_iff`, `piPLL_exists_equilibrium_iff` and
`piPLL_frequencyDriftBoundary_refuted` (an explicit counterexample with a locally exponentially
stable equilibrium) formalize this. The surface `Σ_FD` does not exist in this model.
-/

noncomputable section
namespace powerlib.GFL
open Matrix
open powerlib.Dynamics (State)

/-! ## The model -/

/-- The state `(θ, η)` as an element of `State 2`. -/
def piPLLState (θ η : ℝ) : State 2 := WithLp.toLp 2 ![θ, η]

/-- PI-PLL vector field with phase-detector characteristic `h`:
`θ̇ = K_p h(θ) + K_i η − δω`, `η̇ = h(θ)`; coordinates `x 0 = θ`, `x 1 = η`. -/
def piPLLField (h : ℝ → ℝ) (Kp Ki δω : ℝ) (x : State 2) : State 2 :=
  WithLp.toLp 2 ![Kp * h (x 0) + Ki * x 1 - δω, h (x 0)]

/-- The Jacobian matrix `[[K_p g, K_i], [g, 0]]`, `g = h'(θ)`. -/
def piPLLJacobian (Kp Ki g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Kp * g, Ki; g, 0]

@[simp, powerlib_foundation] theorem piPLLField_apply_zero (h : ℝ → ℝ) (Kp Ki δω : ℝ)
    (x : State 2) : piPLLField h Kp Ki δω x 0 = Kp * h (x 0) + Ki * x 1 - δω := rfl

@[simp, powerlib_foundation] theorem piPLLField_apply_one (h : ℝ → ℝ) (Kp Ki δω : ℝ)
    (x : State 2) : piPLLField h Kp Ki δω x 1 = h (x 0) := rfl

@[simp, powerlib_foundation] theorem piPLLState_apply_zero (θ η : ℝ) :
    piPLLState θ η 0 = θ := rfl

@[simp, powerlib_foundation] theorem piPLLState_apply_one (θ η : ℝ) :
    piPLLState θ η 1 = η := rfl

/-- Two points of `State 2` are equal iff both coordinates agree. -/
@[powerlib_foundation] theorem state_two_ext_iff {x y : State 2} :
    x = y ↔ x 0 = y 0 ∧ x 1 = y 1 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i
    · exact h0
    · exact h1

@[simp, powerlib_foundation] theorem piPLLState_coords (x : State 2) :
    piPLLState (x 0) (x 1) = x :=
  state_two_ext_iff.mpr ⟨rfl, rfl⟩

@[powerlib_foundation] theorem piPLLState_eq_iff {θ η θ' η' : ℝ} :
    piPLLState θ η = piPLLState θ' η' ↔ θ = θ' ∧ η = η' := by
  rw [state_two_ext_iff]
  simp

/-! ## Smoothness and Jacobian (derived from the field) -/

/-- The field is `C¹` on all of `State 2` when `h` is `C¹` on `ℝ`. -/
@[powerlib_foundation] theorem contDiff_piPLLField {h : ℝ → ℝ} {Kp Ki δω : ℝ}
    (hh : ContDiff ℝ 1 h) : ContDiff ℝ 1 (piPLLField h Kp Ki δω) := by
  have hc0 : ContDiff ℝ 1 (fun y : State 2 => y 0) :=
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : State 2 →L[ℝ] ℝ).contDiff
  have hc1 : ContDiff ℝ 1 (fun y : State 2 => y 1) :=
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : State 2 →L[ℝ] ℝ).contDiff
  have hs : ContDiff ℝ 1 (fun y : State 2 => ![Kp * h (y 0) + Ki * y 1 - δω, h (y 0)]) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · show ContDiff ℝ 1 (fun y : State 2 => Kp * h (y 0) + Ki * y 1 - δω)
      exact ((contDiff_const.mul (hh.comp hc0)).add (contDiff_const.mul hc1)).sub contDiff_const
    · show ContDiff ℝ 1 (fun y : State 2 => h (y 0))
      exact hh.comp hc0
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.contDiff.comp hs

/-- Fréchet derivative of the field at any point `x`, from `h'(x 0) = g`. -/
@[powerlib_foundation] theorem hasFDerivAt_piPLLField {h : ℝ → ℝ} {Kp Ki δω g : ℝ}
    {x : State 2} (hh : HasDerivAt h g (x 0)) :
    HasFDerivAt (piPLLField h Kp Ki δω)
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (piPLLJacobian Kp Ki g)) x := by
  have h0 : HasFDerivAt (fun y : State 2 => y 0)
      (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : State 2 →L[ℝ] ℝ) x :=
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : State 2 →L[ℝ] ℝ).hasFDerivAt
  have h1 : HasFDerivAt (fun y : State 2 => y 1)
      (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : State 2 →L[ℝ] ℝ) x :=
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : State 2 →L[ℝ] ℝ).hasFDerivAt
  have hc : HasFDerivAt (fun y : State 2 => h (y 0))
      (g • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : State 2 →L[ℝ] ℝ)) x :=
    hh.comp_hasFDerivAt x h0
  have hF0 := ((hc.const_mul Kp).add (h1.const_mul Ki)).sub_const δω
  have hG : HasFDerivAt (fun y : State 2 => ![Kp * h (y 0) + Ki * y 1 - δω, h (y 0)])
      (ContinuousLinearMap.pi
        ![Kp • (g • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : State 2 →L[ℝ] ℝ))
          + Ki • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : State 2 →L[ℝ] ℝ),
          g • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : State 2 →L[ℝ] ℝ)]) x := by
    rw [hasFDerivAt_pi]
    intro i
    fin_cases i
    · simpa using hF0
    · simpa using hc
  have hE :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.hasFDerivAt.comp x hG
  have hfun : piPLLField h Kp Ki δω =
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm ∘
        (fun y : State 2 => ![Kp * h (y 0) + Ki * y 1 - δω, h (y 0)]) := rfl
  rw [hfun]
  refine hE.congr_fderiv ?_
  ext v i
  rw [Matrix.ofLp_toEuclideanCLM]
  fin_cases i
  · simp [piPLLJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp [piPLLJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The Jacobian of the field (as computed by `fderiv`). -/
@[powerlib_foundation] theorem fderiv_piPLLField {h : ℝ → ℝ} {Kp Ki δω g : ℝ} {x : State 2}
    (hh : HasDerivAt h g (x 0)) :
    fderiv ℝ (piPLLField h Kp Ki δω) x =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (piPLLJacobian Kp Ki g) :=
  (hasFDerivAt_piPLLField hh).fderiv

@[simp, powerlib_foundation] theorem piPLLJacobian_trace (Kp Ki g : ℝ) :
    (piPLLJacobian Kp Ki g).trace = Kp * g := by
  simp [piPLLJacobian, Matrix.trace_fin_two]

@[simp, powerlib_foundation] theorem piPLLJacobian_det (Kp Ki g : ℝ) :
    (piPLLJacobian Kp Ki g).det = -(Ki * g) := by
  simp [piPLLJacobian, Matrix.det_fin_two]

/-- Structural identity: trace and determinant are both proportional to `g`,
`K_i · tr J + K_p · det J = 0` for every `g`. -/
@[powerlib_foundation] theorem piPLLJacobian_trace_det_relation (Kp Ki g : ℝ) :
    Ki * (piPLLJacobian Kp Ki g).trace + Kp * (piPLLJacobian Kp Ki g).det = 0 := by
  simp only [piPLLJacobian_trace, piPLLJacobian_det]
  ring

/-- Hurwitz test of the Jacobian: `IsHurwitz ↔ K_p g < 0 ∧ K_i g < 0`. -/
@[powerlib_foundation] theorem piPLLJacobian_isHurwitz_iff (Kp Ki g : ℝ) :
    LinearSystems.IsHurwitz (piPLLJacobian Kp Ki g) ↔ Kp * g < 0 ∧ Ki * g < 0 := by
  rw [Criteria.isHurwitz_fin_two_iff, piPLLJacobian_trace, piPLLJacobian_det, neg_pos]

/-- With positive gains the Jacobian is Hurwitz exactly when `g = h'(θ*) < 0`. -/
@[powerlib_foundation] theorem piPLLJacobian_isHurwitz_iff_of_pos {Kp Ki : ℝ} (hKp : 0 < Kp)
    (hKi : 0 < Ki) (g : ℝ) :
    LinearSystems.IsHurwitz (piPLLJacobian Kp Ki g) ↔ g < 0 := by
  rw [piPLLJacobian_isHurwitz_iff]
  constructor
  · rintro ⟨h1, _⟩
    by_contra hg
    push Not at hg
    nlinarith
  · intro hg
    exact ⟨mul_neg_of_pos_of_neg hKp hg, mul_neg_of_pos_of_neg hKi hg⟩

/-- At `g = 0` the Jacobian is `[[0, K_i], [0, 0]]`, which squares to zero. -/
@[powerlib_foundation] theorem piPLLJacobian_zero_sq (Kp Ki : ℝ) :
    (piPLLJacobian Kp Ki 0) ^ 2 = 0 := by
  rw [Criteria.sq_eq_zero_iff_trace_det_eq_zero_fin_two]
  simp

@[powerlib_foundation] theorem piPLLJacobian_zero_ne_zero {Kp Ki : ℝ} (hKi : Ki ≠ 0) :
    piPLLJacobian Kp Ki 0 ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [piPLLJacobian] at this
  exact hKi this

@[powerlib_foundation] theorem piPLLJacobian_zero_isNilpotent (Kp Ki : ℝ) :
    IsNilpotent (piPLLJacobian Kp Ki 0) :=
  ⟨2, piPLLJacobian_zero_sq Kp Ki⟩

/-- Every (complex) eigenvalue of the `g = 0` Jacobian is zero. -/
@[powerlib_foundation] theorem piPLLJacobian_zero_eigenvalue_eq_zero (Kp Ki : ℝ) {μ : ℂ}
    {v : Fin 2 → ℂ} (hv : v ≠ 0)
    (heig : (piPLLJacobian Kp Ki 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v) : μ = 0 := by
  set A := (piPLLJacobian Kp Ki 0).map (algebraMap ℝ ℂ) with hA
  have hsq : A * A = 0 := by
    have h2 := piPLLJacobian_zero_sq Kp Ki
    rw [pow_two] at h2
    rw [hA, ← Matrix.map_mul, h2, Matrix.map_zero _ (map_zero _)]
  have h2 : A *ᵥ (A *ᵥ v) = (μ * μ) • v := by
    rw [heig, Matrix.mulVec_smul, heig, smul_smul]
  rw [Matrix.mulVec_mulVec, hsq, Matrix.zero_mulVec] at h2
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have := congrFun h2 i
  simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this
  have hμμ : μ * μ = 0 := by
    rcases mul_eq_zero.mp this.symm with h | h
    · exact h
    · exact absurd h hi
  exact mul_self_eq_zero.mp hμμ

/-! ## Equilibria -/

/-- Equilibrium equations: for `K_i ≠ 0`, `f(x) = 0 ↔ h(θ) = 0 ∧ η = δω / K_i`. -/
@[powerlib_domain] theorem piPLLField_eq_zero_iff {h : ℝ → ℝ} {Kp Ki δω : ℝ} (hKi : Ki ≠ 0)
    (x : State 2) : piPLLField h Kp Ki δω x = 0 ↔ h (x 0) = 0 ∧ x 1 = δω / Ki := by
  rw [state_two_ext_iff]
  simp only [piPLLField_apply_zero, piPLLField_apply_one, PiLp.zero_apply]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h1, ?_⟩
    rw [h1, mul_zero, zero_add, sub_eq_zero] at h0
    field_simp
    linarith
  · rintro ⟨h0, h1⟩
    refine ⟨?_, h0⟩
    rw [h0, h1]
    field_simp
    ring

/-- `K_i = 0` (no integrator): equilibria exist only for `δω = 0`. -/
@[powerlib_domain] theorem piPLLField_eq_zero_iff_of_Ki_eq_zero {h : ℝ → ℝ} {Kp δω : ℝ}
    (x : State 2) : piPLLField h Kp 0 δω x = 0 ↔ h (x 0) = 0 ∧ δω = 0 := by
  rw [state_two_ext_iff]
  simp only [piPLLField_apply_zero, piPLLField_apply_one, PiLp.zero_apply]
  constructor
  · rintro ⟨h0, h1⟩
    rw [h1] at h0
    exact ⟨h1, by linarith⟩
  · rintro ⟨h0, h1⟩
    rw [h0, h1]
    exact ⟨by ring, rfl⟩

@[powerlib_domain] theorem piPLL_isEquilibrium_iff {h : ℝ → ℝ} {Kp Ki δω : ℝ} (hKi : Ki ≠ 0)
    (θ η : ℝ) :
    Dynamics.IsEquilibrium (piPLLField h Kp Ki δω) (piPLLState θ η) ↔ h θ = 0 ∧ η = δω / Ki :=
  piPLLField_eq_zero_iff hKi (piPLLState θ η)

/-- The equilibrium set, for every constant `δω` (`K_i ≠ 0`):
`{x | f x = 0} = {(θ*, δω / K_i) : h(θ*) = 0}`. -/
@[powerlib_domain] theorem piPLL_equilibria_eq {h : ℝ → ℝ} {Kp Ki δω : ℝ} (hKi : Ki ≠ 0) :
    {x : State 2 | piPLLField h Kp Ki δω x = 0} =
      (fun θ => piPLLState θ (δω / Ki)) '' {θ | h θ = 0} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, piPLLField_eq_zero_iff hKi]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨x 0, h0, by rw [← h1, piPLLState_coords]⟩
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨hθ, rfl⟩

/-- Existence of an equilibrium does not depend on the constant frequency offset `δω`. -/
@[powerlib_domain] theorem piPLL_exists_equilibrium_iff {h : ℝ → ℝ} {Kp Ki δω : ℝ}
    (hKi : Ki ≠ 0) : (∃ x, piPLLField h Kp Ki δω x = 0) ↔ ∃ θ, h θ = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x 0, ((piPLLField_eq_zero_iff hKi x).mp hx).1⟩
  · rintro ⟨θ, hθ⟩
    exact ⟨piPLLState θ (δω / Ki), (piPLLField_eq_zero_iff hKi _).mpr ⟨hθ, rfl⟩⟩

/-! ## Local stability at an equilibrium -/

/-- General form: `K_p g < 0` and `K_i g < 0` at a zero `θ*` of `h` (with `g = h'(θ*)`) give
local exponential stability of `(θ*, δω / K_i)`. -/
@[powerlib_domain] theorem piPLL_locallyExponentiallyStable_of_mul_neg {h : ℝ → ℝ}
    {Kp Ki δω θ g : ℝ} (hh : ContDiff ℝ 1 h) (hzero : h θ = 0) (hderiv : HasDerivAt h g θ)
    (hKpg : Kp * g < 0) (hKig : Ki * g < 0) :
    Dynamics.LocallyExponentiallyStable (piPLLField h Kp Ki δω) (piPLLState θ (δω / Ki)) := by
  have hKi : Ki ≠ 0 := by
    rintro rfl
    simp at hKig
  refine Criteria.locallyExponentiallyStable_of_jacobian_fin_two (piPLLJacobian Kp Ki g)
    (contDiff_piPLLField hh) ((piPLLField_eq_zero_iff hKi _).mpr ⟨hzero, rfl⟩)
    (fderiv_piPLLField hderiv) ?_ ?_
  · rw [piPLLJacobian_trace]
    exact hKpg
  · rw [piPLLJacobian_det]
    linarith

/-- `K_p, K_i > 0` and `h'(θ*) < 0`: the equilibrium `(θ*, δω / K_i)` is locally exponentially
stable, for every constant `δω`. -/
@[powerlib_domain] theorem piPLL_locallyExponentiallyStable {h : ℝ → ℝ} {Kp Ki δω θ g : ℝ}
    (hh : ContDiff ℝ 1 h) (hzero : h θ = 0) (hderiv : HasDerivAt h g θ) (hg : g < 0)
    (hKp : 0 < Kp) (hKi : 0 < Ki) :
    Dynamics.LocallyExponentiallyStable (piPLLField h Kp Ki δω) (piPLLState θ (δω / Ki)) :=
  piPLL_locallyExponentiallyStable_of_mul_neg hh hzero hderiv (mul_neg_of_pos_of_neg hKp hg)
    (mul_neg_of_pos_of_neg hKi hg)

/-- General saddle form: `K_i g > 0` at a zero `θ*` of `h` makes `(θ*, δω / K_i)` unstable
(`det J = −K_i g < 0`, a positive real eigenvalue). No sign condition on `K_p`. -/
@[powerlib_domain] theorem piPLL_unstable_of_mul_pos {h : ℝ → ℝ} {Kp Ki δω θ g : ℝ}
    (hh : ContDiff ℝ 1 h) (hzero : h θ = 0) (hderiv : HasDerivAt h g θ) (hKig : 0 < Ki * g) :
    Dynamics.Unstable (piPLLField h Kp Ki δω) (piPLLState θ (δω / Ki)) := by
  have hKi : Ki ≠ 0 := by
    rintro rfl
    simp at hKig
  refine Criteria.unstable_of_jacobian_det_neg_fin_two (piPLLJacobian Kp Ki g)
    (contDiff_piPLLField hh) ((piPLLField_eq_zero_iff hKi _).mpr ⟨hzero, rfl⟩)
    (fderiv_piPLLField hderiv) ?_
  rw [piPLLJacobian_det]
  linarith

/-- `K_i > 0` and `h'(θ*) > 0`: the equilibrium `(θ*, δω / K_i)` is unstable (saddle). -/
@[powerlib_domain] theorem piPLL_unstable {h : ℝ → ℝ} {Kp Ki δω θ g : ℝ}
    (hh : ContDiff ℝ 1 h) (hzero : h θ = 0) (hderiv : HasDerivAt h g θ) (hg : 0 < g)
    (hKi : 0 < Ki) :
    Dynamics.Unstable (piPLLField h Kp Ki δω) (piPLLState θ (δω / Ki)) :=
  piPLL_unstable_of_mul_pos hh hzero hderiv (mul_pos hKi hg)

/-- Positive trace: `K_p g > 0` at a zero of `h` (`K_i ≠ 0`) makes the equilibrium unstable. -/
@[powerlib_domain] theorem piPLL_unstable_of_trace_pos {h : ℝ → ℝ} {Kp Ki δω θ g : ℝ}
    (hh : ContDiff ℝ 1 h) (hzero : h θ = 0) (hderiv : HasDerivAt h g θ) (hKi : Ki ≠ 0)
    (hKpg : 0 < Kp * g) :
    Dynamics.Unstable (piPLLField h Kp Ki δω) (piPLLState θ (δω / Ki)) := by
  refine Criteria.unstable_of_jacobian_trace_pos_fin_two (piPLLJacobian Kp Ki g)
    (contDiff_piPLLField hh) ((piPLLField_eq_zero_iff hKi _).mpr ⟨hzero, rfl⟩)
    (fderiv_piPLLField hderiv) ?_
  rw [piPLLJacobian_trace]
  exact hKpg

/-- `h'(θ*) = 0` (`K_i ≠ 0`): the Jacobian of the field at the equilibrium `(θ*, δω / K_i)` is
the nonzero nilpotent matrix `[[0, K_i], [0, 0]]` — a double zero eigenvalue with a single Jordan
block. The equilibrium is not hyperbolic, and the linearization theorems decide nothing there.
This is a statement about the linearization only, not a stability conclusion. -/
@[powerlib_domain] theorem piPLL_jacobian_nilpotent_of_deriv_zero {h : ℝ → ℝ}
    {Kp Ki δω θ : ℝ} (hzero : h θ = 0) (hderiv : HasDerivAt h 0 θ) (hKi : Ki ≠ 0) :
    piPLLField h Kp Ki δω (piPLLState θ (δω / Ki)) = 0 ∧
      fderiv ℝ (piPLLField h Kp Ki δω) (piPLLState θ (δω / Ki)) =
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (piPLLJacobian Kp Ki 0) ∧
      piPLLJacobian Kp Ki 0 ≠ 0 ∧ (piPLLJacobian Kp Ki 0) ^ 2 = 0 ∧
      ¬ LinearSystems.IsHurwitz (piPLLJacobian Kp Ki 0) :=
  ⟨(piPLLField_eq_zero_iff hKi _).mpr ⟨hzero, rfl⟩, fderiv_piPLLField hderiv,
    piPLLJacobian_zero_ne_zero hKi, piPLLJacobian_zero_sq Kp Ki,
    by rw [piPLLJacobian_isHurwitz_iff]; simp⟩

/-! ## Refutation of the frequency-drift boundary `Σ_FD` -/

/-- `T-gfl-dynamics` §1.12 claims: if `|δω| > K_p max |h|`, the reduced PLL loses all
equilibria. Counterexample: `h = −sin`, `K_p = K_i = 1`, `|h| ≤ 1`, `δω = 2`; the point
`(0, 2)` is an equilibrium, and it is even locally exponentially stable. -/
@[powerlib_domain] theorem piPLL_frequencyDriftBoundary_refuted :
    ¬ (∀ (h : ℝ → ℝ) (Kp Ki δω M : ℝ), 0 < Kp → 0 < Ki → (∀ θ, |h θ| ≤ M) →
        Kp * M < |δω| → ¬ ∃ x, piPLLField h Kp Ki δω x = 0) := by
  intro H
  apply H (fun θ => -Real.sin θ) 1 1 2 1 one_pos one_pos
    (fun θ => by rw [abs_neg]; exact Real.abs_sin_le_one θ) (by norm_num)
  exact ⟨piPLLState 0 2, (piPLLField_eq_zero_iff one_ne_zero _).mpr ⟨by simp, by simp⟩⟩

/-- The equilibrium of the counterexample is locally exponentially stable although
`|δω| = 2 > K_p max |h| = 1`. -/
@[powerlib_domain] theorem piPLL_frequencyDriftBoundary_counterexample_stable :
    Dynamics.LocallyExponentiallyStable (piPLLField (fun θ => -Real.sin θ) 1 1 2)
      (piPLLState 0 (2 / 1)) := by
  refine piPLL_locallyExponentiallyStable (g := -1) Real.contDiff_sin.neg (by simp) ?_
    (by norm_num) one_pos one_pos
  have h := (Real.hasDerivAt_sin 0).neg
  rw [Real.cos_zero] at h
  exact h

end powerlib.GFL
