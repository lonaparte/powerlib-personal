import theorem.Criteria.Hurwitz2
import theorem.PhasePlane.Planar
import theorem.Linear.EigenMap

/-! # PI phase-locked loop with a general phase-detector characteristic: the static model

Static foundation of the PI-PLL model. This module contains the vector field, its Jacobian and
the equilibrium set; it states no behaviour. The behavioural (connection) conclusions are made in
`theorem/PLL/PIPLLFamily.lean`, through the family's system map.

Model boundary.
* State `x : ℝ² = EuclideanSpace ℝ (Fin 2)`, coordinates in this order:
  `x 0 = θ` (phase offset `θ_e = θ̂_g − θ_g`, PLL estimate minus grid angle, swing-style sign of
  work-sync `conventions.md` §D5), `x 1 = η` (state of the PI integrator, `η̇ = h(θ)`); the
  point `(θ, η)` is `PhasePlane.mk θ η` (`theorem/PhasePlane/Planar.lean`).
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

Source: work-sync `theory/T-gfl-dynamics.md` §1.7 (boxed 2D ODE), §1.9 (equilibria), §1.10
(Jacobian and local stability), §1.12 (`Σ_FD`); `theory/T-bogdanov-takens-bifurcation.md` §1.6;
`theory/T-gfl-ph.md` (1.1); `projects/vsc-stochastic-stability/notes/concepts/
equilibria-and-bifurcation.md` §1, §3 (written with `δω = 0`).

Results.
* Equilibria (`K_i ≠ 0`): exactly `{(θ*, δω / K_i) : h(θ*) = 0}`, for **every** constant `δω`.
  Hence existence of an equilibrium does not depend on `δω`. With `K_i = 0` an equilibrium needs
  `δω = 0` (`piPLLField_point_eq_zero_iff` covers both cases at the selected point).
* Jacobian at any point: `[[K_p g, K_i], [g, 0]]` with `g = h'(θ)`; trace `K_p g`, determinant
  `−K_i g` (so `K_i · tr + K_p · det = 0`); Hurwitz iff `K_p g < 0 ∧ K_i g < 0`.
* `h'(θ*) = 0` (`K_i ≠ 0`): the Jacobian is a nonzero nilpotent matrix (loss of hyperbolicity;
  linearization decides nothing).

Correction (`T-gfl-dynamics` §1.12, `Σ_FD`, and §1.14 region D): the note claims that when
`|δω| > K_p max |h|` "the system loses all equilibria". This is false for the reduced model of
§1.7: the PI integrator absorbs any constant frequency offset, the equilibria are
`(θ*, δω / K_i)` with the same `θ*` for every `δω`. `piPLL_exists_equilibrium_iff` and
`piPLL_frequencyDriftBoundary_refuted` state this statically; the connection conclusions
`PIPLL.frequencyDriftBoundary_refuted` and `PIPLL.frequencyDriftBoundary_stable` of
`PIPLLFamily` refute the claim through the family's requirement and semantics connections. The
note now states the boundary for a frequency ramp `ρ`; `PIPLLFamily` reads the ramped loop as the
model `m.ramp ρ` with detector `h − ρ/K_i` (`PIPLL.ramp_hasDerivAt_iff`) and proves the boundary
(`PIPLL.frequencyRampBoundary`: every ramp model is unstable when `ρ/K_i` leaves the range of `h`).

Sign conventions of the sources. `T-gfl-dynamics` §1.7, `T-gfl-ph` (1.1) and this module use
`θ̇ = K_p h + K_i η − δω`. The vsc note and `T-bogdanov-takens` §1.6 drop `δω` (take `δω = 0`).
`T-gfl-dynamics` §1.12 writes `θ̇ = −K_p h − K_i η − δω`; with `η̇ = h` that field is this one with
`h` replaced by `−h` and `η` by `−η` (so its stability condition would read `h' > 0`); §1.12 is
inconsistent with §1.7–§1.10 and this module follows §1.7.
-/

noncomputable section
namespace powerlib.PLL
open Matrix
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## The model -/

/-- PI-PLL vector field with phase-detector characteristic `h`:
`θ̇ = K_p h(θ) + K_i η − δω`, `η̇ = h(θ)`; coordinates `x 0 = θ`, `x 1 = η`. -/
def piPLLField (h : ℝ → ℝ) (Kp Ki δω : ℝ) (x : ℝ²) : ℝ² :=
  WithLp.toLp 2 ![Kp * h (x 0) + Ki * x 1 - δω, h (x 0)]

/-- The Jacobian matrix `[[K_p g, K_i], [g, 0]]`, `g = h'(θ)`. -/
def piPLLJacobian (Kp Ki g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Kp * g, Ki; g, 0]

@[simp, powerlib_foundation] theorem piPLLField_apply_zero (h : ℝ → ℝ) (Kp Ki δω : ℝ)
    (x : ℝ²) : piPLLField h Kp Ki δω x 0 = Kp * h (x 0) + Ki * x 1 - δω := rfl

@[simp, powerlib_foundation] theorem piPLLField_apply_one (h : ℝ → ℝ) (Kp Ki δω : ℝ)
    (x : ℝ²) : piPLLField h Kp Ki δω x 1 = h (x 0) := rfl

/-! ## Smoothness and Jacobian (derived from the field) -/

/-- The field is `C¹` on all of `ℝ²` when `h` is `C¹` on `ℝ`. -/
@[powerlib_foundation] theorem contDiff_piPLLField {h : ℝ → ℝ} {Kp Ki δω : ℝ}
    (hh : ContDiff ℝ 1 h) : ContDiff ℝ 1 (piPLLField h Kp Ki δω) := by
  have hc0 : ContDiff ℝ 1 (fun y : ℝ² => y 0) :=
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : ℝ² →L[ℝ] ℝ).contDiff
  have hc1 : ContDiff ℝ 1 (fun y : ℝ² => y 1) :=
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : ℝ² →L[ℝ] ℝ).contDiff
  have hs : ContDiff ℝ 1 (fun y : ℝ² => ![Kp * h (y 0) + Ki * y 1 - δω, h (y 0)]) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · show ContDiff ℝ 1 (fun y : ℝ² => Kp * h (y 0) + Ki * y 1 - δω)
      exact ((contDiff_const.mul (hh.comp hc0)).add (contDiff_const.mul hc1)).sub contDiff_const
    · show ContDiff ℝ 1 (fun y : ℝ² => h (y 0))
      exact hh.comp hc0
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.contDiff.comp hs

/-- Fréchet derivative of the field at any point `x`, from `h'(x 0) = g`. -/
@[powerlib_foundation] theorem hasFDerivAt_piPLLField {h : ℝ → ℝ} {Kp Ki δω g : ℝ}
    {x : ℝ²} (hh : HasDerivAt h g (x 0)) :
    HasFDerivAt (piPLLField h Kp Ki δω)
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (piPLLJacobian Kp Ki g)) x := by
  have h0 : HasFDerivAt (fun y : ℝ² => y 0)
      (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : ℝ² →L[ℝ] ℝ) x :=
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : ℝ² →L[ℝ] ℝ).hasFDerivAt
  have h1 : HasFDerivAt (fun y : ℝ² => y 1)
      (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : ℝ² →L[ℝ] ℝ) x :=
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : ℝ² →L[ℝ] ℝ).hasFDerivAt
  have hc : HasFDerivAt (fun y : ℝ² => h (y 0))
      (g • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : ℝ² →L[ℝ] ℝ)) x :=
    hh.comp_hasFDerivAt x h0
  have hF0 := ((hc.const_mul Kp).add (h1.const_mul Ki)).sub_const δω
  have hG : HasFDerivAt (fun y : ℝ² => ![Kp * h (y 0) + Ki * y 1 - δω, h (y 0)])
      (ContinuousLinearMap.pi
        ![Kp • (g • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : ℝ² →L[ℝ] ℝ))
          + Ki • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 : ℝ² →L[ℝ] ℝ),
          g • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 : ℝ² →L[ℝ] ℝ)]) x := by
    rw [hasFDerivAt_pi]
    intro i
    fin_cases i
    · simpa using hF0
    · simpa using hc
  have hE :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.hasFDerivAt.comp x hG
  have hfun : piPLLField h Kp Ki δω =
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm ∘
        (fun y : ℝ² => ![Kp * h (y 0) + Ki * y 1 - δω, h (y 0)]) := rfl
  rw [hfun]
  refine hE.congr_fderiv ?_
  ext v i
  rw [Matrix.ofLp_toEuclideanCLM]
  fin_cases i
  · simp [piPLLJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp [piPLLJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The Jacobian of the field (as computed by `fderiv`). -/
@[powerlib_foundation] theorem fderiv_piPLLField {h : ℝ → ℝ} {Kp Ki δω g : ℝ} {x : ℝ²}
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

/-- Every (complex) eigenvalue of the `g = 0` Jacobian is zero: `J² = 0`, so `μ² v = J² v = 0`
(`Linear.mulVec_pow_of_eigen`). -/
@[powerlib_foundation] theorem piPLLJacobian_zero_eigenvalue_eq_zero (Kp Ki : ℝ) {μ : ℂ}
    {v : Fin 2 → ℂ} (hv : v ≠ 0)
    (heig : (piPLLJacobian Kp Ki 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v) : μ = 0 := by
  have h2 := Linear.mulVec_pow_of_eigen heig 2
  rw [← Matrix.map_pow, piPLLJacobian_zero_sq, Matrix.map_zero _ (map_zero _),
    Matrix.zero_mulVec] at h2
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have := congrFun h2 i
  simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this
  exact pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp this.symm).resolve_right hi)

/-! ## Equilibria -/

/-- Equilibrium equations: for `K_i ≠ 0`, `f(x) = 0 ↔ h(θ) = 0 ∧ η = δω / K_i`.
Static evidence, not a connection conclusion. -/
@[powerlib_foundation] theorem piPLLField_eq_zero_iff {h : ℝ → ℝ} {Kp Ki δω : ℝ} (hKi : Ki ≠ 0)
    (x : ℝ²) : piPLLField h Kp Ki δω x = 0 ↔ h (x 0) = 0 ∧ x 1 = δω / Ki := by
  rw [PhasePlane.ext_iff']
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

/-- `K_i = 0` (no integrator): equilibria exist only for `δω = 0`.
Static evidence, not a connection conclusion. -/
@[powerlib_foundation] theorem piPLLField_eq_zero_iff_of_Ki_eq_zero {h : ℝ → ℝ} {Kp δω : ℝ}
    (x : ℝ²) : piPLLField h Kp 0 δω x = 0 ↔ h (x 0) = 0 ∧ δω = 0 := by
  rw [PhasePlane.ext_iff']
  simp only [piPLLField_apply_zero, piPLLField_apply_one, PiLp.zero_apply]
  constructor
  · rintro ⟨h0, h1⟩
    rw [h1] at h0
    exact ⟨h1, by linarith⟩
  · rintro ⟨h0, h1⟩
    rw [h0, h1]
    exact ⟨by ring, rfl⟩

/-- The equilibrium predicate at `(θ, η)`. Static evidence, not a connection conclusion. -/
@[powerlib_foundation] theorem piPLL_isEquilibrium_iff {h : ℝ → ℝ} {Kp Ki δω : ℝ} (hKi : Ki ≠ 0)
    (θ η : ℝ) :
    IsEquilibrium (piPLLField h Kp Ki δω) (PhasePlane.mk θ η) ↔ h θ = 0 ∧ η = δω / Ki :=
  piPLLField_eq_zero_iff hKi (PhasePlane.mk θ η)

/-- The equilibrium set, for every constant `δω` (`K_i ≠ 0`):
`{x | f x = 0} = {(θ*, δω / K_i) : h(θ*) = 0}`. Static evidence, not a connection conclusion. -/
@[powerlib_foundation] theorem piPLL_equilibria_eq {h : ℝ → ℝ} {Kp Ki δω : ℝ} (hKi : Ki ≠ 0) :
    {x : ℝ² | piPLLField h Kp Ki δω x = 0} =
      (fun θ => PhasePlane.mk θ (δω / Ki)) '' {θ | h θ = 0} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, piPLLField_eq_zero_iff hKi]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨x 0, h0, by rw [← h1, PhasePlane.mk_coords]⟩
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨hθ, rfl⟩

/-- Existence of an equilibrium does not depend on the constant frequency offset `δω`.
Static evidence, not a connection conclusion. -/
@[powerlib_foundation] theorem piPLL_exists_equilibrium_iff {h : ℝ → ℝ} {Kp Ki δω : ℝ}
    (hKi : Ki ≠ 0) : (∃ x, piPLLField h Kp Ki δω x = 0) ↔ ∃ θ, h θ = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x 0, ((piPLLField_eq_zero_iff hKi x).mp hx).1⟩
  · rintro ⟨θ, hθ⟩
    exact ⟨PhasePlane.mk θ (δω / Ki), (piPLLField_eq_zero_iff hKi _).mpr ⟨hθ, rfl⟩⟩

/-- At the selected point `(θ, δω / K_i)` (Lean's `δω / 0 = 0` when `K_i = 0`) the field vanishes
exactly when `h(θ) = 0` and the integrator can absorb the offset (`K_i ≠ 0`) or there is no offset.
Static evidence, not a connection conclusion. -/
@[powerlib_foundation] theorem piPLLField_point_eq_zero_iff {h : ℝ → ℝ} {Kp Ki δω θ : ℝ} :
    piPLLField h Kp Ki δω (PhasePlane.mk θ (δω / Ki)) = 0 ↔ h θ = 0 ∧ (Ki ≠ 0 ∨ δω = 0) := by
  by_cases hKi : Ki = 0
  · subst hKi
    rw [piPLLField_eq_zero_iff_of_Ki_eq_zero]
    simp
  · rw [piPLLField_eq_zero_iff hKi]
    simp [hKi]

/-! ## Loss of hyperbolicity -/

/-- `h'(θ*) = 0` (`K_i ≠ 0`): the Jacobian of the field at the equilibrium `(θ*, δω / K_i)` is
the nonzero nilpotent matrix `[[0, K_i], [0, 0]]` — a double zero eigenvalue with a single Jordan
block. The equilibrium is not hyperbolic, and the linearization theorems decide nothing there.
This is a statement about the linearization only, not a stability conclusion: static evidence,
not a connection conclusion. -/
@[powerlib_foundation] theorem piPLL_jacobian_nilpotent_of_deriv_zero {h : ℝ → ℝ}
    {Kp Ki δω θ : ℝ} (hzero : h θ = 0) (hderiv : HasDerivAt h 0 θ) (hKi : Ki ≠ 0) :
    piPLLField h Kp Ki δω (PhasePlane.mk θ (δω / Ki)) = 0 ∧
      fderiv ℝ (piPLLField h Kp Ki δω) (PhasePlane.mk θ (δω / Ki)) =
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (piPLLJacobian Kp Ki 0) ∧
      piPLLJacobian Kp Ki 0 ≠ 0 ∧ (piPLLJacobian Kp Ki 0) ^ 2 = 0 ∧
      ¬ LinearSystems.IsHurwitz (piPLLJacobian Kp Ki 0) :=
  ⟨(piPLLField_eq_zero_iff hKi _).mpr ⟨hzero, rfl⟩, fderiv_piPLLField hderiv,
    piPLLJacobian_zero_ne_zero hKi, piPLLJacobian_zero_sq Kp Ki,
    by rw [piPLLJacobian_isHurwitz_iff]; simp⟩

/-! ## Refutation of the frequency-drift boundary `Σ_FD` -/

/-- `T-gfl-dynamics` §1.12 claims: if `|δω| > K_p max |h|`, the reduced PLL loses all
equilibria. Counterexample: `h = −sin`, `K_p = K_i = 1`, `|h| ≤ 1`, `δω = 2`; the point
`(0, 2)` is an equilibrium. Static evidence about the equilibrium set, not a connection
conclusion; `PIPLL.frequencyDriftBoundary_refuted` (requirement connection) and
`PIPLL.frequencyDriftBoundary_stable` (semantics connection: the point is even locally
exponentially stable) in `PIPLLFamily` are the connection forms. -/
@[powerlib_foundation] theorem piPLL_frequencyDriftBoundary_refuted :
    ¬ (∀ (h : ℝ → ℝ) (Kp Ki δω M : ℝ), 0 < Kp → 0 < Ki → (∀ θ, |h θ| ≤ M) →
        Kp * M < |δω| → ¬ ∃ x, piPLLField h Kp Ki δω x = 0) := by
  intro H
  apply H (fun θ => -Real.sin θ) 1 1 2 1 one_pos one_pos
    (fun θ => by rw [abs_neg]; exact Real.abs_sin_le_one θ) (by norm_num)
  exact ⟨PhasePlane.mk 0 2, (piPLLField_eq_zero_iff one_ne_zero _).mpr ⟨by simp, by simp⟩⟩

end powerlib.PLL
