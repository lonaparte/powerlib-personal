import theorem.Discrete.Basic

/-! One-step time-integration schemes for an autonomous vector field, and their exact
reduction to discrete LTI recursions when the field is linear.

Model boundary.
* The continuous model is an autonomous field `f : E → E` (`ẋ = f x`), with a fixed step
  `h`.  For the linear results `E = Fin n → ℝ` and `f = linearField A`, i.e. `ẋ = A x`;
  inputs, if any, are already set to zero (perturbation coordinates).
* Schemes are trajectory predicates written directly from the update rule:
  forward Euler `x_{k+1} = x_k + h f(x_k)`, backward Euler `x_{k+1} = x_k + h f(x_{k+1})`,
  trapezoidal rule `x_{k+1} = x_k + (h/2)(f(x_k) + f(x_{k+1}))`.  No step-size control, no
  Newton iteration error: the implicit equation is assumed solved exactly.
* For a linear field the predicates are proved equivalent to the discrete recursions with
  matrices `1 + hA`, `(1 - hA)⁻¹` and `(1 - (h/2)A)⁻¹ (1 + (h/2)A)` (the latter two whenever
  the implicit matrix is invertible).
* Stability statements are about the discretized recursion, not the continuous system.

Main results.
* `isUnit_det_one_sub_smul_of_isHurwitz`: for a Hurwitz `A` and any `c > 0`, `1 - cA` is
  invertible, so backward Euler and the trapezoidal rule are uniquely solvable for every
  `h > 0`.
* `trapezoidal_schurStable_iff_isHurwitz`: when well posed, the trapezoidal recursion is
  Schur stable exactly when `A` is Hurwitz (A-stability with an exact stability region,
  through the Cayley map `μ = (1 + hlam/2)/(1 - hlam/2)`).
* `backwardEuler_schurStable_of_isHurwitz`: Hurwitz implies Schur stability of backward
  Euler (one direction only: backward Euler also damps some unstable modes).
* `forwardEuler_schurStable_iff`: forward Euler is Schur stable exactly when every
  eigenvalue `λ` satisfies `‖1 + hlam‖ < 1`.
* `trapezoidal_exponentiallyStable_of_isHurwitz`, `backwardEuler_exponentiallyStable_of_isHurwitz`:
  trajectory-level geometric decay of every scheme trajectory.

Source: work-sync theory/T-numerical-integration.md §1.2, §1.3, §1.7, §2.7;
theory/T-emt-simulation.md §1.3–§1.5 (trapezoidal discretization).  Foundation results.
-/

noncomputable section
namespace powerlib.Numerics
open Matrix

section Schemes

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Forward (explicit) Euler trajectory with step `h` for `ẋ = f x`. -/
def IsForwardEulerTrajectory (f : E → E) (h : ℝ) (x : ℕ → E) : Prop :=
  ∀ k, x (k + 1) = x k + h • f (x k)

/-- Backward (implicit) Euler trajectory with step `h` for `ẋ = f x`. -/
def IsBackwardEulerTrajectory (f : E → E) (h : ℝ) (x : ℕ → E) : Prop :=
  ∀ k, x (k + 1) = x k + h • f (x (k + 1))

/-- Trapezoidal-rule trajectory with step `h` for `ẋ = f x`. -/
def IsTrapezoidalTrajectory (f : E → E) (h : ℝ) (x : ℕ → E) : Prop :=
  ∀ k, x (k + 1) = x k + (h / 2) • (f (x k) + f (x (k + 1)))

end Schemes

variable {n : ℕ}

/-- The linear field `ẋ = A x`. -/
def linearField (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : Fin n → ℝ := A *ᵥ x

def forwardEulerMatrix (h : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 + h • A

def backwardEulerMatrix (h : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 - h • A)⁻¹

def trapezoidalMatrix (h : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 - (h / 2) • A)⁻¹ * (1 + (h / 2) • A)

section Reduction

variable (A : Matrix (Fin n) (Fin n) ℝ) (h : ℝ)

@[powerlib_foundation] private lemma one_sub_smul_mulVec (c : ℝ) (y : Fin n → ℝ) :
    (1 - c • A) *ᵥ y = y - c • (A *ᵥ y) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]

@[powerlib_foundation] private lemma one_add_smul_mulVec (c : ℝ) (y : Fin n → ℝ) :
    (1 + c • A) *ᵥ y = y + c • (A *ᵥ y) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]

@[powerlib_foundation] private lemma eq_inv_mulVec_iff {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsUnit P.det) (y z : Fin n → ℝ) : y = P⁻¹ *ᵥ z ↔ P *ᵥ y = z := by
  constructor
  · rintro rfl
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec]
  · rintro rfl
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hP, Matrix.one_mulVec]

/-- Forward Euler on a linear field is the recursion with `1 + hA`. -/
@[powerlib_foundation] theorem isForwardEulerTrajectory_iff (x : ℕ → Fin n → ℝ) :
    IsForwardEulerTrajectory (linearField A) h x ↔
      Discrete.IsTrajectory ⟨forwardEulerMatrix h A⟩ x := by
  simp only [IsForwardEulerTrajectory, Discrete.IsTrajectory, Discrete.Model.step,
    forwardEulerMatrix, linearField, one_add_smul_mulVec]

/-- Backward Euler on a linear field is the recursion with `(1 - hA)⁻¹`. -/
@[powerlib_foundation] theorem isBackwardEulerTrajectory_iff (hP : IsUnit (1 - h • A).det)
    (x : ℕ → Fin n → ℝ) :
    IsBackwardEulerTrajectory (linearField A) h x ↔
      Discrete.IsTrajectory ⟨backwardEulerMatrix h A⟩ x := by
  simp only [IsBackwardEulerTrajectory, Discrete.IsTrajectory, Discrete.Model.step,
    backwardEulerMatrix, linearField]
  refine forall_congr' fun k => ?_
  rw [eq_inv_mulVec_iff hP, one_sub_smul_mulVec, sub_eq_iff_eq_add]

/-- The trapezoidal rule on a linear field is the recursion with
`(1 - (h/2)A)⁻¹ (1 + (h/2)A)`. -/
@[powerlib_foundation] theorem isTrapezoidalTrajectory_iff (hP : IsUnit (1 - (h / 2) • A).det)
    (x : ℕ → Fin n → ℝ) :
    IsTrapezoidalTrajectory (linearField A) h x ↔
      Discrete.IsTrajectory ⟨trapezoidalMatrix h A⟩ x := by
  simp only [IsTrapezoidalTrajectory, Discrete.IsTrajectory, Discrete.Model.step,
    trapezoidalMatrix, linearField]
  refine forall_congr' fun k => ?_
  rw [← Matrix.mulVec_mulVec, eq_inv_mulVec_iff hP, one_sub_smul_mulVec, one_add_smul_mulVec,
    smul_add, sub_eq_iff_eq_add, add_assoc]

end Reduction

section Spectral

open LinearSystems

variable {A : Matrix (Fin n) (Fin n) ℝ} {h : ℝ}

@[powerlib_foundation] private lemma map_one_sub_smul (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    (1 - c • A).map (algebraMap ℝ ℂ) = 1 - (c : ℂ) • A.map (algebraMap ℝ ℂ) := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

@[powerlib_foundation] private lemma map_one_add_smul (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    (1 + c • A).map (algebraMap ℝ ℂ) = 1 + (c : ℂ) • A.map (algebraMap ℝ ℂ) := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

@[powerlib_foundation] private lemma complexify_mulVec (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) :
    A.map (algebraMap ℝ ℂ) *ᵥ (fun i => (v i : ℂ)) = fun i => ((A *ᵥ v) i : ℂ) := by
  ext i
  simp [Matrix.mulVec, dotProduct]

@[powerlib_foundation] private lemma cmulVec_one_sub (M : Matrix (Fin n) (Fin n) ℂ) (c : ℂ)
    (w : Fin n → ℂ) : (1 - c • M) *ᵥ w = w - c • (M *ᵥ w) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]

@[powerlib_foundation] private lemma cmulVec_one_add (M : Matrix (Fin n) (Fin n) ℂ) (c : ℂ)
    (w : Fin n → ℂ) : (1 + c • M) *ᵥ w = w + c • (M *ᵥ w) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]

/-- Real part of the Cayley-type quotient `(w - 1)/(w + 1)`. -/
@[powerlib_foundation] theorem re_sub_one_div_add_one (w : ℂ) :
    ((w - 1) / (w + 1)).re = (Complex.normSq w - 1) / Complex.normSq (w + 1) := by
  rw [Complex.div_re]
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.sub_im, Complex.add_im,
    Complex.one_im, sub_zero, add_zero, Complex.normSq_apply]
  ring

/-- For a Hurwitz matrix and any `c > 0`, the implicit matrix `1 - cA` is invertible. -/
@[powerlib_foundation] theorem isUnit_det_one_sub_smul_of_isHurwitz (hA : IsHurwitz A) {c : ℝ}
    (hc : 0 < c) : IsUnit (1 - c • A).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  rw [one_sub_smul_mulVec, sub_eq_zero] at hz
  have hAv : A *ᵥ v = c⁻¹ • v := by
    conv_rhs => rw [hz]
    rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  have hw : (fun i => (v i : ℂ)) ≠ 0 := by
    intro h0
    apply hv
    ext i
    have := congrFun h0 i
    simpa using this
  have heig : A.map (algebraMap ℝ ℂ) *ᵥ (fun i => (v i : ℂ)) =
      ((c⁻¹ : ℝ) : ℂ) • (fun i => (v i : ℂ)) := by
    rw [complexify_mulVec, hAv]
    ext i
    simp
  have hre := hA _ _ hw heig
  simp only [Complex.ofReal_re, neg_zero] at hre
  exact absurd hre (not_lt.mpr (inv_pos.mpr hc).le)

/-- Trapezoidal rule: Hurwitz implies Schur stability for every `h > 0`. -/
@[powerlib_foundation] theorem trapezoidal_schurStable_of_isHurwitz (hA : IsHurwitz A)
    (hh : 0 < h) : Discrete.SchurStable (trapezoidalMatrix h A) := by
  have hP := isUnit_det_one_sub_smul_of_isHurwitz hA (half_pos hh)
  intro μ v hv heig
  have hPΦ : (1 - (h / 2) • A) * trapezoidalMatrix h A = 1 + (h / 2) • A := by
    rw [trapezoidalMatrix, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.one_mul]
  have hc := congrArg (fun M => M.map (algebraMap ℝ ℂ) *ᵥ v) hPΦ
  simp only [Matrix.map_mul, map_one_sub_smul, map_one_add_smul] at hc
  rw [← Matrix.mulVec_mulVec, heig, cmulVec_one_sub, cmulVec_one_add, Matrix.mulVec_smul] at hc
  set c : ℂ := ((h / 2 : ℝ) : ℂ) with hcdef
  set u := A.map (algebraMap ℝ ℂ) *ᵥ v with hu
  have hc0 : c ≠ 0 := by
    rw [hcdef]; exact_mod_cast (half_pos hh).ne'
  have hrel : (μ - 1) • v = (c * (μ + 1)) • u := by
    have : μ • v - c • μ • u = v + c • u := hc
    rw [sub_smul, one_smul, mul_smul, add_smul, one_smul, smul_add]
    rw [smul_comm c μ u] at this
    linear_combination (norm := module) this
  have hμ1 : μ + 1 ≠ 0 := by
    intro h0
    have hm : μ - 1 = -2 := by linear_combination h0
    rw [h0, mul_zero, zero_smul, hm] at hrel
    exact hv (by simpa using hrel)
  have hcμ : c * (μ + 1) ≠ 0 := mul_ne_zero hc0 hμ1
  have hlam : u = ((μ - 1) / (c * (μ + 1))) • v := by
    rw [div_eq_inv_mul, mul_smul, hrel, ← mul_smul, inv_mul_cancel₀ hcμ, one_smul]
  have hre := hA _ v hv hlam
  rw [neg_zero, div_mul_eq_div_div_swap, hcdef, Complex.div_ofReal_re,
    re_sub_one_div_add_one] at hre
  have hq : (Complex.normSq μ - 1) / Complex.normSq (μ + 1) < 0 := by
    have := (div_lt_iff₀ (half_pos hh)).mp hre
    simpa using this
  have hns : 0 < Complex.normSq (μ + 1) := Complex.normSq_pos.mpr hμ1
  have hlt : Complex.normSq μ < 1 := by
    have := (div_lt_iff₀ hns).mp hq
    linarith
  rw [Complex.normSq_eq_norm_sq] at hlt
  nlinarith [norm_nonneg μ]

@[powerlib_foundation] private lemma map_one_complex :
    (1 : Matrix (Fin n) (Fin n) ℝ).map (algebraMap ℝ ℂ) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

/-- `‖1 + w‖² - ‖1 - w‖² = 4 Re w`. -/
@[powerlib_foundation] theorem normSq_one_add_sub_normSq_one_sub (w : ℂ) :
    Complex.normSq (1 + w) - Complex.normSq (1 - w) = 4 * w.re := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.one_re,
    Complex.add_im, Complex.sub_im, Complex.one_im]
  ring

/-- Trapezoidal rule, converse: a well-posed Schur-stable trapezoidal recursion comes from a
Hurwitz matrix.  Together with `trapezoidal_schurStable_of_isHurwitz` the trapezoidal rule
neither creates nor destroys stability of `ẋ = A x`. -/
@[powerlib_foundation] theorem isHurwitz_of_trapezoidal_schurStable (hh : 0 < h)
    (hP : IsUnit (1 - (h / 2) • A).det) (hS : Discrete.SchurStable (trapezoidalMatrix h A)) :
    IsHurwitz A := by
  intro lam v hv heig
  set c : ℂ := ((h / 2 : ℝ) : ℂ) with hcdef
  set Ac := A.map (algebraMap ℝ ℂ) with hAc
  set Pinv := ((1 - (h / 2) • A)⁻¹).map (algebraMap ℝ ℂ) with hPinv
  have hPiP : Pinv * (1 - c • Ac) = 1 := by
    rw [hPinv, hcdef, hAc, ← map_one_sub_smul, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hP,
      map_one_complex]
  have hPv : (1 - c • Ac) *ᵥ v = (1 - c * lam) • v := by
    rw [cmulVec_one_sub, heig, smul_smul, sub_smul, one_smul]
  have hQv : (1 + c • Ac) *ᵥ v = (1 + c * lam) • v := by
    rw [cmulVec_one_add, heig, smul_smul, add_smul, one_smul]
  have hback : ∀ w : Fin n → ℂ, w = Pinv *ᵥ ((1 - c • Ac) *ᵥ w) := by
    intro w
    rw [Matrix.mulVec_mulVec, hPiP, Matrix.one_mulVec]
  have hd : 1 - c * lam ≠ 0 := by
    intro h0
    apply hv
    rw [hback v, hPv, h0, zero_smul, Matrix.mulVec_zero]
  have hPiv : Pinv *ᵥ v = (1 - c * lam)⁻¹ • v := by
    have h1 := hback v
    rw [hPv, Matrix.mulVec_smul] at h1
    calc Pinv *ᵥ v = (1 - c * lam)⁻¹ • ((1 - c * lam) • Pinv *ᵥ v) := by
          rw [smul_smul, inv_mul_cancel₀ hd, one_smul]
      _ = (1 - c * lam)⁻¹ • v := by rw [← h1]
  have hΦv : (trapezoidalMatrix h A).map (algebraMap ℝ ℂ) *ᵥ v =
      ((1 + c * lam) / (1 - c * lam)) • v := by
    rw [trapezoidalMatrix, Matrix.map_mul, ← hPinv, map_one_add_smul, ← hcdef, ← hAc,
      ← Matrix.mulVec_mulVec, hQv, Matrix.mulVec_smul, hPiv, smul_smul, div_eq_mul_inv,
      mul_comm (1 + c * lam)]
  have hlt := hS _ v hv hΦv
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hd)] at hlt
  have hsq : Complex.normSq (1 + c * lam) < Complex.normSq (1 - c * lam) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    exact pow_lt_pow_left₀ hlt (norm_nonneg _) two_ne_zero
  have hkey := normSq_one_add_sub_normSq_one_sub (c * lam)
  rw [hcdef, Complex.re_ofReal_mul] at hkey
  have : h / 2 * lam.re < 0 := by linarith
  rw [neg_zero]
  nlinarith [half_pos hh]

/-- The trapezoidal recursion is Schur stable exactly when `A` is Hurwitz (for `h > 0` and a
well-posed implicit step). -/
@[powerlib_foundation] theorem trapezoidal_schurStable_iff_isHurwitz (hh : 0 < h)
    (hP : IsUnit (1 - (h / 2) • A).det) :
    Discrete.SchurStable (trapezoidalMatrix h A) ↔ IsHurwitz A :=
  ⟨isHurwitz_of_trapezoidal_schurStable hh hP,
    fun hA => trapezoidal_schurStable_of_isHurwitz hA hh⟩

/-- Backward Euler: Hurwitz implies Schur stability for every `h > 0`. -/
@[powerlib_foundation] theorem backwardEuler_schurStable_of_isHurwitz (hA : IsHurwitz A)
    (hh : 0 < h) : Discrete.SchurStable (backwardEulerMatrix h A) := by
  have hP := isUnit_det_one_sub_smul_of_isHurwitz hA hh
  intro μ v hv heig
  have hPΦ : (1 - h • A) * backwardEulerMatrix h A = 1 := Matrix.mul_nonsing_inv _ hP
  have hc := congrArg (fun M => M.map (algebraMap ℝ ℂ) *ᵥ v) hPΦ
  simp only [Matrix.map_mul, map_one_sub_smul, map_one_complex] at hc
  rw [← Matrix.mulVec_mulVec, heig, cmulVec_one_sub, Matrix.mulVec_smul,
    Matrix.one_mulVec] at hc
  set c : ℂ := (h : ℂ) with hcdef
  set u := A.map (algebraMap ℝ ℂ) *ᵥ v with hu
  have hc0 : c ≠ 0 := by rw [hcdef]; exact_mod_cast hh.ne'
  have hrel : (μ - 1) • v = (c * μ) • u := by
    have : μ • v - c • μ • u = v := hc
    rw [sub_smul, one_smul, mul_smul]
    rw [smul_comm c μ u] at this
    linear_combination (norm := module) this
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_smul, zero_sub, neg_smul, one_smul, neg_eq_zero] at hrel
    exact hv hrel
  have hcμ : c * μ ≠ 0 := mul_ne_zero hc0 hμ0
  have hlam : u = ((μ - 1) / (c * μ)) • v := by
    rw [div_eq_inv_mul, mul_smul, hrel, ← mul_smul, inv_mul_cancel₀ hcμ, one_smul]
  have hre := hA _ v hv hlam
  rw [neg_zero, div_mul_eq_div_div_swap, hcdef, Complex.div_ofReal_re] at hre
  have hq : ((μ - 1) / μ).re < 0 := by
    have := (div_lt_iff₀ hh).mp hre
    simpa using this
  have hsplit : (μ - 1) / μ = 1 - μ⁻¹ := by field_simp
  rw [hsplit, Complex.sub_re, Complex.one_re, Complex.inv_re] at hq
  have hns : 0 < Complex.normSq μ := Complex.normSq_pos.mpr hμ0
  have h1 : Complex.normSq μ < μ.re := by
    have := (lt_div_iff₀ hns).mp (by linarith : 1 < μ.re / Complex.normSq μ)
    linarith
  have h2 : μ.re ≤ ‖μ‖ := Complex.re_le_norm μ
  rw [Complex.normSq_eq_norm_sq] at h1
  have hpos : 0 < ‖μ‖ := norm_pos_iff.mpr hμ0
  nlinarith

/-- Forward Euler is Schur stable exactly when every eigenvalue `λ` of `A` has
`‖1 + hλ‖ < 1` (that is, `hλ` is in the open forward-Euler disk). -/
@[powerlib_foundation] theorem forwardEuler_schurStable_iff (hh : h ≠ 0) :
    Discrete.SchurStable (forwardEulerMatrix h A) ↔
      ∀ (lam : ℂ) (v : Fin n → ℂ), v ≠ 0 → A.map (algebraMap ℝ ℂ) *ᵥ v = lam • v →
        ‖1 + (h : ℂ) * lam‖ < 1 := by
  have hmap : (forwardEulerMatrix h A).map (algebraMap ℝ ℂ) =
      1 + (h : ℂ) • A.map (algebraMap ℝ ℂ) := map_one_add_smul A h
  constructor
  · intro hS lam v hv heig
    apply hS _ v hv
    rw [hmap, cmulVec_one_add, heig, smul_smul, add_smul, one_smul]
  · intro hF μ v hv heig
    rw [hmap, cmulVec_one_add] at heig
    have hc0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh
    have hlam : A.map (algebraMap ℝ ℂ) *ᵥ v = ((μ - 1) / (h : ℂ)) • v := by
      have h1 : (h : ℂ) • (A.map (algebraMap ℝ ℂ) *ᵥ v) = (μ - 1) • v := by
        rw [sub_smul, one_smul, ← heig]; abel
      rw [div_eq_inv_mul, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have := hF _ v hv hlam
    rwa [mul_div_cancel₀ _ hc0, add_sub_cancel] at this

end Spectral

section Semantic

open LinearSystems

variable {A : Matrix (Fin n) (Fin n) ℝ} {h : ℝ}

/-- Every trapezoidal trajectory of a Hurwitz linear field decays geometrically, for every
step `h > 0`. -/
@[powerlib_foundation] theorem trapezoidal_exponentiallyStable_of_isHurwitz (hA : IsHurwitz A)
    (hh : 0 < h) :
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x, IsTrapezoidalTrajectory (linearField A) h x →
      ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖ := by
  have hP := isUnit_det_one_sub_smul_of_isHurwitz hA (half_pos hh)
  obtain ⟨C, hC, ρ, hρ0, hρ1, hb⟩ := Discrete.exponentiallyStable_of_schurStable
    (m := ⟨trapezoidalMatrix h A⟩) (trapezoidal_schurStable_of_isHurwitz hA hh)
  exact ⟨C, hC, ρ, hρ0, hρ1, fun x hx => hb x ((isTrapezoidalTrajectory_iff A h hP x).mp hx)⟩

/-- Every backward-Euler trajectory of a Hurwitz linear field decays geometrically, for every
step `h > 0`. -/
@[powerlib_foundation] theorem backwardEuler_exponentiallyStable_of_isHurwitz (hA : IsHurwitz A)
    (hh : 0 < h) :
    ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x, IsBackwardEulerTrajectory (linearField A) h x →
      ∀ k, ‖x k‖ ≤ C * ρ ^ k * ‖x 0‖ := by
  have hP := isUnit_det_one_sub_smul_of_isHurwitz hA hh
  obtain ⟨C, hC, ρ, hρ0, hρ1, hb⟩ := Discrete.exponentiallyStable_of_schurStable
    (m := ⟨backwardEulerMatrix h A⟩) (backwardEuler_schurStable_of_isHurwitz hA hh)
  exact ⟨C, hC, ρ, hρ0, hρ1,
    fun x hx => hb x ((isBackwardEulerTrajectory_iff A h hP x).mp hx)⟩

/-- A well-posed trapezoidal step has exactly one trajectory from each initial state. -/
@[powerlib_foundation] theorem trapezoidal_existsUnique (hP : IsUnit (1 - (h / 2) • A).det)
    (initial : Fin n → ℝ) :
    ∃! x, IsTrapezoidalTrajectory (linearField A) h x ∧ x 0 = initial := by
  refine ⟨Discrete.response ⟨trapezoidalMatrix h A⟩ initial,
    ⟨(isTrapezoidalTrajectory_iff A h hP _).mpr (Discrete.response_isTrajectory _ _),
      Discrete.response_zero _ _⟩, ?_⟩
  rintro y ⟨hy, hy0⟩
  funext k
  rw [((isTrapezoidalTrajectory_iff A h hP y).mp hy).eq_response k, hy0]

/-- A well-posed backward-Euler step has exactly one trajectory from each initial state. -/
@[powerlib_foundation] theorem backwardEuler_existsUnique (hP : IsUnit (1 - h • A).det)
    (initial : Fin n → ℝ) :
    ∃! x, IsBackwardEulerTrajectory (linearField A) h x ∧ x 0 = initial := by
  refine ⟨Discrete.response ⟨backwardEulerMatrix h A⟩ initial,
    ⟨(isBackwardEulerTrajectory_iff A h hP _).mpr (Discrete.response_isTrajectory _ _),
      Discrete.response_zero _ _⟩, ?_⟩
  rintro y ⟨hy, hy0⟩
  funext k
  rw [((isBackwardEulerTrajectory_iff A h hP y).mp hy).eq_response k, hy0]

end Semantic

end powerlib.Numerics
