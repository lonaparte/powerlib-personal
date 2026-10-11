import theorem.PH.PositiveReal
import theorem.Criteria.Hurwitz2

/-! # Passivity, zero-state observability and asymptotic stability of linear pH systems

Source: work-sync `theory/T-ph.md` Part 2, "Passivity 不等于稳定": "(1.4) 给的是 input-output
passivity … 需配合 zero-state observability + detectability（Khalil 2002 §6）才推出渐近稳定".

Model: the constant-coefficient pH system of `theorem/PH/Linear.lean` (P0b) as the `LTI.Model`
`linearLTIModel J R g Q`: `ẋ = (J − R) Q x + g u`, `y = gᵀ Q x`, `H = ½ xᵀ Q x`, with `J`
skew, `R ⪰ 0`, `Q ≻ 0`, real, continuous time. For a linear system zero-state observability is
observability of the pair `(A, C) = ((J − R) Q, gᵀ Q)` (`LinearSystems.IsObservable`).

Correction (refutation of the literal claim). Passivity together with zero-state observability
does **not** give asymptotic stability of the unforced system: the lossless series `LC` loop
(`J = [[0, −1], [1, 0]]`, `R = 0`, `g = (1, 0)ᵀ`, `Q = I`, output the loop current) is passive
(`losslessLC_passive`) and observable (`losslessLC_observable`), but `x(t) = (cos t, sin t)` is an
unforced trajectory that keeps its energy (`losslessLC_trajectory`, `losslessLC_not_tendsto`),
and its state matrix is not Hurwitz (`losslessLC_not_isHurwitz`). Khalil's results need output
strict passivity or an output feedback `u = −φ(y)`.

Corrected statement (`phOutputFeedback_isHurwitz`, `phOutputFeedback_exponentiallyStable`):
with damping injection `u = −k y` (`k > 0`; the closed loop is the pH system with dissipation
`R + k g gᵀ`, i.e. output strictly passive, `Ḣ ≤ −k |y|²`) and `(A, C)` observable, the closed
loop is Hurwitz, hence exponentially stable. The proof is spectral (an eigenvector on the
imaginary axis would have `C v = 0` and be an eigenvector of `A`, contradicting observability);
for linear systems this replaces the LaSalle argument. The nonlinear LaSalle version is not
formalized here.
-/

noncomputable section
namespace powerlib.PH
open Matrix

variable {n m : ℕ}

/-! ## Helpers: real and imaginary parts of real matrices acting on complex vectors -/

@[powerlib_foundation] theorem phCx_mulVec_re {p : ℕ} (M : Matrix (Fin p) (Fin n) ℝ)
    (v : Fin n → ℂ) (i : Fin p) :
    ((LTI.complexify M *ᵥ v) i).re = (M *ᵥ fun j => (v j).re) i := by
  simp [mulVec, dotProduct, Complex.re_sum, Complex.mul_re]

@[powerlib_foundation] theorem phCx_mulVec_im {p : ℕ} (M : Matrix (Fin p) (Fin n) ℝ)
    (v : Fin n → ℂ) (i : Fin p) :
    ((LTI.complexify M *ᵥ v) i).im = (M *ᵥ fun j => (v j).im) i := by
  simp [mulVec, dotProduct, Complex.im_sum, Complex.mul_im]

/-- A complex eigenvector of a real `A` lying in `ker C` contradicts observability of `(A, C)`. -/
@[powerlib_foundation] theorem phCx_eq_zero_of_isObservable {p : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {C : Matrix (Fin p) (Fin n) ℝ} (hobs : LinearSystems.IsObservable A C) {μ : ℂ}
    {v : Fin n → ℂ} (heig : LTI.complexify A *ᵥ v = μ • v) (hC : LTI.complexify C *ᵥ v = 0) :
    v = 0 := by
  have hpow : ∀ k : ℕ, LTI.complexify (C * A ^ k) *ᵥ v = 0 := by
    intro k
    have hA : ∀ j : ℕ, LTI.complexify (A ^ j) *ᵥ v = μ ^ j • v := by
      intro j
      induction j with
      | zero => simp [LTI.complexify]
      | succ j ih =>
        rw [pow_succ, LTI.complexify_mul, ← mulVec_mulVec, heig, mulVec_smul, ih, smul_smul,
          pow_succ, mul_comm]
    rw [LTI.complexify_mul, ← mulVec_mulVec, hA, mulVec_smul, hC, smul_zero]
  have hre := hobs (fun j => (v j).re) fun k => by
    funext i
    have := congrFun (hpow k) i
    rw [← phCx_mulVec_re, this]
    simp
  have him := hobs (fun j => (v j).im) fun k => by
    funext i
    have := congrFun (hpow k) i
    rw [← phCx_mulVec_im, this]
    simp
  funext j
  apply Complex.ext
  · simpa using congrFun hre j
  · simpa using congrFun him j

/-! ## Counterexample: the lossless `LC` loop -/

/-- Interconnection of the lossless `LC` loop, state `(φ, q)` with `L = C = 1`. -/
def losslessJ : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- Input matrix: the source drives the inductor; the output is the loop current. -/
def losslessG : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

@[powerlib_foundation] theorem losslessJ_skew : losslessJᵀ = -losslessJ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [losslessJ]

@[powerlib_foundation] theorem losslessLC_stateMatrix :
    linearStateMatrix losslessJ 0 1 = !![0, -1; 1, 0] := by
  simp [linearStateMatrix, losslessJ]

/-- The lossless loop is passive with storage `H = ½ |x|²`. -/
@[powerlib_domain] theorem losslessLC_passive :
    Passivity.PassiveWithStorage (StateSpacePassivity.system (linearLTIModel losslessJ 0 losslessG 1))
      (StateSpacePassivity.energy 1) :=
  (linearCollocatedCertificate losslessG losslessJ_skew PosSemidef.zero PosDef.one).toCertificate
    |>.passiveWithStorage

/-- The lossless loop is (zero-state) observable from the loop current. -/
@[powerlib_foundation] theorem losslessLC_observable :
    LinearSystems.IsObservable (linearLTIModel losslessJ 0 losslessG 1).A
      (linearLTIModel losslessJ 0 losslessG 1).C := by
  intro x hx
  have h0 := congrFun (hx 0) 0
  have h1 := congrFun (hx 1) 0
  simp [linearLTIModel, linearStateMatrix, losslessJ, losslessG, mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.mul_apply] at h0 h1
  funext i; fin_cases i <;> simp [h0, h1]

/-- `x(t) = (cos t, sin t)` is an unforced trajectory of the lossless loop. -/
@[powerlib_foundation] theorem losslessLC_trajectory :
    Passivity.IsTrajectory (StateSpacePassivity.system (linearLTIModel losslessJ 0 losslessG 1))
      (fun _ => 0) (fun t => ![Real.cos t, Real.sin t]) := by
  intro t _
  apply HasDerivAt.hasDerivWithinAt
  have h : HasDerivAt (fun t => ![Real.cos t, Real.sin t]) ![-Real.sin t, Real.cos t] t := by
    apply hasDerivAt_pi.2
    intro i; fin_cases i
    · simpa using Real.hasDerivAt_cos t
    · simpa using Real.hasDerivAt_sin t
  convert h using 1
  change LTI.Model.field _ _ _ = _
  ext i; fin_cases i <;>
    simp [LTI.Model.field, linearLTIModel, linearStateMatrix, losslessJ]

/-- That trajectory keeps unit energy, so it does not converge to the origin. -/
@[powerlib_domain] theorem losslessLC_not_tendsto :
    ¬ Filter.Tendsto (fun t => ![Real.cos t, Real.sin t]) Filter.atTop (nhds 0) := by
  intro h
  have h2 : Filter.Tendsto (fun t => (![Real.cos t, Real.sin t] : Fin 2 → ℝ) 0 ^ 2 +
      (![Real.cos t, Real.sin t] : Fin 2 → ℝ) 1 ^ 2) Filter.atTop (nhds ((0 : Fin 2 → ℝ) 0 ^ 2 +
        (0 : Fin 2 → ℝ) 1 ^ 2)) := by
    have hc0 := ((continuous_apply 0).tendsto _).comp h
    have hc1 := ((continuous_apply 1).tendsto _).comp h
    exact (hc0.pow 2).add (hc1.pow 2)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.cos_sq_add_sin_sq,
    Pi.zero_apply] at h2
  norm_num at h2

/-- The lossless loop's state matrix is not Hurwitz (trace zero). -/
@[powerlib_foundation] theorem losslessLC_not_isHurwitz :
    ¬ LinearSystems.IsHurwitz (linearLTIModel losslessJ 0 losslessG 1).A := by
  intro h
  rw [show (linearLTIModel losslessJ 0 losslessG 1).A = !![0, -1; 1, 0] from
    losslessLC_stateMatrix, Criteria.isHurwitz_fin_two_of_iff] at h
  linarith [h.1]

/-! ## Corrected statement: damping injection + observability ⇒ Hurwitz -/

section Feedback

variable {J R Q : Matrix (Fin n) (Fin n) ℝ} {g : Matrix (Fin n) (Fin m) ℝ} {k : ℝ}

/-- Output feedback `u = −k y` turns `(J − R) Q x + g u` into `(J − (R + k g gᵀ)) Q x`. -/
@[powerlib_foundation] theorem phOutputFeedback_stateMatrix (k : ℝ) :
    linearStateMatrix J R Q - g * (k • (gᵀ * Q)) = linearStateMatrix J (R + k • (g * gᵀ)) Q := by
  simp only [linearStateMatrix, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, sub_mul,
    add_mul]
  abel

/-- Damping injection `u = −k y` (`k > 0`) on an observable linear pH system gives a Hurwitz
closed loop. -/
@[powerlib_foundation] theorem phOutputFeedback_isHurwitz (hJ : Jᵀ = -J) (hR : R.PosSemidef)
    (hQ : Q.PosDef) (hk : 0 < k)
    (hobs : LinearSystems.IsObservable (linearStateMatrix J R Q) (gᵀ * Q)) :
    LinearSystems.IsHurwitz (linearStateMatrix J (R + k • (g * gᵀ)) Q) := by
  intro μ v hv heig
  rw [neg_zero]
  have hQt : Qᵀ = Q := StateSpacePassivity.symmetric_of_posDef hQ
  set C := gᵀ * Q with hCdef
  have hggt : (g * gᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose g
  have hR' : (R + k • (g * gᵀ)).PosSemidef := hR.add (hggt.smul hk.le)
  have hle : μ.re ≤ 0 := phSpectral_re_nonpos hJ hR' hQ hv heig
  rcases hle.lt_or_eq with hlt | heq0
  · exact hlt
  · exfalso
    -- the Lyapunov identity with `μ.re = 0` forces `Re vᴴ (Q (R + k g gᵀ) Q) v = 0`
    set A' := linearStateMatrix J (R + k • (g * gᵀ)) Q with hA'def
    set S := star v ⬝ᵥ (LTI.complexify Q *ᵥ v)
    have hR't : (R + k • (g * gᵀ))ᵀ = R + k • (g * gᵀ) := by
      simpa only [conjTranspose_eq_transpose_of_trivial] using hR'.isHermitian.eq
    have hlyap := linearStateMatrix_lyapunov hJ hQt hR't
    have h1 : star v ⬝ᵥ (LTI.complexify (Q * A') *ᵥ v) = μ * S := by
      rw [LTI.complexify_mul, ← mulVec_mulVec, heig, mulVec_smul, dotProduct_smul, smul_eq_mul]
    have h2 : star v ⬝ᵥ (LTI.complexify (A'ᵀ * Q) *ᵥ v) = star μ * S := by
      rw [LTI.complexify_mul, ← mulVec_mulVec, ← phCx_complexify_conjTranspose,
        dotProduct_mulVec, ← star_mulVec, heig, star_smul, smul_dotProduct, smul_eq_mul]
    have hsum : star v ⬝ᵥ (LTI.complexify (A'ᵀ * Q + Q * A') *ᵥ v) = star μ * S + μ * S := by
      rw [phCx_complexify_add, add_mulVec, dotProduct_add, h1, h2]
    have hre0 : (star v ⬝ᵥ (LTI.complexify (A'ᵀ * Q + Q * A') *ᵥ v)).re = 0 := by
      rw [hsum]
      simp only [Complex.add_re, Complex.mul_re, Complex.star_def, Complex.conj_re,
        Complex.conj_im]
      rw [heq0]; ring
    rw [hlyap] at hre0
    -- split `Q (R + k g gᵀ) Q = Qᵀ R Q + k Cᵀ C`
    have hsplit : -(2 : ℝ) • (Q * (R + k • (g * gᵀ)) * Q) =
        -(2 : ℝ) • (Qᵀ * R * Q) + -(2 * k) • (Cᵀ * C) := by
      rw [hCdef, transpose_mul, transpose_transpose, hQt]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add,
        smul_smul, Matrix.mul_assoc]
      ring_nf
    rw [hsplit, phCx_complexify_add, add_mulVec, dotProduct_add, Complex.add_re] at hre0
    have hQRQ : (Qᵀ * R * Q).PosSemidef := by
      simpa [conjTranspose_eq_transpose_of_trivial] using hR.conjTranspose_mul_mul_same Q
    have hCC : (Cᵀ * C).PosSemidef := by
      simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self C
    have hsm : ∀ (c : ℝ) (P : Matrix (Fin n) (Fin n) ℝ),
        (star v ⬝ᵥ (LTI.complexify (c • P) *ᵥ v)).re = c * (star v ⬝ᵥ (LTI.complexify P *ᵥ v)).re := by
      intro c P
      rw [phCx_form_re, phCx_form_re, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_smul,
        dotProduct_smul, smul_eq_mul, smul_eq_mul]
      ring
    rw [hsm, hsm] at hre0
    have hn1 := phCx_form_re_nonneg hQRQ v
    have hn2 := phCx_form_re_nonneg hCC v
    have hCC0 : (star v ⬝ᵥ (LTI.complexify (Cᵀ * C) *ᵥ v)).re = 0 := by nlinarith
    -- hence `C v = 0`
    have hCv : LTI.complexify C *ᵥ v = 0 := by
      rw [phCx_form_re] at hCC0
      have ha := hCC.dotProduct_mulVec_nonneg (fun i => (v i).re)
      have hb := hCC.dotProduct_mulVec_nonneg (fun i => (v i).im)
      rw [star_trivial] at ha hb
      have ha0 : (fun i => (v i).re) ⬝ᵥ ((Cᵀ * C) *ᵥ fun i => (v i).re) = 0 := by linarith
      have hb0 : (fun i => (v i).im) ⬝ᵥ ((Cᵀ * C) *ᵥ fun i => (v i).im) = 0 := by linarith
      rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, dotProduct_self_eq_zero] at ha0 hb0
      funext i
      apply Complex.ext
      · rw [phCx_mulVec_re, ha0]; rfl
      · rw [phCx_mulVec_im, hb0]; rfl
    -- and `v` is an eigenvector of the open-loop `A`
    have hAv : LTI.complexify (linearStateMatrix J R Q) *ᵥ v = μ • v := by
      have hA : linearStateMatrix J R Q = A' + g * (k • C) := by
        rw [hA'def, ← phOutputFeedback_stateMatrix (J := J) (R := R) (Q := Q) (g := g) k, hCdef]
        abel
      rw [hA, phCx_complexify_add, add_mulVec, heig, LTI.complexify_mul, ← mulVec_mulVec]
      have : LTI.complexify (k • C) *ᵥ v = 0 := by
        rw [show LTI.complexify (k • C) = (k : ℂ) • LTI.complexify C by
          ext i j; simp [LTI.complexify]]
        rw [Matrix.smul_mulVec, hCv, smul_zero]
      rw [this, mulVec_zero, add_zero]
    exact hv (phCx_eq_zero_of_isObservable hobs hAv hCv)

/-- Semantic form: the unforced closed loop `ẋ = (J − (R + k g gᵀ)) Q x` is exponentially
stable. -/
@[powerlib_domain] theorem phOutputFeedback_exponentiallyStable (hJ : Jᵀ = -J)
    (hR : R.PosSemidef) (hQ : Q.PosDef) (hk : 0 < k)
    (hobs : LinearSystems.IsObservable (linearStateMatrix J R Q) (gᵀ * Q)) :
    LTI.ExponentiallyStable ⟨linearStateMatrix J (R + k • (g * gᵀ)) Q⟩ :=
  LTI.exponentiallyStable_of_isHurwitz (phOutputFeedback_isHurwitz hJ hR hQ hk hobs)

end Feedback

end powerlib.PH
