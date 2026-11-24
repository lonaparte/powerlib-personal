import theorem.GridTiedConverter.GFM.VSMLPFLossy
import theorem.NormalForm.LyapunovCoefficient

/-! # The first Lyapunov coefficient of the VSM with a power filter on its Hopf boundary

Model boundary.
* State `x = (δ, ω, P_f) : Dynamics.State 3`, in this order (angle, frequency deviation, filtered
  power), continuous time, autonomous: `δ̇ = ω`, `M ω̇ = P_ref − P_f − D ω`,
  `Ṗ_f = ω_c (P(δ) − P_f)` (`HopfCoefficient.field`) with an arbitrary power–angle curve `P` of
  class `C³`, export-positive active power. The lossless curve `P = K₀ sin`
  (`theorem/GridTiedConverter/GFM/VSMLPF.lean`, `VSMLPF.field_eq_hopfField`) and the lossy curve
  `P = c₀ + A sin(· − α)` (`theorem/GridTiedConverter/GFM/VSMLPFLossy.lean`, read through
  `VSMLPFLossy.Model.field_eq_toVSMLPF`) are instances. Excluded as there: line dynamics,
  voltage / reactive-power loops, inner loops, limiting, PLL, delay, PWM.
* The operating point `(δ*, 0, P(δ*))` with `P_ref = P(δ*)`, physical range `M, D, ω_c > 0`, on
  the Hopf boundary `K = P'(δ*) = D ω_c + D²/M`, where the Jacobian has the eigenvalues
  `±iω₀`, `ω₀ = √(D ω_c / M)`, and `−(ω_c + D/M)`.
* Level: the value of Kuznetsov's first Lyapunov coefficient (`NormalForm.LyapunovCoefficient`)
  at the critical pair `hopfQ`, `hopfP` (angle component of `q` equal to `1`, `⟨p, q⟩ = 1`), a
  static quantity of the field at the point. Its sign is independent of the normalisation
  (`NormalForm.LyapunovCoefficient.sign_firstLyapunov_eq`); the behavioural conclusion of the
  lossless and lossy models on the boundary (local asymptotic stability) is proved in
  `theorem/GridTiedConverter/GFM/VSMLPFHopf.lean` and `VSMLPFLossy.lean` from the weak-focus
  coefficient, which the results here identify with `ℓ₁` up to a negative factor.

Source: study note `gfm/t3-bifurcation/REPORT-coord.md` (c) and its scripts `s3_hopf_l1.py`
(H1–H6), `s3b_display_check.py` (discovery evidence only); Kuznetsov, *Elements of Applied
Bifurcation Theory* (3rd ed.), §3.5 (first Lyapunov coefficient).

Results.
* `HopfCoefficient.field_eq_ridge`: the field is a one-nonlinearity field
  (`NormalForm.LyapunovCoefficient.ridge`) with the nonlinearity `ω_c P(δ)` in the filter row.
* `HopfCoefficient.isCriticalPair`: on the boundary `(hopfQ, hopfP)` is a critical pair at
  `ω₀ = √(D ω_c/M)`, `q = (1, iω₀, ω₀² M − iω₀ D)`.
* `HopfCoefficient.firstLyapunov_eq`: with `P'' = P''(δ*)`, `P''' = P'''(δ*)`,
  `ℓ₁ = M² ω₀ (D (D + Mω_c)(D² + 6DMω_c + M²ω_c²) P''' − M (D² + 10DMω_c + M²ω_c²) P''²) /
  (4 D² (D + Mω_c)(D² + 3DMω_c + M²ω_c²)(D² + 6DMω_c + M²ω_c²))`.
* `HopfCoefficient.firstLyapunov_eq_neg_mul_hopfCoeff`: `ℓ₁ = −c κ`, `c > 0`
  (`HopfCoefficient.hopfFactor_pos`), `κ = hopfCoeff H λ g₂ g₃` the weak-focus coefficient of
  `Dynamics.Degenerate.localAsymptoticStable_of_hopf_weakFocus` with `H = Dω_c/M`,
  `λ = ω_c + D/M`, `g₂ = ω_c P''/(2M)`, `g₃ = ω_c P'''/(6M)`.
* General curve (`HopfCoefficient.firstLyapunov_pos_iff`): `ℓ₁ > 0` (subcritical) iff
  `P''' > ρ P''²/K_H`, `K_H = Dω_c + D²/M`, `ρ = (8H + λ²)/(4H + λ²)`, and `1 < ρ < 2`
  (`HopfCoefficient.one_lt_rho`, `HopfCoefficient.rho_lt_two`).
* Lossless model (`VSMLPF.firstLyapunov_eq`, `VSMLPF.firstLyapunov_neg`): at a balanced angle on
  the boundary (`P'' = −P₀`, `P''' = −K`),
  `ℓ₁ = −M ω₀ (D²(D + Mω_c)²(D² + 6DMω_c + M²ω_c²) + M² P₀² (D² + 10DMω_c + M²ω_c²)) /
  (4 D² (D + Mω_c)(D² + 3DMω_c + M²ω_c²)(D² + 6DMω_c + M²ω_c²)) < 0`, and
  `VSMLPF.firstLyapunov_eq_neg_mul_hopfCoeff` with the coefficients `g₂ = −ω_c P₀/(2M)`,
  `g₃ = −ω_c K/(6M)` of `VSMLPF.mem_den_locallyAsymptoticallyStable_of_hopf`.
* Lossy model (`VSMLPFLossy.firstLyapunov_eq`, `VSMLPFLossy.firstLyapunov_neg`): the same with
  `P₀ = P_ref − c₀`; every physical lossy boundary model has `ℓ₁ < 0` (a supercritical Hopf
  point), at every load and line angle.
-/

noncomputable section
namespace powerlib.GFM
namespace HopfCoefficient
open Complex Matrix
open powerlib.Dynamics (State mk3 mk3_zero mk3_one mk3_two state3_ext)
open powerlib.NormalForm.LyapunovCoefficient

/-- The three-state VSM + power-filter field with an arbitrary power–angle curve `P`:
`δ̇ = ω`, `M ω̇ = P_ref − P_f − D ω`, `Ṗ_f = ω_c (P(δ) − P_f)`. -/
def field (M D ωc Pref : ℝ) (P : ℝ → ℝ) (x : State 3) : State 3 :=
  mk3 (x 1) ((Pref - x 2 - D * x 1) / M) (ωc * (P (x 0) - x 2))

/-- The operating point `(δ*, 0, P(δ*))`. -/
def point (P : ℝ → ℝ) (δ : ℝ) : State 3 := mk3 δ 0 (P δ)

/-- The linear part of `field`. -/
def lin (M D ωc : ℝ) : State 3 →L[ℝ] State 3 :=
  Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) !![0, 1, 0; 0, -D / M, -(1 / M); 0, 0, -ωc]

/-- The critical right eigenvector `q = (1, iω₀, ω₀² M − iω₀ D)` (angle component `1`). -/
def hopfQ (M D ω₀ : ℝ) : Fin 3 → ℂ :=
  ![1, (ω₀ : ℂ) * I, ((ω₀ ^ 2 * M : ℝ) : ℂ) + ((-(ω₀ * D) : ℝ) : ℂ) * I]

/-- The critical left eigenvector normalised by `⟨p, hopfQ⟩ = 1`
(`N = D⁴ + 3D²M²ω₀² + M⁴ω₀⁴`). -/
def hopfP (M D ω₀ : ℝ) : Fin 3 → ℂ :=
  let N := D ^ 4 + 3 * D ^ 2 * M ^ 2 * ω₀ ^ 2 + M ^ 4 * ω₀ ^ 4
  ![(((D ^ 2 + M ^ 2 * ω₀ ^ 2) ^ 2 / (2 * N) : ℝ) : ℂ) +
      ((D * M * ω₀ * (D ^ 2 + M ^ 2 * ω₀ ^ 2) / (2 * N) : ℝ) : ℂ) * I,
    ((D ^ 3 * M / (2 * N) : ℝ) : ℂ) +
      ((M ^ 2 * ω₀ * (2 * D ^ 2 + M ^ 2 * ω₀ ^ 2) / (2 * N) : ℝ) : ℂ) * I,
    ((D ^ 2 * M / (2 * N) : ℝ) : ℂ) +
      ((-(D * (D ^ 2 + M ^ 2 * ω₀ ^ 2)) / (2 * ω₀ * N) : ℝ) : ℂ) * I]

@[tmio M, powerlib_domain] theorem field_eq_ridge (M D ωc Pref : ℝ) (P : ℝ → ℝ) :
    field M D ωc Pref P =
      ridge (lin M D ωc) (mk3 0 (Pref / M) 0) (Dynamics.coord 0) (fun t => ωc * P t)
        (mk3 0 0 1) := by
  funext x
  apply state3_ext <;>
    simp [field, ridge, lin, Dynamics.toEuclideanCLM_apply3] <;> ring

@[tmio M, powerlib_domain] private theorem jacobianC_point {M D ωc Pref : ℝ} {P : ℝ → ℝ}
    (hP : ContDiff ℝ 3 P) (δ : ℝ) :
    jacobianC (field M D ωc Pref P) (point P δ) =
      (!![0, 1, 0; 0, -D / M, -(1 / M); ωc * deriv P δ, 0, -ωc] :
        Matrix (Fin 3) (Fin 3) ℝ).map (fun x => (x : ℂ)) := by
  have hφ : Differentiable ℝ (fun t => ωc * P t) :=
    (hP.differentiable (by norm_num)).const_mul ωc
  rw [field_eq_ridge, jacobianC_ridge _ _ _ _ hφ]
  ext k j
  fin_cases k <;> fin_cases j <;>
    simp [lin, point, basisVec, Dynamics.toEuclideanCLM_apply]

/-- The boundary data with `ω_c = M ω₀²/D` (so `ω₀² = D ω_c/M`). -/
@[tmio M, powerlib_domain] private theorem hopf_data {M D ω δ P2 P3 : ℝ} {P : ℝ → ℝ}
    (hM : 0 < M) (hD : 0 < D) (hω : 0 < ω) (hP : ContDiff ℝ 3 P)
    (hK : deriv P δ = D * (M * ω ^ 2 / D) + D ^ 2 / M) (h2 : iteratedDeriv 2 P δ = P2)
    (h3 : iteratedDeriv 3 P δ = P3) :
    IsCriticalPair (field M D (M * ω ^ 2 / D) (P δ) P) (point P δ) ω (hopfQ M D ω)
        (hopfP M D ω) ∧
      firstLyapunov (field M D (M * ω ^ 2 / D) (P δ) P) (point P δ) ω (hopfQ M D ω)
        (hopfP M D ω) =
      D * M ^ 2 * ω * (D ^ 6 * P3 + 7 * D ^ 4 * M ^ 2 * P3 * ω ^ 2 - D ^ 4 * M * P2 ^ 2 +
        7 * D ^ 2 * M ^ 4 * P3 * ω ^ 4 - 10 * D ^ 2 * M ^ 3 * P2 ^ 2 * ω ^ 2 +
        M ^ 6 * P3 * ω ^ 6 - M ^ 5 * P2 ^ 2 * ω ^ 4) /
        (4 * (D ^ 2 + M ^ 2 * ω ^ 2) * (D ^ 4 + 3 * D ^ 2 * M ^ 2 * ω ^ 2 + M ^ 4 * ω ^ 4) *
          (D ^ 4 + 6 * D ^ 2 * M ^ 2 * ω ^ 2 + M ^ 4 * ω ^ 4)) := by
  have hM0 : M ≠ 0 := hM.ne'
  have hD0 : D ≠ 0 := hD.ne'
  have hω0 : ω ≠ 0 := hω.ne'
  have hN3 : D ^ 4 + 3 * D ^ 2 * M ^ 2 * ω ^ 2 + M ^ 4 * ω ^ 4 ≠ 0 := by positivity
  have hN6 : D ^ 4 + 6 * D ^ 2 * M ^ 2 * ω ^ 2 + M ^ 4 * ω ^ 4 ≠ 0 := by positivity
  have hN1 : D ^ 2 + M ^ 2 * ω ^ 2 ≠ 0 := by positivity
  have hJ := jacobianC_point (M := M) (D := D) (ωc := M * ω ^ 2 / D) (Pref := P δ) hP δ
  rw [hK] at hJ
  refine ⟨⟨?_, hω, ?_, ?_, ?_⟩, ?_⟩
  · apply state3_ext <;> simp [field, point]
  · rw [hJ]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hopfQ, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (try refine ⟨?_, ?_⟩)
    all_goals (field_simp; try ring)
  · rw [hJ]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hopfP, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (try refine ⟨?_, ?_⟩)
    all_goals (field_simp; try ring)
  · simp [dotProduct, Fin.sum_univ_three, hopfP, hopfQ, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (try refine ⟨?_, ?_⟩)
    all_goals (field_simp; try ring)
  set r : Fin 3 → ℂ := ![((D / (ω ^ 2 * (D ^ 2 + M ^ 2 * ω ^ 2)) : ℝ) : ℂ), 0, 0]
  set s : Fin 3 → ℂ :=
    ![((D * (D ^ 2 + M ^ 2 * ω ^ 2) / (3 * ω ^ 2 * (D ^ 4 + 6 * D ^ 2 * M ^ 2 * ω ^ 2 +
        M ^ 4 * ω ^ 4)) : ℝ) : ℂ) +
      ((-(2 * D ^ 2 * M) / (3 * ω * (D ^ 4 + 6 * D ^ 2 * M ^ 2 * ω ^ 2 + M ^ 4 * ω ^ 4)) :
        ℝ) : ℂ) * I,
      ((4 * D ^ 2 * M / (3 * (D ^ 4 + 6 * D ^ 2 * M ^ 2 * ω ^ 2 + M ^ 4 * ω ^ 4)) : ℝ) : ℂ) +
      ((2 * D * (D ^ 2 + M ^ 2 * ω ^ 2) / (3 * ω * (D ^ 4 + 6 * D ^ 2 * M ^ 2 * ω ^ 2 +
        M ^ 4 * ω ^ 4)) : ℝ) : ℂ) * I,
      ((4 * D * M ^ 3 * ω ^ 2 / (3 * (D ^ 4 + 6 * D ^ 2 * M ^ 2 * ω ^ 2 + M ^ 4 * ω ^ 4)) :
        ℝ) : ℂ) +
      ((-(2 * D ^ 2 * (D ^ 2 + 5 * M ^ 2 * ω ^ 2)) / (3 * ω * (D ^ 4 + 6 * D ^ 2 * M ^ 2 *
        ω ^ 2 + M ^ 4 * ω ^ 4)) : ℝ) : ℂ) * I]
  have hdet : (jacobianC (field M D (M * ω ^ 2 / D) (P δ) P) (point P δ)).det =
      ((-(ω ^ 2 * (D ^ 2 + M ^ 2 * ω ^ 2) / (D * M)) : ℝ) : ℂ) := by
    rw [hJ, Matrix.det_fin_three]
    simp [Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    field_simp
    ring
  have hdet2 : (shift2 (jacobianC (field M D (M * ω ^ 2 / D) (P δ) P) (point P δ)) ω).det =
      ((-3 * ω ^ 2 * (M * ω ^ 2 / D + D / M) : ℝ) : ℂ) + ((-6 * ω ^ 3 : ℝ) : ℂ) * I := by
    rw [hJ, shift2, Matrix.det_fin_three]
    simp [Complex.ext_iff, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow,
      -Complex.ofReal_neg, -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (try refine ⟨?_, ?_⟩)
    all_goals (field_simp; try ring)
  have hr : jacobianC (field M D (M * ω ^ 2 / D) (P δ) P) (point P δ) *ᵥ r = toC (mk3 0 0 1) := by
    rw [hJ]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, r, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (field_simp; try ring)
  have hs : shift2 (jacobianC (field M D (M * ω ^ 2 / D) (P δ) P) (point P δ)) ω *ᵥ s =
      toC (mk3 0 0 1) := by
    rw [hJ, shift2]
    ext i; fin_cases i
    all_goals simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, s, Complex.ext_iff,
      -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg,
      -Complex.ofReal_sub, -Complex.ofReal_add, -Complex.ofReal_inv]
    all_goals (try refine ⟨?_, ?_⟩)
    all_goals (field_simp; try ring)
  have hu1 := hdet ▸ isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr
    (by have : 0 < ω ^ 2 * (D ^ 2 + M ^ 2 * ω ^ 2) / (D * M) := by positivity
        linarith : -(ω ^ 2 * (D ^ 2 + M ^ 2 * ω ^ 2) / (D * M)) ≠ 0))
  have hne : ((-3 * ω ^ 2 * (M * ω ^ 2 / D + D / M) : ℝ) : ℂ) + ((-6 * ω ^ 3 : ℝ) : ℂ) * I ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.zero_re] at h'
    have : 0 < 3 * ω ^ 2 * (M * ω ^ 2 / D + D / M) := by positivity
    linarith
  have hu2 := hdet2 ▸ isUnit_iff_ne_zero.mpr hne
  rw [field_eq_ridge] at hu1 hu2 hr hs ⊢
  rw [firstLyapunov_ridge _ _ _ _ (contDiff_const.mul hP) hu1 hu2 hr hs]
  simp only [point, Dynamics.coord_apply, mk3_zero, iteratedDeriv_const_mul_field, h2, h3]
  simp [funC, pairing_apply, Fin.sum_univ_three, basisVec, hopfQ, hopfP, r, s,
    Complex.mul_re, Complex.mul_im, pow_two, -Complex.ofReal_mul,
    -Complex.ofReal_div, -Complex.ofReal_pow, -Complex.ofReal_neg, -Complex.ofReal_sub,
    -Complex.ofReal_add, -Complex.ofReal_inv]
  field_simp
  ring

@[tmio M, powerlib_domain] private theorem freq {M D ωc : ℝ} (hM : 0 < M) (hD : 0 < D)
    (hωc : 0 < ωc) : 0 < √(D * ωc / M) ∧ ωc = M * √(D * ωc / M) ^ 2 / D := by
  refine ⟨Real.sqrt_pos.mpr (by positivity), ?_⟩
  rw [Real.sq_sqrt (by positivity)]
  field_simp

/-- On the Hopf boundary `P'(δ*) = D ω_c + D²/M` the pair `(hopfQ, hopfP)` is critical at
`ω₀ = √(D ω_c/M)`. -/
@[tmio M, powerlib_domain] theorem isCriticalPair {M D ωc δ : ℝ} {P : ℝ → ℝ} (hM : 0 < M)
    (hD : 0 < D) (hωc : 0 < ωc) (hP : ContDiff ℝ 3 P) (hK : deriv P δ = D * ωc + D ^ 2 / M) :
    IsCriticalPair (field M D ωc (P δ) P) (point P δ) √(D * ωc / M)
      (hopfQ M D √(D * ωc / M)) (hopfP M D √(D * ωc / M)) := by
  obtain ⟨hω, e⟩ := freq hM hD hωc
  generalize √(D * ωc / M) = ω at hω e ⊢
  subst e
  exact (hopf_data hM hD hω hP hK rfl rfl).1

/-- **The first Lyapunov coefficient on the Hopf boundary**, for an arbitrary power curve:
`ℓ₁ = M² ω₀ (D (D + Mω_c)(D² + 6DMω_c + M²ω_c²) P''' − M (D² + 10DMω_c + M²ω_c²) P''²) /
(4 D² (D + Mω_c)(D² + 3DMω_c + M²ω_c²)(D² + 6DMω_c + M²ω_c²))`, `ω₀ = √(Dω_c/M)`. -/
@[tmio M, powerlib_domain] theorem firstLyapunov_eq {M D ωc δ : ℝ} {P : ℝ → ℝ} (hM : 0 < M)
    (hD : 0 < D) (hωc : 0 < ωc) (hP : ContDiff ℝ 3 P) (hK : deriv P δ = D * ωc + D ^ 2 / M) :
    firstLyapunov (field M D ωc (P δ) P) (point P δ) √(D * ωc / M)
        (hopfQ M D √(D * ωc / M)) (hopfP M D √(D * ωc / M)) =
      M ^ 2 * √(D * ωc / M) * (D * (D + M * ωc) * (D ^ 2 + 6 * D * M * ωc + M ^ 2 * ωc ^ 2) *
          iteratedDeriv 3 P δ -
        M * (D ^ 2 + 10 * D * M * ωc + M ^ 2 * ωc ^ 2) * iteratedDeriv 2 P δ ^ 2) /
      (4 * D ^ 2 * (D + M * ωc) * (D ^ 2 + 3 * D * M * ωc + M ^ 2 * ωc ^ 2) *
        (D ^ 2 + 6 * D * M * ωc + M ^ 2 * ωc ^ 2)) := by
  obtain ⟨hω, e⟩ := freq hM hD hωc
  generalize √(D * ωc / M) = ω at hω e ⊢
  subst e
  rw [(hopf_data hM hD hω hP hK rfl rfl).2]
  have hM0 := hM.ne'
  have hD0 := hD.ne'
  have hω0 := hω.ne'
  have h1 : D + M * (M * ω ^ 2 / D) ≠ 0 := by positivity
  have h2 : D ^ 2 + 3 * D * M * (M * ω ^ 2 / D) + M ^ 2 * (M * ω ^ 2 / D) ^ 2 ≠ 0 := by positivity
  have h3 : D ^ 2 + 6 * D * M * (M * ω ^ 2 / D) + M ^ 2 * (M * ω ^ 2 / D) ^ 2 ≠ 0 := by positivity
  rw [div_eq_div_iff (by positivity) (by positivity)]
  field_simp
  ring

/-- The positive factor `c = M⁵/(2ω₀³(D + Mω_c)(D² + 3DMω_c + M²ω_c²)(D² + 6DMω_c + M²ω_c²))` of
`ℓ₁ = −c κ`. -/
def hopfFactor (M D ωc ω₀ : ℝ) : ℝ :=
  M ^ 5 / (2 * ω₀ ^ 3 * (D + M * ωc) * (D ^ 2 + 3 * D * M * ωc + M ^ 2 * ωc ^ 2) *
    (D ^ 2 + 6 * D * M * ωc + M ^ 2 * ωc ^ 2))

@[tmio M, powerlib_domain] theorem hopfFactor_pos {M D ωc ω₀ : ℝ} (hM : 0 < M) (hD : 0 < D)
    (hωc : 0 < ωc) (hω : 0 < ω₀) : 0 < hopfFactor M D ωc ω₀ := by
  unfold hopfFactor; positivity

/-- **`ℓ₁` and the weak-focus coefficient**: `ℓ₁ = −c κ`, `c = hopfFactor > 0`,
`κ = hopfCoeff H λ g₂ g₃` with `H = Dω_c/M`, `λ = ω_c + D/M`, `g₂ = ω_c P''/(2M)`,
`g₃ = ω_c P'''/(6M)` (`Dynamics.Degenerate.localAsymptoticStable_of_hopf_weakFocus`). -/
@[tmio M, powerlib_domain] theorem firstLyapunov_eq_neg_mul_hopfCoeff {M D ωc δ : ℝ}
    {P : ℝ → ℝ} (hM : 0 < M) (hD : 0 < D) (hωc : 0 < ωc) (hP : ContDiff ℝ 3 P)
    (hK : deriv P δ = D * ωc + D ^ 2 / M) :
    firstLyapunov (field M D ωc (P δ) P) (point P δ) √(D * ωc / M)
        (hopfQ M D √(D * ωc / M)) (hopfP M D √(D * ωc / M)) =
      -hopfFactor M D ωc √(D * ωc / M) *
        Dynamics.Degenerate.hopfCoeff (D * ωc / M) (ωc + D / M) (ωc * iteratedDeriv 2 P δ / (2 * M))
          (ωc * iteratedDeriv 3 P δ / (6 * M)) := by
  rw [firstLyapunov_eq hM hD hωc hP hK]
  obtain ⟨hω, e⟩ := freq hM hD hωc
  generalize √(D * ωc / M) = ω at hω e ⊢
  subst e
  have hM0 := hM.ne'
  have hD0 := hD.ne'
  have hω0 := hω.ne'
  have h1 : D + M * (M * ω ^ 2 / D) ≠ 0 := by positivity
  have h2 : D ^ 2 + 3 * D * M * (M * ω ^ 2 / D) + M ^ 2 * (M * ω ^ 2 / D) ^ 2 ≠ 0 := by positivity
  have h3 : D ^ 2 + 6 * D * M * (M * ω ^ 2 / D) + M ^ 2 * (M * ω ^ 2 / D) ^ 2 ≠ 0 := by positivity
  unfold hopfFactor Dynamics.Degenerate.hopfCoeff
  field_simp
  ring

/-- The threshold ratio `ρ = (8H + λ²)/(4H + λ²)`. -/
def rho (H lam : ℝ) : ℝ := (8 * H + lam ^ 2) / (4 * H + lam ^ 2)

@[tmio M, powerlib_domain] theorem one_lt_rho {H lam : ℝ} (hH : 0 < H) : 1 < rho H lam := by
  unfold rho
  rw [one_lt_div (by positivity)]
  linarith

@[tmio M, powerlib_domain] theorem rho_lt_two {H lam : ℝ} (hH : 0 < H) (hl : lam ≠ 0) :
    rho H lam < 2 := by
  unfold rho
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [sq_pos_of_ne_zero hl]

/-- **Subcritical criterion for a general power curve**: on the Hopf boundary `ℓ₁ > 0` iff
`P''' > ρ P''²/K_H`, `K_H = D ω_c + D²/M`, `ρ = rho (Dω_c/M) (ω_c + D/M) ∈ (1, 2)`. -/
@[tmio M, powerlib_domain] theorem firstLyapunov_pos_iff {M D ωc δ : ℝ} {P : ℝ → ℝ}
    (hM : 0 < M) (hD : 0 < D) (hωc : 0 < ωc) (hP : ContDiff ℝ 3 P)
    (hK : deriv P δ = D * ωc + D ^ 2 / M) :
    0 < firstLyapunov (field M D ωc (P δ) P) (point P δ) √(D * ωc / M)
        (hopfQ M D √(D * ωc / M)) (hopfP M D √(D * ωc / M)) ↔
      rho (D * ωc / M) (ωc + D / M) * iteratedDeriv 2 P δ ^ 2 / (D * ωc + D ^ 2 / M) <
        iteratedDeriv 3 P δ := by
  rw [firstLyapunov_eq_neg_mul_hopfCoeff hM hD hωc hP hK]
  have hc := hopfFactor_pos hM hD hωc (freq hM hD hωc).1
  set P2 := iteratedDeriv 2 P δ
  set P3 := iteratedDeriv 3 P δ
  have hKH : 0 < D * ωc + D ^ 2 / M := by positivity
  have hfac : 0 < ωc ^ 2 * (4 * (D * ωc / M) + (ωc + D / M) ^ 2) * (D * ωc + D ^ 2 / M) /
      (2 * M ^ 2) := by positivity
  have key : Dynamics.Degenerate.hopfCoeff (D * ωc / M) (ωc + D / M) (ωc * P2 / (2 * M))
      (ωc * P3 / (6 * M)) = ωc ^ 2 * (4 * (D * ωc / M) + (ωc + D / M) ^ 2) *
        (D * ωc + D ^ 2 / M) / (2 * M ^ 2) *
        (rho (D * ωc / M) (ωc + D / M) * P2 ^ 2 / (D * ωc + D ^ 2 / M) - P3) := by
    have hM0 := hM.ne'
    have h4 : 4 * (D * ωc / M) + (ωc + D / M) ^ 2 ≠ 0 := by positivity
    unfold Dynamics.Degenerate.hopfCoeff rho
    field_simp
    ring
  rw [key]
  constructor
  · intro h
    by_contra hx
    have hx := not_lt.mp hx
    nlinarith [mul_nonneg hc.le (mul_nonneg hfac.le (sub_nonneg.mpr hx))]
  · intro h
    nlinarith [mul_pos hc (mul_pos hfac (sub_pos.mpr h))]

end HopfCoefficient

namespace VSMLPF
open HopfCoefficient powerlib.NormalForm.LyapunovCoefficient
open powerlib.Dynamics (state3_ext)

/-- The lossless field is `HopfCoefficient.field` with the curve `P = K₀ sin`. Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem field_eq_hopfField (g : VSMLPF) :
    g.field = HopfCoefficient.field g.M g.D g.ωc g.P0 (fun t => g.K0 * Real.sin t) := by
  funext x
  apply state3_ext <;> simp [HopfCoefficient.field]

@[tmio M, powerlib_domain] private theorem sin_derivs (K0 t : ℝ) :
    deriv (fun t => K0 * Real.sin t) t = K0 * Real.cos t ∧
      iteratedDeriv 2 (fun t => K0 * Real.sin t) t = -(K0 * Real.sin t) ∧
      iteratedDeriv 3 (fun t => K0 * Real.sin t) t = -(K0 * Real.cos t) := by
  refine iteratedDeriv_of_hasDerivAt (φ1 := fun t => K0 * Real.cos t)
    (φ2 := fun t => -(K0 * Real.sin t)) (φ3 := fun t => -(K0 * Real.cos t)) (fun t => ?_)
    (fun t => ?_) (fun t => ?_) t
  · exact (Real.hasDerivAt_sin t).const_mul K0
  · exact ((Real.hasDerivAt_cos t).const_mul K0).congr_deriv (by ring)
  · exact ((Real.hasDerivAt_sin t).const_mul K0).neg

@[tmio M, powerlib_domain] private theorem model_field_eq (m : Model)
    (hb : m.g.K0 * Real.sin m.δ = m.g.P0) :
    m.field = fun z => HopfCoefficient.field m.g.M m.g.D m.g.ωc
      ((fun t => m.g.K0 * Real.sin t) m.δ) (fun t => m.g.K0 * Real.sin t)
      (z + HopfCoefficient.point (fun t => m.g.K0 * Real.sin t) m.δ) := by
  funext z
  simp only [Model.field, field_eq_hopfField, Model.point, HopfCoefficient.point, hb]

@[tmio M, powerlib_domain] private theorem contDiff_sin (K0 : ℝ) :
    ContDiff ℝ 3 (fun t => K0 * Real.sin t) := by fun_prop

/-- On the Hopf boundary `K = D ω_c + D²/M` (balanced, physical) `(hopfQ, hopfP)` is a critical
pair of the translated field at `ω₀ = √(Dω_c/M)`. -/
@[tmio M, powerlib_domain] theorem isCriticalPair (m : Model) (hp : Meets m .physical)
    (hb : Meets m .balanced) (hH : m.K = m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M) :
    IsCriticalPair m.field 0 √(m.g.D * m.g.ωc / m.g.M)
      (hopfQ m.g.M m.g.D √(m.g.D * m.g.ωc / m.g.M))
      (hopfP m.g.M m.g.D √(m.g.D * m.g.ωc / m.g.M)) := by
  obtain ⟨hM, hD, hω⟩ := hp
  rw [model_field_eq m hb, isCriticalPair_comp_add]
  exact HopfCoefficient.isCriticalPair hM hD hω (contDiff_sin _)
    (by rw [(sin_derivs _ _).1]; exact hH)

/-- **`ℓ₁` of the lossless model on its Hopf boundary**:
`ℓ₁ = −M ω₀ (D²(D + Mω_c)²(D² + 6DMω_c + M²ω_c²) + M² P₀² (D² + 10DMω_c + M²ω_c²)) /
(4 D² (D + Mω_c)(D² + 3DMω_c + M²ω_c²)(D² + 6DMω_c + M²ω_c²))`. -/
@[tmio M, powerlib_domain] theorem firstLyapunov_eq (m : Model) (hp : Meets m .physical)
    (hb : Meets m .balanced) (hH : m.K = m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M) :
    firstLyapunov m.field 0 √(m.g.D * m.g.ωc / m.g.M)
        (hopfQ m.g.M m.g.D √(m.g.D * m.g.ωc / m.g.M))
        (hopfP m.g.M m.g.D √(m.g.D * m.g.ωc / m.g.M)) =
      -(m.g.M * √(m.g.D * m.g.ωc / m.g.M) *
        (m.g.D ^ 2 * (m.g.D + m.g.M * m.g.ωc) ^ 2 *
            (m.g.D ^ 2 + 6 * m.g.D * m.g.M * m.g.ωc + m.g.M ^ 2 * m.g.ωc ^ 2) +
          m.g.M ^ 2 * m.g.P0 ^ 2 *
            (m.g.D ^ 2 + 10 * m.g.D * m.g.M * m.g.ωc + m.g.M ^ 2 * m.g.ωc ^ 2))) /
      (4 * m.g.D ^ 2 * (m.g.D + m.g.M * m.g.ωc) *
        (m.g.D ^ 2 + 3 * m.g.D * m.g.M * m.g.ωc + m.g.M ^ 2 * m.g.ωc ^ 2) *
        (m.g.D ^ 2 + 6 * m.g.D * m.g.M * m.g.ωc + m.g.M ^ 2 * m.g.ωc ^ 2)) := by
  obtain ⟨hM, hD, hω⟩ := hp
  obtain ⟨hd1, hd2, hd3⟩ := sin_derivs m.g.K0 m.δ
  rw [model_field_eq m hb, firstLyapunov_comp_add,
    HopfCoefficient.firstLyapunov_eq hM hD hω (contDiff_sin _) (by rw [hd1]; exact hH), hd2,
    hd3]
  have hK : m.g.K0 * Real.cos m.δ = m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M := hH
  rw [hK, show m.g.K0 * Real.sin m.δ = m.g.P0 from hb]
  have hM0 := hM.ne'
  have hD0 := hD.ne'
  rw [div_eq_div_iff (by positivity) (by positivity)]
  field_simp
  ring

/-- **Supercritical**: every balanced physical boundary model has `ℓ₁ < 0`. -/
@[tmio M, powerlib_domain] theorem firstLyapunov_neg (m : Model) (hp : Meets m .physical)
    (hb : Meets m .balanced) (hH : m.K = m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M) :
    firstLyapunov m.field 0 √(m.g.D * m.g.ωc / m.g.M)
        (hopfQ m.g.M m.g.D √(m.g.D * m.g.ωc / m.g.M))
        (hopfP m.g.M m.g.D √(m.g.D * m.g.ωc / m.g.M)) < 0 := by
  rw [firstLyapunov_eq m hp hb hH]
  obtain ⟨hM, hD, hω⟩ := hp
  have hw : 0 < √(m.g.D * m.g.ωc / m.g.M) := Real.sqrt_pos.mpr (by positivity)
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (by positivity)

/-- `ℓ₁ = −c κ` with `c = hopfFactor > 0` and `κ` the weak-focus coefficient with
`g₂ = −ω_c P₀/(2M)`, `g₃ = −ω_c K/(6M)`, the coefficients of
`VSMLPF.mem_den_locallyAsymptoticallyStable_of_hopf`. -/
@[tmio M, powerlib_domain] theorem firstLyapunov_eq_neg_mul_hopfCoeff (m : Model)
    (hp : Meets m .physical) (hb : Meets m .balanced)
    (hH : m.K = m.g.D * m.g.ωc + m.g.D ^ 2 / m.g.M) :
    firstLyapunov m.field 0 √(m.g.D * m.g.ωc / m.g.M)
        (hopfQ m.g.M m.g.D √(m.g.D * m.g.ωc / m.g.M))
        (hopfP m.g.M m.g.D √(m.g.D * m.g.ωc / m.g.M)) =
      -hopfFactor m.g.M m.g.D m.g.ωc √(m.g.D * m.g.ωc / m.g.M) *
        Dynamics.Degenerate.hopfCoeff (m.g.D * m.g.ωc / m.g.M) (m.g.ωc + m.g.D / m.g.M)
          (-(m.g.ωc / m.g.M * m.g.P0) / 2) (-(m.g.ωc / m.g.M * m.K) / 6) := by
  obtain ⟨hM, hD, hω⟩ := hp
  obtain ⟨hd1, hd2, hd3⟩ := sin_derivs m.g.K0 m.δ
  rw [model_field_eq m hb, firstLyapunov_comp_add,
    HopfCoefficient.firstLyapunov_eq_neg_mul_hopfCoeff hM hD hω (contDiff_sin _)
      (by rw [hd1]; exact hH), hd2, hd3, show m.g.K0 * Real.sin m.δ = m.g.P0 from hb]
  unfold Model.K
  congr 2 <;> field_simp

end VSMLPF

namespace VSMLPFLossy
open HopfCoefficient powerlib.NormalForm.LyapunovCoefficient

/-- **`ℓ₁` of the lossy model on its Hopf boundary** (`VSMLPF.firstLyapunov_eq` through
`VSMLPFLossy.Model.field_eq_toVSMLPF`): the lossless value with `P₀ = P_ref − c₀`. -/
@[tmio M, powerlib_domain] theorem firstLyapunov_eq (m : Model)
    (hp : 0 < m.p.M ∧ 0 < m.p.D ∧ 0 < m.p.ωc)
    (hb : m.p.c0 + m.p.A * Real.sin (m.δ - m.p.α) = m.p.Pref)
    (hH : m.K = m.p.D * m.p.ωc + m.p.D ^ 2 / m.p.M) :
    firstLyapunov m.field 0 √(m.p.D * m.p.ωc / m.p.M)
        (hopfQ m.p.M m.p.D √(m.p.D * m.p.ωc / m.p.M))
        (hopfP m.p.M m.p.D √(m.p.D * m.p.ωc / m.p.M)) =
      -(m.p.M * √(m.p.D * m.p.ωc / m.p.M) *
        (m.p.D ^ 2 * (m.p.D + m.p.M * m.p.ωc) ^ 2 *
            (m.p.D ^ 2 + 6 * m.p.D * m.p.M * m.p.ωc + m.p.M ^ 2 * m.p.ωc ^ 2) +
          m.p.M ^ 2 * (m.p.Pref - m.p.c0) ^ 2 *
            (m.p.D ^ 2 + 10 * m.p.D * m.p.M * m.p.ωc + m.p.M ^ 2 * m.p.ωc ^ 2))) /
      (4 * m.p.D ^ 2 * (m.p.D + m.p.M * m.p.ωc) *
        (m.p.D ^ 2 + 3 * m.p.D * m.p.M * m.p.ωc + m.p.M ^ 2 * m.p.ωc ^ 2) *
        (m.p.D ^ 2 + 6 * m.p.D * m.p.M * m.p.ωc + m.p.M ^ 2 * m.p.ωc ^ 2)) := by
  rw [Model.field_eq_toVSMLPF]
  exact VSMLPF.firstLyapunov_eq m.toVSMLPF hp
    (show m.p.A * Real.sin (m.δ - m.p.α) = m.p.Pref - m.p.c0 by linarith) hH

/-- **Supercritical on every lossy line**: every physical balanced lossy boundary model has
`ℓ₁ < 0`, at every load and line angle. -/
@[tmio M, powerlib_domain] theorem firstLyapunov_neg (m : Model)
    (hp : 0 < m.p.M ∧ 0 < m.p.D ∧ 0 < m.p.ωc)
    (hb : m.p.c0 + m.p.A * Real.sin (m.δ - m.p.α) = m.p.Pref)
    (hH : m.K = m.p.D * m.p.ωc + m.p.D ^ 2 / m.p.M) :
    firstLyapunov m.field 0 √(m.p.D * m.p.ωc / m.p.M)
        (hopfQ m.p.M m.p.D √(m.p.D * m.p.ωc / m.p.M))
        (hopfP m.p.M m.p.D √(m.p.D * m.p.ωc / m.p.M)) < 0 := by
  rw [Model.field_eq_toVSMLPF]
  exact VSMLPF.firstLyapunov_neg m.toVSMLPF hp
    (show m.p.A * Real.sin (m.δ - m.p.α) = m.p.Pref - m.p.c0 by linarith) hH

end VSMLPFLossy

end powerlib.GFM
