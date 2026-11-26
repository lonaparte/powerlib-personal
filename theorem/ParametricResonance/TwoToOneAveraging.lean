import theorem.ParametricResonance.PeriodicAveraging
import theorem.ParametricResonance.ResonantNormalForm

/-! # The 2:1 criterion as the first-order averaging limit of a two-state Floquet problem

For a two-state variational equation `ẋ = (A₀ + ε Re{A₁ e^{jω t}}) x` whose state matrix has the
synchronizing pair `λ = −σ + jΩ` with `σ = ε s` and `ω/2 − Ω = ε d` (damping and detuning of
order `ε`), the complete periodic system — including every non-resonant term — is Floquet stable
for all small `ε > 0` when the first-order slow flow is exponentially stable, and Floquet unstable
when the slow flow has an exponent with positive real part. This closes, for two states, the
averaging step between the source's 2:1 criterion and the Floquet multipliers.

Scope.
* Two states in the real modal form of the pair: `A₀ = !![−σ, −Ω; Ω, −σ]` (`base`; every real
  `2 × 2` matrix with eigenvalues `−σ ± jΩ` is similar to it by a constant real matrix, which
  changes neither the Floquet multipliers nor the pump coefficient, `Element.pump_similar`), with
  eigentriple `r = (1, −j)`, `u = (1, j)/2` (`base_right`, `base_left`, `base_normalized`).
* An arbitrary complex modulation matrix `A₁`, real modulation `Re{A₁ e^{jωt}}` (`modReal`),
  pump frequency `ω > 0`, period `T = 2π/ω`; `g = u A₁ r̄` (`Element.pump`), the source's `g_m`.
* The scaling `σ = ε s`, `ω/2 − Ω = ε d` (`full`) is the distinguished limit in which the
  first-order theory is asymptotically exact; statements hold for all sufficiently small `ε > 0`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1–§2.2 (`J_p = A₀ + ε Re{A₁ e^{jω_p t}}`, `g_m = l_mᴴ A₁ r_m*`,
"一阶平均给出 …，εA_m > 1 时 Floquet 指数进入右半平面"), [8, 9] of that report.

Results.
* `rot_conj` — `R(−φ/2) M R(φ/2)` splits into a commuting part and a reflection part rotated by
  `φ`.
* `stdForm_eq` — in the frame rotating at `ω/2` the system is `ẏ = ε F(t) y` with
  `F(t) = M_slow + cos(ωt) M₁ + sin(ωt) M₂ + cos(2ωt) M₃ + sin(2ωt) M₄`, where
  `M_slow = slowFlowMatrix s d (g/2)`; `integral_stdForm` — `∫₀ᵀ F = T M_slow`.
* `transition_full`, `monodromy_full` — `Φ_x(t, 0) = R(ωt/2) Φ_y(t, 0)`, so `Φ_x(T) = −Φ_y(T)`.
* `averaging_stable` — `s > 0` and `|g/2|² < s² + d²` give Schur-stable monodromy (all Floquet
  multipliers inside the unit circle) for all small `ε > 0`.
* `averaging_unstable` — `s < 0` or `s² + d² < |g/2|²` give Floquet instability for all small
  `ε > 0`. In the unscaled variables these are the source's `ε|g_m| ≶ 2√(σ_m² + Δ_m²)`.
-/

noncomputable section
namespace powerlib.ParametricResonance.TwoToOne

open Matrix Complex Set Filter Topology ComplexConjugate
open scoped Matrix.Norms.Operator
open NormalForm (rot quarter)

/-! ## The two-state modal model -/

/-- The real modal form of a pair `−σ ± jΩ`. -/
def base (σ Ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-σ, -Ω; Ω, -σ]

/-- The real modulation `Re{A₁ e^{jωt}}`. -/
def modReal (A : Matrix (Fin 2) (Fin 2) ℂ) (ω t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => (A i j).re * Real.cos (ω * t) - (A i j).im * Real.sin (ω * t)

/-- The full variational state matrix with `σ = ε s`, `Ω = ω/2 − ε d`. -/
def full (s d ω : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) (ε t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  base (ε * s) (ω / 2 - ε * d) + ε • modReal A ω t

/-- Right eigenvector `(1, −j)` of `λ = −σ + jΩ`. -/
def right : Fin 2 → ℂ := ![1, -I]

/-- Left eigenvector `(1, j)/2`. -/
def left : Fin 2 → ℂ := ![1 / 2, I / 2]

@[tmio T, powerlib_foundation] theorem base_right (σ Ω : ℝ) :
    Linear.complexify (base σ Ω) *ᵥ right = (-(σ : ℂ) + Ω * I) • right := by
  funext i; fin_cases i
  · simp [Linear.complexify, base, right, mulVec, dotProduct, Fin.sum_univ_two]
  · simp [Linear.complexify, base, right, mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination (Ω : ℂ) * I_sq

@[tmio T, powerlib_foundation] theorem base_left (σ Ω : ℝ) :
    vecMul left (Linear.complexify (base σ Ω)) = (-(σ : ℂ) + Ω * I) • left := by
  funext i; fin_cases i
  · simp [Linear.complexify, base, left, vecMul, dotProduct, Fin.sum_univ_two]
    ring
  · simp [Linear.complexify, base, left, vecMul, dotProduct, Fin.sum_univ_two]
    ring_nf; simp [I_sq]; ring

@[tmio T, powerlib_foundation] theorem base_normalized : left ⬝ᵥ right = 1 := by
  simp [left, right, dotProduct, Fin.sum_univ_two]
  ring_nf; simp [I_sq]; ring

/-- `g = u A₁ r̄ = (a₀₀ − a₁₁ + j(a₀₁ + a₁₀))/2`. -/
@[tmio T, powerlib_foundation] theorem pump_base (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Element.pump A left right = (A 0 0 - A 1 1 + I * (A 0 1 + A 1 0)) / 2 := by
  simp [Element.pump, left, right, mulVec, dotProduct, Fin.sum_univ_two]
  ring_nf; simp [I_sq]; ring

/-! ## The rotating frame -/

/-- The reflection `E₁ = diag(1, −1)`. -/
def refl1 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- The reflection `E₂`. -/
def refl2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- `R(−φ/2) M R(φ/2) = p I + q J + (c_r cos φ + c_i sin φ) E₁ + (c_i cos φ − c_r sin φ) E₂`. -/
@[tmio T, powerlib_foundation] theorem rot_conj (M : Matrix (Fin 2) (Fin 2) ℝ) (φ : ℝ) :
    rot (-(φ / 2)) * M * rot (φ / 2) =
      ((M 0 0 + M 1 1) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + ((M 1 0 - M 0 1) / 2) • quarter +
        ((M 0 0 - M 1 1) / 2 * Real.cos φ + (M 0 1 + M 1 0) / 2 * Real.sin φ) • refl1 +
        ((M 0 1 + M 1 0) / 2 * Real.cos φ - (M 0 0 - M 1 1) / 2 * Real.sin φ) • refl2 := by
  set θ := φ / 2 with hθ
  have hφ : φ = 2 * θ := by rw [hθ]; ring
  have hsc := Real.sin_sq_add_cos_sq θ
  rw [hφ, Real.cos_two_mul, Real.sin_two_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, quarter, refl1, refl2, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (M 1 1) * hsc
  · linear_combination (-(M 1 0)) * hsc
  · linear_combination (-(M 0 1)) * hsc
  · linear_combination (M 0 0) * hsc

@[tmio T, powerlib_foundation] theorem rot_mul_rot_neg (θ : ℝ) : rot θ * rot (-θ) = 1 := by
  have hsc := Real.sin_sq_add_cos_sq θ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot, quarter, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination hsc
  · ring
  · ring
  · linear_combination hsc

@[tmio T, powerlib_foundation] theorem base_comm_rot (σ Ω θ : ℝ) :
    base σ Ω * rot θ = rot θ * base σ Ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [base, rot, quarter, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The standard-form matrix `F(t) = M_slow(s, d, 0) + R(−ωt/2) Re{A₁ e^{jωt}} R(ωt/2)`. -/
def stdForm (s d ω : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  slowFlowMatrix s d 0 + rot (-(ω * t / 2)) * modReal A ω t * rot (ω * t / 2)

/-- `A_ε(t) R(ωt/2) = R(ωt/2)((ω/2) J + ε F(t))`. -/
@[tmio T, powerlib_foundation] theorem full_mul_rot (s d ω : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (ε t : ℝ) :
    full s d ω A ε t * rot (ω * t / 2) =
      rot (ω * t / 2) * ((ω / 2) • quarter + ε • stdForm s d ω A t) := by
  have hb : base (ε * s) (ω / 2 - ε * d) = (ω / 2) • quarter + ε • slowFlowMatrix s d 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [base, quarter, slowFlowMatrix] <;> ring
  have hr := rot_mul_rot_neg (ω * t / 2)
  have hm : modReal A ω t * rot (ω * t / 2) =
      rot (ω * t / 2) * (rot (-(ω * t / 2)) * modReal A ω t * rot (ω * t / 2)) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hr, Matrix.one_mul]
  calc full s d ω A ε t * rot (ω * t / 2)
      = base (ε * s) (ω / 2 - ε * d) * rot (ω * t / 2) + ε • (modReal A ω t * rot (ω * t / 2)) := by
        rw [full, Matrix.add_mul, Matrix.smul_mul]
    _ = rot (ω * t / 2) * ((ω / 2) • quarter + ε • slowFlowMatrix s d 0) +
        ε • (rot (ω * t / 2) * (rot (-(ω * t / 2)) * modReal A ω t * rot (ω * t / 2))) := by
        rw [base_comm_rot, hb, hm]
    _ = _ := by
        rw [stdForm]
        simp only [Matrix.mul_add, Matrix.mul_smul, smul_add]
        abel

@[tmio T, powerlib_foundation] theorem continuous_modReal (A : Matrix (Fin 2) (Fin 2) ℂ)
    (ω : ℝ) : Continuous (modReal A ω) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [modReal]
  fun_prop

@[tmio T, powerlib_foundation] theorem continuous_stdForm (s d ω : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) : Continuous (stdForm s d ω A) := by
  have h1 : Continuous fun t => rot (-(ω * t / 2)) := by unfold rot; fun_prop
  have h2 : Continuous fun t => rot (ω * t / 2) := by unfold rot; fun_prop
  exact continuous_const.add ((h1.mul (continuous_modReal A ω)).mul h2)

@[tmio T, powerlib_foundation] theorem continuous_full (s d ω : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) : Continuous (full s d ω A ε) :=
  continuous_const.add ((continuous_modReal A ω).const_smul ε)

@[tmio T, powerlib_foundation] theorem periodic_modReal (A : Matrix (Fin 2) (Fin 2) ℂ) {ω : ℝ}
    (hω : ω ≠ 0) : Function.Periodic (modReal A ω) (2 * Real.pi / ω) := by
  intro t
  have h : ω * (t + 2 * Real.pi / ω) = ω * t + 2 * Real.pi := by field_simp
  funext i j
  simp only [modReal, h, Real.cos_add_two_pi, Real.sin_add_two_pi]

@[tmio T, powerlib_foundation] theorem rot_add_pi (θ : ℝ) : rot (θ + Real.pi) = -rot θ := by
  simp [rot, Real.cos_add_pi, Real.sin_add_pi, neg_smul]
  abel

@[tmio T, powerlib_foundation] theorem rot_neg_add_pi (θ : ℝ) : rot (-(θ + Real.pi)) = -rot (-θ) := by
  rw [show -(θ + Real.pi) = -θ - Real.pi by ring]
  simp only [rot, Real.cos_sub_pi, Real.sin_sub_pi, neg_smul, neg_add]

@[tmio T, powerlib_foundation] theorem periodic_stdForm (s d : ℝ) {ω : ℝ} (hω : ω ≠ 0)
    (A : Matrix (Fin 2) (Fin 2) ℂ) : Function.Periodic (stdForm s d ω A) (2 * Real.pi / ω) := by
  intro t
  have h1 : ω * (t + 2 * Real.pi / ω) / 2 = ω * t / 2 + Real.pi := by field_simp
  rw [stdForm, stdForm, h1, rot_neg_add_pi, rot_add_pi, periodic_modReal A hω t]
  simp

@[tmio T, powerlib_foundation] theorem periodic_full (s d : ℝ) {ω : ℝ} (hω : ω ≠ 0)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Function.Periodic (full s d ω A ε) (2 * Real.pi / ω) := by
  intro t
  simp only [full, periodic_modReal A hω t]

/-- `Φ_x(t, 0) = R(ωt/2) Φ_y(t, 0)` for the standard-form system `ẏ = εF(t)y`. -/
@[tmio T, powerlib_foundation] theorem transition_full (s d : ℝ) {ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Periodic.transition (full s d ω A ε) t 0 =
      rot (ω * t / 2) * Periodic.transition (fun t => ε • stdForm s d ω A t) t 0 := by
  have hF : Continuous (fun t => ε • stdForm s d ω A t) :=
    (continuous_stdForm s d ω A).const_smul ε
  obtain ⟨B, hB⟩ := Periodic.exists_bound_of_periodic (continuous_full s d ω A ε)
    (periodic_full s d hω.ne' A ε) (by positivity)
  have hY : IsIntegralCurveOn
      (fun t => rot (ω * t / 2) * Periodic.transition (fun t => ε • stdForm s d ω A t) t 0)
      (Periodic.matField (full s d ω A ε)) (Ici 0) := by
    intro r _
    have h : HasDerivAt
        (fun t => rot (ω * t / 2) * Periodic.transition (fun t => ε • stdForm s d ω A t) t 0)
        ((ω / 2) • (rot (ω * r / 2) * quarter) *
            Periodic.transition (fun t => ε • stdForm s d ω A t) r 0 +
          rot (ω * r / 2) * ((ε • stdForm s d ω A r) *
            Periodic.transition (fun t => ε • stdForm s d ω A t) r 0)) r :=
      (NormalForm.hasDerivAt_rot ω r).mul (Dynamics.stm_hasDerivAt hF r 0)
    have key : (ω / 2) • (rot (ω * r / 2) * quarter) *
            Periodic.transition (fun t => ε • stdForm s d ω A t) r 0 +
          rot (ω * r / 2) * ((ε • stdForm s d ω A r) *
            Periodic.transition (fun t => ε • stdForm s d ω A t) r 0) =
        full s d ω A ε r *
          (rot (ω * r / 2) * Periodic.transition (fun t => ε • stdForm s d ω A t) r 0) := by
      calc _ = (rot (ω * r / 2) * ((ω / 2) • quarter + ε • stdForm s d ω A r)) *
            Periodic.transition (fun t => ε • stdForm s d ω A t) r 0 := by
            simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
              Matrix.mul_assoc]
        _ = (full s d ω A ε r * rot (ω * r / 2)) *
            Periodic.transition (fun t => ε • stdForm s d ω A t) r 0 := by rw [full_mul_rot]
        _ = _ := Matrix.mul_assoc _ _ _
    rw [key] at h
    exact h.hasDerivWithinAt
  have h := Periodic.transition_unique (continuous_full s d ω A ε) hB hY t ht
  simpa [rot, LinearSystems.stateTransitionMatrix_self] using h.symm

/-- The monodromy matrices: `Φ_x(T) = −Φ_y(T)`, `T = 2π/ω`. -/
@[tmio T, powerlib_foundation] theorem monodromy_full (s d : ℝ) {ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Periodic.monodromy (full s d ω A ε) (2 * Real.pi / ω) 0 =
      -Periodic.monodromy (fun t => ε • stdForm s d ω A t) (2 * Real.pi / ω) 0 := by
  rw [Periodic.monodromy, Periodic.monodromy, zero_add, transition_full s d hω A ε (by positivity)]
  have h : ω * (2 * Real.pi / ω) / 2 = Real.pi := by field_simp
  rw [h]
  simp [rot]

/-! ## The average of the standard form -/

/-- The trigonometric decomposition of the standard form. -/
@[tmio T, powerlib_foundation] theorem stdForm_eq (s d ω : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (t : ℝ) :
    stdForm s d ω A t = slowFlowMatrix s d (Element.pump A left right / 2) +
      Real.cos (ω * t) • ((((A 0 0).re + (A 1 1).re) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (((A 1 0).re - (A 0 1).re) / 2) • quarter) +
      Real.sin (ω * t) • ((-(((A 0 0).im + (A 1 1).im) / 2)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) -
        (((A 1 0).im - (A 0 1).im) / 2) • quarter) +
      Real.cos (2 * (ω * t)) •
        ((((A 0 0).re - (A 1 1).re + (A 0 1).im + (A 1 0).im) / 4) • refl1 +
          (((A 0 1).re + (A 1 0).re - (A 0 0).im + (A 1 1).im) / 4) • refl2) +
      Real.sin (2 * (ω * t)) •
        ((((A 0 1).re + (A 1 0).re - (A 0 0).im + (A 1 1).im) / 4) • refl1 -
          (((A 0 1).im + (A 1 0).im + (A 0 0).re - (A 1 1).re) / 4) • refl2) := by
  set φ := ω * t with hφ
  have hc := Real.cos_sq φ
  have hs : Real.sin φ ^ 2 = 1 / 2 - Real.cos (2 * φ) / 2 := by
    have := Real.sin_sq_add_cos_sq φ; linarith
  have hsc := Real.sin_two_mul φ
  rw [stdForm, show ω * t / 2 = φ / 2 by rw [hφ], rot_conj, pump_base]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modReal, slowFlowMatrix, quarter, refl1, refl2, ← hφ]
  · linear_combination ((A 0 0).re - (A 1 1).re) / 2 * hc -
      ((A 0 1).im + (A 1 0).im) / 2 * hs -
      (((A 0 1).re + (A 1 0).re) / 2 - ((A 0 0).im - (A 1 1).im) / 2) / 2 * hsc
  · linear_combination ((A 0 1).re + (A 1 0).re) / 2 * hc +
      ((A 0 0).im - (A 1 1).im) / 2 * hs +
      (((A 0 1).im + (A 1 0).im) / 2 + ((A 0 0).re - (A 1 1).re) / 2) / 2 * hsc
  · linear_combination ((A 0 1).re + (A 1 0).re) / 2 * hc +
      ((A 0 0).im - (A 1 1).im) / 2 * hs +
      (((A 0 1).im + (A 1 0).im) / 2 + ((A 0 0).re - (A 1 1).re) / 2) / 2 * hsc
  · linear_combination -((A 0 0).re - (A 1 1).re) / 2 * hc +
      ((A 0 1).im + (A 1 0).im) / 2 * hs +
      (((A 0 1).re + (A 1 0).re) / 2 - ((A 0 0).im - (A 1 1).im) / 2) / 2 * hsc

@[tmio T, powerlib_foundation] theorem integral_cos_mul_period {ω : ℝ} (hω : 0 < ω) (k : ℕ)
    (hk : k ≠ 0) :
    ∫ t in (0 : ℝ)..(2 * Real.pi / ω), Real.cos (k * (ω * t)) = 0 := by
  have hkω : (k : ℝ) * ω ≠ 0 := mul_ne_zero (by exact_mod_cast hk) hω.ne'
  have h := intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hkω
    (a := 0) (b := 2 * Real.pi / ω)
  rw [show (fun t => Real.cos (k * (ω * t))) = fun t => Real.cos (k * ω * t) by
    funext t; ring_nf, h, integral_cos]
  have : (k : ℝ) * ω * (2 * Real.pi / ω) = (k : ℝ) * (2 * Real.pi) := by field_simp
  rw [this, mul_zero, Real.sin_zero, sub_zero]
  have hs : Real.sin ((k : ℝ) * (2 * Real.pi)) = 0 := by
    rw [show (k : ℝ) * (2 * Real.pi) = ((2 * k : ℕ) : ℝ) * Real.pi by push_cast; ring]
    exact Real.sin_nat_mul_pi _
  rw [hs, smul_zero]

@[tmio T, powerlib_foundation] theorem integral_sin_mul_period {ω : ℝ} (hω : 0 < ω) (k : ℕ)
    (hk : k ≠ 0) :
    ∫ t in (0 : ℝ)..(2 * Real.pi / ω), Real.sin (k * (ω * t)) = 0 := by
  have hkω : (k : ℝ) * ω ≠ 0 := mul_ne_zero (by exact_mod_cast hk) hω.ne'
  have h := intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hkω
    (a := 0) (b := 2 * Real.pi / ω)
  rw [show (fun t => Real.sin (k * (ω * t))) = fun t => Real.sin (k * ω * t) by
    funext t; ring_nf, h, integral_sin]
  have : (k : ℝ) * ω * (2 * Real.pi / ω) = (k : ℝ) * (2 * Real.pi) := by field_simp
  rw [this, mul_zero, Real.cos_zero]
  have hc : Real.cos ((k : ℝ) * (2 * Real.pi)) = 1 := by
    rw [show (k : ℝ) * (2 * Real.pi) = (k : ℕ) * (2 * Real.pi) by rfl]
    exact Real.cos_nat_mul_two_pi k
  rw [hc, sub_self, smul_zero]

/-- `∫₀ᵀ F = T · slowFlowMatrix s d (g/2)`. -/
@[tmio T, powerlib_foundation] theorem integral_stdForm (s d : ℝ) {ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi / ω), stdForm s d ω A t =
      (2 * Real.pi / ω) • slowFlowMatrix s d (Element.pump A left right / 2) := by
  have hc1 := integral_cos_mul_period hω 1 one_ne_zero
  have hs1 := integral_sin_mul_period hω 1 one_ne_zero
  have hc2 := integral_cos_mul_period hω 2 two_ne_zero
  have hs2 := integral_sin_mul_period hω 2 two_ne_zero
  simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at hc1 hs1 hc2 hs2
  set T := 2 * Real.pi / ω
  set M0 := slowFlowMatrix s d (Element.pump A left right / 2)
  set M1 : Matrix (Fin 2) (Fin 2) ℝ := (((A 0 0).re + (A 1 1).re) / 2) • 1 +
    (((A 1 0).re - (A 0 1).re) / 2) • quarter
  set M2 : Matrix (Fin 2) (Fin 2) ℝ := (-(((A 0 0).im + (A 1 1).im) / 2)) • 1 -
    (((A 1 0).im - (A 0 1).im) / 2) • quarter
  set M3 : Matrix (Fin 2) (Fin 2) ℝ :=
    (((A 0 0).re - (A 1 1).re + (A 0 1).im + (A 1 0).im) / 4) • refl1 +
      (((A 0 1).re + (A 1 0).re - (A 0 0).im + (A 1 1).im) / 4) • refl2
  set M4 : Matrix (Fin 2) (Fin 2) ℝ :=
    (((A 0 1).re + (A 1 0).re - (A 0 0).im + (A 1 1).im) / 4) • refl1 -
      (((A 0 1).im + (A 1 0).im + (A 0 0).re - (A 1 1).re) / 4) • refl2
  have hfun : (fun t => stdForm s d ω A t) = fun t => M0 + Real.cos (ω * t) • M1 +
      Real.sin (ω * t) • M2 + Real.cos (2 * (ω * t)) • M3 + Real.sin (2 * (ω * t)) • M4 :=
    funext fun t => stdForm_eq s d ω A t
  rw [hfun, intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_smul_const, hc1, hs1, hc2, hs2]
  simp

/-! ## The averaging theorem -/

@[tmio T, powerlib_foundation] theorem exists_bound_stdForm (s d : ℝ) {ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) : ∃ M, 0 ≤ M ∧ ∀ t, ‖stdForm s d ω A t‖ ≤ M := by
  obtain ⟨M, hM⟩ := Periodic.exists_bound_of_periodic (continuous_stdForm s d ω A)
    (periodic_stdForm s d hω.ne' A) (by positivity)
  exact ⟨M, (norm_nonneg _).trans (hM 0), hM⟩

/-- First-order averaging, stability: `s > 0` and `|g/2|² < s² + d²` (slow flow exponentially
stable) give Schur-stable monodromy of the complete system for all small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem averaging_stable {s d ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hs : 0 < s)
    (hg : ‖Element.pump A left right / 2‖ ^ 2 < s ^ 2 + d ^ 2) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      LTI.SchurStable (Periodic.monodromy (full s d ω A ε) (2 * Real.pi / ω) 0) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_stdForm s d hω A
  have h := Averaging.averaging_schurStable (continuous_stdForm s d ω A) hM hM0 (by positivity)
    (integral_stdForm s d hω A) (by rw [trace_slowFlowMatrix]; linarith)
    (by rw [det_slowFlowMatrix]; linarith)
  filter_upwards [h] with ε hε
  rw [monodromy_full s d hω A ε, NormalForm.schurStable_neg_iff]
  exact hε

/-- First-order averaging, instability: `s < 0` or `s² + d² < |g/2|²` (a slow-flow exponent with
positive real part) give Floquet instability of the complete system for all small `ε > 0`. -/
@[tmio T, powerlib_foundation] theorem averaging_unstable {s d ω : ℝ} (hω : 0 < ω)
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (h : s < 0 ∨ s ^ 2 + d ^ 2 < ‖Element.pump A left right / 2‖ ^ 2) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Periodic.FloquetUnstable (full s d ω A ε) (2 * Real.pi / ω) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_stdForm s d hω A
  have hcond : 0 < (slowFlowMatrix s d (Element.pump A left right / 2)).trace ∨
      (slowFlowMatrix s d (Element.pump A left right / 2)).det < 0 := by
    rw [trace_slowFlowMatrix, det_slowFlowMatrix]
    rcases h with h | h
    · left; linarith
    · right; linarith
  have h' := Averaging.averaging_floquetUnstable (continuous_stdForm s d ω A) hM hM0
    (by positivity) (integral_stdForm s d hω A) hcond
  filter_upwards [h'] with ε hε
  obtain ⟨ρ, hρ, hρ1⟩ := hε
  refine ⟨-ρ, ?_, by rwa [norm_neg]⟩
  rw [monodromy_full s d hω A ε, LTI.mem_spectrum_iff_exists_eigvec]
  rw [LTI.mem_spectrum_iff_exists_eigvec] at hρ
  obtain ⟨v, hv, hρv⟩ := hρ
  refine ⟨v, hv, ?_⟩
  rw [Matrix.map_neg _ (fun a => map_neg (algebraMap ℝ ℂ) a), Matrix.neg_mulVec, hρv, neg_smul]

end powerlib.ParametricResonance.TwoToOne
