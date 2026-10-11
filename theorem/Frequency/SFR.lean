import theorem.Frequency.SwingNadir
import theorem.Criteria.Routh3

/-! # Reheat-turbine system frequency response (SFR) model

Source: work-sync `theory/T-sfr-model.md` §1.2–§1.8 (turbine `G_turb`, governor, third-order
SFR transfer function §1.4, second-order reduction §1.5, nadir §1.6, RoCoF / steady state §1.7,
state-space form §1.8).

Model boundary (both models).
* Continuous-time, linear, small-signal single-area model (the note's "one equivalent machine"
  premise), Kundur per-unit: `Δω` per-unit, `M = M_eff = 2 H_eq` [s], powers in system-base
  per-unit, generation-side balance `M Δω̇ = ΔP_m − ΔP_L − D Δω` (load increase positive).
* Input (one port): load step `ΔP_L` (`SwingGovernor.load`); output `Δω`. No AGC
  (`ΔP_C = 0`), dead-band, rate limit, valve saturation, PLL, delay, PWM, voltage dynamics.
* Reheat steam turbine with `T_CH` neglected: `G_turb(s) = (1 + s F T_R)/(1 + s T_R)`
  (`F = F_HP`, `T_R = T_RH`); governor `T_g ΔṖ_v = −ΔP_v − K_R Δω`.

## Third-order model (`model`, state `x = (Δω, ΔP_m, ΔP_v)`)
State matrix (corrected §1.8)
`A = [[−D/M, 1/M, 0], [−F K_R/T_g, −1/T_R, 1/T_R − F/T_g], [−K_R/T_g, 0, −1/T_g]]`.
* `field_swing`, `field_governor`, `field_turbine`: the three rows are the swing equation, the
  governor, and the time-domain form `T_R ΔṖ_m + ΔP_m = ΔP_v + F T_R ΔṖ_v` of `G_turb`.
* `transfer_apply` (foundation): `LTI.transfer` equals the §1.4 third-order transfer function.
* `routhQuantity_eq`, `isHurwitz_iff`, `isHurwitz_of_hp_fraction`: with
  `a₃ = M T_g T_R`, `a₂ = M (T_g + T_R) + D T_g T_R`, `a₁ = M + D (T_g + T_R) + K_R F T_R`,
  `a₀ = D + K_R`, the Routh quantity is
  `a₂ a₁ − a₃ a₀ = M²(T_g+T_R) + M D (T_g+T_R)² + M K_R T_R [F (T_g+T_R) − T_g]
     + D² T_g T_R (T_g+T_R) + D K_R F T_g T_R²`,
  so `F ≥ T_g/(T_g + T_R)` (with `D, K_R ≥ 0`, `K_R + D > 0`) makes the model Hurwitz. The note
  states no stability condition; this one is added.
* `rocof`, `isEquilibrium_iff`, `exponentiallyConvergesTo_steadyState`, `tendsto_freq`
  (domain): initial RoCoF `−ΔP_L/M`; unique equilibrium
  `(−ΔP_L/(K_R+D), K_R ΔP_L/(K_R+D), K_R ΔP_L/(K_R+D))`; exponential convergence of every
  trajectory to it, `Δω → −ΔP_L/(K_R + D)` (§1.7).

## Second-order reduction (`reducedModel`, `T_g → 0`, state `x = (Δω, ΔP_RH)`)
The governor is static (`ΔP_v = −K_R Δω`) and `G_turb` is realised with the reheat (low
pressure) state `ΔP_RH = ΔP_m + F K_R Δω`, `T_R ΔṖ_RH = −ΔP_RH − (1 − F) K_R Δω`. The
reduction `T_g → 0` itself (a singular-perturbation limit) is not formalized: the reduced model
is a separate model, checked against the note's §1.5 equations and transfer function.
It is `SwingGovernor.model M (D + F K_R) ((1 − F) K_R) T_R`, so the exact nadir theorem of
`Frequency.SwingNadir` applies.
* `reduced_field_swing`, `reduced_field_turbine`, `reduced_transfer_apply`,
  `reduced_natFreq_sq`, `reduced_two_mul_dampingRatio_mul_natFreq`: the §1.5 equations,
  transfer function, `ω_n² = (K_R + D)/(M T_R)` and `2 ζ ω_n = (M + (D + K_R F) T_R)/(M T_R)`.
* `reduced_nadir` (domain): for `ζ < 1` and a load increase, `Δω` has its global minimum over
  `t ≥ 0` at `t_n = atan2(ω_d T_R, ζ ω_n T_R − 1)/ω_d` (`atan2(y, x) = arg (x + j y)`), is
  strictly decreasing before it, and the exact minimum is
  `−ΔP_L/(K_R + D) · [1 + √(1 − 2 ζ ω_n T_R + ω_n² T_R²) e^{−ζ ω_n t_n}]`.

Corrections.
* §1.8 state matrix: the note's second row `[−F K_R/(T_R T_g), −1/T_R, (1 − F)/T_R]` does not
  realise `G_turb`: its static gain is `−1/(D + K_R (1 − F + F/T_g))`
  (`noteModel_transfer_zero`) instead of the §1.4/§1.7 value `−1/(K_R + D)` (`transfer_zero`),
  so its transfer function differs from §1.4 whenever `K_R F (1 − T_g) ≠ 0`
  (`noteModel_transfer_ne`; `F/T_g` is also dimensionally inconsistent). The corrected second
  row is `[−F K_R/T_g, −1/T_R, 1/T_R − F/T_g]` (`field_turbine`, `transfer_apply`).
* §1.6 nadir time: the note's `t_n = arctan(ω_d T_R/(1 − ζ ω_n T_R))/ω_d` has the wrong sign
  in the denominator; whenever `ζ ω_n T_R > 1` it equals `−t_n < 0`
  (`noteNadirTime_eq_neg`). (Typical parameters `2H = 8 s`, `T_R = 7 s`, `F = 0.3`,
  `K_R = 20`, `D = 1` give `ζ ω_n T_R ≈ 3.6`; RK4 gives `t_n ≈ +2.20 s`, the note `−2.20 s`.)
* §1.6 states that the closed form needs the approximation `ζ ω_n ≪ 1/T_RH`; it does not:
  `reduced_nadir` is exact for the reduced model. The note's amplitude
  `α e^{−ζω_n t_n} sin(ω_d t_n + φ)` with `φ = ω_d t_n` is replaced by the exact
  `√(1 − 2 ζ ω_n T_R + ω_n² T_R²) e^{−ζ ω_n t_n}`.
-/

noncomputable section
namespace powerlib.Frequency.SFR
open Set Filter Matrix
open scoped Topology

open SwingGovernor (load)

/-- Corrected third-order reheat SFR model, state `(Δω, ΔP_m, ΔP_v)`. -/
def model (M D K F Tg TR : ℝ) : LTI.Model (Fin 3) (Fin 1) where
  A := !![-D / M, 1 / M, 0; -(F * K) / Tg, -1 / TR, 1 / TR - F / Tg; -K / Tg, 0, -1 / Tg]
  B := !![-1 / M; 0; 0]
  C := !![1, 0, 0]
  D := 0

/-- The state matrix printed in the note's §1.8 (second row as in the note). -/
def noteModel (M D K F Tg TR : ℝ) : LTI.Model (Fin 3) (Fin 1) where
  A := !![-D / M, 1 / M, 0; F / TR * (1 / Tg) * (-K), -1 / TR, (1 - F) / TR; -K / Tg, 0, -1 / Tg]
  B := !![-1 / M; 0; 0]
  C := !![1, 0, 0]
  D := 0

/-- Steady state `(−ΔP_L/(K_R+D), K_R ΔP_L/(K_R+D), K_R ΔP_L/(K_R+D))`. -/
def steadyState (D K ΔPL : ℝ) : Fin 3 → ℝ :=
  ![-ΔPL / (K + D), K * ΔPL / (K + D), K * ΔPL / (K + D)]

/-- Third-order denominator coefficients (`a₃ s³ + a₂ s² + a₁ s + a₀`). -/
def coeff3 (M Tg TR : ℝ) : ℝ := M * Tg * TR
def coeff2 (M D Tg TR : ℝ) : ℝ := M * (Tg + TR) + D * Tg * TR
def coeff1 (M D K F Tg TR : ℝ) : ℝ := M + D * (Tg + TR) + K * F * TR
def coeff0 (D K : ℝ) : ℝ := D + K

/-- Routh quantity `a₂ a₁ − a₃ a₀`. -/
def routhQuantity (M D K F Tg TR : ℝ) : ℝ :=
  coeff2 M D Tg TR * coeff1 M D K F Tg TR - coeff3 M Tg TR * coeff0 D K

variable {M D K F Tg TR ΔPL : ℝ}

@[powerlib_foundation] theorem field_apply (x : Fin 3 → ℝ) :
    (model M D K F Tg TR).field x (load ΔPL) =
      ![-D / M * x 0 + 1 / M * x 1 + -1 / M * ΔPL,
        -(F * K) / Tg * x 0 + -1 / TR * x 1 + (1 / TR - F / Tg) * x 2,
        -K / Tg * x 0 + -1 / Tg * x 2] := by
  ext i; fin_cases i <;>
    simp [LTI.Model.field, model, load, dotProduct, Fin.sum_univ_three]

/-- Swing row: `M Δω̇ = ΔP_m − ΔP_L − D Δω`. -/
@[powerlib_foundation] theorem field_swing (hM : M ≠ 0) (x : Fin 3 → ℝ) :
    M * (model M D K F Tg TR).field x (load ΔPL) 0 = x 1 - ΔPL - D * x 0 := by
  rw [field_apply]
  simp only [Fin.isValue, Matrix.cons_val_zero]
  field_simp
  ring

/-- Governor row: `T_g ΔṖ_v = −ΔP_v − K_R Δω`. -/
@[powerlib_foundation] theorem field_governor (hTg : Tg ≠ 0) (x : Fin 3 → ℝ) :
    Tg * (model M D K F Tg TR).field x (load ΔPL) 2 = -x 2 - K * x 0 := by
  rw [field_apply]
  simp only [Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  field_simp
  ring

/-- Turbine row: `T_R ΔṖ_m + ΔP_m = ΔP_v + F T_R ΔṖ_v`, the time-domain form of
`ΔP_m = (1 + s F T_R)/(1 + s T_R) ΔP_v`. -/
@[powerlib_foundation] theorem field_turbine (hTg : Tg ≠ 0) (hTR : TR ≠ 0) (x : Fin 3 → ℝ) :
    TR * (model M D K F Tg TR).field x (load ΔPL) 1 + x 1 =
      x 2 + F * TR * (model M D K F Tg TR).field x (load ΔPL) 2 := by
  rw [field_apply]
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  field_simp
  ring

/-! ## Transfer function (§1.4) -/

@[powerlib_foundation] theorem det_characteristicMatrix (hM : M ≠ 0) (hTg : Tg ≠ 0)
    (hTR : TR ≠ 0) (s : ℂ) :
    (M : ℂ) * Tg * TR * (LTI.characteristicMatrix (model M D K F Tg TR).A s).det =
      M * s * (1 + Tg * s) * (1 + TR * s) + D * (1 + Tg * s) * (1 + TR * s) +
        K * (1 + F * TR * s) := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hT' : (Tg : ℂ) ≠ 0 := by exact_mod_cast hTg
  have hR' : (TR : ℂ) ≠ 0 := by exact_mod_cast hTR
  simp [model, LTI.characteristicMatrix, Matrix.det_fin_three]
  field_simp
  ring

/-- §1.4: `Δω(s)/ΔP_L(s) = −(1 + s T_g)(1 + s T_R) /
(M s (1 + s T_g)(1 + s T_R) + D (1 + s T_g)(1 + s T_R) + K_R (1 + s F T_R))`
(both sides are `0` at the poles). -/
@[powerlib_foundation] theorem transfer_apply (hM : M ≠ 0) (hTg : Tg ≠ 0) (hTR : TR ≠ 0)
    (s : ℂ) :
    LTI.transfer (model M D K F Tg TR) s 0 0 =
      -((1 + Tg * s) * (1 + TR * s)) /
        (M * s * (1 + Tg * s) * (1 + TR * s) + D * (1 + Tg * s) * (1 + TR * s) +
          K * (1 + F * TR * s)) := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hT' : (Tg : ℂ) ≠ 0 := by exact_mod_cast hTg
  have hR' : (TR : ℂ) ≠ 0 := by exact_mod_cast hTR
  have hadj : (LTI.complexify (model M D K F Tg TR).C *
      (LTI.characteristicMatrix (model M D K F Tg TR).A s).adjugate *
        LTI.complexify (model M D K F Tg TR).B) 0 0 =
      -((s + 1 / TR) * (s + 1 / Tg)) / M := by
    simp [model, LTI.characteristicMatrix, Matrix.adjugate_fin_three, Matrix.mul_apply,
      Fin.sum_univ_three]
    field_simp
    ring
  have hD : LTI.complexify (model M D K F Tg TR).D 0 0 = 0 := by simp [model]
  rw [← det_characteristicMatrix hM hTg hTR, LTI.transfer_eq_adjugate]
  simp only [Matrix.add_apply, Matrix.smul_apply, hadj, hD, smul_eq_mul, add_zero]
  generalize (LTI.characteristicMatrix (model M D K F Tg TR).A s).det = d
  by_cases h : d = 0
  · simp [h]
  · field_simp
    ring

/-! ## Stability (Routh–Hurwitz) -/

@[powerlib_foundation] theorem routhQuantity_eq :
    routhQuantity M D K F Tg TR =
      M ^ 2 * (Tg + TR) + M * D * (Tg + TR) ^ 2 + M * K * TR * (F * (Tg + TR) - Tg) +
        D ^ 2 * Tg * TR * (Tg + TR) + D * K * F * Tg * TR ^ 2 := by
  unfold routhQuantity coeff3 coeff2 coeff1 coeff0
  ring

@[powerlib_foundation] theorem trace_A (hM : M ≠ 0) (hTg : Tg ≠ 0) (hTR : TR ≠ 0) :
    (model M D K F Tg TR).A.trace = -coeff2 M D Tg TR / coeff3 M Tg TR := by
  simp only [model, Matrix.trace_fin_three_of, coeff2, coeff3]
  field_simp
  ring

@[powerlib_foundation] theorem det_A (hM : M ≠ 0) (hTg : Tg ≠ 0) (hTR : TR ≠ 0) :
    (model M D K F Tg TR).A.det = -coeff0 D K / coeff3 M Tg TR := by
  simp only [model, Matrix.det_fin_three, coeff0, coeff3, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
  field_simp
  ring

@[powerlib_foundation] theorem principalMinorSum_A (hM : M ≠ 0) (hTg : Tg ≠ 0) (hTR : TR ≠ 0) :
    Criteria.principalMinorSum (model M D K F Tg TR).A =
      coeff1 M D K F Tg TR / coeff3 M Tg TR := by
  simp only [model, Criteria.principalMinorSum, coeff1, coeff3, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.head_fin_const]
  field_simp
  ring

/-- Routh–Hurwitz for the corrected SFR model: for `M, T_g, T_R > 0` it is Hurwitz iff
`a₂ > 0`, `a₀ = K_R + D > 0` and `a₂ a₁ > a₃ a₀`. -/
@[powerlib_foundation] theorem isHurwitz_iff (hM : 0 < M) (hTg : 0 < Tg) (hTR : 0 < TR) :
    LinearSystems.IsHurwitz (model M D K F Tg TR).A ↔
      0 < coeff2 M D Tg TR ∧ 0 < coeff0 D K ∧ 0 < routhQuantity M D K F Tg TR := by
  have h3 : 0 < coeff3 M Tg TR := by unfold coeff3; positivity
  rw [Criteria.isHurwitz_fin_three_iff, trace_A hM.ne' hTg.ne' hTR.ne',
    det_A hM.ne' hTg.ne' hTR.ne', principalMinorSum_A hM.ne' hTg.ne' hTR.ne']
  have e : -coeff2 M D Tg TR / coeff3 M Tg TR * (coeff1 M D K F Tg TR / coeff3 M Tg TR) <
      -coeff0 D K / coeff3 M Tg TR ↔ 0 < routhQuantity M D K F Tg TR := by
    unfold routhQuantity
    rw [div_mul_div_comm, div_lt_div_iff₀ (by positivity) h3]
    constructor <;> intro h <;> nlinarith
  rw [e, neg_div, neg_div, neg_lt_zero, neg_lt_zero, div_pos_iff_of_pos_right h3,
    div_pos_iff_of_pos_right h3]

/-- Added stability condition: `F ≥ T_g/(T_g + T_R)` with `D, K_R ≥ 0`, `K_R + D > 0`. -/
@[powerlib_foundation] theorem isHurwitz_of_hp_fraction (hM : 0 < M) (hTg : 0 < Tg)
    (hTR : 0 < TR) (hD : 0 ≤ D) (hK : 0 ≤ K) (hKD : 0 < K + D) (hF : Tg / (Tg + TR) ≤ F) :
    LinearSystems.IsHurwitz (model M D K F Tg TR).A := by
  rw [isHurwitz_iff hM hTg hTR, routhQuantity_eq]
  have hsum : 0 < Tg + TR := by linarith
  have hF' : Tg ≤ F * (Tg + TR) := by rwa [div_le_iff₀ hsum] at hF
  have hF0 : 0 ≤ F := le_trans (div_nonneg hTg.le hsum.le) hF
  refine ⟨by unfold coeff2; positivity, by unfold coeff0; linarith, ?_⟩
  have h1 : 0 < M ^ 2 * (Tg + TR) := by positivity
  have h2 : 0 ≤ M * D * (Tg + TR) ^ 2 := by positivity
  have h3 : 0 ≤ M * K * TR * (F * (Tg + TR) - Tg) :=
    mul_nonneg (by positivity) (by linarith)
  have h4 : 0 ≤ D ^ 2 * Tg * TR * (Tg + TR) := by positivity
  have h5 : 0 ≤ D * K * F * Tg * TR ^ 2 := by positivity
  linarith

/-! ## RoCoF, steady state, convergence (§1.7) -/

/-- §1.7: from rest, `Δω̇(0⁺) = −ΔP_L/M` (the turbine zero does not change the initial slope). -/
@[powerlib_domain] theorem rocof {x : ℝ → Fin 3 → ℝ}
    (hx : IsTrajectory (model M D K F Tg TR) (load ΔPL) x) (h0 : x 0 = 0) :
    HasDerivWithinAt (fun t => x t 0) (-ΔPL / M) (Ici 0) 0 := by
  have h := hasDerivWithinAt_pi.1 (hx 0 (Set.mem_Ici.2 le_rfl)) 0
  have hv : (StateSpacePassivity.system (model M D K F Tg TR)).field (x 0) (load ΔPL) 0 =
      -ΔPL / M := by
    change (model M D K F Tg TR).field (x 0) (load ΔPL) 0 = _
    rw [field_apply, h0]
    simp only [Fin.isValue, Matrix.cons_val_zero, Pi.zero_apply]
    ring
  rw [hv] at h
  exact h

/-- The equilibria for the load step are exactly the steady state. -/
@[powerlib_domain] theorem isEquilibrium_iff (hM : M ≠ 0) (hTg : Tg ≠ 0) (hTR : TR ≠ 0)
    (hKD : K + D ≠ 0) (e : Fin 3 → ℝ) :
    (model M D K F Tg TR).IsEquilibrium (load ΔPL) e ↔ e = steadyState D K ΔPL := by
  unfold LTI.Model.IsEquilibrium
  rw [field_apply]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, Pi.zero_apply] at h0 h1 h2
    field_simp at h0 h1 h2
    have e2 : e 2 = -(K * e 0) := by linarith
    have e1 : e 1 = e 2 := by
      rw [e2] at h1
      have : Tg * (e 1 + K * e 0) = 0 := by linear_combination -h1
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hTg
      · linarith
    have e0 : e 0 = -ΔPL / (K + D) := by
      field_simp
      rw [e1, e2] at h0
      linarith
    ext i; fin_cases i
    · simpa [steadyState] using e0
    · simp only [steadyState, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      rw [e1, e2, e0]; ring
    · simp only [steadyState, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons]
      rw [e2, e0]; ring
  · rintro rfl
    ext i; fin_cases i <;> simp [steadyState] <;> field_simp <;> ring

@[powerlib_domain] theorem steadyState_isEquilibrium (hM : M ≠ 0) (hTg : Tg ≠ 0)
    (hTR : TR ≠ 0) (hKD : K + D ≠ 0) :
    (model M D K F Tg TR).IsEquilibrium (load ΔPL) (steadyState D K ΔPL) :=
  (isEquilibrium_iff hM hTg hTR hKD _).2 rfl

/-- Every trajectory converges exponentially to the steady state when the Routh–Hurwitz
conditions of `isHurwitz_iff` hold. -/
@[powerlib_domain] theorem exponentiallyConvergesTo_steadyState (hM : 0 < M) (hTg : 0 < Tg)
    (hTR : 0 < TR) (h2 : 0 < coeff2 M D Tg TR) (hKD : 0 < K + D)
    (hR : 0 < routhQuantity M D K F Tg TR) :
    ExponentiallyConvergesTo (model M D K F Tg TR) (load ΔPL) (steadyState D K ΔPL) :=
  exponentiallyConvergesTo_of_isHurwitz
    (steadyState_isEquilibrium hM.ne' hTg.ne' hTR.ne' hKD.ne')
    ((isHurwitz_iff hM hTg hTR).2 ⟨h2, by unfold coeff0; linarith, hR⟩)

/-- §1.7 with the added sufficient condition `F ≥ T_g/(T_g + T_R)`:
`Δω(t) → −ΔP_L/(K_R + D)` exponentially along every trajectory. -/
@[powerlib_domain] theorem tendsto_freq (hM : 0 < M) (hTg : 0 < Tg) (hTR : 0 < TR)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hKD : 0 < K + D) (hF : Tg / (Tg + TR) ≤ F)
    {x : ℝ → Fin 3 → ℝ} (hx : IsTrajectory (model M D K F Tg TR) (load ΔPL) x) :
    Tendsto (fun t => x t 0) atTop (𝓝 (-ΔPL / (K + D))) :=
  tendsto_apply_of_exponentiallyConvergesTo
    (exponentiallyConvergesTo_of_isHurwitz
      (steadyState_isEquilibrium hM.ne' hTg.ne' hTR.ne' hKD.ne')
      (isHurwitz_of_hp_fraction hM hTg hTR hD hK hKD hF)) hx 0

/-! ## Correction: the note's §1.8 state matrix -/

/-- Transfer function of the corrected model at `s = 0` (static gain `−1/(K_R + D)`). -/
@[powerlib_foundation] theorem transfer_zero (hM : M ≠ 0) (hTg : Tg ≠ 0) (hTR : TR ≠ 0) :
    LTI.transfer (model M D K F Tg TR) 0 0 0 = -1 / ((D + K : ℝ) : ℂ) := by
  rw [transfer_apply hM hTg hTR]
  push_cast
  ring_nf

/-- The note's §1.8 matrix has static gain `−1/(D + K_R (1 − F + F/T_g))`. -/
@[powerlib_foundation] theorem noteModel_transfer_zero (hM : M ≠ 0) (hTg : Tg ≠ 0)
    (hTR : TR ≠ 0) :
    LTI.transfer (noteModel M D K F Tg TR) 0 0 0 =
      -1 / ((D + K * (1 - F + F / Tg) : ℝ) : ℂ) := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hT' : (Tg : ℂ) ≠ 0 := by exact_mod_cast hTg
  have hR' : (TR : ℂ) ≠ 0 := by exact_mod_cast hTR
  have hdet : (LTI.characteristicMatrix (noteModel M D K F Tg TR).A 0).det =
      ((D + K * (1 - F + F / Tg) : ℝ) : ℂ) / (M * Tg * TR) := by
    simp [noteModel, LTI.characteristicMatrix, Matrix.det_fin_three]
    field_simp
    ring
  have hadj : (LTI.complexify (noteModel M D K F Tg TR).C *
      (LTI.characteristicMatrix (noteModel M D K F Tg TR).A 0).adjugate *
        LTI.complexify (noteModel M D K F Tg TR).B) 0 0 = -1 / (M * Tg * TR) := by
    simp [noteModel, LTI.characteristicMatrix, Matrix.adjugate_fin_three, Matrix.mul_apply,
      Fin.sum_univ_three]
    field_simp
  have hD : LTI.complexify (noteModel M D K F Tg TR).D 0 0 = 0 := by simp [noteModel]
  rw [LTI.transfer_eq_adjugate]
  simp only [Matrix.add_apply, Matrix.smul_apply, hadj, hD, smul_eq_mul, add_zero, hdet]
  by_cases h : ((D + K * (1 - F + F / Tg) : ℝ) : ℂ) = 0
  · rw [h]; simp
  · field_simp

/-- Correction (§1.8): whenever `K_R F (1 − T_g) ≠ 0` the note's state matrix and the corrected
one have different transfer functions (already at `s = 0`), so the note's matrix does not
realise the §1.4 transfer function. -/
@[powerlib_foundation] theorem noteModel_transfer_ne (hM : M ≠ 0) (hTg : Tg ≠ 0) (hTR : TR ≠ 0)
    (hK : K ≠ 0) (hF : F ≠ 0) (hT1 : Tg ≠ 1) :
    LTI.transfer (noteModel M D K F Tg TR) 0 0 0 ≠ LTI.transfer (model M D K F Tg TR) 0 0 0 := by
  rw [noteModel_transfer_zero hM hTg hTR, transfer_zero hM hTg hTR]
  intro h
  have h1 : ((D + K * (1 - F + F / Tg) : ℝ) : ℂ) = ((D + K : ℝ) : ℂ) := by
    rwa [neg_div, neg_div, neg_inj, one_div, one_div, _root_.inv_inj] at h
  have h2 : D + K * (1 - F + F / Tg) = D + K := by exact_mod_cast h1
  have h3 : K * F * (1 - Tg) = 0 := by
    field_simp at h2
    linear_combination h2
  rcases mul_eq_zero.1 h3 with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact hK h
    · exact hF h
  · exact hT1 (by linarith)

/-! ## Second-order reduction (§1.5) and exact nadir (§1.6) -/

/-- Reduced SFR (`T_g → 0`), state `(Δω, ΔP_RH)` with `ΔP_RH = ΔP_m + F K_R Δω`. -/
def reducedModel (M D K F TR : ℝ) : LTI.Model (Fin 2) (Fin 1) :=
  SwingGovernor.model M (D + F * K) ((1 - F) * K) TR

/-- Reduced swing row: `M Δω̇ = ΔP_m − ΔP_L − D Δω` with `ΔP_m = ΔP_RH − F K_R Δω`. -/
@[powerlib_foundation] theorem reduced_field_swing (hM : M ≠ 0) (x : Fin 2 → ℝ) :
    M * (reducedModel M D K F TR).field x (load ΔPL) 0 =
      (x 1 - F * K * x 0) - ΔPL - D * x 0 := by
  rw [reducedModel, SwingGovernor.field_swing hM]
  ring

/-- Reduced turbine: with `ΔP_v = −K_R Δω` (static governor) and `ΔP_m = ΔP_RH − F K_R Δω`,
the field satisfies `T_R ΔṖ_m + ΔP_m = ΔP_v + F T_R ΔṖ_v`, i.e. `G_turb`. -/
@[powerlib_foundation] theorem reduced_field_turbine (hTR : TR ≠ 0) (x : Fin 2 → ℝ) :
    let f := (reducedModel M D K F TR).field x (load ΔPL)
    TR * (f 1 - F * K * f 0) + (x 1 - F * K * x 0) = -K * x 0 + F * TR * (-K * f 0) := by
  intro f
  have h := SwingGovernor.field_governor (M := M) (D := D + F * K) (K := (1 - F) * K)
    (ΔPL := ΔPL) hTR x
  change TR * ((SwingGovernor.model M (D + F * K) ((1 - F) * K) TR).field x (load ΔPL) 1 -
      F * K * (SwingGovernor.model M (D + F * K) ((1 - F) * K) TR).field x (load ΔPL) 0) +
      (x 1 - F * K * x 0) = -K * x 0 + F * TR * (-K *
        (SwingGovernor.model M (D + F * K) ((1 - F) * K) TR).field x (load ΔPL) 0)
  linear_combination h

/-- §1.5 transfer function `−(1 + T_R s)/(M T_R s² + (M + (D + K_R F) T_R) s + (K_R + D))`. -/
@[powerlib_foundation] theorem reduced_transfer_apply (hM : M ≠ 0) (hTR : TR ≠ 0) (s : ℂ) :
    LTI.transfer (reducedModel M D K F TR) s 0 0 =
      -(1 + (TR : ℂ) * s) / ((M : ℂ) * TR * s ^ 2 + (M + (D + K * F) * TR) * s + (K + D)) := by
  rw [reducedModel, SwingGovernor.transfer_apply hM hTR]
  push_cast
  ring_nf

/-- §1.5 boxed: `ω_n² = (K_R + D)/(M T_R)`. -/
@[powerlib_foundation] theorem reduced_natFreq_sq (hM : 0 < M) (hTR : 0 < TR)
    (hKD : 0 ≤ K + D) :
    SwingGovernor.natFreq M (D + F * K) ((1 - F) * K) TR ^ 2 = (K + D) / (M * TR) := by
  rw [SwingGovernor.natFreq_sq hM hTR (by linarith)]
  ring_nf

/-- §1.5 boxed: `2 ζ ω_n = (M + (D + K_R F) T_R)/(M T_R)`. -/
@[powerlib_foundation] theorem reduced_two_mul_dampingRatio_mul_natFreq (hM : 0 < M)
    (hTR : 0 < TR) (hKD : 0 < K + D) :
    2 * SwingGovernor.dampingRatio M (D + F * K) ((1 - F) * K) TR *
        SwingGovernor.natFreq M (D + F * K) ((1 - F) * K) TR =
      (M + (D + K * F) * TR) / (M * TR) := by
  rw [SwingGovernor.two_mul_dampingRatio_mul_natFreq hM hTR (by linarith)]
  ring_nf

/-- `arg (σ − 1/T_R + j ω_d) = arg (σ T_R − 1 + j ω_d T_R)` for `T_R > 0`. -/
@[powerlib_foundation] theorem arg_scale {σ ωd : ℝ} (hTR : 0 < TR) :
    Complex.arg ⟨σ - 1 / TR, ωd⟩ = Complex.arg ⟨σ * TR - 1, ωd * TR⟩ := by
  have h : (⟨σ - 1 / TR, ωd⟩ : ℂ) = ((1 / TR : ℝ) : ℂ) * ⟨σ * TR - 1, ωd * TR⟩ := by
    apply Complex.ext <;> simp <;> field_simp
  rw [h, Complex.arg_real_mul _ (by positivity)]

/-- `arg (x + j y) = arctan (y / x)` for `x > 0`. -/
@[powerlib_foundation] theorem arg_eq_arctan {x y : ℝ} (hx : 0 < x) :
    Complex.arg ⟨x, y⟩ = Real.arctan (y / x) := by
  have hz : (⟨x, y⟩ : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have habs : |Complex.arg ⟨x, y⟩| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hx)
  have hn : 0 < ‖(⟨x, y⟩ : ℂ)‖ := norm_pos_iff.2 hz
  have htan : Real.tan (Complex.arg ⟨x, y⟩) = y / x := by
    rw [Real.tan_eq_sin_div_cos, Complex.sin_arg, Complex.cos_arg hz]
    simp only
    field_simp
  rw [← htan, Real.arctan_tan (abs_lt.1 habs).1 (abs_lt.1 habs).2]

/-- The note's §1.6 nadir time `arctan(ω_d T_R/(1 − σ T_R))/ω_d`. -/
def noteNadirTime (σ ωd TR : ℝ) : ℝ := Real.arctan (ωd * TR / (1 - σ * TR)) / ωd

/-- Correction (§1.6): for `σ T_R > 1` (`σ = ζ ω_n`) the note's formula is the negative of the
true first-minimum time `arg (σ − 1/T_R + j ω_d)/ω_d`. -/
@[powerlib_foundation] theorem noteNadirTime_eq_neg {σ ωd : ℝ} (hTR : 0 < TR) (hωd : 0 < ωd)
    (h : 1 < σ * TR) :
    noteNadirTime σ ωd TR = -(Complex.arg ⟨σ - 1 / TR, ωd⟩ / ωd) ∧
      noteNadirTime σ ωd TR < 0 := by
  have harg : Complex.arg ⟨σ - 1 / TR, ωd⟩ = Real.arctan (ωd * TR / (σ * TR - 1)) := by
    rw [arg_scale hTR, arg_eq_arctan (by linarith)]
  have heq : noteNadirTime σ ωd TR = -(Complex.arg ⟨σ - 1 / TR, ωd⟩ / ωd) := by
    rw [harg, noteNadirTime, show ωd * TR / (1 - σ * TR) = -(ωd * TR / (σ * TR - 1)) by
      rw [← div_neg, neg_sub], Real.arctan_neg, neg_div]
  refine ⟨heq, ?_⟩
  rw [heq, neg_neg_iff_pos]
  exact SwingGovernor.tCrit_pos hωd

/-- Exact nadir value of the reduced model with the §1.5 parameters substituted. -/
@[powerlib_foundation] theorem reduced_nadirValue_eq :
    SwingGovernor.nadirValue M (D + F * K) ((1 - F) * K) TR ΔPL =
      -ΔPL / (K + D) * (1 + Real.sqrt (1 -
        2 * SwingGovernor.decayRate M (D + F * K) ((1 - F) * K) TR * TR +
          SwingGovernor.natFreq M (D + F * K) ((1 - F) * K) TR ^ 2 * TR ^ 2) *
        Real.exp (-(SwingGovernor.decayRate M (D + F * K) ((1 - F) * K) TR *
          SwingGovernor.nadirTime M (D + F * K) ((1 - F) * K) TR))) := by
  unfold SwingGovernor.nadirValue
  rw [show (1 - F) * K + (D + F * K) = K + D by ring]

/-- The reduced model's nadir time in the corrected §1.6 form
`t_n = atan2(ω_d T_R, ζ ω_n T_R − 1)/ω_d`. -/
@[powerlib_foundation] theorem reduced_nadirTime_eq (hTR : 0 < TR) :
    SwingGovernor.nadirTime M (D + F * K) ((1 - F) * K) TR =
      Complex.arg ⟨SwingGovernor.decayRate M (D + F * K) ((1 - F) * K) TR * TR - 1,
        SwingGovernor.dampedFreq M (D + F * K) ((1 - F) * K) TR * TR⟩ /
        SwingGovernor.dampedFreq M (D + F * K) ((1 - F) * K) TR := by
  unfold SwingGovernor.nadirTime
  rw [arg_scale hTR]

/-- §1.6 corrected and exact: for the reduced SFR model with `ζ < 1` and a load increase, from
rest, `Δω` decreases strictly up to `t_n = atan2(ω_d T_R, ζ ω_n T_R − 1)/ω_d > 0`, attains its
minimum over `t ≥ 0` there, and the minimum is
`−ΔP_L/(K_R + D)·[1 + √(1 − 2 ζ ω_n T_R + ω_n² T_R²) e^{−ζ ω_n t_n}]`. -/
@[powerlib_domain] theorem reduced_nadir (hM : 0 < M) (hTR : 0 < TR) (hD : 0 ≤ D + F * K)
    (hKD : 0 < K + D) (hP : 0 < ΔPL)
    (hζ : SwingGovernor.dampingRatio M (D + F * K) ((1 - F) * K) TR < 1)
    {x : ℝ → Fin 2 → ℝ} (hx : IsTrajectory (reducedModel M D K F TR) (load ΔPL) x)
    (h0 : x 0 = 0) :
    0 < SwingGovernor.nadirTime M (D + F * K) ((1 - F) * K) TR ∧
      StrictAntiOn (fun t => x t 0) (Icc 0 (SwingGovernor.nadirTime M (D + F * K) ((1 - F) * K) TR)) ∧
      IsMinOn (fun t => x t 0) (Ici 0) (SwingGovernor.nadirTime M (D + F * K) ((1 - F) * K) TR) ∧
      x (SwingGovernor.nadirTime M (D + F * K) ((1 - F) * K) TR) 0 =
        -ΔPL / (K + D) * (1 + Real.sqrt (1 -
          2 * SwingGovernor.decayRate M (D + F * K) ((1 - F) * K) TR * TR +
            SwingGovernor.natFreq M (D + F * K) ((1 - F) * K) TR ^ 2 * TR ^ 2) *
          Real.exp (-(SwingGovernor.decayRate M (D + F * K) ((1 - F) * K) TR *
            SwingGovernor.nadirTime M (D + F * K) ((1 - F) * K) TR))) := by
  have hKD' : 0 < (1 - F) * K + (D + F * K) := by linarith
  obtain ⟨h1, h2, h3, h4⟩ := SwingGovernor.nadir hM hTR hD hKD' hP hζ hx h0
  exact ⟨h1, h2, h3, h4.trans reduced_nadirValue_eq⟩

/-- Reduced model: from rest, `Δω̇(0⁺) = −ΔP_L/M` (§1.7). -/
@[powerlib_domain] theorem reduced_rocof {x : ℝ → Fin 2 → ℝ}
    (hx : IsTrajectory (reducedModel M D K F TR) (load ΔPL) x) (h0 : x 0 = 0) :
    HasDerivWithinAt (fun t => x t 0) (-ΔPL / M) (Ici 0) 0 :=
  SwingGovernor.rocof hx h0

/-- Reduced model: `Δω → −ΔP_L/(K_R + D)` along every trajectory (`0 ≤ D + F K_R`). -/
@[powerlib_domain] theorem reduced_tendsto_freq (hM : 0 < M) (hTR : 0 < TR) (hD : 0 ≤ D + F * K)
    (hKD : 0 < K + D) {x : ℝ → Fin 2 → ℝ}
    (hx : IsTrajectory (reducedModel M D K F TR) (load ΔPL) x) :
    Tendsto (fun t => x t 0) atTop (𝓝 (-ΔPL / (K + D))) := by
  have h := SwingGovernor.tendsto_freq hM hTR hD (by linarith : 0 < (1 - F) * K + (D + F * K)) hx
  rwa [show (1 - F) * K + (D + F * K) = K + D by ring] at h

end powerlib.Frequency.SFR
