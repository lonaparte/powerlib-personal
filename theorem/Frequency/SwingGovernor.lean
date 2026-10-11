import theorem.Frequency.Basic
import theorem.Criteria.Hurwitz2

/-! # Single-area swing + first-order governor (two-state frequency model)

Source: work-sync `theory/T-frequency-stability.md` §1.4–§1.8 (model §1.7/§1.8, RoCoF §1.5,
quasi-steady-state deviation §1.6, characteristic polynomial / `ω_n` / `ζ_n` §1.7, damping trend
§2.5).

Model boundary.
* Continuous-time, linear, small-signal model around a nominal operating point, Kundur
  per-unit form (`T-frequency-stability.md` "单位约定"): the frequency deviation `Δω` is
  dimensionless per-unit, `M = M_eff = 2 H_eff` [s], powers are system-base per-unit.
* State `x = (x 0, x 1) = (Δω, ΔP_m)`: COI frequency deviation and aggregated mechanical-power
  deviation. Input (one port, `Fin 1`): load step `ΔP_L` (load increase positive, i.e. the
  generation-side "export-positive" balance `M Δω̇ = ΔP_m − ΔP_L − D Δω`). Output: `Δω`.
* Swing `M Δω̇ = ΔP_m − ΔP_L − D Δω` (`D = D_eff`, damping including load damping and any
  linear virtual damping, already aggregated by `Frequency.Aggregation`), governor
  `T_g ΔṖ_m = −ΔP_m − K_R Δω` (aggregate droop gain `K_R = Σ 1/R_k`, one common `T_g`).
* Excluded: turbine/reheat dynamics (see `Frequency.SFR`), AGC, dead-bands, rate limits,
  valve saturation, converter inner loops, PLL, delays, PWM, voltage dynamics, nonlinear swing.
* Parameter ranges are stated per theorem (typically `0 < M`, `0 < T_g`, `0 ≤ D`,
  `0 < K_R + D`).

Results.
* `field_swing`, `field_governor`: the state equations are exactly the §1.7 pair.
* `transfer_apply` (foundation): `LTI.transfer` from `ΔP_L` to `Δω` is
  `−(1 + T_g s)/(M T_g s² + (M + D T_g) s + (D + K_R))` (§1.7).
* `det_characteristicMatrix_eq`: `det(sI − A) = s² + 2 ζ_n ω_n s + ω_n²` with the §1.7 boxed
  `ω_n`, `ζ_n`; `dampingRatio_strictAntiOn`: `ζ_n` strictly decreases in `K_R` (§2.5).
* `rocof` (domain): every trajectory starting at rest has `Δω̇(0⁺) = −ΔP_L / M_eff` (§1.5), and
  `rocof_hz` gives the Hz/s form `−ΔP_L f₀ / (2 H_eff)`.
* `isEquilibrium_iff` (domain): the unique equilibrium for the step `ΔP_L` is
  `(−ΔP_L/(K_R + D), K_R ΔP_L/(K_R + D))` (§1.6).
* `isHurwitz_iff`: for `0 < M`, `0 < T_g`, `0 ≤ D`, the state matrix is Hurwitz iff
  `0 < K_R + D` (no further condition).
* `exponentiallyConvergesTo_steadyState`, `tendsto_freq` (domain): every trajectory converges
  exponentially to that equilibrium; in particular `Δω(t) → −ΔP_L/(K_R + D)` (§1.6).
-/

noncomputable section
namespace powerlib.Frequency.SwingGovernor
open Set Filter Matrix
open scoped Topology

/-- Two-state swing + governor model, state `(Δω, ΔP_m)`, input/output `ΔP_L` / `Δω`. -/
def model (M D K Tg : ℝ) : LTI.Model (Fin 2) (Fin 1) where
  A := !![-D / M, 1 / M; -K / Tg, -1 / Tg]
  B := !![-1 / M; 0]
  C := !![1, 0]
  D := 0

/-- Constant load-step input `ΔP_L`. -/
def load (ΔPL : ℝ) : Fin 1 → ℝ := fun _ => ΔPL

/-- Quasi-steady state `(Δω^∞, ΔP_m^∞) = (−ΔP_L/(K_R + D), K_R ΔP_L/(K_R + D))`. -/
def steadyState (D K ΔPL : ℝ) : Fin 2 → ℝ := ![-ΔPL / (K + D), K * ΔPL / (K + D)]

/-- Undamped natural frequency `ω_n = √((D + K_R)/(M T_g))` (§1.7). -/
def natFreq (M D K Tg : ℝ) : ℝ := Real.sqrt ((D + K) / (M * Tg))

/-- Damping ratio `ζ_n = (M + D T_g)/(2 √(M T_g (D + K_R)))` (§1.7). -/
def dampingRatio (M D K Tg : ℝ) : ℝ := (M + D * Tg) / (2 * Real.sqrt (M * Tg * (D + K)))

variable {M D K Tg ΔPL : ℝ}

@[powerlib_foundation] theorem field_apply (x : Fin 2 → ℝ) :
    (model M D K Tg).field x (load ΔPL) =
      ![-D / M * x 0 + M⁻¹ * x 1 + -1 / M * ΔPL, -K / Tg * x 0 + -1 / Tg * x 1] := by
  ext i; fin_cases i <;> simp [LTI.Model.field, model, load, dotProduct, Fin.sum_univ_two]

/-- Swing row of the model: `M Δω̇ = ΔP_m − ΔP_L − D Δω`. -/
@[powerlib_foundation] theorem field_swing (hM : M ≠ 0) (x : Fin 2 → ℝ) :
    M * (model M D K Tg).field x (load ΔPL) 0 = x 1 - ΔPL - D * x 0 := by
  rw [field_apply]
  simp only [Fin.isValue, Matrix.cons_val_zero]
  field_simp
  ring

/-- Governor row of the model: `T_g ΔṖ_m = −ΔP_m − K_R Δω`. -/
@[powerlib_foundation] theorem field_governor (hTg : Tg ≠ 0) (x : Fin 2 → ℝ) :
    Tg * (model M D K Tg).field x (load ΔPL) 1 = -x 1 - K * x 0 := by
  rw [field_apply]
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
  field_simp
  ring

/-! ## Transfer function, characteristic polynomial, `ω_n`, `ζ_n` -/

/-- §1.7: `Δω(s)/ΔP_L(s) = −(1 + T_g s)/(M T_g s² + (M + D T_g) s + (D + K_R))`.
At the poles both sides are `0` (Lean's `x / 0 = 0`), so the identity holds for every `s`. -/
@[powerlib_foundation] theorem transfer_apply (hM : M ≠ 0) (hTg : Tg ≠ 0) (s : ℂ) :
    LTI.transfer (model M D K Tg) s 0 0 =
      -(1 + (Tg : ℂ) * s) / ((M : ℂ) * Tg * s ^ 2 + (M + D * Tg) * s + (D + K)) := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hT' : (Tg : ℂ) ≠ 0 := by exact_mod_cast hTg
  rw [LTI.transfer_eq_adjugate]
  simp [model, LTI.characteristicMatrix, Matrix.adjugate_fin_two, Matrix.det_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  have key : (M : ℂ) * Tg * s ^ 2 + (M + D * Tg) * s + (D + K) =
      M * Tg * ((s - -D / M) * (s - -1 / Tg) - (M : ℂ)⁻¹ * (-K / Tg)) := by
    field_simp
    ring
  rw [key]
  by_cases h : (s - -(D : ℂ) / M) * (s - -1 / Tg) - (M : ℂ)⁻¹ * (-K / Tg) = 0
  · simp [h]
  · field_simp
    ring

@[powerlib_foundation] theorem det_characteristicMatrix (s : ℂ) :
    (LTI.characteristicMatrix (model M D K Tg).A s).det =
      s ^ 2 + ((D / M + 1 / Tg : ℝ) : ℂ) * s + (((D + K) / (M * Tg) : ℝ) : ℂ) := by
  simp [model, LTI.characteristicMatrix, Matrix.det_fin_two]
  ring

@[powerlib_foundation] theorem natFreq_sq (hM : 0 < M) (hTg : 0 < Tg) (hKD : 0 ≤ D + K) :
    natFreq M D K Tg ^ 2 = (D + K) / (M * Tg) :=
  Real.sq_sqrt (div_nonneg hKD (mul_pos hM hTg).le)

@[powerlib_foundation] theorem natFreq_pos (hM : 0 < M) (hTg : 0 < Tg) (hKD : 0 < D + K) :
    0 < natFreq M D K Tg :=
  Real.sqrt_pos.2 (div_pos hKD (mul_pos hM hTg))

/-- `2 ζ_n ω_n = (M + D T_g)/(M T_g)` (§1.7 boxed). -/
@[powerlib_foundation] theorem two_mul_dampingRatio_mul_natFreq (hM : 0 < M) (hTg : 0 < Tg)
    (hKD : 0 < D + K) :
    2 * dampingRatio M D K Tg * natFreq M D K Tg = (M + D * Tg) / (M * Tg) := by
  have hMT : 0 < M * Tg := mul_pos hM hTg
  have hprod : 0 < M * Tg * (D + K) := mul_pos hMT hKD
  have h1 : Real.sqrt ((D + K) / (M * Tg)) * Real.sqrt (M * Tg * (D + K)) = D + K := by
    rw [← Real.sqrt_mul (div_nonneg hKD.le hMT.le)]
    rw [show (D + K) / (M * Tg) * (M * Tg * (D + K)) = (D + K) ^ 2 by field_simp]
    exact Real.sqrt_sq hKD.le
  have h2 : 0 < Real.sqrt (M * Tg * (D + K)) := Real.sqrt_pos.2 hprod
  have h3 : Real.sqrt (M * Tg * (D + K)) ^ 2 = M * Tg * (D + K) := Real.sq_sqrt hprod.le
  have hr : Real.sqrt ((D + K) / (M * Tg)) = Real.sqrt (M * Tg * (D + K)) / (M * Tg) := by
    rw [eq_div_iff hMT.ne']
    have : Real.sqrt ((D + K) / (M * Tg)) * (M * Tg) * Real.sqrt (M * Tg * (D + K)) =
        Real.sqrt (M * Tg * (D + K)) * Real.sqrt (M * Tg * (D + K)) := by
      rw [mul_right_comm, h1, ← sq, h3]; ring
    exact mul_right_cancel₀ h2.ne' this
  unfold dampingRatio natFreq
  rw [hr]
  field_simp

/-- §1.7 standard second-order form `det(sI − A) = s² + 2 ζ_n ω_n s + ω_n²`. -/
@[powerlib_foundation] theorem det_characteristicMatrix_eq (hM : 0 < M) (hTg : 0 < Tg)
    (hKD : 0 < D + K) (s : ℂ) :
    (LTI.characteristicMatrix (model M D K Tg).A s).det =
      s ^ 2 + ((2 * dampingRatio M D K Tg * natFreq M D K Tg : ℝ) : ℂ) * s +
        ((natFreq M D K Tg ^ 2 : ℝ) : ℂ) := by
  rw [det_characteristicMatrix, two_mul_dampingRatio_mul_natFreq hM hTg hKD,
    natFreq_sq hM hTg hKD.le]
  have : D / M + 1 / Tg = (M + D * Tg) / (M * Tg) := by
    field_simp
    ring
  rw [this]

/-- §2.5: the damping ratio strictly decreases as the droop gain `K_R` increases. -/
@[powerlib_foundation] theorem dampingRatio_strictAntiOn (hM : 0 < M) (hTg : 0 < Tg)
    (hD : 0 ≤ D) :
    StrictAntiOn (fun K => dampingRatio M D K Tg) (Ioi (-D)) := by
  intro K₁ h₁ K₂ h₂ hlt
  simp only [mem_Ioi] at h₁ h₂
  have hMT : 0 < M * Tg := mul_pos hM hTg
  have hnum : 0 < M + D * Tg := by nlinarith
  have hs₁ : 0 < Real.sqrt (M * Tg * (D + K₁)) := Real.sqrt_pos.2 (mul_pos hMT (by linarith))
  have hlt' : Real.sqrt (M * Tg * (D + K₁)) < Real.sqrt (M * Tg * (D + K₂)) :=
    Real.sqrt_lt_sqrt (mul_pos hMT (by linarith)).le
      (mul_lt_mul_of_pos_left (by linarith) hMT)
  exact div_lt_div_of_pos_left hnum (by positivity) (by linarith)

/-! ## Initial rate of change of frequency (§1.5) -/

/-- §1.5: from rest, the right derivative of `Δω` at `0⁺` is `−ΔP_L / M_eff`. -/
@[powerlib_domain] theorem rocof {x : ℝ → Fin 2 → ℝ}
    (hx : IsTrajectory (model M D K Tg) (load ΔPL) x) (h0 : x 0 = 0) :
    HasDerivWithinAt (fun t => x t 0) (-ΔPL / M) (Ici 0) 0 := by
  have h := hasDerivWithinAt_pi.1 (hx 0 (Set.mem_Ici.2 le_rfl)) 0
  have hv : (StateSpacePassivity.system (model M D K Tg)).field (x 0) (load ΔPL) 0 =
      -ΔPL / M := by
    change (model M D K Tg).field (x 0) (load ΔPL) 0 = _
    rw [field_apply, h0]
    simp only [Fin.isValue, Matrix.cons_val_zero, Pi.zero_apply]
    ring
  rw [hv] at h
  exact h

/-- §1.5 in Hz/s: with `f = f₀ (1 + Δω)` and `M_eff = 2 H_eff`,
`ḟ(0⁺) = −ΔP_L f₀ / (2 H_eff)`. -/
@[powerlib_domain] theorem rocof_hz {H f₀ : ℝ} {x : ℝ → Fin 2 → ℝ}
    (hx : IsTrajectory (model (2 * H) D K Tg) (load ΔPL) x) (h0 : x 0 = 0) :
    HasDerivWithinAt (fun t => f₀ * (1 + x t 0)) (-(ΔPL * f₀) / (2 * H)) (Ici 0) 0 := by
  have h := ((rocof hx h0).const_add 1).const_mul f₀
  convert h using 1
  ring

/-! ## Quasi-steady state and stability (§1.6) -/

/-- §1.6: the equilibria for the load step `ΔP_L` are exactly the quasi-steady state. -/
@[powerlib_domain] theorem isEquilibrium_iff (hM : M ≠ 0) (hTg : Tg ≠ 0) (hKD : K + D ≠ 0)
    (e : Fin 2 → ℝ) :
    (model M D K Tg).IsEquilibrium (load ΔPL) e ↔ e = steadyState D K ΔPL := by
  unfold LTI.Model.IsEquilibrium
  rw [field_apply]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
    field_simp at h0 h1
    have he1 : e 1 = -(K * e 0) := by linarith
    have he0 : e 0 = -ΔPL / (K + D) := by
      field_simp
      nlinarith
    ext i; fin_cases i
    · simpa [steadyState] using he0
    · simp only [steadyState, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [he1, he0]
      ring
  · rintro rfl
    ext i; fin_cases i
    · simp [steadyState]
      field_simp
      ring
    · simp [steadyState]
      field_simp
      ring

@[powerlib_domain] theorem steadyState_isEquilibrium (hM : M ≠ 0) (hTg : Tg ≠ 0)
    (hKD : K + D ≠ 0) : (model M D K Tg).IsEquilibrium (load ΔPL) (steadyState D K ΔPL) :=
  (isEquilibrium_iff hM hTg hKD _).2 rfl

/-- For `0 < M`, `0 < T_g`, `0 ≤ D`: Hurwitz iff `0 < K_R + D`. -/
@[powerlib_foundation] theorem isHurwitz_iff (hM : 0 < M) (hTg : 0 < Tg) (hD : 0 ≤ D) :
    LinearSystems.IsHurwitz (model M D K Tg).A ↔ 0 < K + D := by
  change LinearSystems.IsHurwitz !![-D / M, 1 / M; -K / Tg, -1 / Tg] ↔ _
  rw [Criteria.isHurwitz_fin_two_of_iff]
  have htr : -D / M + -1 / Tg < 0 := by
    have : 0 ≤ D / M := div_nonneg hD hM.le
    have : 0 < 1 / Tg := one_div_pos.2 hTg
    rw [neg_div, neg_div]
    linarith
  have hdet : -D / M * (-1 / Tg) - 1 / M * (-K / Tg) = (K + D) / (M * Tg) := by
    field_simp
    ring
  rw [hdet]
  constructor
  · rintro ⟨-, h⟩
    exact (div_pos_iff_of_pos_right (mul_pos hM hTg)).1 h
  · intro h
    exact ⟨htr, div_pos h (mul_pos hM hTg)⟩

/-- §1.6 at the trajectory level: every trajectory converges exponentially to the quasi-steady
state (unconditionally for `0 < M`, `0 < T_g`, `0 ≤ D`, `0 < K_R + D`). -/
@[powerlib_domain] theorem exponentiallyConvergesTo_steadyState (hM : 0 < M) (hTg : 0 < Tg)
    (hD : 0 ≤ D) (hKD : 0 < K + D) :
    ExponentiallyConvergesTo (model M D K Tg) (load ΔPL) (steadyState D K ΔPL) :=
  exponentiallyConvergesTo_of_isHurwitz
    (steadyState_isEquilibrium hM.ne' hTg.ne' hKD.ne') ((isHurwitz_iff hM hTg hD).2 hKD)

/-- §1.6 boxed: `Δω(t) → Δω^∞ = −ΔP_L/(K_R + D_eff)` along every trajectory. -/
@[powerlib_domain] theorem tendsto_freq (hM : 0 < M) (hTg : 0 < Tg) (hD : 0 ≤ D)
    (hKD : 0 < K + D) {x : ℝ → Fin 2 → ℝ} (hx : IsTrajectory (model M D K Tg) (load ΔPL) x) :
    Tendsto (fun t => x t 0) atTop (𝓝 (-ΔPL / (K + D))) :=
  tendsto_apply_of_exponentiallyConvergesTo
    (exponentiallyConvergesTo_steadyState hM hTg hD hKD) hx 0

end powerlib.Frequency.SwingGovernor
