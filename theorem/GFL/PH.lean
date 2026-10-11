import theorem.GFL.PIPLL
import theorem.PH.Nonlinear

/-! # Port-Hamiltonian form of the reduced GFL PI-PLL (`T-gfl-ph`)

Model boundary (domain module). The system is `piPLLField h K_p K_i δω` of
`theorem/GFL/PIPLL.lean`: state `x = (θ, η)` (`x 0 = θ = θ̂_g − θ_g`, swing sign, `x 1 = η` PI
integrator), continuous time, `θ̇ = K_p h(θ) + K_i η − δω`, `η̇ = h(θ)`. Here `δω` is the port
input (allowed to be time-varying along trajectories, `u(t) = δω(t)`), `K_p ≥ 0`, `K_i` real,
`h` an arbitrary phase-detector characteristic with a chosen primitive `V`, `V' = −h`.
No current loop, LC, line, outer loop, saturation, delay or PWM dynamics (they are eliminated
in the form-B reduction, which is not formalized here). Power sign: `u y` is the power entering
through the port (incoming-positive, matching `theorem/PH/Nonlinear.lean`).

pH data (T-gfl-ph (1.2)): `H(θ, η) = V(θ) + (K_i / 2) η²`, `∇H = (−h(θ), K_i η)`,
`J = [[0, 1], [−1, 0]]`, `R = diag(K_p, 0) ⪰ 0`, `B = (−1, 0)ᵀ`, output `y = Bᵀ ∇H = h(θ)`.
* `gflPH_field`: `(J − R) ∇H + B δω` is exactly the PI-PLL field.
* `gflPH_power_balance`: `Ḣ = −K_p h² + h δω` at every state and input.
* `gflPH_trajectory_energy`: the same along every input/state trajectory; `storage` gives a
  `Passivity.DissipativeStorage` (no sign condition on `H`).
* Form-B characteristic `h = (1/(ω_g C_f)) [c₀ + c₁ sin θ + c₂ cos θ + c₃ sin 2θ + c₄ cos 2θ]`
  (`formBH`), its potential (1.4) (`formBPotential`, proved to be a primitive of `−h` and equal to
  `−∫₀^θ h`), and the fact that for `c₀ ≠ 0` the Hamiltonian is **unbounded below**
  (`formBHamiltonian_not_bddBelow`); hence for no constant `c` is `H − c` a nonnegative storage,
  and `PassiveWithStorage` cannot be obtained with storage `H − c`
  (`formB_not_passiveWithStorage`). This violates assumption 3 (`H ≥ H_min`) of the parent note
  `T-ph`, which `T-gfl-ph` §1.2 claims to inherit.

Source: work-sync `theory/T-gfl-ph.md` (1.1)–(1.4), §1.2 "复用 [[T-pll-ph]] 的所有结构性结论",
§1.3 bare-PLL degeneration; parent `theory/T-ph.md` assumption 3.
Correction (§1.2): "能量平衡与无源…无需重新证明" — the power balance holds, but passivity with a
nonnegative storage fails whenever `c₀ ≠ 0`: `H` contains `−c₀ θ / (ω_g C_f)`.
Correction (§1.3): the bare-PLL degeneration `c₁ = −V_g` gives `h = −V_g sin θ / (ω_g C_f)`, not
`−V_g sin θ`; the correct choice is `c₁ = −V_g ω_g C_f` (`formBH_barePLL`).
-/

noncomputable section
namespace powerlib.GFL
open Matrix Set
open powerlib.Dynamics (State)

/-! ## The pH model -/

/-- The port-Hamiltonian model of the reduced PI-PLL with phase detector `h` and a primitive `V`
of `−h`. -/
def gflPHModel (h V : ℝ → ℝ) (hV : ∀ θ, HasDerivAt V (-h θ) θ) (Kp Ki : ℝ) (hKp : 0 ≤ Kp) :
    PH.NonlinearModel 2 1 where
  J := fun _ => !![0, 1; -1, 0]
  R := fun _ => Matrix.diagonal ![Kp, 0]
  g := fun _ => !![-1; 0]
  H := fun x => V (x 0) + Ki / 2 * x 1 ^ 2
  dH := fun x => piPLLState (-h (x 0)) (Ki * x 1)
  skew := by
    intro _
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  dissipation_posSemidef := by
    intro _
    refine Matrix.PosSemidef.diagonal ?_
    intro i
    fin_cases i
    · simpa using hKp
    · simp
  hasGradient := by
    intro x
    set π0 : State 2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0
    set π1 : State 2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
    have h0 : HasFDerivAt (fun z : State 2 => z 0) π0 x := π0.hasFDerivAt
    have h1 : HasFDerivAt (fun z : State 2 => z 1) π1 x := π1.hasFDerivAt
    have hp := (hV (x 0)).comp_hasFDerivAt x h0
    have hq := (h1.pow 2).const_mul (Ki / 2)
    have hH := hp.add hq
    refine PH.hasGradientAt_of_hasFDerivAt hH ?_
    intro v
    simp [π0, π1, dotProduct, Fin.sum_univ_two, piPLLState]
    ring

variable {h V : ℝ → ℝ} {hV : ∀ θ, HasDerivAt V (-h θ) θ} {Kp Ki : ℝ} {hKp : 0 ≤ Kp}

@[simp, powerlib_foundation] theorem gflPHModel_H (x : State 2) :
    (gflPHModel h V hV Kp Ki hKp).H x = V (x 0) + Ki / 2 * x 1 ^ 2 := rfl

/-- `(J − R) ∇H + B δω` equals the PI-PLL field: T-gfl-ph (1.1) ⇔ (1.2). -/
@[powerlib_domain] theorem gflPH_field (x : State 2) (δω : ℝ) :
    (gflPHModel h V hV Kp Ki hKp).field x ![δω] = piPLLField h Kp Ki δω x := by
  rw [state_two_ext_iff]
  simp [PH.NonlinearModel.field, gflPHModel, piPLLState, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  constructor

/-- The output is the phase-detector signal `y = h(θ)`. -/
@[powerlib_foundation] theorem gflPH_output (x : State 2) :
    (gflPHModel h V hV Kp Ki hKp).output x = ![h (x 0)] := by
  ext i
  fin_cases i
  simp [PH.NonlinearModel.output, gflPHModel, piPLLState, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

@[powerlib_foundation] theorem gflPH_supply (x : State 2) (δω : ℝ) :
    (gflPHModel h V hV Kp Ki hKp).supply x ![δω] = h (x 0) * δω := by
  simp [PH.NonlinearModel.supply, gflPH_output, dotProduct]
  ring

@[powerlib_foundation] theorem gflPH_dampingPower (x : State 2) :
    (gflPHModel h V hV Kp Ki hKp).dampingPower x = Kp * h (x 0) ^ 2 := by
  simp [PH.NonlinearModel.dampingPower, gflPHModel, piPLLState, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.diagonal]
  ring

/-- Energy balance `Ḣ = −K_p h² + h δω` (T-gfl-ph §1.2). -/
@[powerlib_domain] theorem gflPH_power_balance (x : State 2) (δω : ℝ) :
    fderiv ℝ (gflPHModel h V hV Kp Ki hKp).H x (piPLLField h Kp Ki δω x) =
      -(Kp * h (x 0) ^ 2) + h (x 0) * δω := by
  rw [← gflPH_field (hV := hV) (hKp := hKp), PH.NonlinearModel.power_balance, gflPH_supply,
    gflPH_dampingPower]
  ring

/-- Along every input/state trajectory (input `u(t) = (δω(t))`), for `t ≥ 0`:
`d/dt H(x(t)) = −K_p h(θ(t))² + h(θ(t)) δω(t)`. -/
@[powerlib_domain] theorem gflPH_trajectory_energy {u : ℝ → (Fin 1 → ℝ)} {x : ℝ → State 2}
    (hx : Passivity.IsTrajectory (gflPHModel h V hV Kp Ki hKp).toSystem u x) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun τ => (gflPHModel h V hV Kp Ki hKp).H (x τ))
      (-(Kp * h ((x t) 0) ^ 2) + h ((x t) 0) * u t 0) (Ici 0) t := by
  have hd := (gflPHModel h V hV Kp Ki hKp).trajectory_energy_derivative hx ht
  have hu : u t = ![u t 0] := by
    ext i
    fin_cases i
    rfl
  rw [hu, gflPH_supply, gflPH_dampingPower] at hd
  convert hd using 1
  ring

/-! ## Form-B characteristic and its potential (T-gfl-ph (1.3)–(1.4)) -/

/-- `h(θ) = (1/(ω_g C_f)) [c₀ + c₁ sin θ + c₂ cos θ + c₃ sin 2θ + c₄ cos 2θ]` (T-gfl-ph (1.3)). -/
def formBH (ωg Cf c₀ c₁ c₂ c₃ c₄ : ℝ) (θ : ℝ) : ℝ :=
  1 / (ωg * Cf) * (c₀ + c₁ * Real.sin θ + c₂ * Real.cos θ + c₃ * Real.sin (2 * θ) +
    c₄ * Real.cos (2 * θ))

/-- The potential (1.4): `(1/(ω_g C_f)) [−c₀θ + c₁(cos θ − 1) − c₂ sin θ
+ (c₃/2)(cos 2θ − 1) − (c₄/2) sin 2θ]`. -/
def formBPotential (ωg Cf c₀ c₁ c₂ c₃ c₄ : ℝ) (θ : ℝ) : ℝ :=
  1 / (ωg * Cf) * (-c₀ * θ + c₁ * (Real.cos θ - 1) - c₂ * Real.sin θ +
    c₃ / 2 * (Real.cos (2 * θ) - 1) - c₄ / 2 * Real.sin (2 * θ))

/-- (1.4) is a primitive of `−h`. -/
@[powerlib_foundation] theorem hasDerivAt_formBPotential (ωg Cf c₀ c₁ c₂ c₃ c₄ θ : ℝ) :
    HasDerivAt (formBPotential ωg Cf c₀ c₁ c₂ c₃ c₄) (-formBH ωg Cf c₀ c₁ c₂ c₃ c₄ θ) θ := by
  have h2 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h := (((((hasDerivAt_id θ).const_mul (-c₀)).add
    (((Real.hasDerivAt_cos θ).sub_const 1).const_mul c₁)).sub
    ((Real.hasDerivAt_sin θ).const_mul c₂)).add
    ((((Real.hasDerivAt_cos (2 * θ)).comp θ h2).sub_const 1).const_mul (c₃ / 2))).sub
    (((Real.hasDerivAt_sin (2 * θ)).comp θ h2).const_mul (c₄ / 2))
  have h' := h.const_mul (1 / (ωg * Cf))
  refine HasDerivAt.congr_deriv h' ?_
  simp only [formBH]
  ring

@[powerlib_foundation] theorem formBPotential_zero (ωg Cf c₀ c₁ c₂ c₃ c₄ : ℝ) :
    formBPotential ωg Cf c₀ c₁ c₂ c₃ c₄ 0 = 0 := by
  simp [formBPotential]

@[powerlib_foundation] theorem continuous_formBH (ωg Cf c₀ c₁ c₂ c₃ c₄ : ℝ) :
    Continuous (formBH ωg Cf c₀ c₁ c₂ c₃ c₄) := by
  unfold formBH
  fun_prop

/-- (1.4) equals `−∫₀^θ h`. -/
@[powerlib_foundation] theorem formBPotential_eq_neg_integral (ωg Cf c₀ c₁ c₂ c₃ c₄ θ : ℝ) :
    formBPotential ωg Cf c₀ c₁ c₂ c₃ c₄ θ =
      -∫ t in (0 : ℝ)..θ, formBH ωg Cf c₀ c₁ c₂ c₃ c₄ t := by
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := formBPotential ωg Cf c₀ c₁ c₂ c₃ c₄) (a := 0) (b := θ)
    (fun t _ => hasDerivAt_formBPotential ωg Cf c₀ c₁ c₂ c₃ c₄ t)
    ((continuous_formBH ωg Cf c₀ c₁ c₂ c₃ c₄).neg.intervalIntegrable 0 θ)
  rw [intervalIntegral.integral_neg, formBPotential_zero, sub_zero] at hint
  linarith

/-- Bare-PLL degeneration, corrected: `c₁ = −V_g ω_g C_f` (others zero) gives `h = −V_g sin θ`. -/
@[powerlib_foundation] theorem formBH_barePLL {ωg Cf Vg : ℝ} (hωC : ωg * Cf ≠ 0) (θ : ℝ) :
    formBH ωg Cf 0 (-(Vg * ωg * Cf)) 0 0 0 θ = -Vg * Real.sin θ := by
  have hω : ωg ≠ 0 := left_ne_zero_of_mul hωC
  have hC : Cf ≠ 0 := right_ne_zero_of_mul hωC
  simp only [formBH]
  field_simp
  ring

/-- The note's choice `c₁ = −V_g` gives `h = −V_g sin θ / (ω_g C_f)`. -/
@[powerlib_foundation] theorem formBH_barePLL_note (ωg Cf Vg θ : ℝ) :
    formBH ωg Cf 0 (-Vg) 0 0 0 θ = -Vg * Real.sin θ / (ωg * Cf) := by
  simp only [formBH]
  ring

/-- The form-B pH model with the potential (1.4). -/
def formBPHModel (ωg Cf c₀ c₁ c₂ c₃ c₄ Kp Ki : ℝ) (hKp : 0 ≤ Kp) : PH.NonlinearModel 2 1 :=
  gflPHModel (formBH ωg Cf c₀ c₁ c₂ c₃ c₄) (formBPotential ωg Cf c₀ c₁ c₂ c₃ c₄)
    (hasDerivAt_formBPotential ωg Cf c₀ c₁ c₂ c₃ c₄) Kp Ki hKp

/-- For `c₀ ≠ 0` the form-B Hamiltonian is unbounded below (it contains `−c₀θ/(ω_g C_f)`). -/
@[powerlib_domain] theorem formBHamiltonian_not_bddBelow {ωg Cf c₀ c₁ c₂ c₃ c₄ Kp Ki : ℝ}
    {hKp : 0 ≤ Kp} (hωC : ωg * Cf ≠ 0) (hc₀ : c₀ ≠ 0) :
    ¬ ∃ c, ∀ x, c ≤ (formBPHModel ωg Cf c₀ c₁ c₂ c₃ c₄ Kp Ki hKp).H x := by
  rintro ⟨c, hc⟩
  set k := 1 / (ωg * Cf) with hk
  have hk0 : k ≠ 0 := one_div_ne_zero hωC
  set M := |k| * (2 * |c₁| + |c₂| + |c₃| + |c₄|) with hM
  -- the bounded part of the potential
  have hbound (θ : ℝ) : formBPotential ωg Cf c₀ c₁ c₂ c₃ c₄ θ ≤ -(k * c₀) * θ + M := by
    set B := c₁ * (Real.cos θ - 1) - c₂ * Real.sin θ + c₃ / 2 * (Real.cos (2 * θ) - 1) -
        c₄ / 2 * Real.sin (2 * θ) with hBdef
    have hc1 : |Real.cos θ - 1| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
    have hc2 : |Real.cos (2 * θ) - 1| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]
    have e1 : |c₁ * (Real.cos θ - 1)| ≤ 2 * |c₁| := by
      rw [abs_mul]; nlinarith [abs_nonneg c₁, abs_nonneg (Real.cos θ - 1)]
    have e2 : |c₂ * Real.sin θ| ≤ |c₂| := by
      rw [abs_mul]; nlinarith [abs_nonneg c₂, Real.abs_sin_le_one θ, abs_nonneg (Real.sin θ)]
    have e3 : |c₃ / 2 * (Real.cos (2 * θ) - 1)| ≤ |c₃| := by
      rw [abs_mul, abs_div, abs_two]
      nlinarith [abs_nonneg c₃, abs_nonneg (Real.cos (2 * θ) - 1)]
    have e4 : |c₄ / 2 * Real.sin (2 * θ)| ≤ |c₄| := by
      rw [abs_mul, abs_div, abs_two]
      nlinarith [abs_nonneg c₄, Real.abs_sin_le_one (2 * θ), abs_nonneg (Real.sin (2 * θ))]
    have hB : |B| ≤ 2 * |c₁| + |c₂| + |c₃| + |c₄| := by
      have := abs_le.mp e1; have := abs_le.mp e2; have := abs_le.mp e3; have := abs_le.mp e4
      rw [abs_le]; constructor <;> linarith
    have hkB : k * B ≤ M := by
      calc k * B ≤ |k * B| := le_abs_self _
        _ = |k| * |B| := abs_mul _ _
        _ ≤ M := mul_le_mul_of_nonneg_left hB (abs_nonneg _)
    have e : formBPotential ωg Cf c₀ c₁ c₂ c₃ c₄ θ = -(k * c₀) * θ + k * B := by
      simp only [formBPotential, hk, hBdef]
      ring
    rw [e]
    linarith
  have hkc : k * c₀ ≠ 0 := mul_ne_zero hk0 hc₀
  -- choose `θ` with `−(k c₀) θ = c − M − 1`
  set θ := (M - c + 1) / (k * c₀) with hθ
  have hθ' : -(k * c₀) * θ = c - M - 1 := by
    rw [hθ]
    field_simp
    ring
  have h1 := hc (piPLLState θ 0)
  simp only [formBPHModel, gflPHModel_H, piPLLState_apply_zero, piPLLState_apply_one] at h1
  have h2 := hbound θ
  nlinarith

/-- Consequently no shifted Hamiltonian `H − c` is a nonnegative storage, so the passivity
statement of `T-ph` (1.4) is not available for the form-B GFL PLL with `c₀ ≠ 0`. -/
@[powerlib_domain] theorem formB_not_passiveWithStorage {ωg Cf c₀ c₁ c₂ c₃ c₄ Kp Ki : ℝ}
    {hKp : 0 ≤ Kp} (hωC : ωg * Cf ≠ 0) (hc₀ : c₀ ≠ 0) (c : ℝ) :
    ¬ Passivity.PassiveWithStorage (formBPHModel ωg Cf c₀ c₁ c₂ c₃ c₄ Kp Ki hKp).toSystem
      (fun x => (formBPHModel ωg Cf c₀ c₁ c₂ c₃ c₄ Kp Ki hKp).H x - c) := by
  rintro ⟨hnn, -⟩
  exact formBHamiltonian_not_bddBelow (hKp := hKp) hωC hc₀ ⟨c, fun x => by linarith [hnn x]⟩

end powerlib.GFL
