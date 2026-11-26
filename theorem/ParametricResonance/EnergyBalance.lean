import dependencies.Mathlib
import theorem.Attributes
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # The energy balance over one period of an oscillator with time-varying stiffness

A sustained oscillation needs an energy source. For `m δ̈ + D δ̇ + K(t) δ = u(t)` the stored
energy `E = ½ m δ̇² + ½ K δ²` obeys `Ė = u δ̇ − D δ̇² + ½ K̇ δ²`; over one period of a periodic
solution with a periodic stiffness `E` returns to its value, so the dissipation `D ∫ δ̇²` equals
the work of the input `∫ u δ̇` plus the pump work of the stiffness variation `½ ∫ K̇ δ²`. The
three mechanisms of a sustained oscillation are read off: none (natural, constant `K`, `u = 0`:
then `D = 0`), the input (forced: `∫ u δ̇ = D ∫ δ̇² > 0` for `D > 0`), or the parameter
(parametric, `u = 0`: `½ ∫ K̇ δ² = D ∫ δ̇² > 0` for `D > 0`).

Scope.
* A scalar real second-order linear equation `m δ̈ + D δ̇ + K(t) δ = u(t)`, continuous time, with
  constant `m, D ∈ ℝ` (no sign or nondegeneracy assumption unless stated), a differentiable
  stiffness `K` with continuous derivative `K'`, a continuous input `u` and a global twice
  differentiable solution `δ` (derivatives `δ'`, `δ''` written out in the statements). Periodic
  statements ask `K` and `δ` to be `T`-periodic for the same `T`; the input need not be periodic.
* Pure analysis: no model family. The quadratic energy is `E = ½ m δ̇² + ½ K δ²`; no sign of `m` or
  `K` is needed for the balance.
* Matrix form: `ẋ = (J(t) − R(t)) Q(t) x + G(t) u(t)` on `Fin n → ℝ` with skew `J(t)`, symmetric
  `Q(t)` (entrywise differentiable, continuous derivative), continuous `R`, `G`, `u`; energy
  `H = ½ xᵀ Q x`, output `y = Gᵀ Q x`. The constant-coefficient port-Hamiltonian theory is
  `theorem/PH/Linear.lean`; here `Q` varies in time. The scalar oscillator is the case
  `x = (δ, m δ̇)`, `Q = diag(K, 1/m)`, `J = !![0, 1; −1, 0]`, `R = diag(0, D)`, `G = (0, 1)`
  (`m ≠ 0`); that reduction is not stated as a theorem.

Source: the energy mechanism of sustained oscillations behind IEEE PES TR-110 "Forced Oscillations
in Power Systems" (2023) §3.1 (intrinsic damping of natural and forced oscillations) and §3.3
(the swing equation (3-8)–(3-10) with its damping coefficients); the parametric mechanism (pump
work of a periodically varying parameter, Landau–Lifshitz, Mechanics §27).

Results.
* `energy`, `hasDerivAt_energy` — the power balance `Ė = u δ̇ − D δ̇² + ½ K̇ δ²` along a solution.
* `energy_balance_interval` — on every interval `[a, b]`:
  `E(b) − E(a) = ∫ u δ̇ − D ∫ δ̇² + ½ ∫ K̇ δ²`.
* `periodic_of_hasDerivAt` — the derivative of a periodic differentiable function is periodic.
* `energy_balance` — the period energy balance `D ∫₀ᵀ δ̇² = ∫₀ᵀ u δ̇ + ½ ∫₀ᵀ K̇ δ²` of a
  `T`-periodic solution with `T`-periodic `K`.
* `integral_stiffness_power` — over a period `∫₀ᵀ K δ δ̇ = −½ ∫₀ᵀ K̇ δ²` (the stiffness force does
  work only through the variation of `K`).
* `exists_deriv_ne_zero`, `integral_sq_deriv_pos` — a nonconstant periodic solution has
  `∫₀ᵀ δ̇² > 0`.
* `natural_damping_eq_zero`, `natural_exists_of_damping_zero` — natural mechanism: with constant
  stiffness and `u = 0` a nonconstant periodic solution forces `D = 0` (with `D ≠ 0` none exists);
  conversely for `D = 0`, `m, k > 0` the solution `cos(√(k/m) t)` is periodic and nonconstant.
* `forced_balance`, `forced_supply_pos` — forced mechanism: with constant stiffness
  `∫₀ᵀ u δ̇ = D ∫₀ᵀ δ̇²`, positive for `D > 0` and a nonconstant solution: the energy enters through
  the input.
* `parametric_balance`, `parametric_pump_pos` — parametric mechanism: with `u = 0`
  `½ ∫₀ᵀ K̇ δ² = D ∫₀ᵀ δ̇²`, positive for `D > 0` and a nonconstant solution: the pump work of the
  varying stiffness equals the dissipation.
* `damping_eq_supply_div`, `sustained_supply_pos` — for every nonconstant periodic solution
  `D = (∫ u δ̇ + ½ ∫ K̇ δ²) / ∫ δ̇²`, so a sustained oscillation with `D > 0` needs a positive total
  supply from the input or the parameter.
* `hasDerivAt_dotProduct_mulVec`, `hasDerivAt_phEnergy`, `ph_energy_balance` — the matrix form:
  `Ḣ = ½ xᵀ Q̇ x + yᵀ u − (Qx)ᵀ R (Qx)` and, over a period of a periodic solution with periodic
  `Q`, `∮ ½ xᵀ Q̇ x + ∮ yᵀ u = ∮ (Qx)ᵀ R (Qx)` (pump work plus port supply equals dissipation).
-/

noncomputable section
namespace powerlib.ParametricResonance.EnergyBalance

open Set Function

variable {m D T : ℝ} {K K' u δ δ' δ'' : ℝ → ℝ}

/-- Stored energy `E(t) = ½ m δ̇(t)² + ½ K(t) δ(t)²`. -/
def energy (m : ℝ) (K δ δ' : ℝ → ℝ) (t : ℝ) : ℝ := m / 2 * δ' t ^ 2 + K t / 2 * δ t ^ 2

/-- Power balance along a solution of `m δ̈ + D δ̇ + K(t) δ = u(t)`:
`Ė = u δ̇ − D δ̇² + ½ K̇ δ²`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_energy (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t) (hK : ∀ t, HasDerivAt K (K' t) t)
    (heq : ∀ t, m * δ'' t + D * δ' t + K t * δ t = u t) (t : ℝ) :
    HasDerivAt (energy m K δ δ') (u t * δ' t - D * δ' t ^ 2 + K' t / 2 * δ t ^ 2) t := by
  have h1 := ((hδ' t).pow 2).const_mul (m / 2)
  have h2 := ((hK t).div_const 2).mul ((hδ t).pow 2)
  have h := h1.add h2
  have he : energy m K δ δ' = fun s => m / 2 * δ' s ^ 2 + K s / 2 * δ s ^ 2 := rfl
  rw [he]
  convert h using 1
  rw [← heq t]
  simp only [Pi.pow_apply]
  push_cast
  ring

@[tmio T, powerlib_foundation] private theorem continuous_of_hasDerivAt {f f' : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) : Continuous f :=
  continuous_iff_continuousAt.2 fun t => (hf t).continuousAt

/-- The energy balance on an interval: `E(b) − E(a) = ∫ₐᵇ u δ̇ − D ∫ₐᵇ δ̇² + ½ ∫ₐᵇ K̇ δ²`. -/
@[tmio T, powerlib_foundation] theorem energy_balance_interval (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t) (hK : ∀ t, HasDerivAt K (K' t) t)
    (hK' : Continuous K') (hu : Continuous u)
    (heq : ∀ t, m * δ'' t + D * δ' t + K t * δ t = u t) (a b : ℝ) :
    energy m K δ δ' b - energy m K δ δ' a =
      (∫ t in a..b, u t * δ' t) - D * (∫ t in a..b, δ' t ^ 2) +
        (∫ t in a..b, K' t * δ t ^ 2) / 2 := by
  have hδc := continuous_of_hasDerivAt hδ
  have hδ'c := continuous_of_hasDerivAt hδ'
  have hint : IntervalIntegrable (fun t => u t * δ' t - D * δ' t ^ 2 + K' t / 2 * δ t ^ 2)
      MeasureTheory.volume a b := (by fun_prop : Continuous _).intervalIntegrable a b
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_energy hδ hδ' hK heq t) hint]
  have i1 : IntervalIntegrable (fun t => u t * δ' t) MeasureTheory.volume a b :=
    (by fun_prop : Continuous _).intervalIntegrable a b
  have i2 : IntervalIntegrable (fun t => D * δ' t ^ 2) MeasureTheory.volume a b :=
    (by fun_prop : Continuous _).intervalIntegrable a b
  have i3 : IntervalIntegrable (fun t => K' t / 2 * δ t ^ 2) MeasureTheory.volume a b :=
    (by fun_prop : Continuous _).intervalIntegrable a b
  rw [intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_const_mul]
  have e3 : (fun t => K' t / 2 * δ t ^ 2) = fun t => (K' t * δ t ^ 2) / 2 := by
    funext t; ring
  rw [e3, intervalIntegral.integral_div]

/-- The derivative of a `T`-periodic differentiable function is `T`-periodic. -/
@[tmio T, powerlib_foundation] theorem periodic_of_hasDerivAt (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hT : Periodic δ T) : Periodic δ' T := by
  intro t
  have h := HasDerivAt.comp_add_const t T (hδ (t + T))
  rw [show (fun s => δ (s + T)) = δ from funext hT] at h
  exact h.unique (hδ t)

/-- The period energy balance: for a `T`-periodic solution with `T`-periodic stiffness,
`D ∫₀ᵀ δ̇² = ∫₀ᵀ u δ̇ + ½ ∫₀ᵀ K̇ δ²`. -/
@[tmio T, powerlib_foundation] theorem energy_balance (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t) (hK : ∀ t, HasDerivAt K (K' t) t)
    (hK' : Continuous K') (hu : Continuous u)
    (heq : ∀ t, m * δ'' t + D * δ' t + K t * δ t = u t) (hδT : Periodic δ T)
    (hKT : Periodic K T) :
    D * (∫ t in (0 : ℝ)..T, δ' t ^ 2) =
      (∫ t in (0 : ℝ)..T, u t * δ' t) + (∫ t in (0 : ℝ)..T, K' t * δ t ^ 2) / 2 := by
  have h := energy_balance_interval hδ hδ' hK hK' hu heq 0 T
  have hE : energy m K δ δ' T = energy m K δ δ' 0 := by
    have h1 := hδT 0
    have h2 := hKT 0
    have h3 := periodic_of_hasDerivAt hδ hδT 0
    simp only [zero_add] at h1 h2 h3
    simp only [energy, h1, h2, h3]
  rw [hE, sub_self] at h
  linarith

/-- Over one period the stiffness force does work only through the variation of the stiffness:
`∫₀ᵀ K δ δ̇ = −½ ∫₀ᵀ K̇ δ²`. -/
@[tmio T, powerlib_foundation] theorem integral_stiffness_power
    (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hδ'c : Continuous δ') (hK : ∀ t, HasDerivAt K (K' t) t)
    (hK' : Continuous K') (hδT : Periodic δ T) (hKT : Periodic K T) :
    ∫ t in (0 : ℝ)..T, K t * δ t * δ' t = -((∫ t in (0 : ℝ)..T, K' t * δ t ^ 2) / 2) := by
  have hδc := continuous_of_hasDerivAt hδ
  have hKc := continuous_of_hasDerivAt hK
  have hd : ∀ t, HasDerivAt (fun s => K s / 2 * δ s ^ 2)
      (K' t * δ t ^ 2 / 2 + K t * δ t * δ' t) t := by
    intro t
    convert ((hK t).div_const 2).mul ((hδ t).pow 2) using 1
    simp only [Pi.pow_apply]
    push_cast
    ring
  have hint : IntervalIntegrable (fun t => K' t * δ t ^ 2 / 2 + K t * δ t * δ' t)
      MeasureTheory.volume 0 T := (by fun_prop : Continuous _).intervalIntegrable 0 T
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hint
  have h1 := hδT 0
  have h2 := hKT 0
  simp only [zero_add] at h1 h2
  rw [h1, h2, sub_self, intervalIntegral.integral_add
    ((by fun_prop : Continuous fun t => K' t * δ t ^ 2 / 2).intervalIntegrable 0 T)
    ((by fun_prop : Continuous fun t => K t * δ t * δ' t).intervalIntegrable 0 T),
    intervalIntegral.integral_div] at h
  linarith

/-! ## A nonconstant periodic solution moves -/

/-- A nonconstant `T`-periodic differentiable function has a nonzero derivative somewhere in
`[0, T]`. -/
@[tmio T, powerlib_foundation] theorem exists_deriv_ne_zero (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hT : 0 < T) (hδT : Periodic δ T) (hnc : ∃ t, δ t ≠ δ 0) : ∃ c ∈ Icc 0 T, δ' c ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hconst : ∀ x ∈ Icc 0 T, δ x = δ 0 :=
    constant_of_has_deriv_right_zero (continuous_of_hasDerivAt hδ).continuousOn
      (fun x hx => by
        have := (hδ x).hasDerivWithinAt (s := Ici x)
        rwa [hcon x (Ico_subset_Icc_self hx)] at this)
  obtain ⟨t, ht⟩ := hnc
  obtain ⟨y, hy, hty⟩ := hδT.exists_mem_Ico₀ hT t
  exact ht (hty.trans (hconst y (Ico_subset_Icc_self hy)))

/-- A nonconstant `T`-periodic `C¹` function has `∫₀ᵀ δ̇² > 0`. -/
@[tmio T, powerlib_foundation] theorem integral_sq_deriv_pos (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ'c : Continuous δ') (hT : 0 < T) (hδT : Periodic δ T) (hnc : ∃ t, δ t ≠ δ 0) :
    0 < ∫ t in (0 : ℝ)..T, δ' t ^ 2 := by
  obtain ⟨c, hc, hc0⟩ := exists_deriv_ne_zero hδ hT hδT hnc
  exact intervalIntegral.integral_pos hT (by fun_prop) (fun x _ => sq_nonneg _)
    ⟨c, hc, by positivity⟩

/-! ## The three mechanisms -/

/-- Natural mechanism: with constant stiffness `k` and no input, a nonconstant periodic solution
of `m δ̈ + D δ̇ + k δ = 0` forces `D = 0`; with `D ≠ 0` no sustained oscillation exists. -/
@[tmio T, powerlib_foundation] theorem natural_damping_eq_zero {k : ℝ}
    (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t)
    (heq : ∀ t, m * δ'' t + D * δ' t + k * δ t = 0) (hT : 0 < T) (hδT : Periodic δ T)
    (hnc : ∃ t, δ t ≠ δ 0) : D = 0 := by
  have h := energy_balance (K := fun _ => k) (K' := fun _ => 0) (u := fun _ => 0) hδ hδ'
    (fun _ => hasDerivAt_const _ _) continuous_const continuous_const heq hδT
    (fun _ => rfl)
  simp only [zero_mul, intervalIntegral.integral_zero, zero_div, add_zero] at h
  have hpos := integral_sq_deriv_pos hδ (continuous_of_hasDerivAt hδ') hT hδT hnc
  rcases mul_eq_zero.mp h with h | h
  · exact h
  · exact absurd h hpos.ne'

/-- Conversely, with `D = 0` and `m, k > 0` the natural oscillation `δ = cos(√(k/m) t)` is a
nonconstant periodic solution of `m δ̈ + k δ = 0`, of period `2π/√(k/m)`. -/
@[tmio T, powerlib_foundation] theorem natural_exists_of_damping_zero {k : ℝ} (hm : 0 < m)
    (hk : 0 < k) :
    (∀ t, HasDerivAt (fun s => Real.cos (Real.sqrt (k / m) * s))
        (-(Real.sqrt (k / m) * Real.sin (Real.sqrt (k / m) * t))) t) ∧
    (∀ t, HasDerivAt (fun s => -(Real.sqrt (k / m) * Real.sin (Real.sqrt (k / m) * s)))
        (-(Real.sqrt (k / m) ^ 2 * Real.cos (Real.sqrt (k / m) * t))) t) ∧
    (∀ t, m * -(Real.sqrt (k / m) ^ 2 * Real.cos (Real.sqrt (k / m) * t)) +
        0 * -(Real.sqrt (k / m) * Real.sin (Real.sqrt (k / m) * t)) +
        k * Real.cos (Real.sqrt (k / m) * t) = 0) ∧
    Periodic (fun s => Real.cos (Real.sqrt (k / m) * s)) (2 * Real.pi / Real.sqrt (k / m)) ∧
    ∃ t, Real.cos (Real.sqrt (k / m) * t) ≠ Real.cos (Real.sqrt (k / m) * 0) := by
  set w := Real.sqrt (k / m) with hw
  have hw0 : 0 < w := Real.sqrt_pos.mpr (div_pos hk hm)
  have hw2 : w ^ 2 = k / m := Real.sq_sqrt (div_pos hk hm).le
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, ⟨Real.pi / w, ?_⟩⟩
  · have h := ((hasDerivAt_id t).const_mul w).cos
    simp only [id, mul_one] at h
    convert h using 1
    ring
  · have h := (((hasDerivAt_id t).const_mul w).sin.const_mul w).neg
    simp only [id, mul_one] at h
    convert h using 1
    ring
  · rw [hw2]; field_simp; ring
  · show Real.cos (w * (t + 2 * Real.pi / w)) = Real.cos (w * t)
    rw [show w * (t + 2 * Real.pi / w) = w * t + 2 * Real.pi by field_simp]
    exact Real.cos_add_two_pi _
  · rw [mul_zero, Real.cos_zero, show w * (Real.pi / w) = Real.pi by field_simp, Real.cos_pi]
    norm_num

/-- Forced mechanism (constant stiffness `k`): the input supplies exactly the dissipated energy,
`∫₀ᵀ u δ̇ = D ∫₀ᵀ δ̇²`. -/
@[tmio T, powerlib_foundation] theorem forced_balance {k : ℝ} (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t) (hu : Continuous u)
    (heq : ∀ t, m * δ'' t + D * δ' t + k * δ t = u t) (hδT : Periodic δ T) :
    ∫ t in (0 : ℝ)..T, u t * δ' t = D * ∫ t in (0 : ℝ)..T, δ' t ^ 2 := by
  have h := energy_balance (K := fun _ => k) (K' := fun _ => 0) hδ hδ'
    (fun _ => hasDerivAt_const _ _) continuous_const hu heq hδT (fun _ => rfl)
  simp only [zero_mul, intervalIntegral.integral_zero, zero_div, add_zero] at h
  exact h.symm

/-- Forced mechanism: for `D > 0` and a nonconstant periodic solution the input work is positive,
`∫₀ᵀ u δ̇ > 0`. -/
@[tmio T, powerlib_foundation] theorem forced_supply_pos {k : ℝ}
    (hδ : ∀ t, HasDerivAt δ (δ' t) t) (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t) (hu : Continuous u)
    (heq : ∀ t, m * δ'' t + D * δ' t + k * δ t = u t) (hT : 0 < T) (hδT : Periodic δ T)
    (hnc : ∃ t, δ t ≠ δ 0) (hD : 0 < D) : 0 < ∫ t in (0 : ℝ)..T, u t * δ' t := by
  rw [forced_balance hδ hδ' hu heq hδT]
  exact mul_pos hD (integral_sq_deriv_pos hδ (continuous_of_hasDerivAt hδ') hT hδT hnc)

/-- Parametric mechanism (no input): the pump work of the varying stiffness equals the dissipated
energy, `½ ∫₀ᵀ K̇ δ² = D ∫₀ᵀ δ̇²`. -/
@[tmio T, powerlib_foundation] theorem parametric_balance (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t) (hK : ∀ t, HasDerivAt K (K' t) t)
    (hK' : Continuous K') (heq : ∀ t, m * δ'' t + D * δ' t + K t * δ t = 0)
    (hδT : Periodic δ T) (hKT : Periodic K T) :
    (∫ t in (0 : ℝ)..T, K' t * δ t ^ 2) / 2 = D * ∫ t in (0 : ℝ)..T, δ' t ^ 2 := by
  have h := energy_balance (u := fun _ => 0) hδ hδ' hK hK' continuous_const heq hδT hKT
  simp only [zero_mul, intervalIntegral.integral_zero, zero_add] at h
  exact h.symm

/-- Parametric mechanism: for `D > 0` and a nonconstant periodic solution the pump work is
positive, `∫₀ᵀ K̇ δ² > 0`. -/
@[tmio T, powerlib_foundation] theorem parametric_pump_pos (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t) (hK : ∀ t, HasDerivAt K (K' t) t)
    (hK' : Continuous K') (heq : ∀ t, m * δ'' t + D * δ' t + K t * δ t = 0) (hT : 0 < T)
    (hδT : Periodic δ T) (hKT : Periodic K T) (hnc : ∃ t, δ t ≠ δ 0) (hD : 0 < D) :
    0 < ∫ t in (0 : ℝ)..T, K' t * δ t ^ 2 := by
  have h := parametric_balance hδ hδ' hK hK' heq hδT hKT
  have := mul_pos hD (integral_sq_deriv_pos hδ (continuous_of_hasDerivAt hδ') hT hδT hnc)
  linarith

/-- For every nonconstant periodic solution the damping is the total supply per unit of
`∫ δ̇²`: `D = (∫₀ᵀ u δ̇ + ½ ∫₀ᵀ K̇ δ²) / ∫₀ᵀ δ̇²`. -/
@[tmio T, powerlib_foundation] theorem damping_eq_supply_div (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t) (hK : ∀ t, HasDerivAt K (K' t) t)
    (hK' : Continuous K') (hu : Continuous u)
    (heq : ∀ t, m * δ'' t + D * δ' t + K t * δ t = u t) (hT : 0 < T) (hδT : Periodic δ T)
    (hKT : Periodic K T) (hnc : ∃ t, δ t ≠ δ 0) :
    D = ((∫ t in (0 : ℝ)..T, u t * δ' t) + (∫ t in (0 : ℝ)..T, K' t * δ t ^ 2) / 2) /
      ∫ t in (0 : ℝ)..T, δ' t ^ 2 := by
  have hpos := integral_sq_deriv_pos hδ (continuous_of_hasDerivAt hδ') hT hδT hnc
  rw [← energy_balance hδ hδ' hK hK' hu heq hδT hKT, mul_div_cancel_right₀ _ hpos.ne']

/-- A sustained (nonconstant periodic) oscillation with positive damping needs a positive total
energy supply from the input or the stiffness variation: `∫₀ᵀ u δ̇ + ½ ∫₀ᵀ K̇ δ² > 0`. -/
@[tmio T, powerlib_foundation] theorem sustained_supply_pos (hδ : ∀ t, HasDerivAt δ (δ' t) t)
    (hδ' : ∀ t, HasDerivAt δ' (δ'' t) t) (hK : ∀ t, HasDerivAt K (K' t) t)
    (hK' : Continuous K') (hu : Continuous u)
    (heq : ∀ t, m * δ'' t + D * δ' t + K t * δ t = u t) (hT : 0 < T) (hδT : Periodic δ T)
    (hKT : Periodic K T) (hnc : ∃ t, δ t ≠ δ 0) (hD : 0 < D) :
    0 < (∫ t in (0 : ℝ)..T, u t * δ' t) + (∫ t in (0 : ℝ)..T, K' t * δ t ^ 2) / 2 := by
  rw [← energy_balance hδ hδ' hK hK' hu heq hδT hKT]
  exact mul_pos hD (integral_sq_deriv_pos hδ (continuous_of_hasDerivAt hδ') hT hδT hnc)

/-! ## Linear port-Hamiltonian systems with a time-varying energy matrix -/

section Matrix

open Matrix

variable {n k : ℕ}

/-- Product rule for `x ⬝ᵥ (Q y)` with an entrywise differentiable matrix `Q(t)`:
`(x ⬝ᵥ Q y)' = x' ⬝ᵥ Q y + x ⬝ᵥ Q' y + x ⬝ᵥ Q y'`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_dotProduct_mulVec {x x' y y' : ℝ → Fin n → ℝ}
    {Q Q' : ℝ → Matrix (Fin n) (Fin n) ℝ} {t : ℝ} (hx : HasDerivAt x (x' t) t)
    (hy : HasDerivAt y (y' t) t) (hQ : ∀ i j, HasDerivAt (fun s => Q s i j) (Q' t i j) t) :
    HasDerivAt (fun s => x s ⬝ᵥ (Q s *ᵥ y s))
      (x' t ⬝ᵥ (Q t *ᵥ y t) + x t ⬝ᵥ (Q' t *ᵥ y t) + x t ⬝ᵥ (Q t *ᵥ y' t)) t := by
  have hxi : ∀ i, HasDerivAt (fun s => x s i) (x' t i) t := fun i => hasDerivAt_pi.mp hx i
  have hyj : ∀ j, HasDerivAt (fun s => y s j) (y' t j) t := fun j => hasDerivAt_pi.mp hy j
  have h : HasDerivAt (fun s => ∑ i, x s i * ∑ j, Q s i j * y s j)
      (∑ i, (x' t i * ∑ j, Q t i j * y t j +
        x t i * ∑ j, (Q' t i j * y t j + Q t i j * y' t j))) t :=
    HasDerivAt.fun_sum fun i _ =>
      (hxi i).mul (HasDerivAt.fun_sum fun j _ => (hQ i j).mul (hyj j))
  convert h using 1
  · funext s
    simp only [dotProduct, mulVec]
  · simp only [dotProduct, mulVec, mul_add, Finset.sum_add_distrib]
    ring

/-- Power balance of `ẋ = (J(t) − R(t)) Q(t) x + G(t) u(t)` with skew `J(t)` and symmetric
`Q(t)`: the energy `H = ½ xᵀ Q x` obeys `Ḣ = ½ xᵀ Q̇ x + yᵀ u − (Q x)ᵀ R (Q x)`, `y = Gᵀ Q x`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_phEnergy {x : ℝ → Fin n → ℝ}
    {Q Q' J R : ℝ → Matrix (Fin n) (Fin n) ℝ} {G : ℝ → Matrix (Fin n) (Fin k) ℝ}
    {u : ℝ → Fin k → ℝ} (hx : ∀ t, HasDerivAt x ((J t - R t) *ᵥ (Q t *ᵥ x t) + G t *ᵥ u t) t)
    (hJ : ∀ t, (J t)ᵀ = -J t) (hQs : ∀ t, (Q t)ᵀ = Q t)
    (hQ : ∀ t i j, HasDerivAt (fun s => Q s i j) (Q' t i j) t) (t : ℝ) :
    HasDerivAt (fun s => x s ⬝ᵥ (Q s *ᵥ x s) / 2)
      (x t ⬝ᵥ (Q' t *ᵥ x t) / 2 + ((G t)ᵀ *ᵥ (Q t *ᵥ x t)) ⬝ᵥ u t -
        (Q t *ᵥ x t) ⬝ᵥ (R t *ᵥ (Q t *ᵥ x t))) t := by
  have h := (hasDerivAt_dotProduct_mulVec
    (x' := fun s => (J s - R s) *ᵥ (Q s *ᵥ x s) + G s *ᵥ u s)
    (y' := fun s => (J s - R s) *ᵥ (Q s *ᵥ x s) + G s *ᵥ u s) (hx t) (hx t) (hQ t)).div_const 2
  convert h using 1
  set z := Q t *ᵥ x t
  set v := (J t - R t) *ᵥ z + G t *ᵥ u t
  have hsym : x t ⬝ᵥ (Q t *ᵥ v) = v ⬝ᵥ z := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hQs, dotProduct_comm]
  have hskew : z ⬝ᵥ (J t *ᵥ z) = 0 := by
    have h1 : z ⬝ᵥ (J t *ᵥ z) = -(z ⬝ᵥ (J t *ᵥ z)) := by
      conv_lhs => rw [dotProduct_mulVec, ← mulVec_transpose, hJ, neg_mulVec, dotProduct_comm]
      rw [dotProduct_neg]
    linarith
  have hv : v ⬝ᵥ z = -(z ⬝ᵥ (R t *ᵥ z)) + ((G t)ᵀ *ᵥ z) ⬝ᵥ u t := by
    simp only [v, sub_mulVec, add_dotProduct, sub_dotProduct]
    rw [dotProduct_comm (J t *ᵥ z), hskew, dotProduct_comm (R t *ᵥ z), mulVec_transpose,
      ← dotProduct_mulVec, dotProduct_comm (G t *ᵥ u t)]
    ring
  have hfirst : v ⬝ᵥ (Q t *ᵥ x t) = v ⬝ᵥ z := rfl
  rw [hsym, hfirst, hv]
  ring

/-- The period energy balance of a linear port-Hamiltonian system with a `T`-periodic energy
matrix: for a `T`-periodic solution, `∮ ½ xᵀ Q̇ x + ∮ yᵀ u = ∮ (Q x)ᵀ R (Q x)`, `y = Gᵀ Q x`: the
pump work of the varying energy matrix and the port supply equal the dissipation. -/
@[tmio T, powerlib_foundation] theorem ph_energy_balance {T : ℝ} {x : ℝ → Fin n → ℝ}
    {Q Q' J R : ℝ → Matrix (Fin n) (Fin n) ℝ} {G : ℝ → Matrix (Fin n) (Fin k) ℝ}
    {u : ℝ → Fin k → ℝ} (hx : ∀ t, HasDerivAt x ((J t - R t) *ᵥ (Q t *ᵥ x t) + G t *ᵥ u t) t)
    (hJ : ∀ t, (J t)ᵀ = -J t) (hQs : ∀ t, (Q t)ᵀ = Q t)
    (hQ : ∀ t i j, HasDerivAt (fun s => Q s i j) (Q' t i j) t) (hQ' : Continuous Q')
    (hR : Continuous R) (hG : Continuous G) (hu : Continuous u) (hxT : Periodic x T)
    (hQT : Periodic Q T) :
    (∫ t in (0 : ℝ)..T, x t ⬝ᵥ (Q' t *ᵥ x t) / 2) +
        ∫ t in (0 : ℝ)..T, ((G t)ᵀ *ᵥ (Q t *ᵥ x t)) ⬝ᵥ u t =
      ∫ t in (0 : ℝ)..T, (Q t *ᵥ x t) ⬝ᵥ (R t *ᵥ (Q t *ᵥ x t)) := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
  have hQc : Continuous Q := continuous_pi fun i => continuous_pi fun j =>
    continuous_iff_continuousAt.2 fun t => (hQ t i j).continuousAt
  have c1 : Continuous fun t => x t ⬝ᵥ (Q' t *ᵥ x t) / 2 :=
    (hxc.dotProduct (hQ'.matrix_mulVec hxc)).div_const 2
  have c2 : Continuous fun t => ((G t)ᵀ *ᵥ (Q t *ᵥ x t)) ⬝ᵥ u t :=
    (hG.matrix_transpose.matrix_mulVec (hQc.matrix_mulVec hxc)).dotProduct hu
  have c3 : Continuous fun t => (Q t *ᵥ x t) ⬝ᵥ (R t *ᵥ (Q t *ᵥ x t)) :=
    (hQc.matrix_mulVec hxc).dotProduct (hR.matrix_mulVec (hQc.matrix_mulVec hxc))
  have c123 : Continuous fun t => x t ⬝ᵥ (Q' t *ᵥ x t) / 2 +
      ((G t)ᵀ *ᵥ (Q t *ᵥ x t)) ⬝ᵥ u t - (Q t *ᵥ x t) ⬝ᵥ (R t *ᵥ (Q t *ᵥ x t)) := (c1.add c2).sub c3
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_phEnergy hx hJ hQs hQ t) (c123.intervalIntegrable 0 T)
  have h0 := hxT 0
  have h1 := hQT 0
  simp only [zero_add] at h0 h1
  have c12 : Continuous fun t => x t ⬝ᵥ (Q' t *ᵥ x t) / 2 +
      ((G t)ᵀ *ᵥ (Q t *ᵥ x t)) ⬝ᵥ u t := c1.add c2
  rw [h0, h1, sub_self, intervalIntegral.integral_sub (c12.intervalIntegrable 0 T)
    (c3.intervalIntegrable 0 T), intervalIntegral.integral_add (c1.intervalIntegrable 0 T)
    (c2.intervalIntegrable 0 T)] at h
  linarith

end Matrix

end powerlib.ParametricResonance.EnergyBalance
