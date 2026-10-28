import dependencies.Mathlib
import theorem.Attributes

/-! # Mean first-passage time of an overdamped 1D diffusion: the Kramers double integral

The Kramers double integral solves the backward boundary-value problem of the mean first-passage
time, uniquely; the Kramers prefactor algebra; the adjoint form of the note is wrong.

Model boundary.
* Overdamped scalar Smoluchowski dynamics `γ dθ = −V'(θ) dt + √(2Dγ) dW` (washboard / well
  potentials belong to `theorem/Potential/Wells.lean`, not here); generator
  `L = (1/γ)(−V' d/dθ + D d²/dθ²)`. Reflecting boundary at `θ_r` (`T'(θ_r) = 0`), absorbing
  boundary at `θ_c` (`T(θ_c) = 0`). We work on the whole line with these two point conditions.
* The MFPT is treated as the solution of the backward boundary-value problem
  `D T'' − V' T' = −γ`, `T(θ_c) = 0`, `T'(θ_r) = 0` (an ODE statement). That this solution equals
  `E[τ_c]` for the diffusion requires Dynkin's formula / Itô calculus and is **not** formalized.
  The high-barrier Laplace asymptotics of §1.4 are not formalized either; only the algebra that
  combines the two Gaussian factors into the prefactor.

Source: work-sync theory/T-kramers-escape.md §1.1 (first-passage time `τ_c`), §1.2 (backward
equation for the MFPT, reflecting / absorbing boundary conditions), §1.3 (double-integral
solution), §1.4 (prefactor algebra `(γ/D)·√(2πD/|V''_b|)·√(2πD/V''_a) = 2πγ/√(V''_a |V''_b|)`);
theory/T-first-passage-time.md (`L m = −1`, `m = 0` on the absorbing boundary;
hit probability `h = 1 − s`).

Results.
* `kramersT_ode`, `kramersT_absorbing`, `kramersT_reflecting` — the Kramers double integral
  `kramersT`, `T(θ) = (γ/D) ∫_θ^{θ_c} e^{V(y)/D} ∫_{θ_r}^{y} e^{−V(z)/D} dz dy`, solves
  `D T'' − V' T' = −γ` with `T(θ_c) = 0`, `T'(θ_r) = 0`.
* `kramersT_unique` — any twice-differentiable solution of that boundary-value problem is the
  Kramers double integral; `kramersT_pos`: `T(θ) > 0` for `θ_r < θ < θ_c` (`γ, D > 0`).
* `kramers_prefactor` — `(γ/D) √(2πD/κ_b) √(2πD/κ_a) = 2πγ/√(κ_a κ_b)`; `D` cancels.
* `mfpt_free_diffusion` — pure diffusion between two absorbing points: `m(θ) = (θ − a)(b − θ)/(2D)`
  solves `D m'' = −1`, `m(a) = m(b) = 0`.
* `hit_eq_one_sub_survival` — the hit probability before `T` is `h = 1 − s`.

Corrections.
* §1.2: the note writes the MFPT equation in the **adjoint** form
  `−1 = −(1/γ)(V' T)' + (D/γ) T''`. The correct backward equation is
  `−(V'/γ) T' + (D/γ) T'' = −1` (generator applied to `T`). The two differ by `−V'' T/γ`
  (`adjointForm_residual`), so the adjoint form fails wherever `V'' T ≠ 0`, e.g. inside the well
  (`adjointForm_ne`). The double integral of §1.3 is the solution of the correct (backward) form
  (`kramersT_ode`).
-/

noncomputable section
namespace powerlib.Stochastic.MFPT

open MeasureTheory Real intervalIntegral Set

/-- Inner integral `I(y) = ∫_{θ_r}^{y} e^{−V/D}` (Boltzmann weight of the well). -/
def innerI (V : ℝ → ℝ) (D θr y : ℝ) : ℝ := ∫ z in θr..y, exp (-V z / D)

/-- Integrand of the outer integral, `g(y) = e^{V(y)/D} I(y)`. -/
def outerG (V : ℝ → ℝ) (D θr y : ℝ) : ℝ := exp (V y / D) * innerI V D θr y

/-- **Kramers MFPT double integral (§1.3)**:
`T(θ) = (γ/D) ∫_θ^{θ_c} e^{V(y)/D} ∫_{θ_r}^{y} e^{−V(z)/D} dz dy`. -/
def kramersT (V : ℝ → ℝ) (D γ θr θc θ : ℝ) : ℝ := γ / D * ∫ y in θ..θc, outerG V D θr y

variable {V V' : ℝ → ℝ} {D γ θr θc : ℝ}

@[tmio T, powerlib_foundation] theorem innerI_hasDerivAt (hV : Continuous V) (y : ℝ) :
    HasDerivAt (innerI V D θr) (exp (-V y / D)) y :=
  (Continuous.integral_hasStrictDerivAt (by fun_prop) θr y).hasDerivAt

@[powerlib_foundation] theorem innerI_continuous (hV : Continuous V) :
    Continuous (innerI V D θr) :=
  continuous_iff_continuousAt.2 fun y => (innerI_hasDerivAt hV y).continuousAt

@[powerlib_foundation] theorem outerG_continuous (hV : Continuous V) :
    Continuous (outerG V D θr) := by
  unfold outerG
  exact (by fun_prop : Continuous fun y => exp (V y / D)).mul (innerI_continuous hV)

/-- `g' = (V'/D) g + 1`. -/
@[powerlib_foundation] theorem outerG_hasDerivAt (hV : ∀ x, HasDerivAt V (V' x) x) (y : ℝ) :
    HasDerivAt (outerG V D θr) (V' y / D * outerG V D θr y + 1) y := by
  have hVc : Continuous V := continuous_iff_continuousAt.2 fun x => (hV x).continuousAt
  have h1 := ((hV y).div_const D).exp
  have h2 := innerI_hasDerivAt (D := D) (θr := θr) hVc y
  have := h1.mul h2
  unfold outerG
  convert! this using 1
  rw [show exp (V y / D) * exp (-V y / D) = 1 by
    rw [← exp_add, show V y / D + -V y / D = 0 by ring, exp_zero]]
  ring

/-- `T' = −(γ/D) g`. -/
@[powerlib_foundation] theorem kramersT_hasDerivAt (hV : Continuous V) (θ : ℝ) :
    HasDerivAt (kramersT V D γ θr θc) (-(γ / D) * outerG V D θr θ) θ := by
  have hg := outerG_continuous (D := D) (θr := θr) hV
  have h : HasDerivAt (fun u => ∫ y in θc..u, outerG V D θr y) (outerG V D θr θ) θ :=
    (hg.integral_hasStrictDerivAt θc θ).hasDerivAt
  have e : kramersT V D γ θr θc = fun u => -(γ / D) * ∫ y in θc..u, outerG V D θr y := by
    funext u; unfold kramersT; rw [integral_symm]; ring
  rw [e]
  exact h.const_mul _

/-- **Backward MFPT equation (§1.3)**: `D T'' − V' T' = −γ`, written with the explicit first and
second derivatives. -/
@[powerlib_foundation] theorem kramersT_ode (hV : ∀ x, HasDerivAt V (V' x) x) (hD : D ≠ 0)
    (θ : ℝ) :
    HasDerivAt (kramersT V D γ θr θc) (-(γ / D) * outerG V D θr θ) θ ∧
      HasDerivAt (fun u => -(γ / D) * outerG V D θr u)
        (-(γ / D) * (V' θ / D * outerG V D θr θ + 1)) θ ∧
      D * (-(γ / D) * (V' θ / D * outerG V D θr θ + 1)) -
        V' θ * (-(γ / D) * outerG V D θr θ) = -γ := by
  have hVc : Continuous V := continuous_iff_continuousAt.2 fun x => (hV x).continuousAt
  refine ⟨kramersT_hasDerivAt hVc θ, (outerG_hasDerivAt hV θ).const_mul _, ?_⟩
  field_simp
  ring

/-- Absorbing boundary `T(θ_c) = 0`. -/
@[powerlib_foundation] theorem kramersT_absorbing : kramersT V D γ θr θc θc = 0 := by
  simp [kramersT]

/-- Reflecting boundary `T'(θ_r) = 0` (the inner integral vanishes there). -/
@[powerlib_foundation] theorem kramersT_reflecting : -(γ / D) * outerG V D θr θr = 0 := by
  simp [outerG, innerI]

/-- Uniqueness: any twice-differentiable solution of `D U'' − V' U' = −γ` with `U(θ_c) = 0`,
`U'(θ_r) = 0` is the Kramers double integral. -/
@[powerlib_foundation] theorem kramersT_unique (hV : ∀ x, HasDerivAt V (V' x) x) (hD : D ≠ 0)
    {U U1 U2 : ℝ → ℝ} (hU : ∀ θ, HasDerivAt U (U1 θ) θ) (hU1 : ∀ θ, HasDerivAt U1 (U2 θ) θ)
    (hode : ∀ θ, D * U2 θ - V' θ * U1 θ = -γ) (hc : U θc = 0) (hr : U1 θr = 0) :
    U = kramersT V D γ θr θc := by
  have hT := kramersT_ode (γ := γ) (θr := θr) (θc := θc) hV hD
  set T1 : ℝ → ℝ := fun u => -(γ / D) * outerG V D θr u
  set W1 : ℝ → ℝ := fun θ => U1 θ - T1 θ
  -- `e^{−V/D} W1` is constant
  have hq : ∀ θ, HasDerivAt (fun θ => exp (-V θ / D) * W1 θ) 0 θ := by
    intro θ
    have he : HasDerivAt (fun θ => exp (-V θ / D)) (exp (-V θ / D) * (-V' θ / D)) θ := by
      have := ((hV θ).neg.div_const D).exp
      convert! this using 1
    have hw : HasDerivAt W1 (U2 θ - (-(γ / D) * (V' θ / D * outerG V D θr θ + 1))) θ :=
      (hU1 θ).sub (hT θ).2.1
    convert! he.mul hw using 1
    have h1 := hode θ
    have hU2 : U2 θ = (V' θ * U1 θ - γ) / D := by field_simp; linarith
    simp only [W1, T1]
    rw [hU2]
    field_simp
    ring
  have hqc : ∀ θ, exp (-V θ / D) * W1 θ = exp (-V θr / D) * W1 θr := fun θ =>
    is_const_of_deriv_eq_zero (fun s => (hq s).differentiableAt) (fun s => (hq s).deriv) θ θr
  have hW1r : W1 θr = 0 := by
    simp only [W1, T1, hr]; rw [kramersT_reflecting]; ring
  have hW1 : ∀ θ, U1 θ = T1 θ := by
    intro θ
    have := hqc θ
    rw [hW1r, mul_zero] at this
    have := (mul_eq_zero.mp this).resolve_left (exp_pos _).ne'
    simp only [W1] at this; linarith
  -- `U − T` is constant and vanishes at `θ_c`
  have hd : ∀ θ, HasDerivAt (fun θ => U θ - kramersT V D γ θr θc θ) 0 θ := by
    intro θ
    have := (hU θ).sub (hT θ).1
    rwa [hW1 θ, sub_self] at this
  funext θ
  have := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) θ θc
  rw [hc, kramersT_absorbing, sub_zero] at this
  linarith

/-- Positivity inside the domain: `T(θ) > 0` for `θ_r < θ < θ_c` (`γ, D > 0`). -/
@[powerlib_foundation] theorem kramersT_pos (hV : Continuous V) (hD : 0 < D) (hγ : 0 < γ)
    {θ : ℝ} (h1 : θr ≤ θ) (h2 : θ < θc) : 0 < kramersT V D γ θr θc θ := by
  unfold kramersT
  apply mul_pos (div_pos hγ hD)
  have hI : ∀ y, θr < y → 0 < innerI V D θr y := by
    intro y hy
    unfold innerI
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      ((by fun_prop : Continuous fun z => exp (-V z / D)).intervalIntegrable _ _)
      (fun z _ => exp_pos _) hy
  have hpos : ∀ y ∈ Ioo θ θc, 0 < outerG V D θr y := fun y hy =>
    mul_pos (exp_pos _) (hI y (lt_of_le_of_lt h1 hy.1))
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    ((outerG_continuous hV).intervalIntegrable _ _) hpos h2

/-! ## Correction: backward vs adjoint form (§1.2) -/

/-- For any `C²` function `T`, the adjoint-form expression `−(1/γ)(V' T)' + (D/γ) T''` equals the
backward expression `−(V'/γ) T' + (D/γ) T''` minus `V'' T/γ`. -/
@[powerlib_foundation] theorem adjointForm_residual {V2 : ℝ → ℝ} {T T1 : ℝ → ℝ} {θ : ℝ}
    (hV' : HasDerivAt V' (V2 θ) θ) (hT : HasDerivAt T (T1 θ) θ) (T2 : ℝ) :
    HasDerivAt (fun u => V' u * T u) (V2 θ * T θ + V' θ * T1 θ) θ ∧
      -(1 / γ) * (V2 θ * T θ + V' θ * T1 θ) + D / γ * T2 =
        (-(V' θ / γ) * T1 θ + D / γ * T2) - V2 θ * T θ / γ := by
  refine ⟨hV'.mul hT, ?_⟩
  ring

/-- **The adjoint form fails for the MFPT** inside a convex well: the Kramers solution satisfies the
backward equation, and its adjoint-form value is `−1 − V'' T/γ ≠ −1` wherever `V'' T ≠ 0`. -/
@[powerlib_foundation] theorem adjointForm_ne (hV : ∀ x, HasDerivAt V (V' x) x) {V2 : ℝ → ℝ}
    (hV' : ∀ x, HasDerivAt V' (V2 x) x) (hD : 0 < D) (hγ : 0 < γ) {θ : ℝ} (h1 : θr ≤ θ)
    (h2 : θ < θc) (hconv : 0 < V2 θ) :
    HasDerivAt (fun u => V' u * kramersT V D γ θr θc u)
        (V2 θ * kramersT V D γ θr θc θ + V' θ * (-(γ / D) * outerG V D θr θ)) θ ∧
      -(1 / γ) * (V2 θ * kramersT V D γ θr θc θ + V' θ * (-(γ / D) * outerG V D θr θ)) +
        D / γ * (-(γ / D) * (V' θ / D * outerG V D θr θ + 1)) ≠ -1 := by
  have hVc : Continuous V := continuous_iff_continuousAt.2 fun x => (hV x).continuousAt
  have hT := kramersT_pos (γ := γ) (θc := θc) hVc hD hγ h1 h2
  have key : -(1 / γ) * (V2 θ * kramersT V D γ θr θc θ + V' θ * (-(γ / D) * outerG V D θr θ)) +
      D / γ * (-(γ / D) * (V' θ / D * outerG V D θr θ + 1)) =
      -1 - V2 θ * kramersT V D γ θr θc θ / γ := by
    field_simp; ring
  refine ⟨(hV' θ).mul (kramersT_hasDerivAt hVc θ), ?_⟩
  rw [key]
  have : 0 < V2 θ * kramersT V D γ θr θc θ / γ := div_pos (mul_pos hconv hT) hγ
  linarith

/-! ## Prefactor algebra and explicit cases -/

/-- **Kramers prefactor (§1.4)**: the two Gaussian factors combine as
`(γ/D) √(2πD/κ_b) √(2πD/κ_a) = 2πγ/√(κ_a κ_b)` (`κ_a = V''(θ_a)`, `κ_b = |V''(θ_b)|`); `D`
cancels. -/
@[powerlib_foundation] theorem kramers_prefactor {κa κb : ℝ} (hD : 0 < D) (ha : 0 < κa)
    (hb : 0 < κb) :
    γ / D * √(2 * π * D / κb) * √(2 * π * D / κa) = 2 * π * γ / √(κa * κb) := by
  have hπ : 0 < π := pi_pos
  rw [mul_assoc, ← Real.sqrt_mul (by positivity)]
  rw [show 2 * π * D / κb * (2 * π * D / κa) = (2 * π * D) ^ 2 / (κa * κb) by field_simp,
    Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]
  field_simp

/-- Pure diffusion between two absorbing points (`V' = 0`, `L = D d²/dθ²`): the MFPT
`m(θ) = (θ − a)(b − θ)/(2D)` solves `D m'' = −1`, `m(a) = m(b) = 0`. -/
@[powerlib_foundation] theorem mfpt_free_diffusion {a b : ℝ} (hD : D ≠ 0) (θ : ℝ) :
    HasDerivAt (fun x => (x - a) * (b - x) / (2 * D)) ((a + b - 2 * θ) / (2 * D)) θ ∧
      HasDerivAt (fun x => (a + b - 2 * x) / (2 * D)) (-2 / (2 * D)) θ ∧
      D * (-2 / (2 * D)) = -1 ∧
      (a - a) * (b - a) / (2 * D) = 0 ∧ (b - a) * (b - b) / (2 * D) = 0 := by
  refine ⟨?_, ?_, by field_simp, by simp, by simp⟩
  · have := (((hasDerivAt_id' θ).sub_const a).mul ((hasDerivAt_id' θ).const_sub b)).div_const
      (2 * D)
    convert! this using 1; ring
  · have := (((hasDerivAt_id' θ).const_mul 2).const_sub (a + b)).div_const (2 * D)
    convert! this using 1; ring

/-- Hit probability before `T` is one minus the survival probability: `h = 1 − s`. -/
@[powerlib_foundation] theorem hit_eq_one_sub_survival {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {τ : Ω → ℝ} (hτ : Measurable τ) (t : ℝ) :
    P.real {ω | τ ω ≤ t} = 1 - P.real {ω | t < τ ω} := by
  have hs : MeasurableSet {ω | t < τ ω} := measurableSet_lt measurable_const hτ
  have : {ω | τ ω ≤ t} = {ω | t < τ ω}ᶜ := by ext ω; simp
  rw [this, probReal_compl_eq_one_sub hs]

end powerlib.Stochastic.MFPT
