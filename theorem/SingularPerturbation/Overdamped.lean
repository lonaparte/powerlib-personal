import theorem.Dynamics.Linearization
import theorem.Dynamics.Coordinates
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Overdamped (Smoluchowski) limit: energy balance, Boltzmann density, rescaling

Foundation layer (categories B and C).

Source: work-sync `theory/T-overdamped-limit.md` §1.2 (Smoluchowski equation, Boltzmann
stationary density `p ∝ exp(−V/D)`), §1.3 (multiscale rescaling), §1.5 (energy dissipation),
§1.7 (stationary Fokker–Planck check).

Model boundary: scalar Newton form `m θ̈ + γ θ̇ + V'(θ) = F(t)` with constant `m, γ`; potential `V`
differentiable (`C²` where stated); deterministic trajectories for the energy identity; for the
density statement, the Smoluchowski Fokker–Planck flux `J = −(V'/γ) p − (D/γ) p'` with constant
`D > 0` (no stochastic calculus is used: the claim is that the Boltzmann density makes `J ≡ 0`).

Results.
* `energy_balance`: along every trajectory, `d/dt [½ m θ̇² + V(θ)] = −γ θ̇² + F θ̇`.
* `boltzmann_hasDerivAt`, `boltzmann_flux_zero`: `p = e^{−V/D}/Z` has `p' = −(V'/D) p`, so the
  probability flux vanishes identically (stationary, detailed balance);
  `boltzmann_integral_eq_one`, `boltzmann_pos`: under the integrability premise
  `∫ e^{−V/D} < ∞` (which the note leaves implicit) `p` is a probability density.
* `gradientFlow_locallyExponentiallyStable` (C: application of
  `Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian`): the overdamped flow
  `θ̇ = −V'(θ)/γ` (`V ∈ C²`, `γ > 0`) is locally exponentially stable at every critical point with
  `V''(θ*) > 0`.
* Correction (§1.3): with `κ = V''_max > 0`, `τ_V = γ/κ`, `ϑ(s) = θ(τ_V s)`, the exact rescaled
  equation is `ε² ϑ'' + ϑ' + V'(ϑ)/κ = F(τ_V s)/κ` with `ε² = mκ/γ²` (`rescaled_equation`); the
  note's `ε = √(m/(γ² τ_V))` and `ε² ϑ'' + ε ϑ' + V'(ϑ) = F` are wrong: for `m = κ = 1`, `γ = 2`,
  `V' = F = 0` the solution `θ = e^{−2t}` violates the note's equation (`note_rescaling_false`).
-/

noncomputable section
namespace powerlib.SingularPerturbation.Overdamped
open Real MeasureTheory

/-- **Energy balance** `dE/dt = −γ θ̇² + F θ̇` for `E = ½ m θ̇² + V(θ)`. -/
@[powerlib_foundation] theorem energy_balance {m γ : ℝ} {V V' F θ ω a : ℝ → ℝ} {t : ℝ}
    (hθ : HasDerivAt θ (ω t) t) (hω : HasDerivAt ω (a t) t) (hV : HasDerivAt V (V' (θ t)) (θ t))
    (heq : m * a t + γ * ω t + V' (θ t) = F t) :
    HasDerivAt (fun s => m / 2 * ω s ^ 2 + V (θ s)) (-γ * ω t ^ 2 + F t * ω t) t := by
  have h1 := (hω.pow 2).const_mul (m / 2)
  have h2 := hV.comp t hθ
  refine (h1.add h2).congr_deriv ?_
  simp only [Nat.cast_ofNat]
  linear_combination (ω t) * heq

/-- Unnormalised Boltzmann weight `e^{−V/D}`. -/
def weight (V : ℝ → ℝ) (D θ : ℝ) : ℝ := Real.exp (-V θ / D)

/-- `(e^{−V/D})' = −(V'/D) e^{−V/D}`. -/
@[powerlib_foundation] theorem boltzmann_hasDerivAt {V V' : ℝ → ℝ} (D : ℝ) (Z : ℝ) {θ : ℝ}
    (hV : HasDerivAt V (V' θ) θ) :
    HasDerivAt (fun x => weight V D x / Z) (-(V' θ / D) * (weight V D θ / Z)) θ := by
  unfold weight
  have := ((hV.neg.div_const D).exp).div_const Z
  simp only [Pi.neg_apply] at this
  convert this using 1
  ring

/-- **Zero flux**: `J = −(V'/γ) p − (D/γ) p' = 0` for the Boltzmann density. -/
@[powerlib_foundation] theorem boltzmann_flux_zero {V V' : ℝ → ℝ} {D γ Z : ℝ} (hD : D ≠ 0)
    {θ : ℝ} (hV : HasDerivAt V (V' θ) θ) :
    -(V' θ / γ) * (weight V D θ / Z) - D / γ * (deriv (fun x => weight V D x / Z) θ) = 0 := by
  rw [(boltzmann_hasDerivAt D Z hV).deriv]
  field_simp
  ring

@[powerlib_foundation] theorem boltzmann_pos (V : ℝ → ℝ) (D θ : ℝ) : 0 < weight V D θ :=
  Real.exp_pos _

/-- With the integrability premise `∫ e^{−V/D} < ∞`, `p = e^{−V/D}/Z`, `Z = ∫ e^{−V/D}`, is a
probability density. -/
@[powerlib_foundation] theorem boltzmann_integral_eq_one {V : ℝ → ℝ} {D : ℝ}
    (hint : Integrable (fun θ => weight V D θ)) :
    ∫ θ, weight V D θ / (∫ x, weight V D x) = 1 := by
  have hZ : 0 < ∫ x, weight V D x :=
    integral_exp_pos (f := fun x => -V x / D) hint
  rw [integral_div, div_self hZ.ne']

/-! ## Overdamped gradient flow (C wrapper of the linearization theorem) -/

/-- Overdamped flow `θ̇ = −V'(θ)/γ` on `State 1`. -/
def gradField (V : ℝ → ℝ) (γ : ℝ) (y : Dynamics.State 1) : Dynamics.State 1 :=
  WithLp.toLp 2 ![-(deriv V (y 0)) / γ]

/-- The overdamped gradient flow is locally exponentially stable at a nondegenerate minimum. -/
@[powerlib_foundation] theorem gradientFlow_locallyExponentiallyStable {V : ℝ → ℝ} {γ θs : ℝ}
    (hV : ContDiff ℝ 2 V) (hγ : 0 < γ) (hcrit : deriv V θs = 0)
    (hmin : 0 < deriv (deriv V) θs) :
    LocallyExponentiallyStable (gradField V γ) (WithLp.toLp 2 ![θs]) := by
  have h2 : ContDiff ℝ (1 + 1) V := by simpa [one_add_one_eq_two] using hV
  have hdV : ContDiff ℝ 1 (deriv V) := h2.deriv'
  have hdiff : Differentiable ℝ (deriv V) := hdV.differentiable one_ne_zero
  have hcd : ContDiff ℝ 1 (gradField V γ) := by
    apply Dynamics.contDiff_of_components
    intro i; fin_cases i
    simp only [gradField]
    simp
    exact ((hdV.comp (Dynamics.coord 0).contDiff).neg).div_const γ
  set xs : Dynamics.State 1 := WithLp.toLp 2 ![θs]
  have hc : HasFDerivAt (fun y : Dynamics.State 1 => deriv V (y 0))
      ((deriv (deriv V) θs) • Dynamics.coord 0) xs := by
    have h1 : HasDerivAt (deriv V) (deriv (deriv V) θs) (xs 0) := (hdiff θs).hasDerivAt
    have h := h1.comp_hasFDerivAt xs (Dynamics.hasFDerivAt_coord 0 xs)
    exact h
  refine Dynamics.locallyExponentiallyStable_of_isHurwitz_jacobian
    (!![-(deriv (deriv V) θs) / γ]) hcd ?_ ?_ ?_
  · ext i; fin_cases i; simp [gradField, xs, hcrit]
  · refine Dynamics.fderiv_eq_toEuclideanCLM_of_components _
      ![γ⁻¹ • -((deriv (deriv V) θs) • Dynamics.coord 0)] ?_ ?_
    · intro i; fin_cases i
      have h := hc.neg.const_smul γ⁻¹
      convert h using 1
      all_goals first | rfl | (funext y; simp [gradField]; ring)
    · intro i v; fin_cases i; simp [Dynamics.coord]; ring
  · intro μ v hv heig
    have h0 := congrFun heig 0
    simp [Matrix.mulVec, dotProduct] at h0
    have hv0 : v 0 ≠ 0 := by
      intro h; apply hv; funext j; fin_cases j; exact h
    have hre : (-(↑(deriv (deriv V) θs) : ℂ) / (γ : ℂ)).re = -(deriv (deriv V) θs) / γ := by
      rw [show (-(↑(deriv (deriv V) θs) : ℂ) / (γ : ℂ)) = ((-(deriv (deriv V) θs) / γ : ℝ) : ℂ)
        by push_cast; ring, Complex.ofReal_re]
    have hneg : -(deriv (deriv V) θs) / γ < 0 := div_neg_of_neg_of_pos (by linarith) hγ
    rcases h0 with h | h
    · rw [← h, hre]; simpa using hneg
    · exact absurd h hv0

/-! ## Correction: the multiscale rescaling -/

/-- **Exact rescaling**: if `m θ̈ + γ θ̇ + V'(θ) = F(t)` and `ϑ(s) = θ(τ_V s)`, `τ_V = γ/κ`, then
`(mκ/γ²) ϑ'' + ϑ' + V'(ϑ)/κ = F(τ_V s)/κ`, i.e. `ε² = mκ/γ²`. -/
@[powerlib_foundation] theorem rescaled_equation {m γ κ : ℝ} (hγ : γ ≠ 0) (hκ : κ ≠ 0)
    {V' F ω a θ : ℝ → ℝ} (heq : ∀ t, m * a t + γ * ω t + V' (θ t) = F t) (s : ℝ) :
    m * κ / γ ^ 2 * ((γ / κ) ^ 2 * a (γ / κ * s)) + (γ / κ) * ω (γ / κ * s) +
        V' (θ (γ / κ * s)) / κ = F (γ / κ * s) / κ := by
  have := heq (γ / κ * s)
  generalize γ / κ * s = u at this ⊢
  field_simp
  linear_combination this

/-- The rescaled derivatives of `ϑ(s) = θ(τ_V s)`. -/
@[powerlib_foundation] theorem rescaled_derivs {θ ω a : ℝ → ℝ} {τV s : ℝ}
    (hθ : ∀ t, HasDerivAt θ (ω t) t) (hω : ∀ t, HasDerivAt ω (a t) t) :
    HasDerivAt (fun u => θ (τV * u)) (τV * ω (τV * s)) s ∧
      HasDerivAt (fun u => τV * ω (τV * u)) (τV ^ 2 * a (τV * s)) s := by
  constructor
  · have := (hθ (τV * s)).comp s ((hasDerivAt_id' s).const_mul τV)
    exact this.congr_deriv (by ring)
  · have := ((hω (τV * s)).comp s ((hasDerivAt_id' s).const_mul τV)).const_mul τV
    exact this.congr_deriv (by ring)

/-- The note's rescaled equation `ε² ϑ'' + ε ϑ' + V'(ϑ) = F` with `ε² = m/(γ² τ_V)` fails:
`m = κ = 1`, `γ = 2` (`τ_V = 2`, `ε² = 1/8`), `V' = F = 0`, `θ(t) = e^{−2t}` solves the original
equation, but `ϑ(s) = e^{−4s}` gives `ε² ϑ''(0) + ε ϑ'(0) = 2 − √2 ≠ 0`. -/
@[powerlib_foundation] theorem note_rescaling_false :
    (∀ t : ℝ, 1 * (4 * Real.exp (-2 * t)) + 2 * (-2 * Real.exp (-2 * t)) + 0 = 0) ∧
      (1 / 8 : ℝ) * (16 * Real.exp (-4 * 0)) + Real.sqrt (1 / 8) * (-4 * Real.exp (-4 * 0)) + 0 ≠ 0 := by
  refine ⟨fun t => by ring, ?_⟩
  simp only [mul_zero, Real.exp_zero, mul_one, add_zero]
  have h8 : Real.sqrt (1 / 8) = Real.sqrt 2 / 4 := by
    rw [show (1 / 8 : ℝ) = (Real.sqrt 2 / 4) ^ 2 by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num]
    exact Real.sqrt_sq (by positivity)
  rw [h8]
  intro h
  have : Real.sqrt 2 = 2 := by linarith
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [this] at h2
  norm_num at h2

/-- `θ(t) = e^{−2t}` and its derivatives (support for `note_rescaling_false`). -/
@[powerlib_foundation] theorem exp_solution_derivs (t : ℝ) :
    HasDerivAt (fun s => Real.exp (-2 * s)) (-2 * Real.exp (-2 * t)) t ∧
      HasDerivAt (fun s => -2 * Real.exp (-2 * s)) (4 * Real.exp (-2 * t)) t := by
  have h := ((hasDerivAt_id' t).const_mul (-2)).exp
  constructor
  · convert h using 1; ring
  · convert h.const_mul (-2) using 1; ring

end powerlib.SingularPerturbation.Overdamped
