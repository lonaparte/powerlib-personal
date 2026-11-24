import theorem.WPT.LossyLimits
import theorem.SpecialFunctions.BoxQuadratic
import theorem.SpecialFunctions.Duality

/-! # The exact output-power limit of the lossy link under bridge, flux and soft-switching limits

The exact largest real power `−Re(V₂ Ī₂)` the secondary bridge of the tuned lossy series–series
link absorbs when both bridge voltages, both coil fluxes and a soft-switching margin constrain it
at once, `‖V₁‖ ≤ ρ₁`, `‖V₂‖ ≤ ρ₂`, `‖ψ₁‖² ≤ Ψ₁²`, `‖ψ₂‖² ≤ Ψ₂²`, `Q = Im(V₁ Ī₁) ≥ Q_min`,
characterized by Lagrangian strong duality.

On the resonant link the currents are linear in the bridge phasors (`CurrentLimits.currents_eq`),
so every quantity of interest is a Hermitian form of `(V₁, V₂)`, i.e. an affine function of the
lift `(U, W, z) = (‖V₁‖², ‖V₂‖², V₁ V̄₂)`. With `Δ = R₁R₂ + (ωM)²`: the output power is
`(−ωM Im z − R₁ W)/Δ` (`LossyLimits.outputPower_eq`); both bridge ports carry the reactive power
`Im(V₁ Ī₁) = Im(V₂ Ī₂) = ωM Re z/Δ`; and `Δψ₁ = (L₁R₂ − jωM M)V₁ + (MR₁ − jωM L₁)V₂`,
`Δψ₂ = (MR₂ − jωM L₂)V₁ + (L₂R₁ − jωM M)V₂`, so `‖ψ_k‖² = fluxForm_k(U, W, z)` with
nonnegative coefficients of `U`. The Lagrangian
`P_out − μ₁(‖ψ₁‖² − Ψ₁²) − μ₂(‖ψ₂‖² − Ψ₂²) − ν(Q_min − Q)` is `μ₁Ψ₁² + μ₂Ψ₂² − νQ_min` plus the
Hermitian form `a‖V₁‖² + b‖V₂‖² + 2 Re(c V₁ V̄₂)` with the explicit coefficients `lagrangeCoeff₁`,
`lagrangeCoeff₂`, `lagrangeCross`, whose largest value on the bridge bidisk is
`boxQuadMax a b ‖c‖ ρ₁ ρ₂` (`SpecialFunctions.isGreatest_hermitian_boxQuadMax`): this is the dual
function `dualBound`.

Physical reading. Any multipliers `μ₁, μ₂, ν ≥ 0` certify the upper bound `dualBound μ₁ μ₂ ν` on
the output power of every admissible operating point, and any admissible operating point gives a
lower bound on the limit. The exact limit `outputEnvelope` is the least value of `dualBound` over
the nonnegative orthant: the boundary of the operating envelope is located by minimizing an
explicit closed-form function of three variables, and that function is convex
(`convexOn_dualBound`), so this is a small convex program. With all multipliers zero the
certificate is the bridge-only limit `LossyLimits.outputLimit` (`dualBound_zero`); the regimes
in which the bridges alone or the bridges with one flux bound set the limit have the closed forms
of `theorem/WPT/LossyLimits.lean` and `theorem/WPT/LossyFlux.lean` (with their exactness
conditions, and without the margin). Without the margin (`ν = 0`) the characterization holds with
two multipliers (`fluxEnvelope`), and Slater's condition is then automatic.

The strong duality is proved in the lift. The lifted bridge set
`SpecialFunctions.bidiskLift ρ₁ ρ₂` is convex, objective and constraints are affine there, and a
lifted feasible point is realized by bridge phasors with the same `W` and `z` and a smaller `U`
(`SpecialFunctions.exists_lift_of_mem_bidiskLift`); the objective and the margin do not involve
`U` and the flux forms are nondecreasing in it, so the lifted program has the value of the phasor
program. Slater's condition and `SpecialFunctions.exists_lagrangian_le` give multipliers that bound
the lifted Lagrangian by the optimum; at a bidisk maximizer of the Lagrangian this is
`dualBound ≤ optimum`. The optimum exists by compactness of the admissible bridge phasors.

Model boundary.
* The coil pair `w : Passive.Coupled` (boundary of `theorem/Passive/Coupled.lean`: linear
  magnetics, no saturation, hysteresis or core loss) at one angular frequency, RMS phasors in
  sinusoidal steady state: both ports driven by the fundamental voltage phasors `V₁`, `V₂` of two
  bridges, port currents `I₁`, `I₂` into the dotted terminals (`CurrentLimits.Driven`); the
  boundary of `theorem/WPT/CurrentLimits.lean`.
* Resonant tuning `X₁(ω) = X₂(ω) = 0` and `Δ = R₁R₂ + (ωM)² ≠ 0` throughout (no sign condition on
  `R₁`, `R₂`); `dualBound_zero` uses in addition `R₁ > 0`, `Δ > 0`, `ωM ≠ 0`, `ρ_k ≥ 0`, as in
  `theorem/WPT/LossyLimits.lean`. The detuned link is not covered.
* Fundamental-harmonic approximation. The bridge constraint is `‖V_k‖ ≤ ρ_k` on the fundamental.
  The flux bounds `‖ψ_k‖² ≤ Ψ_k²` bound the fundamental flux-linkage phasors
  `Passive.Coupled.flux₁`, `flux₂`; how a core-saturation, core-loss or field-exposure rating
  translates into `Ψ_k` is not modelled. The soft-switching margin is the fundamental reading of
  zero-voltage switching as inductive bridge ports, `Im(V₁ Ī₁) ≥ Q_min`; on the resonant link the
  secondary port carries the same reactive power (`reactive₂_eq_reactive₁`), so the one margin
  covers both bridges. The commutation interval, dead time, device capacitances, harmonic
  currents, device and capacitor ratings, bridge losses and the DC-link dynamics are not
  modelled. The output power is the fundamental real power `−Re(V₂ Ī₂)` absorbed by the
  secondary bridge.
* Strong duality assumes Slater's condition, stated as a hypothesis: an operating point within
  both bridges with both flux bounds and the margin strict. Without the margin it holds for
  `Ψ₁, Ψ₂ ≠ 0`, `ρ_k ≥ 0` (zero bridge voltages). The existence of the optimum assumes one
  admissible operating point. The value is the minimum of an explicit convex function; no closed
  form of the minimizing multipliers is given.

Source: the resonant-link currents `CurrentLimits.currents_eq`, `CurrentLimits.driven_currents`
and the driven two-port `CurrentLimits.Driven` (`theorem/WPT/CurrentLimits.lean`); the output
power `LossyLimits.outputPower_eq` and the bridge-only limit `LossyLimits.outputLimit`,
`LossyLimits.isGreatest_outputPower` (`theorem/WPT/LossyLimits.lean`); the flux linkages of
`theorem/Passive/Coupled.lean`; Lagrangian duality under Slater's condition,
`SpecialFunctions.exists_lagrangian_le` (`theorem/SpecialFunctions/Duality.lean`; M. Slater, 1950;
S. Boyd and L. Vandenberghe, *Convex Optimization*, 2004, §5.3.2); the bidisk maximum of a
Hermitian form `SpecialFunctions.boxQuadMax` and the convex lift
`SpecialFunctions.bidiskLift` (`theorem/SpecialFunctions/BoxQuadratic.lean`), i.e. the semidefinite
lifting of a quadratically constrained program in two complex variables, exact here.

Results.
* `fluxForm₁`, `fluxForm₂` (the squared fluxes `‖ψ_k‖²` as affine functions of `(U, W, z)`),
  `lagrangeCoeff₁`, `lagrangeCoeff₂`, `lagrangeCross` (the coefficients `a`, `b`, `c` of the
  Lagrangian as a Hermitian form of `(V₁, V₂)`), `dualBound` (the dual function
  `μ₁Ψ₁² + μ₂Ψ₂² − νQ_min + boxQuadMax a b ‖c‖ ρ₁ ρ₂`), `outputEnvelope` (its least value over
  `μ₁, μ₂, ν ≥ 0`), `fluxEnvelope` (the least value of `dualBound` over `μ₁, μ₂ ≥ 0` at `ν = 0`).
* `reactive₁_eq` (`Im(V₁ Ī₁) = ωM Re(V₁ V̄₂)/Δ`), `reactive₂_eq_reactive₁`
  (`Im(V₂ Ī₂) = Im(V₁ Ī₁)`), `normSq_flux₁_eq`, `normSq_flux₂_eq`
  (`‖ψ_k‖² = fluxForm_k(‖V₁‖², ‖V₂‖², V₁ V̄₂)`), `lagrangian_eq` (the Lagrangian equals
  `a‖V₁‖² + b‖V₂‖² + 2 Re(c V₁ V̄₂)` plus the constant terms), all on the resonant link.
* `outputPower_le_dualBound` (weak duality: every admissible operating point has
  `−Re(V₂ Ī₂) ≤ dualBound μ₁ μ₂ ν` for all `μ₁, μ₂, ν ≥ 0`), `convexOn_dualBound` (`dualBound` is
  convex in `(μ₁, μ₂, ν)`), `dualBound_zero` (`dualBound 0 0 0 = LossyLimits.outputLimit`).
* `exists_isGreatest_outputPower` (with one admissible operating point, the largest output power
  is attained), `isGreatest_outputEnvelope`, `isLeast_outputEnvelope` (strong duality under
  Slater's condition: `outputEnvelope` is the greatest output power of the admissible operating
  points and the least value of `dualBound` over `μ₁, μ₂, ν ≥ 0`).
* Without the margin: `isGreatest_fluxEnvelope`, `isLeast_fluxEnvelope` (for `Ψ₁, Ψ₂ ≠ 0` and
  `ρ_k ≥ 0`, `fluxEnvelope` is the greatest output power under both bridges and both flux bounds
  and the least value of `dualBound μ₁ μ₂ 0` over `μ₁, μ₂ ≥ 0`).
-/

noncomputable section

namespace powerlib.WPT.LossyEnvelope

open Complex ComplexConjugate CurrentLimits LossyLimits SpecialFunctions

variable (w : Passive.Coupled) (ω : ℝ)

/-- The squared primary flux of the resonant link as a function of the lift
`(U, W, z) = (‖V₁‖², ‖V₂‖², V₁ V̄₂)`:
`(((L₁R₂)² + (MωM)²) U + ((MR₁)² + (L₁ωM)²) W + 2 (L₁MΔ Re z − ωM(L₁²R₂ − M²R₁) Im z))/Δ²`. -/
def fluxForm₁ (U W : ℝ) (z : ℂ) : ℝ :=
  (((w.primary.L * w.secondary.R) ^ 2 + (w.M * (ω * w.M)) ^ 2) * U +
    ((w.M * w.primary.R) ^ 2 + (w.primary.L * (ω * w.M)) ^ 2) * W +
    2 * (w.primary.L * w.M * determinant w ω * z.re -
      ω * w.M * (w.primary.L ^ 2 * w.secondary.R - w.M ^ 2 * w.primary.R) * z.im)) /
    determinant w ω ^ 2

/-- The squared secondary flux of the resonant link as a function of the lift
`(U, W, z) = (‖V₁‖², ‖V₂‖², V₁ V̄₂)`:
`(((MR₂)² + (L₂ωM)²) U + ((L₂R₁)² + (MωM)²) W + 2 (L₂MΔ Re z − ωM(M²R₂ − L₂²R₁) Im z))/Δ²`. -/
def fluxForm₂ (U W : ℝ) (z : ℂ) : ℝ :=
  (((w.M * w.secondary.R) ^ 2 + (w.secondary.L * (ω * w.M)) ^ 2) * U +
    ((w.secondary.L * w.primary.R) ^ 2 + (w.M * (ω * w.M)) ^ 2) * W +
    2 * (w.secondary.L * w.M * determinant w ω * z.re -
      ω * w.M * (w.M ^ 2 * w.secondary.R - w.secondary.L ^ 2 * w.primary.R) * z.im)) /
    determinant w ω ^ 2

/-- The coefficient of `‖V₁‖²` in the Lagrangian:
`−(μ₁((L₁R₂)² + (MωM)²) + μ₂((MR₂)² + (L₂ωM)²))/Δ²`. -/
def lagrangeCoeff₁ (μ₁ μ₂ : ℝ) : ℝ :=
  -(μ₁ * ((w.primary.L * w.secondary.R) ^ 2 + (w.M * (ω * w.M)) ^ 2) +
    μ₂ * ((w.M * w.secondary.R) ^ 2 + (w.secondary.L * (ω * w.M)) ^ 2)) / determinant w ω ^ 2

/-- The coefficient of `‖V₂‖²` in the Lagrangian:
`−R₁/Δ − (μ₁((MR₁)² + (L₁ωM)²) + μ₂((L₂R₁)² + (MωM)²))/Δ²`. -/
def lagrangeCoeff₂ (μ₁ μ₂ : ℝ) : ℝ :=
  -w.primary.R / determinant w ω -
    (μ₁ * ((w.M * w.primary.R) ^ 2 + (w.primary.L * (ω * w.M)) ^ 2) +
      μ₂ * ((w.secondary.L * w.primary.R) ^ 2 + (w.M * (ω * w.M)) ^ 2)) / determinant w ω ^ 2

/-- The cross coefficient `c` of `2 Re(c V₁ V̄₂)` in the Lagrangian:
`Re c = (νωM/2 − M(μ₁L₁ + μ₂L₂))/Δ`,
`Im c = ωM/(2Δ) − ωM(μ₁(L₁²R₂ − M²R₁) + μ₂(M²R₂ − L₂²R₁))/Δ²`. -/
def lagrangeCross (μ₁ μ₂ ν : ℝ) : ℂ :=
  ⟨(ν * (ω * w.M) / 2 - w.M * (μ₁ * w.primary.L + μ₂ * w.secondary.L)) / determinant w ω,
    ω * w.M / (2 * determinant w ω) -
      ω * w.M * (μ₁ * (w.primary.L ^ 2 * w.secondary.R - w.M ^ 2 * w.primary.R) +
        μ₂ * (w.M ^ 2 * w.secondary.R - w.secondary.L ^ 2 * w.primary.R)) / determinant w ω ^ 2⟩

/-- The dual function of the output-power program with multipliers `μ₁`, `μ₂` (flux bounds) and
`ν` (soft-switching margin): `μ₁Ψ₁² + μ₂Ψ₂² − νQ_min + boxQuadMax a b ‖c‖ ρ₁ ρ₂`, with
`a = lagrangeCoeff₁ μ₁ μ₂`, `b = lagrangeCoeff₂ μ₁ μ₂`, `c = lagrangeCross μ₁ μ₂ ν`. -/
def dualBound (ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin μ₁ μ₂ ν : ℝ) : ℝ :=
  μ₁ * Ψ₁ ^ 2 + μ₂ * Ψ₂ ^ 2 - ν * Qmin +
    boxQuadMax (lagrangeCoeff₁ w ω μ₁ μ₂) (lagrangeCoeff₂ w ω μ₁ μ₂)
      ‖lagrangeCross w ω μ₁ μ₂ ν‖ ρ₁ ρ₂

/-- The least value of the dual function over the nonnegative multipliers `μ₁, μ₂, ν ≥ 0`. -/
def outputEnvelope (ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin : ℝ) : ℝ :=
  sInf {d | ∃ μ₁ μ₂ ν : ℝ, 0 ≤ μ₁ ∧ 0 ≤ μ₂ ∧ 0 ≤ ν ∧ d = dualBound w ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin μ₁ μ₂ ν}

/-- The least value of the dual function without the margin, `ν = 0`, over `μ₁, μ₂ ≥ 0`. -/
def fluxEnvelope (ρ₁ ρ₂ Ψ₁ Ψ₂ : ℝ) : ℝ :=
  sInf {d | ∃ μ₁ μ₂ : ℝ, 0 ≤ μ₁ ∧ 0 ≤ μ₂ ∧ d = dualBound w ω ρ₁ ρ₂ Ψ₁ Ψ₂ 0 μ₁ μ₂ 0}

/-! ## The quantities of the resonant link as Hermitian forms of the bridge phasors -/

section Identities

variable {w ω} {V₁ V₂ I₁ I₂ : ℂ}

/-- The reactive power of the primary bridge port of the resonant link:
`Im(V₁ Ī₁) = ωM Re(V₁ V̄₂)/Δ`. -/
@[tmio M, powerlib_domain] theorem reactive₁_eq (hX₁ : w.primary.reactance ω = 0)
    (hX₂ : w.secondary.reactance ω = 0) (hΔ : determinant w ω ≠ 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) :
    (V₁ * conj I₁).im = ω * w.M * (V₁ * conj V₂).re / determinant w ω := by
  rw [(currents_eq w ω hX₁ hX₂ hΔ h).1, map_div₀, Complex.conj_ofReal, mul_div_assoc',
    Complex.div_ofReal_im]
  congr 1
  simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Both bridge ports of the resonant link carry the same reactive power:
`Im(V₂ Ī₂) = Im(V₁ Ī₁)`. -/
@[tmio M, powerlib_domain] theorem reactive₂_eq_reactive₁ (hX₁ : w.primary.reactance ω = 0)
    (hX₂ : w.secondary.reactance ω = 0) (hΔ : determinant w ω ≠ 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) : (V₂ * conj I₂).im = (V₁ * conj I₁).im := by
  rw [reactive₁_eq hX₁ hX₂ hΔ h, (currents_eq w ω hX₁ hX₂ hΔ h).2, map_div₀,
    Complex.conj_ofReal, mul_div_assoc', Complex.div_ofReal_im]
  congr 1
  simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The output power in the lift: `−Re(V₂ Ī₂) = (−ωM Im(V₁ V̄₂) − R₁‖V₂‖²)/Δ`. -/
@[tmio M, powerlib_domain] private theorem outputPower_eq_lift
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) :
    -(V₂ * conj I₂).re =
      (-(ω * w.M) * (V₁ * conj V₂).im - w.primary.R * ‖V₂‖ ^ 2) / determinant w ω := by
  rw [outputPower_eq w ω hX₁ hX₂ hΔ h]
  congr 1
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The squared primary flux of the resonant link:
`‖ψ₁‖² = fluxForm₁(‖V₁‖², ‖V₂‖², V₁ V̄₂)`. -/
@[tmio M, powerlib_domain] theorem normSq_flux₁_eq (hX₁ : w.primary.reactance ω = 0)
    (hX₂ : w.secondary.reactance ω = 0) (hΔ : determinant w ω ≠ 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) :
    normSq (w.flux₁ I₁ I₂) = fluxForm₁ w ω (‖V₁‖ ^ 2) (‖V₂‖ ^ 2) (V₁ * conj V₂) := by
  obtain ⟨e1, e2⟩ := currents_eq w ω hX₁ hX₂ hΔ h
  rw [e1, e2, Passive.Coupled.flux₁, fluxForm₁, Complex.sq_norm, Complex.sq_norm]
  simp only [determinant] at hΔ ⊢
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re,
    Complex.conj_im]
  field_simp
  ring

/-- The squared secondary flux of the resonant link:
`‖ψ₂‖² = fluxForm₂(‖V₁‖², ‖V₂‖², V₁ V̄₂)`. -/
@[tmio M, powerlib_domain] theorem normSq_flux₂_eq (hX₁ : w.primary.reactance ω = 0)
    (hX₂ : w.secondary.reactance ω = 0) (hΔ : determinant w ω ≠ 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) :
    normSq (w.flux₂ I₁ I₂) = fluxForm₂ w ω (‖V₁‖ ^ 2) (‖V₂‖ ^ 2) (V₁ * conj V₂) := by
  obtain ⟨e1, e2⟩ := currents_eq w ω hX₁ hX₂ hΔ h
  rw [e1, e2, Passive.Coupled.flux₂, fluxForm₂, Complex.sq_norm, Complex.sq_norm]
  simp only [determinant] at hΔ ⊢
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re,
    Complex.conj_im]
  field_simp
  ring

end Identities

/-- The Lagrangian in the lift: `(−ωM Im z − R₁W)/Δ − μ₁ fluxForm₁ − μ₂ fluxForm₂ + ν ωM Re z/Δ
= a U + b W + 2 Re(c z)`. -/
@[tmio M, powerlib_domain] private theorem lift_lagrangian (hΔ : determinant w ω ≠ 0)
    (μ₁ μ₂ ν U W : ℝ) (z : ℂ) :
    (-(ω * w.M) * z.im - w.primary.R * W) / determinant w ω - μ₁ * fluxForm₁ w ω U W z -
        μ₂ * fluxForm₂ w ω U W z + ν * (ω * w.M * z.re / determinant w ω) =
      lagrangeCoeff₁ w ω μ₁ μ₂ * U + lagrangeCoeff₂ w ω μ₁ μ₂ * W +
        2 * (lagrangeCross w ω μ₁ μ₂ ν * z).re := by
  simp only [fluxForm₁, fluxForm₂, lagrangeCoeff₁, lagrangeCoeff₂, lagrangeCross, Complex.mul_re]
  field_simp
  ring

/-- The Lagrangian of the output-power program on the resonant link is a Hermitian form of the
bridge phasors: `−Re(V₂ Ī₂) − μ₁‖ψ₁‖² − μ₂‖ψ₂‖² + ν Im(V₁ Ī₁)
= a‖V₁‖² + b‖V₂‖² + 2 Re(c V₁ V̄₂)` with `a = lagrangeCoeff₁ μ₁ μ₂`, `b = lagrangeCoeff₂ μ₁ μ₂`,
`c = lagrangeCross μ₁ μ₂ ν`. -/
@[tmio M, powerlib_domain] theorem lagrangian_eq {V₁ V₂ I₁ I₂ : ℂ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) (μ₁ μ₂ ν : ℝ) :
    -(V₂ * conj I₂).re - μ₁ * normSq (w.flux₁ I₁ I₂) - μ₂ * normSq (w.flux₂ I₁ I₂) +
        ν * (V₁ * conj I₁).im =
      lagrangeCoeff₁ w ω μ₁ μ₂ * ‖V₁‖ ^ 2 + lagrangeCoeff₂ w ω μ₁ μ₂ * ‖V₂‖ ^ 2 +
        2 * (lagrangeCross w ω μ₁ μ₂ ν * V₁ * conj V₂).re := by
  rw [outputPower_eq_lift hX₁ hX₂ hΔ h, normSq_flux₁_eq hX₁ hX₂ hΔ h,
    normSq_flux₂_eq hX₁ hX₂ hΔ h, reactive₁_eq hX₁ hX₂ hΔ h, mul_assoc (lagrangeCross w ω μ₁ μ₂ ν)]
  exact lift_lagrangian w ω hΔ μ₁ μ₂ ν _ _ _

/-! ## Weak duality and the dual function -/

/-- **Weak duality**: for any multipliers `μ₁, μ₂, ν ≥ 0`, every operating point of the resonant
link within both bridges, both flux bounds and the margin delivers
`−Re(V₂ Ī₂) ≤ dualBound μ₁ μ₂ ν`. -/
@[tmio M, powerlib_domain] theorem outputPower_le_dualBound {V₁ V₂ I₁ I₂ : ℂ}
    {ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin μ₁ μ₂ ν : ℝ} (hX₁ : w.primary.reactance ω = 0)
    (hX₂ : w.secondary.reactance ω = 0) (hΔ : determinant w ω ≠ 0)
    (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁) (h₂ : ‖V₂‖ ≤ ρ₂)
    (hψ₁ : normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2) (hψ₂ : normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2)
    (hQ : Qmin ≤ (V₁ * conj I₁).im) (hμ₁ : 0 ≤ μ₁) (hμ₂ : 0 ≤ μ₂) (hν : 0 ≤ ν) :
    -(V₂ * conj I₂).re ≤ dualBound w ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin μ₁ μ₂ ν := by
  have e := lagrangian_eq w ω hX₁ hX₂ hΔ h μ₁ μ₂ ν
  have hb := hermitian_le_boxQuadMax (a := lagrangeCoeff₁ w ω μ₁ μ₂)
    (b := lagrangeCoeff₂ w ω μ₁ μ₂) (c := lagrangeCross w ω μ₁ μ₂ ν) h₁ h₂
  unfold dualBound
  nlinarith [mul_le_mul_of_nonneg_left hψ₁ hμ₁, mul_le_mul_of_nonneg_left hψ₂ hμ₂,
    mul_le_mul_of_nonneg_left hQ hν]

/-- The dual function is convex in the multipliers `(μ₁, μ₂, ν)` (`ρ₁, ρ₂ ≥ 0`). -/
@[tmio M, powerlib_domain] theorem convexOn_dualBound {ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin : ℝ} (hρ₁ : 0 ≤ ρ₁)
    (hρ₂ : 0 ≤ ρ₂) :
    ConvexOn ℝ Set.univ fun m : ℝ × ℝ × ℝ => dualBound w ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin m.1 m.2.1 m.2.2 := by
  refine ⟨convex_univ, fun m _ m' _ a b ha hb hab => ?_⟩
  set m'' := a • m + b • m'
  obtain ⟨z₁, z₂, h₁, h₂, he⟩ := exists_hermitian_eq_boxQuadMax
    (a := lagrangeCoeff₁ w ω m''.1 m''.2.1) (b := lagrangeCoeff₂ w ω m''.1 m''.2.1)
    (lagrangeCross w ω m''.1 m''.2.1 m''.2.2) hρ₁ hρ₂
  have hm := hermitian_le_boxQuadMax (a := lagrangeCoeff₁ w ω m.1 m.2.1)
    (b := lagrangeCoeff₂ w ω m.1 m.2.1) (c := lagrangeCross w ω m.1 m.2.1 m.2.2) h₁ h₂
  have hm' := hermitian_le_boxQuadMax (a := lagrangeCoeff₁ w ω m'.1 m'.2.1)
    (b := lagrangeCoeff₂ w ω m'.1 m'.2.1) (c := lagrangeCross w ω m'.1 m'.2.1 m'.2.2) h₁ h₂
  simp only [dualBound, smul_eq_mul]
  rw [← he]
  obtain rfl : b = 1 - a := by linarith
  have e : m''.1 * Ψ₁ ^ 2 + m''.2.1 * Ψ₂ ^ 2 - m''.2.2 * Qmin +
      (lagrangeCoeff₁ w ω m''.1 m''.2.1 * ‖z₁‖ ^ 2 + lagrangeCoeff₂ w ω m''.1 m''.2.1 * ‖z₂‖ ^ 2 +
        2 * (lagrangeCross w ω m''.1 m''.2.1 m''.2.2 * z₁ * conj z₂).re) =
      a * (m.1 * Ψ₁ ^ 2 + m.2.1 * Ψ₂ ^ 2 - m.2.2 * Qmin +
        (lagrangeCoeff₁ w ω m.1 m.2.1 * ‖z₁‖ ^ 2 + lagrangeCoeff₂ w ω m.1 m.2.1 * ‖z₂‖ ^ 2 +
          2 * (lagrangeCross w ω m.1 m.2.1 m.2.2 * z₁ * conj z₂).re)) +
      (1 - a) * (m'.1 * Ψ₁ ^ 2 + m'.2.1 * Ψ₂ ^ 2 - m'.2.2 * Qmin +
        (lagrangeCoeff₁ w ω m'.1 m'.2.1 * ‖z₁‖ ^ 2 + lagrangeCoeff₂ w ω m'.1 m'.2.1 * ‖z₂‖ ^ 2 +
          2 * (lagrangeCross w ω m'.1 m'.2.1 m'.2.2 * z₁ * conj z₂).re)) := by
    simp only [m'', lagrangeCoeff₁, lagrangeCoeff₂, lagrangeCross, Complex.mul_re,
      Complex.mul_im, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hm ha, mul_le_mul_of_nonneg_left hm' hb]

/-- With all multipliers zero the dual function is the bridge-only limit of
`theorem/WPT/LossyLimits.lean`: `dualBound 0 0 0 = LossyLimits.outputLimit` (`R₁ > 0`, `Δ > 0`,
`ωM ≠ 0`, `ρ₁, ρ₂ ≥ 0`). -/
@[tmio M, powerlib_domain] theorem dualBound_zero {ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hR₁ : 0 < w.primary.R) (hΔ : 0 < determinant w ω) (hm : ω * w.M ≠ 0)
    (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    dualBound w ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin 0 0 0 = outputLimit w ω ρ₁ ρ₂ := by
  have h1 := isGreatest_hermitian_boxQuadMax (a := lagrangeCoeff₁ w ω 0 0)
    (b := lagrangeCoeff₂ w ω 0 0) (lagrangeCross w ω 0 0 0) hρ₁ hρ₂
  have hset : {q | ∃ z₁ z₂ : ℂ, ‖z₁‖ ≤ ρ₁ ∧ ‖z₂‖ ≤ ρ₂ ∧
      q = lagrangeCoeff₁ w ω 0 0 * ‖z₁‖ ^ 2 + lagrangeCoeff₂ w ω 0 0 * ‖z₂‖ ^ 2 +
        2 * (lagrangeCross w ω 0 0 0 * z₁ * conj z₂).re} =
      {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
        P = -(V₂ * conj I₂).re} := by
    ext q
    constructor
    · rintro ⟨z₁, z₂, h₁, h₂, rfl⟩
      have hd := driven_currents w ω z₁ z₂ hX₁ hX₂ hΔ.ne'
      refine ⟨z₁, z₂, _, _, h₁, h₂, hd, ?_⟩
      have := lagrangian_eq w ω hX₁ hX₂ hΔ.ne' hd 0 0 0
      simp only [zero_mul, sub_zero, add_zero] at this
      exact this.symm
    · rintro ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, rfl⟩
      refine ⟨V₁, V₂, h₁, h₂, ?_⟩
      have := lagrangian_eq w ω hX₁ hX₂ hΔ.ne' h 0 0 0
      simp only [zero_mul, sub_zero, add_zero] at this
      exact this
  rw [hset] at h1
  simp only [dualBound, zero_mul, add_zero, sub_zero, zero_add]
  exact h1.unique (isGreatest_outputPower w ω hX₁ hX₂ hR₁ hΔ hm hρ₁ hρ₂)

/-! ## The exact limit -/

/-- The largest output power under both bridges, both flux bounds and the margin is attained
once one admissible operating point exists (the admissible bridge phasors form a compact set). -/
@[tmio M, powerlib_domain] theorem exists_isGreatest_outputPower {ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0)
    (hne : ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
      normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧ normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧
        Qmin ≤ (V₁ * conj I₁).im) :
    ∃ P, IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧
      Driven w ω V₁ V₂ I₁ I₂ ∧ normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧
        normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧ Qmin ≤ (V₁ * conj I₁).im ∧
          P = -(V₂ * conj I₂).re} P := by
  set c₁ : ℂ × ℂ → ℂ := fun v =>
    (w.secondary.R * v.1 - ((ω * w.M : ℝ) : ℂ) * I * v.2) / (determinant w ω : ℂ)
  set c₂ : ℂ × ℂ → ℂ := fun v =>
    (w.primary.R * v.2 - ((ω * w.M : ℝ) : ℂ) * I * v.1) / (determinant w ω : ℂ)
  have hc₁ : Continuous c₁ := by fun_prop
  have hc₂ : Continuous c₂ := by fun_prop
  set S : Set (ℂ × ℂ) := {v | ‖v.1‖ ≤ ρ₁} ∩ ({v | ‖v.2‖ ≤ ρ₂} ∩
    ({v | normSq (w.flux₁ (c₁ v) (c₂ v)) ≤ Ψ₁ ^ 2} ∩
      ({v | normSq (w.flux₂ (c₁ v) (c₂ v)) ≤ Ψ₂ ^ 2} ∩ {v | Qmin ≤ (v.1 * conj (c₁ v)).im})))
  have hS : IsCompact S := by
    refine ((isCompact_closedBall (0 : ℂ) ρ₁).prod
      (isCompact_closedBall (0 : ℂ) ρ₂)).of_isClosed_subset ?_ ?_
    · refine (isClosed_le (by fun_prop) continuous_const).inter
        ((isClosed_le (by fun_prop) continuous_const).inter
          ((isClosed_le ?_ continuous_const).inter
            ((isClosed_le ?_ continuous_const).inter (isClosed_le continuous_const ?_))))
      · exact Complex.continuous_normSq.comp (by unfold Passive.Coupled.flux₁; fun_prop)
      · exact Complex.continuous_normSq.comp (by unfold Passive.Coupled.flux₂; fun_prop)
      · fun_prop
    · rintro v ⟨h1, h2, -⟩
      exact ⟨mem_closedBall_zero_iff.mpr h1, mem_closedBall_zero_iff.mpr h2⟩
  have hSne : S.Nonempty := by
    obtain ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ₁, hψ₂, hQ⟩ := hne
    obtain ⟨e1, e2⟩ := currents_eq w ω hX₁ hX₂ hΔ h
    subst e1 e2
    exact ⟨(V₁, V₂), h₁, h₂, hψ₁, hψ₂, hQ⟩
  obtain ⟨v, hv, hmax⟩ := hS.exists_isMaxOn hSne
    (f := fun v => -(v.2 * conj (c₂ v)).re) (by fun_prop)
  refine ⟨-(v.2 * conj (c₂ v)).re, ⟨v.1, v.2, c₁ v, c₂ v, hv.1, hv.2.1,
    driven_currents w ω v.1 v.2 hX₁ hX₂ hΔ, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2, rfl⟩, ?_⟩
  rintro P ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ₁, hψ₂, hQ, rfl⟩
  obtain ⟨e1, e2⟩ := currents_eq w ω hX₁ hX₂ hΔ h
  subst e1 e2
  exact hmax (show (V₁, V₂) ∈ S from ⟨h₁, h₂, hψ₁, hψ₂, hQ⟩)

/-- The flux forms are nondecreasing in `U`. -/
@[tmio M, powerlib_domain] private theorem fluxForm_mono {U U' W : ℝ} {z : ℂ} (hU : U' ≤ U) :
    fluxForm₁ w ω U' W z ≤ fluxForm₁ w ω U W z ∧ fluxForm₂ w ω U' W z ≤ fluxForm₂ w ω U W z := by
  constructor <;>
  · apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hU (add_nonneg (sq_nonneg (w.primary.L * w.secondary.R))
        (sq_nonneg (w.M * (ω * w.M)))),
      mul_le_mul_of_nonneg_left hU (add_nonneg (sq_nonneg (w.M * w.secondary.R))
        (sq_nonneg (w.secondary.L * (ω * w.M))))]

/-- **Strong duality, certificate**: under Slater's condition, if `P` bounds the output power of
every admissible operating point, some multipliers `μ₁, μ₂, ν ≥ 0` have `dualBound ≤ P`. -/
@[tmio M, powerlib_domain] private theorem exists_dualBound_le {ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin P : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0)
    (hP : ∀ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ → ‖V₂‖ ≤ ρ₂ → Driven w ω V₁ V₂ I₁ I₂ →
      normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 → normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 →
        Qmin ≤ (V₁ * conj I₁).im → -(V₂ * conj I₂).re ≤ P)
    (hS : ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
      normSq (w.flux₁ I₁ I₂) < Ψ₁ ^ 2 ∧ normSq (w.flux₂ I₁ I₂) < Ψ₂ ^ 2 ∧
        Qmin < (V₁ * conj I₁).im) :
    ∃ μ₁ μ₂ ν : ℝ, 0 ≤ μ₁ ∧ 0 ≤ μ₂ ∧ 0 ≤ ν ∧ dualBound w ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin μ₁ μ₂ ν ≤ P := by
  obtain ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ₁, hψ₂, hQ⟩ := hS
  have hρ₁ : 0 ≤ ρ₁ := (norm_nonneg _).trans h₁
  have hρ₂ : 0 ≤ ρ₂ := (norm_nonneg _).trans h₂
  -- the lifted program on `bidiskLift ρ₁ ρ₂ ⊆ ℝ × ℝ × ℂ`
  set F : ℝ × ℝ × ℂ → ℝ := fun x =>
    (-(ω * w.M) * x.2.2.im - w.primary.R * x.2.1) / determinant w ω
  set G : Fin 3 → ℝ × ℝ × ℂ → ℝ := ![fun x => fluxForm₁ w ω x.1 x.2.1 x.2.2 - Ψ₁ ^ 2,
    fun x => fluxForm₂ w ω x.1 x.2.1 x.2.2 - Ψ₂ ^ 2,
    fun x => Qmin - ω * w.M * x.2.2.re / determinant w ω]
  have hF : ConcaveOn ℝ (bidiskLift ρ₁ ρ₂) F := by
    refine ⟨convex_bidiskLift ρ₁ ρ₂, fun x _ y _ a b _ _ hab => le_of_eq ?_⟩
    obtain rfl : b = 1 - a := by linarith
    simp only [F, smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Complex.add_im, Complex.smul_im]
    ring
  have hG : ∀ j, ConvexOn ℝ (bidiskLift ρ₁ ρ₂) (G j) := by
    intro j
    refine ⟨convex_bidiskLift ρ₁ ρ₂, fun x _ y _ a b _ _ hab => le_of_eq ?_⟩
    obtain rfl : b = 1 - a := by linarith
    fin_cases j <;>
      simp only [G, fluxForm₁, fluxForm₂, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im] <;>
      ring
  have hx₀ := lift_mem_bidiskLift h₁ h₂
  have hs : ∀ j, G j (‖V₁‖ ^ 2, ‖V₂‖ ^ 2, V₁ * conj V₂) < 0 := by
    intro j
    fin_cases j
    · simpa [G, ← normSq_flux₁_eq hX₁ hX₂ hΔ h] using hψ₁
    · simpa [G, ← normSq_flux₂_eq hX₁ hX₂ hΔ h] using hψ₂
    · show Qmin - ω * w.M * (V₁ * conj V₂).re / determinant w ω < 0
      rw [← reactive₁_eq hX₁ hX₂ hΔ h]
      linarith
  -- a lifted feasible point is realized by an admissible operating point with the same output
  have hp : ∀ x ∈ bidiskLift ρ₁ ρ₂, (∀ j, G j x ≤ 0) → F x ≤ P := by
    intro x hx hGx
    obtain ⟨Z₁, Z₂, k₁, k₂, hU, hW, hz⟩ := exists_lift_of_mem_bidiskLift hρ₁ hρ₂ hx
    have hdz := driven_currents w ω Z₁ Z₂ hX₁ hX₂ hΔ
    have g1 := hGx 0
    have g2 := hGx 1
    have g3 := hGx 2
    simp only [G, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, sub_nonpos] at g1 g2 g3
    have hm := fluxForm_mono w ω (W := x.2.1) (z := x.2.2) hU
    have := hP _ _ _ _ k₁ k₂ hdz
      (by rw [normSq_flux₁_eq hX₁ hX₂ hΔ hdz, hW, hz]; exact hm.1.trans g1)
      (by rw [normSq_flux₂_eq hX₁ hX₂ hΔ hdz, hW, hz]; exact hm.2.trans g2)
      (by rw [reactive₁_eq hX₁ hX₂ hΔ hdz, hz]; exact g3)
    rwa [outputPower_eq_lift hX₁ hX₂ hΔ hdz, hW, hz] at this
  obtain ⟨μ, hμ, hL⟩ := exists_lagrangian_le hF hG hx₀ hs hp
  obtain ⟨z₁, z₂, k₁, k₂, he⟩ := exists_hermitian_eq_boxQuadMax
    (a := lagrangeCoeff₁ w ω (μ 0) (μ 1)) (b := lagrangeCoeff₂ w ω (μ 0) (μ 1))
    (lagrangeCross w ω (μ 0) (μ 1) (μ 2)) hρ₁ hρ₂
  refine ⟨μ 0, μ 1, μ 2, hμ 0, hμ 1, hμ 2, ?_⟩
  have hl := hL _ (lift_mem_bidiskLift k₁ k₂)
  rw [Fin.sum_univ_three] at hl
  simp only [F, G, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hl
  have key := lift_lagrangian w ω hΔ (μ 0) (μ 1) (μ 2) (‖z₁‖ ^ 2) (‖z₂‖ ^ 2) (z₁ * conj z₂)
  rw [← mul_assoc] at key
  unfold dualBound
  rw [← he]
  linarith

/-- Strong duality: the greatest output power is the least dual value (private combined form). -/
@[tmio M, powerlib_domain] private theorem isGreatest_isLeast {ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0)
    (hS : ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
      normSq (w.flux₁ I₁ I₂) < Ψ₁ ^ 2 ∧ normSq (w.flux₂ I₁ I₂) < Ψ₂ ^ 2 ∧
        Qmin < (V₁ * conj I₁).im) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧
      Driven w ω V₁ V₂ I₁ I₂ ∧ normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧
        normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧ Qmin ≤ (V₁ * conj I₁).im ∧
          P = -(V₂ * conj I₂).re} (outputEnvelope w ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin) ∧
    IsLeast {d | ∃ μ₁ μ₂ ν : ℝ, 0 ≤ μ₁ ∧ 0 ≤ μ₂ ∧ 0 ≤ ν ∧
      d = dualBound w ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin μ₁ μ₂ ν} (outputEnvelope w ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin) := by
  obtain ⟨P, hP⟩ := exists_isGreatest_outputPower w ω hX₁ hX₂ hΔ (by
    obtain ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ₁, hψ₂, hQ⟩ := hS
    exact ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ₁.le, hψ₂.le, hQ.le⟩)
  obtain ⟨⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ₁, hψ₂, hQ, rfl⟩, hub⟩ := hP
  have lower : ∀ μ₁ μ₂ ν : ℝ, 0 ≤ μ₁ → 0 ≤ μ₂ → 0 ≤ ν →
      -(V₂ * conj I₂).re ≤ dualBound w ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin μ₁ μ₂ ν := fun μ₁ μ₂ ν hμ₁ hμ₂ hν =>
    outputPower_le_dualBound w ω hX₁ hX₂ hΔ h h₁ h₂ hψ₁ hψ₂ hQ hμ₁ hμ₂ hν
  have hL : IsLeast {d | ∃ μ₁ μ₂ ν : ℝ, 0 ≤ μ₁ ∧ 0 ≤ μ₂ ∧ 0 ≤ ν ∧
      d = dualBound w ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin μ₁ μ₂ ν} (-(V₂ * conj I₂).re) := by
    refine ⟨?_, ?_⟩
    · obtain ⟨μ₁, μ₂, ν, hμ₁, hμ₂, hν, hle⟩ := exists_dualBound_le w ω hX₁ hX₂ hΔ
        (fun V₁ V₂ I₁ I₂ h₁ h₂ h hψ₁ hψ₂ hQ => hub ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ₁, hψ₂, hQ, rfl⟩)
        hS
      exact ⟨μ₁, μ₂, ν, hμ₁, hμ₂, hν, le_antisymm (lower μ₁ μ₂ ν hμ₁ hμ₂ hν) hle⟩
    · rintro d ⟨μ₁, μ₂, ν, hμ₁, hμ₂, hν, rfl⟩
      exact lower μ₁ μ₂ ν hμ₁ hμ₂ hν
  rw [outputEnvelope, hL.csInf_eq]
  exact ⟨⟨⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ₁, hψ₂, hQ, rfl⟩, hub⟩, hL⟩

/-- **The exact limit (primal side)**: under Slater's condition (an operating point within both
bridges with both flux bounds and the margin strict), `outputEnvelope` is the greatest output
power `−Re(V₂ Ī₂)` over the operating points with `‖V_k‖ ≤ ρ_k`, `‖ψ_k‖² ≤ Ψ_k²` and
`Im(V₁ Ī₁) ≥ Q_min`. -/
@[tmio M, powerlib_domain] theorem isGreatest_outputEnvelope {ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0)
    (hS : ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
      normSq (w.flux₁ I₁ I₂) < Ψ₁ ^ 2 ∧ normSq (w.flux₂ I₁ I₂) < Ψ₂ ^ 2 ∧
        Qmin < (V₁ * conj I₁).im) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧
      Driven w ω V₁ V₂ I₁ I₂ ∧ normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧
        normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧ Qmin ≤ (V₁ * conj I₁).im ∧
          P = -(V₂ * conj I₂).re} (outputEnvelope w ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin) :=
  (isGreatest_isLeast w ω hX₁ hX₂ hΔ hS).1

/-- **Strong duality (dual side)**: under Slater's condition, `outputEnvelope` is the least value
of `dualBound μ₁ μ₂ ν` over `μ₁, μ₂, ν ≥ 0`, attained by some multipliers. -/
@[tmio M, powerlib_domain] theorem isLeast_outputEnvelope {ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0)
    (hS : ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧ Driven w ω V₁ V₂ I₁ I₂ ∧
      normSq (w.flux₁ I₁ I₂) < Ψ₁ ^ 2 ∧ normSq (w.flux₂ I₁ I₂) < Ψ₂ ^ 2 ∧
        Qmin < (V₁ * conj I₁).im) :
    IsLeast {d | ∃ μ₁ μ₂ ν : ℝ, 0 ≤ μ₁ ∧ 0 ≤ μ₂ ∧ 0 ≤ ν ∧
      d = dualBound w ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin μ₁ μ₂ ν} (outputEnvelope w ω ρ₁ ρ₂ Ψ₁ Ψ₂ Qmin) :=
  (isGreatest_isLeast w ω hX₁ hX₂ hΔ hS).2

/-! ## Without the margin -/

/-- Within the bridges the reactive power exceeds `−|ωM|ρ₁ρ₂/|Δ| − 1`. -/
@[tmio M, powerlib_domain] private theorem reactive_gt {V₁ V₂ I₁ I₂ : ℂ} {ρ₁ ρ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0) (h : Driven w ω V₁ V₂ I₁ I₂) (h₁ : ‖V₁‖ ≤ ρ₁)
    (h₂ : ‖V₂‖ ≤ ρ₂) :
    -(|ω * w.M| * (ρ₁ * ρ₂) / |determinant w ω|) - 1 < (V₁ * conj I₁).im := by
  rw [reactive₁_eq hX₁ hX₂ hΔ h]
  have hρ₁ : 0 ≤ ρ₁ := (norm_nonneg _).trans h₁
  have hb : |ω * w.M * (V₁ * conj V₂).re / determinant w ω| ≤
      |ω * w.M| * (ρ₁ * ρ₂) / |determinant w ω| := by
    rw [abs_div, abs_mul]
    gcongr
    calc |(V₁ * conj V₂).re| ≤ ‖V₁ * conj V₂‖ := Complex.abs_re_le_norm _
      _ = ‖V₁‖ * ‖V₂‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ ρ₁ * ρ₂ := mul_le_mul h₁ h₂ (norm_nonneg _) hρ₁
  linarith [neg_abs_le (ω * w.M * (V₁ * conj V₂).re / determinant w ω)]

/-- Without the margin (private combined form). -/
@[tmio M, powerlib_domain] private theorem isGreatest_isLeast_flux {ρ₁ ρ₂ Ψ₁ Ψ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (hΨ₁ : Ψ₁ ≠ 0) (hΨ₂ : Ψ₂ ≠ 0) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧
      Driven w ω V₁ V₂ I₁ I₂ ∧ normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧
        normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧ P = -(V₂ * conj I₂).re}
      (fluxEnvelope w ω ρ₁ ρ₂ Ψ₁ Ψ₂) ∧
    IsLeast {d | ∃ μ₁ μ₂ : ℝ, 0 ≤ μ₁ ∧ 0 ≤ μ₂ ∧ d = dualBound w ω ρ₁ ρ₂ Ψ₁ Ψ₂ 0 μ₁ μ₂ 0}
      (fluxEnvelope w ω ρ₁ ρ₂ Ψ₁ Ψ₂) := by
  -- a margin below every reactive power the bridges allow
  set Q₀ := -(|ω * w.M| * (ρ₁ * ρ₂) / |determinant w ω|) - 1
  have hQ₀ : Q₀ < 0 := by
    have : 0 ≤ |ω * w.M| * (ρ₁ * ρ₂) / |determinant w ω| := by positivity
    linarith
  have hd0 : Driven w ω 0 0 0 0 := (driven_iff w ω 0 0 0 0).mpr ⟨by simp, by simp⟩
  obtain ⟨hG, hL⟩ := isGreatest_isLeast w ω (ρ₁ := ρ₁) (ρ₂ := ρ₂) (Ψ₁ := Ψ₁) (Ψ₂ := Ψ₂)
    (Qmin := Q₀) hX₁ hX₂ hΔ ⟨0, 0, 0, 0, by simpa using hρ₁, by simpa using hρ₂, hd0,
      by simpa [Passive.Coupled.flux₁] using sq_pos_of_ne_zero hΨ₁,
      by simpa [Passive.Coupled.flux₂] using sq_pos_of_ne_zero hΨ₂, by simpa using hQ₀⟩
  set E := outputEnvelope w ω ρ₁ ρ₂ Ψ₁ Ψ₂ Q₀
  have hset : {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧
      Driven w ω V₁ V₂ I₁ I₂ ∧ normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧
        normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧ P = -(V₂ * conj I₂).re} =
      {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧
      Driven w ω V₁ V₂ I₁ I₂ ∧ normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧
        normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧ Q₀ ≤ (V₁ * conj I₁).im ∧
          P = -(V₂ * conj I₂).re} := by
    ext P
    constructor
    · rintro ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ₁, hψ₂, rfl⟩
      exact ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ₁, hψ₂,
        (reactive_gt w ω hX₁ hX₂ hΔ h h₁ h₂).le, rfl⟩
    · rintro ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ₁, hψ₂, -, rfl⟩
      exact ⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ₁, hψ₂, rfl⟩
  rw [← hset] at hG
  -- at `ν = 0` the dual function does not depend on the margin
  have hν0 : ∀ q μ₁ μ₂ : ℝ, dualBound w ω ρ₁ ρ₂ Ψ₁ Ψ₂ q μ₁ μ₂ 0 =
      dualBound w ω ρ₁ ρ₂ Ψ₁ Ψ₂ 0 μ₁ μ₂ 0 := fun q μ₁ μ₂ => by simp [dualBound]
  have hLf : IsLeast {d | ∃ μ₁ μ₂ : ℝ, 0 ≤ μ₁ ∧ 0 ≤ μ₂ ∧
      d = dualBound w ω ρ₁ ρ₂ Ψ₁ Ψ₂ 0 μ₁ μ₂ 0} E := by
    obtain ⟨⟨V₁, V₂, I₁, I₂, h₁, h₂, h, hψ₁, hψ₂, hPE⟩, -⟩ := hG
    refine ⟨?_, ?_⟩
    · obtain ⟨μ₁, μ₂, ν, hμ₁, hμ₂, hν, hE⟩ := hL.1
      refine ⟨μ₁, μ₂, hμ₁, hμ₂, le_antisymm ?_ ?_⟩
      · rw [hPE, ← hν0 ((V₁ * conj I₁).im)]
        exact outputPower_le_dualBound w ω hX₁ hX₂ hΔ h h₁ h₂ hψ₁ hψ₂ le_rfl hμ₁ hμ₂ le_rfl
      · -- `dualBound μ₁ μ₂ 0 ≤ dualBound μ₁ μ₂ ν` at the margin `Q₀`
        rw [hE]
        obtain ⟨z₁, z₂, k₁, k₂, he⟩ := exists_hermitian_eq_boxQuadMax
          (a := lagrangeCoeff₁ w ω μ₁ μ₂) (b := lagrangeCoeff₂ w ω μ₁ μ₂)
          (lagrangeCross w ω μ₁ μ₂ 0) hρ₁ hρ₂
        have hdz := driven_currents w ω z₁ z₂ hX₁ hX₂ hΔ
        have e0 := lagrangian_eq w ω hX₁ hX₂ hΔ hdz μ₁ μ₂ 0
        have eν := lagrangian_eq w ω hX₁ hX₂ hΔ hdz μ₁ μ₂ ν
        have hb := hermitian_le_boxQuadMax (a := lagrangeCoeff₁ w ω μ₁ μ₂)
          (b := lagrangeCoeff₂ w ω μ₁ μ₂) (c := lagrangeCross w ω μ₁ μ₂ ν) k₁ k₂
        have hq := reactive_gt w ω hX₁ hX₂ hΔ hdz k₁ k₂
        unfold dualBound
        rw [← he]
        nlinarith [mul_le_mul_of_nonneg_left hq.le hν]
    · rintro d ⟨μ₁, μ₂, hμ₁, hμ₂, rfl⟩
      rw [hPE, ← hν0 ((V₁ * conj I₁).im)]
      exact outputPower_le_dualBound w ω hX₁ hX₂ hΔ h h₁ h₂ hψ₁ hψ₂ le_rfl hμ₁ hμ₂ le_rfl
  rw [fluxEnvelope, hLf.csInf_eq]
  exact ⟨hG, hLf⟩

/-- **The exact limit without the margin (primal side)**: for `Ψ₁, Ψ₂ ≠ 0` and `ρ₁, ρ₂ ≥ 0`,
`fluxEnvelope` is the greatest output power `−Re(V₂ Ī₂)` over the operating points with
`‖V_k‖ ≤ ρ_k` and `‖ψ_k‖² ≤ Ψ_k²`. -/
@[tmio M, powerlib_domain] theorem isGreatest_fluxEnvelope {ρ₁ ρ₂ Ψ₁ Ψ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (hΨ₁ : Ψ₁ ≠ 0) (hΨ₂ : Ψ₂ ≠ 0) :
    IsGreatest {P : ℝ | ∃ V₁ V₂ I₁ I₂ : ℂ, ‖V₁‖ ≤ ρ₁ ∧ ‖V₂‖ ≤ ρ₂ ∧
      Driven w ω V₁ V₂ I₁ I₂ ∧ normSq (w.flux₁ I₁ I₂) ≤ Ψ₁ ^ 2 ∧
        normSq (w.flux₂ I₁ I₂) ≤ Ψ₂ ^ 2 ∧ P = -(V₂ * conj I₂).re}
      (fluxEnvelope w ω ρ₁ ρ₂ Ψ₁ Ψ₂) :=
  (isGreatest_isLeast_flux w ω hX₁ hX₂ hΔ hρ₁ hρ₂ hΨ₁ hΨ₂).1

/-- **Strong duality without the margin (dual side)**: for `Ψ₁, Ψ₂ ≠ 0` and `ρ₁, ρ₂ ≥ 0`,
`fluxEnvelope` is the least value of `dualBound μ₁ μ₂ 0` over `μ₁, μ₂ ≥ 0`, attained. -/
@[tmio M, powerlib_domain] theorem isLeast_fluxEnvelope {ρ₁ ρ₂ Ψ₁ Ψ₂ : ℝ}
    (hX₁ : w.primary.reactance ω = 0) (hX₂ : w.secondary.reactance ω = 0)
    (hΔ : determinant w ω ≠ 0) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (hΨ₁ : Ψ₁ ≠ 0) (hΨ₂ : Ψ₂ ≠ 0) :
    IsLeast {d | ∃ μ₁ μ₂ : ℝ, 0 ≤ μ₁ ∧ 0 ≤ μ₂ ∧ d = dualBound w ω ρ₁ ρ₂ Ψ₁ Ψ₂ 0 μ₁ μ₂ 0}
      (fluxEnvelope w ω ρ₁ ρ₂ Ψ₁ Ψ₂) :=
  (isGreatest_isLeast_flux w ω hX₁ hX₂ hΔ hρ₁ hρ₂ hΨ₁ hΨ₂).2

end powerlib.WPT.LossyEnvelope
