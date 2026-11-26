import theorem.ParametricResonance.Meissner
import theorem.Averaging.SwitchedStability

/-! # Parametric stabilization: a small-signal instability that the periodic system does not have

The damped oscillator `ẍ + 2c ẋ + k(t) x = 0` with a two-level stiffness, `k = k₁` on the first
and `k = k₂` on the second half of every period `T`, has a closed-form monodromy matrix also when
one half period is hyperbolic. With `x = e^{−ct} y` an oscillatory half (`ν² = k₁ − c² > 0`) is
the rotation `R(ν, θ)`, `θ = νT/2`, and a hyperbolic half (`κ² = c² − k₂ > 0`) is the hyperbolic
rotation `H(κ, η) = [[cosh η, sinh η/κ], [κ sinh η, cosh η]]`, `η = κT/2`, so
`M = e^{−cT} S (H R) S⁻¹`, `det M = e^{−2cT}` and
`tr M = e^{−cT} τ`, `τ = 2 cos θ cosh η + (κ/ν − ν/κ) sin θ sinh η`. The exact Floquet boundary
is `|τ| = 2 cosh(cT)` (`theorem/Periodic/TwoStateBoundary.lean`).

When the mean stiffness `(k₁ + k₂)/2` is negative, small-signal analysis — the frozen matrix of
the soft half period and the averaged (state-space averaged, first-order averaging) matrix
`[[0, 1], [−(k₁ + k₂)/2, −2c]]` — finds a saddle: a real eigenvalue `r > 0`, an exponentially
growing mode, verdict "unstable". The periodic system can nevertheless be stable. At a half turn
`θ = π/2` (`T = π/ν`) the reduced trace is `τ = (r − 1/r) sinh(rπ/2)`, `r = κ/ν`; it vanishes at
`r = 1` and increases strictly, so on the explicit window `1 < r < r₀`,
`(r₀ − 1/r₀) sinh(r₀π/2) = 2`, the undamped multipliers are non-real on the unit circle and any
small damping moves them strictly inside, although the soft half is the stronger one and the
mean stiffness `(ν² − κ²)/2` is negative: the small-signal verdict is a false alarm (parametric
stabilization, the mechanism of Kapitza's inverted pendulum). The effect lies outside first-order
averaging: for fixed stiffness levels with negative mean, no fast switching is uniformly stable
(`not_uniform_fast_decay`); classically (not formalized here) the stabilizing correction is of
second order in the modulation and appears at a finite period. The opposite case does not exist for the damping: a negative damping `c < 0` is
unstable at every level, for every stiffness modulation and every period, because
`det M = e^{−2cT} > 1` (`negative_damping_unstable`).

Scope.
* The scalar equation in the state `(x, ẋ) ∈ ℝ²` with state matrices `B_i = oscMatrix c k_i`
  (`Periodic.oscMatrix`), constant damping `c`, period `T > 0`, continuous time. The coefficient
  jumps, so a solution is a trajectory of the two-topology switched system with duty ratio `1/2`
  in the form of `theorem/Averaging/StateSpaceAveraging.lean`, written out in each statement:
  `∀ k : ℕ, IsIntegralCurveOn x (fun _ y => B₁ *ᵥ y) (Icc (k * T) (k * T + 1 / 2 * T)) ∧
  IsIntegralCurveOn x (fun _ y => B₂ *ᵥ y) (Icc (k * T + 1 / 2 * T) ((k + 1) * T))`
  (one-sided derivatives at the switching instants; such trajectories exist for every initial
  state, `Averaging.exists_switched_trajectory`, and satisfy `x(kT) = Mᵏ x(0)`,
  `Averaging.switched_sample`). The Meissner equation of
  `theorem/ParametricResonance/Meissner.lean` is the case `k_{1,2} = ω₀²(1 ± ε)` with both halves
  oscillatory; here one half is hyperbolic and the mean stiffness may be negative, which the
  Meissner parametrization (`ω₀² ≥ 0`) cannot express.
* Small-signal (level L3) verdicts are LeanForControl's `LinearSystems.IsHurwitz` of the averaged
  matrix `Averaging.avgMatrix (1/2) B₁ B₂` and of the frozen matrices; Floquet (level L1)
  verdicts are `LTI.SchurStable` of the monodromy matrix and multipliers outside the unit circle.
  Norms: sup norm on `ℝ²`, `L∞` operator norm on matrices.
* Generic mathematics; no model family.

Source: P. L. Kapitza, "Dynamic stability of a pendulum with an oscillating point of suspension"
(1951); V. I. Arnold, *Mathematical Methods of Classical Mechanics*, §25 (the inverted pendulum
with a vibrating suspension, piecewise-constant acceleration: the period map is the product of a
hyperbolic and an elliptic rotation, stable iff `|tr| < 2`); the reduction `x = e^{−ct} y` and the
rotation `R` of `theorem/ParametricResonance/Meissner.lean`; the two-state boundary of
`theorem/Periodic/TwoStateBoundary.lean`; the switched-system and averaging results of
`theorem/Averaging/StateSpaceAveraging.lean` and `theorem/Averaging/SwitchedStability.lean`.

Results.
* `exp_smul_of_sq_eq_sq` — `B = A + aI`, `B² = w² I`, `w ≠ 0`:
  `e^{tA} = e^{−at}(cosh(wt) I + (sinh(wt)/w) B)` (the hyperbolic counterpart of
  `LTI.exp_smul_of_sq_eq`); `hyp`, `exp_oscMatrix_hyp` — `e^{hA} = e^{−ch} S H(κ, κh) S⁻¹` for
  `A = oscMatrix c k`, `κ² = c² − k`.
* `kapitzaMonodromy`, `kapitzaMonodromy_eq_exp` — `M = e^{(T/2)B₂} e^{(T/2)B₁}`, the period map
  `Averaging.periodMap (1/2) T B₁ B₂`; `kapitzaMonodromy_eq`, `trace_hyp_mul_rot` —
  `M = e^{−cT} S (H(κ, η) R(ν, θ)) S⁻¹` and `tr(H R) = kapitzaTrace ν κ T`;
  `det_kapitzaMonodromy` — `det M = e^{−2cT}` for all stiffness levels;
  `trace_kapitzaMonodromy` — `tr M = e^{−cT} τ`.
* `floquetUnstable_iff` — `c ≥ 0`: a multiplier outside the unit circle iff `2 cosh(cT) < |τ|`;
  `schurStable_iff` — `c > 0`: Schur stability iff `|τ| < 2 cosh(cT)`;
  `undamped_norm_eq_one` — `c = 0`, `|τ| < 2`: every multiplier is non-real with `|μ| = 1`.
* `kapitzaTrace_half_turn` — `T = π/ν`: `τ = (κ/ν − ν/κ) sinh(κπ/(2ν))`; `exists_window` — there is
  `r₀ ∈ (1, 2)` with `(r₀ − 1/r₀) sinh(r₀π/2) = 2` such that for `0 < ν ≤ κ`: `|τ| < 2` iff
  `κ < r₀ν` (intermediate values and strict monotonicity; no numerical value is used).
* `avgMatrix_oscMatrix` — the averaged matrix is `oscMatrix c ((k₁ + k₂)/2)`;
  `oscMatrix_saddle` — `k < 0`: a real eigenvalue `r > 0` with eigenvector `(1, r)`, not Hurwitz.
* `switched_decay_of_schurStable` — any dimension, any duty ratio, fixed period: a Schur-stable
  period map makes every switched trajectory decay, `‖x(t)‖ ≤ C e^{−αt} ‖x(0)‖`.
* `small_signal_false_alarm` — `c > 0`, `k₁ = ν² + c²`, `k₂ = c² − κ²`, `ν² + 2c² < κ²`,
  `|τ| < 2`: negative mean stiffness, averaged and soft frozen matrices saddles (not Hurwitz), yet
  Schur-stable monodromy and exponential decay of every trajectory.
* `damped_schurStable_of_undamped` — fixed levels `k₁ > 0 > k₂` with undamped `|τ| < 2`: Schur
  stable for every damping `c ∈ (0, c₀)`.
* `parametric_stabilization` — for `ν < κ < r₀ν`, levels `ν²`, `−κ²`, `T = π/ν`: negative mean
  stiffness, averaged matrix a saddle for every `c`, undamped multipliers on the unit circle, and
  Schur stability for small damping.
* `negative_damping_unstable` — `c < 0`: averaged matrix not Hurwitz and a multiplier outside the
  unit circle for every `k₁`, `k₂`, `T` (no modulation stabilizes a negative mean damping).
* `not_uniform_fast_decay` — negative mean stiffness: no uniform exponential decay for all
  sufficiently short periods (`Averaging.isHurwitz_of_switched_decay`).
-/

noncomputable section
namespace powerlib.ParametricResonance.Kapitza

open Set Matrix Function Filter Topology
open powerlib.Periodic (oscMatrix)
open powerlib.ParametricResonance.Meissner (shear rot shear_neg_mul_shear)

/-! ## The hyperbolic half period -/

section MatrixExp

open scoped Matrix.Norms.Frobenius

variable {n : ℕ}

/-- Closed form of `e^{tA}` when `B = A + a I` satisfies `B² = w² I` (`w ≠ 0`):
`e^{tA} = e^{−at} (cosh(wt) I + (sinh(wt)/w) B)`; the hyperbolic counterpart of
`LTI.exp_smul_of_sq_eq`, by the same uniqueness argument `LTI.exp_smul_eq_of_hasDerivAt`. -/
@[tmio T, powerlib_foundation] theorem exp_smul_of_sq_eq_sq {A : Matrix (Fin n) (Fin n) ℝ}
    {a w : ℝ} (hw : w ≠ 0)
    (hB : (A + a • 1) * (A + a • 1) = (w ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ)) (t : ℝ) :
    NormedSpace.exp (t • A) = (Real.exp (-a * t) * Real.cosh (w * t)) • (1 : Matrix _ _ ℝ) +
      (Real.exp (-a * t) * Real.sinh (w * t) / w) • (A + a • 1) := by
  set B := A + a • (1 : Matrix (Fin n) (Fin n) ℝ) with hBdef
  set f1 : ℝ → ℝ := fun s => Real.exp (-a * s) * Real.cosh (w * s) with hf1
  set f2 : ℝ → ℝ := fun s => Real.exp (-a * s) * Real.sinh (w * s) / w with hf2
  have he : ∀ s, HasDerivAt (fun s => Real.exp (-a * s)) (Real.exp (-a * s) * (-a)) s := by
    intro s
    have := ((hasDerivAt_id s).const_mul (-a)).exp
    simpa using this
  have hd1 : ∀ s, HasDerivAt f1 (-a * f1 s + w ^ 2 * f2 s) s := by
    intro s
    have hc : HasDerivAt (fun s => Real.cosh (w * s)) (Real.sinh (w * s) * w) s := by
      have := ((hasDerivAt_id s).const_mul w).cosh
      simpa [mul_comm] using this
    convert! (he s).mul hc using 1
    simp only [hf1, hf2]
    field_simp
  have hd2 : ∀ s, HasDerivAt f2 (f1 s - a * f2 s) s := by
    intro s
    have hs : HasDerivAt (fun s => Real.sinh (w * s)) (Real.cosh (w * s) * w) s := by
      have := ((hasDerivAt_id s).const_mul w).sinh
      simpa [mul_comm] using this
    convert! ((he s).mul hs).div_const w using 1
    simp only [hf1, hf2]
    field_simp
    ring
  have hA : A = B - a • (1 : Matrix (Fin n) (Fin n) ℝ) := by rw [hBdef]; abel
  have key := LTI.exp_smul_eq_of_hasDerivAt (A := A)
    (E := fun s => f1 s • (1 : Matrix (Fin n) (Fin n) ℝ) + f2 s • B)
    (by simp [hf1, hf2]) (fun s => by
      have h := ((hd1 s).smul_const (1 : Matrix (Fin n) (Fin n) ℝ)).add ((hd2 s).smul_const B)
      convert! h using 1
      simp only [hA, sub_mul, mul_add, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hB]
      module) t
  rw [← key]

end MatrixExp

/-- The flow `[[cosh η, sinh η/κ], [κ sinh η, cosh η]]` of `ÿ − κ² y = 0` over the hyperbolic
phase `η`. -/
def hyp (κ η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh η, Real.sinh η / κ; κ * Real.sinh η, Real.cosh η]

/-- `e^{h A} = e^{−ch} S H(κ, κh) S⁻¹` for `A = [[0, 1], [−k, −2c]]` with `κ² = c² − k`,
`κ ≠ 0` (a hyperbolic half period: `x = e^{−ct} y`, `ÿ − κ² y = 0`). -/
@[tmio T, powerlib_foundation] theorem exp_oscMatrix_hyp {c k κ : ℝ} (hκ : κ ^ 2 = c ^ 2 - k)
    (hκ0 : κ ≠ 0) (h : ℝ) :
    NormedSpace.exp (h • oscMatrix c k) =
      Real.exp (-(c * h)) • (shear c * hyp κ (κ * h) * shear (-c)) := by
  have hsq : (oscMatrix c k + c • 1) * (oscMatrix c k + c • 1) =
      (κ ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [oscMatrix, Matrix.mul_apply, Fin.sum_univ_two, hκ] <;> ring
  rw [exp_smul_of_sq_eq_sq hκ0 hsq h]
  have hk : k = c ^ 2 - κ ^ 2 := by linarith
  subst hk
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oscMatrix, shear, hyp] <;> field_simp <;> ring

/-! ## The two-level monodromy matrix -/

section Monodromy

variable {c k₁ k₂ T ν κ : ℝ}

/-- The monodromy matrix of `ẍ + 2c ẋ + k(t) x = 0` with the two-level stiffness `k = k₁` on the
first and `k = k₂` on the second half of every period `T`: the period map
`Averaging.periodMap (1/2) T B₁ B₂` of the two-topology switched system with duty ratio `1/2`,
`B_i = oscMatrix c k_i`. -/
def kapitzaMonodromy (c k₁ k₂ T : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  open scoped Matrix.Norms.Operator in
  Averaging.periodMap (1 / 2) T (oscMatrix c k₁) (oscMatrix c k₂)

/-- The reduced trace `2 cos θ cosh η + (κ/ν − ν/κ) sin θ sinh η`, `θ = νT/2`, `η = κT/2`, of one
oscillatory half period (frequency `ν`) followed by one hyperbolic half period (rate `κ`). -/
def kapitzaTrace (ν κ T : ℝ) : ℝ :=
  2 * Real.cos (ν * T / 2) * Real.cosh (κ * T / 2) +
    (κ / ν - ν / κ) * Real.sin (ν * T / 2) * Real.sinh (κ * T / 2)

/-- `M = e^{(T/2)B₂} e^{(T/2)B₁}`. -/
@[tmio T, powerlib_foundation] theorem kapitzaMonodromy_eq_exp (c k₁ k₂ T : ℝ) :
    kapitzaMonodromy c k₁ k₂ T = NormedSpace.exp ((T / 2) • oscMatrix c k₂) *
      NormedSpace.exp ((T / 2) • oscMatrix c k₁) := by
  show NormedSpace.exp (((1 - 1 / 2 : ℝ) * T) • oscMatrix c k₂) *
    NormedSpace.exp (((1 / 2 : ℝ) * T) • oscMatrix c k₁) = _
  rw [show (1 - 1 / 2 : ℝ) * T = T / 2 by ring, show (1 / 2 : ℝ) * T = T / 2 by ring]

/-- `M = e^{−cT} S (H(κ, η) R(ν, θ)) S⁻¹`, `θ = νT/2`, `η = κT/2`, for an oscillatory first half
(`ν² = k₁ − c²`) and a hyperbolic second half (`κ² = c² − k₂`). -/
@[tmio T, powerlib_foundation] theorem kapitzaMonodromy_eq (hν : ν ^ 2 = k₁ - c ^ 2)
    (hκ : κ ^ 2 = c ^ 2 - k₂) (h₁ : ν ≠ 0) (h₂ : κ ≠ 0) :
    kapitzaMonodromy c k₁ k₂ T = Real.exp (-(c * T)) •
      (shear c * (hyp κ (κ * T / 2) * rot ν (ν * T / 2)) * shear (-c)) := by
  rw [kapitzaMonodromy_eq_exp, exp_oscMatrix_hyp hκ h₂, Meissner.exp_oscMatrix hν h₁,
    smul_mul_smul_comm, ← Real.exp_add, show -(c * (T / 2)) + -(c * (T / 2)) = -(c * T) by ring,
    show κ * (T / 2) = κ * T / 2 by ring, show ν * (T / 2) = ν * T / 2 by ring]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (shear (-c)) (shear c), shear_neg_mul_shear, Matrix.one_mul]

/-- `tr(H(κ, κT/2) R(ν, νT/2)) = 2 cos θ cosh η + (κ/ν − ν/κ) sin θ sinh η`. -/
@[tmio T, powerlib_foundation] theorem trace_hyp_mul_rot {ν κ : ℝ} (h₁ : ν ≠ 0) (h₂ : κ ≠ 0)
    (T : ℝ) : (hyp κ (κ * T / 2) * rot ν (ν * T / 2)).trace = kapitzaTrace ν κ T := by
  simp only [hyp, rot, kapitzaTrace, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  field_simp
  ring

/-- `det M = e^{−2cT}` for every pair of stiffness levels (Liouville's formula for the two
half-period exponentials, `Periodic.det_exp_smul`). -/
@[tmio T, powerlib_foundation] theorem det_kapitzaMonodromy (c k₁ k₂ T : ℝ) :
    (kapitzaMonodromy c k₁ k₂ T).det = Real.exp (-(2 * c) * T) := by
  rw [kapitzaMonodromy_eq_exp, Matrix.det_mul, Periodic.det_exp_smul, Periodic.det_exp_smul,
    Periodic.trace_oscMatrix, Periodic.trace_oscMatrix, ← Real.exp_add]
  ring_nf

/-- `tr M = e^{−cT} τ`, `τ = kapitzaTrace ν κ T`. -/
@[tmio T, powerlib_foundation] theorem trace_kapitzaMonodromy (hν : ν ^ 2 = k₁ - c ^ 2)
    (hκ : κ ^ 2 = c ^ 2 - k₂) (h₁ : ν ≠ 0) (h₂ : κ ≠ 0) :
    (kapitzaMonodromy c k₁ k₂ T).trace = Real.exp (-(c * T)) * kapitzaTrace ν κ T := by
  rw [kapitzaMonodromy_eq hν hκ h₁ h₂, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, shear_neg_mul_shear, Matrix.one_mul, trace_hyp_mul_rot h₁ h₂]

/-- **The exact boundary.** For `c ≥ 0` the two-level system is Floquet unstable (a multiplier
outside the unit circle) iff `2 cosh(cT) < |τ|`. -/
@[tmio T, powerlib_foundation] theorem floquetUnstable_iff (hν : ν ^ 2 = k₁ - c ^ 2)
    (hκ : κ ^ 2 = c ^ 2 - k₂) (h₁ : ν ≠ 0) (h₂ : κ ≠ 0) (hc : 0 ≤ c) (hT : 0 < T) :
    (∃ μ ∈ spectrum ℂ ((kapitzaMonodromy c k₁ k₂ T).map (algebraMap ℝ ℂ)), 1 < ‖μ‖) ↔
      2 * Real.cosh (c * T) < |kapitzaTrace ν κ T| := by
  have hdet := det_kapitzaMonodromy c k₁ k₂ T
  have h0 : 0 < (kapitzaMonodromy c k₁ k₂ T).det := by rw [hdet]; positivity
  have h1 : (kapitzaMonodromy c k₁ k₂ T).det ≤ 1 := by
    rw [hdet, Real.exp_le_one_iff]; nlinarith
  have e : 1 + Real.exp (-(2 * c) * T) = Real.exp (-(c * T)) * (2 * Real.cosh (c * T)) := by
    rw [Real.cosh_eq, mul_div_cancel₀ _ two_ne_zero, mul_add, ← Real.exp_add, ← Real.exp_add,
      show -(c * T) + c * T = 0 by ring, show -(c * T) + -(c * T) = -(2 * c) * T by ring,
      Real.exp_zero]
  rw [Periodic.exists_one_lt_norm_iff h0 h1, hdet, trace_kapitzaMonodromy hν hκ h₁ h₂,
    abs_mul, abs_of_pos (Real.exp_pos _), e]
  exact mul_lt_mul_iff_right₀ (Real.exp_pos _)

/-- For `c > 0`: every multiplier lies strictly inside the unit circle iff `|τ| < 2 cosh(cT)`. -/
@[tmio T, powerlib_foundation] theorem schurStable_iff (hν : ν ^ 2 = k₁ - c ^ 2)
    (hκ : κ ^ 2 = c ^ 2 - k₂) (h₁ : ν ≠ 0) (h₂ : κ ≠ 0) (hc : 0 < c) (hT : 0 < T) :
    LTI.SchurStable (kapitzaMonodromy c k₁ k₂ T) ↔
      |kapitzaTrace ν κ T| < 2 * Real.cosh (c * T) := by
  have hdet := det_kapitzaMonodromy c k₁ k₂ T
  have h1 : (kapitzaMonodromy c k₁ k₂ T).det < 1 := by
    rw [hdet, Real.exp_lt_one_iff]; nlinarith
  have e : 1 + Real.exp (-(2 * c) * T) = Real.exp (-(c * T)) * (2 * Real.cosh (c * T)) := by
    rw [Real.cosh_eq, mul_div_cancel₀ _ two_ne_zero, mul_add, ← Real.exp_add, ← Real.exp_add,
      show -(c * T) + c * T = 0 by ring, show -(c * T) + -(c * T) = -(2 * c) * T by ring,
      Real.exp_zero]
  rw [Periodic.schurStable_iff_abs_trace_lt h1, hdet, trace_kapitzaMonodromy hν hκ h₁ h₂,
    abs_mul, abs_of_pos (Real.exp_pos _), e]
  exact mul_lt_mul_iff_right₀ (Real.exp_pos _)

/-- **Undamped neutral stability.** For `c = 0` (`ν² = k₁`, `κ² = −k₂`) and `|τ| < 2`, every
multiplier is non-real and lies on the unit circle (`det M = 1`). -/
@[tmio T, powerlib_foundation] theorem undamped_norm_eq_one (hν : ν ^ 2 = k₁) (hκ : κ ^ 2 = -k₂)
    (h₁ : ν ≠ 0) (h₂ : κ ≠ 0) (hτ : |kapitzaTrace ν κ T| < 2) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ ((kapitzaMonodromy 0 k₁ k₂ T).map (algebraMap ℝ ℂ))) :
    μ.im ≠ 0 ∧ ‖μ‖ = 1 := by
  have hdet : (kapitzaMonodromy 0 k₁ k₂ T).det = 1 := by
    rw [det_kapitzaMonodromy]; simp
  have htr : (kapitzaMonodromy 0 k₁ k₂ T).trace = kapitzaTrace ν κ T := by
    rw [trace_kapitzaMonodromy (by rw [hν]; ring) (by rw [hκ]; ring) h₁ h₂]; simp
  have him : μ.im ≠ 0 := by
    intro him
    have hroot := Periodic.mem_spectrum_iff_root.mp hμ
    have hre := congrArg Complex.re hroot
    simp [pow_two, Complex.mul_re, him, hdet, htr] at hre
    have ha := abs_lt.mp hτ
    nlinarith [sq_nonneg (2 * μ.re - kapitzaTrace ν κ T)]
  refine ⟨him, ?_⟩
  have h := Periodic.sq_norm_eq_det_of_im_ne_zero hμ him
  rw [hdet] at h
  have hn := norm_nonneg μ
  nlinarith

end Monodromy

/-! ## The stabilization window at a half turn -/

section Window

/-- At a half turn of the oscillatory half period (`θ = νT/2 = π/2`, i.e. `T = π/ν`):
`τ = (κ/ν − ν/κ) sinh(κπ/(2ν))`. -/
@[tmio T, powerlib_foundation] theorem kapitzaTrace_half_turn {ν : ℝ} (hν : ν ≠ 0) (κ : ℝ) :
    kapitzaTrace ν κ (Real.pi / ν) = (κ / ν - ν / κ) * Real.sinh (κ * Real.pi / (2 * ν)) := by
  have h1 : ν * (Real.pi / ν) / 2 = Real.pi / 2 := by field_simp
  have h2 : κ * (Real.pi / ν) / 2 = κ * Real.pi / (2 * ν) := by field_simp
  rw [kapitzaTrace, h1, h2, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

/-- **The exact stabilization window at a half turn.** There is `r₀ ∈ (1, 2)`, the root of
`(r − 1/r) sinh(rπ/2) = 2`, such that for `0 < ν ≤ κ` and `T = π/ν` the undamped reduced trace
satisfies `|τ| < 2` iff `κ < r₀ ν`: the window `ν < κ < r₀ν` is nonempty, and on it the
hyperbolic half period is the stronger one (`κ > ν`). The map `r ↦ (r − 1/r) sinh(rπ/2)` is
strictly increasing on `[1, ∞)`, vanishes at `1` and exceeds `2` at `2`. -/
@[tmio T, powerlib_foundation] theorem exists_window :
    ∃ r₀ : ℝ, 1 < r₀ ∧ r₀ < 2 ∧ (r₀ - r₀⁻¹) * Real.sinh (r₀ * Real.pi / 2) = 2 ∧
      ∀ ν κ : ℝ, 0 < ν → ν ≤ κ → (|kapitzaTrace ν κ (Real.pi / ν)| < 2 ↔ κ < r₀ * ν) := by
  set f : ℝ → ℝ := fun r => (r - r⁻¹) * Real.sinh (r * Real.pi / 2) with hfdef
  have hmono : StrictMonoOn f (Ici 1) := by
    intro a ha b hb hab
    simp only [mem_Ici] at ha hb
    have ha0 : 0 < a := by linarith
    have h1 : a - a⁻¹ < b - b⁻¹ := by
      have : b⁻¹ < a⁻¹ := inv_strictAnti₀ ha0 hab
      linarith
    have h2 : 0 ≤ a - a⁻¹ := by
      have : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha
      linarith
    have h3 : Real.sinh (a * Real.pi / 2) < Real.sinh (b * Real.pi / 2) :=
      Real.sinh_lt_sinh.mpr (by nlinarith [Real.pi_pos])
    have h4 : 0 < Real.sinh (a * Real.pi / 2) := Real.sinh_pos_iff.mpr (by positivity)
    show (a - a⁻¹) * Real.sinh (a * Real.pi / 2) < (b - b⁻¹) * Real.sinh (b * Real.pi / 2)
    nlinarith
  have hcont : ContinuousOn f (Icc 1 2) := by
    refine ContinuousOn.mul (continuousOn_id.sub (continuousOn_id.inv₀ fun x hx => ?_))
      (Continuous.continuousOn (by fun_prop))
    have := hx.1
    simp only [id]
    linarith
  have hf1 : f 1 = 0 := by simp [hfdef]
  have hf2 : 2 < f 2 := by
    have hs : Real.pi ≤ Real.sinh Real.pi := Real.self_le_sinh_iff.mpr Real.pi_pos.le
    have := Real.two_le_pi
    simp only [hfdef]
    rw [show 2 * Real.pi / 2 = Real.pi by ring]
    norm_num
    nlinarith
  obtain ⟨r₀, hr₀, hfr₀⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hcont
    ⟨by rw [hf1]; norm_num, hf2.le⟩
  have hr₀1 : 1 < r₀ := by
    rcases hr₀.1.eq_or_lt with h | h
    · rw [← h, hf1] at hfr₀; norm_num at hfr₀
    · exact h
  have hr₀2 : r₀ < 2 := by
    rcases hr₀.2.eq_or_lt with h | h
    · rw [h] at hfr₀; linarith
    · exact h
  refine ⟨r₀, hr₀1, hr₀2, hfr₀, fun ν κ hν hνκ => ?_⟩
  have hr : 1 ≤ κ / ν := by rw [le_div_iff₀ hν]; linarith
  have hτ : kapitzaTrace ν κ (Real.pi / ν) = f (κ / ν) := by
    rw [kapitzaTrace_half_turn hν.ne']
    simp only [hfdef, inv_div]
    congr 2
    field_simp
  have hnn : 0 ≤ f (κ / ν) := by
    rw [← hf1]
    exact hmono.monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hr) hr
  rw [hτ, abs_of_nonneg hnn, ← hfr₀, hmono.lt_iff_lt (mem_Ici.mpr hr) (mem_Ici.mpr hr₀1.le),
    div_lt_iff₀ hν]

end Window

/-! ## The small-signal verdict: the averaged and the frozen matrices -/

section SmallSignal

open scoped Matrix.Norms.Operator

/-- The averaged (state-space averaged, duty ratio `1/2`) matrix of the two-level system is the
oscillator matrix of the mean stiffness `(k₁ + k₂)/2`. -/
@[tmio T, powerlib_foundation] theorem avgMatrix_oscMatrix (c k₁ k₂ : ℝ) :
    Averaging.avgMatrix (1 / 2) (oscMatrix c k₁) (oscMatrix c k₂) =
      oscMatrix c ((k₁ + k₂) / 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Averaging.avgMatrix, oscMatrix] <;> ring

/-- **A negative stiffness is a saddle.** For `k < 0` the matrix `[[0, 1], [−k, −2c]]` has a real
eigenvalue `λ > 0` with the real eigenvector `(1, λ)` (whatever the sign of `c`), so
`ẏ = A y` has the exponentially growing solution `e^{λt}(1, λ)`, and `A` is not Hurwitz. -/
@[tmio T, powerlib_foundation] theorem oscMatrix_saddle {c k : ℝ} (hk : k < 0) :
    (∃ r : ℝ, 0 < r ∧ oscMatrix c k *ᵥ ![1, r] = r • ![1, r]) ∧
      ¬ LinearSystems.IsHurwitz (oscMatrix c k) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr, hroot⟩ := Criteria.exists_quadratic_root_pos_of_const_neg (a1 := 2 * c) hk
    refine ⟨r, hr, ?_⟩
    funext i
    fin_cases i
    · simp [oscMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp [oscMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      nlinarith
  · rw [Criteria.isHurwitz_fin_two_iff, Periodic.det_oscMatrix]
    intro h
    linarith [h.2]

end SmallSignal

/-! ## Decay of switched trajectories at a fixed period -/

section Decay

open scoped Matrix.Norms.Operator

variable {n : ℕ}

/-- **Floquet stability of a switched system at a fixed period.** If the period map
`e^{(1−d)TA₂} e^{dTA₁}` of the two-topology switched system is Schur stable, every switched
trajectory decays exponentially at every instant, `‖x(t)‖ ≤ C e^{−αt} ‖x(0)‖` for `t ≥ 0`,
with `C`, `α > 0` depending on `A₁`, `A₂`, `d`, `T` only (`Averaging.switched_sample`,
`LTI.SchurStable.exists_pow_bound`, and the bound `e^{(‖A₁‖ + ‖A₂‖)T}` inside one period). -/
@[tmio T, powerlib_foundation] theorem switched_decay_of_schurStable {d T : ℝ} (hd0 : 0 ≤ d)
    (hd1 : d ≤ 1) (hT : 0 < T) (A₁ A₂ : Matrix (Fin n) (Fin n) ℝ)
    (hS : LTI.SchurStable (Averaging.periodMap d T A₁ A₂)) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ x : ℝ → Fin n → ℝ,
      (∀ k : ℕ, IsIntegralCurveOn x (fun _ y => A₁ *ᵥ y) (Icc (k * T) (k * T + d * T)) ∧
        IsIntegralCurveOn x (fun _ y => A₂ *ᵥ y) (Icc (k * T + d * T) ((k + 1) * T))) →
      ∀ t : ℝ, 0 ≤ t → ‖x t‖ ≤ C * Real.exp (-(α * t)) * ‖x 0‖ := by
  obtain ⟨C₀, hC₀, ρ, hρ0, hρ1, hb⟩ := hS.exists_pow_bound
  set γ := -Real.log ρ with hγdef
  have hγ : 0 < γ := by rw [hγdef, neg_pos]; exact Real.log_neg hρ0 hρ1
  have hργ : ρ = Real.exp (-γ) := by rw [hγdef, neg_neg, Real.exp_log hρ0]
  set B := Real.exp ((‖A₁‖ + ‖A₂‖) * T) with hBdef
  have hB1 : 1 ≤ B := Real.one_le_exp (by positivity)
  refine ⟨B * C₀ * Real.exp γ, γ / T, by positivity, div_pos hγ hT, fun x hx t ht => ?_⟩
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · rw [Subsingleton.elim (x t) 0, norm_zero]
    positivity
  set k := ⌊t / T⌋₊ with hkdef
  have hk1 : (k : ℝ) * T ≤ t := by
    have := Nat.floor_le (div_nonneg ht hT.le)
    rwa [le_div_iff₀ hT] at this
  have hk2 : t < ((k : ℝ) + 1) * T := by
    have := Nat.lt_floor_add_one (t / T)
    rwa [div_lt_iff₀ hT] at this
  obtain ⟨h1, h2⟩ := hx k
  have hdT : 0 ≤ d * T := mul_nonneg hd0 hT.le
  -- inside the period: `‖x(t)‖ ≤ B ‖x(kT)‖`
  have hin : ‖x t‖ ≤ B * ‖x (k * T)‖ := by
    by_cases hon : t ≤ k * T + d * T
    · rw [Averaging.const_solution_eq h1 ⟨hk1, hon⟩]
      refine (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      refine (Averaging.norm_exp_smul_le _ (by linarith)).trans (Real.exp_le_exp.mpr ?_)
      nlinarith [norm_nonneg A₁, norm_nonneg A₂]
    · push Not at hon
      have e1 := Averaging.const_solution_eq h1 (t := k * T + d * T) ⟨by linarith, le_rfl⟩
      rw [show k * T + d * T - k * T = d * T by ring] at e1
      rw [Averaging.const_solution_eq h2 ⟨hon.le, by linarith⟩, e1, Matrix.mulVec_mulVec]
      refine (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      refine (norm_mul_le _ _).trans ?_
      have e2 := Averaging.norm_exp_smul_le A₂ (s := t - (k * T + d * T)) (by linarith)
      have e3 := Averaging.norm_exp_smul_le A₁ hdT
      calc ‖NormedSpace.exp ((t - (k * T + d * T)) • A₂)‖ * ‖NormedSpace.exp ((d * T) • A₁)‖
          ≤ Real.exp (‖A₂‖ * (t - (k * T + d * T))) * Real.exp (‖A₁‖ * (d * T)) :=
            mul_le_mul e2 e3 (norm_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (‖A₂‖ * (t - (k * T + d * T)) + ‖A₁‖ * (d * T)) := (Real.exp_add _ _).symm
        _ ≤ B := by
            apply Real.exp_le_exp.mpr
            have hdT1 : d * T ≤ T := by nlinarith
            nlinarith [norm_nonneg A₁, norm_nonneg A₂]
  -- at the sampling instant: `‖x(kT)‖ ≤ C₀ ρ^k ‖x(0)‖`
  have hsamp : ‖x (k * T)‖ ≤ C₀ * ρ ^ k * ‖x 0‖ := by
    rw [Averaging.switched_sample hd0 hd1 hT.le hx k]
    exact (Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul_of_nonneg_right (hb k) (norm_nonneg _))
  have hρk : ρ ^ k ≤ Real.exp γ * Real.exp (-(γ / T * t)) := by
    rw [hργ, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : t / T < k + 1 := by rw [div_lt_iff₀ hT]; linarith
    have e : γ / T * t = γ * (t / T) := by ring
    rw [e]
    nlinarith
  calc ‖x t‖ ≤ B * ‖x (k * T)‖ := hin
    _ ≤ B * (C₀ * ρ ^ k * ‖x 0‖) := by gcongr
    _ ≤ B * (C₀ * (Real.exp γ * Real.exp (-(γ / T * t))) * ‖x 0‖) := by gcongr
    _ = B * C₀ * Real.exp γ * Real.exp (-(γ / T * t)) * ‖x 0‖ := by ring

end Decay

/-! ## Small-signal analysis versus the periodic system -/

section Levels

open scoped Matrix.Norms.Operator

/-- **Small-signal false alarm (parametric stabilization).** Damping `c > 0`, an oscillatory half
period of reduced frequency `ν > 0` (stiffness `k₁ = ν² + c²`) and a hyperbolic half period of
reduced rate `κ > 0` (stiffness `k₂ = c² − κ²`) with negative mean stiffness
(`ν² + 2c² < κ²`, i.e. `(k₁ + k₂)/2 < 0`). Small-signal analysis predicts instability: the
averaged matrix `oscMatrix c ((k₁ + k₂)/2)` (`Averaging.avgMatrix`) and the frozen matrix of the
second half period are saddles (a real eigenvalue `r > 0`, not Hurwitz). Yet if the undamped
reduced trace satisfies `|τ| < 2`, the periodic system is Floquet stable: the monodromy matrix is
Schur stable and every trajectory of the switched system decays exponentially. -/
@[tmio T, powerlib_foundation] theorem small_signal_false_alarm {ν κ c T : ℝ} (hν : 0 < ν)
    (hκ : 0 < κ) (hc : 0 < c) (hT : 0 < T) (hm : ν ^ 2 + 2 * c ^ 2 < κ ^ 2)
    (hτ : |kapitzaTrace ν κ T| < 2) :
    (ν ^ 2 + c ^ 2 + (c ^ 2 - κ ^ 2)) / 2 < 0 ∧
      (∃ r : ℝ, 0 < r ∧ Averaging.avgMatrix (1 / 2) (oscMatrix c (ν ^ 2 + c ^ 2))
        (oscMatrix c (c ^ 2 - κ ^ 2)) *ᵥ ![1, r] = r • ![1, r]) ∧
      ¬ LinearSystems.IsHurwitz (Averaging.avgMatrix (1 / 2) (oscMatrix c (ν ^ 2 + c ^ 2))
        (oscMatrix c (c ^ 2 - κ ^ 2))) ∧
      ¬ LinearSystems.IsHurwitz (oscMatrix c (c ^ 2 - κ ^ 2)) ∧
      LTI.SchurStable (kapitzaMonodromy c (ν ^ 2 + c ^ 2) (c ^ 2 - κ ^ 2) T) ∧
      ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ x : ℝ → Fin 2 → ℝ,
        (∀ k : ℕ, IsIntegralCurveOn x (fun _ y => oscMatrix c (ν ^ 2 + c ^ 2) *ᵥ y)
            (Icc (k * T) (k * T + 1 / 2 * T)) ∧
          IsIntegralCurveOn x (fun _ y => oscMatrix c (c ^ 2 - κ ^ 2) *ᵥ y)
            (Icc (k * T + 1 / 2 * T) ((k + 1) * T))) →
        ∀ t : ℝ, 0 ≤ t → ‖x t‖ ≤ C * Real.exp (-(α * t)) * ‖x 0‖ := by
  have hmean : (ν ^ 2 + c ^ 2 + (c ^ 2 - κ ^ 2)) / 2 < 0 := by linarith
  obtain ⟨hsad, hnot⟩ := oscMatrix_saddle (c := c) hmean
  have hS : LTI.SchurStable (kapitzaMonodromy c (ν ^ 2 + c ^ 2) (c ^ 2 - κ ^ 2) T) := by
    rw [schurStable_iff (ν := ν) (κ := κ) (by ring) (by ring) hν.ne' hκ.ne' hc hT]
    have := Real.one_lt_cosh.mpr (mul_pos hc hT).ne'
    linarith
  refine ⟨hmean, by rw [avgMatrix_oscMatrix]; exact hsad, by rw [avgMatrix_oscMatrix]; exact hnot,
    (oscMatrix_saddle (by nlinarith)).2, hS, ?_⟩
  exact switched_decay_of_schurStable (by norm_num) (by norm_num) hT _ _ hS

/-- **Small damping keeps an undamped stable configuration stable.** For fixed stiffness levels
`k₁ > 0`, `k₂ < 0` and period `T > 0` with undamped reduced trace `|τ(√k₁, √(−k₂), T)| < 2`
(multipliers on the unit circle, `undamped_norm_eq_one`), every damping `c ∈ (0, c₀)` makes the
monodromy matrix Schur stable, for some `c₀ > 0` (continuity of the reduced trace in `c` and
`schurStable_iff`). -/
@[tmio T, powerlib_foundation] theorem damped_schurStable_of_undamped {k₁ k₂ T : ℝ}
    (hk₁ : 0 < k₁) (hk₂ : k₂ < 0) (hT : 0 < T) (hτ : |kapitzaTrace (√k₁) (√(-k₂)) T| < 2) :
    ∃ c₀ > 0, ∀ c ∈ Ioo 0 c₀, LTI.SchurStable (kapitzaMonodromy c k₁ k₂ T) := by
  set g : ℝ → ℝ := fun c => kapitzaTrace (√(k₁ - c ^ 2)) (√(c ^ 2 - k₂)) T with hgdef
  have hνc : Continuous fun c : ℝ => √(k₁ - c ^ 2) := by fun_prop
  have hκc : Continuous fun c : ℝ => √(c ^ 2 - k₂) := by fun_prop
  have hν0 : √(k₁ - 0 ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr (by simpa using hk₁)
  have hκ0 : √(0 ^ 2 - k₂) ≠ 0 := Real.sqrt_ne_zero'.mpr (by simpa using hk₂)
  have hg : ContinuousAt g 0 := by
    simp only [hgdef, kapitzaTrace]
    refine ContinuousAt.add (Continuous.continuousAt (by fun_prop)) ?_
    refine ContinuousAt.mul (ContinuousAt.mul ?_ (Continuous.continuousAt (by fun_prop)))
      (Continuous.continuousAt (by fun_prop))
    exact (hκc.continuousAt.div hνc.continuousAt hν0).sub
      (hνc.continuousAt.div hκc.continuousAt hκ0)
  have hg0 : |g 0| < 2 := by simpa [hgdef] using hτ
  have hev : ∀ᶠ c in 𝓝 (0 : ℝ), |g c| < 2 :=
    (continuous_abs.continuousAt.comp hg).eventually_lt continuousAt_const hg0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min ε (√k₁), lt_min hε (Real.sqrt_pos.mpr hk₁), fun c hc => ?_⟩
  have hc0 := hc.1
  have hcε : c < ε := hc.2.trans_le (min_le_left _ _)
  have hck : c < √k₁ := hc.2.trans_le (min_le_right _ _)
  have hc2 : c ^ 2 < k₁ := by
    have := pow_lt_pow_left₀ hck hc0.le two_ne_zero
    rwa [Real.sq_sqrt hk₁.le] at this
  have hν : 0 < k₁ - c ^ 2 := by linarith
  have hκ : 0 < c ^ 2 - k₂ := by nlinarith
  have hgc : |g c| < 2 := hball (by rw [Real.dist_eq, sub_zero, abs_of_pos hc0]; exact hcε)
  rw [schurStable_iff (Real.sq_sqrt hν.le) (Real.sq_sqrt hκ.le) (Real.sqrt_pos.mpr hν).ne'
    (Real.sqrt_pos.mpr hκ).ne' hc0 hT]
  have := Real.one_lt_cosh.mpr (mul_pos hc0 hT).ne'
  simp only [hgdef] at hgc
  linarith

/-- **Parametric stabilization exists, on an explicit window.** With `r₀ ∈ (1, 2)` the root of
`(r − 1/r) sinh(rπ/2) = 2` (`exists_window`): for every `ν > 0` and every `κ` with
`ν < κ < r₀ ν`, the two-level system with stiffness `ν²` on the first and `−κ²` on the second
half of the period `T = π/ν` (half turn `θ = νT/2 = π/2`, `τ = (κ/ν − ν/κ) sinh(κπ/(2ν))`) has
negative mean stiffness `(ν² − κ²)/2`, so its averaged matrix is a saddle for every damping `c`
(small-signal unstable); undamped, every Floquet multiplier is non-real and on the unit circle;
and for every damping `c ∈ (0, c₀)` every multiplier lies strictly inside the unit circle. -/
@[tmio T, powerlib_foundation] theorem parametric_stabilization :
    ∃ r₀ : ℝ, 1 < r₀ ∧ ∀ ν κ : ℝ, 0 < ν → ν < κ → κ < r₀ * ν →
      (ν ^ 2 + -κ ^ 2) / 2 < 0 ∧
        (∀ c : ℝ, ¬ LinearSystems.IsHurwitz (Averaging.avgMatrix (1 / 2) (oscMatrix c (ν ^ 2))
          (oscMatrix c (-κ ^ 2)))) ∧
        (∀ μ ∈ spectrum ℂ ((kapitzaMonodromy 0 (ν ^ 2) (-κ ^ 2) (Real.pi / ν)).map
          (algebraMap ℝ ℂ)), μ.im ≠ 0 ∧ ‖μ‖ = 1) ∧
        ∃ c₀ > 0, ∀ c ∈ Ioo 0 c₀,
          LTI.SchurStable (kapitzaMonodromy c (ν ^ 2) (-κ ^ 2) (Real.pi / ν)) := by
  obtain ⟨r₀, hr₀, -, -, hwin⟩ := exists_window
  refine ⟨r₀, hr₀, fun ν κ hν hνκ hκr => ?_⟩
  have hκ : 0 < κ := hν.trans hνκ
  have hτ := (hwin ν κ hν hνκ.le).mpr hκr
  have hmean : (ν ^ 2 + -κ ^ 2) / 2 < 0 := by nlinarith
  refine ⟨hmean, fun c => ?_, fun μ hμ => undamped_norm_eq_one (ν := ν) (κ := κ) rfl (by ring)
    hν.ne' hκ.ne' hτ hμ, ?_⟩
  · rw [avgMatrix_oscMatrix]
    exact (oscMatrix_saddle hmean).2
  · refine damped_schurStable_of_undamped (by positivity) (by nlinarith)
      (div_pos Real.pi_pos hν) ?_
    rwa [Real.sqrt_sq hν.le, neg_neg, Real.sqrt_sq hκ.le]

/-- **Negative mean damping is never stabilized** (the levels agree). For `c < 0` the averaged
matrix is not Hurwitz, and for every pair of stiffness levels `k₁`, `k₂` and every period `T > 0`
some Floquet multiplier lies outside the unit circle: the product of the two multipliers is
`det M = e^{−2cT} > 1` (Liouville, `det_kapitzaMonodromy`), whatever the stiffness modulation. -/
@[tmio T, powerlib_foundation] theorem negative_damping_unstable {c : ℝ} (hc : c < 0)
    (k₁ k₂ : ℝ) {T : ℝ} (hT : 0 < T) :
    ¬ LinearSystems.IsHurwitz (Averaging.avgMatrix (1 / 2) (oscMatrix c k₁) (oscMatrix c k₂)) ∧
      ∃ μ ∈ spectrum ℂ ((kapitzaMonodromy c k₁ k₂ T).map (algebraMap ℝ ℂ)), 1 < ‖μ‖ := by
  refine ⟨?_, ?_⟩
  · rw [avgMatrix_oscMatrix, Criteria.isHurwitz_fin_two_iff, Periodic.trace_oscMatrix]
    intro h
    linarith [h.1]
  set P := kapitzaMonodromy c k₁ k₂ T with hP
  have hdet : 1 < P.det := by
    rw [hP, det_kapitzaMonodromy, Real.one_lt_exp_iff]
    nlinarith
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (((P.trace : ℂ)) ^ 2 - 4 * (P.det : ℂ))
    two_pos
  have hroot : ∀ μ : ℂ, μ = (P.trace + s) / 2 ∨ μ = (P.trace - s) / 2 →
      μ ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ)) := by
    rintro μ (rfl | rfl) <;> rw [Periodic.mem_spectrum_iff_root] <;>
      linear_combination hs / 4
  have hprod : ‖((P.trace : ℂ) + s) / 2‖ * ‖((P.trace : ℂ) - s) / 2‖ = P.det := by
    rw [← norm_mul, show ((P.trace : ℂ) + s) / 2 * (((P.trace : ℂ) - s) / 2) = (P.det : ℂ) by
      linear_combination -hs / 4, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  by_contra hno
  push Not at hno
  have h1 := hno _ (hroot _ (Or.inl rfl))
  have h2 := hno _ (hroot _ (Or.inr rfl))
  have : ‖((P.trace : ℂ) + s) / 2‖ * ‖((P.trace : ℂ) - s) / 2‖ ≤ 1 * 1 :=
    mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
  linarith

/-- **First-order averaging is the fast-switching limit.** If the mean stiffness is negative,
no fast switching between the two stiffness levels is uniformly stable: there are no `T₀ > 0`,
`C`, `α > 0` such that every switched trajectory decays as `C e^{−αt}` for every period
`T ∈ (0, T₀]` (`Averaging.isHurwitz_of_switched_decay`; the averaged matrix is a saddle). The
stabilization of `small_signal_false_alarm` is a finite-period effect, outside the validity of
first-order averaging. -/
@[tmio T, powerlib_foundation] theorem not_uniform_fast_decay {c k₁ k₂ : ℝ} (hk : k₁ + k₂ < 0)
    {T₀ C α : ℝ} (hT₀ : 0 < T₀) (hα : 0 < α) :
    ¬ ∀ T ∈ Ioc (0 : ℝ) T₀, ∀ x : ℝ → Fin 2 → ℝ,
      (∀ k : ℕ, IsIntegralCurveOn x (fun _ y => oscMatrix c k₁ *ᵥ y)
          (Icc (k * T) (k * T + 1 / 2 * T)) ∧
        IsIntegralCurveOn x (fun _ y => oscMatrix c k₂ *ᵥ y)
          (Icc (k * T + 1 / 2 * T) ((k + 1) * T))) →
      ∀ t : ℝ, 0 ≤ t → ‖x t‖ ≤ C * Real.exp (-(α * t)) * ‖x 0‖ := by
  intro h
  have hH := Averaging.isHurwitz_of_switched_decay (by norm_num) (by norm_num)
    (oscMatrix c k₁) (oscMatrix c k₂) hT₀ hα h
  rw [avgMatrix_oscMatrix] at hH
  exact (oscMatrix_saddle (c := c) (k := (k₁ + k₂) / 2) (by linarith)).2 hH

end Levels

end powerlib.ParametricResonance.Kapitza
