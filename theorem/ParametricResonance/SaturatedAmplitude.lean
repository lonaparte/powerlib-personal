import theorem.ParametricResonance.SlowFlowBranches
import theorem.PhasePlane.Planar
import theorem.Dynamics.ConverseLinearization

/-! # The saturated amplitude of a parametric oscillation: the cubic 2:1 amplitude equation

The linear slow flow of the principal (2:1) parametric resonance
(`theorem/ParametricResonance/SlowFlow.lean`, `theorem/ParametricResonance/SlowFlowBranches.lean`)
decides whether the zero state grows; how far it grows needs the next resonant term. In the frame
rotating at half the pump frequency the first resonant nonlinearity is cubic:

`ż = −(σ + jΔ) z + c z̄ + (−η + jβ) |z|² z`,

with averaged damping `σ`, detuning `Δ`, pump coefficient `c`, nonlinear damping `η` and
amplitude-dependent frequency shift `β` (a Duffing stiffness gives `β`,
`theorem/ParametricResonance/DuffingMathieu.lean`). A phase-locked state `z = a e^{jφ}`, `a > 0`, is a
steady oscillation at exactly half the pump frequency in the original frame; this module derives
its amplitude and its stability exactly, inside the amplitude equation.

Scope.
* The complex amplitude equation `ampField σ Δ c η β` (real `σ, Δ, η, β`, complex `c`) and the
  same field in the real coordinates `(Re z, Im z)` on `State 2 = EuclideanSpace ℝ (Fin 2)`
  (`ampSystem`, via `toReal` of `theorem/ParametricResonance/SlowFlow.lean`): continuous time,
  autonomous, no input. Its linear part is exactly `slowFlowField σ Δ c`.
* Sign convention: `Δ` is the detuning of the slow flow, `Δ = ω_p/2 − ω` (pump half-frequency
  minus natural frequency); with the opposite convention `Δ' = −Δ` the linear part reads
  `(−σ + jΔ') z` and every formula below holds with `Δ = −Δ'`.
* Stability of a steady state is LeanForControl's `LocallyExponentiallyStable` / `Unstable` of the
  real field, decided by its Jacobian (`Dynamics.locallyExponentiallyStable_iff_isHurwitz_of_eq`,
  `Criteria.unstable_of_jacobian_det`, `Criteria.unstable_of_jacobian_trace_pos`). Degenerate
  steady states (zero determinant, e.g. at a fold `|c| = σ` of the Duffing case) are not decided.
* Generic mathematics, no model family; the averaging step that produces this equation from an
  oscillator is in `theorem/ParametricResonance/DuffingMathieu.lean`. Terms of order `|z|⁵` are
  not part of the equation (a cubic truncation).

Source: first-order averaging of parametrically excited oscillators with cubic nonlinearity
(Nayfeh–Mook, *Nonlinear Oscillations*, Ch. 5, parametrically excited systems: the amplitude–phase
equations, the frequency–response curves and the jump phenomenon; Landau–Lifshitz, *Mechanics*
§27, §29: the instability tongue `(hω₀/4)² > (ε/2)² + λ²` and the limitation of the parametric
amplitude by the nonlinear frequency shift); the linear slow flow and its two unstable branches
(`Branches.slowFlow_unstable_iff`).

Sharpenings.
* Saturation of the parametric branch needs a resonant cubic term of the right sign: with pure
  nonlinear damping the branch born at the threshold is stable for `η > 0` (`supercritical`),
  and for `η < 0` every nontrivial state is unstable (`subcritical_damping`), so the cubic
  equation then predicts no saturated amplitude at all.
* With a pure frequency shift (`η = 0`, the Duffing case) the zero state and a stable locked
  state coexist below the linear threshold exactly on the side `Δβ > 0` (pump half-frequency
  moved towards the bent backbone), for `σ < |c| < √(σ² + Δ²)` (`shift_bistable`): the
  parametric threshold of the linear analysis is then not the onset of a sustained oscillation
  for finite disturbances (hysteresis).
* In the small-signal branch `σ < 0` with a weak pump `|c| < |Δ|` no phase-locked state exists
  under pure nonlinear damping (`damping_exists_iff`): the growth of an unlocked oscillation is
  not limited to a steady state of this equation.

Results.
* `ampField`, `ampSystem`, `toReal_ampField`, `hasDerivAt_ampSystem_iff` — the complex equation
  and its real two-state field (global solutions correspond); `ampSystem_contDiff`,
  `ampSystem_zero`, `norm_toReal`.
* `ampJacobian`, `hasFDerivAt_ampSystem`, `fderiv_ampSystem`, `ampJacobian_zero` — the Jacobian;
  at the zero state it is `slowFlowMatrix σ Δ c`.
* `trace_ampJacobian`, `det_ampJacobian` — trace `−2(σ + 2η|x|²)` everywhere; at a nontrivial
  steady state determinant `4|x|²(ησ − βΔ + (η² + β²)|x|²)`.
* `ampField_eq`, `exists_norm_sq_eq_iff`, `phaseLocked_iff`, `exists_ne_zero_iff` — the amplitude
  condition: some `a e^{jφ}` (`a > 0`) is a steady state iff
  `|(σ + ηa²) + j(Δ − βa²)| = |c|`, i.e. `(σ + ηa²)² + (Δ − βa²)² = |c|²`.
* `states_iff` — general case: `a² = (Δβ − ση ± √D)/(η² + β²)`,
  `D = (η² + β²)|c|² − (σβ + Δη)² ≥ 0`.
* `stable_iff`, `unstable_of_det`, `unstable_of_trace`, `detFactor_sq` — a nontrivial state is
  locally exponentially stable iff `σ + 2ηa² > 0` and `ησ − βΔ + (η² + β²)a² > 0`; the second
  factor is `±√D`: the lower root is a saddle.
* `zero_stable_iff`, `zero_unstable` — the zero state is exactly the linear (averaged) verdict:
  stable iff `σ > 0`, `|c|² < σ² + Δ²`; unstable on both branches of
  `Branches.slowFlow_unstable_iff`, whatever `η, β`.
* `damping_states`, `damping_exists_iff`, `damping_exists_iff_unstable`, `damping_stable_iff` —
  pure nonlinear damping `β = 0`: `a² = (±√(|c|² − Δ²) − σ)/η`; for `η > 0`, `σ ≥ 0` a
  nontrivial state exists iff the slow flow is unstable (the parametric branch).
* `supercritical`, `supercritical_below` — `η > 0`, `β = 0`, `σ ≥ 0`: above the threshold the
  zero state is unstable and every nontrivial state has `a² = (√(|c|² − Δ²) − σ)/η` and is stable;
  at or below it there is none.
* `coexistence_iff`, `subcritical_damping`, `threshold_branch` — the exact window of `|c|` in
  which a stable zero state and a locked state coexist:
  `|σβ + Δη|/√(η² + β²) ≤ |c| < √(σ² + Δ²)` with `ση < Δβ`; for `η < 0`, `β = 0` it is
  `|Δ| ≤ |c| < √(σ² + Δ²)` and all nontrivial states are unstable; at the threshold the branch
  has `(η² + β²)a² = 2(Δβ − ση)` (subcritical iff `Δβ > ση`).
* `shift_states`, `shift_exists_iff`, `shift_stable_iff`, `shift_bistable`, `shift_above`,
  `shift_below` — pure frequency shift `η = 0`: `a² = (Δ ± √(|c|² − σ²))/β`; stability iff
  `β(βa² − Δ) > 0`; bistability window `σ < |c| < √(σ² + Δ²)` for `Δβ > 0` with the stable state
  `a² = (|Δ| + s)/|β|` and the saddle `a² = (|Δ| − s)/|β|`, `s = √(|c|² − σ²)`; above the
  threshold a unique stable amplitude; none for `|c| < σ`.
-/

noncomputable section
namespace powerlib.ParametricResonance.Saturation

open Complex Matrix
open powerlib.Dynamics (State)
open powerlib.PhasePlane (mk norm_sq_eq)

/-! ## The model -/

/-- The cubic 2:1 amplitude field `z ↦ −(σ + jΔ) z + c z̄ + (−η + jβ)|z|² z`: the linear slow flow
`slowFlowField σ Δ c` plus the cubic resonant term. -/
def ampField (σ Δ : ℝ) (c : ℂ) (η β : ℝ) (z : ℂ) : ℂ :=
  slowFlowField σ Δ c z + (-(η : ℂ) + β * I) * ((‖z‖ ^ 2 : ℝ) : ℂ) * z

/-- The cubic amplitude field in the real coordinates `(x 0, x 1) = (Re z, Im z)`. -/
def ampSystem (σ Δ : ℝ) (c : ℂ) (η β : ℝ) (x : State 2) : State 2 :=
  mk ((-σ + c.re) * x 0 + (Δ + c.im) * x 1 - (η * x 0 + β * x 1) * (x 0 ^ 2 + x 1 ^ 2))
    ((-Δ + c.im) * x 0 + (-σ - c.re) * x 1 + (β * x 0 - η * x 1) * (x 0 ^ 2 + x 1 ^ 2))

/-- The Jacobian matrix of `ampSystem` at `x`. -/
def ampJacobian (σ Δ : ℝ) (c : ℂ) (η β : ℝ) (x : State 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-σ + c.re - η * (x 0 ^ 2 + x 1 ^ 2) - 2 * x 0 * (η * x 0 + β * x 1),
      Δ + c.im - β * (x 0 ^ 2 + x 1 ^ 2) - 2 * x 1 * (η * x 0 + β * x 1);
    -Δ + c.im + β * (x 0 ^ 2 + x 1 ^ 2) + 2 * x 0 * (β * x 0 - η * x 1),
      -σ - c.re - η * (x 0 ^ 2 + x 1 ^ 2) + 2 * x 1 * (β * x 0 - η * x 1)]

variable {σ Δ η β : ℝ} {c : ℂ}

@[tmio T, powerlib_foundation] theorem norm_toReal (z : ℂ) : ‖toReal z‖ = ‖z‖ :=
  Complex.orthonormalBasisOneI.repr.norm_map z

@[tmio M, powerlib_foundation] theorem toReal_ampField (σ Δ : ℝ) (c : ℂ) (η β : ℝ) (z : ℂ) :
    ampSystem σ Δ c η β (toReal z) = toReal (ampField σ Δ c η β z) := by
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  ext i
  fin_cases i
  · simp only [ampSystem, ampField, slowFlowField, PhasePlane.mk_apply_zero, toReal_apply_zero,
      toReal_apply_one, Fin.zero_eta, Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im,
      Complex.neg_im, Complex.conj_re, Complex.conj_im, hn]
    ring
  · simp only [ampSystem, ampField, slowFlowField, PhasePlane.mk_apply_one, toReal_apply_zero,
      toReal_apply_one, Fin.mk_one, Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im,
      Complex.neg_im, Complex.conj_re, Complex.conj_im, hn]
    ring

/-- Global solutions of the real field are exactly the real coordinates of global solutions of
the complex amplitude equation. -/
@[tmio M, powerlib_foundation] theorem hasDerivAt_ampSystem_iff (σ Δ : ℝ) (c : ℂ) (η β : ℝ)
    (z : ℝ → ℂ) :
    (∀ t, HasDerivAt (fun t => toReal (z t)) (ampSystem σ Δ c η β (toReal (z t))) t) ↔
      ∀ t, HasDerivAt z (ampField σ Δ c η β (z t)) t := by
  refine forall_congr' fun t => ?_
  rw [toReal_ampField]
  constructor
  · intro h
    have h' := toReal.symm.hasFDerivAt.comp_hasDerivAt t h
    simpa [Function.comp_def] using h'
  · intro h
    exact toReal.hasFDerivAt.comp_hasDerivAt t h

@[tmio M, powerlib_foundation] theorem ampSystem_contDiff (σ Δ : ℝ) (c : ℂ) (η β : ℝ)
    {k : WithTop ℕ∞} : ContDiff ℝ k (ampSystem σ Δ c η β) := by
  refine contDiff_euclidean.2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;>
    (simp only [ampSystem, PhasePlane.mk_apply_zero, PhasePlane.mk_apply_one]; fun_prop)

@[tmio M, powerlib_foundation] theorem ampSystem_zero (σ Δ : ℝ) (c : ℂ) (η β : ℝ) :
    ampSystem σ Δ c η β 0 = 0 := by
  rw [ampSystem, PhasePlane.mk_eq_zero_iff]; simp

@[tmio M, powerlib_foundation] theorem hasFDerivAt_ampSystem (σ Δ : ℝ) (c : ℂ) (η β : ℝ)
    (x : State 2) :
    HasFDerivAt (ampSystem σ Δ c η β)
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (ampJacobian σ Δ c η β x)) x := by
  have h0 := Dynamics.hasFDerivAt_coord 0 x
  have h1 := Dynamics.hasFDerivAt_coord 1 x
  have hρ : HasFDerivAt (fun y : State 2 => y 0 ^ 2 + y 1 ^ 2) _ x := (h0.pow 2).add (h1.pow 2)
  have hF0 : HasFDerivAt (fun y : State 2 =>
      (-σ + c.re) * y 0 + (Δ + c.im) * y 1 - (η * y 0 + β * y 1) * (y 0 ^ 2 + y 1 ^ 2)) _ x :=
    ((h0.const_mul (-σ + c.re)).add (h1.const_mul (Δ + c.im))).sub
      (((h0.const_mul η).add (h1.const_mul β)).mul hρ)
  have hF1 : HasFDerivAt (fun y : State 2 =>
      (-Δ + c.im) * y 0 + (-σ - c.re) * y 1 + (β * y 0 - η * y 1) * (y 0 ^ 2 + y 1 ^ 2)) _ x :=
    ((h0.const_mul (-Δ + c.im)).add (h1.const_mul (-σ - c.re))).add
      (((h0.const_mul β).sub (h1.const_mul η)).mul hρ)
  have e0 : (fun y => ampSystem σ Δ c η β y 0) = fun y : State 2 =>
      (-σ + c.re) * y 0 + (Δ + c.im) * y 1 - (η * y 0 + β * y 1) * (y 0 ^ 2 + y 1 ^ 2) :=
    funext fun _ => rfl
  have e1 : (fun y => ampSystem σ Δ c η β y 1) = fun y : State 2 =>
      (-Δ + c.im) * y 0 + (-σ - c.re) * y 1 + (β * y 0 - η * y 1) * (y 0 ^ 2 + y 1 ^ 2) :=
    funext fun _ => rfl
  refine Dynamics.hasFDerivAt_toEuclideanCLM_of_components _
    (fun i => fderiv ℝ (fun y => ampSystem σ Δ c η β y i) x) (fun i => ?_) ?_
  · fin_cases i
    · show HasFDerivAt (fun y => ampSystem σ Δ c η β y 0) _ x
      rw [e0]; exact hF0.differentiableAt.hasFDerivAt
    · show HasFDerivAt (fun y => ampSystem σ Δ c η β y 1) _ x
      rw [e1]; exact hF1.differentiableAt.hasFDerivAt
  · intro i v
    rw [Fin.sum_univ_two]
    fin_cases i
    · show fderiv ℝ (fun y => ampSystem σ Δ c η β y 0) x v = _
      rw [e0, hF0.fderiv]
      simp [ampJacobian]
      ring
    · show fderiv ℝ (fun y => ampSystem σ Δ c η β y 1) x v = _
      rw [e1, hF1.fderiv]
      simp [ampJacobian]
      ring

@[tmio M, powerlib_foundation] theorem fderiv_ampSystem (σ Δ : ℝ) (c : ℂ) (η β : ℝ)
    (x : State 2) :
    fderiv ℝ (ampSystem σ Δ c η β) x =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (ampJacobian σ Δ c η β x) :=
  (hasFDerivAt_ampSystem σ Δ c η β x).fderiv

/-- At the zero state the Jacobian is the linear slow flow: the cubic term does not change the
linearization. -/
@[tmio M, powerlib_foundation] theorem ampJacobian_zero (σ Δ : ℝ) (c : ℂ) (η β : ℝ) :
    ampJacobian σ Δ c η β 0 = slowFlowMatrix σ Δ c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ampJacobian, slowFlowMatrix]

@[tmio M, powerlib_foundation] theorem trace_ampJacobian (σ Δ : ℝ) (c : ℂ) (η β : ℝ)
    (x : State 2) : (ampJacobian σ Δ c η β x).trace = -2 * (σ + 2 * η * ‖x‖ ^ 2) := by
  rw [norm_sq_eq]; simp [ampJacobian, Matrix.trace_fin_two]; ring

/-- At a nontrivial equilibrium `x` the determinant of the Jacobian is
`4|x|² (ησ − βΔ + (η² + β²)|x|²)`. -/
@[tmio M, powerlib_foundation] theorem det_ampJacobian {x : State 2}
    (hx : ampSystem σ Δ c η β x = 0) (hx0 : x ≠ 0) :
    (ampJacobian σ Δ c η β x).det =
      4 * ‖x‖ ^ 2 * (η * σ - β * Δ + (η ^ 2 + β ^ 2) * ‖x‖ ^ 2) := by
  have hρ : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := by
    rw [← norm_sq_eq]; exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hx0)
  have h0 : (-σ + c.re) * x 0 + (Δ + c.im) * x 1 - (η * x 0 + β * x 1) * (x 0 ^ 2 + x 1 ^ 2) = 0 :=
    congrArg (fun y : State 2 => y 0) hx
  have h1 : (-Δ + c.im) * x 0 + (-σ - c.re) * x 1 + (β * x 0 - η * x 1) * (x 0 ^ 2 + x 1 ^ 2) = 0 :=
    congrArg (fun y : State 2 => y 1) hx
  rw [norm_sq_eq]
  apply mul_left_cancel₀ hρ
  rw [Matrix.det_fin_two]
  simp only [ampJacobian, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  linear_combination
    (-((-σ + c.re) * x 0 + (Δ + c.im) * x 1 - (η * x 0 + β * x 1) * (x 0 ^ 2 + x 1 ^ 2) +
      2 * (σ * x 0 - Δ * x 1))) * h0 +
    (-((-Δ + c.im) * x 0 + (-σ - c.re) * x 1 + (β * x 0 - η * x 1) * (x 0 ^ 2 + x 1 ^ 2) +
      2 * (Δ * x 0 + σ * x 1))) * h1


/-! ## Phase-locked states and the amplitude condition -/

/-- The amplitude field as `c z̄ − K z` with `K = (σ + η|z|²) + j(Δ − β|z|²)`. -/
@[tmio M, powerlib_foundation] theorem ampField_eq (σ Δ : ℝ) (c : ℂ) (η β : ℝ) (z : ℂ) :
    ampField σ Δ c η β z = c * (starRingEnd ℂ) z -
      (((σ + η * ‖z‖ ^ 2 : ℝ) : ℂ) + ((Δ - β * ‖z‖ ^ 2 : ℝ) : ℂ) * I) * z := by
  simp only [ampField, slowFlowField]; push_cast; ring

/-- **The amplitude condition.** For `A > 0` there is a steady state of the amplitude equation
with `|z|² = A` iff `(σ + ηA)² + (Δ − βA)² = |c|²`, i.e.
`|(σ + ηA) + j(Δ − βA)| = |c|`. -/
@[tmio M, powerlib_foundation] theorem exists_norm_sq_eq_iff {A : ℝ} (hA : 0 < A) :
    (∃ z : ℂ, ‖z‖ ^ 2 = A ∧ ampField σ Δ c η β z = 0) ↔
      (σ + η * A) ^ 2 + (Δ - β * A) ^ 2 = ‖c‖ ^ 2 := by
  set K : ℂ := ((σ + η * A : ℝ) : ℂ) + ((Δ - β * A : ℝ) : ℂ) * I with hK
  have hKn : ‖K‖ ^ 2 = (σ + η * A) ^ 2 + (Δ - β * A) ^ 2 := by
    rw [Complex.sq_norm, hK, Complex.normSq_add_mul_I]
  rw [← hKn]
  constructor
  · rintro ⟨z, hz, h0⟩
    rw [ampField_eq, hz, sub_eq_zero] at h0
    have hz0 : 0 < ‖z‖ := by
      rcases (norm_nonneg z).lt_or_eq with h | h
      · exact h
      · rw [← h] at hz; simp at hz; linarith
    have := congrArg norm h0
    rw [norm_mul, norm_mul, Complex.norm_conj] at this
    have h' : ‖K‖ = ‖c‖ := (mul_right_cancel₀ hz0.ne' this).symm
    rw [h']
  · intro hn
    have hn' : ‖K‖ = ‖c‖ := by
      have := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hn
      exact this
    set a := √A with ha
    have ha0 : 0 < a := Real.sqrt_pos.mpr hA
    have haA : a ^ 2 = A := Real.sq_sqrt hA.le
    by_cases hK0 : K = 0
    · have hc0 : c = 0 := by
        rw [hK0, norm_zero] at hn'; exact norm_eq_zero.mp hn'.symm
      refine ⟨(a : ℂ), by rw [Complex.norm_real, Real.norm_of_nonneg ha0.le, haA], ?_⟩
      rw [ampField_eq, hc0]
      rw [show ‖(a : ℂ)‖ ^ 2 = A by rw [Complex.norm_real, Real.norm_of_nonneg ha0.le, haA]]
      rw [← hK, hK0]; ring
    · obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (c / K) two_pos
      have hu1 : ‖u‖ = 1 := by
        have h2 : ‖u‖ ^ 2 = 1 := by
          rw [← norm_pow, hu, norm_div, hn', div_self]
          rw [← hn']; exact norm_ne_zero_iff.mpr hK0
        exact (pow_eq_one_iff_of_nonneg (norm_nonneg u) two_ne_zero).mp h2
      have hzn : ‖(a : ℂ) * u‖ ^ 2 = A := by
        rw [norm_mul, hu1, mul_one, Complex.norm_real, Real.norm_of_nonneg ha0.le, haA]
      refine ⟨(a : ℂ) * u, hzn, ?_⟩
      rw [ampField_eq, hzn, ← hK, sub_eq_zero]
      have huu : u * (starRingEnd ℂ) u = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu1]; simp
      have hKu : K * u ^ 2 = c := by rw [hu]; field_simp
      rw [map_mul, Complex.conj_ofReal]
      linear_combination (-(a : ℂ) * (starRingEnd ℂ) u) * hKu + (a : ℂ) * K * u * huu

/-- **Phase-locked states `z = a e^{jφ}`.** For `a > 0` some phase `φ` makes `a e^{jφ}` a
steady state of the amplitude equation iff `|(σ + ηa²) + j(Δ − βa²)| = |c|`. -/
@[tmio M, powerlib_foundation] theorem phaseLocked_iff {a : ℝ} (ha : 0 < a) :
    (∃ φ : ℝ, ampField σ Δ c η β (a * Complex.exp (φ * I)) = 0) ↔
      ‖((σ + η * a ^ 2 : ℝ) : ℂ) + ((Δ - β * a ^ 2 : ℝ) : ℂ) * I‖ = ‖c‖ := by
  have hn : ‖((σ + η * a ^ 2 : ℝ) : ℂ) + ((Δ - β * a ^ 2 : ℝ) : ℂ) * I‖ ^ 2 =
      (σ + η * a ^ 2) ^ 2 + (Δ - β * a ^ 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), hn,
    ← exists_norm_sq_eq_iff (pow_pos ha 2)]
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨_, ?_, hφ⟩
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg ha.le]
  · rintro ⟨z, hz, h0⟩
    have hza : ‖z‖ = a := by
      have := (sq_eq_sq₀ (norm_nonneg z) ha.le).mp hz
      exact this
    refine ⟨Complex.arg z, ?_⟩
    rw [← hza, Complex.norm_mul_exp_arg_mul_I]
    exact h0

/-- Nontrivial steady states exist iff the amplitude condition has a positive root `A = a²`. -/
@[tmio M, powerlib_foundation] theorem exists_ne_zero_iff :
    (∃ z : ℂ, z ≠ 0 ∧ ampField σ Δ c η β z = 0) ↔
      ∃ A : ℝ, 0 < A ∧ (σ + η * A) ^ 2 + (Δ - β * A) ^ 2 = ‖c‖ ^ 2 := by
  constructor
  · rintro ⟨z, hz0, h⟩
    have hA : 0 < ‖z‖ ^ 2 := by positivity
    exact ⟨_, hA, (exists_norm_sq_eq_iff hA).mp ⟨z, rfl, h⟩⟩
  · rintro ⟨A, hA, h⟩
    obtain ⟨z, hz, h0⟩ := (exists_norm_sq_eq_iff hA).mpr h
    refine ⟨z, fun hz0 => ?_, h0⟩
    rw [hz0, norm_zero] at hz
    linarith [pow_pos (zero_lt_two : (0:ℝ) < 2) 0, hz]


/-- **The amplitudes in the general case: the roots of a quadratic in `a²`.** For `η² + β² > 0`
there is a steady state with `|z|² = A > 0` iff `D = (η² + β²)|c|² − (σβ + Δη)² ≥ 0` and
`A = (Δβ − ση ± √D) / (η² + β²)`. -/
@[tmio M, powerlib_foundation] theorem states_iff (hS : 0 < η ^ 2 + β ^ 2) {A : ℝ}
    (hA : 0 < A) :
    (∃ z : ℂ, ‖z‖ ^ 2 = A ∧ ampField σ Δ c η β z = 0) ↔
      0 ≤ (η ^ 2 + β ^ 2) * ‖c‖ ^ 2 - (σ * β + Δ * η) ^ 2 ∧
        (A = (Δ * β - σ * η + √((η ^ 2 + β ^ 2) * ‖c‖ ^ 2 - (σ * β + Δ * η) ^ 2)) /
            (η ^ 2 + β ^ 2) ∨
          A = (Δ * β - σ * η - √((η ^ 2 + β ^ 2) * ‖c‖ ^ 2 - (σ * β + Δ * η) ^ 2)) /
            (η ^ 2 + β ^ 2)) := by
  rw [exists_norm_sq_eq_iff hA]
  set S := η ^ 2 + β ^ 2 with hSdef
  set D := S * ‖c‖ ^ 2 - (σ * β + Δ * η) ^ 2 with hD
  have key : S * ((σ + η * A) ^ 2 + (Δ - β * A) ^ 2 - ‖c‖ ^ 2) =
      (S * A + σ * η - Δ * β) ^ 2 - D := by rw [hD, hSdef]; ring
  rw [eq_div_iff hS.ne', eq_div_iff hS.ne']
  constructor
  · intro h
    have hsq : (S * A + σ * η - Δ * β) ^ 2 = D := by
      have := key; rw [h, sub_self, mul_zero] at this; linarith
    have hD0 : 0 ≤ D := hsq ▸ sq_nonneg _
    refine ⟨hD0, ?_⟩
    have : (S * A + σ * η - Δ * β) ^ 2 = √D ^ 2 := by rw [Real.sq_sqrt hD0, hsq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with h1 | h1
    · left; linarith
    · right; linarith
  · rintro ⟨hD0, h1⟩
    have hsq : (S * A + σ * η - Δ * β) ^ 2 = D := by
      rcases h1 with h1 | h1
      · rw [show S * A + σ * η - Δ * β = √D by linarith, Real.sq_sqrt hD0]
      · rw [show S * A + σ * η - Δ * β = -√D by linarith, neg_sq, Real.sq_sqrt hD0]
    have h2 : S * ((σ + η * A) ^ 2 + (Δ - β * A) ^ 2 - ‖c‖ ^ 2) = 0 := by rw [key, hsq, sub_self]
    have := (mul_eq_zero.mp h2).resolve_left hS.ne'
    linarith

/-! ## Stability of the nontrivial states -/

@[tmio M, powerlib_foundation] private theorem toReal_eq_zero {z : ℂ}
    (hz : ampField σ Δ c η β z = 0) : ampSystem σ Δ c η β (toReal z) = 0 := by
  rw [toReal_ampField, hz, map_zero]

@[tmio T, powerlib_foundation] private theorem toReal_ne_zero {z : ℂ} (hz0 : z ≠ 0) :
    toReal z ≠ 0 := by
  rwa [Ne, ContinuousLinearEquiv.map_eq_zero_iff]

/-- **Stability of a nontrivial steady state** (trace `−2(σ + 2η|z|²)`, determinant
`4|z|²(ησ − βΔ + (η² + β²)|z|²)` of the Jacobian, `trace_ampJacobian`, `det_ampJacobian`): a
steady state `z ≠ 0` is locally exponentially stable iff `σ + 2η|z|² > 0` and
`ησ − βΔ + (η² + β²)|z|² > 0`. -/
@[tmio TM, powerlib_foundation] theorem stable_iff {z : ℂ} (hz : ampField σ Δ c η β z = 0)
    (hz0 : z ≠ 0) :
    LocallyExponentiallyStable (ampSystem σ Δ c η β) (toReal z) ↔
      0 < σ + 2 * η * ‖z‖ ^ 2 ∧ 0 < η * σ - β * Δ + (η ^ 2 + β ^ 2) * ‖z‖ ^ 2 := by
  have hx := toReal_eq_zero hz
  rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_of_eq _ (ampSystem_contDiff σ Δ c η β) hx
    (fderiv_ampSystem σ Δ c η β _), Criteria.isHurwitz_fin_two_iff, trace_ampJacobian,
    det_ampJacobian hx (toReal_ne_zero hz0), norm_toReal]
  have hp : 0 < 4 * ‖z‖ ^ 2 := by positivity
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, pos_of_mul_pos_right h2 hp.le⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, mul_pos hp h2⟩

/-- A nontrivial steady state with `ησ − βΔ + (η² + β²)|z|² < 0` is a saddle, hence unstable. -/
@[tmio TM, powerlib_foundation] theorem unstable_of_det {z : ℂ} (hz : ampField σ Δ c η β z = 0)
    (hz0 : z ≠ 0) (h : η * σ - β * Δ + (η ^ 2 + β ^ 2) * ‖z‖ ^ 2 < 0) :
    Unstable (ampSystem σ Δ c η β) (toReal z) := by
  have hx := toReal_eq_zero hz
  refine Criteria.unstable_of_jacobian_det _ (ampSystem_contDiff σ Δ c η β) hx
    (fderiv_ampSystem σ Δ c η β _) ?_
  rw [det_ampJacobian hx (toReal_ne_zero hz0), norm_toReal]
  have hp : 0 < 4 * ‖z‖ ^ 2 := by positivity
  have := mul_neg_of_pos_of_neg hp h
  norm_num
  linarith

/-- A nontrivial steady state with `σ + 2η|z|² < 0` (positive trace) is unstable. -/
@[tmio TM, powerlib_foundation] theorem unstable_of_trace {z : ℂ}
    (hz : ampField σ Δ c η β z = 0) (h : σ + 2 * η * ‖z‖ ^ 2 < 0) :
    Unstable (ampSystem σ Δ c η β) (toReal z) :=
  Criteria.unstable_of_jacobian_trace_pos _ (ampSystem_contDiff σ Δ c η β) (toReal_eq_zero hz)
    (fderiv_ampSystem σ Δ c η β _) (by rw [trace_ampJacobian, norm_toReal]; linarith)

/-- **Upper and lower branch.** At a nontrivial steady state the determinant factor is a square
root of the discriminant: `(ησ − βΔ + (η² + β²)|z|²)² = (η² + β²)|c|² − (σβ + Δη)²`. The upper
root `A₊` of `states_iff` has the factor `+√D`, the lower root `A₋` the factor `−√D`: for `D > 0`
the lower state is always a saddle, the upper one is stable iff `σ + 2ηA₊ > 0`. -/
@[tmio M, powerlib_foundation] theorem detFactor_sq {z : ℂ} (hz : ampField σ Δ c η β z = 0)
    (hz0 : z ≠ 0) :
    (η * σ - β * Δ + (η ^ 2 + β ^ 2) * ‖z‖ ^ 2) ^ 2 =
      (η ^ 2 + β ^ 2) * ‖c‖ ^ 2 - (σ * β + Δ * η) ^ 2 := by
  have h := (exists_norm_sq_eq_iff (by positivity : 0 < ‖z‖ ^ 2)).mp ⟨z, rfl, hz⟩
  linear_combination (η ^ 2 + β ^ 2) * h

/-! ## The zero state: the linear (averaged) verdict -/

/-- The zero state is locally exponentially stable iff the slow flow is Hurwitz:
`σ > 0` and `|c|² < σ² + Δ²` (its Jacobian is `slowFlowMatrix σ Δ c`, `ampJacobian_zero`). -/
@[tmio TM, powerlib_foundation] theorem zero_stable_iff :
    LocallyExponentiallyStable (ampSystem σ Δ c η β) 0 ↔ 0 < σ ∧ ‖c‖ ^ 2 < σ ^ 2 + Δ ^ 2 := by
  rw [Dynamics.locallyExponentiallyStable_iff_isHurwitz_of_eq (slowFlowMatrix σ Δ c)
    (ampSystem_contDiff σ Δ c η β) (ampSystem_zero σ Δ c η β)
    (by rw [fderiv_ampSystem, ampJacobian_zero]), Criteria.isHurwitz_fin_two_iff,
    trace_slowFlowMatrix, det_slowFlowMatrix]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **The zero state is unstable on both unstable branches of the slow flow**
(`Branches.slowFlow_unstable_iff`: small-signal `σ < 0`, parametric `σ ≥ 0`, `σ² + Δ² < |c|²`),
whatever the cubic coefficients. -/
@[tmio TM, powerlib_foundation] theorem zero_unstable
    (h : Xor (σ < 0) (0 ≤ σ ∧ σ ^ 2 + Δ ^ 2 < ‖c‖ ^ 2)) :
    Unstable (ampSystem σ Δ c η β) 0 := by
  obtain ⟨μ, hμ, hre⟩ := (Branches.slowFlow_unstable_iff σ Δ c).mpr h
  exact Dynamics.unstable_of_characteristic_root_re_pos (slowFlowMatrix σ Δ c)
    (ampSystem_contDiff σ Δ c η β) (ampSystem_zero σ Δ c η β)
    (by rw [fderiv_ampSystem, ampJacobian_zero]) hμ hre


/-! ## Pure nonlinear damping (`β = 0`): the supercritical and subcritical branch -/

/-- **Amplitudes under pure nonlinear damping.** With `β = 0`, `η ≠ 0`, a steady state with
`|z|² = A > 0` exists iff `Δ² ≤ |c|²` and `A = (±√(|c|² − Δ²) − σ)/η`. -/
@[tmio M, powerlib_foundation] theorem damping_states (hη : η ≠ 0) {A : ℝ} (hA : 0 < A) :
    (∃ z : ℂ, ‖z‖ ^ 2 = A ∧ ampField σ Δ c η 0 z = 0) ↔
      Δ ^ 2 ≤ ‖c‖ ^ 2 ∧
        (A = (√(‖c‖ ^ 2 - Δ ^ 2) - σ) / η ∨ A = (-√(‖c‖ ^ 2 - Δ ^ 2) - σ) / η) := by
  rw [exists_norm_sq_eq_iff hA, eq_div_iff hη, eq_div_iff hη]
  simp only [zero_mul, sub_zero]
  constructor
  · intro h
    have hD : Δ ^ 2 ≤ ‖c‖ ^ 2 := by nlinarith [sq_nonneg (σ + η * A)]
    refine ⟨hD, ?_⟩
    have hs : (σ + η * A) ^ 2 = √(‖c‖ ^ 2 - Δ ^ 2) ^ 2 := by
      rw [Real.sq_sqrt (by linarith)]; linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h1 | h1
    · left; linarith
    · right; linarith
  · rintro ⟨hD, h1 | h1⟩
    · rw [show σ + η * A = √(‖c‖ ^ 2 - Δ ^ 2) by linarith, Real.sq_sqrt (by linarith)]; ring
    · rw [show σ + η * A = -√(‖c‖ ^ 2 - Δ ^ 2) by linarith, neg_sq, Real.sq_sqrt (by linarith)]
      ring

/-- **Existence under pure nonlinear damping** (`β = 0`, `η > 0`): a nontrivial steady state
exists iff `Δ² ≤ |c|²` and `σ < √(|c|² − Δ²)`. -/
@[tmio M, powerlib_foundation] theorem damping_exists_iff (hη : 0 < η) :
    (∃ z : ℂ, z ≠ 0 ∧ ampField σ Δ c η 0 z = 0) ↔
      Δ ^ 2 ≤ ‖c‖ ^ 2 ∧ σ < √(‖c‖ ^ 2 - Δ ^ 2) := by
  rw [exists_ne_zero_iff]
  simp only [zero_mul, sub_zero]
  constructor
  · rintro ⟨A, hA, h⟩
    have hD : Δ ^ 2 ≤ ‖c‖ ^ 2 := by nlinarith [sq_nonneg (σ + η * A)]
    refine ⟨hD, ?_⟩
    have h1 : |σ + η * A| ≤ √(‖c‖ ^ 2 - Δ ^ 2) := Real.abs_le_sqrt (by linarith)
    have h2 := le_abs_self (σ + η * A)
    nlinarith
  · rintro ⟨hD, hσ⟩
    refine ⟨(√(‖c‖ ^ 2 - Δ ^ 2) - σ) / η, div_pos (by linarith) hη, ?_⟩
    rw [show σ + η * ((√(‖c‖ ^ 2 - Δ ^ 2) - σ) / η) = √(‖c‖ ^ 2 - Δ ^ 2) by field_simp; ring,
      Real.sq_sqrt (by linarith)]
    ring

/-- **Saturation exists exactly on the linear parametric branch.** With pure nonlinear damping
(`β = 0`, `η > 0`) and `σ ≥ 0`, a nontrivial steady state exists iff the zero state's slow flow
has an exponent with `Re λ > 0` (`Branches.slowFlow_unstable_iff`: here the parametric branch
`σ² + Δ² < |c|²`). -/
@[tmio M, powerlib_foundation] theorem damping_exists_iff_unstable (hη : 0 < η) (hσ : 0 ≤ σ) :
    (∃ z : ℂ, z ≠ 0 ∧ ampField σ Δ c η 0 z = 0) ↔
      ∃ μ : ℂ, (Linear.characteristicMatrix (slowFlowMatrix σ Δ c) μ).det = 0 ∧ 0 < μ.re := by
  rw [damping_exists_iff hη, Branches.slowFlow_unstable_iff]
  have hn : ¬ σ < 0 := not_lt.mpr hσ
  simp only [Xor, hn, false_and, false_or, not_false_eq_true, and_true]
  constructor
  · rintro ⟨hD, h⟩
    refine ⟨hσ, ?_⟩
    have := (Real.lt_sqrt hσ).mp h
    linarith
  · rintro ⟨-, h⟩
    refine ⟨by nlinarith [sq_nonneg σ], (Real.lt_sqrt hσ).mpr (by linarith)⟩

/-- Pure nonlinear damping, `η > 0`: a nontrivial steady state is locally exponentially stable
iff `σ + η|z|² > 0` (the upper root `η|z|² = √(|c|² − Δ²) − σ` with `|c|² > Δ²`). -/
@[tmio TM, powerlib_foundation] theorem damping_stable_iff (hη : 0 < η) {z : ℂ}
    (hz : ampField σ Δ c η 0 z = 0) (hz0 : z ≠ 0) :
    LocallyExponentiallyStable (ampSystem σ Δ c η 0) (toReal z) ↔ 0 < σ + η * ‖z‖ ^ 2 := by
  rw [stable_iff hz hz0]
  have hA : 0 < ‖z‖ ^ 2 := by positivity
  constructor
  · rintro ⟨-, h2⟩
    have : η * σ - 0 * Δ + (η ^ 2 + 0 ^ 2) * ‖z‖ ^ 2 = η * (σ + η * ‖z‖ ^ 2) := by ring
    rw [this] at h2
    exact pos_of_mul_pos_right h2 hη.le
  · intro h
    refine ⟨by nlinarith, ?_⟩
    have : η * σ - 0 * Δ + (η ^ 2 + 0 ^ 2) * ‖z‖ ^ 2 = η * (σ + η * ‖z‖ ^ 2) := by ring
    rw [this]
    exact mul_pos hη h

/-- **Supercritical saturation** (`η > 0`, `β = 0`, `σ ≥ 0`). Above the linear threshold
(`σ² + Δ² < |c|²`) the zero state is unstable, a phase-locked state exists, and every
nontrivial steady state has the saturated amplitude `a² = (√(|c|² − Δ²) − σ)/η` and is locally
exponentially stable. -/
@[tmio TM, powerlib_foundation] theorem supercritical (hη : 0 < η) (hσ : 0 ≤ σ)
    (hc : σ ^ 2 + Δ ^ 2 < ‖c‖ ^ 2) :
    Unstable (ampSystem σ Δ c η 0) 0 ∧ (∃ z : ℂ, z ≠ 0 ∧ ampField σ Δ c η 0 z = 0) ∧
      ∀ z : ℂ, z ≠ 0 → ampField σ Δ c η 0 z = 0 →
        ‖z‖ ^ 2 = (√(‖c‖ ^ 2 - Δ ^ 2) - σ) / η ∧
          LocallyExponentiallyStable (ampSystem σ Δ c η 0) (toReal z) := by
  have hr : σ < √(‖c‖ ^ 2 - Δ ^ 2) := (Real.lt_sqrt hσ).mpr (by linarith)
  refine ⟨zero_unstable (Or.inr ⟨⟨hσ, hc⟩, not_lt.mpr hσ⟩),
    (damping_exists_iff hη).mpr ⟨by nlinarith [sq_nonneg σ], hr⟩, fun z hz0 hz => ?_⟩
  have hA : 0 < ‖z‖ ^ 2 := by positivity
  obtain ⟨-, h | h⟩ := (damping_states hη.ne' hA).mp ⟨z, rfl, hz⟩
  · refine ⟨h, (damping_stable_iff hη hz hz0).mpr ?_⟩
    rw [h, show σ + η * ((√(‖c‖ ^ 2 - Δ ^ 2) - σ) / η) = √(‖c‖ ^ 2 - Δ ^ 2) by field_simp; ring]
    linarith
  · exfalso
    rw [h] at hA
    have := Real.sqrt_nonneg (‖c‖ ^ 2 - Δ ^ 2)
    have : (-√(‖c‖ ^ 2 - Δ ^ 2) - σ) / η ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le
    linarith

/-- **No saturated state below the threshold** (`η > 0`, `β = 0`, `σ ≥ 0`,
`|c|² ≤ σ² + Δ²`): the only steady state is `z = 0`, so the branch is born at the linear
threshold. -/
@[tmio M, powerlib_foundation] theorem supercritical_below (hη : 0 < η) (hσ : 0 ≤ σ)
    (hc : ‖c‖ ^ 2 ≤ σ ^ 2 + Δ ^ 2) {z : ℂ} (hz : ampField σ Δ c η 0 z = 0) : z = 0 := by
  by_contra hz0
  obtain ⟨-, h⟩ := (damping_exists_iff hη).mp ⟨z, hz0, hz⟩
  have := (Real.lt_sqrt hσ).mp h
  linarith

/-! ## Coexistence below the threshold (subcritical case) -/

/-- **Coexistence of a stable zero state and a phase-locked state.** For `η² + β² > 0` the zero
state is locally exponentially stable while a nontrivial steady state exists iff `σ > 0`,
`ση < Δβ` (the branch bends back below the threshold) and
`|σβ + Δη| / √(η² + β²) ≤ |c| < √(σ² + Δ²)`, written
`(σβ + Δη)² ≤ (η² + β²)|c|²` and `|c|² < σ² + Δ²`. -/
@[tmio TM, powerlib_foundation] theorem coexistence_iff (hS : 0 < η ^ 2 + β ^ 2) :
    (LocallyExponentiallyStable (ampSystem σ Δ c η β) 0 ∧
        ∃ z : ℂ, z ≠ 0 ∧ ampField σ Δ c η β z = 0) ↔
      0 < σ ∧ ‖c‖ ^ 2 < σ ^ 2 + Δ ^ 2 ∧ σ * η < Δ * β ∧
        (σ * β + Δ * η) ^ 2 ≤ (η ^ 2 + β ^ 2) * ‖c‖ ^ 2 := by
  rw [zero_stable_iff, exists_ne_zero_iff]
  constructor
  · rintro ⟨⟨hσ, hc⟩, A, hA, h⟩
    refine ⟨hσ, hc, ?_, ?_⟩
    · nlinarith [sq_nonneg (η * A), sq_nonneg (β * A)]
    · nlinarith [sq_nonneg ((η ^ 2 + β ^ 2) * A + σ * η - Δ * β)]
  · rintro ⟨hσ, hc, hB, hD⟩
    refine ⟨⟨hσ, hc⟩, ?_⟩
    set D := (η ^ 2 + β ^ 2) * ‖c‖ ^ 2 - (σ * β + Δ * η) ^ 2 with hDdef
    have hD0 : 0 ≤ D := by linarith
    have hA : 0 < (Δ * β - σ * η + √D) / (η ^ 2 + β ^ 2) :=
      div_pos (by have := Real.sqrt_nonneg D; linarith) hS
    refine ⟨_, hA, ?_⟩
    obtain ⟨z, hz, h0⟩ := (states_iff hS hA).mpr ⟨hD0, Or.inl rfl⟩
    exact (exists_norm_sq_eq_iff hA).mp ⟨z, hz, h0⟩

/-- **Subcritical nonlinear damping** (`η < 0`, `β = 0`). The zero state is stable while
nontrivial steady states exist iff `σ > 0` and `|Δ| ≤ |c| < √(σ² + Δ²)` (below the linear
threshold); and every nontrivial steady state is unstable: without a frequency nonlinearity
the cubic term cannot saturate the growth. -/
@[tmio TM, powerlib_foundation] theorem subcritical_damping (hη : η < 0) :
    ((LocallyExponentiallyStable (ampSystem σ Δ c η 0) 0 ∧
        ∃ z : ℂ, z ≠ 0 ∧ ampField σ Δ c η 0 z = 0) ↔
      0 < σ ∧ Δ ^ 2 ≤ ‖c‖ ^ 2 ∧ ‖c‖ ^ 2 < σ ^ 2 + Δ ^ 2) ∧
    ∀ z : ℂ, z ≠ 0 → ampField σ Δ c η 0 z = 0 → Unstable (ampSystem σ Δ c η 0) (toReal z) := by
  have hS : 0 < η ^ 2 + 0 ^ 2 := by nlinarith
  refine ⟨?_, fun z hz0 hz => ?_⟩
  · rw [coexistence_iff hS]
    simp only [mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero]
    constructor
    · rintro ⟨hσ, hc, -, hD⟩
      exact ⟨hσ, by nlinarith [sq_nonneg η], hc⟩
    · rintro ⟨hσ, hD, hc⟩
      exact ⟨hσ, hc, by nlinarith, by nlinarith [sq_nonneg η]⟩
  · have hA : 0 < ‖z‖ ^ 2 := by positivity
    by_cases hu : 0 < σ + η * ‖z‖ ^ 2
    · exact unstable_of_det hz hz0 (by nlinarith)
    · exact unstable_of_trace hz (by nlinarith)

/-- **The direction of the branch at the threshold.** At the linear threshold
`|c|² = σ² + Δ²` a steady state with `|z|² = A > 0` exists iff
`(η² + β²) A = 2(Δβ − ση)`: the nontrivial branch leaves the threshold into the stable region of
the zero state (subcritical, hysteresis) iff `Δβ > ση`, into its unstable region
(supercritical) iff `Δβ < ση`. -/
@[tmio M, powerlib_foundation] theorem threshold_branch (hc : ‖c‖ ^ 2 = σ ^ 2 + Δ ^ 2)
    {A : ℝ} (hA : 0 < A) :
    (∃ z : ℂ, ‖z‖ ^ 2 = A ∧ ampField σ Δ c η β z = 0) ↔
      (η ^ 2 + β ^ 2) * A = 2 * (Δ * β - σ * η) := by
  rw [exists_norm_sq_eq_iff hA, hc]
  constructor
  · intro h
    have : A * ((η ^ 2 + β ^ 2) * A - 2 * (Δ * β - σ * η)) = 0 := by linear_combination h
    linarith [(mul_eq_zero.mp this).resolve_left hA.ne']
  · intro h
    linear_combination A * h

/-! ## Pure frequency-shift nonlinearity (`η = 0`): the Duffing case and hysteresis -/

/-- **Amplitudes under a pure frequency shift.** With `η = 0`, `β ≠ 0`, a steady state with
`|z|² = A > 0` exists iff `σ² ≤ |c|²` and `A = (Δ ± √(|c|² − σ²))/β`. -/
@[tmio M, powerlib_foundation] theorem shift_states (hβ : β ≠ 0) {A : ℝ} (hA : 0 < A) :
    (∃ z : ℂ, ‖z‖ ^ 2 = A ∧ ampField σ Δ c 0 β z = 0) ↔
      σ ^ 2 ≤ ‖c‖ ^ 2 ∧
        (A = (Δ + √(‖c‖ ^ 2 - σ ^ 2)) / β ∨ A = (Δ - √(‖c‖ ^ 2 - σ ^ 2)) / β) := by
  rw [exists_norm_sq_eq_iff hA, eq_div_iff hβ, eq_div_iff hβ]
  simp only [zero_mul, add_zero]
  constructor
  · intro h
    have hD : σ ^ 2 ≤ ‖c‖ ^ 2 := by nlinarith [sq_nonneg (Δ - β * A)]
    refine ⟨hD, ?_⟩
    have hs : (Δ - β * A) ^ 2 = √(‖c‖ ^ 2 - σ ^ 2) ^ 2 := by
      rw [Real.sq_sqrt (by linarith)]; linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h1 | h1
    · right; linarith
    · left; linarith
  · rintro ⟨hD, h1 | h1⟩
    · rw [show Δ - β * A = -√(‖c‖ ^ 2 - σ ^ 2) by linarith, neg_sq, Real.sq_sqrt (by linarith)]
      ring
    · rw [show Δ - β * A = √(‖c‖ ^ 2 - σ ^ 2) by linarith, Real.sq_sqrt (by linarith)]; ring

/-- **Existence under a pure frequency shift** (`η = 0`, `β ≠ 0`): a nontrivial steady state
exists iff `σ² ≤ |c|²` and either `Δβ > 0` (the frequency shift bends the response towards the
pump: states down to `|c| = σ`, below the linear threshold) or `σ² + Δ² < |c|²` (above it). -/
@[tmio M, powerlib_foundation] theorem shift_exists_iff (hβ : β ≠ 0) :
    (∃ z : ℂ, z ≠ 0 ∧ ampField σ Δ c 0 β z = 0) ↔
      σ ^ 2 ≤ ‖c‖ ^ 2 ∧ (0 < Δ * β ∨ σ ^ 2 + Δ ^ 2 < ‖c‖ ^ 2) := by
  rw [exists_ne_zero_iff]
  simp only [zero_mul, add_zero]
  constructor
  · rintro ⟨A, hA, h⟩
    have hD : σ ^ 2 ≤ ‖c‖ ^ 2 := by nlinarith [sq_nonneg (Δ - β * A)]
    refine ⟨hD, ?_⟩
    by_contra hn
    push Not at hn
    obtain ⟨h1, h2⟩ := hn
    -- `Δβ ≤ 0` and `(Δ − βA)² ≤ Δ²` force `βA (βA − 2Δ) ≤ 0` with `βA` and `−Δ` of one sign
    have h3 : (Δ - β * A) ^ 2 ≤ Δ ^ 2 := by linarith
    have h4 : 0 < (β * A) ^ 2 := by positivity
    nlinarith [mul_pos hA hA, sq_nonneg β]
  · rintro ⟨hD, h | h⟩
    · set s := √(‖c‖ ^ 2 - σ ^ 2)
      have hs : s ^ 2 = ‖c‖ ^ 2 - σ ^ 2 := Real.sq_sqrt (by linarith)
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      rcases lt_or_gt_of_ne hβ with hb | hb
      · refine ⟨(Δ - s) / β, ?_, ?_⟩
        · have : Δ < 0 := by nlinarith
          exact div_pos_of_neg_of_neg (by linarith) hb
        · rw [show Δ - β * ((Δ - s) / β) = s by field_simp; ring, hs]; ring
      · refine ⟨(Δ + s) / β, ?_, ?_⟩
        · have : 0 < Δ := by nlinarith
          exact div_pos (by linarith) hb
        · rw [show Δ - β * ((Δ + s) / β) = -s by field_simp; ring, neg_sq, hs]; ring
    · set s := √(‖c‖ ^ 2 - σ ^ 2)
      have hs : s ^ 2 = ‖c‖ ^ 2 - σ ^ 2 := Real.sq_sqrt (by linarith)
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      have hsΔ : |Δ| < s := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
      rcases lt_or_gt_of_ne hβ with hb | hb
      · refine ⟨(Δ - s) / β, ?_, ?_⟩
        · exact div_pos_of_neg_of_neg (by linarith [le_abs_self Δ]) hb
        · rw [show Δ - β * ((Δ - s) / β) = s by field_simp; ring, hs]; ring
      · refine ⟨(Δ + s) / β, ?_, ?_⟩
        · exact div_pos (by linarith [neg_abs_le Δ]) hb
        · rw [show Δ - β * ((Δ + s) / β) = -s by field_simp; ring, neg_sq, hs]; ring

/-- Pure frequency shift with `σ > 0`: a nontrivial steady state is locally exponentially stable
iff `β(β|z|² − Δ) > 0`, and a saddle (unstable) iff `β(β|z|² − Δ) < 0`. -/
@[tmio TM, powerlib_foundation] theorem shift_stable_iff (hσ : 0 < σ) {z : ℂ}
    (hz : ampField σ Δ c 0 β z = 0) (hz0 : z ≠ 0) :
    (LocallyExponentiallyStable (ampSystem σ Δ c 0 β) (toReal z) ↔
        0 < β * (β * ‖z‖ ^ 2 - Δ)) ∧
      (β * (β * ‖z‖ ^ 2 - Δ) < 0 → Unstable (ampSystem σ Δ c 0 β) (toReal z)) := by
  have e : 0 * σ - β * Δ + (0 ^ 2 + β ^ 2) * ‖z‖ ^ 2 = β * (β * ‖z‖ ^ 2 - Δ) := by ring
  refine ⟨?_, fun h => unstable_of_det hz hz0 (by rw [e]; exact h)⟩
  rw [stable_iff hz hz0, e]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨by linarith, h⟩


/-- **Bistability and hysteresis under a pure frequency shift** (`η = 0`, `σ > 0`, `Δβ > 0`). In
the window `σ < |c| < √(σ² + Δ²)` below the linear threshold three locked regimes coexist: the
stable zero state, a stable large state with `a² = (|Δ| + s)/|β|` and a saddle with
`a² = (|Δ| − s)/|β|`, `s = √(|c|² − σ²)`. Raising `|c|` through `√(σ² + Δ²)` destabilizes the
zero state (`zero_unstable`); lowering it, the large state survives down to `|c| = σ`. -/
@[tmio TM, powerlib_foundation] theorem shift_bistable (hσ : 0 < σ) (hΔβ : 0 < Δ * β)
    (h1 : σ ^ 2 < ‖c‖ ^ 2) (h2 : ‖c‖ ^ 2 < σ ^ 2 + Δ ^ 2) :
    LocallyExponentiallyStable (ampSystem σ Δ c 0 β) 0 ∧
      (∃ z : ℂ, ‖z‖ ^ 2 = (|Δ| + √(‖c‖ ^ 2 - σ ^ 2)) / |β| ∧ ampField σ Δ c 0 β z = 0 ∧
        LocallyExponentiallyStable (ampSystem σ Δ c 0 β) (toReal z)) ∧
      (∃ z : ℂ, ‖z‖ ^ 2 = (|Δ| - √(‖c‖ ^ 2 - σ ^ 2)) / |β| ∧ z ≠ 0 ∧
        ampField σ Δ c 0 β z = 0 ∧ Unstable (ampSystem σ Δ c 0 β) (toReal z)) := by
  have hβ : β ≠ 0 := by rintro rfl; simp at hΔβ
  set s := √(‖c‖ ^ 2 - σ ^ 2) with hsdef
  have hs : s ^ 2 = ‖c‖ ^ 2 - σ ^ 2 := Real.sq_sqrt (by linarith)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hsΔ : s < |Δ| := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have hb : 0 < |β| := abs_pos.mpr hβ
  -- the two amplitudes solve `(Δ − βA)² = s²` with `β(βA − Δ) = ±|β| s`
  have hroot : ∀ e : ℝ, e = 1 ∨ e = -1 →
      β * (β * ((|Δ| + e * s) / |β|) - Δ) = e * |β| * s ∧
        σ ^ 2 + (Δ - β * ((|Δ| + e * s) / |β|)) ^ 2 = ‖c‖ ^ 2 := by
    intro e he
    have he2 : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
    rcases lt_or_gt_of_ne hβ with hneg | hpos
    · have hΔ : Δ < 0 := by nlinarith
      rw [abs_of_neg hneg, abs_of_neg hΔ]
      constructor
      · field_simp; ring
      · rw [show Δ - β * ((-Δ + e * s) / -β) = e * s by field_simp; ring, mul_pow, he2, hs]
        ring
    · have hΔ : 0 < Δ := by nlinarith
      rw [abs_of_pos hpos, abs_of_pos hΔ]
      constructor
      · field_simp; ring
      · rw [show Δ - β * ((Δ + e * s) / β) = -(e * s) by field_simp; ring, neg_sq, mul_pow,
          he2, hs]
        ring
  obtain ⟨hp1, hp2⟩ := hroot 1 (Or.inl rfl)
  obtain ⟨hm1, hm2⟩ := hroot (-1) (Or.inr rfl)
  simp only [one_mul, neg_mul, ← sub_eq_add_neg] at hp1 hp2 hm1 hm2
  have hAp : 0 < (|Δ| + s) / |β| := div_pos (by linarith) hb
  have hAm : 0 < (|Δ| - s) / |β| := div_pos (by linarith) hb
  refine ⟨zero_stable_iff.mpr ⟨hσ, h2⟩, ?_, ?_⟩
  · obtain ⟨z, hz, h0⟩ := (exists_norm_sq_eq_iff (σ := σ) (Δ := Δ) (c := c) (η := 0) (β := β)
      hAp).mpr (by rw [zero_mul, add_zero]; exact hp2)
    have hz0 : z ≠ 0 := by rintro rfl; rw [norm_zero] at hz; linarith [hz ▸ hAp]
    refine ⟨z, hz, h0, ((shift_stable_iff hσ h0 hz0).1).mpr ?_⟩
    rw [hz, hp1]; positivity
  · obtain ⟨z, hz, h0⟩ := (exists_norm_sq_eq_iff (σ := σ) (Δ := Δ) (c := c) (η := 0) (β := β)
      hAm).mpr (by rw [zero_mul, add_zero]; exact hm2)
    have hz0 : z ≠ 0 := by rintro rfl; rw [norm_zero] at hz; linarith [hz ▸ hAm]
    refine ⟨z, hz, hz0, h0, (shift_stable_iff hσ h0 hz0).2 ?_⟩
    rw [hz, hm1]
    have := mul_pos hb hs0
    linarith

/-- **Above the threshold under a pure frequency shift** (`η = 0`, `σ > 0`, `β ≠ 0`,
`σ² + Δ² < |c|²`): the zero state is unstable, and the phase-locked state is unique in
amplitude, with `β(β a² − Δ) = |β| √(|c|² − σ²)`, i.e. `a² = (Δ + sgn β · s)/β`, and locally
exponentially stable. -/
@[tmio TM, powerlib_foundation] theorem shift_above (hσ : 0 < σ) (hβ : β ≠ 0)
    (hc : σ ^ 2 + Δ ^ 2 < ‖c‖ ^ 2) :
    Unstable (ampSystem σ Δ c 0 β) 0 ∧ (∃ z : ℂ, z ≠ 0 ∧ ampField σ Δ c 0 β z = 0) ∧
      ∀ z : ℂ, z ≠ 0 → ampField σ Δ c 0 β z = 0 →
        β * (β * ‖z‖ ^ 2 - Δ) = |β| * √(‖c‖ ^ 2 - σ ^ 2) ∧
          LocallyExponentiallyStable (ampSystem σ Δ c 0 β) (toReal z) := by
  have hD : σ ^ 2 ≤ ‖c‖ ^ 2 := by nlinarith [sq_nonneg Δ]
  refine ⟨zero_unstable (Or.inr ⟨⟨hσ.le, hc⟩, not_lt.mpr hσ.le⟩),
    (shift_exists_iff hβ).mpr ⟨hD, Or.inr hc⟩, fun z hz0 hz => ?_⟩
  set s := √(‖c‖ ^ 2 - σ ^ 2) with hsdef
  have hsΔ : |Δ| < s := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have hs0 : 0 < s := lt_of_le_of_lt (abs_nonneg _) hsΔ
  have hA : 0 < ‖z‖ ^ 2 := by positivity
  have key : β * (β * ‖z‖ ^ 2 - Δ) = |β| * s := by
    obtain ⟨-, h | h⟩ := (shift_states hβ hA).mp ⟨z, rfl, hz⟩
    · rw [h, show β * (β * ((Δ + s) / β) - Δ) = β * s by field_simp; ring]
      rcases lt_or_gt_of_ne hβ with hb | hb
      · exfalso
        rw [h] at hA
        have : (Δ + s) / β < 0 := div_neg_of_pos_of_neg (by linarith [neg_abs_le Δ]) hb
        linarith
      · rw [abs_of_pos hb]
    · rw [h, show β * (β * ((Δ - s) / β) - Δ) = -(β * s) by field_simp; ring]
      rcases lt_or_gt_of_ne hβ with hb | hb
      · rw [abs_of_neg hb]; ring
      · exfalso
        rw [h] at hA
        have : (Δ - s) / β < 0 := div_neg_of_neg_of_pos (by linarith [le_abs_self Δ]) hb
        linarith
  refine ⟨key, ((shift_stable_iff hσ hz hz0).1).mpr ?_⟩
  rw [key]; exact mul_pos (abs_pos.mpr hβ) hs0

/-- **No phase-locked state for a weak pump under a pure frequency shift**: with `η = 0` and
`|c| < σ` the only steady state is `z = 0` (the hysteresis loop closes at `|c| = σ`). -/
@[tmio M, powerlib_foundation] theorem shift_below (hc : ‖c‖ ^ 2 < σ ^ 2) {z : ℂ}
    (hz : ampField σ Δ c 0 β z = 0) : z = 0 := by
  by_contra hz0
  have hA : 0 < ‖z‖ ^ 2 := by positivity
  have h := (exists_norm_sq_eq_iff hA).mp ⟨z, rfl, hz⟩
  nlinarith [sq_nonneg (Δ - β * ‖z‖ ^ 2)]

end powerlib.ParametricResonance.Saturation
