import theorem.Periodic.AndronovWitt

/-! # Critical cycles: the multipliers decide nothing, and attraction without asymptotic phase

When a nontrivial multiplier of a periodic orbit lies on the unit circle and the others inside
(the critical case of the Andronov–Witt theorem), the multipliers do not decide orbital
stability, and an attracting orbit need not carry an asymptotic phase. Both facts are shown on
explicit planar fields `ż = ω(s) J z + g(s) z`, `s = |z|²`, `J` the generator of the rotations
(`planarField`; in polar coordinates `θ̇ = ω(r²)`, `ṙ = g(r²) r`), all with the unit circle
`unitCycle(t) = (cos t, sin t)` as a `2π`-periodic orbit when `ω(1) = 1`, `g(1) = 0`
(`hasDerivAt_unitCycle`). Along every solution `ṡ = 2 g(s) s` (`hasDerivWithinAt_sqr`), and the
distance to the circle is comparable with `| |z|² − 1 |` (`infDist_le_abs_sqr_sub_one`,
`abs_sqr_sub_one_le`).

* **(a) The multipliers decide nothing.** The cubic fields `ż = J z + c (|z|² − 1)³ z`
  (`cubicField`): on the circle the cubic term is flat, the field has the derivative `J`
  (`hasFDerivAt_cubicField`), the variational equation is `ẏ = J y` and the monodromy is the
  rotation by `2π`, the identity — the multipliers `{1, 1}`, the same for every `c`
  (`monodromy_cubicField`). For `c = −1` the orbit is orbitally asymptotically stable (the
  Lyapunov function `V = (s − 1)²` with `V̇ = −4 (s − 1)⁴ s ≤ −2 V²`), for `c = 1` it is orbitally
  unstable (solutions inside fall towards the origin), for `c = 0` (the rotation) it is orbitally
  stable and not attracting (`|z|` is constant): `multipliers_do_not_decide`. The polar form
  `ṙ = ∓(r − 1)³` of the brief is replaced by `ṙ = ∓r (r² − 1)³ = ∓r (r + 1)³ (r − 1)³`, with the
  same cubic contact with the circle, so that the fields are polynomial on `ℝ²`.
* **(b) Attraction without asymptotic phase.** The twisted field
  `ż = |z|² J z − (|z|² − 1)³ z` (`twistField`; `θ̇ = r²`, `ṙ = −r (r² − 1)³`) has the radial law
  of `c = −1`, so the circle is orbitally asymptotically stable (`orbit_stable_of_stable_law`),
  but no solution starting off the circle has an asymptotic phase (`not_tendsto_twistField`): in
  the frame rotating with `unitCycle(· + θ)` the angle of the solution moves by `α̇ = |z|² − 1`
  (`hasDerivAt_frame_arctan`), `u = |z|² − 1` keeps its sign, and `1/u − 3α` is monotone because
  `(1/u)˙ = 2u (1 + u)`, so a bounded angle would keep `|u|` away from `0`. Hence its multipliers
  are critical (`twistField_critical`).
* **Existence.** The fields are polynomial, not globally Lipschitz. The solutions near the circle
  exist on `[0, ∞)`: the solution of the localized, globally Lipschitz field
  `LocalField.localField` never leaves a Lyapunov sublevel set lying in the ball where it equals
  the field (`exists_solution_of_lyapunov`, `exists_solution_planar`; the first-exit argument
  `le_of_deriv_nonpos_of_lt`, `lyapunov_le`).

Scope.
* The plane `Fin 2 → ℝ` with the sup norm, solutions on `[0, ∞)` (Mathlib `IsIntegralCurveOn`),
  orbital distance `Metric.infDist` to the circle, multipliers through `Periodic.monodromy` of
  `Periodic.variationalMatrix`. The monodromy of the twisted field is not computed: its
  criticality is derived from the dynamics through `AndronovWitt.andronov_witt_local` and
  `AndronovWitt.orbit_unstable_local`.
* Only the qualitative facts are proved: the algebraic rate of attraction
  (`| |z|² − 1 | ~ t^{−1/2}`) and the growth `~ √t` of the phase drift are not quantified (the
  drift is shown to be unbounded).
* Generic mathematics; no model family.

Source: Andronov, Vitt and Khaikin, *Theory of Oscillators* (limit cycles of planar fields in
polar form, the multiple cycle); Coddington and Levinson, *Theory of Ordinary Differential
Equations*, Ch. 13 (orbital stability and asymptotic phase under the Andronov–Witt hypothesis);
Hartman, *Ordinary Differential Equations* (the asymptotic phase); Hirsch, Smale and Devaney,
*Differential Equations, Dynamical Systems, and an Introduction to Chaos*, Ch. 8 and 10 (planar
systems in polar coordinates); the open item of `theorem/Periodic/AndronovWitt.lean` (Scope:
"The critical case (a nontrivial multiplier on the unit circle, the others inside) is not decided
here").

Results.
* The fields and the orbit: `sqr`, `rotGen`, `planarField`, `unitCycle`, `planarField_apply_zero`,
  `planarField_apply_one`, `sqr_unitCycle`, `unitCycle_periodic`, `hasDerivAt_unitCycle`,
  `planarField_unitCycle_zero_ne`, `sqrD`, `sqrD_apply`, `hasFDerivAt_sqr`, `sqrD_planarField`.
* The multipliers `{1, 1}`: `cubicField`, `hasFDerivAt_cubicField`,
  `variationalMatrix_cubicField`, `rotMat`, `hasDerivAt_rotMat`, `monodromy_cubicField`.
* Distance to the circle: `mem_range_unitCycle`, `norm_unitCycle_le`,
  `infDist_le_abs_sqr_sub_one`, `abs_sqr_sub_one_le`, `abs_sqr_sub_one_lt_of_infDist`.
* Lyapunov functions and existence: `le_of_deriv_nonpos_of_lt`, `lyapunov_le`,
  `exists_solution_of_lyapunov`, `contDiff_sqr`, `contDiff_planarField`, `hasDerivWithinAt_sqr`,
  `hasFDerivAt_sqr_sub_one_sq`, `abs_sqr_sub_one_le_of_solution`, `norm_lt_two_of_sqr`,
  `exists_solution_planar`, `isIntegralCurveOn_tail`.
* **(a)**: `tendsto_sqr_of_stable`, `orbit_stable_of_stable_law`, `contDiff_cubicField`,
  `cubicField_neg_one`, `norm_le_one_of_sqr`, `orbit_unstable_cubicField_one`,
  `orbit_neutral_cubicField_zero`, **the theorem** `multipliers_do_not_decide`.
* **(b)**: `twistField`, `frame0`, `frame1`, `hasDerivAt_frame_arctan`, `abs_frame0_sub_one_le`,
  **the theorems** `not_tendsto_twistField`, `twistField_critical`.

Corrections.
None: counterexamples for the critical case, which `theorem/Periodic/AndronovWitt.lean` left
open. The brief's example forms `ṙ = ∓(r − 1)³`, `θ̇ = 1 + (r − 1)` are realized with
`ṙ = ∓r (r² − 1)³`, `θ̇ = 1` resp. `θ̇ = r²` (polynomial fields with the same qualitative
behaviour).

Family and connection conclusions.
None: static evidence on autonomous ODEs (orbital stability of planar cycles).
-/

noncomputable section
namespace powerlib.Periodic.CriticalCycles

open Set Matrix Function Filter Topology
open scoped Matrix.Norms.Operator

/-- The squared Euclidean norm `s(z) = z₀² + z₁²` of a point of the plane. -/
def sqr (z : Fin 2 → ℝ) : ℝ := z 0 ^ 2 + z 1 ^ 2

/-- The generator of the rotations of the plane, `J = [[0, −1], [1, 0]]`. -/
def rotGen : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- The planar field `ż = ω(s) J z + g(s) z`, `s = |z|²`: in polar coordinates
`ṙ = g(r²) r`, `θ̇ = ω(r²)`. -/
def planarField (ω g : ℝ → ℝ) (z : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ω (sqr z) • (rotGen *ᵥ z) + g (sqr z) • z

/-- The unit circle traversed with unit speed, `t ↦ (cos t, sin t)`. -/
def unitCycle (t : ℝ) : Fin 2 → ℝ := ![Real.cos t, Real.sin t]

@[tmio T, powerlib_foundation] theorem planarField_apply_zero (ω g : ℝ → ℝ) (z : Fin 2 → ℝ) :
    planarField ω g z 0 = ω (sqr z) * -z 1 + g (sqr z) * z 0 := by
  simp [planarField, rotGen, dotProduct, Fin.sum_univ_two]

@[tmio T, powerlib_foundation] theorem planarField_apply_one (ω g : ℝ → ℝ) (z : Fin 2 → ℝ) :
    planarField ω g z 1 = ω (sqr z) * z 0 + g (sqr z) * z 1 := by
  simp [planarField, rotGen, dotProduct, Fin.sum_univ_two]

@[tmio T, powerlib_foundation] theorem sqr_unitCycle (t : ℝ) : sqr (unitCycle t) = 1 := by
  simp [sqr, unitCycle, Real.cos_sq_add_sin_sq]

@[tmio T, powerlib_foundation] theorem unitCycle_periodic : Periodic unitCycle (2 * Real.pi) :=
  fun t => by
    funext i; fin_cases i <;> simp [unitCycle, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The unit circle is a periodic orbit of every field `ω(s) J z + g(s) z` with `ω(1) = 1`,
`g(1) = 0`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_unitCycle {ω g : ℝ → ℝ} (hω : ω 1 = 1)
    (hg : g 1 = 0) (t : ℝ) : HasDerivAt unitCycle (planarField ω g (unitCycle t)) t := by
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, planarField_apply_zero, sqr_unitCycle, hω, hg]
    simpa [unitCycle] using Real.hasDerivAt_cos t
  · simp only [Fin.mk_one, Fin.isValue, planarField_apply_one, sqr_unitCycle, hω, hg]
    simpa [unitCycle] using Real.hasDerivAt_sin t

@[tmio T, powerlib_foundation] theorem planarField_unitCycle_zero_ne {ω g : ℝ → ℝ}
    (hω : ω 1 = 1) (hg : g 1 = 0) : planarField ω g (unitCycle 0) ≠ 0 := by
  intro h
  have := congrFun h 1
  rw [planarField_apply_one, sqr_unitCycle, hω, hg] at this
  simp [unitCycle] at this

/-- The derivative of `s = |z|²`: `w ↦ 2 z₀ w₀ + 2 z₁ w₁`. -/
def sqrD (z : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  (2 * z 0) • ContinuousLinearMap.proj 0 + (2 * z 1) • ContinuousLinearMap.proj 1

@[tmio T, powerlib_foundation] theorem sqrD_apply (z w : Fin 2 → ℝ) :
    sqrD z w = 2 * z 0 * w 0 + 2 * z 1 * w 1 := by
  simp [sqrD]

@[tmio T, powerlib_foundation] theorem hasFDerivAt_sqr (z : Fin 2 → ℝ) :
    HasFDerivAt sqr (sqrD z) z := by
  have h0 := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) z).pow 2
  have h1 := (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) z).pow 2
  show HasFDerivAt (fun x : Fin 2 → ℝ => x 0 ^ 2 + x 1 ^ 2) (sqrD z) z
  refine (h0.add h1).congr_fderiv ?_
  ext w
  simp [sqrD]

/-- **The radial law.** Along `ż = ω(s) J z + g(s) z` the squared radius moves by
`ṡ = 2 g(s) s`. -/
@[tmio T, powerlib_foundation] theorem sqrD_planarField (ω g : ℝ → ℝ) (z : Fin 2 → ℝ) :
    sqrD z (planarField ω g z) = 2 * g (sqr z) * sqr z := by
  rw [sqrD_apply, planarField_apply_zero, planarField_apply_one, sqr]
  ring


/-! ## The cycles with the multipliers `{1, 1}` -/

/-- The planar fields `ż = J z + c (|z|² − 1)³ z`: in polar coordinates `θ̇ = 1`,
`ṙ = c r (r² − 1)³`. -/
def cubicField (c : ℝ) : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  planarField (fun _ => 1) fun s => c * (s - 1) ^ 3

/-- **On the unit circle the cubic fields have the derivative `J`.** -/
@[tmio T, powerlib_foundation] theorem hasFDerivAt_cubicField (c : ℝ) {z : Fin 2 → ℝ}
    (hz : sqr z = 1) :
    HasFDerivAt (cubicField c) (Matrix.toLin' rotGen).toContinuousLinearMap z := by
  set L := (Matrix.toLin' rotGen).toContinuousLinearMap with hL
  have hfun : cubicField c = fun y => L y + (c * (sqr y - 1) ^ 3) • y := by
    funext y
    simp [cubicField, planarField, hL]
  have hc := (((hasFDerivAt_sqr z).sub_const 1).pow 3).const_mul c
  have h := L.hasFDerivAt.add (hc.smul (hasFDerivAt_id z))
  rw [hfun]
  refine h.congr_fderiv ?_
  ext w
  simp [hz]

/-- The variational matrix of a cubic field along the unit circle is the constant `J`. -/
@[tmio T, powerlib_foundation] theorem variationalMatrix_cubicField (c t : ℝ) :
    variationalMatrix (cubicField c) unitCycle t = rotGen := by
  rw [variationalMatrix, (hasFDerivAt_cubicField c (sqr_unitCycle t)).fderiv]
  exact LinearMap.toMatrix'_toLin' rotGen

/-- The rotation matrices `R(t) = [[cos t, −sin t], [sin t, cos t]]`. -/
def rotMat (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t]

@[tmio T, powerlib_foundation] theorem hasDerivAt_rotMat (t : ℝ) :
    HasDerivAt rotMat (rotGen * rotMat t) t := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j
  · simpa [rotMat, rotGen, Matrix.mul_apply, Fin.sum_univ_two] using Real.hasDerivAt_cos t
  · have h : HasDerivAt (fun x => -Real.sin x) (-Real.cos t) t := (Real.hasDerivAt_sin t).neg
    simp [rotMat, rotGen, Matrix.mul_apply, Fin.sum_univ_two]
    exact h
  · simpa [rotMat, rotGen, Matrix.mul_apply, Fin.sum_univ_two] using Real.hasDerivAt_sin t
  · simpa [rotMat, rotGen, Matrix.mul_apply, Fin.sum_univ_two] using Real.hasDerivAt_cos t

/-- **The multipliers `{1, 1}`.** The monodromy of the unit circle as a `2π`-periodic orbit of
every cubic field `ż = J z + c (|z|² − 1)³ z` is the identity. -/
@[tmio T, powerlib_foundation] theorem monodromy_cubicField (c : ℝ) :
    monodromy (variationalMatrix (cubicField c) unitCycle) (2 * Real.pi) 0 = 1 := by
  have hA : variationalMatrix (cubicField c) unitCycle = fun _ => rotGen :=
    funext fun t => variationalMatrix_cubicField c t
  rw [hA, monodromy, zero_add]
  have hY : IsIntegralCurveOn rotMat (matField fun _ => rotGen) (Ici 0) :=
    fun t _ => (hasDerivAt_rotMat t).hasDerivWithinAt
  have h := transition_unique continuous_const (M := ‖rotGen‖) (fun _ => le_rfl) hY
    (2 * Real.pi) (by positivity)
  have h0 : rotMat 0 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat]
  have h2 : rotMat (2 * Real.pi) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat]
  rw [h0, h2, mul_one] at h
  exact h.symm


/-! ## The distance to the unit circle -/

/-- The orbit of `unitCycle` is the unit circle `|z|² = 1`. -/
@[tmio T, powerlib_foundation] theorem mem_range_unitCycle {z : Fin 2 → ℝ} (hz : sqr z = 1) :
    z ∈ range unitCycle := by
  set w : ℂ := ⟨z 0, z 1⟩ with hw
  have hw1 : ‖w‖ = 1 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp only [hw]
    rw [show z 0 ^ 2 + z 1 ^ 2 = sqr z from rfl, hz, Real.sqrt_one]
  have hw0 : w ≠ 0 := by rw [← norm_ne_zero_iff, hw1]; exact one_ne_zero
  refine ⟨Complex.arg w, ?_⟩
  funext i
  fin_cases i
  · show Real.cos (Complex.arg w) = z 0
    rw [Complex.cos_arg hw0, hw1, div_one]
  · show Real.sin (Complex.arg w) = z 1
    rw [Complex.sin_arg, hw1, div_one]

@[tmio T, powerlib_foundation] theorem norm_unitCycle_le (t : ℝ) : ‖unitCycle t‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  fin_cases i
  · simpa [unitCycle] using Real.abs_cos_le_one t
  · simpa [unitCycle] using Real.abs_sin_le_one t

/-- **The distance to the unit circle is at most `| |z|² − 1 |`.** -/
@[tmio T, powerlib_foundation] theorem infDist_le_abs_sqr_sub_one (z : Fin 2 → ℝ) :
    Metric.infDist z (range unitCycle) ≤ |sqr z - 1| := by
  by_cases hz : z = 0
  · subst hz
    calc Metric.infDist 0 (range unitCycle) ≤ dist 0 (unitCycle 0) :=
          Metric.infDist_le_dist_of_mem (mem_range_self _)
      _ = 1 := by
          rw [dist_eq_norm, zero_sub, norm_neg]
          refine le_antisymm (norm_unitCycle_le 0) ?_
          have := norm_le_pi_norm (unitCycle 0) 0
          simpa [unitCycle] using this
      _ = |sqr 0 - 1| := by simp [sqr]
  set s := sqr z with hs
  have hs0 : 0 < s := by
    rcases (add_nonneg (sq_nonneg (z 0)) (sq_nonneg (z 1))).lt_or_eq with h | h
    · exact h
    · exfalso; apply hz
      have h0 : z 0 = 0 := by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
      have h1 : z 1 = 0 := by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
      funext i; fin_cases i <;> simp [h0, h1]
  set ρ := Real.sqrt s with hρ
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 hs0
  have hρs : ρ ^ 2 = s := Real.sq_sqrt hs0.le
  have hc : sqr (ρ⁻¹ • z) = 1 := by
    simp only [sqr, Pi.smul_apply, smul_eq_mul]
    rw [mul_pow, mul_pow, ← mul_add, show z 0 ^ 2 + z 1 ^ 2 = s from rfl, inv_pow, hρs,
      inv_mul_cancel₀ hs0.ne']
  have hz0 : z 0 ^ 2 ≤ s := by simp only [hs, sqr]; nlinarith [sq_nonneg (z 1)]
  have hz1 : z 1 ^ 2 ≤ s := by simp only [hs, sqr]; nlinarith [sq_nonneg (z 0)]
  have hzρ : ‖z‖ ≤ ρ := (pi_norm_le_iff_of_nonneg hρ0.le).2 (Fin.forall_fin_two.2
    ⟨by rw [Real.norm_eq_abs]; exact Real.abs_le_sqrt hz0,
      by rw [Real.norm_eq_abs]; exact Real.abs_le_sqrt hz1⟩)
  calc Metric.infDist z (range unitCycle) ≤ dist z (ρ⁻¹ • z) :=
        Metric.infDist_le_dist_of_mem (mem_range_unitCycle hc)
    _ = |1 - ρ⁻¹| * ‖z‖ := by
        rw [dist_eq_norm, show z - ρ⁻¹ • z = (1 - ρ⁻¹) • z by rw [sub_smul, one_smul],
          norm_smul, Real.norm_eq_abs]
    _ ≤ |1 - ρ⁻¹| * ρ := mul_le_mul_of_nonneg_left hzρ (abs_nonneg _)
    _ = |ρ - 1| := by
        rw [← abs_of_pos hρ0, ← abs_mul, abs_of_pos hρ0, sub_mul, one_mul,
          inv_mul_cancel₀ hρ0.ne']
    _ ≤ |ρ - 1| * (ρ + 1) := le_mul_of_one_le_right (abs_nonneg _) (by linarith)
    _ = |s - 1| := by
        rw [← abs_of_pos (by linarith : (0 : ℝ) < ρ + 1), ← abs_mul]
        congr 1; rw [← hρs]; ring

/-- **The distance to the unit circle is at least `| |z|² − 1 |/(2 (‖z‖ + 1))`.** -/
@[tmio T, powerlib_foundation] theorem abs_sqr_sub_one_le (z : Fin 2 → ℝ) :
    |sqr z - 1| ≤ 2 * (‖z‖ + 1) * Metric.infDist z (range unitCycle) := by
  have hpos : 0 < 2 * (‖z‖ + 1) := by positivity
  rw [← div_le_iff₀' hpos]
  refine (Metric.le_infDist (range_nonempty unitCycle)).2 ?_
  rintro _ ⟨t, rfl⟩
  rw [div_le_iff₀' hpos, dist_eq_norm]
  set y := unitCycle t with hy
  have hy1 : sqr y = 1 := sqr_unitCycle t
  have hyn : ‖y‖ ≤ 1 := norm_unitCycle_le t
  have hi : ∀ i, |z i - y i| ≤ ‖z - y‖ := fun i => by
    have := norm_le_pi_norm (z - y) i; rwa [Real.norm_eq_abs] at this
  have hj : ∀ i, |z i + y i| ≤ ‖z‖ + 1 := fun i => by
    have h1 := norm_le_pi_norm z i
    have h2 := norm_le_pi_norm y i
    rw [Real.norm_eq_abs] at h1 h2
    exact (abs_add_le _ _).trans (by linarith)
  have e : sqr z - 1 = (z 0 - y 0) * (z 0 + y 0) + (z 1 - y 1) * (z 1 + y 1) := by
    rw [← hy1]; simp only [sqr]; ring
  rw [e]
  calc |(z 0 - y 0) * (z 0 + y 0) + (z 1 - y 1) * (z 1 + y 1)|
      ≤ |z 0 - y 0| * |z 0 + y 0| + |z 1 - y 1| * |z 1 + y 1| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ ‖z - y‖ * (‖z‖ + 1) + ‖z - y‖ * (‖z‖ + 1) := by
        gcongr <;> first | exact hi _ | exact hj _
    _ = 2 * (‖z‖ + 1) * ‖z - y‖ := by ring


/-! ## Lyapunov functions along solutions, and existence near the circle -/

/-- **First exit.** A function continuous on `[0, ∞)`, with right derivative `≤ 0` wherever it
is below `c'`, that starts below `c'` never exceeds its initial value. -/
@[tmio T, powerlib_foundation] theorem le_of_deriv_nonpos_of_lt {φ φ' : ℝ → ℝ} {c' : ℝ}
    (hc : ContinuousOn φ (Ici 0)) (hd : ∀ t, 0 ≤ t → HasDerivWithinAt φ (φ' t) (Ici t) t)
    (hneg : ∀ t, 0 ≤ t → φ t < c' → φ' t ≤ 0) (h0 : φ 0 < c') :
    ∀ t, 0 ≤ t → φ t ≤ φ 0 := by
  intro t₁ ht₁
  by_contra hcon
  push Not at hcon
  set ε := min ((c' - φ 0) / (2 * (1 + t₁))) ((φ t₁ - φ 0) / (2 * (1 + t₁))) with hε
  have h1t : 0 < 1 + t₁ := by linarith
  have hε0 : 0 < ε := lt_min (div_pos (by linarith) (by positivity))
    (div_pos (by linarith) (by positivity))
  have hε1 : ε * (1 + t₁) ≤ (c' - φ 0) / 2 := by
    have := min_le_left ((c' - φ 0) / (2 * (1 + t₁))) ((φ t₁ - φ 0) / (2 * (1 + t₁)))
    calc ε * (1 + t₁) ≤ (c' - φ 0) / (2 * (1 + t₁)) * (1 + t₁) :=
          mul_le_mul_of_nonneg_right this h1t.le
      _ = (c' - φ 0) / 2 := by field_simp
  have hε2 : ε * (1 + t₁) ≤ (φ t₁ - φ 0) / 2 := by
    have := min_le_right ((c' - φ 0) / (2 * (1 + t₁))) ((φ t₁ - φ 0) / (2 * (1 + t₁)))
    calc ε * (1 + t₁) ≤ (φ t₁ - φ 0) / (2 * (1 + t₁)) * (1 + t₁) :=
          mul_le_mul_of_nonneg_right this h1t.le
      _ = (φ t₁ - φ 0) / 2 := by field_simp
  have hB : ∀ x, HasDerivAt (fun x => φ 0 + ε * (1 + x)) ε x := fun x => by
    simpa using (((hasDerivAt_id x).const_add 1).const_mul ε).const_add (φ 0)
  have h := image_le_of_deriv_right_lt_deriv_boundary (f := φ) (f' := φ') (a := 0) (b := t₁)
    (hc.mono Icc_subset_Ici_self) (fun x hx => hd x hx.1) (B := fun x => φ 0 + ε * (1 + x))
    (B' := fun _ => ε) (by nlinarith) hB (fun x hx hfx => by
      have hlt : φ x < c' := by
        rw [hfx]
        have : ε * (1 + x) ≤ ε * (1 + t₁) := mul_le_mul_of_nonneg_left (by linarith [hx.2.le])
          hε0.le
        linarith
      exact (hneg x hx.1 hlt).trans_lt hε0) ⟨ht₁, le_rfl⟩
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A Lyapunov function along a solution.** If `V` (with derivatives `V'`) does not increase
along the field `G` wherever `V < c'`, then along every solution on `[0, ∞)` starting in
`V < c'`, `V(x(t)) ≤ V(x(0))`. -/
@[tmio T, powerlib_foundation] theorem lyapunov_le {G : E → E} {x : ℝ → E}
    (hx : IsIntegralCurveOn x (fun _ => G) (Ici 0)) {V : E → ℝ} {V' : E → E →L[ℝ] ℝ}
    (hV : ∀ z, HasFDerivAt V (V' z) z) {c' : ℝ} (hdec : ∀ z, V z < c' → V' z (G z) ≤ 0)
    (h0 : V (x 0) < c') : ∀ t, 0 ≤ t → V (x t) ≤ V (x 0) := by
  have hVc : Continuous V := continuous_iff_continuousAt.2 fun z => (hV z).continuousAt
  refine le_of_deriv_nonpos_of_lt (φ := fun t => V (x t)) (φ' := fun t => V' (x t) (G (x t)))
    (hVc.comp_continuousOn hx.continuousOn) (fun t ht => ?_) (fun t _ h => hdec _ h) h0
  exact ((hV (x t)).comp_hasDerivWithinAt t (hx t ht)).mono (Ici_subset_Ici.2 ht)

/-- **Existence of global solutions from a Lyapunov sublevel set.** Let `F` be of class `C¹` on
`ℝ^{Fin n}` and `V` a differentiable function that does not increase along `F` on the sublevel
set `V < c'`, which lies in the ball `‖z‖ < R`. Then every point of the sublevel set starts a
solution of `F` on `[0, ∞)` (the solution of the globally Lipschitz localized field
`LocalField.localField` never leaves the sublevel set). -/
@[tmio T, powerlib_foundation] theorem exists_solution_of_lyapunov {n : ℕ}
    {F : (Fin n → ℝ) → Fin n → ℝ} (hF : ContDiff ℝ 1 F) {V : (Fin n → ℝ) → ℝ}
    {V' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hV : ∀ z, HasFDerivAt V (V' z) z) {c' R : ℝ}
    (hVR : ∀ z, V z < c' → ‖z‖ < R) (hdec : ∀ z, V z < c' → V' z (F z) ≤ 0)
    {ξ : Fin n → ℝ} (hξ : V ξ < c') :
    ∃ x : ℝ → Fin n → ℝ, x 0 = ξ ∧ IsIntegralCurveOn x (fun _ => F) (Ici 0) := by
  have hGd : ∀ (t : ℝ) x, DifferentiableAt ℝ ((fun _ : ℝ => F) t) x :=
    fun _ x => (hF.differentiable one_ne_zero) x
  have hD : Continuous fun q : ℝ × (Fin n → ℝ) => fderiv ℝ ((fun _ : ℝ => F) q.1) q.2 :=
    (hF.continuous_fderiv one_ne_zero).comp continuous_snd
  obtain ⟨K', hK'⟩ := LocalField.exists_lipschitzWith_localField hGd hD one_pos
    (G := fun _ => F) (fun _ => rfl) R
  set fl := LocalField.localField (fun _ => F) R 0 with hfl
  have hflK : LipschitzWith K' fl := hK' 0
  set y := FlowDerivative.flow (G := fun _ => fl) (hflK.continuous.comp continuous_snd)
    (fun _ => hflK) 0 ξ with hy
  have hyI : IsIntegralCurveOn y (fun _ => fl) (Ici 0) := FlowDerivative.flow_solution _ _ 0 ξ
  have hy0 : y 0 = ξ := FlowDerivative.flow_start _ _ 0 ξ
  have hdec' : ∀ z, V z < c' → V' z (fl z) ≤ 0 := fun z hz => by
    rw [hfl, LocalField.localField_eq (hVR z hz).le]; exact hdec z hz
  have hle := lyapunov_le hyI hV hdec' (by rw [hy0]; exact hξ)
  refine ⟨y, hy0, LocalField.isIntegralCurveOn_of_localField (G := fun _ => F) hyI
    fun t ht => (hVR _ ((hle t ht).trans_lt (by rw [hy0]; exact hξ))).le⟩

/-! ## The radial law of the planar fields -/

@[tmio T, powerlib_foundation] theorem contDiff_sqr : ContDiff ℝ 1 sqr :=
  ((contDiff_apply ℝ ℝ (0 : Fin 2)).pow 2).add ((contDiff_apply ℝ ℝ (1 : Fin 2)).pow 2)

@[tmio T, powerlib_foundation] theorem contDiff_planarField {ω g : ℝ → ℝ} (hω : ContDiff ℝ 1 ω)
    (hg : ContDiff ℝ 1 g) : ContDiff ℝ 1 (planarField ω g) := by
  have hrot : ContDiff ℝ 1 fun z : Fin 2 → ℝ => rotGen *ᵥ z := by
    have : (fun z : Fin 2 → ℝ => rotGen *ᵥ z) =
        ⇑(Matrix.toLin' rotGen).toContinuousLinearMap := by funext z; rfl
    rw [this]; exact ContinuousLinearMap.contDiff _
  exact ((hω.comp contDiff_sqr).smul hrot).add ((hg.comp contDiff_sqr).smul contDiff_id)

/-- Along every solution of `ż = ω(s) J z + g(s) z` the squared radius satisfies `ṡ = 2 g(s) s`. -/
@[tmio T, powerlib_foundation] theorem hasDerivWithinAt_sqr {ω g : ℝ → ℝ}
    {x : ℝ → Fin 2 → ℝ} (hx : IsIntegralCurveOn x (fun _ => planarField ω g) (Ici 0)) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => sqr (x r)) (2 * g (sqr (x t)) * sqr (x t)) (Ici 0) t := by
  have h := (hasFDerivAt_sqr (x t)).comp_hasDerivWithinAt t (hx t ht)
  rwa [sqrD_planarField] at h

/-- The Lyapunov function `V(z) = (|z|² − 1)²` and its derivative. -/
@[tmio T, powerlib_foundation] theorem hasFDerivAt_sqr_sub_one_sq (z : Fin 2 → ℝ) :
    HasFDerivAt (fun y => (sqr y - 1) ^ 2) ((2 * (sqr z - 1)) • sqrD z) z := by
  have h := ((hasFDerivAt_sqr z).sub_const 1).pow 2
  refine h.congr_fderiv ?_
  ext w; simp

/-- If `(s − 1) g(s) ≤ 0`, the distance `| |z|² − 1 |` to the circle does not increase along the
solutions of `ż = ω(s) J z + g(s) z`. -/
@[tmio T, powerlib_foundation] theorem abs_sqr_sub_one_le_of_solution {ω g : ℝ → ℝ}
    (hug : ∀ s, (s - 1) * g s ≤ 0) {x : ℝ → Fin 2 → ℝ}
    (hx : IsIntegralCurveOn x (fun _ => planarField ω g) (Ici 0)) :
    ∀ t, 0 ≤ t → |sqr (x t) - 1| ≤ |sqr (x 0) - 1| := by
  have hdec : ∀ z, (sqr z - 1) ^ 2 < (sqr (x 0) - 1) ^ 2 + 1 →
      ((2 * (sqr z - 1)) • sqrD z) (planarField ω g z) ≤ 0 := fun z _ => by
    rw [_root_.smul_apply, sqrD_planarField, smul_eq_mul]
    have h1 := hug (sqr z)
    have h2 : 0 ≤ sqr z := add_nonneg (sq_nonneg _) (sq_nonneg _)
    nlinarith
  intro t ht
  have h := lyapunov_le hx hasFDerivAt_sqr_sub_one_sq hdec (by linarith) t ht
  exact sq_le_sq.1 h

/-- Points with `| |z|² − 1 | < 1/2` lie in the ball `‖z‖ < 2`. -/
@[tmio T, powerlib_foundation] theorem norm_lt_two_of_sqr {z : Fin 2 → ℝ} (hz : sqr z < 4) :
    ‖z‖ < 2 := by
  have h0 : z 0 ^ 2 < 2 ^ 2 := by simp only [sqr] at hz; nlinarith [sq_nonneg (z 1)]
  have h1 : z 1 ^ 2 < 2 ^ 2 := by simp only [sqr] at hz; nlinarith [sq_nonneg (z 0)]
  refine (pi_norm_lt_iff two_pos).2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · rw [Real.norm_eq_abs]; exact abs_lt_of_sq_lt_sq h0 (by norm_num)
  · rw [Real.norm_eq_abs]; exact abs_lt_of_sq_lt_sq h1 (by norm_num)

/-- **Existence near the circle.** If `(s − 1) g(s) ≤ 0` (and `ω`, `g` are of class `C¹`), every
point with `| |z|² − 1 | < 1/2` starts a solution of `ż = ω(s) J z + g(s) z` on `[0, ∞)`. -/
@[tmio T, powerlib_foundation] theorem exists_solution_planar {ω g : ℝ → ℝ}
    (hω : ContDiff ℝ 1 ω) (hg : ContDiff ℝ 1 g) (hug : ∀ s, (s - 1) * g s ≤ 0)
    {ξ : Fin 2 → ℝ} (hξ : |sqr ξ - 1| < 1 / 2) :
    ∃ x : ℝ → Fin 2 → ℝ, x 0 = ξ ∧ IsIntegralCurveOn x (fun _ => planarField ω g) (Ici 0) := by
  refine exists_solution_of_lyapunov (contDiff_planarField hω hg) hasFDerivAt_sqr_sub_one_sq
    (c' := 1 / 4) (R := 2) (fun z hz => norm_lt_two_of_sqr (by nlinarith)) (fun z _ => ?_) ?_
  · rw [_root_.smul_apply, sqrD_planarField, smul_eq_mul]
    have h1 := hug (sqr z)
    have h2 : 0 ≤ sqr z := add_nonneg (sq_nonneg _) (sq_nonneg _)
    nlinarith
  · have := abs_lt.1 hξ; nlinarith


/-- The tail of a solution on `[0, ∞)` from the time `t₀ ≥ 0` is a solution on `[0, ∞)`. -/
@[tmio T, powerlib_foundation] theorem isIntegralCurveOn_tail {G : E → E} {x : ℝ → E}
    (hx : IsIntegralCurveOn x (fun _ => G) (Ici 0)) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    IsIntegralCurveOn (fun r => x (r + t₀)) (fun _ => G) (Ici 0) :=
  (FlipOrbitUniform.isIntegralCurveOn_shift (fun _ => rfl) hx).mono
    (Ici_subset_Ici.2 (by linarith))

/-- A point within `δ ≤ 1` of the unit circle has `| |z|² − 1 | < 6 δ`. -/
@[tmio T, powerlib_foundation] theorem abs_sqr_sub_one_lt_of_infDist {z : Fin 2 → ℝ} {δ : ℝ}
    (hδ1 : δ ≤ 1) (hz : Metric.infDist z (range unitCycle) < δ) : |sqr z - 1| < 6 * δ := by
  obtain ⟨_, ⟨σ, rfl⟩, hσ⟩ := (Metric.infDist_lt_iff (range_nonempty unitCycle)).1 hz
  rw [dist_eq_norm] at hσ
  have hzn : ‖z‖ ≤ 2 := by
    calc ‖z‖ = ‖unitCycle σ + (z - unitCycle σ)‖ := by rw [add_sub_cancel]
      _ ≤ ‖unitCycle σ‖ + ‖z - unitCycle σ‖ := norm_add_le _ _
      _ ≤ 1 + 1 := add_le_add (norm_unitCycle_le σ) (hσ.le.trans hδ1)
      _ = 2 := by norm_num
  have h := abs_sqr_sub_one_le z
  have h0 := Metric.infDist_nonneg (x := z) (s := range unitCycle)
  calc |sqr z - 1| ≤ 2 * (‖z‖ + 1) * Metric.infDist z (range unitCycle) := h
    _ ≤ 6 * Metric.infDist z (range unitCycle) := by nlinarith
    _ < 6 * δ := by linarith

/-! ## The radial law `ṡ = −2 (s − 1)³ s`: orbital asymptotic stability -/

/-- **Attraction for the radial law `ṡ = −2 (s − 1)³ s`.** Along every solution of
`ż = ω(s) J z − (s − 1)³ z` with `| |z(0)|² − 1 | < 1/2`, `|z(t)|² → 1`. (The squared distance
`V = (s − 1)²` satisfies `V̇ = −4 (s − 1)⁴ s ≤ −2 V²`.) -/
@[tmio T, powerlib_foundation] theorem tendsto_sqr_of_stable {ω : ℝ → ℝ} {x : ℝ → Fin 2 → ℝ}
    (hx : IsIntegralCurveOn x (fun _ => planarField ω fun s => -(s - 1) ^ 3) (Ici 0))
    (h0 : |sqr (x 0) - 1| < 1 / 2) : Tendsto (fun t => sqr (x t) - 1) atTop (𝓝 0) := by
  have hug : ∀ s : ℝ, (s - 1) * (-(s - 1) ^ 3) ≤ 0 := fun s => by
    nlinarith [sq_nonneg ((s - 1) ^ 2)]
  have hb := abs_sqr_sub_one_le_of_solution hug hx
  rw [Metric.tendsto_atTop]
  intro η hη
  by_cases hex : ∃ t₀, 0 ≤ t₀ ∧ |sqr (x t₀) - 1| < η
  · obtain ⟨t₀, ht₀, hlt⟩ := hex
    refine ⟨t₀, fun t ht => ?_⟩
    have h := abs_sqr_sub_one_le_of_solution hug (isIntegralCurveOn_tail hx ht₀) (t - t₀)
      (by linarith)
    simp only [sub_add_cancel, zero_add] at h
    rw [Real.dist_eq, sub_zero]
    exact h.trans_lt hlt
  exfalso
  push Not at hex
  -- `W = V + 2 η⁴ t` does not increase
  set V : ℝ → ℝ := fun t => (sqr (x t) - 1) ^ 2 with hV
  have hVd : ∀ t, 0 ≤ t → HasDerivWithinAt V (-(4 * (sqr (x t) - 1) ^ 4 * sqr (x t)))
      (Ici t) t := fun t ht => by
    have h := ((hasDerivWithinAt_sqr hx ht).sub_const 1).pow 2
    refine (h.congr_deriv ?_).mono (Ici_subset_Ici.2 ht)
    simp only [Nat.cast_ofNat]
    ring
  set W : ℝ → ℝ := fun t => V t + 2 * η ^ 4 * t with hW
  have hWd : ∀ t, 0 ≤ t → HasDerivWithinAt W (-(4 * (sqr (x t) - 1) ^ 4 * sqr (x t)) +
      2 * η ^ 4) (Ici t) t := fun t ht => by
    have h := (hVd t ht).add ((hasDerivAt_id t).const_mul (2 * η ^ 4)).hasDerivWithinAt
    rw [mul_one] at h
    exact h
  have hWc : ContinuousOn W (Ici 0) := by
    have hxc := hx.continuousOn
    exact ((contDiff_sqr.continuous.comp_continuousOn hxc).sub continuousOn_const).pow 2 |>.add
      (continuousOn_const.mul continuousOn_id)
  have hWle := le_of_deriv_nonpos_of_lt hWc hWd (c' := W 0 + 1) (fun t ht _ => by
    have h1 := hex t ht
    have h2 := abs_lt.1 ((hb t ht).trans_lt h0)
    have hs : 1 / 2 ≤ sqr (x t) := by linarith [h2.1]
    have h3 : η ^ 4 ≤ (sqr (x t) - 1) ^ 4 := by
      have := pow_le_pow_left₀ hη.le h1 4
      rwa [pow_abs, abs_of_nonneg (by positivity)] at this
    nlinarith [sq_nonneg ((sqr (x t) - 1) ^ 2)]) (by linarith)
  set t₁ := V 0 / (2 * η ^ 4) + 1 with ht₁
  have ht₁0 : 0 ≤ t₁ := by positivity
  have h := hWle t₁ ht₁0
  simp only [hW, mul_zero, add_zero] at h
  have hV0 : 0 ≤ V t₁ := sq_nonneg _
  have : 2 * η ^ 4 * t₁ = V 0 + 2 * η ^ 4 := by
    rw [ht₁, mul_add, mul_one, mul_div_cancel₀ _ (by positivity)]
  have hη4 : 0 < η ^ 4 := by positivity
  linarith

/-- **Orbital asymptotic stability for the radial law `ṡ = −2 (s − 1)³ s`.** For every `C¹`
angular law `ω` with `ω(1) = 1`, the unit circle, a `2π`-periodic orbit of
`ż = ω(s) J z − (s − 1)³ z`, is orbitally asymptotically stable: every point within `1/12` of it
starts a solution on `[0, ∞)`; for every `ε > 0` there is `δ > 0` such that every solution starting
within `δ` of the circle stays within `ε` of it; and every solution starting within `1/12`
converges to it. -/
@[tmio T, powerlib_foundation] theorem orbit_stable_of_stable_law {ω : ℝ → ℝ}
    (hω : ContDiff ℝ 1 ω) :
    (∀ ξ, Metric.infDist ξ (range unitCycle) < 1 / 12 → ∃ x : ℝ → Fin 2 → ℝ, x 0 = ξ ∧
      IsIntegralCurveOn x (fun _ => planarField ω fun s => -(s - 1) ^ 3) (Ici 0)) ∧
    (∀ ε > 0, ∃ δ > 0, ∀ x : ℝ → Fin 2 → ℝ,
      IsIntegralCurveOn x (fun _ => planarField ω fun s => -(s - 1) ^ 3) (Ici 0) →
      Metric.infDist (x 0) (range unitCycle) < δ → ∀ t, 0 ≤ t →
        Metric.infDist (x t) (range unitCycle) < ε) ∧
    ∀ x : ℝ → Fin 2 → ℝ,
      IsIntegralCurveOn x (fun _ => planarField ω fun s => -(s - 1) ^ 3) (Ici 0) →
      Metric.infDist (x 0) (range unitCycle) < 1 / 12 →
        Tendsto (fun t => Metric.infDist (x t) (range unitCycle)) atTop (𝓝 0) := by
  have hug : ∀ s : ℝ, (s - 1) * (-(s - 1) ^ 3) ≤ 0 := fun s => by
    nlinarith [sq_nonneg ((s - 1) ^ 2)]
  have hg : ContDiff ℝ 1 fun s : ℝ => -(s - 1) ^ 3 := ((contDiff_id.sub contDiff_const).pow 3).neg
  refine ⟨fun ξ hξ => exists_solution_planar hω hg hug ?_, fun ε hε => ?_, fun x hx hx0 => ?_⟩
  · have := abs_sqr_sub_one_lt_of_infDist (by norm_num) hξ; linarith
  · refine ⟨min (1 / 12) (ε / 6), by positivity, fun x hx hx0 t ht => ?_⟩
    have h1 := abs_sqr_sub_one_lt_of_infDist (by
      have := min_le_left (1 / 12 : ℝ) (ε / 6); linarith) hx0
    have h2 := abs_sqr_sub_one_le_of_solution hug hx t ht
    calc Metric.infDist (x t) (range unitCycle) ≤ |sqr (x t) - 1| :=
          infDist_le_abs_sqr_sub_one _
      _ ≤ |sqr (x 0) - 1| := h2
      _ < 6 * min (1 / 12) (ε / 6) := h1
      _ ≤ 6 * (ε / 6) := by gcongr; exact min_le_right _ _
      _ = ε := by ring
  · have h1 := abs_sqr_sub_one_lt_of_infDist (by norm_num) hx0
    have hu := tendsto_sqr_of_stable hx (by linarith)
    refine squeeze_zero (fun t => Metric.infDist_nonneg)
      (fun t => infDist_le_abs_sqr_sub_one (x t)) ?_
    simpa using hu.abs


/-! ## The three cubic fields: the multipliers `{1, 1}` decide nothing -/

@[tmio T, powerlib_foundation] theorem contDiff_cubicField (c : ℝ) : ContDiff ℝ 1 (cubicField c) :=
  contDiff_planarField contDiff_const (contDiff_const.mul ((contDiff_id.sub contDiff_const).pow 3))

@[tmio T, powerlib_foundation] theorem cubicField_neg_one :
    cubicField (-1) = planarField (fun _ => 1) fun s => -(s - 1) ^ 3 := by
  simp only [cubicField, neg_one_mul]

/-- A point with `|z|² ≤ 1` has `‖z‖ ≤ 1`. -/
@[tmio T, powerlib_foundation] theorem norm_le_one_of_sqr {z : Fin 2 → ℝ} (hz : sqr z ≤ 1) :
    ‖z‖ ≤ 1 := by
  simp only [sqr] at hz
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;>
    rw [Real.norm_eq_abs] <;> refine abs_le.2 ⟨?_, ?_⟩ <;>
    nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]

/-- **The repelling cycle.** For `ż = J z + (|z|² − 1)³ z` (`ṙ = r (r² − 1)³`) the unit circle is
orbitally unstable: solutions starting arbitrarily close to `(1, 0)`, inside the circle, reach the
distance `1/8` from it. -/
@[tmio T, powerlib_foundation] theorem orbit_unstable_cubicField_one :
    ∃ ε > 0, ∀ δ > 0, ∃ x : ℝ → Fin 2 → ℝ, IsIntegralCurveOn x (fun _ => cubicField 1) (Ici 0) ∧
      ‖x 0 - unitCycle 0‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ Metric.infDist (x t) (range unitCycle) := by
  refine ⟨1 / 8, by norm_num, fun δ hδ => ?_⟩
  set η := min (δ / 2) (1 / 2) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  have hη1 : η ≤ 1 / 2 := min_le_right _ _
  have hηδ : η < δ := (min_le_left _ _).trans_lt (by linarith)
  set ξ : Fin 2 → ℝ := ![1 - η, 0] with hξ
  have hsξ : sqr ξ = (1 - η) ^ 2 := by simp [sqr, hξ]
  have hsξ1 : sqr ξ < 1 := by rw [hsξ]; nlinarith
  have hdec : ∀ z, sqr z < 1 → sqrD z (cubicField 1 z) ≤ 0 := fun z hz => by
    rw [cubicField, sqrD_planarField]
    have h2 : 0 ≤ sqr z := add_nonneg (sq_nonneg _) (sq_nonneg _)
    have h3 : (sqr z - 1) ^ 3 ≤ 0 := by
      have : sqr z - 1 ≤ 0 := by linarith
      nlinarith [sq_nonneg (sqr z - 1)]
    nlinarith
  obtain ⟨x, hx0, hx⟩ := exists_solution_of_lyapunov (contDiff_cubicField 1) hasFDerivAt_sqr
    (c' := 1) (R := 2) (fun z hz => norm_lt_two_of_sqr (by linarith)) hdec hsξ1
  refine ⟨x, hx, ?_, ?_⟩
  · rw [hx0]
    have e : ξ - unitCycle 0 = ![-η, 0] := by
      funext i; fin_cases i <;> simp [hξ, unitCycle]
    rw [e]
    have : ‖(![-η, 0] : Fin 2 → ℝ)‖ = η := by
      refine le_antisymm ((pi_norm_le_iff_of_nonneg hη0.le).2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩))
        ?_
      · simp [abs_of_pos hη0]
      · simp [hη0.le]
      · have := norm_le_pi_norm (![-η, 0] : Fin 2 → ℝ) 0
        simpa [abs_of_pos hη0] using this
    rw [this]; exact hηδ
  have hle := lyapunov_le hx hasFDerivAt_sqr hdec (by rw [hx0]; exact hsξ1)
  -- the solution reaches `|z|² ≤ 1/2`
  have hreach : ∃ t, 0 ≤ t ∧ sqr (x t) ≤ 1 / 2 := by
    by_contra hcon
    push Not at hcon
    set κ := 1 - sqr ξ with hκ
    have hκ0 : 0 < κ := by linarith
    set W : ℝ → ℝ := fun t => sqr (x t) + κ ^ 3 * t with hW
    have hWd : ∀ t, 0 ≤ t → HasDerivWithinAt W (2 * (1 * (sqr (x t) - 1) ^ 3) * sqr (x t) +
        κ ^ 3) (Ici t) t := fun t ht => by
      have h := ((hasDerivWithinAt_sqr hx ht).mono (Ici_subset_Ici.2 ht)).add
        ((hasDerivAt_id t).const_mul (κ ^ 3)).hasDerivWithinAt
      rw [mul_one] at h
      exact h
    have hWc : ContinuousOn W (Ici 0) :=
      (contDiff_sqr.continuous.comp_continuousOn hx.continuousOn).add
        (continuousOn_const.mul continuousOn_id)
    have hWle := le_of_deriv_nonpos_of_lt hWc hWd (c' := W 0 + 1) (fun t ht _ => by
      have h1 := hcon t ht
      have h2 : sqr (x t) ≤ sqr ξ := by rw [← hx0]; exact hle t ht
      have h3 : sqr (x t) - 1 ≤ -κ := by linarith
      have h4 : (sqr (x t) - 1) ^ 3 ≤ -κ ^ 3 := by
        have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ κ) (show κ ≤ -(sqr (x t) - 1) by
          linarith) 3
        nlinarith
      have h5 : (sqr (x t) - 1) ^ 3 < 0 := by nlinarith [pow_pos hκ0 3]
      nlinarith) (by linarith)
    set t₁ := sqr ξ / κ ^ 3 + 1 with ht₁
    have ht₁0 : 0 ≤ t₁ := by
      have : 0 ≤ sqr ξ := add_nonneg (sq_nonneg _) (sq_nonneg _)
      positivity
    have h := hWle t₁ ht₁0
    simp only [hW, mul_zero, add_zero] at h
    have e : κ ^ 3 * t₁ = sqr ξ + κ ^ 3 := by
      rw [ht₁, mul_add, mul_one, mul_div_cancel₀ _ (by positivity)]
    rw [hx0] at h
    have := hcon t₁ ht₁0
    nlinarith [pow_pos hκ0 3]
  obtain ⟨t₁, ht₁, hs₁⟩ := hreach
  refine ⟨t₁, ht₁, ?_⟩
  have hn := norm_le_one_of_sqr (z := x t₁) (by linarith)
  have h := abs_sqr_sub_one_le (x t₁)
  have habs : 1 / 2 ≤ |sqr (x t₁) - 1| := by
    rw [abs_of_neg (by linarith)]; linarith
  have h0 := Metric.infDist_nonneg (x := x t₁) (s := range unitCycle)
  nlinarith

/-- **The neutral cycle.** For the rotation `ż = J z` (the cubic field with `c = 0`) the unit circle
is orbitally stable but not attracting: every point near it starts a solution on `[0, ∞)`, the
solutions starting within `δ` stay within `6 δ` of the circle, and arbitrarily close to it start
solutions that keep a positive distance from it forever (`|z(t)|` is constant). -/
@[tmio T, powerlib_foundation] theorem orbit_neutral_cubicField_zero :
    (∀ ξ, Metric.infDist ξ (range unitCycle) < 1 / 12 → ∃ x : ℝ → Fin 2 → ℝ, x 0 = ξ ∧
      IsIntegralCurveOn x (fun _ => cubicField 0) (Ici 0)) ∧
    (∀ ε > 0, ∃ δ > 0, ∀ x : ℝ → Fin 2 → ℝ, IsIntegralCurveOn x (fun _ => cubicField 0) (Ici 0) →
      Metric.infDist (x 0) (range unitCycle) < δ → ∀ t, 0 ≤ t →
        Metric.infDist (x t) (range unitCycle) < ε) ∧
    ∀ δ > 0, ∃ x : ℝ → Fin 2 → ℝ, IsIntegralCurveOn x (fun _ => cubicField 0) (Ici 0) ∧
      Metric.infDist (x 0) (range unitCycle) < δ ∧
        ∃ c₀ > 0, ∀ t, 0 ≤ t → c₀ ≤ Metric.infDist (x t) (range unitCycle) := by
  have hug : ∀ s : ℝ, (s - 1) * (0 * (s - 1) ^ 3) ≤ 0 := fun s => by simp
  have hg : ContDiff ℝ 1 fun s : ℝ => 0 * (s - 1) ^ 3 :=
    contDiff_const.mul ((contDiff_id.sub contDiff_const).pow 3)
  -- the radius is constant
  have hconst : ∀ x : ℝ → Fin 2 → ℝ, IsIntegralCurveOn x (fun _ => cubicField 0) (Ici 0) →
      ∀ t, 0 ≤ t → sqr (x t) = sqr (x 0) := fun x hx t ht => by
    have hd : ∀ r, 0 ≤ r → HasDerivWithinAt (fun r => sqr (x r)) 0 (Ici r) r := fun r hr => by
      have h := (hasDerivWithinAt_sqr hx hr).mono (Ici_subset_Ici.2 hr)
      simpa using h
    have hc : ContinuousOn (fun r => sqr (x r)) (Ici 0) :=
      contDiff_sqr.continuous.comp_continuousOn hx.continuousOn
    have h1 := le_of_deriv_nonpos_of_lt hc hd (c' := sqr (x 0) + 1) (fun _ _ _ => le_rfl)
      (by linarith) t ht
    have h2 := le_of_deriv_nonpos_of_lt (φ := fun r => -sqr (x r)) hc.neg
      (fun r hr => by
        have h := (hd r hr).neg
        rw [neg_zero] at h
        exact h) (c' := -sqr (x 0) + 1) (fun _ _ _ => le_rfl) (by linarith) t ht
    linarith
  refine ⟨fun ξ hξ => exists_solution_planar contDiff_const hg hug ?_, fun ε hε => ?_,
    fun δ hδ => ?_⟩
  · have := abs_sqr_sub_one_lt_of_infDist (by norm_num) hξ; linarith
  · refine ⟨min (1 / 12) (ε / 6), by positivity, fun x hx hx0 t ht => ?_⟩
    have h1 := abs_sqr_sub_one_lt_of_infDist (by
      have := min_le_left (1 / 12 : ℝ) (ε / 6); linarith) hx0
    calc Metric.infDist (x t) (range unitCycle) ≤ |sqr (x t) - 1| :=
          infDist_le_abs_sqr_sub_one _
      _ = |sqr (x 0) - 1| := by rw [hconst x hx t ht]
      _ < 6 * min (1 / 12) (ε / 6) := h1
      _ ≤ 6 * (ε / 6) := by gcongr; exact min_le_right _ _
      _ = ε := by ring
  · set η := min (δ / 2) (1 / 8) with hη
    have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
    have hη1 : η ≤ 1 / 8 := min_le_right _ _
    have hηδ : η < δ := (min_le_left _ _).trans_lt (by linarith)
    set ξ : Fin 2 → ℝ := ![1 + η, 0] with hξ
    have hsξ : sqr ξ = (1 + η) ^ 2 := by simp [sqr, hξ]
    obtain ⟨x, hx0, hx⟩ := exists_solution_planar contDiff_const hg hug (ξ := ξ) (by
      rw [hsξ, abs_lt]; constructor <;> nlinarith)
    refine ⟨x, hx, ?_, (2 * η + η ^ 2) / 6, by positivity, fun t ht => ?_⟩
    · rw [hx0]
      refine (Metric.infDist_le_dist_of_mem (mem_range_self 0)).trans_lt ?_
      rw [dist_eq_norm]
      have e : ξ - unitCycle 0 = ![η, 0] := by
        funext i; fin_cases i <;> simp [hξ, unitCycle]
      rw [e]
      have : ‖(![η, 0] : Fin 2 → ℝ)‖ ≤ η :=
        (pi_norm_le_iff_of_nonneg hη0.le).2 (Fin.forall_fin_two.2
          ⟨by simp [abs_of_pos hη0], by simp [hη0.le]⟩)
      exact this.trans_lt hηδ
    · have hs := hconst x hx t ht
      rw [hx0, hsξ] at hs
      have hn : ‖x t‖ ≤ 2 := (norm_lt_two_of_sqr (by rw [hs]; nlinarith)).le
      have h := abs_sqr_sub_one_le (x t)
      have habs : |sqr (x t) - 1| = 2 * η + η ^ 2 := by
        rw [hs, abs_of_pos (by nlinarith)]; ring
      have h0 := Metric.infDist_nonneg (x := x t) (s := range unitCycle)
      rw [habs] at h
      nlinarith


/-! ## An attracting cycle without asymptotic phase -/

/-- The twisted field `ż = |z|² J z − (|z|² − 1)³ z`: in polar coordinates `θ̇ = r²`,
`ṙ = −r (r² − 1)³` — the angular speed grows with the radius. -/
def twistField : (Fin 2 → ℝ) → Fin 2 → ℝ := planarField id fun s => -(s - 1) ^ 3

/-- The first coordinate of `z(r)` in the frame rotating with `unitCycle(· + θ)`. -/
def frame0 (θ : ℝ) (x : ℝ → Fin 2 → ℝ) (r : ℝ) : ℝ :=
  Real.cos (r + θ) * x r 0 + Real.sin (r + θ) * x r 1

/-- The second coordinate of `z(r)` in the frame rotating with `unitCycle(· + θ)`. -/
def frame1 (θ : ℝ) (x : ℝ → Fin 2 → ℝ) (r : ℝ) : ℝ :=
  -Real.sin (r + θ) * x r 0 + Real.cos (r + θ) * x r 1

/-- **The phase drift.** Along a solution of the twisted field, the angle
`α = arctan(w₁/w₀)` of `z(t)` in the frame rotating with `unitCycle(· + θ)` (where `w₀ ≠ 0`) has
the derivative `α̇ = |z|² − 1`: the solution turns faster than the cycle outside it and slower
inside. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_frame_arctan {x : ℝ → Fin 2 → ℝ}
    (hx : IsIntegralCurveOn x (fun _ => twistField) (Ici 0)) (θ : ℝ) {t : ℝ} (ht : 0 < t)
    (hw : frame0 θ x t ≠ 0) :
    HasDerivAt (fun r => Real.arctan (frame1 θ x r / frame0 θ x r)) (sqr (x t) - 1) t := by
  have hxt : HasDerivAt x (twistField (x t)) t := (hx t ht.le).hasDerivAt (Ici_mem_nhds ht)
  have hx0 : HasDerivAt (fun r => x r 0) (twistField (x t) 0) t := hasDerivAt_pi.1 hxt 0
  have hx1 : HasDerivAt (fun r => x r 1) (twistField (x t) 1) t := hasDerivAt_pi.1 hxt 1
  have hc : HasDerivAt (fun r => Real.cos (r + θ)) (-Real.sin (t + θ)) t := by
    simpa using (Real.hasDerivAt_cos (t + θ)).comp_add_const t θ
  have hs : HasDerivAt (fun r => Real.sin (r + θ)) (Real.cos (t + θ)) t := by
    simpa using (Real.hasDerivAt_sin (t + θ)).comp_add_const t θ
  have hw0 := (hc.mul hx0).add (hs.mul hx1)
  have hw1 := (hs.neg.mul hx0).add (hc.mul hx1)
  have hq := (hw1.div hw0 hw).arctan
  refine hq.congr_deriv ?_
  have hF0 : twistField (x t) 0 = sqr (x t) * -x t 1 + -(sqr (x t) - 1) ^ 3 * x t 0 := by
    rw [twistField, planarField_apply_zero]; rfl
  have hF1 : twistField (x t) 1 = sqr (x t) * x t 0 + -(sqr (x t) - 1) ^ 3 * x t 1 := by
    rw [twistField, planarField_apply_one]; rfl
  have hw0' : frame0 θ x t = Real.cos (t + θ) * x t 0 + Real.sin (t + θ) * x t 1 := rfl
  rw [hw0'] at hw
  simp only [Pi.mul_apply, Pi.add_apply, Pi.neg_apply, Pi.div_apply, hF0, hF1]
  have key : ∀ A B D0 D1 : ℝ, A ≠ 0 → D1 * A - B * D0 = (sqr (x t) - 1) * (A ^ 2 + B ^ 2) →
      1 / (1 + (B / A) ^ 2) * ((D1 * A - B * D0) / A ^ 2) = sqr (x t) - 1 := by
    intro A B D0 D1 hA h
    have hAB : A ^ 2 + B ^ 2 ≠ 0 := by positivity
    rw [h]
    field_simp
  exact key _ _ _ _ hw (by ring)


/-- Close to `unitCycle(t + θ)`, the first coordinate in the rotating frame is close to `1`. -/
@[tmio T, powerlib_foundation] theorem abs_frame0_sub_one_le (θ : ℝ) (x : ℝ → Fin 2 → ℝ)
    (t : ℝ) : |frame0 θ x t - 1| ≤ 2 * ‖x t - unitCycle (t + θ)‖ := by
  have h0 := norm_le_pi_norm (x t - unitCycle (t + θ)) 0
  have h1 := norm_le_pi_norm (x t - unitCycle (t + θ)) 1
  simp only [Pi.sub_apply, Real.norm_eq_abs] at h0 h1
  have e0 : unitCycle (t + θ) 0 = Real.cos (t + θ) := rfl
  have e1 : unitCycle (t + θ) 1 = Real.sin (t + θ) := rfl
  rw [e0] at h0; rw [e1] at h1
  have hcs := Real.cos_sq_add_sin_sq (t + θ)
  have e : frame0 θ x t - 1 = Real.cos (t + θ) * (x t 0 - Real.cos (t + θ)) +
      Real.sin (t + θ) * (x t 1 - Real.sin (t + θ)) := by
    rw [frame0]; linear_combination hcs
  rw [e]
  calc |Real.cos (t + θ) * (x t 0 - Real.cos (t + θ)) +
        Real.sin (t + θ) * (x t 1 - Real.sin (t + θ))|
      ≤ |Real.cos (t + θ)| * |x t 0 - Real.cos (t + θ)| +
        |Real.sin (t + θ)| * |x t 1 - Real.sin (t + θ)| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ 1 * ‖x t - unitCycle (t + θ)‖ + 1 * ‖x t - unitCycle (t + θ)‖ := by
        gcongr
        · exact Real.abs_cos_le_one _
        · exact Real.abs_sin_le_one _
    _ = 2 * ‖x t - unitCycle (t + θ)‖ := by ring

/-- **The twisted cycle has no asymptotic phase.** Let `x` be a solution on `[0, ∞)` of
`ż = |z|² J z − (|z|² − 1)³ z` starting off the unit circle with `| |x(0)|² − 1 | < 1/2`. Then
`x(t) − unitCycle(t + θ)` does not tend to `0` for any phase `θ`, although `x` converges to the
circle (`orbit_stable_of_stable_law`). In the frame rotating with `unitCycle(· + θ)` the angle
of `x` moves by `α̇ = u = |x|² − 1`, `u` keeps its sign, and `1/u − 3α` is monotone
(`(1/u)˙ = 2u(1 + u)`), so a bounded `α` would keep `|u|` away from `0`: the phase drifts without
bound (like `√t`). -/
@[tmio T, powerlib_foundation] theorem not_tendsto_twistField {x : ℝ → Fin 2 → ℝ}
    (hx : IsIntegralCurveOn x (fun _ => twistField) (Ici 0)) (h0 : |sqr (x 0) - 1| < 1 / 2)
    (hne : sqr (x 0) ≠ 1) (θ : ℝ) :
    ¬ Tendsto (fun t => x t - unitCycle (t + θ)) atTop (𝓝 0) := by
  intro hT
  have hug : ∀ s : ℝ, (s - 1) * (-(s - 1) ^ 3) ≤ 0 := fun s => by
    nlinarith [sq_nonneg ((s - 1) ^ 2)]
  have hb := abs_sqr_sub_one_le_of_solution hug hx
  have hlim : Tendsto (fun t => sqr (x t) - 1) atTop (𝓝 0) := tendsto_sqr_of_stable hx h0
  have huc : ContinuousOn (fun t => sqr (x t) - 1) (Ici 0) :=
    (contDiff_sqr.continuous.comp_continuousOn hx.continuousOn).sub continuousOn_const
  have hbd : ∀ t, 0 ≤ t → |sqr (x t) - 1| < 1 / 2 := fun t ht => (hb t ht).trans_lt h0
  -- the squared distance stays positive
  set V₀ := (sqr (x 0) - 1) ^ 2 with hV₀
  have hV₀0 : 0 < V₀ := by
    have : sqr (x 0) - 1 ≠ 0 := sub_ne_zero.2 hne
    positivity
  have hnz : ∀ t, 0 ≤ t → sqr (x t) - 1 ≠ 0 := by
    set Z : ℝ → ℝ := fun t => -((sqr (x t) - 1) ^ 2 * Real.exp (6 * V₀ * t)) with hZ
    have hZd : ∀ t, 0 ≤ t → HasDerivWithinAt Z (-((2 * (sqr (x t) - 1) *
        (2 * -(sqr (x t) - 1) ^ 3 * sqr (x t))) * Real.exp (6 * V₀ * t) +
        (sqr (x t) - 1) ^ 2 * (Real.exp (6 * V₀ * t) * (6 * V₀)))) (Ici t) t := fun t ht => by
      have h1 := ((hasDerivWithinAt_sqr hx ht).sub_const 1).pow 2
      have h2 := ((hasDerivAt_id t).const_mul (6 * V₀)).exp
      have h3 := (h1.mul h2.hasDerivWithinAt).neg
      refine (h3.congr_deriv ?_).mono (Ici_subset_Ici.2 ht)
      simp only [Pi.pow_apply, Nat.cast_ofNat, id, mul_one]
      ring
    have hZc : ContinuousOn Z (Ici 0) :=
      ((huc.pow 2).mul (Continuous.continuousOn (by fun_prop))).neg
    have hZle := le_of_deriv_nonpos_of_lt hZc hZd (c' := Z 0 + 1) (fun t ht _ => by
      have h1 := hbd t ht
      have h2 : (sqr (x t) - 1) ^ 2 ≤ V₀ := by
        have := hb t ht
        rw [hV₀]; exact sq_le_sq.2 this
      have h3 := abs_lt.1 h1
      have he := Real.exp_pos (6 * V₀ * t)
      have hs : sqr (x t) ≤ 3 / 2 := by linarith
      have hs0 : 0 ≤ sqr (x t) := add_nonneg (sq_nonneg _) (sq_nonneg _)
      have h4 : 0 ≤ (sqr (x t) - 1) ^ 2 * (6 * V₀ - 4 * (sqr (x t) - 1) ^ 2 * sqr (x t)) := by
        apply mul_nonneg (sq_nonneg _)
        nlinarith [sq_nonneg (sqr (x t) - 1)]
      nlinarith [mul_nonneg h4 he.le]) (by linarith)
    intro t ht h
    have hZt : Z t = 0 := by simp only [hZ]; rw [h]; ring
    have hZ0 : Z 0 = -V₀ := by simp only [hZ, mul_zero, Real.exp_zero, mul_one]; rw [hV₀]
    have := hZle t ht
    linarith
  -- the sign of `u` is constant
  have hsign : ∀ t, 0 ≤ t → 0 < (sqr (x 0) - 1) * (sqr (x t) - 1) := fun t ht => by
    rcases lt_or_gt_of_ne (hnz 0 le_rfl) with hneg | hpos
    · have : sqr (x t) - 1 < 0 := by
        by_contra hc
        push Not at hc
        obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc ht (huc.mono Icc_subset_Ici_self)
          ⟨hneg.le, hc⟩
        exact hnz r hr.1 hr0
      nlinarith
    · have : 0 < sqr (x t) - 1 := by
        by_contra hc
        push Not at hc
        obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' ht (huc.mono Icc_subset_Ici_self)
          ⟨hc, hpos.le⟩
        exact hnz r hr.1 hr0
      nlinarith
  -- the rotating frame
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hT (1 / 4) (by norm_num)
  set t₁ := max N 1 with ht₁
  have ht₁0 : 0 < t₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hw : ∀ t, t₁ ≤ t → 1 / 2 < frame0 θ x t := fun t ht => by
    have h := hN t ((le_max_left _ _).trans ht)
    rw [dist_eq_norm, sub_zero] at h
    have := abs_le.1 (abs_frame0_sub_one_le θ x t)
    linarith
  set α : ℝ → ℝ := fun r => Real.arctan (frame1 θ x r / frame0 θ x r) with hα
  set ψ : ℝ → ℝ := fun r => (sqr (x r) - 1)⁻¹ - 3 * α r with hψ
  have hψd : ∀ t, t₁ ≤ t → HasDerivAt ψ ((sqr (x t) - 1) * (2 * (sqr (x t) - 1) - 1)) t :=
    fun t ht => by
      have htpos : 0 < t := ht₁0.trans_le ht
      have hs := ((hasDerivWithinAt_sqr hx htpos.le).hasDerivAt (Ici_mem_nhds htpos)).sub_const 1
      have hinv := hs.inv (hnz t htpos.le)
      have ha := hasDerivAt_frame_arctan hx θ htpos (ne_of_gt ((by norm_num : (0 : ℝ) < 1 / 2).trans
        (hw t ht)))
      refine (hinv.sub (ha.const_mul 3)).congr_deriv ?_
      have hu0 := hnz t htpos.le
      field_simp
      ring
  have hψc : ∀ t, t₁ ≤ t → ContinuousAt ψ t := fun t ht => (hψd t ht).continuousAt
  -- the monotone function `ψ(· + t₁)`
  set φ : ℝ → ℝ := fun r => ψ (r + t₁) with hφ
  have hφd : ∀ r, 0 ≤ r → HasDerivWithinAt φ ((sqr (x (r + t₁)) - 1) *
      (2 * (sqr (x (r + t₁)) - 1) - 1)) (Ici r) r := fun r hr =>
    ((hψd (r + t₁) (by linarith)).comp_add_const r t₁).hasDerivWithinAt
  have hφc : ContinuousOn φ (Ici 0) := fun r hr =>
    (ContinuousAt.comp (f := fun r => r + t₁) (hψc (r + t₁) (by linarith [mem_Ici.1 hr]))
      (by fun_prop)).continuousWithinAt
  have hαb : ∀ r, |α r| < Real.pi / 2 := fun r =>
    abs_lt.2 ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  -- `|u|` stays away from `0`
  obtain ⟨M, hM0, hM⟩ : ∃ M > 0, ∀ r, 0 ≤ r → |(sqr (x (r + t₁)) - 1)⁻¹| ≤ M := by
    rcases lt_or_gt_of_ne (hnz 0 le_rfl) with hneg | hpos
    · -- `u < 0`: `ψ` does not decrease
      have hle := le_of_deriv_nonpos_of_lt (φ := fun r => -φ r) hφc.neg
        (fun r hr => (hφd r hr).neg) (c' := -φ 0 + 1) (fun r hr _ => by
          have h1 : sqr (x (r + t₁)) - 1 < 0 := by
            have := hsign (r + t₁) (by linarith); nlinarith
          nlinarith) (by linarith)
      refine ⟨|ψ t₁| + 3 * Real.pi / 2 + 1, by positivity, fun r hr => ?_⟩
      have h1 := hle r hr
      simp only [hφ, hψ, zero_add] at h1
      have h2 := hαb (r + t₁)
      have h3 : sqr (x (r + t₁)) - 1 < 0 := by
        have := hsign (r + t₁) (by linarith); nlinarith
      have h4 : (sqr (x (r + t₁)) - 1)⁻¹ < 0 := inv_lt_zero.2 h3
      rw [abs_of_neg h4]
      have := abs_lt.1 h2
      have := le_abs_self (ψ t₁)
      have := neg_abs_le (ψ t₁)
      simp only [hψ] at *
      linarith
    · -- `u > 0`: `ψ` does not increase
      have hle := le_of_deriv_nonpos_of_lt hφc hφd (c' := φ 0 + 1) (fun r hr _ => by
          have h1 : 0 < sqr (x (r + t₁)) - 1 := by
            have := hsign (r + t₁) (by linarith); nlinarith
          have h2 := abs_lt.1 (hbd (r + t₁) (by linarith))
          nlinarith) (by linarith)
      refine ⟨|ψ t₁| + 3 * Real.pi / 2 + 1, by positivity, fun r hr => ?_⟩
      have h1 := hle r hr
      simp only [hφ, hψ, zero_add] at h1
      have h2 := hαb (r + t₁)
      have h3 : 0 < sqr (x (r + t₁)) - 1 := by
        have := hsign (r + t₁) (by linarith); nlinarith
      have h4 : 0 < (sqr (x (r + t₁)) - 1)⁻¹ := inv_pos.2 h3
      rw [abs_of_pos h4]
      have := abs_lt.1 h2
      have := le_abs_self (ψ t₁)
      have := neg_abs_le (ψ t₁)
      simp only [hψ] at *
      linarith
  -- but `u → 0`
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hlim (1 / M) (by positivity)
  set r := max N₂ t₁ with hr
  have h1 := hN₂ r (le_max_left _ _)
  rw [Real.dist_eq, sub_zero] at h1
  have h2 := hM (r - t₁) (by linarith [le_max_right N₂ t₁])
  rw [sub_add_cancel] at h2
  have h3 : 0 < |sqr (x r) - 1| := abs_pos.2 (hnz r (by linarith [le_max_right N₂ t₁]))
  rw [abs_inv] at h2
  have h4 : 1 / M ≤ |sqr (x r) - 1| := by
    rw [div_le_iff₀ hM0]
    calc 1 = |sqr (x r) - 1|⁻¹ * |sqr (x r) - 1| := (inv_mul_cancel₀ h3.ne').symm
      _ ≤ M * |sqr (x r) - 1| := mul_le_mul_of_nonneg_right h2 h3.le
      _ = |sqr (x r) - 1| * M := mul_comm _ _
  linarith


/-- **The twisted cycle is attracting, without asymptotic phase, and critical.** The unit circle is
a `2π`-periodic orbit of the twisted field `ż = |z|² J z − (|z|² − 1)³ z`; it is orbitally
asymptotically stable (`orbit_stable_of_stable_law`), no solution starting off it within
`| |z|² − 1 | < 1/2` has an asymptotic phase (`not_tendsto_twistField`), and accordingly its
multipliers are critical: not `1` simple with all others strictly inside the unit circle (which
would give an asymptotic phase, `AndronovWitt.andronov_witt_local`), and none outside (which would
make the orbit orbitally unstable, `AndronovWitt.orbit_unstable_local`). -/
@[tmio T, powerlib_foundation] theorem twistField_critical :
    (∀ t, HasDerivAt unitCycle (twistField (unitCycle t)) t) ∧
    ¬ (Polynomial.rootMultiplicity 1
        (monodromy (variationalMatrix twistField unitCycle) (2 * Real.pi) 0).charpoly = 1 ∧
      ∀ μ ∈ spectrum ℂ ((monodromy (variationalMatrix twistField unitCycle)
        (2 * Real.pi) 0).map (algebraMap ℝ ℂ)), μ ≠ 1 → ‖μ‖ < 1) ∧
    ∀ μ ∈ spectrum ℂ ((monodromy (variationalMatrix twistField unitCycle)
      (2 * Real.pi) 0).map (algebraMap ℝ ℂ)), ‖μ‖ ≤ 1 := by
  have hω : ContDiff ℝ 1 (id : ℝ → ℝ) := contDiff_id
  have hg : ContDiff ℝ 1 fun s : ℝ => -(s - 1) ^ 3 := ((contDiff_id.sub contDiff_const).pow 3).neg
  have hF : ContDiff ℝ 1 twistField := contDiff_planarField hω hg
  have hxs : ∀ t, HasDerivAt unitCycle (twistField (unitCycle t)) t :=
    hasDerivAt_unitCycle (ω := id) (g := fun s => -(s - 1) ^ 3) rfl (by norm_num)
  have hne : twistField (unitCycle 0) ≠ 0 :=
    planarField_unitCycle_zero_ne (ω := id) (g := fun s => -(s - 1) ^ 3) rfl (by norm_num)
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  obtain ⟨hex, hst, -⟩ := orbit_stable_of_stable_law hω
  -- the points `(1 + η, 0)`
  have hpt : ∀ η, 0 < η → η ≤ 1 / 24 → Metric.infDist (![1 + η, 0] : Fin 2 → ℝ)
      (range unitCycle) < 2 * η ∧ ‖(![1 + η, 0] : Fin 2 → ℝ) - unitCycle 0‖ ≤ η ∧
      |sqr (![1 + η, 0] : Fin 2 → ℝ) - 1| < 1 / 2 ∧ sqr (![1 + η, 0] : Fin 2 → ℝ) ≠ 1 :=
    fun η hη hη1 => by
      have hsq : sqr (![1 + η, 0] : Fin 2 → ℝ) = (1 + η) ^ 2 := by simp [sqr]
      have hd : ‖(![1 + η, 0] : Fin 2 → ℝ) - unitCycle 0‖ ≤ η := by
        have e : (![1 + η, 0] : Fin 2 → ℝ) - unitCycle 0 = ![η, 0] := by
          funext i; fin_cases i <;> simp [unitCycle]
        rw [e]
        exact (pi_norm_le_iff_of_nonneg hη.le).2 (Fin.forall_fin_two.2
          ⟨by simp [abs_of_pos hη], by simp [hη.le]⟩)
      refine ⟨(Metric.infDist_le_dist_of_mem (mem_range_self 0)).trans_lt ?_, hd, ?_, ?_⟩
      · rw [dist_eq_norm]; linarith
      · rw [hsq, abs_lt]; constructor <;> nlinarith
      · rw [hsq]; nlinarith
  refine ⟨hxs, fun ⟨h1, hμ⟩ => ?_, fun μ hμ => ?_⟩
  · -- all inside would give an asymptotic phase
    obtain ⟨δ, C, lam, hδ, hC, hlam, hexist, hph, -⟩ :=
      AndronovWitt.andronov_witt_local hF hxs hT unitCycle_periodic hne h1 hμ
    set η := min (δ / 4) (1 / 24) with hη
    have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
    obtain ⟨hinf, hd, hs, hs1⟩ := hpt η hη0 (min_le_right _ _)
    have hηδ : 2 * η < δ := by have := min_le_left (δ / 4) (1 / 24); linarith
    obtain ⟨x, hx0, hx⟩ := hexist _ (hinf.trans hηδ)
    obtain ⟨θ, -, hθ⟩ := hph 0 x hx (by rw [hx0]; linarith)
    refine not_tendsto_twistField hx (by rwa [hx0]) (by rwa [hx0]) θ ?_
    have hlim : Tendsto (fun t => C * Real.exp (-(lam * t)) * ‖x 0 - unitCycle 0‖) atTop
        (𝓝 0) := by
      have h := ((Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hlam)).inv_tendsto_atTop)
      have h' : Tendsto (fun t => Real.exp (-(lam * t))) atTop (𝓝 0) := by
        refine h.congr fun t => ?_
        simp [Real.exp_neg]
      simpa using (h'.const_mul C).mul_const ‖x 0 - unitCycle 0‖
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 0] with t ht
    have := hθ t ht
    rwa [add_zero] at this
  · -- one outside would make the orbit orbitally unstable
    by_contra hcon
    push Not at hcon
    obtain ⟨ε, hε, hesc⟩ :=
      AndronovWitt.orbit_unstable_local hF hxs hT unitCycle_periodic hne hμ hcon
    obtain ⟨δ, hδ, hb⟩ := hst ε hε
    have hGd : ∀ (t : ℝ) x, DifferentiableAt ℝ ((fun _ : ℝ => twistField) t) x :=
      fun _ x => (hF.differentiable one_ne_zero) x
    have hD : Continuous fun q : ℝ × (Fin 2 → ℝ) => fderiv ℝ ((fun _ : ℝ => twistField) q.1) q.2 :=
      (hF.continuous_fderiv one_ne_zero).comp continuous_snd
    obtain ⟨x, t, ht, hxI, hx0, hxt⟩ := hesc (min δ (1 / 12)) (lt_min hδ (by norm_num))
    have hinf0 : Metric.infDist (x 0) (range unitCycle) < min δ (1 / 12) :=
      (Metric.infDist_le_dist_of_mem (mem_range_self 0)).trans_lt (by rwa [dist_eq_norm])
    obtain ⟨y, hy0, hy⟩ := hex (x 0) (hinf0.trans_le (min_le_right _ _))
    have hxy := LocalField.eqOn_of_isIntegralCurveOn_Icc_of_fderiv hGd hD hxI
      (hy.mono Icc_subset_Ici_self) hy0.symm ⟨ht, le_rfl⟩
    have := hb y hy (by rw [hy0]; exact hinf0.trans_le (min_le_left _ _)) t ht
    rw [← hxy] at this
    linarith


/-- **In the critical case the multipliers decide nothing.** The cubic fields
`ż = J z + c (|z|² − 1)³ z` (`ṙ = c r (r² − 1)³`, `θ̇ = 1`) all have the unit circle as a
`2π`-periodic orbit with the same monodromy, the identity (the multipliers `{1, 1}`). For `c = −1`
the orbit is orbitally asymptotically stable, for `c = 1` it is orbitally unstable, and for
`c = 0` it is orbitally stable but not attracting. -/
@[tmio T, powerlib_foundation] theorem multipliers_do_not_decide :
    (∀ c t : ℝ, HasDerivAt unitCycle (cubicField c (unitCycle t)) t) ∧
    (∀ c : ℝ, monodromy (variationalMatrix (cubicField c) unitCycle) (2 * Real.pi) 0 = 1) ∧
    ((∀ ε > 0, ∃ δ > 0, ∀ x : ℝ → Fin 2 → ℝ,
        IsIntegralCurveOn x (fun _ => cubicField (-1)) (Ici 0) →
        Metric.infDist (x 0) (range unitCycle) < δ → ∀ t, 0 ≤ t →
          Metric.infDist (x t) (range unitCycle) < ε) ∧
      ∀ x : ℝ → Fin 2 → ℝ, IsIntegralCurveOn x (fun _ => cubicField (-1)) (Ici 0) →
        Metric.infDist (x 0) (range unitCycle) < 1 / 12 →
          Tendsto (fun t => Metric.infDist (x t) (range unitCycle)) atTop (𝓝 0)) ∧
    (∃ ε > 0, ∀ δ > 0, ∃ x : ℝ → Fin 2 → ℝ,
      IsIntegralCurveOn x (fun _ => cubicField 1) (Ici 0) ∧
      ‖x 0 - unitCycle 0‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ Metric.infDist (x t) (range unitCycle)) ∧
    ((∀ ε > 0, ∃ δ > 0, ∀ x : ℝ → Fin 2 → ℝ,
        IsIntegralCurveOn x (fun _ => cubicField 0) (Ici 0) →
        Metric.infDist (x 0) (range unitCycle) < δ → ∀ t, 0 ≤ t →
          Metric.infDist (x t) (range unitCycle) < ε) ∧
      ∀ δ > 0, ∃ x : ℝ → Fin 2 → ℝ, IsIntegralCurveOn x (fun _ => cubicField 0) (Ici 0) ∧
        Metric.infDist (x 0) (range unitCycle) < δ ∧
          ∃ c₀ > 0, ∀ t, 0 ≤ t → c₀ ≤ Metric.infDist (x t) (range unitCycle)) := by
  obtain ⟨-, hst, hatt⟩ := orbit_stable_of_stable_law (ω := fun _ => 1) contDiff_const
  obtain ⟨-, hst0, hna⟩ := orbit_neutral_cubicField_zero
  refine ⟨fun c t => hasDerivAt_unitCycle (ω := fun _ => 1) rfl (by simp) t,
    monodromy_cubicField, ⟨?_, ?_⟩, orbit_unstable_cubicField_one, hst0, hna⟩
  · rw [cubicField_neg_one]; exact hst
  · rw [cubicField_neg_one]; exact hatt

end powerlib.Periodic.CriticalCycles
