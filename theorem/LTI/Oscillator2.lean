import theorem.LTI.Plant

/-! # Closed-form flow of a real 2×2 system with complex eigenvalues (foundation)

For a real matrix `A : Matrix (Fin 2) (Fin 2) ℝ` with `tr A = −2σ`, `det A = σ² + ω_d²` and
`ω_d ≠ 0` (eigenvalues `−σ ± j ω_d`), the explicit candidate

`osc2 A σ ω_d p t = e^{−σ t} (cos(ω_d t) p + (sin(ω_d t)/ω_d) (A + σ I) p)`

solves `ẏ = A y`, `y(0) = p` (`hasDerivAt_osc2`, `osc2_zero`). The proof uses only the 2×2
Cayley–Hamilton identity `(A + σ I)² = −ω_d² I` (`shift_sq_mulVec`). Uniqueness of global
solutions (Mathlib `ODE_solution_unique_univ`) then gives the flow law
`osc2 p (s + t) = osc2 (osc2 p s) t` (`osc2_add`), and the half-period law
`osc2 p (t + π/ω_d) = −e^{−σπ/ω_d} osc2 p t` (`osc2_add_half_period`) is a direct trigonometric
identity.

`trajectory_eq_osc2` connects this to any two-state linear plant (`Linear.Plant 2 p`) whose
state matrix has that trace and determinant: every forward solution from `t = 0` under a constant
input `u` with equilibrium `e` is `e + osc2 A σ ω_d (x 0 − e) t` for `t ≥ 0` (explicit candidate
+ uniqueness of solution segments of the affine linear field, `Linear.trajectory_unique`). This
is the time-domain closed form used by the frequency-nadir results; no Laplace inversion is
imported.

`one_add_ratio_sin_le_exp` is the elementary inequality
`e^{−σu}(cos(ω_d u) + (σ/ω_d) sin(ω_d u)) ≤ 1` for `σ ≥ 0`, `ω_d > 0`, `u ≥ 0`, which bounds
every later excursion of a damped response by its first extremum.

Family and connection conclusions. This module is foundation only: `osc2` is an explicit closed
form, and `trajectory_eq_osc2` is a generic implication about an arbitrary caller-supplied
two-state plant (Rules §3). It defines no family. The former `@[powerlib_domain]` label of
`trajectory_eq_osc2` (stated for an arbitrary `LTI.Model`) is now `@[powerlib_foundation]`.
-/

noncomputable section
namespace powerlib.LTI
open Set Filter Matrix
open scoped Topology

/-- Closed-form solution of `ẏ = A y`, `y(0) = p`, when `A` has eigenvalues `−σ ± j ω_d`. -/
def osc2 (A : Matrix (Fin 2) (Fin 2) ℝ) (σ ωd : ℝ) (p : Fin 2 → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  Real.exp (-(σ * t)) •
    (Real.cos (ωd * t) • p + (Real.sin (ωd * t) / ωd) • ((A + σ • 1) *ᵥ p))

variable {A : Matrix (Fin 2) (Fin 2) ℝ} {σ ωd : ℝ}

/-- 2×2 Cayley–Hamilton: `A² = tr A · A − det A · I`. -/
@[powerlib_foundation] theorem mul_self_fin_two (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

/-- `(A + σ I)² = −ω_d² I` when `tr A = −2σ`, `det A = σ² + ω_d²`. -/
@[powerlib_foundation] theorem shift_sq_mulVec (htr : A.trace = -2 * σ)
    (hdet : A.det = σ ^ 2 + ωd ^ 2) (p : Fin 2 → ℝ) :
    (A + σ • 1) *ᵥ ((A + σ • 1) *ᵥ p) = -(ωd ^ 2) • p := by
  rw [Matrix.mulVec_mulVec]
  have h : (A + σ • 1) * (A + σ • 1) = -(ωd ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    have hA := mul_self_fin_two A
    rw [htr, hdet] at hA
    calc (A + σ • 1) * (A + σ • 1) = A * A + (2 * σ) • A + σ ^ 2 • (1 : Matrix _ _ ℝ) := by
          simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
            Matrix.mul_one, smul_smul]
          module
      _ = _ := by rw [hA]; module
  rw [h, Matrix.smul_mulVec, Matrix.one_mulVec]

@[simp, powerlib_foundation] theorem osc2_zero (A : Matrix (Fin 2) (Fin 2) ℝ) (σ ωd : ℝ)
    (p : Fin 2 → ℝ) : osc2 A σ ωd p 0 = p := by
  simp [osc2]

/-- `osc2` solves `ẏ = A y`. -/
@[powerlib_foundation] theorem hasDerivAt_osc2 (htr : A.trace = -2 * σ)
    (hdet : A.det = σ ^ 2 + ωd ^ 2) (hωd : ωd ≠ 0) (p : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (osc2 A σ ωd p) (A *ᵥ osc2 A σ ωd p t) t := by
  set q := (A + σ • 1) *ᵥ p with hq
  have hAp : A *ᵥ p = q - σ • p := by
    rw [hq, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]; abel
  have hAq : A *ᵥ q = -(ωd ^ 2) • p - σ • q := by
    have h := shift_sq_mulVec htr hdet p
    rw [← hq, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    rw [eq_sub_iff_add_eq, h]
  have he : HasDerivAt (fun s => Real.exp (-(σ * s))) (Real.exp (-(σ * t)) * (-σ)) t := by
    have := ((hasDerivAt_id t).const_mul σ).neg.exp
    simpa using this
  have hc : HasDerivAt (fun s => Real.cos (ωd * s)) (-Real.sin (ωd * t) * ωd) t := by
    have := ((hasDerivAt_id t).const_mul ωd).cos
    simpa using this
  have hs : HasDerivAt (fun s => Real.sin (ωd * s) / ωd) (Real.cos (ωd * t) * ωd / ωd) t := by
    have := (((hasDerivAt_id t).const_mul ωd).sin).div_const ωd
    simpa using this
  have h := he.smul ((hc.smul_const p).add (hs.smul_const q))
  convert h using 1
  · rfl
  simp only [osc2, ← hq, Matrix.mulVec_smul, Matrix.mulVec_add, hAp, hAq]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

@[powerlib_foundation] private theorem lipschitz_mulVec (A : Matrix (Fin 2) (Fin 2) ℝ) :
    LipschitzWith ‖LinearMap.toContinuousLinearMap (Matrix.toLin' A)‖₊
      (fun y : Fin 2 → ℝ => A *ᵥ y) := by
  have h := (LinearMap.toContinuousLinearMap (Matrix.toLin' A)).lipschitzWith
  have hf : (fun y : Fin 2 → ℝ => A *ᵥ y) =
      ⇑(LinearMap.toContinuousLinearMap (Matrix.toLin' A)) := by
    funext y; simp
  rw [hf]; exact h

/-- Flow law: `osc2 p (s + t) = osc2 (osc2 p s) t`. -/
@[powerlib_foundation] theorem osc2_add (htr : A.trace = -2 * σ)
    (hdet : A.det = σ ^ 2 + ωd ^ 2) (hωd : ωd ≠ 0) (p : Fin 2 → ℝ) (s t : ℝ) :
    osc2 A σ ωd p (s + t) = osc2 A σ ωd (osc2 A σ ωd p s) t := by
  have hf : ∀ u, HasDerivAt (fun u => osc2 A σ ωd p (s + u))
      (A *ᵥ osc2 A σ ωd p (s + u)) u ∧ osc2 A σ ωd p (s + u) ∈ (univ : Set (Fin 2 → ℝ)) := by
    intro u
    refine ⟨?_, trivial⟩
    exact HasDerivAt.comp_const_add s u (hasDerivAt_osc2 htr hdet hωd p (s + u))
  have hg : ∀ u, HasDerivAt (fun u => osc2 A σ ωd (osc2 A σ ωd p s) u)
      (A *ᵥ osc2 A σ ωd (osc2 A σ ωd p s) u) u ∧
        osc2 A σ ωd (osc2 A σ ωd p s) u ∈ (univ : Set (Fin 2 → ℝ)) :=
    fun u => ⟨hasDerivAt_osc2 htr hdet hωd _ u, trivial⟩
  have heq := ODE_solution_unique_univ (v := fun _ y => A *ᵥ y) (s := fun _ => univ)
    (t₀ := 0) (fun _ => (lipschitz_mulVec A).lipschitzOnWith) hf hg (by simp)
  exact congrFun heq t

/-- Half-period law: `osc2 p (t + π/ω_d) = −e^{−σπ/ω_d} osc2 p t`. -/
@[powerlib_foundation] theorem osc2_add_half_period (hωd : ωd ≠ 0) (p : Fin 2 → ℝ) (t : ℝ) :
    osc2 A σ ωd p (t + Real.pi / ωd) = -Real.exp (-(σ * (Real.pi / ωd))) • osc2 A σ ωd p t := by
  have harg : ωd * (t + Real.pi / ωd) = ωd * t + Real.pi := by field_simp
  have hexp : Real.exp (-(σ * (t + Real.pi / ωd))) =
      Real.exp (-(σ * (Real.pi / ωd))) * Real.exp (-(σ * t)) := by
    rw [← Real.exp_add]; ring_nf
  simp only [osc2, harg, Real.cos_add_pi, Real.sin_add_pi, hexp]
  ext i
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, neg_mul]
  ring

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- `osc2` read on Euclidean state space solves the linear field `x' = A x`. -/
@[powerlib_foundation] theorem hasDerivAt_toLp_osc2 (htr : A.trace = -2 * σ)
    (hdet : A.det = σ ^ 2 + ωd ^ 2) (hωd : ωd ≠ 0) (p : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (fun s => WithLp.toLp 2 (osc2 A σ ωd p s))
      (Linear.op A (WithLp.toLp 2 (osc2 A σ ωd p t))) t :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_osc2 htr hdet hωd p t)

/-- Every forward solution from `t = 0` of a two-state linear plant whose state matrix has
eigenvalues `−σ ± j ω_d`, under a constant input `u` with equilibrium `e`, is the explicit closed
form. -/
@[powerlib_foundation] theorem trajectory_eq_osc2 {p : ℕ} (M : Linear.Plant 2 p)
    {u : Fin p → ℝ} {e : ℝ²} (he : IsEquilibrium (M.inputField u) e)
    (htr : M.A.trace = -2 * σ) (hdet : M.A.det = σ ^ 2 + ωd ^ 2) (hωd : ωd ≠ 0)
    {x : ℝ → ℝ²} (hx : IsIntegralCurveOn x (fun _ y => M.inputField u y) (Ici 0)) {t : ℝ}
    (ht : 0 ≤ t) :
    x t = e + WithLp.toLp 2 (osc2 M.A σ ωd (WithLp.ofLp (x 0 - e)) t) := by
  rw [M.inputField_eq he] at hx
  have hy : IsTrajectoryOn (fun s => e + WithLp.toLp 2 (osc2 M.A σ ωd (WithLp.ofLp (x 0 - e)) s))
      (LinearSystems.affineLinearVectorField M.A e) 0 t := by
    intro s _
    have h := ((hasDerivAt_toLp_osc2 htr hdet hωd (WithLp.ofLp (x 0 - e)) s).const_add e)
    refine h.hasDerivWithinAt.congr_deriv ?_
    show _ = LinearSystems.affineLinearVectorField M.A e _
    rw [Linear.affine_apply, add_sub_cancel_left]
  have h := Linear.trajectory_unique (hx.mono Icc_subset_Ici_self) hy (by simp) t ⟨ht, le_rfl⟩
  exact h

/-- `e^{−σu}(cos(ω_d u) + (σ/ω_d) sin(ω_d u)) ≤ 1` for `0 ≤ σ`, `0 < ω_d`, `0 ≤ u`. -/
@[powerlib_foundation] theorem one_add_ratio_sin_le_exp (hσ : 0 ≤ σ) (hωd : 0 < ωd) {u : ℝ}
    (hu : 0 ≤ u) :
    Real.exp (-(σ * u)) * (Real.cos (ωd * u) + σ / ωd * Real.sin (ωd * u)) ≤ 1 := by
  have hs : Real.sin (ωd * u) ≤ ωd * u := Real.sin_le (mul_nonneg hωd.le hu)
  have hc : Real.cos (ωd * u) ≤ 1 := Real.cos_le_one _
  have h1 : σ / ωd * Real.sin (ωd * u) ≤ σ * u := by
    calc σ / ωd * Real.sin (ωd * u) ≤ σ / ωd * (ωd * u) :=
          mul_le_mul_of_nonneg_left hs (div_nonneg hσ hωd.le)
      _ = σ * u := by field_simp
  have h2 : 1 + σ * u ≤ Real.exp (σ * u) := by
    have := Real.add_one_le_exp (σ * u); linarith
  have hpos : 0 < Real.exp (-(σ * u)) := Real.exp_pos _
  have hprod : Real.exp (-(σ * u)) * Real.exp (σ * u) = 1 := by
    rw [← Real.exp_add]; simp
  calc Real.exp (-(σ * u)) * (Real.cos (ωd * u) + σ / ωd * Real.sin (ωd * u))
      ≤ Real.exp (-(σ * u)) * Real.exp (σ * u) :=
        mul_le_mul_of_nonneg_left (by linarith) hpos.le
    _ = 1 := hprod

end powerlib.LTI
