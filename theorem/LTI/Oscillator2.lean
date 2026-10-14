import theorem.LTI.Plant

/-! # Closed-form flow of a real 2×2 system with complex eigenvalues (foundation)

The explicit flow of `ẏ = A y` for a real `2 × 2` matrix with eigenvalues `−σ ± j ω_d`, its use as
the time-domain closed form of two-state linear plants, and the matching matrix exponential in
any dimension.

Scope.
* A real matrix `A : Matrix (Fin 2) (Fin 2) ℝ` with `tr A = −2σ`, `det A = σ² + ω_d²` and
  `ω_d ≠ 0` (eigenvalues `−σ ± j ω_d`); the matrix-exponential results hold in any size `n`.
* Foundation only: `osc2` is an explicit closed form, and `trajectory_eq_osc2` is a generic
  implication about an arbitrary caller-supplied two-state plant (Rules §3). It defines no
  family. No Laplace inversion is imported.

Source: work-sync `theory/T-frequency-stability.md` §1.7 (underdamped frequency response
`e^{−σt}(cos ω_d t − α sin ω_d t)` and its nadir) and `theory/T-sfr-model.md` §1.5–§1.6
(second-order SFR model and its nadir closed form).

Results.
* `osc2 A σ ω_d p t = e^{−σ t} (cos(ω_d t) p + (sin(ω_d t)/ω_d) (A + σ I) p)` solves `ẏ = A y`,
  `y(0) = p` (`hasDerivAt_osc2`, `osc2_zero`). The proof uses only the 2×2 Cayley–Hamilton
  identity `(A + σ I)² = −ω_d² I` (`shift_sq_mulVec`). Uniqueness of global solutions (Mathlib
  `ODE_solution_unique_univ`) then gives the flow law `osc2 p (s + t) = osc2 (osc2 p s) t`
  (`osc2_add`), and the half-period law `osc2 p (t + π/ω_d) = −e^{−σπ/ω_d} osc2 p t`
  (`osc2_add_half_period`) is a direct trigonometric identity.
* `trajectory_eq_osc2` connects this to any two-state linear plant (`Linear.Plant 2 p`) whose
  state matrix has that trace and determinant: every forward solution from `t = 0` under a
  constant input `u` with equilibrium `e` is `e + osc2 A σ ω_d (x 0 − e) t` for `t ≥ 0` (explicit
  candidate + uniqueness of solution segments of the affine linear field,
  `Linear.trajectory_unique`). This is the time-domain closed form used by the frequency-nadir
  results.
* `one_add_ratio_sin_le_exp` is the elementary inequality
  `e^{−σu}(cos(ω_d u) + (σ/ω_d) sin(ω_d u)) ≤ 1` for `σ ≥ 0`, `ω_d > 0`, `u ≥ 0`, which bounds
  every later excursion of a damped response by its first extremum.
* Matrix exponential (any size `n`): `exp_smul_eq_of_hasDerivAt` (a differentiable `E` with
  `Ė = A E`, `E 0 = 1` is `t ↦ e^{tA}`) and `exp_smul_of_sq_eq` (if `B = A + a I` satisfies
  `B² = −w² I`, `w ≠ 0`, then `e^{tA} = e^{−at} (cos(wt) I + (sin(wt)/w) B)`, the matrix form of
  `osc2`); used by the lag covariance of the stochastic COI swing
  (`theorem/Frequency/StochasticCOI.lean`).
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

/-! ## The matrix exponential as the solution of `Ė = A E` -/

section MatrixExp

open scoped Matrix.Norms.Frobenius

variable {n : ℕ}

/-- Uniqueness of the matrix exponential: a differentiable `E` with `Ė = A E`, `E 0 = 1` is
`t ↦ e^{tA}`. -/
@[powerlib_foundation] theorem exp_smul_eq_of_hasDerivAt {A : Matrix (Fin n) (Fin n) ℝ}
    {E : ℝ → Matrix (Fin n) (Fin n) ℝ} (h0 : E 0 = 1) (hE : ∀ t, HasDerivAt E (A * E t) t)
    (t : ℝ) : E t = NormedSpace.exp (t • A) := by
  set F : ℝ → Matrix (Fin n) (Fin n) ℝ := fun s => NormedSpace.exp (s • (-A)) * E s with hF
  have hFd : ∀ s, HasDerivAt F 0 s := by
    intro s
    have h := (hasDerivAt_exp_smul_const' (-A) s).mul (hE s)
    have c1 : A * NormedSpace.exp (s • (-A)) = NormedSpace.exp (s • (-A)) * A :=
      ((((Commute.refl A).neg_right).smul_right s).exp_right).eq
    have hval : -A * NormedSpace.exp (s • (-A)) * E s +
        NormedSpace.exp (s • (-A)) * (A * E s) = 0 := by
      rw [← mul_assoc, ← c1, neg_mul, neg_mul, neg_add_cancel]
    convert! h using 1
    exact hval.symm
  have hFc : F t = F 0 :=
    is_const_of_deriv_eq_zero (fun s => (hFd s).differentiableAt) (fun s => (hFd s).deriv) t 0
  have hF0 : F 0 = 1 := by simp [hF, h0, NormedSpace.exp_zero]
  have hinv : NormedSpace.exp (t • A) * NormedSpace.exp (t • (-A)) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ ((((Commute.refl A).neg_right).smul_left t).smul_right t)]
    simp [NormedSpace.exp_zero]
  calc E t = NormedSpace.exp (t • A) * F t := by
        simp only [hF, ← mul_assoc, hinv, one_mul]
    _ = NormedSpace.exp (t • A) := by rw [hFc, hF0, mul_one]

/-- Closed form of `e^{tA}` when `B = A + a I` satisfies `B² = −w² I` (`w ≠ 0`):
`e^{tA} = e^{−at} (cos(wt) I + (sin(wt)/w) B)`. -/
@[powerlib_foundation] theorem exp_smul_of_sq_eq {A : Matrix (Fin n) (Fin n) ℝ} {a w : ℝ}
    (hw : w ≠ 0) (hB : (A + a • 1) * (A + a • 1) = -(w ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ))
    (t : ℝ) :
    NormedSpace.exp (t • A) = (Real.exp (-a * t) * Real.cos (w * t)) • (1 : Matrix _ _ ℝ) +
      (Real.exp (-a * t) * Real.sin (w * t) / w) • (A + a • 1) := by
  set B := A + a • (1 : Matrix (Fin n) (Fin n) ℝ) with hBdef
  set f1 : ℝ → ℝ := fun s => Real.exp (-a * s) * Real.cos (w * s) with hf1
  set f2 : ℝ → ℝ := fun s => Real.exp (-a * s) * Real.sin (w * s) / w with hf2
  have hd1 : ∀ s, HasDerivAt f1 (-a * f1 s - w ^ 2 * f2 s) s := by
    intro s
    have he : HasDerivAt (fun s => Real.exp (-a * s)) (Real.exp (-a * s) * (-a)) s := by
      have := ((hasDerivAt_id s).const_mul (-a)).exp
      simpa using this
    have hc : HasDerivAt (fun s => Real.cos (w * s)) (-Real.sin (w * s) * w) s := by
      have := ((hasDerivAt_id s).const_mul w).cos
      simpa [mul_comm] using this
    convert! he.mul hc using 1
    simp only [hf1, hf2]
    field_simp
    ring
  have hd2 : ∀ s, HasDerivAt f2 (f1 s - a * f2 s) s := by
    intro s
    have he : HasDerivAt (fun s => Real.exp (-a * s)) (Real.exp (-a * s) * (-a)) s := by
      have := ((hasDerivAt_id s).const_mul (-a)).exp
      simpa using this
    have hs : HasDerivAt (fun s => Real.sin (w * s)) (Real.cos (w * s) * w) s := by
      have := ((hasDerivAt_id s).const_mul w).sin
      simpa [mul_comm] using this
    convert! (he.mul hs).div_const w using 1
    simp only [hf1, hf2]
    field_simp
    ring
  have hA : A = B - a • (1 : Matrix (Fin n) (Fin n) ℝ) := by rw [hBdef]; abel
  have key := exp_smul_eq_of_hasDerivAt (A := A)
    (E := fun s => f1 s • (1 : Matrix (Fin n) (Fin n) ℝ) + f2 s • B)
    (by simp [hf1, hf2]) (fun s => by
      have h := ((hd1 s).smul_const (1 : Matrix (Fin n) (Fin n) ℝ)).add ((hd2 s).smul_const B)
      convert! h using 1
      simp only [hA, sub_mul, mul_add, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hB]
      module) t
  rw [← key]

end MatrixExp

end powerlib.LTI
