import theorem.LTI.Plant
import theorem.Criteria.Hurwitz2

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
  identity (`Criteria.sq_eq_trace_smul_sub_det_smul_fin_two`) in the form
  `(A + σ I)² = −ω_d² I` (`shift_sq_mulVec`). Uniqueness of global solutions (Mathlib
  `ODE_solution_unique_univ`) then gives the flow law `osc2 p (s + t) = osc2 (osc2 p s) t`
  (`osc2_add`), and the half-period law `osc2 p (t + π/ω_d) = −e^{−σπ/ω_d} osc2 p t`
  (`osc2_add_half_period`) is a direct trigonometric identity.
* `trajectory_eq_osc2` connects this to any two-state linear plant (`Linear.Plant 2 p`) whose
  state matrix has that trace and determinant: every forward solution from `t = 0` under a
  constant input `u` with equilibrium `e` is `e + osc2 A σ ω_d (x 0 − e) t` for `t ≥ 0` (explicit
  candidate + uniqueness of solution segments of the affine linear field,
  `Linear.trajectory_unique`). This is the time-domain closed form used by the frequency-nadir
  results.
* First extremum (nadir) of a damped response, for any such plant: every coordinate of a forward
  solution is `e_i + dampedResp σ ω_d a r t` with initial deviation `a = (x(0) − e)_i` and
  initial slope `r = (A (x(0) − e))_i` (`trajectory_apply_eq_dampedResp`). The scalar response
  has derivative `−ρ e^{−σt} sin(θ − ω_d t)`, `ρ e^{jθ} = dampedRespPhase σ ω_d a r`
  (`hasDerivAt_dampedResp`), vanishing at `θ/ω_d + kπ/ω_d` (`hasDerivAt_dampedResp_crit_add`),
  and the half-period law `g(t + π/ω_d) = −e^{−σπ/ω_d} g(t)` (`dampedResp_add_half_period`).
  Starting downwards (`r < 0`) it decreases strictly up to `T = dampedRespCrit σ ω_d a r > 0`
  (`dampedRespCrit_pos`, `dampedResp_strictAntiOn`), `g(T) = −(ω_d ρ/(σ² + ω_d²)) e^{−σT}`
  (`dampedResp_crit`), and for `σ ≥ 0` `g(T)` is the minimum over `t ≥ 0`
  (`dampedResp_isMinOn`); `trajectory_nadir_osc2` is the trajectory form. The limit and the
  initial rate of such trajectories are the any-dimension laws `LTI.tendsto_apply_of_isHurwitz`
  and `LTI.hasDerivWithinAt_apply_zero` (`theorem/LTI/Plant.lean`).
* `one_add_ratio_sin_le_exp` is the elementary inequality
  `e^{−σu}(cos(ω_d u) + (σ/ω_d) sin(ω_d u)) ≤ 1` for `σ ≥ 0`, `ω_d > 0`, `u ≥ 0`, which bounds
  every later excursion of a damped response by its first extremum.
* Matrix exponential (any size `n`): `exp_smul_eq_of_hasDerivAt` (a differentiable `E` with
  `Ė = A E`, `E 0 = 1` is `t ↦ e^{tA}`) and `exp_smul_of_sq_eq` (if `B = A + a I` satisfies
  `B² = −w² I`, `w ≠ 0`, then `e^{tA} = e^{−at} (cos(wt) I + (sin(wt)/w) B)`, the matrix form of
  `osc2`); used by the lag covariance of the stochastic COI swing
  (`theorem/PowerSystem/Frequency/StochasticCOI.lean`).
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

/-- `(A + σ I)² = −ω_d² I` when `tr A = −2σ`, `det A = σ² + ω_d²`. -/
@[tmio T, powerlib_foundation] theorem shift_sq_mulVec (htr : A.trace = -2 * σ)
    (hdet : A.det = σ ^ 2 + ωd ^ 2) (p : Fin 2 → ℝ) :
    (A + σ • 1) *ᵥ ((A + σ • 1) *ᵥ p) = -(ωd ^ 2) • p := by
  rw [Matrix.mulVec_mulVec]
  have h : (A + σ • 1) * (A + σ • 1) = -(ωd ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    have hA := Criteria.sq_eq_trace_smul_sub_det_smul_fin_two A
    rw [sq, htr, hdet] at hA
    calc (A + σ • 1) * (A + σ • 1) = A * A + (2 * σ) • A + σ ^ 2 • (1 : Matrix _ _ ℝ) := by
          simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
            Matrix.mul_one, smul_smul]
          module
      _ = _ := by rw [hA]; module
  rw [h, Matrix.smul_mulVec, Matrix.one_mulVec]

@[tmio T, simp, powerlib_foundation] theorem osc2_zero (A : Matrix (Fin 2) (Fin 2) ℝ) (σ ωd : ℝ)
    (p : Fin 2 → ℝ) : osc2 A σ ωd p 0 = p := by
  simp [osc2]

/-- `osc2` solves `ẏ = A y`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_osc2 (htr : A.trace = -2 * σ)
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

@[tmio T, powerlib_foundation] private theorem lipschitz_mulVec (A : Matrix (Fin 2) (Fin 2) ℝ) :
    LipschitzWith ‖LinearMap.toContinuousLinearMap (Matrix.toLin' A)‖₊
      (fun y : Fin 2 → ℝ => A *ᵥ y) := by
  have h := (LinearMap.toContinuousLinearMap (Matrix.toLin' A)).lipschitzWith
  have hf : (fun y : Fin 2 → ℝ => A *ᵥ y) =
      ⇑(LinearMap.toContinuousLinearMap (Matrix.toLin' A)) := by
    funext y; simp
  rw [hf]; exact h

/-- Flow law: `osc2 p (s + t) = osc2 (osc2 p s) t`. -/
@[tmio T, powerlib_foundation] theorem osc2_add (htr : A.trace = -2 * σ)
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
@[tmio T, powerlib_foundation] theorem osc2_add_half_period (hωd : ωd ≠ 0) (p : Fin 2 → ℝ) (t : ℝ) :
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
@[tmio T, powerlib_foundation] theorem hasDerivAt_toLp_osc2 (htr : A.trace = -2 * σ)
    (hdet : A.det = σ ^ 2 + ωd ^ 2) (hωd : ωd ≠ 0) (p : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (fun s => WithLp.toLp 2 (osc2 A σ ωd p s))
      (Linear.op A (WithLp.toLp 2 (osc2 A σ ωd p t))) t :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_osc2 htr hdet hωd p t)

/-- Every forward solution from `t = 0` of a two-state linear plant whose state matrix has
eigenvalues `−σ ± j ω_d`, under a constant input `u` with equilibrium `e`, is the explicit closed
form. -/
@[tmio T, powerlib_foundation] theorem trajectory_eq_osc2 {p : ℕ} (M : Linear.Plant 2 p)
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
@[tmio T, powerlib_foundation] theorem one_add_ratio_sin_le_exp (hσ : 0 ≤ σ) (hωd : 0 < ωd) {u : ℝ}
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

/-! ## First extremum of a damped response

Every coordinate of `osc2` is the damped scalar response `dampedResp`. When it starts downwards
(`g'(0) = r < 0`) it decreases strictly up to its first critical time, attains there its minimum
over `t ≥ 0` (`σ ≥ 0`), and the minimum has a closed form; the trajectory form is
`trajectory_nadir_osc2`. -/

section DampedResponse

/-- The damped scalar response `g(t) = e^{−σt}(a cos ω_d t + ((r + σ a)/ω_d) sin ω_d t)`, with
`g(0) = a` and `g'(0) = r`. -/
def dampedResp (σ ωd a r t : ℝ) : ℝ :=
  Real.exp (-(σ * t)) * (a * Real.cos (ωd * t) + (r + σ * a) / ωd * Real.sin (ωd * t))

/-- The phase point `−q − j r`, `q = ((σ² + ω_d²) a + σ r)/ω_d`: with `θ` its argument and `ρ`
its norm, `g'(t) = −ρ e^{−σt} sin(θ − ω_d t)` (`hasDerivAt_dampedResp`). -/
def dampedRespPhase (σ ωd a r : ℝ) : ℂ := ⟨-(((σ ^ 2 + ωd ^ 2) * a + σ * r) / ωd), -r⟩

/-- The first critical time `θ/ω_d` of the damped response. -/
def dampedRespCrit (σ ωd a r : ℝ) : ℝ := Complex.arg (dampedRespPhase σ ωd a r) / ωd

variable {a r : ℝ}

@[tmio T, powerlib_foundation] private theorem dampedRespPhase_re (σ ωd a r : ℝ) :
    ‖dampedRespPhase σ ωd a r‖ * Real.cos (Complex.arg (dampedRespPhase σ ωd a r)) =
      -(((σ ^ 2 + ωd ^ 2) * a + σ * r) / ωd) := by
  rw [Complex.norm_mul_cos_arg]; rfl

@[tmio T, powerlib_foundation] private theorem dampedRespPhase_im (σ ωd a r : ℝ) :
    ‖dampedRespPhase σ ωd a r‖ * Real.sin (Complex.arg (dampedRespPhase σ ωd a r)) = -r := by
  rw [Complex.norm_mul_sin_arg]; rfl

@[tmio T, powerlib_foundation] private theorem dampedRespPhase_arg_mem (hr : r < 0) :
    0 < Complex.arg (dampedRespPhase σ ωd a r) ∧
      Complex.arg (dampedRespPhase σ ωd a r) < Real.pi := by
  have him : (dampedRespPhase σ ωd a r).im = -r := rfl
  refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.2 (by rw [him]; linarith)) fun h => ?_,
    Complex.arg_lt_pi_iff.2 (Or.inr (by rw [him]; linarith))⟩
  have := (Complex.arg_eq_zero_iff.1 h.symm).2
  rw [him] at this
  linarith

@[tmio T, powerlib_foundation] private theorem dampedRespPhase_norm_pos (hr : r < 0) :
    0 < ‖dampedRespPhase σ ωd a r‖ :=
  norm_pos_iff.2 fun h => by
    have : (dampedRespPhase σ ωd a r).im = 0 := by rw [h]; rfl
    change -r = 0 at this
    linarith

/-- `g'(t) = −ρ e^{−σt} sin(θ − ω_d t)`, `ρ e^{jθ} = −q − j r`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_dampedResp (hωd : ωd ≠ 0) (t : ℝ) :
    HasDerivAt (dampedResp σ ωd a r)
      (-‖dampedRespPhase σ ωd a r‖ * Real.exp (-(σ * t)) *
        Real.sin (Complex.arg (dampedRespPhase σ ωd a r) - ωd * t)) t := by
  have he : HasDerivAt (fun s => Real.exp (-(σ * s))) (Real.exp (-(σ * t)) * (-σ)) t := by
    simpa using ((hasDerivAt_id t).const_mul σ).neg.exp
  have hc : HasDerivAt (fun s => Real.cos (ωd * s)) (-Real.sin (ωd * t) * ωd) t := by
    simpa using ((hasDerivAt_id t).const_mul ωd).cos
  have hs : HasDerivAt (fun s => Real.sin (ωd * s)) (Real.cos (ωd * t) * ωd) t := by
    simpa using ((hasDerivAt_id t).const_mul ωd).sin
  have h := he.mul ((hc.const_mul a).add (hs.const_mul ((r + σ * a) / ωd)))
  convert h using 1
  · funext s; simp only [dampedResp, Pi.mul_apply, Pi.add_apply]
  simp only [Pi.add_apply]
  have hre := dampedRespPhase_re σ ωd a r
  have him := dampedRespPhase_im σ ωd a r
  have hb : (r + σ * a) / ωd * ωd = r + σ * a := div_mul_cancel₀ _ hωd
  have hq : σ * ((r + σ * a) / ωd) + a * ωd = ((σ ^ 2 + ωd ^ 2) * a + σ * r) / ωd := by
    field_simp; ring
  rw [Real.sin_sub]
  set E := Real.exp (-(σ * t))
  set C := Real.cos (ωd * t)
  set S := Real.sin (ωd * t)
  linear_combination (-E * C) * him + (-E * C) * hb + (E * S) * hre + (E * S) * hq

/-- The derivative vanishes at `θ/ω_d + k π/ω_d`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_dampedResp_crit_add (hωd : ωd ≠ 0) (k : ℕ) :
    HasDerivAt (dampedResp σ ωd a r) 0 (dampedRespCrit σ ωd a r + k * (Real.pi / ωd)) := by
  convert hasDerivAt_dampedResp (σ := σ) (a := a) (r := r) hωd _ using 1
  have harg : ωd * (dampedRespCrit σ ωd a r + k * (Real.pi / ωd)) =
      Complex.arg (dampedRespPhase σ ωd a r) + k * Real.pi := by
    rw [dampedRespCrit]; field_simp
  rw [harg, show ∀ x y : ℝ, x - (x + y) = -y from fun x y => by ring, Real.sin_neg,
    Real.sin_nat_mul_pi]
  ring

/-- Half-period law `g(t + π/ω_d) = −e^{−σπ/ω_d} g(t)`. -/
@[tmio T, powerlib_foundation] theorem dampedResp_add_half_period (hωd : ωd ≠ 0) (t : ℝ) :
    dampedResp σ ωd a r (t + Real.pi / ωd) =
      -Real.exp (-(σ * (Real.pi / ωd))) * dampedResp σ ωd a r t := by
  have harg : ωd * (t + Real.pi / ωd) = ωd * t + Real.pi := by field_simp
  have hexp : Real.exp (-(σ * (t + Real.pi / ωd))) =
      Real.exp (-(σ * (Real.pi / ωd))) * Real.exp (-(σ * t)) := by
    rw [← Real.exp_add]; ring_nf
  unfold dampedResp
  rw [harg, hexp, Real.cos_add_pi, Real.sin_add_pi]
  ring

/-- The first critical time is positive for a response that starts downwards. -/
@[tmio T, powerlib_foundation] theorem dampedRespCrit_pos (hωd : 0 < ωd) (hr : r < 0) :
    0 < dampedRespCrit σ ωd a r :=
  div_pos (dampedRespPhase_arg_mem hr).1 hωd

/-- A response that starts downwards decreases strictly up to its first critical time. -/
@[tmio T, powerlib_foundation] theorem dampedResp_strictAntiOn (hωd : 0 < ωd) (hr : r < 0) :
    StrictAntiOn (dampedResp σ ωd a r) (Icc 0 (dampedRespCrit σ ωd a r)) := by
  obtain ⟨hθ0, hθπ⟩ := dampedRespPhase_arg_mem (σ := σ) (ωd := ωd) (a := a) hr
  have hρ := dampedRespPhase_norm_pos (σ := σ) (ωd := ωd) (a := a) hr
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact fun t _ => (hasDerivAt_dampedResp hωd.ne' t).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hasDerivAt_dampedResp hωd.ne' t).deriv]
    have h1 : ωd * t < Complex.arg (dampedRespPhase σ ωd a r) := by
      have := mul_lt_mul_of_pos_left ht.2 hωd
      rwa [dampedRespCrit, mul_div_cancel₀ _ hωd.ne'] at this
    have hsin : 0 < Real.sin (Complex.arg (dampedRespPhase σ ωd a r) - ωd * t) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by nlinarith [ht.1])
    have := mul_pos (mul_pos hρ (Real.exp_pos (-(σ * t)))) hsin
    linarith

/-- Value at the first critical time: `g(T) = −(ω_d ρ/(σ² + ω_d²)) e^{−σT}`. -/
@[tmio T, powerlib_foundation] theorem dampedResp_crit (hωd : 0 < ωd) (hr : r < 0) :
    dampedResp σ ωd a r (dampedRespCrit σ ωd a r) =
      -(ωd * ‖dampedRespPhase σ ωd a r‖ / (σ ^ 2 + ωd ^ 2)) *
        Real.exp (-(σ * dampedRespCrit σ ωd a r)) := by
  have hρ := dampedRespPhase_norm_pos (σ := σ) (ωd := ωd) (a := a) hr
  have hre := dampedRespPhase_re σ ωd a r
  have him := dampedRespPhase_im σ ωd a r
  have hsq : ‖dampedRespPhase σ ωd a r‖ ^ 2 =
      (((σ ^ 2 + ωd ^ 2) * a + σ * r) / ωd) ^ 2 + r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    show (-(((σ ^ 2 + ωd ^ 2) * a + σ * r) / ωd)) * (-(((σ ^ 2 + ωd ^ 2) * a + σ * r) / ωd)) +
      (-r) * (-r) = _
    ring
  have hT : ωd * dampedRespCrit σ ωd a r = Complex.arg (dampedRespPhase σ ωd a r) := by
    rw [dampedRespCrit, mul_div_cancel₀ _ hωd.ne']
  have hω0 : ωd ≠ 0 := hωd.ne'
  have hn : 0 < σ ^ 2 + ωd ^ 2 := by positivity
  have hbr : a * Real.cos (Complex.arg (dampedRespPhase σ ωd a r)) +
      (r + σ * a) / ωd * Real.sin (Complex.arg (dampedRespPhase σ ωd a r)) =
        -(ωd * ‖dampedRespPhase σ ωd a r‖ / (σ ^ 2 + ωd ^ 2)) := by
    generalize ‖dampedRespPhase σ ωd a r‖ = ρ at hρ hre him hsq ⊢
    generalize Complex.arg (dampedRespPhase σ ωd a r) = θ at hre him ⊢
    have hsq' : ρ ^ 2 * ωd ^ 2 = ((σ ^ 2 + ωd ^ 2) * a + σ * r) ^ 2 + r ^ 2 * ωd ^ 2 := by
      rw [hsq]; field_simp
    refine mul_right_cancel₀ (b := ρ * ωd * (σ ^ 2 + ωd ^ 2)) (by positivity) ?_
    have e1 : (a * Real.cos θ + (r + σ * a) / ωd * Real.sin θ) * (ρ * ωd * (σ ^ 2 + ωd ^ 2)) =
        (σ ^ 2 + ωd ^ 2) * (ωd * a * (ρ * Real.cos θ) + (r + σ * a) * (ρ * Real.sin θ)) := by
      field_simp
    have e2 : -(ωd * ρ / (σ ^ 2 + ωd ^ 2)) * (ρ * ωd * (σ ^ 2 + ωd ^ 2)) =
        -(ρ ^ 2 * ωd ^ 2) := by
      field_simp
    rw [e1, e2, hre, him, hsq']
    field_simp
    ring
  unfold dampedResp
  rw [hT, hbr]
  ring

/-- After its first critical time the response stays at or above that value (`σ ≥ 0`): it is the
minimum over `t ≥ 0`. -/
@[tmio T, powerlib_foundation] theorem dampedResp_isMinOn (hωd : 0 < ωd) (hσ : 0 ≤ σ)
    (hr : r < 0) : IsMinOn (dampedResp σ ωd a r) (Ici 0) (dampedRespCrit σ ωd a r) := by
  set T := dampedRespCrit σ ωd a r
  have hT0 : 0 < T := dampedRespCrit_pos hωd hr
  intro t ht
  simp only [Set.mem_ofPred_eq]
  rcases le_total t T with h | h
  · exact (dampedResp_strictAntiOn hωd hr).antitoneOn ⟨ht, h⟩ ⟨hT0.le, le_rfl⟩ h
  -- critical-point shift: `g(T + u) = g(T) e^{−σu}(cos ω_d u + (σ/ω_d) sin ω_d u)`
  have hd := (hasDerivAt_dampedResp (σ := σ) (a := a) (r := r) hωd.ne' T)
  have hd0 := (hasDerivAt_dampedResp_crit_add (σ := σ) (a := a) (r := r) hωd.ne' 0)
  simp only [Nat.cast_zero, zero_mul, add_zero] at hd0
  have hcrit := hd.unique hd0
  have hval := dampedResp_crit (σ := σ) (a := a) hωd hr
  have hneg : dampedResp σ ωd a r T < 0 := by
    rw [hval]
    have hρ := dampedRespPhase_norm_pos (σ := σ) (ωd := ωd) (a := a) hr
    have : 0 < ωd * ‖dampedRespPhase σ ωd a r‖ / (σ ^ 2 + ωd ^ 2) := by positivity
    have := mul_pos this (Real.exp_pos (-(σ * T)))
    linarith
  have hshift : dampedResp σ ωd a r t = dampedResp σ ωd a r T *
      (Real.exp (-(σ * (t - T))) * (Real.cos (ωd * (t - T)) + σ / ωd * Real.sin (ωd * (t - T))))
      := by
    -- the bracket derivative vanishes at `T`
    have hk : (r + σ * a) / ωd * Real.cos (ωd * T) - a * Real.sin (ωd * T) =
        σ / ωd * (a * Real.cos (ωd * T) + (r + σ * a) / ωd * Real.sin (ωd * T)) := by
      have hre := dampedRespPhase_re σ ωd a r
      have him := dampedRespPhase_im σ ωd a r
      have hρ := dampedRespPhase_norm_pos (σ := σ) (ωd := ωd) (a := a) hr
      have hT : ωd * T = Complex.arg (dampedRespPhase σ ωd a r) := by
        simp only [T, dampedRespCrit, mul_div_cancel₀ _ hωd.ne']
      rw [hT]
      generalize ‖dampedRespPhase σ ωd a r‖ = ρ at hρ hre him
      generalize Complex.arg (dampedRespPhase σ ωd a r) = θ at hre him ⊢
      rw [← mul_right_inj' hρ.ne', ← mul_right_inj' hωd.ne']
      have e : ωd * (ρ * ((r + σ * a) / ωd * Real.cos θ - a * Real.sin θ)) =
          (r + σ * a) * (ρ * Real.cos θ) - ωd * a * (ρ * Real.sin θ) := by field_simp
      have e' : ωd * (ρ * (σ / ωd * (a * Real.cos θ + (r + σ * a) / ωd * Real.sin θ))) =
          σ * (a * (ρ * Real.cos θ) + (r + σ * a) / ωd * (ρ * Real.sin θ)) := by
        field_simp
      rw [e, e', hre, him]
      field_simp
      ring
    have ht' : t = T + (t - T) := by ring
    conv_lhs => rw [ht']
    unfold dampedResp
    rw [show ωd * (T + (t - T)) = ωd * T + ωd * (t - T) by ring, Real.cos_add, Real.sin_add,
      show -(σ * (T + (t - T))) = -(σ * T) + -(σ * (t - T)) by ring, Real.exp_add]
    linear_combination (Real.exp (-(σ * T)) * Real.exp (-(σ * (t - T))) *
      Real.sin (ωd * (t - T))) * hk
  have hG := one_add_ratio_sin_le_exp hσ hωd (sub_nonneg.2 h)
  rw [hshift]
  nlinarith

end DampedResponse

/-- Every coordinate of a forward solution of a two-state plant with eigenvalues `−σ ± j ω_d`
(constant input `u`, equilibrium `e`) is `e_i` plus the damped response with initial deviation
`a = (x(0) − e)_i` and initial slope `r = (A (x(0) − e))_i`. -/
@[tmio T, powerlib_foundation] theorem trajectory_apply_eq_dampedResp {p : ℕ}
    (M : Linear.Plant 2 p) {u : Fin p → ℝ} {e : ℝ²} (he : IsEquilibrium (M.inputField u) e)
    (htr : M.A.trace = -2 * σ) (hdet : M.A.det = σ ^ 2 + ωd ^ 2) (hωd : ωd ≠ 0)
    {x : ℝ → ℝ²} (hx : IsIntegralCurveOn x (fun _ y => M.inputField u y) (Ici 0)) (i : Fin 2)
    {t : ℝ} (ht : 0 ≤ t) :
    x t i = e i + dampedResp σ ωd (WithLp.ofLp (x 0 - e) i)
      ((M.A *ᵥ WithLp.ofLp (x 0 - e)) i) t := by
  rw [trajectory_eq_osc2 M he htr hdet hωd hx ht]
  simp only [PiLp.add_apply, osc2, dampedResp, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  ring

/-- First extremum of a forward solution: if a coordinate starts downwards
(`r = (A (x(0) − e))_i < 0`) and `σ ≥ 0`, it decreases strictly up to
`T = dampedRespCrit σ ω_d a r > 0`, attains its minimum over `t ≥ 0` at `T`, and that minimum is
`e_i − (ω_d ρ/(σ² + ω_d²)) e^{−σT}`, `ρ = ‖dampedRespPhase σ ω_d a r‖`. -/
@[tmio T, powerlib_foundation] theorem trajectory_nadir_osc2 {p : ℕ} (M : Linear.Plant 2 p)
    {u : Fin p → ℝ} {e : ℝ²} (he : IsEquilibrium (M.inputField u) e)
    (htr : M.A.trace = -2 * σ) (hdet : M.A.det = σ ^ 2 + ωd ^ 2) (hωd : 0 < ωd) (hσ : 0 ≤ σ)
    {x : ℝ → ℝ²} (hx : IsIntegralCurveOn x (fun _ y => M.inputField u y) (Ici 0)) (i : Fin 2)
    {a r : ℝ} (ha : WithLp.ofLp (x 0 - e) i = a) (hra : (M.A *ᵥ WithLp.ofLp (x 0 - e)) i = r)
    (hr : r < 0) :
    0 < dampedRespCrit σ ωd a r ∧
      StrictAntiOn (fun t => x t i) (Icc 0 (dampedRespCrit σ ωd a r)) ∧
      IsMinOn (fun t => x t i) (Ici 0) (dampedRespCrit σ ωd a r) ∧
      x (dampedRespCrit σ ωd a r) i = e i - ωd * ‖dampedRespPhase σ ωd a r‖ / (σ ^ 2 + ωd ^ 2) *
        Real.exp (-(σ * dampedRespCrit σ ωd a r)) := by
  have hT0 := dampedRespCrit_pos (σ := σ) (a := a) hωd hr
  have hx' : ∀ {t : ℝ}, 0 ≤ t → x t i = e i + dampedResp σ ωd a r t := fun ht => by
    rw [trajectory_apply_eq_dampedResp M he htr hdet hωd.ne' hx i ht, ha, hra]
  refine ⟨hT0, fun s hs t ht hst => ?_, fun t ht => ?_, ?_⟩
  · simp only
    rw [hx' hs.1, hx' ht.1]
    linarith [dampedResp_strictAntiOn (σ := σ) (a := a) hωd hr hs ht hst]
  · have hmin := dampedResp_isMinOn (a := a) hωd hσ hr ht
    simp only [Set.mem_ofPred_eq] at hmin ⊢
    rw [hx' ht, hx' hT0.le]
    linarith
  · rw [hx' hT0.le, dampedResp_crit hωd hr]
    ring

/-! ## The matrix exponential as the solution of `Ė = A E` -/

section MatrixExp

open scoped Matrix.Norms.Frobenius

variable {n : ℕ}

/-- Uniqueness of the matrix exponential: a differentiable `E` with `Ė = A E`, `E 0 = 1` is
`t ↦ e^{tA}`. -/
@[tmio T, powerlib_foundation] theorem exp_smul_eq_of_hasDerivAt {A : Matrix (Fin n) (Fin n) ℝ}
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
@[tmio T, powerlib_foundation] theorem exp_smul_of_sq_eq {A : Matrix (Fin n) (Fin n) ℝ} {a w : ℝ}
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
