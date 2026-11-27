import theorem.ParametricResonance.SmoothOrbitStability

/-! # The forced orbit of a smooth field driven by a multi-channel phasor source

`SmoothForcedOrbit` and `SmoothOrbitStability` take a scalar input with the drive
`w₀ + ε V̂ cos ωt`. A grid source is a phasor: its magnitude and its angle are two channels, and a
general oscillation source modulates both, with arbitrary relative phases (an interharmonic, for
instance, modulates them in quadrature). This file extends the end-to-end theorems to an input
`w ∈ ℝ^U` with the drive `w₀ + ε Re{ŵ e^{jωt}}`, `ŵ ∈ ℂ^U`:
* the forced response solves `(jωI − A₀) z = ∂_wF ŵ`;
* `A₁ = D_x(∂ₓF) z + D_w(∂ₓF) ŵ`;
* the criterion `|g/2| ≶ |λ₁|` (`g = u A₁ r̄`) decides the Floquet multipliers of the actual
  forced orbit, and in the stable case the orbit is exponentially stable.
For a field invariant under a joint shift of an angle state and the grid angle
(`F(x + s e, w + s u) = F(x, w)`, a grid-synchronized converter), the angle component of the
source enters only through the relative response: `∂_wF u = −A₀ e`, `D_w(∂ₓF) u = −D_x(∂ₓF) e`,
and `A₁(ŵ + θ̂u, z) = A₁(ŵ, z − θ̂e)`.

Model boundary.
* `F : ℝ^X × ℝ^U → ℝ^X` (finite `X`, `U`, sup norms), `ContDiffAt ℝ 3 F q₀`, `F q₀ = 0`; drive
  `w₀ + ε Re{ŵ e^{jωt}}` with a complex amplitude `ŵ`; state perturbation `εA₀'` with a constant
  real `A₀'`.
* The Floquet statements need real modal coordinates of `∂ₓF(q₀)` with the pair `±jω/2` and a
  stable block with one-period spectral radius `< 1`, as in `SmoothForcedOrbit`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07) §2.1–§2.2 (framework
`A₁ = Σ (∂A/∂x_l) z_l + G û` with an input vector `û`); the end-to-end statements for a
multi-channel phasor input are new.

Results.
* `jacXV`, `matXV`, `matXV_mulVec`, `smDxV`, `smMwV`, `linC`, `linC_harm`, `fderivWC`,
  `harm_fderivWC`, `norm_harm_le`, `smBV`, `smNV`, `smJV`, `smDuV`, `smA1V`,
  `smNV_rhs`, `norm_prod_zeroV`, `fderivWC_smul_ofv`, `linC_smul_ofv` — the forced system of a
  smooth field with a phasor input.
* `smooth_estimates_vec`, `smooth_link_vec` — the estimates and the harmonic data.
* `smooth_orbit_floquet_stable_vec`, `smooth_orbit_floquet_unstable_vec`,
  `smooth_orbit_exp_stable_vec` — end-to-end.
* `hasDerivAt_lineV`, `matXV_of_line`, `fderivW_of_lineV`, `hasDerivAt_matXV_line`,
  `smDxV_of_line`, `smMwV_of_line` — derivatives from directional derivatives.
* `fderiv_shift_eq_zero`, `fderivW_shift`, `jacXV_shift`, `smMwV_shift`, `fderivWC_shift`,
  `forced_shift`, `smA1V_shift` — shift-invariant fields: the angle channel acts on the relative
  response as the rate input `−jωθ̂ e`, and only the relative response enters `A₁`.
* `smDxV_eq_smDx`, `smMwV_eq_smM1` — the second derivatives from those of a scalar-input field.
* `uMag`, `uAng`, `gridSrc`, `harm_gridSrc`, `forced_gridSrc`, `smA1V_gridSrc` — the grid phasor
  source `(v̂, θ̂)` and the general source form of a grid-synchronized converter:
  `(jωI − A₀) z_rel = v̂ b_V − jωθ̂ e` and `A₁ = D_x(∂ₓF) z_rel + v̂ D_V(∂ₓF)`.
* `smooth_orbit_floquet_three_stable_vec`, `smooth_orbit_floquet_three_unstable_vec`,
  `smooth_orbit_exp_three_stable_vec` — three-state fields from their eigen-data.

Corrections.
None: an extension.

Family and connection conclusions.
None: static evidence on smooth periodically forced ODEs with a vector input.
-/

noncomputable section
namespace powerlib.ParametricResonance.ForcedOrbit
open Complex Matrix Set Filter Topology Metric
open scoped Matrix.Norms.Operator
open TwoToOne (base)
open BlockAveraging (expS modX physLeft physRight modalP modalQ modal_three norm_expS_one)

section Vec

variable {X U : Type*} [Fintype X] [DecidableEq X] [Fintype U]

/-- The partial Jacobian `∂ₓF(q)` of `F : ℝ^X × ℝ^U → ℝ^X`. -/
def jacXV (F : (X → ℝ) × (U → ℝ) → X → ℝ) (q : (X → ℝ) × (U → ℝ)) :
    (X → ℝ) →L[ℝ] (X → ℝ) :=
  (fderiv ℝ F q).comp (ContinuousLinearMap.inl ℝ (X → ℝ) (U → ℝ))

/-- Its matrix. -/
def matXV (F : (X → ℝ) × (U → ℝ) → X → ℝ) (q : (X → ℝ) × (U → ℝ)) : Matrix X X ℝ :=
  LinearMap.toMatrix' (jacXV F q : (X → ℝ) →ₗ[ℝ] (X → ℝ))

omit [Fintype U] in
@[tmio T, powerlib_foundation] theorem matXV_mulVec (F : (X → ℝ) × (U → ℝ) → X → ℝ)
    (q : (X → ℝ) × (U → ℝ)) (v : X → ℝ) : matXV F q *ᵥ v = fderiv ℝ F q (v, 0) := by
  rw [matXV, LinearMap.toMatrix'_mulVec]; rfl

/-- The second derivative `D_x(∂ₓF)(q₀) y` as a linear map into matrices. -/
def smDxV (F : (X → ℝ) × (U → ℝ) → X → ℝ) (q0 : (X → ℝ) × (U → ℝ)) :
    (X → ℝ) →ₗ[ℝ] Matrix X X ℝ where
  toFun y := LinearMap.toMatrix'
    ((fderiv ℝ (jacXV F) q0 (y, 0) : (X → ℝ) →L[ℝ] (X → ℝ)) : (X → ℝ) →ₗ[ℝ] (X → ℝ))
  map_add' y z := by
    rw [show ((y + z, (0 : U → ℝ)) : (X → ℝ) × (U → ℝ)) = (y, 0) + (z, 0) by simp, map_add,
      ContinuousLinearMap.toLinearMap_add, map_add]
  map_smul' c y := by
    rw [show ((c • y, (0 : U → ℝ)) : (X → ℝ) × (U → ℝ)) = c • (y, 0) by simp, map_smul,
      ContinuousLinearMap.toLinearMap_smul, map_smul]; rfl

/-- The mixed second derivative `D_w(∂ₓF)(q₀) a` as a linear map into matrices. -/
def smMwV (F : (X → ℝ) × (U → ℝ) → X → ℝ) (q0 : (X → ℝ) × (U → ℝ)) :
    (U → ℝ) →ₗ[ℝ] Matrix X X ℝ where
  toFun a := LinearMap.toMatrix'
    ((fderiv ℝ (jacXV F) q0 (0, a) : (X → ℝ) →L[ℝ] (X → ℝ)) : (X → ℝ) →ₗ[ℝ] (X → ℝ))
  map_add' a b := by
    rw [show (((0 : X → ℝ), a + b) : (X → ℝ) × (U → ℝ)) = (0, a) + (0, b) by simp, map_add,
      ContinuousLinearMap.toLinearMap_add, map_add]
  map_smul' c a := by
    rw [show (((0 : X → ℝ), c • a) : (X → ℝ) × (U → ℝ)) = c • (0, a) by simp, map_smul,
      ContinuousLinearMap.toLinearMap_smul, map_smul]; rfl

/-- A real-linear map into matrices applied to a complex vector: `M(Re w) + j M(Im w)`. -/
def linC (M : (U → ℝ) →ₗ[ℝ] Matrix X X ℝ) (w : U → ℂ) : Matrix X X ℂ :=
  fun i j => ⟨M (fun k => (w k).re) i j, M (fun k => (w k).im) i j⟩

omit [Fintype X] [DecidableEq X] [Fintype U] in
/-- `M Re{w e^{jωt}} = Re{(M w) e^{jωt}}`. -/
@[tmio T, powerlib_foundation] theorem linC_harm (M : (U → ℝ) →ₗ[ℝ] Matrix X X ℝ) (w : U → ℂ)
    (ω t : ℝ) : M (harm w ω t) = modX (linC M w) ω t := by
  have e : harm w ω t = Real.cos (ω * t) • (fun k => (w k).re) -
      Real.sin (ω * t) • (fun k => (w k).im) := by
    funext k; simp [harm]; ring
  rw [e, map_sub, map_smul, map_smul]
  ext i j
  simp [modX, linC]
  ring

/-- The input direction `∂_wF(q₀) ŵ` for a complex amplitude `ŵ`. -/
def fderivWC (F : (X → ℝ) × (U → ℝ) → X → ℝ) (q0 : (X → ℝ) × (U → ℝ)) (w : U → ℂ) : X → ℂ :=
  fun i => ⟨fderiv ℝ F q0 (0, fun k => (w k).re) i, fderiv ℝ F q0 (0, fun k => (w k).im) i⟩

omit [Fintype X] [DecidableEq X] [Fintype U] in
@[tmio T, powerlib_foundation] theorem harm_fderivWC (F : (X → ℝ) × (U → ℝ) → X → ℝ)
    (q0 : (X → ℝ) × (U → ℝ)) (w : U → ℂ) (ω t : ℝ) :
    harm (fderivWC F q0 w) ω t = fderiv ℝ F q0 (0, harm w ω t) := by
  have e : (((0 : X → ℝ), harm w ω t) : (X → ℝ) × (U → ℝ)) =
      Real.cos (ω * t) • ((0 : X → ℝ), fun k => (w k).re) -
        Real.sin (ω * t) • ((0 : X → ℝ), fun k => (w k).im) := by
    ext k
    · simp
    · simp [harm]; ring
  rw [e, map_sub, map_smul, map_smul]
  funext i
  simp [harm, fderivWC]
  ring

@[tmio T, powerlib_foundation] theorem norm_harm_le (w : U → ℂ) (ω t : ℝ) :
    ‖harm w ω t‖ ≤ 2 * ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
  have h1 := Complex.abs_re_le_norm (w k)
  have h2 := Complex.abs_im_le_norm (w k)
  have h3 := norm_le_pi_norm w k
  have hc := Real.abs_cos_le_one (ω * t)
  have hs := Real.abs_sin_le_one (ω * t)
  rw [Real.norm_eq_abs]
  simp only [harm]
  calc |(w k).re * Real.cos (ω * t) - (w k).im * Real.sin (ω * t)|
      ≤ |(w k).re| * |Real.cos (ω * t)| + |(w k).im| * |Real.sin (ω * t)| := by
        rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
    _ ≤ ‖w k‖ * 1 + ‖w k‖ * 1 := by gcongr
    _ ≤ 2 * ‖w‖ := by linarith

/-- The forcing `b(t) = ∂_wF(q₀) Re{ŵ e^{jωt}}`. -/
def smBV (F : (X → ℝ) × (U → ℝ) → X → ℝ) (q0 : (X → ℝ) × (U → ℝ)) (w : U → ℂ) (ω t : ℝ) :
    X → ℝ :=
  fderiv ℝ F q0 (0, harm w ω t)

/-- The nonlinear remainder of `y ↦ F(x₀ + y, w₀ + ε Re{ŵ e^{jωt}}) + ε A₀' y`. -/
def smNV (F : (X → ℝ) × (U → ℝ) → X → ℝ) (q0 : (X → ℝ) × (U → ℝ)) (w : U → ℂ) (ω : ℝ)
    (A0' : Matrix X X ℝ) (ε t : ℝ) (y : X → ℝ) : X → ℝ :=
  F (q0.1 + y, q0.2 + ε • harm w ω t) + ε • (A0' *ᵥ y) - matXV F q0 *ᵥ y - ε • smBV F q0 w ω t

/-- The variational matrix `∂ₓF(x₀ + y, w₀ + ε Re{ŵ e^{jωt}}) + ε A₀'`. -/
def smJV (F : (X → ℝ) × (U → ℝ) → X → ℝ) (q0 : (X → ℝ) × (U → ℝ)) (w : U → ℂ) (ω : ℝ)
    (A0' : Matrix X X ℝ) (ε t : ℝ) (y : X → ℝ) : Matrix X X ℝ :=
  matXV F (q0.1 + y, q0.2 + ε • harm w ω t) + ε • A0'

/-- `D_u(t) = A₀' + D_w(∂ₓF)(q₀) Re{ŵ e^{jωt}}`. -/
def smDuV (F : (X → ℝ) × (U → ℝ) → X → ℝ) (q0 : (X → ℝ) × (U → ℝ)) (w : U → ℂ) (ω : ℝ)
    (A0' : Matrix X X ℝ) (t : ℝ) : Matrix X X ℝ :=
  A0' + smMwV F q0 (harm w ω t)

/-- The modulation `A₁ = D_x(∂ₓF)(q₀) z + D_w(∂ₓF)(q₀) ŵ`. -/
def smA1V (F : (X → ℝ) × (U → ℝ) → X → ℝ) (q0 : (X → ℝ) × (U → ℝ)) (w : U → ℂ)
    (z : X → ℂ) : Matrix X X ℂ :=
  DxC (smDxV F q0) z + linC (smMwV F q0) w

omit [Fintype U] in
@[tmio T, powerlib_foundation] theorem smNV_rhs (F : (X → ℝ) × (U → ℝ) → X → ℝ)
    (q0 : (X → ℝ) × (U → ℝ)) (w : U → ℂ) (ω : ℝ) (A0' : Matrix X X ℝ) (ε t : ℝ) (y : X → ℝ) :
    matXV F q0 *ᵥ y + (ε • smBV F q0 w ω t + smNV F q0 w ω A0' ε t y) =
      F (q0.1 + y, q0.2 + ε • harm w ω t) + ε • (A0' *ᵥ y) := by
  simp only [smNV]; abel

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem norm_prod_zeroV (y : X → ℝ) :
    ‖((y, (0 : U → ℝ)) : (X → ℝ) × (U → ℝ))‖ = ‖y‖ := by
  rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]

/-- The estimates of `forced_orbit` and `orbit_variational` for a `C³` vector field with an
equilibrium at `q₀` and the drive `w₀ + ε Re{ŵ e^{jωt}}`. -/
@[tmio T, powerlib_foundation] theorem smooth_estimates_vec {F : (X → ℝ) × (U → ℝ) → X → ℝ}
    {q0 : (X → ℝ) × (U → ℝ)} (hF : ContDiffAt ℝ 3 F q0) (hF0 : F q0 = 0) (w : U → ℂ) (ω : ℝ)
    (A0' : Matrix X X ℝ) :
    ∃ K ρ ε0 KJ KD : ℝ, 0 ≤ K ∧ 0 < ρ ∧ 0 < ε0 ∧ 0 ≤ KJ ∧ 0 ≤ KD ∧
      (∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × (X → ℝ) => smNV F q0 w ω A0' ε p.1 p.2)
        (Set.univ ×ˢ closedBall 0 ρ)) ∧
      (∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t, ‖smNV F q0 w ω A0' ε t 0‖ ≤ K * ε ^ 2) ∧
      (∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y1 y2, ‖y1‖ ≤ ρ → ‖y2‖ ≤ ρ →
        ‖smNV F q0 w ω A0' ε t y1 - smNV F q0 w ω A0' ε t y2‖ ≤
          K * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖) ∧
      (∀ v, ‖smDxV F q0 v‖ ≤ KD * ‖v‖) ∧
      (∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × (X → ℝ) => smJV F q0 w ω A0' ε p.1 p.2)
        (Set.univ ×ˢ closedBall 0 ρ)) ∧
      ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y, ‖y‖ ≤ ρ →
        ‖smJV F q0 w ω A0' ε t y - matXV F q0 - smDxV F q0 y - ε • smDuV F q0 w ω A0' t‖ ≤
          KJ * (‖y‖ ^ 2 + ε ^ 2) := by
  have hF2 : ContDiffAt ℝ 2 F q0 := hF.of_le (by norm_num)
  have hJ2 : ContDiffAt ℝ 2 (jacXV F) q0 :=
    (hF.fderiv_right (m := 2) (by norm_num)).clm_comp contDiffAt_const
  obtain ⟨r1, L1, hr1, hL1, hd1, hl1⟩ := exists_taylor_ball hF2
  obtain ⟨r2, L2, hr2, hL2, hd2, hl2⟩ := exists_taylor_ball hJ2
  set r := min r1 r2 with hr
  have hr0 : 0 < r := lt_min hr1 hr2
  set a := 2 * ‖w‖ with ha
  have ha0 : 0 ≤ a := by positivity
  set D2 := fderiv ℝ (jacXV F) q0 with hD2
  set qp : ℝ → ℝ → (X → ℝ) → (X → ℝ) × (U → ℝ) :=
    fun ε t y => (q0.1 + y, q0.2 + ε • harm w ω t) with hqp
  have hqd : ∀ ε t y, qp ε t y - q0 = (y, ε • harm w ω t) := by
    intro ε t y; ext <;> simp [hqp]
  have hva : ∀ t, ‖harm w ω t‖ ≤ a := fun t => norm_harm_le w ω t
  have hqn : ∀ ε t y, 0 ≤ ε → ‖qp ε t y - q0‖ ≤ max ‖y‖ (ε * a) := by
    intro ε t y hε
    rw [hqd, Prod.norm_def, norm_smul, Real.norm_of_nonneg hε]
    exact max_le_max le_rfl (mul_le_mul_of_nonneg_left (hva t) hε)
  have hεa : ∀ ε, 0 ≤ ε → ε ≤ r / (3 * (a + 1)) → ε * a ≤ r / 3 := by
    intro ε hε h
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  have hr13 : r / 3 ≤ r1 := (div_le_self hr0.le (by norm_num)).trans (min_le_left _ _)
  have hr23 : r / 3 ≤ r2 := (div_le_self hr0.le (by norm_num)).trans (min_le_right _ _)
  have hc : ∀ ε, Continuous (fun p : ℝ × (X → ℝ) => qp ε p.1 p.2) := fun ε => by
    simp only [hqp]
    exact (continuous_const.add continuous_snd).prodMk
      (continuous_const.add (((continuous_harm w ω).comp continuous_fst).const_smul ε))
  have hmap : ∀ ε, 0 ≤ ε → ε ≤ r / (3 * (a + 1)) → ∀ ρ', r / 3 ≤ ρ' →
      MapsTo (fun p : ℝ × (X → ℝ) => qp ε p.1 p.2) (Set.univ ×ˢ closedBall 0 (r / 3))
        (closedBall q0 ρ') := by
    rintro ε hε hεe ρ' hρ' ⟨t, y⟩ ⟨-, hy⟩
    rw [mem_closedBall_iff_norm]
    refine (hqn ε t y hε).trans (max_le ?_ ((hεa ε hε hεe).trans hρ'))
    exact (mem_closedBall_zero_iff.1 hy).trans hρ'
  have hsq : ∀ ε t y, 0 ≤ ε →
      ‖qp ε t y - q0‖ * ‖qp ε t y - q0‖ ≤ (1 + a ^ 2) * (‖y‖ ^ 2 + ε ^ 2) := by
    intro ε t y hε
    have h := hqn ε t y hε
    have h0 := norm_nonneg (qp ε t y - q0)
    have hm : ‖qp ε t y - q0‖ * ‖qp ε t y - q0‖ ≤ ‖y‖ ^ 2 + (ε * a) ^ 2 := by
      rcases le_total ‖y‖ (ε * a) with h1 | h1
      · rw [max_eq_right h1] at h; nlinarith [norm_nonneg y]
      · rw [max_eq_left h1] at h; nlinarith [mul_nonneg hε ha0]
    nlinarith [sq_nonneg ε, sq_nonneg a, sq_nonneg ‖y‖, mul_nonneg (sq_nonneg a) (sq_nonneg ‖y‖)]
  refine ⟨L1 * (1 + a) + ‖A0'‖ + L1 * a ^ 2, r / 3, r / (3 * (a + 1)),
    L2 * (1 + a ^ 2), ‖D2‖, by positivity, by positivity, by positivity, by positivity,
    by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ε hε hεe
    have hFon : ContinuousOn F (closedBall q0 r1) := fun q hq =>
      (hd1 q hq).continuousAt.continuousWithinAt
    have h1 := hFon.comp (hc ε).continuousOn (hmap ε hε hεe r1 hr13)
    have h2 : Continuous fun p : ℝ × (X → ℝ) => ε • (A0' *ᵥ p.2) :=
      (continuous_const.matrix_mulVec continuous_snd).const_smul ε
    have h3 : Continuous fun p : ℝ × (X → ℝ) => matXV F q0 *ᵥ p.2 :=
      continuous_const.matrix_mulVec continuous_snd
    have h4 : Continuous fun p : ℝ × (X → ℝ) => ε • smBV F q0 w ω p.1 := by
      simp only [smBV]
      exact ((fderiv ℝ F q0).continuous.comp (continuous_const.prodMk
        ((continuous_harm w ω).comp continuous_fst))).const_smul ε
    exact ((h1.add h2.continuousOn).sub h3.continuousOn).sub h4.continuousOn
  · intro ε hε hεe t
    have hsplit : ((0 : X → ℝ), ε • harm w ω t) = ε • ((0 : X → ℝ), harm w ω t) := by
      ext <;> simp
    have e : smNV F q0 w ω A0' ε t 0 =
        F (qp ε t 0) - F q0 - fderiv ℝ F q0 (qp ε t 0 - q0) := by
      rw [hqd, hF0, sub_zero, hsplit, map_smul]
      simp only [smNV, smBV, hqp, Matrix.mulVec_zero, smul_zero, add_zero, sub_zero]
    rw [e]
    have hm : ‖qp ε t 0 - q0‖ ≤ ε * a := by
      have := hqn ε t 0 hε; rwa [norm_zero, max_eq_right (by positivity)] at this
    have hb := taylor_sub hL1 hd1 hl1 (m := ‖qp ε t 0 - q0‖)
      (hm.trans ((hεa ε hε hεe).trans hr13))
      (q1 := qp ε t 0) (q2 := q0) (by rw [mem_closedBall_iff_norm])
      (mem_closedBall_self (norm_nonneg _))
    refine hb.trans ?_
    have h0 := norm_nonneg (qp ε t 0 - q0)
    calc L1 * ‖qp ε t 0 - q0‖ * ‖qp ε t 0 - q0‖ ≤ L1 * (ε * a) * (ε * a) := by gcongr
      _ ≤ (L1 * (1 + a) + ‖A0'‖ + L1 * a ^ 2) * ε ^ 2 := by
          nlinarith [mul_nonneg hL1 ha0, norm_nonneg A0', sq_nonneg ε,
            mul_nonneg hL1 (sq_nonneg ε)]
  · intro ε hε hεe t y1 y2 hy1 hy2
    have hq12 : qp ε t y1 - qp ε t y2 = (y1 - y2, 0) := by ext <;> simp [hqp]
    have e : smNV F q0 w ω A0' ε t y1 - smNV F q0 w ω A0' ε t y2 =
        (F (qp ε t y1) - F (qp ε t y2) - fderiv ℝ F q0 (qp ε t y1 - qp ε t y2)) +
          ε • (A0' *ᵥ (y1 - y2)) := by
      rw [hq12, ← matXV_mulVec]
      simp only [smNV, hqp, Matrix.mulVec_sub, smul_sub]; abel
    rw [e, hq12]
    set m := ‖y1‖ + ‖y2‖ + ε * a with hmd
    have hm1 : ‖qp ε t y1 - q0‖ ≤ m := (hqn ε t y1 hε).trans (max_le (by
      have := norm_nonneg y2; have := mul_nonneg hε ha0; linarith) (by
      have := norm_nonneg y1; have := norm_nonneg y2; linarith))
    have hm2 : ‖qp ε t y2 - q0‖ ≤ m := (hqn ε t y2 hε).trans (max_le (by
      have := norm_nonneg y1; have := mul_nonneg hε ha0; linarith) (by
      have := norm_nonneg y1; have := norm_nonneg y2; linarith))
    have hmr : m ≤ r1 := by
      have := hεa ε hε hεe
      have : r / 3 + r / 3 + r / 3 ≤ r1 := by linarith [min_le_left r1 r2]
      linarith
    have hb := taylor_sub hL1 hd1 hl1 hmr (by rw [mem_closedBall_iff_norm]; exact hm1)
      (by rw [mem_closedBall_iff_norm]; exact hm2)
    rw [hq12, norm_prod_zeroV] at hb
    have hA : ‖ε • (A0' *ᵥ (y1 - y2))‖ ≤ ε * ‖A0'‖ * ‖y1 - y2‖ := by
      rw [norm_smul, Real.norm_of_nonneg hε, mul_assoc]
      exact mul_le_mul_of_nonneg_left (Matrix.linfty_opNorm_mulVec _ _) hε
    have hd0 := norm_nonneg (y1 - y2)
    have hn1 := norm_nonneg y1
    have hn2 := norm_nonneg y2
    calc _ ≤ L1 * m * ‖y1 - y2‖ + ε * ‖A0'‖ * ‖y1 - y2‖ :=
          (norm_add_le _ _).trans (add_le_add hb hA)
      _ ≤ (L1 * (1 + a) + ‖A0'‖ + L1 * a ^ 2) * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖ := by
          rw [hmd]
          have hA0 := norm_nonneg A0'
          have hk : L1 * (‖y1‖ + ‖y2‖ + ε * a) + ε * ‖A0'‖ ≤
              (L1 * (1 + a) + ‖A0'‖ + L1 * a ^ 2) * (‖y1‖ + ‖y2‖ + ε) := by
            nlinarith [mul_nonneg hL1 ha0, mul_nonneg (mul_nonneg hL1 ha0) (add_nonneg hn1 hn2),
              mul_nonneg hA0 (add_nonneg hn1 hn2), mul_nonneg (mul_nonneg hL1 (sq_nonneg a))
                (add_nonneg (add_nonneg hn1 hn2) hε), mul_nonneg hL1 hε]
          nlinarith [mul_le_mul_of_nonneg_right hk hd0]
  · intro v
    show ‖LinearMap.toMatrix' ((D2 (v, 0) : (X → ℝ) →L[ℝ] (X → ℝ)) :
      (X → ℝ) →ₗ[ℝ] (X → ℝ))‖ ≤ _
    rw [Matrix.linfty_opNorm_toMatrix]
    exact (D2.le_opNorm _).trans_eq (by rw [norm_prod_zeroV])
  · intro ε hε hεe
    have hJon : ContinuousOn (jacXV F) (closedBall q0 r2) := fun q hq =>
      (hd2 q hq).continuousAt.continuousWithinAt
    have h1 := continuous_toMatrix.comp_continuousOn
      (hJon.comp (hc ε).continuousOn (hmap ε hε hεe r2 hr23))
    exact h1.add continuousOn_const
  · intro ε hε hεe t y hy
    have hsplit : (y, ε • harm w ω t) =
        ((y, (0 : U → ℝ)) : (X → ℝ) × (U → ℝ)) + ε • ((0 : X → ℝ), harm w ω t) := by
      ext <;> simp
    have e : smJV F q0 w ω A0' ε t y - matXV F q0 - smDxV F q0 y - ε • smDuV F q0 w ω A0' t =
        LinearMap.toMatrix' ((jacXV F (qp ε t y) - jacXV F q0 - D2 (qp ε t y - q0) :
          (X → ℝ) →L[ℝ] (X → ℝ)) : (X → ℝ) →ₗ[ℝ] (X → ℝ)) := by
      rw [hqd, hsplit, map_add, map_smul]
      simp only [smJV, smDuV, smDxV, smMwV, matXV, hqp, LinearMap.coe_mk, AddHom.coe_mk,
        ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_add,
        ContinuousLinearMap.toLinearMap_smul, map_sub, map_add, map_smul, smul_add]
      abel
    rw [e, Matrix.linfty_opNorm_toMatrix]
    have hm := (hqn ε t y hε).trans (max_le hy ((hεa ε hε hεe)))
    have hb := taylor_sub hL2 hd2 hl2 (m := ‖qp ε t y - q0‖) (hm.trans hr23)
      (q1 := qp ε t y) (q2 := q0) (by rw [mem_closedBall_iff_norm])
      (mem_closedBall_self (norm_nonneg _))
    refine hb.trans ?_
    rw [mul_assoc]
    calc L2 * (‖qp ε t y - q0‖ * ‖qp ε t y - q0‖) ≤ L2 * ((1 + a ^ 2) * (‖y‖ ^ 2 + ε ^ 2)) :=
          mul_le_mul_of_nonneg_left (hsq ε t y hε) hL2
      _ = _ := by ring

/-- The common data: the forcing is harmonic, `y_p = Re{z e^{jωt}}` solves the linearization and
`D_x y_p + D_u = A₀' + Re{A₁ e^{jωt}}`. -/
@[tmio T, powerlib_foundation] theorem smooth_link_vec (F : (X → ℝ) × (U → ℝ) → X → ℝ)
    (q0 : (X → ℝ) × (U → ℝ)) {w : U → ℂ} {ω : ℝ} (hω : ω ≠ 0) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matXV F q0).map (algebraMap ℝ ℂ) *ᵥ z = fderivWC F q0 w)
    (A0' : Matrix X X ℝ) :
    Continuous (smBV F q0 w ω) ∧
      (∀ t, smBV F q0 w ω (t + 2 * Real.pi / ω) = smBV F q0 w ω t) ∧
      (∀ ε t y, smNV F q0 w ω A0' ε (t + 2 * Real.pi / ω) y = smNV F q0 w ω A0' ε t y) ∧
      Continuous (smDuV F q0 w ω A0') ∧
      (∀ t, harm z ω (t + 2 * Real.pi / ω) = harm z ω t) ∧
      (∀ t, HasDerivAt (harm z ω) (matXV F q0 *ᵥ harm z ω t + smBV F q0 w ω t) t) ∧
      ∀ t, smDxV F q0 (harm z ω t) + smDuV F q0 w ω A0' t = A0' + modX (smA1V F q0 w z) ω t := by
  refine ⟨?_, fun t => by simp only [smBV, harm_periodic w hω t],
    fun ε t y => by simp only [smNV, smBV, harm_periodic w hω t], ?_,
    fun t => harm_periodic z hω t, fun t => ?_, fun t => ?_⟩
  · exact (fderiv ℝ F q0).continuous.comp (continuous_const.prodMk (continuous_harm w ω))
  · exact continuous_const.add
      ((LinearMap.continuous_of_finiteDimensional (smMwV F q0)).comp (continuous_harm w ω))
  · have h := harm_hasDerivAt hz t
    rwa [harm_fderivWC] at h
  · rw [Dx_harm, smA1V, modX_add, smDuV, linC_harm]; abel

/-- End-to-end for a `C³` vector field with a vector input, stability. `F(x₀, w₀) = 0`, drive
`w₀ + ε Re{ŵ e^{jωt}}` with a complex amplitude `ŵ` (any relative phases between the input
channels), state matrix perturbation `ε A₀'`; `∂ₓF(q₀)` has real modal coordinates with the pair
`±jω/2`; `z` the first-order forced response. If `Re λ₁ < 0` and `|g/2| < |λ₁|`
(`g = u A₁ r̄`, `A₁ = smA1V`), then for all small `ε > 0` the forced orbit exists and every
Floquet multiplier of its variational equation lies inside the unit circle. -/
@[tmio T, powerlib_foundation] theorem smooth_orbit_floquet_stable_vec {Y : Type*} [Fintype Y]
    [DecidableEq Y] {F : (X → ℝ) × (U → ℝ) → X → ℝ}
    {q0 : (X → ℝ) × (U → ℝ)} (hF : ContDiffAt ℝ 3 F q0) (hF0 : F q0 = 0) {w : U → ℂ} {ω : ℝ}
    (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matXV F q0 * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matXV F q0).map (algebraMap ℝ ℂ) *ᵥ z = fderivWC F q0 w)
    (A0' : Matrix X X ℝ)
    (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hg : ‖physLeft Q ⬝ᵥ (smA1V F q0 w z *ᵥ star (physRight P)) / 2‖ ^ 2 <
      ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
        (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : X → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => smJV F q0 w ω A0' ε t (y t)) (2 * Real.pi / ω) 0).map
            (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  obtain ⟨K, ρ, ε0, KJ, KD, hK, hρ, hε0, hKJ, hKD, hNc, hN0, hNL, hDx, hJc, hJ⟩ :=
    smooth_estimates_vec hF hF0 w ω A0'
  obtain ⟨Minv, hL, hR⟩ := exists_minv_of_modal hω hPQ hQP As hA0 hsr
  obtain ⟨hb, hbp, hNp, hDu, hpp, hpd, hlink⟩ := smooth_link_vec F q0 hω.ne' hz A0'
  have h := orbit_floquet_stable (by positivity) hL hR hb hbp hK hρ hε0 hNc hNp hN0 hNL hKJ hKD
    hDx hDu hJc hJ hpp hpd hω rfl hPQ hQP As hA0 hsr A0' (smA1V F q0 w z) hlink hs hg
  simp only [smNV_rhs] at h
  exact h

/-- End-to-end for a `C³` vector field with a vector input, parametric instability:
`|λ₁| < |g/2|`. -/
@[tmio T, powerlib_foundation] theorem smooth_orbit_floquet_unstable_vec {Y : Type*} [Fintype Y]
    [DecidableEq Y] {F : (X → ℝ) × (U → ℝ) → X → ℝ}
    {q0 : (X → ℝ) × (U → ℝ)} (hF : ContDiffAt ℝ 3 F q0) (hF0 : F q0 = 0) {w : U → ℂ} {ω : ℝ}
    (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matXV F q0 * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matXV F q0).map (algebraMap ℝ ℂ) *ᵥ z = fderivWC F q0 w)
    (A0' : Matrix X X ℝ)
    (hg : ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2 <
      ‖physLeft Q ⬝ᵥ (smA1V F q0 w z *ᵥ star (physRight P)) / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
        (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV F q0 w ω A0' ε t (y t)) (2 * Real.pi / ω) := by
  obtain ⟨K, ρ, ε0, KJ, KD, hK, hρ, hε0, hKJ, hKD, hNc, hN0, hNL, hDx, hJc, hJ⟩ :=
    smooth_estimates_vec hF hF0 w ω A0'
  obtain ⟨Minv, hL, hR⟩ := exists_minv_of_modal hω hPQ hQP As hA0 hsr
  obtain ⟨hb, hbp, hNp, hDu, hpp, hpd, hlink⟩ := smooth_link_vec F q0 hω.ne' hz A0'
  have h := orbit_floquet_unstable (by positivity) hL hR hb hbp hK hρ hε0 hNc hNp hN0 hNL hKJ hKD
    hDx hDu hJc hJ hpp hpd hω rfl hPQ hQP As hA0 hsr A0' (smA1V F q0 w z) hlink hg
  simp only [smNV_rhs] at h
  exact h

/-- End-to-end with orbital stability for a vector input: under the hypotheses of
`smooth_orbit_floquet_stable_vec`, for all small `ε > 0` the forced orbit is locally
exponentially stable for the nonlinear driven system. -/
@[tmio T, powerlib_foundation] theorem smooth_orbit_exp_stable_vec {Y : Type*} [Fintype Y]
    [DecidableEq Y] {F : (X → ℝ) × (U → ℝ) → X → ℝ}
    {q0 : (X → ℝ) × (U → ℝ)} (hF : ContDiffAt ℝ 3 F q0) (hF0 : F q0 = 0) {w : U → ℂ} {ω : ℝ}
    (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matXV F q0 * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matXV F q0).map (algebraMap ℝ ℂ) *ᵥ z = fderivWC F q0 w)
    (A0' : Matrix X X ℝ)
    (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hg : ‖physLeft Q ⬝ᵥ (smA1V F q0 w z *ᵥ star (physRight P)) / 2‖ ^ 2 <
      ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ,
      (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
      (∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → X → ℝ),
        IsIntegralCurveOn x (fun t v => F (q0.1 + v, q0.2 + ε • harm w ω t) +
          ε • (A0' *ᵥ v)) (Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  obtain ⟨c, hc, hex, hfl⟩ := smooth_orbit_floquet_stable_vec hF hF0 hω hPQ hQP As hA0 hsr hz A0'
    hs hg
  obtain ⟨-, ρ, ε0, -, -, -, hρ, hε0, -, -, -, -, -, -, hJc, -⟩ :=
    smooth_estimates_vec hF hF0 w ω A0'
  obtain ⟨R, KL, hR, hKL, hd, hl⟩ :=
    exists_lipschitz_ball (hF.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
  refine ⟨c, hc, ?_⟩
  set a := 2 * ‖w‖ with ha
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ ε0 ∧ c * ε ≤ ρ ∧ c * ε ≤ R / 3 ∧ ε * a ≤ R / 3 := by
    have hlim : Tendsto (fun ε : ℝ => (ε, c * ε, c * ε, ε * a)) (𝓝[>] 0)
        (𝓝 (0, 0, 0, 0)) := by
      have hcont : Continuous (fun ε : ℝ => (ε, c * ε, c * ε, ε * a)) := by fun_prop
      have h0 := hcont.tendsto 0
      simp only [mul_zero, zero_mul] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have hopen : ∀ᶠ p : ℝ × ℝ × ℝ × ℝ in 𝓝 (0, 0, 0, 0),
        p.1 < ε0 ∧ p.2.1 < ρ ∧ p.2.2.1 < R / 3 ∧ p.2.2.2 < R / 3 := by
      refine ((continuous_fst.tendsto _).eventually (gt_mem_nhds hε0)).and
        (((continuous_fst.comp continuous_snd).tendsto _).eventually (gt_mem_nhds hρ) |>.and
        ((((continuous_fst.comp (continuous_snd.comp continuous_snd)).tendsto _).eventually
          (gt_mem_nhds (by positivity : (0 : ℝ) < R / 3))).and
        (((continuous_snd.comp (continuous_snd.comp continuous_snd)).tendsto _).eventually
          (gt_mem_nhds (by positivity : (0 : ℝ) < R / 3)))))
    filter_upwards [hlim.eventually hopen] with ε hε
    exact ⟨hε.1.le, hε.2.1.le, hε.2.2.1.le, hε.2.2.2.le⟩
  filter_upwards [hex, hfl, hsmall, self_mem_nhdsWithin] with ε hεex hεfl ⟨hε0', hcρ, hcR, hVR⟩
    hεpos
  obtain ⟨y, hper, hbd, hode⟩ := hεex
  refine ⟨y, hper, hbd, hode, ?_⟩
  have hεpos' : 0 < ε := hεpos
  have hT : 0 < 2 * Real.pi / ω := by positivity
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hode t).continuousAt
  have hJcont : Continuous fun t => smJV F q0 w ω A0' ε t (y t) :=
    (hJc ε hεpos'.le hε0').comp_continuous (continuous_id.prodMk hyc) fun t =>
      Set.mk_mem_prod (Set.mem_univ _) (mem_closedBall_zero_iff.2 ((hbd t).trans hcρ))
  have hJp : Function.Periodic (fun t => smJV F q0 w ω A0' ε t (y t)) (2 * Real.pi / ω) := by
    intro t
    simp only [smJV, hper t, harm_periodic w hω.ne' t]
  have hsr' := spectralRadius_lt_one_of_eig _ (hεfl y hper hbd hode)
  have hpt : ∀ t (v : X → ℝ), ‖v - y t‖ ≤ R / 3 →
      ‖((q0.1 + v, q0.2 + ε • harm w ω t) : (X → ℝ) × (U → ℝ)) - q0‖ ≤ 2 * R / 3 := by
    intro t v hv
    have h1 : ‖v‖ ≤ 2 * R / 3 := by
      have h2 : ‖v‖ ≤ ‖y t‖ + ‖v - y t‖ := by
        have := norm_add_le (y t) (v - y t); simpa using this
      linarith [hbd t]
    have h3 : ‖ε • harm w ω t‖ ≤ 2 * R / 3 := by
      rw [norm_smul, Real.norm_of_nonneg hεpos'.le]
      have := mul_le_mul_of_nonneg_left (norm_harm_le w ω t) hεpos'.le
      linarith
    rw [Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub, add_sub_cancel_left]
    exact max_le h1 h3
  have hGc : ContinuousOn (fun p : ℝ × (X → ℝ) =>
      F (q0.1 + p.2, q0.2 + ε • harm w ω p.1) + ε • (A0' *ᵥ p.2))
      {p | ‖p.2 - y p.1‖ ≤ R / 3} := by
    intro p hp
    have hφ : Continuous fun p : ℝ × (X → ℝ) =>
        ((q0.1 + p.2, q0.2 + ε • harm w ω p.1) : (X → ℝ) × (U → ℝ)) :=
      (continuous_const.add continuous_snd).prodMk
        (continuous_const.add (((continuous_harm w ω).comp continuous_fst).const_smul ε))
    have hmem : ((q0.1 + p.2, q0.2 + ε • harm w ω p.1) : (X → ℝ) × (U → ℝ)) ∈
        closedBall q0 R := by
      rw [mem_closedBall, dist_eq_norm]; have := hpt p.1 p.2 hp; linarith
    refine ContinuousWithinAt.add ?_ ?_
    · have hca := ContinuousAt.comp (g := F) (x := p) (f := fun p : ℝ × (X → ℝ) =>
        ((q0.1 + p.2, q0.2 + ε • harm w ω p.1) : (X → ℝ) × (U → ℝ)))
        (hd _ hmem).continuousAt hφ.continuousAt
      exact hca.continuousWithinAt
    · exact (by fun_prop : Continuous fun p : ℝ × (X → ℝ) => ε • (A0' *ᵥ p.2)).continuousWithinAt
  have hRem : ∀ t (e : X → ℝ), ‖e‖ ≤ R / 3 →
      ‖(F (q0.1 + (y t + e), q0.2 + ε • harm w ω t) + ε • (A0' *ᵥ (y t + e))) -
        (F (q0.1 + y t, q0.2 + ε • harm w ω t) + ε • (A0' *ᵥ y t)) -
        smJV F q0 w ω A0' ε t (y t) *ᵥ e‖ ≤ KL * ‖e‖ ^ 2 := by
    intro t e he
    set b : (X → ℝ) × (U → ℝ) := (q0.1 + y t, q0.2 + ε • harm w ω t) with hbd'
    have hb : ‖b - q0‖ ≤ 2 * R / 3 := hpt t (y t) (by simp; positivity)
    have hsub : closedBall b ‖((e, (0 : U → ℝ)) : (X → ℝ) × (U → ℝ))‖ ⊆ closedBall q0 R := by
      intro q hq
      rw [mem_closedBall, dist_eq_norm] at hq ⊢
      rw [norm_prod_zeroV] at hq
      have := norm_sub_le_norm_sub_add_norm_sub q b q0
      linarith
    have hq := quad_remainder hKL hd hl hsub
    rw [norm_prod_zeroV] at hq
    have e1 : ((q0.1 + (y t + e), q0.2 + ε • harm w ω t) : (X → ℝ) × (U → ℝ)) = b + (e, 0) := by
      rw [hbd']; ext <;> simp [add_assoc]
    have e2 : smJV F q0 w ω A0' ε t (y t) *ᵥ e = fderiv ℝ F b (e, 0) + ε • (A0' *ᵥ e) := by
      rw [smJV, Matrix.add_mulVec, Matrix.smul_mulVec, matXV_mulVec]
    rw [e1, e2, Matrix.mulVec_add, smul_add]
    convert hq using 2
    abel
  exact Periodic.exp_stable_of_floquet hT hJcont hJp hsr' hode (by positivity) hKL hGc hRem

/-! ### Derivatives from directional derivatives -/

omit [Fintype X] [DecidableEq X] [Fintype U] in
@[tmio T, powerlib_foundation] theorem hasDerivAt_lineV {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (q v : E) : HasDerivAt (fun s : ℝ => q + s • v) v 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q

/-- The partial Jacobian from directional derivatives along `x + s y`. -/
@[tmio T, powerlib_foundation] theorem matXV_of_line {F : (X → ℝ) × (U → ℝ) → X → ℝ}
    {q : (X → ℝ) × (U → ℝ)} (hF : DifferentiableAt ℝ F q) {M : Matrix X X ℝ}
    (h : ∀ y, HasDerivAt (fun s : ℝ => F (q.1 + s • y, q.2)) (M *ᵥ y) 0) : matXV F q = M := by
  have hv : ∀ y, matXV F q *ᵥ y = M *ᵥ y := fun y => by
    rw [matXV_mulVec]
    have hl := hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      (hasDerivAt_lineV q ((y, (0 : U → ℝ)) : (X → ℝ) × (U → ℝ))) (by simp)
    have e : ∀ s : ℝ, q + s • ((y, (0 : U → ℝ)) : (X → ℝ) × (U → ℝ)) = (q.1 + s • y, q.2) :=
      fun s => by ext <;> simp
    simp only [Function.comp_def, e] at hl
    exact hl.unique (h y)
  ext i j
  have := congrFun (hv (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

omit [DecidableEq X] in
/-- The input derivative `∂_wF(q) a` from the directional derivative along `w + s a`. -/
@[tmio T, powerlib_foundation] theorem fderivW_of_lineV {F : (X → ℝ) × (U → ℝ) → X → ℝ}
    {q : (X → ℝ) × (U → ℝ)} (hF : DifferentiableAt ℝ F q) (a : U → ℝ) {b : X → ℝ}
    (h : HasDerivAt (fun s : ℝ => F (q.1, q.2 + s • a)) b 0) : fderiv ℝ F q (0, a) = b := by
  have hl := hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
    (hasDerivAt_lineV q (((0 : X → ℝ), a) : (X → ℝ) × (U → ℝ))) (by simp)
  have e : ∀ s : ℝ, q + s • (((0 : X → ℝ), a) : (X → ℝ) × (U → ℝ)) = (q.1, q.2 + s • a) :=
    fun s => by ext <;> simp
  simp only [Function.comp_def, e] at hl
  exact hl.unique h

/-- The entries of `∂ₓF` along a line through `q₀` have the derivatives of the second
derivative `D(∂ₓF)(q₀) v`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_matXV_line {F : (X → ℝ) × (U → ℝ) → X → ℝ}
    {q0 : (X → ℝ) × (U → ℝ)} (hF : ContDiffAt ℝ 2 F q0) (v : (X → ℝ) × (U → ℝ)) (i j : X) :
    HasDerivAt (fun t : ℝ => matXV F (q0 + t • v) i j)
      (LinearMap.toMatrix' ((fderiv ℝ (jacXV F) q0 v : (X → ℝ) →L[ℝ] (X → ℝ)) :
        (X → ℝ) →ₗ[ℝ] (X → ℝ)) i j) 0 := by
  have hJ : DifferentiableAt ℝ (jacXV F) q0 :=
    ((hF.fderiv_right (m := 1) (by norm_num)).clm_comp contDiffAt_const).differentiableAt
      (by norm_num)
  have hl := hJ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_lineV q0 v) (by simp)
  have h2 := (ContinuousLinearMap.apply ℝ (X → ℝ) (Pi.single j 1)).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hl
  have h3 := hasDerivAt_pi.1 h2 i
  simpa [matXV, LinearMap.toMatrix'_apply, Function.comp_def] using h3

/-- `D_x(∂ₓF)(q₀) y` from the entries of `∂ₓF` along `x₀ + t y`. -/
@[tmio T, powerlib_foundation] theorem smDxV_of_line {F : (X → ℝ) × (U → ℝ) → X → ℝ}
    {q0 : (X → ℝ) × (U → ℝ)} (hF : ContDiffAt ℝ 2 F q0) (y : X → ℝ) {Jr : ℝ → Matrix X X ℝ}
    (hJr : ∀ᶠ t in 𝓝 (0 : ℝ), matXV F (q0.1 + t • y, q0.2) = Jr t)
    {M : Matrix X X ℝ} (hM : ∀ i j, HasDerivAt (fun t => Jr t i j) (M i j) 0) :
    smDxV F q0 y = M := by
  ext i j
  have h := hasDerivAt_matXV_line hF ((y, (0 : U → ℝ)) : (X → ℝ) × (U → ℝ)) i j
  have e : ∀ t : ℝ, q0 + t • ((y, (0 : U → ℝ)) : (X → ℝ) × (U → ℝ)) = (q0.1 + t • y, q0.2) :=
    fun t => by ext <;> simp
  simp only [e] at h
  have h2 : HasDerivAt (fun t => Jr t i j) _ 0 := h.congr_of_eventuallyEq
    (hJr.mono fun t ht => by show Jr t i j = _; rw [← ht])
  exact h2.unique (hM i j)

/-- `D_w(∂ₓF)(q₀) a` from the entries of `∂ₓF` along `w₀ + t a`. -/
@[tmio T, powerlib_foundation] theorem smMwV_of_line {F : (X → ℝ) × (U → ℝ) → X → ℝ}
    {q0 : (X → ℝ) × (U → ℝ)} (hF : ContDiffAt ℝ 2 F q0) (a : U → ℝ) {Jr : ℝ → Matrix X X ℝ}
    (hJr : ∀ᶠ t in 𝓝 (0 : ℝ), matXV F (q0.1, q0.2 + t • a) = Jr t)
    {M : Matrix X X ℝ} (hM : ∀ i j, HasDerivAt (fun t => Jr t i j) (M i j) 0) :
    smMwV F q0 a = M := by
  ext i j
  have h := hasDerivAt_matXV_line hF (((0 : X → ℝ), a) : (X → ℝ) × (U → ℝ)) i j
  have e : ∀ t : ℝ, q0 + t • (((0 : X → ℝ), a) : (X → ℝ) × (U → ℝ)) = (q0.1, q0.2 + t • a) :=
    fun t => by ext <;> simp
  simp only [e] at h
  have h2 : HasDerivAt (fun t => Jr t i j) _ 0 := h.congr_of_eventuallyEq
    (hJr.mono fun t ht => by show Jr t i j = _; rw [← ht])
  exact h2.unique (hM i j)

/-! ### Fields invariant under a joint shift of a state and an input (the grid angle)

For a converter synchronized to the grid, rotating the grid angle and every angle state by the
same amount leaves the field unchanged: `F(x + s e, w + s u) = F(x, w)`. Then the angle input
enters only through the relative coordinates `z − θ̂ e`: `∂_wF u = −A₀ e`,
`D_w(∂ₓF) u = −D_x(∂ₓF) e`, the angle part of the source acts on the relative response as the
rate input `−jωθ̂ e`, and only the relative response enters `A₁`. -/

omit [DecidableEq X] in
/-- Under the joint shift invariance the derivative along `(e, u)` vanishes. -/
@[tmio T, powerlib_foundation] theorem fderiv_shift_eq_zero {F : (X → ℝ) × (U → ℝ) → X → ℝ}
    {e : X → ℝ} {u : U → ℝ} (hinv : ∀ (q : (X → ℝ) × (U → ℝ)) (s : ℝ), F (q + s • (e, u)) = F q)
    {q : (X → ℝ) × (U → ℝ)} (hF : DifferentiableAt ℝ F q) : fderiv ℝ F q (e, u) = 0 := by
  have hl := hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_lineV q (e, u)) (by simp)
  have hc : HasDerivAt (fun s : ℝ => F (q + s • (e, u))) 0 0 := by
    have h : (fun s : ℝ => F (q + s • (e, u))) = fun _ => F q := funext fun s => hinv q s
    rw [h]; exact hasDerivAt_const _ _
  exact hl.unique hc

/-- `∂_wF(q) u = −∂ₓF(q) e`. -/
@[tmio T, powerlib_foundation] theorem fderivW_shift {F : (X → ℝ) × (U → ℝ) → X → ℝ}
    {e : X → ℝ} {u : U → ℝ} (hinv : ∀ (q : (X → ℝ) × (U → ℝ)) (s : ℝ), F (q + s • (e, u)) = F q)
    {q : (X → ℝ) × (U → ℝ)} (hF : DifferentiableAt ℝ F q) :
    fderiv ℝ F q (0, u) = -(matXV F q *ᵥ e) := by
  have h0 := fderiv_shift_eq_zero hinv hF
  have hsplit : ((e, u) : (X → ℝ) × (U → ℝ)) = (e, 0) + (0, u) := by ext <;> simp
  rw [hsplit, map_add] at h0
  rw [matXV_mulVec]
  exact eq_neg_of_add_eq_zero_right h0

omit [DecidableEq X] in
/-- The partial Jacobian is invariant under the joint shift. -/
@[tmio T, powerlib_foundation] theorem jacXV_shift {F : (X → ℝ) × (U → ℝ) → X → ℝ}
    {e : X → ℝ} {u : U → ℝ} (hinv : ∀ (q : (X → ℝ) × (U → ℝ)) (s : ℝ), F (q + s • (e, u)) = F q)
    (q : (X → ℝ) × (U → ℝ)) (s : ℝ) : jacXV F (q + s • (e, u)) = jacXV F q := by
  have hF' : F = fun q => F (q + s • (e, u)) := funext fun q => (hinv q s).symm
  have h : fderiv ℝ F q = fderiv ℝ F (q + s • (e, u)) := by
    calc fderiv ℝ F q = fderiv ℝ (fun q => F (q + s • (e, u))) q :=
          congrArg (fun G => fderiv ℝ G q) hF'
      _ = fderiv ℝ F (q + s • (e, u)) := by rw [fderiv_comp_add_right]
  simp only [jacXV, h]

/-- `D_w(∂ₓF)(q₀) u = −D_x(∂ₓF)(q₀) e`. -/
@[tmio T, powerlib_foundation] theorem smMwV_shift {F : (X → ℝ) × (U → ℝ) → X → ℝ}
    {e : X → ℝ} {u : U → ℝ} (hinv : ∀ (q : (X → ℝ) × (U → ℝ)) (s : ℝ), F (q + s • (e, u)) = F q)
    {q0 : (X → ℝ) × (U → ℝ)} (hF : ContDiffAt ℝ 2 F q0) : smMwV F q0 u = -smDxV F q0 e := by
  have hJ : DifferentiableAt ℝ (jacXV F) q0 :=
    ((hF.fderiv_right (m := 1) (by norm_num)).clm_comp contDiffAt_const).differentiableAt
      (by norm_num)
  have hl := hJ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_lineV q0 (e, u)) (by simp)
  have hc : HasDerivAt (fun s : ℝ => jacXV F (q0 + s • (e, u))) 0 0 := by
    have h : (fun s : ℝ => jacXV F (q0 + s • (e, u))) = fun _ => jacXV F q0 :=
      funext fun s => jacXV_shift hinv q0 s
    rw [h]; exact hasDerivAt_const _ _
  have h0 : fderiv ℝ (jacXV F) q0 (e, u) = 0 := hl.unique hc
  have hsplit : ((e, u) : (X → ℝ) × (U → ℝ)) = (e, 0) + (0, u) := by ext <;> simp
  rw [hsplit, map_add] at h0
  have h1 : fderiv ℝ (jacXV F) q0 (0, u) = -fderiv ℝ (jacXV F) q0 (e, 0) :=
    eq_neg_of_add_eq_zero_right h0
  ext i j
  simp [smMwV, smDxV, h1]

/-- The source `ŵ + θ̂ u` (an angle component `θ̂ ∈ ℂ` along `u`) has the input direction
`∂_wF ŵ − θ̂ A₀ e`. -/
@[tmio T, powerlib_foundation] theorem fderivWC_shift {F : (X → ℝ) × (U → ℝ) → X → ℝ}
    {e : X → ℝ} {u : U → ℝ} (hinv : ∀ (q : (X → ℝ) × (U → ℝ)) (s : ℝ), F (q + s • (e, u)) = F q)
    {q0 : (X → ℝ) × (U → ℝ)} (hF : DifferentiableAt ℝ F q0) (w : U → ℂ) (θ : ℂ) :
    fderivWC F q0 (w + θ • ofv u) = fderivWC F q0 w - θ • ofv (matXV F q0 *ᵥ e) := by
  have hB := fderivW_shift hinv hF
  have hre : (fun k => ((w + θ • ofv u) k).re) = (fun k => (w k).re) + θ.re • u := by
    funext k; simp [ofv]
  have him : (fun k => ((w + θ • ofv u) k).im) = (fun k => (w k).im) + θ.im • u := by
    funext k; simp [ofv]
  have e1 : ∀ a : U → ℝ, ∀ c : ℝ, (((0 : X → ℝ), a + c • u) : (X → ℝ) × (U → ℝ)) =
      ((0 : X → ℝ), a) + c • ((0 : X → ℝ), u) := fun a c => by ext <;> simp
  funext i
  simp only [fderivWC, hre, him, e1, map_add, map_smul, hB]
  apply Complex.ext <;> simp [ofv, fderivWC] <;> ring

/-- The forced response to `ŵ + θ̂ u` in relative coordinates: `(jωI − A₀) z = ∂_wF(ŵ + θ̂u)` iff
`(jωI − A₀)(z − θ̂ e) = ∂_wF ŵ − jωθ̂ e`. -/
@[tmio T, powerlib_foundation] theorem forced_shift {F : (X → ℝ) × (U → ℝ) → X → ℝ}
    {e : X → ℝ} {u : U → ℝ} (hinv : ∀ (q : (X → ℝ) × (U → ℝ)) (s : ℝ), F (q + s • (e, u)) = F q)
    {q0 : (X → ℝ) × (U → ℝ)} (hF : DifferentiableAt ℝ F q0) (w : U → ℂ) (θ : ℂ) (ω : ℝ)
    (z : X → ℂ) :
    ((ω : ℂ) * I) • z - (matXV F q0).map (algebraMap ℝ ℂ) *ᵥ z = fderivWC F q0 (w + θ • ofv u) ↔
      ((ω : ℂ) * I) • (z - θ • ofv e) - (matXV F q0).map (algebraMap ℝ ℂ) *ᵥ (z - θ • ofv e) =
        fderivWC F q0 w - (((ω : ℂ) * I) * θ) • ofv e := by
  rw [fderivWC_shift hinv hF, Matrix.mulVec_sub, Matrix.mulVec_smul, map_ofReal_mulVec_ofv,
    smul_sub, smul_smul]
  constructor <;> intro h
  · rw [← sub_eq_zero] at h ⊢
    rw [← h]; abel
  · rw [← sub_eq_zero] at h ⊢
    rw [← h]; abel

/-- Only the relative response enters `A₁`: `A₁(ŵ + θ̂u, z) = A₁(ŵ, z − θ̂ e)`. -/
@[tmio T, powerlib_foundation] theorem smA1V_shift {F : (X → ℝ) × (U → ℝ) → X → ℝ}
    {e : X → ℝ} {u : U → ℝ} (hinv : ∀ (q : (X → ℝ) × (U → ℝ)) (s : ℝ), F (q + s • (e, u)) = F q)
    {q0 : (X → ℝ) × (U → ℝ)} (hF : ContDiffAt ℝ 2 F q0) (w : U → ℂ) (θ : ℂ) (z : X → ℂ) :
    smA1V F q0 (w + θ • ofv u) z = smA1V F q0 w (z - θ • ofv e) := by
  have hM := smMwV_shift hinv hF
  have hre : (fun k => ((w + θ • ofv u) k).re) = (fun k => (w k).re) + θ.re • u := by
    funext k; simp [ofv]
  have him : (fun k => ((w + θ • ofv u) k).im) = (fun k => (w k).im) + θ.im • u := by
    funext k; simp [ofv]
  have hzre : (fun k => ((z - θ • ofv e) k).re) = (fun k => (z k).re) - θ.re • e := by
    funext k; simp [ofv]
  have hzim : (fun k => ((z - θ • ofv e) k).im) = (fun k => (z k).im) - θ.im • e := by
    funext k; simp [ofv]
  ext i j
  simp only [smA1V, DxC, linC, Matrix.add_apply, hre, him, hzre, hzim, map_add, map_sub,
    map_smul, hM]
  apply Complex.ext <;> simp <;> ring

omit [Fintype X] [DecidableEq X] [Fintype U] in
/-- `∂_wF (c a) = c ∂_wF a` for a real direction `a` and a complex amplitude `c`. -/
@[tmio T, powerlib_foundation] theorem fderivWC_smul_ofv (F : (X → ℝ) × (U → ℝ) → X → ℝ)
    (q0 : (X → ℝ) × (U → ℝ)) (c : ℂ) (a : U → ℝ) :
    fderivWC F q0 (c • ofv a) = c • ofv (fderiv ℝ F q0 (0, a)) := by
  have hre : (fun k => ((c • ofv a) k).re) = c.re • a := by funext k; simp [ofv]
  have him : (fun k => ((c • ofv a) k).im) = c.im • a := by funext k; simp [ofv]
  have e1 : ∀ r : ℝ, (((0 : X → ℝ), r • a) : (X → ℝ) × (U → ℝ)) = r • ((0 : X → ℝ), a) :=
    fun r => by ext <;> simp
  funext i
  simp only [fderivWC, hre, him, e1, map_smul]
  apply Complex.ext <;> simp [ofv]

omit [Fintype X] [DecidableEq X] [Fintype U] in
/-- `linC M (c a) = c M a` for a real direction `a`. -/
@[tmio T, powerlib_foundation] theorem linC_smul_ofv (M : (U → ℝ) →ₗ[ℝ] Matrix X X ℝ) (c : ℂ)
    (a : U → ℝ) : linC M (c • ofv a) = c • (M a).map (algebraMap ℝ ℂ) := by
  have hre : (fun k => ((c • ofv a) k).re) = c.re • a := by funext k; simp [ofv]
  have him : (fun k => ((c • ofv a) k).im) = c.im • a := by funext k; simp [ofv]
  ext i j
  simp only [linC, hre, him, map_smul]
  apply Complex.ext <;> simp

/-! ### Transfer from a scalar-input field -/

/-- If the Jacobians of `F` and of a scalar-input field `G` agree along `x₀ + t y`, so do their
second derivatives along `y`. -/
@[tmio T, powerlib_foundation] theorem smDxV_eq_smDx {F : (X → ℝ) × (U → ℝ) → X → ℝ}
    {G : (X → ℝ) × ℝ → X → ℝ} {q0 : (X → ℝ) × (U → ℝ)} {g0 : (X → ℝ) × ℝ}
    (hF : ContDiffAt ℝ 2 F q0) (hG : ContDiffAt ℝ 2 G g0) (y : X → ℝ)
    (hJ : ∀ᶠ t in 𝓝 (0 : ℝ), matXV F (q0.1 + t • y, q0.2) = matX G (g0.1 + t • y, g0.2)) :
    smDxV F q0 y = smDx G g0 y := by
  refine smDxV_of_line hF y (Jr := fun t => matX G (g0.1 + t • y, g0.2)) hJ fun i j => ?_
  have h := hasDerivAt_matX_line hG (y, 0) i j
  have e : ∀ t : ℝ, g0 + t • ((y, (0 : ℝ)) : (X → ℝ) × ℝ) = (g0.1 + t • y, g0.2) := fun t => by
    ext <;> simp
  simp only [e] at h
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  simpa [Function.comp_def, smDx] using h2

/-- If the Jacobians of `F` along `w₀ + t a` and of a scalar-input field `G` along `w₀ + t` agree,
then `D_w(∂ₓF) a = D_w(∂ₓG)`. -/
@[tmio T, powerlib_foundation] theorem smMwV_eq_smM1 {F : (X → ℝ) × (U → ℝ) → X → ℝ}
    {G : (X → ℝ) × ℝ → X → ℝ} {q0 : (X → ℝ) × (U → ℝ)} {g0 : (X → ℝ) × ℝ}
    (hF : ContDiffAt ℝ 2 F q0) (hG : ContDiffAt ℝ 2 G g0) (a : U → ℝ)
    (hJ : ∀ᶠ t in 𝓝 (0 : ℝ), matXV F (q0.1, q0.2 + t • a) = matX G (g0.1, g0.2 + t)) :
    smMwV F q0 a = smM1 G g0 := by
  refine smMwV_of_line hF a (Jr := fun t => matX G (g0.1, g0.2 + t)) hJ fun i j => ?_
  have h := hasDerivAt_matX_line hG ((0 : X → ℝ), (1 : ℝ)) i j
  have e : ∀ t : ℝ, g0 + t • (((0 : X → ℝ), (1 : ℝ)) : (X → ℝ) × ℝ) = (g0.1, g0.2 + t) :=
    fun t => by ext <;> simp
  simp only [e] at h
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  simpa [Function.comp_def, smM1] using h2

end Vec

/-! ### The grid phasor source

A grid source has two channels, the magnitude and the angle. The source `(v̂, θ̂)` drives
`w₀ + ε (Re{v̂ e^{jωt}}, Re{θ̂ e^{jωt}})`. For a grid-synchronized converter (`F` invariant under
the joint rotation of its angle state `e` and the grid angle) the general form is
* `(jωI − A₀) z_rel = v̂ b_V − jωθ̂ e` for the relative response `z_rel = z − θ̂ e`;
* `A₁ = D_x(∂ₓF) z_rel + v̂ D_V(∂ₓF)`.
-/

/-- The magnitude channel `(1, 0)`. -/
def uMag : Fin 2 → ℝ := ![1, 0]
/-- The angle channel `(0, 1)`. -/
def uAng : Fin 2 → ℝ := ![0, 1]
/-- The grid source with magnitude amplitude `v̂` and angle amplitude `θ̂`. -/
def gridSrc (v θ : ℂ) : Fin 2 → ℂ := v • ofv uMag + θ • ofv uAng

@[tmio T, powerlib_foundation] theorem harm_gridSrc (v θ : ℂ) (ω t : ℝ) :
    harm (gridSrc v θ) ω t =
      ![v.re * Real.cos (ω * t) - v.im * Real.sin (ω * t),
        θ.re * Real.cos (ω * t) - θ.im * Real.sin (ω * t)] := by
  funext k; fin_cases k <;> simp [harm, gridSrc, ofv, uMag, uAng]

section Grid

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The general source form, forced response: `(jωI − A₀) z = ∂_wF(v̂, θ̂)` iff the relative
response `z − θ̂ e` solves `(jωI − A₀)(z − θ̂ e) = v̂ b_V − jωθ̂ e`. -/
@[tmio T, powerlib_foundation] theorem forced_gridSrc {F : (X → ℝ) × (Fin 2 → ℝ) → X → ℝ}
    {e : X → ℝ}
    (hinv : ∀ (q : (X → ℝ) × (Fin 2 → ℝ)) (s : ℝ), F (q + s • (e, uAng)) = F q)
    {q0 : (X → ℝ) × (Fin 2 → ℝ)} (hF : DifferentiableAt ℝ F q0) (v θ : ℂ) (ω : ℝ)
    (z : X → ℂ) :
    ((ω : ℂ) * I) • z - (matXV F q0).map (algebraMap ℝ ℂ) *ᵥ z = fderivWC F q0 (gridSrc v θ) ↔
      ((ω : ℂ) * I) • (z - θ • ofv e) - (matXV F q0).map (algebraMap ℝ ℂ) *ᵥ (z - θ • ofv e) =
        v • ofv (fderiv ℝ F q0 (0, uMag)) - (((ω : ℂ) * I) * θ) • ofv e := by
  rw [gridSrc, forced_shift hinv hF, fderivWC_smul_ofv]

/-- The general source form, modulation: `A₁(v̂, θ̂; z) = D_x(∂ₓF)(z − θ̂ e) + v̂ D_V(∂ₓF)`. -/
@[tmio T, powerlib_foundation] theorem smA1V_gridSrc {F : (X → ℝ) × (Fin 2 → ℝ) → X → ℝ}
    {e : X → ℝ}
    (hinv : ∀ (q : (X → ℝ) × (Fin 2 → ℝ)) (s : ℝ), F (q + s • (e, uAng)) = F q)
    {q0 : (X → ℝ) × (Fin 2 → ℝ)} (hF : ContDiffAt ℝ 2 F q0) (v θ : ℂ) (z : X → ℂ) :
    smA1V F q0 (gridSrc v θ) (z + θ • ofv e) =
      DxC (smDxV F q0) z + v • (smMwV F q0 uMag).map (algebraMap ℝ ℂ) := by
  rw [gridSrc, smA1V_shift hinv hF, add_sub_cancel_right, smA1V, linC_smul_ofv]

end Grid

section Three

variable {U : Type*} [Fintype U]

/-- Three-state `C³` fields with a phasor input, end-to-end stability (eigen-data of `∂ₓF(q₀)`:
pair `±jΩ`, real pole `λ₃ < 0`; drive at `2Ω`). -/
@[tmio T, powerlib_foundation] theorem smooth_orbit_floquet_three_stable_vec
    {F : (Fin 3 → ℝ) × (U → ℝ) → Fin 3 → ℝ} {q0 : (Fin 3 → ℝ) × (U → ℝ)}
    (hF : ContDiffAt ℝ 3 F q0) (hF0 : F q0 = 0) {w : U → ℂ} {Ω : ℝ} (hΩ : 0 < Ω)
    {l3 : ℝ} (hl3 : l3 < 0) {r u : Fin 3 → ℂ} {r3 u3 : Fin 3 → ℝ}
    (hr : (matXV F q0).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (matXV F q0).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : matXV F q0 *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* matXV F q0 = l3 • u3) (hur3 : u3 ⬝ᵥ r3 = 1)
    {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matXV F q0).map (algebraMap ℝ ℂ) *ᵥ z = fderivWC F q0 w)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ (smA1V F q0 w z *ᵥ star r) / 2‖ ^ 2 <
      ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε • harm w (2 * Ω) t) +
            ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε • harm w (2 * Ω) t) +
            ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 3 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => smJV F q0 w (2 * Ω) A0' ε t (y t))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  obtain ⟨hQP, hPQ, hQAP, hLu, hRr⟩ := modal_three hΩ.ne' hr hu hur hr3 hu3 hur3
  have hω : 0 < 2 * Ω := by linarith
  have hA0 : modalQ u u3 * matXV F q0 * modalP r r3 =
      fromBlocks (base 0 (2 * Ω / 2)) 0 0 !![l3] := by
    rw [hQAP, mul_div_cancel_left₀ _ two_ne_zero]
  have hq : ‖expS (!![l3] : Matrix (Fin 1) (Fin 1) ℝ) (2 * Real.pi / (2 * Ω))‖ < 1 := by
    rw [norm_expS_one, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (by positivity) hl3
  exact smooth_orbit_floquet_stable_vec hF hF0 hω hPQ hQP _ hA0
    (BlockAveraging.spectralRadius_lt_one_of_norm _ hq) hz A0'
    (by rw [hLu, hRr]; exact hs) (by rw [hLu, hRr]; exact hg)

/-- Three-state `C³` fields with a phasor input, end-to-end parametric instability. -/
@[tmio T, powerlib_foundation] theorem smooth_orbit_floquet_three_unstable_vec
    {F : (Fin 3 → ℝ) × (U → ℝ) → Fin 3 → ℝ} {q0 : (Fin 3 → ℝ) × (U → ℝ)}
    (hF : ContDiffAt ℝ 3 F q0) (hF0 : F q0 = 0) {w : U → ℂ} {Ω : ℝ} (hΩ : 0 < Ω)
    {l3 : ℝ} (hl3 : l3 < 0) {r u : Fin 3 → ℂ} {r3 u3 : Fin 3 → ℝ}
    (hr : (matXV F q0).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (matXV F q0).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : matXV F q0 *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* matXV F q0 = l3 • u3) (hur3 : u3 ⬝ᵥ r3 = 1)
    {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matXV F q0).map (algebraMap ℝ ℂ) *ᵥ z = fderivWC F q0 w)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2 <
      ‖u ⬝ᵥ (smA1V F q0 w z *ᵥ star r) / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
        (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε • harm w (2 * Ω) t) +
            ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) →
        (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε • harm w (2 * Ω) t) +
            ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJV F q0 w (2 * Ω) A0' ε t (y t))
          (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨hQP, hPQ, hQAP, hLu, hRr⟩ := modal_three hΩ.ne' hr hu hur hr3 hu3 hur3
  have hω : 0 < 2 * Ω := by linarith
  have hA0 : modalQ u u3 * matXV F q0 * modalP r r3 =
      fromBlocks (base 0 (2 * Ω / 2)) 0 0 !![l3] := by
    rw [hQAP, mul_div_cancel_left₀ _ two_ne_zero]
  have hq : ‖expS (!![l3] : Matrix (Fin 1) (Fin 1) ℝ) (2 * Real.pi / (2 * Ω))‖ < 1 := by
    rw [norm_expS_one, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (by positivity) hl3
  exact smooth_orbit_floquet_unstable_vec hF hF0 hω hPQ hQP _ hA0
    (BlockAveraging.spectralRadius_lt_one_of_norm _ hq) hz A0' (by rw [hLu, hRr]; exact hg)

/-- Three-state `C³` fields with a phasor input, end-to-end with orbital stability: in the stable
case the forced orbit is locally exponentially stable. -/
@[tmio T, powerlib_foundation] theorem smooth_orbit_exp_three_stable_vec
    {F : (Fin 3 → ℝ) × (U → ℝ) → Fin 3 → ℝ} {q0 : (Fin 3 → ℝ) × (U → ℝ)}
    (hF : ContDiffAt ℝ 3 F q0) (hF0 : F q0 = 0) {w : U → ℂ} {Ω : ℝ} (hΩ : 0 < Ω)
    {l3 : ℝ} (hl3 : l3 < 0) {r u : Fin 3 → ℂ} {r3 u3 : Fin 3 → ℝ}
    (hr : (matXV F q0).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (matXV F q0).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : matXV F q0 *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* matXV F q0 = l3 • u3) (hur3 : u3 ⬝ᵥ r3 = 1)
    {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matXV F q0).map (algebraMap ℝ ℂ) *ᵥ z = fderivWC F q0 w)
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ (smA1V F q0 w z *ᵥ star r) / 2‖ ^ 2 <
      ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ,
      (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
      (∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε • harm w (2 * Ω) t) + ε • (A0' *ᵥ y t)) t) ∧
      ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → Fin 3 → ℝ),
        IsIntegralCurveOn x (fun t v => F (q0.1 + v, q0.2 + ε • harm w (2 * Ω) t) +
          ε • (A0' *ᵥ v)) (Ici s) →
        ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
          ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖ := by
  obtain ⟨hQP, hPQ, hQAP, hLu, hRr⟩ := modal_three hΩ.ne' hr hu hur hr3 hu3 hur3
  have hω : 0 < 2 * Ω := by linarith
  have hA0 : modalQ u u3 * matXV F q0 * modalP r r3 =
      fromBlocks (base 0 (2 * Ω / 2)) 0 0 !![l3] := by
    rw [hQAP, mul_div_cancel_left₀ _ two_ne_zero]
  have hq : ‖expS (!![l3] : Matrix (Fin 1) (Fin 1) ℝ) (2 * Real.pi / (2 * Ω))‖ < 1 := by
    rw [norm_expS_one, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (by positivity) hl3
  exact smooth_orbit_exp_stable_vec hF hF0 hω hPQ hQP _ hA0
    (BlockAveraging.spectralRadius_lt_one_of_norm _ hq) hz A0'
    (by rw [hLu, hRr]; exact hs) (by rw [hLu, hRr]; exact hg)

end Three

end powerlib.ParametricResonance.ForcedOrbit
