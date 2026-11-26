import theorem.ParametricResonance.ForcedOrbitFloquet

/-! # The forced orbit and its Floquet multipliers for a smooth vector field with a modulated input

`ForcedOrbitFloquet` takes the forced system `ẏ = A y + ε b(t) + N_ε(t, y)` and the Jacobian
`J_ε(t, y)` with explicit estimates. This file derives all of them from a single hypothesis: the
vector field `F(x, w)` is `C³` at an equilibrium `F(x₀, w₀) = 0`, the input is
`w = w₀ + ε V̂ cos ωt`, and the state matrix is perturbed by `ε A₀'`. Then `A = ∂ₓF(q₀)`,
`b = V̂ cos(ωt) ∂_wF(q₀)`, `D_x = D_x(∂ₓF)(q₀)`, `D_u = A₀' + V̂ cos(ωt) D_w(∂ₓF)(q₀)`, and the
first-order criterion `|g/2| ≶ |λ₁|` with `A₁ = D_x z + V̂ D_w(∂ₓF)(q₀)` (`z` the first-order
forced response) decides the Floquet multipliers of the variational equation of the actual forced
orbit. The derivatives of a concrete model are identified from directional derivatives along lines
(real or complexified), and real modal coordinates are built from the critical eigenvectors and a
basis of the stable subspace.

Model boundary.
* `F : ℝ^X × ℝ → ℝ^X` (finite `X`, sup norms), `ContDiffAt ℝ 3 F q₀`, `F q₀ = 0`; scalar input;
  drive `w₀ + ε V̂ cos ωt`; state perturbation `ε A₀'` with a constant real `A₀'`.
* The Floquet statements need real modal coordinates of `∂ₓF(q₀)` with the pair `±jω/2` and a
  stable block `A_s` with one-period spectral radius `ρ(e^{TA_s}) < 1` (`T = 2π/ω`), or the
  eigen-data of a three-state core with a real pole `λ₃ < 0`. The spectral condition does not
  depend on the basis of the stable subspace; `StableBasis` constructs the basis from the critical
  eigenvectors.
* The exponential stability of the nonlinear solutions near the orbit is derived from the
  multipliers in `SmoothOrbitStability`; parameter changes `p → p + εp₁` and limiters inactive at
  the operating point are covered by `FieldTransfer`.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1–§2.2 (`J_p = A₀ + ε Re{A₁ e^{jω_p t}}` along the forced
trajectory, `g_m = l_mᴴ A₁ r_m*`, first-order averaging).

Results.
* `taylor_sub`, `exists_taylor_ball` — first-order Taylor bounds from a locally Lipschitz
  derivative (`C²` maps).
* `jacX`, `matX`, `matX_mulVec`, `smDx`, `smM1`, `smB`, `smN`, `smJ`, `smDu`, `smN_rhs` — the forced
  system of a smooth field; `smooth_estimates` — every estimate of `forced_orbit` and
  `orbit_variational` (`ContinuousOn` on `ℝ × {‖y‖ ≤ ρ}`, Lipschitz and Taylor bounds);
  `smA1`, `smooth_link` — the harmonic data.
* `smooth_orbit_floquet_stable`, `smooth_orbit_floquet_unstable` — end-to-end for a `C³` field with
  general modal coordinates; `smooth_orbit_floquet_three_stable`,
  `smooth_orbit_floquet_three_unstable` — for three-state fields from their eigen-data.
* `real_right_eig_gen`, `real_left_eig_gen`, `basisP`, `basisQ`, `modal_of_basis` — modal
  coordinates from `r`, `u` (`u r = 1`) and a basis `W` of an invariant complement with left
  inverse `W'` annihilating the pair (`A W = W A_s`, `W' W = I`, `u W = 0`, `W' r = 0`).
* `ofv`, `matX_of_lift`, `fderivW_of_lift`, `hasDerivAt_matX_line`, `smDx_of_lift`,
  `smM1_of_lift`, `DxC_of_lift`, `hasDerivAt_conj_entries`, `hasDerivAt_mulVec_c` — the derivatives
  from complexified directional derivatives (eventually along the line for the second
  derivatives); `matX_of_line`, `fderivW_of_line`, `smDx_of_line`, `smM1_of_line` — the real
  versions.

Corrections.
None: an extension (the first-order criterion for the actual forced orbit of a smooth model).

Family and connection conclusions.
None: static evidence on smooth periodically forced ODEs (forced orbit, Floquet multipliers).
-/

noncomputable section
namespace powerlib.ParametricResonance.ForcedOrbit
open Complex Matrix Set Filter Topology Metric
open scoped Matrix.Norms.Operator
open TwoToOne (base)
open BlockAveraging (expS modX physLeft physRight modalP modalQ modal_three norm_expS_one)

/-! ### Taylor estimates from a locally Lipschitz derivative -/

section Taylor

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

/-- `‖G q₁ − G q₂ − G'(q₀)(q₁ − q₂)‖ ≤ L m ‖q₁ − q₂‖` on the ball of radius `m` when
`‖G'(q) − G'(q₀)‖ ≤ L ‖q − q₀‖`. -/
@[tmio T, powerlib_foundation] theorem taylor_sub {G : P → V} {q0 : P} {r L : ℝ} (hL0 : 0 ≤ L)
    (hd : ∀ q ∈ closedBall q0 r, HasFDerivAt G (fderiv ℝ G q) q)
    (hL : ∀ q ∈ closedBall q0 r, ‖fderiv ℝ G q - fderiv ℝ G q0‖ ≤ L * ‖q - q0‖)
    {m : ℝ} (hm : m ≤ r) {q1 q2 : P} (h1 : q1 ∈ closedBall q0 m) (h2 : q2 ∈ closedBall q0 m) :
    ‖G q1 - G q2 - fderiv ℝ G q0 (q1 - q2)‖ ≤ L * m * ‖q1 - q2‖ := by
  have hH : ∀ q ∈ closedBall q0 m, HasFDerivWithinAt (fun q => G q - fderiv ℝ G q0 q)
      (fderiv ℝ G q - fderiv ℝ G q0) (closedBall q0 m) q := fun q hq =>
    ((hd q (closedBall_subset_closedBall hm hq)).sub (fderiv ℝ G q0).hasFDerivAt).hasFDerivWithinAt
  have hb : ∀ q ∈ closedBall q0 m, ‖fderiv ℝ G q - fderiv ℝ G q0‖ ≤ L * m := fun q hq =>
    (hL q (closedBall_subset_closedBall hm hq)).trans
      (mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.1 hq) hL0)
  have h := (convex_closedBall q0 m).norm_image_sub_le_of_norm_hasFDerivWithin_le hH hb h2 h1
  rw [show G q1 - fderiv ℝ G q0 q1 - (G q2 - fderiv ℝ G q0 q2) =
    G q1 - G q2 - fderiv ℝ G q0 (q1 - q2) by rw [map_sub]; abel] at h
  exact h

/-- A `C²` map has, on a small ball, a derivative with `‖G'(q) − G'(q₀)‖ ≤ L ‖q − q₀‖`. -/
@[tmio T, powerlib_foundation] theorem exists_taylor_ball {G : P → V} {q0 : P}
    (hG : ContDiffAt ℝ 2 G q0) :
    ∃ r L, 0 < r ∧ 0 ≤ L ∧ (∀ q ∈ closedBall q0 r, HasFDerivAt G (fderiv ℝ G q) q) ∧
      ∀ q ∈ closedBall q0 r, ‖fderiv ℝ G q - fderiv ℝ G q0‖ ≤ L * ‖q - q0‖ := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ G) q0 := hG.fderiv_right (m := 1) (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := h1.exists_lipschitzOnWith
  have h2 : ∀ᶠ q in 𝓝 q0, ContDiffAt ℝ 2 G q := hG.eventually (by simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem ht h2)
  have hsub : closedBall q0 (δ / 2) ⊆ ball q0 δ := closedBall_subset_ball (by linarith)
  refine ⟨δ / 2, K, by positivity, K.2, fun q hq => ?_, fun q hq => ?_⟩
  · have hc : ContDiffAt ℝ 2 G q := (hball (hsub hq)).2
    exact (hc.differentiableAt (by norm_num)).hasFDerivAt
  · have := hK.dist_le_mul q (hball (hsub hq)).1 q0 (mem_of_mem_nhds ht)
    rwa [dist_eq_norm, dist_eq_norm] at this

end Taylor

/-! ### The smooth forced system -/

section Smooth

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The partial Jacobian `∂ₓF(q)` of `F : ℝ^X × ℝ → ℝ^X`. -/
def jacX (F : (X → ℝ) × ℝ → X → ℝ) (q : (X → ℝ) × ℝ) : (X → ℝ) →L[ℝ] (X → ℝ) :=
  (fderiv ℝ F q).comp (ContinuousLinearMap.inl ℝ (X → ℝ) ℝ)

/-- Its matrix. -/
def matX (F : (X → ℝ) × ℝ → X → ℝ) (q : (X → ℝ) × ℝ) : Matrix X X ℝ :=
  LinearMap.toMatrix' (jacX F q : (X → ℝ) →ₗ[ℝ] (X → ℝ))

@[tmio T, powerlib_foundation] theorem matX_mulVec (F : (X → ℝ) × ℝ → X → ℝ)
    (q : (X → ℝ) × ℝ) (v : X → ℝ) : matX F q *ᵥ v = fderiv ℝ F q (v, 0) := by
  rw [matX, LinearMap.toMatrix'_mulVec]; rfl

/-- The second derivative `D_x(∂ₓF)(q₀) y` as a linear map into matrices. -/
def smDx (F : (X → ℝ) × ℝ → X → ℝ) (q0 : (X → ℝ) × ℝ) : (X → ℝ) →ₗ[ℝ] Matrix X X ℝ where
  toFun y := LinearMap.toMatrix'
    ((fderiv ℝ (jacX F) q0 (y, 0) : (X → ℝ) →L[ℝ] (X → ℝ)) : (X → ℝ) →ₗ[ℝ] (X → ℝ))
  map_add' y z := by
    rw [show ((y + z, (0 : ℝ)) : (X → ℝ) × ℝ) = (y, 0) + (z, 0) by simp, map_add,
      ContinuousLinearMap.toLinearMap_add, map_add]
  map_smul' c y := by
    rw [show ((c • y, (0 : ℝ)) : (X → ℝ) × ℝ) = c • (y, 0) by simp, map_smul,
      ContinuousLinearMap.toLinearMap_smul, map_smul]; rfl

/-- The mixed second derivative `D_w(∂ₓF)(q₀)` as a matrix. -/
def smM1 (F : (X → ℝ) × ℝ → X → ℝ) (q0 : (X → ℝ) × ℝ) : Matrix X X ℝ :=
  LinearMap.toMatrix'
    ((fderiv ℝ (jacX F) q0 (0, 1) : (X → ℝ) →L[ℝ] (X → ℝ)) : (X → ℝ) →ₗ[ℝ] (X → ℝ))

/-- The forcing `b(t) = V̂ cos(ωt) ∂_wF(q₀)`. -/
def smB (F : (X → ℝ) × ℝ → X → ℝ) (q0 : (X → ℝ) × ℝ) (Vh ω t : ℝ) : X → ℝ :=
  (Vh * Real.cos (ω * t)) • fderiv ℝ F q0 (0, 1)

/-- The nonlinear remainder of `y ↦ F(x₀ + y, w₀ + ε V̂ cos ωt) + ε A₀' y`. -/
def smN (F : (X → ℝ) × ℝ → X → ℝ) (q0 : (X → ℝ) × ℝ) (Vh ω : ℝ) (A0' : Matrix X X ℝ)
    (ε t : ℝ) (y : X → ℝ) : X → ℝ :=
  F (q0.1 + y, q0.2 + ε * (Vh * Real.cos (ω * t))) + ε • (A0' *ᵥ y) - matX F q0 *ᵥ y -
    ε • smB F q0 Vh ω t

/-- The variational matrix `∂ₓF(x₀ + y, w₀ + ε V̂ cos ωt) + ε A₀'`. -/
def smJ (F : (X → ℝ) × ℝ → X → ℝ) (q0 : (X → ℝ) × ℝ) (Vh ω : ℝ) (A0' : Matrix X X ℝ)
    (ε t : ℝ) (y : X → ℝ) : Matrix X X ℝ :=
  matX F (q0.1 + y, q0.2 + ε * (Vh * Real.cos (ω * t))) + ε • A0'

/-- `D_u(t) = A₀' + V̂ cos(ωt) D_w(∂ₓF)(q₀)`. -/
def smDu (F : (X → ℝ) × ℝ → X → ℝ) (q0 : (X → ℝ) × ℝ) (Vh ω : ℝ) (A0' : Matrix X X ℝ)
    (t : ℝ) : Matrix X X ℝ :=
  A0' + (Vh * Real.cos (ω * t)) • smM1 F q0

@[tmio T, powerlib_foundation] theorem smN_rhs (F : (X → ℝ) × ℝ → X → ℝ) (q0 : (X → ℝ) × ℝ)
    (Vh ω : ℝ) (A0' : Matrix X X ℝ) (ε t : ℝ) (y : X → ℝ) :
    matX F q0 *ᵥ y + (ε • smB F q0 Vh ω t + smN F q0 Vh ω A0' ε t y) =
      F (q0.1 + y, q0.2 + ε * (Vh * Real.cos (ω * t))) + ε • (A0' *ᵥ y) := by
  simp only [smN]; abel

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem norm_prod_zero (y : X → ℝ) :
    ‖((y, (0 : ℝ)) : (X → ℝ) × ℝ)‖ = ‖y‖ := by
  rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]

@[tmio T, powerlib_foundation] theorem continuous_toMatrix :
    Continuous fun L : (X → ℝ) →L[ℝ] (X → ℝ) =>
      LinearMap.toMatrix' (L : (X → ℝ) →ₗ[ℝ] (X → ℝ)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe]
  exact (continuous_apply i).comp
    (ContinuousLinearMap.apply ℝ (X → ℝ) (Pi.single j 1)).continuous

/-- The estimates of `forced_orbit` and `orbit_variational` for a `C³` vector field with an
equilibrium at `q₀` and the drive `w₀ + ε V̂ cos ωt`. -/
@[tmio T, powerlib_foundation] theorem smooth_estimates {F : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 3 F q0) (hF0 : F q0 = 0) (Vh ω : ℝ)
    (A0' : Matrix X X ℝ) :
    ∃ K ρ ε0 KJ KD : ℝ, 0 ≤ K ∧ 0 < ρ ∧ 0 < ε0 ∧ 0 ≤ KJ ∧ 0 ≤ KD ∧
      (∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × (X → ℝ) => smN F q0 Vh ω A0' ε p.1 p.2)
        (Set.univ ×ˢ closedBall 0 ρ)) ∧
      (∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t, ‖smN F q0 Vh ω A0' ε t 0‖ ≤ K * ε ^ 2) ∧
      (∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y1 y2, ‖y1‖ ≤ ρ → ‖y2‖ ≤ ρ →
        ‖smN F q0 Vh ω A0' ε t y1 - smN F q0 Vh ω A0' ε t y2‖ ≤
          K * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖) ∧
      (∀ v, ‖smDx F q0 v‖ ≤ KD * ‖v‖) ∧
      (∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × (X → ℝ) => smJ F q0 Vh ω A0' ε p.1 p.2)
        (Set.univ ×ˢ closedBall 0 ρ)) ∧
      ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y, ‖y‖ ≤ ρ →
        ‖smJ F q0 Vh ω A0' ε t y - matX F q0 - smDx F q0 y - ε • smDu F q0 Vh ω A0' t‖ ≤
          KJ * (‖y‖ ^ 2 + ε ^ 2) := by
  have hF2 : ContDiffAt ℝ 2 F q0 := hF.of_le (by norm_num)
  have hJ2 : ContDiffAt ℝ 2 (jacX F) q0 :=
    (hF.fderiv_right (m := 2) (by norm_num)).clm_comp contDiffAt_const
  obtain ⟨r1, L1, hr1, hL1, hd1, hl1⟩ := exists_taylor_ball hF2
  obtain ⟨r2, L2, hr2, hL2, hd2, hl2⟩ := exists_taylor_ball hJ2
  set r := min r1 r2 with hr
  have hr0 : 0 < r := lt_min hr1 hr2
  set a := |Vh| with ha
  have ha0 : 0 ≤ a := abs_nonneg _
  set D2 := fderiv ℝ (jacX F) q0 with hD2
  set qp : ℝ → ℝ → (X → ℝ) → (X → ℝ) × ℝ :=
    fun ε t y => (q0.1 + y, q0.2 + ε * (Vh * Real.cos (ω * t))) with hqp
  have hqd : ∀ ε t y, qp ε t y - q0 = (y, ε * (Vh * Real.cos (ω * t))) := by
    intro ε t y; ext <;> simp [hqp]
  have hva : ∀ t, |Vh * Real.cos (ω * t)| ≤ a := fun t => by
    rw [abs_mul]; exact mul_le_of_le_one_right ha0 (Real.abs_cos_le_one _)
  have hqn : ∀ ε t y, 0 ≤ ε → ‖qp ε t y - q0‖ ≤ max ‖y‖ (ε * a) := by
    intro ε t y hε
    rw [hqd, Prod.norm_def, Real.norm_eq_abs, abs_mul, abs_of_nonneg hε]
    exact max_le_max le_rfl (mul_le_mul_of_nonneg_left (hva t) hε)
  have hεa : ∀ ε, 0 ≤ ε → ε ≤ r / (3 * (a + 1)) → ε * a ≤ r / 3 := by
    intro ε hε h
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  have hr13 : r / 3 ≤ r1 := (div_le_self hr0.le (by norm_num)).trans (min_le_left _ _)
  have hr23 : r / 3 ≤ r2 := (div_le_self hr0.le (by norm_num)).trans (min_le_right _ _)
  have hc : ∀ ε, Continuous (fun p : ℝ × (X → ℝ) => qp ε p.1 p.2) := fun ε => by
    simp only [hqp]; fun_prop
  have hmap : ∀ ε, 0 ≤ ε → ε ≤ r / (3 * (a + 1)) → ∀ ρ', r / 3 ≤ ρ' →
      MapsTo (fun p : ℝ × (X → ℝ) => qp ε p.1 p.2) (Set.univ ×ˢ closedBall 0 (r / 3))
        (closedBall q0 ρ') := by
    rintro ε hε hεe ρ' hρ' ⟨t, y⟩ ⟨-, hy⟩
    rw [mem_closedBall_iff_norm]
    refine (hqn ε t y hε).trans (max_le ?_ ((hεa ε hε hεe).trans hρ'))
    exact (mem_closedBall_zero_iff.1 hy).trans hρ'
  have hsq : ∀ ε t y, 0 ≤ ε → ‖qp ε t y - q0‖ * ‖qp ε t y - q0‖ ≤ (1 + a ^ 2) * (‖y‖ ^ 2 + ε ^ 2) := by
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
    have h3 : Continuous fun p : ℝ × (X → ℝ) => matX F q0 *ᵥ p.2 :=
      continuous_const.matrix_mulVec continuous_snd
    have h4 : Continuous fun p : ℝ × (X → ℝ) => ε • smB F q0 Vh ω p.1 := by
      simp only [smB]; fun_prop
    exact ((h1.add h2.continuousOn).sub h3.continuousOn).sub h4.continuousOn
  · intro ε hε hεe t
    have hsplit : ((0 : X → ℝ), ε * (Vh * Real.cos (ω * t))) =
        (ε * (Vh * Real.cos (ω * t))) • ((0 : X → ℝ), (1 : ℝ)) := by ext <;> simp
    have e : smN F q0 Vh ω A0' ε t 0 = F (qp ε t 0) - F q0 - fderiv ℝ F q0 (qp ε t 0 - q0) := by
      rw [hqd, hF0, sub_zero, hsplit, map_smul]
      simp only [smN, smB, hqp, Matrix.mulVec_zero, smul_zero, add_zero, sub_zero, smul_smul]
    rw [e]
    have hm : ‖qp ε t 0 - q0‖ ≤ ε * a := by
      have := hqn ε t 0 hε; rwa [norm_zero, max_eq_right (by positivity)] at this
    have hb := taylor_sub hL1 hd1 hl1 (m := ‖qp ε t 0 - q0‖) (hm.trans ((hεa ε hε hεe).trans hr13))
      (q1 := qp ε t 0) (q2 := q0) (by rw [mem_closedBall_iff_norm])
      (mem_closedBall_self (norm_nonneg _))
    refine hb.trans ?_
    have h0 := norm_nonneg (qp ε t 0 - q0)
    calc L1 * ‖qp ε t 0 - q0‖ * ‖qp ε t 0 - q0‖ ≤ L1 * (ε * a) * (ε * a) := by gcongr
      _ ≤ (L1 * (1 + a) + ‖A0'‖ + L1 * a ^ 2) * ε ^ 2 := by
          nlinarith [mul_nonneg hL1 ha0, norm_nonneg A0', sq_nonneg ε, mul_nonneg hL1 (sq_nonneg ε)]
  · intro ε hε hεe t y1 y2 hy1 hy2
    have hq12 : qp ε t y1 - qp ε t y2 = (y1 - y2, 0) := by ext <;> simp [hqp]
    have e : smN F q0 Vh ω A0' ε t y1 - smN F q0 Vh ω A0' ε t y2 =
        (F (qp ε t y1) - F (qp ε t y2) - fderiv ℝ F q0 (qp ε t y1 - qp ε t y2)) +
          ε • (A0' *ᵥ (y1 - y2)) := by
      rw [hq12, ← matX_mulVec]
      simp only [smN, hqp, Matrix.mulVec_sub, smul_sub]; abel
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
    rw [hq12, norm_prod_zero] at hb
    have hA : ‖ε • (A0' *ᵥ (y1 - y2))‖ ≤ ε * ‖A0'‖ * ‖y1 - y2‖ := by
      rw [norm_smul, Real.norm_of_nonneg hε, mul_assoc]
      exact mul_le_mul_of_nonneg_left (Matrix.linfty_opNorm_mulVec _ _) hε
    have hd0 := norm_nonneg (y1 - y2)
    have hn1 := norm_nonneg y1
    have hn2 := norm_nonneg y2
    calc _ ≤ L1 * m * ‖y1 - y2‖ + ε * ‖A0'‖ * ‖y1 - y2‖ := (norm_add_le _ _).trans (add_le_add hb hA)
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
    show ‖LinearMap.toMatrix' ((D2 (v, 0) : (X → ℝ) →L[ℝ] (X → ℝ)) : (X → ℝ) →ₗ[ℝ] (X → ℝ))‖ ≤ _
    rw [Matrix.linfty_opNorm_toMatrix]
    exact (D2.le_opNorm _).trans_eq (by rw [norm_prod_zero])
  · intro ε hε hεe
    have hJon : ContinuousOn (jacX F) (closedBall q0 r2) := fun q hq =>
      (hd2 q hq).continuousAt.continuousWithinAt
    have h1 := continuous_toMatrix.comp_continuousOn
      (hJon.comp (hc ε).continuousOn (hmap ε hε hεe r2 hr23))
    exact h1.add continuousOn_const
  · intro ε hε hεe t y hy
    have hsplit : (y, ε * (Vh * Real.cos (ω * t))) =
        ((y, (0 : ℝ)) : (X → ℝ) × ℝ) + (ε * (Vh * Real.cos (ω * t))) • ((0 : X → ℝ), (1 : ℝ)) := by
      ext <;> simp
    have e : smJ F q0 Vh ω A0' ε t y - matX F q0 - smDx F q0 y - ε • smDu F q0 Vh ω A0' t =
        LinearMap.toMatrix' ((jacX F (qp ε t y) - jacX F q0 - D2 (qp ε t y - q0) :
          (X → ℝ) →L[ℝ] (X → ℝ)) : (X → ℝ) →ₗ[ℝ] (X → ℝ)) := by
      rw [hqd, hsplit, map_add, map_smul]
      simp only [smJ, smDu, smDx, smM1, matX, hqp, LinearMap.coe_mk, AddHom.coe_mk,
        ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_add,
        ContinuousLinearMap.toLinearMap_smul, map_sub, map_add, map_smul, smul_add, smul_smul]
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

/-- The modulation `A₁ = D_x(∂ₓF)(q₀) z + V̂ D_w(∂ₓF)(q₀)` along the first-order orbit
`y_p = Re{z e^{jωt}}`. -/
def smA1 (F : (X → ℝ) × ℝ → X → ℝ) (q0 : (X → ℝ) × ℝ) (Vh : ℝ) (z : X → ℂ) : Matrix X X ℂ :=
  DxC (smDx F q0) z + (Vh : ℂ) • (smM1 F q0).map (algebraMap ℝ ℂ)

/-- The common data: the forcing is harmonic, `y_p = Re{z e^{jωt}}` solves the linearization and
`D_x y_p + D_u = A₀' + Re{A₁ e^{jωt}}`. -/
@[tmio T, powerlib_foundation] theorem smooth_link (F : (X → ℝ) × ℝ → X → ℝ)
    (q0 : (X → ℝ) × ℝ) {Vh ω : ℝ} (hω : ω ≠ 0) {z : X → ℂ} (hz : ((ω : ℂ) * I) • z - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ z =   (Vh : ℂ) • fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ))
    (A0' : Matrix X X ℝ) :
    Continuous (smB F q0 Vh ω) ∧ (∀ t, smB F q0 Vh ω (t + 2 * Real.pi / ω) = smB F q0 Vh ω t) ∧
      (∀ ε t y, smN F q0 Vh ω A0' ε (t + 2 * Real.pi / ω) y = smN F q0 Vh ω A0' ε t y) ∧
      Continuous (smDu F q0 Vh ω A0') ∧
      (∀ t, harm z ω (t + 2 * Real.pi / ω) = harm z ω t) ∧
      (∀ t, HasDerivAt (harm z ω) (matX F q0 *ᵥ harm z ω t + smB F q0 Vh ω t) t) ∧
      ∀ t, smDx F q0 (harm z ω t) + smDu F q0 Vh ω A0' t = A0' + modX (smA1 F q0 Vh z) ω t := by
  have e : ∀ t, ω * (t + 2 * Real.pi / ω) = ω * t + 2 * Real.pi := fun t => by field_simp
  have hbh : ∀ t, harm ((Vh : ℂ) • fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ)) ω t =
      smB F q0 Vh ω t := fun t => by
    funext i; simp [harm, smB]; ring
  refine ⟨by unfold smB; fun_prop, fun t => by simp only [smB, e, Real.cos_add_two_pi],
    fun ε t y => by simp only [smN, smB, e, Real.cos_add_two_pi],
    by unfold smDu; fun_prop, fun t => harm_periodic z hω t, fun t => ?_, fun t => ?_⟩
  · have h := harm_hasDerivAt hz t
    rwa [hbh] at h
  · rw [Dx_harm, smA1, modX_add, smDu]
    have hm : modX ((Vh : ℂ) • (smM1 F q0).map (algebraMap ℝ ℂ)) ω t =
        (Vh * Real.cos (ω * t)) • smM1 F q0 := by
      ext i j; simp [modX]; ring
    rw [hm]; abel

/-- End-to-end for a `C³` vector field, stability. `F(x₀, w₀) = 0`, drive `w₀ + ε V̂ cos ωt`,
state matrix perturbation `ε A₀'`; `∂ₓF(q₀)` has real modal coordinates with the pair `±jω/2`; `z`
the first-order forced response. If `Re λ₁ < 0` and `|g/2| < |λ₁|` (`λ₁ = u A₀' r`,
`g = u A₁ r̄`, `A₁ = smA1`), then for all small `ε > 0` the forced orbit exists (unique in the
ball of radius `cε`) and every Floquet multiplier of its variational equation lies inside the
unit circle. -/
@[tmio T, powerlib_foundation] theorem smooth_orbit_floquet_stable {Y : Type*} [Fintype Y]
    [DecidableEq Y] {F : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 3 F q0) (hF0 : F q0 = 0) {Vh ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matX F q0 * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ z =
      (Vh : ℂ) • fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ))
    (A0' : Matrix X X ℝ)
    (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hg : ‖physLeft Q ⬝ᵥ (smA1 F q0 Vh z *ᵥ star (physRight P)) / 2‖ ^ 2 <
      ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t))) +
            ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t))) +
            ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : X → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => smJ F q0 Vh ω A0' ε t (y t)) (2 * Real.pi / ω) 0).map
            (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  obtain ⟨K, ρ, ε0, KJ, KD, hK, hρ, hε0, hKJ, hKD, hNc, hN0, hNL, hDx, hJc, hJ⟩ :=
    smooth_estimates hF hF0 Vh ω A0'
  obtain ⟨Minv, hL, hR⟩ := exists_minv_of_modal hω hPQ hQP As hA0 hsr
  obtain ⟨hb, hbp, hNp, hDu, hpp, hpd, hlink⟩ := smooth_link F q0 hω.ne' hz A0'
  have h := orbit_floquet_stable (by positivity) hL hR hb hbp hK hρ hε0 hNc hNp hN0 hNL hKJ hKD
    hDx hDu hJc hJ hpp hpd hω rfl hPQ hQP As hA0 hsr A0' (smA1 F q0 Vh z) hlink hs hg
  simp only [smN_rhs] at h
  exact h

/-- End-to-end for a `C³` vector field, parametric instability: `|λ₁| < |g/2|`. -/
@[tmio T, powerlib_foundation] theorem smooth_orbit_floquet_unstable {Y : Type*} [Fintype Y]
    [DecidableEq Y] {F : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 3 F q0) (hF0 : F q0 = 0) {Vh ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matX F q0 * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ z =
      (Vh : ℂ) • fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ))
    (A0' : Matrix X X ℝ)
    (hg : ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2 <
      ‖physLeft Q ⬝ᵥ (smA1 F q0 Vh z *ᵥ star (physRight P)) / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t))) +
            ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t))) +
            ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJ F q0 Vh ω A0' ε t (y t)) (2 * Real.pi / ω) := by
  obtain ⟨K, ρ, ε0, KJ, KD, hK, hρ, hε0, hKJ, hKD, hNc, hN0, hNL, hDx, hJc, hJ⟩ :=
    smooth_estimates hF hF0 Vh ω A0'
  obtain ⟨Minv, hL, hR⟩ := exists_minv_of_modal hω hPQ hQP As hA0 hsr
  obtain ⟨hb, hbp, hNp, hDu, hpp, hpd, hlink⟩ := smooth_link F q0 hω.ne' hz A0'
  have h := orbit_floquet_unstable (by positivity) hL hR hb hbp hK hρ hε0 hNc hNp hN0 hNL hKJ hKD
    hDx hDu hJc hJ hpp hpd hω rfl hPQ hQP As hA0 hsr A0' (smA1 F q0 Vh z) hlink hg
  simp only [smN_rhs] at h
  exact h

/-- Three-state `C³` vector fields, end-to-end stability (eigen-data of `∂ₓF(q₀)`: pair `±jΩ`,
real pole `λ₃ < 0`; drive at `2Ω`). -/
@[tmio T, powerlib_foundation] theorem smooth_orbit_floquet_three_stable {F : ((Fin 3) → ℝ) × ℝ → (Fin 3) → ℝ}
    {q0 : ((Fin 3) → ℝ) × ℝ} (hF : ContDiffAt ℝ 3 F q0) (hF0 : F q0 = 0) {Vh Ω : ℝ} (hΩ : 0 < Ω)
    {l3 : ℝ} (hl3 : l3 < 0) {r u : Fin 3 → ℂ} {r3 u3 : Fin 3 → ℝ}
    (hr : (matX F q0).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (matX F q0).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : matX F q0 *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* matX F q0 = l3 • u3) (hur3 : u3 ⬝ᵥ r3 = 1)
    {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ z =
      (Vh : ℂ) • fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ))
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : (u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)).re < 0)
    (hg : ‖u ⬝ᵥ (smA1 F q0 Vh z *ᵥ star r) / 2‖ ^ 2 <
      ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (2 * Ω * t))) +
            ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (2 * Ω * t))) +
            ε • (A0' *ᵥ y t)) t) →
        ∀ (μ : ℂ) (v : Fin 3 → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => smJ F q0 Vh (2 * Ω) A0' ε t (y t))
            (2 * Real.pi / (2 * Ω)) 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1 := by
  obtain ⟨hQP, hPQ, hQAP, hLu, hRr⟩ := modal_three hΩ.ne' hr hu hur hr3 hu3 hur3
  have hω : 0 < 2 * Ω := by linarith
  have hA0 : modalQ u u3 * matX F q0 * modalP r r3 =
      fromBlocks (base 0 (2 * Ω / 2)) 0 0 !![l3] := by
    rw [hQAP, mul_div_cancel_left₀ _ two_ne_zero]
  have hq : ‖expS (!![l3] : Matrix (Fin 1) (Fin 1) ℝ) (2 * Real.pi / (2 * Ω))‖ < 1 := by
    rw [norm_expS_one, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (by positivity) hl3
  exact smooth_orbit_floquet_stable hF hF0 hω hPQ hQP _ hA0 (BlockAveraging.spectralRadius_lt_one_of_norm _ hq) hz A0'
    (by rw [hLu, hRr]; exact hs) (by rw [hLu, hRr]; exact hg)

/-- Three-state `C³` vector fields, end-to-end parametric instability. -/
@[tmio T, powerlib_foundation] theorem smooth_orbit_floquet_three_unstable {F : ((Fin 3) → ℝ) × ℝ → (Fin 3) → ℝ}
    {q0 : ((Fin 3) → ℝ) × ℝ} (hF : ContDiffAt ℝ 3 F q0) (hF0 : F q0 = 0) {Vh Ω : ℝ} (hΩ : 0 < Ω)
    {l3 : ℝ} (hl3 : l3 < 0) {r u : Fin 3 → ℂ} {r3 u3 : Fin 3 → ℝ}
    (hr : (matX F q0).map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* (matX F q0).map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    (hr3 : matX F q0 *ᵥ r3 = l3 • r3) (hu3 : u3 ᵥ* matX F q0 = l3 • u3) (hur3 : u3 ⬝ᵥ r3 = 1)
    {z : Fin 3 → ℂ}
    (hz : (((2 * Ω : ℝ) : ℂ) * I) • z - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ z =
      (Vh : ℂ) • fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ))
    (A0' : Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ‖u ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ r)‖ ^ 2 <
      ‖u ⬝ᵥ (smA1 F q0 Vh z *ᵥ star r) / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧ (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (2 * Ω * t))) +
            ε • (A0' *ᵥ y t)) t) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → Fin 3 → ℝ, (∀ t, y (t + 2 * Real.pi / (2 * Ω)) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (2 * Ω * t))) +
            ε • (A0' *ᵥ y t)) t) →
        Periodic.FloquetUnstable (fun t => smJ F q0 Vh (2 * Ω) A0' ε t (y t))
          (2 * Real.pi / (2 * Ω)) := by
  obtain ⟨hQP, hPQ, hQAP, hLu, hRr⟩ := modal_three hΩ.ne' hr hu hur hr3 hu3 hur3
  have hω : 0 < 2 * Ω := by linarith
  have hA0 : modalQ u u3 * matX F q0 * modalP r r3 =
      fromBlocks (base 0 (2 * Ω / 2)) 0 0 !![l3] := by
    rw [hQAP, mul_div_cancel_left₀ _ two_ne_zero]
  have hq : ‖expS (!![l3] : Matrix (Fin 1) (Fin 1) ℝ) (2 * Real.pi / (2 * Ω))‖ < 1 := by
    rw [norm_expS_one, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (by positivity) hl3
  exact smooth_orbit_floquet_unstable hF hF0 hω hPQ hQP _ hA0 (BlockAveraging.spectralRadius_lt_one_of_norm _ hq) hz A0'
    (by rw [hLu, hRr]; exact hg)

end Smooth

/-! ### Modal coordinates from the critical eigenvectors and a basis of the stable subspace -/

section Basis

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem real_right_eig_gen {A : Matrix X X ℝ} {r : X → ℂ} {Ω : ℝ}
    (hr : A.map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r) :
    A *ᵥ (fun k => (r k).re) = -Ω • (fun k => (r k).im) ∧
      A *ᵥ (fun k => (r k).im) = Ω • (fun k => (r k).re) := by
  constructor <;> funext i <;> have h := congrFun hr i
  · have h1 := congrArg Complex.re h
    simp [Matrix.mulVec, dotProduct, Complex.re_sum] at h1
    simp [Matrix.mulVec, dotProduct]; linarith
  · have h1 := congrArg Complex.im h
    simp [Matrix.mulVec, dotProduct, Complex.im_sum] at h1
    simp [Matrix.mulVec, dotProduct]; linarith

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem real_left_eig_gen {A : Matrix X X ℝ} {u : X → ℂ} {Ω : ℝ}
    (hu : u ᵥ* A.map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) :
    (fun k => (u k).re) ᵥ* A = -Ω • (fun k => (u k).im) ∧
      (fun k => (u k).im) ᵥ* A = Ω • (fun k => (u k).re) := by
  constructor <;> funext i <;> have h := congrFun hu i
  · have h1 := congrArg Complex.re h
    simp [Matrix.vecMul, dotProduct, Complex.re_sum] at h1
    simp [Matrix.vecMul, dotProduct]; linarith
  · have h1 := congrArg Complex.im h
    simp [Matrix.vecMul, dotProduct, Complex.im_sum] at h1
    simp [Matrix.vecMul, dotProduct]; linarith

/-- `P = [Re r, −Im r | W]`. -/
def basisP (r : X → ℂ) (W : Matrix X Y ℝ) : Matrix X (Fin 2 ⊕ Y) ℝ :=
  Matrix.fromCols (Matrix.of fun i j => ![(r i).re, -(r i).im] j) W

/-- `Q = [2 Re u; 2 Im u; W']`. -/
def basisQ (u : X → ℂ) (W' : Matrix Y X ℝ) : Matrix (Fin 2 ⊕ Y) X ℝ :=
  Matrix.fromRows (Matrix.of fun i j => ![2 * (u j).re, 2 * (u j).im] i) W'

/-- Modal coordinates of any real matrix with the simple pair `±jΩ` (eigenvectors `r`, `u`,
`u r = 1`) and an invariant complement spanned by `W` (`A W = W A_s`) with left inverse `W'` (`W' W = I`)
annihilating the critical pair (`u W = 0`, `W' r = 0`): `Q P = I`, `P Q = I`,
`Q A P = diag(base(0, Ω), A_s)`, `(ℓ, 0) Q = u`, `P (r₀, 0) = r`. -/
@[tmio T, powerlib_foundation] theorem modal_of_basis (e : X ≃ Fin 2 ⊕ Y) {A : Matrix X X ℝ}
    {Ω : ℝ} (hΩ : Ω ≠ 0) {r u : X → ℂ}
    (hr : A.map (algebraMap ℝ ℂ) *ᵥ r = ((Ω : ℂ) * I) • r)
    (hu : u ᵥ* A.map (algebraMap ℝ ℂ) = ((Ω : ℂ) * I) • u) (hur : u ⬝ᵥ r = 1)
    {W : Matrix X Y ℝ} {W' : Matrix Y X ℝ} {As : Matrix Y Y ℝ} (hW : A * W = W * As)
    (hWW : W' * W = 1) (huW : u ᵥ* W.map (algebraMap ℝ ℂ) = 0)
    (hWr : W'.map (algebraMap ℝ ℂ) *ᵥ r = 0) :
    basisQ u W' * basisP r W = 1 ∧ basisP r W * basisQ u W' = 1 ∧
      basisQ u W' * A * basisP r W = fromBlocks (TwoToOne.base 0 Ω) 0 0 As ∧
      physLeft (basisQ u W') = u ∧ physRight (basisP r W) = r := by
  obtain ⟨hx, hy⟩ := real_right_eig_gen hr
  obtain ⟨hp, hq⟩ := real_left_eig_gen hu
  set x : X → ℝ := fun k => (r k).re with hxd
  set y : X → ℝ := fun k => (r k).im with hyd
  set p : X → ℝ := fun k => (u k).re with hpd
  set q : X → ℝ := fun k => (u k).im with hqd
  have hre : p ⬝ᵥ x - q ⬝ᵥ y = 1 := by
    have h := congrArg Complex.re hur
    simp [dotProduct, Complex.re_sum] at h
    simp only [hxd, hyd, hpd, hqd, dotProduct]; linarith
  have him : p ⬝ᵥ y + q ⬝ᵥ x = 0 := by
    have h := congrArg Complex.im hur
    simp [dotProduct, Complex.im_sum, Finset.sum_add_distrib] at h
    simp only [hxd, hyd, hpd, hqd, dotProduct]; linarith
  have e1 : -Ω * (q ⬝ᵥ x) = -Ω * (p ⬝ᵥ y) := by
    have h := Matrix.dotProduct_mulVec p A x
    rw [hx, hp, dotProduct_smul, smul_dotProduct] at h
    simpa [smul_eq_mul] using h.symm
  have e2 : -Ω * (q ⬝ᵥ y) = Ω * (p ⬝ᵥ x) := by
    have h := Matrix.dotProduct_mulVec p A y
    rw [hy, hp, dotProduct_smul, smul_dotProduct] at h
    simpa [smul_eq_mul] using h.symm
  have hqx : q ⬝ᵥ x = p ⬝ᵥ y := mul_left_cancel₀ (neg_ne_zero.2 hΩ) e1
  have hpx2 : p ⬝ᵥ x = -(q ⬝ᵥ y) :=
    mul_left_cancel₀ hΩ (show Ω * (p ⬝ᵥ x) = Ω * (-(q ⬝ᵥ y)) by linarith)
  have hpx : p ⬝ᵥ x = 1 / 2 := by linarith
  have hqy : q ⬝ᵥ y = -(1 / 2) := by linarith
  have hpy : p ⬝ᵥ y = 0 := by linarith
  have hqx0 : q ⬝ᵥ x = 0 := by linarith
  have hpW : p ᵥ* W = 0 := by
    funext l; have h := congrArg Complex.re (congrFun huW l)
    simpa [Matrix.vecMul, dotProduct, Complex.re_sum] using h
  have hqW : q ᵥ* W = 0 := by
    funext l; have h := congrArg Complex.im (congrFun huW l)
    simpa [Matrix.vecMul, dotProduct, Complex.im_sum] using h
  have hWx : W' *ᵥ x = 0 := by
    funext k; have h := congrArg Complex.re (congrFun hWr k)
    simpa [Matrix.mulVec, dotProduct, Complex.re_sum] using h
  have hWy : W' *ᵥ y = 0 := by
    funext k; have h := congrArg Complex.im (congrFun hWr k)
    simpa [Matrix.mulVec, dotProduct, Complex.im_sum] using h
  set Pc : Matrix X (Fin 2) ℝ := Matrix.of fun i j => ![(r i).re, -(r i).im] j with hPc
  set Qc : Matrix (Fin 2) X ℝ := Matrix.of fun i j => ![2 * (u j).re, 2 * (u j).im] i with hQc
  have hQP1 : Qc * Pc = 1 := by
    simp only [dotProduct, hxd, hyd, hpd, hqd] at hpx hqy hpy hqx0
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [hQc, hPc, Matrix.mul_apply, mul_assoc, ← Finset.mul_sum] <;> linarith
  have hQW : Qc * W = 0 := by
    ext a l
    have h1 := congrFun hpW l
    have h2 := congrFun hqW l
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at h1 h2
    fin_cases a <;> simp [hQc, Matrix.mul_apply, mul_assoc, ← Finset.mul_sum, hpd, hqd] at h1 h2 ⊢
    · simpa using h1
    · simpa using h2
  have hWP : W' * Pc = 0 := by
    ext k b
    have h1 := congrFun hWx k
    have h2 := congrFun hWy k
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h1 h2
    fin_cases b <;> simp [hPc, Matrix.mul_apply, hxd, hyd] at h1 h2 ⊢
    · simpa [mul_comm] using h1
    · simpa [mul_comm] using h2
  have hQP : basisQ u W' * basisP r W = 1 := by
    rw [basisQ, basisP, ← hPc, ← hQc, Matrix.fromRows_mul_fromCols, hQP1, hQW, hWP, hWW,
      fromBlocks_one]
  have hAPc : A * Pc = Pc * TwoToOne.base 0 Ω := by
    ext i b
    have hxi := congrFun hx i
    have hyi := congrFun hy i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hxi hyi
    fin_cases b <;> simp [hPc, Matrix.mul_apply, TwoToOne.base, Fin.sum_univ_two, hxd, hyd]
      at hxi hyi ⊢ <;> linarith
  refine ⟨hQP, (Matrix.mul_eq_one_comm_of_equiv e.symm).1 hQP, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, basisP, Matrix.mul_fromCols, ← hPc, hAPc, hW, basisQ, ← hQc,
      Matrix.fromRows_mul_fromCols, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hQP1, hQW, hWP, hWW]
    simp
  · funext k
    simp only [physLeft, basisQ, Matrix.fromRows_map, Matrix.sumElim_vecMul_fromRows,
      Matrix.zero_vecMul, add_zero]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, TwoToOne.left]
    apply Complex.ext <;> simp
  · funext k
    simp only [physRight, basisP, Matrix.fromCols_map, Matrix.fromCols_mulVec_sumElim,
      Matrix.mulVec_zero, add_zero]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, TwoToOne.right]

end Basis

/-! ### Derivatives from complexified directional derivatives -/

section Lift

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The complexification of a real vector. -/
def ofv (y : X → ℝ) : X → ℂ := fun i => (y i : ℂ)

omit [Fintype X] [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem ofv_injective : Function.Injective (ofv (X := X)) := by
  intro a b h; funext i; have := congrFun h i; simpa [ofv] using this

omit [Fintype X] [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem hasDerivAt_ofv {G : ℝ → X → ℝ} {G' : X → ℝ} {s : ℝ}
    (h : HasDerivAt G G' s) : HasDerivAt (fun s => ofv (G s)) (ofv G') s :=
  hasDerivAt_pi.2 fun i => (hasDerivAt_pi.1 h i).ofReal_comp

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem hasDerivAt_line (q : (X → ℝ) × ℝ) (w : (X → ℝ) × ℝ) :
    HasDerivAt (fun s : ℝ => q + s • w) w 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add q

/-- The partial Jacobian from a complexified directional derivative: if the complexification of
`s ↦ F(x + s y, w)` has the derivative `M_c ȳ` for every `y`, then `∂ₓF = M_c`. -/
@[tmio T, powerlib_foundation] theorem matX_of_lift {F : (X → ℝ) × ℝ → X → ℝ} {q : (X → ℝ) × ℝ}
    (hF : DifferentiableAt ℝ F q) {Mc : Matrix X X ℂ}
    (h : ∀ y, HasDerivAt (fun s : ℝ => ofv (F (q.1 + s • y, q.2))) (Mc *ᵥ ofv y) 0) :
    (matX F q).map (algebraMap ℝ ℂ) = Mc := by
  ext i j
  have hl := hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line q (Pi.single j 1, 0))
    (by simp)
  have h1 := hasDerivAt_ofv hl
  have hs : ofv (Pi.single j (1 : ℝ)) = Pi.single j (1 : ℂ) := by
    funext k; by_cases hk : k = j
    · subst hk; simp [ofv]
    · simp [ofv, hk]
  have h2 := h (Pi.single j 1)
  rw [hs] at h2
  have e : ∀ s : ℝ, q + s • ((Pi.single j 1 : X → ℝ), (0 : ℝ)) = (q.1 + s • Pi.single j 1, q.2) :=
    fun s => by ext <;> simp
  simp only [Function.comp_def, e] at h1
  have hu := congrFun (h1.unique h2) i
  rw [← matX_mulVec] at hu
  simpa [ofv, Matrix.mulVec_single_one] using hu

omit [DecidableEq X] in
/-- The voltage derivative `∂_wF` from a complexified directional derivative. -/
@[tmio T, powerlib_foundation] theorem fderivW_of_lift {F : (X → ℝ) × ℝ → X → ℝ}
    {q : (X → ℝ) × ℝ} (hF : DifferentiableAt ℝ F q) {b : X → ℂ}
    (h : HasDerivAt (fun s : ℝ => ofv (F (q.1, q.2 + s))) b 0) :
    ofv (fderiv ℝ F q (0, 1)) = b := by
  have hl := hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line q (0, 1)) (by simp)
  have h1 := hasDerivAt_ofv hl
  have e : ∀ s : ℝ, q + s • ((0 : X → ℝ), (1 : ℝ)) = (q.1, q.2 + s) := fun s => by ext <;> simp
  simp only [Function.comp_def, e] at h1
  exact h1.unique h

/-- The entries of `∂ₓF` along a line through `q₀` have the derivatives of the second
derivative `D(∂ₓF)(q₀) w`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_matX_line {F : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 2 F q0) (w : (X → ℝ) × ℝ) (i j : X) :
    HasDerivAt (fun t : ℝ => ((matX F (q0 + t • w) i j : ℝ) : ℂ))
      ((LinearMap.toMatrix' ((fderiv ℝ (jacX F) q0 w : (X → ℝ) →L[ℝ] (X → ℝ)) :
        (X → ℝ) →ₗ[ℝ] (X → ℝ)) i j : ℝ) : ℂ) 0 := by
  have hJ : DifferentiableAt ℝ (jacX F) q0 :=
    ((hF.fderiv_right (m := 1) (by norm_num)).clm_comp contDiffAt_const).differentiableAt
      (by norm_num)
  have hl := hJ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_line q0 w) (by simp)
  have h2 := (ContinuousLinearMap.apply ℝ (X → ℝ) (Pi.single j 1)).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hl
  have h3 := (hasDerivAt_pi.1 h2 i).ofReal_comp
  simpa [matX, LinearMap.toMatrix'_apply, Function.comp_def] using h3

/-- `D_x(∂ₓF)(q₀) y` from complexified entries along the line `x₀ + t y`. -/
@[tmio T, powerlib_foundation] theorem smDx_of_lift {F : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 2 F q0) (y : X → ℝ) {Jc : ℝ → Matrix X X ℂ}
    (hJc : ∀ᶠ t in 𝓝 (0 : ℝ), (matX F (q0.1 + t • y, q0.2)).map (algebraMap ℝ ℂ) = Jc t)
    {M : Matrix X X ℂ} (hM : ∀ i j, HasDerivAt (fun t => Jc t i j) (M i j) 0) :
    (smDx F q0 y).map (algebraMap ℝ ℂ) = M := by
  ext i j
  have h := hasDerivAt_matX_line hF (y, 0) i j
  have e : ∀ t : ℝ, q0 + t • (y, (0 : ℝ)) = (q0.1 + t • y, q0.2) := fun t => by ext <;> simp
  simp only [e] at h
  have h2 : HasDerivAt (fun t => Jc t i j) _ 0 := h.congr_of_eventuallyEq
    (hJc.mono fun t ht => by simp only [← ht]; rfl)
  exact h2.unique (hM i j)

/-- `D_w(∂ₓF)(q₀)` from complexified entries along the line `w₀ + t`. -/
@[tmio T, powerlib_foundation] theorem smM1_of_lift {F : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 2 F q0) {Jc : ℝ → Matrix X X ℂ}
    (hJc : ∀ᶠ t in 𝓝 (0 : ℝ), (matX F (q0.1, q0.2 + t)).map (algebraMap ℝ ℂ) = Jc t)
    {M : Matrix X X ℂ} (hM : ∀ i j, HasDerivAt (fun t => Jc t i j) (M i j) 0) :
    (smM1 F q0).map (algebraMap ℝ ℂ) = M := by
  ext i j
  have h := hasDerivAt_matX_line hF (0, 1) i j
  have e : ∀ t : ℝ, q0 + t • ((0 : X → ℝ), (1 : ℝ)) = (q0.1, q0.2 + t) := fun t => by
    ext <;> simp
  simp only [e] at h
  have h2 : HasDerivAt (fun t => Jc t i j) _ 0 := h.congr_of_eventuallyEq
    (hJc.mono fun t ht => by simp only [← ht]; rfl)
  exact h2.unique (hM i j)

omit [Fintype X] [DecidableEq X] in
/-- `D_x z` for a complex direction from the real directions: if `D(Re z)` and `D(Im z)` lift to
`M(Re z)`, `M(Im z)` with `M` complex-linear, then `D_x z = M z`. -/
@[tmio T, powerlib_foundation] theorem DxC_of_lift (Dx : (X → ℝ) →ₗ[ℝ] Matrix X X ℝ)
    (M : (X → ℂ) →ₗ[ℂ] Matrix X X ℂ) (h : ∀ y, (Dx y).map (algebraMap ℝ ℂ) = M (ofv y))
    (z : X → ℂ) : DxC Dx z = M z := by
  have hz : z = ofv (fun k => (z k).re) + I • ofv (fun k => (z k).im) := by
    funext k; apply Complex.ext <;> simp [ofv]
  have e1 := h (fun k => (z k).re)
  have e2 := h (fun k => (z k).im)
  conv_rhs => rw [hz, map_add, map_smul, ← e1, ← e2]
  ext i j
  apply Complex.ext <;> simp [DxC]

omit [DecidableEq X] in
/-- Derivatives of the entries of `A J(t) B` from those of `J(t)`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_conj_entries {J : ℝ → Matrix X X ℂ}
    {M : Matrix X X ℂ} (hM : ∀ i j, HasDerivAt (fun t => J t i j) (M i j) 0)
    (A B : Matrix X X ℂ) (i j : X) :
    HasDerivAt (fun t => (A * J t * B) i j) ((A * M * B) i j) 0 := by
  simp only [Matrix.mul_apply]
  refine HasDerivAt.fun_sum fun k _ => ?_
  refine HasDerivAt.mul_const (HasDerivAt.fun_sum fun l _ => ?_) _
  exact (hM l k).const_mul _

omit [DecidableEq X] in
/-- Derivative of `M v(s)`. -/
@[tmio T, powerlib_foundation] theorem hasDerivAt_mulVec_c {G : ℝ → X → ℂ} {G' : X → ℂ} {s : ℝ}
    (M : Matrix X X ℂ) (h : HasDerivAt G G' s) :
    HasDerivAt (fun s => M *ᵥ G s) (M *ᵥ G') s := by
  refine hasDerivAt_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_pi.1 h k).const_mul _

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem map_ofReal_mulVec_ofv (M : Matrix X X ℝ) (y : X → ℝ) :
    M.map (algebraMap ℝ ℂ) *ᵥ ofv y = ofv (M *ᵥ y) := by
  funext i; simp [ofv, Matrix.mulVec, dotProduct]

omit [Fintype X] [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem map_ofReal_injective :
    Function.Injective (fun M : Matrix X X ℝ => M.map (algebraMap ℝ ℂ)) := by
  intro A B h
  ext i j
  have := congrFun (congrFun h i) j
  simpa using this

/-- Real version of `matX_of_lift`. -/
@[tmio T, powerlib_foundation] theorem matX_of_line {F : (X → ℝ) × ℝ → X → ℝ} {q : (X → ℝ) × ℝ}
    (hF : DifferentiableAt ℝ F q) {M : Matrix X X ℝ}
    (h : ∀ y, HasDerivAt (fun s : ℝ => F (q.1 + s • y, q.2)) (M *ᵥ y) 0) : matX F q = M :=
  map_ofReal_injective (matX_of_lift hF fun y => by
    rw [map_ofReal_mulVec_ofv]; exact hasDerivAt_ofv (h y))

omit [DecidableEq X] in
/-- Real version of `fderivW_of_lift`. -/
@[tmio T, powerlib_foundation] theorem fderivW_of_line {F : (X → ℝ) × ℝ → X → ℝ}
    {q : (X → ℝ) × ℝ} (hF : DifferentiableAt ℝ F q) {b : X → ℝ}
    (h : HasDerivAt (fun s : ℝ => F (q.1, q.2 + s)) b 0) : fderiv ℝ F q (0, 1) = b :=
  ofv_injective (fderivW_of_lift hF (hasDerivAt_ofv h))

/-- Real version of `smDx_of_lift`. -/
@[tmio T, powerlib_foundation] theorem smDx_of_line {F : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 2 F q0) (y : X → ℝ) {Jr : ℝ → Matrix X X ℝ}
    (hJ : ∀ᶠ t in 𝓝 (0 : ℝ), matX F (q0.1 + t • y, q0.2) = Jr t) {M : Matrix X X ℝ}
    (hM : ∀ i j, HasDerivAt (fun t => Jr t i j) (M i j) 0) : smDx F q0 y = M :=
  map_ofReal_injective (smDx_of_lift hF y (Jc := fun t => (Jr t).map (algebraMap ℝ ℂ))
    (hJ.mono fun t ht => by rw [ht]) fun i j => (hM i j).ofReal_comp)

/-- Real version of `smM1_of_lift`. -/
@[tmio T, powerlib_foundation] theorem smM1_of_line {F : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 2 F q0) {Jr : ℝ → Matrix X X ℝ}
    (hJ : ∀ᶠ t in 𝓝 (0 : ℝ), matX F (q0.1, q0.2 + t) = Jr t) {M : Matrix X X ℝ}
    (hM : ∀ i j, HasDerivAt (fun t => Jr t i j) (M i j) 0) : smM1 F q0 = M :=
  map_ofReal_injective (smM1_of_lift hF (Jc := fun t => (Jr t).map (algebraMap ℝ ℂ))
    (hJ.mono fun t ht => by rw [ht]) fun i j => (hM i j).ofReal_comp)

end Lift

end powerlib.ParametricResonance.ForcedOrbit
