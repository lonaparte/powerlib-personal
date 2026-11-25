import theorem.ParametricResonance.SmoothForcedOrbit

/-! # Transfer of the end-to-end statements: parameter changes and inactive limiters

The end-to-end theorems are stated for a `C³` field `F` with the perturbation `εA₀'(x − x₀)` added
to it. Two facts let them speak about other fields. First, a physical parameter change
`p → p + εp₁` that enters the field affinely in the state gives exactly
`G = F + εA₀'(x − x₀)`; then the Jacobian `smJ` of the theorems is the true Jacobian of `G` along
the orbit. Second, a field `G` that agrees with `F` on a ball around the operating point (a
saturation inactive there) has the same orbits in the `O(ε)` tube and the same Jacobian along them,
although `G` need not be smooth.

Scope.
* Fields `(X → ℝ) × ℝ → X → ℝ` on a finite state space with the sup norm; scalar input
  `w₀ + εV̂ cos ωt`; the orbit tube `‖y‖ ≤ cε`.
* Saturation `max(−M, min(M, P))` of a scalar port map `P(x_i, w)` continuous at the operating
  point with `|P| < M` there. The switching set `|P| = M` is not reached by the tube for small
  `ε`; nothing is claimed about solutions that reach it.

Source: technical report `GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的
统一元素级比较：A₀、A₁ 与 Γ") §2.1 (the unfolding `A₀(ε) = A₀c + εA₀'` of a design parameter) and §3; limits are
outside the model of the report.

Results.
* `matX_shift`, `smJ_shift` — `G = F + εA(x − x₀)` has Jacobian `∂ₓF + εA` wherever `F` is
  differentiable; along the orbit this is `smJ`.
* `eventually_tube` — the tube lies in any ball around `q₀` for small `ε > 0`.
* `matX_congr_ball`, `smJ_congr_ball` — fields that agree on a ball have the same Jacobians there.
* `satMap`, `exists_ball_sat_eq` — an inactive saturation is inactive on a ball.

Corrections.
None: an extension.

Family and connection conclusions.
None: static evidence on vector fields (Jacobians of shifted and locally equal fields).
-/

noncomputable section
namespace powerlib.ParametricResonance.ForcedOrbit
open Matrix Filter Topology

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Parameter shifts: `G = F + ε A₀'(x − x₀)` -/

/-- If `G(x, V) = F(x, V) + ε A(x − x₀)`, the state Jacobian of `G` is that of `F` plus `ε A` at
every point where `F` is differentiable. -/
@[tmio T, powerlib_foundation] theorem matX_shift {F G : (X → ℝ) × ℝ → X → ℝ} {x0 : X → ℝ}
    {ε : ℝ} {A : Matrix X X ℝ} (hG : ∀ x V, G (x, V) = F (x, V) + ε • (A *ᵥ (x - x0)))
    {q : (X → ℝ) × ℝ} (hF : DifferentiableAt ℝ F q) : matX G q = matX F q + ε • A := by
  have hGe : G = F + ε • (⇑(Matrix.toLin' A).toContinuousLinearMap ∘
      fun q : (X → ℝ) × ℝ => q.1 - x0) := by
    funext ⟨x, V⟩; rw [hG]; simp [Matrix.toLin'_apply]
  have h1 : HasFDerivAt (fun q : (X → ℝ) × ℝ => q.1 - x0)
      (ContinuousLinearMap.fst ℝ (X → ℝ) ℝ) q := hasFDerivAt_fst.sub_const x0
  have h2 := (((Matrix.toLin' A).toContinuousLinearMap.hasFDerivAt).comp q h1).const_smul ε
  have h3 := hF.hasFDerivAt.add h2
  rw [← hGe] at h3
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, matX_mulVec, h3.fderiv, Matrix.add_mulVec,
    matX_mulVec, Matrix.smul_mulVec]
  simp

/-- Along an orbit, the Jacobian `smJ` of the end-to-end theorems is the true state Jacobian of
the shifted field `G = F + ε A₀'(x − x₀)`, wherever `F` is differentiable. -/
@[tmio T, powerlib_foundation] theorem smJ_shift {F G : (X → ℝ) × ℝ → X → ℝ} {ε : ℝ}
    {A : Matrix X X ℝ} (q0 : (X → ℝ) × ℝ)
    (hG : ∀ x V, G (x, V) = F (x, V) + ε • (A *ᵥ (x - q0.1))) (Vh ω : ℝ) (y : ℝ → X → ℝ)
    (hF : ∀ t, DifferentiableAt ℝ F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t)))) :
    (fun t => smJ F q0 Vh ω A ε t (y t)) =
      fun t => matX G (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t))) :=
  funext fun t => by rw [smJ, matX_shift hG (hF t)]

/-! ### Fields that agree near the operating point -/

omit [DecidableEq X] in
/-- The tube `‖y‖ ≤ cε`, `V = V₀ + εV̂s` (`|s| ≤ 1`) lies in any ball around `q₀` for all small
`ε > 0`. -/
@[tmio T, powerlib_foundation] theorem eventually_tube (q0 : (X → ℝ) × ℝ) {r : ℝ} (hr : 0 < r)
    (c Vh : ℝ) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (y : X → ℝ) (s : ℝ), ‖y‖ ≤ c * ε → |s| ≤ 1 →
      ‖(q0.1 + y, q0.2 + ε * (Vh * s)) - q0‖ < r := by
  have hK : 0 < |c| + |Vh| + 1 := by positivity
  filter_upwards [Ioo_mem_nhdsGT (div_pos hr hK)] with ε hε y s hy hs
  obtain ⟨hε0, hε1⟩ := hε
  have hεK : ε * (|c| + |Vh| + 1) < r := by rwa [lt_div_iff₀ hK] at hε1
  have e : (q0.1 + y, q0.2 + ε * (Vh * s)) - q0 = (y, ε * (Vh * s)) :=
    Prod.ext (by simp) (by simp)
  rw [e, Prod.norm_def, max_lt_iff]
  constructor
  · calc ‖y‖ ≤ c * ε := hy
      _ ≤ |c| * ε := mul_le_mul_of_nonneg_right (le_abs_self c) hε0.le
      _ < r := by nlinarith [abs_nonneg c, abs_nonneg Vh]
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hε0]
    have : |Vh| * |s| ≤ |Vh| := by nlinarith [abs_nonneg Vh, abs_nonneg s]
    calc ε * (|Vh| * |s|) ≤ ε * |Vh| := mul_le_mul_of_nonneg_left this hε0.le
      _ < r := by nlinarith [abs_nonneg c, abs_nonneg Vh]

/-- Fields that agree on a ball have the same state Jacobian inside it. -/
@[tmio T, powerlib_foundation] theorem matX_congr_ball {F G : (X → ℝ) × ℝ → X → ℝ}
    {q0 q : (X → ℝ) × ℝ} {r : ℝ} (hGF : ∀ q', ‖q' - q0‖ < r → G q' = F q')
    (hq : ‖q - q0‖ < r) : matX G q = matX F q := by
  have h : G =ᶠ[𝓝 q] F := by
    have hb : Metric.ball q0 r ∈ 𝓝 q :=
      Metric.isOpen_ball.mem_nhds (by rwa [Metric.mem_ball, dist_eq_norm])
    filter_upwards [hb] with q' hq'
    exact hGF q' (by rwa [Metric.mem_ball, dist_eq_norm] at hq')
  simp only [matX, jacX, h.fderiv_eq]

/-- Along a curve inside the ball, the Jacobians `smJ` of two fields agreeing on the ball
coincide. -/
@[tmio T, powerlib_foundation] theorem smJ_congr_ball {F G : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} {r : ℝ} (hGF : ∀ q', ‖q' - q0‖ < r → G q' = F q') (Vh ω : ℝ)
    (A : Matrix X X ℝ) (ε : ℝ) (y : ℝ → X → ℝ)
    (hy : ∀ t, ‖(q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t))) - q0‖ < r) :
    (fun t => smJ G q0 Vh ω A ε t (y t)) = fun t => smJ F q0 Vh ω A ε t (y t) :=
  funext fun t => by rw [smJ, smJ, matX_congr_ball hGF (hy t)]

/-- The saturation `max(−M, min(M, P))` of a scalar port map. -/
def satMap (M : ℝ) (P : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ := max (-M) (min M (P z))

omit [DecidableEq X] in
/-- A saturation that is inactive at the operating point (`|P(z₀)| < M`, `P` continuous there) is
inactive on a ball around it: `sat_M P = P` for all states within `r` of `q₀`, where
`z = (x_i, V)`. -/
@[tmio T, powerlib_foundation] theorem exists_ball_sat_eq {P : ℝ × ℝ → ℝ} {q0 : (X → ℝ) × ℝ}
    (i : X) {M : ℝ} (hP : ContinuousAt P (q0.1 i, q0.2)) (hM : |P (q0.1 i, q0.2)| < M) :
    ∃ r, 0 < r ∧ ∀ q : (X → ℝ) × ℝ, ‖q - q0‖ < r → satMap M P (q.1 i, q.2) = P (q.1 i, q.2) := by
  have h : ∀ᶠ z in 𝓝 (q0.1 i, q0.2), |P z| < M :=
    (continuous_abs.continuousAt.comp hP).eventually_lt continuousAt_const hM
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨r, hr, fun q hq => ?_⟩
  have hd : dist (q.1 i, q.2) (q0.1 i, q0.2) < r := by
    rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]
    have h1 : ‖q.1 i - q0.1 i‖ ≤ ‖q.1 - q0.1‖ := by
      rw [← Pi.sub_apply]; exact norm_le_pi_norm (q.1 - q0.1) i
    have h2 : ‖q.1 - q0.1‖ ≤ ‖q - q0‖ := norm_fst_le (q - q0)
    have h3 : ‖q.2 - q0.2‖ ≤ ‖q - q0‖ := norm_snd_le (q - q0)
    exact ⟨by linarith, by linarith⟩
  obtain ⟨hl, hu⟩ := abs_lt.1 (hb hd)
  rw [satMap, min_eq_right hu.le, max_eq_right hl.le]

end powerlib.ParametricResonance.ForcedOrbit
