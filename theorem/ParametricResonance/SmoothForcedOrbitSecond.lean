import theorem.ParametricResonance.ForcedOrbitSecond
import theorem.ParametricResonance.SmoothOrbitStability
import theorem.Periodic.OrbitalInstability

/-! # The forced orbit of a smooth field on the first-order boundary: decided at second order

`ForcedOrbit.smooth_orbit_floquet_stable` / `smooth_orbit_floquet_unstable` and
`Periodic.Levels.orbit_stable_below_threshold` / `orbit_unstable_above_threshold` decide the forced
orbit of a `C³` field `F(x, w)` (equilibrium `F(x₀, w₀) = 0`, drive `w₀ + εV̂ cos ωt`, state
perturbation `εA₀'`) off the first-order boundary `|g/2| = |λ₁|` (`|V̂||g₁| = 2|λ₁|`). This file
decides the boundary itself, for a `C⁴` field, at the levels L1 (Floquet multipliers of the
variational equation of the actual forced orbit) and L0 (the nonlinear orbit).

The second-order data are explicit in the derivatives of the field at `q₀ = (x₀, w₀)` and the
first-order displacement `k(t) = (Re{z e^{jωt}}, V̂ cos ωt)` of state and input (`smK`, `z` the
first-order forced response):
* the second-order forcing `h₂ = ½ D²F(q₀)[k, k] + A₀' Re{z e^{jωt}}` (`smH2`): the quadratic term
  of the field on the first-order displacement (frequencies `0` and `2ω`) and the first-order
  state perturbation acting on the first-order response; the second-order forced response `y₂` is
  its periodic response `ẏ₂ = ∂ₓF(q₀) y₂ + h₂`, unique and given by the Green function
  (`second_response`), explicitly `y₂ = w₀ + Re{w₁ e^{jωt}} + Re{w₂ e^{2jωt}}` with
  `A w₀ = −h₀`, `(jωI − A) w₁ = A₀' z`, `(2jωI − A) w₂ = h₂ᶜ` by harmonic balance
  (`smH2_harmonic`, `second_response_harmonic`);
* the second-order part of the variational matrix
  `A₂ = D_x(∂ₓF)(q₀)[y₂] + ½ D²(∂ₓF)(q₀)[k, k]` (`smDx`, `smB2`): the second-order response through
  the curvature of the Jacobian, plus the third derivatives of the field on the first-order
  response and the input;
* the decisive quantity `Δ = orbitMixed P Q A_s ω A₀' A₁ A₂` of
  `theorem/ParametricResonance/ForcedOrbitSecond.lean`:
  `mixedDet(M, N_eff + ∫₀ᵀ R(−ωt/2)(Q A₂ P)₁₁ R(ωt/2) dt)` with the first-order slow-flow matrix
  `M`, the effective second-order matrix `N_eff` of the modal standard form (its second Picard
  term and the coupling to the stable block through `E = e^{TA_s}`) and the rotating-frame mean of
  the critical block of `A₂`.
On the boundary `|λ₁| = |g/2|`, `Re λ₁ < 0`: `Δ > 0` gives all Floquet multipliers inside the unit
circle and a locally exponentially stable nonlinear orbit, `Δ < 0` Floquet instability and an
unstable nonlinear orbit, for all small `ε > 0` (`smooth_orbit_boundary_floquet`,
`smooth_orbit_boundary`). The estimates are the second-order Taylor bound `taylor_two` along
lines (no symmetry of the second derivative is used) and the quadratic remainder of the field
around the orbit (`smooth_orbit_L0`).

Model boundary.
* `F : ℝ^X × ℝ → ℝ^X` (finite `X`, sup norms), `ContDiffAt ℝ 4 F q₀` (`C³` for the orbit
  expansion and for L0, `C⁴` for the second-order Jacobian), `F(q₀) = 0`; scalar input
  `w₀ + εV̂ cos ωt`, `ω > 0`, `T = 2π/ω`; state perturbation `εA₀'` with a constant real `A₀'`;
  deviation coordinates `x = state − x₀`.
* Real modal coordinates `Q ∂ₓF(q₀) P = diag(base(0, ω/2), A_s)` with `ρ(e^{TA_s}) < 1`; `z` with
  `(jωI − ∂ₓF(q₀)) z = V̂ ∂_wF(q₀)`; `y₂` any `T`-periodic solution of `ẏ₂ = ∂ₓF(q₀) y₂ + h₂`.
* The first-order boundary `|λ₁| = |g/2|`, `Re λ₁ < 0` (`λ₁ = u A₀' r`, `g = u A₁ r̄`,
  `A₁ = ForcedOrbit.smA1`). Conclusions for all sufficiently small `ε > 0`; `Δ = 0` is not decided
  (it needs the next order).
* Solutions of the stability statements are integral curves on `[s, ∞)`, those of the instability
  statements on segments `[s, t]`.

Source: the wave-6 question of this library (the forced orbit on the first-order boundary, left
open in `theorem/Periodic/LevelsNonlinear.lean` and
`theorem/ParametricResonance/BoundaryUndecided.lean`); technical report
`GFM_five_unified_A0A1_Gamma` (2026-11-07, "五类构网型变流器参数振荡的统一元素级比较：A₀、A₁ 与 Γ")
§2.1–§2.2 (`J_p = A₀ + ε Re{A₁ e^{jω_p t}}` along the forced trajectory, its `O(ε²)` terms);
second-order perturbation of a forced periodic orbit and the variational equation along it
(Nayfeh–Mook, *Nonlinear Oscillations*, Ch. 5); `ForcedOrbit.smooth_estimates`,
`ForcedOrbit.smooth_link`, `ForcedOrbitSecond.orbit_boundary_floquet`,
`Periodic.exp_stable_of_floquet`, `Periodic.unstable_of_floquet`, `Periodic.Levels.pump_drive`,
`Boundary.forced_threshold_boundary_iff`.

Results.
* `taylor_two` — `‖G(q₀ + h) − G(q₀) − G'(q₀)h − ½G''(q₀)hh‖ ≤ L‖h‖³`.
* `smK`, `smH2`, `smB2`, `continuous_smK`, `smK_periodic`, `smK_smul`, `continuous_smH2`,
  `continuous_smB2`, `smH2_periodic` — the second-order data of the field.
* `smooth_h2_bound`, `smooth_B2_bound`, `smooth_jac_lip` — the second-order estimates of the
  nonlinearity and of the Jacobian along the first-order orbit.
* `second_response` — existence, uniqueness and Green-function form of `y₂`; `kapR`, `kapI`,
  `smH0`, `smH2c`, `smK_eq`, `smH2_harmonic` (`h₂ = h₀ + Re{h₂ᶜ e^{2jωt}} + Re{A₀' z e^{jωt}}`),
  `second_response_harmonic` — `y₂ = w₀ + Re{w₁ e^{jωt}} + Re{w₂ e^{2jωt}}` by harmonic balance.
* `smooth_orbit_boundary_floquet` — level L1 on the boundary, decided by the sign of `Δ`.
* `smooth_orbit_L0` — from the multipliers of any small periodic solution to its nonlinear
  stability or instability; `smooth_orbit_boundary` — level L0 on the boundary;
  `smooth_orbit_at_threshold` — the same at the drive threshold `|V̂||g₁| = 2|λ₁|`.

Corrections.
None: an extension (the boundary `|V̂||g₁| = 2|λ₁|` of `Periodic.Levels`).

Family and connection conclusions.
None: static evidence on smooth periodically forced ODEs (forced orbit, Floquet multipliers,
local exponential stability and instability).
-/

noncomputable section
namespace powerlib.ParametricResonance.ForcedOrbitSecond

open Complex Matrix Set Filter Topology Metric
open scoped Matrix.Norms.Operator
open ForcedOrbit (taylor_sub exists_taylor_ball jacX matX matX_mulVec smDx smM1 smB smN smJ smDu
  smA1 smooth_estimates smooth_link harm norm_prod_zero continuous_toMatrix exists_minv_of_modal
  exists_lipschitz_ball quad_remainder spectralRadius_lt_one_of_eig smN_rhs
  exists_bound_of_periodic_vec)
open BlockAveraging (expS modX physJR physLeft physRight)
open TwoToOne (base)

/-! ## Second-order Taylor bound along a line -/

section Taylor

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

/-- **Second-order Taylor bound.** If `G` is differentiable on the ball `‖q − q₀‖ ≤ r` with a
differentiable derivative whose derivative is Lipschitz at `q₀`
(`‖G''(q) − G''(q₀)‖ ≤ L ‖q − q₀‖`), then
`‖G(q₀ + h) − G(q₀) − G'(q₀) h − ½ G''(q₀) h h‖ ≤ L ‖h‖³` for `‖h‖ ≤ r` (mean value inequality for
`s ↦ G(q₀ + s h) − s G'(q₀) h − (s²/2) G''(q₀) h h` on `[0, 1]`; no symmetry of `G''` is used). -/
@[tmio T, powerlib_foundation] theorem taylor_two {G : P → V} {q0 : P} {r L : ℝ} (hL0 : 0 ≤ L)
    (hd : ∀ q ∈ closedBall q0 r, HasFDerivAt G (fderiv ℝ G q) q)
    (hd2 : ∀ q ∈ closedBall q0 r, HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) q) q)
    (hL : ∀ q ∈ closedBall q0 r,
      ‖fderiv ℝ (fderiv ℝ G) q - fderiv ℝ (fderiv ℝ G) q0‖ ≤ L * ‖q - q0‖)
    {h : P} (hh : ‖h‖ ≤ r) :
    ‖G (q0 + h) - G q0 - fderiv ℝ G q0 h - (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ G) q0 h h‖ ≤
      L * ‖h‖ ^ 3 := by
  set D2 := fderiv ℝ (fderiv ℝ G) q0 with hD2
  set g : ℝ → V := fun s => G (q0 + s • h) - s • fderiv ℝ G q0 h - (s ^ 2 / 2) • D2 h h with hg
  set g' : ℝ → V := fun s => fderiv ℝ G (q0 + s • h) h - fderiv ℝ G q0 h - s • D2 h h with hg'
  have hsn : ∀ s ∈ Icc (0 : ℝ) 1, ‖s • h‖ ≤ ‖h‖ := fun s hs => by
    rw [norm_smul, Real.norm_of_nonneg hs.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hs.2
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, q0 + s • h ∈ closedBall q0 r := fun s hs => by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact (hsn s hs).trans hh
  have hder : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g (g' s) (Icc 0 1) s := by
    intro s hs
    have hline : HasDerivAt (fun s : ℝ => q0 + s • h) h s := by
      simpa using ((hasDerivAt_id s).smul_const h).const_add q0
    have h1 := (hd _ (hmem s hs)).comp_hasDerivAt s hline
    have h2 : HasDerivAt (fun s : ℝ => s • fderiv ℝ G q0 h) (fderiv ℝ G q0 h) s := by
      simpa using (hasDerivAt_id s).smul_const (fderiv ℝ G q0 h)
    have h3 : HasDerivAt (fun s : ℝ => (s ^ 2 / 2) • D2 h h) (s • D2 h h) s := by
      have := ((hasDerivAt_pow 2 s).div_const 2).smul_const (D2 h h)
      convert this using 1
      rw [show ((2 : ℕ) : ℝ) * s ^ (2 - 1) / 2 = s by norm_num]
    exact ((h1.sub h2).sub h3).hasDerivWithinAt
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1, ‖g' s‖ ≤ L * ‖h‖ ^ 3 := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hs
    have hm : ‖s • h‖ ≤ r := (hsn s hs').trans hh
    have ht := taylor_sub (G := fderiv ℝ G) (q0 := q0) (r := r) (L := L) hL0 hd2 hL hm
      (q1 := q0 + s • h) (q2 := q0) (by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left])
      (mem_closedBall_self (norm_nonneg _))
    rw [add_sub_cancel_left] at ht
    have e : g' s = (fderiv ℝ G (q0 + s • h) - fderiv ℝ G q0 - D2 (s • h)) h := by
      simp only [hg', map_smul, _root_.sub_apply, _root_.smul_apply]
    rw [e]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have h0 := norm_nonneg h
    have hs0 := norm_nonneg (s • h)
    calc ‖fderiv ℝ G (q0 + s • h) - fderiv ℝ G q0 - D2 (s • h)‖ * ‖h‖ ≤
          L * ‖s • h‖ * ‖s • h‖ * ‖h‖ := mul_le_mul_of_nonneg_right ht h0
      _ ≤ L * ‖h‖ * ‖h‖ * ‖h‖ := by
          have := hsn s hs'
          gcongr
      _ = L * ‖h‖ ^ 3 := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01' hder hbound
  have e : g 1 - g 0 = G (q0 + h) - G q0 - fderiv ℝ G q0 h - (1 / 2 : ℝ) • D2 h h := by
    simp only [hg, one_smul, zero_smul, add_zero, one_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_div, sub_zero]
    abel
  rw [← e]
  exact hmv

end Taylor

/-! ## The second-order data of a smooth field -/

section Smooth

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The first-order displacement of the operating point `q₀ + ε k(t) + O(ε²)` of state and input:
`k(t) = (Re{z e^{jωt}}, V̂ cos ωt)`. -/
def smK (z : X → ℂ) (Vh ω t : ℝ) : (X → ℝ) × ℝ := (harm z ω t, Vh * Real.cos (ω * t))

/-- The second-order forcing along the first-order orbit:
`h₂(t) = ½ D²F(q₀)[k(t), k(t)] + A₀' Re{z e^{jωt}}`. -/
def smH2 (F : (X → ℝ) × ℝ → X → ℝ) (q0 : (X → ℝ) × ℝ) (Vh ω : ℝ) (A0' : Matrix X X ℝ)
    (z : X → ℂ) (t : ℝ) : X → ℝ :=
  (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ F) q0 (smK z Vh ω t) (smK z Vh ω t) + A0' *ᵥ harm z ω t

/-- The second-order part of the Jacobian along the first-order orbit:
`B₂(t) = ½ D²(∂ₓF)(q₀)[k(t), k(t)]` (third derivatives of the field on the first-order response
and the input). -/
def smB2 (F : (X → ℝ) × ℝ → X → ℝ) (q0 : (X → ℝ) × ℝ) (Vh ω : ℝ) (z : X → ℂ) (t : ℝ) :
    Matrix X X ℝ :=
  (1 / 2 : ℝ) • LinearMap.toMatrix' ((fderiv ℝ (fderiv ℝ (jacX F)) q0 (smK z Vh ω t)
    (smK z Vh ω t) : (X → ℝ) →L[ℝ] (X → ℝ)) : (X → ℝ) →ₗ[ℝ] (X → ℝ))

omit [Fintype X] [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem continuous_smK (z : X → ℂ) (Vh ω : ℝ) :
    Continuous (smK z Vh ω) :=
  (ForcedOrbit.continuous_harm z ω).prodMk (by fun_prop)

omit [Fintype X] [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem smK_periodic (z : X → ℂ) (Vh : ℝ) {ω : ℝ} (hω : ω ≠ 0)
    (t : ℝ) : smK z Vh ω (t + 2 * Real.pi / ω) = smK z Vh ω t := by
  have e : ω * (t + 2 * Real.pi / ω) = ω * t + 2 * Real.pi := by field_simp
  rw [smK, smK, ForcedOrbit.harm_periodic z hω, e, Real.cos_add_two_pi]

omit [Fintype X] [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem smK_smul (z : X → ℂ) (Vh ω ε t : ℝ) :
    ε • smK z Vh ω t = ((ε • harm z ω t, (0 : ℝ)) : (X → ℝ) × ℝ) +
      (ε * (Vh * Real.cos (ω * t))) • (((0 : X → ℝ), (1 : ℝ)) : (X → ℝ) × ℝ) := by
  ext <;> simp [smK]

/-- The nonlinearity along the first-order orbit is `ε² h₂ + O(ε³)`: with `F(q₀) = 0`,
`N_ε(t, ε y₁) − ε² h₂ = F(q₀ + εk) − F(q₀) − F'(q₀)(εk) − ½ F''(q₀)(εk)(εk)`, bounded by the
second-order Taylor bound of a `C³` field. -/
@[tmio T, powerlib_foundation] theorem smooth_h2_bound {F : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 3 F q0) (hF0 : F q0 = 0) (Vh ω : ℝ)
    (A0' : Matrix X X ℝ) (z : X → ℂ) :
    ∃ r L, 0 < r ∧ 0 ≤ L ∧ ∀ ε t, ‖ε • smK z Vh ω t‖ ≤ r →
      ‖smN F q0 Vh ω A0' ε t (ε • harm z ω t) - ε ^ 2 • smH2 F q0 Vh ω A0' z t‖ ≤
        L * ‖ε • smK z Vh ω t‖ ^ 3 := by
  obtain ⟨r1, L1, hr1, hL1, hd1, -⟩ := exists_taylor_ball (hF.of_le (by norm_num))
  have hF1 : ContDiffAt ℝ 2 (fderiv ℝ F) q0 := hF.fderiv_right (m := 2) (by norm_num)
  obtain ⟨r2, L2, hr2, hL2, hd2, hl2⟩ := exists_taylor_ball hF1
  refine ⟨min r1 r2, L2, lt_min hr1 hr2, hL2, fun ε t hk => ?_⟩
  have hsub1 : closedBall q0 (min r1 r2) ⊆ closedBall q0 r1 :=
    closedBall_subset_closedBall (min_le_left _ _)
  have hsub2 : closedBall q0 (min r1 r2) ⊆ closedBall q0 r2 :=
    closedBall_subset_closedBall (min_le_right _ _)
  have ht := taylor_two hL2 (fun q hq => hd1 q (hsub1 hq)) (fun q hq => hd2 q (hsub2 hq))
    (fun q hq => hl2 q (hsub2 hq)) hk
  set D2 := fderiv ℝ (fderiv ℝ F) q0 with hD2
  have hq : q0 + ε • smK z Vh ω t =
      ((q0.1 + ε • harm z ω t, q0.2 + ε * (Vh * Real.cos (ω * t))) : (X → ℝ) × ℝ) := by
    ext <;> simp [smK]
  have hlin : fderiv ℝ F q0 (ε • smK z Vh ω t) =
      matX F q0 *ᵥ (ε • harm z ω t) + ε • smB F q0 Vh ω t := by
    rw [smK_smul, map_add, map_smul, matX_mulVec, smB, smul_smul]
  have hquad : D2 (ε • smK z Vh ω t) (ε • smK z Vh ω t) =
      ε ^ 2 • D2 (smK z Vh ω t) (smK z Vh ω t) := by
    simp only [map_smul, _root_.smul_apply, smul_smul, sq]
  have e : smN F q0 Vh ω A0' ε t (ε • harm z ω t) - ε ^ 2 • smH2 F q0 Vh ω A0' z t =
      F (q0 + ε • smK z Vh ω t) - F q0 - fderiv ℝ F q0 (ε • smK z Vh ω t) -
        (1 / 2 : ℝ) • D2 (ε • smK z Vh ω t) (ε • smK z Vh ω t) := by
    rw [hlin, hquad, hq, hF0, smN, smH2, Matrix.mulVec_smul]
    simp only [smul_add, smul_smul]
    module
  rw [e]
  exact ht

/-- The variational matrix along the first-order orbit is `A + ε A₁ + ε² B₂ + O(ε³)` for a `C⁴`
field: `J_ε(t, ε y₁) − A − ε(D_x y₁ + D_u) − ε² B₂` is the second-order Taylor remainder of
`∂ₓF` at `q₀` in the direction `εk`. -/
@[tmio T, powerlib_foundation] theorem smooth_B2_bound {F : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 4 F q0) (Vh ω : ℝ) (A0' : Matrix X X ℝ)
    (z : X → ℂ) :
    ∃ r L, 0 < r ∧ 0 ≤ L ∧ ∀ ε t, ‖ε • smK z Vh ω t‖ ≤ r →
      ‖smJ F q0 Vh ω A0' ε t (ε • harm z ω t) - matX F q0 -
          ε • (smDx F q0 (harm z ω t) + smDu F q0 Vh ω A0' t) - ε ^ 2 • smB2 F q0 Vh ω z t‖ ≤
        L * ‖ε • smK z Vh ω t‖ ^ 3 := by
  have hJ3 : ContDiffAt ℝ 3 (jacX F) q0 :=
    (hF.fderiv_right (m := 3) (by norm_num)).clm_comp contDiffAt_const
  obtain ⟨r1, L1, hr1, hL1, hd1, -⟩ := exists_taylor_ball (hJ3.of_le (by norm_num))
  have hJ1 : ContDiffAt ℝ 2 (fderiv ℝ (jacX F)) q0 := hJ3.fderiv_right (m := 2) (by norm_num)
  obtain ⟨r2, L2, hr2, hL2, hd2, hl2⟩ := exists_taylor_ball hJ1
  refine ⟨min r1 r2, L2, lt_min hr1 hr2, hL2, fun ε t hk => ?_⟩
  have hsub1 : closedBall q0 (min r1 r2) ⊆ closedBall q0 r1 :=
    closedBall_subset_closedBall (min_le_left _ _)
  have hsub2 : closedBall q0 (min r1 r2) ⊆ closedBall q0 r2 :=
    closedBall_subset_closedBall (min_le_right _ _)
  have ht := taylor_two hL2 (fun q hq => hd1 q (hsub1 hq)) (fun q hq => hd2 q (hsub2 hq))
    (fun q hq => hl2 q (hsub2 hq)) hk
  set D1 := fderiv ℝ (jacX F) q0 with hD1
  set D2 := fderiv ℝ (fderiv ℝ (jacX F)) q0 with hD2
  have hq : q0 + ε • smK z Vh ω t =
      ((q0.1 + ε • harm z ω t, q0.2 + ε * (Vh * Real.cos (ω * t))) : (X → ℝ) × ℝ) := by
    ext <;> simp [smK]
  have hquad : D2 (ε • smK z Vh ω t) (ε • smK z Vh ω t) =
      ε ^ 2 • D2 (smK z Vh ω t) (smK z Vh ω t) := by
    simp only [map_smul, _root_.smul_apply, smul_smul, sq]
  have hlin : D1 (ε • smK z Vh ω t) = ε • D1 ((harm z ω t, (0 : ℝ))) +
      (ε * (Vh * Real.cos (ω * t))) • D1 (((0 : X → ℝ), (1 : ℝ))) := by
    rw [smK_smul, map_add, map_smul]
    congr 1
    rw [show ((ε • harm z ω t, (0 : ℝ)) : (X → ℝ) × ℝ) = ε • ((harm z ω t, (0 : ℝ)) : (X → ℝ) × ℝ)
      by simp, map_smul]
  have e : smJ F q0 Vh ω A0' ε t (ε • harm z ω t) - matX F q0 -
        ε • (smDx F q0 (harm z ω t) + smDu F q0 Vh ω A0' t) - ε ^ 2 • smB2 F q0 Vh ω z t =
      LinearMap.toMatrix' ((jacX F (q0 + ε • smK z Vh ω t) - jacX F q0 -
        D1 (ε • smK z Vh ω t) - (1 / 2 : ℝ) • D2 (ε • smK z Vh ω t) (ε • smK z Vh ω t) :
          (X → ℝ) →L[ℝ] (X → ℝ)) : (X → ℝ) →ₗ[ℝ] (X → ℝ)) := by
    rw [hquad, hlin, hq]
    simp only [smJ, smDu, smDx, smM1, smB2, matX, LinearMap.coe_mk, AddHom.coe_mk, hD1,
      ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_add,
      ContinuousLinearMap.toLinearMap_smul, map_sub, map_add, map_smul, smul_add, smul_smul]
    module
  rw [e, Matrix.linfty_opNorm_toMatrix]
  exact ht

/-- The Jacobian is Lipschitz in the state up to its derivative at `q₀`, for a `C³` field:
`‖J_ε(t, y) − J_ε(t, y') − D_x(y − y')‖ ≤ L (‖y‖ + ‖y'‖ + ε|V̂|) ‖y − y'‖` on a ball. -/
@[tmio T, powerlib_foundation] theorem smooth_jac_lip {F : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 3 F q0) (Vh ω : ℝ) (A0' : Matrix X X ℝ) :
    ∃ r L, 0 < r ∧ 0 ≤ L ∧ ∀ ε t (y y' : X → ℝ), 0 ≤ ε → ‖y‖ + ‖y'‖ + ε * |Vh| ≤ r →
      ‖smJ F q0 Vh ω A0' ε t y - smJ F q0 Vh ω A0' ε t y' - smDx F q0 (y - y')‖ ≤
        L * (‖y‖ + ‖y'‖ + ε * |Vh|) * ‖y - y'‖ := by
  have hJ2 : ContDiffAt ℝ 2 (jacX F) q0 :=
    (hF.fderiv_right (m := 2) (by norm_num)).clm_comp contDiffAt_const
  obtain ⟨r, L, hr, hL, hd, hl⟩ := exists_taylor_ball hJ2
  refine ⟨r, L, hr, hL, fun ε t y y' hε hm => ?_⟩
  set qy : (X → ℝ) × ℝ := (q0.1 + y, q0.2 + ε * (Vh * Real.cos (ω * t))) with hqy
  set qy' : (X → ℝ) × ℝ := (q0.1 + y', q0.2 + ε * (Vh * Real.cos (ω * t))) with hqy'
  have hva : |ε * (Vh * Real.cos (ω * t))| ≤ ε * |Vh| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hε]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (abs_nonneg _)
      (Real.abs_cos_le_one _)) hε
  have hn : ∀ v : X → ℝ, ‖v‖ ≤ ‖y‖ + ‖y'‖ →
      ‖((q0.1 + v, q0.2 + ε * (Vh * Real.cos (ω * t))) : (X → ℝ) × ℝ) - q0‖ ≤
        ‖y‖ + ‖y'‖ + ε * |Vh| := by
    intro v hv
    rw [Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub, add_sub_cancel_left, Real.norm_eq_abs]
    have := mul_nonneg hε (abs_nonneg Vh)
    exact max_le (by linarith) (by linarith [norm_nonneg y, norm_nonneg y'])
  have h1 : qy ∈ closedBall q0 (‖y‖ + ‖y'‖ + ε * |Vh|) := by
    rw [mem_closedBall, dist_eq_norm]; exact hn y (by linarith [norm_nonneg y'])
  have h2 : qy' ∈ closedBall q0 (‖y‖ + ‖y'‖ + ε * |Vh|) := by
    rw [mem_closedBall, dist_eq_norm]; exact hn y' (by linarith [norm_nonneg y])
  have ht := taylor_sub hL hd hl hm h1 h2
  have hdq : qy - qy' = ((y - y', (0 : ℝ)) : (X → ℝ) × ℝ) := by ext <;> simp [hqy, hqy']
  rw [hdq, norm_prod_zero] at ht
  have e : smJ F q0 Vh ω A0' ε t y - smJ F q0 Vh ω A0' ε t y' - smDx F q0 (y - y') =
      LinearMap.toMatrix' ((jacX F qy - jacX F qy' - fderiv ℝ (jacX F) q0 (qy - qy') :
        (X → ℝ) →L[ℝ] (X → ℝ)) : (X → ℝ) →ₗ[ℝ] (X → ℝ)) := by
    rw [hdq, show smDx F q0 (y - y') = LinearMap.toMatrix' ((fderiv ℝ (jacX F) q0 (y - y', 0) :
      (X → ℝ) →L[ℝ] (X → ℝ)) : (X → ℝ) →ₗ[ℝ] (X → ℝ)) from rfl,
      ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_sub, map_sub, map_sub]
    simp only [smJ, matX, hqy, hqy']
    abel
  rw [e, Matrix.linfty_opNorm_toMatrix, hdq]
  exact ht

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem continuous_smH2 (F : (X → ℝ) × ℝ → X → ℝ)
    (q0 : (X → ℝ) × ℝ) (Vh ω : ℝ) (A0' : Matrix X X ℝ) (z : X → ℂ) :
    Continuous (smH2 F q0 Vh ω A0' z) := by
  have hk := continuous_smK z Vh ω
  have h1 : Continuous fun t => fderiv ℝ (fderiv ℝ F) q0 (smK z Vh ω t) (smK z Vh ω t) :=
    ((fderiv ℝ (fderiv ℝ F) q0).continuous.comp hk).clm_apply hk
  have h2 : Continuous fun t => A0' *ᵥ harm z ω t :=
    continuous_const.matrix_mulVec (ForcedOrbit.continuous_harm z ω)
  show Continuous fun t => (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ F) q0 (smK z Vh ω t) (smK z Vh ω t) +
    A0' *ᵥ harm z ω t
  exact (h1.const_smul (1 / 2 : ℝ)).add h2

@[tmio T, powerlib_foundation] theorem continuous_smB2 (F : (X → ℝ) × ℝ → X → ℝ)
    (q0 : (X → ℝ) × ℝ) (Vh ω : ℝ) (z : X → ℂ) : Continuous (smB2 F q0 Vh ω z) := by
  have hk := continuous_smK z Vh ω
  have h1 : Continuous fun t =>
      fderiv ℝ (fderiv ℝ (jacX F)) q0 (smK z Vh ω t) (smK z Vh ω t) :=
    ((fderiv ℝ (fderiv ℝ (jacX F)) q0).continuous.comp hk).clm_apply hk
  show Continuous fun t => (1 / 2 : ℝ) • LinearMap.toMatrix' ((fderiv ℝ (fderiv ℝ (jacX F)) q0
    (smK z Vh ω t) (smK z Vh ω t) : (X → ℝ) →L[ℝ] (X → ℝ)) : (X → ℝ) →ₗ[ℝ] (X → ℝ))
  exact (continuous_toMatrix.comp h1).const_smul (1 / 2 : ℝ)

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem smH2_periodic (F : (X → ℝ) × ℝ → X → ℝ)
    (q0 : (X → ℝ) × ℝ) (Vh : ℝ) {ω : ℝ} (hω : ω ≠ 0) (A0' : Matrix X X ℝ) (z : X → ℂ) (t : ℝ) :
    smH2 F q0 Vh ω A0' z (t + 2 * Real.pi / ω) = smH2 F q0 Vh ω A0' z t := by
  rw [smH2, smH2, smK_periodic z Vh hω, ForcedOrbit.harm_periodic z hω]

omit [DecidableEq X] in
@[tmio T, powerlib_foundation] private theorem exists_bound_smK (z : X → ℂ) (Vh : ℝ) {ω : ℝ}
    (hω : 0 < ω) : ∃ B, 0 ≤ B ∧ ∀ t, ‖smK z Vh ω t‖ ≤ B := by
  obtain ⟨Bh, hBh⟩ := exists_bound_of_periodic_vec (ForcedOrbit.continuous_harm z ω)
    (ForcedOrbit.harm_periodic z hω.ne') (by positivity : (0 : ℝ) < 2 * Real.pi / ω)
  refine ⟨max (max Bh |Vh|) 0, le_max_right _ _, fun t => ?_⟩
  rw [smK, Prod.norm_def, Real.norm_eq_abs]
  refine max_le ((hBh t).trans ((le_max_left _ _).trans (le_max_left _ _))) ?_
  rw [abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)).trans
    ((le_max_right _ _).trans (le_max_left _ _))

set_option maxHeartbeats 4000000 in
/-- **The forced orbit of a `C⁴` field on the first-order boundary, level L1.** `F(x₀, w₀) = 0`,
drive `w₀ + ε V̂ cos ωt`, state perturbation `ε A₀'`; real modal coordinates of `∂ₓF(q₀)` with
the pair `±jω/2` and `ρ(e^{TA_s}) < 1` (`T = 2π/ω`); `z` the first-order forced response,
`y₂` a `T`-periodic second-order forced response `ẏ₂ = ∂ₓF(q₀) y₂ + h₂`,
`h₂ = ½ D²F(q₀)[k, k] + A₀' Re{z e^{jωt}}` (`smH2`, `k = smK`); the first-order boundary
`|λ₁| = |g/2|`, `Re λ₁ < 0` (`λ₁ = u A₀' r`, `g = u A₁ r̄`, `A₁ = smA1`). With
`A₂ = D_x(∂ₓF)(q₀)[y₂] + ½ D²(∂ₓF)(q₀)[k, k]` and `Δ = orbitMixed P Q A_s ω A₀' A₁ A₂`: for all
small `ε > 0` the forced orbit exists (unique in the ball of radius `cε`); `Δ > 0` puts every
Floquet multiplier of its variational equation inside the unit circle and `Δ < 0` makes it
Floquet unstable. -/
@[tmio T, powerlib_foundation] theorem smooth_orbit_boundary_floquet {Y : Type*} [Fintype Y]
    [DecidableEq Y] {F : (X → ℝ) × ℝ → X → ℝ} {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 4 F q0)
    (hF0 : F q0 = 0) {Vh ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matX F q0 * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ z =
      (Vh : ℂ) • fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ))
    (A0' : Matrix X X ℝ) {y₂ : ℝ → X → ℝ} (h₂yp : ∀ t, y₂ (t + 2 * Real.pi / ω) = y₂ t)
    (h₂d : ∀ t, HasDerivAt y₂ (matX F q0 *ᵥ y₂ t + smH2 F q0 Vh ω A0' z t) t)
    (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hbd : ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2 =
      ‖physLeft Q ⬝ᵥ (smA1 F q0 Vh z *ᵥ star (physRight P)) / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧
        (∀ t, ‖y t‖ ≤ c * ε) ∧ ∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t))) +
          ε • (A0' *ᵥ y t)) t) ∧
      (0 < orbitMixed P Q As ω A0' (smA1 F q0 Vh z)
          (fun t => smDx F q0 (y₂ t) + smB2 F q0 Vh ω z t) →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) →
          (∀ t, ‖y t‖ ≤ c * ε) → (∀ t, HasDerivAt y (F (q0.1 + y t,
            q0.2 + ε * (Vh * Real.cos (ω * t))) + ε • (A0' *ᵥ y t)) t) →
          ∀ (μ : ℂ) (v : X → ℂ), v ≠ 0 →
            (Periodic.monodromy (fun t => smJ F q0 Vh ω A0' ε t (y t)) (2 * Real.pi / ω) 0).map
              (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1) ∧
      (orbitMixed P Q As ω A0' (smA1 F q0 Vh z)
          (fun t => smDx F q0 (y₂ t) + smB2 F q0 Vh ω z t) < 0 →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) →
          (∀ t, ‖y t‖ ≤ c * ε) → (∀ t, HasDerivAt y (F (q0.1 + y t,
            q0.2 + ε * (Vh * Real.cos (ω * t))) + ε • (A0' *ᵥ y t)) t) →
          Periodic.FloquetUnstable (fun t => smJ F q0 Vh ω A0' ε t (y t)) (2 * Real.pi / ω)) := by
  have hF3 : ContDiffAt ℝ 3 F q0 := hF.of_le (by norm_num)
  obtain ⟨K, ρ, ε0, -, KD, hK, hρ, hε0, -, hKD, hNc, hN0, hNL, hDx, hJc, -⟩ :=
    smooth_estimates hF3 hF0 Vh ω A0'
  obtain ⟨Minv, hL, hR⟩ := exists_minv_of_modal hω hPQ hQP As hA0 hsr
  obtain ⟨hb, hbp, hNp, hDu, hpp, hpd, hlink⟩ := smooth_link F q0 hω.ne' hz A0'
  obtain ⟨r1, L1, hr1, hL1, hN2b⟩ := smooth_h2_bound hF3 hF0 Vh ω A0' z
  obtain ⟨r2, L2, hr2, hL2, hJ2b⟩ := smooth_B2_bound hF Vh ω A0' z
  obtain ⟨r3, L3, hr3, hL3, hJLb⟩ := smooth_jac_lip hF3 Vh ω A0'
  obtain ⟨Bk, hBk0, hBk⟩ := exists_bound_smK z Vh hω
  set a := |Vh| with ha
  have ha0 : 0 ≤ a := abs_nonneg _
  set ρ' := min ρ (r3 / 3) with hρ'
  have hρ'0 : 0 < ρ' := lt_min hρ (by positivity)
  have hρ'ρ : ρ' ≤ ρ := min_le_left _ _
  have hρ'3 : ρ' ≤ r3 / 3 := min_le_right _ _
  set ε0' := min (min ε0 1) (min (r1 / (Bk + 1)) (min (r2 / (Bk + 1)) (r3 / (3 * (a + 1)))))
    with hε0'
  have hε0'p : 0 < ε0' := lt_min (lt_min hε0 one_pos)
    (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hε0'a : ε0' ≤ ε0 := (min_le_left _ _).trans (min_le_left _ _)
  have hε0'1 : ε0' ≤ r1 / (Bk + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hε0'2 : ε0' ≤ r2 / (Bk + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε0'3 : ε0' ≤ r3 / (3 * (a + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hkn : ∀ ε t, 0 ≤ ε → ‖ε • smK z Vh ω t‖ ≤ ε * Bk := fun ε t hε => by
    rw [norm_smul, Real.norm_of_nonneg hε]; exact mul_le_mul_of_nonneg_left (hBk t) hε
  have hεBk : ∀ ε r, 0 ≤ ε → 0 < r → ε ≤ r / (Bk + 1) → ε * Bk ≤ r := fun ε r hε hr h => by
    rw [le_div_iff₀ (by positivity)] at h; nlinarith
  have hcube : ∀ ε t (L : ℝ), 0 ≤ ε → 0 ≤ L → L * ‖ε • smK z Vh ω t‖ ^ 3 ≤ L * Bk ^ 3 * ε ^ 3 :=
    fun ε t L hε hL0 => by
      have h1 := hkn ε t hε
      have h2 : ‖ε • smK z Vh ω t‖ ^ 3 ≤ (ε * Bk) ^ 3 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 3
      calc L * ‖ε • smK z Vh ω t‖ ^ 3 ≤ L * (ε * Bk) ^ 3 := mul_le_mul_of_nonneg_left h2 hL0
        _ = L * Bk ^ 3 * ε ^ 3 := by ring
  -- the restricted hypotheses
  have hNc' : ∀ ε, 0 ≤ ε → ε ≤ ε0' → ContinuousOn (fun p : ℝ × (X → ℝ) => smN F q0 Vh ω A0' ε p.1 p.2)
      (Set.univ ×ˢ closedBall 0 ρ') := fun ε h0 h1 =>
    (hNc ε h0 (h1.trans hε0'a)).mono (Set.prod_mono le_rfl (closedBall_subset_closedBall hρ'ρ))
  have hN0' : ∀ ε, 0 ≤ ε → ε ≤ ε0' → ∀ t, ‖smN F q0 Vh ω A0' ε t 0‖ ≤ K * ε ^ 2 :=
    fun ε h0 h1 => hN0 ε h0 (h1.trans hε0'a)
  have hNL' : ∀ ε, 0 ≤ ε → ε ≤ ε0' → ∀ t y1 y2, ‖y1‖ ≤ ρ' → ‖y2‖ ≤ ρ' →
      ‖smN F q0 Vh ω A0' ε t y1 - smN F q0 Vh ω A0' ε t y2‖ ≤
        K * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖ := fun ε h0 h1 t y1 y2 hy1 hy2 =>
    hNL ε h0 (h1.trans hε0'a) t y1 y2 (hy1.trans hρ'ρ) (hy2.trans hρ'ρ)
  have hJc' : ∀ ε, 0 ≤ ε → ε ≤ ε0' → ContinuousOn (fun p : ℝ × (X → ℝ) => smJ F q0 Vh ω A0' ε p.1 p.2)
      (Set.univ ×ˢ closedBall 0 ρ') := fun ε h0 h1 =>
    (hJc ε h0 (h1.trans hε0'a)).mono (Set.prod_mono le_rfl (closedBall_subset_closedBall hρ'ρ))
  have hN₂ : ∀ ε, 0 < ε → ε ≤ ε0' → ∀ t, ‖smN F q0 Vh ω A0' ε t (ε • harm z ω t) -
      ε ^ 2 • smH2 F q0 Vh ω A0' z t‖ ≤ (L1 * Bk ^ 3) * ε ^ 3 := fun ε h0 h1 t =>
    (hN2b ε t ((hkn ε t h0.le).trans (hεBk ε r1 h0.le hr1 (h1.trans hε0'1)))).trans
      (hcube ε t L1 h0.le hL1)
  set KJ := L3 * (1 + a) + L2 * Bk ^ 3 with hKJ
  have hKJ0 : 0 ≤ KJ := by positivity
  have hJ₂ : ∀ ε, 0 < ε → ε ≤ ε0' → ∀ t, ‖smJ F q0 Vh ω A0' ε t (ε • harm z ω t) - matX F q0 -
      ε • (smDx F q0 (harm z ω t) + smDu F q0 Vh ω A0' t) - ε ^ 2 • smB2 F q0 Vh ω z t‖ ≤
        KJ * ε ^ 3 := fun ε h0 h1 t => by
    refine (hJ2b ε t ((hkn ε t h0.le).trans (hεBk ε r2 h0.le hr2 (h1.trans hε0'2)))).trans
      ((hcube ε t L2 h0.le hL2).trans ?_)
    have : L2 * Bk ^ 3 ≤ KJ := by rw [hKJ]; nlinarith [mul_nonneg hL3 (by linarith : (0:ℝ) ≤ 1 + a)]
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hJL : ∀ ε, 0 ≤ ε → ε ≤ ε0' → ∀ t (y y' : X → ℝ), ‖y‖ ≤ ρ' → ‖y'‖ ≤ ρ' →
      ‖smJ F q0 Vh ω A0' ε t y - smJ F q0 Vh ω A0' ε t y' - smDx F q0 (y - y')‖ ≤
        KJ * (‖y‖ + ‖y'‖ + ε) * ‖y - y'‖ := fun ε h0 h1 t y y' hy hy' => by
    have hεa : ε * a ≤ r3 / 3 := by
      have h := h1.trans hε0'3
      rw [le_div_iff₀ (by positivity)] at h
      nlinarith
    have hm : ‖y‖ + ‖y'‖ + ε * a ≤ r3 := by linarith
    refine (hJLb ε t y y' h0 hm).trans ?_
    have hd0 := norm_nonneg (y - y')
    have hk : L3 * (‖y‖ + ‖y'‖ + ε * a) ≤ KJ * (‖y‖ + ‖y'‖ + ε) := by
      have hy0 := norm_nonneg y
      have hy'0 := norm_nonneg y'
      have h2 : L3 * (‖y‖ + ‖y'‖ + ε * a) ≤ L3 * (1 + a) * (‖y‖ + ‖y'‖ + ε) := by
        nlinarith [mul_nonneg hL3 ha0, mul_nonneg (mul_nonneg hL3 ha0) (add_nonneg hy0 hy'0)]
      have h3 : L3 * (1 + a) * (‖y‖ + ‖y'‖ + ε) ≤ KJ * (‖y‖ + ‖y'‖ + ε) :=
        mul_le_mul_of_nonneg_right (by rw [hKJ]; nlinarith [pow_nonneg hBk0 3]) (by positivity)
      linarith
    exact mul_le_mul_of_nonneg_right hk hd0
  have hA₁ : Continuous (fun t => smDx F q0 (harm z ω t) + smDu F q0 Vh ω A0' t) :=
    ((LinearMap.continuous_of_finiteDimensional (smDx F q0)).comp
      (ForcedOrbit.continuous_harm z ω)).add hDu
  have h := orbit_boundary_floquet (by positivity : (0 : ℝ) < 2 * Real.pi / ω) hL hR hb hbp hK
    hρ'0 hε0'p hNc' hNp hN0' hNL' hpp hpd (continuous_smH2 F q0 Vh ω A0' z)
    (smH2_periodic F q0 Vh hω.ne' A0' z) hN₂ h₂yp h₂d hKJ0 hKD hDx hJc' hJL hA₁
    (continuous_smB2 F q0 Vh ω z) hJ₂ hω rfl hPQ hQP As hA0 hsr A0' (smA1 F q0 Vh z) hlink hs hbd
  simp only [smN_rhs] at h
  exact h

set_option maxHeartbeats 4000000 in
/-- **From the multipliers to the nonlinear forced orbit (level L0), for a `C³` field.** For every
`c`, for all small `ε > 0` and every `T`-periodic solution `y` of the driven system
`ẋ = F(x₀ + x, w₀ + εV̂ cos ωt) + εA₀'x` with `‖y‖ ≤ cε` (deviation coordinates): if every Floquet
multiplier of its variational equation `ξ̇ = smJ(t, y(t)) ξ` lies inside the unit circle, `y` is
locally exponentially stable; if one lies outside, `y` is unstable from every initial time
(`Periodic.exp_stable_of_floquet`, `Periodic.unstable_of_floquet` with the quadratic Taylor
remainder of the field on a tube around the orbit). -/
@[tmio T, powerlib_foundation] theorem smooth_orbit_L0 {F : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 3 F q0) (hF0 : F q0 = 0) (Vh : ℝ) {ω : ℝ}
    (hω : 0 < ω) (A0' : Matrix X X ℝ) (c : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) →
      (∀ t, ‖y t‖ ≤ c * ε) →
      (∀ t, HasDerivAt y (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t))) +
        ε • (A0' *ᵥ y t)) t) →
      ((∀ (μ : ℂ) (v : X → ℂ), v ≠ 0 →
          (Periodic.monodromy (fun t => smJ F q0 Vh ω A0' ε t (y t)) (2 * Real.pi / ω) 0).map
            (algebraMap ℝ ℂ) *ᵥ v = μ • v → ‖μ‖ < 1) →
        ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → X → ℝ),
          IsIntegralCurveOn x (fun t v => F (q0.1 + v, q0.2 + ε * (Vh * Real.cos (ω * t))) +
            ε • (A0' *ᵥ v)) (Ici s) →
          ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
            ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖) ∧
      (Periodic.FloquetUnstable (fun t => smJ F q0 Vh ω A0' ε t (y t)) (2 * Real.pi / ω) →
        ∀ s, ∃ η, 0 < η ∧ ∀ δ, 0 < δ → ∃ (x : ℝ → X → ℝ) (t : ℝ), s ≤ t ∧
          IsIntegralCurveOn x (fun t v => F (q0.1 + v, q0.2 + ε * (Vh * Real.cos (ω * t))) +
            ε • (A0' *ᵥ v)) (Icc s t) ∧ ‖x s - y s‖ < δ ∧ η ≤ ‖x t - y t‖) := by
  obtain ⟨-, ρ, ε0, -, -, -, hρ, hε0, -, -, -, -, -, -, hJc, -⟩ := smooth_estimates hF hF0 Vh ω A0'
  obtain ⟨R, KL, hR, hKL, hd, hl⟩ :=
    exists_lipschitz_ball (hF.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ ε0 ∧ c * ε ≤ ρ ∧ c * ε ≤ R / 3 ∧ ε * |Vh| ≤ R / 3 := by
    have hlim : Tendsto (fun ε : ℝ => (ε, c * ε, c * ε, ε * |Vh|)) (𝓝[>] 0)
        (𝓝 (0, 0, 0, 0)) := by
      have hcont : Continuous (fun ε : ℝ => (ε, c * ε, c * ε, ε * |Vh|)) := by fun_prop
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
  filter_upwards [hsmall, self_mem_nhdsWithin] with ε ⟨hε0', hcρ, hcR, hVR⟩ hεpos
  intro y hper hbd hode
  have hεpos' : 0 < ε := hεpos
  have hT : 0 < 2 * Real.pi / ω := by positivity
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hode t).continuousAt
  have hJcont : Continuous fun t => smJ F q0 Vh ω A0' ε t (y t) :=
    (hJc ε hεpos'.le hε0').comp_continuous (continuous_id.prodMk hyc) fun t =>
      Set.mk_mem_prod (Set.mem_univ _) (mem_closedBall_zero_iff.2 ((hbd t).trans hcρ))
  have hJp : Function.Periodic (fun t => smJ F q0 Vh ω A0' ε t (y t)) (2 * Real.pi / ω) := by
    intro t
    have e : ω * (t + 2 * Real.pi / ω) = ω * t + 2 * Real.pi := by field_simp
    simp only [smJ, hper t, e, Real.cos_add_two_pi]
  have hpt : ∀ t (v : X → ℝ), ‖v - y t‖ ≤ R / 3 →
      ‖((q0.1 + v, q0.2 + ε * (Vh * Real.cos (ω * t))) : (X → ℝ) × ℝ) - q0‖ ≤ 2 * R / 3 := by
    intro t v hv
    have h1 : ‖v‖ ≤ 2 * R / 3 := by
      have h2 : ‖v‖ ≤ ‖y t‖ + ‖v - y t‖ := by
        have := norm_add_le (y t) (v - y t); simpa using this
      linarith [hbd t]
    have h3 : |ε * (Vh * Real.cos (ω * t))| ≤ 2 * R / 3 := by
      rw [abs_mul, abs_mul, abs_of_pos hεpos']
      have := Real.abs_cos_le_one (ω * t)
      have : ε * (|Vh| * |Real.cos (ω * t)|) ≤ ε * |Vh| := by
        have := mul_le_mul_of_nonneg_left this (abs_nonneg Vh)
        nlinarith
      linarith
    rw [Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub, add_sub_cancel_left, Real.norm_eq_abs]
    exact max_le h1 h3
  have hGc : ContinuousOn (fun p : ℝ × (X → ℝ) =>
      F (q0.1 + p.2, q0.2 + ε * (Vh * Real.cos (ω * p.1))) + ε • (A0' *ᵥ p.2))
      {p | ‖p.2 - y p.1‖ ≤ R / 3} := by
    intro p hp
    have hφ : Continuous fun p : ℝ × (X → ℝ) =>
        ((q0.1 + p.2, q0.2 + ε * (Vh * Real.cos (ω * p.1))) : (X → ℝ) × ℝ) := by fun_prop
    have hmem : ((q0.1 + p.2, q0.2 + ε * (Vh * Real.cos (ω * p.1))) : (X → ℝ) × ℝ) ∈
        closedBall q0 R := by
      rw [mem_closedBall, dist_eq_norm]; have := hpt p.1 p.2 hp; linarith
    refine ContinuousWithinAt.add ?_ ?_
    · have hca := ContinuousAt.comp (g := F) (x := p) (f := fun p : ℝ × (X → ℝ) =>
        ((q0.1 + p.2, q0.2 + ε * (Vh * Real.cos (ω * p.1))) : (X → ℝ) × ℝ))
        (hd _ hmem).continuousAt hφ.continuousAt
      exact hca.continuousWithinAt
    · exact (by fun_prop : Continuous fun p : ℝ × (X → ℝ) => ε • (A0' *ᵥ p.2)).continuousWithinAt
  have hRem : ∀ t (e : X → ℝ), ‖e‖ ≤ R / 3 →
      ‖(F (q0.1 + (y t + e), q0.2 + ε * (Vh * Real.cos (ω * t))) + ε • (A0' *ᵥ (y t + e))) -
        (F (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t))) + ε • (A0' *ᵥ y t)) -
        smJ F q0 Vh ω A0' ε t (y t) *ᵥ e‖ ≤ KL * ‖e‖ ^ 2 := by
    intro t e he
    set a : (X → ℝ) × ℝ := (q0.1 + y t, q0.2 + ε * (Vh * Real.cos (ω * t))) with had
    have ha : ‖a - q0‖ ≤ 2 * R / 3 := hpt t (y t) (by simp; positivity)
    have hsub : closedBall a ‖((e, (0 : ℝ)) : (X → ℝ) × ℝ)‖ ⊆ closedBall q0 R := by
      intro q hq
      rw [mem_closedBall, dist_eq_norm] at hq ⊢
      rw [norm_prod_zero] at hq
      have := norm_sub_le_norm_sub_add_norm_sub q a q0
      linarith
    have hq := quad_remainder hKL hd hl hsub
    rw [norm_prod_zero] at hq
    have e1 : ((q0.1 + (y t + e), q0.2 + ε * (Vh * Real.cos (ω * t))) : (X → ℝ) × ℝ) =
        a + (e, 0) := by
      rw [had]; ext <;> simp [add_assoc]
    have e2 : smJ F q0 Vh ω A0' ε t (y t) *ᵥ e = fderiv ℝ F a (e, 0) + ε • (A0' *ᵥ e) := by
      rw [smJ, Matrix.add_mulVec, Matrix.smul_mulVec, matX_mulVec]
    rw [e1, e2, Matrix.mulVec_add, smul_add]
    convert hq using 2
    abel
  refine ⟨fun hεfl => ?_, fun hun s => ?_⟩
  · have hsr' := spectralRadius_lt_one_of_eig _ hεfl
    exact Periodic.exp_stable_of_floquet hT hJcont hJp hsr' hode (by positivity) hKL hGc hRem
  · set KF : ℝ := ‖fderiv ℝ F q0‖ + KL * R + ε * ‖A0'‖ with hKFdef
    have hKF : 0 ≤ KF := by positivity
    have hLip : ∀ t, LipschitzOnWith (Real.toNNReal KF)
        (fun v => F (q0.1 + v, q0.2 + ε * (Vh * Real.cos (ω * t))) + ε • (A0' *ᵥ v))
        (closedBall (y t) (R / 3)) := by
      intro t
      refine LipschitzOnWith.of_dist_le_mul fun v1 hv1 v2 hv2 => ?_
      rw [Real.coe_toNNReal _ hKF, dist_eq_norm, dist_eq_norm]
      rw [mem_closedBall, dist_eq_norm] at hv1 hv2
      set q1 : (X → ℝ) × ℝ := (q0.1 + v1, q0.2 + ε * (Vh * Real.cos (ω * t))) with hq1d
      set q2 : (X → ℝ) × ℝ := (q0.1 + v2, q0.2 + ε * (Vh * Real.cos (ω * t))) with hq2d
      have hq1 : q1 ∈ closedBall q0 R := by
        rw [mem_closedBall, dist_eq_norm]; have := hpt t v1 hv1; linarith
      have hq2 : q2 ∈ closedBall q0 R := by
        rw [mem_closedBall, dist_eq_norm]; have := hpt t v2 hv2; linarith
      have hdiff : q1 - q2 = (v1 - v2, 0) := by
        rw [hq1d, hq2d]; ext <;> simp
      have hts := taylor_sub (G := F) (q0 := q0) (r := R) (L := KL) hKL hd
        (fun q hq => hl q hq q0 (mem_closedBall_self hR.le)) le_rfl hq1 hq2
      rw [hdiff, norm_prod_zero] at hts
      have hlin : ‖fderiv ℝ F q0 (v1 - v2, 0)‖ ≤ ‖fderiv ℝ F q0‖ * ‖v1 - v2‖ := by
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        rw [norm_prod_zero]
      have hA : ‖ε • (A0' *ᵥ v1) - ε • (A0' *ᵥ v2)‖ ≤ ε * ‖A0'‖ * ‖v1 - v2‖ := by
        rw [← smul_sub, ← Matrix.mulVec_sub, norm_smul, Real.norm_of_nonneg hεpos'.le, mul_assoc]
        exact mul_le_mul_of_nonneg_left (Matrix.linfty_opNorm_mulVec _ _) hεpos'.le
      calc ‖(F q1 + ε • (A0' *ᵥ v1)) - (F q2 + ε • (A0' *ᵥ v2))‖ =
            ‖(F q1 - F q2 - fderiv ℝ F q0 (v1 - v2, 0)) + fderiv ℝ F q0 (v1 - v2, 0) +
              (ε • (A0' *ᵥ v1) - ε • (A0' *ᵥ v2))‖ := by congr 1; abel
        _ ≤ KL * R * ‖v1 - v2‖ + ‖fderiv ℝ F q0‖ * ‖v1 - v2‖ + ε * ‖A0'‖ * ‖v1 - v2‖ :=
            (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hts hlin)) hA)
        _ = KF * ‖v1 - v2‖ := by rw [hKFdef]; ring
    exact Periodic.unstable_of_floquet hT hJcont hJp hun hode (by positivity) hKL hGc hLip hRem s

/-- **The nonlinear forced orbit of a `C⁴` field on the first-order boundary, level L0.** Under the
hypotheses of `smooth_orbit_boundary_floquet` (on the boundary `|λ₁| = |g/2|`, `Re λ₁ < 0`, with
`Δ = orbitMixed P Q A_s ω A₀' A₁ A₂`, `A₂ = D_x(∂ₓF)(q₀)[y₂] + ½ D²(∂ₓF)(q₀)[k, k]`): if `Δ > 0`,
for all small `ε > 0` the forced periodic orbit `y` exists and is locally exponentially stable for
the nonlinear driven system; if `Δ < 0`, it exists and is unstable from every initial time. -/
@[tmio T, powerlib_foundation] theorem smooth_orbit_boundary {Y : Type*} [Fintype Y]
    [DecidableEq Y] {F : (X → ℝ) × ℝ → X → ℝ} {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 4 F q0)
    (hF0 : F q0 = 0) {Vh ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matX F q0 * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z : X → ℂ}
    (hz : ((ω : ℂ) * I) • z - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ z =
      (Vh : ℂ) • fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ))
    (A0' : Matrix X X ℝ) {y₂ : ℝ → X → ℝ} (h₂yp : ∀ t, y₂ (t + 2 * Real.pi / ω) = y₂ t)
    (h₂d : ∀ t, HasDerivAt y₂ (matX F q0 *ᵥ y₂ t + smH2 F q0 Vh ω A0' z t) t)
    (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hbd : ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2 =
      ‖physLeft Q ⬝ᵥ (smA1 F q0 Vh z *ᵥ star (physRight P)) / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧
      (0 < orbitMixed P Q As ω A0' (smA1 F q0 Vh z)
          (fun t => smDx F q0 (y₂ t) + smB2 F q0 Vh ω z t) →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧
          (∀ t, ‖y t‖ ≤ c * ε) ∧ (∀ t, HasDerivAt y (F (q0.1 + y t,
            q0.2 + ε * (Vh * Real.cos (ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
          ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → X → ℝ),
            IsIntegralCurveOn x (fun t v => F (q0.1 + v, q0.2 + ε * (Vh * Real.cos (ω * t))) +
              ε • (A0' *ᵥ v)) (Ici s) →
            ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
              ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖) ∧
      (orbitMixed P Q As ω A0' (smA1 F q0 Vh z)
          (fun t => smDx F q0 (y₂ t) + smB2 F q0 Vh ω z t) < 0 →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧
          (∀ t, ‖y t‖ ≤ c * ε) ∧ (∀ t, HasDerivAt y (F (q0.1 + y t,
            q0.2 + ε * (Vh * Real.cos (ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
          ∀ s, ∃ η, 0 < η ∧ ∀ δ, 0 < δ → ∃ (x : ℝ → X → ℝ) (t : ℝ), s ≤ t ∧
            IsIntegralCurveOn x (fun t v => F (q0.1 + v, q0.2 + ε * (Vh * Real.cos (ω * t))) +
              ε • (A0' *ᵥ v)) (Icc s t) ∧ ‖x s - y s‖ < δ ∧ η ≤ ‖x t - y t‖) := by
  obtain ⟨c, hc, hex, hst, hun⟩ := smooth_orbit_boundary_floquet hF hF0 hω hPQ hQP As hA0 hsr hz
    A0' h₂yp h₂d hs hbd
  have hL0 := smooth_orbit_L0 (hF.of_le (by norm_num)) hF0 Vh hω A0' c
  refine ⟨c, hc, fun hmix => ?_, fun hmix => ?_⟩
  · filter_upwards [hex, hst hmix, hL0] with ε hεex hεst hεL0
    obtain ⟨y, hper, hbd', hode⟩ := hεex
    exact ⟨y, hper, hbd', hode, (hεL0 y hper hbd' hode).1 (hεst y hper hbd' hode)⟩
  · filter_upwards [hex, hun hmix, hL0] with ε hεex hεun hεL0
    obtain ⟨y, hper, hbd', hode⟩ := hεex
    exact ⟨y, hper, hbd', hode, (hεL0 y hper hbd' hode).2 (hεun y hper hbd' hode)⟩

/-- The second-order forced response exists and is unique: with `(I − e^{TA})⁻¹` (`A = ∂ₓF(q₀)`,
`T = 2π/ω`) the `T`-periodic solutions of `ẏ₂ = A y₂ + h₂` are exactly the Green function
`y₂ = G h₂ = (I − e^{TA})⁻¹ ∫_{t−T}^{t} e^{(t−s)A} h₂(s) ds` (`ForcedOrbit.green`). -/
@[tmio T, powerlib_foundation] theorem second_response {F : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} {Minv : Matrix X X ℝ} {Vh ω : ℝ} (hω : 0 < ω)
    (hL : Minv * (1 - expS (matX F q0) (2 * Real.pi / ω)) = 1)
    (hR : (1 - expS (matX F q0) (2 * Real.pi / ω)) * Minv = 1) (A0' : Matrix X X ℝ)
    (z : X → ℂ) :
    (∀ t, ForcedOrbit.green (matX F q0) Minv (2 * Real.pi / ω) (smH2 F q0 Vh ω A0' z)
        (t + 2 * Real.pi / ω) =
      ForcedOrbit.green (matX F q0) Minv (2 * Real.pi / ω) (smH2 F q0 Vh ω A0' z) t) ∧
    (∀ t, HasDerivAt (ForcedOrbit.green (matX F q0) Minv (2 * Real.pi / ω) (smH2 F q0 Vh ω A0' z))
      (matX F q0 *ᵥ ForcedOrbit.green (matX F q0) Minv (2 * Real.pi / ω) (smH2 F q0 Vh ω A0' z) t +
        smH2 F q0 Vh ω A0' z t) t) ∧
    ∀ y₂ : ℝ → X → ℝ, (∀ t, y₂ (t + 2 * Real.pi / ω) = y₂ t) →
      (∀ t, HasDerivAt y₂ (matX F q0 *ᵥ y₂ t + smH2 F q0 Vh ω A0' z t) t) →
      y₂ = ForcedOrbit.green (matX F q0) Minv (2 * Real.pi / ω) (smH2 F q0 Vh ω A0' z) := by
  have hc := continuous_smH2 F q0 Vh ω A0' z
  have hp := smH2_periodic F q0 Vh hω.ne' A0' z
  refine ⟨ForcedOrbit.green_periodic _ _ _ hc hp, ForcedOrbit.green_hasDerivAt hL hR hc hp,
    fun y₂ hy hd => funext fun t => ForcedOrbit.periodic_eq_green hL hR hc hp hd hy t⟩

/-! ### The second-order response by harmonic balance -/

/-- The cosine part `(Re z, V̂)` of the first-order displacement `k(t)`. -/
def kapR (z : X → ℂ) (Vh : ℝ) : (X → ℝ) × ℝ := (fun i => (z i).re, Vh)

/-- The sine part `(Im z, 0)` of the first-order displacement `k(t)`. -/
def kapI (z : X → ℂ) : (X → ℝ) × ℝ := (fun i => (z i).im, 0)

/-- The constant part of `½ D²F(q₀)[k, k]`: `¼ (D²F[κᵣ, κᵣ] + D²F[κᵢ, κᵢ])`. -/
def smH0 (F : (X → ℝ) × ℝ → X → ℝ) (q0 : (X → ℝ) × ℝ) (Vh : ℝ) (z : X → ℂ) : X → ℝ :=
  (1 / 4 : ℝ) • (fderiv ℝ (fderiv ℝ F) q0 (kapR z Vh) (kapR z Vh) +
    fderiv ℝ (fderiv ℝ F) q0 (kapI z) (kapI z))

/-- The second-harmonic amplitude of `½ D²F(q₀)[k, k] = h₀ + Re{h₂ e^{2jωt}}`:
`h₂ = ¼ (D²F[κᵣ, κᵣ] − D²F[κᵢ, κᵢ]) + ¼ j (D²F[κᵣ, κᵢ] + D²F[κᵢ, κᵣ])`. -/
def smH2c (F : (X → ℝ) × ℝ → X → ℝ) (q0 : (X → ℝ) × ℝ) (Vh : ℝ) (z : X → ℂ) : X → ℂ :=
  fun i => ⟨(1 / 4 : ℝ) * (fderiv ℝ (fderiv ℝ F) q0 (kapR z Vh) (kapR z Vh) i -
      fderiv ℝ (fderiv ℝ F) q0 (kapI z) (kapI z) i),
    (1 / 4 : ℝ) * (fderiv ℝ (fderiv ℝ F) q0 (kapR z Vh) (kapI z) i +
      fderiv ℝ (fderiv ℝ F) q0 (kapI z) (kapR z Vh) i)⟩

omit [Fintype X] [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem smK_eq (z : X → ℂ) (Vh ω t : ℝ) :
    smK z Vh ω t = Real.cos (ω * t) • kapR z Vh - Real.sin (ω * t) • kapI z := by
  ext i <;> simp [smK, kapR, kapI, harm] <;> ring

omit [DecidableEq X] in
/-- **The second-order forcing in harmonics:** `h₂(t) = h₀ + Re{h₂ᶜ e^{2jωt}} + Re{A₀' z e^{jωt}}`
— the quadratic term of the field contributes the frequencies `0` and `2ω`, the state
perturbation acting on the first-order response the frequency `ω`. -/
@[tmio T, powerlib_foundation] theorem smH2_harmonic (F : (X → ℝ) × ℝ → X → ℝ)
    (q0 : (X → ℝ) × ℝ) (Vh ω : ℝ) (A0' : Matrix X X ℝ) (z : X → ℂ) (t : ℝ) :
    smH2 F q0 Vh ω A0' z t = smH0 F q0 Vh z + harm (smH2c F q0 Vh z) (2 * ω) t +
      harm (A0'.map (algebraMap ℝ ℂ) *ᵥ z) ω t := by
  set D2 := fderiv ℝ (fderiv ℝ F) q0 with hD2
  have hk : D2 (smK z Vh ω t) (smK z Vh ω t) =
      (Real.cos (ω * t) ^ 2) • D2 (kapR z Vh) (kapR z Vh) -
        (Real.cos (ω * t) * Real.sin (ω * t)) • (D2 (kapR z Vh) (kapI z) +
          D2 (kapI z) (kapR z Vh)) + (Real.sin (ω * t) ^ 2) • D2 (kapI z) (kapI z) := by
    rw [smK_eq]
    simp only [map_sub, map_smul, _root_.sub_apply, _root_.smul_apply, smul_sub, smul_smul]
    module
  have hc2 : Real.cos (2 * ω * t) = Real.cos (ω * t) ^ 2 - Real.sin (ω * t) ^ 2 := by
    rw [show 2 * ω * t = 2 * (ω * t) by ring, Real.cos_two_mul, ← Real.cos_sq_add_sin_sq (ω * t)]
    ring
  have hs2 : Real.sin (2 * ω * t) = 2 * Real.sin (ω * t) * Real.cos (ω * t) := by
    rw [show 2 * ω * t = 2 * (ω * t) by ring, Real.sin_two_mul]
  have hsc := Real.sin_sq_add_cos_sq (ω * t)
  have hA : A0' *ᵥ harm z ω t = harm (A0'.map (algebraMap ℝ ℂ) *ᵥ z) ω t := by
    funext i
    simp only [harm, Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.re_sum, Complex.im_sum,
      Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
    ring
  rw [smH2, hk, hA]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, smH0, harm, smH2c, hc2, hs2]
  linear_combination (1 / 4 * (D2 (kapR z Vh) (kapR z Vh) i + D2 (kapI z) (kapI z) i)) * hsc

/-- **The second-order forced response by harmonic balance.** If `w₀`, `w₁`, `w₂` solve
`A w₀ + h₀ = 0`, `(jωI − A) w₁ = A₀' z`, `(2jωI − A) w₂ = h₂ᶜ` (`A = ∂ₓF(q₀)`), then
`y₂(t) = w₀ + Re{w₁ e^{jωt}} + Re{w₂ e^{2jωt}}` is a `T`-periodic solution of
`ẏ₂ = A y₂ + h₂` (`T = 2π/ω`), hence the second-order response of `second_response`. -/
@[tmio T, powerlib_foundation] theorem second_response_harmonic {F : (X → ℝ) × ℝ → X → ℝ}
    {q0 : (X → ℝ) × ℝ} {Vh ω : ℝ} (hω : ω ≠ 0) (A0' : Matrix X X ℝ) (z : X → ℂ)
    {w₀ : X → ℝ} {w₁ w₂ : X → ℂ} (h₀ : matX F q0 *ᵥ w₀ + smH0 F q0 Vh z = 0)
    (h₁ : ((ω : ℂ) * I) • w₁ - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ w₁ =
      A0'.map (algebraMap ℝ ℂ) *ᵥ z)
    (h₂ : (((2 * ω : ℝ) : ℂ) * I) • w₂ - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ w₂ =
      smH2c F q0 Vh z) :
    (∀ t, w₀ + harm w₁ ω (t + 2 * Real.pi / ω) + harm w₂ (2 * ω) (t + 2 * Real.pi / ω) =
      w₀ + harm w₁ ω t + harm w₂ (2 * ω) t) ∧
    ∀ t, HasDerivAt (fun t => w₀ + harm w₁ ω t + harm w₂ (2 * ω) t)
      (matX F q0 *ᵥ (w₀ + harm w₁ ω t + harm w₂ (2 * ω) t) + smH2 F q0 Vh ω A0' z t) t := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · have e2 : 2 * ω * (t + 2 * Real.pi / ω) = 2 * ω * t + 2 * Real.pi + 2 * Real.pi := by
      field_simp; ring
    rw [ForcedOrbit.harm_periodic w₁ hω]
    congr 1
    funext i
    simp only [harm, e2, Real.cos_add_two_pi, Real.sin_add_two_pi]
  · have d1 := ForcedOrbit.harm_hasDerivAt h₁ t
    have d2 := ForcedOrbit.harm_hasDerivAt h₂ t
    have h := ((hasDerivAt_const t w₀).add d1).add d2
    refine h.congr_deriv ?_
    rw [smH2_harmonic, Matrix.mulVec_add, Matrix.mulVec_add, ← sub_eq_zero]
    have h₀' : matX F q0 *ᵥ w₀ = -smH0 F q0 Vh z := eq_neg_of_add_eq_zero_left h₀
    rw [h₀']
    abel

/-- **The forced operating point at the drive threshold `|V̂||g₁| = 2|λ₁|`, decided at second
order** (levels L1 and L0). `z₁` is the forced response per unit drive amplitude, `g₁ = u A₁(1) r̄`
the pump per unit amplitude, `λ₁ = u A₀' r` with `Re λ₁ < 0`; at the threshold
`|V̂| |g₁| = 2 |λ₁|` left open by `Periodic.Levels.orbit_stable_below_threshold` /
`orbit_unstable_above_threshold` (`Boundary.forced_threshold_boundary_iff`), with the second-order
response `y₂` of the drive amplitude `V̂` and `Δ = orbitMixed P Q A_s ω A₀' A₁(V̂) A₂`:
`Δ > 0` gives a locally exponentially stable and `Δ < 0` an unstable forced orbit, for all small
`ε > 0`. -/
@[tmio T, powerlib_foundation] theorem smooth_orbit_at_threshold {Y : Type*} [Fintype Y]
    [DecidableEq Y] {F : (X → ℝ) × ℝ → X → ℝ} {q0 : (X → ℝ) × ℝ} (hF : ContDiffAt ℝ 4 F q0)
    (hF0 : F q0 = 0) {Vh ω : ℝ} (hω : 0 < ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (As : Matrix Y Y ℝ) (hA0 : Q * matX F q0 * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1) {z₁ : X → ℂ}
    (hz₁ : ((ω : ℂ) * I) • z₁ - (matX F q0).map (algebraMap ℝ ℂ) *ᵥ z₁ =
      fun i => ((fderiv ℝ F q0 (0, 1) i : ℝ) : ℂ))
    (A0' : Matrix X X ℝ) {y₂ : ℝ → X → ℝ} (h₂yp : ∀ t, y₂ (t + 2 * Real.pi / ω) = y₂ t)
    (h₂d : ∀ t, HasDerivAt y₂ (matX F q0 *ᵥ y₂ t + smH2 F q0 Vh ω A0' ((Vh : ℂ) • z₁) t) t)
    (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hdrive : |Vh| * ‖physLeft Q ⬝ᵥ (smA1 F q0 1 z₁ *ᵥ star (physRight P))‖ =
      2 * ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖) :
    ∃ c, 0 ≤ c ∧
      (0 < orbitMixed P Q As ω A0' (smA1 F q0 Vh ((Vh : ℂ) • z₁))
          (fun t => smDx F q0 (y₂ t) + smB2 F q0 Vh ω ((Vh : ℂ) • z₁) t) →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧
          (∀ t, ‖y t‖ ≤ c * ε) ∧ (∀ t, HasDerivAt y (F (q0.1 + y t,
            q0.2 + ε * (Vh * Real.cos (ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
          ∃ δ K β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ (s : ℝ) (x : ℝ → X → ℝ),
            IsIntegralCurveOn x (fun t v => F (q0.1 + v, q0.2 + ε * (Vh * Real.cos (ω * t))) +
              ε • (A0' *ᵥ v)) (Ici s) →
            ‖x s - y s‖ ≤ δ → ∀ t, s ≤ t →
              ‖x t - y t‖ ≤ K * Real.exp (-(β * (t - s))) * ‖x s - y s‖) ∧
      (orbitMixed P Q As ω A0' (smA1 F q0 Vh ((Vh : ℂ) • z₁))
          (fun t => smDx F q0 (y₂ t) + smB2 F q0 Vh ω ((Vh : ℂ) • z₁) t) < 0 →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ, (∀ t, y (t + 2 * Real.pi / ω) = y t) ∧
          (∀ t, ‖y t‖ ≤ c * ε) ∧ (∀ t, HasDerivAt y (F (q0.1 + y t,
            q0.2 + ε * (Vh * Real.cos (ω * t))) + ε • (A0' *ᵥ y t)) t) ∧
          ∀ s, ∃ η, 0 < η ∧ ∀ δ, 0 < δ → ∃ (x : ℝ → X → ℝ) (t : ℝ), s ≤ t ∧
            IsIntegralCurveOn x (fun t v => F (q0.1 + v, q0.2 + ε * (Vh * Real.cos (ω * t))) +
              ε • (A0' *ᵥ v)) (Icc s t) ∧ ‖x s - y s‖ < δ ∧ η ≤ ‖x t - y t‖) := by
  have hbd : ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2 =
      ‖physLeft Q ⬝ᵥ (smA1 F q0 Vh ((Vh : ℂ) • z₁) *ᵥ star (physRight P)) / 2‖ ^ 2 := by
    rw [Periodic.Levels.pump_drive]
    exact ((Boundary.forced_threshold_boundary_iff _ _ Vh).mpr hdrive).symm
  exact smooth_orbit_boundary hF hF0 hω hPQ hQP As hA0 hsr
    (Periodic.Levels.forced_response_drive hz₁ Vh) A0' h₂yp h₂d hs hbd

end Smooth

end powerlib.ParametricResonance.ForcedOrbitSecond
