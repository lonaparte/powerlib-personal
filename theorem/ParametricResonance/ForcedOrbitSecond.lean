import theorem.ParametricResonance.BlockRemainderSecond
import theorem.ParametricResonance.ForcedOrbitFloquet

/-! # The forced orbit to second order and its variational equation on the first-order boundary

`ForcedOrbit.forced_orbit` gives the forced periodic orbit of `ẏ = A y + ε b(t) + N_ε(t, y)` with
`‖y − ε y₁‖ ≤ C ε²`, and `ForcedOrbit.orbit_variational` its variational matrix
`A + ε(D_x y₁ + D_u) + ε² R_ε(t)` with `R_ε` only bounded; with that, the first-order criterion
decides every point off the boundary `|g/2| = |λ₁|`, and nothing on it
(`BlockAveraging.averagingR_stable`, `RemainderSecond.averagingR_bounded_undecided`). This file
carries the orbit and its variational matrix one order further and decides the boundary.

* Second-order orbit: if the nonlinearity along the first-order orbit has a second-order
  coefficient, `‖N_ε(t, ε y₁(t)) − ε² h₂(t)‖ ≤ K₂ ε³`, the orbit is
  `y = ε y₁ + ε² y₂ + O(ε³)` with `y₂` the periodic solution of `ẏ₂ = A y₂ + h₂`
  (`orbit_expansion_second`; the error is the periodic Green operator applied to
  `N_ε(·, y) − ε² h₂ = O(ε³)`). For a smooth field `h₂ = ½ D²F(q₀)[k, k] + A₀' y₁`,
  `k = (y₁, input)`, has the frequencies `0` and `2ω` from the quadratic term (and `ω` from
  `A₀' y₁`).
* Second-order variational matrix: if the Jacobian field satisfies
  `‖J_ε(t, y) − J_ε(t, y') − D_x(y − y')‖ ≤ K_J(‖y‖ + ‖y'‖ + ε)‖y − y'‖` and
  `‖J_ε(t, ε y₁) − A − ε A₁ − ε² B₂‖ ≤ K_J ε³`, then along the orbit
  `J_ε(t, y(t)) = A + ε A₁(t) + ε² A₂(t) + ε³ R₃,ε(t)`, `A₂ = D_x y₂ + B₂`, with `R₃,ε` continuous
  and uniformly bounded (`orbit_variational_second`). For a smooth field
  `A₂ = D_x(∂ₓF)(q₀)[y₂] + ½ D²(∂ₓF)(q₀)[k, k]`: the second-order forced response acting through
  the curvature, plus the third derivatives of the field on the first-order response and the
  input.
* The boundary: in modal coordinates this is `BlockAveraging.physJR` with the expanded remainder
  `A₂ + ε R₃`, so `RemainderSecond.physicalR2_boundary` decides it by the sign of
  `orbitMixed P Q A_s ω A₀' A₁ᶜ A₂ = mixedDet(M, N_eff + ∫₀ᵀ R(−ωt/2)(Q A₂ P)₁₁ R(ωt/2) dt)`
  (`orbit_boundary_floquet`, level L1): the first-order data `M`, the effective second-order matrix
  `N_eff` of the modal standard form (its second Picard term and the coupling through the stable
  block, `E = e^{TA_s}`) and the critical block of `A₂` averaged in the rotating frame.

Scope.
* The forced system of `ForcedOrbit.forced_orbit` on a finite state space (sup norms): constant
  `A` with `(I − e^{TA})⁻¹`, continuous `T`-periodic `b`, `N` with the bounds of `forced_orbit`;
  the second-order data `h₂` (continuous, `T`-periodic), `y₂` (a `T`-periodic solution of
  `ẏ₂ = A y₂ + h₂`, unique by `ForcedOrbit.periodic_eq_green`); a matrix field `J_ε(t, y)` with the
  stated bounds (for a concrete model the Jacobian of the field). Statements for all small
  `ε > 0`.
* The boundary statement needs real modal coordinates of `A` with the pair `±jω/2` and a stable
  block with `ρ(e^{TA_s}) < 1` (`T = 2π/ω`), and the first-order part
  `A₁ = A₀' + Re{A₁ᶜ e^{jωt}}` on the boundary `|λ₁| = |g/2|`, `Re λ₁ < 0`.
* The conclusions are Floquet statements (level L1); for a smooth field the nonlinear orbit
  (level L0) follows in `theorem/ParametricResonance/SmoothForcedOrbitSecond.lean`.

Source: the wave-6 question of this library (the `O(ε²)` part of the variational matrix of the
`n`-state forced orbit, left open in `theorem/ParametricResonance/BoundaryUndecided.lean` and
`theorem/Periodic/LevelsNonlinear.lean`); second-order perturbation of a forced periodic orbit by
the periodic Green operator (variation of constants) and second-order averaging of its
variational equation (Nayfeh–Mook, *Nonlinear Oscillations*, Ch. 5; Yakubovich–Starzhinskii,
*Linear Differential Equations with Periodic Coefficients*); `ForcedOrbit.forced_orbit`,
`ForcedOrbit.periodic_eq_green`, `RemainderSecond.physicalR2_boundary`.

Results.
* `orbit_expansion_second` — `‖y − ε y₁ − ε² y₂‖ ≤ C₃ ε³` for the forced orbit.
* `jacRem3`, `jacRem3_eq`, `orbit_variational_second` — the variational matrix along the orbit
  `A + ε A₁ + ε² (D_x y₂ + B₂) + ε³ R₃,ε` with `R₃,ε` continuous and bounded.
* `orbitMixed`, `orbit_boundary_floquet` — the forced orbit on the first-order boundary decided by
  the sign of `orbitMixed`.

Corrections.
None: an extension (the boundary `|V̂||g₁| = 2|λ₁|` left undecided by
`Periodic.Levels.orbit_stable_below_threshold` / `orbit_unstable_above_threshold`).

Family and connection conclusions.
None: static evidence on periodically forced ODEs (forced orbit, Floquet multipliers).
-/

noncomputable section
namespace powerlib.ParametricResonance.ForcedOrbitSecond

open Matrix Complex Set Filter Topology
open scoped Matrix.Norms.Operator
open ForcedOrbit (green green_bound periodic_eq_green forced_orbit exists_bound_of_periodic_vec)
open BlockAveraging (expS modX physJR physLeft physRight FzcB)
open BlockBoundary (effSecond)
open RemainderSecond (critIntegral)
open Boundary (mixedDet)
open TwoToOne (base)

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## The forced orbit to second order -/

set_option maxHeartbeats 1000000 in
/-- **The forced orbit to second order.** Under the hypotheses of `ForcedOrbit.forced_orbit`
(`ẏ = A y + ε b(t) + N_ε(t, y)`, `I − e^{TA}` invertible, `N` quadratically small), let `y₁` be the
periodic solution of `ẏ₁ = A y₁ + b`, let the nonlinearity along the first-order orbit have the
second-order coefficient `h₂`: `‖N_ε(t, ε y₁(t)) − ε² h₂(t)‖ ≤ K₂ ε³`, and let `y₂` be the periodic
solution of `ẏ₂ = A y₂ + h₂` (the second-order forced response). Then for all small `ε > 0` the
forced orbit exists (unique in the ball of radius `cε`) and every such periodic solution satisfies
`‖y − ε y₁ − ε² y₂‖ ≤ C₃ ε³`. -/
@[tmio T, powerlib_foundation] theorem orbit_expansion_second {A Minv : Matrix X X ℝ} {T : ℝ}
    (hT : 0 < T) (hL : Minv * (1 - expS A T) = 1) (hR : (1 - expS A T) * Minv = 1)
    {b : ℝ → X → ℝ} (hb : Continuous b) (hbp : ∀ t, b (t + T) = b t)
    {N : ℝ → ℝ → (X → ℝ) → X → ℝ} {K ρ ε0 : ℝ} (hK : 0 ≤ K) (hρ : 0 < ρ) (hε0 : 0 < ε0)
    (hNc : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × (X → ℝ) => N ε p.1 p.2)
      (Set.univ ×ˢ Metric.closedBall 0 ρ))
    (hNp : ∀ ε t y, N ε (t + T) y = N ε t y)
    (hN0 : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t, ‖N ε t 0‖ ≤ K * ε ^ 2)
    (hNL : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y1 y2, ‖y1‖ ≤ ρ → ‖y2‖ ≤ ρ →
      ‖N ε t y1 - N ε t y2‖ ≤ K * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖)
    {y₁ : ℝ → X → ℝ} (h₁p : ∀ t, y₁ (t + T) = y₁ t)
    (h₁d : ∀ t, HasDerivAt y₁ (A *ᵥ y₁ t + b t) t)
    {h₂ : ℝ → X → ℝ} (h₂c : Continuous h₂) (h₂p : ∀ t, h₂ (t + T) = h₂ t) {K₂ : ℝ}
    (hN₂ : ∀ ε, 0 < ε → ε ≤ ε0 → ∀ t, ‖N ε t (ε • y₁ t) - ε ^ 2 • h₂ t‖ ≤ K₂ * ε ^ 3)
    {y₂ : ℝ → X → ℝ} (h₂yp : ∀ t, y₂ (t + T) = y₂ t)
    (h₂d : ∀ t, HasDerivAt y₂ (A *ᵥ y₂ t + h₂ t) t) :
    ∃ c C₃ ε1, 0 ≤ c ∧ 0 ≤ C₃ ∧ 0 < ε1 ∧ ε1 ≤ ε0 ∧ c * ε1 ≤ ρ ∧ ∀ ε, 0 < ε → ε ≤ ε1 →
      (∃ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) ∧
      (∀ y1 y2 : ℝ → X → ℝ, (∀ t, y1 (t + T) = y1 t) → (∀ t, ‖y1 t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y1 (A *ᵥ y1 t + (ε • b t + N ε t (y1 t))) t) →
        (∀ t, y2 (t + T) = y2 t) → (∀ t, ‖y2 t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y2 (A *ᵥ y2 t + (ε • b t + N ε t (y2 t))) t) → y1 = y2) ∧
      ∀ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
        (∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) →
        ∀ t, ‖y t - ε • y₁ t - ε ^ 2 • y₂ t‖ ≤ C₃ * ε ^ 3 := by
  obtain ⟨c, C, ε1, hc, hC, hε1, hε1e, hcρ, hmain⟩ := forced_orbit hT hL hR hb hbp hK hρ hε0
    hNc hNp hN0 hNL
  obtain ⟨CL, hCL0, hCL⟩ := green_bound A Minv hT.le
  have hy₁c : Continuous y₁ := continuous_iff_continuousAt.2 fun t => (h₁d t).continuousAt
  obtain ⟨B0, hB0⟩ := exists_bound_of_periodic_vec hy₁c h₁p hT
  set B1 := max B0 0 with hB1
  have hB1b : ∀ t, ‖y₁ t‖ ≤ B1 := fun t => (hB0 t).trans (le_max_left _ _)
  have hB10 : 0 ≤ B1 := le_max_right _ _
  set ε2 := min ε1 (ρ / (B1 + 1)) with hε2
  have hε2p : 0 < ε2 := lt_min hε1 (by positivity)
  have hε2a : ε2 ≤ ε1 := min_le_left _ _
  have hε2b : ε2 ≤ ρ / (B1 + 1) := min_le_right _ _
  set K' := K * (c + B1 + 1) * C + K₂ with hK'
  have hK₂ : 0 ≤ K₂ := by
    have h := hN₂ (min ε0 1) (lt_min hε0 one_pos) (min_le_left _ _) 0
    have hp : 0 < (min ε0 1) ^ 3 := by have := lt_min hε0 one_pos; positivity
    by_contra hneg
    replace hneg := not_le.mp hneg
    have : K₂ * (min ε0 1) ^ 3 < 0 := mul_neg_of_neg_of_pos hneg hp
    linarith [norm_nonneg (N (min ε0 1) 0 (min ε0 1 • y₁ 0) - min ε0 1 ^ 2 • h₂ 0)]
  refine ⟨c, CL * K', ε2, hc, by positivity, hε2p, hε2a.trans hε1e,
    (mul_le_mul_of_nonneg_left hε2a hc).trans hcρ, fun ε hε hεe => ?_⟩
  have hεe1 : ε ≤ ε1 := hεe.trans hε2a
  obtain ⟨hex, huniq, hexp⟩ := hmain ε hε hεe1
  refine ⟨hex, huniq, fun y hyp hyb hyd => ?_⟩
  have hε0' : ε ≤ ε0 := hεe1.trans hε1e
  have hcρε : c * ε ≤ ρ := (mul_le_mul_of_nonneg_left hεe1 hc).trans hcρ
  have hεB : ε * B1 ≤ ρ := by
    have h := hεe.trans hε2b
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hyd t).continuousAt
  have hNyc : Continuous (fun s => N ε s (y s)) :=
    (hNc ε hε.le hε0').comp_continuous (continuous_id.prodMk hyc) fun s =>
      Set.mk_mem_prod (Set.mem_univ _) (mem_closedBall_zero_iff.2 ((hyb s).trans hcρε))
  set h : ℝ → X → ℝ := fun s => N ε s (y s) - ε ^ 2 • h₂ s with hh
  have hhc : Continuous h := hNyc.sub (Continuous.smul (f := fun _ => ε ^ 2) (g := h₂) continuous_const h₂c)
  have hhp : ∀ s, h (s + T) = h s := fun s => by simp only [hh, hNp, hyp, h₂p]
  set w : ℝ → X → ℝ := fun t => y t - ε • y₁ t - ε ^ 2 • y₂ t with hw
  have hwd : ∀ t, HasDerivAt w (A *ᵥ w t + h t) t := by
    intro t
    have hd := ((hyd t).sub ((h₁d t).const_smul ε)).sub ((h₂d t).const_smul (ε ^ 2))
    refine hd.congr_deriv ?_
    simp only [hw, hh, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_add]
    abel
  have hwp : ∀ t, w (t + T) = w t := fun t => by simp only [hw, hyp, h₁p, h₂yp]
  have hhb : ∀ s, ‖h s‖ ≤ K' * ε ^ 3 := by
    intro s
    have hy1n : ‖ε • y₁ s‖ ≤ ε * B1 := by
      rw [norm_smul, Real.norm_of_nonneg hε.le]; exact mul_le_mul_of_nonneg_left (hB1b s) hε.le
    have e : h s = (N ε s (y s) - N ε s (ε • y₁ s)) + (N ε s (ε • y₁ s) - ε ^ 2 • h₂ s) := by
      simp only [hh]; abel
    rw [e]
    have h1 := hNL ε hε.le hε0' s (y s) (ε • y₁ s) ((hyb s).trans hcρε) (hy1n.trans hεB)
    have h2 := hN₂ ε hε hε0' s
    have h3 := hexp y hyp hyb hyd y₁ h₁p h₁d s
    have hfac : K * (‖y s‖ + ‖ε • y₁ s‖ + ε) ≤ K * ((c + B1 + 1) * ε) := by
      have := hyb s
      gcongr
      nlinarith
    have hm : K * (‖y s‖ + ‖ε • y₁ s‖ + ε) * ‖y s - ε • y₁ s‖ ≤
        K * ((c + B1 + 1) * ε) * (C * ε ^ 2) :=
      mul_le_mul hfac h3 (norm_nonneg _) (by positivity)
    calc ‖N ε s (y s) - N ε s (ε • y₁ s) + (N ε s (ε • y₁ s) - ε ^ 2 • h₂ s)‖
        ≤ K * ((c + B1 + 1) * ε) * (C * ε ^ 2) + K₂ * ε ^ 3 :=
          (norm_add_le _ _).trans (add_le_add (h1.trans hm) h2)
      _ = K' * ε ^ 3 := by rw [hK']; ring
  intro t
  rw [show y t - ε • y₁ t - ε ^ 2 • y₂ t = w t from rfl,
    periodic_eq_green hL hR hhc hhp hwd hwp t]
  refine (hCL h _ hhc hhb t).trans (le_of_eq ?_)
  ring

/-- The remainder of the variational matrix at third order:
`R₃,ε(t) = ε⁻³ (J_ε(t, y(t)) − A − ε A₁(t) − ε² A₂(t))`. -/
def jacRem3 (Jf : ℝ → ℝ → (X → ℝ) → Matrix X X ℝ) (A : Matrix X X ℝ) (A₁ A₂ : ℝ → Matrix X X ℝ)
    (y : ℝ → X → ℝ) (ε t : ℝ) : Matrix X X ℝ :=
  (ε ^ 3)⁻¹ • (Jf ε t (y t) - A - ε • A₁ t - ε ^ 2 • A₂ t)

omit [Fintype X] [DecidableEq X] in
@[tmio T, powerlib_foundation] theorem jacRem3_eq (Jf : ℝ → ℝ → (X → ℝ) → Matrix X X ℝ)
    (A : Matrix X X ℝ) (A₁ A₂ : ℝ → Matrix X X ℝ) (y : ℝ → X → ℝ) {ε : ℝ} (hε : ε ≠ 0)
    (t : ℝ) :
    Jf ε t (y t) = A + ε • A₁ t + ε ^ 2 • A₂ t + ε ^ 3 • jacRem3 Jf A A₁ A₂ y ε t := by
  rw [jacRem3, smul_smul, mul_inv_cancel₀ (pow_ne_zero 3 hε), one_smul]
  abel

set_option maxHeartbeats 1000000 in
/-- **The variational matrix along the forced orbit to second order.** Under the hypotheses of
`orbit_expansion_second`, let the matrix field `J_ε(t, y)` (the Jacobian of the vector field)
satisfy `‖J_ε(t, y) − J_ε(t, y') − D_x(y − y')‖ ≤ K_J (‖y‖ + ‖y'‖ + ε)‖y − y'‖` on the ball
(`D_x` the derivative of the Jacobian in the state at the equilibrium) and, along the first-order
orbit, `‖J_ε(t, ε y₁(t)) − A − ε A₁(t) − ε² B₂(t)‖ ≤ K_J ε³`. Then for all small `ε > 0` the
variational matrix along the (unique small) forced orbit is
`A + ε A₁(t) + ε² (D_x y₂(t) + B₂(t)) + ε³ R₃,ε(t)` with `R₃,ε` continuous and uniformly bounded. -/
@[tmio T, powerlib_foundation] theorem orbit_variational_second {A Minv : Matrix X X ℝ} {T : ℝ}
    (hT : 0 < T) (hL : Minv * (1 - expS A T) = 1) (hR : (1 - expS A T) * Minv = 1)
    {b : ℝ → X → ℝ} (hb : Continuous b) (hbp : ∀ t, b (t + T) = b t)
    {N : ℝ → ℝ → (X → ℝ) → X → ℝ} {K ρ ε0 : ℝ} (hK : 0 ≤ K) (hρ : 0 < ρ) (hε0 : 0 < ε0)
    (hNc : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × (X → ℝ) => N ε p.1 p.2)
      (Set.univ ×ˢ Metric.closedBall 0 ρ))
    (hNp : ∀ ε t y, N ε (t + T) y = N ε t y)
    (hN0 : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t, ‖N ε t 0‖ ≤ K * ε ^ 2)
    (hNL : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y1 y2, ‖y1‖ ≤ ρ → ‖y2‖ ≤ ρ →
      ‖N ε t y1 - N ε t y2‖ ≤ K * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖)
    {y₁ : ℝ → X → ℝ} (h₁p : ∀ t, y₁ (t + T) = y₁ t)
    (h₁d : ∀ t, HasDerivAt y₁ (A *ᵥ y₁ t + b t) t)
    {h₂ : ℝ → X → ℝ} (h₂c : Continuous h₂) (h₂p : ∀ t, h₂ (t + T) = h₂ t) {K₂ : ℝ}
    (hN₂ : ∀ ε, 0 < ε → ε ≤ ε0 → ∀ t, ‖N ε t (ε • y₁ t) - ε ^ 2 • h₂ t‖ ≤ K₂ * ε ^ 3)
    {y₂ : ℝ → X → ℝ} (h₂yp : ∀ t, y₂ (t + T) = y₂ t)
    (h₂d : ∀ t, HasDerivAt y₂ (A *ᵥ y₂ t + h₂ t) t)
    {Jf : ℝ → ℝ → (X → ℝ) → Matrix X X ℝ} {Dx : (X → ℝ) →ₗ[ℝ] Matrix X X ℝ} {KJ KD : ℝ}
    (hKJ : 0 ≤ KJ) (hKD : 0 ≤ KD) (hDx : ∀ v, ‖Dx v‖ ≤ KD * ‖v‖)
    (hJc : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × (X → ℝ) => Jf ε p.1 p.2)
      (Set.univ ×ˢ Metric.closedBall 0 ρ))
    (hJL : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y y', ‖y‖ ≤ ρ → ‖y'‖ ≤ ρ →
      ‖Jf ε t y - Jf ε t y' - Dx (y - y')‖ ≤ KJ * (‖y‖ + ‖y'‖ + ε) * ‖y - y'‖)
    {A₁ B₂ : ℝ → Matrix X X ℝ} (hA₁ : Continuous A₁) (hB₂ : Continuous B₂)
    (hJ₂ : ∀ ε, 0 < ε → ε ≤ ε0 → ∀ t,
      ‖Jf ε t (ε • y₁ t) - A - ε • A₁ t - ε ^ 2 • B₂ t‖ ≤ KJ * ε ^ 3) :
    ∃ c ε1 CR, 0 ≤ c ∧ 0 < ε1 ∧ ∃ R₃ : ℝ → ℝ → Matrix X X ℝ,
      (∀ ε, 0 < ε → ε ≤ ε1 → Continuous (R₃ ε)) ∧
      (∀ ε, 0 < ε → ε ≤ ε1 → ∀ t, ‖R₃ ε t‖ ≤ CR) ∧
      ∀ ε, 0 < ε → ε ≤ ε1 → (∃ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
          ∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) ∧
        ∀ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) →
          (fun t => Jf ε t (y t)) =
            fun t => A + ε • A₁ t + ε ^ 2 • (Dx (y₂ t) + B₂ t) + ε ^ 3 • R₃ ε t := by
  obtain ⟨c, C₃, ε1, hc, hC₃, hε1, hε1e, hcρ, hmain⟩ := orbit_expansion_second hT hL hR hb hbp
    hK hρ hε0 hNc hNp hN0 hNL h₁p h₁d h₂c h₂p hN₂ h₂yp h₂d
  have hy₁c : Continuous y₁ := continuous_iff_continuousAt.2 fun t => (h₁d t).continuousAt
  have hy₂c : Continuous y₂ := continuous_iff_continuousAt.2 fun t => (h₂d t).continuousAt
  obtain ⟨B0, hB0⟩ := exists_bound_of_periodic_vec hy₁c h₁p hT
  obtain ⟨E0, hE0⟩ := exists_bound_of_periodic_vec hy₂c h₂yp hT
  set B1 := max B0 0 with hB1
  set B2 := max E0 0 with hB2
  have hB1b : ∀ t, ‖y₁ t‖ ≤ B1 := fun t => (hB0 t).trans (le_max_left _ _)
  have hB2b : ∀ t, ‖y₂ t‖ ≤ B2 := fun t => (hE0 t).trans (le_max_left _ _)
  have hB10 : 0 ≤ B1 := le_max_right _ _
  have hB20 : 0 ≤ B2 := le_max_right _ _
  set ε2 := min ε1 (min 1 (ρ / (B1 + 1))) with hε2
  have hε2p : 0 < ε2 := lt_min hε1 (lt_min one_pos (by positivity))
  have hε2a : ε2 ≤ ε1 := min_le_left _ _
  have hε2b : ε2 ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hε2c : ε2 ≤ ρ / (B1 + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hex : ∀ ε, 0 < ε → ε ≤ ε2 → ∃ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) ∧
      (∀ t, ‖y t‖ ≤ c * ε) ∧ ∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t :=
    fun ε h0 h1 => (hmain ε h0 (h1.trans hε2a)).1
  set orb : ℝ → ℝ → X → ℝ := fun ε =>
    if h : 0 < ε ∧ ε ≤ ε2 then Classical.choose (hex ε h.1 h.2) else 0 with horb
  have horbS : ∀ ε, 0 < ε → ε ≤ ε2 → (∀ t, orb ε (t + T) = orb ε t) ∧
      (∀ t, ‖orb ε t‖ ≤ c * ε) ∧
      ∀ t, HasDerivAt (orb ε) (A *ᵥ orb ε t + (ε • b t + N ε t (orb ε t))) t := by
    intro ε h0 h1
    simp only [horb, h0, h1, and_self, ↓reduceDIte]
    exact Classical.choose_spec (hex ε h0 h1)
  set A₂ : ℝ → Matrix X X ℝ := fun t => Dx (y₂ t) + B₂ t with hA₂
  have hA₂c : Continuous A₂ :=
    ((LinearMap.continuous_of_finiteDimensional Dx).comp hy₂c).add hB₂
  set R₃ : ℝ → ℝ → Matrix X X ℝ := fun ε => jacRem3 Jf A A₁ A₂ (orb ε) ε with hR₃
  set CR := KJ * (c + B1 + 1) * (C₃ + B2) + KD * C₃ + KJ with hCR
  refine ⟨c, ε2, CR, hc, hε2p, R₃, ?_, ?_, ?_⟩
  · intro ε h0 h1
    have hy := horbS ε h0 h1
    have hcρε : c * ε ≤ ρ := (mul_le_mul_of_nonneg_left (h1.trans hε2a) hc).trans hcρ
    have hyc : Continuous (orb ε) := continuous_iff_continuousAt.2 fun t => (hy.2.2 t).continuousAt
    have hJo : Continuous fun t => Jf ε t (orb ε t) :=
      (hJc ε h0.le ((h1.trans hε2a).trans hε1e)).comp_continuous (continuous_id.prodMk hyc)
        fun s => Set.mk_mem_prod (Set.mem_univ _) (mem_closedBall_zero_iff.2 ((hy.2.1 s).trans hcρε))
    show Continuous fun t => (ε ^ 3)⁻¹ • (Jf ε t (orb ε t) - A - ε • A₁ t - ε ^ 2 • A₂ t)
    exact (((hJo.sub continuous_const).sub (hA₁.const_smul ε)).sub
      (hA₂c.const_smul (ε ^ 2))).const_smul ((ε ^ 3)⁻¹ : ℝ)
  · intro ε h0 h1 t
    have hy := horbS ε h0 h1
    have hεe1 : ε ≤ ε1 := h1.trans hε2a
    have hε0' : ε ≤ ε0 := hεe1.trans hε1e
    have hε1' : ε ≤ 1 := h1.trans hε2b
    have hcρε : c * ε ≤ ρ := (mul_le_mul_of_nonneg_left hεe1 hc).trans hcρ
    have hεB : ε * B1 ≤ ρ := by
      have h := h1.trans hε2c
      rw [le_div_iff₀ (by positivity)] at h
      nlinarith
    have h3 := (hmain ε h0 hεe1).2.2 (orb ε) hy.1 hy.2.1 hy.2.2 t
    set u := orb ε t with hu
    have hy1n : ‖ε • y₁ t‖ ≤ ε * B1 := by
      rw [norm_smul, Real.norm_of_nonneg h0.le]; exact mul_le_mul_of_nonneg_left (hB1b t) h0.le
    have h1st : ‖u - ε • y₁ t‖ ≤ (C₃ + B2) * ε ^ 2 := by
      have e : u - ε • y₁ t = (u - ε • y₁ t - ε ^ 2 • y₂ t) + ε ^ 2 • y₂ t := by abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      have hε3 : ε ^ 3 ≤ ε ^ 2 := pow_le_pow_of_le_one h0.le hε1' (by norm_num)
      have : C₃ * ε ^ 3 ≤ C₃ * ε ^ 2 := mul_le_mul_of_nonneg_left hε3 hC₃
      nlinarith [hB2b t, sq_nonneg ε]
    have e : Jf ε t u - A - ε • A₁ t - ε ^ 2 • A₂ t =
        (Jf ε t u - Jf ε t (ε • y₁ t) - Dx (u - ε • y₁ t)) + Dx (u - ε • y₁ t - ε ^ 2 • y₂ t) +
          (Jf ε t (ε • y₁ t) - A - ε • A₁ t - ε ^ 2 • B₂ t) := by
      simp only [hA₂, map_sub, map_smul, smul_add]
      abel
    have hb1 := hJL ε h0.le hε0' t u (ε • y₁ t) ((hy.2.1 t).trans hcρε) (hy1n.trans hεB)
    have hfac : KJ * (‖u‖ + ‖ε • y₁ t‖ + ε) ≤ KJ * ((c + B1 + 1) * ε) := by
      have := hy.2.1 t
      gcongr
      nlinarith
    have hb1' : ‖Jf ε t u - Jf ε t (ε • y₁ t) - Dx (u - ε • y₁ t)‖ ≤
        KJ * (c + B1 + 1) * (C₃ + B2) * ε ^ 3 := by
      refine hb1.trans ?_
      calc KJ * (‖u‖ + ‖ε • y₁ t‖ + ε) * ‖u - ε • y₁ t‖ ≤
            KJ * ((c + B1 + 1) * ε) * ((C₃ + B2) * ε ^ 2) :=
            mul_le_mul hfac h1st (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hb2 : ‖Dx (u - ε • y₁ t - ε ^ 2 • y₂ t)‖ ≤ KD * C₃ * ε ^ 3 := by
      refine (hDx _).trans ?_
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h3 hKD
    have hb3 := hJ₂ ε h0 hε0' t
    have hε3p : 0 < ε ^ 3 := by positivity
    show ‖(ε ^ 3)⁻¹ • (Jf ε t (orb ε t) - A - ε • A₁ t - ε ^ 2 • A₂ t)‖ ≤ CR
    rw [← hu, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hε3p.le), inv_mul_le_iff₀ hε3p, e]
    calc _ ≤ ‖Jf ε t u - Jf ε t (ε • y₁ t) - Dx (u - ε • y₁ t)‖ +
          ‖Dx (u - ε • y₁ t - ε ^ 2 • y₂ t)‖ +
          ‖Jf ε t (ε • y₁ t) - A - ε • A₁ t - ε ^ 2 • B₂ t‖ := norm_add₃_le
      _ ≤ KJ * (c + B1 + 1) * (C₃ + B2) * ε ^ 3 + KD * C₃ * ε ^ 3 + KJ * ε ^ 3 := by
          gcongr
      _ = ε ^ 3 * CR := by rw [hCR]; ring
  · intro ε h0 h1
    refine ⟨hex ε h0 h1, fun y hy1 hy2 hy3 => ?_⟩
    have hyo : y = orb ε := (hmain ε h0 (h1.trans hε2a)).2.1 y (orb ε) hy1 hy2 hy3
      (horbS ε h0 h1).1 (horbS ε h0 h1).2.1 (horbS ε h0 h1).2.2
    funext t
    rw [hyo, jacRem3_eq Jf A A₁ A₂ (orb ε) h0.ne' t]

/-! ## The forced orbit on the first-order boundary -/

section Boundary

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- **The second-order decisive quantity of a physical variational matrix** on the first-order
boundary: `mixedDet(M, N_eff + ∫₀ᵀ R(−ωt/2) (Q R₂ P)₁₁ R(ωt/2) dt)` with
`M = slowFlowMatrix (−Re λ₁) (−Im λ₁) (g/2)` (`λ₁ = u A₀' r`, `g = u A₁ r̄`), `N_eff` the effective
second-order matrix of the modal standard form `FzcB 0 0 ω T A_s (Q A₁ P) (Q A₀' P)` with
`E = e^{TA_s}`, and `R₂` the `O(ε²)` part of the variational matrix, `T = 2π/ω`. -/
def orbitMixed (P : Matrix X (Fin 2 ⊕ Y) ℝ) (Q : Matrix (Fin 2 ⊕ Y) X ℝ) (As : Matrix Y Y ℝ)
    (ω : ℝ) (A0' : Matrix X X ℝ) (A1 : Matrix X X ℂ) (R₂ : ℝ → Matrix X X ℝ) : ℝ :=
  mixedDet (slowFlowMatrix (-(physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re)
      (-(physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).im)
      (physLeft Q ⬝ᵥ (A1 *ᵥ star (physRight P)) / 2))
    (effSecond (FzcB 0 0 ω (2 * Real.pi / ω) As
        (Q.map (algebraMap ℝ ℂ) * A1 * P.map (algebraMap ℝ ℂ)) (Q * A0' * P))
      (2 * Real.pi / ω) (expS As (2 * Real.pi / ω)) +
      critIntegral ω (2 * Real.pi / ω) (fun t => Q * R₂ t * P))

set_option maxHeartbeats 2000000 in
/-- **The forced orbit on the first-order boundary, level L1.** Under the hypotheses of
`orbit_variational_second` (forced system, second-order orbit data `h₂`, `y₂`, Jacobian data
`D_x`, `A₁`, `B₂`), with real modal coordinates of `A` (`Q A P = diag(base(0, ω/2), A_s)`,
`ρ(e^{TA_s}) < 1`, `T = 2π/ω`) and the first-order part `A₁(t) = A₀' + Re{A₁ᶜ e^{jωt}}` on the
first-order boundary `|λ₁| = |g/2|`, `Re λ₁ < 0` (`λ₁ = u A₀' r`, `g = u A₁ᶜ r̄`): for all small
`ε > 0` the forced orbit exists (unique in the ball of radius `cε`), and with
`Δ = orbitMixed P Q A_s ω A₀' A₁ᶜ (D_x y₂ + B₂)`, `Δ > 0` puts every Floquet multiplier of its
variational equation inside the unit circle and `Δ < 0` makes it Floquet unstable. -/
@[tmio T, powerlib_foundation] theorem orbit_boundary_floquet {A Minv : Matrix X X ℝ} {T : ℝ}
    (hT : 0 < T) (hL : Minv * (1 - expS A T) = 1) (hR : (1 - expS A T) * Minv = 1)
    {b : ℝ → X → ℝ} (hb : Continuous b) (hbp : ∀ t, b (t + T) = b t)
    {N : ℝ → ℝ → (X → ℝ) → X → ℝ} {K ρ ε0 : ℝ} (hK : 0 ≤ K) (hρ : 0 < ρ) (hε0 : 0 < ε0)
    (hNc : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × (X → ℝ) => N ε p.1 p.2)
      (Set.univ ×ˢ Metric.closedBall 0 ρ))
    (hNp : ∀ ε t y, N ε (t + T) y = N ε t y)
    (hN0 : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t, ‖N ε t 0‖ ≤ K * ε ^ 2)
    (hNL : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y1 y2, ‖y1‖ ≤ ρ → ‖y2‖ ≤ ρ →
      ‖N ε t y1 - N ε t y2‖ ≤ K * (‖y1‖ + ‖y2‖ + ε) * ‖y1 - y2‖)
    {y₁ : ℝ → X → ℝ} (h₁p : ∀ t, y₁ (t + T) = y₁ t)
    (h₁d : ∀ t, HasDerivAt y₁ (A *ᵥ y₁ t + b t) t)
    {h₂ : ℝ → X → ℝ} (h₂c : Continuous h₂) (h₂p : ∀ t, h₂ (t + T) = h₂ t) {K₂ : ℝ}
    (hN₂ : ∀ ε, 0 < ε → ε ≤ ε0 → ∀ t, ‖N ε t (ε • y₁ t) - ε ^ 2 • h₂ t‖ ≤ K₂ * ε ^ 3)
    {y₂ : ℝ → X → ℝ} (h₂yp : ∀ t, y₂ (t + T) = y₂ t)
    (h₂d : ∀ t, HasDerivAt y₂ (A *ᵥ y₂ t + h₂ t) t)
    {Jf : ℝ → ℝ → (X → ℝ) → Matrix X X ℝ} {Dx : (X → ℝ) →ₗ[ℝ] Matrix X X ℝ} {KJ KD : ℝ}
    (hKJ : 0 ≤ KJ) (hKD : 0 ≤ KD) (hDx : ∀ v, ‖Dx v‖ ≤ KD * ‖v‖)
    (hJc : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ContinuousOn (fun p : ℝ × (X → ℝ) => Jf ε p.1 p.2)
      (Set.univ ×ˢ Metric.closedBall 0 ρ))
    (hJL : ∀ ε, 0 ≤ ε → ε ≤ ε0 → ∀ t y y', ‖y‖ ≤ ρ → ‖y'‖ ≤ ρ →
      ‖Jf ε t y - Jf ε t y' - Dx (y - y')‖ ≤ KJ * (‖y‖ + ‖y'‖ + ε) * ‖y - y'‖)
    {A₁ B₂ : ℝ → Matrix X X ℝ} (hA₁ : Continuous A₁) (hB₂ : Continuous B₂)
    (hJ₂ : ∀ ε, 0 < ε → ε ≤ ε0 → ∀ t,
      ‖Jf ε t (ε • y₁ t) - A - ε • A₁ t - ε ^ 2 • B₂ t‖ ≤ KJ * ε ^ 3)
    {ω : ℝ} (hω : 0 < ω) (hTω : T = 2 * Real.pi / ω)
    {P : Matrix X (Fin 2 ⊕ Y) ℝ} {Q : Matrix (Fin 2 ⊕ Y) X ℝ}
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (As : Matrix Y Y ℝ)
    (hA0 : Q * A * P = fromBlocks (base 0 (ω / 2)) 0 0 As)
    (hsr : spectralRadius ℂ ((expS As (2 * Real.pi / ω)).map (algebraMap ℝ ℂ)) < 1)
    (A0' : Matrix X X ℝ) (A1 : Matrix X X ℂ) (hlink : ∀ t, A₁ t = A0' + modX A1 ω t)
    (hs : (physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)).re < 0)
    (hbd : ‖physLeft Q ⬝ᵥ (A0'.map (algebraMap ℝ ℂ) *ᵥ physRight P)‖ ^ 2 =
      ‖physLeft Q ⬝ᵥ (A1 *ᵥ star (physRight P)) / 2‖ ^ 2) :
    ∃ c, 0 ≤ c ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) ∧ (∀ t, ‖y t‖ ≤ c * ε) ∧
        ∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) ∧
      (0 < orbitMixed P Q As ω A0' A1 (fun t => Dx (y₂ t) + B₂ t) →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) →
          ∀ (μ : ℂ) (v : X → ℂ), v ≠ 0 →
            (Periodic.monodromy (fun t => Jf ε t (y t)) T 0).map (algebraMap ℝ ℂ) *ᵥ v = μ • v →
              ‖μ‖ < 1) ∧
      (orbitMixed P Q As ω A0' A1 (fun t => Dx (y₂ t) + B₂ t) < 0 →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) → (∀ t, ‖y t‖ ≤ c * ε) →
          (∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) →
          Periodic.FloquetUnstable (fun t => Jf ε t (y t)) T) := by
  obtain ⟨c, ε1, CR, hc, hε1, R₃, hR₃c, hR₃b, hmain⟩ := orbit_variational_second hT hL hR hb hbp
    hK hρ hε0 hNc hNp hN0 hNL h₁p h₁d h₂c h₂p hN₂ h₂yp h₂d hKJ hKD hDx hJc hJL hA₁ hB₂ hJ₂
  have hy₂c : Continuous y₂ := continuous_iff_continuousAt.2 fun t => (h₂d t).continuousAt
  have hR₂c : Continuous (fun t => Dx (y₂ t) + B₂ t) :=
    ((LinearMap.continuous_of_finiteDimensional Dx).comp hy₂c).add hB₂
  have hphys := RemainderSecond.physicalR2_boundary hω hPQ hQP As hA0 A0' A1 hε1 hR₂c hR₃c hR₃b
    hs hbd hsr
  have hJeq : ∀ ε, 0 < ε → ε ≤ ε1 → ∀ y : ℝ → X → ℝ, (∀ t, y (t + T) = y t) →
      (∀ t, ‖y t‖ ≤ c * ε) → (∀ t, HasDerivAt y (A *ᵥ y t + (ε • b t + N ε t (y t))) t) →
      (fun t => Jf ε t (y t)) =
        physJR A A0' A1 (fun ε t => (Dx (y₂ t) + B₂ t) + ε • R₃ ε t) ω ε := by
    intro ε h0 h1 y hy1 hy2 hy3
    rw [(hmain ε h0 h1).2 y hy1 hy2 hy3]
    funext t
    simp only [physJR, BlockAveraging.physJ, hlink, smul_add, smul_smul]
    module
  refine ⟨c, hc, ?_, fun hmix => ?_, fun hmix => ?_⟩
  · filter_upwards [BlockAveraging.eventually_lt_nhdsGT hε1] with ε ⟨h0, h1⟩
    exact (hmain ε h0 h1.le).1
  · filter_upwards [hphys.1 hmix, BlockAveraging.eventually_lt_nhdsGT hε1] with ε hε ⟨h0, h1⟩
    intro y hy1 hy2 hy3 μ v hv hμ
    rw [hJeq ε h0 h1.le y hy1 hy2 hy3, hTω] at hμ
    exact hε μ v hv hμ
  · filter_upwards [hphys.2 hmix, BlockAveraging.eventually_lt_nhdsGT hε1] with ε hε ⟨h0, h1⟩
    intro y hy1 hy2 hy3
    rw [hJeq ε h0 h1.le y hy1 hy2 hy3, hTω]
    exact hε

end Boundary

end powerlib.ParametricResonance.ForcedOrbitSecond
