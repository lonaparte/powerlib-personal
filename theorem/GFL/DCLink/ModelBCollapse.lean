import theorem.GFL.DCLink.ModelBStability
import theorem.Dynamics.Degenerate.PlaneCollapse

/-! # GFL model B on the singular plane: the degenerate power balance

Model boundary.
The model-B family `ModelB.family` of `theorem/GFL/DCLink/ModelBStability.lean`
(field `ModelBParams.field`, state `(Δθ, x_pll, V_dc, ξ_v)`, continuous-time autonomous, constant
grid frequency, inner current loop eliminated, reactive current frozen, no saturation, PWM, delay or
filters), read at a selected state `x*` on the singular plane `V_dc* = 0`, where the field is read
with Lean's `x / 0 = 0` (DC-link component `I₀ / C_dc`). This module settles the case left open in
`theorem/GFL/DCLink/ModelBStability.lean`: the degenerate power balance `P(x*) = 0` (`P = pccP`).

Convention: port current IN-positive (work-sync conventions §D1), as in `ModelBStability`.

Source: work-sync `theory/T-gfl-reduced-order-dynamics.md` §1.6 (model B); the reduction is new
(answers the residual case of the `V_dc* = 0` question). Candidate analysis checked numerically
(untrusted); Lean proves every statement.

Results.
Reduction. With `q = (I₀ V_dc + (3/2) P) / C_dc` (`planeQ`) the field satisfies, off the plane,
`V_dc V_dc' = q` (`field_two_eq_planeQ_div`) and `q' = G + H q / V_dc` (`planeQ_lie`), with the
continuous coefficients `G = (3/2)(∂_Δθ P · f_Δθ + ∂_ξ P · f_ξ) / C_dc` (`planeG`) and
`H = (I₀ + (3/2) ∂_{V_dc} P) / C_dc` (`planeH`). In the time `dτ = dt / V_dc` this is the linear
system `(V_dc, q)' = [[0, 1], [G, H]] (V_dc, q)`, whose type at `x*` is decided by the
discriminant `D = H² + 4G` (`planeDisc`).
* `ModelB.mem_den_unstable_of_disc_pos`: `D > 0` ⇒ unstable. A root `λ₊ > 0` of `λ² − Hλ − G`
  on one side of the plane gives an invariant cone `{σ V_dc > 0, q ≥ μ σ V_dc}` in which
  `σ V_dc` grows linearly (`Dynamics.Degenerate.unstable_of_cone`).
* `ModelB.mem_den_locallyExponentiallyStable_of_disc_neg`: `D < 0` and `I₀ / C_dc ≠ 0` ⇒ the
  segment-based local exponential estimate holds although `x*` is not an equilibrium: the focus
  winds every solution segment into the plane within a time `O(‖x(t₀) − x*‖)`
  (`Dynamics.Degenerate.locallyExponentiallyStable_of_spiral`). Witness `degenerateFocus`
  (`degenerateFocus_mem_den_locallyExponentiallyStable`, `D = −3`).
* `ModelB.mem_den_locallyExponentiallyStable_iff_of_Vdc_eq_zero_of_nondegenerate`: complete
  characterization of local exponential stability on the singular plane outside the degenerate set
  `{P(x*) = 0, I₀ / C_dc ≠ 0, D = 0}`: LES ⇔ `I₀ / C_dc ≠ 0 ∧ (P / C_dc < 0 ∨ (P = 0 ∧ D < 0))`.
* Static support (foundation): `dP0`, `dP2`, `dP3` (partial derivatives of `P`), `planeQ`,
  `planeG`, `planeH`, `planeDisc`, `hasFDerivAt_planeQ`, `planeQ_lie`, `field_two_eq_planeQ_div`,
  `continuous_planeG`, `continuous_planeH`, `exists_contDiff_eq_field_of_sign`.

Family and connection conclusions.
Connection conclusions on `ModelB.family`: `mem_den_unstable_of_disc_pos`,
`mem_den_locallyExponentiallyStable_of_disc_neg`,
`degenerateFocus_mem_den_locallyExponentiallyStable`,
`mem_den_locallyExponentiallyStable_iff_of_Vdc_eq_zero_of_nondegenerate`. The plane coefficients and
their identities are foundation; the trajectory-level statements are private implementation
evidence.

The degenerate discriminant `D = 0` (with `P(x*) = 0`, `I₀ / C_dc ≠ 0`) is treated in
`theorem/GFL/DCLink/ModelBCollapseDegenerate.lean`: `H ≠ 0` ⇒ unstable, `H = G = 0` with nonzero
drift `(f₀, f₁, f₃)(x*)` ⇒ not locally exponentially stable; it leaves (UNPROVED) only the residual
set `{P = 0, I₀ / C_dc ≠ 0, H = 0, f₀ = f₁ = f₃ = 0}`, which forces `V_dc,ref = 0`.
-/

noncomputable section
namespace powerlib.GFL.DCLink
open Set Filter Matrix
open scoped Topology
open powerlib.Dynamics (State)

namespace ModelBParams

variable (p : ModelBParams)

/-- `∂P/∂Δθ` (`P = pccP`). -/
def dP0 (y : State 4) : ℝ :=
  -p.Vg * Real.sin (y 0) * p.idRef (y 2) (y 3) - p.Vg * Real.cos (y 0) * p.iq0

/-- `∂P/∂V_dc`. -/
def dP2 (y : State 4) : ℝ :=
  p.kpv * (p.Rg * p.idRef (y 2) (y 3) - p.vgd (y 0) (p.idRef (y 2) (y 3)) + p.Xg * p.iq0)

/-- `∂P/∂ξ_v`. -/
def dP3 (y : State 4) : ℝ :=
  p.kiv * (p.vgd (y 0) (p.idRef (y 2) (y 3)) - p.Rg * p.idRef (y 2) (y 3) - p.Xg * p.iq0)

/-- `q = (I₀ V_dc + (3/2) P) / C_dc`: off the plane the DC-link component of the field is
`q / V_dc`, and `d(V_dc²)/dt = 2 q`. -/
def planeQ (y : State 4) : ℝ := (p.I0 * y 2 + 3 / 2 * p.pccP y) / p.Cdc

/-- The part of `dq/dt` that does not involve the DC-link component of the field. -/
def planeG (y : State 4) : ℝ :=
  3 / 2 * (p.dP0 y * p.field y 0 + p.dP3 y * p.field y 3) / p.Cdc

/-- `∂q/∂V_dc`, so that `dq/dt = G + H q / V_dc` off the plane. -/
def planeH (y : State 4) : ℝ := (p.I0 + 3 / 2 * p.dP2 y) / p.Cdc

/-- The discriminant `H² + 4 G` of the quadratic `λ² − H λ − G` of the reduced dynamics
`V_dc V_dc' = q`, `q' = G + H q / V_dc` near the plane. -/
def planeDisc (y : State 4) : ℝ := p.planeH y ^ 2 + 4 * p.planeG y

@[tmio M, powerlib_foundation] theorem hasFDerivAt_planeQ (y : State 4) :
    HasFDerivAt p.planeQ (row4 (3 / 2 * p.dP0 y / p.Cdc) 0 ((p.I0 + 3 / 2 * p.dP2 y) / p.Cdc)
      (3 / 2 * p.dP3 y / p.Cdc)) y := by
  have h := (((Dynamics.hasFDerivAt_coord 2 y).const_mul p.I0).add
    ((p.hasFDerivAt_pccP y).const_mul (3 / 2))).mul_const p.Cdc⁻¹
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
  · ext v
    simp [row4, dP0, dP2, dP3]
    ring
  · simp [planeQ, div_eq_mul_inv]

@[powerlib_foundation] theorem contDiff_planeQ : ContDiff ℝ 1 p.planeQ := by
  unfold planeQ
  exact ((contDiff_const.mul (Dynamics.contDiff_coord 2)).add
    (contDiff_const.mul p.contDiff_pccP)).div_const _

@[powerlib_foundation] theorem planeQ_eq_zero {x : State 4} (hx : x 2 = 0) (hP : p.pccP x = 0) :
    p.planeQ x = 0 := by
  simp [planeQ, hx, hP]

/-- Off the plane the DC-link component of the field is `q / V_dc`. -/
@[powerlib_foundation] theorem field_two_eq_planeQ_div {y : State 4} (hy : y 2 ≠ 0) :
    p.field y 2 = p.planeQ y / y 2 := by
  have h : p.field y 2 = (p.I0 + 3 * p.pccP y / (2 * y 2)) / p.Cdc := by
    simp [field, pccP]
  rw [h, planeQ]
  field_simp

/-- `dq/dt = G + H q / V_dc` off the plane. -/
@[powerlib_foundation] theorem planeQ_lie {y : State 4} (hy : y 2 ≠ 0) :
    fderiv ℝ p.planeQ y (p.field y) = p.planeG y + p.planeH y * (p.planeQ y / y 2) := by
  rw [(p.hasFDerivAt_planeQ y).fderiv, ← p.field_two_eq_planeQ_div hy]
  simp only [row4_apply, planeG, planeH]
  ring

@[powerlib_foundation] theorem continuous_planeG : Continuous p.planeG := by
  show Continuous fun y : State 4 => 3 / 2 * (p.dP0 y *
    (p.ωs - p.ωg + p.kp * p.vgq (y 0) (p.idRef (y 2) (y 3)) + p.ki * y 1) +
      p.dP3 y * (p.VdcRef - y 2)) / p.Cdc
  unfold dP0 dP3 vgq vgd idRef
  fun_prop

@[powerlib_foundation] theorem continuous_planeH : Continuous p.planeH := by
  unfold planeH dP2 vgd idRef
  fun_prop

/-- A `C¹` field equal to model B on the half space `σ V_dc ≥ s` (`σ = ±1`, `s > 0`): the
denominator `V_dc` is replaced by `σ regDen s (σ V_dc)`. -/
@[powerlib_foundation] theorem exists_contDiff_eq_field_of_sign {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {s : ℝ} (hs : 0 < s) :
    ∃ g : State 4 → State 4, ContDiff ℝ 1 g ∧
      ∀ y : State 4, s ≤ σ * y 2 → g y = p.field y := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine ⟨fun y => (WithLp.toLp 2 ![p.field y 0, p.field y 1,
      (p.I0 + 3 * p.pccP y / (2 * (σ * Dynamics.regDen s (σ * y 2)))) / p.Cdc,
      p.field y 3] : State 4),
    ?_, ?_⟩
  · have hden : ContDiff ℝ 1 (fun y : State 4 => 2 * (σ * Dynamics.regDen s (σ * y 2))) :=
      contDiff_const.mul (contDiff_const.mul ((Dynamics.contDiff_regDen _).comp
        (contDiff_const.mul (Dynamics.contDiff_coord 2))))
    have hden0 : ∀ y : State 4, 2 * (σ * Dynamics.regDen s (σ * y 2)) ≠ 0 := fun y => by
      have h1 := Dynamics.half_le_regDen hs (σ * y 2)
      have h2 : 0 < Dynamics.regDen s (σ * y 2) := lt_of_lt_of_le (by positivity) h1
      rcases hσ with rfl | rfl
      · positivity
      · have : 0 < 2 * Dynamics.regDen s (-1 * y 2) := by positivity
        intro h; linarith
    have hoff := p.contDiff_field_offDC
    apply Dynamics.contDiff_of_components
    intro i
    fin_cases i
    · show ContDiff ℝ 1 (fun y : State 4 => p.field y 0)
      have h := (Dynamics.contDiff_coord (n := 4) (k := 1) 0).comp hoff
      exact h
    · show ContDiff ℝ 1 (fun y : State 4 => p.field y 1)
      have h := (Dynamics.contDiff_coord (n := 4) (k := 1) 1).comp hoff
      exact h
    · show ContDiff ℝ 1 (fun y : State 4 =>
        (p.I0 + 3 * p.pccP y / (2 * (σ * Dynamics.regDen s (σ * y 2)))) / p.Cdc)
      exact (contDiff_const.add ((contDiff_const.mul p.contDiff_pccP).div hden hden0)).div_const _
    · show ContDiff ℝ 1 (fun y : State 4 => p.field y 3)
      have h := (Dynamics.contDiff_coord (n := 4) (k := 1) 3).comp hoff
      exact h
  · intro y hy
    have hr : σ * Dynamics.regDen s (σ * y 2) = y 2 := by
      rw [Dynamics.regDen_eq hs (by linarith)]
      rw [← mul_assoc, hσ2, one_mul]
    ext i
    fin_cases i
    · rfl
    · rfl
    · show (p.I0 + 3 * p.pccP y / (2 * (σ * Dynamics.regDen s (σ * y 2)))) / p.Cdc = p.field y 2
      rw [hr]
      simp [field, pccP]
    · rfl

/-- **Degenerate power balance on the singular plane, positive discriminant: instability.** At a
state `x` with `V_dc = 0` and `P(x) = 0`, write `q = (I₀ V_dc + (3/2) P) / C_dc`, so that near
the plane `V_dc V_dc' = q` and `q' = G + H q / V_dc` (`planeQ_lie`). If `H² + 4G > 0` at `x`, the
quadratic `λ² − Hλ − G` has a root `λ₊ > 0` on the side `σ = sign H` (or on both sides if
`G > 0`), and the cone `{σ V_dc > 0, q ≥ μ σ V_dc}` for `μ` slightly above `σH/2` is entered by
the field and carries `σ V_dc' ≥ μ > 0` (`Dynamics.Degenerate.unstable_of_cone`). -/
@[tmio TM] private theorem modelB_unstable_of_disc_pos {x : State 4} (hx : x 2 = 0) (hP : p.pccP x = 0)
    (hD : 0 < p.planeDisc x) :
    connection% ((⟨p, x⟩ : ModelB.Model) ∈ ModelB.family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% (Spectral.mem_den_flow_iff_shift (f := fun m : ModelB.Model => m.p.field) (pt := ModelB.Model.x) ModelB.family_isAutonomous))]
  change Unstable p.field x
  obtain ⟨σ, hσ, hσH⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ σ * p.planeH x = |p.planeH x| := by
    by_cases h : 0 ≤ p.planeH x
    · exact ⟨1, Or.inl rfl, by rw [one_mul, abs_of_nonneg h]⟩
    · exact ⟨-1, Or.inr rfl, by rw [abs_of_neg (not_le.mp h)]; ring⟩
  have hσ2 : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  obtain ⟨a0, ha0⟩ : ∃ a, a = 3 / 2 * p.dP0 x / p.Cdc := ⟨_, rfl⟩
  obtain ⟨a3, ha3⟩ : ∃ a, a = 3 / 2 * p.dP3 x / p.Cdc := ⟨_, rfl⟩
  have hG : p.planeG x = a0 * p.field x 0 + a3 * p.field x 3 := by
    rw [ha0, ha3, planeG]; ring
  have hDHG : p.planeDisc x = p.planeH x ^ 2 + 4 * p.planeG x := rfl
  have hS : 0 < a0 ^ 2 + a3 ^ 2 + |p.planeH x| / 2 := by
    by_contra hS
    push Not at hS
    have e0 : a0 = 0 := by nlinarith [sq_nonneg a0, sq_nonneg a3, abs_nonneg (p.planeH x)]
    have e3 : a3 = 0 := by nlinarith [sq_nonneg a0, sq_nonneg a3, abs_nonneg (p.planeH x)]
    have eH : |p.planeH x| = 0 := by
      nlinarith [sq_nonneg a0, sq_nonneg a3, abs_nonneg (p.planeH x)]
    have : p.planeDisc x = 0 := by
      rw [hDHG, hG, e0, e3, ← sq_abs (p.planeH x), eH]; ring
    linarith
  obtain ⟨μ, hμ, hmargin, hμS⟩ : ∃ μ : ℝ, 0 < μ ∧
      0 < p.planeG x + |p.planeH x| * μ - μ ^ 2 ∧ μ < a0 ^ 2 + a3 ^ 2 + |p.planeH x| := by
    set ν := min (min 1 (p.planeDisc x / 8)) ((a0 ^ 2 + a3 ^ 2 + |p.planeH x| / 2) / 2) with hν
    have hν0 : 0 < ν := lt_min (lt_min one_pos (by positivity)) (by positivity)
    have hν1 : ν ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
    have hνD : ν ≤ p.planeDisc x / 8 := (min_le_left _ _).trans (min_le_right _ _)
    have hνS : ν ≤ (a0 ^ 2 + a3 ^ 2 + |p.planeH x| / 2) / 2 := min_le_right _ _
    refine ⟨|p.planeH x| / 2 + ν, by positivity, ?_, by linarith⟩
    have : p.planeG x + |p.planeH x| * (|p.planeH x| / 2 + ν) - (|p.planeH x| / 2 + ν) ^ 2 =
        p.planeDisc x / 4 - ν ^ 2 := by
      rw [hDHG, ← sq_abs (p.planeH x)]; ring
    rw [this]
    nlinarith
  -- the boundary rate is positive near `x`
  have hcont : Continuous fun y : State 4 => p.planeG y + σ * p.planeH y * μ - μ ^ 2 :=
    (p.continuous_planeG.add ((continuous_const.mul p.continuous_planeH).mul
      continuous_const)).sub continuous_const
  have hmargin' : 0 < p.planeG x + σ * p.planeH x * μ - μ ^ 2 := by rw [hσH]; exact hmargin
  obtain ⟨ρ, hρ, hball⟩ := Metric.continuous_iff.mp hcont x _ hmargin'
  have hWc : ContDiff ℝ 1 (fun y : State 4 => p.planeQ y - μ * σ * y 2) :=
    p.contDiff_planeQ.sub (contDiff_const.mul (Dynamics.contDiff_coord 2))
  have hWd : ∀ y : State 4, HasFDerivAt (fun y : State 4 => p.planeQ y - μ * σ * y 2)
      (row4 (3 / 2 * p.dP0 y / p.Cdc) 0 ((p.I0 + 3 / 2 * p.dP2 y) / p.Cdc - μ * σ)
        (3 / 2 * p.dP3 y / p.Cdc)) y := by
    intro y
    have h := (p.hasFDerivAt_planeQ y).sub ((Dynamics.hasFDerivAt_coord 2 y).const_mul (μ * σ))
    refine h.congr_fderiv ?_
    ext v
    simp only [row4_apply, _root_.sub_apply, _root_.smul_apply, Dynamics.coord_apply,
      smul_eq_mul]
    ring
  have hW0 : p.planeQ x - μ * σ * x 2 = 0 := by rw [p.planeQ_eq_zero hx hP, hx]; ring
  refine Dynamics.Degenerate.unstable_of_cone 2 hσ hρ hμ hWc hx hW0 ?_ ?_
    (WithLp.toLp 2 ![a0, 0, σ, a3]) ?_ ?_ ?_
  · intro y _ hy hWy
    have hy2 : y 2 ≠ 0 := by intro h; rw [h, mul_zero] at hy; exact lt_irrefl _ hy
    rw [p.field_two_eq_planeQ_div hy2]
    have hq : μ * σ * y 2 ≤ p.planeQ y := by linarith
    have hσy : σ * (p.planeQ y / y 2) * (σ * y 2) = p.planeQ y := by
      field_simp
      linear_combination p.planeQ y * hσ2
    have h1 : μ * (σ * y 2) ≤ σ * (p.planeQ y / y 2) * (σ * y 2) := by
      rw [hσy]; linarith
    exact le_of_mul_le_mul_right h1 hy
  · intro y hyx hy hWy
    have hy2 : y 2 ≠ 0 := by intro h; rw [h, mul_zero] at hy; exact lt_irrefl _ hy
    rw [(hWd y).fderiv]
    have hq : p.planeQ y = μ * σ * y 2 := by linarith
    have hrate := hball y (by rw [dist_eq_norm]; exact hyx)
    rw [Real.dist_eq] at hrate
    have hrate' := (abs_lt.mp hrate).1
    have hf2' : p.field y 2 = μ * σ := by
      rw [p.field_two_eq_planeQ_div hy2, hq]; field_simp
    have hlie : row4 (3 / 2 * p.dP0 y / p.Cdc) 0 ((p.I0 + 3 / 2 * p.dP2 y) / p.Cdc - μ * σ)
        (3 / 2 * p.dP3 y / p.Cdc) (p.field y) =
        p.planeG y + σ * p.planeH y * μ - μ ^ 2 := by
      rw [row4_apply, hf2', planeG, planeH]
      linear_combination (-(μ ^ 2)) * hσ2
    rw [hlie]
    linarith
  · simp [hσ2]
  · rw [(hWd x).fderiv, row4_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    have h1 : (p.I0 + 3 / 2 * p.dP2 x) / p.Cdc = p.planeH x := rfl
    rw [h1, ← ha0, ← ha3]
    have : a0 * a0 + 0 * 0 + (p.planeH x - μ * σ) * σ + a3 * a3 =
        a0 ^ 2 + a3 ^ 2 + |p.planeH x| - μ := by
      rw [← hσH]
      linear_combination (-μ) * hσ2
    rw [this]
    linarith
  · intro s hs
    obtain ⟨g, hg, hgf⟩ := p.exists_contDiff_eq_field_of_sign hσ hs
    exact ⟨g, hg, fun y _ hy => hgf y hy⟩


/-- **Degenerate power balance on the singular plane, negative discriminant: collapse.** At a
state `x` with `V_dc = 0`, `P(x) = 0` and `I₀ / C_dc ≠ 0`, if `H² + 4G < 0` at `x` then in the
time `dτ = dt / V_dc` the pair `(V_dc, q)` is a linear focus near `x`: every solution segment
reaches the plane at most at its end, after a time `O(‖x(t₀) − x‖)`, so the segment-based local
exponential estimate holds although `x` is not an equilibrium
(`Dynamics.Degenerate.locallyExponentiallyStable_of_spiral`). Implementation evidence for
`ModelB.mem_den_locallyExponentiallyStable_of_disc_neg`. -/
@[tmio TM] private theorem modelB_locallyExponentiallyStable_of_disc_neg {x : State 4} (hx : x 2 = 0)
    (hP : p.pccP x = 0) (hI : p.I0 / p.Cdc ≠ 0) (hD : p.planeDisc x < 0) :
    connection% ((⟨p, x⟩ : ModelB.Model) ∈ ModelB.family.den (.flow .locallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [(connection_proof% (Spectral.mem_den_flow_iff_shift (f := fun m : ModelB.Model => m.p.field) (pt := ModelB.Model.x) ModelB.family_isAutonomous))]
  change LocallyExponentiallyStable p.field x
  obtain ⟨M, hM⟩ := (isCompact_closedBall x 1).exists_bound_of_continuousOn
    p.contDiff_field_offDC.continuous.continuousOn
  refine Dynamics.Degenerate.locallyExponentiallyStable_of_spiral 2 hx p.contDiff_planeQ
    (p.planeQ_eq_zero hx hP) p.continuous_planeG.continuousAt p.continuous_planeH.continuousAt
    (ρ := 1) (M := M) one_pos ?_ ?_ ?_ hD ?_
  · intro y _ hy
    rw [p.field_two_eq_planeQ_div hy]
    field_simp
  · intro y _ hy
    rw [p.field_two_of_Vdc_eq_zero hy]
    exact hI
  · intro y _ hy
    exact p.planeQ_lie hy
  · intro y hy
    have hFy : p.field y - p.field y 2 • EuclideanSpace.single 2 (1 : ℝ) =
        (WithLp.toLp 2 ![p.field y 0, p.field y 1, 0, p.field y 3] : State 4) := by
      ext i
      fin_cases i <;> simp
    rw [hFy]
    exact hM y (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hy.le)

end ModelBParams

namespace ModelB

/-- A flow sentence of a model is the sentence of the untranslated field at the selected state. -/
private theorem mem_den_flow_iff' {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.p.field m.x :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.p.field) (pt := Model.x)
    family_isAutonomous

/-- **Degenerate power balance, positive discriminant: instability.** A selected state on the
singular plane (`V_dc* = 0`) with `P(x*) = 0` and `H² + 4G > 0` (`planeDisc`) is unstable. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_disc_pos (m : Model) (hx : m.x 2 = 0)
    (hP : m.p.pccP m.x = 0) (hD : 0 < m.p.planeDisc m.x) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow_iff'.mpr (((Spectral.mem_den_flow_iff_shift (f := fun m : ModelB.Model => m.p.field) (pt := ModelB.Model.x) ModelB.family_isAutonomous).mp (m.p.modelB_unstable_of_disc_pos hx hP hD)))

/-- **Degenerate power balance, negative discriminant: local exponential estimate.** A selected
state on the singular plane with `P(x*) = 0`, `I₀ / C_dc ≠ 0` and `H² + 4G < 0` is locally
exponentially stable in the segment semantics, although it is not an equilibrium: solution
segments spiral into the plane within a time `O(‖x(t₀) − x*‖)`. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_of_disc_neg (m : Model)
    (hx : m.x 2 = 0) (hP : m.p.pccP m.x = 0) (hI : m.p.I0 / m.p.Cdc ≠ 0)
    (hD : m.p.planeDisc m.x < 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  exact mem_den_flow_iff'.mpr (((Spectral.mem_den_flow_iff_shift (f := fun m : ModelB.Model => m.p.field) (pt := ModelB.Model.x) ModelB.family_isAutonomous).mp (m.p.modelB_locallyExponentiallyStable_of_disc_neg hx hP hI hD)))

/-- A converter at rest on the singular plane with zero power: `x* = 0`, so `i_d* = 0` and
`P = 0`; `I₀ = C_dc = 3/2`, `V_dc,ref = −1`, `V_g = k_p = k_i = k_iv = 1`,
`k_pv = R_g = X_g = i_q0 = 0`, `ω_s = ω_g = 0`. Then `G = V_dc,ref = −1`, `H = I₀ / C_dc = 1`,
`D = −3`. -/
def degenerateFocus : Model :=
  ⟨⟨0, 0, 1, 1, 3 / 2, 3 / 2, -1, 0, 1, 1, 0, 0, 0⟩, WithLp.toLp 2 ![0, 0, 0, 0]⟩

/-- The degenerate focus is locally exponentially stable in the segment semantics (it is not an
equilibrium: its DC-link component is `I₀ / C_dc = 1`). -/
@[tmio TM, powerlib_domain] theorem degenerateFocus_mem_den_locallyExponentiallyStable :
    connection% (degenerateFocus ∈ family.den (.flow .locallyExponentiallyStable)) := by
  have h := mem_den_locallyExponentiallyStable_of_disc_neg degenerateFocus
    (by simp [degenerateFocus])
    (by simp [degenerateFocus, ModelBParams.pccP, ModelBParams.idRef, ModelBParams.vgd,
      ModelBParams.vgq])
    (by norm_num [degenerateFocus])
    (by
      simp [degenerateFocus, ModelBParams.planeDisc, ModelBParams.planeH, ModelBParams.planeG,
        ModelBParams.dP0, ModelBParams.dP2, ModelBParams.dP3, ModelBParams.idRef,
        ModelBParams.vgd, ModelBParams.vgq, ModelBParams.field])
  unfold powerlib.TMIO.Statement at h ⊢
  exact h

/-- **Local exponential stability on the singular plane, all but a degenerate set.** For a
selected state with `V_dc* = 0` outside the degenerate set `{P(x*) = 0, I₀ / C_dc ≠ 0, D = 0}`, the
segment-based local exponential estimate holds exactly when the injection crosses the plane
(`I₀ / C_dc ≠ 0`) and either the power term drives `V_dc` into the plane (`P / C_dc < 0`) or the
power balance is degenerate with a focus (`P = 0`, `D < 0`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff_of_Vdc_eq_zero_of_nondegenerate
    (m : Model) (hx : m.x 2 = 0)
    (hnd : m.p.pccP m.x = 0 → m.p.I0 / m.p.Cdc ≠ 0 → m.p.planeDisc m.x ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m ∈ {m : Model | m.p.I0 / m.p.Cdc ≠ 0 ∧ (m.p.pccP m.x / m.p.Cdc < 0 ∨
        (m.p.pccP m.x = 0 ∧ m.p.planeDisc m.x < 0))}) := by
  have hI0 := not_mem_den_locallyExponentiallyStable_of_Vdc_eq_zero_of_I0 m hx
  unfold powerlib.TMIO.Statement at hI0 ⊢
  rw [Set.mem_ofPred_eq]
  by_cases hI : m.p.I0 / m.p.Cdc = 0
  · exact ⟨fun hm => absurd hm (hI0 hI), fun h => absurd hI h.1⟩
  have hC : m.p.Cdc ≠ 0 := by intro h; apply hI; rw [h, div_zero]
  by_cases hP : m.p.pccP m.x = 0
  · have hD := hnd hP hI
    rcases lt_or_gt_of_ne hD with hneg | hpos
    · have h := mem_den_locallyExponentiallyStable_of_disc_neg m hx hP hI hneg
      unfold powerlib.TMIO.Statement at h
      exact ⟨fun _ => ⟨hI, Or.inr ⟨hP, hneg⟩⟩, fun _ => h⟩
    · have h := mem_den_unstable_of_disc_pos m hx hP hpos
      unfold powerlib.TMIO.Statement at h
      constructor
      · intro hm
        exact absurd ((mem_den_flow_iff'.mp hm).lyapunovStable) (mem_den_flow_iff'.mp h)
      · rintro ⟨-, h1 | ⟨-, h2⟩⟩
        · rw [hP, zero_div] at h1; exact absurd h1 (lt_irrefl 0)
        · exact absurd h2 (not_lt.mpr hpos.le)
  · have hPC : m.p.pccP m.x / m.p.Cdc ≠ 0 := div_ne_zero hP hC
    have h := mem_den_locallyExponentiallyStable_iff_of_Vdc_eq_zero m hx hPC
    unfold powerlib.TMIO.Statement at h
    rw [h, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, Or.inl h1⟩
    · rintro ⟨h2, h1 | ⟨h3, -⟩⟩
      · exact ⟨h1, h2⟩
      · exact absurd h3 hP

end ModelB

end powerlib.GFL.DCLink
