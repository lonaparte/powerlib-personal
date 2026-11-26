import theorem.GridTiedConverter.GFM.DCLink.VSMDCBoundary
import theorem.Dynamics.CascadeNode

/-! # The VSM–DC model with its DC-voltage loop on the singular plane `V = 0`

Model boundary.
The VSM–DC family `VSMDC.family` of `theorem/GridTiedConverter/GFM/DCLink/VSMDC.lean`: state
`x = (δ, ω, V, ζ)`, continuous time, autonomous; quasi-static line `P_e(δ) = c₀ + A sin(δ − α)`,
constant EMF magnitude, affine DC source `P_src(V) = P_s + I_s V`, DC node
`C V̇ = (P_src(V) − P_e(δ))/V`, DC-voltage PI loop `P_ref = P_ff + K_p (V − V*) + K_i ζ`,
`ζ̇ = V − V*`; export-positive power; parameters arbitrary reals. On the singular plane `V = 0`
the power term is read with Lean's `x / 0 = 0`: there `V̇ = I_s/C` and `ζ̇ = −V*`
(`Params.field_two_of_V_eq_zero`, `Params.field_three_of_V_eq_zero`). The family reads a model at
`(δ*, 0, V*, ζ*)`, so its selected point lies on the plane exactly when `V* = 0`; this module
treats those models (the physical limit, overmodulation, is reached before `V = 0` and is not
modelled). Excluded as in `VSMDC.lean`. Level: local behaviour at the selected point, including
the segment-based local exponential estimate at points that are not equilibria.

Source: GFM counterpart study, note T7 part (c) (`t7-dcside`, the singular plane, there derived
and not tested; notes outside the repository); the analysis follows the open loop
(`theorem/GridTiedConverter/GFM/DCLink/OpenLoop.lean`: collapse, repulsion, the degenerate
balance, the invariant plane) and the GFL counterparts
`theorem/GridTiedConverter/GFL/DCLink/PLLDC/Stability.lean`, `Collapse.lean`; the generic laws are
`Dynamics.Degenerate.locallyExponentiallyStable_of_collapse`, `unstable_of_repel`,
`unstable_of_cone` (`theorem/Dynamics/Degenerate/PlaneCollapse.lean`) and
`Dynamics.Degenerate.localAsymptoticStable_of_invariantPlane`
(`theorem/GridTiedConverter/GFM/DCLink/InvariantPlane.lean`).

Results.
* The flow on the plane (static, every `V*`): `Params.field_two_of_V_eq_zero` (`V̇ = I_s/C`: the
  plane is crossed iff `I_s/C ≠ 0`), `Params.field_three_of_V_eq_zero` (`ζ̇ = −V*`),
  `Params.field_ne_zero_of_V_eq_zero` (no equilibrium on the plane when `V* ≠ 0`).
* Static support: `Plant.abs_Pe_add_sub_le` (`|P_e(δ + θ) − P_e(δ) − k(δ) θ| ≤ |A| θ²`, the second
  order remainder of the power curve), `Params.exists_contDiff_eq_field_of_sign` (`C¹` fields
  equal to the model on a half space `σ V ≥ s`), `Params.planeQ`
  (`q = (I_s V + P_s − P_e(δ))/C`, `V V̇ = q` off the plane, `Params.field_two_eq_planeQ_div`),
  `Params.planeG` (`G = −k(δ) ω/C`, `q̇ = G + (I_s/C) q/V`,
  `Params.planeQ_lie`), `Params.planeField` (the field read on the plane with `V` relaxed at unit
  rate, `Params.planeField_eq` for `I_s/C = 0`; its `ζ` row is `−V*`).

Family and connection conclusions (selected points with `V* = 0`, `VSMDC.family`).
* `VSMDC.mem_den_locallyExponentiallyStable_of_collapse`: `(P_s − P_e(δ*))/C < 0` and
  `I_s/C ≠ 0` give the segment-based local exponential estimate although the point is not an
  equilibrium (solutions reach the plane in finite time, `d(V²)/dt ≤ −a` nearby).
* `VSMDC.mem_den_unstable_of_repel`: `(P_s − P_e(δ*))/C > 0` is unstable;
  `VSMDC.mem_den_unstable_of_degenerate`: the degenerate balance `P_s = P_e(δ*)` with a crossing
  source current `I_s/C ≠ 0` is unstable (invariant cone, `G(x*) = 0`, discriminant `H² > 0`).
* `VSMDC.not_mem_den_locallyAsymptoticallyStable_of_invariant`: with `I_s/C = 0` the plane is
  invariant and its flow freezes `ζ` (the plane field's `ζ` row vanishes): never locally
  asymptotically stable, whatever the swing.
* **Complete decisions on the plane.** `VSMDC.mem_den_locallyExponentiallyStable_iff_of_V_eq_zero`
  and `VSMDC.mem_den_locallyAsymptoticallyStable_iff_of_V_eq_zero`: with `V* = 0` the point
  satisfies the local exponential estimate iff it is locally asymptotically stable iff
  `I_s/C ≠ 0` and `(P_s − P_e(δ*))/C < 0`;
  `VSMDC.mem_den_lyapunovStable_iff_of_V_eq_zero`: for a crossing source current (`I_s/C ≠ 0`) it
  is Lyapunov stable iff `(P_s − P_e(δ*))/C < 0`.

The invariant plane (`V* = 0`, `I_s/C = 0`): the plane carries the swing with the integrator
frozen (`Params.planeField`: on the plane `P_ref = P_ff + K_i ζ`, `K_p` multiplying `V − V* = 0`;
`ζ̇ = 0`), and the slice `ζ = ζ*` of the plane flow is the open loop's plane flow at the power
reference `P_ff + K_i ζ*` (`Dynamics.lyapunovStable_of_invariantSlice`; read through an open-loop
model whose DC side collapses, `OpenLoop.mem_den_lyapunovStable_iff_of_invariant`).
* Static support: `Params.planeEnergy` (the parametric swing energy
  `ω² + (2/M)[∫(P_e − P_e(δ*)) − K_i (ζ − ζ*)(δ − δ*)] + l (ζ − ζ*)² + V²`, decreasing at the rate
  `2 (D/M) ω² + 2 V²` along the plane flow, `Params.planeEnergy_lie`; positive definite near the
  point for `0 < k(δ*)/M`, `l = 2 (K_i/M)²/(k/M) + 1`, by the cubic bound on the sinusoid's
  potential), `Params.planeFlatEnergy` (`A = 0`, `K_i = 0`), `Params.planeDrift` (`A = 0`: the
  frozen integrator drives `M ω + D (δ − δ*)` at the rate `K_i (ζ − ζ*)`,
  `Params.planeDrift_lie`).
* `VSMDC.mem_den_unstable_of_invariant`: unstable, for every sign of `(P_s − P_e(δ*))/C`, when
  the frozen swing drifts (`(P_ff + K_i ζ* − P_e(δ*))/M ≠ 0`), `D/M < 0`, or `k(δ*)/M ≤ 0` unless
  `A = 0` with `0 < D/M` (saddle, fold `k(δ*) = 0 ≠ A`, undamped flat curve, `M = 0`);
  `VSMDC.mem_den_unstable_of_invariant_flat`: unstable when `A = 0` and `K_i ≠ 0`.
* **Collapse: complete decision.** `VSMDC.mem_den_lyapunovStable_iff_of_invariant`: with
  `(P_s − P_e(δ*))/C < 0`, Lyapunov stable iff `(P_ff + K_i ζ* − P_e(δ*))/M = 0` and either
  `0 ≤ D/M`, `0 < k(δ*)/M` or `A = 0`, `K_i = 0`, `0 < D/M`
  (`Dynamics.Degenerate.lyapunovStable_iff_of_invariantPlane`). With `D = 0` a centre of the
  frozen swing; for `K_i ≠ 0` the integrator only shifts the swing's equilibrium. The repelling
  sign `(P_s − P_e(δ*))/C > 0` is unstable (`VSMDC.mem_den_unstable_of_repel`).
* **The balance `(P_s − P_e(δ*))/C = 0`.** `VSMDC.mem_den_unstable_of_V_eq_zero_of_C_eq_zero`
  (`C = 0`: `V` frozen everywhere drives `ζ`); `VSMDC.mem_den_unstable_of_invariant_degenerate`
  (`K_p = K_i = 0`: the solutions `(δ*, 0, η, ζ* + η t)`; the open loop's first integral holds,
  `V` stays at `η`, and the integrator integrates it). `Params.planeIntegral_lie`: off the plane
  `V² − (2/C)(M ω + D δ − K_p ζ)` changes at the rate `2 (P_s − P_ff − K_i ζ)/C`, i.e.
  `−2 K_i (ζ − ζ*)/C` at the balance: the first integral survives `K_p` (as `K_p ζ̇ = K_p V`) and is
  lost for `K_i ≠ 0`; but the open loop's first-integral law never applies, since the integrator
  reads `V` (`Params.not_forall_field_sub_single`), and with both gains zero the point is unstable.

* **The balance with DC gains.** `VSMDC.mem_den_unstable_of_invariant_flat_degenerate`
  (`(P_s − P_e(δ*))/C = 0`, a flat curve `A = 0`, `K_i = 0`, `D ≠ 0`, any `K_p`: the solutions
  `(δ* + (K_p η/D) t, K_p η/D, η, ζ* + η t)` drift);
  `VSMDC.mem_den_unstable_of_invariant_stiff_degenerate` (`C ≠ 0`, `P_s = P_e(δ*) = P_ff + K_i ζ*`,
  a stiff swing `0 < k(δ*)/M`, `0 ≤ D/M`, DC gains `(K_p, K_i) ≠ (0, 0)` of one sign,
  `K_p K_i ≥ 0`; for `M < 0` read through the converter with every power, gain, inertia, damping
  and capacitance negated, which has the same field): on the side `σ V > 0`,
  `σ (K_p + K_i) C < 0`, the barrier `F θ − Π(θ) − M ω²/2` (`F = K_p V + K_i (ζ − ζ*)`, `Π` the
  potential of the power curve) never decreases, `Ẇ = D ω² − K_p θ ΔP(θ)/(C V) + K_i θ V ≥ 0`, so
  the swing angle stays where `ΔP(θ)/C < 0` and `C V V̇ = −ΔP(θ)` drives `V²` up at a uniform
  rate (`Dynamics.Degenerate.unstable_of_barriers`). With `mem_den_unstable_of_invariant` (an
  unbalanced frozen swing, `M = 0`, a negatively damped, saddle or undamped flat swing) these
  decide the balance except for a stiff swing with DC gains of opposite signs (`K_p K_i < 0`),
  where the rate `D ω² − K_p θ ΔP(θ)/(C V) + K_i θ V` has terms of both signs and the barrier
  argument fails.

The remaining case is decided in `theorem/GridTiedConverter/GFM/DCLink/VSMDCCone.lean`:
`VSMDC.mem_den_unstable_of_invariant_cone` (`C ≠ 0`, the balance, `M ≠ 0`, `k(δ*) ≠ 0`,
`K_p ≠ 0`, any `D` and `K_i`: unstable, an escape along a self-similar cone `V ∝ t³`, `θ ∝ t⁵`
found by a weighted blow-up of the plane), with it `VSMDC.mem_den_unstable_of_invariant_balance`
(the balance of the invariant plane is never stable) and the complete decision
`VSMDC.mem_den_lyapunovStable_iff_of_invariant_plane`.
-/

noncomputable section
namespace powerlib.GFM.DCLink
open Matrix Filter
open powerlib.Dynamics (State coord)

/-- The second-order remainder of the sine: `|sin(θ + w) − sin θ − cos θ w| ≤ w²` (mean value
inequality, `|cos(θ + u) − cos θ| ≤ |u|`). -/
@[tmio T, powerlib_foundation] private theorem abs_sin_add_sub_le (θ w : ℝ) :
    |Real.sin (θ + w) - Real.sin θ - Real.cos θ * w| ≤ w ^ 2 := by
  have hd : ∀ u, HasDerivAt (fun u => Real.sin (θ + u) - u * Real.cos θ)
      (Real.cos (θ + u) - Real.cos θ) u := fun u => by
    have h : HasDerivAt (fun u => Real.sin (θ + u) - u * Real.cos θ)
        (Real.cos (θ + u) * 1 - 1 * Real.cos θ) u :=
      ((Real.hasDerivAt_sin (θ + u)).comp u ((hasDerivAt_id' u).const_add θ)).sub
        ((hasDerivAt_id' u).mul_const (Real.cos θ))
    convert h using 1; ring
  have hb : ∀ u ∈ Set.uIcc 0 w, ‖Real.cos (θ + u) - Real.cos θ‖ ≤ |w| := fun u hu => by
    rw [Real.norm_eq_abs]
    have hu' : |u| ≤ |w| := by
      rcases Set.mem_uIcc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
      · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith
    calc |Real.cos (θ + u) - Real.cos θ| ≤ |θ + u - θ| := Real.abs_cos_sub_cos_le _ _
      _ = |u| := by ring_nf
      _ ≤ |w| := hu'
  have h := (convex_uIcc (0 : ℝ) w).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (hd u).hasDerivWithinAt) hb Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [Real.norm_eq_abs, add_zero, zero_mul, sub_zero] at h
  calc |Real.sin (θ + w) - Real.sin θ - Real.cos θ * w| =
        |Real.sin (θ + w) - w * Real.cos θ - Real.sin θ| := by ring_nf
    _ ≤ |w| * |w| := h
    _ = w ^ 2 := by rw [← sq, sq_abs]

/-- The power curve differs from its tangent by at most `|A| θ²`:
`|P_e(δ + θ) − P_e(δ) − k(δ) θ| ≤ |A| θ²`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem Plant.abs_Pe_add_sub_le (q : Plant) (δ θ : ℝ) :
    |q.Pe (δ + θ) - q.Pe δ - q.k δ * θ| ≤ |q.A| * θ ^ 2 := by
  have h := abs_sin_add_sub_le (δ - q.α) θ
  have he : q.Pe (δ + θ) - q.Pe δ - q.k δ * θ = q.A * (Real.sin (δ - q.α + θ) -
      Real.sin (δ - q.α) - Real.cos (δ - q.α) * θ) := by
    simp only [Plant.Pe, Plant.k]; ring_nf
  rw [he, abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

namespace Params

variable (p : Params)

/-- On the singular plane `V = 0` the DC component is read with Lean's `x / 0 = 0`: `V̇ = I_s/C`.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem field_two_of_V_eq_zero {y : State 4} (hy : y 2 = 0) :
    p.field y 2 = p.Is / p.C := by
  rw [field_apply_two, hy, Plant.nodeRate_zero]

/-- On the singular plane `ζ̇ = −V*`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem field_three_of_V_eq_zero {y : State 4} (hy : y 2 = 0) :
    p.field y 3 = -p.Vref := by
  rw [field_apply_three, hy, zero_sub]

/-- With `V* ≠ 0` the singular plane contains no equilibrium (`ζ̇ = −V*`). Static evidence on the
model. -/
@[tmio M, powerlib_domain] theorem field_ne_zero_of_V_eq_zero (hV : p.Vref ≠ 0) {y : State 4}
    (hy : y 2 = 0) : p.field y ≠ 0 := fun h => by
  have h3 := congrArg (fun z : State 4 => z 3) h
  simp only [PiLp.zero_apply] at h3
  rw [p.field_three_of_V_eq_zero hy, neg_eq_zero] at h3
  exact hV h3

/-- A `C¹` field equal to the model on the half space `σ V ≥ s` (`σ = ±1`, `s > 0`): the
denominator `V` is replaced by `σ Dynamics.regDen s (σ V)`. -/
@[tmio M, powerlib_domain] theorem exists_contDiff_eq_field_of_sign {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {s : ℝ} (hs : 0 < s) :
    ∃ g : State 4 → State 4, ContDiff ℝ 1 g ∧ ∀ y : State 4, s ≤ σ * y 2 → g y = p.field y := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine ⟨fun y => WithLp.toLp 2 ![y 1, p.swingRate (p.Pref (y 2) (y 3)) (y 0) (y 1),
    GFL.DCLink.nodeRate p.C p.Is (p.Ps - p.Pe (y 0)) (σ * Dynamics.regDen s (σ * y 2)),
    y 2 - p.Vref], ?_, ?_⟩
  · have hden : ∀ y ∈ (Set.univ : Set (State 4)), σ * Dynamics.regDen s (σ * y 2) ≠ 0 :=
      fun y _ => by
        have h2 : 0 < Dynamics.regDen s (σ * y 2) :=
          lt_of_lt_of_le (by positivity) (Dynamics.half_le_regDen hs (σ * y 2))
        rcases hσ with rfl | rfl
        · positivity
        · intro h; linarith
    have hP : ContDiff ℝ 1 (fun y : State 4 => p.Ps - p.Pe (y 0)) := by
      unfold Plant.Pe
      fun_prop
    have hR : ContDiff ℝ 1 (fun y : State 4 => σ * Dynamics.regDen s (σ * y 2)) :=
      contDiff_const.mul ((Dynamics.contDiff_regDen s).comp
        (contDiff_const.mul (Dynamics.contDiff_coord 2)))
    rw [contDiff_euclidean]
    intro i
    fin_cases i
    · simpa using Dynamics.contDiff_coord (n := 4) (k := 1) 1
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      unfold Plant.swingRate Pref Plant.Pe
      fun_prop
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      exact contDiffOn_univ.mp (GFL.DCLink.contDiffOn_nodeRate p.C contDiffOn_const
        hP.contDiffOn hR.contDiffOn hden)
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      fun_prop
  · intro y hy
    have hr : σ * Dynamics.regDen s (σ * y 2) = y 2 := by
      rw [Dynamics.regDen_eq hs (by linarith), ← mul_assoc, hσ2, one_mul]
    ext i
    fin_cases i <;> simp [field, Plant.nodeRate, hr]

/-- `q = (I_s V + P_s − P_e(δ))/C`: off the singular plane `V V̇ = q`
(`Params.field_two_eq_planeQ_div`). -/
def planeQ (y : State 4) : ℝ := (p.Is * y 2 + p.Ps - p.Pe (y 0)) / p.C

/-- `G = −k(δ) ω / C`: off the plane `dq/dt = G + (I_s/C) q / V` (`Params.planeQ_lie`). -/
def planeG (y : State 4) : ℝ := -(p.k (y 0) * y 1) / p.C

@[tmio M, powerlib_domain] theorem hasFDerivAt_planeQ (y : State 4) :
    HasFDerivAt p.planeQ ((-p.k (y 0) / p.C) • coord 0 + (p.Is / p.C) • coord 2) y := by
  have h := ((((Dynamics.hasFDerivAt_coord (2 : Fin 4) y).const_mul p.Is).add_const p.Ps).sub
    (p.hasFDerivAt_Pe_comp 0 y)).mul_const p.C⁻¹
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
  · ext v
    simp [div_eq_mul_inv]
    ring
  · simp [planeQ, div_eq_mul_inv]

@[tmio M, powerlib_domain] theorem contDiff_planeQ : ContDiff ℝ 1 p.planeQ := by
  unfold planeQ Plant.Pe
  fun_prop

@[tmio M, powerlib_domain] theorem contDiff_planeG : ContDiff ℝ 1 p.planeG := by
  unfold planeG Plant.k
  fun_prop

/-- Off the singular plane the DC component of the field is `q / V`. -/
@[tmio M, powerlib_domain] theorem field_two_eq_planeQ_div {y : State 4} (hy : y 2 ≠ 0) :
    p.field y 2 = p.planeQ y / y 2 := by
  rw [eq_div_iff hy, mul_comm, field_apply_two]
  have h := p.two_mul_nodeRate (δ := y 0) hy
  rw [planeQ]
  linear_combination h / 2

/-- `dq/dt = G + (I_s/C) q / V` off the singular plane. -/
@[tmio M, powerlib_domain] theorem planeQ_lie {y : State 4} (hy : y 2 ≠ 0) :
    fderiv ℝ p.planeQ y (p.field y) = p.planeG y + p.Is / p.C * (p.planeQ y / y 2) := by
  rw [(p.hasFDerivAt_planeQ y).fderiv, ← p.field_two_eq_planeQ_div hy]
  simp [planeG]
  ring

@[tmio M, powerlib_domain] theorem continuous_field_sub_single :
    Continuous fun y => p.field y - p.field y 2 • EuclideanSpace.single 2 (1 : ℝ) := by
  have e : (fun y => p.field y - p.field y 2 • EuclideanSpace.single 2 (1 : ℝ)) =
      fun y : State 4 => WithLp.toLp 2 ![y 1, p.swingRate (p.Pref (y 2) (y 3)) (y 0) (y 1), 0,
        y 2 - p.Vref] := by
    funext y
    ext i
    fin_cases i <;> simp [field]
  rw [e]
  have h : ContDiff ℝ 1 (fun y : State 4 => WithLp.toLp 2
      ![y 1, p.swingRate (p.Pref (y 2) (y 3)) (y 0) (y 1), 0, y 2 - p.Vref]) := by
    rw [contDiff_euclidean]
    intro i
    fin_cases i
    · simpa using Dynamics.contDiff_coord (n := 4) (k := 1) 1
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      unfold Plant.swingRate Pref Plant.Pe
      fun_prop
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      exact contDiff_const
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      fun_prop
  exact h.continuous

/-- The field read on the singular plane, with `V` relaxed at unit rate:
`(ω, ω̇ at P_ref(0, ζ), −V, −V*)`. For `I_s/C = 0` it is `y ↦ f(y − V e_V) − V e_V`
(`Params.planeField_eq`). -/
def planeField (y : State 4) : State 4 :=
  WithLp.toLp 2 ![y 1, p.swingRate (p.Pref 0 (y 3)) (y 0) (y 1), -y 2, -p.Vref]

@[tmio M, powerlib_domain] theorem planeField_eq (hI : p.Is / p.C = 0) (y : State 4) :
    p.planeField y = p.field (y - y 2 • EuclideanSpace.single 2 (1 : ℝ)) -
      y 2 • EuclideanSpace.single 2 (1 : ℝ) := by
  ext i
  fin_cases i <;> simp [planeField, field, Plant.nodeRate_zero, hI]

@[tmio M, powerlib_domain] theorem contDiff_planeField : ContDiff ℝ 1 p.planeField := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · simpa [planeField] using Dynamics.contDiff_coord (n := 4) (k := 1) 1
  · simp only [planeField, Fin.mk_one, Fin.isValue, PiLp.toLp_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    unfold Plant.swingRate Pref Plant.Pe
    fun_prop
  · simp only [planeField, Fin.reduceFinMk, Fin.isValue, PiLp.toLp_apply, Matrix.cons_val]
    fun_prop
  · simp only [planeField, Fin.reduceFinMk, Fin.isValue, PiLp.toLp_apply, Matrix.cons_val]
    exact contDiff_const

end Params

namespace VSMDC

@[tmio TM, powerlib_domain] private theorem mem_den_flow_iff {m : Model} {P : Flow.Property} :
    m ∈ family.den (.flow P) ↔ P.holds m.p.field m.point :=
  Spectral.mem_den_flow_iff_shift (f := fun m : Model => m.p.field) (pt := Model.point)
    (Spectral.localFamily_isAutonomous _ _ _)

@[tmio M, powerlib_domain] private theorem point_two (m : Model) (hV : m.p.Vref = 0) :
    m.point 2 = 0 := by
  simp [Model.point, hV]

/-- Near a selected point of the singular plane with `(P_s − P_e(δ*))/C < 0` the field collapses
onto the plane (`2 V V̇ ≤ −a` off it) and its components off `V` are bounded. -/
@[tmio M, powerlib_domain] private theorem exists_collapse (m : Model) (hV : m.p.Vref = 0)
    (hP : (m.p.Ps - m.p.Pe m.δ) / m.p.C < 0) :
    ∃ ρ a B : ℝ, 0 < ρ ∧ 0 < a ∧
      (∀ y : State 4, ‖y - m.point‖ < ρ → y 2 ≠ 0 → 2 * y 2 * m.p.field y 2 ≤ -a) ∧
      ∀ y : State 4, ‖y - m.point‖ < ρ →
        ‖m.p.field y - m.p.field y 2 • EuclideanSpace.single 2 (1 : ℝ)‖ ≤ B := by
  set g : State 4 → ℝ := fun y => 2 * (m.p.Is * y 2 + m.p.Ps - m.p.Pe (y 0)) / m.p.C with hg
  have hgc : Continuous g := by
    simp only [hg, Plant.Pe]
    fun_prop
  have hgx : g m.point = 2 * ((m.p.Ps - m.p.Pe m.δ) / m.p.C) := by
    simp only [hg, Model.point, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, hV]
    ring
  set a := -(g m.point) / 2 with ha
  have ha0 : 0 < a := by rw [ha, hgx]; linarith
  obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.continuous_iff.mp hgc m.point a ha0
  obtain ⟨B, hB⟩ := (isCompact_closedBall m.point 1).exists_bound_of_continuousOn
    m.p.continuous_field_sub_single.continuousOn
  refine ⟨min ρ₁ 1, a, B, lt_min hρ₁ one_pos, ha0, fun y hy hy2 => ?_, fun y hy => ?_⟩
  · rw [Params.field_apply_two, m.p.two_mul_nodeRate hy2]
    have h1 := hball y (by rw [dist_eq_norm]; exact lt_of_lt_of_le hy (min_le_left _ _))
    rw [Real.dist_eq] at h1
    have h2 := (abs_lt.mp h1).2
    show g y ≤ -a
    linarith
  · exact hB y (by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact (lt_of_lt_of_le hy (min_le_right _ _)).le)

/-- **Collapse onto the singular plane.** A selected point with `V* = 0` at which the DC node is
driven into the plane from both sides (`(P_s − P_e(δ*))/C < 0`) and the source current crosses it
(`I_s/C ≠ 0`) satisfies the segment-based local exponential estimate although it is not an
equilibrium (generic `Dynamics.Degenerate.locallyExponentiallyStable_of_collapse`): solutions
cease, they do not converge. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_of_collapse (m : Model)
    (hV : m.p.Vref = 0) (hP : (m.p.Ps - m.p.Pe m.δ) / m.p.C < 0) (hI : m.p.Is / m.p.C ≠ 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  obtain ⟨ρ, a, B, hρ, ha, hcol, hbound⟩ := exists_collapse m hV hP
  exact Dynamics.Degenerate.locallyExponentiallyStable_of_collapse 2 (point_two m hV) hρ ha hcol
    (fun y _ hy2 => by rw [m.p.field_two_of_V_eq_zero hy2]; exact hI) hbound

/-- **Repulsion from the singular plane.** A selected point with `V* = 0` at which
`(P_s − P_e(δ*))/C > 0` is unstable: `V²` grows near it (generic
`Dynamics.Degenerate.unstable_of_repel`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_repel (m : Model) (hV : m.p.Vref = 0)
    (hP : 0 < (m.p.Ps - m.p.Pe m.δ) / m.p.C) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  set g : State 4 → ℝ := fun y => 2 * (m.p.Is * y 2 + m.p.Ps - m.p.Pe (y 0)) / m.p.C with hg
  have hgc : Continuous g := by
    simp only [hg, Plant.Pe]
    fun_prop
  have hgx : g m.point = 2 * ((m.p.Ps - m.p.Pe m.δ) / m.p.C) := by
    simp only [hg, Model.point, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, hV]
    ring
  set a := g m.point / 2 with ha
  have ha0 : 0 < a := by rw [ha, hgx]; linarith
  obtain ⟨ρ, hρ, hball⟩ := Metric.continuous_iff.mp hgc m.point a ha0
  refine Dynamics.Degenerate.unstable_of_repel 2 (point_two m hV) hρ ha0 (fun y hy hy2 => ?_)
    (fun s hs => ?_)
  · rw [Params.field_apply_two, m.p.two_mul_nodeRate hy2]
    have h1 := hball y (by rw [dist_eq_norm]; exact hy)
    rw [Real.dist_eq] at h1
    have h2 := (abs_lt.mp h1).1
    show a ≤ g y
    linarith
  · obtain ⟨g, hg, hgf⟩ := m.p.exists_contDiff_eq_field_of_sign (Or.inl rfl) hs
    exact ⟨g, hg, fun y _ hy2 => hgf y (by rw [one_mul]; exact hy2)⟩

/-- **Degenerate balance, crossing source current: instability.** A selected point with `V* = 0`,
`P_s = P_e(δ*)` and `H = I_s/C ≠ 0` is unstable: on the side `σ = sign H` the cone
`{σ V > 0, q ≥ (|H|/2) σ V}` is entered through its boundary, where
`dq/dt − (|H|/2) σ V̇ = G + H²/4 > 0` near the point (`G(x*) = 0`), and in it `σ V̇ ≥ |H|/2`
(generic `Dynamics.Degenerate.unstable_of_cone`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_degenerate (m : Model)
    (hV : m.p.Vref = 0) (hP : m.p.Ps = m.p.Pe m.δ) (hI : m.p.Is / m.p.C ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  set H := m.p.Is / m.p.C with hH
  obtain ⟨σ, hσ, hσH⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ σ * H = |H| := by
    by_cases h : 0 ≤ H
    · exact ⟨1, Or.inl rfl, by rw [one_mul, abs_of_nonneg h]⟩
    · exact ⟨-1, Or.inr rfl, by rw [abs_of_neg (not_le.mp h)]; ring⟩
  have hσ2 : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hHa : 0 < |H| := abs_pos.mpr hI
  set μ := |H| / 2 with hμ
  have hμ0 : 0 < μ := by positivity
  have hx0 : m.point 0 = m.δ := by simp [Model.point]
  have hx1 : m.point 1 = 0 := by simp [Model.point]
  have hx2 := point_two m hV
  have hGx : m.p.planeG m.point = 0 := by simp [Params.planeG, hx1]
  obtain ⟨ρ, hρ, hball⟩ := Metric.continuous_iff.mp m.p.contDiff_planeG.continuous m.point
    (μ ^ 2) (by positivity)
  set W : State 4 → ℝ := fun y => m.p.planeQ y - μ * σ * y 2 with hW
  have hWc : ContDiff ℝ 1 W :=
    m.p.contDiff_planeQ.sub (contDiff_const.mul (Dynamics.contDiff_coord 2))
  have hWd : ∀ y : State 4, HasFDerivAt W ((-m.p.k (y 0) / m.p.C) • coord 0 +
      (H - μ * σ) • coord 2) y := by
    intro y
    have h := (m.p.hasFDerivAt_planeQ y).sub
      ((Dynamics.hasFDerivAt_coord (2 : Fin 4) y).const_mul (μ * σ))
    refine h.congr_fderiv ?_
    ext v
    simp only [_root_.add_apply, _root_.smul_apply, _root_.sub_apply, Dynamics.coord_apply,
      smul_eq_mul, hH]
    ring
  have hW0 : W m.point = 0 := by simp [hW, Params.planeQ, hx0, hx2, hP]
  have hy2 : ∀ y : State 4, 0 < σ * y 2 → y 2 ≠ 0 := fun y hy h => by
    rw [h, mul_zero] at hy
    exact lt_irrefl _ hy
  refine Dynamics.Degenerate.unstable_of_cone 2 hσ hρ hμ0 hWc hx2 hW0 ?_ ?_
    (WithLp.toLp 2 ![-m.p.k m.δ / m.p.C, 0, σ, 0]) ?_ ?_ ?_
  · intro y _ hy hWy
    rw [m.p.field_two_eq_planeQ_div (hy2 y hy)]
    have hq : μ * σ * y 2 ≤ m.p.planeQ y := by simp only [hW] at hWy; linarith
    have hσy : σ * (m.p.planeQ y / y 2) * (σ * y 2) = m.p.planeQ y := by
      field_simp [hy2 y hy]
      linear_combination m.p.planeQ y * hσ2
    have h1 : μ * (σ * y 2) ≤ σ * (m.p.planeQ y / y 2) * (σ * y 2) := by
      rw [hσy]; linarith
    exact le_of_mul_le_mul_right h1 hy
  · intro y hyx hy hWy
    rw [(hWd y).fderiv]
    have hq : m.p.planeQ y = μ * σ * y 2 := by simp only [hW] at hWy; linarith
    have hf2 : m.p.field y 2 = μ * σ := by
      rw [m.p.field_two_eq_planeQ_div (hy2 y hy), hq]
      field_simp [hy2 y hy]
    have hrate := hball y (by rw [dist_eq_norm]; exact hyx)
    rw [Real.dist_eq, hGx, sub_zero] at hrate
    have hrate' := (abs_lt.mp hrate).1
    have hlie : ((-m.p.k (y 0) / m.p.C) • coord 0 + (H - μ * σ) • coord 2 :
        State 4 →L[ℝ] ℝ) (m.p.field y) = m.p.planeG y + μ ^ 2 := by
      simp only [_root_.add_apply, _root_.smul_apply, Dynamics.coord_apply, smul_eq_mul, hf2]
      rw [Params.field_apply_zero, Params.planeG]
      have : H * σ = 2 * μ := by rw [mul_comm, hσH, hμ]; ring
      linear_combination μ * this - μ ^ 2 * hσ2
    rw [hlie]
    linarith
  · simp [hσ2]
  · rw [(hWd m.point).fderiv]
    simp only [_root_.add_apply, _root_.smul_apply, Dynamics.coord_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, hx0]
    have : (H - μ * σ) * σ = |H| / 2 := by
      rw [sub_mul, mul_assoc, hσ2, mul_comm, hσH, hμ]; ring
    rw [this]
    nlinarith [sq_nonneg (-m.p.k m.δ / m.p.C)]
  · intro s hs
    obtain ⟨g, hg, hgf⟩ := m.p.exists_contDiff_eq_field_of_sign hσ hs
    exact ⟨g, hg, fun y _ hy => hgf y hy⟩

/-- **An invariant singular plane freezes the integrator.** With `V* = 0` and a source current
that does not cross the plane (`I_s/C = 0`, Lean's `x / 0 = 0` reading `V̇ = 0` there), local
asymptotic stability of the model passes to the plane field
(`Dynamics.Degenerate.localAsymptoticStable_of_invariantPlane`, `Params.planeField_eq`), whose `ζ`
row vanishes: `ζ` is conserved, so the point is never locally asymptotically stable
(`Dynamics.not_localAsymptoticStable_of_linear_lie_nonpos`). -/
@[tmio TM, powerlib_domain] theorem not_mem_den_locallyAsymptoticallyStable_of_invariant
    (m : Model) (hV : m.p.Vref = 0) (hI : m.p.Is / m.p.C = 0) :
    connection% (m ∉ family.den (.flow .locallyAsymptoticallyStable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  intro hm
  have hg := Dynamics.Degenerate.localAsymptoticStable_of_invariantPlane 2 (point_two m hV)
    (fun y hy => by rw [m.p.field_two_of_V_eq_zero hy, hI]) (m.p.planeField_eq hI) hm
  refine Dynamics.not_localAsymptoticStable_of_linear_lie_nonpos m.p.contDiff_planeField
    (ℓ := coord 3) (fun h => ?_) (Eventually.of_forall fun y => ?_) hg
  · have := congrArg (fun L : State 4 →L[ℝ] ℝ => L (EuclideanSpace.single 3 1)) h
    simp at this
  · simp [Params.planeField, hV]

/-- **Local exponential stability on the singular plane.** For a selected point with `V* = 0`
the segment-based local exponential estimate holds exactly when the source current crosses the
plane and the power term drives `V` into it, `I_s/C ≠ 0` and `(P_s − P_e(δ*))/C < 0`
(`mem_den_locallyExponentiallyStable_of_collapse`; `> 0` repels, `mem_den_unstable_of_repel`;
`= 0` is the degenerate balance, `mem_den_unstable_of_degenerate`; `I_s/C = 0` freezes `ζ`,
`not_mem_den_locallyAsymptoticallyStable_of_invariant`). -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyExponentiallyStable_iff_of_V_eq_zero
    (m : Model) (hV : m.p.Vref = 0) :
    connection% (m ∈ family.den (.flow .locallyExponentiallyStable) ↔
      m.p.Is / m.p.C ≠ 0 ∧ (m.p.Ps - m.p.Pe m.δ) / m.p.C < 0) := by
  have hcol := mem_den_locallyExponentiallyStable_of_collapse m hV
  have hinv := not_mem_den_locallyAsymptoticallyStable_of_invariant m hV
  unfold TMIO.Statement at hcol hinv ⊢
  refine ⟨fun hm => ?_, fun h => hcol h.2 h.1⟩
  have hI : m.p.Is / m.p.C ≠ 0 := fun hI =>
    hinv hI (Spectral.den_locallyExponentiallyStable_subset_las hm)
  have hC : m.p.C ≠ 0 := fun h => hI (by rw [h, div_zero])
  refine ⟨hI, ?_⟩
  have hls := Spectral.den_locallyExponentiallyStable_subset_lyapunovStable hm
  rcases lt_trichotomy ((m.p.Ps - m.p.Pe m.δ) / m.p.C) 0 with h | h | h
  · exact h
  · rw [div_eq_zero_iff, or_iff_left hC, sub_eq_zero] at h
    have hu := mem_den_unstable_of_degenerate m hV h hI
    unfold TMIO.Statement at hu
    exact absurd hls (Spectral.not_mem_den_lyapunovStable_of_unstable hu)
  · have hu := mem_den_unstable_of_repel m hV h
    unfold TMIO.Statement at hu
    exact absurd hls (Spectral.not_mem_den_lyapunovStable_of_unstable hu)

/-- **Local asymptotic stability on the singular plane**: with `V* = 0`, exactly the conditions
of the local exponential estimate, `I_s/C ≠ 0` and `(P_s − P_e(δ*))/C < 0`. -/
@[tmio TM, powerlib_domain] theorem mem_den_locallyAsymptoticallyStable_iff_of_V_eq_zero
    (m : Model) (hV : m.p.Vref = 0) :
    connection% (m ∈ family.den (.flow .locallyAsymptoticallyStable) ↔
      m.p.Is / m.p.C ≠ 0 ∧ (m.p.Ps - m.p.Pe m.δ) / m.p.C < 0) := by
  have hles := mem_den_locallyExponentiallyStable_iff_of_V_eq_zero m hV
  have hinv := not_mem_den_locallyAsymptoticallyStable_of_invariant m hV
  unfold TMIO.Statement at hles hinv ⊢
  refine ⟨fun hm => ?_, fun h => Spectral.den_locallyExponentiallyStable_subset_las
    (hles.mpr h)⟩
  have hI : m.p.Is / m.p.C ≠ 0 := fun hI => hinv hI hm
  have hC : m.p.C ≠ 0 := fun h => hI (by rw [h, div_zero])
  refine ⟨hI, ?_⟩
  have hls := Spectral.den_las_subset_lyapunovStable hm
  rcases lt_trichotomy ((m.p.Ps - m.p.Pe m.δ) / m.p.C) 0 with h | h | h
  · exact h
  · rw [div_eq_zero_iff, or_iff_left hC, sub_eq_zero] at h
    have hu := mem_den_unstable_of_degenerate m hV h hI
    unfold TMIO.Statement at hu
    exact absurd hls (Spectral.not_mem_den_lyapunovStable_of_unstable hu)
  · have hu := mem_den_unstable_of_repel m hV h
    unfold TMIO.Statement at hu
    exact absurd hls (Spectral.not_mem_den_lyapunovStable_of_unstable hu)

/-- **Lyapunov stability on the singular plane, crossing source current.** For a selected point
with `V* = 0` and `I_s/C ≠ 0`, Lyapunov stability holds exactly when
`(P_s − P_e(δ*))/C < 0` (the collapse gives the local exponential estimate; repulsion and the
degenerate balance are unstable). -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff_of_V_eq_zero (m : Model)
    (hV : m.p.Vref = 0) (hI : m.p.Is / m.p.C ≠ 0) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      (m.p.Ps - m.p.Pe m.δ) / m.p.C < 0) := by
  have hcol := mem_den_locallyExponentiallyStable_of_collapse m hV
  unfold TMIO.Statement at hcol ⊢
  have hC : m.p.C ≠ 0 := fun h => hI (by rw [h, div_zero])
  refine ⟨fun hls => ?_, fun h => Spectral.den_locallyExponentiallyStable_subset_lyapunovStable
    (hcol h hI)⟩
  rcases lt_trichotomy ((m.p.Ps - m.p.Pe m.δ) / m.p.C) 0 with h | h | h
  · exact h
  · rw [div_eq_zero_iff, or_iff_left hC, sub_eq_zero] at h
    have hu := mem_den_unstable_of_degenerate m hV h hI
    unfold TMIO.Statement at hu
    exact absurd hls (Spectral.not_mem_den_lyapunovStable_of_unstable hu)
  · have hu := mem_den_unstable_of_repel m hV h
    unfold TMIO.Statement at hu
    exact absurd hls (Spectral.not_mem_den_lyapunovStable_of_unstable hu)

end VSMDC


/-! ## Lyapunov stability on the invariant singular plane

With `V* = 0` and `I_s/C = 0` the plane `V = 0` is invariant (`V̇ = I_s/C = 0` there) and its flow
is `Params.planeField`: on the plane the power reference is `P_ff + K_i ζ` (`K_p` multiplies
`V − V* = 0`), the integrator is frozen (`ζ̇ = V − V* = 0`) and `V` relaxes. -/

namespace Params

variable (p : Params)

/-- Twice the parametric swing energy about `(δ*, 0, 0, ζ*)`, the integrator frozen, with weight
`l` on it: `ω² + (2/M) [∫_{δ*}^{δ} (P_e − P_e(δ*)) − K_i (ζ − ζ*)(δ − δ*)] + l (ζ − ζ*)² + V²`. -/
def planeEnergy (δs ζs l : ℝ) (y : State 4) : ℝ :=
  y 1 ^ 2 + 2 * (p.A / p.M) *
      (Real.cos (δs - p.α) - Real.cos (y 0 - p.α) - Real.sin (δs - p.α) * (y 0 - δs)) -
    2 * (p.Ki / p.M) * (y 3 - ζs) * (y 0 - δs) + l * (y 3 - ζs) ^ 2 + y 2 ^ 2

@[tmio M, powerlib_domain] theorem contDiff_planeEnergy (δs ζs l : ℝ) :
    ContDiff ℝ 1 (p.planeEnergy δs ζs l) := by
  unfold planeEnergy
  fun_prop

/-- **The parametric energy does not increase** along the plane flow (`V* = 0`, `M ≠ 0`, the
swing balanced at the frozen integrator, `P_ff + K_i ζ* = P_e(δ*)`):
`d/dt planeEnergy = −2 (D/M) ω² − 2 V²`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem planeEnergy_lie (hV : p.Vref = 0) (hM : p.M ≠ 0)
    {δs ζs : ℝ} (hb : p.Pff + p.Ki * ζs = p.Pe δs) (l : ℝ) (y : State 4) :
    fderiv ℝ (p.planeEnergy δs ζs l) y (p.planeField y) =
      -2 * (p.D / p.M) * y 1 ^ 2 - 2 * y 2 ^ 2 := by
  have h0 := Dynamics.hasFDerivAt_coord 0 y
  have h1 := Dynamics.hasFDerivAt_coord 1 y
  have h2 := Dynamics.hasFDerivAt_coord 2 y
  have h3 := Dynamics.hasFDerivAt_coord 3 y
  have h := (((((h1.pow 2).add ((((hasFDerivAt_const (Real.cos (δs - p.α)) y).sub
    (h0.sub_const p.α).cos).sub ((h0.sub_const δs).const_mul (Real.sin (δs - p.α)))).const_mul
    (2 * (p.A / p.M)))).sub (((h3.sub_const ζs).const_mul (2 * (p.Ki / p.M))).mul
    (h0.sub_const δs))).add (((h3.sub_const ζs).pow 2).const_mul l)).add (h2.pow 2))
  have hE : HasFDerivAt (p.planeEnergy δs ζs l) _ y := h
  rw [hE.fderiv]
  have hP : p.Pff = p.c0 + p.A * Real.sin (δs - p.α) - p.Ki * ζs := by
    rw [Plant.Pe] at hb; linarith
  simp [planeField, Pref, Plant.swingRate, Plant.Pe, hV, hP]
  field_simp
  ring

/-- Twice the energy of the flat curve without integral gain on the plane:
`(ω + (D/M)(δ − δ*))² + ω² + V² + (ζ − ζ*)²`. -/
def planeFlatEnergy (δs ζs : ℝ) (y : State 4) : ℝ :=
  (y 1 + p.D / p.M * (y 0 - δs)) ^ 2 + y 1 ^ 2 + y 2 ^ 2 + (y 3 - ζs) ^ 2

@[tmio M, powerlib_domain] theorem contDiff_planeFlatEnergy (δs ζs : ℝ) :
    ContDiff ℝ 1 (p.planeFlatEnergy δs ζs) := by
  unfold planeFlatEnergy
  fun_prop

/-- On the flat curve (`A = 0`) without integral gain (`K_i = 0`), balanced (`P_ff = c₀`),
`d/dt planeFlatEnergy = −2 (D/M) ω² − 2 V²` along the plane flow (`V* = 0`, `M ≠ 0`). Static
evidence on the model. -/
@[tmio M, powerlib_domain] theorem planeFlatEnergy_lie (hV : p.Vref = 0) (hM : p.M ≠ 0)
    (hA : p.A = 0) (hKi : p.Ki = 0) (hb : p.Pff = p.c0) (δs ζs : ℝ) (y : State 4) :
    fderiv ℝ (p.planeFlatEnergy δs ζs) y (p.planeField y) =
      -2 * (p.D / p.M) * y 1 ^ 2 - 2 * y 2 ^ 2 := by
  have h0 := Dynamics.hasFDerivAt_coord 0 y
  have h1 := Dynamics.hasFDerivAt_coord 1 y
  have h2 := Dynamics.hasFDerivAt_coord 2 y
  have h3 := Dynamics.hasFDerivAt_coord 3 y
  have h := ((((h1.add ((h0.sub_const δs).const_mul (p.D / p.M))).pow 2).add (h1.pow 2)).add
    (h2.pow 2)).add ((h3.sub_const ζs).pow 2)
  have hE : HasFDerivAt (p.planeFlatEnergy δs ζs) _ y := h
  rw [hE.fderiv]
  simp [planeField, Pref, Plant.swingRate, Plant.Pe, hV, hA, hKi, hb]
  field_simp
  ring

/-- The integrator's Chetaev function on the flat curve: `K_i (ζ − ζ*)(M ω + D (δ − δ*))`. -/
def planeDrift (δs ζs : ℝ) (y : State 4) : ℝ := p.Ki * (y 3 - ζs) * (p.M * y 1 + p.D * (y 0 - δs))

/-- On the flat curve (`A = 0`), balanced at the frozen integrator (`P_ff + K_i ζ* = c₀`),
`M ω + D (δ − δ*)` is driven by the frozen integrator at the rate `K_i (ζ − ζ*)`:
`d/dt planeDrift = K_i² (ζ − ζ*)²` along the plane flow (`V* = 0`, `M ≠ 0`). Static evidence on
the model. -/
@[tmio M, powerlib_domain] theorem planeDrift_lie (hV : p.Vref = 0) (hM : p.M ≠ 0)
    (hA : p.A = 0) {δs ζs : ℝ} (hb : p.Pff + p.Ki * ζs = p.c0) (y : State 4) :
    fderiv ℝ (p.planeDrift δs ζs) y (p.planeField y) = p.Ki ^ 2 * (y 3 - ζs) ^ 2 := by
  have h0 := Dynamics.hasFDerivAt_coord 0 y
  have h1 := Dynamics.hasFDerivAt_coord 1 y
  have h3 := Dynamics.hasFDerivAt_coord 3 y
  have h := ((h3.sub_const ζs).const_mul p.Ki).mul ((h1.const_mul p.M).add
    ((h0.sub_const δs).const_mul p.D))
  have hE : HasFDerivAt (p.planeDrift δs ζs) _ y := h
  rw [hE.fderiv]
  have hP : p.Pff = p.c0 - p.Ki * ζs := by linarith
  simp [planeField, Pref, Plant.swingRate, Plant.Pe, hV, hA, hP]
  field_simp
  ring

end Params

namespace VSMDC

@[tmio M, powerlib_domain] private theorem point_apply_of_V_eq_zero (m : Model)
    (hV : m.p.Vref = 0) :
    m.point 0 = m.δ ∧ m.point 1 = 0 ∧ m.point 2 = 0 ∧ m.point 3 = m.ζ := by
  simp [Model.point, hV]

/-- The sinusoid's potential about `θ` is its quadratic part up to `|u|³`: for `|u| ≤ 1`,
`|cos θ − cos(θ + u) − u sin θ − (u²/2) cos θ| ≤ |u|³` (Mathlib's `Real.cos_bound`,
`Real.sin_bound`). -/
@[tmio M, powerlib_domain] private theorem pot_cubic {θ u : ℝ} (hu : |u| ≤ 1) :
    |Real.cos θ - Real.cos (θ + u) - Real.sin θ * u - Real.cos θ * u ^ 2 / 2| ≤ |u| ^ 3 := by
  have e : Real.cos θ - Real.cos (θ + u) - Real.sin θ * u - Real.cos θ * u ^ 2 / 2 =
      -Real.cos θ * (Real.cos u - (1 - u ^ 2 / 2)) +
        Real.sin θ * (Real.sin u - (u - u ^ 3 / 6)) - Real.sin θ * (u ^ 3 / 6) := by
    rw [Real.cos_add]; ring
  rw [e]
  have hc1 := Real.abs_cos_le_one θ
  have hs1 := Real.abs_sin_le_one θ
  have hu0 := abs_nonneg u
  have h4 : |u| ^ 4 ≤ |u| ^ 3 := pow_le_pow_of_le_one hu0 hu (by norm_num)
  have h5 : |u| ^ 5 ≤ |u| ^ 3 := pow_le_pow_of_le_one hu0 hu (by norm_num)
  have t1 : |-Real.cos θ * (Real.cos u - (1 - u ^ 2 / 2))| ≤ |u| ^ 4 * (5 / 96) := by
    rw [abs_mul, abs_neg]
    exact (mul_le_of_le_one_left (abs_nonneg _) hc1).trans (Real.cos_bound hu)
  have t2 : |Real.sin θ * (Real.sin u - (u - u ^ 3 / 6))| ≤ |u| ^ 5 / 100 := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hs1).trans (Real.sin_bound hu)
  have t3 : |Real.sin θ * (u ^ 3 / 6)| ≤ |u| ^ 3 / 6 := by
    rw [abs_mul, abs_div, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    exact mul_le_of_le_one_left (by positivity) hs1
  have t12 := abs_add_le (-Real.cos θ * (Real.cos u - (1 - u ^ 2 / 2)))
    (Real.sin θ * (Real.sin u - (u - u ^ 3 / 6)))
  have t := abs_sub (-Real.cos θ * (Real.cos u - (1 - u ^ 2 / 2)) +
    Real.sin θ * (Real.sin u - (u - u ^ 3 / 6))) (Real.sin θ * (u ^ 3 / 6))
  have h3 : 0 ≤ |u| ^ 3 := by positivity
  linarith

/-- **The plane flow of a stiff, damped swing is Lyapunov stable.** At a selected point with
`V* = 0`, the swing balanced at the frozen integrator (`P_ff + K_i ζ* = P_e(δ*)`),
`0 < k(δ*)/M` and `0 ≤ D/M`, the parametric energy `Params.planeEnergy` with
`l = 2 (K_i/M)²/(k/M) + 1` is positive definite on the ball of radius
`min 1 ((k/M)/(8 (|A/M| + 1)))` (`pot_cubic`) and does not increase (`Params.planeEnergy_lie`). -/
@[tmio TM, powerlib_domain] private theorem lyapunovStable_planeField_of_swing (m : Model)
    (hV : m.p.Vref = 0) (hb : m.p.Pff + m.p.Ki * m.ζ = m.p.Pe m.δ)
    (hk : 0 < m.p.k m.δ / m.p.M) (hD : 0 ≤ m.p.D / m.p.M) :
    LyapunovStable m.p.planeField m.point := by
  obtain ⟨p0, p1, p2, p3⟩ := point_apply_of_V_eq_zero m hV
  have hM : m.p.M ≠ 0 := fun h => by simp [h] at hk
  obtain ⟨a, ha⟩ : ∃ a, a = m.p.k m.δ / m.p.M := ⟨_, rfl⟩
  obtain ⟨b, hbb⟩ : ∃ b, b = m.p.Ki / m.p.M := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = m.p.A / m.p.M := ⟨_, rfl⟩
  rw [← ha] at hk
  have hK0 : 0 < |c| + 1 := by positivity
  have hr0 : 0 < min 1 (a / (8 * (|c| + 1))) := lt_min one_pos (by positivity)
  refine lyapunov_stable (V := m.p.planeEnergy m.δ m.ζ (2 * b ^ 2 / a + 1))
    (D := Metric.ball m.point (min 1 (a / (8 * (|c| + 1))))) (by norm_num)
    ⟨Metric.isOpen_ball, Metric.mem_ball_self hr0, (m.p.contDiff_planeEnergy _ _ _).continuous,
      (m.p.contDiff_planeEnergy _ _ _).differentiable one_ne_zero, ?_, fun y hy hne => ?_,
      fun y _ => ?_⟩
  · simp [Params.planeEnergy, p0, p1, p2, p3]
  · rw [Metric.mem_ball, dist_eq_norm] at hy
    have bu := (Dynamics.abs_coord_sub_le m.point y 0).trans_lt hy
    rw [p0] at bu
    have hu1 : |y 0 - m.δ| ≤ 1 := (bu.trans_le (min_le_left _ _)).le
    have hur : |y 0 - m.δ| * (8 * (|c| + 1)) ≤ a :=
      (le_div_iff₀ (by positivity)).mp (bu.trans_le (min_le_right _ _)).le
    have hpot := pot_cubic (θ := m.δ - m.p.α) hu1
    rw [show m.δ - m.p.α + (y 0 - m.δ) = y 0 - m.p.α by ring] at hpot
    have hka : c * Real.cos (m.δ - m.p.α) = a := by rw [hc, ha, Plant.k]; ring
    have hR : a / 2 * (y 0 - m.δ) ^ 2 - |c| * |y 0 - m.δ| ^ 3 ≤
        c * (Real.cos (m.δ - m.p.α) - Real.cos (y 0 - m.p.α) -
          Real.sin (m.δ - m.p.α) * (y 0 - m.δ)) := by
      have h1 : |c * (Real.cos (m.δ - m.p.α) - Real.cos (y 0 - m.p.α) -
          Real.sin (m.δ - m.p.α) * (y 0 - m.δ) - Real.cos (m.δ - m.p.α) * (y 0 - m.δ) ^ 2 / 2)| ≤
          |c| * |y 0 - m.δ| ^ 3 := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hpot (abs_nonneg c)
      have h2 := neg_abs_le (c * (Real.cos (m.δ - m.p.α) - Real.cos (y 0 - m.p.α) -
          Real.sin (m.δ - m.p.α) * (y 0 - m.δ) - Real.cos (m.δ - m.p.α) * (y 0 - m.δ) ^ 2 / 2))
      have h3 : c * (Real.cos (m.δ - m.p.α) - Real.cos (y 0 - m.p.α) -
          Real.sin (m.δ - m.p.α) * (y 0 - m.δ) - Real.cos (m.δ - m.p.α) * (y 0 - m.δ) ^ 2 / 2) =
          c * (Real.cos (m.δ - m.p.α) - Real.cos (y 0 - m.p.α) -
            Real.sin (m.δ - m.p.α) * (y 0 - m.δ)) - a / 2 * (y 0 - m.δ) ^ 2 := by
        rw [← hka]; ring
      linarith
    have hcub : |c| * |y 0 - m.δ| ^ 3 ≤ a / 8 * (y 0 - m.δ) ^ 2 := by
      have e : |y 0 - m.δ| ^ 3 = |y 0 - m.δ| * (y 0 - m.δ) ^ 2 := by
        rw [pow_succ, mul_comm, sq_abs]
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_right hur (sq_nonneg (y 0 - m.δ)),
        mul_nonneg (abs_nonneg (y 0 - m.δ)) (sq_nonneg (y 0 - m.δ))]
    have hcross : 2 * b * (y 3 - m.ζ) * (y 0 - m.δ) ≤
        a / 2 * (y 0 - m.δ) ^ 2 + 2 * b ^ 2 / a * (y 3 - m.ζ) ^ 2 := by
      have e : a / 2 * (y 0 - m.δ) ^ 2 + 2 * b ^ 2 / a * (y 3 - m.ζ) ^ 2 -
          2 * b * (y 3 - m.ζ) * (y 0 - m.δ) =
          (a * (y 0 - m.δ) - 2 * b * (y 3 - m.ζ)) ^ 2 / (2 * a) := by
        field_simp
        ring
      have : 0 ≤ (a * (y 0 - m.δ) - 2 * b * (y 3 - m.ζ)) ^ 2 / (2 * a) := by positivity
      linarith
    have hS : 0 < y 1 ^ 2 + y 2 ^ 2 + a / 4 * (y 0 - m.δ) ^ 2 + (y 3 - m.ζ) ^ 2 := by
      by_contra hle
      push Not at hle
      have q1 := sq_nonneg (y 1)
      have q2 := sq_nonneg (y 2)
      have q3 : 0 ≤ a / 4 * (y 0 - m.δ) ^ 2 := by positivity
      have q4 := sq_nonneg (y 3 - m.ζ)
      have e1 : y 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
      have e2 : y 2 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
      have e3 : y 3 = m.ζ := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
          (show (y 3 - m.ζ) ^ 2 = 0 by linarith)
        linarith
      have e0 : y 0 = m.δ := by
        have h5 : (y 0 - m.δ) ^ 2 = 0 := by
          have : a / 4 * (y 0 - m.δ) ^ 2 = 0 := by linarith
          rcases mul_eq_zero.mp this with h | h
          · linarith
          · exact h
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h5
        linarith
      apply hne
      ext i
      fin_cases i
      · simpa [p0] using e0
      · simpa [p1] using e1
      · simpa [p2] using e2
      · simpa [p3] using e3
    unfold Params.planeEnergy
    rw [← hc, ← hbb]
    linarith
  · rw [m.p.planeEnergy_lie hV hM hb]
    nlinarith [sq_nonneg (y 1), sq_nonneg (y 2), mul_nonneg hD (sq_nonneg (y 1))]

/-- **The plane flow of a damped flat curve without integral gain is Lyapunov stable**
(`A = 0`, `K_i = 0`, `P_ff = c₀`, `0 < D/M`): `Params.planeFlatEnergy` is positive definite and
does not increase (`Params.planeFlatEnergy_lie`); the angle settles where the damping leaves it. -/
@[tmio TM, powerlib_domain] private theorem lyapunovStable_planeField_of_flat (m : Model)
    (hV : m.p.Vref = 0) (hA : m.p.A = 0) (hKi : m.p.Ki = 0) (hb : m.p.Pff = m.p.c0)
    (hD : 0 < m.p.D / m.p.M) :
    LyapunovStable m.p.planeField m.point := by
  obtain ⟨p0, p1, p2, p3⟩ := point_apply_of_V_eq_zero m hV
  have hM : m.p.M ≠ 0 := fun h => by simp [h] at hD
  refine lyapunov_stable (V := m.p.planeFlatEnergy m.δ m.ζ) (D := Set.univ) (by norm_num)
    ⟨isOpen_univ, Set.mem_univ _, (m.p.contDiff_planeFlatEnergy _ _).continuous,
      (m.p.contDiff_planeFlatEnergy _ _).differentiable one_ne_zero, ?_, fun y _ hne => ?_,
      fun y _ => ?_⟩
  · simp [Params.planeFlatEnergy, p0, p1, p2, p3]
  · by_contra hle
    push Not at hle
    simp only [Params.planeFlatEnergy] at hle
    have q1 := sq_nonneg (y 1 + m.p.D / m.p.M * (y 0 - m.δ))
    have q2 := sq_nonneg (y 1)
    have q3 := sq_nonneg (y 2)
    have q4 := sq_nonneg (y 3 - m.ζ)
    have e1 : y 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have e2 : y 2 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have e3 : y 3 = m.ζ := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        (show (y 3 - m.ζ) ^ 2 = 0 by linarith)
      linarith
    have e0 : y 0 = m.δ := by
      have h4 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        (show (y 1 + m.p.D / m.p.M * (y 0 - m.δ)) ^ 2 = 0 by linarith)
      rw [e1, zero_add] at h4
      have := (mul_eq_zero.mp h4).resolve_left hD.ne'
      linarith
    apply hne
    ext i
    fin_cases i
    · simpa [p0] using e0
    · simpa [p1] using e1
    · simpa [p2] using e2
    · simpa [p3] using e3
  · rw [m.p.planeFlatEnergy_lie hV hM hA hKi hb]
    nlinarith [sq_nonneg (y 1), sq_nonneg (y 2), mul_nonneg hD.le (sq_nonneg (y 1))]

/-- **On the flat curve the frozen integrator drives the angle**: with `A = 0`, `K_i ≠ 0`,
`M ≠ 0` and the swing balanced at the frozen integrator (`P_ff + K_i ζ* = c₀`), the plane flow is
unstable (Chetaev's function `Params.planeDrift`, `Params.planeDrift_lie`: a frozen offset
`ζ − ζ*` makes `M ω + D (δ − δ*)` drift at the rate `K_i (ζ − ζ*)`). -/
@[tmio TM, powerlib_domain] private theorem unstable_planeField_of_drift (m : Model)
    (hV : m.p.Vref = 0) (hM : m.p.M ≠ 0) (hA : m.p.A = 0) (hKi : m.p.Ki ≠ 0)
    (hb : m.p.Pff + m.p.Ki * m.ζ = m.p.c0) :
    Unstable m.p.planeField m.point := by
  obtain ⟨p0, p1, p2, p3⟩ := point_apply_of_V_eq_zero m hV
  set v : State 4 := EuclideanSpace.single 3 (1 : ℝ) +
    EuclideanSpace.single 1 (m.p.Ki * m.p.M) with hv
  refine Dynamics.unstable_of_chetaev (W := m.p.planeDrift m.δ m.ζ) (r := 1)
    m.p.contDiff_planeField (by unfold Params.planeDrift; fun_prop) one_pos
    (fun ε hε => ?_) (fun y _ hWy => ?_)
  · have hv0 : 0 < ‖v‖ + 1 := by positivity
    have hη0 : 0 < ε / (2 * (‖v‖ + 1)) := by positivity
    refine ⟨m.point + (ε / (2 * (‖v‖ + 1))) • v, ?_, ?_⟩
    · rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hη0]
      have : ε / (2 * (‖v‖ + 1)) * (‖v‖ + 1) = ε / 2 := by field_simp
      nlinarith [norm_nonneg v]
    · have hx : m.p.Ki * m.p.M * (ε / (2 * (‖v‖ + 1))) ≠ 0 :=
        mul_ne_zero (mul_ne_zero hKi hM) hη0.ne'
      have e : m.p.planeDrift m.δ m.ζ (m.point + (ε / (2 * (‖v‖ + 1))) • v) =
          (m.p.Ki * m.p.M * (ε / (2 * (‖v‖ + 1)))) ^ 2 := by
        simp [Params.planeDrift, hv, p0, p1, p3]
        ring
      rw [e]
      exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hx))
  · rw [m.p.planeDrift_lie hV hM hA hb]
    have hz : y 3 - m.ζ ≠ 0 := fun h => by
      rw [Params.planeDrift, h, mul_zero, zero_mul] at hWy
      exact lt_irrefl 0 hWy
    exact mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hKi)))
      (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hz)))

/-- An open-loop model that carries the plane flow with the integrator frozen at `ζ*`: the plant
with the power reference `P_ff + K_i ζ*`, at `(δ*, 0, 0)`, with an auxiliary DC side
(`C = 1`, `I_s = 0`, `P_s = c₀ − |A| − 1`) that collapses onto the plane from both sides. -/
private def frozenOpenLoop (m : Model) : OpenLoop.Model :=
  ⟨⟨m.p.M, m.p.D, 1, m.p.Pff + m.p.Ki * m.ζ, m.p.c0, m.p.A, m.p.α, m.p.c0 - |m.p.A| - 1, 0⟩,
    m.δ, 0⟩

/-- **Lyapunov stability passes to the frozen swing.** With `V* = 0` and `I_s/C = 0`, a Lyapunov
stable selected point makes the plane flow Lyapunov stable
(`Dynamics.Degenerate.lyapunovStable_of_invariantPlane`); the slice `ζ = ζ*` is invariant for the
plane flow, which reads there as the plane flow of `frozenOpenLoop`
(`Dynamics.lyapunovStable_of_invariantSlice`); its DC side collapses (`2 V V̇ ≤ −2`), so the
open-loop model is Lyapunov stable
(`Dynamics.Degenerate.lyapunovStable_of_invariantPlane_collapse`), and its frozen swing is
balanced and Lyapunov stable (`OpenLoop.mem_den_lyapunovStable_iff_of_invariant`). -/
@[tmio TM, powerlib_domain] private theorem swing_of_lyapunovStable (m : Model)
    (hV : m.p.Vref = 0) (hI : m.p.Is / m.p.C = 0) (hs : LyapunovStable m.p.field m.point) :
    (m.p.Pff + m.p.Ki * m.ζ - m.p.Pe m.δ) / m.p.M = 0 ∧
      ((0 ≤ m.p.D / m.p.M ∧ 0 < m.p.k m.δ / m.p.M) ∨ (m.p.A = 0 ∧ 0 < m.p.D / m.p.M)) := by
  have hpl := Dynamics.Degenerate.lyapunovStable_of_invariantPlane 2 (point_two m hV)
    (fun y hy => by rw [m.p.field_two_of_V_eq_zero hy, hI]) (m.p.planeField_eq hI) hs
  have hpt : m.point = Dynamics.incl34 (frozenOpenLoop m).point +
      m.ζ • EuclideanSpace.single 3 (1 : ℝ) := by
    ext i
    fin_cases i <;> simp [Model.point, OpenLoop.Model.point, frozenOpenLoop, hV]
  have hgh : ∀ u : State 3,
      m.p.planeField (Dynamics.incl34 u + m.ζ • EuclideanSpace.single 3 (1 : ℝ)) =
        Dynamics.incl34 ((frozenOpenLoop m).q.planeField u) := by
    intro u
    ext i
    fin_cases i <;> simp [Params.planeField, Plant.planeField, Params.Pref, Plant.swingRate,
      Plant.Pe, frozenOpenLoop, hV]
  rw [hpt] at hpl
  have hg := Dynamics.lyapunovStable_of_invariantSlice Dynamics.incl34 Dynamics.norm_incl34 _ hgh
    hpl
  have hx2 : (frozenOpenLoop m).point 2 = 0 := by simp [OpenLoop.Model.point, frozenOpenLoop]
  have hI' : (frozenOpenLoop m).q.Is / (frozenOpenLoop m).q.C = 0 := by simp [frozenOpenLoop]
  have hcol : ∀ y : State 3, ‖y - (frozenOpenLoop m).point‖ < 1 → y 2 ≠ 0 →
      2 * y 2 * (frozenOpenLoop m).q.openField y 2 ≤ -2 := by
    intro y _ hy
    have hA : -|m.p.A| ≤ m.p.A * Real.sin (y 0 - m.p.α) := by
      have h1 := abs_mul m.p.A (Real.sin (y 0 - m.p.α))
      have h2 := Real.abs_sin_le_one (y 0 - m.p.α)
      have h3 := neg_abs_le (m.p.A * Real.sin (y 0 - m.p.α))
      nlinarith [abs_nonneg m.p.A, abs_nonneg (Real.sin (y 0 - m.p.α))]
    show 2 * y 2 * (frozenOpenLoop m).q.nodeRate (y 0) (y 2) ≤ -2
    rw [(frozenOpenLoop m).q.two_mul_nodeRate hy]
    simp only [frozenOpenLoop, Plant.Pe, zero_mul, zero_add, div_one]
    linarith
  obtain ⟨B, hB⟩ := (isCompact_closedBall (frozenOpenLoop m).point 1).exists_bound_of_continuousOn
    (frozenOpenLoop m).q.continuous_openField_sub_single.continuousOn
  have hopen := Dynamics.Degenerate.lyapunovStable_of_invariantPlane_collapse 2 hx2 one_pos
    two_pos hcol (fun y hy => hB y (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hy.le))
    (fun y _ hy => by rw [(frozenOpenLoop m).q.planeField_eq hI', hy, zero_smul, sub_zero,
      sub_zero]) hg
  have hmem : frozenOpenLoop m ∈ OpenLoop.family.den (.flow .lyapunovStable) :=
    (Spectral.mem_den_flow_iff_shift (f := fun m : OpenLoop.Model => m.q.openField)
      (pt := OpenLoop.Model.point) (Spectral.localFamily_isAutonomous _ _ _)).mpr hopen
  have h := OpenLoop.mem_den_lyapunovStable_iff_of_invariant (frozenOpenLoop m) rfl hI'
  unfold TMIO.Statement at h
  obtain ⟨-, hb, hc⟩ := h.mp hmem
  simp only [frozenOpenLoop, Plant.Pe, Plant.k] at hb hc
  exact ⟨hb, hc⟩

/-- **Invariant singular plane: instability from the frozen swing.** A selected point with
`V* = 0` and a source current that does not cross the plane (`I_s/C = 0`) is unstable, whatever
the sign of `(P_s − P_e(δ*))/C`, when the swing with the integrator frozen at `ζ*` is: it drifts
(`(P_ff + K_i ζ* − P_e(δ*))/M ≠ 0`), is negatively damped (`D/M < 0`), or has `k(δ*)/M ≤ 0`
unless the power curve is flat (`A = 0`) with positive damping (a saddle, a fold
`k(δ*) = 0 ≠ A`, an undamped flat curve, `M = 0`). The open-loop counterpart is
`OpenLoop.mem_den_unstable_of_invariant`, read at the reference `P_ff + K_i ζ*`. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_invariant (m : Model)
    (hV : m.p.Vref = 0) (hI : m.p.Is / m.p.C = 0)
    (h : (m.p.Pff + m.p.Ki * m.ζ - m.p.Pe m.δ) / m.p.M ≠ 0 ∨ m.p.D / m.p.M < 0 ∨
      (m.p.k m.δ / m.p.M ≤ 0 ∧ (m.p.A ≠ 0 ∨ m.p.D / m.p.M ≤ 0))) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  intro hs
  obtain ⟨hb, hc⟩ := swing_of_lyapunovStable m hV hI hs
  rcases h with h | h | ⟨hk, h⟩
  · exact h hb
  · rcases hc with ⟨hD, -⟩ | ⟨-, hD⟩ <;> linarith
  · rcases hc with ⟨-, hk'⟩ | ⟨hA, hD⟩
    · linarith
    · rcases h with h | h
      · exact h hA
      · linarith

/-- **Invariant singular plane, flat curve: the frozen integrator drifts.** With `V* = 0`,
`I_s/C = 0`, a flat power curve (`A = 0`) and an integral gain `K_i ≠ 0`, every selected point is
unstable, whatever the sign of `(P_s − P_e(δ*))/C`: a perturbed integrator stays frozen on the
plane and drives `M ω + D (δ − δ*)` at the rate `K_i (ζ − ζ*)` (`Params.planeDrift_lie`); the
plane's solutions are the model's. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_invariant_flat (m : Model)
    (hV : m.p.Vref = 0) (hI : m.p.Is / m.p.C = 0) (hA : m.p.A = 0) (hKi : m.p.Ki ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  intro hs
  obtain ⟨hb, hc⟩ := swing_of_lyapunovStable m hV hI hs
  have hM : m.p.M ≠ 0 := by
    rcases hc with ⟨-, h⟩ | ⟨-, h⟩ <;> exact fun hM => by simp [hM] at h
  have hb' : m.p.Pff + m.p.Ki * m.ζ = m.p.c0 := by
    rw [div_eq_zero_iff, or_iff_left hM, sub_eq_zero] at hb
    simpa [Plant.Pe, hA] using hb
  exact unstable_planeField_of_drift m hV hM hA hKi hb'
    (Dynamics.Degenerate.lyapunovStable_of_invariantPlane 2 (point_two m hV)
      (fun y hy => by rw [m.p.field_two_of_V_eq_zero hy, hI]) (m.p.planeField_eq hI) hs)

/-- **Lyapunov stability on the invariant singular plane under the collapse.** For a selected
point with `V* = 0`, a source current that does not cross the plane (`I_s/C = 0`) and the DC node
driven into it (`(P_s − P_e(δ*))/C < 0`), Lyapunov stability holds exactly when the swing with
the integrator frozen at `ζ*` is balanced, `(P_ff + K_i ζ* − P_e(δ*))/M = 0`, and either stiff and
not negatively damped, `0 ≤ D/M`, `0 < k(δ*)/M` (the parametric energy `Params.planeEnergy`), or
flat, undriven by the integrator and damped, `A = 0`, `K_i = 0`, `0 < D/M`
(`Params.planeFlatEnergy`). The collapse carries the stability of the plane flow to the model
(`Dynamics.Degenerate.lyapunovStable_iff_of_invariantPlane`); otherwise
`mem_den_unstable_of_invariant`, `mem_den_unstable_of_invariant_flat`. -/
@[tmio TM, powerlib_domain] theorem mem_den_lyapunovStable_iff_of_invariant (m : Model)
    (hV : m.p.Vref = 0) (hI : m.p.Is / m.p.C = 0) (hP : (m.p.Ps - m.p.Pe m.δ) / m.p.C < 0) :
    connection% (m ∈ family.den (.flow .lyapunovStable) ↔
      (m.p.Pff + m.p.Ki * m.ζ - m.p.Pe m.δ) / m.p.M = 0 ∧
        ((0 ≤ m.p.D / m.p.M ∧ 0 < m.p.k m.δ / m.p.M) ∨
          (m.p.A = 0 ∧ m.p.Ki = 0 ∧ 0 < m.p.D / m.p.M))) := by
  have hflat := mem_den_unstable_of_invariant_flat m hV hI
  unfold TMIO.Statement at hflat ⊢
  rw [mem_den_flow_iff]
  constructor
  · intro hs
    obtain ⟨hb, hc⟩ := swing_of_lyapunovStable m hV hI hs
    refine ⟨hb, ?_⟩
    rcases hc with h | ⟨hA, hD⟩
    · exact Or.inl h
    · refine Or.inr ⟨hA, ?_, hD⟩
      by_contra hKi
      have hu := hflat hA hKi
      rw [mem_den_flow_iff] at hu
      exact hu hs
  · rintro ⟨hb, hc⟩
    obtain ⟨ρ, a, B, hρ, ha, hcol, hbound⟩ := exists_collapse m hV hP
    change LyapunovStable m.p.field m.point
    rw [Dynamics.Degenerate.lyapunovStable_iff_of_invariantPlane 2 (point_two m hV) hρ ha hcol
      hbound (fun y hy => by rw [m.p.field_two_of_V_eq_zero hy, hI]) (m.p.planeField_eq hI)]
    have hM : m.p.M ≠ 0 := by
      rcases hc with ⟨-, h⟩ | ⟨-, -, h⟩ <;> exact fun hM => by simp [hM] at h
    have hb' : m.p.Pff + m.p.Ki * m.ζ = m.p.Pe m.δ := by
      rw [div_eq_zero_iff, or_iff_left hM, sub_eq_zero] at hb
      exact hb
    rcases hc with ⟨hD, hk⟩ | ⟨hA, hKi, hD⟩
    · exact lyapunovStable_planeField_of_swing m hV hb' hk hD
    · exact lyapunovStable_planeField_of_flat m hV hA hKi
        (by simpa [Plant.Pe, hA, hKi] using hb') hD

/-- **Invariant singular plane without capacitance.** With `V* = 0` and `C = 0` (Lean's
`x / 0 = 0`: `V̇ = 0` everywhere) the field is `C¹` and `V` is conserved and drives the
integrator, `ζ̇ = V`: every selected point is unstable
(`Dynamics.unstable_of_conserved_drive_local`; the case `V* ≠ 0` is
`mem_den_unstable_of_C_eq_zero`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_V_eq_zero_of_C_eq_zero (m : Model)
    (hV : m.p.Vref = 0) (hC : m.p.C = 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  have hfC : ContDiff ℝ 1 m.p.field := by
    rw [contDiff_euclidean]
    intro i
    fin_cases i
    · simpa using Dynamics.contDiff_coord (n := 4) (k := 1) 1
    · simp only [Fin.mk_one, Params.field_apply_one]
      unfold Plant.swingRate Params.Pref Plant.Pe
      fun_prop
    · simp only [Fin.reduceFinMk, Params.field_apply_two, Plant.nodeRate, GFL.DCLink.nodeRate,
        hC, div_zero]
      exact contDiff_const
    · simp only [Fin.reduceFinMk, Params.field_apply_three]
      fun_prop
  refine Dynamics.unstable_of_conserved_drive_local (U := Set.univ) (i := 2) (j := 3)
    (g := fun s => s - m.p.Vref) isOpen_univ (Set.mem_univ _) hfC.contDiffOn (by decide)
    (contDiff_id.sub contDiff_const) (fun ε hε => ⟨ε / 2, ?_, ?_⟩) (fun x _ => ?_)
    (fun x _ => ?_)
  · rw [point_two m hV, sub_zero, abs_of_pos (half_pos hε)]
    linarith
  · rw [hV, sub_zero]
    exact (half_pos hε).ne'
  · simp [Plant.nodeRate, GFL.DCLink.nodeRate, hC]
  · simp

/-- **Invariant singular plane, degenerate balance, no DC gains: the integrator drifts.** With
`V* = 0`, `I_s/C = 0`, `(P_s − P_e(δ*))/C = 0` (the degenerate balance, or `C = 0`) and
`K_p = K_i = 0`, every selected point is unstable. If the frozen swing is unbalanced or `M = 0`
this is `mem_den_unstable_of_invariant`; otherwise `(δ*, 0, η, ζ* + η t)` is a solution for every
`η`: the swing rests, the DC voltage is frozen at `η` (the open loop's first integral) and the
integrator integrates it, leaving every ball. So the open loop's first-integral stability
(`OpenLoop.mem_den_lyapunovStable_iff_of_invariant`) does not survive the integrator, even with
both gains zero. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_invariant_degenerate (m : Model)
    (hV : m.p.Vref = 0) (hI : m.p.Is / m.p.C = 0) (hP : (m.p.Ps - m.p.Pe m.δ) / m.p.C = 0)
    (hKp : m.p.Kp = 0) (hKi : m.p.Ki = 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  by_cases hM : m.p.M = 0
  · exact mem_den_unstable_of_invariant m hV hI (Or.inr (Or.inr ⟨by simp [hM], Or.inr (by
      simp [hM])⟩))
  by_cases hb : (m.p.Pff + m.p.Ki * m.ζ - m.p.Pe m.δ) / m.p.M ≠ 0
  · exact mem_den_unstable_of_invariant m hV hI (Or.inl hb)
  push Not at hb
  have hb' : m.p.Pff = m.p.Pe m.δ := by
    rw [div_eq_zero_iff, or_iff_left hM, hKi, zero_mul, add_zero, sub_eq_zero] at hb
    exact hb
  obtain ⟨p0, p1, p2, p3⟩ := point_apply_of_V_eq_zero m hV
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  intro hs
  obtain ⟨d, hd, hdb⟩ := hs 1 one_pos
  have hη : 0 < d / 2 := half_pos hd
  set e3 : State 4 := EuclideanSpace.single 3 (1 : ℝ) with he3
  set φ : ℝ → State 4 := fun t =>
    m.point + EuclideanSpace.single 2 (d / 2) + (d / 2 * t) • e3 with hφ
  have hc : ∀ t, φ t 0 = m.δ ∧ φ t 1 = 0 ∧ φ t 2 = d / 2 ∧ φ t 3 = m.ζ + d / 2 * t := by
    intro t
    simp [hφ, he3, p0, p1, p2, p3]
  have hn : (m.p.Is + (m.p.Ps - m.p.Pe m.δ) / (d / 2)) / m.p.C = 0 := by
    rw [add_div, hI, zero_add, div_div, mul_comm, ← div_div, hP, zero_div]
  have hf : ∀ t, m.p.field (φ t) = (d / 2 * 1) • e3 := by
    intro t
    obtain ⟨c0, c1, c2, c3⟩ := hc t
    ext i
    fin_cases i
    · simp [he3, c1]
    · simp [he3, c0, c1, c2, c3, Plant.swingRate, Params.Pref, hKp, hKi, hb']
    · simp only [Fin.reduceFinMk, Params.field_apply_two, c0, c2, Plant.nodeRate,
        GFL.DCLink.nodeRate, hn]
      simp [he3]
    · simp [he3, c2, hV]
  have htraj : IsTrajectoryOn φ m.p.field 0 (2 / (d / 2)) := fun t _ => by
    show HasDerivWithinAt φ (m.p.field (φ t)) _ t
    rw [hf t]
    exact ((((hasDerivAt_id t).const_mul (d / 2)).smul_const e3).const_add
      (m.point + EuclideanSpace.single 2 (d / 2))).hasDerivWithinAt
  have h0 : ‖φ 0 - m.point‖ < d := by
    simp only [hφ, mul_zero, zero_smul, add_zero, add_sub_cancel_left]
    rw [EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos hη]
    linarith
  have h1 := hdb 0 (2 / (d / 2)) φ htraj h0 (2 / (d / 2)) ⟨by positivity, le_rfl⟩
  have h2 := Dynamics.abs_coord_sub_le m.point (φ (2 / (d / 2))) 3
  rw [(hc _).2.2.2, p3, add_sub_cancel_left, show d / 2 * (2 / (d / 2)) = 2 by
    field_simp, abs_of_pos two_pos] at h2
  linarith

/-- **Invariant singular plane, degenerate balance, flat curve, no integral gain: the swing and the
integrator drift.** With `V* = 0`, `I_s/C = 0`, `(P_s − P_e(δ*))/C = 0` (the degenerate balance),
a flat power curve `A = 0`, `K_i = 0` and damping `D ≠ 0`, every selected point is unstable,
whatever `K_p`. If the frozen swing is unbalanced or `M = 0` this is
`mem_den_unstable_of_invariant`; otherwise
`(δ* + (K_p η/D) t, K_p η/D, η, ζ* + η t)` is a solution for every `η`: the DC voltage is frozen
at `η` (the flat curve draws the balanced power at every angle), the proportional DC gain raises
the power reference by `K_p η`, which the damping balances at the frequency `K_p η/D`, and the
integrator integrates `η`, leaving every ball. With `K_p = 0` these are the solutions of
`mem_den_unstable_of_invariant_degenerate`. -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_invariant_flat_degenerate (m : Model)
    (hV : m.p.Vref = 0) (hI : m.p.Is / m.p.C = 0) (hP : (m.p.Ps - m.p.Pe m.δ) / m.p.C = 0)
    (hA : m.p.A = 0) (hKi : m.p.Ki = 0) (hD : m.p.D ≠ 0) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  by_cases hM : m.p.M = 0
  · exact mem_den_unstable_of_invariant m hV hI (Or.inr (Or.inr ⟨by simp [hM], Or.inr (by
      simp [hM])⟩))
  by_cases hb : (m.p.Pff + m.p.Ki * m.ζ - m.p.Pe m.δ) / m.p.M ≠ 0
  · exact mem_den_unstable_of_invariant m hV hI (Or.inl hb)
  push Not at hb
  have hb' : m.p.Pff = m.p.Pe m.δ := by
    rw [div_eq_zero_iff, or_iff_left hM, hKi, zero_mul, add_zero, sub_eq_zero] at hb
    exact hb
  have hPe : ∀ δ, m.p.Pe δ = m.p.Pe m.δ := fun δ => by simp [Plant.Pe, hA]
  obtain ⟨p0, p1, p2, p3⟩ := point_apply_of_V_eq_zero m hV
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  intro hs
  obtain ⟨d, hd, hdb⟩ := hs 1 one_pos
  set κ := m.p.Kp / m.p.D with hκ
  set η := d / (2 * (1 + |κ|)) with hηdef
  have hη : 0 < η := by positivity
  set e0 : State 4 := EuclideanSpace.single 0 (1 : ℝ) with he0
  set e3 : State 4 := EuclideanSpace.single 3 (1 : ℝ) with he3
  set w : State 4 := EuclideanSpace.single 1 (κ * η) + EuclideanSpace.single 2 η with hw
  set φ : ℝ → State 4 := fun t => m.point + w + t • ((κ * η) • e0 + η • e3) with hφ
  have hc : ∀ t, φ t 0 = m.δ + κ * η * t ∧ φ t 1 = κ * η ∧ φ t 2 = η ∧ φ t 3 = m.ζ + η * t := by
    intro t
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hφ, hw, he0, he3, p0, p1, p2, p3] <;> ring
  have hn : ∀ δ, (m.p.Is + (m.p.Ps - m.p.Pe δ) / η) / m.p.C = 0 := fun δ => by
    rw [hPe, add_div, hI, zero_add, div_div, mul_comm, ← div_div, hP, zero_div]
  have hf : ∀ t, m.p.field (φ t) = (κ * η) • e0 + η • e3 := by
    intro t
    obtain ⟨c0, c1, c2, c3⟩ := hc t
    ext i
    fin_cases i
    · simp [he0, he3, c1]
    · simp only [Fin.mk_one, Params.field_apply_one, c0, c1, c2, c3, Plant.swingRate,
        Params.Pref, hV, hKi, hPe, ← hb']
      simp [he0, he3, hκ]
      left
      field_simp
      ring
    · simp only [Fin.reduceFinMk, Params.field_apply_two, c0, c2, Plant.nodeRate,
        GFL.DCLink.nodeRate, hn]
      simp [he0, he3]
    · simp [he0, he3, c2, hV]
  have htraj : IsTrajectoryOn φ m.p.field 0 (2 / η) := fun t _ => by
    show HasDerivWithinAt φ (m.p.field (φ t)) _ t
    rw [hf t]
    have h := ((hasDerivAt_id t).smul_const ((κ * η) • e0 + η • e3)).const_add (m.point + w)
    simp only [id, one_smul] at h
    exact h.hasDerivWithinAt
  have h0 : ‖φ 0 - m.point‖ < d := by
    simp only [hφ, zero_smul, add_zero, add_sub_cancel_left]
    calc ‖w‖ ≤ ‖(EuclideanSpace.single 1 (κ * η) : State 4)‖ +
          ‖(EuclideanSpace.single 2 η : State 4)‖ := norm_add_le _ _
      _ = |κ| * η + η := by
          rw [EuclideanSpace.single, PiLp.norm_single, EuclideanSpace.single, PiLp.norm_single,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos hη]
      _ = d / 2 := by rw [hηdef]; field_simp; ring
      _ < d := by linarith
  have h1 := hdb 0 (2 / η) φ htraj h0 (2 / η) ⟨by positivity, le_rfl⟩
  have h2 := Dynamics.abs_coord_sub_le m.point (φ (2 / η)) 3
  rw [(hc _).2.2.2, p3, add_sub_cancel_left, show η * (2 / η) = 2 by field_simp,
    abs_of_pos two_pos] at h2
  linarith

/-- The potential of the power curve about `δ*`, `Π(θ) = ∫₀^θ (P_e(δ* + s) − P_e(δ*)) ds`. -/
private def Model.potential (m : Model) (θ : ℝ) : ℝ :=
  m.p.A * (Real.cos (m.δ - m.p.α) - Real.cos (m.δ - m.p.α + θ)) -
    m.p.A * Real.sin (m.δ - m.p.α) * θ

/-- The potential is its quadratic part `k θ²/2` up to `|A| |θ|³` for `|θ| ≤ 1` (`pot_cubic`). -/
@[tmio M, powerlib_domain] private theorem pot_bound (m : Model) {θ : ℝ} (hθ : |θ| ≤ 1) :
    |m.potential θ - m.p.k m.δ * θ ^ 2 / 2| ≤ |m.p.A| * |θ| ^ 3 := by
  have h := pot_cubic (θ := m.δ - m.p.α) hθ
  have he : m.potential θ - m.p.k m.δ * θ ^ 2 / 2 =
      m.p.A * (Real.cos (m.δ - m.p.α) - Real.cos (m.δ - m.p.α + θ) -
        Real.sin (m.δ - m.p.α) * θ - Real.cos (m.δ - m.p.α) * θ ^ 2 / 2) := by
    simp only [Model.potential, Plant.k]; ring
  rw [he, abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-- The rate of the potential barrier `F θ − Π(θ) − M ω²/2 − w₀` along the field at a state off the
plane (`V* = 0`, `I_s = 0`, `P_s = P_e(δ*)`, the frozen swing balanced, `M ≠ 0`):
`D ω² + θ K_p V̇ + θ K_i V`. -/
@[tmio M, powerlib_domain] private theorem barrier_rate (m : Model) (hV : m.p.Vref = 0)
    (hIs : m.p.Is = 0) (hP : m.p.Ps = m.p.Pe m.δ) (hb : m.p.Pff + m.p.Ki * m.ζ = m.p.Pe m.δ)
    (hM : m.p.M ≠ 0) (hC : m.p.C ≠ 0) (w₀ : ℝ) {y : State 4} (hy : y 2 ≠ 0) :
    fderiv ℝ (fun y : State 4 => (m.p.Kp * y 2 + m.p.Ki * (y 3 - m.ζ)) * (y 0 - m.δ) -
        m.potential (y 0 - m.δ) - m.p.M / 2 * y 1 ^ 2 - w₀) y (m.p.field y) =
      m.p.D * y 1 ^ 2 + (y 0 - m.δ) * m.p.Kp *
        (-(m.p.Pe (m.δ + (y 0 - m.δ)) - m.p.Pe m.δ) / y 2 / m.p.C) +
        (y 0 - m.δ) * m.p.Ki * y 2 := by
  have h0 : HasFDerivAt (fun y : State 4 => y 0) (PiLp.proj 2 (fun _ : Fin 4 => ℝ) 0) y :=
    (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (0 : Fin 4) : State 4 →L[ℝ] ℝ).hasFDerivAt
  have h1 : HasFDerivAt (fun y : State 4 => y 1) (PiLp.proj 2 (fun _ : Fin 4 => ℝ) 1) y :=
    (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (1 : Fin 4) : State 4 →L[ℝ] ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun y : State 4 => y 2) (PiLp.proj 2 (fun _ : Fin 4 => ℝ) 2) y :=
    (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (2 : Fin 4) : State 4 →L[ℝ] ℝ).hasFDerivAt
  have h3 : HasFDerivAt (fun y : State 4 => y 3) (PiLp.proj 2 (fun _ : Fin 4 => ℝ) 3) y :=
    (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (3 : Fin 4) : State 4 →L[ℝ] ℝ).hasFDerivAt
  have hθ := h0.sub_const m.δ
  have hF := (h2.const_mul m.p.Kp).add ((h3.sub_const m.ζ).const_mul m.p.Ki)
  have hcos := (Real.hasDerivAt_cos (m.δ - m.p.α + (y 0 - m.δ))).comp_hasFDerivAt y
    (hθ.const_add (m.δ - m.p.α))
  have hP' := ((hcos.const_sub (Real.cos (m.δ - m.p.α))).const_mul m.p.A).sub
    (hθ.const_mul (m.p.A * Real.sin (m.δ - m.p.α)))
  have hW := (((hF.mul hθ).sub hP').sub ((h1.pow 2).const_mul (m.p.M / 2))).sub_const w₀
  rw [show fderiv ℝ (fun y : State 4 => (m.p.Kp * y 2 + m.p.Ki * (y 3 - m.ζ)) * (y 0 - m.δ) -
      m.potential (y 0 - m.δ) - m.p.M / 2 * y 1 ^ 2 - w₀) y = _ from hW.fderiv]
  simp only [_root_.sub_apply, _root_.add_apply, _root_.smul_apply, PiLp.proj_apply,
    smul_eq_mul]
  simp only [Params.field_apply_zero, Params.field_apply_one, Params.field_apply_two,
    Params.field_apply_three, Plant.swingRate, Params.Pref, Plant.nodeRate,
    GFL.DCLink.nodeRate, hV, hIs, hP]
  have hb' : m.p.Pff = m.p.Pe m.δ - m.p.Ki * m.ζ := by linarith
  rw [hb']
  have harg : m.δ - m.p.α + (y 0 - m.δ) = y 0 - m.p.α := by ring
  have harg' : m.δ + (y 0 - m.δ) = y 0 := by ring
  rw [harg, harg']
  simp only [Plant.Pe]
  simp
  field_simp
  ring

/-- The norm of a perturbation of the angle, the DC voltage and the integrator:
`|(θ₀ e₀ + a e₂ + b e₃)| ≤ |θ₀| + |a| + |b|`. -/
@[tmio T, powerlib_foundation] private theorem norm_seed_le (θ₀ a b : ℝ) :
    ‖(EuclideanSpace.single 0 θ₀ + EuclideanSpace.single 2 a + EuclideanSpace.single 3 b :
      State 4)‖ ≤ |θ₀| + |a| + |b| := by
  have t1 := norm_add_le (EuclideanSpace.single 0 θ₀ + EuclideanSpace.single 2 a : State 4)
    (EuclideanSpace.single 3 b)
  have t2 := norm_add_le (EuclideanSpace.single 0 θ₀ : State 4) (EuclideanSpace.single 2 a)
  simp only [EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs] at t1 t2
  linarith

/-- The constants of the seeds of `mem_den_unstable_of_invariant_stiff_degenerate`: for
`K, c, G, δ' > 0`, `a ≥ 0` there are `h, τ > 0` with `c τ + 2h < δ'`, `c τ ≤ 1/2` and
`(K + a) c τ ≤ G h/2`. -/
@[tmio T, powerlib_foundation] private theorem stiff_seed_constants {K a c G δ' : ℝ} (hK : 0 < K)
    (ha : 0 ≤ a) (hc : 0 < c) (hG : 0 < G) (hδ : 0 < δ') :
    ∃ h τ : ℝ, 0 < h ∧ 0 < τ ∧ c * τ + 2 * h < δ' ∧ c * τ ≤ 1 / 2 ∧
      (K + a) * c * τ ≤ G * h / 2 := by
  obtain ⟨d, hd⟩ : ∃ d, d = min δ' 1 := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; exact lt_min hδ one_pos
  have hd1 : d ≤ 1 := by rw [hd]; exact min_le_right _ _
  have hdδ : d ≤ δ' := by rw [hd]; exact min_le_left _ _
  have hK2 : 0 < 2 * K := by linarith
  obtain ⟨q, hq⟩ : ∃ q, q = G / (2 * K) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; exact div_nonneg hG.le hK2.le
  obtain ⟨h, hh⟩ : ∃ h, h = d / (2 * (2 + q)) := ⟨_, rfl⟩
  have h2q : 0 < 2 + q := by linarith
  have hh0 : 0 < h := by rw [hh]; exact div_pos hd0 (by linarith)
  have hhd : h * (2 + q) = d / 2 := by
    rw [hh, div_mul_eq_mul_div, mul_comm (2 : ℝ) (2 + q), mul_comm d (2 + q),
      mul_div_mul_left _ _ h2q.ne']
  obtain ⟨D, hD⟩ : ∃ D, D = 2 * (K + a) * c + 1 := ⟨_, rfl⟩
  have hD0 : 0 < D := by
    rw [hD]; have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (add_nonneg hK.le ha))
      hc.le
    linarith
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = G * h / D := ⟨_, rfl⟩
  have hGh : 0 < G * h := mul_pos hG hh0
  have hτ0 : 0 < τ := by rw [hτ]; exact div_pos hGh hD0
  have hτD : τ * D = G * h := by rw [hτ, div_mul_cancel₀ _ hD0.ne']
  have hcτ : c * τ ≤ q * h := by
    have h1 : 2 * K * c ≤ D := by
      rw [hD]; have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha) hc.le
      nlinarith
    have h2 : 2 * K * (c * τ) ≤ G * h := by
      calc 2 * K * (c * τ) = (2 * K * c) * τ := by ring
        _ ≤ D * τ := mul_le_mul_of_nonneg_right h1 hτ0.le
        _ = G * h := by rw [mul_comm, hτD]
    have h3 : q * h * (2 * K) = G * h := by rw [hq]; field_simp
    nlinarith
  refine ⟨h, τ, hh0, hτ0, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · have h1 : 2 * ((K + a) * c) ≤ D := by rw [hD]; linarith
    have h2 : 2 * ((K + a) * c * τ) ≤ D * τ := by nlinarith
    rw [mul_comm D τ, hτD] at h2
    linarith

/-- The arithmetic of the trapping region of `mem_den_unstable_of_invariant_stiff_degenerate`: in
the region (`σ V > 0`, `C θ ≤ 0`, the barrier `F θ − Π − M ω²/2 − w₀ ≥ 0` with the potential
`Π ≥ 0`, the
power curve `X = ΔP(θ)` with `X θ ≥ (K/2) θ²`, coordinates in the ball of radius `ρ`) the DC
voltage moves away from the plane, `V²` grows at the uniform rate `K c/|C|`,
`c = w₀/((|K_p| + |K_i|) ρ + 1)`, the barrier's rate is positive and `C θ < 0`. -/
@[tmio T, powerlib_foundation] private theorem stiff_region {σ Kp Ki C D M K w₀ ρ θ V u ω X Pt : ℝ}
    (hσ2 : σ * σ = 1) (hKpσ : Kp * σ * C ≤ 0) (hKiσ : Ki * σ * C ≤ 0)
    (hKpσ' : Kp ≠ 0 → Kp * σ * C < 0) (hKiσ' : Ki ≠ 0 → Ki * σ * C < 0)
    (hgain : Kp ≠ 0 ∨ Ki ≠ 0) (hC : C ≠ 0) (hM : 0 < M) (hD : 0 ≤ D) (hK : 0 < K)
    (hw₀ : 0 < w₀) (hρ : 0 < ρ) (hV : |V| < ρ) (hu : |u| < ρ) (hσV : 0 < σ * V)
    (hPt : 0 ≤ Pt) (hX : K / 2 * θ ^ 2 ≤ X * θ)
    (hW : 0 ≤ (Kp * V + Ki * u) * θ - Pt - M / 2 * ω ^ 2 - w₀) (hW2 : 0 ≤ -C * θ) :
    0 ≤ σ * (-X / V / C) ∧
      K * (w₀ / ((|Kp| + |Ki|) * ρ + 1)) / |C| ≤ 2 * V * (-X / V / C) ∧
      0 < D * ω ^ 2 + θ * Kp * (-X / V / C) + θ * Ki * V ∧ C * θ < 0 := by
  have hV0 : V ≠ 0 := fun h => by rw [h, mul_zero] at hσV; exact lt_irrefl _ hσV
  have hC2 : 0 < C ^ 2 := by positivity
  have hV2 : 0 < V ^ 2 := by positivity
  -- the barrier forces `F θ ≥ w₀`
  have hω : 0 ≤ M / 2 * ω ^ 2 := by positivity
  have hFθ : w₀ ≤ (Kp * V + Ki * u) * θ := by linarith
  have hF : |Kp * V + Ki * u| ≤ (|Kp| + |Ki|) * ρ := by
    calc |Kp * V + Ki * u| ≤ |Kp| * |V| + |Ki| * |u| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |Kp| * ρ + |Ki| * ρ := by gcongr
      _ = (|Kp| + |Ki|) * ρ := by ring
  have hden : 0 < (|Kp| + |Ki|) * ρ + 1 := by positivity
  have hθc : w₀ / ((|Kp| + |Ki|) * ρ + 1) ≤ |θ| := by
    rw [div_le_iff₀ hden]
    have h1 : (Kp * V + Ki * u) * θ ≤ |Kp * V + Ki * u| * |θ| := by
      rw [← abs_mul]; exact le_abs_self _
    have h2 : |Kp * V + Ki * u| * |θ| ≤ (|Kp| + |Ki|) * ρ * |θ| :=
      mul_le_mul_of_nonneg_right hF (abs_nonneg θ)
    nlinarith [abs_nonneg θ]
  have hθ0 : θ ≠ 0 := by
    intro h; rw [h, abs_zero] at hθc
    have : 0 < w₀ / ((|Kp| + |Ki|) * ρ + 1) := div_pos hw₀ hden
    linarith
  have hθ2 : 0 < θ ^ 2 := by positivity
  have hCθ : C * θ < 0 := by
    have h1 : C * θ ≤ 0 := by linarith
    exact lt_of_le_of_ne h1 (mul_ne_zero hC hθ0)
  have hXθ : 0 < X * θ := lt_of_lt_of_le (by positivity) hX
  have hXC : X * C < 0 := by
    have h1 : (X * θ) * (C * θ) < 0 := mul_neg_of_pos_of_neg hXθ hCθ
    have h2 : (X * θ) * (C * θ) = (X * C) * θ ^ 2 := by ring
    rw [h2] at h1
    by_contra h3
    have := mul_nonneg (not_lt.mp h3) hθ2.le
    linarith
  refine ⟨?_, ?_, ?_, hCθ⟩
  · have e : σ * (-X / V / C) = (σ * V) * (-(X * C)) / (V ^ 2 * C ^ 2) := by
      field_simp
    rw [e]
    exact div_nonneg (mul_nonneg hσV.le (by linarith)) (by positivity)
  · have e : 2 * V * (-X / V / C) = 2 * (-(X * C)) / C ^ 2 := by
      field_simp
    rw [e]
    have hXa : |X| * |θ| ≥ K / 2 * |θ| ^ 2 := by
      rw [← abs_mul, sq_abs]; exact le_trans hX (le_abs_self _)
    have hXk : K / 2 * |θ| ≤ |X| := by
      have hθp : 0 < |θ| := abs_pos.mpr hθ0
      nlinarith
    have hXC' : -(X * C) = |X| * |C| := by rw [← abs_mul, abs_of_neg hXC]
    have hCa : C ^ 2 = |C| * |C| := by rw [← sq, sq_abs]
    rw [hXC', hCa]
    have hCp : 0 < |C| := abs_pos.mpr hC
    rw [show 2 * (|X| * |C|) / (|C| * |C|) = 2 * |X| / |C| by field_simp]
    rw [div_le_div_iff_of_pos_right hCp]
    have h1 : K * (w₀ / ((|Kp| + |Ki|) * ρ + 1)) ≤ K * |θ| :=
      mul_le_mul_of_nonneg_left hθc hK.le
    linarith
  · have hT1 : 0 ≤ D * ω ^ 2 := by positivity
    have e2 : θ * Kp * (-X / V / C) = (X * θ) * (-(Kp * σ * C)) * (σ * V) / (V ^ 2 * C ^ 2) := by
      have : (X * θ) * (-(Kp * σ * C)) * (σ * V) = (X * θ) * (-(Kp * C)) * V * (σ * σ) := by ring
      rw [this, hσ2, mul_one]
      field_simp
    have e3 : θ * Ki * V = (Ki * σ * C) * (C * θ) * (σ * V) / C ^ 2 := by
      have : (Ki * σ * C) * (C * θ) * (σ * V) = Ki * θ * V * C ^ 2 * (σ * σ) := by ring
      rw [this, hσ2, mul_one]
      field_simp
    rw [e2, e3]
    have hT2 : 0 ≤ (X * θ) * (-(Kp * σ * C)) * (σ * V) / (V ^ 2 * C ^ 2) :=
      div_nonneg (mul_nonneg (mul_nonneg hXθ.le (by linarith)) hσV.le) (by positivity)
    have hT3 : 0 ≤ (Ki * σ * C) * (C * θ) * (σ * V) / C ^ 2 :=
      div_nonneg (mul_nonneg (mul_nonneg_of_nonpos_of_nonpos hKiσ hCθ.le) hσV.le) hC2.le
    rcases hgain with h | h
    · have : 0 < (X * θ) * (-(Kp * σ * C)) * (σ * V) / (V ^ 2 * C ^ 2) :=
        div_pos (mul_pos (mul_pos hXθ (by linarith [hKpσ' h])) hσV) (by positivity)
      linarith
    · have : 0 < (Ki * σ * C) * (C * θ) * (σ * V) / C ^ 2 :=
        div_pos (mul_pos (mul_pos_of_neg_of_neg (hKiσ' h) hCθ) hσV) hC2
      linarith

/-- The escape side of `mem_den_unstable_of_invariant_stiff_degenerate`: for DC gains
`(K_p, K_i) ≠ (0, 0)` of one sign (`K_p K_i ≥ 0`) and `C ≠ 0` there is `σ = ±1` with
`σ (K_p + K_i) C < 0`; then `K_p σ C ≤ 0`, `K_i σ C ≤ 0`, strictly for a nonzero gain. -/
@[tmio T, powerlib_foundation] private theorem stiff_signs {Kp Ki C : ℝ} (hC : C ≠ 0)
    (hgain : Kp ≠ 0 ∨ Ki ≠ 0) (hsame : 0 ≤ Kp * Ki) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ σ * σ = 1 ∧ σ * (Kp + Ki) * C < 0 ∧ Kp * σ * C ≤ 0 ∧
      Ki * σ * C ≤ 0 ∧ (Kp ≠ 0 → Kp * σ * C < 0) ∧ (Ki ≠ 0 → Ki * σ * C < 0) := by
  have hg : Kp + Ki ≠ 0 := by
    intro h0
    rcases hgain with h | h
    · have : Ki = -Kp := by linarith
      rw [this] at hsame; nlinarith [sq_pos_of_ne_zero h]
    · have : Kp = -Ki := by linarith
      rw [this] at hsame; nlinarith [sq_pos_of_ne_zero h]
  obtain ⟨σ, hσ, hσgC⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ σ * (Kp + Ki) * C < 0 := by
    by_cases h : 0 < (Kp + Ki) * C
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [one_mul]
      exact lt_of_le_of_ne (not_lt.mp h) (mul_ne_zero hg hC)
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hg2 : 0 < (Kp + Ki) ^ 2 := by positivity
  have key : ∀ K : ℝ, 0 ≤ K * (Kp + Ki) → K * σ * C ≤ 0 := fun K hK => by
    have e : K * σ * C * (Kp + Ki) ^ 2 = K * (Kp + Ki) * (σ * (Kp + Ki) * C) := by ring
    by_contra h
    have h1 := mul_pos (not_le.mp h) hg2
    rw [e] at h1
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hK hσgC.le]
  have key' : ∀ K : ℝ, 0 < K * (Kp + Ki) → K * σ * C < 0 := fun K hK => by
    have e : K * σ * C * (Kp + Ki) ^ 2 = K * (Kp + Ki) * (σ * (Kp + Ki) * C) := by ring
    have h1 : K * σ * C * (Kp + Ki) ^ 2 < 0 := by rw [e]; exact mul_neg_of_pos_of_neg hK hσgC
    by_contra h
    nlinarith [mul_nonneg (not_lt.mp h) hg2.le]
  refine ⟨σ, hσ, hσ2, hσgC, key _ (by nlinarith [sq_nonneg Kp]),
    key _ (by nlinarith [sq_nonneg Ki]),
    fun h => key' _ (by nlinarith [sq_pos_of_ne_zero h]),
    fun h => key' _ (by nlinarith [sq_pos_of_ne_zero h])⟩

/-- The power curve near a stiff angle (`k(δ*) > 0`): on the radius
`ρ = min 1 (k/(4(|A| + 1)))` it keeps the sign of `θ`, `ΔP(θ) θ ≥ (k/2) θ²`, and its potential is
nonnegative. -/
@[tmio M, powerlib_domain] private theorem stiff_curve (m : Model) (hk : 0 < m.p.k m.δ) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ 1 ∧
      (∀ θ, |θ| < ρ → m.p.k m.δ / 2 * θ ^ 2 ≤ (m.p.Pe (m.δ + θ) - m.p.Pe m.δ) * θ) ∧
      ∀ θ, |θ| < ρ → 0 ≤ m.potential θ := by
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = min 1 (m.p.k m.δ / (4 * (|m.p.A| + 1))) := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρdef]; exact lt_min one_pos (by positivity)
  have hρ1 : ρ ≤ 1 := by rw [hρdef]; exact min_le_left _ _
  have hρA : |m.p.A| * ρ ≤ m.p.k m.δ / 4 := by
    have h1 : ρ ≤ m.p.k m.δ / (4 * (|m.p.A| + 1)) := by rw [hρdef]; exact min_le_right _ _
    have hA1 : |m.p.A| + 1 ≠ 0 := by positivity
    calc |m.p.A| * ρ ≤ |m.p.A| * (m.p.k m.δ / (4 * (|m.p.A| + 1))) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = m.p.k m.δ / 4 * (|m.p.A| / (|m.p.A| + 1)) := by field_simp
      _ ≤ m.p.k m.δ / 4 := mul_le_of_le_one_right (by positivity)
          ((div_le_one (by positivity)).mpr (by linarith))
  refine ⟨ρ, hρ, hρ1, fun θ hθ => ?_, fun θ hθ => ?_⟩
  · have h := m.p.abs_Pe_add_sub_le m.δ θ
    have ha : 0 ≤ |m.p.A| := abs_nonneg _
    have hk' := hk
    have hρA' := hρA
    generalize m.p.Pe (m.δ + θ) - m.p.Pe m.δ = X at h ⊢
    generalize m.p.k m.δ = kk at h hk' hρA' ⊢
    generalize |m.p.A| = a at h ha hρA' ⊢
    have e1 : |(X - kk * θ) * θ| ≤ a * θ ^ 2 * |θ| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right h (abs_nonneg θ)
    have e2 : a * θ ^ 2 * |θ| ≤ a * θ ^ 2 * ρ :=
      mul_le_mul_of_nonneg_left hθ.le (mul_nonneg ha (sq_nonneg θ))
    have e3 : a * ρ * θ ^ 2 ≤ kk / 4 * θ ^ 2 := mul_le_mul_of_nonneg_right hρA' (sq_nonneg θ)
    have e4 := neg_abs_le ((X - kk * θ) * θ)
    have e5 : 0 ≤ kk * θ ^ 2 := mul_nonneg hk'.le (sq_nonneg θ)
    have e6 : X * θ = kk * θ ^ 2 + (X - kk * θ) * θ := by ring
    have e7 : a * θ ^ 2 * ρ = a * ρ * θ ^ 2 := by ring
    linarith
  · have h := pot_bound m (hθ.le.trans hρ1)
    have ha : 0 ≤ |m.p.A| := abs_nonneg _
    have hk' := hk
    have hρA' := hρA
    have e : |θ| ^ 3 = |θ| * θ ^ 2 := by rw [pow_succ, sq_abs]; ring
    rw [e] at h
    generalize m.potential θ = X at h ⊢
    generalize m.p.k m.δ = kk at h hk' hρA' ⊢
    generalize |m.p.A| = a at h ha hρA' ⊢
    have e2 : a * (|θ| * θ ^ 2) ≤ a * (ρ * θ ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hθ.le (sq_nonneg θ)) ha
    have e3 : a * ρ * θ ^ 2 ≤ kk / 4 * θ ^ 2 := mul_le_mul_of_nonneg_right hρA' (sq_nonneg θ)
    have e4 := neg_abs_le (X - kk * θ ^ 2 / 2)
    have e5 : 0 ≤ kk * θ ^ 2 := mul_nonneg hk'.le (sq_nonneg θ)
    have e6 : a * (ρ * θ ^ 2) = a * ρ * θ ^ 2 := by ring
    linarith

/-- The potential is at most `(k + |A|) θ²` for `|θ| ≤ 1`, `k(δ*) > 0`. -/
@[tmio M, powerlib_domain] private theorem potential_le (m : Model) (hk : 0 < m.p.k m.δ)
    {θ : ℝ} (hθ : |θ| ≤ 1) : m.potential θ ≤ (m.p.k m.δ + |m.p.A|) * θ ^ 2 := by
  have h := pot_bound m hθ
  have ha : 0 ≤ |m.p.A| := abs_nonneg _
  have hk' := hk
  have e : |θ| ^ 3 = |θ| * θ ^ 2 := by rw [pow_succ, sq_abs]; ring
  rw [e] at h
  generalize m.potential θ = X at h ⊢
  generalize m.p.k m.δ = kk at h hk' ⊢
  generalize |m.p.A| = a at h ha ⊢
  have e2 : a * (|θ| * θ ^ 2) ≤ a * θ ^ 2 :=
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (sq_nonneg θ) hθ) ha
  have e4 := le_abs_self (X - kk * θ ^ 2 / 2)
  have e5 : 0 ≤ kk * θ ^ 2 := mul_nonneg hk'.le (sq_nonneg θ)
  have e6 : (kk + a) * θ ^ 2 = kk * θ ^ 2 + a * θ ^ 2 := by ring
  linarith

/-- The DC row off the plane at the degenerate balance (`I_s = 0`, `P_s = P_e(δ*)`):
`V̇ = (−ΔP(θ)/V)/C`. -/
@[tmio M, powerlib_domain] private theorem field_two_of_balance (m : Model) (hIs : m.p.Is = 0)
    (hP : m.p.Ps = m.p.Pe m.δ) (y : State 4) :
    m.p.field y 2 = (-(m.p.Pe (m.δ + (y 0 - m.δ)) - m.p.Pe m.δ) / y 2) / m.p.C := by
  rw [Params.field_apply_two]
  simp only [Plant.nodeRate, GFL.DCLink.nodeRate, hIs, hP, zero_add]
  rw [show m.δ + (y 0 - m.δ) = y 0 by ring]
  ring

@[tmio T, powerlib_foundation] private theorem fderiv_sq_two (y v : State 4) :
    fderiv ℝ (fun y : State 4 => y 2 ^ 2) y v = 2 * y 2 * v 2 := by
  have h2 : HasFDerivAt (fun y : State 4 => y 2) (PiLp.proj 2 (fun _ : Fin 4 => ℝ) 2) y :=
    (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (2 : Fin 4) : State 4 →L[ℝ] ℝ).hasFDerivAt
  rw [(h2.pow 2).fderiv]
  simp

/-- The seeds of `mem_den_unstable_of_invariant_stiff_degenerate`: arbitrarily close to the
point, `(δ* − C τ, 0, σ h, ζ* + σ h)` lies on the escape side with a positive barrier. -/
@[tmio M, powerlib_domain] private theorem stiff_seed (m : Model) (hV : m.p.Vref = 0)
    (hk : 0 < m.p.k m.δ) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hσ2 : σ * σ = 1)
    (hσgC : σ * (m.p.Kp + m.p.Ki) * m.p.C < 0) {δ' : ℝ} (hδ' : 0 < δ') :
    ∃ y₀ : State 4, ∃ w₀ > 0, ‖y₀ - m.point‖ < δ' ∧ 0 < σ * y₀ 2 ∧
      0 < (m.p.Kp * y₀ 2 + m.p.Ki * (y₀ 3 - m.ζ)) * (y₀ 0 - m.δ) -
        m.potential (y₀ 0 - m.δ) - m.p.M / 2 * y₀ 1 ^ 2 - w₀ ∧
      0 < -m.p.C * (y₀ 0 - m.δ) := by
  have hC : m.p.C ≠ 0 := fun h => by rw [h, mul_zero] at hσgC; exact lt_irrefl _ hσgC
  have hg : m.p.Kp + m.p.Ki ≠ 0 := fun h => by
    rw [h, mul_zero, zero_mul] at hσgC; exact lt_irrefl _ hσgC
  obtain ⟨p0, p1, p2, p3⟩ := point_apply_of_V_eq_zero m hV
  have hA0 : 0 ≤ |m.p.A| := abs_nonneg _
  have hC0 : 0 < |m.p.C| := abs_pos.mpr hC
  have hgabs : 0 < |m.p.Kp + m.p.Ki| := abs_pos.mpr hg
  obtain ⟨h, τ, hh0, hτ0, hsmall, hτ1, hτA⟩ := stiff_seed_constants hk hA0 hC0 hgabs hδ'
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀, θ₀ = -(m.p.C * τ) := ⟨_, rfl⟩
  have hθ₀abs : |θ₀| = |m.p.C| * τ := by rw [hθ₀, abs_neg, abs_mul, abs_of_pos hτ0]
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : State 4, y₀ = m.point + (EuclideanSpace.single 0 θ₀ +
      EuclideanSpace.single 2 (σ * h) + EuclideanSpace.single 3 (σ * h)) := ⟨_, rfl⟩
  have c0 : y₀ 0 = m.δ + θ₀ := by simp [hy₀, p0]
  have c1 : y₀ 1 = 0 := by simp [hy₀, p1]
  have c2 : y₀ 2 = σ * h := by simp [hy₀, p2]
  have c3 : y₀ 3 = m.ζ + σ * h := by simp [hy₀, p3]
  have hσh : |σ * h| = h := by
    rw [abs_mul, abs_of_pos hh0]; rcases hσ with rfl | rfl <;> simp
  have hpot : m.potential θ₀ ≤ (m.p.k m.δ + |m.p.A|) * θ₀ ^ 2 :=
    potential_le m hk (le_trans (le_of_eq hθ₀abs) (by linarith only [hτ1]))
  have hθ₀2 : θ₀ ^ 2 = |m.p.C| * τ * (|m.p.C| * τ) := by rw [← sq_abs, hθ₀abs, sq]
  have habs : -(σ * (m.p.Kp + m.p.Ki) * m.p.C) = |m.p.Kp + m.p.Ki| * |m.p.C| := by
    have : |σ * (m.p.Kp + m.p.Ki) * m.p.C| = |m.p.Kp + m.p.Ki| * |m.p.C| := by
      rw [abs_mul, abs_mul]; rcases hσ with rfl | rfl <;> simp
    rw [← this, abs_of_neg hσgC]
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, w₀ = (|m.p.Kp + m.p.Ki| * |m.p.C| * h * τ - m.potential θ₀) / 2 :=
    ⟨_, rfl⟩
  have hw₀pos : 0 < w₀ := by
    rw [hθ₀2] at hpot
    have h2 : (m.p.k m.δ + |m.p.A|) * (|m.p.C| * τ * (|m.p.C| * τ)) ≤
        |m.p.C| * τ * (|m.p.Kp + m.p.Ki| * h / 2) := by
      have := mul_le_mul_of_nonneg_left hτA (mul_pos hC0 hτ0).le
      calc (m.p.k m.δ + |m.p.A|) * (|m.p.C| * τ * (|m.p.C| * τ)) =
            |m.p.C| * τ * ((m.p.k m.δ + |m.p.A|) * |m.p.C| * τ) := by ring
        _ ≤ _ := this
    have h3 : 0 < |m.p.C| * τ * (|m.p.Kp + m.p.Ki| * h) :=
      mul_pos (mul_pos hC0 hτ0) (mul_pos hgabs hh0)
    have h4 : |m.p.Kp + m.p.Ki| * |m.p.C| * h * τ = |m.p.C| * τ * (|m.p.Kp + m.p.Ki| * h) := by
      ring
    rw [hw₀]
    linarith only [hpot, h2, h3, h4]
  refine ⟨y₀, w₀, hw₀pos, ?_, ?_, ?_, ?_⟩
  · rw [hy₀, add_sub_cancel_left]
    refine (norm_seed_le θ₀ (σ * h) (σ * h)).trans_lt ?_
    rw [hσh, hθ₀abs]
    linarith only [hsmall]
  · rw [c2, ← mul_assoc, hσ2, one_mul]; exact hh0
  · rw [c0, c1, c2, c3, show m.δ + θ₀ - m.δ = θ₀ by ring, show m.ζ + σ * h - m.ζ = σ * h by ring]
    have e3 : (m.p.Kp * (σ * h) + m.p.Ki * (σ * h)) * θ₀ =
        -(σ * (m.p.Kp + m.p.Ki) * m.p.C) * h * τ := by rw [hθ₀]; ring
    rw [e3, habs]
    have e4 : |m.p.Kp + m.p.Ki| * |m.p.C| * h * τ - m.potential θ₀ = 2 * w₀ := by rw [hw₀]; ring
    have e5 : m.p.M / 2 * (0 : ℝ) ^ 2 = 0 := by ring
    rw [e5]
    linarith only [e4, hw₀pos]
  · rw [c0, show m.δ + θ₀ - m.δ = θ₀ by ring, hθ₀]
    have : -m.p.C * -(m.p.C * τ) = m.p.C ^ 2 * τ := by ring
    rw [this]
    exact mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hC))) hτ0

/-- The core of `mem_den_unstable_of_invariant_stiff_degenerate` for `M > 0`. -/
@[tmio TM, powerlib_domain] private theorem unstable_stiff_core (m : Model)
    (hV : m.p.Vref = 0) (hI : m.p.Is / m.p.C = 0) (hC : m.p.C ≠ 0)
    (hP : m.p.Ps = m.p.Pe m.δ) (hb : m.p.Pff + m.p.Ki * m.ζ = m.p.Pe m.δ) (hM : 0 < m.p.M)
    (hk : 0 < m.p.k m.δ) (hD : 0 ≤ m.p.D) (hgain : m.p.Kp ≠ 0 ∨ m.p.Ki ≠ 0)
    (hsame : 0 ≤ m.p.Kp * m.p.Ki) : Unstable m.p.field m.point := by
  have hIs : m.p.Is = 0 := by rwa [div_eq_zero_iff, or_iff_left hC] at hI
  obtain ⟨p0, p1, p2, p3⟩ := point_apply_of_V_eq_zero m hV
  obtain ⟨σ, hσ, hσ2, hσgC, hKpσ, hKiσ, hKpσ', hKiσ'⟩ := stiff_signs hC hgain hsame
  obtain ⟨ρ, hρ, -, hΔ, hPot⟩ := stiff_curve m hk
  refine Dynamics.Degenerate.unstable_of_barriers 2 (σ := σ) hρ (fun s hs => ?_) fun δ' hδ' => ?_
  · obtain ⟨G, hG, hGf⟩ := m.p.exists_contDiff_eq_field_of_sign hσ hs
    exact ⟨G, hG, fun y _ hy => hGf y hy⟩
  obtain ⟨y₀, w₀, hw₀, hy₀x, hσ0, hW1₀, hW2₀⟩ := stiff_seed m hV hk hσ hσ2 hσgC hδ'
  have hden : 0 < (|m.p.Kp| + |m.p.Ki|) * ρ + 1 := by
    have := mul_nonneg (add_nonneg (abs_nonneg m.p.Kp) (abs_nonneg m.p.Ki)) hρ.le
    linarith only [this]
  refine ⟨y₀, hy₀x, hσ0,
    fun y => (m.p.Kp * y 2 + m.p.Ki * (y 3 - m.ζ)) * (y 0 - m.δ) - m.potential (y 0 - m.δ) -
      m.p.M / 2 * y 1 ^ 2 - w₀,
    fun y => -m.p.C * (y 0 - m.δ), fun _ => 1, fun y => y 2 ^ 2,
    m.p.k m.δ * (w₀ / ((|m.p.Kp| + |m.p.Ki|) * ρ + 1)) / |m.p.C|, ρ ^ 2,
    div_pos (mul_pos hk (div_pos hw₀ hden)) (abs_pos.mpr hC),
    by unfold Model.potential; fun_prop, by fun_prop, contDiff_const, by fun_prop, hW1₀, hW2₀,
    one_pos, fun y hy => ?_, fun y hy hσy hW1 hW2 _ => ?_⟩
  · -- `V²` is bounded near the point
    have h1 := Dynamics.abs_coord_sub_le m.point y 2
    rw [p2, sub_zero] at h1
    have h2 : |y 2| < ρ := lt_of_le_of_lt h1 hy
    show y 2 ^ 2 ≤ ρ ^ 2
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h2.le 2
  · -- the trapping region
    have hθρ : |y 0 - m.δ| < ρ := by
      have := Dynamics.abs_coord_sub_le m.point y 0; rw [p0] at this; exact lt_of_le_of_lt this hy
    have hVρ : |y 2| < ρ := by
      have := Dynamics.abs_coord_sub_le m.point y 2; rw [p2, sub_zero] at this
      exact lt_of_le_of_lt this hy
    have huρ : |y 3 - m.ζ| < ρ := by
      have := Dynamics.abs_coord_sub_le m.point y 3; rw [p3] at this; exact lt_of_le_of_lt this hy
    have hσV : 0 < σ * y 2 := by linarith only [hσy, hσ0]
    have hy2 : y 2 ≠ 0 := fun h0 => by rw [h0, mul_zero] at hσV; exact lt_irrefl _ hσV
    have hW1' : 0 ≤ (m.p.Kp * y 2 + m.p.Ki * (y 3 - m.ζ)) * (y 0 - m.δ) -
        m.potential (y 0 - m.δ) - m.p.M / 2 * y 1 ^ 2 - w₀ := hW1
    have hW2' : 0 ≤ -m.p.C * (y 0 - m.δ) := hW2
    obtain ⟨r1, r2, r3, r4⟩ := stiff_region (σ := σ) (Kp := m.p.Kp) (Ki := m.p.Ki) (C := m.p.C)
      (D := m.p.D) (M := m.p.M) (K := m.p.k m.δ) (w₀ := w₀) (ρ := ρ) (θ := y 0 - m.δ)
      (V := y 2) (u := y 3 - m.ζ) (ω := y 1) (X := m.p.Pe (m.δ + (y 0 - m.δ)) - m.p.Pe m.δ)
      (Pt := m.potential (y 0 - m.δ)) hσ2 hKpσ hKiσ hKpσ' hKiσ' hgain hC hM hD hk
      hw₀ hρ hVρ huρ hσV (hPot _ hθρ) (hΔ _ hθρ) hW1' hW2'
    refine ⟨by rw [field_two_of_balance m hIs hP y]; exact r1,
      by rw [fderiv_sq_two, field_two_of_balance m hIs hP y]; exact r2, fun _ => ?_,
      fun h0 => ?_, fun h0 => absurd h0 one_ne_zero⟩
    · rw [barrier_rate m hV hIs hP hb hM.ne' hC w₀ hy2]; exact r3
    · exfalso
      have h5 : -m.p.C * (y 0 - m.δ) = 0 := h0
      have h6 : m.p.C * (y 0 - m.δ) = 0 := by linarith only [h5]
      linarith only [h6, r4]

/-- The same converter with every power, gain, inertia, damping and capacitance negated: the
field is unchanged (each row is a quotient of negated quantities). -/
private def Model.neg (m : Model) : Model :=
  ⟨{ toPlant :=
      { M := -m.p.M, D := -m.p.D, C := -m.p.C, Pff := -m.p.Pff, c0 := -m.p.c0
        A := -m.p.A, α := m.p.α, Ps := -m.p.Ps, Is := -m.p.Is }
     Vref := m.p.Vref, Kp := -m.p.Kp, Ki := -m.p.Ki }, m.δ, m.ζ⟩

@[tmio M, powerlib_domain] private theorem Model.neg_field (m : Model) :
    m.neg.p.field = m.p.field := by
  funext y
  ext i
  fin_cases i
  · simp [Model.neg]
  · simp only [Fin.mk_one, Params.field_apply_one, Plant.swingRate, Params.Pref, Plant.Pe,
      Model.neg]
    rw [div_neg]
    ring
  · simp only [Fin.reduceFinMk, Params.field_apply_two, Plant.nodeRate, GFL.DCLink.nodeRate,
      Plant.Pe, Model.neg]
    rw [div_neg]
    ring
  · simp [Model.neg]

/-- **Invariant singular plane, degenerate balance, stiff swing, DC gains of one sign: the DC
voltage escapes.** With `V* = 0`, `I_s/C = 0`, `C ≠ 0`, `P_s = P_e(δ*)`, the frozen swing balanced
(`P_ff + K_i ζ* = P_e(δ*)`), stiff and not negatively damped (`0 < k(δ*)/M`, `0 ≤ D/M`) and DC
gains `(K_p, K_i) ≠ (0, 0)` with `K_p K_i ≥ 0`, every selected point is unstable. For `M > 0`
(`unstable_stiff_core`; `M < 0` through the negated converter `Model.neg`, the same field): on the
side
`σ V > 0` with `σ (K_p + K_i) C < 0` the function `W = F θ − Π(θ) − M ω²/2`
(`F = K_p V + K_i (ζ − ζ*)`
the power reference's deviation, `θ = δ − δ*`, `Π` the potential of the power curve) changes at the
rate `Ẇ = D ω² − K_p θ ΔP(θ)/(C V) + K_i θ V ≥ 0` (positive where `W > 0`): it traps the solution in
`{W ≥ W₀/2, C θ ≤ 0}`, where the swing angle stays on the side `ΔP(θ)/C < 0`, so `C V V̇ = −ΔP(θ)`
drives `V²` up at a uniform rate and the DC voltage leaves every small ball
(`Dynamics.Degenerate.unstable_of_barriers`, the seeds `(δ* − C τ, 0, σ h, ζ* + σ h)`). -/
@[tmio TM, powerlib_domain] theorem mem_den_unstable_of_invariant_stiff_degenerate (m : Model)
    (hV : m.p.Vref = 0) (hI : m.p.Is / m.p.C = 0) (hC : m.p.C ≠ 0)
    (hP : m.p.Ps = m.p.Pe m.δ) (hb : m.p.Pff + m.p.Ki * m.ζ = m.p.Pe m.δ)
    (hk : 0 < m.p.k m.δ / m.p.M) (hD : 0 ≤ m.p.D / m.p.M) (hgain : m.p.Kp ≠ 0 ∨ m.p.Ki ≠ 0)
    (hsame : 0 ≤ m.p.Kp * m.p.Ki) :
    connection% (m ∈ family.den (.flow .unstable)) := by
  unfold TMIO.Statement
  rw [mem_den_flow_iff]
  have hM : m.p.M ≠ 0 := fun h => by simp [h] at hk
  rcases hM.lt_or_gt with hM | hM
  · -- `M < 0`: the negated converter has the same field and `M > 0`
    have hk0 : m.p.k m.δ < 0 := by
      by_contra h
      exact absurd hk (not_lt.mpr (div_nonpos_of_nonneg_of_nonpos (not_lt.mp h) hM.le))
    have hD0 : m.p.D ≤ 0 := by
      by_contra h
      exact absurd hD (not_le.mpr (div_neg_of_pos_of_neg (not_le.mp h) hM))
    have ek : m.neg.p.k m.neg.δ = -m.p.k m.δ := by simp [Model.neg, Plant.k]
    have ePe : ∀ δ, m.neg.p.Pe δ = -m.p.Pe δ := fun δ => by simp [Model.neg, Plant.Pe]; ring
    have hu := unstable_stiff_core m.neg (by simpa [Model.neg] using hV)
      (by simp only [Model.neg]; rw [neg_div_neg_eq]; exact hI)
      (by simpa [Model.neg] using hC)
      (by rw [ePe]; simp only [Model.neg]; rw [hP])
      (by rw [ePe]; simp only [Model.neg]; linarith)
      (by simp only [Model.neg]; linarith) (by rw [ek]; linarith)
      (by simp only [Model.neg]; linarith) (by simpa [Model.neg] using hgain)
      (by simp only [Model.neg]; nlinarith)
    rwa [Model.neg_field, show m.neg.point = m.point from rfl] at hu
  · exact unstable_stiff_core m hV hI hC hP hb hM ((div_pos_iff_of_pos_right hM).mp hk)
      ((div_nonneg_iff.mp hD).elim (fun h => h.1) fun h => absurd h.2 (not_le.mpr hM)) hgain
      hsame

end VSMDC

namespace Params

variable (p : Params)

/-- The open loop's first integral on the plane, as far as it survives the DC loop:
`V² − (2/C)(M ω + D δ − K_p ζ)`. -/
def planeIntegral (y : State 4) : ℝ :=
  y 2 ^ 2 - 2 / p.C * (p.M * y 1 + p.D * y 0 - p.Kp * y 3)

/-- **The first integral survives the proportional gain, not the integral one.** Off the plane,
with `V* = 0`, `I_s/C = 0` and `M ≠ 0`, `d/dt planeIntegral = 2 (P_s − P_ff − K_i ζ)/C`: the term
`K_p V` of the swing is `K_p ζ̇`; at the degenerate balance of a frozen swing
(`P_s = P_ff + K_i ζ*`) the rate is `−2 K_i (ζ − ζ*)/C`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem planeIntegral_lie (hV : p.Vref = 0) (hI : p.Is / p.C = 0)
    (hM : p.M ≠ 0) {y : State 4} (hy : y 2 ≠ 0) :
    fderiv ℝ p.planeIntegral y (p.field y) = 2 * (p.Ps - p.Pff - p.Ki * y 3) / p.C := by
  have h0 := Dynamics.hasFDerivAt_coord 0 y
  have h1 := Dynamics.hasFDerivAt_coord 1 y
  have h2 := Dynamics.hasFDerivAt_coord 2 y
  have h3 := Dynamics.hasFDerivAt_coord 3 y
  have h := (h2.pow 2).sub ((((h1.const_mul p.M).add (h0.const_mul p.D)).sub
    (h3.const_mul p.Kp)).const_mul (2 / p.C))
  have hE : HasFDerivAt p.planeIntegral _ y := h
  rw [hE.fderiv]
  by_cases hC : p.C = 0
  · simp [hC, Plant.nodeRate, GFL.DCLink.nodeRate]
  have hIs : p.Is = 0 := by
    rw [div_eq_zero_iff, or_iff_left hC] at hI
    exact hI
  simp [Plant.nodeRate, GFL.DCLink.nodeRate, Plant.swingRate, Pref, Plant.Pe, hV, hIs]
  field_simp
  ring

/-- **The integrator reads the DC voltage**, `ζ̇ = V − V*`: the field never meets the hypothesis
`f(y − y_V e_V) = f(y) − f_V(y) e_V` of the open loop's first-integral law
(`Dynamics.Degenerate.lyapunovStable_iff_of_invariantPlane_firstIntegral`), whatever the gains.
Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem not_forall_field_sub_single :
    ¬ ∀ y : State 4, p.field (y - y 2 • EuclideanSpace.single 2 (1 : ℝ)) =
      p.field y - p.field y 2 • EuclideanSpace.single 2 (1 : ℝ) := by
  intro h
  have h3 := congrArg (fun v : State 4 => v 3) (h (EuclideanSpace.single 2 (1 : ℝ)))
  simp at h3
  linarith

end Params

end powerlib.GFM.DCLink
