import theorem.GridTiedConverter.GFM.Discrete.SwingPort
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Grid-forming swing synchronization discretized by a discrete gradient: passivity

The two-state grid-forming swing law with the set-point port (`SwingPort.Params.field`) is, in
the momentum coordinate `p = M Δω`, a port-Hamiltonian system with constant structure
`J = [[0, 1], [−1, 0]]`, `R = diag(0, D)`, `g = (0, 1)ᵀ` and the separable energy
`H(δ, p) = U(δ) + p²/(2M)`, `U(δ) = −(P_ref − c₀) δ + A (1 − cos(δ − α))`
(`SwingPort.dg_self`: the discrete-gradient right-hand side on the diagonal is the swing field).
Discretized by the discrete-gradient method with the separable discrete gradient
(`Numerics.separableDiscreteGradient`), with the discrete-gradient output `ω̄ = (p + p⁺)/(2M)`,
it is passive exactly when the set-point is matched, `P_ref = c₀` — the discrete counterpart of
`SwingPort.mem_den_passive_iff`, unlike the explicit Euler discretization, which is never passive
(`SwingPort.euler_not_mem_den_passive`). With `P_ref = c₀` the energy is nonnegative and the
generic discrete-gradient law gives the storage `H`; with `P_ref ≠ c₀` a discrete slow spin at the
speed `ω₀ = (P_ref − c₀)/(2 (D + 1))`, held by the port, draws `h ω₀ ((P_ref − c₀) − D ω₀)` per step
up to the bounded electrical potential, without bound over many steps.

Model boundary.
* The parameters `SwingPort.Params` (`M > 0`, `D ≥ 0`, `A > 0`, any `c₀`, `α`, `P_ref`); state
  `(δ, p)`, `p = M Δω`, uncentred (passivity does not depend on the selected angle); one port, the
  set-point deviation `u`.
* Discretization: any discrete-time system with `2` states and `1` port whose steps solve the
  discrete-gradient relation `x⁺ − x = h ((J − R) ∇̄H(x, x⁺) + g u)` with its step length `h`
  and whose output is the discrete-gradient output `gᵀ ∇̄H(x, x⁺)`; for the converse the relation
  is required to determine the step. The implicit step exists for every `h > 0` and is unique for
  every state and input exactly when `A h² ≤ 4 M + 2 D h` (below); exact arithmetic, fixed
  step.
* Excluded: the power filter, the line dynamics and every exclusion of
  `theorem/GridTiedConverter/GFM/Discrete/SwingPort.lean`; other discrete gradients (the results
  are stated for the separable one).

Source: work-sync GFM study note t9 (scratchpad `gfm/t9-discrete/REPORT-coord.md`, (c):
nonlinear discrete gradient passive iff `P_ref = c₀`; script `s5_dg_nonlinear_and_sims.py`);
`theorem/Numerics/DiscreteGradient.lean` (`Numerics.separableDiscreteGradient`,
`Numerics.discreteGradient_dissipation`), `theorem/Numerics/EulerPorts.lean`
(`Numerics.discreteGradient_passiveWith`, `Map.System.not_passive_of_feedback_supply_unbounded`);
Gonzalez, "Time integration and discrete Hamiltonian systems", J. Nonlinear Sci. 6 (1996);
Celledoni and Høiseth, "Energy-preserving and passivity-consistent numerical discretization of
port-Hamiltonian systems" (2017).

Results.
* `SwingPort.swingJ`, `SwingPort.Params.swingR`, `SwingPort.swingG` (the structure matrices),
  `SwingPort.Params.potential`, `SwingPort.Params.potentialDeriv`, `SwingPort.Params.dg` (the
  separable discrete gradient of the energy); `SwingPort.dg_self` (consistency: on the diagonal
  the discrete-gradient right-hand side is the swing field in momentum coordinates).
* `SwingPort.dg_passive`: with `P_ref = c₀`, every such discretization with a step `h ≥ 0` is
  passive (storage `H ≥ 0`, `Numerics.discreteGradient_passiveWith`).
* `SwingPort.dg_not_passive`: with `P_ref ≠ c₀`, every such discretization with a step `h > 0`
  whose relation determines the step is not passive
  (`Map.System.not_passive_of_feedback_supply_unbounded` along the discrete slow spin).
* The implicit step. `SwingPort.Params.DGRelation` (the relation), `SwingPort.Params.dgPhi` (its
  scalar form): `SwingPort.dg_zero_eq_integral` (`∇̄₁H = −(P_ref − c₀) + A ∫₀¹ sin(δ − α +
  t (δ⁺ − δ)) dt` on and off the diagonal), `SwingPort.dgRelation_iff` (the relation is
  `p⁺ = 2 M (δ⁺ − δ)/h − p` and `Φ(δ⁺ − δ) = 2 p + h u`,
  `Φ(d) = (2 M/h + D) d + h (−(P_ref − c₀) + A ∫₀¹ sin(θ + t d) dt)`).
  Existence: `SwingPort.exists_dgRelation` (every `h > 0`, every state and input: `Φ` is
  continuous and within `h (|P_ref − c₀| + A)` of `(2 M/h + D) d`, intermediate value theorem),
  `SwingPort.exists_dg_system` (a discrete system realizing the method exists for every `h > 0`).
  Uniqueness, exactly: `SwingPort.dgRelation_unique` (`A h² ≤ 4 M + 2 D h`: `Φ` is strictly
  increasing, `|sin a − sin b| < |a − b|` for `a ≠ b` under the integral),
  `SwingPort.exists_dgRelation_ne` (`A h² > 4 M + 2 D h`: two solutions from `δ = α + π`, the
  maximum of the electrical potential, `h A (1 − cos d) = (2 M/h + D) d²` with `d > 0`),
  `SwingPort.dgRelation_unique_iff` (unique for every state and input iff
  `A h² ≤ 4 M + 2 D h`). Hence `SwingPort.dg_passive_iff`: for `0 < h` with `A h² ≤ 4 M + 2 D h`
  a discrete system realizing the method is passive iff `P_ref = c₀`.
-/

noncomputable section

namespace powerlib.GFM.SwingPort

open powerlib.Dynamics (State)
open Matrix

/-- The interconnection of the swing law in momentum coordinates, `J = [[0, 1], [−1, 0]]`. -/
def swingJ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- The dissipation of the swing law, `R = diag(0, D)`. -/
def Params.swingR (g : Params) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![0, g.D]

/-- The input matrix of the set-point port, `g = (0, 1)ᵀ`. -/
def swingG : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]

/-- The potential `U(δ) = −(P_ref − c₀) δ + A (1 − cos(δ − α))`: the work of the set-point
against the line's constant power plus the electrical potential, which is zero at `δ = α`. -/
def Params.potential (g : Params) (δ : ℝ) : ℝ :=
  -(g.Pref - g.c0) * δ + g.A * (1 - Real.cos (δ - g.α))

/-- `U'(δ) = P(δ) − P_ref`, the electrical power less the set-point. -/
def Params.potentialDeriv (g : Params) (δ : ℝ) : ℝ := g.power δ - g.Pref

/-- The separable discrete gradient of `H(δ, p) = U(δ) + p²/(2M)`. -/
def Params.dg (g : Params) :=
  Numerics.separableDiscreteGradient g.potential g.potentialDeriv (1 / g.M)

/-- **Consistency.** On the diagonal `x⁺ = x` the discrete-gradient right-hand side
`(J − R) ∇̄H(x, x) + g u` is the swing field `SwingPort.Params.field` in the momentum coordinates
`(δ, p) = (δ, M Δω)`. Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem dg_self (g : Params) (y : State 2) (u : Fin 1 → ℝ) :
    (swingJ - g.swingR) *ᵥ g.dg.dg (WithLp.ofLp y) (WithLp.ofLp y) + swingG *ᵥ u =
      WithLp.ofLp (Dynamics.scaleCoord g.M_pos.ne'
        (g.field ((Dynamics.scaleCoord g.M_pos.ne').symm y) u)) := by
  have hM := g.M_pos.ne'
  rw [Params.dg, Numerics.separableDiscreteGradient_dg_self, Dynamics.scaleCoord_symm_apply,
    Dynamics.scaleCoord_apply]
  ext i
  fin_cases i
  · simp [swingJ, Params.swingR, swingG, Params.field, Matrix.mulVec, dotProduct]
    ring
  · simp [swingJ, Params.swingR, swingG, Params.field, Params.potentialDeriv, Params.power,
      Matrix.mulVec, dotProduct]
    field_simp
    ring

@[tmio M, powerlib_domain] private theorem swingJ_skew : swingJᵀ = -swingJ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swingJ]

@[tmio M, powerlib_domain] private theorem swingR_posSemidef (g : Params) :
    g.swingR.PosSemidef :=
  PosSemidef.diagonal fun i => by fin_cases i <;> simp [g.D_nonneg]

/-- **The discrete-gradient discretization of the matched GFM swing is passive.** With
`P_ref = c₀` the energy `H = A (1 − cos(δ − α)) + p²/(2M)` is nonnegative, so every discrete
system with a step `h ≥ 0` whose steps solve the discrete-gradient relation and whose output is
the discrete-gradient output `ω̄` is passive with the storage `H`
(`Numerics.discreteGradient_passiveWith`). -/
@[tmio TM, powerlib_domain] theorem dg_passive (g : Params) (hg : g.Pref = g.c0)
    (s : Map.System 2 1) (hT : 0 ≤ s.period)
    (hstep : ∀ x u, WithLp.ofLp (s.step x u) - WithLp.ofLp x = s.period •
      ((swingJ - g.swingR) *ᵥ g.dg.dg (WithLp.ofLp x) (WithLp.ofLp (s.step x u)) +
        swingG *ᵥ u))
    (hout : ∀ x u, s.output x u = swingGᵀ *ᵥ g.dg.dg (WithLp.ofLp x) (WithLp.ofLp (s.step x u))) :
    s.Passive := by
  refine ⟨_, Numerics.discreteGradient_passiveWith s g.dg swingG swingJ_skew
    (swingR_posSemidef g) (fun z => ?_) hT hstep hout⟩
  have hc := Real.cos_le_one (z 0 - g.α)
  have hM := g.M_pos
  have : 0 ≤ 1 / g.M / 2 * z 1 ^ 2 := by positivity
  simp only [Params.potential, hg, sub_self, neg_zero, zero_mul, zero_add]
  nlinarith [g.A_pos]

/-- Along the slow spin `(δ, M ω₀) ↦ (δ + h ω₀, M ω₀)` the discrete gradient is
`(U[δ, δ + h ω₀], ω₀)` (`U[a, b]` the slope of `U`). -/
@[tmio M, powerlib_domain] private theorem spin_dg (g : Params) {h ω₀ : ℝ} (hω : h * ω₀ ≠ 0)
    (δ : ℝ) : g.dg.dg ![δ, g.M * ω₀] ![δ + h * ω₀, g.M * ω₀] =
      ![slope g.potential δ (δ + h * ω₀), ω₀] := by
  have hM := g.M_pos.ne'
  have hne : δ ≠ δ + h * ω₀ := fun e => hω (by linarith)
  have e : 1 / g.M * (g.M * ω₀ + g.M * ω₀) / 2 = ω₀ := by
    rw [← mul_two, mul_div_assoc, mul_div_cancel_right₀ _ two_ne_zero, ← mul_assoc,
      one_div, inv_mul_cancel₀ hM, one_mul]
  simp only [Params.dg, Numerics.separableDiscreteGradient, Matrix.cons_val_zero,
    Matrix.cons_val_one, e, hne, ↓reduceIte]

/-- The slow spin: from `(δ, M ω₀)` the step to `(δ + h ω₀, M ω₀)` solves the discrete-gradient
relation under the input `U[δ, δ + h ω₀] + D ω₀`. -/
@[tmio M, powerlib_domain] private theorem spin_relation (g : Params) {h ω₀ : ℝ} (hω : h * ω₀ ≠ 0)
    (δ : ℝ) :
    WithLp.ofLp (WithLp.toLp 2 ![δ + h * ω₀, g.M * ω₀] : State 2) -
        WithLp.ofLp (WithLp.toLp 2 ![δ, g.M * ω₀] : State 2) =
      h • ((swingJ - g.swingR) *ᵥ g.dg.dg ![δ, g.M * ω₀] ![δ + h * ω₀, g.M * ω₀] +
        swingG *ᵥ ![slope g.potential δ (δ + h * ω₀) + g.D * ω₀]) := by
  rw [spin_dg g hω δ]
  ext i
  fin_cases i
  · simp [swingJ, Params.swingR, swingG, Matrix.mulVec, dotProduct]
  · simp [swingJ, Params.swingR, swingG, Matrix.mulVec, dotProduct]
    right
    ring

/-- **The discrete-gradient discretization of the unmatched GFM swing is not passive.** With
`P_ref ≠ c₀` and a step `h > 0`, a discrete system whose step is the solution of the
discrete-gradient relation and whose output is the discrete-gradient output is not passive, for
any storage: the input `u = U[δ, δ + h ω₀] + D ω₀` holds the slow spin
`(δ_k, p_k) = (k h ω₀, M ω₀)`, `ω₀ = (P_ref − c₀)/(2 (D + 1))`, and over `N` steps supplies
`U(δ_N) − U(0) + N h D ω₀² ≤ N h ω₀ (D ω₀ − (P_ref − c₀)) + 2A`, which tends to `−∞`
(`Map.System.not_passive_of_feedback_supply_unbounded`). -/
@[tmio TM, powerlib_domain] theorem dg_not_passive (g : Params) (hg : g.Pref ≠ g.c0)
    (s : Map.System 2 1) (hT : 0 < s.period)
    (hunique : ∀ x u y, WithLp.ofLp y - WithLp.ofLp x = s.period •
      ((swingJ - g.swingR) *ᵥ g.dg.dg (WithLp.ofLp x) (WithLp.ofLp y) + swingG *ᵥ u) →
        s.step x u = y)
    (hout : ∀ x u, s.output x u = swingGᵀ *ᵥ g.dg.dg (WithLp.ofLp x) (WithLp.ofLp (s.step x u))) :
    ¬ s.Passive := by
  set h := s.period
  set Pm := g.Pref - g.c0 with hPm_def
  have hPm : Pm ≠ 0 := sub_ne_zero.mpr hg
  have hD := g.D_nonneg
  have hM := g.M_pos
  set ω₀ : ℝ := Pm / (2 * (g.D + 1)) with hω₀
  have hω₀0 : ω₀ ≠ 0 := div_ne_zero hPm (by positivity)
  have hhω : h * ω₀ ≠ 0 := mul_ne_zero hT.ne' hω₀0
  set κ : ℝ := ω₀ * (g.D * ω₀ - Pm) with hκ_def
  have hκ : κ < 0 := by
    have e : κ = -(Pm ^ 2 * (g.D + 2)) / (4 * (g.D + 1) ^ 2) := by
      rw [hκ_def, hω₀]
      field_simp
      ring
    rw [e, neg_div, neg_lt_zero]
    have : 0 < Pm ^ 2 := by positivity
    positivity
  -- the feedback and the closed-loop orbit
  let fb : State 2 → Fin 1 → ℝ := fun x => ![slope g.potential (x 0) (x 0 + h * ω₀) + g.D * ω₀]
  let F : State 2 → State 2 := fun x => s.step x (fb x)
  have hF : ∀ δ : ℝ, F (WithLp.toLp 2 ![δ, g.M * ω₀]) = WithLp.toLp 2 ![δ + h * ω₀, g.M * ω₀] :=
    fun δ => hunique _ _ _ (by simpa [fb] using spin_relation g hhω δ)
  have horbit : ∀ k : ℕ, F^[k] (WithLp.toLp 2 ![0, g.M * ω₀]) =
      WithLp.toLp 2 ![k * (h * ω₀), g.M * ω₀] := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, hF]
      congr 2
      push_cast
      ring
  -- the energy supplied over one step of the spin
  have hsup : ∀ δ : ℝ, s.supply (WithLp.toLp 2 ![δ, g.M * ω₀]) (fb (WithLp.toLp 2 ![δ, g.M * ω₀])) =
      g.potential (δ + h * ω₀) - g.potential δ + h * g.D * ω₀ ^ 2 := by
    intro δ
    have hsl := sub_smul_slope g.potential δ (δ + h * ω₀)
    rw [smul_eq_mul, vsub_eq_sub] at hsl
    have hs : s.step (WithLp.toLp 2 ![δ, g.M * ω₀]) (fb (WithLp.toLp 2 ![δ, g.M * ω₀])) =
        WithLp.toLp 2 ![δ + h * ω₀, g.M * ω₀] := hF δ
    rw [Map.System.supply, hout, hs]
    rw [spin_dg g hhω δ]
    simp [fb, swingG, Matrix.mulVec, dotProduct]
    linear_combination hsl
  have hsupply : ∀ k : ℕ, s.supply (F^[k] (WithLp.toLp 2 ![0, g.M * ω₀]))
      (fb (F^[k] (WithLp.toLp 2 ![0, g.M * ω₀]))) =
      g.potential ((k + 1 : ℕ) * (h * ω₀)) - g.potential (k * (h * ω₀)) + h * g.D * ω₀ ^ 2 := by
    intro k
    rw [horbit k, hsup, Nat.cast_succ, add_mul, one_mul]
  refine Map.System.not_passive_of_feedback_supply_unbounded s fb (WithLp.toLp 2 ![0, g.M * ω₀])
    fun c => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 * g.A - c) / (h * -κ))
  refine ⟨N, ?_⟩
  have hsum : ∑ k ∈ Finset.range N, s.supply (F^[k] (WithLp.toLp 2 ![0, g.M * ω₀]))
      (fb (F^[k] (WithLp.toLp 2 ![0, g.M * ω₀]))) =
      g.potential (N * (h * ω₀)) - g.potential 0 + N * (h * g.D * ω₀ ^ 2) := by
    rw [Finset.sum_congr rfl fun k _ => hsupply k, Finset.sum_add_distrib,
      Finset.sum_range_sub (fun k : ℕ => g.potential (k * (h * ω₀)))]
    simp
  change ∑ k ∈ Finset.range N, s.supply (F^[k] (WithLp.toLp 2 ![0, g.M * ω₀]))
      (fb (F^[k] (WithLp.toLp 2 ![0, g.M * ω₀]))) < c
  rw [hsum]
  have hcos1 := Real.neg_one_le_cos (N * (h * ω₀) - g.α)
  have hcos2 := Real.cos_le_one (0 - g.α)
  have hA := g.A_pos
  have hU : g.potential (N * (h * ω₀)) - g.potential 0 + N * (h * g.D * ω₀ ^ 2) ≤
      N * h * κ + 2 * g.A := by
    simp only [Params.potential, hκ_def]
    rw [← hPm_def]
    nlinarith [mul_le_mul_of_nonneg_left hcos2 hA.le, mul_le_mul_of_nonneg_left hcos1 hA.le]
  have hpos : 0 < h * -κ := mul_pos hT (neg_pos.mpr hκ)
  have hN' : 2 * g.A - c < N * (h * -κ) := (div_lt_iff₀ hpos).mp hN
  nlinarith

/-! ### The implicit step: existence and uniqueness -/

/-- The discrete-gradient relation of the swing law with step `h`:
`y − x = h ((J − R) ∇̄H(x, y) + g u)`. -/
def Params.DGRelation (g : Params) (h : ℝ) (x : Fin 2 → ℝ) (u : Fin 1 → ℝ) (y : Fin 2 → ℝ) :
    Prop :=
  y - x = h • ((swingJ - g.swingR) *ᵥ g.dg.dg x y + swingG *ᵥ u)

/-- The scalar step function `Φ(d) = (2 M/h + D) d + h (−(P_ref − c₀) + A ∫₀¹ sin(θ + t d) dt)`:
the discrete-gradient relation from `(δ, p)` is solved by the angle increment `d` with
`Φ(d) = 2 p + h u` (`θ = δ − α`). -/
def Params.dgPhi (g : Params) (h θ d : ℝ) : ℝ :=
  (2 * g.M / h + g.D) * d +
    h * (-(g.Pref - g.c0) + g.A * ∫ t in (0 : ℝ)..1, Real.sin (θ + t * d))

/-- **The first component of the separable discrete gradient is an average of the electrical
power**: `∇̄₁H(x, y) = −(P_ref − c₀) + A ∫₀¹ sin(x₀ − α + t (y₀ − x₀)) dt`, on the diagonal
(`U'`) and off it (the slope of `U`, `∫ sin = cos a − cos b`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem dg_zero_eq_integral (g : Params) (x y : Fin 2 → ℝ) :
    g.dg.dg x y 0 = -(g.Pref - g.c0) +
      g.A * ∫ t in (0 : ℝ)..1, Real.sin (x 0 - g.α + t * (y 0 - x 0)) := by
  simp only [Params.dg, Numerics.separableDiscreteGradient, Matrix.cons_val_zero]
  by_cases hd : x 0 = y 0
  · rw [ite_eq_left hd, ← hd, sub_self]
    simp only [mul_zero, add_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
      one_mul, Params.potentialDeriv, Params.power]
    ring
  · rw [ite_eq_right hd, slope_def_field]
    have hd' : y 0 - x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hd)
    have hint : ∫ t in (0 : ℝ)..1, Real.sin (x 0 - g.α + t * (y 0 - x 0)) =
        (Real.cos (x 0 - g.α) - Real.cos (y 0 - g.α)) / (y 0 - x 0) := by
      have e : (fun t => Real.sin (x 0 - g.α + t * (y 0 - x 0))) =
          fun t => Real.sin ((y 0 - x 0) * t + (x 0 - g.α)) := by
        funext t; ring_nf
      rw [e, intervalIntegral.integral_comp_mul_add (fun t => Real.sin t) hd', integral_sin,
        smul_eq_mul, mul_zero, zero_add, mul_one,
        show y 0 - x 0 + (x 0 - g.α) = y 0 - g.α by ring, inv_mul_eq_div]
    rw [hint, Params.potential, Params.potential]
    field_simp
    ring

@[tmio M, powerlib_domain] private theorem relation_vec (g : Params) (v : Fin 2 → ℝ)
    (u : Fin 1 → ℝ) :
    (swingJ - g.swingR) *ᵥ v + swingG *ᵥ u = ![v 1, -v 0 - g.D * v 1 + u 0] := by
  ext i
  fin_cases i
  all_goals simp [swingJ, Params.swingR, swingG, dotProduct, Fin.sum_univ_two, Matrix.diagonal,
    Matrix.vecHead, Matrix.vecTail]
  ring_nf

@[tmio M, powerlib_domain] private theorem dg_one (g : Params) (x y : Fin 2 → ℝ) :
    g.dg.dg x y 1 = 1 / g.M * (x 1 + y 1) / 2 := by
  simp [Params.dg, Numerics.separableDiscreteGradient]

/-- The discrete-gradient relation in components: `y₁ = 2 M (y₀ − x₀)/h − x₁` and
`Φ(y₀ − x₀) = 2 x₁ + h u` (`h ≠ 0`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem dgRelation_iff (g : Params) {h : ℝ} (hh : h ≠ 0)
    (x : Fin 2 → ℝ) (u : Fin 1 → ℝ) (y : Fin 2 → ℝ) :
    g.DGRelation h x u y ↔ y 1 = 2 * g.M * (y 0 - x 0) / h - x 1 ∧
      g.dgPhi h (x 0 - g.α) (y 0 - x 0) = 2 * x 1 + h * u 0 := by
  have hM := g.M_pos.ne'
  unfold Params.DGRelation Params.dgPhi
  rw [relation_vec, dg_one, dg_zero_eq_integral]
  set I := ∫ t in (0 : ℝ)..1, Real.sin (x 0 - g.α + t * (y 0 - x 0))
  constructor
  · intro hr
    have r0 := congrFun hr 0
    have r1 := congrFun hr 1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one] at r0 r1
    have r0' : 2 * g.M * (y 0 - x 0) = h * (x 1 + y 1) := by
      rw [r0]; field_simp
    refine ⟨?_, ?_⟩
    · rw [eq_sub_iff_add_eq, eq_div_iff hh]
      linear_combination -r0'
    · have e1 : 2 * g.M / h * (y 0 - x 0) = x 1 + y 1 := by
        field_simp
        linear_combination r0'
      have e2 : g.D * (y 0 - x 0) = g.D * h * (x 1 + y 1) / (2 * g.M) := by
        rw [r0]; ring
      have e3 : h * (-(g.Pref - g.c0) + g.A * I) =
          h * u 0 - (y 1 - x 1) - g.D * h * (x 1 + y 1) / (2 * g.M) := by
        linear_combination r1
      rw [add_mul, e1, e2, e3]
      ring
  · rintro ⟨h1, h2⟩
    have hd : y 0 - x 0 = h * (1 / g.M * (x 1 + y 1) / 2) := by
      rw [h1]; field_simp; ring
    funext i
    fin_cases i
    · simpa using hd
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, Fin.mk_one, Fin.isValue]
      linear_combination h1 - g.D * hd + h2

/-- The step function is continuous in the increment (`intervalIntegral` of a continuous
integrand with a parameter). -/
@[tmio M, powerlib_domain] private theorem continuous_dgPhi (g : Params) (h θ : ℝ) :
    Continuous (g.dgPhi h θ) := by
  unfold Params.dgPhi
  have : Continuous fun d : ℝ => ∫ t in (0 : ℝ)..1, Real.sin (θ + t * d) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) 0 1
  fun_prop

/-- `|∫₀¹ sin(θ + t d) dt| ≤ 1`. -/
@[tmio T, powerlib_foundation] private theorem abs_integral_sin_le (θ d : ℝ) :
    |∫ t in (0 : ℝ)..1, Real.sin (θ + t * d)| ≤ 1 := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := 1)
    (f := fun t => Real.sin (θ + t * d)) fun t _ => by
      rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _
  simpa using this

/-- **The step relation is solvable for every step `h > 0`**: `Φ` is continuous and
`|Φ(d) − (2 M/h + D) d| ≤ h (|P_ref − c₀| + A)`, so it takes every value (intermediate value
theorem). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem exists_dgRelation (g : Params) {h : ℝ} (hh : 0 < h)
    (x : Fin 2 → ℝ) (u : Fin 1 → ℝ) : ∃ y, g.DGRelation h x u y := by
  have hc : 0 < 2 * g.M / h + g.D := by have := g.M_pos; have := g.D_nonneg; positivity
  have hB : 0 ≤ h * (|g.Pref - g.c0| + g.A) := by have := g.A_pos; positivity
  have hbound : ∀ d, |g.dgPhi h (x 0 - g.α) d - (2 * g.M / h + g.D) * d| ≤
      h * (|g.Pref - g.c0| + g.A) := by
    intro d
    have hi := abs_integral_sin_le (x 0 - g.α) d
    have e : g.dgPhi h (x 0 - g.α) d - (2 * g.M / h + g.D) * d = h * (-(g.Pref - g.c0) +
        g.A * ∫ t in (0 : ℝ)..1, Real.sin (x 0 - g.α + t * d)) := by
      unfold Params.dgPhi; ring
    rw [e, abs_mul, abs_of_pos hh]
    refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) hh.le
    rw [abs_neg, abs_mul, abs_of_pos g.A_pos]
    nlinarith [g.A_pos]
  set T := (|2 * x 1 + h * u 0| + h * (|g.Pref - g.c0| + g.A)) / (2 * g.M / h + g.D) + 1
    with hTdef
  have hT : 0 < T := by positivity
  have hcT : (2 * g.M / h + g.D) * T =
      |2 * x 1 + h * u 0| + h * (|g.Pref - g.c0| + g.A) + (2 * g.M / h + g.D) := by
    rw [hTdef]
    linear_combination div_mul_cancel₀ (|2 * x 1 + h * u 0| + h * (|g.Pref - g.c0| + g.A))
      hc.ne'
  have hlo : g.dgPhi h (x 0 - g.α) (-T) ≤ 2 * x 1 + h * u 0 := by
    have := (abs_le.mp (hbound (-T))).2
    have := neg_abs_le (2 * x 1 + h * u 0)
    nlinarith
  have hhi : 2 * x 1 + h * u 0 ≤ g.dgPhi h (x 0 - g.α) T := by
    have := (abs_le.mp (hbound T)).1
    have := le_abs_self (2 * x 1 + h * u 0)
    nlinarith
  obtain ⟨d, -, hd⟩ := intermediate_value_Icc (by linarith : -T ≤ T)
    (continuous_dgPhi g h (x 0 - g.α)).continuousOn ⟨hlo, hhi⟩
  refine ⟨![x 0 + d, 2 * g.M * d / h - x 1], (dgRelation_iff g hh.ne' x u _).mpr ?_⟩
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, add_sub_cancel_left]
  exact ⟨trivial, hd⟩

/-- Strict growth of the averaged sine: for `d < d'`,
`∫₀¹ sin(θ + t d') dt − ∫₀¹ sin(θ + t d) dt > −(d' − d)/2`, since `|sin a − sin b| < |a − b|` for
`a ≠ b` and `∫₀¹ t dt = 1/2`. -/
@[tmio T, powerlib_foundation] private theorem integral_sin_sub_gt (θ : ℝ) {d d' : ℝ}
    (hlt : d < d') :
    -((d' - d) / 2) < (∫ t in (0 : ℝ)..1, Real.sin (θ + t * d')) -
      ∫ t in (0 : ℝ)..1, Real.sin (θ + t * d) := by
  have hi : ∀ e : ℝ, IntervalIntegrable (fun t : ℝ => Real.sin (θ + t * e))
      MeasureTheory.volume 0 1 := fun e =>
    (by fun_prop : Continuous fun t : ℝ => Real.sin (θ + t * e)).intervalIntegrable _ _
  have hpos : 0 < ∫ t in (0 : ℝ)..1,
      (Real.sin (θ + t * d') - Real.sin (θ + t * d) + t * (d' - d)) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      ((by fun_prop : Continuous fun t : ℝ =>
        Real.sin (θ + t * d') - Real.sin (θ + t * d) + t * (d' - d)).intervalIntegrable _ _)
      (fun t ht => ?_) one_pos
    have ht0 : 0 < t := ht.1
    have htd : 0 < t * (d' - d) := mul_pos ht0 (sub_pos.mpr hlt)
    have e2 : (θ + t * d' - (θ + t * d)) / 2 = t * (d' - d) / 2 := by ring
    have hne : t * (d' - d) / 2 ≠ 0 := by positivity
    have hs := Real.abs_sin_lt_abs hne
    rw [abs_of_pos (by positivity : 0 < t * (d' - d) / 2)] at hs
    have hsub := Real.sin_sub_sin (θ + t * d') (θ + t * d)
    rw [e2] at hsub
    have hc := Real.abs_cos_le_one ((θ + t * d' + (θ + t * d)) / 2)
    have hprod : |Real.sin (θ + t * d') - Real.sin (θ + t * d)| < t * (d' - d) := by
      rw [hsub, abs_mul, abs_mul, abs_two]
      calc 2 * |Real.sin (t * (d' - d) / 2)| * |Real.cos ((θ + t * d' + (θ + t * d)) / 2)|
          ≤ 2 * |Real.sin (t * (d' - d) / 2)| * 1 :=
            mul_le_mul_of_nonneg_left hc (by positivity)
        _ < t * (d' - d) := by linarith
    have := neg_abs_le (Real.sin (θ + t * d') - Real.sin (θ + t * d))
    linarith
  rw [intervalIntegral.integral_add ((hi d').sub (hi d))
      ((by fun_prop : Continuous fun t : ℝ => t * (d' - d)).intervalIntegrable _ _),
    intervalIntegral.integral_sub (hi d') (hi d), intervalIntegral.integral_mul_const,
    integral_id] at hpos
  linarith

/-- **Uniqueness of the implicit step for `A h² ≤ 4 M + 2 D h`**: then `Φ` is strictly
increasing, `Φ(d') − Φ(d) > (d' − d)(2 M/h + D − h A/2) ≥ 0` for `d < d'`
(`integral_sin_sub_gt`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem dgRelation_unique (g : Params) {h : ℝ} (hh : 0 < h)
    (hA : g.A * h ^ 2 ≤ 4 * g.M + 2 * g.D * h) {x : Fin 2 → ℝ} {u : Fin 1 → ℝ}
    {y y' : Fin 2 → ℝ} (hy : g.DGRelation h x u y) (hy' : g.DGRelation h x u y') : y = y' := by
  rw [dgRelation_iff g hh.ne'] at hy hy'
  have hc : g.A * h / 2 ≤ 2 * g.M / h + g.D := by
    have e : 2 * g.M / h + g.D - g.A * h / 2 = (4 * g.M + 2 * g.D * h - g.A * h ^ 2) / (2 * h) := by
      field_simp; ring
    have : 0 ≤ (4 * g.M + 2 * g.D * h - g.A * h ^ 2) / (2 * h) :=
      div_nonneg (by linarith) (by positivity)
    linarith
  have hmono : ∀ d d' : ℝ, d < d' → g.dgPhi h (x 0 - g.α) d < g.dgPhi h (x 0 - g.α) d' := by
    intro d d' hlt
    have hi := integral_sin_sub_gt (x 0 - g.α) hlt
    have hAh : 0 < h * g.A := mul_pos hh g.A_pos
    have h1 : 0 < d' - d := sub_pos.mpr hlt
    have key := mul_lt_mul_of_pos_left hi hAh
    have key2 : g.A * h / 2 * (d' - d) ≤ (2 * g.M / h + g.D) * (d' - d) :=
      mul_le_mul_of_nonneg_right hc h1.le
    unfold Params.dgPhi
    nlinarith
  have hd : y 0 - x 0 = y' 0 - x 0 := by
    rcases lt_trichotomy (y 0 - x 0) (y' 0 - x 0) with hl | he | hl
    · exact absurd (hy.2.trans hy'.2.symm) (hmono _ _ hl).ne
    · exact he
    · exact absurd (hy'.2.trans hy.2.symm) (hmono _ _ hl).ne
  have h0 : y 0 = y' 0 := by linarith
  funext i
  fin_cases i
  · exact h0
  · show y 1 = y' 1
    rw [hy.1, hy'.1, hd]

/-- **Non-uniqueness of the implicit step for `A h² > 4 M + 2 D h`**: at the angle `δ = α + π`
(the electrical potential at its maximum) with `p = −h (P_ref − c₀)/2` and `u = 0` the relation
has the solution `d = 0` and a solution with `d > 0`: `h A (1 − cos d) = (2 M/h + D) d²` changes
sign on `(0, ∞)` (`Real.cos_bound` near `0`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem exists_dgRelation_ne (g : Params) {h : ℝ} (hh : 0 < h)
    (hA : 4 * g.M + 2 * g.D * h < g.A * h ^ 2) :
    ∃ x u y y', g.DGRelation h x u y ∧ g.DGRelation h x u y' ∧ y ≠ y' := by
  have hAp := g.A_pos
  set c := 2 * g.M / h + g.D with hcdef
  have hc : 0 < c := by have := g.M_pos; have := g.D_nonneg; positivity
  have hgap : c < g.A * h / 2 := by
    have e : g.A * h / 2 - c = (g.A * h ^ 2 - 4 * g.M - 2 * g.D * h) / (2 * h) := by
      rw [hcdef]; field_simp; ring
    have : 0 < (g.A * h ^ 2 - 4 * g.M - 2 * g.D * h) / (2 * h) :=
      div_pos (by linarith) (by positivity)
    linarith
  -- a small positive value and a large negative value of `ψ(d) = h A (1 − cos d) − c d²`
  set ε := g.A * h / 2 - c with hεdef
  have hε : 0 < ε := by linarith
  set d1 := min 1 (ε / (g.A * h)) with hd1def
  have hd1 : 0 < d1 := lt_min one_pos (by positivity)
  have hd1le : d1 ≤ 1 := min_le_left _ _
  have hpos : 0 < h * g.A * (1 - Real.cos d1) - c * d1 ^ 2 := by
    have hb := Real.cos_bound (x := d1) (by rw [abs_of_pos hd1]; exact hd1le)
    rw [abs_of_pos hd1] at hb
    have hcb := (abs_le.mp hb).2
    have hsq : d1 ^ 2 ≤ ε / (g.A * h) := by
      calc d1 ^ 2 ≤ d1 * 1 := by nlinarith
        _ ≤ ε / (g.A * h) := by rw [mul_one]; exact min_le_right _ _
    have hAh : g.A * h * (ε / (g.A * h)) = ε := by field_simp
    have h4 : g.A * h * d1 ^ 4 ≤ ε * d1 ^ 2 := by
      have := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ g.A * h * d1 ^ 2)
      nlinarith
    have hd2 : 0 < d1 ^ 2 := by positivity
    have hexp : h * g.A * (1 - Real.cos d1) - c * d1 ^ 2 ≥
        ε * d1 ^ 2 - h * g.A * (d1 ^ 4 * (5 / 96)) := by
      have : h * g.A * (1 - Real.cos d1) ≥ h * g.A * (d1 ^ 2 / 2 - d1 ^ 4 * (5 / 96)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      rw [hεdef]
      nlinarith
    nlinarith
  set d2 := Real.sqrt (2 * h * g.A / c) + 1 with hd2def
  have hd12 : d1 < d2 := by
    have : 0 < Real.sqrt (2 * h * g.A / c) := Real.sqrt_pos.mpr (by positivity)
    rw [hd2def]
    linarith
  have hneg : h * g.A * (1 - Real.cos d2) - c * d2 ^ 2 < 0 := by
    have hs : Real.sqrt (2 * h * g.A / c) ^ 2 = 2 * h * g.A / c :=
      Real.sq_sqrt (by positivity)
    have hsq : 2 * h * g.A / c < d2 ^ 2 := by
      have := Real.sqrt_nonneg (2 * h * g.A / c)
      rw [hd2def]
      nlinarith
    have hcos := Real.neg_one_le_cos d2
    have : 2 * h * g.A < c * d2 ^ 2 := by rwa [div_lt_iff₀' hc] at hsq
    nlinarith [mul_pos hh hAp]
  obtain ⟨d, hdI, hd0⟩ := intermediate_value_Icc' hd12.le
    (by fun_prop : Continuous fun d : ℝ => h * g.A * (1 - Real.cos d) - c * d ^ 2).continuousOn
    ⟨hneg.le, hpos.le⟩
  have hdpos : 0 < d := lt_of_lt_of_le hd1 hdI.1
  -- the two solutions
  set x : Fin 2 → ℝ := ![g.α + Real.pi, -(h * (g.Pref - g.c0)) / 2] with hxdef
  have hθ : x 0 - g.α = Real.pi := by simp [hxdef]
  have hx1 : x 1 = -(h * (g.Pref - g.c0)) / 2 := by simp [hxdef]
  have hphi0 : g.dgPhi h Real.pi 0 = 2 * x 1 + h * (0 : Fin 1 → ℝ) 0 := by
    simp [Params.dgPhi, hx1]
    ring
  have hphid : g.dgPhi h Real.pi d = 2 * x 1 + h * (0 : Fin 1 → ℝ) 0 := by
    have hint : ∫ t in (0 : ℝ)..1, Real.sin (Real.pi + t * d) = (Real.cos d - 1) / d := by
      have e : (fun t => Real.sin (Real.pi + t * d)) = fun t => -Real.sin (d * t + 0) := by
        funext t
        rw [add_zero, add_comm, Real.sin_add_pi, mul_comm]
      rw [e, intervalIntegral.integral_neg,
        intervalIntegral.integral_comp_mul_add (fun t => Real.sin t) hdpos.ne', integral_sin,
        smul_eq_mul]
      simp only [mul_zero, zero_add, mul_one, Real.cos_zero]
      field_simp
      ring_nf
    have hψ : h * g.A * (1 - Real.cos d) = c * d ^ 2 := by
      have := hd0; simp only at this; linarith
    have key : h * g.A * ((Real.cos d - 1) / d) = -(c * d) := by
      rw [show h * g.A * ((Real.cos d - 1) / d) = -(h * g.A * (1 - Real.cos d)) / d by ring, hψ,
        pow_two, ← mul_assoc, neg_div, mul_div_assoc, div_self hdpos.ne', mul_one]
    unfold Params.dgPhi
    rw [hint, hx1, ← hcdef]
    simp only [Pi.zero_apply, mul_zero, add_zero]
    linear_combination key
  refine ⟨x, 0, ![x 0, 2 * g.M * 0 / h - x 1], ![x 0 + d, 2 * g.M * d / h - x 1], ?_, ?_, ?_⟩
  · rw [dgRelation_iff g hh.ne']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_self]
    exact ⟨trivial, by rw [hθ]; exact hphi0⟩
  · rw [dgRelation_iff g hh.ne']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, add_sub_cancel_left]
    exact ⟨trivial, by rw [hθ]; exact hphid⟩
  · intro he
    have := congrFun he 0
    simp at this
    linarith

/-- **The implicit step is unique for every state and input exactly when `A h² ≤ 4 M + 2 D h`**
(`dgRelation_unique`, `exists_dgRelation_ne`); it exists for every step `h > 0`
(`exists_dgRelation`). Static evidence on the model. -/
@[tmio M, powerlib_domain] theorem dgRelation_unique_iff (g : Params) {h : ℝ} (hh : 0 < h) :
    (∀ x u y y', g.DGRelation h x u y → g.DGRelation h x u y' → y = y') ↔
      g.A * h ^ 2 ≤ 4 * g.M + 2 * g.D * h := by
  refine ⟨fun H => not_lt.mp fun hlt => ?_, fun hA x u y y' => dgRelation_unique g hh hA⟩
  obtain ⟨x, u, y, y', hy, hy', hne⟩ := exists_dgRelation_ne g hh hlt
  exact hne (H x u y y' hy hy')

/-- **The discrete-gradient discretizations of the GFM swing, with a step that determines the
relation, are passive exactly when the set-point is matched**: for `0 < h` with
`A h² ≤ 4 M + 2 D h`, a discrete system whose step solves the relation (it exists,
`exists_dgRelation`) and whose output is the discrete-gradient output is passive iff
`P_ref = c₀` (`dg_passive`; `dg_not_passive` with the uniqueness `dgRelation_unique`). -/
@[tmio TM, powerlib_domain] theorem dg_passive_iff (g : Params) (s : Map.System 2 1)
    (hT : 0 < s.period) (hA : g.A * s.period ^ 2 ≤ 4 * g.M + 2 * g.D * s.period)
    (hstep : ∀ x u, WithLp.ofLp (s.step x u) - WithLp.ofLp x = s.period •
      ((swingJ - g.swingR) *ᵥ g.dg.dg (WithLp.ofLp x) (WithLp.ofLp (s.step x u)) +
        swingG *ᵥ u))
    (hout : ∀ x u, s.output x u = swingGᵀ *ᵥ g.dg.dg (WithLp.ofLp x) (WithLp.ofLp (s.step x u))) :
    s.Passive ↔ g.Pref = g.c0 := by
  refine ⟨fun hp => by_contra fun hne => dg_not_passive g hne s hT (fun x u y hy => ?_) hout hp,
    fun hg => dg_passive g hg s hT.le hstep hout⟩
  have h1 : g.DGRelation s.period (WithLp.ofLp x) u (WithLp.ofLp y) := hy
  have h2 : g.DGRelation s.period (WithLp.ofLp x) u (WithLp.ofLp (s.step x u)) := hstep x u
  have := dgRelation_unique g hT hA h2 h1
  exact (WithLp.ofLp_injective 2) this

/-- **A discrete-gradient discretization exists for every step**: a discrete system with period
`h > 0` whose step solves the relation (`exists_dgRelation`, a choice of solution) and whose
output is the discrete-gradient output. -/
@[tmio M, powerlib_domain] theorem exists_dg_system (g : Params) {h : ℝ} (hh : 0 < h) :
    ∃ s : Map.System 2 1, s.period = h ∧
      (∀ x u, WithLp.ofLp (s.step x u) - WithLp.ofLp x = s.period •
        ((swingJ - g.swingR) *ᵥ g.dg.dg (WithLp.ofLp x) (WithLp.ofLp (s.step x u)) +
          swingG *ᵥ u)) ∧
      ∀ x u, s.output x u = swingGᵀ *ᵥ g.dg.dg (WithLp.ofLp x) (WithLp.ofLp (s.step x u)) := by
  choose y hy using fun (x : State 2) (u : Fin 1 → ℝ) => exists_dgRelation g hh (WithLp.ofLp x) u
  exact ⟨⟨fun x u => WithLp.toLp 2 (y x u),
    fun x u => swingGᵀ *ᵥ g.dg.dg (WithLp.ofLp x) (y x u), h⟩, rfl, fun x u => hy x u,
    fun x u => rfl⟩

end powerlib.GFM.SwingPort
