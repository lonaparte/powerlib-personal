import theorem.GridTiedConverter.GFM.Discrete.SwingPort

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
  is required to determine the step (a unique solution, which holds for small steps). The
  existence of the implicit step is not proved here; exact arithmetic, fixed step.
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

end powerlib.GFM.SwingPort
