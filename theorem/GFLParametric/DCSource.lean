import theorem.GFLParametric.FourState

/-! # dc-source stiffness convention (switch W9)

Foundation layer.  The dc bus `C V̇ = (source) + P_abs(V)/V` is linearized at `V = 1` for two
ideal dc sources:
* constant current: `C V̇ = I₀ + P_abs(V)/V`;
* constant power: `C V̇ = (P₀ + P_abs(V))/V`.
Here `P_abs` is the absorbed ac power (IN-positive), so the exported power at the operating
point is `P = −P_abs(1)` (`= I₀ = P₀` at the equilibrium).  The dc-voltage loop enters through
`P_abs(V) = (3/2) v_{d0} (i_{d0} − k_pv (V − 1) − k_iv η)`.

* `hasDerivAt_constCurrent`, `hasDerivAt_constPower`: the diagonal entries are
  `(P_abs'(1) − P_abs(1))/C` and `P_abs'(1)/C`; their difference is exactly `P/C`
  (`a33_sub`).
* `a33_constCurrent`, `a33_constPower`: for the voltage-loop power,
  `A₃₃ = (−1.5 v_{d0} k_pv + P)/C` (constant current) and `A₃₃ = −1.5 v_{d0} k_pv / C`
  (constant power); the constant-power source cancels the `+P/C` term exactly.
* `a33_constCurrent_eq_A0`: the constant-current value is the `(V, V)` entry of the
  four-state `A₀`.

The source writes the same formulas in its OUT-positive convention; both `A₃₃` values are
convention invariant (`P` is the exported power in both).

Family and connection conclusions. No family and no connection conclusion: derivative identities
of scalar dc-bus right-hand sides only.

Source: work-sync `projects/vsc-parametric-oscillation/references/gfl-gfm-contrast/archive/
notes/concepts/convention-gates.md` 开关一 (W9).
-/

noncomputable section
namespace powerlib.GFLParametric.DCSource

/-- Constant-current source: `V̇ = (I₀ + P(V)/V)/C`, derivative at `V = 1`. -/
@[powerlib_foundation] theorem hasDerivAt_constCurrent {P : ℝ → ℝ} {P' : ℝ} (I0 C : ℝ)
    (hP : HasDerivAt P P' 1) :
    HasDerivAt (fun V => (I0 + P V / V) / C) ((P' - P 1) / C) 1 := by
  have h := ((hP.div (hasDerivAt_id (1 : ℝ)) one_ne_zero).const_add I0).div_const C
  convert h using 1 <;> simp

/-- Constant-power source: `V̇ = (P₀ + P(V))/(C V)`, derivative at an equilibrium `V = 1`. -/
@[powerlib_foundation] theorem hasDerivAt_constPower {P : ℝ → ℝ} {P' : ℝ} (P0 C : ℝ)
    (hC : C ≠ 0) (hP : HasDerivAt P P' 1) (heq : P0 + P 1 = 0) :
    HasDerivAt (fun V => (P0 + P V) / (C * V)) (P' / C) 1 := by
  have h := (hP.const_add P0).div ((hasDerivAt_id (1 : ℝ)).const_mul C) (by simpa using hC)
  convert h using 1
  · ext V; simp
  · simp only [id, heq]
    field_simp
    ring

/-- The two diagonal entries differ by exactly the exported power over `C`. -/
@[powerlib_foundation] theorem a33_sub (P1 P' C : ℝ) :
    (P' - P1) / C - P' / C = -P1 / C := by ring

/-- Absorbed power of the dc-voltage loop as a function of `V` (fixed `η`). -/
def loopPower (vd0 id0 kpv kiv η : ℝ) (V : ℝ) : ℝ :=
  3 / 2 * vd0 * (id0 - kpv * (V - 1) - kiv * η)

@[powerlib_foundation] theorem hasDerivAt_loopPower (vd0 id0 kpv kiv η : ℝ) :
    HasDerivAt (loopPower vd0 id0 kpv kiv η) (-(3 / 2) * vd0 * kpv) 1 := by
  have := (((hasDerivAt_id (1 : ℝ)).sub_const 1).const_mul kpv).const_sub id0
    |>.sub_const (kiv * η) |>.const_mul (3 / 2 * vd0)
  convert this using 1
  · ext V; simp [loopPower]
  · simp

/-- W9, constant-current source: `A₃₃ = (−1.5 v_{d0} k_pv + P)/C`, `P = −P_abs(1)`. -/
@[powerlib_foundation] theorem a33_constCurrent (vd0 id0 kpv kiv η I0 C : ℝ) :
    HasDerivAt (fun V => (I0 + loopPower vd0 id0 kpv kiv η V / V) / C)
      ((-1.5 * vd0 * kpv + -loopPower vd0 id0 kpv kiv η 1) / C) 1 := by
  have := hasDerivAt_constCurrent I0 C (hasDerivAt_loopPower vd0 id0 kpv kiv η)
  convert this using 1
  ring

/-- W9, constant-power source: `A₃₃ = −1.5 v_{d0} k_pv / C` (at the equilibrium
`P₀ = P = −P_abs(1)`). -/
@[powerlib_foundation] theorem a33_constPower (vd0 id0 kpv kiv η C : ℝ) (hC : C ≠ 0) :
    HasDerivAt (fun V => (-loopPower vd0 id0 kpv kiv η 1 + loopPower vd0 id0 kpv kiv η V) /
        (C * V)) (-1.5 * vd0 * kpv / C) 1 := by
  have := hasDerivAt_constPower (-loopPower vd0 id0 kpv kiv η 1) C hC
    (hasDerivAt_loopPower vd0 id0 kpv kiv η) (by ring)
  convert this using 1
  ring

/-- The constant-current `A₃₃` is the `(V, V)` entry of the four-state `A₀`
(`η = 0`, `P = −(3/2) v_{d0} i_{d0}`). -/
@[powerlib_foundation] theorem a33_constCurrent_eq_A0 (p : FourState.Params) (θ0 : ℝ) :
    (-1.5 * FourState.vd0 p θ0 * p.kpv +
        -loopPower (FourState.vd0 p θ0) p.id0 p.kpv p.kiv 0 1) / p.C =
      FourState.A0 p θ0 2 2 := by
  simp [FourState.A0, loopPower, FourState.Params.γ]
  ring

end powerlib.GFLParametric.DCSource
