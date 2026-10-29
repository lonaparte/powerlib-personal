import theorem.Frequency.Basic
import theorem.Linear.Rate
import theorem.TMIO.ClaimElab
import theorem.Spectral.LinearNamed

/-! # Two-area load-frequency control (LFC) with AGC

The two-area LFC/AGC small-signal model (five states with instantaneous governors, seven states
with governors kept) as linear families: tie-line linearization, non-interactive steady state, and
global exponential convergence to it under a Hurwitz state matrix.

Model boundary.
* Continuous-time, linear, small-signal model around an operating point; Kundur per-unit
  (`Δω̂` per-unit, `M = 2H` [s], powers system-base per-unit, tie-line angles in rad).
  Each control area is one coherent machine (COI aggregation of `Frequency.Aggregation`).
* Area parameters (`Area`): `M_eff > 0`, `D_eff`, aggregated droop `K_R`, AGC integral gain
  `K_I` [1/s], frequency bias `B`, governor time constant `T_g`. Tie line `a → b`:
  synchronizing coefficient `T = V_a V_b cos δ⁰_ab / X_ab` [pu/rad], `ω_s` [rad/s].
* Sign conventions: `ΔP_tie,ab` is the flow from `a` to `b` (export of `a` positive);
  area swing `M Δω̇ = ΔP_m − ΔP_L − D Δω − ΔP_tie,area` with `ΔP_tie,a = +ΔP_tie,ab`,
  `ΔP_tie,b = −ΔP_tie,ab`; `ACE = ΔP_tie,area + B Δω`; AGC `ΔṖ_C = −K_I ACE`.
* `plant` (§1.7, governors instantaneous, `T_g → 0`, a `Linear.Plant 5 2`): state
  `x = (Δω_a, Δω_b, ΔP_tie,ab, ΔP_C,a, ΔP_C,b)` in `EuclideanSpace ℝ (Fin 5)`, input
  `u = (ΔP_L,a, ΔP_L,b)`, output `(Δω_a, Δω_b)`; `ΔP_m = ΔP_C − K_R Δω`.
* `plant7` (§1.3 governors kept, a `Linear.Plant 7 2`): state
  `x = (Δω_a, Δω_b, ΔP_tie,ab, ΔP_C,a, ΔP_C,b, ΔP_m,a, ΔP_m,b)`,
  `T_g ΔṖ_m = −ΔP_m − K_R Δω + ΔP_C`.
* Excluded: dead-bands, rate limits, generation limits / saturation, HVDC ties, voltage
  dynamics, delays, nonlinear tie-line power beyond the linearization, AGC filters.

Source: work-sync `theory/T-load-frequency-control.md` §1.1 (area swing), §1.2 (tie-line
linearization), §1.3 (governor), §1.4 (ACE, `B^Hz = B/f₀`, sign of `ACE_b`), §1.5 (AGC
integral), §1.6 (steady state / non-interactive control), §1.7 (two-area state matrix).

Results.
* `tiePower_hasDerivAt`, `tieFlow_hasDerivAt` (foundation, §1.2): `T = V_a V_b cos δ⁰/X` is the
  slope of `V_a V_b sin δ / X`, and the linearised flow obeys `ΔṖ_tie = ω_s T (Δω_a − Δω_b)`.
* `ace_hz` (foundation, §1.4): `B Δω̂ = (B/f₀) Δf` with `Δf = f₀ Δω̂`.
* `field_*` (foundation): every row of the §1.7 matrix is the corresponding §1.1–§1.5
  equation (including the opposite sign of `ΔP_tie,ab` in the two AGC rows).
* `isEquilibrium_iff`, `plant7_isEquilibrium_iff` (foundation, static, §1.6): for
  `B_a + B_b ≠ 0`, `K_I ≠ 0`, `ω_s T ≠ 0` (and `M, T_g ≠ 0`) the unique equilibrium for
  constant loads is `Δω = 0`, `ΔP_tie = 0`, `ΔP_C,a = ΔP_L,a`, `ΔP_C,b = ΔP_L,b`
  (non-interactive control). The steady state is an equilibrium for every parameter value
  (`steadyState_isEquilibrium`, `plant7_steadyState_isEquilibrium`).
* If the state matrix is Hurwitz, every trajectory converges exponentially to that equilibrium.
  In this module Hurwitz is an explicit (static) premise; a parametric sufficient condition —
  `K_I M ≤ D + K_R` in both areas with `M, K_I, B, ω_s T > 0` — is proved in
  `Frequency.LFCNetwork` (`plant_isHurwitz_of_gain`, connection `mem_den_of_gain`), by reading
  the five-state matrix as the two-area case of the radial `N`-area matrix.

Family and connection conclusions.
* System maps: a two-area model (`Model`: areas `a`, `b`, `ω_s`, `T`) is read as the port
  system of its five-state plant, and `Model7` as that of its seven-state plant
  (`Family.IsLinear`): port input the area loads, port output the area frequencies. The steady
  state `(0, 0, 0, ΔP_L)` is an equilibrium of every constant load `u`, and the plant field in
  deviation coordinates about it is the zero-input field; so the flow sentences about the origin
  are exactly the sentences about the non-interactive steady state of every constant load
  (`Linear.holds_input_iff`, `Flow.Property.holds_shift_iff`).
* Requirements (static): `hurwitz` (the state matrix is Hurwitz), `rhpRoot` (a characteristic
  root in the open right half plane), `rate a` (`Linear.RateMargin`). Lyapunov stability and the
  attractive sentences translate into `hurwitz`, instability into `rhpRoot`, decay into its
  margin; conservation and passivity into the whole (inconsistent) language.
* Connection theorems: `chain_le_semantics`, `exact_hurwitz`,
  `mem_den_globallyExponentiallyStable` (Hurwitz premise) and the same three for the
  seven-state family (`chain_le_semantics7`, `exact_hurwitz7`,
  `mem_den_globallyExponentiallyStable7`).
* The matrix requirement language (`MeetsMatrix`) and its soundness and exactness for any linear
  family read through it (`sound_of_meetsMatrix`, `exact_of_meetsMatrix`, instances of the linear
  table `Spectral.chain_le_semantics_of_linearTable_univ`, `Spectral.exact_of_linearTable` of
  `theorem/Spectral/LinearNamed.lean`) are generic foundation, reused by the multi-area family of
  `Frequency.LFCNetwork`.
* Static evidence: `isEquilibrium_iff`, `steadyState_isEquilibrium`, `plant7_isEquilibrium_iff`,
  `plant7_steadyState_isEquilibrium`. Private implementation evidence (trajectory level, Rules
  §3a): `tendsto_of_isHurwitz`, `exponentiallyConvergesTo_of_isHurwitz`,
  `plant7_exponentiallyConvergesTo_of_isHurwitz`.

Correction.
* The note's §1.6 "设稳态存在" assumes convergence; the steady-state analysis alone does not
  establish it (convergence needs the Hurwitz premise above).
-/

noncomputable section
namespace powerlib.Frequency.LFC
open Set Filter Matrix LinearSystems TMIO
open scoped Topology

/-- Aggregated parameters of one control area. -/
structure Area where
  /-- Inertia `M_eff = 2 H_eff` [s]. -/
  M : ℝ
  /-- Damping `D_eff`. -/
  D : ℝ
  /-- Aggregated droop gain `K_R`. -/
  K : ℝ
  /-- AGC integral gain `K_I` [1/s]. -/
  KI : ℝ
  /-- Frequency bias `B`. -/
  B : ℝ
  /-- Governor time constant `T_g` [s] (only used by `plant7`). -/
  Tg : ℝ

/-! ## Tie-line linearization and ACE (§1.2, §1.4) -/

/-- Tie-line synchronizing coefficient `T = V_a V_b cos δ⁰ / X`. -/
def syncCoeff (Va Vb X δ0 : ℝ) : ℝ := Va * Vb * Real.cos δ0 / X

/-- §1.2: `T` is the slope of `P_tie(δ) = V_a V_b sin δ / X` at `δ⁰`. -/
@[tmio M, powerlib_foundation] theorem tiePower_hasDerivAt (Va Vb X δ0 : ℝ) :
    HasDerivAt (fun δ => Va * Vb / X * Real.sin δ) (syncCoeff Va Vb X δ0) δ0 := by
  have h := (Real.hasDerivAt_sin δ0).const_mul (Va * Vb / X)
  convert h using 1
  unfold syncCoeff
  ring

/-- §1.2 boxed: with `δ̇_a = ω_s Δω̂_a`, `δ̇_b = ω_s Δω̂_b`, the linearised tie flow
`ΔP_tie = T (δ_a − δ_b − δ⁰)` has rate `ω_s T (Δω̂_a − Δω̂_b)`. -/
@[powerlib_foundation] theorem tieFlow_hasDerivAt {δa δb : ℝ → ℝ} {wa wb ωs T δ0 t : ℝ}
    (ha : HasDerivAt δa (ωs * wa) t) (hb : HasDerivAt δb (ωs * wb) t) :
    HasDerivAt (fun t => T * (δa t - δb t - δ0)) (ωs * T * (wa - wb)) t := by
  have h := ((ha.sub hb).sub_const δ0).const_mul T
  convert h using 1
  ring

/-- §1.4: `ACE = ΔP_tie + B Δω̂ = ΔP_tie + B^Hz Δf` with `Δf = f₀ Δω̂`, `B^Hz = B/f₀`. -/
@[powerlib_foundation] theorem ace_hz {f₀ : ℝ} (hf : f₀ ≠ 0) (Ptie B w : ℝ) :
    Ptie + B * w = Ptie + B / f₀ * (f₀ * w) := by
  field_simp

/-! ## Two-area model, governors instantaneous (§1.7) -/

/-- §1.7 five-state two-area LFC plant. -/
def plant (a b : Area) (ωs T : ℝ) : Linear.Plant 5 2 where
  A := !![-(a.D + a.K) / a.M, 0, -1 / a.M, 1 / a.M, 0;
          0, -(b.D + b.K) / b.M, 1 / b.M, 0, 1 / b.M;
          ωs * T, -(ωs * T), 0, 0, 0;
          -(a.KI * a.B), 0, -a.KI, 0, 0;
          0, -(b.KI * b.B), b.KI, 0, 0]
  B := !![-1 / a.M, 0; 0, -1 / b.M; 0, 0; 0, 0; 0, 0]
  C := !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0]
  D := 0

/-- The equilibrium `(0, 0, 0, ΔP_L,a, ΔP_L,b)`. -/
def steadyState (u : Fin 2 → ℝ) : EuclideanSpace ℝ (Fin 5) := WithLp.toLp 2 ![0, 0, 0, u 0, u 1]

variable {a b : Area} {ωs T : ℝ}

@[powerlib_foundation] theorem field_apply (x : EuclideanSpace ℝ (Fin 5)) (u : Fin 2 → ℝ) :
    (plant a b ωs T).inputField u x =
      WithLp.toLp 2 ![-(a.D + a.K) / a.M * x 0 + -1 / a.M * x 2 + 1 / a.M * x 3 + -1 / a.M * u 0,
        -(b.D + b.K) / b.M * x 1 + 1 / b.M * x 2 + 1 / b.M * x 4 + -1 / b.M * u 1,
        ωs * T * x 0 + -(ωs * T) * x 1,
        -(a.KI * a.B) * x 0 + -a.KI * x 2,
        -(b.KI * b.B) * x 1 + b.KI * x 2] := by
  rw [LTI.inputField_apply]
  congr 1
  ext i; fin_cases i <;>
    simp [plant, dotProduct, Fin.sum_univ_five, Fin.sum_univ_two]

/-- Area `a` swing (§1.1 with §1.3, `T_g → 0`): `M_a Δω̇_a = ΔP_m,a − ΔP_L,a − D_a Δω_a − ΔP_tie,ab`
with `ΔP_m,a = ΔP_C,a − K_R,a Δω_a`. -/
@[powerlib_foundation] theorem field_swing_a (ha : a.M ≠ 0) (x : EuclideanSpace ℝ (Fin 5))
    (u : Fin 2 → ℝ) :
    a.M * (plant a b ωs T).inputField u x 0 = (x 3 - a.K * x 0) - u 0 - a.D * x 0 - x 2 := by
  rw [field_apply]
  simp only [Fin.isValue, Matrix.cons_val_zero]
  field_simp
  ring

/-- Area `b` swing: its net export is `−ΔP_tie,ab`. -/
@[powerlib_foundation] theorem field_swing_b (hb : b.M ≠ 0) (x : EuclideanSpace ℝ (Fin 5))
    (u : Fin 2 → ℝ) :
    b.M * (plant a b ωs T).inputField u x 1 = (x 4 - b.K * x 1) - u 1 - b.D * x 1 - (-x 2) := by
  rw [field_apply]
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
  field_simp
  ring

/-- Tie-line row: `ΔṖ_tie,ab = ω_s T (Δω_a − Δω_b)`. -/
@[powerlib_foundation] theorem field_tie (x : EuclideanSpace ℝ (Fin 5)) (u : Fin 2 → ℝ) :
    (plant a b ωs T).inputField u x 2 = ωs * T * (x 0 - x 1) := by
  rw [field_apply]
  simp only [Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  ring

/-- AGC of area `a`: `ΔṖ_C,a = −K_I,a ACE_a`, `ACE_a = ΔP_tie,ab + B_a Δω_a`. -/
@[powerlib_foundation] theorem field_agc_a (x : EuclideanSpace ℝ (Fin 5)) (u : Fin 2 → ℝ) :
    (plant a b ωs T).inputField u x 3 = -a.KI * (x 2 + a.B * x 0) := by
  rw [field_apply]
  simp [Matrix.cons_val]
  ring

/-- AGC of area `b`: `ΔṖ_C,b = −K_I,b ACE_b`, `ACE_b = −ΔP_tie,ab + B_b Δω_b` (§1.4 sign flip). -/
@[powerlib_foundation] theorem field_agc_b (x : EuclideanSpace ℝ (Fin 5)) (u : Fin 2 → ℝ) :
    (plant a b ωs T).inputField u x 4 = -b.KI * (-x 2 + b.B * x 1) := by
  rw [field_apply]
  simp [Matrix.cons_val]
  ring

/-- The steady state is an equilibrium of every constant load, for every parameter value. Static
evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem steadyState_isEquilibrium (u : Fin 2 → ℝ) :
    IsEquilibrium ((plant a b ωs T).inputField u) (steadyState u) := by
  unfold IsEquilibrium
  rw [field_apply]
  ext i; fin_cases i <;> simp [steadyState] <;> ring

/-- §1.6 (non-interactive control): for `B_a + B_b ≠ 0`, `K_I,a, K_I,b ≠ 0`, `ω_s T ≠ 0`, the
unique equilibrium for constant loads `u = (ΔP_L,a, ΔP_L,b)` is `(0, 0, 0, ΔP_L,a, ΔP_L,b)`.
Static evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem isEquilibrium_iff (ha : a.M ≠ 0) (hb : b.M ≠ 0)
    (hKa : a.KI ≠ 0) (hKb : b.KI ≠ 0) (hT : ωs * T ≠ 0) (hB : a.B + b.B ≠ 0)
    (u : Fin 2 → ℝ) (e : EuclideanSpace ℝ (Fin 5)) :
    IsEquilibrium ((plant a b ωs T).inputField u) e ↔ e = steadyState u := by
  constructor
  · intro h
    unfold IsEquilibrium at h
    have h0 := field_swing_a (b := b) (ωs := ωs) (T := T) ha e u
    have h1 := field_swing_b (a := a) (ωs := ωs) (T := T) hb e u
    have h2 := field_tie (a := a) (b := b) (ωs := ωs) (T := T) e u
    have h3 := field_agc_a (a := a) (b := b) (ωs := ωs) (T := T) e u
    have h4 := field_agc_b (a := a) (b := b) (ωs := ωs) (T := T) e u
    rw [h] at h0 h1 h2 h3 h4
    simp only [PiLp.zero_apply, mul_zero] at h0 h1 h2 h3 h4
    have e01 : e 0 = e 1 := by
      have := (mul_eq_zero.1 h2.symm).resolve_left hT
      linarith
    have e2a : e 2 + a.B * e 0 = 0 := by
      have := (mul_eq_zero.1 h3.symm).resolve_left (neg_ne_zero.2 hKa)
      linarith
    have e2b : -e 2 + b.B * e 1 = 0 := by
      have := (mul_eq_zero.1 h4.symm).resolve_left (neg_ne_zero.2 hKb)
      linarith
    have e0 : e 0 = 0 := by
      have : (a.B + b.B) * e 0 = 0 := by rw [← e01] at e2b; linarith
      exact (mul_eq_zero.1 this).resolve_left hB
    have e1 : e 1 = 0 := by rw [← e01, e0]
    have e2 : e 2 = 0 := by rw [e0] at e2a; linarith
    ext i; fin_cases i
    · simpa [steadyState] using e0
    · simpa [steadyState] using e1
    · simpa [steadyState] using e2
    · simp only [steadyState, Fin.reduceFinMk, Fin.isValue, PiLp.toLp_apply, Matrix.cons_val]
      rw [e0, e2] at h0; simp at h0; linarith
    · simp only [steadyState, Fin.reduceFinMk, Fin.isValue, PiLp.toLp_apply, Matrix.cons_val]
      rw [e1, e2] at h1; simp at h1; linarith
  · rintro rfl
    exact steadyState_isEquilibrium u

/-! ## Two-area model with governor dynamics -/

/-- Seven-state two-area plant with first-order governors. -/
def plant7 (a b : Area) (ωs T : ℝ) : Linear.Plant 7 2 where
  A := !![-a.D / a.M, 0, -1 / a.M, 0, 0, 1 / a.M, 0;
          0, -b.D / b.M, 1 / b.M, 0, 0, 0, 1 / b.M;
          ωs * T, -(ωs * T), 0, 0, 0, 0, 0;
          -(a.KI * a.B), 0, -a.KI, 0, 0, 0, 0;
          0, -(b.KI * b.B), b.KI, 0, 0, 0, 0;
          -a.K / a.Tg, 0, 0, 1 / a.Tg, 0, -1 / a.Tg, 0;
          0, -b.K / b.Tg, 0, 0, 1 / b.Tg, 0, -1 / b.Tg]
  B := !![-1 / a.M, 0; 0, -1 / b.M; 0, 0; 0, 0; 0, 0; 0, 0; 0, 0]
  C := !![1, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0]
  D := 0

/-- The equilibrium `(0, 0, 0, ΔP_L,a, ΔP_L,b, ΔP_L,a, ΔP_L,b)`. -/
def steadyState7 (u : Fin 2 → ℝ) : EuclideanSpace ℝ (Fin 7) :=
  WithLp.toLp 2 ![0, 0, 0, u 0, u 1, u 0, u 1]

@[powerlib_foundation] theorem plant7_field_apply (x : EuclideanSpace ℝ (Fin 7)) (u : Fin 2 → ℝ) :
    (plant7 a b ωs T).inputField u x =
      WithLp.toLp 2 ![-a.D / a.M * x 0 + -1 / a.M * x 2 + 1 / a.M * x 5 + -1 / a.M * u 0,
        -b.D / b.M * x 1 + 1 / b.M * x 2 + 1 / b.M * x 6 + -1 / b.M * u 1,
        ωs * T * x 0 + -(ωs * T) * x 1,
        -(a.KI * a.B) * x 0 + -a.KI * x 2,
        -(b.KI * b.B) * x 1 + b.KI * x 2,
        -a.K / a.Tg * x 0 + 1 / a.Tg * x 3 + -1 / a.Tg * x 5,
        -b.K / b.Tg * x 1 + 1 / b.Tg * x 4 + -1 / b.Tg * x 6] := by
  rw [LTI.inputField_apply]
  congr 1
  ext i; fin_cases i <;>
    simp [plant7, dotProduct, Fin.sum_univ_seven, Fin.sum_univ_two]

/-- Governor rows of `plant7`: `T_g ΔṖ_m = −ΔP_m − K_R Δω + ΔP_C` (§1.3). -/
@[powerlib_foundation] theorem plant7_field_governor (ha : a.Tg ≠ 0) (hb : b.Tg ≠ 0)
    (x : EuclideanSpace ℝ (Fin 7)) (u : Fin 2 → ℝ) :
    a.Tg * (plant7 a b ωs T).inputField u x 5 = -x 5 - a.K * x 0 + x 3 ∧
      b.Tg * (plant7 a b ωs T).inputField u x 6 = -x 6 - b.K * x 1 + x 4 := by
  rw [plant7_field_apply]
  simp only [Fin.isValue, Matrix.cons_val]
  constructor <;> field_simp <;> ring

/-- The steady state is an equilibrium of every constant load, for every parameter value. Static
evidence on the model, not a connection conclusion. -/
@[powerlib_foundation] theorem plant7_steadyState_isEquilibrium (u : Fin 2 → ℝ) :
    IsEquilibrium ((plant7 a b ωs T).inputField u) (steadyState7 u) := by
  unfold IsEquilibrium
  rw [plant7_field_apply]
  ext i; fin_cases i <;> simp [steadyState7] <;> ring

/-- The seven-state version of §1.6: unique equilibrium
`(0, 0, 0, ΔP_L,a, ΔP_L,b, ΔP_L,a, ΔP_L,b)`. Static evidence on the model, not a connection
conclusion. -/
@[powerlib_foundation] theorem plant7_isEquilibrium_iff (ha : a.M ≠ 0) (hb : b.M ≠ 0)
    (hga : a.Tg ≠ 0) (hgb : b.Tg ≠ 0) (hKa : a.KI ≠ 0) (hKb : b.KI ≠ 0) (hT : ωs * T ≠ 0)
    (hB : a.B + b.B ≠ 0) (u : Fin 2 → ℝ) (e : EuclideanSpace ℝ (Fin 7)) :
    IsEquilibrium ((plant7 a b ωs T).inputField u) e ↔ e = steadyState7 u := by
  constructor
  · intro h
    unfold IsEquilibrium at h
    rw [plant7_field_apply] at h
    have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 7) => v 0) h
    have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 7) => v 1) h
    have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 7) => v 2) h
    have h3 := congrArg (fun v : EuclideanSpace ℝ (Fin 7) => v 3) h
    have h4 := congrArg (fun v : EuclideanSpace ℝ (Fin 7) => v 4) h
    have h5 := congrArg (fun v : EuclideanSpace ℝ (Fin 7) => v 5) h
    have h6 := congrArg (fun v : EuclideanSpace ℝ (Fin 7) => v 6) h
    simp only [Fin.isValue, Matrix.cons_val, PiLp.zero_apply] at h0 h1 h2 h3 h4 h5 h6
    have e01 : e 0 = e 1 := by
      have : ωs * T * (e 0 - e 1) = 0 := by linear_combination h2
      have := (mul_eq_zero.1 this).resolve_left hT
      linarith
    have e2a : e 2 + a.B * e 0 = 0 := by
      have : -a.KI * (e 2 + a.B * e 0) = 0 := by linear_combination h3
      exact (mul_eq_zero.1 this).resolve_left (neg_ne_zero.2 hKa)
    have e2b : -e 2 + b.B * e 1 = 0 := by
      have : b.KI * (e 2 - b.B * e 1) = 0 := by linear_combination h4
      have := (mul_eq_zero.1 this).resolve_left hKb
      linarith
    have e0 : e 0 = 0 := by
      have : (a.B + b.B) * e 0 = 0 := by rw [← e01] at e2b; linarith
      exact (mul_eq_zero.1 this).resolve_left hB
    have e1 : e 1 = 0 := by rw [← e01, e0]
    have e2 : e 2 = 0 := by rw [e0] at e2a; linarith
    rw [e0, e2] at h0
    rw [e0] at h5
    rw [e1, e2] at h1
    rw [e1] at h6
    field_simp at h0 h1 h5 h6
    have e5 : e 5 = u 0 := by linarith
    have e6 : e 6 = u 1 := by linarith
    have e3 : e 3 = u 0 := by linarith
    have e4 : e 4 = u 1 := by linarith
    ext i; fin_cases i <;> simp [steadyState7, e0, e1, e2, e3, e4, e5, e6]
  · rintro rfl
    exact plant7_steadyState_isEquilibrium u

/-! ## The families -/

/-- A two-area LFC model: the two areas, `ω_s` and the tie-line synchronizing coefficient. -/
structure Model where
  a : Area
  b : Area
  ωs : ℝ
  T : ℝ

/-- The five-state plant of a model. -/
def Model.plant (m : Model) : Linear.Plant 5 2 := LFC.plant m.a m.b m.ωs m.T

/-- A two-area LFC model with governor dynamics. -/
structure Model7 where
  a : Area
  b : Area
  ωs : ℝ
  T : ℝ

/-- The seven-state plant of a model. -/
def Model7.plant (m : Model7) : Linear.Plant 7 2 := LFC.plant7 m.a m.b m.ωs m.T

/-- Requirements on the state matrix of an LFC plant, all static. -/
inductive Requirement
  /-- The state matrix is Hurwitz. -/
  | hurwitz
  /-- A characteristic root in the open right half plane. -/
  | rhpRoot
  /-- A strict spectral margin at the rate `a`. -/
  | rate (a : ℝ)

/-- Satisfaction of a requirement by a state matrix. -/
def MeetsMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Requirement → Prop
  | .hurwitz => IsHurwitz A
  | .rhpRoot => ∃ s : ℂ, (Linear.characteristicMatrix A s).det = 0 ∧ 0 < s.re
  | .rate a => Linear.RateMargin A a

/-- The translation of the sentences: Lyapunov stability, the attractive sentences and sampled
contraction into `hurwitz`, instability into `rhpRoot`, a decay rate into its margin.
Conservation and passivity are translated into the whole language, which no model meets
(unavailable translation coverage, not a usable translation). -/
def translate : Sentence → Set Requirement
  | .flow .unstable => {.rhpRoot}
  | .flow (.decay a) => {.rate a}
  | .flow .conservative => Set.univ
  | .flow _ => {.hurwitz}
  | .passive => Set.univ
  | .envelope _ => ∅

/-- The five-state LFC family: every model read as the port system of its plant (area loads in,
area frequencies out). -/
def family : Family Model Requirement 5 2 :=
  ⟨fun m => m.plant.system, fun m => MeetsMatrix m.plant.A, translate⟩

/-- The seven-state LFC family. -/
def family7 : Family Model7 Requirement 7 2 :=
  ⟨fun m => m.plant.system, fun m => MeetsMatrix m.plant.A, translate⟩

@[powerlib_foundation] theorem family_isLinear : family.IsLinear Model.plant := fun _ => rfl

@[powerlib_foundation] theorem family7_isLinear : family7.IsLinear Model7.plant := fun _ => rfl

/-- A matrix is not both Hurwitz and with a right-half-plane root. -/
@[powerlib_foundation] theorem meetsMatrix_univ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ q, MeetsMatrix A q) : False := by
  obtain ⟨s, hs, hre⟩ : MeetsMatrix A .rhpRoot := h .rhpRoot
  have := (Linear.spectrallyStable_iff_isHurwitz A).2 (h .hurwitz) s hs
  linarith

/-- No five-state model meets every requirement. -/
@[tmio M, powerlib_foundation] theorem realize_univ :
    connection% (realize family.meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.realize_univ_eq_empty_of_forall fun _ h => meetsMatrix_univ _ h

/-- No seven-state model meets every requirement. -/
@[tmio M, powerlib_foundation] theorem realize_univ7 :
    connection% (realize family7.meets Set.univ = ∅) := by
  unfold powerlib.TMIO.Statement
  exact Spectral.realize_univ_eq_empty_of_forall fun _ h => meetsMatrix_univ _ h

/-- The LFC translation is the linear table of `theorem/Spectral/LinearNamed.lean`. -/
private theorem translate_eq_linearTable (s : Sentence) :
    translate s = Spectral.linearTable {.hurwitz} {.rhpRoot} univ univ (fun a => {.rate a}) s := by
  rcases s with P | _ | _
  · cases P <;> rfl
  · rfl
  · rfl

/-- Soundness of the matrix requirements for any linear family read through `MeetsMatrix`
(generic: an arbitrary family with an arbitrary plant map); the instance of
`Spectral.chain_le_semantics_of_linearTable_univ`. -/
@[tmio TM, powerlib_foundation] theorem sound_of_meetsMatrix {X : Type*} {n p : ℕ}
    {F : Family X Requirement n p}
    {plant : X → Linear.Plant n p} (hF : F.IsLinear plant)
    (hmeets : ∀ x q, F.meets x q ↔ MeetsMatrix (plant x).A q) (htr : F.translate = translate) :
    connection% (∀ P, F.chain P ≤ F.semantics P) := show ∀ P, F.chain P ≤ F.semantics P from
  Spectral.chain_le_semantics_of_linearTable_univ (Rs := {.hurwitz}) (Ru := {.rhpRoot})
    (Rd := fun a => {.rate a}) hF (fun s => htr ▸ translate_eq_linearTable s)
    (fun x hx => (hmeets x .hurwitz).1 ((mem_realize _ _ _).mp hx _ rfl))
    (fun x hx => (hmeets x .rhpRoot).1 ((mem_realize _ _ _).mp hx _ rfl))
    fun a x hx => hF.mem_den_decay_of_rateMargin
      ((hmeets x (.rate a)).1 ((mem_realize _ _ _).mp hx _ rfl))

/-- Exactness of the Hurwitz requirement for the attractive sentences and sampled contraction,
for any linear family read through `MeetsMatrix` (generic); the instance of
`Spectral.exact_of_linearTable`. -/
@[tmio TM, powerlib_foundation] theorem exact_of_meetsMatrix {X : Type*} {n p : ℕ}
    {F : Family X Requirement n p}
    {plant : X → Linear.Plant n p} (hF : F.IsLinear plant)
    (hmeets : ∀ x q, F.meets x q ↔ MeetsMatrix (plant x).A q) (htr : F.translate = translate)
    {P : Flow.Property} (hP : P.Attractive ∨ P = .contractive) :
    connection% (F.Exact (.flow P)) := show F.Exact (.flow P) from
  Spectral.exact_of_linearTable (Rs := {.hurwitz}) (Ru := {.rhpRoot}) (Rd := fun a => {.rate a})
    hF (fun s => htr ▸ translate_eq_linearTable s)
    (fun x => by simp [mem_realize, hmeets, MeetsMatrix]) hP

/-- Every translation of the five-state LFC family is sound. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics :
    connection% (∀ P, family.chain P ≤ family.semantics P) := by
  unfold powerlib.TMIO.Statement
  exact sound_of_meetsMatrix family_isLinear (fun _ _ => Iff.rfl) rfl

/-- The attractive sentences and sampled contraction of the five-state family are translated
exactly by the Hurwitz property of the state matrix. -/
@[tmio TM, powerlib_domain] theorem exact_hurwitz {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (family.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact exact_of_meetsMatrix family_isLinear (fun _ _ => Iff.rfl) rfl hP

/-- With a Hurwitz state matrix (explicit premise) the five-state model is globally
exponentially stable; in deviation coordinates this is the exponential convergence of every
trajectory under constant loads to the non-interactive steady state. -/
@[tmio TM, powerlib_domain] theorem mem_den_globallyExponentiallyStable (m : Model)
    (hA : IsHurwitz m.plant.A) :
    connection% (m ∈ family.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [family_isLinear.den_hurwitz (Or.inl (by simp))]
  exact hA

/-- Every translation of the seven-state LFC family is sound. -/
@[tmio TM, powerlib_domain] theorem chain_le_semantics7 :
    connection% (∀ P, family7.chain P ≤ family7.semantics P) := by
  unfold powerlib.TMIO.Statement
  exact sound_of_meetsMatrix family7_isLinear (fun _ _ => Iff.rfl) rfl

/-- The attractive sentences and sampled contraction of the seven-state family are translated
exactly by the Hurwitz property of the state matrix. -/
@[tmio TM, powerlib_domain] theorem exact_hurwitz7 {P : Flow.Property}
    (hP : P.Attractive ∨ P = .contractive) :
    connection% (family7.Exact (.flow P)) := by
  unfold powerlib.TMIO.Statement
  exact exact_of_meetsMatrix family7_isLinear (fun _ _ => Iff.rfl) rfl hP

/-- Seven-state model: Hurwitz premise ⇒ global exponential stability (convergence to the
steady state in deviation coordinates). -/
@[tmio TM, powerlib_domain] theorem mem_den_globallyExponentiallyStable7 (m : Model7)
    (hA : IsHurwitz m.plant.A) :
    connection% (m ∈ family7.den (.flow .globallyExponentiallyStable)) := by
  unfold powerlib.TMIO.Statement
  rw [family7_isLinear.den_hurwitz (Or.inl (by simp))]
  exact hA

/-! ## Implementation evidence (private, trajectory level) -/

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
§1.6 boxed, at trajectory level: `Δω_a, Δω_b, ΔP_tie → 0`, `ΔP_C,a → ΔP_L,a`,
`ΔP_C,b → ΔP_L,b` (Hurwitz premise), read from `mem_den_globallyExponentiallyStable`. -/
private theorem tendsto_of_isHurwitz (m : Model) (hA : IsHurwitz m.plant.A) (u : Fin 2 → ℝ)
    {x : ℝ → EuclideanSpace ℝ (Fin 5)}
    (hx : IsIntegralCurveOn x (fun _ y => m.plant.inputField u y) (Ici 0)) :
    Tendsto x atTop (𝓝 (steadyState u)) := by
  have hmem := mem_den_globallyExponentiallyStable m hA
  unfold powerlib.TMIO.Statement at hmem
  rw [family_isLinear.den_hurwitz (Or.inl (by simp))] at hmem
  exact LTI.tendsto_equilibrium m.plant hmem (steadyState_isEquilibrium u) hx

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
With a Hurwitz state matrix every solution under constant loads converges exponentially to the
non-interactive steady state. -/
private theorem exponentiallyConvergesTo_of_isHurwitz (m : Model) (hA : IsHurwitz m.plant.A)
    (u : Fin 2 → ℝ) :
    Flow.GloballyExponentiallyStable (m.plant.inputField u) (steadyState u) :=
  (Linear.holds_input_iff m.plant (steadyState_isEquilibrium u)
    (P := .globallyExponentiallyStable) (by simp)).2 hA

/-- Implementation evidence: trajectory-level result outside the sentence language (Rules §3a).
The seven-state version of `exponentiallyConvergesTo_of_isHurwitz`. -/
private theorem plant7_exponentiallyConvergesTo_of_isHurwitz (m : Model7)
    (hA : IsHurwitz m.plant.A) (u : Fin 2 → ℝ) :
    Flow.GloballyExponentiallyStable (m.plant.inputField u) (steadyState7 u) :=
  (Linear.holds_input_iff m.plant (plant7_steadyState_isEquilibrium u)
    (P := .globallyExponentiallyStable) (by simp)).2 hA

end powerlib.Frequency.LFC
