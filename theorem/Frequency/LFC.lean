import theorem.Frequency.Basic

/-! # Two-area load-frequency control (LFC) with AGC

Source: work-sync `theory/T-load-frequency-control.md` §1.1 (area swing), §1.2 (tie-line
linearization), §1.3 (governor), §1.4 (ACE, `B^Hz = B/f₀`, sign of `ACE_b`), §1.5 (AGC
integral), §1.6 (steady state / non-interactive control), §1.7 (two-area state matrix).

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
* `model` (§1.7, governors instantaneous, `T_g → 0`): state
  `x = (Δω_a, Δω_b, ΔP_tie,ab, ΔP_C,a, ΔP_C,b)`, input `u = (ΔP_L,a, ΔP_L,b)`, output
  `(Δω_a, Δω_b)`; `ΔP_m = ΔP_C − K_R Δω`.
* `model7` (§1.3 governors kept): state
  `x = (Δω_a, Δω_b, ΔP_tie,ab, ΔP_C,a, ΔP_C,b, ΔP_m,a, ΔP_m,b)`,
  `T_g ΔṖ_m = −ΔP_m − K_R Δω + ΔP_C`.
* Excluded: dead-bands, rate limits, generation limits / saturation, HVDC ties, voltage
  dynamics, delays, nonlinear tie-line power beyond the linearization, AGC filters.

Results.
* `tiePower_hasDerivAt`, `tieFlow_hasDerivAt` (foundation, §1.2): `T = V_a V_b cos δ⁰/X` is the
  slope of `V_a V_b sin δ / X`, and the linearised flow obeys `ΔṖ_tie = ω_s T (Δω_a − Δω_b)`.
* `ace_hz` (foundation, §1.4): `B Δω̂ = (B/f₀) Δf` with `Δf = f₀ Δω̂`.
* `field_*` (foundation): every row of the §1.7 matrix is the corresponding §1.1–§1.5
  equation (including the opposite sign of `ΔP_tie,ab` in the two AGC rows).
* `isEquilibrium_iff`, `model7_isEquilibrium_iff` (domain, §1.6): for `B_a + B_b ≠ 0`,
  `K_I ≠ 0`, `ω_s T ≠ 0` (and `M, T_g ≠ 0`) the unique equilibrium for constant loads is
  `Δω = 0`, `ΔP_tie = 0`, `ΔP_C,a = ΔP_L,a`, `ΔP_C,b = ΔP_L,b` (non-interactive control).
* `exponentiallyConvergesTo_of_isHurwitz`, `tendsto_of_isHurwitz` (domain): if the state
  matrix is Hurwitz, every trajectory converges exponentially to that equilibrium. The
  five-state matrix has no parametric Routh–Hurwitz condition here, so Hurwitz is an explicit
  premise. Correction: the note's §1.6 "设稳态存在" assumes convergence; the steady-state
  analysis alone does not establish it.
-/

noncomputable section
namespace powerlib.Frequency.LFC
open Set Filter Matrix
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
  /-- Governor time constant `T_g` [s] (only used by `model7`). -/
  Tg : ℝ

/-! ## Tie-line linearization and ACE (§1.2, §1.4) -/

/-- Tie-line synchronizing coefficient `T = V_a V_b cos δ⁰ / X`. -/
def syncCoeff (Va Vb X δ0 : ℝ) : ℝ := Va * Vb * Real.cos δ0 / X

/-- §1.2: `T` is the slope of `P_tie(δ) = V_a V_b sin δ / X` at `δ⁰`. -/
@[powerlib_foundation] theorem tiePower_hasDerivAt (Va Vb X δ0 : ℝ) :
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

/-- §1.7 five-state two-area LFC model. -/
def model (a b : Area) (ωs T : ℝ) : LTI.Model (Fin 5) (Fin 2) where
  A := !![-(a.D + a.K) / a.M, 0, -1 / a.M, 1 / a.M, 0;
          0, -(b.D + b.K) / b.M, 1 / b.M, 0, 1 / b.M;
          ωs * T, -(ωs * T), 0, 0, 0;
          -(a.KI * a.B), 0, -a.KI, 0, 0;
          0, -(b.KI * b.B), b.KI, 0, 0]
  B := !![-1 / a.M, 0; 0, -1 / b.M; 0, 0; 0, 0; 0, 0]
  C := !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0]
  D := 0

/-- The equilibrium `(0, 0, 0, ΔP_L,a, ΔP_L,b)`. -/
def steadyState (u : Fin 2 → ℝ) : Fin 5 → ℝ := ![0, 0, 0, u 0, u 1]

variable {a b : Area} {ωs T : ℝ}

@[powerlib_foundation] theorem field_apply (x : Fin 5 → ℝ) (u : Fin 2 → ℝ) :
    (model a b ωs T).field x u =
      ![-(a.D + a.K) / a.M * x 0 + -1 / a.M * x 2 + 1 / a.M * x 3 + -1 / a.M * u 0,
        -(b.D + b.K) / b.M * x 1 + 1 / b.M * x 2 + 1 / b.M * x 4 + -1 / b.M * u 1,
        ωs * T * x 0 + -(ωs * T) * x 1,
        -(a.KI * a.B) * x 0 + -a.KI * x 2,
        -(b.KI * b.B) * x 1 + b.KI * x 2] := by
  ext i; fin_cases i <;>
    simp [LTI.Model.field, model, dotProduct, Fin.sum_univ_five, Fin.sum_univ_two]

/-- Area `a` swing (§1.1 with §1.3, `T_g → 0`): `M_a Δω̇_a = ΔP_m,a − ΔP_L,a − D_a Δω_a − ΔP_tie,ab`
with `ΔP_m,a = ΔP_C,a − K_R,a Δω_a`. -/
@[powerlib_foundation] theorem field_swing_a (ha : a.M ≠ 0) (x : Fin 5 → ℝ) (u : Fin 2 → ℝ) :
    a.M * (model a b ωs T).field x u 0 = (x 3 - a.K * x 0) - u 0 - a.D * x 0 - x 2 := by
  rw [field_apply]
  simp only [Fin.isValue, Matrix.cons_val_zero]
  field_simp
  ring

/-- Area `b` swing: its net export is `−ΔP_tie,ab`. -/
@[powerlib_foundation] theorem field_swing_b (hb : b.M ≠ 0) (x : Fin 5 → ℝ) (u : Fin 2 → ℝ) :
    b.M * (model a b ωs T).field x u 1 = (x 4 - b.K * x 1) - u 1 - b.D * x 1 - (-x 2) := by
  rw [field_apply]
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
  field_simp
  ring

/-- Tie-line row: `ΔṖ_tie,ab = ω_s T (Δω_a − Δω_b)`. -/
@[powerlib_foundation] theorem field_tie (x : Fin 5 → ℝ) (u : Fin 2 → ℝ) :
    (model a b ωs T).field x u 2 = ωs * T * (x 0 - x 1) := by
  rw [field_apply]
  simp only [Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  ring

/-- AGC of area `a`: `ΔṖ_C,a = −K_I,a ACE_a`, `ACE_a = ΔP_tie,ab + B_a Δω_a`. -/
@[powerlib_foundation] theorem field_agc_a (x : Fin 5 → ℝ) (u : Fin 2 → ℝ) :
    (model a b ωs T).field x u 3 = -a.KI * (x 2 + a.B * x 0) := by
  rw [field_apply]
  simp [Matrix.cons_val]
  ring

/-- AGC of area `b`: `ΔṖ_C,b = −K_I,b ACE_b`, `ACE_b = −ΔP_tie,ab + B_b Δω_b` (§1.4 sign flip). -/
@[powerlib_foundation] theorem field_agc_b (x : Fin 5 → ℝ) (u : Fin 2 → ℝ) :
    (model a b ωs T).field x u 4 = -b.KI * (-x 2 + b.B * x 1) := by
  rw [field_apply]
  simp [Matrix.cons_val]
  ring

/-- §1.6 (non-interactive control): for `B_a + B_b ≠ 0`, `K_I,a, K_I,b ≠ 0`, `ω_s T ≠ 0`, the
unique equilibrium for constant loads `u = (ΔP_L,a, ΔP_L,b)` is `(0, 0, 0, ΔP_L,a, ΔP_L,b)`. -/
@[powerlib_domain] theorem isEquilibrium_iff (ha : a.M ≠ 0) (hb : b.M ≠ 0)
    (hKa : a.KI ≠ 0) (hKb : b.KI ≠ 0) (hT : ωs * T ≠ 0) (hB : a.B + b.B ≠ 0)
    (u : Fin 2 → ℝ) (e : Fin 5 → ℝ) :
    (model a b ωs T).IsEquilibrium u e ↔ e = steadyState u := by
  unfold LTI.Model.IsEquilibrium
  constructor
  · intro h
    have h0 := field_swing_a (b := b) (ωs := ωs) (T := T) ha e u
    have h1 := field_swing_b (a := a) (ωs := ωs) (T := T) hb e u
    have h2 := field_tie (a := a) (b := b) (ωs := ωs) (T := T) e u
    have h3 := field_agc_a (a := a) (b := b) (ωs := ωs) (T := T) e u
    have h4 := field_agc_b (a := a) (b := b) (ωs := ωs) (T := T) e u
    rw [h] at h0 h1 h2 h3 h4
    simp only [Pi.zero_apply, mul_zero] at h0 h1 h2 h3 h4
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
    · simp only [steadyState, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      rw [e0, e2] at h0; simp at h0; linarith
    · simp only [steadyState, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      rw [e1, e2] at h1; simp at h1; linarith
  · rintro rfl
    rw [field_apply]
    ext i; fin_cases i <;> simp [steadyState] <;> ring

@[powerlib_domain] theorem steadyState_isEquilibrium (ha : a.M ≠ 0) (hb : b.M ≠ 0)
    (hKa : a.KI ≠ 0) (hKb : b.KI ≠ 0) (hT : ωs * T ≠ 0) (hB : a.B + b.B ≠ 0)
    (u : Fin 2 → ℝ) : (model a b ωs T).IsEquilibrium u (steadyState u) :=
  (isEquilibrium_iff ha hb hKa hKb hT hB u _).2 rfl

/-- With a Hurwitz state matrix (explicit premise), every trajectory under constant loads
converges exponentially to the non-interactive steady state. -/
@[powerlib_domain] theorem exponentiallyConvergesTo_of_isHurwitz (ha : a.M ≠ 0) (hb : b.M ≠ 0)
    (hKa : a.KI ≠ 0) (hKb : b.KI ≠ 0) (hT : ωs * T ≠ 0) (hB : a.B + b.B ≠ 0)
    (hA : LinearSystems.IsHurwitz (model a b ωs T).A) (u : Fin 2 → ℝ) :
    ExponentiallyConvergesTo (model a b ωs T) u (steadyState u) :=
  Frequency.exponentiallyConvergesTo_of_isHurwitz
    (steadyState_isEquilibrium ha hb hKa hKb hT hB u) hA

/-- §1.6 boxed, at trajectory level: `Δω_a, Δω_b, ΔP_tie → 0`, `ΔP_C,a → ΔP_L,a`,
`ΔP_C,b → ΔP_L,b` (Hurwitz premise). -/
@[powerlib_domain] theorem tendsto_of_isHurwitz (ha : a.M ≠ 0) (hb : b.M ≠ 0)
    (hKa : a.KI ≠ 0) (hKb : b.KI ≠ 0) (hT : ωs * T ≠ 0) (hB : a.B + b.B ≠ 0)
    (hA : LinearSystems.IsHurwitz (model a b ωs T).A) (u : Fin 2 → ℝ)
    {x : ℝ → Fin 5 → ℝ} (hx : IsTrajectory (model a b ωs T) u x) :
    Tendsto x atTop (𝓝 ![0, 0, 0, u 0, u 1]) :=
  tendsto_of_exponentiallyConvergesTo
    (exponentiallyConvergesTo_of_isHurwitz ha hb hKa hKb hT hB hA u) hx

/-! ## Two-area model with governor dynamics -/

/-- Seven-state two-area model with first-order governors. -/
def model7 (a b : Area) (ωs T : ℝ) : LTI.Model (Fin 7) (Fin 2) where
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
def steadyState7 (u : Fin 2 → ℝ) : Fin 7 → ℝ := ![0, 0, 0, u 0, u 1, u 0, u 1]

@[powerlib_foundation] theorem model7_field_apply (x : Fin 7 → ℝ) (u : Fin 2 → ℝ) :
    (model7 a b ωs T).field x u =
      ![-a.D / a.M * x 0 + -1 / a.M * x 2 + 1 / a.M * x 5 + -1 / a.M * u 0,
        -b.D / b.M * x 1 + 1 / b.M * x 2 + 1 / b.M * x 6 + -1 / b.M * u 1,
        ωs * T * x 0 + -(ωs * T) * x 1,
        -(a.KI * a.B) * x 0 + -a.KI * x 2,
        -(b.KI * b.B) * x 1 + b.KI * x 2,
        -a.K / a.Tg * x 0 + 1 / a.Tg * x 3 + -1 / a.Tg * x 5,
        -b.K / b.Tg * x 1 + 1 / b.Tg * x 4 + -1 / b.Tg * x 6] := by
  ext i; fin_cases i <;>
    simp [LTI.Model.field, model7, dotProduct, Fin.sum_univ_seven, Fin.sum_univ_two]

/-- Governor rows of `model7`: `T_g ΔṖ_m = −ΔP_m − K_R Δω + ΔP_C` (§1.3). -/
@[powerlib_foundation] theorem model7_field_governor (ha : a.Tg ≠ 0) (hb : b.Tg ≠ 0)
    (x : Fin 7 → ℝ) (u : Fin 2 → ℝ) :
    a.Tg * (model7 a b ωs T).field x u 5 = -x 5 - a.K * x 0 + x 3 ∧
      b.Tg * (model7 a b ωs T).field x u 6 = -x 6 - b.K * x 1 + x 4 := by
  rw [model7_field_apply]
  simp only [Fin.isValue, Matrix.cons_val]
  constructor <;> field_simp <;> ring

/-- The seven-state version of §1.6: unique equilibrium
`(0, 0, 0, ΔP_L,a, ΔP_L,b, ΔP_L,a, ΔP_L,b)`. -/
@[powerlib_domain] theorem model7_isEquilibrium_iff (ha : a.M ≠ 0) (hb : b.M ≠ 0)
    (hga : a.Tg ≠ 0) (hgb : b.Tg ≠ 0) (hKa : a.KI ≠ 0) (hKb : b.KI ≠ 0) (hT : ωs * T ≠ 0)
    (hB : a.B + b.B ≠ 0) (u : Fin 2 → ℝ) (e : Fin 7 → ℝ) :
    (model7 a b ωs T).IsEquilibrium u e ↔ e = steadyState7 u := by
  unfold LTI.Model.IsEquilibrium
  rw [model7_field_apply]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    have h4 := congrFun h 4
    have h5 := congrFun h 5
    have h6 := congrFun h 6
    simp only [Fin.isValue, Matrix.cons_val, Pi.zero_apply] at h0 h1 h2 h3 h4 h5 h6
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
    ext i; fin_cases i <;> simp [steadyState7] <;> ring

@[powerlib_domain] theorem model7_steadyState_isEquilibrium (ha : a.M ≠ 0) (hb : b.M ≠ 0)
    (hga : a.Tg ≠ 0) (hgb : b.Tg ≠ 0) (hKa : a.KI ≠ 0) (hKb : b.KI ≠ 0) (hT : ωs * T ≠ 0)
    (hB : a.B + b.B ≠ 0) (u : Fin 2 → ℝ) :
    (model7 a b ωs T).IsEquilibrium u (steadyState7 u) :=
  (model7_isEquilibrium_iff ha hb hga hgb hKa hKb hT hB u _).2 rfl

/-- Seven-state model: Hurwitz premise ⇒ exponential convergence to the steady state. -/
@[powerlib_domain] theorem model7_exponentiallyConvergesTo_of_isHurwitz (ha : a.M ≠ 0)
    (hb : b.M ≠ 0) (hga : a.Tg ≠ 0) (hgb : b.Tg ≠ 0) (hKa : a.KI ≠ 0) (hKb : b.KI ≠ 0)
    (hT : ωs * T ≠ 0) (hB : a.B + b.B ≠ 0)
    (hA : LinearSystems.IsHurwitz (model7 a b ωs T).A) (u : Fin 2 → ℝ) :
    ExponentiallyConvergesTo (model7 a b ωs T) u (steadyState7 u) :=
  Frequency.exponentiallyConvergesTo_of_isHurwitz
    (model7_steadyState_isEquilibrium ha hb hga hgb hKa hKb hT hB u) hA

end powerlib.Frequency.LFC
